import LongTails.Proofs.CentralStencilStream
import LongTails.Proofs.QuinticStencilEstimator

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

/-!
Analysis of the four-point (quartic-bias) coordinate stencil inside the damped anchored momentum
round. One scheduled round reserves `2 * n k` central replicas; its two replica halves are recombined
by `(4 • central h - central (2 * h)) / 3`. The reply splits into its conditional mean, the
four-point secant `qDiff h f y`, and a mean-zero deviation whose second moment is at most
`4 * d * σ ^ 2 / (h ^ 2 * n k)`. The squared bias is supplied by the calling setup as an abstract
bound `B` on `‖qDiff h f y - gradient f y‖²`.
-/

namespace OracleTemplate.SecantPolyak.QuinticStencil

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
open OracleTemplate
open OracleTemplate.SecantPolyak.Centered
open OracleTemplate.SecantPolyak.CentralStencil
open SecantDescent SecantPolyak SecantPolyak.Accelerated ZerothOrder InexactGradient Scheduled
open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {Ω : Type} [_ms : MeasurableSpace Ω] {p : Measure Ω} [_ip : IsProbabilityMeasure p]

/-- Reply of one scheduled four-point round: the two replica halves of the slot block are decoded
by the Richardson combination `(4 • central h - central (2 * h)) / 3`. -/
noncomputable def qReplyS {d n N : ℕ} (hnN : 2 * n ≤ N) (g : Point d → Ω → ℝ) (h : ℝ)
    (x : Point d) (ω : secantSpace d N → Ω) : Point d :=
  qReply g h x (qCellsLow (fun t : secantSpace d (2 * n) => ω (cellInj hnN t)))
    (qCellsHigh (fun t : secantSpace d (2 * n) => ω (cellInj hnN t)))

/-- One scheduled four-point round: momentum extrapolation, then the four-point stencil at the
momentum probe point. -/
noncomputable def qStepSched {d N : ℕ} (n : ℕ → ℕ) (hnN : ∀ k, 2 * n k ≤ N)
    (L μ θ : ℝ) (g : Point d → Ω → ℝ) (h : ℝ) (k : ℕ) (s : Point d × Point d)
    (ω : secantSpace d N → Ω) : Point d × Point d :=
  step L μ θ s (qReplyS (hnN k) g h (query θ s) ω)

/-- The four-point reply of a round is the Richardson combination of the two half-batch replies. -/
lemma qReplyS_apply {d n N : ℕ} (hnN : 2 * n ≤ N) (g : Point d → Ω → ℝ) (h : ℝ) (x : Point d)
    (ω : secantSpace d N → Ω) :
    qReplyS hnN g h x ω =
      ((4 : ℝ) / 3) •
          cReply g h x (qCellsLow (fun t : secantSpace d (2 * n) => ω (cellInj hnN t))) -
        ((1 : ℝ) / 3) •
          cReply g (2 * h) x (qCellsHigh (fun t : secantSpace d (2 * n) => ω (cellInj hnN t))) := rfl

/-- The lower half of an ambient slot block depends measurably on the block. -/
lemma measurable_qCellsLowAmb {d n N : ℕ} (hnN : 2 * n ≤ N) :
    Measurable (fun ω : secantSpace d N → Ω =>
        qCellsLow (fun t : secantSpace d (2 * n) => ω (cellInj hnN t))) := by
  classical
  have hr : Measurable (fun ω : secantSpace d N → Ω =>
      fun t : secantSpace d (2 * n) => ω (cellInj hnN t)) :=
    measurable_pi_iff.mpr fun t => measurable_pi_apply (cellInj hnN t)
  have hc : Measurable (fun ξ : secantSpace d (2 * n) → Ω => qCellsLow ξ) :=
    measurable_qCellsLow
  show Measurable ((fun ξ : secantSpace d (2 * n) → Ω => qCellsLow ξ) ∘
    (fun ω : secantSpace d N → Ω => fun t : secantSpace d (2 * n) => ω (cellInj hnN t)))
  exact hc.comp hr

/-- The upper half of an ambient slot block depends measurably on the block. -/
lemma measurable_qCellsHighAmb {d n N : ℕ} (hnN : 2 * n ≤ N) :
    Measurable (fun ω : secantSpace d N → Ω =>
        qCellsHigh (fun t : secantSpace d (2 * n) => ω (cellInj hnN t))) := by
  classical
  have hr : Measurable (fun ω : secantSpace d N → Ω =>
      fun t : secantSpace d (2 * n) => ω (cellInj hnN t)) :=
    measurable_pi_iff.mpr fun t => measurable_pi_apply (cellInj hnN t)
  have hc : Measurable (fun ξ : secantSpace d (2 * n) → Ω => qCellsHigh ξ) :=
    measurable_qCellsHigh
  show Measurable ((fun ξ : secantSpace d (2 * n) → Ω => qCellsHigh ξ) ∘
    (fun ω : secantSpace d N → Ω => fun t : secantSpace d (2 * n) => ω (cellInj hnN t)))
  exact hc.comp hr

/-- The slot-to-halves map is measurable. -/
lemma measurable_qCellsPair {d n N : ℕ} (hnN : 2 * n ≤ N) :
    Measurable (fun ω : secantSpace d N → Ω =>
        (qCellsLow (fun t : secantSpace d (2 * n) => ω (cellInj hnN t)),
          qCellsHigh (fun t : secantSpace d (2 * n) => ω (cellInj hnN t)))) :=
  (measurable_qCellsLowAmb hnN).prodMk (measurable_qCellsHighAmb hnN)

/-- The four-point reply of a round is measurable at a fixed base point. -/
lemma measurable_qReplyS_at {d n N : ℕ} (hnN : 2 * n ≤ N) {g : Point d → Ω → ℝ}
    (hg : Measurable (Function.uncurry g)) (h : ℝ) (x : Point d) :
    Measurable (fun ω : secantSpace d N → Ω => qReplyS hnN g h x ω) := by
  classical
  have h1 : Measurable (fun ω : secantSpace d N → Ω =>
      cReply g h x (qCellsLow (fun t : secantSpace d (2 * n) => ω (cellInj hnN t)))) :=
    (measurable_cReply_at hg h x).comp (measurable_qCellsLowAmb hnN)
  have h2 : Measurable (fun ω : secantSpace d N → Ω =>
      cReply g (2 * h) x (qCellsHigh (fun t : secantSpace d (2 * n) => ω (cellInj hnN t)))) :=
    (measurable_cReply_at hg (2 * h) x).comp (measurable_qCellsHighAmb hnN)
  show Measurable (fun ω : secantSpace d N → Ω =>
      ((4 : ℝ) / 3) • cReply g h x (qCellsLow (fun t : secantSpace d (2 * n) =>
          ω (cellInj hnN t))) -
        ((1 : ℝ) / 3) • cReply g (2 * h) x (qCellsHigh (fun t : secantSpace d (2 * n) =>
          ω (cellInj hnN t))))
  exact smul_measurable measurable_const h1 |>.sub (smul_measurable measurable_const h2)

/-- Each replica half of a round is an integrable central reply. -/
lemma qReplyS_halves_integrable {d n N : ℕ} (hnN : 2 * n ≤ N) {g : Point d → Ω → ℝ}
    {f : Point d → ℝ} (hgi : ∀ x, Integrable (g x) p)
    (hmean : ∀ x, (∫ ω, g x ω ∂p) = f x) (hn : 0 < n) (x : Point d) :
    Integrable (fun ω : secantSpace d N → Ω =>
        cReply g h x (qCellsLow (fun t : secantSpace d (2 * n) => ω (cellInj hnN t))))
        (slotLaw d N p) ∧
      Integrable (fun ω : secantSpace d N → Ω =>
        cReply g (2 * h) x (qCellsHigh (fun t : secantSpace d (2 * n) => ω (cellInj hnN t))))
        (slotLaw d N p) := by
  classical
  have hc1 : Integrable (cReply g h x) (batchLaw d n p) := cReply_integrable hgi hmean hn x
  have hc2 : Integrable (cReply g (2 * h) x) (batchLaw d n p) := cReply_integrable hgi hmean hn x
  have hp1 := measurePreserving_qCellsLow_ambient (Ω := Ω) (p := p) (d := d) (n := n) (N := N) hnN
  have hp2 := measurePreserving_qCellsHigh_ambient (Ω := Ω) (p := p) (d := d) (n := n) (N := N) hnN
  exact ⟨hp1.integrable_comp_of_integrable (ε := Point d) hc1,
    hp2.integrable_comp_of_integrable (ε := Point d) hc2⟩

/-- The four-point reply of a round is integrable. -/
lemma qReplyS_integrable {d n N : ℕ} (hnN : 2 * n ≤ N) {g : Point d → Ω → ℝ} {f : Point d → ℝ}
    (hgi : ∀ x, Integrable (g x) p) (hmean : ∀ x, (∫ ω, g x ω ∂p) = f x)
    (hn : 0 < n) (x : Point d) : Integrable (qReplyS hnN g h x) (slotLaw d N p) := by
  classical
  obtain ⟨h1, h2⟩ := qReplyS_halves_integrable hnN hgi hmean hn x
  refine (Integrable.smul ((4 : ℝ) / 3) h1).sub (Integrable.smul ((1 : ℝ) / 3) h2) |>.congr
    (ae_of_all _ fun ω => (qReplyS_apply hnN g h x ω).symm)

/-- The mean of the four-point reply of a round is the four-point secant. -/
lemma qReplyS_mean {d n N : ℕ} (hnN : 2 * n ≤ N) {g : Point d → Ω → ℝ} {f : Point d → ℝ} {h : ℝ}
    (hgi : ∀ x, Integrable (g x) p) (hmean : ∀ x, (∫ ω, g x ω ∂p) = f x)
    (hn : 0 < n) (x : Point d) :
    (∫ ω : secantSpace d N → Ω, qReplyS hnN g h x ω ∂(slotLaw d N p)) = qDiff h f x := by
  classical
  obtain ⟨h1, h2⟩ := qReplyS_halves_integrable hnN hgi hmean hn x
  have hc1 : Integrable (cReply g h x) (batchLaw d n p) := cReply_integrable hgi hmean hn x
  have hc2 : Integrable (cReply g (2 * h) x) (batchLaw d n p) := cReply_integrable hgi hmean hn x
  have he1 : (∫ ω : secantSpace d N → Ω,
      cReply g h x (qCellsLow (fun t : secantSpace d (2 * n) => ω (cellInj hnN t)))
        ∂(slotLaw d N p)) = cDiff h f x := by
    have hpm := measurePreserving_qCellsLow_ambient (Ω := Ω) (p := p) (d := d) (n := n) (N := N) hnN
    rw [integral_comp_preserving_point hpm hc1]
    exact cReply_mean (d := d) (m := n) (g := g) (f := f) (h := h) hgi hmean hn x
  have he2 : (∫ ω : secantSpace d N → Ω,
      cReply g (2 * h) x (qCellsHigh (fun t : secantSpace d (2 * n) => ω (cellInj hnN t)))
        ∂(slotLaw d N p)) = cDiff (2 * h) f x := by
    have hpm := measurePreserving_qCellsHigh_ambient (Ω := Ω) (p := p) (d := d) (n := n) (N := N) hnN
    rw [integral_comp_preserving_point hpm hc2]
    exact cReply_mean (d := d) (m := n) (g := g) (f := f) (h := 2 * h) hgi hmean hn x
  have hsplit : (∫ ω : secantSpace d N → Ω, qReplyS hnN g h x ω ∂(slotLaw d N p))
      = ((4 : ℝ) / 3) • (∫ ω : secantSpace d N → Ω,
            cReply g h x (qCellsLow (fun t : secantSpace d (2 * n) => ω (cellInj hnN t)))
              ∂(slotLaw d N p)) -
          ((1 : ℝ) / 3) • (∫ ω : secantSpace d N → Ω,
            cReply g (2 * h) x (qCellsHigh (fun t : secantSpace d (2 * n) => ω (cellInj hnN t)))
              ∂(slotLaw d N p)) := by
    show (∫ ω : secantSpace d N → Ω,
            ((4 : ℝ) / 3) •
                cReply g h x (qCellsLow (fun t : secantSpace d (2 * n) => ω (cellInj hnN t))) -
              ((1 : ℝ) / 3) •
                cReply g (2 * h) x (qCellsHigh (fun t : secantSpace d (2 * n) =>
                  ω (cellInj hnN t))) ∂(slotLaw d N p)) =
          ((4 : ℝ) / 3) • (∫ ω : secantSpace d N → Ω,
                cReply g h x (qCellsLow (fun t : secantSpace d (2 * n) => ω (cellInj hnN t)))
                  ∂(slotLaw d N p)) -
            ((1 : ℝ) / 3) • (∫ ω : secantSpace d N → Ω,
                cReply g (2 * h) x
                  (qCellsHigh (fun t : secantSpace d (2 * n) => ω (cellInj hnN t)))
                  ∂(slotLaw d N p))
    calc (∫ ω : secantSpace d N → Ω,
              ((4 : ℝ) / 3) •
                  cReply g h x (qCellsLow (fun t : secantSpace d (2 * n) => ω (cellInj hnN t))) -
                ((1 : ℝ) / 3) •
                  cReply g (2 * h) x
                    (qCellsHigh (fun t : secantSpace d (2 * n) => ω (cellInj hnN t)))
              ∂(slotLaw d N p))
          = (∫ ω : secantSpace d N → Ω,
                ((4 : ℝ) / 3) •
                  cReply g h x (qCellsLow (fun t : secantSpace d (2 * n) => ω (cellInj hnN t)))
                  ∂(slotLaw d N p)) -
              ∫ ω : secantSpace d N → Ω,
                ((1 : ℝ) / 3) •
                  cReply g (2 * h) x
                    (qCellsHigh (fun t : secantSpace d (2 * n) => ω (cellInj hnN t)))
                ∂(slotLaw d N p) :=
            integral_sub (Integrable.smul ((4 : ℝ) / 3) h1) (Integrable.smul ((1 : ℝ) / 3) h2)
      _ = ((4 : ℝ) / 3) • (∫ ω : secantSpace d N → Ω,
                cReply g h x (qCellsLow (fun t : secantSpace d (2 * n) => ω (cellInj hnN t)))
                  ∂(slotLaw d N p)) -
            ((1 : ℝ) / 3) • (∫ ω : secantSpace d N → Ω,
                cReply g (2 * h) x
                  (qCellsHigh (fun t : secantSpace d (2 * n) => ω (cellInj hnN t)))
                  ∂(slotLaw d N p)) := by
          rw [integral_smul, integral_smul]
  rw [hsplit, he1, he2]
  rfl

/-- The mean-square noise of the four-point reply of a round, measured at the slot level. -/
lemma qReplyS_deviation {d n N : ℕ} (hnN : 2 * n ≤ N) {g : Point d → Ω → ℝ} {f : Point d → ℝ}
    {σ h : ℝ}
    (hg : Measurable (Function.uncurry g))
    (hgi : ∀ x, Integrable (g x) p)
    (hmean : ∀ x, (∫ ω, g x ω ∂p) = f x)
    (hvi : ∀ x, Integrable (fun ω => (g x ω - f x) ^ 2) p)
    (hv : ∀ x, (∫ ω, (g x ω - f x) ^ 2 ∂p) ≤ σ ^ 2)
    (hn : 0 < n) (x : Point d) :
    Integrable (fun ω : secantSpace d N → Ω => ‖qReplyS hnN g h x ω - qDiff h f x‖ ^ 2)
        (slotLaw d N p) ∧
      (∫ ω : secantSpace d N → Ω, ‖qReplyS hnN g h x ω - qDiff h f x‖ ^ 2 ∂(slotLaw d N p))
        ≤ (4 : ℝ) * ((d : ℝ) * σ ^ 2 / (h ^ 2 * n)) := by
  classical
  obtain ⟨h1i, h1b⟩ := cReply_deviation (d := d) (m := n) (g := g) (h := h) hg hgi hmean hvi hv hn x
  obtain ⟨h2i, h2b⟩ := cReply_deviation (d := d) (m := n) (g := g) (h := 2 * h) hg hgi hmean hvi hv
    hn x
  set F1 : (secantSpace d N → Ω) → ℝ := fun ω =>
    ‖cReply g h x (qCellsLow (fun t : secantSpace d (2 * n) => ω (cellInj hnN t))) - cDiff h f x‖ ^ 2
  set F2 : (secantSpace d N → Ω) → ℝ := fun ω =>
    ‖cReply g (2 * h) x (qCellsHigh (fun t : secantSpace d (2 * n) => ω (cellInj hnN t))) -
      cDiff (2 * h) f x‖ ^ 2
  have hp1 := measurePreserving_qCellsLow_ambient (Ω := Ω) (p := p) (d := d) (n := n) (N := N) hnN
  have hp2 := measurePreserving_qCellsHigh_ambient (Ω := Ω) (p := p) (d := d) (n := n) (N := N) hnN
  have hF1i : Integrable F1 (slotLaw d N p) := hp1.integrable_comp_of_integrable (ε := ℝ) h1i
  have hF2i : Integrable F2 (slotLaw d N p) := hp2.integrable_comp_of_integrable (ε := ℝ) h2i
  have ht1 : (∫ ω : secantSpace d N → Ω, F1 ω ∂(slotLaw d N p))
      = ∫ η, ‖cReply g h x η - cDiff h f x‖ ^ 2 ∂(batchLaw d n p) :=
    integral_comp_preserving hp1 h1i
  have ht2 : (∫ ω : secantSpace d N → Ω, F2 ω ∂(slotLaw d N p))
      = ∫ η, ‖cReply g (2 * h) x η - cDiff (2 * h) f x‖ ^ 2 ∂(batchLaw d n p) :=
    integral_comp_preserving hp2 h2i
  have hbd : ∀ ω : secantSpace d N → Ω,
      ‖qReplyS hnN g h x ω - qDiff h f x‖ ^ 2 ≤ ((32 : ℝ) / 9) * F1 ω + ((2 : ℝ) / 9) * F2 ω := by
    intro ω
    exact qReply_pointwise x _ _
  have hsumi : Integrable (fun ω : secantSpace d N → Ω =>
      ((32 : ℝ) / 9) * F1 ω + ((2 : ℝ) / 9) * F2 ω) (slotLaw d N p) :=
    Integrable.add (hF1i.const_mul ((32 : ℝ) / 9)) (hF2i.const_mul ((2 : ℝ) / 9))
  have hZmeas : Measurable (fun ω : secantSpace d N → Ω =>
      ‖qReplyS hnN g h x ω - qDiff h f x‖ ^ 2) :=
    ((measurable_qReplyS_at hnN hg h x).sub_const (qDiff h f x)).norm.pow_const 2
  have hZm : AEStronglyMeasurable
      (fun ω : secantSpace d N → Ω => ‖qReplyS hnN g h x ω - qDiff h f x‖ ^ 2) (slotLaw d N p) :=
    hZmeas.aestronglyMeasurable
  have hZi : Integrable (fun ω : secantSpace d N → Ω => ‖qReplyS hnN g h x ω - qDiff h f x‖ ^ 2)
      (slotLaw d N p) := by
    refine hsumi.mono hZm (ae_of_all _ fun ω => ?_)
    have hb := hbd ω
    have hM : 0 ≤ ((32 : ℝ) / 9) * F1 ω + ((2 : ℝ) / 9) * F2 ω := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), abs_of_nonneg hM]
    exact hb
  refine ⟨hZi, ?_⟩
  calc (∫ ω : secantSpace d N → Ω, ‖qReplyS hnN g h x ω - qDiff h f x‖ ^ 2 ∂(slotLaw d N p))
      ≤ ∫ ω : secantSpace d N → Ω, ((32 : ℝ) / 9) * F1 ω + ((2 : ℝ) / 9) * F2 ω
          ∂(slotLaw d N p) := integral_mono hZi hsumi hbd
    _ = ((32 : ℝ) / 9) * (∫ ω : secantSpace d N → Ω, F1 ω ∂(slotLaw d N p)) +
          ((2 : ℝ) / 9) * (∫ ω : secantSpace d N → Ω, F2 ω ∂(slotLaw d N p)) := by
        rw [integral_add (hF1i.const_mul ((32 : ℝ) / 9)) (hF2i.const_mul ((2 : ℝ) / 9)),
          integral_const_mul, integral_const_mul]
    _ = ((32 : ℝ) / 9) * (∫ η, ‖cReply g h x η - cDiff h f x‖ ^ 2 ∂(batchLaw d n p)) +
          ((2 : ℝ) / 9) * (∫ η, ‖cReply g (2 * h) x η - cDiff (2 * h) f x‖ ^ 2
            ∂(batchLaw d n p)) := by rw [ht1, ht2]
    _ ≤ ((32 : ℝ) / 9) * ((d : ℝ) * σ ^ 2 / (h ^ 2 * n)) +
          ((2 : ℝ) / 9) * ((d : ℝ) * σ ^ 2 / ((2 * h) ^ 2 * n)) := by gcongr
    _ ≤ (4 : ℝ) * ((d : ℝ) * σ ^ 2 / (h ^ 2 * n)) :=
        quintic_noise_arith _ _ (by positivity) (quintic_half_scale d h σ n)

/-- The reply of round `k` is jointly measurable in state and slots. -/
lemma measurable_qReplyRound {d N : ℕ} (n : ℕ → ℕ) (hnN : ∀ k, 2 * n k ≤ N)
    {g : Point d → Ω → ℝ} (hg : Measurable (Function.uncurry g)) (θ h : ℝ) (k : ℕ) :
    Measurable (fun q : (Point d × Point d) × (secantSpace d N → Ω) =>
      qReplyS (hnN k) g h (query θ q.1) q.2) := by
  classical
  have hq : Measurable (fun q : (Point d × Point d) × (secantSpace d N → Ω) => query θ q.1) := by
    have hc : Continuous (fun p : Point d × Point d => (1 / (1 + θ)) • (p.1 + θ • p.2)) := by
      fun_prop
    show Measurable ((fun p : Point d × Point d => (1 / (1 + θ)) • (p.1 + θ • p.2)) ∘
      (fun q : (Point d × Point d) × (secantSpace d N → Ω) => q.1))
    exact hc.measurable.comp measurable_fst
  have ha : Measurable (fun q : (Point d × Point d) × (secantSpace d N → Ω) =>
      cReply g h (query θ q.1)
        (qCellsLow (fun t : secantSpace d (2 * n k) => q.2 (cellInj (hnN k) t)))) := by
    show Measurable
        ((fun pq : Point d × (Fin (n k) → Fin d × Bool → Ω) => cReply g h pq.1 pq.2) ∘
          (fun q : (Point d × Point d) × (secantSpace d N → Ω) =>
            (query θ q.1,
              qCellsLow (fun t : secantSpace d (2 * n k) => q.2 (cellInj (hnN k) t)))))
    exact (measurable_cReply_joint hg h).comp
      (hq.prodMk ((measurable_qCellsLowAmb (hnN k)).comp measurable_snd))
  have hb : Measurable (fun q : (Point d × Point d) × (secantSpace d N → Ω) =>
      cReply g (2 * h) (query θ q.1)
        (qCellsHigh (fun t : secantSpace d (2 * n k) => q.2 (cellInj (hnN k) t)))) := by
    show Measurable
        ((fun pq : Point d × (Fin (n k) → Fin d × Bool → Ω) =>
            cReply g (2 * h) pq.1 pq.2) ∘
          (fun q : (Point d × Point d) × (secantSpace d N → Ω) =>
            (query θ q.1,
              qCellsHigh (fun t : secantSpace d (2 * n k) => q.2 (cellInj (hnN k) t)))))
    exact (measurable_cReply_joint hg (2 * h)).comp
      (hq.prodMk ((measurable_qCellsHighAmb (hnN k)).comp measurable_snd))
  show Measurable (fun q : (Point d × Point d) × (secantSpace d N → Ω) =>
      ((4 : ℝ) / 3) •
          cReply g h (query θ q.1)
            (qCellsLow (fun t : secantSpace d (2 * n k) => q.2 (cellInj (hnN k) t))) -
        ((1 : ℝ) / 3) •
          cReply g (2 * h) (query θ q.1)
            (qCellsHigh (fun t : secantSpace d (2 * n k) => q.2 (cellInj (hnN k) t))))
  exact (smul_measurable measurable_const ha).sub (smul_measurable measurable_const hb)

/-- The scheduled four-point step is jointly measurable. -/
lemma measurable_qStepSched_joint {d N : ℕ} (n : ℕ → ℕ) (hnN : ∀ k, 2 * n k ≤ N)
    {g : Point d → Ω → ℝ} (hg : Measurable (Function.uncurry g)) (L μ θ h : ℝ) (k : ℕ) :
    Measurable (fun q : (Point d × Point d) × (secantSpace d N → Ω) =>
      qStepSched n hnN L μ θ g h k q.1 q.2) := by
  classical
  have h1 : Measurable (fun q : (Point d × Point d) × (secantSpace d N → Ω) =>
      qReplyS (hnN k) g h (query θ q.1) q.2) := measurable_qReplyRound n hnN hg θ h k
  have hstepc : Continuous (fun p : (Point d × Point d) × Point d => step L μ θ p.1 p.2) := by
    show Continuous (fun p : (Point d × Point d) × Point d =>
      ((1 / (1 + θ)) • (p.1.1 + θ • p.1.2) - (1 / L) • p.2,
        (1 - θ) • p.1.2 + θ • ((1 / (1 + θ)) • (p.1.1 + θ • p.1.2)) - (2 * θ / μ) • p.2))
    fun_prop
  have heq : (fun q : (Point d × Point d) × (secantSpace d N → Ω) =>
      qStepSched n hnN L μ θ g h k q.1 q.2) =
      (fun p : (Point d × Point d) × Point d => step L μ θ p.1 p.2) ∘
        (fun q : (Point d × Point d) × (secantSpace d N → Ω) =>
          (q.1, qReplyS (hnN k) g h (query θ q.1) q.2)) := by
    funext q
    rfl
  rw [heq]
  exact hstepc.measurable.comp (measurable_fst.prodMk h1)

/-- One four-point accelerated round: with a stencil whose squared bias is at most `B`, the Lyapunov
decrease holds with the bias factor `2 * (3 / (4 * L) + 2 * θ / μ) * B` and the centered variance
coefficient `1 / (2 * L) + θ ^ 2 / μ` times `4 * d * σ ^ 2 / (h ^ 2 * n k)`. -/
lemma q_one_step {d N : ℕ} (n : ℕ → ℕ) (hnN : ∀ k, 2 * n k ≤ N) (hn : ∀ k, 0 < n k) {B : ℝ}
    {g : Point d → Ω → ℝ} {f : Point d → ℝ} {σ L μ θ h : ℝ} {xstar : Point d}
    (_hh : 0 < h) (hL : 0 < L) (hμ : 0 < μ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hθL : 16 * L * θ ^ 2 ≤ μ)
    (hbias : ∀ y, ‖qDiff h f y - gradient f y‖ ^ 2 ≤ B)
    (hg : Measurable (Function.uncurry g))
    (hgi : ∀ x, Integrable (g x) p)
    (hmean : ∀ x, (∫ ω, g x ω ∂p) = f x)
    (hvi : ∀ x, Integrable (fun ω => (g x ω - f x) ^ 2) p)
    (hv : ∀ x, (∫ ω, (g x ω - f x) ^ 2 ∂p) ≤ σ ^ 2)
    (_hc : ConvexOn ℝ Set.univ f)
    (hgr : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hsc : ∀ x y, f x + ⟪gradient f x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (hmin : IsMinOn f Set.univ xstar)
    (k : ℕ) (s : Point d × Point d) :
    Integrable (fun ω => potential f μ xstar (qStepSched n hnN L μ θ g h k s ω)) (slotLaw d N p) ∧
      (∫ ω, potential f μ xstar (qStepSched n hnN L μ θ g h k s ω) ∂(slotLaw d N p)) ≤
        (1 - θ / 2) * potential f μ xstar s
          + 2 * (3 / (4 * L) + 2 * θ / μ) * B
          + (1 / (2 * L) + θ ^ 2 / μ) * (4 * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (n k)))) := by
  classical
  have hminf : ∀ x, f xstar ≤ f x := fun x => hmin (Set.mem_univ x)
  have hf : Measurable f :=
    (continuous_iff_continuousAt.mpr fun x => (hgr x).continuousAt).measurable
  set y : Point d := query θ s with hydef
  set v₀ : Point d := qDiff h f y with hv0def
  set q : (secantSpace d N → Ω) → (Fin (n k) → Fin d × Bool → Ω) ×
      (Fin (n k) → Fin d × Bool → Ω) :=
    fun ω => (qCellsLow (fun t : secantSpace d (2 * n k) => ω (cellInj (hnN k) t)),
      qCellsHigh (fun t : secantSpace d (2 * n k) => ω (cellInj (hnN k) t))) with hqdef
  set V : (secantSpace d N → Ω) → Point d := fun ω => qReplyS (hnN k) g h y ω with hVdef
  set xi : (secantSpace d N → Ω) → Point d := fun ω => V ω - v₀ with hxidef
  set c : Point d := -(1 / L) • gradient f (y - (1 / L) • v₀)
      - θ • ((1 - θ) • s.2 + θ • y - (2 * θ / μ) • v₀ - xstar) with hcdef
  set cv : ℝ := 1 / (2 * L) + θ ^ 2 / μ with hcvdef
  set cb : ℝ := 2 * (3 / (4 * L) + 2 * θ / μ) with hcbdef
  set S1 : (secantSpace d N → Ω) → Point d × Point d :=
    (fun r : (Point d × Point d) × (secantSpace d N → Ω) =>
        qStepSched n hnN L μ θ g h k r.1 r.2) ∘ (fun ω : secantSpace d N → Ω => (s, ω))
    with hS1def
  set F : (secantSpace d N → Ω) → ℝ := potential f μ xstar ∘ S1 with hfdef
  set Lc : Point d →L[ℝ] ℝ := InnerProductSpace.toDual ℝ (Point d) c with hLcdef
  set E : (secantSpace d N → Ω) → ℝ := fun ω => Lc (xi ω) + cv * ‖xi ω‖ ^ 2 with hEdef
  set a : ℝ := (1 - θ / 2) * potential f μ xstar s + cb * B with hadef
  set G : (secantSpace d N → Ω) → ℝ := fun ω => a + E ω with hGdef
  have hreplyi : Integrable V (slotLaw d N p) :=
    qReplyS_integrable (hnN k) hgi hmean (hn k) y
  have hVnonneg : ∀ t : Point d × Point d, 0 ≤ potential f μ xstar t := by
    intro t
    show 0 ≤ f t.1 - f xstar + μ / 4 * ‖t.2 - xstar‖ ^ 2
    exact add_nonneg (sub_nonneg.mpr (hminf t.1)) (mul_nonneg (by positivity) (sq_nonneg _))
  have hcb0 : 0 ≤ cb := by positivity
  have hcv0 : 0 ≤ cv := by positivity
  have hVm : Measurable V := measurable_qReplyS_at (hnN k) hg h y
  have hxim : Measurable xi := hVm.sub measurable_const
  have hxii : Integrable xi (slotLaw d N p) := hreplyi.sub (integrable_const _)
  have hVmean : (∫ ω, V ω ∂(slotLaw d N p)) = v₀ := by
    show (∫ ω, qReplyS (hnN k) g h y ω ∂(slotLaw d N p)) = v₀
    rw [hv0def, hydef]
    exact qReplyS_mean (hnN k) hgi hmean (hn k) y
  have hxi0 : (∫ ω, xi ω ∂(slotLaw d N p)) = 0 := by
    show (∫ ω, V ω - v₀ ∂(slotLaw d N p)) = 0
    rw [integral_sub hreplyi (integrable_const _), hVmean, integral_const, probReal_univ,
      one_smul, sub_self]
  have hlin0 : (∫ ω, Lc (xi ω) ∂(slotLaw d N p)) = 0 := by
    rw [Lc.integral_comp_comm hxii, hxi0, map_zero]
  have hFm : Measurable F := by
    rw [hfdef, hS1def]
    exact (measurable_potentialZO hf).comp
      ((measurable_qStepSched_joint n hnN hg L μ θ h k).comp
        (measurable_const.prodMk measurable_id))
  have hdeV : ∀ ω, qStepSched n hnN L μ θ g h k s ω = step L μ θ s (V ω) := fun _ => rfl
  have hVadd : ∀ ω, V ω = v₀ + xi ω := fun ω => by
    show V ω = v₀ + (V ω - v₀)
    rw [add_comm, sub_add_cancel]
  have hde : ∀ ω, qStepSched n hnN L μ θ g h k s ω = step L μ θ s (v₀ + xi ω) := fun ω =>
    (hdeV ω).trans (congrArg (step L μ θ s) (hVadd ω))
  have hbiasy : ‖v₀ - gradient f (query θ s)‖ ^ 2 ≤ B := by
    rw [hv0def, hydef]
    exact hbias y
  have hpath : ∀ ω, F ω ≤ G ω := by
    intro ω
    have hp1 : potential f μ xstar (step L μ θ s (v₀ + xi ω)) ≤
        potential f μ xstar (step L μ θ s v₀) + Lc (xi ω) + cv * ‖xi ω‖ ^ 2 :=
      potential_step_perturb (d := d) (f := f) (L := L) (μ := μ) (xstar := xstar)
        hL hμ hθ0 hgr hlip s v₀ (xi ω)
    have hp2 := accel_potential_step (f := f) (L := L) (μ := μ) (θ := θ) (xstar := xstar)
      hL hμ hθ0 hθ1 hθL hgr hlip hsc hmin s v₀
    have h4 : cb * ‖v₀ - gradient f (query θ s)‖ ^ 2 ≤ cb * B :=
      mul_le_mul_of_nonneg_left hbiasy hcb0
    have hw : F ω = potential f μ xstar (qStepSched n hnN L μ θ g h k s ω) := rfl
    rw [hw, hde ω]
    show potential f μ xstar (step L μ θ s (v₀ + xi ω)) ≤ a + (Lc (xi ω) + cv * ‖xi ω‖ ^ 2)
    linarith
  obtain hdev := qReplyS_deviation (hnN k) hg hgi hmean hvi hv (hn k) y
  have hxi2 : Integrable (fun ω => ‖xi ω‖ ^ 2) (slotLaw d N p) := by
    refine Integrable.congr hdev.1 (ae_of_all _ fun ω => ?_)
    show ‖V ω - v₀‖ ^ 2 = ‖V ω - v₀‖ ^ 2
    rfl
  have hEm : Measurable E := by
    show Measurable (fun ω => Lc (xi ω) + cv * ‖xi ω‖ ^ 2)
    have hq2 : Continuous (fun t : ℝ => cv * t ^ 2) := by continuity
    refine (Lc.continuous.measurable.comp hxim).add ?_
    exact hq2.measurable.comp hxim.norm
  have hEi : Integrable E (slotLaw d N p) := by
    show Integrable (fun ω => Lc (xi ω) + cv * ‖xi ω‖ ^ 2) (slotLaw d N p)
    refine (Lc.integrable_comp hxii).add ?_
    exact hxi2.const_mul cv
  have hGi : Integrable G (slotLaw d N p) := by
    rw [hGdef]
    exact (integrable_const a).add hEi
  have hFi : Integrable F (slotLaw d N p) :=
    hGi.mono' hFm.aestronglyMeasurable (ae_of_all _ fun ω => by
      have h0 : 0 ≤ F ω := hVnonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact hpath ω)
  have hEint : (∫ ω, E ω ∂(slotLaw d N p)) = cv * ∫ ω, ‖xi ω‖ ^ 2 ∂(slotLaw d N p) := by
    show (∫ ω, Lc (xi ω) + cv * ‖xi ω‖ ^ 2 ∂(slotLaw d N p)) =
      cv * ∫ ω, ‖xi ω‖ ^ 2 ∂(slotLaw d N p)
    have hEi2 : Integrable (fun ω => cv * ‖xi ω‖ ^ 2) (slotLaw d N p) := hxi2.const_mul cv
    rw [integral_add (f := fun ω => Lc (xi ω)) (g := fun ω => cv * ‖xi ω‖ ^ 2)
      (Lc.integrable_comp hxii) hEi2, hlin0, zero_add, integral_const_mul]
  have hbnd : (∫ ω, ‖xi ω‖ ^ 2 ∂(slotLaw d N p)) ≤ 4 * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (n k))) := by
    refine hdev.2.trans_eq ?_
    rfl
  have h5 : cv * ∫ ω, ‖xi ω‖ ^ 2 ∂(slotLaw d N p)
      ≤ cv * (4 * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (n k)))) :=
    mul_le_mul_of_nonneg_left hbnd hcv0
  have hlin : (∫ ω, G ω ∂(slotLaw d N p)) = a + ∫ ω, E ω ∂(slotLaw d N p) := by
    show (∫ ω, a + E ω ∂(slotLaw d N p)) = a + ∫ ω, E ω ∂(slotLaw d N p)
    rw [integral_add (f := fun _ => a) (g := E) (integrable_const a) hEi, integral_const,
      probReal_univ, one_smul]
  refine ⟨hFi, ?_⟩
  calc (∫ ω, potential f μ xstar (qStepSched n hnN L μ θ g h k s ω) ∂(slotLaw d N p))
      = ∫ ω, F ω ∂(slotLaw d N p) := rfl
    _ ≤ ∫ ω, G ω ∂(slotLaw d N p) := integral_mono hFi hGi hpath
    _ = a + ∫ ω, E ω ∂(slotLaw d N p) := hlin
    _ = a + cv * ∫ ω, ‖xi ω‖ ^ 2 ∂(slotLaw d N p) := by rw [hEint]
    _ ≤ a + cv * (4 * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (n k)))) := by linarith
    _ = (1 - θ / 2) * potential f μ xstar s + 2 * (3 / (4 * L) + 2 * θ / μ) * B
          + (1 / (2 * L) + θ ^ 2 / μ) * (4 * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (n k)))) := by
          show (1 - θ / 2) * potential f μ xstar s + cb * B
              + cv * (4 * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (n k)))) = _
          rw [hcvdef, hcbdef]

/-- `K` four-point rounds contract the momentum potential geometrically and pay the centered error
sum: the noise enters with `1 / (2 * L) + θ ^ 2 / μ`, the bias with the Young factor. -/
lemma q_sched_potential {d N : ℕ} {n : ℕ → ℕ} (hnN : ∀ k, 2 * n k ≤ N) (hn : ∀ k, 0 < n k)
    {B : ℝ} {g : Point d → Ω → ℝ} {f : Point d → ℝ} {σ L μ h θ : ℝ} {xstar : Point d}
    (hh : 0 < h) (hL : 0 < L) (hμ : 0 < μ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hθL : 16 * L * θ ^ 2 ≤ μ)
    (hbias : ∀ y, ‖qDiff h f y - gradient f y‖ ^ 2 ≤ B)
    (hg : Measurable (Function.uncurry g))
    (hgi : ∀ x, Integrable (g x) p)
    (hmean : ∀ x, (∫ ω, g x ω ∂p) = f x)
    (hvi : ∀ x, Integrable (fun ω => (g x ω - f x) ^ 2) p)
    (hv : ∀ x, (∫ ω, (g x ω - f x) ^ 2 ∂p) ≤ σ ^ 2)
    (hc : ConvexOn ℝ Set.univ f)
    (hgr : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hsc : ∀ x y, f x + ⟪gradient f x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (hmin : IsMinOn f Set.univ xstar)
    (i K : ℕ) (s : Point d × Point d) :
    Integrable (fun Ξ => potential f μ xstar
        (runSched (fun k s' ω => qStepSched n hnN L μ θ g h k s' ω) i K s Ξ))
        (Measure.pi (fun _ : Fin K => slotLaw d N p)) ∧
      (∫ Ξ, potential f μ xstar
        (runSched (fun k s' ω => qStepSched n hnN L μ θ g h k s' ω) i K s Ξ)
        ∂Measure.pi (fun _ : Fin K => slotLaw d N p)) ≤
      (1 - θ / 2) ^ K * potential f μ xstar s
        + ∑ k ∈ Finset.range K, (1 - θ / 2) ^ (K - 1 - k)
            * (2 * (3 / (4 * L) + 2 * θ / μ) * B
              + (1 / (2 * L) + θ ^ 2 / μ) * (4 * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (n (i + k)))))) := by
  classical
  have hf : Measurable f :=
    (continuous_iff_continuousAt.mpr fun x => (hgr x).continuousAt).measurable
  have hVnonneg : ∀ t : Point d × Point d, 0 ≤ potential f μ xstar t := by
    intro t
    have hminf : ∀ x, f xstar ≤ f x := fun x => hmin (Set.mem_univ x)
    show 0 ≤ f t.1 - f xstar + μ / 4 * ‖t.2 - xstar‖ ^ 2
    exact add_nonneg (sub_nonneg.mpr (hminf t.1)) (mul_nonneg (by positivity) (sq_nonneg _))
  have hrho : 0 ≤ (1 : ℝ) - θ / 2 := by linarith
  have hB0 : 0 ≤ B := by
    have hbe := hbias xstar
    have h2 : (0 : ℝ) ≤ ‖qDiff h f xstar - gradient f xstar‖ ^ 2 := by positivity
    linarith
  refine sched_iterate_accuracy (d := d) (M := N)
    (step := fun k s' ω => qStepSched n hnN L μ θ g h k s' ω) (ρ := (1 : ℝ) - θ / 2)
    (c := fun k => 2 * (3 / (4 * L) + 2 * θ / μ) * B
      + (1 / (2 * L) + θ ^ 2 / μ) * (4 * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (n k)))))
    (fun k => measurable_qStepSched_joint n hnN hg L μ θ h k)
    ⟨slotLaw d N p, inferInstance⟩ (potential f μ xstar) (measurable_potentialZO hf) hVnonneg hrho
    (fun k => by positivity)
    (fun k s' =>
      have h1 := q_one_step (n := n) hnN hn hh hL hμ hθ0 hθ1 hθL hbias hg hgi hmean hvi hv
        hc hgr hlip hsc hmin k s'
      ⟨h1.1, h1.2.trans (le_of_eq (add_assoc _ _ _))⟩) i K s

/-- `K` four-point rounds bound the expected suboptimality of the momentum output. -/
lemma q_sched_gap {d N : ℕ} {n : ℕ → ℕ} (hnN : ∀ k, 2 * n k ≤ N) (hn : ∀ k, 0 < n k)
    {B : ℝ} {g : Point d → Ω → ℝ} {f : Point d → ℝ} {σ L μ h θ : ℝ} {xstar : Point d}
    (hh : 0 < h) (hL : 0 < L) (hμ : 0 < μ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hθL : 16 * L * θ ^ 2 ≤ μ)
    (hbias : ∀ y, ‖qDiff h f y - gradient f y‖ ^ 2 ≤ B)
    (hg : Measurable (Function.uncurry g))
    (hgi : ∀ x, Integrable (g x) p)
    (hmean : ∀ x, (∫ ω, g x ω ∂p) = f x)
    (hvi : ∀ x, Integrable (fun ω => (g x ω - f x) ^ 2) p)
    (hv : ∀ x, (∫ ω, (g x ω - f x) ^ 2 ∂p) ≤ σ ^ 2)
    (hc : ConvexOn ℝ Set.univ f)
    (hgr : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hsc : ∀ x y, f x + ⟪gradient f x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (hmin : IsMinOn f Set.univ xstar)
    (x0 : Point d) (K : ℕ) :
    Integrable (fun Ξ : Fin K → secantSpace d N → Ω =>
        f (runSched (fun k s' ω => qStepSched n hnN L μ θ g h k s' ω) 0 K (x0, x0) Ξ).1
          - f xstar) (Measure.pi (fun _ : Fin K => slotLaw d N p)) ∧
      (∫ Ξ, f (runSched (fun k s' ω => qStepSched n hnN L μ θ g h k s' ω) 0 K (x0, x0) Ξ).1
        - f xstar ∂Measure.pi (fun _ : Fin K => slotLaw d N p)) ≤
      (1 - θ / 2) ^ K * (f x0 - f xstar + μ / 4 * ‖x0 - xstar‖ ^ 2)
        + ∑ k ∈ Finset.range K, (1 - θ / 2) ^ (K - 1 - k)
            * (2 * (3 / (4 * L) + 2 * θ / μ) * B
              + (1 / (2 * L) + θ ^ 2 / μ) * (4 * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (n k))))) := by
  classical
  have hminf : ∀ x, f xstar ≤ f x := fun x => hmin (Set.mem_univ x)
  have hf : Measurable f :=
    (continuous_iff_continuousAt.mpr fun x => (hgr x).continuousAt).measurable
  obtain ⟨hIf, hb⟩ := q_sched_potential (d := d) (n := n) hnN hn (B := B) (g := g) (f := f)
    (σ := σ) (L := L) (μ := μ) (h := h) (θ := θ) (xstar := xstar) hh hL hμ hθ0 hθ1 hθL hbias hg
    hgi hmean hvi hv hc hgr hlip hsc hmin (i := 0) (K := K) (s := (x0, x0))
  simp only [Nat.zero_add] at hb
  have hrun2 : Measurable ((fun q : (Point d × Point d) × (Fin K → secantSpace d N → Ω) =>
      runSched (fun k s' ω => qStepSched n hnN L μ θ g h k s' ω) 0 K q.1 q.2) ∘
      (fun Ξ : Fin K → secantSpace d N → Ω => ((x0, x0), Ξ))) :=
    (measurable_runSched (fun k => measurable_qStepSched_joint n hnN hg L μ θ h k) K 0).comp
      (measurable_const.prodMk measurable_id)
  have hf1 : Measurable (fun p : Point d × Point d => p.1) := continuous_fst.measurable
  have hgapMeas : Measurable ((fun v : Point d => f v - f xstar) ∘
      (fun p : Point d × Point d => p.1) ∘
      (fun Ξ : Fin K → secantSpace d N → Ω =>
        runSched (fun k s' ω => qStepSched n hnN L μ θ g h k s' ω) 0 K (x0, x0) Ξ)) :=
    (hf.sub measurable_const).comp (hf1.comp hrun2)
  have hpoint : ∀ Ξ : Fin K → secantSpace d N → Ω,
      f (runSched (fun k s' ω => qStepSched n hnN L μ θ g h k s' ω) 0 K (x0, x0) Ξ).1
          - f xstar
        ≤ potential f μ xstar
          (runSched (fun k s' ω => qStepSched n hnN L μ θ g h k s' ω) 0 K (x0, x0) Ξ) :=
    fun Ξ => le_add_of_nonneg_right (mul_nonneg (by positivity) (sq_nonneg _))
  have hgapInt : Integrable (fun Ξ : Fin K → secantSpace d N → Ω =>
      f (runSched (fun k s' ω => qStepSched n hnN L μ θ g h k s' ω) 0 K (x0, x0) Ξ).1
        - f xstar) (Measure.pi (fun _ : Fin K => slotLaw d N p)) :=
    hIf.mono' hgapMeas.aestronglyMeasurable (ae_of_all _ fun Ξ => by
      have h0 : 0 ≤
          f (runSched (fun k s' ω => qStepSched n hnN L μ θ g h k s' ω) 0 K (x0, x0) Ξ).1
            - f xstar := sub_nonneg.mpr (hminf _)
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact hpoint Ξ)
  exact ⟨hgapInt, (integral_mono hgapInt hIf hpoint).trans hb⟩

end OracleTemplate.SecantPolyak.QuinticStencil

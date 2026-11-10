import LongTails.Proofs.CentralStencilStream
import LongTails.Proofs.DecicStencilEstimator

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

/-!
Stream analysis of the ten-point coordinate stencil inside the damped anchored momentum schedule.
One round draws `5 * n` central replicas from the slot block and decodes them by the Richardson
combination `3 / 2 • central h - 3 / 5 • central (2 * h) + 1 / 10 • central (3 * h)`. The reply is
centered at the ten-point secant and its mean-square noise is at most `6 * d * σ ^ 2 / (h ^ 2 * n)`,
the same noise coefficient as the two-point central stencil, while the squared bias drops to
`d * (rho6 * h ^ 6) ^ 2`.
-/
namespace OracleTemplate.SecantPolyak.DecicStencil

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
open OracleTemplate
open OracleTemplate.SecantPolyak.Centered
open OracleTemplate.SecantPolyak.CentralStencil
open SecantDescent SecantPolyak SecantPolyak.Accelerated ZerothOrder InexactGradient Scheduled
open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {Ω : Type} [_ms : MeasurableSpace Ω] {p : Measure Ω} [_ip : IsProbabilityMeasure p]

/-- Linearity of the Bochner integral on the Richardson combination of five vector-valued
functions. -/
lemma integral_richardson5 {d : ℕ} {α : Type} [mα : MeasurableSpace α] {μ : Measure α}
    {f₁ f₂ f₃ f₄ f₅ : α → Point d} (c₁ c₂ c₃ c₄ c₅ : ℝ)
    (h₁ : Integrable f₁ μ) (h₂ : Integrable f₂ μ) (h₃ : Integrable f₃ μ)
    (h₄ : Integrable f₄ μ) (h₅ : Integrable f₅ μ) :
    (∫ a, c₁ • f₁ a - c₂ • f₂ a + c₃ • f₃ a - c₄ • f₄ a + c₅ • f₅ a ∂μ)
      = c₁ • ∫ a, f₁ a ∂μ - c₂ • ∫ a, f₂ a ∂μ + c₃ • ∫ a, f₃ a ∂μ - c₄ • ∫ a, f₄ a ∂μ
          + c₅ • ∫ a, f₅ a ∂μ := by
  have h1 : Integrable (fun x => c₁ • f₁ x) μ := h₁.smul c₁
  have h2 : Integrable (fun x => c₂ • f₂ x) μ := h₂.smul c₂
  have h3 : Integrable (fun x => c₃ • f₃ x) μ := h₃.smul c₃
  have h4 : Integrable (fun x => c₄ • f₄ x) μ := h₄.smul c₄
  have h5 : Integrable (fun x => c₅ • f₅ x) μ := h₅.smul c₅
  have h12 : Integrable (fun x => c₁ • f₁ x - c₂ • f₂ x) μ := h1.sub h2
  have h123 : Integrable (fun x => c₁ • f₁ x - c₂ • f₂ x + c₃ • f₃ x) μ := h12.add h3
  have h1234 : Integrable (fun x => c₁ • f₁ x - c₂ • f₂ x + c₃ • f₃ x - c₄ • f₄ x) μ :=
    h123.sub h4
  rw [integral_add h1234 h5, integral_sub h123 h4, integral_add h12 h3, integral_sub h1 h2,
    integral_smul, integral_smul, integral_smul, integral_smul, integral_smul]

/-- Linearity of the Lebesgue integral on a combination of five real-valued functions. -/
lemma integral_lin5 {α : Type} [mα : MeasurableSpace α] {μ : Measure α}
    {f₁ f₂ f₃ f₄ f₅ : α → ℝ} (c₁ c₂ c₃ c₄ c₅ : ℝ)
    (h₁ : Integrable f₁ μ) (h₂ : Integrable f₂ μ) (h₃ : Integrable f₃ μ)
    (h₄ : Integrable f₄ μ) (h₅ : Integrable f₅ μ) :
    (∫ a, c₁ * f₁ a + c₂ * f₂ a + c₃ * f₃ a + c₄ * f₄ a + c₅ * f₅ a ∂μ)
      = c₁ * ∫ a, f₁ a ∂μ + c₂ * ∫ a, f₂ a ∂μ + c₃ * ∫ a, f₃ a ∂μ + c₄ * ∫ a, f₄ a ∂μ
          + c₅ * ∫ a, f₅ a ∂μ := by
  have h1 : Integrable (fun x => c₁ * f₁ x) μ := h₁.const_mul c₁
  have h2 : Integrable (fun x => c₂ * f₂ x) μ := h₂.const_mul c₂
  have h3 : Integrable (fun x => c₃ * f₃ x) μ := h₃.const_mul c₃
  have h4 : Integrable (fun x => c₄ * f₄ x) μ := h₄.const_mul c₄
  have h5 : Integrable (fun x => c₅ * f₅ x) μ := h₅.const_mul c₅
  have h12 : Integrable (fun x => c₁ * f₁ x + c₂ * f₂ x) μ := h1.add h2
  have h123 : Integrable (fun x => c₁ * f₁ x + c₂ * f₂ x + c₃ * f₃ x) μ := h12.add h3
  have h1234 : Integrable (fun x => c₁ * f₁ x + c₂ * f₂ x + c₃ * f₃ x + c₄ * f₄ x) μ :=
    h123.add h4
  rw [integral_add h1234 h5, integral_add h123 h4, integral_add h12 h3, integral_add h1 h2,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul]

/-- Reply of one scheduled ten-point round: the five replica bands of the slot block are decoded
by the Richardson combination
`5 / 3 • central h - 20 / 21 • central (2 * h) + 5 / 14 • central (3 * h)
   - 5 / 63 • central (4 * h) + 1 / 126 • central (5 * h)`.
-/
noncomputable def dxReplyS {d n N : ℕ} (hnN : 5 * n ≤ N) (g : Point d → Ω → ℝ) (h : ℝ)
    (x : Point d) (ω : secantSpace d N → Ω) : Point d :=
  dxReply g h x (dxCellsLow (fun t : secantSpace d (5 * n) => ω (cellInj hnN t)))
    (dxCellsMid (fun t : secantSpace d (5 * n) => ω (cellInj hnN t)))
    (dxCellsHigh (fun t : secantSpace d (5 * n) => ω (cellInj hnN t)))
    (dxCellsTop (fun t : secantSpace d (5 * n) => ω (cellInj hnN t)))
    (dxCellsFive (fun t : secantSpace d (5 * n) => ω (cellInj hnN t)))

/-- One scheduled ten-point round: momentum extrapolation, then the ten-point stencil at the
momentum probe point. -/
noncomputable def dxStepSched {d N : ℕ} (n : ℕ → ℕ) (hnN : ∀ k, 5 * n k ≤ N)
    (L μ θ : ℝ) (g : Point d → Ω → ℝ) (h : ℝ) (k : ℕ) (s : Point d × Point d)
    (ω : secantSpace d N → Ω) : Point d × Point d :=
  step L μ θ s (dxReplyS (hnN k) g h (query θ s) ω)

/-- The ten-point reply of a round is the Richardson combination of the five fifth-batch replies. -/
lemma dxReplyS_apply {d n N : ℕ} (hnN : 5 * n ≤ N) (g : Point d → Ω → ℝ) (h : ℝ) (x : Point d)
    (ω : secantSpace d N → Ω) :
    dxReplyS hnN g h x ω =
      ((5 : ℝ) / 3) • cReply g h x (dxCellsLow (fun t : secantSpace d (5 * n) => ω (cellInj hnN t))) -
        ((20 : ℝ) / 21) • cReply g (2 * h) x (dxCellsMid (fun t : secantSpace d (5 * n) => ω (cellInj hnN t))) +
          ((5 : ℝ) / 14) • cReply g (3 * h) x (dxCellsHigh (fun t : secantSpace d (5 * n) => ω (cellInj hnN t))) -
          ((5 : ℝ) / 63) • cReply g (4 * h) x (dxCellsTop (fun t : secantSpace d (5 * n) => ω (cellInj hnN t))) +
          ((1 : ℝ) / 126) • cReply g (5 * h) x (dxCellsFive (fun t : secantSpace d (5 * n) => ω (cellInj hnN t))) := rfl

/-- The first fifth of an ambient slot block depends measurably on the block. -/
lemma measurable_dxCellsLowAmb {d n N : ℕ} (hnN : 5 * n ≤ N) :
    Measurable (fun ω : secantSpace d N → Ω =>
        dxCellsLow (fun t : secantSpace d (5 * n) => ω (cellInj hnN t))) := by
  classical
  have hr : Measurable (fun ω : secantSpace d N → Ω =>
      fun t : secantSpace d (5 * n) => ω (cellInj hnN t)) :=
    measurable_pi_iff.mpr fun t => measurable_pi_apply (cellInj hnN t)
  have hc : Measurable (fun ξ : secantSpace d (5 * n) → Ω => dxCellsLow ξ) :=
    measurable_dxCellsLow
  show Measurable ((fun ξ : secantSpace d (5 * n) → Ω => dxCellsLow ξ) ∘
    (fun ω : secantSpace d N → Ω => fun t : secantSpace d (5 * n) => ω (cellInj hnN t)))
  exact hc.comp hr

/-- The second fifth of an ambient slot block depends measurably on the block. -/
lemma measurable_dxCellsMidAmb {d n N : ℕ} (hnN : 5 * n ≤ N) :
    Measurable (fun ω : secantSpace d N → Ω =>
        dxCellsMid (fun t : secantSpace d (5 * n) => ω (cellInj hnN t))) := by
  classical
  have hr : Measurable (fun ω : secantSpace d N → Ω =>
      fun t : secantSpace d (5 * n) => ω (cellInj hnN t)) :=
    measurable_pi_iff.mpr fun t => measurable_pi_apply (cellInj hnN t)
  have hc : Measurable (fun ξ : secantSpace d (5 * n) → Ω => dxCellsMid ξ) :=
    measurable_dxCellsMid
  show Measurable ((fun ξ : secantSpace d (5 * n) → Ω => dxCellsMid ξ) ∘
    (fun ω : secantSpace d N → Ω => fun t : secantSpace d (5 * n) => ω (cellInj hnN t)))
  exact hc.comp hr

/-- The third fifth of an ambient slot block depends measurably on the block. -/
lemma measurable_dxCellsHighAmb {d n N : ℕ} (hnN : 5 * n ≤ N) :
    Measurable (fun ω : secantSpace d N → Ω =>
        dxCellsHigh (fun t : secantSpace d (5 * n) => ω (cellInj hnN t))) := by
  classical
  have hr : Measurable (fun ω : secantSpace d N → Ω =>
      fun t : secantSpace d (5 * n) => ω (cellInj hnN t)) :=
    measurable_pi_iff.mpr fun t => measurable_pi_apply (cellInj hnN t)
  have hc : Measurable (fun ξ : secantSpace d (5 * n) → Ω => dxCellsHigh ξ) :=
    measurable_dxCellsHigh
  show Measurable ((fun ξ : secantSpace d (5 * n) → Ω => dxCellsHigh ξ) ∘
    (fun ω : secantSpace d N → Ω => fun t : secantSpace d (5 * n) => ω (cellInj hnN t)))
  exact hc.comp hr
lemma measurable_dxCellsFiveAmb {d n N : ℕ} (hnN : 5 * n ≤ N) :
    Measurable (fun ω : secantSpace d N → Ω =>
        dxCellsFive (fun t : secantSpace d (5 * n) => ω (cellInj hnN t))) := by
  classical
  have hr : Measurable (fun ω : secantSpace d N → Ω =>
      fun t : secantSpace d (5 * n) => ω (cellInj hnN t)) :=
    measurable_pi_iff.mpr fun t => measurable_pi_apply (cellInj hnN t)
  have hc : Measurable (fun ξ : secantSpace d (5 * n) → Ω => dxCellsFive ξ) :=
    measurable_dxCellsFive
  show Measurable ((fun ξ : secantSpace d (5 * n) → Ω => dxCellsFive ξ) ∘
    (fun ω : secantSpace d N → Ω => fun t : secantSpace d (5 * n) => ω (cellInj hnN t)))
  exact hc.comp hr

lemma measurable_dxCellsTopAmb {d n N : ℕ} (hnN : 5 * n ≤ N) :
    Measurable (fun ω : secantSpace d N → Ω =>
        dxCellsTop (fun t : secantSpace d (5 * n) => ω (cellInj hnN t))) := by
  classical
  have hr : Measurable (fun ω : secantSpace d N → Ω =>
      fun t : secantSpace d (5 * n) => ω (cellInj hnN t)) :=
    measurable_pi_iff.mpr fun t => measurable_pi_apply (cellInj hnN t)
  have hc : Measurable (fun ξ : secantSpace d (5 * n) → Ω => dxCellsTop ξ) :=
    measurable_dxCellsTop
  show Measurable ((fun ξ : secantSpace d (5 * n) → Ω => dxCellsTop ξ) ∘
    (fun ω : secantSpace d N → Ω => fun t : secantSpace d (5 * n) => ω (cellInj hnN t)))
  exact hc.comp hr

/-- The ten-point reply of a round is measurable at a fixed base point. -/
lemma measurable_dxReplyS_at {d n N : ℕ} (hnN : 5 * n ≤ N) {g : Point d → Ω → ℝ}
    (hg : Measurable (Function.uncurry g)) (h : ℝ) (x : Point d) :
    Measurable (fun ω : secantSpace d N → Ω => dxReplyS hnN g h x ω) := by
  classical
  have h1 : Measurable (fun ω : secantSpace d N → Ω =>
      cReply g h x (dxCellsLow (fun t : secantSpace d (5 * n) => ω (cellInj hnN t)))) :=
    (measurable_cReply_at hg h x).comp (measurable_dxCellsLowAmb hnN)
  have h2 : Measurable (fun ω : secantSpace d N → Ω =>
      cReply g (2 * h) x (dxCellsMid (fun t : secantSpace d (5 * n) => ω (cellInj hnN t)))) :=
    (measurable_cReply_at hg (2 * h) x).comp (measurable_dxCellsMidAmb hnN)
  have h3 : Measurable (fun ω : secantSpace d N → Ω =>
      cReply g (3 * h) x (dxCellsHigh (fun t : secantSpace d (5 * n) => ω (cellInj hnN t)))) :=
    (measurable_cReply_at hg (3 * h) x).comp (measurable_dxCellsHighAmb hnN)
  have h4 : Measurable (fun ω : secantSpace d N → Ω =>
      cReply g (4 * h) x (dxCellsTop (fun t : secantSpace d (5 * n) => ω (cellInj hnN t)))) :=
    (measurable_cReply_at hg (4 * h) x).comp (measurable_dxCellsTopAmb hnN)
  have h5 : Measurable (fun ω : secantSpace d N → Ω =>
      cReply g (5 * h) x (dxCellsFive (fun t : secantSpace d (5 * n) => ω (cellInj hnN t)))) :=
    (measurable_cReply_at hg (5 * h) x).comp (measurable_dxCellsFiveAmb hnN)
  show Measurable (fun ω : secantSpace d N → Ω =>
      ((5 : ℝ) / 3) • cReply g h x (dxCellsLow (fun t : secantSpace d (5 * n) => ω (cellInj hnN t))) -
        ((20 : ℝ) / 21) • cReply g (2 * h) x (dxCellsMid (fun t : secantSpace d (5 * n) => ω (cellInj hnN t))) +
          ((5 : ℝ) / 14) • cReply g (3 * h) x (dxCellsHigh (fun t : secantSpace d (5 * n) => ω (cellInj hnN t))) -
          ((5 : ℝ) / 63) • cReply g (4 * h) x (dxCellsTop (fun t : secantSpace d (5 * n) => ω (cellInj hnN t))) +
          ((1 : ℝ) / 126) • cReply g (5 * h) x (dxCellsFive (fun t : secantSpace d (5 * n) => ω (cellInj hnN t))))
  exact ((((smul_measurable measurable_const h1).sub (smul_measurable measurable_const h2)).add
    (smul_measurable measurable_const h3)).sub (smul_measurable measurable_const h4)).add
    (smul_measurable measurable_const h5)

/-- Each replica band of a round is an integrable central reply. -/
lemma dxReplyS_halves_integrable {d n N : ℕ} (hnN : 5 * n ≤ N) {g : Point d → Ω → ℝ}
    {f : Point d → ℝ} (hgi : ∀ x, Integrable (g x) p)
    (hmean : ∀ x, (∫ ω, g x ω ∂p) = f x) (hn : 0 < n) (x : Point d) :
    Integrable (fun ω : secantSpace d N → Ω =>
        cReply g h x (dxCellsLow (fun t : secantSpace d (5 * n) => ω (cellInj hnN t)))) (slotLaw d N p) ∧
      Integrable (fun ω : secantSpace d N → Ω =>
        cReply g (2 * h) x (dxCellsMid (fun t : secantSpace d (5 * n) => ω (cellInj hnN t)))) (slotLaw d N p) ∧
      Integrable (fun ω : secantSpace d N → Ω =>
        cReply g (3 * h) x (dxCellsHigh (fun t : secantSpace d (5 * n) => ω (cellInj hnN t)))) (slotLaw d N p) ∧
      Integrable (fun ω : secantSpace d N → Ω =>
        cReply g (4 * h) x (dxCellsTop (fun t : secantSpace d (5 * n) => ω (cellInj hnN t)))) (slotLaw d N p) ∧
      Integrable (fun ω : secantSpace d N → Ω =>
        cReply g (5 * h) x (dxCellsFive (fun t : secantSpace d (5 * n) => ω (cellInj hnN t)))) (slotLaw d N p) := by
  classical
  have hc1 : Integrable (cReply g h x) (batchLaw d n p) := cReply_integrable hgi hmean hn x
  have hc2 : Integrable (cReply g (2 * h) x) (batchLaw d n p) := cReply_integrable hgi hmean hn x
  have hc3 : Integrable (cReply g (3 * h) x) (batchLaw d n p) := cReply_integrable hgi hmean hn x
  have hc4 : Integrable (cReply g (4 * h) x) (batchLaw d n p) := cReply_integrable hgi hmean hn x
  have hc5 : Integrable (cReply g (5 * h) x) (batchLaw d n p) := cReply_integrable hgi hmean hn x
  have hp1 := measurePreserving_dxCellsLow_ambient (Ω := Ω) (p := p) (d := d) (n := n) (N := N) hnN
  have hp2 := measurePreserving_dxCellsMid_ambient (Ω := Ω) (p := p) (d := d) (n := n) (N := N) hnN
  have hp3 := measurePreserving_dxCellsHigh_ambient (Ω := Ω) (p := p) (d := d) (n := n) (N := N) hnN
  have hp4 := measurePreserving_dxCellsTop_ambient (Ω := Ω) (p := p) (d := d) (n := n) (N := N) hnN
  have hp5 := measurePreserving_dxCellsFive_ambient (Ω := Ω) (p := p) (d := d) (n := n) (N := N) hnN
  exact ⟨hp1.integrable_comp_of_integrable (ε := Point d) hc1,
    hp2.integrable_comp_of_integrable (ε := Point d) hc2,
    hp3.integrable_comp_of_integrable (ε := Point d) hc3,
    hp4.integrable_comp_of_integrable (ε := Point d) hc4,
    hp5.integrable_comp_of_integrable (ε := Point d) hc5⟩

/-- The ten-point reply of a round is integrable. -/
lemma dxReplyS_integrable {d n N : ℕ} (hnN : 5 * n ≤ N) {g : Point d → Ω → ℝ} {f : Point d → ℝ}
    (hgi : ∀ x, Integrable (g x) p) (hmean : ∀ x, (∫ ω, g x ω ∂p) = f x)
    (hn : 0 < n) (x : Point d) : Integrable (dxReplyS hnN g h x) (slotLaw d N p) := by
  classical
  obtain ⟨h1, h2, h3, h4, h5⟩ := dxReplyS_halves_integrable (h := h) hnN hgi hmean hn x
  refine (((((Integrable.smul ((5 : ℝ) / 3) h1).sub (Integrable.smul ((20 : ℝ) / 21) h2)).add
    (Integrable.smul ((5 : ℝ) / 14) h3)).sub (Integrable.smul ((5 : ℝ) / 63) h4)).add
    (Integrable.smul ((1 : ℝ) / 126) h5)).congr
    (ae_of_all _ fun ω => (dxReplyS_apply hnN g h x ω).symm)

/-- The mean of the ten-point reply of a round is the ten-point secant. -/
lemma dxReplyS_mean {d n N : ℕ} (hnN : 5 * n ≤ N) {g : Point d → Ω → ℝ} {f : Point d → ℝ} {h : ℝ}
    (hgi : ∀ x, Integrable (g x) p) (hmean : ∀ x, (∫ ω, g x ω ∂p) = f x)
    (hn : 0 < n) (x : Point d) :
    (∫ ω : secantSpace d N → Ω, dxReplyS hnN g h x ω ∂(slotLaw d N p)) = dxDiff h f x := by
  classical
  obtain ⟨h1, h2, h3, h4, h5⟩ := dxReplyS_halves_integrable (h := h) hnN hgi hmean hn x
  have hc1 : Integrable (cReply g h x) (batchLaw d n p) := cReply_integrable hgi hmean hn x
  have hc2 : Integrable (cReply g (2 * h) x) (batchLaw d n p) := cReply_integrable hgi hmean hn x
  have hc3 : Integrable (cReply g (3 * h) x) (batchLaw d n p) := cReply_integrable hgi hmean hn x
  have hc4 : Integrable (cReply g (4 * h) x) (batchLaw d n p) := cReply_integrable hgi hmean hn x
  have hc5 : Integrable (cReply g (5 * h) x) (batchLaw d n p) := cReply_integrable hgi hmean hn x
  have he1 : (∫ ω : secantSpace d N → Ω,
      cReply g h x (dxCellsLow (fun t : secantSpace d (5 * n) => ω (cellInj hnN t))) ∂(slotLaw d N p)) = cDiff h f x := by
    have hpm := measurePreserving_dxCellsLow_ambient (Ω := Ω) (p := p) (d := d) (n := n) (N := N) hnN
    rw [integral_comp_preserving_point hpm hc1]
    exact cReply_mean (d := d) (m := n) (g := g) (f := f) (h := h) hgi hmean hn x
  have he2 : (∫ ω : secantSpace d N → Ω,
      cReply g (2 * h) x (dxCellsMid (fun t : secantSpace d (5 * n) => ω (cellInj hnN t))) ∂(slotLaw d N p)) = cDiff (2 * h) f x := by
    have hpm := measurePreserving_dxCellsMid_ambient (Ω := Ω) (p := p) (d := d) (n := n) (N := N) hnN
    rw [integral_comp_preserving_point hpm hc2]
    exact cReply_mean (d := d) (m := n) (g := g) (f := f) (h := 2 * h) hgi hmean hn x
  have he3 : (∫ ω : secantSpace d N → Ω,
      cReply g (3 * h) x (dxCellsHigh (fun t : secantSpace d (5 * n) => ω (cellInj hnN t))) ∂(slotLaw d N p)) = cDiff (3 * h) f x := by
    have hpm := measurePreserving_dxCellsHigh_ambient (Ω := Ω) (p := p) (d := d) (n := n) (N := N) hnN
    rw [integral_comp_preserving_point hpm hc3]
    exact cReply_mean (d := d) (m := n) (g := g) (f := f) (h := 3 * h) hgi hmean hn x
  have he4 : (∫ ω : secantSpace d N → Ω,
      cReply g (4 * h) x (dxCellsTop (fun t : secantSpace d (5 * n) => ω (cellInj hnN t))) ∂(slotLaw d N p)) = cDiff (4 * h) f x := by
    have hpm := measurePreserving_dxCellsTop_ambient (Ω := Ω) (p := p) (d := d) (n := n) (N := N) hnN
    rw [integral_comp_preserving_point hpm hc4]
    exact cReply_mean (d := d) (m := n) (g := g) (f := f) (h := 4 * h) hgi hmean hn x
  have he5 : (∫ ω : secantSpace d N → Ω,
      cReply g (5 * h) x (dxCellsFive (fun t : secantSpace d (5 * n) => ω (cellInj hnN t))) ∂(slotLaw d N p)) = cDiff (5 * h) f x := by
    have hpm := measurePreserving_dxCellsFive_ambient (Ω := Ω) (p := p) (d := d) (n := n) (N := N) hnN
    rw [integral_comp_preserving_point hpm hc5]
    exact cReply_mean (d := d) (m := n) (g := g) (f := f) (h := 5 * h) hgi hmean hn x
  have hsb := integral_richardson5 (μ := slotLaw d N p) ((5 : ℝ) / 3) ((20 : ℝ) / 21)
    ((5 : ℝ) / 14) ((5 : ℝ) / 63) ((1 : ℝ) / 126) h1 h2 h3 h4 h5
  rw [he1, he2, he3, he4, he5] at hsb
  have hsplit := (integral_congr_ae (ae_of_all _ fun ω => (dxReplyS_apply hnN g h x ω))).trans hsb
  rw [hsplit]
  rfl

/-- The mean-square noise of the ten-point reply of a round, measured at the slot level. -/
lemma dxReplyS_deviation {d n N : ℕ} (hnN : 5 * n ≤ N) {g : Point d → Ω → ℝ} {f : Point d → ℝ}
    {σ h : ℝ}
    (hg : Measurable (Function.uncurry g))
    (hgi : ∀ x, Integrable (g x) p)
    (hmean : ∀ x, (∫ ω, g x ω ∂p) = f x)
    (hvi : ∀ x, Integrable (fun ω => (g x ω - f x) ^ 2) p)
    (hv : ∀ x, (∫ ω, (g x ω - f x) ^ 2 ∂p) ≤ σ ^ 2)
    (hn : 0 < n) (x : Point d) :
    Integrable (fun ω : secantSpace d N → Ω => ‖dxReplyS hnN g h x ω - dxDiff h f x‖ ^ 2)
        (slotLaw d N p) ∧
      (∫ ω : secantSpace d N → Ω, ‖dxReplyS hnN g h x ω - dxDiff h f x‖ ^ 2 ∂(slotLaw d N p))
        ≤ (6 : ℝ) * ((d : ℝ) * σ ^ 2 / (h ^ 2 * n)) := by
  classical
  obtain ⟨h1i, h1b⟩ := cReply_deviation (d := d) (m := n) (g := g) (h := h) hg hgi hmean hvi hv hn x
  obtain ⟨h2i, h2b⟩ := cReply_deviation (d := d) (m := n) (g := g) (h := 2 * h) hg hgi hmean hvi hv
    hn x
  obtain ⟨h3i, h3b⟩ := cReply_deviation (d := d) (m := n) (g := g) (h := 3 * h) hg hgi hmean hvi hv
    hn x
  obtain ⟨h4i, h4b⟩ := cReply_deviation (d := d) (m := n) (g := g) (h := 4 * h) hg hgi hmean hvi hv
    hn x
  obtain ⟨h5i, h5b⟩ := cReply_deviation (d := d) (m := n) (g := g) (h := 5 * h) hg hgi hmean hvi hv
    hn x
  set F1 : (secantSpace d N → Ω) → ℝ := fun ω =>
    ‖cReply g h x (dxCellsLow (fun t : secantSpace d (5 * n) => ω (cellInj hnN t))) - cDiff h f x‖ ^ 2
  set F2 : (secantSpace d N → Ω) → ℝ := fun ω =>
    ‖cReply g (2 * h) x (dxCellsMid (fun t : secantSpace d (5 * n) => ω (cellInj hnN t))) - cDiff (2 * h) f x‖ ^ 2
  set F3 : (secantSpace d N → Ω) → ℝ := fun ω =>
    ‖cReply g (3 * h) x (dxCellsHigh (fun t : secantSpace d (5 * n) => ω (cellInj hnN t))) - cDiff (3 * h) f x‖ ^ 2
  set F4 : (secantSpace d N → Ω) → ℝ := fun ω =>
    ‖cReply g (4 * h) x (dxCellsTop (fun t : secantSpace d (5 * n) => ω (cellInj hnN t))) - cDiff (4 * h) f x‖ ^ 2
  set F5 : (secantSpace d N → Ω) → ℝ := fun ω =>
    ‖cReply g (5 * h) x (dxCellsFive (fun t : secantSpace d (5 * n) => ω (cellInj hnN t))) - cDiff (5 * h) f x‖ ^ 2
  have hp1 := measurePreserving_dxCellsLow_ambient (Ω := Ω) (p := p) (d := d) (n := n) (N := N) hnN
  have hp2 := measurePreserving_dxCellsMid_ambient (Ω := Ω) (p := p) (d := d) (n := n) (N := N) hnN
  have hp3 := measurePreserving_dxCellsHigh_ambient (Ω := Ω) (p := p) (d := d) (n := n) (N := N) hnN
  have hp4 := measurePreserving_dxCellsTop_ambient (Ω := Ω) (p := p) (d := d) (n := n) (N := N) hnN
  have hp5 := measurePreserving_dxCellsFive_ambient (Ω := Ω) (p := p) (d := d) (n := n) (N := N) hnN
  have hF1i : Integrable F1 (slotLaw d N p) := hp1.integrable_comp_of_integrable (ε := ℝ) h1i
  have hF2i : Integrable F2 (slotLaw d N p) := hp2.integrable_comp_of_integrable (ε := ℝ) h2i
  have hF3i : Integrable F3 (slotLaw d N p) := hp3.integrable_comp_of_integrable (ε := ℝ) h3i
  have hF4i : Integrable F4 (slotLaw d N p) := hp4.integrable_comp_of_integrable (ε := ℝ) h4i
  have hF5i : Integrable F5 (slotLaw d N p) := hp5.integrable_comp_of_integrable (ε := ℝ) h5i
  have ht1 : (∫ ω : secantSpace d N → Ω, F1 ω ∂(slotLaw d N p))
      = ∫ η, ‖cReply g h x η - cDiff h f x‖ ^ 2 ∂(batchLaw d n p) :=
    integral_comp_preserving hp1 h1i
  have ht2 : (∫ ω : secantSpace d N → Ω, F2 ω ∂(slotLaw d N p))
      = ∫ η, ‖cReply g (2 * h) x η - cDiff (2 * h) f x‖ ^ 2 ∂(batchLaw d n p) :=
    integral_comp_preserving hp2 h2i
  have ht3 : (∫ ω : secantSpace d N → Ω, F3 ω ∂(slotLaw d N p))
      = ∫ η, ‖cReply g (3 * h) x η - cDiff (3 * h) f x‖ ^ 2 ∂(batchLaw d n p) :=
    integral_comp_preserving hp3 h3i
  have ht4 : (∫ ω : secantSpace d N → Ω, F4 ω ∂(slotLaw d N p))
      = ∫ η, ‖cReply g (4 * h) x η - cDiff (4 * h) f x‖ ^ 2 ∂(batchLaw d n p) :=
    integral_comp_preserving hp4 h4i
  have ht5 : (∫ ω : secantSpace d N → Ω, F5 ω ∂(slotLaw d N p))
      = ∫ η, ‖cReply g (5 * h) x η - cDiff (5 * h) f x‖ ^ 2 ∂(batchLaw d n p) :=
    integral_comp_preserving hp5 h5i
  have hbd : ∀ ω : secantSpace d N → Ω,
      ‖dxReplyS hnN g h x ω - dxDiff h f x‖ ^ 2 ≤
        ((965 : ℝ) / 189) * F1 ω + ((3860 : ℝ) / 1323) * F2 ω + ((965 : ℝ) / 882) * F3 ω +
          ((965 : ℝ) / 3969) * F4 ω + ((193 : ℝ) / 7938) * F5 ω := by
    intro ω
    have hpw := dxReply_pointwise (d := d) (n := n) (g := g) (f := f) (h := h) x
      (dxCellsLow (fun t : secantSpace d (5 * n) => ω (cellInj hnN t))) (dxCellsMid (fun t : secantSpace d (5 * n) => ω (cellInj hnN t)))
      (dxCellsHigh (fun t : secantSpace d (5 * n) => ω (cellInj hnN t))) (dxCellsTop (fun t : secantSpace d (5 * n) => ω (cellInj hnN t))) (dxCellsFive (fun t : secantSpace d (5 * n) => ω (cellInj hnN t)))
    have hz : dxReplyS hnN g h x ω
        = dxReply g h x (dxCellsLow (fun t : secantSpace d (5 * n) => ω (cellInj hnN t))) (dxCellsMid (fun t : secantSpace d (5 * n) => ω (cellInj hnN t)))
            (dxCellsHigh (fun t : secantSpace d (5 * n) => ω (cellInj hnN t))) (dxCellsTop (fun t : secantSpace d (5 * n) => ω (cellInj hnN t))) (dxCellsFive (fun t : secantSpace d (5 * n) => ω (cellInj hnN t))) := rfl
    have hc : ((193 : ℝ) / 63) * (((5 : ℝ) / 3) * F1 ω + ((20 : ℝ) / 21) * F2 ω +
          ((5 : ℝ) / 14) * F3 ω + ((5 : ℝ) / 63) * F4 ω + ((1 : ℝ) / 126) * F5 ω)
        = ((965 : ℝ) / 189) * F1 ω + ((3860 : ℝ) / 1323) * F2 ω + ((965 : ℝ) / 882) * F3 ω +
          ((965 : ℝ) / 3969) * F4 ω + ((193 : ℝ) / 7938) * F5 ω := by ring
    rw [← hz, hc] at hpw
    exact hpw
  have hsumi : Integrable (fun ω : secantSpace d N → Ω =>
      ((965 : ℝ) / 189) * F1 ω + ((3860 : ℝ) / 1323) * F2 ω + ((965 : ℝ) / 882) * F3 ω +
        ((965 : ℝ) / 3969) * F4 ω + ((193 : ℝ) / 7938) * F5 ω) (slotLaw d N p) :=
    ((((hF1i.const_mul ((965 : ℝ) / 189)).add (hF2i.const_mul ((3860 : ℝ) / 1323))).add
      (hF3i.const_mul ((965 : ℝ) / 882))).add (hF4i.const_mul ((965 : ℝ) / 3969))).add
      (hF5i.const_mul ((193 : ℝ) / 7938))
  have hZmeas : Measurable (fun ω : secantSpace d N → Ω =>
      ‖dxReplyS hnN g h x ω - dxDiff h f x‖ ^ 2) :=
    ((measurable_dxReplyS_at hnN hg h x).sub_const (dxDiff h f x)).norm.pow_const 2
  have hZm : AEStronglyMeasurable
      (fun ω : secantSpace d N → Ω => ‖dxReplyS hnN g h x ω - dxDiff h f x‖ ^ 2) (slotLaw d N p) :=
    hZmeas.aestronglyMeasurable
  have hZi : Integrable (fun ω : secantSpace d N → Ω => ‖dxReplyS hnN g h x ω - dxDiff h f x‖ ^ 2)
      (slotLaw d N p) := by
    refine hsumi.mono hZm (ae_of_all _ fun ω => ?_)
    have hb := hbd ω
    have hM : 0 ≤ ((965 : ℝ) / 189) * F1 ω + ((3860 : ℝ) / 1323) * F2 ω +
        ((965 : ℝ) / 882) * F3 ω + ((965 : ℝ) / 3969) * F4 ω + ((193 : ℝ) / 7938) * F5 ω :=
      by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), abs_of_nonneg hM]
    exact hb
  refine ⟨hZi, ?_⟩
  have hint := integral_lin5 (μ := slotLaw d N p) ((965 : ℝ) / 189) ((3860 : ℝ) / 1323)
    ((965 : ℝ) / 882) ((965 : ℝ) / 3969) ((193 : ℝ) / 7938) hF1i hF2i hF3i hF4i hF5i
  calc (∫ ω : secantSpace d N → Ω, ‖dxReplyS hnN g h x ω - dxDiff h f x‖ ^ 2 ∂(slotLaw d N p))
      ≤ ∫ ω : secantSpace d N → Ω,
            ((965 : ℝ) / 189) * F1 ω + ((3860 : ℝ) / 1323) * F2 ω + ((965 : ℝ) / 882) * F3 ω +
              ((965 : ℝ) / 3969) * F4 ω + ((193 : ℝ) / 7938) * F5 ω ∂(slotLaw d N p) :=
        integral_mono hZi hsumi hbd
    _ = ((965 : ℝ) / 189) * (∫ ω : secantSpace d N → Ω, F1 ω ∂(slotLaw d N p)) +
          ((3860 : ℝ) / 1323) * (∫ ω : secantSpace d N → Ω, F2 ω ∂(slotLaw d N p)) +
          ((965 : ℝ) / 882) * (∫ ω : secantSpace d N → Ω, F3 ω ∂(slotLaw d N p)) +
          ((965 : ℝ) / 3969) * (∫ ω : secantSpace d N → Ω, F4 ω ∂(slotLaw d N p)) +
          ((193 : ℝ) / 7938) * (∫ ω : secantSpace d N → Ω, F5 ω ∂(slotLaw d N p)) := hint
    _ = ((965 : ℝ) / 189) * (∫ η, ‖cReply g h x η - cDiff h f x‖ ^ 2 ∂(batchLaw d n p)) +
          ((3860 : ℝ) / 1323) * (∫ η, ‖cReply g (2 * h) x η - cDiff (2 * h) f x‖ ^ 2
            ∂(batchLaw d n p)) +
          ((965 : ℝ) / 882) * (∫ η, ‖cReply g (3 * h) x η - cDiff (3 * h) f x‖ ^ 2
            ∂(batchLaw d n p)) +
          ((965 : ℝ) / 3969) * (∫ η, ‖cReply g (4 * h) x η - cDiff (4 * h) f x‖ ^ 2
            ∂(batchLaw d n p)) +
          ((193 : ℝ) / 7938) * (∫ η, ‖cReply g (5 * h) x η - cDiff (5 * h) f x‖ ^ 2
            ∂(batchLaw d n p)) := by rw [ht1, ht2, ht3, ht4, ht5]
    _ ≤ ((965 : ℝ) / 189) * ((d : ℝ) * σ ^ 2 / (h ^ 2 * n)) +
          ((3860 : ℝ) / 1323) * ((d : ℝ) * σ ^ 2 / ((2 * h) ^ 2 * n)) +
          ((965 : ℝ) / 882) * ((d : ℝ) * σ ^ 2 / ((3 * h) ^ 2 * n)) +
          ((965 : ℝ) / 3969) * ((d : ℝ) * σ ^ 2 / ((4 * h) ^ 2 * n)) +
          ((193 : ℝ) / 7938) * ((d : ℝ) * σ ^ 2 / ((5 * h) ^ 2 * n)) := by gcongr
    _ ≤ ((965 : ℝ) / 189) * ((d : ℝ) * σ ^ 2 / (h ^ 2 * n)) +
          ((3860 : ℝ) / 1323) * (((1 : ℝ) / 4) * ((d : ℝ) * σ ^ 2 / (h ^ 2 * n))) +
          ((965 : ℝ) / 882) * (((1 : ℝ) / 9) * ((d : ℝ) * σ ^ 2 / (h ^ 2 * n))) +
          ((965 : ℝ) / 3969) * (((1 : ℝ) / 16) * ((d : ℝ) * σ ^ 2 / (h ^ 2 * n))) +
          ((193 : ℝ) / 7938) * (((1 : ℝ) / 25) * ((d : ℝ) * σ ^ 2 / (h ^ 2 * n))) := by
        gcongr
        · exact decic_scale2 d h σ n
        · exact decic_scale3 d h σ n
        · exact decic_scale4 d h σ n
        · exact decic_scale5 d h σ n
    _ ≤ (6 : ℝ) * ((d : ℝ) * σ ^ 2 / (h ^ 2 * n)) := by
        set V : ℝ := (d : ℝ) * σ ^ 2 / (h ^ 2 * (n : ℝ)) with hVdef
        have hv0 : (0 : ℝ) ≤ V := by
          show 0 ≤ (d : ℝ) * σ ^ 2 / (h ^ 2 * (n : ℝ))
          positivity
        have hnum : ((965 : ℝ) / 189) + ((3860 : ℝ) / 1323) * ((1 : ℝ) / 4) +
            ((965 : ℝ) / 882) * ((1 : ℝ) / 9) + ((965 : ℝ) / 3969) * ((1 : ℝ) / 16) +
              ((193 : ℝ) / 7938) * ((1 : ℝ) / 25) ≤ (6 : ℝ) := by
          norm_num
        have hsum : ((965 : ℝ) / 189) * V + ((3860 : ℝ) / 1323) * (((1 : ℝ) / 4) * V) +
            ((965 : ℝ) / 882) * (((1 : ℝ) / 9) * V) + ((965 : ℝ) / 3969) * (((1 : ℝ) / 16) * V) +
              ((193 : ℝ) / 7938) * (((1 : ℝ) / 25) * V)
            = (((965 : ℝ) / 189) + ((3860 : ℝ) / 1323) * ((1 : ℝ) / 4) +
                ((965 : ℝ) / 882) * ((1 : ℝ) / 9) + ((965 : ℝ) / 3969) * ((1 : ℝ) / 16) +
                  ((193 : ℝ) / 7938) * ((1 : ℝ) / 25)) * V := by
          ring
        nlinarith

/-- The reply of round `k` is jointly measurable in state and slots. -/
lemma measurable_dxReplyRound {d N : ℕ} (n : ℕ → ℕ) (hnN : ∀ k, 5 * n k ≤ N)
    {g : Point d → Ω → ℝ} (hg : Measurable (Function.uncurry g)) (θ h : ℝ) (k : ℕ) :
    Measurable (fun q : (Point d × Point d) × (secantSpace d N → Ω) =>
      dxReplyS (hnN k) g h (query θ q.1) q.2) := by
  classical
  have hq : Measurable (fun q : (Point d × Point d) × (secantSpace d N → Ω) => query θ q.1) := by
    have hc : Continuous (fun p : Point d × Point d => (1 / (1 + θ)) • (p.1 + θ • p.2)) := by
      fun_prop
    show Measurable ((fun p : Point d × Point d => (1 / (1 + θ)) • (p.1 + θ • p.2)) ∘
      (fun q : (Point d × Point d) × (secantSpace d N → Ω) => q.1))
    exact hc.measurable.comp measurable_fst
  have h1 : Measurable (fun q : (Point d × Point d) × (secantSpace d N → Ω) =>
      cReply g h (query θ q.1) (dxCellsLow (fun t : secantSpace d (5 * n k) => q.2 (cellInj (hnN k) t)))) := by
    show Measurable
        ((fun pq : Point d × (Fin (n k) → Fin d × Bool → Ω) => cReply g h pq.1 pq.2) ∘
          (fun q : (Point d × Point d) × (secantSpace d N → Ω) =>
            (query θ q.1, dxCellsLow (fun t : secantSpace d (5 * n k) => q.2 (cellInj (hnN k) t)))))
    exact (measurable_cReply_joint hg h).comp
      (hq.prodMk ((measurable_dxCellsLowAmb (hnN k)).comp measurable_snd))
  have h2 : Measurable (fun q : (Point d × Point d) × (secantSpace d N → Ω) =>
      cReply g (2 * h) (query θ q.1) (dxCellsMid (fun t : secantSpace d (5 * n k) => q.2 (cellInj (hnN k) t)))) := by
    show Measurable
        ((fun pq : Point d × (Fin (n k) → Fin d × Bool → Ω) => cReply g (2 * h) pq.1 pq.2) ∘
          (fun q : (Point d × Point d) × (secantSpace d N → Ω) =>
            (query θ q.1, dxCellsMid (fun t : secantSpace d (5 * n k) => q.2 (cellInj (hnN k) t)))))
    exact (measurable_cReply_joint hg ((2 * h))).comp
      (hq.prodMk ((measurable_dxCellsMidAmb (hnN k)).comp measurable_snd))
  have h3 : Measurable (fun q : (Point d × Point d) × (secantSpace d N → Ω) =>
      cReply g (3 * h) (query θ q.1) (dxCellsHigh (fun t : secantSpace d (5 * n k) => q.2 (cellInj (hnN k) t)))) := by
    show Measurable
        ((fun pq : Point d × (Fin (n k) → Fin d × Bool → Ω) => cReply g (3 * h) pq.1 pq.2) ∘
          (fun q : (Point d × Point d) × (secantSpace d N → Ω) =>
            (query θ q.1, dxCellsHigh (fun t : secantSpace d (5 * n k) => q.2 (cellInj (hnN k) t)))))
    exact (measurable_cReply_joint hg ((3 * h))).comp
      (hq.prodMk ((measurable_dxCellsHighAmb (hnN k)).comp measurable_snd))
  have h4 : Measurable (fun q : (Point d × Point d) × (secantSpace d N → Ω) =>
      cReply g (4 * h) (query θ q.1) (dxCellsTop (fun t : secantSpace d (5 * n k) => q.2 (cellInj (hnN k) t)))) := by
    show Measurable
        ((fun pq : Point d × (Fin (n k) → Fin d × Bool → Ω) => cReply g (4 * h) pq.1 pq.2) ∘
          (fun q : (Point d × Point d) × (secantSpace d N → Ω) =>
            (query θ q.1, dxCellsTop (fun t : secantSpace d (5 * n k) => q.2 (cellInj (hnN k) t)))))
    exact (measurable_cReply_joint hg ((4 * h))).comp
      (hq.prodMk ((measurable_dxCellsTopAmb (hnN k)).comp measurable_snd))
  have h5 : Measurable (fun q : (Point d × Point d) × (secantSpace d N → Ω) =>
      cReply g (5 * h) (query θ q.1) (dxCellsFive (fun t : secantSpace d (5 * n k) => q.2 (cellInj (hnN k) t)))) := by
    show Measurable
        ((fun pq : Point d × (Fin (n k) → Fin d × Bool → Ω) => cReply g (5 * h) pq.1 pq.2) ∘
          (fun q : (Point d × Point d) × (secantSpace d N → Ω) =>
            (query θ q.1, dxCellsFive (fun t : secantSpace d (5 * n k) => q.2 (cellInj (hnN k) t)))))
    exact (measurable_cReply_joint hg ((5 * h))).comp
      (hq.prodMk ((measurable_dxCellsFiveAmb (hnN k)).comp measurable_snd))
  show Measurable (fun q : (Point d × Point d) × (secantSpace d N → Ω) =>
      ((5 : ℝ) / 3) • cReply g h (query θ q.1)
          (dxCellsLow (fun t : secantSpace d (5 * n k) => q.2 (cellInj (hnN k) t))) -
        ((20 : ℝ) / 21) • cReply g (2 * h) (query θ q.1)
          (dxCellsMid (fun t : secantSpace d (5 * n k) => q.2 (cellInj (hnN k) t))) +
          ((5 : ℝ) / 14) • cReply g (3 * h) (query θ q.1)
            (dxCellsHigh (fun t : secantSpace d (5 * n k) => q.2 (cellInj (hnN k) t))) -
          ((5 : ℝ) / 63) • cReply g (4 * h) (query θ q.1)
            (dxCellsTop (fun t : secantSpace d (5 * n k) => q.2 (cellInj (hnN k) t))) +
          ((1 : ℝ) / 126) • cReply g (5 * h) (query θ q.1)
            (dxCellsFive (fun t : secantSpace d (5 * n k) => q.2 (cellInj (hnN k) t))))
  exact ((((smul_measurable measurable_const h1).sub (smul_measurable measurable_const h2)).add
    (smul_measurable measurable_const h3)).sub (smul_measurable measurable_const h4)).add
    (smul_measurable measurable_const h5)

/-- The scheduled ten-point step is jointly measurable. -/
lemma measurable_dxStepSched_joint {d N : ℕ} (n : ℕ → ℕ) (hnN : ∀ k, 5 * n k ≤ N)
    {g : Point d → Ω → ℝ} (hg : Measurable (Function.uncurry g)) (L μ θ h : ℝ) (k : ℕ) :
    Measurable (fun q : (Point d × Point d) × (secantSpace d N → Ω) =>
      dxStepSched n hnN L μ θ g h k q.1 q.2) := by
  classical
  have h1 : Measurable (fun q : (Point d × Point d) × (secantSpace d N → Ω) =>
      dxReplyS (hnN k) g h (query θ q.1) q.2) := measurable_dxReplyRound n hnN hg θ h k
  have hstepc : Continuous (fun p : (Point d × Point d) × Point d => step L μ θ p.1 p.2) := by
    show Continuous (fun p : (Point d × Point d) × Point d =>
      ((1 / (1 + θ)) • (p.1.1 + θ • p.1.2) - (1 / L) • p.2,
        (1 - θ) • p.1.2 + θ • ((1 / (1 + θ)) • (p.1.1 + θ • p.1.2)) - (2 * θ / μ) • p.2))
    fun_prop
  have heq : (fun q : (Point d × Point d) × (secantSpace d N → Ω) =>
      dxStepSched n hnN L μ θ g h k q.1 q.2) =
      (fun p : (Point d × Point d) × Point d => step L μ θ p.1 p.2) ∘
        (fun q : (Point d × Point d) × (secantSpace d N → Ω) =>
          (q.1, dxReplyS (hnN k) g h (query θ q.1) q.2)) := by
    funext q
    rfl
  rw [heq]
  exact hstepc.measurable.comp (measurable_fst.prodMk h1)

/-- One ten-point accelerated round: with a stencil whose squared bias is at most `B`, the Lyapunov
decrease holds with the bias factor `2 * (3 / (4 * L) + 2 * θ / μ) * B` and the centered variance
coefficient `1 / (2 * L) + θ ^ 2 / μ` times `4 * d * σ ^ 2 / (h ^ 5 * n k)`. -/
lemma dx_one_step {d N : ℕ} (n : ℕ → ℕ) (hnN : ∀ k, 5 * n k ≤ N) (hn : ∀ k, 0 < n k) {B : ℝ}
    {g : Point d → Ω → ℝ} {f : Point d → ℝ} {σ L μ θ h : ℝ} {xstar : Point d}
    (_hh : 0 < h) (hL : 0 < L) (hμ : 0 < μ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hθL : 16 * L * θ ^ 2 ≤ μ)
    (hbias : ∀ y, ‖dxDiff h f y - gradient f y‖ ^ 2 ≤ B)
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
    Integrable (fun ω => potential f μ xstar (dxStepSched n hnN L μ θ g h k s ω)) (slotLaw d N p) ∧
      (∫ ω, potential f μ xstar (dxStepSched n hnN L μ θ g h k s ω) ∂(slotLaw d N p)) ≤
        (1 - θ / 2) * potential f μ xstar s
          + 2 * (3 / (4 * L) + 2 * θ / μ) * B
          + (1 / (2 * L) + θ ^ 2 / μ) * (6 * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (n k)))) := by
  classical
  have hminf : ∀ x, f xstar ≤ f x := fun x => hmin (Set.mem_univ x)
  have hf : Measurable f :=
    (continuous_iff_continuousAt.mpr fun x => (hgr x).continuousAt).measurable
  set y : Point d := query θ s with hydef
  set v₀ : Point d := dxDiff h f y with hv0def
  set V : (secantSpace d N → Ω) → Point d := fun ω => dxReplyS (hnN k) g h y ω with hVdef
  set xi : (secantSpace d N → Ω) → Point d := fun ω => V ω - v₀ with hxidef
  set c : Point d := -(1 / L) • gradient f (y - (1 / L) • v₀)
      - θ • ((1 - θ) • s.2 + θ • y - (2 * θ / μ) • v₀ - xstar) with hcdef
  set cv : ℝ := 1 / (2 * L) + θ ^ 2 / μ with hcvdef
  set cb : ℝ := 2 * (3 / (4 * L) + 2 * θ / μ) with hcbdef
  set S1 : (secantSpace d N → Ω) → Point d × Point d :=
    (fun r : (Point d × Point d) × (secantSpace d N → Ω) =>
        dxStepSched n hnN L μ θ g h k r.1 r.2) ∘ (fun ω : secantSpace d N → Ω => (s, ω))
    with hS1def
  set F : (secantSpace d N → Ω) → ℝ := potential f μ xstar ∘ S1 with hfdef
  set Lc : Point d →L[ℝ] ℝ := InnerProductSpace.toDual ℝ (Point d) c with hLcdef
  set E : (secantSpace d N → Ω) → ℝ := fun ω => Lc (xi ω) + cv * ‖xi ω‖ ^ 2 with hEdef
  set a : ℝ := (1 - θ / 2) * potential f μ xstar s + cb * B with hadef
  set G : (secantSpace d N → Ω) → ℝ := fun ω => a + E ω with hGdef
  have hreplyi : Integrable V (slotLaw d N p) :=
    dxReplyS_integrable (hnN k) hgi hmean (hn k) y
  have hVnonneg : ∀ t : Point d × Point d, 0 ≤ potential f μ xstar t := by
    intro t
    show 0 ≤ f t.1 - f xstar + μ / 4 * ‖t.2 - xstar‖ ^ 2
    exact add_nonneg (sub_nonneg.mpr (hminf t.1)) (mul_nonneg (by positivity) (sq_nonneg _))
  have hcb0 : 0 ≤ cb := by positivity
  have hcv0 : 0 ≤ cv := by positivity
  have hVm : Measurable V := measurable_dxReplyS_at (hnN k) hg h y
  have hxim : Measurable xi := hVm.sub measurable_const
  have hxii : Integrable xi (slotLaw d N p) := hreplyi.sub (integrable_const _)
  have hVmean : (∫ ω, V ω ∂(slotLaw d N p)) = v₀ := by
    show (∫ ω, dxReplyS (hnN k) g h y ω ∂(slotLaw d N p)) = v₀
    rw [hv0def, hydef]
    exact dxReplyS_mean (hnN k) hgi hmean (hn k) y
  have hxi0 : (∫ ω, xi ω ∂(slotLaw d N p)) = 0 := by
    show (∫ ω, V ω - v₀ ∂(slotLaw d N p)) = 0
    rw [integral_sub hreplyi (integrable_const _), hVmean, integral_const, probReal_univ,
      one_smul, sub_self]
  have hlin0 : (∫ ω, Lc (xi ω) ∂(slotLaw d N p)) = 0 := by
    rw [Lc.integral_comp_comm hxii, hxi0, map_zero]
  have hFm : Measurable F := by
    rw [hfdef, hS1def]
    exact (measurable_potentialZO hf).comp
      ((measurable_dxStepSched_joint n hnN hg L μ θ h k).comp
        (measurable_const.prodMk measurable_id))
  have hdeV : ∀ ω, dxStepSched n hnN L μ θ g h k s ω = step L μ θ s (V ω) := fun _ => rfl
  have hVadd : ∀ ω, V ω = v₀ + xi ω := fun ω => by
    show V ω = v₀ + (V ω - v₀)
    rw [add_comm, sub_add_cancel]
  have hde : ∀ ω, dxStepSched n hnN L μ θ g h k s ω = step L μ θ s (v₀ + xi ω) := fun ω =>
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
    have hw : F ω = potential f μ xstar (dxStepSched n hnN L μ θ g h k s ω) := rfl
    rw [hw, hde ω]
    show potential f μ xstar (step L μ θ s (v₀ + xi ω)) ≤ a + (Lc (xi ω) + cv * ‖xi ω‖ ^ 2)
    linarith
  obtain hdev := dxReplyS_deviation (hnN k) hg hgi hmean hvi hv (hn k) y
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
  have hbnd : (∫ ω, ‖xi ω‖ ^ 2 ∂(slotLaw d N p)) ≤ 6 * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (n k))) := by
    refine hdev.2.trans_eq ?_
    rfl
  have h5 : cv * ∫ ω, ‖xi ω‖ ^ 2 ∂(slotLaw d N p)
      ≤ cv * (6 * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (n k)))) :=
    mul_le_mul_of_nonneg_left hbnd hcv0
  have hlin : (∫ ω, G ω ∂(slotLaw d N p)) = a + ∫ ω, E ω ∂(slotLaw d N p) := by
    show (∫ ω, a + E ω ∂(slotLaw d N p)) = a + ∫ ω, E ω ∂(slotLaw d N p)
    rw [integral_add (f := fun _ => a) (g := E) (integrable_const a) hEi, integral_const,
      probReal_univ, one_smul]
  refine ⟨hFi, ?_⟩
  calc (∫ ω, potential f μ xstar (dxStepSched n hnN L μ θ g h k s ω) ∂(slotLaw d N p))
      = ∫ ω, F ω ∂(slotLaw d N p) := rfl
    _ ≤ ∫ ω, G ω ∂(slotLaw d N p) := integral_mono hFi hGi hpath
    _ = a + ∫ ω, E ω ∂(slotLaw d N p) := hlin
    _ = a + cv * ∫ ω, ‖xi ω‖ ^ 2 ∂(slotLaw d N p) := by rw [hEint]
    _ ≤ a + cv * (6 * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (n k)))) := by linarith
    _ = (1 - θ / 2) * potential f μ xstar s + 2 * (3 / (4 * L) + 2 * θ / μ) * B
          + (1 / (2 * L) + θ ^ 2 / μ) * (6 * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (n k)))) := by
          show (1 - θ / 2) * potential f μ xstar s + cb * B
              + cv * (6 * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (n k)))) = _
          rw [hcvdef, hcbdef]

/-- `K` ten-point rounds contract the momentum potential geometrically and pay the centered error
sum: the noise enters with `1 / (2 * L) + θ ^ 2 / μ`, the bias with the Young factor. -/
lemma dx_sched_potential {d N : ℕ} {n : ℕ → ℕ} (hnN : ∀ k, 5 * n k ≤ N) (hn : ∀ k, 0 < n k)
    {B : ℝ} {g : Point d → Ω → ℝ} {f : Point d → ℝ} {σ L μ h θ : ℝ} {xstar : Point d}
    (hh : 0 < h) (hL : 0 < L) (hμ : 0 < μ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hθL : 16 * L * θ ^ 2 ≤ μ)
    (hbias : ∀ y, ‖dxDiff h f y - gradient f y‖ ^ 2 ≤ B)
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
        (runSched (fun k s' ω => dxStepSched n hnN L μ θ g h k s' ω) i K s Ξ))
        (Measure.pi (fun _ : Fin K => slotLaw d N p)) ∧
      (∫ Ξ, potential f μ xstar
        (runSched (fun k s' ω => dxStepSched n hnN L μ θ g h k s' ω) i K s Ξ)
        ∂Measure.pi (fun _ : Fin K => slotLaw d N p)) ≤
      (1 - θ / 2) ^ K * potential f μ xstar s
        + ∑ k ∈ Finset.range K, (1 - θ / 2) ^ (K - 1 - k)
            * (2 * (3 / (4 * L) + 2 * θ / μ) * B
              + (1 / (2 * L) + θ ^ 2 / μ) * (6 * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (n (i + k)))))) := by
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
    have h2 : (0 : ℝ) ≤ ‖dxDiff h f xstar - gradient f xstar‖ ^ 2 := by positivity
    linarith
  refine sched_iterate_accuracy (d := d) (M := N)
    (step := fun k s' ω => dxStepSched n hnN L μ θ g h k s' ω) (ρ := (1 : ℝ) - θ / 2)
    (c := fun k => 2 * (3 / (4 * L) + 2 * θ / μ) * B
      + (1 / (2 * L) + θ ^ 2 / μ) * (6 * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (n k)))))
    (fun k => measurable_dxStepSched_joint n hnN hg L μ θ h k)
    ⟨slotLaw d N p, inferInstance⟩ (potential f μ xstar) (measurable_potentialZO hf) hVnonneg hrho
    (fun k => by positivity)
    (fun k s' =>
      have h1 := dx_one_step (n := n) hnN hn hh hL hμ hθ0 hθ1 hθL hbias hg hgi hmean hvi hv
        hc hgr hlip hsc hmin k s'
      ⟨h1.1, h1.2.trans (le_of_eq (add_assoc _ _ _))⟩) i K s

/-- `K` ten-point rounds bound the expected suboptimality of the momentum output. -/
lemma dx_sched_gap {d N : ℕ} {n : ℕ → ℕ} (hnN : ∀ k, 5 * n k ≤ N) (hn : ∀ k, 0 < n k)
    {B : ℝ} {g : Point d → Ω → ℝ} {f : Point d → ℝ} {σ L μ h θ : ℝ} {xstar : Point d}
    (hh : 0 < h) (hL : 0 < L) (hμ : 0 < μ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hθL : 16 * L * θ ^ 2 ≤ μ)
    (hbias : ∀ y, ‖dxDiff h f y - gradient f y‖ ^ 2 ≤ B)
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
        f (runSched (fun k s' ω => dxStepSched n hnN L μ θ g h k s' ω) 0 K (x0, x0) Ξ).1
          - f xstar) (Measure.pi (fun _ : Fin K => slotLaw d N p)) ∧
      (∫ Ξ, f (runSched (fun k s' ω => dxStepSched n hnN L μ θ g h k s' ω) 0 K (x0, x0) Ξ).1
        - f xstar ∂Measure.pi (fun _ : Fin K => slotLaw d N p)) ≤
      (1 - θ / 2) ^ K * (f x0 - f xstar + μ / 4 * ‖x0 - xstar‖ ^ 2)
        + ∑ k ∈ Finset.range K, (1 - θ / 2) ^ (K - 1 - k)
            * (2 * (3 / (4 * L) + 2 * θ / μ) * B
              + (1 / (2 * L) + θ ^ 2 / μ) * (6 * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (n k))))) := by
  classical
  have hminf : ∀ x, f xstar ≤ f x := fun x => hmin (Set.mem_univ x)
  have hf : Measurable f :=
    (continuous_iff_continuousAt.mpr fun x => (hgr x).continuousAt).measurable
  obtain ⟨hIf, hb⟩ := dx_sched_potential (d := d) (n := n) hnN hn (B := B) (g := g) (f := f)
    (σ := σ) (L := L) (μ := μ) (h := h) (θ := θ) (xstar := xstar) hh hL hμ hθ0 hθ1 hθL hbias hg
    hgi hmean hvi hv hc hgr hlip hsc hmin (i := 0) (K := K) (s := (x0, x0))
  simp only [Nat.zero_add] at hb
  have hrun2 : Measurable ((fun q : (Point d × Point d) × (Fin K → secantSpace d N → Ω) =>
      runSched (fun k s' ω => dxStepSched n hnN L μ θ g h k s' ω) 0 K q.1 q.2) ∘
      (fun Ξ : Fin K → secantSpace d N → Ω => ((x0, x0), Ξ))) :=
    (measurable_runSched (fun k => measurable_dxStepSched_joint n hnN hg L μ θ h k) K 0).comp
      (measurable_const.prodMk measurable_id)
  have hf1 : Measurable (fun p : Point d × Point d => p.1) := continuous_fst.measurable
  have hgapMeas : Measurable ((fun v : Point d => f v - f xstar) ∘
      (fun p : Point d × Point d => p.1) ∘
      (fun Ξ : Fin K → secantSpace d N → Ω =>
        runSched (fun k s' ω => dxStepSched n hnN L μ θ g h k s' ω) 0 K (x0, x0) Ξ)) :=
    (hf.sub measurable_const).comp (hf1.comp hrun2)
  have hpoint : ∀ Ξ : Fin K → secantSpace d N → Ω,
      f (runSched (fun k s' ω => dxStepSched n hnN L μ θ g h k s' ω) 0 K (x0, x0) Ξ).1
          - f xstar
        ≤ potential f μ xstar
          (runSched (fun k s' ω => dxStepSched n hnN L μ θ g h k s' ω) 0 K (x0, x0) Ξ) :=
    fun Ξ => le_add_of_nonneg_right (mul_nonneg (by positivity) (sq_nonneg _))
  have hgapInt : Integrable (fun Ξ : Fin K → secantSpace d N → Ω =>
      f (runSched (fun k s' ω => dxStepSched n hnN L μ θ g h k s' ω) 0 K (x0, x0) Ξ).1
        - f xstar) (Measure.pi (fun _ : Fin K => slotLaw d N p)) :=
    hIf.mono' hgapMeas.aestronglyMeasurable (ae_of_all _ fun Ξ => by
      have h0 : 0 ≤
          f (runSched (fun k s' ω => dxStepSched n hnN L μ θ g h k s' ω) 0 K (x0, x0) Ξ).1
            - f xstar := sub_nonneg.mpr (hminf _)
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact hpoint Ξ)
  exact ⟨hgapInt, (integral_mono hgapInt hIf hpoint).trans hb⟩

end OracleTemplate.SecantPolyak.DecicStencil

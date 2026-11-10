import LongTails.Proofs.CentralStencilStream
import LongTails.Proofs.BetaStencilEstimator

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

/-!
Stream analysis of the unified `M`-band central Richardson coordinate stencil inside the damped
anchored momentum schedule. One round draws `M * n` central replicas per coordinate from the slot
block and decodes them by `∑ j : Fin M, betaWeight M j • centralDecode ((j + 1) * h)`. The reply is
centered at the `M`-band secant `betaDiff M h` and its mean-square noise is at most
`betaAbs M ^ 2 * d * σ ^ 2 / (h ^ 2 * n)`, while the squared bias is the one allowed by the calling
setup, `d * (rho * h ^ (2 * M)) ^ 2`.
-/
namespace OracleTemplate.SecantPolyak.BetaStencil

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
open OracleTemplate
open OracleTemplate.SecantPolyak.Centered
open OracleTemplate.SecantPolyak.CentralStencil
open SecantDescent SecantPolyak SecantPolyak.Accelerated ZerothOrder InexactGradient Scheduled
open LongTails.Setups.ZerothOrderSmoothAndConvex
open LongTails.Setups.ZerothOrderStronglyConvexBetaBias
open OracleTemplate.Research.BetaStencilMomentumZO

variable {Ω : Type} [_ms : MeasurableSpace Ω] {p : Measure Ω} [_ip : IsProbabilityMeasure p]

/-- Restricting a slot block to an initial segment of slots is measurable. -/
lemma measurable_precomp_cellInj {d m N : ℕ} (hN : m ≤ N) :
    Measurable (fun ω : secantSpace d N → Ω => fun t : secantSpace d m => ω (cellInj hN t)) :=
  measurable_pi_iff.mpr fun t => measurable_pi_apply (cellInj hN t)

/-- Reply of one scheduled `M`-band round: the `M` replica bands of the slot block are decoded by
the Lagrange combination of the symmetric differences at the radii `h, 2 * h, ..., M * h`. -/
noncomputable def betaReplyS {M n N : ℕ} (hnN : M * n ≤ N) (g : Point d → Ω → ℝ) (h : ℝ)
    (x : Point d) (ω : secantSpace d N → Ω) : Point d :=
  betaReply M g h x (fun t : secantSpace d (M * n) => ω (cellInj hnN t))

/-- One scheduled `M`-band round: momentum extrapolation, then the `M`-band stencil at the
momentum probe point. -/
noncomputable def betaStepSched {M d N : ℕ} (n : ℕ → ℕ) (hnN : ∀ k, M * n k ≤ N)
    (L μ θ : ℝ) (g : Point d → Ω → ℝ) (h : ℝ) (k : ℕ) (s : Point d × Point d)
    (ω : secantSpace d N → Ω) : Point d × Point d :=
  step L μ θ s (betaReplyS (M := M) (n := n k) (N := N) (hnN k) g h (query θ s) ω)

/-- One band of the reply as a function of the pair of base point and slots. -/
noncomputable def betaTerm {M n : ℕ} (g : Point d → Ω → ℝ) (h : ℝ) (j : Fin M)
    (q : Point d × (secantSpace d (M * n) → Ω)) : Point d :=
  betaWeight M j • cReply g (((j : ℝ) + 1) * h) q.1 (betaCells j q.2)

/-- One band of the reply is measurable in base point and slots. -/
lemma measurable_betaTerm {M n : ℕ} {g : Point d → Ω → ℝ}
    (hg : Measurable (Function.uncurry g)) (h : ℝ) (j : Fin M) :
    Measurable (fun q : Point d × (secantSpace d (M * n) → Ω) => betaTerm g h j q) := by
  classical
  have he : (fun q : Point d × (secantSpace d (M * n) → Ω) => betaTerm g h j q) =
      (fun q : Point d × (secantSpace d (M * n) → Ω) =>
        betaWeight M j • cReply g (((j : ℝ) + 1) * h) q.1 (betaCells j q.2)) := rfl
  rw [he]
  refine smul_measurable measurable_const ?_
  have hh : (fun q : Point d × (secantSpace d (M * n) → Ω) =>
      cReply g (((j : ℝ) + 1) * h) q.1 (betaCells j q.2))
      = (fun p : Point d × (Fin n → Fin d × Bool → Ω) =>
          cReply g (((j : ℝ) + 1) * h) p.1 p.2) ∘
        (fun q : Point d × (secantSpace d (M * n) → Ω) => (q.1, betaCells j q.2)) := by
    funext q
    rfl
  rw [hh]
  refine (measurable_cReply_joint hg (((j : ℝ) + 1) * h)).comp ?_
  refine Measurable.prodMk ?_ ?_
  · exact measurable_fst
  · exact (measurable_betaCells j).comp measurable_snd

/-- The `M`-band reply is jointly measurable in base point and slots. -/
lemma measurable_betaReply_joint {M n : ℕ} {g : Point d → Ω → ℝ}
    (hg : Measurable (Function.uncurry g)) (h : ℝ) :
    Measurable (fun q : Point d × (secantSpace d (M * n) → Ω) => betaReply M g h q.1 q.2) := by
  classical
  have heq : (fun q : Point d × (secantSpace d (M * n) → Ω) => betaReply M g h q.1 q.2) =
      (fun q : Point d × (secantSpace d (M * n) → Ω) => ∑ j : Fin M, betaTerm g h j q) := by
    funext q
    rfl
  rw [heq]
  exact Finset.measurable_sum Finset.univ (fun j _ => measurable_betaTerm hg h j)

/-- The ambient `M`-band reply of a round is jointly measurable in base point and slots. -/
lemma measurable_betaReplyS_joint {M n N : ℕ} (hnN : M * n ≤ N) {g : Point d → Ω → ℝ}
    (hg : Measurable (Function.uncurry g)) (h : ℝ) :
    Measurable (fun p : Point d × (secantSpace d N → Ω) => betaReplyS hnN g h p.1 p.2) := by
  classical
  set W : Fin M → ((Point d × (secantSpace d N → Ω)) → Point d) := fun j p =>
    betaWeight M j • cReply g (((j : ℝ) + 1) * h) p.1
      (betaCells j (fun t : secantSpace d (M * n) => p.2 (cellInj hnN t))) with hWdef
  have heq : (fun p : Point d × (secantSpace d N → Ω) => betaReplyS hnN g h p.1 p.2) =
      (fun p : Point d × (secantSpace d N → Ω) => ∑ j : Fin M, W j p) := by
    funext p
    rfl
  rw [heq]
  refine Finset.measurable_sum Finset.univ (fun j _ => ?_)
  have h2 : (fun p : Point d × (secantSpace d N → Ω) =>
      cReply g (((j : ℝ) + 1) * h) p.1
        (betaCells j (fun t : secantSpace d (M * n) => p.2 (cellInj hnN t))))
      = (fun q : Point d × (Fin n → Fin d × Bool → Ω) =>
          cReply g (((j : ℝ) + 1) * h) q.1 q.2) ∘
        (fun p : Point d × (secantSpace d N → Ω) =>
          (p.1, betaCells j (fun t : secantSpace d (M * n) => p.2 (cellInj hnN t)))) := by
    funext p
    rfl
  rw [hWdef]
  refine smul_measurable measurable_const ?_
  rw [h2]
  refine (measurable_cReply_joint hg (((j : ℝ) + 1) * h)).comp ?_
  refine Measurable.prodMk ?_ ?_
  · exact measurable_fst
  · show Measurable (fun p : Point d × (secantSpace d N → Ω) =>
        fun i : Fin n => fun r : Fin d × Bool => p.2 (cellInj hnN (bandFin j i, r)))
    refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun r => ?_
    exact (measurable_pi_apply (cellInj hnN (bandFin j i, r))).comp measurable_snd

/-- The `M`-band reply of a round is measurable at a fixed base point. -/
lemma measurable_betaReplyS_at {M n N : ℕ} (hnN : M * n ≤ N) {g : Point d → Ω → ℝ}
    (hg : Measurable (Function.uncurry g)) (h : ℝ) (x : Point d) :
    Measurable (fun ω : secantSpace d N → Ω => betaReplyS hnN g h x ω) := by
  classical
  have hh : (fun ω : secantSpace d N → Ω => betaReplyS hnN g h x ω) =
      (fun p : Point d × (secantSpace d N → Ω) => betaReplyS hnN g h p.1 p.2) ∘
        (fun ω : secantSpace d N → Ω => (x, ω)) := by
    funext ω
    rfl
  rw [hh]
  refine (measurable_betaReplyS_joint hnN hg h).comp ?_
  refine Measurable.prodMk ?_ ?_
  · exact measurable_const
  · exact measurable_id

/-- The reply of round `k` is jointly measurable in state and slots. -/
lemma measurable_betaReplyRound {M d N : ℕ} (n : ℕ → ℕ) (hnN : ∀ k, M * n k ≤ N)
    {g : Point d → Ω → ℝ} (hg : Measurable (Function.uncurry g)) (θ h : ℝ) (k : ℕ) :
    Measurable (fun q : (Point d × Point d) × (secantSpace d N → Ω) =>
      betaReplyS (M := M) (n := n k) (N := N) (hnN k) g h (query θ q.1) q.2) := by
  classical
  have hq : Measurable (fun q : (Point d × Point d) × (secantSpace d N → Ω) => query θ q.1) := by
    have hc : Continuous (fun p : Point d × Point d => (1 / (1 + θ)) • (p.1 + θ • p.2)) := by
      fun_prop
    show Measurable ((fun p : Point d × Point d => (1 / (1 + θ)) • (p.1 + θ • p.2)) ∘
      (fun q : (Point d × Point d) × (secantSpace d N → Ω) => q.1))
    exact hc.measurable.comp measurable_fst
  have hh : (fun q : (Point d × Point d) × (secantSpace d N → Ω) =>
      betaReplyS (M := M) (n := n k) (N := N) (hnN k) g h (query θ q.1) q.2)
      = (fun p : Point d × (secantSpace d N → Ω) =>
          betaReplyS (M := M) (n := n k) (N := N) (hnN k) g h p.1 p.2) ∘
        (fun q : (Point d × Point d) × (secantSpace d N → Ω) => (query θ q.1, q.2)) := by
    funext q
    rfl
  rw [hh]
  refine (measurable_betaReplyS_joint (hnN k) hg h).comp ?_
  refine Measurable.prodMk ?_ ?_
  · exact hq
  · exact measurable_snd

/-- The `M`-band reply of a round is integrable. -/
lemma betaReplyS_integrable {M n N : ℕ} (hnN : M * n ≤ N) {g : Point d → Ω → ℝ}
    {f : Point d → ℝ} (hgi : ∀ x, Integrable (g x) p)
    (hmean : ∀ x, (∫ ω, g x ω ∂p) = f x) (hn : 0 < n) (x : Point d) :
    Integrable (betaReplyS hnN g h x) (slotLaw d N p) := by
  classical
  refine (measurePreserving_cellInj (d := d) (hM := hnN)).integrable_comp_of_integrable
    (ε := Point d) ?_
  exact betaReply_integrable hgi hmean hn x

/-- The mean of the `M`-band reply of a round is the `M`-band secant. -/
lemma betaReplyS_mean {M n N : ℕ} (hnN : M * n ≤ N) {g : Point d → Ω → ℝ} {f : Point d → ℝ}
    {h : ℝ} (hgi : ∀ x, Integrable (g x) p) (hmean : ∀ x, (∫ ω, g x ω ∂p) = f x)
    (hn : 0 < n) (x : Point d) :
    (∫ ω : secantSpace d N → Ω, betaReplyS hnN g h x ω ∂(slotLaw d N p)) = betaDiff M h f x := by
  classical
  refine (integral_comp_preserving_point (measurePreserving_cellInj (d := d) (hM := hnN))
    (betaReply_integrable hgi hmean hn x)).trans ?_
  exact betaReply_mean hgi hmean hn x

/-- Mean-square noise of the `M`-band reply of one scheduled round. -/
lemma betaReplyS_deviation {M n N : ℕ} (hnN : M * n ≤ N) {g : Point d → Ω → ℝ}
    {f : Point d → ℝ} {σ h : ℝ} (hg : Measurable (Function.uncurry g))
    (hgi : ∀ x, Integrable (g x) p)
    (hmean : ∀ x, (∫ ω, g x ω ∂p) = f x)
    (hvi : ∀ x, Integrable (fun ω => (g x ω - f x) ^ 2) p)
    (hv : ∀ x, (∫ ω, (g x ω - f x) ^ 2 ∂p) ≤ σ ^ 2)
    (hn : 0 < n) (x : Point d) :
    Integrable (fun ω : secantSpace d N → Ω =>
        ‖betaReplyS hnN g h x ω - betaDiff M h f x‖ ^ 2) (slotLaw d N p) ∧
      (∫ ω : secantSpace d N → Ω, ‖betaReplyS hnN g h x ω - betaDiff M h f x‖ ^ 2
          ∂(slotLaw d N p))
        ≤ betaAbs M ^ 2 * ((d : ℝ) * σ ^ 2 / (h ^ 2 * n)) := by
  classical
  obtain hdev := betaReply_deviation hg hgi hmean hvi hv hn x
  set Φ : (secantSpace d N → Ω) → (secantSpace d (M * n) → Ω) :=
    fun ω t => ω (cellInj hnN t) with hΦdef
  have hpΦ : MeasurePreserving Φ (slotLaw d N p) (slotLaw d (M * n) p) :=
    measurePreserving_cellInj (d := d) (hM := hnN)
  have hfun : (fun ω : secantSpace d N → Ω => ‖betaReplyS hnN g h x ω - betaDiff M h f x‖ ^ 2) =
      (fun ξ : secantSpace d (M * n) → Ω => ‖betaReply M g h x ξ - betaDiff M h f x‖ ^ 2) ∘ Φ := by
    funext ω
    show ‖betaReply M g h x (Φ ω) - betaDiff M h f x‖ ^ 2 =
        ‖betaReply M g h x (Φ ω) - betaDiff M h f x‖ ^ 2
    rfl
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact hpΦ.integrable_comp_of_integrable (ε := ℝ) hdev.1
  · rw [hfun]
    exact (integral_comp_preserving hpΦ hdev.1).trans_le hdev.2

/-- The scheduled `M`-band step is jointly measurable. -/
lemma measurable_betaStepSched_joint {M d N : ℕ} (n : ℕ → ℕ) (hnN : ∀ k, M * n k ≤ N)
    {g : Point d → Ω → ℝ} (hg : Measurable (Function.uncurry g)) (L μ θ h : ℝ) (k : ℕ) :
    Measurable (fun q : (Point d × Point d) × (secantSpace d N → Ω) =>
      betaStepSched n hnN L μ θ g h k q.1 q.2) := by
  classical
  have h1 : Measurable (fun q : (Point d × Point d) × (secantSpace d N → Ω) =>
      betaReplyS (M := M) (n := n k) (N := N) (hnN k) g h (query θ q.1) q.2) :=
    measurable_betaReplyRound n hnN hg θ h k
  have hstepc : Continuous (fun p : (Point d × Point d) × Point d => step L μ θ p.1 p.2) := by
    show Continuous (fun p : (Point d × Point d) × Point d =>
      ((1 / (1 + θ)) • (p.1.1 + θ • p.1.2) - (1 / L) • p.2,
        (1 - θ) • p.1.2 + θ • ((1 / (1 + θ)) • (p.1.1 + θ • p.1.2)) - (2 * θ / μ) • p.2))
    fun_prop
  have heq : (fun q : (Point d × Point d) × (secantSpace d N → Ω) =>
      betaStepSched n hnN L μ θ g h k q.1 q.2) =
      (fun p : (Point d × Point d) × Point d => step L μ θ p.1 p.2) ∘
        (fun q : (Point d × Point d) × (secantSpace d N → Ω) =>
          (q.1, betaReplyS (M := M) (n := n k) (N := N) (hnN k) g h (query θ q.1) q.2)) := by
    funext q
    rfl
  rw [heq]
  refine hstepc.measurable.comp ?_
  refine Measurable.prodMk ?_ ?_
  · exact measurable_fst
  · exact h1

/-- One `M`-band accelerated round: with a stencil whose squared bias is at most `B`, the Lyapunov
decrease holds with the bias factor `2 * (3 / (4 * L) + 2 * θ / μ) * B` and the centered variance
coefficient `1 / (2 * L) + θ ^ 2 / μ` times `betaAbs M ^ 2 * d * σ ^ 2 / (h ^ 2 * n k)`. -/
lemma beta_one_step {M d N : ℕ} (n : ℕ → ℕ) (hnN : ∀ k, M * n k ≤ N) (hn : ∀ k, 0 < n k)
    {B : ℝ} {g : Point d → Ω → ℝ} {f : Point d → ℝ} {σ L μ θ h : ℝ} {xstar : Point d}
    (_hh : 0 < h) (hL : 0 < L) (hμ : 0 < μ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hθL : 16 * L * θ ^ 2 ≤ μ)
    (hbias : ∀ y, ‖betaDiff M h f y - gradient f y‖ ^ 2 ≤ B)
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
    Integrable (fun ω => potential f μ xstar (betaStepSched n hnN L μ θ g h k s ω))
        (slotLaw d N p) ∧
      (∫ ω, potential f μ xstar (betaStepSched n hnN L μ θ g h k s ω) ∂(slotLaw d N p)) ≤
        (1 - θ / 2) * potential f μ xstar s
          + 2 * (3 / (4 * L) + 2 * θ / μ) * B
          + (1 / (2 * L) + θ ^ 2 / μ) * (betaAbs M ^ 2 * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (n k)))) := by
  classical
  have hminf : ∀ x, f xstar ≤ f x := fun x => hmin (Set.mem_univ x)
  have hf : Measurable f :=
    (continuous_iff_continuousAt.mpr fun x => (hgr x).continuousAt).measurable
  set y : Point d := query θ s with hydef
  set v₀ : Point d := betaDiff M h f y with hv0def
  set V : (secantSpace d N → Ω) → Point d := fun ω => betaReplyS (M := M) (n := n k) (N := N) (hnN k) g h y ω with hVdef
  set xi : (secantSpace d N → Ω) → Point d := fun ω => V ω - v₀ with hxidef
  set c : Point d := -(1 / L) • gradient f (y - (1 / L) • v₀)
      - θ • ((1 - θ) • s.2 + θ • y - (2 * θ / μ) • v₀ - xstar) with hcdef
  set cv : ℝ := 1 / (2 * L) + θ ^ 2 / μ with hcvdef
  set cb : ℝ := 2 * (3 / (4 * L) + 2 * θ / μ) with hcbdef
  set S1 : (secantSpace d N → Ω) → Point d × Point d :=
    (fun r : (Point d × Point d) × (secantSpace d N → Ω) =>
        betaStepSched n hnN L μ θ g h k r.1 r.2) ∘ (fun ω : secantSpace d N → Ω => (s, ω))
    with hS1def
  set F : (secantSpace d N → Ω) → ℝ := potential f μ xstar ∘ S1 with hfdef
  set Lc : Point d →L[ℝ] ℝ := InnerProductSpace.toDual ℝ (Point d) c with hLcdef
  set E : (secantSpace d N → Ω) → ℝ := fun ω => Lc (xi ω) + cv * ‖xi ω‖ ^ 2 with hEdef
  set a : ℝ := (1 - θ / 2) * potential f μ xstar s + cb * B with hadef
  set G : (secantSpace d N → Ω) → ℝ := fun ω => a + E ω with hGdef
  have hreplyi : Integrable V (slotLaw d N p) :=
    betaReplyS_integrable (M := M) (n := n k) (N := N) (hnN k) hgi hmean (hn k) y
  have hVnonneg : ∀ t : Point d × Point d, 0 ≤ potential f μ xstar t := by
    intro t
    show 0 ≤ f t.1 - f xstar + μ / 4 * ‖t.2 - xstar‖ ^ 2
    exact add_nonneg (sub_nonneg.mpr (hminf t.1)) (mul_nonneg (by positivity) (sq_nonneg _))
  have hcb0 : 0 ≤ cb := by positivity
  have hcv0 : 0 ≤ cv := by positivity
  have hVm : Measurable V := measurable_betaReplyS_at (M := M) (n := n k) (N := N) (hnN k) hg h y
  have hxim : Measurable xi := hVm.sub measurable_const
  have hxii : Integrable xi (slotLaw d N p) := hreplyi.sub (integrable_const _)
  have hVmean : (∫ ω, V ω ∂(slotLaw d N p)) = v₀ := by
    show (∫ ω, betaReplyS (M := M) (n := n k) (N := N) (hnN k) g h y ω ∂(slotLaw d N p)) = v₀
    rw [hv0def, hydef]
    exact betaReplyS_mean (M := M) (n := n k) (N := N) (hnN k) hgi hmean (hn k) y
  have hxi0 : (∫ ω, xi ω ∂(slotLaw d N p)) = 0 := by
    show (∫ ω, V ω - v₀ ∂(slotLaw d N p)) = 0
    rw [integral_sub hreplyi (integrable_const _), hVmean, integral_const, probReal_univ,
      one_smul, sub_self]
  have hlin0 : (∫ ω, Lc (xi ω) ∂(slotLaw d N p)) = 0 := by
    rw [Lc.integral_comp_comm hxii, hxi0, map_zero]
  have hFm : Measurable F := by
    rw [hfdef, hS1def]
    exact (measurable_potentialZO hf).comp
      ((measurable_betaStepSched_joint n hnN hg L μ θ h k).comp
        (measurable_const.prodMk measurable_id))
  have hdeV : ∀ ω, betaStepSched n hnN L μ θ g h k s ω = step L μ θ s (V ω) := fun _ => rfl
  have hVadd : ∀ ω, V ω = v₀ + xi ω := fun ω => by
    show V ω = v₀ + (V ω - v₀)
    rw [add_comm, sub_add_cancel]
  have hde : ∀ ω, betaStepSched n hnN L μ θ g h k s ω = step L μ θ s (v₀ + xi ω) := fun ω =>
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
    have hw : F ω = potential f μ xstar (betaStepSched n hnN L μ θ g h k s ω) := rfl
    rw [hw, hde ω]
    show potential f μ xstar (step L μ θ s (v₀ + xi ω)) ≤ a + (Lc (xi ω) + cv * ‖xi ω‖ ^ 2)
    linarith
  obtain hdev := betaReplyS_deviation (M := M) (n := n k) (N := N) (hnN k) hg hgi hmean hvi hv (hn k) y
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
  have hbnd : (∫ ω, ‖xi ω‖ ^ 2 ∂(slotLaw d N p))
      ≤ betaAbs M ^ 2 * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (n k))) := by
    refine hdev.2.trans_eq ?_
    rfl
  have hmul : cv * ∫ ω, ‖xi ω‖ ^ 2 ∂(slotLaw d N p)
      ≤ cv * (betaAbs M ^ 2 * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (n k)))) :=
    mul_le_mul_of_nonneg_left hbnd hcv0
  have hlin : (∫ ω, G ω ∂(slotLaw d N p)) = a + ∫ ω, E ω ∂(slotLaw d N p) := by
    show (∫ ω, a + E ω ∂(slotLaw d N p)) = a + ∫ ω, E ω ∂(slotLaw d N p)
    rw [integral_add (f := fun _ => a) (g := E) (integrable_const a) hEi, integral_const,
      probReal_univ, one_smul]
  refine ⟨hFi, ?_⟩
  calc (∫ ω, potential f μ xstar (betaStepSched n hnN L μ θ g h k s ω) ∂(slotLaw d N p))
      = ∫ ω, F ω ∂(slotLaw d N p) := rfl
    _ ≤ ∫ ω, G ω ∂(slotLaw d N p) := integral_mono hFi hGi hpath
    _ = a + ∫ ω, E ω ∂(slotLaw d N p) := hlin
    _ = a + cv * ∫ ω, ‖xi ω‖ ^ 2 ∂(slotLaw d N p) := by rw [hEint]
    _ ≤ a + cv * (betaAbs M ^ 2 * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (n k)))) := by linarith
    _ = (1 - θ / 2) * potential f μ xstar s
          + 2 * (3 / (4 * L) + 2 * θ / μ) * B
          + (1 / (2 * L) + θ ^ 2 / μ)
              * (betaAbs M ^ 2 * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (n k)))) := by
          show (1 - θ / 2) * potential f μ xstar s + cb * B
              + cv * (betaAbs M ^ 2 * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (n k)))) = _
          rw [hcvdef, hcbdef]

/-- `K` `M`-band rounds contract the momentum potential geometrically and pay the centered error
sum: the noise enters with `1 / (2 * L) + θ ^ 2 / μ`, the bias with the Young factor. -/
lemma beta_sched_potential {M d N : ℕ} {n : ℕ → ℕ} (hnN : ∀ k, M * n k ≤ N) (hn : ∀ k, 0 < n k)
    {B : ℝ} {g : Point d → Ω → ℝ} {f : Point d → ℝ} {σ L μ h θ : ℝ} {xstar : Point d}
    (hh : 0 < h) (hL : 0 < L) (hμ : 0 < μ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hθL : 16 * L * θ ^ 2 ≤ μ)
    (hbias : ∀ y, ‖betaDiff M h f y - gradient f y‖ ^ 2 ≤ B)
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
        (runSched (fun k s' ω => betaStepSched n hnN L μ θ g h k s' ω) i K s Ξ))
        (Measure.pi (fun _ : Fin K => slotLaw d N p)) ∧
      (∫ Ξ, potential f μ xstar
        (runSched (fun k s' ω => betaStepSched n hnN L μ θ g h k s' ω) i K s Ξ)
        ∂Measure.pi (fun _ : Fin K => slotLaw d N p)) ≤
      (1 - θ / 2) ^ K * potential f μ xstar s
        + ∑ k ∈ Finset.range K, (1 - θ / 2) ^ (K - 1 - k)
            * (2 * (3 / (4 * L) + 2 * θ / μ) * B
              + (1 / (2 * L) + θ ^ 2 / μ)
                  * (betaAbs M ^ 2 * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (n (i + k)))))) := by
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
    have h2 : (0 : ℝ) ≤ ‖betaDiff M h f xstar - gradient f xstar‖ ^ 2 := by positivity
    linarith
  refine sched_iterate_accuracy (d := d) (M := N)
    (step := fun k s' ω => betaStepSched n hnN L μ θ g h k s' ω) (ρ := (1 : ℝ) - θ / 2)
    (c := fun k => 2 * (3 / (4 * L) + 2 * θ / μ) * B
      + (1 / (2 * L) + θ ^ 2 / μ) * (betaAbs M ^ 2 * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (n k)))))
    (fun k => measurable_betaStepSched_joint n hnN hg L μ θ h k)
    ⟨slotLaw d N p, inferInstance⟩ (potential f μ xstar) (measurable_potentialZO hf) hVnonneg hrho
    (fun k => by positivity)
    (fun k s' =>
      have h1 := beta_one_step (M := M) (n := n) hnN hn hh hL hμ hθ0 hθ1 hθL hbias hg hgi hmean hvi
        hv hc hgr hlip hsc hmin k s'
      ⟨h1.1, h1.2.trans (le_of_eq (add_assoc _ _ _))⟩) i K s

/-- `K` `M`-band rounds bound the expected suboptimality of the momentum output. -/
lemma beta_sched_gap {M d N : ℕ} {n : ℕ → ℕ} (hnN : ∀ k, M * n k ≤ N) (hn : ∀ k, 0 < n k)
    {B : ℝ} {g : Point d → Ω → ℝ} {f : Point d → ℝ} {σ L μ h θ : ℝ} {xstar : Point d}
    (hh : 0 < h) (hL : 0 < L) (hμ : 0 < μ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hθL : 16 * L * θ ^ 2 ≤ μ)
    (hbias : ∀ y, ‖betaDiff M h f y - gradient f y‖ ^ 2 ≤ B)
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
        f (runSched (fun k s' ω => betaStepSched n hnN L μ θ g h k s' ω) 0 K (x0, x0) Ξ).1
          - f xstar) (Measure.pi (fun _ : Fin K => slotLaw d N p)) ∧
      (∫ Ξ, f (runSched (fun k s' ω => betaStepSched n hnN L μ θ g h k s' ω) 0 K (x0, x0) Ξ).1
        - f xstar ∂Measure.pi (fun _ : Fin K => slotLaw d N p)) ≤
      (1 - θ / 2) ^ K * (f x0 - f xstar + μ / 4 * ‖x0 - xstar‖ ^ 2)
        + ∑ k ∈ Finset.range K, (1 - θ / 2) ^ (K - 1 - k)
            * (2 * (3 / (4 * L) + 2 * θ / μ) * B
              + (1 / (2 * L) + θ ^ 2 / μ)
                  * (betaAbs M ^ 2 * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (n k))))) := by
  classical
  have hminf : ∀ x, f xstar ≤ f x := fun x => hmin (Set.mem_univ x)
  have hf : Measurable f :=
    (continuous_iff_continuousAt.mpr fun x => (hgr x).continuousAt).measurable
  obtain ⟨hIf, hb⟩ := beta_sched_potential (M := M) (d := d) (n := n) hnN hn (B := B) (g := g)
    (f := f) (σ := σ) (L := L) (μ := μ) (h := h) (θ := θ) (xstar := xstar) hh hL hμ hθ0 hθ1 hθL
    hbias hg hgi hmean hvi hv hc hgr hlip hsc hmin (i := 0) (K := K) (s := (x0, x0))
  simp only [Nat.zero_add] at hb
  have hrun2 : Measurable ((fun q : (Point d × Point d) × (Fin K → secantSpace d N → Ω) =>
      runSched (fun k s' ω => betaStepSched n hnN L μ θ g h k s' ω) 0 K q.1 q.2) ∘
      (fun Ξ : Fin K → secantSpace d N → Ω => ((x0, x0), Ξ))) :=
    (measurable_runSched (fun k => measurable_betaStepSched_joint n hnN hg L μ θ h k) K 0).comp
      (measurable_const.prodMk measurable_id)
  have hf1 : Measurable (fun p : Point d × Point d => p.1) := continuous_fst.measurable
  have hgapMeas : Measurable ((fun v : Point d => f v - f xstar) ∘
      (fun p : Point d × Point d => p.1) ∘
      (fun Ξ : Fin K → secantSpace d N → Ω =>
        runSched (fun k s' ω => betaStepSched n hnN L μ θ g h k s' ω) 0 K (x0, x0) Ξ)) :=
    (hf.sub measurable_const).comp (hf1.comp hrun2)
  have hpoint : ∀ Ξ : Fin K → secantSpace d N → Ω,
      f (runSched (fun k s' ω => betaStepSched n hnN L μ θ g h k s' ω) 0 K (x0, x0) Ξ).1
          - f xstar
        ≤ potential f μ xstar
          (runSched (fun k s' ω => betaStepSched n hnN L μ θ g h k s' ω) 0 K (x0, x0) Ξ) :=
    fun Ξ => le_add_of_nonneg_right (mul_nonneg (by positivity) (sq_nonneg _))
  have hgapInt : Integrable (fun Ξ : Fin K → secantSpace d N → Ω =>
      f (runSched (fun k s' ω => betaStepSched n hnN L μ θ g h k s' ω) 0 K (x0, x0) Ξ).1
        - f xstar) (Measure.pi (fun _ : Fin K => slotLaw d N p)) :=
    hIf.mono' hgapMeas.aestronglyMeasurable (ae_of_all _ fun Ξ => by
      have h0 : 0 ≤
          f (runSched (fun k s' ω => betaStepSched n hnN L μ θ g h k s' ω) 0 K (x0, x0) Ξ).1
            - f xstar := sub_nonneg.mpr (hminf _)
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact hpoint Ξ)
  exact ⟨hgapInt, (integral_mono hgapInt hIf hpoint).trans hb⟩

end OracleTemplate.SecantPolyak.BetaStencil

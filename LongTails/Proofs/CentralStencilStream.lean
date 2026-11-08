import LongTails.Proofs.AcceleratedSecantStream
import LongTails.Proofs.CenteredMomentumStream
import LongTails.Proofs.CentralStencilEstimator

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

/-!
Analysis of the symmetric (central) value stencil inside the damped anchored momentum round.
The reply splits into its conditional mean, the central secant `cDiff h f y`, and a mean-zero
deviation, so the linear term of the potential averages out and the noise pays the sharp
coefficient `1 / (2 * L) + θ ^ 2 / μ`. Unlike the one-sided secant, the symmetric stencil has
`O (h ^ 2)` bias, which is supplied here as an abstract bound `B` on `‖cDiff h f y - gradient f y‖²`.
-/

namespace OracleTemplate.SecantPolyak.CentralStencil

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
open OracleTemplate
open OracleTemplate.SecantPolyak.Centered
open SecantDescent SecantPolyak SecantPolyak.Accelerated ZerothOrder InexactGradient Scheduled
open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {Ω : Type} [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]

/-- One scheduled central round: momentum extrapolation, then a batch of `m k` symmetric
stencils at the momentum probe point. -/
noncomputable def cStepSched {d M : ℕ} (m : ℕ → ℕ) (hmM : ∀ k, m k ≤ M)
    (L μ θ : ℝ) (g : Point d → Ω → ℝ) (h : ℝ) (k : ℕ) (s : Point d × Point d)
    (ω : secantSpace d M → Ω) : Point d × Point d :=
  step L μ θ s (cReply g h (query θ s) (toCells fun t => ω (cellInj (hmM k) t)))

/-- A batch of centered replicas is integrable. -/
lemma cReply_integrable {d m : ℕ} {g : Point d → Ω → ℝ} {f : Point d → ℝ} {h : ℝ}
    (hgi : ∀ x, Integrable (g x) p) (hmean : ∀ x, (∫ ω, g x ω ∂p) = f x)
    (_hm : 0 < m) (x : Point d) :
    Integrable (cReply g h x) (batchLaw d m p) := by
  classical
  obtain ⟨hEi, _⟩ := cEstimate_integral (fun j => cell_preserving j) hgi hmean h x
  have hri (r : Fin m) : Integrable (fun ξ : Fin m → Fin d × Bool → Ω =>
      cEstimate g h x (ξ r)) (batchLaw d m p) :=
    (batch_preserving_cells r).integrable_comp_of_integrable (ε := Point d) hEi
  have hsum : Integrable (fun ξ : Fin m → Fin d × Bool → Ω =>
      ∑ r : Fin m, cEstimate g h x (ξ r)) (batchLaw d m p) :=
    integrable_finsetSum Finset.univ fun r _ => hri r
  have hEq : cReply g h x = fun ξ => (1 / (m : ℝ)) • ∑ r : Fin m, cEstimate g h x (ξ r) := rfl
  have hsmul : Integrable (fun ξ : Fin m → Fin d × Bool → Ω =>
      (1 / (m : ℝ)) • ∑ r : Fin m, cEstimate g h x (ξ r)) (batchLaw d m p) :=
    Integrable.smul (1 / (m : ℝ)) hsum
  rw [hEq]
  exact hsmul

/-- The mean of the replicated centered reply is the symmetric secant. -/
lemma cReply_mean {d m : ℕ} {g : Point d → Ω → ℝ} {f : Point d → ℝ} {h : ℝ}
    (hgi : ∀ x, Integrable (g x) p) (hmean : ∀ x, (∫ ω, g x ω ∂p) = f x)
    (hm : 0 < m) (x : Point d) :
    (∫ ξ : Fin m → Fin d × Bool → Ω, cReply g h x ξ ∂(batchLaw d m p)) = cDiff h f x := by
  classical
  obtain ⟨hEi, hE⟩ := cEstimate_integral (fun j => cell_preserving j) hgi hmean h x
  have hrE (r : Fin m) : (∫ ξ : Fin m → Fin d × Bool → Ω, cEstimate g h x (ξ r)
      ∂(batchLaw d m p)) = cDiff h f x :=
    (integral_comp_preserving_point (batch_preserving_cells r) hEi).trans hE
  have hri (r : Fin m) : Integrable (fun ξ : Fin m → Fin d × Bool → Ω =>
      cEstimate g h x (ξ r)) (batchLaw d m p) :=
    (batch_preserving_cells r).integrable_comp_of_integrable (ε := Point d) hEi
  have h1 : (∫ ξ : Fin m → Fin d × Bool → Ω, cReply g h x ξ ∂(batchLaw d m p))
      = (1 / (m : ℝ)) • ∫ ξ : Fin m → Fin d × Bool → Ω,
        ∑ r : Fin m, cEstimate g h x (ξ r) ∂(batchLaw d m p) := by
    show (∫ ξ : Fin m → Fin d × Bool → Ω,
        (1 / (m : ℝ)) • ∑ r : Fin m, cEstimate g h x (ξ r) ∂(batchLaw d m p)) = _
    exact integral_smul (c := (1 / (m : ℝ))) _
  rw [h1]
  have h3 : (∫ ξ : Fin m → Fin d × Bool → Ω, ∑ r : Fin m, cEstimate g h x (ξ r)
      ∂(batchLaw d m p)) = ∑ r : Fin m, cDiff h f x :=
    ((integral_finsetSum Finset.univ fun r _ => hri r) : _ =
        ∑ r : Fin m, ∫ ξ : Fin m → Fin d × Bool → Ω, cEstimate g h x (ξ r)
          ∂(batchLaw d m p))
      |>.trans (Finset.sum_congr rfl fun r _ => hrE r)
  rw [h3]
  have h2 : (1 / (m : ℝ)) • ∑ r : Fin m, (cDiff h f x : Point d) = cDiff h f x := by
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ,
      smul_smul]
    rw [show ((1 / (m : ℝ)) * (m : ℝ)) = (1 : ℝ) by rw [div_mul_cancel₀ 1 hm'], one_smul]
  exact h2

/-- The centered reply of one scheduled round is jointly measurable. -/
lemma measurable_cReplyRound {d M : ℕ} (m : ℕ → ℕ) (hmM : ∀ k, m k ≤ M)
    {g : Point d → Ω → ℝ} (hg : Measurable (Function.uncurry g)) (θ h : ℝ) (k : ℕ) :
    Measurable (fun q : (Point d × Point d) × (secantSpace d M → Ω) =>
      cReply g h (query θ q.1)
        (toCells fun t : secantSpace d (m k) => q.2 (cellInj (hmM k) t))) := by
  classical
  have hjoint : Measurable (fun p : Point d × (Fin (m k) → Fin d × Bool → Ω) =>
      cReply g h p.1 p.2) := measurable_cReply_joint hg h
  have hq : Measurable (fun q : (Point d × Point d) × (secantSpace d M → Ω) => query θ q.1) := by
    have hc : Continuous (fun p : Point d × Point d => (1 / (1 + θ)) • (p.1 + θ • p.2)) := by
      fun_prop
    show Measurable ((fun p : Point d × Point d => (1 / (1 + θ)) • (p.1 + θ • p.2)) ∘
      (fun q : (Point d × Point d) × (secantSpace d M → Ω) => q.1))
    exact hc.measurable.comp measurable_fst
  have hcells : Measurable (fun q : (Point d × Point d) × (secantSpace d M → Ω) =>
      toCells fun t : secantSpace d (m k) => q.2 (cellInj (hmM k) t)) := by
    have hc : Measurable (fun ω : secantSpace d (m k) → Ω =>
        toCells (ω : secantSpace d (m k) → Ω)) :=
      (MeasurableEquiv.curry (Fin (m k)) (Fin d × Bool) Ω).measurable
    have hr : Measurable (fun ω : secantSpace d M → Ω =>
        fun t : secantSpace d (m k) => ω (cellInj (hmM k) t)) :=
      measurable_pi_iff.mpr fun t => measurable_pi_apply (cellInj (hmM k) t)
    show Measurable ((fun ω : secantSpace d (m k) → Ω => toCells ω) ∘
      (fun ω : secantSpace d M → Ω => fun t : secantSpace d (m k) => ω (cellInj (hmM k) t)) ∘
      (fun q : (Point d × Point d) × (secantSpace d M → Ω) => q.2))
    exact hc.comp (hr.comp measurable_snd)
  have heq : (fun q : (Point d × Point d) × (secantSpace d M → Ω) =>
      cReply g h (query θ q.1) (toCells fun t : secantSpace d (m k) => q.2 (cellInj (hmM k) t))) =
      (fun p : Point d × (Fin (m k) → Fin d × Bool → Ω) => cReply g h p.1 p.2) ∘
        (fun q => (query θ q.1, toCells fun t : secantSpace d (m k) =>
          q.2 (cellInj (hmM k) t))) := by
    funext q
    rfl
  rw [heq]
  exact hjoint.comp (hq.prodMk hcells)

/-- The scheduled central step is jointly measurable. -/
lemma measurable_cStepSched_joint {d M : ℕ} (m : ℕ → ℕ) (hmM : ∀ k, m k ≤ M)
    {g : Point d → Ω → ℝ} (hg : Measurable (Function.uncurry g)) (L μ θ h : ℝ) (k : ℕ) :
    Measurable (fun q : (Point d × Point d) × (secantSpace d M → Ω) =>
      cStepSched m hmM L μ θ g h k q.1 q.2) := by
  classical
  have h1 : Measurable (fun q : (Point d × Point d) × (secantSpace d M → Ω) =>
      cReply g h (query θ q.1)
        (toCells fun t : secantSpace d (m k) => q.2 (cellInj (hmM k) t))) :=
    measurable_cReplyRound m hmM hg θ h k
  have hstepc : Continuous (fun p : (Point d × Point d) × Point d => step L μ θ p.1 p.2) := by
    show Continuous (fun p : (Point d × Point d) × Point d =>
      ((1 / (1 + θ)) • (p.1.1 + θ • p.1.2) - (1 / L) • p.2,
        (1 - θ) • p.1.2 + θ • ((1 / (1 + θ)) • (p.1.1 + θ • p.1.2)) - (2 * θ / μ) • p.2))
    fun_prop
  have heq : (fun q : (Point d × Point d) × (secantSpace d M → Ω) =>
      cStepSched m hmM L μ θ g h k q.1 q.2) =
      (fun p : (Point d × Point d) × Point d => step L μ θ p.1 p.2) ∘
        (fun q : (Point d × Point d) × (secantSpace d M → Ω) =>
          (q.1, cReply g h (query θ q.1)
            (toCells fun t : secantSpace d (m k) => q.2 (cellInj (hmM k) t)))) := by
    funext q
    rfl
  rw [heq]
  exact hstepc.measurable.comp (measurable_fst.prodMk h1)

/-- One central accelerated round: with a symmetric stencil whose squared bias is at most `B`,
the Lyapunov decrease holds with the bias factor `2 * (3 / (4 * L) + 2 * θ / μ) * B` and the
centered variance coefficient `1 / (2 * L) + θ ^ 2 / μ`. -/
lemma c_one_step {d M : ℕ} (m : ℕ → ℕ) (hmM : ∀ k, m k ≤ M) (hm : ∀ k, 0 < m k) {B : ℝ}
    {g : Point d → Ω → ℝ} {f : Point d → ℝ} {σ L μ θ h : ℝ} {xstar : Point d}
    (_hh : 0 < h) (hL : 0 < L) (hμ : 0 < μ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hθL : 16 * L * θ ^ 2 ≤ μ)
    (hbias : ∀ y, ‖cDiff h f y - gradient f y‖ ^ 2 ≤ B)
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
    Integrable (fun ω => potential f μ xstar (cStepSched m hmM L μ θ g h k s ω))
        (slotLaw d M p) ∧
      (∫ ω, potential f μ xstar (cStepSched m hmM L μ θ g h k s ω) ∂(slotLaw d M p)) ≤
        (1 - θ / 2) * potential f μ xstar s
          + 2 * (3 / (4 * L) + 2 * θ / μ) * B
          + (1 / (2 * L) + θ ^ 2 / μ) * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (m k))) := by
  classical
  have hminf : ∀ x, f xstar ≤ f x := fun x => hmin (Set.mem_univ x)
  have hf : Measurable f :=
    (continuous_iff_continuousAt.mpr fun x => (hgr x).continuousAt).measurable
  set y : Point d := query θ s with hydef
  set v₀ : Point d := cDiff h f y with hv0def
  set q : (secantSpace d M → Ω) → (Fin (m k) → Fin d × Bool → Ω) :=
    fun ω => toCells (fun t : secantSpace d (m k) => ω (cellInj (hmM k) t)) with hqdef
  have hp : MeasurePreserving q (slotLaw d M p) (batchLaw d (m k) p) :=
    (measurePreserving_toCells d (m k)).comp (measurePreserving_cellInj (hmM k))
  set V : (secantSpace d M → Ω) → Point d := fun ω => cReply g h y (q ω) with hVdef
  set xi : (secantSpace d M → Ω) → Point d := fun ω => V ω - v₀ with hxidef
  set c : Point d := -(1 / L) • gradient f (y - (1 / L) • v₀)
      - θ • ((1 - θ) • s.2 + θ • y - (2 * θ / μ) • v₀ - xstar) with hcdef
  set cv : ℝ := 1 / (2 * L) + θ ^ 2 / μ with hcvdef
  set cb : ℝ := 2 * (3 / (4 * L) + 2 * θ / μ) with hcbdef
  set S1 : (secantSpace d M → Ω) → Point d × Point d :=
    (fun r : (Point d × Point d) × (secantSpace d M → Ω) =>
        cStepSched m hmM L μ θ g h k r.1 r.2) ∘ (fun ω : secantSpace d M → Ω => (s, ω))
    with hS1def
  set F : (secantSpace d M → Ω) → ℝ := potential f μ xstar ∘ S1 with hfdef
  set Lc : Point d →L[ℝ] ℝ := InnerProductSpace.toDual ℝ (Point d) c with hLcdef
  set E : (secantSpace d M → Ω) → ℝ := fun ω => Lc (xi ω) + cv * ‖xi ω‖ ^ 2 with hEdef
  set a : ℝ := (1 - θ / 2) * potential f μ xstar s + cb * B with hadef
  set G : (secantSpace d M → Ω) → ℝ := fun ω => a + E ω with hGdef
  have hreplyi : Integrable (cReply g h y) (batchLaw d (m k) p) :=
    cReply_integrable hgi hmean (hm k) y
  have hVnonneg : ∀ t : Point d × Point d, 0 ≤ potential f μ xstar t := by
    intro t
    show 0 ≤ f t.1 - f xstar + μ / 4 * ‖t.2 - xstar‖ ^ 2
    exact add_nonneg (sub_nonneg.mpr (hminf t.1)) (mul_nonneg (by positivity) (sq_nonneg _))
  have hcb0 : 0 ≤ cb := by positivity
  have hcv0 : 0 ≤ cv := by positivity
  have hVm : Measurable V := (measurable_cReply_at hg h y).comp hp.measurable
  have hxim : Measurable xi := hVm.sub measurable_const
  have hVi : Integrable V (slotLaw d M p) :=
    hp.integrable_comp_of_integrable (ε := Point d) hreplyi
  have hxii : Integrable xi (slotLaw d M p) := hVi.sub (integrable_const _)
  have hVmean : (∫ ω, V ω ∂(slotLaw d M p)) = v₀ := by
    show (∫ ω, cReply g h y (q ω) ∂(slotLaw d M p)) = v₀
    rw [integral_comp_preserving_point hp hreplyi]
    exact cReply_mean hgi hmean (hm k) y
  have hxi0 : (∫ ω, xi ω ∂(slotLaw d M p)) = 0 := by
    show (∫ ω, V ω - v₀ ∂(slotLaw d M p)) = 0
    rw [integral_sub hVi (integrable_const _), hVmean, integral_const, probReal_univ, one_smul,
      sub_self]
  have hlin0 : (∫ ω, Lc (xi ω) ∂(slotLaw d M p)) = 0 := by
    rw [Lc.integral_comp_comm hxii, hxi0, map_zero]
  have hFm : Measurable F := by
    rw [hfdef, hS1def]
    exact (measurable_potentialZO hf).comp
      ((measurable_cStepSched_joint m hmM hg L μ θ h k).comp
        (measurable_const.prodMk measurable_id))
  have hde : ∀ ω, cStepSched m hmM L μ θ g h k s ω = step L μ θ s (v₀ + xi ω) := by
    intro ω
    have h1 : v₀ + xi ω = V ω := by
      show v₀ + (V ω - v₀) = V ω
      rw [add_comm, sub_add_cancel]
    show step L μ θ s (cReply g h (query θ s) (q ω)) = step L μ θ s (v₀ + xi ω)
    rw [h1]
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
    have hw : F ω = potential f μ xstar (cStepSched m hmM L μ θ g h k s ω) := rfl
    rw [hw, hde ω]
    show potential f μ xstar (step L μ θ s (v₀ + xi ω)) ≤ a + (Lc (xi ω) + cv * ‖xi ω‖ ^ 2)
    linarith
  have hxi2 : Integrable (fun ω => ‖xi ω‖ ^ 2) (slotLaw d M p) := by
    have hdev := cReply_deviation (d := d) (m := m k) (g := g) (f := f) (σ := σ) (h := h)
      hg hgi hmean hvi hv (hm k) y
    have h1 : (fun ω : secantSpace d M → Ω => ‖xi ω‖ ^ 2)
        = (fun b : Fin (m k) → Fin d × Bool → Ω => ‖cReply g h y b - v₀‖ ^ 2) ∘ q := by
      funext ω
      rfl
    rw [h1]
    exact hp.integrable_comp_of_integrable (ε := ℝ) hdev.1
  have hEm : Measurable E := by
    show Measurable (fun ω => Lc (xi ω) + cv * ‖xi ω‖ ^ 2)
    have hq2 : Continuous (fun t : ℝ => cv * t ^ 2) := by continuity
    refine (Lc.continuous.measurable.comp hxim).add ?_
    exact hq2.measurable.comp hxim.norm
  have hEi : Integrable E (slotLaw d M p) := by
    show Integrable (fun ω => Lc (xi ω) + cv * ‖xi ω‖ ^ 2) (slotLaw d M p)
    refine (Lc.integrable_comp hxii).add ?_
    exact hxi2.const_mul cv
  have hGi : Integrable G (slotLaw d M p) := by
    rw [hGdef]
    exact (integrable_const a).add hEi
  have hFi : Integrable F (slotLaw d M p) :=
    hGi.mono' hFm.aestronglyMeasurable (ae_of_all _ fun ω => by
      have h0 : 0 ≤ F ω := hVnonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact hpath ω)
  have hEint : (∫ ω, E ω ∂(slotLaw d M p)) = cv * ∫ ω, ‖xi ω‖ ^ 2 ∂(slotLaw d M p) := by
    show (∫ ω, Lc (xi ω) + cv * ‖xi ω‖ ^ 2 ∂(slotLaw d M p)) =
      cv * ∫ ω, ‖xi ω‖ ^ 2 ∂(slotLaw d M p)
    have hEi2 : Integrable (fun ω => cv * ‖xi ω‖ ^ 2) (slotLaw d M p) := hxi2.const_mul cv
    rw [integral_add (f := fun ω => Lc (xi ω)) (g := fun ω => cv * ‖xi ω‖ ^ 2)
      (Lc.integrable_comp hxii) hEi2, hlin0, zero_add, integral_const_mul]
  have hbnd : (∫ ω, ‖xi ω‖ ^ 2 ∂(slotLaw d M p)) ≤ (d : ℝ) * σ ^ 2 / (h ^ 2 * (m k)) := by
    have hdev := cReply_deviation (d := d) (m := m k) (g := g) (f := f) (σ := σ) (h := h)
      hg hgi hmean hvi hv (hm k) y
    have h1 : (∫ ω, ‖xi ω‖ ^ 2 ∂(slotLaw d M p))
        = ∫ b : Fin (m k) → Fin d × Bool → Ω, ‖cReply g h y b - v₀‖ ^ 2 ∂(batchLaw d (m k) p) :=
      integral_comp_preserving hp hdev.1
    rw [h1, hv0def, hydef]
    exact hdev.2
  have h5 : cv * ∫ ω, ‖xi ω‖ ^ 2 ∂(slotLaw d M p)
      ≤ cv * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (m k))) :=
    mul_le_mul_of_nonneg_left hbnd hcv0
  have hlin : (∫ ω, G ω ∂(slotLaw d M p)) = a + ∫ ω, E ω ∂(slotLaw d M p) := by
    show (∫ ω, a + E ω ∂(slotLaw d M p)) = a + ∫ ω, E ω ∂(slotLaw d M p)
    rw [integral_add (f := fun _ => a) (g := E) (integrable_const a) hEi, integral_const,
      probReal_univ, one_smul]
  refine ⟨hFi, ?_⟩
  calc (∫ ω, potential f μ xstar (cStepSched m hmM L μ θ g h k s ω) ∂(slotLaw d M p))
      = ∫ ω, F ω ∂(slotLaw d M p) := rfl
    _ ≤ ∫ ω, G ω ∂(slotLaw d M p) := integral_mono hFi hGi hpath
    _ = a + ∫ ω, E ω ∂(slotLaw d M p) := hlin
    _ = a + cv * ∫ ω, ‖xi ω‖ ^ 2 ∂(slotLaw d M p) := by rw [hEint]
    _ ≤ a + cv * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (m k))) := by linarith
    _ = (1 - θ / 2) * potential f μ xstar s + 2 * (3 / (4 * L) + 2 * θ / μ) * B
          + (1 / (2 * L) + θ ^ 2 / μ) * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (m k))) := by
          show (1 - θ / 2) * potential f μ xstar s + cb * B
              + cv * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (m k))) = _
          rw [hcvdef, hcbdef]

/-- `K` central rounds contract the momentum potential geometrically and pay the centered error
sum: the noise enters with `1 / (2 * L) + θ ^ 2 / μ`, the bias with the Young factor. -/
lemma c_sched_potential {d M : ℕ} {m : ℕ → ℕ} (hmM : ∀ k, m k ≤ M) (hm : ∀ k, 0 < m k)
    {B : ℝ} {g : Point d → Ω → ℝ} {f : Point d → ℝ} {σ L μ h θ : ℝ} {xstar : Point d}
    (hh : 0 < h) (hL : 0 < L) (hμ : 0 < μ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hθL : 16 * L * θ ^ 2 ≤ μ)
    (hbias : ∀ y, ‖cDiff h f y - gradient f y‖ ^ 2 ≤ B)
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
        (runSched (fun k s' ω => cStepSched m hmM L μ θ g h k s' ω) i K s Ξ))
        (Measure.pi (fun _ : Fin K => slotLaw d M p)) ∧
      (∫ Ξ, potential f μ xstar
        (runSched (fun k s' ω => cStepSched m hmM L μ θ g h k s' ω) i K s Ξ)
        ∂Measure.pi (fun _ : Fin K => slotLaw d M p)) ≤
      (1 - θ / 2) ^ K * potential f μ xstar s
        + ∑ k ∈ Finset.range K, (1 - θ / 2) ^ (K - 1 - k)
            * (2 * (3 / (4 * L) + 2 * θ / μ) * B
              + (1 / (2 * L) + θ ^ 2 / μ) * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (m (i + k))))) := by
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
    have h2 : (0 : ℝ) ≤ ‖cDiff h f xstar - gradient f xstar‖ ^ 2 := by positivity
    linarith
  refine sched_iterate_accuracy (d := d) (M := M)
    (step := fun k s' ω => cStepSched m hmM L μ θ g h k s' ω) (ρ := (1 : ℝ) - θ / 2)
    (c := fun k => 2 * (3 / (4 * L) + 2 * θ / μ) * B
      + (1 / (2 * L) + θ ^ 2 / μ) * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (m k))))
    (fun k => measurable_cStepSched_joint m hmM hg L μ θ h k)
    ⟨slotLaw d M p, inferInstance⟩ (potential f μ xstar) (measurable_potentialZO hf) hVnonneg hrho
    (fun k => by positivity)
    (fun k s' =>
      have h1 := c_one_step (m := m) hmM hm hh hL hμ hθ0 hθ1 hθL hbias hg hgi hmean hvi hv
        hc hgr hlip hsc hmin k s'
      ⟨h1.1, h1.2.trans (le_of_eq (add_assoc _ _ _))⟩) i K s

/-- `K` central rounds bound the expected suboptimality of the momentum output. -/
lemma c_sched_gap {d M : ℕ} {m : ℕ → ℕ} (hmM : ∀ k, m k ≤ M) (hm : ∀ k, 0 < m k)
    {B : ℝ} {g : Point d → Ω → ℝ} {f : Point d → ℝ} {σ L μ h θ : ℝ} {xstar : Point d}
    (hh : 0 < h) (hL : 0 < L) (hμ : 0 < μ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hθL : 16 * L * θ ^ 2 ≤ μ)
    (hbias : ∀ y, ‖cDiff h f y - gradient f y‖ ^ 2 ≤ B)
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
    Integrable (fun Ξ : Fin K → secantSpace d M → Ω =>
        f (runSched (fun k s' ω => cStepSched m hmM L μ θ g h k s' ω) 0 K (x0, x0) Ξ).1
          - f xstar) (Measure.pi (fun _ : Fin K => slotLaw d M p)) ∧
      (∫ Ξ, f (runSched (fun k s' ω => cStepSched m hmM L μ θ g h k s' ω) 0 K (x0, x0) Ξ).1
        - f xstar ∂Measure.pi (fun _ : Fin K => slotLaw d M p)) ≤
      (1 - θ / 2) ^ K * (f x0 - f xstar + μ / 4 * ‖x0 - xstar‖ ^ 2)
        + ∑ k ∈ Finset.range K, (1 - θ / 2) ^ (K - 1 - k)
            * (2 * (3 / (4 * L) + 2 * θ / μ) * B
              + (1 / (2 * L) + θ ^ 2 / μ) * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (m k)))) := by
  classical
  have hminf : ∀ x, f xstar ≤ f x := fun x => hmin (Set.mem_univ x)
  have hf : Measurable f :=
    (continuous_iff_continuousAt.mpr fun x => (hgr x).continuousAt).measurable
  obtain ⟨hIf, hb⟩ := c_sched_potential (d := d) (m := m) hmM hm (B := B) (g := g) (f := f)
    (σ := σ) (L := L) (μ := μ) (h := h) (θ := θ) (xstar := xstar) hh hL hμ hθ0 hθ1 hθL hbias hg
    hgi hmean hvi hv hc hgr hlip hsc hmin (i := 0) (K := K) (s := (x0, x0))
  simp only [Nat.zero_add] at hb
  have hrun2 : Measurable ((fun q : (Point d × Point d) × (Fin K → secantSpace d M → Ω) =>
      runSched (fun k s' ω => cStepSched m hmM L μ θ g h k s' ω) 0 K q.1 q.2) ∘
      (fun Ξ : Fin K → secantSpace d M → Ω => ((x0, x0), Ξ))) :=
    (measurable_runSched (fun k => measurable_cStepSched_joint m hmM hg L μ θ h k) K 0).comp
      (measurable_const.prodMk measurable_id)
  have hf1 : Measurable (fun p : Point d × Point d => p.1) := continuous_fst.measurable
  have hgapMeas : Measurable ((fun v : Point d => f v - f xstar) ∘
      (fun p : Point d × Point d => p.1) ∘
      (fun Ξ : Fin K → secantSpace d M → Ω =>
        runSched (fun k s' ω => cStepSched m hmM L μ θ g h k s' ω) 0 K (x0, x0) Ξ)) :=
    (hf.sub measurable_const).comp (hf1.comp hrun2)
  have hpoint : ∀ Ξ : Fin K → secantSpace d M → Ω,
      f (runSched (fun k s' ω => cStepSched m hmM L μ θ g h k s' ω) 0 K (x0, x0) Ξ).1
          - f xstar
        ≤ potential f μ xstar
          (runSched (fun k s' ω => cStepSched m hmM L μ θ g h k s' ω) 0 K (x0, x0) Ξ) :=
    fun Ξ => le_add_of_nonneg_right (mul_nonneg (by positivity) (sq_nonneg _))
  have hgapInt : Integrable (fun Ξ : Fin K → secantSpace d M → Ω =>
      f (runSched (fun k s' ω => cStepSched m hmM L μ θ g h k s' ω) 0 K (x0, x0) Ξ).1
        - f xstar) (Measure.pi (fun _ : Fin K => slotLaw d M p)) :=
    hIf.mono' hgapMeas.aestronglyMeasurable (ae_of_all _ fun Ξ => by
      have h0 : 0 ≤
          f (runSched (fun k s' ω => cStepSched m hmM L μ θ g h k s' ω) 0 K (x0, x0) Ξ).1
            - f xstar := sub_nonneg.mpr (hminf _)
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact hpoint Ξ)
  exact ⟨hgapInt, (integral_mono hgapInt hIf hpoint).trans hb⟩

end OracleTemplate.SecantPolyak.CentralStencil

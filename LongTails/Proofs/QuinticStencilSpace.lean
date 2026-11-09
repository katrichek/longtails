import LongTails.Proofs.SecantPolyakSpace
import LongTails.Proofs.QuinticStencilExecution

namespace OracleTemplate.SecantPolyak.QuinticStencil

open MeasureTheory ProbabilityTheory OracleTemplate SecantDescent SecantPolyak
  SecantPolyak.Accelerated ZerothOrder
open OracleTemplate.Research
open LongTails.Setups.ZerothOrderSmoothAndConvex
open scoped BigOperators RealInnerProductSpace

variable {Ω : Type} [MeasurableSpace Ω]

/-- Accuracy of the executed four-point stencil algorithm transported to the space of the problem
statement along a linear isometry. The four-point stencil pays the bias allowed by the extra
regularity of the calling setup, `rho4 * h ^ 4` per unit direction, and four times the centered
variance of one replica batch. -/
lemma q_space_accuracy {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] {d : ℕ} (hd : 0 < d)
    {e : E ≃ₗᵢ[ℝ] Point d} {f : E → ℝ} {L R σ μ ε θ h ρ4 : ℝ} {x0 : E}
    (hconv : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hL : 0 < L) (_hR : 0 ≤ R) (_hσ : 0 ≤ σ) (hμ : 0 < μ) (_hμL : μ ≤ L) (_hε : 0 < ε)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hθL : 16 * L * θ ^ 2 ≤ μ) (hh : 0 < h)
    (hρ : 0 ≤ ρ4)
    (hcb : ∀ (x v : E) (s : ℝ), 0 < s → ‖v‖ = 1 →
      |(-f (x + (2 * s) • v) + 8 * f (x + s • v) - 8 * f (x - s • v) + f (x - (2 * s) • v)) /
          (12 * s) - ⟪gradient f x, v⟫| ≤ ρ4 * s ^ 4)
    (hsc : ∀ x y, f x + ⟪gradient f x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (xstar : E) (hmin : IsMinOn f Set.univ xstar) (hdist : ‖x0 - xstar‖ ≤ R)
    {g : E → Ω → ℝ} (hgm : Measurable (Function.uncurry g))
    {p : ProbabilityMeasure Ω} {P : ProbabilityMeasure (ℕ → Ω)}
    (hind : iIndepFun (fun k (ξ : ℕ → Ω) => ξ k) (P : Measure _))
    (hmarg : ∀ k, (P : Measure _).map (fun ξ : ℕ → Ω => ξ k) = (p : Measure _))
    (hgi : ∀ x, Integrable (g x) (p : Measure Ω))
    (hmean : ∀ x, (∫ ω, g x ω ∂(p : Measure Ω)) = f x)
    (hgsq : ∀ x, Integrable (fun ω => (g x ω - f x) ^ 2) (p : Measure Ω))
    (hvar : ∀ x, (∫ ω, (g x ω - f x) ^ 2 ∂(p : Measure Ω)) ≤ σ ^ 2)
    {n : ℕ → ℕ} (hnpos : ∀ k, 0 < n k) {N : ℕ} (hnN : ∀ k, 2 * n k ≤ N) (K : ℕ)
    (hbound : (1 - θ / 2) ^ K * (L / 2 * R ^ 2 + μ / 4 * R ^ 2)
        + ∑ k ∈ Finset.range K, (1 - θ / 2) ^ (K - 1 - k)
            * (2 * (3 / (4 * L) + 2 * θ / μ) * ((d : ℝ) * (ρ4 * h ^ 4) ^ 2)
              + (1 / (2 * L) + θ ^ 2 / μ) * (4 * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (n k))))) ≤ ε) :
    let result := fun seed : Unit × (ℕ → Ω) =>
      execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
        (SecantPolyak.ofPoint e.symm (QuinticStencilMomentumZO.algorithm hd hnpos L μ θ h (e x0)))
        (fun _ => (Scheduled.schedOffsets (d := d) (fun k => 2 * n k)).off K) seed.1 seed.2
    Measurable result ∧
      Integrable (fun seed => f (result seed) - f xstar)
        ((Measure.dirac () : Measure Unit).prod (P : Measure (ℕ → Ω))) ∧
      (∫ seed, f (result seed) - f xstar
          ∂((Measure.dirac () : Measure Unit).prod (P : Measure (ℕ → Ω)))) ≤ ε := by
  classical
  intro result
  set F : Point d → ℝ := fun y => f (e.symm y) with hFdef
  set G : Point d → Ω → ℝ := fun y ω => g (e.symm y) ω with hGdef
  have hF : ∀ y, F y = f (e.symm y) := fun y => rfl
  have hG : ∀ y ω, G y ω = g (e.symm y) ω := fun y ω => rfl
  have hcont : Measurable (e.symm : Point d → E) := e.symm.continuous.measurable
  have hconvF : ConvexOn ℝ Set.univ F := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    have h1 : e.symm (a • x + b • y) = a • e.symm x + b • e.symm y := by
      rw [map_add, map_smul, map_smul]
    have h2 := hconv.2 (Set.mem_univ (e.symm x)) (Set.mem_univ (e.symm y)) ha hb hab
    rw [← h1] at h2
    simpa [F] using h2
  have hgrF' : ∀ y, HasGradientAt F (e (gradient f (e.symm y))) y :=
    fun y => ZerothOrder.gradient_coordinates e hg y
  have hgrF : ∀ y, HasGradientAt F (gradient F y) y := by
    intro y
    have h1 : gradient F y = e (gradient f (e.symm y)) := (hgrF' y).gradient
    rw [h1]
    exact hgrF' y
  have hlipF : ∀ x y, ‖gradient F x - gradient F y‖ ≤ L * ‖x - y‖ := by
    intro x y
    have hx : gradient F x = e (gradient f (e.symm x)) := (hgrF' x).gradient
    have hy : gradient F y = e (gradient f (e.symm y)) := (hgrF' y).gradient
    rw [hx, hy, ← e.map_sub, e.norm_map]
    have h3 : ‖e.symm x - e.symm y‖ = ‖x - y‖ := by rw [← e.symm.map_sub, e.symm.norm_map]
    rw [← h3]
    exact hlip (e.symm x) (e.symm y)
  have hscF : ∀ x y, F x + ⟪gradient F x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ F y := by
    intro x y
    have hx : gradient F x = e (gradient f (e.symm x)) := (hgrF' x).gradient
    have h1 : ⟪e (gradient f (e.symm x)), y - x⟫ = ⟪gradient f (e.symm x), e.symm y - e.symm x⟫ := by
      have h4 := e.inner_map_map (gradient f (e.symm x)) (e.symm (y - x))
      rw [e.apply_symm_apply, map_sub] at h4
      exact h4
    have h2 : ‖y - x‖ = ‖e.symm y - e.symm x‖ := by
      rw [← e.symm.map_sub, e.symm.norm_map]
    have h3 := hsc (e.symm x) (e.symm y)
    rw [← h1, ← h2, ← hx] at h3
    exact h3
  have hminF : IsMinOn F Set.univ (e xstar) := by
    intro y _
    show f (e.symm (e xstar)) ≤ f (e.symm y)
    rw [e.symm_apply_apply]
    exact hmin (Set.mem_univ _)
  have hdistF : ‖e x0 - e xstar‖ ≤ R := by
    rw [← e.map_sub, e.norm_map]
    exact hdist
  have hgmG : Measurable (Function.uncurry G) := by
    have h1 : Function.uncurry G = fun z : Point d × Ω => Function.uncurry g (e.symm z.1, z.2) :=
      rfl
    rw [h1]
    exact hgm.comp ((hcont.comp measurable_fst).prodMk measurable_snd)
  have hgiG : ∀ y, Integrable (G y) (p : Measure Ω) := fun y => hgi (e.symm y)
  have hmeanG : ∀ y, (∫ ω, G y ω ∂(p : Measure Ω)) = F y := fun y => hmean (e.symm y)
  have hgsqG : ∀ y, Integrable (fun ω => (G y ω - F y) ^ 2) (p : Measure Ω) :=
    fun y => hgsq (e.symm y)
  have hvarG : ∀ y, (∫ ω, (G y ω - F y) ^ 2 ∂(p : Measure Ω)) ≤ σ ^ 2 := fun y => hvar (e.symm y)
  have hcbF : ∀ (x v : Point d), ‖v‖ = 1 →
      |(-F (x + (2 * h) • v) + 8 * F (x + h • v) - 8 * F (x - h • v) + F (x - (2 * h) • v)) /
          (12 * h) - ⟪gradient F x, v⟫| ≤ ρ4 * h ^ 4 := by
    intro x v hvn
    have hv' : ‖e.symm v‖ = 1 := by rw [e.symm.norm_map]; exact hvn
    have h1 := hcb (e.symm x) (e.symm v) h hh hv'
    have h2 : F (x + (2 * h) • v) = f (e.symm x + (2 * h) • e.symm v) := by
      show f (e.symm (x + (2 * h) • v)) = _
      rw [map_add, map_smul]
    have h3 : F (x - (2 * h) • v) = f (e.symm x - (2 * h) • e.symm v) := by
      show f (e.symm (x - (2 * h) • v)) = _
      rw [map_sub, map_smul]
    have h4 : F (x + h • v) = f (e.symm x + h • e.symm v) := by
      show f (e.symm (x + h • v)) = _
      rw [map_add, map_smul]
    have h5 : F (x - h • v) = f (e.symm x - h • e.symm v) := by
      show f (e.symm (x - h • v)) = _
      rw [map_sub, map_smul]
    have h6 : gradient F x = e (gradient f (e.symm x)) := (hgrF' x).gradient
    have h7 : ⟪e (gradient f (e.symm x)), v⟫ = ⟪gradient f (e.symm x), e.symm v⟫ := by
      have h8 := e.inner_map_map (gradient f (e.symm x)) (e.symm v)
      rw [e.apply_symm_apply] at h8
      exact h8
    rw [h2, h3, h4, h5, h6, h7] at *
    exact h1
  have hbiasF : ∀ y : Point d, ‖qDiff h F y - gradient F y‖ ^ 2 ≤ (d : ℝ) * (ρ4 * h ^ 4) ^ 2 :=
    fun y => qDiff_bias_sq (β := ρ4 * h ^ 4) (by positivity) hcbF y
  have hzero : gradient f xstar = 0 := by
    apply (_root_.InnerProductSpace.toDual ℝ E).injective
    simpa using (hmin.isLocalMin Filter.univ_mem).hasFDerivAt_eq_zero (hg xstar).hasFDerivAt
  have hgap : ∀ y : E, f y - f xstar ≤ L / 2 * ‖y - xstar‖ ^ 2 := by
    intro y
    have h1 := _root_.OracleTemplate.Gradient.smooth_upper_bound hg hlip xstar y
    rw [hzero, inner_zero_left, add_zero] at h1
    exact sub_le_iff_le_add'.mpr h1
  let OGp : Oracle (Point d) ℝ :=
    { Seed := fun _ => Ω, law := P, answer := fun _ (_, t) ω => g (e.symm t) ω }
  obtain ⟨hIntP, hbP⟩ := q_exec_accuracy (d := d) (N := N) (K := K) (n := n) hnN hnpos hd
    (g := G) (f := F) (σ := σ) (L := L) (μ := μ) (h := h) (θ := θ)
    (B := (d : ℝ) * (ρ4 * h ^ 4) ^ 2)
    (x0 := e x0) (xstar := e xstar) hh hL hμ hθ0 hθ1 hθL hbiasF hgmG hgiG hmeanG hgsqG hvarG
    hconvF hgrF hlipF hscF hminF P hind hmarg
    (Scheduled.schedOffsets (d := d) (fun k => 2 * n k))
  have hex : (fun seed : Unit × (ℕ → Ω) =>
      execute OGp (QuinticStencilMomentumZO.algorithm hd hnpos L μ θ h (e x0))
        (fun _ => (Scheduled.schedOffsets (d := d) (fun k => 2 * n k)).off K) seed.1 seed.2)
      = fun seed : Unit × (ℕ → Ω) =>
        (Scheduled.runSched (qStepSched n hnN L μ θ G h) 0 K (e x0, e x0)
          (fun k : Fin K => fun t : secantSpace d N =>
            seed.2 (Scheduled.schedIndex (d := d) (M := N) (fun k => 2 * n k)
              (Scheduled.schedOffsets (d := d) (fun k => 2 * n k)) K ⟨k, t⟩))).1 := by
    funext seed
    exact execute_qAlgorithm hd (hnN := hnN) hnpos L μ θ h (e x0)
      (Scheduled.schedOffsets (d := d) (fun k => 2 * n k)) G seed.2 P K
  have heq : result = fun seed : Unit × (ℕ → Ω) =>
      e.symm ((Scheduled.runSched (qStepSched n hnN L μ θ G h) 0 K (e x0, e x0)
        (fun k : Fin K => fun t : secantSpace d N =>
          seed.2 (Scheduled.schedIndex (d := d) (M := N) (fun k => 2 * n k)
            (Scheduled.schedOffsets (d := d) (fun k => 2 * n k)) K ⟨k, t⟩))).1) := by
    funext seed
    exact (execute_ofPoint e.symm (g := g)
        (K := (Scheduled.schedOffsets (d := d) (fun k => 2 * n k)).off K) seed.1 seed.2).trans
      (congrArg (fun w : Point d => e.symm w) (congrFun hex seed))
  have hlift : Measurable (fun xi : ℕ → Ω => fun k : Fin K => fun t : secantSpace d N =>
      xi (Scheduled.schedIndex (d := d) (M := N) (fun k => 2 * n k)
        (Scheduled.schedOffsets (d := d) (fun k => 2 * n k)) K ⟨k, t⟩)) := by
    fun_prop
  have hrun : Measurable (fun seed : Unit × (ℕ → Ω) =>
      Scheduled.runSched (qStepSched n hnN L μ θ G h) 0 K (e x0, e x0)
        (fun k : Fin K => fun t : secantSpace d N =>
          seed.2 (Scheduled.schedIndex (d := d) (M := N) (fun k => 2 * n k)
            (Scheduled.schedOffsets (d := d) (fun k => 2 * n k)) K ⟨k, t⟩))) :=
    (Scheduled.measurable_runSched (S := Point d × Point d)
      (fun k => measurable_qStepSched_joint n hnN hgmG L μ θ h k) K 0).comp
      (measurable_const.prodMk (hlift.comp measurable_snd))
  have hfun : (fun seed : Unit × (ℕ → Ω) => f (result seed) - f xstar)
      = (fun ξ : ℕ → Ω =>
          F (execute OGp (QuinticStencilMomentumZO.algorithm hd hnpos L μ θ h (e x0))
            (fun _ => (Scheduled.schedOffsets (d := d) (fun k => 2 * n k)).off K) () ξ) -
            F (e xstar)) ∘
          Prod.snd := by
    funext seed
    simp only [heq]
    rw [← congrFun hex seed, ← congrArg f (e.symm_apply_apply xstar)]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [heq]
    exact hcont.comp (continuous_fst.measurable.comp hrun)
  · have hi2 : Integrable (fun seed : Unit × (ℕ → Ω) =>
        F (execute OGp (QuinticStencilMomentumZO.algorithm hd hnpos L μ θ h (e x0))
          (fun _ => (Scheduled.schedOffsets (d := d) (fun k => 2 * n k)).off K) () seed.2)
          - F (e xstar))
        ((Measure.dirac () : Measure Unit).prod (P : Measure (ℕ → Ω))) :=
      (measurePreserving_snd).integrable_comp_of_integrable (ε := ℝ)
        (g := fun ξ : ℕ → Ω =>
          F (execute OGp (QuinticStencilMomentumZO.algorithm hd hnpos L μ θ h (e x0))
            (fun _ => (Scheduled.schedOffsets (d := d) (fun k => 2 * n k)).off K) () ξ)
            - F (e xstar)) hIntP
    exact hi2.congr (ae_of_all _ fun seed => (congrFun hfun seed).symm)
  · have h2 : F (e x0) - F (e xstar) + μ / 4 * ‖e x0 - e xstar‖ ^ 2
        ≤ L / 2 * R ^ 2 + μ / 4 * R ^ 2 := by
      have h3 : ‖x0 - xstar‖ ^ 2 ≤ R ^ 2 := by
        refine pow_le_pow_left₀ (norm_nonneg _) hdist 2
      have h4 : f x0 - f xstar ≤ L / 2 * ‖x0 - xstar‖ ^ 2 := hgap x0
      have h5 : L / 2 * ‖x0 - xstar‖ ^ 2 ≤ L / 2 * R ^ 2 :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      have h6 : F (e x0) - F (e xstar) = f x0 - f xstar := by
        show f (e.symm (e x0)) - f (e.symm (e xstar)) = f x0 - f xstar
        rw [e.symm_apply_apply, e.symm_apply_apply]
      have h7 : ‖e x0 - e xstar‖ ^ 2 = ‖x0 - xstar‖ ^ 2 := by rw [← e.map_sub, e.norm_map]
      rw [h6, h7]
      exact add_le_add (le_trans h4 h5) (mul_le_mul_of_nonneg_left h3 (by positivity))
    calc (∫ seed : Unit × (ℕ → Ω), f (result seed) - f xstar
            ∂((Measure.dirac () : Measure Unit).prod (P : Measure (ℕ → Ω))))
        = ∫ ξ : ℕ → Ω,
            F (execute OGp (QuinticStencilMomentumZO.algorithm hd hnpos L μ θ h (e x0))
                (fun _ => (Scheduled.schedOffsets (d := d) (fun k => 2 * n k)).off K) () ξ)
              - F (e xstar) ∂(P : Measure (ℕ → Ω)) := by
          have hpush : (∫ seed : Unit × (ℕ → Ω),
                (fun ξ : ℕ → Ω => F (execute OGp
                    (QuinticStencilMomentumZO.algorithm hd hnpos L μ θ h (e x0))
                    (fun _ => (Scheduled.schedOffsets (d := d) (fun k => 2 * n k)).off K) () ξ)
                  - F (e xstar)) (seed.2)
                ∂((Measure.dirac () : Measure Unit).prod (P : Measure (ℕ → Ω))))
              = ∫ ξ : ℕ → Ω, F (execute OGp
                  (QuinticStencilMomentumZO.algorithm hd hnpos L μ θ h (e x0))
                  (fun _ => (Scheduled.schedOffsets (d := d) (fun k => 2 * n k)).off K) () ξ)
                  - F (e xstar) ∂(P : Measure (ℕ → Ω)) :=
            integral_comp_preserving (φ := fun ξ : ℕ → Ω =>
              F (execute OGp (QuinticStencilMomentumZO.algorithm hd hnpos L μ θ h (e x0))
                (fun _ => (Scheduled.schedOffsets (d := d) (fun k => 2 * n k)).off K) () ξ)
                - F (e xstar))
              measurePreserving_snd hIntP
          rw [hfun]
          exact hpush
      _ ≤ (1 - θ / 2) ^ K * (F (e x0) - F (e xstar) + μ / 4 * ‖e x0 - e xstar‖ ^ 2)
            + ∑ k ∈ Finset.range K, (1 - θ / 2) ^ (K - 1 - k)
              * (2 * (3 / (4 * L) + 2 * θ / μ) * ((d : ℝ) * (ρ4 * h ^ 4) ^ 2)
                + (1 / (2 * L) + θ ^ 2 / μ) * (4 * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (n k))))) := hbP
      _ ≤ (1 - θ / 2) ^ K * (L / 2 * R ^ 2 + μ / 4 * R ^ 2)
            + ∑ k ∈ Finset.range K, (1 - θ / 2) ^ (K - 1 - k)
              * (2 * (3 / (4 * L) + 2 * θ / μ) * ((d : ℝ) * (ρ4 * h ^ 4) ^ 2)
                + (1 / (2 * L) + θ ^ 2 / μ) * (4 * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (n k))))) := by
          refine add_le_add
            (mul_le_mul_of_nonneg_left h2
              (pow_nonneg (by
                have : θ / 2 ≤ 1 := by linarith
                linarith) K)) (le_refl _)
      _ ≤ ε := hbound

end OracleTemplate.SecantPolyak.QuinticStencil

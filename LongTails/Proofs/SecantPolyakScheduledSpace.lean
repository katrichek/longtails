import LongTails.Proofs.SecantPolyakSpace
import LongTails.Proofs.SecantPolyakScheduledExecution

namespace OracleTemplate.SecantPolyak.Scheduled

open MeasureTheory ProbabilityTheory OracleTemplate SecantDescent SecantPolyak ZerothOrder
open LongTails.Setups.ZerothOrderSmoothAndConvex
open scoped BigOperators

variable {Ω : Type} [MeasurableSpace Ω]

/-- Accuracy of the graded scheduled secant algorithm transported to the space of the problem
statement along a linear isometry. Each round's batch error is charged once and discounted by the
contraction of the rounds that follow it. -/
lemma sched_space_accuracy {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] {d : ℕ} (hd : 0 < d)
    {e : E ≃ₗᵢ[ℝ] Point d} {f : E → ℝ} {L R σ μ ε : ℝ} {x0 : E}
    (hconv : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hL : 0 < L) (_hR : 0 ≤ R) (_hσ : 0 ≤ σ) (hμ : 0 < μ) (hμL : μ ≤ L) (hε : 0 < ε)
    (xstar : E) (hmin : IsMinOn f Set.univ xstar) (hdist : ‖x0 - xstar‖ ≤ R)
    (hpl : ∀ x, 2 * μ * (f x - f xstar) ≤ ‖gradient f x‖ ^ 2)
    {Ω : Type} [MeasurableSpace Ω] {g : E → Ω → ℝ} (hgm : Measurable (Function.uncurry g))
    {p : ProbabilityMeasure Ω} {P : ProbabilityMeasure (ℕ → Ω)}
    (hind : iIndepFun (fun k (ξ : ℕ → Ω) => ξ k) (P : Measure _))
    (hmarg : ∀ k, (P : Measure _).map (fun ξ : ℕ → Ω => ξ k) = (p : Measure _))
    (hgi : ∀ x, Integrable (g x) (p : Measure Ω))
    (hmean : ∀ x, (∫ ω, g x ω ∂(p : Measure Ω)) = f x)
    (hgsq : ∀ x, Integrable (fun ω => (g x ω - f x) ^ 2) (p : Measure Ω))
    (hvar : ∀ x, (∫ ω, (g x ω - f x) ^ 2 ∂(p : Measure Ω)) ≤ σ ^ 2)
    {m : ℕ → ℕ} (hm : ∀ k, 0 < m k) {M : ℕ} (hmM : ∀ k, m k ≤ M) (K : ℕ)
    (hbound : (1 - μ / L) ^ K * (L / 2 * R ^ 2)
        + ∑ k ∈ Finset.range K, (1 - μ / L) ^ (K - 1 - k)
            * ((1 / L) * batchError d (m k) σ L
              (Real.sqrt (μ * ε / (4 * (d : ℝ) * L ^ 2)))) ≤ ε) :
    let result := fun seed : Unit × (ℕ → Ω) =>
      execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
        (ofPoint e.symm
          (schedDescent hd hm L (Real.sqrt (μ * ε / (4 * (d : ℝ) * L ^ 2))) (e x0)))
        (fun _ => (schedOffsets (d := d) m).off K) seed.1 seed.2
    Measurable result ∧
      Integrable (fun seed => f (result seed) - f xstar)
        ((Measure.dirac () : Measure Unit).prod (P : Measure (ℕ → Ω))) ∧
      (∫ seed, f (result seed) - f xstar
          ∂((Measure.dirac () : Measure Unit).prod (P : Measure (ℕ → Ω)))) ≤ ε := by
  classical
  intro result
  let hband : ℝ := Real.sqrt (μ * ε / (4 * (d : ℝ) * L ^ 2))
  have hhb : 0 < hband := by
    refine Real.sqrt_pos.mpr (div_pos (mul_pos hμ hε) ?_)
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
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
  have hminF : IsMinOn F Set.univ (e xstar) := by
    intro y _
    show f (e.symm (e xstar)) ≤ f (e.symm y)
    rw [e.symm_apply_apply]
    exact hmin (Set.mem_univ _)
  have hdistF : ‖e x0 - e xstar‖ ≤ R := by
    rw [← e.map_sub, e.norm_map]
    exact hdist
  have hplF : ∀ y, 2 * μ * (F y - F (e xstar)) ≤ ‖gradient F y‖ ^ 2 := by
    intro y
    have hy : gradient F y = e (gradient f (e.symm y)) := (hgrF' y).gradient
    rw [hy, hF, hF, e.symm_apply_apply, e.norm_map]
    exact hpl _
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
  have hzero : gradient f xstar = 0 := by
    apply (_root_.InnerProductSpace.toDual ℝ E).injective
    simpa using (hmin.isLocalMin Filter.univ_mem).hasFDerivAt_eq_zero (hg xstar).hasFDerivAt
  have hgap : ∀ y : E, f y - f xstar ≤ L / 2 * ‖y - xstar‖ ^ 2 := by
    intro y
    have h1 := _root_.OracleTemplate.Gradient.smooth_upper_bound hg hlip xstar y
    rw [hzero, inner_zero_left, add_zero] at h1
    exact sub_le_iff_le_add'.mpr h1
  let OG : Oracle (Point d) ℝ :=
    { Seed := fun _ => Ω, law := P, answer := fun _ (_, t) ω => g (e.symm t) ω }
  let Aco := schedDescent hd hm L hband (e x0)
  let execCo : Unit × (ℕ → Ω) → Point d := fun seed =>
    execute OG Aco (fun _ => (schedOffsets (d := d) m).off K) seed.1 seed.2
  have hlif : Measurable (fun xi : ℕ → Ω => fun k : Fin K => fun t : secantSpace d M =>
      xi (schedIndex (d := d) (M := M) m (schedOffsets (d := d) m) K ⟨k, t⟩)) := by
    classical
    fun_prop
  have hco := Scheduled.exec_accuracy (d := d) (M := M) (K := K) (m := m) (x0 := e x0)
    (xstar := e xstar) (h := hband) hmM hm hd
    (g := G) (f := F) (σ := σ) (L := L) (μ := μ)
    (hh := hhb) (hL := hL) (hμ := hμ) (hμL := hμL) (hg := hgmG) (hgi := hgiG) (hmean := hmeanG)
    (hvi := hgsqG) (hv := hvarG) (hc := hconvF) (hgr := hgrF) (hlip := hlipF) (hmin := hminF)
    (hpl := hplF) P hind hmarg (schedOffsets (d := d) m)
  have heq : result = fun seed : Unit × (ℕ → Ω) => e.symm (execCo seed) := by
    funext seed
    exact execute_ofPoint e.symm (g := g) (K := (schedOffsets (d := d) m).off K) seed.1 seed.2
  have hfun : (fun seed : Unit × (ℕ → Ω) => f (result seed) - f xstar)
      = (fun seed : Unit × (ℕ → Ω) => F (execCo seed) - F (e xstar)) := by
    funext seed
    rw [heq, hF, hF, e.symm_apply_apply]
  have hex : execCo = fun seed : Unit × (ℕ → Ω) =>
      runSched (stepSched m hmM L G hband) 0 K (e x0)
        (fun k : Fin K => fun t : secantSpace d M => seed.2 (schedIndex (d := d) (M := M) m
          (schedOffsets (d := d) m) K ⟨k, t⟩)) := by
    funext seed
    exact execute_schedDescent hd (hmM := hmM) hm L hband (e x0) (schedOffsets (d := d) m) G
      seed.2 P K
  have ha1 : Integrable (fun Ξ => F (runSched (stepSched m hmM L G hband) 0 K (e x0) Ξ) - F (e xstar))
      (Measure.pi fun _ : Fin K => slotLaw d M p) :=
    (Scheduled.sched_accuracy (d := d) (M := M) (K := K) (m := m) (x0 := e x0)
      hmM hm hhb hL hμ hμL hgmG hgiG hmeanG hgsqG hvarG hconvF hgrF hlipF hminF hplF).1
  have hcurry : MeasurePreserving (fun ξ : ℕ → Ω => fun k : Fin K => fun t : secantSpace d M =>
      ξ (schedIndex (d := d) (M := M) m (schedOffsets (d := d) m) K ⟨k, t⟩))
      (P : Measure (ℕ → Ω)) (Measure.pi fun _ : Fin K => slotLaw d M p) :=
    sched_stream_law_curry (M := M) m (schedOffsets (d := d) m) K P hind hmarg
  have hint : Integrable (fun ξ : ℕ → Ω =>
        F (runSched (stepSched m hmM L G hband) 0 K (e x0) (fun k : Fin K => fun t : secantSpace d M =>
              ξ (schedIndex (d := d) (M := M) m (schedOffsets (d := d) m) K ⟨k, t⟩))) - F (e xstar))
      (P : Measure (ℕ → Ω)) := hcurry.integrable_comp_of_integrable ha1
  have hrec : (∫ seed : Unit × (ℕ → Ω), F (execCo seed) - F (e xstar)
          ∂((Measure.dirac () : Measure Unit).prod (P : Measure (ℕ → Ω))))
      = ∫ ξ : ℕ → Ω, F (runSched (stepSched m hmM L G hband) 0 K (e x0) (fun k : Fin K => fun t : secantSpace d M =>
              ξ (schedIndex (d := d) (M := M) m (schedOffsets (d := d) m) K ⟨k, t⟩))) -
          F (e xstar) ∂(P : Measure (ℕ → Ω)) := by
    rw [hex]
    exact integral_comp_preserving measurePreserving_snd hint
  have hco' : (∫ ξ : ℕ → Ω, F (runSched (stepSched m hmM L G hband) 0 K (e x0) (fun k : Fin K => fun t : secantSpace d M =>
              ξ (schedIndex (d := d) (M := M) m (schedOffsets (d := d) m) K ⟨k, t⟩))) -
          F (e xstar) ∂(P : Measure (ℕ → Ω)))
      ≤ (1 - μ / L) ^ K * (F (e x0) - F (e xstar))
        + ∑ k ∈ Finset.range K, (1 - μ / L) ^ (K - 1 - k) * ((1 / L) * batchError d (m k) σ L hband) := by
    have h1 : (fun ξ : ℕ → Ω => F (execute OG (schedDescent hd hm L hband (e x0))
          (fun _ => (schedOffsets (d := d) m).off K) () ξ) - F (e xstar))
        = (fun ξ : ℕ → Ω => F (runSched (stepSched m hmM L G hband) 0 K (e x0) (fun k : Fin K => fun t : secantSpace d M =>
              ξ (schedIndex (d := d) (M := M) m (schedOffsets (d := d) m) K ⟨k, t⟩))) -
            F (e xstar)) := by
      refine funext fun ξ => congrArg (fun v => F v - F (e xstar))
        (execute_schedDescent hd (hmM := hmM) hm L hband (e x0) (schedOffsets (d := d) m) G ξ P K)
    rw [← h1]
    exact hco
  refine ⟨?_, ?_, ?_⟩
  · rw [heq]
    rw [hex]
    exact hcont.comp ((measurable_runSched (S := Point d)
      (measurable_stepSched_joint (L := L) m hmM hgmG hband) K 0).comp
      (measurable_const.prodMk (hlif.comp measurable_snd)))
  · rw [hfun]
    have hmp : MeasurePreserving (fun seed : Unit × (ℕ → Ω) =>
        fun k : Fin K => fun t : secantSpace d M =>
          seed.2 (schedIndex (d := d) (M := M) m (schedOffsets (d := d) m) K ⟨k, t⟩))
        ((Measure.dirac () : Measure Unit).prod (P : Measure (ℕ → Ω)))
        (Measure.pi fun _ : Fin K => slotLaw d M p) :=
      (sched_stream_law_curry (M := M) m (schedOffsets (d := d) m) K P hind hmarg).comp
        measurePreserving_snd
    rw [hex]
    exact hmp.integrable_comp_of_integrable
      (Scheduled.sched_accuracy (d := d) (M := M) (K := K) (m := m) (x0 := e x0)
        hmM hm hhb hL hμ hμL hgmG hgiG hmeanG hgsqG hvarG hconvF hgrF hlipF hminF hplF).1
  · rw [hfun]
    have h2 : F (e x0) - F (e xstar) ≤ L / 2 * R ^ 2 := by
      simp only [hF, e.symm_apply_apply]
      have h3 : ‖x0 - xstar‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hdist 2
      have h4 : f x0 - f xstar ≤ L / 2 * ‖x0 - xstar‖ ^ 2 := hgap x0
      have h5 : L / 2 * ‖x0 - xstar‖ ^ 2 ≤ L / 2 * R ^ 2 :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      exact le_trans h4 h5
    calc (∫ seed : Unit × (ℕ → Ω), F (execCo seed) - F (e xstar)
            ∂((Measure.dirac () : Measure Unit).prod (P : Measure (ℕ → Ω))))
        = ∫ ξ : ℕ → Ω, F (runSched (stepSched m hmM L G hband) 0 K (e x0) (fun k : Fin K => fun t : secantSpace d M =>
              ξ (schedIndex (d := d) (M := M) m (schedOffsets (d := d) m) K ⟨k, t⟩))) -
            F (e xstar) ∂(P : Measure (ℕ → Ω)) := hrec
      _ ≤ (1 - μ / L) ^ K * (F (e x0) - F (e xstar))
          + ∑ k ∈ Finset.range K, (1 - μ / L) ^ (K - 1 - k)
              * ((1 / L) * batchError d (m k) σ L hband) := hco'
      _ ≤ (1 - μ / L) ^ K * (L / 2 * R ^ 2)
          + ∑ k ∈ Finset.range K, (1 - μ / L) ^ (K - 1 - k)
              * ((1 / L) * batchError d (m k) σ L
                (Real.sqrt (μ * ε / (4 * (d : ℝ) * L ^ 2)))) := by
          refine add_le_add
            (mul_le_mul_of_nonneg_left h2
              (pow_nonneg (by
                have : μ / L ≤ 1 := (div_le_one hL).mpr hμL
                linarith) K)) (le_refl _)
      _ ≤ ε := hbound

end OracleTemplate.SecantPolyak.Scheduled

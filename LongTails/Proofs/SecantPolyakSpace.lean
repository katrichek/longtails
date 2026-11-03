import LongTails.Proofs.SecantPolyakStream
import LongTails.Proofs.GdConvex
import LongTails.Proofs.ZerothOrderConvergence

/-!
Batched secant descent on the space of the problem statement. The analysis lives in
`EuclideanSpace ℝ (Fin d)`; this module transports it along a linear isometry and turns the
proved bound into concrete tuning parameters.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.SecantPolyak

open ContinuizedSimilarQuasar GapStrongGrowth SecantDescent StochasticGradient ZerothOrder
open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {Ω : Type} [MeasurableSpace Ω]

/-- Conjugate a coordinate algorithm by a map into the problem space. -/
noncomputable def ofPoint {E : Type} {d : ℕ} (u : Point d → E)
    (A : Algorithm (Point d) ℝ (Point d)) : Algorithm E ℝ E where
  Seed := A.Seed
  law := A.law
  State := A.State
  initial := A.initial
  query s := (0, u ((A.query s).2))
  update s r := A.update s r
  output s := u (A.output s)

/-- Running the conjugated algorithm is running the coordinate algorithm and mapping back. -/
lemma execute_ofPoint {E : Type} {d : ℕ} (u : Point d → E)
    {A : Algorithm (Point d) ℝ (Point d)} {P : ProbabilityMeasure (ℕ → Ω)}
    (g : E → Ω → ℝ) (K : ℕ) (sd : A.Seed) (ξ : ℕ → Ω) :
    execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
        (ofPoint u A) (fun _ => K) sd ξ
      = u (execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, t) ω => g (u t) ω }
          A (fun _ => K) sd ξ) := by
  have h1 := execute_advance (law := P) (g := fun x : E => g x) (A := ofPoint u A) K sd ξ
  have h2 := execute_advance (law := P) (g := fun t : Point d => g (u t)) (A := A) K sd ξ
  exact h1.trans (congrArg u h2.symm)

namespace Tuning

variable {L R σ μ ε h : ℝ} {d K m : ℕ}

/-- The geometric term is at most half of the target accuracy. -/
lemma gap_term (hL : 0 < L) (hμL : μ ≤ L) (hε : 0 < ε)
    (hLambda : (K : ℝ) * (μ / L) ≥ 1 + Real.log (1 + 2 * L * R ^ 2 / ε)) :
    (1 - μ / L) ^ K * (L / 2 * R ^ 2) ≤ ε / 2 := by
  have hρ0 : 0 ≤ 1 - μ / L := by
    have : μ / L ≤ 1 := (div_le_one hL).mpr hμL
    linarith
  have hbase : 1 - μ / L ≤ Real.exp (-(μ / L)) := by
    linarith [Real.add_one_le_exp (-(μ / L))]
  have hz : 0 < 1 + 2 * L * R ^ 2 / ε := by positivity
  have he1 : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hzl : 0 ≤ Real.exp (-Real.log (1 + 2 * L * R ^ 2 / ε)) := by positivity
  have hexp : Real.exp (-Real.log (1 + 2 * L * R ^ 2 / ε)) =
      (1 + 2 * L * R ^ 2 / ε)⁻¹ := by rw [Real.exp_neg, Real.exp_log hz]
  have hpow : (1 - μ / L) ^ K ≤ (1 + 2 * L * R ^ 2 / ε)⁻¹ := by
    calc (1 - μ / L) ^ K ≤ Real.exp (-(μ / L)) ^ K := pow_le_pow_left₀ hρ0 hbase K
      _ = Real.exp ((K : ℝ) * -(μ / L)) := (Real.exp_nat_mul _ _).symm
      _ = Real.exp (-((K : ℝ) * (μ / L))) := by rw [neg_mul_eq_mul_neg]
      _ ≤ Real.exp (-(1 + Real.log (1 + 2 * L * R ^ 2 / ε))) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp (-1) * Real.exp (-Real.log (1 + 2 * L * R ^ 2 / ε)) := by
          rw [← Real.exp_add]
          ring_nf
      _ ≤ 1 * Real.exp (-Real.log (1 + 2 * L * R ^ 2 / ε)) :=
          mul_le_mul_of_nonneg_right he1 hzl
      _ = (1 + 2 * L * R ^ 2 / ε)⁻¹ := by rw [one_mul, hexp]
  have h5 : (1 + 2 * L * R ^ 2 / ε) * (ε / 2) = ε / 2 + L * R ^ 2 := by field_simp
  have h6 : L / 2 * R ^ 2 ≤ (1 + 2 * L * R ^ 2 / ε) * (ε / 2) := by
    rw [h5]
    nlinarith [sq_nonneg R, mul_nonneg (le_of_lt hL) (sq_nonneg R)]
  calc (1 - μ / L) ^ K * (L / 2 * R ^ 2) ≤ (1 + 2 * L * R ^ 2 / ε)⁻¹ * (L / 2 * R ^ 2) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
    _ ≤ (1 + 2 * L * R ^ 2 / ε)⁻¹ * ((1 + 2 * L * R ^ 2 / ε) * (ε / 2)) :=
        mul_le_mul_of_nonneg_left h6 (by positivity)
    _ = ε / 2 := by field_simp

/-- The bandwidth term is at most a quarter of the target accuracy. -/
lemma bias_term (hL : 0 < L) (hε : 0 < ε) (hK : 0 < K) (hd : 0 < d)
    (hh : h = Real.sqrt (ε / (2 * (K : ℝ) * (d : ℝ) * L))) :
    (K : ℝ) * (1 / L) * (2 * ((d : ℝ) * (L * h / 2) ^ 2)) ≤ ε / 4 := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have h2 : h ^ 2 = ε / (2 * (K : ℝ) * (d : ℝ) * L) := by
    rw [hh, Real.sq_sqrt]
    positivity
  have h3 : (K : ℝ) * (1 / L) * (2 * ((d : ℝ) * (L * h / 2) ^ 2))
      = (K : ℝ) * (d : ℝ) * L * h ^ 2 / 2 := by field_simp
  rw [h3, h2]
  field_simp
  linarith

/-- The noise term is at most a quarter of the target accuracy. -/
lemma noise_term (hL : 0 < L) (hK : 0 < K) (hd : 0 < d) (hm : 0 < m)
    (hh : 0 < h) (hnoise : ε * (L * (h ^ 2 * (m : ℝ))) ≥ 32 * (K : ℝ) * (d : ℝ) * σ ^ 2) :
    (K : ℝ) * (1 / L) * (8 * (d : ℝ) * σ ^ 2 / (h ^ 2 * (m : ℝ))) ≤ ε / 4 := by
  have h1 : (K : ℝ) * (1 / L) * (8 * (d : ℝ) * σ ^ 2 / (h ^ 2 * (m : ℝ)))
      = (K : ℝ) * (8 * (d : ℝ) * σ ^ 2) / (L * (h ^ 2 * (m : ℝ))) := by field_simp
  rw [h1]
  apply (div_le_iff₀ (by positivity : 0 < L * (h ^ 2 * (m : ℝ)))).mpr
  nlinarith [hnoise]

/-- Geometric contraction plus batch error fits the target accuracy. -/
lemma tuning_bound (hL : 0 < L) (_hR : 0 ≤ R) (_hσ : 0 ≤ σ) (_hμ : 0 < μ) (hμL : μ ≤ L)
    (hε : 0 < ε) (hK : 0 < K) (hd : 0 < d) (hm : 0 < m)
    (hLambda : (K : ℝ) * (μ / L) ≥ 1 + Real.log (1 + 2 * L * R ^ 2 / ε))
    (hh : h = Real.sqrt (ε / (2 * (K : ℝ) * (d : ℝ) * L)))
    (hnoise : (m : ℝ) * ε ^ 2 ≥ 64 * (K : ℝ) ^ 2 * (d : ℝ) ^ 2 * σ ^ 2) :
    (1 - μ / L) ^ K * (L / 2 * R ^ 2) + (K : ℝ) * (1 / L) * batchError d m σ L h ≤ ε := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hh0 : 0 < h := by
    rw [hh]
    refine Real.sqrt_pos.mpr (div_pos hε ?_)
    positivity
  have hsq : h ^ 2 = ε / (2 * (K : ℝ) * (d : ℝ) * L) := by
    rw [hh, Real.sq_sqrt]
    positivity
  have hkey : ε * (L * (h ^ 2 * (m : ℝ))) = (m : ℝ) * ε ^ 2 / (2 * (K : ℝ) * (d : ℝ)) := by
    rw [hsq]
    field_simp
  have hnoise' : ε * (L * (h ^ 2 * (m : ℝ))) ≥ 32 * (K : ℝ) * (d : ℝ) * σ ^ 2 := by
    rw [hkey]
    apply (le_div_iff₀ (by positivity : 0 < (2 : ℝ) * (K : ℝ) * (d : ℝ))).mpr
    nlinarith [hnoise]
  have hg := gap_term hL hμL hε hLambda
  have hb := bias_term hL hε hK hd hh
  have hn := noise_term hL hK hd hm hh0 hnoise'
  have hsum : (K : ℝ) * (1 / L) * batchError d m σ L h
      ≤ (K : ℝ) * (1 / L) * (2 * ((d : ℝ) * (L * h / 2) ^ 2))
        + (K : ℝ) * (1 / L) * (8 * (d : ℝ) * σ ^ 2 / (h ^ 2 * (m : ℝ))) := by
    unfold batchError
    have h1 : 0 ≤ (K : ℝ) * (1 / L) := by positivity
    have h2 : 0 ≤ 8 * (d : ℝ) * σ ^ 2 / (h ^ 2 * (m : ℝ)) := by positivity
    have h3 : 0 ≤ 2 * ((d : ℝ) * (L * h / 2) ^ 2) := by positivity
    nlinarith
  calc (1 - μ / L) ^ K * (L / 2 * R ^ 2) + (K : ℝ) * (1 / L) * batchError d m σ L h
      ≤ ε / 2 + (K : ℝ) * (1 / L) * batchError d m σ L h := add_le_add hg (le_refl _)
    _ ≤ ε / 2 + ((K : ℝ) * (1 / L) * (2 * ((d : ℝ) * (L * h / 2) ^ 2))
        + (K : ℝ) * (1 / L) * (8 * (d : ℝ) * σ ^ 2 / (h ^ 2 * (m : ℝ)))) := by
          linarith
    _ ≤ ε / 2 + (ε / 4 + ε / 4) := by linarith
    _ = ε := by ring

end Tuning

/-- Secant descent executed on the problem space along a linear isometry. -/
lemma space_accuracy {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
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
    (K m : ℕ) (hK : 0 < K) (hm : 0 < m)
    (hbound : (1 - μ / L) ^ K * (L / 2 * R ^ 2)
        + (K : ℝ) * (1 / L)
            * batchError d m σ L (Real.sqrt (ε / (2 * (K : ℝ) * (d : ℝ) * L))) ≤ ε) :
    let result := fun seed : Unit × (ℕ → Ω) =>
      execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
        (ofPoint e.symm
          (secantDescent hd hm L (Real.sqrt (ε / (2 * (K : ℝ) * (d : ℝ) * L))) (e x0)))
        (fun _ => K * (2 * d * m)) seed.1 seed.2
    Measurable result ∧
      Integrable (fun seed => f (result seed) - f xstar)
        ((Measure.dirac () : Measure Unit).prod (P : Measure (ℕ → Ω))) ∧
      (∫ seed, f (result seed) - f xstar
          ∂((Measure.dirac () : Measure Unit).prod (P : Measure (ℕ → Ω)))) ≤ ε := by
  classical
  intro result
  let hband : ℝ := Real.sqrt (ε / (2 * (K : ℝ) * (d : ℝ) * L))
  have hhb : 0 < hband := by
    refine Real.sqrt_pos.mpr (div_pos hε ?_)
    have hK' : (0 : ℝ) < K := by exact_mod_cast hK
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
  let Aco := secantDescent hd hm L hband (e x0)
  let execCo : Unit × (ℕ → Ω) → Point d := fun seed =>
    execute OG Aco (fun _ => K * (2 * d * m)) seed.1 seed.2
  have hco := executed_accuracy (d := d) (m := m) (K := K) hd hm
    (g := G) (f := F) (σ := σ) (L := L) (μ := μ) (h := hband) (x0 := e x0) (xstar := e xstar)
    (hh := hhb) (hL := hL) (hμ := hμ) (hμL := hμL) (hg := hgmG) (hgi := hgiG) (hmean := hmeanG)
    (hvi := hgsqG) (hv := hvarG) (hc := hconvF) (hgr := hgrF) (hlip := hlipF) (hmin := hminF)
    (hpl := hplF) P hind hmarg
  have heq : result = fun seed : Unit × (ℕ → Ω) => e.symm (execCo seed) := by
    funext seed
    exact execute_ofPoint e.symm (g := g) (K := K * (2 * d * m)) seed.1 seed.2
  have hfun : (fun seed : Unit × (ℕ → Ω) => f (result seed) - f xstar)
      = (fun seed : Unit × (ℕ → Ω) => F (execCo seed) - F (e xstar)) := by
    funext seed
    rw [heq, hF, hF, e.symm_apply_apply]
  refine ⟨?_, ?_, ?_⟩
  · rw [heq]
    exact hcont.comp hco.1
  · rw [hfun]
    exact hco.2.1
  · rw [hfun]
    have h2 : F (e x0) - F (e xstar) ≤ L / 2 * R ^ 2 := by
      simp only [hF, e.symm_apply_apply]
      have h3 : ‖x0 - xstar‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hdist 2
      have h4 : f x0 - f xstar ≤ L / 2 * ‖x0 - xstar‖ ^ 2 := hgap x0
      have h5 : L / 2 * ‖x0 - xstar‖ ^ 2 ≤ L / 2 * R ^ 2 :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      exact le_trans h4 h5
    have hbnd : (∫ seed : Unit × (ℕ → Ω), F (execCo seed) - F (e xstar)
            ∂((Measure.dirac () : Measure Unit).prod (P : Measure (ℕ → Ω))))
        ≤ (1 - μ / L) ^ K * (F (e x0) - F (e xstar))
          + (K : ℝ) * (1 / L) * batchError d m σ L hband := by
      have h1 := hco.2.2
      have hc : (K : ℝ) * ((1 / L) * batchError d m σ L hband)
          = (K : ℝ) * (1 / L) * batchError d m σ L hband := (mul_assoc _ _ _).symm
      rw [hc] at h1
      exact h1
    calc (∫ seed : Unit × (ℕ → Ω), F (execCo seed) - F (e xstar)
            ∂((Measure.dirac () : Measure Unit).prod (P : Measure (ℕ → Ω))))
        ≤ (1 - μ / L) ^ K * (F (e x0) - F (e xstar))
          + (K : ℝ) * (1 / L) * batchError d m σ L hband := hbnd
      _ ≤ (1 - μ / L) ^ K * (L / 2 * R ^ 2)
          + (K : ℝ) * (1 / L)
              * batchError d m σ L (Real.sqrt (ε / (2 * (K : ℝ) * (d : ℝ) * L))) := by
          refine add_le_add
            (mul_le_mul_of_nonneg_left h2
              (pow_nonneg (by
                have : μ / L ≤ 1 := (div_le_one hL).mpr hμL
                linarith) K)) (le_refl _)
      _ ≤ ε := hbound

end OracleTemplate.SecantPolyak

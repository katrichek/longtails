import LongTails.Proofs.LineSearchTransfer
import LongTails.Proofs.GdConvex

namespace OracleTemplate.LineSearch

open MeasureTheory ProbabilityTheory Set
open _root_.OracleTemplate.Gradient
open scoped ENNReal

variable {Ω : Type} [MeasurableSpace Ω]

noncomputable def funConst (d : ℕ) (t : ℝ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun _ : Fin d => t)

lemma toReal_two : ENNReal.toReal (2 : ENNReal) = (2 : ℝ) := by
  rw [ENNReal.toReal_ofNat]

lemma abs_half (c : ℝ) : (c ^ 2 : ℝ) ^ (1 / ENNReal.toReal 2) = |c| := by
  rw [show (1 / ENNReal.toReal 2 : ℝ) = (1:ℝ) / 2 by rw [toReal_two],
    show (c ^ 2 : ℝ) = c * c by ring, ← Real.sqrt_eq_rpow, Real.sqrt_mul_self_eq_abs]

lemma norm_funConst_one (c : ℝ) : ‖(funConst 1 c : EuclideanSpace ℝ (Fin 1))‖ = |c| := by
  rw [PiLp.norm_eq_sum (by norm_num : (0:ℝ) < ENNReal.toReal 2)]
  have hsum : ∑ i : Fin 1, ‖(funConst 1 c).ofLp i‖ ^ ENNReal.toReal 2 = c ^ 2 := by
    have h1 : (fun i : Fin 1 => ‖(funConst 1 c).ofLp i‖ ^ ENNReal.toReal 2)
        = fun _ : Fin 1 => c ^ 2 := by
      funext i
      show |c| ^ ENNReal.toReal 2 = c ^ 2
      rw [toReal_two]
      simp
    rw [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    norm_num
  rw [hsum, abs_half]

def zeroFin {d : ℕ} (_hd : d = 1) : Fin d := ⟨0, by omega⟩

lemma funConst_apply (d : ℕ) (t : ℝ) (i : Fin d) : funConst d t i = t := rfl

lemma funConst_coord {d : ℕ} (hd : d = 1) (v : EuclideanSpace ℝ (Fin d)) :
    funConst d (v (zeroFin hd)) = v := by
  subst hd
  ext i
  cases i with
  | mk i hi =>
      have hz : i = 0 := by omega
      subst hz
      rfl

lemma norm_funConst {d : ℕ} (hd : d = 1) {a b : ℝ} : ‖funConst d a - funConst d b‖ = |a - b| := by
  subst hd
  have subc : funConst 1 a - funConst 1 b = funConst 1 (a - b) := by
    ext i
    rfl
  rw [subc, norm_funConst_one]

noncomputable def uOf {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
    (_hd : d = 1) (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) : ℝ → E :=
  fun t => e.symm (funConst d t)

noncomputable def psiOf {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
    (hd : d = 1) (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) : E → ℝ :=
  fun x => e x (zeroFin hd)

lemma uOf_psiOf {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ} (hd : d = 1)
    (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) (x : E) : uOf hd e (psiOf hd e x) = x := by
  show e.symm (funConst d (e x (zeroFin hd))) = x
  rw [funConst_coord hd (v := e x)]
  exact e.symm_apply_apply x

lemma psiOf_uOf {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ} (hd : d = 1)
    (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) (t : ℝ) : psiOf hd e (uOf hd e t) = t := by
  show (e (e.symm (funConst d t))) (zeroFin hd) = t
  rw [e.apply_symm_apply]
  exact funConst_apply d t (zeroFin hd)

lemma psiOf_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ} (hd : d = 1)
    (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) (x y : E) :
    |psiOf hd e x - psiOf hd e y| = ‖x - y‖ := by
  have key : funConst d (psiOf hd e x) - funConst d (psiOf hd e y) = e x - e y := by
    show funConst d (e x (zeroFin hd)) - funConst d (e y (zeroFin hd)) = e x - e y
    rw [funConst_coord hd (v := e x), funConst_coord hd (v := e y)]
  have h1 : ‖funConst d (psiOf hd e x) - funConst d (psiOf hd e y)‖
      = |psiOf hd e x - psiOf hd e y| := norm_funConst hd
  have hi : ‖e x - e y‖ = ‖x - y‖ := by
    rw [← map_sub (f := e), LinearIsometryEquiv.norm_map]
  rw [← h1, key, hi]

lemma continuous_funConst {d : ℕ} (hd : d = 1) : Continuous (fun t : ℝ => funConst d t) := by
  subst hd
  refine continuous_iff_continuousAt.mpr (fun t => ?_)
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨ε, hε, fun s hs => ?_⟩
  rw [dist_eq_norm]
  have key : (funConst 1 s : EuclideanSpace ℝ (Fin 1)) - funConst 1 t = funConst 1 (s - t) := by
    ext i
    rfl
  rw [key, norm_funConst_one]
  rwa [dist_eq_norm] at hs

lemma uOf_continuous {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
    (hd : d = 1) (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) : Continuous (uOf hd e) :=
  e.symm.continuous.comp (continuous_funConst hd)

lemma uOf_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ} (hd : d = 1)
    (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) (a b : ℝ) : ‖uOf hd e a - uOf hd e b‖ = |a - b| := by
  show ‖(e.symm (funConst d a) : E) - e.symm (funConst d b)‖ = |a - b|
  rw [← map_sub (f := e.symm), LinearIsometryEquiv.norm_map, norm_funConst hd]

lemma uOf_measurable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {d : ℕ} (hd : d = 1)
    (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) : Measurable (uOf hd e) :=
  (uOf_continuous hd e).measurable

lemma uOf_convex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ} (hd : d = 1)
    (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) {f : E → ℝ} (hc : ConvexOn ℝ univ f) :
    ConvexOn ℝ univ (fun t : ℝ => f (uOf hd e t)) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have key : uOf hd e (a • x + b • y) = a • uOf hd e x + b • uOf hd e y := by
    apply e.injective
    show e (e.symm (funConst d (a * x + b * y)))
      = e (a • e.symm (funConst d x) + b • e.symm (funConst d y))
    rw [e.apply_symm_apply, e.map_add, e.map_smul, e.map_smul, e.apply_symm_apply,
      e.apply_symm_apply]
    show funConst d (a * x + b * y) = a • funConst d x + b • funConst d y
    ext i
    rfl
  show f (uOf hd e (a • x + b • y)) ≤ a • f (uOf hd e x) + b • f (uOf hd e y)
  rw [key]
  exact hc.2 (mem_univ _) (mem_univ _) ha hb hab

/-- Transport the query and output spaces of a line algorithm along a map into `E`. -/
noncomputable def ofReal {E : Type} (u : ℝ → E) (A : Algorithm ℝ ℝ ℝ) : Algorithm E ℝ E where
  Seed := A.Seed
  law := A.law
  State := A.State
  initial := A.initial
  query s := (0, u ((A.query s).2))
  update s r := A.update s r
  output s := u (A.output s)

lemma execute_ofReal {E : Type} (u : ℝ → E) {A : Algorithm ℝ ℝ ℝ}
    {P : ProbabilityMeasure (ℕ → Ω)} (g : E → Ω → ℝ) (K : ℕ) (sd : A.Seed) (ξ : ℕ → Ω) :
    execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
        (ofReal u A) (fun _ => K) sd ξ
      = u (execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, t) ω => g (u t) ω }
          A (fun _ => K) sd ξ) := by
  have h1 := StochasticGradient.execute_advance (law := P) (g := fun x : E => g x)
    (A := ofReal u A) K sd ξ
  have h2 := StochasticGradient.execute_advance (law := P) (g := fun t : ℝ => g (u t)) (A := A) K sd ξ
  exact h1.trans (congrArg u h2.symm)

lemma line_search_expected_space {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] {d : ℕ} (hd : d = 1)
    {e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)} {f : E → ℝ} {L R σ ε : ℝ} {x0 xstar : E}
    (hconv : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hmin : IsMinOn f univ xstar) (hdist : ‖x0 - xstar‖ ≤ R)
    {g : E → Ω → ℝ} (hgm : Measurable (Function.uncurry g)) {p : ProbabilityMeasure Ω}
    {P : ProbabilityMeasure (ℕ → Ω)}
    (hind : iIndepFun (fun k (ξ : ℕ → Ω) => ξ k) (P : Measure (ℕ → Ω)))
    (hmarg : ∀ k, (P : Measure (ℕ → Ω)).map (fun ξ : ℕ → Ω => ξ k) = (p : Measure Ω))
    (hgi : ∀ x, Integrable (g x) (p : Measure Ω))
    (hmean : ∀ x, ∫ ω, g x ω ∂(p : Measure Ω) = f x)
    (hgsq : ∀ x, Integrable (fun ω => (g x ω - f x) ^ 2) (p : Measure Ω))
    (hvar : ∀ x, ∫ ω, (g x ω - f x) ^ 2 ∂(p : Measure Ω) ≤ σ ^ 2)
    (hL : 0 < L) (hR : 0 ≤ R) (hσ : 0 ≤ σ) {m J : ℕ} (hm : 0 < m) (hJ : 1 ≤ J)
    (hbound : L / 2 * (2 * R * ((2:ℝ) / 3) ^ (J - 1)) ^ 2
        + 3 * (2 * σ * Real.sqrt ((J : ℝ) / m)) ≤ ε) :
    Integrable (fun seed : Unit × (ℕ → Ω) =>
        f (execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
            (ofReal (uOf hd e) (lineSearch R (psiOf hd e x0) (by omega : 0 < 2 * m)))
              (fun _ => J * (2 * m)) seed.1 seed.2) - f xstar)
        ((Measure.dirac () : Measure Unit).prod (P : Measure (ℕ → Ω))) ∧
      (∫ seed : Unit × (ℕ → Ω),
          f (execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
              (ofReal (uOf hd e) (lineSearch R (psiOf hd e x0) (by omega : 0 < 2 * m)))
                (fun _ => J * (2 * m)) seed.1 seed.2) - f xstar
            ∂((Measure.dirac () : Measure Unit).prod (P : Measure (ℕ → Ω)))) ≤ ε := by
  have hzero : gradient f xstar = 0 := by
    apply (_root_.InnerProductSpace.toDual ℝ E).injective
    simpa using (hmin.isLocalMin Filter.univ_mem).hasFDerivAt_eq_zero (hg xstar).hasFDerivAt
  have hgap : ∀ y : E, f y - f xstar ≤ L / 2 * ‖y - xstar‖ ^ 2 := by
    intro y
    have h := smooth_upper_bound hg hlip xstar y
    rw [hzero, inner_zero_left, add_zero] at h
    exact sub_le_iff_le_add'.mpr h
  have hsm : ∀ t ∈ Icc (psiOf hd e x0 - R) (psiOf hd e x0 + R),
      (fun t : ℝ => f (uOf hd e t)) t - (fun t : ℝ => f (uOf hd e t)) (psiOf hd e xstar)
        ≤ L / 2 * (t - psiOf hd e xstar) ^ 2 := by
    intro t ht
    have h1 := hgap (uOf hd e t)
    have h3 : ‖uOf hd e t - xstar‖ = |t - psiOf hd e xstar| :=
      (congrArg (fun z : E => ‖uOf hd e t - z‖) ((uOf_psiOf hd e xstar).symm)).trans
        (uOf_norm hd e t (psiOf hd e xstar))
    rw [h3, sq_abs] at h1
    show f (uOf hd e t) - f (uOf hd e (psiOf hd e xstar)) ≤ L / 2 * (t - psiOf hd e xstar) ^ 2
    rw [uOf_psiOf hd e xstar]
    exact h1
  have hx : psiOf hd e xstar ∈ Icc (psiOf hd e x0 - R) (psiOf hd e x0 + R) := by
    have h1 : |psiOf hd e xstar - psiOf hd e x0| ≤ R := by
      rw [psiOf_norm, norm_sub_rev]
      exact hdist
    rcases abs_le.mp h1 with ⟨h1a, h1b⟩
    exact ⟨by linarith, by linarith⟩
  have hmin0 : IsMinOn (fun t : ℝ => f (uOf hd e t)) univ (psiOf hd e xstar) := by
    intro t _
    show f (uOf hd e (psiOf hd e xstar)) ≤ f (uOf hd e t)
    rw [uOf_psiOf hd e xstar]
    exact hmin (mem_univ _)
  have hf : Measurable f :=
    (continuous_iff_continuousAt.mpr (fun x => (hg x).continuousAt)).measurable
  have hfm : Measurable (fun t : ℝ => f (uOf hd e t)) := hf.comp (uOf_continuous hd e).measurable
  have hgm0 : Measurable (Function.uncurry (fun t : ℝ => fun ω => g (uOf hd e t) ω)) := by
    have h1 : Function.uncurry (fun t : ℝ => fun ω => g (uOf hd e t) ω)
        = fun p : ℝ × Ω => Function.uncurry g (uOf hd e p.1, p.2) := rfl
    rw [h1]
    exact hgm.comp ((uOf_measurable hd e).comp measurable_fst |>.prodMk measurable_snd)
  have hgi0 : ∀ t : ℝ, Integrable (fun ω => g (uOf hd e t) ω) (p : Measure Ω) :=
    fun t => hgi (uOf hd e t)
  have hmean0 : ∀ t : ℝ, ∫ ω, g (uOf hd e t) ω ∂(p : Measure Ω) = f (uOf hd e t) :=
    fun t => hmean (uOf hd e t)
  have hgsq0 : ∀ t : ℝ, Integrable (fun ω => (g (uOf hd e t) ω - f (uOf hd e t)) ^ 2)
      (p : Measure Ω) := fun t => hgsq (uOf hd e t)
  have hvar0 : ∀ t : ℝ, ∫ ω, (g (uOf hd e t) ω - f (uOf hd e t)) ^ 2 ∂(p : Measure Ω) ≤ σ ^ 2 :=
    fun t => hvar (uOf hd e t)
  have hres := lineSearch_expected (hn := by omega) (P := P) (R := R) (x0 := psiOf hd e x0)
    (g := fun t ω => g (uOf hd e t) ω) (f := fun t : ℝ => f (uOf hd e t))
    (xstar := psiOf hd e xstar) (L := L) (σ := σ) (ε := ε) hind hmarg hfm hgm0 hm hσ hmean0 hgi0
    hgsq0 hvar0 (uOf_convex hd e hconv) hmin0 hsm hL (by linarith) hx hJ hbound
  let A2 : Algorithm ℝ ℝ ℝ := lineSearch R (psiOf hd e x0) (by omega : 0 < 2 * m)
  let A1 : Algorithm E ℝ E := ofReal (uOf hd e) A2
  let OO : Oracle E ℝ := { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
  let OG : Oracle ℝ ℝ := { Seed := fun _ => Ω, law := P, answer := fun _ (_, t) ω => g (uOf hd e t) ω }
  let KK := J * (2 * m)
  have heq : (fun seed : Unit × (ℕ → Ω) => f (execute OO A1 KK seed.1 seed.2) - f xstar)
      = (fun seed : Unit × (ℕ → Ω) =>
          f (uOf hd e (execute OG A2 KK seed.1 seed.2)) - f (uOf hd e (psiOf hd e xstar))) := by
    funext seed
    have h1 : execute OO A1 KK seed.1 seed.2 = uOf hd e (execute OG A2 KK seed.1 seed.2) :=
      execute_ofReal (uOf hd e) (P := P) (g := g) (K := KK) (sd := seed.1) (ξ := seed.2)
    have h2 : f xstar = f (uOf hd e (psiOf hd e xstar)) :=
      congrArg f ((uOf_psiOf hd e xstar).symm)
    rw [h1, ← h2]
  refine ⟨(hres.1).congr (ae_of_all _ (fun seed => (congrFun heq seed).symm)), ?_⟩
  exact (integral_congr_ae (ae_of_all _ (fun seed => congrFun heq seed))).trans_le hres.2

end OracleTemplate.LineSearch

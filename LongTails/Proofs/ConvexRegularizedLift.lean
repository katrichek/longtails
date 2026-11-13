import LongTails.Proofs.Execution
import LongTails.Proofs.GdConvex
import LongTails.Proofs.CompositeProx
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.ProperSpace
import LongTails.Setups.ZerothOrderSmoothAndConvex

open MeasureTheory Set
open scoped RealInnerProductSpace
open OracleTemplate
open LongTails.Setups.ZerothOrderSmoothAndConvex

namespace LongTails.Proofs.ConvexRegularizedLift

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def reg (f : E → ℝ) (lam : ℝ) (c : E) : E → ℝ :=
  fun y => f y + lam / 2 * ‖y - c‖ ^ 2

omit [CompleteSpace E] in
lemma affine_convex (g : E →L[ℝ] ℝ) (k : ℝ) : ConvexOn ℝ Set.univ (fun y : E => g y + k) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have h2 : g (a • x + b • y) + k = a * (g x + k) + b * (g y + k) := by
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    calc a * g x + b * g y + k = a * g x + b * g y + (a + b) * k := by rw [hab]; ring
      _ = a * (g x + k) + b * (g y + k) := by ring
  simpa only [smul_eq_mul] using le_of_eq h2

omit [CompleteSpace E] in
lemma quadratic_strongConvex (lam : ℝ) (c : E) :
    StrongConvexOn Set.univ lam (fun y : E => lam / 2 * ‖y - c‖ ^ 2) := by
  rw [strongConvexOn_iff_convex]
  have hfun : (fun y : E => lam / 2 * ‖y - c‖ ^ 2 - lam / 2 * ‖y‖ ^ 2) =
      fun y : E => ⟪(-lam) • c, y⟫ + lam / 2 * ‖c‖ ^ 2 := by
    funext y
    rw [norm_sub_sq_real, real_inner_smul_left, real_inner_comm y c]
    ring
  rw [hfun]
  exact affine_convex (innerSL ℝ ((-lam) • c)) (lam / 2 * ‖c‖ ^ 2)

omit [CompleteSpace E] in
lemma quadratic_tangent (lam : ℝ) (c x y : E) :
    lam / 2 * ‖x - c‖ ^ 2 + ⟪lam • (x - c), y - x⟫ + lam / 2 * ‖y - x‖ ^ 2 =
      lam / 2 * ‖y - c‖ ^ 2 := by
  have h : y - c = (x - c) + (y - x) := by abel
  rw [h, norm_add_sq_real, real_inner_smul_left]
  ring

omit [CompleteSpace E] in
lemma norm_step_sq (v : E) (hv : ‖v‖ = 1) (t : ℝ) : ‖t • v‖ ^ 2 = t ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, mul_pow, hv, one_pow, mul_one, sq_abs]

lemma reg_hasGradient (f : E → ℝ) (lam : ℝ) (c : E) {x : E}
    (hg : HasGradientAt f (gradient f x) x) :
    HasGradientAt (reg f lam c) (gradient f x + lam • (x - c)) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert! hg.hasFDerivAt.add
    (((hasFDerivAt_id (x := x)).sub_const c).norm_sq.const_mul (lam / 2)) using 1
  ext v
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, InnerProductSpace.toDual_apply_apply, innerSL_apply_apply,
    id_eq, real_inner_smul_left, inner_add_left, smul_eq_mul]
  ring

lemma reg_gradient_eq (f : E → ℝ) (lam : ℝ) (c : E) {x : E}
    (hg : HasGradientAt f (gradient f x) x) :
    gradient (reg f lam c) x = gradient f x + lam • (x - c) :=
  (reg_hasGradient f lam c hg).gradient

lemma reg_lipschitz (f : E → ℝ) {lam L : ℝ} (c : E) (hlam : 0 ≤ lam)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) :
    ∀ x y, ‖gradient (reg f lam c) x - gradient (reg f lam c) y‖ ≤ (L + lam) * ‖x - y‖ := by
  intro x y
  rw [reg_gradient_eq f lam c (hg x), reg_gradient_eq f lam c (hg y)]
  have h1 : gradient f x + lam • (x - c) - (gradient f y + lam • (y - c)) =
      (gradient f x - gradient f y) + lam • (x - y) := by module
  rw [h1]
  have h2 : ‖lam • (x - y)‖ = lam * ‖x - y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam]
  calc ‖(gradient f x - gradient f y) + lam • (x - y)‖
      ≤ ‖gradient f x - gradient f y‖ + ‖lam • (x - y)‖ := norm_add_le _ _
    _ ≤ L * ‖x - y‖ + lam * ‖x - y‖ := by rw [h2]; linarith [hlip x y]
    _ = (L + lam) * ‖x - y‖ := by ring

omit [CompleteSpace E] in
lemma reg_strongConvex (f : E → ℝ) {lam : ℝ} (c : E) (hc : ConvexOn ℝ Set.univ f) :
    StrongConvexOn Set.univ lam (reg f lam c) := by
  have h := OracleTemplate.Composite.strong_add_convex hc (quadratic_strongConvex lam c)
  change StrongConvexOn Set.univ lam (fun x => f x + lam / 2 * ‖x - c‖ ^ 2)
  exact h

omit [CompleteSpace E] in
lemma reg_convex (f : E → ℝ) {lam : ℝ} (c : E) (hc : ConvexOn ℝ Set.univ f) (hlam : 0 ≤ lam) :
    ConvexOn ℝ Set.univ (reg f lam c) :=
  (reg_strongConvex f c hc).convexOn (fun r => by positivity)

lemma reg_tangent (f : E → ℝ) {lam : ℝ} (c : E) (hc : ConvexOn ℝ Set.univ f)
    (hg : ∀ x, HasGradientAt f (gradient f x) x) :
    ∀ x y, reg f lam c x + ⟪gradient (reg f lam c) x, y - x⟫ + lam / 2 * ‖y - x‖ ^ 2 ≤
      reg f lam c y := by
  intro x y
  have h1 := OracleTemplate.Gradient.convex_support hc hg x y
  have h2 := quadratic_tangent lam c x y
  rw [reg_gradient_eq f lam c (hg x), inner_add_left]
  simp only [reg]
  linarith

lemma gradient_minimizer_zero {f : E → ℝ} {L : ℝ} (hL : 0 < L)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    {u : E} (hm : IsMinOn f Set.univ u) : gradient f u = 0 := by
  have hd := OracleTemplate.Gradient.descent hL hg hlip u
  have hh := hm (show u - (1 / L) • gradient f u ∈ Set.univ from trivial)
  change f u ≤ f (u - (1 / L) • gradient f u) at hh
  have hsq : ‖gradient f u‖ ^ 2 / (2 * L) ≤ 0 := by linarith
  have hz := (div_le_iff₀ (by positivity : 0 < 2 * L)).mp hsq
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (gradient f u)])

lemma gap_f_le (f : E → ℝ) {L R : ℝ} {x0 u : E} (hL : 0 < L)
    (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hminu : IsMinOn f Set.univ u) (hdist : ‖x0 - u‖ ≤ R) :
    f x0 - f u ≤ L * R ^ 2 := by
  have hzero : gradient f u = 0 := gradient_minimizer_zero hL hg hlip hminu
  have h1 : f x0 - f u ≤ ⟪gradient f x0, x0 - u⟫ := by
    have hcs := OracleTemplate.Gradient.convex_support hc hg x0 u
    have hu : u - x0 = -(x0 - u) := by abel
    rw [hu, inner_neg_right] at hcs
    linarith
  have hnorm : ‖gradient f x0‖ ≤ L * ‖x0 - u‖ := by
    have hh := hlip x0 u
    rw [hzero, sub_zero] at hh
    exact hh
  have hR2 : ‖x0 - u‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg (x0 - u), hdist]
  calc f x0 - f u ≤ ⟪gradient f x0, x0 - u⟫ := h1
    _ ≤ ‖gradient f x0‖ * ‖x0 - u‖ := real_inner_le_norm _ _
    _ ≤ (L * ‖x0 - u‖) * ‖x0 - u‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
    _ = L * ‖x0 - u‖ ^ 2 := by ring
    _ ≤ L * R ^ 2 := mul_le_mul_of_nonneg_left hR2 hL.le

lemma reg_minimizer (f : E → ℝ) {lam L R : ℝ} {x0 u : E} {d : ℕ} (e : E ≃ₗᵢ[ℝ] Point d)
    (hL : 0 < L) (hlam : 0 < lam) (hc : ConvexOn ℝ Set.univ f)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hminu : IsMinOn f Set.univ u) (hdist : ‖x0 - u‖ ≤ R) :
    ∃ ystar : E, IsMinOn (reg f lam x0) Set.univ ystar ∧
      lam * ‖x0 - ystar‖ ^ 2 ≤ L * R ^ 2 := by
  let : FiniteDimensional ℝ E := by
    have : FiniteDimensional ℝ (Point d) := inferInstance
    exact e.toLinearEquiv.symm.finiteDimensional
  let : ProperSpace E := FiniteDimensional.proper ℝ E
  have hcont : Continuous (reg f lam x0) := by
    have hf : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hg x).continuousAt)
    have hq : Continuous (fun y : E => lam / 2 * ‖y - x0‖ ^ 2) := by fun_prop
    change Continuous (fun y : E => f y + lam / 2 * ‖y - x0‖ ^ 2)
    exact hf.add hq
  have hgx0 : gradient (reg f lam x0) x0 = gradient f x0 := by
    rw [reg_gradient_eq f lam x0 (hg x0)]
    simp
  set S : ℝ := 2 * ‖gradient f x0‖ / lam + 1 with hS
  have hS0 : 0 ≤ S := by positivity
  have hcompact : IsCompact (Metric.closedBall x0 S) := ProperSpace.isCompact_closedBall x0 S
  have hne : (Metric.closedBall x0 S).Nonempty :=
    ⟨x0, by rw [Metric.mem_closedBall]; simpa using hS0⟩
  obtain ⟨ystar, hmem, hminB⟩ := hcompact.exists_isMinOn hne hcont.continuousOn
  have hx0mem : x0 ∈ Metric.closedBall x0 S := by rw [Metric.mem_closedBall]; simpa using hS0
  have htan := reg_tangent (f := f) (lam := lam) (c := x0) hc hg
  have hglob : IsMinOn (reg f lam x0) Set.univ ystar := by
    intro z _
    by_cases hz : z ∈ Metric.closedBall x0 S
    · exact hminB hz
    · have hzS : 2 * ‖gradient f x0‖ ≤ lam * ‖z - x0‖ := by
        rw [Metric.mem_closedBall, not_le, dist_eq_norm] at hz
        have hS' : 2 * ‖gradient f x0‖ / lam ≤ ‖z - x0‖ := by
          rw [hS] at hz
          linarith [le_of_lt hz]
        rw [div_le_iff₀ hlam] at hS'
        linarith
      have ht := htan x0 z
      have hcs : -‖gradient f x0‖ * ‖z - x0‖ ≤ ⟪gradient (reg f lam x0) x0, z - x0⟫ := by
        rw [hgx0]
        have hb := real_inner_le_norm (-(gradient f x0)) (z - x0)
        rw [inner_neg_left, norm_neg] at hb
        linarith
      have hquad : 0 ≤ lam / 2 * ‖z - x0‖ ^ 2 - ‖gradient f x0‖ * ‖z - x0‖ := by
        have hmul : ‖gradient f x0‖ * ‖z - x0‖ ≤ (lam * ‖z - x0‖ / 2) * ‖z - x0‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg (z - x0))
          linarith [hzS]
        nlinarith [hmul]
      have hy0 : reg f lam x0 ystar ≤ reg f lam x0 x0 := hminB hx0mem
      have hlow : reg f lam x0 x0 ≤ reg f lam x0 z := by linarith
      exact le_trans hy0 hlow
  refine ⟨ystar, hglob, ?_⟩
  have hregx0 : reg f lam x0 x0 = f x0 := by simp [reg]
  have hbound := OracleTemplate.Composite.strong_minimum_bound (reg_strongConvex f x0 hc) hglob x0
  rw [hregx0] at hbound
  have hlower : f u + lam / 2 * ‖x0 - ystar‖ ^ 2 ≤ reg f lam x0 ystar := by
    have h1 : f u ≤ f ystar := hminu (Set.mem_univ ystar)
    have h2 : ‖ystar - x0‖ = ‖x0 - ystar‖ := norm_sub_rev _ _
    simp only [reg, h2]
    linarith
  have hgap := gap_f_le f hL hc hg hlip hminu hdist
  linarith

/-- The four-point stencil bias hypothesis of the calling setup, in general form. -/
def QuinticBias (rho4 : ℝ) (f : E → ℝ) : Prop :=
  ∀ (x v : E) (h : ℝ), 0 < h → ‖v‖ = 1 →
    |(-f (x + (2 * h) • v) + 8 * f (x + h • v) - 8 * f (x - h • v) +
        f (x - (2 * h) • v)) / (12 * h) - ⟪gradient f x, v⟫| ≤ rho4 * h ^ 4

omit [CompleteSpace E] in
lemma quadratic_stencil (lam h : ℝ) (c x v : E) (hh : h ≠ 0) (hv : ‖v‖ = 1) :
    (-(lam / 2 * ‖x + (2 * h) • v - c‖ ^ 2) + 8 * (lam / 2 * ‖x + h • v - c‖ ^ 2)
        - 8 * (lam / 2 * ‖x - h • v - c‖ ^ 2) + lam / 2 * ‖x - (2 * h) • v - c‖ ^ 2) /
        (12 * h) = ⟪lam • (x - c), v⟫ := by
  set w : E := x - c with hw
  have e : ∀ t : ℝ, ‖w + t • v‖ ^ 2 = ‖w‖ ^ 2 + 2 * t * ⟪w, v⟫ + t ^ 2 := by
    intro t
    rw [norm_add_sq_real, real_inner_smul_right, norm_step_sq v hv t]
    ring
  have f1 : x + (2 * h) • v - c = w + (2 * h) • v := by rw [hw]; module
  have f2 : x + h • v - c = w + h • v := by rw [hw]; module
  have f3 : x - h • v - c = w + (-h) • v := by rw [hw]; module
  have f4 : x - (2 * h) • v - c = w + (-(2 * h)) • v := by rw [hw]; module
  have hvw : ⟪x - c, v⟫ = ⟪w, v⟫ := by rw [hw]
  rw [f1, f2, f3, f4, e (2 * h), e h, e (-h), e (-(2 * h)), real_inner_smul_left, hvw]
  field_simp
  ring

lemma quinticBias_reg {rho4 lam : ℝ} {f : E → ℝ} (hb : QuinticBias (E := E) rho4 f) (c : E)
    (hg : ∀ x, HasGradientAt f (gradient f x) x) :
    QuinticBias (E := E) rho4 (reg f lam c) := by
  intro x v h hh hv
  have hgrade : ⟪gradient (reg f lam c) x, v⟫ =
      ⟪gradient f x, v⟫ + ⟪lam • (x - c), v⟫ := by
    rw [reg_gradient_eq f lam c (hg x), inner_add_left]
  have hquad := quadratic_stencil lam h c x v hh.ne' hv
  have hsplit :
      (-(reg f lam c (x + (2 * h) • v)) + 8 * reg f lam c (x + h • v)
          - 8 * reg f lam c (x - h • v) + reg f lam c (x - (2 * h) • v)) / (12 * h) =
        (-f (x + (2 * h) • v) + 8 * f (x + h • v) - 8 * f (x - h • v) +
            f (x - (2 * h) • v)) / (12 * h) +
          (-(lam / 2 * ‖x + (2 * h) • v - c‖ ^ 2) + 8 * (lam / 2 * ‖x + h • v - c‖ ^ 2)
              - 8 * (lam / 2 * ‖x - h • v - c‖ ^ 2) +
              lam / 2 * ‖x - (2 * h) • v - c‖ ^ 2) / (12 * h) := by
    simp only [reg]
    field_simp
    ring
  have hb' := hb x v h hh hv
  rw [hgrade, hsplit, hquad] at *
  rw [abs_le] at hb' ⊢
  constructor <;> linarith [hb'.1, hb'.2]

/-- An oracle whose replies are the noisy values `g x ω` of the queried point `x`. -/
def mkOracle {Query : Type*} {Ω : Type} [MeasurableSpace Ω] (P : ProbabilityMeasure (ℕ → Ω))
    (G : Query → Ω → ℝ) : Oracle Query ℝ 1 where
  Seed := fun _ => Ω
  law := P
  answer := fun _ query ω => G query.2 ω

/-- Shift all replies of an algorithm by a function of the query point. -/
def shiftAlg {Query Output : Type*} {n : ℕ}
    (A : Algorithm Query ℝ Output n) (s : Query → ℝ) : Algorithm Query ℝ Output n where
  Seed := A.Seed
  seedSpace := A.seedSpace
  law := A.law
  State := A.State
  initial := A.initial
  query := A.query
  update := fun st r => A.update st (r + s (A.query st).2)
  output := A.output

lemma execute_shiftAlg {Query Output : Type*} {Ω : Type} [MeasurableSpace Ω]
    (P : ProbabilityMeasure (ℕ → Ω)) (G : Query → Ω → ℝ) (s : Query → ℝ)
    (A : Algorithm Query ℝ Output 1) (K : ℕ) (seed : A.Seed) (ξ : ℕ → Ω) :
    execute (mkOracle (Query := Query) P G) (shiftAlg A s) (fun _ => K) seed ξ =
      execute (mkOracle (Query := Query) P (fun x ω => G x ω + s x)) A (fun _ => K) seed ξ := by
  have h1 : ∀ history query, (mkOracle (Query := Query) P G).answer history query
      (ξ history.length) = (fun k (q : Fin 1 × Query) => G q.2 (ξ k)) history.length query :=
    fun _ _ => rfl
  have h2 : ∀ history query,
      (mkOracle (Query := Query) P (fun x ω => G x ω + s x)).answer history query
        (ξ history.length) =
        (fun k (q : Fin 1 × Query) => G q.2 (ξ k) + s q.2) history.length query :=
    fun _ _ => rfl
  rw [execute_indexed_of_answer (mkOracle (Query := Query) P G) (shiftAlg A s) K seed ξ
      (response := fun k q => G q.2 (ξ k)) h1,
    execute_indexed_of_answer (mkOracle (Query := Query) P (fun x ω => G x ω + s x)) A K seed ξ
      (response := fun k q => G q.2 (ξ k) + s q.2) h2]
  rfl


omit [CompleteSpace E] [InnerProductSpace ℝ E] [NormedAddCommGroup E] in
/-- Integrability transfers from a `c`-shifted comparison function. -/
lemma integrable_of_shift {Ω' : Type*} [MeasurableSpace Ω'] {μ : Measure Ω'} [IsFiniteMeasure μ]
    {ψ φ : E → ℝ}
    {out : Ω' → E} {w u : E} {c : ℝ} (hint : Integrable (fun s => φ (out s) - φ w) μ)
    (hmeas : AEStronglyMeasurable (fun s => ψ (out s) - ψ u) μ)
    (hnonneg : ∀ z, 0 ≤ ψ z - ψ u) (hle : ∀ z, ψ z - ψ u ≤ (φ z - φ w) + c) :
    Integrable (fun s => ψ (out s) - ψ u) μ :=
  (hint.add (integrable_const c)).mono_nonneg hmeas
    (Filter.Eventually.of_forall fun s => hnonneg (out s))
    (Filter.Eventually.of_forall fun s => hle (out s))

omit [CompleteSpace E] [InnerProductSpace ℝ E] [NormedAddCommGroup E] in
/-- Integral transfer along a pointwise `c`-shifted comparison. -/
lemma integral_le_of_shift {Ω' : Type*} [MeasurableSpace Ω'] {μ : Measure Ω'}
    [IsProbabilityMeasure μ] [IsFiniteMeasure μ] {ψ φ : E → ℝ} {out : Ω' → E} {w u : E} {c : ℝ}
    (hint : Integrable (fun s => φ (out s) - φ w) μ)
    (hintψ : Integrable (fun s => ψ (out s) - ψ u) μ)
    (hle : ∀ z, ψ z - ψ u ≤ (φ z - φ w) + c) :
    (∫ s, ψ (out s) - ψ u ∂μ) ≤ (∫ s, φ (out s) - φ w ∂μ) + c := by
  have h1 := integral_mono hintψ (hint.add (integrable_const c))
    (fun s => hle (out s))
  simp only [Pi.add_apply] at h1
  have h2 : (∫ s, (φ (out s) - φ w) + c ∂μ) = (∫ s, φ (out s) - φ w ∂μ) + c := by
    rw [integral_add hint (integrable_const c), integral_const, probReal_univ, one_smul]
  linarith [h1, h2]


/-- The shift commutation in the shape of the value oracle of the convex setup. -/
lemma execute_shiftAlg' {Q Out : Type*} {Ω : Type} [MeasurableSpace Ω]
    (P : ProbabilityMeasure (ℕ → Ω)) (g : Q → Ω → ℝ) (s : Q → ℝ)
    (A : Algorithm Q ℝ Out 1) (K : ℕ) (seed : A.Seed) (ξ : ℕ → Ω) :
    execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω } (shiftAlg A s)
        (fun _ => K) seed ξ =
      execute (mkOracle P (fun x ω => g x ω + s x)) A (fun _ => K) seed ξ :=
  execute_shiftAlg P g s A K seed ξ


omit [CompleteSpace E] [InnerProductSpace ℝ E] [NormedAddCommGroup E] in
variable [MeasurableSpace E] in
/-- Transfer of the accuracy statement from the regularized objective `φ` back to the convex
objective `f`: the cost of undoing the quadratic shift is the constant `c`. -/
lemma successful_transfer {Ω' : Type} [MeasurableSpace Ω'] (P : ProbabilityMeasure Ω')
    {f φ : E → ℝ} {outS outR : Ω' → E} {u w : E} {ε c : ℝ}
    (hout : outS = outR) (hmeas : Measurable outR)
    (hint : Integrable (fun s => φ (outR s) - φ w) (P : Measure Ω'))
    (hintle : (∫ s, φ (outR s) - φ w ∂(P : Measure Ω')) ≤ ε - c)
    (hminf : IsMinOn f Set.univ u) (hfm : Measurable f)
    (hpt : ∀ z, f z - f u ≤ (φ z - φ w) + c) :
    Measurable outS ∧ ∃ xstar : E, IsMinOn f Set.univ xstar ∧
      Integrable (fun s => f (outS s) - f xstar) (P : Measure Ω') ∧
      (∫ s, f (outS s) - f xstar ∂(P : Measure Ω')) ≤ ε := by
  have hmeasS : Measurable outS := hout ▸ hmeas
  have hintS : Integrable (fun s => φ (outS s) - φ w) (P : Measure Ω') := hout ▸ hint
  have hintleS : (∫ s, φ (outS s) - φ w ∂(P : Measure Ω')) ≤ ε - c := hout ▸ hintle
  have hintf := integrable_of_shift (φ := φ) (ψ := f) (w := w) (u := u) (c := c) (out := outS)
    hintS ((hfm.comp hmeasS).sub_const _).aestronglyMeasurable
    (fun z => sub_nonneg.mpr (hminf (Set.mem_univ z))) hpt
  have hile := integral_le_of_shift (φ := φ) (ψ := f) (w := w) (u := u) (c := c) (out := outS)
    hintS hintf hpt
  exact ⟨hmeasS, u, hminf, hintf, by linarith⟩

end LongTails.Proofs.ConvexRegularizedLift



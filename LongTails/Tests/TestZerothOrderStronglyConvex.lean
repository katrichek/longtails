import LongTails.Theorems.ZerothOrderStronglyConvex
import Mathlib.Tactic

namespace LongTails.Tests.ZerothOrderStronglyConvex

open MeasureTheory Set OracleTemplate ProbabilityTheory
open scoped RealInnerProductSpace
open LongTails.Setups.ZerothOrderSmoothAndConvex

abbrev Q := Point 2

noncomputable def fEx : Q → ℝ := fun x => ‖x‖ ^ 2

lemma hasGradSumEx (x : Q) : HasGradientAt fEx (x + x) x := by
  have h : HasFDerivAt (fun y : Q => ‖y‖ ^ 2) (2 • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  simp only [two_smul] at h
  have h2 : InnerProductSpace.toDual ℝ Q (x + x) = innerSL ℝ x + innerSL ℝ x := by
    show (innerSL ℝ) (x + x) = innerSL ℝ x + innerSL ℝ x
    rw [map_add]
  rw [hasGradientAt_iff_hasFDerivAt, h2]
  exact h

lemma gradEx (x : Q) : gradient fEx x = x + x := (hasGradSumEx x).gradient

lemma hasGradEx (x : Q) : HasGradientAt fEx (gradient fEx x) x := by
  rw [gradEx]
  exact hasGradSumEx x

lemma smoothEx : ∀ x y, ‖gradient fEx x - gradient fEx y‖ ≤ 2 * ‖x - y‖ := by
  intro x y
  rw [gradEx, gradEx]
  have hid : (x + x) - (y + y) = (2 : ℝ) • (x - y) := by
    rw [← two_smul ℝ x, ← two_smul ℝ y, smul_sub]
  rw [hid, norm_smul]
  have hnorm : ‖(2 : ℝ)‖ = (2 : ℝ) := by norm_num
  rw [hnorm]

lemma tangentEx : LongTails.Setups.ZerothOrderStronglyConvex.tangentStrong 2 fEx := by
  intro x y
  have h : ‖y‖ ^ 2 = ‖x‖ ^ 2 + (2 * ⟪x, y - x⟫ + ‖y - x‖ ^ 2) := by
    have h1 : ‖x + (y - x)‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪x, y - x⟫ + ‖y - x‖ ^ 2 :=
      norm_add_sq_real x (y - x)
    rw [show x + (y - x) = y by abel] at h1
    rw [h1]
    ring
  show fEx x + ⟪gradient fEx x, y - x⟫ + 2 / 2 * ‖y - x‖ ^ 2 ≤ fEx y
  simp only [fEx, gradEx, inner_add_left]
  norm_num
  linarith [h]

lemma minEx : IsMinOn fEx univ 0 := by
  intro x _
  show fEx 0 ≤ fEx x
  simp only [fEx]
  norm_num

lemma convexEx : ConvexOn ℝ univ fEx := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hn : ‖a • x + b • y‖ ≤ a * ‖x‖ + b * ‖y‖ := by
    calc ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
      _ = a * ‖x‖ + b * ‖y‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg ha, abs_of_nonneg hb]
  have key : (a * ‖x‖ + b * ‖y‖) ^ 2 ≤ a * ‖x‖ ^ 2 + b * ‖y‖ ^ 2 := by
    have h1 : b = 1 - a := by linarith
    rw [h1]
    have hident : a * ‖x‖ ^ 2 + (1 - a) * ‖y‖ ^ 2 - (a * ‖x‖ + (1 - a) * ‖y‖) ^ 2
        = a * (1 - a) * (‖x‖ - ‖y‖) ^ 2 := by ring
    have h2 : 0 ≤ a * (1 - a) := by nlinarith
    have h3 : 0 ≤ (‖x‖ - ‖y‖) ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg h2 h3, hident]
  have hf : fEx (a • x + b • y) = ‖a • x + b • y‖ ^ 2 := rfl
  have hx : fEx x = ‖x‖ ^ 2 := rfl
  have hy : fEx y = ‖y‖ ^ 2 := rfl
  rw [hf, hx, hy]
  calc ‖a • x + b • y‖ ^ 2 ≤ (a * ‖x‖ + b * ‖y‖) ^ 2 := by gcongr
    _ ≤ a * ‖x‖ ^ 2 + b * ‖y‖ ^ 2 := key

noncomputable def lawSample : ProbabilityMeasure Unit := ⟨Measure.dirac (), inferInstance⟩

noncomputable def lawStream : ProbabilityMeasure (ℕ → Unit) :=
  ⟨Measure.infinitePi fun _ : ℕ => (Measure.dirac () : Measure Unit), inferInstance⟩

noncomputable def gEx : Q → Unit → ℝ := fun x _ => fEx x

noncomputable def oracleEx : Oracle Q ℝ where
  Seed := fun _ => Unit
  law := lawStream
  answer := fun _ (_, x) ω => gEx x ω

noncomputable abbrev qEx : LongTails.Setups.ZerothOrderStronglyConvex.Params where
  E := Q
  Ω := Unit
  normedE := inferInstance
  linearE := inferInstance
  completeE := inferInstance
  measurableE := inferInstance
  borelE := inferInstance
  measurableΩ := inferInstance
  d := 2
  L := 2
  R := 1
  σ := 0
  μ := 2
  ε := 1 / 4
  x0 := 0

lemma marginalsEx (k : ℕ) :
    ((lawStream : Measure (ℕ → Unit)).map (fun ξ : ℕ → Unit => ξ k) : Measure Unit) =
      (lawSample : Measure Unit) := by
  simp [lawStream, lawSample, Measure.infinitePi_dirac, Measure.map_dirac]

lemma distEx : ‖(qEx.x0 : qEx.E) - (0 : qEx.E)‖ ≤ qEx.R := by
  have hz : ‖(qEx.x0 : qEx.E) - 0‖ = (0 : ℝ) := by
    rw [sub_zero]
    exact norm_zero
  rw [hz]
  norm_num

lemma baseShapeEx : LongTails.Setups.ZerothOrderPolyakConvex.baseShape qEx fEx oracleEx := by
  refine ⟨⟨LinearIsometryEquiv.refl ℝ Q⟩, gEx, lawSample, lawStream, ?_, ?_, rfl, convexEx, ?_,
    smoothEx, ⟨0, minEx, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · show ProbabilityTheory.iIndepFun (fun (k : ℕ) (ω : ℕ → Unit) => ω k)
      (Measure.infinitePi fun _ : ℕ => (Measure.dirac () : Measure Unit))
    exact iIndepFun_infinitePi (P := fun _ : ℕ => (Measure.dirac () : Measure Unit))
      (X := fun _ => id) (fun _ => measurable_id)
  · intro k; exact marginalsEx k
  · intro x; exact hasGradEx x
  · exact distEx
  · show Measurable (fun p : Q × Unit => ‖p.1‖ ^ 2)
    exact ((continuous_norm.pow (2 : ℕ)).measurable).comp measurable_fst
  · intro x
    show Integrable (fun _ : Unit => fEx x) (Measure.dirac ())
    exact integrable_dirac (by simp)
  · intro x
    show ∫ _ : Unit, fEx x ∂Measure.dirac () = fEx x
    simp
  · intro x
    show Integrable (fun _ : Unit => (fEx x - fEx x : ℝ) ^ 2) (lawSample : Measure Unit)
    exact integrable_dirac (by simp)
  · intro x
    show ∫ _ : Unit, (fEx x - fEx x : ℝ) ^ 2 ∂lawSample ≤ (0 : ℝ) ^ 2
    simp

lemma validEx : LongTails.Setups.ZerothOrderStronglyConvex.spec.valid qEx := by
  refine ⟨by decide, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num

lemma admEx : LongTails.Setups.ZerothOrderStronglyConvex.spec.admissible qEx fEx oracleEx := by
  refine ⟨baseShapeEx, 0, ?_, ?_, ?_⟩
  · exact minEx
  · exact distEx
  · exact tangentEx

theorem nonvacuous :
    ∃ (q : LongTails.Setups.ZerothOrderStronglyConvex.Params) (f : q.E → ℝ)
      (O : Oracle q.E ℝ),
      LongTails.Setups.ZerothOrderStronglyConvex.spec.valid q ∧
        LongTails.Setups.ZerothOrderStronglyConvex.spec.admissible q f O :=
  ⟨qEx, fEx, oracleEx, validEx, admEx⟩

theorem conclusionInhabited :
    ∃ (q : LongTails.Setups.ZerothOrderStronglyConvex.Params) (f : q.E → ℝ)
      (O : Oracle q.E ℝ) (Ω : Type) (m : MeasurableSpace Ω) (output : Ω → q.E)
      (P : ProbabilityMeasure Ω),
      LongTails.Setups.ZerothOrderStronglyConvex.spec.valid q ∧
        LongTails.Setups.ZerothOrderStronglyConvex.spec.admissible q f O ∧
        @LongTails.Setups.ZerothOrderStronglyConvex.spec.successful Ω m q f output P := by
  obtain ⟨A, hacc, _⟩ := LongTails.Theorems.ZerothOrderStronglyConvex.result
  have h := hacc qEx validEx fEx oracleEx admEx
  exact ⟨qEx, fEx, oracleEx, _, _, _, _, ⟨validEx, admEx, h⟩⟩

end LongTails.Tests.ZerothOrderStronglyConvex

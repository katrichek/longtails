import LongTails.Theorems.LineSearchZerothOrderConvex
import LongTails.Theorems.ZerothOrderStronglyConvex
import Mathlib.Tactic

namespace LongTails.Tests.ZerothOrderInstances

open MeasureTheory Set OracleTemplate ProbabilityTheory
open scoped RealInnerProductSpace
open LongTails.Setups.ZerothOrderSmoothAndConvex

noncomputable def normSq (n : ℕ) : Point n → ℝ := fun x => ‖x‖ ^ 2

lemma normSqHasGradSum (n : ℕ) (x : Point n) : HasGradientAt (normSq n) (x + x) x := by
  have h : HasFDerivAt (fun y : Point n => ‖y‖ ^ 2) (2 • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  simp only [two_smul] at h ⊢
  have h2 : InnerProductSpace.toDual ℝ (Point n) (x + x) = innerSL ℝ x + innerSL ℝ x := by
    show (innerSL ℝ) (x + x) = innerSL ℝ x + innerSL ℝ x
    rw [map_add]
  rw [hasGradientAt_iff_hasFDerivAt, h2]
  exact h

lemma normSqGradient (n : ℕ) (x : Point n) : gradient (normSq n) x = x + x :=
  (normSqHasGradSum n x).gradient

lemma normSqHasGradient (n : ℕ) (x : Point n) :
    HasGradientAt (normSq n) (gradient (normSq n) x) x := by
  rw [normSqGradient]
  exact normSqHasGradSum n x

lemma normSqSmooth (n : ℕ) :
    ∀ x y, ‖gradient (normSq n) x - gradient (normSq n) y‖ ≤ 2 * ‖x - y‖ := by
  intro x y
  rw [normSqGradient, normSqGradient]
  have hid : (x + x) - (y + y) = (2 : ℝ) • (x - y) := by
    rw [← two_smul ℝ x, ← two_smul ℝ y, smul_sub]
  rw [hid, norm_smul]
  have hnorm : ‖(2 : ℝ)‖ = (2 : ℝ) := by norm_num
  rw [hnorm]

lemma normSqTangent (n : ℕ) :
    LongTails.Setups.ZerothOrderStronglyConvex.tangentStrong 2 (normSq n) := by
  intro x y
  have h : ‖y‖ ^ 2 = ‖x‖ ^ 2 + (2 * ⟪x, y - x⟫ + ‖y - x‖ ^ 2) := by
    have h1 : ‖x + (y - x)‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪x, y - x⟫ + ‖y - x‖ ^ 2 :=
      norm_add_sq_real x (y - x)
    rw [show x + (y - x) = y by abel] at h1
    rw [h1]
    ring
  show normSq n x + ⟪gradient (normSq n) x, y - x⟫ + 2 / 2 * ‖y - x‖ ^ 2 ≤ normSq n y
  simp only [normSq, normSqGradient, inner_add_left]
  norm_num
  linarith [h]

lemma normSqMin (n : ℕ) : IsMinOn (normSq n) univ 0 := by
  intro x _
  show normSq n 0 ≤ normSq n x
  simp only [normSq]
  norm_num

lemma normSqConvex (n : ℕ) : ConvexOn ℝ univ (normSq n) := by
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
  have hf : normSq n (a • x + b • y) = ‖a • x + b • y‖ ^ 2 := rfl
  have hx : normSq n x = ‖x‖ ^ 2 := rfl
  have hy : normSq n y = ‖y‖ ^ 2 := rfl
  rw [hf, hx, hy]
  calc ‖a • x + b • y‖ ^ 2 ≤ (a * ‖x‖ + b * ‖y‖) ^ 2 := by gcongr
    _ ≤ a * ‖x‖ ^ 2 + b * ‖y‖ ^ 2 := key

noncomputable def lawSample : ProbabilityMeasure Unit := ⟨Measure.dirac (), inferInstance⟩

noncomputable def lawStream : ProbabilityMeasure (ℕ → Unit) :=
  ⟨Measure.infinitePi fun _ : ℕ => (Measure.dirac () : Measure Unit), inferInstance⟩

noncomputable def gSample (n : ℕ) : Point n → Unit → ℝ := fun x _ => normSq n x

noncomputable def oracleOf (n : ℕ) : Oracle (Point n) ℝ where
  Seed := fun _ => Unit
  law := lawStream
  answer := fun _ (_, x) ω => gSample n x ω

lemma marginalsSample (k : ℕ) :
    ((lawStream : Measure (ℕ → Unit)).map (fun ξ : ℕ → Unit => ξ k) : Measure Unit) =
      (lawSample : Measure Unit) := by
  simp [lawStream, lawSample, Measure.infinitePi_dirac, Measure.map_dirac]

lemma lawMeasurable (n : ℕ) : Measurable (fun p : Point n × Unit => ‖p.1‖ ^ 2) :=
  ((continuous_norm.pow (2 : ℕ)).measurable).comp measurable_fst

lemma lawIntegrable (n : ℕ) (x : Point n) :
    Integrable (fun _ : Unit => ‖x‖ ^ 2) (Measure.dirac ()) := integrable_dirac (by simp)

lemma lawMean (n : ℕ) (x : Point n) : ∫ _ : Unit, ‖x‖ ^ 2 ∂Measure.dirac () = ‖x‖ ^ 2 := by simp

lemma lawSquare (n : ℕ) (x : Point n) :
    Integrable (fun _ : Unit => (‖x‖ ^ 2 - ‖x‖ ^ 2 : ℝ) ^ 2) (lawSample : Measure Unit) := by
  show Integrable (fun _ : Unit => (‖x‖ ^ 2 - ‖x‖ ^ 2 : ℝ) ^ 2) (Measure.dirac ())
  exact integrable_dirac (by simp)

lemma lawVariance (n : ℕ) (x : Point n) :
    ∫ _ : Unit, (‖x‖ ^ 2 - ‖x‖ ^ 2 : ℝ) ^ 2 ∂lawSample ≤ (0 : ℝ) ^ 2 := by simp

noncomputable abbrev qTwo : LongTails.Setups.ZerothOrderStronglyConvex.Params where
  E := Point 2
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

noncomputable abbrev qOne : Params where
  E := Point 1
  Ω := Unit
  normedE := inferInstance
  linearE := inferInstance
  completeE := inferInstance
  measurableE := inferInstance
  borelE := inferInstance
  measurableΩ := inferInstance
  d := 1
  L := 2
  R := 1
  σ := 0
  ε := 1 / 4
  x0 := 0

lemma distZeroPoint {E : Type} [NormedAddCommGroup E] {x0 : E} (hx0 : x0 = 0) {R : ℝ}
    (hR : (1 : ℝ) ≤ R) : ‖(x0 : E) - 0‖ ≤ R := by
  have hz : ‖(x0 : E) - 0‖ = (0 : ℝ) := by
    rw [hx0, sub_zero]
    exact norm_zero
  rw [hz]
  linarith

lemma baseShapeOne : LongTails.Setups.ZerothOrderPolyakConvex.baseShape qTwo (normSq 2)
    (oracleOf 2) := by
  refine ⟨⟨LinearIsometryEquiv.refl ℝ (Point 2)⟩, gSample 2, lawSample, lawStream, ?_, ?_, rfl,
    normSqConvex 2, ?_, normSqSmooth 2, ⟨0, normSqMin 2, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · show ProbabilityTheory.iIndepFun (fun (k : ℕ) (ω : ℕ → Unit) => ω k)
      (Measure.infinitePi fun _ : ℕ => (Measure.dirac () : Measure Unit))
    exact iIndepFun_infinitePi (P := fun _ : ℕ => (Measure.dirac () : Measure Unit))
      (X := fun _ => id) (fun _ => measurable_id)
  · intro k; exact marginalsSample k
  · intro x; exact normSqHasGradient 2 x
  · exact distZeroPoint rfl (by norm_num)
  · exact lawMeasurable 2
  · intro x; exact lawIntegrable 2 x
  · intro x; exact lawMean 2 x
  · intro x; exact lawSquare 2 x
  · intro x; exact lawVariance 2 x

lemma baseShapeSmooth : spec.admissible qOne (normSq 1) (oracleOf 1) := by
  refine ⟨⟨LinearIsometryEquiv.refl ℝ (Point 1)⟩, gSample 1, lawSample, lawStream, ?_, ?_, rfl,
    normSqConvex 1, ?_, normSqSmooth 1, ⟨0, normSqMin 1, ?_⟩, lawMeasurable 1, ?_, ?_, ?_, ?_⟩
  · show ProbabilityTheory.iIndepFun (fun (k : ℕ) (ω : ℕ → Unit) => ω k)
      (Measure.infinitePi fun _ : ℕ => (Measure.dirac () : Measure Unit))
    exact iIndepFun_infinitePi (P := fun _ : ℕ => (Measure.dirac () : Measure Unit))
      (X := fun _ => id) (fun _ => measurable_id)
  · intro k; exact marginalsSample k
  · intro x; exact normSqHasGradient 1 x
  · exact distZeroPoint rfl (by norm_num)
  · intro x; exact lawIntegrable 1 x
  · intro x; exact lawMean 1 x
  · intro x; exact lawSquare 1 x
  · intro x; exact lawVariance 1 x

lemma validTwo : LongTails.Setups.ZerothOrderStronglyConvex.spec.valid qTwo := by
  refine ⟨by decide, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num

lemma validOne : spec.valid qOne := by
  refine ⟨by decide, by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num

lemma admTwo :
    LongTails.Setups.ZerothOrderStronglyConvex.spec.admissible qTwo (normSq 2) (oracleOf 2) := by
  refine ⟨baseShapeOne, 0, ?_, ?_, ?_⟩
  · exact normSqMin 2
  · exact distZeroPoint rfl (by norm_num)
  · exact normSqTangent 2

noncomputable abbrev qLine : LongTails.Setups.ZerothOrderLineConvex.Params :=
  ⟨qOne, rfl⟩

lemma validLine : LongTails.Setups.ZerothOrderLineConvex.spec.valid qLine := validOne

lemma admLine :
    LongTails.Setups.ZerothOrderLineConvex.spec.admissible qLine (normSq 1) (oracleOf 1) :=
  baseShapeSmooth

theorem lineSetupNonvacuous :
    ∃ (q : LongTails.Setups.ZerothOrderLineConvex.Params) (f : q.val.E → ℝ)
      (O : Oracle q.val.E ℝ),
      LongTails.Setups.ZerothOrderLineConvex.spec.valid q ∧
        LongTails.Setups.ZerothOrderLineConvex.spec.admissible q f O :=
  ⟨qLine, normSq 1, oracleOf 1, validLine, admLine⟩

theorem lineConclusionInhabited :
    ∃ (q : LongTails.Setups.ZerothOrderLineConvex.Params) (f : q.val.E → ℝ)
      (O : Oracle q.val.E ℝ) (Ω : Type) (m : MeasurableSpace Ω) (output : Ω → q.val.E)
      (P : ProbabilityMeasure Ω),
      LongTails.Setups.ZerothOrderLineConvex.spec.valid q ∧
        LongTails.Setups.ZerothOrderLineConvex.spec.admissible q f O ∧
        @LongTails.Setups.ZerothOrderLineConvex.spec.successful Ω m q f output P := by
  obtain ⟨A, hacc, _⟩ := LongTails.Theorems.LineSearchZerothOrderConvex.result
  have h := hacc qLine validLine (normSq 1) (oracleOf 1) admLine
  exact ⟨qLine, normSq 1, oracleOf 1, _, _, _, _, ⟨validLine, admLine, h⟩⟩

theorem strongClassIsConvex :
    ∃ (q : LongTails.Setups.ZerothOrderStronglyConvex.Params) (f : q.E → ℝ) (O : Oracle q.E ℝ),
      LongTails.Setups.ZerothOrderStronglyConvex.spec.valid q ∧
        LongTails.Setups.ZerothOrderStronglyConvex.spec.admissible q f O ∧
        ConvexOn ℝ Set.univ f :=
  ⟨qTwo, normSq 2, oracleOf 2, validTwo, admTwo, normSqConvex 2⟩

theorem admissibleIsConvex {q : LongTails.Setups.ZerothOrderStronglyConvex.Params}
    {f : q.E → ℝ} {O : Oracle q.E ℝ}
    (h : LongTails.Setups.ZerothOrderStronglyConvex.spec.admissible q f O) :
      ConvexOn ℝ Set.univ f :=
  LongTails.Setups.ZerothOrderStronglyConvex.admissibleConvex h

theorem strongSetupNonvacuous :
    ∃ (q : LongTails.Setups.ZerothOrderStronglyConvex.Params) (f : q.E → ℝ)
      (O : Oracle q.E ℝ),
      LongTails.Setups.ZerothOrderStronglyConvex.spec.valid q ∧
        LongTails.Setups.ZerothOrderStronglyConvex.spec.admissible q f O :=
  ⟨qTwo, normSq 2, oracleOf 2, validTwo, admTwo⟩

theorem strongConclusionInhabited :
    ∃ (q : LongTails.Setups.ZerothOrderStronglyConvex.Params) (f : q.E → ℝ)
      (O : Oracle q.E ℝ) (Ω : Type) (m : MeasurableSpace Ω) (output : Ω → q.E)
      (P : ProbabilityMeasure Ω),
      LongTails.Setups.ZerothOrderStronglyConvex.spec.valid q ∧
        LongTails.Setups.ZerothOrderStronglyConvex.spec.admissible q f O ∧
        @LongTails.Setups.ZerothOrderStronglyConvex.spec.successful Ω m q f output P := by
  obtain ⟨A, hacc, _⟩ := LongTails.Theorems.ZerothOrderStronglyConvex.result
  have h := hacc qTwo validTwo (normSq 2) (oracleOf 2) admTwo
  exact ⟨qTwo, normSq 2, oracleOf 2, _, _, _, _, ⟨validTwo, admTwo, h⟩⟩

end LongTails.Tests.ZerothOrderInstances

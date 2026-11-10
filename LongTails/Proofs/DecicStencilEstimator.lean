import LongTails.Proofs.CentralStencilEstimator
import LongTails.Proofs.ScheduledSlots
import LongTails.Algorithms.DecicStencilMomentumZO

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

/-!
Estimator analysis of the ten-point coordinate stencil. The reply is the Richardson combination
`5 / 3 • central h - 20 / 21 • central (2 * h) + 5 / 14 • central (3 * h)
   - 5 / 63 • central (4 * h) + 1 / 126 • central (5 * h)`
of the five central decodes taken over the five replica bands of a `5 * n`-replica block, so its
conditional mean is the ten-point secant `dxDiff` and its mean-square noise is at most
`6 * d * σ ^ 2 / (h ^ 2 * n)`. Coordinate by coordinate `dxDiff` equals

  (2100 * (f (x + h * e i) - f (x - h * e i)) - 600 * (f (x + 2 * h * e i) - f (x - 2 * h * e i))
    + 150 * (f (x + 3 * h * e i) - f (x - 3 * h * e i))
    - 25 * (f (x + 4 * h * e i) - f (x - 4 * h * e i))
    + 2 * (f (x + 5 * h * e i) - f (x - 5 * h * e i))) / (2520 * h)

which is the stencil whose `O (h ^ 10)` bias the calling setup assumes.
-/
namespace OracleTemplate.SecantPolyak.DecicStencil

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
open OracleTemplate SecantDescent SecantPolyak ZerothOrder RobustGradient
open OracleTemplate.SecantPolyak.Centered
open OracleTemplate.SecantPolyak.CentralStencil
open OracleTemplate.Research.CubicCentralMomentumZO
open OracleTemplate.SecantPolyak.Scheduled
open OracleTemplate.Research.DecicStencilMomentumZO
open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {Ω : Type} [_ms : MeasurableSpace Ω] {p : Measure Ω} [_ip : IsProbabilityMeasure p]

/-- Ten-point coordinate secant: `5 / 3` times the central secant at bandwidth `h`, minus `20 / 21`
times the central secant at bandwidth `2 * h`, plus `5 / 14` times the central secant at bandwidth
`3 * h`, minus `5 / 63` times the central secant at bandwidth `4 * h`, plus `1 / 126` times the
central secant at bandwidth `5 * h`. -/
noncomputable def dxDiff (h : ℝ) (f : Point d → ℝ) (x : Point d) : Point d :=
  ((5 : ℝ) / 3) • cDiff h f x - ((20 : ℝ) / 21) • cDiff (2 * h) f x +
    ((5 : ℝ) / 14) • cDiff (3 * h) f x - ((5 : ℝ) / 63) • cDiff (4 * h) f x +
      ((1 : ℝ) / 126) • cDiff (5 * h) f x

/-- First replica band of a `5 * n`-replica block of raw slots. -/
noncomputable def dxCellsLow {d n : ℕ} (ω : secantSpace d (5 * n) → Ω) :
    Fin n → Fin d × Bool → Ω := fun j r => ω (band1Fin j, r)

/-- Second replica band of a `5 * n`-replica block of raw slots. -/
noncomputable def dxCellsMid {d n : ℕ} (ω : secantSpace d (5 * n) → Ω) :
    Fin n → Fin d × Bool → Ω := fun j r => ω (band2Fin j, r)

/-- Third replica band of a `5 * n`-replica block of raw slots. -/
noncomputable def dxCellsHigh {d n : ℕ} (ω : secantSpace d (5 * n) → Ω) :
    Fin n → Fin d × Bool → Ω := fun j r => ω (band3Fin j, r)

/-- Fifth replica band of a `5 * n`-replica block of raw slots. -/
noncomputable def dxCellsFive {d n : ℕ} (ω : secantSpace d (5 * n) → Ω) :
    Fin n → Fin d × Bool → Ω := fun j r => ω (band5Fin j, r)

/-- Fourth replica band of a `5 * n`-replica block of raw slots. -/
noncomputable def dxCellsTop {d n : ℕ} (ω : secantSpace d (5 * n) → Ω) :
    Fin n → Fin d × Bool → Ω := fun j r => ω (band4Fin j, r)

lemma measurable_dxCellsLow {d n : ℕ} :
    Measurable (fun ω : secantSpace d (5 * n) → Ω => dxCellsLow ω) := by
  classical
  unfold dxCellsLow
  fun_prop

lemma measurable_dxCellsMid {d n : ℕ} :
    Measurable (fun ω : secantSpace d (5 * n) → Ω => dxCellsMid ω) := by
  classical
  unfold dxCellsMid
  fun_prop

lemma measurable_dxCellsHigh {d n : ℕ} :
    Measurable (fun ω : secantSpace d (5 * n) → Ω => dxCellsHigh ω) := by
  classical
  unfold dxCellsHigh
  fun_prop

lemma measurable_dxCellsFive {d n : ℕ} :
    Measurable (fun ω : secantSpace d (5 * n) → Ω => dxCellsFive ω) := by
  classical
  unfold dxCellsFive
  fun_prop

lemma measurable_dxCellsTop {d n : ℕ} :
    Measurable (fun ω : secantSpace d (5 * n) → Ω => dxCellsTop ω) := by
  classical
  unfold dxCellsTop
  fun_prop

/-- The band embeddings are injective. -/
lemma band1Fin_injective {n : ℕ} : Function.Injective (band1Fin (n := n)) := by
  intro a b hab
  exact Fin.eq_of_val_eq (by simpa [band1Fin_val] using congrArg Fin.val hab)

lemma band2Fin_injective {n : ℕ} : Function.Injective (band2Fin (n := n)) := by
  intro a b hab
  refine Fin.eq_of_val_eq ?_
  have h1 := congrArg Fin.val hab
  simp only [band2Fin_val] at h1
  omega

lemma band3Fin_injective {n : ℕ} : Function.Injective (band3Fin (n := n)) := by
  intro a b hab
  refine Fin.eq_of_val_eq ?_
  have h1 := congrArg Fin.val hab
  simp only [band3Fin_val] at h1
  omega

lemma band5Fin_injective {n : ℕ} : Function.Injective (band5Fin (n := n)) := by
  intro a b hab
  refine Fin.eq_of_val_eq ?_
  have h1 := congrArg Fin.val hab
  simp only [band5Fin_val] at h1
  omega

lemma band4Fin_injective {n : ℕ} : Function.Injective (band4Fin (n := n)) := by
  intro a b hab
  refine Fin.eq_of_val_eq ?_
  have h1 := congrArg Fin.val hab
  simp only [band4Fin_val] at h1
  omega

/-- Reply of the ten-point stencil from the five replica bands. -/
noncomputable def dxReply {d n : ℕ} (g : Point d → Ω → ℝ) (h : ℝ) (x : Point d)
    (ξ₁ ξ₂ ξ₃ ξ₄ ξ₅ : Fin n → Fin d × Bool → Ω) : Point d :=
  ((5 : ℝ) / 3) • cReply g h x ξ₁ - ((20 : ℝ) / 21) • cReply g (2 * h) x ξ₂ +
    ((5 : ℝ) / 14) • cReply g (3 * h) x ξ₃ - ((5 : ℝ) / 63) • cReply g (4 * h) x ξ₄ +
      ((1 : ℝ) / 126) • cReply g (5 * h) x ξ₅

lemma dxDiff_apply {d : ℕ} {f : Point d → ℝ} {h : ℝ} (x : Point d) (i : Fin d) :
    dxDiff h f x i =
      (2100 * (f (x + h • direction i) - f (x - h • direction i))
          - 600 * (f (x + (2 * h) • direction i) - f (x - (2 * h) • direction i))
          + 150 * (f (x + (3 * h) • direction i) - f (x - (3 * h) • direction i))
          - 25 * (f (x + (4 * h) • direction i) - f (x - (4 * h) • direction i))
          + 2 * (f (x + (5 * h) • direction i) - f (x - (5 * h) • direction i))) / (2520 * h) := by
  classical
  by_cases hh : h = 0
  · subst hh
    simp [dxDiff, cDiff, add_zero, sub_self]
  · have h2 : (2 : ℝ) * h ≠ 0 := by
      intro h0
      apply hh
      linarith
    have h3 : (3 : ℝ) * h ≠ 0 := by
      intro h0
      apply hh
      linarith
    have h4 : (4 : ℝ) * h ≠ 0 := by
      intro h0
      apply hh
      linarith
    have h5 : (5 : ℝ) * h ≠ 0 := by
      intro h0
      apply hh
      linarith
    unfold dxDiff
    have he : (((5 : ℝ) / 3) • cDiff h f x - ((20 : ℝ) / 21) • cDiff (2 * h) f x +
        ((5 : ℝ) / 14) • cDiff (3 * h) f x - ((5 : ℝ) / 63) • cDiff (4 * h) f x +
          ((1 : ℝ) / 126) • cDiff (5 * h) f x).ofLp i =
        ((5 : ℝ) / 3) • cDiff h f x i - ((20 : ℝ) / 21) • cDiff (2 * h) f x i +
          ((5 : ℝ) / 14) • cDiff (3 * h) f x i - ((5 : ℝ) / 63) • cDiff (4 * h) f x i +
            ((1 : ℝ) / 126) • cDiff (5 * h) f x i := rfl
    rw [he, cDiff_apply, cDiff_apply, cDiff_apply, cDiff_apply, cDiff_apply]
    set A := f (x + h • direction i)
    set B := f (x - h • direction i)
    set C := f (x + (2 * h) • direction i)
    set D := f (x - (2 * h) • direction i)
    set E := f (x + (3 * h) • direction i)
    set F := f (x - (3 * h) • direction i)
    set G := f (x + (4 * h) • direction i)
    set H := f (x - (4 * h) • direction i)
    set I := f (x + (5 * h) • direction i)
    set J := f (x - (5 * h) • direction i)
    have hz : (2520 : ℝ) * h ≠ 0 := by
      intro hc
      apply hh
      linarith
    show ((5 : ℝ) / 3) * ((A - B) / (2 * h)) - ((20 : ℝ) / 21) * ((C - D) / (2 * (2 * h))) +
        ((5 : ℝ) / 14) * ((E - F) / (2 * (3 * h))) - ((5 : ℝ) / 63) * ((G - H) / (2 * (4 * h))) +
          ((1 : ℝ) / 126) * ((I - J) / (2 * (5 * h))) =
        (2100 * (A - B) - 600 * (C - D) + 150 * (E - F) - 25 * (G - H)
          + 2 * (I - J)) / (2520 * h)
    field_simp [hh, h2, h3, h4, h5, hz]
    ring

/-- Coordinate-wise error of the ten-point secant under the ten-point stencil bound. -/
lemma dxDiff_bias_sq {d : ℕ} {f : Point d → ℝ} {h β : ℝ}
    (_hβ : 0 ≤ β)
    (hq : ∀ (x v : Point d), ‖v‖ = 1 →
      |(2100 * (f (x + h • v) - f (x - h • v))
            - 600 * (f (x + (2 * h) • v) - f (x - (2 * h) • v))
          + 150 * (f (x + (3 * h) • v) - f (x - (3 * h) • v))
          - 25 * (f (x + (4 * h) • v) - f (x - (4 * h) • v))
          + 2 * (f (x + (5 * h) • v) - f (x - (5 * h) • v))) / (2520 * h)
          - ⟪gradient f x, v⟫| ≤ β)
    (x : Point d) : ‖dxDiff h f x - gradient f x‖ ^ 2 ≤ (d : ℝ) * β ^ 2 := by
  classical
  have hcoord (i : Fin d) : |dxDiff h f x i - gradient f x i| ≤ β := by
    have h1 := hq x (direction i) (direction_norm i)
    have hi : ⟪gradient f x, direction i⟫ = gradient f x i :=
      EuclideanSpace.inner_basisFun_real (Fin d) (gradient f x) i
    rw [dxDiff_apply, ← hi]
    exact h1
  have hbound (i : Fin d) :
      (dxDiff h f x - gradient f x).ofLp i ^ 2 ≤ β ^ 2 := by
    have h2 : (dxDiff h f x - gradient f x).ofLp i = dxDiff h f x i - gradient f x i := rfl
    rw [h2]
    have h3 := abs_mul_abs_self (dxDiff h f x i - gradient f x i)
    nlinarith [hcoord i, abs_nonneg (dxDiff h f x i - gradient f x i), h3]
  have hcard : (∑ _i : Fin d, β ^ 2) = (d : ℝ) * β ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ,
      smul_eq_mul]
  rw [EuclideanSpace.real_norm_sq_eq]
  calc (∑ i : Fin d, (dxDiff h f x - gradient f x).ofLp i ^ 2)
      ≤ ∑ _i : Fin d, β ^ 2 := Finset.sum_le_sum fun i _ => hbound i
    _ = (d : ℝ) * β ^ 2 := hcard

/-- Currying a flat independent batch gives the batch of cells. -/
lemma measure_map_curry_cells {d n : ℕ} :
    Measure.map (MeasurableEquiv.curry (Fin n) (Fin d × Bool) Ω)
      (Measure.pi (fun _ : Fin n × (Fin d × Bool) => p)) = batchLaw d n p := by
  have h2 := Measure.infinitePi_map_curry (fun (_ : Fin n) (_ : Fin d × Bool) => p)
  simpa [Measure.infinitePi_eq_pi, batchLaw, cellLaw] using h2

/-- The first replica band of a block is an independent batch. -/
lemma measurePreserving_dxCellsLow {d n : ℕ} :
    MeasurePreserving (fun ω : secantSpace d (5 * n) → Ω => dxCellsLow ω)
      (slotLaw d (5 * n) p) (batchLaw d n p) := by
  classical
  refine ⟨measurable_dxCellsLow, ?_⟩
  have hin : Function.Injective (fun t : Fin n × (Fin d × Bool) => (band1Fin t.1, t.2)) := by
    intro a b hab
    have hv := congrArg (fun v : Fin (5 * n) × (Fin d × Bool) => (v.1 : ℕ)) hab
    simp only [band1Fin_val] at hv
    exact Prod.ext (Fin.eq_of_val_eq hv) (by simpa using congrArg Prod.snd hab)
  have h1 : Measure.map (fun ω : Fin (5 * n) × (Fin d × Bool) → Ω =>
      fun t : Fin n × (Fin d × Bool) => ω (band1Fin t.1, t.2)) (slotLaw d (5 * n) p) =
      Measure.pi (fun _ : Fin n × (Fin d × Bool) => p) := by
    have := Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : Fin (5 * n) × (Fin d × Bool) => p) hin
    simpa [slotLaw, Measure.infinitePi_eq_pi] using this
  have hcomp : (fun ω : Fin (5 * n) × (Fin d × Bool) → Ω => dxCellsLow ω) =
      (fun ξ : Fin n × (Fin d × Bool) → Ω =>
        MeasurableEquiv.curry (Fin n) (Fin d × Bool) Ω ξ) ∘
        (fun ω : Fin (5 * n) × (Fin d × Bool) → Ω =>
          fun t : Fin n × (Fin d × Bool) => ω (band1Fin t.1, t.2)) := by
    funext ω j r
    rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), h1]
  exact measure_map_curry_cells

/-- The second replica band of a block is an independent batch. -/
lemma measurePreserving_dxCellsMid {d n : ℕ} :
    MeasurePreserving (fun ω : secantSpace d (5 * n) → Ω => dxCellsMid ω)
      (slotLaw d (5 * n) p) (batchLaw d n p) := by
  classical
  refine ⟨measurable_dxCellsMid, ?_⟩
  have hin : Function.Injective (fun t : Fin n × (Fin d × Bool) => (band2Fin t.1, t.2)) := by
    intro a b hab
    have hv := congrArg (fun v : Fin (5 * n) × (Fin d × Bool) => (v.1 : ℕ)) hab
    simp only [band2Fin_val] at hv
    have h1 : a.1.val = b.1.val := by omega
    exact Prod.ext (Fin.eq_of_val_eq h1) (by simpa using congrArg Prod.snd hab)
  have h1 : Measure.map (fun ω : Fin (5 * n) × (Fin d × Bool) → Ω =>
      fun t : Fin n × (Fin d × Bool) => ω (band2Fin t.1, t.2)) (slotLaw d (5 * n) p) =
      Measure.pi (fun _ : Fin n × (Fin d × Bool) => p) := by
    have := Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : Fin (5 * n) × (Fin d × Bool) => p) hin
    simpa [slotLaw, Measure.infinitePi_eq_pi] using this
  have hcomp : (fun ω : Fin (5 * n) × (Fin d × Bool) → Ω => dxCellsMid ω) =
      (fun ξ : Fin n × (Fin d × Bool) → Ω =>
        MeasurableEquiv.curry (Fin n) (Fin d × Bool) Ω ξ) ∘
        (fun ω : Fin (5 * n) × (Fin d × Bool) → Ω =>
          fun t : Fin n × (Fin d × Bool) => ω (band2Fin t.1, t.2)) := by
    funext ω j r
    rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), h1]
  exact measure_map_curry_cells

/-- The third replica band of a block is an independent batch. -/
lemma measurePreserving_dxCellsHigh {d n : ℕ} :
    MeasurePreserving (fun ω : secantSpace d (5 * n) → Ω => dxCellsHigh ω)
      (slotLaw d (5 * n) p) (batchLaw d n p) := by
  classical
  refine ⟨measurable_dxCellsHigh, ?_⟩
  have hin : Function.Injective (fun t : Fin n × (Fin d × Bool) => (band3Fin t.1, t.2)) := by
    intro a b hab
    have hv := congrArg (fun v : Fin (5 * n) × (Fin d × Bool) => (v.1 : ℕ)) hab
    simp only [band3Fin_val] at hv
    have h1 : a.1.val = b.1.val := by omega
    exact Prod.ext (Fin.eq_of_val_eq h1) (by simpa using congrArg Prod.snd hab)
  have h1 : Measure.map (fun ω : Fin (5 * n) × (Fin d × Bool) → Ω =>
      fun t : Fin n × (Fin d × Bool) => ω (band3Fin t.1, t.2)) (slotLaw d (5 * n) p) =
      Measure.pi (fun _ : Fin n × (Fin d × Bool) => p) := by
    have := Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : Fin (5 * n) × (Fin d × Bool) => p) hin
    simpa [slotLaw, Measure.infinitePi_eq_pi] using this
  have hcomp : (fun ω : Fin (5 * n) × (Fin d × Bool) → Ω => dxCellsHigh ω) =
      (fun ξ : Fin n × (Fin d × Bool) → Ω =>
        MeasurableEquiv.curry (Fin n) (Fin d × Bool) Ω ξ) ∘
        (fun ω : Fin (5 * n) × (Fin d × Bool) → Ω =>
          fun t : Fin n × (Fin d × Bool) => ω (band3Fin t.1, t.2)) := by
    funext ω j r
    rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), h1]
  exact measure_map_curry_cells

lemma measurePreserving_dxCellsFive {d n : ℕ} :
    MeasurePreserving (fun ω : secantSpace d (5 * n) → Ω => dxCellsFive ω)
      (slotLaw d (5 * n) p) (batchLaw d n p) := by
  classical
  refine ⟨measurable_dxCellsFive, ?_⟩
  have hin : Function.Injective (fun t : Fin n × (Fin d × Bool) => (band5Fin t.1, t.2)) := by
    intro a b hab
    have hv := congrArg (fun v : Fin (5 * n) × (Fin d × Bool) => (v.1 : ℕ)) hab
    simp only [band5Fin_val] at hv
    have h1 : a.1.val = b.1.val := by omega
    exact Prod.ext (Fin.eq_of_val_eq h1) (by simpa using congrArg Prod.snd hab)
  have h1 : Measure.map (fun ω : Fin (5 * n) × (Fin d × Bool) → Ω =>
      fun t : Fin n × (Fin d × Bool) => ω (band5Fin t.1, t.2)) (slotLaw d (5 * n) p) =
      Measure.pi (fun _ : Fin n × (Fin d × Bool) => p) := by
    have := Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : Fin (5 * n) × (Fin d × Bool) => p) hin
    simpa [slotLaw, Measure.infinitePi_eq_pi] using this
  have hcomp : (fun ω : Fin (5 * n) × (Fin d × Bool) → Ω => dxCellsFive ω) =
      (fun ξ : Fin n × (Fin d × Bool) → Ω =>
        MeasurableEquiv.curry (Fin n) (Fin d × Bool) Ω ξ) ∘
        (fun ω : Fin (5 * n) × (Fin d × Bool) → Ω =>
          fun t : Fin n × (Fin d × Bool) => ω (band5Fin t.1, t.2)) := by
    funext ω j r
    rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), h1]
  exact measure_map_curry_cells

lemma measurePreserving_dxCellsTop {d n : ℕ} :
    MeasurePreserving (fun ω : secantSpace d (5 * n) → Ω => dxCellsTop ω)
      (slotLaw d (5 * n) p) (batchLaw d n p) := by
  classical
  refine ⟨measurable_dxCellsTop, ?_⟩
  have hin : Function.Injective (fun t : Fin n × (Fin d × Bool) => (band4Fin t.1, t.2)) := by
    intro a b hab
    have hv := congrArg (fun v : Fin (5 * n) × (Fin d × Bool) => (v.1 : ℕ)) hab
    simp only [band4Fin_val] at hv
    have h1 : a.1.val = b.1.val := by omega
    exact Prod.ext (Fin.eq_of_val_eq h1) (by simpa using congrArg Prod.snd hab)
  have h1 : Measure.map (fun ω : Fin (5 * n) × (Fin d × Bool) → Ω =>
      fun t : Fin n × (Fin d × Bool) => ω (band4Fin t.1, t.2)) (slotLaw d (5 * n) p) =
      Measure.pi (fun _ : Fin n × (Fin d × Bool) => p) := by
    have := Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : Fin (5 * n) × (Fin d × Bool) => p) hin
    simpa [slotLaw, Measure.infinitePi_eq_pi] using this
  have hcomp : (fun ω : Fin (5 * n) × (Fin d × Bool) → Ω => dxCellsTop ω) =
      (fun ξ : Fin n × (Fin d × Bool) → Ω =>
        MeasurableEquiv.curry (Fin n) (Fin d × Bool) Ω ξ) ∘
        (fun ω : Fin (5 * n) × (Fin d × Bool) → Ω =>
          fun t : Fin n × (Fin d × Bool) => ω (band4Fin t.1, t.2)) := by
    funext ω j r
    rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), h1]
  exact measure_map_curry_cells
/-- The first replica band of the slot block of a scheduled round is an independent batch. -/
lemma measurePreserving_dxCellsLow_ambient {d n N : ℕ} (hnN : 5 * n ≤ N) :
    MeasurePreserving (fun ω : secantSpace d N → Ω =>
        dxCellsLow (fun t : secantSpace d (5 * n) => ω (cellInj hnN t)))
      (slotLaw d N p) (batchLaw d n p) := by
  classical
  have hmeas : Measurable (fun ω : secantSpace d N → Ω =>
      fun t : Fin n × (Fin d × Bool) => ω (cellInj hnN (band1Fin t.1, t.2))) :=
    measurable_pi_iff.mpr fun t => measurable_pi_apply (cellInj hnN (band1Fin t.1, t.2))
  refine ⟨(MeasurableEquiv.curry (Fin n) (Fin d × Bool) Ω).measurable.comp hmeas, ?_⟩
  have hin : Function.Injective (fun t : Fin n × (Fin d × Bool) =>
      cellInj (d := d) hnN (band1Fin t.1, t.2)) := by
    intro a b hab
    have h1 := cellInj_injective (d := d) hnN hab
    have hv := congrArg (fun v : Fin (5 * n) × (Fin d × Bool) => (v.1 : ℕ)) h1
    simp only [band1Fin_val] at hv
    exact Prod.ext (Fin.eq_of_val_eq hv) (by simpa using congrArg Prod.snd h1)
  have hcomp : (fun ω : secantSpace d N → Ω =>
      dxCellsLow (fun t : secantSpace d (5 * n) => ω (cellInj hnN t))) =
      (fun ξ : Fin n × (Fin d × Bool) → Ω =>
        MeasurableEquiv.curry (Fin n) (Fin d × Bool) Ω ξ) ∘
        (fun ω : secantSpace d N → Ω =>
          fun t : Fin n × (Fin d × Bool) => ω (cellInj hnN (band1Fin t.1, t.2))) := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop)]
  have h2 := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : secantSpace d N => p) hin
  rw [slotLaw, ← Measure.infinitePi_eq_pi, h2, Measure.infinitePi_eq_pi]
  exact measure_map_curry_cells

/-- The second replica band of the slot block of a scheduled round is an independent batch. -/
lemma measurePreserving_dxCellsMid_ambient {d n N : ℕ} (hnN : 5 * n ≤ N) :
    MeasurePreserving (fun ω : secantSpace d N → Ω =>
        dxCellsMid (fun t : secantSpace d (5 * n) => ω (cellInj hnN t)))
      (slotLaw d N p) (batchLaw d n p) := by
  classical
  have hmeas : Measurable (fun ω : secantSpace d N → Ω =>
      fun t : Fin n × (Fin d × Bool) => ω (cellInj hnN (band2Fin t.1, t.2))) :=
    measurable_pi_iff.mpr fun t => measurable_pi_apply (cellInj hnN (band2Fin t.1, t.2))
  refine ⟨(MeasurableEquiv.curry (Fin n) (Fin d × Bool) Ω).measurable.comp hmeas, ?_⟩
  have hin : Function.Injective (fun t : Fin n × (Fin d × Bool) =>
      cellInj (d := d) hnN (band2Fin t.1, t.2)) := by
    intro a b hab
    have h1 := cellInj_injective (d := d) hnN hab
    have hv := congrArg (fun v : Fin (5 * n) × (Fin d × Bool) => (v.1 : ℕ)) h1
    simp only [band2Fin_val] at hv
    have h2 : a.1.val = b.1.val := by omega
    exact Prod.ext (Fin.eq_of_val_eq h2) (by simpa using congrArg Prod.snd h1)
  have hcomp : (fun ω : secantSpace d N → Ω =>
      dxCellsMid (fun t : secantSpace d (5 * n) => ω (cellInj hnN t))) =
      (fun ξ : Fin n × (Fin d × Bool) → Ω =>
        MeasurableEquiv.curry (Fin n) (Fin d × Bool) Ω ξ) ∘
        (fun ω : secantSpace d N → Ω =>
          fun t : Fin n × (Fin d × Bool) => ω (cellInj hnN (band2Fin t.1, t.2))) := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop)]
  have h2 := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : secantSpace d N => p) hin
  rw [slotLaw, ← Measure.infinitePi_eq_pi, h2, Measure.infinitePi_eq_pi]
  exact measure_map_curry_cells

/-- The third replica band of the slot block of a scheduled round is an independent batch. -/
lemma measurePreserving_dxCellsHigh_ambient {d n N : ℕ} (hnN : 5 * n ≤ N) :
    MeasurePreserving (fun ω : secantSpace d N → Ω =>
        dxCellsHigh (fun t : secantSpace d (5 * n) => ω (cellInj hnN t)))
      (slotLaw d N p) (batchLaw d n p) := by
  classical
  have hmeas : Measurable (fun ω : secantSpace d N → Ω =>
      fun t : Fin n × (Fin d × Bool) => ω (cellInj hnN (band3Fin t.1, t.2))) :=
    measurable_pi_iff.mpr fun t => measurable_pi_apply (cellInj hnN (band3Fin t.1, t.2))
  refine ⟨(MeasurableEquiv.curry (Fin n) (Fin d × Bool) Ω).measurable.comp hmeas, ?_⟩
  have hin : Function.Injective (fun t : Fin n × (Fin d × Bool) =>
      cellInj (d := d) hnN (band3Fin t.1, t.2)) := by
    intro a b hab
    have h1 := cellInj_injective (d := d) hnN hab
    have hv := congrArg (fun v : Fin (5 * n) × (Fin d × Bool) => (v.1 : ℕ)) h1
    simp only [band3Fin_val] at hv
    have h2 : a.1.val = b.1.val := by omega
    exact Prod.ext (Fin.eq_of_val_eq h2) (by simpa using congrArg Prod.snd h1)
  have hcomp : (fun ω : secantSpace d N → Ω =>
      dxCellsHigh (fun t : secantSpace d (5 * n) => ω (cellInj hnN t))) =
      (fun ξ : Fin n × (Fin d × Bool) → Ω =>
        MeasurableEquiv.curry (Fin n) (Fin d × Bool) Ω ξ) ∘
        (fun ω : secantSpace d N → Ω =>
          fun t : Fin n × (Fin d × Bool) => ω (cellInj hnN (band3Fin t.1, t.2))) := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop)]
  have h2 := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : secantSpace d N => p) hin
  rw [slotLaw, ← Measure.infinitePi_eq_pi, h2, Measure.infinitePi_eq_pi]
  exact measure_map_curry_cells

lemma measurePreserving_dxCellsFive_ambient {d n N : ℕ} (hnN : 5 * n ≤ N) :
    MeasurePreserving (fun ω : secantSpace d N → Ω =>
        dxCellsFive (fun t : secantSpace d (5 * n) => ω (cellInj hnN t)))
      (slotLaw d N p) (batchLaw d n p) := by
  classical
  have hmeas : Measurable (fun ω : secantSpace d N → Ω =>
      fun t : Fin n × (Fin d × Bool) => ω (cellInj hnN (band5Fin t.1, t.2))) :=
    measurable_pi_iff.mpr fun t => measurable_pi_apply (cellInj hnN (band5Fin t.1, t.2))
  refine ⟨(MeasurableEquiv.curry (Fin n) (Fin d × Bool) Ω).measurable.comp hmeas, ?_⟩
  have hin : Function.Injective (fun t : Fin n × (Fin d × Bool) =>
      cellInj (d := d) hnN (band5Fin t.1, t.2)) := by
    intro a b hab
    have h1 := cellInj_injective (d := d) hnN hab
    have hv := congrArg (fun v : Fin (5 * n) × (Fin d × Bool) => (v.1 : ℕ)) h1
    simp only [band5Fin_val] at hv
    have h2 : a.1.val = b.1.val := by omega
    exact Prod.ext (Fin.eq_of_val_eq h2) (by simpa using congrArg Prod.snd h1)
  have hcomp : (fun ω : secantSpace d N → Ω =>
      dxCellsFive (fun t : secantSpace d (5 * n) => ω (cellInj hnN t))) =
      (fun ξ : Fin n × (Fin d × Bool) → Ω =>
        MeasurableEquiv.curry (Fin n) (Fin d × Bool) Ω ξ) ∘
        (fun ω : secantSpace d N → Ω =>
          fun t : Fin n × (Fin d × Bool) => ω (cellInj hnN (band5Fin t.1, t.2))) := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop)]
  have h2 := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : secantSpace d N => p) hin
  rw [slotLaw, ← Measure.infinitePi_eq_pi, h2, Measure.infinitePi_eq_pi]
  exact measure_map_curry_cells

lemma measurePreserving_dxCellsTop_ambient {d n N : ℕ} (hnN : 5 * n ≤ N) :
    MeasurePreserving (fun ω : secantSpace d N → Ω =>
        dxCellsTop (fun t : secantSpace d (5 * n) => ω (cellInj hnN t)))
      (slotLaw d N p) (batchLaw d n p) := by
  classical
  have hmeas : Measurable (fun ω : secantSpace d N → Ω =>
      fun t : Fin n × (Fin d × Bool) => ω (cellInj hnN (band4Fin t.1, t.2))) :=
    measurable_pi_iff.mpr fun t => measurable_pi_apply (cellInj hnN (band4Fin t.1, t.2))
  refine ⟨(MeasurableEquiv.curry (Fin n) (Fin d × Bool) Ω).measurable.comp hmeas, ?_⟩
  have hin : Function.Injective (fun t : Fin n × (Fin d × Bool) =>
      cellInj (d := d) hnN (band4Fin t.1, t.2)) := by
    intro a b hab
    have h1 := cellInj_injective (d := d) hnN hab
    have hv := congrArg (fun v : Fin (5 * n) × (Fin d × Bool) => (v.1 : ℕ)) h1
    simp only [band4Fin_val] at hv
    have h2 : a.1.val = b.1.val := by omega
    exact Prod.ext (Fin.eq_of_val_eq h2) (by simpa using congrArg Prod.snd h1)
  have hcomp : (fun ω : secantSpace d N → Ω =>
      dxCellsTop (fun t : secantSpace d (5 * n) => ω (cellInj hnN t))) =
      (fun ξ : Fin n × (Fin d × Bool) → Ω =>
        MeasurableEquiv.curry (Fin n) (Fin d × Bool) Ω ξ) ∘
        (fun ω : secantSpace d N → Ω =>
          fun t : Fin n × (Fin d × Bool) => ω (cellInj hnN (band4Fin t.1, t.2))) := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop)]
  have h2 := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : secantSpace d N => p) hin
  rw [slotLaw, ← Measure.infinitePi_eq_pi, h2, Measure.infinitePi_eq_pi]
  exact measure_map_curry_cells
/-- Cauchy-Schwarz for five nonnegative weights. -/
lemma decic_cs5 (w1 w2 w3 w4 w5 a b c e f : ℝ) (hw1 : 0 ≤ w1) (hw2 : 0 ≤ w2) (hw3 : 0 ≤ w3)
    (hw4 : 0 ≤ w4) (hw5 : 0 ≤ w5) :
    (w1 * a + w2 * b + w3 * c + w4 * e + w5 * f) ^ 2
      ≤ (w1 + w2 + w3 + w4 + w5) *
          (w1 * a ^ 2 + w2 * b ^ 2 + w3 * c ^ 2 + w4 * e ^ 2 + w5 * f ^ 2) := by
  have hkey : (w1 + w2 + w3 + w4 + w5) *
        (w1 * a ^ 2 + w2 * b ^ 2 + w3 * c ^ 2 + w4 * e ^ 2 + w5 * f ^ 2)
      - (w1 * a + w2 * b + w3 * c + w4 * e + w5 * f) ^ 2
      = w1 * w2 * (a - b) ^ 2 + w1 * w3 * (a - c) ^ 2 + w1 * w4 * (a - e) ^ 2
          + w1 * w5 * (a - f) ^ 2 + w2 * w3 * (b - c) ^ 2 + w2 * w4 * (b - e) ^ 2
          + w2 * w5 * (b - f) ^ 2 + w3 * w4 * (c - e) ^ 2 + w3 * w5 * (c - f) ^ 2
          + w4 * w5 * (e - f) ^ 2 := by ring
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - e), sq_nonneg (a - f),
    sq_nonneg (b - c), sq_nonneg (b - e), sq_nonneg (b - f), sq_nonneg (c - e),
    sq_nonneg (c - f), sq_nonneg (e - f), mul_nonneg hw1 hw2, mul_nonneg hw1 hw3,
    mul_nonneg hw1 hw4, mul_nonneg hw1 hw5, mul_nonneg hw2 hw3, mul_nonneg hw2 hw4,
    mul_nonneg hw2 hw5, mul_nonneg hw3 hw4, mul_nonneg hw3 hw5, mul_nonneg hw4 hw5, hkey]

/-- Squaring preserves order on nonnegative numbers. -/
lemma decic_sq_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : a ^ 2 ≤ b ^ 2 := by nlinarith

/-- Triangle inequality for five vectors. -/
lemma decic_norm5 {V : Type} [SeminormedAddCommGroup V] (a b c e f : V) :
    ‖a - b + c - e + f‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖e‖ + ‖f‖ := by
  nlinarith [norm_sub_le a b, norm_add_le (a - b) c, norm_sub_le (a - b + c) e,
    norm_add_le (a - b + c - e) f]

/-- Pointwise cost of the Richardson combination: the squared error of the ten-point reply is at
most `193 / 63` times the weighted sum of the squared errors of the five central replies. -/
lemma dxReply_pointwise {d n : ℕ} {g : Point d → Ω → ℝ} {f : Point d → ℝ} {h : ℝ} (x : Point d)
    (ξ₁ ξ₂ ξ₃ ξ₄ ξ₅ : Fin n → Fin d × Bool → Ω) :
    ‖dxReply g h x ξ₁ ξ₂ ξ₃ ξ₄ ξ₅ - dxDiff h f x‖ ^ 2 ≤
      ((193 : ℝ) / 63) * (((5 : ℝ) / 3) * ‖cReply g h x ξ₁ - cDiff h f x‖ ^ 2 +
        ((20 : ℝ) / 21) * ‖cReply g (2 * h) x ξ₂ - cDiff (2 * h) f x‖ ^ 2 +
          ((5 : ℝ) / 14) * ‖cReply g (3 * h) x ξ₃ - cDiff (3 * h) f x‖ ^ 2 +
            ((5 : ℝ) / 63) * ‖cReply g (4 * h) x ξ₄ - cDiff (4 * h) f x‖ ^ 2 +
              ((1 : ℝ) / 126) * ‖cReply g (5 * h) x ξ₅ - cDiff (5 * h) f x‖ ^ 2) := by
  classical
  set u₁ := cReply g h x ξ₁ - cDiff h f x with hu1
  set u₂ := cReply g (2 * h) x ξ₂ - cDiff (2 * h) f x with hu2
  set u₃ := cReply g (3 * h) x ξ₃ - cDiff (3 * h) f x with hu3
  set u₄ := cReply g (4 * h) x ξ₄ - cDiff (4 * h) f x with hu4
  set u₅ := cReply g (5 * h) x ξ₅ - cDiff (5 * h) f x with hu5
  have he : dxReply g h x ξ₁ ξ₂ ξ₃ ξ₄ ξ₅ - dxDiff h f x =
      ((5 : ℝ) / 3) • u₁ - ((20 : ℝ) / 21) • u₂ + ((5 : ℝ) / 14) • u₃ - ((5 : ℝ) / 63) • u₄ +
        ((1 : ℝ) / 126) • u₅ := by
    unfold dxReply dxDiff
    rw [smul_sub, smul_sub, smul_sub, smul_sub, smul_sub]
    abel
  have p1 : ‖((5 : ℝ) / 3) • u₁‖ = ((5 : ℝ) / 3) * ‖u₁‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (5 : ℝ) / 3)]
  have p2 : ‖((20 : ℝ) / 21) • u₂‖ = ((20 : ℝ) / 21) * ‖u₂‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (20 : ℝ) / 21)]
  have p3 : ‖((5 : ℝ) / 14) • u₃‖ = ((5 : ℝ) / 14) * ‖u₃‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (5 : ℝ) / 14)]
  have p4 : ‖((5 : ℝ) / 63) • u₄‖ = ((5 : ℝ) / 63) * ‖u₄‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (5 : ℝ) / 63)]
  have p5 : ‖((1 : ℝ) / 126) • u₅‖ = ((1 : ℝ) / 126) * ‖u₅‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 126)]
  have hnorm : ‖dxReply g h x ξ₁ ξ₂ ξ₃ ξ₄ ξ₅ - dxDiff h f x‖ ≤
      ((5 : ℝ) / 3) * ‖u₁‖ + ((20 : ℝ) / 21) * ‖u₂‖ + ((5 : ℝ) / 14) * ‖u₃‖ +
        ((5 : ℝ) / 63) * ‖u₄‖ + ((1 : ℝ) / 126) * ‖u₅‖ := by
    rw [he]
    refine le_trans (decic_norm5 _ _ _ _ _) ?_
    rw [p1, p2, p3, p4, p5]
  have hsq : (((5 : ℝ) / 3) * ‖u₁‖ + ((20 : ℝ) / 21) * ‖u₂‖ + ((5 : ℝ) / 14) * ‖u₃‖
      + ((5 : ℝ) / 63) * ‖u₄‖ + ((1 : ℝ) / 126) * ‖u₅‖) ^ 2 ≤
      ((193 : ℝ) / 63) * (((5 : ℝ) / 3) * ‖u₁‖ ^ 2 + ((20 : ℝ) / 21) * ‖u₂‖ ^ 2
        + ((5 : ℝ) / 14) * ‖u₃‖ ^ 2 + ((5 : ℝ) / 63) * ‖u₄‖ ^ 2 + ((1 : ℝ) / 126) * ‖u₅‖ ^ 2) := by
    have hw : (5 : ℝ) / 3 + 20 / 21 + 5 / 14 + 5 / 63 + 1 / 126 = 193 / 63 := by norm_num
    have hcs := decic_cs5 ((5 : ℝ) / 3) ((20 : ℝ) / 21) ((5 : ℝ) / 14) ((5 : ℝ) / 63)
      ((1 : ℝ) / 126) ‖u₁‖ ‖u₂‖ ‖u₃‖ ‖u₄‖ ‖u₅‖ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
    rwa [hw] at hcs
  exact decic_sq_le (norm_nonneg _) hnorm |>.trans hsq

/-- Widening the stencil bandwidth by `c` divides the batch variance by `c ^ 2`. -/
lemma decic_band_scale (d : ℕ) (h σ c : ℝ) (n : ℕ) :
    (d : ℝ) * σ ^ 2 / ((c * h) ^ 2 * (n : ℝ)) =
      (1 / c ^ 2) * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (n : ℝ))) := by
  by_cases hc : c = 0
  · subst hc
    simp
  · by_cases hz : (h ^ 2 * (n : ℝ)) = 0
    · have h1 : ((c * h) ^ 2 * (n : ℝ) : ℝ) = c ^ 2 * (h ^ 2 * (n : ℝ)) := by ring
      rw [h1, hz]
      simp [mul_zero]
    · have h1 : ((c * h) ^ 2 * (n : ℝ) : ℝ) = c ^ 2 * (h ^ 2 * (n : ℝ)) := by ring
      rw [h1]
      field_simp [hz, pow_ne_zero (2 : ℕ) hc]

/-- Doubling the bandwidth divides the batch variance by four. -/
lemma decic_scale2 (d : ℕ) (h σ : ℝ) (n : ℕ) :
    (d : ℝ) * σ ^ 2 / ((2 * h) ^ 2 * (n : ℝ)) ≤
      ((1 : ℝ) / 4) * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (n : ℝ))) := by
  rw [decic_band_scale]
  norm_num

/-- Tripling the bandwidth divides the batch variance by nine. -/
lemma decic_scale3 (d : ℕ) (h σ : ℝ) (n : ℕ) :
    (d : ℝ) * σ ^ 2 / ((3 * h) ^ 2 * (n : ℝ)) ≤
      ((1 : ℝ) / 9) * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (n : ℝ))) := by
  rw [decic_band_scale]
  norm_num

/-- Quadrupling the bandwidth divides the batch variance by sixteen. -/
lemma decic_scale4 (d : ℕ) (h σ : ℝ) (n : ℕ) :
    (d : ℝ) * σ ^ 2 / ((4 * h) ^ 2 * (n : ℝ)) ≤
      ((1 : ℝ) / 16) * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (n : ℝ))) := by
  rw [decic_band_scale]
  norm_num

/-- Quintupling the bandwidth divides the batch variance by twenty-five. -/
lemma decic_scale5 (d : ℕ) (h σ : ℝ) (n : ℕ) :
    (d : ℝ) * σ ^ 2 / ((5 * h) ^ 2 * (n : ℝ)) ≤
      ((1 : ℝ) / 25) * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (n : ℝ))) := by
  rw [decic_band_scale]
  norm_num

/-- Richardson bookkeeping for the ten-point combination. -/
lemma decic_noise_arith (v v2 v3 v4 v5 : ℝ) (_hv : 0 ≤ v) (h2 : v2 ≤ ((1 : ℝ) / 4) * v)
    (h3 : v3 ≤ ((1 : ℝ) / 9) * v) (h4 : v4 ≤ ((1 : ℝ) / 16) * v)
    (h5 : v5 ≤ ((1 : ℝ) / 25) * v) :
    ((193 : ℝ) / 63) * (((5 : ℝ) / 3) * v + ((20 : ℝ) / 21) * v2 + ((5 : ℝ) / 14) * v3
        + ((5 : ℝ) / 63) * v4 + ((1 : ℝ) / 126) * v5) ≤ (6 : ℝ) * v := by
  linarith

/-- The first replica band probes the stencil at bandwidth `h`. -/
lemma decPoint_rep1 {n : ℕ} (h : ℝ) (x : Point d) (t : secantSpace d n) :
    decPoint h x (rep1 t) = centralPoint h x t := by
  show centralPoint (decBandwidth h (band1Fin t.1)) x (band1Fin t.1, t.2) = centralPoint h x t
  rw [decBandwidth_first h]
  rfl

/-- The second replica band probes the stencil at bandwidth `2 * h`. -/
lemma decPoint_rep2 {n : ℕ} (h : ℝ) (x : Point d) (t : secantSpace d n) :
    decPoint h x (rep2 t) = centralPoint (2 * h) x t := by
  show centralPoint (decBandwidth h (band2Fin t.1)) x (band2Fin t.1, t.2) =
    centralPoint (2 * h) x t
  rw [decBandwidth_second h]
  rfl

/-- The third replica band probes the stencil at bandwidth `3 * h`. -/
lemma decPoint_rep3 {n : ℕ} (h : ℝ) (x : Point d) (t : secantSpace d n) :
    decPoint h x (rep3 t) = centralPoint (3 * h) x t := by
  show centralPoint (decBandwidth h (band3Fin t.1)) x (band3Fin t.1, t.2) =
    centralPoint (3 * h) x t
  rw [decBandwidth_third h]
  rfl

lemma decPoint_rep5 {n : ℕ} (h : ℝ) (x : Point d) (t : secantSpace d n) :
    decPoint h x (rep5 t) = centralPoint (5 * h) x t := by
  show centralPoint (decBandwidth h (band5Fin t.1)) x (band5Fin t.1, t.2) =
    centralPoint (5 * h) x t
  rw [decBandwidth_fifth h]
  rfl

lemma decPoint_rep4 {n : ℕ} (h : ℝ) (x : Point d) (t : secantSpace d n) :
    decPoint h x (rep4 t) = centralPoint (4 * h) x t := by
  show centralPoint (decBandwidth h (band4Fin t.1)) x (band4Fin t.1, t.2) =
    centralPoint (4 * h) x t
  rw [decBandwidth_fourth h]
  rfl

/-- The ten-point decode of raw slot replies is the Richardson combination of the five central
replies of the replica bands. -/
lemma decDecode_eq_dxReply {n : ℕ} {g : Point d → Ω → ℝ} (h : ℝ) (x : Point d)
    (ξ : secantSpace d (5 * n) → Ω) :
    decDecode h (fun t : secantSpace d (5 * n) => g (decPoint h x t) (ξ t))
      = dxReply g h x (dxCellsLow ξ) (dxCellsMid ξ) (dxCellsHigh ξ) (dxCellsTop ξ)
          (dxCellsFive ξ) := by
  classical
  have h1 : (fun t : secantSpace d n =>
      (fun s : secantSpace d (5 * n) => g (decPoint h x s) (ξ s)) (rep1 t))
      = (fun t : secantSpace d n => g (centralPoint h x t) (dxCellsLow ξ t.1 t.2)) := by
    refine funext fun t => ?_
    show g (decPoint h x (band1Fin t.1, t.2)) (ξ (band1Fin t.1, t.2)) = _
    have ht : decPoint h x (band1Fin t.1, t.2) = centralPoint h x t := decPoint_rep1 h x t
    rw [ht]
    rfl
  have h2 : (fun t : secantSpace d n =>
      (fun s : secantSpace d (5 * n) => g (decPoint h x s) (ξ s)) (rep2 t))
      = (fun t : secantSpace d n => g (centralPoint (2 * h) x t) (dxCellsMid ξ t.1 t.2)) := by
    refine funext fun t => ?_
    show g (decPoint h x (band2Fin t.1, t.2)) (ξ (band2Fin t.1, t.2)) = _
    have ht : decPoint h x (band2Fin t.1, t.2) = centralPoint (2 * h) x t := decPoint_rep2 h x t
    rw [ht]
    rfl
  have h3 : (fun t : secantSpace d n =>
      (fun s : secantSpace d (5 * n) => g (decPoint h x s) (ξ s)) (rep3 t))
      = (fun t : secantSpace d n => g (centralPoint (3 * h) x t) (dxCellsHigh ξ t.1 t.2)) := by
    refine funext fun t => ?_
    show g (decPoint h x (band3Fin t.1, t.2)) (ξ (band3Fin t.1, t.2)) = _
    have ht : decPoint h x (band3Fin t.1, t.2) = centralPoint (3 * h) x t := decPoint_rep3 h x t
    rw [ht]
    rfl
  have h4 : (fun t : secantSpace d n =>
      (fun s : secantSpace d (5 * n) => g (decPoint h x s) (ξ s)) (rep4 t))
      = (fun t : secantSpace d n => g (centralPoint (4 * h) x t) (dxCellsTop ξ t.1 t.2)) := by
    refine funext fun t => ?_
    show g (decPoint h x (band4Fin t.1, t.2)) (ξ (band4Fin t.1, t.2)) = _
    have ht : decPoint h x (band4Fin t.1, t.2) = centralPoint (4 * h) x t := decPoint_rep4 h x t
    rw [ht]
    rfl
  have h5 : (fun t : secantSpace d n =>
      (fun s : secantSpace d (5 * n) => g (decPoint h x s) (ξ s)) (rep5 t))
      = (fun t : secantSpace d n => g (centralPoint (5 * h) x t) (dxCellsFive ξ t.1 t.2)) := by
    refine funext fun t => ?_
    show g (decPoint h x (band5Fin t.1, t.2)) (ξ (band5Fin t.1, t.2)) = _
    have ht : decPoint h x (band5Fin t.1, t.2) = centralPoint (5 * h) x t := decPoint_rep5 h x t
    rw [ht]
    rfl
  calc decDecode h (fun t : secantSpace d (5 * n) => g (decPoint h x t) (ξ t))
      = ((5 : ℝ) / 3) •
            centralDecode h (fun t : secantSpace d n =>
              (fun s : secantSpace d (5 * n) => g (decPoint h x s) (ξ s)) (rep1 t)) -
          ((20 : ℝ) / 21) •
            centralDecode (2 * h) (fun t : secantSpace d n =>
              (fun s : secantSpace d (5 * n) => g (decPoint h x s) (ξ s)) (rep2 t)) +
          ((5 : ℝ) / 14) •
            centralDecode (3 * h) (fun t : secantSpace d n =>
              (fun s : secantSpace d (5 * n) => g (decPoint h x s) (ξ s)) (rep3 t)) -
          ((5 : ℝ) / 63) •
            centralDecode (4 * h) (fun t : secantSpace d n =>
              (fun s : secantSpace d (5 * n) => g (decPoint h x s) (ξ s)) (rep4 t)) +
          ((1 : ℝ) / 126) •
            centralDecode (5 * h) (fun t : secantSpace d n =>
              (fun s : secantSpace d (5 * n) => g (decPoint h x s) (ξ s)) (rep5 t)) :=
          rfl
    _ = ((5 : ℝ) / 3) • cReply g h x (dxCellsLow ξ) -
          ((20 : ℝ) / 21) • cReply g (2 * h) x (dxCellsMid ξ) +
          ((5 : ℝ) / 14) • cReply g (3 * h) x (dxCellsHigh ξ) -
          ((5 : ℝ) / 63) • cReply g (4 * h) x (dxCellsTop ξ) +
          ((1 : ℝ) / 126) • cReply g (5 * h) x (dxCellsFive ξ) := by
          rw [h1, h2, h3, h4, h5, centralDecode_eq_cReply, centralDecode_eq_cReply,
            centralDecode_eq_cReply, centralDecode_eq_cReply, centralDecode_eq_cReply]
    _ = dxReply g h x (dxCellsLow ξ) (dxCellsMid ξ) (dxCellsHigh ξ) (dxCellsTop ξ)
        (dxCellsFive ξ) := rfl

end OracleTemplate.SecantPolyak.DecicStencil

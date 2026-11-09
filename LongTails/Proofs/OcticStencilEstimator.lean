import LongTails.Proofs.CentralStencilEstimator
import LongTails.Proofs.ScheduledSlots
import LongTails.Algorithms.OcticStencilMomentumZO

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

/-!
Estimator analysis of the eight-point coordinate stencil. The reply is the Richardson combination
`8 / 5 • central h - 4 / 5 • central (2 * h) + 8 / 35 • central (3 * h) - 1 / 35 • central (4 * h)`
of the four central decodes taken over the four replica bands of a `4 * n`-replica block, so its
conditional mean is the eight-point secant `oxDiff` and its mean-square noise is at most
`5 * d * σ ^ 2 / (h ^ 2 * n)`. Coordinate by coordinate `oxDiff` equals

  (672 * (f (x + h * e i) - f (x - h * e i)) - 168 * (f (x + 2 * h * e i) - f (x - 2 * h * e i))
    + 32 * (f (x + 3 * h * e i) - f (x - 3 * h * e i))
    - 3 * (f (x + 4 * h * e i) - f (x - 4 * h * e i))) / (840 * h)

which is the stencil whose `O (h ^ 8)` bias the calling setup assumes.
-/
namespace OracleTemplate.SecantPolyak.OcticStencil

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
open OracleTemplate SecantDescent SecantPolyak ZerothOrder RobustGradient
open OracleTemplate.SecantPolyak.Centered
open OracleTemplate.SecantPolyak.CentralStencil
open OracleTemplate.Research.CubicCentralMomentumZO
open OracleTemplate.SecantPolyak.Scheduled
open OracleTemplate.Research.OcticStencilMomentumZO
open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {Ω : Type} [_ms : MeasurableSpace Ω] {p : Measure Ω} [_ip : IsProbabilityMeasure p]

/-- Eight-point coordinate secant: `8 / 5` times the central secant at bandwidth `h`, minus `4 / 5`
times the central secant at bandwidth `2 * h`, plus `8 / 35` times the central secant at bandwidth
`3 * h`, minus `1 / 35` times the central secant at bandwidth `4 * h`. -/
noncomputable def oxDiff (h : ℝ) (f : Point d → ℝ) (x : Point d) : Point d :=
  ((8 : ℝ) / 5) • cDiff h f x - ((4 : ℝ) / 5) • cDiff (2 * h) f x +
    ((8 : ℝ) / 35) • cDiff (3 * h) f x - ((1 : ℝ) / 35) • cDiff (4 * h) f x

/-- First replica band of a `4 * n`-replica block of raw slots. -/
noncomputable def oxCellsLow {d n : ℕ} (ω : secantSpace d (4 * n) → Ω) :
    Fin n → Fin d × Bool → Ω := fun j r => ω (band1Fin j, r)

/-- Second replica band of a `4 * n`-replica block of raw slots. -/
noncomputable def oxCellsMid {d n : ℕ} (ω : secantSpace d (4 * n) → Ω) :
    Fin n → Fin d × Bool → Ω := fun j r => ω (band2Fin j, r)

/-- Third replica band of a `4 * n`-replica block of raw slots. -/
noncomputable def oxCellsHigh {d n : ℕ} (ω : secantSpace d (4 * n) → Ω) :
    Fin n → Fin d × Bool → Ω := fun j r => ω (band3Fin j, r)

/-- Fourth replica band of a `4 * n`-replica block of raw slots. -/
noncomputable def oxCellsTop {d n : ℕ} (ω : secantSpace d (4 * n) → Ω) :
    Fin n → Fin d × Bool → Ω := fun j r => ω (band4Fin j, r)

lemma measurable_oxCellsLow {d n : ℕ} :
    Measurable (fun ω : secantSpace d (4 * n) → Ω => oxCellsLow ω) := by
  classical
  unfold oxCellsLow
  fun_prop

lemma measurable_oxCellsMid {d n : ℕ} :
    Measurable (fun ω : secantSpace d (4 * n) → Ω => oxCellsMid ω) := by
  classical
  unfold oxCellsMid
  fun_prop

lemma measurable_oxCellsHigh {d n : ℕ} :
    Measurable (fun ω : secantSpace d (4 * n) → Ω => oxCellsHigh ω) := by
  classical
  unfold oxCellsHigh
  fun_prop

lemma measurable_oxCellsTop {d n : ℕ} :
    Measurable (fun ω : secantSpace d (4 * n) → Ω => oxCellsTop ω) := by
  classical
  unfold oxCellsTop
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

lemma band4Fin_injective {n : ℕ} : Function.Injective (band4Fin (n := n)) := by
  intro a b hab
  refine Fin.eq_of_val_eq ?_
  have h1 := congrArg Fin.val hab
  simp only [band4Fin_val] at h1
  omega

/-- Reply of the eight-point stencil from the four replica bands. -/
noncomputable def oxReply {d n : ℕ} (g : Point d → Ω → ℝ) (h : ℝ) (x : Point d)
    (ξ₁ ξ₂ ξ₃ ξ₄ : Fin n → Fin d × Bool → Ω) : Point d :=
  ((8 : ℝ) / 5) • cReply g h x ξ₁ - ((4 : ℝ) / 5) • cReply g (2 * h) x ξ₂ +
    ((8 : ℝ) / 35) • cReply g (3 * h) x ξ₃ - ((1 : ℝ) / 35) • cReply g (4 * h) x ξ₄

lemma oxDiff_apply {d : ℕ} {f : Point d → ℝ} {h : ℝ} (x : Point d) (i : Fin d) :
    oxDiff h f x i =
      (672 * (f (x + h • direction i) - f (x - h • direction i))
          - 168 * (f (x + (2 * h) • direction i) - f (x - (2 * h) • direction i))
          + 32 * (f (x + (3 * h) • direction i) - f (x - (3 * h) • direction i))
          - 3 * (f (x + (4 * h) • direction i) - f (x - (4 * h) • direction i))) / (840 * h) := by
  classical
  by_cases hh : h = 0
  · subst hh
    simp [oxDiff, cDiff, add_zero, sub_self]
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
    unfold oxDiff
    have he : (((8 : ℝ) / 5) • cDiff h f x - ((4 : ℝ) / 5) • cDiff (2 * h) f x +
        ((8 : ℝ) / 35) • cDiff (3 * h) f x - ((1 : ℝ) / 35) • cDiff (4 * h) f x).ofLp i =
        ((8 : ℝ) / 5) • cDiff h f x i - ((4 : ℝ) / 5) • cDiff (2 * h) f x i +
          ((8 : ℝ) / 35) • cDiff (3 * h) f x i - ((1 : ℝ) / 35) • cDiff (4 * h) f x i := rfl
    rw [he, cDiff_apply, cDiff_apply, cDiff_apply, cDiff_apply]
    set A := f (x + h • direction i)
    set B := f (x - h • direction i)
    set C := f (x + (2 * h) • direction i)
    set D := f (x - (2 * h) • direction i)
    set E := f (x + (3 * h) • direction i)
    set F := f (x - (3 * h) • direction i)
    set G := f (x + (4 * h) • direction i)
    set H := f (x - (4 * h) • direction i)
    have hz : (840 : ℝ) * h ≠ 0 := by
      intro hc
      apply hh
      linarith
    show ((8 : ℝ) / 5) * ((A - B) / (2 * h)) - ((4 : ℝ) / 5) * ((C - D) / (2 * (2 * h))) +
        ((8 : ℝ) / 35) * ((E - F) / (2 * (3 * h))) - ((1 : ℝ) / 35) * ((G - H) / (2 * (4 * h))) =
        (672 * (A - B) - 168 * (C - D) + 32 * (E - F) - 3 * (G - H)) / (840 * h)
    field_simp [hh, h2, h3, h4, hz]
    ring

/-- Coordinate-wise error of the eight-point secant under the eight-point stencil bound. -/
lemma oxDiff_bias_sq {d : ℕ} {f : Point d → ℝ} {h β : ℝ}
    (_hβ : 0 ≤ β)
    (hq : ∀ (x v : Point d), ‖v‖ = 1 →
      |(672 * (f (x + h • v) - f (x - h • v))
            - 168 * (f (x + (2 * h) • v) - f (x - (2 * h) • v))
          + 32 * (f (x + (3 * h) • v) - f (x - (3 * h) • v))
          - 3 * (f (x + (4 * h) • v) - f (x - (4 * h) • v))) / (840 * h)
          - ⟪gradient f x, v⟫| ≤ β)
    (x : Point d) : ‖oxDiff h f x - gradient f x‖ ^ 2 ≤ (d : ℝ) * β ^ 2 := by
  classical
  have hcoord (i : Fin d) : |oxDiff h f x i - gradient f x i| ≤ β := by
    have h1 := hq x (direction i) (direction_norm i)
    have hi : ⟪gradient f x, direction i⟫ = gradient f x i :=
      EuclideanSpace.inner_basisFun_real (Fin d) (gradient f x) i
    rw [oxDiff_apply, ← hi]
    exact h1
  have hbound (i : Fin d) :
      (oxDiff h f x - gradient f x).ofLp i ^ 2 ≤ β ^ 2 := by
    have h2 : (oxDiff h f x - gradient f x).ofLp i = oxDiff h f x i - gradient f x i := rfl
    rw [h2]
    have h3 := abs_mul_abs_self (oxDiff h f x i - gradient f x i)
    nlinarith [hcoord i, abs_nonneg (oxDiff h f x i - gradient f x i), h3]
  have hcard : (∑ _i : Fin d, β ^ 2) = (d : ℝ) * β ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ,
      smul_eq_mul]
  rw [EuclideanSpace.real_norm_sq_eq]
  calc (∑ i : Fin d, (oxDiff h f x - gradient f x).ofLp i ^ 2)
      ≤ ∑ _i : Fin d, β ^ 2 := Finset.sum_le_sum fun i _ => hbound i
    _ = (d : ℝ) * β ^ 2 := hcard

/-- Currying a flat independent batch gives the batch of cells. -/
lemma measure_map_curry_cells {d n : ℕ} :
    Measure.map (MeasurableEquiv.curry (Fin n) (Fin d × Bool) Ω)
      (Measure.pi (fun _ : Fin n × (Fin d × Bool) => p)) = batchLaw d n p := by
  have h2 := Measure.infinitePi_map_curry (fun (_ : Fin n) (_ : Fin d × Bool) => p)
  simpa [Measure.infinitePi_eq_pi, batchLaw, cellLaw] using h2

/-- The first replica band of a block is an independent batch. -/
lemma measurePreserving_oxCellsLow {d n : ℕ} :
    MeasurePreserving (fun ω : secantSpace d (4 * n) → Ω => oxCellsLow ω)
      (slotLaw d (4 * n) p) (batchLaw d n p) := by
  classical
  refine ⟨measurable_oxCellsLow, ?_⟩
  have hin : Function.Injective (fun t : Fin n × (Fin d × Bool) => (band1Fin t.1, t.2)) := by
    intro a b hab
    have hv := congrArg (fun v : Fin (4 * n) × (Fin d × Bool) => (v.1 : ℕ)) hab
    simp only [band1Fin_val] at hv
    exact Prod.ext (Fin.eq_of_val_eq hv) (by simpa using congrArg Prod.snd hab)
  have h1 : Measure.map (fun ω : Fin (4 * n) × (Fin d × Bool) → Ω =>
      fun t : Fin n × (Fin d × Bool) => ω (band1Fin t.1, t.2)) (slotLaw d (4 * n) p) =
      Measure.pi (fun _ : Fin n × (Fin d × Bool) => p) := by
    have := Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : Fin (4 * n) × (Fin d × Bool) => p) hin
    simpa [slotLaw, Measure.infinitePi_eq_pi] using this
  have hcomp : (fun ω : Fin (4 * n) × (Fin d × Bool) → Ω => oxCellsLow ω) =
      (fun ξ : Fin n × (Fin d × Bool) → Ω =>
        MeasurableEquiv.curry (Fin n) (Fin d × Bool) Ω ξ) ∘
        (fun ω : Fin (4 * n) × (Fin d × Bool) → Ω =>
          fun t : Fin n × (Fin d × Bool) => ω (band1Fin t.1, t.2)) := by
    funext ω j r
    rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), h1]
  exact measure_map_curry_cells

/-- The second replica band of a block is an independent batch. -/
lemma measurePreserving_oxCellsMid {d n : ℕ} :
    MeasurePreserving (fun ω : secantSpace d (4 * n) → Ω => oxCellsMid ω)
      (slotLaw d (4 * n) p) (batchLaw d n p) := by
  classical
  refine ⟨measurable_oxCellsMid, ?_⟩
  have hin : Function.Injective (fun t : Fin n × (Fin d × Bool) => (band2Fin t.1, t.2)) := by
    intro a b hab
    have hv := congrArg (fun v : Fin (4 * n) × (Fin d × Bool) => (v.1 : ℕ)) hab
    simp only [band2Fin_val] at hv
    have h1 : a.1.val = b.1.val := by omega
    exact Prod.ext (Fin.eq_of_val_eq h1) (by simpa using congrArg Prod.snd hab)
  have h1 : Measure.map (fun ω : Fin (4 * n) × (Fin d × Bool) → Ω =>
      fun t : Fin n × (Fin d × Bool) => ω (band2Fin t.1, t.2)) (slotLaw d (4 * n) p) =
      Measure.pi (fun _ : Fin n × (Fin d × Bool) => p) := by
    have := Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : Fin (4 * n) × (Fin d × Bool) => p) hin
    simpa [slotLaw, Measure.infinitePi_eq_pi] using this
  have hcomp : (fun ω : Fin (4 * n) × (Fin d × Bool) → Ω => oxCellsMid ω) =
      (fun ξ : Fin n × (Fin d × Bool) → Ω =>
        MeasurableEquiv.curry (Fin n) (Fin d × Bool) Ω ξ) ∘
        (fun ω : Fin (4 * n) × (Fin d × Bool) → Ω =>
          fun t : Fin n × (Fin d × Bool) => ω (band2Fin t.1, t.2)) := by
    funext ω j r
    rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), h1]
  exact measure_map_curry_cells

/-- The third replica band of a block is an independent batch. -/
lemma measurePreserving_oxCellsHigh {d n : ℕ} :
    MeasurePreserving (fun ω : secantSpace d (4 * n) → Ω => oxCellsHigh ω)
      (slotLaw d (4 * n) p) (batchLaw d n p) := by
  classical
  refine ⟨measurable_oxCellsHigh, ?_⟩
  have hin : Function.Injective (fun t : Fin n × (Fin d × Bool) => (band3Fin t.1, t.2)) := by
    intro a b hab
    have hv := congrArg (fun v : Fin (4 * n) × (Fin d × Bool) => (v.1 : ℕ)) hab
    simp only [band3Fin_val] at hv
    have h1 : a.1.val = b.1.val := by omega
    exact Prod.ext (Fin.eq_of_val_eq h1) (by simpa using congrArg Prod.snd hab)
  have h1 : Measure.map (fun ω : Fin (4 * n) × (Fin d × Bool) → Ω =>
      fun t : Fin n × (Fin d × Bool) => ω (band3Fin t.1, t.2)) (slotLaw d (4 * n) p) =
      Measure.pi (fun _ : Fin n × (Fin d × Bool) => p) := by
    have := Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : Fin (4 * n) × (Fin d × Bool) => p) hin
    simpa [slotLaw, Measure.infinitePi_eq_pi] using this
  have hcomp : (fun ω : Fin (4 * n) × (Fin d × Bool) → Ω => oxCellsHigh ω) =
      (fun ξ : Fin n × (Fin d × Bool) → Ω =>
        MeasurableEquiv.curry (Fin n) (Fin d × Bool) Ω ξ) ∘
        (fun ω : Fin (4 * n) × (Fin d × Bool) → Ω =>
          fun t : Fin n × (Fin d × Bool) => ω (band3Fin t.1, t.2)) := by
    funext ω j r
    rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), h1]
  exact measure_map_curry_cells

lemma measurePreserving_oxCellsTop {d n : ℕ} :
    MeasurePreserving (fun ω : secantSpace d (4 * n) → Ω => oxCellsTop ω)
      (slotLaw d (4 * n) p) (batchLaw d n p) := by
  classical
  refine ⟨measurable_oxCellsTop, ?_⟩
  have hin : Function.Injective (fun t : Fin n × (Fin d × Bool) => (band4Fin t.1, t.2)) := by
    intro a b hab
    have hv := congrArg (fun v : Fin (4 * n) × (Fin d × Bool) => (v.1 : ℕ)) hab
    simp only [band4Fin_val] at hv
    have h1 : a.1.val = b.1.val := by omega
    exact Prod.ext (Fin.eq_of_val_eq h1) (by simpa using congrArg Prod.snd hab)
  have h1 : Measure.map (fun ω : Fin (4 * n) × (Fin d × Bool) → Ω =>
      fun t : Fin n × (Fin d × Bool) => ω (band4Fin t.1, t.2)) (slotLaw d (4 * n) p) =
      Measure.pi (fun _ : Fin n × (Fin d × Bool) => p) := by
    have := Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : Fin (4 * n) × (Fin d × Bool) => p) hin
    simpa [slotLaw, Measure.infinitePi_eq_pi] using this
  have hcomp : (fun ω : Fin (4 * n) × (Fin d × Bool) → Ω => oxCellsTop ω) =
      (fun ξ : Fin n × (Fin d × Bool) → Ω =>
        MeasurableEquiv.curry (Fin n) (Fin d × Bool) Ω ξ) ∘
        (fun ω : Fin (4 * n) × (Fin d × Bool) → Ω =>
          fun t : Fin n × (Fin d × Bool) => ω (band4Fin t.1, t.2)) := by
    funext ω j r
    rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), h1]
  exact measure_map_curry_cells
/-- The first replica band of the slot block of a scheduled round is an independent batch. -/
lemma measurePreserving_oxCellsLow_ambient {d n N : ℕ} (hnN : 4 * n ≤ N) :
    MeasurePreserving (fun ω : secantSpace d N → Ω =>
        oxCellsLow (fun t : secantSpace d (4 * n) => ω (cellInj hnN t)))
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
    have hv := congrArg (fun v : Fin (4 * n) × (Fin d × Bool) => (v.1 : ℕ)) h1
    simp only [band1Fin_val] at hv
    exact Prod.ext (Fin.eq_of_val_eq hv) (by simpa using congrArg Prod.snd h1)
  have hcomp : (fun ω : secantSpace d N → Ω =>
      oxCellsLow (fun t : secantSpace d (4 * n) => ω (cellInj hnN t))) =
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
lemma measurePreserving_oxCellsMid_ambient {d n N : ℕ} (hnN : 4 * n ≤ N) :
    MeasurePreserving (fun ω : secantSpace d N → Ω =>
        oxCellsMid (fun t : secantSpace d (4 * n) => ω (cellInj hnN t)))
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
    have hv := congrArg (fun v : Fin (4 * n) × (Fin d × Bool) => (v.1 : ℕ)) h1
    simp only [band2Fin_val] at hv
    have h2 : a.1.val = b.1.val := by omega
    exact Prod.ext (Fin.eq_of_val_eq h2) (by simpa using congrArg Prod.snd h1)
  have hcomp : (fun ω : secantSpace d N → Ω =>
      oxCellsMid (fun t : secantSpace d (4 * n) => ω (cellInj hnN t))) =
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
lemma measurePreserving_oxCellsHigh_ambient {d n N : ℕ} (hnN : 4 * n ≤ N) :
    MeasurePreserving (fun ω : secantSpace d N → Ω =>
        oxCellsHigh (fun t : secantSpace d (4 * n) => ω (cellInj hnN t)))
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
    have hv := congrArg (fun v : Fin (4 * n) × (Fin d × Bool) => (v.1 : ℕ)) h1
    simp only [band3Fin_val] at hv
    have h2 : a.1.val = b.1.val := by omega
    exact Prod.ext (Fin.eq_of_val_eq h2) (by simpa using congrArg Prod.snd h1)
  have hcomp : (fun ω : secantSpace d N → Ω =>
      oxCellsHigh (fun t : secantSpace d (4 * n) => ω (cellInj hnN t))) =
      (fun ξ : Fin n × (Fin d × Bool) → Ω =>
        MeasurableEquiv.curry (Fin n) (Fin d × Bool) Ω ξ) ∘
        (fun ω : secantSpace d N → Ω =>
          fun t : Fin n × (Fin d × Bool) => ω (cellInj hnN (band3Fin t.1, t.2))) := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop)]
  have h2 := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : secantSpace d N => p) hin
  rw [slotLaw, ← Measure.infinitePi_eq_pi, h2, Measure.infinitePi_eq_pi]
  exact measure_map_curry_cells

lemma measurePreserving_oxCellsTop_ambient {d n N : ℕ} (hnN : 4 * n ≤ N) :
    MeasurePreserving (fun ω : secantSpace d N → Ω =>
        oxCellsTop (fun t : secantSpace d (4 * n) => ω (cellInj hnN t)))
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
    have hv := congrArg (fun v : Fin (4 * n) × (Fin d × Bool) => (v.1 : ℕ)) h1
    simp only [band4Fin_val] at hv
    have h2 : a.1.val = b.1.val := by omega
    exact Prod.ext (Fin.eq_of_val_eq h2) (by simpa using congrArg Prod.snd h1)
  have hcomp : (fun ω : secantSpace d N → Ω =>
      oxCellsTop (fun t : secantSpace d (4 * n) => ω (cellInj hnN t))) =
      (fun ξ : Fin n × (Fin d × Bool) → Ω =>
        MeasurableEquiv.curry (Fin n) (Fin d × Bool) Ω ξ) ∘
        (fun ω : secantSpace d N → Ω =>
          fun t : Fin n × (Fin d × Bool) => ω (cellInj hnN (band4Fin t.1, t.2))) := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop)]
  have h2 := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : secantSpace d N => p) hin
  rw [slotLaw, ← Measure.infinitePi_eq_pi, h2, Measure.infinitePi_eq_pi]
  exact measure_map_curry_cells
/-- Cauchy-Schwarz for four nonnegative weights. -/
lemma octic_cs4 (w1 w2 w3 w4 a b c e : ℝ) (hw1 : 0 ≤ w1) (hw2 : 0 ≤ w2) (hw3 : 0 ≤ w3)
    (hw4 : 0 ≤ w4) :
    (w1 * a + w2 * b + w3 * c + w4 * e) ^ 2
      ≤ (w1 + w2 + w3 + w4) * (w1 * a ^ 2 + w2 * b ^ 2 + w3 * c ^ 2 + w4 * e ^ 2) := by
  have hkey : (w1 + w2 + w3 + w4) * (w1 * a ^ 2 + w2 * b ^ 2 + w3 * c ^ 2 + w4 * e ^ 2)
      - (w1 * a + w2 * b + w3 * c + w4 * e) ^ 2
      = w1 * w2 * (a - b) ^ 2 + w1 * w3 * (a - c) ^ 2 + w1 * w4 * (a - e) ^ 2
          + w2 * w3 * (b - c) ^ 2 + w2 * w4 * (b - e) ^ 2 + w3 * w4 * (c - e) ^ 2 := by ring
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - e), sq_nonneg (b - c),
    sq_nonneg (b - e), sq_nonneg (c - e), mul_nonneg hw1 hw2, mul_nonneg hw1 hw3,
    mul_nonneg hw1 hw4, mul_nonneg hw2 hw3, mul_nonneg hw2 hw4, mul_nonneg hw3 hw4, hkey]

/-- Squaring preserves order on nonnegative numbers. -/
lemma octic_sq_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : a ^ 2 ≤ b ^ 2 := by nlinarith

/-- Triangle inequality for four vectors. -/
lemma octic_norm4 {V : Type} [SeminormedAddCommGroup V] (a b c e : V) :
    ‖a - b + c - e‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖e‖ := by
  nlinarith [norm_sub_le a b, norm_add_le (a - b) c, norm_sub_le (a - b + c) e]

/-- Pointwise cost of the Richardson combination: the squared error of the eight-point reply is at
most `93 / 35` times the weighted sum of the squared errors of the four central replies. -/
lemma oxReply_pointwise {d n : ℕ} {g : Point d → Ω → ℝ} {f : Point d → ℝ} {h : ℝ} (x : Point d)
    (ξ₁ ξ₂ ξ₃ ξ₄ : Fin n → Fin d × Bool → Ω) :
    ‖oxReply g h x ξ₁ ξ₂ ξ₃ ξ₄ - oxDiff h f x‖ ^ 2 ≤
      ((93 : ℝ) / 35) * (((8 : ℝ) / 5) * ‖cReply g h x ξ₁ - cDiff h f x‖ ^ 2 +
        ((4 : ℝ) / 5) * ‖cReply g (2 * h) x ξ₂ - cDiff (2 * h) f x‖ ^ 2 +
          ((8 : ℝ) / 35) * ‖cReply g (3 * h) x ξ₃ - cDiff (3 * h) f x‖ ^ 2 +
            ((1 : ℝ) / 35) * ‖cReply g (4 * h) x ξ₄ - cDiff (4 * h) f x‖ ^ 2) := by
  classical
  set u₁ := cReply g h x ξ₁ - cDiff h f x with hu1
  set u₂ := cReply g (2 * h) x ξ₂ - cDiff (2 * h) f x with hu2
  set u₃ := cReply g (3 * h) x ξ₃ - cDiff (3 * h) f x with hu3
  set u₄ := cReply g (4 * h) x ξ₄ - cDiff (4 * h) f x with hu4
  have he : oxReply g h x ξ₁ ξ₂ ξ₃ ξ₄ - oxDiff h f x =
      ((8 : ℝ) / 5) • u₁ - ((4 : ℝ) / 5) • u₂ + ((8 : ℝ) / 35) • u₃ - ((1 : ℝ) / 35) • u₄ := by
    unfold oxReply oxDiff
    rw [smul_sub, smul_sub, smul_sub, smul_sub]
    abel
  have p1 : ‖((8 : ℝ) / 5) • u₁‖ = ((8 : ℝ) / 5) * ‖u₁‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (8 : ℝ) / 5)]
  have p2 : ‖((4 : ℝ) / 5) • u₂‖ = ((4 : ℝ) / 5) * ‖u₂‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (4 : ℝ) / 5)]
  have p3 : ‖((8 : ℝ) / 35) • u₃‖ = ((8 : ℝ) / 35) * ‖u₃‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (8 : ℝ) / 35)]
  have p4 : ‖((1 : ℝ) / 35) • u₄‖ = ((1 : ℝ) / 35) * ‖u₄‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 35)]
  have hnorm : ‖oxReply g h x ξ₁ ξ₂ ξ₃ ξ₄ - oxDiff h f x‖ ≤
      ((8 : ℝ) / 5) * ‖u₁‖ + ((4 : ℝ) / 5) * ‖u₂‖ + ((8 : ℝ) / 35) * ‖u₃‖ +
        ((1 : ℝ) / 35) * ‖u₄‖ := by
    rw [he]
    refine le_trans (octic_norm4 _ _ _ _) ?_
    rw [p1, p2, p3, p4]
  have hsq : (((8 : ℝ) / 5) * ‖u₁‖ + ((4 : ℝ) / 5) * ‖u₂‖ + ((8 : ℝ) / 35) * ‖u₃‖
      + ((1 : ℝ) / 35) * ‖u₄‖) ^ 2 ≤
      ((93 : ℝ) / 35) * (((8 : ℝ) / 5) * ‖u₁‖ ^ 2 + ((4 : ℝ) / 5) * ‖u₂‖ ^ 2
        + ((8 : ℝ) / 35) * ‖u₃‖ ^ 2 + ((1 : ℝ) / 35) * ‖u₄‖ ^ 2) := by
    have hw : (8 : ℝ) / 5 + 4 / 5 + 8 / 35 + 1 / 35 = 93 / 35 := by norm_num
    have hcs := octic_cs4 ((8 : ℝ) / 5) ((4 : ℝ) / 5) ((8 : ℝ) / 35) ((1 : ℝ) / 35)
      ‖u₁‖ ‖u₂‖ ‖u₃‖ ‖u₄‖ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    rwa [hw] at hcs
  exact octic_sq_le (norm_nonneg _) hnorm |>.trans hsq

/-- Widening the stencil bandwidth by `c` divides the batch variance by `c ^ 2`. -/
lemma octic_band_scale (d : ℕ) (h σ c : ℝ) (n : ℕ) :
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
lemma octic_scale2 (d : ℕ) (h σ : ℝ) (n : ℕ) :
    (d : ℝ) * σ ^ 2 / ((2 * h) ^ 2 * (n : ℝ)) ≤
      ((1 : ℝ) / 4) * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (n : ℝ))) := by
  rw [octic_band_scale]
  norm_num

/-- Tripling the bandwidth divides the batch variance by nine. -/
lemma octic_scale3 (d : ℕ) (h σ : ℝ) (n : ℕ) :
    (d : ℝ) * σ ^ 2 / ((3 * h) ^ 2 * (n : ℝ)) ≤
      ((1 : ℝ) / 9) * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (n : ℝ))) := by
  rw [octic_band_scale]
  norm_num

/-- Quadrupling the bandwidth divides the batch variance by sixteen. -/
lemma octic_scale4 (d : ℕ) (h σ : ℝ) (n : ℕ) :
    (d : ℝ) * σ ^ 2 / ((4 * h) ^ 2 * (n : ℝ)) ≤
      ((1 : ℝ) / 16) * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (n : ℝ))) := by
  rw [octic_band_scale]
  norm_num

/-- Richardson bookkeeping for the eight-point combination. -/
lemma octic_noise_arith (v v2 v3 v4 : ℝ) (_hv : 0 ≤ v) (h2 : v2 ≤ ((1 : ℝ) / 4) * v)
    (h3 : v3 ≤ ((1 : ℝ) / 9) * v) (h4 : v4 ≤ ((1 : ℝ) / 16) * v) :
    ((93 : ℝ) / 35) * (((8 : ℝ) / 5) * v + ((4 : ℝ) / 5) * v2 + ((8 : ℝ) / 35) * v3
        + ((1 : ℝ) / 35) * v4) ≤ (5 : ℝ) * v := by
  linarith

/-- The first replica band probes the stencil at bandwidth `h`. -/
lemma octPoint_rep1 {n : ℕ} (h : ℝ) (x : Point d) (t : secantSpace d n) :
    octPoint h x (rep1 t) = centralPoint h x t := by
  show centralPoint (octBandwidth h (band1Fin t.1)) x (band1Fin t.1, t.2) = centralPoint h x t
  rw [octBandwidth_first h]
  rfl

/-- The second replica band probes the stencil at bandwidth `2 * h`. -/
lemma octPoint_rep2 {n : ℕ} (h : ℝ) (x : Point d) (t : secantSpace d n) :
    octPoint h x (rep2 t) = centralPoint (2 * h) x t := by
  show centralPoint (octBandwidth h (band2Fin t.1)) x (band2Fin t.1, t.2) =
    centralPoint (2 * h) x t
  rw [octBandwidth_second h]
  rfl

/-- The third replica band probes the stencil at bandwidth `3 * h`. -/
lemma octPoint_rep3 {n : ℕ} (h : ℝ) (x : Point d) (t : secantSpace d n) :
    octPoint h x (rep3 t) = centralPoint (3 * h) x t := by
  show centralPoint (octBandwidth h (band3Fin t.1)) x (band3Fin t.1, t.2) =
    centralPoint (3 * h) x t
  rw [octBandwidth_third h]
  rfl

lemma octPoint_rep4 {n : ℕ} (h : ℝ) (x : Point d) (t : secantSpace d n) :
    octPoint h x (rep4 t) = centralPoint (4 * h) x t := by
  show centralPoint (octBandwidth h (band4Fin t.1)) x (band4Fin t.1, t.2) =
    centralPoint (4 * h) x t
  rw [octBandwidth_fourth h]
  rfl

/-- The eight-point decode of raw slot replies is the Richardson combination of the four central
replies of the replica bands. -/
lemma octDecode_eq_oxReply {n : ℕ} {g : Point d → Ω → ℝ} (h : ℝ) (x : Point d)
    (ξ : secantSpace d (4 * n) → Ω) :
    octDecode h (fun t : secantSpace d (4 * n) => g (octPoint h x t) (ξ t))
      = oxReply g h x (oxCellsLow ξ) (oxCellsMid ξ) (oxCellsHigh ξ) (oxCellsTop ξ) := by
  classical
  have h1 : (fun t : secantSpace d n =>
      (fun s : secantSpace d (4 * n) => g (octPoint h x s) (ξ s)) (rep1 t))
      = (fun t : secantSpace d n => g (centralPoint h x t) (oxCellsLow ξ t.1 t.2)) := by
    refine funext fun t => ?_
    show g (octPoint h x (band1Fin t.1, t.2)) (ξ (band1Fin t.1, t.2)) = _
    have ht : octPoint h x (band1Fin t.1, t.2) = centralPoint h x t := octPoint_rep1 h x t
    rw [ht]
    rfl
  have h2 : (fun t : secantSpace d n =>
      (fun s : secantSpace d (4 * n) => g (octPoint h x s) (ξ s)) (rep2 t))
      = (fun t : secantSpace d n => g (centralPoint (2 * h) x t) (oxCellsMid ξ t.1 t.2)) := by
    refine funext fun t => ?_
    show g (octPoint h x (band2Fin t.1, t.2)) (ξ (band2Fin t.1, t.2)) = _
    have ht : octPoint h x (band2Fin t.1, t.2) = centralPoint (2 * h) x t := octPoint_rep2 h x t
    rw [ht]
    rfl
  have h3 : (fun t : secantSpace d n =>
      (fun s : secantSpace d (4 * n) => g (octPoint h x s) (ξ s)) (rep3 t))
      = (fun t : secantSpace d n => g (centralPoint (3 * h) x t) (oxCellsHigh ξ t.1 t.2)) := by
    refine funext fun t => ?_
    show g (octPoint h x (band3Fin t.1, t.2)) (ξ (band3Fin t.1, t.2)) = _
    have ht : octPoint h x (band3Fin t.1, t.2) = centralPoint (3 * h) x t := octPoint_rep3 h x t
    rw [ht]
    rfl
  have h4 : (fun t : secantSpace d n =>
      (fun s : secantSpace d (4 * n) => g (octPoint h x s) (ξ s)) (rep4 t))
      = (fun t : secantSpace d n => g (centralPoint (4 * h) x t) (oxCellsTop ξ t.1 t.2)) := by
    refine funext fun t => ?_
    show g (octPoint h x (band4Fin t.1, t.2)) (ξ (band4Fin t.1, t.2)) = _
    have ht : octPoint h x (band4Fin t.1, t.2) = centralPoint (4 * h) x t := octPoint_rep4 h x t
    rw [ht]
    rfl
  calc octDecode h (fun t : secantSpace d (4 * n) => g (octPoint h x t) (ξ t))
      = ((8 : ℝ) / 5) •
            centralDecode h (fun t : secantSpace d n =>
              (fun s : secantSpace d (4 * n) => g (octPoint h x s) (ξ s)) (rep1 t)) -
          ((4 : ℝ) / 5) •
            centralDecode (2 * h) (fun t : secantSpace d n =>
              (fun s : secantSpace d (4 * n) => g (octPoint h x s) (ξ s)) (rep2 t)) +
          ((8 : ℝ) / 35) •
            centralDecode (3 * h) (fun t : secantSpace d n =>
              (fun s : secantSpace d (4 * n) => g (octPoint h x s) (ξ s)) (rep3 t)) -
          ((1 : ℝ) / 35) •
            centralDecode (4 * h) (fun t : secantSpace d n =>
              (fun s : secantSpace d (4 * n) => g (octPoint h x s) (ξ s)) (rep4 t)) :=
          rfl
    _ = ((8 : ℝ) / 5) • cReply g h x (oxCellsLow ξ) -
          ((4 : ℝ) / 5) • cReply g (2 * h) x (oxCellsMid ξ) +
          ((8 : ℝ) / 35) • cReply g (3 * h) x (oxCellsHigh ξ) -
          ((1 : ℝ) / 35) • cReply g (4 * h) x (oxCellsTop ξ) := by
          rw [h1, h2, h3, h4, centralDecode_eq_cReply, centralDecode_eq_cReply,
            centralDecode_eq_cReply, centralDecode_eq_cReply]
    _ = oxReply g h x (oxCellsLow ξ) (oxCellsMid ξ) (oxCellsHigh ξ) (oxCellsTop ξ) := rfl

end OracleTemplate.SecantPolyak.OcticStencil

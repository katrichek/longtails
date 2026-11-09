import LongTails.Proofs.CentralStencilEstimator
import LongTails.Proofs.ScheduledSlots
import LongTails.Algorithms.SexticStencilMomentumZO

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

/-!
Estimator analysis of the six-point coordinate stencil. The reply is the Richardson combination
`3 / 2 • central h - 3 / 5 • central (2 * h) + 1 / 10 • central (3 * h)` of the three central
decodes taken over the three replica thirds of a `3 * n`-replica block, so its conditional mean is
the six-point secant `sxDiff` and its mean-square noise is at most `4 * d * σ ^ 2 / (h ^ 2 * n)`.
Coordinate by coordinate `sxDiff` equals

  (f (x + 3 * h * e i) - 9 * f (x + 2 * h * e i) + 45 * f (x + h * e i)
    - 45 * f (x - h * e i) + 9 * f (x - 2 * h * e i) - f (x - 3 * h * e i)) / (60 * h)

which is the stencil whose `O (h ^ 6)` bias the calling setup assumes.
-/
namespace OracleTemplate.SecantPolyak.SexticStencil

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
open OracleTemplate SecantDescent SecantPolyak ZerothOrder RobustGradient
open OracleTemplate.SecantPolyak.Centered
open OracleTemplate.SecantPolyak.CentralStencil
open OracleTemplate.Research.CubicCentralMomentumZO
open OracleTemplate.SecantPolyak.Scheduled
open OracleTemplate.Research.SexticStencilMomentumZO
open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {Ω : Type} [_ms : MeasurableSpace Ω] {p : Measure Ω} [_ip : IsProbabilityMeasure p]

/-- Six-point coordinate secant: `3 / 2` times the central secant at bandwidth `h`, minus `3 / 5`
times the central secant at bandwidth `2 * h`, plus `1 / 10` times the central secant at bandwidth
`3 * h`. -/
noncomputable def sxDiff (h : ℝ) (f : Point d → ℝ) (x : Point d) : Point d :=
  ((3 : ℝ) / 2) • cDiff h f x - ((3 : ℝ) / 5) • cDiff (2 * h) f x +
    ((1 : ℝ) / 10) • cDiff (3 * h) f x

/-- First replica third of a `3 * n`-replica block of raw slots. -/
noncomputable def sxCellsLow {d n : ℕ} (ω : secantSpace d (3 * n) → Ω) :
    Fin n → Fin d × Bool → Ω := fun j r => ω (band1Fin j, r)

/-- Second replica third of a `3 * n`-replica block of raw slots. -/
noncomputable def sxCellsMid {d n : ℕ} (ω : secantSpace d (3 * n) → Ω) :
    Fin n → Fin d × Bool → Ω := fun j r => ω (band2Fin j, r)

/-- Third replica third of a `3 * n`-replica block of raw slots. -/
noncomputable def sxCellsHigh {d n : ℕ} (ω : secantSpace d (3 * n) → Ω) :
    Fin n → Fin d × Bool → Ω := fun j r => ω (band3Fin j, r)

lemma measurable_sxCellsLow {d n : ℕ} :
    Measurable (fun ω : secantSpace d (3 * n) → Ω => sxCellsLow ω) := by
  classical
  unfold sxCellsLow
  fun_prop

lemma measurable_sxCellsMid {d n : ℕ} :
    Measurable (fun ω : secantSpace d (3 * n) → Ω => sxCellsMid ω) := by
  classical
  unfold sxCellsMid
  fun_prop

lemma measurable_sxCellsHigh {d n : ℕ} :
    Measurable (fun ω : secantSpace d (3 * n) → Ω => sxCellsHigh ω) := by
  classical
  unfold sxCellsHigh
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

/-- Reply of the six-point stencil from the three replica thirds. -/
noncomputable def sxReply {d n : ℕ} (g : Point d → Ω → ℝ) (h : ℝ) (x : Point d)
    (ξ₁ ξ₂ ξ₃ : Fin n → Fin d × Bool → Ω) : Point d :=
  ((3 : ℝ) / 2) • cReply g h x ξ₁ - ((3 : ℝ) / 5) • cReply g (2 * h) x ξ₂ +
    ((1 : ℝ) / 10) • cReply g (3 * h) x ξ₃

lemma sxDiff_apply {d : ℕ} {f : Point d → ℝ} {h : ℝ} (x : Point d) (i : Fin d) :
    sxDiff h f x i =
      (f (x + (3 * h) • direction i) - 9 * f (x + (2 * h) • direction i)
          + 45 * f (x + h • direction i) - 45 * f (x - h • direction i)
          + 9 * f (x - (2 * h) • direction i) - f (x - (3 * h) • direction i)) / (60 * h) := by
  classical
  by_cases hh : h = 0
  · subst hh
    simp [sxDiff, cDiff, add_zero, sub_self]
  · have h2 : (2 : ℝ) * h ≠ 0 := by
      intro h0
      apply hh
      linarith
    have h3 : (3 : ℝ) * h ≠ 0 := by
      intro h0
      apply hh
      linarith
    unfold sxDiff
    have he : (((3 : ℝ) / 2) • cDiff h f x - ((3 : ℝ) / 5) • cDiff (2 * h) f x +
        ((1 : ℝ) / 10) • cDiff (3 * h) f x).ofLp i =
        ((3 : ℝ) / 2) • cDiff h f x i - ((3 : ℝ) / 5) • cDiff (2 * h) f x i +
          ((1 : ℝ) / 10) • cDiff (3 * h) f x i := rfl
    rw [he, cDiff_apply, cDiff_apply, cDiff_apply]
    set A := f (x + h • direction i)
    set B := f (x - h • direction i)
    set C := f (x + (2 * h) • direction i)
    set D := f (x - (2 * h) • direction i)
    set E := f (x + (3 * h) • direction i)
    set F := f (x - (3 * h) • direction i)
    have hz : (60 : ℝ) * h ≠ 0 := by
      intro hc
      apply hh
      linarith
    show ((3 : ℝ) / 2) * ((A - B) / (2 * h)) - ((3 : ℝ) / 5) * ((C - D) / (2 * (2 * h))) +
        ((1 : ℝ) / 10) * ((E - F) / (2 * (3 * h))) =
        (E - 9 * C + 45 * A - 45 * B + 9 * D - F) / (60 * h)
    field_simp [hh, h2, h3, hz]
    ring

/-- Coordinate-wise error of the six-point secant under the six-point stencil bound. -/
lemma sxDiff_bias_sq {d : ℕ} {f : Point d → ℝ} {h β : ℝ}
    (_hβ : 0 ≤ β)
    (hq : ∀ (x v : Point d), ‖v‖ = 1 →
      |(f (x + (3 * h) • v) - 9 * f (x + (2 * h) • v) + 45 * f (x + h • v)
            - 45 * f (x - h • v) + 9 * f (x - (2 * h) • v) - f (x - (3 * h) • v)) / (60 * h)
          - ⟪gradient f x, v⟫| ≤ β)
    (x : Point d) : ‖sxDiff h f x - gradient f x‖ ^ 2 ≤ (d : ℝ) * β ^ 2 := by
  classical
  have hcoord (i : Fin d) : |sxDiff h f x i - gradient f x i| ≤ β := by
    have h1 := hq x (direction i) (direction_norm i)
    have hi : ⟪gradient f x, direction i⟫ = gradient f x i :=
      EuclideanSpace.inner_basisFun_real (Fin d) (gradient f x) i
    rw [sxDiff_apply, ← hi]
    exact h1
  have hbound (i : Fin d) :
      (sxDiff h f x - gradient f x).ofLp i ^ 2 ≤ β ^ 2 := by
    have h2 : (sxDiff h f x - gradient f x).ofLp i = sxDiff h f x i - gradient f x i := rfl
    rw [h2]
    have h3 := abs_mul_abs_self (sxDiff h f x i - gradient f x i)
    nlinarith [hcoord i, abs_nonneg (sxDiff h f x i - gradient f x i), h3]
  have hcard : (∑ _i : Fin d, β ^ 2) = (d : ℝ) * β ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ,
      smul_eq_mul]
  rw [EuclideanSpace.real_norm_sq_eq]
  calc (∑ i : Fin d, (sxDiff h f x - gradient f x).ofLp i ^ 2)
      ≤ ∑ _i : Fin d, β ^ 2 := Finset.sum_le_sum fun i _ => hbound i
    _ = (d : ℝ) * β ^ 2 := hcard

/-- Currying a flat independent batch gives the batch of cells. -/
lemma measure_map_curry_cells {d n : ℕ} :
    Measure.map (MeasurableEquiv.curry (Fin n) (Fin d × Bool) Ω)
      (Measure.pi (fun _ : Fin n × (Fin d × Bool) => p)) = batchLaw d n p := by
  have h2 := Measure.infinitePi_map_curry (fun (_ : Fin n) (_ : Fin d × Bool) => p)
  simpa [Measure.infinitePi_eq_pi, batchLaw, cellLaw] using h2

/-- The first replica third of a block is an independent batch. -/
lemma measurePreserving_sxCellsLow {d n : ℕ} :
    MeasurePreserving (fun ω : secantSpace d (3 * n) → Ω => sxCellsLow ω)
      (slotLaw d (3 * n) p) (batchLaw d n p) := by
  classical
  refine ⟨measurable_sxCellsLow, ?_⟩
  have hin : Function.Injective (fun t : Fin n × (Fin d × Bool) => (band1Fin t.1, t.2)) := by
    intro a b hab
    have hv := congrArg (fun v : Fin (3 * n) × (Fin d × Bool) => (v.1 : ℕ)) hab
    simp only [band1Fin_val] at hv
    exact Prod.ext (Fin.eq_of_val_eq hv) (by simpa using congrArg Prod.snd hab)
  have h1 : Measure.map (fun ω : Fin (3 * n) × (Fin d × Bool) → Ω =>
      fun t : Fin n × (Fin d × Bool) => ω (band1Fin t.1, t.2)) (slotLaw d (3 * n) p) =
      Measure.pi (fun _ : Fin n × (Fin d × Bool) => p) := by
    have := Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : Fin (3 * n) × (Fin d × Bool) => p) hin
    simpa [slotLaw, Measure.infinitePi_eq_pi] using this
  have hcomp : (fun ω : Fin (3 * n) × (Fin d × Bool) → Ω => sxCellsLow ω) =
      (fun ξ : Fin n × (Fin d × Bool) → Ω =>
        MeasurableEquiv.curry (Fin n) (Fin d × Bool) Ω ξ) ∘
        (fun ω : Fin (3 * n) × (Fin d × Bool) → Ω =>
          fun t : Fin n × (Fin d × Bool) => ω (band1Fin t.1, t.2)) := by
    funext ω j r
    rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), h1]
  exact measure_map_curry_cells

/-- The second replica third of a block is an independent batch. -/
lemma measurePreserving_sxCellsMid {d n : ℕ} :
    MeasurePreserving (fun ω : secantSpace d (3 * n) → Ω => sxCellsMid ω)
      (slotLaw d (3 * n) p) (batchLaw d n p) := by
  classical
  refine ⟨measurable_sxCellsMid, ?_⟩
  have hin : Function.Injective (fun t : Fin n × (Fin d × Bool) => (band2Fin t.1, t.2)) := by
    intro a b hab
    have hv := congrArg (fun v : Fin (3 * n) × (Fin d × Bool) => (v.1 : ℕ)) hab
    simp only [band2Fin_val] at hv
    have h1 : a.1.val = b.1.val := by omega
    exact Prod.ext (Fin.eq_of_val_eq h1) (by simpa using congrArg Prod.snd hab)
  have h1 : Measure.map (fun ω : Fin (3 * n) × (Fin d × Bool) → Ω =>
      fun t : Fin n × (Fin d × Bool) => ω (band2Fin t.1, t.2)) (slotLaw d (3 * n) p) =
      Measure.pi (fun _ : Fin n × (Fin d × Bool) => p) := by
    have := Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : Fin (3 * n) × (Fin d × Bool) => p) hin
    simpa [slotLaw, Measure.infinitePi_eq_pi] using this
  have hcomp : (fun ω : Fin (3 * n) × (Fin d × Bool) → Ω => sxCellsMid ω) =
      (fun ξ : Fin n × (Fin d × Bool) → Ω =>
        MeasurableEquiv.curry (Fin n) (Fin d × Bool) Ω ξ) ∘
        (fun ω : Fin (3 * n) × (Fin d × Bool) → Ω =>
          fun t : Fin n × (Fin d × Bool) => ω (band2Fin t.1, t.2)) := by
    funext ω j r
    rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), h1]
  exact measure_map_curry_cells

/-- The third replica third of a block is an independent batch. -/
lemma measurePreserving_sxCellsHigh {d n : ℕ} :
    MeasurePreserving (fun ω : secantSpace d (3 * n) → Ω => sxCellsHigh ω)
      (slotLaw d (3 * n) p) (batchLaw d n p) := by
  classical
  refine ⟨measurable_sxCellsHigh, ?_⟩
  have hin : Function.Injective (fun t : Fin n × (Fin d × Bool) => (band3Fin t.1, t.2)) := by
    intro a b hab
    have hv := congrArg (fun v : Fin (3 * n) × (Fin d × Bool) => (v.1 : ℕ)) hab
    simp only [band3Fin_val] at hv
    have h1 : a.1.val = b.1.val := by omega
    exact Prod.ext (Fin.eq_of_val_eq h1) (by simpa using congrArg Prod.snd hab)
  have h1 : Measure.map (fun ω : Fin (3 * n) × (Fin d × Bool) → Ω =>
      fun t : Fin n × (Fin d × Bool) => ω (band3Fin t.1, t.2)) (slotLaw d (3 * n) p) =
      Measure.pi (fun _ : Fin n × (Fin d × Bool) => p) := by
    have := Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : Fin (3 * n) × (Fin d × Bool) => p) hin
    simpa [slotLaw, Measure.infinitePi_eq_pi] using this
  have hcomp : (fun ω : Fin (3 * n) × (Fin d × Bool) → Ω => sxCellsHigh ω) =
      (fun ξ : Fin n × (Fin d × Bool) → Ω =>
        MeasurableEquiv.curry (Fin n) (Fin d × Bool) Ω ξ) ∘
        (fun ω : Fin (3 * n) × (Fin d × Bool) → Ω =>
          fun t : Fin n × (Fin d × Bool) => ω (band3Fin t.1, t.2)) := by
    funext ω j r
    rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), h1]
  exact measure_map_curry_cells

/-- The first replica third of the slot block of a scheduled round is an independent batch. -/
lemma measurePreserving_sxCellsLow_ambient {d n N : ℕ} (hnN : 3 * n ≤ N) :
    MeasurePreserving (fun ω : secantSpace d N → Ω =>
        sxCellsLow (fun t : secantSpace d (3 * n) => ω (cellInj hnN t)))
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
    have hv := congrArg (fun v : Fin (3 * n) × (Fin d × Bool) => (v.1 : ℕ)) h1
    simp only [band1Fin_val] at hv
    exact Prod.ext (Fin.eq_of_val_eq hv) (by simpa using congrArg Prod.snd h1)
  have hcomp : (fun ω : secantSpace d N → Ω =>
      sxCellsLow (fun t : secantSpace d (3 * n) => ω (cellInj hnN t))) =
      (fun ξ : Fin n × (Fin d × Bool) → Ω =>
        MeasurableEquiv.curry (Fin n) (Fin d × Bool) Ω ξ) ∘
        (fun ω : secantSpace d N → Ω =>
          fun t : Fin n × (Fin d × Bool) => ω (cellInj hnN (band1Fin t.1, t.2))) := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop)]
  have h2 := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : secantSpace d N => p) hin
  rw [slotLaw, ← Measure.infinitePi_eq_pi, h2, Measure.infinitePi_eq_pi]
  exact measure_map_curry_cells

/-- The second replica third of the slot block of a scheduled round is an independent batch. -/
lemma measurePreserving_sxCellsMid_ambient {d n N : ℕ} (hnN : 3 * n ≤ N) :
    MeasurePreserving (fun ω : secantSpace d N → Ω =>
        sxCellsMid (fun t : secantSpace d (3 * n) => ω (cellInj hnN t)))
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
    have hv := congrArg (fun v : Fin (3 * n) × (Fin d × Bool) => (v.1 : ℕ)) h1
    simp only [band2Fin_val] at hv
    have h2 : a.1.val = b.1.val := by omega
    exact Prod.ext (Fin.eq_of_val_eq h2) (by simpa using congrArg Prod.snd h1)
  have hcomp : (fun ω : secantSpace d N → Ω =>
      sxCellsMid (fun t : secantSpace d (3 * n) => ω (cellInj hnN t))) =
      (fun ξ : Fin n × (Fin d × Bool) → Ω =>
        MeasurableEquiv.curry (Fin n) (Fin d × Bool) Ω ξ) ∘
        (fun ω : secantSpace d N → Ω =>
          fun t : Fin n × (Fin d × Bool) => ω (cellInj hnN (band2Fin t.1, t.2))) := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop)]
  have h2 := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : secantSpace d N => p) hin
  rw [slotLaw, ← Measure.infinitePi_eq_pi, h2, Measure.infinitePi_eq_pi]
  exact measure_map_curry_cells

/-- The third replica third of the slot block of a scheduled round is an independent batch. -/
lemma measurePreserving_sxCellsHigh_ambient {d n N : ℕ} (hnN : 3 * n ≤ N) :
    MeasurePreserving (fun ω : secantSpace d N → Ω =>
        sxCellsHigh (fun t : secantSpace d (3 * n) => ω (cellInj hnN t)))
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
    have hv := congrArg (fun v : Fin (3 * n) × (Fin d × Bool) => (v.1 : ℕ)) h1
    simp only [band3Fin_val] at hv
    have h2 : a.1.val = b.1.val := by omega
    exact Prod.ext (Fin.eq_of_val_eq h2) (by simpa using congrArg Prod.snd h1)
  have hcomp : (fun ω : secantSpace d N → Ω =>
      sxCellsHigh (fun t : secantSpace d (3 * n) => ω (cellInj hnN t))) =
      (fun ξ : Fin n × (Fin d × Bool) → Ω =>
        MeasurableEquiv.curry (Fin n) (Fin d × Bool) Ω ξ) ∘
        (fun ω : secantSpace d N → Ω =>
          fun t : Fin n × (Fin d × Bool) => ω (cellInj hnN (band3Fin t.1, t.2))) := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop)]
  have h2 := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : secantSpace d N => p) hin
  rw [slotLaw, ← Measure.infinitePi_eq_pi, h2, Measure.infinitePi_eq_pi]
  exact measure_map_curry_cells

/-- Cauchy-Schwarz for three nonnegative weights. -/
lemma sextic_cs3 (w1 w2 w3 a b c : ℝ) (hw1 : 0 ≤ w1) (hw2 : 0 ≤ w2) (hw3 : 0 ≤ w3) :
    (w1 * a + w2 * b + w3 * c) ^ 2 ≤ (w1 + w2 + w3) * (w1 * a ^ 2 + w2 * b ^ 2 + w3 * c ^ 2) := by
  have hkey : (w1 + w2 + w3) * (w1 * a ^ 2 + w2 * b ^ 2 + w3 * c ^ 2) -
      (w1 * a + w2 * b + w3 * c) ^ 2 =
      w1 * w2 * (a - b) ^ 2 + w1 * w3 * (a - c) ^ 2 + w2 * w3 * (b - c) ^ 2 := by ring
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
    mul_nonneg hw1 hw2, mul_nonneg hw1 hw3, mul_nonneg hw2 hw3, hkey]

/-- Squaring preserves order on nonnegative numbers. -/
lemma sextic_sq_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : a ^ 2 ≤ b ^ 2 := by nlinarith

/-- Pointwise cost of the Richardson combination: the squared error of the six-point reply is at
most `11 / 5` times the weighted sum of the squared errors of the three central replies. -/
lemma sxReply_pointwise {d n : ℕ} {g : Point d → Ω → ℝ} {f : Point d → ℝ} {h : ℝ} (x : Point d)
    (ξ₁ ξ₂ ξ₃ : Fin n → Fin d × Bool → Ω) :
    ‖sxReply g h x ξ₁ ξ₂ ξ₃ - sxDiff h f x‖ ^ 2 ≤
      ((11 : ℝ) / 5) * (((3 : ℝ) / 2) * ‖cReply g h x ξ₁ - cDiff h f x‖ ^ 2 +
        ((3 : ℝ) / 5) * ‖cReply g (2 * h) x ξ₂ - cDiff (2 * h) f x‖ ^ 2 +
          ((1 : ℝ) / 10) * ‖cReply g (3 * h) x ξ₃ - cDiff (3 * h) f x‖ ^ 2) := by
  classical
  have hnorm : ‖sxReply g h x ξ₁ ξ₂ ξ₃ - sxDiff h f x‖ ≤
      ((3 : ℝ) / 2) * ‖cReply g h x ξ₁ - cDiff h f x‖ +
        ((3 : ℝ) / 5) * ‖cReply g (2 * h) x ξ₂ - cDiff (2 * h) f x‖ +
          ((1 : ℝ) / 10) * ‖cReply g (3 * h) x ξ₃ - cDiff (3 * h) f x‖ := by
    have he : sxReply g h x ξ₁ ξ₂ ξ₃ - sxDiff h f x =
        ((3 : ℝ) / 2) • (cReply g h x ξ₁ - cDiff h f x) -
          ((3 : ℝ) / 5) • (cReply g (2 * h) x ξ₂ - cDiff (2 * h) f x) +
            ((1 : ℝ) / 10) • (cReply g (3 * h) x ξ₃ - cDiff (3 * h) f x) := by
      unfold sxReply sxDiff
      rw [smul_sub, smul_sub, smul_sub]
      abel
    rw [he]
    refine le_trans (norm_add_le _ _) ?_
    refine add_le_add (le_trans (norm_sub_le _ _) ?_) ?_
    · rw [norm_smul, norm_smul]
      norm_num
    · rw [norm_smul]
      norm_num
  have hsq : (((3 : ℝ) / 2) * ‖cReply g h x ξ₁ - cDiff h f x‖ +
        ((3 : ℝ) / 5) * ‖cReply g (2 * h) x ξ₂ - cDiff (2 * h) f x‖ +
          ((1 : ℝ) / 10) * ‖cReply g (3 * h) x ξ₃ - cDiff (3 * h) f x‖) ^ 2 ≤
      ((11 : ℝ) / 5) * (((3 : ℝ) / 2) * ‖cReply g h x ξ₁ - cDiff h f x‖ ^ 2 +
        ((3 : ℝ) / 5) * ‖cReply g (2 * h) x ξ₂ - cDiff (2 * h) f x‖ ^ 2 +
          ((1 : ℝ) / 10) * ‖cReply g (3 * h) x ξ₃ - cDiff (3 * h) f x‖ ^ 2) := by
    have hw : (3 : ℝ) / 2 + 3 / 5 + 1 / 10 = 11 / 5 := by norm_num
    have hcs := sextic_cs3 (3 / 2) (3 / 5) (1 / 10)
      ‖cReply g h x ξ₁ - cDiff h f x‖ ‖cReply g (2 * h) x ξ₂ - cDiff (2 * h) f x‖
      ‖cReply g (3 * h) x ξ₃ - cDiff (3 * h) f x‖ (by norm_num) (by norm_num) (by norm_num)
    rwa [hw] at hcs
  exact sextic_sq_le (norm_nonneg _) hnorm |>.trans hsq

/-- Widening the stencil bandwidth by `c` divides the batch variance by `c ^ 2`. -/
lemma sextic_band_scale (d : ℕ) (h σ c : ℝ) (n : ℕ) :
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
lemma sextic_scale2 (d : ℕ) (h σ : ℝ) (n : ℕ) :
    (d : ℝ) * σ ^ 2 / ((2 * h) ^ 2 * (n : ℝ)) ≤
      ((1 : ℝ) / 4) * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (n : ℝ))) := by
  rw [sextic_band_scale]
  norm_num

/-- Tripling the bandwidth divides the batch variance by nine. -/
lemma sextic_scale3 (d : ℕ) (h σ : ℝ) (n : ℕ) :
    (d : ℝ) * σ ^ 2 / ((3 * h) ^ 2 * (n : ℝ)) ≤
      ((1 : ℝ) / 9) * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (n : ℝ))) := by
  rw [sextic_band_scale]
  norm_num

/-- Richardson bookkeeping for the six-point combination. -/
lemma sextic_noise_arith (v v2 v3 : ℝ) (hv : 0 ≤ v) (h2 : v2 ≤ ((1 : ℝ) / 4) * v)
    (h3 : v3 ≤ ((1 : ℝ) / 9) * v) :
    ((11 : ℝ) / 5) * (((3 : ℝ) / 2) * v + ((3 : ℝ) / 5) * v2 + ((1 : ℝ) / 10) * v3) ≤ 4 * v := by
  linarith

/-- The first replica third probes the stencil at bandwidth `h`. -/
lemma hexPoint_rep1 {n : ℕ} (h : ℝ) (x : Point d) (t : secantSpace d n) :
    hexPoint h x (rep1 t) = centralPoint h x t := by
  show centralPoint (hexBandwidth h (band1Fin t.1)) x (band1Fin t.1, t.2) = centralPoint h x t
  rw [hexBandwidth_first h]
  rfl

/-- The second replica third probes the stencil at bandwidth `2 * h`. -/
lemma hexPoint_rep2 {n : ℕ} (h : ℝ) (x : Point d) (t : secantSpace d n) :
    hexPoint h x (rep2 t) = centralPoint (2 * h) x t := by
  show centralPoint (hexBandwidth h (band2Fin t.1)) x (band2Fin t.1, t.2) =
    centralPoint (2 * h) x t
  rw [hexBandwidth_second h]
  rfl

/-- The third replica third probes the stencil at bandwidth `3 * h`. -/
lemma hexPoint_rep3 {n : ℕ} (h : ℝ) (x : Point d) (t : secantSpace d n) :
    hexPoint h x (rep3 t) = centralPoint (3 * h) x t := by
  show centralPoint (hexBandwidth h (band3Fin t.1)) x (band3Fin t.1, t.2) =
    centralPoint (3 * h) x t
  rw [hexBandwidth_third h]
  rfl

/-- The six-point decode of raw slot replies is the Richardson combination of the three central
replies of the replica thirds. -/
lemma hexDecode_eq_sxReply {n : ℕ} {g : Point d → Ω → ℝ} (h : ℝ) (x : Point d)
    (ξ : secantSpace d (3 * n) → Ω) :
    hexDecode h (fun t : secantSpace d (3 * n) => g (hexPoint h x t) (ξ t))
      = sxReply g h x (sxCellsLow ξ) (sxCellsMid ξ) (sxCellsHigh ξ) := by
  classical
  have h1 : (fun t : secantSpace d n =>
      (fun s : secantSpace d (3 * n) => g (hexPoint h x s) (ξ s)) (rep1 t))
      = (fun t : secantSpace d n => g (centralPoint h x t) (sxCellsLow ξ t.1 t.2)) := by
    refine funext fun t => ?_
    show g (hexPoint h x (band1Fin t.1, t.2)) (ξ (band1Fin t.1, t.2)) = _
    have ht : hexPoint h x (band1Fin t.1, t.2) = centralPoint h x t := hexPoint_rep1 h x t
    rw [ht]
    rfl
  have h2 : (fun t : secantSpace d n =>
      (fun s : secantSpace d (3 * n) => g (hexPoint h x s) (ξ s)) (rep2 t))
      = (fun t : secantSpace d n => g (centralPoint (2 * h) x t) (sxCellsMid ξ t.1 t.2)) := by
    refine funext fun t => ?_
    show g (hexPoint h x (band2Fin t.1, t.2)) (ξ (band2Fin t.1, t.2)) = _
    have ht : hexPoint h x (band2Fin t.1, t.2) = centralPoint (2 * h) x t := hexPoint_rep2 h x t
    rw [ht]
    rfl
  have h3 : (fun t : secantSpace d n =>
      (fun s : secantSpace d (3 * n) => g (hexPoint h x s) (ξ s)) (rep3 t))
      = (fun t : secantSpace d n => g (centralPoint (3 * h) x t) (sxCellsHigh ξ t.1 t.2)) := by
    refine funext fun t => ?_
    show g (hexPoint h x (band3Fin t.1, t.2)) (ξ (band3Fin t.1, t.2)) = _
    have ht : hexPoint h x (band3Fin t.1, t.2) = centralPoint (3 * h) x t := hexPoint_rep3 h x t
    rw [ht]
    rfl
  calc hexDecode h (fun t : secantSpace d (3 * n) => g (hexPoint h x t) (ξ t))
      = ((3 : ℝ) / 2) •
            centralDecode h (fun t : secantSpace d n =>
              (fun s : secantSpace d (3 * n) => g (hexPoint h x s) (ξ s)) (rep1 t)) -
          ((3 : ℝ) / 5) •
            centralDecode (2 * h) (fun t : secantSpace d n =>
              (fun s : secantSpace d (3 * n) => g (hexPoint h x s) (ξ s)) (rep2 t)) +
          ((1 : ℝ) / 10) •
            centralDecode (3 * h) (fun t : secantSpace d n =>
              (fun s : secantSpace d (3 * n) => g (hexPoint h x s) (ξ s)) (rep3 t)) :=
          rfl
    _ = ((3 : ℝ) / 2) • cReply g h x (sxCellsLow ξ) -
          ((3 : ℝ) / 5) • cReply g (2 * h) x (sxCellsMid ξ) +
          ((1 : ℝ) / 10) • cReply g (3 * h) x (sxCellsHigh ξ) := by
          rw [h1, h2, h3, centralDecode_eq_cReply, centralDecode_eq_cReply,
            centralDecode_eq_cReply]
    _ = sxReply g h x (sxCellsLow ξ) (sxCellsMid ξ) (sxCellsHigh ξ) := rfl

end OracleTemplate.SecantPolyak.SexticStencil

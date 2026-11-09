import LongTails.Proofs.CentralStencilEstimator
import LongTails.Proofs.ScheduledSlots
import LongTails.Algorithms.QuinticStencilMomentumZO

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

/-!
Estimator analysis of the four-point coordinate stencil. The reply is the Richardson combination
`(4 • central h - central (2 * h)) / 3` of two central decodes taken over the two replica halves of
a `2 * n`-replica block, so its conditional mean is the four-point secant `qDiff` and its
mean-square noise is at most `4 * d * σ ^ 2 / (h ^ 2 * n)`. Coordinate by coordinate `qDiff` equals

  (- f (x + 2 * h * e i) + 8 * f (x + h * e i) - 8 * f (x - h * e i) + f (x - 2 * h * e i)) / (12 * h)

which is the stencil whose `O (h ^ 4)` bias the calling setup assumes.
-/
namespace OracleTemplate.SecantPolyak.QuinticStencil

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
open OracleTemplate SecantDescent SecantPolyak ZerothOrder RobustGradient
open OracleTemplate.SecantPolyak.Centered
open OracleTemplate.SecantPolyak.CentralStencil
open OracleTemplate.Research.CubicCentralMomentumZO
open OracleTemplate.SecantPolyak.Scheduled
open OracleTemplate.Research.QuinticStencilMomentumZO
open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {Ω : Type} [_ms : MeasurableSpace Ω] {p : Measure Ω} [_ip : IsProbabilityMeasure p]

/-- Four-point coordinate secant: `4 / 3` times the central secant at bandwidth `h` minus
`1 / 3` times the central secant at bandwidth `2 * h`. -/
noncomputable def qDiff (h : ℝ) (f : Point d → ℝ) (x : Point d) : Point d :=
  ((4 : ℝ) / 3) • cDiff h f x - ((1 : ℝ) / 3) • cDiff (2 * h) f x

/-- Lower replica half of a `2 * n`-replica block of raw slots. -/
noncomputable def qCellsLow {d n : ℕ} (ω : secantSpace d (2 * n) → Ω) : Fin n → Fin d × Bool → Ω :=
  fun j r => ω (lowFin j, r)

/-- Upper replica half of a `2 * n`-replica block of raw slots. -/
noncomputable def qCellsHigh {d n : ℕ} (ω : secantSpace d (2 * n) → Ω) :
    Fin n → Fin d × Bool → Ω :=
  fun j r => ω (upFin j, r)

lemma measurable_qCellsLow {d n : ℕ} :
    Measurable (fun ω : secantSpace d (2 * n) → Ω => qCellsLow ω) := by
  classical
  unfold qCellsLow
  fun_prop

lemma measurable_qCellsHigh {d n : ℕ} :
    Measurable (fun ω : secantSpace d (2 * n) → Ω => qCellsHigh ω) := by
  classical
  unfold qCellsHigh
  fun_prop

/-- Reply of the four-point stencil from the two replica halves. -/
noncomputable def qReply {d n : ℕ} (g : Point d → Ω → ℝ) (h : ℝ) (x : Point d)
    (ξ₁ ξ₂ : Fin n → Fin d × Bool → Ω) : Point d :=
  ((4 : ℝ) / 3) • cReply g h x ξ₁ - ((1 : ℝ) / 3) • cReply g (2 * h) x ξ₂

lemma qDiff_apply {d : ℕ} {f : Point d → ℝ} {h : ℝ} (x : Point d) (i : Fin d) :
    qDiff h f x i =
      (-f (x + (2 * h) • direction i) + 8 * f (x + h • direction i) -
          8 * f (x - h • direction i) + f (x - (2 * h) • direction i)) / (12 * h) := by
  classical
  by_cases hh : h = 0
  · subst hh
    simp [qDiff, cDiff, add_zero, sub_self]
  · have h2 : (2 : ℝ) * h ≠ 0 := by
      intro h0
      apply hh
      linarith
    unfold qDiff
    have he : (((4 : ℝ) / 3) • cDiff h f x - ((1 : ℝ) / 3) • cDiff (2 * h) f x).ofLp i =
        ((4 : ℝ) / 3) • cDiff h f x i - ((1 : ℝ) / 3) • cDiff (2 * h) f x i := rfl
    rw [he, cDiff_apply, cDiff_apply]
    set A := f (x + h • direction i)
    set B := f (x - h • direction i)
    set C := f (x + (2 * h) • direction i)
    set D := f (x - (2 * h) • direction i)
    have hz : (12 : ℝ) * h ≠ 0 := by
      intro hc
      apply hh
      linarith
    show ((4 : ℝ) / 3) * ((A - B) / (2 * h)) - ((1 : ℝ) / 3) * ((C - D) / (2 * (2 * h))) =
      (-C + 8 * A - 8 * B + D) / (12 * h)
    field_simp [hh, h2, hz]
    ring

/-- Coordinate-wise error of the four-point secant under the four-point stencil bound. -/
lemma qDiff_bias_sq {d : ℕ} {f : Point d → ℝ} {h β : ℝ}
    (_hβ : 0 ≤ β)
    (hq : ∀ (x v : Point d), ‖v‖ = 1 →
      |(-f (x + (2 * h) • v) + 8 * f (x + h • v) - 8 * f (x - h • v) + f (x - (2 * h) • v)) /
          (12 * h) - ⟪gradient f x, v⟫| ≤ β)
    (x : Point d) : ‖qDiff h f x - gradient f x‖ ^ 2 ≤ (d : ℝ) * β ^ 2 := by
  classical
  have hcoord (i : Fin d) : |qDiff h f x i - gradient f x i| ≤ β := by
    have h1 := hq x (direction i) (direction_norm i)
    have hi : ⟪gradient f x, direction i⟫ = gradient f x i :=
      EuclideanSpace.inner_basisFun_real (Fin d) (gradient f x) i
    rw [qDiff_apply, ← hi]
    exact h1
  have hbound (i : Fin d) :
      (qDiff h f x - gradient f x).ofLp i ^ 2 ≤ β ^ 2 := by
    have h2 : (qDiff h f x - gradient f x).ofLp i = qDiff h f x i - gradient f x i := rfl
    rw [h2]
    have h3 := abs_mul_abs_self (qDiff h f x i - gradient f x i)
    nlinarith [hcoord i, abs_nonneg (qDiff h f x i - gradient f x i), h3]
  have hcard : (∑ _i : Fin d, β ^ 2) = (d : ℝ) * β ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ,
      smul_eq_mul]
  rw [EuclideanSpace.real_norm_sq_eq]
  calc (∑ i : Fin d, (qDiff h f x - gradient f x).ofLp i ^ 2)
      ≤ ∑ _i : Fin d, β ^ 2 := Finset.sum_le_sum fun i _ => hbound i
    _ = (d : ℝ) * β ^ 2 := hcard

/-- Currying a flat independent batch gives the batch of cells. -/
lemma measure_map_curry_cells {d n : ℕ} :
    Measure.map (MeasurableEquiv.curry (Fin n) (Fin d × Bool) Ω)
      (Measure.pi (fun _ : Fin n × (Fin d × Bool) => p)) = batchLaw d n p := by
  have h2 := Measure.infinitePi_map_curry (fun (_ : Fin n) (_ : Fin d × Bool) => p)
  simpa [Measure.infinitePi_eq_pi, batchLaw, cellLaw] using h2

/-- The lower replica half of a block is an independent batch. -/
lemma measurePreserving_qCellsLow {d n : ℕ} :
    MeasurePreserving (fun ω : secantSpace d (2 * n) → Ω => qCellsLow ω)
      (slotLaw d (2 * n) p) (batchLaw d n p) := by
  classical
  refine ⟨measurable_qCellsLow, ?_⟩
  have hin : Function.Injective (fun t : Fin n × (Fin d × Bool) => (lowFin t.1, t.2)) := by
    intro a b hab
    have hv := congrArg (fun v : Fin (2 * n) × (Fin d × Bool) => (v.1 : ℕ)) hab
    simp [lowFin] at hv
    exact Prod.ext (Fin.ext hv) (by simpa using congrArg Prod.snd hab)
  have h1 : Measure.map (fun ω : Fin (2 * n) × (Fin d × Bool) → Ω =>
      fun t : Fin n × (Fin d × Bool) => ω (lowFin t.1, t.2)) (slotLaw d (2 * n) p) =
      Measure.pi (fun _ : Fin n × (Fin d × Bool) => p) := by
    have := Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : Fin (2 * n) × (Fin d × Bool) => p) hin
    simpa [slotLaw, Measure.infinitePi_eq_pi] using this
  have hcomp : (fun ω : Fin (2 * n) × (Fin d × Bool) → Ω => qCellsLow ω) =
      (fun ξ : Fin n × (Fin d × Bool) → Ω =>
        MeasurableEquiv.curry (Fin n) (Fin d × Bool) Ω ξ) ∘
        (fun ω : Fin (2 * n) × (Fin d × Bool) → Ω =>
          fun t : Fin n × (Fin d × Bool) => ω (lowFin t.1, t.2)) := by
    funext ω j r
    rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), h1]
  exact measure_map_curry_cells

/-- The upper replica half of a block is an independent batch. -/
lemma measurePreserving_qCellsHigh {d n : ℕ} :
    MeasurePreserving (fun ω : secantSpace d (2 * n) → Ω => qCellsHigh ω)
      (slotLaw d (2 * n) p) (batchLaw d n p) := by
  classical
  refine ⟨measurable_qCellsHigh, ?_⟩
  have hin : Function.Injective (fun t : Fin n × (Fin d × Bool) => (upFin t.1, t.2)) := by
    intro a b hab
    have hv := congrArg (fun v : Fin (2 * n) × (Fin d × Bool) => (v.1 : ℕ)) hab
    simp [upFin, Fin.natAdd] at hv
    exact Prod.ext (Fin.ext hv) (by simpa using congrArg Prod.snd hab)
  have h1 : Measure.map (fun ω : Fin (2 * n) × (Fin d × Bool) → Ω =>
      fun t : Fin n × (Fin d × Bool) => ω (upFin t.1, t.2)) (slotLaw d (2 * n) p) =
      Measure.pi (fun _ : Fin n × (Fin d × Bool) => p) := by
    have := Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : Fin (2 * n) × (Fin d × Bool) => p) hin
    simpa [slotLaw, Measure.infinitePi_eq_pi] using this
  have hcomp : (fun ω : Fin (2 * n) × (Fin d × Bool) → Ω => qCellsHigh ω) =
      (fun ξ : Fin n × (Fin d × Bool) → Ω =>
        MeasurableEquiv.curry (Fin n) (Fin d × Bool) Ω ξ) ∘
        (fun ω : Fin (2 * n) × (Fin d × Bool) → Ω =>
          fun t : Fin n × (Fin d × Bool) => ω (upFin t.1, t.2)) := by
    funext ω j r
    rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), h1]
  exact measure_map_curry_cells

/-- The lower replica half of the slot block of a scheduled round is an independent batch. -/
lemma measurePreserving_qCellsLow_ambient {d n N : ℕ} (hnN : 2 * n ≤ N) :
    MeasurePreserving (fun ω : secantSpace d N → Ω =>
        qCellsLow (fun t : secantSpace d (2 * n) => ω (cellInj hnN t)))
      (slotLaw d N p) (batchLaw d n p) := by
  classical
  have hmeas : Measurable (fun ω : secantSpace d N → Ω =>
      fun t : Fin n × (Fin d × Bool) => ω (cellInj hnN (lowFin t.1, t.2))) :=
    measurable_pi_iff.mpr fun t => measurable_pi_apply (cellInj hnN (lowFin t.1, t.2))
  refine ⟨(MeasurableEquiv.curry (Fin n) (Fin d × Bool) Ω).measurable.comp hmeas, ?_⟩
  have hin : Function.Injective (fun t : Fin n × (Fin d × Bool) =>
      cellInj (d := d) hnN (lowFin t.1, t.2)) := by
    intro a b hab
    have h1 := cellInj_injective (d := d) hnN hab
    have hv := congrArg (fun v : Fin (2 * n) × (Fin d × Bool) => (v.1 : ℕ)) h1
    simp [lowFin] at hv
    exact Prod.ext (Fin.ext hv) (by simpa using congrArg Prod.snd h1)
  have hcomp : (fun ω : secantSpace d N → Ω =>
      qCellsLow (fun t : secantSpace d (2 * n) => ω (cellInj hnN t))) =
      (fun ξ : Fin n × (Fin d × Bool) → Ω =>
        MeasurableEquiv.curry (Fin n) (Fin d × Bool) Ω ξ) ∘
        (fun ω : secantSpace d N → Ω =>
          fun t : Fin n × (Fin d × Bool) => ω (cellInj hnN (lowFin t.1, t.2))) := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop)]
  have h2 := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : secantSpace d N => p) hin
  rw [slotLaw, ← Measure.infinitePi_eq_pi, h2, Measure.infinitePi_eq_pi]
  exact measure_map_curry_cells

/-- The upper replica half of the slot block of a scheduled round is an independent batch. -/
lemma measurePreserving_qCellsHigh_ambient {d n N : ℕ} (hnN : 2 * n ≤ N) :
    MeasurePreserving (fun ω : secantSpace d N → Ω =>
        qCellsHigh (fun t : secantSpace d (2 * n) => ω (cellInj hnN t)))
      (slotLaw d N p) (batchLaw d n p) := by
  classical
  have hmeas : Measurable (fun ω : secantSpace d N → Ω =>
      fun t : Fin n × (Fin d × Bool) => ω (cellInj hnN (upFin t.1, t.2))) :=
    measurable_pi_iff.mpr fun t => measurable_pi_apply (cellInj hnN (upFin t.1, t.2))
  refine ⟨(MeasurableEquiv.curry (Fin n) (Fin d × Bool) Ω).measurable.comp hmeas, ?_⟩
  have hin : Function.Injective (fun t : Fin n × (Fin d × Bool) =>
      cellInj (d := d) hnN (upFin t.1, t.2)) := by
    intro a b hab
    have h1 := cellInj_injective (d := d) hnN hab
    have hv := congrArg (fun v : Fin (2 * n) × (Fin d × Bool) => (v.1 : ℕ)) h1
    simp [upFin, Fin.natAdd] at hv
    exact Prod.ext (Fin.ext hv) (by simpa using congrArg Prod.snd h1)
  have hcomp : (fun ω : secantSpace d N → Ω =>
      qCellsHigh (fun t : secantSpace d (2 * n) => ω (cellInj hnN t))) =
      (fun ξ : Fin n × (Fin d × Bool) → Ω =>
        MeasurableEquiv.curry (Fin n) (Fin d × Bool) Ω ξ) ∘
        (fun ω : secantSpace d N → Ω =>
          fun t : Fin n × (Fin d × Bool) => ω (cellInj hnN (upFin t.1, t.2))) := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop)]
  have h2 := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : secantSpace d N => p) hin
  rw [slotLaw, ← Measure.infinitePi_eq_pi, h2, Measure.infinitePi_eq_pi]
  exact measure_map_curry_cells

/-- The four-point reply is measurable at a fixed base point. -/
lemma measurable_qReply_at {d n : ℕ} {g : Point d → Ω → ℝ}
    (hg : Measurable (Function.uncurry g)) (h : ℝ) (x : Point d) :
    Measurable (fun ξ : (Fin n → Fin d × Bool → Ω) × (Fin n → Fin d × Bool → Ω) =>
      qReply g h x ξ.1 ξ.2) := by
  classical
  set W : Type := Fin n → Fin d × Bool → Ω with hW
  have h1 : Measurable (fun ξ : W × W => cReply g h x ξ.1) :=
    (measurable_cReply_at hg h x).comp (measurable_fst (α := W))
  have h2 : Measurable (fun ξ : W × W => cReply g (2 * h) x ξ.2) :=
    (measurable_cReply_at hg (2 * h) x).comp (measurable_snd (α := W))
  unfold qReply
  refine smul_measurable measurable_const h1 |>.sub (smul_measurable measurable_const h2)

/-- Pointwise cost of the Richardson combination: the squared error of the four-point reply is at
most `(32 / 9)` times the squared error of the lower-half central reply plus `(2 / 9)` times the
squared error of the upper-half central reply. -/
lemma qReply_pointwise {d n : ℕ} {g : Point d → Ω → ℝ} {f : Point d → ℝ} {h : ℝ} (x : Point d)
    (ξ₁ ξ₂ : Fin n → Fin d × Bool → Ω) :
    ‖qReply g h x ξ₁ ξ₂ - qDiff h f x‖ ^ 2 ≤
      ((32 : ℝ) / 9) * ‖cReply g h x ξ₁ - cDiff h f x‖ ^ 2 +
        ((2 : ℝ) / 9) * ‖cReply g (2 * h) x ξ₂ - cDiff (2 * h) f x‖ ^ 2 := by
  classical
  have haux : ∀ (z a b : ℝ), 0 ≤ z → 0 ≤ a → 0 ≤ b → z ≤ ((4 : ℝ) / 3) * a + ((1 : ℝ) / 3) * b →
      z ^ 2 ≤ ((32 : ℝ) / 9) * a ^ 2 + ((2 : ℝ) / 9) * b ^ 2 := by
    intro z a b hz ha hb h
    have h1 : z * z ≤ (((4 : ℝ) / 3) * a + ((1 : ℝ) / 3) * b) * z := by nlinarith
    have h2 : (((4 : ℝ) / 3) * a + ((1 : ℝ) / 3) * b) * z ≤
        (((4 : ℝ) / 3) * a + ((1 : ℝ) / 3) * b) * (((4 : ℝ) / 3) * a + ((1 : ℝ) / 3) * b) := by
      nlinarith
    have h3 : (((4 : ℝ) / 3) * a + ((1 : ℝ) / 3) * b) * (((4 : ℝ) / 3) * a + ((1 : ℝ) / 3) * b) ≤
        ((32 : ℝ) / 9) * a * a + ((2 : ℝ) / 9) * b * b := by
      nlinarith [sq_nonneg (4 * a - b)]
    nlinarith
  have hnorm : ‖qReply g h x ξ₁ ξ₂ - qDiff h f x‖ ≤
      ((4 : ℝ) / 3) * ‖cReply g h x ξ₁ - cDiff h f x‖ +
        ((1 : ℝ) / 3) * ‖cReply g (2 * h) x ξ₂ - cDiff (2 * h) f x‖ := by
    have he : qReply g h x ξ₁ ξ₂ - qDiff h f x =
        ((4 : ℝ) / 3) • (cReply g h x ξ₁ - cDiff h f x) -
          ((1 : ℝ) / 3) • (cReply g (2 * h) x ξ₂ - cDiff (2 * h) f x) := by
      unfold qReply qDiff
      rw [smul_sub, smul_sub]
      abel
    rw [he]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, norm_smul]
    norm_num
  refine haux _ _ _ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hnorm

/-- Halving the probe distance of the upper half costs a factor `4` in the denominator. -/
lemma quintic_half_scale (d : ℕ) (h σ : ℝ) (n : ℕ) :
    (d : ℝ) * σ ^ 2 / ((2 * h) ^ 2 * n) ≤ (d : ℝ) * σ ^ 2 / (h ^ 2 * n) := by
  have h4 : ((2 * h) ^ 2 * n : ℝ) = 4 * (h ^ 2 * (n : ℝ)) := by ring
  rw [h4]
  by_cases hz : (h ^ 2 * (n : ℝ)) = 0
  · rw [hz, show (4 : ℝ) * (0 : ℝ) = 0 by norm_num]
    try simp
  · have ht : (0 : ℝ) < h ^ 2 * (n : ℝ) :=
      lt_of_not_ge fun hn => hz (le_antisymm hn (by positivity))
    have hv0 : 0 ≤ (d : ℝ) * σ ^ 2 / (h ^ 2 * (n : ℝ)) := by positivity
    have heq : (d : ℝ) * σ ^ 2 / (4 * (h ^ 2 * (n : ℝ))) =
        ((1 : ℝ) / 4) * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (n : ℝ))) := by field_simp
    rw [heq]
    nlinarith

/-- Richardson bookkeeping: `(32 / 9) v + (2 / 9) v' ≤ 4 v` when `v' ≤ v` and `0 ≤ v`. -/
lemma quintic_noise_arith (v v' : ℝ) (hv : 0 ≤ v) (hle : v' ≤ v) :
    ((32 : ℝ) / 9) * v + ((2 : ℝ) / 9) * v' ≤ 4 * v := by nlinarith

/-- The lower replica half probes the stencil at bandwidth `h`. -/
lemma quadPoint_repLower {n : ℕ} (h : ℝ) (x : Point d) (t : secantSpace d n) :
    quadPoint h x (repLower t) = centralPoint h x t := by
  show centralPoint (quadBandwidth h (lowFin t.1)) x (lowFin t.1, t.2) = centralPoint h x t
  rw [quadBandwidth_lower h]
  rfl

/-- The upper replica half probes the stencil at bandwidth `2 * h`. -/
lemma quadPoint_repUpper {n : ℕ} (h : ℝ) (x : Point d) (t : secantSpace d n) :
    quadPoint h x (repUpper t) = centralPoint (2 * h) x t := by
  show centralPoint (quadBandwidth h (upFin t.1)) x (upFin t.1, t.2) = centralPoint (2 * h) x t
  rw [quadBandwidth_upper h]
  rfl

/-- The four-point decode of raw slot replies is the Richardson combination of the two central
replies of the replica halves. -/
lemma quadDecode_eq_qReply {n : ℕ} {g : Point d → Ω → ℝ} (h : ℝ) (x : Point d)
    (ξ : secantSpace d (2 * n) → Ω) :
    quadDecode h (fun t : secantSpace d (2 * n) => g (quadPoint h x t) (ξ t))
      = qReply g h x (qCellsLow ξ) (qCellsHigh ξ) := by
  classical
  have hlow : (fun t : secantSpace d n =>
      (fun s : secantSpace d (2 * n) => g (quadPoint h x s) (ξ s)) (repLower t))
      = (fun t : secantSpace d n => g (centralPoint h x t) (qCellsLow ξ t.1 t.2)) := by
    refine funext fun t => ?_
    show g (quadPoint h x (lowFin t.1, t.2)) (ξ (lowFin t.1, t.2)) = _
    have ht : quadPoint h x (lowFin t.1, t.2) = centralPoint h x t := quadPoint_repLower h x t
    rw [ht]
    rfl
  have hhigh : (fun t : secantSpace d n =>
      (fun s : secantSpace d (2 * n) => g (quadPoint h x s) (ξ s)) (repUpper t))
      = (fun t : secantSpace d n => g (centralPoint (2 * h) x t) (qCellsHigh ξ t.1 t.2)) := by
    refine funext fun t => ?_
    show g (quadPoint h x (upFin t.1, t.2)) (ξ (upFin t.1, t.2)) = _
    have ht : quadPoint h x (upFin t.1, t.2) = centralPoint (2 * h) x t := quadPoint_repUpper h x t
    rw [ht]
    rfl
  calc quadDecode h (fun t : secantSpace d (2 * n) => g (quadPoint h x t) (ξ t))
      = ((4 : ℝ) / 3) •
            centralDecode h (fun t : secantSpace d n =>
              (fun s : secantSpace d (2 * n) => g (quadPoint h x s) (ξ s)) (repLower t)) -
          ((1 : ℝ) / 3) •
            centralDecode (2 * h) (fun t : secantSpace d n =>
              (fun s : secantSpace d (2 * n) => g (quadPoint h x s) (ξ s)) (repUpper t)) :=
          rfl
    _ = ((4 : ℝ) / 3) • cReply g h x (qCellsLow ξ) -
          ((1 : ℝ) / 3) • cReply g (2 * h) x (qCellsHigh ξ) := by
          rw [hlow, hhigh, centralDecode_eq_cReply, centralDecode_eq_cReply]
    _ = qReply g h x (qCellsLow ξ) (qCellsHigh ξ) := rfl

end OracleTemplate.SecantPolyak.QuinticStencil

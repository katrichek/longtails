import LongTails.Proofs.CentralStencilEstimator
import LongTails.Proofs.CentralStencilStream
import LongTails.Proofs.ScheduledSlots
import LongTails.Proofs.CenteredMomentumStream
import LongTails.Algorithms.BetaStencilMomentumZO

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

/-!
Estimator analysis of the unified `M`-band central Richardson stencil. A round block holds
`M * n` central replicas per coordinate and the reply is the Lagrange combination
`∑ j : Fin M, betaWeight M j • centralDecode ((j + 1) * h)`, so its conditional mean is the `M`-band
secant `betaDiff` and its mean-square noise is at most `betaAbs M ^ 2 * d * σ ^ 2 / (h ^ 2 * n)`,
where `betaAbs M` is the total mass of the absolute Richardson weights. Coordinate by coordinate
`betaDiff` is the stencil whose `O (h ^ (2 * M))` bias the calling setup assumes.
-/
namespace OracleTemplate.SecantPolyak.BetaStencil

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
open OracleTemplate SecantDescent SecantPolyak ZerothOrder RobustGradient
open OracleTemplate.SecantPolyak.Centered
open OracleTemplate.SecantPolyak.CentralStencil
open OracleTemplate.Research.CubicCentralMomentumZO
open OracleTemplate.SecantPolyak.Scheduled
open OracleTemplate.Research.BetaStencilMomentumZO
open LongTails.Setups.ZerothOrderStronglyConvexBetaBias
open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {Ω : Type} [_ms : MeasurableSpace Ω] {p : Measure Ω} [_ip : IsProbabilityMeasure p]

/-- `M`-band Richardson coordinate secant: the Lagrange combination of the central secants at the
radii `h`, `2 * h`, ..., `M * h`. -/
noncomputable def betaDiff (M : ℕ) (h : ℝ) (f : Point d → ℝ) (x : Point d) : Point d :=
  ∑ j : Fin M, betaWeight M j • cDiff (((j : ℝ) + 1) * h) f x

/-- The samples of one replica band inside a block of `M * n` replicas. -/
noncomputable def betaCells {M n : ℕ} (j : Fin M) (ω : secantSpace d (M * n) → Ω) :
    Fin n → Fin d × Bool → Ω := fun i r => ω (bandFin j i, r)

/-- The `M`-band stencil reply of one block: the Lagrange combination of the band replies. -/
noncomputable def betaReply (M : ℕ) {n : ℕ} (g : Point d → Ω → ℝ) (h : ℝ) (x : Point d)
    (ξ : secantSpace d (M * n) → Ω) : Point d :=
  ∑ j : Fin M, betaWeight M j • cReply g (((j : ℝ) + 1) * h) x (betaCells j ξ)

/-- Every probe radius is positive. -/
lemma betaRadius_pos {M : ℕ} (j : Fin M) {h : ℝ} (hh : 0 < h) : 0 < ((j : ℝ) + 1) * h :=
  mul_pos (by have h1 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _; linarith) hh

lemma betaRadius_ne_zero {M : ℕ} (j : Fin M) {h : ℝ} (hh : 0 < h) : ((j : ℝ) + 1) * h ≠ 0 :=
  (betaRadius_pos (j := j) hh).ne'

/-- Coordinate form of the `M`-band secant: the Lagrange combination of the symmetric differences,
each normalized by its own radius. -/
lemma betaDiff_apply {M d : ℕ} {f : Point d → ℝ} {h : ℝ} (x : Point d) (i : Fin d) :
    (betaDiff M h f x) i =
      ∑ j : Fin M, betaWeight M j *
        ((f (x + (((j : ℝ) + 1) * h) • direction i)
            - f (x - (((j : ℝ) + 1) * h) • direction i)) / (2 * ((j : ℝ) + 1) * h)) := by
  classical
  have h1 : (betaDiff M h f x) i =
      ∑ j : Fin M, betaWeight M j *
        ((f (x + (((j : ℝ) + 1) * h) • direction i)
            - f (x - (((j : ℝ) + 1) * h) • direction i)) / (2 * (((j : ℝ) + 1) * h))) := by
    show (∑ j : Fin M, betaWeight M j • cDiff (((j : ℝ) + 1) * h) f x) i = _
    simp [Finset.sum_apply, Pi.smul_apply, cDiff_apply]
  rw [h1]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The `M`-band secant is within `beta` of the gradient in every coordinate, so its squared error
is at most `d * beta ^ 2`. -/
lemma betaDiff_bias_sq {M d : ℕ} {f : Point d → ℝ} {h β : ℝ}
    (hcb : ∀ (x v : Point d), ‖v‖ = 1 →
      |∑ j : Fin M, betaWeight M j *
          ((f (x + (((j : ℝ) + 1) * h) • v) - f (x - (((j : ℝ) + 1) * h) • v))
            / (2 * ((j : ℝ) + 1) * h)) - ⟪gradient f x, v⟫| ≤ β)
    (x : Point d) : ‖betaDiff M h f x - gradient f x‖ ^ 2 ≤ (d : ℝ) * β ^ 2 := by
  classical
  have hcoord (i : Fin d) : |(betaDiff M h f x) i - gradient f x i| ≤ β := by
    have h1 := hcb x (direction i) (direction_norm i)
    have hi : ⟪gradient f x, direction i⟫ = gradient f x i :=
      EuclideanSpace.inner_basisFun_real (Fin d) (gradient f x) i
    rw [betaDiff_apply, ← hi]
    exact h1
  have hbound (i : Fin d) : (betaDiff M h f x - gradient f x).ofLp i ^ 2 ≤ β ^ 2 := by
    have h2 : (betaDiff M h f x - gradient f x).ofLp i =
        (betaDiff M h f x) i - gradient f x i := rfl
    rw [h2]
    have h3 := abs_mul_abs_self ((betaDiff M h f x) i - gradient f x i)
    nlinarith [hcoord i, abs_nonneg ((betaDiff M h f x) i - gradient f x i), h3]
  have hcard : (∑ _i : Fin d, β ^ 2) = (d : ℝ) * β ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ,
      smul_eq_mul]
  rw [EuclideanSpace.real_norm_sq_eq]
  calc (∑ i : Fin d, (betaDiff M h f x - gradient f x).ofLp i ^ 2)
      ≤ ∑ _i : Fin d, β ^ 2 := Finset.sum_le_sum (fun i _ => hbound i)
    _ = (d : ℝ) * β ^ 2 := hcard

/-- The band embedding is injective. -/
lemma bandFin_injective {M n : ℕ} (j : Fin M) : Function.Injective (bandFin (n := n) j) := by
  intro a b hab
  have hv := congrArg (fun v : Fin (M * n) => (v : ℕ)) hab
  simp only [bandFin_val] at hv
  exact Fin.eq_of_val_eq (Nat.add_left_cancel hv)

/-- Currying identifies the product measure on cells with a batch law. -/
lemma measure_map_curry_cells {d n : ℕ} :
    Measure.map (MeasurableEquiv.curry (Fin n) (Fin d × Bool) Ω)
      (Measure.pi (fun _ : Fin n × (Fin d × Bool) => p)) = batchLaw d n p := by
  have h2 := Measure.infinitePi_map_curry (fun (_ : Fin n) (_ : Fin d × Bool) => p)
  simpa [Measure.infinitePi_eq_pi, batchLaw, cellLaw] using h2

/-- The samples of one replica band are measurable. -/
lemma measurable_betaCells {M n : ℕ} (j : Fin M) :
    Measurable (fun ω : secantSpace d (M * n) → Ω => betaCells j ω) := by
  classical
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun r => ?_
  exact measurable_pi_apply (bandFin j i, r)

/-- One replica band of a block is an independent batch. -/
lemma measurePreserving_betaCells {M n : ℕ} (j : Fin M) :
    MeasurePreserving (fun ω : secantSpace d (M * n) → Ω => betaCells j ω)
      (slotLaw d (M * n) p) (batchLaw d n p) := by
  classical
  refine ⟨measurable_betaCells j, ?_⟩
  have hin : Function.Injective (fun t : Fin n × (Fin d × Bool) => (bandFin j t.1, t.2)) := by
    intro a b hab
    have hv := congrArg (fun v : Fin (M * n) × (Fin d × Bool) => (v.1 : ℕ)) hab
    simp only [bandFin_val] at hv
    exact Prod.ext (Fin.eq_of_val_eq (Nat.add_left_cancel hv))
      (by simpa using congrArg Prod.snd hab)
  have h1 : Measure.map (fun ω : Fin (M * n) × (Fin d × Bool) → Ω =>
      fun t : Fin n × (Fin d × Bool) => ω (bandFin j t.1, t.2)) (slotLaw d (M * n) p) =
      Measure.pi (fun _ : Fin n × (Fin d × Bool) => p) := by
    have := Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : Fin (M * n) × (Fin d × Bool) => p) hin
    simpa [slotLaw, Measure.infinitePi_eq_pi] using this
  have hcomp : (fun ω : Fin (M * n) × (Fin d × Bool) → Ω => betaCells j ω) =
      (fun ξ : Fin n × (Fin d × Bool) → Ω =>
        MeasurableEquiv.curry (Fin n) (Fin d × Bool) Ω ξ) ∘
        (fun ω : Fin (M * n) × (Fin d × Bool) → Ω =>
          fun t : Fin n × (Fin d × Bool) => ω (bandFin j t.1, t.2)) := by
    funext ω j' r
    rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), h1]
  exact measure_map_curry_cells

/-- One replica band of the slot block of a scheduled round is an independent batch. -/
lemma measurePreserving_betaCells_ambient {M n N : ℕ} (hnN : M * n ≤ N) (j : Fin M) :
    MeasurePreserving (fun ω : secantSpace d N → Ω =>
        betaCells j (fun t : secantSpace d (M * n) => ω (cellInj hnN t)))
      (slotLaw d N p) (batchLaw d n p) := by
  classical
  have h1 : MeasurePreserving (fun ω : secantSpace d N → Ω =>
      fun t : secantSpace d (M * n) => ω (cellInj hnN t)) (slotLaw d N p) (slotLaw d (M * n) p) :=
    measurePreserving_cellInj (d := d) (hM := hnN)
  have h2 : MeasurePreserving (fun ω : secantSpace d (M * n) → Ω => betaCells j ω)
      (slotLaw d (M * n) p) (batchLaw d n p) := measurePreserving_betaCells (M := M) (j := j)
  refine ⟨h2.1.comp h1.1, ?_⟩
  have h10 : Measure.map (fun ω : secantSpace d (M * n) → Ω => betaCells j ω)
      (Measure.map (fun ω : secantSpace d N → Ω =>
        fun t : secantSpace d (M * n) => ω (cellInj hnN t)) (slotLaw d N p)) = batchLaw d n p := by
    rw [h1.2]
    exact h2.2
  rw [Measure.map_map h2.1 h1.1] at h10
  exact h10

/-- Cauchy-Schwarz for a finite weighted sum in a real seminormed group. -/
lemma beta_cs {V : Type} [SeminormedAddCommGroup V] [NormedSpace ℝ V] {ι : Type}
    (s : Finset ι) (w : ι → ℝ) (u : ι → V) :
    ‖∑ i ∈ s, w i • u i‖ ^ 2 ≤ (∑ i ∈ s, |w i|) * (∑ i ∈ s, |w i| * ‖u i‖ ^ 2) := by
  have h1 : ‖∑ i ∈ s, w i • u i‖ ≤ ∑ i ∈ s, ‖w i • u i‖ := norm_sum_le s _
  have h2 : (∑ i ∈ s, ‖w i • u i‖) ≤ ∑ i ∈ s, |w i| * ‖u i‖ :=
    Finset.sum_le_sum fun i _ => by
      rw [norm_smul, Real.norm_eq_abs]
  have h3 : (∑ i ∈ s, |w i| * ‖u i‖) =
      ∑ i ∈ s, Real.sqrt (|w i|) * (Real.sqrt (|w i|) * ‖u i‖) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    calc |w i| * ‖u i‖ = (Real.sqrt (|w i|) * Real.sqrt (|w i|)) * ‖u i‖ := by
          rw [Real.mul_self_sqrt (abs_nonneg _)]
      _ = Real.sqrt (|w i|) * (Real.sqrt (|w i|) * ‖u i‖) := by ring
  have hcs : (∑ i ∈ s, Real.sqrt (|w i|) * (Real.sqrt (|w i|) * ‖u i‖)) ^ 2 ≤
      (∑ i ∈ s, (Real.sqrt (|w i|)) ^ 2) *
        (∑ i ∈ s, (Real.sqrt (|w i|) * ‖u i‖) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq s _ _
  have hA : (∑ i ∈ s, (Real.sqrt (|w i|)) ^ 2) = ∑ i ∈ s, |w i| := by
    refine Finset.sum_congr rfl fun i _ => Real.sq_sqrt (abs_nonneg _)
  have hB : (∑ i ∈ s, (Real.sqrt (|w i|) * ‖u i‖) ^ 2) = ∑ i ∈ s, |w i| * ‖u i‖ ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow, Real.sq_sqrt (abs_nonneg _)]
  calc ‖∑ i ∈ s, w i • u i‖ ^ 2 ≤ (∑ i ∈ s, ‖w i • u i‖) ^ 2 := by gcongr
    _ ≤ (∑ i ∈ s, |w i| * ‖u i‖) ^ 2 := by gcongr
    _ = (∑ i ∈ s, Real.sqrt (|w i|) * (Real.sqrt (|w i|) * ‖u i‖)) ^ 2 := by rw [h3]
    _ ≤ (∑ i ∈ s, (Real.sqrt (|w i|)) ^ 2) *
        (∑ i ∈ s, (Real.sqrt (|w i|) * ‖u i‖) ^ 2) := hcs
    _ = (∑ i ∈ s, |w i|) * (∑ i ∈ s, |w i| * ‖u i‖ ^ 2) := by rw [hA, hB]

/-- Widening the stencil bandwidth by a factor `(j + 1)` only reduces the batch variance. -/
lemma beta_band_scale (d : ℕ) (h σ : ℝ) (n : ℕ) (j : ℕ) :
    (d : ℝ) * σ ^ 2 / ((((j : ℝ) + 1) * h) ^ 2 * (n : ℝ)) ≤
      (d : ℝ) * σ ^ 2 / (h ^ 2 * (n : ℝ)) := by
  have h1 : (((j : ℝ) + 1) * h) ^ 2 * (n : ℝ) = ((j : ℝ) + 1) ^ 2 * (h ^ 2 * (n : ℝ)) := by ring
  rw [h1]
  have h2 : (1 : ℝ) ≤ ((j : ℝ) + 1) ^ 2 := by
    have h3 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
    nlinarith
  by_cases hz : h ^ 2 * (n : ℝ) = 0
  · rw [hz, mul_zero]
  · have hc : ((j : ℝ) + 1) ^ 2 ≠ 0 := by positivity
    have hcb : ((j : ℝ) + 1) ^ 2 * (h ^ 2 * (n : ℝ)) ≠ 0 := mul_ne_zero hc hz
    have h7 : (d : ℝ) * σ ^ 2 / (((j : ℝ) + 1) ^ 2 * (h ^ 2 * (n : ℝ)))
        = ((d : ℝ) * σ ^ 2 / (h ^ 2 * (n : ℝ))) / ((j : ℝ) + 1) ^ 2 := by
      field_simp [hz, hc, hcb]
    rw [h7]
    exact div_le_self (by positivity) h2

/-- Pointwise squared error of the `M`-band reply: weighted Cauchy-Schwarz over the bands. -/
lemma betaReply_pointwise {M n : ℕ} {g : Point d → Ω → ℝ} {f : Point d → ℝ} {h : ℝ} (x : Point d)
    (ξ : secantSpace d (M * n) → Ω) :
    ‖betaReply M g h x ξ - betaDiff M h f x‖ ^ 2 ≤
      betaAbs M *
        ∑ j : Fin M, |betaWeight M j| *
          ‖cReply g (((j : ℝ) + 1) * h) x (betaCells j ξ) - cDiff (((j : ℝ) + 1) * h) f x‖ ^ 2 := by
  classical
  have he : betaReply M g h x ξ - betaDiff M h f x =
      ∑ j : Fin M, betaWeight M j •
        (cReply g (((j : ℝ) + 1) * h) x (betaCells j ξ) - cDiff (((j : ℝ) + 1) * h) f x) := by
    show (∑ j : Fin M, betaWeight M j • cReply g (((j : ℝ) + 1) * h) x (betaCells j ξ)) -
        (∑ j : Fin M, betaWeight M j • cDiff (((j : ℝ) + 1) * h) f x) = _
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => (smul_sub _ _ _).symm
  have hcs := beta_cs (Finset.univ : Finset (Fin M)) (betaWeight M)
    (fun j : Fin M => cReply g (((j : ℝ) + 1) * h) x (betaCells j ξ) -
      cDiff (((j : ℝ) + 1) * h) f x)
  calc ‖betaReply M g h x ξ - betaDiff M h f x‖ ^ 2
      = ‖∑ j : Fin M, betaWeight M j •
          (cReply g (((j : ℝ) + 1) * h) x (betaCells j ξ) - cDiff (((j : ℝ) + 1) * h) f x)‖ ^ 2 := by
        rw [he]
    _ ≤ (∑ j : Fin M, |betaWeight M j|) *
          ∑ j : Fin M, |betaWeight M j| *
            ‖cReply g (((j : ℝ) + 1) * h) x (betaCells j ξ) - cDiff (((j : ℝ) + 1) * h) f x‖ ^ 2 :=
        hcs
    _ = betaAbs M *
          ∑ j : Fin M, |betaWeight M j| *
            ‖cReply g (((j : ℝ) + 1) * h) x (betaCells j ξ) - cDiff (((j : ℝ) + 1) * h) f x‖ ^ 2 :=
        rfl

lemma betaReply_measurable {M n : ℕ} {g : Point d → Ω → ℝ}
    (hg : Measurable (Function.uncurry g)) (h : ℝ) (x : Point d) :
    Measurable (fun ξ : secantSpace d (M * n) → Ω => betaReply M g h x ξ) := by
  classical
  refine Finset.measurable_sum Finset.univ fun j _ =>
    smul_measurable measurable_const ?_
  exact (measurable_cReply_at hg (((j : ℝ) + 1) * h) x).comp (measurable_betaCells j)

/-- Mean-square noise of the `M`-band reply of one block: the weights contribute the factor
`betaAbs M ^ 2`, and the larger band radii only reduce the variance. -/
lemma betaReply_deviation {M n : ℕ} {g : Point d → Ω → ℝ} {f : Point d → ℝ} {σ h : ℝ}
    (hg : Measurable (Function.uncurry g))
    (hgi : ∀ x, Integrable (g x) p)
    (hmean : ∀ x, (∫ ω, g x ω ∂p) = f x)
    (hvi : ∀ x, Integrable (fun ω => (g x ω - f x) ^ 2) p)
    (hv : ∀ x, (∫ ω, (g x ω - f x) ^ 2 ∂p) ≤ σ ^ 2)
    (hm : 0 < n) (x : Point d) :
    Integrable (fun ξ : secantSpace d (M * n) → Ω =>
        ‖betaReply M g h x ξ - betaDiff M h f x‖ ^ 2) (slotLaw d (M * n) p) ∧
      (∫ ξ : secantSpace d (M * n) → Ω, ‖betaReply M g h x ξ - betaDiff M h f x‖ ^ 2
          ∂(slotLaw d (M * n) p))
        ≤ betaAbs M ^ 2 * ((d : ℝ) * σ ^ 2 / (h ^ 2 * n)) := by
  classical
  set F : Fin M → ((secantSpace d (M * n) → Ω) → ℝ) := fun j => fun ξ =>
    ‖cReply g (((j : ℝ) + 1) * h) x (betaCells j ξ) - cDiff (((j : ℝ) + 1) * h) f x‖ ^ 2 with hFdef
  have hFmeas (j : Fin M) : Measurable (F j) := by
    have h1 : Measurable (fun ξ : secantSpace d (M * n) → Ω =>
        cReply g (((j : ℝ) + 1) * h) x (betaCells j ξ)) :=
      (measurable_cReply_at hg (((j : ℝ) + 1) * h) x).comp (measurable_betaCells j)
    have h2 : Measurable (fun _ : secantSpace d (M * n) → Ω =>
        cDiff (((j : ℝ) + 1) * h) f x) := measurable_const
    show Measurable (fun ξ => ‖cReply g (((j : ℝ) + 1) * h) x (betaCells j ξ) -
        cDiff (((j : ℝ) + 1) * h) f x‖ ^ 2)
    exact ((h1.sub h2).norm).pow_const 2
  have hD (j : Fin M) :
      Integrable (fun η : Fin n → Fin d × Bool → Ω =>
          ‖cReply g (((j : ℝ) + 1) * h) x η - cDiff (((j : ℝ) + 1) * h) f x‖ ^ 2)
          (batchLaw d n p) ∧
        (∫ η : Fin n → Fin d × Bool → Ω,
            ‖cReply g (((j : ℝ) + 1) * h) x η - cDiff (((j : ℝ) + 1) * h) f x‖ ^ 2 ∂(batchLaw d n p))
          ≤ (d : ℝ) * σ ^ 2 / ((((j : ℝ) + 1) * h) ^ 2 * n) :=
    cReply_deviation (d := d) (m := n) (g := g) (h := ((j : ℝ) + 1) * h) hg hgi hmean hvi hv hm x
  have hp (j : Fin M) : MeasurePreserving (fun ξ : secantSpace d (M * n) → Ω => betaCells j ξ)
      (slotLaw d (M * n) p) (batchLaw d n p) := measurePreserving_betaCells j
  have hFi (j : Fin M) : Integrable (F j) (slotLaw d (M * n) p) :=
    (hp j).integrable_comp_of_integrable (ε := ℝ) (hD j).1
  have hFb (j : Fin M) : (∫ ξ : secantSpace d (M * n) → Ω, F j ξ ∂(slotLaw d (M * n) p))
      ≤ (d : ℝ) * σ ^ 2 / (h ^ 2 * n) :=
    ((integral_comp_preserving (hp j) (hD j).1).trans_le (hD j).2).trans
      (beta_band_scale d h σ n j.1)
  have hsum0 : Integrable (fun ξ : secantSpace d (M * n) → Ω =>
      ∑ j : Fin M, |betaWeight M j| * F j ξ) (slotLaw d (M * n) p) :=
    integrable_finsetSum Finset.univ fun j _ => (hFi j).const_mul (|betaWeight M j|)
  have hsumi : Integrable (fun ξ : secantSpace d (M * n) → Ω =>
      betaAbs M * ∑ j : Fin M, |betaWeight M j| * F j ξ) (slotLaw d (M * n) p) :=
    hsum0.const_mul (betaAbs M)
  have hZms : Measurable (fun ξ : secantSpace d (M * n) → Ω =>
      ‖betaReply M g h x ξ - betaDiff M h f x‖ ^ 2) :=
    ((betaReply_measurable hg h x).sub_const (betaDiff M h f x)).norm.pow_const 2
  have hZm : AEStronglyMeasurable (fun ξ : secantSpace d (M * n) → Ω =>
      ‖betaReply M g h x ξ - betaDiff M h f x‖ ^ 2) (slotLaw d (M * n) p) :=
    hZms.aestronglyMeasurable
  have hZi : Integrable (fun ξ : secantSpace d (M * n) → Ω =>
      ‖betaReply M g h x ξ - betaDiff M h f x‖ ^ 2) (slotLaw d (M * n) p) := by
    refine hsumi.mono hZm (ae_of_all _ fun ξ => ?_)
    have hb := betaReply_pointwise (M := M) (n := n) (g := g) (f := f) (h := h) x ξ
    have hM : 0 ≤ betaAbs M * ∑ j : Fin M, |betaWeight M j| * F j ξ := by
      refine mul_nonneg (betaAbs_nonneg M)
        (Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), abs_of_nonneg hM]
    exact hb
  refine ⟨hZi, ?_⟩
  calc (∫ ξ : secantSpace d (M * n) → Ω, ‖betaReply M g h x ξ - betaDiff M h f x‖ ^ 2
        ∂(slotLaw d (M * n) p))
      ≤ ∫ ξ : secantSpace d (M * n) → Ω,
          betaAbs M * ∑ j : Fin M, |betaWeight M j| * F j ξ ∂(slotLaw d (M * n) p) :=
        integral_mono hZi hsumi (fun ξ =>
          betaReply_pointwise (M := M) (n := n) (g := g) (f := f) (h := h) x ξ)
    _ = betaAbs M * ∑ j : Fin M, |betaWeight M j| *
        (∫ ξ : secantSpace d (M * n) → Ω, F j ξ ∂(slotLaw d (M * n) p)) := by
        rw [integral_const_mul (μ := slotLaw d (M * n) p) (betaAbs M)
            (fun ξ : secantSpace d (M * n) → Ω => ∑ j : Fin M, |betaWeight M j| * F j ξ),
          integral_finsetSum Finset.univ (fun j _ => (hFi j).const_mul (|betaWeight M j|))]
        congr 1
        refine Finset.sum_congr rfl fun j _ =>
          integral_const_mul (μ := slotLaw d (M * n) p) (|betaWeight M j|) (F j)
    _ ≤ betaAbs M * ∑ j : Fin M, |betaWeight M j| * ((d : ℝ) * σ ^ 2 / (h ^ 2 * n)) := by
        refine mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hFb j) (abs_nonneg _))
          (betaAbs_nonneg M)
    _ = betaAbs M * (betaAbs M * ((d : ℝ) * σ ^ 2 / (h ^ 2 * n))) := by
        rw [← Finset.sum_mul]
        simp only [betaAbs]
    _ = betaAbs M ^ 2 * ((d : ℝ) * σ ^ 2 / (h ^ 2 * n)) := by
        show betaAbs M * (betaAbs M * _) = _
        ring

/-- Mean of the `M`-band reply of one block is the `M`-band secant. -/
lemma betaReply_mean {M n : ℕ} {g : Point d → Ω → ℝ} {f : Point d → ℝ} {h : ℝ}
    (hgi : ∀ x, Integrable (g x) p)
    (hmean : ∀ x, (∫ ω, g x ω ∂p) = f x)
    (hm : 0 < n) (x : Point d) :
    (∫ ξ : secantSpace d (M * n) → Ω, betaReply M g h x ξ ∂(slotLaw d (M * n) p))
      = betaDiff M h f x := by
  classical
  have hc (j : Fin M) : Integrable (cReply g (((j : ℝ) + 1) * h) x) (batchLaw d n p) :=
    cReply_integrable hgi hmean hm x
  have hp (j : Fin M) : MeasurePreserving (fun ξ : secantSpace d (M * n) → Ω => betaCells j ξ)
      (slotLaw d (M * n) p) (batchLaw d n p) := measurePreserving_betaCells j
  have hi (j : Fin M) : Integrable (fun ξ : secantSpace d (M * n) → Ω =>
      cReply g (((j : ℝ) + 1) * h) x (betaCells j ξ)) (slotLaw d (M * n) p) :=
    (hp j).integrable_comp_of_integrable (ε := Point d) (hc j)
  have hI : (∫ ξ : secantSpace d (M * n) → Ω, betaReply M g h x ξ ∂(slotLaw d (M * n) p))
      = ∑ j : Fin M, betaWeight M j •
        (∫ ξ : secantSpace d (M * n) → Ω,
          cReply g (((j : ℝ) + 1) * h) x (betaCells j ξ) ∂(slotLaw d (M * n) p)) := by
    classical
    set B : Fin M → ((secantSpace d (M * n) → Ω) → Point d) := fun j ξ =>
      betaWeight M j • cReply g (((j : ℝ) + 1) * h) x (betaCells j ξ) with hBdef
    have hb (j : Fin M) : Integrable (B j) (slotLaw d (M * n) p) := (hi j).smul (betaWeight M j)
    have h2 : (∫ ξ : secantSpace d (M * n) → Ω, ∑ j : Fin M, B j ξ ∂(slotLaw d (M * n) p))
        = ∑ j : Fin M, ∫ ξ : secantSpace d (M * n) → Ω, B j ξ ∂(slotLaw d (M * n) p) :=
      integral_finsetSum Finset.univ (fun j _ => hb j)
    calc (∫ ξ : secantSpace d (M * n) → Ω, betaReply M g h x ξ ∂(slotLaw d (M * n) p))
        = ∫ ξ : secantSpace d (M * n) → Ω, ∑ j : Fin M, B j ξ ∂(slotLaw d (M * n) p) :=
          integral_congr_ae (ae_of_all _ fun _ => rfl)
      _ = ∑ j : Fin M, ∫ ξ : secantSpace d (M * n) → Ω, B j ξ ∂(slotLaw d (M * n) p) := h2
      _ = ∑ j : Fin M, betaWeight M j •
          (∫ ξ : secantSpace d (M * n) → Ω,
            cReply g (((j : ℝ) + 1) * h) x (betaCells j ξ) ∂(slotLaw d (M * n) p)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          show ∫ ξ : secantSpace d (M * n) → Ω,
              betaWeight M j • cReply g (((j : ℝ) + 1) * h) x (betaCells j ξ)
              ∂(slotLaw d (M * n) p)
            = betaWeight M j •
              (∫ ξ : secantSpace d (M * n) → Ω,
                cReply g (((j : ℝ) + 1) * h) x (betaCells j ξ) ∂(slotLaw d (M * n) p))
          rw [integral_smul]
  have he (j : Fin M) : (∫ η : Fin n → Fin d × Bool → Ω,
      cReply g (((j : ℝ) + 1) * h) x η ∂(batchLaw d n p)) = cDiff (((j : ℝ) + 1) * h) f x :=
    cReply_mean (d := d) (m := n) (g := g) (f := f) (h := ((j : ℝ) + 1) * h) hgi hmean hm x
  rw [hI]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_comp_preserving_point (hp j) (hc j), he j]

/-- The `M`-band reply of one block is integrable. -/
lemma betaReply_integrable {M n : ℕ} {g : Point d → Ω → ℝ} {f : Point d → ℝ} {h : ℝ}
    (hgi : ∀ x, Integrable (g x) p) (hmean : ∀ x, (∫ ω, g x ω ∂p) = f x)
    (hm : 0 < n) (x : Point d) : Integrable (betaReply M g h x) (slotLaw d (M * n) p) := by
  classical
  have hc (j : Fin M) : Integrable (cReply g (((j : ℝ) + 1) * h) x) (batchLaw d n p) :=
    cReply_integrable hgi hmean hm x
  have hp (j : Fin M) : MeasurePreserving (fun ξ : secantSpace d (M * n) → Ω => betaCells j ξ)
      (slotLaw d (M * n) p) (batchLaw d n p) := measurePreserving_betaCells j
  have hi (j : Fin M) : Integrable (fun ξ : secantSpace d (M * n) → Ω =>
      cReply g (((j : ℝ) + 1) * h) x (betaCells j ξ)) (slotLaw d (M * n) p) :=
    (hp j).integrable_comp_of_integrable (ε := Point d) (hc j)
  show Integrable (fun ξ : secantSpace d (M * n) → Ω =>
      ∑ j : Fin M, betaWeight M j • cReply g (((j : ℝ) + 1) * h) x (betaCells j ξ))
      (slotLaw d (M * n) p)
  exact integrable_finsetSum Finset.univ (fun j _ => (hi j).smul (betaWeight M j))

/-- The band probe of a block slot is the symmetric difference probe at radius `(j + 1) * h`. -/
lemma betaPoint_band {M n : ℕ} (h : ℝ) (x : Point d) (j : Fin M) (t : secantSpace d n) :
    betaPoint h x (betaRep j t) = centralPoint (((j : ℝ) + 1) * h) x t := by
  show centralPoint (betaBandwidth h (bandFin j t.1)) x (bandFin j t.1, t.2) = _
  rw [betaBandwidth_band]
  cases t with
  | mk r s => rfl

/-- The executed `M`-band decoder is the `M`-band reply of the block. -/
lemma betaDecode_eq_betaReply {M n : ℕ} {g : Point d → Ω → ℝ} (h : ℝ) (x : Point d)
    (ξ : secantSpace d (M * n) → Ω) :
    betaDecode h (fun t : secantSpace d (M * n) => g (betaPoint h x t) (ξ t))
      = betaReply M g h x ξ := by
  classical
  unfold betaDecode betaReply
  refine Finset.sum_congr rfl fun j _ => congrArg (fun v : Point d => betaWeight M j • v) ?_
  have h1 : (fun t : secantSpace d n =>
      (fun s : secantSpace d (M * n) => g (betaPoint h x s) (ξ s)) (betaRep j t))
      = (fun t : secantSpace d n =>
        g (centralPoint (((j : ℝ) + 1) * h) x t) (betaCells j ξ t.1 t.2)) := by
    refine funext fun t => congrArg₂ g (betaPoint_band h x j t) ?_
    show ξ (betaRep j t) = betaCells j ξ t.1 t.2
    rfl
  rw [h1, centralDecode_eq_cReply]

end OracleTemplate.SecantPolyak.BetaStencil

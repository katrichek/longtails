import LongTails.Proofs.ZerothOrderEstimator
import LongTails.Proofs.FiniteVarianceBatch

/-!
One batched secant reply: the average of `m` independent replicas of the coordinate
one-sided difference estimator. Its mean square error against the true gradient is the
averaged noise term `8 * d * σ ^ 2 / (h ^ 2 * m)` plus the bandwidth bias term.
-/

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.SecantPolyak

open ZerothOrder RobustGradient LongTails.Setups.ZerothOrderSmoothAndConvex

variable {Ω : Type*} [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]

/-- One replica of the coordinate secant estimator: a pair of value samples per coordinate. -/
@[reducible] noncomputable def cellLaw (d : ℕ) (q : Measure Ω) : Measure (Fin d × Bool → Ω) :=
  Measure.pi fun _ : Fin d × Bool => q

/-- One batch of `m` independent replicas. -/
@[reducible] noncomputable def batchLaw (d m : ℕ) (q : Measure Ω) : Measure (Fin m → Fin d × Bool → Ω) :=
  Measure.pi fun _ : Fin m => cellLaw d q

instance cellLaw_isProbability {d : ℕ} : IsProbabilityMeasure (cellLaw d p) := by
  unfold cellLaw
  infer_instance

instance batchLaw_isProbability {d m : ℕ} : IsProbabilityMeasure (batchLaw d m p) := by
  unfold batchLaw
  infer_instance

/-- Replicated secant reply. -/
noncomputable def reply {d m : ℕ} (g : Point d → Ω → ℝ) (h : ℝ) (x : Point d)
    (ξ : Fin m → Fin d × Bool → Ω) : Point d :=
  (1 / (m : ℝ)) • ∑ r : Fin m, estimate g h x (ξ r)

lemma smul_measurable {α : Type*} [MeasurableSpace α] {f : α → ℝ} {v : α → Point d}
    (hf : Measurable f) (hv : Measurable v) : Measurable (fun a => f a • v a) :=
  (continuous_smul (M := ℝ) (X := Point d)).measurable.comp (hf.prodMk hv)

lemma cell_preserving {d : ℕ} (j : Fin d × Bool) :
    MeasurePreserving (fun ξ : Fin d × Bool → Ω => ξ j) (cellLaw d p) p := by
  unfold cellLaw
  exact measurePreserving_eval _ j

lemma batch_preserving {d m : ℕ} (r : Fin m) (j : Fin d × Bool) :
    MeasurePreserving (fun ξ : Fin m → Fin d × Bool → Ω => ξ r j) (batchLaw d m p) p := by
  refine MeasurePreserving.comp (hg := cell_preserving j) ?_
  unfold batchLaw
  exact measurePreserving_eval (fun _ : Fin m => cellLaw d p) r

/-- The coordinate secant estimator is measurable in its sample argument. -/
lemma estimate_measurable {d : ℕ} {g : Point d → Ω → ℝ}
    (hg : Measurable (Function.uncurry g)) (h : ℝ) (x : Point d) :
    Measurable (fun ξ : Fin d × Bool → Ω => estimate g h x ξ) := by
  classical
  unfold estimate
  refine Finset.measurable_sum Finset.univ fun i _ => ?_
  have h1 : Measurable (fun ξ : Fin d × Bool → Ω => g (x + h • direction i) (ξ (i, true))) :=
    hg.comp (measurable_const.prodMk (measurable_pi_apply (i, true)))
  have h2 : Measurable (fun ξ : Fin d × Bool → Ω => g x (ξ (i, false))) :=
    hg.comp (measurable_const.prodMk (measurable_pi_apply (i, false)))
  exact smul_measurable ((h1.sub h2).div_const h) measurable_const

lemma reply_measurable {d m : ℕ} {g : Point d → Ω → ℝ}
    (hg : Measurable (Function.uncurry g)) (h : ℝ) (x : Point d) :
    Measurable (fun ξ : Fin m → Fin d × Bool → Ω => reply (g := g) h x ξ) := by
  classical
  have hs : Measurable (fun ξ : Fin m → Fin d × Bool → Ω =>
      ∑ r : Fin m, estimate g h x (ξ r)) :=
    Finset.measurable_sum Finset.univ fun r _ =>
      (estimate_measurable hg h x).comp (measurable_pi_apply r)
  exact smul_measurable measurable_const hs

/-- Deviation of the replicated reply from the grid difference: `m` replicas divide the
single-replica mean square deviation by `m`. -/
lemma reply_deviation {d m : ℕ} {g : Point d → Ω → ℝ} {f : Point d → ℝ} {σ h : ℝ}
    (hg : Measurable (Function.uncurry g))
    (hgi : ∀ x, Integrable (g x) p)
    (hmean : ∀ x, (∫ ω, g x ω ∂p) = f x)
    (hvi : ∀ x, Integrable (fun ω => (g x ω - f x) ^ 2) p)
    (hv : ∀ x, (∫ ω, (g x ω - f x) ^ 2 ∂p) ≤ σ ^ 2)
    (hm : 0 < m) (x : Point d) :
    Integrable (fun ξ : Fin m → Fin d × Bool → Ω => ‖reply (g := g) h x ξ - difference h x f‖ ^ 2)
        (batchLaw d m p) ∧
      (∫ ξ : Fin m → Fin d × Bool → Ω, ‖reply (g := g) h x ξ - difference h x f‖ ^ 2
        ∂(batchLaw d m p)) ≤ 4 * (d : ℝ) * σ ^ 2 / (h ^ 2 * m) := by
  classical
  let X := fun η : Fin d × Bool → Ω => estimate (g := g) h x η - difference h x f
  have hXe (ξ : Fin m → Fin d × Bool → Ω) : reply (g := g) h x ξ - difference h x f
      = (1 / (m : ℝ)) • ∑ r : Fin m, X (ξ r) := by
    unfold reply X
    rw [← finite_mean_centered (u := difference h x f) m hm]
  have hXm : Measurable X := (estimate_measurable hg h x).sub measurable_const
  have hEst := estimate_integral cell_preserving hgi hmean h x
  have hXi : Integrable X (cellLaw d p) := hEst.1.sub (integrable_const _)
  have hX0 : (∫ η, X η ∂(cellLaw d p)) = 0 := by
    rw [integral_sub hEst.1 (integrable_const _), hEst.2]
    simp
  have hX2 := estimate_variance cell_preserving hgi hvi hv h x
  obtain ⟨hIi, hI⟩ := finite_mean_second_moment hXm hXi hX2.1 hX0 m hm
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  refine ⟨hIi.congr (ae_of_all _ fun ξ =>
      (congrArg (fun v : Point d => ‖v‖ ^ 2) (hXe ξ)).symm), ?_⟩
  calc (∫ ξ : Fin m → Fin d × Bool → Ω, ‖reply (g := g) h x ξ - difference h x f‖ ^ 2
        ∂(batchLaw d m p))
      = ∫ ξ : Fin m → Fin d × Bool → Ω, ‖(1 / (m : ℝ)) • ∑ r : Fin m, X (ξ r)‖ ^ 2
        ∂(batchLaw d m p) := by
          refine integral_congr_ae ?_
          exact ae_of_all _ (fun ξ => congrArg (fun v : Point d => ‖v‖ ^ 2) (hXe ξ))
    _ = (∫ η, ‖X η‖ ^ 2 ∂(cellLaw d p)) / m := hI
    _ ≤ (4 * (d : ℝ) * σ ^ 2 / h ^ 2) / m := (div_le_div_of_nonneg_right hX2.2 (le_of_lt hm'))
    _ = 4 * (d : ℝ) * σ ^ 2 / (h ^ 2 * m) := by
        simp only [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]

/-- Mean square error of the replicated secant reply against the true gradient. -/
lemma reply_error_moment {d m : ℕ} {g : Point d → Ω → ℝ} {f : Point d → ℝ} {σ L h : ℝ}
    (hh : 0 < h) (hg : Measurable (Function.uncurry g))
    (hgi : ∀ x, Integrable (g x) p)
    (hmean : ∀ x, (∫ ω, g x ω ∂p) = f x)
    (hvi : ∀ x, Integrable (fun ω => (g x ω - f x) ^ 2) p)
    (hv : ∀ x, (∫ ω, (g x ω - f x) ^ 2 ∂p) ≤ σ ^ 2)
    (hc : ConvexOn ℝ Set.univ f)
    (hgr : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hm : 0 < m) (x : Point d) :
    (∫ ξ : Fin m → Fin d × Bool → Ω, ‖reply (g := g) h x ξ - gradient f x‖ ^ 2
        ∂(batchLaw d m p)) ≤
        8 * (d : ℝ) * σ ^ 2 / (h ^ 2 * m) + 2 * ((d : ℝ) * (L * h / 2) ^ 2) := by
  classical
  have hB := reply_deviation (h := h) hg hgi hmean hvi hv hm x
  have hb := difference_bias_sq hh hc hgr hlip x
  have hsq {a b : Point d} : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
    calc ‖a + b‖ ^ 2 = ‖a + b‖ * ‖a + b‖ := by ring
      _ ≤ (‖a‖ + ‖b‖) * (‖a‖ + ‖b‖) := by
          nlinarith [norm_add_le a b, norm_nonneg (a + b), norm_nonneg a, norm_nonneg b]
      _ ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
          have h : (‖a‖ + ‖b‖) * (‖a‖ + ‖b‖) = ‖a‖ ^ 2 + 2 * ‖a‖ * ‖b‖ + ‖b‖ ^ 2 := by ring
          rw [h]
          nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  have hpt (ξ : Fin m → Fin d × Bool → Ω) : ‖reply (g := g) h x ξ - gradient f x‖ ^ 2 ≤
      2 * ‖reply (g := g) h x ξ - difference h x f‖ ^ 2 +
        2 * ‖difference h x f - gradient f x‖ ^ 2 := by
    have h1 : reply (g := g) h x ξ - gradient f x
        = (reply (g := g) h x ξ - difference h x f) + (difference h x f - gradient f x) := by abel
    rw [h1]
    exact hsq
  have hsm : AEStronglyMeasurable (fun ξ : Fin m → Fin d × Bool → Ω =>
      ‖reply (g := g) h x ξ - gradient f x‖ ^ 2) (batchLaw d m p) :=
    ((reply_measurable hg h x).sub measurable_const).norm.aestronglyMeasurable.pow 2
  have hI2 : Integrable (fun ξ => 2 * ‖reply (g := g) h x ξ - difference h x f‖ ^ 2 +
      2 * ‖difference h x f - gradient f x‖ ^ 2) (batchLaw d m p) :=
    Integrable.add (hB.1.const_mul 2) (integrable_const _)
  have hL : Integrable (fun ξ : Fin m → Fin d × Bool → Ω =>
      ‖reply (g := g) h x ξ - gradient f x‖ ^ 2) (batchLaw d m p) := by
    refine hI2.mono hsm (ae_of_all _ fun ξ => ?_)
    have h0 : 0 ≤ ‖reply (g := g) h x ξ - gradient f x‖ ^ 2 := sq_nonneg _
    have hne : 0 ≤ 2 * ‖reply (g := g) h x ξ - difference h x f‖ ^ 2 +
        2 * ‖difference h x f - gradient f x‖ ^ 2 := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0, abs_of_nonneg hne]
    exact hpt ξ
  refine le_trans (integral_mono hL hI2 hpt) ?_
  calc (∫ ξ, 2 * ‖reply (g := g) h x ξ - difference h x f‖ ^ 2 +
        2 * ‖difference h x f - gradient f x‖ ^ 2 ∂(batchLaw d m p))
      = 2 * ∫ ξ, ‖reply (g := g) h x ξ - difference h x f‖ ^ 2 ∂(batchLaw d m p) +
          2 * ‖difference h x f - gradient f x‖ ^ 2 := by
          rw [integral_add (hB.1.const_mul 2) (integrable_const _), integral_const_mul]
          rw [integral_const]
          simp
    _ ≤ 2 * (4 * (d : ℝ) * σ ^ 2 / (h ^ 2 * m)) + 2 * ((d : ℝ) * (L * h / 2) ^ 2) := by
        refine add_le_add (mul_le_mul_of_nonneg_left hB.2 (by norm_num))
          (mul_le_mul_of_nonneg_left hb (by norm_num))
    _ = 8 * (d : ℝ) * σ ^ 2 / (h ^ 2 * m) + 2 * ((d : ℝ) * (L * h / 2) ^ 2) := by ring

end OracleTemplate.SecantPolyak

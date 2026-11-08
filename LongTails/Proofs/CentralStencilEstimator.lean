import LongTails.Proofs.SecantPolyakEstimator
import LongTails.Algorithms.CubicCentralMomentumZO

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

/-!
Symmetric (central) coordinate differences driven by the same scalar noisy value oracle as the
original zeroth-order setups. One replica estimates coordinate `i` by
`(f (x + h * e i) - f (x - h * e i)) / (2 * h)`; a batch averages `m` independent replicas, which
divides the second moment of the noise by `m`. The bias of the symmetric difference is whatever
the extra regularity assumption of the calling setup provides.
-/

namespace OracleTemplate.SecantPolyak.CentralStencil

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
open SecantDescent SecantPolyak ZerothOrder RobustGradient
open LongTails.Setups.ZerothOrderSmoothAndConvex
open OracleTemplate.Research.CubicCentralMomentumZO

variable {Ω : Type} [_ms : MeasurableSpace Ω] {p : Measure Ω} [_ip : IsProbabilityMeasure p]

/-- The symmetric coordinate difference of the objective. -/
noncomputable def cDiff (h : ℝ) (f : Point d → ℝ) (x : Point d) : Point d :=
  ∑ i : Fin d, ((f (x + h • direction i) - f (x - h • direction i)) / (2 * h)) • direction i

lemma cDiff_apply {d : ℕ} (h : ℝ) (f : Point d → ℝ) (x : Point d) (i : Fin d) :
    cDiff h f x i = (f (x + h • direction i) - f (x - h • direction i)) / (2 * h) := by
  simp [cDiff, direction, EuclideanSpace.basisFun_apply, Pi.single_apply]

/-- One replica of the symmetric estimator from scalar value replies. -/
noncomputable def cEstimate (g : Point d → Ω → ℝ) (h : ℝ) (x : Point d)
    (ξ : Fin d × Bool → Ω) : Point d :=
  ∑ i : Fin d, ((g (x + h • direction i) (ξ (i, true)) -
    g (x - h • direction i) (ξ (i, false))) / (2 * h)) • direction i

lemma cEstimate_apply {d : ℕ} (g : Point d → Ω → ℝ) (h : ℝ) (x : Point d)
    (ξ : Fin d × Bool → Ω) (i : Fin d) :
    cEstimate g h x ξ i =
      (g (x + h • direction i) (ξ (i, true)) - g (x - h • direction i) (ξ (i, false))) / (2 * h) := by
  simp [cEstimate, direction, EuclideanSpace.basisFun_apply, Pi.single_apply]

lemma measurable_cEstimate {d : ℕ} {g : Point d → Ω → ℝ}
    (hg : Measurable (Function.uncurry g)) (h : ℝ) :
    Measurable (fun z : Point d × (Fin d × Bool → Ω) => cEstimate g h z.1 z.2) := by
  apply Finset.measurable_sum
  intro i _
  have hc : Continuous (fun x : Point d => x + h • direction i) := by continuity
  have hd : Continuous (fun x : Point d => x - h • direction i) := by continuity
  exact (((hg.comp ((hc.measurable.comp measurable_fst).prodMk
      ((measurable_pi_apply (i, true)).comp measurable_snd))).sub
      (hg.comp ((hd.measurable.comp measurable_fst).prodMk
        ((measurable_pi_apply (i, false)).comp measurable_snd)))).div_const (2 * h)).smul_const _

lemma cEstimate_integral {d : ℕ} {g : Point d → Ω → ℝ} {f : Point d → ℝ}
    {Q : Measure (Fin d × Bool → Ω)}
    (hmap : ∀ j, MeasurePreserving (fun ξ : Fin d × Bool → Ω => ξ j) Q p)
    (hgi : ∀ x, Integrable (g x) p)
    (hmean : ∀ x, (∫ ω, g x ω ∂p) = f x) (h : ℝ) (x : Point d) :
    Integrable (cEstimate g h x) Q ∧ (∫ ξ, cEstimate g h x ξ ∂Q) = cDiff h f x := by
  classical
  have hi (i : Fin d) : Integrable (fun ξ : Fin d × Bool → Ω =>
      (g (x + h • direction i) (ξ (i, true)) -
        g (x - h • direction i) (ξ (i, false))) / (2 * h)) Q :=
    ((hmap _).integrable_comp_of_integrable (hgi _)).sub
      ((hmap _).integrable_comp_of_integrable (hgi _)) |>.div_const (2 * h)
  constructor
  · exact integrable_finsetSum _ (fun i _ => (hi i).smul_const _)
  · have h1 : (fun ξ => cEstimate g h x ξ) =
        fun ξ => ∑ i : Fin d,
          ((g (x + h • direction i) (ξ (i, true)) -
              g (x - h • direction i) (ξ (i, false))) / (2 * h)) • direction i := rfl
    rw [h1, integral_finsetSum _ (fun i _ => (hi i).smul_const _)]
    unfold cDiff
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hp : Integrable (fun ξ : Fin d × Bool → Ω => g (x + h • direction i) (ξ (i, true))) Q :=
      (hmap _).integrable_comp_of_integrable (hgi _)
    have hm : Integrable (fun ξ : Fin d × Bool → Ω => g (x - h • direction i) (ξ (i, false))) Q :=
      (hmap _).integrable_comp_of_integrable (hgi _)
    rw [integral_smul_const, integral_div, integral_sub hp hm]
    rw [integral_comp_preserving (hmap (i, true)) (hgi _),
      integral_comp_preserving (hmap (i, false)) (hgi _), hmean, hmean]

/-- The symmetric estimator is measurable at a fixed base point. -/
lemma measurable_cEstimate_at {d : ℕ} {g : Point d → Ω → ℝ}
    (hg : Measurable (Function.uncurry g)) (h : ℝ) (x : Point d) :
    Measurable (cEstimate g h x) := by
  apply Finset.measurable_sum
  intro i _
  have h1 : Measurable (fun p : Fin d × Bool → Ω =>
      g (x + h • direction i) (p (i, true))) := by fun_prop
  have h2 : Measurable (fun p : Fin d × Bool → Ω =>
      g (x - h • direction i) (p (i, false))) := by fun_prop
  exact (((h1.sub h2).div_const (2 * h)).smul_const _)

/-- The reply of one batch: the mean of `m` independent replicas of the symmetric estimator. -/
noncomputable def cReply {d m : ℕ} (g : Point d → Ω → ℝ) (h : ℝ) (x : Point d)
    (ξ : Fin m → Fin d × Bool → Ω) : Point d :=
  (1 / (m : ℝ)) • ∑ r : Fin m, cEstimate g h x (ξ r)

lemma centralPoint_true {d m : ℕ} (h : ℝ) (x : Point d) (r : Fin m) (i : Fin d) :
    centralPoint h x (r, (i, true)) = x + h • direction i := by
  simp [centralPoint, secantSign, secantCoord]

lemma centralPoint_false {d m : ℕ} (h : ℝ) (x : Point d) (r : Fin m) (i : Fin d) :
    centralPoint h x (r, (i, false)) = x - h • direction i := by
  simp [centralPoint, secantSign, secantCoord]

/-- Regroup the slots of the central decoder into coordinate symmetric differences. -/
lemma centralDecode_group {d m : ℕ} (h : ℝ) (replies : secantSpace d m → ℝ) :
    (∑ t : secantSpace d m,
      ((if secantSign t then replies t else -replies t) / (2 * h)) •
        direction (secantCoord t)) =
      ∑ r : Fin m, ∑ i : Fin d,
        ((replies (r, (i, true)) - replies (r, (i, false))) / (2 * h)) • direction i := by
  classical
  refine Eq.trans (Fintype.sum_prod_type _) (Finset.sum_congr rfl (fun r _ => ?_))
  refine Eq.trans (Fintype.sum_prod_type _) (Finset.sum_congr rfl (fun k _ => ?_))
  simp only [secantSign, secantCoord]
  have huniv : (Finset.univ : Finset Bool) = {true, false} := by decide
  rw [huniv, Finset.sum_pair (by decide : (true : Bool) ≠ false)]
  simp only [Bool.false_eq_true, ite_false, ite_true]
  rw [← add_smul]
  refine congrArg (fun v : ℝ => v • direction k) ?_
  by_cases hz : h = 0
  · subst hz
    simp
  · field_simp
    ring

/-- The executed central decoder is the replicated symmetric estimator. -/
lemma centralDecode_eq_cReply {d m : ℕ} {g : Point d → Ω → ℝ} (h : ℝ) (x : Point d)
    (ξ : Fin m → Fin d × Bool → Ω) :
    centralDecode h (fun t : secantSpace d m => g (centralPoint h x t) (ξ t.1 t.2))
      = cReply g h x ξ := by
  classical
  unfold cReply
  refine congrArg (fun v : Point d => (1 / (m : ℝ)) • v) ?_
  rw [centralDecode_group]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  have hr : cEstimate g h x (ξ r) =
      ∑ i : Fin d, ((g (x + h • direction i) (ξ r (i, true)) -
          g (x - h • direction i) (ξ r (i, false))) / (2 * h)) • direction i := rfl
  rw [hr]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [centralPoint_true, centralPoint_false]

/-- The symmetric difference approximates the gradient with the bias allowed by the setup. -/
lemma cDiff_bias_sq {d : ℕ} {f : Point d → ℝ} {h β : ℝ}
    (_hh : 0 < h) (_hβ : 0 ≤ β)
    (hcb : ∀ (x v : Point d), ‖v‖ = 1 →
      |(f (x + h • v) - f (x - h • v)) / (2 * h) - ⟪gradient f x, v⟫| ≤ β)
    (x : Point d) : ‖cDiff h f x - gradient f x‖ ^ 2 ≤ (d : ℝ) * β ^ 2 := by
  classical
  have hcoord (i : Fin d) : |cDiff h f x i - gradient f x i| ≤ β := by
    have h1 := hcb x (direction i) (direction_norm i)
    have hi : ⟪gradient f x, direction i⟫ = gradient f x i :=
      EuclideanSpace.inner_basisFun_real (Fin d) (gradient f x) i
    rw [cDiff_apply, ← hi]
    exact h1
  have hbound (i : Fin d) :
      (cDiff h f x - gradient f x).ofLp i ^ 2 ≤ β ^ 2 := by
    have h2 : (cDiff h f x - gradient f x).ofLp i = cDiff h f x i - gradient f x i := rfl
    rw [h2]
    have h3 := abs_mul_abs_self (cDiff h f x i - gradient f x i)
    nlinarith [hcoord i, abs_nonneg (cDiff h f x i - gradient f x i), h3]
  have hcard : (∑ _i : Fin d, β ^ 2) = (d : ℝ) * β ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ,
      smul_eq_mul]
  rw [EuclideanSpace.real_norm_sq_eq]
  calc (∑ i : Fin d, (cDiff h f x - gradient f x).ofLp i ^ 2)
      ≤ ∑ _i : Fin d, β ^ 2 := Finset.sum_le_sum (fun i _ => hbound i)
    _ = (d : ℝ) * β ^ 2 := hcard

/-- Mean-square noise of one replica of the symmetric estimator. -/
lemma cEstimate_variance {d : ℕ} {g : Point d → Ω → ℝ} {f : Point d → ℝ} {σ : ℝ}
    (hgi : ∀ x, Integrable (g x) p)
    (hvi : ∀ x, Integrable (fun ω => (g x ω - f x) ^ 2) p)
    (hv : ∀ x, (∫ ω, (g x ω - f x) ^ 2 ∂p) ≤ σ ^ 2) (h : ℝ) (x : Point d) :
    Integrable (fun ξ => ‖cEstimate g h x ξ - cDiff h f x‖ ^ 2) (cellLaw d p) ∧
      (∫ ξ, ‖cEstimate g h x ξ - cDiff h f x‖ ^ 2 ∂(cellLaw d p)) ≤ (d : ℝ) * σ ^ 2 / h ^ 2 := by
  classical
  have hcoord (i : Fin d) :
      Integrable (fun ξ => (cEstimate g h x ξ i - cDiff h f x i) ^ 2) (cellLaw d p) ∧
        (∫ ξ, (cEstimate g h x ξ i - cDiff h f x i) ^ 2 ∂(cellLaw d p)) ≤ σ ^ 2 / h ^ 2 := by
    let a := fun ξ : Fin d × Bool → Ω =>
      g (x + h • direction i) (ξ (i, true)) - f (x + h • direction i)
    let b := fun ξ : Fin d × Bool → Ω =>
      g (x - h • direction i) (ξ (i, false)) - f (x - h • direction i)
    have ha : Integrable (fun ξ => a ξ ^ 2) (cellLaw d p) :=
      (cell_preserving (i, true)).integrable_comp_of_integrable (hvi _)
    have hb : Integrable (fun ξ => b ξ ^ 2) (cellLaw d p) :=
      (cell_preserving (i, false)).integrable_comp_of_integrable (hvi _)
    have hpm : AEStronglyMeasurable (fun ξ : Fin d × Bool → Ω =>
        g (x + h • direction i) (ξ (i, true))) (cellLaw d p) :=
      ((cell_preserving (i, true)).integrable_comp_of_integrable (hgi _)).aestronglyMeasurable
    have hqm : AEStronglyMeasurable (fun ξ : Fin d × Bool → Ω =>
        g (x - h • direction i) (ξ (i, false))) (cellLaw d p) :=
      ((cell_preserving (i, false)).integrable_comp_of_integrable (hgi _)).aestronglyMeasurable
    have ham : AEStronglyMeasurable a (cellLaw d p) :=
      hpm.sub aestronglyMeasurable_const
    have hbm : AEStronglyMeasurable b (cellLaw d p) :=
      hqm.sub aestronglyMeasurable_const
    have hav : (∫ ξ, a ξ ^ 2 ∂(cellLaw d p)) ≤ σ ^ 2 := by
      change (∫ ξ, (g (x + h • direction i) (ξ (i, true)) -
          f (x + h • direction i)) ^ 2 ∂(cellLaw d p)) ≤ _
      exact (integral_comp_preserving (cell_preserving (i, true)) (hvi _)).trans_le (hv _)
    have hbv : (∫ ξ, b ξ ^ 2 ∂(cellLaw d p)) ≤ σ ^ 2 := by
      change (∫ ξ, (g (x - h • direction i) (ξ (i, false)) -
          f (x - h • direction i)) ^ 2 ∂(cellLaw d p)) ≤ _
      exact (integral_comp_preserving (cell_preserving (i, false)) (hvi _)).trans_le (hv _)
    have he : (fun ξ => (cEstimate g h x ξ i - cDiff h f x i) ^ 2) =
        fun ξ => ((a ξ - b ξ) / (2 * h)) ^ 2 := by
      funext ξ
      rw [cEstimate_apply, cDiff_apply]
      congr 1
      dsimp only [a, b]
      ring
    rw [he]
    obtain ⟨h1, h2⟩ := difference_noise_sq ha hb ham hbm hav hbv
    refine ⟨h1, le_trans h2 ?_⟩
    have h3 : (4 : ℝ) * σ ^ 2 / (2 * h) ^ 2 = σ ^ 2 / h ^ 2 := by
      by_cases hz : h = 0
      · subst hz
        simp
      · field_simp
        ring
    rw [← h3]
  have he : (fun ξ => ‖cEstimate g h x ξ - cDiff h f x‖ ^ 2) =
      fun ξ => ∑ i : Fin d, (cEstimate g h x ξ i - cDiff h f x i) ^ 2 := by
    funext ξ
    rw [EuclideanSpace.real_norm_sq_eq]
    refine Finset.sum_congr rfl (fun i _ => congrArg (fun w : ℝ => w ^ 2) ?_)
    show (cEstimate g h x ξ - cDiff h f x).ofLp i =
      (cEstimate g h x ξ).ofLp i - (cDiff h f x).ofLp i
    rfl
  rw [he]
  refine ⟨integrable_finsetSum _ (fun i _ => (hcoord i).1), ?_⟩
  rw [integral_finsetSum _ (fun i _ => (hcoord i).1)]
  calc _ ≤ ∑ _i : Fin d, σ ^ 2 / h ^ 2 := Finset.sum_le_sum (fun i _ => (hcoord i).2)
    _ = (d : ℝ) * (σ ^ 2 / h ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ,
          smul_eq_mul]
    _ = (d : ℝ) * σ ^ 2 / h ^ 2 := by ring

/-- The centered reply is jointly measurable in base point and samples. -/
lemma measurable_cReply_joint {d m : ℕ} {g : Point d → Ω → ℝ}
    (hg : Measurable (Function.uncurry g)) (h : ℝ) :
    Measurable (fun q : Point d × (Fin m → Fin d × Bool → Ω) => cReply g h q.1 q.2) := by
  classical
  have hv : Measurable (fun q : Point d × (Fin m → Fin d × Bool → Ω) =>
      ∑ r : Fin m, cEstimate g h q.1 (q.2 r)) := by
    refine Finset.measurable_sum Finset.univ (fun r _ => ?_)
    unfold cEstimate
    refine Finset.measurable_sum Finset.univ (fun i _ => ?_)
    have hp : Measurable (fun q : Point d × (Fin m → Fin d × Bool → Ω) =>
        q.1 + h • direction i) := measurable_fst.add measurable_const
    have hq : Measurable (fun q : Point d × (Fin m → Fin d × Bool → Ω) =>
        q.1 - h • direction i) := measurable_fst.sub measurable_const
    have hw (b : Bool) : Measurable (fun q : Point d × (Fin m → Fin d × Bool → Ω) =>
        q.2 r (i, b)) :=
      (measurable_pi_apply (i, b)).comp ((measurable_pi_apply r).comp measurable_snd)
    have h1 : Measurable (fun q : Point d × (Fin m → Fin d × Bool → Ω) =>
        g (q.1 + h • direction i) (q.2 r (i, true))) := hg.comp (hp.prodMk (hw true))
    have h2 : Measurable (fun q : Point d × (Fin m → Fin d × Bool → Ω) =>
        g (q.1 - h • direction i) (q.2 r (i, false))) := hg.comp (hq.prodMk (hw false))
    exact smul_measurable ((h1.sub h2).div_const (2 * h)) measurable_const
  exact smul_measurable measurable_const hv

/-- The centered reply is measurable at a fixed base point. -/
lemma measurable_cReply_at {d m : ℕ} {g : Point d → Ω → ℝ}
    (hg : Measurable (Function.uncurry g)) (h : ℝ) (x : Point d) :
    Measurable (fun ξ : Fin m → Fin d × Bool → Ω => cReply g h x ξ) := by
  classical
  have hs : Measurable (fun ξ : Fin m → Fin d × Bool → Ω =>
      ∑ r : Fin m, cEstimate g h x (ξ r)) :=
    Finset.measurable_sum Finset.univ fun r _ =>
      (measurable_cEstimate_at hg h x).comp (measurable_pi_apply r)
  exact smul_measurable measurable_const hs

set_option maxHeartbeats 4000000 in
/-- Mean-square noise of a batch of `m` independent replicas of the symmetric estimator. -/
lemma cReply_deviation {d m : ℕ} {g : Point d → Ω → ℝ} {f : Point d → ℝ} {σ : ℝ}
    (hg : Measurable (Function.uncurry g))
    (hgi : ∀ x, Integrable (g x) p)
    (hmean : ∀ x, (∫ ω, g x ω ∂p) = f x)
    (hvi : ∀ x, Integrable (fun ω => (g x ω - f x) ^ 2) p)
    (hv : ∀ x, (∫ ω, (g x ω - f x) ^ 2 ∂p) ≤ σ ^ 2)
    (hm : 0 < m) (x : Point d) :
    Integrable (fun ξ : Fin m → Fin d × Bool → Ω => ‖cReply g h x ξ - cDiff h f x‖ ^ 2)
        (batchLaw d m p) ∧
      (∫ ξ : Fin m → Fin d × Bool → Ω, ‖cReply g h x ξ - cDiff h f x‖ ^ 2 ∂(batchLaw d m p)) ≤
        (d : ℝ) * σ ^ 2 / (h ^ 2 * m) := by
  classical
  set X : (Fin d × Bool → Ω) → Point d := cEstimate g h x with hXdef
  have hXm : Measurable X := measurable_cEstimate_at hg h x
  obtain ⟨hEi, hE⟩ := cEstimate_integral (fun j => cell_preserving j) hgi hmean h x
  obtain ⟨hI2, hI⟩ := finite_mean_variance hXm hEi (cDiff h f x)
    (cEstimate_variance hgi hvi hv h x).1 hE m hm
  have hXe (ξ : Fin m → Fin d × Bool → Ω) :
      cReply g h x ξ - cDiff h f x =
        (1 / (m : ℝ)) • ∑ r : Fin m, X (ξ r) - cDiff h f x := rfl
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  refine ⟨hI2.congr (ae_of_all _ fun ξ =>
      (congrArg (fun v : Point d => ‖v‖ ^ 2) (hXe ξ)).symm), ?_⟩
  calc (∫ ξ : Fin m → Fin d × Bool → Ω, ‖cReply g h x ξ - cDiff h f x‖ ^ 2 ∂(batchLaw d m p))
      = ∫ ξ : Fin m → Fin d × Bool → Ω, ‖(1 / (m : ℝ)) • ∑ r : Fin m, X (ξ r)
            - cDiff h f x‖ ^ 2 ∂(batchLaw d m p) := by
          refine integral_congr_ae ?_
          exact ae_of_all _ (fun ξ => congrArg (fun v : Point d => ‖v‖ ^ 2) (hXe ξ))
    _ = (∫ η, ‖X η - cDiff h f x‖ ^ 2 ∂(cellLaw d p)) / m := hI
    _ ≤ ((d : ℝ) * σ ^ 2 / h ^ 2) / m :=
        div_le_div_of_nonneg_right (cEstimate_variance hgi hvi hv h x).2 (le_of_lt hm')
    _ = (d : ℝ) * σ ^ 2 / (h ^ 2 * m) := by
        simp only [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]

end OracleTemplate.SecantPolyak.CentralStencil

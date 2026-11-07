import LongTails.Algorithms.DampedAnchoredPairAcceleration
import LongTails.Proofs.GdConvex
import LongTails.Proofs.InexactAcceleratedStep

set_option maxHeartbeats 2000000

/-!
One round of damped anchored pair acceleration. Because the probe deviation is bounded by the
smoothed gap at the probed point rather than by a fixed variance, the deviation term of the round is
absorbed by the negative `‖y - xh‖²` term that the accelerated potential produces, provided
`(L * η² / 2 + θ² / μ) * 2 * ρ² ≤ μ * θ / (2 * L)`. The round then contracts the expected potential
by `1 - θ` with no additive error, which is what turns the budget into a logarithm.
-/

namespace OracleTemplate.SecantPolyak.AnchoredPair

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
open OracleTemplate SecantDescent InexactGradient
open _root_.OracleTemplate.Gradient
open LongTails.Setups.ZerothOrderSmoothAndConvex (Point)

variable {Ω : Type} [MeasurableSpace Ω] {d : ℕ}

/-- Square-integrable surrogate: the mean square splits into the squared mean and the mean-square
deviation. -/
lemma ap_pyth {P : Measure Ω} [IsProbabilityMeasure P] (V : Ω → Point d) (g : Point d)
    (hV : Integrable V P) (hdev : Integrable (fun ω => ‖V ω - g‖ ^ 2) P)
    (hmean : (∫ ω, V ω ∂P) = g) :
    (∫ ω, ‖V ω‖ ^ 2 ∂P) = ‖g‖ ^ 2 + ∫ ω, ‖V ω - g‖ ^ 2 ∂P := by
  classical
  have hsub : Integrable (fun ω => V ω - g) P := hV.sub (integrable_const g)
  have hint0 : (∫ ω, V ω - g ∂P) = 0 := by
    rw [integral_sub hV (integrable_const g), hmean, integral_const, probReal_univ, one_smul,
      sub_self]
  set Lc : Point d →L[ℝ] ℝ := InnerProductSpace.toDual ℝ (Point d) g with hLcdef
  have hLc : ∀ y : Point d, Lc y = ⟪g, y⟫ := fun _ => rfl
  have hlin0 : (∫ ω, ⟪g, V ω - g⟫ ∂P) = 0 := by
    refine (integral_congr_ae (ae_of_all _ fun ω => (hLc (V ω - g)).symm)).trans ?_
    rw [Lc.integral_comp_comm hsub, hint0, map_zero]
  have hlin_int : Integrable (fun ω => 2 * ⟪g, V ω - g⟫) P := by
    have he : (fun ω => 2 * ⟪g, V ω - g⟫) = fun ω => (2 : ℝ) • Lc (V ω - g) := by
      funext ω
      rw [hLc, smul_eq_mul]
    rw [he]
    exact Integrable.smul (2 : ℝ) (Lc.integrable_comp hsub)
  have hpt : ∀ ω, ‖V ω‖ ^ 2 = ‖g‖ ^ 2 + 2 * ⟪g, V ω - g⟫ + ‖V ω - g‖ ^ 2 := by
    intro ω
    have h2 : ‖g + (V ω - g)‖ ^ 2 = ‖g‖ ^ 2 + 2 * ⟪g, V ω - g⟫ + ‖V ω - g‖ ^ 2 :=
      norm_add_sq_real g (V ω - g)
    have h3 : g + (V ω - g) = V ω := by rw [add_comm, sub_add_cancel]
    rw [h3] at h2
    exact h2
  have hA : (∫ ω, ‖g‖ ^ 2 + 2 * ⟪g, V ω - g⟫ + ‖V ω - g‖ ^ 2 ∂P)
      = (∫ ω, ‖g‖ ^ 2 + 2 * ⟪g, V ω - g⟫ ∂P) + ∫ ω, ‖V ω - g‖ ^ 2 ∂P :=
    integral_add ((integrable_const _).add hlin_int) hdev
  have hB : (∫ ω, ‖g‖ ^ 2 + 2 * ⟪g, V ω - g⟫ ∂P) = ‖g‖ ^ 2 := by
    rw [integral_add (integrable_const _) hlin_int, integral_const, probReal_univ, one_smul,
      integral_const_mul, hlin0, mul_zero, add_zero]
  have hF : Integrable (fun ω => ‖g‖ ^ 2 + 2 * ⟪g, V ω - g⟫ + ‖V ω - g‖ ^ 2) P :=
    ((integrable_const _).add hlin_int).add hdev
  calc (∫ ω, ‖V ω‖ ^ 2 ∂P)
      = ∫ ω, ‖g‖ ^ 2 + 2 * ⟪g, V ω - g⟫ + ‖V ω - g‖ ^ 2 ∂P :=
          integral_congr_ae (ae_of_all _ hpt)
    _ = ‖g‖ ^ 2 + ∫ ω, ‖V ω - g‖ ^ 2 ∂P := by rw [hA, hB]

/-- The mean of a centered surrogate annihilates every fixed linear functional. -/
lemma ap_inner_zero {P : Measure Ω} [IsProbabilityMeasure P] (V : Ω → Point d) (g φ : Point d)
    (hV : Integrable V P) (hmean : (∫ ω, V ω ∂P) = g) :
    (∫ ω, ⟪φ, V ω - g⟫ ∂P) = 0 := by
  classical
  have hsub : Integrable (fun ω => V ω - g) P := hV.sub (integrable_const g)
  have hint0 : (∫ ω, V ω - g ∂P) = 0 := by
    rw [integral_sub hV (integrable_const g), hmean, integral_const, probReal_univ, one_smul,
      sub_self]
  set Lc : Point d →L[ℝ] ℝ := InnerProductSpace.toDual ℝ (Point d) φ with hLcdef
  have hLc : ∀ y : Point d, Lc y = ⟪φ, y⟫ := fun _ => rfl
  refine (integral_congr_ae (ae_of_all _ fun ω => (hLc (V ω - g)).symm)).trans ?_
  rw [Lc.integral_comp_comm hsub, hint0, map_zero]

/-- The accelerated telescoping inequality of the interpolated query point. -/
lemma ap_telescope {f : Point d → ℝ} {G : Point d} {μ θ : ℝ} {x z y xh : Point d}
    (hμ : 0 ≤ μ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hyq : (1 + θ) • y = x + θ • z)
    (h1 : f y + ⟪G, xh - y⟫ + μ / 2 * ‖xh - y‖ ^ 2 ≤ f xh)
    (h2 : f y + ⟪G, x - y⟫ + μ / 2 * ‖x - y‖ ^ 2 ≤ f x) :
    θ * (f y - f xh + μ / 2 * ‖y - xh‖ ^ 2) + (1 - θ) * (f y - f x)
      ≤ θ * ⟪G, (1 - θ) • (z - xh) + θ • (y - xh)⟫ := by
  classical
  set w : Point d := (1 - θ) • (z - xh) + θ • (y - xh) with hwdef
  have hb1 : f y - f xh + μ / 2 * ‖y - xh‖ ^ 2 ≤ ⟪G, y - xh⟫ := by
    have hz : ⟪G, xh - y⟫ = -⟪G, y - xh⟫ := by rw [← neg_sub, inner_neg_right]
    rw [hz, norm_sub_rev] at h1
    linarith
  have hb2 : f y - f x ≤ ⟪G, y - x⟫ := by
    have hz : ⟪G, x - y⟫ = -⟪G, y - x⟫ := by rw [← neg_sub, inner_neg_right]
    rw [hz] at h2
    have hnn : 0 ≤ μ / 2 * ‖x - y‖ ^ 2 := by positivity
    linarith
  have hw : θ • w = θ • (y - xh) + (1 - θ) • (y - x) := by
    have h3 : θ • w = θ • (y - xh) + (1 - θ) • (y - x) +
        (1 - θ) • (x + θ • z - (1 + θ) • y) := by
      simp only [w]
      module
    rw [h3, hyq, sub_self, smul_zero, add_zero]
  have hlin : θ * ⟪G, w⟫ = θ * ⟪G, y - xh⟫ + (1 - θ) * ⟪G, y - x⟫ := by
    rw [← inner_smul_right, hw, inner_add_right, inner_smul_right, inner_smul_right]
  have m1 := mul_le_mul_of_nonneg_left hb1 hθ0.le
  have m2 := mul_le_mul_of_nonneg_left hb2 (show (0 : ℝ) ≤ 1 - θ by linarith)
  rw [hlin]
  simp only [hwdef] at *
  linarith

/-- Jensen inequality for the squared norm of an interpolated displacement. -/
lemma ap_jensen {θ : ℝ} {a b : Point d} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ‖(1 - θ) • a + θ • b‖ ^ 2 ≤ (1 - θ) * ‖a‖ ^ 2 + θ * ‖b‖ ^ 2 := by
  have h2 : 2 * ⟪a, b⟫ ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    have h := sq_nonneg ‖a - b‖
    rw [norm_sub_sq_real] at h
    linarith
  have hn : ‖(1 - θ) • a + θ • b‖ ^ 2 =
      (1 - θ) ^ 2 * ‖a‖ ^ 2 + 2 * ((1 - θ) * θ * ⟪a, b⟫) + θ ^ 2 * ‖b‖ ^ 2 := by
    rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
      Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
    ring
  have hcross : 0 ≤ (1 - θ) * θ := mul_nonneg (by linarith) hθ0
  have hcr := mul_le_mul_of_nonneg_left h2 hcross
  rw [hn]
  nlinarith

/-- Algebraic expansion of the two surrogate terms of one damped anchored update. -/
lemma ap_algebra {L μ θ η : ℝ} (w g e : Point d) (hμ : 0 < μ) :
    ⟪g, -η • (g + e)⟫ + L / 2 * ‖η • (g + e)‖ ^ 2
      + μ / 4 * ‖w - (2 * θ / μ) • (g + e)‖ ^ 2
    = (L * η ^ 2 / 2 + θ ^ 2 / μ) * ‖e‖ ^ 2
      + ⟪(-η + L * η ^ 2) • g - θ • (w - (2 * θ / μ) • g), e⟫
      - η * ‖g‖ ^ 2 + L * η ^ 2 / 2 * ‖g‖ ^ 2
      + μ / 4 * ‖w - (2 * θ / μ) • g‖ ^ 2 := by
  have h1 : ‖η • (g + e)‖ ^ 2 = η ^ 2 * ‖g + e‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have h4 : w - (2 * θ / μ) • (g + e) = (w - (2 * θ / μ) • g) - (2 * θ / μ) • e := by
    rw [smul_add, sub_sub]
  have h5 : ‖(2 * θ / μ) • e‖ ^ 2 = (2 * θ / μ) ^ 2 * ‖e‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have h6 : ⟪g, -η • (g + e)⟫ = -η * (⟪g, g⟫ + ⟪g, e⟫) := by
    rw [inner_smul_right, inner_add_right, neg_mul]
  rw [h1, h4, h6, norm_add_sq_real, norm_sub_sq_real, h5]
  simp only [inner_smul_right, inner_sub_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, mul_add, add_mul, mul_sub, neg_mul, mul_comm, mul_left_comm,
    mul_assoc]
  field_simp [hμ.ne']
  ring

/-- Uniform upper bound of the smoothed objective by the squared distance to a minimizer. -/
lemma ap_gap_upper {f : Point d → ℝ} {L : ℝ} {xh : Point d}
    (hgr : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hmin : IsMinOn f Set.univ xh) :
    ∀ y : Point d, f y - f xh ≤ L / 2 * ‖y - xh‖ ^ 2 := by
  intro y
  have hl : IsLocalMin f xh := hmin.isLocalMin Filter.univ_mem
  have hzero : gradient f xh = 0 := by
    apply (_root_.InnerProductSpace.toDual ℝ (Point d)).injective
    simpa using _root_.IsLocalMin.hasFDerivAt_eq_zero hl (hgr xh).hasFDerivAt
  have h1 := smooth_upper_bound (f := f) (oracle := gradient f) (L := L) hgr hlip xh y
  rw [hzero, inner_zero_left, add_zero] at h1
  exact sub_le_iff_le_add'.mpr h1

/-- Pointwise expansion of one damped anchored round. -/
lemma ap_perturb {f : Point d → ℝ} {L μ θ η : ℝ} {xh : Point d} (s : Point d × Point d)
    (v : Point d)
    (hgr : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) :
    potential f μ xh (apStep μ θ η s v) ≤
      (f (query θ s) - f xh) + ⟪gradient f (query θ s), -η • v⟫ + L / 2 * ‖η • v‖ ^ 2
        + μ / 4 * ‖(1 - θ) • (s.2 - xh) + θ • (query θ s - xh) - (2 * θ / μ) • v‖ ^ 2 := by
  classical
  have h1 : f (query θ s - η • v) - f xh
      ≤ f (query θ s) + ⟪gradient f (query θ s), -η • v⟫ + L / 2 * ‖η • v‖ ^ 2 - f xh := by
    have hz : query θ s - η • v - query θ s = -η • v := by module
    have hn : ‖-η • v‖ ^ 2 = ‖η • v‖ ^ 2 := by rw [neg_smul, norm_neg]
    have h := smooth_upper_bound (f := f) (oracle := gradient f) (L := L) hgr hlip
      (query θ s) (query θ s - η • v)
    rw [hz, hn] at h
    linarith
  have h3 : (1 - θ) • s.2 + θ • query θ s - (2 * θ / μ) • v - xh
      = (1 - θ) • (s.2 - xh) + θ • (query θ s - xh) - (2 * θ / μ) • v := by
    rw [sub_smul, sub_smul]
    module
  have h4 : μ / 4 * ‖(1 - θ) • s.2 + θ • query θ s - (2 * θ / μ) • v - xh‖ ^ 2
      = μ / 4 * ‖(1 - θ) • (s.2 - xh) + θ • (query θ s - xh) - (2 * θ / μ) • v‖ ^ 2 := by
    rw [h3]
  have h5 := add_le_add h1 (le_of_eq h4)
  calc potential f μ xh (apStep μ θ η s v)
      = f (query θ s - η • v) - f xh
        + μ / 4 * ‖(1 - θ) • s.2 + θ • query θ s - (2 * θ / μ) • v - xh‖ ^ 2 := rfl
    _ ≤ f (query θ s) + ⟪gradient f (query θ s), -η • v⟫ + L / 2 * ‖η • v‖ ^ 2 - f xh
        + μ / 4 * ‖(1 - θ) • (s.2 - xh) + θ • (query θ s - xh) - (2 * θ / μ) • v‖ ^ 2 := h5
    _ = (f (query θ s) - f xh) + ⟪gradient f (query θ s), -η • v⟫ + L / 2 * ‖η • v‖ ^ 2
        + μ / 4 * ‖(1 - θ) • (s.2 - xh) + θ • (query θ s - xh) - (2 * θ / μ) • v‖ ^ 2 := by ring

/-- Deterministic core of one damped anchored round: the mean part of the potential contracts. -/
lemma ap_det {f : Point d → ℝ} {L μ θ η ρ : ℝ} {xh : Point d} (s : Point d × Point d)
    (hL : 0 < L) (hμ : 0 < μ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hcap1 : θ ^ 2 / μ ≤ η - L * η ^ 2 / 2)
    (hcap3 : (L * η ^ 2 / 2 + θ ^ 2 / μ) * (2 * ρ ^ 2) ≤ μ * θ / 4 * (2 / L))
    (hgr : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hsc : ∀ x y, f x + ⟪gradient f x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (hmin : IsMinOn f Set.univ xh) :
    (f (query θ s) - f xh) - η * ‖gradient f (query θ s)‖ ^ 2
        + (L * η ^ 2 / 2) * ‖gradient f (query θ s)‖ ^ 2
        + μ / 4
          * ‖(1 - θ) • (s.2 - xh) + θ • (query θ s - xh)
            - (2 * θ / μ) • gradient f (query θ s)‖ ^ 2
        + (L * η ^ 2 / 2 + θ ^ 2 / μ) * (2 * ρ ^ 2 * (f (query θ s) - f xh))
      ≤ (1 - θ) * potential f μ xh s := by
  classical
  set y : Point d := query θ s with hydef
  set g : Point d := gradient f y with hgdef
  set w : Point d := (1 - θ) • (s.2 - xh) + θ • (y - xh) with hwdef
  have hyq : (1 + θ) • y = s.1 + θ • s.2 := by
    have hq : y = (1 / (1 + θ)) • (s.1 + θ • s.2) := rfl
    rw [hq, smul_smul, mul_one_div_cancel (show (1 : ℝ) + θ ≠ 0 by linarith), one_smul]
  have hup := ap_gap_upper hgr hlip hmin
  have hu0 : 0 ≤ f y - f xh := sub_nonneg.mpr (hmin (Set.mem_univ y))
  have hY : (2 : ℝ) / L * (f y - f xh) ≤ ‖y - xh‖ ^ 2 := by
    have h := hup y
    have h2 : (2 : ℝ) / L * (f y - f xh) ≤ (2 : ℝ) / L * (L / 2 * ‖y - xh‖ ^ 2) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    have h3 : (2 : ℝ) / L * (L / 2 * ‖y - xh‖ ^ 2) = ‖y - xh‖ ^ 2 := by
      field_simp [hL.ne']
    linarith
  have hj : ‖w‖ ^ 2 ≤ (1 - θ) * ‖s.2 - xh‖ ^ 2 + θ * ‖y - xh‖ ^ 2 := by
    simpa only [hwdef] using ap_jensen (a := s.2 - xh) (b := y - xh) hθ0.le hθ1
  have htel := ap_telescope hμ.le hθ0 hθ1 hyq
    (hsc y xh) (hsc y s.1)
  have hneg : -(θ * ⟪g, w⟫)
      ≤ -(θ * (f y - f xh + μ / 2 * ‖y - xh‖ ^ 2) + (1 - θ) * (f y - f s.1)) := by linarith
  have hw2 : μ / 4 * ‖w‖ ^ 2 ≤ μ / 4 * ((1 - θ) * ‖s.2 - xh‖ ^ 2 + θ * ‖y - xh‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hj (by positivity)
  have h2 : ‖(2 * θ / μ) • g‖ ^ 2 = (2 * θ / μ) ^ 2 * ‖g‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have h1 : ⟪w, (2 * θ / μ) • g⟫ = (2 * θ / μ) * ⟪g, w⟫ := by
    rw [real_inner_smul_right, real_inner_comm w g]
  have hexp : μ / 4 * ‖w - (2 * θ / μ) • g‖ ^ 2
      = μ / 4 * ‖w‖ ^ 2 - θ * ⟪g, w⟫ + θ ^ 2 / μ * ‖g‖ ^ 2 := by
    rw [norm_sub_sq_real, h1, h2]
    field_simp [hμ.ne']
    ring
  have hgcoef : (θ ^ 2 / μ - η + L * η ^ 2 / 2) * ‖g‖ ^ 2 ≤ 0 := by
    have hn : 0 ≤ ‖g‖ ^ 2 := sq_nonneg _
    nlinarith
  have hnoise : (L * η ^ 2 / 2 + θ ^ 2 / μ) * (2 * ρ ^ 2 * (f y - f xh))
      ≤ μ * θ / 4 * (2 / L * (f y - f xh)) := by
    have hn : 0 ≤ f y - f xh := hu0
    have h := mul_le_mul_of_nonneg_right hcap3 hn
    calc (L * η ^ 2 / 2 + θ ^ 2 / μ) * (2 * ρ ^ 2 * (f y - f xh))
        = (L * η ^ 2 / 2 + θ ^ 2 / μ) * (2 * ρ ^ 2) * (f y - f xh) := (mul_assoc _ _ _).symm
      _ ≤ (μ * θ / 4 * (2 / L)) * (f y - f xh) := h
      _ = μ * θ / 4 * (2 / L * (f y - f xh)) := mul_assoc _ _ _
  have hYneg : -(μ * θ / 4 * ‖y - xh‖ ^ 2) ≤ -(μ * θ / 4 * ((2 : ℝ) / L * (f y - f xh))) := by
    have hn : 0 ≤ μ * θ / 4 := by positivity
    have h := mul_le_mul_of_nonneg_left hY hn
    linarith
  have hpot : potential f μ xh s = f s.1 - f xh + μ / 4 * ‖s.2 - xh‖ ^ 2 := rfl
  rw [hpot]
  simp only [hydef, hgdef, hwdef] at *
  nlinarith [sq_nonneg ‖s.2 - xh‖, sq_nonneg ‖y - xh‖, hθ0.le, hL.le]

/-- One round of damped anchored pair acceleration in expectation. -/
lemma ap_one_round {f : Point d → ℝ} {L μ θ η ρ : ℝ} {xh : Point d} (s : Point d × Point d)
    (hL : 0 < L) (hμ : 0 < μ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hcap1 : θ ^ 2 / μ ≤ η - L * η ^ 2 / 2)
    (hcap3 : (L * η ^ 2 / 2 + θ ^ 2 / μ) * (2 * ρ ^ 2) ≤ μ * θ / 4 * (2 / L))
    (hgr : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hsc : ∀ x y, f x + ⟪gradient f x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (hmin : IsMinOn f Set.univ xh)
    {P : Measure Ω} [IsProbabilityMeasure P] (V : Ω → Point d)
    (hV : Integrable V P)
    (hdev : Integrable (fun ω => ‖V ω - gradient f (query θ s)‖ ^ 2) P)
    (hmean : (∫ ω, V ω ∂P) = gradient f (query θ s))
    (hvb : (∫ ω, ‖V ω - gradient f (query θ s)‖ ^ 2 ∂P)
        ≤ 2 * ρ ^ 2 * (f (query θ s) - f xh))
    (hmeas : AEStronglyMeasurable
      (fun ω => potential f μ xh (apStep μ θ η s (V ω))) P) :
    Integrable (fun ω => potential f μ xh (apStep μ θ η s (V ω))) P ∧
      (∫ ω, potential f μ xh (apStep μ θ η s (V ω)) ∂P) ≤ (1 - θ) * potential f μ xh s := by
  classical
  set y : Point d := query θ s with hydef
  set g : Point d := gradient f y with hgdef
  set w : Point d := (1 - θ) • (s.2 - xh) + θ • (y - xh) with hwdef
  set cv : ℝ := L * η ^ 2 / 2 + θ ^ 2 / μ with hcvdef
  set φ : Point d := (-η + L * η ^ 2) • g - θ • (w - (2 * θ / μ) • g) with hhdef
  set Ddet : ℝ := (f y - f xh) - η * ‖g‖ ^ 2 + (L * η ^ 2 / 2) * ‖g‖ ^ 2
    + μ / 4 * ‖w - (2 * θ / μ) • g‖ ^ 2 with hDdef
  have hmu : 0 ≤ μ := hμ.le
  have hc0 : 0 ≤ cv := by positivity
  have hptw : ∀ ω, potential f μ xh (apStep μ θ η s (V ω))
      ≤ Ddet + ⟪φ, V ω - g⟫ + cv * ‖V ω - g‖ ^ 2 := by
    intro ω
    have he : V ω = g + (V ω - g) := by rw [add_comm, sub_add_cancel]
    have h1 := ap_perturb (f := f) (L := L) (μ := μ) (θ := θ) (η := η) (xh := xh) s (V ω) hgr
      hlip
    have h2 := ap_algebra (L := L) (μ := μ) (θ := θ) (η := η) w g (V ω - g) hμ
    calc potential f μ xh (apStep μ θ η s (V ω))
        ≤ (f y - f xh) + ⟪g, -η • V ω⟫ + L / 2 * ‖η • V ω‖ ^ 2
            + μ / 4 * ‖w - (2 * θ / μ) • V ω‖ ^ 2 := h1
      _ = (f y - f xh)
          + (⟪g, -η • (g + (V ω - g))⟫ + L / 2 * ‖η • (g + (V ω - g))‖ ^ 2
            + μ / 4 * ‖w - (2 * θ / μ) • (g + (V ω - g))‖ ^ 2) := by
          conv_lhs => rw [he]
          ring
      _ = (f y - f xh)
          + (cv * ‖V ω - g‖ ^ 2 + ⟪φ, V ω - g⟫ - η * ‖g‖ ^ 2 + L * η ^ 2 / 2 * ‖g‖ ^ 2
            + μ / 4 * ‖w - (2 * θ / μ) • g‖ ^ 2) := by rw [h2]
      _ = Ddet + ⟪φ, V ω - g⟫ + cv * ‖V ω - g‖ ^ 2 := by ring

  set Lp : Point d →L[ℝ] ℝ := InnerProductSpace.toDual ℝ (Point d) φ with hlpdef
  have hpL : ∀ z : Point d, Lp z = ⟪φ, z⟫ := fun _ => rfl
  have hlin_int : Integrable (fun ω => ⟪φ, V ω - g⟫) P := by
    refine (Lp.integrable_comp (hV.sub (integrable_const g))).congr ?_
    exact ae_of_all _ fun ω => hpL (V ω - g)
  have hA : Integrable (fun ω => Ddet + ⟪φ, V ω - g⟫ + cv * ‖V ω - g‖ ^ 2) P :=
    ((integrable_const _).add hlin_int).add (hdev.const_mul cv)
  have hnonneg : ∀ ω, 0 ≤ potential f μ xh (apStep μ θ η s (V ω)) := by
    intro ω
    have h1 : 0 ≤ f (apStep μ θ η s (V ω)).1 - f xh := sub_nonneg.mpr (hmin (Set.mem_univ _))
    have h2 : 0 ≤ μ / 4 * ‖(apStep μ θ η s (V ω)).2 - xh‖ ^ 2 := by positivity
    show 0 ≤ f (apStep μ θ η s (V ω)).1 - f xh + μ / 4 * ‖(apStep μ θ η s (V ω)).2 - xh‖ ^ 2
    linarith
  have hintegrable : Integrable (fun ω => potential f μ xh (apStep μ θ η s (V ω))) P :=
    hA.mono' hmeas (ae_of_all _ fun ω => by
      have h0 := hnonneg ω
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact hptw ω)
  refine ⟨hintegrable, ?_⟩
  have hlin0 : (∫ ω, ⟪φ, V ω - g⟫ ∂P) = 0 := ap_inner_zero V g φ hV hmean
  have hAB : Integrable (fun ω => Ddet + ⟪φ, V ω - g⟫) P := (integrable_const _).add hlin_int
  have h1 : (∫ ω, Ddet + ⟪φ, V ω - g⟫ + cv * ‖V ω - g‖ ^ 2 ∂P)
      = (∫ ω, Ddet + ⟪φ, V ω - g⟫ ∂P) + ∫ ω, cv * ‖V ω - g‖ ^ 2 ∂P :=
    integral_add hAB (hdev.const_mul cv)
  have h2 : (∫ ω, Ddet + ⟪φ, V ω - g⟫ ∂P) = Ddet := by
    rw [integral_add (integrable_const _) hlin_int, integral_const, probReal_univ, one_smul,
      hlin0, add_zero]
  have h3 : (∫ ω, cv * ‖V ω - g‖ ^ 2 ∂P) = cv * ∫ ω, ‖V ω - g‖ ^ 2 ∂P :=
    integral_const_mul _ _
  have hsum : (∫ ω, Ddet + ⟪φ, V ω - g⟫ + cv * ‖V ω - g‖ ^ 2 ∂P)
      = Ddet + cv * ∫ ω, ‖V ω - g‖ ^ 2 ∂P := by rw [h1, h2, h3]
  have hmono : (∫ ω, potential f μ xh (apStep μ θ η s (V ω)) ∂P)
      ≤ ∫ ω, Ddet + ⟪φ, V ω - g⟫ + cv * ‖V ω - g‖ ^ 2 ∂P :=
    integral_mono_ae hintegrable hA (ae_of_all _ hptw)
  have hnoise : cv * ∫ ω, ‖V ω - g‖ ^ 2 ∂P ≤ cv * (2 * ρ ^ 2 * (f y - f xh)) :=
    mul_le_mul_of_nonneg_left hvb hc0
  have hdet := ap_det (f := f) (L := L) (μ := μ) (θ := θ) (η := η) (ρ := ρ) (xh := xh) s
    hL hμ hθ0 hθ1 hcap1 hcap3 hgr hlip hsc hmin
  calc (∫ ω, potential f μ xh (apStep μ θ η s (V ω)) ∂P)
      ≤ ∫ ω, Ddet + ⟪φ, V ω - g⟫ + cv * ‖V ω - g‖ ^ 2 ∂P := hmono
    _ = Ddet + cv * ∫ ω, ‖V ω - g‖ ^ 2 ∂P := hsum
    _ ≤ Ddet + cv * (2 * ρ ^ 2 * (f y - f xh)) := by gcongr
    _ ≤ (1 - θ) * potential f μ xh s := hdet

end OracleTemplate.SecantPolyak.AnchoredPair

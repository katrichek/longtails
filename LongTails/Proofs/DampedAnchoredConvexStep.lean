import LongTails.Algorithms.DampedAnchoredConvexPairAcceleration
import LongTails.Proofs.DampedAnchoredStep
import LongTails.Proofs.GdConvex

set_option maxHeartbeats 2000000

namespace OracleTemplate.SecantPolyak.AnchoredConvexPair

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
open OracleTemplate SecantDescent InexactGradient
open _root_.OracleTemplate.Gradient
open LongTails.Setups.ZerothOrderSmoothAndConvex (Point)
open OracleTemplate.SecantPolyak.AnchoredPair

variable {Ω : Type} [MeasurableSpace Ω] {d : ℕ}

noncomputable def dacPotential (f : Point d → ℝ) (η : ℝ) (xh : Point d)
    (k : ℕ) (s : Point d × Point d) : ℝ :=
  dacWeight k * (f s.1 - f xh) + (8 / η) * ‖s.2 - xh‖ ^ 2

lemma dacWeight_nonneg (k : ℕ) : 0 ≤ dacWeight k := by
  unfold dacWeight
  positivity

lemma dacWeight_succ (k : ℕ) : dacWeight (k + 1) = ((k : ℝ) + 1) * ((k : ℝ) + 2) := by
  unfold dacWeight
  push_cast
  ring

lemma measurable_dacQuery (k : ℕ) :
    Measurable (dacQuery k : Point d × Point d → Point d) := by
  unfold dacQuery
  fun_prop

lemma measurable_dacPotential {f : Point d → ℝ} (hf : Measurable f) (η : ℝ) (xh : Point d)
    (k : ℕ) :
    Measurable (dacPotential f η xh k) := by
  have h1 : Measurable (fun s : Point d × Point d => dacWeight k * (f s.1 - f xh)) :=
    measurable_const.mul ((hf.comp measurable_fst).sub measurable_const)
  have h2 : Measurable (fun s : Point d × Point d => (8 / η) * ‖s.2 - xh‖ ^ 2) := by
    fun_prop
  exact h1.add h2

lemma dacQuery_rel (k : ℕ) (s : Point d × Point d) :
    ((k : ℝ) + 4) • dacQuery k s = (k : ℝ) • s.1 + (4 : ℝ) • s.2 := by
  have hk4 : (k : ℝ) + 4 ≠ 0 := by positivity
  unfold dacQuery
  rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ hk4, mul_div_cancel₀ _ hk4]

lemma dac_telescope {f : Point d → ℝ} {xh : Point d} (k : ℕ) (s : Point d × Point d)
    (hc : ConvexOn ℝ Set.univ f)
    (hgr : ∀ x, HasGradientAt f (gradient f x) x) :
    ((k : ℝ) + 1) * ((k : ℝ) + 4) * (f (dacQuery k s) - f xh)
      - 4 * ((k : ℝ) + 1) * ⟪gradient f (dacQuery k s), s.2 - xh⟫
      ≤ dacWeight k * (f s.1 - f xh) := by
  set y : Point d := dacQuery k s
  set g : Point d := gradient f y
  have hs1 : ⟪g, s.1 - y⟫ ≤ f s.1 - f y := convex_support hc hgr y s.1
  have hs2 : ⟪g, xh - y⟫ ≤ f xh - f y := convex_support hc hgr y xh
  have hrel := dacQuery_rel k s
  have hvec : (k : ℝ) • (s.1 - y) + (4 : ℝ) • (xh - y) = -(4 : ℝ) • (s.2 - xh) := by
    have h1 : (k : ℝ) • s.1 = ((k : ℝ) + 4) • y - (4 : ℝ) • s.2 :=
      eq_sub_of_add_eq hrel.symm
    calc (k : ℝ) • (s.1 - y) + (4 : ℝ) • (xh - y)
        = (k : ℝ) • s.1 - (k : ℝ) • y + (4 : ℝ) • xh - (4 : ℝ) • y := by module
      _ = (((k : ℝ) + 4) • y - (4 : ℝ) • s.2) - (k : ℝ) • y + (4 : ℝ) • xh - (4 : ℝ) • y := by
          rw [h1]
      _ = -(4 : ℝ) • (s.2 - xh) := by
          rw [add_smul]
          module
  have hin : (k : ℝ) * ⟪g, s.1 - y⟫ + 4 * ⟪g, xh - y⟫ = -4 * ⟪g, s.2 - xh⟫ := by
    calc (k : ℝ) * ⟪g, s.1 - y⟫ + 4 * ⟪g, xh - y⟫
        = ⟪g, (k : ℝ) • (s.1 - y) + (4 : ℝ) • (xh - y)⟫ := by
          rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
      _ = ⟪g, -(4 : ℝ) • (s.2 - xh)⟫ := by rw [hvec]
      _ = -4 * ⟪g, s.2 - xh⟫ := by
          rw [neg_smul, inner_neg_right, real_inner_smul_right]
          ring
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hk1 : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  have hcomb : (k : ℝ) * ⟪g, s.1 - y⟫ + 4 * ⟪g, xh - y⟫
      ≤ (k : ℝ) * (f s.1 - f y) + 4 * (f xh - f y) := by
    nlinarith
  rw [hin] at hcomb
  have hmul := mul_le_mul_of_nonneg_left hcomb hk1
  unfold dacWeight
  nlinarith

lemma dac_perturb {f : Point d → ℝ} {L η : ℝ} {xh : Point d} (k : ℕ) (s : Point d × Point d)
    (v : Point d)
    (hgr : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) :
    dacPotential f η xh (k + 1) (dacStep k η s v) ≤
      dacWeight (k + 1) * ((f (dacQuery k s) - f xh) + ⟪gradient f (dacQuery k s), -η • v⟫
        + L / 2 * ‖η • v‖ ^ 2)
        + (8 / η) * ‖(s.2 - xh) - (η * ((k : ℝ) + 1) / 4) • v‖ ^ 2 := by
  have h1 : f (dacQuery k s - η • v) - f xh
      ≤ (f (dacQuery k s) - f xh) + ⟪gradient f (dacQuery k s), -η • v⟫ + L / 2 * ‖η • v‖ ^ 2 := by
    have hz : dacQuery k s - η • v - dacQuery k s = -η • v := by module
    have hn : ‖-η • v‖ ^ 2 = ‖η • v‖ ^ 2 := by rw [neg_smul, norm_neg]
    have h := smooth_upper_bound (f := f) (oracle := gradient f) (L := L) hgr hlip
      (dacQuery k s) (dacQuery k s - η • v)
    rw [hz, hn] at h
    linarith
  have hw : 0 ≤ dacWeight (k + 1) := dacWeight_nonneg (k + 1)
  have h2 := mul_le_mul_of_nonneg_left h1 hw
  have h3 : s.2 - (η * ((k : ℝ) + 1) / 4) • v - xh
      = (s.2 - xh) - (η * ((k : ℝ) + 1) / 4) • v := by module
  unfold dacPotential dacStep
  dsimp only
  rw [h3]
  linarith

lemma dac_anchor {η : ℝ} (k : ℕ) {w g : Point d} (hη : 0 < η) :
    (8 / η) * ‖w - (η * ((k : ℝ) + 1) / 4) • g‖ ^ 2
      = (8 / η) * ‖w‖ ^ 2 - 4 * ((k : ℝ) + 1) * ⟪g, w⟫
        + (η * ((k : ℝ) + 1) ^ 2 / 2) * ‖g‖ ^ 2 := by
  have h1 : ⟪w, (η * ((k : ℝ) + 1) / 4) • g⟫ = (η * ((k : ℝ) + 1) / 4) * ⟪g, w⟫ := by
    rw [real_inner_smul_right, real_inner_comm w g]
  have h2 : ‖(η * ((k : ℝ) + 1) / 4) • g‖ ^ 2 = (η * ((k : ℝ) + 1) / 4) ^ 2 * ‖g‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [norm_sub_sq_real, h1, h2]
  field_simp [hη.ne']
  ring

lemma dac_algebra {L η : ℝ} (k : ℕ) (w g e : Point d) (hη : 0 < η) :
    dacWeight (k + 1) * (⟪g, -η • (g + e)⟫ + L / 2 * ‖η • (g + e)‖ ^ 2)
      + (8 / η) * ‖w - (η * ((k : ℝ) + 1) / 4) • (g + e)‖ ^ 2
    = (dacWeight (k + 1) * (L * η ^ 2 / 2) + η * ((k : ℝ) + 1) ^ 2 / 2) * ‖e‖ ^ 2
      + ⟪(dacWeight (k + 1) * (-η + L * η ^ 2)) • g
          - (4 * ((k : ℝ) + 1)) • (w - (η * ((k : ℝ) + 1) / 4) • g), e⟫
      + dacWeight (k + 1) * (-η * ‖g‖ ^ 2 + L * η ^ 2 / 2 * ‖g‖ ^ 2)
      + (8 / η) * ‖w - (η * ((k : ℝ) + 1) / 4) • g‖ ^ 2 := by
  have h1 : ‖η • (g + e)‖ ^ 2 = η ^ 2 * ‖g + e‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have h4 : w - (η * ((k : ℝ) + 1) / 4) • (g + e)
      = (w - (η * ((k : ℝ) + 1) / 4) • g) - (η * ((k : ℝ) + 1) / 4) • e := by
    rw [smul_add, sub_sub]
  have h5 : ‖(η * ((k : ℝ) + 1) / 4) • e‖ ^ 2 = (η * ((k : ℝ) + 1) / 4) ^ 2 * ‖e‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have h6 : ⟪g, -η • (g + e)⟫ = -η * (⟪g, g⟫ + ⟪g, e⟫) := by
    rw [inner_smul_right, inner_add_right, neg_mul]
  rw [h1, h4, h6, norm_add_sq_real, norm_sub_sq_real, h5]
  simp only [inner_smul_right, inner_sub_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, mul_add, add_mul, mul_sub, neg_mul, mul_comm, mul_left_comm,
    mul_assoc]
  field_simp [hη.ne']
  ring

lemma dac_det {f : Point d → ℝ} {L η ρ : ℝ} {xh : Point d} (k : ℕ) (s : Point d × Point d)
    (hη : 0 < η) (hLη : L * η ≤ 1) (hρη : ρ ^ 2 * ((k : ℝ) + 2) * η ≤ 1)
    (hc : ConvexOn ℝ Set.univ f)
    (hgr : ∀ x, HasGradientAt f (gradient f x) x)
    (hmin : IsMinOn f Set.univ xh) :
    dacWeight (k + 1) * (f (dacQuery k s) - f xh)
      + dacWeight (k + 1) * (-η * ‖gradient f (dacQuery k s)‖ ^ 2
          + L * η ^ 2 / 2 * ‖gradient f (dacQuery k s)‖ ^ 2)
      + (8 / η) * ‖(s.2 - xh) - (η * ((k : ℝ) + 1) / 4) • gradient f (dacQuery k s)‖ ^ 2
      + (dacWeight (k + 1) * (L * η ^ 2 / 2) + η * ((k : ℝ) + 1) ^ 2 / 2)
          * (2 * ρ ^ 2 * (f (dacQuery k s) - f xh))
    ≤ dacPotential f η xh k s := by
  set y : Point d := dacQuery k s
  set g : Point d := gradient f y
  set w : Point d := s.2 - xh
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hwk : dacWeight (k + 1) = ((k : ℝ) + 1) * ((k : ℝ) + 2) := dacWeight_succ k
  have hu0 : 0 ≤ f y - f xh := sub_nonneg.mpr (hmin (Set.mem_univ y))
  have hexp := dac_anchor k (w := w) (g := g) hη
  have htel := dac_telescope (xh := xh) k s hc hgr
  have hLη2 : L * η ^ 2 ≤ η := by nlinarith
  have hgcoef0 : dacWeight (k + 1) * (-η + L * η ^ 2 / 2) + η * ((k : ℝ) + 1) ^ 2 / 2 ≤ 0 := by
    rw [hwk]
    nlinarith
  have hgcoef : (dacWeight (k + 1) * (-η + L * η ^ 2 / 2) + η * ((k : ℝ) + 1) ^ 2 / 2)
      * ‖g‖ ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hgcoef0 (sq_nonneg _)
  have hcv : dacWeight (k + 1) * (L * η ^ 2 / 2) + η * ((k : ℝ) + 1) ^ 2 / 2
      ≤ ((k : ℝ) + 1) * ((k : ℝ) + 2) * η := by
    rw [hwk]
    nlinarith
  have hcv_rho : (dacWeight (k + 1) * (L * η ^ 2 / 2) + η * ((k : ℝ) + 1) ^ 2 / 2) * (2 * ρ ^ 2)
      ≤ 2 * ((k : ℝ) + 1) := by
    have h1 : (dacWeight (k + 1) * (L * η ^ 2 / 2) + η * ((k : ℝ) + 1) ^ 2 / 2) * (2 * ρ ^ 2)
        ≤ (((k : ℝ) + 1) * ((k : ℝ) + 2) * η) * (2 * ρ ^ 2) :=
      mul_le_mul_of_nonneg_right hcv (by positivity)
    have h2 : (((k : ℝ) + 1) * ((k : ℝ) + 2) * η) * (2 * ρ ^ 2)
        = 2 * ((k : ℝ) + 1) * (ρ ^ 2 * ((k : ℝ) + 2) * η) := by ring
    have h3 : 2 * ((k : ℝ) + 1) * (ρ ^ 2 * ((k : ℝ) + 2) * η) ≤ 2 * ((k : ℝ) + 1) := by
      nlinarith
    linarith
  have hnoise : (dacWeight (k + 1) * (L * η ^ 2 / 2) + η * ((k : ℝ) + 1) ^ 2 / 2)
        * (2 * ρ ^ 2 * (f y - f xh))
      ≤ 2 * ((k : ℝ) + 1) * (f y - f xh) := by
    have h := mul_le_mul_of_nonneg_right hcv_rho hu0
    linarith
  have hpot : dacPotential f η xh k s = dacWeight k * (f s.1 - f xh) + (8 / η) * ‖w‖ ^ 2 := rfl
  rw [hpot, hexp]
  have hgap : (dacWeight (k + 1) + 2 * ((k : ℝ) + 1)) * (f y - f xh)
      = ((k : ℝ) + 1) * ((k : ℝ) + 4) * (f y - f xh) := by
    rw [hwk]
    ring
  linarith

lemma dac_one_round {f : Point d → ℝ} {L η ρ : ℝ} {xh : Point d} (k : ℕ) (s : Point d × Point d)
    (_hL : 0 < L) (hη : 0 < η) (hLη : L * η ≤ 1) (hρη : ρ ^ 2 * ((k : ℝ) + 2) * η ≤ 1)
    (hc : ConvexOn ℝ Set.univ f)
    (hgr : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hmin : IsMinOn f Set.univ xh)
    {P : Measure Ω} [IsProbabilityMeasure P] (V : Ω → Point d)
    (hV : Integrable V P)
    (hdev : Integrable (fun ω => ‖V ω - gradient f (dacQuery k s)‖ ^ 2) P)
    (hmean : (∫ ω, V ω ∂P) = gradient f (dacQuery k s))
    (hvb : (∫ ω, ‖V ω - gradient f (dacQuery k s)‖ ^ 2 ∂P)
        ≤ 2 * ρ ^ 2 * (f (dacQuery k s) - f xh))
    (hmeas : AEStronglyMeasurable
      (fun ω => dacPotential f η xh (k + 1) (dacStep k η s (V ω))) P) :
    Integrable (fun ω => dacPotential f η xh (k + 1) (dacStep k η s (V ω))) P ∧
      (∫ ω, dacPotential f η xh (k + 1) (dacStep k η s (V ω)) ∂P) ≤ dacPotential f η xh k s := by
  classical
  set y : Point d := dacQuery k s
  set g : Point d := gradient f y
  set w : Point d := s.2 - xh
  set cv : ℝ := dacWeight (k + 1) * (L * η ^ 2 / 2) + η * ((k : ℝ) + 1) ^ 2 / 2
  set φ : Point d := (dacWeight (k + 1) * (-η + L * η ^ 2)) • g
    - (4 * ((k : ℝ) + 1)) • (w - (η * ((k : ℝ) + 1) / 4) • g)
  set Ddet : ℝ := dacWeight (k + 1) * (f y - f xh)
    + dacWeight (k + 1) * (-η * ‖g‖ ^ 2 + L * η ^ 2 / 2 * ‖g‖ ^ 2)
    + (8 / η) * ‖w - (η * ((k : ℝ) + 1) / 4) • g‖ ^ 2
  have hwk : 0 ≤ dacWeight (k + 1) := dacWeight_nonneg (k + 1)
  have hc0 : 0 ≤ cv := by positivity
  have hptw : ∀ ω, dacPotential f η xh (k + 1) (dacStep k η s (V ω))
      ≤ Ddet + ⟪φ, V ω - g⟫ + cv * ‖V ω - g‖ ^ 2 := by
    intro ω
    have he : V ω = g + (V ω - g) := by rw [add_comm, sub_add_cancel]
    have h1 := dac_perturb (f := f) (L := L) (η := η) (xh := xh) k s (V ω) hgr hlip
    have h2 := dac_algebra (L := L) (η := η) k w g (V ω - g) hη
    calc dacPotential f η xh (k + 1) (dacStep k η s (V ω))
        ≤ dacWeight (k + 1) * ((f y - f xh) + ⟪g, -η • V ω⟫ + L / 2 * ‖η • V ω‖ ^ 2)
            + (8 / η) * ‖w - (η * ((k : ℝ) + 1) / 4) • V ω‖ ^ 2 := h1
      _ = dacWeight (k + 1) * (f y - f xh)
          + (dacWeight (k + 1) * (⟪g, -η • (g + (V ω - g))⟫ + L / 2 * ‖η • (g + (V ω - g))‖ ^ 2)
            + (8 / η) * ‖w - (η * ((k : ℝ) + 1) / 4) • (g + (V ω - g))‖ ^ 2) := by
          conv_lhs => rw [he]
          ring
      _ = dacWeight (k + 1) * (f y - f xh)
          + (cv * ‖V ω - g‖ ^ 2 + ⟪φ, V ω - g⟫
            + dacWeight (k + 1) * (-η * ‖g‖ ^ 2 + L * η ^ 2 / 2 * ‖g‖ ^ 2)
            + (8 / η) * ‖w - (η * ((k : ℝ) + 1) / 4) • g‖ ^ 2) := by rw [h2]
      _ = Ddet + ⟪φ, V ω - g⟫ + cv * ‖V ω - g‖ ^ 2 := by ring
  set Lp : Point d →L[ℝ] ℝ := InnerProductSpace.toDual ℝ (Point d) φ
  have hpL : ∀ z : Point d, Lp z = ⟪φ, z⟫ := fun _ => rfl
  have hlin_int : Integrable (fun ω => ⟪φ, V ω - g⟫) P := by
    refine (Lp.integrable_comp (hV.sub (integrable_const g))).congr ?_
    exact ae_of_all _ fun ω => hpL (V ω - g)
  have hA : Integrable (fun ω => Ddet + ⟪φ, V ω - g⟫ + cv * ‖V ω - g‖ ^ 2) P :=
    ((integrable_const _).add hlin_int).add (hdev.const_mul cv)
  have hnonneg : ∀ ω, 0 ≤ dacPotential f η xh (k + 1) (dacStep k η s (V ω)) := by
    intro ω
    have h1 : 0 ≤ f (dacStep k η s (V ω)).1 - f xh := sub_nonneg.mpr (hmin (Set.mem_univ _))
    have h2 : 0 ≤ (8 / η) * ‖(dacStep k η s (V ω)).2 - xh‖ ^ 2 := by positivity
    unfold dacPotential
    nlinarith
  have hintegrable : Integrable (fun ω => dacPotential f η xh (k + 1) (dacStep k η s (V ω))) P :=
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
  have hmono : (∫ ω, dacPotential f η xh (k + 1) (dacStep k η s (V ω)) ∂P)
      ≤ ∫ ω, Ddet + ⟪φ, V ω - g⟫ + cv * ‖V ω - g‖ ^ 2 ∂P :=
    integral_mono_ae hintegrable hA (ae_of_all _ hptw)
  have hdet := dac_det (f := f) (L := L) (η := η) (ρ := ρ) (xh := xh) k s
    hη hLη hρη hc hgr hmin
  calc (∫ ω, dacPotential f η xh (k + 1) (dacStep k η s (V ω)) ∂P)
      ≤ ∫ ω, Ddet + ⟪φ, V ω - g⟫ + cv * ‖V ω - g‖ ^ 2 ∂P := hmono
    _ = Ddet + cv * ∫ ω, ‖V ω - g‖ ^ 2 ∂P := hsum
    _ ≤ Ddet + cv * (2 * ρ ^ 2 * (f y - f xh)) := by gcongr
    _ ≤ dacPotential f η xh k s := hdet

end OracleTemplate.SecantPolyak.AnchoredConvexPair

import LongTails.Proofs.DirectionMomentumRound
import LongTails.Proofs.GdConvex
import LongTails.Proofs.AuxiliaryInner
import LongTails.Proofs.InterpolatedProbeRound

set_option maxHeartbeats 2000000

/-!
Convex growth rounds. For a merely convex smoothed objective a descent step contracts the squared
distance to a reference point, and the decrease it buys is a multiple of the current smoothed gap.
Under growth noise the mean square deviation of a mirrored pair is proportional to that same gap, so
one round decreases the distance potential by a multiple of the gap. Averaging the iterates then
converts the accumulated distance drop into accuracy, which is the carrier a convex objective permits
in place of the geometric gap contraction available under strong convexity.
-/

namespace OracleTemplate.SecantPolyak.GrowthConvex

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
open OracleTemplate _root_.OracleTemplate.Gradient SecantDescent SecantPolyak
  SecantPolyak.Scheduled SecantPolyak.Centered SecantPolyak.DirectionSampled
open LongTails.Proofs.AuxiliaryInner
open LongTails.Setups.ZerothOrderSmoothAndConvex
open OracleTemplate.SecantPolyak.Interpolated (roundOf_devAt)

variable {Ω : Type} [MeasurableSpace Ω] {d : ℕ}

/-- Smoothness and a minimizer bound the squared gradient by the gap. -/
lemma grad_norm_sq_le {f : Point d → ℝ} {L : ℝ} {xh x : Point d} (hL : 0 < L)
    (hgr : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hmin : IsMinOn f Set.univ xh) :
    ‖gradient f x‖ ^ 2 ≤ 2 * L * (f x - f xh) := by
  have hd := descent hL hgr hlip x
  have h1 : f xh ≤ f (x - (1 / L) • gradient f x) := hmin (Set.mem_univ _)
  have h2 : ‖gradient f x‖ ^ 2 / (2 * L) ≤ f x - f xh := by linarith
  have h3 : 2 * L * (‖gradient f x‖ ^ 2 / (2 * L)) = ‖gradient f x‖ ^ 2 := by field_simp
  nlinarith

/-- The squared norm of an almost everywhere strongly measurable step direction. -/
lemma aes_norm_sq {E : Type} [NormedAddCommGroup E]
    {P : Measure Ω} {V : Ω → E} (hV : AEStronglyMeasurable V P) :
    AEStronglyMeasurable (fun ω => ‖V ω‖ ^ 2) P :=
  ((hV.norm).mul (hV.norm)).congr (ae_of_all _ fun _ω => (pow_two _).symm)

/-- A step direction whose deviation from a point has an integrable square also has an integrable
squared norm, dominated twice by that point and twice by the deviation. -/
lemma integrable_norm_sq_dev {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {P : Measure Ω} [IsProbabilityMeasure P] {V : Ω → E} {g : E}
    (hV : AEStronglyMeasurable V P) (hdev : Integrable (fun ω => ‖V ω - g‖ ^ 2) P) :
    Integrable (fun ω => ‖V ω‖ ^ 2) P := by
  refine ((integrable_const (2 * ‖g‖ ^ 2)).add (hdev.const_mul 2)).mono'
    (aes_norm_sq hV) (Filter.Eventually.of_forall fun ω => ?_)
  · have h2 : ‖g + (V ω - g)‖ ^ 2 ≤ 2 * ‖g‖ ^ 2 + 2 * ‖V ω - g‖ ^ 2 := norm_add_sq_le g (V ω - g)
    rw [show g + (V ω - g) = V ω from by abel] at h2
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact h2

/-- One inexact descent step against a convex objective: the expected squared distance to a
reference point drops by twice the step times the supporting gap and pays the step squared times the
second moment of the step direction. -/
lemma distance_step {f : Point d → ℝ} {η : ℝ} {xh x : Point d}
    (hη0 : 0 ≤ η)
    (hc : ConvexOn ℝ Set.univ f)
    (hgr : ∀ x, HasGradientAt f (gradient f x) x)
    {P : Measure Ω} [IsProbabilityMeasure P] (V : Ω → Point d) (v : ℝ)
    (hV : Integrable V P)
    (hdev : Integrable (fun ω => ‖V ω - gradient f x‖ ^ 2) P)
    (hmean : (∫ ω, V ω ∂P) = gradient f x)
    (hvb : (∫ ω, ‖V ω - gradient f x‖ ^ 2 ∂P) ≤ v) :
    Integrable (fun ω => ‖x - η • V ω - xh‖ ^ 2) P ∧
      (∫ ω, ‖x - η • V ω - xh‖ ^ 2 ∂P)
        ≤ ‖x - xh‖ ^ 2 - 2 * η * (f x - f xh) + η ^ 2 * (2 * ‖gradient f x‖ ^ 2 + 2 * v) := by
  classical
  set g0 : Point d := gradient f x with hg0
  set w : Point d := x - xh with hw
  have hdev2 : Integrable (fun ω : Ω => (2 : ℝ) * ‖V ω - g0‖ ^ 2) P := hdev.const_mul 2
  have hV2 : Integrable (fun ω => ‖V ω‖ ^ 2) P :=
    integrable_norm_sq_dev (g := g0) hV.aestronglyMeasurable hdev
  have hInt : Integrable (fun ω => ‖x - η • V ω - xh‖ ^ 2) P := by
    have hmain : Integrable (fun ω : Ω => (2 : ℝ) * ‖w‖ ^ 2 + 2 * η ^ 2 * ‖V ω‖ ^ 2) P :=
      (integrable_const (2 * ‖w‖ ^ 2)).add (hV2.const_mul (2 * η ^ 2))
    have hWaes : AEStronglyMeasurable (fun ω : Ω => x - η • V ω - xh) P :=
      (((integrable_const x).sub (hV.smul η)).sub (integrable_const xh)).aestronglyMeasurable
    refine hmain.mono' (aes_norm_sq hWaes) (Filter.Eventually.of_forall fun ω => ?_)
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h22 : ‖(η : ℝ) • V ω‖ ^ 2 = η ^ 2 * ‖V ω‖ ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      have h2 : ‖w - η • V ω‖ ^ 2 ≤ 2 * ‖w‖ ^ 2 + 2 * ‖(η : ℝ) • V ω‖ ^ 2 :=
        norm_sub_sq_le w _
      have h4 : x - η • V ω - xh = w - η • V ω := by
        show x - η • V ω - xh = (x - xh) - η • V ω
        module
      rw [h4]
      refine le_trans h2 ?_
      rw [h22]
      exact le_of_eq (by ring)
  set Lc : Point d →L[ℝ] ℝ := InnerProductSpace.toDual ℝ (Point d) w with hLcdef
  have hLc : ∀ y : Point d, Lc y = ⟪w, y⟫ := fun _ => rfl
  have hlin : (∫ ω, ⟪w, V ω⟫ ∂P) = ⟪w, gradient f x⟫ := by
    rw [show (fun ω : Ω => ⟪w, V ω⟫) = Lc ∘ V from funext fun ω => (hLc (V ω)).symm]
    exact ((Lc.integral_comp_comm hV).trans (congrArg Lc hmean)).trans (hLc (gradient f x))
  have hsq : ∀ ω, ‖V ω‖ ^ 2 ≤ 2 * ‖g0‖ ^ 2 + 2 * ‖V ω - g0‖ ^ 2 := fun ω => by
    have h2 := norm_add_sq_le g0 (V ω - g0)
    rw [show g0 + (V ω - g0) = V ω from by abel] at h2
    exact h2
  have hsqb : (∫ ω, ‖V ω‖ ^ 2 ∂P) ≤ 2 * ‖g0‖ ^ 2 + 2 * v := by
    have h1 : (∫ ω, ‖V ω‖ ^ 2 ∂P) ≤ ∫ ω, (2 * ‖g0‖ ^ 2 + 2 * ‖V ω - g0‖ ^ 2) ∂P :=
      integral_mono hV2 ((integrable_const _).add hdev2) fun ω => hsq ω
    have hA : (∫ ω, (2 * ‖g0‖ ^ 2 + 2 * ‖V ω - g0‖ ^ 2) ∂P)
        = ∫ ω, (2 * ‖g0‖ ^ 2 : ℝ) ∂P + ∫ ω, (2 : ℝ) * ‖V ω - g0‖ ^ 2 ∂P :=
      integral_add (integrable_const _) hdev2
    have hB : (∫ ω, (2 * ‖g0‖ ^ 2 : ℝ) ∂P) = 2 * ‖g0‖ ^ 2 := by
      rw [integral_const, probReal_univ, one_smul]
    have hC : (∫ ω, (2 : ℝ) * ‖V ω - g0‖ ^ 2 ∂P) = (2 : ℝ) * ∫ ω, ‖V ω - g0‖ ^ 2 ∂P := by
      have hC1 := integral_const_mul (μ := P) (2 : ℝ) (fun ω : Ω => ‖V ω - g0‖ ^ 2)
      exact hC1
    linarith
  have hpoint : ∀ ω, x - η • V ω - xh = w - η • V ω := by
    intro ω
    show x - η • V ω - xh = (x - xh) - η • V ω
    module
  have hVin : Integrable (fun ω => (2 : ℝ) * η * ⟪w, V ω⟫) P := (hV.const_inner w).const_mul (2 * η)
  have hLin : Integrable (fun ω : Ω => ‖w‖ ^ 2 - (2 : ℝ) * η * ⟪w, V ω⟫) P :=
    (integrable_const _).sub hVin
  have hexp : (∫ ω, ‖x - η • V ω - xh‖ ^ 2 ∂P)
      = ∫ ω, (‖w‖ ^ 2 - (2 : ℝ) * η * ⟪w, V ω⟫ + η ^ 2 * ‖V ω‖ ^ 2) ∂P := by
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    show ‖x - η • V ω - xh‖ ^ 2 = ‖w‖ ^ 2 - (2 : ℝ) * η * ⟪w, V ω⟫ + η ^ 2 * ‖V ω‖ ^ 2
    rw [hpoint ω, norm_sub_sq_real w (η • V ω)]
    have h2 : ‖(η : ℝ) • V ω‖ ^ 2 = η ^ 2 * ‖V ω‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have h3 : ⟪w, (η : ℝ) • V ω⟫ = η * ⟪w, V ω⟫ := real_inner_smul_right _ _ _
    rw [h2, h3]
    ring
  have hsplit : (∫ ω, (‖w‖ ^ 2 - (2 : ℝ) * η * ⟪w, V ω⟫ + η ^ 2 * ‖V ω‖ ^ 2) ∂P)
      = (∫ ω, ‖w‖ ^ 2 - (2 : ℝ) * η * ⟪w, V ω⟫ ∂P) + ∫ ω, η ^ 2 * ‖V ω‖ ^ 2 ∂P :=
    integral_add hLin (hV2.const_mul (η ^ 2))
  have hfin : (∫ ω, ‖w‖ ^ 2 - (2 : ℝ) * η * ⟪w, V ω⟫ ∂P)
      = ‖w‖ ^ 2 - (2 : ℝ) * η * ⟪w, gradient f x⟫ := by
    have hA : (∫ ω, ‖w‖ ^ 2 - (2 : ℝ) * η * ⟪w, V ω⟫ ∂P)
        = ∫ ω, (‖w‖ ^ 2 : ℝ) ∂P - ∫ ω, (2 : ℝ) * η * ⟪w, V ω⟫ ∂P :=
      integral_sub (integrable_const _) hVin
    have hB : (∫ ω, (‖w‖ ^ 2 : ℝ) ∂P) = ‖w‖ ^ 2 := by
      rw [integral_const, probReal_univ, one_smul]
    have hC : (∫ ω, (2 : ℝ) * η * ⟪w, V ω⟫ ∂P)
        = (2 : ℝ) * η * ∫ ω, ⟪w, V ω⟫ ∂P := by
      have hC1 := integral_const_mul (μ := P) ((2 : ℝ) * η) (fun ω : Ω => ⟪w, V ω⟫)
      exact hC1
    rw [hA, hB, hC, hlin]
  have hsup : ⟪gradient f x, xh - x⟫ ≤ f xh - f x := convex_support hc hgr x xh
  have hD : (∫ ω, η ^ 2 * ‖V ω‖ ^ 2 ∂P) = η ^ 2 * ∫ ω, ‖V ω‖ ^ 2 ∂P := by
    have h1 := integral_const_mul (μ := P) (η ^ 2) (fun ω : Ω => ‖V ω‖ ^ 2)
    exact h1
  have hpair : ⟪w, gradient f x⟫ ≥ f x - f xh := by
    have hneg : w = -(xh - x) := by
      rw [hw]
      module
    have hinner : ⟪w, gradient f x⟫ = -⟪xh - x, gradient f x⟫ := by
      rw [hneg, inner_neg_left]
    have hcomm : ⟪xh - x, gradient f x⟫ = ⟪gradient f x, xh - x⟫ := by
      simp only [real_inner_comm]
    linarith
  have hw2 : ‖w‖ ^ 2 = ‖x - xh‖ ^ 2 := by rw [hw]
  have hg02 : ‖g0‖ ^ 2 = ‖gradient f x‖ ^ 2 := by rw [hg0]
  refine ⟨hInt, ?_⟩
  rw [hexp, hsplit, hfin, hD]
  nlinarith

/-- One mirrored-pair round under growth noise decreases the squared distance to the surrogate
minimizer by `η` times the smoothed gap, provided `4 * η * (L + ρ ^ 2) ≤ 1`. -/
lemma gp_one_round {g : Point d → Ω → ℝ} {fh : Point d → ℝ}
    {W : Measure (Point d × Ω)} [IsProbabilityMeasure W]
    {L η h ρ : ℝ} {xh x : Point d}
    (hL : 0 < L) (hη0 : 0 ≤ η) (hη : 4 * η * (L + ρ ^ 2) ≤ 1)
    (hc : ConvexOn ℝ Set.univ fh)
    (hgr : ∀ x, HasGradientAt fh (gradient fh x) x)
    (hlip : ∀ x y, ‖gradient fh x - gradient fh y‖ ≤ L * ‖x - y‖)
    (hminh : IsMinOn fh Set.univ xh)
    (hg : Measurable (Function.uncurry g))
    (hint : ∀ x s, Integrable (fun u : Point d × Ω =>
        slotVal h g x s u - halfGrad fh x s) (W))
    (hmean : ∀ x s, (∫ u : Point d × Ω, slotVal h g x s u ∂(W)) = halfGrad fh x s)
    (hvar2 : ∀ x s, Integrable (fun u : Point d × Ω =>
        ‖slotVal h g x s u - halfGrad fh x s‖ ^ 2) (W))
    (hvar : ∀ s, (∫ u : Point d × Ω, ‖slotVal h g x s u - halfGrad fh x s‖ ^ 2 ∂(W))
        ≤ ρ ^ 2 * (fh x - fh xh)) :
    Integrable (fun ω : secantSpace 1 1 → Point d × Ω =>
        ‖x - η • roundOf h g x 1 ω - xh‖ ^ 2) (slotLaw 1 1 (W)) ∧
      (∫ ω : secantSpace 1 1 → Point d × Ω,
          ‖x - η • roundOf h g x 1 ω - xh‖ ^ 2 ∂(slotLaw 1 1 (W)))
        ≤ ‖x - xh‖ ^ 2 - η * (fh x - fh xh) := by
  classical
  obtain ⟨hdv, hdb⟩ := roundOf_devAt (m := 1) (g := g) (fh := fh) (h := h) (x := x) (W := W)
    (v := ρ ^ 2 * (fh x - fh xh)) hg hint hmean hvar2 hvar Nat.one_pos
  have hVin : Integrable (fun ω : secantSpace 1 1 → Point d × Ω => roundOf h g x 1 ω)
      (slotLaw 1 1 (W)) := roundOf_integrable (m := 1) hint x
  have hmeanR : (∫ ω : secantSpace 1 1 → Point d × Ω, roundOf h g x 1 ω ∂(slotLaw 1 1 (W)))
      = gradient fh x :=
    roundOf_mean (m := 1) (g := g) (fh := fh) (h := h) hg hint hmean Nat.one_pos x
  obtain ⟨hi, hb⟩ := distance_step (f := fh) (η := η) (xh := xh) (x := x)
    (V := fun ω : secantSpace 1 1 → Point d × Ω => roundOf h g x 1 ω)
    (v := 2 * (ρ ^ 2 * (fh x - fh xh))) hη0 hc hgr hVin hdv hmeanR (by simpa using hdb)
  have h0 : 0 ≤ fh x - fh xh := sub_nonneg.mpr (hminh (Set.mem_univ x))
  have hgn : ‖gradient fh x‖ ^ 2 ≤ 2 * L * (fh x - fh xh) := grad_norm_sq_le hL hgr hlip hminh
  refine ⟨hi, ?_⟩
  have h2 : (4 : ℝ) * η ^ 2 * (L + ρ ^ 2) ≤ η := by nlinarith
  have h3 : (4 : ℝ) * L * η ^ 2 * (fh x - fh xh) + 4 * ρ ^ 2 * η ^ 2 * (fh x - fh xh)
      ≤ η * (fh x - fh xh) := by
    have h31 : (4 : ℝ) * η ^ 2 * (L + ρ ^ 2) * (fh x - fh xh) ≤ η * (fh x - fh xh) :=
      mul_le_mul_of_nonneg_right h2 h0
    nlinarith
  have h4 : 2 * η ^ 2 * ‖gradient fh x‖ ^ 2 ≤ 4 * L * η ^ 2 * (fh x - fh xh) := by
    have h41 : 2 * η ^ 2 * (2 * L * (fh x - fh xh)) = 4 * L * η ^ 2 * (fh x - fh xh) := by ring
    rw [← h41]
    exact mul_le_mul_of_nonneg_left hgn (by nlinarith : (0 : ℝ) ≤ 2 * η ^ 2)
  nlinarith

end OracleTemplate.SecantPolyak.GrowthConvex

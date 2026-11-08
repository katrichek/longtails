import LongTails.Algorithms.GradedAnchoredPairAcceleration
import LongTails.Proofs.DampedAnchoredStep
import LongTails.Proofs.GdConvex

set_option maxHeartbeats 2000000

/-!
One round of weighted anchored pair acceleration. The anchor weight `β` is a free parameter of the
potential `f x - f xh + β * ‖z - xh‖²`, and the anchor moves by `θ / (2 * β)` times the round
surrogate, which is the weight the accelerated telescoping cancels with. The probe deviation enters
with coefficient `β * (θ / (2 * β))² = θ² / (4 * β)` and the potential leaves a negative
`θ * (μ / 2 - β) * ‖y - xh‖²`, so a surrogate whose mean-square deviation is `v` times the smoothed
gap is absorbed exactly when `(L * η² / 2 + θ² / (4 * β)) * v ≤ θ * (μ / 2 - β) * (2 / L)`. Mirrored
batching drives `v` down to `2 * ρ² / m` without any restriction on `ρ`.
-/

namespace OracleTemplate.SecantPolyak.GradedAnchored

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
open OracleTemplate SecantDescent InexactGradient
open _root_.OracleTemplate.Gradient
open LongTails.Setups.ZerothOrderSmoothAndConvex (Point)
open OracleTemplate.SecantPolyak.AnchoredPair

variable {Ω : Type} [MeasurableSpace Ω] {d : ℕ}

/-- Weighted anchored potential: the smoothed gap of the iterate plus `β` times the squared anchor
displacement from the minimizer. -/
noncomputable def waPotential (f : Point d → ℝ) (β : ℝ) (xh : Point d) (s : Point d × Point d) : ℝ :=
  f s.1 - f xh + β * ‖s.2 - xh‖ ^ 2

/-- Pointwise expansion of one weighted anchored round. -/
lemma wa_perturb {f : Point d → ℝ} {L β θ η : ℝ} {xh : Point d} (s : Point d × Point d)
    (v : Point d)
    (hgr : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) :
    waPotential f β xh (waStep β θ η s v) ≤
      (f (query θ s) - f xh) + ⟪gradient f (query θ s), -η • v⟫ + L / 2 * ‖η • v‖ ^ 2
        + β * ‖(1 - θ) • (s.2 - xh) + θ • (query θ s - xh) - (θ / (2 * β)) • v‖ ^ 2 := by
  classical
  have h1 : f (query θ s - η • v) - f xh
      ≤ f (query θ s) + ⟪gradient f (query θ s), -η • v⟫ + L / 2 * ‖η • v‖ ^ 2 - f xh := by
    have hz : query θ s - η • v - query θ s = -η • v := by module
    have hn : ‖-η • v‖ ^ 2 = ‖η • v‖ ^ 2 := by rw [neg_smul, norm_neg]
    have h := smooth_upper_bound (f := f) (oracle := gradient f) (L := L) hgr hlip
      (query θ s) (query θ s - η • v)
    rw [hz, hn] at h
    linarith
  have h3 : (1 - θ) • s.2 + θ • query θ s - (θ / (2 * β)) • v - xh
      = (1 - θ) • (s.2 - xh) + θ • (query θ s - xh) - (θ / (2 * β)) • v := by
    rw [sub_smul, sub_smul]
    module
  have h4 : β * ‖(1 - θ) • s.2 + θ • query θ s - (θ / (2 * β)) • v - xh‖ ^ 2
      = β * ‖(1 - θ) • (s.2 - xh) + θ • (query θ s - xh) - (θ / (2 * β)) • v‖ ^ 2 := by
    rw [h3]
  have h5 := add_le_add h1 (le_of_eq h4)
  calc waPotential f β xh (waStep β θ η s v)
      = f (query θ s - η • v) - f xh
        + β * ‖(1 - θ) • s.2 + θ • query θ s - (θ / (2 * β)) • v - xh‖ ^ 2 := rfl
    _ ≤ f (query θ s) + ⟪gradient f (query θ s), -η • v⟫ + L / 2 * ‖η • v‖ ^ 2 - f xh
        + β * ‖(1 - θ) • (s.2 - xh) + θ • (query θ s - xh) - (θ / (2 * β)) • v‖ ^ 2 := h5
    _ = (f (query θ s) - f xh) + ⟪gradient f (query θ s), -η • v⟫ + L / 2 * ‖η • v‖ ^ 2
        + β * ‖(1 - θ) • (s.2 - xh) + θ • (query θ s - xh) - (θ / (2 * β)) • v‖ ^ 2 := by ring

/-- Expansion of the anchor term: the cross term carries the telescoping coefficient `θ`, and the
gradient term the noise coefficient `θ² / (4 β)`. -/
lemma wa_anchor {β θ : ℝ} {w g : Point d} (hβ : 0 < β) :
    β * ‖w - (θ / (2 * β)) • g‖ ^ 2
      = β * ‖w‖ ^ 2 - θ * ⟪g, w⟫ + θ ^ 2 / (4 * β) * ‖g‖ ^ 2 := by
  have h1 : ⟪w, (θ / (2 * β)) • g⟫ = (θ / (2 * β)) * ⟪g, w⟫ := by
    rw [real_inner_smul_right, real_inner_comm w g]
  have h2 : ‖(θ / (2 * β)) • g‖ ^ 2 = (θ / (2 * β)) ^ 2 * ‖g‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [norm_sub_sq_real, h1, h2]
  field_simp [hβ.ne']
  ring

/-- Algebraic expansion of the two surrogate terms of one weighted anchored update. -/
lemma wa_algebra {L β θ η : ℝ} (w g e : Point d) (hβ : 0 < β) :
    ⟪g, -η • (g + e)⟫ + L / 2 * ‖η • (g + e)‖ ^ 2
      + β * ‖w - (θ / (2 * β)) • (g + e)‖ ^ 2
    = (L * η ^ 2 / 2 + θ ^ 2 / (4 * β)) * ‖e‖ ^ 2
      + ⟪(-η + L * η ^ 2) • g - θ • (w - (θ / (2 * β)) • g), e⟫
      - η * ‖g‖ ^ 2 + L * η ^ 2 / 2 * ‖g‖ ^ 2
      + β * ‖w - (θ / (2 * β)) • g‖ ^ 2 := by
  have h1 : ‖η • (g + e)‖ ^ 2 = η ^ 2 * ‖g + e‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have h4 : w - (θ / (2 * β)) • (g + e) = (w - (θ / (2 * β)) • g) - (θ / (2 * β)) • e := by
    rw [smul_add, sub_sub]
  have h5 : ‖(θ / (2 * β)) • e‖ ^ 2 = (θ / (2 * β)) ^ 2 * ‖e‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have h6 : ⟪g, -η • (g + e)⟫ = -η * (⟪g, g⟫ + ⟪g, e⟫) := by
    rw [inner_smul_right, inner_add_right, neg_mul]
  rw [h1, h4, h6, norm_add_sq_real, norm_sub_sq_real, h5]
  simp only [inner_smul_right, inner_sub_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, mul_add, add_mul, mul_sub, neg_mul, mul_comm, mul_left_comm,
    mul_assoc]
  field_simp [hβ.ne']
  ring

/-- Deterministic core of one weighted anchored round: the mean part of the potential contracts. -/
lemma wa_det {f : Point d → ℝ} {L μ β θ η v : ℝ} {xh : Point d} (s : Point d × Point d)
    (hL : 0 < L) (hμ : 0 < μ) (hβ : 0 < β) (hβh : β ≤ μ / 2) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hcap1 : θ ^ 2 / (4 * β) ≤ η - L * η ^ 2 / 2)
    (hcap3 : (L * η ^ 2 / 2 + θ ^ 2 / (4 * β)) * v ≤ θ * (μ / 2 - β) * (2 / L))
    (hgr : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hsc : ∀ x y, f x + ⟪gradient f x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (hmin : IsMinOn f Set.univ xh) :
    (f (query θ s) - f xh) - η * ‖gradient f (query θ s)‖ ^ 2
        + (L * η ^ 2 / 2) * ‖gradient f (query θ s)‖ ^ 2
        + β * ‖(1 - θ) • (s.2 - xh) + θ • (query θ s - xh)
            - (θ / (2 * β)) • gradient f (query θ s)‖ ^ 2
        + (L * η ^ 2 / 2 + θ ^ 2 / (4 * β)) * (v * (f (query θ s) - f xh))
      ≤ (1 - θ) * waPotential f β xh s := by
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
  have htel := ap_telescope hμ.le hθ0 hθ1 hyq (hsc y xh) (hsc y s.1)
  have hneg : -(θ * ⟪g, w⟫)
      ≤ -(θ * (f y - f xh + μ / 2 * ‖y - xh‖ ^ 2) + (1 - θ) * (f y - f s.1)) := by linarith
  have hbm : 0 ≤ μ / 2 - β := by linarith
  have hcap0 : 0 ≤ θ * (μ / 2 - β) := by positivity
  have hw2 : β * ‖w‖ ^ 2 ≤ β * ((1 - θ) * ‖s.2 - xh‖ ^ 2 + θ * ‖y - xh‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hj hβ.le
  have hexp : β * ‖w - (θ / (2 * β)) • g‖ ^ 2
      = β * ‖w‖ ^ 2 - θ * ⟪g, w⟫ + θ ^ 2 / (4 * β) * ‖g‖ ^ 2 :=
    wa_anchor (β := β) (θ := θ) (w := w) (g := g) hβ
  have hgcoef0 : θ ^ 2 / (4 * β) - η + L * η ^ 2 / 2 ≤ 0 := by linarith [hcap1]
  have hgcoef : (θ ^ 2 / (4 * β) - η + L * η ^ 2 / 2) * ‖g‖ ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hgcoef0 (sq_nonneg _)
  have hnoise : (L * η ^ 2 / 2 + θ ^ 2 / (4 * β)) * (v * (f y - f xh))
      ≤ θ * (μ / 2 - β) * (2 / L * (f y - f xh)) := by
    have h := mul_le_mul_of_nonneg_right hcap3 hu0
    calc (L * η ^ 2 / 2 + θ ^ 2 / (4 * β)) * (v * (f y - f xh))
        = ((L * η ^ 2 / 2 + θ ^ 2 / (4 * β)) * v) * (f y - f xh) := (mul_assoc _ _ _).symm
      _ ≤ (θ * (μ / 2 - β) * (2 / L)) * (f y - f xh) := h
      _ = θ * (μ / 2 - β) * (2 / L * (f y - f xh)) := mul_assoc _ _ _
  have hYneg : -(θ * (μ / 2 - β) * ‖y - xh‖ ^ 2)
      ≤ -(θ * (μ / 2 - β) * (2 / L * (f y - f xh))) := by
    have h := mul_le_mul_of_nonneg_left hY hcap0
    linarith
  have hpot : waPotential f β xh s = f s.1 - f xh + β * ‖s.2 - xh‖ ^ 2 := rfl
  rw [hpot]
  simp only [hydef, hgdef, hwdef] at *
  nlinarith [sq_nonneg ‖s.2 - xh‖, sq_nonneg ‖y - xh‖, hθ0.le, hL.le]

/-- One round of weighted anchored pair acceleration in expectation. -/
lemma wa_one_round {f : Point d → ℝ} {L μ β θ η v : ℝ} {xh : Point d} (s : Point d × Point d)
    (hL : 0 < L) (hμ : 0 < μ) (hβ : 0 < β) (hβh : β ≤ μ / 2) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hcap1 : θ ^ 2 / (4 * β) ≤ η - L * η ^ 2 / 2)
    (hcap3 : (L * η ^ 2 / 2 + θ ^ 2 / (4 * β)) * v ≤ θ * (μ / 2 - β) * (2 / L))
    (hgr : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hsc : ∀ x y, f x + ⟪gradient f x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (hmin : IsMinOn f Set.univ xh)
    {P : Measure Ω} [IsProbabilityMeasure P] (V : Ω → Point d)
    (hV : Integrable V P)
    (hdev : Integrable (fun ω => ‖V ω - gradient f (query θ s)‖ ^ 2) P)
    (hmean : (∫ ω, V ω ∂P) = gradient f (query θ s))
    (hvb : (∫ ω, ‖V ω - gradient f (query θ s)‖ ^ 2 ∂P)
        ≤ v * (f (query θ s) - f xh))
    (hmeas : AEStronglyMeasurable
      (fun ω => waPotential f β xh (waStep β θ η s (V ω))) P) :
    Integrable (fun ω => waPotential f β xh (waStep β θ η s (V ω))) P ∧
      (∫ ω, waPotential f β xh (waStep β θ η s (V ω)) ∂P) ≤ (1 - θ) * waPotential f β xh s := by
  classical
  set y : Point d := query θ s with hydef
  set g : Point d := gradient f y with hgdef
  set w : Point d := (1 - θ) • (s.2 - xh) + θ • (y - xh) with hwdef
  set cv : ℝ := L * η ^ 2 / 2 + θ ^ 2 / (4 * β) with hcvdef
  set φ : Point d := (-η + L * η ^ 2) • g - θ • (w - (θ / (2 * β)) • g) with hhdef
  set Ddet : ℝ := (f y - f xh) - η * ‖g‖ ^ 2 + (L * η ^ 2 / 2) * ‖g‖ ^ 2
    + β * ‖w - (θ / (2 * β)) • g‖ ^ 2 with hDdef
  have hc0 : 0 ≤ cv := by positivity
  have hptw : ∀ ω, waPotential f β xh (waStep β θ η s (V ω))
      ≤ Ddet + ⟪φ, V ω - g⟫ + cv * ‖V ω - g‖ ^ 2 := by
    intro ω
    have he : V ω = g + (V ω - g) := by rw [add_comm, sub_add_cancel]
    have h1 := wa_perturb (f := f) (L := L) (β := β) (θ := θ) (η := η) (xh := xh) s (V ω) hgr
      hlip
    have h2 := wa_algebra (L := L) (β := β) (θ := θ) (η := η) w g (V ω - g) hβ
    calc waPotential f β xh (waStep β θ η s (V ω))
        ≤ (f y - f xh) + ⟪g, -η • V ω⟫ + L / 2 * ‖η • V ω‖ ^ 2
            + β * ‖w - (θ / (2 * β)) • V ω‖ ^ 2 := h1
      _ = (f y - f xh)
          + (⟪g, -η • (g + (V ω - g))⟫ + L / 2 * ‖η • (g + (V ω - g))‖ ^ 2
            + β * ‖w - (θ / (2 * β)) • (g + (V ω - g))‖ ^ 2) := by
          conv_lhs => rw [he]
          ring
      _ = (f y - f xh)
          + (cv * ‖V ω - g‖ ^ 2 + ⟪φ, V ω - g⟫ - η * ‖g‖ ^ 2 + L * η ^ 2 / 2 * ‖g‖ ^ 2
            + β * ‖w - (θ / (2 * β)) • g‖ ^ 2) := by rw [h2]
      _ = Ddet + ⟪φ, V ω - g⟫ + cv * ‖V ω - g‖ ^ 2 := by ring
  set Lp : Point d →L[ℝ] ℝ := InnerProductSpace.toDual ℝ (Point d) φ with hlpdef
  have hpL : ∀ z : Point d, Lp z = ⟪φ, z⟫ := fun _ => rfl
  have hlin_int : Integrable (fun ω => ⟪φ, V ω - g⟫) P := by
    refine (Lp.integrable_comp (hV.sub (integrable_const g))).congr ?_
    exact ae_of_all _ fun ω => hpL (V ω - g)
  have hA : Integrable (fun ω => Ddet + ⟪φ, V ω - g⟫ + cv * ‖V ω - g‖ ^ 2) P :=
    ((integrable_const _).add hlin_int).add (hdev.const_mul cv)
  have hnonneg : ∀ ω, 0 ≤ waPotential f β xh (waStep β θ η s (V ω)) := by
    intro ω
    have h1 : 0 ≤ f (waStep β θ η s (V ω)).1 - f xh := sub_nonneg.mpr (hmin (Set.mem_univ _))
    have h2 : 0 ≤ β * ‖(waStep β θ η s (V ω)).2 - xh‖ ^ 2 := by positivity
    show 0 ≤ f (waStep β θ η s (V ω)).1 - f xh + β * ‖(waStep β θ η s (V ω)).2 - xh‖ ^ 2
    linarith
  have hintegrable : Integrable (fun ω => waPotential f β xh (waStep β θ η s (V ω))) P :=
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
  have hmono : (∫ ω, waPotential f β xh (waStep β θ η s (V ω)) ∂P)
      ≤ ∫ ω, Ddet + ⟪φ, V ω - g⟫ + cv * ‖V ω - g‖ ^ 2 ∂P :=
    integral_mono_ae hintegrable hA (ae_of_all _ hptw)
  have hnoise : cv * ∫ ω, ‖V ω - g‖ ^ 2 ∂P ≤ cv * (v * (f y - f xh)) :=
    mul_le_mul_of_nonneg_left hvb hc0
  have hdet := wa_det (f := f) (L := L) (μ := μ) (β := β) (θ := θ) (η := η) (v := v) (xh := xh) s
    hL hμ hβ hβh hθ0 hθ1 hcap1 hcap3 hgr hlip hsc hmin
  calc (∫ ω, waPotential f β xh (waStep β θ η s (V ω)) ∂P)
      ≤ ∫ ω, Ddet + ⟪φ, V ω - g⟫ + cv * ‖V ω - g‖ ^ 2 ∂P := hmono
    _ = Ddet + cv * ∫ ω, ‖V ω - g‖ ^ 2 ∂P := hsum
    _ ≤ Ddet + cv * (v * (f y - f xh)) := by gcongr
    _ ≤ (1 - θ) * waPotential f β xh s := hdet

end OracleTemplate.SecantPolyak.GradedAnchored

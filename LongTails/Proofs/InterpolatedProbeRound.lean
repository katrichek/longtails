import LongTails.Proofs.DirectionMomentumRound
import LongTails.Proofs.GdConvex
import LongTails.Proofs.PLHessianGeometry

set_option maxHeartbeats 2000000

/-!
Interpolated (strong growth) rounds. Under the strong growth model a probe's mean square deviation
is bounded by the current smoothed gap, so the deviation of a mirrored pair is bounded by twice that
gap rather than by a fixed noise level. A single gradient step then contracts the expected gap by a
constant factor, which is what turns the budget from `1 / ε` into a logarithm.
-/

namespace OracleTemplate.SecantPolyak.Interpolated

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
open OracleTemplate _root_.OracleTemplate.Gradient SecantDescent SecantPolyak
  SecantPolyak.Scheduled SecantPolyak.Centered SecantPolyak.DirectionSampled
open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {Ω : Type} [MeasurableSpace Ω] {d : ℕ}

/-- Independent probes divide the mean square deviation of the round surrogate by `m`, with the
deviation bound taken only at the point being probed. -/
lemma roundOf_devAt {m : ℕ} {W : Measure (Point d × Ω)} [IsProbabilityMeasure W]
    {g : Point d → Ω → ℝ} {fh : Point d → ℝ} {h : ℝ} {x : Point d} {v : ℝ}
    (hg : Measurable (Function.uncurry g))
    (hint : ∀ x s, Integrable (fun u : Point d × Ω => slotVal h g x s u - halfGrad fh x s) W)
    (hmean : ∀ x s, (∫ u : Point d × Ω, slotVal h g x s u ∂W) = halfGrad fh x s)
    (hvar2 : ∀ x s, Integrable (fun u : Point d × Ω =>
        ‖slotVal h g x s u - halfGrad fh x s‖ ^ 2) W)
    (hvarx : ∀ s, (∫ u : Point d × Ω, ‖slotVal h g x s u - halfGrad fh x s‖ ^ 2 ∂W) ≤ v)
    (hm : 0 < m) :
    Integrable (fun a : secantSpace 1 m → Point d × Ω => ‖roundOf h g x m a - gradient fh x‖ ^ 2)
        (slotLaw 1 m W) ∧
      (∫ a : secantSpace 1 m → Point d × Ω, ‖roundOf h g x m a - gradient fh x‖ ^ 2
          ∂(slotLaw 1 m W)) ≤ 2 * v / (m : ℝ) := by
  classical
  have hZm (t : secantSpace 1 m) : Measurable (fun a : secantSpace 1 m → Point d × Ω =>
      slotDev h g fh x m a t) :=
    (cellDev_measurable hg h fh x t.2.2).comp (measurable_pi_apply t)
  have hZi (t : secantSpace 1 m) : Integrable (fun a : secantSpace 1 m → Point d × Ω =>
      slotDev h g fh x m a t) (slotLaw 1 m W) :=
    (preserving_slotEval W t).integrable_comp_of_integrable (ε := Point d)
      (cellDev_integrable hint x t.2.2)
  have hZ0 (t : secantSpace 1 m) :
      (∫ a : secantSpace 1 m → Point d × Ω, slotDev h g fh x m a t ∂(slotLaw 1 m W)) = 0 :=
    ((Centered.integral_comp_preserving_point (preserving_slotEval W t)
      (cellDev_integrable hint x t.2.2))).trans (cellDev_integral hint hmean x t.2.2)
  have hn2 (t : secantSpace 1 m) :
      (fun a : secantSpace 1 m → Point d × Ω => ‖slotDev h g fh x m a t‖ ^ 2)
      = (fun a => ‖slotVal h g x t.2.2 (a t) - halfGrad fh x t.2.2‖ ^ 2) := by
    refine funext fun a => ?_
    show ‖slotDev h g fh x m a t‖ ^ 2 = ‖slotVal h g x t.2.2 (a t) - halfGrad fh x t.2.2‖ ^ 2
    rw [show slotDev h g fh x m a t = cellDev h g fh x t.2.2 (a t) from rfl,
      cellDev_norm h g fh x t.2.2 (a t)]
  have hcu2 (t : secantSpace 1 m) : Integrable
      (fun u : Point d × Ω => ‖slotVal h g x t.2.2 u - halfGrad fh x t.2.2‖ ^ 2) W :=
    hvar2 x t.2.2
  have hZ2 (t : secantSpace 1 m) :
      Integrable (fun a => ‖slotDev h g fh x m a t‖ ^ 2) (slotLaw 1 m W) := by
    rw [hn2]
    exact (preserving_slotEval W t).integrable_comp_of_integrable (ε := ℝ) (hcu2 t)
  have hint2 (t : secantSpace 1 m) :
      Integrable (fun u : Point d × Ω => ‖cellDev h g fh x t.2.2 u‖ ^ 2) W :=
    (hvar2 x t.2.2).congr (ae_of_all _ fun u => congrArg (fun v : ℝ => v ^ 2)
      (cellDev_norm h g fh x t.2.2 u).symm)
  have hZb (t : secantSpace 1 m) : (∫ a : secantSpace 1 m → Point d × Ω,
      ‖slotDev h g fh x m a t‖ ^ 2 ∂(slotLaw 1 m W)) ≤ v := by
    have hc2 : (∫ a : secantSpace 1 m → Point d × Ω, ‖cellDev h g fh x t.2.2 (a t)‖ ^ 2
          ∂(slotLaw 1 m W))
        = ∫ u : Point d × Ω, ‖cellDev h g fh x t.2.2 u‖ ^ 2 ∂W :=
        ZerothOrder.integral_comp_preserving (preserving_slotEval W t) (hint2 t)
    calc (∫ a : secantSpace 1 m → Point d × Ω, ‖slotDev h g fh x m a t‖ ^ 2 ∂(slotLaw 1 m W))
        = ∫ a : secantSpace 1 m → Point d × Ω, ‖cellDev h g fh x t.2.2 (a t)‖ ^ 2
            ∂(slotLaw 1 m W) :=
            integral_congr_ae (ae_of_all _ fun a => rfl)
      _ = ∫ u : Point d × Ω, ‖cellDev h g fh x t.2.2 u‖ ^ 2 ∂W := hc2
      _ ≤ v := by
            have he : (fun u : Point d × Ω => ‖cellDev h g fh x t.2.2 u‖ ^ 2)
                = fun u : Point d × Ω => ‖slotVal h g x t.2.2 u - halfGrad fh x t.2.2‖ ^ 2 := by
              funext u
              rw [cellDev_norm h g fh x t.2.2 u]
            rw [he]
            exact hvarx t.2.2
  have hind : iIndepFun (fun t a => slotDev h g fh x m a t) (slotLaw 1 m W) := by
    show iIndepFun (fun (t : secantSpace 1 m) (a : secantSpace 1 m → Point d × Ω) =>
        cellDev h g fh x t.2.2 (a t)) (Measure.pi (fun _ : secantSpace 1 m => W))
    refine iIndepFun_pi (X := fun (t : secantSpace 1 m) (u : Point d × Ω) =>
        cellDev h g fh x t.2.2 u) ?_
    intro t
    exact (cellDev_measurable hg h fh x t.2.2).aemeasurable
  obtain ⟨hSi, hS⟩ := RobustGradient.independent_sum_second_moment
    (fun t a => slotDev h g fh x m a t) hind hZi hZ2 hZ0
  have hcard : ((Fintype.card (secantSpace 1 m) : ℕ) : ℝ) = (2 : ℝ) * (m : ℝ) := by
    rw [card_secantSpace]
    push_cast
    ring
  have hG : (1 / (m : ℝ)) • ∑ _ : secantSpace 1 m, ((1 / 2 : ℝ) • gradient fh x : Point d)
      = gradient fh x := hsumv (d := d) (m := m) hm _
  have hsg (s : Bool) : (if s then (1 : ℝ) else (-1 : ℝ)) • halfGrad fh x s
      = (1 / 2 : ℝ) • gradient fh x := by
    cases s <;> simp [halfGrad]
  have hid (a : secantSpace 1 m → Point d × Ω) :
      roundOf h g x m a - gradient fh x
      = (1 / (m : ℝ)) • ∑ t : secantSpace 1 m, slotDev h g fh x m a t := by
    unfold roundOf
    symm
    calc (1 / (m : ℝ)) • ∑ t : secantSpace 1 m, cellDev h g fh x t.2.2 (a t)
        = (1 / (m : ℝ)) • ∑ t : secantSpace 1 m,
            ((if t.2.2 then (1 : ℝ) else (-1 : ℝ)) • slotVal h g x t.2.2 (a t)
              - (1 / 2 : ℝ) • gradient fh x) := by
              refine congrArg (fun v => (1 / (m : ℝ)) • v) (Finset.sum_congr rfl ?_)
              intro t _
              rw [cellDev_eq h g fh x t.2.2 (a t), smul_sub, hsg t.2.2]
      _ = (1 / (m : ℝ)) • (∑ t : secantSpace 1 m,
              (if t.2.2 then (1 : ℝ) else (-1 : ℝ)) • slotVal h g x t.2.2 (a t)
            - ∑ t : secantSpace 1 m, (1 / 2 : ℝ) • gradient fh x) := by
              rw [Finset.sum_sub_distrib]
      _ = (1 / (m : ℝ)) • ∑ t : secantSpace 1 m,
              (if t.2.2 then (1 : ℝ) else (-1 : ℝ)) • slotVal h g x t.2.2 (a t)
            - gradient fh x := by rw [smul_sub, hG]
  have hsq (a : secantSpace 1 m → Point d × Ω) : ‖roundOf h g x m a - gradient fh x‖ ^ 2
      = ((1 / (m : ℝ)) ^ 2) * ‖∑ t : secantSpace 1 m, slotDev h g fh x m a t‖ ^ 2 := by
    rw [hid a, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (m : ℝ)), mul_pow]
  refine ⟨(Integrable.smul ((1 / (m : ℝ)) ^ 2) hSi).congr (ae_of_all _ fun a => (hsq a).symm), ?_⟩
  have h1 : (∫ a : secantSpace 1 m → Point d × Ω, ‖roundOf h g x m a - gradient fh x‖ ^ 2
        ∂(slotLaw 1 m W))
      = ((1 / (m : ℝ)) ^ 2) *
        ∫ a : secantSpace 1 m → Point d × Ω, ‖∑ t : secantSpace 1 m, slotDev h g fh x m a t‖ ^ 2
          ∂(slotLaw 1 m W) := by
    refine (integral_congr_ae (ae_of_all _ fun a => hsq a)).trans (integral_const_mul _ _)
  rw [h1]
  have hsum : (∑ t : secantSpace 1 m,
        ∫ a : secantSpace 1 m → Point d × Ω, ‖slotDev h g fh x m a t‖ ^ 2 ∂(slotLaw 1 m W))
      ≤ ((2 : ℝ) * (m : ℝ)) * v := by
    calc (∑ t : secantSpace 1 m,
          ∫ a : secantSpace 1 m → Point d × Ω, ‖slotDev h g fh x m a t‖ ^ 2 ∂(slotLaw 1 m W))
        ≤ ∑ t : secantSpace 1 m, v := Finset.sum_le_sum fun t _ => hZb t
      _ = ((Fintype.card (secantSpace 1 m) : ℕ) : ℝ) * v := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ((2 : ℝ) * (m : ℝ)) * v := by rw [hcard]
  have hfin : ((1 / (m : ℝ)) ^ 2) * (((2 : ℝ) * (m : ℝ)) * v) = 2 * v / (m : ℝ) := by
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    field_simp
  calc ((1 / (m : ℝ)) ^ 2)
        * ∫ a : secantSpace 1 m → Point d × Ω,
          ‖∑ t : secantSpace 1 m, slotDev h g fh x m a t‖ ^ 2 ∂(slotLaw 1 m W)
      ≤ ((1 / (m : ℝ)) ^ 2)
          * ∑ t : secantSpace 1 m,
            ∫ a : secantSpace 1 m → Point d × Ω, ‖slotDev h g fh x m a t‖ ^ 2 ∂(slotLaw 1 m W) :=
          mul_le_mul_of_nonneg_left hS.le (sq_nonneg _)
      _ ≤ ((1 / (m : ℝ)) ^ 2) * (((2 : ℝ) * (m : ℝ)) * v) :=
          mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
      _ = 2 * v / (m : ℝ) := hfin

omit [MeasurableSpace Ω] in
/-- Polyak Łojasiewicz inequality from strong convexity. -/
lemma pl_ineq {f : Point d → ℝ} {μ : ℝ} {xstar x : Point d}
    (hμ : 0 < μ)
    (hsc : ∀ x y, f x + ⟪gradient f x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y) :
    2 * μ * (f x - f xstar) ≤ ‖gradient f x‖ ^ 2 := by
  have h2 : ⟪gradient f x, xstar - x⟫ ≥ -‖gradient f x‖ * ‖xstar - x‖ := by
    have h2a : ⟪gradient f x, x - xstar⟫ ≤ ‖gradient f x‖ * ‖x - xstar‖ := real_inner_le_norm _ _
    have h2b : ⟪gradient f x, xstar - x⟫ + ⟪gradient f x, x - xstar⟫ = 0 := by
      rw [← inner_add_right]
      have h1 : xstar - x + (x - xstar) = 0 := by abel
      rw [h1]
      simp
    have h2c : ‖x - xstar‖ = ‖xstar - x‖ := norm_sub_rev _ _
    rw [h2c] at h2a
    nlinarith
  have hA : f x - f xstar ≤ ‖gradient f x‖ * ‖xstar - x‖ - μ / 2 * ‖xstar - x‖ ^ 2 := by
    have h1 : f x + ⟪gradient f x, xstar - x⟫ + μ / 2 * ‖xstar - x‖ ^ 2 ≤ f xstar := hsc x xstar
    linarith
  have hB1 : 0 < 2 * μ := by positivity
  have hB2 : 2 * μ * (f x - f xstar)
      ≤ 2 * μ * (‖gradient f x‖ * ‖xstar - x‖ - μ / 2 * ‖xstar - x‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hA (le_of_lt hB1)
  have hB3 : 2 * μ * (‖gradient f x‖ * ‖xstar - x‖ - μ / 2 * ‖xstar - x‖ ^ 2)
      = 2 * μ * (‖gradient f x‖ * ‖xstar - x‖) - μ ^ 2 * ‖xstar - x‖ ^ 2 := by ring
  have hC : 2 * μ * (‖gradient f x‖ * ‖xstar - x‖) - μ ^ 2 * ‖xstar - x‖ ^ 2
      ≤ ‖gradient f x‖ ^ 2 := by
    nlinarith [sq_nonneg (μ * ‖xstar - x‖ - ‖gradient f x‖)]
  linarith

/-- One inexact descent step against the smoothed objective: the expected gap contracts by `η μ`
and pays `L η² / 2` times the mean square deviation of the step direction. -/
lemma gap_step {f : Point d → ℝ} {L μ η : ℝ} {xstar x : Point d}
    (hL : 0 < L) (hμ : 0 < μ) (hη0 : 0 ≤ η) (hηL : L * η ≤ 1)
    (hgr : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hsc : ∀ x y, f x + ⟪gradient f x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (hmin : IsMinOn f Set.univ xstar)
    {P : Measure Ω} [IsProbabilityMeasure P] (V : Ω → Point d) (v : ℝ)
    (hV : Integrable V P)
    (hdev : Integrable (fun ω => ‖V ω - gradient f x‖ ^ 2) P)
    (hmean : (∫ ω, V ω ∂P) = gradient f x)
    (hvb : (∫ ω, ‖V ω - gradient f x‖ ^ 2 ∂P) ≤ v)
    (hmeas : AEStronglyMeasurable (fun ω => f (x - η • V ω) - f xstar) P) :
    Integrable (fun ω => f (x - η • V ω) - f xstar) P ∧
      (∫ ω, f (x - η • V ω) - f xstar ∂P)
        ≤ (f x - f xstar) - η * μ * (f x - f xstar) + (L * η ^ 2 / 2) * v := by
  classical
  have hminf : ∀ y, f xstar ≤ f y := fun y => hmin (Set.mem_univ y)
  set g0 : Point d := gradient f x with hg0def
  set xi : Ω → Point d := fun ω => V ω - g0 with hxidef
  have hxie : ∀ ω, V ω = g0 + xi ω := by
    intro ω
    show V ω = g0 + (V ω - g0)
    rw [add_comm, sub_add_cancel]
  have hxii : Integrable xi P := hV.sub (integrable_const g0)
  have hxi0 : (∫ ω, xi ω ∂P) = 0 := by
    show (∫ ω, V ω - g0 ∂P) = 0
    rw [integral_sub hV (integrable_const g0), hmean, hg0def, integral_const, probReal_univ,
      one_smul, sub_self]
  set Lc : Point d →L[ℝ] ℝ := InnerProductSpace.toDual ℝ (Point d) g0 with hLcdef
  have hLc : ∀ y : Point d, Lc y = ⟪g0, y⟫ := fun _ => rfl
  have hlin0 : (∫ ω, ⟪g0, xi ω⟫ ∂P) = 0 := by
    refine (integral_congr_ae (ae_of_all _ fun ω => (hLc (xi ω)).symm)).trans ?_
    rw [Lc.integral_comp_comm hxii, hxi0, map_zero]
  have hlin_int : Integrable (fun ω => (-η + L * η ^ 2) * ⟪g0, xi ω⟫) P := by
    have he : (fun ω => (-η + L * η ^ 2) * ⟪g0, xi ω⟫)
        = fun ω => (-η + L * η ^ 2) • (Lc (xi ω)) := by
      funext ω
      rw [hLc, smul_eq_mul]
    rw [he]
    exact Integrable.smul (-η + L * η ^ 2) (Lc.integrable_comp hxii)
  have hsqu_int : Integrable (fun ω => L * η ^ 2 / 2 * ‖xi ω‖ ^ 2) P :=
    hdev.const_mul (L * η ^ 2 / 2)
  have hsum_int : Integrable (fun ω =>
      (-η + L * η ^ 2) * ⟪g0, xi ω⟫ + L * η ^ 2 / 2 * ‖xi ω‖ ^ 2) P := hlin_int.add hsqu_int
  have hup : ∀ ω, f (x - η • V ω) - f xstar
      ≤ (f x - f xstar - η * ‖g0‖ ^ 2 + L * η ^ 2 / 2 * ‖g0‖ ^ 2)
        + ((-η + L * η ^ 2) * ⟪g0, xi ω⟫ + L * η ^ 2 / 2 * ‖xi ω‖ ^ 2) := by
    intro ω
    have h1 : x - η • V ω = x + (-η) • V ω := by rw [sub_eq_add_neg, ← neg_smul]
    have heq : (x - η • V ω) - x = (-η) • (g0 + xi ω) := by
      rw [h1, add_sub_cancel_left, hxie ω]
    have hp := smooth_upper_bound (f := f) (oracle := gradient f) (L := L) hgr hlip x
      (x - η • V ω)
    rw [← hg0def, heq] at hp
    have h2 : ⟪g0, (-η) • (g0 + xi ω)⟫ = -η * (‖g0‖ ^ 2 + ⟪g0, xi ω⟫) := by
      rw [real_inner_smul_right, inner_add_right, real_inner_self_eq_norm_sq]
    have h3 : L / 2 * ‖(-η) • (g0 + xi ω)‖ ^ 2 = (L * η ^ 2 / 2) * ‖g0 + xi ω‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      ring
    have h4 : ‖g0 + xi ω‖ ^ 2 = ‖g0‖ ^ 2 + 2 * ⟪g0, xi ω⟫ + ‖xi ω‖ ^ 2 := norm_add_sq_real _ _
    rw [h2, h3, h4] at hp
    linarith
  have hG : Integrable (fun ω => (f x - f xstar - η * ‖g0‖ ^ 2 + L * η ^ 2 / 2 * ‖g0‖ ^ 2)
      + ((-η + L * η ^ 2) * ⟪g0, xi ω⟫ + L * η ^ 2 / 2 * ‖xi ω‖ ^ 2)) P :=
    (integrable_const _).add hsum_int
  have hFi : Integrable (fun ω => f (x - η • V ω) - f xstar) P :=
    hG.mono' hmeas (ae_of_all _ fun ω => by
      have h0 : 0 ≤ f (x - η • V ω) - f xstar := sub_nonneg.mpr (hminf _)
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact hup ω)
  have hlinV : (∫ ω, (-η + L * η ^ 2) * ⟪g0, xi ω⟫ ∂P) = 0 := by
    have h4 : (∫ ω, (-η + L * η ^ 2) * ⟪g0, xi ω⟫ ∂P)
        = (-η + L * η ^ 2) * ∫ ω, ⟪g0, xi ω⟫ ∂P := integral_const_mul _ _
    rw [h4, hlin0, mul_zero]
  have hI : (∫ ω, (f x - f xstar - η * ‖g0‖ ^ 2 + L * η ^ 2 / 2 * ‖g0‖ ^ 2)
      + ((-η + L * η ^ 2) * ⟪g0, xi ω⟫ + L * η ^ 2 / 2 * ‖xi ω‖ ^ 2) ∂P)
      = (f x - f xstar) - η * ‖g0‖ ^ 2 + (L * η ^ 2 / 2) * ‖g0‖ ^ 2
        + (L * η ^ 2 / 2) * ∫ ω, ‖xi ω‖ ^ 2 ∂P := by
    rw [integral_add (integrable_const _) hsum_int, integral_add hlin_int hsqu_int, hlinV,
      zero_add, integral_const_mul, integral_const, probReal_univ, one_smul]
  have hmono : (∫ ω, f (x - η • V ω) - f xstar ∂P)
      ≤ ∫ ω, (f x - f xstar - η * ‖g0‖ ^ 2 + L * η ^ 2 / 2 * ‖g0‖ ^ 2)
        + ((-η + L * η ^ 2) * ⟪g0, xi ω⟫ + L * η ^ 2 / 2 * ‖xi ω‖ ^ 2) ∂P :=
    integral_mono hFi hG hup
  rw [hI] at hmono
  have hv0 : (L * η ^ 2 / 2) * ∫ ω, ‖xi ω‖ ^ 2 ∂P ≤ (L * η ^ 2 / 2) * v :=
    mul_le_mul_of_nonneg_left hvb (by positivity)
  have hpl : 2 * μ * (f x - f xstar) ≤ ‖g0‖ ^ 2 := by
    simpa [hg0def] using pl_ineq (f := f) (μ := μ) (xstar := xstar) (x := x) hμ hsc
  have hcoef : η * ‖g0‖ ^ 2 - L * η ^ 2 / 2 * ‖g0‖ ^ 2 ≥ η * μ * (f x - f xstar) := by
    have h11 : 1 - L * η / 2 ≥ 1 / 2 := by nlinarith
    have hc1 : η * (1 - L * η / 2) ≥ η / 2 := by nlinarith
    have hc2 : η * (1 - L * η / 2) * ‖g0‖ ^ 2 ≥ (η / 2) * ‖g0‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hc1 (sq_nonneg _)
    have hc3 : (η / 2) * ‖g0‖ ^ 2 ≥ (η / 2) * (2 * μ * (f x - f xstar)) :=
      mul_le_mul_of_nonneg_left hpl (by linarith : (0 : ℝ) ≤ η / 2)
    have hc4 : (η / 2) * (2 * μ * (f x - f xstar)) = η * μ * (f x - f xstar) := by ring
    have hc5 : η * (1 - L * η / 2) * ‖g0‖ ^ 2
        = η * ‖g0‖ ^ 2 - L * η ^ 2 / 2 * ‖g0‖ ^ 2 := by ring
    linarith
  refine ⟨hFi, ?_⟩
  nlinarith

/-- One mirrored-pair round contracts the expected smoothed gap by `1 − η μ / 2` under strong
growth. -/
lemma ip_one_round {g : Point d → Ω → ℝ} {fh : Point d → ℝ}
    {W : Measure (Point d × Ω)} [IsProbabilityMeasure W]
    {L μ η h ρ : ℝ} {xh x : Point d}
    (hL : 0 < L) (hμ : 0 < μ) (hη0 : 0 ≤ η) (hηL : L * η ≤ 1) (hηr : L * η * ρ ^ 2 ≤ μ / 2)
    (hgr : ∀ x, HasGradientAt fh (gradient fh x) x)
    (hlip : ∀ x y, ‖gradient fh x - gradient fh y‖ ≤ L * ‖x - y‖)
    (hsc : ∀ x y, fh x + ⟪gradient fh x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ fh y)
    (hminh : IsMinOn fh Set.univ xh)
    (hg : Measurable (Function.uncurry g))
    (hint : ∀ x s, Integrable (fun u : Point d × Ω =>
        slotVal h g x s u - halfGrad fh x s) (W))
    (hmean : ∀ x s, (∫ u : Point d × Ω, slotVal h g x s u ∂(W))
        = halfGrad fh x s)
    (hvar2 : ∀ x s, Integrable (fun u : Point d × Ω =>
        ‖slotVal h g x s u - halfGrad fh x s‖ ^ 2) (W))
    (hvar : ∀ s, (∫ u : Point d × Ω, ‖slotVal h g x s u - halfGrad fh x s‖ ^ 2
        ∂(W)) ≤ ρ ^ 2 * (fh x - fh xh)) :
    Integrable (fun ω : secantSpace 1 1 → Point d × Ω =>
        fh (x - η • roundOf h g x 1 ω) - fh xh) (slotLaw 1 1 (W)) ∧
      (∫ ω : secantSpace 1 1 → Point d × Ω,
          fh (x - η • roundOf h g x 1 ω) - fh xh ∂(slotLaw 1 1 (W)))
        ≤ (1 - η * μ / 2) * (fh x - fh xh) := by
  classical
  obtain ⟨hdv, hdb⟩ := roundOf_devAt (m := 1) (g := g) (fh := fh) (h := h) (x := x) (W := W)
    (v := ρ ^ 2 * (fh x - fh xh)) hg hint hmean hvar2 hvar Nat.one_pos
  have hVin : Integrable (fun ω : secantSpace 1 1 → Point d × Ω => roundOf h g x 1 ω)
      (slotLaw 1 1 (W)) := roundOf_integrable (m := 1) hint x
  have hmeanR : (∫ ω : secantSpace 1 1 → Point d × Ω, roundOf h g x 1 ω
      ∂(slotLaw 1 1 (W))) = gradient fh x :=
    roundOf_mean (m := 1) (g := g) (fh := fh) (h := h) hg hint hmean Nat.one_pos x
  have hfh : Measurable fh :=
    (continuous_iff_continuousAt.mpr fun y => (hgr y).continuousAt).measurable
  have hmeas : AEStronglyMeasurable (fun ω : secantSpace 1 1 → Point d × Ω =>
      fh (x - η • roundOf h g x 1 ω) - fh xh) (slotLaw 1 1 (W)) := by
    have h1 : Integrable (fun ω : secantSpace 1 1 → Point d × Ω => η • roundOf h g x 1 ω)
        (slotLaw 1 1 W) := Integrable.smul η hVin
    have h2 : AEStronglyMeasurable (fun ω : secantSpace 1 1 → Point d × Ω =>
        x - η • roundOf h g x 1 ω) (slotLaw 1 1 W) :=
      ((integrable_const x).sub h1).aestronglyMeasurable
    exact (hfh.comp_aemeasurable h2.aemeasurable).aestronglyMeasurable.sub
      aestronglyMeasurable_const
  obtain ⟨hi, hb⟩ := gap_step (f := fh) (L := L) (μ := μ) (η := η) (xstar := xh) (x := x)
    (V := fun ω : secantSpace 1 1 → Point d × Ω => roundOf h g x 1 ω)
    (v := 2 * (ρ ^ 2 * (fh x - fh xh))) hL hμ hη0 hηL hgr hlip hsc hminh hVin hdv hmeanR
    (by simpa using hdb) hmeas
  have h0 : 0 ≤ fh x - fh xh := sub_nonneg.mpr (hminh (Set.mem_univ x))
  have h2 : L * η ^ 2 / 2 * (2 * (ρ ^ 2 * (fh x - fh xh)))
      = η * (L * η * ρ ^ 2) * (fh x - fh xh) := by ring
  have h31 : η * (L * η * ρ ^ 2) ≤ η * (μ / 2) := mul_le_mul_of_nonneg_left hηr hη0
  have h3 : η * (L * η * ρ ^ 2) * (fh x - fh xh) ≤ η * (μ / 2) * (fh x - fh xh) :=
    mul_le_mul_of_nonneg_right h31 h0
  refine ⟨hi, ?_⟩
  have h4 : (1 - η * μ / 2) * (fh x - fh xh)
      = (fh x - fh xh) - η * μ * (fh x - fh xh) + η * (μ / 2) * (fh x - fh xh) := by ring
  rw [h4]
  refine hb.trans ?_
  nlinarith

end OracleTemplate.SecantPolyak.Interpolated

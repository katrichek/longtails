import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic

namespace LongTails.Proofs.ZerothOrderBiasBarrier

open Filter Topology

noncomputable def hinge (s : ℝ) : ℝ := if s ≤ 0 then 0 else s ^ 2 / 2

lemma hinge_zero_of_nonpos {s : ℝ} (hs : s ≤ 0) : hinge s = 0 := by simp [hinge, hs]

lemma hinge_sq_of_pos {s : ℝ} (hs : 0 < s) : hinge s = s ^ 2 / 2 := by
  simp [hinge, not_le.mpr hs]

lemma hinge_sq {s : ℝ} : hinge s = max s 0 ^ 2 / 2 := by
  by_cases hs : s ≤ 0
  · rw [hinge_zero_of_nonpos hs, max_eq_right hs]
    norm_num
  · have hs' : 0 < s := by linarith
    rw [hinge_sq_of_pos hs', max_eq_left (le_of_lt hs')]

lemma hinge_abs_bound {t : ℝ} : |hinge t| ≤ t ^ 2 / 2 := by
  rcases lt_trichotomy t 0 with ht | ht | ht
  · rw [hinge_zero_of_nonpos (le_of_lt ht), abs_zero]
    nlinarith [sq_nonneg t]
  · subst ht
    rw [hinge_zero_of_nonpos (by norm_num : (0 : ℝ) ≤ 0), abs_zero]
    nlinarith
  · rw [hinge_sq_of_pos ht]
    exact abs_le.mpr ⟨by nlinarith [sq_nonneg t], le_refl _⟩

lemma hinge_norm_bound {t : ℝ} : ‖hinge t‖ ≤ ‖(t : ℝ)‖ ^ 2 / 2 := by
  calc ‖hinge t‖ = |hinge t| := Real.norm_eq_abs _
    _ ≤ t ^ 2 / 2 := hinge_abs_bound
    _ = ‖(t : ℝ)‖ ^ 2 / 2 := by rw [Real.norm_eq_abs, sq_abs]

lemma hasDerivAt_hinge_zero : HasDerivAt hinge 0 0 := by
  refine (hasDerivAt_iff_tendsto (f := hinge) (x := 0) (f' := 0)).mpr ?_
  have hsimp : (fun t : ℝ => ‖(t : ℝ) - 0‖⁻¹ * ‖hinge t - hinge 0 - (t - 0) • (0 : ℝ)‖)
      = fun t : ℝ => ‖(t : ℝ)‖⁻¹ * ‖hinge t‖ := by
    funext t
    simp [hinge_zero_of_nonpos (le_refl 0)]
  rw [hsimp]
  refine Metric.tendsto_nhds_nhds.mpr (fun ε hε => ⟨2 * ε, by linarith, fun t ht => ?_⟩)
  have hb : ‖(t : ℝ)‖⁻¹ * ‖hinge t‖ ≤ ‖(t : ℝ)‖⁻¹ * (‖(t : ℝ)‖ ^ 2 / 2) :=
    mul_le_mul_of_nonneg_left hinge_norm_bound (inv_nonneg.mpr (norm_nonneg _))
  have hsum : ‖(t : ℝ)‖⁻¹ * (‖(t : ℝ)‖ ^ 2 / 2) ≤ ‖(t : ℝ)‖ / 2 := by
    by_cases ht0 : (t : ℝ) = 0
    · subst ht0
      norm_num
    · have hpos : 0 < ‖(t : ℝ)‖ := norm_pos_iff.mpr ht0
      have hcan : ‖(t : ℝ)‖⁻¹ * ‖(t : ℝ)‖ ^ 2 = ‖(t : ℝ)‖ := by
        rw [show ‖(t : ℝ)‖ ^ 2 = ‖(t : ℝ)‖ * ‖(t : ℝ)‖ by ring]
        field_simp [hpos.ne']
      rw [show ‖(t : ℝ)‖⁻¹ * (‖(t : ℝ)‖ ^ 2 / 2) = (‖(t : ℝ)‖⁻¹ * ‖(t : ℝ)‖ ^ 2) / 2 by ring, hcan]
  have hlt : ‖(t : ℝ)‖ < 2 * ε := by simpa [Real.dist_eq] using ht
  have hfin : ‖(t : ℝ)‖⁻¹ * ‖hinge t‖ < ε := (hb.trans hsum).trans_lt (by linarith)
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))]
  exact hfin

lemma hasDerivAt_hinge (s : ℝ) : HasDerivAt hinge (max s 0) s := by
  rcases lt_trichotomy s 0 with hs | hs | hs
  · have hU : Set.Iio (0 : ℝ) ∈ 𝓝 s := isOpen_Iio.mem_nhds (by simpa using hs)
    have hEq : hinge =ᶠ[𝓝 s] fun _ : ℝ => (0 : ℝ) := by
      filter_upwards [hU] with t ht
      exact hinge_zero_of_nonpos (le_of_lt (by simpa using ht))
    have h3 : HasDerivAt hinge 0 s := (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq hEq
    rw [max_eq_right (le_of_lt hs)]
    exact h3
  · subst hs
    simpa using hasDerivAt_hinge_zero
  · have hU : Set.Ioi (0 : ℝ) ∈ 𝓝 s := isOpen_Ioi.mem_nhds (by simpa using hs)
    have hEq : hinge =ᶠ[𝓝 s] fun t : ℝ => t ^ 2 / 2 := by
      filter_upwards [hU] with t ht
      exact hinge_sq_of_pos (by simpa using ht)
    have h3 : HasDerivAt hinge (↑2 * s ^ (2 - 1) / 2) s :=
      ((hasDerivAt_pow 2 s).div_const 2).congr_of_eventuallyEq hEq
    rw [show (↑2 * s ^ (2 - 1) / 2 : ℝ) = s by norm_num] at h3
    rw [max_eq_left (le_of_lt hs)]
    exact h3

/-- Extremal derivative profile: flat on `[-h, 0]`, slope `L` on both sides. -/
noncomputable def profile (L ρ h t : ℝ) : ℝ :=
  L * (max (t + ρ) 0 - max (t + h) 0 + max t 0)

/-- The objective whose central difference at the evaluation point has the largest bias. -/
noncomputable def gapFn (L ρ h y : ℝ) : ℝ :=
  L * (hinge (y + ρ) - hinge (y + h) + hinge y)

lemma hasDerivAt_gapFn (L ρ h y : ℝ) : HasDerivAt (gapFn L ρ h) (profile L ρ h y) y := by
  have hinner1 : HasDerivAt (fun t : ℝ => t + ρ) 1 y := (hasDerivAt_id y).add_const ρ
  have hc1 := HasDerivAt.comp y (hasDerivAt_hinge (y + ρ)) hinner1
  rw [mul_one] at hc1
  have hinner2 : HasDerivAt (fun t : ℝ => t + h) 1 y := (hasDerivAt_id y).add_const h
  have hc2 := HasDerivAt.comp y (hasDerivAt_hinge (y + h)) hinner2
  rw [mul_one] at hc2
  have h3 : HasDerivAt (fun t : ℝ => hinge t) (max y 0) y := hasDerivAt_hinge y
  exact ((hc1.sub hc2).add h3).const_mul L

/-- The derivative of the objective is its profile. -/
lemma deriv_gapFn (L ρ h y : ℝ) : deriv (gapFn L ρ h) y = profile L ρ h y :=
  (hasDerivAt_gapFn L ρ h y).deriv

lemma differentiable_gapFn (L ρ h : ℝ) : Differentiable ℝ (gapFn L ρ h) :=
  fun y => (hasDerivAt_gapFn L ρ h y).differentiableAt

lemma profile_zero_of_le {L ρ h t : ℝ} (hh : 0 ≤ h) (hρ : h ≤ ρ) (ht : t ≤ -ρ) :
    profile L ρ h t = 0 := by
  have h1 : max (t + ρ) 0 = 0 := max_eq_right (by linarith)
  have h2 : max (t + h) 0 = 0 := max_eq_right (by linarith)
  have h3 : max t 0 = 0 := max_eq_right (by linarith)
  rw [profile, h1, h2, h3]
  ring

lemma profile_slope_left {L ρ h t : ℝ} (hh : 0 ≤ h) (_hρ : h ≤ ρ) (h1 : -ρ < t) (h2 : t ≤ -h) :
    profile L ρ h t = L * (t + ρ) := by
  have hm1 : max (t + ρ) 0 = t + ρ := max_eq_left (by linarith)
  have hm2 : max (t + h) 0 = 0 := max_eq_right (by linarith)
  have hm3 : max t 0 = 0 := max_eq_right (by linarith)
  rw [profile, hm1, hm2, hm3]
  ring

lemma profile_flat {L ρ h t : ℝ} (_hh : 0 ≤ h) (hρ : h ≤ ρ) (h1 : -h < t) (h2 : t ≤ 0) :
    profile L ρ h t = L * (ρ - h) := by
  have hm1 : max (t + ρ) 0 = t + ρ := max_eq_left (by linarith)
  have hm2 : max (t + h) 0 = t + h := max_eq_left (by linarith)
  have hm3 : max t 0 = 0 := max_eq_right (by linarith)
  rw [profile, hm1, hm2, hm3]
  ring

lemma profile_slope_right {L ρ h t : ℝ} (hh : 0 ≤ h) (hρ : h ≤ ρ) (h1 : 0 < t) :
    profile L ρ h t = L * (ρ - h) + L * t := by
  have hm1 : max (t + ρ) 0 = t + ρ := max_eq_left (by linarith)
  have hm2 : max (t + h) 0 = t + h := max_eq_left (by linarith)
  have hm3 : max t 0 = t := max_eq_left (by linarith)
  rw [profile, hm1, hm2, hm3]
  ring

/-- Which of the four linear pieces the profile follows at a given point. -/
lemma profile_cases {L ρ h : ℝ} (hh : 0 ≤ h) (hρ : h ≤ ρ) (t : ℝ) :
    (t ≤ -ρ ∧ profile L ρ h t = 0) ∨
      (-ρ < t ∧ t ≤ -h ∧ profile L ρ h t = L * (t + ρ)) ∨
      (-h < t ∧ t ≤ 0 ∧ profile L ρ h t = L * (ρ - h)) ∨
      (0 < t ∧ profile L ρ h t = L * (ρ - h) + L * t) := by
  rcases lt_trichotomy t (-ρ) with ht | ht | ht
  · exact Or.inl ⟨le_of_lt ht, profile_zero_of_le hh hρ (le_of_lt ht)⟩
  · subst ht
    exact Or.inl ⟨by linarith, profile_zero_of_le hh hρ (by linarith)⟩
  · rcases lt_trichotomy t (-h) with ht' | ht' | ht'
    · exact Or.inr (Or.inl ⟨ht, le_of_lt ht', profile_slope_left hh hρ ht (le_of_lt ht')⟩)
    · subst ht'
      exact Or.inr (Or.inl ⟨ht, by linarith, profile_slope_left hh hρ ht (by linarith)⟩)
    · rcases lt_trichotomy t 0 with ht'' | ht'' | ht''
      · exact Or.inr (Or.inr (Or.inl ⟨ht', le_of_lt ht'', profile_flat hh hρ ht' (le_of_lt ht'')⟩))
      · subst ht''
        exact Or.inr (Or.inr (Or.inl ⟨ht', by linarith, profile_flat hh hρ ht' (by linarith)⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨ht'', profile_slope_right hh hρ ht''⟩))

/-- The profile is nonnegative. -/
lemma profile_nonneg {L ρ h t : ℝ} (hL : 0 ≤ L) (hh : 0 ≤ h) (hρ : h ≤ ρ) :
    0 ≤ profile L ρ h t := by
  rcases profile_cases hh hρ t with ⟨_, h2⟩ | ⟨_, _, h3⟩ | ⟨_, _, h3⟩ | ⟨_, h2⟩
  · rw [h2]
  · rw [h3]
    nlinarith
  · rw [h3]
    nlinarith
  · rw [h2]
    nlinarith

/-- The profile is monotone, hence the objective is convex. -/
lemma monotone_profile {L ρ h : ℝ} (hL : 0 ≤ L) (hh : 0 ≤ h) (hρ : h ≤ ρ) :
    Monotone (profile L ρ h) := by
  intro u v huv
  rcases profile_cases (L := L) hh hρ u with hu1 | hu2 | hu3 | hu4
  · rcases profile_cases (L := L) hh hρ v with hv1 | hv2 | hv3 | hv4
    · rw [hu1.2, hv1.2]
    · rw [hu1.2, hv2.2.2]
      nlinarith
    · rw [hu1.2, hv3.2.2]
      nlinarith
    · rw [hu1.2, hv4.2]
      nlinarith
  · rcases profile_cases (L := L) hh hρ v with hv1 | hv2 | hv3 | hv4
    · exfalso
      linarith
    · rw [hu2.2.2, hv2.2.2]
      nlinarith
    · rw [hu2.2.2, hv3.2.2]
      nlinarith
    · rw [hu2.2.2, hv4.2]
      nlinarith
  · rcases profile_cases (L := L) hh hρ v with hv1 | hv2 | hv3 | hv4
    · exfalso
      linarith
    · exfalso
      linarith
    · rw [hu3.2.2, hv3.2.2]
    · rw [hu3.2.2, hv4.2]
      nlinarith
  · rcases profile_cases (L := L) hh hρ v with hv1 | hv2 | hv3 | hv4
    · exfalso
      linarith
    · exfalso
      linarith
    · exfalso
      linarith
    · rw [hu4.2, hv4.2]
      nlinarith

/-- The slope of the profile never exceeds `L`. -/
lemma slope_profile {L ρ h : ℝ} (hL : 0 ≤ L) (hh : 0 ≤ h) (hρ : h ≤ ρ) {u v : ℝ} (huv : u ≤ v) :
    profile L ρ h v - profile L ρ h u ≤ L * (v - u) := by
  rcases profile_cases (L := L) hh hρ u with hu1 | hu2 | hu3 | hu4
  · rcases profile_cases (L := L) hh hρ v with hv1 | hv2 | hv3 | hv4
    · rw [hu1.2, hv1.2]
      nlinarith
    · rw [hu1.2, hv2.2.2]
      nlinarith
    · rw [hu1.2, hv3.2.2]
      nlinarith
    · rw [hu1.2, hv4.2]
      nlinarith
  · rcases profile_cases (L := L) hh hρ v with hv1 | hv2 | hv3 | hv4
    · exfalso
      linarith
    · rw [hu2.2.2, hv2.2.2]
      nlinarith
    · rw [hu2.2.2, hv3.2.2]
      nlinarith
    · rw [hu2.2.2, hv4.2]
      nlinarith
  · rcases profile_cases (L := L) hh hρ v with hv1 | hv2 | hv3 | hv4
    · exfalso
      linarith
    · exfalso
      linarith
    · rw [hu3.2.2, hv3.2.2]
      nlinarith
    · rw [hu3.2.2, hv4.2]
      nlinarith
  · rcases profile_cases (L := L) hh hρ v with hv1 | hv2 | hv3 | hv4
    · exfalso
      linarith
    · exfalso
      linarith
    · exfalso
      linarith
    · rw [hu4.2, hv4.2]
      nlinarith

/-- The derivative of the objective is `L`-Lipschitz. -/
lemma gapFn_deriv_lipschitz (L ρ h : ℝ) (hL : 0 ≤ L) (hh : 0 ≤ h) (hρ : h ≤ ρ) :
    ∀ u v, |deriv (gapFn L ρ h) u - deriv (gapFn L ρ h) v| ≤ L * |u - v| := by
  intro u v
  rw [deriv_gapFn, deriv_gapFn, abs_le]
  rcases le_total u v with huv | huv
  · rw [abs_of_nonpos (by linarith : u - v ≤ 0)]
    refine ⟨by nlinarith [slope_profile hL hh hρ huv, monotone_profile hL hh hρ huv],
      by nlinarith [slope_profile hL hh hρ huv, monotone_profile hL hh hρ huv]⟩
  · rw [abs_of_nonneg (by linarith : 0 ≤ u - v)]
    refine ⟨by nlinarith [slope_profile hL hh hρ huv, monotone_profile hL hh hρ huv],
      by nlinarith [slope_profile hL hh hρ huv, monotone_profile hL hh hρ huv]⟩

/-- The objective is convex. -/
lemma gapFn_convex (L ρ h : ℝ) (hL : 0 ≤ L) (hh : 0 ≤ h) (hρ : h ≤ ρ) :
    ConvexOn ℝ Set.univ (gapFn L ρ h) := by
  have hmono : Monotone (deriv (gapFn L ρ h)) := fun a b hab => by
    rw [deriv_gapFn, deriv_gapFn]
    exact monotone_profile hL hh hρ hab
  exact hmono.convexOn_univ_of_deriv (differentiable_gapFn L ρ h)

/-- The objective is nondecreasing, so the left end of the flat region is a minimizer. -/
lemma gapFn_min (L ρ h : ℝ) (hL : 0 ≤ L) (hh : 0 ≤ h) (hρ : h ≤ ρ) :
    IsMinOn (gapFn L ρ h) Set.univ (-ρ) := by
  intro y _
  have hmono : MonotoneOn (gapFn L ρ h) (Set.Ici (-ρ)) :=
    monotoneOn_of_deriv_nonneg (convex_Ici (-ρ))
      (differentiable_gapFn L ρ h).continuous.continuousOn
      (differentiable_gapFn L ρ h).differentiableOn fun z _ => by
        rw [deriv_gapFn]
        exact profile_nonneg hL hh hρ
  rcases le_total y (-ρ) with hy | hy
  · have h1 : gapFn L ρ h y = gapFn L ρ h (-ρ) := by
      have e1 : hinge (y + ρ) = 0 := hinge_zero_of_nonpos (by linarith)
      have e2 : hinge (y + h) = 0 := hinge_zero_of_nonpos (by linarith)
      have e3 : hinge y = 0 := hinge_zero_of_nonpos (by linarith)
      have e4 : hinge (-ρ + ρ) = 0 := by simpa using hinge_zero_of_nonpos (le_refl 0)
      have e5 : hinge (-ρ + h) = 0 := hinge_zero_of_nonpos (by linarith)
      have e6 : hinge (-ρ) = 0 := hinge_zero_of_nonpos (by linarith)
      simp only [gapFn, e1, e2, e3, e4, e5, e6]
    exact h1.symm.le
  · exact hmono (Set.mem_Ici.mpr (le_refl (-ρ))) (Set.mem_Ici.mpr hy) hy

/-- Central difference of the objective equals the derivative plus `L h / 4`. -/
lemma barrier_bias (L ρ h : ℝ) (hL : 0 < L) (hh : 0 < h) (hρ : h ≤ ρ) :
    (gapFn L ρ h h - gapFn L ρ h (-h)) / (2 * h) - deriv (gapFn L ρ h) 0 = L * h / 4 := by
  have m1 : max (h + ρ) 0 = h + ρ := max_eq_left (by linarith)
  have m2 : max (h + h) 0 = h + h := max_eq_left (by linarith)
  have m3 : max h 0 = h := max_eq_left (by linarith)
  have m4 : max (-h + ρ) 0 = -h + ρ := max_eq_left (by linarith)
  have m5 : max (-h + h) 0 = 0 := max_eq_right (by linarith)
  have m6 : max (-h) 0 = 0 := max_eq_right (by linarith)
  have he1 : hinge (h + ρ) = (h + ρ) ^ 2 / 2 := by rw [hinge_sq, m1]
  have he2 : hinge (h + h) = (h + h) ^ 2 / 2 := by rw [hinge_sq, m2]
  have he3 : hinge h = h ^ 2 / 2 := by rw [hinge_sq, m3]
  have he4 : hinge (-h + ρ) = (-h + ρ) ^ 2 / 2 := by rw [hinge_sq, m4]
  have he5 : hinge (-h + h) = 0 := by rw [hinge_sq, m5]; norm_num
  have he6 : hinge (-h) = 0 := by rw [hinge_sq, m6]; norm_num
  have hd : deriv (gapFn L ρ h) 0 = L * (ρ - h) := by
    rw [deriv_gapFn, profile]
    have n1 : max (0 + ρ) 0 = 0 + ρ := max_eq_left (by linarith)
    have n2 : max (0 + h) 0 = 0 + h := max_eq_left (by linarith)
    have n3 : max (0 : ℝ) 0 = 0 := max_eq_right (le_refl 0)
    rw [n1, n2, n3]
    ring
  rw [hd]
  simp only [gapFn, he1, he2, he3, he4, he5, he6]
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have hh' : h ≠ 0 := ne_of_gt hh
  field_simp [h2, hh']
  ring

/-- Machine-checked barrier: for every bandwidth `h` there is a convex `L`-smooth objective with a
minimizer at distance `ρ` whose central-difference estimator has bias `L h / 4`, pointing away from
that minimizer. -/
theorem exists_central_difference_bias (L ρ h : ℝ) (hL : 0 < L) (hh : 0 < h) (hρ : h ≤ ρ) :
    ∃ (f : ℝ → ℝ) (x xstar : ℝ),
      ConvexOn ℝ Set.univ f ∧
        (∀ u v, |deriv f u - deriv f v| ≤ L * |u - v|) ∧
        IsMinOn f Set.univ xstar ∧
        x - xstar = ρ ∧
        (f (x + h) - f (x - h)) / (2 * h) - deriv f x = L * h / 4 ∧
        ((f (x + h) - f (x - h)) / (2 * h) - deriv f x) * (x - xstar) > 0 := by
  refine ⟨gapFn L ρ h, 0, -ρ,
    gapFn_convex L ρ h (le_of_lt hL) (le_of_lt hh) hρ,
    gapFn_deriv_lipschitz L ρ h (le_of_lt hL) (le_of_lt hh) hρ,
    gapFn_min L ρ h (le_of_lt hL) (le_of_lt hh) hρ, ?_, ?_, ?_⟩
  · ring
  · simpa using (barrier_bias L ρ h hL hh hρ)
  · have hb2 : (gapFn L ρ h (0 + h) - gapFn L ρ h (0 - h)) / (2 * h)
      - deriv (gapFn L ρ h) 0 = L * h / 4 := by simpa using barrier_bias L ρ h hL hh hρ
    rw [hb2]
    have h1 : (0 : ℝ) - -ρ = ρ := by ring
    rw [h1]
    have hpos : 0 < ρ := by linarith
    have h2 : 0 < L * h / 4 := by positivity
    nlinarith


lemma deriv_gapFn_zero (L ρ h : ℝ) (hh : 0 ≤ h) (hρ : h ≤ ρ) :
    deriv (gapFn L ρ h) 0 = L * (ρ - h) := by
  rw [deriv_gapFn, profile]
  have n1 : max (0 + ρ) 0 = 0 + ρ := max_eq_left (by linarith)
  have n2 : max (0 + h) 0 = 0 + h := max_eq_left (by linarith)
  have n3 : max (0 : ℝ) 0 = 0 := max_eq_right (le_refl 0)
  rw [n1, n2, n3]
  ring

/-- Fourth-order accurate central difference of the same objective keeps a bias of `5 L h / 24`. -/
lemma barrier_bias4 (L ρ h : ℝ) (hL : 0 < L) (hh : 0 < h) (hρ : 2 * h ≤ ρ) :
    (8 * (gapFn L ρ h h - gapFn L ρ h (-h)) - (gapFn L ρ h (2 * h) - gapFn L ρ h (-2 * h))) /
        (12 * h) - deriv (gapFn L ρ h) 0 = 5 * L * h / 24 := by
  have k1 : max (h + ρ) 0 = h + ρ := max_eq_left (by linarith)
  have k2 : max (h + h) 0 = h + h := max_eq_left (by linarith)
  have k3 : max h 0 = h := max_eq_left (by linarith)
  have k4 : max (-h + ρ) 0 = -h + ρ := max_eq_left (by linarith)
  have k5 : max (-h + h) 0 = 0 := max_eq_right (by linarith)
  have k6 : max (-h) 0 = 0 := max_eq_right (by linarith)
  have k7 : max (2 * h + ρ) 0 = 2 * h + ρ := max_eq_left (by linarith)
  have k8 : max (2 * h + h) 0 = 2 * h + h := max_eq_left (by linarith)
  have k9 : max (2 * h) 0 = 2 * h := max_eq_left (by linarith)
  have k10 : max (-2 * h + ρ) 0 = -2 * h + ρ := max_eq_left (by linarith)
  have k11 : max (-2 * h + h) 0 = 0 := max_eq_right (by linarith)
  have k12 : max (-2 * h) 0 = 0 := max_eq_right (by linarith)
  have he1 : hinge (h + ρ) = (h + ρ) ^ 2 / 2 := by rw [hinge_sq, k1]
  have he2 : hinge (h + h) = (h + h) ^ 2 / 2 := by rw [hinge_sq, k2]
  have he3 : hinge h = h ^ 2 / 2 := by rw [hinge_sq, k3]
  have he4 : hinge (-h + ρ) = (-h + ρ) ^ 2 / 2 := by rw [hinge_sq, k4]
  have he5 : hinge (-h + h) = 0 := by rw [hinge_sq, k5]; norm_num
  have he6 : hinge (-h) = 0 := by rw [hinge_sq, k6]; norm_num
  have he7 : hinge (2 * h + ρ) = (2 * h + ρ) ^ 2 / 2 := by rw [hinge_sq, k7]
  have he8 : hinge (2 * h + h) = (2 * h + h) ^ 2 / 2 := by rw [hinge_sq, k8]
  have he9 : hinge (2 * h) = (2 * h) ^ 2 / 2 := by rw [hinge_sq, k9]
  have he10 : hinge (-2 * h + ρ) = (-2 * h + ρ) ^ 2 / 2 := by rw [hinge_sq, k10]
  have he11 : hinge (-2 * h + h) = 0 := by rw [hinge_sq, k11]; norm_num
  have he12 : hinge (-2 * h) = 0 := by rw [hinge_sq, k12]; norm_num
  rw [deriv_gapFn_zero L ρ h (le_of_lt hh) (by linarith)]
  simp only [gapFn, he1, he2, he3, he4, he5, he6, he7, he8, he9, he10, he11, he12]
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have h12 : (12 : ℝ) ≠ 0 := by norm_num
  have hh' : h ≠ 0 := ne_of_gt hh
  field_simp [h2, h12, hh']
  ring

/-- Machine-checked barrier for the fourth-order stencil: even the classical `O(h⁴)`-accurate
gradient approximation has bias `5 L h / 24` away from the minimizer on a convex `L`-smooth
objective. -/
theorem exists_four_point_difference_bias (L h : ℝ) (hL : 0 < L) (hh : 0 < h) :
    ∃ (f : ℝ → ℝ) (x xstar : ℝ),
      ConvexOn ℝ Set.univ f ∧
        (∀ u v, |deriv f u - deriv f v| ≤ L * |u - v|) ∧
        IsMinOn f Set.univ xstar ∧
        x - xstar = 2 * h ∧
        (8 * (f (x + h) - f (x - h)) - (f (x + 2 * h) - f (x - 2 * h))) / (12 * h)
            - deriv f x = 5 * L * h / 24 ∧
        ((8 * (f (x + h) - f (x - h)) - (f (x + 2 * h) - f (x - 2 * h))) / (12 * h)
            - deriv f x) * (x - xstar) > 0 := by
  have hle : h ≤ 2 * h := by linarith
  refine ⟨gapFn L (2 * h) h, 0, -(2 * h),
    gapFn_convex L (2 * h) h (le_of_lt hL) (le_of_lt hh) hle,
    gapFn_deriv_lipschitz L (2 * h) h (le_of_lt hL) (le_of_lt hh) hle,
    gapFn_min L (2 * h) h (le_of_lt hL) (le_of_lt hh) hle, ?_, ?_, ?_⟩
  · ring
  · simpa using barrier_bias4 L (2 * h) h hL hh (by linarith)
  · have hb : (8 * (gapFn L (2 * h) h (0 + h) - gapFn L (2 * h) h (0 - h)) -
        (gapFn L (2 * h) h (0 + 2 * h) - gapFn L (2 * h) h (0 - 2 * h))) / (12 * h)
      - deriv (gapFn L (2 * h) h) 0 = 5 * L * h / 24 := by
      simpa using barrier_bias4 L (2 * h) h hL hh (by linarith)
    rw [hb]
    have h1 : (0 : ℝ) - -(2 * h) = 2 * h := by ring
    rw [h1]
    have h2 : 0 < 2 * h := by linarith
    have h3 : 0 < 5 * L * h / 24 := by positivity
    nlinarith

end LongTails.Proofs.ZerothOrderBiasBarrier

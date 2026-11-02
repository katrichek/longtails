import Mathlib.Analysis.Convex.Slope
import Mathlib.Tactic

open Set

namespace OracleTemplate.LineSearch

lemma monotoneOn_Ici_of_isMinOn {f : ℝ → ℝ} (hconv : ConvexOn ℝ univ f) {xstar : ℝ}
    (hmin : IsMinOn f univ xstar) : MonotoneOn f (Ici xstar) := by
  intro x hx y hy hxy
  have hx' : xstar ≤ x := hx
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · exact le_rfl
  rcases lt_or_eq_of_le hx' with hxlt | rfl
  · have h1 : 0 < x - xstar := by linarith
    have h2 : 0 < y - x := by linarith
    have hs := hconv.slope_mono_adjacent (mem_univ xstar) (mem_univ y) hxlt hlt
    rw [div_le_div_iff₀ h1 h2] at hs
    have hnonneg : 0 ≤ (f x - f xstar) * (y - x) :=
      mul_nonneg (sub_nonneg.mpr (hmin (mem_univ x))) h2.le
    nlinarith [hs, hnonneg, h1, h2]
  · exact hmin (mem_univ y)

lemma antitoneOn_Iic_of_isMinOn {f : ℝ → ℝ} (hconv : ConvexOn ℝ univ f) {xstar : ℝ}
    (hmin : IsMinOn f univ xstar) : AntitoneOn f (Iic xstar) := by
  intro x hx y hy hxy
  have hy' : y ≤ xstar := hy
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · exact le_rfl
  rcases eq_or_lt_of_le hy' with rfl | hylt
  · exact hmin (mem_univ x)
  · have h1 : 0 < y - x := by linarith
    have h2 : 0 < xstar - y := by linarith
    have hs := hconv.slope_mono_adjacent (mem_univ x) (mem_univ xstar) hlt hylt
    rw [div_le_div_iff₀ h1 h2] at hs
    have hnonpos : (f xstar - f y) * (y - x) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hmin (mem_univ y))) h1.le
    nlinarith [hs, hnonpos, h1, h2]

lemma dichotomy_of_ternary_layout {f : ℝ → ℝ} (hconv : ConvexOn ℝ univ f) {xstar lo a b hi : ℝ}
    (hmin : IsMinOn f univ xstar) (hab : a < b)
    (h1 : a - lo = b - a) (h2 : hi - b = b - a) (hx : xstar ∈ Icc lo hi) :
    xstar ∈ Icc a b ∨ min (f a) (f b) - f xstar ≤ |f b - f a| := by
  by_cases hmem : xstar ∈ Icc a b
  · exact Or.inl hmem
  · right
    have hlt : xstar < a ∨ b < xstar := by
      by_contra hcon
      push Not at hcon
      exact hmem ⟨hcon.1, hcon.2⟩
    rcases hlt with hxa | hbx
    · have hxb : xstar < b := lt_trans hxa hab
      have h1' : 0 < a - xstar := by linarith
      have h2' : 0 < b - a := by linarith
      have hs := hconv.slope_mono_adjacent (mem_univ xstar) (mem_univ b) hxa hab
      rw [div_le_div_iff₀ h1' h2'] at hs
      have hmono := monotoneOn_Ici_of_isMinOn hconv hmin (mem_Ici.mpr (by linarith))
        (mem_Ici.mpr (by linarith)) hab.le
      have hfac : a - xstar ≤ b - a := by linarith [hx.1, h1]
      rw [min_eq_left hmono, abs_of_nonneg (sub_nonneg.mpr hmono)]
      nlinarith [hs, hmono, hfac, h2']
    · have h1' : 0 < b - a := by linarith
      have h2' : 0 < xstar - b := by linarith
      have hs := hconv.slope_mono_adjacent (mem_univ a) (mem_univ xstar) hab hbx
      rw [div_le_div_iff₀ h1' h2'] at hs
      have hanti := antitoneOn_Iic_of_isMinOn hconv hmin (mem_Iic.mpr (by linarith))
        (mem_Iic.mpr (by linarith)) hab.le
      have hfac : xstar - b ≤ b - a := by linarith [hx.2, h2]
      rw [min_eq_right hanti, abs_of_nonpos (sub_nonpos.mpr hanti)]
      nlinarith [hs, hanti, hfac, h1']

end OracleTemplate.LineSearch

import LongTails.Proofs.LineSearchDichotomy
import Mathlib.Analysis.Convex.Function

open Set

namespace OracleTemplate.LineSearch

variable {f : ℝ → ℝ}

noncomputable def ptLeft (l h : ℝ) : ℝ := l + (h - l) / 3

noncomputable def ptRight (l h : ℝ) : ℝ := l + 2 * (h - l) / 3

noncomputable def stepInterval (l h : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  if v.1 > v.2 then (ptLeft l h, h) else (l, ptRight l h)

lemma ptLeft_sub (l h : ℝ) : ptLeft l h - l = (h - l) / 3 := by
  unfold ptLeft; ring

lemma ptRight_sub_left (l h : ℝ) : ptRight l h - ptLeft l h = (h - l) / 3 := by
  unfold ptRight ptLeft; ring

lemma sub_ptRight (l h : ℝ) : h - ptRight l h = (h - l) / 3 := by
  unfold ptRight; ring

lemma ptLeft_lt_ptRight {l h : ℝ} (hlh : l < h) : ptLeft l h < ptRight l h := by
  rw [← sub_pos, ptRight_sub_left]; linarith

lemma le_ptLeft {l h : ℝ} (hlh : l ≤ h) : l ≤ ptLeft l h := by
  rw [← sub_nonneg, ptLeft_sub]; linarith

lemma ptRight_le {l h : ℝ} (hlh : l ≤ h) : ptRight l h ≤ h := by
  rw [← sub_nonneg, sub_ptRight]; linarith

lemma stepInterval_subset {l h : ℝ} (hlh : l ≤ h) (v : ℝ × ℝ) :
    l ≤ (stepInterval l h v).1 ∧ (stepInterval l h v).2 ≤ h := by
  unfold stepInterval
  by_cases hv : v.1 > v.2
  · rw [ite_eq_left hv]; exact ⟨le_ptLeft hlh, le_rfl⟩
  · rw [ite_eq_right hv]; exact ⟨le_rfl, ptRight_le hlh⟩

lemma stepInterval_len {l h : ℝ} (v : ℝ × ℝ) :
    (stepInterval l h v).2 - (stepInterval l h v).1 = 2 * (h - l) / 3 := by
  unfold stepInterval
  by_cases hv : v.1 > v.2
  · rw [ite_eq_left hv]; unfold ptLeft; ring
  · rw [ite_eq_right hv]; unfold ptRight; ring

lemma stepInterval_nonempty {l h : ℝ} (hlh : l ≤ h) (v : ℝ × ℝ) :
    (stepInterval l h v).1 ≤ (stepInterval l h v).2 := by
  unfold stepInterval
  by_cases hv : v.1 > v.2
  · rw [ite_eq_left hv]
    unfold ptLeft
    nlinarith
  · rw [ite_eq_right hv]
    unfold ptRight
    nlinarith

lemma stepInterval_contains {l h : ℝ} {x : ℝ} (hx : x ∈ Icc l h)
    (hmid : x ∈ Icc (ptLeft l h) (ptRight l h)) (v : ℝ × ℝ) :
    x ∈ Icc (stepInterval l h v).1 (stepInterval l h v).2 := by
  have hlh : l ≤ h := le_trans hx.1 hx.2
  unfold stepInterval
  by_cases hv : v.1 > v.2
  · rw [ite_eq_left hv]
    exact ⟨hmid.1, le_trans hmid.2 (ptRight_le hlh)⟩
  · rw [ite_eq_right hv]
    exact ⟨le_trans (le_ptLeft hlh) hmid.1, hmid.2⟩

lemma gap_le_of_not_mem_middle {xstar l h : ℝ} (hconv : ConvexOn ℝ univ f)
    (hmin : IsMinOn f univ xstar) (hlh : l < h) (hx : xstar ∈ Icc l h)
    (hnot : xstar ∉ Icc (ptLeft l h) (ptRight l h)) :
    f (ptLeft l h) - f xstar ≤ 2 * |f (ptRight l h) - f (ptLeft l h)| ∧
      f (ptRight l h) - f xstar ≤ 2 * |f (ptRight l h) - f (ptLeft l h)| := by
  have hab : ptLeft l h < ptRight l h := ptLeft_lt_ptRight hlh
  have h1 : ptLeft l h - l = ptRight l h - ptLeft l h := by
    rw [ptLeft_sub, ptRight_sub_left]
  have h2 : h - ptRight l h = ptRight l h - ptLeft l h := by
    rw [sub_ptRight, ptRight_sub_left]
  have hdich := dichotomy_of_ternary_layout hconv hmin hab h1 h2 hx
  have hmem : xstar ∉ Icc (ptLeft l h) (ptRight l h) := hnot
  have hbound : min (f (ptLeft l h)) (f (ptRight l h)) - f xstar
      ≤ |f (ptRight l h) - f (ptLeft l h)| := by
    rcases hdich with h | h
    · exact absurd h hmem
    · exact h
  have hminle : f xstar ≤ f (ptLeft l h) := hmin (mem_univ _)
  have hminle' : f xstar ≤ f (ptRight l h) := hmin (mem_univ _)
  rcases le_total (f (ptLeft l h)) (f (ptRight l h)) with hle | hle
  · rw [min_eq_left hle] at hbound
    have habs : |f (ptRight l h) - f (ptLeft l h)| = f (ptRight l h) - f (ptLeft l h) :=
      abs_of_nonneg (by linarith)
    exact ⟨by linarith [hbound], by linarith [hbound, habs]⟩
  · rw [min_eq_right hle] at hbound
    have habs : |f (ptRight l h) - f (ptLeft l h)| = f (ptLeft l h) - f (ptRight l h) := by
      rw [abs_of_nonpos (by linarith)]; ring
    exact ⟨by linarith [hbound, habs], by linarith [hbound]⟩

end OracleTemplate.LineSearch

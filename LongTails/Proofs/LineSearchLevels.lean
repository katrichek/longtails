import LongTails.Proofs.LineSearchChampion
import LongTails.Proofs.LineSearchDichotomy

open Set

namespace OracleTemplate.LineSearch

variable (R x0 : ℝ)

lemma step_level (s : State) (v : ℝ × ℝ) : (step s v).level = s.level + 1 := by
  rw [step]
  by_cases h0 : s.level = 0
  · rw [if_pos h0, h0]
  · rw [if_neg h0]
    by_cases hc : min v.1 v.2 < s.champVal
    · rw [if_pos hc]
    · rw [if_neg hc]

lemma step_bounds {s : State} (hs : s.lo ≤ s.hi) (v : ℝ × ℝ) :
    (step s v).lo ≤ (step s v).hi := by
  rw [step]
  by_cases h0 : s.level = 0
  · rw [if_pos h0]
    by_cases hv : v.1 > v.2
    · rw [if_pos hv, if_pos hv]; unfold leftPoint; nlinarith
    · rw [if_neg hv, if_neg hv]; unfold rightPoint; nlinarith
  · rw [if_neg h0]
    by_cases hc : min v.1 v.2 < s.champVal
    · rw [if_pos hc]
      by_cases hv : v.1 > v.2
      · rw [if_pos hv, if_pos hv]; unfold leftPoint; nlinarith
      · rw [if_neg hv, if_neg hv]; unfold rightPoint; nlinarith
    · rw [if_neg hc]
      by_cases hv : v.1 > v.2
      · rw [if_pos hv, if_pos hv]; unfold leftPoint; nlinarith
      · rw [if_neg hv, if_neg hv]; unfold rightPoint; nlinarith

noncomputable def runState (v : ℕ → ℝ × ℝ) : ℕ → State :=
  fun j => Nat.rec (motive := fun _ => State)
    { level := 0, lo := x0 - R, hi := x0 + R, champ := x0, champVal := 0 }
    (fun i s => step s (v i)) j

lemma runState_zero_lo (v : ℕ → ℝ × ℝ) : (runState R x0 v 0).lo = x0 - R := rfl

lemma runState_zero_hi (v : ℕ → ℝ × ℝ) : (runState R x0 v 0).hi = x0 + R := rfl

lemma runState_succ (v : ℕ → ℝ × ℝ) (j : ℕ) :
    runState R x0 v (j + 1) = step (runState R x0 v j) (v j) := rfl

lemma runState_level (v : ℕ → ℝ × ℝ) (j : ℕ) : (runState R x0 v j).level = j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [runState_succ, step_level, ih]

lemma runState_interval_le (v : ℕ → ℝ × ℝ) (hs : x0 - R ≤ x0 + R) (j : ℕ) :
    (runState R x0 v j).lo ≤ (runState R x0 v j).hi := by
  induction j with
  | zero => rw [runState_zero_lo, runState_zero_hi]; exact hs
  | succ j ih => rw [runState_succ]; exact step_bounds ih (v j)

lemma good_step_or_harm {v : ℕ → ℝ × ℝ} {f : ℝ → ℝ} {xstar : ℝ} (hconv : ConvexOn ℝ univ f)
    (hmin : IsMinOn f univ xstar) {j : ℕ}
    (hgood : xstar ∈ Icc (runState R x0 v j).lo (runState R x0 v j).hi) :
    xstar ∈ Icc (runState R x0 v (j + 1)).lo (runState R x0 v (j + 1)).hi ∨
      min (f (leftPoint (runState R x0 v j))) (f (rightPoint (runState R x0 v j))) - f xstar ≤
        |f (rightPoint (runState R x0 v j)) - f (leftPoint (runState R x0 v j))| := by
  rw [runState_succ R x0 v j]
  by_cases hmid : xstar ∈ Icc (leftPoint (runState R x0 v j)) (rightPoint (runState R x0 v j))
  · refine Or.inl ?_
    have h := interval_inner_update_contains R x0 (runState R x0 v j) hgood hmid (v j)
    rw [inner_update_eq_step] at h
    exact h
  · have hlh : (runState R x0 v j).lo < (runState R x0 v j).hi := by
      rcases lt_or_ge (runState R x0 v j).lo (runState R x0 v j).hi with h | h
      · exact h
      · exfalso
        have heq : (runState R x0 v j).lo = (runState R x0 v j).hi :=
          le_antisymm (hgood.1.trans hgood.2) h
        have hself : xstar = (runState R x0 v j).lo :=
          le_antisymm (hgood.2.trans heq.ge) hgood.1
        have hl : leftPoint (runState R x0 v j) = xstar := by
          rw [hself]; unfold leftPoint; rw [heq]; ring
        have hr : rightPoint (runState R x0 v j) = xstar := by
          rw [hself]; unfold rightPoint; rw [heq]; ring
        exact hmid ⟨hl.le, hr.ge⟩
    have hdich := dichotomy_of_ternary_layout hconv hmin (ptLeft_lt_ptRight hlh)
      (by rw [ptLeft_sub, ptRight_sub_left]) (by rw [sub_ptRight, ptRight_sub_left]) hgood
    simp only [leftPoint_eq_ptLeft, rightPoint_eq_ptRight] at hmid
    rcases hdich with hc | hc
    · exact absurd hc hmid
    · exact Or.inr (by simpa only [leftPoint_eq_ptLeft, rightPoint_eq_ptRight] using hc)

lemma champVal_step_le (s : State) (v : ℝ × ℝ) :
    (step s v).champVal ≤ min v.1 v.2 := by
  rw [step]
  by_cases h0 : s.level = 0
  · rw [if_pos h0]
  · rw [if_neg h0]
    by_cases hc : min v.1 v.2 < s.champVal
    · rw [if_pos hc]
    · rw [if_neg hc]
      exact le_of_not_gt hc

lemma champVal_step_le_champ (s : State) (v : ℝ × ℝ) (h0 : ¬ s.level = 0) :
    (step s v).champVal ≤ s.champVal := by
  rw [step, if_neg h0]
  by_cases hc : min v.1 v.2 < s.champVal
  · rw [if_pos hc]
    exact le_of_lt hc
  · rw [if_neg hc]

lemma champVal_runState_mono (v : ℕ → ℝ × ℝ) {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) :
    (runState R x0 v j).champVal ≤ (runState R x0 v i).champVal := by
  induction j with
  | zero => omega
  | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with hlt | hge
      · have hle : i ≤ j := Nat.lt_succ_iff.mp hlt
        have hprev := ih hle
        have hstep := champVal_step_le_champ (runState R x0 v j) (v j)
          (by rw [runState_level]; omega)
        rw [runState_succ R x0 v j]
        exact le_trans hstep hprev
      · have hz : i = j + 1 := le_antisymm hij hge
        subst hz
        exact le_rfl

lemma champVal_runState_le_min (v : ℕ → ℝ × ℝ) {j J : ℕ} (hj : j < J) :
    (runState R x0 v J).champVal ≤ min (v j).1 (v j).2 := by
  have h1 := champVal_runState_mono R x0 v (i := j + 1) (j := J) (by omega) (by omega)
  have h2 : (runState R x0 v (j + 1)).champVal ≤ min (v j).1 (v j).2 := by
    rw [runState_succ]
    exact champVal_step_le (runState R x0 v j) (v j)
  exact le_trans h1 h2

end OracleTemplate.LineSearch

namespace OracleTemplate.LineSearch

variable (R x0 : ℝ)

lemma lo_step (s : State) (v : ℝ × ℝ) :
    (step s v).lo = (if v.1 > v.2 then leftPoint s else s.lo) := by
  rw [step]
  by_cases h0 : s.level = 0
  · rw [if_pos h0]
  · rw [if_neg h0]
    by_cases hc : min v.1 v.2 < s.champVal
    · rw [if_pos hc]
    · rw [if_neg hc]

lemma hi_step (s : State) (v : ℝ × ℝ) :
    (step s v).hi = (if v.1 > v.2 then s.hi else rightPoint s) := by
  rw [step]
  by_cases h0 : s.level = 0
  · rw [if_pos h0]
  · rw [if_neg h0]
    by_cases hc : min v.1 v.2 < s.champVal
    · rw [if_pos hc]
    · rw [if_neg hc]

lemma leftPoint_lt_rightPoint {s : State} (hlh : s.lo < s.hi) :
    leftPoint s < rightPoint s := by
  have := ptLeft_lt_ptRight hlh
  simpa only [leftPoint_eq_ptLeft, rightPoint_eq_ptRight] using this

lemma harm_le_errors_of_fail {v : ℕ → ℝ × ℝ} {f : ℝ → ℝ} {xstar : ℝ}
    (hconv : ConvexOn ℝ univ f) (hmin : IsMinOn f univ xstar) {j : ℕ}
    (hgood : xstar ∈ Icc (runState R x0 v j).lo (runState R x0 v j).hi)
    (hfail : xstar ∉ Icc (step (runState R x0 v j) (v j)).lo
      (step (runState R x0 v j) (v j)).hi) :
    min (f (leftPoint (runState R x0 v j))) (f (rightPoint (runState R x0 v j))) - f xstar ≤
      |(v j).1 - f (leftPoint (runState R x0 v j))| +
        |(v j).2 - f (rightPoint (runState R x0 v j))| := by
  have hnotmid : xstar ∉ Icc (leftPoint (runState R x0 v j))
      (rightPoint (runState R x0 v j)) := by
    intro hmid
    have hcont := interval_inner_update_contains R x0 (runState R x0 v j) hgood hmid (v j)
    rw [inner_update_eq_step] at hcont
    exact hfail hcont
  have hlh : (runState R x0 v j).lo < (runState R x0 v j).hi := by
    rcases lt_or_ge (runState R x0 v j).lo (runState R x0 v j).hi with h | h
    · exact h
    · exfalso
      have heq : (runState R x0 v j).lo = (runState R x0 v j).hi :=
        le_antisymm (hgood.1.trans hgood.2) h
      have hself : xstar = (runState R x0 v j).lo :=
        le_antisymm (hgood.2.trans heq.ge) hgood.1
      have hl : leftPoint (runState R x0 v j) = xstar := by
        rw [hself]; unfold leftPoint; rw [heq]; ring
      have hr : rightPoint (runState R x0 v j) = xstar := by
        rw [hself]; unfold rightPoint; rw [heq]; ring
      exact hnotmid ⟨hl.le, hr.ge⟩
  have hgap : min (f (leftPoint (runState R x0 v j))) (f (rightPoint (runState R x0 v j))) - f xstar
      ≤ |f (rightPoint (runState R x0 v j)) - f (leftPoint (runState R x0 v j))| := by
    have hdich := dichotomy_of_ternary_layout hconv hmin (ptLeft_lt_ptRight hlh)
      (by rw [ptLeft_sub, ptRight_sub_left]) (by rw [sub_ptRight, ptRight_sub_left]) hgood
    simp only [leftPoint_eq_ptLeft, rightPoint_eq_ptRight] at hnotmid
    rcases hdich with hc | hc
    · exact absurd hc hnotmid
    · simpa only [leftPoint_eq_ptLeft, rightPoint_eq_ptRight] using hc
  have hlt := leftPoint_lt_rightPoint hlh
  have hlt' : xstar < leftPoint (runState R x0 v j) ∨
      rightPoint (runState R x0 v j) < xstar := by
    by_contra hcon
    push_neg at hcon
    exact hnotmid ⟨hcon.1, hcon.2⟩
  rcases hlt' with hxa | hbx
  · have hv : (v j).1 > (v j).2 := by
      by_contra hv
      push_neg at hv
      have hmem : xstar ∈ Icc (step (runState R x0 v j) (v j)).lo
          (step (runState R x0 v j) (v j)).hi := by
        rw [lo_step, hi_step, if_neg (by simpa using hv), if_neg (by simpa using hv)]
        exact ⟨hgood.1, le_of_lt (lt_trans hxa hlt)⟩
      exact hfail hmem
    have hm : f (leftPoint (runState R x0 v j)) ≤ f (rightPoint (runState R x0 v j)) :=
      monotoneOn_Ici_of_isMinOn hconv hmin (show leftPoint (runState R x0 v j) ∈ Ici xstar by
        simpa only [mem_Ici] using le_of_lt hxa)
        (show rightPoint (runState R x0 v j) ∈ Ici xstar by
          simpa only [mem_Ici] using le_of_lt (lt_trans hxa hlt)) hlt.le
    have hb : f (rightPoint (runState R x0 v j)) - f (leftPoint (runState R x0 v j)) ≤
        |(v j).1 - f (leftPoint (runState R x0 v j))| +
          |(v j).2 - f (rightPoint (runState R x0 v j))| := by
      have hkey : f (rightPoint (runState R x0 v j)) - f (leftPoint (runState R x0 v j)) ≤
          ((v j).1 - f (leftPoint (runState R x0 v j))) -
            ((v j).2 - f (rightPoint (runState R x0 v j))) := by linarith
      linarith [le_abs_self ((v j).1 - f (leftPoint (runState R x0 v j))),
        neg_le_abs ((v j).2 - f (rightPoint (runState R x0 v j)))]
    have habs : |f (rightPoint (runState R x0 v j)) - f (leftPoint (runState R x0 v j))| =
        f (rightPoint (runState R x0 v j)) - f (leftPoint (runState R x0 v j)) :=
      abs_of_nonneg (by linarith)
    calc min (f (leftPoint (runState R x0 v j))) (f (rightPoint (runState R x0 v j))) - f xstar
        ≤ |f (rightPoint (runState R x0 v j)) - f (leftPoint (runState R x0 v j))| := hgap
      _ = f (rightPoint (runState R x0 v j)) - f (leftPoint (runState R x0 v j)) := habs
      _ ≤ _ := hb
  · have hv : ¬ ((v j).1 > (v j).2) := by
      intro hv
      have hmem : xstar ∈ Icc (step (runState R x0 v j) (v j)).lo
          (step (runState R x0 v j) (v j)).hi := by
        rw [lo_step, hi_step, if_pos (by simpa using hv), if_pos (by simpa using hv)]
        exact ⟨le_of_lt (lt_trans hlt hbx), hgood.2⟩
      exact hfail hmem
    have hm : f (rightPoint (runState R x0 v j)) ≤ f (leftPoint (runState R x0 v j)) :=
      antitoneOn_Iic_of_isMinOn hconv hmin (show leftPoint (runState R x0 v j) ∈ Iic xstar by
        simpa only [mem_Iic] using le_of_lt (lt_trans hlt hbx))
        (show rightPoint (runState R x0 v j) ∈ Iic xstar by
          simpa only [mem_Iic] using le_of_lt hbx) hlt.le
    have hb : f (leftPoint (runState R x0 v j)) - f (rightPoint (runState R x0 v j)) ≤
        |(v j).1 - f (leftPoint (runState R x0 v j))| +
          |(v j).2 - f (rightPoint (runState R x0 v j))| := by
      have hkey : f (leftPoint (runState R x0 v j)) - f (rightPoint (runState R x0 v j)) ≤
          ((v j).2 - f (rightPoint (runState R x0 v j))) -
            ((v j).1 - f (leftPoint (runState R x0 v j))) := by linarith
      linarith [le_abs_self ((v j).2 - f (rightPoint (runState R x0 v j))),
        neg_le_abs ((v j).1 - f (leftPoint (runState R x0 v j)))]
    have habs : |f (rightPoint (runState R x0 v j)) - f (leftPoint (runState R x0 v j))| =
        f (leftPoint (runState R x0 v j)) - f (rightPoint (runState R x0 v j)) := by
      rw [abs_of_nonpos (by linarith)]; ring
    calc min (f (leftPoint (runState R x0 v j))) (f (rightPoint (runState R x0 v j))) - f xstar
        ≤ |f (rightPoint (runState R x0 v j)) - f (leftPoint (runState R x0 v j))| := hgap
      _ = f (leftPoint (runState R x0 v j)) - f (rightPoint (runState R x0 v j)) := habs
      _ ≤ _ := hb

end OracleTemplate.LineSearch

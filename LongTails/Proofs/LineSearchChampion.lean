import LongTails.Algorithms.LineSearch
import LongTails.Proofs.LineSearchInterval

open Set

namespace OracleTemplate.LineSearch

variable (R x0 : ℝ)

lemma leftPoint_eq_ptLeft (s : State) : leftPoint s = ptLeft s.lo s.hi := rfl

lemma rightPoint_eq_ptRight (s : State) : rightPoint s = ptRight s.lo s.hi := rfl

lemma lo_inner_update (s : State) (v : ℝ × ℝ) :
    ((inner R x0).update s v).lo = (if v.1 > v.2 then leftPoint s else s.lo) := by
  simp only [inner]
  split_ifs <;> rfl

lemma hi_inner_update (s : State) (v : ℝ × ℝ) :
    ((inner R x0).update s v).hi = (if v.1 > v.2 then s.hi else rightPoint s) := by
  simp only [inner]
  split_ifs <;> rfl

lemma champVal_inner_update (s : State) (v : ℝ × ℝ) :
    ((inner R x0).update s v).champVal =
      (if s.level = 0 then min v.1 v.2
        else if min v.1 v.2 < s.champVal then min v.1 v.2 else s.champVal) := by
  simp only [inner]
  split_ifs <;> rfl

lemma champ_inner_update (s : State) (v : ℝ × ℝ) :
    ((inner R x0).update s v).champ =
      (if s.level = 0 then (if v.1 > v.2 then rightPoint s else leftPoint s)
        else if min v.1 v.2 < s.champVal then
          (if v.1 > v.2 then rightPoint s else leftPoint s) else s.champ) := by
  simp only [inner]
  split_ifs <;> rfl

lemma interval_inner_update (s : State) (v : ℝ × ℝ) :
    (((inner R x0).update s v).lo, ((inner R x0).update s v).hi) =
      stepInterval s.lo s.hi v := by
  rw [lo_inner_update R x0 s v, hi_inner_update R x0 s v]
  simp only [stepInterval, leftPoint_eq_ptLeft, rightPoint_eq_ptRight, ptLeft, ptRight]
  by_cases hv : v.1 > v.2 <;> simp [hv]

lemma interval_inner_update_subset (s : State) (hs : s.lo ≤ s.hi) (v : ℝ × ℝ) :
    s.lo ≤ ((inner R x0).update s v).lo ∧ ((inner R x0).update s v).hi ≤ s.hi := by
  have h := interval_inner_update R x0 s v
  have hsub := stepInterval_subset hs v
  rw [← h] at hsub
  exact ⟨hsub.1, hsub.2⟩

lemma interval_inner_update_contains (s : State) {x : ℝ}
    (hx : x ∈ Icc s.lo s.hi) (hmid : x ∈ Icc (leftPoint s) (rightPoint s)) (v : ℝ × ℝ) :
    x ∈ Icc ((inner R x0).update s v).lo ((inner R x0).update s v).hi := by
  have h := interval_inner_update R x0 s v
  have hc := stepInterval_contains hx hmid v
  rw [← h] at hc
  have h1 : ptLeft s.lo s.hi = leftPoint s := (leftPoint_eq_ptLeft s).symm
  have h2 : ptRight s.lo s.hi = rightPoint s := (rightPoint_eq_ptRight s).symm
  simpa only [h1, h2] using hc

lemma interval_inner_update_len (s : State) (v : ℝ × ℝ) :
    ((inner R x0).update s v).hi - ((inner R x0).update s v).lo = 2 * (s.hi - s.lo) / 3 := by
  have h := interval_inner_update R x0 s v
  have hlen := stepInterval_len (l := s.lo) (h := s.hi) v
  rw [← h] at hlen
  exact hlen

end OracleTemplate.LineSearch

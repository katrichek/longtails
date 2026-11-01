import LongTails.Algorithms.Batched

namespace OracleTemplate.LineSearch

open scoped BigOperators

structure State where
  level : ℕ
  lo : ℝ
  hi : ℝ
  champ : ℝ
  champVal : ℝ

noncomputable def leftPoint (s : State) : ℝ := s.lo + (s.hi - s.lo) / 3

noncomputable def rightPoint (s : State) : ℝ := s.lo + 2 * (s.hi - s.lo) / 3

noncomputable def inner (R x0 : ℝ) : Algorithm ℝ (ℝ × ℝ) ℝ where
  State := State
  initial _ := { level := 0, lo := x0 - R, hi := x0 + R, champ := x0, champVal := 0 }
  query s := (0, leftPoint s)
  update s v :=
    if s.level = 0 then
      { level := 1,
        lo := (if v.1 > v.2 then leftPoint s else s.lo),
        hi := (if v.1 > v.2 then s.hi else rightPoint s),
        champ := (if v.1 > v.2 then rightPoint s else leftPoint s),
        champVal := min v.1 v.2 }
    else
      if min v.1 v.2 < s.champVal then
        { level := s.level + 1,
          lo := (if v.1 > v.2 then leftPoint s else s.lo),
          hi := (if v.1 > v.2 then s.hi else rightPoint s),
          champ := (if v.1 > v.2 then rightPoint s else leftPoint s),
          champVal := min v.1 v.2 }
      else
        { level := s.level + 1,
          lo := (if v.1 > v.2 then leftPoint s else s.lo),
          hi := (if v.1 > v.2 then s.hi else rightPoint s),
          champ := s.champ,
          champVal := s.champVal }
  output s := s.champ

noncomputable def queries (R x0 : ℝ) (m : ℕ) : (inner R x0).State → Fin (2 * m) → ℝ :=
  fun s i => if (i : ℕ) < m then leftPoint s else rightPoint s

noncomputable def decode (R x0 : ℝ) {m : ℕ} :
    (inner R x0).State → (Fin (2 * m) → ℝ) → (ℝ × ℝ) :=
  fun _ r =>
    ((∑ j : Fin m, r ⟨j.val, by omega⟩) / (m : ℝ),
      (∑ j : Fin m, r ⟨m + j.val, by omega⟩) / (m : ℝ))

noncomputable def lineSearch (R x0 : ℝ) {m : ℕ} (hn : 0 < 2 * m) : Algorithm ℝ ℝ ℝ :=
  batched hn (inner R x0) (queries R x0 m) (decode R x0) 0

end OracleTemplate.LineSearch

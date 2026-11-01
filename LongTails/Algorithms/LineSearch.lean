import LongTails.Algorithms.Batched

namespace OracleTemplate.LineSearch

open scoped BigOperators

abbrev State : Type := ℕ × ℝ × ℝ × ℝ × ℝ

def lo (s : State) : ℝ := s.2.1
def hi (s : State) : ℝ := s.2.2.1
def champ (s : State) : ℝ := s.2.2.2.1
def champVal (s : State) : ℝ := s.2.2.2.2
noncomputable def leftPoint (s : State) : ℝ := s.2.1 + (s.2.2.1 - s.2.1) / 3
noncomputable def rightPoint (s : State) : ℝ := s.2.1 + 2 * (s.2.2.1 - s.2.1) / 3

noncomputable def inner (R x0 : ℝ) : Algorithm ℝ (ℝ × ℝ) ℝ where
  State := State
  initial _ := (0, x0 - R, x0 + R, x0, 0)
  query s := (0, leftPoint s)
  update s v :=
    if s.1 = 0 then
      (1, (if v.1 > v.2 then leftPoint s else lo s), (if v.1 > v.2 then hi s else rightPoint s),
        (if v.1 > v.2 then rightPoint s else leftPoint s), min v.1 v.2)
    else
      let s' := (s.1 + 1, (if v.1 > v.2 then leftPoint s else lo s),
        (if v.1 > v.2 then hi s else rightPoint s), champ s, champVal s)
      if min v.1 v.2 < champVal s then
        (s'.1, s'.2.1, s'.2.2.1, (if v.1 > v.2 then rightPoint s else leftPoint s), min v.1 v.2)
      else s'
  output s := champ s

noncomputable def queries (R x0 : ℝ) (m : ℕ) :
    (inner R x0).State → Fin (2 * m) → ℝ :=
  fun s i => if (i : ℕ) < m then leftPoint s else rightPoint s

noncomputable def decode (R x0 : ℝ) {m : ℕ} :
    (inner R x0).State → (Fin (2 * m) → ℝ) → (ℝ × ℝ) :=
  fun _ r =>
    ((∑ j : Fin m, r ⟨j.val, by omega⟩) / (m : ℝ),
      (∑ j : Fin m, r ⟨m + j.val, by omega⟩) / (m : ℝ))

noncomputable def lineSearch (R x0 : ℝ) {m : ℕ} (hn : 0 < 2 * m) : Algorithm ℝ ℝ ℝ :=
  batched hn (inner R x0) (queries R x0 m) (decode R x0) 0

end OracleTemplate.LineSearch

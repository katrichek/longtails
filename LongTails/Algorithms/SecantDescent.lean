import LongTails.Algorithms.Batched
import LongTails.Algorithms.AcceleratedZerothOrderConvex

namespace OracleTemplate.SecantDescent

open scoped BigOperators
open OracleTemplate.ZerothOrder LongTails.Setups.ZerothOrderSmoothAndConvex

variable {d m : ℕ}

noncomputable def descent (L : ℝ) (x0 : Point d) : Algorithm (Point d) (Point d) (Point d) where
  State := ℕ × Point d
  initial _ := (0, x0)
  query s := (0, s.2)
  update s v := (s.1 + 1, s.2 - (1 / L) • v)
  output s := s.2

abbrev secantSpace (d m : ℕ) := (Fin d × Fin m) × Bool

noncomputable def secantIndex {m : ℕ}
    (t : Fin (Fintype.card (secantSpace d m))) : secantSpace d m :=
  (Fintype.equivFin (secantSpace d m)).symm t

noncomputable def centralDifference (h : ℝ) (x : Point d) (f : Point d → ℝ) : Point d :=
  ∑ i : Fin d, ((f (x + h • direction i) - f (x - h • direction i)) / (2 * h)) • direction i

noncomputable def secantQuery (h : ℝ) (s : ℕ × Point d)
    (t : Fin (Fintype.card (secantSpace d m))) : Point d :=
  let j := secantIndex t
  if j.2 then s.2 + h • direction j.1.1 else s.2 - h • direction j.1.1

noncomputable def secantDecode (h : ℝ) (_s : ℕ × Point d)
    (replies : Fin (Fintype.card (secantSpace d m)) → ℝ) : Point d :=
  (1 / (m : ℝ)) • ∑ j : secantSpace d m,
    ((if j.2 then replies (Fintype.equivFin _ j) else -replies (Fintype.equivFin _ j)) / (2 * h)) •
      direction j.1.1

lemma secant_nonempty (hd : 0 < d) (hm : 0 < m) : Nonempty (secantSpace d m) :=
  ⟨((⟨0, hd⟩ : Fin d), ⟨0, hm⟩), false⟩

lemma secant_card_pos (hd : 0 < d) (hm : 0 < m) : 0 < Fintype.card (secantSpace d m) := by
  classical
  rw [Fintype.card_pos_iff]
  exact secant_nonempty hd hm

noncomputable def secantDescent (hd : 0 < d) (hm : 0 < m) (L h : ℝ) (x0 : Point d) :
    Algorithm (Point d) ℝ (Point d) :=
  batched (secant_card_pos hd hm) (descent L x0) (secantQuery h) (fun s => secantDecode h s) 0

lemma secantQuery_apply (h : ℝ) (x : Point d)
    (t : Fin (Fintype.card (secantSpace d m))) :
    secantQuery h (k, x) t =
      if (secantIndex t).2 then x + h • direction (secantIndex t).1.1
      else x - h • direction (secantIndex t).1.1 := by
  simp [secantQuery]

end OracleTemplate.SecantDescent

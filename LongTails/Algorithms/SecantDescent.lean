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


noncomputable def secantSign {m : ℕ}
    (t : Fin (Fintype.card (secantSpace d m))) : Bool := (secantIndex t).2

noncomputable def secantCoord {m : ℕ}
    (t : Fin (Fintype.card (secantSpace d m))) : Fin d := (secantIndex t).1.1

noncomputable def secantPoint (h : ℝ) (x : Point d)
    (t : Fin (Fintype.card (secantSpace d m))) : Point d :=
  if secantSign t then x + h • direction (secantCoord t) else x

noncomputable def secantQuery (h : ℝ) (s : ℕ × Point d)
    (t : Fin (Fintype.card (secantSpace d m))) : Point d :=
  secantPoint h s.2 t

noncomputable def secantDecode (h : ℝ) (_s : ℕ × Point d)
    (replies : Fin (Fintype.card (secantSpace d m)) → ℝ) : Point d :=
  (1 / (m : ℝ)) • ∑ t, ((if secantSign t then replies t else -replies t) / h) •
    direction (secantCoord t)

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
    secantQuery h (k, x) t = secantPoint h x t := by
  simp [secantQuery]

lemma secantIndex_apply
    (a : secantSpace d m) :
    secantIndex (Fintype.equivFin (secantSpace d m) a) = a :=
  Equiv.symm_apply_apply _ _

lemma secantIndex_apply'
    (t : Fin (Fintype.card (secantSpace d m))) :
    Fintype.equivFin (secantSpace d m) (secantIndex t) = t :=
  Equiv.apply_symm_apply _ _

end OracleTemplate.SecantDescent

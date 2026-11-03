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

/-- One gradient step needs `m` replicas of the `d` coordinate two-sided differences. -/
abbrev secantSpace (d m : ℕ) := Fin m × (Fin d × Bool)

noncomputable def secantSign (t : secantSpace d m) : Bool := t.2.2

noncomputable def secantCoord (t : secantSpace d m) : Fin d := t.2.1

noncomputable def secantPoint (h : ℝ) (x : Point d) (t : secantSpace d m) : Point d :=
  if secantSign t then x + h • direction (secantCoord t) else x

noncomputable def secantQuery (h : ℝ) (s : ℕ × Point d) (t : secantSpace d m) : Point d :=
  secantPoint h s.2 t

noncomputable def secantDecode (h : ℝ) (_s : ℕ × Point d)
    (replies : secantSpace d m → ℝ) : Point d :=
  (1 / (m : ℝ)) • ∑ t, ((if secantSign t then replies t else -replies t) / h) •
    direction (secantCoord t)

lemma secant_nonempty (hd : 0 < d) (hm : 0 < m) : Nonempty (secantSpace d m) :=
  ⟨(⟨0, hm⟩, (⟨0, hd⟩, false))⟩

lemma card_secantSpace (d m : ℕ) : Fintype.card (secantSpace d m) = 2 * d * m := by
  classical
  calc Fintype.card (secantSpace d m) = Fintype.card (Fin m × (Fin d × Bool)) := rfl
    _ = Fintype.card (Fin m) * Fintype.card (Fin d × Bool) := Fintype.card_prod _ _
    _ = Fintype.card (Fin m) * (Fintype.card (Fin d) * Fintype.card Bool) := by
          rw [Fintype.card_prod]
    _ = m * (d * 2) := by rw [Fintype.card_fin, Fintype.card_fin, Fintype.card_bool]
    _ = 2 * d * m := by simp [Nat.mul_comm, Nat.mul_left_comm]

lemma secant_card_pos (hd : 0 < d) (hm : 0 < m) : 0 < Fintype.card (secantSpace d m) := by
  classical
  rw [Fintype.card_pos_iff]
  exact secant_nonempty hd hm

/-- The algorithm slot drawn by the `t`-th call of a batch. -/
noncomputable def secantSlot {d m : ℕ} (t : Fin (Fintype.card (secantSpace d m))) :
    secantSpace d m :=
  (Fintype.equivFin (secantSpace d m)).symm t

lemma secantSlot_equivFin {d m : ℕ} (a : secantSpace d m) :
    secantSlot (Fintype.equivFin (secantSpace d m) a) = a :=
  Equiv.symm_apply_apply _ _

noncomputable def secantDescent (hd : 0 < d) (hm : 0 < m) (L h : ℝ) (x0 : Point d) :
    Algorithm (Point d) ℝ (Point d) :=
  batched (secant_card_pos hd hm) (descent L x0)
    (fun s t => secantQuery h s (secantSlot t))
    (fun s replies => secantDecode h s (fun t => replies (Fintype.equivFin (secantSpace d m) t))) 0

lemma secantQuery_apply (h : ℝ) (x : Point d) (t : secantSpace d m) :
    secantQuery h (k, x) t = secantPoint h x t := by
  simp [secantQuery]

end OracleTemplate.SecantDescent

import LongTails.Algorithms.CenteredMomentumSecant

/-!
Research candidate for the additional QuinticBias regularity assumption:
the fourth-order four-value stencil (-f(x+2h)+8f(x+h)-8f(x-h)+f(x-2h))/(12h).
One round costs 4*d*m(k) scalar value queries.
-/
namespace OracleTemplate.Research.QuinticFourPointMomentumZO

open OracleTemplate.SecantPolyak.Centered
open OracleTemplate.InexactGradient
open OracleTemplate.ZerothOrder
open LongTails.Setups.ZerothOrderSmoothAndConvex
open scoped BigOperators

abbrev Slot (d m : ℕ) := Fin m × (Fin d × Fin 4)

noncomputable def slot {d m : ℕ} (t : Fin (Fintype.card (Slot d m))) : Slot d m :=
  (Fintype.equivFin (Slot d m)).symm t

noncomputable def queryPoint {d m : ℕ} (h : ℝ) (x : Point d) (t : Slot d m) : Point d :=
  let e := direction t.2.1
  if t.2.2 = 0 then x + (2 * h) • e
  else if t.2.2 = 1 then x + h • e
  else if t.2.2 = 2 then x - h • e
  else x - (2 * h) • e

noncomputable def coeff (j : Fin 4) : ℝ :=
  if j = 0 then -1 else if j = 1 then 8 else if j = 2 then -8 else 1

noncomputable def decode {d m : ℕ} (h : ℝ) (replies : Slot d m → ℝ) : Point d :=
  (1 / (m : ℝ)) • ∑ t : Slot d m,
    ((coeff t.2.2 * replies t) / (12 * h)) • direction t.2.1

lemma slot_card_pos {d m : ℕ} (hd : 0 < d) (hm : 0 < m) :
    0 < Fintype.card (Slot d m) := by
  classical
  rw [Fintype.card_pos_iff]
  exact ⟨(⟨0, hm⟩, (⟨0, hd⟩, ⟨0, by omega⟩))⟩

noncomputable def queries {d : ℕ} {m : ℕ → ℕ} (theta h : ℝ) :
    ∀ k : ℕ, (ℕ × Point d × Point d) →
      Fin (Fintype.card (Slot d (m k))) → Point d :=
  fun _ s t => queryPoint h
    (OracleTemplate.InexactGradient.query theta ⟨s.2.1, s.2.2⟩)
    (slot t)

noncomputable def decoder {d : ℕ} {m : ℕ → ℕ} (h : ℝ) :
    ∀ k : ℕ, (ℕ × Point d × Point d) →
      (Fin (Fintype.card (Slot d (m k))) → ℝ) → Point d :=
  fun k _ replies => decode h
    (fun t : Slot d (m k) => replies (Fintype.equivFin _ t))

/-- Every iteration consumes 4*d*m(k) raw function values. -/
noncomputable def algorithm {d : ℕ} (hd : 0 < d) {m : ℕ → ℕ}
    (hm : ∀ k, 0 < m k) (L mu theta h : ℝ) (x0 : Point d) :
    OracleTemplate.Algorithm (Point d) ℝ (Point d) :=
  OracleTemplate.batchedSched
    (fun k => Fintype.card (Slot d (m k)))
    (fun k => slot_card_pos hd (hm k))
    (cmBase L mu theta x0) (queries theta h) (decoder h) 0

end OracleTemplate.Research.QuinticFourPointMomentumZO

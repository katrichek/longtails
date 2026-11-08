import LongTails.Algorithms.CenteredMomentumSecant

/-!
Research candidate: same scalar value query as the original setup, but
CENTRAL differences x + h e_i and x - h e_i, with the existing two-vector momentum core.
Unlike forward differences, the central estimator can have O(h^2) bias
under the EXTRA regularity condition of CubicBias.spec.
-/
namespace OracleTemplate.Research.CubicCentralMomentumZO

open OracleTemplate.SecantDescent
open OracleTemplate.SecantPolyak.Centered
open OracleTemplate.ZerothOrder
open LongTails.Setups.ZerothOrderSmoothAndConvex
open scoped BigOperators

noncomputable def centralPoint {d m : ℕ} (h : ℝ) (x : Point d)
    (t : secantSpace d m) : Point d :=
  if secantSign t then x + h • direction (secantCoord t)
  else x - h • direction (secantCoord t)

noncomputable def centralDecode {d m : ℕ} (h : ℝ)
    (replies : secantSpace d m → ℝ) : Point d :=
  (1 / (m : ℝ)) • ∑ t : secantSpace d m,
    ((if secantSign t then replies t else -replies t) / (2 * h)) •
      direction (secantCoord t)

noncomputable def queries {d : ℕ} {m : ℕ → ℕ} (theta h : ℝ) :
    ∀ k : ℕ, (ℕ × Point d × Point d) →
      Fin (Fintype.card (secantSpace d (m k))) → Point d :=
  fun _ s t => centralPoint h
    (OracleTemplate.InexactGradient.query theta ⟨s.2.1, s.2.2⟩)
    (secantSlot t)

noncomputable def decoder {d : ℕ} {m : ℕ → ℕ} (h : ℝ) :
    ∀ k : ℕ, (ℕ × Point d × Point d) →
      (Fin (Fintype.card (secantSpace d (m k))) → ℝ) → Point d :=
  fun k _ replies => centralDecode h
    (fun t : secantSpace d (m k) => replies (Fintype.equivFin _ t))

/-- Every iteration consumes 2*d*m(k) raw function values. -/
noncomputable def algorithm {d : ℕ} (hd : 0 < d) {m : ℕ → ℕ}
    (hm : ∀ k, 0 < m k) (L mu theta h : ℝ) (x0 : Point d) :
    OracleTemplate.Algorithm (Point d) ℝ (Point d) :=
  OracleTemplate.batchedSched
    (fun k => Fintype.card (secantSpace d (m k)))
    (fun k => secant_card_pos hd (hm k))
    (cmBase L mu theta x0) (queries theta h) (decoder h) 0

end OracleTemplate.Research.CubicCentralMomentumZO

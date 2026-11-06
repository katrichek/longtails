import LongTails.Algorithms.InexactAccelerated
import LongTails.Algorithms.SecantDescent
import LongTails.Algorithms.BatchedScheduled
import LongTails.Setups.ZerothOrderSmoothingStronglyConvex

namespace OracleTemplate.SecantPolyak.DirectionSampled

open InexactGradient SecantDescent
open LongTails.Setups.ZerothOrderSmoothAndConvex
open LongTails.Setups.ZerothOrderSmoothingStronglyConvex
open scoped BigOperators

/-- The surrogate recovered from one reply at bandwidth `h`. -/
noncomputable def term {d : ℕ} (h : ℝ) (r : ℝ × Point d) : Point d := (1 / (2 * h)) • (r.1 • r.2)

/-- Momentum descent driven by direction-sampled surrogates. The state stores the current iterate
together with the momentum anchor; the oracle supplies the probe directions. -/
noncomputable def dirBase {d : ℕ} (L μ θ : ℝ) (x0 : Point d) :
    Algorithm (Point d × Bool) (Point d) (Point d) :=
  { State := ℕ × Point d × Point d
    initial _ := (0, x0, x0)
    query s := (0, (query θ ⟨s.2.1, s.2.2⟩, true))
    update s v := (s.1 + 1, (step L μ θ ⟨s.2.1, s.2.2⟩ v).1, (step L μ θ ⟨s.2.1, s.2.2⟩ v).2)
    output s := s.2.1 }

/-- Slot query of a direction-sampled round: the oracle probes the momentum point on the side of
the cell, choosing its own direction. -/
noncomputable def dirQS {d : ℕ} {m : ℕ → ℕ} (θ : ℝ) :
    ∀ k : ℕ, (ℕ × Point d × Point d) →
      Fin (Fintype.card (secantSpace 1 (m k))) → Point d × Bool :=
  fun _ s t => (query θ ⟨s.2.1, s.2.2⟩, secantSign (secantSlot t))

/-- Decoding of one direction-sampled round: the signed average of the reported one-sided terms. -/
noncomputable def dirDec {d : ℕ} {m : ℕ → ℕ} (h : ℝ) :
    ∀ k : ℕ, (ℕ × Point d × Point d) →
      (Fin (Fintype.card (secantSpace 1 (m k))) → ℝ × Point d) → Point d :=
  fun k _s replies =>
    (1 / (m k : ℝ)) •
      ∑ t : secantSpace 1 (m k),
        (if secantSign t then (1 : ℝ) else -1) •
          term h (replies (Fintype.equivFin (secantSpace 1 (m k)) t))

/-- Direction-sampled momentum descent: round `k` asks the oracle for `2 * m k` one-sided probes
along its own independent directions at the momentum point and drives both the iterate and the
anchor by the signed average of the reported terms. -/
noncomputable def dirDescent {d : ℕ} {m : ℕ → ℕ} (hm : ∀ k, 0 < m k) (L μ θ h : ℝ) (x0 : Point d) :
    Algorithm (Point d × Bool) (ℝ × Point d) (Point d) :=
  batchedSched (fun k => Fintype.card (secantSpace 1 (m k)))
    (fun k => secant_card_pos (show 0 < 1 from Nat.zero_lt_one) (hm k))
    (dirBase L μ θ x0) (dirQS θ) (dirDec h) (0, 0)

end OracleTemplate.SecantPolyak.DirectionSampled

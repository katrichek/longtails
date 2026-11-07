import LongTails.Algorithms.InexactAccelerated
import LongTails.Algorithms.SecantDescent
import LongTails.Algorithms.BatchedScheduled
import LongTails.Algorithms.DirectionSampledMomentum
import LongTails.Setups.ZerothOrderSmoothingStrongGrowth

namespace OracleTemplate.SecantPolyak.Interpolated

open InexactGradient SecantDescent
open OracleTemplate.SecantPolyak.DirectionSampled
open LongTails.Setups.ZerothOrderSmoothAndConvex
open LongTails.Setups.ZerothOrderSmoothingStrongGrowth

/-- Single-iterate descent driven by one mirrored probe pair per step. The state keeps only the
current iterate, so there is no momentum anchor and no averaging window. -/
noncomputable def ipBase {d : ℕ} (η : ℝ) (x0 : Point d) :
    Algorithm (Point d × Bool) (Point d) (Point d) :=
  { State := ℕ × Point d
    initial _ := (0, x0)
    query s := (0, (s.2, true))
    update s v := (s.1 + 1, s.2 - η • v)
    output s := s.2 }

/-- Slot query of a mirrored pair: the oracle probes the current iterate on each side of its own
sampled direction. -/
noncomputable def ipQS {d : ℕ} :
    ∀ _k : ℕ, (ℕ × Point d) → Fin (Fintype.card (secantSpace 1 1)) → Point d × Bool :=
  fun _ s t => (s.2, secantSign (secantSlot t))

/-- Decoding of one mirrored pair: the signed sum of the two reported one-sided terms, which
estimates the smoothed gradient at the current iterate. -/
noncomputable def ipDec {d : ℕ} (h : ℝ) :
    ∀ _k : ℕ, (ℕ × Point d) →
      (Fin (Fintype.card (secantSpace 1 1)) → ℝ × Point d) → Point d :=
  fun _ _s replies =>
    ∑ t : secantSpace 1 1,
      (if secantSign t then (1 : ℝ) else -1) •
        term h (replies (Fintype.equivFin (secantSpace 1 1) t))

/-- Interpolated mirrored-pair descent: step `k` asks two one-sided probes along fresh directions
at the current iterate and moves a fixed distance `η` against their signed sum. -/
noncomputable def ipDescent {d : ℕ} (η h : ℝ) (x0 : Point d) :
    Algorithm (Point d × Bool) (ℝ × Point d) (Point d) :=
  batchedSched (fun _ => Fintype.card (secantSpace 1 1))
    (fun _ => secant_card_pos (show 0 < 1 from Nat.zero_lt_one) Nat.one_pos)
    (ipBase η x0) ipQS (ipDec h) (0, 0)

end OracleTemplate.SecantPolyak.Interpolated

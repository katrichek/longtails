import LongTails.Algorithms.InexactAccelerated
import LongTails.Algorithms.SecantDescent
import LongTails.Algorithms.BatchedScheduled
import LongTails.Algorithms.DirectionSampledMomentum
import LongTails.Setups.ZerothOrderSmoothingGrowthConvex

namespace OracleTemplate.SecantPolyak.GrowthConvex

open InexactGradient SecantDescent
open OracleTemplate.SecantPolyak.DirectionSampled
open LongTails.Setups.ZerothOrderSmoothAndConvex

/-- Averaged descent driven by one mirrored probe pair per step. The state keeps the current
iterate together with the sum of the iterates visited so far, so the output is the uniform average,
which is the accuracy carrier for a merely convex objective. -/
noncomputable def gpBase {d : ℕ} (η : ℝ) (x0 : Point d) :
    Algorithm (Point d × Bool) (Point d) (Point d) :=
  { State := ℕ × Point d × Point d
    initial _ := (0, x0, 0)
    query s := (0, (s.2.1, true))
    update s v := (s.1 + 1, s.2.1 - η • v, s.2.2 + s.2.1)
    output s := (1 / max 1 (s.1 : ℝ)) • s.2.2 }

/-- Slot query of a mirrored pair: the oracle probes the current iterate on each side of its own
sampled direction. -/
noncomputable def gpQS {d : ℕ} :
    ∀ _k : ℕ, (ℕ × Point d × Point d) → Fin (Fintype.card (secantSpace 1 1)) → Point d × Bool :=
  fun _ s t => (s.2.1, secantSign (secantSlot t))

/-- Decoding of one mirrored pair: the signed sum of the two reported one-sided terms, which
estimates the smoothed gradient at the current iterate. -/
noncomputable def gpDec {d : ℕ} (h : ℝ) :
    ∀ _k : ℕ, (ℕ × Point d × Point d) →
      (Fin (Fintype.card (secantSpace 1 1)) → ℝ × Point d) → Point d :=
  fun _ _s replies =>
    ∑ t : secantSpace 1 1,
      (if secantSign t then (1 : ℝ) else -1) •
        term h (replies (Fintype.equivFin (secantSpace 1 1) t))

/-- Growth-convex probe descent: step `k` asks two one-sided probes along fresh directions at the
current iterate, moves a fixed distance `η` against their signed sum, and accumulates the iterate. -/
noncomputable def gpDescent {d : ℕ} (η h : ℝ) (x0 : Point d) :
    Algorithm (Point d × Bool) (ℝ × Point d) (Point d) :=
  batchedSched (fun _ => Fintype.card (secantSpace 1 1))
    (fun _ => secant_card_pos (show 0 < 1 from Nat.zero_lt_one) Nat.one_pos)
    (gpBase η x0) gpQS (gpDec h) (0, 0)

end OracleTemplate.SecantPolyak.GrowthConvex

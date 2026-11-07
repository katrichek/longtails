import LongTails.Algorithms.InexactAccelerated
import LongTails.Algorithms.SecantDescent
import LongTails.Algorithms.BatchedScheduled
import LongTails.Algorithms.DirectionSampledMomentum
import LongTails.Setups.ZerothOrderSmoothingInterpolatedAcceleration

namespace OracleTemplate.SecantPolyak.AnchoredPair

open InexactGradient SecantDescent
open OracleTemplate.SecantPolyak.DirectionSampled
open LongTails.Setups.ZerothOrderSmoothAndConvex (Point)

/-- One damped anchored update. The iterate takes the damped step against the surrogate of the
interpolated point, while the anchor absorbs the same surrogate with the accelerated weight. -/
noncomputable def apStep {d : ℕ} (μ θ η : ℝ) (s : Point d × Point d) (v : Point d) :
    Point d × Point d :=
  (query θ s - η • v, (1 - θ) • s.2 + θ • query θ s - (2 * θ / μ) • v)

/-- Damped anchored pair acceleration. The state keeps the iterate together with the momentum
anchor, and the output is the iterate. -/
noncomputable def apBase {d : ℕ} (μ θ η : ℝ) (x0 : Point d) :
    Algorithm (Point d × Bool) (Point d) (Point d) :=
  { State := ℕ × Point d × Point d
    initial _ := (0, x0, x0)
    query s := (0, (query θ ⟨s.2.1, s.2.2⟩, true))
    update s v :=
      (s.1 + 1, (apStep μ θ η ⟨s.2.1, s.2.2⟩ v).1, (apStep μ θ η ⟨s.2.1, s.2.2⟩ v).2)
    output s := s.2.1 }

/-- Slot query of one damped anchored round: the oracle probes the interpolated point on the side
picked by the cell, choosing its own direction. -/
noncomputable def apQS {d : ℕ} (θ : ℝ) :
    ∀ _k : ℕ, (ℕ × Point d × Point d) → Fin (Fintype.card (secantSpace 1 1)) → Point d × Bool :=
  fun _ s t => (query θ ⟨s.2.1, s.2.2⟩, secantSign (secantSlot t))

/-- Decoding of one damped anchored round: the signed sum of the two reported one-sided terms of
the interpolated point, which estimates the smoothed gradient there. -/
noncomputable def apDec {d : ℕ} (h : ℝ) :
    ∀ _k : ℕ, (ℕ × Point d × Point d) →
      (Fin (Fintype.card (secantSpace 1 1)) → ℝ × Point d) → Point d :=
  fun _ _s replies =>
    ∑ t : secantSpace 1 1,
      (if secantSign t then (1 : ℝ) else -1) •
        term h (replies (Fintype.equivFin (secantSpace 1 1) t))

/-- Damped anchored pair acceleration: round `k` asks two one-sided probes of the interpolated point
along one fresh direction and drives both the iterate and the anchor by their signed sum. -/
noncomputable def apDescent {d : ℕ} (μ θ η h : ℝ) (x0 : Point d) :
    Algorithm (Point d × Bool) (ℝ × Point d) (Point d) :=
  batchedSched (fun _ => Fintype.card (secantSpace 1 1))
    (fun _ => secant_card_pos (show 0 < 1 from Nat.zero_lt_one) Nat.one_pos)
    (apBase μ θ η x0) (apQS θ) (apDec h) (0, 0)

end OracleTemplate.SecantPolyak.AnchoredPair

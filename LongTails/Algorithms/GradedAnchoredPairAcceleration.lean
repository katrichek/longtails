import LongTails.Algorithms.InexactAccelerated
import LongTails.Algorithms.SecantDescent
import LongTails.Algorithms.BatchedScheduled
import LongTails.Algorithms.DirectionSampledMomentum
import LongTails.Setups.ZerothOrderSmoothingBatchedAcceleration

namespace OracleTemplate.SecantPolyak.GradedAnchored

open InexactGradient SecantDescent
open OracleTemplate.SecantPolyak.DirectionSampled
open LongTails.Setups.ZerothOrderSmoothAndConvex (Point)

/-- One weighted anchored update. The iterate takes the damped step against the batched surrogate of
the interpolated point, while the anchor absorbs the same surrogate with weight `θ / (2 * β)`, which
is the weight the weighted potential telescopes with. -/
noncomputable def waStep {d : ℕ} (β θ η : ℝ) (s : Point d × Point d) (v : Point d) :
    Point d × Point d :=
  (query θ s - η • v, (1 - θ) • s.2 + θ • query θ s - (θ / (2 * β)) • v)

/-- Weighted anchored pair acceleration. The state keeps the iterate together with the momentum
anchor, and the output is the iterate. -/
noncomputable def agBase {d : ℕ} (β θ η : ℝ) (x0 : Point d) :
    Algorithm (Point d × Bool) (Point d) (Point d) :=
  { State := ℕ × Point d × Point d
    initial _ := (0, x0, x0)
    query s := (0, (query θ ⟨s.2.1, s.2.2⟩, true))
    update s v :=
      (s.1 + 1, (waStep β θ η ⟨s.2.1, s.2.2⟩ v).1, (waStep β θ η ⟨s.2.1, s.2.2⟩ v).2)
    output s := s.2.1 }

/-- Slot query of one graded anchored round: the oracle probes the interpolated point on the side
picked by the cell, choosing its own direction. Round `k` owns `2 * m k` slots. -/
noncomputable def agQS {d : ℕ} {m : ℕ → ℕ} (θ : ℝ) :
    ∀ _k : ℕ, (ℕ × Point d × Point d) → Fin (Fintype.card (secantSpace 1 (m _k))) → Point d × Bool :=
  fun _ s t => (query θ ⟨s.2.1, s.2.2⟩, secantSign (secantSlot t))

/-- Decoding of one graded anchored round: the signed average of the `2 * m k` reported one-sided
terms of the interpolated point, which estimates the smoothed gradient there. -/
noncomputable def agDec {d : ℕ} {m : ℕ → ℕ} (h : ℝ) :
    ∀ _k : ℕ, (ℕ × Point d × Point d) →
      (Fin (Fintype.card (secantSpace 1 (m _k))) → ℝ × Point d) → Point d :=
  fun k _s replies =>
    (1 / (m k : ℝ)) •
      ∑ t : secantSpace 1 (m k),
        (if secantSign t then (1 : ℝ) else -1) •
          term h (replies (Fintype.equivFin (secantSpace 1 (m k)) t))

/-- Graded anchored pair acceleration: round `k` asks the oracle for `2 * m k` one-sided probes along
its own independent directions at the interpolated point and drives both the iterate and the anchor
by their signed average. -/
noncomputable def agDescent {d : ℕ} {m : ℕ → ℕ} (hm : ∀ k, 0 < m k) (β θ η h : ℝ) (x0 : Point d) :
    Algorithm (Point d × Bool) (ℝ × Point d) (Point d) :=
  batchedSched (fun k => Fintype.card (secantSpace 1 (m k)))
    (fun k => secant_card_pos (show 0 < 1 from Nat.zero_lt_one) (hm k))
    (agBase β θ η x0) (agQS θ) (agDec h) (0, 0)

end OracleTemplate.SecantPolyak.GradedAnchored

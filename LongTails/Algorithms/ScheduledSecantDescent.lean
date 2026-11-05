import LongTails.Algorithms.SecantDescent
import LongTails.Algorithms.BatchedScheduled

namespace OracleTemplate.SecantPolyak.Scheduled

open SecantDescent
open LongTails.Setups.ZerothOrderSmoothAndConvex

/-- Batched secant descent whose round `k` averages `m k` independent replicas of every coordinate
two-sided difference. -/
noncomputable def schedDescent {d : ℕ} (hd : 0 < d) {m : ℕ → ℕ} (hm : ∀ k, 0 < m k)
    (L h : ℝ) (x0 : Point d) : Algorithm (Point d) ℝ (Point d) :=
  batchedSched (fun k => Fintype.card (secantSpace d (m k))) (fun k => secant_card_pos hd (hm k))
    (descent L x0) (fun _ s t => secantQuery h s (secantSlot t))
    (fun k s replies =>
      secantDecode h s (fun t : secantSpace d (m k) =>
        replies (Fintype.equivFin (secantSpace d (m k)) t))) 0

end OracleTemplate.SecantPolyak.Scheduled

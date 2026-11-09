import LongTails.Algorithms.InexactAccelerated
import LongTails.Algorithms.SecantDescent
import LongTails.Algorithms.BatchedScheduled
import LongTails.Algorithms.DirectionSampledMomentum
import LongTails.Setups.ZerothOrderSmoothAndConvex

namespace OracleTemplate.SecantPolyak.AnchoredConvexPair

open InexactGradient SecantDescent
open OracleTemplate.SecantPolyak.DirectionSampled
open LongTails.Setups.ZerothOrderSmoothAndConvex (Point)

noncomputable def dacWeight (k : ℕ) : ℝ :=
  (k : ℝ) * ((k : ℝ) + 1)

noncomputable def dacQuery {d : ℕ} (k : ℕ) (s : Point d × Point d) : Point d :=
  ((k : ℝ) / ((k : ℝ) + 4)) • s.1 + (4 / ((k : ℝ) + 4)) • s.2

noncomputable def dacStep {d : ℕ} (k : ℕ) (η : ℝ) (s : Point d × Point d) (v : Point d) :
    Point d × Point d :=
  (dacQuery k s - η • v, s.2 - (η * ((k : ℝ) + 1) / 4) • v)

noncomputable def dacBase {d : ℕ} (η : ℝ) (x0 : Point d) :
    Algorithm (Point d × Bool) (Point d) (Point d) :=
  { State := ℕ × Point d × Point d
    initial _ := (0, x0, x0)
    query s := (0, (dacQuery s.1 ⟨s.2.1, s.2.2⟩, true))
    update s v :=
      (s.1 + 1, (dacStep s.1 η ⟨s.2.1, s.2.2⟩ v).1, (dacStep s.1 η ⟨s.2.1, s.2.2⟩ v).2)
    output s := s.2.1 }

noncomputable def dacQS {d : ℕ} :
    ∀ _k : ℕ, (ℕ × Point d × Point d) → Fin (Fintype.card (secantSpace 1 1)) → Point d × Bool :=
  fun _ s t => (dacQuery s.1 ⟨s.2.1, s.2.2⟩, secantSign (secantSlot t))

noncomputable def dacDec {d : ℕ} (h : ℝ) :
    ∀ _k : ℕ, (ℕ × Point d × Point d) →
      (Fin (Fintype.card (secantSpace 1 1)) → ℝ × Point d) → Point d :=
  fun _ _ replies =>
    ∑ t : secantSpace 1 1,
      (if secantSign t then (1 : ℝ) else -1) •
        term h (replies (Fintype.equivFin (secantSpace 1 1) t))

noncomputable def dacDescent {d : ℕ} (η h : ℝ) (x0 : Point d) :
    Algorithm (Point d × Bool) (ℝ × Point d) (Point d) :=
  batchedSched (fun _ => Fintype.card (secantSpace 1 1))
    (fun _ => secant_card_pos (show 0 < 1 from Nat.zero_lt_one) Nat.one_pos)
    (dacBase η x0) dacQS (dacDec h) (0, 0)

end OracleTemplate.SecantPolyak.AnchoredConvexPair

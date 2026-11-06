import LongTails.Algorithms.InexactAccelerated
import LongTails.Algorithms.SecantDescent
import LongTails.Algorithms.BatchedScheduled

namespace OracleTemplate.SecantPolyak.Centered

open SecantDescent InexactGradient LongTails.Setups.ZerothOrderSmoothAndConvex

/-- Momentum descent driven by surrogate gradients. The state stores the current iterate together
with the momentum anchor, and every round queries the surrogate gradient at the probe point. -/
noncomputable def cmBase {d : ℕ} (L μ θ : ℝ) (x0 : Point d) :
    Algorithm (Point d) (Point d) (Point d) where
  State := ℕ × Point d × Point d
  initial _ := (0, x0, x0)
  query s := (0, query θ ⟨s.2.1, s.2.2⟩)
  update s v := (s.1 + 1, (step L μ θ ⟨s.2.1, s.2.2⟩ v).1, (step L μ θ ⟨s.2.1, s.2.2⟩ v).2)
  output s := s.2.1

/-- Slot query of an accelerated round: every replica probes from the momentum point. -/
noncomputable def cmQS {d : ℕ} {m : ℕ → ℕ} (θ h : ℝ) :
    ∀ k : ℕ, (ℕ × Point d × Point d) → Fin (Fintype.card (secantSpace d (m k))) → Point d :=
  fun _ s t => secantQuery h (0, query θ ⟨s.2.1, s.2.2⟩) (secantSlot t)

/-- Decode the replies of one accelerated round into the surrogate gradient at the momentum point. -/
noncomputable def cmDec {d : ℕ} {m : ℕ → ℕ} (θ h : ℝ) :
    ∀ k : ℕ, (ℕ × Point d × Point d) → (Fin (Fintype.card (secantSpace d (m k))) → ℝ) → Point d :=
  fun k s replies => secantDecode h (0, query θ ⟨s.2.1, s.2.2⟩)
    (fun t : secantSpace d (m k) => replies (Fintype.equivFin (secantSpace d (m k)) t))

/-- Mean-anchored momentum secant descent: round `k` queries `m k` two-sided
every-coordinate differences at the momentum probe point and drives both the iterate and the
anchor by the paired mean, whose mean-zero deviation is what the centered analysis in
`LongTails/Proofs/CenteredMomentumStream.lean` exploits. -/
noncomputable def cmDescent {d : ℕ} (hd : 0 < d) {m : ℕ → ℕ} (hm : ∀ k, 0 < m k)
    (L μ θ h : ℝ) (x0 : Point d) : Algorithm (Point d) ℝ (Point d) :=
  batchedSched (fun k => Fintype.card (secantSpace d (m k)))
    (fun k => secant_card_pos hd (hm k)) (cmBase L μ θ x0) (cmQS θ h) (cmDec θ h) 0

end OracleTemplate.SecantPolyak.Centered

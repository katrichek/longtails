import LongTails.Template

namespace OracleTemplate

/-- Batching whose batch width depends on the completed round index. The state carries the round
number, the position inside the round, the state of the wrapped algorithm, and the replies of the
current round stored on all of `ℕ`, of which the first `n k` carry the round. -/
noncomputable def batchedSched {Q V W U : Type} (n : ℕ → ℕ) (hn : ∀ k, 0 < n k)
    (A : Algorithm Q V U) (queries : ∀ k, A.State → Fin (n k) → Q)
    (decode : ∀ k, A.State → (Fin (n k) → W) → V) (zero : W) : Algorithm Q W U where
  Seed := A.Seed
  law := A.law
  State := ℕ × ℕ × A.State × (ℕ → W)
  initial seed := (0, 0, A.initial seed, fun _ => zero)
  query state :=
    (0, queries state.1 state.2.2.1 ⟨state.2.1 % n state.1, Nat.mod_lt _ (hn state.1)⟩)
  update state reply :=
    let i := state.2.1 % n state.1
    let replies := Function.update state.2.2.2 i reply
    if i + 1 < n state.1 then (state.1, i + 1, state.2.2.1, replies)
    else
      (state.1 + 1, 0, A.update state.2.2.1
        (decode state.1 state.2.2.1 (fun t => replies t.val)), fun _ => zero)
  output state := A.output state.2.2.1

end OracleTemplate

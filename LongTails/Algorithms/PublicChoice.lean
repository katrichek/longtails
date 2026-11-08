import LongTails.Template

/-!
A zero-additional-query meta-algorithm: select an existing oracle algorithm
*before any calls*, using only public input. The two subalgorithms may have
completely different state and seed types; the selected `Algorithm` has the
corresponding type after the `if` is reduced.
-/

namespace OracleTemplate.Portfolio

/-- Make a public-parameter-dependent choice between two oracle algorithms.
The choice does not itself query the oracle. -/
noncomputable def chooseAlgorithm
    (S : OracleTemplate.Setup)
    (preferLeft : S.Public → Prop)
    (left right : (p : S.Public) →
      OracleTemplate.Algorithm (S.Query p) (S.Reply p) (S.Output p) S.numOracles) :
    (p : S.Public) →
      OracleTemplate.Algorithm (S.Query p) (S.Reply p) (S.Output p) S.numOracles := by
  classical
  intro p
  exact if preferLeft p then left p else right p

end OracleTemplate.Portfolio

import LongTails.Setups.ZerothOrderLineConvex
import LongTails.Setups.ZerothOrderSmoothAndConvex

/-!
A one-dimensional Setup is a subtype of the original smooth-convex Setup.
This transfer uses the *same* function-value oracle and exactly the same
call budget. It does not smuggle a gradient into the algorithm.
-/

namespace OracleTemplate.Portfolio

/-- Restrict any generic noisy value-oracle optimizer to the one-dimensional
Setup, retaining its exact budget. -/
theorem lift_to_line
    (budget : LongTails.Setups.ZerothOrderSmoothAndConvex.spec.Params → Fin 1 → ℕ)
    (h : OracleTemplate.Convergence
      LongTails.Setups.ZerothOrderSmoothAndConvex.spec budget) :
    OracleTemplate.Convergence
      LongTails.Setups.ZerothOrderLineConvex.spec
      (fun q => budget q.val) := by
  rcases h with ⟨A, hA, hAllowed⟩
  refine ⟨(fun q => A q.val), ?_, ?_⟩
  · intro q hq f O hO
    exact hA q.val hq f O hO
  · intro q hq
    exact hAllowed q.val hq

end OracleTemplate.Portfolio

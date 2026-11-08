import LongTails.Setups.ZerothOrderPolyakConvex
import LongTails.Theorems.ZerothOrderPolyakConvex
import LongTails.Theorems.ScheduledSecantPolyakConvex
import LongTails.Proofs.MinBudget

/-!
No-strong-convexity assumption is introduced here. Both underlying
algorithms have the SAME PL Setup and noisy scalar function-value oracle.
The selected algorithm has the minimum of their certified call budgets.
-/

namespace LongTails.Theorems.PortfolioPolyakConvex

open OracleTemplate

private abbrev S := LongTails.Setups.ZerothOrderPolyakConvex.spec
private abbrev Params := LongTails.Setups.ZerothOrderPolyakConvex.Params

private noncomputable abbrev bA :=
  LongTails.Theorems.ZerothOrderPolyakConvex.budget
private noncomputable abbrev bB :=
  LongTails.Theorems.ScheduledSecantPolyakConvex.budget

noncomputable def budget : (let S := LongTails.Setups.ZerothOrderPolyakConvex.spec; S.Params → Fin S.numOracles → ℕ) :=
  OracleTemplate.Portfolio.chooseBudget S
    (fun q => bA q 0 ≤ bB q 0) bA bB

lemma budget_eq_min (q : Params) :
    budget q 0 = min (bA q 0) (bB q 0) := by
  classical
  by_cases h : bA q 0 ≤ bB q 0
  · rw [show budget q 0 = bA q 0 from ite_eq_left h, min_eq_left h]
  · rw [show budget q 0 = bB q 0 from ite_eq_right h]
    rw [min_eq_right (Nat.le_of_lt (Nat.lt_of_not_le h))]

/-- Exact convergence of the better of standard and scheduled secant descent. -/
theorem result :
    OracleTemplate.Convergence LongTails.Setups.ZerothOrderPolyakConvex.spec budget := by
  exact OracleTemplate.Portfolio.choose_convergence S
    (fun q => bA q 0 ≤ bB q 0)
    bA bB
    LongTails.Theorems.ZerothOrderPolyakConvex.result
    LongTails.Theorems.ScheduledSecantPolyakConvex.result

end LongTails.Theorems.PortfolioPolyakConvex

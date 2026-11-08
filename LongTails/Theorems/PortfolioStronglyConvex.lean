import LongTails.Setups.ZerothOrderStronglyConvex
import LongTails.Theorems.ZerothOrderStronglyConvex
import LongTails.Theorems.ScheduledSecantStronglyConvex
import LongTails.Theorems.ScheduledAcceleratedSecantStronglyConvex
import LongTails.Theorems.CenteredMomentumSecantStronglyConvex
import LongTails.Proofs.MinBudget

/-!
Best certified budget among four *additive-noise* zeroth-order methods under
exactly `ZerothOrderStronglyConvex.spec`. The program decides which algorithm
to run from known public parameters, before it has observed any oracle reply.
No gradient oracle, special common random numbers or strong-growth model.
-/

namespace LongTails.Theorems.PortfolioStronglyConvex

open OracleTemplate

private abbrev S := LongTails.Setups.ZerothOrderStronglyConvex.spec
private abbrev Params := LongTails.Setups.ZerothOrderStronglyConvex.Params

private noncomputable abbrev bA :=
  LongTails.Theorems.ZerothOrderStronglyConvex.budget
private noncomputable abbrev bB :=
  LongTails.Theorems.ScheduledSecantStronglyConvex.budget
private noncomputable abbrev bC :=
  LongTails.Theorems.ScheduledAcceleratedSecantStronglyConvex.budget
private noncomputable abbrev bD :=
  LongTails.Theorems.CenteredMomentumSecantStronglyConvex.budget

noncomputable def budgetAB : Params → Fin 1 → ℕ :=
  OracleTemplate.Portfolio.chooseBudget S
    (fun q => bA q 0 ≤ bB q 0) bA bB

noncomputable def budgetCD : Params → Fin 1 → ℕ :=
  OracleTemplate.Portfolio.chooseBudget S
    (fun q => bC q 0 ≤ bD q 0) bC bD

/-- The smaller total zeroth-order budget among all four methods. -/
noncomputable def budget : (let S := LongTails.Setups.ZerothOrderStronglyConvex.spec; S.Params → Fin S.numOracles → ℕ) :=
  OracleTemplate.Portfolio.chooseBudget S
    (fun q => budgetAB q 0 ≤ budgetCD q 0) budgetAB budgetCD

lemma budgetAB_eq_min (q : Params) :
    budgetAB q 0 = min (bA q 0) (bB q 0) := by
  classical
  by_cases h : bA q 0 ≤ bB q 0
  · rw [show budgetAB q 0 = bA q 0 from ite_eq_left h, min_eq_left h]
  · rw [show budgetAB q 0 = bB q 0 from ite_eq_right h]
    rw [min_eq_right (Nat.le_of_lt (Nat.lt_of_not_le h))]

lemma budgetCD_eq_min (q : Params) :
    budgetCD q 0 = min (bC q 0) (bD q 0) := by
  classical
  by_cases h : bC q 0 ≤ bD q 0
  · rw [show budgetCD q 0 = bC q 0 from ite_eq_left h, min_eq_left h]
  · rw [show budgetCD q 0 = bD q 0 from ite_eq_right h]
    rw [min_eq_right (Nat.le_of_lt (Nat.lt_of_not_le h))]

lemma budget_eq_min (q : Params) :
    budget q 0 =
      min (min (bA q 0) (bB q 0))
          (min (bC q 0) (bD q 0)) := by
  calc
    budget q 0 = min (budgetAB q 0) (budgetCD q 0) := by
      classical
      by_cases h : budgetAB q 0 ≤ budgetCD q 0
      · rw [show budget q 0 = budgetAB q 0 from ite_eq_left h, min_eq_left h]
      · rw [show budget q 0 = budgetCD q 0 from ite_eq_right h]
        rw [min_eq_right (Nat.le_of_lt (Nat.lt_of_not_le h))]
    _ = min (min (bA q 0) (bB q 0))
            (min (bC q 0) (bD q 0)) := by
      rw [budgetAB_eq_min q, budgetCD_eq_min q]

/-- Completeness is inherited from the four kernel-checkable source theorems. -/
theorem result :
    OracleTemplate.Convergence LongTails.Setups.ZerothOrderStronglyConvex.spec budget := by
  have hAB : OracleTemplate.Convergence S budgetAB :=
    OracleTemplate.Portfolio.choose_convergence S
      (fun q => bA q 0 ≤ bB q 0)
      bA bB
      LongTails.Theorems.ZerothOrderStronglyConvex.result
      LongTails.Theorems.ScheduledSecantStronglyConvex.result
  have hCD : OracleTemplate.Convergence S budgetCD :=
    OracleTemplate.Portfolio.choose_convergence S
      (fun q => bC q 0 ≤ bD q 0)
      bC bD
      LongTails.Theorems.ScheduledAcceleratedSecantStronglyConvex.result
      LongTails.Theorems.CenteredMomentumSecantStronglyConvex.result
  exact OracleTemplate.Portfolio.choose_convergence S
    (fun q => budgetAB q 0 ≤ budgetCD q 0)
    budgetAB budgetCD hAB hCD

end LongTails.Theorems.PortfolioStronglyConvex

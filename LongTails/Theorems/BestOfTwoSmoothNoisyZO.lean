import LongTails.Algorithms.BestOfTwoSmoothNoisyZO
import LongTails.Proofs.ConvergenceChoice

namespace LongTails.Theorems.BestOfTwoSmoothNoisyZO

open OracleTemplate
open LongTails.Setups.ZerothOrderSmoothAndConvex

noncomputable def budget :
    (let S := spec; S.Params → Fin S.numOracles → ℕ) :=
  OracleTemplate.ConvergenceChoice.selectedBudget spec
    LongTails.Algorithms.BestOfTwoSmoothNoisyZO.chooseTwo
    OracleTemplate.ZerothOrder.AcceleratedTwoPointZerothOrderConvex.budget
    OracleTemplate.ZerothOrder.AcceleratedZerothOrderConvex.budget

/-- This theorem reduces to two ALREADY PROVED LongTails results.
    There is no new stochastic-convergence proof in this wrapper. -/
theorem result : Convergence spec budget := by
  exact OracleTemplate.ConvergenceChoice.select_convergence
    spec LongTails.Algorithms.BestOfTwoSmoothNoisyZO.chooseTwo
    OracleTemplate.ZerothOrder.AcceleratedTwoPointZerothOrderConvex.budget
    OracleTemplate.ZerothOrder.AcceleratedZerothOrderConvex.budget
    OracleTemplate.ZerothOrder.AcceleratedTwoPointZerothOrderConvex.result
    OracleTemplate.ZerothOrder.AcceleratedZerothOrderConvex.result

end LongTails.Theorems.BestOfTwoSmoothNoisyZO

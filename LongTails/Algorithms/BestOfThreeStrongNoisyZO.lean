import LongTails.Theorems.ZerothOrderStronglyConvex
import LongTails.Theorems.ScheduledSecantStronglyConvex
import LongTails.Theorems.CenteredMomentumSecantStronglyConvex

/-!
Select among three ALREADY FORMALIZED scalar noisy value-oracle methods:
fixed-batch secant descent, graded-batch secant descent, and centered-momentum
secant descent. No stronger assumptions than ZerothOrderStronglyConvex.spec.
-/
namespace LongTails.Algorithms.BestOfThreeStrongNoisyZO

open OracleTemplate
open LongTails.Setups.ZerothOrderStronglyConvex

noncomputable def fixedCost (q : Params) : ℕ :=
  LongTails.Theorems.ZerothOrderStronglyConvex.budget q 0
noncomputable def scheduledCost (q : Params) : ℕ :=
  LongTails.Theorems.ScheduledSecantStronglyConvex.budget q 0
noncomputable def momentumCost (q : Params) : ℕ :=
  LongTails.Theorems.CenteredMomentumSecantStronglyConvex.budget q 0

/-- Choose fixed instead of scheduled when the former uses fewer values. -/
noncomputable def pickFixed (q : Params) : Bool :=
  decide (fixedCost q ≤ scheduledCost q)

/-- Compare the winning first-stage budget with centered-momentum. -/
noncomputable def pickFirstStage (q : Params) : Bool :=
  decide (min (fixedCost q) (scheduledCost q) ≤ momentumCost q)

noncomputable def firstStage (q : Params) : Algorithm q.E ℝ q.E :=
  if pickFixed q then
    LongTails.Theorems.ZerothOrderStronglyConvex.result.choose q
  else
    LongTails.Theorems.ScheduledSecantStronglyConvex.result.choose q

noncomputable def algorithm (q : Params) : Algorithm q.E ℝ q.E :=
  if pickFirstStage q then firstStage q
  else LongTails.Theorems.CenteredMomentumSecantStronglyConvex.result.choose q

end LongTails.Algorithms.BestOfThreeStrongNoisyZO

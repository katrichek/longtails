import LongTails.Algorithms.BestOfThreeStrongNoisyZO
import LongTails.Proofs.ConvergenceChoice

namespace LongTails.Theorems.BestOfThreeStrongNoisyZO

open OracleTemplate
open LongTails.Setups.ZerothOrderStronglyConvex
open LongTails.Algorithms.BestOfThreeStrongNoisyZO

private noncomputable def fixedBudget : Params → Fin 1 → ℕ :=
  LongTails.Theorems.ZerothOrderStronglyConvex.budget
private noncomputable def scheduledBudget : Params → Fin 1 → ℕ :=
  LongTails.Theorems.ScheduledSecantStronglyConvex.budget
private noncomputable def momentumBudget : Params → Fin 1 → ℕ :=
  LongTails.Theorems.CenteredMomentumSecantStronglyConvex.budget

private noncomputable def firstBudget : Params → Fin 1 → ℕ :=
  ConvergenceChoice.selectedBudget spec pickFixed fixedBudget scheduledBudget

noncomputable def budget :
    (let S := LongTails.Setups.ZerothOrderStronglyConvex.spec; S.Params → Fin S.numOracles → ℕ) :=
  ConvergenceChoice.selectedBudget spec pickFirstStage firstBudget momentumBudget

/-- A proof-backed, public-data portfolio of THREE existing algorithms.
    The best previous epsilon exponent (2, for positive sigma) is not improved. -/
theorem result : Convergence spec budget := by
  have hFirst : Convergence spec firstBudget :=
    ConvergenceChoice.select_convergence spec pickFixed fixedBudget scheduledBudget
      LongTails.Theorems.ZerothOrderStronglyConvex.result
      LongTails.Theorems.ScheduledSecantStronglyConvex.result
  exact ConvergenceChoice.select_convergence spec pickFirstStage firstBudget momentumBudget
    hFirst LongTails.Theorems.CenteredMomentumSecantStronglyConvex.result

end LongTails.Theorems.BestOfThreeStrongNoisyZO

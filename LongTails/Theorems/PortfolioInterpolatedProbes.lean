import LongTails.Theorems.InterpolatedProbeDescentStrongGrowth
import LongTails.Theorems.DampedAnchoredAccelerationStrongGrowth
import LongTails.Proofs.StrongGrowthLift
import LongTails.Proofs.MinBudget

/-!
An OPTIONAL frontier for the specially constrained, direction-sampled
interpolation oracle. It is NOT a theorem about the ordinary
`ZerothOrderSmoothAndConvex` model with additive value noise.
-/

namespace LongTails.Theorems.PortfolioInterpolatedProbes

open OracleTemplate

private abbrev S := LongTails.Setups.ZerothOrderSmoothingInterpolatedAcceleration.spec
private abbrev Params := LongTails.Setups.ZerothOrderSmoothingStrongGrowth.Params

private noncomputable abbrev bA :=
  LongTails.Theorems.InterpolatedProbeDescentStrongGrowth.budget
private noncomputable abbrev bB :=
  LongTails.Theorems.DampedAnchoredAccelerationStrongGrowth.budget

noncomputable def budget : (let S := LongTails.Setups.ZerothOrderSmoothingInterpolatedAcceleration.spec; S.Params → Fin S.numOracles → ℕ) :=
  OracleTemplate.Portfolio.chooseBudget S
    (fun q => bA q 0 ≤ bB q 0) bA bB

lemma budget_eq_min (q : Params) :
    budget q 0 = min (bA q 0) (bB q 0) := by
  classical
  by_cases h : bA q 0 ≤ bB q 0
  · rw [show budget q 0 = bA q 0 from ite_eq_left h, min_eq_left h]
  · rw [show budget q 0 = bB q 0 from ite_eq_right h]
    rw [min_eq_right (Nat.le_of_lt (Nat.lt_of_not_le h))]

theorem result :
    OracleTemplate.Convergence
      LongTails.Setups.ZerothOrderSmoothingInterpolatedAcceleration.spec budget := by
  have hBase : OracleTemplate.Convergence S bA :=
    OracleTemplate.Portfolio.lift_to_interpolated bA
      LongTails.Theorems.InterpolatedProbeDescentStrongGrowth.result
  exact OracleTemplate.Portfolio.choose_convergence S
    (fun q => bA q 0 ≤ bB q 0)
    bA bB hBase
    LongTails.Theorems.DampedAnchoredAccelerationStrongGrowth.result

end LongTails.Theorems.PortfolioInterpolatedProbes

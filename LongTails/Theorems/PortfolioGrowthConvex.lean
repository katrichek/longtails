import LongTails.Setups.ZerothOrderSmoothingGrowthConvex
import LongTails.Theorems.AveragedProbeDescentGrowthConvex
import LongTails.Theorems.DampedAnchoredConvexGrowth
import LongTails.Proofs.MinBudget

/-!
Both underlying algorithms are proved for the SAME Setup: multidimensional convex
zeroth-order optimization with randomized-smoothing mirrored probes whose variance grows with
the current smoothed gap. The selector reads public parameters only, never an oracle sample, and
picks the algorithm with the smaller certified budget:

* damped anchored pair acceleration, budget `2 * max 1 ⌈sqrt (16 L R² / eps) + 16 rho² R² / eps⌉₊`,
  which is cheaper exactly when `rho² < L`;
* averaged mirrored-pair descent, budget `2 * max 1 ⌈8 (L + rho²) R² / eps⌉₊`,
  which is cheaper when the noise constant dominates.

The selected algorithm and the selected budget are tied together, so the envelope is attained by
a concrete method and no budget is ever claimed without the method that achieves it.
-/

namespace LongTails.Theorems.PortfolioGrowthConvex

open OracleTemplate

private abbrev S := LongTails.Setups.ZerothOrderSmoothingGrowthConvex.spec
private abbrev Params := LongTails.Setups.ZerothOrderSmoothingGrowthConvex.Params

private noncomputable abbrev bDamped :=
  LongTails.Theorems.DampedAnchoredConvexGrowth.budget
private noncomputable abbrev bAveraged :=
  LongTails.Theorems.AveragedProbeDescentGrowthConvex.budget

noncomputable def budget :
    (let S := LongTails.Setups.ZerothOrderSmoothingGrowthConvex.spec;
      S.Params → Fin S.numOracles → ℕ) :=
  OracleTemplate.Portfolio.chooseBudget
    LongTails.Setups.ZerothOrderSmoothingGrowthConvex.spec
    (fun q => bDamped q 0 ≤ bAveraged q 0) bDamped bAveraged

/-- The envelope is exactly the minimum of the two certified budgets. -/
lemma budget_eq_min (q : Params) :
    budget q 0 = min (bAveraged q 0) (bDamped q 0) := by
  classical
  by_cases h : bDamped q 0 ≤ bAveraged q 0
  · rw [show budget q 0 = bDamped q 0 from ite_eq_left h, min_comm, min_eq_left h]
  · rw [show budget q 0 = bAveraged q 0 from ite_eq_right h]
    rw [min_eq_left (Nat.le_of_lt (Nat.lt_of_not_le h))]

/-- Machine-checked scale of the envelope: it never exceeds either branch, hence is at most the
smaller of `2 + 2 sqrt (16 L R² / eps) + 32 rho² R² / eps` and `2 + 16 (L + rho²) R² / eps`. -/
lemma budget_le (q : Params) (hL : 0 < q.L) (hε : 0 < q.ε) :
    (budget q 0 : ℝ)
      ≤ min (2 + 2 * Real.sqrt (16 * q.L * q.R ^ 2 / q.ε) + 32 * q.ρ ^ 2 * q.R ^ 2 / q.ε)
          (2 + 16 * (q.L + q.ρ ^ 2) * q.R ^ 2 / q.ε) := by
  classical
  have hDamped : (budget q 0 : ℝ)
      ≤ 2 + 2 * Real.sqrt (16 * q.L * q.R ^ 2 / q.ε) + 32 * q.ρ ^ 2 * q.R ^ 2 / q.ε := by
    have h1 : (budget q 0 : ℝ) ≤ (bDamped q 0 : ℝ) := by
      rw [budget_eq_min q]
      exact_mod_cast Nat.min_le_right _ _
    refine h1.trans (OracleTemplate.SecantPolyak.AnchoredConvexPair.dac_budget_le hL hε)
  have hAveraged : (budget q 0 : ℝ) ≤ 2 + 16 * (q.L + q.ρ ^ 2) * q.R ^ 2 / q.ε := by
    have h1 : (budget q 0 : ℝ) ≤ (bAveraged q 0 : ℝ) := by
      rw [budget_eq_min q]
      exact_mod_cast Nat.min_le_left _ _
    refine h1.trans
      (LongTails.Theorems.AveragedProbeDescentGrowthConvex.budget_le q 0 hL hε)
  exact le_min hDamped hAveraged

/-- Exact convergence of the cheaper of damped anchored pair acceleration and averaged
mirrored-pair descent, under the same gap-proportional variance model. -/
theorem result :
    OracleTemplate.Convergence LongTails.Setups.ZerothOrderSmoothingGrowthConvex.spec budget := by
  exact OracleTemplate.Portfolio.choose_convergence
    LongTails.Setups.ZerothOrderSmoothingGrowthConvex.spec
    (fun q => bDamped q 0 ≤ bAveraged q 0) bDamped bAveraged
    LongTails.Theorems.DampedAnchoredConvexGrowth.result
    LongTails.Theorems.AveragedProbeDescentGrowthConvex.result

end LongTails.Theorems.PortfolioGrowthConvex

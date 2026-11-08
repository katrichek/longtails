import LongTails.Theorems.LineSearchZerothOrderConvex
import LongTails.Theorems.PortfolioSmoothConvex
import LongTails.Proofs.LineLiftConvergence
import LongTails.Proofs.MinBudget

/-!
One-dimensional convex value-oracle optimization: take whichever has
better *certified* query count: noisy ternary line search or the general
smooth-convex zeroth-order portfolio restricted to dimension one.
-/

namespace LongTails.Theorems.PortfolioLineConvex

open OracleTemplate

private abbrev S := LongTails.Setups.ZerothOrderLineConvex.spec
private abbrev Params := LongTails.Setups.ZerothOrderLineConvex.Params

private noncomputable abbrev bLine :=
  LongTails.Theorems.LineSearchZerothOrderConvex.budget

private noncomputable def bSmooth (q : Params) : Fin 1 → ℕ :=
  LongTails.Theorems.PortfolioSmoothConvex.budget q.val

noncomputable def budget : (let S := LongTails.Setups.ZerothOrderLineConvex.spec; S.Params → Fin S.numOracles → ℕ) :=
  OracleTemplate.Portfolio.chooseBudget S
    (fun q => bLine q 0 ≤ bSmooth q 0) bLine bSmooth

lemma budget_eq_min (q : Params) :
    budget q 0 = min (bLine q 0) (bSmooth q 0) := by
  classical
  by_cases h : bLine q 0 ≤ bSmooth q 0
  · rw [show budget q 0 = bLine q 0 from ite_eq_left h, min_eq_left h]
  · rw [show budget q 0 = bSmooth q 0 from ite_eq_right h]
    rw [min_eq_right (Nat.le_of_lt (Nat.lt_of_not_le h))]

/-- A new one-dimensional portfolio without any extra assumptions beyond
those encoded in the existing `ZerothOrderLineConvex.spec`. -/
theorem result :
    OracleTemplate.Convergence LongTails.Setups.ZerothOrderLineConvex.spec budget := by
  have hSmooth : OracleTemplate.Convergence S bSmooth :=
    OracleTemplate.Portfolio.lift_to_line
      LongTails.Theorems.PortfolioSmoothConvex.budget
      LongTails.Theorems.PortfolioSmoothConvex.result
  exact OracleTemplate.Portfolio.choose_convergence S
    (fun q => bLine q 0 ≤ bSmooth q 0)
    bLine bSmooth
    LongTails.Theorems.LineSearchZerothOrderConvex.result hSmooth

end LongTails.Theorems.PortfolioLineConvex

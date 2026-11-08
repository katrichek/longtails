import LongTails.Setups.ZerothOrderStronglyConvex

/-!
RESEARCH EXTENSION, NOT THE ORIGINAL SETUP.
Same independent scalar noisy value oracle, same strong convexity, plus the
ADDITIONAL O(h^2) central-difference bias bound (e.g. from Lipschitz Hessian).
Without this extra regularity, an epsilon^{-3/2} claim is unsupported.
-/
namespace LongTails.Setups.ZerothOrderStronglyConvexCubicBias

open OracleTemplate
open scoped RealInnerProductSpace

private abbrev Base := LongTails.Setups.ZerothOrderStronglyConvex.spec

structure Params where
  base : LongTails.Setups.ZerothOrderStronglyConvex.Params
  rho : ℝ

/-- The extra assumption is imposed on the UNKNOWN objective, NOT on the oracle
    noise.  rho controls symmetric finite-difference bias. -/
def centralCubicBias (q : Params) (f : q.base.E → ℝ) : Prop :=
  ∀ (x v : q.base.E) (h : ℝ), 0 < h → ‖v‖ = 1 →
    |(f (x + h • v) - f (x - h • v)) / (2 * h) -
        ⟪gradient f x, v⟫| ≤ q.rho * h ^ 2

abbrev spec : OracleTemplate.Setup where
  Params := Params
  Public := Params
  Instance q := Base.Instance q.base
  Query q := Base.Query q.base
  Reply q := Base.Reply q.base
  Output q := Base.Output q.base
  publicInput q := q
  valid q := Base.valid q.base ∧ 0 ≤ q.rho
  admissible q f oracle := Base.admissible q.base f oracle ∧ centralCubicBias q f
  successful q f output P := Base.successful q.base f output P

end LongTails.Setups.ZerothOrderStronglyConvexCubicBias

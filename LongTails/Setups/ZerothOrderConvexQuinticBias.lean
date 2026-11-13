import LongTails.Setups.ZerothOrderSmoothAndConvex

/-!
RESEARCH EXTENSION, NOT THE ORIGINAL SETUP.
Identical scalar-noise oracle, convexity and smoothness as the plain convex setup, plus `O(h^4)`
bias for the four-point central stencil. The valid parameter range requires a positive radius `R`;
the degenerate case `R = 0` has `x0` as a minimizer and needs no query. A bounded fifth derivative is sufficient, but it
DOES NOT follow from ordinary `L`-smoothness.
-/
namespace LongTails.Setups.ZerothOrderConvexQuinticBias

open OracleTemplate
open scoped RealInnerProductSpace

private abbrev Base := LongTails.Setups.ZerothOrderSmoothAndConvex.spec

structure Params where
  base : LongTails.Setups.ZerothOrderSmoothAndConvex.Params
  rho4 : ℝ

/-- Stronger function regularity for the 4-point finite-difference stencil. -/
def centralQuinticBias (q : Params) (f : q.base.E → ℝ) : Prop :=
  ∀ (x v : q.base.E) (h : ℝ), 0 < h → ‖v‖ = 1 →
    |(-f (x + (2 * h) • v) + 8 * f (x + h • v)
        - 8 * f (x - h • v) + f (x - (2 * h) • v)) / (12 * h)
        - ⟪gradient f x, v⟫| ≤ q.rho4 * h ^ 4

abbrev spec : OracleTemplate.Setup where
  Params := Params
  Public := Params
  Instance q := Base.Instance q.base
  Query q := Base.Query q.base
  Reply q := Base.Reply q.base
  Output q := Base.Output q.base
  publicInput q := q
  valid q := Base.valid q.base ∧ 0 < q.base.R ∧ 0 ≤ q.rho4
  admissible q f oracle := Base.admissible q.base f oracle ∧ centralQuinticBias q f
  successful q f output P := Base.successful q.base f output P

end LongTails.Setups.ZerothOrderConvexQuinticBias
import LongTails.Setups.ZerothOrderStronglyConvex

/-!
RESEARCH EXTENSION, NOT THE ORIGINAL SETUP.
Identical scalar-noise oracle and strong convexity, plus `O (h ^ 10)` bias for the ten-point central
stencil. A bounded eleventh derivative along every line is sufficient, but it DOES NOT follow from
ordinary `L`-smoothness, nor from the eight-point `O (h ^ 8)` regularity of
`LongTails.Setups.ZerothOrderStronglyConvexNonicBias`. The accuracy criterion and the oracle model
are inherited unchanged from `LongTails.Setups.ZerothOrderStronglyConvex`.
-/
namespace LongTails.Setups.ZerothOrderStronglyConvexUndecicBias

open OracleTemplate
open scoped RealInnerProductSpace

private abbrev Base := LongTails.Setups.ZerothOrderStronglyConvex.spec

structure Params where
  base : LongTails.Setups.ZerothOrderStronglyConvex.Params
  rho10 : ℝ

/-- Stronger function regularity for the 10-point finite-difference stencil. -/
def centralUndecicBias (q : Params) (f : q.base.E → ℝ) : Prop :=
  ∀ (x v : q.base.E) (h : ℝ), 0 < h → ‖v‖ = 1 →
    |(2100 * (f (x + h • v) - f (x - h • v))
        - 600 * (f (x + (2 * h) • v) - f (x - (2 * h) • v))
        + 150 * (f (x + (3 * h) • v) - f (x - (3 * h) • v))
        - 25 * (f (x + (4 * h) • v) - f (x - (4 * h) • v))
        + 2 * (f (x + (5 * h) • v) - f (x - (5 * h) • v))) / (2520 * h)
        - ⟪gradient f x, v⟫| ≤ q.rho10 * h ^ 10

abbrev spec : OracleTemplate.Setup where
  Params := Params
  Public := Params
  Instance q := Base.Instance q.base
  Query q := Base.Query q.base
  Reply q := Base.Reply q.base
  Output q := Base.Output q.base
  publicInput q := q
  valid q := Base.valid q.base ∧ 0 ≤ q.rho10
  admissible q f oracle := Base.admissible q.base f oracle ∧ centralUndecicBias q f
  successful q f output P := Base.successful q.base f output P

end LongTails.Setups.ZerothOrderStronglyConvexUndecicBias

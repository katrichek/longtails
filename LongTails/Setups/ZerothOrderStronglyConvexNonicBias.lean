import LongTails.Setups.ZerothOrderStronglyConvex

/-!
RESEARCH EXTENSION, NOT THE ORIGINAL SETUP.
Identical scalar-noise oracle and strong convexity, plus O(h^8) bias for the eight-point central
stencil. A bounded ninth derivative is sufficient, but it DOES NOT follow from ordinary
L-smoothness, nor from the six-point `O (h ^ 6)` regularity of
`LongTails.Setups.ZerothOrderStronglyConvexSepticBias`.
-/
namespace LongTails.Setups.ZerothOrderStronglyConvexNonicBias

open OracleTemplate
open scoped RealInnerProductSpace

private abbrev Base := LongTails.Setups.ZerothOrderStronglyConvex.spec

structure Params where
  base : LongTails.Setups.ZerothOrderStronglyConvex.Params
  rho8 : ℝ

/-- Stronger function regularity for the 8-point finite-difference stencil. -/
def centralNonicBias (q : Params) (f : q.base.E → ℝ) : Prop :=
  ∀ (x v : q.base.E) (h : ℝ), 0 < h → ‖v‖ = 1 →
    |(672 * (f (x + h • v) - f (x - h • v)) - 168 * (f (x + (2 * h) • v) - f (x - (2 * h) • v))
        + 32 * (f (x + (3 * h) • v) - f (x - (3 * h) • v))
        - 3 * (f (x + (4 * h) • v) - f (x - (4 * h) • v))) / (840 * h)
        - ⟪gradient f x, v⟫| ≤ q.rho8 * h ^ 8

abbrev spec : OracleTemplate.Setup where
  Params := Params
  Public := Params
  Instance q := Base.Instance q.base
  Query q := Base.Query q.base
  Reply q := Base.Reply q.base
  Output q := Base.Output q.base
  publicInput q := q
  valid q := Base.valid q.base ∧ 0 ≤ q.rho8
  admissible q f oracle := Base.admissible q.base f oracle ∧ centralNonicBias q f
  successful q f output P := Base.successful q.base f output P

end LongTails.Setups.ZerothOrderStronglyConvexNonicBias

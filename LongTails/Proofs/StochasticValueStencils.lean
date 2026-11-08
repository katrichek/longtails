import Mathlib.Tactic

/-!
Algebraic consistency lemmas for stencils. These ARE ACTUAL THEOREM PROOFS,
but they prove exactness only on POLYNOMIALS, not stochastic convergence.
-/
namespace LongTails.Proofs.StochasticValueStencils

/-- Symmetric two-point differences differentiate quadratics exactly. -/
theorem centered_quadratic_exact (a b c x h : ℝ) (hh : h ≠ 0) :
    ((a * (x + h) ^ 2 + b * (x + h) + c) -
      (a * (x - h) ^ 2 + b * (x - h) + c)) / (2 * h)
    = 2 * a * x + b := by
  field_simp [hh]
  ring

private def quartic (a b c d e : ℝ) (x : ℝ) : ℝ :=
  a * x ^ 4 + b * x ^ 3 + c * x ^ 2 + d * x + e

/-- The four-point central stencil differentiates every quartic polynomial exactly. -/
theorem fourth_order_quartic_exact (a b c d e x h : ℝ) (hh : h ≠ 0) :
    (-quartic a b c d e (x + 2 * h)
      + 8 * quartic a b c d e (x + h)
      - 8 * quartic a b c d e (x - h)
      + quartic a b c d e (x - 2 * h)) / (12 * h)
    = 4 * a * x ^ 3 + 3 * b * x ^ 2 + 2 * c * x + d := by
  unfold quartic
  field_simp [hh]
  ring

end LongTails.Proofs.StochasticValueStencils

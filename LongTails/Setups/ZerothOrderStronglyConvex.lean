import LongTails.Setups.ZerothOrderPolyakConvex

namespace LongTails.Setups.ZerothOrderStronglyConvex

open OracleTemplate Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
open LongTails.Setups.ZerothOrderSmoothAndConvex

/-- Parameters of the strongly convex value-oracle problem. `μ` is the strong convexity modulus. -/
abbrev Params : Type 1 := LongTails.Setups.ZerothOrderPolyakConvex.Params

/-- Strong convexity with modulus `μ` through the tangent quadratic support. -/
def tangentStrong (μ : ℝ) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) : Prop :=
  ∀ x y, f x + ⟪gradient f x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := p.E → ℝ
  Query p := p.E
  Reply _ := ℝ
  Output p := p.E
  publicInput p := p
  valid q := 0 < q.d ∧ 0 < q.L ∧ 0 ≤ q.R ∧ 0 ≤ q.σ ∧ 0 < q.μ ∧ 0 < q.ε
  admissible q f O :=
    LongTails.Setups.ZerothOrderPolyakConvex.baseShape q f O ∧
      ∃ xstar, IsMinOn f univ xstar ∧ ‖q.x0 - xstar‖ ≤ q.R ∧ tangentStrong q.μ f
  successful q f output P :=
    Measurable output ∧
      ∃ xstar, IsMinOn f univ xstar ∧
        Integrable (fun ω => f (output ω) - f xstar) (P : Measure _) ∧
        (∫ ω, f (output ω) - f xstar ∂(P : Measure _)) ≤ q.ε

/-- Strong convexity with modulus `μ` gives the Polyak-Łojasiewicz inequality with the same `μ`. -/
lemma polyak_of_strong {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} {μ : ℝ} (hμ : 0 < μ) (xstar : E)
    (_hmin : IsMinOn f Set.univ xstar)
    (hsc : tangentStrong μ f) (x : E) :
    2 * μ * (f x - f xstar) ≤ ‖gradient f x‖ ^ 2 := by
  have hv : xstar - x = -(x - xstar) := by abel
  have h1 := hsc x xstar
  have hin : ⟪gradient f x, x - xstar⟫ ≤ ‖gradient f x‖ * ‖x - xstar‖ :=
    real_inner_le_norm _ _
  have hgap : f x - f xstar ≤ ‖gradient f x‖ * ‖x - xstar‖ - μ / 2 * ‖x - xstar‖ ^ 2 := by
    have h2 := h1
    simp only [hv, inner_neg_right, norm_neg] at h2
    linarith
  have hmul := mul_le_mul_of_nonneg_left hgap (le_of_lt hμ)
  have hamp : μ * (‖gradient f x‖ * ‖x - xstar‖) - μ * (μ / 2) * ‖x - xstar‖ ^ 2
      ≤ ‖gradient f x‖ ^ 2 / 2 := by
    nlinarith [sq_nonneg (‖gradient f x‖ - μ * ‖x - xstar‖)]
  have hmid : μ * (f x - f xstar) ≤ ‖gradient f x‖ ^ 2 / 2 := by
    refine le_trans hmul ?_
    nlinarith
  linarith

end LongTails.Setups.ZerothOrderStronglyConvex

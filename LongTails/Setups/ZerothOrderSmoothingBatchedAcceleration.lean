import LongTails.Template
import LongTails.Setups.ZerothOrderSmoothingStrongGrowth
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace LongTails.Setups.ZerothOrderSmoothingBatchedAcceleration

open OracleTemplate
open LongTails.Setups.ZerothOrderSmoothAndConvex (Point)

/-- Momentum weight of the weighted anchored pair scheme with damped step `1 / L` and anchor weight
`μ / 4`: the contraction `√(μ / (2 L))` is the largest one the damped step admits, and its reciprocal
`√(2 L / μ)` is the per-round logarithmic cost. -/
noncomputable def mmt : LongTails.Setups.ZerothOrderSmoothingStrongGrowth.Params → ℝ :=
  fun q => Real.sqrt (q.μ / (2 * q.L))

/-- Anchor weight of the scheme: one quarter of the strong convexity modulus, so the anchor moves by
`(θ / (2 · μ / 4)) = 2 * θ / μ` times the round surrogate, the accelerated anchor step, while the
potential carries the weight `μ / 4`. -/
noncomputable def anch : LongTails.Setups.ZerothOrderSmoothingStrongGrowth.Params → ℝ :=
  fun q => q.μ / 4

/-- Batch width forced by the noise absorption cap: `m` mirrored pairs per round give a surrogate
whose mean-square deviation is `2 * ρ² / m` times the smoothed gap at the probed point, and the
weighted anchored potential absorbs it exactly when `4 * ρ² ≤ m * μ * θ`. One pair therefore
suffices throughout the interpolation regime `ρ² ≤ μ * θ / 4`. -/
noncomputable def width : LongTails.Setups.ZerothOrderSmoothingStrongGrowth.Params → ℕ :=
  fun q => max 1 ⌈4 * q.ρ ^ 2 / (q.μ * mmt q)⌉₊

/-- The derived batch width is positive, so every round asks at least one mirrored pair. -/
lemma width_pos (q : LongTails.Setups.ZerothOrderSmoothingStrongGrowth.Params) : 0 < width q :=
  Nat.lt_of_lt_of_le Nat.one_pos (Nat.le_max_left _ _)

abbrev spec : Setup where
  Params := LongTails.Setups.ZerothOrderSmoothingStrongGrowth.Params
  Public := LongTails.Setups.ZerothOrderSmoothingStrongGrowth.Params
  Instance p := Point p.d → ℝ
  Query p := Point p.d × Bool
  Reply p := ℝ × Point p.d
  Output p := Point p.d
  publicInput p := p
  valid q :=
    0 < q.d ∧ 0 < q.L ∧ 0 ≤ q.R ∧ 0 < q.μ ∧ q.μ ≤ q.L ∧ 0 < q.ε ∧ 0 < q.h ∧ 0 < q.ρ ∧
      2 * q.L * q.h ^ 2 * (q.d : ℝ) ≤ q.ε
  admissible q f O :=
    LongTails.Setups.ZerothOrderSmoothingStrongGrowth.spec.admissible q f O
  successful q f output P :=
    LongTails.Setups.ZerothOrderSmoothingStrongGrowth.spec.successful q f output P

end LongTails.Setups.ZerothOrderSmoothingBatchedAcceleration

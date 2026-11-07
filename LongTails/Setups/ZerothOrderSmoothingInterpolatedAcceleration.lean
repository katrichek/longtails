import LongTails.Template
import LongTails.Setups.ZerothOrderSmoothingStrongGrowth
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace LongTails.Setups.ZerothOrderSmoothingInterpolatedAcceleration

open OracleTemplate
open LongTails.Setups.ZerothOrderSmoothAndConvex (Point)

/-- Momentum weight selected by the accelerated analysis of the damped anchored pair scheme. -/
noncomputable def mmt : LongTails.Setups.ZerothOrderSmoothingStrongGrowth.Params → ℝ :=
  fun q => Real.sqrt (3 * q.μ / (8 * q.L))

/-- Interpolation strength of the probe model. The accelerated anchored scheme absorbs the probe
deviation into the negative smoothed-gap terms of its own potential only when the variance constant
is of this order, so this is a quantitative interpolation assumption on the oracle. -/
def interpolated : LongTails.Setups.ZerothOrderSmoothingStrongGrowth.Params → Prop :=
  fun q => q.ρ ^ 2 ≤ q.μ * mmt q / 2

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
      2 * q.L * q.h ^ 2 * (q.d : ℝ) ≤ q.ε ∧ interpolated q
  admissible q f O :=
    LongTails.Setups.ZerothOrderSmoothingStrongGrowth.spec.admissible q f O
  successful q f output P :=
    LongTails.Setups.ZerothOrderSmoothingStrongGrowth.spec.successful q f output P

end LongTails.Setups.ZerothOrderSmoothingInterpolatedAcceleration

import LongTails.Theorems.AcceleratedTwoPointZerothOrderConvex
import LongTails.Theorems.AcceleratedZerothOrderConvex

/-!
Public-parameter selection between two EXISTING accelerated zeroth-order
algorithms, not a newly discovered gradient estimator.
-/
namespace LongTails.Algorithms.BestOfTwoSmoothNoisyZO

open OracleTemplate
open LongTails.Setups.ZerothOrderSmoothAndConvex

private noncomputable def twoCalls (q : Params) : ℕ :=
  OracleTemplate.ZerothOrder.AcceleratedTwoPointZerothOrderConvex.budget q 0

private noncomputable def coordinateCalls (q : Params) : ℕ :=
  OracleTemplate.ZerothOrder.AcceleratedZerothOrderConvex.budget q 0

/-- True iff the random-direction accelerated method has no larger oracle budget. -/
noncomputable def chooseTwo (q : Params) : Bool :=
  decide (twoCalls q ≤ coordinateCalls q)

/-- The meta-algorithm only sees Public=Params and makes its decision BEFORE the
    first oracle call. Neither branch has access to exact derivatives. -/
noncomputable def algorithm (q : Params) : Algorithm q.E ℝ q.E :=
  if chooseTwo q then
    OracleTemplate.ZerothOrder.AcceleratedTwoPointZerothOrderConvex.result.choose q
  else
    OracleTemplate.ZerothOrder.AcceleratedZerothOrderConvex.result.choose q

end LongTails.Algorithms.BestOfTwoSmoothNoisyZO

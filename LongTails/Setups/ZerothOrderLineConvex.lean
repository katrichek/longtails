import LongTails.Setups.ZerothOrderSmoothAndConvex

namespace LongTails.Setups.ZerothOrderLineConvex

open OracleTemplate

abbrev Params := {q : LongTails.Setups.ZerothOrderSmoothAndConvex.Params // q.d = 1}

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := LongTails.Setups.ZerothOrderSmoothAndConvex.spec.Instance p.val
  Query p := LongTails.Setups.ZerothOrderSmoothAndConvex.spec.Query p.val
  Reply p := LongTails.Setups.ZerothOrderSmoothAndConvex.spec.Reply p.val
  Output p := LongTails.Setups.ZerothOrderSmoothAndConvex.spec.Output p.val
  publicInput p := p
  valid q := LongTails.Setups.ZerothOrderSmoothAndConvex.spec.valid q.val
  admissible q I O := LongTails.Setups.ZerothOrderSmoothAndConvex.spec.admissible q.val I O
  successful q I output P :=
    LongTails.Setups.ZerothOrderSmoothAndConvex.spec.successful q.val I output P

end LongTails.Setups.ZerothOrderLineConvex

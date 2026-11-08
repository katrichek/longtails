import LongTails.Setups.ZerothOrderSmoothAndConvex
import LongTails.Setups.ZerothOrderPolyakConvex
import LongTails.Setups.ZerothOrderStronglyConvex
import LongTails.Setups.ZerothOrderLineConvex

/-!
Registry of source setups used by the portfolios. These are *aliases*,
not modifications or strengthenings of the user's oracle assumptions.
-/

namespace LongTails.Setups.OriginalNoiseProfiles

abbrev smooth := LongTails.Setups.ZerothOrderSmoothAndConvex.spec
abbrev polyak := LongTails.Setups.ZerothOrderPolyakConvex.spec
abbrev stronglyConvex := LongTails.Setups.ZerothOrderStronglyConvex.spec
abbrev line := LongTails.Setups.ZerothOrderLineConvex.spec

end LongTails.Setups.OriginalNoiseProfiles

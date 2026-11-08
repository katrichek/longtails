import LongTails.Theorems.PortfolioSmoothConvex
import LongTails.Theorems.PortfolioStronglyConvex
import LongTails.Theorems.PortfolioPolyakConvex
import LongTails.Theorems.PortfolioLineConvex
import LongTails.Theorems.PortfolioInterpolatedProbes

/-!
Compilation smoke tests. `#check` is NOT a substitute for Comparator;
run Comparator on the five individual Theorems files separately.
-/

#check LongTails.Theorems.PortfolioSmoothConvex.result
#check LongTails.Theorems.PortfolioStronglyConvex.result
#check LongTails.Theorems.PortfolioPolyakConvex.result
#check LongTails.Theorems.PortfolioLineConvex.result
#check LongTails.Theorems.PortfolioInterpolatedProbes.result

#check LongTails.Theorems.PortfolioSmoothConvex.budget_eq_min
#check LongTails.Theorems.PortfolioStronglyConvex.budget_eq_min
#check LongTails.Theorems.PortfolioPolyakConvex.budget_eq_min
#check LongTails.Theorems.PortfolioLineConvex.budget_eq_min

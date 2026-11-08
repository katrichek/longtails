import LongTails.Setups.ZerothOrderSmoothingStrongGrowth
import LongTails.Setups.ZerothOrderSmoothingInterpolatedAcceleration

/-!
The interpolation Setup is a restriction of the strong-growth Setup:
its validity predicate implies the latter's validity predicate, and its
admissibility/successfulness definitions are exactly those of strong growth.
This is *not* a reduction to ordinary additive-noise function values.
-/

namespace OracleTemplate.Portfolio

theorem lift_to_interpolated
    (budget : LongTails.Setups.ZerothOrderSmoothingStrongGrowth.spec.Params → Fin 1 → ℕ)
    (h : OracleTemplate.Convergence
      LongTails.Setups.ZerothOrderSmoothingStrongGrowth.spec budget) :
    OracleTemplate.Convergence
      LongTails.Setups.ZerothOrderSmoothingInterpolatedAcceleration.spec budget := by
  rcases h with ⟨A, hA, hAllowed⟩
  refine ⟨A, ?_, ?_⟩
  · intro q hq f O hO
    rcases hq with ⟨hd, hL, hR, hmu, _hmuL, heps, hh, hrho, hband, _hinterpolated⟩
    exact hA q ⟨hd, hL, hR, hmu, heps, hh, hrho, hband⟩ f O hO
  · intro q hq
    trivial

end OracleTemplate.Portfolio

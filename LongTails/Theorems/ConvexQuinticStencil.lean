import LongTails.Setups.ZerothOrderConvexQuinticBias
import LongTails.Proofs.ConvexRegularizedLift
import LongTails.Theorems.QuinticStencilStronglyConvex

/-!
Convex stochastic zeroth-order minimization from noisy values with the four-point (Richardson)
stencil. The oracle returns `f x + noise` with `∫ g = f` and variance `σ ^ 2`, the objective is
merely convex and `L`-smooth, and it carries the four-point regularity `centralQuinticBias`.

The algorithm regularizes the objective to `f + lam / 2 * ‖· - x0‖ ^ 2` with `lam = ε / (2 R ^ 2)` and
runs the damped anchored momentum schedule of `QuinticStencilStronglyConvex` on the regularized
objective, adding the known quadratic term to every reply (`shiftAlg`). The regularized objective is
`lam`-strongly convex and its minimizer lies within `sqrt (L R ^ 2 / lam)` of `x0` (`reg_minimizer`),
so the strongly convex ladder applies; the four-point stencil is exact on quadratics, so the bias
hypothesis transfers unchanged (`quinticBias_reg`). Convexity converts the regularized accuracy back
into accuracy of `f` at the cost of `lam / 2 * R ^ 2 = ε / 4` (`successful_transfer`).

The budget is the four-point budget of the strongly convex ladder at modulus `lam = ε / (2 R ^ 2)`,
radius `sqrt (L R ^ 2 / lam)` and accuracy `3 ε / 4`, so `QuinticStencilStronglyConvex.budget_le`
applies to `budget` verbatim once those parameters are substituted, and it is that bound which
improves on the `ε ^ (-3)` of the plain convex uniform-variance model of
`AcceleratedTwoPointZerothOrderConvex` and `PortfolioSmoothConvex` (it is `ε ^ (-5 / 2)` up to the
logarithmic factor and `(1 + rho4 ^ 2) ^ (1 / 4)`). The extra exponent is bought by the `O(h ^ 4)`
bias assumption `centralQuinticBias`, which does not follow from `L`-smoothness.
-/

namespace LongTails.Theorems.ConvexQuinticStencil

open MeasureTheory ProbabilityTheory
open LongTails.Setups
open LongTails.Setups.ZerothOrderConvexQuinticBias
open scoped BigOperators RealInnerProductSpace
open OracleTemplate OracleTemplate.SecantPolyak OracleTemplate.SecantPolyak.QuinticStencil
open OracleTemplate.SecantPolyak.Accelerated OracleTemplate.SecantPolyak.Scheduled
open OracleTemplate.SecantPolyak.CentralStencil LongTails.Proofs.ConvexRegularizedLift

/-- Regularization modulus, chosen so that the convexity correction costs only `ε / 4`. -/
noncomputable def lam (q : Params) : ℝ := q.base.ε / (2 * q.base.R ^ 2)

/-- Accuracy asked of the regularized strongly convex problem. -/
noncomputable def inner (q : Params) : ℝ := 3 * q.base.ε / 4

/-- Radius of the regularized problem around its own minimizer. -/
noncomputable def radius (q : Params) : ℝ := Real.sqrt (q.base.L * q.base.R ^ 2 / lam q)

/-- Smoothness constant of the regularized objective. -/
noncomputable def stiff (q : Params) : ℝ := q.base.L + lam q

/-- The quadratic added to the replies of the oracle. -/
noncomputable def shifty (q : Params) (x : q.base.E) : ℝ := lam q / 2 * ‖x - q.base.x0‖ ^ 2

/-- Parameters of the regularized four-point-stencil problem. -/
noncomputable abbrev slParams (q : Params) :
    LongTails.Setups.ZerothOrderStronglyConvexQuinticBias.Params where
  base :=
    { E := q.base.E
      Ω := q.base.Ω
      d := q.base.d
      L := stiff q
      R := radius q
      σ := q.base.σ
      μ := lam q
      ε := inner q
      x0 := q.base.x0 }
  rho4 := q.rho4

/-- The ladder's strong-convexity constant at the regularized parameters, i.e.
`min (lam q) (stiff q)`. -/
noncomputable abbrev muL (q : Params) : ℝ :=
  LongTails.Theorems.QuinticStencilStronglyConvex.mu (slParams q).base

/-- The ladder's momentum parameter at the regularized parameters, i.e.
`th (stiff q) (muL q)`. -/
noncomputable abbrev momL (q : Params) : ℝ :=
  LongTails.Theorems.QuinticStencilStronglyConvex.mom (slParams q).base

/-- The ladder's four-point bandwidth at the regularized parameters, i.e.
`qhband q.base.d (stiff q) (muL q) (inner q) q.rho4`. -/
noncomputable abbrev bandL (q : Params) : ℝ :=
  LongTails.Theorems.QuinticStencilStronglyConvex.bandwidth (slParams q)

/-- Oracle budget: the four-point budget of the strongly convex ladder at the regularized
parameters, radius and accuracy, counting every scalar value read by the momentum rounds. -/
noncomputable abbrev budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) :=
  fun q i => LongTails.Theorems.QuinticStencilStronglyConvex.budget (slParams q) i

set_option maxHeartbeats 4000000 in
theorem result : Convergence LongTails.Setups.ZerothOrderConvexQuinticBias.spec budget := by
  classical
  refine ⟨fun q =>
      shiftAlg (LongTails.Theorems.QuinticStencilStronglyConvex.result.choose (slParams q))
        (shifty q),
    ?_, fun _ _ => trivial⟩
  intro q hq f O ho
  obtain ⟨⟨hd, hL, hR0, hσ, hε⟩, hR, hρ4⟩ := hq
  obtain ⟨hbadm, hcb⟩ := ho
  obtain ⟨he, g, p, P, hind, hmarg, hO, hconv, hgr, hlip, ⟨u, hminu, hdist⟩, hgm, hgi, hmean,
    hgsq, hvar⟩ := hbadm
  subst hO
  let Ab : Algorithm q.base.E ℝ q.base.E :=
    LongTails.Theorems.QuinticStencilStronglyConvex.result.choose (slParams q)
  let G : q.base.E → q.base.Ω → ℝ := fun x ω => g x ω + shifty q x
  let O₁ : Oracle q.base.E ℝ 1 :=
    { Seed := fun _ => q.base.Ω, law := P, answer := fun _ (_, x) ω => g x ω }
  let O₂ : Oracle q.base.E ℝ 1 := mkOracle P G
  let F : q.base.E → ℝ := reg f (lam q) q.base.x0
  have hlam : 0 < lam q := by
    have hR2 : 0 < q.base.R ^ 2 := by positivity
    simp only [lam]
    positivity
  have hstiff : 0 < stiff q := by
    simp only [stiff]
    linarith
  have hinner : 0 < inner q := by
    simp only [inner]
    linarith
  have hGm : Measurable (Function.uncurry G) := by
    have h1 : Measurable (fun z : q.base.E × q.base.Ω => g z.1 z.2) := hgm
    have h2 : Measurable (fun z : q.base.E × q.base.Ω => shifty q z.1) := by
      simp only [shifty]
      fun_prop
    change Measurable (fun z : q.base.E × q.base.Ω => g z.1 z.2 + shifty q z.1)
    exact h1.add h2
  have hmeanS : ∀ x, ∫ ω, G x ω ∂(p : Measure _) = F x := by
    intro x
    have h1 : ∫ ω, g x ω ∂(p : Measure _) = f x := hmean x
    have h2 : ∫ _ω : q.base.Ω, shifty q x ∂(p : Measure _) = shifty q x := by simp
    rw [integral_add (hgi x) (integrable_const _), h1, h2]
    simp only [F, reg, shifty]
  have hgiS : ∀ x, Integrable (G x) (p : Measure _) := fun x =>
    (hgi x).add (integrable_const _)
  have hsq_eq : ∀ x, (fun ω => (G x ω - F x) ^ 2) = fun ω => (g x ω - f x) ^ 2 := by
    intro x
    funext ω
    have h : G x ω - F x = g x ω - f x := by
      show (g x ω + shifty q x) - (f x + lam q / 2 * ‖x - q.base.x0‖ ^ 2) = g x ω - f x
      rw [shifty]
      ring
    rw [h]
  have hgsqS : ∀ x, Integrable (fun ω => (G x ω - F x) ^ 2) (p : Measure _) := by
    intro x
    rw [hsq_eq x]
    exact hgsq x
  have hvarS : ∀ x, (∫ ω, (G x ω - F x) ^ 2 ∂(p : Measure _)) ≤ (slParams q).base.σ ^ 2 := by
    intro x
    rw [hsq_eq x]
    exact hvar x
  obtain ⟨ystar, hminS, hdistS⟩ :=
    reg_minimizer (f := f) (lam := lam q) (L := q.base.L) (R := q.base.R) (x0 := q.base.x0)
      (u := u) he.some hL hlam hconv hgr hlip hminu hdist
  have hdistRad : ‖q.base.x0 - ystar‖ ≤ radius q := by
    have h1 : ‖q.base.x0 - ystar‖ ^ 2 ≤ q.base.L * q.base.R ^ 2 / lam q := by
      rw [le_div_iff₀ hlam]
      nlinarith [hdistS]
    have h2 : Real.sqrt (‖q.base.x0 - ystar‖ ^ 2) ≤
        Real.sqrt (q.base.L * q.base.R ^ 2 / lam q) := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (norm_nonneg _)] at h2
  have hbias : LongTails.Setups.ZerothOrderStronglyConvexQuinticBias.centralQuinticBias
      (slParams q) F := quinticBias_reg (c := q.base.x0) hcb hgr
  have hadm : LongTails.Setups.ZerothOrderStronglyConvexQuinticBias.spec.admissible (slParams q)
      F O₂ := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · refine ⟨⟨he.some⟩, G, p, P, hind, hmarg, ?_, ?_, ?_, ?_, ⟨ystar, hminS, hdistRad⟩, hGm,
        hgiS, hmeanS, hgsqS, hvarS⟩
      · rfl
      · exact reg_convex f (c := q.base.x0) hconv hlam.le
      · intro x
        change HasGradientAt F (gradient F x) x
        rw [reg_gradient_eq f (lam q) q.base.x0 (hgr x)]
        exact reg_hasGradient f (lam q) q.base.x0 (hgr x)
      · exact fun x y => reg_lipschitz f q.base.x0 hlam.le hgr hlip x y
    · exact ⟨ystar, hminS, hdistRad, fun x y => reg_tangent f q.base.x0 hconv hgr x y⟩
    · exact hbias
  have hvalid : LongTails.Setups.ZerothOrderStronglyConvexQuinticBias.spec.valid (slParams q) :=
    ⟨⟨hd, hstiff, Real.sqrt_nonneg _, hσ, hlam, hinner⟩, hρ4⟩
  obtain ⟨hmeas, xs, hminxs, hint, hbnd⟩ :=
    LongTails.Theorems.QuinticStencilStronglyConvex.result.choose_spec.1 (slParams q) hvalid F O₂
      hadm
  have hfm : Measurable f :=
    (continuous_iff_continuousAt.mpr (fun x => (hgr x).continuousAt)).measurable
  have hpt : ∀ z : q.base.E, f z - f u ≤ (F z - F xs) + q.base.ε / 4 := by
    intro z
    have h1 : f xs + lam q / 2 * ‖xs - q.base.x0‖ ^ 2 ≤
        f u + lam q / 2 * ‖u - q.base.x0‖ ^ 2 := hminxs (Set.mem_univ u)
    have hR2 : ‖u - q.base.x0‖ ^ 2 ≤ q.base.R ^ 2 := by
      rw [norm_sub_rev u q.base.x0]
      nlinarith [norm_nonneg (q.base.x0 - u), hdist]
    have hmul : lam q / 2 * ‖u - q.base.x0‖ ^ 2 ≤ lam q / 2 * q.base.R ^ 2 :=
      mul_le_mul_of_nonneg_left hR2 (by positivity)
    have hlamR : lam q / 2 * q.base.R ^ 2 = q.base.ε / 4 := by
      simp only [lam]
      field_simp
      ring
    have hnonneg : 0 ≤ lam q / 2 * ‖z - q.base.x0‖ ^ 2 := by positivity
    simp only [F, reg]
    linarith
  have hinnerε : inner q + q.base.ε / 4 = q.base.ε := by
    simp only [inner]
    ring
  refine successful_transfer
    (P := ⟨(Ab.law : Measure Ab.Seed).prod (P : Measure (ℕ → q.base.Ω)), inferInstance⟩)
    (f := f) (φ := F) (u := u) (w := xs) (ε := q.base.ε) (c := q.base.ε / 4)
    (outS := fun seed : (shiftAlg Ab (shifty q)).Seed × ((k : ℕ) → q.base.Ω) =>
      execute O₁ (shiftAlg Ab (shifty q)) (budget q) seed.1 seed.2)
    (outR := fun seed : Ab.Seed × ((k : ℕ) → q.base.Ω) =>
      execute O₂ Ab (budget q) seed.1 seed.2) ?_ ?_ ?_ ?_ hminu hfm hpt
  · funext seed
    exact execute_shiftAlg' P g (shifty q) Ab (budget q 0) seed.1 seed.2
  · exact hmeas
  · exact hint
  · refine le_trans hbnd ?_
    linarith [hinnerε]

set_option maxHeartbeats 1000000 in
/-- Machine-checked scale of the budget: it is the bound of `QuinticStencilStronglyConvex.budget_le`
at the regularized parameters, that is

`4 d (1 + 2 / momL * log (1 + 2 (stiff / 2 * radius2 + muL / 4 * radius2) / inner))
   (2 + 32 (1 / (2 stiff) + momL2 / muL) d sigma2 / (momL * inner * bandL2))`,

up to the constant factors written out in the statement. With `lam = ε / (2 R2)` and
`inner = 3 ε / 4` its small-`ε` order is `d * (d / (lam * inner)) ^ (5 / 4) * sigma2 * log (1 / ε)`,
i.e. `ε ^ (-5 / 2)` up to the logarithmic factor and `(1 + rho4 ^ 2) ^ (1 / 4)`, against the
`ε ^ (-3)` of the plain convex uniform-variance model. -/
lemma budget_le (q : Params) (i : Fin 1) (hq : spec.valid q) :
    (budget q i : ℝ)
      ≤ 4 * (q.base.d : ℝ)
        * (1 + 2 / momL q
            * Real.log (2 * (stiff q / 2 * radius q ^ 2 + muL q / 4 * radius q ^ 2) / inner q + 1))
        * (2 + 32 * (1 / (2 * stiff q) + momL q ^ 2 / muL q) * (q.base.d : ℝ) * q.base.σ ^ 2
            / (momL q * inner q * bandL q ^ 2)) := by
  obtain ⟨⟨hd, hL, hR0, hσ, hε⟩, hR, hρ4⟩ := hq
  have hlam : 0 < lam q := by
    have hR2 : 0 < q.base.R ^ 2 := by positivity
    simp only [lam]
    positivity
  have hstiff : 0 < stiff q := by
    simp only [stiff]
    linarith
  have hinner : 0 < inner q := by
    simp only [inner]
    linarith
  exact LongTails.Theorems.QuinticStencilStronglyConvex.budget_le (slParams q) i
    ⟨⟨hd, hstiff, Real.sqrt_nonneg _, hσ, hlam, hinner⟩, hρ4⟩

end LongTails.Theorems.ConvexQuinticStencil
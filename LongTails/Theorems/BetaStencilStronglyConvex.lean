import LongTails.Setups.ZerothOrderStronglyConvexBetaBias
import LongTails.Proofs.BetaStencilSpace
import LongTails.Proofs.BetaStencilTuning

/-!
Zeroth-order stochastic minimization of a strongly convex objective from noisy values, using the
`M`-band (Richardson) coordinate stencil

  ∑ j : Fin M, betaWeight M j *
    (f (x + ((j + 1) * h) • e i) - f (x - ((j + 1) * h) • e i)) / (2 * (j + 1) * h)

inside the damped anchored momentum schedule. This is the single algorithm that unifies the ladder
already proved in this repository: `M = 1` is the symmetric central stencil of
`CubicCentralMomentumStronglyConvex`, `M = 2` the four-point stencil of
`QuinticStencilStronglyConvex`, `M = 3` the six-point stencil of `SexticStencilStronglyConvex`,
`M = 4` the eight-point stencil of `OcticStencilStronglyConvex` and `M = 5` the ten-point stencil of
`DecicStencilStronglyConvex`; the weight checks `betaWeight_one`, `betaWeight_two`,
`betaWeight_three`, `betaWeight_four` and `betaWeight_five` in the calling setup identify the
weights of all five previously proved members of the ladder.

The stencil is realised with `M * n` central replicas per coordinate, the bands probing bandwidth
`h, 2 * h, ..., M * h`, so every round reads `2 * M * d * n` scalar values. Under the `M`-band
regularity `centralBetaBias` of the calling setup the squared bias is
`d * (rho * h ^ (2 * M)) ^ 2`, the bandwidth is a `(4 * M)`-th root of `epsilon`, and the budget
lemma `budget_le` exhibits a budget of order

  d * (d / (mu * epsilon)) ^ ((2 * M + 1) / (2 * M)) * sigma ^ 2 * log (1 / epsilon),
  up to the factor (1 + rho ^ 2) ^ (1 / (2 * M)) and the noise factor betaAbs M ^ 2.

Writing the smoothness order as `beta = 2 * M + 1`, the exponent `(2 * M + 1) / (2 * M)` is exactly
`beta / (beta - 1)`, the rate of the minimax theory of highly smooth strongly convex zeroth-order
optimization (`arXiv 2610.00276`), and the ladder above is the sequence `M = 1, 2, 3, 4, 5`.

The exponent is a consequence of the extra `O (h ^ (2 * M))` bias assumption `centralBetaBias`,
which does NOT follow from ordinary `L`-smoothness nor from any weaker member of the ladder, and is
not claimed for the plain strongly convex or the convex setups: with only `L`-smoothness
`ZerothOrderStronglyConvex` needs `epsilon ^ 2` calls, and the convex uniform-variance model of
`LongTails.Theorems.PortfolioSmoothConvex` still costs `epsilon ^ 3`.
-/

namespace LongTails.Theorems.BetaStencilStronglyConvex

open MeasureTheory ProbabilityTheory
open LongTails.Setups
open LongTails.Setups.ZerothOrderSmoothAndConvex
open LongTails.Setups.ZerothOrderStronglyConvexBetaBias
open scoped BigOperators
open scoped RealInnerProductSpace
open OracleTemplate SecantPolyak
open OracleTemplate.SecantPolyak.Accelerated OracleTemplate.SecantPolyak.Centered
open OracleTemplate.SecantPolyak.Scheduled OracleTemplate.Research
open OracleTemplate.SecantPolyak.CentralStencil
open OracleTemplate.SecantPolyak.BetaStencil OracleTemplate.SecantDescent

/-- Strong-convexity constant used for tuning: no larger than the smoothness constant. -/
noncomputable def mu (q : LongTails.Setups.ZerothOrderStronglyConvex.Params) : ℝ :=
  min q.μ q.L

/-- Momentum parameter: of order `sqrt (μ / L)`, the classic acceleration scaling. -/
noncomputable def mom (q : LongTails.Setups.ZerothOrderStronglyConvex.Params) : ℝ :=
  th q.L (mu q)

/-- Number of momentum rounds: of order `sqrt (L / μ) * log (1 / ε)`. -/
noncomputable def steps (q : LongTails.Setups.ZerothOrderStronglyConvex.Params) : ℕ :=
  iters q.L (mu q) q.R q.ε

/-- Bandwidth of the `M`-band stencil: the `(4 * M)`-th root balancing `d * (rho * h ^ (2*M)) ^ 2`. -/
noncomputable def bandwidth (q : LongTails.Setups.ZerothOrderStronglyConvexBetaBias.Params) : ℝ :=
  betaHband q.bands q.base.d q.base.L (mu q.base) q.base.ε q.rho

/-- Replicas of the `M`-band stencil averaged per coordinate in every round. -/
noncomputable def replicas (q : LongTails.Setups.ZerothOrderStronglyConvexBetaBias.Params) : ℕ :=
  betaBatch q.bands q.base.d q.base.L (mu q.base) q.base.σ q.base.ε q.rho

/-- The replica count is positive. -/
lemma replicas_pos (q : LongTails.Setups.ZerothOrderStronglyConvexBetaBias.Params) :
    0 < replicas q := Nat.succ_pos _

/-- Oracle budget: the exact number of scalar value calls made by the `steps q.base` momentum
rounds, counting the `2 * q.bands` stencil points of every replica of every coordinate. -/
noncomputable def budget :
    (let S := LongTails.Setups.ZerothOrderStronglyConvexBetaBias.spec;
      S.Params → Fin S.numOracles → ℕ) :=
  fun q _ => ∑ _k ∈ Finset.range (steps q.base), roundSlots q.base.d (q.bands * replicas q)

/-- The fallback algorithm used when the dimension or the band count is degenerate. -/
noncomputable def trivialAlgorithm (q : LongTails.Setups.ZerothOrderStronglyConvex.Params) :
    Algorithm q.E ℝ q.E :=
  { State := q.E, initial := fun _ => q.x0, query := fun x => (0, x), update := fun x _ => x,
    output := id }

theorem result :
    Convergence LongTails.Setups.ZerothOrderStronglyConvexBetaBias.spec budget := by
  classical
  refine ⟨fun q =>
      if h : Nonempty (q.base.E ≃ₗᵢ[ℝ] Point q.base.d) then
        if hd : 0 < q.base.d then
          if hb : 0 < q.bands then
            SecantPolyak.ofPoint h.some.symm
              (BetaStencilMomentumZO.algorithm hd (fun _ => replicas_pos q) hb q.base.L
                (mu q.base) (mom q.base) (bandwidth q) (h.some q.base.x0))
          else trivialAlgorithm q.base
        else trivialAlgorithm q.base
      else trivialAlgorithm q.base,
    ?_, fun _ _ => trivial⟩
  intro q hq f O ho
  rcases hq with ⟨⟨hd, hL, hR, hσ, hμ, hε⟩, hbands, hρ⟩
  obtain ⟨hbadm, hcbq⟩ := ho
  obtain ⟨hbase, xstar, hmin, hdist, hsc⟩ := hbadm
  obtain ⟨he, g, p, P, hind, hmarg, hO, hconv, hgr, hlip, _, hgm, hgi, hmean, hgsq, hvar⟩ := hbase
  subst hO
  set e : q.base.E ≃ₗᵢ[ℝ] Point q.base.d := he.some
  set mub : ℝ := mu q.base with hmubdef
  have hmu : 0 < mub := lt_min_iff.mpr ⟨hμ, hL⟩
  have hmuL : mub ≤ q.base.L := min_le_right _ _
  have hscmu : ∀ x y,
      f x + ⟪gradient f x, y - x⟫ + mub / 2 * ‖y - x‖ ^ 2 ≤ f y := by
    intro x y
    have h1 : mub / 2 * ‖y - x‖ ^ 2 ≤ q.base.μ / 2 * ‖y - x‖ ^ 2 := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have : mub ≤ q.base.μ := min_le_left _ _
      linarith
    linarith [hsc x y]
  have hth0 : 0 < mom q.base := th_pos q.base.L mub hL hmu
  have hth1 : mom q.base ≤ 1 := th_le_one q.base.L mub
  have hthL : 16 * q.base.L * mom q.base ^ 2 ≤ mub := th_constraint q.base.L mub hL hmu
  have hh0 : 0 < bandwidth q :=
    betaHband_pos hd q.base.L mub q.base.ε q.rho hL hmu hε
  have hbound : (1 - mom q.base / 2) ^ steps q.base * (q.base.L / 2 * q.base.R ^ 2
        + mub / 4 * q.base.R ^ 2)
      + ∑ k ∈ Finset.range (steps q.base), (1 - mom q.base / 2) ^ (steps q.base - 1 - k)
          * (2 * (3 / (4 * q.base.L) + 2 * mom q.base / mub)
              * ((q.base.d : ℝ) * (q.rho * bandwidth q ^ (2 * q.bands)) ^ 2)
            + (1 / (2 * q.base.L) + mom q.base ^ 2 / mub)
                * (betaAbs q.bands ^ 2
                  * ((q.base.d : ℝ) * q.base.σ ^ 2 / (bandwidth q ^ 2 * (replicas q : ℝ)))))
        ≤ q.base.ε :=
    betaTuning hbands q.base.d hd q.base.L mub q.base.σ q.base.R q.base.ε q.rho
      hL hmu hmuL hσ hR hε hρ
  have hmain := beta_space_accuracy (M := q.bands) hbands (E := q.base.E) (d := q.base.d)
    (hd := hd) (e := e) (f := f)
    (L := q.base.L) (R := q.base.R) (σ := q.base.σ) (μ := mub) (ε := q.base.ε) (θ := mom q.base)
    (h := bandwidth q) (ρ := q.rho) (x0 := q.base.x0) (xstar := xstar) (Ω := q.base.Ω) (g := g)
    (K := steps q.base) (N := q.bands * replicas q)
    hconv hgr hlip hL hR hσ hmu hmuL hε hth0 hth1 hthL hh0 hρ hcbq hscmu hmin hdist
    hgm hind hmarg hgi hmean hgsq hvar (fun _ => replicas_pos q)
    (fun _ => Nat.le_refl _) hbound
  dsimp only
  have hEq : (if h : Nonempty (q.base.E ≃ₗᵢ[ℝ] Point q.base.d) then
        if hd' : 0 < q.base.d then
          if hb : 0 < q.bands then
            SecantPolyak.ofPoint h.some.symm
              (BetaStencilMomentumZO.algorithm hd' (fun _ => replicas_pos q) hb q.base.L
                (mu q.base) (mom q.base) (bandwidth q) (h.some q.base.x0))
          else trivialAlgorithm q.base
        else trivialAlgorithm q.base
      else trivialAlgorithm q.base)
      = SecantPolyak.ofPoint e.symm
        (BetaStencilMomentumZO.algorithm hd (fun _ => replicas_pos q) hbands q.base.L mub
          (mom q.base) (bandwidth q) (e q.base.x0)) := by
    rw [dite_eq_left he, dite_eq_left hd, dite_eq_left hbands]
  have htransport : ∀ (A A' : Algorithm q.base.E ℝ q.base.E), A = A' →
      LongTails.Setups.ZerothOrderStronglyConvexBetaBias.spec.successful q f
        (fun seed : A.Seed × ((k : ℕ) → q.base.Ω) =>
          execute { Seed := fun _ => q.base.Ω, law := P, answer := fun _ (_, x) ω => g x ω } A
            (budget q) seed.1 seed.2)
        ⟨(A.law : Measure _).prod (P : Measure _), inferInstance⟩ →
      LongTails.Setups.ZerothOrderStronglyConvexBetaBias.spec.successful q f
        (fun seed : A'.Seed × ((k : ℕ) → q.base.Ω) =>
          execute { Seed := fun _ => q.base.Ω, law := P, answer := fun _ (_, x) ω => g x ω } A'
            (budget q) seed.1 seed.2)
        ⟨(A'.law : Measure _).prod (P : Measure _), inferInstance⟩ := by
    intro A A' hAA h
    cases hAA
    exact h
  exact htransport _ _ hEq.symm ⟨hmain.1, xstar, hmin, hmain.2.1, hmain.2.2⟩

/-- Machine-checked scale of the budget: the call count is the number of rounds times the
`2 * q.bands` stencil points per replica, bounded by
`2 * M * d * (1 + 2 / theta * log (1 + 2 (L/2 + mu/4) R² / eps))
   * (2 + 8 * betaAbs M ^ 2 * (1/(2L) + theta²/mu) * d sigma² / (theta eps h²))`
with `h` the `(4 * M)`-th root bandwidth, hence of order whose dominant small-epsilon term is
`d * (d / (mu * eps)) ^ ((2 * M + 1) / (2 * M)) * sigma² * log (1 / eps)`, up to the factor
`(1 + rho²) ^ (1 / (2 * M))`, which is `beta / (beta - 1)` for `beta = 2 * M + 1`. -/
lemma budget_le (q : LongTails.Setups.ZerothOrderStronglyConvexBetaBias.Params)
    (i : Fin 1) (hq : LongTails.Setups.ZerothOrderStronglyConvexBetaBias.spec.valid q) :
    (budget q i : ℝ)
      ≤ 2 * (q.bands : ℝ) * (q.base.d : ℝ)
        * (1 + 2 / mom q.base
            * Real.log (2 * (q.base.L / 2 * q.base.R ^ 2 + mu q.base / 4 * q.base.R ^ 2)
              / q.base.ε + 1))
        * (2 + 8 * betaAbs q.bands ^ 2 * (1 / (2 * q.base.L) + mom q.base ^ 2 / mu q.base)
            * (q.base.d : ℝ) * q.base.σ ^ 2 / (mom q.base * q.base.ε * bandwidth q ^ 2)) := by
  classical
  rcases hq.1 with ⟨hd, hL, hR, hσ, hμ, hε⟩
  have hmu : 0 < mu q.base := lt_min_iff.mpr ⟨hμ, hL⟩
  have hth : 0 < mom q.base := th_pos q.base.L (mu q.base) hL hmu
  have hn : (budget q i : ℝ)
      = (steps q.base : ℝ) * (2 * (q.bands : ℝ) * (q.base.d : ℝ) * (replicas q : ℝ)) := by
    have hsum : (budget q i : ℝ) =
        ∑ _k ∈ Finset.range (steps q.base), (roundSlots q.base.d (q.bands * replicas q) : ℝ) := by
      simp [budget]
    have hcard : (roundSlots q.base.d (q.bands * replicas q) : ℝ)
        = 2 * (q.bands : ℝ) * (q.base.d : ℝ) * (replicas q : ℝ) := by
      show (Fintype.card (Fin (q.bands * replicas q) × (Fin q.base.d × Bool)) : ℝ) = _
      rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
        Fintype.card_bool]
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      ring
    rw [hsum, Finset.sum_congr rfl (fun _ _ => hcard), Finset.sum_const, Finset.card_range]
    ring
  set X : ℝ := (2 / mom q.base)
    * Real.log (2 * (q.base.L / 2 * q.base.R ^ 2 + mu q.base / 4 * q.base.R ^ 2) / q.base.ε + 1)
    with hXdef
  set Y : ℝ := 8 * betaAbs q.bands ^ 2 * (1 / (2 * q.base.L) + mom q.base ^ 2 / mu q.base)
    * (q.base.d : ℝ) * q.base.σ ^ 2 / (mom q.base * q.base.ε * bandwidth q ^ 2) with hYdef
  have hX0 : (0 : ℝ) ≤ X := by
    rw [hXdef]
    refine mul_nonneg (div_nonneg (by norm_num) (le_of_lt hth)) ?_
    have h1 : (0 : ℝ) ≤ 2 * (q.base.L / 2 * q.base.R ^ 2 + mu q.base / 4 * q.base.R ^ 2)
        / q.base.ε := by positivity
    have hlt : (1 : ℝ) ≤ 2 * (q.base.L / 2 * q.base.R ^ 2 + mu q.base / 4 * q.base.R ^ 2)
        / q.base.ε + 1 := by linarith
    exact Real.log_nonneg hlt
  have hY0 : (0 : ℝ) ≤ Y := by
    rw [hYdef]
    refine div_nonneg ?_ (by positivity)
    refine mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) ?_) (Nat.cast_nonneg _))
      (sq_nonneg _)
    refine add_nonneg (by positivity) (div_nonneg (sq_nonneg _) (le_of_lt hmu))
  have hK : (steps q.base : ℝ) < X + 1 := by
    have h1 : (steps q.base : ℝ) = (⌈X⌉₊ : ℝ) := rfl
    rw [h1]
    exact Nat.ceil_lt_add_one hX0
  have hM : (replicas q : ℝ) < Y + 2 := by
    have h1 : (replicas q : ℝ) = (⌈Y⌉₊ : ℝ) + 1 := by
      show ((⌈Y⌉₊ + 1 : ℕ) : ℝ) = (⌈Y⌉₊ : ℝ) + 1
      rw [Nat.cast_add, Nat.cast_one]
    rw [h1]
    linarith [Nat.ceil_lt_add_one hY0]
  have hd0 : (0 : ℝ) ≤ q.bands := Nat.cast_nonneg _
  have hd1 : (0 : ℝ) ≤ q.base.d := Nat.cast_nonneg _
  have hK0 : (0 : ℝ) ≤ steps q.base := Nat.cast_nonneg _
  have hM0 : (0 : ℝ) ≤ replicas q := Nat.cast_nonneg _
  have hKM : (steps q.base : ℝ) * (replicas q : ℝ) ≤ (1 + X) * (2 + Y) := by nlinarith
  have hc : (0 : ℝ) ≤ 2 * (q.bands : ℝ) * (q.base.d : ℝ) := by positivity
  have hprod : (steps q.base : ℝ) * (2 * (q.bands : ℝ) * (q.base.d : ℝ) * (replicas q : ℝ))
      = 2 * (q.bands : ℝ) * (q.base.d : ℝ)
          * ((steps q.base : ℝ) * (replicas q : ℝ)) := by ring
  have hstep : 2 * (q.bands : ℝ) * (q.base.d : ℝ) * ((steps q.base : ℝ) * (replicas q : ℝ))
      ≤ 2 * (q.bands : ℝ) * (q.base.d : ℝ) * ((1 + X) * (2 + Y)) :=
    mul_le_mul_of_nonneg_left hKM hc
  have has : 2 * (q.bands : ℝ) * (q.base.d : ℝ) * ((1 + X) * (2 + Y))
      = 2 * (q.bands : ℝ) * (q.base.d : ℝ) * (1 + X) * (2 + Y) := by ring
  rw [hn, hprod, ← has]
  exact hstep

end LongTails.Theorems.BetaStencilStronglyConvex

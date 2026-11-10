import LongTails.Setups.ZerothOrderStronglyConvexUndecicBias
import LongTails.Proofs.DecicStencilSpace
import LongTails.Proofs.DecicStencilTuning

/-!
Zeroth-order stochastic minimization of a strongly convex objective from noisy values, using the
ten-point (Richardson) coordinate stencil

  (2100 * (f (x + h e i) - f (x - h e i)) - 600 * (f (x + 2 h e i) - f (x - 2 h e i))
    + 150 * (f (x + 3 h e i) - f (x - 3 h e i))
    - 25 * (f (x + 4 h e i) - f (x - 4 h e i))
    + 2 * (f (x + 5 h e i) - f (x - 5 h e i))) / (2520 h)

inside the damped anchored momentum schedule. The stencil is realised with 5 n central replicas
per coordinate, the five bands probing bandwidth `h`, `2 h`, `3 h`, `4 h` and `5 h`, so every round
reads `10 * d * n` scalar values. Under the extra ten-point regularity of the calling setup the
squared bias is `d * (rho10 * h ^ 10) ^ 2`, the bandwidth is a twentieth root of `epsilon`, and
`budget_le`
exhibits a budget of order

  d * (d / (mu * epsilon)) ^ (11 / 10) * sigma ^ 2 * log (1 / epsilon),
  up to the factor `(1 + rho10 ^ 2) ^ (1 / 10)`; `budget_le` states the bound with the exact
  constants, and `bandwidth` and `replicas` give the tuning that attains it.

whereas the six-point stencil of `SexticStencilStronglyConvex` needs `epsilon ^ (7 / 6)` calls under
`O (h ^ 6)` bias, the four-point stencil of `QuinticStencilStronglyConvex` needs `epsilon ^ (5 / 4)`
calls under `O (h ^ 4)` bias, the symmetric central stencil of `CubicCentralMomentumStronglyConvex`
needs `epsilon ^ (3 / 2)` calls under `O (h ^ 2)` bias, and the one-sided secant stencil of
`ZerothOrderStronglyConvex` needs `epsilon ^ 2` calls under ordinary `L`-smoothness. The exponent
The eight-point stencil of `OcticStencilStronglyConvex` needs `epsilon ^ (9 / 8)` calls under
`O (h ^ 8)` bias. The exponent `11 / 10` is a consequence of the extra `O (h ^ 10)` bias
assumption, which does NOT follow from ordinary `L`-smoothness nor from the eight-point
`O (h ^ 8)` regularity, and is not claimed for the plain strongly convex or convex setups.
-/

namespace LongTails.Theorems.DecicStencilStronglyConvex

open MeasureTheory ProbabilityTheory
open LongTails.Setups
open LongTails.Setups.ZerothOrderSmoothAndConvex
open scoped BigOperators
open scoped RealInnerProductSpace
open OracleTemplate SecantPolyak
open OracleTemplate.SecantPolyak.Accelerated OracleTemplate.SecantPolyak.Centered
open OracleTemplate.SecantPolyak.Scheduled OracleTemplate.Research
open OracleTemplate.SecantPolyak.CentralStencil
open OracleTemplate.SecantPolyak.DecicStencil OracleTemplate.SecantDescent

/-- Strong-convexity constant used for tuning: no larger than the smoothness constant. -/
noncomputable def mu (q : LongTails.Setups.ZerothOrderStronglyConvex.Params) : ℝ :=
  min q.μ q.L

/-- Momentum parameter: of order `sqrt (μ / L)`, the classic acceleration scaling. -/
noncomputable def mom (q : LongTails.Setups.ZerothOrderStronglyConvex.Params) : ℝ :=
  th q.L (mu q)

/-- Number of momentum rounds: of order `sqrt (L / μ) * log (1 / ε)`. -/
noncomputable def steps (q : LongTails.Setups.ZerothOrderStronglyConvex.Params) : ℕ :=
  iters q.L (mu q) q.R q.ε

/-- Bandwidth of the ten-point stencil: the twentieth root balancing `d * (rho10 * h ^ 10) ^ 2`. -/
noncomputable def bandwidth
    (q : LongTails.Setups.ZerothOrderStronglyConvexUndecicBias.Params) : ℝ :=
  dxhband q.base.d q.base.L (mu q.base) q.base.ε q.rho10

/-- Replicas of the ten-point stencil averaged per coordinate in every round. -/
noncomputable def replicas
    (q : LongTails.Setups.ZerothOrderStronglyConvexUndecicBias.Params) : ℕ :=
  dxbatch q.base.d q.base.L (mu q.base) q.base.σ q.base.ε q.rho10

/-- The replica count is positive. -/
lemma replicas_pos (q : LongTails.Setups.ZerothOrderStronglyConvexUndecicBias.Params) :
    0 < replicas q := Nat.succ_pos _

/-- Oracle budget: the exact number of scalar value calls made by the `steps q.base` momentum
rounds, counting the ten stencil points of every replica of every coordinate. -/
noncomputable def budget :
    (let S := LongTails.Setups.ZerothOrderStronglyConvexUndecicBias.spec;
      S.Params → Fin S.numOracles → ℕ) :=
  fun q _ => ∑ _k ∈ Finset.range (steps q.base), roundSlots q.base.d (5 * replicas q)

theorem result :
    Convergence LongTails.Setups.ZerothOrderStronglyConvexUndecicBias.spec budget := by
  classical
  refine ⟨fun q =>
      if h : Nonempty (q.base.E ≃ₗᵢ[ℝ] Point q.base.d) then
        if hd : 0 < q.base.d then
          SecantPolyak.ofPoint h.some.symm
            (DecicStencilMomentumZO.algorithm hd (fun _ => replicas_pos q) q.base.L (mu q.base)
              (mom q.base) (bandwidth q) (h.some q.base.x0))
        else
          { State := q.base.E, initial := fun _ => q.base.x0, query := fun x => (0, x),
            update := fun x _ => x, output := id }
      else
        { State := q.base.E, initial := fun _ => q.base.x0, query := fun x => (0, x),
          update := fun x _ => x, output := id },
    ?_, fun _ _ => trivial⟩
  intro q hq f O ho
  rcases hq with ⟨⟨hd, hL, hR, hσ, hμ, hε⟩, hρ⟩
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
    dxhband_pos hd q.base.L mub q.base.ε q.rho10 hL hmu hε
  have hbound : (1 - mom q.base / 2) ^ steps q.base * (q.base.L / 2 * q.base.R ^ 2
        + mub / 4 * q.base.R ^ 2)
      + ∑ k ∈ Finset.range (steps q.base), (1 - mom q.base / 2) ^ (steps q.base - 1 - k)
          * (2 * (3 / (4 * q.base.L) + 2 * mom q.base / mub)
              * ((q.base.d : ℝ) * (q.rho10 * bandwidth q ^ 10) ^ 2)
            + (1 / (2 * q.base.L) + mom q.base ^ 2 / mub)
                * (6 * ((q.base.d : ℝ) * q.base.σ ^ 2 / (bandwidth q ^ 2 * (replicas q : ℝ)))))
        ≤ q.base.ε :=
    dx_tuning q.base.d hd q.base.L mub q.base.σ q.base.R q.base.ε q.rho10 hL hmu hmuL hσ hR hε hρ
  have hmain := dx_space_accuracy (E := q.base.E) (d := q.base.d) (hd := hd) (e := e) (f := f)
    (L := q.base.L) (R := q.base.R) (σ := q.base.σ) (μ := mub) (ε := q.base.ε) (θ := mom q.base)
    (h := bandwidth q) (ρ10 := q.rho10) (x0 := q.base.x0) (xstar := xstar) (Ω := q.base.Ω) (g := g)
    (K := steps q.base) (N := 5 * replicas q)
    hconv hgr hlip hL hR hσ hmu hmuL hε hth0 hth1 hthL hh0 hρ hcbq hscmu hmin hdist
    hgm hind hmarg hgi hmean hgsq hvar (fun _ => replicas_pos q)
    (fun _ => Nat.le_refl _) hbound
  dsimp only
  have hEq : (if h : Nonempty (q.base.E ≃ₗᵢ[ℝ] Point q.base.d) then
        if hd' : 0 < q.base.d then
          SecantPolyak.ofPoint h.some.symm
            (DecicStencilMomentumZO.algorithm hd' (fun _ => replicas_pos q) q.base.L (mu q.base)
              (mom q.base) (bandwidth q) (h.some q.base.x0))
        else
          { State := q.base.E, initial := fun _ => q.base.x0, query := fun x => (0, x),
            update := fun x _ => x, output := id }
      else
        { State := q.base.E, initial := fun _ => q.base.x0, query := fun x => (0, x),
          update := fun x _ => x, output := id })
      = SecantPolyak.ofPoint e.symm
        (DecicStencilMomentumZO.algorithm hd (fun _ => replicas_pos q) q.base.L mub (mom q.base)
          (bandwidth q) (e q.base.x0)) := by
    rw [dite_eq_left he, dite_eq_left hd]
  have htransport : ∀ (A A' : Algorithm q.base.E ℝ q.base.E), A = A' →
      LongTails.Setups.ZerothOrderStronglyConvexUndecicBias.spec.successful q f
        (fun seed : A.Seed × ((k : ℕ) → q.base.Ω) =>
          execute { Seed := fun _ => q.base.Ω, law := P, answer := fun _ (_, x) ω => g x ω } A
            (budget q) seed.1 seed.2)
        ⟨(A.law : Measure _).prod (P : Measure _), inferInstance⟩ →
      LongTails.Setups.ZerothOrderStronglyConvexUndecicBias.spec.successful q f
        (fun seed : A'.Seed × ((k : ℕ) → q.base.Ω) =>
          execute { Seed := fun _ => q.base.Ω, law := P, answer := fun _ (_, x) ω => g x ω } A'
            (budget q) seed.1 seed.2)
        ⟨(A'.law : Measure _).prod (P : Measure _), inferInstance⟩ := by
    intro A A' hAA h
    cases hAA
    exact h
  exact htransport _ _ hEq.symm ⟨hmain.1, xstar, hmin, hmain.2.1, hmain.2.2⟩

/-- Machine-checked scale of the budget: the call count is the number of rounds times the ten
stencil points per replica, bounded by
`10 d (1 + 2 / theta * log (1 + 2 (L/2 + mu/4) R² / eps))
   (2 + 48 (1/(2L) + theta²/mu) d sigma² / (theta eps h²))`
with `h` the twentieth-root bandwidth of the ten-point stencil, hence of order
whose dominant small-epsilon term is
`d * (d / (mu * eps)) ^ (11 / 10) * sigma² * log (1 / eps)`, up to the factor
`(1 + rho10²) ^ (1 / 10)`. -/
lemma budget_le (q : LongTails.Setups.ZerothOrderStronglyConvexUndecicBias.Params)
    (i : Fin 1) (hq : LongTails.Setups.ZerothOrderStronglyConvexUndecicBias.spec.valid q) :
    (budget q i : ℝ)
      ≤ 10 * (q.base.d : ℝ)
        * (1 + 2 / mom q.base
            * Real.log (2 * (q.base.L / 2 * q.base.R ^ 2 + mu q.base / 4 * q.base.R ^ 2)
              / q.base.ε + 1))
        * (2 + 48 * (1 / (2 * q.base.L) + mom q.base ^ 2 / mu q.base) * (q.base.d : ℝ)
            * q.base.σ ^ 2 / (mom q.base * q.base.ε * bandwidth q ^ 2)) := by
  classical
  rcases hq.1 with ⟨hd, hL, hR, hσ, hμ, hε⟩
  have hmu : 0 < mu q.base := lt_min_iff.mpr ⟨hμ, hL⟩
  have hth : 0 < mom q.base := th_pos q.base.L (mu q.base) hL hmu
  have hn : (budget q i : ℝ)
      = (steps q.base : ℝ) * (10 * (q.base.d : ℝ) * (replicas q : ℝ)) := by
    have hsum : (budget q i : ℝ) =
        ∑ _k ∈ Finset.range (steps q.base), (roundSlots q.base.d (5 * replicas q) : ℝ) := by
      simp [budget]
    have hcard : (roundSlots q.base.d (5 * replicas q) : ℝ)
        = 10 * (q.base.d : ℝ) * (replicas q : ℝ) := by
      show (Fintype.card (Fin (5 * replicas q) × (Fin q.base.d × Bool)) : ℝ) = _
      rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
        Fintype.card_bool]
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      ring
    rw [hsum, Finset.sum_congr rfl (fun _ _ => hcard), Finset.sum_const, Finset.card_range]
    ring
  set X : ℝ := (2 / mom q.base)
    * Real.log (2 * (q.base.L / 2 * q.base.R ^ 2 + mu q.base / 4 * q.base.R ^ 2) / q.base.ε + 1)
    with hXdef
  set Y : ℝ := 48 * (1 / (2 * q.base.L) + mom q.base ^ 2 / mu q.base) * (q.base.d : ℝ)
    * q.base.σ ^ 2 / (mom q.base * q.base.ε * bandwidth q ^ 2) with hYdef
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
    refine mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) ?_) (Nat.cast_nonneg _)) (sq_nonneg _)
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
  have hd0 : (0 : ℝ) ≤ q.base.d := Nat.cast_nonneg _
  have hK0 : (0 : ℝ) ≤ steps q.base := Nat.cast_nonneg _
  have hM0 : (0 : ℝ) ≤ replicas q := Nat.cast_nonneg _
  rw [hn]
  have hKM : (steps q.base : ℝ) * (replicas q : ℝ) ≤ (1 + X) * (2 + Y) := by nlinarith
  nlinarith

end LongTails.Theorems.DecicStencilStronglyConvex

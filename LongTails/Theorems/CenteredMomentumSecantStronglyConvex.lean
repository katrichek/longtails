import LongTails.Setups.ZerothOrderStronglyConvex
import LongTails.Proofs.CenteredMomentumSpace
import LongTails.Proofs.CenteredMomentumTuning

namespace LongTails.Theorems.CenteredMomentumSecantStronglyConvex

open MeasureTheory ProbabilityTheory
open LongTails.Setups
open LongTails.Setups.ZerothOrderSmoothAndConvex
open scoped BigOperators
open scoped RealInnerProductSpace
open OracleTemplate SecantPolyak
open OracleTemplate.SecantPolyak.Accelerated OracleTemplate.SecantPolyak.Centered
open OracleTemplate.SecantPolyak.Scheduled

/-- Strong-convexity constant used for tuning: no larger than the smoothness constant. -/
noncomputable def mu (q : LongTails.Setups.ZerothOrderStronglyConvex.Params) : ℝ := min q.μ q.L

/-- Momentum parameter: of order `sqrt (μ / L)`, the classic acceleration scaling. -/
noncomputable def mom (q : LongTails.Setups.ZerothOrderStronglyConvex.Params) : ℝ := th q.L (mu q)

/-- Number of momentum rounds: of order `sqrt (L / μ) * log (1 / ε)`. -/
noncomputable def steps (q : LongTails.Setups.ZerothOrderStronglyConvex.Params) : ℕ := iters q.L (mu q) q.R q.ε

/-- Sampling radius of one two-sided coordinate difference. -/
noncomputable def bandwidth (q : LongTails.Setups.ZerothOrderStronglyConvex.Params) : ℝ := hband q.d q.L (mu q) q.ε

/-- Graded replicas averaged per coordinate: round `k` of the `steps q` rounds. -/
noncomputable def batches (q : LongTails.Setups.ZerothOrderStronglyConvex.Params) : ℕ → ℕ :=
  batchA q.d q.L (mu q) (sig q.L (mu q) q.σ) q.ε (steps q)

/-- Oracle budget: the exact number of zeroth-order calls made by the `steps q` momentum rounds. -/
noncomputable def budget :
    (let S := LongTails.Setups.ZerothOrderStronglyConvex.spec; S.Params → Fin S.numOracles → ℕ) :=
  fun q _ => ∑ k ∈ Finset.range (steps q), roundSlots q.d (batches q k)

theorem result : Convergence LongTails.Setups.ZerothOrderStronglyConvex.spec budget := by
  classical
  refine ⟨fun q =>
      if h : Nonempty (q.E ≃ₗᵢ[ℝ] Point q.d) then
        if hd : 0 < q.d then
          SecantPolyak.ofPoint h.some.symm (cmDescent (m := batches q) hd
            (Scheduled.graded_pos (noiseA q.d q.L (mu q) (sig q.L (mu q) q.σ) q.ε) (tauA q.L (mu q)) (steps q))
            q.L (mu q) (mom q) (bandwidth q) (h.some q.x0))
        else
          { State := q.E, initial := fun _ => q.x0, query := fun x => (0, x),
            update := fun x _ => x, output := id }
      else
        { State := q.E, initial := fun _ => q.x0, query := fun x => (0, x),
          update := fun x _ => x, output := id },
    ?_, fun _ _ => trivial⟩
  intro q hq f O ho
  rcases hq with ⟨hd, hL, hR, hσ, hμ, hε⟩
  obtain ⟨hbase, xstar, hmin, hdist, hsc⟩ := ho
  obtain ⟨he, g, p, P, hind, hmarg, hO, hconv, hgr, hlip, _, hgm, hgi, hmean, hgsq, hvar⟩ := hbase
  subst hO
  set e : q.E ≃ₗᵢ[ℝ] Point q.d := he.some
  set mub : ℝ := mu q with hmubdef
  have hmu : 0 < mub := lt_min_iff.mpr ⟨hμ, hL⟩
  have hmuL : mub ≤ q.L := min_le_right _ _
  have hscmu : ∀ x y, f x + ⟪gradient f x, y - x⟫ + mub / 2 * ‖y - x‖ ^ 2 ≤ f y := by
    intro x y
    have h1 : mub / 2 * ‖y - x‖ ^ 2 ≤ q.μ / 2 * ‖y - x‖ ^ 2 := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have : mub ≤ q.μ := min_le_left _ _
      linarith
    linarith [hsc x y]
  have hth0 : 0 < mom q := th_pos q.L mub hL hmu
  have hth1 : mom q ≤ 1 := th_le_one q.L mub
  have hthL : 16 * q.L * mom q ^ 2 ≤ mub := th_constraint q.L mub hL hmu
  have hh0 : 0 < bandwidth q := by
    show 0 < hband q.d q.L mub q.ε
    unfold hband
    refine Real.sqrt_pos.mpr (div_pos (mul_pos hε (by linarith [th_pos q.L mub hL hmu])) ?_)
    show 0 < 2 * C0 q.L mub * (q.d : ℝ) * q.L ^ 2
    have : 0 < C0 q.L mub := C0_pos q.L mub hL hmu
    positivity
  have hmM : ∀ k, batches q k ≤ batches q (steps q - 1) := by
    intro k
    by_cases hk : k ≤ steps q - 1
    · exact Scheduled.graded_le_last (noiseA q.d q.L (mu q) (sig q.L (mu q) q.σ) q.ε) (tauA q.L (mu q))
        (le_of_lt (noiseA_pos q.d q.L (mu q) (sig q.L (mu q) q.σ) q.ε hL hmu hε))
        (le_of_lt (tauA_pos q.L (mu q) hL hmu)) (tauA_le_one q.L (mu q) hL hmu) (steps q) k hk
    · show Scheduled.graded (noiseA q.d q.L (mu q) (sig q.L (mu q) q.σ) q.ε) (tauA q.L (mu q)) (steps q) k
        ≤ Scheduled.graded (noiseA q.d q.L (mu q) (sig q.L (mu q) q.σ) q.ε) (tauA q.L (mu q)) (steps q)
          (steps q - 1)
      simp [Scheduled.graded, show steps q - 1 - k = 0 by omega]
  have hbound : (1 - mom q / 2) ^ steps q * (q.L / 2 * q.R ^ 2 + mub / 4 * q.R ^ 2)
      + ∑ k ∈ Finset.range (steps q), (1 - mom q / 2) ^ (steps q - 1 - k)
          * (2 * (3 / (4 * q.L) + 2 * mom q / mub) * ((q.d : ℝ) * (q.L * bandwidth q / 2) ^ 2)
            + 4 * (1 / (2 * q.L) + mom q ^ 2 / mub) * (q.d : ℝ) * q.σ ^ 2
              / (bandwidth q ^ 2 * (batches q k))) ≤ q.ε :=
    cm_tuning_graded q.d hd q.L mub q.σ q.R q.ε hL hmu hσ hR hε
  have hmain := cm_space_accuracy (E := q.E) (d := q.d) (hd := hd) (e := e) (f := f)
    (L := q.L) (R := q.R) (σ := q.σ) (μ := mub) (ε := q.ε) (θ := mom q) (h := bandwidth q)
    (x0 := q.x0) (xstar := xstar) (Ω := q.Ω) (g := g) (K := steps q)
    (M := batches q (steps q - 1))
    hconv hgr hlip hL hR hσ hmu hmuL hε hth0 hth1 hthL hh0 hscmu hmin hdist
    hgm hind hmarg hgi hmean hgsq hvar
    (Scheduled.graded_pos (noiseA q.d q.L (mu q) (sig q.L (mu q) q.σ) q.ε) (tauA q.L (mu q)) (steps q))
    hmM hbound
  dsimp only
  have hEq : (if h : Nonempty (q.E ≃ₗᵢ[ℝ] Point q.d) then
        if hd' : 0 < q.d then
          SecantPolyak.ofPoint h.some.symm (cmDescent (m := batches q) hd'
            (Scheduled.graded_pos (noiseA q.d q.L (mu q) (sig q.L (mu q) q.σ) q.ε) (tauA q.L (mu q)) (steps q))
            q.L (mu q) (mom q) (bandwidth q) (h.some q.x0))
        else
          { State := q.E, initial := fun _ => q.x0, query := fun x => (0, x),
            update := fun x _ => x, output := id }
      else
        { State := q.E, initial := fun _ => q.x0, query := fun x => (0, x),
          update := fun x _ => x, output := id })
      = SecantPolyak.ofPoint e.symm
        (cmDescent (m := batches q) hd
          (Scheduled.graded_pos (noiseA q.d q.L (mu q) (sig q.L (mu q) q.σ) q.ε) (tauA q.L (mu q)) (steps q))
          q.L (mu q) (mom q) (bandwidth q) (e q.x0)) := by
    rw [dite_eq_left he, dite_eq_left hd]
  have htransport : ∀ (A A' : Algorithm q.E ℝ q.E), A = A' →
      LongTails.Setups.ZerothOrderStronglyConvex.spec.successful q f
        (fun seed : A.Seed × ((k : ℕ) → q.Ω) =>
          execute { Seed := fun _ => q.Ω, law := P, answer := fun _ (_, x) ω => g x ω } A
            (budget q) seed.1 seed.2)
        ⟨(A.law : Measure _).prod (P : Measure _), inferInstance⟩ →
      LongTails.Setups.ZerothOrderStronglyConvex.spec.successful q f
        (fun seed : A'.Seed × ((k : ℕ) → q.Ω) =>
          execute { Seed := fun _ => q.Ω, law := P, answer := fun _ (_, x) ω => g x ω } A'
            (budget q) seed.1 seed.2)
        ⟨(A'.law : Measure _).prod (P : Measure _), inferInstance⟩ := by
    intro A A' hAA h
    cases hAA
    exact h
  exact htransport _ _ hEq.symm ⟨hmain.1, xstar, hmin, hmain.2.1, hmain.2.2⟩

end LongTails.Theorems.CenteredMomentumSecantStronglyConvex

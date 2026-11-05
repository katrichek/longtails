import LongTails.Setups.ZerothOrderPolyakConvex
import LongTails.Proofs.SecantPolyakScheduled
import LongTails.Proofs.SecantPolyakScheduledSpace

namespace LongTails.Theorems.ScheduledSecantPolyakConvex

open MeasureTheory ProbabilityTheory
open LongTails.Setups
open LongTails.Setups.ZerothOrderSmoothAndConvex
open scoped BigOperators
open OracleTemplate SecantPolyak
open OracleTemplate.SecantPolyak.Scheduled

/-- Logarithmic contraction factor: the number of steps grows only like `L/μ`. -/
noncomputable def contraction (q : LongTails.Setups.ZerothOrderPolyakConvex.Params) : ℝ :=
  1 + Real.log (1 + 2 * q.L * q.R ^ 2 / q.ε)

/-- Gradient steps of the scheduled secant descent. -/
noncomputable def steps (q : LongTails.Setups.ZerothOrderPolyakConvex.Params) : ℕ :=
  ⌈contraction q * q.L / min q.μ q.L⌉₊

/-- Sampling radius of one two-sided coordinate difference. -/
noncomputable def bandwidth (q : LongTails.Setups.ZerothOrderPolyakConvex.Params) : ℝ :=
  Real.sqrt (min q.μ q.L * q.ε / (4 * (q.d : ℝ) * q.L ^ 2))

/-- Graded batch widths: round `k` averages `schedM q k` independent replicas per coordinate. -/
noncomputable def schedM (q : LongTails.Setups.ZerothOrderPolyakConvex.Params) : ℕ → ℕ :=
  OracleTemplate.SecantPolyak.Scheduled.graded
    (OracleTemplate.SecantPolyak.Scheduled.noiseScale q.d q.σ q.L (bandwidth q) (min q.μ q.L) q.ε)
    (OracleTemplate.SecantPolyak.Scheduled.rat q.L (min q.μ q.L)) (steps q)

/-- Oracle budget: the exact number of zeroth-order calls made by the `steps q` graded rounds. -/
noncomputable def budget :
    (let S := LongTails.Setups.ZerothOrderPolyakConvex.spec; S.Params → Fin S.numOracles → ℕ) :=
  fun q _ => ∑ k ∈ Finset.range (steps q), roundSlots q.d (schedM q k)

theorem result : Convergence LongTails.Setups.ZerothOrderPolyakConvex.spec budget := by
  classical
  refine ⟨fun q =>
      if h : Nonempty (q.E ≃ₗᵢ[ℝ] Point q.d) then
        if hd : 0 < q.d then
          SecantPolyak.ofPoint h.some.symm (Scheduled.schedDescent (m := schedM q) hd
            (fun k => Scheduled.graded_pos (noiseScale q.d q.σ q.L (bandwidth q) (min q.μ q.L) q.ε)
              (rat q.L (min q.μ q.L)) (steps q) k) q.L (bandwidth q) (h.some q.x0))
        else
          { State := q.E, initial := fun _ => q.x0, query := fun x => (0, x),
            update := fun x _ => x, output := id }
      else
        { State := q.E, initial := fun _ => q.x0, query := fun x => (0, x),
          update := fun x _ => x, output := id },
    ?_, fun _ _ => trivial⟩
  intro q hq f O ho
  rcases hq with ⟨hd, hL, hR, hσ, hμ, hε⟩
  obtain ⟨hbase, xstar, hmin, hdist, hpl⟩ := ho
  obtain ⟨he, g, p, P, hind, hmarg, hO, hconv, hgr, hlip, _, hgm, hgi, hmean, hgsq, hvar⟩ := hbase
  subst hO
  set e : q.E ≃ₗᵢ[ℝ] Point q.d := he.some
  set mu : ℝ := min q.μ q.L
  have hmu : 0 < mu := lt_min_iff.mpr ⟨hμ, hL⟩
  have hmuL : mu ≤ q.L := min_le_right _ _
  have hplmu : ∀ x, 2 * mu * (f x - f xstar) ≤ ‖gradient f x‖ ^ 2 := by
    intro x
    have h1 : 0 ≤ f x - f xstar := sub_nonneg.mpr (hmin (Set.mem_univ x))
    have h2 : (2 : ℝ) * mu ≤ 2 * q.μ :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)
    refine le_trans (mul_le_mul_of_nonneg_right h2 h1) (hpl x)
  have hlog : (0 : ℝ) ≤ Real.log (1 + 2 * q.L * q.R ^ 2 / q.ε) := by
    refine Real.log_nonneg ?_
    have hz : 0 ≤ 2 * q.L * q.R ^ 2 / q.ε := by positivity
    linarith
  have hge1 : (1 : ℝ) ≤ contraction q := le_add_of_nonneg_right hlog
  have hK0 : 0 < steps q :=
    Nat.ceil_pos.mpr (div_pos (mul_pos (by linarith) hL) hmu)
  have hLambda : (steps q : ℝ) * (mu / q.L) ≥ contraction q := by
    have hc : (contraction q * q.L / mu) * (mu / q.L) = contraction q := by field_simp
    rw [← hc]
    exact mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity)
  have hmMsched : ∀ k, schedM q k ≤ schedM q (steps q - 1) := by
    intro k
    by_cases hk : k ≤ steps q - 1
    · exact Scheduled.graded_le_last
        (noiseScale q.d q.σ q.L (bandwidth q) mu q.ε) (rat q.L mu)
        ((Scheduled.noiseScale_pos q.d q.σ q.L (bandwidth q) mu q.ε hL
            (Real.sqrt_pos.mpr (div_pos (mul_pos hmu hε) (by positivity))) hmu hε).le)
        (Scheduled.rat_pos hL hmu hmuL).le (Scheduled.rat_lt_one hL hmu).le (steps q) k hk
    · show graded _ _ (steps q) k ≤ graded _ _ (steps q) (steps q - 1)
      simp [Scheduled.graded, show steps q - 1 - k = 0 by omega]
  have hbound : Scheduled.rho q.L mu ^ (steps q) * (q.L / 2 * q.R ^ 2)
      + ∑ n ∈ Finset.range (steps q), Scheduled.rho q.L mu ^ (steps q - 1 - n)
          * ((1 / q.L) * SecantPolyak.batchError q.d (schedM q n) q.σ q.L (bandwidth q)) ≤ q.ε :=
    Scheduled.tuning_bound q.d q.σ q.L q.R (bandwidth q) mu q.ε hd hL hR hmu hmuL hε
      (by simpa [contraction] using hLambda) rfl
  have hmain := Scheduled.sched_space_accuracy (E := q.E) (d := q.d) (hd := hd) (e := e) (f := f)
    (L := q.L) (R := q.R) (σ := q.σ) (μ := mu) (ε := q.ε) (x0 := q.x0) (xstar := xstar)
    (Ω := q.Ω) (g := g) (K := steps q) (M := schedM q (steps q - 1)) hconv hgr hlip hL hR hσ hmu hmuL hε hmin
    hdist
    hplmu hgm hind hmarg hgi hmean hgsq hvar (fun k => Scheduled.graded_pos (noiseScale q.d q.σ q.L (bandwidth q) (min q.μ q.L) q.ε)
              (rat q.L (min q.μ q.L)) (steps q) k) hmMsched hbound
  dsimp only
  have hEq : (if h : Nonempty (q.E ≃ₗᵢ[ℝ] Point q.d) then
        if hd' : 0 < q.d then
          SecantPolyak.ofPoint h.some.symm (Scheduled.schedDescent (m := schedM q) hd'
            (fun k => Scheduled.graded_pos (noiseScale q.d q.σ q.L (bandwidth q) (min q.μ q.L) q.ε)
              (rat q.L (min q.μ q.L)) (steps q) k) q.L (bandwidth q) (h.some q.x0))
        else
          { State := q.E, initial := fun _ => q.x0, query := fun x => (0, x),
            update := fun x _ => x, output := id }
      else
        { State := q.E, initial := fun _ => q.x0, query := fun x => (0, x),
          update := fun x _ => x, output := id })
      = SecantPolyak.ofPoint e.symm
        (Scheduled.schedDescent (m := schedM q) hd (fun k => Scheduled.graded_pos (noiseScale q.d q.σ q.L (bandwidth q) (min q.μ q.L) q.ε)
              (rat q.L (min q.μ q.L)) (steps q) k) q.L (bandwidth q) (e q.x0)) := by
    rw [dite_eq_left he, dite_eq_left hd]
  have htransport : ∀ (A A' : Algorithm q.E ℝ q.E), A = A' →
      LongTails.Setups.ZerothOrderPolyakConvex.spec.successful q f
        (fun seed : A.Seed × ((k : ℕ) → q.Ω) =>
          execute { Seed := fun _ => q.Ω, law := P, answer := fun _ (_, x) ω => g x ω } A
            (budget q) seed.1 seed.2)
        ⟨(A.law : Measure _).prod (P : Measure _), inferInstance⟩ →
      LongTails.Setups.ZerothOrderPolyakConvex.spec.successful q f
        (fun seed : A'.Seed × ((k : ℕ) → q.Ω) =>
          execute { Seed := fun _ => q.Ω, law := P, answer := fun _ (_, x) ω => g x ω } A'
            (budget q) seed.1 seed.2)
        ⟨(A'.law : Measure _).prod (P : Measure _), inferInstance⟩ := by
    intro A A' hAA h
    cases hAA
    exact h
  exact htransport _ _ hEq.symm ⟨hmain.1, xstar, hmin, hmain.2.1, hmain.2.2⟩


end LongTails.Theorems.ScheduledSecantPolyakConvex

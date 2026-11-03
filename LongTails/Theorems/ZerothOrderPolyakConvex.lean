import LongTails.Setups.ZerothOrderPolyakConvex
import LongTails.Proofs.SecantPolyakSpace

namespace LongTails.Theorems.ZerothOrderPolyakConvex

open OracleTemplate MeasureTheory ProbabilityTheory
open LongTails.Setups
open LongTails.Setups.ZerothOrderSmoothAndConvex
open scoped BigOperators

/-- Logarithmic contraction factor of batched secant descent. -/
noncomputable def contraction (q : LongTails.Setups.ZerothOrderPolyakConvex.Params) : ℝ :=
  1 + Real.log (1 + 2 * q.L * q.R ^ 2 / q.ε)

/-- Gradient steps of batched secant descent. -/
noncomputable def steps (q : LongTails.Setups.ZerothOrderPolyakConvex.Params) : ℕ :=
  ⌈contraction q * q.L / min q.μ q.L⌉₊

/-- Independent replicas averaged inside one secant step. -/
noncomputable def replicas (q : LongTails.Setups.ZerothOrderPolyakConvex.Params) : ℕ :=
  1 + ⌈(8 * (steps q : ℝ) * (q.d : ℝ) * q.σ / q.ε) ^ 2⌉₊

/-- Sampling radius of one two-sided coordinate difference. -/
noncomputable def bandwidth (q : LongTails.Setups.ZerothOrderPolyakConvex.Params) : ℝ :=
  Real.sqrt (q.ε / (2 * (steps q : ℝ) * (q.d : ℝ) * q.L))

noncomputable def budget :
    (let S := LongTails.Setups.ZerothOrderPolyakConvex.spec; S.Params → Fin S.numOracles → ℕ) :=
  fun q _ => ⌈(1 + Real.log (1 + 2 * q.L * q.R ^ 2 / q.ε)) * q.L / min q.μ q.L⌉₊
    * (2 * q.d * (1 + ⌈(8 * ↑⌈(1 + Real.log (1 + 2 * q.L * q.R ^ 2 / q.ε)) * q.L /
      min q.μ q.L⌉₊ * (q.d : ℝ) * q.σ / q.ε) ^ 2⌉₊))

theorem result : Convergence LongTails.Setups.ZerothOrderPolyakConvex.spec budget := by
  classical
  refine ⟨fun q =>
      if h : Nonempty (q.E ≃ₗᵢ[ℝ] Point q.d) then
        if hd : 0 < q.d then
          SecantPolyak.ofPoint h.some.symm (SecantDescent.secantDescent (m := replicas q) hd
            (by simp only [replicas]; omega) q.L (bandwidth q) (h.some q.x0))
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
  have hm0 : 0 < replicas q := by simp only [replicas]; omega
  have hLambda : (steps q : ℝ) * (mu / q.L) ≥ contraction q := by
    have hc : (contraction q * q.L / mu) * (mu / q.L) = contraction q := by field_simp
    rw [← hc]
    exact mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity)
  have hnoise : (replicas q : ℝ) * q.ε ^ 2 ≥
      64 * (steps q : ℝ) ^ 2 * (q.d : ℝ) ^ 2 * q.σ ^ 2 := by
    have h1 : ((8 * (steps q : ℝ) * (q.d : ℝ) * q.σ / q.ε) ^ 2 : ℝ) ≤ (replicas q : ℝ) :=
      le_trans (Nat.le_ceil _) (by
        simp only [replicas, Nat.cast_add, Nat.cast_one]
        linarith)
    have h2 : (8 * (steps q : ℝ) * (q.d : ℝ) * q.σ / q.ε) ^ 2 * q.ε ^ 2
        = 64 * (steps q : ℝ) ^ 2 * (q.d : ℝ) ^ 2 * q.σ ^ 2 := by
      field_simp
      ring
    calc 64 * (steps q : ℝ) ^ 2 * (q.d : ℝ) ^ 2 * q.σ ^ 2
        = (8 * (steps q : ℝ) * (q.d : ℝ) * q.σ / q.ε) ^ 2 * q.ε ^ 2 := h2.symm
      _ ≤ (replicas q : ℝ) * q.ε ^ 2 := mul_le_mul_of_nonneg_right h1 (by positivity)
  have hbound : (1 - mu / q.L) ^ (steps q) * (q.L / 2 * q.R ^ 2)
      + (steps q : ℝ) * (1 / q.L)
          * SecantPolyak.batchError q.d (replicas q) q.σ q.L (bandwidth q) ≤ q.ε :=
    SecantPolyak.Tuning.tuning_bound hL hR hσ hmu hmuL hε hK0 hd hm0
      (by simpa [contraction] using hLambda) rfl hnoise
  have hmain := SecantPolyak.space_accuracy (E := q.E) (d := q.d) (hd := hd) (e := e) (f := f)
    (L := q.L) (R := q.R) (σ := q.σ) (μ := mu) (ε := q.ε) (x0 := q.x0) (xstar := xstar)
    (Ω := q.Ω) (g := g) (K := steps q) (m := replicas q) hconv hgr hlip hL hR hσ hmu hmuL hε hmin
    hdist
    hplmu hgm hind hmarg hgi hmean hgsq hvar hK0 hm0 hbound
  dsimp only
  have hEq : (if h : Nonempty (q.E ≃ₗᵢ[ℝ] Point q.d) then
        if hd' : 0 < q.d then
          SecantPolyak.ofPoint h.some.symm (SecantDescent.secantDescent (m := replicas q) hd'
            (by simp only [replicas]; omega) q.L (bandwidth q) (h.some q.x0))
        else
          { State := q.E, initial := fun _ => q.x0, query := fun x => (0, x),
            update := fun x _ => x, output := id }
      else
        { State := q.E, initial := fun _ => q.x0, query := fun x => (0, x),
          update := fun x _ => x, output := id })
      = SecantPolyak.ofPoint e.symm
        (SecantDescent.secantDescent (m := replicas q) hd hm0 q.L (bandwidth q) (e q.x0)) := by
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

end LongTails.Theorems.ZerothOrderPolyakConvex

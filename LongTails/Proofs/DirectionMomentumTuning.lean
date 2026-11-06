import LongTails.Proofs.AcceleratedSecantTuning
import LongTails.Proofs.CenteredMomentumTuning
import LongTails.Proofs.DirectionMomentumStep

set_option maxHeartbeats 2000000

namespace OracleTemplate.SecantPolyak.DirectionSampled

open OracleTemplate SecantPolyak.Accelerated SecantPolyak.Centered Scheduled
open scoped BigOperators

/-- Second-moment scale of one unit of the direction-sampled surrogate at bandwidth
`h ^ 2 = eps / (L * d)`, using `2 * G ^ 2 * h ^ 2 <= sigma ^ 2 * d`. -/
noncomputable def var (d : ℕ) (L σ ε : ℝ) : ℝ := σ ^ 2 * L * (d : ℝ) ^ 2 / (2 * ε)

/-- Graded batch widths of the direction-sampled schedule. -/
noncomputable def batchD (d : ℕ) (L μ σ ε : ℝ) (K n : ℕ) : ℕ :=
  Scheduled.graded (1 + 8 * cv L μ * var d L σ ε / (ε * th L μ)) (tauA L μ) K n

/-- The graded batches make the accumulated second-moment error fit into `ε / 2`, while the
momentum rounds contract the initial potential below `ε / 2`. -/
lemma dir_tuning (d : ℕ) (hd : 0 < d) (L μ σ R ε : ℝ)
    (hL : 0 < L) (hμ : 0 < μ) (_hσ : 0 ≤ σ) (_hR : 0 ≤ R) (hε : 0 < ε) :
    rhoA L μ ^ iters L μ R ε * (L / 2 * R ^ 2 + μ / 4 * R ^ 2)
        + ∑ k ∈ Finset.range (iters L μ R ε), rhoA L μ ^ (iters L μ R ε - 1 - k)
            * (cv L μ * (var d L σ ε / (batchD d L μ σ ε (iters L μ R ε) k))) ≤ ε := by
  classical
  have hth0 : 0 < th L μ := th_pos L μ hL hμ
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hh0 : 0 < th L μ / 2 := by linarith
  set A : ℝ := L / 2 * R ^ 2 + μ / 4 * R ^ 2 with hAdef
  set ρ : ℝ := rhoA L μ with hρdef
  set K : ℕ := iters L μ R ε with hKdef
  have hA0 : 0 ≤ A := by
    show 0 ≤ L / 2 * R ^ 2 + μ / 4 * R ^ 2
    positivity
  have hρ0 : 0 ≤ ρ := le_of_lt (rhoA_pos L μ hL hμ)
  have hρ1 : ρ < 1 := rhoA_lt_one L μ hL hμ
  have hinit : ρ ^ K * A ≤ ε / 2 := by
    have hK : (2 / th L μ) * Real.log (2 * A / ε + 1) ≤ (K : ℝ) := by
      rw [hKdef]
      exact_mod_cast Nat.le_ceil _
    have h3 : (th L μ / 2) * ((2 / th L μ) * Real.log (2 * A / ε + 1))
        = Real.log (2 * A / ε + 1) := by
      field_simp
    have h2 : Real.log (2 * A / ε + 1) ≤ (th L μ / 2) * (K : ℝ) := by
      rw [← h3]
      exact mul_le_mul_of_nonneg_left hK (le_of_lt hh0)
    have hp : 0 < 2 * A / ε + 1 := by positivity
    have h4 : Real.exp (-(th L μ / 2) * (K : ℝ)) ≤ 1 / (2 * A / ε + 1) := by
      have h5 : -(th L μ / 2) * (K : ℝ) ≤ -Real.log (2 * A / ε + 1) := by linarith
      calc Real.exp (-(th L μ / 2) * (K : ℝ)) ≤ Real.exp (-Real.log (2 * A / ε + 1)) :=
          Real.exp_le_exp.mpr h5
        _ = 1 / (2 * A / ε + 1) := by
          rw [Real.exp_neg, Real.exp_log hp]
          simp
    have h5 : ρ ^ K ≤ 1 / (2 * A / ε + 1) := le_trans (rho_pow_le L μ hL hμ K) h4
    have h6 : ρ ^ K * A ≤ A / (2 * A / ε + 1) := by
      calc ρ ^ K * A ≤ (1 / (2 * A / ε + 1)) * A := mul_le_mul_of_nonneg_right h5 hA0
        _ = A / (2 * A / ε + 1) := by field_simp
    have h7 : A / (2 * A / ε + 1) ≤ ε / 2 := by
      field_simp
      nlinarith [sq_nonneg ε]
    linarith
  have hcv0 : 0 ≤ cv L μ := cv_nonneg L μ hL hμ
  have hvar0 : 0 ≤ var d L σ ε := by
    show 0 ≤ σ ^ 2 * L * (d : ℝ) ^ 2 / (2 * ε)
    positivity
  have hX0 : 0 ≤ cv L μ * var d L σ ε := mul_nonneg hcv0 hvar0
  have hN0 : 0 < 1 + 8 * cv L μ * var d L σ ε / (ε * th L μ) := by positivity
  have hnoise : ∑ k ∈ Finset.range K,
      ρ ^ (K - 1 - k) * (cv L μ * (var d L σ ε / (batchD d L μ σ ε K k))) ≤ ε / 2 := by
    have hshape : ∑ k ∈ Finset.range K,
        ρ ^ (K - 1 - k) * (cv L μ * (var d L σ ε / (batchD d L μ σ ε K k)))
        = ∑ k ∈ Finset.range K,
          ρ ^ (K - 1 - k) * ((cv L μ * var d L σ ε) / (batchD d L μ σ ε K k)) := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [mul_div_assoc]
    rw [hshape]
    have h3 := graded_noise_sum (ρ := ρ) (τ := tauA L μ) hρ0 (rhoA_lt_tauA L μ hL hμ)
      (tauA_pos L μ hL hμ) (tauA_le_one L μ hL hμ)
      (1 + 8 * cv L μ * var d L σ ε / (ε * th L μ)) (cv L μ * var d L σ ε) hN0 hX0 K
    have h4 : 1 / (1 - ρ / tauA L μ) ≤ 4 / th L μ := ratio_inv_le L μ hL hμ
    have hzle : (8 * cv L μ * var d L σ ε / (ε * th L μ))
        / (1 + 8 * cv L μ * var d L σ ε / (ε * th L μ)) ≤ 1 :=
      (div_le_one hN0).mpr (by linarith)
    have h5 : cv L μ * var d L σ ε / (1 + 8 * cv L μ * var d L σ ε / (ε * th L μ))
        ≤ ε * th L μ / 8 := by
      calc cv L μ * var d L σ ε / (1 + 8 * cv L μ * var d L σ ε / (ε * th L μ))
          = (ε * th L μ / 8) * ((8 * cv L μ * var d L σ ε / (ε * th L μ))
              / (1 + 8 * cv L μ * var d L σ ε / (ε * th L μ))) := by
            field_simp
        _ ≤ (ε * th L μ / 8) * 1 := mul_le_mul_of_nonneg_left hzle (by positivity)
        _ = ε * th L μ / 8 := by ring
    have hden1 : 0 < 1 - ρ / tauA L μ := by
      have hlt := rhoA_lt_tauA L μ hL hμ
      have hτ := tauA_pos L μ hL hμ
      rw [sub_pos, div_lt_one hτ]
      simpa [hρdef] using hlt
    have h6 : (cv L μ * var d L σ ε) / (1 + 8 * cv L μ * var d L σ ε / (ε * th L μ))
        * (1 / (1 - ρ / tauA L μ)) ≤ ε / 2 := by
      have h7 := mul_le_mul h5 h4 (div_nonneg zero_le_one (le_of_lt hden1))
        (by positivity : (0 : ℝ) ≤ ε * th L μ / 8)
      have h8 : (ε * th L μ / 8) * (4 / th L μ) = ε / 2 := by
        field_simp
        ring
      linarith [h7, h8]
    exact le_trans h3 h6
  have hgoal : ρ ^ K * A + ∑ k ∈ Finset.range K,
      ρ ^ (K - 1 - k) * (cv L μ * (var d L σ ε / (batchD d L μ σ ε K k))) ≤ ε := by
    linarith
  exact hgoal

end OracleTemplate.SecantPolyak.DirectionSampled
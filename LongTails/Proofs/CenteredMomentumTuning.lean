import LongTails.Proofs.AcceleratedSecantTuning

set_option maxHeartbeats 2000000

/-!
Tuning of the mean-anchored momentum schedule. The centered round pays the sharp variance
coefficient `cv = 1 / (2 * L) + θ ^ 2 / μ` for the noise and the Young coefficient `C0` for the
bias, so the graded batches only have to cover the effective noise level `sig`, which is
`σ ^ 2 * cv / (2 * C0)` in variance units.
-/

namespace OracleTemplate.SecantPolyak.Centered

open OracleTemplate OracleTemplate.SecantPolyak.Accelerated InexactGradient Scheduled
open LongTails.Setups.ZerothOrderSmoothAndConvex
open scoped BigOperators RealInnerProductSpace

/-- Sharp variance coefficient of one centered momentum round. -/
noncomputable def cv (L μ : ℝ) : ℝ := 1 / (2 * L) + th L μ ^ 2 / μ

/-- Effective noise level of the centered schedule. -/
noncomputable def sig (L μ σ : ℝ) : ℝ := σ * Real.sqrt (cv L μ / (2 * C0 L μ))

lemma cv_nonneg (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ) : 0 ≤ cv L μ := by
  show 0 ≤ 1 / (2 * L) + th L μ ^ 2 / μ
  positivity

/-- The effective noise level is nonnegative and its square is the rescaled variance. -/
lemma sig_sq (L μ σ : ℝ) (hL : 0 < L) (hμ : 0 < μ) (hσ : 0 ≤ σ) :
    0 ≤ sig L μ σ ∧ sig L μ σ ^ 2 = σ ^ 2 * (cv L μ / (2 * C0 L μ)) := by
  have hcv : 0 ≤ cv L μ := cv_nonneg L μ hL hμ
  refine ⟨mul_nonneg hσ (Real.sqrt_nonneg _), ?_⟩
  have h2c0 : 0 < 2 * C0 L μ := mul_pos two_pos (C0_pos L μ hL hμ)
  show (σ * Real.sqrt (cv L μ / (2 * C0 L μ))) ^ 2 = _
  rw [mul_pow, Real.sq_sqrt (div_nonneg hcv (le_of_lt h2c0))]

/-- Graded tuning of the centered schedule: the same bandwidth and the same number of rounds, with
graded batches sized for the effective noise level, make the centered error sum fit into `ε`. -/
lemma cm_tuning_graded (d : ℕ) (hd : 0 < d) (L μ σ R ε : ℝ)
    (hL : 0 < L) (hμ : 0 < μ) (hσ : 0 ≤ σ) (hR : 0 ≤ R) (hε : 0 < ε) :
    rhoA L μ ^ iters L μ R ε * (L / 2 * R ^ 2 + μ / 4 * R ^ 2)
        + ∑ k ∈ Finset.range (iters L μ R ε), rhoA L μ ^ (iters L μ R ε - 1 - k)
            * (C0 L μ * ((d : ℝ) * (L * hband d L μ ε / 2) ^ 2)
              + 4 * cv L μ * (d : ℝ) * σ ^ 2
                / (hband d L μ ε ^ 2 * (batchA d L μ (sig L μ σ) ε (iters L μ R ε) k))) ≤ ε := by
  classical
  have hC0 : 0 < C0 L μ := C0_pos L μ hL hμ
  have hcv : 0 ≤ cv L μ := cv_nonneg L μ hL hμ
  obtain ⟨hs0, hsq⟩ := sig_sq L μ σ hL hμ hσ
  have hb := accel_tuning_graded d hd L μ (sig L μ σ) R ε hL hμ hs0 hR hε
  have hρ0 : 0 ≤ rhoA L μ := le_of_lt (rhoA_pos L μ hL hμ)
  have hX0 : 0 ≤ C0 L μ * ((d : ℝ) * (L * hband d L μ ε / 2) ^ 2) := by positivity
  have hnum : 4 * cv L μ * (d : ℝ) * σ ^ 2 = C0 L μ * (8 * (d : ℝ) * sig L μ σ ^ 2) := by
    rw [hsq]
    field_simp
    ring
  have hnoise : ∀ n : ℕ, 4 * cv L μ * (d : ℝ) * σ ^ 2
      / (hband d L μ ε ^ 2 * (batchA d L μ (sig L μ σ) ε (iters L μ R ε) n))
      = C0 L μ * (8 * (d : ℝ) * sig L μ σ ^ 2
        / (hband d L μ ε ^ 2 * (batchA d L μ (sig L μ σ) ε (iters L μ R ε) n))) := by
    intro n
    rw [hnum, mul_div_assoc]
  have hsum : ∑ k ∈ Finset.range (iters L μ R ε),
      rhoA L μ ^ (iters L μ R ε - 1 - k)
        * (C0 L μ * ((d : ℝ) * (L * hband d L μ ε / 2) ^ 2)
          + 4 * cv L μ * (d : ℝ) * σ ^ 2
            / (hband d L μ ε ^ 2 * (batchA d L μ (sig L μ σ) ε (iters L μ R ε) k)))
      ≤ ∑ k ∈ Finset.range (iters L μ R ε), rhoA L μ ^ (iters L μ R ε - 1 - k)
          * (C0 L μ * (8 * (d : ℝ) * sig L μ σ ^ 2
              / (hband d L μ ε ^ 2 * (batchA d L μ (sig L μ σ) ε (iters L μ R ε) k))
            + 2 * ((d : ℝ) * (L * hband d L μ ε / 2) ^ 2))) := by
    refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_
      (pow_nonneg hρ0 (iters L μ R ε - 1 - k))
    rw [hnoise k, mul_add]
    linarith
  have hgoal := add_le_add_left hsum (rhoA L μ ^ iters L μ R ε * (L / 2 * R ^ 2 + μ / 4 * R ^ 2))
  linarith

end OracleTemplate.SecantPolyak.Centered

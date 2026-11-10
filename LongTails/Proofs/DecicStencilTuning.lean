import LongTails.Proofs.CentralStencilTuning

set_option maxHeartbeats 2000000

/-!
Tuning of the ten-point (Richardson) coordinate stencil inside the damped anchored momentum
schedule. The squared ten-point bias is `d * (rho10 * h ^ 10) ^ 2`, so the bandwidth is a twentieth
root of `epsilon`, the replica count is of order `d / (h ^ 2 * epsilon)`, and the oracle budget is
whose dominant small-epsilon term is of order `d * (d / (mu * epsilon)) ^ (11 / 10) * sigma ^ 2 * log (1 / epsilon)`, up to the
factor `(1 + rho10 ^ 2) ^ (1 / 10)`, as `budget_le` states with exact constants. The
ten-point bandwidth is a twentieth root, the four-point bandwidth an eighth root, the central
bandwidth `chband` a fourth root because the symmetric difference has bias `rho * h ^ 2`, and the
secant bandwidth only a square root because the one-sided difference has bias `L * h / 2`.
-/

namespace OracleTemplate.SecantPolyak.DecicStencil

open OracleTemplate OracleTemplate.SecantPolyak.Accelerated InexactGradient Scheduled
open OracleTemplate.SecantPolyak.CentralStencil
open scoped BigOperators RealInnerProductSpace

/-- Ten-point-stencil bandwidth: the twentieth root balancing the squared ten-point bias against
the geometric sum of the momentum contractions. -/
noncomputable def dxhband (d : ℕ) (L μ ε ρ10 : ℝ) : ℝ :=
  (ε * th L μ / (8 * C0 L μ * (d : ℝ) * (1 + ρ10 ^ 2))) ^ (1 / 20 : ℝ)

/-- Replicas of the ten-point stencil averaged per coordinate in every round. The five replica
bands of one replica probe bandwidth `h`, `2 * h`, `3 * h`, `4 * h` and `5 * h`. -/
noncomputable def dxbatch (d : ℕ) (L μ σ ε ρ10 : ℝ) : ℕ :=
  ⌈48 * cvc L μ * (d : ℝ) * σ ^ 2 / (th L μ * ε * dxhband d L μ ε ρ10 ^ 2)⌉₊ + 1

lemma dxden_pos {d : ℕ} (hd : 0 < d) (L μ ρ10 : ℝ) (hL : 0 < L) (hμ : 0 < μ) :
    0 < 8 * C0 L μ * (d : ℝ) * (1 + ρ10 ^ 2) := by
  have hC0 : 0 < C0 L μ := C0_pos L μ hL hμ
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hq : 0 < (1 : ℝ) + ρ10 ^ 2 := by nlinarith [sq_nonneg ρ10]
  exact mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 8) hC0) hd') hq

lemma dxhband_pos {d : ℕ} (hd : 0 < d) (L μ ε ρ10 : ℝ) (hL : 0 < L) (hμ : 0 < μ) (hε : 0 < ε) :
    0 < dxhband d L μ ε ρ10 :=
  Real.rpow_pos_of_pos
    (div_pos (mul_pos hε (th_pos L μ hL hμ)) (dxden_pos hd L μ ρ10 hL hμ)) (1 / 20 : ℝ)

/-- The twentieth power of the bandwidth is the balancing quantity. -/
lemma dxhband_twentieth {d : ℕ} (hd : 0 < d) (L μ ε ρ10 : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hε : 0 < ε) :
    dxhband d L μ ε ρ10 ^ 20 = ε * th L μ / (8 * C0 L μ * (d : ℝ) * (1 + ρ10 ^ 2)) := by
  set X : ℝ := ε * th L μ / (8 * C0 L μ * (d : ℝ) * (1 + ρ10 ^ 2)) with hXdef
  have hX0 : 0 ≤ X := by
    rw [hXdef]
    refine div_nonneg (mul_nonneg hε.le (le_of_lt (th_pos L μ hL hμ)))
      (le_of_lt (dxden_pos hd L μ ρ10 hL hμ))
  calc dxhband d L μ ε ρ10 ^ 20 = X ^ ((1 / 20 : ℝ) * (20 : ℕ)) :=
      (Real.rpow_mul_natCast hX0 (1 / 20 : ℝ) 20).symm
    _ = X ^ (1 : ℝ) := by norm_num
    _ = X := Real.rpow_one X
    _ = ε * th L μ / (8 * C0 L μ * (d : ℝ) * (1 + ρ10 ^ 2)) := hXdef.symm

/-- The replica count covers the noise of one ten-point round. -/
lemma dxbatch_ge {d : ℕ} (_hd : 0 < d) (L μ σ ε ρ10 : ℝ) (_hL : 0 < L) (_hμ : 0 < μ)
    (_hε : 0 < ε) :
    (dxbatch d L μ σ ε ρ10 : ℝ)
      ≥ 48 * cvc L μ * (d : ℝ) * σ ^ 2 / (th L μ * ε * dxhband d L μ ε ρ10 ^ 2) := by
  set X : ℝ := 48 * cvc L μ * (d : ℝ) * σ ^ 2 / (th L μ * ε * dxhband d L μ ε ρ10 ^ 2) with hXdef
  have h1 : X ≤ (⌈X⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : (⌈X⌉₊ : ℝ) ≤ (dxbatch d L μ σ ε ρ10 : ℝ) := Nat.cast_le.mpr (Nat.le_succ _)
  linarith

/-- The ten-point tuning inequality: the contracted initial gap, the summed squared ten-point
bias and the summed centered noise of the quintupled batch fit into `epsilon`. -/
lemma dx_tuning (d : ℕ) (hd : 0 < d) (L μ σ R ε ρ10 : ℝ)
    (hL : 0 < L) (hμ : 0 < μ) (_hμL : μ ≤ L) (_hσ : 0 ≤ σ) (_hR : 0 ≤ R) (hε : 0 < ε)
    (_hρ : 0 ≤ ρ10) :
    rhoA L μ ^ iters L μ R ε * (L / 2 * R ^ 2 + μ / 4 * R ^ 2)
        + ∑ k ∈ Finset.range (iters L μ R ε), rhoA L μ ^ (iters L μ R ε - 1 - k)
            * (C0 L μ * ((d : ℝ) * (ρ10 * dxhband d L μ ε ρ10 ^ 10) ^ 2)
              + cvc L μ * (6 * ((d : ℝ) * σ ^ 2
                / (dxhband d L μ ε ρ10 ^ 2 * (dxbatch d L μ σ ε ρ10 : ℝ))))) ≤ ε := by
  classical
  have hth : 0 < th L μ := th_pos L μ hL hμ
  have hC0 : 0 < C0 L μ := C0_pos L μ hL hμ
  have hρ0 : 0 ≤ rhoA L μ := le_of_lt (rhoA_pos L μ hL hμ)
  have hK : rhoA L μ ^ iters L μ R ε * (L / 2 * R ^ 2 + μ / 4 * R ^ 2) ≤ ε / 2 := by
    set A := L / 2 * R ^ 2 + μ / 4 * R ^ 2 with hAdef
    have hA0 : 0 ≤ A := by positivity
    by_cases hAz : A = 0
    · rw [hAz, mul_zero]
      linarith
    have hAp : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hAz)
    have hceil : (2 / th L μ) * Real.log (2 * A / ε + 1) ≤ (iters L μ R ε : ℝ) := by
      have h2 : (iters L μ R ε : ℝ) = (⌈(2 / th L μ) * Real.log (2 * A / ε + 1)⌉₊ : ℝ) := rfl
      rw [h2]
      exact Nat.le_ceil _
    have hx : (th L μ / 2) * (iters L μ R ε : ℝ) ≥ Real.log (2 * A / ε) := by
      have h2 : (th L μ / 2) * ((2 / th L μ) * Real.log (2 * A / ε + 1))
          = Real.log (2 * A / ε + 1) := by
        field_simp
      have h3 : Real.log (2 * A / ε + 1) ≥ Real.log (2 * A / ε) :=
        Real.log_le_log (by positivity) (by linarith)
      calc (th L μ / 2) * (iters L μ R ε : ℝ)
          ≥ (th L μ / 2) * ((2 / th L μ) * Real.log (2 * A / ε + 1)) :=
            mul_le_mul_of_nonneg_left hceil (by positivity)
        _ = Real.log (2 * A / ε + 1) := h2
        _ ≥ Real.log (2 * A / ε) := h3
    have hexp : Real.exp (-(th L μ / 2) * (iters L μ R ε : ℝ)) ≤ ε / (2 * A) := by
      calc Real.exp (-(th L μ / 2) * (iters L μ R ε : ℝ))
          ≤ Real.exp (-(Real.log (2 * A / ε))) :=
            Real.exp_le_exp.mpr (by linarith)
        _ = (2 * A / ε)⁻¹ := by rw [Real.exp_neg, Real.exp_log (by positivity)]
        _ = ε / (2 * A) := by field_simp
    calc rhoA L μ ^ iters L μ R ε * A
        ≤ Real.exp (-(th L μ / 2) * (iters L μ R ε : ℝ)) * A :=
          mul_le_mul_of_nonneg_right (rho_pow_le L μ hL hμ (iters L μ R ε)) hA0
      _ ≤ (ε / (2 * A)) * A := mul_le_mul_of_nonneg_right hexp hA0
      _ = ε / 2 := by field_simp [hAz]
  have hsumc : ∑ k ∈ Finset.range (iters L μ R ε), rhoA L μ ^ (iters L μ R ε - 1 - k)
      ≤ 1 / (th L μ / 2) := by
    have h1 := sum_rho_shift hρ0 (rhoA_lt_one L μ hL hμ) (iters L μ R ε)
    rw [one_sub_rhoA] at h1
    exact h1
  have hh : 0 < dxhband d L μ ε ρ10 := dxhband_pos hd L μ ε ρ10 hL hμ hε
  have h20 : dxhband d L μ ε ρ10 ^ 20
      = ε * th L μ / (8 * C0 L μ * (d : ℝ) * (1 + ρ10 ^ 2)) :=
    dxhband_twentieth hd L μ ε ρ10 hL hμ hε
  have hbiasb : (1 / (th L μ / 2)) * (C0 L μ * ((d : ℝ) * (ρ10 * dxhband d L μ ε ρ10 ^ 10) ^ 2))
      ≤ ε / 4 := by
    have hbexpr : C0 L μ * ((d : ℝ) * (ρ10 * dxhband d L μ ε ρ10 ^ 10) ^ 2)
        = C0 L μ * (d : ℝ) * ρ10 ^ 2 * dxhband d L μ ε ρ10 ^ 20 := by ring
    rw [hbexpr, h20]
    have hd0 : (0 : ℝ) < d := Nat.cast_pos.mpr hd
    have hρ2 : ρ10 ^ 2 ≤ 1 + ρ10 ^ 2 := by linarith [sq_nonneg ρ10]
    have hw : 0 ≤ C0 L μ * (d : ℝ) * (ε * th L μ) * 4 := by positivity
    have hle : (ρ10 ^ 2) * (C0 L μ * (d : ℝ) * (ε * th L μ) * 4)
        ≤ (1 + ρ10 ^ 2) * (C0 L μ * (d : ℝ) * (ε * th L μ) * 4) :=
      mul_le_mul_of_nonneg_right hρ2 hw
    have h1 : (1 / (th L μ / 2)) * (C0 L μ * (d : ℝ) * ρ10 ^ 2
            * (ε * th L μ / (8 * C0 L μ * (d : ℝ) * (1 + ρ10 ^ 2))))
        = C0 L μ * (d : ℝ) * ρ10 ^ 2 * (ε * th L μ)
            / ((th L μ / 2) * (8 * C0 L μ * (d : ℝ) * (1 + ρ10 ^ 2))) := by
      field_simp
    rw [h1]
    refine (div_le_div_iff₀
      (mul_pos (by positivity) (dxden_pos hd L μ ρ10 hL hμ)) (by norm_num : (0 : ℝ) < 4)).mpr ?_
    have he1 : C0 L μ * (d : ℝ) * ρ10 ^ 2 * (ε * th L μ) * 4
        = (ρ10 ^ 2) * (C0 L μ * (d : ℝ) * (ε * th L μ) * 4) := by ring
    have he2 : ε * ((th L μ / 2) * (8 * C0 L μ * (d : ℝ) * (1 + ρ10 ^ 2)))
        = (1 + ρ10 ^ 2) * (C0 L μ * (d : ℝ) * (ε * th L μ) * 4) := by ring
    nlinarith [hle, he1, he2]
  have hm : (dxbatch d L μ σ ε ρ10 : ℝ)
      ≥ 48 * cvc L μ * (d : ℝ) * σ ^ 2 / (th L μ * ε * dxhband d L μ ε ρ10 ^ 2) :=
    dxbatch_ge hd L μ σ ε ρ10 hL hμ hε
  have hm0 : (0 : ℝ) < dxbatch d L μ σ ε ρ10 :=
    Nat.cast_pos.mpr (Nat.succ_pos _)
  have hmul : (dxbatch d L μ σ ε ρ10 : ℝ) * (th L μ * ε * dxhband d L μ ε ρ10 ^ 2)
      ≥ 48 * cvc L μ * (d : ℝ) * σ ^ 2 := by
    have ht0 : 0 < th L μ * ε * dxhband d L μ ε ρ10 ^ 2 := by positivity
    calc (dxbatch d L μ σ ε ρ10 : ℝ) * (th L μ * ε * dxhband d L μ ε ρ10 ^ 2)
        ≥ (48 * cvc L μ * (d : ℝ) * σ ^ 2 / (th L μ * ε * dxhband d L μ ε ρ10 ^ 2))
            * (th L μ * ε * dxhband d L μ ε ρ10 ^ 2) :=
          mul_le_mul_of_nonneg_right hm (le_of_lt ht0)
      _ = 48 * cvc L μ * (d : ℝ) * σ ^ 2 := by field_simp
  have hnoiseb : (1 / (th L μ / 2))
      * (cvc L μ * (6 * ((d : ℝ) * σ ^ 2
        / (dxhband d L μ ε ρ10 ^ 2 * (dxbatch d L μ σ ε ρ10 : ℝ))))) ≤ ε / 4 := by
    have h2 : (1 / (th L μ / 2))
        * (cvc L μ * (6 * ((d : ℝ) * σ ^ 2
            / (dxhband d L μ ε ρ10 ^ 2 * (dxbatch d L μ σ ε ρ10 : ℝ)))))
        = 12 * cvc L μ * (d : ℝ) * σ ^ 2
            / (th L μ * dxhband d L μ ε ρ10 ^ 2 * (dxbatch d L μ σ ε ρ10 : ℝ)) := by
      field_simp
      ring
    rw [h2]
    have hp : 0 < th L μ * dxhband d L μ ε ρ10 ^ 2 * (dxbatch d L μ σ ε ρ10 : ℝ) := by
      refine mul_pos (mul_pos hth (pow_pos hh 2)) hm0
    refine (div_le_iff₀ hp).mpr ?_
    have h3 : (ε / 4) * (th L μ * dxhband d L μ ε ρ10 ^ 2 * (dxbatch d L μ σ ε ρ10 : ℝ))
        = (dxbatch d L μ σ ε ρ10 : ℝ) * (th L μ * ε * dxhband d L μ ε ρ10 ^ 2) / 4 := by ring
    have h4' : 12 * cvc L μ * (d : ℝ) * σ ^ 2
        ≤ (dxbatch d L μ σ ε ρ10 : ℝ) * (th L μ * ε * dxhband d L μ ε ρ10 ^ 2) / 4 := by linarith
    linarith
  have hsum3 : ∑ k ∈ Finset.range (iters L μ R ε), rhoA L μ ^ (iters L μ R ε - 1 - k)
        * (C0 L μ * ((d : ℝ) * (ρ10 * dxhband d L μ ε ρ10 ^ 10) ^ 2)
          + cvc L μ * (6 * ((d : ℝ) * σ ^ 2
            / (dxhband d L μ ε ρ10 ^ 2 * (dxbatch d L μ σ ε ρ10 : ℝ))))) ≤ ε / 2 := by
    have hbn : 0 ≤ C0 L μ * ((d : ℝ) * (ρ10 * dxhband d L μ ε ρ10 ^ 10) ^ 2)
        + cvc L μ * (6 * ((d : ℝ) * σ ^ 2
          / (dxhband d L μ ε ρ10 ^ 2 * (dxbatch d L μ σ ε ρ10 : ℝ)))) := by
      refine add_nonneg
        (mul_nonneg (le_of_lt hC0)
          (mul_nonneg (Nat.cast_nonneg d) (sq_nonneg (ρ10 * dxhband d L μ ε ρ10 ^ 10))))
        (mul_nonneg (cvc_nonneg L μ hL hμ)
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6)
            (div_nonneg (mul_nonneg (Nat.cast_nonneg d) (sq_nonneg σ))
              (le_of_lt (mul_pos (pow_pos hh 2) hm0)))))
    have hs : ∑ k ∈ Finset.range (iters L μ R ε),
        rhoA L μ ^ (iters L μ R ε - 1 - k)
          * (C0 L μ * ((d : ℝ) * (ρ10 * dxhband d L μ ε ρ10 ^ 10) ^ 2)
            + cvc L μ * (6 * ((d : ℝ) * σ ^ 2
              / (dxhband d L μ ε ρ10 ^ 2 * (dxbatch d L μ σ ε ρ10 : ℝ)))))
        = (∑ k ∈ Finset.range (iters L μ R ε), rhoA L μ ^ (iters L μ R ε - 1 - k))
            * (C0 L μ * ((d : ℝ) * (ρ10 * dxhband d L μ ε ρ10 ^ 10) ^ 2)
              + cvc L μ * (6 * ((d : ℝ) * σ ^ 2
                / (dxhband d L μ ε ρ10 ^ 2 * (dxbatch d L μ σ ε ρ10 : ℝ))))) :=
      (Finset.sum_mul _ _ _).symm
    rw [hs]
    refine le_trans (mul_le_mul_of_nonneg_right hsumc hbn) ?_
    have h2 : (1 / (th L μ / 2))
        * (C0 L μ * ((d : ℝ) * (ρ10 * dxhband d L μ ε ρ10 ^ 10) ^ 2)
          + cvc L μ * (6 * ((d : ℝ) * σ ^ 2
            / (dxhband d L μ ε ρ10 ^ 2 * (dxbatch d L μ σ ε ρ10 : ℝ)))))
        = (1 / (th L μ / 2)) * (C0 L μ * ((d : ℝ) * (ρ10 * dxhband d L μ ε ρ10 ^ 10) ^ 2))
          + (1 / (th L μ / 2))
            * (cvc L μ * (6 * ((d : ℝ) * σ ^ 2
              / (dxhband d L μ ε ρ10 ^ 2 * (dxbatch d L μ σ ε ρ10 : ℝ))))) := by
      ring
    linarith [hbiasb, hnoiseb]
  linarith

end OracleTemplate.SecantPolyak.DecicStencil

import LongTails.Proofs.AcceleratedSecantTuning

set_option maxHeartbeats 2000000

/-!
Tuning of the symmetric central stencil inside the damped anchored momentum schedule. The squared
symmetric bias is `d * (rho * h ^ 2) ^ 2`, so the bandwidth is a fourth root of `epsilon`, the
replica count is of order `1 / (h ^ 2 * epsilon)`, and the oracle budget is of order
`sqrt (L / mu) * log (1 / epsilon) * d * sigma ^ 2 * sqrt (1 + rho ^ 2) / epsilon ^ (3 / 2)`.
The secant bandwidth `hband` is only a square root because the one-sided difference has bias
`L * h / 2`, which is why the central stencil lowers the exponent of `epsilon`.
-/

namespace OracleTemplate.SecantPolyak.CentralStencil

open OracleTemplate OracleTemplate.SecantPolyak.Accelerated InexactGradient Scheduled
open scoped BigOperators RealInnerProductSpace

/-- Sharp variance coefficient of one centered momentum round. -/
noncomputable def cvc (L μ : ℝ) : ℝ := 1 / (2 * L) + th L μ ^ 2 / μ

/-- Symmetric-stencil bandwidth: the fourth root balancing the squared central bias against the
geometric sum of the momentum contractions. -/
noncomputable def chband (d : ℕ) (L μ ε ρ : ℝ) : ℝ :=
  Real.sqrt (Real.sqrt (ε * th L μ / (8 * C0 L μ * (d : ℝ) * (1 + ρ ^ 2))))

/-- Replicas averaged per coordinate in every round of the schedule. -/
noncomputable def cbatch (d : ℕ) (L μ σ ε ρ : ℝ) : ℕ :=
  ⌈8 * cvc L μ * (d : ℝ) * σ ^ 2 / (th L μ * ε * chband d L μ ε ρ ^ 2)⌉₊ + 1

lemma cvc_nonneg (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ) : 0 ≤ cvc L μ := by
  show 0 ≤ 1 / (2 * L) + th L μ ^ 2 / μ
  positivity

lemma chden_pos {d : ℕ} (hd : 0 < d) (L μ ρ : ℝ) (hL : 0 < L) (hμ : 0 < μ) :
    0 < 8 * C0 L μ * (d : ℝ) * (1 + ρ ^ 2) := by
  have hC0 : 0 < C0 L μ := C0_pos L μ hL hμ
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hq : 0 < (1 : ℝ) + ρ ^ 2 := by nlinarith [sq_nonneg ρ]
  exact mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 8) hC0) hd') hq

lemma chband_pos {d : ℕ} (hd : 0 < d) (L μ ε ρ : ℝ) (hL : 0 < L) (hμ : 0 < μ) (hε : 0 < ε) :
    0 < chband d L μ ε ρ := by
  refine Real.sqrt_pos.mpr (Real.sqrt_pos.mpr ?_)
  refine div_pos (mul_pos hε (th_pos L μ hL hμ)) (chden_pos hd L μ ρ hL hμ)

/-- The fourth power of the bandwidth is the balancing quantity. -/
lemma chband_fourth {d : ℕ} (hd : 0 < d) (L μ ε ρ : ℝ) (hL : 0 < L) (hμ : 0 < μ) (hε : 0 < ε) :
    chband d L μ ε ρ ^ 4 = ε * th L μ / (8 * C0 L μ * (d : ℝ) * (1 + ρ ^ 2)) := by
  classical
  set X := ε * th L μ / (8 * C0 L μ * (d : ℝ) * (1 + ρ ^ 2)) with hXdef
  have hX0 : 0 ≤ X := by
    rw [hXdef]
    refine div_nonneg (mul_nonneg hε.le (le_of_lt (th_pos L μ hL hμ)))
      (le_of_lt (chden_pos hd L μ ρ hL hμ))
  have hsq : chband d L μ ε ρ ^ 2 = Real.sqrt X :=
    Real.sq_sqrt (Real.sqrt_nonneg X)
  calc chband d L μ ε ρ ^ 4 = (chband d L μ ε ρ ^ 2) ^ 2 := by ring
    _ = (Real.sqrt X) ^ 2 := by rw [hsq]
    _ = X := Real.sq_sqrt hX0
    _ = ε * th L μ / (8 * C0 L μ * (d : ℝ) * (1 + ρ ^ 2)) := rfl

/-- The replica count covers the noise of one centered round. -/
lemma cbatch_ge {d : ℕ} (_hd : 0 < d) (L μ σ ε ρ : ℝ) (_hL : 0 < L) (_hμ : 0 < μ) (_hε : 0 < ε) :
    (cbatch d L μ σ ε ρ : ℝ) ≥ 8 * cvc L μ * (d : ℝ) * σ ^ 2 / (th L μ * ε * chband d L μ ε ρ ^ 2) := by
  set X : ℝ := 8 * cvc L μ * (d : ℝ) * σ ^ 2 / (th L μ * ε * chband d L μ ε ρ ^ 2) with hXdef
  have h1 : X ≤ (⌈X⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : (⌈X⌉₊ : ℝ) ≤ (cbatch d L μ σ ε ρ : ℝ) := Nat.cast_le.mpr (Nat.le_succ _)
  linarith

/-- The central tuning inequality: the contracted initial gap, the summed squared central bias and
the summed centered noise fit into `epsilon`. -/
lemma c_tuning (d : ℕ) (hd : 0 < d) (L μ σ R ε ρ : ℝ)
    (hL : 0 < L) (hμ : 0 < μ) (_hμL : μ ≤ L) (_hσ : 0 ≤ σ) (_hR : 0 ≤ R) (hε : 0 < ε)
    (_hρ : 0 ≤ ρ) :
    rhoA L μ ^ iters L μ R ε * (L / 2 * R ^ 2 + μ / 4 * R ^ 2)
        + ∑ k ∈ Finset.range (iters L μ R ε), rhoA L μ ^ (iters L μ R ε - 1 - k)
            * (C0 L μ * ((d : ℝ) * (ρ * chband d L μ ε ρ ^ 2) ^ 2)
              + cvc L μ * ((d : ℝ) * σ ^ 2
                / (chband d L μ ε ρ ^ 2 * (cbatch d L μ σ ε ρ : ℝ)))) ≤ ε := by
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
  have hh : 0 < chband d L μ ε ρ := chband_pos hd L μ ε ρ hL hμ hε
  have h4 : chband d L μ ε ρ ^ 4 = ε * th L μ / (8 * C0 L μ * (d : ℝ) * (1 + ρ ^ 2)) :=
    chband_fourth hd L μ ε ρ hL hμ hε
  have hbiasb : (1 / (th L μ / 2)) * (C0 L μ * ((d : ℝ) * (ρ * chband d L μ ε ρ ^ 2) ^ 2))
      ≤ ε / 4 := by
    have hbexpr : C0 L μ * ((d : ℝ) * (ρ * chband d L μ ε ρ ^ 2) ^ 2)
        = C0 L μ * (d : ℝ) * ρ ^ 2 * chband d L μ ε ρ ^ 4 := by ring
    rw [hbexpr, h4]
    have hd0 : (0 : ℝ) < d := Nat.cast_pos.mpr hd
    have hρ2 : ρ ^ 2 ≤ 1 + ρ ^ 2 := by linarith [sq_nonneg ρ]
    have hw : 0 ≤ C0 L μ * (d : ℝ) * (ε * th L μ) * 4 := by positivity
    have hle : (ρ ^ 2) * (C0 L μ * (d : ℝ) * (ε * th L μ) * 4)
        ≤ (1 + ρ ^ 2) * (C0 L μ * (d : ℝ) * (ε * th L μ) * 4) :=
      mul_le_mul_of_nonneg_right hρ2 hw
    have h1 : (1 / (th L μ / 2)) * (C0 L μ * (d : ℝ) * ρ ^ 2
            * (ε * th L μ / (8 * C0 L μ * (d : ℝ) * (1 + ρ ^ 2))))
        = C0 L μ * (d : ℝ) * ρ ^ 2 * (ε * th L μ)
            / ((th L μ / 2) * (8 * C0 L μ * (d : ℝ) * (1 + ρ ^ 2))) := by
      field_simp
    rw [h1]
    refine (div_le_div_iff₀
      (mul_pos (by positivity) (chden_pos hd L μ ρ hL hμ)) (by norm_num : (0 : ℝ) < 4)).mpr ?_
    have he1 : C0 L μ * (d : ℝ) * ρ ^ 2 * (ε * th L μ) * 4
        = (ρ ^ 2) * (C0 L μ * (d : ℝ) * (ε * th L μ) * 4) := by ring
    have he2 : ε * ((th L μ / 2) * (8 * C0 L μ * (d : ℝ) * (1 + ρ ^ 2)))
        = (1 + ρ ^ 2) * (C0 L μ * (d : ℝ) * (ε * th L μ) * 4) := by ring
    nlinarith [hle, he1, he2]
  have hm : (cbatch d L μ σ ε ρ : ℝ) ≥
      8 * cvc L μ * (d : ℝ) * σ ^ 2 / (th L μ * ε * chband d L μ ε ρ ^ 2) :=
    cbatch_ge hd L μ σ ε ρ hL hμ hε
  have hm0 : (0 : ℝ) < cbatch d L μ σ ε ρ :=
    Nat.cast_pos.mpr (Nat.succ_pos _)
  have hmul : (cbatch d L μ σ ε ρ : ℝ) * (th L μ * ε * chband d L μ ε ρ ^ 2)
      ≥ 8 * cvc L μ * (d : ℝ) * σ ^ 2 := by
    have ht0 : 0 < th L μ * ε * chband d L μ ε ρ ^ 2 := by positivity
    calc (cbatch d L μ σ ε ρ : ℝ) * (th L μ * ε * chband d L μ ε ρ ^ 2)
        ≥ (8 * cvc L μ * (d : ℝ) * σ ^ 2 / (th L μ * ε * chband d L μ ε ρ ^ 2))
            * (th L μ * ε * chband d L μ ε ρ ^ 2) :=
          mul_le_mul_of_nonneg_right hm (le_of_lt ht0)
      _ = 8 * cvc L μ * (d : ℝ) * σ ^ 2 := by field_simp
  have hnoiseb : (1 / (th L μ / 2))
      * (cvc L μ * ((d : ℝ) * σ ^ 2 / (chband d L μ ε ρ ^ 2 * (cbatch d L μ σ ε ρ : ℝ)))) ≤ ε / 4 := by
    have h2 : (1 / (th L μ / 2))
        * (cvc L μ * ((d : ℝ) * σ ^ 2 / (chband d L μ ε ρ ^ 2 * (cbatch d L μ σ ε ρ : ℝ))))
        = 2 * cvc L μ * (d : ℝ) * σ ^ 2 / (th L μ * chband d L μ ε ρ ^ 2 * (cbatch d L μ σ ε ρ : ℝ)) := by
      field_simp
    rw [h2]
    have hp : 0 < th L μ * chband d L μ ε ρ ^ 2 * (cbatch d L μ σ ε ρ : ℝ) := by
      refine mul_pos (mul_pos hth (pow_pos hh 2)) hm0
    refine (div_le_iff₀ hp).mpr ?_
    have h3 : (ε / 4) * (th L μ * chband d L μ ε ρ ^ 2 * (cbatch d L μ σ ε ρ : ℝ))
        = (cbatch d L μ σ ε ρ : ℝ) * (th L μ * ε * chband d L μ ε ρ ^ 2) / 4 := by ring
    have h4' : 2 * cvc L μ * (d : ℝ) * σ ^ 2
        ≤ (cbatch d L μ σ ε ρ : ℝ) * (th L μ * ε * chband d L μ ε ρ ^ 2) / 4 := by linarith
    linarith
  have hsum3 : ∑ k ∈ Finset.range (iters L μ R ε), rhoA L μ ^ (iters L μ R ε - 1 - k)
        * (C0 L μ * ((d : ℝ) * (ρ * chband d L μ ε ρ ^ 2) ^ 2)
          + cvc L μ * ((d : ℝ) * σ ^ 2 / (chband d L μ ε ρ ^ 2 * (cbatch d L μ σ ε ρ : ℝ))))
      ≤ ε / 2 := by
    have hbn : 0 ≤ C0 L μ * ((d : ℝ) * (ρ * chband d L μ ε ρ ^ 2) ^ 2)
        + cvc L μ * ((d : ℝ) * σ ^ 2 / (chband d L μ ε ρ ^ 2 * (cbatch d L μ σ ε ρ : ℝ))) := by
      refine add_nonneg
        (mul_nonneg (le_of_lt hC0)
          (mul_nonneg (Nat.cast_nonneg d) (sq_nonneg (ρ * chband d L μ ε ρ ^ 2))))
        (mul_nonneg (cvc_nonneg L μ hL hμ)
          (div_nonneg (mul_nonneg (Nat.cast_nonneg d) (sq_nonneg σ))
            (le_of_lt (mul_pos (pow_pos hh 2) hm0))))
    have hs : ∑ k ∈ Finset.range (iters L μ R ε),
        rhoA L μ ^ (iters L μ R ε - 1 - k)
          * (C0 L μ * ((d : ℝ) * (ρ * chband d L μ ε ρ ^ 2) ^ 2)
            + cvc L μ * ((d : ℝ) * σ ^ 2 / (chband d L μ ε ρ ^ 2 * (cbatch d L μ σ ε ρ : ℝ))))
        = (∑ k ∈ Finset.range (iters L μ R ε), rhoA L μ ^ (iters L μ R ε - 1 - k))
            * (C0 L μ * ((d : ℝ) * (ρ * chband d L μ ε ρ ^ 2) ^ 2)
              + cvc L μ * ((d : ℝ) * σ ^ 2 / (chband d L μ ε ρ ^ 2 * (cbatch d L μ σ ε ρ : ℝ)))) :=
      (Finset.sum_mul _ _ _).symm
    rw [hs]
    refine le_trans (mul_le_mul_of_nonneg_right hsumc hbn) ?_
    have h2 : (1 / (th L μ / 2))
        * (C0 L μ * ((d : ℝ) * (ρ * chband d L μ ε ρ ^ 2) ^ 2)
          + cvc L μ * ((d : ℝ) * σ ^ 2 / (chband d L μ ε ρ ^ 2 * (cbatch d L μ σ ε ρ : ℝ))))
        = (1 / (th L μ / 2)) * (C0 L μ * ((d : ℝ) * (ρ * chband d L μ ε ρ ^ 2) ^ 2))
          + (1 / (th L μ / 2))
            * (cvc L μ * ((d : ℝ) * σ ^ 2 / (chband d L μ ε ρ ^ 2 * (cbatch d L μ σ ε ρ : ℝ)))) := by
      ring
    linarith [hbiasb, hnoiseb]
  linarith

end OracleTemplate.SecantPolyak.CentralStencil

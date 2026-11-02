import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace OracleTemplate.LineSearch.Tuning

lemma log_ratio_le {L R ε : ℝ} (hL : 0 < L) (hR : 0 < R) (hε : 0 < ε) (n : ℕ)
    (hn : (n : ℝ) ≥ Real.log (4 * L * R ^ 2 / ε) / Real.log (9 / 4)) :
    4 * L * R ^ 2 / ε ≤ (9 / 4 : ℝ) ^ n := by
  have hc : (0 : ℝ) < Real.log (9 / 4) := Real.log_pos (by norm_num)
  have h1 : Real.log (4 * L * R ^ 2 / ε) ≤ (n : ℝ) * Real.log (9 / 4) := by
    have h2 : Real.log (4 * L * R ^ 2 / ε) / Real.log (9 / 4) * Real.log (9 / 4)
        ≤ (n : ℝ) * Real.log (9 / 4) := mul_le_mul_of_nonneg_right hn hc.le
    rwa [div_mul_cancel₀ _ (ne_of_gt hc)] at h2
  have h2 : Real.log (4 * L * R ^ 2 / ε) ≤ Real.log ((9 / 4 : ℝ) ^ n) := by
    rw [Real.log_pow]
    exact h1
  calc 4 * L * R ^ 2 / ε = Real.exp (Real.log (4 * L * R ^ 2 / ε)) :=
      (Real.exp_log (by positivity)).symm
    _ ≤ Real.exp (Real.log ((9 / 4 : ℝ) ^ n)) := Real.exp_le_exp.mpr h2
    _ = (9 / 4 : ℝ) ^ n := Real.exp_log (by positivity)

lemma shrink_le_half {L R ε : ℝ} (hL : 0 < L) (hR : 0 ≤ R) (hε : 0 < ε) (J : ℕ)
    (hJ : (J : ℝ) = 1 + ⌈Real.log (4 * L * R ^ 2 / ε) / Real.log (9 / 4)⌉₊) :
    L / 2 * (2 * R * ((2:ℝ) / 3) ^ (J - 1)) ^ 2 ≤ ε / 2 := by
  by_cases hR0 : R = 0
  · rw [hR0]
    norm_num
    positivity
  have hRp : 0 < R := lt_of_le_of_ne hR (Ne.symm hR0)
  set n := ⌈Real.log (4 * L * R ^ 2 / ε) / Real.log (9 / 4)⌉₊ with hn
  have hJn : J = 1 + n := by
    rw [← Nat.cast_inj (R := ℝ), hJ, Nat.cast_add, Nat.cast_one]
  have hs : J - 1 = n := by
    omega
  have hn' : (n : ℝ) ≥ Real.log (4 * L * R ^ 2 / ε) / Real.log (9 / 4) := by
    rw [hn]
    exact Nat.le_ceil _
  have hB : 4 * L * R ^ 2 / ε ≤ (9 / 4 : ℝ) ^ n := log_ratio_le hL hRp hε n hn'
  have hpow : ((2:ℝ) / 3) ^ n * ((2:ℝ) / 3) ^ n = 1 / (9 / 4 : ℝ) ^ n := by
    have h1 : ((2:ℝ) / 3) ^ n * ((2:ℝ) / 3) ^ n = ((2:ℝ) / 3 * ((2:ℝ) / 3)) ^ n :=
      (mul_pow _ _ _).symm
    rw [h1]
    have h2 : ((2:ℝ) / 3 * ((2:ℝ) / 3) : ℝ) = (9 / 4 : ℝ)⁻¹ := by norm_num
    rw [h2, inv_pow, ← one_div]
  have hpos : (0 : ℝ) < (9 / 4 : ℝ) ^ n := by positivity
  have hinv : 1 / ((9 / 4 : ℝ) ^ n) ≤ ε / (4 * L * R ^ 2) := by
    calc 1 / ((9 / 4 : ℝ) ^ n) ≤ 1 / (4 * L * R ^ 2 / ε) :=
        one_div_le_one_div_of_le (by positivity) hB
      _ = ε / (4 * L * R ^ 2) := by field_simp
  calc L / 2 * (2 * R * ((2:ℝ) / 3) ^ (J - 1)) ^ 2
      = L / 2 * (2 * R * ((2:ℝ) / 3) ^ n) ^ 2 := by rw [hs]
    _ = L / 2 * (4 * R ^ 2 * (((2:ℝ) / 3) ^ n * ((2:ℝ) / 3) ^ n)) := by ring
    _ = L / 2 * (4 * R ^ 2 * (1 / (9 / 4 : ℝ) ^ n)) := by rw [hpow]
    _ ≤ L / 2 * (4 * R ^ 2 * (ε / (4 * L * R ^ 2))) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact hinv
    _ = ε / 2 := by
      have h1 : (4:ℝ) * L * R ^ 2 ≠ 0 := by positivity
      field_simp

lemma noise_le_half {σ ε : ℝ} (hσ : 0 ≤ σ) (hε : 0 < ε) (J m : ℕ) (hJ : 1 ≤ J)
    (hm : (m : ℝ) = 1 + ⌈(12 * (J : ℝ) * σ / ε) ^ 2⌉₊) :
    (J : ℝ) * (3 * (2 * (σ / Real.sqrt m))) ≤ ε / 2 := by
  by_cases hσ0 : σ = 0
  · rw [hσ0]
    norm_num
    linarith
  have hσp : 0 < σ := lt_of_le_of_ne hσ (Ne.symm hσ0)
  have hjp : (0 : ℝ) < J := by exact_mod_cast Nat.zero_lt_one.trans_le hJ
  have hsq : (12 * (J : ℝ) * σ / ε) ^ 2 ≤ (m : ℝ) := by
    rw [hm]
    have h1 : (12 * (J : ℝ) * σ / ε) ^ 2 ≤ ⌈(12 * (J : ℝ) * σ / ε) ^ 2⌉₊ := Nat.le_ceil _
    have h2 : (⌈(12 * (J : ℝ) * σ / ε) ^ 2⌉₊ : ℝ) ≤ (⌈(12 * (J : ℝ) * σ / ε) ^ 2⌉₊ : ℝ) + 1 := by
      linarith
    linarith
  have hs : 12 * (J : ℝ) * σ / ε ≤ Real.sqrt (m : ℝ) := by
    have h1 : Real.sqrt ((12 * (J : ℝ) * σ / ε) ^ 2) ≤ Real.sqrt (m : ℝ) :=
      Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)] at h1
  have hm0 : (0 : ℝ) < Real.sqrt (m : ℝ) := by
    have h1 : (1 : ℝ) ≤ (m : ℝ) := by
      rw [hm]
      have := Nat.zero_le ⌈(12 * (J : ℝ) * σ / ε) ^ 2⌉₊
      linarith
    exact Real.sqrt_pos.mpr (by linarith)
  have hmul : 12 * ((J : ℝ) * σ) ≤ ε * Real.sqrt (m : ℝ) := by
    have h1 : 12 * (J : ℝ) * σ / ε ≤ Real.sqrt (m : ℝ) := hs
    have h2 : 12 * (J : ℝ) * σ ≤ Real.sqrt (m : ℝ) * ε := (div_le_iff₀ hε).mp h1
    simpa [mul_assoc, mul_comm, mul_left_comm] using h2
  have hmain : 6 * ((J : ℝ) * σ) ≤ ε / 2 * Real.sqrt (m : ℝ) := by
    have h1 : 6 * ((J : ℝ) * σ) = 12 * ((J : ℝ) * σ) / 2 := by ring
    rw [h1]
    have h2 : 12 * ((J : ℝ) * σ) / 2 ≤ (ε * Real.sqrt (m : ℝ)) / 2 := by gcongr
    have h3 : (ε * Real.sqrt (m : ℝ)) / 2 = ε / 2 * Real.sqrt (m : ℝ) := by ring
    linarith
  have hw : (J : ℝ) * (3 * (2 * (σ / Real.sqrt m))) = 6 * ((J : ℝ) * σ) / Real.sqrt (m : ℝ) := by
    field_simp [hm0.ne']
    ring
  rw [hw]
  have h9 : 6 * ((J : ℝ) * σ) / Real.sqrt (m : ℝ)
      ≤ (ε / 2 * Real.sqrt (m : ℝ)) / Real.sqrt (m : ℝ) := by gcongr
  have h10 : (ε / 2 * Real.sqrt (m : ℝ)) / Real.sqrt (m : ℝ) = ε / 2 := by
    field_simp [hm0.ne']
  linarith

lemma tuning_bound {L R σ ε : ℝ} (hL : 0 < L) (hR : 0 ≤ R) (hσ : 0 ≤ σ) (hε : 0 < ε)
    (J m : ℕ) (hJ : (J : ℝ) = 1 + ⌈Real.log (4 * L * R ^ 2 / ε) / Real.log (9 / 4)⌉₊)
    (hm : (m : ℝ) = 1 + ⌈144 * (J : ℝ) * σ ^ 2 / ε ^ 2⌉₊) :
    L / 2 * (2 * R * ((2:ℝ) / 3) ^ (J - 1)) ^ 2 + 3 * (2 * σ * Real.sqrt ((J : ℝ) / m)) ≤ ε := by
  have hJ1 : 1 ≤ J := by
    have h1 : (1 : ℝ) ≤ (J : ℝ) := by
      have := Nat.zero_le ⌈Real.log (4 * L * R ^ 2 / ε) / Real.log (9 / 4)⌉₊
      linarith
    exact_mod_cast h1
  have h1 := shrink_le_half hL hR hε J hJ
  have hJ0 : 0 < (J : ℝ) := by
    rw [hJ]
    have := Nat.cast_nonneg (α := ℝ) ⌈Real.log (4 * L * R ^ 2 / ε) / Real.log (9 / 4)⌉₊
    linarith
  have h2 : 3 * (2 * σ * Real.sqrt ((J : ℝ) / m)) ≤ ε / 2 := by
    by_cases hσ0 : σ = 0
    · rw [hσ0]
      norm_num
      linarith
    have hB : 0 < 144 * (J : ℝ) * σ ^ 2 / ε ^ 2 := by positivity
    have hm' : (144 * (J : ℝ) * σ ^ 2 / ε ^ 2) ≤ (m : ℝ) := by
      have := Nat.le_ceil (144 * (J : ℝ) * σ ^ 2 / ε ^ 2)
      linarith
    have hm0 : (0 : ℝ) < m := by
      rw [hm]
      have := Nat.cast_nonneg (α := ℝ) ⌈144 * (J : ℝ) * σ ^ 2 / ε ^ 2⌉₊
      linarith
    have hinv : 1 / (m : ℝ) ≤ 1 / (144 * (J : ℝ) * σ ^ 2 / ε ^ 2) :=
      (one_div_le_one_div hm0 hB).mpr hm'
    have h3 : (J : ℝ) / m ≤ (J : ℝ) / (144 * (J : ℝ) * σ ^ 2 / ε ^ 2) := by
      have e1 : (J : ℝ) / m = (J : ℝ) * (1 / (m : ℝ)) := by field_simp
      have e2 : (J : ℝ) / (144 * (J : ℝ) * σ ^ 2 / ε ^ 2)
          = (J : ℝ) * (1 / (144 * (J : ℝ) * σ ^ 2 / ε ^ 2)) := by field_simp
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_left hinv (by positivity : (0 : ℝ) ≤ J)
    have hdiv : (J : ℝ) / m ≤ ε ^ 2 / (144 * σ ^ 2) := by
      calc (J : ℝ) / m ≤ (J : ℝ) / (144 * (J : ℝ) * σ ^ 2 / ε ^ 2) := h3
        _ = ε ^ 2 / (144 * σ ^ 2) := by field_simp [hJ0.ne', hσ0, hε.ne']
    have hsqr : Real.sqrt ((J : ℝ) / m) ≤ ε / (12 * σ) := by
      refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
      have hsq2 : (ε / (12 * σ)) ^ 2 = ε ^ 2 / (144 * σ ^ 2) := by
        field_simp [hσ0, hε.ne']
        norm_num
      rw [hsq2]
      exact hdiv
    have hc : 3 * (2 * σ * (ε / (12 * σ))) = ε / 2 := by
      field_simp [hσ0, hε.ne']
      norm_num
    rw [← hc]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hsqr (by positivity : (0 : ℝ) ≤ 2 * σ))
      (by positivity : (0 : ℝ) ≤ 3)
  linarith

end OracleTemplate.LineSearch.Tuning

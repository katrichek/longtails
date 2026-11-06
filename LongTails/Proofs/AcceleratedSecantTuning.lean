import LongTails.Proofs.AcceleratedSecantSpace
import LongTails.Proofs.SecantPolyakScheduled

/-!
Tuning of the scheduled momentum zeroth-order algorithm. The momentum step contracts the Lyapunov
potential by `rhoA = 1 - th / 2` with `th` of order `sqrt (μ / L)`, so the number of rounds grows
like `sqrt (L / μ)`. A uniform batch of width `batch` keeps both the bias and the noise of every
round below the share of `ε` allowed by the geometric sum of the contractions.
-/

namespace OracleTemplate.SecantPolyak.Accelerated

open scoped BigOperators
open MeasureTheory

/-- Momentum parameter: `16 * L * th L μ ^ 2 ≤ μ` and `th L μ ≤ 1`. -/
noncomputable def th (L μ : ℝ) : ℝ := min 1 (Real.sqrt (μ / (16 * L)))

/-- Per-round contraction of the momentum potential. -/
noncomputable def rhoA (L μ : ℝ) : ℝ := 1 - th L μ / 2

/-- Coefficient turning one round's mean-square gradient error into potential loss. -/
noncomputable def C0 (L μ : ℝ) : ℝ := 2 * (3 / (4 * L) + 2 * th L μ / μ)

/-- Sampling radius balancing the secant bias against the geometric sum of the contractions. -/
noncomputable def hband (d : ℕ) (L μ ε : ℝ) : ℝ :=
  Real.sqrt (ε * (th L μ / 2) / (2 * C0 L μ * (d : ℝ) * L ^ 2))

/-- Uniform batch width: replicas per coordinate in every round. -/
noncomputable def iters (L μ R ε : ℝ) : ℕ :=
  ⌈(2 / th L μ) * Real.log (2 * (L / 2 * R ^ 2 + μ / 4 * R ^ 2) / ε + 1)⌉₊

lemma th_pos (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ) : 0 < th L μ := by
  show min 1 (Real.sqrt (μ / (16 * L))) > 0
  exact lt_min (by norm_num) (Real.sqrt_pos.mpr (div_pos hμ (by positivity)))

lemma th_le_one (L μ : ℝ) : th L μ ≤ 1 := min_le_left _ _

lemma th_sq_le (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ) : th L μ ^ 2 ≤ μ / (16 * L) := by
  have h0 : 0 ≤ th L μ := le_of_lt (th_pos L μ hL hμ)
  have hx : 0 ≤ μ / (16 * L) := by positivity
  have hle : th L μ ≤ Real.sqrt (μ / (16 * L)) := min_le_right _ _
  have h2 : Real.sqrt (μ / (16 * L)) * Real.sqrt (μ / (16 * L)) = μ / (16 * L) := Real.mul_self_sqrt hx
  have h1 : th L μ * th L μ ≤ Real.sqrt (μ / (16 * L)) * Real.sqrt (μ / (16 * L)) := by
    nlinarith
  rw [pow_two, ← h2]
  exact h1

lemma th_constraint (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ) : 16 * L * th L μ ^ 2 ≤ μ := by
  have h1 : 16 * L * th L μ ^ 2 ≤ 16 * L * (μ / (16 * L)) :=
    mul_le_mul_of_nonneg_left (th_sq_le L μ hL hμ) (by positivity)
  have h2 : 16 * L * (μ / (16 * L)) = μ := by field_simp
  exact le_trans h1 h2.le

lemma rhoA_pos (L μ : ℝ) (_hL : 0 < L) (_hμ : 0 < μ) : 0 < rhoA L μ := by
  show 0 < 1 - th L μ / 2
  linarith [th_le_one L μ]

lemma rhoA_lt_one (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ) : rhoA L μ < 1 := by
  show 1 - th L μ / 2 < 1
  linarith [th_pos L μ hL hμ]

lemma one_sub_rhoA (L μ : ℝ) : 1 - rhoA L μ = th L μ / 2 := by
  show 1 - (1 - th L μ / 2) = th L μ / 2
  ring

lemma C0_pos (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ) : 0 < C0 L μ := by
  have h1 : 0 < 3 / (4 * L) := by positivity
  have h2 : 0 < 2 * th L μ / μ := by
    refine div_pos (mul_pos (by norm_num) (th_pos L μ hL hμ)) hμ
  show 0 < 2 * (3 / (4 * L) + 2 * th L μ / μ)
  exact mul_pos (by norm_num) (add_pos h1 h2)

lemma sum_pow_le_one_sub {ρ : ℝ} (_hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (K : ℕ) :
    ∑ k ∈ Finset.range K, ρ ^ k ≤ (1 - ρ ^ K) / (1 - ρ) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have h5 : ρ ^ K + ∑ k ∈ Finset.range K, ρ ^ k
          ≤ ρ ^ K + (1 - ρ ^ K) / (1 - ρ) := add_le_add_right ih _
      have h6 : (1 - ρ ^ K) / (1 - ρ) + ρ ^ K = (1 - ρ ^ K * ρ) / (1 - ρ) := by
        have hp : 1 - ρ ≠ 0 := by linarith
        field_simp
        ring
      linarith

lemma sum_rho_shift {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (K : ℕ) :
    ∑ k ∈ Finset.range K, ρ ^ (K - 1 - k) ≤ 1 / (1 - ρ) := by
  have h_eq : ∑ k ∈ Finset.range K, ρ ^ (K - 1 - k) = ∑ k ∈ Finset.range K, ρ ^ k :=
    Finset.sum_range_reflect (fun j : ℕ => ρ ^ j) K
  rw [h_eq]
  have h1 : ∑ k ∈ Finset.range K, ρ ^ k ≤ (1 - ρ ^ K) / (1 - ρ) := sum_pow_le_one_sub hρ hρ1 K
  have h0 : 0 ≤ ρ ^ K := pow_nonneg hρ K
  refine le_trans h1 ?_
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

lemma rho_pow_le (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ) (K : ℕ) :
    rhoA L μ ^ K ≤ Real.exp (-(th L μ / 2) * (K : ℝ)) := by
  have h0 : 0 ≤ rhoA L μ := le_of_lt (rhoA_pos L μ hL hμ)
  have h1 : rhoA L μ ≤ Real.exp (-(th L μ / 2)) := by
    show 1 - th L μ / 2 ≤ Real.exp (-(th L μ / 2))
    exact Real.one_sub_le_exp_neg _
  calc rhoA L μ ^ K ≤ Real.exp (-(th L μ / 2)) ^ K := pow_le_pow_left₀ h0 h1 K
    _ = Real.exp (-(th L μ / 2) * (K : ℝ)) := by
        rw [← Real.exp_nat_mul]
        simp [mul_comm]


/-- Geometric decay of the graded momentum batches: slower than the contraction `rhoA`. -/
noncomputable def tauA (L μ : ℝ) : ℝ := 1 - th L μ / 4

lemma tauA_pos (L μ : ℝ) (_hL : 0 < L) (_hμ : 0 < μ) : 0 < tauA L μ := by
  show 0 < 1 - th L μ / 4
  linarith [th_le_one L μ]

lemma tauA_le_one (L μ : ℝ) (_hL : 0 < L) (_hμ : 0 < μ) : tauA L μ ≤ 1 := by
  show 1 - th L μ / 4 ≤ 1
  have h := th_pos L μ _hL _hμ
  linarith

lemma rhoA_lt_tauA (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ) : rhoA L μ < tauA L μ := by
  show 1 - th L μ / 2 < 1 - th L μ / 4
  linarith [th_pos L μ hL hμ]

lemma ratio_inv_le (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ) :
    1 / (1 - rhoA L μ / tauA L μ) ≤ 4 / th L μ := by
  have hth : 0 < th L μ := th_pos L μ hL hμ
  have ht : 0 < tauA L μ := tauA_pos L μ hL hμ
  have h1 : 1 - rhoA L μ / tauA L μ = (tauA L μ - rhoA L μ) / tauA L μ := by
    have hz : tauA L μ ≠ 0 := ne_of_gt ht
    field_simp
  have h2 : tauA L μ - rhoA L μ = th L μ / 4 := by
    show (1 - th L μ / 4) - (1 - th L μ / 2) = th L μ / 4
    ring
  have h3 : 1 / (1 - rhoA L μ / tauA L μ) = tauA L μ / (th L μ / 4) := by
    rw [h1, h2]
    field_simp
  rw [h3]
  refine (div_le_div_iff₀ (by positivity) (by positivity)).mpr ?_
  nlinarith [tauA_le_one L μ hL hμ]

lemma graded_noise_sum {ρ τ : ℝ} (hρ : 0 ≤ ρ) (hρτ : ρ < τ) (hτ : 0 < τ) (_hτ1 : τ ≤ 1)
    (C A : ℝ) (hC : 0 < C) (hA : 0 ≤ A) (K : ℕ) :
    ∑ n ∈ Finset.range K, ρ ^ (K - 1 - n) * (A / (Scheduled.graded C τ K n : ℝ))
      ≤ A / C * (1 / (1 - ρ / τ)) := by
  have hgr : ∀ n : ℕ, C * τ ^ (K - 1 - n) ≤ (Scheduled.graded C τ K n : ℝ) := by
    intro n
    have h1 : C * τ ^ (K - 1 - n) ≤ (⌈C * τ ^ (K - 1 - n)⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (Scheduled.graded C τ K n : ℝ) = 1 + ⌈C * τ ^ (K - 1 - n)⌉₊ := by
      simp [Scheduled.graded]
    linarith
  have hratio : ρ / τ < 1 := (div_lt_one hτ).mpr hρτ
  have hterm : ∀ n ∈ Finset.range K,
      ρ ^ (K - 1 - n) * (A / (Scheduled.graded C τ K n : ℝ))
        ≤ A / C * (ρ / τ) ^ (K - 1 - n) := by
    intro n _
    have hp : (0 : ℝ) < Scheduled.graded C τ K n := by
      exact_mod_cast Scheduled.graded_pos C τ K n
    have hden : A / (Scheduled.graded C τ K n : ℝ) ≤ A / (C * τ ^ (K - 1 - n)) :=
      (div_le_div_iff₀ hp (by positivity)).mpr (by nlinarith [hgr n])
    calc ρ ^ (K - 1 - n) * (A / (Scheduled.graded C τ K n : ℝ))
        ≤ ρ ^ (K - 1 - n) * (A / (C * τ ^ (K - 1 - n))) :=
          mul_le_mul_of_nonneg_left hden (pow_nonneg hρ _)
      _ = A / C * (ρ / τ) ^ (K - 1 - n) := by
          rw [div_pow]
          field_simp
  calc ∑ n ∈ Finset.range K, ρ ^ (K - 1 - n) * (A / (Scheduled.graded C τ K n : ℝ))
      ≤ ∑ n ∈ Finset.range K, A / C * (ρ / τ) ^ (K - 1 - n) := Finset.sum_le_sum hterm
    _ = A / C * ∑ n ∈ Finset.range K, (ρ / τ) ^ (K - 1 - n) := (Finset.mul_sum _ _ _).symm
    _ = A / C * ∑ j ∈ Finset.range K, (ρ / τ) ^ j := by rw [Finset.sum_range_reflect]
    _ ≤ A / C * (1 / (1 - ρ / τ)) := by
        refine mul_le_mul_of_nonneg_left
          (Scheduled.sum_geom_le (ρ / τ) (div_nonneg hρ (le_of_lt hτ)) hratio K) ?_
        exact div_nonneg hA (le_of_lt hC)

/-- Noise strength of the graded momentum schedule. -/
noncomputable def noiseA (d : ℕ) (L μ σ ε : ℝ) : ℝ :=
  1 + 512 * C0 L μ ^ 2 * (d : ℝ) ^ 2 * L ^ 2 * σ ^ 2 / (ε ^ 2 * th L μ ^ 2)

/-- Graded batch widths of the momentum schedule: round `n` of a `K`-round run. -/
noncomputable def batchA (d : ℕ) (L μ σ ε : ℝ) (K n : ℕ) : ℕ :=
  Scheduled.graded (noiseA d L μ σ ε) (tauA L μ) K n

lemma noiseA_pos (d : ℕ) (L μ σ ε : ℝ) (hL : 0 < L) (_hμ : 0 < μ) (hε : 0 < ε) :
    0 < noiseA d L μ σ ε := by
  show 0 < 1 + 512 * C0 L μ ^ 2 * (d : ℝ) ^ 2 * L ^ 2 * σ ^ 2 / (ε ^ 2 * th L μ ^ 2)
  positivity

set_option maxHeartbeats 4000000 in
/-- Graded tuning bound for the scheduled momentum algorithm: the graded batches make the summed
secant noise and bias fit into `ε / 2`, while the momentum rounds contract the initial potential
below `ε / 2`. -/
lemma accel_tuning_graded (d : ℕ) (hd : 0 < d) (L μ σ R ε : ℝ)
    (hL : 0 < L) (hμ : 0 < μ) (_hσ : 0 ≤ σ) (_hR : 0 ≤ R) (hε : 0 < ε) :
    rhoA L μ ^ iters L μ R ε * (L / 2 * R ^ 2 + μ / 4 * R ^ 2)
        + ∑ k ∈ Finset.range (iters L μ R ε), rhoA L μ ^ (iters L μ R ε - 1 - k)
            * (C0 L μ * (8 * (d : ℝ) * σ ^ 2
                / (hband d L μ ε ^ 2 * (batchA d L μ σ ε (iters L μ R ε) k))
              + 2 * ((d : ℝ) * (L * hband d L μ ε / 2) ^ 2))) ≤ ε := by
  classical
  have hth0 : 0 < th L μ := th_pos L μ hL hμ
  have hC0 : 0 < C0 L μ := C0_pos L μ hL hμ
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hh0 : 0 < th L μ / 2 := by linarith
  set A : ℝ := L / 2 * R ^ 2 + μ / 4 * R ^ 2 with hAdef
  set ρ : ℝ := rhoA L μ with hρdef
  set K : ℕ := iters L μ R ε with hKdef
  set hb : ℝ := hband d L μ ε with hbdef
  have hA0 : 0 ≤ A := by
    show 0 ≤ L / 2 * R ^ 2 + μ / 4 * R ^ 2
    positivity
  have hρ0 : 0 ≤ ρ := le_of_lt (rhoA_pos L μ hL hμ)
  have hρ1 : ρ < 1 := rhoA_lt_one L μ hL hμ
  have hhb : 0 < hb := by
    show 0 < Real.sqrt (ε * (th L μ / 2) / (2 * C0 L μ * (d : ℝ) * L ^ 2))
    exact Real.sqrt_pos.mpr (div_pos (mul_pos hε (by linarith)) (by positivity))
  have hhbnz : hb ≠ 0 := ne_of_gt hhb
  have hhb2 : hb ^ 2 = ε * (th L μ / 2) / (2 * C0 L μ * (d : ℝ) * L ^ 2) := by
    rw [hbdef]
    exact Real.sq_sqrt (by positivity)
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
  have hnoise : ∑ k ∈ Finset.range K, ρ ^ (K - 1 - k)
      * (C0 L μ * (8 * (d : ℝ) * σ ^ 2 / (hb ^ 2 * (batchA d L μ σ ε K k)))) ≤ ε / 4 := by
    have h1 : ∑ k ∈ Finset.range K, ρ ^ (K - 1 - k)
        * (C0 L μ * (8 * (d : ℝ) * σ ^ 2 / (hb ^ 2 * (batchA d L μ σ ε K k))))
        = ∑ k ∈ Finset.range K, ρ ^ (K - 1 - k)
            * ((C0 L μ * 8 * (d : ℝ) * σ ^ 2 / hb ^ 2) / (batchA d L μ σ ε K k : ℝ)) := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      show ρ ^ (K - 1 - k)
          * (C0 L μ * (8 * (d : ℝ) * σ ^ 2 / (hb ^ 2 * ((batchA d L μ σ ε K k : ℕ) : ℝ))))
        = ρ ^ (K - 1 - k) * ((C0 L μ * 8 * (d : ℝ) * σ ^ 2 / hb ^ 2)
          / ((batchA d L μ σ ε K k : ℕ) : ℝ))
      field_simp
    rw [h1]
    have h2 : C0 L μ * 8 * (d : ℝ) * σ ^ 2 / hb ^ 2 / noiseA d L μ σ ε ≤ ε * th L μ / 16 := by
      have hEq : C0 L μ * 8 * (d : ℝ) * σ ^ 2 / hb ^ 2
          = (ε * th L μ / 16) * (512 * C0 L μ ^ 2 * (d : ℝ) ^ 2 * L ^ 2 * σ ^ 2
            / (ε ^ 2 * th L μ ^ 2)) := by
        rw [hhb2]
        field_simp
        ring
      have hX : (512 * C0 L μ ^ 2 * (d : ℝ) ^ 2 * L ^ 2 * σ ^ 2 / (ε ^ 2 * th L μ ^ 2))
          ≤ noiseA d L μ σ ε := by
        show (512 * C0 L μ ^ 2 * (d : ℝ) ^ 2 * L ^ 2 * σ ^ 2 / (ε ^ 2 * th L μ ^ 2))
          ≤ 1 + 512 * C0 L μ ^ 2 * (d : ℝ) ^ 2 * L ^ 2 * σ ^ 2 / (ε ^ 2 * th L μ ^ 2)
        linarith [show (0 : ℝ) ≤ 512 * C0 L μ ^ 2 * (d : ℝ) ^ 2 * L ^ 2 * σ ^ 2
            / (ε ^ 2 * th L μ ^ 2) by positivity]
      have hpos : 0 ≤ ε * th L μ / 16 := by positivity
      have hn : 0 < noiseA d L μ σ ε := noiseA_pos d L μ σ ε hL hμ hε
      calc C0 L μ * 8 * (d : ℝ) * σ ^ 2 / hb ^ 2 / noiseA d L μ σ ε
          = (ε * th L μ / 16) * (512 * C0 L μ ^ 2 * (d : ℝ) ^ 2 * L ^ 2 * σ ^ 2
            / (ε ^ 2 * th L μ ^ 2)) / noiseA d L μ σ ε := by rw [hEq]
        _ = (ε * th L μ / 16) *
            ((512 * C0 L μ ^ 2 * (d : ℝ) ^ 2 * L ^ 2 * σ ^ 2 / (ε ^ 2 * th L μ ^ 2))
              / noiseA d L μ σ ε) := by ring
        _ ≤ (ε * th L μ / 16) * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ hpos
            exact (div_le_one hn).mpr hX
        _ = ε * th L μ / 16 := by ring
    have h3 := graded_noise_sum hρ0 (rhoA_lt_tauA L μ hL hμ) (tauA_pos L μ hL hμ)
      (tauA_le_one L μ hL hμ) (noiseA d L μ σ ε) (C0 L μ * 8 * (d : ℝ) * σ ^ 2 / hb ^ 2)
      (noiseA_pos d L μ σ ε hL hμ hε) (by positivity) K
    have h4 : 1 / (1 - ρ / tauA L μ) ≤ 4 / th L μ := ratio_inv_le L μ hL hμ
    have hlt : rhoA L μ / tauA L μ < 1 :=
      (div_lt_one (tauA_pos L μ hL hμ)).mpr (rhoA_lt_tauA L μ hL hμ)
    have hd0' : 0 < 1 - ρ / tauA L μ := by
      show 0 < 1 - rhoA L μ / tauA L μ
      linarith
    calc ∑ k ∈ Finset.range K, ρ ^ (K - 1 - k)
        * ((C0 L μ * 8 * (d : ℝ) * σ ^ 2 / hb ^ 2) / (batchA d L μ σ ε K k : ℝ))
      ≤ (C0 L μ * 8 * (d : ℝ) * σ ^ 2 / hb ^ 2) / noiseA d L μ σ ε
        * (1 / (1 - ρ / tauA L μ)) := h3
      _ ≤ (ε * th L μ / 16) * (1 / (1 - ρ / tauA L μ)) :=
          mul_le_mul_of_nonneg_right h2 (div_nonneg zero_le_one (le_of_lt hd0'))
      _ ≤ (ε * th L μ / 16) * (4 / th L μ) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = ε / 4 := by field_simp; ring
  have hbias : ∑ k ∈ Finset.range K, ρ ^ (K - 1 - k)
      * (C0 L μ * (2 * ((d : ℝ) * (L * hb / 2) ^ 2))) ≤ ε / 4 := by
    have h1 : ∑ k ∈ Finset.range K, ρ ^ (K - 1 - k)
        * (C0 L μ * (2 * ((d : ℝ) * (L * hb / 2) ^ 2)))
        = (∑ k ∈ Finset.range K, ρ ^ (K - 1 - k)) * (C0 L μ * (2 * ((d : ℝ) * (L * hb / 2) ^ 2))) :=
        (Finset.sum_mul _ _ _).symm
    rw [h1]
    have h2 : ∑ k ∈ Finset.range K, ρ ^ (K - 1 - k) ≤ 1 / (th L μ / 2) := by
      have h3 : ∑ k ∈ Finset.range K, ρ ^ (K - 1 - k) ≤ 1 / (1 - ρ) := sum_rho_shift hρ0 hρ1 K
      have h4 : 1 / (1 - ρ) = 1 / (th L μ / 2) := by
        show 1 / (1 - (1 - th L μ / 2)) = 1 / (th L μ / 2)
        ring_nf
      exact h3.trans h4.le
    have hB : 0 ≤ C0 L μ * (2 * ((d : ℝ) * (L * hb / 2) ^ 2)) := by positivity
    have h5 : (∑ k ∈ Finset.range K, ρ ^ (K - 1 - k))
        * (C0 L μ * (2 * ((d : ℝ) * (L * hb / 2) ^ 2)))
        ≤ (1 / (th L μ / 2)) * (C0 L μ * (2 * ((d : ℝ) * (L * hb / 2) ^ 2))) :=
        mul_le_mul_of_nonneg_right h2 hB
    have h6 : (1 / (th L μ / 2)) * (C0 L μ * (2 * ((d : ℝ) * (L * hb / 2) ^ 2))) = ε / 4 := by
      have h7 : 2 * ((d : ℝ) * (L * hb / 2) ^ 2) = (d : ℝ) * L ^ 2 * hb ^ 2 / 2 := by ring
      rw [h7, hhb2]
      field_simp
      norm_num
    linarith
  have hsplit : ∑ k ∈ Finset.range K, ρ ^ (K - 1 - k)
      * (C0 L μ * (8 * (d : ℝ) * σ ^ 2 / (hb ^ 2 * (batchA d L μ σ ε K k))
        + 2 * ((d : ℝ) * (L * hb / 2) ^ 2)))
      = (∑ k ∈ Finset.range K, ρ ^ (K - 1 - k)
          * (C0 L μ * (8 * (d : ℝ) * σ ^ 2 / (hb ^ 2 * (batchA d L μ σ ε K k)))))
        + ∑ k ∈ Finset.range K, ρ ^ (K - 1 - k)
            * (C0 L μ * (2 * ((d : ℝ) * (L * hb / 2) ^ 2))) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring
  have hgoal : rhoA L μ ^ iters L μ R ε * (L / 2 * R ^ 2 + μ / 4 * R ^ 2)
      + ∑ k ∈ Finset.range (iters L μ R ε), ρ ^ (iters L μ R ε - 1 - k)
        * (C0 L μ * (8 * (d : ℝ) * σ ^ 2
            / (hband d L μ ε ^ 2 * (batchA d L μ σ ε (iters L μ R ε) k))
          + 2 * ((d : ℝ) * (L * hband d L μ ε / 2) ^ 2)))
      = ρ ^ K * A + ∑ k ∈ Finset.range K, ρ ^ (K - 1 - k)
        * (C0 L μ * (8 * (d : ℝ) * σ ^ 2 / (hb ^ 2 * (batchA d L μ σ ε K k))
          + 2 * ((d : ℝ) * (L * hb / 2) ^ 2))) := rfl
  linarith
end OracleTemplate.SecantPolyak.Accelerated

import LongTails.Proofs.SecantPolyakSpace

/-!
Graded batch schedule for batched secant descent. An early step contracts the gap but needs only
a weak batch, because its noise is contracted again by every later step. Choosing the batch of
step `n` like `C * rat ^ (K - 1 - n)`, with `rat` strictly closer to `1` than the contraction
`rho`, makes the weighted noise sum to a constant. The total budget then carries no logarithm in
`1 / ε`, unlike a uniform batch, whose cost is the number of steps times the final batch.
-/

namespace OracleTemplate.SecantPolyak.Scheduled

open scoped BigOperators

variable {K : ℕ}

/-- Per-step contraction of the expected gap. -/
noncomputable def rho (L μ : ℝ) : ℝ := 1 - μ / L

/-- Geometric decay of the graded batch sizes, strictly slower than `rho`. -/
noncomputable def rat (L μ : ℝ) : ℝ := 1 - μ / (2 * L)

/-- Batch size of step `n` in a `K`-step run with noise constant `C` and decay `tau`. -/
noncomputable def graded (C tau : ℝ) (K n : ℕ) : ℕ := 1 + ⌈C * tau ^ (K - 1 - n)⌉₊

/-- Noise constant of one batched secant step. -/
noncomputable def noiseConst (d : ℕ) (σ L h : ℝ) : ℝ := 8 * (d : ℝ) * σ ^ 2 / (L * h ^ 2)

/-- Noise strength of the graded schedule: `1` plus the value forced by the accuracy target. -/
noncomputable def noiseScale (d : ℕ) (σ L h μ ε : ℝ) : ℝ :=
  1 + 8 * noiseConst d σ L h * L / (μ * ε)

lemma graded_pos (C tau : ℝ) (K n : ℕ) : 0 < graded C tau K n := by
  show 0 < 1 + ⌈C * tau ^ (K - 1 - n)⌉₊
  omega

lemma graded_ge (C tau : ℝ) (K n : ℕ) :
    1 + C * tau ^ (K - 1 - n) ≤ (graded C tau K n : ℝ) := by
  have hc : C * tau ^ (K - 1 - n) ≤ (⌈C * tau ^ (K - 1 - n)⌉₊ : ℝ) := by
    exact_mod_cast Nat.le_ceil _
  have h1 : (graded C tau K n : ℝ) = 1 + (⌈C * tau ^ (K - 1 - n)⌉₊ : ℝ) := by
    simp [graded]
  rw [h1]
  linarith

lemma graded_lt (hC : 0 ≤ C) (htau : 0 ≤ tau) (K n : ℕ) :
    (graded C tau K n : ℝ) < 2 + C * tau ^ (K - 1 - n) := by
  have hz : 0 ≤ C * tau ^ (K - 1 - n) := by positivity
  have hceil : (⌈C * tau ^ (K - 1 - n)⌉₊ : ℝ) < C * tau ^ (K - 1 - n) + 1 :=
    Nat.ceil_lt_add_one hz
  have h1 : (graded C tau K n : ℝ) = 1 + (⌈C * tau ^ (K - 1 - n)⌉₊ : ℝ) := by
    simp [graded]
  rw [h1]
  linarith

lemma noiseConst_nonneg (d : ℕ) (σ L h : ℝ) (_hL : 0 < L) (hh : 0 < h) :
    0 ≤ noiseConst d σ L h := by
  show 0 ≤ 8 * (d : ℝ) * σ ^ 2 / (L * h ^ 2)
  positivity

lemma noiseScale_pos (d : ℕ) (σ L h μ ε : ℝ) (hL : 0 < L) (hh : 0 < h) (hμ : 0 < μ)
    (hε : 0 < ε) : 0 < noiseScale d σ L h μ ε := by
  show 0 < 1 + 8 * (8 * (d : ℝ) * σ ^ 2 / (L * h ^ 2)) * L / (μ * ε)
  positivity

lemma rho_lt_one (hL : 0 < L) (hμ : 0 < μ) : rho L μ < 1 := by
  show 1 - μ / L < 1
  exact sub_lt_self _ (div_pos hμ hL)

lemma rho_nonneg (hL : 0 < L) (_hμ : 0 < μ) (hμL : μ ≤ L) : 0 ≤ rho L μ := by
  show 0 ≤ 1 - μ / L
  have : μ / L ≤ 1 := (div_le_one hL).mpr hμL
  linarith

lemma rat_pos (hL : 0 < L) (_hμ : 0 < μ) (_hμL : μ ≤ L) : 0 < rat L μ := by
  have : μ / (2 * L) < 1 := by
    refine (div_lt_iff₀ (by positivity)).mpr ?_
    nlinarith
  show 0 < 1 - μ / (2 * L)
  linarith

lemma rat_lt_one (hL : 0 < L) (hμ : 0 < μ) : rat L μ < 1 := by
  show 1 - μ / (2 * L) < 1
  exact sub_lt_self _ (div_pos hμ (by linarith))

lemma rho_le_rat (hL : 0 < L) (hμ : 0 < μ) : rho L μ ≤ rat L μ := by
  refine sub_le_sub_left ?_ 1
  have : μ / L ≥ μ / (2 * L) := by
    rw [ge_iff_le, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

lemma rat_sub_rho (L μ : ℝ) : rat L μ - rho L μ = μ / (2 * L) := by
  show (1 - μ / (2 * L)) - (1 - μ / L) = μ / (2 * L)
  ring

lemma one_sub_rat (_hL : 0 < L) (_hμ : 0 < μ) : 1 - rat L μ = μ / (2 * L) := by
  show 1 - (1 - μ / (2 * L)) = μ / (2 * L)
  ring

lemma one_sub_ratio (hL : 0 < L) (hμ : 0 < μ) (hμL : μ ≤ L) :
    μ / (2 * L) ≤ 1 - rho L μ / rat L μ := by
  have ht : 0 < rat L μ := rat_pos hL hμ hμL
  have ht1 : rat L μ ≤ 1 := le_of_lt (rat_lt_one hL hμ)
  have hd : rat L μ - rho L μ = μ / (2 * L) := rat_sub_rho L μ
  have hnn : 0 ≤ rat L μ - rho L μ := by rw [hd]; positivity
  have h1 : (rat L μ - rho L μ) / rat L μ = 1 - rho L μ / rat L μ := by field_simp
  calc μ / (2 * L) = rat L μ - rho L μ := hd.symm
    _ ≤ (rat L μ - rho L μ) / rat L μ := (le_div_iff₀ ht).mpr (by nlinarith)
    _ = 1 - rho L μ / rat L μ := h1

lemma ratio_lt_one (hL : 0 < L) (hμ : 0 < μ) (hμL : μ ≤ L) : rho L μ / rat L μ < 1 := by
  have ht : 0 < rat L μ := rat_pos hL hμ hμL
  rw [div_lt_one ht]
  refine sub_lt_sub_left ?_ 1
  refine (div_lt_div_iff₀ (by positivity) (by positivity)).mpr ?_
  nlinarith

/-- Finite geometric sums are dominated by the limiting geometric series. -/
lemma sum_geom_le (x : ℝ) (hx : 0 ≤ x) (hx1 : x < 1) (K : ℕ) :
    (∑ j ∈ Finset.range K, x ^ j) ≤ 1 / (1 - x) := by
  have hpos : 0 < 1 - x := by linarith
  have hpe : (∑ j ∈ Finset.range K, x ^ j) * (1 - x) = 1 - x ^ K := geom_sum_mul_neg x K
  have hle : (∑ j ∈ Finset.range K, x ^ j) * (1 - x) ≤ 1 := by
    rw [hpe]
    linarith [pow_nonneg hx K]
  rw [le_div_iff₀ hpos]
  nlinarith

/-- The contraction weights sum to at most `L / μ`. -/
lemma sum_rho_le (hL : 0 < L) (hμ : 0 < μ) (hμL : μ ≤ L) (K : ℕ) :
    (∑ j ∈ Finset.range K, rho L μ ^ j) ≤ L / μ := by
  have hρ : 0 ≤ rho L μ := rho_nonneg hL hμ hμL
  calc (∑ j ∈ Finset.range K, rho L μ ^ j) ≤ 1 / (1 - rho L μ) :=
        sum_geom_le (rho L μ) hρ (rho_lt_one hL hμ) K
    _ = L / μ := by
        show 1 / (1 - (1 - μ / L)) = L / μ
        have he : 1 - (1 - μ / L) = μ / L := by ring
        rw [he]
        field_simp

/-- The weighted noise of the graded schedule is bounded by a quarter of the target accuracy. -/
lemma noise_sum_le (d : ℕ) (σ L h μ ε : ℝ) (hd : 0 < d) (hL : 0 < L) (hμ : 0 < μ)
    (hμL : μ ≤ L) (hε : 0 < ε) (hh : 0 < h) :
    ∑ n ∈ Finset.range K,
        rho L μ ^ (K - 1 - n) * ((1 / L) * (8 * (d : ℝ) * σ ^ 2 /
          (h ^ 2 * (graded (noiseScale d σ L h μ ε) (rat L μ) K n : ℝ)))) ≤ ε / 4 := by
  classical
  set C : ℝ := noiseScale d σ L h μ ε with hCdef
  set A : ℝ := noiseConst d σ L h with hAdef
  have hC : 0 < C := noiseScale_pos d σ L h μ ε hL hh hμ hε
  have hA : 0 ≤ A := noiseConst_nonneg d σ L h hL hh
  have hAeq : ∀ n : ℕ,
      (1 / L) * (8 * (d : ℝ) * σ ^ 2 / (h ^ 2 * (graded C (rat L μ) K n : ℝ)))
        = A / (graded C (rat L μ) K n : ℝ) := by
    intro n
    show (1 / L) * (8 * (d : ℝ) * σ ^ 2 / (h ^ 2 * (graded C (rat L μ) K n : ℝ))) =
      8 * (d : ℝ) * σ ^ 2 / (L * h ^ 2) / (graded C (rat L μ) K n : ℝ)
    field_simp
  have hCbig : 8 * A * L / (μ * ε) ≤ C := by
    show 8 * (8 * (d : ℝ) * σ ^ 2 / (L * h ^ 2)) * L / (μ * ε) ≤
      1 + 8 * (8 * (d : ℝ) * σ ^ 2 / (L * h ^ 2)) * L / (μ * ε)
    have h0 : 0 ≤ 8 * (8 * (d : ℝ) * σ ^ 2 / (L * h ^ 2)) * L / (μ * ε) := by positivity
    linarith
  have hC3 : 8 * A * L ≤ C * (μ * ε) := (div_le_iff₀ (by positivity : (0 : ℝ) < μ * ε)).mp hCbig
  have ht : 0 < rat L μ := rat_pos hL hμ hμL
  have hρ : 0 ≤ rho L μ := rho_nonneg hL hμ hμL
  have hterm : ∀ n ∈ Finset.range K,
      rho L μ ^ (K - 1 - n) * (A / (graded C (rat L μ) K n : ℝ)) ≤
        A / C * (rho L μ / rat L μ) ^ (K - 1 - n) := by
    intro n _
    have hg : 1 + C * rat L μ ^ (K - 1 - n) ≤ (graded C (rat L μ) K n : ℝ) :=
      graded_ge C (rat L μ) K n
    have hp : 0 < (graded C (rat L μ) K n : ℝ) := by
      exact_mod_cast graded_pos C _ K n
    have hden : C * rat L μ ^ (K - 1 - n) ≤ (graded C (rat L μ) K n : ℝ) := by linarith
    have hdiv : A / (graded C (rat L μ) K n : ℝ) ≤ A / (C * rat L μ ^ (K - 1 - n)) :=
      (div_le_div_iff₀ hp (by positivity)).mpr (by nlinarith)
    calc rho L μ ^ (K - 1 - n) * (A / (graded C (rat L μ) K n : ℝ))
        ≤ rho L μ ^ (K - 1 - n) * (A / (C * rat L μ ^ (K - 1 - n))) :=
          mul_le_mul_of_nonneg_left hdiv (pow_nonneg hρ _)
      _ = A / C * (rho L μ / rat L μ) ^ (K - 1 - n) := by
          rw [div_pow]
          field_simp
  calc ∑ n ∈ Finset.range K,
        rho L μ ^ (K - 1 - n) * ((1 / L) * (8 * (d : ℝ) * σ ^ 2 /
          (h ^ 2 * (graded C (rat L μ) K n : ℝ))))
      = ∑ n ∈ Finset.range K, rho L μ ^ (K - 1 - n) * (A / (graded C (rat L μ) K n : ℝ)) :=
          Finset.sum_congr rfl (fun n _ => by rw [hAeq n])
    _ ≤ ∑ n ∈ Finset.range K, A / C * (rho L μ / rat L μ) ^ (K - 1 - n) :=
          Finset.sum_le_sum hterm
    _ = A / C * ∑ n ∈ Finset.range K, (rho L μ / rat L μ) ^ (K - 1 - n) :=
          (Finset.mul_sum _ _ _).symm
    _ = A / C * ∑ j ∈ Finset.range K, (rho L μ / rat L μ) ^ j := by
          rw [Finset.sum_range_reflect]
    _ ≤ A / C * (1 / (1 - rho L μ / rat L μ)) := by
          refine mul_le_mul_of_nonneg_left
            (sum_geom_le (rho L μ / rat L μ) (div_nonneg hρ (le_of_lt ht))
              (ratio_lt_one hL hμ hμL) K) ?_
          exact div_nonneg hA (le_of_lt hC)
    _ ≤ A / C * (2 * L / μ) := by
          refine mul_le_mul_of_nonneg_left ?_ (div_nonneg hA (le_of_lt hC))
          calc 1 / (1 - rho L μ / rat L μ) ≤ 1 / (μ / (2 * L)) :=
                one_div_le_one_div_of_le (by positivity : (0 : ℝ) < μ / (2 * L))
                  (one_sub_ratio hL hμ hμL)
            _ = 2 * L / μ := by field_simp
    _ ≤ ε / 4 := by
      have h5 : A / C * (2 * L / μ) = 2 * A * L / (C * μ) := by field_simp
      rw [h5]
      refine (div_le_div_iff₀ (by positivity) (by positivity)).mpr ?_
      nlinarith [hC3]

/-- The weighted bandwidth bias of the graded schedule is bounded by a quarter of the target. -/
lemma bias_sum_le (d : ℕ) (hL : 0 < L) (hμ : 0 < μ) (hμL : μ ≤ L) (hε : 0 < ε) (hd : 0 < d)
    {h : ℝ} (hh : h = Real.sqrt (μ * ε / (4 * (d : ℝ) * L ^ 2))) :
    ∑ n ∈ Finset.range K,
        rho L μ ^ (K - 1 - n) * ((1 / L) * (2 * ((d : ℝ) * (L * h / 2) ^ 2))) ≤ ε / 4 := by
  have hρ : 0 ≤ rho L μ := rho_nonneg hL hμ hμL
  have hB : 0 ≤ (1 / L) * (2 * ((d : ℝ) * (L * h / 2) ^ 2)) := by positivity
  have hsum : (∑ n ∈ Finset.range K, rho L μ ^ (K - 1 - n)) ≤ L / μ := by
    rw [Finset.sum_range_reflect]
    exact sum_rho_le hL hμ hμL K
  have h2 : (∑ n ∈ Finset.range K, rho L μ ^ (K - 1 - n) *
      ((1 / L) * (2 * ((d : ℝ) * (L * h / 2) ^ 2))))
      = (∑ n ∈ Finset.range K, rho L μ ^ (K - 1 - n)) *
        ((1 / L) * (2 * ((d : ℝ) * (L * h / 2) ^ 2))) :=
      (Finset.sum_mul _ _ _).symm
  have h3 : (L / μ) * ((1 / L) * (2 * ((d : ℝ) * (L * h / 2) ^ 2)))
      = (1 / μ) * (2 * ((d : ℝ) * (L * h / 2) ^ 2)) := by
    show (L / μ) * ((1 / L) * (2 * ((d : ℝ) * (L * h / 2) ^ 2))) =
      (1 / μ) * (2 * ((d : ℝ) * (L * h / 2) ^ 2))
    field_simp
  have h4 : (1 / μ) * (2 * ((d : ℝ) * (L * h / 2) ^ 2)) = (d : ℝ) * L ^ 2 * h ^ 2 / (2 * μ) := by
    field_simp
  have h5 : (d : ℝ) * L ^ 2 * h ^ 2 / (2 * μ) = ε / 8 := by
    have hsq : h ^ 2 = μ * ε / (4 * (d : ℝ) * L ^ 2) := by
      rw [hh, Real.sq_sqrt]
      positivity
    rw [hsq]
    field_simp
    ring
  calc ∑ n ∈ Finset.range K, rho L μ ^ (K - 1 - n) *
        ((1 / L) * (2 * ((d : ℝ) * (L * h / 2) ^ 2)))
      = (∑ n ∈ Finset.range K, rho L μ ^ (K - 1 - n)) *
          ((1 / L) * (2 * ((d : ℝ) * (L * h / 2) ^ 2))) := h2
    _ ≤ (L / μ) * ((1 / L) * (2 * ((d : ℝ) * (L * h / 2) ^ 2))) :=
        mul_le_mul_of_nonneg_right hsum hB
    _ = (1 / μ) * (2 * ((d : ℝ) * (L * h / 2) ^ 2)) := h3
    _ = (d : ℝ) * L ^ 2 * h ^ 2 / (2 * μ) := h4
    _ = ε / 8 := h5
    _ ≤ ε / 4 := by linarith

/-- The graded batches cost at most the final batch times the contraction length. -/
lemma cost_le (d : ℕ) (σ L h μ ε : ℝ) (hL : 0 < L) (hh : 0 < h) (hμ : 0 < μ) (hε : 0 < ε)
    (hμL : μ ≤ L) :
    (∑ n ∈ Finset.range K, (graded (noiseScale d σ L h μ ε) (rat L μ) K n : ℝ))
      ≤ 2 * K + noiseScale d σ L h μ ε * (2 * L / μ) := by
  have hC : 0 ≤ noiseScale d σ L h μ ε :=
    le_of_lt (noiseScale_pos d σ L h μ ε hL hh hμ hε)
  have ht : 0 ≤ rat L μ := le_of_lt (rat_pos hL hμ hμL)
  have hstep : ∀ n ∈ Finset.range K,
      (graded (noiseScale d σ L h μ ε) (rat L μ) K n : ℝ)
        ≤ 2 + noiseScale d σ L h μ ε * rat L μ ^ (K - 1 - n) :=
      fun n _ => le_of_lt (graded_lt hC ht K n)
  have hsum : (∑ n ∈ Finset.range K, noiseScale d σ L h μ ε * rat L μ ^ (K - 1 - n))
      = noiseScale d σ L h μ ε * ∑ n ∈ Finset.range K, rat L μ ^ (K - 1 - n) :=
      (Finset.mul_sum _ _ _).symm
  calc (∑ n ∈ Finset.range K, (graded (noiseScale d σ L h μ ε) (rat L μ) K n : ℝ))
      ≤ ∑ n ∈ Finset.range K, (2 + noiseScale d σ L h μ ε * rat L μ ^ (K - 1 - n)) :=
          Finset.sum_le_sum hstep
    _ = 2 * K + ∑ n ∈ Finset.range K, noiseScale d σ L h μ ε * rat L μ ^ (K - 1 - n) := by
          rw [Finset.sum_add_distrib]
          have h2 : (∑ _n ∈ Finset.range K, (2 : ℝ)) = 2 * K := by
            simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            ring
          rw [h2]
    _ = 2 * K + noiseScale d σ L h μ ε * ∑ n ∈ Finset.range K, rat L μ ^ (K - 1 - n) := by
          rw [hsum]
    _ = 2 * K + noiseScale d σ L h μ ε * ∑ j ∈ Finset.range K, rat L μ ^ j := by
          rw [Finset.sum_range_reflect]
    _ ≤ 2 * K + noiseScale d σ L h μ ε * (1 / (1 - rat L μ)) := by
          have hx : noiseScale d σ L h μ ε * ∑ j ∈ Finset.range K, rat L μ ^ j
              ≤ noiseScale d σ L h μ ε * (1 / (1 - rat L μ)) :=
            mul_le_mul_of_nonneg_left (sum_geom_le (rat L μ) ht (rat_lt_one hL hμ) K) hC
          exact (add_le_add_iff_left (2 * (K : ℝ))).mpr hx
    _ = 2 * K + noiseScale d σ L h μ ε * (2 * L / μ) := by
          rw [one_sub_rat hL hμ]
          field_simp

/-- The oracle slots consumed by `K` graded rounds fit one explicit closed-form budget. -/
lemma slots_le_budget (d : ℕ) {sigma L h mu eps : ℝ} (hL : 0 < L) (hh : 0 < h) (hmu : 0 < mu)
    (heps : 0 < eps) (hmuL : mu ≤ L) :
    2 * d * ∑ n ∈ Finset.range K, graded (noiseScale d sigma L h mu eps) (rat L mu) K n
      ≤ 2 * d * ⌈2 * K + noiseScale d sigma L h mu eps * (2 * L / mu)⌉₊ := by
  refine Nat.mul_le_mul_left (2 * d) ((Nat.cast_le (α := ℝ)).mp ?_)
  rw [Nat.cast_sum]
  exact le_trans (cost_le d sigma L h mu eps hL hh hmu heps hmuL) (Nat.le_ceil _)

/-- Contraction plus the graded batch error fits the target accuracy. -/
lemma tuning_bound (d : ℕ) (σ L R h μ ε : ℝ) (hd : 0 < d) (hL : 0 < L) (_hR : 0 ≤ R)
    (hμ : 0 < μ) (hμL : μ ≤ L) (hε : 0 < ε)
    (hLambda : (K : ℝ) * (μ / L) ≥ 1 + Real.log (1 + 2 * L * R ^ 2 / ε))
    (hh : h = Real.sqrt (μ * ε / (4 * (d : ℝ) * L ^ 2))) :
    rho L μ ^ K * (L / 2 * R ^ 2)
        + ∑ n ∈ Finset.range K, rho L μ ^ (K - 1 - n)
            * ((1 / L) * batchError d (graded (noiseScale d σ L h μ ε) (rat L μ) K n) σ L h)
      ≤ ε := by
  have hg : rho L μ ^ K * (L / 2 * R ^ 2) ≤ ε / 2 :=
    Tuning.gap_term hL hμL hε hLambda
  have hn : ∑ n ∈ Finset.range K,
        rho L μ ^ (K - 1 - n) * ((1 / L) * (8 * (d : ℝ) * σ ^ 2 /
          (h ^ 2 * (graded (noiseScale d σ L h μ ε) (rat L μ) K n : ℝ)))) ≤ ε / 4 :=
      noise_sum_le d σ L h μ ε hd hL hμ hμL hε (by
        rw [hh]
        refine Real.sqrt_pos.mpr (div_pos (mul_pos hμ hε) ?_)
        have hd' : (0 : ℝ) < d := by exact_mod_cast hd
        positivity)
  have hb : ∑ n ∈ Finset.range K,
        rho L μ ^ (K - 1 - n) * ((1 / L) * (2 * ((d : ℝ) * (L * h / 2) ^ 2))) ≤ ε / 4 :=
      bias_sum_le d hL hμ hμL hε hd hh
  have he : ∀ n : ℕ, rho L μ ^ (K - 1 - n)
        * ((1 / L) * batchError d (graded (noiseScale d σ L h μ ε) (rat L μ) K n) σ L h)
      = rho L μ ^ (K - 1 - n)
          * ((1 / L) * (8 * (d : ℝ) * σ ^ 2 /
            (h ^ 2 * (graded (noiseScale d σ L h μ ε) (rat L μ) K n : ℝ))))
        + rho L μ ^ (K - 1 - n) * ((1 / L) * (2 * ((d : ℝ) * (L * h / 2) ^ 2))) := by
    intro n
    show rho L μ ^ (K - 1 - n) * ((1 / L) * (8 * (d : ℝ) * σ ^ 2 /
            (h ^ 2 * (graded (noiseScale d σ L h μ ε) (rat L μ) K n : ℝ))
            + 2 * ((d : ℝ) * (L * h / 2) ^ 2))) = _
    rw [mul_add, mul_add]
  have hsplit : (∑ n ∈ Finset.range K, rho L μ ^ (K - 1 - n)
        * ((1 / L) * batchError d (graded (noiseScale d σ L h μ ε) (rat L μ) K n) σ L h))
      = (∑ n ∈ Finset.range K,
          rho L μ ^ (K - 1 - n) * ((1 / L) * (8 * (d : ℝ) * σ ^ 2 /
            (h ^ 2 * (graded (noiseScale d σ L h μ ε) (rat L μ) K n : ℝ)))))
        + ∑ n ∈ Finset.range K,
          rho L μ ^ (K - 1 - n) * ((1 / L) * (2 * ((d : ℝ) * (L * h / 2) ^ 2))) := by
    rw [Finset.sum_congr rfl (fun n _ => he n), Finset.sum_add_distrib]
  linarith

end OracleTemplate.SecantPolyak.Scheduled

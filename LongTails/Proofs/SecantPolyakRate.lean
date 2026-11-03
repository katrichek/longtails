import LongTails.Setups.ZerothOrderPolyakConvex

/-!
Deterministic core of batched secant descent under the Polyak-Łojasiewicz inequality:
one step contracts the gap by `1 - μ / L` and pays the reply error, and the recursion
closes into an explicit bound with a geometric factor and a linear noise term.
-/

open scoped RealInnerProductSpace

namespace OracleTemplate.SecantPolyak

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- One descent step `x - (1 / L) • (gradient f x + e)` under the Polyak-Łojasiewicz inequality:
the gap contracts by `1 - μ / L` and pays the reply error `‖e‖ ^ 2 / L`. -/
lemma plain_pl_step {f : E → ℝ} {L μ : ℝ} (hL : 0 < L) (hμ : 0 < μ) (xstar : E)
    (hs : ∀ x y, f y ≤ f x + ⟪gradient f x, y - x⟫ + (L / 2) * ‖y - x‖ ^ 2)
    (hpl : ∀ x, 2 * μ * (f x - f xstar) ≤ ‖gradient f x‖ ^ 2)
    (x e : E) :
    f (x - (1 / L) • (gradient f x + e)) - f xstar
      ≤ (1 - μ / L) * (f x - f xstar) + (1 / L) * ‖e‖ ^ 2 := by
  have hpos : (0 : ℝ) < 1 / L := by positivity
  have hd : x - (1 / L) • (gradient f x + e) - x = (-(1 / L)) • (gradient f x + e) := by
    have h : x - (1 / L) • (gradient f x + e) - x = -((1 / L) • (gradient f x + e)) := by abel
    rw [h, neg_smul]
  have h1 : ⟪gradient f x, (-(1 / L)) • (gradient f x + e)⟫
      = -(1 / L) * (‖gradient f x‖ ^ 2 + ⟪gradient f x, e⟫) := by
    rw [inner_smul_right, inner_add_right, real_inner_self_eq_norm_sq]
  have hn : ‖(-(1 / L) : ℝ)‖ = 1 / L := by
    rw [Real.norm_eq_abs, abs_neg, abs_of_pos hpos]
  have h2 : ‖(-(1 / L)) • (gradient f x + e)‖ ^ 2
      = (1 / L) ^ 2 * (‖gradient f x‖ ^ 2 + 2 * ⟪gradient f x, e⟫ + ‖e‖ ^ 2) := by
    rw [norm_smul, hn]
    ring_nf
    rw [norm_add_sq_real]
    ring
  have hz : -(1 / L) * (‖gradient f x‖ ^ 2 + ⟪gradient f x, e⟫)
      + (L / 2) * ((1 / L) ^ 2 * (‖gradient f x‖ ^ 2 + 2 * ⟪gradient f x, e⟫ + ‖e‖ ^ 2))
      = -(1 / (2 * L)) * ‖gradient f x‖ ^ 2 + (1 / (2 * L)) * ‖e‖ ^ 2 := by
    field_simp
    ring
  have hstep : f (x - (1 / L) • (gradient f x + e))
      ≤ f x - (1 / (2 * L)) * ‖gradient f x‖ ^ 2 + (1 / (2 * L)) * ‖e‖ ^ 2 := by
    have hy := hs x (x - (1 / L) • (gradient f x + e))
    rw [hd, h1, h2] at hy
    linarith [hz]
  have heq : (μ / L) * (f x - f xstar) = (1 / (2 * L)) * (2 * μ * (f x - f xstar)) := by
    field_simp
  have hpl' : (μ / L) * (f x - f xstar) ≤ (1 / (2 * L)) * ‖gradient f x‖ ^ 2 := by
    rw [heq]
    exact mul_le_mul_of_nonneg_left (hpl x) (by positivity)
  have hexp : (1 - μ / L) * (f x - f xstar) + (1 / L) * ‖e‖ ^ 2
      = f x - f xstar - (μ / L) * (f x - f xstar) + (1 / L) * ‖e‖ ^ 2 := by ring
  have he : (1 / (2 * L)) * ‖e‖ ^ 2 ≤ (1 / L) * ‖e‖ ^ 2 := by
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have h2 : (1 : ℝ) / (2 * L) = (1 / 2) * (1 / L) := by field_simp
    rw [h2]
    have h4 : (1 / 2 : ℝ) * (1 / L) ≤ 1 * (1 / L) :=
      mul_le_mul_of_nonneg_right (by norm_num) (le_of_lt hpos)
    simpa using h4
  rw [hexp]
  linarith

/-- Geometric recursion with a constant forcing term: `a (k+1) ≤ ρ * a k + c` gives
`a K ≤ ρ ^ K * a 0 + K * c`. -/
lemma pl_recursion {a : ℕ → ℝ} {ρ c : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hc : 0 ≤ c)
    (h : ∀ k, a (k + 1) ≤ ρ * a k + c) (K : ℕ) : a K ≤ ρ ^ K * a 0 + (K : ℝ) * c := by
  induction K with
  | zero => simp
  | succ K ih =>
      have hrc : ρ * (K : ℝ) ≤ (K : ℝ) := mul_le_of_le_one_left (Nat.cast_nonneg _) hρ1
      have h1' : ρ * ((K : ℝ) * c) ≤ (K : ℝ) * c := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hrc hc
      have h2' : ρ * (ρ ^ K * a 0) = ρ * ρ ^ K * a 0 := by ring
      calc a (K + 1) ≤ ρ * a K + c := h K
        _ ≤ ρ * (ρ ^ K * a 0 + (K : ℝ) * c) + c := by gcongr
        _ ≤ ρ * ρ ^ K * a 0 + ((K : ℝ) + 1) * c := by nlinarith
        _ = ρ ^ (K + 1) * a 0 + ((K + 1 : ℕ) : ℝ) * c := by
          rw [pow_succ', Nat.cast_add, Nat.cast_one]

/-- Closed form for descent under the Polyak-Łojasiewicz inequality. With step `1 / L` and a
reply error of mean square at most `v`, `K` steps leave a gap of at most
`(1 - μ / L) ^ K * Δ + (K : ℝ) * v / L`. -/
lemma pl_rate {a : ℕ → ℝ} {L μ Δ v : ℝ} (hL : 0 < L) (hμ : 0 < μ) (hμL : μ ≤ L)
    (hv : 0 ≤ v) (h0 : a 0 ≤ Δ)
    (hrec : ∀ k, a (k + 1) ≤ (1 - μ / L) * a k + v / L) (K : ℕ) :
    a K ≤ (1 - μ / L) ^ K * Δ + (K : ℝ) * (v / L) := by
  have hρ : 0 ≤ 1 - μ / L := by
    have hpos : 0 < μ / L := div_pos hμ hL
    have hle : μ / L ≤ 1 := (div_le_one hL).mpr hμL
    linarith
  have hc : 0 ≤ v / L := div_nonneg hv (le_of_lt hL)
  have hρ1 : 1 - μ / L ≤ 1 := by
    have : 0 ≤ μ / L := div_nonneg (le_of_lt hμ) (le_of_lt hL)
    linarith
  have hp : 0 ≤ (1 - μ / L) ^ K := pow_nonneg hρ _
  have h := pl_recursion hρ hρ1 hc hrec K
  calc a K ≤ (1 - μ / L) ^ K * a 0 + (K : ℝ) * (v / L) := h
    _ ≤ (1 - μ / L) ^ K * Δ + (K : ℝ) * (v / L) :=
      add_le_add (mul_le_mul_of_nonneg_left h0 hp) (le_refl _)

end OracleTemplate.SecantPolyak

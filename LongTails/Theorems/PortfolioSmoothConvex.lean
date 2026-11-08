import LongTails.Setups.ZerothOrderSmoothAndConvex
import LongTails.Theorems.AcceleratedTwoPointZerothOrderConvex
import LongTails.Theorems.AcceleratedZerothOrderConvex
import LongTails.Proofs.MinBudget

/-!
An oracle-free, parameter-dependent choice between the two fully proved multidimensional
stochastic zeroth-order methods for convex objectives with noisy scalar function values, under
exactly `ZerothOrderSmoothAndConvex.spec`. No strong convexity, Polyak inequality, interpolation
or lighter noise model is introduced. For every instance the returned algorithm uses at most the
minimum of the two certified call budgets, counting every paired probe and every batch replica.
The selector itself makes zero oracle calls because it reads only public parameters.
-/

namespace LongTails.Theorems.PortfolioSmoothConvex

open OracleTemplate

private abbrev S := LongTails.Setups.ZerothOrderSmoothAndConvex.spec
private abbrev Params := LongTails.Setups.ZerothOrderSmoothAndConvex.Params

private noncomputable abbrev bA :=
  ZerothOrder.AcceleratedTwoPointZerothOrderConvex.budget
private noncomputable abbrev bB :=
  ZerothOrder.AcceleratedZerothOrderConvex.budget

/-- The exact number of function-value calls of the selected method. -/
noncomputable def budget : (let S := LongTails.Setups.ZerothOrderSmoothAndConvex.spec; S.Params → Fin S.numOracles → ℕ) :=
  OracleTemplate.Portfolio.chooseBudget S
    (fun q => bA q 0 ≤ bB q 0) bA bB

/-- The budget is the pointwise minimum of the two certified bounds. -/
lemma budget_eq_min (q : Params) :
    budget q 0 = min (bA q 0) (bB q 0) := by
  classical
  by_cases h : bA q 0 ≤ bB q 0
  · rw [show budget q 0 = bA q 0 from ite_eq_left h, min_eq_left h]
  · rw [show budget q 0 = bB q 0 from ite_eq_right h]
    rw [min_eq_right (Nat.le_of_lt (Nat.lt_of_not_le h))]

/-- The selected method never costs more than the accelerated random two-point method. -/
lemma budget_le_twoPoint (q : Params) : (budget q 0 : ℝ) ≤ (bA q 0 : ℝ) := by
  rw [budget_eq_min q]
  exact mod_cast min_le_left _ _

/-- The selected method never costs more than the accelerated coordinate probe method. -/
lemma budget_le_onePoint (q : Params) : (budget q 0 : ℝ) ≤ (bB q 0 : ℝ) := by
  rw [budget_eq_min q]
  exact mod_cast min_le_right _ _

/-- Rounding and the dimension factor are monotone, so a budget whose per-round ceiling is at
most the dimension times another ceiling stays ordered after multiplication. -/
private lemma ceil_budget_le {X Y : ℝ} {d : ℕ} (hd : 0 < d) (hXY : X ≤ (d : ℝ) * Y)
    (hY : (1 : ℝ) ≤ Y) :
    max 1 ⌈X⌉₊ * 2 ≤ max 1 ⌈Y⌉₊ * (2 * d) := by
  have hd1 : 1 ≤ d := Nat.succ_le_of_lt hd
  have hY1 : 1 ≤ ⌈Y⌉₊ := by exact_mod_cast hY.trans (Nat.le_ceil Y)
  have hc : ⌈X⌉₊ ≤ d * ⌈Y⌉₊ :=
    Nat.ceil_le.mpr (by
      exact_mod_cast hXY.trans (mul_le_mul_of_nonneg_left (Nat.le_ceil Y) (Nat.cast_nonneg d)))
  have hm : max 1 ⌈X⌉₊ ≤ d * max 1 ⌈Y⌉₊ := by
    have h1 : 1 ≤ d * ⌈Y⌉₊ := by
      have h : 1 * 1 ≤ d * ⌈Y⌉₊ := Nat.mul_le_mul hd1 hY1
      simpa using h
    calc max 1 ⌈X⌉₊ ≤ max 1 (d * ⌈Y⌉₊) := max_le_max (le_refl 1) hc
      _ = d * ⌈Y⌉₊ := max_eq_right h1
      _ ≤ d * max 1 ⌈Y⌉₊ := Nat.mul_le_mul_left _ (le_max_right 1 ⌈Y⌉₊)
  calc max 1 ⌈X⌉₊ * 2 ≤ (d * max 1 ⌈Y⌉₊) * 2 := Nat.mul_le_mul_right _ hm
    _ = max 1 ⌈Y⌉₊ * (2 * d) := by ring

/-- Under the setup's own positivity conditions the accelerated random two-point budget is
never larger than the accelerated coordinate probe budget, because each per-round cost term of
the former is at most the dimension times the matching term of the latter. -/
lemma twoPoint_le_onePoint (q : Params) (hd : 0 < q.d) (hL : 0 < q.L) (hσ : 0 ≤ q.σ)
    (hε : 0 < q.ε) : bA q 0 ≤ bB q 0 := by
  show max 1
        ⌈64 * q.d * Real.sqrt (q.L * q.R ^ 2 / q.ε)
            + 512 * q.L * q.d ^ 2 * q.R ^ 2 * q.σ / q.ε ^ 2
            + 256 * q.L * q.d ^ 2 * q.R ^ 2 * q.σ ^ 2 / q.ε ^ 3 + 1⌉₊ * 2 ≤
      max 1
        ⌈128 * Real.sqrt (q.L * q.R ^ 2 / q.ε)
            + 32768 * q.L * q.d * q.R ^ 2 * q.σ / q.ε ^ 2
            + 8192 * q.L * q.d ^ 2 * q.R ^ 2 * q.σ ^ 2 / q.ε ^ 3 + 1⌉₊ * (2 * q.d)
  refine ceil_budget_le hd ?_ ?_
  · have hd' : (1 : ℝ) ≤ q.d := by exact_mod_cast Nat.succ_le_of_lt hd
    have hs : 0 ≤ Real.sqrt (q.L * q.R ^ 2 * q.ε⁻¹) := Real.sqrt_nonneg _
    have ht : 0 ≤ q.L * q.R ^ 2 * q.ε⁻¹ ^ 2 * q.σ := by positivity
    have hu : 0 ≤ q.L * q.R ^ 2 * q.ε⁻¹ ^ 3 * q.σ ^ 2 := by positivity
    have hd0 : 0 ≤ (q.d : ℝ) := by positivity
    have hd3 : (q.d : ℝ) ^ 2 ≤ (q.d : ℝ) ^ 3 :=
      calc (q.d : ℝ) ^ 2 = (q.d : ℝ) ^ 2 * 1 := by ring
        _ ≤ (q.d : ℝ) ^ 2 * q.d := mul_le_mul_of_nonneg_left hd' (by positivity)
        _ = (q.d : ℝ) ^ 3 := by ring
    ring_nf
    nlinarith [hs, ht, hu, hd0, hd3, sq_nonneg ((q.d : ℝ))]
  · have hs : 0 ≤ Real.sqrt (q.L * q.R ^ 2 / q.ε) := Real.sqrt_nonneg _
    have ht : 0 ≤ 32768 * q.L * q.d * q.R ^ 2 * q.σ / q.ε ^ 2 := by positivity
    have hu : 0 ≤ 8192 * q.L * q.d ^ 2 * q.R ^ 2 * q.σ ^ 2 / q.ε ^ 3 := by positivity
    nlinarith

/-- In the multidimensional convex noisy-value model the envelope reproduces the accelerated
random two-point budget exactly, so it is not asymptotically better than that shipped result. -/
lemma budget_eq_twoPoint (q : Params) (hd : 0 < q.d) (hL : 0 < q.L) (hσ : 0 ≤ q.σ)
    (hε : 0 < q.ε) : budget q 0 = bA q 0 := by
  rw [budget_eq_min q, min_eq_left (twoPoint_le_onePoint q hd hL hσ hε)]

/-- FULL convergence theorem for the original noisy zeroth-order Setup. -/
theorem result :
    OracleTemplate.Convergence LongTails.Setups.ZerothOrderSmoothAndConvex.spec budget :=
  OracleTemplate.Portfolio.choose_convergence S
    (fun q => bA q 0 ≤ bB q 0) bA bB
      ZerothOrder.AcceleratedTwoPointZerothOrderConvex.result
      ZerothOrder.AcceleratedZerothOrderConvex.result

end LongTails.Theorems.PortfolioSmoothConvex

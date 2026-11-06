import LongTails.Algorithms.SecantDescent

namespace OracleTemplate.AveragedTwoPoint

open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {d : ℕ}

/-- Two-point bandit gradient descent with a constant step `η` and averaged output: every round
spends the batch of value queries at the current iterate, moves by `- η • v`, and accumulates the
visited iterate, which is the algorithm output. -/
noncomputable def zoSgd (η : ℝ) (x0 : Point d) : Algorithm (Point d) (Point d) (Point d) where
  State := ℕ × Point d × Point d
  initial _ := (0, x0, 0)
  query s := (0, s.2.1)
  update s v := (s.1 + 1, s.2.1 - η • v, s.2.2 + s.2.1)
  output s := if s.1 = 0 then x0 else (s.1 : ℝ)⁻¹ • s.2.2

/-- The `k`-th visited iterate of the recursion `x_{k+1} = x_k - η • v_k`. -/
noncomputable def iter (η : ℝ) (x0 : Point d) (v : ℕ → Point d) : ℕ → Point d
  | 0 => x0
  | k + 1 => iter η x0 v k - η • v k

/-- The running average of the first `K` visited iterates. -/
noncomputable def avg (η : ℝ) (x0 : Point d) (v : ℕ → Point d) (K : ℕ) : Point d :=
  if _hK : K = 0 then x0 else (K : ℝ)⁻¹ • ∑ k ∈ Finset.range K, iter η x0 v k

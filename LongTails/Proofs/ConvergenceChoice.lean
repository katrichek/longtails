import LongTails.Template

open MeasureTheory

/-!
An exact meta-algorithm construction: a public-parameter-dependent choice between
TWO already proved convergence results.  The result does not claim a novel rate;
it carries their guarantees to the selected budget without changing the oracle.
-/

namespace OracleTemplate.ConvergenceChoice

/-- A deterministic choice based only on the Setup's public data. In particular,
    it cannot inspect the objective, its minimizer or future oracle replies. -/
def selectedBudget (S : OracleTemplate.Setup) (pick : S.Public → Bool)
    (budgetA budgetB : S.Params → Fin S.numOracles → ℕ) :
    S.Params → Fin S.numOracles → ℕ :=
  fun p => if pick (S.publicInput p) then budgetA p else budgetB p

/-- Changing the selected algorithm and the selected call count only changes the executed
programme up to equality, so the accuracy statement is invariant under the choice. -/
theorem successful_congr_execute {S : OracleTemplate.Setup} (p : S.Params)
    (I : S.Instance (S.publicInput p))
    (oracle : Oracle (S.Query (S.publicInput p)) (S.Reply (S.publicInput p)) S.numOracles)
    (A A' : Algorithm (S.Query (S.publicInput p)) (S.Reply (S.publicInput p))
      (S.Output (S.publicInput p)) S.numOracles) (c c' : Fin S.numOracles → ℕ)
    (hAA : A = A') (hcc : c = c') :
    (S.successful p I (fun seed : A.Seed × ((k : ℕ) → oracle.Seed k) =>
        execute oracle A c seed.1 seed.2)
        ⟨(A.law : Measure _).prod (oracle.law : Measure _), inferInstance⟩)
      ↔
      (S.successful p I (fun seed : A'.Seed × ((k : ℕ) → oracle.Seed k) =>
        execute oracle A' c' seed.1 seed.2)
        ⟨(A'.law : Measure _).prod (oracle.law : Measure _), inferInstance⟩) := by
  cases hAA
  cases hcc
  exact Iff.rfl

/-- Each branch can use a different algorithm (and even a different Seed type).
    Therefore the algorithm and its budget must be selected together. -/
theorem select_convergence
    (S : OracleTemplate.Setup)
    (pick : S.Public → Bool)
    (budgetA budgetB : S.Params → Fin S.numOracles → ℕ)
    (hA : OracleTemplate.Convergence S budgetA)
    (hB : OracleTemplate.Convergence S budgetB) :
    OracleTemplate.Convergence S (selectedBudget S pick budgetA budgetB) := by
  classical
  obtain ⟨algA, hAaccurate, hAallowed⟩ := hA
  obtain ⟨algB, hBaccurate, hBallowed⟩ := hB
  refine ⟨(fun p => if pick p then algA p else algB p), ?_, ?_⟩
  · intro p hp I oracle hadmissible
    by_cases h : pick (S.publicInput p)
    · exact
        ((successful_congr_execute (S := S) p I oracle (algA (S.publicInput p))
            ((fun p => if pick p then algA p else algB p) (S.publicInput p)) (budgetA p)
            (selectedBudget S pick budgetA budgetB p) (ite_eq_left h).symm
            (ite_eq_left h).symm).mp)
          (hAaccurate p hp I oracle hadmissible)
    · exact
        ((successful_congr_execute (S := S) p I oracle (algB (S.publicInput p))
            ((fun p => if pick p then algA p else algB p) (S.publicInput p)) (budgetB p)
            (selectedBudget S pick budgetA budgetB p) (ite_eq_right h).symm
            (ite_eq_right h).symm).mp)
          (hBaccurate p hp I oracle hadmissible)
  · intro p hp
    by_cases h : pick (S.publicInput p)
    · have heq : ((fun p => if pick p then algA p else algB p) (S.publicInput p))
        = algA (S.publicInput p) := ite_eq_left h
      exact heq ▸ hAallowed p hp
    · have heq : ((fun p => if pick p then algA p else algB p) (S.publicInput p))
        = algB (S.publicInput p) := ite_eq_right h
      exact heq ▸ hBallowed p hp

end OracleTemplate.ConvergenceChoice

import LongTails.Algorithms.PublicChoice
import LongTails.Proofs.AlgorithmChoiceTransport
import LongTails.Template

/--
A public parameter selector may choose the smaller of two proved budgets without
making oracle calls. The selected algorithm and budget are always tied together.
-/
noncomputable def OracleTemplate.Portfolio.chooseBudget
    (S : OracleTemplate.Setup)
    (preferLeft : S.Public → Prop)
    (left right : S.Params → Fin S.numOracles → ℕ) :
    S.Params → Fin S.numOracles → ℕ := by
  classical
  exact fun q i => if preferLeft (S.publicInput q) then left q i else right q i

/--
Choosing one of two admissible oracle algorithms from public parameters alone preserves
convergence, and the resulting method uses the selected budget. The choice is valid because
it inspects no oracle sample.
-/
theorem OracleTemplate.Portfolio.choose_convergence
    (S : OracleTemplate.Setup)
    (preferLeft : S.Public → Prop)
    (left right : S.Params → Fin S.numOracles → ℕ)
    (hleft : OracleTemplate.Convergence S left)
    (hright : OracleTemplate.Convergence S right) :
    OracleTemplate.Convergence S
      (chooseBudget S preferLeft left right) := by
  classical
  rcases hleft with ⟨A, hA, hAllowedA⟩
  rcases hright with ⟨B, hB, hAllowedB⟩
  refine ⟨chooseAlgorithm S preferLeft A B, ?_, ?_⟩
  · intro q hq I O hO
    by_cases h : preferLeft (S.publicInput q)
    · have hb : chooseBudget S preferLeft left right q = left q := by
        funext i
        exact ite_eq_left h
      have hAlg : A (S.publicInput q) = chooseAlgorithm S preferLeft A B (S.publicInput q) :=
        (ite_eq_left h).symm
      rw [hb]
      refine OracleTemplate.Portfolio.successful_congr_algorithm S q I O (left q) hAlg ?_
      exact hA q hq I O hO
    · have hb : chooseBudget S preferLeft left right q = right q := by
        funext i
        exact ite_eq_right h
      have hAlg : B (S.publicInput q) = chooseAlgorithm S preferLeft A B (S.publicInput q) :=
        (ite_eq_right h).symm
      rw [hb]
      refine OracleTemplate.Portfolio.successful_congr_algorithm S q I O (right q) hAlg ?_
      exact hB q hq I O hO
  · intro q hq
    by_cases h : preferLeft (S.publicInput q)
    · rw [show chooseAlgorithm S preferLeft A B (S.publicInput q) = A (S.publicInput q)
             from ite_eq_left h]
      exact hAllowedA q hq
    · rw [show chooseAlgorithm S preferLeft A B (S.publicInput q) = B (S.publicInput q)
             from ite_eq_right h]
      exact hAllowedB q hq

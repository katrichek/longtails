import LongTails.Algorithms.PublicChoice
import LongTails.Template

namespace OracleTemplate.Portfolio

/-- Transport a success statement along an equality of the selected algorithm.
The two branches of a public-parameter selector carry different seed types, so the
seed space and the product law of a run depend on the branch. Substituting the
chosen algorithm inside this lemma avoids rewriting a dependent goal. -/
theorem successful_congr_algorithm
    (S : OracleTemplate.Setup) (q : S.Params)
    (I : S.Instance (S.publicInput q))
    (O : OracleTemplate.Oracle (S.Query (S.publicInput q))
      (S.Reply (S.publicInput q)) S.numOracles)
    (b : Fin S.numOracles → ℕ)
    {A B : OracleTemplate.Algorithm (S.Query (S.publicInput q))
      (S.Reply (S.publicInput q)) (S.Output (S.publicInput q)) S.numOracles}
    (hAB : A = B) :
    S.successful q I
        (fun seed : A.Seed × ((k : ℕ) → O.Seed k) =>
          OracleTemplate.execute O A b seed.1 seed.2)
        ⟨MeasureTheory.Measure.prod (A.law : MeasureTheory.Measure A.Seed)
            (O.law : MeasureTheory.Measure ((k : ℕ) → O.Seed k)), inferInstance⟩ →
    S.successful q I
        (fun seed : B.Seed × ((k : ℕ) → O.Seed k) =>
          OracleTemplate.execute O B b seed.1 seed.2)
        ⟨MeasureTheory.Measure.prod (B.law : MeasureTheory.Measure B.Seed)
            (O.law : MeasureTheory.Measure ((k : ℕ) → O.Seed k)), inferInstance⟩ := by
  intro h
  cases hAB
  exact h

end OracleTemplate.Portfolio

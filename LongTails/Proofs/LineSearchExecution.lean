import LongTails.Proofs.BatchedExecution
import LongTails.Algorithms.LineSearch

namespace OracleTemplate.LineSearch

open MeasureTheory

lemma execute_lineSearch {Ω : Type} [MeasurableSpace Ω]
    (P : ProbabilityMeasure (ℕ → Ω)) (g : ℝ → Ω → ℝ) (ξ : ℕ → Ω)
    (R x0 : ℝ) {m J : ℕ} (hn : 0 < 2 * m) (seed : (inner R x0).Seed) :
    execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
        (lineSearch R x0 hn) (fun _ => J * (2 * m)) seed ξ =
      (inner R x0).output
        (StochasticGradient.advance (fun call s => (inner R x0).update s
          (decode R x0 s (fun i => g (queries R x0 m s i) (ξ (call * (2 * m) + i.val)))))
          J 0 ((inner R x0).initial seed)) := by
  have h := execute_batched (hn := hn) (A := inner R x0) (queries := queries R x0 m)
    (decode := decode R x0) (zero := 0) P g ξ J seed
  simpa only [lineSearch] using h

end OracleTemplate.LineSearch

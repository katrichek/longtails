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

namespace OracleTemplate.LineSearch

open MeasureTheory

lemma decode_queries {Ω : Type} (R x0 : ℝ) {m : ℕ}
    (s : (inner R x0).State) (g : ℝ → Ω → ℝ) (ξ : ℕ → Ω) (call : ℕ) :
    decode R x0 s (fun i => g (queries R x0 m s i) (ξ (call * (2 * m) + i.val))) =
      ((∑ j : Fin m, g (leftPoint s) (ξ (call * (2 * m) + j.val))) / (m : ℝ),
        (∑ j : Fin m, g (rightPoint s) (ξ (call * (2 * m) + m + j.val))) / (m : ℝ)) := by
  simp only [decode, queries]
  congr 2
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Fin.val_mk, if_pos j.isLt]
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Fin.val_mk, if_neg (by omega : ¬ (m + j.val < m))]
    congr 1
    ring

end OracleTemplate.LineSearch

namespace OracleTemplate.LineSearch

variable (R x0 : ℝ) {Ω : Type}

noncomputable def blockRun (m : ℕ) (g : ℝ → Ω → ℝ) (β : ℕ → (Fin (2 * m) → Ω)) :
    ℕ → State × (ℝ × ℝ) :=
  fun j => Nat.rec (motive := fun _ => State × (ℝ × ℝ))
    ({ level := 0, lo := x0 - R, hi := x0 + R, champ := x0, champVal := 0 }, (0, 0))
    (fun i p =>
      let v := decode R x0 p.1 (fun k => g (leftPoint p.1) (β i k))
      (step p.1 v, v)) j

lemma blockRun_zero (m : ℕ) (g : ℝ → Ω → ℝ) (β : ℕ → (Fin (2 * m) → Ω)) :
    blockRun R x0 m g β 0
      = ({ level := 0, lo := x0 - R, hi := x0 + R, champ := x0, champVal := 0 }, (0, 0)) := rfl

lemma blockRun_succ (m : ℕ) (g : ℝ → Ω → ℝ) (β : ℕ → (Fin (2 * m) → Ω)) (j : ℕ) :
    blockRun R x0 m g β (j + 1)
      = (step (blockRun R x0 m g β j).1
          (decode R x0 (blockRun R x0 m g β j).1
            (fun k => g (leftPoint (blockRun R x0 m g β j).1) (β j k))),
        decode R x0 (blockRun R x0 m g β j).1
          (fun k => g (leftPoint (blockRun R x0 m g β j).1) (β j k))) := rfl

lemma blockRun_pair_succ (m : ℕ) (g : ℝ → Ω → ℝ) (β : ℕ → (Fin (2 * m) → Ω)) (j : ℕ) :
    (blockRun R x0 m g β (j + 1)).2
      = decode R x0 (blockRun R x0 m g β j).1
          (fun k => g (leftPoint (blockRun R x0 m g β j).1) (β j k)) := by
  have h := congrArg Prod.snd (blockRun_succ R x0 m g β j)
  simpa using h

lemma blockRun_state_succ (m : ℕ) (g : ℝ → Ω → ℝ) (β : ℕ → (Fin (2 * m) → Ω)) (j : ℕ) :
    (blockRun R x0 m g β (j + 1)).1
      = step (blockRun R x0 m g β j).1
          (decode R x0 (blockRun R x0 m g β j).1
            (fun k => g (leftPoint (blockRun R x0 m g β j).1) (β j k))) := by
  have h := congrArg Prod.fst (blockRun_succ R x0 m g β j)
  simpa using h

end OracleTemplate.LineSearch

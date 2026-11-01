import LongTails.Algorithms.LineSearch
import LongTails.Proofs.LineSearchLevels

namespace OracleTemplate.LineSearch

variable (R x0 : ℝ) {Ω : Type}

noncomputable def pairRun (m : ℕ) (g : ℝ → Ω → ℝ) (β : ℕ → (Fin m → Ω)) :
    ℕ → State × (ℝ × ℝ) :=
  fun j => Nat.rec (motive := fun _ => State × (ℝ × ℝ))
    ({ level := 0, lo := x0 - R, hi := x0 + R, champ := x0, champVal := 0 }, (0, 0))
    (fun i p =>
      (step p.1
        ((∑ k : Fin m, g (leftPoint p.1) (β (2 * i) k)) / (m : ℝ),
         (∑ k : Fin m, g (rightPoint p.1) (β (2 * i + 1) k)) / (m : ℝ)),
       ((∑ k : Fin m, g (leftPoint p.1) (β (2 * i) k)) / (m : ℝ),
        (∑ k : Fin m, g (rightPoint p.1) (β (2 * i + 1) k)) / (m : ℝ)))) j

lemma pairRun_zero (m : ℕ) (g : ℝ → Ω → ℝ) (β : ℕ → (Fin m → Ω)) :
    pairRun R x0 m g β 0
      = ({ level := 0, lo := x0 - R, hi := x0 + R, champ := x0, champVal := 0 }, (0, 0)) := rfl

lemma pairRun_succ (m : ℕ) (g : ℝ → Ω → ℝ) (β : ℕ → (Fin m → Ω)) (j : ℕ) :
    pairRun R x0 m g β (j + 1)
      = (step (pairRun R x0 m g β j).1
          ((∑ k : Fin m, g (leftPoint (pairRun R x0 m g β j).1) (β (2 * j) k)) / (m : ℝ),
           (∑ k : Fin m, g (rightPoint (pairRun R x0 m g β j).1) (β (2 * j + 1) k)) / (m : ℝ)),
        ((∑ k : Fin m, g (leftPoint (pairRun R x0 m g β j).1) (β (2 * j) k)) / (m : ℝ),
         (∑ k : Fin m, g (rightPoint (pairRun R x0 m g β j).1) (β (2 * j + 1) k)) / (m : ℝ))) := rfl

lemma pairRun_pair_succ (m : ℕ) (g : ℝ → Ω → ℝ) (β : ℕ → (Fin m → Ω)) (j : ℕ) :
    (pairRun R x0 m g β (j + 1)).2
      = ((∑ k : Fin m, g (leftPoint (pairRun R x0 m g β j).1) (β (2 * j) k)) / (m : ℝ),
         (∑ k : Fin m, g (rightPoint (pairRun R x0 m g β j).1) (β (2 * j + 1) k)) / (m : ℝ)) :=
  congrArg Prod.snd (pairRun_succ R x0 m g β j)

lemma pairRun_state_succ (m : ℕ) (g : ℝ → Ω → ℝ) (β : ℕ → (Fin m → Ω)) (j : ℕ) :
    (pairRun R x0 m g β (j + 1)).1
      = step (pairRun R x0 m g β j).1 (pairRun R x0 m g β (j + 1)).2 :=
  congrArg Prod.fst (pairRun_succ R x0 m g β j)

end OracleTemplate.LineSearch

namespace OracleTemplate.LineSearch

variable (R x0 : ℝ) {Ω : Type}

lemma pairRun_state_eq_runState (m : ℕ) (g : ℝ → Ω → ℝ) (β : ℕ → (Fin m → Ω)) (j : ℕ) :
    (pairRun R x0 m g β j).1
      = runState R x0 (fun i => (pairRun R x0 m g β (i + 1)).2) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [pairRun_state_succ R x0 m g β j,
        runState_succ R x0 (fun i => (pairRun R x0 m g β (i + 1)).2) j]
      refine Eq.trans (congrArg (fun s => step s (pairRun R x0 m g β (j + 1)).2) ih) ?_
      rfl

end OracleTemplate.LineSearch

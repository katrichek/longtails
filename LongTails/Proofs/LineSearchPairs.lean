import LongTails.Algorithms.LineSearch
import LongTails.Proofs.LineSearchLevels

open MeasureTheory Set

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

lemma pairRun_congr (m : ℕ) (g : ℝ → Ω → ℝ) {β β' : ℕ → (Fin m → Ω)} {j : ℕ}
    (h : ∀ i < 2 * j, β i = β' i) :
    pairRun R x0 m g β j = pairRun R x0 m g β' j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      have ih' := ih (fun i hi => h i (by omega))
      rw [pairRun_succ R x0 m g β j, pairRun_succ R x0 m g β' j, ih',
        h (2 * j) (by omega), h (2 * j + 1) (by omega)]

lemma pairRun_state_congr (m : ℕ) (g : ℝ → Ω → ℝ) {β β' : ℕ → (Fin m → Ω)} {j : ℕ}
    (h : ∀ i < 2 * j, β i = β' i) :
    (pairRun R x0 m g β j).1 = (pairRun R x0 m g β' j).1 :=
  congrArg Prod.fst (pairRun_congr R x0 m g h)

lemma nonempty_of_probability [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p] :
    Nonempty Ω := by
  by_contra h
  have hempty : (univ : Set Ω) = ∅ := by
    ext x
    exact ⟨fun _ => (h ⟨x⟩).elim, fun hx => hx.elim⟩
  have h1 : p univ = 1 := measure_univ (μ := p)
  rw [hempty, measure_empty] at h1
  exact one_ne_zero h1.symm

noncomputable def combine {m j : ℕ} (h : Fin (2 * j) → (Fin m → Ω))
    (t : ℕ → (Fin m → Ω)) : ℕ → (Fin m → Ω) :=
  fun i => if hi : i < 2 * j then h ⟨i, hi⟩ else t (i - 2 * j)

lemma combine_lt {m j : ℕ} (h : Fin (2 * j) → (Fin m → Ω)) (_t : ℕ → (Fin m → Ω))
    {i : ℕ} (hi : i < 2 * j) : combine h _t i = h ⟨i, hi⟩ := by
  simp only [combine, dif_pos hi]

lemma combine_at {m j : ℕ} (_h : Fin (2 * j) → (Fin m → Ω)) (t : ℕ → (Fin m → Ω)) :
    combine _h t (2 * j) = t 0 := by
  simp only [combine, dif_neg (lt_irrefl _), Nat.sub_self]

lemma pairRun_combine_congr {m j : ℕ} (g : ℝ → Ω → ℝ)
    (h : Fin (2 * j) → (Fin m → Ω)) (t t' : ℕ → (Fin m → Ω)) :
    (pairRun R x0 m g (combine h t) j).1 = (pairRun R x0 m g (combine h t') j).1 := by
  refine pairRun_state_congr R x0 m g (fun i hi => ?_)
  rw [combine_lt h t hi, combine_lt h t' hi]

end OracleTemplate.LineSearch

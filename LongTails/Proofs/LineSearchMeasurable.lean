import LongTails.Proofs.LineSearchPairs
import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory Set ProbabilityTheory

namespace OracleTemplate.LineSearch

variable {Ω : Type}

noncomputable def loAt (R x0 : ℝ) (m : ℕ) (g : ℝ → Ω → ℝ) (β : ℕ → Fin m → Ω) (j : ℕ) : ℝ :=
  (pairRun R x0 m g β j).1.lo

noncomputable def hiAt (R x0 : ℝ) (m : ℕ) (g : ℝ → Ω → ℝ) (β : ℕ → Fin m → Ω) (j : ℕ) : ℝ :=
  (pairRun R x0 m g β j).1.hi

noncomputable def champAt (R x0 : ℝ) (m : ℕ) (g : ℝ → Ω → ℝ) (β : ℕ → Fin m → Ω) (j : ℕ) : ℝ :=
  (pairRun R x0 m g β j).1.champ

noncomputable def valAt (R x0 : ℝ) (m : ℕ) (g : ℝ → Ω → ℝ) (β : ℕ → Fin m → Ω) (j : ℕ) : ℝ :=
  (pairRun R x0 m g β j).1.champVal

noncomputable def leftAt (R x0 : ℝ) (m : ℕ) (g : ℝ → Ω → ℝ) (β : ℕ → Fin m → Ω) (j : ℕ) : ℝ :=
  loAt R x0 m g β j + (hiAt R x0 m g β j - loAt R x0 m g β j) / 3

noncomputable def rightAt (R x0 : ℝ) (m : ℕ) (g : ℝ → Ω → ℝ) (β : ℕ → Fin m → Ω) (j : ℕ) : ℝ :=
  loAt R x0 m g β j + 2 * (hiAt R x0 m g β j - loAt R x0 m g β j) / 3

lemma leftPoint_eq_leftAt (R x0 : ℝ) (m : ℕ) (g : ℝ → Ω → ℝ) (β : ℕ → Fin m → Ω) (j : ℕ) :
    leftPoint (pairRun R x0 m g β j).1 = leftAt R x0 m g β j := rfl

lemma rightPoint_eq_rightAt (R x0 : ℝ) (m : ℕ) (g : ℝ → Ω → ℝ) (β : ℕ → Fin m → Ω) (j : ℕ) :
    rightPoint (pairRun R x0 m g β j).1 = rightAt R x0 m g β j := rfl

noncomputable def estLeft (R x0 : ℝ) (m : ℕ) (g : ℝ → Ω → ℝ) (β : ℕ → Fin m → Ω) (j : ℕ) : ℝ :=
  (∑ k : Fin m, g (leftAt R x0 m g β j) (β (2 * j) k)) / (m : ℝ)

noncomputable def estRight (R x0 : ℝ) (m : ℕ) (g : ℝ → Ω → ℝ) (β : ℕ → Fin m → Ω) (j : ℕ) : ℝ :=
  (∑ k : Fin m, g (rightAt R x0 m g β j) (β (2 * j + 1) k)) / (m : ℝ)

lemma pairRun_pair_succ' (R x0 : ℝ) (m : ℕ) (g : ℝ → Ω → ℝ) (β : ℕ → Fin m → Ω) (j : ℕ) :
    (pairRun R x0 m g β (j + 1)).2 = (estLeft R x0 m g β j, estRight R x0 m g β j) :=
  pairRun_pair_succ R x0 m g β j

lemma pairRun_level (R x0 : ℝ) (m : ℕ) (g : ℝ → Ω → ℝ) (β : ℕ → Fin m → Ω) (j : ℕ) :
    (pairRun R x0 m g β j).1.level = j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pairRun_state_succ, step_level, ih]

lemma champ_step (s : State) (v : ℝ × ℝ) :
    (step s v).champ =
      (if s.level = 0 ∨ min v.1 v.2 < s.champVal then
        (if v.1 > v.2 then rightPoint s else leftPoint s) else s.champ) := by
  rw [step]
  by_cases h0 : s.level = 0
  · rw [ite_eq_left h0, ite_eq_left (Or.inl h0)]
  · rw [ite_eq_right h0]
    by_cases hc : min v.1 v.2 < s.champVal
    · rw [ite_eq_left hc, ite_eq_left (Or.inr hc)]
    · rw [ite_eq_right hc, ite_eq_right (not_or.mpr ⟨h0, hc⟩)]

lemma champVal_step (s : State) (v : ℝ × ℝ) :
    (step s v).champVal =
      (if s.level = 0 ∨ min v.1 v.2 < s.champVal then min v.1 v.2 else s.champVal) := by
  rw [step]
  by_cases h0 : s.level = 0
  · rw [ite_eq_left h0, ite_eq_left (Or.inl h0)]
  · rw [ite_eq_right h0]
    by_cases hc : min v.1 v.2 < s.champVal
    · rw [ite_eq_left hc, ite_eq_left (Or.inr hc)]
    · rw [ite_eq_right hc, ite_eq_right (not_or.mpr ⟨h0, hc⟩)]

variable [MeasurableSpace Ω]

lemma measurableSet_disj_const {α : Type*} [MeasurableSpace α] {p : Prop} {s : Set α}
    (hs : MeasurableSet s) : MeasurableSet {a : α | p ∨ a ∈ s} :=
  MeasurableSet.union (MeasurableSet.const (p := p)) hs

/-- The law of independent blocks of `m` oracle samples. -/
noncomputable def blockLaw (p : Measure Ω) (m : ℕ) : Measure (ℕ → Fin m → Ω) :=
  Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin m => p

/-- The law of countably many independent blocks of `m` i.i.d. samples is a probability measure. -/
instance isProbabilityMeasure_blockLaw (p : Measure Ω) [IsProbabilityMeasure p] (m : ℕ) :
    IsProbabilityMeasure (blockLaw p m) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi fun _ : ℕ =>
    Measure.pi fun _ : Fin m => p))

/-- Evaluate the oracle at a varying point and one fixed sample slot. -/
lemma measurable_oracle_slot {m : ℕ} {g : ℝ → Ω → ℝ} (hg : Measurable (Function.uncurry g))
    (k : Fin m) :
    Measurable (fun p : ℝ × (Fin m → Ω) => g p.1 (p.2 k)) :=
  hg.comp (Measurable.prodMk measurable_fst
    ((measurable_pi_apply k : Measurable (fun v : Fin m → Ω => v k)).comp measurable_snd))

lemma measurable_pairRun_components (R x0 : ℝ) (m : ℕ) (g : ℝ → Ω → ℝ)
    (hg : Measurable (Function.uncurry g)) (j : ℕ) :
    Measurable (fun β : ℕ → Fin m → Ω => loAt R x0 m g β j) ∧
      Measurable (fun β : ℕ → Fin m → Ω => hiAt R x0 m g β j) ∧
      Measurable (fun β : ℕ → Fin m → Ω => champAt R x0 m g β j) ∧
      Measurable (fun β : ℕ → Fin m → Ω => valAt R x0 m g β j) := by
  induction j with
  | zero =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · have : (fun β : ℕ → Fin m → Ω => loAt R x0 m g β 0) = fun _ => x0 - R := rfl
        rw [this]
        exact measurable_const
      · have : (fun β : ℕ → Fin m → Ω => hiAt R x0 m g β 0) = fun _ => x0 + R := rfl
        rw [this]
        exact measurable_const
      · have : (fun β : ℕ → Fin m → Ω => champAt R x0 m g β 0) = fun _ => x0 := rfl
        rw [this]
        exact measurable_const
      · have : (fun β : ℕ → Fin m → Ω => valAt R x0 m g β 0) = fun _ => 0 := rfl
        rw [this]
        exact measurable_const
  | succ j ih =>
      obtain ⟨hlo, hhi, hch, hva⟩ := ih
      have hleft : Measurable (fun β => leftAt R x0 m g β j) := by
        have : (fun β => leftAt R x0 m g β j)
            = fun β => loAt R x0 m g β j + (hiAt R x0 m g β j - loAt R x0 m g β j) / 3 := rfl
        rw [this]
        fun_prop
      have hright : Measurable (fun β => rightAt R x0 m g β j) := by
        have : (fun β => rightAt R x0 m g β j)
            = fun β => loAt R x0 m g β j + 2 * (hiAt R x0 m g β j - loAt R x0 m g β j) / 3 := rfl
        rw [this]
        fun_prop
      have hEL : Measurable (fun β => estLeft R x0 m g β j) := by
        have hsum : Measurable (fun β => ∑ k : Fin m, g (leftAt R x0 m g β j) (β (2 * j) k)) :=
          Finset.measurable_sum Finset.univ fun k _ =>
            (measurable_oracle_slot hg k).comp (Measurable.prodMk hleft
              (measurable_pi_apply _))
        have : (fun β => estLeft R x0 m g β j)
            = fun β => (∑ k : Fin m, g (leftAt R x0 m g β j) (β (2 * j) k)) / (m : ℝ) := rfl
        rw [this]
        exact Measurable.div hsum measurable_const
      have hER : Measurable (fun β => estRight R x0 m g β j) := by
        have hsum : Measurable (fun β => ∑ k : Fin m, g (rightAt R x0 m g β j) (β (2 * j + 1) k)) :=
          Finset.measurable_sum Finset.univ fun k _ =>
            (measurable_oracle_slot hg k).comp (Measurable.prodMk hright
              (measurable_pi_apply _))
        have : (fun β => estRight R x0 m g β j)
            = fun β => (∑ k : Fin m, g (rightAt R x0 m g β j) (β (2 * j + 1) k)) / (m : ℝ) := rfl
        rw [this]
        exact Measurable.div hsum measurable_const
      refine ⟨?_, ?_, ?_, ?_⟩
      · have heq : (fun β => loAt R x0 m g β (j + 1))
            = fun β => if estLeft R x0 m g β j > estRight R x0 m g β j
              then leftAt R x0 m g β j else loAt R x0 m g β j := by
          funext β
          show (pairRun R x0 m g β (j + 1)).1.lo = _
          rw [pairRun_state_succ, lo_step, pairRun_pair_succ', leftPoint_eq_leftAt]
          rfl
        rw [heq]
        refine Measurable.ite (measurableSet_lt hER hEL) hleft hlo
      · have heq : (fun β => hiAt R x0 m g β (j + 1))
            = fun β => if estLeft R x0 m g β j > estRight R x0 m g β j
              then hiAt R x0 m g β j else rightAt R x0 m g β j := by
          funext β
          show (pairRun R x0 m g β (j + 1)).1.hi = _
          rw [pairRun_state_succ, hi_step, pairRun_pair_succ', rightPoint_eq_rightAt]
          rfl
        rw [heq]
        refine Measurable.ite (measurableSet_lt hER hEL) hhi hright
      · have heq : (fun β => champAt R x0 m g β (j + 1))
            = fun β => if j = 0 ∨ min (estLeft R x0 m g β j) (estRight R x0 m g β j)
                < valAt R x0 m g β j then
              (if estLeft R x0 m g β j > estRight R x0 m g β j
                then rightAt R x0 m g β j else leftAt R x0 m g β j)
              else champAt R x0 m g β j := by
          funext β
          show (pairRun R x0 m g β (j + 1)).1.champ = _
          rw [pairRun_state_succ, champ_step, pairRun_pair_succ',
            rightPoint_eq_rightAt, leftPoint_eq_leftAt, pairRun_level]
          rfl
        rw [heq]
        refine Measurable.ite (measurableSet_disj_const
          (measurableSet_lt (Measurable.min hEL hER) hva)) ?_ hch
        · refine Measurable.ite (measurableSet_lt hER hEL) hright hleft
      · have heq : (fun β => valAt R x0 m g β (j + 1))
            = fun β => if j = 0 ∨ min (estLeft R x0 m g β j) (estRight R x0 m g β j)
                < valAt R x0 m g β j then
              min (estLeft R x0 m g β j) (estRight R x0 m g β j) else valAt R x0 m g β j := by
          funext β
          show (pairRun R x0 m g β (j + 1)).1.champVal = _
          rw [pairRun_state_succ, champVal_step, pairRun_pair_succ', pairRun_level]
          rfl
        rw [heq]
        refine Measurable.ite (measurableSet_disj_const
          (measurableSet_lt (Measurable.min hEL hER) hva)) (Measurable.min hEL hER) hva

lemma measurable_leftAt (R x0 : ℝ) (m : ℕ) (g : ℝ → Ω → ℝ)
    (hg : Measurable (Function.uncurry g)) (j : ℕ) :
    Measurable (fun β : ℕ → Fin m → Ω => leftAt R x0 m g β j) := by
  obtain ⟨hlo, hhi, _, _⟩ := measurable_pairRun_components R x0 m g hg j
  have : (fun β : ℕ → Fin m → Ω => leftAt R x0 m g β j)
      = fun β => loAt R x0 m g β j + (hiAt R x0 m g β j - loAt R x0 m g β j) / 3 := rfl
  rw [this]
  fun_prop

lemma measurable_rightAt (R x0 : ℝ) (m : ℕ) (g : ℝ → Ω → ℝ)
    (hg : Measurable (Function.uncurry g)) (j : ℕ) :
    Measurable (fun β : ℕ → Fin m → Ω => rightAt R x0 m g β j) := by
  obtain ⟨hlo, hhi, _, _⟩ := measurable_pairRun_components R x0 m g hg j
  have : (fun β : ℕ → Fin m → Ω => rightAt R x0 m g β j)
      = fun β => loAt R x0 m g β j + 2 * (hiAt R x0 m g β j - loAt R x0 m g β j) / 3 := rfl
  rw [this]
  fun_prop

lemma measurable_champAt (R x0 : ℝ) (m : ℕ) (g : ℝ → Ω → ℝ)
    (hg : Measurable (Function.uncurry g)) (j : ℕ) :
    Measurable (fun β : ℕ → Fin m → Ω => champAt R x0 m g β j) :=
  (measurable_pairRun_components R x0 m g hg j).2.2.1

lemma measurable_estLeft (R x0 : ℝ) (m : ℕ) (g : ℝ → Ω → ℝ)
    (hg : Measurable (Function.uncurry g)) (j : ℕ) :
    Measurable (fun β : ℕ → Fin m → Ω => estLeft R x0 m g β j) := by
  have hleft : Measurable (fun β => leftAt R x0 m g β j) := measurable_leftAt R x0 m g hg j
  have hsum : Measurable (fun β => ∑ k : Fin m, g (leftAt R x0 m g β j) (β (2 * j) k)) :=
    Finset.measurable_sum Finset.univ fun k _ =>
      (measurable_oracle_slot hg k).comp (Measurable.prodMk hleft (measurable_pi_apply _))
  have : (fun β => estLeft R x0 m g β j)
      = fun β => (∑ k : Fin m, g (leftAt R x0 m g β j) (β (2 * j) k)) / (m : ℝ) := rfl
  rw [this]
  exact Measurable.div hsum measurable_const

lemma measurable_estRight (R x0 : ℝ) (m : ℕ) (g : ℝ → Ω → ℝ)
    (hg : Measurable (Function.uncurry g)) (j : ℕ) :
    Measurable (fun β : ℕ → Fin m → Ω => estRight R x0 m g β j) := by
  have hright : Measurable (fun β => rightAt R x0 m g β j) := measurable_rightAt R x0 m g hg j
  have hsum : Measurable (fun β => ∑ k : Fin m, g (rightAt R x0 m g β j) (β (2 * j + 1) k)) :=
    Finset.measurable_sum Finset.univ fun k _ =>
      (measurable_oracle_slot hg k).comp (Measurable.prodMk hright (measurable_pi_apply _))
  have : (fun β => estRight R x0 m g β j)
      = fun β => (∑ k : Fin m, g (rightAt R x0 m g β j) (β (2 * j + 1) k)) / (m : ℝ) := rfl
  rw [this]
  exact Measurable.div hsum measurable_const

end OracleTemplate.LineSearch

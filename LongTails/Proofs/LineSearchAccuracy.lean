import LongTails.Proofs.LineSearchCore
import LongTails.Proofs.LineSearchFubini
import LongTails.Proofs.LineSearchMeasurable
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OracleTemplate.LineSearch

open MeasureTheory ENNReal Set

variable {Ω : Type} [MeasurableSpace Ω] {p : Measure Ω} [hp : IsProbabilityMeasure p]
  (R x0 : ℝ)

/-- Pair estimates driven by the block stream. -/
noncomputable def V (m : ℕ) (g : ℝ → Ω → ℝ) (β : ℕ → Fin m → Ω) (j : ℕ) : ℝ × ℝ :=
  (estLeft R x0 m g β j, estRight R x0 m g β j)

omit [MeasurableSpace Ω] in
lemma runState_V (m : ℕ) (g : ℝ → Ω → ℝ) (β : ℕ → Fin m → Ω) (j : ℕ) :
    runState R x0 (V R x0 m g β) j = (pairRun R x0 m g β j).1 := by
  have hf : (fun i => (pairRun R x0 m g β (i + 1)).2) = V R x0 m g β :=
    funext fun i => (pairRun_pair_succ' R x0 m g β i).symm
  rw [← hf]
  exact (pairRun_state_eq_runState R x0 m g β j).symm

omit [MeasurableSpace Ω] in
/-- One level error written through the deterministic level error. -/
lemma levelError_eq_lvlErr (m : ℕ) (g : ℝ → Ω → ℝ) (f : ℝ → ℝ) (β : ℕ → Fin m → Ω) (j : ℕ) :
    |estLeft R x0 m g β j - f (leftAt R x0 m g β j)|
      + |estRight R x0 m g β j - f (rightAt R x0 m g β j)| = lvlErr R x0 (V R x0 m g β) f j := by
  have h1 : leftPoint (runState R x0 (V R x0 m g β) j) = leftAt R x0 m g β j := by
    rw [runState_V, leftPoint_eq_leftAt]
  have h2 : rightPoint (runState R x0 (V R x0 m g β) j) = rightAt R x0 m g β j := by
    rw [runState_V, rightPoint_eq_rightAt]
  unfold lvlErr
  rw [h1, h2]
  simp only [V]

/-- Measurability of the pathwise gap. -/
lemma measurable_gap (m : ℕ) (g : ℝ → Ω → ℝ) (f : ℝ → ℝ) (xstar : ℝ)
    (hfm : Measurable f) (hg : Measurable (Function.uncurry g)) (J : ℕ) :
    Measurable (fun β : ℕ → Fin m → Ω => f (champAt R x0 m g β J) - f xstar) :=
  (hfm.comp (measurable_champAt R x0 m g hg J)).sub measurable_const

end OracleTemplate.LineSearch

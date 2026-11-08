import LongTails.Proofs.PublicChoiceConvergence

namespace OracleTemplate.Portfolio

/-- Selecting by any decision equivalent to the budget comparison returns the smaller budget. -/
theorem choose_if_eq_min {P : Prop} [dec : Decidable P] (a b : ℕ) (hP : P ↔ a ≤ b) :
    (if P then a else b) = min a b := by
  by_cases h : P
  · rw [ite_eq_left h, min_eq_left (hP.mp h)]
  · rw [ite_eq_right h,
        min_eq_right (Nat.le_of_lt (Nat.lt_of_not_le fun hle => h (hP.mpr hle)))]

end OracleTemplate.Portfolio

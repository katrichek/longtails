import LongTails.Algorithms.ScheduledSecantDescent
import LongTails.Proofs.SecantPolyakScheduledStream
import LongTails.Proofs.BatchedScheduledExecution

namespace OracleTemplate.SecantPolyak.Scheduled

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open SecantDescent SecantPolyak ZerothOrder
open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {Ω : Type} [MeasurableSpace Ω]

/-- Round offsets of the schedule inside the flat oracle stream: round `j` starts after the slots
consumed by the previous rounds. -/
def schedOffsets {d : ℕ} (m : ℕ → ℕ) : Offsets d m where
  off := fun j => ∑ k ∈ Finset.range j, roundSlots d (m k)
  zero := by simp
  step := fun j => Finset.sum_range_succ _ j

/-- Restricting an embedded ambient cell recovers the cell. -/
lemma cellOf_cellInj {d m M : ℕ} (hM : m ≤ M) (t : secantSpace d m)
    (h : (cellInj hM t).1.val < m) : cellOf (cellInj hM t) h = t := by
  refine Prod.ext (Fin.ext ?_) (Prod.ext rfl rfl)
  simp [cellOf, cellInj, Fin.val_castLE]

/-- Round `k` reads the flat-stream slot of its own cell. -/
lemma schedIndex_cellInj {d M : ℕ} {m : ℕ → ℕ} (o : Offsets d m) (K k : ℕ) (hk : k < K)
    (hM : m k ≤ M) (t : secantSpace d (m k)) :
    schedIndex m o K ⟨⟨k, hk⟩, cellInj hM t⟩ =
      o.off k + ((Fintype.equivFin (secantSpace d (m k)) :
        secantSpace d (m k) ≃ Fin (roundSlots d (m k))) t).val := by
  classical
  have hv : (cellInj hM t).1.val < m k := by
    simp [cellInj, Fin.val_castLE]
  rw [schedIndex_used m o K k hk (cellInj hM t) hv]
  have h3 : (Fintype.equivFin (secantSpace d (m k)) :
      secantSpace d (m k) ≃ Fin (roundSlots d (m k))) (cellOf (cellInj hM t) hv)
      = Fintype.equivFin (secantSpace d (m k)) t := by
    refine congrArg _ ?_
    exact cellOf_cellInj hM t _
  rw [h3]

end OracleTemplate.SecantPolyak.Scheduled

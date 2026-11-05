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

/-- The flat-stream slot of round `l` used by the cell `t`. -/
noncomputable def readFlat {d : ℕ} {m : ℕ → ℕ} (ξ : ℕ → Ω) (off : ℕ → ℕ) (l : ℕ)
    (t : secantSpace d (m l)) : Ω :=
  ξ (off l + (Fintype.equivFin (secantSpace d (m l)) t).val)

/-- The points queried by one round of scheduled secant descent. -/
noncomputable def roundReads {d : ℕ} {m : ℕ → ℕ} (h : ℝ) (g : Point d → Ω → ℝ) (ξ : ℕ → Ω) (off : ℕ → ℕ)
    (l : ℕ)
    (x : Point d) : secantSpace d (m l) → ℝ :=
  fun t => g (secantPoint h x t) (readFlat ξ off l t)

omit [MeasurableSpace Ω] in
/-- The reply vector of a round determines the whole update, so only the embedded cells matter. -/
lemma roundReads_congr {d : ℕ} {m : ℕ → ℕ} (h : ℝ) {g : Point d → Ω → ℝ} (ξ ξ' : ℕ → Ω)
    (off : ℕ → ℕ) (l : ℕ) (x : Point d)
    (hcell : ∀ t : secantSpace d (m l), readFlat ξ off l t = readFlat ξ' off l t) :
    (roundReads h g ξ off l x : secantSpace d (m l) → ℝ) = roundReads h g ξ' off l x := by
  refine funext fun t => congrArg (g (secantPoint h x t)) ?_
  exact hcell t

omit [MeasurableSpace Ω] in
/-- Decoding the replies of one round only depends on the slots of that round. -/
lemma roundReads_decode {d : ℕ} {m : ℕ → ℕ} (h : ℝ) {g : Point d → Ω → ℝ} (ξ : ℕ → Ω)
    (off : ℕ → ℕ) (l k : ℕ) (x : Point d) :
    secantDecode (m := m l) h (k, x) (roundReads h g ξ off l x)
      = secantDecode (m := m l) h (k, x) (fun t : secantSpace d (m l) =>
          g (secantPoint h x t) (readFlat ξ off l t)) := rfl

end OracleTemplate.SecantPolyak.Scheduled

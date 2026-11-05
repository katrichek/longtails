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

omit [MeasurableSpace Ω] in
/-- Scheduled rounds only read ambient cells through the embedding, so streams that agree on the
embedded cells of every round give the same analysed run. -/
lemma runSched_congr {d M : ℕ} {m : ℕ → ℕ} (hmM : ∀ k, m k ≤ M) (L : ℝ)
    {g : Point d → Ω → ℝ} (h : ℝ) (i K : ℕ) (x : Point d)
    (Ξ Ξ' : Fin K → secantSpace d M → Ω)
    (hcell : ∀ (l : ℕ) (hi : i ≤ l) (t : secantSpace d (m l)) (hl : l < i + K),
        Ξ ⟨l - i, by omega⟩ (cellInj (hmM l) t) = Ξ' ⟨l - i, by omega⟩ (cellInj (hmM l) t)) :
    runSched (stepSched m hmM L g h) i K x Ξ
      = runSched (stepSched m hmM L g h) i K x Ξ' := by
  classical
  induction K generalizing i x with
  | zero => rfl
  | succ K ih =>
      show runSched (stepSched m hmM L g h) (i + 1) K (stepSched m hmM L g h i x (Ξ 0))
            (fun j : Fin K => Ξ ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
        = runSched (stepSched m hmM L g h) (i + 1) K (stepSched m hmM L g h i x (Ξ' 0))
            (fun j : Fin K => Ξ' ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
      have hstep : stepSched m hmM L g h i x (Ξ 0) = stepSched m hmM L g h i x (Ξ' 0) := by
        refine congrArg (fun ω : secantSpace d (m i) → Ω => stepSlot L g h x ω) (funext fun t => ?_)
        have hpre := hcell i (Nat.le_refl i) t (by omega)
        rw [show (⟨i - i, by omega⟩ : Fin (K + 1)) = (0 : Fin (K + 1)) from
            Fin.ext (Nat.sub_self i)] at hpre
        exact hpre
      have hs : ∀ (l : ℕ) (hi : i + 1 ≤ l) (t : secantSpace d (m l)) (hl : l < i + 1 + K),
          (fun j : Fin K => Ξ ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) ⟨l - (i + 1), by omega⟩
              (cellInj (hmM l) t)
            = (fun j : Fin K => Ξ' ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) ⟨l - (i + 1), by omega⟩
                (cellInj (hmM l) t) := by
        intro l hi t hl
        have hp1 : l - i < K + 1 := by omega
        have hp2 : l - (i + 1) + 1 < K + 1 := by omega
        have hf' : (l - i : ℕ) = l - (i + 1) + 1 := by
          rw [← Nat.sub_sub, Nat.sub_add_cancel (show (1 : ℕ) ≤ l - i by omega)]
        have hf : (⟨l - i, hp1⟩ : Fin (K + 1)) = ⟨l - (i + 1) + 1, hp2⟩ := Fin.ext hf'
        have hpre := hcell l (Nat.le_trans (Nat.le_succ i) hi) t (by omega)
        rw [hf] at hpre
        exact hpre
      rw [ih (i + 1) (stepSched m hmM L g h i x (Ξ 0))
        (fun j : Fin K => Ξ ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
        (fun j : Fin K => Ξ' ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) hs, hstep]

end OracleTemplate.SecantPolyak.Scheduled

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

noncomputable abbrev schedQS {d : ℕ} {m : ℕ → ℕ} (h : ℝ) :
    ∀ k, (ℕ × Point d) → Fin (Fintype.card (secantSpace d (m k))) → Point d :=
  fun _ s t => secantQuery h s (secantSlot t)

noncomputable abbrev schedDec {d : ℕ} {m : ℕ → ℕ} (h : ℝ) :
    ∀ k, (ℕ × Point d) → (Fin (Fintype.card (secantSpace d (m k))) → ℝ) → Point d :=
  fun k s reps => secantDecode h s (fun t : secantSpace d (m k) =>
    reps (Fintype.equivFin (secantSpace d (m k)) t))

omit [MeasurableSpace Ω] in
/-- Running `K` scheduled secant rounds on the flat oracle stream reproduces the analysed run. -/
lemma roundsR_eq_runSched {d M : ℕ} {m : ℕ → ℕ} (hmM : ∀ k, m k ≤ M) (L h : ℝ) (x0 : Point d)
    (o : Offsets d m) (g : Point d → Ω → ℝ) (ξ : ℕ → Ω) :
    ∀ K : ℕ, @OracleTemplate.StochasticGradient.roundsR (Point d) (Point d) ℝ (Point d) Ω (fun k => Fintype.card (secantSpace d (m k))) o.off (descent L x0)
        (schedQS h) (schedDec h) g ξ K (0, x0)
      = (K, runSched (stepSched m hmM L g h) 0 K x0
          (fun k : Fin K => fun t : secantSpace d M => ξ (schedIndex m o K ⟨k, t⟩))) := by
  classical
  intro K
  induction K with
  | zero => rfl
  | succ K ih =>
      have hround : ∀ y, (descent L x0).update (K, y)
            (schedDec (m := m) h K (K, y) (fun i => g (schedQS (m := m) h K (K, y) i) (ξ (o.off K + i.val))))
          = (K + 1, stepSched m hmM L g h K y (fun t : secantSpace d M =>
              ξ (schedIndex m o (K + 1) ⟨⟨K, Nat.lt_succ_self K⟩, t⟩))) := by
        intro y
        refine Prod.ext rfl ?_
        show y - (1 / L) • secantDecode h (K, y)
              (fun t : secantSpace d (m K) =>
                g (secantQuery h (K, y) (secantSlot (Fintype.equivFin (secantSpace d (m K)) t)))
                  (ξ (o.off K + (Fintype.equivFin (secantSpace d (m K)) t).val))) = _
        have hq : (fun t : secantSpace d (m K) =>
              g (secantQuery h (K, y) (secantSlot (Fintype.equivFin (secantSpace d (m K)) t)))
                (ξ (o.off K + (Fintype.equivFin (secantSpace d (m K)) t).val)))
            = (fun t : secantSpace d (m K) =>
                g (secantPoint h y t)
                  (ξ (o.off K + (Fintype.equivFin (secantSpace d (m K)) t).val))) := by
          refine funext fun t =>
            congrArg (fun p => g p (ξ (o.off K + (Fintype.equivFin (secantSpace d (m K)) t).val)))
              ?_
          rw [secantQuery_apply, secantSlot_equivFin]
        rw [hq, decode_eq_reply]
        have hidx : (fun t : secantSpace d (m K) =>
              ξ (schedIndex m o (K + 1)
                ⟨⟨K, Nat.lt_succ_self K⟩, cellInj (hmM K) t⟩))
            = (fun t : secantSpace d (m K) =>
                ξ (o.off K + (Fintype.equivFin (secantSpace d (m K)) t).val)) := by
          refine funext fun t => congrArg ξ ?_
          exact schedIndex_cellInj o (K + 1) K (Nat.lt_succ_self K) (hmM K) t
        rw [← hidx]
        rfl
      have hcon : runSched (stepSched m hmM L g h) 0 K x0
            (fun j : Fin K => fun t : secantSpace d M =>
              ξ (schedIndex m o (K + 1) ⟨Fin.castAdd 1 j, t⟩))
          = runSched (stepSched m hmM L g h) 0 K x0
            (fun k : Fin K => fun t : secantSpace d M => ξ (schedIndex m o K ⟨k, t⟩)) := by
        refine runSched_congr hmM L h 0 K x0 _ _ ?_
        intro l hi t hl
        show ξ (schedIndex m o (K + 1) (Fin.castAdd 1 ⟨l - 0, _⟩, cellInj (hmM l) t))
          = ξ (schedIndex m o K (⟨l - 0, _⟩, cellInj (hmM l) t))
        exact congrArg ξ ((schedIndex_cellInj o (K + 1) l (by omega) (hmM l) t).trans
          (schedIndex_cellInj o K l (by omega) (hmM l) t).symm)
      show (descent L x0).update (@OracleTemplate.StochasticGradient.roundsR (Point d) (Point d) ℝ (Point d) Ω (fun k => Fintype.card (secantSpace d (m k)))
              o.off (descent L x0) (schedQS h) (schedDec h) g ξ K (0, x0))
            (schedDec h K
              (@OracleTemplate.StochasticGradient.roundsR (Point d) (Point d) ℝ (Point d) Ω (fun k => Fintype.card (secantSpace d (m k))) o.off (descent L x0)
                (schedQS h) (schedDec h) g ξ K (0, x0))
              (fun i => g (schedQS h K
                (@OracleTemplate.StochasticGradient.roundsR (Point d) (Point d) ℝ (Point d) Ω (fun k => Fintype.card (secantSpace d (m k))) o.off (descent L x0)
                  (schedQS h) (schedDec h) g ξ K (0, x0)) i) (ξ (o.off K + i.val))))
          = (K + 1, runSched (stepSched m hmM L g h) 0 (K + 1) x0
              (fun k : Fin (K + 1) => fun t : secantSpace d M =>
                ξ (schedIndex m o (K + 1) ⟨k, t⟩)))
      rw [ih, hround, runSched_snoc]
      simp only [Fin.castSucc]
      rw [hcon]
      simp only [Nat.zero_add]
      exact Prod.ext rfl rfl

lemma exec_aux {d M : ℕ} {m : ℕ → ℕ} (hd : 0 < d) {hmM : ∀ k, m k ≤ M} (hm : ∀ k, 0 < m k) (L h : ℝ)
    (x0 : Point d) (o : Offsets d m) (g : Point d → Ω → ℝ) (ξ : ℕ → Ω)
    (law : ProbabilityMeasure (ℕ → Ω)) (K : ℕ) :
    execute { Seed := fun _ => Ω, law := law, answer := fun _ (_, x) ω => g x ω }
      (batchedSched (fun k => Fintype.card (secantSpace d (m k)))
        (fun k => secant_card_pos hd (hm k)) (descent L x0) (schedQS h) (schedDec h) 0)
      (fun _ => o.off K) () ξ
      = runSched (stepSched m hmM L g h) 0 K x0
          (fun k : Fin K => fun t : secantSpace d M => ξ (schedIndex m o K ⟨k, t⟩)) := by
  classical
  refine (OracleTemplate.StochasticGradient.execute_batchedSched (h0 := o.zero) (hs := fun j => o.step j) (law := law)
    (K := K) (seed := ())).trans ?_
  rw [show (descent L x0).initial () = (0, x0) from rfl]
  exact ((congrArg (fun st => (descent L x0).output st)
      (roundsR_eq_runSched hmM L h x0 o g ξ K)).trans rfl)

lemma execute_schedDescent {d M : ℕ} {m : ℕ → ℕ} (hd : 0 < d) {hmM : ∀ k, m k ≤ M} (hm : ∀ k, 0 < m k)
    (L h : ℝ) (x0 : Point d) (o : Offsets d m) (g : Point d → Ω → ℝ) (ξ : ℕ → Ω)
    (law : ProbabilityMeasure (ℕ → Ω)) (K : ℕ) :
    execute { Seed := fun _ => Ω, law := law, answer := fun _ (_, x) ω => g x ω }
      (schedDescent hd hm L h x0) (fun _ => o.off K) () ξ
      = runSched (stepSched m hmM L g h) 0 K x0
          (fun k : Fin K => fun t : secantSpace d M => ξ (schedIndex m o K ⟨k, t⟩)) := by
  show execute { Seed := fun _ => Ω, law := law, answer := fun _ (_, x) ω => g x ω }
      (batchedSched (fun k => Fintype.card (secantSpace d (m k)))
        (fun k => secant_card_pos hd (hm k)) (descent L x0) (schedQS h) (schedDec h) 0)
      (fun _ => o.off K) () ξ = _
  exact exec_aux hd (hmM := hmM) hm L h x0 o g ξ law K

end OracleTemplate.SecantPolyak.Scheduled

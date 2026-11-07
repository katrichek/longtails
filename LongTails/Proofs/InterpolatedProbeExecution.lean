import LongTails.Algorithms.InterpolatedProbeDescent
import LongTails.Proofs.InterpolatedProbeStream
import LongTails.Proofs.SecantPolyakScheduledExecution
import LongTails.Proofs.DirectionMomentumExecution

set_option maxHeartbeats 2000000

/-!
Execution of mirrored-pair descent. Every round asks exactly two one-sided probes, so the slot
offsets are `off k = 2 * k`, and the decoded replies coincide cell by cell with the surrogate
`roundOf` analysed in the stream module.
-/

namespace OracleTemplate.SecantPolyak.Interpolated

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
open InexactGradient SecantDescent SecantPolyak SecantPolyak.Accelerated SecantPolyak.Scheduled
  SecantPolyak.Centered SecantPolyak.DirectionSampled
open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {Ω : Type} [MeasurableSpace Ω] {d : ℕ}

/-- The probe schedule of mirrored-pair descent: one mirrored pair per round. -/
def ipM : ℕ → ℕ := fun _ => 1

lemma ipM_pos : ∀ k, 0 < ipM k := fun _ => Nat.one_pos

lemma ipM_le : ∀ k, ipM k ≤ 1 := fun _ => Nat.le_refl 1

/-- With one mirrored pair per round the ambient cell map is the identity. -/
lemma cellInj_one (l : ℕ) (t : secantSpace 1 1) : cellInj (ipM_le l) t = t := by
  have h1 : (cellInj (ipM_le l) t).1 = t.1 := Subsingleton.elim _ _
  have h2 : (cellInj (ipM_le l) t).2 = t.2 := rfl
  exact Prod.ext h1 h2

/-- The slot offsets of mirrored-pair descent: two probes per round. -/
noncomputable def ipOffsets : Offsets 1 ipM where
  off := fun k => 2 * k
  zero := rfl
  step := fun j => by
    show 2 * (j + 1) = 2 * j + Fintype.card (secantSpace 1 1)
    rw [card_secantSpace]
    omega

omit [MeasurableSpace Ω] in
/-- Two flat streams that agree on the cells of the schedule give the same mirrored-pair run. -/
lemma ipRunSched_congr (η h : ℝ) (g : Point d → Ω → ℝ) (i K : ℕ) (x : Point d)
    (Ξ Ξ' : Fin K → secantSpace 1 1 → Point d × Ω)
    (hcell : ∀ (l : ℕ) (hi : i ≤ l) (t : secantSpace 1 1) (hl : l < i + K),
        Ξ ⟨l - i, by omega⟩ t = Ξ' ⟨l - i, by omega⟩ t) :
    runSched (ipStepSched g η h) i K x Ξ = runSched (ipStepSched g η h) i K x Ξ' := by
  classical
  induction K generalizing i x with
  | zero => rfl
  | succ K ih =>
      show runSched (ipStepSched g η h) (i + 1) K (ipStepSched g η h i x (Ξ 0))
            (fun j : Fin K => Ξ ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
        = runSched (ipStepSched g η h) (i + 1) K (ipStepSched g η h i x (Ξ' 0))
            (fun j : Fin K => Ξ' ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
      have hstep : ipStepSched g η h i x (Ξ 0) = ipStepSched g η h i x (Ξ' 0) := by
        refine congrArg (fun φ : secantSpace 1 1 → Point d × Ω => x - η • roundOf h g x 1 φ) ?_
        refine funext fun t => ?_
        have hpre := hcell i (Nat.le_refl i) t (by omega)
        rw [show (⟨i - i, by omega⟩ : Fin (K + 1)) = (0 : Fin (K + 1)) from
            Fin.ext (Nat.sub_self i)] at hpre
        exact hpre
      have hs : ∀ (l : ℕ) (hi : i + 1 ≤ l) (t : secantSpace 1 1) (hl : l < i + 1 + K),
          (fun j : Fin K => Ξ ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) ⟨l - (i + 1), by omega⟩ t
            = (fun j : Fin K => Ξ' ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
                ⟨l - (i + 1), by omega⟩ t := by
        intro l hi t hl
        have hp1 : l - i < K + 1 := by omega
        have hp2 : l - (i + 1) + 1 < K + 1 := by omega
        have hf' : (l - i : ℕ) = l - (i + 1) + 1 := by
          rw [← Nat.sub_sub, Nat.sub_add_cancel (show (1 : ℕ) ≤ l - i by omega)]
        have hf : (⟨l - i, hp1⟩ : Fin (K + 1)) = ⟨l - (i + 1) + 1, hp2⟩ := Fin.ext hf'
        have hpre := hcell l (Nat.le_trans (Nat.le_succ i) hi) t (by omega)
        rw [hf] at hpre
        exact hpre
      rw [ih (i + 1) (ipStepSched g η h i x (Ξ 0))
        (fun j : Fin K => Ξ ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
        (fun j : Fin K => Ξ' ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) hs, hstep]

omit [MeasurableSpace Ω] in
/-- One round of mirrored-pair descent, read off the executed algorithm. -/
lemma ip_upd (η h : ℝ) (x0 : Point d) (o : Offsets 1 ipM) (g : Point d → Ω → ℝ)
    (ξ : ℕ → Point d × Ω) :
    ∀ (k : ℕ) (s : Point d), (ipBase η x0).update (k, s) (ipDec h k (k, s)
        (fun i : Fin (Fintype.card (secantSpace 1 1)) =>
          dirAns h g (ipQS k (k, s) i) (ξ (o.off k + i.val))))
      = (k + 1, ipStepSched g η h k s (fun t : secantSpace 1 1 =>
          ξ (o.off k + (Fintype.equivFin (secantSpace 1 1) t).val))) := by
  intro k s
  refine Prod.ext rfl ?_
  have hsum : ipDec h k (k, s) (fun i : Fin (Fintype.card (secantSpace 1 1)) =>
        dirAns h g (ipQS k (k, s) i) (ξ (o.off k + i.val)))
      = roundOf h g s 1 (fun t : secantSpace 1 1 =>
          ξ (o.off k + (Fintype.equivFin (secantSpace 1 1) t).val)) := by
    show ∑ t : secantSpace 1 1, (if secantSign t then (1 : ℝ) else (-1 : ℝ)) •
          term h (dirAns h g (s, secantSign (secantSlot (Fintype.equivFin (secantSpace 1 1) t)))
            (ξ (o.off k + (Fintype.equivFin (secantSpace 1 1) t).val))) = _
    simp only [secantSlot_equivFin, secantSign, term, dirAns, rawReply, roundOf, slotVal,
      Nat.cast_one, div_one, one_smul]
    apply Finset.sum_congr rfl
    intro t _
    rfl
  rw [hsum]
  rfl

omit [MeasurableSpace Ω] in
/-- Running `K` mirrored-pair rounds on the flat oracle stream reproduces the analysed run. -/
lemma ip_roundsR_eq_runSched (η h : ℝ) (x0 : Point d) (o : Offsets 1 ipM)
    (g : Point d → Ω → ℝ) (ξ : ℕ → Point d × Ω) :
    ∀ K : ℕ, StochasticGradient.roundsR o.off (ipBase η x0) ipQS (ipDec h) (dirAns h g) ξ K
        (0, x0)
      = (K, runSched (ipStepSched g η h) 0 K x0 (fun k : Fin K => fun t : secantSpace 1 1 =>
          ξ (schedIndex (d := 1) (M := 1) ipM o K ⟨k, t⟩))) := by
  classical
  intro K
  induction K with
  | zero => rfl
  | succ K ih =>
      have hidx : (fun t : secantSpace 1 1 =>
          ξ (schedIndex (d := 1) (M := 1) ipM o (K + 1) ⟨⟨K, Nat.lt_succ_self K⟩, t⟩))
          = (fun t : secantSpace 1 1 =>
            ξ (o.off K + (Fintype.equivFin (secantSpace 1 1) t).val)) := by
        refine funext fun t => congrArg ξ ?_
        have h1 := Scheduled.schedIndex_cellInj o (K + 1) K (Nat.lt_succ_self K) (ipM_le K) t
        rw [cellInj_one K t] at h1
        exact h1
      have hcon : runSched (ipStepSched g η h) 0 K x0
            (fun j : Fin K => fun t : secantSpace 1 1 =>
              ξ (schedIndex (d := 1) (M := 1) ipM o (K + 1) ⟨Fin.castAdd 1 j, t⟩))
          = runSched (ipStepSched g η h) 0 K x0
            (fun k : Fin K => fun t : secantSpace 1 1 =>
              ξ (schedIndex (d := 1) (M := 1) ipM o K ⟨k, t⟩)) := by
        refine ipRunSched_congr η h g 0 K x0 _ _ ?_
        intro l hi t hl
        show ξ (schedIndex (d := 1) (M := 1) ipM o (K + 1) (Fin.castAdd 1 ⟨l - 0, _⟩, t))
          = ξ (schedIndex (d := 1) (M := 1) ipM o K (⟨l - 0, _⟩, t))
        have h1 := Scheduled.schedIndex_cellInj o (K + 1) l (by omega) (ipM_le l) t
        have h2 := Scheduled.schedIndex_cellInj o K l (by omega) (ipM_le l) t
        rw [cellInj_one l t] at h1 h2
        exact congrArg ξ (h1.trans h2.symm)
      show (ipBase η x0).update
            (StochasticGradient.roundsR o.off (ipBase η x0) ipQS (ipDec h) (dirAns h g) ξ K (0, x0))
            (ipDec h K
              (StochasticGradient.roundsR o.off (ipBase η x0) ipQS (ipDec h) (dirAns h g) ξ K
                (0, x0))
              (fun i => dirAns h g (ipQS K
                (StochasticGradient.roundsR o.off (ipBase η x0) ipQS (ipDec h) (dirAns h g) ξ K
                  (0, x0)) i) (ξ (o.off K + i.val))))
          = (K + 1, runSched (ipStepSched g η h) 0 (K + 1) x0 (fun k : Fin (K + 1) =>
              fun t : secantSpace 1 1 => ξ (schedIndex (d := 1) (M := 1) ipM o (K + 1) ⟨k, t⟩)))
      rw [ih, ip_upd η h x0 o g ξ K, ← hidx, runSched_snoc]
      simp only [Fin.castSucc, Nat.zero_add]
      rw [hcon]

/-- The executed mirrored-pair algorithm coincides with the analysed run. -/
lemma ip_execute (η h : ℝ) (x0 : Point d) (o : Offsets 1 ipM) (g : Point d → Ω → ℝ)
    (ξ : ℕ → Point d × Ω) (law : ProbabilityMeasure (ℕ → Point d × Ω)) (K : ℕ) :
    execute (dirOracle h g law) (ipDescent η h x0) (fun _ => o.off K) () ξ
      = runSched (ipStepSched g η h) 0 K x0 (fun k : Fin K => fun t : secantSpace 1 1 =>
          ξ (schedIndex (d := 1) (M := 1) ipM o K ⟨k, t⟩)) := by
  classical
  have h1 : execute (dirOracle h g law) (ipDescent η h x0) (fun _ => o.off K) () ξ
      = (ipBase η x0).output
        (StochasticGradient.roundsR o.off (ipBase η x0) ipQS (ipDec h) (dirAns h g) ξ K
          ((ipBase η x0).initial ())) :=
    StochasticGradient.execute_batchedSched (n := fun _ => roundSlots 1 1)
      (hn := fun _ => secant_card_pos (show 0 < 1 from Nat.zero_lt_one) Nat.one_pos)
      (A := ipBase η x0) (queries := ipQS) (decode := ipDec h)
      (zero := ((0 : ℝ), (0 : Point d))) (g := dirAns h g) (ξ := ξ) (h0 := o.zero) (hs := o.step)
      (law := law) (K := K) (seed := ())
  rw [h1]
  rw [show (ipBase η x0).initial () = (0, x0) from rfl]
  rw [ip_roundsR_eq_runSched η h x0 o g ξ K]
  rfl

/-- Expected smoothed accuracy of the executed mirrored-pair algorithm. -/
lemma ip_exec_accuracy {K : ℕ} {g : Point d → Ω → ℝ} {fh : Point d → ℝ}
    {W : Measure (Point d × Ω)} [IsProbabilityMeasure W]
    {L μ η h ρ : ℝ} {x0 xh : Point d}
    (hL : 0 < L) (hμ : 0 < μ) (hη0 : 0 ≤ η) (hηL : L * η ≤ 1) (hημ : η * μ ≤ 1)
    (hηr : L * η * ρ ^ 2 ≤ μ / 2)
    (hg : Measurable (Function.uncurry g))
    (hgr : ∀ x, HasGradientAt fh (gradient fh x) x)
    (hlip : ∀ x y, ‖gradient fh x - gradient fh y‖ ≤ L * ‖x - y‖)
    (hsc : ∀ x y, fh x + ⟪gradient fh x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ fh y)
    (hminh : IsMinOn fh Set.univ xh)
    (hint : ∀ x s, Integrable (fun u : Point d × Ω =>
        slotVal h g x s u - halfGrad fh x s) W)
    (hmean : ∀ x s, (∫ u : Point d × Ω, slotVal h g x s u ∂W) = halfGrad fh x s)
    (hvar2 : ∀ x s, Integrable (fun u : Point d × Ω =>
        ‖slotVal h g x s u - halfGrad fh x s‖ ^ 2) W)
    (hvar : ∀ x s, (∫ u : Point d × Ω, ‖slotVal h g x s u - halfGrad fh x s‖ ^ 2 ∂W)
        ≤ ρ ^ 2 * (fh x - fh xh))
    (P : ProbabilityMeasure (ℕ → Point d × Ω))
    (hind : iIndepFun (fun k (ξ : ℕ → Point d × Ω) => ξ k) (P : Measure _))
    (hmarg : ∀ k, (P : Measure _).map (fun ξ : ℕ → Point d × Ω => ξ k)
        = (W : Measure (Point d × Ω)))
    (o : Offsets 1 ipM) :
    Integrable (fun ξ : ℕ → Point d × Ω =>
        fh (execute (dirOracle h g P) (ipDescent η h x0) (fun _ => o.off K) () ξ) - fh xh)
        (P : Measure _) ∧
      (∫ ξ : ℕ → Point d × Ω,
          fh (execute (dirOracle h g P) (ipDescent η h x0) (fun _ => o.off K) () ξ) - fh xh
          ∂(P : Measure (ℕ → Point d × Ω))) ≤ (1 - η * μ / 2) ^ K * (fh x0 - fh xh) := by
  classical
  obtain ⟨hgapInt, hgapb⟩ := ip_stream_gap (g := g) (fh := fh) (W := W) (L := L) (μ := μ)
    (η := η) (h := h) (ρ := ρ) (x0 := x0) (xh := xh) (K := K) hL hμ hη0 hηL hημ hηr hg hgr hlip hsc
    hminh hint hmean hvar2 hvar
  have hpre := sched_stream_law_curry (d := 1) (M := 1) ipM o K P hind hmarg
  set Φ : (Fin K → secantSpace 1 1 → Point d × Ω) → ℝ := fun Ξ =>
    fh (runSched (ipStepSched g η h) 0 K x0 Ξ) - fh xh with hΦdef
  set Q : (ℕ → Point d × Ω) → (Fin K → secantSpace 1 1 → Point d × Ω) := fun ξ =>
    fun k : Fin K => fun t : secantSpace 1 1 =>
      ξ (schedIndex (d := 1) (M := 1) ipM o K ⟨k, t⟩) with hQdef
  have hcomp : (fun ξ : ℕ → Point d × Ω =>
        fh (execute (dirOracle h g P) (ipDescent η h x0) (fun _ => o.off K) () ξ) - fh xh)
      = Φ ∘ Q := by
    refine funext fun ξ => congrArg (fun v => fh v - fh xh) (ip_execute η h x0 o g ξ P K)
  have hpush : (∫ ξ : ℕ → Point d × Ω, (Φ ∘ Q) ξ ∂(P : Measure _))
      = ∫ Ξ, Φ Ξ ∂Measure.pi (fun _ : Fin K => slotLaw 1 1 W) :=
    ZerothOrder.integral_comp_preserving (q := Q) hpre hgapInt
  refine ⟨hcomp.symm ▸ (hpre.integrable_comp_of_integrable (ε := ℝ) (g := Φ) hgapInt),
    le_of_eq_of_le
      (congrArg (fun F : (ℕ → Point d × Ω) → ℝ => ∫ ξ : ℕ → Point d × Ω, F ξ ∂(P : Measure _))
        hcomp) ?_⟩
  rw [hpush]
  exact hgapb

end OracleTemplate.SecantPolyak.Interpolated

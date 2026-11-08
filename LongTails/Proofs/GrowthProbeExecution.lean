import LongTails.Algorithms.GrowthProbeAveragedDescent
import LongTails.Proofs.GrowthProbeAccuracy
import LongTails.Proofs.InterpolatedProbeExecution

set_option maxHeartbeats 4000000

/-!
Execution of averaged probe descent. Each round asks exactly two one-sided probes, so the slot
offsets are `off k = 2 * k` and the decoded replies coincide cell by cell with the surrogate
`roundOf` analysed in the stream module. The executed state carries the running sum of visited
points, so its output is the average of the iterates.
-/

namespace OracleTemplate.SecantPolyak.GrowthConvex

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
open InexactGradient SecantDescent SecantPolyak SecantPolyak.Scheduled
  SecantPolyak.Centered SecantPolyak.DirectionSampled
open OracleTemplate.SecantPolyak.Interpolated (ipM ipM_pos ipM_le ipOffsets cellInj_one)
open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {Ω : Type} [MeasurableSpace Ω] {d : ℕ}

/-- One averaged probe descent round read off the executed state: advance the counter, move against
the mirrored-pair surrogate, and add the current point to the running sum. -/
noncomputable def gpAlgStep (η h : ℝ) (g : Point d → Ω → ℝ) :
    ℕ → (ℕ × Point d × Point d) → (secantSpace 1 1 → Point d × Ω) → (ℕ × Point d × Point d) :=
  fun _ s Ξ => (s.1 + 1, s.2.1 - η • roundOf h g s.2.1 1 Ξ, s.2.2 + s.2.1)

omit [MeasurableSpace Ω] in
/-- The counter, iterate and running sum of the executed state after `K` rounds: the point and the
sum agree with the components of the analysed run, whatever accumulated gap one starts from. -/
lemma gp_alg_eq (η h : ℝ) (g : Point d → Ω → ℝ) (fh : Point d → ℝ) (xh : Point d) :
    ∀ (K i : ℕ) (s : ℕ × Point d × Point d) (b : ℝ)
      (Ξ : Fin K → secantSpace 1 1 → Point d × Ω),
      runSched (gpAlgStep η h g) i K s Ξ
        = (s.1 + K, (runSched (gpStep g fh xh η h) i K (s.2.1, s.2.2, b) Ξ).1,
          (runSched (gpStep g fh xh η h) i K (s.2.1, s.2.2, b) Ξ).2.1) := by
  intro K
  induction K with
  | zero => intro i s b Ξ; simp [runSched]
  | succ K ih =>
      intro i s b Ξ
      show runSched (gpAlgStep η h g) (i + 1) K (gpAlgStep η h g i s (Ξ 0)) (fun j => Ξ j.succ)
        = (s.1 + (K + 1),
            (runSched (gpStep g fh xh η h) (i + 1) K
                (gpStep g fh xh η h i (s.2.1, s.2.2, b) (Ξ 0)) (fun j => Ξ j.succ)).1,
            (runSched (gpStep g fh xh η h) (i + 1) K
                (gpStep g fh xh η h i (s.2.1, s.2.2, b) (Ξ 0)) (fun j => Ξ j.succ)).2.1)
      rw [ih (i + 1) (gpAlgStep η h g i s (Ξ 0))
        ((gpStep g fh xh η h i (s.2.1, s.2.2, b) (Ξ 0)).2.2) (fun j => Ξ j.succ)]
      refine Prod.ext ?_ (Prod.ext rfl rfl)
      show (s.1 + 1) + K = s.1 + (K + 1)
      omega

omit [MeasurableSpace Ω] in
/-- One executed round decodes to the mirrored-pair surrogate and updates the executed state. -/
lemma gp_upd (η h : ℝ) (x0 : Point d) (o : Offsets 1 ipM) (g : Point d → Ω → ℝ)
    (ξ : ℕ → Point d × Ω) (k : ℕ) (s : ℕ × Point d × Point d) :
    (gpBase η x0).update s (gpDec h k s
        (fun i : Fin (Fintype.card (secantSpace 1 1)) =>
          dirAns h g (gpQS k s i) (ξ (o.off k + i.val))))
      = (s.1 + 1, s.2.1 - η • roundOf h g s.2.1 1
          (fun t : secantSpace 1 1 => ξ (o.off k + (Fintype.equivFin (secantSpace 1 1) t).val)),
          s.2.2 + s.2.1) := by
  show (s.1 + 1,
        (s.2.1 - η • gpDec h k s
          (fun i : Fin (Fintype.card (secantSpace 1 1)) => dirAns h g (gpQS k s i)
            (ξ (o.off k + i.val))), s.2.2 + s.2.1))
      = (s.1 + 1,
        (s.2.1 - η • roundOf h g s.2.1 1
          (fun t : secantSpace 1 1 => ξ (o.off k + (Fintype.equivFin (secantSpace 1 1) t).val)),
          s.2.2 + s.2.1))
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  have hsum : gpDec h k s (fun i : Fin (Fintype.card (secantSpace 1 1)) =>
        dirAns h g (gpQS k s i) (ξ (o.off k + i.val)))
      = roundOf h g s.2.1 1 (fun t : secantSpace 1 1 =>
          ξ (o.off k + (Fintype.equivFin (secantSpace 1 1) t).val)) := by
    show ∑ t : secantSpace 1 1, (if secantSign t then (1 : ℝ) else (-1 : ℝ)) •
          term h (dirAns h g (s.2.1,
            secantSign (secantSlot (Fintype.equivFin (secantSpace 1 1) t)))
            (ξ (o.off k + (Fintype.equivFin (secantSpace 1 1) t).val))) = _
    simp only [secantSlot_equivFin, secantSign, term, dirAns, rawReply, roundOf, slotVal,
      Nat.cast_one, div_one, one_smul]
    apply Finset.sum_congr rfl
    intro t _
    rfl
  rw [hsum]

omit [MeasurableSpace Ω] in
/-- Running `K` averaged probe descent rounds on the flat oracle stream reproduces the analysed
recursion. -/
lemma gp_roundsR_eq (η h : ℝ) (x0 : Point d) (o : Offsets 1 ipM) (g : Point d → Ω → ℝ)
    (ξ : ℕ → Point d × Ω) :
    ∀ K : ℕ,
      StochasticGradient.roundsR o.off (gpBase η x0) gpQS (gpDec h) (dirAns h g) ξ K (0, x0, 0)
        = runSched (gpAlgStep η h g) 0 K (0, x0, 0)
            (fun k : Fin K => fun t : secantSpace 1 1 =>
              ξ (schedIndex (d := 1) (M := 1) ipM o K ⟨k, t⟩)) := by
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
      have htail : (fun j : Fin K => fun t : secantSpace 1 1 =>
            ξ (schedIndex (d := 1) (M := 1) ipM o (K + 1) ⟨Fin.castSucc j, t⟩))
          = (fun k : Fin K => fun t : secantSpace 1 1 =>
            ξ (schedIndex (d := 1) (M := 1) ipM o K ⟨k, t⟩)) := by
        refine funext fun k => funext fun t => congrArg ξ ?_
        have hkn : (k : ℕ) < K + 1 := by
          have hk := k.isLt
          omega
        have h1 := Scheduled.schedIndex_cellInj o (K + 1) k.val hkn (ipM_le k.val) t
        have h2 := Scheduled.schedIndex_cellInj o K k.val k.isLt (ipM_le k.val) t
        rw [cellInj_one k.val t] at h1 h2
        exact h1.trans h2.symm
      show StochasticGradient.roundsR o.off (gpBase η x0) gpQS (gpDec h) (dirAns h g) ξ (K + 1)
            (0, x0, 0)
          = runSched (gpAlgStep η h g) 0 (K + 1) (0, x0, 0)
              (fun k : Fin (K + 1) => fun t : secantSpace 1 1 =>
                ξ (schedIndex (d := 1) (M := 1) ipM o (K + 1) ⟨k, t⟩))
      show (gpBase η x0).update
            (StochasticGradient.roundsR o.off (gpBase η x0) gpQS (gpDec h) (dirAns h g) ξ K
              (0, x0, 0))
            (gpDec h K
              (StochasticGradient.roundsR o.off (gpBase η x0) gpQS (gpDec h) (dirAns h g) ξ K
                (0, x0, 0))
              (fun i => dirAns h g (gpQS K
                (StochasticGradient.roundsR o.off (gpBase η x0) gpQS (gpDec h) (dirAns h g) ξ K
                  (0, x0, 0)) i) (ξ (o.off K + i.val))))
          = runSched (gpAlgStep η h g) 0 (K + 1) (0, x0, 0)
              (fun k : Fin (K + 1) => fun t : secantSpace 1 1 =>
                ξ (schedIndex (d := 1) (M := 1) ipM o (K + 1) ⟨k, t⟩))
      rw [runSched_snoc, htail, ← ih]
      rw [gp_upd η h x0 o g ξ K
        (StochasticGradient.roundsR o.off (gpBase η x0) gpQS (gpDec h) (dirAns h g) ξ K
          (0, x0, 0)), ← hidx]
      simp only [gpAlgStep]
      exact Prod.ext rfl (Prod.ext rfl rfl)


/-- The output of the executed algorithm is the average of the visited points. -/
lemma gp_execute (η h : ℝ) (x0 : Point d) (fh : Point d → ℝ) (xh : Point d)
    (o : Offsets 1 ipM) (g : Point d → Ω → ℝ) (ξ : ℕ → Point d × Ω)
    (law : ProbabilityMeasure (ℕ → Point d × Ω)) (K : ℕ) :
    execute (dirOracle h g law) (gpDescent η h x0) (fun _ => o.off K) () ξ
      = (1 / max 1 (K : ℝ)) •
          (runSched (gpStep g fh xh η h) 0 K (x0, (0 : Point d), (0 : ℝ))
            (fun k : Fin K => fun t : secantSpace 1 1 =>
              ξ (schedIndex (d := 1) (M := 1) ipM o K ⟨k, t⟩))).2.1 := by
  classical
  have h1 : execute (dirOracle h g law) (gpDescent η h x0) (fun _ => o.off K) () ξ
      = (gpBase η x0).output
        (StochasticGradient.roundsR o.off (gpBase η x0) gpQS (gpDec h) (dirAns h g) ξ K
          ((gpBase η x0).initial ())) :=
    StochasticGradient.execute_batchedSched (n := fun _ => roundSlots 1 1)
      (hn := fun _ => secant_card_pos (show 0 < 1 from Nat.zero_lt_one) Nat.one_pos)
      (A := gpBase η x0) (queries := gpQS) (decode := gpDec h)
      (zero := ((0 : ℝ), (0 : Point d))) (g := dirAns h g) (ξ := ξ) (h0 := o.zero) (hs := o.step)
      (law := law) (K := K) (seed := ())
  rw [h1]
  rw [show (gpBase η x0).initial () = (0, x0, 0) from rfl]
  rw [gp_roundsR_eq η h x0 o g ξ K,
    gp_alg_eq (η := η) (h := h) (g := g) (fh := fh) (xh := xh) K 0 (0, x0, 0) 0]
  have ho : (gpBase η x0).output = fun s => (1 / max 1 (s.1 : ℝ)) • s.2.2 := rfl
  rw [ho]
  simp only [Nat.zero_add]

/-- Expected smoothed gap of the averaged output of the executed algorithm. -/
lemma gp_exec_accuracy {K : ℕ} {g : Point d → Ω → ℝ} {fh : Point d → ℝ}
    {W : Measure (Point d × Ω)} [hW : IsProbabilityMeasure W] {L ρ η h : ℝ} {x0 xh : Point d}
    (M : GPHyp g fh xh L ρ η h W) (hK : 0 < K) (hηp : 0 < η)
    (P : ProbabilityMeasure (ℕ → Point d × Ω))
    (hind : iIndepFun (fun k (ξ : ℕ → Point d × Ω) => ξ k) (P : Measure _))
    (hmarg : ∀ k, (P : Measure _).map (fun ξ : ℕ → Point d × Ω => ξ k)
        = (W : Measure (Point d × Ω))) (o : Offsets 1 ipM) :
    Integrable (fun ξ : ℕ → Point d × Ω =>
        fh (execute (dirOracle h g P) (gpDescent η h x0) (fun _ => o.off K) () ξ) - fh xh)
        (P : Measure _) ∧
      (∫ ξ : ℕ → Point d × Ω,
          fh (execute (dirOracle h g P) (gpDescent η h x0) (fun _ => o.off K) () ξ) - fh xh
          ∂(P : Measure (ℕ → Point d × Ω))) ≤ ‖x0 - xh‖ ^ 2 / (η * (K : ℝ)) := by
  classical
  have hacc := gp_stream_accuracy (g := g) (fh := fh) (xh := xh) (L := L) (ρ := ρ) (η := η)
    (h := h) (M := M) (K := K) hK hηp x0
  have hpre := sched_stream_law_curry (d := 1) (M := 1) ipM o K P hind hmarg
  set Φ : (Fin K → secantSpace 1 1 → Point d × Ω) → ℝ := fun Ξ =>
    fh ((1 / (K : ℝ)) • (runSched (gpStep g fh xh η h) 0 K (x0, (0 : Point d), (0 : ℝ)) Ξ).2.1)
      - fh xh with hΦdef
  set Q : (ℕ → Point d × Ω) → (Fin K → secantSpace 1 1 → Point d × Ω) := fun ξ =>
    fun k : Fin K => fun t : secantSpace 1 1 =>
      ξ (schedIndex (d := 1) (M := 1) ipM o K ⟨k, t⟩) with hQdef
  have hmax : (1 / max 1 (K : ℝ)) = (1 / (K : ℝ) : ℝ) := by
    have hz : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hK)
    rw [max_eq_right hz]
  have hcomp : (fun ξ : ℕ → Point d × Ω =>
        fh (execute (dirOracle h g P) (gpDescent η h x0) (fun _ => o.off K) () ξ) - fh xh)
      = Φ ∘ Q := by
    refine funext fun ξ => congrArg (fun v => fh v - fh xh) ?_
    rw [gp_execute η h x0 fh xh o g ξ P K, hmax]
  have hpush : (∫ ξ : ℕ → Point d × Ω, (Φ ∘ Q) ξ ∂(P : Measure _))
      = ∫ Ξ, Φ Ξ ∂Measure.pi (fun _ : Fin K => slotLaw 1 1 W) :=
    ZerothOrder.integral_comp_preserving (q := Q) hpre hacc.1
  refine ⟨hcomp.symm ▸ (hpre.integrable_comp_of_integrable (ε := ℝ) (g := Φ) ?_),
    le_of_eq_of_le
      (congrArg (fun F : (ℕ → Point d × Ω) → ℝ => ∫ ξ : ℕ → Point d × Ω, F ξ ∂(P : Measure _))
        hcomp) ?_⟩
  · exact hacc.1
  · rw [hpush]
    simpa [Φ] using hacc.2

end OracleTemplate.SecantPolyak.GrowthConvex

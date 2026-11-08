import LongTails.Algorithms.GradedAnchoredPairAcceleration
import LongTails.Proofs.GradedAnchoredStream
import LongTails.Proofs.SecantPolyakScheduledExecution
import LongTails.Proofs.DirectionMomentumExecution

set_option maxHeartbeats 2000000

/-!
Execution of weighted anchored pair acceleration. Every round asks `2 * m` one-sided probes at the
interpolated point along `m` directions, so the slot offsets are `off k = 2 * m * k`, and the decoded
replies coincide cell by cell with the batched surrogate `roundOf` analysed in the stream module. The
reported iterate is the first component of the scheduled state.
-/

namespace OracleTemplate.SecantPolyak.GradedAnchored

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
open InexactGradient SecantDescent SecantPolyak SecantPolyak.Accelerated SecantPolyak.Scheduled
  SecantPolyak.Centered SecantPolyak.DirectionSampled Interpolated
open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {Ω : Type} [MeasurableSpace Ω] {d : ℕ}

/-- The probe schedule of weighted anchored pair acceleration: `m` mirrored pairs per round. -/
@[reducible] def agM (m : ℕ) : ℕ → ℕ := fun _ => m

lemma agM_le (m : ℕ) {k : ℕ} : agM m k ≤ m := Nat.le_refl m



/-- The slot offsets of weighted anchored pair acceleration: `2 * m` probes per round. -/
noncomputable def agOffsets (m : ℕ) : Offsets 1 (agM m) where
  off := fun k => 2 * m * k
  zero := rfl
  step := fun j => by
    show 2 * m * (j + 1) = 2 * m * j + Fintype.card (secantSpace 1 m)
    rw [card_secantSpace]
    ring

omit [MeasurableSpace Ω] in
/-- Two flat streams that agree on the cells of the schedule give the same anchored run. -/
lemma agRunSched_congr (m : ℕ) (β θ η h : ℝ) (g : Point d → Ω → ℝ) (i K : ℕ) (s : Point d × Point d)
    (Ξ Ξ' : Fin K → secantSpace 1 m → Point d × Ω)
    (hcell : ∀ (l : ℕ) (hi : i ≤ l) (t : secantSpace 1 m) (hl : l < i + K),
        Ξ ⟨l - i, by omega⟩ t = Ξ' ⟨l - i, by omega⟩ t) :
    runSched (waStepSched β θ η g h m) i K s Ξ = runSched (waStepSched β θ η g h m) i K s Ξ' := by
  classical
  induction K generalizing i s with
  | zero => rfl
  | succ K ih =>
      show runSched (waStepSched β θ η g h m) (i + 1) K (waStepSched β θ η g h m i s (Ξ 0))
            (fun j : Fin K => Ξ ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
        = runSched (waStepSched β θ η g h m) (i + 1) K (waStepSched β θ η g h m i s (Ξ' 0))
            (fun j : Fin K => Ξ' ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
      have hstep : waStepSched β θ η g h m i s (Ξ 0) = waStepSched β θ η g h m i s (Ξ' 0) := by
        refine congrArg (fun φ : secantSpace 1 m → Point d × Ω =>
          waStep β θ η s (roundOf h g (query θ s) m φ)) ?_
        refine funext fun t => ?_
        have hpre := hcell i (Nat.le_refl i) t (by omega)
        rw [show (⟨i - i, by omega⟩ : Fin (K + 1)) = (0 : Fin (K + 1)) from
            Fin.ext (Nat.sub_self i)] at hpre
        exact hpre
      have hs : ∀ (l : ℕ) (hi : i + 1 ≤ l) (t : secantSpace 1 m) (hl : l < i + 1 + K),
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
      rw [ih (i + 1) (waStepSched β θ η g h m i s (Ξ 0))
        (fun j : Fin K => Ξ ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
        (fun j : Fin K => Ξ' ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) hs, hstep]

omit [MeasurableSpace Ω] in
/-- One round of damped anchored pair acceleration, read off the executed algorithm. -/
lemma ag_upd (m : ℕ) (β θ η h : ℝ) (x0 : Point d) (o : Offsets 1 (agM m)) (g : Point d → Ω → ℝ)
    (ξ : ℕ → Point d × Ω) :
    ∀ (k : ℕ) (s : Point d × Point d),
      (agBase β θ η x0).update (k, s) (agDec (m := agM m) h k (k, s)
          (fun i : Fin (Fintype.card (secantSpace 1 m)) =>
            dirAns h g (agQS (m := agM m) θ k (k, s) i) (ξ (o.off k + i.val))))
        = (k + 1, waStepSched β θ η g h m k s (fun t : secantSpace 1 m =>
            ξ (o.off k + (Fintype.equivFin (secantSpace 1 m) t).val))) := by
  intro k s
  refine Prod.ext rfl ?_
  have hsum : agDec (m := agM m) h k (k, s) (fun i : Fin (Fintype.card (secantSpace 1 m)) =>
        dirAns h g (agQS (m := agM m) θ k (k, s) i) (ξ (o.off k + i.val)))
      = roundOf h g (query θ s) m (fun t : secantSpace 1 m =>
          ξ (o.off k + (Fintype.equivFin (secantSpace 1 m) t).val)) := by
    classical
    unfold agDec agQS agM
    refine congrArg (fun u : Point d => (1 / (m : ℝ)) • u) ?_
    refine Finset.sum_congr rfl (fun t _ => ?_)
    simp only [secantSign, term, dirAns, rawReply, slotVal, secantSlot_equivFin]
    exact rfl
  rw [hsum]
  rfl

omit [MeasurableSpace Ω] in
/-- Running `K` damped anchored rounds on the flat oracle stream reproduces the analysed run. -/
lemma ag_roundsR_eq_runSched (m : ℕ) (β θ η h : ℝ) (x0 : Point d) (o : Offsets 1 (agM m))
    (g : Point d → Ω → ℝ) (ξ : ℕ → Point d × Ω) :
    ∀ K : ℕ,
      StochasticGradient.roundsR o.off (agBase β θ η x0) (agQS (m := agM m) θ) (agDec (m := agM m) h) (dirAns h g) ξ K
          (0, (x0, x0))
        = (K, runSched (waStepSched β θ η g h m) 0 K (x0, x0)
            (fun k : Fin K => fun t : secantSpace 1 m =>
              ξ (schedIndex (d := 1) (M := m) (agM m) o K ⟨k, t⟩))) := by
  classical
  intro K
  induction K with
  | zero => rfl
  | succ K ih =>
      have hidx : (fun t : secantSpace 1 m =>
          ξ (schedIndex (d := 1) (M := m) (agM m) o (K + 1) ⟨⟨K, Nat.lt_succ_self K⟩, t⟩))
          = (fun t : secantSpace 1 m =>
            ξ (o.off K + (Fintype.equivFin (secantSpace 1 m) t).val)) := by
        refine funext fun t => congrArg ξ ?_
        have h1 := Scheduled.schedIndex_cellInj o (K + 1) K (Nat.lt_succ_self K) (agM_le m) t
        show schedIndex (agM m) o (K + 1) (⟨K, Nat.lt_succ_self K⟩, t)
            = o.off K + (Fintype.equivFin (secantSpace 1 m) t).val
        exact h1
      have hcon : runSched (waStepSched β θ η g h m) 0 K (x0, x0)
            (fun j : Fin K => fun t : secantSpace 1 m =>
              ξ (schedIndex (d := 1) (M := m) (agM m) o (K + 1) ⟨Fin.castAdd 1 j, t⟩))
          = runSched (waStepSched β θ η g h m) 0 K (x0, x0)
            (fun k : Fin K => fun t : secantSpace 1 m =>
              ξ (schedIndex (d := 1) (M := m) (agM m) o K ⟨k, t⟩)) := by
        refine agRunSched_congr m β θ η h g 0 K (x0, x0) _ _ ?_
        intro l hi t hl
        show ξ (schedIndex (d := 1) (M := m) (agM m) o (K + 1) (Fin.castAdd 1 ⟨l - 0, _⟩, t))
          = ξ (schedIndex (d := 1) (M := m) (agM m) o K (⟨l - 0, _⟩, t))
        have h1 := Scheduled.schedIndex_cellInj o (K + 1) l (by omega) (agM_le m) t
        have h2 := Scheduled.schedIndex_cellInj o K l (by omega) (agM_le m) t
        rw [cellInj_refl_any] at h1 h2
        exact congrArg ξ (h1.trans h2.symm)
      show (agBase β θ η x0).update
            (StochasticGradient.roundsR o.off (agBase β θ η x0) (agQS (m := agM m) θ) (agDec (m := agM m) h) (dirAns h g) ξ K
              (0, (x0, x0)))
            (agDec (m := agM m) h K
              (StochasticGradient.roundsR o.off (agBase β θ η x0) (agQS (m := agM m) θ) (agDec (m := agM m) h) (dirAns h g) ξ
                K (0, (x0, x0)))
              (fun i => dirAns h g (agQS (m := agM m) θ K
                (StochasticGradient.roundsR o.off (agBase β θ η x0) (agQS (m := agM m) θ) (agDec (m := agM m) h)
                  (dirAns h g) ξ K (0, (x0, x0))) i) (ξ (o.off K + i.val))))
          = (K + 1, runSched (waStepSched β θ η g h m) 0 (K + 1) (x0, x0)
              (fun k : Fin (K + 1) => fun t : secantSpace 1 m =>
                ξ (schedIndex (d := 1) (M := m) (agM m) o (K + 1) ⟨k, t⟩)))
      rw [ih, ag_upd m β θ η h x0 o g ξ K, ← hidx, runSched_snoc]
      simp only [Fin.castSucc, Nat.zero_add]
      rw [hcon]

/-- The executed damped anchored algorithm coincides with the analysed run. -/
lemma ag_execute (m : ℕ) (hm : 0 < m) (β θ η h : ℝ) (x0 : Point d) (o : Offsets 1 (agM m)) (g : Point d → Ω → ℝ)
    (ξ : ℕ → Point d × Ω) (law : ProbabilityMeasure (ℕ → Point d × Ω)) (K : ℕ) :
    execute (dirOracle h g law) (agDescent (m := agM m) (show ∀ k, 0 < agM m k from fun _ => hm) β θ η h x0) (fun _ => o.off K) () ξ
      = (runSched (waStepSched β θ η g h m) 0 K (x0, x0)
          (fun k : Fin K => fun t : secantSpace 1 m =>
            ξ (schedIndex (d := 1) (M := m) (agM m) o K ⟨k, t⟩))).1 := by
  classical
  have h1 : execute (dirOracle h g law) (agDescent (m := agM m) (show ∀ k, 0 < agM m k from fun _ => hm) β θ η h x0) (fun _ => o.off K) () ξ
      = (agBase β θ η x0).output
        (StochasticGradient.roundsR o.off (agBase β θ η x0) (agQS (m := agM m) θ) (agDec (m := agM m) h) (dirAns h g) ξ K
          ((agBase β θ η x0).initial ())) :=
    StochasticGradient.execute_batchedSched (n := fun _ => roundSlots 1 m)
      (hn := fun _ => secant_card_pos (show 0 < 1 from Nat.zero_lt_one) hm)
      (A := agBase β θ η x0) (queries := agQS (m := agM m) θ) (decode := agDec (m := agM m) h)
      (zero := ((0 : ℝ), (0 : Point d))) (g := dirAns h g) (ξ := ξ) (h0 := o.zero) (hs := o.step)
      (law := law) (K := K) (seed := ())
  rw [h1]
  rw [show (agBase β θ η x0).initial () = (0, (x0, x0)) from rfl]
  rw [ag_roundsR_eq_runSched m β θ η h x0 o g ξ K]
  rfl

/-- Expected smoothed accuracy of the executed damped anchored algorithm. -/
lemma ag_exec_accuracy (m : ℕ) (hm : 0 < m) {K : ℕ} {g : Point d → Ω → ℝ} {fh : Point d → ℝ}
    {W : Measure (Point d × Ω)} [IsProbabilityMeasure W]
    {L μ β θ η h ρ : ℝ} {x0 xh : Point d}
    (hL : 0 < L) (hμ : 0 < μ) (hβ : 0 < β) (hβh : β ≤ μ / 2) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hcap1 : θ ^ 2 / (4 * β) ≤ η - L * η ^ 2 / 2)
    (hcap3 : (L * η ^ 2 / 2 + θ ^ 2 / (4 * β)) * (2 * ρ ^ 2 / (m : ℝ))
        ≤ θ * (μ / 2 - β) * (2 / L))
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
    (o : Offsets 1 (agM m)) :
    Integrable (fun ξ : ℕ → Point d × Ω =>
        fh (execute (dirOracle h g P) (agDescent (m := agM m) (show ∀ k, 0 < agM m k from fun _ => hm) β θ η h x0) (fun _ => o.off K) () ξ) - fh xh)
        (P : Measure _) ∧
      (∫ ξ : ℕ → Point d × Ω,
          fh (execute (dirOracle h g P) (agDescent (m := agM m) (show ∀ k, 0 < agM m k from fun _ => hm) β θ η h x0) (fun _ => o.off K) () ξ) - fh xh
          ∂(P : Measure (ℕ → Point d × Ω))) ≤ (1 - θ) ^ K * waPotential fh β xh (x0, x0) := by
  classical
  obtain ⟨hgapInt, hgapb⟩ := wa_stream_gap (g := g) (fh := fh) (W := W) (L := L) (μ := μ)
    (β := β) (θ := θ) (η := η) (h := h) (ρ := ρ) (x0 := x0) (xh := xh) (K := K) m hm hL hμ hβ hβh
    hθ0 hθ1 hcap1 hcap3 hg hgr hlip hsc hminh hint hmean hvar2 hvar
  have hpre := sched_stream_law_curry (d := 1) (M := m) (agM m) o K P hind hmarg
  set Φ : (Fin K → secantSpace 1 m → Point d × Ω) → ℝ := fun Ξ =>
    fh (runSched (waStepSched β θ η g h m) 0 K (x0, x0) Ξ).1 - fh xh with hΦdef
  set Q : (ℕ → Point d × Ω) → (Fin K → secantSpace 1 m → Point d × Ω) := fun ξ =>
    fun k : Fin K => fun t : secantSpace 1 m =>
      ξ (schedIndex (d := 1) (M := m) (agM m) o K ⟨k, t⟩) with hQdef
  have hcomp : (fun ξ : ℕ → Point d × Ω =>
        fh (execute (dirOracle h g P) (agDescent (m := agM m) (show ∀ k, 0 < agM m k from fun _ => hm) β θ η h x0) (fun _ => o.off K) () ξ) - fh xh)
      = Φ ∘ Q := by
    refine funext fun ξ => congrArg (fun v => fh v - fh xh)
      (ag_execute m hm β θ η h x0 o g ξ P K)
  have hpush : (∫ ξ : ℕ → Point d × Ω, (Φ ∘ Q) ξ ∂(P : Measure _))
      = ∫ Ξ, Φ Ξ ∂Measure.pi (fun _ : Fin K => slotLaw 1 m W) :=
    ZerothOrder.integral_comp_preserving (q := Q) hpre hgapInt
  refine ⟨hcomp.symm ▸ (hpre.integrable_comp_of_integrable (ε := ℝ) (g := Φ) hgapInt),
    le_of_eq_of_le
      (congrArg (fun F : (ℕ → Point d × Ω) → ℝ => ∫ ξ : ℕ → Point d × Ω, F ξ ∂(P : Measure _))
        hcomp) ?_⟩
  rw [hpush]
  exact hgapb

end OracleTemplate.SecantPolyak.GradedAnchored

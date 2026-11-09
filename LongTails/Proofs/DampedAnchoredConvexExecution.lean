import LongTails.Algorithms.DampedAnchoredConvexPairAcceleration
import LongTails.Proofs.DampedAnchoredConvexStream
import LongTails.Proofs.DampedAnchoredExecution

set_option maxHeartbeats 2000000

namespace OracleTemplate.SecantPolyak.AnchoredConvexPair

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
open InexactGradient SecantDescent SecantPolyak SecantPolyak.Accelerated SecantPolyak.Scheduled
  SecantPolyak.Centered SecantPolyak.DirectionSampled Interpolated
open OracleTemplate.SecantPolyak.AnchoredPair
open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {Ω : Type} [MeasurableSpace Ω] {d : ℕ}

omit [MeasurableSpace Ω] in
lemma dacRunSched_congr (η h : ℝ) (g : Point d → Ω → ℝ) (i K : ℕ) (s : Point d × Point d)
    (Ξ Ξ' : Fin K → secantSpace 1 1 → Point d × Ω)
    (hcell : ∀ (l : ℕ) (_hi : i ≤ l) (t : secantSpace 1 1) (_hl : l < i + K),
        Ξ ⟨l - i, by omega⟩ t = Ξ' ⟨l - i, by omega⟩ t) :
    runSched (dacStepSched η g h) i K s Ξ = runSched (dacStepSched η g h) i K s Ξ' := by
  classical
  induction K generalizing i s with
  | zero => rfl
  | succ K ih =>
      show runSched (dacStepSched η g h) (i + 1) K (dacStepSched η g h i s (Ξ 0))
            (fun j : Fin K => Ξ ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
        = runSched (dacStepSched η g h) (i + 1) K (dacStepSched η g h i s (Ξ' 0))
            (fun j : Fin K => Ξ' ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
      have hstep : dacStepSched η g h i s (Ξ 0) = dacStepSched η g h i s (Ξ' 0) := by
        refine congrArg (fun φ : secantSpace 1 1 → Point d × Ω =>
          dacStep i η s (roundOf h g (dacQuery i s) 1 φ)) ?_
        refine funext fun t => ?_
        have hpre := hcell i (Nat.le_refl i) t (by omega)
        rw [show (⟨i - i, by omega⟩ : Fin (K + 1)) = (0 : Fin (K + 1)) from
            Fin.ext (Nat.sub_self i)] at hpre
        exact hpre
      have hs : ∀ (l : ℕ) (_hi : i + 1 ≤ l) (t : secantSpace 1 1) (_hl : l < i + 1 + K),
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
      rw [ih (i + 1) (dacStepSched η g h i s (Ξ 0))
        (fun j : Fin K => Ξ ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
        (fun j : Fin K => Ξ' ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) hs, hstep]

omit [MeasurableSpace Ω] in
lemma dac_upd (η h : ℝ) (x0 : Point d) (o : Offsets 1 apM) (g : Point d → Ω → ℝ)
    (ξ : ℕ → Point d × Ω) :
    ∀ (k : ℕ) (s : Point d × Point d),
      (dacBase η x0).update (k, s) (dacDec h k (k, s)
          (fun i : Fin (Fintype.card (secantSpace 1 1)) =>
            dirAns h g (dacQS k (k, s) i) (ξ (o.off k + i.val))))
        = (k + 1, dacStepSched η g h k s (fun t : secantSpace 1 1 =>
            ξ (o.off k + (Fintype.equivFin (secantSpace 1 1) t).val))) := by
  intro k s
  refine Prod.ext rfl ?_
  have hsum : dacDec h k (k, s) (fun i : Fin (Fintype.card (secantSpace 1 1)) =>
        dirAns h g (dacQS k (k, s) i) (ξ (o.off k + i.val)))
      = roundOf h g (dacQuery k s) 1 (fun t : secantSpace 1 1 =>
          ξ (o.off k + (Fintype.equivFin (secantSpace 1 1) t).val)) := by
    show ∑ t : secantSpace 1 1, (if secantSign t then (1 : ℝ) else (-1 : ℝ)) •
          term h (dirAns h g (dacQuery k s, secantSign (secantSlot
            (Fintype.equivFin (secantSpace 1 1) t)))
            (ξ (o.off k + (Fintype.equivFin (secantSpace 1 1) t).val))) = _
    simp only [secantSlot_equivFin, secantSign, term, dirAns, rawReply, roundOf, slotVal,
      Nat.cast_one, div_one, one_smul]
    apply Finset.sum_congr rfl
    intro t _
    rfl
  rw [hsum]
  rfl

omit [MeasurableSpace Ω] in
lemma dac_roundsR_eq_runSched (η h : ℝ) (x0 : Point d) (o : Offsets 1 apM)
    (g : Point d → Ω → ℝ) (ξ : ℕ → Point d × Ω) :
    ∀ K : ℕ,
      StochasticGradient.roundsR o.off (dacBase η x0) dacQS (dacDec h) (dirAns h g) ξ K
          (0, (x0, x0))
        = (K, runSched (dacStepSched η g h) 0 K (x0, x0)
            (fun k : Fin K => fun t : secantSpace 1 1 =>
              ξ (schedIndex (d := 1) (M := 1) apM o K ⟨k, t⟩))) := by
  classical
  intro K
  induction K with
  | zero => rfl
  | succ K ih =>
      have hidx : (fun t : secantSpace 1 1 =>
          ξ (schedIndex (d := 1) (M := 1) apM o (K + 1) ⟨⟨K, Nat.lt_succ_self K⟩, t⟩))
          = (fun t : secantSpace 1 1 =>
            ξ (o.off K + (Fintype.equivFin (secantSpace 1 1) t).val)) := by
        refine funext fun t => congrArg ξ ?_
        have h1 := Scheduled.schedIndex_cellInj o (K + 1) K (Nat.lt_succ_self K) (apM_le K) t
        rw [apCellInj_le K t] at h1
        exact h1
      have hcon : runSched (dacStepSched η g h) 0 K (x0, x0)
            (fun j : Fin K => fun t : secantSpace 1 1 =>
              ξ (schedIndex (d := 1) (M := 1) apM o (K + 1) ⟨Fin.castAdd 1 j, t⟩))
          = runSched (dacStepSched η g h) 0 K (x0, x0)
            (fun k : Fin K => fun t : secantSpace 1 1 =>
              ξ (schedIndex (d := 1) (M := 1) apM o K ⟨k, t⟩)) := by
        refine dacRunSched_congr η h g 0 K (x0, x0) _ _ ?_
        intro l _hi t _hl
        show ξ (schedIndex (d := 1) (M := 1) apM o (K + 1) (Fin.castAdd 1 ⟨l - 0, _⟩, t))
          = ξ (schedIndex (d := 1) (M := 1) apM o K (⟨l - 0, _⟩, t))
        have h1 := Scheduled.schedIndex_cellInj o (K + 1) l (by omega) (apM_le l) t
        have h2 := Scheduled.schedIndex_cellInj o K l (by omega) (apM_le l) t
        rw [apCellInj_le l t] at h1 h2
        exact congrArg ξ (h1.trans h2.symm)
      show (dacBase η x0).update
            (StochasticGradient.roundsR o.off (dacBase η x0) dacQS (dacDec h) (dirAns h g) ξ K
              (0, (x0, x0)))
            (dacDec h K
              (StochasticGradient.roundsR o.off (dacBase η x0) dacQS (dacDec h) (dirAns h g) ξ
                K (0, (x0, x0)))
              (fun i => dirAns h g (dacQS K
                (StochasticGradient.roundsR o.off (dacBase η x0) dacQS (dacDec h)
                  (dirAns h g) ξ K (0, (x0, x0))) i) (ξ (o.off K + i.val))))
          = (K + 1, runSched (dacStepSched η g h) 0 (K + 1) (x0, x0)
              (fun k : Fin (K + 1) => fun t : secantSpace 1 1 =>
                ξ (schedIndex (d := 1) (M := 1) apM o (K + 1) ⟨k, t⟩)))
      rw [ih, dac_upd η h x0 o g ξ K, ← hidx, runSched_snoc]
      simp only [Fin.castSucc, Nat.zero_add]
      rw [hcon]

lemma dac_execute (η h : ℝ) (x0 : Point d) (o : Offsets 1 apM) (g : Point d → Ω → ℝ)
    (ξ : ℕ → Point d × Ω) (law : ProbabilityMeasure (ℕ → Point d × Ω)) (K : ℕ) :
    execute (dirOracle h g law) (dacDescent η h x0) (fun _ => o.off K) () ξ
      = (runSched (dacStepSched η g h) 0 K (x0, x0)
          (fun k : Fin K => fun t : secantSpace 1 1 =>
            ξ (schedIndex (d := 1) (M := 1) apM o K ⟨k, t⟩))).1 := by
  classical
  have h1 : execute (dirOracle h g law) (dacDescent η h x0) (fun _ => o.off K) () ξ
      = (dacBase η x0).output
        (StochasticGradient.roundsR o.off (dacBase η x0) dacQS (dacDec h) (dirAns h g) ξ K
          ((dacBase η x0).initial ())) :=
    StochasticGradient.execute_batchedSched (n := fun _ => roundSlots 1 1)
      (hn := fun _ => secant_card_pos (show 0 < 1 from Nat.zero_lt_one) Nat.one_pos)
      (A := dacBase η x0) (queries := dacQS) (decode := dacDec h)
      (zero := ((0 : ℝ), (0 : Point d))) (g := dirAns h g) (ξ := ξ) (h0 := o.zero) (hs := o.step)
      (law := law) (K := K) (seed := ())
  rw [h1]
  rw [show (dacBase η x0).initial () = (0, (x0, x0)) from rfl]
  rw [dac_roundsR_eq_runSched η h x0 o g ξ K]
  rfl

lemma dac_exec_accuracy {K : ℕ} {g : Point d → Ω → ℝ} {fh : Point d → ℝ}
    {W : Measure (Point d × Ω)} [IsProbabilityMeasure W]
    {L η h ρ : ℝ} {x0 xh : Point d}
    (hK : 0 < K) (hL : 0 < L) (hη : 0 < η) (hLη : L * η ≤ 1)
    (hρη : ρ ^ 2 * ((K : ℝ) + 1) * η ≤ 1)
    (hg : Measurable (Function.uncurry g))
    (hc : ConvexOn ℝ Set.univ fh)
    (hgr : ∀ x, HasGradientAt fh (gradient fh x) x)
    (hlip : ∀ x y, ‖gradient fh x - gradient fh y‖ ≤ L * ‖x - y‖)
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
    (o : Offsets 1 apM) :
    Integrable (fun ξ : ℕ → Point d × Ω =>
        fh (execute (dirOracle h g P) (dacDescent η h x0) (fun _ => o.off K) () ξ) - fh xh)
        (P : Measure _) ∧
      (∫ ξ : ℕ → Point d × Ω,
          fh (execute (dirOracle h g P) (dacDescent η h x0) (fun _ => o.off K) () ξ) - fh xh
          ∂(P : Measure (ℕ → Point d × Ω))) ≤ 8 * ‖x0 - xh‖ ^ 2 / (η * dacWeight K) := by
  classical
  obtain ⟨hgapInt, hgapb⟩ := dac_stream_gap (g := g) (fh := fh) (W := W) (L := L)
    (η := η) (h := h) (ρ := ρ) (x0 := x0) (xh := xh) (K := K) hK hL hη hLη hρη
    hg hc hgr hlip hminh hint hmean hvar2 hvar
  have hpre := sched_stream_law_curry (d := 1) (M := 1) apM o K P hind hmarg
  set Φ : (Fin K → secantSpace 1 1 → Point d × Ω) → ℝ := fun Ξ =>
    fh (runSched (dacStepSched η g h) 0 K (x0, x0) Ξ).1 - fh xh
  set Q : (ℕ → Point d × Ω) → (Fin K → secantSpace 1 1 → Point d × Ω) := fun ξ =>
    fun k : Fin K => fun t : secantSpace 1 1 =>
      ξ (schedIndex (d := 1) (M := 1) apM o K ⟨k, t⟩)
  have hcomp : (fun ξ : ℕ → Point d × Ω =>
        fh (execute (dirOracle h g P) (dacDescent η h x0) (fun _ => o.off K) () ξ) - fh xh)
      = Φ ∘ Q := by
    refine funext fun ξ => congrArg (fun v => fh v - fh xh)
      (dac_execute η h x0 o g ξ P K)
  have hpush : (∫ ξ : ℕ → Point d × Ω, (Φ ∘ Q) ξ ∂(P : Measure _))
      = ∫ Ξ, Φ Ξ ∂Measure.pi (fun _ : Fin K => slotLaw 1 1 W) :=
    ZerothOrder.integral_comp_preserving (q := Q) hpre hgapInt
  refine ⟨hcomp.symm ▸ (hpre.integrable_comp_of_integrable (ε := ℝ) (g := Φ) hgapInt),
    le_of_eq_of_le
      (congrArg (fun F : (ℕ → Point d × Ω) → ℝ => ∫ ξ : ℕ → Point d × Ω, F ξ ∂(P : Measure _))
        hcomp) ?_⟩
  rw [hpush]
  exact hgapb

lemma dac_rate_bound {L R ε ρ : ℝ} {x0 xh : Point d} {K : ℕ}
    (hL : 0 < L) (hε : 0 < ε) (hR_xh : ‖x0 - xh‖ ≤ R)
    (hK1 : 1 ≤ K)
    (habK : Real.sqrt (16 * L * R ^ 2 / ε) + 16 * ρ ^ 2 * R ^ 2 / ε ≤ (K : ℝ)) :
    8 * ‖x0 - xh‖ ^ 2 / ((1 / (L + ρ ^ 2 * ((K : ℝ) + 1))) * dacWeight K) ≤ ε / 2 := by
  set η : ℝ := 1 / (L + ρ ^ 2 * ((K : ℝ) + 1))
  have hKpos : 0 < K := Nat.one_pos.trans_le hK1
  have hKR : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr hKpos
  have hKR1 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hdenom : 0 < L + ρ ^ 2 * ((K : ℝ) + 1) := by positivity
  have hη : 0 < η := one_div_pos.mpr hdenom
  have hdist : ‖x0 - xh‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hR_xh 2
  set a : ℝ := Real.sqrt (16 * L * R ^ 2 / ε)
  set b : ℝ := 16 * ρ ^ 2 * R ^ 2 / ε
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := by positivity
  have ha2 : a ^ 2 = 16 * L * R ^ 2 / ε := Real.sq_sqrt (by positivity)
  have haK : a ≤ (K : ℝ) := by linarith
  have hquad : a ^ 2 + b * (K : ℝ) ≤ (K : ℝ) ^ 2 := by
    have h1 : a ^ 2 ≤ a * (K : ℝ) := by nlinarith
    have h2 : (a + b) * (K : ℝ) ≤ (K : ℝ) * (K : ℝ) :=
      mul_le_mul_of_nonneg_right habK hKR.le
    nlinarith
  have hnum : 8 * L * R ^ 2 + 8 * ρ ^ 2 * R ^ 2 * (K : ℝ)
      ≤ (ε / 2) * (K : ℝ) ^ 2 := by
    have h1 : (ε / 2) * (a ^ 2 + b * (K : ℝ)) ≤ (ε / 2) * (K : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hquad (by positivity)
    have h2 : (ε / 2) * a ^ 2 = 8 * L * R ^ 2 := by
      rw [ha2]
      field_simp [hε.ne']
      ring
    have h3 : (ε / 2) * (b * (K : ℝ)) = 8 * ρ ^ 2 * R ^ 2 * (K : ℝ) := by
      show (ε / 2) * ((16 * ρ ^ 2 * R ^ 2 / ε) * (K : ℝ)) = _
      field_simp [hε.ne']
      ring
    linarith
  have hwpos : 0 < dacWeight K := by
    unfold dacWeight
    positivity
  have h1 : 8 * ‖x0 - xh‖ ^ 2 / (η * dacWeight K)
      ≤ 8 * R ^ 2 / (η * dacWeight K) := by gcongr
  have h2 : 8 * R ^ 2 / (η * dacWeight K)
      = (8 * L * R ^ 2 + 8 * ρ ^ 2 * R ^ 2 * ((K : ℝ) + 1))
          / ((K : ℝ) * ((K : ℝ) + 1)) := by
    show 8 * R ^ 2 / ((1 / (L + ρ ^ 2 * ((K : ℝ) + 1))) * ((K : ℝ) * ((K : ℝ) + 1))) = _
    field_simp [hdenom.ne', hKR.ne', hKR1.ne']
  have h3 : (8 * L * R ^ 2 + 8 * ρ ^ 2 * R ^ 2 * ((K : ℝ) + 1))
        / ((K : ℝ) * ((K : ℝ) + 1))
      ≤ (8 * L * R ^ 2 + 8 * ρ ^ 2 * R ^ 2 * (K : ℝ)) / (K : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hLR : 0 ≤ 8 * L * R ^ 2 := by positivity
    nlinarith
  have h4 : (8 * L * R ^ 2 + 8 * ρ ^ 2 * R ^ 2 * (K : ℝ)) / (K : ℝ) ^ 2 ≤ ε / 2 :=
    (div_le_iff₀ (by positivity)).mpr hnum
  linarith

lemma dac_budget_le {L R ε ρ : ℝ} (_hL : 0 < L) (_hε : 0 < ε) :
    ((2 * max 1 ⌈Real.sqrt (16 * L * R ^ 2 / ε) + 16 * ρ ^ 2 * R ^ 2 / ε⌉₊ : ℕ) : ℝ)
      ≤ 2 + 2 * Real.sqrt (16 * L * R ^ 2 / ε) + 32 * ρ ^ 2 * R ^ 2 / ε := by
  set x : ℝ := Real.sqrt (16 * L * R ^ 2 / ε) + 16 * ρ ^ 2 * R ^ 2 / ε with hx
  have hx0 : 0 ≤ x := by
    rw [hx]
    positivity
  have hmax : ((max 1 ⌈x⌉₊ : ℕ) : ℝ) ≤ x + 1 := by
    have key : max (1 : ℝ) (⌈x⌉₊ : ℝ) ≤ x + 1 :=
      max_le_iff.mpr ⟨le_add_of_nonneg_left hx0, (Nat.ceil_lt_add_one hx0).le⟩
    simpa [Nat.cast_max] using key
  calc ((2 * max 1 ⌈x⌉₊ : ℕ) : ℝ)
      = 2 * ((max 1 ⌈x⌉₊ : ℕ) : ℝ) := by push_cast; ring
    _ ≤ 2 * (x + 1) := mul_le_mul_of_nonneg_left hmax (by positivity)
    _ = 2 + 2 * Real.sqrt (16 * L * R ^ 2 / ε) + 32 * ρ ^ 2 * R ^ 2 / ε := by
        rw [hx]
        ring

end OracleTemplate.SecantPolyak.AnchoredConvexPair

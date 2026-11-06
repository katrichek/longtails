import LongTails.Algorithms.DirectionSampledMomentum
import LongTails.Proofs.BatchedScheduledExecution
import LongTails.Proofs.DirectionMomentumStream
import LongTails.Proofs.SecantPolyakScheduledExecution

set_option maxHeartbeats 2000000

/-!
Execution of direction-sampled momentum descent. The oracle supplies one independent direction and
value sample per probe, so the flat stream cells carry pairs. Running `K` rounds consumes exactly
`2 * m k` cells in round `k`, and the decoded replies coincide cell by cell with the surrogate
`roundOf` analysed in the stream module.
-/

namespace OracleTemplate.SecantPolyak.DirectionSampled

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
open InexactGradient SecantDescent SecantPolyak SecantPolyak.Accelerated SecantPolyak.Scheduled
  SecantPolyak.Centered
open LongTails.Setups.ZerothOrderSmoothAndConvex
open LongTails.Setups.ZerothOrderSmoothingStronglyConvex

variable {Ω : Type} [MeasurableSpace Ω] {d : ℕ}

/-- The raw reply of one probe: the noisy value together with the direction of the probe. -/
noncomputable def rawReply (h : ℝ) (g : Point d → Ω → ℝ) (x : Point d) (s : Bool)
    (u : Point d × Ω) : ℝ × Point d := (g (x + (if s then h else -h) • u.1) u.2, u.1)

/-- The answer of one probe as a function of the query and the cell sample. -/
noncomputable def dirAns (h : ℝ) (g : Point d → Ω → ℝ) :
    (Point d × Bool) → (Point d × Ω) → ℝ × Point d := fun q u => rawReply h g q.1 q.2 u

/-- The oracle of the direction-sampled model driven by the value function `g`. -/
noncomputable def dirOracle (h : ℝ) (g : Point d → Ω → ℝ)
    (law : ProbabilityMeasure (ℕ → Point d × Ω)) : Oracle (Point d × Bool) (ℝ × Point d) :=
  { Seed := fun _ => Point d × Ω, law := law, answer := fun _ (_, r) u => rawReply h g r.1 r.2 u }

/-- The model oracle of the smoothing setup is the raw oracle at the setup bandwidth. -/
lemma dirOracle_eq {q : LongTails.Setups.ZerothOrderSmoothingStronglyConvex.Params}
    (g : Point q.d → q.Ω → ℝ)
    (law : ProbabilityMeasure (ℕ → Point q.d × q.Ω)) :
    dirOracle (d := q.d) q.h g law =
      { Seed := fun _ => Point q.d × q.Ω, law := law,
        answer := fun _ (_, r) u => dirReply g r.1 r.2 u } := rfl

omit [MeasurableSpace Ω] in
/-- Two flat streams that agree on the cells of the schedule give the same direction-sampled run. -/
lemma dirRunSched_congr {M : ℕ} {m : ℕ → ℕ} (hmM : ∀ k, m k ≤ M) (L μ θ : ℝ)
    {g : Point d → Ω → ℝ} (h : ℝ) (i K : ℕ) (s : Point d × Point d)
    (Ξ Ξ' : Fin K → secantSpace 1 M → Point d × Ω)
    (hcell : ∀ (l : ℕ) (hi : i ≤ l) (t : secantSpace 1 (m l)) (hl : l < i + K),
        Ξ ⟨l - i, by omega⟩ (cellInj (hmM l) t) = Ξ' ⟨l - i, by omega⟩ (cellInj (hmM l) t)) :
    runSched (dirStepSched m hmM L μ θ g h) i K s Ξ
      = runSched (dirStepSched m hmM L μ θ g h) i K s Ξ' := by
  classical
  induction K generalizing i s with
  | zero => rfl
  | succ K ih =>
      show runSched (dirStepSched m hmM L μ θ g h) (i + 1) K
            (dirStepSched m hmM L μ θ g h i s (Ξ 0))
            (fun j : Fin K => Ξ ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
        = runSched (dirStepSched m hmM L μ θ g h) (i + 1) K
            (dirStepSched m hmM L μ θ g h i s (Ξ' 0))
            (fun j : Fin K => Ξ' ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
      have hstep : dirStepSched m hmM L μ θ g h i s (Ξ 0)
          = dirStepSched m hmM L μ θ g h i s (Ξ' 0) := by
        refine congrArg (fun φ : secantSpace 1 (m i) → Point d × Ω =>
            step L μ θ s (roundOf h g (query θ s) (m i) φ)) ?_
        refine funext fun t => ?_
        have hpre := hcell i (Nat.le_refl i) t (by omega)
        rw [show (⟨i - i, by omega⟩ : Fin (K + 1)) = (0 : Fin (K + 1)) from
            Fin.ext (Nat.sub_self i)] at hpre
        exact hpre
      have hs : ∀ (l : ℕ) (hi : i + 1 ≤ l) (t : secantSpace 1 (m l)) (hl : l < i + 1 + K),
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
      rw [ih (i + 1) (dirStepSched m hmM L μ θ g h i s (Ξ 0))
        (fun j : Fin K => Ξ ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
        (fun j : Fin K => Ξ' ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) hs, hstep]

omit [MeasurableSpace Ω] in
/-- Running `K` direction-sampled rounds on the flat oracle stream reproduces the analysed run. -/
lemma dir_roundsR_eq_runSched {M : ℕ} {m : ℕ → ℕ} (hmM : ∀ k, m k ≤ M) (L μ θ h : ℝ)
    (x0 : Point d) (o : Offsets 1 m) (g : Point d → Ω → ℝ) (ξ : ℕ → Point d × Ω) :
    ∀ K : ℕ, @StochasticGradient.roundsR (Point d × Bool) (Point d) (ℝ × Point d) (Point d)
        (Point d × Ω) (fun k => Fintype.card (secantSpace 1 (m k))) o.off (dirBase L μ θ x0)
        (dirQS θ) (dirDec h) (dirAns h g) ξ K (0, x0, x0)
      = (K, runSched (dirStepSched m hmM L μ θ g h) 0 K (x0, x0)
          (fun k : Fin K => fun t : secantSpace 1 M =>
            ξ (schedIndex (d := 1) (M := M) m o K ⟨k, t⟩))) := by
  classical
  intro K
  induction K with
  | zero => rfl
  | succ K ih =>
      have hround : ∀ s, (dirBase L μ θ x0).update (K, s)
            (dirDec h K (K, s)
              (fun i : Fin (Fintype.card (secantSpace 1 (m K))) =>
                dirAns h g (dirQS (m := m) θ K (K, s) i) (ξ (o.off K + i.val))))
          = (K + 1, dirStepSched m hmM L μ θ g h K s
              (fun t : secantSpace 1 M =>
                ξ (schedIndex (d := 1) (M := M) m o (K + 1) ⟨⟨K, Nat.lt_succ_self K⟩, t⟩))) := by
        intro s
        refine Prod.ext rfl ?_
        have hsum : dirDec h K (K, s)
              (fun i : Fin (Fintype.card (secantSpace 1 (m K))) =>
                dirAns h g (dirQS θ K (K, s) i) (ξ (o.off K + i.val)))
            = roundOf h g (query θ s) (m K)
              (fun t : secantSpace 1 (m K) =>
                ξ (o.off K + (Fintype.equivFin (secantSpace 1 (m K)) t).val)) := by
          show (1 / (m K : ℝ)) • ∑ t : secantSpace 1 (m K),
                (if secantSign t then (1 : ℝ) else (-1 : ℝ)) •
                  term h (rawReply h g (query θ s)
                    (secantSign (secantSlot (Fintype.equivFin (secantSpace 1 (m K)) t)))
                    (ξ (o.off K + (Fintype.equivFin (secantSpace 1 (m K)) t).val))) = _
          simp only [secantSlot_equivFin]
          show (1 / (m K : ℝ)) • ∑ t : secantSpace 1 (m K),
                (if t.2.2 then (1 : ℝ) else (-1 : ℝ)) •
                  slotVal h g (query θ s) t.2.2
                    (ξ (o.off K + (Fintype.equivFin (secantSpace 1 (m K)) t).val)) = _
          rfl
        rw [hsum]
        have hidx : (fun t : secantSpace 1 (m K) =>
              ξ (schedIndex (d := 1) (M := M) m o (K + 1)
                ⟨⟨K, Nat.lt_succ_self K⟩, cellInj (hmM K) t⟩))
            = (fun t : secantSpace 1 (m K) =>
                ξ (o.off K + (Fintype.equivFin (secantSpace 1 (m K)) t).val)) := by
          refine funext fun t => congrArg ξ ?_
          exact Scheduled.schedIndex_cellInj o (K + 1) K (Nat.lt_succ_self K) (hmM K) t
        rw [← hidx]
        rfl
      have hcon : runSched (dirStepSched m hmM L μ θ g h) 0 K (x0, x0)
            (fun j : Fin K => fun t : secantSpace 1 M =>
              ξ (schedIndex (d := 1) (M := M) m o (K + 1) ⟨Fin.castAdd 1 j, t⟩))
          = runSched (dirStepSched m hmM L μ θ g h) 0 K (x0, x0)
            (fun k : Fin K => fun t : secantSpace 1 M =>
              ξ (schedIndex (d := 1) (M := M) m o K ⟨k, t⟩)) := by
        refine dirRunSched_congr hmM L μ θ h 0 K (x0, x0) _ _ ?_
        intro l hi t hl
        show ξ (schedIndex (d := 1) (M := M) m o (K + 1)
            (Fin.castAdd 1 ⟨l - 0, _⟩, cellInj (hmM l) t))
          = ξ (schedIndex (d := 1) (M := M) m o K (⟨l - 0, _⟩, cellInj (hmM l) t))
        exact congrArg ξ ((Scheduled.schedIndex_cellInj o (K + 1) l (by omega) (hmM l) t).trans
          (Scheduled.schedIndex_cellInj o K l (by omega) (hmM l) t).symm)
      show (dirBase L μ θ x0).update
            (@StochasticGradient.roundsR (Point d × Bool) (Point d) (ℝ × Point d) (Point d)
              (Point d × Ω) (fun k => Fintype.card (secantSpace 1 (m k))) o.off
              (dirBase L μ θ x0) (dirQS θ) (dirDec h) (dirAns h g) ξ K (0, x0, x0))
            (dirDec h K
              (@StochasticGradient.roundsR (Point d × Bool) (Point d) (ℝ × Point d) (Point d)
                (Point d × Ω) (fun k => Fintype.card (secantSpace 1 (m k))) o.off
                (dirBase L μ θ x0) (dirQS θ) (dirDec h) (dirAns h g) ξ K (0, x0, x0))
              (fun i => dirAns h g (dirQS θ K
                (@StochasticGradient.roundsR (Point d × Bool) (Point d) (ℝ × Point d) (Point d)
                  (Point d × Ω) (fun k => Fintype.card (secantSpace 1 (m k))) o.off
                  (dirBase L μ θ x0) (dirQS θ) (dirDec h) (dirAns h g) ξ K (0, x0, x0)) i)
                (ξ (o.off K + i.val))))
          = (K + 1, runSched (dirStepSched m hmM L μ θ g h) 0 (K + 1) (x0, x0)
              (fun k : Fin (K + 1) => fun t : secantSpace 1 M =>
                ξ (schedIndex (d := 1) (M := M) m o (K + 1) ⟨k, t⟩)))
      rw [ih, hround, runSched_snoc]
      simp only [Fin.castSucc]
      rw [hcon]
      simp only [Nat.zero_add]
      exact Prod.ext rfl rfl

/-- The executed direction-sampled algorithm coincides with the analysed run. -/
lemma execute_dirDescent {M : ℕ} {m : ℕ → ℕ} {hmM : ∀ k, m k ≤ M} (hm : ∀ k, 0 < m k)
    (L μ θ h : ℝ) (x0 : Point d) (o : Offsets 1 m) (g : Point d → Ω → ℝ)
    (ξ : ℕ → Point d × Ω) (law : ProbabilityMeasure (ℕ → Point d × Ω)) (K : ℕ) :
    execute (dirOracle h g law) (dirDescent hm L μ θ h x0) (fun _ => o.off K) () ξ
      = (runSched (dirStepSched m hmM L μ θ g h) 0 K (x0, x0)
          (fun k : Fin K => fun t : secantSpace 1 M =>
            ξ (schedIndex (d := 1) (M := M) m o K ⟨k, t⟩))).1 := by
  classical
  have h1 : execute (dirOracle h g law) (dirDescent hm L μ θ h x0) (fun _ => o.off K) () ξ
      = (dirBase L μ θ x0).output
        (StochasticGradient.roundsR o.off (dirBase L μ θ x0) (dirQS θ) (dirDec h) (dirAns h g) ξ K
          ((dirBase L μ θ x0).initial ())) :=
    StochasticGradient.execute_batchedSched (n := fun k => roundSlots 1 (m k))
      (hn := fun k => secant_card_pos (show 0 < 1 from Nat.zero_lt_one) (hm k))
      (A := dirBase L μ θ x0) (queries := dirQS θ) (decode := dirDec h) (zero := ((0 : ℝ), (0 : Point d)))
      (g := dirAns h g) (ξ := ξ) (h0 := o.zero) (hs := o.step) (law := law) (K := K) (seed := ())
  rw [h1]
  rw [show (dirBase L μ θ x0).initial () = (0, x0, x0) from rfl]
  rw [dir_roundsR_eq_runSched hmM L μ θ h x0 o g ξ K]
  rfl

/-- The slots of one round of the direction-sampled schedule: two probes per replica. -/
lemma roundSlots_one (m : ℕ) : roundSlots 1 m = 2 * m := by
  show Fintype.card (secantSpace 1 m) = 2 * m
  rw [card_secantSpace]

/-- Expected smoothed accuracy of the executed direction-sampled algorithm. -/
lemma dir_exec_accuracy {M K : ℕ} {m : ℕ → ℕ} (hmM : ∀ k, m k ≤ M) (hm : ∀ k, 0 < m k)
    {g : Point d → Ω → ℝ} {fh : Point d → ℝ} {nu : ProbabilityMeasure (Point d)}
    {p : Measure Ω} [IsProbabilityMeasure p] {L μ θ h G : ℝ} {x0 xh : Point d}
    (hL : 0 < L) (hμ : 0 < μ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hθL : 16 * L * θ ^ 2 ≤ μ)
    (hg : Measurable (Function.uncurry g))
    (hgr : ∀ x, HasGradientAt fh (gradient fh x) x)
    (hlip : ∀ x y, ‖gradient fh x - gradient fh y‖ ≤ L * ‖x - y‖)
    (hsc : ∀ x y, fh x + ⟪gradient fh x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ fh y)
    (hminh : IsMinOn fh Set.univ xh)
    (hint : ∀ x s, Integrable (fun u : Point d × Ω =>
        slotVal h g x s u - halfGrad fh x s) (probeMeasure nu p))
    (hmean : ∀ x s, (∫ u : Point d × Ω, slotVal h g x s u ∂(probeMeasure nu p)) = halfGrad fh x s)
    (hvar2 : ∀ x s, Integrable (fun u : Point d × Ω =>
        ‖slotVal h g x s u - halfGrad fh x s‖ ^ 2) (probeMeasure nu p))
    (hvar : ∀ x s, (∫ u : Point d × Ω, ‖slotVal h g x s u - halfGrad fh x s‖ ^ 2
        ∂(probeMeasure nu p)) ≤ G ^ 2)
    (P : ProbabilityMeasure (ℕ → Point d × Ω))
    (hind : iIndepFun (fun k (ξ : ℕ → Point d × Ω) => ξ k) (P : Measure _))
    (hmarg : ∀ k, (P : Measure _).map (fun ξ : ℕ → Point d × Ω => ξ k)
        = (probeMeasure nu p : Measure (Point d × Ω)))
    (o : Offsets 1 m) :
    Integrable (fun ξ : ℕ → Point d × Ω =>
        fh (execute (dirOracle h g P) (dirDescent hm L μ θ h x0) (fun _ => o.off K) () ξ) - fh xh)
        (P : Measure _) ∧
      (∫ ξ : ℕ → Point d × Ω,
          fh (execute (dirOracle h g P) (dirDescent hm L μ θ h x0) (fun _ => o.off K) () ξ) - fh xh
          ∂(P : Measure (ℕ → Point d × Ω)))
        ≤ (1 - θ / 2) ^ K * (fh x0 - fh xh + μ / 4 * ‖x0 - xh‖ ^ 2)
          + ∑ k ∈ Finset.range K, (1 - θ / 2) ^ (K - 1 - k)
              * ((1 / (2 * L) + θ ^ 2 / μ) * (2 * G ^ 2 / (m k : ℝ))) := by
  classical
  obtain ⟨hgapInt, hgapb⟩ := dir_stream_gap (M := M) (m := m) hmM hm (g := g) (fh := fh) (nu := nu)
    (p := p) (L := L) (μ := μ) (θ := θ) (h := h) (G := G) (x0 := x0) (xh := xh) (K := K)
    hL hμ hθ0 hθ1 hθL hg hgr hlip hsc hminh hint hmean hvar2 hvar
  have hpre := sched_stream_law_curry (d := 1) (M := M) m o K P hind hmarg
  set Φ : (Fin K → secantSpace 1 M → Point d × Ω) → ℝ := fun Ξ =>
    fh (runSched (dirStepSched m hmM L μ θ g h) 0 K (x0, x0) Ξ).1 - fh xh with hΦdef
  set Q : (ℕ → Point d × Ω) → (Fin K → secantSpace 1 M → Point d × Ω) := fun ξ =>
    fun k : Fin K => fun t : secantSpace 1 M =>
      ξ (schedIndex (d := 1) (M := M) m o K ⟨k, t⟩) with hQdef
  have hcomp : (fun ξ : ℕ → Point d × Ω =>
        fh (execute (dirOracle h g P) (dirDescent hm L μ θ h x0) (fun _ => o.off K) () ξ) - fh xh)
      = Φ ∘ Q := by
    refine funext fun ξ => congrArg (fun v => fh v - fh xh)
      (execute_dirDescent (hmM := hmM) hm L μ θ h x0 o g ξ P K)
  have hpush : (∫ ξ : ℕ → Point d × Ω, (Φ ∘ Q) ξ ∂(P : Measure _))
      = ∫ Ξ, Φ Ξ ∂Measure.pi (fun _ : Fin K => slotLaw 1 M (probeMeasure nu p)) :=
    ZerothOrder.integral_comp_preserving (q := Q) hpre hgapInt
  refine ⟨hcomp.symm ▸ (hpre.integrable_comp_of_integrable (ε := ℝ) (g := Φ) hgapInt),
    le_of_eq_of_le
      (congrArg (fun F : (ℕ → Point d × Ω) → ℝ => ∫ ξ : ℕ → Point d × Ω, F ξ ∂(P : Measure _))
        hcomp) ?_⟩
  rw [hpush]
  exact hgapb

end OracleTemplate.SecantPolyak.DirectionSampled

import LongTails.Algorithms.AcceleratedSecantDescent
import LongTails.Proofs.AcceleratedSecantStream
import LongTails.Proofs.SecantPolyakScheduledExecution
import LongTails.Proofs.BatchedScheduledExecution

namespace OracleTemplate.SecantPolyak.Accelerated

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
open SecantDescent SecantPolyak ZerothOrder InexactGradient Scheduled
open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {Ω : Type} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- Two flat streams that agree on the cells of the schedule give the same accelerated run. -/
lemma accelRunSched_congr {d M : ℕ} {m : ℕ → ℕ} (hmM : ∀ k, m k ≤ M) (L μ θ : ℝ)
    {g : Point d → Ω → ℝ} (h : ℝ) (i K : ℕ) (s : Point d × Point d)
    (Ξ Ξ' : Fin K → secantSpace d M → Ω)
    (hcell : ∀ (l : ℕ) (hi : i ≤ l) (t : secantSpace d (m l)) (hl : l < i + K),
        Ξ ⟨l - i, by omega⟩ (cellInj (hmM l) t) = Ξ' ⟨l - i, by omega⟩ (cellInj (hmM l) t)) :
    runSched (accelStepSched m hmM L μ θ g h) i K s Ξ
      = runSched (accelStepSched m hmM L μ θ g h) i K s Ξ' := by
  classical
  induction K generalizing i s with
  | zero => rfl
  | succ K ih =>
      show runSched (accelStepSched m hmM L μ θ g h) (i + 1) K
            (accelStepSched m hmM L μ θ g h i s (Ξ 0))
            (fun j : Fin K => Ξ ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
        = runSched (accelStepSched m hmM L μ θ g h) (i + 1) K
            (accelStepSched m hmM L μ θ g h i s (Ξ' 0))
            (fun j : Fin K => Ξ' ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
      have hstep : accelStepSched m hmM L μ θ g h i s (Ξ 0)
          = accelStepSched m hmM L μ θ g h i s (Ξ' 0) := by
        refine congrArg (fun φ : (secantSpace d (m i) → Ω) =>
            step L μ θ s (reply (g := g) h (query θ s) (toCells φ))) ?_
        refine funext fun t => ?_
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
      rw [ih (i + 1) (accelStepSched m hmM L μ θ g h i s (Ξ 0))
        (fun j : Fin K => Ξ ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
        (fun j : Fin K => Ξ' ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) hs, hstep]

omit [MeasurableSpace Ω] in
/-- Running `K` accelerated rounds on the flat oracle stream reproduces the analysed run. -/
lemma accel_roundsR_eq_runSched {d M : ℕ} {m : ℕ → ℕ} (hmM : ∀ k, m k ≤ M) (L μ θ h : ℝ)
    (x0 : Point d) (o : Offsets d m) (g : Point d → Ω → ℝ) (ξ : ℕ → Ω) :
    ∀ K : ℕ, @StochasticGradient.roundsR (Point d) (Point d) ℝ (Point d) Ω
        (fun k => Fintype.card (secantSpace d (m k))) o.off (accelBase L μ θ x0) (accelQS θ h)
        (accelDec θ h) g ξ K (0, x0, x0)
      = (K, runSched (accelStepSched m hmM L μ θ g h) 0 K (x0, x0)
          (fun k : Fin K => fun t : secantSpace d M => ξ (schedIndex m o K ⟨k, t⟩))) := by
  classical
  intro K
  induction K with
  | zero => rfl
  | succ K ih =>
      have hround : ∀ s, (accelBase L μ θ x0).update (K, s)
            (accelDec θ h K (K, s)
              (fun i : Fin (Fintype.card (secantSpace d (m K))) =>
                g (accelQS (m := m) θ h K (K, s) i) (ξ (o.off K + i.val))))
          = (K + 1, accelStepSched m hmM L μ θ g h K s
              (fun t : secantSpace d M =>
                ξ (schedIndex m o (K + 1) ⟨⟨K, Nat.lt_succ_self K⟩, t⟩))) := by
        intro s
        refine Prod.ext rfl ?_
        show step L μ θ s (secantDecode h (0, query θ s)
              (fun t : secantSpace d (m K) =>
                g (secantQuery h (0, query θ s)
                    (secantSlot (Fintype.equivFin (secantSpace d (m K)) t)))
                  (ξ (o.off K + (Fintype.equivFin (secantSpace d (m K)) t).val)))) = _
        have hq : (fun t : secantSpace d (m K) =>
              g (secantQuery h (0, query θ s) (secantSlot (Fintype.equivFin (secantSpace d (m K)) t)))
                (ξ (o.off K + (Fintype.equivFin (secantSpace d (m K)) t).val)))
            = (fun t : secantSpace d (m K) =>
                g (secantPoint h (query θ s) t)
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
          exact Scheduled.schedIndex_cellInj o (K + 1) K (Nat.lt_succ_self K) (hmM K) t
        rw [← hidx]
        rfl
      have hcon : runSched (accelStepSched m hmM L μ θ g h) 0 K (x0, x0)
            (fun j : Fin K => fun t : secantSpace d M =>
              ξ (schedIndex m o (K + 1) ⟨Fin.castAdd 1 j, t⟩))
          = runSched (accelStepSched m hmM L μ θ g h) 0 K (x0, x0)
            (fun k : Fin K => fun t : secantSpace d M => ξ (schedIndex m o K ⟨k, t⟩)) := by
        refine accelRunSched_congr hmM L μ θ h 0 K (x0, x0) _ _ ?_
        intro l hi t hl
        show ξ (schedIndex m o (K + 1) (Fin.castAdd 1 ⟨l - 0, _⟩, cellInj (hmM l) t))
          = ξ (schedIndex m o K (⟨l - 0, _⟩, cellInj (hmM l) t))
        exact congrArg ξ ((Scheduled.schedIndex_cellInj o (K + 1) l (by omega) (hmM l) t).trans
          (Scheduled.schedIndex_cellInj o K l (by omega) (hmM l) t).symm)
      show (accelBase L μ θ x0).update
            (@StochasticGradient.roundsR (Point d) (Point d) ℝ (Point d) Ω
              (fun k => Fintype.card (secantSpace d (m k))) o.off (accelBase L μ θ x0) (accelQS θ h)
              (accelDec θ h) g ξ K (0, x0, x0))
            (accelDec θ h K
              (@StochasticGradient.roundsR (Point d) (Point d) ℝ (Point d) Ω
                (fun k => Fintype.card (secantSpace d (m k))) o.off (accelBase L μ θ x0)
                (accelQS θ h) (accelDec θ h) g ξ K (0, x0, x0))
              (fun i => g (accelQS θ h K
                (@StochasticGradient.roundsR (Point d) (Point d) ℝ (Point d) Ω
                  (fun k => Fintype.card (secantSpace d (m k))) o.off (accelBase L μ θ x0)
                  (accelQS θ h) (accelDec θ h) g ξ K (0, x0, x0)) i) (ξ (o.off K + i.val))))
          = (K + 1, runSched (accelStepSched m hmM L μ θ g h) 0 (K + 1) (x0, x0)
              (fun k : Fin (K + 1) => fun t : secantSpace d M =>
                ξ (schedIndex m o (K + 1) ⟨k, t⟩)))
      rw [ih, hround, runSched_snoc]
      simp only [Fin.castSucc]
      rw [hcon]
      simp only [Nat.zero_add]
      exact Prod.ext rfl rfl

lemma accel_exec_aux {d M : ℕ} {m : ℕ → ℕ} (hd : 0 < d) {hmM : ∀ k, m k ≤ M} (hm : ∀ k, 0 < m k)
    (L μ θ h : ℝ) (x0 : Point d) (o : Offsets d m) (g : Point d → Ω → ℝ) (ξ : ℕ → Ω)
    (law : ProbabilityMeasure (ℕ → Ω)) (K : ℕ) :
    execute { Seed := fun _ => Ω, law := law, answer := fun _ (_, x) ω => g x ω }
      (batchedSched (fun k => Fintype.card (secantSpace d (m k)))
        (fun k => secant_card_pos hd (hm k)) (accelBase L μ θ x0) (accelQS θ h) (accelDec θ h) 0)
      (fun _ => o.off K) () ξ
      = (runSched (accelStepSched m hmM L μ θ g h) 0 K (x0, x0)
          (fun k : Fin K => fun t : secantSpace d M => ξ (schedIndex m o K ⟨k, t⟩))).1 := by
  classical
  refine (StochasticGradient.execute_batchedSched (h0 := o.zero) (hs := fun j => o.step j)
    (law := law) (K := K) (seed := ())).trans ?_
  rw [show (accelBase L μ θ x0).initial () = (0, x0, x0) from rfl]
  exact ((congrArg (fun st => (accelBase L μ θ x0).output st)
      (accel_roundsR_eq_runSched hmM L μ θ h x0 o g ξ K)).trans rfl)

/-- The executed accelerated algorithm coincides with the analysed accelerated run. -/
lemma execute_accelDescent {d M : ℕ} {m : ℕ → ℕ} (hd : 0 < d) {hmM : ∀ k, m k ≤ M}
    (hm : ∀ k, 0 < m k) (L μ θ h : ℝ) (x0 : Point d) (o : Offsets d m) (g : Point d → Ω → ℝ)
    (ξ : ℕ → Ω) (law : ProbabilityMeasure (ℕ → Ω)) (K : ℕ) :
    execute { Seed := fun _ => Ω, law := law, answer := fun _ (_, x) ω => g x ω }
      (accelDescent hd hm L μ θ h x0) (fun _ => o.off K) () ξ
      = (runSched (accelStepSched m hmM L μ θ g h) 0 K (x0, x0)
          (fun k : Fin K => fun t : secantSpace d M => ξ (schedIndex m o K ⟨k, t⟩))).1 := by
  show execute { Seed := fun _ => Ω, law := law, answer := fun _ (_, x) ω => g x ω }
      (batchedSched (fun k => Fintype.card (secantSpace d (m k)))
        (fun k => secant_card_pos hd (hm k)) (accelBase L μ θ x0) (accelQS θ h) (accelDec θ h) 0)
      (fun _ => o.off K) () ξ = _
  exact accel_exec_aux hd (hmM := hmM) hm L μ θ h x0 o g ξ law K

/-- Expected accuracy of the scheduled accelerated algorithm under the flat oracle law. -/
lemma accel_exec_accuracy {p : Measure Ω} [IsProbabilityMeasure p] {d M K : ℕ} {m : ℕ → ℕ}
    (hmM : ∀ k, m k ≤ M) (hm : ∀ k, 0 < m k) (hd : 0 < d)
    {g : Point d → Ω → ℝ} {f : Point d → ℝ} {σ L μ h θ : ℝ} {x0 xstar : Point d}
    (hh : 0 < h) (hL : 0 < L) (hμ : 0 < μ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hθL : 16 * L * θ ^ 2 ≤ μ)
    (hg : Measurable (Function.uncurry g)) (hgi : ∀ x, Integrable (g x) p)
    (hmean : ∀ x, (∫ ω, g x ω ∂p) = f x)
    (hvi : ∀ x, Integrable (fun ω => (g x ω - f x) ^ 2) p)
    (hv : ∀ x, (∫ ω, (g x ω - f x) ^ 2 ∂p) ≤ σ ^ 2) (hc : ConvexOn ℝ Set.univ f)
    (hgr : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hsc : ∀ x y, f x + ⟪gradient f x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (hmin : IsMinOn f Set.univ xstar)
    (P : ProbabilityMeasure (ℕ → Ω))
    (hind : iIndepFun (fun k (ξ : ℕ → Ω) => ξ k) (P : Measure _))
    (hmarg : ∀ k, (P : Measure _).map (fun ξ : ℕ → Ω => ξ k) = (p : Measure _))
    (o : Offsets d m) :
    Integrable (fun ξ : ℕ → Ω =>
        f (execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
          (accelDescent hd hm L μ θ h x0) (fun _ => o.off K) () ξ) - f xstar) (P : Measure _) ∧
      (∫ ξ, f (execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
          (accelDescent hd hm L μ θ h x0) (fun _ => o.off K) () ξ) - f xstar ∂(P : Measure _))
        ≤ (1 - θ / 2) ^ K * (f x0 - f xstar + μ / 4 * ‖x0 - xstar‖ ^ 2)
          + ∑ k ∈ Finset.range K, (1 - θ / 2) ^ (K - 1 - k)
              * (2 * (3 / (4 * L) + 2 * θ / μ)
                * (8 * (d : ℝ) * σ ^ 2 / (h ^ 2 * (m k)) + 2 * ((d : ℝ) * (L * h / 2) ^ 2))) := by
  classical
  obtain ⟨hgapInt, hgapb⟩ := accel_sched_gap (d := d) (m := m) hmM hm (g := g) (f := f) (σ := σ)
    (L := L) (μ := μ) (h := h) (θ := θ) (xstar := xstar) hh hL hμ hθ0 hθ1 hθL hg hgi hmean hvi hv hc
    hgr hlip hsc hmin x0 K
  have hpre := sched_stream_law_curry (M := M) m o K P hind hmarg
  set Φ : (Fin K → secantSpace d M → Ω) → ℝ := fun Ξ =>
    f (runSched (accelStepSched m hmM L μ θ g h) 0 K (x0, x0) Ξ).1 - f xstar with hΦdef
  set Q : (ℕ → Ω) → (Fin K → secantSpace d M → Ω) := fun ξ =>
    fun k : Fin K => fun t : secantSpace d M =>
      ξ (schedIndex (d := d) (M := M) m o K ⟨k, t⟩) with hQdef
  have hcomp : (fun ξ : ℕ → Ω =>
        f (execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
          (accelDescent hd hm L μ θ h x0) (fun _ => o.off K) () ξ) - f xstar)
      = Φ ∘ Q := by
    refine funext fun ξ => congrArg (fun v => f v - f xstar)
      (execute_accelDescent hd (hmM := hmM) hm L μ θ h x0 o g ξ P K)
  have hpush : (∫ ξ : ℕ → Ω, (Φ ∘ Q) ξ ∂(P : Measure _))
      = ∫ Ξ, Φ Ξ ∂Measure.pi (fun _ : Fin K => slotLaw d M p) :=
    integral_comp_preserving (q := Q) hpre hgapInt
  have hbnd : (∫ ξ : ℕ → Ω, (Φ ∘ Q) ξ ∂(P : Measure _))
      ≤ (1 - θ / 2) ^ K * (f x0 - f xstar + μ / 4 * ‖x0 - xstar‖ ^ 2)
        + ∑ k ∈ Finset.range K, (1 - θ / 2) ^ (K - 1 - k)
            * (2 * (3 / (4 * L) + 2 * θ / μ)
              * (8 * (d : ℝ) * σ ^ 2 / (h ^ 2 * (m k)) + 2 * ((d : ℝ) * (L * h / 2) ^ 2))) := by
    rw [hpush]
    exact hgapb
  refine ⟨hcomp.symm ▸ (hpre.integrable_comp_of_integrable (ε := ℝ) (g := Φ) hgapInt),
    le_of_eq_of_le
      (congrArg (fun F : (ℕ → Ω) → ℝ => ∫ ξ : ℕ → Ω, F ξ ∂(P : Measure _)) hcomp) hbnd⟩

end OracleTemplate.SecantPolyak.Accelerated

import LongTails.Algorithms.DecicStencilMomentumZO
import LongTails.Algorithms.CenteredMomentumSecant
import LongTails.Proofs.DecicStencilStream
import LongTails.Proofs.SecantPolyakScheduledExecution
import LongTails.Proofs.BatchedScheduledExecution

namespace OracleTemplate.SecantPolyak.DecicStencil

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
open OracleTemplate
open SecantDescent SecantPolyak SecantPolyak.Accelerated ZerothOrder
  InexactGradient Scheduled
open OracleTemplate.SecantPolyak.Centered
open LongTails.Setups.ZerothOrderSmoothAndConvex
open OracleTemplate.Research.DecicStencilMomentumZO

variable {Ω : Type} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- Two flat streams that agree on the cells of the schedule give the same ten-point run. -/
lemma dxRunSched_congr {d N : ℕ} {n : ℕ → ℕ} (hnN : ∀ k, 5 * n k ≤ N) (L μ θ : ℝ)
    {g : Point d → Ω → ℝ} (h : ℝ) (i K : ℕ) (s : Point d × Point d)
    (Ξ Ξ' : Fin K → secantSpace d N → Ω)
    (hcell : ∀ (l : ℕ) (hi : i ≤ l) (t : secantSpace d (5 * n l)) (hl : l < i + K),
        Ξ ⟨l - i, by omega⟩ (cellInj (hnN l) t) = Ξ' ⟨l - i, by omega⟩ (cellInj (hnN l) t)) :
    runSched (dxStepSched n hnN L μ θ g h) i K s Ξ
      = runSched (dxStepSched n hnN L μ θ g h) i K s Ξ' := by
  classical
  induction K generalizing i s with
  | zero => rfl
  | succ K ih =>
      show runSched (dxStepSched n hnN L μ θ g h) (i + 1) K
            (dxStepSched n hnN L μ θ g h i s (Ξ 0))
            (fun j : Fin K => Ξ ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
        = runSched (dxStepSched n hnN L μ θ g h) (i + 1) K
            (dxStepSched n hnN L μ θ g h i s (Ξ' 0))
            (fun j : Fin K => Ξ' ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
      have hstep : dxStepSched n hnN L μ θ g h i s (Ξ 0)
          = dxStepSched n hnN L μ θ g h i s (Ξ' 0) := by
        refine congrArg (fun φ : (secantSpace d (5 * n i) → Ω) =>
            step L μ θ s
              (dxReply g h (query θ s) (dxCellsLow φ) (dxCellsMid φ)
                (dxCellsHigh φ) (dxCellsTop φ) (dxCellsFive φ))) ?_
        refine funext fun t => ?_
        have hpre := hcell i (Nat.le_refl i) t (by omega)
        rw [show (⟨i - i, by omega⟩ : Fin (K + 1)) = (0 : Fin (K + 1)) from
            Fin.ext (Nat.sub_self i)] at hpre
        exact hpre
      have hs : ∀ (l : ℕ) (hi : i + 1 ≤ l) (t : secantSpace d (5 * n l)) (hl : l < i + 1 + K),
          (fun j : Fin K => Ξ ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) ⟨l - (i + 1), by omega⟩
              (cellInj (hnN l) t)
            = (fun j : Fin K => Ξ' ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) ⟨l - (i + 1), by omega⟩
                (cellInj (hnN l) t) := by
        intro l hi t hl
        have hp1 : l - i < K + 1 := by omega
        have hp2 : l - (i + 1) + 1 < K + 1 := by omega
        have hf' : (l - i : ℕ) = l - (i + 1) + 1 := by
          rw [← Nat.sub_sub, Nat.sub_add_cancel (show (1 : ℕ) ≤ l - i by omega)]
        have hf : (⟨l - i, hp1⟩ : Fin (K + 1)) = ⟨l - (i + 1) + 1, hp2⟩ := Fin.ext hf'
        have hpre := hcell l (Nat.le_trans (Nat.le_succ i) hi) t (by omega)
        rw [hf] at hpre
        exact hpre
      rw [ih (i + 1) (dxStepSched n hnN L μ θ g h i s (Ξ 0))
        (fun j : Fin K => Ξ ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
        (fun j : Fin K => Ξ' ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) hs, hstep]

/-- Running `K` ten-point rounds on the flat oracle stream reproduces the analysed run. -/
lemma dx_roundsR_eq_runSched {d N : ℕ} {n : ℕ → ℕ} (hnN : ∀ k, 5 * n k ≤ N) (L μ θ h : ℝ)
    (x0 : Point d) (o : Offsets d (fun k => 5 * n k)) (g : Point d → Ω → ℝ) (ξ : ℕ → Ω) :
    ∀ K : ℕ, @StochasticGradient.roundsR (Point d) (Point d) ℝ (Point d) Ω
        (fun k => Fintype.card (secantSpace d (5 * n k))) o.off (cmBase L μ θ x0) (queries θ h)
        (decoder h) g ξ K (0, x0, x0)
      = (K, runSched (dxStepSched n hnN L μ θ g h) 0 K (x0, x0)
          (fun k : Fin K => fun t : secantSpace d N =>
            ξ (schedIndex (fun k => 5 * n k) o K ⟨k, t⟩))) := by
  classical
  intro K
  induction K with
  | zero => rfl
  | succ K ih =>
      have hround : ∀ s, (cmBase L μ θ x0).update (K, s)
            (decoder h K (K, s)
              (fun i : Fin (Fintype.card (secantSpace d (5 * n K))) =>
                g (queries (m := n) θ h K (K, s) i) (ξ (o.off K + i.val))))
          = (K + 1, dxStepSched n hnN L μ θ g h K s
              (fun t : secantSpace d N =>
                ξ (schedIndex (fun k => 5 * n k) o (K + 1)
                  ⟨⟨K, Nat.lt_succ_self K⟩, t⟩))) := by
        intro s
        refine Prod.ext rfl ?_
        show step L μ θ s (decDecode h
              (fun t : secantSpace d (5 * n K) =>
                g (decPoint h (query θ s)
                    (secantSlot (Fintype.equivFin (secantSpace d (5 * n K)) t)))
                  (ξ (o.off K + (Fintype.equivFin (secantSpace d (5 * n K)) t).val)))) = _
        have hq : (fun t : secantSpace d (5 * n K) =>
              g (decPoint h (query θ s)
                  (secantSlot (Fintype.equivFin (secantSpace d (5 * n K)) t)))
                (ξ (o.off K + (Fintype.equivFin (secantSpace d (5 * n K)) t).val)))
            = (fun t : secantSpace d (5 * n K) =>
                g (decPoint h (query θ s) t)
                  ((fun u : secantSpace d (5 * n K) =>
                      ξ (schedIndex (fun k => 5 * n k) o (K + 1)
                        ⟨⟨K, Nat.lt_succ_self K⟩, cellInj (hnN K) u⟩)) t)) := by
          refine funext fun t => ?_
          have h1 : secantSlot (Fintype.equivFin (secantSpace d (5 * n K)) t) = t :=
            secantSlot_equivFin _
          have h2 : ξ (o.off K + (Fintype.equivFin (secantSpace d (5 * n K)) t).val)
              = ξ (schedIndex (fun k => 5 * n k) o (K + 1)
                  ⟨⟨K, Nat.lt_succ_self K⟩, cellInj (hnN K) t⟩) :=
            congrArg ξ ((Scheduled.schedIndex_cellInj o (K + 1) K (Nat.lt_succ_self K) (hnN K) t).symm)
          show g (decPoint h (query θ s)
                (secantSlot (Fintype.equivFin (secantSpace d (5 * n K)) t)))
              (ξ (o.off K + (Fintype.equivFin (secantSpace d (5 * n K)) t).val)) = _
          rw [h1, h2]
        have hz := decDecode_eq_dxReply (g := g) (h := h) (x := query θ s)
          (fun u : secantSpace d (5 * n K) =>
            ξ (schedIndex (fun k => 5 * n k) o (K + 1)
              ⟨⟨K, Nat.lt_succ_self K⟩, cellInj (hnN K) u⟩))
        rw [hq, hz]
        rfl
      have hcon : runSched (dxStepSched n hnN L μ θ g h) 0 K (x0, x0)
            (fun j : Fin K => fun t : secantSpace d N =>
              ξ (schedIndex (fun k => 5 * n k) o (K + 1) ⟨Fin.castAdd 1 j, t⟩))
          = runSched (dxStepSched n hnN L μ θ g h) 0 K (x0, x0)
            (fun k : Fin K => fun t : secantSpace d N =>
              ξ (schedIndex (fun k => 5 * n k) o K ⟨k, t⟩)) := by
        refine dxRunSched_congr hnN L μ θ h 0 K (x0, x0) _ _ ?_
        intro l hi t hl
        show ξ (schedIndex (fun k => 5 * n k) o (K + 1)
              (Fin.castAdd 1 ⟨l - 0, _⟩, cellInj (hnN l) t))
          = ξ (schedIndex (fun k => 5 * n k) o K (⟨l - 0, _⟩, cellInj (hnN l) t))
        exact congrArg ξ ((Scheduled.schedIndex_cellInj o (K + 1) l (by omega) (hnN l) t).trans
          (Scheduled.schedIndex_cellInj o K l (by omega) (hnN l) t).symm)
      show (cmBase L μ θ x0).update
            (@StochasticGradient.roundsR (Point d) (Point d) ℝ (Point d) Ω
              (fun k => Fintype.card (secantSpace d (5 * n k))) o.off (cmBase L μ θ x0)
              (queries θ h) (decoder h) g ξ K (0, x0, x0))
            (decoder h K
              (@StochasticGradient.roundsR (Point d) (Point d) ℝ (Point d) Ω
                (fun k => Fintype.card (secantSpace d (5 * n k))) o.off (cmBase L μ θ x0)
                (queries θ h) (decoder h) g ξ K (0, x0, x0))
              (fun i => g (queries θ h K
                (@StochasticGradient.roundsR (Point d) (Point d) ℝ (Point d) Ω
                  (fun k => Fintype.card (secantSpace d (5 * n k))) o.off (cmBase L μ θ x0)
                  (queries θ h) (decoder h) g ξ K (0, x0, x0)) i) (ξ (o.off K + i.val))))
          = (K + 1, runSched (dxStepSched n hnN L μ θ g h) 0 (K + 1) (x0, x0)
              (fun k : Fin (K + 1) => fun t : secantSpace d N =>
                ξ (schedIndex (fun k => 5 * n k) o (K + 1) ⟨k, t⟩)))
      rw [ih, hround, runSched_snoc]
      simp only [Fin.castSucc]
      rw [hcon]
      simp only [Nat.zero_add]
      exact Prod.ext rfl rfl

lemma dx_exec_aux {d N : ℕ} {n : ℕ → ℕ} (hd : 0 < d) {hnN : ∀ k, 5 * n k ≤ N} (hn : ∀ k, 0 < n k)
    (L μ θ h : ℝ) (x0 : Point d) (o : Offsets d (fun k => 5 * n k)) (g : Point d → Ω → ℝ)
    (ξ : ℕ → Ω) (law : ProbabilityMeasure (ℕ → Ω)) (K : ℕ) :
    execute { Seed := fun _ => Ω, law := law, answer := fun _ (_, x) ω => g x ω }
      (batchedSched (fun k => Fintype.card (secantSpace d (5 * n k)))
        (fun k => secant_card_pos hd (by have h1 := hn k; omega))
        (cmBase L μ θ x0) (queries θ h) (decoder h) 0)
      (fun _ => o.off K) () ξ
      = (runSched (dxStepSched n hnN L μ θ g h) 0 K (x0, x0)
          (fun k : Fin K => fun t : secantSpace d N =>
            ξ (schedIndex (fun k => 5 * n k) o K ⟨k, t⟩))).1 := by
  classical
  refine (StochasticGradient.execute_batchedSched (h0 := o.zero) (hs := fun j => o.step j)
    (law := law) (K := K) (seed := ())).trans ?_
  rw [show (cmBase L μ θ x0).initial () = (0, x0, x0) from rfl]
  exact ((congrArg (fun st => (cmBase L μ θ x0).output st)
      (dx_roundsR_eq_runSched hnN L μ θ h x0 o g ξ K)).trans rfl)

/-- The executed ten-point algorithm coincides with the analysed run. -/
lemma execute_dxAlgorithm {d N : ℕ} {n : ℕ → ℕ} (hd : 0 < d) {hnN : ∀ k, 5 * n k ≤ N}
    (hn : ∀ k, 0 < n k) (L μ θ h : ℝ) (x0 : Point d) (o : Offsets d (fun k => 5 * n k))
    (g : Point d → Ω → ℝ) (ξ : ℕ → Ω) (law : ProbabilityMeasure (ℕ → Ω)) (K : ℕ) :
    execute { Seed := fun _ => Ω, law := law, answer := fun _ (_, x) ω => g x ω }
      (algorithm hd hn L μ θ h x0) (fun _ => o.off K) () ξ
      = (runSched (dxStepSched n hnN L μ θ g h) 0 K (x0, x0)
          (fun k : Fin K => fun t : secantSpace d N =>
            ξ (schedIndex (fun k => 5 * n k) o K ⟨k, t⟩))).1 := by
  show execute { Seed := fun _ => Ω, law := law, answer := fun _ (_, x) ω => g x ω }
      (batchedSched (fun k => Fintype.card (secantSpace d (5 * n k)))
        (fun k => secant_card_pos hd (by have h1 := hn k; omega))
        (cmBase L μ θ x0) (queries θ h) (decoder h) 0)
      (fun _ => o.off K) () ξ = _
  exact dx_exec_aux hd (hnN := hnN) hn L μ θ h x0 o g ξ law K

/-- Expected accuracy of the executed ten-point algorithm under the flat oracle law. -/
lemma dx_exec_accuracy {p : Measure Ω} [IsProbabilityMeasure p] {d N K : ℕ} {n : ℕ → ℕ}
    (hnN : ∀ k, 5 * n k ≤ N) (hn : ∀ k, 0 < n k) (hd : 0 < d)
    {g : Point d → Ω → ℝ} {f : Point d → ℝ} {σ L μ h θ B : ℝ} {x0 xstar : Point d}
    (hh : 0 < h) (hL : 0 < L) (hμ : 0 < μ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hθL : 16 * L * θ ^ 2 ≤ μ)
    (hbias : ∀ y, ‖dxDiff h f y - gradient f y‖ ^ 2 ≤ B)
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
    (o : Offsets d (fun k => 5 * n k)) :
    Integrable (fun ξ : ℕ → Ω =>
        f (execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
          (algorithm hd hn L μ θ h x0) (fun _ => o.off K) () ξ) - f xstar) (P : Measure _) ∧
      (∫ ξ, f (execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
          (algorithm hd hn L μ θ h x0) (fun _ => o.off K) () ξ) - f xstar ∂(P : Measure _))
        ≤ (1 - θ / 2) ^ K * (f x0 - f xstar + μ / 4 * ‖x0 - xstar‖ ^ 2)
          + ∑ k ∈ Finset.range K, (1 - θ / 2) ^ (K - 1 - k)
              * (2 * (3 / (4 * L) + 2 * θ / μ) * B
                + (1 / (2 * L) + θ ^ 2 / μ) * (6 * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (n k))))) := by
  classical
  obtain ⟨hgapInt, hgapb⟩ := dx_sched_gap (d := d) (n := n) hnN hn (B := B) (g := g) (f := f)
    (σ := σ) (L := L) (μ := μ) (h := h) (θ := θ) (xstar := xstar) hh hL hμ hθ0 hθ1 hθL hbias hg
    hgi hmean hvi hv hc hgr hlip hsc hmin x0 K
  have hpre := sched_stream_law_curry (M := N) (fun k => 5 * n k) o K P hind hmarg
  set Φ : (Fin K → secantSpace d N → Ω) → ℝ := fun Ξ =>
    f (runSched (dxStepSched n hnN L μ θ g h) 0 K (x0, x0) Ξ).1 - f xstar with hΦdef
  set Q : (ℕ → Ω) → (Fin K → secantSpace d N → Ω) := fun ξ =>
    fun k : Fin K => fun t : secantSpace d N =>
      ξ (schedIndex (d := d) (M := N) (fun k => 5 * n k) o K ⟨k, t⟩) with hQdef
  have hcomp : (fun ξ : ℕ → Ω =>
        f (execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
          (algorithm hd hn L μ θ h x0) (fun _ => o.off K) () ξ) - f xstar)
      = Φ ∘ Q := by
    refine funext fun ξ => congrArg (fun v => f v - f xstar)
      (execute_dxAlgorithm hd (hnN := hnN) hn L μ θ h x0 o g ξ P K)
  have hpush : (∫ ξ : ℕ → Ω, (Φ ∘ Q) ξ ∂(P : Measure _))
      = ∫ Ξ, Φ Ξ ∂Measure.pi (fun _ : Fin K => slotLaw d N p) :=
    integral_comp_preserving (q := Q) hpre hgapInt
  have hbnd : (∫ ξ : ℕ → Ω, (Φ ∘ Q) ξ ∂(P : Measure _))
      ≤ (1 - θ / 2) ^ K * (f x0 - f xstar + μ / 4 * ‖x0 - xstar‖ ^ 2)
        + ∑ k ∈ Finset.range K, (1 - θ / 2) ^ (K - 1 - k)
            * (2 * (3 / (4 * L) + 2 * θ / μ) * B
              + (1 / (2 * L) + θ ^ 2 / μ) * (6 * ((d : ℝ) * σ ^ 2 / (h ^ 2 * (n k))))) := by
    rw [hpush]
    exact hgapb
  refine ⟨hcomp.symm ▸ (hpre.integrable_comp_of_integrable (ε := ℝ) (g := Φ) hgapInt),
    le_of_eq_of_le
      (congrArg (fun F : (ℕ → Ω) → ℝ => ∫ ξ : ℕ → Ω, F ξ ∂(P : Measure _)) hcomp) hbnd⟩

end OracleTemplate.SecantPolyak.DecicStencil

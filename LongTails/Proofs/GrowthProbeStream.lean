import LongTails.Setups.ZerothOrderSmoothingGrowthConvex
import LongTails.Proofs.GrowthProbeRound
import LongTails.Proofs.InterpolatedProbeStream
import LongTails.Proofs.InterpolatedProbeRound

set_option maxHeartbeats 4000000

/-!
Rounds of averaged probe descent run on the product sample space. The squared distance to the
surrogate minimizer together with the accumulated smoothed gaps forms a supermartingale, so the
total decrease of the distance potential bounds the accumulated gaps. Jensen's inequality then turns
the running sum of visited points into the accuracy of the averaged output.
-/

namespace OracleTemplate.SecantPolyak.GrowthConvex

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators RealInnerProductSpace
open OracleTemplate _root_.OracleTemplate.Gradient SecantDescent SecantPolyak
  SecantPolyak.Scheduled SecantPolyak.Centered SecantPolyak.DirectionSampled
open LongTails.Proofs.AuxiliaryInner
open LongTails.Setups.ZerothOrderSmoothAndConvex
open OracleTemplate.SecantPolyak.Interpolated (roundOf_devAt measurable_ipRound)

variable {Ω : Type} [MeasurableSpace Ω] {d : ℕ} {g : Point d → Ω → ℝ} {fh : Point d → ℝ}
  {xh : Point d} {W : Measure (Point d × Ω)} [IsProbabilityMeasure W] {L ρ η h : ℝ}

/-- Analysis state of averaged probe descent: current point, running sum of visited points, and
accumulated smoothed gaps. -/
abbrev GPState (d : ℕ) := Point d × Point d × ℝ

/-- One averaged probe descent round on the analysis state. -/
noncomputable def gpStep (g : Point d → Ω → ℝ) (fh : Point d → ℝ) (xh : Point d) (η h : ℝ) :
    ℕ → GPState d → (secantSpace 1 1 → Point d × Ω) → GPState d :=
  fun _ s Ξ =>
    (s.1 - η • roundOf h g s.1 1 Ξ, s.2.1 + s.1, s.2.2 + (fh s.1 - fh xh))

/-- Potential of an analysis state: squared distance to the surrogate minimizer plus the
accumulated smoothed gaps weighted by the step size. -/
noncomputable def gpPot (xh : Point d) (η : ℝ) (s : GPState d) : ℝ :=
  ‖s.1 - xh‖ ^ 2 + η * s.2.2

/-- The round surrogate is measurable jointly in the analysis state and the round samples. -/
lemma gp_round_m {g : Point d → Ω → ℝ} (hg : Measurable (Function.uncurry g)) (h : ℝ) :
    Measurable (fun q : GPState d × (secantSpace 1 1 → Point d × Ω) =>
      roundOf h g q.1.1 1 q.2) := by
  classical
  have hx : Measurable (fun q : GPState d × (secantSpace 1 1 → Point d × Ω) => q.1.1) :=
    measurable_fst.comp measurable_fst
  have h2 (t : secantSpace 1 1) :
      Measurable (fun q : GPState d × (secantSpace 1 1 → Point d × Ω) => (q.2 t).2) :=
    measurable_snd.comp ((measurable_pi_apply t).comp measurable_snd)
  have hs (t : secantSpace 1 1) : Measurable (fun q : GPState d × (secantSpace 1 1 → Point d × Ω) =>
      g (q.1.1 + (if t.2.2 then h else -h) • (q.2 t).1) (q.2 t).2) := by
    have hsa : Measurable (fun q : GPState d × (secantSpace 1 1 → Point d × Ω) =>
        (if t.2.2 then h else (-h)) • (q.2 t).1) := by fun_prop
    exact hg.comp ((hx.add hsa).prodMk (h2 t))
  have ht (t : secantSpace 1 1) : Measurable (fun q : GPState d × (secantSpace 1 1 → Point d × Ω) =>
      (if t.2.2 then (1 : ℝ) else (-1 : ℝ)) •
        ((1 / (2 * h)) •
          (g (q.1.1 + (if t.2.2 then h else -h) • (q.2 t).1) (q.2 t).2 • (q.2 t).1))) := by
    fun_prop
  have hsum : Measurable (fun q : GPState d × (secantSpace 1 1 → Point d × Ω) =>
      ∑ t : secantSpace 1 1, (if t.2.2 then (1 : ℝ) else (-1 : ℝ)) •
        ((1 / (2 * h)) •
          (g (q.1.1 + (if t.2.2 then h else -h) • (q.2 t).1) (q.2 t).2 • (q.2 t).1))) :=
    Finset.measurable_sum Finset.univ fun t _ => ht t
  have hfun : (fun q : GPState d × (secantSpace 1 1 → Point d × Ω) => roundOf h g q.1.1 1 q.2)
      = fun q => ∑ t : secantSpace 1 1, (if t.2.2 then (1 : ℝ) else (-1 : ℝ)) •
          ((1 / (2 * h)) •
            (g (q.1.1 + (if t.2.2 then h else -h) • (q.2 t).1) (q.2 t).2 • (q.2 t).1)) := by
    funext q
    simp only [roundOf, slotVal, Nat.cast_one, div_one, one_smul]
  rw [hfun]
  exact hsum

/-- The joint map of one averaged probe descent round is measurable. -/
lemma measurable_gpStep {g : Point d → Ω → ℝ} {fh : Point d → ℝ}
    (hg : Measurable (Function.uncurry g)) (hfm : Measurable fh) (xh : Point d) (η h : ℝ) (k : ℕ) :
    Measurable (fun q : GPState d × (secantSpace 1 1 → Point d × Ω) =>
      gpStep (g := g) (fh := fh) (xh := xh) (η := η) (h := h) k q.1 q.2) := by
  classical
  have hr := gp_round_m (hg := hg) (h := h)
  show Measurable fun q : GPState d × (secantSpace 1 1 → Point d × Ω) =>
      (q.1.1 - η • roundOf h g q.1.1 1 q.2, q.1.2.1 + q.1.1, q.1.2.2 + (fh q.1.1 - fh xh))
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
  · refine Measurable.sub (measurable_fst.comp measurable_fst) ?_
    exact (measurable_const :
      Measurable (fun _ : GPState d × (secantSpace 1 1 → Point d × Ω) => η)).smul hr
  · exact (measurable_fst.comp (measurable_snd.comp measurable_fst)).add
      (measurable_fst.comp measurable_fst)
  · refine (measurable_snd.comp (measurable_snd.comp measurable_fst)).add ?_
    exact (hfm.comp (measurable_fst.comp measurable_fst)).sub measurable_const

/-- The hypotheses used by averaged probe descent: a convex smoothed surrogate with an
`L`-Lipschitz gradient that attains its minimum at `xh`, mirrored probes that are integrable,
unbiased, and have variance at most `ρ²` times the current smoothed gap, and a step size admissible
for the drift. -/
structure GPHyp (g : Point d → Ω → ℝ) (fh : Point d → ℝ) (xh : Point d)
    (L ρ η h : ℝ) (W : Measure (Point d × Ω)) : Prop where
  hL : 0 < L
  eta0 : 0 ≤ η
  cap : 4 * η * (L + ρ ^ 2) ≤ 1
  convex : ConvexOn ℝ Set.univ fh
  grad : ∀ x, HasGradientAt fh (gradient fh x) x
  lip : ∀ x y, ‖gradient fh x - gradient fh y‖ ≤ L * ‖x - y‖
  min : ∀ x, fh xh ≤ fh x
  gmeas : Measurable (Function.uncurry g)
  fmeas : Measurable fh
  slotInt : ∀ x s, Integrable (fun u : Point d × Ω => slotVal h g x s u - halfGrad fh x s) W
  varInt : ∀ x s, Integrable (fun u : Point d × Ω => ‖slotVal h g x s u - halfGrad fh x s‖ ^ 2) W
  mean : ∀ x s, (∫ u : Point d × Ω, slotVal h g x s u ∂W) = halfGrad fh x s
  var : ∀ x s, (∫ u : Point d × Ω, ‖slotVal h g x s u - halfGrad fh x s‖ ^ 2 ∂W)
      ≤ ρ ^ 2 * (fh x - fh xh)

/-- Extract the single-round drift from the bundled hypotheses. -/
lemma gp_hyp_round (M : GPHyp g fh xh L ρ η h W) (x : Point d) :
    Integrable (fun ω : secantSpace 1 1 → Point d × Ω => ‖x - η • roundOf h g x 1 ω - xh‖ ^ 2)
        (slotLaw 1 1 W) ∧
      (∫ ω, ‖x - η • roundOf h g x 1 ω - xh‖ ^ 2 ∂(slotLaw 1 1 W)) ≤
        ‖x - xh‖ ^ 2 - η * (fh x - fh xh) := by
  exact gp_one_round (hL := M.hL) (hη0 := M.eta0) (hη := M.cap) (hc := M.convex)
    (hgr := M.grad) (hlip := M.lip) (hminh := fun y _ => M.min y) (hg := M.gmeas)
    (hint := M.slotInt) (hvar2 := M.varInt) (hmean := M.mean) (hvar := fun st => M.var x st)
    (x := x)

/-- One averaged probe descent round does not increase the potential in expectation. -/
lemma gp_step_potential (M : GPHyp g fh xh L ρ η h W) (i : ℕ) (s : GPState d) :
    Integrable (fun Ξ : secantSpace 1 1 → Point d × Ω =>
        gpPot xh η (gpStep g fh xh η h i s Ξ)) (slotLaw 1 1 W) ∧
      (∫ Ξ, gpPot xh η (gpStep g fh xh η h i s Ξ) ∂(slotLaw 1 1 W)) ≤ gpPot xh η s := by
  classical
  have h1 := gp_hyp_round (M := M) (x := s.1)
  have hx : (fun Ξ : secantSpace 1 1 → Point d × Ω => gpPot xh η (gpStep g fh xh η h i s Ξ)) =
      fun Ξ => ‖s.1 - η • roundOf h g s.1 1 Ξ - xh‖ ^ 2 + η * (s.2.2 + (fh s.1 - fh xh)) := by
    funext Ξ
    show ‖(s.1 - η • roundOf h g s.1 1 Ξ) - xh‖ ^ 2 + η * (s.2.2 + (fh s.1 - fh xh)) = _
    rfl
  constructor
  · rw [hx]
    exact h1.1.add (integrable_const _)
  · rw [hx, integral_add h1.1 (integrable_const _)]
    have hC : (∫ _Ξ : secantSpace 1 1 → Point d × Ω,
        (η * (s.2.2 + (fh s.1 - fh xh)) : ℝ) ∂(slotLaw 1 1 W)) = η * (s.2.2 + (fh s.1 - fh xh)) := by
      rw [integral_const, probReal_univ, one_smul]
    rw [hC]
    have hp2 : gpPot xh η s = ‖s.1 - xh‖ ^ 2 + η * s.2.2 := rfl
    rw [hp2]
    nlinarith

omit [MeasurableSpace Ω] in
/-- The accumulated gaps stay nonnegative along a run started from a nonnegative accumulator. -/
lemma gp_bnonneg {fh : Point d → ℝ} (hmin : ∀ x, fh xh ≤ fh x) :
    ∀ (K : ℕ) (i : ℕ) (s : GPState d) (Ξ : Fin K → secantSpace 1 1 → Point d × Ω),
      0 ≤ s.2.2 → 0 ≤ (runSched (gpStep g fh xh η h) i K s Ξ).2.2 := by
  intro K
  induction K with
  | zero => intro i s Ξ hb; simpa [runSched] using hb
  | succ K ih =>
      intro i s Ξ hb
      have hgap : 0 ≤ fh s.1 - fh xh := sub_nonneg.mpr (hmin s.1)
      have h1 : 0 ≤ (gpStep g fh xh η h i s (Ξ 0)).2.2 := by
        show 0 ≤ s.2.2 + (fh s.1 - fh xh)
        nlinarith
      show 0 ≤ (runSched (gpStep g fh xh η h) (i + 1) K (gpStep g fh xh η h i s (Ξ 0))
          (fun j => Ξ j.succ)).2.2
      exact ih (i + 1) (gpStep g fh xh η h i s (Ξ 0)) (fun j => Ξ j.succ) h1

/-- The potential of averaged probe descent is a supermartingale along the scheduled run. -/
lemma gp_supermart (M : GPHyp g fh xh L ρ η h W) : ∀ (K : ℕ), ∀ (i : ℕ) (s0 : GPState d),
    0 ≤ s0.2.2 →
      Integrable (fun Ξ : Fin K → secantSpace 1 1 → Point d × Ω =>
          gpPot xh η (runSched (gpStep g fh xh η h) i K s0 Ξ))
          (Measure.pi (fun _ : Fin K =>
            (slotLaw 1 1 W : Measure (secantSpace 1 1 → Point d × Ω)))) ∧
        (∫ Ξ, gpPot xh η (runSched (gpStep g fh xh η h) i K s0 Ξ)
            ∂(Measure.pi (fun _ : Fin K =>
              (slotLaw 1 1 W : Measure (secantSpace 1 1 → Point d × Ω))))) ≤ gpPot xh η s0 := by
  classical
  have hstep : ∀ k, Measurable (fun q : GPState d × (secantSpace 1 1 → Point d × Ω) =>
      gpStep (g := g) (fh := fh) (xh := xh) (η := η) (h := h) k q.1 q.2) :=
    fun k => measurable_gpStep (hg := M.gmeas) (hfm := M.fmeas) (xh := xh) (η := η) (h := h) k
  have hV : Measurable (gpPot xh η) := by
    show Measurable (fun s : GPState d => ‖s.1 - xh‖ ^ 2 + η * s.2.2)
    have hn : Measurable (fun s : GPState d => ‖s.1 - xh‖) :=
      Measurable.norm ((measurable_fst : Measurable (fun p : GPState d => p.1)).sub measurable_const)
    refine Measurable.add ?_ ?_
    · exact Measurable.pow hn measurable_const
    · exact measurable_const.mul (measurable_snd.comp measurable_snd)
  have hbound (i : ℕ) (s : GPState d) :
      Integrable (fun Ξ : secantSpace 1 1 → Point d × Ω =>
          gpPot xh η (gpStep (g := g) (fh := fh) (xh := xh) (η := η) (h := h) i s Ξ))
          (slotLaw 1 1 W) ∧
        (∫ Ξ, gpPot xh η (gpStep (g := g) (fh := fh) (xh := xh) (η := η) (h := h) i s Ξ)
            ∂(slotLaw 1 1 W)) ≤ gpPot xh η s := gp_step_potential (M := M) i s
  intro K
  induction K with
  | zero =>
      intro i s0 hb
      constructor
      · change Integrable (fun _ : Fin 0 → secantSpace 1 1 → Point d × Ω => gpPot xh η s0)
          (Measure.pi (fun _ : Fin 0 => (slotLaw 1 1 W : Measure (secantSpace 1 1 → Point d × Ω))))
        exact integrable_const _
      · simp [runSched, measureReal_def]
  | succ K ih =>
      intro i s0 hb
      let P1 : Measure (secantSpace 1 1 → Point d × Ω) := slotLaw 1 1 W
      let PK : Measure (Fin K → secantSpace 1 1 → Point d × Ω) :=
        Measure.pi (fun _ : Fin K => (P1 : Measure (secantSpace 1 1 → Point d × Ω)))
      let F := fun a : (secantSpace 1 1 → Point d × Ω) × (Fin K → secantSpace 1 1 → Point d × Ω) =>
        gpPot xh η (runSched (gpStep g fh xh η h) (i + 1) K (gpStep g fh xh η h i s0 a.1) a.2)
      have hn (a : secantSpace 1 1 → Point d × Ω) :
          0 ≤ (gpStep g fh xh η h i s0 a).2.2 := by
        show 0 ≤ s0.2.2 + (fh s0.1 - fh xh)
        nlinarith [sub_nonneg.mpr (M.min s0.1)]
      have hFc : Measurable F := (hV.comp
        ((measurable_runSched hstep K (i + 1)).comp
          (((hstep i).comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)))
      have hFm : AEStronglyMeasurable F (P1.prod PK) := hFc.aestronglyMeasurable
      have hF0 (a : (secantSpace 1 1 → Point d × Ω) × (Fin K → secantSpace 1 1 → Point d × Ω)) :
          0 ≤ F a :=
        add_nonneg (sq_nonneg _)
          (mul_nonneg M.eta0
            (gp_bnonneg (g := g) (fh := fh) (xh := xh) (η := η) (h := h) (hmin := M.min)
              K (i + 1) (gpStep g fh xh η h i s0 a.1) a.2 (hn a.1)))
      have hNorm (a : secantSpace 1 1 → Point d × Ω) :
          (∫ t, ‖F (a, t)‖ ∂PK) = ∫ t, F (a, t) ∂PK := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun t => by
          change ‖F (a, t)‖ = F (a, t)
          rw [Real.norm_eq_abs, abs_of_nonneg (hF0 (a, t))])
      have hBound : Integrable (fun a => gpPot xh η (gpStep g fh xh η h i s0 a)) P1 :=
        (hbound i s0).1
      have hOuter : Integrable (fun a => ∫ t, ‖F (a, t)‖ ∂PK) P1 := by
        apply hBound.mono' hFm.norm.integral_prod_right'
        apply Filter.Eventually.of_forall
        intro a
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun t => norm_nonneg _)), hNorm]
        exact (ih (i + 1) (gpStep g fh xh η h i s0 a) (hn a)).2
      have hFi : Integrable F (P1.prod PK) :=
        (integrable_prod_iff hFm).mpr
          ⟨Filter.Eventually.of_forall (fun a =>
            (ih (i + 1) (gpStep g fh xh η h i s0 a) (hn a)).1), hOuter⟩
      have hp := (measurePreserving_piFinSuccAbove
        (fun _ : Fin (K + 1) => (P1 : Measure (secantSpace 1 1 → Point d × Ω))) 0).symm
      have hPi : Integrable (fun Ξ => gpPot xh η (runSched (gpStep g fh xh η h) i (K + 1) s0 Ξ))
          (Measure.pi (fun _ : Fin (K + 1) => (P1 : Measure (secantSpace 1 1 → Point d × Ω)))) := by
        rw [← hp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)]
        simpa only [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNthEquiv, Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk,
          runSched, Fin.cons_zero, Fin.cons_succ, cast_eq] using hFi
      refine ⟨hPi, ?_⟩
      have he : (∫ Ξ, gpPot xh η (runSched (gpStep g fh xh η h) i (K + 1) s0 Ξ)
            ∂(Measure.pi (fun _ : Fin (K + 1) =>
              (P1 : Measure (secantSpace 1 1 → Point d × Ω))))) =
          ∫ a, F a ∂(P1.prod PK) := by
        rw [← hp.integral_comp']
        simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNthEquiv, Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk,
          runSched, Fin.cons_zero, Fin.cons_succ, cast_eq]
        rfl
      rw [he, integral_prod _ hFi]
      have hIntg : Integrable (fun a => ∫ t, F (a, t) ∂PK) P1 :=
        hOuter.congr (Filter.Eventually.of_forall fun a => hNorm a)
      have hpt : (fun a => ∫ t, F (a, t) ∂PK) ≤
          fun Ξ => gpPot xh η (gpStep g fh xh η h i s0 Ξ) := fun a =>
        (ih (i + 1) (gpStep g fh xh η h i s0 a) (hn a)).2
      refine le_trans (integral_mono hIntg (hbound i s0).1 hpt) ((hbound i s0).2)

omit [MeasurableSpace Ω] in
/-- The two accumulators of the analysis state are the sums of the visited points and of their
smoothed values. -/
lemma gp_accumulate {fh : Point d → ℝ} {xh : Point d} :
    ∀ (K : ℕ) (i : ℕ) (s : GPState d) (Ξ : Fin K → secantSpace 1 1 → Point d × Ω),
      ∃ f : ℕ → Point d,
        (runSched (gpStep g fh xh η h) i K s Ξ).2.1 = s.2.1 + ∑ k ∈ Finset.range K, f k ∧
        (runSched (gpStep g fh xh η h) i K s Ξ).2.2 =
          s.2.2 + ∑ k ∈ Finset.range K, fh (f k) - (K : ℝ) * fh xh := by
  intro K
  induction K with
  | zero =>
      intro i s Ξ
      refine ⟨fun _ => 0, ?_, ?_⟩ <;> simp [runSched]
  | succ K ih =>
      intro i s Ξ
      obtain ⟨f, h1, h2⟩ := ih (i + 1) (gpStep g fh xh η h i s (Ξ 0)) (fun j => Ξ j.succ)
      have hs1 : (gpStep g fh xh η h i s (Ξ 0)).2.1 = s.2.1 + s.1 := rfl
      have hs2 : (gpStep g fh xh η h i s (Ξ 0)).2.2 = s.2.2 + (fh s.1 - fh xh) := rfl
      refine ⟨fun k => if k = K then s.1 else f k, ?_, ?_⟩
      · show (runSched (gpStep g fh xh η h) (i + 1) K (gpStep g fh xh η h i s (Ξ 0))
            (fun j => Ξ j.succ)).2.1 = _
        have hc : (∑ k ∈ Finset.range (K + 1), (if k = K then s.1 else f k))
            = (∑ k ∈ Finset.range K, f k) + s.1 := by
          rw [Finset.sum_range_succ]
          have hsum : (∑ k ∈ Finset.range K, (if k = K then s.1 else f k))
              = ∑ k ∈ Finset.range K, f k := by
            refine Finset.sum_congr rfl (fun k hk => ?_)
            split
            · have hk' := Finset.mem_range.mp hk
              omega
            · rfl
          have hlast : (if (K : ℕ) = K then s.1 else f K) = s.1 := by
            split
            · rfl
            · exact absurd (rfl : (K : ℕ) = K) (by assumption)
          rw [hsum, hlast]
        rw [h1, hs1, hc]
        abel
      · show (runSched (gpStep g fh xh η h) (i + 1) K (gpStep g fh xh η h i s (Ξ 0))
            (fun j => Ξ j.succ)).2.2 = _
        have hc : (∑ k ∈ Finset.range (K + 1), fh (if k = K then s.1 else f k))
            = (∑ k ∈ Finset.range K, fh (f k)) + fh s.1 := by
          rw [Finset.sum_range_succ]
          have hsum : (∑ k ∈ Finset.range K, fh (if k = K then s.1 else f k))
              = ∑ k ∈ Finset.range K, fh (f k) := by
            refine Finset.sum_congr rfl (fun k hk => ?_)
            split
            · have hk' := Finset.mem_range.mp hk
              omega
            · rfl
          have hlast : fh (if (K : ℕ) = K then s.1 else f K) = fh s.1 := by
            split
            · rfl
            · exact absurd (rfl : (K : ℕ) = K) (by assumption)
          rw [hsum, hlast]
        rw [h2, hs2, hc]
        push_cast
        ring

/-- Jensen's inequality for the average of the visited points. -/
lemma gp_avg_le {fh : Point d → ℝ} (hfhc : ConvexOn ℝ Set.univ fh) {K : ℕ} (hK : 0 < K)
    (f : ℕ → Point d) :
    fh ((1 / (K : ℝ)) • ∑ k ∈ Finset.range K, f k)
        ≤ ∑ k ∈ Finset.range K, (1 / (K : ℝ)) * fh (f k) := by
  classical
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hw : ∑ k ∈ Finset.range K, (1 : ℝ) / (K : ℝ) = 1 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  have hj := ConvexOn.map_sum_le (t := Finset.range K) (w := fun _ : ℕ => (1 : ℝ) / (K : ℝ))
    (p := f) hfhc (fun _ _ => by positivity) hw (fun _ _ => Set.mem_univ _)
  rw [Finset.smul_sum]
  simpa [smul_eq_mul] using hj

/-- Jensen's inequality turns the accumulated smoothed values into the accuracy of the average. -/
lemma gp_avg_gap_le {fh : Point d → ℝ} {xh : Point d} (hfhc : ConvexOn ℝ Set.univ fh)
    {K : ℕ} (hK : 0 < K) {s : GPState d} (f : ℕ → Point d)
    (ha : s.2.1 = ∑ k ∈ Finset.range K, f k)
    (hb : s.2.2 = ∑ k ∈ Finset.range K, fh (f k) - (K : ℝ) * fh xh) :
    fh ((1 / (K : ℝ)) • s.2.1) - fh xh ≤ s.2.2 / (K : ℝ) := by
  have h4 : ∑ k ∈ Finset.range K, fh (f k) = s.2.2 + (K : ℝ) * fh xh := by linarith
  have h5 : (1 / (K : ℝ)) * (s.2.2 + (K : ℝ) * fh xh) = s.2.2 / (K : ℝ) + fh xh := by
    field_simp
  have hj := gp_avg_le (hfhc := hfhc) (hK := hK) (f := f)
  rw [← Finset.mul_sum, h4, h5, ← ha] at hj
  linarith

end OracleTemplate.SecantPolyak.GrowthConvex

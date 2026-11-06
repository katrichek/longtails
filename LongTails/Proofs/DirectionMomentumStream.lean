import LongTails.Proofs.CenteredMomentumStream
import LongTails.Proofs.DirectionMomentumRound
import LongTails.Proofs.DirectionMomentumStep

set_option maxHeartbeats 2000000

/-!
Momentum rounds driven by direction-sampled surrogates. A round asks for `2 * m` one-sided probes
along independent directions drawn from the model's direction measure. Each probe of side `s` is
unbiased for the signed half of the smoothed gradient, so the round is unbiased for the smoothed
gradient itself, and independent probes divide its mean-square deviation by `m`. The momentum
recursion then pays `(1 / (2 * L) + θ ^ 2 / μ)` times that deviation, with no bias term.
-/

namespace OracleTemplate.SecantPolyak.DirectionSampled

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
open OracleTemplate InexactGradient SecantPolyak SecantPolyak.Accelerated SecantPolyak.Scheduled
  SecantDescent
open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {Ω : Type} [MeasurableSpace Ω] {d : ℕ}

/-- The law of one direction-sampled probe: an independent direction and value sample. -/
noncomputable def probeMeasure (nu : ProbabilityMeasure (Point d)) (p : Measure Ω) :
    Measure (Point d × Ω) := (nu : Measure (Point d)).prod p

instance probeMeasure_isProbability {nu : ProbabilityMeasure (Point d)} {p : Measure Ω}
    [IsProbabilityMeasure p] : IsProbabilityMeasure (probeMeasure nu p) := by
  unfold probeMeasure
  infer_instance

/-- One direction-sampled momentum round at the ambient cell law. -/
noncomputable def dirStepSched {M : ℕ} (m : ℕ → ℕ) (hmM : ∀ k, m k ≤ M) (L μ θ : ℝ)
    (g : Point d → Ω → ℝ) (h : ℝ) (k : ℕ) (s : Point d × Point d)
    (ω : secantSpace 1 M → Point d × Ω) : Point d × Point d :=
  step L μ θ s (roundOf h g (query θ s) (m k)
    (fun t : secantSpace 1 (m k) => ω (cellInj (hmM k) t)))

/-- The anchor of a momentum state is a measurable function of the state. -/
lemma measurable_query {θ : ℝ} : Measurable (fun s : Point d × Point d => query θ s) := by
  show Measurable (fun s : Point d × Point d => (1 / (1 + θ)) • (s.1 + θ • s.2))
  fun_prop

/-- The surrogate of one round is a measurable function of the state and the ambient samples. -/
lemma measurable_dirRound {M : ℕ} (m : ℕ → ℕ) (hmM : ∀ k, m k ≤ M)
    {g : Point d → Ω → ℝ} (hg : Measurable (Function.uncurry g)) (h θ : ℝ) (k : ℕ) :
    Measurable (fun q : (Point d × Point d) × (secantSpace 1 M → Point d × Ω) =>
      roundOf h g (query θ q.1) (m k) (fun t : secantSpace 1 (m k) => q.2 (cellInj (hmM k) t))) := by
  classical
  have hq : Measurable (fun q : (Point d × Point d) × (secantSpace 1 M → Point d × Ω) => query θ q.1) := measurable_query.comp measurable_fst
  have hcell (t : secantSpace 1 (m k)) : Measurable (fun q : (Point d × Point d) × (secantSpace 1 M → Point d × Ω) => q.2 (cellInj (hmM k) t)) :=
    (measurable_pi_apply (cellInj (hmM k) t)).comp measurable_snd
  have h1 (t : secantSpace 1 (m k)) : Measurable (fun q : (Point d × Point d) × (secantSpace 1 M → Point d × Ω) => (q.2 (cellInj (hmM k) t)).1) :=
    measurable_fst.comp (hcell t)
  have h2 (t : secantSpace 1 (m k)) : Measurable (fun q : (Point d × Point d) × (secantSpace 1 M → Point d × Ω) => (q.2 (cellInj (hmM k) t)).2) :=
    measurable_snd.comp (hcell t)
  have hs (t : secantSpace 1 (m k)) : Measurable (fun q : (Point d × Point d) × (secantSpace 1 M → Point d × Ω) =>
      g (query θ q.1 + (if t.2.2 then h else -h) • (q.2 (cellInj (hmM k) t)).1)
        (q.2 (cellInj (hmM k) t)).2) := by
    have hs1 : Measurable (fun q : (Point d × Point d) × (secantSpace 1 M → Point d × Ω) =>
        (if t.2.2 then h else (-h)) • (q.2 (cellInj (hmM k) t)).1) := by fun_prop
    have hp : Measurable (fun q : (Point d × Point d) × (secantSpace 1 M → Point d × Ω) =>
        (query θ q.1 + (if t.2.2 then h else -h) • (q.2 (cellInj (hmM k) t)).1,
          (q.2 (cellInj (hmM k) t)).2)) := (hq.add hs1).prodMk (h2 t)
    exact hg.comp hp
  have ht (t : secantSpace 1 (m k)) : Measurable (fun q : (Point d × Point d) × (secantSpace 1 M → Point d × Ω) =>
      (if t.2.2 then (1 : ℝ) else (-1 : ℝ)) •
        ((1 / (2 * h)) •
          ((g (query θ q.1 + (if t.2.2 then h else -h) • (q.2 (cellInj (hmM k) t)).1)
              (q.2 (cellInj (hmM k) t)).2) • (q.2 (cellInj (hmM k) t)).1))) := by
    fun_prop
  have hsum : Measurable (fun q : (Point d × Point d) × (secantSpace 1 M → Point d × Ω) => ∑ t : secantSpace 1 (m k),
      (if t.2.2 then (1 : ℝ) else (-1 : ℝ)) •
        ((1 / (2 * h)) •
          ((g (query θ q.1 + (if t.2.2 then h else -h) • (q.2 (cellInj (hmM k) t)).1)
              (q.2 (cellInj (hmM k) t)).2) • (q.2 (cellInj (hmM k) t)).1))) :=
    Finset.measurable_sum Finset.univ fun t _ => ht t
  have hc : Measurable (fun _ : (Point d × Point d) × (secantSpace 1 M → Point d × Ω) => (1 / (m k : ℝ)) : (Point d × Point d) × (secantSpace 1 M → Point d × Ω) → ℝ) := measurable_const
  show Measurable (fun q : (Point d × Point d) × (secantSpace 1 M → Point d × Ω) => (1 / (m k : ℝ)) • ∑ t : secantSpace 1 (m k),
      (if t.2.2 then (1 : ℝ) else (-1 : ℝ)) •
        ((1 / (2 * h)) •
          ((g (query θ q.1 + (if t.2.2 then h else -h) • (q.2 (cellInj (hmM k) t)).1)
              (q.2 (cellInj (hmM k) t)).2) • (q.2 (cellInj (hmM k) t)).1)))
  exact hc.smul hsum

/-- The joint map of one direction-sampled round is measurable. -/
lemma measurable_dirStepSched_joint {M : ℕ} (m : ℕ → ℕ) (hmM : ∀ k, m k ≤ M)
    {g : Point d → Ω → ℝ} (hg : Measurable (Function.uncurry g)) (L μ θ h : ℝ) (k : ℕ) :
    Measurable (fun q : (Point d × Point d) × (secantSpace 1 M → Point d × Ω) =>
      dirStepSched m hmM L μ θ g h k q.1 q.2) := by
  classical
  let R : (Point d × Point d) × (secantSpace 1 M → Point d × Ω) → Point d := fun q =>
      roundOf h g (query θ q.1) (m k) (fun t : secantSpace 1 (m k) => q.2 (cellInj (hmM k) t))
  have hq : Measurable (fun q : (Point d × Point d) × (secantSpace 1 M → Point d × Ω) => query θ q.1) := measurable_query.comp measurable_fst
  have hR : Measurable R := measurable_dirRound m hmM hg h θ k
  have h1 : Measurable (fun q : (Point d × Point d) × (secantSpace 1 M → Point d × Ω) => query θ q.1 - (1 / L) • R q) := by fun_prop
  have h2 : Measurable (fun q : (Point d × Point d) × (secantSpace 1 M → Point d × Ω) =>
      (1 - θ) • q.1.2 + θ • query θ q.1 - (2 * θ / μ) • R q) := by fun_prop
  exact h1.prodMk h2

/-- One direction-sampled round contracts the smoothed momentum potential and pays its own
second-moment error. -/
lemma dir_one_round {M : ℕ} {m : ℕ → ℕ} (hmM : ∀ k, m k ≤ M) (hm : ∀ k, 0 < m k)
    {g : Point d → Ω → ℝ} {fh : Point d → ℝ} {nu : ProbabilityMeasure (Point d)}
    {p : Measure Ω} [IsProbabilityMeasure p] {L μ θ h G : ℝ} {xh : Point d}
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
    (k : ℕ) (s : Point d × Point d) :
    Integrable (fun ω => potential fh μ xh (dirStepSched m hmM L μ θ g h k s ω))
        (slotLaw 1 M (probeMeasure nu p)) ∧
      (∫ ω, potential fh μ xh (dirStepSched m hmM L μ θ g h k s ω)
          ∂(slotLaw 1 M (probeMeasure nu p))) ≤
        (1 - θ / 2) * potential fh μ xh s
          + (1 / (2 * L) + θ ^ 2 / μ) * (2 * G ^ 2 / (m k : ℝ)) := by
  classical
  set W : Measure (Point d × Ω) := probeMeasure nu p with hWdef
  have hp : MeasurePreserving (fun ω : secantSpace 1 M → Point d × Ω =>
      fun t : secantSpace 1 (m k) => ω (cellInj (hmM k) t)) (slotLaw 1 M W) (slotLaw 1 (m k) W) :=
    measurePreserving_cellInj (d := 1) (hmM k)
  have hi : Integrable (fun ξ : secantSpace 1 (m k) → Point d × Ω =>
      roundOf h g (query θ s) (m k) ξ) (slotLaw 1 (m k) W) := roundOf_integrable hint (query θ s)
  have hV : Integrable (fun ω : secantSpace 1 M → Point d × Ω =>
      roundOf h g (query θ s) (m k) (fun t => ω (cellInj (hmM k) t))) (slotLaw 1 M W) :=
    hp.integrable_comp_of_integrable (ε := Point d)
      (g := fun ξ : secantSpace 1 (m k) → Point d × Ω => roundOf h g (query θ s) (m k) ξ) hi
  have hm1 : (∫ ω : secantSpace 1 M → Point d × Ω,
        roundOf h g (query θ s) (m k) (fun t => ω (cellInj (hmM k) t)) ∂(slotLaw 1 M W))
      = gradient fh (query θ s) := by
    rw [Centered.integral_comp_preserving_point (d := d)
      (φ := fun ξ : secantSpace 1 (m k) → Point d × Ω => roundOf h g (query θ s) (m k) ξ) hp hi]
    exact roundOf_mean hg hint hmean (hm k) (query θ s)
  obtain ⟨hdv1, hdv2⟩ := roundOf_dev hg hint hmean hvar2 hvar (hm k) (query θ s)
  have hxi : Integrable (fun ζ : secantSpace 1 (m k) → Point d × Ω =>
      ‖roundOf h g (query θ s) (m k) ζ - gradient fh (query θ s)‖ ^ 2) (slotLaw 1 (m k) W) := hdv1
  have hV2 : Integrable (fun ω : secantSpace 1 M → Point d × Ω =>
      ‖roundOf h g (query θ s) (m k) (fun t => ω (cellInj (hmM k) t))
        - gradient fh (query θ s)‖ ^ 2) (slotLaw 1 M W) :=
    hp.integrable_comp_of_integrable (ε := ℝ)
      (g := fun ζ : secantSpace 1 (m k) → Point d × Ω =>
        ‖roundOf h g (query θ s) (m k) ζ - gradient fh (query θ s)‖ ^ 2) hxi
  have hb2 : (∫ ω : secantSpace 1 M → Point d × Ω,
        ‖roundOf h g (query θ s) (m k) (fun t => ω (cellInj (hmM k) t))
          - gradient fh (query θ s)‖ ^ 2 ∂(slotLaw 1 M W))
      ≤ 2 * G ^ 2 / (m k : ℝ) := by
    rw [ZerothOrder.integral_comp_preserving
      (φ := fun ζ : secantSpace 1 (m k) → Point d × Ω =>
        ‖roundOf h g (query θ s) (m k) ζ - gradient fh (query θ s)‖ ^ 2) hp hxi]
    exact hdv2
  have hfh : Measurable fh :=
    (continuous_iff_continuousAt.mpr fun x => (hgr x).continuousAt).measurable
  have hj : Measurable (fun ω : secantSpace 1 M → Point d × Ω => (s, ω)) :=
    measurable_const.prodMk measurable_id
  have hmeas : AEStronglyMeasurable
      (fun ω : secantSpace 1 M → Point d × Ω =>
        potential fh μ xh (step L μ θ s
          (roundOf h g (query θ s) (m k) (fun t => ω (cellInj (hmM k) t))))) (slotLaw 1 M W) :=
    ((measurable_potentialZO (μ := μ) (xstar := xh) hfh).comp
      ((measurable_dirStepSched_joint m hmM hg L μ θ h k).comp hj)).aestronglyMeasurable
  obtain ⟨hI, hb⟩ := dir_one_step (f := fh) (L := L) (μ := μ) (θ := θ) (xstar := xh)
    hL hμ hθ0 hθ1 hθL hgr hlip hsc hminh s
    (V := fun ω : secantSpace 1 M → Point d × Ω =>
      roundOf h g (query θ s) (m k) (fun t => ω (cellInj (hmM k) t))) hV hm1 hV2 hmeas
  refine ⟨hI, ?_⟩
  have hcv : 0 ≤ 1 / (2 * L) + θ ^ 2 / μ := by positivity
  have hfin : (1 - θ / 2) * potential fh μ xh s
        + (1 / (2 * L) + θ ^ 2 / μ)
            * ∫ ω : secantSpace 1 M → Point d × Ω, ‖roundOf h g (query θ s) (m k)
                (fun t => ω (cellInj (hmM k) t)) - gradient fh (query θ s)‖ ^ 2 ∂(slotLaw 1 M W)
        ≤ (1 - θ / 2) * potential fh μ xh s + (1 / (2 * L) + θ ^ 2 / μ) * (2 * G ^ 2 / (m k : ℝ)) :=
    add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hb2 hcv)
  calc (∫ ω, potential fh μ xh (dirStepSched m hmM L μ θ g h k s ω) ∂(slotLaw 1 M W))
      = ∫ ω, potential fh μ xh (step L μ θ s
            (roundOf h g (query θ s) (m k) (fun t => ω (cellInj (hmM k) t)))) ∂(slotLaw 1 M W) :=
          integral_congr_ae (ae_of_all _ fun ω => rfl)
    _ ≤ (1 - θ / 2) * potential fh μ xh s
            + (1 / (2 * L) + θ ^ 2 / μ)
              * ∫ ω, ‖roundOf h g (query θ s) (m k) (fun t => ω (cellInj (hmM k) t))
                  - gradient fh (query θ s)‖ ^ 2 ∂(slotLaw 1 M W) := hb
    _ ≤ (1 - θ / 2) * potential fh μ xh s
            + (1 / (2 * L) + θ ^ 2 / μ) * (2 * G ^ 2 / (m k : ℝ)) := hfin

/-- Direction-sampled momentum rounds: the expected smoothed potential contracts geometrically and
each round pays its own surrogate error. -/
lemma dir_stream_potential {M : ℕ} {m : ℕ → ℕ} (hmM : ∀ k, m k ≤ M) (hm : ∀ k, 0 < m k)
    {g : Point d → Ω → ℝ} {fh : Point d → ℝ} {nu : ProbabilityMeasure (Point d)}
    {p : Measure Ω} [IsProbabilityMeasure p] {L μ θ h G : ℝ} {x0 xh : Point d} {K : ℕ}
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
        ∂(probeMeasure nu p)) ≤ G ^ 2) :
    Integrable (fun Ξ => potential fh μ xh
        (runSched (dirStepSched m hmM L μ θ g h) 0 K (x0, x0) Ξ))
        (Measure.pi fun _ : Fin K => slotLaw 1 M (probeMeasure nu p)) ∧
      (∫ Ξ, potential fh μ xh (runSched (dirStepSched m hmM L μ θ g h) 0 K (x0, x0) Ξ)
          ∂Measure.pi fun _ : Fin K => slotLaw 1 M (probeMeasure nu p)) ≤
        (1 - θ / 2) ^ K * potential fh μ xh (x0, x0)
          + ∑ k ∈ Finset.range K, (1 - θ / 2) ^ (K - 1 - k)
              * ((1 / (2 * L) + θ ^ 2 / μ) * (2 * G ^ 2 / (m k : ℝ))) := by
  classical
  have hρ : 0 ≤ 1 - θ / 2 := by linarith
  have hfh : Measurable fh :=
    (continuous_iff_continuousAt.mpr fun x => (hgr x).continuousAt).measurable
  have hc0 : ∀ k : ℕ, 0 ≤ (1 / (2 * L) + θ ^ 2 / μ) * (2 * G ^ 2 / (m k : ℝ)) := by
    intro k
    refine mul_nonneg (by positivity) (div_nonneg (by positivity) (by positivity))
  have hVnonneg : ∀ s : Point d × Point d, 0 ≤ potential fh μ xh s := by
    intro s
    show 0 ≤ fh s.1 - fh xh + μ / 4 * ‖s.2 - xh‖ ^ 2
    exact add_nonneg (sub_nonneg.mpr (hminh (Set.mem_univ s.1)))
      (mul_nonneg (by positivity) (sq_nonneg _))
  have hstep := fun (k : ℕ) (s : Point d × Point d) =>
    dir_one_round (M := M) (m := m) hmM hm (g := g) (fh := fh) (nu := nu) (p := p)
      (L := L) (μ := μ) (θ := θ) (h := h) (G := G) (xh := xh) hL hμ hθ0 hθ1 hθL hg hgr hlip hsc hminh
      hint hmean hvar2 hvar k s
  have hkey := sched_iterate_accuracy (d := 1) (M := M)
    (step := dirStepSched m hmM L μ θ g h)
    (fun k => measurable_dirStepSched_joint m hmM hg L μ θ h k)
    ⟨slotLaw 1 M (probeMeasure nu p), inferInstance⟩ (potential fh μ xh)
      (measurable_potentialZO hfh) hVnonneg hρ hc0 hstep 0 K (x0, x0)
  refine ⟨hkey.1, ?_⟩
  calc (∫ Ξ, potential fh μ xh (runSched (dirStepSched m hmM L μ θ g h) 0 K (x0, x0) Ξ)
          ∂Measure.pi fun _ : Fin K => slotLaw 1 M (probeMeasure nu p))
      ≤ (1 - θ / 2) ^ K * potential fh μ xh (x0, x0)
            + ∑ k ∈ Finset.range K, (1 - θ / 2) ^ (K - 1 - k)
                * ((1 / (2 * L) + θ ^ 2 / μ) * (2 * G ^ 2 / (m k : ℝ))) := by
          simpa [Nat.zero_add] using hkey.2

/-- Direction-sampled momentum rounds bound the expected smoothed objective gap. -/
lemma dir_stream_gap {M : ℕ} {m : ℕ → ℕ} (hmM : ∀ k, m k ≤ M) (hm : ∀ k, 0 < m k)
    {g : Point d → Ω → ℝ} {fh : Point d → ℝ} {nu : ProbabilityMeasure (Point d)}
    {p : Measure Ω} [IsProbabilityMeasure p] {L μ θ h G : ℝ} {x0 xh : Point d} {K : ℕ}
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
        ∂(probeMeasure nu p)) ≤ G ^ 2) :
    Integrable (fun Ξ => fh ((runSched (dirStepSched m hmM L μ θ g h) 0 K (x0, x0) Ξ).1) - fh xh)
        (Measure.pi fun _ : Fin K => slotLaw 1 M (probeMeasure nu p)) ∧
      (∫ Ξ, fh ((runSched (dirStepSched m hmM L μ θ g h) 0 K (x0, x0) Ξ).1) - fh xh
          ∂Measure.pi fun _ : Fin K => slotLaw 1 M (probeMeasure nu p)) ≤
        (1 - θ / 2) ^ K * (fh x0 - fh xh + μ / 4 * ‖x0 - xh‖ ^ 2)
          + ∑ k ∈ Finset.range K, (1 - θ / 2) ^ (K - 1 - k)
              * ((1 / (2 * L) + θ ^ 2 / μ) * (2 * G ^ 2 / (m k : ℝ))) := by
  classical
  obtain ⟨hI, hb⟩ := dir_stream_potential (M := M) (m := m) hmM hm (g := g) (fh := fh) (nu := nu)
    (p := p) (L := L) (μ := μ) (θ := θ) (h := h) (G := G) (x0 := x0) (xh := xh) (K := K)
    hL hμ hθ0 hθ1 hθL hg hgr hlip hsc hminh hint hmean hvar2 hvar
  have hfh : Measurable fh :=
    (continuous_iff_continuousAt.mpr fun x => (hgr x).continuousAt).measurable
  have hrun : Measurable (fun Ξ => fh ((runSched (dirStepSched m hmM L μ θ g h) 0 K (x0, x0) Ξ).1)) :=
    hfh.comp (measurable_fst.comp
      ((Scheduled.measurable_runSched (S := Point d × Point d)
          (fun k => measurable_dirStepSched_joint m hmM hg L μ θ h k) K 0).comp
          ((by fun_prop : Measurable (fun Ξ : Fin K → secantSpace 1 M → Point d × Ω =>
              ((x0, x0), Ξ))))))
  have hpoint : ∀ Ξ, fh ((runSched (dirStepSched m hmM L μ θ g h) 0 K (x0, x0) Ξ).1) - fh xh
      ≤ potential fh μ xh (runSched (dirStepSched m hmM L μ θ g h) 0 K (x0, x0) Ξ) := by
    intro Ξ
    show fh ((runSched (dirStepSched m hmM L μ θ g h) 0 K (x0, x0) Ξ).1) - fh xh
      ≤ fh (runSched (dirStepSched m hmM L μ θ g h) 0 K (x0, x0) Ξ).1
        - fh xh + μ / 4 * ‖(runSched (dirStepSched m hmM L μ θ g h) 0 K (x0, x0) Ξ).2 - xh‖ ^ 2
    exact le_add_of_nonneg_right (mul_nonneg (by positivity) (sq_nonneg _))
  have hInt : Integrable (fun Ξ => fh ((runSched (dirStepSched m hmM L μ θ g h) 0 K (x0, x0) Ξ).1)
      - fh xh) (Measure.pi fun _ : Fin K => slotLaw 1 M (probeMeasure nu p)) := by
    refine hI.mono' ((hrun.sub measurable_const).aestronglyMeasurable) (ae_of_all _ fun Ξ => ?_)
    have ha : 0 ≤ fh (runSched (dirStepSched m hmM L μ θ g h) 0 K (x0, x0) Ξ).1 - fh xh :=
      sub_nonneg.mpr (hminh (Set.mem_univ _))
    rw [Real.norm_eq_abs, abs_of_nonneg ha]
    exact hpoint Ξ
  refine ⟨hInt, ?_⟩
  calc (∫ Ξ, fh ((runSched (dirStepSched m hmM L μ θ g h) 0 K (x0, x0) Ξ).1) - fh xh
          ∂Measure.pi fun _ : Fin K => slotLaw 1 M (probeMeasure nu p))
      ≤ ∫ Ξ, potential fh μ xh (runSched (dirStepSched m hmM L μ θ g h) 0 K (x0, x0) Ξ)
          ∂Measure.pi fun _ : Fin K => slotLaw 1 M (probeMeasure nu p) :=
          integral_mono_ae hInt hI (ae_of_all _ hpoint)
    _ ≤ (1 - θ / 2) ^ K * (fh x0 - fh xh + μ / 4 * ‖x0 - xh‖ ^ 2)
            + ∑ k ∈ Finset.range K, (1 - θ / 2) ^ (K - 1 - k)
                * ((1 / (2 * L) + θ ^ 2 / μ) * (2 * G ^ 2 / (m k : ℝ))) := by
          have h1 : potential fh μ xh (x0, x0) = fh x0 - fh xh + μ / 4 * ‖x0 - xh‖ ^ 2 := rfl
          rw [← h1]
          exact hb

end OracleTemplate.SecantPolyak.DirectionSampled

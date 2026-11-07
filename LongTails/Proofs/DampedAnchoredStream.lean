import LongTails.Proofs.DampedAnchoredStep
import LongTails.Proofs.InterpolatedProbeRound
import LongTails.Proofs.DirectionMomentumStream

set_option maxHeartbeats 2000000

/-!
Stream contraction of damped anchored pair acceleration. Under the interpolation model a mirrored
pair at the interpolated point costs two probes and contracts the expected accelerated potential by
`1 - θ`, with no additive error term, so `K` rounds need `2 * K` probes and the number of rounds
needed for accuracy `ε` grows logarithmically in `1 / ε`.
-/

namespace OracleTemplate.SecantPolyak.AnchoredPair

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
open OracleTemplate InexactGradient SecantDescent SecantPolyak SecantPolyak.Accelerated
  SecantPolyak.Scheduled SecantPolyak.Centered SecantPolyak.DirectionSampled
open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {Ω : Type} [MeasurableSpace Ω] {d : ℕ}

/-- One damped anchored round as a scheduled step: the mirrored-pair surrogate of the interpolated
point drives the damped iterate step and the anchor step. -/
noncomputable def apStepSched (μ θ η : ℝ) (g : Point d → Ω → ℝ) (h : ℝ) :
    ℕ → (Point d × Point d) → (secantSpace 1 1 → Point d × Ω) → Point d × Point d :=
  fun _ s ω => apStep μ θ η s (roundOf h g (query θ s) 1 ω)

/-- With one mirrored pair per round the ambient cell map is the identity. -/
lemma apCellInj_one (hle : (1 : ℕ) ≤ 1) (t : secantSpace 1 1) : cellInj hle t = t := by
  have h1 : (cellInj hle t).1 = t.1 := Subsingleton.elim _ _
  have h2 : (cellInj hle t).2 = t.2 := rfl
  exact Prod.ext h1 h2

/-- The surrogate of one damped anchored round is measurable in the state and the round samples. -/
lemma measurable_apRound {g : Point d → Ω → ℝ} (hg : Measurable (Function.uncurry g)) (h θ : ℝ) :
    Measurable (fun q : (Point d × Point d) × (secantSpace 1 1 → Point d × Ω) =>
      roundOf h g (query θ q.1) 1 q.2) := by
  classical
  have h1 := measurable_dirRound (m := fun _ => 1) (hmM := fun _ => Nat.le_refl 1) hg h θ 0
  have h2 : (fun q : (Point d × Point d) × (secantSpace 1 1 → Point d × Ω) =>
      roundOf h g (query θ q.1) 1 (fun t => q.2 (cellInj (Nat.le_refl 1) t)))
      = (fun q : (Point d × Point d) × (secantSpace 1 1 → Point d × Ω) =>
        roundOf h g (query θ q.1) 1 q.2) := by
    refine funext fun q => congrArg (fun φ : secantSpace 1 1 → Point d × Ω =>
      roundOf h g (query θ q.1) 1 φ) ?_
    refine funext fun t => congrArg (fun u : secantSpace 1 1 => q.2 u) ?_
    exact apCellInj_one (Nat.le_refl 1) t
  rw [h2] at h1
  exact h1

/-- The joint map of one damped anchored round is measurable. -/
lemma measurable_apStepSched_joint {g : Point d → Ω → ℝ}
    (hg : Measurable (Function.uncurry g)) (μ θ η h : ℝ) (k : ℕ) :
    Measurable (fun q : (Point d × Point d) × (secantSpace 1 1 → Point d × Ω) =>
      apStepSched μ θ η g h k q.1 q.2) := by
  classical
  have hR := measurable_apRound hg h θ
  have hq : Measurable (fun q : (Point d × Point d) × (secantSpace 1 1 → Point d × Ω) =>
      query θ q.1) := measurable_query.comp measurable_fst
  have h1 : Measurable (fun q : (Point d × Point d) × (secantSpace 1 1 → Point d × Ω) =>
      query θ q.1 - η • roundOf h g (query θ q.1) 1 q.2) :=
    hq.sub ((measurable_const : Measurable (fun _ => (η : ℝ))).smul hR)
  have h2 : Measurable (fun q : (Point d × Point d) × (secantSpace 1 1 → Point d × Ω) =>
      (1 - θ) • q.1.2 + θ • query θ q.1 - (2 * θ / μ) • roundOf h g (query θ q.1) 1 q.2) := by
    fun_prop
  show Measurable (fun q : (Point d × Point d) × (secantSpace 1 1 → Point d × Ω) =>
      (query θ q.1 - η • roundOf h g (query θ q.1) 1 q.2,
        (1 - θ) • q.1.2 + θ • query θ q.1 - (2 * θ / μ) • roundOf h g (query θ q.1) 1 q.2))
  exact h1.prodMk h2

/-- One damped anchored round contracts the accelerated potential in expectation, with no additive
error: the probe deviation is bounded by the smoothed gap at the probed point. -/
lemma ap_stream_round {g : Point d → Ω → ℝ} {fh : Point d → ℝ}
    {W : Measure (Point d × Ω)} [IsProbabilityMeasure W]
    {L μ θ η h ρ : ℝ} {xh : Point d}
    (hL : 0 < L) (hμ : 0 < μ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hcap1 : θ ^ 2 / μ ≤ η - L * η ^ 2 / 2)
    (hcap3 : (L * η ^ 2 / 2 + θ ^ 2 / μ) * (2 * ρ ^ 2) ≤ μ * θ / 4 * (2 / L))
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
    (k : ℕ) (s : Point d × Point d) :
    Integrable (fun ω => potential fh μ xh (apStepSched μ θ η g h k s ω)) (slotLaw 1 1 W) ∧
      (∫ ω, potential fh μ xh (apStepSched μ θ η g h k s ω) ∂slotLaw 1 1 W)
        ≤ (1 - θ) * potential fh μ xh s := by
  classical
  have hi : Integrable (fun ω : secantSpace 1 1 → Point d × Ω =>
      roundOf h g (query θ s) 1 ω) (slotLaw 1 1 W) := roundOf_integrable hint (query θ s)
  have hm1 : (∫ ω : secantSpace 1 1 → Point d × Ω, roundOf h g (query θ s) 1 ω ∂(slotLaw 1 1 W))
      = gradient fh (query θ s) := roundOf_mean hg hint hmean Nat.one_pos (query θ s)
  obtain ⟨hdv1, hdv2⟩ :=
    Interpolated.roundOf_devAt (m := 1) (g := g) (fh := fh) (h := h) (x := query θ s) (W := W) hg hint hmean
      hvar2 (fun t => hvar (query θ s) t) Nat.one_pos
  have hfh : Measurable fh :=
    (continuous_iff_continuousAt.mpr fun x => (hgr x).continuousAt).measurable
  have hj : Measurable (fun ω : secantSpace 1 1 → Point d × Ω => (s, ω)) :=
    measurable_const.prodMk measurable_id
  have hmeas : AEStronglyMeasurable
      (fun ω : secantSpace 1 1 → Point d × Ω =>
        potential fh μ xh (apStep μ θ η s (roundOf h g (query θ s) 1 ω))) (slotLaw 1 1 W) :=
    ((measurable_potentialZO (μ := μ) (xstar := xh) hfh).comp
      ((measurable_apStepSched_joint hg μ θ η h k).comp hj)).aestronglyMeasurable
  obtain ⟨hI, hb⟩ := ap_one_round (f := fh) (L := L) (μ := μ) (θ := θ) (η := η) (ρ := ρ)
    (xh := xh) s hL hμ hθ0 hθ1 hcap1 hcap3 hgr hlip hsc hminh
    (V := fun ω : secantSpace 1 1 → Point d × Ω => roundOf h g (query θ s) 1 ω) hi hdv1 hm1
    (by
      have hb := hdv2
      simpa [Nat.cast_one, div_one, mul_assoc] using hb) hmeas
  refine ⟨hI, ?_⟩
  have hcon : (fun ω => potential fh μ xh (apStepSched μ θ η g h k s ω))
      = fun ω : secantSpace 1 1 → Point d × Ω =>
        potential fh μ xh (apStep μ θ η s (roundOf h g (query θ s) 1 ω)) := rfl
  rw [hcon]
  exact hb

/-- Damped anchored pair rounds: the expected accelerated potential contracts geometrically. -/
lemma ap_stream_potential {g : Point d → Ω → ℝ} {fh : Point d → ℝ}
    {W : Measure (Point d × Ω)} [IsProbabilityMeasure W]
    {L μ θ η h ρ : ℝ} {x0 xh : Point d} {K : ℕ}
    (hL : 0 < L) (hμ : 0 < μ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hcap1 : θ ^ 2 / μ ≤ η - L * η ^ 2 / 2)
    (hcap3 : (L * η ^ 2 / 2 + θ ^ 2 / μ) * (2 * ρ ^ 2) ≤ μ * θ / 4 * (2 / L))
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
        ≤ ρ ^ 2 * (fh x - fh xh)) :
    Integrable (fun Ξ => potential fh μ xh
        (runSched (apStepSched μ θ η g h) 0 K (x0, x0) Ξ))
        (Measure.pi fun _ : Fin K => slotLaw 1 1 W) ∧
      (∫ Ξ, potential fh μ xh (runSched (apStepSched μ θ η g h) 0 K (x0, x0) Ξ)
          ∂Measure.pi fun _ : Fin K => slotLaw 1 1 W)
        ≤ (1 - θ) ^ K * potential fh μ xh (x0, x0) := by
  classical
  have hρ : 0 ≤ 1 - θ := by linarith
  have hfh : Measurable fh :=
    (continuous_iff_continuousAt.mpr fun x => (hgr x).continuousAt).measurable
  have hc0 : ∀ k : ℕ, (0 : ℝ) ≤ 0 := fun _ => le_refl _
  have hVnonneg : ∀ s : Point d × Point d, 0 ≤ potential fh μ xh s := by
    intro s
    show 0 ≤ fh s.1 - fh xh + μ / 4 * ‖s.2 - xh‖ ^ 2
    exact add_nonneg (sub_nonneg.mpr (hminh (Set.mem_univ s.1)))
      (mul_nonneg (by positivity) (sq_nonneg _))
  have hstep : ∀ (k : ℕ) (s : Point d × Point d),
      Integrable (fun ω => potential fh μ xh (apStepSched μ θ η g h k s ω)) (slotLaw 1 1 W) ∧
        (∫ ω, potential fh μ xh (apStepSched μ θ η g h k s ω) ∂slotLaw 1 1 W)
          ≤ (1 - θ) * potential fh μ xh s + 0 := by
    intro k s
    obtain ⟨a, b⟩ := ap_stream_round (g := g) (fh := fh) (W := W) (L := L) (μ := μ) (θ := θ)
      (η := η) (h := h) (ρ := ρ) (xh := xh) hL hμ hθ0 hθ1 hcap1 hcap3 hg hgr hlip hsc hminh hint
      hmean hvar2 hvar k s
    exact ⟨a, by simpa using b⟩
  obtain ⟨hI, hb⟩ := sched_iterate_accuracy (d := 1) (M := 1)
    (step := apStepSched μ θ η g h)
    (fun k => measurable_apStepSched_joint hg μ θ η h k)
    ⟨slotLaw 1 1 W, inferInstance⟩ (potential fh μ xh) (measurable_potentialZO hfh) hVnonneg hρ
      hc0 hstep 0 K (x0, x0)
  refine ⟨hI, ?_⟩
  have hsum : (∑ k ∈ Finset.range K, (1 - θ) ^ (K - 1 - k) * (0 : ℝ)) = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    ring
  calc (∫ Ξ, potential fh μ xh (runSched (apStepSched μ θ η g h) 0 K (x0, x0) Ξ)
          ∂Measure.pi fun _ : Fin K => slotLaw 1 1 W)
      ≤ (1 - θ) ^ K * potential fh μ xh (x0, x0)
            + ∑ k ∈ Finset.range K, (1 - θ) ^ (K - 1 - k) * (0 : ℝ) := by
          simpa [Nat.zero_add] using hb
    _ = (1 - θ) ^ K * potential fh μ xh (x0, x0) := by rw [hsum, add_zero]

/-- Damped anchored pair rounds bound the expected smoothed objective gap of the iterate. -/
lemma ap_stream_gap {g : Point d → Ω → ℝ} {fh : Point d → ℝ}
    {W : Measure (Point d × Ω)} [IsProbabilityMeasure W]
    {L μ θ η h ρ : ℝ} {x0 xh : Point d} {K : ℕ}
    (hL : 0 < L) (hμ : 0 < μ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hcap1 : θ ^ 2 / μ ≤ η - L * η ^ 2 / 2)
    (hcap3 : (L * η ^ 2 / 2 + θ ^ 2 / μ) * (2 * ρ ^ 2) ≤ μ * θ / 4 * (2 / L))
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
        ≤ ρ ^ 2 * (fh x - fh xh)) :
    Integrable (fun Ξ => fh (runSched (apStepSched μ θ η g h) 0 K (x0, x0) Ξ).1 - fh xh)
        (Measure.pi fun _ : Fin K => slotLaw 1 1 W) ∧
      (∫ Ξ, fh (runSched (apStepSched μ θ η g h) 0 K (x0, x0) Ξ).1 - fh xh
          ∂Measure.pi fun _ : Fin K => slotLaw 1 1 W)
        ≤ (1 - θ) ^ K * potential fh μ xh (x0, x0) := by
  classical
  obtain ⟨hI, hb⟩ := ap_stream_potential (g := g) (fh := fh) (W := W) (L := L) (μ := μ)
    (θ := θ) (η := η) (h := h) (ρ := ρ) (x0 := x0) (xh := xh) (K := K) hL hμ hθ0 hθ1 hcap1 hcap3
    hg hgr hlip hsc hminh hint hmean hvar2 hvar
  set Ψ : (Fin K → secantSpace 1 1 → Point d × Ω) → ℝ := fun Xi =>
    potential fh μ xh (runSched (apStepSched μ θ η g h) 0 K (x0, x0) Xi) with hΨdef
  have hV : Measurable (fun Xi => fh (runSched (apStepSched μ θ η g h) 0 K (x0, x0) Xi).1 - fh xh) := by
    have hfh : Measurable fh :=
      (continuous_iff_continuousAt.mpr fun x => (hgr x).continuousAt).measurable
    have hrm := measurable_runSched (step := apStepSched μ θ η g h)
      (fun k => measurable_apStepSched_joint hg μ θ η h k) K 0
    exact ((hfh.comp measurable_fst).comp
      (hrm.comp (measurable_const.prodMk measurable_id))).sub measurable_const
  have hnonneg : ∀ Xi, 0 ≤ fh (runSched (apStepSched μ θ η g h) 0 K (x0, x0) Xi).1 - fh xh := by
    intro Xi
    exact sub_nonneg.mpr (hminh (Set.mem_univ _))
  have hle : ∀ Xi, fh (runSched (apStepSched μ θ η g h) 0 K (x0, x0) Xi).1 - fh xh ≤ Ψ Xi := by
    intro Xi
    show fh (runSched (apStepSched μ θ η g h) 0 K (x0, x0) Xi).1 - fh xh
      ≤ fh (runSched (apStepSched μ θ η g h) 0 K (x0, x0) Xi).1 - fh xh
        + μ / 4 * ‖(runSched (apStepSched μ θ η g h) 0 K (x0, x0) Xi).2 - xh‖ ^ 2
    exact le_add_of_nonneg_right (by positivity)
  have hInt : Integrable (fun Xi => fh (runSched (apStepSched μ θ η g h) 0 K (x0, x0) Xi).1 - fh xh)
      (Measure.pi fun _ : Fin K => slotLaw 1 1 W) :=
    hI.mono' hV.aestronglyMeasurable (ae_of_all _ fun Xi => by
      have h0 := hnonneg Xi
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact hle Xi)
  refine ⟨hInt, ?_⟩
  calc (∫ Xi, fh (runSched (apStepSched μ θ η g h) 0 K (x0, x0) Xi).1 - fh xh
          ∂Measure.pi fun _ : Fin K => slotLaw 1 1 W)
      ≤ ∫ Xi, Ψ Xi ∂Measure.pi fun _ : Fin K => slotLaw 1 1 W :=
          integral_mono_ae hInt hI (ae_of_all _ hle)
    _ = ∫ Xi, potential fh μ xh (runSched (apStepSched μ θ η g h) 0 K (x0, x0) Xi)
          ∂Measure.pi fun _ : Fin K => slotLaw 1 1 W := by
          refine integral_congr_ae (ae_of_all _ fun _ => rfl)
    _ ≤ (1 - θ) ^ K * potential fh μ xh (x0, x0) := hb

end OracleTemplate.SecantPolyak.AnchoredPair

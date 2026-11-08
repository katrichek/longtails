import LongTails.Proofs.GradedAnchoredStep
import LongTails.Proofs.InterpolatedProbeRound
import LongTails.Proofs.DirectionMomentumStream

set_option maxHeartbeats 2000000

/-!
Stream contraction of weighted anchored pair acceleration. A round asks `2 * m` one-sided probes at
the interpolated point along `m` independent directions, so the mean-square deviation of the round
surrogate is `2 * ρ² / m` times the smoothed gap there. Choosing `m` to satisfy
`(L * η² / 2 + θ² / (4 * β)) * (2 * ρ² / m) ≤ θ * (μ / 2 - β) * (2 / L)` makes the expected weighted
potential contract by `1 - θ` with no additive error, and `K` rounds then cost `2 * m * K` probes.
-/

namespace OracleTemplate.SecantPolyak.GradedAnchored

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
open OracleTemplate InexactGradient SecantDescent SecantPolyak SecantPolyak.Accelerated
  SecantPolyak.Scheduled SecantPolyak.Centered SecantPolyak.DirectionSampled
open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {Ω : Type} [MeasurableSpace Ω] {d : ℕ}

/-- One weighted anchored round as a scheduled step: the batched mirrored surrogate of the
interpolated point drives the damped iterate step and the anchor step. -/
noncomputable def waStepSched (β θ η : ℝ) (g : Point d → Ω → ℝ) (h : ℝ) (m : ℕ) :
    ℕ → (Point d × Point d) → (secantSpace 1 m → Point d × Ω) → Point d × Point d :=
  fun _ s ω => waStep β θ η s (roundOf h g (query θ s) m ω)

/-- With the ambient cell count equal to the round cell count the cell map is the identity. -/
lemma waCellInj_refl {m : ℕ} (t : secantSpace 1 m) : cellInj (Nat.le_refl m) t = t := by
  have h1 : (cellInj (Nat.le_refl m) t).1 = t.1 := Fin.eq_of_val_eq rfl
  have h2 : (cellInj (Nat.le_refl m) t).2 = t.2 := rfl
  exact Prod.ext h1 h2

/-- Any reflexive cell bound acts as the identity on cells. -/
lemma cellInj_refl_any {m : ℕ} (h : m ≤ m) (t : secantSpace 1 m) : cellInj h t = t := by
  have h2 : h = Nat.le_refl m := Subsingleton.elim h _
  rw [h2, waCellInj_refl t]

/-- The batched surrogate of one round is measurable in the state and the round samples. -/
lemma measurable_waRound {g : Point d → Ω → ℝ}
    (hg : Measurable (Function.uncurry g)) (h θ : ℝ) (m : ℕ) :
    Measurable (fun q : (Point d × Point d) × (secantSpace 1 m → Point d × Ω) =>
      roundOf h g (query θ q.1) m q.2) := by
  classical
  have h1 := measurable_dirRound (M := m) (m := fun _ => m) (hmM := fun _ => Nat.le_refl m) hg h θ 0
  have h2 : (fun q : (Point d × Point d) × (secantSpace 1 m → Point d × Ω) =>
      roundOf h g (query θ q.1) m (fun t : secantSpace 1 m => q.2 (cellInj (Nat.le_refl m) t)))
      = (fun q : (Point d × Point d) × (secantSpace 1 m → Point d × Ω) =>
        roundOf h g (query θ q.1) m q.2) := by
    refine funext fun q => congrArg (fun φ : secantSpace 1 m → Point d × Ω =>
      roundOf h g (query θ q.1) m φ) ?_
    refine funext fun t => congrArg (fun u : secantSpace 1 m => q.2 u) ?_
    exact waCellInj_refl t
  rw [h2] at h1
  exact h1

/-- The joint map of one weighted anchored round is measurable. -/
lemma measurable_waStepSched_joint {g : Point d → Ω → ℝ}
    (hg : Measurable (Function.uncurry g)) (β θ η h : ℝ) (m : ℕ) (k : ℕ) :
    Measurable (fun q : (Point d × Point d) × (secantSpace 1 m → Point d × Ω) =>
      waStepSched β θ η g h m k q.1 q.2) := by
  classical
  have hR := measurable_waRound hg h θ m
  have hq : Measurable (fun q : (Point d × Point d) × (secantSpace 1 m → Point d × Ω) =>
      query θ q.1) := measurable_query.comp measurable_fst
  show Measurable (fun q : (Point d × Point d) × (secantSpace 1 m → Point d × Ω) =>
      (query θ q.1 - η • roundOf h g (query θ q.1) m q.2,
        (1 - θ) • q.1.2 + θ • query θ q.1 - (θ / (2 * β)) •
          roundOf h g (query θ q.1) m q.2))
  fun_prop

/-- Measurability of the weighted anchored potential. -/
lemma measurable_waPotential {f : Point d → ℝ} (hf : Measurable f) (β : ℝ) (xh : Point d) :
    Measurable (fun s : Point d × Point d => waPotential f β xh s) := by
  show Measurable (fun s : Point d × Point d => f s.1 - f xh + β * ‖s.2 - xh‖ ^ 2)
  fun_prop

/-- One weighted anchored round contracts the weighted potential in expectation, with no additive
error: the probe deviation is bounded by the smoothed gap at the probed point. -/
lemma wa_stream_round {g : Point d → Ω → ℝ} {fh : Point d → ℝ}
    {W : Measure (Point d × Ω)} [IsProbabilityMeasure W]
    {L μ β θ η h ρ : ℝ} {xh : Point d} (m : ℕ) (hm : 0 < m)
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
    (k : ℕ) (s : Point d × Point d) :
    Integrable (fun ω => waPotential fh β xh (waStepSched β θ η g h m k s ω))
        (slotLaw 1 m W) ∧
      (∫ ω, waPotential fh β xh (waStepSched β θ η g h m k s ω) ∂slotLaw 1 m W)
        ≤ (1 - θ) * waPotential fh β xh s := by
  classical
  have hi : Integrable (fun ω : secantSpace 1 m → Point d × Ω =>
      roundOf h g (query θ s) m ω) (slotLaw 1 m W) := roundOf_integrable hint (query θ s)
  have hm1 : (∫ ω : secantSpace 1 m → Point d × Ω, roundOf h g (query θ s) m ω ∂(slotLaw 1 m W))
      = gradient fh (query θ s) := roundOf_mean hg hint hmean hm (query θ s)
  obtain ⟨hdv1, hdv2⟩ :=
    Interpolated.roundOf_devAt (m := m) (g := g) (fh := fh) (h := h) (x := query θ s) (W := W)
      hg hint hmean hvar2 (fun t => hvar (query θ s) t) hm
  have hfh : Measurable fh :=
    (continuous_iff_continuousAt.mpr fun x => (hgr x).continuousAt).measurable
  have hj : Measurable (fun ω : secantSpace 1 m → Point d × Ω => (s, ω)) :=
    measurable_const.prodMk measurable_id
  have hmeas : AEStronglyMeasurable
      (fun ω : secantSpace 1 m → Point d × Ω =>
        waPotential fh β xh (waStep β θ η s (roundOf h g (query θ s) m ω))) (slotLaw 1 m W) :=
    ((measurable_waPotential hfh β xh).comp
      ((measurable_waStepSched_joint hg β θ η h m k).comp hj)).aestronglyMeasurable
  have hvb : (∫ ω : secantSpace 1 m → Point d × Ω,
        ‖roundOf h g (query θ s) m ω - gradient fh (query θ s)‖ ^ 2 ∂(slotLaw 1 m W))
      ≤ (2 * ρ ^ 2 / (m : ℝ)) * (fh (query θ s) - fh xh) := by
    have hm0 : (m : ℝ) ≠ 0 := by positivity
    have h1 : 2 * (ρ ^ 2 * (fh (query θ s) - fh xh)) / (m : ℝ)
        = (2 * ρ ^ 2 / (m : ℝ)) * (fh (query θ s) - fh xh) := by
      field_simp [hm0]
    exact hdv2.trans h1.le
  obtain ⟨hI, hb⟩ := wa_one_round (f := fh) (L := L) (μ := μ) (β := β) (θ := θ) (η := η)
    (v := 2 * ρ ^ 2 / (m : ℝ)) (xh := xh) s hL hμ hβ hβh hθ0 hθ1 hcap1 hcap3 hgr hlip hsc hminh
    (V := fun ω : secantSpace 1 m → Point d × Ω => roundOf h g (query θ s) m ω) hi hdv1 hm1 hvb
    hmeas
  refine ⟨hI, ?_⟩
  have hcon : (fun ω => waPotential fh β xh (waStepSched β θ η g h m k s ω))
      = fun ω : secantSpace 1 m → Point d × Ω =>
        waPotential fh β xh (waStep β θ η s (roundOf h g (query θ s) m ω)) := rfl
  rw [hcon]
  exact hb

/-- Weighted anchored pair rounds: the expected weighted potential contracts geometrically. -/
lemma wa_stream_potential {g : Point d → Ω → ℝ} {fh : Point d → ℝ}
    {W : Measure (Point d × Ω)} [IsProbabilityMeasure W]
    {L μ β θ η h ρ : ℝ} {x0 xh : Point d} {K : ℕ}
    (m : ℕ) (hm : 0 < m)
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
        ≤ ρ ^ 2 * (fh x - fh xh)) :
    Integrable (fun Ξ => waPotential fh β xh
        (runSched (waStepSched β θ η g h m) 0 K (x0, x0) Ξ))
        (Measure.pi fun _ : Fin K => slotLaw 1 m W) ∧
      (∫ Ξ, waPotential fh β xh (runSched (waStepSched β θ η g h m) 0 K (x0, x0) Ξ)
          ∂Measure.pi fun _ : Fin K => slotLaw 1 m W)
        ≤ (1 - θ) ^ K * waPotential fh β xh (x0, x0) := by
  classical
  have hρ : 0 ≤ 1 - θ := by linarith
  have hfh : Measurable fh :=
    (continuous_iff_continuousAt.mpr fun x => (hgr x).continuousAt).measurable
  have hc0 : ∀ k : ℕ, (0 : ℝ) ≤ 0 := fun _ => le_refl _
  have hVnonneg : ∀ s : Point d × Point d, 0 ≤ waPotential fh β xh s := by
    intro s
    show 0 ≤ fh s.1 - fh xh + β * ‖s.2 - xh‖ ^ 2
    exact add_nonneg (sub_nonneg.mpr (hminh (Set.mem_univ s.1)))
      (mul_nonneg hβ.le (sq_nonneg _))
  have hstep : ∀ (k : ℕ) (s : Point d × Point d),
      Integrable (fun ω => waPotential fh β xh (waStepSched β θ η g h m k s ω)) (slotLaw 1 m W) ∧
        (∫ ω, waPotential fh β xh (waStepSched β θ η g h m k s ω) ∂slotLaw 1 m W)
          ≤ (1 - θ) * waPotential fh β xh s + 0 := by
    intro k s
    obtain ⟨a, b⟩ := wa_stream_round (g := g) (fh := fh) (W := W) (L := L) (μ := μ) (β := β)
      (θ := θ) (η := η) (h := h) (ρ := ρ) (xh := xh) m hm hL hμ hβ hβh hθ0 hθ1 hcap1 hcap3 hg hgr
      hlip hsc hminh hint hmean hvar2 hvar k s
    exact ⟨a, by simpa using b⟩
  obtain ⟨hI, hb⟩ := sched_iterate_accuracy (d := 1) (M := m)
    (step := waStepSched β θ η g h m)
    (fun k => measurable_waStepSched_joint hg β θ η h m k)
    ⟨slotLaw 1 m W, inferInstance⟩ (waPotential fh β xh) (measurable_waPotential hfh β xh)
      hVnonneg hρ hc0 hstep 0 K (x0, x0)
  refine ⟨hI, ?_⟩
  have hsum : (∑ k ∈ Finset.range K, (1 - θ) ^ (K - 1 - k) * (0 : ℝ)) = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    ring
  calc (∫ Ξ, waPotential fh β xh (runSched (waStepSched β θ η g h m) 0 K (x0, x0) Ξ)
          ∂Measure.pi fun _ : Fin K => slotLaw 1 m W)
      ≤ (1 - θ) ^ K * waPotential fh β xh (x0, x0)
            + ∑ k ∈ Finset.range K, (1 - θ) ^ (K - 1 - k) * (0 : ℝ) := by
          simpa [Nat.zero_add] using hb
    _ = (1 - θ) ^ K * waPotential fh β xh (x0, x0) := by rw [hsum, add_zero]

/-- Weighted anchored pair rounds bound the expected smoothed objective gap of the iterate. -/
lemma wa_stream_gap {g : Point d → Ω → ℝ} {fh : Point d → ℝ}
    {W : Measure (Point d × Ω)} [IsProbabilityMeasure W]
    {L μ β θ η h ρ : ℝ} {x0 xh : Point d} {K : ℕ}
    (m : ℕ) (hm : 0 < m)
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
        ≤ ρ ^ 2 * (fh x - fh xh)) :
    Integrable (fun Ξ => fh (runSched (waStepSched β θ η g h m) 0 K (x0, x0) Ξ).1 - fh xh)
        (Measure.pi fun _ : Fin K => slotLaw 1 m W) ∧
      (∫ Ξ, fh (runSched (waStepSched β θ η g h m) 0 K (x0, x0) Ξ).1 - fh xh
          ∂Measure.pi fun _ : Fin K => slotLaw 1 m W)
        ≤ (1 - θ) ^ K * waPotential fh β xh (x0, x0) := by
  classical
  obtain ⟨hI, hb⟩ := wa_stream_potential (g := g) (fh := fh) (W := W) (L := L) (μ := μ) (β := β)
    (θ := θ) (η := η) (h := h) (ρ := ρ) (x0 := x0) (xh := xh) (K := K) m hm hL hμ hβ hβh hθ0 hθ1
    hcap1 hcap3 hg hgr hlip hsc hminh hint hmean hvar2 hvar
  set Ψ : (Fin K → secantSpace 1 m → Point d × Ω) → ℝ := fun Xi =>
    waPotential fh β xh (runSched (waStepSched β θ η g h m) 0 K (x0, x0) Xi) with hΨdef
  have hfh : Measurable fh :=
    (continuous_iff_continuousAt.mpr fun x => (hgr x).continuousAt).measurable
  have hV : Measurable (fun Xi =>
      fh (runSched (waStepSched β θ η g h m) 0 K (x0, x0) Xi).1 - fh xh) := by
    have hrm := measurable_runSched (step := waStepSched β θ η g h m)
      (fun k => measurable_waStepSched_joint hg β θ η h m k) K 0
    exact ((hfh.comp measurable_fst).comp
      (hrm.comp (measurable_const.prodMk measurable_id))).sub measurable_const
  have hnonneg : ∀ Xi, 0 ≤ fh (runSched (waStepSched β θ η g h m) 0 K (x0, x0) Xi).1 - fh xh := by
    intro Xi
    exact sub_nonneg.mpr (hminh (Set.mem_univ _))
  have hle : ∀ Xi, fh (runSched (waStepSched β θ η g h m) 0 K (x0, x0) Xi).1 - fh xh ≤ Ψ Xi := by
    intro Xi
    show fh (runSched (waStepSched β θ η g h m) 0 K (x0, x0) Xi).1 - fh xh
      ≤ fh (runSched (waStepSched β θ η g h m) 0 K (x0, x0) Xi).1 - fh xh
        + β * ‖(runSched (waStepSched β θ η g h m) 0 K (x0, x0) Xi).2 - xh‖ ^ 2
    exact le_add_of_nonneg_right (by positivity)
  have hInt : Integrable
      (fun Xi => fh (runSched (waStepSched β θ η g h m) 0 K (x0, x0) Xi).1 - fh xh)
        (Measure.pi fun _ : Fin K => slotLaw 1 m W) :=
    hI.mono' hV.aestronglyMeasurable (ae_of_all _ fun Xi => by
      have h0 := hnonneg Xi
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact hle Xi)
  refine ⟨hInt, ?_⟩
  calc (∫ Xi, fh (runSched (waStepSched β θ η g h m) 0 K (x0, x0) Xi).1 - fh xh
          ∂Measure.pi fun _ : Fin K => slotLaw 1 m W)
      ≤ ∫ Xi, Ψ Xi ∂Measure.pi fun _ : Fin K => slotLaw 1 m W :=
          integral_mono_ae hInt hI (ae_of_all _ hle)
    _ = ∫ Xi, waPotential fh β xh (runSched (waStepSched β θ η g h m) 0 K (x0, x0) Xi)
          ∂Measure.pi fun _ : Fin K => slotLaw 1 m W := by
          refine integral_congr_ae (ae_of_all _ fun _ => rfl)
    _ ≤ (1 - θ) ^ K * waPotential fh β xh (x0, x0) := hb

end OracleTemplate.SecantPolyak.GradedAnchored

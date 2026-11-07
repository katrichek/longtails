import LongTails.Proofs.InterpolatedProbeRound
import LongTails.Proofs.SecantPolyakScheduledStream

set_option maxHeartbeats 2000000

/-!
Stream contraction of mirrored-pair descent. Under strong growth one mirrored pair per step already
contracts the expected smoothed gap by a constant factor, so the number of rounds needed to reach
accuracy `ε` grows only logarithmically in `1 / ε`, unlike the `1 / ε` budget of a fixed noise level.
-/

namespace OracleTemplate.SecantPolyak.Interpolated

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
open OracleTemplate _root_.OracleTemplate.Gradient SecantDescent SecantPolyak
  SecantPolyak.Scheduled SecantPolyak.Centered SecantPolyak.DirectionSampled
open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {Ω : Type} [MeasurableSpace Ω] {d : ℕ}

/-- One mirrored-pair descent step written as a scheduled step function. -/
noncomputable def ipStepSched (g : Point d → Ω → ℝ) (η h : ℝ) :
    ℕ → Point d → (secantSpace 1 1 → Point d × Ω) → Point d :=
  fun _ x Ξ => x - η • roundOf h g x 1 Ξ

/-- The round surrogate is a measurable function of the iterate and of the round samples. -/
lemma measurable_ipRound {g : Point d → Ω → ℝ}
    (hg : Measurable (Function.uncurry g)) (h : ℝ) :
    Measurable (fun q : Point d × (secantSpace 1 1 → Point d × Ω) => roundOf h g q.1 1 q.2) := by
  classical
  have hx : Measurable (fun q : Point d × (secantSpace 1 1 → Point d × Ω) => q.1) := measurable_fst
  have h2 (t : secantSpace 1 1) :
      Measurable (fun q : Point d × (secantSpace 1 1 → Point d × Ω) => (q.2 t).2) :=
    measurable_snd.comp ((measurable_pi_apply t).comp measurable_snd)
  have hs (t : secantSpace 1 1) : Measurable (fun q : Point d × (secantSpace 1 1 → Point d × Ω) =>
      g (q.1 + (if t.2.2 then h else -h) • (q.2 t).1) (q.2 t).2) := by
    have hsa : Measurable (fun q : Point d × (secantSpace 1 1 → Point d × Ω) =>
        (if t.2.2 then h else (-h)) • (q.2 t).1) := by fun_prop
    exact hg.comp ((hx.add hsa).prodMk (h2 t))
  have ht (t : secantSpace 1 1) : Measurable (fun q : Point d × (secantSpace 1 1 → Point d × Ω) =>
      (if t.2.2 then (1 : ℝ) else (-1 : ℝ)) •
        ((1 / (2 * h)) •
          (g (q.1 + (if t.2.2 then h else -h) • (q.2 t).1) (q.2 t).2 • (q.2 t).1))) := by
    fun_prop
  have hsum : Measurable (fun q : Point d × (secantSpace 1 1 → Point d × Ω) =>
      ∑ t : secantSpace 1 1, (if t.2.2 then (1 : ℝ) else (-1 : ℝ)) •
        ((1 / (2 * h)) •
          (g (q.1 + (if t.2.2 then h else -h) • (q.2 t).1) (q.2 t).2 • (q.2 t).1))) :=
    Finset.measurable_sum Finset.univ fun t _ => ht t
  have hfun : (fun q : Point d × (secantSpace 1 1 → Point d × Ω) => roundOf h g q.1 1 q.2)
      = fun q => ∑ t : secantSpace 1 1, (if t.2.2 then (1 : ℝ) else (-1 : ℝ)) •
          ((1 / (2 * h)) •
            (g (q.1 + (if t.2.2 then h else -h) • (q.2 t).1) (q.2 t).2 • (q.2 t).1)) := by
    funext q
    simp only [roundOf, slotVal, Nat.cast_one, div_one, one_smul]
  rw [hfun]
  exact hsum

/-- The joint map of one mirrored-pair round is measurable. -/
lemma measurable_ipStepSched_joint {g : Point d → Ω → ℝ} (hg : Measurable (Function.uncurry g))
    (η h : ℝ) (k : ℕ) :
    Measurable (fun q : Point d × (secantSpace 1 1 → Point d × Ω) =>
      ipStepSched g η h k q.1 q.2) := by
  classical
  show Measurable (fun q : Point d × (secantSpace 1 1 → Point d × Ω) =>
      q.1 - η • roundOf h g q.1 1 q.2)
  have hconst : Measurable (fun _ : Point d × (secantSpace 1 1 → Point d × Ω) => (η : ℝ)) :=
    measurable_const
  refine Measurable.sub measurable_fst ?_
  exact hconst.smul (measurable_ipRound hg h)

/-- Mirrored-pair descent contracts the expected smoothed gap geometrically under strong growth. -/
lemma ip_stream_gap {g : Point d → Ω → ℝ} {fh : Point d → ℝ}
    {W : Measure (Point d × Ω)} [IsProbabilityMeasure W]
    {L μ η h ρ : ℝ} {x0 xh : Point d} {K : ℕ}
    (hL : 0 < L) (hμ : 0 < μ) (hη0 : 0 ≤ η) (hηL : L * η ≤ 1) (hημ : η * μ ≤ 1)
    (hηr : L * η * ρ ^ 2 ≤ μ / 2)
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
    Integrable (fun Ξ => fh (runSched (ipStepSched g η h) 0 K x0 Ξ) - fh xh)
        (Measure.pi fun _ : Fin K => slotLaw 1 1 W) ∧
      (∫ Ξ, fh (runSched (ipStepSched g η h) 0 K x0 Ξ) - fh xh
          ∂Measure.pi fun _ : Fin K => slotLaw 1 1 W)
        ≤ (1 - η * μ / 2) ^ K * (fh x0 - fh xh) := by
  classical
  have hρ : 0 ≤ 1 - η * μ / 2 := by linarith
  have hfh : Measurable fh :=
    (continuous_iff_continuousAt.mpr fun x => (hgr x).continuousAt).measurable
  set V : Point d → ℝ := fun x => fh x - fh xh with hVdef
  have hV : Measurable V := hfh.sub measurable_const
  have hV0 : ∀ x, 0 ≤ V x := fun x => sub_nonneg.mpr (hminh (Set.mem_univ x))
  have hc0 : ∀ k : ℕ, (0 : ℝ) ≤ 0 := fun _ => le_refl _
  have hbound : ∀ k s, Integrable (fun a => V (ipStepSched g η h k s a))
      (slotLaw 1 1 (W : Measure (Point d × Ω))) ∧
      (∫ a, V (ipStepSched g η h k s a) ∂(slotLaw 1 1 (W : Measure (Point d × Ω))))
        ≤ (1 - η * μ / 2) * V s + 0 := by
    intro k s
    obtain ⟨hi, hb⟩ := ip_one_round (g := g) (fh := fh) (W := W) (L := L) (μ := μ) (η := η)
      (h := h) (ρ := ρ) (xh := xh) (x := s) hL hμ hη0 hηL hηr hgr hlip hsc hminh hg hint hmean
      hvar2 (fun t => hvar s t)
    have heq : (fun a => V (ipStepSched g η h k s a)) =
        fun a => fh (s - η • roundOf h g s 1 a) - fh xh := by
      funext a
      show V (s - η • roundOf h g s 1 a) = fh (s - η • roundOf h g s 1 a) - fh xh
      rfl
    have hI2 : Integrable (fun a => V (ipStepSched g η h k s a)) (slotLaw 1 1 W) := by
      rw [heq]
      exact hi
    have h2 : (1 - η * μ / 2) * (fh s - fh xh) = (1 - η * μ / 2) * V s + 0 := by
      simp [hVdef]
    refine ⟨hI2, ?_⟩
    have h3 : (∫ a, V (ipStepSched g η h k s a) ∂slotLaw 1 1 W)
        = ∫ a, fh (s - η • roundOf h g s 1 a) - fh xh ∂slotLaw 1 1 W := by rw [heq]
    have h5 : (∫ a, V (ipStepSched g η h k s a) ∂slotLaw 1 1 W)
        ≤ (1 - η * μ / 2) * (fh s - fh xh) := by
      rw [h3]
      exact hb
    exact h5.trans (le_of_eq h2)
  obtain ⟨hI, hb⟩ := sched_iterate_accuracy (d := 1) (M := 1) (step := ipStepSched g η h)
    (fun k => measurable_ipStepSched_joint hg η h k)
    ⟨slotLaw 1 1 W, inferInstance⟩ V hV hV0 hρ hc0 hbound 0 K x0
  refine ⟨hI, ?_⟩
  have hsum : (∑ k ∈ Finset.range K, (1 - η * μ / 2) ^ (K - 1 - k) * (0 : ℝ)) = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    ring
  have hVx : V x0 = fh x0 - fh xh := rfl
  calc (∫ Ξ, fh (runSched (ipStepSched g η h) 0 K x0 Ξ) - fh xh
          ∂Measure.pi fun _ : Fin K => slotLaw 1 1 W)
      = ∫ Ξ, V (runSched (ipStepSched g η h) 0 K x0 Ξ)
          ∂Measure.pi fun _ : Fin K => slotLaw 1 1 W := by
        refine integral_congr_ae (ae_of_all _ fun Ξ => ?_)
        show fh (runSched (ipStepSched g η h) 0 K x0 Ξ) - fh xh = V (runSched (ipStepSched g η h) 0 K x0 Ξ)
        rfl
    _ ≤ (1 - η * μ / 2) ^ K * V x0 +
            ∑ k ∈ Finset.range K, (1 - η * μ / 2) ^ (K - 1 - k) * (0 : ℝ) := hb
    _ ≤ (1 - η * μ / 2) ^ K * (fh x0 - fh xh) := by
        rw [hsum, add_zero, hVx]

end OracleTemplate.SecantPolyak.Interpolated

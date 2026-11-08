import LongTails.Proofs.GrowthProbeStream

set_option maxHeartbeats 4000000

/-!
Accuracy of averaged probe descent: the supermartingale potential bounds the accumulated smoothed
gaps, so the average of the visited points reaches the surrogate minimum with expected gap at most
the squared initial distance divided by the step size times the number of rounds.
-/

namespace OracleTemplate.SecantPolyak.GrowthConvex

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
open OracleTemplate _root_.OracleTemplate.Gradient SecantDescent SecantPolyak
  SecantPolyak.Scheduled SecantPolyak.Centered SecantPolyak.DirectionSampled
open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {Ω : Type} [MeasurableSpace Ω] {d : ℕ} {g : Point d → Ω → ℝ} {fh : Point d → ℝ}
  {xh : Point d} {W : Measure (Point d × Ω)} {L ρ η h : ℝ}

/-- Product law of `K` rounds of mirrored probe pairs. -/
noncomputable abbrev gpLaw (W : Measure (Point d × Ω)) (K : ℕ) :
    Measure (Fin K → secantSpace 1 1 → Point d × Ω) :=
  Measure.pi fun _ : Fin K => slotLaw 1 1 W

/-- The expected smoothed gap of the averaged output decays like the squared initial distance over
the step size times the number of rounds. -/
lemma gp_stream_accuracy [IsProbabilityMeasure W] (M : GPHyp g fh xh L ρ η h W) {K : ℕ}
    (hK : 0 < K) (hηp : 0 < η) (x0 : Point d) :
    Integrable (μ := gpLaw W K) (fun Ξ =>
        fh ((1 / (K : ℝ)) • (runSched (gpStep g fh xh η h) 0 K (x0, (0 : Point d), (0 : ℝ)) Ξ).2.1)
          - fh xh) ∧
      ∫ Ξ, fh ((1 / (K : ℝ)) • (runSched (gpStep g fh xh η h) 0 K (x0, 0, 0) Ξ).2.1) - fh xh
        ∂(gpLaw W K) ≤ ‖x0 - xh‖ ^ 2 / (η * (K : ℝ)) := by
  have hk : (0 : ℝ) < K := by positivity
  have hk1 : (1 : ℝ) ≤ (K : ℝ) := mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hK))
  have hstep : ∀ k : ℕ, Measurable
      (fun q : GPState d × (secantSpace 1 1 → Point d × Ω) =>
        gpStep (g := g) (fh := fh) (xh := xh) (η := η) (h := h) k q.1 q.2) :=
    fun k => measurable_gpStep (hg := M.gmeas) (hfm := M.fmeas) xh η h k
  have hrun : Measurable fun Ξ : Fin K → secantSpace 1 1 → Point d × Ω =>
      runSched (gpStep g fh xh η h) 0 K (x0, (0 : Point d), (0 : ℝ)) Ξ :=
    (measurable_runSched hstep K 0).comp (measurable_const.prodMk measurable_id)
  obtain ⟨hInt, hle⟩ := gp_supermart (M := M) (K := K) (i := 0) (x0, (0 : Point d), (0 : ℝ)) le_rfl
  have hpot : gpPot xh η (x0, (0 : Point d), (0 : ℝ)) = ‖x0 - xh‖ ^ 2 := by simp [gpPot]
  rw [hpot] at hle
  have hmeas : Measurable fun Ξ =>
      fh ((1 / (K : ℝ)) • (runSched (gpStep g fh xh η h) 0 K (x0, (0 : Point d), (0 : ℝ)) Ξ).2.1) - fh xh :=
    Measurable.sub (M.fmeas.comp (Measurable.const_smul hrun.snd.fst (1 / (K : ℝ)))) measurable_const
  have hnonneg : ∀ Ξ, 0 ≤ fh ((1 / (K : ℝ)) • (runSched (gpStep g fh xh η h) 0 K (x0, (0 : Point d), (0 : ℝ)) Ξ).2.1) - fh xh := fun Ξ => sub_nonneg.mpr (M.min _)
  have hpt : ∀ Ξ, fh ((1 / (K : ℝ)) • (runSched (gpStep g fh xh η h) 0 K (x0, (0 : Point d), (0 : ℝ)) Ξ).2.1) - fh xh ≤ (runSched (gpStep g fh xh η h) 0 K (x0, (0 : Point d), (0 : ℝ)) Ξ).2.2 / (K : ℝ) := by
    intro Ξ
    obtain ⟨f, ha, hb⟩ := gp_accumulate (g := g) (fh := fh) (xh := xh) (η := η) (h := h)
      (K := K) (i := 0) (s := (x0, (0 : Point d), (0 : ℝ))) (Ξ := Ξ)
    refine gp_avg_gap_le (hfhc := M.convex) (hK := hK) (s := (runSched (gpStep g fh xh η h) 0 K (x0, (0 : Point d), (0 : ℝ)) Ξ)) (f := f) ?_ ?_
    · simp [ha]
    · simp [hb]
  have hbnonneg : ∀ Ξ, 0 ≤ (runSched (gpStep g fh xh η h) 0 K (x0, (0 : Point d), (0 : ℝ)) Ξ).2.2 := fun Ξ =>
    gp_bnonneg (g := g) (fh := fh) (xh := xh) (η := η) (h := h) (hmin := M.min)
      K 0 (x0, (0 : Point d), (0 : ℝ)) Ξ le_rfl
  have hInt2 : Integrable (μ := gpLaw W K) (fun Ξ => η * (runSched (gpStep g fh xh η h) 0 K (x0, (0 : Point d), (0 : ℝ)) Ξ).2.2) := by
    refine Integrable.mono' hInt
      ((measurable_const :
          Measurable (fun _ : Fin K → secantSpace 1 1 → Point d × Ω => η)).mul
        hrun.snd.snd).aestronglyMeasurable ?_
    filter_upwards with Ξ
    have hb := hbnonneg Ξ
    have h0 := M.eta0
    have hηb : 0 ≤ η * (runSched (gpStep g fh xh η h) 0 K (x0, (0 : Point d), (0 : ℝ)) Ξ).2.2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hηb]
    have hp : 0 ≤ ‖(runSched (gpStep g fh xh η h) 0 K (x0, (0 : Point d), (0 : ℝ)) Ξ).1 - xh‖ ^ 2 := by positivity
    simp only [gpPot]
    linarith
  have hIntg : Integrable (μ := gpLaw W K) (fun Ξ => (runSched (gpStep g fh xh η h) 0 K (x0, (0 : Point d), (0 : ℝ)) Ξ).2.2 / (K : ℝ)) := by
    refine Integrable.mono' (hInt.div_const η)
      (Measurable.div_const hrun.snd.snd (K : ℝ)).aestronglyMeasurable ?_
    filter_upwards with Ξ
    have hb := hbnonneg Ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hb (by positivity))]
    have hdiv : (runSched (gpStep g fh xh η h) 0 K (x0, (0 : Point d), (0 : ℝ)) Ξ).2.2 / (K : ℝ) ≤ (runSched (gpStep g fh xh η h) 0 K (x0, (0 : Point d), (0 : ℝ)) Ξ).2.2 := (div_le_iff₀ hk).mpr (by nlinarith)
    have hge : (runSched (gpStep g fh xh η h) 0 K (x0, (0 : Point d), (0 : ℝ)) Ξ).2.2 ≤ gpPot xh η (runSched (gpStep g fh xh η h) 0 K (x0, (0 : Point d), (0 : ℝ)) Ξ) / η := by
      have hp : 0 ≤ ‖(runSched (gpStep g fh xh η h) 0 K (x0, (0 : Point d), (0 : ℝ)) Ξ).1 - xh‖ ^ 2 := by positivity
      refine (le_div_iff₀ hηp).mpr ?_
      simp only [gpPot]
      nlinarith
    exact hdiv.trans hge
  have hfn_intg : Integrable (μ := gpLaw W K)
      (fun Ξ => fh ((1 / (K : ℝ)) • (runSched (gpStep g fh xh η h) 0 K (x0, (0 : Point d), (0 : ℝ)) Ξ).2.1) - fh xh) := by
    refine Integrable.mono' hIntg hmeas.aestronglyMeasurable ?_
    filter_upwards with Ξ
    have hn := hnonneg Ξ
    have hp := hpt Ξ
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    linarith
  have h1 : ∫ Ξ, η * (runSched (gpStep g fh xh η h) 0 K (x0, (0 : Point d), (0 : ℝ)) Ξ).2.2 ∂(gpLaw W K) ≤ ‖x0 - xh‖ ^ 2 := by
    have h1a : ∫ Ξ, η * (runSched (gpStep g fh xh η h) 0 K (x0, (0 : Point d), (0 : ℝ)) Ξ).2.2 ∂(gpLaw W K) ≤ ∫ Ξ, gpPot xh η (runSched (gpStep g fh xh η h) 0 K (x0, (0 : Point d), (0 : ℝ)) Ξ) ∂(gpLaw W K) :=
      integral_mono hInt2 hInt (fun Ξ => by
        have hp : 0 ≤ ‖(runSched (gpStep g fh xh η h) 0 K (x0, (0 : Point d), (0 : ℝ)) Ξ).1 - xh‖ ^ 2 := by positivity
        simp only [gpPot]
        linarith)
    exact h1a.trans hle
  have h3 : ∫ Ξ, η * (runSched (gpStep g fh xh η h) 0 K (x0, (0 : Point d), (0 : ℝ)) Ξ).2.2 ∂(gpLaw W K)
      = η * ∫ Ξ, (runSched (gpStep g fh xh η h) 0 K (x0, (0 : Point d), (0 : ℝ)) Ξ).2.2 ∂(gpLaw W K) := integral_const_mul (μ := gpLaw W K) η _
  rw [h3] at h1
  have h5 : ∫ Ξ, (runSched (gpStep g fh xh η h) 0 K (x0, (0 : Point d), (0 : ℝ)) Ξ).2.2 ∂(gpLaw W K) ≤ ‖x0 - xh‖ ^ 2 / η := by
    field_simp [hηp.ne']
    nlinarith
  have h6 : ∫ Ξ, (runSched (gpStep g fh xh η h) 0 K (x0, (0 : Point d), (0 : ℝ)) Ξ).2.2 / (K : ℝ) ∂(gpLaw W K) = (∫ Ξ, (runSched (gpStep g fh xh η h) 0 K (x0, (0 : Point d), (0 : ℝ)) Ξ).2.2 ∂(gpLaw W K)) / (K : ℝ) := integral_div _ _
  have h7 : ∫ Ξ, fh ((1 / (K : ℝ)) • (runSched (gpStep g fh xh η h) 0 K (x0, (0 : Point d), (0 : ℝ)) Ξ).2.1) - fh xh ∂(gpLaw W K) ≤ ∫ Ξ, (runSched (gpStep g fh xh η h) 0 K (x0, (0 : Point d), (0 : ℝ)) Ξ).2.2 / (K : ℝ) ∂(gpLaw W K) :=
    integral_mono hfn_intg hIntg hpt
  have h9 : ∫ Ξ, (runSched (gpStep g fh xh η h) 0 K (x0, (0 : Point d), (0 : ℝ)) Ξ).2.2 / (K : ℝ) ∂(gpLaw W K) ≤ ‖x0 - xh‖ ^ 2 / (η * (K : ℝ)) := by
    rw [h6]
    have h9a : (∫ Ξ, (runSched (gpStep g fh xh η h) 0 K (x0, (0 : Point d), (0 : ℝ)) Ξ).2.2
        ∂(gpLaw W K)) / (K : ℝ) ≤ (‖x0 - xh‖ ^ 2 / η) / (K : ℝ) := by
      gcongr
    have h9b : (‖x0 - xh‖ ^ 2 / η) / (K : ℝ) = ‖x0 - xh‖ ^ 2 / (η * (K : ℝ)) := by
      field_simp [hηp.ne']
    linarith
  exact ⟨hfn_intg, h7.trans h9⟩

end OracleTemplate.SecantPolyak.GrowthConvex

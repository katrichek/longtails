import LongTails.Setups.ZerothOrderSmoothingStronglyConvex
import LongTails.Proofs.DirectionMomentumExecution
import LongTails.Proofs.DirectionMomentumTuning

set_option maxHeartbeats 2000000

/-!
Direction-sampled momentum descent for zeroth-order strongly convex minimization. Each round asks
the oracle for `2 * m k` one-sided probes along independent directions of the model's direction
measure, so the round surrogate is unbiased for the smoothed gradient and its mean-square deviation
is `2 * G ^ 2 / m k`. Because the surrogate carries no bias, only the noise level decides the batch
widths, and the budget is of order `κ * G ^ 2 / (L * ε)` instead of the `κ² * d³ * σ² / ε²` of the
coordinate-secant analysis. The bandwidth only has to keep the smoothing gap under `ε / 2`.
-/

namespace LongTails.Theorems.DirectionSampledMomentumStronglyConvex

open MeasureTheory ProbabilityTheory
open LongTails.Setups
open LongTails.Setups.ZerothOrderSmoothAndConvex
open LongTails.Setups.ZerothOrderSmoothingStronglyConvex
open scoped BigOperators RealInnerProductSpace
open OracleTemplate SecantPolyak SecantDescent
open OracleTemplate.SecantPolyak.Accelerated OracleTemplate.SecantPolyak.Centered
open OracleTemplate.SecantPolyak.Scheduled OracleTemplate.SecantPolyak.DirectionSampled

/-- Parameters of the randomized-smoothing zeroth-order model. -/
abbrev Par := LongTails.Setups.ZerothOrderSmoothingStronglyConvex.Params

/-- Noise strength of the direction-sampled schedule: `1` plus the value forced by the target. -/
noncomputable def noise (q : Par) : ℝ :=
  1 + 8 * cv q.L q.μ * (2 * q.G ^ 2) / (q.ε / 2 * th q.L q.μ)

/-- Momentum parameter: of order `sqrt (μ / L)`, the classic acceleration scaling. -/
noncomputable def mom (q : Par) : ℝ := th q.L q.μ

/-- Number of momentum rounds: of order `sqrt (L / μ) * log (L R² / ε)`. -/
noncomputable def steps (q : Par) : ℕ := iters q.L q.μ q.R (q.ε / 2)

/-- Replicas averaged in round `k`: graded so that the damped second-moment errors sum to `ε / 2`. -/
noncomputable def batches (q : Par) : ℕ → ℕ :=
  dirBatch q.L q.μ (2 * q.G ^ 2) (q.ε / 2) (steps q)

/-- Oracle budget: the exact number of zeroth-order probes, two one-sided probes per replica. -/
noncomputable def budget :
    (let S := LongTails.Setups.ZerothOrderSmoothingStronglyConvex.spec;
      S.Params → Fin S.numOracles → ℕ) :=
  fun q _ => ∑ k ∈ Finset.range (steps q), 2 * batches q k

/-- Direction-sampled momentum descent reaches expected accuracy `ε` with
`∑ k, 2 * batches q k` zeroth-order probes. -/
theorem result : Convergence LongTails.Setups.ZerothOrderSmoothingStronglyConvex.spec budget := by
  classical
  refine ⟨fun q => dirDescent (m := batches q)
      (fun k => Scheduled.graded_pos (noise q) (tauA q.L q.μ) (steps q) k)
      q.L q.μ (mom q) q.h q.x0, ?_, fun _ _ => trivial⟩
  intro q hq f O ho
  rcases hq with ⟨_hd, hL, hR, _hG, hμ, hε, _hh0, hband⟩
  obtain ⟨g, p, P, hind, hmarg, hO, hgm, hf, hxstar, hfh⟩ := ho
  obtain ⟨xstar, hmin, _hdist⟩ := hxstar
  obtain ⟨fh, _hcvx, hgr, hlip, hsc, hxh, hup, hdown, hint, hmean, hvar2, hvar⟩ := hfh
  obtain ⟨xh, hminh, hR_xh⟩ := hxh
  subst hO
  have hε2 : 0 < q.ε / 2 := by linarith
  have hth0 : 0 < mom q := th_pos q.L q.μ hL hμ
  have hth1 : mom q ≤ 1 := th_le_one q.L q.μ
  have hthL : 16 * q.L * mom q ^ 2 ≤ q.μ := th_constraint q.L q.μ hL hμ
  have hρ0 : 0 ≤ 1 - mom q / 2 := by linarith
  set K : ℕ := steps q
  set M : ℕ := batches q (K - 1)
  set o : Offsets 1 (batches q) := Scheduled.schedOffsets (d := 1) (batches q)
  set hb : ∀ k, 0 < batches q k := fun k => Scheduled.graded_pos (noise q) (tauA q.L q.μ) K k
  have hcv0 : 0 ≤ cv q.L q.μ := by
    show 0 ≤ 1 / (2 * q.L) + th q.L q.μ ^ 2 / q.μ
    positivity
  have hC0 : 0 ≤ noise q := by
    show 0 ≤ 1 + 8 * cv q.L q.μ * (2 * q.G ^ 2) / (q.ε / 2 * th q.L q.μ)
    refine add_nonneg zero_le_one
      (div_nonneg (mul_nonneg (mul_nonneg (by positivity) hcv0) (by positivity)) (by positivity))
  have hmM : ∀ k, batches q k ≤ M := by
    intro k
    by_cases hk : k ≤ K - 1
    · exact Scheduled.graded_le_last (noise q) (tauA q.L q.μ) hC0 (le_of_lt (tauA_pos q.L q.μ hL hμ))
        (tauA_le_one q.L q.μ hL hμ) K k hk
    · show Scheduled.graded (noise q) (tauA q.L q.μ) K k
          ≤ Scheduled.graded (noise q) (tauA q.L q.μ) K (K - 1)
      simp [Scheduled.graded, show K - 1 - k = 0 by omega]
  have hzeroh : gradient fh xh = 0 := by
    apply (InnerProductSpace.toDual ℝ (Point q.d)).injective
    simpa using (hminh.isLocalMin Filter.univ_mem).hasFDerivAt_eq_zero (hgr xh).hasFDerivAt
  have hinit : fh q.x0 - fh xh + q.μ / 4 * ‖q.x0 - xh‖ ^ 2
      ≤ q.L / 2 * q.R ^ 2 + q.μ / 4 * q.R ^ 2 := by
    have h1 : ‖q.x0 - xh‖ ^ 2 ≤ q.R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hR_xh 2
    have h2 : fh q.x0 - fh xh ≤ q.L / 2 * ‖q.x0 - xh‖ ^ 2 := by
      have h3 := _root_.OracleTemplate.Gradient.smooth_upper_bound hgr hlip xh q.x0
      rw [hzeroh, inner_zero_left, add_zero] at h3
      exact sub_le_iff_le_add'.mpr h3
    exact add_le_add (le_trans h2 (mul_le_mul_of_nonneg_left h1 (by positivity)))
      (mul_le_mul_of_nonneg_left h1 (by positivity))
  have hA : (1 - mom q / 2) ^ K * (q.L / 2 * q.R ^ 2 + q.μ / 4 * q.R ^ 2)
      + ∑ k ∈ Finset.range K, (1 - mom q / 2) ^ (K - 1 - k)
          * (cv q.L q.μ * ((2 * q.G ^ 2) / (batches q k : ℝ))) ≤ q.ε / 2 :=
    dir_tuning q.L q.μ (2 * q.G ^ 2) q.R (q.ε / 2) hL hμ (by positivity) hR hε2
  obtain ⟨hInt, hbnd⟩ := dir_exec_accuracy (d := q.d) (M := M) (m := batches q) hmM hb
    (g := g) (fh := fh) (nu := q.nu) (p := p) (L := q.L) (μ := q.μ) (θ := mom q) (h := q.h)
    (G := q.G) (x0 := q.x0) (xh := xh) hL hμ hth0 hth1 hthL hgm hgr hlip hsc hminh
    (fun x s => hint x s) (fun x s => hmean x s) (fun x s => hvar2 x s) (fun x s => hvar x s)
    P hind (fun k => hmarg k) o
  have hbud : budget q = fun _ : Fin 1 => o.off K := by
    refine funext fun _ => ?_
    show (∑ k ∈ Finset.range K, 2 * batches q k) = ∑ k ∈ Finset.range K, roundSlots 1 (batches q k)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [roundSlots_one]
  set X : (ℕ → Point q.d × q.Ω) → Point q.d := fun ξ =>
    (runSched (dirStepSched (batches q) hmM q.L q.μ (mom q) g q.h) 0 K (q.x0, q.x0)
      (fun k : Fin K => fun t : secantSpace 1 M =>
        ξ (schedIndex (d := 1) (M := M) (batches q) o K ⟨k, t⟩))).1
  have hXexec : X = fun ξ : ℕ → Point q.d × q.Ω =>
      execute (dirOracle q.h g P) (dirDescent (m := batches q) hb q.L q.μ (mom q) q.h q.x0)
        (fun _ => o.off K) () ξ := by
    funext ξ
    exact (execute_dirDescent (m := batches q) (hmM := hmM) hb q.L q.μ (mom q) q.h q.x0 o g ξ P K).symm
  have hlift : Measurable (fun ξ : ℕ → Point q.d × q.Ω => fun k : Fin K =>
      fun t : secantSpace 1 M => ξ (schedIndex (d := 1) (M := M) (batches q) o K ⟨k, t⟩)) := by
    fun_prop
  have hpair : Measurable (fun ξ : ℕ → Point q.d × q.Ω =>
      ((q.x0, q.x0), fun k : Fin K => fun t : secantSpace 1 M =>
        ξ (schedIndex (d := 1) (M := M) (batches q) o K ⟨k, t⟩))) :=
    measurable_const.prodMk hlift
  have hrun0 :
      Measurable ((fun w : (Point q.d × Point q.d) × (Fin K → secantSpace 1 M → Point q.d × q.Ω) =>
          runSched (dirStepSched (batches q) hmM q.L q.μ (mom q) g q.h) 0 K w.1 w.2) ∘
          (fun ξ : ℕ → Point q.d × q.Ω =>
            ((q.x0, q.x0), fun k : Fin K => fun t : secantSpace 1 M =>
              ξ (schedIndex (d := 1) (M := M) (batches q) o K ⟨k, t⟩)))) :=
    Measurable.comp
      (Scheduled.measurable_runSched (S := Point q.d × Point q.d)
        (fun k => measurable_dirStepSched_joint (m := batches q) hmM hgm q.L q.μ (mom q) q.h k) K 0)
      hpair
  have hrun : Measurable X := measurable_fst.comp hrun0
  have hB : q.L * q.h ^ 2 * (q.d : ℝ) ≤ q.ε / 2 := by linarith
  have hpoint : ∀ ξ : ℕ → Point q.d × q.Ω,
      f (X ξ) - f xstar ≤ (fh (X ξ) - fh xh) + q.L * q.h ^ 2 * (q.d : ℝ) := by
    intro ξ
    have h1 := smoothed_value_bound (q := q) (f := f) (fh := fh) (xstar := xstar) (xh := xh)
      (B := q.L * q.h ^ 2 * (q.d : ℝ) / 2) hmin hminh hup hdown (X ξ)
    have h2 : (2 : ℝ) * (q.L * q.h ^ 2 * (q.d : ℝ) / 2) = q.L * q.h ^ 2 * (q.d : ℝ) := by ring
    rw [h2] at h1
    exact h1
  have hgapInt : Integrable (fun ξ : ℕ → Point q.d × q.Ω => fh (X ξ) - fh xh)
      (P : Measure (ℕ → Point q.d × q.Ω)) := by
    rw [hXexec]
    exact hInt
  have hgapb : (∫ ξ : ℕ → Point q.d × q.Ω, fh (X ξ) - fh xh ∂(P : Measure (ℕ → Point q.d × q.Ω)))
      ≤ q.ε / 2 := by
    rw [hXexec]
    have heq : (∑ k ∈ Finset.range K, (1 - mom q / 2) ^ (K - 1 - k)
          * ((1 / (2 * q.L) + mom q ^ 2 / q.μ) * (2 * q.G ^ 2 / (batches q k : ℝ))))
        = ∑ k ∈ Finset.range K, (1 - mom q / 2) ^ (K - 1 - k)
            * (cv q.L q.μ * ((2 * q.G ^ 2) / (batches q k : ℝ))) := rfl
    refine (le_trans hbnd (add_le_add
      (mul_le_mul_of_nonneg_left hinit (pow_nonneg hρ0 K)) (le_of_eq heq))).trans hA
  have hmeas : Measurable (fun ξ : ℕ → Point q.d × q.Ω => f (X ξ) - f xstar) :=
    (hf.comp hrun).sub measurable_const
  have hfi : Integrable (fun ξ : ℕ → Point q.d × q.Ω => f (X ξ) - f xstar)
      (P : Measure (ℕ → Point q.d × q.Ω)) := by
    refine (hgapInt.add (integrable_const (q.L * q.h ^ 2 * (q.d : ℝ)))).mono'
      ((hf.comp hrun).sub measurable_const).aestronglyMeasurable ?_
    refine ae_of_all _ fun ξ => show ‖f (X ξ) - f xstar‖ ≤
        (fh (X ξ) - fh xh) + q.L * q.h ^ 2 * (q.d : ℝ) from ?_
    have h0 : 0 ≤ f (X ξ) - f xstar := sub_nonneg.mpr (hmin (Set.mem_univ _))
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact hpoint ξ
  have hgapFinal : (∫ ξ : ℕ → Point q.d × q.Ω, f (X ξ) - f xstar
        ∂(P : Measure (ℕ → Point q.d × q.Ω))) ≤ q.ε := by
    refine le_trans
      (integral_mono_ae hfi (hgapInt.add (integrable_const (q.L * q.h ^ 2 * (q.d : ℝ))))
        (ae_of_all _ hpoint)) ?_
    have h1 : (∫ ξ : ℕ → Point q.d × q.Ω,
          (fh (X ξ) - fh xh) + q.L * q.h ^ 2 * (q.d : ℝ)
          ∂(P : Measure (ℕ → Point q.d × q.Ω)))
        = (∫ ξ : ℕ → Point q.d × q.Ω, fh (X ξ) - fh xh
            ∂(P : Measure (ℕ → Point q.d × q.Ω))) + q.L * q.h ^ 2 * (q.d : ℝ) := by
      rw [integral_add hgapInt (integrable_const (q.L * q.h ^ 2 * (q.d : ℝ))), integral_const]
      simp
    refine (le_of_eq h1).trans ?_
    linarith
  set OT : Oracle (Point q.d × Bool) (ℝ × Point q.d) :=
    { Seed := fun _ => Point q.d × q.Ω, law := P,
      answer := fun _ (_, r) u => dirReply g r.1 r.2 u }
  have htransport (f : Point q.d → ℝ) (output1 output2 : Unit × (ℕ → Point q.d × q.Ω) → Point q.d)
      (μ : ProbabilityMeasure (Unit × (ℕ → Point q.d × q.Ω))) (hEq : output1 = output2)
      (hc : LongTails.Setups.ZerothOrderSmoothingStronglyConvex.spec.successful q f output2 μ) :
      LongTails.Setups.ZerothOrderSmoothingStronglyConvex.spec.successful q f output1 μ := by
    subst hEq
    exact hc
  have hpt : ∀ seed : Unit × (ℕ → Point q.d × q.Ω),
      execute OT (dirDescent (m := batches q) hb q.L q.μ (mom q) q.h q.x0) (budget q)
          seed.1 seed.2
        = X seed.2 := by
    intro seed
    cases seed with
    | mk s xi =>
        have h1 : execute OT (dirDescent (m := batches q) hb q.L q.μ (mom q) q.h q.x0)
              (budget q) () xi
            = execute OT (dirDescent (m := batches q) hb q.L q.μ (mom q) q.h q.x0)
              (fun _ => o.off K) () xi :=
          congrArg (fun b : Fin 1 → ℕ =>
            execute OT (dirDescent (m := batches q) hb q.L q.μ (mom q) q.h q.x0) b () xi) hbud
        exact h1.trans (congrFun hXexec.symm xi)
  have hfunEq : (fun seed : Unit × (ℕ → Point q.d × q.Ω) =>
        execute OT (dirDescent (m := batches q) hb q.L q.μ (mom q) q.h q.x0) (budget q)
          seed.1 seed.2)
      = (fun seed : Unit × (ℕ → Point q.d × q.Ω) => X seed.2) :=
    funext hpt
  have hfi2 : Integrable (fun seed : Unit × (ℕ → Point q.d × q.Ω) =>
      f (X seed.2) - f xstar)
      ((Measure.dirac () : Measure Unit).prod (P : Measure (ℕ → Point q.d × q.Ω))) :=
    (measurePreserving_snd).integrable_comp_of_integrable (ε := ℝ)
      (g := fun ξ : ℕ → Point q.d × q.Ω => f (X ξ) - f xstar) hfi
  have hintEq : (∫ seed : Unit × (ℕ → Point q.d × q.Ω),
        f (X seed.2) - f xstar
        ∂((Measure.dirac () : Measure Unit).prod (P : Measure (ℕ → Point q.d × q.Ω))))
      = ∫ ξ : ℕ → Point q.d × q.Ω, f (X ξ) - f xstar
          ∂(P : Measure (ℕ → Point q.d × q.Ω)) := by
    rw [integral_prod (f := fun seed : Unit × (ℕ → Point q.d × q.Ω) =>
        f (X seed.2) - f xstar) hfi2]
    dsimp only
    rw [integral_const]
    simp
  refine htransport _ _ _ _ hfunEq ⟨?_, xstar, hmin, ?_, ?_⟩
  · exact hrun.comp measurable_snd
  · exact hfi2
  · exact (le_of_eq hintEq).trans hgapFinal

end LongTails.Theorems.DirectionSampledMomentumStronglyConvex

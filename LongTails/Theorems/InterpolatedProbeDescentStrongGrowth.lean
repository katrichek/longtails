import LongTails.Setups.ZerothOrderSmoothingStrongGrowth
import LongTails.Proofs.InterpolatedProbeExecution
import LongTails.Proofs.GdPL

set_option maxHeartbeats 2000000

/-!
Mirrored-pair descent for zeroth-order strongly convex minimization under strong growth. Each round
asks two one-sided probes of the current iterate along one fresh direction of the model's direction
measure and moves against their signed sum by the fixed step `η`, the tightest of `1 / L`, `1 / μ`
and `μ / (2 L ρ²)`. Because the model bounds the mean-square probe deviation by `ρ²` times the
current smoothed gap instead of by a fixed variance, one pair per round contracts the expected
smoothed gap by `1 - η * μ / 2`, and `2 * ⌈2 / (η * μ) * log (1 + L * R² / ε)⌉` probes reach expected
accuracy `ε`. That is logarithmic in `1 / ε`, against the `G² / (μ * ε)` of the same model with only
a uniform variance bound. The bandwidth only has to keep the smoothing gap under `ε / 2`.
-/

namespace LongTails.Theorems.InterpolatedProbeDescentStrongGrowth

open MeasureTheory ProbabilityTheory
open LongTails.Setups
open LongTails.Setups.ZerothOrderSmoothAndConvex
open LongTails.Setups.ZerothOrderSmoothingStrongGrowth
open scoped BigOperators RealInnerProductSpace
open OracleTemplate SecantPolyak SecantDescent
open OracleTemplate.SecantPolyak.Interpolated
open OracleTemplate.SecantPolyak.Scheduled OracleTemplate.SecantPolyak.DirectionSampled

/-- Parameters of the strong-growth randomized-smoothing probe model. -/
abbrev Par := LongTails.Setups.ZerothOrderSmoothingStrongGrowth.Params

/-- Step size: the tightest of the descent cap `1 / L`, the contraction cap `1 / μ`, and the
strong-growth cap `μ / (2 L ρ²)`. -/
noncomputable def eta (q : Par) : ℝ :=
  min (1 / q.L) (min (1 / q.μ) (q.μ / (2 * q.L * q.ρ ^ 2)))

/-- Contraction of the expected smoothed gap in one mirrored-pair round. -/
noncomputable def rate (q : Par) : ℝ := eta q * q.μ / 2

/-- The initial smoothed gap bound forced by `‖x0 − xh‖ ≤ R`. -/
noncomputable def gap0 (q : Par) : ℝ := q.L * q.R ^ 2 / 2

/-- Rounds of mirrored-pair descent: logarithmic in `1 / ε` under strong growth. -/
noncomputable def iters (q : Par) : ℕ :=
  ⌈(1 / rate q) * Real.log (1 + gap0 q / (q.ε / 2))⌉₊

/-- Oracle budget: exactly two one-sided probes per round, with no batching. -/
noncomputable def budget :
    (let S := LongTails.Setups.ZerothOrderSmoothingStrongGrowth.spec;
      S.Params → Fin S.numOracles → ℕ) :=
  fun q _ => 2 * iters q

/-- Mirrored-pair descent reaches expected accuracy `ε` with `2 * iters q` zeroth-order probes. -/
theorem result :
    Convergence LongTails.Setups.ZerothOrderSmoothingStrongGrowth.spec budget := by
  classical
  refine ⟨fun q => ipDescent (eta q) q.h q.x0, ?_, fun _ _ => trivial⟩
  intro q hq f O ho
  rcases hq with ⟨_hd, hL, hR, hμ, hε, _hh0, hrho, hband⟩
  obtain ⟨g, p, P, hind, hmarg, hO, hgm, hf, hxstar, hfh⟩ := ho
  obtain ⟨xstar, hmin, _hdist⟩ := hxstar
  obtain ⟨fh, xh, _hcvx, hgr, hlip, hsc, hminh, hR_xh, hup, hdown, hint, hmean, hvar2, hvar⟩ :=
    hfh
  subst hO
  set B : ℝ := q.L * q.h ^ 2 * (q.d : ℝ)
  have hε2 : 0 < q.ε / 2 := by linarith
  have hEtaL : q.L * eta q ≤ 1 := by
    have h1 : eta q ≤ 1 / q.L := min_le_left _ _
    have h2 : q.L * (1 / q.L) = 1 := by field_simp
    refine (mul_le_mul_of_nonneg_left h1 (le_of_lt hL)).trans ?_
    rw [h2]
  have hEtaM : eta q * q.μ ≤ 1 := by
    have h1 : eta q ≤ 1 / q.μ := (min_le_right _ _).trans (min_le_left _ _)
    have h2 : (1 / q.μ) * q.μ = 1 := by field_simp
    refine (mul_le_mul_of_nonneg_right h1 (le_of_lt hμ)).trans ?_
    rw [h2]
  have hEtaR : q.L * eta q * q.ρ ^ 2 ≤ q.μ / 2 := by
    have h1 : eta q ≤ q.μ / (2 * q.L * q.ρ ^ 2) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have h2 : q.L * (q.μ / (2 * q.L * q.ρ ^ 2)) * q.ρ ^ 2 = q.μ / 2 := by field_simp
    have h3 : q.L * eta q * q.ρ ^ 2 ≤ q.L * (q.μ / (2 * q.L * q.ρ ^ 2)) * q.ρ ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (le_of_lt hL)) (sq_nonneg _)
    exact h3.trans (le_of_eq h2)
  have hrho2 : 0 < q.ρ ^ 2 := pow_pos hrho 2
  have hden : 0 < 2 * q.L * q.ρ ^ 2 := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hL) hrho2
  have h1 : 0 < (1 : ℝ) / q.L := by positivity
  have h2 : 0 < (1 : ℝ) / q.μ := by positivity
  have h3 : 0 < q.μ / (2 * q.L * q.ρ ^ 2) := div_pos hμ hden
  have hEtaP : 0 < eta q := by
    show 0 < min (1 / q.L) (min (1 / q.μ) (q.μ / (2 * q.L * q.ρ ^ 2)))
    rw [lt_min_iff, lt_min_iff]
    exact ⟨h1, h2, h3⟩
  have hEta0 : 0 ≤ eta q := le_of_lt hEtaP
  have hrate0 : 0 < rate q := by
    show 0 < eta q * q.μ / 2
    refine div_pos (mul_pos hEtaP hμ) two_pos
  have hrate1 : rate q ≤ 1 := by
    show eta q * q.μ / 2 ≤ 1
    have h1 : 0 ≤ eta q * q.μ := by nlinarith
    have h2 : 0 ≤ q.μ := le_of_lt hμ
    nlinarith
  set K : ℕ := iters q
  set o : Offsets 1 ipM := ipOffsets
  have hoff : ∀ k : ℕ, o.off k = 2 * k := fun _ => rfl
  have hzeroh : gradient fh xh = 0 := by
    apply (InnerProductSpace.toDual ℝ (Point q.d)).injective
    simpa using (hminh.isLocalMin Filter.univ_mem).hasFDerivAt_eq_zero (hgr xh).hasFDerivAt
  have hinit : fh q.x0 - fh xh ≤ gap0 q := by
    have h1 : ‖q.x0 - xh‖ ^ 2 ≤ q.R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hR_xh 2
    have h2 : fh q.x0 - fh xh ≤ q.L / 2 * ‖q.x0 - xh‖ ^ 2 := by
      have h3 := _root_.OracleTemplate.Gradient.smooth_upper_bound hgr hlip xh q.x0
      rw [hzeroh, inner_zero_left, add_zero] at h3
      exact sub_le_iff_le_add'.mpr h3
    have h4 : q.L / 2 * ‖q.x0 - xh‖ ^ 2 ≤ q.L / 2 * q.R ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ q.L / 2)
    have h5 : q.L / 2 * q.R ^ 2 = gap0 q := by show q.L / 2 * q.R ^ 2 = q.L * q.R ^ 2 / 2; ring
    exact h2.trans h4 |>.trans h5.le
  have hgap0 : 0 ≤ gap0 q :=
    div_nonneg (mul_nonneg (le_of_lt hL) (sq_nonneg _)) (by norm_num : (0 : ℝ) ≤ 2)
  have hgeo0 : (1 - rate q / 1) ^ K * gap0 q ≤ q.ε / 2 :=
    OracleTemplate.PLGradient.geometric_budget 1 (rate q) (gap0 q) (q.ε / 2) hrate0 hrate1 hgap0
      hε2 K (Nat.le_ceil _)
  have hid : (1 - rate q / 1 : ℝ) = 1 - rate q := by rw [div_one]
  rw [hid] at hgeo0
  have hgeo := hgeo0
  obtain ⟨hInt, hbnd⟩ := ip_exec_accuracy (d := q.d) (g := g) (fh := fh) (W := probeMeasure q.nu p)
    (L := q.L) (μ := q.μ) (η := eta q) (h := q.h) (ρ := q.ρ) (x0 := q.x0) (xh := xh) (K := K)
    hL hμ hEta0 hEtaL hEtaM hEtaR hgm hgr hlip hsc hminh (fun x s => hint x s)
    (fun x s => hmean x s) (fun x s => hvar2 x s) (fun x s => hvar x s) P hind (fun k => hmarg k) o
  have hbud : budget q = fun _ : Fin 1 => o.off K := by
    refine funext fun _ => ?_
    show 2 * K = o.off K
    rw [hoff]
  set X : (ℕ → Point q.d × q.Ω) → Point q.d := fun ξ =>
    runSched (ipStepSched g (eta q) q.h) 0 K q.x0
      (fun k : Fin K => fun t : secantSpace 1 1 =>
        ξ (schedIndex (d := 1) (M := 1) ipM o K ⟨k, t⟩))
  have hXexec : X = fun ξ : ℕ → Point q.d × q.Ω =>
      execute (dirOracle q.h g P) (ipDescent (eta q) q.h q.x0) (fun _ => o.off K) () ξ := by
    funext ξ
    exact (ip_execute (eta q) q.h q.x0 o g ξ P K).symm
  have hlift : Measurable (fun ξ : ℕ → Point q.d × q.Ω => fun k : Fin K =>
      fun t : secantSpace 1 1 => ξ (schedIndex (d := 1) (M := 1) ipM o K ⟨k, t⟩)) := by
    fun_prop
  have hpair : Measurable (fun ξ : ℕ → Point q.d × q.Ω =>
      (q.x0, fun k : Fin K => fun t : secantSpace 1 1 =>
        ξ (schedIndex (d := 1) (M := 1) ipM o K ⟨k, t⟩))) :=
    measurable_const.prodMk hlift
  have hrun0 :
      Measurable ((fun w : Point q.d × (Fin K → secantSpace 1 1 → Point q.d × q.Ω) =>
          runSched (ipStepSched g (eta q) q.h) 0 K w.1 w.2) ∘
          (fun ξ : ℕ → Point q.d × q.Ω =>
            (q.x0, fun k : Fin K => fun t : secantSpace 1 1 =>
              ξ (schedIndex (d := 1) (M := 1) ipM o K ⟨k, t⟩)))) :=
    Measurable.comp
      (Scheduled.measurable_runSched (S := Point q.d)
        (fun k => measurable_ipStepSched_joint hgm (eta q) q.h k) K 0) hpair
  have hrun : Measurable X := hrun0
  have hB : B ≤ q.ε / 2 := by
    show q.L * q.h ^ 2 * (q.d : ℝ) ≤ q.ε / 2
    have h1 : (2 : ℝ) * (q.L * q.h ^ 2 * (q.d : ℝ)) = 2 * q.L * q.h ^ 2 * (q.d : ℝ) := by ring
    have h2 : (2 : ℝ) * (q.L * q.h ^ 2 * (q.d : ℝ)) ≤ q.ε := by
      rw [h1]
      exact hband
    have h3 : q.L * q.h ^ 2 * (q.d : ℝ) = (2 * (q.L * q.h ^ 2 * (q.d : ℝ))) / 2 := by ring
    rw [h3]
    refine (div_le_iff₀ (by norm_num : (0 : ℝ) < (2 : ℝ))).mpr ?_
    have h4 : (q.ε / 2) * 2 = q.ε := by ring
    rw [h4]
    exact h2
  have hpoint : ∀ y : Point q.d, f y - f xstar ≤ (fh y - fh xh) + B := by
    intro y
    have h1 : f y - fh y ≤ B / 2 := hdown y
    have h2 : fh xstar - f xstar ≤ B / 2 := hup xstar
    have h3 : fh xh ≤ fh xstar := hminh (Set.mem_univ xstar)
    have h4 : fh y - fh xstar ≤ fh y - fh xh := sub_le_sub_left h3 _
    linarith
  have hgapInt : Integrable (fun ξ : ℕ → Point q.d × q.Ω => fh (X ξ) - fh xh)
      (P : Measure (ℕ → Point q.d × q.Ω)) := by
    rw [hXexec]
    exact hInt
  have hgapb : (∫ ξ : ℕ → Point q.d × q.Ω, fh (X ξ) - fh xh ∂(P : Measure (ℕ → Point q.d × q.Ω)))
      ≤ q.ε / 2 := by
    rw [hXexec]
    have h1 : 0 ≤ (1 : ℝ) - eta q * q.μ / 2 := by
      have h2 : 0 ≤ eta q * q.μ := by nlinarith
      nlinarith
    have h3 : (1 - eta q * q.μ / 2) ^ K * (fh q.x0 - fh xh)
        ≤ (1 - eta q * q.μ / 2) ^ K * gap0 q :=
      mul_le_mul_of_nonneg_left hinit (pow_nonneg h1 K)
    exact hbnd.trans (h3.trans hgeo)
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
    exact hpoint (X ξ)
  have hgapFinal : (∫ ξ : ℕ → Point q.d × q.Ω, f (X ξ) - f xstar
        ∂(P : Measure (ℕ → Point q.d × q.Ω))) ≤ q.ε := by
    refine le_trans
      (integral_mono_ae hfi (hgapInt.add (integrable_const (q.L * q.h ^ 2 * (q.d : ℝ))))
        (ae_of_all _ fun ξ => hpoint (X ξ))) ?_
    have h1 : (∫ ξ : ℕ → Point q.d × q.Ω,
          (fh (X ξ) - fh xh) + q.L * q.h ^ 2 * (q.d : ℝ)
          ∂(P : Measure (ℕ → Point q.d × q.Ω)))
        = (∫ ξ : ℕ → Point q.d × q.Ω, fh (X ξ) - fh xh
            ∂(P : Measure (ℕ → Point q.d × q.Ω))) + q.L * q.h ^ 2 * (q.d : ℝ) := by
      rw [integral_add hgapInt (integrable_const (q.L * q.h ^ 2 * (q.d : ℝ))), integral_const]
      simp
    refine (le_of_eq h1).trans ?_
    linarith
  set OT : Oracle (Point q.d × Bool) (ℝ × Point q.d) := dirOracle q.h g P
  have htransport (f : Point q.d → ℝ) (output1 output2 : Unit × (ℕ → Point q.d × q.Ω) → Point q.d)
      (μ : ProbabilityMeasure (Unit × (ℕ → Point q.d × q.Ω))) (hEq : output1 = output2)
      (hc : LongTails.Setups.ZerothOrderSmoothingStrongGrowth.spec.successful q f output2 μ) :
      LongTails.Setups.ZerothOrderSmoothingStrongGrowth.spec.successful q f output1 μ := by
    subst hEq
    exact hc
  have hpt : ∀ seed : Unit × (ℕ → Point q.d × q.Ω),
      execute OT (ipDescent (eta q) q.h q.x0) (budget q) seed.1 seed.2 = X seed.2 := by
    intro seed
    cases seed with
    | mk s xi =>
        have h1 : execute OT (ipDescent (eta q) q.h q.x0) (budget q) () xi
            = execute OT (ipDescent (eta q) q.h q.x0) (fun _ => o.off K) () xi :=
          congrArg (fun b : Fin 1 → ℕ => execute OT (ipDescent (eta q) q.h q.x0) b () xi) hbud
        exact h1.trans (congrFun hXexec.symm xi)
  have hfunEq : (fun seed : Unit × (ℕ → Point q.d × q.Ω) =>
        execute OT (ipDescent (eta q) q.h q.x0) (budget q) seed.1 seed.2)
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

end LongTails.Theorems.InterpolatedProbeDescentStrongGrowth

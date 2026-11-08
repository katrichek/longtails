import LongTails.Setups.ZerothOrderSmoothingBatchedAcceleration
import LongTails.Proofs.GradedAnchoredExecution
import LongTails.Proofs.GdPL

set_option maxHeartbeats 2000000

/-!
Weighted anchored pair acceleration with mirrored batching for zeroth-order strongly convex
minimization. Round `k` asks `2 * m` one-sided probes of the interpolated point
`(x + θ z) / (1 + θ)` along `m` independent directions, moves the iterate by the damped step
`η = 1 / L` and the anchor by the weighted step `θ / (2 * β)` against their signed average, where
`β = μ / 3` and `θ = √(2 μ / (3 L))`. Averaging `m` mirrored pairs divides the mean-square deviation
of the round surrogate by `m`, so the weighted potential absorbs it as soon as
`6 * ρ² ≤ m * μ * θ`; the width `m = max 1 ⌈6 ρ² / (μ θ)⌉₊` is derived from that cap, so the model
needs no interpolation restriction on `ρ`. The expected potential contracts by `1 − θ` per round, and
`2 * m * ⌈√(3 L / (2 μ)) · log (1 + 5 L R² / (3 ε))⌉` probes reach expected accuracy `ε`, which is
`Θ(√(L / μ) · log (1 / ε))` with leading constant `√(3 / 2)` in the small-`ρ` regime.
-/

namespace LongTails.Theorems.GradedAnchoredAccelerationStrongGrowth

open MeasureTheory ProbabilityTheory
open LongTails.Setups
open LongTails.Setups.ZerothOrderSmoothAndConvex
open LongTails.Setups.ZerothOrderSmoothingBatchedAcceleration
open scoped BigOperators RealInnerProductSpace
open OracleTemplate SecantPolyak SecantDescent InexactGradient
open OracleTemplate.SecantPolyak.GradedAnchored
open OracleTemplate.SecantPolyak.Scheduled OracleTemplate.SecantPolyak.DirectionSampled

/-- Parameters of the randomized-smoothing strong-growth probe model. -/
abbrev Par := LongTails.Setups.ZerothOrderSmoothingStrongGrowth.Params

/-- Contraction weight of the weighted anchored pair scheme. -/
noncomputable def rate (q : Par) : ℝ := mmt q

/-- Batch width derived from the noise absorption cap of the weighted anchored potential. -/
noncomputable def widthOf (q : Par) : ℕ := width q

/-- Initial weighted potential bound forced by `‖x0 − xh‖ ≤ R` and `μ ≤ L`. -/
noncomputable def gap0 (q : Par) : ℝ := 3 * q.L * q.R ^ 2 / 4

/-- Rounds of weighted anchored pair acceleration: logarithmic in `1 / ε`. -/
noncomputable def iters (q : Par) : ℕ :=
  ⌈(1 / rate q) * Real.log (1 + gap0 q / (q.ε / 2))⌉₊

/-- Oracle budget: `2 * m` one-sided probes per round, `m` the derived batch width. -/
noncomputable def budget :
    (let S := LongTails.Setups.ZerothOrderSmoothingBatchedAcceleration.spec;
      S.Params → Fin S.numOracles → ℕ) :=
  fun q _ =>
    2 * max 1 ⌈4 * q.ρ ^ 2 / (q.μ * Real.sqrt (q.μ / (2 * q.L)))⌉₊ *
      ⌈Real.sqrt (2 * q.L / q.μ) * Real.log (1 + 3 * q.L * q.R ^ 2 / (2 * q.ε))⌉₊

/-- Weighted anchored pair acceleration with mirrored batching reaches expected accuracy `ε` with
`2 * m * ⌈√(3 L / (2 μ)) · log (1 + 5 L R² / (3 ε))⌉` zeroth-order probes and no interpolation cap. -/
theorem result :
    Convergence LongTails.Setups.ZerothOrderSmoothingBatchedAcceleration.spec budget := by
  classical
  refine ⟨fun q => agDescent (m := agM (width q)) (fun _ => width_pos q) (anch q) (mmt q)
      (1 / q.L) q.h q.x0, ?_, fun _ _ => trivial⟩
  intro q hq f O ho
  rcases hq with ⟨_hd, hL, hR, hμ, hμL, hε, _hh0, hrho, hband⟩
  obtain ⟨g, p, P, hind, hmarg, hO, hgm, hf, hxstar, hfh⟩ := ho
  obtain ⟨xstar, hmin, _hdist⟩ := hxstar
  obtain ⟨fh, xh, _hcvx, hgr, hlip, hsc, hminh, hR_xh, hup, hdown, hint, hmean, hvar2, hvar⟩ :=
    hfh
  subst hO
  set B : ℝ := q.L * q.h ^ 2 * (q.d : ℝ)
  have hε2 : 0 < q.ε / 2 := by linarith
  have hm : 0 < width q := width_pos q
  have hβ : 0 < anch q := by
    show 0 < q.μ / 4
    positivity
  have hβh : anch q ≤ q.μ / 2 := by
    show q.μ / 4 ≤ q.μ / 2
    linarith
  have hθ : mmt q = Real.sqrt (q.μ / (2 * q.L)) := rfl
  have hθ0 : 0 < mmt q := by
    show 0 < Real.sqrt (q.μ / (2 * q.L))
    refine Real.sqrt_pos.mpr (div_pos (by positivity) (by positivity))
  have hθ1 : mmt q ≤ 1 := by
    have h1 : q.μ / (2 * q.L) ≤ 1 := by
      refine (div_le_one (by positivity)).mpr ?_
      nlinarith
    exact Real.sqrt_le_one.mpr h1
  have hθsq : mmt q ^ 2 = q.μ / (2 * q.L) := by
    show Real.sqrt (q.μ / (2 * q.L)) ^ 2 = _
    rw [Real.sq_sqrt (by positivity)]
  have hstep : q.L * (1 / q.L) ^ 2 / 2 = 1 / (2 * q.L) := by
    field_simp [hL.ne']
  have hdev : mmt q ^ 2 / (4 * anch q) = 1 / (2 * q.L) := by
    rw [hθsq]
    show (q.μ / (2 * q.L)) / (4 * (q.μ / 4)) = 1 / (2 * q.L)
    field_simp
  have hcap1 : mmt q ^ 2 / (4 * anch q) ≤ 1 / q.L - q.L * (1 / q.L) ^ 2 / 2 := by
    have h1 : 1 / q.L - q.L * (1 / q.L) ^ 2 / 2 = 1 / (2 * q.L) := by
      rw [hstep]
      ring
    rw [h1, hdev]
  have hcapcv : q.L * (1 / q.L) ^ 2 / 2 + mmt q ^ 2 / (4 * anch q) = 1 / q.L := by
    rw [hstep, hdev]
    ring
  have hw : (width q : ℝ) ≥ 4 * q.ρ ^ 2 / (q.μ * mmt q) := by
    have h2 : (4 * q.ρ ^ 2 / (q.μ * mmt q) : ℝ) ≤ (⌈4 * q.ρ ^ 2 / (q.μ * mmt q)⌉₊ : ℝ) :=
      Nat.le_ceil _
    have h3 : (⌈4 * q.ρ ^ 2 / (q.μ * mmt q)⌉₊ : ℝ) ≤ (width q : ℝ) :=
      mod_cast Nat.le_max_right 1 ⌈4 * q.ρ ^ 2 / (q.μ * mmt q)⌉₊
    linarith
  have hmge : (2 : ℝ) * q.ρ ^ 2 / (width q : ℝ) ≤ q.μ * mmt q / 2 := by
    refine (div_le_iff₀ (by positivity)).mpr ?_
    have hq : q.μ * mmt q ≠ 0 := by
      show q.μ * Real.sqrt (q.μ / (2 * q.L)) ≠ 0
      positivity
    have h2 : (4 * q.ρ ^ 2 / (q.μ * mmt q)) * (q.μ * mmt q / 2) = 2 * q.ρ ^ 2 := by
      field_simp [hq, hrho.ne']
      ring
    have h3 : (4 * q.ρ ^ 2 / (q.μ * mmt q)) * (q.μ * mmt q / 2) ≤
        (width q : ℝ) * (q.μ * mmt q / 2) :=
      mul_le_mul_of_nonneg_right hw (by positivity)
    linarith
  have hcap3 :
      (q.L * (1 / q.L) ^ 2 / 2 + mmt q ^ 2 / (4 * anch q)) * (2 * q.ρ ^ 2 / (width q : ℝ))
        ≤ mmt q * (q.μ / 2 - anch q) * (2 / q.L) := by
    rw [hcapcv]
    have h1 : mmt q * (q.μ / 2 - anch q) * (2 / q.L) = (q.μ * mmt q / 2) / q.L := by
      show mmt q * (q.μ / 2 - q.μ / 4) * (2 / q.L) = _
      ring
    have h2 : (1 / q.L) * (2 * q.ρ ^ 2 / (width q : ℝ)) = (2 * q.ρ ^ 2 / (width q : ℝ)) / q.L := by
      ring
    rw [h1, h2]
    refine (div_le_div_iff₀ (by positivity) (by positivity)).mpr ?_
    nlinarith
  set K : ℕ :=
    ⌈Real.sqrt (2 * q.L / q.μ) * Real.log (1 + 3 * q.L * q.R ^ 2 / (2 * q.ε))⌉₊
  have hinv : Real.sqrt (2 * q.L / q.μ) = 1 / mmt q := by
    have h2 : 2 * q.L / q.μ = (q.μ / (2 * q.L))⁻¹ := by field_simp
    rw [h2, Real.sqrt_inv]
    show (Real.sqrt (q.μ / (2 * q.L)))⁻¹ = 1 / Real.sqrt (q.μ / (2 * q.L))
    exact (one_mul _).symm
  have hgapid : gap0 q / (q.ε / 2) = 3 * q.L * q.R ^ 2 / (2 * q.ε) := by
    show (3 * q.L * q.R ^ 2 / 4) / (q.ε / 2) = _
    field_simp
    ring
  have hKb : ⌈(1 / mmt q) * Real.log (1 + gap0 q / (q.ε / 2))⌉₊ ≤ K := by
    rw [hgapid, show (1 / mmt q) = Real.sqrt (2 * q.L / q.μ) from hinv.symm]
  have hgap0 : 0 ≤ gap0 q := by
    show 0 ≤ 3 * q.L * q.R ^ 2 / 4
    refine div_nonneg ?_ (by norm_num)
    refine mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hL)) (sq_nonneg _)
  have hgeo : (1 - mmt q) ^ K * gap0 q ≤ q.ε / 2 := by
    have h1 : (1 - mmt q / 1) ^ K * gap0 q ≤ q.ε / 2 :=
      OracleTemplate.PLGradient.geometric_budget 1 (mmt q) (gap0 q) (q.ε / 2) hθ0 hθ1 hgap0 hε2
        K hKb
    have h3 : (1 - mmt q / 1 : ℝ) = 1 - mmt q := by rw [div_one]
    rw [h3] at h1
    exact h1
  set o : Offsets 1 (agM (width q)) := agOffsets (width q)
  have hoff : ∀ k : ℕ, o.off k = 2 * (width q) * k := fun _ => rfl
  have hbud : budget q = fun _ : Fin 1 => o.off K := by
    refine funext fun _ => ?_
    show 2 * width q * K = o.off K
    rw [hoff]
  have hzeroh : gradient fh xh = 0 := by
    apply (InnerProductSpace.toDual ℝ (Point q.d)).injective
    simpa using (hminh.isLocalMin Filter.univ_mem).hasFDerivAt_eq_zero (hgr xh).hasFDerivAt
  have hgapx : fh q.x0 - fh xh ≤ q.L * q.R ^ 2 / 2 := by
    have h1 : ‖q.x0 - xh‖ ^ 2 ≤ q.R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hR_xh 2
    have h2 : fh q.x0 - fh xh ≤ q.L / 2 * ‖q.x0 - xh‖ ^ 2 := by
      have h3 := _root_.OracleTemplate.Gradient.smooth_upper_bound hgr hlip xh q.x0
      rw [hzeroh, inner_zero_left, add_zero] at h3
      exact sub_le_iff_le_add'.mpr h3
    have h4 : q.L / 2 * ‖q.x0 - xh‖ ^ 2 ≤ q.L / 2 * q.R ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ q.L / 2)
    have h5 : q.L / 2 * q.R ^ 2 = q.L * q.R ^ 2 / 2 := by ring
    exact h2.trans h4 |>.trans h5.le
  have hinit : waPotential fh (anch q) xh (q.x0, q.x0) ≤ gap0 q := by
    have h1 : ‖q.x0 - xh‖ ^ 2 ≤ q.R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hR_xh 2
    have h2 : waPotential fh (anch q) xh (q.x0, q.x0)
        = fh q.x0 - fh xh + (q.μ / 4) * ‖q.x0 - xh‖ ^ 2 := rfl
    rw [h2]
    have h3a : (q.μ / 4) * ‖q.x0 - xh‖ ^ 2 ≤ (q.μ / 4) * q.R ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3b : (q.μ / 4) * q.R ^ 2 ≤ (q.L / 4) * q.R ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith [hμL]) (sq_nonneg _)
    have h3 : (q.μ / 4) * ‖q.x0 - xh‖ ^ 2 ≤ (q.L / 4) * q.R ^ 2 := h3a.trans h3b
    have h4 : fh q.x0 - fh xh ≤ q.L / 2 * q.R ^ 2 := by
      have h5 : q.L * q.R ^ 2 / 2 = q.L / 2 * q.R ^ 2 := by ring
      rw [← h5]
      exact hgapx
    have h6 : q.L / 2 * q.R ^ 2 + q.L / 4 * q.R ^ 2 = gap0 q := by
      show q.L / 2 * q.R ^ 2 + q.L / 4 * q.R ^ 2 = 3 * q.L * q.R ^ 2 / 4
      ring
    linarith
  obtain ⟨hInt, hbnd⟩ := ag_exec_accuracy (d := q.d) (m := width q) hm (g := g) (fh := fh)
    (W := probeMeasure q.nu p) (L := q.L) (μ := q.μ) (β := anch q) (θ := mmt q) (η := 1 / q.L)
    (h := q.h) (ρ := q.ρ) (x0 := q.x0) (xh := xh) (K := K) hL hμ hβ hβh hθ0 hθ1 hcap1 hcap3 hgm
    hgr hlip hsc hminh (fun x s => hint x s) (fun x s => hmean x s) (fun x s => hvar2 x s)
    (fun x s => hvar x s) P hind (fun k => hmarg k) o
  set X : (ℕ → Point q.d × q.Ω) → Point q.d := fun ξ =>
    (runSched (waStepSched (anch q) (mmt q) (1 / q.L) g q.h (width q)) 0 K (q.x0, q.x0)
      (fun k : Fin K => fun t : secantSpace 1 (width q) =>
        ξ (schedIndex (d := 1) (M := width q) (agM (width q)) o K ⟨k, t⟩))).1
  have hXexec : X = fun ξ : ℕ → Point q.d × q.Ω =>
      execute (dirOracle q.h g P)
        (agDescent (m := agM (width q)) (fun _ => hm) (anch q) (mmt q) (1 / q.L) q.h q.x0)
        (fun _ => o.off K) () ξ := by
    funext ξ
    exact (ag_execute (width q) hm (anch q) (mmt q) (1 / q.L) q.h q.x0 o g ξ P K).symm
  have hlift : Measurable (fun ξ : ℕ → Point q.d × q.Ω => fun k : Fin K =>
      fun t : secantSpace 1 (width q) =>
        ξ (schedIndex (d := 1) (M := width q) (agM (width q)) o K ⟨k, t⟩)) := by
    fun_prop
  have hpair : Measurable (fun ξ : ℕ → Point q.d × q.Ω =>
      ((q.x0, q.x0), fun k : Fin K => fun t : secantSpace 1 (width q) =>
        ξ (schedIndex (d := 1) (M := width q) (agM (width q)) o K ⟨k, t⟩))) :=
    measurable_const.prodMk hlift
  have hrun0 :
      Measurable ((fun w : (Point q.d × Point q.d) ×
            (Fin K → secantSpace 1 (width q) → Point q.d × q.Ω) =>
          runSched (waStepSched (anch q) (mmt q) (1 / q.L) g q.h (width q)) 0 K w.1 w.2) ∘
          (fun ξ : ℕ → Point q.d × q.Ω =>
            ((q.x0, q.x0), fun k : Fin K => fun t : secantSpace 1 (width q) =>
              ξ (schedIndex (d := 1) (M := width q) (agM (width q)) o K ⟨k, t⟩)))) :=
    Measurable.comp
      (Scheduled.measurable_runSched (S := Point q.d × Point q.d)
        (fun k => measurable_waStepSched_joint hgm (anch q) (mmt q) (1 / q.L) q.h (width q) k)
        K 0) hpair
  have hrun : Measurable (fun ξ : ℕ → Point q.d × q.Ω =>
      runSched (waStepSched (anch q) (mmt q) (1 / q.L) g q.h (width q)) 0 K (q.x0, q.x0)
        (fun k : Fin K => fun t : secantSpace 1 (width q) =>
          ξ (schedIndex (d := 1) (M := width q) (agM (width q)) o K ⟨k, t⟩))) := hrun0
  have hrunmeas : Measurable X := Measurable.fst hrun
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
    have h1 : 0 ≤ (1 : ℝ) - mmt q := by linarith
    have h3 : (1 - mmt q) ^ K * waPotential fh (anch q) xh (q.x0, q.x0)
        ≤ (1 - mmt q) ^ K * gap0 q :=
      mul_le_mul_of_nonneg_left hinit (pow_nonneg h1 K)
    exact hbnd.trans (h3.trans hgeo)
  have hmeas : Measurable (fun ξ : ℕ → Point q.d × q.Ω => f (X ξ) - f xstar) :=
    (hf.comp hrunmeas).sub measurable_const
  have hfi : Integrable (fun ξ : ℕ → Point q.d × q.Ω => f (X ξ) - f xstar)
      (P : Measure (ℕ → Point q.d × q.Ω)) := by
    refine (hgapInt.add (integrable_const (q.L * q.h ^ 2 * (q.d : ℝ)))).mono'
      ((hf.comp hrunmeas).sub measurable_const).aestronglyMeasurable ?_
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
      LongTails.Setups.ZerothOrderSmoothingBatchedAcceleration.spec.successful q f output1 μ := by
    subst hEq
    exact hc
  have hpt : ∀ seed : Unit × (ℕ → Point q.d × q.Ω),
      execute OT
        (agDescent (m := agM (width q)) (fun _ => hm) (anch q) (mmt q) (1 / q.L) q.h q.x0)
        (budget q) seed.1 seed.2 = X seed.2 := by
    intro seed
    cases seed with
    | mk s xi =>
        have h1 : execute OT
              (agDescent (m := agM (width q)) (fun _ => hm) (anch q) (mmt q) (1 / q.L) q.h q.x0)
              (budget q) () xi
            = execute OT
                (agDescent (m := agM (width q)) (fun _ => hm) (anch q) (mmt q) (1 / q.L) q.h q.x0)
                (fun _ => o.off K) () xi :=
          congrArg
            (fun b : Fin 1 → ℕ => execute OT
              (agDescent (m := agM (width q)) (fun _ => hm) (anch q) (mmt q) (1 / q.L) q.h q.x0)
              b () xi) hbud
        exact h1.trans (congrFun hXexec.symm xi)
  have hfunEq : (fun seed : Unit × (ℕ → Point q.d × q.Ω) =>
        execute OT
          (agDescent (m := agM (width q)) (fun _ => hm) (anch q) (mmt q) (1 / q.L) q.h q.x0)
          (budget q) seed.1 seed.2)
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
  · exact hrunmeas.comp measurable_snd
  · exact hfi2
  · exact (le_of_eq hintEq).trans hgapFinal

end LongTails.Theorems.GradedAnchoredAccelerationStrongGrowth

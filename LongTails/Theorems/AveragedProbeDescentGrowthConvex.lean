import LongTails.Setups.ZerothOrderSmoothingGrowthConvex
import LongTails.Proofs.GrowthProbeExecution

set_option maxHeartbeats 4000000

/-!
Averaged mirrored-pair probe descent for multidimensional stochastic *convex* minimization in the
randomized-smoothing probe model whose probe noise is proportional to the current smoothed gap:

    ∫ ‖probe - half gradient‖² dμ ≤ ρ² * (fh x - fh xh).

One mirrored pair per round moves against the smoothed gradient, and the output is the uniform
average of the visited iterates, so Jensen's inequality turns telescoping distance descent into an
accuracy statement for a merely convex objective. With step `η = 1 / (4 (L + ρ²))` the squared
distance to the surrogate minimizer plus `η` times the accumulated smoothed gaps is a
supermartingale, so the accumulated gaps are at most `‖x0 - xh‖² / η`, and

    2 * max 1 ⌈8 (L + ρ²) R² / ε⌉

probes give expected accuracy `ε`, i.e. `Θ((L + ρ²) R² / ε)` zeroth-order probes, free of the
dimension except through the bandwidth admissibility `2 L h² d ≤ ε`.

Assumptions, honestly stated. This budget is *not* comparable with the repo's earlier convex
zeroth-order budgets, which bound the probe variance by a fixed `σ²` and reach
`Θ(d² R² σ² / ε³)`; here the variance bound is stronger (it vanishes at the surrogate minimizer)
while the curvature assumption is weaker (convex, no strong convexity, so the earlier
`Θ(log (1 / ε))` strong-growth result does not apply). No lower bound is claimed: the exponent of
`1 / ε` here is an upper bound for this algorithm and this model, and the tuning is not proved
optimal.
-/

namespace LongTails.Theorems.AveragedProbeDescentGrowthConvex

open MeasureTheory ProbabilityTheory
open LongTails.Setups
open LongTails.Setups.ZerothOrderSmoothAndConvex
open LongTails.Setups.ZerothOrderSmoothingGrowthConvex
open scoped BigOperators RealInnerProductSpace
open OracleTemplate SecantPolyak SecantDescent
open OracleTemplate.SecantPolyak.GrowthConvex
open OracleTemplate.SecantPolyak.Interpolated (ipM ipOffsets)
open OracleTemplate.SecantPolyak.Scheduled OracleTemplate.SecantPolyak.DirectionSampled

/-- Parameters of the gap-proportional randomized-smoothing probe model. -/
abbrev Par := LongTails.Setups.ZerothOrderSmoothingGrowthConvex.Params

/-- Step size: the descent-plus-noise cap `4 η (L + ρ²) ≤ 1` solved with equality. -/
noncomputable def eta (q : Par) : ℝ := 1 / (4 * (q.L + q.ρ ^ 2))

/-- Rounds of averaged probe descent: linear in `1 / ε`, independent of the dimension. -/
noncomputable def rounds (q : Par) : ℕ := max 1 ⌈8 * (q.L + q.ρ ^ 2) * q.R ^ 2 / q.ε⌉₊

/-- Oracle budget: exactly two one-sided probes per round. -/
noncomputable def budget :
    (let S := LongTails.Setups.ZerothOrderSmoothingGrowthConvex.spec;
      S.Params → Fin S.numOracles → ℕ) :=
  fun q _ => 2 * rounds q

/-- The proved budget is `Θ((L + ρ²) R² / ε)` probes: two probes per round and a round count linear
in `1 / ε`, with no dependence on the dimension except through the bandwidth admissibility. -/
lemma budget_le (q : Par) (i : Fin 1) (hL : 0 < q.L) (hε : 0 < q.ε) :
    (budget q i : ℝ) ≤ 2 + 16 * (q.L + q.ρ ^ 2) * q.R ^ 2 / q.ε := by
  set x : ℝ := 8 * (q.L + q.ρ ^ 2) * q.R ^ 2 / q.ε with hx
  have hx0 : 0 ≤ x := by
    rw [hx]
    positivity
  have hmax : ((max 1 ⌈x⌉₊ : ℕ) : ℝ) ≤ x + 1 := by
    have key : max (1 : ℝ) (⌈x⌉₊ : ℝ) ≤ x + 1 :=
      max_le_iff.mpr ⟨le_add_of_nonneg_left hx0, (Nat.ceil_lt_add_one hx0).le⟩
    simpa [Nat.cast_max] using key
  calc (budget q i : ℝ)
      = 2 * max 1 ⌈x⌉₊ := by
        simp only [budget, rounds, ← hx]
        norm_cast
    _ ≤ 2 * (x + 1) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 2)
        show ((max 1 ⌈x⌉₊ : ℕ) : ℝ) ≤ x + 1
        exact hmax
    _ = 2 + 16 * (q.L + q.ρ ^ 2) * q.R ^ 2 / q.ε := by
        rw [hx, mul_add]
        field_simp
        ring

/-- Averaged mirrored-pair probe descent reaches expected accuracy `ε` with `2 * rounds q`
zeroth-order probes. -/
theorem result :
    Convergence LongTails.Setups.ZerothOrderSmoothingGrowthConvex.spec budget := by
  classical
  refine ⟨fun q => gpDescent (eta q) q.h q.x0, ?_, fun _ _ => trivial⟩
  intro q hq f O ho
  rcases hq with ⟨_hd, hL, _hR, hε, _hh0, _hrho, hband⟩
  obtain ⟨g, p, P, hind, hmarg, hO, hgm, hf, hxstar, hfh⟩ := ho
  obtain ⟨xstar, hmin, _hdist0⟩ := hxstar
  obtain ⟨fh, xh, hcvx, hgr, hlip, hminh, hR_xh, hup, hdown, hint, hmean, hvar2, hvar⟩ := hfh
  subst hO
  set B : ℝ := q.L * q.h ^ 2 * (q.d : ℝ)
  have hε2 : 0 < q.ε / 2 := by linarith
  have hsq : 0 ≤ q.ρ ^ 2 := sq_nonneg _
  have hLp : 0 < q.L + q.ρ ^ 2 := by linarith
  have hEtaP : 0 < eta q :=
    div_pos (by norm_num : (0 : ℝ) < 1) (mul_pos (by norm_num : (0 : ℝ) < 4) hLp)
  have hEta0 : 0 ≤ eta q := le_of_lt hEtaP
  have hcap : 4 * eta q * (q.L + q.ρ ^ 2) ≤ 1 := by
    have h1 : 4 * eta q * (q.L + q.ρ ^ 2) = 1 := by
      show 4 * (1 / (4 * (q.L + q.ρ ^ 2))) * (q.L + q.ρ ^ 2) = 1
      field_simp
    exact h1.le
  have hWp : IsProbabilityMeasure (probe p : Measure (Point q.d × q.Ω)) := by
    have h1 : Measure.map (fun u : ℕ → Point q.d × q.Ω => u 0) (P : Measure (ℕ → Point q.d × q.Ω))
        = (probe p : Measure (Point q.d × q.Ω)) := hmarg 0
    have h2 : IsProbabilityMeasure
        (Measure.map (fun u : ℕ → Point q.d × q.Ω => u 0) (P : Measure (ℕ → Point q.d × q.Ω))) :=
      by infer_instance
    exact h1 ▸ h2
  have hfhm : Continuous fh := continuous_iff_continuousAt.mpr fun x =>
    (hgr x).hasFDerivAt.continuousAt
  have hM : GPHyp g fh xh q.L q.ρ (eta q) q.h (probe p : Measure (Point q.d × q.Ω)) :=
    { hL := hL
      eta0 := hEta0
      cap := hcap
      convex := hcvx
      grad := hgr
      lip := hlip
      min := fun x => hminh (Set.mem_univ x)
      gmeas := hgm
      fmeas := hfhm.measurable
      slotInt := fun x s => hint x s
      varInt := fun x s => hvar2 x s
      mean := fun x s => hmean x s
      var := fun x s => hvar x s }
  set K : ℕ := rounds q
  set o : Offsets 1 ipM := ipOffsets
  have hoff : ∀ k : ℕ, o.off k = 2 * k := fun _ => rfl
  have hK1 : 1 ≤ K := by
    show 1 ≤ max 1 ⌈8 * (q.L + q.ρ ^ 2) * q.R ^ 2 / q.ε⌉₊
    exact le_max_left _ _
  have hK : (K : ℝ) ≥ 8 * (q.L + q.ρ ^ 2) * q.R ^ 2 / q.ε :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_max_right _ _)
  have hdist : ‖q.x0 - xh‖ ^ 2 ≤ q.R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hR_xh 2
  have hprod : 8 * (q.L + q.ρ ^ 2) * q.R ^ 2 ≤ (K : ℝ) * q.ε := (div_le_iff₀ hε).mp hK
  have hk : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr (Nat.one_pos.trans_le hK1)
  have hstep : ‖q.x0 - xh‖ ^ 2 / (eta q * (K : ℝ)) ≤ q.ε / 2 := by
    have h1 : ‖q.x0 - xh‖ ^ 2 / (eta q * (K : ℝ)) ≤ q.R ^ 2 / (eta q * (K : ℝ)) := by
      gcongr
    have h2 : q.R ^ 2 / (eta q * (K : ℝ)) = 4 * (q.L + q.ρ ^ 2) * q.R ^ 2 / (K : ℝ) := by
      show q.R ^ 2 / ((1 / (4 * (q.L + q.ρ ^ 2))) * (K : ℝ)) = _
      field_simp
    have h3 : 4 * (q.L + q.ρ ^ 2) * q.R ^ 2 / (K : ℝ) ≤ q.ε / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)]
      nlinarith
    calc ‖q.x0 - xh‖ ^ 2 / (eta q * (K : ℝ)) ≤ q.R ^ 2 / (eta q * (K : ℝ)) := h1
      _ = 4 * (q.L + q.ρ ^ 2) * q.R ^ 2 / (K : ℝ) := h2
      _ ≤ q.ε / 2 := h3
  obtain ⟨hInt, hbnd⟩ :=
    gp_exec_accuracy (d := q.d) (hW := hWp) (g := g) (fh := fh) (W := probe p)
    (L := q.L) (ρ := q.ρ) (η := eta q) (h := q.h) (x0 := q.x0) (xh := xh) (K := K)
    hM (by exact_mod_cast hK1) hEtaP P hind (fun k => hmarg k) o
  have hbud : budget q = fun _ : Fin 1 => o.off K := by
    refine funext fun _ => ?_
    show 2 * K = o.off K
    rw [hoff]
  set X : (ℕ → Point q.d × q.Ω) → Point q.d := fun ξ =>
    (1 / max 1 (K : ℝ)) •
      (runSched (gpStep g fh xh (eta q) q.h) 0 K (q.x0, (0 : Point q.d), (0 : ℝ))
        (fun k : Fin K => fun t : secantSpace 1 1 =>
          ξ (schedIndex (d := 1) (M := 1) ipM o K ⟨k, t⟩))).2.1
  have hstepM : ∀ k : ℕ, Measurable (fun s :
      GPState q.d × (secantSpace 1 1 → Point q.d × q.Ω) =>
        gpStep g fh xh (eta q) q.h k s.1 s.2) :=
    fun k => measurable_gpStep (hg := hgm) (hfm := hfhm.measurable) xh (eta q) q.h k
  have hlift : Measurable (fun ξ : ℕ → Point q.d × q.Ω => fun k : Fin K =>
      fun t : secantSpace 1 1 => ξ (schedIndex (d := 1) (M := 1) ipM o K ⟨k, t⟩)) := by
    fun_prop
  have hpair : Measurable (fun ξ : ℕ → Point q.d × q.Ω =>
      ((q.x0, (0 : Point q.d), (0 : ℝ)), fun k : Fin K => fun t : secantSpace 1 1 =>
        ξ (schedIndex (d := 1) (M := 1) ipM o K ⟨k, t⟩))) :=
    measurable_const.prodMk hlift
  have hrun : Measurable fun ξ : ℕ → Point q.d × q.Ω =>
      runSched (gpStep g fh xh (eta q) q.h) 0 K (q.x0, (0 : Point q.d), (0 : ℝ))
        (fun k : Fin K => fun t : secantSpace 1 1 =>
          ξ (schedIndex (d := 1) (M := 1) ipM o K ⟨k, t⟩)) :=
    (measurable_runSched hstepM K 0).comp hpair
  have hXm : Measurable X :=
    Measurable.const_smul (c := (1 / max 1 (K : ℝ))) hrun.snd.fst
  have hXexec : X = fun ξ : ℕ → Point q.d × q.Ω =>
      execute (dirOracle q.h g P) (gpDescent (eta q) q.h q.x0) (fun _ => o.off K) () ξ := by
    funext ξ
    exact (gp_execute (eta q) q.h q.x0 fh xh o g ξ P K).symm
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
    exact hbnd.trans hstep
  have hmeas : Measurable (fun ξ : ℕ → Point q.d × q.Ω => f (X ξ) - f xstar) :=
    (hf.comp hXm).sub measurable_const
  have hfi : Integrable (fun ξ : ℕ → Point q.d × q.Ω => f (X ξ) - f xstar)
      (P : Measure (ℕ → Point q.d × q.Ω)) := by
    refine (hgapInt.add (integrable_const B)).mono' hmeas.aestronglyMeasurable ?_
    refine ae_of_all _ fun ξ => show ‖f (X ξ) - f xstar‖ ≤ (fh (X ξ) - fh xh) + B from ?_
    have h0 : 0 ≤ f (X ξ) - f xstar := sub_nonneg.mpr (hmin (Set.mem_univ _))
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact hpoint (X ξ)
  have hgapFinal : (∫ ξ : ℕ → Point q.d × q.Ω, f (X ξ) - f xstar
        ∂(P : Measure (ℕ → Point q.d × q.Ω))) ≤ q.ε := by
    refine le_trans
      (integral_mono hfi (hgapInt.add (integrable_const B)) (fun ξ => hpoint (X ξ))) ?_
    have h1 : (∫ ξ : ℕ → Point q.d × q.Ω,
          (fh (X ξ) - fh xh) + B ∂(P : Measure (ℕ → Point q.d × q.Ω)))
        = (∫ ξ : ℕ → Point q.d × q.Ω, fh (X ξ) - fh xh
            ∂(P : Measure (ℕ → Point q.d × q.Ω))) + B := by
      rw [integral_add hgapInt (integrable_const B), integral_const]
      simp
    refine (le_of_eq h1).trans ?_
    linarith
  set OT : Oracle (Point q.d × Bool) (ℝ × Point q.d) := dirOracle q.h g P
  have htransport (f : Point q.d → ℝ) (output1 output2 : Unit × (ℕ → Point q.d × q.Ω) → Point q.d)
      (μ : ProbabilityMeasure (Unit × (ℕ → Point q.d × q.Ω))) (hEq : output1 = output2)
      (hc : LongTails.Setups.ZerothOrderSmoothingGrowthConvex.spec.successful q f output2 μ) :
      LongTails.Setups.ZerothOrderSmoothingGrowthConvex.spec.successful q f output1 μ := by
    subst hEq
    exact hc
  have hpt : ∀ seed : Unit × (ℕ → Point q.d × q.Ω),
      execute OT (gpDescent (eta q) q.h q.x0) (budget q) seed.1 seed.2 = X seed.2 := by
    intro seed
    cases seed with
    | mk s xi =>
        have h1 : execute OT (gpDescent (eta q) q.h q.x0) (budget q) () xi
            = execute OT (gpDescent (eta q) q.h q.x0) (fun _ => o.off K) () xi :=
          congrArg (fun b : Fin 1 → ℕ => execute OT (gpDescent (eta q) q.h q.x0) b () xi) hbud
        exact h1.trans (congrFun hXexec.symm xi)
  have hfunEq : (fun seed : Unit × (ℕ → Point q.d × q.Ω) =>
        execute OT (gpDescent (eta q) q.h q.x0) (budget q) seed.1 seed.2)
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
  · exact hXm.comp measurable_snd
  · exact hfi2
  · exact (le_of_eq hintEq).trans hgapFinal

end LongTails.Theorems.AveragedProbeDescentGrowthConvex

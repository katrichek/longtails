import LongTails.Setups.ZerothOrderSmoothingGrowthConvex
import LongTails.Proofs.DampedAnchoredConvexExecution

set_option maxHeartbeats 4000000

namespace LongTails.Theorems.DampedAnchoredConvexGrowth

open MeasureTheory ProbabilityTheory
open LongTails.Setups
open LongTails.Setups.ZerothOrderSmoothAndConvex
open LongTails.Setups.ZerothOrderSmoothingGrowthConvex
open scoped BigOperators RealInnerProductSpace
open OracleTemplate SecantPolyak SecantDescent
open OracleTemplate.SecantPolyak.AnchoredPair
open OracleTemplate.SecantPolyak.AnchoredConvexPair
open OracleTemplate.SecantPolyak.Scheduled OracleTemplate.SecantPolyak.DirectionSampled

noncomputable def budget : (let S := LongTails.Setups.ZerothOrderSmoothingGrowthConvex.spec; S.Params → Fin S.numOracles → ℕ) :=
  fun q _ => 2 * max 1 ⌈Real.sqrt (16 * q.L * q.R ^ 2 / q.ε) + 16 * q.ρ ^ 2 * q.R ^ 2 / q.ε⌉₊

theorem result :
    Convergence LongTails.Setups.ZerothOrderSmoothingGrowthConvex.spec budget := by
  classical
  refine ⟨fun q =>
    let K : ℕ := max 1 ⌈Real.sqrt (16 * q.L * q.R ^ 2 / q.ε) + 16 * q.ρ ^ 2 * q.R ^ 2 / q.ε⌉₊
    let η : ℝ := 1 / (q.L + q.ρ ^ 2 * ((K : ℝ) + 1))
    dacDescent η q.h q.x0, ?_, fun _ _ => trivial⟩
  intro q hq f O ho
  rcases hq with ⟨_hd, hL, _hR, hε, _hh0, _hrho, hband⟩
  obtain ⟨g, p, P, hind, hmarg, hO, hgm, hf, hxstar, hfh⟩ := ho
  obtain ⟨xstar, hmin, _hdist0⟩ := hxstar
  obtain ⟨fh, xh, hcvx, hgr, hlip, hminh, hR_xh, hup, hdown, hint, hmean, hvar2, hvar⟩ := hfh
  subst hO
  set K : ℕ := max 1 ⌈Real.sqrt (16 * q.L * q.R ^ 2 / q.ε) + 16 * q.ρ ^ 2 * q.R ^ 2 / q.ε⌉₊
  set η : ℝ := 1 / (q.L + q.ρ ^ 2 * ((K : ℝ) + 1))
  set B : ℝ := q.L * q.h ^ 2 * (q.d : ℝ)
  have hK1 : 1 ≤ K := le_max_left _ _
  have hKpos : 0 < K := Nat.one_pos.trans_le hK1
  have hdenom : 0 < q.L + q.ρ ^ 2 * ((K : ℝ) + 1) := by positivity
  have hη : 0 < η := one_div_pos.mpr hdenom
  have hLη : q.L * η ≤ 1 := by
    show q.L * (1 / (q.L + q.ρ ^ 2 * ((K : ℝ) + 1))) ≤ 1
    rw [mul_one_div, div_le_one hdenom]
    have : 0 ≤ q.ρ ^ 2 * ((K : ℝ) + 1) := by positivity
    linarith
  have hρη : q.ρ ^ 2 * ((K : ℝ) + 1) * η ≤ 1 := by
    show q.ρ ^ 2 * ((K : ℝ) + 1) * (1 / (q.L + q.ρ ^ 2 * ((K : ℝ) + 1))) ≤ 1
    rw [mul_one_div, div_le_one hdenom]
    linarith
  have hWp : IsProbabilityMeasure (probe p : Measure (Point q.d × q.Ω)) := by
    have h1 : Measure.map (fun u : ℕ → Point q.d × q.Ω => u 0) (P : Measure (ℕ → Point q.d × q.Ω))
        = (probe p : Measure (Point q.d × q.Ω)) := hmarg 0
    have h2 : IsProbabilityMeasure
        (Measure.map (fun u : ℕ → Point q.d × q.Ω => u 0) (P : Measure (ℕ → Point q.d × q.Ω))) :=
      by infer_instance
    exact h1 ▸ h2
  set o : Offsets 1 apM := apOffsets
  have hoff : ∀ k : ℕ, o.off k = 2 * k := fun _ => rfl
  have habK : Real.sqrt (16 * q.L * q.R ^ 2 / q.ε) + 16 * q.ρ ^ 2 * q.R ^ 2 / q.ε ≤ (K : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_max_right 1 _)
  have hstep : 8 * ‖q.x0 - xh‖ ^ 2 / (η * dacWeight K) ≤ q.ε / 2 :=
    dac_rate_bound hL hε hR_xh hK1 habK
  obtain ⟨hInt, hbnd⟩ :=
    dac_exec_accuracy (d := q.d) (g := g) (fh := fh) (W := probe p)
      (L := q.L) (η := η) (h := q.h) (ρ := q.ρ) (x0 := q.x0) (xh := xh) (K := K)
      hKpos hL hη hLη hρη hgm hcvx hgr hlip hminh hint hmean hvar2 hvar
      P hind (fun k => hmarg k) o
  have hbud : budget q = fun _ : Fin 1 => o.off K := by
    refine funext fun _ => ?_
    show 2 * K = o.off K
    rw [hoff]
  set X : (ℕ → Point q.d × q.Ω) → Point q.d := fun ξ =>
    (runSched (dacStepSched η g q.h) 0 K (q.x0, q.x0)
      (fun k : Fin K => fun t : secantSpace 1 1 =>
        ξ (schedIndex (d := 1) (M := 1) apM o K ⟨k, t⟩))).1
  have hstepM : ∀ k : ℕ, Measurable (fun s :
      (Point q.d × Point q.d) × (secantSpace 1 1 → Point q.d × q.Ω) =>
        dacStepSched η g q.h k s.1 s.2) :=
    fun k => measurable_dacStepSched_joint hgm η q.h k
  have hlift : Measurable (fun ξ : ℕ → Point q.d × q.Ω => fun k : Fin K =>
      fun t : secantSpace 1 1 => ξ (schedIndex (d := 1) (M := 1) apM o K ⟨k, t⟩)) := by
    fun_prop
  have hpair : Measurable (fun ξ : ℕ → Point q.d × q.Ω =>
      ((q.x0, q.x0), fun k : Fin K => fun t : secantSpace 1 1 =>
        ξ (schedIndex (d := 1) (M := 1) apM o K ⟨k, t⟩))) :=
    measurable_const.prodMk hlift
  have hrun : Measurable fun ξ : ℕ → Point q.d × q.Ω =>
      runSched (dacStepSched η g q.h) 0 K (q.x0, q.x0)
        (fun k : Fin K => fun t : secantSpace 1 1 =>
          ξ (schedIndex (d := 1) (M := 1) apM o K ⟨k, t⟩)) :=
    (measurable_runSched hstepM K 0).comp hpair
  have hXm : Measurable X := measurable_fst.comp hrun
  have hXexec : X = fun ξ : ℕ → Point q.d × q.Ω =>
      execute (dirOracle q.h g P) (dacDescent η q.h q.x0) (fun _ => o.off K) () ξ := by
    funext ξ
    exact (dac_execute η q.h q.x0 o g ξ P K).symm
  have hB : B ≤ q.ε / 2 := by
    show q.L * q.h ^ 2 * (q.d : ℝ) ≤ q.ε / 2
    linarith [hband]
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
      execute OT (dacDescent η q.h q.x0) (budget q) seed.1 seed.2 = X seed.2 := by
    intro seed
    cases seed with
    | mk s xi =>
        have h1 : execute OT (dacDescent η q.h q.x0) (budget q) () xi
            = execute OT (dacDescent η q.h q.x0) (fun _ => o.off K) () xi :=
          congrArg (fun b : Fin 1 → ℕ => execute OT (dacDescent η q.h q.x0) b () xi) hbud
        exact h1.trans (congrFun hXexec.symm xi)
  have hfunEq : (fun seed : Unit × (ℕ → Point q.d × q.Ω) =>
        execute OT (dacDescent η q.h q.x0) (budget q) seed.1 seed.2)
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

end LongTails.Theorems.DampedAnchoredConvexGrowth

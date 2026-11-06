import LongTails.Proofs.CenteredMomentumStream

set_option maxHeartbeats 1000000

namespace OracleTemplate.SecantPolyak.DirectionSampled

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
open OracleTemplate
open InexactGradient SecantPolyak.Accelerated SecantPolyak.Centered
open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {d : ℕ}

lemma dir_one_step {f : Point d → ℝ} {L μ θ : ℝ} {xstar : Point d}
    (hL : 0 < L) (hμ : 0 < μ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hθL : 16 * L * θ ^ 2 ≤ μ)
    (hgr : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hsc : ∀ x y, f x + ⟪gradient f x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (hmin : IsMinOn f Set.univ xstar)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (s : Point d × Point d) (V : Ω → Point d)
    (hV : Integrable V P)
    (hmean : (∫ ω, V ω ∂P) = gradient f (query θ s))
    (hdev : Integrable (fun ω => ‖V ω - gradient f (query θ s)‖ ^ 2) P)
    (hmeas : AEStronglyMeasurable (fun ω => potential f μ xstar (step L μ θ s (V ω))) P) :
    Integrable (fun ω => potential f μ xstar (step L μ θ s (V ω))) P ∧
      (∫ ω, potential f μ xstar (step L μ θ s (V ω)) ∂P) ≤
        (1 - θ / 2) * potential f μ xstar s
          + (1 / (2 * L) + θ ^ 2 / μ) * ∫ ω, ‖V ω - gradient f (query θ s)‖ ^ 2 ∂P := by
  classical
  have hminf : ∀ x, f xstar ≤ f x := fun x => hmin (Set.mem_univ x)
  have hVnonneg : ∀ t : Point d × Point d, 0 ≤ potential f μ xstar t := by
    intro t
    show 0 ≤ f t.1 - f xstar + μ / 4 * ‖t.2 - xstar‖ ^ 2
    exact add_nonneg (sub_nonneg.mpr (hminf t.1)) (mul_nonneg (by positivity) (sq_nonneg _))
  set g0 : Point d := gradient f (query θ s) with hg0def
  set c : Point d := -(1 / L) • gradient f (query θ s - (1 / L) • g0)
      - θ • ((1 - θ) • s.2 + θ • query θ s - (2 * θ / μ) • g0 - xstar) with hcdef
  set xi : Ω → Point d := fun ω => V ω - g0 with hxidef
  set cv : ℝ := 1 / (2 * L) + θ ^ 2 / μ with hcvdef
  have hcv0 : 0 ≤ cv := by positivity
  have hxii : Integrable xi P := hV.sub (integrable_const g0)
  have hxi0 : (∫ ω, xi ω ∂P) = 0 := by
    show (∫ ω, V ω - g0 ∂P) = 0
    rw [integral_sub hV (integrable_const g0), hmean, hg0def, integral_const,
      probReal_univ, one_smul, sub_self]
  set Lc : Point d →L[ℝ] ℝ := InnerProductSpace.toDual ℝ (Point d) c with hLcdef
  have hlin0 : (∫ ω, Lc (xi ω) ∂P) = 0 := by
    rw [Lc.integral_comp_comm hxii, hxi0, map_zero]
  have hbase : potential f μ xstar (step L μ θ s g0) ≤ (1 - θ / 2) * potential f μ xstar s := by
    have hb := accel_potential_step (f := f) (L := L) (μ := μ) (θ := θ) (xstar := xstar)
      hL hμ hθ0 hθ1 hθL hgr hlip hsc hmin s g0
    simpa [hg0def] using hb
  have hpath : ∀ ω, potential f μ xstar (step L μ θ s (V ω))
      ≤ (1 - θ / 2) * potential f μ xstar s + (Lc (xi ω) + cv * ‖xi ω‖ ^ 2) := by
    intro ω
    have hVω : V ω = g0 + xi ω := by
      show V ω = g0 + (V ω - g0)
      rw [add_comm, sub_add_cancel]
    have hp := potential_step_perturb (d := d) (f := f) (L := L) (μ := μ) (xstar := xstar)
      hL hμ hθ0 hgr hlip s g0 (xi ω)
    rw [hVω]
    have hcval : (⟪-(1 / L) • gradient f (query θ s - (1 / L) • g0)
        - θ • ((1 - θ) • s.2 + θ • query θ s - (2 * θ / μ) • g0 - xstar), xi ω⟫) = Lc (xi ω) := by
      rw [hLcdef, hcdef]
      rfl
    rw [hcval] at hp
    have hcvval : (1 / (2 * L) + θ ^ 2 / μ) * ‖xi ω‖ ^ 2 = cv * ‖xi ω‖ ^ 2 := by rw [hcvdef]
    rw [hcvval] at hp
    linarith
  have h1 : Integrable (fun ω => Lc (xi ω)) P := Lc.integrable_comp hxii
  have h2 : Integrable (fun ω => cv * ‖xi ω‖ ^ 2) P := hdev.const_mul cv
  have hsum : Integrable (fun ω => Lc (xi ω) + cv * ‖xi ω‖ ^ 2) P := h1.add h2
  have hGi : Integrable (fun ω => (1 - θ / 2) * potential f μ xstar s
      + (Lc (xi ω) + cv * ‖xi ω‖ ^ 2)) P := (integrable_const _).add hsum
  have hFi : Integrable (fun ω => potential f μ xstar (step L μ θ s (V ω))) P :=
    hGi.mono' hmeas (ae_of_all _ fun ω => by
      have h0 : 0 ≤ potential f μ xstar (step L μ θ s (V ω)) := hVnonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact hpath ω)
  refine ⟨hFi, ?_⟩
  have hmono := integral_mono hFi hGi hpath
  have hlin : (∫ ω, (Lc (xi ω) + cv * ‖xi ω‖ ^ 2) ∂P) = cv * ∫ ω, ‖xi ω‖ ^ 2 ∂P := by
    rw [integral_add h1 h2, hlin0, zero_add, integral_const_mul]
  have hconst : (∫ ω, ((1 - θ / 2) * potential f μ xstar s
      + (Lc (xi ω) + cv * ‖xi ω‖ ^ 2)) ∂P)
      = (1 - θ / 2) * potential f μ xstar s + cv * ∫ ω, ‖xi ω‖ ^ 2 ∂P := by
    rw [integral_add (integrable_const ((1 - θ / 2) * potential f μ xstar s)) hsum, hlin,
      integral_const, probReal_univ, one_smul]
  rw [hconst] at hmono
  exact hmono

end OracleTemplate.SecantPolyak.DirectionSampled
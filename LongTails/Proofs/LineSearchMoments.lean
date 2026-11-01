import LongTails.Proofs.LineSearchExecution
import Mathlib.Probability.Independence.Integration

open MeasureTheory ProbabilityTheory

namespace OracleTemplate.LineSearch

variable {Ω : Type} [MeasurableSpace Ω]

lemma integrable_eval_pi {p : Measure Ω} [IsProbabilityMeasure p] {m : ℕ}
    (φ : Ω → ℝ) (hint : Integrable φ p) (i : Fin m) :
    Integrable (fun β : Fin m → Ω => φ (β i)) (Measure.pi fun _ : Fin m => p) :=
  integrable_comp_eval hint

lemma integral_eval_pi {p : Measure Ω} [IsProbabilityMeasure p] {m : ℕ}
    (φ : Ω → ℝ) (hint : Integrable φ p) (i : Fin m) :
    ∫ β : Fin m → Ω, φ (β i) ∂(Measure.pi fun _ : Fin m => p) = ∫ z, φ z ∂p :=
  integral_comp_eval hint.aestronglyMeasurable

lemma integral_sum_eval_pi {p : Measure Ω} [IsProbabilityMeasure p] {m : ℕ}
    (φ : Ω → ℝ) (hint : Integrable φ p) :
    ∫ β : Fin m → Ω, (∑ i : Fin m, φ (β i)) ∂(Measure.pi fun _ : Fin m => p)
      = (m : ℝ) * ∫ z, φ z ∂p := by
  rw [integral_finset_sum _ (fun i _ => integrable_eval_pi φ hint i)]
  simp only [integral_eval_pi φ hint]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma integral_eval_mul_eval_pi {p : Measure Ω} [IsProbabilityMeasure p] {m : ℕ}
    {k l : Fin m} (hkl : k ≠ l) (φ ψ : Ω → ℝ)
    (hφ : Measurable φ) (hψ : Measurable ψ) :
    ∫ β : Fin m → Ω, φ (β k) * ψ (β l) ∂(Measure.pi fun _ : Fin m => p)
      = (∫ z, φ z ∂p) * (∫ z, ψ z ∂p) := by
  have hpi : iIndepFun (fun (i : Fin m) (β : Fin m → Ω) => β i)
      (Measure.pi fun _ : Fin m => p) :=
    iIndepFun_pi (μ := fun _ : Fin m => p) (X := fun _ : Fin m => id)
      (fun _ => aemeasurable_id)
  have hind : IndepFun (fun β : Fin m → Ω => φ (β k)) (fun β : Fin m → Ω => ψ (β l))
      (Measure.pi fun _ : Fin m => p) :=
    (hpi.indepFun hkl).comp hφ hψ
  have h1 : AEStronglyMeasurable (fun β : Fin m → Ω => φ (β k))
      (Measure.pi fun _ : Fin m => p) :=
    (hφ.comp (measurable_pi_apply k)).aestronglyMeasurable
  have h2 : AEStronglyMeasurable (fun β : Fin m → Ω => ψ (β l))
      (Measure.pi fun _ : Fin m => p) :=
    (hψ.comp (measurable_pi_apply l)).aestronglyMeasurable
  have hstep := hind.integral_mul_eq_mul_integral h1 h2
  simp only [Pi.mul_apply] at hstep
  rw [hstep, integral_comp_eval (μ := fun _ : Fin m => p) hφ.aestronglyMeasurable,
    integral_comp_eval (μ := fun _ : Fin m => p) hψ.aestronglyMeasurable]

end OracleTemplate.LineSearch

namespace OracleTemplate.LineSearch

open MeasureTheory ProbabilityTheory

lemma block_center_sq_le {Ω : Type} [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]
    {m : ℕ} (φ : Ω → ℝ) (c σ : ℝ) (hφm : Measurable φ)
    (hint : Integrable φ p) (hl2 : Integrable (fun z => (φ z - c) ^ 2) p)
    (hmean : ∫ z, φ z ∂p = c) (hvar : ∫ z, (φ z - c) ^ 2 ∂p ≤ σ ^ 2) :
    Integrable (fun β : Fin m → Ω => (∑ k : Fin m, (φ (β k) - c)) ^ 2)
        (Measure.pi fun _ : Fin m => p) ∧
      ∫ β : Fin m → Ω, (∑ k : Fin m, (φ (β k) - c)) ^ 2 ∂(Measure.pi fun _ : Fin m => p)
        ≤ (m : ℝ) * σ ^ 2 := by
  let ν : Measure (Fin m → Ω) := Measure.pi fun _ : Fin m => p
  haveI : IsProbabilityMeasure ν := inferInstanceAs (IsProbabilityMeasure (Measure.pi _))
  let X : Fin m → (Fin m → Ω) → ℝ := fun k β => φ (β k) - c
  have hXm : ∀ k, Measurable (X k) := fun k => (hφm.comp (measurable_pi_apply k)).sub_const c
  have hmem : ∀ k, MemLp (X k) 2 ν := fun k =>
    MemLp.comp_measurePreserving (g := fun z : Ω => φ z - c)
      ((memLp_two_iff_integrable_sq_norm ((hφm.sub_const c).aestronglyMeasurable)).mpr
        (by simpa only [Real.norm_eq_abs, sq_abs] using hl2))
      (measurePreserving_eval (μ := fun _ : Fin m => p) k)
  have hInt : ∀ k, Integrable (X k) ν := fun k => (hmem k).integrable (by norm_num)
  have hzero_p : ∫ z : Ω, (φ z - c) ∂p = 0 := by
    rw [integral_sub hint (integrable_const c), hmean]
    simp
  have hprod : ∀ k l, Integrable (fun β => X k β * X l β) ν := fun k l =>
    memLp_one_iff_integrable.mp ((hmem k).mul (hmem l))
  have hdiag : ∀ k, ∫ β, X k β * X k β ∂ν = ∫ z, (φ z - c) ^ 2 ∂p := by
    intro k
    have h1 : ∫ β : Fin m → Ω, (φ (β k) - c) * (φ (β k) - c) ∂ν
        = ∫ z : Ω, (φ z - c) * (φ z - c) ∂p :=
      integral_comp_eval (μ := fun _ : Fin m => p)
        ((hφm.sub_const c).mul (hφm.sub_const c)).aestronglyMeasurable
    simpa only [X, pow_two] using h1
  have hoff : ∀ k l, k ≠ l → ∫ β, X k β * X l β ∂ν = 0 := by
    intro k l hkl
    rw [integral_eval_mul_eval_pi hkl (fun z => φ z - c) (fun z => φ z - c)
      (hφm.sub_const c) (hφm.sub_const c), hzero_p]
    ring
  have hpt : ∀ β : Fin m → Ω, (∑ k : Fin m, X k β) ^ 2 = ∑ k, ∑ l, X k β * X l β := by
    intro β
    rw [pow_two, Finset.sum_mul_sum]
  have hsq : ∫ β, (∑ k : Fin m, X k β) ^ 2 ∂ν
      = ∑ k : Fin m, ∑ l : Fin m, ∫ β, X k β * X l β ∂ν := by
    simp only [hpt]
    rw [integral_finset_sum _ (fun k _ => integrable_finset_sum _ (fun l _ => hprod k l))]
    exact Finset.sum_congr rfl fun k _ =>
      integral_finset_sum _ (fun l _ => hprod k l)
  have hsplit : ∑ k : Fin m, ∑ l : Fin m, ∫ β, X k β * X l β ∂ν
      = (∑ k : Fin m, ∫ β, X k β * X k β ∂ν)
        + ∑ k : Fin m, ∑ l ∈ Finset.univ.erase k, ∫ β, X k β * X l β ∂ν := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k), add_comm]
  have hoffsum : ∑ k : Fin m, ∑ l ∈ Finset.univ.erase k, ∫ β, X k β * X l β ∂ν = 0 := by
    refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l hl => ?_
    exact hoff k l (Finset.mem_erase.mp hl).1.symm
  have hpointwise : (fun β : Fin m → Ω => (∑ k : Fin m, (φ (β k) - c)) ^ 2)
      = fun β => (∑ k : Fin m, X k β) ^ 2 := by
    funext β; simp only [X]
  have hIntSq : Integrable (fun β : Fin m → Ω => (∑ k : Fin m, X k β) ^ 2) ν := by
    rw [show (fun β : Fin m → Ω => (∑ k : Fin m, X k β) ^ 2)
        = fun β => ∑ k : Fin m, ∑ l : Fin m, X k β * X l β from by
      funext β; exact hpt β]
    exact integrable_finset_sum _ (fun k _ => integrable_finset_sum _ (fun l _ => hprod k l))
  refine ⟨by rw [hpointwise]; exact hIntSq, ?_⟩
  rw [hpointwise, hsq, hsplit, hoffsum, add_zero]
  calc ∑ k : Fin m, ∫ β, X k β * X k β ∂ν
      ≤ ∑ _k : Fin m, σ ^ 2 := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [hdiag k]
        exact hvar
    _ = (m : ℝ) * σ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma block_mean_sq_le {Ω : Type} [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]
    {m : ℕ} (hm : 0 < m) (φ : Ω → ℝ) (c σ : ℝ) (hφm : Measurable φ)
    (hint : Integrable φ p) (hl2 : Integrable (fun z => (φ z - c) ^ 2) p)
    (hmean : ∫ z, φ z ∂p = c) (hvar : ∫ z, (φ z - c) ^ 2 ∂p ≤ σ ^ 2) :
    ∫ β : Fin m → Ω, ((∑ k : Fin m, φ (β k)) / (m : ℝ) - c) ^ 2
        ∂(Measure.pi fun _ : Fin m => p) ≤ σ ^ 2 / m := by
  let ν : Measure (Fin m → Ω) := Measure.pi fun _ : Fin m => p
  haveI : IsProbabilityMeasure ν := inferInstanceAs (IsProbabilityMeasure (Measure.pi _))
  obtain ⟨hInt, hle⟩ := block_center_sq_le (Ω := Ω) (p := p) (m := m) φ c σ hφm hint hl2 hmean hvar
  have hpt : ∀ β : Fin m → Ω, ((∑ k : Fin m, φ (β k)) / (m : ℝ) - c)
      = (1 / (m : ℝ)) * (∑ k : Fin m, (φ (β k) - c)) := by
    intro β
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
  have hsq : ∀ β : Fin m → Ω,
      ((∑ k : Fin m, φ (β k)) / (m : ℝ) - c) ^ 2
        = (1 / (m : ℝ)) ^ 2 * (∑ k : Fin m, (φ (β k) - c)) ^ 2 := by
    intro β; rw [hpt β]; ring
  have hfun : (fun β : Fin m → Ω => ((∑ k : Fin m, φ (β k)) / (m : ℝ) - c) ^ 2)
      = fun β => (1 / (m : ℝ)) ^ 2 * (∑ k : Fin m, (φ (β k) - c)) ^ 2 := by
    funext β; exact hsq β
  rw [hfun, integral_const_mul]
  have := mul_le_mul_of_nonneg_left hle (show (0 : ℝ) ≤ (1 / (m : ℝ)) ^ 2 by positivity)
  have he : (1 / (m : ℝ)) ^ 2 * ((m : ℝ) * σ ^ 2) = σ ^ 2 / m := by
    field_simp
  linarith

end OracleTemplate.LineSearch

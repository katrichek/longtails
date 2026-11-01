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

import LongTails.Proofs.SecantPolyakEstimator
import LongTails.Proofs.SecantPolyakRate
import LongTails.Proofs.GapStrongGrowthIteration
import LongTails.Proofs.GdConvex

/-!
Batched secant descent under the Polyak-Łojasiewicz inequality: one step contracts the
expected gap by `1 - μ / L` and pays the batched reply error, and `K` steps give an
expected gap of `(1 - μ / L) ^ K * Δ + K * batchError / L`.
-/

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.SecantPolyak

open ZerothOrder _root_.OracleTemplate.Gradient ContinuizedSimilarQuasar GapStrongGrowth
open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {Ω : Type*} [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]

/-- One secant descent step driven by one batch of value replies. -/
noncomputable def secantStep {d m : ℕ} (L : ℝ) (g : Point d → Ω → ℝ) (h : ℝ)
    (x : Point d) (ξ : Fin m → Fin d × Bool → Ω) : Point d :=
  x - (1 / L) • reply (g := g) h x ξ

/-- Mean square error budget of one batched secant reply. -/
noncomputable def batchError (d m : ℕ) (σ L h : ℝ) : ℝ :=
  8 * (d : ℝ) * σ ^ 2 / (h ^ 2 * m) + 2 * ((d : ℝ) * (L * h / 2) ^ 2)

/-- One secant run of `K` steps from `x0` over `K` independent batches. -/
noncomputable def secantRun {d m K : ℕ} (L : ℝ) (g : Point d → Ω → ℝ) (h : ℝ)
    (x0 : Point d) (ξ : Fin K → Fin m → Fin d × Bool → Ω) : Point d :=
  iterateSamples (secantStep L g h) K x0 ξ

lemma measurable_reply_joint {d m : ℕ} {g : Point d → Ω → ℝ}
    (hg : Measurable (Function.uncurry g)) (h : ℝ) :
    Measurable (fun q : Point d × (Fin m → Fin d × Bool → Ω) => reply (g := g) h q.1 q.2) := by
  classical
  have hv : Measurable (fun q : Point d × (Fin m → Fin d × Bool → Ω) =>
      ∑ r : Fin m, estimate (g := g) h q.1 (q.2 r)) := by
    refine Finset.measurable_sum Finset.univ (fun r _ => ?_)
    unfold estimate
    refine Finset.measurable_sum Finset.univ (fun i _ => ?_)
    have hp : Measurable (fun q : Point d × (Fin m → Fin d × Bool → Ω) => q.1 + h • direction i) :=
      measurable_fst.add measurable_const
    have hw (b : Bool) : Measurable (fun q : Point d × (Fin m → Fin d × Bool → Ω) =>
        q.2 r (i, b)) := (measurable_pi_apply (i, b)).comp ((measurable_pi_apply r).comp measurable_snd)
    have h1 : Measurable (fun q : Point d × (Fin m → Fin d × Bool → Ω) =>
        g (q.1 + h • direction i) (q.2 r (i, true))) := hg.comp (hp.prodMk (hw true))
    have h2 : Measurable (fun q : Point d × (Fin m → Fin d × Bool → Ω) =>
        g q.1 (q.2 r (i, false))) := hg.comp (measurable_fst.prodMk (hw false))
    exact smul_measurable ((h1.sub h2).div_const h) measurable_const
  exact smul_measurable measurable_const hv

lemma measurable_secantStep {d m : ℕ} (L : ℝ) {g : Point d → Ω → ℝ}
    (hg : Measurable (Function.uncurry g)) (h : ℝ) :
    Measurable (fun q : Point d × (Fin m → Fin d × Bool → Ω) => secantStep L g h q.1 q.2) := by
  classical
  refine Measurable.sub measurable_fst ?_
  exact smul_measurable measurable_const (measurable_reply_joint hg h)

/-- One batched secant step contracts the expected gap and pays the batch error. -/
lemma secant_one_step {d m : ℕ} {g : Point d → Ω → ℝ} {f : Point d → ℝ} {σ L μ h : ℝ}
    (hh : 0 < h) (hL : 0 < L) (hμ : 0 < μ) (hμL : μ ≤ L)
    (hg : Measurable (Function.uncurry g))
    (hgi : ∀ x, Integrable (g x) p)
    (hmean : ∀ x, (∫ ω, g x ω ∂p) = f x)
    (hvi : ∀ x, Integrable (fun ω => (g x ω - f x) ^ 2) p)
    (hv : ∀ x, (∫ ω, (g x ω - f x) ^ 2 ∂p) ≤ σ ^ 2)
    (hc : ConvexOn ℝ Set.univ f)
    (hgr : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hm : 0 < m) (xstar : Point d) (hmin : IsMinOn f Set.univ xstar)
    (hpl : ∀ x, 2 * μ * (f x - f xstar) ≤ ‖gradient f x‖ ^ 2)
    (x : Point d) :
    Integrable (fun ξ => f (secantStep L g h x ξ) - f xstar) (batchLaw d m p) ∧
      (∫ ξ, f (secantStep L g h x ξ) - f xstar ∂(batchLaw d m p)) ≤
        (1 - μ / L) * (f x - f xstar) + (1 / L) * batchError d m σ L h := by
  classical
  obtain ⟨hEi, hE⟩ := reply_error_moment (d := d) (m := m) (g := g) (f := f) (σ := σ) (L := L)
    (h := h) (hh := hh) (hg := hg) (hgi := hgi) (hmean := hmean) (hvi := hvi) (hv := hv)
    (hc := hc) (hgr := hgr) (hlip := hlip) (hm := hm) (x := x)
  have hρ : 0 ≤ 1 - μ / L := by
    have : μ / L ≤ 1 := (div_le_one hL).mpr hμL
    linarith
  have hstep (ξ : Fin m → Fin d × Bool → Ω) :
      f (secantStep L g h x ξ) - f xstar ≤
        (1 - μ / L) * (f x - f xstar) + (1 / L) * ‖reply (g := g) h x ξ - gradient f x‖ ^ 2 := by
    have heq : gradient f x + (reply (g := g) h x ξ - gradient f x) = reply (g := g) h x ξ := by abel
    have h1 := plain_pl_step hL hμ xstar (smooth_upper_bound hgr hlip) hpl x
      (reply (g := g) h x ξ - gradient f x)
    have h2 : x - (1 / L) • (gradient f x + (reply (g := g) h x ξ - gradient f x))
        = secantStep L g h x ξ := by
      rw [heq]
      rfl
    rw [h2] at h1
    exact h1
  have hlo (ξ : Fin m → Fin d × Bool → Ω) : 0 ≤ f (secantStep L g h x ξ) - f xstar :=
    sub_nonneg.mpr (hmin (Set.mem_univ _))
  have hRi : Integrable (fun ξ => (1 - μ / L) * (f x - f xstar) +
      (1 / L) * ‖reply (g := g) h x ξ - gradient f x‖ ^ 2) (batchLaw d m p) :=
    Integrable.add (integrable_const _) (hEi.const_mul (1 / L))
  have hR0 (ξ : Fin m → Fin d × Bool → Ω) :
      0 ≤ (1 - μ / L) * (f x - f xstar) + (1 / L) * ‖reply (g := g) h x ξ - gradient f x‖ ^ 2 := by
    refine add_nonneg (mul_nonneg hρ (sub_nonneg.mpr (hmin (Set.mem_univ _))))
      (mul_nonneg (le_of_lt (by positivity)) (sq_nonneg _))
  have haes : AEStronglyMeasurable (fun ξ => f (secantStep L g h x ξ) - f xstar)
      (batchLaw d m p) := by
    have hf : Measurable f :=
      (continuous_iff_continuousAt.mpr (fun y => (hgr y).continuousAt)).measurable
    have hx : Measurable (fun ξ : Fin m → Fin d × Bool → Ω => secantStep L g h x ξ) := by
      show Measurable (fun ξ : Fin m → Fin d × Bool → Ω => x - (1 / L : ℝ) • reply (g := g) h x ξ)
      exact measurable_const.sub (smul_measurable measurable_const (reply_measurable hg h x))
    exact (hf.comp hx).aestronglyMeasurable.sub aestronglyMeasurable_const
  have hL1 : Integrable (fun ξ => f (secantStep L g h x ξ) - f xstar) (batchLaw d m p) :=
    hRi.mono haes (ae_of_all _ fun ξ => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hlo ξ), abs_of_nonneg (hR0 ξ)]
      exact hstep ξ)
  refine ⟨hL1, ?_⟩
  refine le_trans (integral_mono hL1 hRi hstep) ?_
  calc (∫ ξ, (1 - μ / L) * (f x - f xstar) + (1 / L) * ‖reply (g := g) h x ξ - gradient f x‖ ^ 2
        ∂(batchLaw d m p))
      = (1 - μ / L) * (f x - f xstar) + (1 / L) *
          ∫ ξ, ‖reply (g := g) h x ξ - gradient f x‖ ^ 2 ∂(batchLaw d m p) := by
          rw [integral_add (integrable_const _) (hEi.const_mul (1 / L))]
          simp [integral_const_mul, integral_const]
    _ ≤ (1 - μ / L) * (f x - f xstar) + (1 / L) * batchError d m σ L h := by
          refine add_le_add (le_refl _)
            (mul_le_mul_of_nonneg_left hE (le_of_lt (by positivity)))

/-- `K` batched secant steps contract the expected gap geometrically and accumulate `K`
copies of the batch error. -/
lemma secant_accuracy {d m K : ℕ} {g : Point d → Ω → ℝ} {f : Point d → ℝ} {σ L μ h : ℝ}
    {x0 xstar : Point d}
    (hh : 0 < h) (hL : 0 < L) (hμ : 0 < μ) (hμL : μ ≤ L)
    (hg : Measurable (Function.uncurry g))
    (hgi : ∀ x, Integrable (g x) p)
    (hmean : ∀ x, (∫ ω, g x ω ∂p) = f x)
    (hvi : ∀ x, Integrable (fun ω => (g x ω - f x) ^ 2) p)
    (hv : ∀ x, (∫ ω, (g x ω - f x) ^ 2 ∂p) ≤ σ ^ 2)
    (hc : ConvexOn ℝ Set.univ f)
    (hgr : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hm : 0 < m) (hmin : IsMinOn f Set.univ xstar)
    (hpl : ∀ x, 2 * μ * (f x - f xstar) ≤ ‖gradient f x‖ ^ 2) :
    (∫ ξ : Fin K → Fin m → Fin d × Bool → Ω,
        f (secantRun L g h x0 ξ) - f xstar ∂Measure.pi fun _ : Fin K => batchLaw d m p) ≤
        (1 - μ / L) ^ K * (f x0 - f xstar) +
          (K : ℝ) * ((1 / L) * batchError d m σ L h) := by
  classical
  have hρ : 0 ≤ 1 - μ / L := by
    have : μ / L ≤ 1 := (div_le_one hL).mpr hμL
    linarith
  have hf : Measurable f :=
    (continuous_iff_continuousAt.mpr (fun y => (hgr y).continuousAt)).measurable
  let V := f - fun _ => f xstar
  have hV : Measurable V := hf.sub measurable_const
  have hV0 : ∀ x, 0 ≤ V x := fun x => sub_nonneg.mpr (hmin (Set.mem_univ x))
  have hstep : ∀ x, Integrable (fun a => V (secantStep L g h x a)) (batchLaw d m p) ∧
      (∫ a, V (secantStep L g h x a) ∂(batchLaw d m p)) ≤
        (1 - μ / L) * V x + (1 / L) * batchError d m σ L h :=
    fun x => secant_one_step (d := d) (m := m) (g := g) (f := f) (σ := σ) (L := L) (μ := μ)
      (h := h) (hh := hh) (hL := hL) (hμ := hμ) (hμL := hμL) (hg := hg) (hgi := hgi)
      (hmean := hmean) (hvi := hvi) (hv := hv) (hc := hc) (hgr := hgr) (hlip := hlip)
      (hm := hm) (xstar := xstar) (hmin := hmin) (hpl := hpl) (x := x)
  have hkey := iterateSamples_measurable_integral (advance := secantStep L g h)
    (measurable_secantStep L hg h) (P := ⟨batchLaw d m p, inferInstance⟩)
    (V := V) hV hV0 hρ hstep K x0
  have hsum : (∑ j ∈ Finset.range K, (1 - μ / L) ^ j) ≤ (K : ℝ) := by
    calc (∑ j ∈ Finset.range K, (1 - μ / L) ^ j) ≤ ∑ j ∈ Finset.range K, (1 : ℝ) :=
        Finset.sum_le_sum fun j _ => le_trans (pow_le_pow_of_le_one hρ
          (by have : 0 ≤ μ / L := div_nonneg (le_of_lt hμ) (le_of_lt hL); linarith)
          (Nat.zero_le j)) (by simp)
      _ = (K : ℝ) := by simp
  refine le_trans hkey.2 ?_
  have hK : 0 ≤ (1 / L) * batchError d m σ L h := by
    simp only [batchError]
    positivity
  calc (1 - μ / L) ^ K * (f x0 - f xstar) +
        ((1 / L) * batchError d m σ L h) *
          ∑ j ∈ Finset.range K, (1 - μ / L) ^ j
      ≤ (1 - μ / L) ^ K * (f x0 - f xstar) +
          ((1 / L) * batchError d m σ L h) * (K : ℝ) := by
          refine add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hsum hK)
      _ = (1 - μ / L) ^ K * (f x0 - f xstar) +
          (K : ℝ) * ((1 / L) * batchError d m σ L h) := by ring

end OracleTemplate.SecantPolyak

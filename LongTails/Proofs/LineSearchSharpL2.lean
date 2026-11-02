import LongTails.Proofs.LineSearchAccuracy
import LongTails.Proofs.LineSearchFubini
import LongTails.Proofs.LineSearchMeasurable
import LongTails.Proofs.LineSearchSharp
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal

namespace OracleTemplate.LineSearch

variable {Ω : Type} [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]

structure Hyps {Ω : Type} [MeasurableSpace Ω] (m : ℕ) (g : ℝ → Ω → ℝ) (f : ℝ → ℝ) (σ : ℝ)
    (p : Measure Ω) [IsProbabilityMeasure p] where
  hm : 0 < m
  hfm : Measurable f
  hg : Measurable (Function.uncurry g)
  hmean : ∀ x, ∫ z, g x z ∂p = f x
  hint : ∀ x, Integrable (g x) p
  hsql2 : ∀ x, Integrable (fun z => (g x z - f x) ^ 2) p
  hvar : ∀ x, ∫ z, (g x z - f x) ^ 2 ∂p ≤ σ ^ 2

lemma product_block_error_sq_lintegral_le {n m : ℕ} (g : ℝ → Ω → ℝ) (f : ℝ → ℝ) (σ : ℝ)
    (c : (Fin n → Fin m → Ω) → ℝ) (hc : Measurable c) (hfm : Measurable f)
    (hg : Measurable (Function.uncurry g)) (hm : 0 < m)
    (hmean : ∀ x, ∫ z, g x z ∂p = f x)
    (hint : ∀ x, Integrable (g x) p)
    (hsql2 : ∀ x, Integrable (fun z => (g x z - f x) ^ 2) p)
    (hvar : ∀ x, ∫ z, (g x z - f x) ^ 2 ∂p ≤ σ ^ 2) :
    ∫⁻ z : (Fin n → Fin m → Ω) × (Fin m → Ω), ENNReal.ofReal (blkErr g f c z ^ 2)
        ∂((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin m => p).prod
          (Measure.pi fun _ : Fin m => p))
      ≤ ENNReal.ofReal (σ ^ 2 / m) := by
  set μ : Measure (Fin n → Fin m → Ω) := Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin m => p
    with hμ
  set ν : Measure (Fin m → Ω) := Measure.pi fun _ : Fin m => p with hν
  have hG : Measurable (fun z : (Fin n → Fin m → Ω) × (Fin m → Ω) => blkErr g f c z ^ 2) :=
    (continuous_pow 2).measurable.comp (measurable_blkErr g f c hc hfm hg)
  have hφm (a : Fin n → Fin m → Ω) : Measurable (fun z : Ω => g (c a) z) :=
    hg.comp (Measurable.prodMk measurable_const measurable_id)
  have hfibre (a : Fin n → Fin m → Ω) :
      ∫ y : Fin m → Ω, ((∑ k : Fin m, g (c a) (y k)) / (m : ℝ) - f (c a)) ^ 2 ∂ν ≤ σ ^ 2 / m :=
    block_mean_sq_le hm (fun z : Ω => g (c a) z) (f (c a)) σ (hφm a) (hint (c a))
      (hsql2 (c a)) (hmean (c a)) (hvar (c a))
  have hlint (a : Fin n → Fin m → Ω) :
      ∫⁻ y : Fin m → Ω, ENNReal.ofReal (blkErr g f c (a, y) ^ 2) ∂ν
        ≤ ENNReal.ofReal (σ ^ 2 / m) := by
    obtain ⟨hInt0, _⟩ := block_center_sq_le (Ω := Ω) (p := p) (fun z : Ω => g (c a) z) (f (c a)) σ
      (hφm a) (hint (c a)) (hsql2 (c a)) (hmean (c a)) (hvar (c a))
    have hInt : Integrable (fun y : Fin m → Ω =>
        ((∑ k : Fin m, g (c a) (y k)) / (m : ℝ) - f (c a)) ^ 2) ν := by
      have heq : (fun y : Fin m → Ω => ((∑ k : Fin m, g (c a) (y k)) / (m : ℝ) - f (c a)) ^ 2)
          = fun y : Fin m → Ω =>
            (1 / (m : ℝ)) ^ 2 * (∑ k : Fin m, (g (c a) (y k) - f (c a))) ^ 2 := by
        funext y
        have h1 : ((∑ k : Fin m, g (c a) (y k)) / (m : ℝ) - f (c a))
            = (1 / (m : ℝ)) * (∑ k : Fin m, (g (c a) (y k) - f (c a))) := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          field_simp
        rw [h1]
        ring
      rw [heq]
      exact Integrable.const_mul hInt0 _
    calc ∫⁻ y : Fin m → Ω, ENNReal.ofReal (blkErr g f c (a, y) ^ 2) ∂ν
        = ∫⁻ y : Fin m → Ω,
            ENNReal.ofReal (((∑ k : Fin m, g (c a) (y k)) / (m : ℝ) - f (c a)) ^ 2) ∂ν := by
          congr with y
          simp only [blkErr, sq_abs]
      _ = ENNReal.ofReal (∫ y : Fin m → Ω,
            ((∑ k : Fin m, g (c a) (y k)) / (m : ℝ) - f (c a)) ^ 2 ∂ν) :=
          (ofReal_integral_eq_lintegral_ofReal hInt
            (Filter.Eventually.of_forall fun _ => sq_nonneg _)).symm
      _ ≤ ENNReal.ofReal (σ ^ 2 / m) := ENNReal.ofReal_le_ofReal (hfibre a)
  have hprod :
      ∫⁻ z : (Fin n → Fin m → Ω) × (Fin m → Ω), ENNReal.ofReal (blkErr g f c z ^ 2) ∂(μ.prod ν)
      = ∫⁻ a : Fin n → Fin m → Ω, ∫⁻ y : Fin m → Ω, ENNReal.ofReal (blkErr g f c (a, y) ^ 2) ∂ν ∂μ :=
    lintegral_prod (fun z : (Fin n → Fin m → Ω) × (Fin m → Ω) =>
        ENNReal.ofReal (blkErr g f c z ^ 2)) ((ENNReal.measurable_ofReal.comp hG).aemeasurable)
  calc ∫⁻ z : (Fin n → Fin m → Ω) × (Fin m → Ω), ENNReal.ofReal (blkErr g f c z ^ 2) ∂(μ.prod ν)
      = ∫⁻ a : Fin n → Fin m → Ω, ∫⁻ y : Fin m → Ω,
          ENNReal.ofReal (blkErr g f c (a, y) ^ 2) ∂ν ∂μ := hprod
    _ ≤ ∫⁻ _a : Fin n → Fin m → Ω, ENNReal.ofReal (σ ^ 2 / m) ∂μ := lintegral_mono hlint
    _ = ENNReal.ofReal (σ ^ 2 / m) * μ Set.univ := lintegral_const _
    _ = ENNReal.ofReal (σ ^ 2 / m) * 1 := by rw [measure_univ (μ := μ)]
    _ = ENNReal.ofReal (σ ^ 2 / m) := by simp

section Oracle

variable (R x0 : ℝ)

lemma left_error_sq_lintegral_le {m : ℕ} (g : ℝ → Ω → ℝ) (f : ℝ → ℝ) (σ : ℝ)
    (hfm : Measurable f) (hg : Measurable (Function.uncurry g))
    (hm : 0 < m) (hmean : ∀ x, ∫ z, g x z ∂p = f x)
    (hint : ∀ x, Integrable (g x) p)
    (hsql2 : ∀ x, Integrable (fun z => (g x z - f x) ^ 2) p)
    (hvar : ∀ x, ∫ z, (g x z - f x) ^ 2 ∂p ≤ σ ^ 2) (j : ℕ) :
    ∫⁻ β : ℕ → Fin m → Ω,
        ENNReal.ofReal ((estLeft R x0 m g β j - f (leftAt R x0 m g β j)) ^ 2) ∂(blockLaw p m)
      ≤ ENNReal.ofReal (σ ^ 2 / m) := by
  let hn : Nonempty Ω := nonempty_of_probability (p := p)
  let t0 : ℕ → Fin m → Ω := fun _ _ => Classical.choice hn
  let c : (Fin (2 * j) → Fin m → Ω) → ℝ := fun a => leftAt R x0 m g (combine a t0) j
  have hc : Measurable c := (measurable_leftAt R x0 m g hg j).comp (measurable_combine_head t0)
  have hG : Measurable (fun z => blkErr g f c z ^ 2) :=
    (continuous_pow 2).measurable.comp (measurable_blkErr g f c hc hfm hg)
  have hpt (β : ℕ → Fin m → Ω) :
      blkErr g f c ((fun i : Fin (2 * j) => β i), β (2 * j))
        = |estLeft R x0 m g β j - f (leftAt R x0 m g β j)| := by
    simp only [blkErr, c, estLeft]
    rw [leftAt_combine R x0 g t0 β j]
  calc ∫⁻ β : ℕ → Fin m → Ω,
        ENNReal.ofReal ((estLeft R x0 m g β j - f (leftAt R x0 m g β j)) ^ 2) ∂(blockLaw p m)
      = ∫⁻ β, ENNReal.ofReal (blkErr g f c ((fun i : Fin (2 * j) => β i), β (2 * j)) ^ 2)
          ∂(blockLaw p m) := by
        congr with β
        rw [hpt β, sq_abs]
      _ = ∫⁻ z : (Fin (2 * j) → Fin m → Ω) × (Fin m → Ω), ENNReal.ofReal (blkErr g f c z ^ 2)
          ∂((Measure.pi fun _ : Fin (2 * j) => Measure.pi fun _ : Fin m => p).prod
            (Measure.pi fun _ : Fin m => p)) := by
        rw [← (map_prefix_block_preserving p j 0).map_eq]
        exact (lintegral_map (hf := ENNReal.measurable_ofReal.comp hG)
          (hg := (map_prefix_block_preserving p j 0).measurable)).symm
      _ ≤ ENNReal.ofReal (σ ^ 2 / m) :=
        product_block_error_sq_lintegral_le g f σ c hc hfm hg hm hmean hint hsql2 hvar

lemma right_error_sq_lintegral_le {m : ℕ} (g : ℝ → Ω → ℝ) (f : ℝ → ℝ) (σ : ℝ)
    (hfm : Measurable f) (hg : Measurable (Function.uncurry g))
    (hm : 0 < m) (hmean : ∀ x, ∫ z, g x z ∂p = f x)
    (hint : ∀ x, Integrable (g x) p)
    (hsql2 : ∀ x, Integrable (fun z => (g x z - f x) ^ 2) p)
    (hvar : ∀ x, ∫ z, (g x z - f x) ^ 2 ∂p ≤ σ ^ 2) (j : ℕ) :
    ∫⁻ β : ℕ → Fin m → Ω,
        ENNReal.ofReal ((estRight R x0 m g β j - f (rightAt R x0 m g β j)) ^ 2) ∂(blockLaw p m)
      ≤ ENNReal.ofReal (σ ^ 2 / m) := by
  let hn : Nonempty Ω := nonempty_of_probability (p := p)
  let t0 : ℕ → Fin m → Ω := fun _ _ => Classical.choice hn
  let c : (Fin (2 * j) → Fin m → Ω) → ℝ := fun a => rightAt R x0 m g (combine a t0) j
  have hc : Measurable c := (measurable_rightAt R x0 m g hg j).comp (measurable_combine_head t0)
  have hG : Measurable (fun z => blkErr g f c z ^ 2) :=
    (continuous_pow 2).measurable.comp (measurable_blkErr g f c hc hfm hg)
  have hpt (β : ℕ → Fin m → Ω) :
      blkErr g f c ((fun i : Fin (2 * j) => β i), β (2 * j + 1))
        = |estRight R x0 m g β j - f (rightAt R x0 m g β j)| := by
    simp only [blkErr, c, estRight]
    rw [rightAt_combine R x0 g t0 β j]
  calc ∫⁻ β : ℕ → Fin m → Ω,
        ENNReal.ofReal ((estRight R x0 m g β j - f (rightAt R x0 m g β j)) ^ 2) ∂(blockLaw p m)
      = ∫⁻ β, ENNReal.ofReal (blkErr g f c ((fun i : Fin (2 * j) => β i), β (2 * j + 1)) ^ 2)
          ∂(blockLaw p m) := by
        congr with β
        rw [hpt β, sq_abs]
      _ = ∫⁻ z : (Fin (2 * j) → Fin m → Ω) × (Fin m → Ω), ENNReal.ofReal (blkErr g f c z ^ 2)
          ∂((Measure.pi fun _ : Fin (2 * j) => Measure.pi fun _ : Fin m => p).prod
            (Measure.pi fun _ : Fin m => p)) := by
        rw [← (map_prefix_block_preserving p j 1).map_eq]
        exact (lintegral_map (hf := ENNReal.measurable_ofReal.comp hG)
          (hg := (map_prefix_block_preserving p j 1).measurable)).symm
      _ ≤ ENNReal.ofReal (σ ^ 2 / m) :=
        product_block_error_sq_lintegral_le g f σ c hc hfm hg hm hmean hint hsql2 hvar

noncomputable def errL (m : ℕ) (g : ℝ → Ω → ℝ) (f : ℝ → ℝ) (β : ℕ → Fin m → Ω) (j : ℕ) : ℝ :=
  |estLeft R x0 m g β j - f (leftAt R x0 m g β j)|

noncomputable def errR (m : ℕ) (g : ℝ → Ω → ℝ) (f : ℝ → ℝ) (β : ℕ → Fin m → Ω) (j : ℕ) : ℝ :=
  |estRight R x0 m g β j - f (rightAt R x0 m g β j)|

lemma measurable_errL (m : ℕ) (g : ℝ → Ω → ℝ) (f : ℝ → ℝ) (σ : ℝ)
    (H : Hyps m g f σ p) (j : ℕ) :
    Measurable (fun β : ℕ → Fin m → Ω => errL R x0 m g f β j) :=
  continuous_abs.measurable.comp
    ((measurable_estLeft R x0 m g H.hg j).sub (H.hfm.comp (measurable_leftAt R x0 m g H.hg j)))

lemma measurable_errR (m : ℕ) (g : ℝ → Ω → ℝ) (f : ℝ → ℝ) (σ : ℝ)
    (H : Hyps m g f σ p) (j : ℕ) :
    Measurable (fun β : ℕ → Fin m → Ω => errR R x0 m g f β j) :=
  continuous_abs.measurable.comp
    ((measurable_estRight R x0 m g H.hg j).sub (H.hfm.comp (measurable_rightAt R x0 m g H.hg j)))

omit [MeasurableSpace Ω] in
lemma lvlErr_eq_err (m : ℕ) (g : ℝ → Ω → ℝ) (f : ℝ → ℝ) (β : ℕ → Fin m → Ω) (j : ℕ) :
    lvlErr R x0 (V R x0 m g β) f j = errL R x0 m g f β j + errR R x0 m g f β j :=
  (levelError_eq_lvlErr R x0 m g f β j).symm

lemma errL_sq_integral_le (m : ℕ) (g : ℝ → Ω → ℝ) (f : ℝ → ℝ) (σ : ℝ)
    (H : Hyps m g f σ p) (j : ℕ) :
    ∫ β : ℕ → Fin m → Ω, errL R x0 m g f β j ^ 2 ∂(blockLaw p m) ≤ σ ^ 2 / m := by
  have hmeas : AEStronglyMeasurable (fun β : ℕ → Fin m → Ω => errL R x0 m g f β j ^ 2)
      (blockLaw p m) :=
    ((continuous_pow 2).measurable.comp (measurable_errL R x0 m g f σ H j)).aestronglyMeasurable
  have hbnd : ∫⁻ β : ℕ → Fin m → Ω, ENNReal.ofReal (errL R x0 m g f β j ^ 2) ∂(blockLaw p m)
      ≤ ENNReal.ofReal (σ ^ 2 / m) := by
    refine le_trans ?_ (left_error_sq_lintegral_le R x0 g f σ H.hfm H.hg H.hm H.hmean H.hint
      H.hsql2 H.hvar j)
    refine le_of_eq (lintegral_congr fun β => ?_)
    show ENNReal.ofReal (errL R x0 m g f β j ^ 2)
        = ENNReal.ofReal ((estLeft R x0 m g β j - f (leftAt R x0 m g β j)) ^ 2)
    simp [errL]
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun _ => sq_nonneg _) hmeas]
  have hne : (∫⁻ β : ℕ → Fin m → Ω, ENNReal.ofReal (errL R x0 m g f β j ^ 2) ∂(blockLaw p m))
      ≠ ⊤ := (lt_of_le_of_lt hbnd ENNReal.ofReal_lt_top).ne
  exact ((ENNReal.toReal_le_toReal hne ENNReal.ofReal_lt_top.ne).mpr hbnd).trans
    (le_of_eq (ENNReal.toReal_ofReal (by positivity)))

lemma errR_sq_integral_le (m : ℕ) (g : ℝ → Ω → ℝ) (f : ℝ → ℝ) (σ : ℝ)
    (H : Hyps m g f σ p) (j : ℕ) :
    ∫ β : ℕ → Fin m → Ω, errR R x0 m g f β j ^ 2 ∂(blockLaw p m) ≤ σ ^ 2 / m := by
  have hmeas : AEStronglyMeasurable (fun β : ℕ → Fin m → Ω => errR R x0 m g f β j ^ 2)
      (blockLaw p m) :=
    ((continuous_pow 2).measurable.comp (measurable_errR R x0 m g f σ H j)).aestronglyMeasurable
  have hbnd : ∫⁻ β : ℕ → Fin m → Ω, ENNReal.ofReal (errR R x0 m g f β j ^ 2) ∂(blockLaw p m)
      ≤ ENNReal.ofReal (σ ^ 2 / m) := by
    refine le_trans ?_ (right_error_sq_lintegral_le R x0 g f σ H.hfm H.hg H.hm H.hmean H.hint
      H.hsql2 H.hvar j)
    refine le_of_eq (lintegral_congr fun β => ?_)
    show ENNReal.ofReal (errR R x0 m g f β j ^ 2)
        = ENNReal.ofReal ((estRight R x0 m g β j - f (rightAt R x0 m g β j)) ^ 2)
    simp [errR]
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun _ => sq_nonneg _) hmeas]
  have hne : (∫⁻ β : ℕ → Fin m → Ω, ENNReal.ofReal (errR R x0 m g f β j ^ 2) ∂(blockLaw p m))
      ≠ ⊤ := (lt_of_le_of_lt hbnd ENNReal.ofReal_lt_top).ne
  exact ((ENNReal.toReal_le_toReal hne ENNReal.ofReal_lt_top.ne).mpr hbnd).trans
    (le_of_eq (ENNReal.toReal_ofReal (by positivity)))

lemma integrable_errL_sq (m : ℕ) (g : ℝ → Ω → ℝ) (f : ℝ → ℝ) (σ : ℝ)
    (H : Hyps m g f σ p) (j : ℕ) :
    Integrable (fun β : ℕ → Fin m → Ω => errL R x0 m g f β j ^ 2) (blockLaw p m) := by
  have hnn : 0 ≤ᵐ[blockLaw p m] fun β : ℕ → Fin m → Ω => errL R x0 m g f β j ^ 2 :=
    Filter.Eventually.of_forall fun _ => sq_nonneg _
  refine ⟨((continuous_pow 2).measurable.comp (measurable_errL R x0 m g f σ H j)).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal hnn).mpr ?_⟩
  refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun β => by
    show ENNReal.ofReal (errL R x0 m g f β j ^ 2)
        = ENNReal.ofReal ((estLeft R x0 m g β j - f (leftAt R x0 m g β j)) ^ 2)
    simp [errL])) ?_
  refine lt_of_le_of_lt (left_error_sq_lintegral_le R x0 g f σ H.hfm H.hg H.hm H.hmean H.hint
    H.hsql2 H.hvar j) ENNReal.ofReal_lt_top

lemma integrable_errR_sq (m : ℕ) (g : ℝ → Ω → ℝ) (f : ℝ → ℝ) (σ : ℝ)
    (H : Hyps m g f σ p) (j : ℕ) :
    Integrable (fun β : ℕ → Fin m → Ω => errR R x0 m g f β j ^ 2) (blockLaw p m) := by
  have hnn : 0 ≤ᵐ[blockLaw p m] fun β : ℕ → Fin m → Ω => errR R x0 m g f β j ^ 2 :=
    Filter.Eventually.of_forall fun _ => sq_nonneg _
  refine ⟨((continuous_pow 2).measurable.comp (measurable_errR R x0 m g f σ H j)).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal hnn).mpr ?_⟩
  refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun β => by
    show ENNReal.ofReal (errR R x0 m g f β j ^ 2)
        = ENNReal.ofReal ((estRight R x0 m g β j - f (rightAt R x0 m g β j)) ^ 2)
    simp [errR])) ?_
  refine lt_of_le_of_lt (right_error_sq_lintegral_le R x0 g f σ H.hfm H.hg H.hm H.hmean H.hint
    H.hsql2 H.hvar j) ENNReal.ofReal_lt_top

lemma integrable_sum_errL_sq (m : ℕ) (g : ℝ → Ω → ℝ) (f : ℝ → ℝ) (σ : ℝ)
    (H : Hyps m g f σ p) (J : ℕ) :
    Integrable (fun β : ℕ → Fin m → Ω => ∑ j ∈ Finset.range J, errL R x0 m g f β j ^ 2)
      (blockLaw p m) := by
  refine integrable_finsetSum (Finset.range J) ?_
  intro j _
  exact integrable_errL_sq R x0 m g f σ H j

lemma integrable_sum_errR_sq (m : ℕ) (g : ℝ → Ω → ℝ) (f : ℝ → ℝ) (σ : ℝ)
    (H : Hyps m g f σ p) (J : ℕ) :
    Integrable (fun β : ℕ → Fin m → Ω => ∑ j ∈ Finset.range J, errR R x0 m g f β j ^ 2)
      (blockLaw p m) := by
  refine integrable_finsetSum (Finset.range J) ?_
  intro j _
  exact integrable_errR_sq R x0 m g f σ H j

noncomputable def aggSq (m : ℕ) (g : ℝ → Ω → ℝ) (f : ℝ → ℝ) (β : ℕ → Fin m → Ω) (J : ℕ) : ℝ :=
  2 * (∑ j ∈ Finset.range J, errL R x0 m g f β j ^ 2
    + ∑ j ∈ Finset.range J, errR R x0 m g f β j ^ 2)

omit [MeasurableSpace Ω] in
lemma aggSq_nonneg (m : ℕ) (g : ℝ → Ω → ℝ) (f : ℝ → ℝ) (β : ℕ → Fin m → Ω) (J : ℕ) :
    0 ≤ aggSq R x0 m g f β J := by
  show 2 * (_ + _) ≥ 0
  positivity

lemma measurable_aggSq (m : ℕ) (g : ℝ → Ω → ℝ) (f : ℝ → ℝ) (σ : ℝ)
    (H : Hyps m g f σ p) (J : ℕ) :
    Measurable (fun β : ℕ → Fin m → Ω => aggSq R x0 m g f β J) := by
  refine Measurable.mul measurable_const ?_
  refine Measurable.add ?_ ?_
  · exact Finset.measurable_sum (Finset.range J) fun j _ =>
      (continuous_pow 2).measurable.comp (measurable_errL R x0 m g f σ H j)
  · exact Finset.measurable_sum (Finset.range J) fun j _ =>
      (continuous_pow 2).measurable.comp (measurable_errR R x0 m g f σ H j)

lemma integrable_aggSq (m : ℕ) (g : ℝ → Ω → ℝ) (f : ℝ → ℝ) (σ : ℝ)
    (H : Hyps m g f σ p) (J : ℕ) :
    Integrable (fun β : ℕ → Fin m → Ω => aggSq R x0 m g f β J) (blockLaw p m) := by
  refine Integrable.const_mul ?_ (2 : ℝ)
  exact (integrable_sum_errL_sq R x0 m g f σ H J).add (integrable_sum_errR_sq R x0 m g f σ H J)

lemma integral_aggSq_le (m : ℕ) (g : ℝ → Ω → ℝ) (f : ℝ → ℝ) (σ : ℝ)
    (H : Hyps m g f σ p) (J : ℕ) :
    ∫ β : ℕ → Fin m → Ω, aggSq R x0 m g f β J ∂(blockLaw p m)
      ≤ 2 * ((J : ℝ) * (σ ^ 2 / m) + (J : ℝ) * (σ ^ 2 / m)) := by
  have hL : ∫ β : ℕ → Fin m → Ω, ∑ j ∈ Finset.range J, errL R x0 m g f β j ^ 2 ∂(blockLaw p m)
      ≤ (J : ℝ) * (σ ^ 2 / m) := by
    rw [integral_finsetSum (Finset.range J) fun j _ => integrable_errL_sq R x0 m g f σ H j]
    refine le_trans (Finset.sum_le_sum fun j _ =>
      errL_sq_integral_le R x0 m g f σ H j) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hR : ∫ β : ℕ → Fin m → Ω, ∑ j ∈ Finset.range J, errR R x0 m g f β j ^ 2 ∂(blockLaw p m)
      ≤ (J : ℝ) * (σ ^ 2 / m) := by
    rw [integral_finsetSum (Finset.range J) fun j _ => integrable_errR_sq R x0 m g f σ H j]
    refine le_trans (Finset.sum_le_sum fun j _ =>
      errR_sq_integral_le R x0 m g f σ H j) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h1 : ∫ β : ℕ → Fin m → Ω, aggSq R x0 m g f β J ∂(blockLaw p m)
      = 2 * (∫ β : ℕ → Fin m → Ω, ∑ j ∈ Finset.range J, errL R x0 m g f β j ^ 2 ∂(blockLaw p m)
        + ∫ β : ℕ → Fin m → Ω, ∑ j ∈ Finset.range J, errR R x0 m g f β j ^ 2 ∂(blockLaw p m)) := by
    show ∫ β : ℕ → Fin m → Ω,
        2 * (∑ j ∈ Finset.range J, errL R x0 m g f β j ^ 2
          + ∑ j ∈ Finset.range J, errR R x0 m g f β j ^ 2) ∂(blockLaw p m) = _
    rw [integral_const_mul, integral_add]
    · exact integrable_sum_errL_sq R x0 m g f σ H J
    · exact integrable_sum_errR_sq R x0 m g f σ H J
  rw [h1]
  gcongr

omit [MeasurableSpace Ω] in
lemma lvlErr_le_sqrt_aggSq (m : ℕ) (g : ℝ → Ω → ℝ) (f : ℝ → ℝ) (β : ℕ → Fin m → Ω) (J j : ℕ)
    (hj : j < J) :
    lvlErr R x0 (V R x0 m g β) f j ≤ Real.sqrt (aggSq R x0 m g f β J) := by
  refine Real.le_sqrt_of_sq_le ?_
  have h1 : lvlErr R x0 (V R x0 m g β) f j = errL R x0 m g f β j + errR R x0 m g f β j :=
    lvlErr_eq_err R x0 m g f β j
  have h2 : (errL R x0 m g f β j + errR R x0 m g f β j) ^ 2
      ≤ 2 * (errL R x0 m g f β j ^ 2 + errR R x0 m g f β j ^ 2) := by
    nlinarith [sq_nonneg (errL R x0 m g f β j - errR R x0 m g f β j)]
  have h3 : errL R x0 m g f β j ^ 2 ≤ ∑ k ∈ Finset.range J, errL R x0 m g f β k ^ 2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg _) (Finset.mem_range.mpr hj)
  have h4 : errR R x0 m g f β j ^ 2 ≤ ∑ k ∈ Finset.range J, errR R x0 m g f β k ^ 2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg _) (Finset.mem_range.mpr hj)
  show (lvlErr R x0 (V R x0 m g β) f j) ^ 2 ≤ _
  rw [h1]
  refine le_trans h2 (mul_le_mul_of_nonneg_left (add_le_add h3 h4) ?_)
  norm_num

lemma integrable_sqrt_aggSq (m : ℕ) (g : ℝ → Ω → ℝ) (f : ℝ → ℝ) (σ : ℝ)
    (H : Hyps m g f σ p) (J : ℕ) :
    Integrable (fun β : ℕ → Fin m → Ω => Real.sqrt (aggSq R x0 m g f β J)) (blockLaw p m) := by
  have hInt := integrable_aggSq R x0 m g f σ H J
  have hpt : ∀ β : ℕ → Fin m → Ω, Real.sqrt (aggSq R x0 m g f β J) ≤ 1 + aggSq R x0 m g f β J := by
    intro β
    have hx : 0 ≤ aggSq R x0 m g f β J := aggSq_nonneg R x0 m g f β J
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    nlinarith [sq_nonneg (aggSq R x0 m g f β J)]
  have hsq_nn : 0 ≤ᵐ[blockLaw p m]
      fun β : ℕ → Fin m → Ω => Real.sqrt (aggSq R x0 m g f β J) :=
    Filter.Eventually.of_forall fun _ => Real.sqrt_nonneg _
  refine ⟨((Continuous.measurable Real.continuous_sqrt |>.comp
      (measurable_aggSq R x0 m g f σ H J)).aestronglyMeasurable),
    (hasFiniteIntegral_iff_ofReal hsq_nn).mpr ?_⟩
  refine lt_of_le_of_lt (lintegral_mono fun β => ENNReal.ofReal_le_ofReal (hpt β)) ?_
  have heq : (fun β : ℕ → Fin m → Ω => ENNReal.ofReal (1 + aggSq R x0 m g f β J))
      = fun β : ℕ → Fin m → Ω => (1 : ℝ≥0∞) + ENNReal.ofReal (aggSq R x0 m g f β J) := by
    funext β
    rw [ENNReal.ofReal_add (by positivity) (aggSq_nonneg R x0 m g f β J), ENNReal.ofReal_one]
  rw [heq, lintegral_add_left' measurable_const.aemeasurable]
  rw [lintegral_const, measure_univ, one_mul]
  refine ENNReal.add_lt_top.mpr ⟨?_, ?_⟩
  · exact ENNReal.one_lt_top
  · rw [← ofReal_integral_eq_lintegral_ofReal hInt
      (Filter.Eventually.of_forall fun β => aggSq_nonneg R x0 m g f β J)]
    exact ENNReal.ofReal_lt_top

lemma integral_sqrt_aggSq_le (m : ℕ) (g : ℝ → Ω → ℝ) (f : ℝ → ℝ) (σ : ℝ)
    (H : Hyps m g f σ p) (hσ : 0 ≤ σ) (J : ℕ) :
    ∫ β : ℕ → Fin m → Ω, Real.sqrt (aggSq R x0 m g f β J) ∂(blockLaw p m)
      ≤ 2 * (σ * Real.sqrt ((J : ℝ) / m)) := by
  have hInt := integrable_aggSq R x0 m g f σ H J
  have hIsqrt := integrable_sqrt_aggSq R x0 m g f σ H J
  have hnn : 0 ≤ᵐ[blockLaw p m] fun β : ℕ → Fin m → Ω => aggSq R x0 m g f β J :=
    Filter.Eventually.of_forall fun β => aggSq_nonneg R x0 m g f β J
  have hmain : ∫ β : ℕ → Fin m → Ω, Real.sqrt (aggSq R x0 m g f β J) ∂(blockLaw p m)
      ≤ Real.sqrt (∫ β : ℕ → Fin m → Ω, aggSq R x0 m g f β J ∂(blockLaw p m)) := by
    by_cases hc : ∫ β : ℕ → Fin m → Ω, aggSq R x0 m g f β J ∂(blockLaw p m) = 0
    · have hz : (fun β : ℕ → Fin m → Ω => aggSq R x0 m g f β J)
        =ᵐ[blockLaw p m] fun _ => 0 := (integral_eq_zero_iff_of_nonneg_ae hnn hInt).mp hc
      have hz2 : (fun β : ℕ → Fin m → Ω => Real.sqrt (aggSq R x0 m g f β J))
          =ᵐ[blockLaw p m] fun _ => 0 := by
        filter_upwards [hz] with β hβ
        rw [hβ, Real.sqrt_zero]
      rw [integral_congr_ae hz2, integral_zero]
      positivity
    · have hc0 : 0 < ∫ β : ℕ → Fin m → Ω, aggSq R x0 m g f β J ∂(blockLaw p m) :=
        lt_of_le_of_ne' (integral_nonneg fun β => aggSq_nonneg R x0 m g f β J) hc
      set c := Real.sqrt (∫ β : ℕ → Fin m → Ω, aggSq R x0 m g f β J ∂(blockLaw p m)) with hcdef
      have hcp : 0 < c := Real.sqrt_pos.mpr hc0
      have hc2 : c ^ 2 = ∫ β : ℕ → Fin m → Ω, aggSq R x0 m g f β J ∂(blockLaw p m) := by
        rw [hcdef, Real.sq_sqrt (le_of_lt hc0)]
      have hpt : ∀ β : ℕ → Fin m → Ω, Real.sqrt (aggSq R x0 m g f β J)
          ≤ (1 / (2 * c)) * aggSq R x0 m g f β J + c / 2 := by
        intro β
        have hs : Real.sqrt (aggSq R x0 m g f β J) ^ 2 = aggSq R x0 m g f β J :=
          Real.sq_sqrt (aggSq_nonneg R x0 m g f β J)
        have hsq : 0 ≤ (Real.sqrt (aggSq R x0 m g f β J) - c) ^ 2 := sq_nonneg _
        field_simp
        nlinarith
      calc ∫ β : ℕ → Fin m → Ω, Real.sqrt (aggSq R x0 m g f β J) ∂(blockLaw p m)
          ≤ ∫ β : ℕ → Fin m → Ω, ((1 / (2 * c)) * aggSq R x0 m g f β J + c / 2)
            ∂(blockLaw p m) := integral_mono hIsqrt
              ((hInt.const_mul (1 / (2 * c))).add (integrable_const (c / 2))) hpt
        _ = (∫ β : ℕ → Fin m → Ω, aggSq R x0 m g f β J ∂(blockLaw p m)) / (2 * c) + c / 2 := by
          rw [integral_add (hInt.const_mul (1 / (2 * c))) (integrable_const (c / 2)),
            integral_const_mul]
          simp only [integral_const, probReal_univ, one_smul]
          field_simp
        _ = c := by
          rw [← hc2]
          field_simp
          nlinarith
  refine le_trans hmain ?_
  have hab := integral_aggSq_le R x0 m g f σ H J
  have h2 : 2 * ((J : ℝ) * (σ ^ 2 / m) + (J : ℝ) * (σ ^ 2 / m)) = 4 * (σ ^ 2 * ((J : ℝ) / m)) := by
    field_simp
    ring
  have hsq : Real.sqrt (4 * (σ ^ 2 * ((J : ℝ) / m))) = 2 * (σ * Real.sqrt ((J : ℝ) / m)) := by
    have h4 : (4 : ℝ) * (σ ^ 2 * ((J : ℝ) / m)) = (2 * σ) ^ 2 * ((J : ℝ) / m) := by ring
    rw [h4, Real.sqrt_mul (show 0 ≤ (2 * σ) ^ 2 by positivity),
      Real.sqrt_sq (show (0 : ℝ) ≤ 2 * σ by positivity)]
    ring
  calc Real.sqrt (∫ β : ℕ → Fin m → Ω, aggSq R x0 m g f β J ∂(blockLaw p m))
      ≤ Real.sqrt (2 * ((J : ℝ) * (σ ^ 2 / m) + (J : ℝ) * (σ ^ 2 / m))) := Real.sqrt_le_sqrt hab
    _ = Real.sqrt (4 * (σ ^ 2 * ((J : ℝ) / m))) := by rw [h2]
    _ = 2 * (σ * Real.sqrt ((J : ℝ) / m)) := hsq

lemma expected_gap_sqrt {m J : ℕ} (g : ℝ → Ω → ℝ) (f : ℝ → ℝ) (xstar L σ ε : ℝ)
    (H : Hyps m g f σ p) (hσ : 0 ≤ σ)
    (hconv : ConvexOn ℝ univ f) (hmin : IsMinOn f univ xstar)
    (hsmooth : ∀ x ∈ Icc (x0 - R) (x0 + R), f x - f xstar ≤ L / 2 * (x - xstar) ^ 2)
    (hL : 0 < L) (hR : x0 - R ≤ x0 + R) (hx : xstar ∈ Icc (x0 - R) (x0 + R)) (hJ : 1 ≤ J)
    (hbound : L / 2 * (2 * R * ((2:ℝ) / 3) ^ (J - 1)) ^ 2
      + 3 * (2 * σ * Real.sqrt ((J : ℝ) / m)) ≤ ε) :
    Integrable (fun β : ℕ → Fin m → Ω => f (champAt R x0 m g β J) - f xstar) (blockLaw p m) ∧
      (∫ β : ℕ → Fin m → Ω, f (champAt R x0 m g β J) - f xstar ∂(blockLaw p m)) ≤ ε := by
  have hshrink : 0 ≤ L / 2 * (2 * R * ((2:ℝ) / 3) ^ (J - 1)) ^ 2 := by positivity
  have hpt (β : ℕ → Fin m → Ω) : f (champAt R x0 m g β J) - f xstar
      ≤ L / 2 * (2 * R * ((2:ℝ) / 3) ^ (J - 1)) ^ 2 + 3 * Real.sqrt (aggSq R x0 m g f β J) := by
    have hs : ∀ j : ℕ, j < J → lvlErr R x0 (V R x0 m g β) f j
        ≤ Real.sqrt (aggSq R x0 m g f β J) := fun j hj => lvlErr_le_sqrt_aggSq R x0 m g f β J j hj
    have h1 := line_search_gap_le_delta R x0 (v := V R x0 m g β) (f := f) (xstar := xstar) (L := L)
      hconv hmin hsmooth hL hR hx hJ hs
    have hchamp : champAt R x0 m g β J = (runState R x0 (V R x0 m g β) J).champ :=
      congrArg State.champ (runState_V R x0 m g β J).symm
    rw [← hchamp] at h1
    exact h1
  have hsqrtInt : Integrable (fun β : ℕ → Fin m → Ω => Real.sqrt (aggSq R x0 m g f β J))
      (blockLaw p m) := integrable_sqrt_aggSq R x0 m g f σ H J
  have hright : Integrable
      (fun β : ℕ → Fin m → Ω => L / 2 * (2 * R * ((2:ℝ) / 3) ^ (J - 1)) ^ 2
        + 3 * Real.sqrt (aggSq R x0 m g f β J)) (blockLaw p m) :=
    (integrable_const _).add ((hsqrtInt.const_mul 3).congr
      (ae_of_all _ fun β => by ring))
  have hInt : Integrable (fun β : ℕ → Fin m → Ω => f (champAt R x0 m g β J) - f xstar)
      (blockLaw p m) := by
    refine Integrable.mono' hright
      ((measurable_gap R x0 m g f xstar H.hfm H.hg J).aestronglyMeasurable) ?_
    filter_upwards with β
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hmin (Set.mem_univ _)))]
    exact hpt β
  refine ⟨hInt, ?_⟩
  calc (∫ β : ℕ → Fin m → Ω, f (champAt R x0 m g β J) - f xstar ∂(blockLaw p m))
      ≤ ∫ β : ℕ → Fin m → Ω,
          (L / 2 * (2 * R * ((2:ℝ) / 3) ^ (J - 1)) ^ 2 + 3 * Real.sqrt (aggSq R x0 m g f β J))
            ∂(blockLaw p m) := integral_mono hInt hright (fun β => hpt β)
    _ = L / 2 * (2 * R * ((2:ℝ) / 3) ^ (J - 1)) ^ 2
        + 3 * ∫ β : ℕ → Fin m → Ω, Real.sqrt (aggSq R x0 m g f β J) ∂(blockLaw p m) := by
      refine Eq.trans (integral_add (integrable_const _) (hsqrtInt.const_mul 3)) ?_
      simp only [integral_const, probReal_univ, one_smul, integral_const_mul]
    _ ≤ L / 2 * (2 * R * ((2:ℝ) / 3) ^ (J - 1)) ^ 2
        + 3 * (2 * (σ * Real.sqrt ((J : ℝ) / m))) := by
      refine add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left (integral_sqrt_aggSq_le R x0 m g f σ H hσ J)
          (by norm_num : (0 : ℝ) ≤ 3))
    _ ≤ ε := by
      have h3 : (3 : ℝ) * (2 * σ * Real.sqrt ((J : ℝ) / m))
          = 3 * (2 * (σ * Real.sqrt ((J : ℝ) / m))) := by ring
      linarith

end Oracle

end OracleTemplate.LineSearch

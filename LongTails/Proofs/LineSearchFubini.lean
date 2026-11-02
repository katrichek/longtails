import LongTails.Proofs.LineSearchMeasurable
import LongTails.Proofs.LineSearchMoments
import LongTails.Proofs.AdaptiveIID

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal

namespace OracleTemplate.LineSearch

variable {Ω : Type}

/-- Block mean error at a point fixed by the first coordinate of the product space. -/
noncomputable def blkErr {n m : ℕ} (g : ℝ → Ω → ℝ) (f : ℝ → ℝ)
    (c : (Fin n → Fin m → Ω) → ℝ) (z : (Fin n → Fin m → Ω) × (Fin m → Ω)) : ℝ :=
  |(∑ k : Fin m, g (c z.1) (z.2 k)) / (m : ℝ) - f (c z.1)|

lemma blkErr_nonneg {n m : ℕ} (g : ℝ → Ω → ℝ) (f : ℝ → ℝ)
    (c : (Fin n → Fin m → Ω) → ℝ) (z : (Fin n → Fin m → Ω) × (Fin m → Ω)) :
    0 ≤ blkErr g f c z := abs_nonneg _

section Oracle

variable (R x0 : ℝ)

/-- The state at level `j` only depends on the blocks before level `j`. -/
lemma pairRun_state_combine {m : ℕ} (g : ℝ → Ω → ℝ) (t : ℕ → Fin m → Ω)
    (β : ℕ → Fin m → Ω) (j : ℕ) :
    (pairRun R x0 m g (combine (fun i : Fin (2 * j) => β i) t) j).1
      = (pairRun R x0 m g β j).1 :=
  pairRun_state_congr R x0 m g (fun _ hi => combine_lt (fun i => β i) t hi)

lemma loAt_combine {m : ℕ} (g : ℝ → Ω → ℝ) (t : ℕ → Fin m → Ω) (β : ℕ → Fin m → Ω) (j : ℕ) :
    loAt R x0 m g (combine (fun i : Fin (2 * j) => β i) t) j = loAt R x0 m g β j := by
  show (pairRun R x0 m g (combine (fun i : Fin (2 * j) => β i) t) j).1.lo
      = (pairRun R x0 m g β j).1.lo
  rw [pairRun_state_combine R x0 g t β j]

lemma hiAt_combine {m : ℕ} (g : ℝ → Ω → ℝ) (t : ℕ → Fin m → Ω) (β : ℕ → Fin m → Ω) (j : ℕ) :
    hiAt R x0 m g (combine (fun i : Fin (2 * j) => β i) t) j = hiAt R x0 m g β j := by
  show (pairRun R x0 m g (combine (fun i : Fin (2 * j) => β i) t) j).1.hi
      = (pairRun R x0 m g β j).1.hi
  rw [pairRun_state_combine R x0 g t β j]

lemma leftAt_combine {m : ℕ} (g : ℝ → Ω → ℝ) (t : ℕ → Fin m → Ω) (β : ℕ → Fin m → Ω) (j : ℕ) :
    leftAt R x0 m g (combine (fun i : Fin (2 * j) => β i) t) j = leftAt R x0 m g β j := by
  show (pairRun R x0 m g (combine (fun i : Fin (2 * j) => β i) t) j).1.lo
        + ((pairRun R x0 m g (combine (fun i : Fin (2 * j) => β i) t) j).1.hi
          - (pairRun R x0 m g (combine (fun i : Fin (2 * j) => β i) t) j).1.lo) / 3
        = (pairRun R x0 m g β j).1.lo
          + ((pairRun R x0 m g β j).1.hi - (pairRun R x0 m g β j).1.lo) / 3
  rw [pairRun_state_combine R x0 g t β j]

lemma rightAt_combine {m : ℕ} (g : ℝ → Ω → ℝ) (t : ℕ → Fin m → Ω) (β : ℕ → Fin m → Ω) (j : ℕ) :
    rightAt R x0 m g (combine (fun i : Fin (2 * j) => β i) t) j = rightAt R x0 m g β j := by
  show (pairRun R x0 m g (combine (fun i : Fin (2 * j) => β i) t) j).1.lo
        + 2 * ((pairRun R x0 m g (combine (fun i : Fin (2 * j) => β i) t) j).1.hi
          - (pairRun R x0 m g (combine (fun i : Fin (2 * j) => β i) t) j).1.lo) / 3
        = (pairRun R x0 m g β j).1.lo
          + 2 * ((pairRun R x0 m g β j).1.hi - (pairRun R x0 m g β j).1.lo) / 3
  rw [pairRun_state_combine R x0 g t β j]

end Oracle

variable [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]

lemma measurable_combine_head {m j : ℕ} (t : ℕ → Fin m → Ω) :
    Measurable (fun a : Fin (2 * j) → Fin m → Ω => combine a t) := by
  refine Measurable.of_eval fun i => ?_
  by_cases hi : i < 2 * j
  · rw [show (fun a : Fin (2 * j) → Fin m → Ω => combine a t i)
        = fun a : Fin (2 * j) → Fin m → Ω => a ⟨i, hi⟩ from funext fun a => combine_lt a t hi]
    exact measurable_pi_apply _
  · rw [show (fun a : Fin (2 * j) → Fin m → Ω => combine a t i)
        = fun _ : Fin (2 * j) → Fin m → Ω => t (i - 2 * j) from funext fun a => dite_eq_right hi]
    exact measurable_const

lemma measurable_blkErr {n m : ℕ} (g : ℝ → Ω → ℝ) (f : ℝ → ℝ)
    (c : (Fin n → Fin m → Ω) → ℝ) (hc : Measurable c) (hfm : Measurable f)
    (hg : Measurable (Function.uncurry g)) : Measurable (blkErr g f c) := by
  have h1 : Measurable (fun z : (Fin n → Fin m → Ω) × (Fin m → Ω) =>
      (∑ k : Fin m, g (c z.1) (z.2 k)) / (m : ℝ) - f (c z.1)) := by
    refine Measurable.sub ?_ ((hfm.comp hc).comp measurable_fst)
    refine Measurable.div ?_ measurable_const
    refine Finset.measurable_sum Finset.univ fun k _ => ?_
    exact hg.comp (Measurable.prodMk (hc.comp measurable_fst)
      ((measurable_pi_apply k : Measurable (fun v : Fin m → Ω => v k)).comp measurable_snd))
  have heq : blkErr g f c
      = (fun x : ℝ => |x|)
        ∘ (fun z : (Fin n → Fin m → Ω) × (Fin m → Ω) =>
          (∑ k : Fin m, g (c z.1) (z.2 k)) / (m : ℝ) - f (c z.1)) := rfl
  rw [heq]
  exact continuous_abs.measurable.comp h1

/-- Fubini step: the block mean error at a point chosen from the past has expectation at most
`σ / sqrt m`. -/
lemma product_block_error_lintegral_le {n m : ℕ} (g : ℝ → Ω → ℝ) (f : ℝ → ℝ) (σ : ℝ)
    (c : (Fin n → Fin m → Ω) → ℝ) (hc : Measurable c) (hfm : Measurable f)
    (hg : Measurable (Function.uncurry g)) (hm : 0 < m) (hσ : 0 ≤ σ)
    (hmean : ∀ x, ∫ z, g x z ∂p = f x)
    (hint : ∀ x, Integrable (g x) p)
    (hsql2 : ∀ x, Integrable (fun z => (g x z - f x) ^ 2) p)
    (hvar : ∀ x, ∫ z, (g x z - f x) ^ 2 ∂p ≤ σ ^ 2) :
    ∫⁻ z : (Fin n → Fin m → Ω) × (Fin m → Ω), ENNReal.ofReal (blkErr g f c z)
        ∂((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin m => p).prod
          (Measure.pi fun _ : Fin m => p)) ≤ ENNReal.ofReal (σ / Real.sqrt m) := by
  set μ : Measure (Fin n → Fin m → Ω) := Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin m => p
    with hμ
  set ν : Measure (Fin m → Ω) := Measure.pi fun _ : Fin m => p with hν
  have hG : Measurable (blkErr g f c) := measurable_blkErr g f c hc hfm hg
  have hgf (a : Fin n → Fin m → Ω) : Measurable (fun z : Ω => g (c a) z) :=
    hg.comp (Measurable.prodMk measurable_const measurable_id)
  have hInt (a : Fin n → Fin m → Ω) :
      Integrable (fun y : Fin m → Ω => blkErr g f c (a, y)) ν := by
    have hk (k : Fin m) : Integrable (fun y : Fin m → Ω => g (c a) (y k)) ν := by
      have he : Measure.map (fun y : Fin m → Ω => y k) ν = p :=
        (measurePreserving_eval (μ := fun _ : Fin m => p) k).map_eq
      have h1 : Integrable (fun z : Ω => g (c a) z)
          (Measure.map (fun y : Fin m → Ω => y k) ν) := by
        rw [he]
        exact hint (c a)
      exact h1.comp_measurable (measurable_pi_apply k)
    have hsum : Integrable (fun y : Fin m → Ω => ∑ k : Fin m, g (c a) (y k)) ν :=
      integrable_finsetSum Finset.univ fun k _ => hk k
    have h2 : Integrable (fun y : Fin m → Ω =>
        (∑ k : Fin m, g (c a) (y k)) / (m : ℝ) - f (c a)) ν :=
      (hsum.div_const _).sub (integrable_const _)
    show Integrable (fun y : Fin m → Ω =>
        |(∑ k : Fin m, g (c a) (y k)) / (m : ℝ) - f (c a)|) ν
    exact h2.abs
  have hinder (a : Fin n → Fin m → Ω) :
      ∫ y : Fin m → Ω, blkErr g f c (a, y) ∂ν ≤ σ / Real.sqrt m :=
    block_mean_abs_le (Ω := Ω) (p := p) hm (g (c a)) (f (c a)) σ hσ (hgf a) (hint (c a))
      (hsql2 (c a)) (hmean (c a)) (hvar (c a))
  have hfibre (a : Fin n → Fin m → Ω) :
      ∫⁻ y : Fin m → Ω, ENNReal.ofReal (blkErr g f c (a, y)) ∂ν
        ≤ ENNReal.ofReal (σ / Real.sqrt m) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hInt a)
      (Filter.Eventually.of_forall fun y => blkErr_nonneg g f c (a, y))]
    exact ENNReal.ofReal_le_ofReal (hinder a)
  have hprod : ∫⁻ z : (Fin n → Fin m → Ω) × (Fin m → Ω), ENNReal.ofReal (blkErr g f c z) ∂(μ.prod ν)
      = ∫⁻ a : Fin n → Fin m → Ω, ∫⁻ y : Fin m → Ω, ENNReal.ofReal (blkErr g f c (a, y)) ∂ν ∂μ :=
    lintegral_prod (fun z : (Fin n → Fin m → Ω) × (Fin m → Ω) => ENNReal.ofReal (blkErr g f c z))
      ((ENNReal.measurable_ofReal.comp hG).aemeasurable)
  calc ∫⁻ z : (Fin n → Fin m → Ω) × (Fin m → Ω), ENNReal.ofReal (blkErr g f c z) ∂(μ.prod ν)
      = ∫⁻ a : Fin n → Fin m → Ω, ∫⁻ y : Fin m → Ω, ENNReal.ofReal (blkErr g f c (a, y)) ∂ν ∂μ :=
        hprod
    _ ≤ ∫⁻ _a : Fin n → Fin m → Ω, ENNReal.ofReal (σ / Real.sqrt m) ∂μ :=
        lintegral_mono (fun a => hfibre a)
    _ = ENNReal.ofReal (σ / Real.sqrt m) * μ Set.univ := lintegral_const _
    _ = ENNReal.ofReal (σ / Real.sqrt m) * 1 := by rw [measure_univ (μ := μ)]
    _ = ENNReal.ofReal (σ / Real.sqrt m) := by simp

section Oracle

variable (R x0 : ℝ)

/-- The first `2 * j` blocks together with block `2 * j + r` are independent standard blocks. -/
lemma map_prefix_block_preserving {m : ℕ} (p : Measure Ω) [IsProbabilityMeasure p] (j r : ℕ) :
    MeasurePreserving
      (fun β : ℕ → Fin m → Ω => ((fun i : Fin (2 * j) => β i), β (2 * j + r)))
      (blockLaw p m)
      ((Measure.pi fun _ : Fin (2 * j) => Measure.pi fun _ : Fin m => p).prod
        (Measure.pi fun _ : Fin m => p)) := by
  have heval : MeasurePreserving (fun t : ℕ → Fin m → Ω => t r)
      (Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin m => p)
      (Measure.pi fun _ : Fin m => p) := by
    refine ⟨by fun_prop, ?_⟩
    exact Measure.infinitePi_map_eval _ _
  have h := ((MeasurePreserving.id (Measure.pi fun _ : Fin (2 * j) =>
      Measure.pi fun _ : Fin m => p)).prod heval).comp
    (OracleTemplate.StochasticGeneralized.splitStream_preserving (Measure.pi fun _ : Fin m => p)
      (2 * j))
  show MeasurePreserving ((fun z : (Fin (2 * j) → Fin m → Ω) × (ℕ → Fin m → Ω) =>
      (z.1, z.2 r)) ∘ OracleTemplate.StochasticGeneralized.splitStream (2 * j)) _ _
  convert h using 1
  · funext β
    rfl
  · rfl

/-- Expected block error of the left query of one level of the line search. -/
lemma left_error_lintegral_le {m : ℕ} (g : ℝ → Ω → ℝ) (f : ℝ → ℝ) (σ : ℝ)
    (hfm : Measurable f) (hg : Measurable (Function.uncurry g))
    (hm : 0 < m) (hσ : 0 ≤ σ) (hmean : ∀ x, ∫ z, g x z ∂p = f x)
    (hint : ∀ x, Integrable (g x) p)
    (hsql2 : ∀ x, Integrable (fun z => (g x z - f x) ^ 2) p)
    (hvar : ∀ x, ∫ z, (g x z - f x) ^ 2 ∂p ≤ σ ^ 2) (j : ℕ) :
    ∫⁻ β : ℕ → Fin m → Ω,
        ENNReal.ofReal |estLeft R x0 m g β j - f (leftAt R x0 m g β j)| ∂(blockLaw p m)
      ≤ ENNReal.ofReal (σ / Real.sqrt m) := by
  let hn : Nonempty Ω := nonempty_of_probability (p := p)
  let t0 : ℕ → Fin m → Ω := fun _ _ => Classical.choice hn
  let c : (Fin (2 * j) → Fin m → Ω) → ℝ := fun a => leftAt R x0 m g (combine a t0) j
  have hc : Measurable c := (measurable_leftAt R x0 m g hg j).comp (measurable_combine_head t0)
  have hG : Measurable (blkErr g f c) := measurable_blkErr g f c hc hfm hg
  have hpt (β : ℕ → Fin m → Ω) :
      blkErr g f c ((fun i : Fin (2 * j) => β i), β (2 * j))
        = |estLeft R x0 m g β j - f (leftAt R x0 m g β j)| := by
    simp only [blkErr, c, estLeft]
    rw [leftAt_combine R x0 g t0 β j]
  calc ∫⁻ β : ℕ → Fin m → Ω, ENNReal.ofReal |estLeft R x0 m g β j - f (leftAt R x0 m g β j)|
        ∂(blockLaw p m)
      = ∫⁻ β, ENNReal.ofReal (blkErr g f c ((fun i : Fin (2 * j) => β i), β (2 * j)))
          ∂(blockLaw p m) := by
        congr with β
        rw [hpt β]
      _ = ∫⁻ z : (Fin (2 * j) → Fin m → Ω) × (Fin m → Ω), ENNReal.ofReal (blkErr g f c z)
          ∂((Measure.pi fun _ : Fin (2 * j) => Measure.pi fun _ : Fin m => p).prod
            (Measure.pi fun _ : Fin m => p)) := by
        rw [← (map_prefix_block_preserving p j 0).map_eq]
        exact (lintegral_map (hf := ENNReal.measurable_ofReal.comp hG)
          (hg := (map_prefix_block_preserving p j 0).measurable)).symm
      _ ≤ ENNReal.ofReal (σ / Real.sqrt m) :=
        product_block_error_lintegral_le g f σ c hc hfm hg hm hσ hmean hint hsql2 hvar

/-- Expected block error of the right query of one level of the line search. -/
lemma right_error_lintegral_le {m : ℕ} (g : ℝ → Ω → ℝ) (f : ℝ → ℝ) (σ : ℝ)
    (hfm : Measurable f) (hg : Measurable (Function.uncurry g))
    (hm : 0 < m) (hσ : 0 ≤ σ) (hmean : ∀ x, ∫ z, g x z ∂p = f x)
    (hint : ∀ x, Integrable (g x) p)
    (hsql2 : ∀ x, Integrable (fun z => (g x z - f x) ^ 2) p)
    (hvar : ∀ x, ∫ z, (g x z - f x) ^ 2 ∂p ≤ σ ^ 2) (j : ℕ) :
    ∫⁻ β : ℕ → Fin m → Ω,
        ENNReal.ofReal |estRight R x0 m g β j - f (rightAt R x0 m g β j)| ∂(blockLaw p m)
      ≤ ENNReal.ofReal (σ / Real.sqrt m) := by
  let hn : Nonempty Ω := nonempty_of_probability (p := p)
  let t0 : ℕ → Fin m → Ω := fun _ _ => Classical.choice hn
  let c : (Fin (2 * j) → Fin m → Ω) → ℝ := fun a => rightAt R x0 m g (combine a t0) j
  have hc : Measurable c := (measurable_rightAt R x0 m g hg j).comp (measurable_combine_head t0)
  have hG : Measurable (blkErr g f c) := measurable_blkErr g f c hc hfm hg
  have hpt (β : ℕ → Fin m → Ω) :
      blkErr g f c ((fun i : Fin (2 * j) => β i), β (2 * j + 1))
        = |estRight R x0 m g β j - f (rightAt R x0 m g β j)| := by
    simp only [blkErr, c, estRight]
    rw [rightAt_combine R x0 g t0 β j]
  calc ∫⁻ β : ℕ → Fin m → Ω, ENNReal.ofReal |estRight R x0 m g β j - f (rightAt R x0 m g β j)|
        ∂(blockLaw p m)
      = ∫⁻ β, ENNReal.ofReal (blkErr g f c ((fun i : Fin (2 * j) => β i), β (2 * j + 1)))
          ∂(blockLaw p m) := by
        congr with β
        rw [hpt β]
      _ = ∫⁻ z : (Fin (2 * j) → Fin m → Ω) × (Fin m → Ω), ENNReal.ofReal (blkErr g f c z)
          ∂((Measure.pi fun _ : Fin (2 * j) => Measure.pi fun _ : Fin m => p).prod
            (Measure.pi fun _ : Fin m => p)) := by
        rw [← (map_prefix_block_preserving p j 1).map_eq]
        exact (lintegral_map (hf := ENNReal.measurable_ofReal.comp hG)
          (hg := (map_prefix_block_preserving p j 1).measurable)).symm
      _ ≤ ENNReal.ofReal (σ / Real.sqrt m) :=
        product_block_error_lintegral_le g f σ c hc hfm hg hm hσ hmean hint hsql2 hvar

/-- Expected total error of one level of the line search. -/
lemma level_errors_integral_le {m : ℕ} (g : ℝ → Ω → ℝ) (f : ℝ → ℝ) (σ : ℝ)
    (hfm : Measurable f) (hg : Measurable (Function.uncurry g))
    (hm : 0 < m) (hσ : 0 ≤ σ) (hmean : ∀ x, ∫ z, g x z ∂p = f x)
    (hint : ∀ x, Integrable (g x) p)
    (hsql2 : ∀ x, Integrable (fun z => (g x z - f x) ^ 2) p)
    (hvar : ∀ x, ∫ z, (g x z - f x) ^ 2 ∂p ≤ σ ^ 2) (j : ℕ) :
    ∫ β : ℕ → Fin m → Ω,
        (|estLeft R x0 m g β j - f (leftAt R x0 m g β j)|
          + |estRight R x0 m g β j - f (rightAt R x0 m g β j)|) ∂(blockLaw p m)
      ≤ 2 * (σ / Real.sqrt m) := by
  have h1 := left_error_lintegral_le R x0 g f σ hfm hg hm hσ hmean hint hsql2 hvar j
  have h2 := right_error_lintegral_le R x0 g f σ hfm hg hm hσ hmean hint hsql2 hvar j
  have hml : Measurable (fun β : ℕ → Fin m → Ω =>
      |estLeft R x0 m g β j - f (leftAt R x0 m g β j)|) := by
    have hu := measurable_estLeft R x0 m g hg j
    have hc := measurable_leftAt R x0 m g hg j
    fun_prop
  have hmr : Measurable (fun β : ℕ → Fin m → Ω =>
      |estRight R x0 m g β j - f (rightAt R x0 m g β j)|) := by
    have hu := measurable_estRight R x0 m g hg j
    have hc := measurable_rightAt R x0 m g hg j
    fun_prop
  have hK : AEStronglyMeasurable (fun β : ℕ → Fin m → Ω =>
      |estLeft R x0 m g β j - f (leftAt R x0 m g β j)|
        + |estRight R x0 m g β j - f (rightAt R x0 m g β j)|) (blockLaw p m) :=
    AEStronglyMeasurable.add hml.aestronglyMeasurable hmr.aestronglyMeasurable
  have heq : (fun β : ℕ → Fin m → Ω => ENNReal.ofReal
      (|estLeft R x0 m g β j - f (leftAt R x0 m g β j)|
        + |estRight R x0 m g β j - f (rightAt R x0 m g β j)|))
      = (fun β : ℕ → Fin m → Ω => ENNReal.ofReal (|estLeft R x0 m g β j
          - f (leftAt R x0 m g β j)|))
        + (fun β : ℕ → Fin m → Ω => ENNReal.ofReal (|estRight R x0 m g β j
          - f (rightAt R x0 m g β j)|)) := by
    funext β
    exact ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
  have hlint : ∫⁻ β : ℕ → Fin m → Ω, ENNReal.ofReal
      (|estLeft R x0 m g β j - f (leftAt R x0 m g β j)|
        + |estRight R x0 m g β j - f (rightAt R x0 m g β j)|) ∂(blockLaw p m)
      ≤ ENNReal.ofReal (σ / Real.sqrt m) + ENNReal.ofReal (σ / Real.sqrt m) := by
    refine le_of_eq_of_le ?_ (add_le_add h1 h2)
    refine (congrArg (fun F : (ℕ → Fin m → Ω) → ℝ≥0∞ => ∫⁻ β, F β ∂(blockLaw p m)) heq).trans ?_
    exact lintegral_add_right'
      (fun β : ℕ → Fin m → Ω =>
        ENNReal.ofReal |estLeft R x0 m g β j - f (leftAt R x0 m g β j)|)
      ((ENNReal.measurable_ofReal.comp hmr).aemeasurable)
  calc ∫ β : ℕ → Fin m → Ω,
          (|estLeft R x0 m g β j - f (leftAt R x0 m g β j)|
            + |estRight R x0 m g β j - f (rightAt R x0 m g β j)|) ∂(blockLaw p m)
      = ENNReal.toReal (∫⁻ β : ℕ → Fin m → Ω, ENNReal.ofReal
          (|estLeft R x0 m g β j - f (leftAt R x0 m g β j)|
            + |estRight R x0 m g β j - f (rightAt R x0 m g β j)|) ∂(blockLaw p m)) :=
        integral_eq_lintegral_of_nonneg_ae
          (Filter.Eventually.of_forall fun β => add_nonneg (abs_nonneg _) (abs_nonneg _)) hK
    _ ≤ ENNReal.toReal (ENNReal.ofReal (σ / Real.sqrt m)
          + ENNReal.ofReal (σ / Real.sqrt m)) :=
        (ENNReal.toReal_le_toReal
            (ne_of_lt (lt_of_le_of_lt hlint
              (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩)))
            (ne_of_lt (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩))).mpr hlint
    _ = ENNReal.toReal (ENNReal.ofReal (2 * (σ / Real.sqrt m))) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      congr 1
      linarith
    _ = 2 * (σ / Real.sqrt m) := ENNReal.toReal_ofReal (by positivity)

end Oracle

end OracleTemplate.LineSearch

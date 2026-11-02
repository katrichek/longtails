import LongTails.Proofs.LineSearchCore
import LongTails.Proofs.LineSearchFubini
import LongTails.Proofs.LineSearchMeasurable
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OracleTemplate.LineSearch

open MeasureTheory ENNReal Set

variable {Ω : Type} [MeasurableSpace Ω] {p : Measure Ω} [hp : IsProbabilityMeasure p]
  (R x0 : ℝ)

/-- Pair estimates driven by the block stream. -/
noncomputable def V (m : ℕ) (g : ℝ → Ω → ℝ) (β : ℕ → Fin m → Ω) (j : ℕ) : ℝ × ℝ :=
  (estLeft R x0 m g β j, estRight R x0 m g β j)

lemma runState_V (m : ℕ) (g : ℝ → Ω → ℝ) (β : ℕ → Fin m → Ω) (j : ℕ) :
    runState R x0 (V R x0 m g β) j = (pairRun R x0 m g β j).1 := by
  have hf : (fun i => (pairRun R x0 m g β (i + 1)).2) = V R x0 m g β :=
    funext fun i => (pairRun_pair_succ' R x0 m g β i).symm
  rw [← hf]
  exact (pairRun_state_eq_runState R x0 m g β j).symm

/-- One level error written through the deterministic level error. -/
lemma levelError_eq_lvlErr (m : ℕ) (g : ℝ → Ω → ℝ) (f : ℝ → ℝ) (β : ℕ → Fin m → Ω) (j : ℕ) :
    |estLeft R x0 m g β j - f (leftAt R x0 m g β j)|
      + |estRight R x0 m g β j - f (rightAt R x0 m g β j)| = lvlErr R x0 (V R x0 m g β) f j := by
  have h1 : leftPoint (runState R x0 (V R x0 m g β) j) = leftAt R x0 m g β j := by
    rw [runState_V, leftPoint_eq_leftAt]
  have h2 : rightPoint (runState R x0 (V R x0 m g β) j) = rightAt R x0 m g β j := by
    rw [runState_V, rightPoint_eq_rightAt]
  unfold lvlErr
  rw [h1, h2]
  simp only [V]

/-- Pathwise accuracy of the line search through the block-level estimation errors. -/
lemma gap_le_sum (m : ℕ) (g : ℝ → Ω → ℝ) (f : ℝ → ℝ) (xstar L : ℝ)
    (hconv : ConvexOn ℝ univ f) (hmin : IsMinOn f univ xstar)
    (hsmooth : ∀ x ∈ Icc (x0 - R) (x0 + R), f x - f xstar ≤ L / 2 * (x - xstar) ^ 2)
    (hL : 0 < L) (hR : x0 - R ≤ x0 + R) (hx : xstar ∈ Icc (x0 - R) (x0 + R)) {J : ℕ} (hJ : 1 ≤ J)
    (β : ℕ → Fin m → Ω) :
    f (champAt R x0 m g β J) - f xstar
      ≤ L / 2 * (2 * R * ((2:ℝ) / 3) ^ (J - 1)) ^ 2
        + ∑ j ∈ Finset.range J,
          3 * (|estLeft R x0 m g β j - f (leftAt R x0 m g β j)|
            + |estRight R x0 m g β j - f (rightAt R x0 m g β j)|) := by
  have hchamp : champAt R x0 m g β J = (runState R x0 (V R x0 m g β) J).champ :=
    congrArg State.champ (runState_V R x0 m g β J).symm
  have h := line_search_gap_le R x0 (v := V R x0 m g β) (f := f) (xstar := xstar) (L := L) hconv
    hmin hsmooth hL hR hx hJ
  rw [← hchamp] at h
  have hsum : 3 * ∑ j ∈ Finset.range J, lvlErr R x0 (V R x0 m g β) f j
      = ∑ j ∈ Finset.range J,
          3 * (|estLeft R x0 m g β j - f (leftAt R x0 m g β j)|
            + |estRight R x0 m g β j - f (rightAt R x0 m g β j)|) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← levelError_eq_lvlErr R x0 m g f β j]
  linarith

/-- Measurability of the pathwise gap. -/
lemma measurable_gap (m : ℕ) (g : ℝ → Ω → ℝ) (f : ℝ → ℝ) (xstar : ℝ)
    (hfm : Measurable f) (hg : Measurable (Function.uncurry g)) (J : ℕ) :
    Measurable (fun β : ℕ → Fin m → Ω => f (champAt R x0 m g β J) - f xstar) :=
  (hfm.comp (measurable_champAt R x0 m g hg J)).sub measurable_const

/-- Measurability of one level error. -/
lemma measurable_levelError (m : ℕ) (g : ℝ → Ω → ℝ) (f : ℝ → ℝ)
    (hfm : Measurable f) (hg : Measurable (Function.uncurry g)) (j : ℕ) :
    Measurable (fun β : ℕ → Fin m → Ω => |estLeft R x0 m g β j - f (leftAt R x0 m g β j)|
      + |estRight R x0 m g β j - f (rightAt R x0 m g β j)|) := by
  have hu := measurable_estLeft R x0 m g hg j
  have hc := measurable_leftAt R x0 m g hg j
  have hv := measurable_estRight R x0 m g hg j
  have hw := measurable_rightAt R x0 m g hg j
  fun_prop

/-- Expected error of one level of the line search: two fresh blocks of `m` samples. -/
lemma lintegral_levelError (m : ℕ) (g : ℝ → Ω → ℝ) (f : ℝ → ℝ) (σ : ℝ)
    (hfm : Measurable f) (hg : Measurable (Function.uncurry g))
    (hm : 0 < m) (hσ : 0 ≤ σ) (hmean : ∀ x, ∫ z, g x z ∂p = f x)
    (hint : ∀ x, Integrable (g x) p)
    (hsql2 : ∀ x, Integrable (fun z => (g x z - f x) ^ 2) p)
    (hvar : ∀ x, ∫ z, (g x z - f x) ^ 2 ∂p ≤ σ ^ 2) (j : ℕ) :
    ∫⁻ β : ℕ → Fin m → Ω,
        ENNReal.ofReal (3 * (|estLeft R x0 m g β j - f (leftAt R x0 m g β j)|
            + |estRight R x0 m g β j - f (rightAt R x0 m g β j)|)) ∂(blockLaw p m)
      ≤ ENNReal.ofReal (3 * (2 * (σ / Real.sqrt m))) := by
  have h1 := left_error_lintegral_le R x0 g f σ hfm hg hm hσ hmean hint hsql2 hvar j
  have h2 := right_error_lintegral_le R x0 g f σ hfm hg hm hσ hmean hint hsql2 hvar j
  have hmeasL : Measurable (fun β : ℕ → Fin m → Ω =>
      |estLeft R x0 m g β j - f (leftAt R x0 m g β j)|) := by
    have hu := measurable_estLeft R x0 m g hg j
    have hc := measurable_leftAt R x0 m g hg j
    fun_prop
  have hmeasR : Measurable (fun β : ℕ → Fin m → Ω =>
      |estRight R x0 m g β j - f (rightAt R x0 m g β j)|) := by
    have hu := measurable_estRight R x0 m g hg j
    have hc := measurable_rightAt R x0 m g hg j
    fun_prop
  have hfa : AEMeasurable (fun β : ℕ → Fin m → Ω =>
      ENNReal.ofReal |estLeft R x0 m g β j - f (leftAt R x0 m g β j)|) (blockLaw p m) :=
    (ENNReal.measurable_ofReal.comp hmeasL).aemeasurable
  have hsum : ∫⁻ β : ℕ → Fin m → Ω,
        ENNReal.ofReal (|estLeft R x0 m g β j - f (leftAt R x0 m g β j)|
            + |estRight R x0 m g β j - f (rightAt R x0 m g β j)|) ∂(blockLaw p m)
      ≤ ENNReal.ofReal (2 * (σ / Real.sqrt m)) := by
    refine le_of_eq_of_le (lintegral_congr fun β => ENNReal.ofReal_add (abs_nonneg _)
        (abs_nonneg _)) ?_
    rw [lintegral_add_left' hfa (fun β : ℕ → Fin m → Ω =>
      ENNReal.ofReal |estRight R x0 m g β j - f (rightAt R x0 m g β j)|)]
    have hsq : 0 ≤ σ / Real.sqrt m := by positivity
    rw [two_mul, ENNReal.ofReal_add hsq hsq]
    exact add_le_add h1 h2

  calc ∫⁻ β : ℕ → Fin m → Ω,
          ENNReal.ofReal (3 * (|estLeft R x0 m g β j - f (leftAt R x0 m g β j)|
              + |estRight R x0 m g β j - f (rightAt R x0 m g β j)|)) ∂(blockLaw p m)
      = ∫⁻ β : ℕ → Fin m → Ω,
          ENNReal.ofReal 3 * ENNReal.ofReal (|estLeft R x0 m g β j - f (leftAt R x0 m g β j)|
              + |estRight R x0 m g β j - f (rightAt R x0 m g β j)|) ∂(blockLaw p m) := by
        congr with β
        exact ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)
    _ = ENNReal.ofReal 3 * ∫⁻ β : ℕ → Fin m → Ω,
          ENNReal.ofReal (|estLeft R x0 m g β j - f (leftAt R x0 m g β j)|
              + |estRight R x0 m g β j - f (rightAt R x0 m g β j)|) ∂(blockLaw p m) := by
        rw [lintegral_congr fun β => mul_comm _ _,
          lintegral_mul_const' _ _ ENNReal.ofReal_lt_top.ne, mul_comm]
    _ ≤ ENNReal.ofReal 3 * ENNReal.ofReal (2 * (σ / Real.sqrt m)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ENNReal.ofReal (3 * (2 * (σ / Real.sqrt m))) :=
        (ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)).symm

/-- Expected accuracy of the line search after `J` levels with `m` samples per query. -/
lemma lintegral_gap_le (m : ℕ) (g : ℝ → Ω → ℝ) (f : ℝ → ℝ) (xstar L σ : ℝ)
    (hfm : Measurable f) (hg : Measurable (Function.uncurry g))
    (hm : 0 < m) (hσ : 0 ≤ σ) (hmean : ∀ x, ∫ z, g x z ∂p = f x)
    (hint : ∀ x, Integrable (g x) p)
    (hsql2 : ∀ x, Integrable (fun z => (g x z - f x) ^ 2) p)
    (hvar : ∀ x, ∫ z, (g x z - f x) ^ 2 ∂p ≤ σ ^ 2)
    (hconv : ConvexOn ℝ univ f) (hmin : IsMinOn f univ xstar)
    (hsmooth : ∀ x ∈ Icc (x0 - R) (x0 + R), f x - f xstar ≤ L / 2 * (x - xstar) ^ 2)
    (hL : 0 < L) (hR : x0 - R ≤ x0 + R) (hx : xstar ∈ Icc (x0 - R) (x0 + R)) {J : ℕ} (hJ : 1 ≤ J) :
    ∫⁻ β : ℕ → Fin m → Ω, ENNReal.ofReal (f (champAt R x0 m g β J) - f xstar) ∂(blockLaw p m)
      ≤ ENNReal.ofReal (L / 2 * (2 * R * ((2:ℝ) / 3) ^ (J - 1)) ^ 2
        + (J : ℝ) * (3 * (2 * (σ / Real.sqrt m)))) := by
  have hA : 0 ≤ L / 2 * (2 * R * ((2:ℝ) / 3) ^ (J - 1)) ^ 2 := by positivity
  have hmeas := measurable_gap R x0 m g f xstar hfm hg J
  have hle : ∀ β : ℕ → Fin m → Ω, f (champAt R x0 m g β J) - f xstar
      ≤ L / 2 * (2 * R * ((2:ℝ) / 3) ^ (J - 1)) ^ 2
        + ∑ j ∈ Finset.range J,
          3 * (|estLeft R x0 m g β j - f (leftAt R x0 m g β j)|
            + |estRight R x0 m g β j - f (rightAt R x0 m g β j)|) :=
    fun β => gap_le_sum R x0 m g f xstar L hconv hmin hsmooth hL hR hx hJ β
  calc ∫⁻ β : ℕ → Fin m → Ω, ENNReal.ofReal (f (champAt R x0 m g β J) - f xstar) ∂(blockLaw p m)
      ≤ ∫⁻ β : ℕ → Fin m → Ω,
          ENNReal.ofReal (L / 2 * (2 * R * ((2:ℝ) / 3) ^ (J - 1)) ^ 2
              + ∑ j ∈ Finset.range J,
                3 * (|estLeft R x0 m g β j - f (leftAt R x0 m g β j)|
                  + |estRight R x0 m g β j - f (rightAt R x0 m g β j)|)) ∂(blockLaw p m) :=
        lintegral_mono fun β => ENNReal.ofReal_le_ofReal (hle β)
    _ = ∫⁻ β : ℕ → Fin m → Ω,
          ENNReal.ofReal (L / 2 * (2 * R * ((2:ℝ) / 3) ^ (J - 1)) ^ 2)
            + ENNReal.ofReal (∑ j ∈ Finset.range J,
              3 * (|estLeft R x0 m g β j - f (leftAt R x0 m g β j)|
                + |estRight R x0 m g β j - f (rightAt R x0 m g β j)|)) ∂(blockLaw p m) :=
        lintegral_congr fun β => ENNReal.ofReal_add hA (by positivity)
    _ = ENNReal.ofReal (L / 2 * (2 * R * ((2:ℝ) / 3) ^ (J - 1)) ^ 2)
        + ∫⁻ β : ℕ → Fin m → Ω,
            ENNReal.ofReal (∑ j ∈ Finset.range J,
              3 * (|estLeft R x0 m g β j - f (leftAt R x0 m g β j)|
                + |estRight R x0 m g β j - f (rightAt R x0 m g β j)|)) ∂(blockLaw p m) := by
        have hc : AEMeasurable (fun _ : ℕ → Fin m → Ω =>
            ENNReal.ofReal (L / 2 * (2 * R * ((2:ℝ) / 3) ^ (J - 1)) ^ 2)) (blockLaw p m) :=
          measurable_const.aemeasurable
        rw [lintegral_add_left' hc (fun β : ℕ → Fin m → Ω => ENNReal.ofReal
            (∑ j ∈ Finset.range J,
              3 * (|estLeft R x0 m g β j - f (leftAt R x0 m g β j)|
                + |estRight R x0 m g β j - f (rightAt R x0 m g β j)|)))]
        rw [lintegral_const, measure_univ, mul_one]
    _ = ENNReal.ofReal (L / 2 * (2 * R * ((2:ℝ) / 3) ^ (J - 1)) ^ 2)
        + ∑ j ∈ Finset.range J,
            ∫⁻ β : ℕ → Fin m → Ω,
              ENNReal.ofReal (3 * (|estLeft R x0 m g β j - f (leftAt R x0 m g β j)|
                + |estRight R x0 m g β j - f (rightAt R x0 m g β j)|)) ∂(blockLaw p m) := by
        refine congrArg (fun t : ℝ≥0∞ =>
            ENNReal.ofReal (L / 2 * (2 * R * ((2:ℝ) / 3) ^ (J - 1)) ^ 2) + t) ?_
        refine Eq.trans (lintegral_congr fun β => ENNReal.ofReal_sum_of_nonneg (fun j _ =>
          by positivity)) ?_
        refine lintegral_finsetSum' _ (fun j _ => ?_)
        have hme : Measurable (fun β : ℕ → Fin m → Ω =>
            |estLeft R x0 m g β j - f (leftAt R x0 m g β j)|
              + |estRight R x0 m g β j - f (rightAt R x0 m g β j)|) :=
          measurable_levelError R x0 m g f hfm hg j
        exact (ENNReal.measurable_ofReal.comp (measurable_const.mul hme)).aemeasurable
    _ ≤ ENNReal.ofReal (L / 2 * (2 * R * ((2:ℝ) / 3) ^ (J - 1)) ^ 2)
        + ∑ j ∈ Finset.range J,
            ENNReal.ofReal (3 * (2 * (σ / Real.sqrt m))) :=
        add_le_add (le_refl _) (Finset.sum_le_sum fun j _ =>
          lintegral_levelError R x0 m g f σ hfm hg hm hσ hmean hint hsql2 hvar j)
    _ = ENNReal.ofReal (L / 2 * (2 * R * ((2:ℝ) / 3) ^ (J - 1)) ^ 2
        + (J : ℝ) * (3 * (2 * (σ / Real.sqrt m)))) := by
        have hc : 0 ≤ (3 : ℝ) * (2 * (σ / Real.sqrt m)) := by positivity
        have hj : 0 ≤ (J : ℝ) := by positivity
        have hjc : ENNReal.ofReal ((J : ℝ) * (3 * (2 * (σ / Real.sqrt m))))
            = (J : ℝ≥0∞) * ENNReal.ofReal (3 * (2 * (σ / Real.sqrt m))) := by
          rw [ENNReal.ofReal_mul hj]
          refine congrArg (fun t => t * ENNReal.ofReal (3 * (2 * (σ / Real.sqrt m)))) ?_
          norm_cast
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ENNReal.ofReal_add hA (by positivity), hjc]

/-- Expected accuracy of the line search after `J` levels with `m` samples per query. -/
lemma expected_gap (m : ℕ) (g : ℝ → Ω → ℝ) (f : ℝ → ℝ) (xstar L σ ε : ℝ)
    (hfm : Measurable f) (hg : Measurable (Function.uncurry g))
    (hm : 0 < m) (hσ : 0 ≤ σ) (hmean : ∀ x, ∫ z, g x z ∂p = f x)
    (hint : ∀ x, Integrable (g x) p)
    (hsql2 : ∀ x, Integrable (fun z => (g x z - f x) ^ 2) p)
    (hvar : ∀ x, ∫ z, (g x z - f x) ^ 2 ∂p ≤ σ ^ 2)
    (hconv : ConvexOn ℝ univ f) (hmin : IsMinOn f univ xstar)
    (hsmooth : ∀ x ∈ Icc (x0 - R) (x0 + R), f x - f xstar ≤ L / 2 * (x - xstar) ^ 2)
    (hL : 0 < L) (hR : x0 - R ≤ x0 + R) (hx : xstar ∈ Icc (x0 - R) (x0 + R)) {J : ℕ} (hJ : 1 ≤ J)
    (hbound : L / 2 * (2 * R * ((2:ℝ) / 3) ^ (J - 1)) ^ 2
        + (J : ℝ) * (3 * (2 * (σ / Real.sqrt m))) ≤ ε) :
    Integrable (fun β : ℕ → Fin m → Ω => f (champAt R x0 m g β J) - f xstar) (blockLaw p m) ∧
      (∫ β : ℕ → Fin m → Ω, f (champAt R x0 m g β J) - f xstar ∂(blockLaw p m)) ≤ ε := by
  have hmeas := measurable_gap R x0 m g f xstar hfm hg J
  have hnn : 0 ≤ᵐ[blockLaw p m] fun β : ℕ → Fin m → Ω => f (champAt R x0 m g β J) - f xstar :=
    Filter.Eventually.of_forall fun β =>
      sub_nonneg.mpr (hmin (Set.mem_univ _))
  have hlint := lintegral_gap_le R x0 m g f xstar L σ hfm hg hm hσ hmean hint hsql2 hvar hconv hmin
    hsmooth hL hR hx hJ
  refine ⟨⟨hmeas.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal hnn).mpr (lt_of_le_of_lt hlint ENNReal.ofReal_lt_top)⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal (le_trans (by positivity) hbound) ?_
  exact le_trans hlint (ENNReal.ofReal_le_ofReal hbound)

end OracleTemplate.LineSearch

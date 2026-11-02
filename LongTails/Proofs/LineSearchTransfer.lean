import LongTails.Proofs.LineSearchExecution
import LongTails.Proofs.LineSearchMeasurable
import LongTails.Proofs.LineSearchSharpL2
import LongTails.Proofs.IIDBlocks
import LongTails.Proofs.ZerothOrderEstimator

namespace OracleTemplate.LineSearch

open MeasureTheory ProbabilityTheory Set

variable {Ω : Type} [MeasurableSpace Ω]

/-- Level blocks of a raw stream of samples. -/
noncomputable def toBlocks (m : ℕ) (ξ : ℕ → Ω) : ℕ → Fin m → Ω := fun j k => ξ (j * m + k.val)

lemma measurable_toBlocks (m : ℕ) : Measurable (toBlocks m : (ℕ → Ω) → ℕ → Fin m → Ω) :=
  measurable_pi_iff.mpr fun j => measurable_pi_iff.mpr fun k =>
    measurable_pi_apply (j * m + k.val)

/-- One batched line search transition driven by the samples of stream `ξ`. -/
noncomputable def execStep (m : ℕ) (g : ℝ → Ω → ℝ) (R x0 : ℝ) (ξ : ℕ → Ω) (call : ℕ)
    (s : OracleTemplate.LineSearch.State) : OracleTemplate.LineSearch.State :=
  step s (decode R x0 s (fun i => g (queries R x0 m s i) (ξ (call * (2 * m) + i.val))))

lemma advance_add_one {State : Type} (F : ℕ → State → State) :
    ∀ (K call : ℕ) (s : State),
      StochasticGradient.advance F (K + 1) call s
        = F (call + K) (StochasticGradient.advance F K call s) := by
  intro K
  induction K with
  | zero =>
      intro call s
      rfl
  | succ K ih =>
      intro call s
      calc StochasticGradient.advance F (K + 1 + 1) call s
          = StochasticGradient.advance F (K + 1) (call + 1) (F call s) := rfl
        _ = F (call + 1 + K) (StochasticGradient.advance F K (call + 1) (F call s)) :=
            ih (call + 1) (F call s)
        _ = F (call + (K + 1)) (StochasticGradient.advance F (K + 1) call s) := by
            have h1 : call + 1 + K = call + (K + 1) := by ring
            have h2 : StochasticGradient.advance F K (call + 1) (F call s)
                = StochasticGradient.advance F (K + 1) call s := rfl
            rw [h1, h2]

omit [MeasurableSpace Ω] in
/-- The line search driven by oracle replies follows the deterministic level recursion. -/
lemma advance_runState (m : ℕ) (g : ℝ → Ω → ℝ) (R x0 : ℝ) (ξ : ℕ → Ω) :
    ∀ j : ℕ,
      StochasticGradient.advance (execStep m g R x0 ξ) j 0
          (runState R x0 (V R x0 m g (toBlocks m ξ)) 0)
        = runState R x0 (V R x0 m g (toBlocks m ξ)) j := by
  intro j
  induction j with
  | zero => rfl
  | succ k ih =>
      rw [advance_add_one, ih, runState_succ]
      simp only [execStep]
      congr 1
      rw [decode_queries R x0 (s := (runState R x0 (V R x0 m g (toBlocks m ξ)) k)) (g := g)
        (ξ := ξ) (call := 0 + k)]
      have hleft : leftPoint (runState R x0 (V R x0 m g (toBlocks m ξ)) k)
          = leftAt R x0 m g (toBlocks m ξ) k := by
        rw [runState_V, leftPoint_eq_leftAt]
      have hright : rightPoint (runState R x0 (V R x0 m g (toBlocks m ξ)) k)
          = rightAt R x0 m g (toBlocks m ξ) k := by
        rw [runState_V, rightPoint_eq_rightAt]
      rw [hleft, hright]
      congr 2
      · refine Finset.sum_congr rfl (fun j _ => ?_)
        simp only [toBlocks]
        rw [show (0 + k) * (2 * m) = (2 * k) * m by ring]
      · refine Finset.sum_congr rfl (fun j _ => ?_)
        simp only [toBlocks]
        rw [show (0 + k) * (2 * m) + m = (2 * k + 1) * m by ring]

/-- The point returned by the executed line search after `J` levels. -/
lemma execute_champ {m J : ℕ} (hn : 0 < 2 * m) (P : ProbabilityMeasure (ℕ → Ω))
    (g : ℝ → Ω → ℝ) (R x0 : ℝ) :
    ∀ (seed : Unit) (ξ : ℕ → Ω),
      execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
          (lineSearch R x0 hn) (fun _ => J * (2 * m)) seed ξ
        = champAt R x0 m g (toBlocks m ξ) J := by
  intro seed ξ
  have key : StochasticGradient.advance (fun call s => (inner R x0).update s
      (decode R x0 s (fun i => g (queries R x0 m s i) (ξ (call * (2 * m) + i.val)))))
      J 0 ((inner R x0).initial seed) = runState R x0 (V R x0 m g (toBlocks m ξ)) J :=
    advance_runState m g R x0 ξ J
  have h := execute_lineSearch (P := P) (g := g) (ξ := ξ) (R := R) (x0 := x0) (hn := hn)
    (m := m) (J := J) seed
  rw [h, key]
  show (runState R x0 (V R x0 m g (toBlocks m ξ)) J).champ = champAt R x0 m g (toBlocks m ξ) J
  rw [runState_V]
  rfl

/-- The blocks of an i.i.d. stream have the block product law. -/
lemma blocks_measurePreserving {p : Measure Ω} [IsProbabilityMeasure p] {P : Measure (ℕ → Ω)}
    [IsProbabilityMeasure P] (hind : iIndepFun (fun k (ξ : ℕ → Ω) => ξ k) P)
    (hmarg : ∀ k, P.map (fun ξ : ℕ → Ω => ξ k) = p) (m : ℕ) :
    MeasurePreserving (toBlocks m) P (blockLaw p m) := by
  refine ⟨measurable_toBlocks m, ?_⟩
  have h := FiniteVariance.infinite_block_law p P hind hmarg m
  have hf : toBlocks m = fun ξ : ℕ → Ω => fun k : ℕ => fun i : Fin m => ξ (k * m + i.val) := by
    funext ξ k i
    rfl
  rw [hf]
  exact h.map_eq

/-- Expected accuracy of the executed line search on the raw i.i.d. stream. -/
lemma lineSearch_expected {m J : ℕ} (hn : 0 < 2 * m) {p : Measure Ω} [IsProbabilityMeasure p]
    {P : ProbabilityMeasure (ℕ → Ω)}
    (hind : iIndepFun (fun k (ξ : ℕ → Ω) => ξ k) (P : Measure (ℕ → Ω)))
    (hmarg : ∀ k, (P : Measure (ℕ → Ω)).map (fun ξ : ℕ → Ω => ξ k) = p)
    (R x0 : ℝ) (g : ℝ → Ω → ℝ) (f : ℝ → ℝ) (xstar L σ ε : ℝ)
    (hfm : Measurable f) (hg : Measurable (Function.uncurry g))
    (hm : 0 < m) (hσ : 0 ≤ σ) (hmean : ∀ x, ∫ z, g x z ∂p = f x)
    (hint : ∀ x, Integrable (g x) p)
    (hsql2 : ∀ x, Integrable (fun z => (g x z - f x) ^ 2) p)
    (hvar : ∀ x, ∫ z, (g x z - f x) ^ 2 ∂p ≤ σ ^ 2)
    (hconv : ConvexOn ℝ univ f) (hmin : IsMinOn f univ xstar)
    (hsmooth : ∀ x ∈ Icc (x0 - R) (x0 + R), f x - f xstar ≤ L / 2 * (x - xstar) ^ 2)
    (hL : 0 < L) (hR : x0 - R ≤ x0 + R) (hx : xstar ∈ Icc (x0 - R) (x0 + R)) (hJ : 1 ≤ J)
    (hbound : L / 2 * (2 * R * ((2:ℝ) / 3) ^ (J - 1)) ^ 2
        + 3 * (2 * σ * Real.sqrt ((J : ℝ) / m)) ≤ ε) :
    Integrable (fun seed : Unit × (ℕ → Ω) =>
        f (execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
            (lineSearch R x0 hn) (fun _ => J * (2 * m)) seed.1 seed.2) - f xstar)
        ((Measure.dirac () : Measure Unit).prod (P : Measure (ℕ → Ω))) ∧
      (∫ seed : Unit × (ℕ → Ω),
          f (execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
              (lineSearch R x0 hn) (fun _ => J * (2 * m)) seed.1 seed.2) - f xstar
            ∂((Measure.dirac () : Measure Unit).prod (P : Measure (ℕ → Ω)))) ≤ ε := by
  have hacc := expected_gap_sqrt R x0 g f xstar L σ ε
    ⟨hm, hfm, hg, hmean, hint, hsql2, hvar⟩ hσ hconv hmin hsmooth hL hR hx hJ hbound
  rcases hacc with ⟨haccI, haccB⟩
  have hmp := blocks_measurePreserving hind hmarg m
  have hF : (fun β : ℕ → Fin m → Ω => f (champAt R x0 m g β J) - f xstar)
      ∘ toBlocks m = fun ξ : ℕ → Ω =>
        f (execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
            (lineSearch R x0 hn) (fun _ => J * (2 * m)) () ξ) - f xstar := by
    funext ξ
    rw [execute_champ (hn := hn) (P := P) (g := g) (R := R) (x0 := x0)]
    rfl
  have hint1 : Integrable (fun ξ : ℕ → Ω =>
      f (execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
          (lineSearch R x0 hn) (fun _ => J * (2 * m)) () ξ) - f xstar) P := by
    have h1 : Integrable ((fun β : ℕ → Fin m → Ω => f (champAt R x0 m g β J) - f xstar)
        ∘ toBlocks m) P := hmp.integrable_comp_of_integrable haccI
    rw [hF] at h1
    exact h1
  have hint2 : (∫ ξ : ℕ → Ω,
        f (execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
            (lineSearch R x0 hn) (fun _ => J * (2 * m)) () ξ) - f xstar
          ∂(P : Measure (ℕ → Ω))) ≤ ε := by
    have hca : ∫ ξ : ℕ → Ω,
          f (execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
              (lineSearch R x0 hn) (fun _ => J * (2 * m)) () ξ) - f xstar
            ∂(P : Measure (ℕ → Ω))
        = ∫ ξ : ℕ → Ω,
            ((fun β : ℕ → Fin m → Ω => f (champAt R x0 m g β J) - f xstar) ∘ toBlocks m) ξ
              ∂(P : Measure (ℕ → Ω)) :=
      integral_congr_ae (ae_of_all _ (congrFun hF.symm))
    rw [hca]
    have heq : ∫ ξ : ℕ → Ω,
          ((fun β : ℕ → Fin m → Ω => f (champAt R x0 m g β J) - f xstar) ∘ toBlocks m) ξ
            ∂(P : Measure (ℕ → Ω))
        = ∫ β : ℕ → Fin m → Ω, f (champAt R x0 m g β J) - f xstar ∂(blockLaw p m) := by
      simpa only [Function.comp_apply] using ZerothOrder.integral_comp_preserving hmp haccI
    rw [heq]
    exact haccB
  have hdrop : MeasurePreserving Prod.snd
      ((Measure.dirac () : Measure Unit).prod (P : Measure (ℕ → Ω))) (P : Measure (ℕ → Ω)) :=
    ⟨measurable_snd, by rw [Measure.map_snd_prod, measure_univ, one_smul]⟩
  refine ⟨?_, ?_⟩
  · exact hdrop.integrable_comp_of_integrable hint1
  · refine le_of_eq_of_le (ZerothOrder.integral_comp_preserving hdrop hint1) hint2

end OracleTemplate.LineSearch

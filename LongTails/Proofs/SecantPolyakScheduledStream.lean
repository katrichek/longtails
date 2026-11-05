import LongTails.Proofs.ScheduledSlots
import LongTails.Proofs.ZerothOrderEstimator
import LongTails.Proofs.SecantPolyakAccuracy
import LongTails.Proofs.GapStrongGrowthIteration

/-!
Rounds whose replica counts vary with the round index. The ambient sample space keeps the cells of
the largest batch, so every round draws from the same product law, and a round only reads the cells
of its own replica count. The recursion carries the round index, which lets each round pay its own
batch error.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
open LongTails.Setups.ZerothOrderSmoothAndConvex

namespace OracleTemplate.SecantPolyak.Scheduled

open SecantDescent SecantPolyak ZerothOrder

variable {Ω : Type} [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]

/-- Iteration whose sample slots are cells of the ambient batch, indexed by the round number. -/
noncomputable def runSched {S : Type} {d M : ℕ} (step : ℕ → S → (secantSpace d M → Ω) → S) :
    (i : ℕ) → (K : ℕ) → S → (Fin K → secantSpace d M → Ω) → S
  | _, 0, x, _ => x
  | i, K + 1, x, Ξ => runSched step (i + 1) K (step i x (Ξ 0)) (fun j => Ξ j.succ)

omit [MeasurableSpace Ω] in
/-- A scheduled run can also be assembled by appending its last round. -/
lemma runSched_snoc {S : Type} {d M : ℕ} (step : ℕ → S → (secantSpace d M → Ω) → S)
    (i K : ℕ) (x : S) (Ξ : Fin (K + 1) → secantSpace d M → Ω) :
    runSched step i (K + 1) x Ξ
      = step (i + K) (runSched step i K x (fun j : Fin K => Ξ j.castSucc))
          (Ξ ⟨K, Nat.lt_succ_self K⟩) := by
  induction K generalizing i x with
  | zero => rfl
  | succ K ih =>
      show runSched step (i + 1) (K + 1) (step i x (Ξ 0)) (fun j : Fin (K + 1) => Ξ j.succ) = _
      rw [ih (i + 1) (step i x (Ξ 0))]
      rw [show i + 1 + K = i + (K + 1) by omega]
      have hlast : Ξ (Fin.succ ⟨K, Nat.lt_succ_self K⟩)
          = Ξ ⟨K + 1, Nat.lt_succ_self (K + 1)⟩ := congrArg Ξ (Fin.ext rfl)
      have hinner : runSched step i (K + 1) x (fun j : Fin (K + 1) => Ξ j.castSucc)
          = runSched step (i + 1) K (step i x (Ξ 0)) (fun j : Fin K => Ξ j.castSucc.succ) := by
        show runSched step (i + 1) K (step i x ((fun j : Fin (K + 1) => Ξ j.castSucc) 0))
              (fun j : Fin K => (fun j : Fin (K + 1) => Ξ j.castSucc) j.succ) = _
        refine congrArg (fun q => runSched step (i + 1) K (step i x (Ξ 0)) q)
          (funext fun j => congrArg Ξ (Fin.ext rfl))
      rw [hlast, hinner]

/-- One round of the scheduled secant step: round `k` uses `m k` replicas of the ambient cells. -/
noncomputable def stepSched {d M : ℕ} (m : ℕ → ℕ) (hmM : ∀ k, m k ≤ M) (L : ℝ)
    (g : Point d → Ω → ℝ) (h : ℝ) (k : ℕ) (x : Point d) (ω : secantSpace d M → Ω) : Point d :=
  stepSlot L g h x (fun t => ω (cellInj (hmM k) t))

/-- The joint map of one scheduled round is measurable. -/
lemma measurable_stepSched_joint {d M : ℕ} (m : ℕ → ℕ) (hmM : ∀ k, m k ≤ M)
    {g : Point d → Ω → ℝ} (hg : Measurable (Function.uncurry g)) (h : ℝ) (k : ℕ) :
    Measurable (fun q : Point d × (secantSpace d M → Ω) =>
      stepSched m hmM L g h k q.1 q.2) := by
  classical
  have hres : Measurable (fun ω : secantSpace d M → Ω => fun t : secantSpace d (m k) =>
      ω (cellInj (hmM k) t)) := by
    refine measurable_pi_iff.mpr (fun t => measurable_pi_apply (cellInj (hmM k) t))
  have h2 : Measurable (fun q : Point d × (secantSpace d M → Ω) =>
      (q.1, fun t : secantSpace d (m k) => q.2 (cellInj (hmM k) t))) :=
    measurable_fst.prodMk (hres.comp measurable_snd)
  exact (measurable_stepSlot_joint (m := m k) hg h).comp h2

/-- The joint map of a whole scheduled run is measurable. -/
lemma measurable_runSched {S : Type} [MeasurableSpace S] {d M : ℕ}
    {step : ℕ → S → (secantSpace d M → Ω) → S} (hstep : ∀ k,
      Measurable (fun q : S × (secantSpace d M → Ω) => step k q.1 q.2)) (K : ℕ) :
    ∀ (i : ℕ), Measurable (fun q : S × (Fin K → secantSpace d M → Ω) =>
      runSched step i K q.1 q.2) := by
  induction K with
  | zero =>
      intro i
      simpa only [runSched] using
        (measurable_fst : Measurable (fun q : S × (Fin 0 → secantSpace d M → Ω) => q.1))
  | succ K ih =>
      intro i
      have h1 : Measurable (fun q : S × (Fin (K + 1) → secantSpace d M → Ω) =>
          step i q.1 (q.2 0)) :=
        (hstep i).comp (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))
      refine (ih (i + 1)).comp ((h1.prodMk
        (Measurable.of_eval (fun j => (measurable_pi_apply j.succ).comp measurable_snd))))

/-- Peel the first round out of the weighted error sum. -/
lemma sum_sched_peel (ρ : ℝ) (c : ℕ → ℝ) (i K : ℕ) :
    (∑ k ∈ Finset.range (K + 1), ρ ^ (K - k) * c (i + k))
      = ρ ^ K * c i + ∑ k ∈ Finset.range K, ρ ^ (K - 1 - k) * c (i + 1 + k) := by
  rw [Finset.sum_range_succ', add_comm]
  refine congrArg (fun v => ρ ^ K * c i + v) (Finset.sum_congr rfl (fun k hk => ?_))
  have hkv : k < K := Finset.mem_range.mp hk
  have h1 : (K - (k + 1) : ℕ) = K - 1 - k := by omega
  have h2 : (i + (k + 1) : ℕ) = i + 1 + k := by omega
  simp only [h1, h2]

/-- A run of rounds with per-round additive errors contracts by `ρ` and accumulates the errors with
the contraction weights. -/
lemma sched_iterate_accuracy {S : Type} [MeasurableSpace S] {d M : ℕ}
    {step : ℕ → S → (secantSpace d M → Ω) → S}
    (hstep : ∀ k, Measurable (fun q : S × (secantSpace d M → Ω) => step k q.1 q.2))
    (P : ProbabilityMeasure (secantSpace d M → Ω)) (V : S → ℝ) (hV : Measurable V)
    (hV0 : ∀ s, 0 ≤ V s) {ρ : ℝ} (hρ : 0 ≤ ρ) {c : ℕ → ℝ} (hc : ∀ k, 0 ≤ c k)
    (hbound : ∀ k s, Integrable (fun a => V (step k s a)) (P : Measure (secantSpace d M → Ω)) ∧
      (∫ a, V (step k s a) ∂(P : Measure (secantSpace d M → Ω))) ≤ ρ * V s + c k)
    (i K : ℕ) (s : S) :
    Integrable (fun Ξ => V (runSched step i K s Ξ))
      (Measure.pi (fun _ : Fin K => (P : Measure (secantSpace d M → Ω)))) ∧
      (∫ Ξ, V (runSched step i K s Ξ)
          ∂Measure.pi (fun _ : Fin K => (P : Measure (secantSpace d M → Ω)))) ≤
        ρ ^ K * V s + ∑ k ∈ Finset.range K, ρ ^ (K - 1 - k) * c (i + k) := by
  induction K generalizing i s with
  | zero =>
      constructor
      · change Integrable (fun _ : Fin 0 → secantSpace d M → Ω => V s)
          (Measure.pi (fun _ : Fin 0 => (P : Measure (secantSpace d M → Ω))))
        exact integrable_const _
      · simp [runSched, measureReal_def]
  | succ K ih =>
      have hsum := sum_sched_peel ρ c i K
      let F := fun a : (secantSpace d M → Ω) × (Fin K → secantSpace d M → Ω) =>
        V (runSched step (i + 1) K (step i s a.1) a.2)
      have hFc : Measurable F := (hV.comp
        ((measurable_runSched hstep K (i + 1)).comp
          (((hstep i).comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)))
      have hFm : AEStronglyMeasurable F
          ((P : Measure (secantSpace d M → Ω)).prod
            (Measure.pi (fun _ : Fin K => (P : Measure (secantSpace d M → Ω))))) :=
        hFc.aestronglyMeasurable
      have hF0 (a : (secantSpace d M → Ω) × (Fin K → secantSpace d M → Ω)) : 0 ≤ F a := hV0 _
      have hNorm (a : secantSpace d M → Ω) :
          (∫ t, ‖F (a, t)‖ ∂Measure.pi (fun _ : Fin K => (P : Measure (secantSpace d M → Ω)))) =
            ∫ t, F (a, t) ∂Measure.pi (fun _ : Fin K => (P : Measure (secantSpace d M → Ω))) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun t => by
          change ‖F (a, t)‖ = F (a, t)
          rw [Real.norm_eq_abs, abs_of_nonneg (hF0 (a, t))])
      have hc0 : 0 ≤ ∑ j ∈ Finset.range K, ρ ^ (K - 1 - j) * c (i + 1 + j) := by
        refine Finset.sum_nonneg (fun j _ => mul_nonneg (pow_nonneg hρ _) (hc _))
      have hBound : Integrable (fun a => ρ ^ K * V (step i s a) +
          ∑ j ∈ Finset.range K, ρ ^ (K - 1 - j) * c (i + 1 + j))
          (P : Measure (secantSpace d M → Ω)) :=
        ((hbound i s).1.const_mul (ρ ^ K)).add (integrable_const _)
      have hOuter : Integrable
          (fun a => ∫ t, ‖F (a, t)‖ ∂Measure.pi (fun _ : Fin K =>
            (P : Measure (secantSpace d M → Ω))))
          (P : Measure (secantSpace d M → Ω)) := by
        apply hBound.mono' hFm.norm.integral_prod_right'
        apply Filter.Eventually.of_forall
        intro a
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun t => norm_nonneg _)), hNorm]
        exact (ih (i + 1) (step i s a)).2
      have hFi : Integrable F
          ((P : Measure (secantSpace d M → Ω)).prod
            (Measure.pi (fun _ : Fin K => (P : Measure (secantSpace d M → Ω))))) :=
        (integrable_prod_iff hFm).mpr
          ⟨Filter.Eventually.of_forall (fun a => (ih (i + 1) (step i s a)).1), hOuter⟩
      have hp := (measurePreserving_piFinSuccAbove
        (fun _ : Fin (K + 1) => (P : Measure (secantSpace d M → Ω))) 0).symm
      have hPi : Integrable (fun Ξ => V (runSched step i (K + 1) s Ξ))
          (Measure.pi (fun _ : Fin (K + 1) => (P : Measure (secantSpace d M → Ω)))) := by
        rw [← hp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)]
        simpa only [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNthEquiv, Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk,
          runSched, Fin.cons_zero, Fin.cons_succ, cast_eq] using hFi
      refine ⟨hPi, ?_⟩
      have he : (∫ Ξ, V (runSched step i (K + 1) s Ξ)
            ∂Measure.pi (fun _ : Fin (K + 1) => (P : Measure (secantSpace d M → Ω)))) =
          ∫ a, F a ∂(P : Measure (secantSpace d M → Ω)).prod
            (Measure.pi (fun _ : Fin K => (P : Measure (secantSpace d M → Ω)))) := by
        rw [← hp.integral_comp']
        simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNthEquiv, Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk,
          runSched, Fin.cons_zero, Fin.cons_succ, cast_eq]
        rfl
      rw [he, integral_prod _ hFi]
      calc _ ≤ ∫ a, (ρ ^ K * V (step i s a) + ∑ j ∈ Finset.range K, ρ ^ (K - 1 - j) *
              c (i + 1 + j))
            ∂(P : Measure (secantSpace d M → Ω)) :=
          integral_mono_ae hFi.integral_prod_left hBound
            (Filter.Eventually.of_forall (fun a => (ih (i + 1) (step i s a)).2))
        _ = ρ ^ K * (∫ a, V (step i s a) ∂(P : Measure (secantSpace d M → Ω))) +
              ∑ j ∈ Finset.range K, ρ ^ (K - 1 - j) * c (i + 1 + j) := by
            rw [integral_add ((hbound i s).1.const_mul _) (integrable_const _),
              integral_const_mul]
            simp
        _ ≤ ρ ^ K * (ρ * V s + c i) + ∑ j ∈ Finset.range K, ρ ^ (K - 1 - j) * c (i + 1 + j) :=
          add_le_add (mul_le_mul_of_nonneg_left (hbound i s).2 (pow_nonneg hρ K)) (le_refl _)
        _ = ρ ^ (K + 1) * V s + (ρ ^ K * c i +
              ∑ j ∈ Finset.range K, ρ ^ (K - 1 - j) * c (i + 1 + j)) := by
            rw [pow_succ]
            ring
        _ = ρ ^ (K + 1) * V s + ∑ k ∈ Finset.range (K + 1), ρ ^ (K - k) * c (i + k) := by
            rw [hsum]

/-- One scheduled round at the ambient law contracts the expected gap and pays its own batch
error. -/
lemma sched_one_step_ambient {d M : ℕ} {m : ℕ → ℕ} (hmM : ∀ k, m k ≤ M) (hm : ∀ k, 0 < m k)
    {g : Point d → Ω → ℝ} {f : Point d → ℝ} {σ L μ h : ℝ} {xstar : Point d}
    (hh : 0 < h) (hL : 0 < L) (hμ : 0 < μ) (hμL : μ ≤ L)
    (hg : Measurable (Function.uncurry g))
    (hgi : ∀ x, Integrable (g x) p)
    (hmean : ∀ x, (∫ ω, g x ω ∂p) = f x)
    (hvi : ∀ x, Integrable (fun ω => (g x ω - f x) ^ 2) p)
    (hv : ∀ x, (∫ ω, (g x ω - f x) ^ 2 ∂p) ≤ σ ^ 2)
    (hc : ConvexOn ℝ Set.univ f)
    (hgr : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hmin : IsMinOn f Set.univ xstar)
    (hpl : ∀ x, 2 * μ * (f x - f xstar) ≤ ‖gradient f x‖ ^ 2)
    (k : ℕ) (x : Point d) :
    Integrable (fun ω => f (stepSched m hmM L g h k x ω) - f xstar) (slotLaw d M p) ∧
      (∫ ω, f (stepSched m hmM L g h k x ω) - f xstar ∂(slotLaw d M p)) ≤
        (1 - μ / L) * (f x - f xstar) + (1 / L) * batchError d (m k) σ L h := by
  classical
  obtain ⟨hi, hb⟩ := secant_one_step_slot (d := d) (m := m k) (g := g) (f := f) (σ := σ) (L := L)
    (μ := μ) (h := h) (hh := hh) (hL := hL) (hμ := hμ) (hμL := hμL) (hg := hg) (hgi := hgi)
    (hmean := hmean) (hvi := hvi) (hv := hv) (hc := hc) (hgr := hgr) (hlip := hlip)
    (hm := hm k) (xstar := xstar) (hmin := hmin) (hpl := hpl) (x := x)
  have hp : MeasurePreserving (fun ω : secantSpace d M → Ω => fun t : secantSpace d (m k) =>
      ω (cellInj (hmM k) t)) (slotLaw d M p) (slotLaw d (m k) p) :=
    measurePreserving_cellInj (hmM k)
  have hI : Integrable (fun ω : secantSpace d M → Ω =>
      f (stepSlot L g h x (fun t => ω (cellInj (hmM k) t))) - f xstar) (slotLaw d M p) :=
    hp.integrable_comp_of_integrable (ε := ℝ)
      (g := fun ξ : secantSpace d (m k) → Ω => f (stepSlot L g h x ξ) - f xstar) hi
  refine ⟨hI, ?_⟩
  calc (∫ ω, f (stepSlot L g h x (fun t => ω (cellInj (hmM k) t))) - f xstar ∂(slotLaw d M p))
      = ∫ ξ, f (stepSlot L g h x ξ) - f xstar ∂(slotLaw d (m k) p) :=
          integral_comp_preserving hp hi
    _ ≤ (1 - μ / L) * (f x - f xstar) + (1 / L) * batchError d (m k) σ L h := hb

/-- Scheduled rounds: the expected gap contracts geometrically and each round pays its own batch
error with the contraction weight. -/
lemma sched_accuracy {d M K : ℕ} {m : ℕ → ℕ} (hmM : ∀ k, m k ≤ M) (hm : ∀ k, 0 < m k)
    {g : Point d → Ω → ℝ} {f : Point d → ℝ} {σ L μ h : ℝ} {x0 xstar : Point d}
    (hh : 0 < h) (hL : 0 < L) (hμ : 0 < μ) (hμL : μ ≤ L)
    (hg : Measurable (Function.uncurry g))
    (hgi : ∀ x, Integrable (g x) p)
    (hmean : ∀ x, (∫ ω, g x ω ∂p) = f x)
    (hvi : ∀ x, Integrable (fun ω => (g x ω - f x) ^ 2) p)
    (hv : ∀ x, (∫ ω, (g x ω - f x) ^ 2 ∂p) ≤ σ ^ 2)
    (hc : ConvexOn ℝ Set.univ f)
    (hgr : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hmin : IsMinOn f Set.univ xstar)
    (hpl : ∀ x, 2 * μ * (f x - f xstar) ≤ ‖gradient f x‖ ^ 2) :
    Integrable (fun Ξ => f (runSched (stepSched m hmM L g h) 0 K x0 Ξ) - f xstar)
        (Measure.pi fun _ : Fin K => slotLaw d M p) ∧
      (∫ Ξ, f (runSched (stepSched m hmM L g h) 0 K x0 Ξ) - f xstar
          ∂Measure.pi fun _ : Fin K => slotLaw d M p) ≤
        (1 - μ / L) ^ K * (f x0 - f xstar)
          + ∑ k ∈ Finset.range K, (1 - μ / L) ^ (K - 1 - k)
              * ((1 / L) * batchError d (m k) σ L h) := by
  classical
  have hρ : 0 ≤ 1 - μ / L := by
    have : μ / L ≤ 1 := (div_le_one hL).mpr hμL
    linarith
  have hf : Measurable f :=
    (continuous_iff_continuousAt.mpr (fun y => (hgr y).continuousAt)).measurable
  let V := f - fun _ => f xstar
  have hV : Measurable V := hf.sub measurable_const
  have hV0 : ∀ x, 0 ≤ V x := fun x => sub_nonneg.mpr (hmin (Set.mem_univ x))
  have hstep : ∀ (k : ℕ) (x : Point d),
      Integrable (fun a => V (stepSched m hmM L g h k x a)) (slotLaw d M p) ∧
        (∫ a, V (stepSched m hmM L g h k x a) ∂(slotLaw d M p)) ≤
          (1 - μ / L) * V x + (1 / L) * batchError d (m k) σ L h :=
    fun k x => sched_one_step_ambient (d := d) (M := M) (m := m) (hmM := hmM) (hm := hm)
      (g := g) (f := f) (σ := σ) (L := L) (μ := μ) (h := h) (hh := hh) (hL := hL) (hμ := hμ)
      (hμL := hμL) (hg := hg) (hgi := hgi) (hmean := hmean) (hvi := hvi) (hv := hv) (hc := hc)
      (hgr := hgr) (hlip := hlip) (hmin := hmin) (hpl := hpl) k x
  have hc0 : ∀ k : ℕ, 0 ≤ (1 / L) * batchError d (m k) σ L h := by
    intro k
    simp only [batchError]
    positivity
  have hkey := sched_iterate_accuracy (d := d) (M := M)
    (step := stepSched m hmM L g h)
    (fun k => measurable_stepSched_joint (d := d) (M := M) (m := m) (hmM := hmM) (g := g)
      (hg := hg) (h := h) k)
    ⟨slotLaw d M p, inferInstance⟩ V hV hV0 hρ hc0 hstep 0 K x0
  refine ⟨hkey.1, ?_⟩
  calc (∫ Ξ, f (runSched (stepSched m hmM L g h) 0 K x0 Ξ) - f xstar
          ∂Measure.pi fun _ : Fin K => slotLaw d M p)
      = ∫ Ξ, V (runSched (stepSched m hmM L g h) 0 K x0 Ξ)
          ∂Measure.pi fun _ : Fin K => slotLaw d M p := by
          simp [V]
    _ ≤ (1 - μ / L) ^ K * V x0
          + ∑ k ∈ Finset.range K, (1 - μ / L) ^ (K - 1 - k)
              * ((1 / L) * batchError d (m k) σ L h) := by
          simpa [Nat.zero_add] using hkey.2
    _ = (1 - μ / L) ^ K * (f x0 - f xstar)
          + ∑ k ∈ Finset.range K, (1 - μ / L) ^ (K - 1 - k)
              * ((1 / L) * batchError d (m k) σ L h) := by simp [V]

end OracleTemplate.SecantPolyak.Scheduled

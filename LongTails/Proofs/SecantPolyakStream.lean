import LongTails.Proofs.SecantPolyakAccuracy
import LongTails.Proofs.ZerothOrderExecution
import LongTails.Proofs.SgdExecution
import LongTails.Proofs.ClippedExtragradientIteration
import LongTails.Proofs.BatchedExecution
import LongTails.Algorithms.SecantDescent

/-!
Batched secant descent driven by flat oracle slots. One gradient step consumes
`2 * d * m` value samples indexed by `(replica, coordinate, side)`; the slot law is the
algorithm's own product law, and `toCells` identifies it with the law used by the analysis.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.SecantPolyak

open ContinuizedSimilarQuasar GapStrongGrowth SecantDescent StochasticGradient ZerothOrder
open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {Ω : Type} [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]

/-- Slot law: independent value samples indexed by `(replica, coordinate, side)`. -/
@[reducible] noncomputable def slotLaw (d m : ℕ) (q : Measure Ω) : Measure (secantSpace d m → Ω) :=
  Measure.pi fun _ : secantSpace d m => q

instance slotLaw_isProbability {d m : ℕ} : IsProbabilityMeasure (slotLaw d m p) := by
  unfold slotLaw
  infer_instance

/-- Regroup slots into `m` replicas of `d` coordinate-side pairs. -/
noncomputable def toCells {d m : ℕ} (ω : secantSpace d m → Ω) : Fin m → Fin d × Bool → Ω :=
  fun r ib => ω (r, ib)

/-- The slots of step `k` cut out of the raw oracle stream. -/
noncomputable def blockOf {d m K : ℕ} (ξ : ℕ → Ω) : Fin K → secantSpace d m → Ω :=
  fun k j => ξ (k.val * Fintype.card (secantSpace d m)
    + (Fintype.equivFin (secantSpace d m) j).val)

lemma measurePreserving_toCells (d m : ℕ) :
    MeasurePreserving (toCells (d := d) (m := m)) (slotLaw d m p) (batchLaw d m p) := by
  classical
  change MeasurePreserving (fun ω : Fin m × (Fin d × Bool) → Ω =>
    MeasurableEquiv.curry (Fin m) (Fin d × Bool) Ω ω) (slotLaw d m p) (batchLaw d m p)
  refine ⟨(MeasurableEquiv.curry (Fin m) (Fin d × Bool) Ω).measurable, ?_⟩
  unfold slotLaw batchLaw cellLaw
  simpa only [Measure.infinitePi_eq_pi] using
    (Measure.infinitePi_map_curry (fun (_ : Fin m) (_ : Fin d × Bool) => p))

/-- One gradient step driven by flat slots. -/
noncomputable def stepSlot {d m : ℕ} (L : ℝ) (g : Point d → Ω → ℝ) (h : ℝ) (x : Point d)
    (ω : secantSpace d m → Ω) : Point d :=
  secantStep L g h x (toCells ω)

/-- `K` slot-driven secant steps from `x0`. -/
noncomputable def runSlot {d m K : ℕ} (L : ℝ) (g : Point d → Ω → ℝ) (h : ℝ) (x0 : Point d)
    (ξ : Fin K → secantSpace d m → Ω) : Point d :=
  iterateSamples (stepSlot L g h) K x0 ξ

/-- One slot-driven step contracts the expected gap and pays the batch error. -/
lemma secant_one_step_slot {d m : ℕ} {g : Point d → Ω → ℝ} {f : Point d → ℝ} {σ L μ h : ℝ}
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
    Integrable (fun ω => f (stepSlot L g h x ω) - f xstar) (slotLaw d m p) ∧
      (∫ ω, f (stepSlot L g h x ω) - f xstar ∂(slotLaw d m p)) ≤
        (1 - μ / L) * (f x - f xstar) + (1 / L) * batchError d m σ L h := by
  classical
  obtain ⟨hi, hb⟩ := secant_one_step (d := d) (m := m) (g := g) (f := f) (σ := σ) (L := L)
    (μ := μ) (h := h) (hh := hh) (hL := hL) (hμ := hμ) (hμL := hμL) (hg := hg) (hgi := hgi)
    (hmean := hmean) (hvi := hvi) (hv := hv) (hc := hc) (hgr := hgr) (hlip := hlip) (hm := hm)
    (xstar := xstar) (hmin := hmin) (hpl := hpl) (x := x)
  have hp : MeasurePreserving (toCells (d := d) (m := m)) (slotLaw d m p) (batchLaw d m p) :=
    measurePreserving_toCells d m
  have hI : Integrable (fun ω : secantSpace d m → Ω =>
      f (secantStep L g h x (toCells ω)) - f xstar) (slotLaw d m p) :=
    hp.integrable_comp_of_integrable (ε := ℝ)
      (g := fun ξ : Fin m → Fin d × Bool → Ω => f (secantStep L g h x ξ) - f xstar) hi
  refine ⟨hI, ?_⟩
  calc (∫ ω, f (secantStep L g h x (toCells ω)) - f xstar ∂(slotLaw d m p))
      = ∫ ξ, f (secantStep L g h x ξ) - f xstar ∂(batchLaw d m p) :=
          integral_comp_preserving hp hi
    _ ≤ (1 - μ / L) * (f x - f xstar) + (1 / L) * batchError d m σ L h := hb

lemma measurable_stepSlot_joint {d m : ℕ} {g : Point d → Ω → ℝ}
    (hg : Measurable (Function.uncurry g)) (h : ℝ) :
    Measurable (fun q : Point d × (secantSpace d m → Ω) => stepSlot L g h q.1 q.2) := by
  classical
  have h1 : Measurable (fun ω : secantSpace d m → Ω => toCells (ω : secantSpace d m → Ω)) :=
    MeasurableEquiv.measurable (MeasurableEquiv.curry (Fin m) (Fin d × Bool) Ω)
  have h2 : Measurable (fun q : Point d × (secantSpace d m → Ω) =>
      (q.1, toCells (q.2 : secantSpace d m → Ω))) := measurable_fst.prodMk (h1.comp measurable_snd)
  exact (measurable_secantStep L hg h).comp h2

/-- `K` slot-driven steps contract the expected gap geometrically and accumulate the batch
error with the contraction weights, which is bounded by one batch error per `μ`. -/
lemma secant_accuracy_slot {d m K : ℕ} {g : Point d → Ω → ℝ} {f : Point d → ℝ} {σ L μ h : ℝ}
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
    Integrable (fun ξ : Fin K → secantSpace d m → Ω => f (runSlot L g h x0 ξ) - f xstar)
        (Measure.pi fun _ : Fin K => slotLaw d m p) ∧
      (∫ ξ : Fin K → secantSpace d m → Ω,
          f (runSlot L g h x0 ξ) - f xstar ∂Measure.pi fun _ : Fin K => slotLaw d m p) ≤
        (1 - μ / L) ^ K * (f x0 - f xstar) + (1 / μ) * batchError d m σ L h := by
  classical
  have hρ : 0 ≤ 1 - μ / L := by
    have : μ / L ≤ 1 := (div_le_one hL).mpr hμL
    linarith
  have hf : Measurable f :=
    (continuous_iff_continuousAt.mpr (fun y => (hgr y).continuousAt)).measurable
  let V := f - fun _ => f xstar
  have hV : Measurable V := hf.sub measurable_const
  have hV0 : ∀ x, 0 ≤ V x := fun x => sub_nonneg.mpr (hmin (Set.mem_univ x))
  have hstep : ∀ x, Integrable (fun a => V (stepSlot L g h x a)) (slotLaw d m p) ∧
      (∫ a, V (stepSlot L g h x a) ∂(slotLaw d m p)) ≤
        (1 - μ / L) * V x + (1 / L) * batchError d m σ L h :=
    fun x => secant_one_step_slot (g := g) (f := f) (σ := σ) (L := L)
      (μ := μ) (h := h) (hh := hh) (hL := hL) (hμ := hμ) (hμL := hμL) (hg := hg) (hgi := hgi)
      (hmean := hmean) (hvi := hvi) (hv := hv) (hc := hc) (hgr := hgr) (hlip := hlip)
      (hm := hm) (xstar := xstar) (hmin := hmin) (hpl := hpl) (x := x)
  have hkey := iterateSamples_measurable_integral (advance := stepSlot L g h)
    (measurable_stepSlot_joint hg h) (P := ⟨slotLaw d m p, inferInstance⟩)
    (V := V) hV hV0 hρ hstep K x0
  have hρ1 : 1 - μ / L < 1 := by
    have : 0 < μ / L := div_pos hμ hL
    linarith
  have hsum : (∑ j ∈ Finset.range K, (1 - μ / L) ^ j) ≤ L / μ := by
    have hpos : 0 < μ / L := div_pos hμ hL
    have h1 : (∑ j ∈ Finset.range K, (1 - μ / L) ^ j) * (1 - (1 - μ / L)) =
        1 - (1 - μ / L) ^ K := geom_sum_mul_neg _ K
    have h2 : 1 - (1 - μ / L) = μ / L := by ring
    rw [h2] at h1
    have hle : (∑ j ∈ Finset.range K, (1 - μ / L) ^ j) * (μ / L) ≤ 1 := by
      rw [h1]
      linarith [pow_nonneg hρ K]
    calc (∑ j ∈ Finset.range K, (1 - μ / L) ^ j) ≤ 1 / (μ / L) := (le_div_iff₀ hpos).mpr hle
      _ = L / μ := by field_simp
  refine ⟨hkey.1, le_trans hkey.2 ?_⟩
  have hK : 0 ≤ (1 / L) * batchError d m σ L h := by
    simp only [batchError]
    positivity
  calc (1 - μ / L) ^ K * (f x0 - f xstar) +
        ((1 / L) * batchError d m σ L h) *
          ∑ j ∈ Finset.range K, (1 - μ / L) ^ j
      ≤ (1 - μ / L) ^ K * (f x0 - f xstar) +
          ((1 / L) * batchError d m σ L h) * (L / μ) := by
          refine add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hsum hK)
      _ = (1 - μ / L) ^ K * (f x0 - f xstar) + (1 / μ) * batchError d m σ L h := by
          have hne : μ ≠ 0 := ne_of_gt hμ
          field_simp

/-- Cutting the step blocks out of an i.i.d. oracle stream gives the slot product law. -/
lemma secant_stream_law {d m K : ℕ} (P : ProbabilityMeasure (ℕ → Ω))
    (hind : iIndepFun (fun k (ξ : ℕ → Ω) => ξ k) (P : Measure _))
    (hmarg : ∀ k, (P : Measure _).map (fun ξ : ℕ → Ω => ξ k) = (p : Measure _)) :
    MeasurePreserving (blockOf (d := d) (m := m)) (P : Measure _)
      (Measure.pi fun _ : Fin K => slotLaw d m p) := by
  classical
  convert block_law (J := secantSpace d m) (p := (p : Measure Ω)) (P := (P : Measure _))
    hind hmarg K using 1
  rfl

omit [MeasurableSpace Ω] in
/-- Grouping the two sides of one coordinate difference. -/
lemma slot_term_eq (a b h : ℝ) (v : Point d) :
    (a / h) • v + (-b / h) • v = ((a - b) / h) • v := by
  rw [← add_smul]
  congr 1
  ring

omit [MeasurableSpace Ω] in
/-- The reply rebuilt from slots equals the secant decode of the batched algorithm. -/
lemma decode_eq_reply {d m : ℕ} {g : Point d → Ω → ℝ} (h : ℝ) (k : ℕ) (x : Point d)
    (ω : secantSpace d m → Ω) :
    secantDecode h (k, x) (fun t => g (secantPoint h x t) (ω t)) = reply g h x (toCells ω) := by
  classical
  have hinner (r : Fin m) (i : Fin d) :
      (∑ b : Bool, ((if b then g (if b then x + h • direction i else x) (ω (r, (i, b)))
          else -g (if b then x + h • direction i else x) (ω (r, (i, b)))) / h) • direction i) =
        ((g (x + h • direction i) (ω (r, (i, true))) - g x (ω (r, (i, false)))) / h) •
          direction i := by
    have hu : (Finset.univ : Finset Bool) = {true, false} := by decide
    rw [hu, Finset.sum_pair (by decide : (true : Bool) ≠ false)]
    simp only [Bool.false_eq_true, ite_true, ite_false]
    rw [slot_term_eq]
  have h1 : (∑ t : secantSpace d m,
      ((if secantSign t then g (secantPoint h x t) (ω t)
          else -g (secantPoint h x t) (ω t)) / h) • direction (secantCoord t)) =
      ∑ r : Fin m, ∑ i : Fin d, ((g (x + h • direction i) (ω (r, (i, true)))
          - g x (ω (r, (i, false)))) / h) • direction i := by
    refine Eq.trans (Fintype.sum_prod_type _) ?_
    refine Finset.sum_congr rfl (fun r _ => ?_)
    refine Eq.trans (Fintype.sum_prod_type _) ?_
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [secantSign, secantCoord, secantPoint]
    exact hinner r i
  unfold secantDecode reply toCells
  refine congrArg (fun v : Point d => (1 / (m : ℝ)) • v) ?_
  rw [h1]
  rfl

/-- The step function of the batched secant algorithm over the raw slot stream. -/
noncomputable def streamStep {d m : ℕ} (L : ℝ) (g : Point d → Ω → ℝ) (h : ℝ) (x0 : Point d)
    (ξ : ℕ → Ω) : ℕ → (ℕ × Point d) → (ℕ × Point d) :=
  fun call state => (descent L x0).update state
    (secantDecode h state (fun t =>
      g (secantQuery h state (secantSlot (Fintype.equivFin (secantSpace d m) t)))
        (ξ (call * Fintype.card (secantSpace d m)
          + (Fintype.equivFin (secantSpace d m) t).val))))

omit [MeasurableSpace Ω] in
/-- Running `n` batched steps from call index `c` reproduces the analysed slot run. -/
lemma advance_runSlot {d m : ℕ} (L h : ℝ) (g : Point d → Ω → ℝ) (x0 : Point d) (ξ : ℕ → Ω) :
    ∀ (n c j : ℕ) (y : Point d),
      advance (streamStep (d := d) (m := m) L g h x0 ξ) n c (j, y) =
        (j + n, runSlot L g h y (fun k : Fin n => fun t : secantSpace d m =>
          ξ ((c + k.val) * Fintype.card (secantSpace d m)
            + (Fintype.equivFin (secantSpace d m) t).val))) := by
  classical
  intro n
  induction n with
  | zero => intro c j y; rfl
  | succ n ih =>
    intro c j y
    have hstep : (streamStep (d := d) (m := m) L g h x0 ξ) c (j, y) =
        (j + 1, stepSlot L g h y (fun t : secantSpace d m =>
          ξ (c * Fintype.card (secantSpace d m)
            + (Fintype.equivFin (secantSpace d m) t).val))) := by
      refine Prod.ext rfl ?_
      show y - (1 / L) • secantDecode h (j, y) (fun t =>
          g (secantQuery h (j, y) (secantSlot (Fintype.equivFin (secantSpace d m) t)))
            (ξ (c * Fintype.card (secantSpace d m)
              + (Fintype.equivFin (secantSpace d m) t).val))) = _
      simp only [secantQuery_apply, secantSlot_equivFin]
      rw [decode_eq_reply]
      rfl
    have hpeel : runSlot L g h y (fun k : Fin (n + 1) => fun t : secantSpace d m =>
          ξ ((c + k.val) * Fintype.card (secantSpace d m)
            + (Fintype.equivFin (secantSpace d m) t).val)) =
        iterateSamples (stepSlot L g h) n
          (stepSlot L g h y (fun t : secantSpace d m =>
            ξ ((c + 0) * Fintype.card (secantSpace d m)
              + (Fintype.equivFin (secantSpace d m) t).val)))
          (fun i : Fin n => fun t : secantSpace d m =>
            ξ ((c + i.succ.val) * Fintype.card (secantSpace d m)
              + (Fintype.equivFin (secantSpace d m) t).val)) := rfl
    have hb : stepSlot (d := d) (m := m) L g h y (fun t : secantSpace d m =>
        ξ ((c + 0) * Fintype.card (secantSpace d m)
          + (Fintype.equivFin (secantSpace d m) t).val)) =
        stepSlot (d := d) (m := m) L g h y (fun t : secantSpace d m =>
          ξ (c * Fintype.card (secantSpace d m)
            + (Fintype.equivFin (secantSpace d m) t).val)) := by
      refine congrArg (stepSlot (d := d) (m := m) L g h y)
        (funext fun t => congrArg ξ ?_)
      rw [Nat.add_zero]
    have hs : (fun i : Fin n => fun t : secantSpace d m =>
        ξ ((c + i.succ.val) * Fintype.card (secantSpace d m)
          + (Fintype.equivFin (secantSpace d m) t).val)) =
        (fun i : Fin n => fun t : secantSpace d m =>
          ξ ((c + 1 + i.val) * Fintype.card (secantSpace d m)
            + (Fintype.equivFin (secantSpace d m) t).val)) := by
      refine funext fun i => funext fun t => congrArg ξ
        (congrArg (fun w : ℕ => w * Fintype.card (secantSpace d m)
            + (Fintype.equivFin (secantSpace d m) t).val) ?_)
      rw [Fin.val_succ]
      omega
    show advance (streamStep (d := d) (m := m) L g h x0 ξ) (n + 1) c (j, y) =
        (j + (n + 1), runSlot L g h y (fun k : Fin (n + 1) => fun t : secantSpace d m =>
          ξ ((c + k.val) * Fintype.card (secantSpace d m)
            + (Fintype.equivFin (secantSpace d m) t).val)))
    rw [show advance (streamStep (d := d) (m := m) L g h x0 ξ) (n + 1) c (j, y) =
        advance (streamStep (d := d) (m := m) L g h x0 ξ) n (c + 1)
          ((streamStep (d := d) (m := m) L g h x0 ξ) c (j, y)) from rfl,
      hstep, ih (c + 1) (j + 1) _]
    refine Prod.ext ?_ ?_
    · omega
    · show runSlot L g h (stepSlot L g h y (fun t : secantSpace d m =>
              ξ (c * Fintype.card (secantSpace d m)
                + (Fintype.equivFin (secantSpace d m) t).val)))
            (fun k : Fin n => fun t : secantSpace d m =>
              ξ ((c + 1 + k.val) * Fintype.card (secantSpace d m)
                + (Fintype.equivFin (secantSpace d m) t).val)) =
          runSlot L g h y (fun k : Fin (n + 1) => fun t : secantSpace d m =>
            ξ ((c + k.val) * Fintype.card (secantSpace d m)
              + (Fintype.equivFin (secantSpace d m) t).val))
      rw [hpeel]
      unfold runSlot
      rw [← hb, ← hs]

/-- Executing batched secant descent equals the analysed slot run. -/
lemma execute_secant {d m K : ℕ} (hd : 0 < d) (hm : 0 < m) (L h : ℝ) (x0 : Point d)
    (g : Point d → Ω → ℝ) (P : ProbabilityMeasure (ℕ → Ω)) (ξ : ℕ → Ω) :
    execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
      (secantDescent hd hm L h x0) (fun _ => K * Fintype.card (secantSpace d m)) () ξ =
      runSlot (K := K) L g h x0 (blockOf (d := d) (m := m) (K := K) ξ) := by
  classical
  have hn : 0 < Fintype.card (secantSpace d m) := secant_card_pos hd hm
  have hb := execute_batched hn (descent L x0) (fun s t => secantQuery h s (secantSlot t))
    (fun s replies => secantDecode h s (fun t => replies (Fintype.equivFin (secantSpace d m) t)))
    0 P g ξ K ()
  have h2 : (descent L x0).output
      (advance (fun call state => (descent L x0).update state
        (secantDecode h state (fun i =>
          g (secantQuery h state (secantSlot (Fintype.equivFin (secantSpace d m) i)))
            (ξ (call * Fintype.card (secantSpace d m)
              + (Fintype.equivFin (secantSpace d m) i).val))))) K 0
        ((descent L x0).initial ())) =
      runSlot (K := K) L g h x0 (blockOf (d := d) (m := m) (K := K) ξ) := by
    have hstep2 := congrArg ((descent L x0).output)
      (advance_runSlot (d := d) (m := m) L h g x0 ξ K 0 0 x0)
    have h3 : (descent L x0).output
        (0 + K, runSlot (K := K) L g h x0 (fun k : Fin K => fun t : secantSpace d m =>
          ξ ((0 + k.val) * Fintype.card (secantSpace d m)
            + (Fintype.equivFin (secantSpace d m) t).val))) =
        runSlot (K := K) L g h x0 (blockOf (d := d) (m := m) (K := K) ξ) := by
      show runSlot (K := K) L g h x0 (fun k : Fin K => fun t : secantSpace d m =>
          ξ ((0 + k.val) * Fintype.card (secantSpace d m)
            + (Fintype.equivFin (secantSpace d m) t).val)) = _
      refine congrArg (runSlot (K := K) L g h x0)
        (funext fun k => funext fun t => congrArg ξ
          (congrArg (fun w : ℕ => w * Fintype.card (secantSpace d m)
              + (Fintype.equivFin (secantSpace d m) t).val) (Nat.zero_add k.val)))
    exact hstep2.trans h3
  exact hb.trans h2


/-- The slot run is measurable in the block samples. -/
lemma measurable_runSlot {d m K : ℕ} {g : Point d → Ω → ℝ}
    (hg : Measurable (Function.uncurry g)) (L h : ℝ) (x0 : Point d) :
    Measurable (fun xi : Fin K → secantSpace d m → Ω => runSlot (K := K) L g h x0 xi) := by
  classical
  exact (ClippedExtragradient.measurable_iterateSamples (measurable_stepSlot_joint hg h) K).comp
    (measurable_const.prodMk measurable_id)

/-- Step blocks cut out of the stream are measurable. -/
lemma measurable_blockOf {d m K : ℕ} :
    Measurable (fun xi : ℕ → Ω => blockOf (d := d) (m := m) (K := K) xi) := by
  classical
    show Measurable (fun xi : ℕ → Ω =>
        fun k : Fin K => fun t : secantSpace d m =>
          xi (k.val * Fintype.card (secantSpace d m)
            + (Fintype.equivFin (secantSpace d m) t).val))
    fun_prop

/-- Accuracy of the executed secant algorithm on the template product space. -/
lemma executed_accuracy {d m K : ℕ} (hd : 0 < d) (hm : 0 < m) {g : Point d → Ω → ℝ}
    {f : Point d → ℝ} {σ L μ h : ℝ} {x0 xstar : Point d}
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
    (P : ProbabilityMeasure (ℕ → Ω))
    (hind : iIndepFun (fun k (xi : ℕ → Ω) => xi k) (P : Measure _))
    (hmarg : ∀ k, (P : Measure _).map (fun xi : ℕ → Ω => xi k) = (p : Measure _)) :
    let result := fun seed : Unit × (ℕ → Ω) =>
      execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
        (secantDescent hd hm L h x0) (fun _ => K * (2 * d * m)) seed.1 seed.2
    Measurable result ∧
      Integrable (fun seed => f (result seed) - f xstar)
        ((Measure.dirac () : Measure Unit).prod (P : Measure (ℕ → Ω))) ∧
      (∫ seed, f (result seed) - f xstar
          ∂((Measure.dirac () : Measure Unit).prod (P : Measure (ℕ → Ω)))) ≤
        (1 - μ / L) ^ K * (f x0 - f xstar) + (1 / μ) * batchError d m σ L h := by
  classical
  intro result
  have hbc : (fun _ : Fin 1 => K * Fintype.card (secantSpace d m))
      = (fun _ : Fin 1 => K * (2 * d * m)) := by
    classical
    funext i
    rw [card_secantSpace]
  have hres : result = fun seed : Unit × (ℕ → Ω) =>
      runSlot (K := K) L g h x0 (blockOf (d := d) (m := m) (K := K) seed.2) := by
    refine funext fun seed => ?_
    cases seed with
    | mk u xi =>
      cases u
      show execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
          (secantDescent hd hm L h x0) (fun _ => K * (2 * d * m)) () xi =
          runSlot (K := K) L g h x0 (blockOf (d := d) (m := m) (K := K) xi)
      rw [← hbc]
      exact execute_secant hd hm L h x0 g P xi
  have hmeas : Measurable result := by
    rw [hres]
    exact (measurable_runSlot hg L h x0).comp (measurable_blockOf.comp measurable_snd)
  have ha := secant_accuracy_slot (d := d) (m := m) (K := K) (g := g) (f := f) (σ := σ) (L := L)
    (μ := μ) (x0 := x0) (xstar := xstar) (h := h) (hh := hh) (hL := hL) (hμ := hμ) (hμL := hμL) (hg := hg) (hgi := hgi)
    (hmean := hmean) (hvi := hvi) (hv := hv) (hc := hc) (hgr := hgr) (hlip := hlip) (hm := hm)
    (hmin := hmin) (hpl := hpl)
  have hmp : MeasurePreserving (fun seed : Unit × (ℕ → Ω) =>
      blockOf (d := d) (m := m) (K := K) seed.2)
      ((Measure.dirac () : Measure Unit).prod (P : Measure (ℕ → Ω)))
      (Measure.pi fun _ : Fin K => slotLaw d m p) := by
    have h1 : MeasurePreserving Prod.snd
        ((Measure.dirac () : Measure Unit).prod (P : Measure (ℕ → Ω)))
        (P : Measure (ℕ → Ω)) := measurePreserving_snd
    exact (secant_stream_law (d := d) (m := m) (K := K) P hind hmarg).comp h1
  refine ⟨hmeas, ?_, ?_⟩
  · rw [hres]
    exact hmp.integrable_comp_of_integrable ha.1
  · rw [hres]
    calc (∫ seed : Unit × (ℕ → Ω),
            f (runSlot (K := K) L g h x0 (blockOf (d := d) (m := m) (K := K) seed.2)) - f xstar
            ∂((Measure.dirac () : Measure Unit).prod (P : Measure (ℕ → Ω))))
        = ∫ xi : Fin K → secantSpace d m → Ω,
            f (runSlot (K := K) L g h x0 xi) - f xstar
            ∂(Measure.pi fun _ : Fin K => slotLaw d m p) :=
          integral_comp_preserving hmp ha.1
      _ ≤ (1 - μ / L) ^ K * (f x0 - f xstar) + (1 / μ) * batchError d m σ L h := ha.2


end OracleTemplate.SecantPolyak

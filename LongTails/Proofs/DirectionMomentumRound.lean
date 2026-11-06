import LongTails.Proofs.DirectionMomentumStep
import LongTails.Proofs.ScheduledSlots

set_option maxHeartbeats 2000000

/-!
Direction-sampled rounds. One round probes the momentum point along `2 * m` independent directions
drawn from the model's direction measure and averages the signed one-sided terms. A probe of side
`s` is unbiased for the signed half of the smoothed gradient, so the round is unbiased for the
smoothed gradient itself and independent probes divide its mean square deviation by `m`.
-/

namespace OracleTemplate.SecantPolyak.DirectionSampled

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
open OracleTemplate InexactGradient SecantPolyak SecantPolyak.Scheduled SecantDescent
open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {Ω : Type} [MeasurableSpace Ω]

/-- One probe as a function of its direction and value sample. -/
noncomputable def slotVal {d : ℕ} (h : ℝ) (g : Point d → Ω → ℝ) (x : Point d) (s : Bool)
    (u : Point d × Ω) : Point d :=
  (1 / (2 * h)) • ((g (x + (if s then h else -h) • u.1) u.2) • u.1)

/-- The signed half-gradient that a probe of side `s` estimates. -/
noncomputable def halfGrad {d : ℕ} (fh : Point d → ℝ) (x : Point d) (s : Bool) : Point d :=
  (if s then (1 / 2 : ℝ) else -(1 / 2 : ℝ)) • gradient fh x

/-- The surrogate of one round: the signed average of the `2 * m` one-sided probes. -/
noncomputable def roundOf {d : ℕ} (h : ℝ) (g : Point d → Ω → ℝ) (x : Point d) (m : ℕ)
    (a : secantSpace 1 m → Point d × Ω) : Point d :=
  (1 / (m : ℝ)) • ∑ t : secantSpace 1 m,
    (if t.2.2 then (1 : ℝ) else -1) • slotVal h g x t.2.2 (a t)

/-- The deviation of a probe of side `s` from its signed half-gradient target. -/
noncomputable def cellDev {d : ℕ} (h : ℝ) (g : Point d → Ω → ℝ) (fh : Point d → ℝ) (x : Point d)
    (s : Bool) (u : Point d × Ω) : Point d :=
  (if s then (1 : ℝ) else -1) • slotVal h g x s u - (1 / 2 : ℝ) • gradient fh x

/-- The deviation of slot `t` of a round. -/
noncomputable def slotDev {d : ℕ} (h : ℝ) (g : Point d → Ω → ℝ) (fh : Point d → ℝ) (x : Point d)
    (m : ℕ) (a : secantSpace 1 m → Point d × Ω) (t : secantSpace 1 m) : Point d :=
  cellDev h g fh x t.2.2 (a t)

/-- Scalar multiples of an integrable `Point d`-valued map are integrable. -/
lemma integrable_smul_pt {α : Type} [MeasurableSpace α] {W : Measure α} {c : ℝ}
    {f : α → Point d} (hf : Integrable f W) : Integrable (fun a => c • f a) W :=
  Integrable.smul c hf

/-- Reading one cell of a round is measure preserving. -/
lemma preserving_slotEval {m : ℕ} (W : Measure (Point d × Ω)) [IsProbabilityMeasure W]
    (t : secantSpace 1 m) :
    MeasurePreserving (fun a : secantSpace 1 m → Point d × Ω => a t) (slotLaw 1 m W) W := by
  unfold slotLaw
  exact measurePreserving_eval (fun _ : secantSpace 1 m => W) t

omit [MeasurableSpace Ω] in
/-- The signed half-gradient times its own sign is the unsigned half-gradient. -/
lemma smul_half {d : ℕ} (fh : Point d → ℝ) (x : Point d) (s : Bool) :
    (if s then (1 : ℝ) else -1) • halfGrad fh x s = (1 / 2 : ℝ) • gradient fh x := by
  classical
  cases s <;> simp [halfGrad]

omit [MeasurableSpace Ω] in
omit [MeasurableSpace Ω] in
/-- A probe's deviation is its own sign times the deviation from the signed target. -/
lemma cellDev_eq {d : ℕ} (h : ℝ) (g : Point d → Ω → ℝ) (fh : Point d → ℝ) (x : Point d) (s : Bool)
    (u : Point d × Ω) :
    cellDev h g fh x s u
      = (if s then (1 : ℝ) else -1) • (slotVal h g x s u - halfGrad fh x s) := by
  classical
  cases s <;> simp [cellDev, halfGrad, neg_smul, sub_eq_add_neg]

lemma slotVal_measurable {d : ℕ} {g : Point d → Ω → ℝ} (hg : Measurable (Function.uncurry g))
    (h : ℝ) (x : Point d) (s : Bool) : Measurable (fun u : Point d × Ω => slotVal h g x s u) := by
  classical
  have hv : Measurable (fun u : Point d × Ω => x + (if s then h else -h) • u.1) := by fun_prop
  have hgv : Measurable (fun u : Point d × Ω => g (x + (if s then h else -h) • u.1) u.2) :=
    hg.comp (hv.prodMk measurable_snd)
  exact smul_measurable measurable_const (smul_measurable hgv measurable_fst)

lemma cellDev_measurable {d : ℕ} {g : Point d → Ω → ℝ} (hg : Measurable (Function.uncurry g))
    (h : ℝ) (fh : Point d → ℝ) (x : Point d) (s : Bool) :
    Measurable (fun u : Point d × Ω => cellDev h g fh x s u) := by
  classical
  have he : (fun u : Point d × Ω => cellDev h g fh x s u)
      = (fun u : Point d × Ω =>
        (if s then (1 : ℝ) else -1) • (slotVal h g x s u - halfGrad fh x s)) := by
    funext u
    exact cellDev_eq h g fh x s u
  rw [he]
  exact smul_measurable measurable_const
    ((slotVal_measurable hg h x s).sub measurable_const)

lemma slotVal_integrable {d : ℕ} {W : Measure (Point d × Ω)} [IsFiniteMeasure W]
    {g : Point d → Ω → ℝ} {fh : Point d → ℝ} {h : ℝ}
    (hint : ∀ x s, Integrable (fun u : Point d × Ω => slotVal h g x s u - halfGrad fh x s) W)
    (x : Point d) (s : Bool) : Integrable (fun u : Point d × Ω => slotVal h g x s u) W := by
  have h2 : (fun u : Point d × Ω => slotVal h g x s u - halfGrad fh x s) + (fun _ => halfGrad fh x s)
      = (fun u => slotVal h g x s u) := by
    funext u
    show slotVal h g x s u - halfGrad fh x s + halfGrad fh x s = slotVal h g x s u
    abel
  rw [← h2]
  exact (hint x s).add (integrable_const (halfGrad fh x s))

lemma cellDev_integrable {d : ℕ} {W : Measure (Point d × Ω)}
    {g : Point d → Ω → ℝ} {fh : Point d → ℝ} {h : ℝ}
    (hint : ∀ x s, Integrable (fun u : Point d × Ω => slotVal h g x s u - halfGrad fh x s) W)
    (x : Point d) (s : Bool) : Integrable (fun u : Point d × Ω => cellDev h g fh x s u) W := by
  classical
  have he : (fun u : Point d × Ω => cellDev h g fh x s u)
      = (fun u : Point d × Ω =>
        (if s then (1 : ℝ) else -1) • (slotVal h g x s u - halfGrad fh x s)) := by
    funext u
    exact cellDev_eq h g fh x s u
  rw [he]
  exact integrable_smul_pt (c := (if s then (1 : ℝ) else -1)) (hint x s)

lemma integral_const_one_pt {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (v : Point d) : (∫ _a : Ω, v ∂μ) = v := by
  rw [integral_const]
  simp

lemma cellDev_integral {d : ℕ} {W : Measure (Point d × Ω)} [IsProbabilityMeasure W]
    {g : Point d → Ω → ℝ} {fh : Point d → ℝ} {h : ℝ}
    (hint : ∀ x s, Integrable (fun u : Point d × Ω => slotVal h g x s u - halfGrad fh x s) W)
    (hmean : ∀ x s, (∫ u : Point d × Ω, slotVal h g x s u ∂W) = halfGrad fh x s)
    (x : Point d) (s : Bool) :
    (∫ u : Point d × Ω, cellDev h g fh x s u ∂W) = 0 := by
  classical
  calc (∫ u : Point d × Ω, cellDev h g fh x s u ∂W)
      = ∫ u : Point d × Ω,
          (if s then (1 : ℝ) else -1) • (slotVal h g x s u - halfGrad fh x s) ∂W :=
          integral_congr_ae (ae_of_all _ fun u => cellDev_eq h g fh x s u)
    _ = (if s then (1 : ℝ) else -1) • ∫ u : Point d × Ω, (slotVal h g x s u - halfGrad fh x s) ∂W :=
          integral_smul _ _
    _ = (if s then (1 : ℝ) else -1) • (halfGrad fh x s - halfGrad fh x s) := by
          congr 1
          rw [integral_sub (slotVal_integrable hint x s) (integrable_const (halfGrad fh x s)),
            hmean x s, integral_const_one_pt]
    _ = 0 := by rw [sub_self, smul_zero]

omit [MeasurableSpace Ω] in
/-- The norm of a probe's deviation is the norm of its deviation from the signed target. -/
lemma cellDev_norm {d : ℕ} (h : ℝ) (g : Point d → Ω → ℝ) (fh : Point d → ℝ) (x : Point d)
    (s : Bool) (u : Point d × Ω) :
    ‖cellDev h g fh x s u‖ = ‖slotVal h g x s u - halfGrad fh x s‖ := by
  classical
  rw [cellDev_eq, norm_smul, Real.norm_eq_abs]
  cases s <;> simp

/-- The signed half-gradients of a round add up to the full gradient. -/
lemma hsumv {d m : ℕ} (hm : 0 < m) (v : Point d) :
    (1 / (m : ℝ)) • ∑ _ : secantSpace 1 m, ((1 / 2 : ℝ) • v) = v := by
  classical
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hcard : ((Fintype.card (secantSpace 1 m) : ℕ) : ℝ) = (2 : ℝ) * (m : ℝ) := by
    rw [card_secantSpace]
    push_cast
    ring
  have h1 : (∑ _ : secantSpace 1 m, ((1 / 2 : ℝ) • (v : Point d)))
      = ((Fintype.card (secantSpace 1 m) : ℕ) : ℝ) • ((1 / 2 : ℝ) • (v : Point d)) := by
        rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ]
  have h2 : ((1 / (m : ℝ)) •
      (((Fintype.card (secantSpace 1 m) : ℕ) : ℝ) • ((1 / 2 : ℝ) • (v : Point d))))
      = ((1 / (m : ℝ)) * ((Fintype.card (secantSpace 1 m) : ℕ) : ℝ))
        • ((1 / 2 : ℝ) • (v : Point d)) := by rw [smul_smul]
  have h3 : (((1 / (m : ℝ)) * ((Fintype.card (secantSpace 1 m) : ℕ) : ℝ))
      • ((1 / 2 : ℝ) • (v : Point d)))
      = (((1 / (m : ℝ)) * ((Fintype.card (secantSpace 1 m) : ℕ) : ℝ)) * (1 / 2))
        • (v : Point d) := by rw [smul_smul]
  have h4 : ((1 / (m : ℝ)) * ((Fintype.card (secantSpace 1 m) : ℕ) : ℝ)) * (1 / 2) = (1 : ℝ) := by
    rw [hcard]
    field_simp
  rw [h1, h2, h3, h4, one_smul]

/-- The mean of one direction-sampled round is the smoothed gradient. -/
lemma roundOf_mean {d m : ℕ} {W : Measure (Point d × Ω)} [IsProbabilityMeasure W]
    {g : Point d → Ω → ℝ} {fh : Point d → ℝ} {h : ℝ}
    (_hg : Measurable (Function.uncurry g))
    (hint : ∀ x s, Integrable (fun u : Point d × Ω => slotVal h g x s u - halfGrad fh x s) W)
    (hmean : ∀ x s, (∫ u : Point d × Ω, slotVal h g x s u ∂W) = halfGrad fh x s)
    (hm : 0 < m) (x : Point d) :
    (∫ a : secantSpace 1 m → Point d × Ω, roundOf h g x m a ∂(slotLaw 1 m W)) = gradient fh x := by
  classical
  have hsi (t : secantSpace 1 m) :
      Integrable (fun u : Point d × Ω =>
        (if t.2.2 then (1 : ℝ) else -1) • slotVal h g x t.2.2 u) W :=
    integrable_smul_pt (c := (if t.2.2 then (1 : ℝ) else -1)) (slotVal_integrable hint x t.2.2)
  have hu (t : secantSpace 1 m) :
      Integrable (fun a : secantSpace 1 m → Point d × Ω =>
          (if t.2.2 then (1 : ℝ) else -1) • slotVal h g x t.2.2 (a t)) (slotLaw 1 m W) := by
    have h1 : (fun a : secantSpace 1 m → Point d × Ω =>
          (if t.2.2 then (1 : ℝ) else -1) • slotVal h g x t.2.2 (a t))
        = (fun u : Point d × Ω =>
          (if t.2.2 then (1 : ℝ) else -1) • slotVal h g x t.2.2 u) ∘
          (fun a : secantSpace 1 m → Point d × Ω => a t) := rfl
    rw [h1]
    exact (preserving_slotEval W t).integrable_comp_of_integrable (ε := Point d) (hsi t)
  have hc (t : secantSpace 1 m) :
      (∫ a : secantSpace 1 m → Point d × Ω,
          (if t.2.2 then (1 : ℝ) else -1) • slotVal h g x t.2.2 (a t) ∂(slotLaw 1 m W))
        = (1 / 2 : ℝ) • gradient fh x := by
    have h1 : (∫ a : secantSpace 1 m → Point d × Ω,
          (if t.2.2 then (1 : ℝ) else -1) • slotVal h g x t.2.2 (a t) ∂(slotLaw 1 m W))
        = (if t.2.2 then (1 : ℝ) else -1) •
          ∫ a : secantSpace 1 m → Point d × Ω, slotVal h g x t.2.2 (a t) ∂(slotLaw 1 m W) :=
      integral_smul _ _
    rw [h1,
      (Centered.integral_comp_preserving_point (preserving_slotEval W t)
        (slotVal_integrable hint x t.2.2)).trans (hmean x t.2.2), smul_half]
  calc (∫ a : secantSpace 1 m → Point d × Ω, roundOf h g x m a ∂(slotLaw 1 m W))
      = (1 / (m : ℝ)) • ∫ a : secantSpace 1 m → Point d × Ω,
          ∑ t : secantSpace 1 m,
            (if t.2.2 then (1 : ℝ) else -1) • slotVal h g x t.2.2 (a t) ∂(slotLaw 1 m W) :=
            integral_smul _ _
    _ = (1 / (m : ℝ)) • ∑ t : secantSpace 1 m,
          ∫ a : secantSpace 1 m → Point d × Ω,
            (if t.2.2 then (1 : ℝ) else -1) • slotVal h g x t.2.2 (a t) ∂(slotLaw 1 m W) := by
              rw [integral_finsetSum Finset.univ (fun t _ => hu t)]
    _ = (1 / (m : ℝ)) • ∑ _ : secantSpace 1 m, ((1 / 2 : ℝ) • gradient fh x : Point d) := by
              congr 1
              exact Finset.sum_congr rfl fun t _ => hc t
    _ = gradient fh x := hsumv (d := d) (m := m) hm _

/-- Independent probes divide the mean square deviation of the round surrogate by `m`. -/
lemma roundOf_dev {d m : ℕ} {W : Measure (Point d × Ω)} [IsProbabilityMeasure W]
    {g : Point d → Ω → ℝ} {fh : Point d → ℝ} {h G : ℝ}
    (hg : Measurable (Function.uncurry g))
    (hint : ∀ x s, Integrable (fun u : Point d × Ω => slotVal h g x s u - halfGrad fh x s) W)
    (hmean : ∀ x s, (∫ u : Point d × Ω, slotVal h g x s u ∂W) = halfGrad fh x s)
    (hvar2 : ∀ x s, Integrable (fun u : Point d × Ω =>
        ‖slotVal h g x s u - halfGrad fh x s‖ ^ 2) W)
    (hvar : ∀ x s, (∫ u : Point d × Ω, ‖slotVal h g x s u - halfGrad fh x s‖ ^ 2 ∂W) ≤ G ^ 2)
    (hm : 0 < m) (x : Point d) :
    Integrable (fun a : secantSpace 1 m → Point d × Ω => ‖roundOf h g x m a - gradient fh x‖ ^ 2)
        (slotLaw 1 m W) ∧
      (∫ a : secantSpace 1 m → Point d × Ω, ‖roundOf h g x m a - gradient fh x‖ ^ 2
          ∂(slotLaw 1 m W)) ≤ 2 * G ^ 2 / (m : ℝ) := by
  classical
  have hZm (t : secantSpace 1 m) : Measurable (fun a : secantSpace 1 m → Point d × Ω =>
      slotDev h g fh x m a t) :=
    (cellDev_measurable hg h fh x t.2.2).comp (measurable_pi_apply t)
  have hZi (t : secantSpace 1 m) : Integrable (fun a : secantSpace 1 m → Point d × Ω =>
      slotDev h g fh x m a t) (slotLaw 1 m W) :=
    (preserving_slotEval W t).integrable_comp_of_integrable (ε := Point d)
      (cellDev_integrable hint x t.2.2)
  have hZ0 (t : secantSpace 1 m) : (∫ a : secantSpace 1 m → Point d × Ω, slotDev h g fh x m a t ∂(slotLaw 1 m W)) = 0 :=
    ((Centered.integral_comp_preserving_point (preserving_slotEval W t)
      (cellDev_integrable hint x t.2.2))).trans (cellDev_integral hint hmean x t.2.2)
  have hn2 (t : secantSpace 1 m) : (fun a : secantSpace 1 m → Point d × Ω => ‖slotDev h g fh x m a t‖ ^ 2)
      = (fun a => ‖slotVal h g x t.2.2 (a t) - halfGrad fh x t.2.2‖ ^ 2) := by
    refine funext fun a => ?_
    show ‖slotDev h g fh x m a t‖ ^ 2 = ‖slotVal h g x t.2.2 (a t) - halfGrad fh x t.2.2‖ ^ 2
    rw [show slotDev h g fh x m a t = cellDev h g fh x t.2.2 (a t) from rfl,
      cellDev_norm h g fh x t.2.2 (a t)]
  have hcu2 (t : secantSpace 1 m) : Integrable
      (fun u : Point d × Ω => ‖slotVal h g x t.2.2 u - halfGrad fh x t.2.2‖ ^ 2) W :=
    hvar2 x t.2.2
  have hZ2 (t : secantSpace 1 m) : Integrable (fun a => ‖slotDev h g fh x m a t‖ ^ 2) (slotLaw 1 m W) := by
    rw [hn2]
    exact (preserving_slotEval W t).integrable_comp_of_integrable (ε := ℝ) (hcu2 t)
  have hint2 (t : secantSpace 1 m) : Integrable
      (fun u : Point d × Ω => ‖cellDev h g fh x t.2.2 u‖ ^ 2) W :=
    (hvar2 x t.2.2).congr (ae_of_all _ fun u => congrArg (fun v : ℝ => v ^ 2)
      (cellDev_norm h g fh x t.2.2 u).symm)
  have hZb (t : secantSpace 1 m) : (∫ a : secantSpace 1 m → Point d × Ω,
      ‖slotDev h g fh x m a t‖ ^ 2 ∂(slotLaw 1 m W)) ≤ G ^ 2 := by
    have hc2 : (∫ a : secantSpace 1 m → Point d × Ω, ‖cellDev h g fh x t.2.2 (a t)‖ ^ 2
          ∂(slotLaw 1 m W))
        = ∫ u : Point d × Ω, ‖cellDev h g fh x t.2.2 u‖ ^ 2 ∂W :=
        ZerothOrder.integral_comp_preserving (preserving_slotEval W t) (hint2 t)
    calc (∫ a : secantSpace 1 m → Point d × Ω, ‖slotDev h g fh x m a t‖ ^ 2 ∂(slotLaw 1 m W))
        = ∫ a : secantSpace 1 m → Point d × Ω, ‖cellDev h g fh x t.2.2 (a t)‖ ^ 2
            ∂(slotLaw 1 m W) :=
            integral_congr_ae (ae_of_all _ fun a => rfl)
      _ = ∫ u : Point d × Ω, ‖cellDev h g fh x t.2.2 u‖ ^ 2 ∂W := hc2
      _ ≤ G ^ 2 := by
            have he : (fun u : Point d × Ω => ‖cellDev h g fh x t.2.2 u‖ ^ 2)
                = fun u : Point d × Ω => ‖slotVal h g x t.2.2 u - halfGrad fh x t.2.2‖ ^ 2 := by
              funext u
              rw [cellDev_norm h g fh x t.2.2 u]
            rw [he]
            exact hvar x t.2.2
  have hind : iIndepFun (fun t a => slotDev h g fh x m a t) (slotLaw 1 m W) := by
    show iIndepFun (fun (t : secantSpace 1 m) (a : secantSpace 1 m → Point d × Ω) =>
        cellDev h g fh x t.2.2 (a t)) (Measure.pi (fun _ : secantSpace 1 m => W))
    refine iIndepFun_pi (X := fun (t : secantSpace 1 m) (u : Point d × Ω) =>
        cellDev h g fh x t.2.2 u) ?_
    intro t
    exact (cellDev_measurable hg h fh x t.2.2).aemeasurable
  obtain ⟨hSi, hS⟩ := RobustGradient.independent_sum_second_moment
    (fun t a => slotDev h g fh x m a t) hind hZi hZ2 hZ0
  have hcard : ((Fintype.card (secantSpace 1 m) : ℕ) : ℝ) = (2 : ℝ) * (m : ℝ) := by
    rw [card_secantSpace]
    push_cast
    ring
  have hG : (1 / (m : ℝ)) • ∑ _ : secantSpace 1 m, ((1 / 2 : ℝ) • gradient fh x : Point d)
      = gradient fh x := hsumv (d := d) (m := m) hm _
  have hsg (s : Bool) : (if s then (1 : ℝ) else (-1 : ℝ)) • halfGrad fh x s
      = (1 / 2 : ℝ) • gradient fh x := by
    cases s <;> simp [halfGrad]
  have hid (a : secantSpace 1 m → Point d × Ω) :
      roundOf h g x m a - gradient fh x
      = (1 / (m : ℝ)) • ∑ t : secantSpace 1 m, slotDev h g fh x m a t := by
    unfold roundOf
    symm
    calc (1 / (m : ℝ)) • ∑ t : secantSpace 1 m, cellDev h g fh x t.2.2 (a t)
        = (1 / (m : ℝ)) • ∑ t : secantSpace 1 m,
            ((if t.2.2 then (1 : ℝ) else (-1 : ℝ)) • slotVal h g x t.2.2 (a t)
              - (1 / 2 : ℝ) • gradient fh x) := by
              refine congrArg (fun v => (1 / (m : ℝ)) • v) (Finset.sum_congr rfl ?_)
              intro t _
              rw [cellDev_eq h g fh x t.2.2 (a t), smul_sub, hsg t.2.2]
      _ = (1 / (m : ℝ)) • (∑ t : secantSpace 1 m,
              (if t.2.2 then (1 : ℝ) else (-1 : ℝ)) • slotVal h g x t.2.2 (a t)
            - ∑ t : secantSpace 1 m, (1 / 2 : ℝ) • gradient fh x) := by
              rw [Finset.sum_sub_distrib]
      _ = (1 / (m : ℝ)) • ∑ t : secantSpace 1 m,
              (if t.2.2 then (1 : ℝ) else (-1 : ℝ)) • slotVal h g x t.2.2 (a t)
            - gradient fh x := by rw [smul_sub, hG]
  have hsq (a : secantSpace 1 m → Point d × Ω) : ‖roundOf h g x m a - gradient fh x‖ ^ 2
      = ((1 / (m : ℝ)) ^ 2) * ‖∑ t : secantSpace 1 m, slotDev h g fh x m a t‖ ^ 2 := by
    rw [hid a, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (m : ℝ)), mul_pow]
  refine ⟨(Integrable.smul ((1 / (m : ℝ)) ^ 2) hSi).congr (ae_of_all _ fun a => (hsq a).symm), ?_⟩
  have h1 : (∫ a : secantSpace 1 m → Point d × Ω, ‖roundOf h g x m a - gradient fh x‖ ^ 2
        ∂(slotLaw 1 m W))
      = ((1 / (m : ℝ)) ^ 2) *
        ∫ a : secantSpace 1 m → Point d × Ω, ‖∑ t : secantSpace 1 m, slotDev h g fh x m a t‖ ^ 2
          ∂(slotLaw 1 m W) := by
    refine (integral_congr_ae (ae_of_all _ fun a => hsq a)).trans (integral_const_mul _ _)
  rw [h1]
  have hsum : (∑ t : secantSpace 1 m,
        ∫ a : secantSpace 1 m → Point d × Ω, ‖slotDev h g fh x m a t‖ ^ 2 ∂(slotLaw 1 m W))
      ≤ ((2 : ℝ) * (m : ℝ)) * G ^ 2 := by
    calc (∑ t : secantSpace 1 m,
          ∫ a : secantSpace 1 m → Point d × Ω, ‖slotDev h g fh x m a t‖ ^ 2 ∂(slotLaw 1 m W))
        ≤ ∑ t : secantSpace 1 m, G ^ 2 := Finset.sum_le_sum fun t _ => hZb t
      _ = ((Fintype.card (secantSpace 1 m) : ℕ) : ℝ) * G ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ((2 : ℝ) * (m : ℝ)) * G ^ 2 := by rw [hcard]
  have hfin : ((1 / (m : ℝ)) ^ 2) * (((2 : ℝ) * (m : ℝ)) * G ^ 2) = 2 * G ^ 2 / (m : ℝ) := by
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    field_simp
  calc ((1 / (m : ℝ)) ^ 2)
        * ∫ a : secantSpace 1 m → Point d × Ω,
          ‖∑ t : secantSpace 1 m, slotDev h g fh x m a t‖ ^ 2 ∂(slotLaw 1 m W)
      ≤ ((1 / (m : ℝ)) ^ 2)
          * ∑ t : secantSpace 1 m,
            ∫ a : secantSpace 1 m → Point d × Ω, ‖slotDev h g fh x m a t‖ ^ 2 ∂(slotLaw 1 m W) :=
          mul_le_mul_of_nonneg_left hS.le (sq_nonneg _)
      _ ≤ ((1 / (m : ℝ)) ^ 2) * (((2 : ℝ) * (m : ℝ)) * G ^ 2) :=
          mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
      _ = 2 * G ^ 2 / (m : ℝ) := hfin

end OracleTemplate.SecantPolyak.DirectionSampled

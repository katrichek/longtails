import LongTails.Proofs.SecantPolyakScheduledStream
import LongTails.Proofs.InexactAcceleratedStep
import LongTails.Proofs.GdConvex

set_option maxHeartbeats 1000000

namespace OracleTemplate.SecantPolyak.Accelerated

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
open OracleTemplate
open SecantDescent SecantPolyak ZerothOrder InexactGradient Scheduled
open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {Ω : Type} [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]

/-- One accelerated round: the momentum probe point is estimated by `m k` secant replicas. -/
noncomputable def accelStepSched {d M : ℕ} (m : ℕ → ℕ) (hmM : ∀ k, m k ≤ M)
    (L μ θ : ℝ) (g : Point d → Ω → ℝ) (h : ℝ) (k : ℕ) (s : Point d × Point d)
    (ω : secantSpace d M → Ω) : Point d × Point d :=
  step L μ θ s (reply (g := g) h (query θ s) (toCells fun t => ω (cellInj (hmM k) t)))

/-- Regrouping the slots of a subschedule is measurable. -/
lemma measurable_toCellsRestr {d M m : ℕ} (hM : m ≤ M) :
    Measurable (fun ω : secantSpace d M → Ω =>
      toCells (fun t : secantSpace d m => ω (cellInj hM t))) := by
  refine measurable_pi_iff.mpr (fun r => measurable_pi_iff.mpr (fun ib => ?_))
  exact measurable_pi_apply (cellInj hM (r, ib))

/-- The reply of one accelerated round, at the ambient slot law, is jointly measurable. -/
lemma measurable_replyRound {d M : ℕ} (m : ℕ → ℕ) (hmM : ∀ k, m k ≤ M)
    {g : Point d → Ω → ℝ} (hg : Measurable (Function.uncurry g)) (θ h : ℝ) (k : ℕ) :
    Measurable (fun q : (Point d × Point d) × (secantSpace d M → Ω) =>
      reply (g := g) h (query θ q.1)
        (toCells (fun t : secantSpace d (m k) => q.2 (cellInj (hmM k) t)))) := by
  set Φ : ((Point d × Point d) × (secantSpace d M → Ω)) →
      Point d × (Fin (m k) → Fin d × Bool → Ω) :=
    fun q => (query θ q.1, toCells fun t : secantSpace d (m k) => q.2 (cellInj (hmM k) t))
      with hΦ
  have hΦm : Measurable Φ := by
    refine Measurable.prodMk ?_ ?_
    · show Measurable (fun q : (Point d × Point d) × (secantSpace d M → Ω) => query θ q.1)
      have hc : Continuous (fun p : Point d × Point d => (1 / (1 + θ)) • (p.1 + θ • p.2)) := by
        fun_prop
      exact hc.measurable.comp measurable_fst
    · show Measurable (fun q : (Point d × Point d) × (secantSpace d M → Ω) =>
          toCells (fun t : secantSpace d (m k) => q.2 (cellInj (hmM k) t)))
      have hc : Measurable (fun ω : secantSpace d (m k) → Ω =>
          toCells (ω : secantSpace d (m k) → Ω)) :=
        (MeasurableEquiv.curry (Fin (m k)) (Fin d × Bool) Ω).measurable
      have hr : Measurable (fun ω : secantSpace d M → Ω =>
          fun t : secantSpace d (m k) => ω (cellInj (hmM k) t)) :=
        measurable_pi_iff.mpr (fun t => measurable_pi_apply (cellInj (hmM k) t))
      exact hc.comp (hr.comp measurable_snd)
  have hrep : Measurable (fun q : Point d × (Fin (m k) → Fin d × Bool → Ω) =>
      reply (g := g) h q.1 q.2) := measurable_reply_joint (d := d) (m := m k) hg h
  have heq : (fun q : (Point d × Point d) × (secantSpace d M → Ω) =>
      reply (g := g) h (query θ q.1)
        (toCells (fun t : secantSpace d (m k) => q.2 (cellInj (hmM k) t))))
      = (fun q : Point d × (Fin (m k) → Fin d × Bool → Ω) => reply (g := g) h q.1 q.2) ∘ Φ := by
    funext q
    rfl
  exact heq ▸ hrep.comp hΦm

/-- The joint map of one accelerated round is measurable. -/
lemma measurable_accelStepSched_joint {d M : ℕ} (m : ℕ → ℕ) (hmM : ∀ k, m k ≤ M)
    {g : Point d → Ω → ℝ} (hg : Measurable (Function.uncurry g)) (L μ θ h : ℝ) (k : ℕ) :
    Measurable (fun q : (Point d × Point d) × (secantSpace d M → Ω) =>
      accelStepSched m hmM L μ θ g h k q.1 q.2) := by
  have h1 : Measurable (fun q : (Point d × Point d) × (secantSpace d M → Ω) =>
      reply (g := g) h (query θ q.1)
        (toCells (fun t : secantSpace d (m k) => q.2 (cellInj (hmM k) t)))) :=
    measurable_replyRound m hmM hg θ h k
  have hstepc : Continuous (fun p : (Point d × Point d) × Point d => step L μ θ p.1 p.2) := by
    show Continuous (fun p : (Point d × Point d) × Point d =>
      ((1 / (1 + θ)) • (p.1.1 + θ • p.1.2) - (1 / L) • p.2,
        (1 - θ) • p.1.2 + θ • ((1 / (1 + θ)) • (p.1.1 + θ • p.1.2)) - (2 * θ / μ) • p.2))
    fun_prop
  set Ψ : ((Point d × Point d) × (secantSpace d M → Ω)) → (Point d × Point d) × Point d :=
    fun q => (q.1, reply (g := g) h (query θ q.1)
      (toCells (fun t : secantSpace d (m k) => q.2 (cellInj (hmM k) t)))) with hΨ
  have hΨm : Measurable Ψ := measurable_fst.prodMk h1
  have h2 : Measurable (fun p : (Point d × Point d) × Point d => step L μ θ p.1 p.2) :=
    hstepc.measurable
  have heq2 : (fun q : (Point d × Point d) × (secantSpace d M → Ω) =>
      accelStepSched m hmM L μ θ g h k q.1 q.2)
      = (fun p : (Point d × Point d) × Point d => step L μ θ p.1 p.2) ∘ Ψ := by
    funext q
    rfl
  exact heq2 ▸ h2.comp hΨm

/-- The accelerated potential is measurable. -/
lemma measurable_potentialZO {f : Point d → ℝ} (hf : Measurable f) {μ : ℝ} {xstar : Point d} :
    Measurable (fun s : Point d × Point d => potential f μ xstar s) := by
  have h1 : Continuous (fun s : Point d × Point d => ‖s.2 - xstar‖ ^ 2) := by fun_prop
  show Measurable (fun s : Point d × Point d => f s.1 - f xstar + μ / 4 * ‖s.2 - xstar‖ ^ 2)
  refine ((hf.comp measurable_fst).sub measurable_const).add ?_
  show Measurable (fun s : Point d × Point d => μ / 4 * ‖s.2 - xstar‖ ^ 2)
  exact measurable_const.mul h1.measurable

/-- One accelerated step contracts the momentum potential up to the squared surrogate error. -/
lemma accel_potential_step {f : Point d → ℝ} {L μ θ : ℝ} {xstar : Point d}
    (hL : 0 < L) (hμ : 0 < μ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hθL : 16 * L * θ ^ 2 ≤ μ)
    (hgr : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hsc : ∀ x y, f x + ⟪gradient f x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (hmin : IsMinOn f Set.univ xstar) (s : Point d × Point d) (v : Point d) :
    potential f μ xstar (step L μ θ s v) ≤ (1 - θ / 2) * potential f μ xstar s
        + 2 * (3 / (4 * L) + 2 * θ / μ) * ‖v - gradient f (query θ s)‖ ^ 2 := by
  have hminf : ∀ x, f xstar ≤ f x := fun x => hmin (Set.mem_univ x)
  have hs := step_potential (E := Point d) (f := f) (grad := gradient f) (L := L) (μ := μ)
    (α := (0 : ℝ)) (θ := θ) (xs := xstar) (hL := hL) (hμ := hμ) (hα0 := le_refl 0)
    (hα1 := by norm_num) (hθ0 := hθ0) (hθ1 := hθ1) (hθL := by simpa using hθL)
    (hθα := by simpa using le_of_lt hμ) (hup := _root_.OracleTemplate.Gradient.smooth_upper_bound hgr hlip)
    (hsc := hsc) (hmin := fun x => hminf x) (s := s) (g := v)
    (δ := ‖v - gradient f (query θ s)‖) (by rw [zero_mul, zero_add])
  have h2 : (2 : ℝ) / (1 - 0) = 2 := by norm_num
  rw [h2] at hs
  exact hs

/-- One accelerated round contracts the expected potential and pays its own mean-square error. -/
lemma accel_one_step_ambient {d M : ℕ} {m : ℕ → ℕ} (hmM : ∀ k, m k ≤ M) (hm : ∀ k, 0 < m k)
    {g : Point d → Ω → ℝ} {f : Point d → ℝ} {σ L μ h θ : ℝ} {xstar : Point d}
    (hh : 0 < h) (hL : 0 < L) (hμ : 0 < μ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hθL : 16 * L * θ ^ 2 ≤ μ)
    (hg : Measurable (Function.uncurry g))
    (hgi : ∀ x, Integrable (g x) p)
    (hmean : ∀ x, (∫ ω, g x ω ∂p) = f x)
    (hvi : ∀ x, Integrable (fun ω => (g x ω - f x) ^ 2) p)
    (hv : ∀ x, (∫ ω, (g x ω - f x) ^ 2 ∂p) ≤ σ ^ 2)
    (hc : ConvexOn ℝ Set.univ f)
    (hgr : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hsc : ∀ x y, f x + ⟪gradient f x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (hmin : IsMinOn f Set.univ xstar)
    (k : ℕ) (s : Point d × Point d) :
    Integrable (fun ω => potential f μ xstar (accelStepSched m hmM L μ θ g h k s ω))
        (slotLaw d M p) ∧
      (∫ ω, potential f μ xstar (accelStepSched m hmM L μ θ g h k s ω) ∂(slotLaw d M p)) ≤
        (1 - θ / 2) * potential f μ xstar s
          + 2 * (3 / (4 * L) + 2 * θ / μ)
            * (8 * (d : ℝ) * σ ^ 2 / (h ^ 2 * (m k)) + 2 * ((d : ℝ) * (L * h / 2) ^ 2)) := by
  classical
  have hminf : ∀ x, f xstar ≤ f x := fun x => hmin (Set.mem_univ x)
  have hf : Measurable f :=
    (continuous_iff_continuousAt.mpr fun x => (hgr x).continuousAt).measurable
  set a : ℝ := (1 - θ / 2) * potential f μ xstar s with hadef
  set C : ℝ := 2 * (3 / (4 * L) + 2 * θ / μ) with hcdef
  set y : Point d := query θ s with hydef
  set E : (secantSpace d M → Ω) → ℝ := fun ω => ‖reply (g := g) h y
      (toCells (fun t : secantSpace d (m k) => ω (cellInj (hmM k) t))) - gradient f y‖ ^ 2
    with hedef
  set S1 : (secantSpace d M → Ω) → Point d × Point d :=
    (fun q : (Point d × Point d) × (secantSpace d M → Ω) =>
        accelStepSched m hmM L μ θ g h k q.1 q.2) ∘ (fun ω : secantSpace d M → Ω => (s, ω))
    with hS1def
  set F : (secantSpace d M → Ω) → ℝ := potential f μ xstar ∘ S1 with hfdef
  have hS1m : Measurable S1 :=
    (measurable_accelStepSched_joint m hmM hg L μ θ h k).comp
      (measurable_const.prodMk measurable_id)
  have hFmeas : Measurable F := (measurable_potentialZO hf).comp hS1m
  have hC0 : 0 ≤ C := by
    show 0 ≤ 2 * (3 / (4 * L) + 2 * θ / μ)
    positivity
  have ha0 : 0 ≤ a := by
    show 0 ≤ (1 - θ / 2) * potential f μ xstar s
    refine mul_nonneg (by linarith) ?_
    show 0 ≤ f s.1 - f xstar + μ / 4 * ‖s.2 - xstar‖ ^ 2
    exact add_nonneg (sub_nonneg.mpr (hminf s.1)) (mul_nonneg (by positivity) (sq_nonneg _))
  have hVnonneg : ∀ t : Point d × Point d, 0 ≤ potential f μ xstar t := by
    intro t
    exact add_nonneg (sub_nonneg.mpr (hminf t.1)) (mul_nonneg (by positivity) (sq_nonneg _))
  obtain ⟨hI2, hb2⟩ := reply_error_moment (d := d) (m := m k) (g := g) (f := f) (σ := σ)
    (L := L) (h := h) hh hg hgi hmean hvi hv hc hgr hlip (hm k) y
  have hp : MeasurePreserving (fun ω : secantSpace d M → Ω =>
      toCells (fun t : secantSpace d (m k) => ω (cellInj (hmM k) t)))
      (slotLaw d M p) (batchLaw d (m k) p) :=
    (measurePreserving_toCells d (m k)).comp (measurePreserving_cellInj (hmM k))
  have hpath : ∀ ω : secantSpace d M → Ω, F ω ≤ a + C * E ω := by
    intro ω
    show potential f μ xstar (accelStepSched m hmM L μ θ g h k s ω) ≤
      (1 - θ / 2) * potential f μ xstar s
        + 2 * (3 / (4 * L) + 2 * θ / μ)
          * ‖reply (g := g) h y
            (toCells (fun t : secantSpace d (m k) => ω (cellInj (hmM k) t)))
            - gradient f y‖ ^ 2
    set v : Point d := reply (g := g) h y
      (toCells (fun t : secantSpace d (m k) => ω (cellInj (hmM k) t))) with hvdef
    have hg' : ‖v - gradient f y‖ ≤ (0 : ℝ) * ‖gradient f y‖ + ‖v - gradient f y‖ := by
      rw [zero_mul, zero_add]
    have hs := _root_.OracleTemplate.InexactGradient.step_potential (E := Point d) (f := f)
      (grad := gradient f) (L := L) (μ := μ) (α := (0 : ℝ)) (θ := θ) (xs := xstar) (hL := hL)
      (hμ := hμ) (hα0 := le_refl 0) (hα1 := by norm_num) (hθ0 := hθ0) (hθ1 := hθ1)
      (hθL := by simpa using hθL) (hθα := by simpa using le_of_lt hμ)
      (hup := _root_.OracleTemplate.Gradient.smooth_upper_bound hgr hlip) (hsc := hsc)
      (hmin := fun x => hminf x) (s := s) (g := v) (δ := ‖v - gradient f y‖) hg'
    have h2 : (2 : ℝ) / (1 - 0) = 2 := by norm_num
    rw [h2] at hs
    exact hs
  have hEi : Integrable E (slotLaw d M p) := by
    show Integrable (fun ω : secantSpace d M → Ω => ‖reply (g := g) h y
        (toCells (fun t : secantSpace d (m k) => ω (cellInj (hmM k) t))) - gradient f y‖ ^ 2)
        (slotLaw d M p)
    exact hp.integrable_comp_of_integrable (ε := ℝ)
      (g := fun ξ : Fin (m k) → Fin d × Bool → Ω => ‖reply (g := g) h y ξ - gradient f y‖ ^ 2) hI2
  have hbnd : Integrable (fun ω : secantSpace d M → Ω => a + C * E ω) (slotLaw d M p) :=
    (integrable_const a).add (hEi.const_mul C)
  have hFi : Integrable F (slotLaw d M p) :=
    hbnd.mono' hFmeas.aestronglyMeasurable (ae_of_all _ fun ω => by
      have h1 := hpath ω
      have h0 : 0 ≤ F ω := hVnonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact h1)
  refine ⟨hFi, ?_⟩
  set φ : (Fin (m k) → Fin d × Bool → Ω) → ℝ :=
    fun ξ => ‖reply (g := g) h y ξ - gradient f y‖ ^ 2 with hφdef
  set q : (secantSpace d M → Ω) → (Fin (m k) → Fin d × Bool → Ω) :=
    fun ω => toCells (fun t : secantSpace d (m k) => ω (cellInj (hmM k) t)) with hqdef
  have hEF : E = φ ∘ q := by
    show (fun ω : secantSpace d M → Ω => ‖reply (g := g) h y
        (toCells (fun t : secantSpace d (m k) => ω (cellInj (hmM k) t))) - gradient f y‖ ^ 2)
      = φ ∘ q
    funext ω
    rfl
  have hstep : (∫ ω : secantSpace d M → Ω, (φ ∘ q) ω ∂(slotLaw d M p))
      = ∫ ξ, ‖reply (g := g) h y ξ - gradient f y‖ ^ 2 ∂(batchLaw d (m k) p) :=
    integral_comp_preserving hp hI2
  have hEint : (∫ ω, E ω ∂(slotLaw d M p))
      = ∫ ξ, ‖reply (g := g) h y ξ - gradient f y‖ ^ 2 ∂(batchLaw d (m k) p) :=
    (integral_congr_ae (ae_of_all _ fun ω => hEF ▸ rfl)).trans hstep
  have hlin : (∫ ω : secantSpace d M → Ω, (a + C * E ω) ∂(slotLaw d M p))
      = a + C * ∫ ω, E ω ∂(slotLaw d M p) := by
    have hCE : Integrable (fun ω : secantSpace d M → Ω => C * E ω) (slotLaw d M p) :=
      hEi.const_mul C
    have h1 : (∫ ω : secantSpace d M → Ω, (a + C * E ω) ∂(slotLaw d M p))
        = (∫ ω : secantSpace d M → Ω, a ∂(slotLaw d M p))
          + ∫ ω : secantSpace d M → Ω, C * E ω ∂(slotLaw d M p) :=
      integral_add (integrable_const a) hCE
    have h2 : (∫ ω : secantSpace d M → Ω, a ∂(slotLaw d M p)) = a := by
      rw [integral_const, probReal_univ, one_smul]
    have h3 : (∫ ω : secantSpace d M → Ω, C * E ω ∂(slotLaw d M p))
        = C * ∫ ω : secantSpace d M → Ω, E ω ∂(slotLaw d M p) := integral_const_mul C E
    rw [h1, h2, h3]
  have hmono : (∫ ω, F ω ∂(slotLaw d M p)) ≤ a + C * ∫ ω, E ω ∂(slotLaw d M p) :=
    (integral_mono hFi hbnd hpath).trans (le_of_eq hlin)
  have hb2' : (∫ ω, E ω ∂(slotLaw d M p))
      ≤ 8 * (d : ℝ) * σ ^ 2 / (h ^ 2 * (m k)) + 2 * ((d : ℝ) * (L * h / 2) ^ 2) :=
    hEint.symm ▸ hb2
  have hc2 : C * ∫ ω, E ω ∂(slotLaw d M p)
      ≤ C * (8 * (d : ℝ) * σ ^ 2 / (h ^ 2 * (m k)) + 2 * ((d : ℝ) * (L * h / 2) ^ 2)) :=
    mul_le_mul_of_nonneg_left hb2' hC0
  have h5 : a + C * ∫ ω, E ω ∂(slotLaw d M p)
      ≤ a + C * (8 * (d : ℝ) * σ ^ 2 / (h ^ 2 * (m k)) + 2 * ((d : ℝ) * (L * h / 2) ^ 2)) := by
    linarith
  exact hmono.trans h5

/-- K accelerated rounds contract the potential geometrically and pay the graded error sum. -/
lemma accel_sched_potential {d M : ℕ} {m : ℕ → ℕ} (hmM : ∀ k, m k ≤ M) (hm : ∀ k, 0 < m k)
    {g : Point d → Ω → ℝ} {f : Point d → ℝ} {σ L μ h θ : ℝ} {xstar : Point d}
    (hh : 0 < h) (hL : 0 < L) (hμ : 0 < μ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hθL : 16 * L * θ ^ 2 ≤ μ)
    (hg : Measurable (Function.uncurry g))
    (hgi : ∀ x, Integrable (g x) p)
    (hmean : ∀ x, (∫ ω, g x ω ∂p) = f x)
    (hvi : ∀ x, Integrable (fun ω => (g x ω - f x) ^ 2) p)
    (hv : ∀ x, (∫ ω, (g x ω - f x) ^ 2 ∂p) ≤ σ ^ 2)
    (hc : ConvexOn ℝ Set.univ f)
    (hgr : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hsc : ∀ x y, f x + ⟪gradient f x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (hmin : IsMinOn f Set.univ xstar)
    (i K : ℕ) (s : Point d × Point d) :
    Integrable (fun Ξ => potential f μ xstar
        (runSched (fun k s' ω => accelStepSched m hmM L μ θ g h k s' ω) i K s Ξ))
        (Measure.pi (fun _ : Fin K => slotLaw d M p)) ∧
      (∫ Ξ, potential f μ xstar
        (runSched (fun k s' ω => accelStepSched m hmM L μ θ g h k s' ω) i K s Ξ)
        ∂Measure.pi (fun _ : Fin K => slotLaw d M p)) ≤
      (1 - θ / 2) ^ K * potential f μ xstar s
        + ∑ k ∈ Finset.range K, (1 - θ / 2) ^ (K - 1 - k)
            * (2 * (3 / (4 * L) + 2 * θ / μ)
              * (8 * (d : ℝ) * σ ^ 2 / (h ^ 2 * (m (i + k)))
                + 2 * ((d : ℝ) * (L * h / 2) ^ 2))) := by
  classical
  have hf : Measurable f :=
    (continuous_iff_continuousAt.mpr fun x => (hgr x).continuousAt).measurable
  have hVnonneg : ∀ t : Point d × Point d, 0 ≤ potential f μ xstar t := by
    intro t
    have hminf : ∀ x, f xstar ≤ f x := fun x => hmin (Set.mem_univ x)
    show 0 ≤ f t.1 - f xstar + μ / 4 * ‖t.2 - xstar‖ ^ 2
    exact add_nonneg (sub_nonneg.mpr (hminf t.1)) (mul_nonneg (by positivity) (sq_nonneg _))
  have hrho : 0 ≤ (1 : ℝ) - θ / 2 := by linarith
  refine sched_iterate_accuracy (d := d) (M := M)
    (step := fun k s' ω => accelStepSched m hmM L μ θ g h k s' ω) (ρ := (1 : ℝ) - θ / 2)
    (c := fun k => 2 * (3 / (4 * L) + 2 * θ / μ)
      * (8 * (d : ℝ) * σ ^ 2 / (h ^ 2 * (m k)) + 2 * ((d : ℝ) * (L * h / 2) ^ 2)))
    (fun k => measurable_accelStepSched_joint m hmM hg L μ θ h k)
    ⟨slotLaw d M p, inferInstance⟩ (potential f μ xstar) (measurable_potentialZO hf) hVnonneg hrho
    (fun k => by positivity) (fun k s' =>
      accel_one_step_ambient (m := m) hmM hm hh hL hμ hθ0 hθ1 hθL hg hgi hmean hvi hv hc hgr hlip
        hsc hmin k s') i K s

/-- K accelerated rounds bound the expected suboptimality of the momentum output. -/
lemma accel_sched_gap {d M : ℕ} {m : ℕ → ℕ} (hmM : ∀ k, m k ≤ M) (hm : ∀ k, 0 < m k)
    {g : Point d → Ω → ℝ} {f : Point d → ℝ} {σ L μ h θ : ℝ} {xstar : Point d}
    (hh : 0 < h) (hL : 0 < L) (hμ : 0 < μ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hθL : 16 * L * θ ^ 2 ≤ μ)
    (hg : Measurable (Function.uncurry g))
    (hgi : ∀ x, Integrable (g x) p)
    (hmean : ∀ x, (∫ ω, g x ω ∂p) = f x)
    (hvi : ∀ x, Integrable (fun ω => (g x ω - f x) ^ 2) p)
    (hv : ∀ x, (∫ ω, (g x ω - f x) ^ 2 ∂p) ≤ σ ^ 2)
    (hc : ConvexOn ℝ Set.univ f)
    (hgr : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hsc : ∀ x y, f x + ⟪gradient f x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (hmin : IsMinOn f Set.univ xstar)
    (x0 : Point d) (K : ℕ) :
    Integrable (fun Ξ : Fin K → secantSpace d M → Ω =>
        f (runSched (fun k s' ω => accelStepSched m hmM L μ θ g h k s' ω) 0 K (x0, x0) Ξ).1
          - f xstar) (Measure.pi (fun _ : Fin K => slotLaw d M p)) ∧
      (∫ Ξ, f (runSched (fun k s' ω => accelStepSched m hmM L μ θ g h k s' ω) 0 K (x0, x0) Ξ).1
        - f xstar ∂Measure.pi (fun _ : Fin K => slotLaw d M p)) ≤
      (1 - θ / 2) ^ K * (f x0 - f xstar + μ / 4 * ‖x0 - xstar‖ ^ 2)
        + ∑ k ∈ Finset.range K, (1 - θ / 2) ^ (K - 1 - k)
            * (2 * (3 / (4 * L) + 2 * θ / μ)
              * (8 * (d : ℝ) * σ ^ 2 / (h ^ 2 * (m k)) + 2 * ((d : ℝ) * (L * h / 2) ^ 2))) := by
  classical
  have hminf : ∀ x, f xstar ≤ f x := fun x => hmin (Set.mem_univ x)
  have hf : Measurable f :=
    (continuous_iff_continuousAt.mpr fun x => (hgr x).continuousAt).measurable
  obtain ⟨hIf, hb⟩ := accel_sched_potential (d := d) (m := m) hmM hm (g := g) (f := f) (σ := σ)
    (L := L) (μ := μ) (h := h) (θ := θ) (xstar := xstar) hh hL hμ hθ0 hθ1 hθL hg hgi hmean hvi hv
    hc hgr hlip hsc hmin (i := 0) (K := K) (s := (x0, x0))
  simp only [Nat.zero_add] at hb
  have hrun2 : Measurable ((fun q : (Point d × Point d) × (Fin K → secantSpace d M → Ω) =>
      runSched (fun k s' ω => accelStepSched m hmM L μ θ g h k s' ω) 0 K q.1 q.2) ∘
      (fun Ξ : Fin K → secantSpace d M → Ω => ((x0, x0), Ξ))) :=
    (measurable_runSched (fun k => measurable_accelStepSched_joint m hmM hg L μ θ h k) K 0).comp
      (measurable_const.prodMk measurable_id)
  have hf1 : Measurable (fun p : Point d × Point d => p.1) := continuous_fst.measurable
  have hgapMeas : Measurable ((fun v : Point d => f v - f xstar) ∘
      (fun p : Point d × Point d => p.1) ∘
      (fun Ξ : Fin K → secantSpace d M → Ω =>
        runSched (fun k s' ω => accelStepSched m hmM L μ θ g h k s' ω) 0 K (x0, x0) Ξ)) :=
    (hf.sub measurable_const).comp (hf1.comp hrun2)
  have hpoint : ∀ Ξ : Fin K → secantSpace d M → Ω,
      f (runSched (fun k s' ω => accelStepSched m hmM L μ θ g h k s' ω) 0 K (x0, x0) Ξ).1
          - f xstar
        ≤ potential f μ xstar
          (runSched (fun k s' ω => accelStepSched m hmM L μ θ g h k s' ω) 0 K (x0, x0) Ξ) :=
    fun Ξ => le_add_of_nonneg_right (mul_nonneg (by positivity) (sq_nonneg _))
  have hgapInt : Integrable (fun Ξ : Fin K → secantSpace d M → Ω =>
      f (runSched (fun k s' ω => accelStepSched m hmM L μ θ g h k s' ω) 0 K (x0, x0) Ξ).1
        - f xstar) (Measure.pi (fun _ : Fin K => slotLaw d M p)) :=
    hIf.mono' hgapMeas.aestronglyMeasurable (ae_of_all _ fun Ξ => by
      have h0 : 0 ≤
          f (runSched (fun k s' ω => accelStepSched m hmM L μ θ g h k s' ω) 0 K (x0, x0) Ξ).1
            - f xstar := sub_nonneg.mpr (hminf _)
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact hpoint Ξ)
  exact ⟨hgapInt, (integral_mono hgapInt hIf hpoint).trans hb⟩

end OracleTemplate.SecantPolyak.Accelerated

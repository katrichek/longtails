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

end OracleTemplate.SecantPolyak.Accelerated

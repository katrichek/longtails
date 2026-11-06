import LongTails.Template
import Mathlib.Analysis.Calculus.Gradient.Basic
import LongTails.Setups.ZerothOrderSmoothAndConvex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Probability.Independence.Basic

namespace LongTails.Setups.ZerothOrderSmoothingStronglyConvex

open OracleTemplate MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
open LongTails.Setups.ZerothOrderSmoothAndConvex

structure Params where
  d : ℕ
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  L : ℝ
  μ : ℝ
  G : ℝ
  R : ℝ
  ε : ℝ
  h : ℝ
  x0 : Point d
  nu : ProbabilityMeasure (Point d)

attribute [instance] Params.measurableΩ

/-- The probe point of side `s`: shift the base point by `± h` along the sampled direction. -/
noncomputable def dirPoint {q : Params} (x z : Point q.d) (s : Bool) : Point q.d :=
  x + (if s then q.h else -q.h) • z

/-- One probe of the zeroth-order oracle: `z` is the sampled direction, `ω` the value sample, and
`s` selects the side of the probe. -/
noncomputable def dirSlot {q : Params} (g : Point q.d → q.Ω → ℝ) (x : Point q.d) (s : Bool)
    (z : Point q.d) (ω : q.Ω) : Point q.d :=
  (1 / (2 * q.h)) • ((g (dirPoint x z s) ω) • z)

/-- The law of one probe: an independent direction and value sample. -/
noncomputable def probeLaw {q : Params} (p : Measure q.Ω) : Measure (Point q.d × q.Ω) :=
  (q.nu : Measure (Point q.d)).prod p

/-- The signed mean of a probe: the probe of side `s` estimates half of the smoothed gradient. -/
noncomputable def dirCenter {q : Params} (fh : Point q.d → ℝ) (x : Point q.d) (s : Bool) :
    Point q.d :=
  (if s then (1 / 2 : ℝ) else -(1 / 2 : ℝ)) • gradient fh x

/-- The reply of one probe: the noisy value together with the direction the oracle probed along. -/
noncomputable def dirReply {q : Params} (g : Point q.d → q.Ω → ℝ) (x : Point q.d) (s : Bool)
    (u : Point q.d × q.Ω) : ℝ × Point q.d :=
  (g (dirPoint x u.1 s) u.2, u.1)

/-- The surrogate recovered from one reply: the reported value times the reported direction. -/
noncomputable def dirTerm {q : Params} (r : ℝ × Point q.d) : Point q.d :=
  (1 / (2 * q.h)) • (r.1 • r.2)

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := Point p.d → ℝ
  Query p := Point p.d × Bool
  Reply p := ℝ × Point p.d
  Output p := Point p.d
  publicInput p := p
  valid q :=
    0 < q.d ∧ 0 < q.L ∧ 0 ≤ q.R ∧ 0 ≤ q.G ∧ 0 < q.μ ∧ 0 < q.ε ∧ 0 < q.h ∧
      2 * q.L * q.h ^ 2 * (q.d : ℝ) ≤ q.ε
  admissible q f O :=
    ∃ (g : Point q.d → q.Ω → ℝ) (p : ProbabilityMeasure q.Ω)
      (P : ProbabilityMeasure (ℕ → Point q.d × q.Ω)),
      ProbabilityTheory.iIndepFun (fun k (u : ℕ → Point q.d × q.Ω) => u k)
        (P : Measure (ℕ → Point q.d × q.Ω)) ∧
      (∀ k : ℕ,
        Measure.map (fun (u : ℕ → Point q.d × q.Ω) => u k)
          (P : Measure (ℕ → Point q.d × q.Ω)) = (probeLaw p : Measure (Point q.d × q.Ω))) ∧
      O = { Seed := fun _ => Point q.d × q.Ω, law := P,
            answer := fun _ (_, r) u => dirReply g r.1 r.2 u } ∧
      Measurable (Function.uncurry g) ∧ Measurable f ∧
      (∃ xstar, IsMinOn f Set.univ xstar ∧ ‖q.x0 - xstar‖ ≤ q.R) ∧
      ∃ (fh : Point q.d → ℝ),
        ConvexOn ℝ Set.univ fh ∧
        (∀ x, HasGradientAt fh (gradient fh x) x) ∧
        (∀ x y, ‖gradient fh x - gradient fh y‖ ≤ q.L * ‖x - y‖) ∧
        (∀ x y, fh x + ⟪gradient fh x, y - x⟫ + q.μ / 2 * ‖y - x‖ ^ 2 ≤ fh y) ∧
        (∃ xh, IsMinOn fh Set.univ xh ∧ ‖q.x0 - xh‖ ≤ q.R) ∧
        (∀ x, fh x - f x ≤ q.L * q.h ^ 2 * (q.d : ℝ) / 2) ∧
        (∀ x, f x - fh x ≤ q.L * q.h ^ 2 * (q.d : ℝ) / 2) ∧
        (∀ x s, Integrable (fun u : Point q.d × q.Ω =>
            dirSlot g x s u.1 u.2 - dirCenter fh x s) (probeLaw p)) ∧
        (∀ x s, (∫ u : Point q.d × q.Ω, dirSlot g x s u.1 u.2 ∂(probeLaw p))
            = dirCenter fh x s) ∧
        (∀ x s, Integrable (fun u : Point q.d × q.Ω =>
            ‖dirSlot g x s u.1 u.2 - dirCenter fh x s‖ ^ 2) (probeLaw p)) ∧
        (∀ x s, (∫ u : Point q.d × q.Ω,
            ‖dirSlot g x s u.1 u.2 - dirCenter fh x s‖ ^ 2 ∂(probeLaw p)) ≤ q.G ^ 2)
  successful q f output P :=
    Measurable output ∧
      ∃ xstar, IsMinOn f Set.univ xstar ∧
        Integrable (fun ω => f (output ω) - f xstar) (P : Measure _) ∧
        (∫ ω, f (output ω) - f xstar ∂(P : Measure _)) ≤ q.ε

/-- Value conversion: a point that is good for the smoothed objective is good for the original one. -/
lemma smoothed_value_bound {q : Params} {f fh : Point q.d → ℝ} {xstar xh : Point q.d} {B : ℝ}
    (_hmin : IsMinOn f Set.univ xstar) (hminh : IsMinOn fh Set.univ xh)
    (hup : ∀ x, fh x - f x ≤ B) (hdown : ∀ x, f x - fh x ≤ B) (y : Point q.d) :
    f y - f xstar ≤ (fh y - fh xh) + 2 * B := by
  have hy : f y ≤ fh y + B := by linarith [hdown y]
  have hxh : fh xh ≤ fh xstar := hminh (Set.mem_univ xstar)
  have hs : fh xstar ≤ f xstar + B := by linarith [hup xstar]
  linarith

/-- The reply term is the probe surrogate: decoding the reply gives back `dirSlot`. -/
lemma dirReply_slot {q : Params} (g : Point q.d → q.Ω → ℝ) (x : Point q.d) (s : Bool)
    (u : Point q.d × q.Ω) : dirTerm (dirReply g x s u) = dirSlot g x s u.1 u.2 := rfl

end LongTails.Setups.ZerothOrderSmoothingStronglyConvex

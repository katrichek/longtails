import LongTails.Template
import Mathlib.Analysis.Calculus.Gradient.Basic
import LongTails.Setups.ZerothOrderSmoothAndConvex
import LongTails.Setups.ZerothOrderSmoothingStronglyConvex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Probability.Independence.Basic

namespace LongTails.Setups.ZerothOrderSmoothingStrongGrowth

open OracleTemplate MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
open LongTails.Setups.ZerothOrderSmoothAndConvex
open LongTails.Setups.ZerothOrderSmoothingStronglyConvex

structure Params where
  d : ℕ
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  L : ℝ
  μ : ℝ
  ρ : ℝ
  R : ℝ
  ε : ℝ
  h : ℝ
  x0 : Point d
  nu : ProbabilityMeasure (Point d)

attribute [instance] Params.measurableΩ

/-- Read the parameters in the randomized-smoothing probe model. Only the bandwidth and the
direction measure are used by the probe primitives, so `G` is a placeholder there. -/
def asZO (q : Params) : LongTails.Setups.ZerothOrderSmoothingStronglyConvex.Params :=
  { d := q.d, Ω := q.Ω, measurableΩ := q.measurableΩ, L := q.L, μ := q.μ, G := q.ρ, R := q.R,
    ε := q.ε, h := q.h, x0 := q.x0, nu := q.nu }

/-- The law of one probe: an independent direction and value sample. -/
noncomputable def probe {q : Params} (p : Measure q.Ω) : Measure (Point q.d × q.Ω) :=
  probeLaw (q := asZO q) p

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := Point p.d → ℝ
  Query p := Point p.d × Bool
  Reply p := ℝ × Point p.d
  Output p := Point p.d
  publicInput p := p
  valid q :=
    0 < q.d ∧ 0 < q.L ∧ 0 ≤ q.R ∧ 0 < q.μ ∧ 0 < q.ε ∧ 0 < q.h ∧ 0 < q.ρ ∧
      2 * q.L * q.h ^ 2 * (q.d : ℝ) ≤ q.ε
  admissible q f O :=
    ∃ (g : Point q.d → q.Ω → ℝ) (p : ProbabilityMeasure q.Ω)
      (P : ProbabilityMeasure (ℕ → Point q.d × q.Ω)),
      ProbabilityTheory.iIndepFun (fun k (u : ℕ → Point q.d × q.Ω) => u k)
        (P : Measure (ℕ → Point q.d × q.Ω)) ∧
      (∀ k : ℕ,
        Measure.map (fun (u : ℕ → Point q.d × q.Ω) => u k)
          (P : Measure (ℕ → Point q.d × q.Ω)) = (probe p : Measure (Point q.d × q.Ω))) ∧
      O = { Seed := fun _ => Point q.d × q.Ω, law := P,
            answer := fun _ (_, r) u => dirReply (q := asZO q) g r.1 r.2 u } ∧
      Measurable (Function.uncurry g) ∧ Measurable f ∧
      (∃ xstar, IsMinOn f Set.univ xstar ∧ ‖q.x0 - xstar‖ ≤ q.R) ∧
      ∃ (fh : Point q.d → ℝ) (xh : Point q.d),
        ConvexOn ℝ Set.univ fh ∧
        (∀ x, HasGradientAt fh (gradient fh x) x) ∧
        (∀ x y, ‖gradient fh x - gradient fh y‖ ≤ q.L * ‖x - y‖) ∧
        (∀ x y, fh x + ⟪gradient fh x, y - x⟫ + q.μ / 2 * ‖y - x‖ ^ 2 ≤ fh y) ∧
        IsMinOn fh Set.univ xh ∧ ‖q.x0 - xh‖ ≤ q.R ∧
        (∀ x, fh x - f x ≤ q.L * q.h ^ 2 * (q.d : ℝ) / 2) ∧
        (∀ x, f x - fh x ≤ q.L * q.h ^ 2 * (q.d : ℝ) / 2) ∧
        (∀ x s, Integrable (fun u : Point q.d × q.Ω =>
            dirSlot (q := asZO q) g x s u.1 u.2 - dirCenter (q := asZO q) fh x s) (probe p)) ∧
        (∀ x s, (∫ u : Point q.d × q.Ω,
            dirSlot (q := asZO q) g x s u.1 u.2 ∂(probe p))
            = dirCenter (q := asZO q) fh x s) ∧
        (∀ x s, Integrable (fun u : Point q.d × q.Ω =>
            ‖dirSlot (q := asZO q) g x s u.1 u.2 - dirCenter (q := asZO q) fh x s‖ ^ 2)
            (probe p)) ∧
        (∀ x s, (∫ u : Point q.d × q.Ω,
            ‖dirSlot (q := asZO q) g x s u.1 u.2 - dirCenter (q := asZO q) fh x s‖ ^ 2
              ∂(probe p)) ≤ q.ρ ^ 2 * (fh x - fh xh))
  successful q f output P :=
    Measurable output ∧
      ∃ xstar, IsMinOn f Set.univ xstar ∧
        Integrable (fun ω => f (output ω) - f xstar) (P : Measure _) ∧
        (∫ ω, f (output ω) - f xstar ∂(P : Measure _)) ≤ q.ε

end LongTails.Setups.ZerothOrderSmoothingStrongGrowth

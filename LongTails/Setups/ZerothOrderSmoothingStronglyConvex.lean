import LongTails.Setups.ZerothOrderStronglyConvex

namespace LongTails.Setups.ZerothOrderSmoothingStronglyConvex

open OracleTemplate Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
open LongTails.Setups.ZerothOrderSmoothAndConvex

structure Params where
  E : Type
  [normedE : NormedAddCommGroup E]
  [linearE : InnerProductSpace ℝ E]
  [completeE : CompleteSpace E]
  [measurableE : MeasurableSpace E]
  [borelE : BorelSpace E]
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  d : ℕ
  L : ℝ
  μ : ℝ
  σ : ℝ
  G : ℝ
  R : ℝ
  ε : ℝ
  h : ℝ
  x0 : E
  nu : ProbabilityMeasure E

attribute [instance] Params.normedE Params.linearE Params.completeE Params.measurableE
attribute [instance] Params.borelE Params.measurableΩ

def base (p : Params) : LongTails.Setups.ZerothOrderPolyakConvex.Params :=
  { E := p.E, Ω := p.Ω, d := p.d, L := p.L, R := p.R, σ := p.σ, μ := p.μ, ε := p.ε, x0 := p.x0 }

noncomputable def dirEstimate {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (q : Params) (g : E → q.Ω → ℝ) (x z : E) (ω : q.Ω) : E :=
  (1 / (2 * q.h)) • ((g (x + q.h • z) ω - g (x - q.h • z) ω) • z)

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := p.E → ℝ
  Query p := p.E
  Reply _ := ℝ
  Output p := p.E
  publicInput p := p
  valid q := 0 < q.d ∧ 0 < q.L ∧ 0 ≤ q.R ∧ 0 ≤ q.σ ∧ 0 ≤ q.G ∧ 0 < q.μ ∧ 0 < q.ε ∧ 0 < q.h ∧
    q.L * q.h ^ 2 * (q.d : ℝ) ≤ q.ε
  admissible q f O :=
    LongTails.Setups.ZerothOrderPolyakConvex.baseShape (base q) f O ∧
      (∃ xstar, IsMinOn f univ xstar ∧ ‖q.x0 - xstar‖ ≤ q.R ∧
        LongTails.Setups.ZerothOrderStronglyConvex.tangentStrong q.μ f) ∧
      ∃ (fh : q.E → ℝ) (g : q.E → q.Ω → ℝ) (p : ProbabilityMeasure q.Ω),
        ConvexOn ℝ univ fh ∧
        (∀ x, HasGradientAt fh (gradient fh x) x) ∧
        (∀ x y, ‖gradient fh x - gradient fh y‖ ≤ q.L * ‖x - y‖) ∧
        LongTails.Setups.ZerothOrderStronglyConvex.tangentStrong q.μ fh ∧
        (∃ xh, IsMinOn fh univ xh) ∧
        (∀ x, fh x - f x ≤ q.L * q.h ^ 2 * (q.d : ℝ) / 2) ∧
        (∀ x, f x - fh x ≤ q.L * q.h ^ 2 * (q.d : ℝ) / 2) ∧
        (∀ x, (∫ z, (∫ ω, dirEstimate q g x z ω ∂(p : Measure _)) ∂(q.nu : Measure _))
          = gradient fh x) ∧
        (∀ x, (∫ z, (∫ ω, ‖dirEstimate q g x z ω - gradient fh x‖ ^ 2 ∂(p : Measure _))
          ∂(q.nu : Measure _)) ≤ q.G ^ 2)
  successful q f output P :=
    Measurable output ∧
      ∃ xstar, IsMinOn f univ xstar ∧
        Integrable (fun ω => f (output ω) - f xstar) (P : Measure _) ∧
        (∫ ω, f (output ω) - f xstar ∂(P : Measure _)) ≤ q.ε

end LongTails.Setups.ZerothOrderSmoothingStronglyConvex
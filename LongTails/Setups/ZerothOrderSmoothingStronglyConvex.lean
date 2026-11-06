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

noncomputable def dirSlot {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (q : Params) (g : E → q.Ω → ℝ) (x : E) (s : Bool) (z : E) (ω : q.Ω) : E :=
  (1 / (2 * q.h)) • ((g (x + (if s then q.h else -q.h) • z) ω) • z)

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
        (∀ x s, (∫ z, (∫ ω, dirSlot q g x s z ω ∂(p : Measure _)) ∂(q.nu : Measure _))
          = (if s then (1 / 2 : ℝ) else -(1 / 2 : ℝ)) • gradient fh x) ∧
        (∀ x s, (∫ z, (∫ ω, ‖dirSlot q g x s z ω‖ ^ 2 ∂(p : Measure _))
          ∂(q.nu : Measure _)) ≤ q.G ^ 2)
  successful q f output P :=
    Measurable output ∧
      ∃ xstar, IsMinOn f univ xstar ∧
        Integrable (fun ω => f (output ω) - f xstar) (P : Measure _) ∧
        (∫ ω, f (output ω) - f xstar ∂(P : Measure _)) ≤ q.ε


/-- Value conversion: a point that is good for the smoothed objective is good for the original one. -/
lemma smoothed_value_bound {q : Params} {f fh : q.E → ℝ} {xstar xh : q.E} {B : ℝ}
    (_hmin : IsMinOn f Set.univ xstar) (hminh : IsMinOn fh Set.univ xh)
    (hup : ∀ x, fh x - f x ≤ B) (hdown : ∀ x, f x - fh x ≤ B) (y : q.E) :
    f y - f xstar ≤ (fh y - fh xh) + 2 * B := by
  have hy : f y ≤ fh y + B := by linarith [hdown y]
  have hxh : fh xh ≤ fh xstar := hminh (Set.mem_univ xstar)
  have hs : fh xstar ≤ f xstar + B := by linarith [hup xstar]
  linarith
end LongTails.Setups.ZerothOrderSmoothingStronglyConvex

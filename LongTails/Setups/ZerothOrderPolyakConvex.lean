import LongTails.Setups.ZerothOrderSmoothAndConvex

namespace LongTails.Setups.ZerothOrderPolyakConvex

open OracleTemplate Set

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
  R : ℝ
  σ : ℝ
  μ : ℝ
  ε : ℝ
  x0 : E

attribute [instance] Params.normedE Params.linearE Params.completeE Params.measurableE
attribute [instance] Params.borelE Params.measurableΩ

noncomputable def base (p : Params) : LongTails.Setups.ZerothOrderSmoothAndConvex.Params :=
  { E := p.E, Ω := p.Ω, d := p.d, L := p.L, R := p.R, σ := p.σ, ε := p.ε, x0 := p.x0 }

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := p.E → ℝ
  Query p := p.E
  Reply _ := ℝ
  Output p := p.E
  publicInput p := p
  valid q := 0 < q.d ∧ 0 < q.L ∧ 0 ≤ q.R ∧ 0 ≤ q.σ ∧ 0 < q.μ ∧ 0 < q.ε
  admissible q f O :=
    LongTails.Setups.ZerothOrderSmoothAndConvex.spec.admissible (base q) f O ∧
    ∃ xstar, IsMinOn f univ xstar ∧ ‖q.x0 - xstar‖ ≤ q.R ∧
      ∀ x, 2 * q.μ * (f x - f xstar) ≤ ‖gradient f x‖ ^ 2
  successful q f output P :=
    LongTails.Setups.ZerothOrderSmoothAndConvex.spec.successful (base q) f output P

lemma valid_base {q : Params} (hq : spec.valid q) :
    LongTails.Setups.ZerothOrderSmoothAndConvex.spec.valid (base q) := by
  obtain ⟨hd, hL, hR, hσ, hμ, hε⟩ := hq
  exact ⟨hd, hL, hR, hσ, hε⟩

lemma admissible_base {q : Params} {f : q.E → ℝ} {O : Oracle q.E ℝ}
    (hq : spec.admissible q f O) :
    LongTails.Setups.ZerothOrderSmoothAndConvex.spec.admissible (base q) f O := hq.1

lemma admissible_polyak {q : Params} {f : q.E → ℝ} {O : Oracle q.E ℝ}
    (hq : spec.admissible q f O) :
    ∃ xstar, IsMinOn f univ xstar ∧ ‖q.x0 - xstar‖ ≤ q.R ∧
      ∀ x, 2 * q.μ * (f x - f xstar) ≤ ‖gradient f x‖ ^ 2 := hq.2

end LongTails.Setups.ZerothOrderPolyakConvex

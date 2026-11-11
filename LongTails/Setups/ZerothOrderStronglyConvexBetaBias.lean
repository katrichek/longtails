import LongTails.Setups.ZerothOrderStronglyConvex

/-!
RESEARCH EXTENSION, NOT THE ORIGINAL SETUP.
Uniform parameterization of the central Richardson stencil ladder by the number of radii bands.
For `m` bands the probe radii are `h, 2 * h, ..., m * h` and the decoder is the Lagrange
(Richardson) combination of the `m` symmetric differences with weights `betaWeight m j`, the
Lagrange basis polynomials at `0` for the nodes `1 ^ 2, ..., (m : ℝ) ^ 2`. The extra regularity
assumed here is that this combination approximates the directional derivative with error
`rho * h ^ (2 * m)`; a bounded `(2 * m + 1)`-st derivative along every line is sufficient. It does
NOT follow from ordinary `L`-smoothness, nor from any weaker member of the ladder. The scalar
noisy value oracle, the strong convexity and the accuracy criterion are inherited unchanged from
`LongTails.Setups.ZerothOrderStronglyConvex`.

The ladder instances already proved in this repository are the cases `m = 1` (central stencil,
`CubicCentralMomentumStronglyConvex`), `m = 2` (`QuinticStencilStronglyConvex`), `m = 3`
(`SexticStencilStronglyConvex`), `m = 4` (`OcticStencilStronglyConvex`) and `m = 5`
(`DecicStencilStronglyConvex`); the weight checks below identify `betaWeight` with their numeric
weights, and the general convergence proof `LongTails.Theorems.BetaStencilStronglyConvex` covers
every `m` at once with budget exponent `(2 * m + 1) / (2 * m)`, which is `beta / (beta - 1)` for
the smoothness order `beta = 2 * m + 1` of `arXiv 2610 00276`. That paper indexes its class by a
real order `beta > 2`, so even and non-integer orders exist there. Because this decoder is built
from symmetric differences, whose error expansion contains only even powers of `h`, the ladder
realizes the odd integer orders `beta = 3, 5, 7, ...`: an even order `beta = 2 * m` would need a
bias of odd order `h ^ (2 * m - 1)`, hence asymmetric one-sided bands, which this setup does not
model.
-/
namespace LongTails.Setups.ZerothOrderStronglyConvexBetaBias

open OracleTemplate
open scoped BigOperators RealInnerProductSpace

private abbrev Base := LongTails.Setups.ZerothOrderStronglyConvex.spec

/-- Richardson weight of the band of radius `(j + 1) * h` among `m` bands: the Lagrange basis
polynomial at `0` for the nodes `1 ^ 2, ..., (m : ℝ) ^ 2`. -/
noncomputable def betaWeight (m : ℕ) (j : Fin m) : ℝ :=
  ∏ l ∈ Finset.univ.erase j, ((l : ℝ) + 1) ^ 2 / (((l : ℝ) + 1) ^ 2 - ((j : ℝ) + 1) ^ 2)

/-- Total mass of the absolute Richardson weights of `m` bands; it is the noise inflation factor
of the `m`-band stencil. -/
noncomputable def betaAbs (m : ℕ) : ℝ := ∑ j : Fin m, |betaWeight m j|

lemma betaAbs_nonneg (m : ℕ) : 0 ≤ betaAbs m :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- One radius is `0` at the left edge, so `h` stays a free bandwidth parameter. -/
lemma betaRadius_pos (m : ℕ) (j : Fin m) : (0 : ℝ) < (j : ℝ) + 1 := by
  have h1 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
  linarith

structure Params where
  base : LongTails.Setups.ZerothOrderStronglyConvex.Params
  bands : ℕ
  rho : ℝ

/-- `m`-band central Richardson stencil: the Lagrange combination of the symmetric differences at
the radii `h, 2 * h, ..., m * h`, each normalized by its own radius. -/
def centralBetaBias (q : Params) (f : q.base.E → ℝ) : Prop :=
  ∀ (x v : q.base.E) (h : ℝ), 0 < h → ‖v‖ = 1 →
    |∑ j : Fin q.bands, betaWeight q.bands j *
        ((f (x + (((j : ℝ) + 1) * h) • v) - f (x - (((j : ℝ) + 1) * h) • v))
          / (2 * ((j : ℝ) + 1) * h)) - ⟪gradient f x, v⟫| ≤ q.rho * h ^ (2 * q.bands)

abbrev spec : OracleTemplate.Setup where
  Params := Params
  Public := Params
  Instance q := Base.Instance q.base
  Query q := Base.Query q.base
  Reply q := Base.Reply q.base
  Output q := Base.Output q.base
  publicInput q := q
  valid q := Base.valid q.base ∧ 0 < q.bands ∧ 0 ≤ q.rho
  admissible q f oracle := Base.admissible q.base f oracle ∧ centralBetaBias q f
  successful q f output P := Base.successful q.base f output P

/-- One band reproduces the symmetric central stencil weight `1` of `CubicCentralMomentumZO`. -/
lemma betaWeight_one : betaWeight 1 ⟨0, by omega⟩ = 1 := by
  classical
  have hset : (Finset.univ : Finset (Fin 1)).erase ⟨0, by omega⟩ =
      (∅ : Finset (Fin 1)) := by decide
  rw [betaWeight, hset]
  norm_num

/-- Four bands reproduce the eight-point stencil weights `8 / 5`, `-4 / 5`, `8 / 35` and `-1 / 35`
of `OcticStencilMomentumZO`. -/
lemma betaWeight_four : betaWeight 4 ⟨0, by omega⟩ = 8 / 5 ∧ betaWeight 4 ⟨1, by omega⟩ = -4 / 5 ∧
    betaWeight 4 ⟨2, by omega⟩ = 8 / 35 ∧ betaWeight 4 ⟨3, by omega⟩ = -1 / 35 := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hset : (Finset.univ : Finset (Fin 4)).erase ⟨0, by omega⟩ =
      ({1, 2, 3} : Finset (Fin 4)) := by decide
    rw [betaWeight, hset]
    norm_num
  · have hset : (Finset.univ : Finset (Fin 4)).erase ⟨1, by omega⟩ =
      ({0, 2, 3} : Finset (Fin 4)) := by decide
    rw [betaWeight, hset]
    norm_num
  · have hset : (Finset.univ : Finset (Fin 4)).erase ⟨2, by omega⟩ =
      ({0, 1, 3} : Finset (Fin 4)) := by decide
    rw [betaWeight, hset]
    norm_num
  · have hset : (Finset.univ : Finset (Fin 4)).erase ⟨3, by omega⟩ =
      ({0, 1, 2} : Finset (Fin 4)) := by decide
    rw [betaWeight, hset]
    norm_num

/-- Two bands reproduce the four-point stencil weights `4 / 3` and `-1 / 3` of
`QuinticStencilMomentumZO`. -/
lemma betaWeight_two : betaWeight 2 ⟨0, by omega⟩ = 4 / 3 ∧ betaWeight 2 ⟨1, by omega⟩ = -1 / 3 := by
  classical
  constructor
  · have hset : (Finset.univ : Finset (Fin 2)).erase ⟨0, by omega⟩ = ({1} : Finset (Fin 2)) :=
      by decide
    rw [betaWeight, hset]
    norm_num
  · have hset : (Finset.univ : Finset (Fin 2)).erase ⟨1, by omega⟩ = ({0} : Finset (Fin 2)) :=
      by decide
    rw [betaWeight, hset]
    norm_num

/-- Three bands reproduce the six-point stencil weights `3 / 2`, `-3 / 5`, `1 / 10` of
`SexticStencilMomentumZO`. -/
lemma betaWeight_three : betaWeight 3 ⟨0, by omega⟩ = 3 / 2 ∧
    betaWeight 3 ⟨1, by omega⟩ = -3 / 5 ∧ betaWeight 3 ⟨2, by omega⟩ = 1 / 10 := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · have hset : (Finset.univ : Finset (Fin 3)).erase ⟨0, by omega⟩ = ({1, 2} : Finset (Fin 3)) :=
      by decide
    rw [betaWeight, hset]
    norm_num
  · have hset : (Finset.univ : Finset (Fin 3)).erase ⟨1, by omega⟩ = ({0, 2} : Finset (Fin 3)) :=
      by decide
    rw [betaWeight, hset]
    norm_num
  · have hset : (Finset.univ : Finset (Fin 3)).erase ⟨2, by omega⟩ = ({0, 1} : Finset (Fin 3)) :=
      by decide
    rw [betaWeight, hset]
    norm_num

/-- Five bands reproduce the ten-point stencil weights `5 / 3`, `-20 / 21`, `5 / 14`, `-5 / 63`,
`1 / 126` of `DecicStencilMomentumZO`. -/
lemma betaWeight_five : betaWeight 5 ⟨0, by omega⟩ = 5 / 3 ∧ betaWeight 5 ⟨1, by omega⟩ = -20 / 21 ∧
    betaWeight 5 ⟨2, by omega⟩ = 5 / 14 ∧ betaWeight 5 ⟨3, by omega⟩ = -5 / 63 ∧
    betaWeight 5 ⟨4, by omega⟩ = 1 / 126 := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hset : (Finset.univ : Finset (Fin 5)).erase ⟨0, by omega⟩ =
      ({1, 2, 3, 4} : Finset (Fin 5)) := by decide
    rw [betaWeight, hset]
    norm_num
  · have hset : (Finset.univ : Finset (Fin 5)).erase ⟨1, by omega⟩ =
      ({0, 2, 3, 4} : Finset (Fin 5)) := by decide
    rw [betaWeight, hset]
    norm_num
  · have hset : (Finset.univ : Finset (Fin 5)).erase ⟨2, by omega⟩ =
      ({0, 1, 3, 4} : Finset (Fin 5)) := by decide
    rw [betaWeight, hset]
    norm_num
  · have hset : (Finset.univ : Finset (Fin 5)).erase ⟨3, by omega⟩ =
      ({0, 1, 2, 4} : Finset (Fin 5)) := by decide
    rw [betaWeight, hset]
    norm_num
  · have hset : (Finset.univ : Finset (Fin 5)).erase ⟨4, by omega⟩ =
      ({0, 1, 2, 3} : Finset (Fin 5)) := by decide
    rw [betaWeight, hset]
    norm_num

end LongTails.Setups.ZerothOrderStronglyConvexBetaBias

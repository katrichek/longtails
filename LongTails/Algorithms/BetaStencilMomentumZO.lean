import LongTails.Algorithms.CubicCentralMomentumZO
import LongTails.Setups.ZerothOrderStronglyConvexBetaBias

/-!
Unified `M`-band central Richardson coordinate stencil, which specializes to the five stencil
algorithms of this repository. One round reserves `M * n` central replicas per coordinate: replicas
in `[j * n, (j + 1) * n)` probe the radius `(j + 1) * h`, so the probe set is
`x ± (j + 1) * h * e i`. The decoder is the Lagrange (Richardson) combination

  ∑ j : Fin M, betaWeight M j • centralDecode ((j + 1) * h)

of the symmetric differences, each normalized by its own radius. For `M = 1` this is the symmetric
difference of `CubicCentralMomentumZO`; for `M = 2` the weights `4 / 3`, `-1 / 3` give the four-point
stencil of `QuinticStencilMomentumZO`; for `M = 3` the weights `3 / 2`, `-3 / 5`, `1 / 10` give the
six-point stencil of `SexticStencilMomentumZO`; for `M = 4` the weights `8 / 5`, `-4 / 5`, `8 / 35`,
`-1 / 35` give the eight-point stencil of `OcticStencilMomentumZO`; and for `M = 5` the weights
`5 / 3`, `-20 / 21`, `5 / 14`, `-5 / 63`, `1 / 126` give the ten-point stencil of
`DecicStencilMomentumZO`. Every round consumes `2 * M * d * n` raw function values, and the
directional bias is `O (h ^ (2 * M))` under the extra regularity of the calling setup.
-/
namespace OracleTemplate.Research.BetaStencilMomentumZO

open OracleTemplate.SecantDescent
open OracleTemplate.SecantPolyak.Centered
open OracleTemplate.ZerothOrder
open LongTails.Setups.ZerothOrderSmoothAndConvex
open LongTails.Setups.ZerothOrderStronglyConvexBetaBias
open OracleTemplate.Research.CubicCentralMomentumZO
open scoped BigOperators

/-- Bandwidth of a replica of the `M`-band stencil: replica `r` probes the radius
`(r / n + 1) * h`, so consecutive blocks of `n` replicas use `h`, `2 * h`, ..., `M * h`. -/
noncomputable def betaBandwidth {M n : ℕ} (h : ℝ) (r : Fin (M * n)) : ℝ :=
  (((r.val / n : ℕ) : ℝ)) * h + h

/-- Embedding of the `j`-th band of replicas into the replica range. -/
noncomputable def bandFin {M n : ℕ} (j : Fin M) : Fin n → Fin (M * n) :=
  fun r => ⟨j.val * n + r.val, by
    have h1 : j.val + 1 ≤ M := j.isLt
    have h3 : (j.val + 1) * n ≤ M * n := Nat.mul_le_mul_right n h1
    have h4 : j.val * n + n ≤ M * n := by rw [Nat.succ_mul] at h3; exact h3
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left r.isLt (j.val * n)) h4⟩

lemma bandFin_val {M n : ℕ} (j : Fin M) (r : Fin n) :
    (bandFin j r).val = j.val * n + r.val := rfl

/-- The replicas of the `j`-th band probe the radius `(j + 1) * h`. -/
lemma betaBandwidth_band {M n : ℕ} (hb : ℝ) (j : Fin M) (r : Fin n) :
    betaBandwidth hb (bandFin j r) = ((j : ℝ) + 1) * hb := by
  have h1 : (j.val * n + r.val) / n = j.val := by
    refine Nat.div_eq_of_lt_le ?_ ?_
    · have h2 : r.val < n := r.isLt
      nlinarith
    · have h3 : r.val < n := r.isLt
      have h4 : j.val * n + r.val < j.val * n + n := Nat.add_lt_add_left h3 (j.val * n)
      have h5 : (j.val + 1) * n = j.val * n + n := by ring
      rwa [h5]
  simp only [betaBandwidth, bandFin_val, h1]
  ring

/-- Replica embedding of the `j`-th band. -/
noncomputable def betaRep {M n : ℕ} (j : Fin M) (t : secantSpace d n) : secantSpace d (M * n) :=
  (bandFin j t.1, t.2)

/-- Probe of a band slot: the sign chooses the side, the replica band chooses the bandwidth. -/
noncomputable def betaPoint {M n : ℕ} (h : ℝ) (x : Point d) (t : secantSpace d (M * n)) : Point d :=
  centralPoint (betaBandwidth h t.1) x t

lemma betaPoint_true {M n : ℕ} (h : ℝ) (x : Point d) (r : Fin (M * n)) (i : Fin d) :
    betaPoint h x (r, (i, true)) = x + betaBandwidth h r • direction i := by
  simp [betaPoint, centralPoint, secantSign, secantCoord]

lemma betaPoint_false {M n : ℕ} (h : ℝ) (x : Point d) (r : Fin (M * n)) (i : Fin d) :
    betaPoint h x (r, (i, false)) = x - betaBandwidth h r • direction i := by
  simp [betaPoint, centralPoint, secantSign, secantCoord]

/-- Richardson combination of the `M` central decodes, one band per probe radius. -/
noncomputable def betaDecode {M n : ℕ} (h : ℝ) (replies : secantSpace d (M * n) → ℝ) : Point d :=
  ∑ j : Fin M, betaWeight M j •
    centralDecode (((j : ℝ) + 1) * h) (fun t : secantSpace d n => replies (betaRep j t))

noncomputable def queries {d : ℕ} (M : ℕ) {m : ℕ → ℕ} (theta h : ℝ) :
    ∀ k : ℕ, (ℕ × Point d × Point d) →
      Fin (Fintype.card (secantSpace d (M * m k))) → Point d :=
  fun _ s t => betaPoint h
    (OracleTemplate.InexactGradient.query theta ⟨s.2.1, s.2.2⟩)
    (secantSlot t)

noncomputable def decoder {d : ℕ} (M : ℕ) {m : ℕ → ℕ} (h : ℝ) :
    ∀ k : ℕ, (ℕ × Point d × Point d) →
      (Fin (Fintype.card (secantSpace d (M * m k))) → ℝ) → Point d :=
  fun k _ replies => betaDecode h
    (fun t : secantSpace d (M * m k) => replies (Fintype.equivFin _ t))

/-- Every iteration consumes `2 * M * d * m k` raw function values. -/
noncomputable def algorithm {d : ℕ} (hd : 0 < d) {m : ℕ → ℕ}
    (hm : ∀ k, 0 < m k) {M : ℕ} (hM : 0 < M) (L mu theta h : ℝ) (x0 : Point d) :
    OracleTemplate.Algorithm (Point d) ℝ (Point d) :=
  OracleTemplate.batchedSched
    (fun k => Fintype.card (secantSpace d (M * m k)))
    (fun k => secant_card_pos hd (Nat.mul_pos hM (hm k)))
    (cmBase L mu theta x0) (queries M theta h) (decoder M h) 0

end OracleTemplate.Research.BetaStencilMomentumZO

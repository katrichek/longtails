import LongTails.Algorithms.CubicCentralMomentumZO

/-!
Four-point coordinate stencil driven by the same scalar noisy value oracle as the original
zeroth-order setups. One round reserves `2 * n` central replicas: replicas below `n` probe
`x ± h * e i`, the remaining replicas probe `x ± 2 * h * e i`. The decoder takes the Richardson
combination `(4 • central h - central (2 * h)) / 3`, which equals

  (- f (x + 2 * h * e i) + 8 * f (x + h * e i) - 8 * f (x - h * e i) + f (x - 2 * h * e i)) / (12 * h)

coordinate by coordinate. Its directional bias is `O (h ^ 4)`, which requires the extra four-point
stencil regularity of the calling setup and does NOT follow from ordinary `L`-smoothness. Each round
consumes `4 * d * n` raw function values, twice the central stencil.
-/
namespace OracleTemplate.Research.QuinticStencilMomentumZO

open OracleTemplate.SecantDescent
open OracleTemplate.SecantPolyak.Centered
open OracleTemplate.ZerothOrder
open LongTails.Setups.ZerothOrderSmoothAndConvex
open OracleTemplate.Research.CubicCentralMomentumZO
open scoped BigOperators

/-- Bandwidth of a replica: the lower half uses `h`, the upper half uses `2 * h`. -/
noncomputable def quadBandwidth {n : ℕ} (h : ℝ) (r : Fin (2 * n)) : ℝ :=
  if r.val < n then h else 2 * h

/-- Embedding of the lower half of the replica range. -/
noncomputable def lowFin {n : ℕ} : Fin n → Fin (2 * n) := Fin.castLE (by omega)

/-- Embedding of the upper half of the replica range. -/
noncomputable def upFin {n : ℕ} : Fin n → Fin (2 * n) :=
  fun r => Fin.cast (Nat.two_mul n).symm (Fin.natAdd n r)

lemma lowFin_val {n : ℕ} (r : Fin n) : (lowFin r).val = r.val := Fin.val_castLE _ _

lemma upFin_val {n : ℕ} (r : Fin n) : (upFin r).val = r.val + n := by
  show (Fin.cast (Nat.two_mul n).symm (Fin.natAdd n r)).val = _
  simp [Fin.natAdd, add_comm]

lemma quadBandwidth_lower {n : ℕ} (hb : ℝ) (r : Fin n) : quadBandwidth hb (lowFin r) = hb := by
  simp [quadBandwidth, lowFin_val, r.isLt]

lemma quadBandwidth_upper {n : ℕ} (hb : ℝ) (r : Fin n) :
    quadBandwidth hb (upFin r) = 2 * hb := by
  simp [quadBandwidth, upFin_val]

/-- Lower-half replica embedding. -/
noncomputable def repLower {n : ℕ} (t : secantSpace d n) : secantSpace d (2 * n) :=
  (lowFin t.1, t.2)

/-- Upper-half replica embedding. -/
noncomputable def repUpper {n : ℕ} (t : secantSpace d n) : secantSpace d (2 * n) :=
  (upFin t.1, t.2)

/-- Probe of a quadrupled slot: the sign chooses the side, the replica half chooses the bandwidth. -/
noncomputable def quadPoint {n : ℕ} (h : ℝ) (x : Point d) (t : secantSpace d (2 * n)) : Point d :=
  centralPoint (quadBandwidth h t.1) x t

lemma quadPoint_true {n : ℕ} (h : ℝ) (x : Point d) (r : Fin (2 * n)) (i : Fin d) :
    quadPoint h x (r, (i, true)) = x + quadBandwidth h r • direction i := by
  simp [quadPoint, centralPoint, secantSign, secantCoord]

lemma quadPoint_false {n : ℕ} (h : ℝ) (x : Point d) (r : Fin (2 * n)) (i : Fin d) :
    quadPoint h x (r, (i, false)) = x - quadBandwidth h r • direction i := by
  simp [quadPoint, centralPoint, secantSign, secantCoord]

/-- Richardson combination of the two central decodes; equals the four-point stencil per
coordinate. -/
noncomputable def quadDecode {n : ℕ} (h : ℝ) (replies : secantSpace d (2 * n) → ℝ) : Point d :=
  ((4 : ℝ) / 3) • centralDecode h (fun t : secantSpace d n => replies (repLower t)) -
    ((1 : ℝ) / 3) • centralDecode (2 * h) (fun t : secantSpace d n => replies (repUpper t))

noncomputable def queries {d : ℕ} {m : ℕ → ℕ} (theta h : ℝ) :
    ∀ k : ℕ, (ℕ × Point d × Point d) →
      Fin (Fintype.card (secantSpace d (2 * m k))) → Point d :=
  fun _ s t => quadPoint h
    (OracleTemplate.InexactGradient.query theta ⟨s.2.1, s.2.2⟩)
    (secantSlot t)

noncomputable def decoder {d : ℕ} {m : ℕ → ℕ} (h : ℝ) :
    ∀ k : ℕ, (ℕ × Point d × Point d) →
      (Fin (Fintype.card (secantSpace d (2 * m k))) → ℝ) → Point d :=
  fun k _ replies => quadDecode h
    (fun t : secantSpace d (2 * m k) => replies (Fintype.equivFin _ t))

/-- Every iteration consumes `4 * d * m k` raw function values. -/
noncomputable def algorithm {d : ℕ} (hd : 0 < d) {m : ℕ → ℕ}
    (hm : ∀ k, 0 < m k) (L mu theta h : ℝ) (x0 : Point d) :
    OracleTemplate.Algorithm (Point d) ℝ (Point d) :=
  OracleTemplate.batchedSched
    (fun k => Fintype.card (secantSpace d (2 * m k)))
    (fun k => secant_card_pos hd (by have h1 := hm k; omega))
    (cmBase L mu theta x0) (queries theta h) (decoder h) 0

end OracleTemplate.Research.QuinticStencilMomentumZO

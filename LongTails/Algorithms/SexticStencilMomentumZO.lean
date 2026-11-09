import LongTails.Algorithms.CubicCentralMomentumZO

/-!
Six-point coordinate stencil driven by the same scalar noisy value oracle as the original
zeroth-order setups. One round reserves `3 * n` central replicas: replicas below `n` probe
`x ± h * e i`, replicas in `[n, 2 * n)` probe `x ± 2 * h * e i`, the remaining replicas probe
`x ± 3 * h * e i`. The decoder takes the Richardson combination
`3 / 2 • central h - 3 / 5 • central (2 * h) + 1 / 10 • central (3 * h)`, which equals

  (f (x + 3 * h * e i) - 9 * f (x + 2 * h * e i) + 45 * f (x + h * e i)
    - 45 * f (x - h * e i) + 9 * f (x - 2 * h * e i) - f (x - 3 * h * e i)) / (60 * h)

coordinate by coordinate. Its directional bias is `O (h ^ 6)`, which requires the extra six-point
stencil regularity of the calling setup and does NOT follow from ordinary `L`-smoothness. Each round
consumes `6 * d * n` raw function values, three times the central stencil.
-/
namespace OracleTemplate.Research.SexticStencilMomentumZO

open OracleTemplate.SecantDescent
open OracleTemplate.SecantPolyak.Centered
open OracleTemplate.ZerothOrder
open LongTails.Setups.ZerothOrderSmoothAndConvex
open OracleTemplate.Research.CubicCentralMomentumZO
open scoped BigOperators

/-- Bandwidth of a replica: the three thirds of the replica range use `h`, `2 * h`, `3 * h`. -/
noncomputable def hexBandwidth {n : ℕ} (h : ℝ) (r : Fin (3 * n)) : ℝ :=
  if r.val < n then h else if r.val < 2 * n then 2 * h else 3 * h

/-- Embedding of the first third of the replica range. -/
noncomputable def band1Fin {n : ℕ} : Fin n → Fin (3 * n) := fun r => ⟨r.val, by omega⟩

/-- Embedding of the second third of the replica range. -/
noncomputable def band2Fin {n : ℕ} : Fin n → Fin (3 * n) := fun r => ⟨r.val + n, by omega⟩

/-- Embedding of the third third of the replica range. -/
noncomputable def band3Fin {n : ℕ} : Fin n → Fin (3 * n) := fun r => ⟨r.val + 2 * n, by omega⟩

lemma band1Fin_val {n : ℕ} (r : Fin n) : (band1Fin r).val = r.val := rfl

lemma band2Fin_val {n : ℕ} (r : Fin n) : (band2Fin r).val = r.val + n := rfl

lemma band3Fin_val {n : ℕ} (r : Fin n) : (band3Fin r).val = r.val + 2 * n := rfl

lemma hexBandwidth_first {n : ℕ} (hb : ℝ) (r : Fin n) :
    hexBandwidth hb (band1Fin r) = hb := by
  show (if r.val < n then hb else if r.val < 2 * n then 2 * hb else 3 * hb) = hb
  exact ite_eq_left r.isLt

lemma hexBandwidth_second {n : ℕ} (hb : ℝ) (r : Fin n) :
    hexBandwidth hb (band2Fin r) = 2 * hb := by
  show (if r.val + n < n then hb else if r.val + n < 2 * n then 2 * hb else 3 * hb) = 2 * hb
  rw [ite_eq_right (by omega : ¬ (r.val + n < n)), ite_eq_left (by omega : r.val + n < 2 * n)]

lemma hexBandwidth_third {n : ℕ} (hb : ℝ) (r : Fin n) :
    hexBandwidth hb (band3Fin r) = 3 * hb := by
  show (if r.val + 2 * n < n then hb else if r.val + 2 * n < 2 * n then 2 * hb else 3 * hb) = 3 * hb
  rw [ite_eq_right (by omega : ¬ (r.val + 2 * n < n)), ite_eq_right (by omega : ¬ (r.val + 2 * n < 2 * n))]

/-- First-third replica embedding. -/
noncomputable def rep1 {n : ℕ} (t : secantSpace d n) : secantSpace d (3 * n) := (band1Fin t.1, t.2)

/-- Second-third replica embedding. -/
noncomputable def rep2 {n : ℕ} (t : secantSpace d n) : secantSpace d (3 * n) :=
  (band2Fin t.1, t.2)

/-- Third-third replica embedding. -/
noncomputable def rep3 {n : ℕ} (t : secantSpace d n) : secantSpace d (3 * n) :=
  (band3Fin t.1, t.2)

/-- Probe of a sextupled slot: the sign chooses the side, the replica third chooses the bandwidth. -/
noncomputable def hexPoint {n : ℕ} (h : ℝ) (x : Point d) (t : secantSpace d (3 * n)) : Point d :=
  centralPoint (hexBandwidth h t.1) x t

lemma hexPoint_true {n : ℕ} (h : ℝ) (x : Point d) (r : Fin (3 * n)) (i : Fin d) :
    hexPoint h x (r, (i, true)) = x + hexBandwidth h r • direction i := by
  simp [hexPoint, centralPoint, secantSign, secantCoord]

lemma hexPoint_false {n : ℕ} (h : ℝ) (x : Point d) (r : Fin (3 * n)) (i : Fin d) :
    hexPoint h x (r, (i, false)) = x - hexBandwidth h r • direction i := by
  simp [hexPoint, centralPoint, secantSign, secantCoord]

/-- Richardson combination of the three central decodes; equals the six-point stencil per
coordinate. -/
noncomputable def hexDecode {n : ℕ} (h : ℝ) (replies : secantSpace d (3 * n) → ℝ) : Point d :=
  ((3 : ℝ) / 2) • centralDecode h (fun t : secantSpace d n => replies (rep1 t)) -
    ((3 : ℝ) / 5) • centralDecode (2 * h) (fun t : secantSpace d n => replies (rep2 t)) +
      ((1 : ℝ) / 10) • centralDecode (3 * h) (fun t : secantSpace d n => replies (rep3 t))

noncomputable def queries {d : ℕ} {m : ℕ → ℕ} (theta h : ℝ) :
    ∀ k : ℕ, (ℕ × Point d × Point d) →
      Fin (Fintype.card (secantSpace d (3 * m k))) → Point d :=
  fun _ s t => hexPoint h
    (OracleTemplate.InexactGradient.query theta ⟨s.2.1, s.2.2⟩)
    (secantSlot t)

noncomputable def decoder {d : ℕ} {m : ℕ → ℕ} (h : ℝ) :
    ∀ k : ℕ, (ℕ × Point d × Point d) →
      (Fin (Fintype.card (secantSpace d (3 * m k))) → ℝ) → Point d :=
  fun k _ replies => hexDecode h
    (fun t : secantSpace d (3 * m k) => replies (Fintype.equivFin _ t))

/-- Every iteration consumes `6 * d * m k` raw function values. -/
noncomputable def algorithm {d : ℕ} (hd : 0 < d) {m : ℕ → ℕ}
    (hm : ∀ k, 0 < m k) (L mu theta h : ℝ) (x0 : Point d) :
    OracleTemplate.Algorithm (Point d) ℝ (Point d) :=
  OracleTemplate.batchedSched
    (fun k => Fintype.card (secantSpace d (3 * m k)))
    (fun k => secant_card_pos hd (by have h1 := hm k; omega))
    (cmBase L mu theta x0) (queries theta h) (decoder h) 0

end OracleTemplate.Research.SexticStencilMomentumZO

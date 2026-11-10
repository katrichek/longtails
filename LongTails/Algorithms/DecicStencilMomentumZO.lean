import LongTails.Algorithms.CubicCentralMomentumZO

/-!
Ten-point coordinate stencil driven by the same scalar noisy value oracle as the original
zeroth-order setups. One round reserves `5 * n` central replicas: replicas below `n` probe
`x ± h * e i`, replicas in `[n, 2 * n)` probe `x ± 2 * h * e i`, those in `[2 * n, 3 * n)` probe
`x ± 3 * h * e i`, those in `[3 * n, 4 * n)` probe `x ± 4 * h * e i`, and the remaining replicas
probe `x ± 5 * h * e i`. The decoder takes the Richardson combination
`5 / 3 • central h - 20 / 21 • central (2 * h) + 5 / 14 • central (3 * h)
   - 5 / 63 • central (4 * h) + 1 / 126 • central (5 * h)`,
which equals

  (2100 * (f (x + h * e i) - f (x - h * e i)) - 600 * (f (x + 2 * h * e i) - f (x - 2 * h * e i))
    + 150 * (f (x + 3 * h * e i) - f (x - 3 * h * e i))
    - 25 * (f (x + 4 * h * e i) - f (x - 4 * h * e i))
    + 2 * (f (x + 5 * h * e i) - f (x - 5 * h * e i))) / (2520 * h)

coordinate by coordinate. Its directional bias is `O (h ^ 10)`, which requires the extra ten-point
stencil regularity of the calling setup and does NOT follow from ordinary `L`-smoothness. This is
the cancellation depth that `arXiv 2610 00276` uses at smoothness order `beta = 11`, where their
upper construction spends `2 * (1 + floor ((k - 1) / 2)) = 10` raw values per stochastic-gradient
iteration. Each round consumes `10 * d * n` raw function values, five times the central stencil.
-/
namespace OracleTemplate.Research.DecicStencilMomentumZO

open OracleTemplate.SecantDescent
open OracleTemplate.SecantPolyak.Centered
open OracleTemplate.ZerothOrder
open LongTails.Setups.ZerothOrderSmoothAndConvex
open OracleTemplate.Research.CubicCentralMomentumZO
open scoped BigOperators

/-- Bandwidth of a replica: the five fifths of the replica range use `h`, `2 * h`, `3 * h`,
`4 * h` and `5 * h`. -/
noncomputable def decBandwidth {n : ℕ} (h : ℝ) (r : Fin (5 * n)) : ℝ :=
  if r.val < n then h else if r.val < 2 * n then 2 * h else if r.val < 3 * n then 3 * h
    else if r.val < 4 * n then 4 * h else 5 * h

/-- Embedding of the first fifth of the replica range. -/
noncomputable def band1Fin {n : ℕ} : Fin n → Fin (5 * n) := fun r => ⟨r.val, by omega⟩

/-- Embedding of the second fifth of the replica range. -/
noncomputable def band2Fin {n : ℕ} : Fin n → Fin (5 * n) := fun r => ⟨r.val + n, by omega⟩

/-- Embedding of the third fifth of the replica range. -/
noncomputable def band3Fin {n : ℕ} : Fin n → Fin (5 * n) := fun r => ⟨r.val + 2 * n, by omega⟩

/-- Embedding of the fourth fifth of the replica range. -/
noncomputable def band4Fin {n : ℕ} : Fin n → Fin (5 * n) := fun r => ⟨r.val + 3 * n, by omega⟩

/-- Embedding of the fifth fifth of the replica range. -/
noncomputable def band5Fin {n : ℕ} : Fin n → Fin (5 * n) := fun r => ⟨r.val + 4 * n, by omega⟩

lemma band1Fin_val {n : ℕ} (r : Fin n) : (band1Fin r).val = r.val := rfl

lemma band2Fin_val {n : ℕ} (r : Fin n) : (band2Fin r).val = r.val + n := rfl

lemma band3Fin_val {n : ℕ} (r : Fin n) : (band3Fin r).val = r.val + 2 * n := rfl

lemma band4Fin_val {n : ℕ} (r : Fin n) : (band4Fin r).val = r.val + 3 * n := rfl

lemma band5Fin_val {n : ℕ} (r : Fin n) : (band5Fin r).val = r.val + 4 * n := rfl

lemma decBandwidth_first {n : ℕ} (hb : ℝ) (r : Fin n) :
    decBandwidth hb (band1Fin r) = hb := by
  show (if r.val < n then hb else if r.val < 2 * n then 2 * hb else if r.val < 3 * n then 3 * hb
      else if r.val < 4 * n then 4 * hb else 5 * hb) = hb
  exact ite_eq_left r.isLt

lemma decBandwidth_second {n : ℕ} (hb : ℝ) (r : Fin n) :
    decBandwidth hb (band2Fin r) = 2 * hb := by
  show (if r.val + n < n then hb else if r.val + n < 2 * n then 2 * hb
      else if r.val + n < 3 * n then 3 * hb else if r.val + n < 4 * n then 4 * hb
      else 5 * hb) = 2 * hb
  rw [ite_eq_right (by omega : ¬ (r.val + n < n)), ite_eq_left (by omega : r.val + n < 2 * n)]

lemma decBandwidth_third {n : ℕ} (hb : ℝ) (r : Fin n) :
    decBandwidth hb (band3Fin r) = 3 * hb := by
  show (if r.val + 2 * n < n then hb else if r.val + 2 * n < 2 * n then 2 * hb
      else if r.val + 2 * n < 3 * n then 3 * hb else if r.val + 2 * n < 4 * n then 4 * hb
      else 5 * hb) = 3 * hb
  rw [ite_eq_right (by omega : ¬ (r.val + 2 * n < n)),
    ite_eq_right (by omega : ¬ (r.val + 2 * n < 2 * n)),
    ite_eq_left (by omega : r.val + 2 * n < 3 * n)]

lemma decBandwidth_fourth {n : ℕ} (hb : ℝ) (r : Fin n) :
    decBandwidth hb (band4Fin r) = 4 * hb := by
  show (if r.val + 3 * n < n then hb else if r.val + 3 * n < 2 * n then 2 * hb
      else if r.val + 3 * n < 3 * n then 3 * hb else if r.val + 3 * n < 4 * n then 4 * hb
      else 5 * hb) = 4 * hb
  rw [ite_eq_right (by omega : ¬ (r.val + 3 * n < n)),
    ite_eq_right (by omega : ¬ (r.val + 3 * n < 2 * n)),
    ite_eq_right (by omega : ¬ (r.val + 3 * n < 3 * n)),
    ite_eq_left (by omega : r.val + 3 * n < 4 * n)]

lemma decBandwidth_fifth {n : ℕ} (hb : ℝ) (r : Fin n) :
    decBandwidth hb (band5Fin r) = 5 * hb := by
  show (if r.val + 4 * n < n then hb else if r.val + 4 * n < 2 * n then 2 * hb
      else if r.val + 4 * n < 3 * n then 3 * hb else if r.val + 4 * n < 4 * n then 4 * hb
      else 5 * hb) = 5 * hb
  rw [ite_eq_right (by omega : ¬ (r.val + 4 * n < n)),
    ite_eq_right (by omega : ¬ (r.val + 4 * n < 2 * n)),
    ite_eq_right (by omega : ¬ (r.val + 4 * n < 3 * n)),
    ite_eq_right (by omega : ¬ (r.val + 4 * n < 4 * n))]

/-- First-fifth replica embedding. -/
noncomputable def rep1 {n : ℕ} (t : secantSpace d n) : secantSpace d (5 * n) := (band1Fin t.1, t.2)

/-- Second-fifth replica embedding. -/
noncomputable def rep2 {n : ℕ} (t : secantSpace d n) : secantSpace d (5 * n) :=
  (band2Fin t.1, t.2)

/-- Third-fifth replica embedding. -/
noncomputable def rep3 {n : ℕ} (t : secantSpace d n) : secantSpace d (5 * n) :=
  (band3Fin t.1, t.2)

/-- Fourth-fifth replica embedding. -/
noncomputable def rep4 {n : ℕ} (t : secantSpace d n) : secantSpace d (5 * n) :=
  (band4Fin t.1, t.2)

/-- Fifth-fifth replica embedding. -/
noncomputable def rep5 {n : ℕ} (t : secantSpace d n) : secantSpace d (5 * n) :=
  (band5Fin t.1, t.2)

/-- Probe of a quintupled slot: the sign chooses the side, the replica band chooses the bandwidth. -/
noncomputable def decPoint {n : ℕ} (h : ℝ) (x : Point d) (t : secantSpace d (5 * n)) : Point d :=
  centralPoint (decBandwidth h t.1) x t

lemma decPoint_true {n : ℕ} (h : ℝ) (x : Point d) (r : Fin (5 * n)) (i : Fin d) :
    decPoint h x (r, (i, true)) = x + decBandwidth h r • direction i := by
  simp [decPoint, centralPoint, secantSign, secantCoord]

lemma decPoint_false {n : ℕ} (h : ℝ) (x : Point d) (r : Fin (5 * n)) (i : Fin d) :
    decPoint h x (r, (i, false)) = x - decBandwidth h r • direction i := by
  simp [decPoint, centralPoint, secantSign, secantCoord]

/-- Richardson combination of the five central decodes; equals the ten-point stencil per
coordinate. -/
noncomputable def decDecode {n : ℕ} (h : ℝ) (replies : secantSpace d (5 * n) → ℝ) : Point d :=
  ((5 : ℝ) / 3) • centralDecode h (fun t : secantSpace d n => replies (rep1 t)) -
    ((20 : ℝ) / 21) • centralDecode (2 * h) (fun t : secantSpace d n => replies (rep2 t)) +
      ((5 : ℝ) / 14) • centralDecode (3 * h) (fun t : secantSpace d n => replies (rep3 t)) -
        ((5 : ℝ) / 63) • centralDecode (4 * h) (fun t : secantSpace d n => replies (rep4 t)) +
          ((1 : ℝ) / 126) • centralDecode (5 * h) (fun t : secantSpace d n => replies (rep5 t))

noncomputable def queries {d : ℕ} {m : ℕ → ℕ} (theta h : ℝ) :
    ∀ k : ℕ, (ℕ × Point d × Point d) →
      Fin (Fintype.card (secantSpace d (5 * m k))) → Point d :=
  fun _ s t => decPoint h
    (OracleTemplate.InexactGradient.query theta ⟨s.2.1, s.2.2⟩)
    (secantSlot t)

noncomputable def decoder {d : ℕ} {m : ℕ → ℕ} (h : ℝ) :
    ∀ k : ℕ, (ℕ × Point d × Point d) →
      (Fin (Fintype.card (secantSpace d (5 * m k))) → ℝ) → Point d :=
  fun k _ replies => decDecode h
    (fun t : secantSpace d (5 * m k) => replies (Fintype.equivFin _ t))

/-- Every iteration consumes `10 * d * m k` raw function values. -/
noncomputable def algorithm {d : ℕ} (hd : 0 < d) {m : ℕ → ℕ}
    (hm : ∀ k, 0 < m k) (L mu theta h : ℝ) (x0 : Point d) :
    OracleTemplate.Algorithm (Point d) ℝ (Point d) :=
  OracleTemplate.batchedSched
    (fun k => Fintype.card (secantSpace d (5 * m k)))
    (fun k => secant_card_pos hd (by have h1 := hm k; omega))
    (cmBase L mu theta x0) (queries theta h) (decoder h) 0

end OracleTemplate.Research.DecicStencilMomentumZO

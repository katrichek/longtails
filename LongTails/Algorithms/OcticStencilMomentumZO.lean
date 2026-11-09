import LongTails.Algorithms.CubicCentralMomentumZO

/-!
Eight-point coordinate stencil driven by the same scalar noisy value oracle as the original
zeroth-order setups. One round reserves `4 * n` central replicas: replicas below `n` probe
`x ± h * e i`, replicas in `[n, 2 * n)` probe `x ± 2 * h * e i`, those in `[2 * n, 3 * n)` probe
`x ± 3 * h * e i`, and the remaining replicas probe `x ± 4 * h * e i`. The decoder takes the
Richardson combination
`8 / 5 • central h - 4 / 5 • central (2 * h) + 8 / 35 • central (3 * h) - 1 / 35 • central (4 * h)`,
which equals

  (672 * (f (x + h * e i) - f (x - h * e i)) - 168 * (f (x + 2 * h * e i) - f (x - 2 * h * e i))
    + 32 * (f (x + 3 * h * e i) - f (x - 3 * h * e i))
    - 3 * (f (x + 4 * h * e i) - f (x - 4 * h * e i))) / (840 * h)

coordinate by coordinate. Its directional bias is `O (h ^ 8)`, which requires the extra eight-point
stencil regularity of the calling setup and does NOT follow from ordinary `L`-smoothness. Each round
consumes `8 * d * n` raw function values, four times the central stencil.
-/
namespace OracleTemplate.Research.OcticStencilMomentumZO

open OracleTemplate.SecantDescent
open OracleTemplate.SecantPolyak.Centered
open OracleTemplate.ZerothOrder
open LongTails.Setups.ZerothOrderSmoothAndConvex
open OracleTemplate.Research.CubicCentralMomentumZO
open scoped BigOperators

/-- Bandwidth of a replica: the four fourths of the replica range use `h`, `2 * h`, `3 * h`, `4 * h`. -/
noncomputable def octBandwidth {n : ℕ} (h : ℝ) (r : Fin (4 * n)) : ℝ :=
  if r.val < n then h else if r.val < 2 * n then 2 * h else if r.val < 3 * n then 3 * h else 4 * h

/-- Embedding of the first fourth of the replica range. -/
noncomputable def band1Fin {n : ℕ} : Fin n → Fin (4 * n) := fun r => ⟨r.val, by omega⟩

/-- Embedding of the second fourth of the replica range. -/
noncomputable def band2Fin {n : ℕ} : Fin n → Fin (4 * n) := fun r => ⟨r.val + n, by omega⟩

/-- Embedding of the third fourth of the replica range. -/
noncomputable def band3Fin {n : ℕ} : Fin n → Fin (4 * n) := fun r => ⟨r.val + 2 * n, by omega⟩

/-- Embedding of the fourth fourth of the replica range. -/
noncomputable def band4Fin {n : ℕ} : Fin n → Fin (4 * n) := fun r => ⟨r.val + 3 * n, by omega⟩

lemma band1Fin_val {n : ℕ} (r : Fin n) : (band1Fin r).val = r.val := rfl

lemma band2Fin_val {n : ℕ} (r : Fin n) : (band2Fin r).val = r.val + n := rfl

lemma band3Fin_val {n : ℕ} (r : Fin n) : (band3Fin r).val = r.val + 2 * n := rfl

lemma band4Fin_val {n : ℕ} (r : Fin n) : (band4Fin r).val = r.val + 3 * n := rfl

lemma octBandwidth_first {n : ℕ} (hb : ℝ) (r : Fin n) :
    octBandwidth hb (band1Fin r) = hb := by
  show (if r.val < n then hb else if r.val < 2 * n then 2 * hb else if r.val < 3 * n then 3 * hb
      else 4 * hb) = hb
  exact ite_eq_left r.isLt

lemma octBandwidth_second {n : ℕ} (hb : ℝ) (r : Fin n) :
    octBandwidth hb (band2Fin r) = 2 * hb := by
  show (if r.val + n < n then hb else if r.val + n < 2 * n then 2 * hb
      else if r.val + n < 3 * n then 3 * hb else 4 * hb) = 2 * hb
  rw [ite_eq_right (by omega : ¬ (r.val + n < n)), ite_eq_left (by omega : r.val + n < 2 * n)]

lemma octBandwidth_third {n : ℕ} (hb : ℝ) (r : Fin n) :
    octBandwidth hb (band3Fin r) = 3 * hb := by
  show (if r.val + 2 * n < n then hb else if r.val + 2 * n < 2 * n then 2 * hb
      else if r.val + 2 * n < 3 * n then 3 * hb else 4 * hb) = 3 * hb
  rw [ite_eq_right (by omega : ¬ (r.val + 2 * n < n)),
    ite_eq_right (by omega : ¬ (r.val + 2 * n < 2 * n)),
    ite_eq_left (by omega : r.val + 2 * n < 3 * n)]

lemma octBandwidth_fourth {n : ℕ} (hb : ℝ) (r : Fin n) :
    octBandwidth hb (band4Fin r) = 4 * hb := by
  show (if r.val + 3 * n < n then hb else if r.val + 3 * n < 2 * n then 2 * hb
      else if r.val + 3 * n < 3 * n then 3 * hb else 4 * hb) = 4 * hb
  rw [ite_eq_right (by omega : ¬ (r.val + 3 * n < n)),
    ite_eq_right (by omega : ¬ (r.val + 3 * n < 2 * n)),
    ite_eq_right (by omega : ¬ (r.val + 3 * n < 3 * n))]

/-- First-fourth replica embedding. -/
noncomputable def rep1 {n : ℕ} (t : secantSpace d n) : secantSpace d (4 * n) := (band1Fin t.1, t.2)

/-- Second-fourth replica embedding. -/
noncomputable def rep2 {n : ℕ} (t : secantSpace d n) : secantSpace d (4 * n) :=
  (band2Fin t.1, t.2)

/-- Third-fourth replica embedding. -/
noncomputable def rep3 {n : ℕ} (t : secantSpace d n) : secantSpace d (4 * n) :=
  (band3Fin t.1, t.2)

/-- Fourth-fourth replica embedding. -/
noncomputable def rep4 {n : ℕ} (t : secantSpace d n) : secantSpace d (4 * n) :=
  (band4Fin t.1, t.2)

/-- Probe of a quadrupled slot: the sign chooses the side, the replica band chooses the bandwidth. -/
noncomputable def octPoint {n : ℕ} (h : ℝ) (x : Point d) (t : secantSpace d (4 * n)) : Point d :=
  centralPoint (octBandwidth h t.1) x t

lemma octPoint_true {n : ℕ} (h : ℝ) (x : Point d) (r : Fin (4 * n)) (i : Fin d) :
    octPoint h x (r, (i, true)) = x + octBandwidth h r • direction i := by
  simp [octPoint, centralPoint, secantSign, secantCoord]

lemma octPoint_false {n : ℕ} (h : ℝ) (x : Point d) (r : Fin (4 * n)) (i : Fin d) :
    octPoint h x (r, (i, false)) = x - octBandwidth h r • direction i := by
  simp [octPoint, centralPoint, secantSign, secantCoord]

/-- Richardson combination of the four central decodes; equals the eight-point stencil per
coordinate. -/
noncomputable def octDecode {n : ℕ} (h : ℝ) (replies : secantSpace d (4 * n) → ℝ) : Point d :=
  ((8 : ℝ) / 5) • centralDecode h (fun t : secantSpace d n => replies (rep1 t)) -
    ((4 : ℝ) / 5) • centralDecode (2 * h) (fun t : secantSpace d n => replies (rep2 t)) +
      ((8 : ℝ) / 35) • centralDecode (3 * h) (fun t : secantSpace d n => replies (rep3 t)) -
        ((1 : ℝ) / 35) • centralDecode (4 * h) (fun t : secantSpace d n => replies (rep4 t))

noncomputable def queries {d : ℕ} {m : ℕ → ℕ} (theta h : ℝ) :
    ∀ k : ℕ, (ℕ × Point d × Point d) →
      Fin (Fintype.card (secantSpace d (4 * m k))) → Point d :=
  fun _ s t => octPoint h
    (OracleTemplate.InexactGradient.query theta ⟨s.2.1, s.2.2⟩)
    (secantSlot t)

noncomputable def decoder {d : ℕ} {m : ℕ → ℕ} (h : ℝ) :
    ∀ k : ℕ, (ℕ × Point d × Point d) →
      (Fin (Fintype.card (secantSpace d (4 * m k))) → ℝ) → Point d :=
  fun k _ replies => octDecode h
    (fun t : secantSpace d (4 * m k) => replies (Fintype.equivFin _ t))

/-- Every iteration consumes `8 * d * m k` raw function values. -/
noncomputable def algorithm {d : ℕ} (hd : 0 < d) {m : ℕ → ℕ}
    (hm : ∀ k, 0 < m k) (L mu theta h : ℝ) (x0 : Point d) :
    OracleTemplate.Algorithm (Point d) ℝ (Point d) :=
  OracleTemplate.batchedSched
    (fun k => Fintype.card (secantSpace d (4 * m k)))
    (fun k => secant_card_pos hd (by have h1 := hm k; omega))
    (cmBase L mu theta x0) (queries theta h) (decoder h) 0

end OracleTemplate.Research.OcticStencilMomentumZO

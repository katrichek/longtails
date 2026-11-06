import LongTails.Algorithms.InexactAccelerated
import LongTails.Algorithms.SecantDescent
import LongTails.Algorithms.BatchedScheduled

namespace OracleTemplate.SecantPolyak.DirectionSampled

open MeasureTheory OracleTemplate InexactGradient
open scoped BigOperators
open LongTails.Setups.ZerothOrderSmoothAndConvex

/-- Momentum descent driven by the direction-sampled surrogate. The seed holds `K` independent
directions drawn from the model's direction measure; the state carries the momentum probe pair, the
round counter and the direction sequence. -/
noncomputable def dirBase {d : ℕ} (K : ℕ) (hK : 0 < K) (L μ θ : ℝ) (x0 : Point d)
    (nu : ProbabilityMeasure (Point d)) : Algorithm (Point d) (Point d) (Point d) where
  Seed := Fin K → Point d
  law := ⟨Measure.pi (fun _ : Fin K => (nu : Measure (Point d))), inferInstance⟩
  State := ℕ × Point d × Point d × (ℕ → Point d)
  initial seed := (0, x0, x0,
    fun i => seed ⟨min i (K - 1), Nat.lt_of_le_of_lt (Nat.min_le_right i (K - 1))
      (Nat.sub_lt hK one_pos)⟩)
  query s := (0, query θ ⟨s.2.1, s.2.2.1⟩)
  update s v := (s.1 + 1, (step L μ θ ⟨s.2.1, s.2.2.1⟩ v).1, (step L μ θ ⟨s.2.1, s.2.2.1⟩ v).2, s.2.2.2)
  output s := s.2.1

/-- Slot queries of one round: replica `t / 2` is probed at `y ± h z` along its own direction. -/
noncomputable def dirQS {d : ℕ} {m : ℕ → ℕ} (θ h : ℝ) :
    ∀ k, (ℕ × Point d × Point d × (ℕ → Point d)) → Fin (2 * m k) → Point d :=
  fun k s t =>
    query θ ⟨s.2.1, s.2.2.1⟩ + (if t.val % 2 = 0 then h else -h) • s.2.2.2 ((∑ j ∈ Finset.range k, m j) + t.val / 2)

/-- Decoding a round: the signed average of the `2 * m k` one-sided direction-sampled terms. -/
noncomputable def dirDec {d : ℕ} {m : ℕ → ℕ} (h : ℝ) :
    ∀ k, (ℕ × Point d × Point d × (ℕ → Point d)) → (Fin (2 * m k) → ℝ) → Point d :=
  fun k s replies =>
    (1 / (m k : ℝ)) •
      ∑ t : Fin (2 * m k),
        (if t.val % 2 = 0 then (1 : ℝ) else -1) •
          ((1 / (2 * h)) • (replies t • s.2.2.2 ((∑ j ∈ Finset.range k, m j) + t.val / 2)))

/-- Direction-sampled momentum descent: each round probes `2 * m k` points along the random
directions and drives the momentum step by the averaged surrogate. -/
noncomputable def dirDescent {d : ℕ} (K : ℕ) (hK : 0 < K) {m : ℕ → ℕ} (hm : ∀ k, 0 < m k)
    (L μ θ h : ℝ) (nu : ProbabilityMeasure (Point d)) (x0 : Point d) :
    Algorithm (Point d) ℝ (Point d) :=
  batchedSched (fun k => 2 * m k) (fun k => by have := hm k; omega)
    (dirBase K hK L μ θ x0 nu) (dirQS θ h) (dirDec (m := m) h) 0

end OracleTemplate.SecantPolyak.DirectionSampled
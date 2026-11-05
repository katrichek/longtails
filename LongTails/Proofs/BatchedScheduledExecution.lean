import LongTails.Algorithms.BatchedScheduled
import LongTails.Proofs.AcceleratedMarkovExecution

namespace OracleTemplate.StochasticGradient

open OracleTemplate

variable {Q V W U Ω : Type} {n : ℕ → ℕ} {hn : ∀ k, 0 < n k}
  {A : Algorithm Q V U} {queries : ∀ k, A.State → Fin (n k) → Q}
  {decode : ∀ k, A.State → (Fin (n k) → W) → V} {zero : W} {g : Q → Ω → W} {ξ : ℕ → Ω}

/-- The slot of index `i` inside a batch of width `w`. -/
noncomputable def slotFin (w : ℕ) (hw : 0 < w) (i : ℕ) : Fin w := ⟨i % w, Nat.mod_lt _ hw⟩

lemma slotFin_of_lt (w : ℕ) (hw : 0 < w) (i : ℕ) (hi : i < w) : slotFin w hw i = ⟨i, hi⟩ :=
  Fin.ext_iff.mpr (Nat.mod_eq_of_lt hi)

/-- Reply table of a partial scheduled round: slot `i` carries the reply of query `i` while
`i < j`, and is `zero` afterwards. -/
noncomputable def partialReplies (queries : ∀ k, A.State → Fin (n k) → Q) (g : Q → Ω → W)
    (zero : W) (ξ : ℕ → Ω) (hw : ∀ k, 0 < n k) (k j call : ℕ) (s : A.State) (i : ℕ) : W :=
  if i < j then g (queries k s (slotFin (n k) (hw k) i)) (ξ (call + i)) else zero

/-- One query of the scheduled batched algorithm driven by the slot stream. -/
noncomputable def schedStep (call : ℕ) (state : ℕ × ℕ × A.State × (ℕ → W)) :
    ℕ × ℕ × A.State × (ℕ → W) :=
  (batchedSched n hn A queries decode zero).update state
    (g ((batchedSched n hn A queries decode zero).query state).2 (ξ call))

/-- A query that stays inside the round appends one reply. -/
lemma schedStep_apply (call : ℕ) (k j : ℕ) (s : A.State) (rep : ℕ → W)
    (hj : j + 1 < n k) :
    (@schedStep Q V W U Ω n hn A queries decode zero g ξ) call (k, j, s, rep) =
      (k, j + 1, s, Function.update rep j (g (queries k s ⟨j, by omega⟩) (ξ call))) := by
  classical
  have hj0 : j < n k := by omega
  simp [batchedSched, schedStep, Nat.mod_eq_of_lt hj0, hj]

/-- The last query of a round decodes the round and starts the next one. -/
lemma schedStep_wrap (call : ℕ) (k j : ℕ) (s : A.State) (rep : ℕ → W) (hjk : j + 1 = n k) :
    (@schedStep Q V W U Ω n hn A queries decode zero g ξ) call (k, j, s, rep) =
      (k + 1, 0,
        A.update s (decode k s (fun t => Function.update rep j
          (g (queries k s ⟨j, by omega⟩) (ξ call)) t.val)), fun _ => zero) := by
  classical
  have hj0 : j < n k := by omega
  simp [batchedSched, schedStep, Nat.mod_eq_of_lt hj0, hjk]

@[simp]
lemma partialReplies_zero (k call : ℕ) (s : A.State) (i : ℕ) :
    partialReplies queries g zero ξ hn k 0 call s i = zero := by
  classical
  simp [partialReplies]

/-- The reply slot of the query just issued. -/
lemma partialReplies_succ_at (k j call : ℕ) (s : A.State) (hj : j < n k) :
    partialReplies queries g zero ξ hn k (j + 1) call s j =
      g (queries k s ⟨j, hj⟩) (ξ (call + j)) := by
  classical
  simp [partialReplies, slotFin_of_lt _ _ _ hj]

/-- Replies of earlier slots are unchanged by one more query. -/
lemma partialReplies_succ (k j call : ℕ) (s : A.State) (i : ℕ) (h1 : i ≠ j) :
    partialReplies queries g zero ξ hn k (j + 1) call s i
      = partialReplies queries g zero ξ hn k j call s i := by
  classical
  simp only [partialReplies]
  by_cases h : i < j
  · rw [ite_eq_left (Nat.lt_succ_of_lt h), ite_eq_left h]
  · have h2 : ¬ i < j + 1 := by omega
    rw [ite_eq_right h2, ite_eq_right (by omega : ¬ i < j)]

/-- Replies of a full round are the answers of the round's queries. -/
lemma partialReplies_full (k j call : ℕ) (s : A.State) (hjk : j + 1 = n k) (i : Fin (n k)) :
    Function.update (partialReplies queries g zero ξ hn k j call s) j
        (g (queries k s ⟨j, by omega⟩) (ξ (call + j))) i.val
      = g (queries k s i) (ξ (call + i.val)) := by
  classical
  have hjn : j < n k := by omega
  by_cases h1 : i.val = j
  · rw [Function.update_apply, ite_eq_left h1]
    subst h1
    rfl
  · rw [Function.update_of_ne h1]
    have hil : i.val < j := by
      have hv := i.isLt
      omega
    show partialReplies queries g zero ξ hn k j call s i.val = g (queries k s i) (ξ (call + i.val))
    simp only [partialReplies]
    rw [ite_eq_left hil]
    refine congrArg (fun t : Fin (n k) => g (queries k s t) (ξ (call + i.val))) ?_
    exact slotFin_of_lt _ _ _ i.isLt

/-- Running `j ≤ n k` queries of a scheduled round either fills `j` reply slots or, when the
round is complete, decodes it and starts the next round. -/
lemma advance_sched_upto (k j : ℕ) (hj : j ≤ n k) (s : A.State) (call : ℕ) :
    advance (@schedStep Q V W U Ω n hn A queries decode zero g ξ) j call (k, 0, s, fun _ => zero) =
      if j < n k
        then (k, j, s, partialReplies queries g zero ξ hn k j call s)
        else (k + 1, 0, A.update s (decode k s (fun i => g (queries k s i) (ξ (call + i.val)))),
          fun _ => zero) := by
  classical
  induction j with
  | zero =>
      rw [ite_eq_left (hn k)]
      refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))
      refine funext fun i => ?_
      show (fun _ => zero) i = partialReplies queries g zero ξ hn k 0 call s i
      simp
  | succ j ih =>
      have hj' : j ≤ n k := by omega
      have hstep : advance (@schedStep Q V W U Ω n hn A queries decode zero g ξ) (j + 1) call
            (k, 0, s, fun _ => zero)
          = @schedStep Q V W U Ω n hn A queries decode zero g ξ (call + j)
            (advance (@schedStep Q V W U Ω n hn A queries decode zero g ξ) j call
              (k, 0, s, fun _ => zero)) := by
        rw [HeavyTailedMarkovGradient.advance_add]
        rfl
      rw [hstep, ih hj']
      by_cases hlt : j < n k
      · rw [ite_eq_left hlt]
        by_cases hnext : j + 1 < n k
        · rw [schedStep_apply (call + j) j (k := k) s
            (partialReplies queries g zero ξ hn k j call s) hnext, ite_eq_left hnext]
          refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))
          refine funext fun i => ?_
          show (Function.update (partialReplies queries g zero ξ hn k j call s) j
              (g (queries k s ⟨j, by omega⟩) (ξ (call + j)))) i
              = partialReplies queries g zero ξ hn k (j + 1) call s i
          by_cases h1 : i = j
          · rw [Function.update_apply, ite_eq_left h1]
            subst h1
            exact (partialReplies_succ_at k i call s (by omega)).symm
          · rw [Function.update_of_ne h1, partialReplies_succ k j call s i h1]
        · have heq : j + 1 = n k := by omega
          rw [ite_eq_right (by omega : ¬ j + 1 < n k),
            schedStep_wrap (call + j) k j s (partialReplies queries g zero ξ hn k j call s) heq]
          refine Prod.ext rfl (Prod.ext rfl ?_)
          have hfun : (fun t => Function.update (partialReplies queries g zero ξ hn k j call s) j
                (g (queries k s ⟨j, by omega⟩) (ξ (call + j))) t.val)
              = (fun i => g (queries k s i) (ξ (call + i.val))) := by
              refine funext fun i => ?_
              exact partialReplies_full k j call s heq i
          rw [hfun]
      · exfalso
        omega

/-- Running the whole of round `k` decodes it and starts round `k + 1`. -/
lemma advance_sched_full (k : ℕ) (s : A.State) (call : ℕ) :
    advance (@schedStep Q V W U Ω n hn A queries decode zero g ξ) (n k) call
        (k, 0, s, fun _ => zero)
      = (k + 1, 0, A.update s (decode k s (fun i => g (queries k s i) (ξ (call + i.val)))),
          fun _ => zero) := by
  classical
  have h := advance_sched_upto (n := n) (hn := hn) (A := A) (queries := queries)
    (decode := decode) (zero := zero) (g := g) (ξ := ξ) k (n k) (Nat.le_refl (n k)) s call
  rwa [ite_eq_right (by omega : ¬ n k < n k)] at h

/-- The wrapped algorithm state after `k` scheduled rounds with slot offsets `off`. -/
noncomputable def roundsR (off : ℕ → ℕ) (Alg : Algorithm Q V U)
    (qs : ∀ k, Alg.State → Fin (n k) → Q) (dec : ∀ k, Alg.State → (Fin (n k) → W) → V)
    (gg : Q → Ω → W) (xx : ℕ → Ω) : ℕ → Alg.State → Alg.State
  | 0 => fun s => s
  | k + 1 =>
      fun s => Alg.update (roundsR off Alg qs dec gg xx k s)
        (dec k (roundsR off Alg qs dec gg xx k s)
          (fun i => gg (qs k (roundsR off Alg qs dec gg xx k s) i) (xx (off k + i.val))))

/-- Running the queries of `k` scheduled rounds advances the wrapped algorithm by `k` rounds. -/
lemma advance_sched_rounds {off : ℕ → ℕ} (h0 : off 0 = 0) (hs : ∀ j, off (j + 1) = off j + n j)
    (k : ℕ) (s : A.State) :
    advance (@schedStep Q V W U Ω n hn A queries decode zero g ξ) (off k) 0 (0, 0, s, fun _ => zero) = (k, 0, (roundsR off A queries decode g ξ k s), fun _ => zero) := by
  classical
  induction k with
  | zero =>
      rw [h0]
      rfl
  | succ k ih =>
      have h2 : off (k + 1) = off k + n k := hs k
      have h3 : advance (@schedStep Q V W U Ω n hn A queries decode zero g ξ) (off k + n k) 0
            (0, 0, s, fun _ => zero)
          = advance (@schedStep Q V W U Ω n hn A queries decode zero g ξ) (n k) (0 + off k)
            (advance (@schedStep Q V W U Ω n hn A queries decode zero g ξ) (off k) 0
              (0, 0, s, fun _ => zero)) :=
        HeavyTailedMarkovGradient.advance_add
          (@schedStep Q V W U Ω n hn A queries decode zero g ξ) (off k) (n k) 0 _
      have h4 : advance (@schedStep Q V W U Ω n hn A queries decode zero g ξ) (n k) (0 + off k)
            (k, 0, roundsR off A queries decode g ξ k s, fun _ => zero)
          = (k + 1, 0,
            A.update (roundsR off A queries decode g ξ k s)
              (decode k (roundsR off A queries decode g ξ k s)
                (fun i => g (queries k (roundsR off A queries decode g ξ k s) i)
                  (ξ (0 + off k + i.val)))), fun _ => zero) :=
        advance_sched_full k (roundsR off A queries decode g ξ k s) (0 + off k)
      rw [h2, h3, ih, h4]
      have h6 : (0 : ℕ) + off k = off k := by omega
      rw [h6]
      rfl

/-- Executing the scheduled batched algorithm runs the wrapped algorithm once per round. -/
lemma execute_batchedSched [MeasurableSpace Ω] {off : ℕ → ℕ} (h0 : off 0 = 0)
    (hs : ∀ j, off (j + 1) = off j + n j) (law : MeasureTheory.ProbabilityMeasure (ℕ → Ω))
    (K : ℕ) (seed : A.Seed) :
    execute { Seed := fun _ => Ω, law := law, answer := fun _ (_, x) ω => g x ω }
      (batchedSched n hn A queries decode zero) (fun _ => off K) seed ξ
      = A.output (roundsR off A queries decode g ξ K (A.initial seed)) := by
  classical
  have h1 : execute { Seed := fun _ => Ω, law := law, answer := fun _ (_, x) ω => g x ω }
      (batchedSched n hn A queries decode zero) (fun _ => off K) seed ξ
      = (batchedSched n hn A queries decode zero).output
          (advance (@schedStep Q V W U Ω n hn A queries decode zero g ξ) (off K) 0
            (0, 0, A.initial seed, fun _ => zero)) :=
    execute_advance (law := law) (g := g) (A := batchedSched n hn A queries decode zero)
      (K := off K) seed ξ
  have h2 : advance (@schedStep Q V W U Ω n hn A queries decode zero g ξ) (off K) 0
        (0, 0, A.initial seed, fun _ => zero)
      = (K, 0, roundsR off A queries decode g ξ K (A.initial seed), fun _ => zero) :=
    advance_sched_rounds h0 hs K (A.initial seed)
  refine h1.trans (congrArg (fun st : ℕ × ℕ × A.State × (ℕ → W) =>
    (batchedSched n hn A queries decode zero).output st) h2)

end OracleTemplate.StochasticGradient

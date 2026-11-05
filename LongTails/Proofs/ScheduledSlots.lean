import LongTails.Proofs.SecantPolyakStream
import LongTails.Algorithms.BatchedScheduled

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace OracleTemplate.SecantPolyak.Scheduled

open SecantDescent SecantPolyak

variable {Ω : Type} [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]

/-- The number of slots of one round with `m` replicas. -/
def roundSlots (d m : ℕ) : ℕ := Fintype.card (secantSpace d m)

/-- Offsets of the rounds inside the flat oracle stream. -/
structure Offsets (d : ℕ) (m : ℕ → ℕ) where
  off : ℕ → ℕ
  zero : off 0 = 0
  step : ∀ j, off (j + 1) = off j + roundSlots d (m j)

lemma offsets_step_le {d : ℕ} (m : ℕ → ℕ) (o : Offsets d m) (t : ℕ) :
    o.off t ≤ o.off (t + 1) := by
  rw [o.step]
  exact Nat.le_add_right _ _

lemma offsets_add_le {d : ℕ} (m : ℕ → ℕ) (o : Offsets d m) (j t : ℕ) :
    o.off j ≤ o.off (j + t) := by
  induction t with
  | zero => exact le_refl _
  | succ t ih =>
      calc o.off j ≤ o.off (j + t) := ih
        _ ≤ o.off (j + t + 1) := offsets_step_le m o (j + t)

lemma offsets_le {d : ℕ} (m : ℕ → ℕ) (o : Offsets d m) {j l : ℕ} (h : j ≤ l) : o.off j ≤ o.off l :=
  by
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le h
  subst ht
  exact offsets_add_le m o j t

/-- The cell of `m` replicas with the same coordinate, side and replica index. -/
noncomputable def cellOf {d M m : ℕ} (t : secantSpace d M) (h : t.1.val < m) : secantSpace d m :=
  ⟨⟨t.1.val, h⟩, t.2⟩

/-- Embed the cells of `m` replicas into the cells of `M` replicas. -/
noncomputable def cellInj {d m M : ℕ} (hM : m ≤ M) : secantSpace d m → secantSpace d M :=
  fun t => (Fin.castLE hM t.1, t.2)

lemma cellInj_injective {d m M : ℕ} (hM : m ≤ M) :
    Function.Injective (cellInj (d := d) hM) := by
  intro a b h
  have hv : a.1.val = b.1.val := by
    have := congrArg (fun v : secantSpace d M => (v.1 : ℕ)) h
    simpa [cellInj, Fin.val_castLE] using this
  have h2 : a.2 = b.2 := by
    have := congrArg Prod.snd h
    simpa [cellInj] using this
  exact Prod.ext (Fin.ext hv) h2

/-- Restricting ambient cell samples to the first  replicas gives the smaller product law. -/
lemma measurePreserving_cellInj {d m M : ℕ} (hM : m ≤ M) :
    MeasurePreserving (fun ω : secantSpace d M → Ω => fun t : secantSpace d m => ω (cellInj hM t))
      (slotLaw d M p) (slotLaw d m p) := by
  classical
  refine ⟨by fun_prop, ?_⟩
  have := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : secantSpace d M => p) (cellInj_injective hM)
  simpa [slotLaw, Measure.infinitePi_eq_pi] using this

/-- The stream slot read by round `k` for the ambient cell `t`. A round queries only the cells of
its own replica count; the unused ambient cells read fresh tail coordinates. -/
noncomputable def schedIndex {d M : ℕ} (m : ℕ → ℕ) (o : Offsets d m) (K : ℕ)
    (p : Fin K × secantSpace d M) : ℕ :=
  if h : p.2.1.val < m p.1.val then
    o.off p.1.val +
      ((Fintype.equivFin (secantSpace d (m p.1.val)) :
        secantSpace d (m p.1.val) ≃ Fin (roundSlots d (m p.1.val))) (cellOf p.2 h)).val
  else
    o.off K + ((Fintype.equivFin (Fin K × secantSpace d M) :
      Fin K × secantSpace d M ≃ Fin (Fintype.card (Fin K × secantSpace d M))) p).val

lemma schedIndex_used {d M : ℕ} (m : ℕ → ℕ) (o : Offsets d m) (K k : ℕ) (hk : k < K)
    (t : secantSpace d M) (h : t.1.val < m k) :
    schedIndex m o K ⟨⟨k, hk⟩, t⟩ =
      o.off k +
        ((Fintype.equivFin (secantSpace d (m k)) :
          secantSpace d (m k) ≃ Fin (roundSlots d (m k))) (cellOf t h)).val := by
  unfold schedIndex
  exact dite_eq_left h

lemma schedIndex_used_lt {d M : ℕ} (m : ℕ → ℕ) (o : Offsets d m) (K k : ℕ) (hk : k < K)
    (t : secantSpace d M) (h : t.1.val < m k) :
    schedIndex m o K ⟨⟨k, hk⟩, t⟩ < o.off (k + 1) := by
  rw [schedIndex_used m o K k hk t h, o.step]
  exact Nat.add_lt_add_left ((Fintype.equivFin (secantSpace d (m k)) (cellOf t h))).isLt _

lemma schedIndex_tail {d M : ℕ} (m : ℕ → ℕ) (o : Offsets d m) (K k : ℕ) (hk : k < K)
    (t : secantSpace d M) (h : ¬ t.1.val < m k) : o.off K ≤ schedIndex m o K ⟨⟨k, hk⟩, t⟩ := by
  have : schedIndex m o K ⟨⟨k, hk⟩, t⟩ =
      o.off K + ((Fintype.equivFin (Fin K × secantSpace d M) :
        Fin K × secantSpace d M ≃ Fin (Fintype.card (Fin K × secantSpace d M))) ⟨⟨k, hk⟩, t⟩).val :=
    by
      unfold schedIndex
      exact dite_eq_right h
  omega

lemma schedIndex_injective {d M : ℕ} (m : ℕ → ℕ) (o : Offsets d m) (K : ℕ) :
    Function.Injective (schedIndex (d := d) (M := M) m o K) := by
  classical
  intro a b hab
  rcases a with ⟨k, t⟩
  rcases b with ⟨k', t'⟩
  have hk : k.val < K := k.isLt
  have hk' : k'.val < K := k'.isLt
  by_cases h1 : t.1.val < m k.val
  · by_cases h2 : t'.1.val < m k'.val
    · -- both rounds read their own cells
      by_cases hkk : k.val = k'.val
      · have hkval : k = k' := Fin.ext hkk
        subst hkval
        have h3 := schedIndex_used m o K k.val hk t h1
        have h4 := schedIndex_used m o K k.val hk t' h2
        rw [h3, h4] at hab
        have h5 : cellOf t h1 = cellOf t' h2 :=
          (Fintype.equivFin (secantSpace d (m k.val))).injective
            (Fin.ext (Nat.add_left_cancel_iff.mp hab))
        have h7 : t.1.val = t'.1.val := by
          have := congrArg (fun (v : secantSpace d (m k.val)) => (v.1 : ℕ)) h5
          simpa [cellOf] using this
        have h8 : t = t' := by
          apply Prod.ext
          · exact Fin.ext h7
          · have := congrArg Prod.snd h5
            simpa [cellOf] using this
        exact Prod.ext (Fin.ext rfl) h8
      · have hlt : k.val < k'.val ∨ k'.val < k.val := by omega
        rcases hlt with hlt | hlt
        · have hA : schedIndex m o K ⟨k, t⟩ < o.off (k.val + 1) :=
            schedIndex_used_lt m o K k.val hk t h1
          have hD : o.off (k.val + 1) ≤ o.off k'.val := offsets_le m o (Nat.succ_le_of_lt hlt)
          have hB : o.off k'.val ≤ schedIndex m o K ⟨k', t'⟩ := by
            rw [schedIndex_used m o K k'.val hk' t' h2]
            exact Nat.le_add_right _ _
          omega
        · exfalso
          have hA : schedIndex m o K ⟨k', t'⟩ < o.off (k'.val + 1) :=
            schedIndex_used_lt m o K k'.val hk' t' h2
          have hD : o.off (k'.val + 1) ≤ o.off k.val := offsets_le m o (Nat.succ_le_of_lt hlt)
          have hB : o.off k.val ≤ schedIndex m o K ⟨k, t⟩ := by
            rw [schedIndex_used m o K k.val hk t h1]
            exact Nat.le_add_right _ _
          omega
    · exfalso
      have h3 : schedIndex m o K ⟨k, t⟩ < o.off K :=
        lt_of_lt_of_le (schedIndex_used_lt m o K k.val hk t h1)
          (offsets_le m o (Nat.succ_le_of_lt hk))
      have h4 : o.off K ≤ schedIndex m o K ⟨k', t'⟩ := schedIndex_tail m o K k'.val hk' t' h2
      omega
  · by_cases h2 : t'.1.val < m k'.val
    · exfalso
      have h3 : schedIndex m o K ⟨k', t'⟩ < o.off K :=
        lt_of_lt_of_le (schedIndex_used_lt m o K k'.val hk' t' h2)
          (offsets_le m o (Nat.succ_le_of_lt hk'))
      have h4 : o.off K ≤ schedIndex m o K ⟨k, t⟩ := schedIndex_tail m o K k.val hk t h1
      omega
    · -- both read tail coordinates
      have h3 := schedIndex_tail m o K k.val hk t h1
      have h4 := schedIndex_tail m o K k'.val hk' t' h2
      have h5 : schedIndex m o K ⟨k, t⟩ =
          o.off K + ((Fintype.equivFin (Fin K × secantSpace d M)) ⟨⟨k, hk⟩, t⟩).val := by
        unfold schedIndex
        exact dite_eq_right h1
      have h6 : schedIndex m o K ⟨k', t'⟩ =
          o.off K + ((Fintype.equivFin (Fin K × secantSpace d M)) ⟨⟨k', hk'⟩, t'⟩).val := by
        unfold schedIndex
        exact dite_eq_right h2
      rw [h5, h6] at hab
      have h7 : (⟨⟨k, hk⟩, t⟩ : Fin K × secantSpace d M) = (⟨⟨k', hk'⟩, t'⟩ : Fin K × secantSpace d M) :=
        (Fintype.equivFin (Fin K × secantSpace d M)).injective
          (Fin.ext (Nat.add_left_cancel_iff.mp hab))
      exact Prod.ext (congrArg Prod.fst h7) (congrArg Prod.snd h7)

omit [IsProbabilityMeasure p] in
/-- Cutting the round blocks out of an i.i.d. oracle stream gives the ambient round product law. -/
lemma sched_stream_law {d M : ℕ} (m : ℕ → ℕ) (o : Offsets d m) (K : ℕ)
    (P : ProbabilityMeasure (ℕ → Ω))
    (hind : iIndepFun (fun k (ξ : ℕ → Ω) => ξ k) (P : Measure _))
    (hmarg : ∀ k, (P : Measure _).map (fun ξ : ℕ → Ω => ξ k) = (p : Measure _)) :
    MeasurePreserving (fun ξ : ℕ → Ω => fun p : Fin K × secantSpace d M =>
        ξ (schedIndex (d := d) (M := M) m o K p))
      P (Measure.infinitePi fun _ : Fin K × secantSpace d M => p) := by
  classical
  refine ⟨by fun_prop, ?_⟩
  have hsub : iIndepFun (fun (v : Fin K × secantSpace d M) (ξ : ℕ → Ω) =>
      ξ (schedIndex m o K v)) (P : Measure (ℕ → Ω)) :=
    iIndepFun.precomp (f := fun (k : ℕ) (ξ : ℕ → Ω) => ξ k) (g := schedIndex m o K)
      (schedIndex_injective m o K) hind
  have h := (iIndepFun_iff_map_fun_eq_infinitePi_map
      (fun v => measurable_pi_apply (schedIndex m o K v))).mp hsub
  simpa [hmarg] using h

/-- The same law written as a product over rounds of ambient cell laws. -/
lemma sched_stream_law_curry {d M : ℕ} (m : ℕ → ℕ) (o : Offsets d m) (K : ℕ)
    (P : ProbabilityMeasure (ℕ → Ω))
    (hind : iIndepFun (fun k (ξ : ℕ → Ω) => ξ k) (P : Measure _))
    (hmarg : ∀ k, (P : Measure _).map (fun ξ : ℕ → Ω => ξ k) = (p : Measure _)) :
    MeasurePreserving (fun ξ : ℕ → Ω => fun k : Fin K => fun t : secantSpace d M =>
        ξ (schedIndex (d := d) (M := M) m o K ⟨k, t⟩))
      P (Measure.pi fun _ : Fin K => slotLaw d M p) := by
  classical
  have h1 := sched_stream_law (d := d) (M := M) m o K P hind hmarg
  have hc : MeasurePreserving (MeasurableEquiv.curry (Fin K) (secantSpace d M) Ω)
      (Measure.infinitePi fun _ : Fin K × secantSpace d M => p)
      (Measure.infinitePi fun _ : Fin K => Measure.pi fun _ : secantSpace d M => p) := by
    refine ⟨(MeasurableEquiv.curry (Fin K) (secantSpace d M) Ω).measurable, ?_⟩
    simpa only [Measure.infinitePi_eq_pi] using
      (Measure.infinitePi_map_curry (fun (_ : Fin K) (_ : secantSpace d M) => p))
  have h2 := hc.comp h1
  have h3 : Measure.infinitePi (fun _ : Fin K => Measure.pi fun _ : secantSpace d M => p)
      = Measure.pi fun _ : Fin K => slotLaw d M p := by
    simp [slotLaw, Measure.infinitePi_eq_pi]
  exact ⟨h2.measurable, h2.map_eq.trans h3⟩

end OracleTemplate.SecantPolyak.Scheduled

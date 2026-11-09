import LongTails.Proofs.DampedAnchoredConvexStep
import LongTails.Proofs.InterpolatedProbeRound
import LongTails.Proofs.DirectionMomentumStream

set_option maxHeartbeats 4000000

namespace OracleTemplate.SecantPolyak.AnchoredConvexPair

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators RealInnerProductSpace
open OracleTemplate InexactGradient SecantDescent SecantPolyak SecantPolyak.Accelerated
  SecantPolyak.Scheduled SecantPolyak.Centered SecantPolyak.DirectionSampled
open LongTails.Setups.ZerothOrderSmoothAndConvex

variable {Ω : Type} [MeasurableSpace Ω] {d : ℕ}

noncomputable def dacStepSched (η : ℝ) (g : Point d → Ω → ℝ) (h : ℝ) :
    ℕ → (Point d × Point d) → (secantSpace 1 1 → Point d × Ω) → Point d × Point d :=
  fun k s ω => dacStep k η s (roundOf h g (dacQuery k s) 1 ω)

lemma dac_round_m {g : Point d → Ω → ℝ} (hg : Measurable (Function.uncurry g)) (h : ℝ) (k : ℕ) :
    Measurable (fun q : (Point d × Point d) × (secantSpace 1 1 → Point d × Ω) =>
      roundOf h g (dacQuery k q.1) 1 q.2) := by
  classical
  have hx : Measurable (fun q : (Point d × Point d) × (secantSpace 1 1 → Point d × Ω) =>
      dacQuery k q.1) :=
    (measurable_dacQuery k).comp measurable_fst
  have h2 (t : secantSpace 1 1) :
      Measurable (fun q : (Point d × Point d) × (secantSpace 1 1 → Point d × Ω) => (q.2 t).2) :=
    measurable_snd.comp ((measurable_pi_apply t).comp measurable_snd)
  have hs (t : secantSpace 1 1) :
      Measurable (fun q : (Point d × Point d) × (secantSpace 1 1 → Point d × Ω) =>
        g (dacQuery k q.1 + (if t.2.2 then h else -h) • (q.2 t).1) (q.2 t).2) := by
    have hsa : Measurable (fun q : (Point d × Point d) × (secantSpace 1 1 → Point d × Ω) =>
        (if t.2.2 then h else (-h)) • (q.2 t).1) := by fun_prop
    exact hg.comp ((hx.add hsa).prodMk (h2 t))
  have ht (t : secantSpace 1 1) :
      Measurable (fun q : (Point d × Point d) × (secantSpace 1 1 → Point d × Ω) =>
        (if t.2.2 then (1 : ℝ) else (-1 : ℝ)) •
          ((1 / (2 * h)) •
            (g (dacQuery k q.1 + (if t.2.2 then h else -h) • (q.2 t).1) (q.2 t).2 • (q.2 t).1))) := by
    fun_prop
  have hsum : Measurable (fun q : (Point d × Point d) × (secantSpace 1 1 → Point d × Ω) =>
      ∑ t : secantSpace 1 1, (if t.2.2 then (1 : ℝ) else (-1 : ℝ)) •
        ((1 / (2 * h)) •
          (g (dacQuery k q.1 + (if t.2.2 then h else -h) • (q.2 t).1) (q.2 t).2 • (q.2 t).1))) :=
    Finset.measurable_sum Finset.univ fun t _ => ht t
  have hfun : (fun q : (Point d × Point d) × (secantSpace 1 1 → Point d × Ω) =>
        roundOf h g (dacQuery k q.1) 1 q.2)
      = fun q => ∑ t : secantSpace 1 1, (if t.2.2 then (1 : ℝ) else (-1 : ℝ)) •
          ((1 / (2 * h)) •
            (g (dacQuery k q.1 + (if t.2.2 then h else -h) • (q.2 t).1) (q.2 t).2 • (q.2 t).1)) := by
    funext q
    simp only [roundOf, slotVal, Nat.cast_one, div_one, one_smul]
  rw [hfun]
  exact hsum

lemma measurable_dacStepSched_joint {g : Point d → Ω → ℝ}
    (hg : Measurable (Function.uncurry g)) (η h : ℝ) (k : ℕ) :
    Measurable (fun q : (Point d × Point d) × (secantSpace 1 1 → Point d × Ω) =>
      dacStepSched η g h k q.1 q.2) := by
  classical
  have hR := dac_round_m hg h k
  have hq : Measurable (fun q : (Point d × Point d) × (secantSpace 1 1 → Point d × Ω) =>
      dacQuery k q.1) := (measurable_dacQuery k).comp measurable_fst
  have h1 : Measurable (fun q : (Point d × Point d) × (secantSpace 1 1 → Point d × Ω) =>
      dacQuery k q.1 - η • roundOf h g (dacQuery k q.1) 1 q.2) :=
    hq.sub ((measurable_const : Measurable (fun _ => (η : ℝ))).smul hR)
  have h2 : Measurable (fun q : (Point d × Point d) × (secantSpace 1 1 → Point d × Ω) =>
      q.1.2 - (η * ((k : ℝ) + 1) / 4) • roundOf h g (dacQuery k q.1) 1 q.2) :=
    (measurable_snd.comp measurable_fst).sub
      ((measurable_const : Measurable (fun _ => (η * ((k : ℝ) + 1) / 4 : ℝ))).smul hR)
  show Measurable (fun q : (Point d × Point d) × (secantSpace 1 1 → Point d × Ω) =>
      (dacQuery k q.1 - η • roundOf h g (dacQuery k q.1) 1 q.2,
        q.1.2 - (η * ((k : ℝ) + 1) / 4) • roundOf h g (dacQuery k q.1) 1 q.2))
  exact h1.prodMk h2

lemma dac_stream_round {g : Point d → Ω → ℝ} {fh : Point d → ℝ}
    {W : Measure (Point d × Ω)} [IsProbabilityMeasure W]
    {L η h ρ : ℝ} {xh : Point d} (k : ℕ) (s : Point d × Point d)
    (_hL : 0 < L) (hη : 0 < η) (hLη : L * η ≤ 1) (hρη : ρ ^ 2 * ((k : ℝ) + 2) * η ≤ 1)
    (hg : Measurable (Function.uncurry g))
    (hc : ConvexOn ℝ Set.univ fh)
    (hgr : ∀ x, HasGradientAt fh (gradient fh x) x)
    (hlip : ∀ x y, ‖gradient fh x - gradient fh y‖ ≤ L * ‖x - y‖)
    (hminh : IsMinOn fh Set.univ xh)
    (hint : ∀ x s, Integrable (fun u : Point d × Ω =>
        slotVal h g x s u - halfGrad fh x s) W)
    (hmean : ∀ x s, (∫ u : Point d × Ω, slotVal h g x s u ∂W) = halfGrad fh x s)
    (hvar2 : ∀ x s, Integrable (fun u : Point d × Ω =>
        ‖slotVal h g x s u - halfGrad fh x s‖ ^ 2) W)
    (hvar : ∀ x s, (∫ u : Point d × Ω, ‖slotVal h g x s u - halfGrad fh x s‖ ^ 2 ∂W)
        ≤ ρ ^ 2 * (fh x - fh xh)) :
    Integrable (fun ω => dacPotential fh η xh (k + 1) (dacStepSched η g h k s ω))
        (slotLaw 1 1 W) ∧
      (∫ ω, dacPotential fh η xh (k + 1) (dacStepSched η g h k s ω) ∂slotLaw 1 1 W)
        ≤ dacPotential fh η xh k s := by
  classical
  have hi : Integrable (fun ω : secantSpace 1 1 → Point d × Ω =>
      roundOf h g (dacQuery k s) 1 ω) (slotLaw 1 1 W) := roundOf_integrable hint (dacQuery k s)
  have hm1 : (∫ ω : secantSpace 1 1 → Point d × Ω,
        roundOf h g (dacQuery k s) 1 ω ∂(slotLaw 1 1 W))
      = gradient fh (dacQuery k s) := roundOf_mean hg hint hmean Nat.one_pos (dacQuery k s)
  obtain ⟨hdv1, hdv2⟩ :=
    Interpolated.roundOf_devAt (m := 1) (g := g) (fh := fh) (h := h) (x := dacQuery k s)
      (W := W) hg hint hmean hvar2 (fun t => hvar (dacQuery k s) t) Nat.one_pos
  have hfh : Measurable fh :=
    (continuous_iff_continuousAt.mpr fun x => (hgr x).continuousAt).measurable
  have hj : Measurable (fun ω : secantSpace 1 1 → Point d × Ω => (s, ω)) :=
    measurable_const.prodMk measurable_id
  have hmeas : AEStronglyMeasurable
      (fun ω : secantSpace 1 1 → Point d × Ω =>
        dacPotential fh η xh (k + 1) (dacStep k η s (roundOf h g (dacQuery k s) 1 ω)))
      (slotLaw 1 1 W) :=
    ((measurable_dacPotential hfh η xh (k + 1)).comp
      ((measurable_dacStepSched_joint hg η h k).comp hj)).aestronglyMeasurable
  obtain ⟨hI, hb⟩ := dac_one_round (f := fh) (L := L) (η := η) (ρ := ρ)
    (xh := xh) k s _hL hη hLη hρη hc hgr hlip hminh
    (V := fun ω : secantSpace 1 1 → Point d × Ω => roundOf h g (dacQuery k s) 1 ω) hi hdv1 hm1
    (by
      have hb := hdv2
      simpa [Nat.cast_one, div_one, mul_assoc] using hb) hmeas
  refine ⟨hI, ?_⟩
  have hcon : (fun ω => dacPotential fh η xh (k + 1) (dacStepSched η g h k s ω))
      = fun ω : secantSpace 1 1 → Point d × Ω =>
        dacPotential fh η xh (k + 1) (dacStep k η s (roundOf h g (dacQuery k s) 1 ω)) := rfl
  rw [hcon]
  exact hb

lemma dac_potential_nonneg {fh : Point d → ℝ} {η : ℝ} {xh : Point d}
    (hη : 0 < η) (hminh : IsMinOn fh Set.univ xh) (k : ℕ) (s : Point d × Point d) :
    0 ≤ dacPotential fh η xh k s := by
  have h1 : 0 ≤ fh s.1 - fh xh := sub_nonneg.mpr (hminh (Set.mem_univ s.1))
  have h2 : 0 ≤ dacWeight k := dacWeight_nonneg k
  have h3 : 0 ≤ (8 / η) * ‖s.2 - xh‖ ^ 2 := by positivity
  unfold dacPotential
  nlinarith

lemma dac_stream_potential {g : Point d → Ω → ℝ} {fh : Point d → ℝ}
    {W : Measure (Point d × Ω)} [IsProbabilityMeasure W]
    {L η h ρ : ℝ} {xh : Point d} {Kmax : ℕ}
    (hL : 0 < L) (hη : 0 < η) (hLη : L * η ≤ 1)
    (hρη : ρ ^ 2 * ((Kmax : ℝ) + 1) * η ≤ 1)
    (hg : Measurable (Function.uncurry g))
    (hc : ConvexOn ℝ Set.univ fh)
    (hgr : ∀ x, HasGradientAt fh (gradient fh x) x)
    (hlip : ∀ x y, ‖gradient fh x - gradient fh y‖ ≤ L * ‖x - y‖)
    (hminh : IsMinOn fh Set.univ xh)
    (hint : ∀ x s, Integrable (fun u : Point d × Ω =>
        slotVal h g x s u - halfGrad fh x s) W)
    (hmean : ∀ x s, (∫ u : Point d × Ω, slotVal h g x s u ∂W) = halfGrad fh x s)
    (hvar2 : ∀ x s, Integrable (fun u : Point d × Ω =>
        ‖slotVal h g x s u - halfGrad fh x s‖ ^ 2) W)
    (hvar : ∀ x s, (∫ u : Point d × Ω, ‖slotVal h g x s u - halfGrad fh x s‖ ^ 2 ∂W)
        ≤ ρ ^ 2 * (fh x - fh xh)) :
    ∀ (K i : ℕ) (s0 : Point d × Point d),
      i + K ≤ Kmax →
      Integrable (fun Ξ => dacPotential fh η xh (i + K)
          (runSched (dacStepSched η g h) i K s0 Ξ))
          (Measure.pi fun _ : Fin K => slotLaw 1 1 W) ∧
        (∫ Ξ, dacPotential fh η xh (i + K)
            (runSched (dacStepSched η g h) i K s0 Ξ)
            ∂Measure.pi fun _ : Fin K => slotLaw 1 1 W)
          ≤ dacPotential fh η xh i s0 := by
  classical
  have hfh : Measurable fh :=
    (continuous_iff_continuousAt.mpr fun x => (hgr x).continuousAt).measurable
  have hstep : ∀ k, Measurable (fun q : (Point d × Point d) × (secantSpace 1 1 → Point d × Ω) =>
      dacStepSched η g h k q.1 q.2) :=
    fun k => measurable_dacStepSched_joint hg η h k
  intro K
  induction K with
  | zero =>
      intro i s0 _
      constructor
      · change Integrable (fun _ : Fin 0 → secantSpace 1 1 → Point d × Ω =>
            dacPotential fh η xh (i + 0) s0)
          (Measure.pi fun _ : Fin 0 => slotLaw 1 1 W)
        exact integrable_const _
      · simp [runSched, measureReal_def]
  | succ K ih =>
      intro i s0 hiK
      have hi1 : i + 1 ≤ Kmax := by omega
      have hiR : (i : ℝ) + 2 ≤ (Kmax : ℝ) + 1 := by
        have hcast : ((i + 1 : ℕ) : ℝ) ≤ (Kmax : ℝ) := Nat.cast_le.mpr hi1
        push_cast at hcast
        linarith
      have hρi : ρ ^ 2 * ((i : ℝ) + 2) * η ≤ 1 := by
        have h1 : ρ ^ 2 * ((i : ℝ) + 2) * η ≤ ρ ^ 2 * ((Kmax : ℝ) + 1) * η := by
          have hr0 : 0 ≤ ρ ^ 2 * η := by positivity
          nlinarith
        linarith
      have hbound := dac_stream_round (g := g) (fh := fh) (W := W) (L := L) (η := η) (h := h)
        (ρ := ρ) (xh := xh) i s0 hL hη hLη hρi hg hc hgr hlip hminh hint hmean hvar2 hvar
      let P1 : Measure (secantSpace 1 1 → Point d × Ω) := slotLaw 1 1 W
      let PK : Measure (Fin K → secantSpace 1 1 → Point d × Ω) :=
        Measure.pi (fun _ : Fin K => P1)
      have hidx : (i + 1) + K = i + (K + 1) := by omega
      have hiK' : (i + 1) + K ≤ Kmax := by omega
      let F := fun a : (secantSpace 1 1 → Point d × Ω) × (Fin K → secantSpace 1 1 → Point d × Ω) =>
        dacPotential fh η xh ((i + 1) + K)
          (runSched (dacStepSched η g h) (i + 1) K (dacStepSched η g h i s0 a.1) a.2)
      have hFc : Measurable F := ((measurable_dacPotential hfh η xh ((i + 1) + K)).comp
        ((measurable_runSched hstep K (i + 1)).comp
          (((hstep i).comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)))
      have hFm : AEStronglyMeasurable F (P1.prod PK) := hFc.aestronglyMeasurable
      have hF0 (a : (secantSpace 1 1 → Point d × Ω) × (Fin K → secantSpace 1 1 → Point d × Ω)) :
          0 ≤ F a :=
        dac_potential_nonneg hη hminh ((i + 1) + K) _
      have hNorm (a : secantSpace 1 1 → Point d × Ω) :
          (∫ t, ‖F (a, t)‖ ∂PK) = ∫ t, F (a, t) ∂PK := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun t => by
          change ‖F (a, t)‖ = F (a, t)
          rw [Real.norm_eq_abs, abs_of_nonneg (hF0 (a, t))])
      have hOuter : Integrable (fun a => ∫ t, ‖F (a, t)‖ ∂PK) P1 := by
        apply hbound.1.mono' hFm.norm.integral_prod_right'
        apply Filter.Eventually.of_forall
        intro a
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _)), hNorm]
        exact (ih (i + 1) (dacStepSched η g h i s0 a) hiK').2
      have hFi : Integrable F (P1.prod PK) :=
        (integrable_prod_iff hFm).mpr
          ⟨Filter.Eventually.of_forall (fun a =>
            (ih (i + 1) (dacStepSched η g h i s0 a) hiK').1), hOuter⟩
      have hp := (measurePreserving_piFinSuccAbove
        (fun _ : Fin (K + 1) => P1) 0).symm
      have hPi : Integrable (fun Ξ => dacPotential fh η xh (i + (K + 1))
            (runSched (dacStepSched η g h) i (K + 1) s0 Ξ))
          (Measure.pi (fun _ : Fin (K + 1) => P1)) := by
        rw [← hidx, ← hp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)]
        simpa only [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNthEquiv, Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk,
          runSched, Fin.cons_zero, Fin.cons_succ, cast_eq] using hFi
      refine ⟨hPi, ?_⟩
      have he : (∫ Ξ, dacPotential fh η xh (i + (K + 1))
            (runSched (dacStepSched η g h) i (K + 1) s0 Ξ)
            ∂(Measure.pi (fun _ : Fin (K + 1) => P1))) =
          ∫ a, F a ∂(P1.prod PK) := by
        rw [← hidx, ← hp.integral_comp']
        simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNthEquiv, Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk,
          runSched, Fin.cons_zero, Fin.cons_succ, cast_eq]
        rfl
      rw [he, integral_prod _ hFi]
      have hIntg : Integrable (fun a => ∫ t, F (a, t) ∂PK) P1 :=
        hOuter.congr (Filter.Eventually.of_forall fun a => hNorm a)
      have hpt : (fun a => ∫ t, F (a, t) ∂PK) ≤
          fun Ξ => dacPotential fh η xh (i + 1) (dacStepSched η g h i s0 Ξ) := fun a =>
        (ih (i + 1) (dacStepSched η g h i s0 a) hiK').2
      exact le_trans (integral_mono hIntg hbound.1 hpt) hbound.2

lemma dac_stream_gap {g : Point d → Ω → ℝ} {fh : Point d → ℝ}
    {W : Measure (Point d × Ω)} [IsProbabilityMeasure W]
    {L η h ρ : ℝ} {x0 xh : Point d} {K : ℕ}
    (hK : 0 < K) (hL : 0 < L) (hη : 0 < η) (hLη : L * η ≤ 1)
    (hρη : ρ ^ 2 * ((K : ℝ) + 1) * η ≤ 1)
    (hg : Measurable (Function.uncurry g))
    (hc : ConvexOn ℝ Set.univ fh)
    (hgr : ∀ x, HasGradientAt fh (gradient fh x) x)
    (hlip : ∀ x y, ‖gradient fh x - gradient fh y‖ ≤ L * ‖x - y‖)
    (hminh : IsMinOn fh Set.univ xh)
    (hint : ∀ x s, Integrable (fun u : Point d × Ω =>
        slotVal h g x s u - halfGrad fh x s) W)
    (hmean : ∀ x s, (∫ u : Point d × Ω, slotVal h g x s u ∂W) = halfGrad fh x s)
    (hvar2 : ∀ x s, Integrable (fun u : Point d × Ω =>
        ‖slotVal h g x s u - halfGrad fh x s‖ ^ 2) W)
    (hvar : ∀ x s, (∫ u : Point d × Ω, ‖slotVal h g x s u - halfGrad fh x s‖ ^ 2 ∂W)
        ≤ ρ ^ 2 * (fh x - fh xh)) :
    Integrable (fun Ξ => fh (runSched (dacStepSched η g h) 0 K (x0, x0) Ξ).1 - fh xh)
        (Measure.pi fun _ : Fin K => slotLaw 1 1 W) ∧
      (∫ Ξ, fh (runSched (dacStepSched η g h) 0 K (x0, x0) Ξ).1 - fh xh
          ∂Measure.pi fun _ : Fin K => slotLaw 1 1 W)
        ≤ 8 * ‖x0 - xh‖ ^ 2 / (η * dacWeight K) := by
  classical
  obtain ⟨hI0, hb0⟩ := dac_stream_potential (g := g) (fh := fh) (W := W) (L := L) (η := η)
    (h := h) (ρ := ρ) (xh := xh) (Kmax := K) hL hη hLη hρη hg hc hgr hlip hminh hint hmean
    hvar2 hvar K 0 (x0, x0) (by omega)
  have hI : Integrable (fun Ξ => dacPotential fh η xh K
      (runSched (dacStepSched η g h) 0 K (x0, x0) Ξ))
      (Measure.pi fun _ : Fin K => slotLaw 1 1 W) := by
    simpa [Nat.zero_add] using hI0
  have hb : (∫ Ξ, dacPotential fh η xh K (runSched (dacStepSched η g h) 0 K (x0, x0) Ξ)
      ∂Measure.pi fun _ : Fin K => slotLaw 1 1 W) ≤ (8 / η) * ‖x0 - xh‖ ^ 2 := by
    have hp0 : dacPotential fh η xh 0 (x0, x0) = (8 / η) * ‖x0 - xh‖ ^ 2 := by
      unfold dacPotential dacWeight
      simp
    simpa [Nat.zero_add, hp0] using hb0
  have hKpos : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr hK
  have hwpos : 0 < dacWeight K := by
    unfold dacWeight
    positivity
  have hfh : Measurable fh :=
    (continuous_iff_continuousAt.mpr fun x => (hgr x).continuousAt).measurable
  have hrm := measurable_runSched (step := dacStepSched η g h)
    (fun k => measurable_dacStepSched_joint hg η h k) K 0
  have hV : Measurable (fun Ξ => fh (runSched (dacStepSched η g h) 0 K (x0, x0) Ξ).1 - fh xh) :=
    ((hfh.comp measurable_fst).comp
      (hrm.comp (measurable_const.prodMk measurable_id))).sub measurable_const
  have hnonneg : ∀ Ξ, 0 ≤ fh (runSched (dacStepSched η g h) 0 K (x0, x0) Ξ).1 - fh xh :=
    fun _ => sub_nonneg.mpr (hminh (Set.mem_univ _))
  have hle : ∀ Ξ, fh (runSched (dacStepSched η g h) 0 K (x0, x0) Ξ).1 - fh xh
      ≤ dacPotential fh η xh K (runSched (dacStepSched η g h) 0 K (x0, x0) Ξ) / dacWeight K := by
    intro Ξ
    refine (le_div_iff₀ hwpos).mpr ?_
    have ha : 0 ≤ (8 / η) * ‖(runSched (dacStepSched η g h) 0 K (x0, x0) Ξ).2 - xh‖ ^ 2 := by
      positivity
    unfold dacPotential
    linarith
  have hId : Integrable (fun Ξ =>
      dacPotential fh η xh K (runSched (dacStepSched η g h) 0 K (x0, x0) Ξ) / dacWeight K)
      (Measure.pi fun _ : Fin K => slotLaw 1 1 W) := hI.div_const (dacWeight K)
  have hInt : Integrable (fun Ξ => fh (runSched (dacStepSched η g h) 0 K (x0, x0) Ξ).1 - fh xh)
      (Measure.pi fun _ : Fin K => slotLaw 1 1 W) :=
    hId.mono' hV.aestronglyMeasurable (ae_of_all _ fun Ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg Ξ)]
      exact hle Ξ)
  refine ⟨hInt, ?_⟩
  have hm := integral_mono_ae hInt hId (ae_of_all _ hle)
  rw [integral_div] at hm
  have hdiv : (∫ Ξ, dacPotential fh η xh K (runSched (dacStepSched η g h) 0 K (x0, x0) Ξ)
        ∂Measure.pi fun _ : Fin K => slotLaw 1 1 W) / dacWeight K
      ≤ ((8 / η) * ‖x0 - xh‖ ^ 2) / dacWeight K :=
    div_le_div_of_nonneg_right hb hwpos.le
  have heq : ((8 / η) * ‖x0 - xh‖ ^ 2) / dacWeight K = 8 * ‖x0 - xh‖ ^ 2 / (η * dacWeight K) := by
    field_simp [hη.ne', hwpos.ne']
  linarith

end OracleTemplate.SecantPolyak.AnchoredConvexPair

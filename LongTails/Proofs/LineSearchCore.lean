import LongTails.Proofs.LineSearchPairs

open Set

namespace OracleTemplate.LineSearch

variable (R x0 : ℝ)

/-- Total estimation error of one level, using the value estimates `v`. -/
noncomputable def lvlErr (v : ℕ → ℝ × ℝ) (f : ℝ → ℝ) (j : ℕ) : ℝ :=
  |(v j).1 - f (leftPoint (runState R x0 v j))| +
    |(v j).2 - f (rightPoint (runState R x0 v j))|

lemma lvlErr_nonneg (v : ℕ → ℝ × ℝ) (f : ℝ → ℝ) (j : ℕ) : 0 ≤ lvlErr R x0 v f j := by
  unfold lvlErr
  positivity

lemma lvlErr_left {v : ℕ → ℝ × ℝ} {f : ℝ → ℝ} {j : ℕ} :
    (v j).1 - f (leftPoint (runState R x0 v j)) ≤ lvlErr R x0 v f j := by
  unfold lvlErr
  linarith [le_abs_self ((v j).1 - f (leftPoint (runState R x0 v j))),
    abs_nonneg ((v j).2 - f (rightPoint (runState R x0 v j)))]

lemma lvlErr_right {v : ℕ → ℝ × ℝ} {f : ℝ → ℝ} {j : ℕ} :
    (v j).2 - f (rightPoint (runState R x0 v j)) ≤ lvlErr R x0 v f j := by
  unfold lvlErr
  linarith [le_abs_self ((v j).2 - f (rightPoint (runState R x0 v j))),
    abs_nonneg ((v j).1 - f (leftPoint (runState R x0 v j)))]

lemma leftPoint_val (s : State) : leftPoint s = s.lo + (s.hi - s.lo) / 3 := rfl

lemma rightPoint_val (s : State) : rightPoint s = s.lo + 2 * (s.hi - s.lo) / 3 := rfl

lemma leftPoint_interval {s : State} (hs : s.lo ≤ s.hi) :
    s.lo ≤ leftPoint s ∧ leftPoint s ≤ s.hi := by
  unfold leftPoint
  exact ⟨by nlinarith, by nlinarith⟩

lemma rightPoint_interval {s : State} (hs : s.lo ≤ s.hi) :
    s.lo ≤ rightPoint s ∧ rightPoint s ≤ s.hi := by
  unfold rightPoint
  exact ⟨by nlinarith, by nlinarith⟩

lemma step_level0 {s : State} (h0 : s.level = 0) (v : ℝ × ℝ) :
    (step s v).champ = (if v.1 > v.2 then rightPoint s else leftPoint s) ∧
      (step s v).champVal = min v.1 v.2 := by
  rw [step, ite_eq_left h0]
  exact ⟨rfl, rfl⟩

lemma step_champ_updated {s : State} (h0 : s.level ≠ 0) (v : ℝ × ℝ)
    (hc : min v.1 v.2 < s.champVal) :
    (step s v).champ = (if v.1 > v.2 then rightPoint s else leftPoint s) ∧
      (step s v).champVal = min v.1 v.2 := by
  rw [step, ite_eq_right h0, ite_eq_left hc]
  exact ⟨rfl, rfl⟩

lemma step_champ_kept {s : State} (h0 : s.level ≠ 0) (v : ℝ × ℝ)
    (hc : ¬ min v.1 v.2 < s.champVal) :
    (step s v).champ = s.champ ∧ (step s v).champVal = s.champVal := by
  rw [step, ite_eq_right h0, ite_eq_right hc]
  exact ⟨rfl, rfl⟩

/-- The estimate of a level dominates the true value of the champion it selects. -/
lemma lvlEstimate_le {v : ℕ → ℝ × ℝ} {f : ℝ → ℝ} {j : ℕ} :
    f (if (v j).1 > (v j).2 then rightPoint (runState R x0 v j)
        else leftPoint (runState R x0 v j))
      ≤ min (v j).1 (v j).2 + lvlErr R x0 v f j := by
  by_cases hv : (v j).1 > (v j).2
  · rw [ite_eq_left hv, min_eq_right (by linarith)]
    unfold lvlErr
    linarith [neg_le_abs ((v j).2 - f (rightPoint (runState R x0 v j))),
      abs_nonneg ((v j).1 - f (leftPoint (runState R x0 v j)))]
  · rw [ite_eq_right hv, min_eq_left (by linarith)]
    unfold lvlErr
    linarith [neg_le_abs ((v j).1 - f (leftPoint (runState R x0 v j))),
      abs_nonneg ((v j).2 - f (rightPoint (runState R x0 v j)))]

lemma step_lo_ge (s : State) (v : ℝ × ℝ) (hs : s.lo ≤ s.hi) : s.lo ≤ (step s v).lo := by
  rw [lo_step]
  by_cases hv : v.1 > v.2
  · rw [ite_eq_left hv]
    exact (leftPoint_interval hs).1
  · rw [ite_eq_right hv]

lemma step_hi_le (s : State) (v : ℝ × ℝ) (hs : s.lo ≤ s.hi) : (step s v).hi ≤ s.hi := by
  rw [hi_step]
  by_cases hv : v.1 > v.2
  · rw [ite_eq_left hv]
  · rw [ite_eq_right hv]
    exact (rightPoint_interval hs).2

lemma runState_lo_ge (v : ℕ → ℝ × ℝ) (hs : x0 - R ≤ x0 + R) (j : ℕ) :
    x0 - R ≤ (runState R x0 v j).lo := by
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
      rw [runState_succ R x0 v j]
      exact le_trans ih (step_lo_ge _ _ (runState_interval_le R x0 v hs j))

lemma runState_hi_le (v : ℕ → ℝ × ℝ) (hs : x0 - R ≤ x0 + R) (j : ℕ) :
    (runState R x0 v j).hi ≤ x0 + R := by
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
      rw [runState_succ R x0 v j]
      exact le_trans (step_hi_le _ _ (runState_interval_le R x0 v hs j)) ih

lemma runState_len_succ (v : ℕ → ℝ × ℝ) (j : ℕ) :
    (runState R x0 v (j + 1)).hi - (runState R x0 v (j + 1)).lo
      = 2 * ((runState R x0 v j).hi - (runState R x0 v j).lo) / 3 := by
  have h1 := lo_step (runState R x0 v j) (v j)
  have h2 := hi_step (runState R x0 v j) (v j)
  rw [runState_succ R x0 v j]
  by_cases hv : (v j).1 > (v j).2
  · rw [h1, h2, ite_eq_left hv, ite_eq_left hv, leftPoint_val]
    ring
  · rw [h1, h2, ite_eq_right hv, ite_eq_right hv, rightPoint_val]
    ring

lemma runState_len_le (v : ℕ → ℝ × ℝ) (_hs : x0 - R ≤ x0 + R) (j : ℕ) :
    (runState R x0 v j).hi - (runState R x0 v j).lo ≤ 2 * R * ((2:ℝ) / 3) ^ j := by
  induction j with
  | zero =>
      rw [pow_zero, mul_one, runState_zero_hi, runState_zero_lo]
      exact le_of_eq (by ring)
  | succ j ih =>
      rw [runState_len_succ R x0 v j, pow_succ]
      nlinarith [pow_nonneg (show (0 : ℝ) ≤ 2 / 3 by norm_num) j]

lemma lvlPoints_left {v : ℕ → ℝ × ℝ} (hs : x0 - R ≤ x0 + R) (j : ℕ) :
    leftPoint (runState R x0 v j) ∈ Icc (x0 - R) (x0 + R) :=
  ⟨le_trans (runState_lo_ge R x0 v hs j) (leftPoint_interval (runState_interval_le R x0 v hs j)).1,
    le_trans (leftPoint_interval (runState_interval_le R x0 v hs j)).2
      (runState_hi_le R x0 v hs j)⟩

lemma lvlPoints_right {v : ℕ → ℝ × ℝ} (hs : x0 - R ≤ x0 + R) (j : ℕ) :
    rightPoint (runState R x0 v j) ∈ Icc (x0 - R) (x0 + R) :=
  ⟨le_trans (runState_lo_ge R x0 v hs j)
      (rightPoint_interval (runState_interval_le R x0 v hs j)).1,
    le_trans (rightPoint_interval (runState_interval_le R x0 v hs j)).2
      (runState_hi_le R x0 v hs j)⟩

/-- At a level whose interval holds a minimizer, both queries are close to optimal. -/
lemma lvlTrueGap_le {v : ℕ → ℝ × ℝ} {f : ℝ → ℝ} {xstar L : ℝ}
    (hsmooth : ∀ x ∈ Icc (x0 - R) (x0 + R), f x - f xstar ≤ L / 2 * (x - xstar) ^ 2)
    (hL : 0 < L) (hR : x0 - R ≤ x0 + R) {j : ℕ}
    (hx : xstar ∈ Icc (runState R x0 v j).lo (runState R x0 v j).hi) :
    min (f (leftPoint (runState R x0 v j))) (f (rightPoint (runState R x0 v j))) - f xstar
      ≤ L / 2 * (2 * R * ((2:ℝ) / 3) ^ j) ^ 2 := by
  have hinterval := runState_interval_le R x0 v hR j
  have hl := leftPoint_interval hinterval
  have hr := rightPoint_interval hinterval
  have hlen := runState_len_le R x0 v hR j
  have h1 : f (leftPoint (runState R x0 v j)) - f xstar
      ≤ L / 2 * (leftPoint (runState R x0 v j) - xstar) ^ 2 :=
    hsmooth _ (lvlPoints_left R x0 hR j)
  have h2 : f (rightPoint (runState R x0 v j)) - f xstar
      ≤ L / 2 * (rightPoint (runState R x0 v j) - xstar) ^ 2 :=
    hsmooth _ (lvlPoints_right R x0 hR j)
  have hl1 := hl.1
  have hl2 := hl.2
  have hr1 := hr.1
  have hr2 := hr.2
  have hx1 := hx.1
  have hx2 := hx.2
  have hd1 : |leftPoint (runState R x0 v j) - xstar|
      ≤ (runState R x0 v j).hi - (runState R x0 v j).lo := by
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hd2 : |rightPoint (runState R x0 v j) - xstar|
      ≤ (runState R x0 v j).hi - (runState R x0 v j).lo := by
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hn1 : (leftPoint (runState R x0 v j) - xstar) ^ 2
      ≤ ((runState R x0 v j).hi - (runState R x0 v j).lo) ^ 2 := by
    nlinarith [abs_mul_abs_self (leftPoint (runState R x0 v j) - xstar), hd1]
  have hn2 : (rightPoint (runState R x0 v j) - xstar) ^ 2
      ≤ ((runState R x0 v j).hi - (runState R x0 v j).lo) ^ 2 := by
    nlinarith [abs_mul_abs_self (rightPoint (runState R x0 v j) - xstar), hd2]
  have hL2 : 0 ≤ L / 2 := by linarith
  have hn : 0 ≤ (runState R x0 v j).hi - (runState R x0 v j).lo := by linarith [hinterval]
  have hn1' : L / 2 * (leftPoint (runState R x0 v j) - xstar) ^ 2
      ≤ L / 2 * (2 * R * ((2:ℝ) / 3) ^ j) ^ 2 :=
    mul_le_mul_of_nonneg_left (by nlinarith [hlen]) hL2
  calc min (f (leftPoint (runState R x0 v j))) (f (rightPoint (runState R x0 v j))) - f xstar
      ≤ f (leftPoint (runState R x0 v j)) - f xstar := sub_le_sub_right (min_le_left _ _) _
    _ ≤ L / 2 * (leftPoint (runState R x0 v j) - xstar) ^ 2 := h1
    _ ≤ _ := hn1'

/-- The level estimates dominate the true query values up to the level error. -/
lemma lvlMinEstimate_le {v : ℕ → ℝ × ℝ} {f : ℝ → ℝ} {j : ℕ} :
    min (v j).1 (v j).2
      ≤ min (f (leftPoint (runState R x0 v j))) (f (rightPoint (runState R x0 v j)))
        + lvlErr R x0 v f j := by
  have h1 : (v j).1 ≤ f (leftPoint (runState R x0 v j)) + lvlErr R x0 v f j := by
    linarith [lvlErr_left R x0 (v := v) (f := f) (j := j)]
  have h2 : (v j).2 ≤ f (rightPoint (runState R x0 v j)) + lvlErr R x0 v f j := by
    linarith [lvlErr_right R x0 (v := v) (f := f) (j := j)]
  rcases le_total (v j).1 (v j).2 with h | h
  · rw [min_eq_left h]
    rcases le_total (f (leftPoint (runState R x0 v j)))
        (f (rightPoint (runState R x0 v j))) with h' | h'
    · rw [min_eq_left h']
      linarith
    · rw [min_eq_right h']
      linarith
  · rw [min_eq_right h]
    rcases le_total (f (leftPoint (runState R x0 v j)))
        (f (rightPoint (runState R x0 v j))) with h' | h'
    · rw [min_eq_left h']
      linarith
    · rw [min_eq_right h']
      linarith

/-- The incumbent point pays at most the errors accumulated over the previous levels. -/
lemma champ_le_champVal_add (v : ℕ → ℝ × ℝ) (f : ℝ → ℝ) : ∀ k : ℕ,
    f (runState R x0 v (k + 1)).champ
      ≤ (runState R x0 v (k + 1)).champVal + ∑ i ∈ Finset.range (k + 1), lvlErr R x0 v f i := by
  intro k
  induction k with
  | zero =>
      have hlvl : (runState R x0 v 0).level = 0 := runState_level R x0 v 0
      obtain ⟨hc1, hc2⟩ := step_level0 hlvl (v 0)
      rw [runState_succ R x0 v 0, hc1, hc2, Finset.sum_range_one]
      exact lvlEstimate_le R x0 (v := v) (f := f) (j := 0)
  | succ k ih =>
      have hlvl : ¬ (runState R x0 v (k + 1)).level = 0 := by
        rw [runState_level]
        omega
      rw [runState_succ R x0 v (k + 1), Finset.sum_range_succ]
      by_cases hc : min (v (k + 1)).1 (v (k + 1)).2 < (runState R x0 v (k + 1)).champVal
      · obtain ⟨hc1, hc2⟩ := step_champ_updated hlvl (v (k + 1)) hc
        rw [hc1, hc2]
        have := lvlEstimate_le R x0 (v := v) (f := f) (j := k + 1)
        have hsum : 0 ≤ ∑ i ∈ Finset.range (k + 1), lvlErr R x0 v f i :=
          Finset.sum_nonneg (fun i _ => lvlErr_nonneg R x0 v f i)
        linarith
      · obtain ⟨hc1, hc2⟩ := step_champ_kept hlvl (v (k + 1)) hc
        rw [hc1, hc2]
        linarith [ih, lvlErr_nonneg R x0 v f (k + 1)]

/-- Countdown over levels: while the interval holds a minimizer the incumbent value is accurate. -/
lemma champVal_countdown {v : ℕ → ℝ × ℝ} {f : ℝ → ℝ} {xstar L : ℝ}
    (hconv : ConvexOn ℝ univ f) (hmin : IsMinOn f univ xstar)
    (hsmooth : ∀ x ∈ Icc (x0 - R) (x0 + R), f x - f xstar ≤ L / 2 * (x - xstar) ^ 2)
    (hL : 0 < L) (hR : x0 - R ≤ x0 + R) {J : ℕ} (hJ : 1 ≤ J) :
    ∀ k : ℕ, k < J →
      xstar ∈ Icc (runState R x0 v (J - 1 - k)).lo (runState R x0 v (J - 1 - k)).hi →
        (runState R x0 v J).champVal - f xstar
          ≤ L / 2 * (2 * R * ((2:ℝ) / 3) ^ (J - 1)) ^ 2
            + 2 * ∑ i ∈ Finset.Ico (J - 1 - k) J, lvlErr R x0 v f i := by
  intro k
  induction k with
  | zero =>
      intro _ hk
      simp only [Nat.sub_zero] at hk ⊢
      have hJ1 : J - 1 < J := by omega
      have hcv := champVal_runState_le_min R x0 v hJ1
      have htrue := lvlTrueGap_le R x0 (v := v) (f := f) (xstar := xstar) (L := L) hsmooth hL hR hk
      have hest := lvlMinEstimate_le R x0 (v := v) (f := f) (j := J - 1)
      have hsum : ∑ i ∈ Finset.Ico (J - 1) J, lvlErr R x0 v f i = lvlErr R x0 v f (J - 1) := by
        have hs : Finset.Ico (J - 1) J = {(J - 1)} := by
          ext i
          simp only [Finset.mem_Ico, Finset.mem_singleton]
          omega
        rw [hs, Finset.sum_singleton]
      calc (runState R x0 v J).champVal - f xstar
          ≤ min (v (J - 1)).1 (v (J - 1)).2 - f xstar := by linarith
        _ ≤ (min (f (leftPoint (runState R x0 v (J - 1))))
              (f (rightPoint (runState R x0 v (J - 1)))) + lvlErr R x0 v f (J - 1))
              - f xstar := by linarith
        _ ≤ L / 2 * (2 * R * ((2:ℝ) / 3) ^ (J - 1)) ^ 2 + lvlErr R x0 v f (J - 1) := by linarith
        _ ≤ _ := by
          have := lvlErr_nonneg R x0 v f (J - 1)
          have hge : L / 2 * (2 * R * ((2:ℝ) / 3) ^ (J - 1)) ^ 2 ≥ 0 := by positivity
          nlinarith [hsum]
  | succ k ih =>
      intro hk hx
      have hj : J - 1 - k.succ < J := by omega
      have hnext : J - 1 - k.succ + 1 = J - 1 - k := by omega
      by_cases hgood : xstar ∈ Icc (runState R x0 v (J - 1 - k)).lo
          (runState R x0 v (J - 1 - k)).hi
      · have := ih (by omega) hgood
        refine le_trans this (add_le_add_right ?_ _)
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 2)
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => lvlErr_nonneg R x0 v f i)
        intro i hi
        simp only [Finset.mem_Ico] at hi ⊢
        omega
      · have hcv := champVal_runState_le_min R x0 v hj
        have hfail : xstar ∉ Icc (step (runState R x0 v (J - 1 - k.succ))
            (v (J - 1 - k.succ))).lo (step (runState R x0 v (J - 1 - k.succ))
            (v (J - 1 - k.succ))).hi := by
          intro h
          rw [← runState_succ R x0 v (J - 1 - k.succ), hnext] at h
          exact hgood h
        have hharm := harm_le_errors_of_fail R x0 hconv hmin hx hfail
        have hest := lvlMinEstimate_le R x0 (v := v) (f := f) (j := J - 1 - k.succ)
        have hmem : lvlErr R x0 v f (J - 1 - k.succ)
            ≤ ∑ i ∈ Finset.Ico (J - 1 - k.succ) J, lvlErr R x0 v f i := by
          have h1 : lvlErr R x0 v f (J - 1 - k.succ)
              = ∑ i ∈ ({J - 1 - k.succ} : Finset ℕ), lvlErr R x0 v f i :=
            (Finset.sum_singleton _ _).symm
          rw [h1]
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => lvlErr_nonneg R x0 v f i)
          intro i hi
          simp only [Finset.mem_singleton] at hi
          subst hi
          exact Finset.mem_Ico.mpr ⟨by omega, hj⟩
        have hge : 0 ≤ L / 2 * (2 * R * ((2:ℝ) / 3) ^ (J - 1)) ^ 2 := by positivity
        calc (runState R x0 v J).champVal - f xstar
            ≤ min (v (J - 1 - k.succ)).1 (v (J - 1 - k.succ)).2 - f xstar := by linarith
          _ ≤ 2 * lvlErr R x0 v f (J - 1 - k.succ) := by
            unfold lvlErr at hest ⊢
            linarith [hharm]
          _ ≤ _ := by
            refine le_trans (mul_le_mul_of_nonneg_left hmem (by norm_num : (0 : ℝ) ≤ 2)) ?_
            nlinarith

/-- Deterministic accuracy of the line search after `J` levels. -/
lemma line_search_gap_le {v : ℕ → ℝ × ℝ} {f : ℝ → ℝ} {xstar L : ℝ}
    (hconv : ConvexOn ℝ univ f) (hmin : IsMinOn f univ xstar)
    (hsmooth : ∀ x ∈ Icc (x0 - R) (x0 + R), f x - f xstar ≤ L / 2 * (x - xstar) ^ 2)
    (hL : 0 < L) (hR : x0 - R ≤ x0 + R) (hx : xstar ∈ Icc (x0 - R) (x0 + R))
    {J : ℕ} (hJ : 1 ≤ J) :
    f (runState R x0 v J).champ - f xstar
      ≤ L / 2 * (2 * R * ((2:ℝ) / 3) ^ (J - 1)) ^ 2
        + 3 * ∑ j ∈ Finset.range J, lvlErr R x0 v f j := by
  have hkey := champVal_countdown R x0 (v := v) (f := f) (xstar := xstar) (L := L) hconv hmin
    hsmooth hL hR hJ (J - 1) (by omega)
    (by
      have hz : J - 1 - (J - 1) = 0 := by omega
      rw [hz]
      show xstar ∈ Icc (runState R x0 v 0).lo (runState R x0 v 0).hi
      rw [runState_zero_lo, runState_zero_hi]
      exact hx)
  have hchamp := champ_le_champVal_add R x0 v f (J - 1)
  have h1 : J - 1 + 1 = J := by omega
  rw [h1] at hchamp
  have h2 : J - 1 - (J - 1) = 0 := by omega
  rw [h2] at hkey
  rw [Finset.range_eq_Ico] at hchamp ⊢
  linarith [hkey, hchamp]

end OracleTemplate.LineSearch

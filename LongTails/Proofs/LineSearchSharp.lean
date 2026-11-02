import LongTails.Proofs.LineSearchCore

open Set

namespace OracleTemplate.LineSearch

variable (R x0 : ℝ)

lemma champ_le_champVal_delta {v : ℕ → ℝ × ℝ} {f : ℝ → ℝ} {δ : ℝ} :
    ∀ k : ℕ, (∀ j, j ≤ k → lvlErr R x0 v f j ≤ δ) →
      f (runState R x0 v (k + 1)).champ ≤ (runState R x0 v (k + 1)).champVal + δ := by
  intro k
  induction k with
  | zero =>
      intro h0
      have hlvl : (runState R x0 v 0).level = 0 := runState_level R x0 v 0
      obtain ⟨hc1, hc2⟩ := step_level0 hlvl (v 0)
      rw [runState_succ R x0 v 0, hc1, hc2]
      exact (lvlEstimate_le R x0 (v := v) (f := f) (j := 0)).trans (by linarith [h0 0 (by omega)])
  | succ k ih =>
      intro hest
      have hlvl : ¬ (runState R x0 v (k + 1)).level = 0 := by
        rw [runState_level]
        omega
      rw [runState_succ R x0 v (k + 1)]
      by_cases hc : min (v (k + 1)).1 (v (k + 1)).2 < (runState R x0 v (k + 1)).champVal
      · obtain ⟨hc1, hc2⟩ := step_champ_updated hlvl (v (k + 1)) hc
        rw [hc1, hc2]
        exact (lvlEstimate_le R x0 (v := v) (f := f) (j := k + 1)).trans
          (by linarith [hest (k + 1) (by omega)])
      · obtain ⟨hc1, hc2⟩ := step_champ_kept hlvl (v (k + 1)) hc
        rw [hc1, hc2]
        exact ih (fun j hj => hest j (by omega))

lemma champVal_countdown_delta {v : ℕ → ℝ × ℝ} {f : ℝ → ℝ} {xstar L δ : ℝ}
    (hconv : ConvexOn ℝ univ f) (hmin : IsMinOn f univ xstar)
    (hsmooth : ∀ x ∈ Icc (x0 - R) (x0 + R), f x - f xstar ≤ L / 2 * (x - xstar) ^ 2)
    (hL : 0 < L) (hR : x0 - R ≤ x0 + R) {J : ℕ} (hJ : 1 ≤ J)
    (herr : ∀ j, j < J → lvlErr R x0 v f j ≤ δ) :
    ∀ k : ℕ, k < J →
      xstar ∈ Icc (runState R x0 v (J - 1 - k)).lo (runState R x0 v (J - 1 - k)).hi →
        (runState R x0 v J).champVal - f xstar
          ≤ L / 2 * (2 * R * ((2:ℝ) / 3) ^ (J - 1)) ^ 2 + 2 * δ := by
  intro k
  induction k with
  | zero =>
      intro _ hk
      have hk' : xstar ∈ Icc (runState R x0 v (J - 1)).lo (runState R x0 v (J - 1)).hi := hk
      have hJ1 : J - 1 < J := by omega
      have hcv := champVal_runState_le_min R x0 v hJ1
      have htrue := lvlTrueGap_le R x0 (v := v) (f := f) (xstar := xstar) (L := L) hsmooth hL hR hk'
      have hest := lvlMinEstimate_le R x0 (v := v) (f := f) (j := J - 1)
      have hle := herr (J - 1) hJ1
      have hδ : 0 ≤ δ := le_trans (lvlErr_nonneg R x0 v f (J - 1)) hle
      have hge : 0 ≤ L / 2 * (2 * R * ((2:ℝ) / 3) ^ (J - 1)) ^ 2 := by positivity
      calc (runState R x0 v J).champVal - f xstar
          ≤ min (v (J - 1)).1 (v (J - 1)).2 - f xstar := by linarith
        _ ≤ (min (f (leftPoint (runState R x0 v (J - 1))))
              (f (rightPoint (runState R x0 v (J - 1)))) + lvlErr R x0 v f (J - 1)) - f xstar :=
          by linarith
        _ ≤ L / 2 * (2 * R * ((2:ℝ) / 3) ^ (J - 1)) ^ 2 + lvlErr R x0 v f (J - 1) := by linarith
        _ ≤ _ := by linarith
  | succ k ih =>
      intro hk hx
      have hj : J - 1 - k.succ < J := by omega
      have hnext : J - 1 - k.succ + 1 = J - 1 - k := by omega
      by_cases hgood : xstar ∈ Icc (runState R x0 v (J - 1 - k)).lo
          (runState R x0 v (J - 1 - k)).hi
      · exact ih (by omega) hgood
      · have hcv := champVal_runState_le_min R x0 v hj
        have hfail : xstar ∉ Icc (step (runState R x0 v (J - 1 - k.succ))
            (v (J - 1 - k.succ))).lo (step (runState R x0 v (J - 1 - k.succ))
            (v (J - 1 - k.succ))).hi := by
          intro h
          rw [← runState_succ R x0 v (J - 1 - k.succ), hnext] at h
          exact hgood h
        have hharm := harm_le_errors_of_fail R x0 hconv hmin hx hfail
        have hest := lvlMinEstimate_le R x0 (v := v) (f := f) (j := J - 1 - k.succ)
        have hle := herr (J - 1 - k.succ) hj
        unfold lvlErr at hest hharm hle
        have hge : 0 ≤ L / 2 * (2 * R * ((2:ℝ) / 3) ^ (J - 1)) ^ 2 := by positivity
        calc (runState R x0 v J).champVal - f xstar
            ≤ min (v (J - 1 - k.succ)).1 (v (J - 1 - k.succ)).2 - f xstar := by linarith
          _ ≤ 2 * (|(v (J - 1 - k.succ)).1 - f (leftPoint (runState R x0 v (J - 1 - k.succ)))|
              + |(v (J - 1 - k.succ)).2 - f (rightPoint (runState R x0 v (J - 1 - k.succ)))|) := by
            linarith
          _ ≤ _ := by linarith

lemma line_search_gap_le_delta {v : ℕ → ℝ × ℝ} {f : ℝ → ℝ} {xstar L δ : ℝ}
    (hconv : ConvexOn ℝ univ f) (hmin : IsMinOn f univ xstar)
    (hsmooth : ∀ x ∈ Icc (x0 - R) (x0 + R), f x - f xstar ≤ L / 2 * (x - xstar) ^ 2)
    (hL : 0 < L) (hR : x0 - R ≤ x0 + R) (hx : xstar ∈ Icc (x0 - R) (x0 + R))
    {J : ℕ} (hJ : 1 ≤ J) (herr : ∀ j, j < J → lvlErr R x0 v f j ≤ δ) :
    f (runState R x0 v J).champ - f xstar
      ≤ L / 2 * (2 * R * ((2:ℝ) / 3) ^ (J - 1)) ^ 2 + 3 * δ := by
  have hz : xstar ∈ Icc (runState R x0 v 0).lo (runState R x0 v 0).hi := by
    rw [runState_zero_lo, runState_zero_hi]
    exact hx
  have hk0 : J - 1 - (J - 1) = 0 := by omega
  have hcv := champVal_countdown_delta R x0 hconv hmin hsmooth hL hR hJ herr (J - 1)
    (by omega) (by rw [hk0]; exact hz)
  have hchamp := champ_le_champVal_delta R x0 (J - 1) (fun j hj => herr j (by omega))
  have hsub : (J - 1) + 1 = J := by omega
  rw [hsub] at hchamp
  linarith

end OracleTemplate.LineSearch

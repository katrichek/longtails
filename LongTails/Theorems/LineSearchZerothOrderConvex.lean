import LongTails.Setups.ZerothOrderLineConvex
import LongTails.Proofs.LineSearchSpace
import LongTails.Proofs.LineSearchTuning

namespace LongTails.Theorems.LineSearchZerothOrderConvex

open OracleTemplate MeasureTheory ProbabilityTheory
open LongTails.Setups
open scoped BigOperators

/-- Levels of the line search, one ternary reduction per level. -/
noncomputable def levels (q : LongTails.Setups.ZerothOrderLineConvex.spec.Params) : ℕ :=
  1 + ⌈Real.log (4 * q.val.L * q.val.R ^ 2 / q.val.ε) / Real.log (9 / 4)⌉₊

/-- Samples averaged per comparison point of a line search level. -/
noncomputable def samples (q : LongTails.Setups.ZerothOrderLineConvex.spec.Params) : ℕ :=
  1 + ⌈(12 * (levels q : ℝ) * q.val.σ / q.val.ε) ^ 2⌉₊

noncomputable def budget :
    (let S := LongTails.Setups.ZerothOrderLineConvex.spec; S.Params → Fin S.numOracles → ℕ) :=
  fun q _ => (1 + ⌈Real.log (4 * q.val.L * q.val.R ^ 2 / q.val.ε) / Real.log (9 / 4)⌉₊) * (2 * (1 + ⌈(12 * ↑(1 + ⌈Real.log (4 * q.val.L * q.val.R ^ 2 / q.val.ε) / Real.log (9 / 4)⌉₊) * q.val.σ / q.val.ε) ^ 2⌉₊))

theorem result : Convergence LongTails.Setups.ZerothOrderLineConvex.spec budget := by
  classical
  refine ⟨fun q =>
      if h : Nonempty (q.val.E ≃ₗᵢ[ℝ] LongTails.Setups.ZerothOrderSmoothAndConvex.Point q.val.d) then
        LineSearch.ofReal (LineSearch.uOf q.property h.some)
          (LineSearch.lineSearch q.val.R (LineSearch.psiOf q.property h.some q.val.x0)
            (by simp only [samples]; omega : 0 < 2 * samples q))
      else
        { State := q.val.E, initial := fun _ => q.val.x0, query := fun x => (0, x),
          update := fun x _ => x, output := id },
    ?_, fun _ _ => trivial⟩
  intro q hq f O ho
  rcases hq with ⟨_, hL, hR, hσ, hε⟩
  rcases ho with ⟨he, g, p, P, hind, hmarg, hO, hconv, hg, hlip, hxs, hgm, hgi, hmean, hgsq, hvar⟩
  obtain ⟨xstar, hmin, hdist⟩ := hxs
  have hd : q.val.d = 1 := q.property
  subst hO
  have hpos : 0 < samples q := by simp only [samples]; omega
  have hJ1 : 1 ≤ levels q := by
    show 1 ≤ 1 + ⌈Real.log (4 * q.val.L * q.val.R ^ 2 / q.val.ε) / Real.log (9 / 4)⌉₊
    omega
  have hJ : ((levels q : ℕ) : ℝ) = 1 + ⌈Real.log (4 * q.val.L * q.val.R ^ 2 / q.val.ε)
      / Real.log (9 / 4)⌉₊ := by simp only [levels, Nat.cast_add, Nat.cast_one]
  have hm : ((samples q : ℕ) : ℝ) =
      1 + ⌈(12 * (levels q : ℝ) * q.val.σ / q.val.ε) ^ 2⌉₊ := by
    simp only [samples, Nat.cast_add, Nat.cast_one]
  have hbound : q.val.L / 2 * (2 * q.val.R * ((2:ℝ) / 3) ^ (levels q - 1)) ^ 2
        + (levels q : ℝ) * (3 * (2 * (q.val.σ / Real.sqrt (samples q)))) ≤ q.val.ε :=
    LineSearch.Tuning.tuning_bound hL hR hσ hε (levels q) (samples q) hJ hm
  have htransport : ∀ (OG : Oracle q.val.E ℝ) (A A' : Algorithm q.val.E ℝ q.val.E), A = A' →
        LongTails.Setups.ZerothOrderLineConvex.spec.successful q f
            (fun seed : A.Seed × ((k : ℕ) → OG.Seed k) => execute OG A (budget q) seed.1 seed.2)
            ⟨(A.law : Measure _).prod (OG.law : Measure _), inferInstance⟩ →
        LongTails.Setups.ZerothOrderLineConvex.spec.successful q f
            (fun seed : A'.Seed × ((k : ℕ) → OG.Seed k) =>
              execute OG A' (budget q) seed.1 seed.2)
            ⟨(A'.law : Measure _).prod (OG.law : Measure _), inferInstance⟩ := by
    intro OG A A' hAA h
    cases hAA
    exact h
  refine htransport _ _ _ (dite_eq_left he).symm ?_
  have hgm0 :
      Measurable (Function.uncurry (fun t : ℝ => fun ω : q.val.Ω => g (LineSearch.uOf hd he.some t) ω)) := by
    have h1 : Function.uncurry (fun t : ℝ => fun ω : q.val.Ω => g (LineSearch.uOf hd he.some t) ω)
        = fun z : ℝ × q.val.Ω => Function.uncurry g (LineSearch.uOf hd he.some z.1, z.2) := rfl
    rw [h1]
    exact hgm.comp
      (((LineSearch.uOf_measurable hd he.some).comp measurable_fst).prodMk measurable_snd)
  have hres := LineSearch.line_search_expected_space (hd := hd) (e := he.some) (f := f)
    (L := q.val.L) (R := q.val.R) (σ := q.val.σ) (ε := q.val.ε) (x0 := q.val.x0) (xstar := xstar)
    (hconv := hconv) (hg := hg) (hlip := hlip) (hmin := hmin) (hdist := hdist) (g := g)
    (hgm := hgm) (p := p) (P := P) (hind := hind) (hmarg := hmarg) (hgi := hgi) (hmean := hmean)
    (hgsq := hgsq) (hvar := hvar) (hL := hL) (hR := hR) (hσ := hσ)
    (m := samples q) (J := levels q) (hm := hpos) (hJ := hJ1) (hbound := hbound)
  refine ⟨?_, xstar, hmin, ?_, ?_⟩
  · have hm : Measurable (fun seed : Unit × (ℕ → q.val.Ω) =>
          LineSearch.uOf hd he.some
            (LineSearch.champAt q.val.R (LineSearch.psiOf hd he.some q.val.x0) (samples q)
              (fun t ω => g (LineSearch.uOf hd he.some t) ω)
              (LineSearch.toBlocks (samples q) seed.2) (levels q))) :=
      (LineSearch.uOf_continuous hd he.some).measurable.comp
        ((LineSearch.measurable_champAt q.val.R (LineSearch.psiOf hd he.some q.val.x0) (samples q)
            (fun t ω => g (LineSearch.uOf hd he.some t) ω) hgm0 (levels q)).comp
          ((LineSearch.measurable_toBlocks (samples q)).comp measurable_snd))
    have heq : (fun seed : Unit × (ℕ → q.val.Ω) =>
          LineSearch.uOf hd he.some
            (LineSearch.champAt q.val.R (LineSearch.psiOf hd he.some q.val.x0) (samples q)
              (fun t ω => g (LineSearch.uOf hd he.some t) ω)
              (LineSearch.toBlocks (samples q) seed.2) (levels q))
        : Unit × (ℕ → q.val.Ω) → q.val.E)
        = fun seed : Unit × (ℕ → q.val.Ω) =>
            execute { Seed := fun _ => q.val.Ω, law := P, answer := fun _ (_, x) ω => g x ω }
              (LineSearch.ofReal (LineSearch.uOf hd he.some)
                (LineSearch.lineSearch q.val.R (LineSearch.psiOf hd he.some q.val.x0)
                  (by simp only [samples]; omega : 0 < 2 * samples q)))
              (budget q) seed.1 seed.2 := by
      funext seed
      exact ((LineSearch.execute_ofReal (LineSearch.uOf hd he.some) (P := P) (g := g)
            (K := levels q * (2 * samples q)) (sd := seed.1) (ξ := seed.2)).trans
          (congrArg (LineSearch.uOf hd he.some)
            (LineSearch.execute_champ (by simp only [samples]; omega : 0 < 2 * samples q) (P := P)
              (g := fun t ω => g (LineSearch.uOf hd he.some t) ω) (R := q.val.R)
              (x0 := LineSearch.psiOf hd he.some q.val.x0) seed.1 seed.2))).symm
    exact (congrArg Measurable heq).mp hm
  · exact hres.1
  · exact hres.2

end LongTails.Theorems.LineSearchZerothOrderConvex

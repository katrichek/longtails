import LongTails.Proofs.LineSearchPairs

open MeasureTheory Set

namespace ScratchTest

variable {Ω : Type} [MeasurableSpace Ω]

lemma test_ite {f g u v : ℕ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hu : Measurable u) (hv : Measurable v) :
    Measurable (fun i => if f i > g i then u i else v i) := by
  fun_prop

lemma test_ite2 {f g u v : ℕ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hu : Measurable u) (hv : Measurable v) :
    Measurable (fun i => if min (f i) (g i) < 1 then u i else v i) := by
  fun_prop

end ScratchTest

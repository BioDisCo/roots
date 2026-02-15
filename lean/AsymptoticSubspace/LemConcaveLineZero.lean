-- TeX label: lem:concave:line:zero
-- For a concave nonneg function r on [a,c], the zero line through (b, r(b))
-- lies above r on [a,b] and below r on [b,c].

import AsymptoticSubspace.PaperFormalizationCore

noncomputable section

namespace AsymptoticSubspace

open PaperFormalization

theorem lemma_concave_line_zero
    {a b c : ℝ} (hab : a < b) (hbc : b < c) {r : ℝ → ℝ}
    (hconc : ConcaveOn ℝ (Set.Icc a c) r)
    (hnonneg : ∀ x ∈ Set.Icc a c, 0 ≤ r x) :
    let g := zeroLine b c (r b)
    (∀ ξ ∈ Set.Icc a b, g ξ ≥ r ξ) ∧ (∀ ξ ∈ Set.Icc b c, g ξ ≤ r ξ) :=
  lemma_concave_line_zero_complete hab hbc hconc hnonneg

end AsymptoticSubspace

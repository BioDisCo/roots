-- TeX label: lem:concave:line
-- For a concave function r on [a,c], the secant line through (b, r(b)) and (c, r(c))
-- lies above r on [a,b] and below r on [b,c].

import AsymptoticSubspace.PaperFormalizationCore

noncomputable section

namespace AsymptoticSubspace

open PaperFormalization

theorem lemma_concave_line
    {a b c : ℝ} (hab : a < b) (hbc : b < c) {r : ℝ → ℝ}
    (hconc : ConcaveOn ℝ (Set.Icc a c) r) :
    let f := secantLine b c (r b) (r c)
    (∀ ξ ∈ Set.Icc a b, f ξ ≥ r ξ) ∧ (∀ ξ ∈ Set.Icc b c, f ξ ≤ r ξ) :=
  lemma_concave_line_complete hab hbc hconc

end AsymptoticSubspace

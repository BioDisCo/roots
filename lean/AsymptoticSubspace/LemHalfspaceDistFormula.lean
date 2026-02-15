-- TeX label: lem:halfspace:distance:formula
-- The distance from a point z to an open half-space {h | ⟨h - q, v⟩ < 0} equals ⟨z - q, v⟩ / ‖v‖.

import AsymptoticSubspace.PaperFormalizationCore

noncomputable section

namespace AsymptoticSubspace

open PaperFormalization

theorem lemma_halfspace_dist
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {q v z : V} (hv : v ≠ 0)
    (hz : z ∉ {h : V | @inner ℝ V _ (h - q) v < 0}) :
    Metric.infDist z {h : V | @inner ℝ V _ (h - q) v < 0}
      = @inner ℝ V _ (z - q) v / ‖v‖ :=
  lemma_halfspace_distance_formula hv hz

end AsymptoticSubspace

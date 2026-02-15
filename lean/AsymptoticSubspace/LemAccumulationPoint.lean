-- TeX label: lem:accumulation_point
-- A sequence of orthogonal projections has a convergent subsequence
-- whose limit is also an orthogonal projection.

import AsymptoticSubspace.PaperFormalizationCore

noncomputable section

namespace AsymptoticSubspace

open PaperFormalization

theorem lemma_accumulation_point_paper
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (PiSeq : ℕ → V →L[ℝ] V)
    (hPi : ∀ t, IsStarProjection (PiSeq t)) :
    ∃ P : V →L[ℝ] V, IsStarProjection P ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Filter.Tendsto (PiSeq ∘ φ) Filter.atTop (nhds P) :=
  lemma_accumulation_point PiSeq hPi

end AsymptoticSubspace

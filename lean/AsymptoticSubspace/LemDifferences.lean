-- TeX label: lem:differences
-- Differences of process outputs decompose into parallel and residual components.

import AsymptoticSubspace.ModelBridgeCore

noncomputable section

namespace AsymptoticSubspace

open ComputationalModel ModelLemmas PaperFormalization

theorem lemma_differences
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {n : Nat}
    (E : AveragingExecution (V := V) n)
    (M : Round → Finset (Proc n))
    (α : ℝ) (t : Round) (i j : Proc n)
    (hxi :
      ∃ ξi ∈ PolyOn E t (M (t + 1)),
        ∃ ξi' ∈ Poly E t,
          E.outputs (t + 1) i = α • ξi + (1 - α) • ξi')
    (hxj :
      ∃ ξj ∈ PolyOn E t (M (t + 1)),
        ∃ ξj' ∈ Poly E t,
          E.outputs (t + 1) j = α • ξj + (1 - α) • ξj') :
    ∃ uParallel ∈ diffSet (PolyOn E t (M (t + 1))),
      ∃ uRes ∈ diffSet (Poly E t),
        E.outputs (t + 1) i - E.outputs (t + 1) j
          = α • uParallel + (1 - α) • uRes :=
  lemma_differences_model E M α t i j hxi hxj

end AsymptoticSubspace

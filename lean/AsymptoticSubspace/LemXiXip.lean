-- TeX label: lem:xi_xip
-- Decomposition of process outputs into a convex combination of a broadcasting-set
-- component and a residual component.

import AsymptoticSubspace.ModelBridgeCore

noncomputable section

namespace AsymptoticSubspace

open ComputationalModel ModelLemmas

theorem lemma_xi_xip
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {n : Nat}
    (E : AveragingExecution (V := V) n)
    (M : Round → Finset (Proc n))
    (α : ℝ) (t : Round) (i : Proc n)
    (hα_pos : 0 < α)
    (hmbw : MinimumBroadcastWeight (V := V) E M α) :
    ∃ ξ ∈ PolyOn E t (M (t + 1)),
      ∃ ξ' ∈ Poly E t,
        E.outputs (t + 1) i = α • ξ + (1 - α) • ξ' :=
  lemma_xi_xip_model E M α t i hα_pos hmbw

end AsymptoticSubspace

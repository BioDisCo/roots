-- TeX label: lem:halfspace:zone
-- If X(t) ∩ H = ∅ for an open half-space H, then
-- dist(X(t+1), H) ≥ α * dist(P_{M(t+1)}(t), H).

import AsymptoticSubspace.HalfspaceZoneProofCore

noncomputable section

namespace AsymptoticSubspace

open ComputationalModel ModelLemmas

theorem lemma_halfspace_zone_paper
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {n : Nat}
    (E : AveragingExecution (V := V) n)
    (M : Round → Finset (Proc n))
    (α : ℝ) (t : Round)
    (q v : V)
    (hα_pos : 0 < α)
    (hv : v ≠ 0)
    (hmbw : MinimumBroadcastWeight (V := V) E M α)
    (hprev :
      Values E t ∩ {h : V | inner ℝ (h - q) v < 0} = ∅) :
    setDistTo (Values E (t + 1)) {h : V | inner ℝ (h - q) v < 0}
      ≥ α * setDistTo (PolyOn E t (M (t + 1))) {h : V | inner ℝ (h - q) v < 0} :=
  lemma_halfspace_zone E M α t q v hα_pos hv hmbw hprev

end AsymptoticSubspace

-- TeX label: lem:imposs
-- If the adversary is not (s+1)-rooted and dim(V) > s, then no local deterministic
-- algorithm can solve asymptotic subspace consensus.

import AsymptoticSubspace.ImpossibilityProofCore

noncomputable section

namespace AsymptoticSubspace

open ComputationalModel ModelLemmas

theorem lemma_imposs
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {n : Nat} (N : ObliviousMessageAdversary n) (s : Nat)
    (hnotRooted : ¬ IsKRootedAdversary N (s + 1))
    (hfin : s < Module.finrank ℝ V) :
    ¬ ∃ A : DeterministicAlgorithm V n, SolvesAsymptoticSubspace A N s :=
  lemma_imposs_unsolvable_full_paper
    (V := V) (n := n) N s hnotRooted hfin

end AsymptoticSubspace

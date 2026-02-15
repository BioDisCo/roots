-- TeX label: lem:continuity
-- The thickness function is Lipschitz continuous in the projection operator,
-- with Lipschitz constant equal to the pairDiameter of the point set.

import AsymptoticSubspace.ModelBridgeCore

noncomputable section

namespace AsymptoticSubspace

open ModelLemmas

theorem lemma_continuity
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (X : Finset V) (hX : X.Nonempty)
    (P Q : V →L[ℝ] V) :
    |thicknessOn P X hX - thicknessOn Q X hX|
      ≤ ‖P - Q‖ * pairDiameter X hX :=
  lemma_continuity_complete (V := V) X hX P Q

end AsymptoticSubspace

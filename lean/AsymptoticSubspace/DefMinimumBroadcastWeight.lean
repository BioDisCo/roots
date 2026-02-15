-- TeX label: minimum broadcasting weight definition.

import AsymptoticSubspace.DefComputationalModel

namespace AsymptoticSubspace

def IsBroadcastingSet
    {n : Nat} (G : CommGraph n) (M : Finset (Proc n)) : Prop :=
  ∀ i : Proc n, ∃ j : Proc n, j ∈ M ∧ G.edge j i

def MinimumBroadcastWeight
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {n : Nat}
    (E : AveragingExecution (V := V) n)
    (M : Round → Finset (Proc n))
    (α : ℝ) : Prop :=
  (∀ t : Round, IsBroadcastingSet (E.graphs t) (M t)) ∧
    (∀ t i, α ≤ Finset.sum (M t) (fun j => E.weights t i j))

section Verification

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {n : Nat}

/-- Verification anchor: local broadcasting-set definition equals core model definition. -/
@[simp] theorem isBroadcastingSet_iff
    (G : CommGraph n) (M : Finset (Proc n)) :
    IsBroadcastingSet G M ↔ ComputationalModel.IsBroadcastingSet G M :=
  Iff.rfl

/-- Verification anchor: paper definition is exactly the core model definition. -/
@[simp] theorem minimumBroadcastWeight_iff
    (E : AveragingExecution (V := V) n)
    (M : Round → Finset (Proc n))
    (α : ℝ) :
    MinimumBroadcastWeight E M α ↔ ComputationalModel.MinimumBroadcastWeight E M α :=
  Iff.rfl

end Verification

end AsymptoticSubspace

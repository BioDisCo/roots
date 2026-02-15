import AsymptoticSubspace.ThmSolvingCore

noncomputable section

namespace AsymptoticSubspace
namespace ThmSolving

open Set
open ComputationalModel
open ModelLemmas

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {n : Nat}

/--
TeX label: `thm:solving` (full model-grounded form).

For `d ≥ k ≥ 1`, every averaging execution with minimum broadcasting weight `α > 0`
and `k`-broadcastability converges onto a fixed affine subspace of dimension at most `k-1`,
and satisfies validity at limit.
-/
theorem theorem_solving [NeZero n]
    [FiniteDimensional ℝ V]
    (d k : Nat) (_hdk : k ≤ d) (hk : 1 ≤ k)
    (E : AveragingExecution (V := V) n)
    (M : Round → Finset (Proc n))
    (α : ℝ) (hα_pos : 0 < α)
    (hmbw : MinimumBroadcastWeight (V := V) E M α)
    (hcard : ∀ t, (M t).card ≤ k)
    (_hdim : Module.finrank ℝ V = d) :
    ∃ (W : AffineSubspace ℝ V),
      Module.finrank ℝ W.direction ≤ k - 1 ∧
      (∀ i : Proc n, ConvergesToSet (fun t => E.outputs t i) (W : Set V)) ∧
    (∀ i : Proc n,
      ConvergesToSet
        (fun t => E.outputs t i)
        (convexHull ℝ (Set.range (E.outputs 0)))) := by
  exact theorem_solving_core d k _hdk hk E M α hα_pos hmbw hcard _hdim

end ThmSolving
end AsymptoticSubspace

import AsymptoticSubspace.LemDeltaContractionCore

noncomputable section

namespace AsymptoticSubspace

open ComputationalModel
open ModelLemmas

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [DecidableEq V]
variable {n : Nat}

/--
TeX label: `lem:Delta-contraction`.

Paper-facing statement: existence of a projection with kernel dimension at most `k-1`
such that the induced thickness converges to `0`.
-/
theorem lemma_Delta_contraction [NeZero n]
    (k : Nat)
    (_hk : 1 ≤ k)
    (E : AveragingExecution (V := V) n)
    (M : Round → Finset (Proc n))
    (α : ℝ)
    (_hα_pos : 0 < α)
    (_hmbw : MinimumBroadcastWeight (V := V) E M α)
    (_hcard : ∀ t, (M t).card ≤ k) :
    ∃ Pi : V →L[ℝ] V,
      IsStarProjection Pi ∧
      Module.finrank ℝ (LinearMap.ker (Pi : V →ₗ[ℝ] V)) ≤ k - 1 ∧
      ConvergesTo (fun t => thicknessAt Pi E t) 0 := by
  exact lemma_Delta_contraction_core k _hk E M α _hα_pos _hmbw _hcard

end AsymptoticSubspace

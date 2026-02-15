import AsymptoticSubspace.ModelBridgeCore

noncomputable section

namespace AsymptoticSubspace

open ComputationalModel ModelLemmas MeasureTheory

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {n : Nat}

/--
TeX label: `lem:contract`.

Volume contraction per round: if `|(M (t+1))| ≤ d = finrank ℝ V`,
then the `d`-dimensional volume contracts by factor `(1 - α^d)`.

Mathlib v4.27.0 does not yet provide the Steiner-symmetrization/Brunn-Minkowski
machinery used in the paper proof, so the final contraction step is left as `sorry`.
-/
theorem lemma_contract
    [NeZero n]
    (E : AveragingExecution (V := V) n)
    (M : Round → Finset (Proc n))
    (α : ℝ)
    (t : Round)
    (hα_pos : 0 < α)
    (hα_lt_one : α < 1)
    (hmbw : MinimumBroadcastWeight (V := V) E M α)
    (hcard : (M (t + 1)).card ≤ Module.finrank ℝ V) :
    volume (Poly E (t + 1)) ≤
      ENNReal.ofReal (1 - α ^ Module.finrank ℝ V) * volume (Poly E t) := by
  /-
  Missing formal ingredients:
  1. Steiner-type symmetrization of `Poly E t` along a coordinate axis.
  2. Brunn-Minkowski-based concavity of the section-radius profile.
  3. The paper's volume integral estimate (`lem:volumes`) in a usable Mathlib form.
  4. Combination with monotonicity `Poly E (t + 1) ⊆ Poly E t`.
  -/
  sorry

end AsymptoticSubspace

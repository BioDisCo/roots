import AsymptoticSubspace.PaperFormalization
import AsymptoticSubspace.ModelLemmas

noncomputable section

namespace AsymptoticSubspace
namespace TopLevelLemmas

open Set
open PaperFormalization
open ComputationalModel
open ModelLemmas

theorem lemma_concave_line
    -- TeX label: lem:concave:line
    {a b c : ℝ} (hab : a < b) (hbc : b < c) {r : ℝ → ℝ}
    (hconc : ConcaveOn ℝ (Icc a c) r) :
    let f := secantLine b c (r b) (r c)
    (∀ ξ ∈ Icc a b, f ξ ≥ r ξ) ∧ (∀ ξ ∈ Icc b c, f ξ ≤ r ξ) :=
  lemma_concave_line_complete hab hbc hconc

theorem lemma_concave_line_zero
    -- TeX label: lem:concave:line:zero
    {a b c : ℝ} (hab : a < b) (hbc : b < c) {r : ℝ → ℝ}
    (hconc : ConcaveOn ℝ (Icc a c) r)
    (hnonneg : ∀ x ∈ Icc a c, 0 ≤ r x) :
    let g := zeroLine b c (r b)
    (∀ ξ ∈ Icc a b, g ξ ≥ r ξ) ∧ (∀ ξ ∈ Icc b c, g ξ ≤ r ξ) :=
  lemma_concave_line_zero_complete hab hbc hconc hnonneg

theorem lemma_xi_xip
    -- TeX label: lem:xi_xip
    {V : Type*} [AddCommGroup V] [Module ℝ V]
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

theorem lemma_differences
    -- TeX label: lem:differences
    {V : Type*} [AddCommGroup V] [Module ℝ V]
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

theorem lemma_imposs
    -- TeX label: lem:imposs
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {n : Nat} (N : ObliviousMessageAdversary n) (s : Nat)
    (hnotRooted : ¬ IsKRootedAdversary N (s + 1))
    (hfin : s < Module.finrank ℝ V) :
    ¬ ∃ A : DeterministicAlgorithm V n, SolvesAsymptoticSubspace A N s :=
  lemma_imposs_unsolvable_full_exact
    (V := V) (n := n) N s hnotRooted hfin

end TopLevelLemmas
end AsymptoticSubspace

import AsymptoticSubspace.ComputationalModel
import AsymptoticSubspace.PaperFormalization

noncomputable section

namespace AsymptoticSubspace
namespace ModelLemmas

open Set
open ComputationalModel
open PaperFormalization

section

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {n : Nat}

/-- Uniqueness of exact eventual limits. -/
theorem convergesExactly_unique_aux
    {V' : Type*} {x : Round → V'} {l₁ l₂ : V'}
    (h₁ : ConvergesExactly x l₁) (h₂ : ConvergesExactly x l₂) :
    l₁ = l₂ := by
  rcases h₁ with ⟨T₁, hT₁⟩
  rcases h₂ with ⟨T₂, hT₂⟩
  let T := max T₁ T₂
  have hl₁ : x T = l₁ := hT₁ T (le_max_left _ _)
  have hl₂ : x T = l₂ := hT₂ T (le_max_right _ _)
  exact hl₁.symm.trans hl₂

abbrev Values (E : AveragingExecution (V := V) n) (t : Round) : Set V :=
  Set.range (E.outputs t)

abbrev ValuesOn
    (E : AveragingExecution (V := V) n) (t : Round)
    (S : Finset (Proc n)) : Set V :=
  E.outputs t '' (S : Set (Proc n))

abbrev Poly (E : AveragingExecution (V := V) n) (t : Round) : Set V :=
  convexHull ℝ (Values E t)

abbrev PolyOn
    (E : AveragingExecution (V := V) n) (t : Round)
    (S : Finset (Proc n)) : Set V :=
  convexHull ℝ (ValuesOn E t S)

abbrev BroadcastWeight
    (E : AveragingExecution (V := V) n) (M : Round → Finset (Proc n))
    (t : Round) (i : Proc n) : ℝ :=
  Finset.sum (M (t + 1)) (fun j => E.weights (t + 1) i j)

/-- TeX label: `lem:xi_xip` (model-grounded form). -/
theorem lemma_xi_xip_model_of_decomp
    (E : AveragingExecution (V := V) n)
    (M : Round → Finset (Proc n))
    (α : ℝ) (t : Round) (i : Proc n)
    (hα_lt_one : α < 1)
    (hmbw : MinimumBroadcastWeight (V := V) E M α)
    (hw_le_one : BroadcastWeight E M t i ≤ 1)
    (hdecomp :
      ∃ ξ ∈ PolyOn E t (M (t + 1)),
        ∃ η ∈ Poly E t,
          E.outputs (t + 1) i
            = BroadcastWeight E M t i • ξ + (1 - BroadcastWeight E M t i) • η) :
    ∃ ξ ∈ PolyOn E t (M (t + 1)),
      ∃ ξ' ∈ Poly E t,
        E.outputs (t + 1) i = α • ξ + (1 - α) • ξ' := by
  rcases hdecomp with ⟨ξ, hξ, η, hη, hout⟩
  have hαw : α ≤ BroadcastWeight E M t i := hmbw.2 (t + 1) i
  have hpoly_conv : Convex ℝ (Poly E t) := convex_convexHull ℝ (Values E t)
  have hvals_subset :
      ValuesOn E t (M (t + 1)) ⊆ Values E t := by
    intro x hx
    rcases hx with ⟨j, hj, rfl⟩
    exact ⟨j, rfl⟩
  have hpolyOn_subset : PolyOn E t (M (t + 1)) ⊆ Poly E t :=
    convexHull_mono hvals_subset
  have hξ_in_poly : ξ ∈ Poly E t := hpolyOn_subset hξ
  rcases lemma_xi_xip_complete
      (P := Poly E t) hpoly_conv hα_lt_one hαw hw_le_one hξ_in_poly hη with
    ⟨ξ', hξ', hrewrite⟩
  refine ⟨ξ, hξ, ξ', hξ', ?_⟩
  calc
    E.outputs (t + 1) i
        = BroadcastWeight E M t i • ξ + (1 - BroadcastWeight E M t i) • η := hout
    _ = α • ξ + (1 - α) • ξ' := hrewrite

/-- Internal `< 1` branch used for `lem:xi_xip` (model-grounded, derived from update rule). -/
theorem lemma_xi_xip_model_lt_one
    (E : AveragingExecution (V := V) n)
    (M : Round → Finset (Proc n))
    (α : ℝ) (t : Round) (i : Proc n)
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hmbw : MinimumBroadcastWeight (V := V) E M α)
    (hwm_lt_one : BroadcastWeight E M t i < 1) :
    ∃ ξ ∈ PolyOn E t (M (t + 1)),
      ∃ ξ' ∈ Poly E t,
        E.outputs (t + 1) i = α • ξ + (1 - α) • ξ' := by
  let Mset : Finset (Proc n) := M (t + 1)
  let Rset : Finset (Proc n) := Finset.univ \ Mset
  let f : Proc n → ℝ := fun j => E.weights (t + 1) i j
  let z : Proc n → V := fun j => E.outputs t j
  let wM : ℝ := BroadcastWeight E M t i
  have hαw : α ≤ wM := hmbw.2 (t + 1) i
  have hwM_pos : 0 < wM := lt_of_lt_of_le hα_pos hαw
  let ξ : V := Mset.centerMass f z
  have hξ_mem : ξ ∈ PolyOn E t (M (t + 1)) := by
    have hw0 : ∀ j ∈ Mset, 0 ≤ f j := by
      intro j hj
      exact E.weight_nonneg (t + 1) i j
    have hz : ∀ j ∈ Mset, z j ∈ ValuesOn E t (M (t + 1)) := by
      intro j hj
      exact ⟨j, hj, rfl⟩
    simpa [PolyOn, ValuesOn, ξ, Mset, f, z] using
      (Finset.centerMass_mem_convexHull
        (R := ℝ) (E := V) (t := Mset)
        (w := f) hw0 hwM_pos (z := z) hz)
  have hMsubset : Mset ⊆ Finset.univ := by
    intro x hx
    simp
  have hwM_eq : wM = Finset.sum Mset (fun j => f j) := by
    simp [wM, BroadcastWeight, Mset, f]
  have hsumR_add :
      Finset.sum Rset (fun j => f j) + wM = 1 := by
    calc
      Finset.sum Rset (fun j => f j) + wM
          = Finset.sum (Finset.univ \ Mset) (fun j => f j) + Finset.sum Mset (fun j => f j) := by
              simp [Rset, hwM_eq]
      _ = Finset.sum Finset.univ (fun j => f j) := by
            exact (Finset.sum_sdiff (s₁ := Mset) (s₂ := Finset.univ) (f := f) hMsubset)
      _ = 1 := by
            simpa [f] using E.weights_sum_one (t + 1) i
  have hsumR_eq : Finset.sum Rset (fun j => f j) = 1 - wM := by linarith
  have hsumR_pos : 0 < Finset.sum Rset (fun j => f j) := by linarith
  let η : V := Rset.centerMass f z
  have hη_mem : η ∈ Poly E t := by
    have hw0 : ∀ j ∈ Rset, 0 ≤ f j := by
      intro j hj
      exact E.weight_nonneg (t + 1) i j
    have hz : ∀ j ∈ Rset, z j ∈ Values E t := by
      intro j hj
      exact ⟨j, rfl⟩
    simpa [Poly, Values, η, Rset, f, z] using
      (Finset.centerMass_mem_convexHull
        (R := ℝ) (E := V) (t := Rset)
        (w := f) hw0 hsumR_pos (z := z) hz)
  have hwM_smul_ξ :
      wM • ξ = Finset.sum Mset (fun j => f j • z j) := by
    have hsumM_ne : Finset.sum Mset (fun j => f j) ≠ 0 := by
      rw [← hwM_eq]
      exact ne_of_gt hwM_pos
    calc
      wM • ξ
          = wM • ((Finset.sum Mset (fun j => f j))⁻¹ •
              Finset.sum Mset (fun j => f j • z j)) := by
                rfl
      _ = (wM * (Finset.sum Mset (fun j => f j))⁻¹) •
            Finset.sum Mset (fun j => f j • z j) := by
              rw [smul_smul]
      _ = (1 : ℝ) • Finset.sum Mset (fun j => f j • z j) := by
            rw [hwM_eq, mul_inv_cancel₀ hsumM_ne]
      _ = Finset.sum Mset (fun j => f j • z j) := by
            simp
  have hsumR_smul_η :
      Finset.sum Rset (fun j => f j) • η = Finset.sum Rset (fun j => f j • z j) := by
    have hsumR_ne : Finset.sum Rset (fun j => f j) ≠ 0 := ne_of_gt hsumR_pos
    calc
      Finset.sum Rset (fun j => f j) • η
          = Finset.sum Rset (fun j => f j) •
              ((Finset.sum Rset (fun j => f j))⁻¹ •
                Finset.sum Rset (fun j => f j • z j)) := by
                  rfl
      _ = (Finset.sum Rset (fun j => f j) * (Finset.sum Rset (fun j => f j))⁻¹) •
            Finset.sum Rset (fun j => f j • z j) := by
              rw [smul_smul]
      _ = (1 : ℝ) • Finset.sum Rset (fun j => f j • z j) := by
            rw [mul_inv_cancel₀ hsumR_ne]
      _ = Finset.sum Rset (fun j => f j • z j) := by
            simp
  have hsplit_vec :
      Finset.sum Rset (fun j => f j • z j) + Finset.sum Mset (fun j => f j • z j)
        = ∑ j : Proc n, f j • z j := by
    dsimp [Rset]
    exact
      Finset.sum_sdiff
        (s₁ := Mset) (s₂ := Finset.univ) (f := fun j => f j • z j) hMsubset
  have hdecomp :
      ∃ ξ0 ∈ PolyOn E t (M (t + 1)),
        ∃ η0 ∈ Poly E t,
          E.outputs (t + 1) i
            = wM • ξ0 + (1 - wM) • η0 := by
    refine ⟨ξ, hξ_mem, η, hη_mem, ?_⟩
    calc
      E.outputs (t + 1) i
          = ∑ j : Proc n, f j • z j := by
              simpa [f, z] using E.output_succ_eq_weighted_sum t i
      _ = Finset.sum Rset (fun j => f j • z j) + Finset.sum Mset (fun j => f j • z j) := by
            simpa using hsplit_vec.symm
      _ = Finset.sum Rset (fun j => f j) • η + wM • ξ := by
            rw [← hsumR_smul_η, ← hwM_smul_ξ]
      _ = (1 - wM) • η + wM • ξ := by
            simp [hsumR_eq]
      _ = wM • ξ + (1 - wM) • η := by
            ac_rfl
  exact lemma_xi_xip_model_of_decomp E M α t i hα_lt_one hmbw (le_of_lt hwm_lt_one) hdecomp

/-- Internal `= 1` branch used for `lem:xi_xip` (no residual component needed). -/
theorem lemma_xi_xip_model_weight_eq_one
    (E : AveragingExecution (V := V) n)
    (M : Round → Finset (Proc n))
    (α : ℝ) (t : Round) (i : Proc n)
    (hwM_one : BroadcastWeight E M t i = 1) :
    ∃ ξ ∈ PolyOn E t (M (t + 1)),
      ∃ ξ' ∈ Poly E t,
        E.outputs (t + 1) i = α • ξ + (1 - α) • ξ' := by
  let Mset : Finset (Proc n) := M (t + 1)
  let Rset : Finset (Proc n) := Finset.univ \ Mset
  let f : Proc n → ℝ := fun j => E.weights (t + 1) i j
  let z : Proc n → V := fun j => E.outputs t j
  let wM : ℝ := BroadcastWeight E M t i
  have hwM_eq_one : wM = 1 := by simpa [wM] using hwM_one
  have hwM_pos : 0 < wM := by linarith [hwM_eq_one]
  let ξ : V := Mset.centerMass f z
  have hξ_mem : ξ ∈ PolyOn E t (M (t + 1)) := by
    have hw0 : ∀ j ∈ Mset, 0 ≤ f j := by
      intro j hj
      exact E.weight_nonneg (t + 1) i j
    have hz : ∀ j ∈ Mset, z j ∈ ValuesOn E t (M (t + 1)) := by
      intro j hj
      exact ⟨j, hj, rfl⟩
    simpa [PolyOn, ValuesOn, ξ, Mset, f, z] using
      (Finset.centerMass_mem_convexHull
        (R := ℝ) (E := V) (t := Mset)
        (w := f) hw0 hwM_pos (z := z) hz)
  have hvals_subset :
      ValuesOn E t (M (t + 1)) ⊆ Values E t := by
    intro x hx
    rcases hx with ⟨j, hj, rfl⟩
    exact ⟨j, rfl⟩
  have hpolyOn_subset : PolyOn E t (M (t + 1)) ⊆ Poly E t :=
    convexHull_mono hvals_subset
  have hξ_poly : ξ ∈ Poly E t := hpolyOn_subset hξ_mem
  have hMsubset : Mset ⊆ Finset.univ := by
    intro x hx
    simp
  have hwM_eq : wM = Finset.sum Mset (fun j => f j) := by
    simp [wM, BroadcastWeight, Mset, f]
  have hsumR_add :
      Finset.sum Rset (fun j => f j) + wM = 1 := by
    calc
      Finset.sum Rset (fun j => f j) + wM
          = Finset.sum (Finset.univ \ Mset) (fun j => f j) + Finset.sum Mset (fun j => f j) := by
              simp [Rset, hwM_eq]
      _ = Finset.sum Finset.univ (fun j => f j) := by
            exact (Finset.sum_sdiff (s₁ := Mset) (s₂ := Finset.univ) (f := f) hMsubset)
      _ = 1 := by
            simpa [f] using E.weights_sum_one (t + 1) i
  have hsumR_eq_zero : Finset.sum Rset (fun j => f j) = 0 := by
    linarith [hsumR_add, hwM_eq_one]
  have hR_nonneg : ∀ j ∈ Rset, 0 ≤ f j := by
    intro j hj
    exact E.weight_nonneg (t + 1) i j
  have hR_zero : ∀ j ∈ Rset, f j = 0 := by
    intro j hj
    apply le_antisymm
    · have hjle : f j ≤ Finset.sum Rset (fun k => f k) :=
        Finset.single_le_sum (fun k hk => hR_nonneg k hk) hj
      simpa [hsumR_eq_zero] using hjle
    · exact hR_nonneg j hj
  have hsumR_vec_zero : Finset.sum Rset (fun j => f j • z j) = 0 := by
    exact Finset.sum_eq_zero (fun j hj => by simp [hR_zero j hj])
  have hwM_smul_ξ :
      wM • ξ = Finset.sum Mset (fun j => f j • z j) := by
    have hsumM_ne : Finset.sum Mset (fun j => f j) ≠ 0 := by
      rw [← hwM_eq]
      exact ne_of_gt hwM_pos
    calc
      wM • ξ
          = wM • ((Finset.sum Mset (fun j => f j))⁻¹ •
              Finset.sum Mset (fun j => f j • z j)) := by
                rfl
      _ = (wM * (Finset.sum Mset (fun j => f j))⁻¹) •
            Finset.sum Mset (fun j => f j • z j) := by
              rw [smul_smul]
      _ = (1 : ℝ) • Finset.sum Mset (fun j => f j • z j) := by
            rw [hwM_eq, mul_inv_cancel₀ hsumM_ne]
      _ = Finset.sum Mset (fun j => f j • z j) := by
            simp
  have hsplit_vec :
      Finset.sum Rset (fun j => f j • z j) + Finset.sum Mset (fun j => f j • z j)
        = ∑ j : Proc n, f j • z j := by
    dsimp [Rset]
    exact
      Finset.sum_sdiff
        (s₁ := Mset) (s₂ := Finset.univ) (f := fun j => f j • z j) hMsubset
  have hout_eq_ξ : E.outputs (t + 1) i = ξ := by
    calc
      E.outputs (t + 1) i
          = ∑ j : Proc n, f j • z j := by
              simpa [f, z] using E.output_succ_eq_weighted_sum t i
      _ = Finset.sum Rset (fun j => f j • z j) + Finset.sum Mset (fun j => f j • z j) := by
            simpa using hsplit_vec.symm
      _ = 0 + Finset.sum Mset (fun j => f j • z j) := by simp [hsumR_vec_zero]
      _ = Finset.sum Mset (fun j => f j • z j) := by simp
      _ = wM • ξ := by simpa using hwM_smul_ξ.symm
      _ = ξ := by simp [hwM_eq_one]
  refine ⟨ξ, hξ_mem, ξ, hξ_poly, ?_⟩
  calc
    E.outputs (t + 1) i = ξ := hout_eq_ξ
    _ = α • ξ + (1 - α) • ξ := by
          calc
            ξ = (1 : ℝ) • ξ := by simp
            _ = (α + (1 - α)) • ξ := by ring_nf
            _ = α • ξ + (1 - α) • ξ := by rw [add_smul]

/-- TeX label: `lem:xi_xip` (model-grounded, derived from update rule). -/
theorem lemma_xi_xip_model
    (E : AveragingExecution (V := V) n)
    (M : Round → Finset (Proc n))
    (α : ℝ) (t : Round) (i : Proc n)
    (hα_pos : 0 < α)
    (hmbw : MinimumBroadcastWeight (V := V) E M α) :
    ∃ ξ ∈ PolyOn E t (M (t + 1)),
      ∃ ξ' ∈ Poly E t,
        E.outputs (t + 1) i = α • ξ + (1 - α) • ξ' := by
  let Mset : Finset (Proc n) := M (t + 1)
  let f : Proc n → ℝ := fun j => E.weights (t + 1) i j
  have hMsubset : Mset ⊆ Finset.univ := by
    intro x hx
    simp
  have hwM_le_one : BroadcastWeight E M t i ≤ 1 := by
    calc
      BroadcastWeight E M t i
          = Finset.sum Mset (fun j => f j) := by
              simp [BroadcastWeight, Mset, f]
      _ ≤ Finset.sum Finset.univ (fun j => f j) := by
            exact Finset.sum_le_sum_of_subset_of_nonneg hMsubset
              (fun j hjU hjM => E.weight_nonneg (t + 1) i j)
      _ = 1 := by
            simpa [f] using E.weights_sum_one (t + 1) i
  by_cases hwM_one : BroadcastWeight E M t i = 1
  · exact lemma_xi_xip_model_weight_eq_one E M α t i hwM_one
  · have hwm_lt_one : BroadcastWeight E M t i < 1 :=
      lt_of_le_of_ne hwM_le_one hwM_one
    have hαw : α ≤ BroadcastWeight E M t i := hmbw.2 (t + 1) i
    have hα_lt_one : α < 1 := lt_of_le_of_lt hαw hwm_lt_one
    exact lemma_xi_xip_model_lt_one E M α t i hα_pos hα_lt_one hmbw hwm_lt_one

/-- TeX label: `lem:differences` (model-grounded form). -/
theorem lemma_differences_model
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
          = α • uParallel + (1 - α) • uRes := by
  rcases hxi with ⟨ξi, hξi, ξi', hξi', hEi⟩
  rcases hxj with ⟨ξj, hξj, ξj', hξj', hEj⟩
  simpa using
    (lemma_differences_complete
      (S := PolyOn E t (M (t + 1)))
      (P := Poly E t)
      (α := α)
      (xᵢ := E.outputs (t + 1) i)
      (xⱼ := E.outputs (t + 1) j)
      (ξᵢ := ξi) (ξⱼ := ξj)
      (ηᵢ := ξi') (ηⱼ := ξj')
      hEi hEj hξi hξj hξi' hξj')

section ImpossibilityModel

variable (N : ObliviousMessageAdversary n)
variable (s : Nat)

/--
Static-counterexample witness used in the paper proof of `lem:imposs`.
It packages:
- one graph from the adversary that is not `(s+1)`-rooted,
- `s+2` distinguished processes (`roots`),
- initial/limit values where validity pins limits to initials on these roots,
- affine independence of those initial values.
-/
structure ImpossibilityWitness where
  graph : CommGraph n
  graph_in_adversary : graph ∈ N.graphs
  graph_not_k_rooted : ¬ IsKRooted graph (s + 1)
  roots : Finset (Proc n)
  roots_card : roots.card = s + 2
  init : Proc n → V
  limits : Proc n → V
  affine_independent_init : AffineIndependent ℝ (fun p : roots => init p)
  validity_on_roots : ∀ i : Proc n, i ∈ roots → limits i = init i

/-- Subspace-agreement restricted to the distinguished root processes. -/
def SubspaceAgreementOn
    (roots : Finset (Proc n)) (limits : Proc n → V) : Prop :=
  ∃ E : AffineSubspace ℝ V,
    FiniteDimensional ℝ E.direction ∧
    Module.finrank ℝ E.direction ≤ s ∧
    (∀ i : Proc n, i ∈ roots → limits i ∈ (E : Set V))

/--
Abstract problem-level spec (restricted model):
the algorithm solves `d`-to-`s` asymptotic subspace consensus in `N` if every admissible
counterexample-shaped execution witness satisfies subspace agreement.
-/
def Solves_d_to_s : Prop :=
  ∀ w : ImpossibilityWitness (V := V) (n := n) N s,
    SubspaceAgreementOn (V := V) (n := n) s w.roots w.limits

/--
Bridge assumption from full algorithm semantics to the witness model:
any algorithm solving the full spec would induce witness-level agreement.
-/
def FullToWitnessReduction : Prop :=
  (∃ A : DeterministicAlgorithm V n, SolvesAsymptoticSubspace A N s) →
    Solves_d_to_s (V := V) (n := n) N s

/-- Witness `w` is realizable by algorithm `A` on some admissible trace from `w.init`. -/
def RealizableWitnessBy (A : DeterministicAlgorithm V n)
    (w : ImpossibilityWitness (V := V) (n := n) N s) : Prop :=
  ∃ Gseq : Round → CommGraph n,
    AdmissibleTrace N Gseq ∧
    (∀ i : Proc n,
      ConvergesExactly (fun t => (A.run Gseq w.init t) i) (w.limits i))

/--
Concrete bridge: from full solver semantics and a realizable witness run,
derive witness-level subspace agreement on `w.limits`.
-/
theorem agreement_on_realizable_witness
    (A : DeterministicAlgorithm V n)
    (hA : SolvesAsymptoticSubspace A N s)
    (w : ImpossibilityWitness (V := V) (n := n) N s)
    (hreal : RealizableWitnessBy (V := V) (n := n) N s A w) :
    SubspaceAgreementOn (V := V) (n := n) s w.roots w.limits := by
  rcases hreal with ⟨Gseq, hAdm, hConvW⟩
  rcases hA Gseq w.init hAdm with ⟨limitsA, hConvA, hValA, hAgrA⟩
  rcases hAgrA with ⟨E, hfdE, hdimE, hmemE⟩
  refine ⟨E, hfdE, hdimE, ?_⟩
  intro i hi
  have hEq : limitsA i = w.limits i := by
    exact convergesExactly_unique_aux (hConvA i) (hConvW i)
  have hmem : limitsA i ∈ (E : Set V) := hmemE i
  simpa [hEq] using hmem

/-- A witness-extraction assumption from the graph-theoretic side. -/
def HasImpossibilityWitness : Prop :=
  Nonempty (ImpossibilityWitness (V := V) (n := n) N s)

/-- Canonical existence of `s+2` distinct processes when `s+2 ≤ n`. -/
theorem exists_roots_of_two_add_le (hsize : s + 2 ≤ n) :
    ∃ roots : Finset (Proc n), roots.card = s + 2 := by
  refine ⟨(Finset.univ : Finset (Fin (s + 2))).map (Fin.castLEEmb hsize), ?_⟩
  simp

/-- If an adversary is not `(s+1)`-rooted, then necessarily `s+2 ≤ n`. -/
theorem two_add_le_of_not_kRootedAdversary
    (hnotRooted : ¬ IsKRootedAdversary N (s + 1)) :
    s + 2 ≤ n := by
  by_contra hsize
  have hn : n ≤ s + 1 := by omega
  apply hnotRooted
  intro G hG
  refine ⟨Finset.univ, ?_, ?_⟩
  · simpa [Proc] using hn
  · intro i
    refine ⟨i, by simp, ?_⟩
    exact Relation.ReflTransGen.refl

/--
If `V` has affine dimension `s+1`, then for any `s+2` processes we can choose initial values
whose restriction to those processes is affinely independent.
-/
theorem exists_init_affineIndependent_of_finrank_eq
    (hfin : Module.finrank ℝ V = s + 1)
    (roots : Finset (Proc n)) (hcard : roots.card = s + 2) :
    ∃ init : Proc n → V, AffineIndependent ℝ (fun p : roots => init p) := by
  have hfin_succ : Module.finrank ℝ V = Nat.succ s := by simpa [Nat.succ_eq_add_one] using hfin
  letI : FiniteDimensional ℝ V := FiniteDimensional.of_finrank_eq_succ hfin_succ
  have hcardRoots : Fintype.card roots = Module.finrank ℝ V + 1 := by
    calc
      Fintype.card roots = roots.card := by simp
      _ = s + 2 := hcard
      _ = Module.finrank ℝ V + 1 := by omega
  rcases
      (AffineBasis.exists_affineBasis_of_finiteDimensional
        (k := ℝ) (V := V) (P := V) (ι := roots) hcardRoots) with
    ⟨b⟩
  let init : Proc n → V := fun i =>
    if hi : i ∈ roots then b ⟨i, hi⟩ else 0
  refine ⟨init, ?_⟩
  have hinit : (fun p : roots => init p) = fun p : roots => b p := by
    funext p
    simp [init, p.property]
  simpa [hinit] using b.ind

/--
Generalized version: if `Module.finrank ℝ V > s`, then one can realize `s+2` affinely
independent initial values on any `s+2` distinguished processes.
-/
theorem exists_init_affineIndependent_of_finrank_gt
    (hfin : s < Module.finrank ℝ V)
    (roots : Finset (Proc n)) (hcard : roots.card = s + 2) :
    ∃ init : Proc n → V, AffineIndependent ℝ (fun p : roots => init p) := by
  have hpos : 0 < Module.finrank ℝ V := lt_of_le_of_lt (Nat.zero_le s) hfin
  letI : FiniteDimensional ℝ V := FiniteDimensional.of_finrank_pos hpos
  let m : Nat := Module.finrank ℝ V + 1
  have hm : s + 2 ≤ m := by
    dsimp [m]
    omega
  have hcardFin : Fintype.card (Fin m) = Module.finrank ℝ V + 1 := by
    simp [m]
  rcases
      (AffineBasis.exists_affineBasis_of_finiteDimensional
        (k := ℝ) (V := V) (P := V) (ι := Fin m) hcardFin) with
    ⟨b⟩
  let emb : Fin (s + 2) ↪ Fin m := Fin.castLEEmb hm
  let pstd : Fin (s + 2) → V := fun j => b (emb j)
  have hpstd : AffineIndependent ℝ pstd := by
    simpa [pstd] using b.ind.comp_embedding emb
  have hcardRoots : Fintype.card roots = s + 2 := by
    simpa using hcard
  have hcardRootsFin : Fintype.card roots = Fintype.card (Fin (s + 2)) := by
    simpa using hcardRoots
  let eRoots : roots ≃ Fin (s + 2) := Fintype.equivOfCardEq hcardRootsFin
  let init : Proc n → V := fun i =>
    if hi : i ∈ roots then pstd (eRoots ⟨i, hi⟩) else 0
  refine ⟨init, ?_⟩
  have hinit : (fun p : roots => init p) = fun p : roots => pstd (eRoots p) := by
    funext p
    simp [init, p.property]
  have hAffOn : AffineIndependent ℝ (fun p : roots => pstd (eRoots p)) := by
    exact (affineIndependent_equiv eRoots).2 hpstd
  simpa [hinit] using hAffOn

/--
Model-grounded impossibility core:
for a static non-`(s+1)`-rooted witness execution where validity fixes root limits to root initials,
subspace agreement on those roots yields contradiction.
-/
theorem lemma_imposs_model
    (w : ImpossibilityWitness (V := V) (n := n) N s)
    (hagreement : SubspaceAgreementOn (V := V) (n := n) s w.roots w.limits) :
    False := by
  rcases hagreement with ⟨E, hfdE, hdimE, hlimE⟩
  have hcard : Fintype.card w.roots = s + 2 := by
    simpa using w.roots_card
  have hsubset :
      Set.range (fun p : w.roots => w.init p) ⊆ (E : Set V) := by
    intro x hx
    rcases hx with ⟨p, rfl⟩
    have hlim_mem : w.limits p ∈ (E : Set V) := hlimE p p.property
    have hvalid : w.limits p = w.init p := w.validity_on_roots p p.property
    simpa [hvalid] using hlim_mem
  have hcontra :=
    lemma_imposs_complete
      (xLim := fun p : w.roots => w.init p)
      hcard
      w.affine_independent_init
  exact hcontra ⟨E, hfdE, hdimE, hsubset⟩

/--
If a counterexample witness exists, then no algorithm can satisfy the `Solves_d_to_s`
specification in this model.
-/
theorem not_solves_of_hasWitness
    (hw : HasImpossibilityWitness (V := V) (n := n) N s) :
    ¬ Solves_d_to_s (V := V) (n := n) N s := by
  intro hsolve
  rcases hw with ⟨w⟩
  exact lemma_imposs_model (V := V) (n := n) N s w (hsolve w)

/--
Model-grounded unsolvability form of `lem:imposs`:
from a non-`(s+1)`-rooted adversary plus witness extraction,
`d`-to-`s` asymptotic subspace consensus is unsolvable.
-/
theorem lemma_imposs_unsolvable
    (hnotRooted : ¬ IsKRootedAdversary N (s + 1))
    (hextract :
      ¬ IsKRootedAdversary N (s + 1) →
        HasImpossibilityWitness (V := V) (n := n) N s) :
    ¬ Solves_d_to_s (V := V) (n := n) N s := by
  exact not_solves_of_hasWitness (V := V) (n := n) N s (hextract hnotRooted)

/--
Concrete unsolvability form removing the abstract extraction function:
it assumes only enough process/geometry richness to build the paper's static witness.
-/
theorem lemma_imposs_unsolvable_concrete
    (hnotRooted : ¬ IsKRootedAdversary N (s + 1))
    (hsize : s + 2 ≤ n)
    (hgeom :
      ∀ roots : Finset (Proc n), roots.card = s + 2 →
        ∃ init : Proc n → V, AffineIndependent ℝ (fun p : roots => init p)) :
    ¬ Solves_d_to_s (V := V) (n := n) N s := by
  have hbadGraph : ∃ G : CommGraph n, G ∈ N.graphs ∧ ¬ IsKRooted G (s + 1) := by
    by_contra hno
    apply hnotRooted
    intro G hG
    by_contra hGbad
    exact hno ⟨G, hG, hGbad⟩
  rcases hbadGraph with ⟨G, hGin, hGnot⟩
  rcases exists_roots_of_two_add_le (n := n) (s := s) hsize with
    ⟨roots, hrootsCard⟩
  rcases hgeom roots hrootsCard with ⟨init, hAff⟩
  let w : ImpossibilityWitness (V := V) (n := n) N s :=
    { graph := G
      graph_in_adversary := hGin
      graph_not_k_rooted := hGnot
      roots := roots
      roots_card := hrootsCard
      init := init
      limits := init
      affine_independent_init := hAff
      validity_on_roots := by
        intro i hi
        rfl }
  exact not_solves_of_hasWitness (V := V) (n := n) N s ⟨w⟩

/-- Same as `lemma_imposs_unsolvable_concrete`, with root-set existence discharged by `s+2 ≤ n`. -/
theorem lemma_imposs_unsolvable_from_size
    (hnotRooted : ¬ IsKRootedAdversary N (s + 1))
    (hsize : s + 2 ≤ n)
    (hgeom :
      ∀ roots : Finset (Proc n), roots.card = s + 2 →
        ∃ init : Proc n → V, AffineIndependent ℝ (fun p : roots => init p)) :
    ¬ Solves_d_to_s (V := V) (n := n) N s :=
  lemma_imposs_unsolvable_concrete (V := V) (n := n) N s hnotRooted hsize hgeom

/--
Dimension-driven unsolvability form: no separate geometric witness assumption is needed when
`Module.finrank ℝ V = s+1`.
-/
theorem lemma_imposs_unsolvable_finrank
    (hnotRooted : ¬ IsKRootedAdversary N (s + 1))
    (hsize : s + 2 ≤ n)
    (hfin : Module.finrank ℝ V = s + 1) :
    ¬ Solves_d_to_s (V := V) (n := n) N s := by
  apply lemma_imposs_unsolvable_from_size (V := V) (n := n) N s hnotRooted hsize
  intro roots hcard
  exact exists_init_affineIndependent_of_finrank_eq (V := V) (n := n) (s := s)
    hfin roots hcard

/--
Final model-grounded lower-bound form:
if the adversary is not `(s+1)`-rooted and `dim(V) > s`, then `d`-to-`s` solving is impossible.
-/
theorem lemma_imposs_unsolvable_final
    (hnotRooted : ¬ IsKRootedAdversary N (s + 1))
    (hfin : s < Module.finrank ℝ V) :
    ¬ Solves_d_to_s (V := V) (n := n) N s := by
  have hsize : s + 2 ≤ n := two_add_le_of_not_kRootedAdversary (N := N) (s := s) hnotRooted
  apply lemma_imposs_unsolvable_from_size (V := V) (n := n) N s hnotRooted hsize
  intro roots hcard
  exact exists_init_affineIndependent_of_finrank_gt (V := V) (n := n) (s := s)
    hfin roots hcard

/--
Full execution-semantics unsolvability (algorithm quantification),
obtained by reducing full semantics to the witness model.
-/
theorem lemma_imposs_unsolvable_full
    (hnotRooted : ¬ IsKRootedAdversary N (s + 1))
    (hfin : s < Module.finrank ℝ V)
    (hreduce : FullToWitnessReduction (V := V) (n := n) N s) :
    ¬ ∃ A : DeterministicAlgorithm V n, SolvesAsymptoticSubspace A N s := by
  intro hA
  have hwitnessSolve : Solves_d_to_s (V := V) (n := n) N s := hreduce hA
  exact lemma_imposs_unsolvable_final (V := V) (n := n) N s hnotRooted hfin hwitnessSolve

/--
Full unsolvability with concrete bridge:
from each purported solver we can extract one realizable impossibility witness.
-/
theorem lemma_imposs_unsolvable_full_concrete
    (hnotRooted : ¬ IsKRootedAdversary N (s + 1))
    (hfin : s < Module.finrank ℝ V)
    (hextract :
      ¬ IsKRootedAdversary N (s + 1) →
      s < Module.finrank ℝ V →
      ∀ A : DeterministicAlgorithm V n, SolvesAsymptoticSubspace A N s →
        ∃ w : ImpossibilityWitness (V := V) (n := n) N s,
          RealizableWitnessBy (V := V) (n := n) N s A w) :
    ¬ ∃ A : DeterministicAlgorithm V n, SolvesAsymptoticSubspace A N s := by
  intro hAex
  rcases hAex with ⟨A, hA⟩
  rcases hextract hnotRooted hfin A hA with ⟨w, hreal⟩
  have hagr : SubspaceAgreementOn (V := V) (n := n) s w.roots w.limits :=
    agreement_on_realizable_witness (V := V) (n := n) N s A hA w hreal
  exact lemma_imposs_model (V := V) (n := n) N s w hagr

end ImpossibilityModel

end

end ModelLemmas
end AsymptoticSubspace

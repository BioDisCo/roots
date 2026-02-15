-- Internal plumbing module.
-- Reader-facing statement is in `LemDeltaContraction.lean`.
import AsymptoticSubspace.ModelBridgeCore

noncomputable section

namespace AsymptoticSubspace

open ComputationalModel
open ModelLemmas
open PaperFormalization

section PartOne

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [DecidableEq V]
variable {n : Nat}

abbrev outputSet (E : AveragingExecution (V := V) n) (t : Round) : Finset V :=
  Finset.univ.image (E.outputs t)

/-- Thickness at round `t`, defaulting to `0` when the output set is empty. -/
def thicknessAt
    (P : V →L[ℝ] V)
    (E : AveragingExecution (V := V) n)
    (t : Round) : ℝ :=
  if hX : (outputSet E t).Nonempty then
    thicknessOn P (outputSet E t) hX
  else
    0

/-- Part 1 helper: pairwise bounds imply a thickness bound at the next round. -/
lemma one_step_pair_bound_implies_thickness
    (E : AveragingExecution (V := V) n)
    (P : V →L[ℝ] V)
    (t : Round)
    (c : ℝ)
    (hXnext : (outputSet E (t + 1)).Nonempty)
    (hpair :
      ∀ i j : Proc n,
        ‖P (E.outputs (t + 1) i - E.outputs (t + 1) j)‖ ≤ c) :
    thicknessOn P (outputSet E (t + 1)) hXnext ≤ c := by
  have hprod : (outputSet E (t + 1)).product (outputSet E (t + 1)) |>.Nonempty := by
    rcases hXnext with ⟨x, hx⟩
    exact ⟨(x, x), by simp [hx]⟩
  refine Finset.sup'_le (H := hprod) (f := fun p : V × V => ‖P (p.1 - p.2)‖) ?_
  intro p hp
  rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
  rcases Finset.mem_image.mp hp1 with ⟨i, _hiU, hi⟩
  rcases Finset.mem_image.mp hp2 with ⟨j, _hjU, hj⟩
  simpa [hi, hj] using hpair i j

/--
Part 1 (one-step contraction), reduced to projection-geometry side conditions.
-/
lemma one_step_contraction
    (E : AveragingExecution (V := V) n)
    (M : Round → Finset (Proc n))
    (α : ℝ)
    (P : V →L[ℝ] V)
    (t : Round)
    (hα_pos : 0 < α)
    (hα_le_one : α ≤ 1)
    (hmbw : MinimumBroadcastWeight (V := V) E M α)
    (hXnext : (outputSet E (t + 1)).Nonempty)
    (hXt : (outputSet E t).Nonempty)
    (hparallel_zero :
      ∀ u ∈ diffSet (PolyOn E t (M (t + 1))), P u = 0)
    (hres_bound :
      ∀ u ∈ diffSet (Poly E t),
        ‖P u‖ ≤ thicknessOn P (outputSet E t) hXt) :
    thicknessOn P (outputSet E (t + 1)) hXnext
      ≤ (1 - α) * thicknessOn P (outputSet E t) hXt := by
  have hdecomp :
      ∀ i j : Proc n,
        ∃ uParallel ∈ diffSet (PolyOn E t (M (t + 1))),
          ∃ uRes ∈ diffSet (Poly E t),
            E.outputs (t + 1) i - E.outputs (t + 1) j
              = α • uParallel + (1 - α) • uRes := by
    intro i j
    have hxi := lemma_xi_xip_model E M α t i hα_pos hmbw
    have hxj := lemma_xi_xip_model E M α t j hα_pos hmbw
    simpa using lemma_differences_model E M α t i j hxi hxj
  refine one_step_pair_bound_implies_thickness (E := E) (P := P) (t := t)
    (c := (1 - α) * thicknessOn P (outputSet E t) hXt) hXnext ?_
  intro i j
  rcases hdecomp i j with ⟨uParallel, huParallel, uRes, huRes, hEq⟩
  have hmap :
      P (E.outputs (t + 1) i - E.outputs (t + 1) j)
        = α • P uParallel + (1 - α) • P uRes := by
    calc
      P (E.outputs (t + 1) i - E.outputs (t + 1) j)
          = P (α • uParallel + (1 - α) • uRes) := by simp [hEq]
      _ = α • P uParallel + (1 - α) • P uRes := by simp
  have hzero : P uParallel = 0 := hparallel_zero uParallel huParallel
  have hres : ‖P uRes‖ ≤ thicknessOn P (outputSet E t) hXt := hres_bound uRes huRes
  have hmul : |1 - α| * ‖P uRes‖ ≤ |1 - α| * thicknessOn P (outputSet E t) hXt := by
    gcongr
  calc
    ‖P (E.outputs (t + 1) i - E.outputs (t + 1) j)‖
        = ‖α • P uParallel + (1 - α) • P uRes‖ := by simp [hmap]
    _ = ‖(1 - α) • P uRes‖ := by simp [hzero]
    _ = |1 - α| * ‖P uRes‖ := by simp [norm_smul]
    _ ≤ |1 - α| * thicknessOn P (outputSet E t) hXt := hmul
    _ = (1 - α) * thicknessOn P (outputSet E t) hXt := by
          simp [abs_of_nonneg (sub_nonneg.mpr hα_le_one)]

end PartOne

section PartTwo

/--
Part 2 (analysis): perturbed geometric recursion converges to `0`.

This is the pure-analysis step used by the Delta-contraction assembly.
-/
lemma perturbed_geometric_convergesTo_zero
    (a eps : ℕ → ℝ) (α : ℝ)
    (hα : 0 < α ∧ α < 1)
    (ha_nonneg : ∀ i, 0 ≤ a i)
    (hrec : ∀ i, a (i + 1) ≤ (1 - α) * a i + eps i)
    (heps : ConvergesTo eps 0) :
    ConvergesTo a 0 := by
  rcases hα with ⟨hα_pos, hα_lt_one⟩
  let r : ℝ := 1 - α
  have hr_pos : 0 < r := by
    dsimp [r]
    linarith
  have hr_nonneg : 0 ≤ r := le_of_lt hr_pos
  have hr_lt_one : r < 1 := by
    dsimp [r]
    linarith
  intro ε hε_pos
  have hε_half_pos : 0 < ε / 2 := by linarith
  have hδ_pos : 0 < α * (ε / 2) := by positivity
  rcases heps (α * (ε / 2)) hδ_pos with ⟨T1, hT1⟩
  let M : ℝ := max (a T1) (ε / 2)
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact le_max_of_le_right (le_of_lt hε_half_pos)
  have hM_pos : 0 < M := by
    dsimp [M]
    exact lt_of_lt_of_le hε_half_pos (le_max_right _ _)
  have hbound :
      ∀ k : ℕ, a (T1 + k) ≤ r ^ k * M + ε / 2 := by
    intro k
    induction k with
    | zero =>
      calc
        a (T1 + 0) = a T1 := by simp
        _ ≤ M := by
          dsimp [M]
          exact le_max_left _ _
        _ ≤ r ^ 0 * M + ε / 2 := by
          simp [hε_half_pos.le]
    | succ k ih =>
      have heps_le : eps (T1 + k) ≤ α * (ε / 2) := by
        have habs_lt : |eps (T1 + k)| < α * (ε / 2) := by
          simpa [Real.norm_eq_abs] using hT1 (T1 + k) (Nat.le_add_right T1 k)
        have heps_lt : eps (T1 + k) < α * (ε / 2) := by
          exact lt_of_le_of_lt (le_abs_self (eps (T1 + k))) habs_lt
        exact le_of_lt heps_lt
      have hmul :
          r * a (T1 + k) ≤ r * (r ^ k * M + ε / 2) := by
        gcongr
      have hstep :
          a (T1 + (k + 1)) ≤ r * (r ^ k * M + ε / 2) + α * (ε / 2) := by
        have hrec' : a (T1 + (k + 1)) ≤ r * a (T1 + k) + eps (T1 + k) := by
          simpa [r, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hrec (T1 + k)
        linarith
      have hr_add : r + α = 1 := by
        dsimp [r]
        ring
      calc
        a (T1 + (k + 1)) ≤ r * (r ^ k * M + ε / 2) + α * (ε / 2) := hstep
        _ = r ^ (k + 1) * M + (r + α) * (ε / 2) := by ring
        _ = r ^ (k + 1) * M + ε / 2 := by simp [hr_add]
  have hq_pos : 0 < (ε / 2) / M := by positivity
  rcases exists_pow_lt_of_lt_one hq_pos hr_lt_one with ⟨K, hKpow⟩
  have hKmul : r ^ K * M < ε / 2 := by
    have hM_pos' : 0 < M := hM_pos
    have := mul_lt_mul_of_pos_right hKpow hM_pos'
    simpa [hM_pos'.ne'] using this
  refine ⟨T1 + K, ?_⟩
  intro t ht
  have hT1_le_t : T1 ≤ t := le_trans (Nat.le_add_right T1 K) ht
  rcases Nat.exists_eq_add_of_le hT1_le_t with ⟨k, rfl⟩
  have hk_ge : K ≤ k := by
    exact
      (add_le_add_iff_left T1).1
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht)
  have hpow_le : r ^ k ≤ r ^ K := by
    by_cases hEq : k = K
    · simp [hEq]
    · have hK_lt_k : K < k := lt_of_le_of_ne hk_ge (Ne.symm hEq)
      exact (pow_lt_pow_right_of_lt_one₀ hr_pos hr_lt_one hK_lt_k).le
  have hpowk_mul_lt : r ^ k * M < ε / 2 := by
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hpow_le hM_nonneg) hKmul
  have ha_le : a (T1 + k) ≤ r ^ k * M + ε / 2 := hbound k
  have ha_lt : a (T1 + k) < ε := by
    linarith
  have ha_nonneg_t : 0 ≤ a (T1 + k) := ha_nonneg (T1 + k)
  have habs_lt : |a (T1 + k)| < ε := by
    simpa [abs_of_nonneg ha_nonneg_t] using ha_lt
  simpa [Real.norm_eq_abs] using habs_lt

/--
Part 3 helper: assembly along an accumulation-point subsequence once the recursion and
continuity error term are established.
-/
lemma assembly_from_perturbed_recursion
    (a eps : ℕ → ℝ) (α : ℝ)
    (hα : 0 < α ∧ α < 1)
    (ha_nonneg : ∀ i, 0 ≤ a i)
    (hrec : ∀ i, a (i + 1) ≤ (1 - α) * a i + eps i)
    (heps : ConvergesTo eps 0) :
    ConvergesTo a 0 :=
  perturbed_geometric_convergesTo_zero a eps α hα ha_nonneg hrec heps

end PartTwo

section FinalStatement

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [DecidableEq V]
variable {n : Nat}

omit [FiniteDimensional ℝ V] in
lemma outputSet_nonempty [NeZero n]
    (E : AveragingExecution (V := V) n) (t : Round) :
    (outputSet E t).Nonempty := by
  change (Finset.univ.image (E.outputs t)).Nonempty
  exact Finset.Nonempty.image
    (f := E.outputs t)
    (Finset.univ_nonempty : (Finset.univ : Finset (Proc n)).Nonempty)

omit [FiniteDimensional ℝ V] in
lemma thicknessAt_eq
    (P : V →L[ℝ] V)
    (E : AveragingExecution (V := V) n)
    (t : Round)
    (hX : (outputSet E t).Nonempty) :
    thicknessAt P E t = thicknessOn P (outputSet E t) hX := by
  simp [thicknessAt, hX]

def diffSubmodule
    (E : AveragingExecution (V := V) n)
    (M : Round → Finset (Proc n))
    (t : Round) : Submodule ℝ V :=
  Submodule.span ℝ
    (Set.range (fun p : M (t + 1) × M (t + 1) => E.outputs t p.1.1 - E.outputs t p.2.1))

def roundProjection
    (E : AveragingExecution (V := V) n)
    (M : Round → Finset (Proc n))
    (t : Round) : V →L[ℝ] V :=
  (diffSubmodule E M t)ᗮ.starProjection

omit [DecidableEq V] in
lemma roundProjection_isStarProjection
    (E : AveragingExecution (V := V) n)
    (M : Round → Finset (Proc n))
    (t : Round) :
    IsStarProjection (roundProjection E M t) := by
  change IsStarProjection ((diffSubmodule E M t)ᗮ.starProjection)
  exact isStarProjection_starProjection

omit [DecidableEq V] in
lemma ker_roundProjection
    (E : AveragingExecution (V := V) n)
    (M : Round → Finset (Proc n))
    (t : Round) :
    LinearMap.ker ((roundProjection E M t : V →L[ℝ] V) : V →ₗ[ℝ] V) = diffSubmodule E M t := by
  calc
    LinearMap.ker ((roundProjection E M t : V →L[ℝ] V) : V →ₗ[ℝ] V)
        = ((diffSubmodule E M t)ᗮ)ᗮ := by
            rw [roundProjection]
            simp
    _ = diffSubmodule E M t := by
          simp

omit [FiniteDimensional ℝ V] [DecidableEq V] in
lemma diffSubmodule_finrank_le
    (k : Nat)
    (E : AveragingExecution (V := V) n)
    (M : Round → Finset (Proc n))
    (t : Round)
    (_hk : 1 ≤ k)
    (hcard : ∀ r, (M r).card ≤ k) :
    Module.finrank ℝ (diffSubmodule E M t) ≤ k - 1 := by
  classical
  let Mset : Finset (Proc n) := M (t + 1)
  by_cases hMempty : Mset = ∅
  · have hbot : diffSubmodule E M t = ⊥ := by
      simp [diffSubmodule, Mset, hMempty]
    rw [hbot]
    simp
  · rcases Finset.nonempty_iff_ne_empty.mpr hMempty with ⟨i0, hi0⟩
    let G : Finset V := (Mset.erase i0).image (fun i => E.outputs t i - E.outputs t i0)
    have hspan_le : diffSubmodule E M t ≤ Submodule.span ℝ (G : Set V) := by
      refine Submodule.span_le.mpr ?_
      intro u hu
      rcases hu with ⟨p, rfl⟩
      let i : Proc n := p.1.1
      let j : Proc n := p.2.1
      have hiM : i ∈ Mset := p.1.2
      have hjM : j ∈ Mset := p.2.2
      change E.outputs t i - E.outputs t j ∈ Submodule.span ℝ (G : Set V)
      have hi_term : E.outputs t i - E.outputs t i0 ∈ Submodule.span ℝ (G : Set V) := by
        by_cases hi0eq : i = i0
        · subst hi0eq
          simp [G]
        · have hiErase : i ∈ Mset.erase i0 := by
            simp [hiM, hi0eq]
          have hiImg : E.outputs t i - E.outputs t i0 ∈ G := by
            exact Finset.mem_image.mpr ⟨i, hiErase, rfl⟩
          exact Submodule.subset_span hiImg
      have hj_term : E.outputs t j - E.outputs t i0 ∈ Submodule.span ℝ (G : Set V) := by
        by_cases hj0eq : j = i0
        · subst hj0eq
          simp [G]
        · have hjErase : j ∈ Mset.erase i0 := by
            simp [hjM, hj0eq]
          have hjImg : E.outputs t j - E.outputs t i0 ∈ G := by
            exact Finset.mem_image.mpr ⟨j, hjErase, rfl⟩
          exact Submodule.subset_span hjImg
      have hdecomp :
          E.outputs t i - E.outputs t j
            = (E.outputs t i - E.outputs t i0) - (E.outputs t j - E.outputs t i0) := by
        abel_nf
      rw [hdecomp]
      exact Submodule.sub_mem _ hi_term hj_term
    have hfin_mono :
        Module.finrank ℝ (diffSubmodule E M t)
          ≤ Module.finrank ℝ (Submodule.span ℝ (G : Set V)) :=
      Submodule.finrank_mono hspan_le
    have hfin_span :
        Module.finrank ℝ (Submodule.span ℝ (G : Set V)) ≤ G.card := by
      simpa [Set.finrank] using (finrank_span_finset_le_card (R := ℝ) (s := G))
    have hG_le : G.card ≤ Mset.card - 1 := by
      have h1 : G.card ≤ (Mset.erase i0).card := Finset.card_image_le
      have h2 : (Mset.erase i0).card = Mset.card - 1 := Finset.card_erase_of_mem hi0
      exact h1.trans (by simp [h2])
    have hM_le : Mset.card - 1 ≤ k - 1 := Nat.sub_le_sub_right (hcard (t + 1)) 1
    exact hfin_mono.trans (hfin_span.trans (hG_le.trans hM_le))

omit [DecidableEq V] in
lemma roundProjection_ker_finrank_le
    (k : Nat)
    (E : AveragingExecution (V := V) n)
    (M : Round → Finset (Proc n))
    (t : Round)
    (hk : 1 ≤ k)
    (hcard : ∀ r, (M r).card ≤ k) :
    Module.finrank ℝ (LinearMap.ker ((roundProjection E M t : V →L[ℝ] V) : V →ₗ[ℝ] V)) ≤ k - 1 := by
  rw [ker_roundProjection (E := E) (M := M) (t := t)]
  exact diffSubmodule_finrank_le (k := k) (E := E) (M := M) (t := t) hk hcard

omit [FiniteDimensional ℝ V] [DecidableEq V] in
lemma diffSubmodule_eq_vectorSpan_valuesOn
    (E : AveragingExecution (V := V) n)
    (M : Round → Finset (Proc n))
    (t : Round) :
    diffSubmodule E M t = vectorSpan ℝ (ValuesOn E t (M (t + 1))) := by
  let Mset : Finset (Proc n) := M (t + 1)
  have hset :
      Set.range (fun p : Mset × Mset => E.outputs t p.1.1 - E.outputs t p.2.1)
        = ValuesOn E t Mset -ᵥ ValuesOn E t Mset := by
    ext u
    constructor
    · intro hu
      rcases hu with ⟨p, rfl⟩
      exact (Set.mem_vsub).2
        ⟨E.outputs t p.1.1, ⟨p.1.1, p.1.2, rfl⟩, E.outputs t p.2.1, ⟨p.2.1, p.2.2, rfl⟩, rfl⟩
    · intro hu
      rcases (Set.mem_vsub.mp hu) with ⟨x, hx, y, hy, hxy⟩
      rcases hx with ⟨i, hi, rfl⟩
      rcases hy with ⟨j, hj, rfl⟩
      refine ⟨(⟨i, hi⟩, ⟨j, hj⟩), ?_⟩
      simpa using hxy
  calc
    diffSubmodule E M t
        = Submodule.span ℝ (ValuesOn E t Mset -ᵥ ValuesOn E t Mset) := by
            simp [diffSubmodule, Mset, hset]
    _ = vectorSpan ℝ (ValuesOn E t Mset) := by
          simp [vectorSpan_def]
    _ = vectorSpan ℝ (ValuesOn E t (M (t + 1))) := by
          simp [Mset]

omit [DecidableEq V] in
lemma roundProjection_kills_parallel
    (E : AveragingExecution (V := V) n)
    (M : Round → Finset (Proc n))
    (t : Round) :
    ∀ u ∈ diffSet (PolyOn E t (M (t + 1))), roundProjection E M t u = 0 := by
  intro u hu
  rcases hu with ⟨x, hx, y, hy, rfl⟩
  have hx_aff :
      x ∈ affineSpan ℝ (ValuesOn E t (M (t + 1))) :=
    convexHull_subset_affineSpan (𝕜 := ℝ) (s := ValuesOn E t (M (t + 1))) hx
  have hy_aff :
      y ∈ affineSpan ℝ (ValuesOn E t (M (t + 1))) :=
    convexHull_subset_affineSpan (𝕜 := ℝ) (s := ValuesOn E t (M (t + 1))) hy
  have hmem_vec :
      x - y ∈ vectorSpan ℝ (ValuesOn E t (M (t + 1))) :=
    vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan hx_aff hy_aff
  have hmem_diff : x - y ∈ diffSubmodule E M t := by
    simpa [diffSubmodule_eq_vectorSpan_valuesOn (E := E) (M := M) (t := t)] using hmem_vec
  have hmem_orth : x - y ∈ ((diffSubmodule E M t)ᗮ)ᗮ := by
    simpa [Submodule.orthogonal_orthogonal] using hmem_diff
  change ((diffSubmodule E M t)ᗮ.starProjection) (x - y) = 0
  exact (Submodule.starProjection_apply_eq_zero_iff ((diffSubmodule E M t)ᗮ)).2 hmem_orth

omit [FiniteDimensional ℝ V] [DecidableEq V] in
lemma output_succ_mem_poly
    (E : AveragingExecution (V := V) n)
    (t : Round) (i : Proc n) :
    E.outputs (t + 1) i ∈ Poly E t := by
  let f : Proc n → ℝ := fun j => E.weights (t + 1) i j
  let z : Proc n → V := fun j => E.outputs t j
  let ξ : V := Finset.univ.centerMass f z
  have hξ_mem : ξ ∈ Poly E t := by
    have hw0 : ∀ j ∈ (Finset.univ : Finset (Proc n)), 0 ≤ f j := by
      intro j _hj
      exact E.weight_nonneg (t + 1) i j
    have hsum_pos : 0 < Finset.sum (Finset.univ : Finset (Proc n)) (fun j => f j) := by
      have hsum_one : Finset.sum (Finset.univ : Finset (Proc n)) (fun j => f j) = 1 := by
        simpa [f] using E.weights_sum_one (t + 1) i
      linarith
    have hz : ∀ j ∈ (Finset.univ : Finset (Proc n)), z j ∈ Values E t := by
      intro j _hj
      exact ⟨j, rfl⟩
    have hcm :
        ξ ∈ convexHull ℝ (Values E t) := by
      simpa [ξ, f, z, ModelLemmas.Values] using
        (Finset.centerMass_mem_convexHull
          (R := ℝ) (E := V) (t := (Finset.univ : Finset (Proc n)))
          (w := f) hw0 hsum_pos (z := z) hz)
    simpa [ModelLemmas.Poly] using hcm
  have hξ_eq : ξ = E.outputs (t + 1) i := by
    calc
      ξ = (Finset.sum (Finset.univ : Finset (Proc n)) (fun j => f j))⁻¹ •
            Finset.sum (Finset.univ : Finset (Proc n)) (fun j => f j • z j) := rfl
      _ = (1 : ℝ)⁻¹ •
            Finset.sum (Finset.univ : Finset (Proc n)) (fun j => f j • z j) := by
            simp [f, E.weights_sum_one (t + 1) i]
      _ = Finset.sum (Finset.univ : Finset (Proc n)) (fun j => f j • z j) := by simp
      _ = E.outputs (t + 1) i := by
            simpa [f, z] using (E.output_succ_eq_weighted_sum t i).symm
  simpa [hξ_eq] using hξ_mem

omit [FiniteDimensional ℝ V] in
lemma diffSet_poly_norm_bound
    [NeZero n]
    (P : V →L[ℝ] V)
    (E : AveragingExecution (V := V) n)
    (t : Round)
    (hXt : (outputSet E t).Nonempty) :
    ∀ u ∈ diffSet (Poly E t), ‖P u‖ ≤ thicknessOn P (outputSet E t) hXt := by
  intro u hu
  rcases hu with ⟨x, hx, y, hy, rfl⟩
  have hxP : P x ∈ convexHull ℝ (P '' Values E t) := by
    have hxImg : P x ∈ ((P : V →ₗ[ℝ] V) '' convexHull ℝ (Values E t)) := ⟨x, hx, rfl⟩
    exact (LinearMap.image_convexHull (P : V →ₗ[ℝ] V) (Values E t)) ▸ hxImg
  have hyP : P y ∈ convexHull ℝ (P '' Values E t) := by
    have hyImg : P y ∈ ((P : V →ₗ[ℝ] V) '' convexHull ℝ (Values E t)) := ⟨y, hy, rfl⟩
    exact (LinearMap.image_convexHull (P : V →ₗ[ℝ] V) (Values E t)) ▸ hyImg
  rcases convexHull_exists_dist_ge2 hxP hyP with ⟨x', hx', y', hy', hdist⟩
  rcases hx' with ⟨x0, hx0, rfl⟩
  rcases hy' with ⟨y0, hy0, rfl⟩
  rcases hx0 with ⟨i, rfl⟩
  rcases hy0 with ⟨j, rfl⟩
  have hi : E.outputs t i ∈ outputSet E t := by
    exact Finset.mem_image.mpr ⟨i, by simp, rfl⟩
  have hj : E.outputs t j ∈ outputSet E t := by
    exact Finset.mem_image.mpr ⟨j, by simp, rfl⟩
  have hpair : (E.outputs t i, E.outputs t j) ∈ (outputSet E t).product (outputSet E t) := by
    exact Finset.mem_product.mpr ⟨hi, hj⟩
  have hsup : ‖P (E.outputs t i - E.outputs t j)‖ ≤ thicknessOn P (outputSet E t) hXt := by
    dsimp [thicknessOn]
    exact Finset.le_sup' (f := fun p : V × V => ‖P (p.1 - p.2)‖) hpair
  have hdist' : dist (P x) (P y) ≤ dist (P (E.outputs t i)) (P (E.outputs t j)) := by
    simpa using hdist
  calc
    ‖P (x - y)‖ = dist (P x) (P y) := by simp [dist_eq_norm]
    _ ≤ dist (P (E.outputs t i)) (P (E.outputs t j)) := hdist'
    _ = ‖P (E.outputs t i - E.outputs t j)‖ := by simp [dist_eq_norm]
    _ ≤ thicknessOn P (outputSet E t) hXt := hsup

omit [FiniteDimensional ℝ V] in
lemma thicknessAt_monotone
    [NeZero n]
    (P : V →L[ℝ] V)
    (E : AveragingExecution (V := V) n)
    (t : Round) :
    thicknessAt P E (t + 1) ≤ thicknessAt P E t := by
  have hXt : (outputSet E t).Nonempty := outputSet_nonempty (E := E) t
  have hXnext : (outputSet E (t + 1)).Nonempty := outputSet_nonempty (E := E) (t + 1)
  have hpair :
      ∀ i j : Proc n,
        ‖P (E.outputs (t + 1) i - E.outputs (t + 1) j)‖ ≤ thicknessOn P (outputSet E t) hXt := by
    intro i j
    have hiPoly : E.outputs (t + 1) i ∈ Poly E t := output_succ_mem_poly (E := E) t i
    have hjPoly : E.outputs (t + 1) j ∈ Poly E t := output_succ_mem_poly (E := E) t j
    exact
      diffSet_poly_norm_bound (P := P) (E := E) (t := t) hXt
        (E.outputs (t + 1) i - E.outputs (t + 1) j)
        ⟨E.outputs (t + 1) i, hiPoly, E.outputs (t + 1) j, hjPoly, rfl⟩
  have hstep :
      thicknessOn P (outputSet E (t + 1)) hXnext ≤ thicknessOn P (outputSet E t) hXt :=
    one_step_pair_bound_implies_thickness
      (E := E) (P := P) (t := t) (c := thicknessOn P (outputSet E t) hXt) hXnext hpair
  simpa [thicknessAt_eq (P := P) (E := E) (t := t) hXt,
    thicknessAt_eq (P := P) (E := E) (t := t + 1) hXnext] using hstep

/-- One-step contraction for round-specific projection. -/
lemma roundProjection_one_step [NeZero n]
    (E : AveragingExecution (V := V) n)
    (M : Round → Finset (Proc n))
    (α : ℝ) (t : Round)
    (hα_pos : 0 < α)
    (hα_le_one : α ≤ 1)
    (hmbw : MinimumBroadcastWeight (V := V) E M α) :
    thicknessAt (roundProjection E M t) E (t + 1)
      ≤ (1 - α) * thicknessAt (roundProjection E M t) E t := by
  have hXt := outputSet_nonempty (E := E) t
  have hXnext := outputSet_nonempty (E := E) (t + 1)
  rw [thicknessAt_eq _ E t hXt, thicknessAt_eq _ E (t + 1) hXnext]
  exact one_step_contraction E M α (roundProjection E M t) t hα_pos hα_le_one hmbw hXnext hXt
    (roundProjection_kills_parallel E M t)
    (diffSet_poly_norm_bound (roundProjection E M t) E t hXt)


omit [FiniteDimensional ℝ V] in
lemma thicknessAt_nonneg
    (P : V →L[ℝ] V)
    (E : AveragingExecution (V := V) n)
    (t : Round) :
    0 ≤ thicknessAt P E t := by
  by_cases hX : (outputSet E t).Nonempty
  · have hthick_nonneg : 0 ≤ thicknessOn P (outputSet E t) hX := by
      rcases hX with ⟨x, hx⟩
      have hp : (x, x) ∈ (outputSet E t).product (outputSet E t) := by
        simp [hx]
      have hle : ‖P (x - x)‖ ≤ thicknessOn P (outputSet E t) (by exact ⟨x, hx⟩) := by
        dsimp [thicknessOn]
        exact Finset.le_sup' (f := fun p : V × V => ‖P (p.1 - p.2)‖) hp
      calc
        0 = ‖P (x - x)‖ := by simp
        _ ≤ thicknessOn P (outputSet E t) (by exact ⟨x, hx⟩) := hle
    simpa [thicknessAt, hX] using hthick_nonneg
  · simp [thicknessAt, hX]

theorem paper_delta_contraction_bridge_ge_one [NeZero n]
    (k : Nat)
    (E : AveragingExecution (V := V) n)
    (M : Round → Finset (Proc n))
    (α : ℝ)
    (_hk : 1 ≤ k)
    (hα_pos : 0 < α)
    (hα_ge_one : 1 ≤ α)
    (hmbw : MinimumBroadcastWeight (V := V) E M α)
    (hcard : ∀ t, (M t).card ≤ k) :
    ∃ Pi : V →L[ℝ] V,
      IsStarProjection Pi ∧
      Module.finrank ℝ (LinearMap.ker (Pi : V →ₗ[ℝ] V)) ≤ k - 1 ∧
      ConvergesTo (fun t => thicknessAt Pi E t) 0 := by
  let Pi : V →L[ℝ] V := roundProjection E M 0
  have hPiStar : IsStarProjection Pi := roundProjection_isStarProjection E M 0
  have hPiKer : Module.finrank ℝ (LinearMap.ker (Pi : V →ₗ[ℝ] V)) ≤ k - 1 :=
    roundProjection_ker_finrank_le k E M 0 _hk hcard
  have hα_le_one : α ≤ 1 := by
    let i0 : Proc n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
    have hsubset : M 0 ⊆ (Finset.univ : Finset (Proc n)) := by
      intro j hj
      simp
    have hsum_le :
        Finset.sum (M 0) (fun j => E.weights 0 i0 j)
          ≤ Finset.sum (Finset.univ : Finset (Proc n)) (fun j => E.weights 0 i0 j) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun j _hjU _hjM => E.weight_nonneg 0 i0 j)
    have hα_le_sum : α ≤ Finset.sum (M 0) (fun j => E.weights 0 i0 j) := hmbw.2 0 i0
    calc
      α ≤ Finset.sum (M 0) (fun j => E.weights 0 i0 j) := hα_le_sum
      _ ≤ Finset.sum (Finset.univ : Finset (Proc n)) (fun j => E.weights 0 i0 j) := hsum_le
      _ = 1 := by simpa using E.weights_sum_one 0 i0
  have hstep0 :
      thicknessAt Pi E (0 + 1) ≤ (1 - α) * thicknessAt Pi E 0 :=
    roundProjection_one_step E M α 0 hα_pos hα_le_one hmbw
  have h1zero : thicknessAt Pi E 1 = 0 := by
    have hrhs_nonpos : (1 - α) * thicknessAt Pi E 0 ≤ 0 := by
      have hr_nonpos : 1 - α ≤ 0 := sub_nonpos.mpr hα_ge_one
      exact mul_nonpos_of_nonpos_of_nonneg hr_nonpos (thicknessAt_nonneg (P := Pi) (E := E) 0)
    have hle0 : thicknessAt Pi E 1 ≤ 0 := by
      simpa using (le_trans hstep0 hrhs_nonpos)
    exact le_antisymm hle0 (thicknessAt_nonneg (P := Pi) (E := E) 1)
  have hzero_from_one : ∀ m : ℕ, thicknessAt Pi E (m + 1) = 0 := by
    intro m
    induction m with
    | zero =>
        simpa using h1zero
    | succ m ihm =>
        have hmono : thicknessAt Pi E (m + 1 + 1) ≤ thicknessAt Pi E (m + 1) :=
          thicknessAt_monotone (P := Pi) (E := E) (t := m + 1)
        have hle0 : thicknessAt Pi E (m + 1 + 1) ≤ 0 := by
          simpa [ihm] using hmono
        exact le_antisymm hle0 (thicknessAt_nonneg (P := Pi) (E := E) (m + 1 + 1))
  have hconv : ConvergesTo (fun t => thicknessAt Pi E t) 0 := by
    intro ε hε
    refine ⟨1, ?_⟩
    intro t ht
    rcases Nat.exists_eq_add_of_le ht with ⟨m, rfl⟩
    have hzero : thicknessAt Pi E (m + 1) = 0 := hzero_from_one m
    have hzero' : thicknessAt Pi E (1 + m) = 0 := by simpa [Nat.add_comm] using hzero
    simpa [hzero'] using hε
  exact ⟨Pi, hPiStar, hPiKer, hconv⟩

lemma real_le_of_tendsto_of_eventually_ge
    (f : ℕ → ℝ) (l c : ℝ)
    (ht : Filter.Tendsto f Filter.atTop (nhds l))
    (hge : ∀ n, c ≤ f n) :
    c ≤ l := by
  by_contra hcl
  have hlt : l < c := lt_of_not_ge hcl
  let ε : ℝ := (c - l) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have hEv : ∀ᶠ n in Filter.atTop, f n ∈ Metric.ball l ε := by
    exact ht.eventually (Metric.ball_mem_nhds l hε)
  rcases (Filter.mem_atTop_sets.mp hEv) with ⟨N, hN⟩
  have habs : ‖f N - l‖ < ε := by
    simpa [Metric.mem_ball, dist_eq_norm] using hN N le_rfl
  have hfl : f N - l < ε := (abs_lt.mp (by simpa [Real.norm_eq_abs] using habs)).2
  have hfn_lt_c : f N < c := by
    dsimp [ε] at hfl
    linarith
  exact (not_lt_of_ge (hge N)) hfn_lt_c

omit [DecidableEq V] in
lemma isProj_starProjection
    (K : Submodule ℝ V) :
    LinearMap.IsProj K ((K.starProjection : V →L[ℝ] V).toLinearMap) := by
  refine ⟨?_, ?_⟩
  · intro x
    change ((↑(K.orthogonalProjection x) : V)) ∈ K
    exact (K.orthogonalProjection x).property
  · intro x hx
    let xs : K := ⟨x, hx⟩
    have hself : K.orthogonalProjection x = xs := by
      simpa [xs] using (Submodule.orthogonalProjection_mem_subspace_eq_self xs)
    change ((↑(K.orthogonalProjection x) : V)) = x
    rw [hself]

omit [DecidableEq V] in
lemma kernel_bound_of_accumulation
    (k : Nat)
    (PiSeq : ℕ → V →L[ℝ] V)
    (hPiStar : ∀ t, IsStarProjection (PiSeq t))
    (hPiKer : ∀ t, Module.finrank ℝ (LinearMap.ker ((PiSeq t : V →ₗ[ℝ] V))) ≤ k - 1)
    (Pi : V →L[ℝ] V)
    (hPiStarPi : IsStarProjection Pi)
    (φ : ℕ → ℕ)
    (hφtendsto : Filter.Tendsto (PiSeq ∘ φ) Filter.atTop (nhds Pi)) :
    Module.finrank ℝ (LinearMap.ker (Pi : V →ₗ[ℝ] V)) ≤ k - 1 := by
  let trCLM : (V →L[ℝ] V) →ₗ[ℝ] ℝ :=
    (LinearMap.trace ℝ V).comp (ContinuousLinearMap.coeLM (S := ℝ) (M := V) (N₃ := V))
  have htr_tendsto :
      Filter.Tendsto (fun i => trCLM ((PiSeq ∘ φ) i)) Filter.atTop (nhds (trCLM Pi)) := by
    have hcont : Continuous trCLM := LinearMap.continuous_of_finiteDimensional trCLM
    exact (hcont.tendsto Pi).comp hφtendsto
  have htrace_ge :
      ∀ t, ((Module.finrank ℝ V - (k - 1) : ℕ) : ℝ) ≤ trCLM (PiSeq t) := by
    intro t
    rcases (isStarProjection_iff_eq_starProjection.mp (hPiStar t)) with ⟨K, _hK, hKproj⟩
    have hPiKer_t : Module.finrank ℝ (LinearMap.ker ((PiSeq t : V →ₗ[ℝ] V))) ≤ k - 1 := hPiKer t
    have hker_eq_t : LinearMap.ker ((PiSeq t : V →ₗ[ℝ] V)) = Kᗮ := by
      rw [hKproj]
      exact Submodule.ker_starProjection K
    have hkerK : Module.finrank ℝ Kᗮ ≤ k - 1 := by
      rw [← hker_eq_t]
      exact hPiKer_t
    have hsum : Module.finrank ℝ K + Module.finrank ℝ Kᗮ = Module.finrank ℝ V :=
      Submodule.finrank_add_finrank_orthogonal K
    have hK_ge : Module.finrank ℝ V - (k - 1) ≤ Module.finrank ℝ K := by
      have hK_eq : Module.finrank ℝ K = Module.finrank ℝ V - Module.finrank ℝ Kᗮ := by
        exact Nat.eq_sub_of_add_eq (by simpa [Nat.add_comm] using hsum)
      calc
        Module.finrank ℝ V - (k - 1)
            ≤ Module.finrank ℝ V - Module.finrank ℝ Kᗮ := Nat.sub_le_sub_left hkerK _
        _ = Module.finrank ℝ K := by
              rw [hK_eq]
    have htraceK :
        trCLM (K.starProjection) = (Module.finrank ℝ K : ℝ) := by
      have htrace_proj :
          (LinearMap.trace ℝ V) ((K.starProjection : V →L[ℝ] V).toLinearMap)
            = (Module.finrank ℝ K : ℝ) := by
        simpa using
          (LinearMap.IsProj.trace (R := ℝ) (M := V) (p := K)
            (f := ((K.starProjection : V →L[ℝ] V).toLinearMap))
            (isProj_starProjection (K := K))
            )
      simpa [trCLM] using htrace_proj
    rw [hKproj]
    calc
      ((Module.finrank ℝ V - (k - 1) : ℕ) : ℝ) ≤ (Module.finrank ℝ K : ℝ) := Nat.cast_le.mpr hK_ge
      _ = trCLM (K.starProjection) := by simpa using htraceK.symm
  have htracePi_ge :
      ((Module.finrank ℝ V - (k - 1) : ℕ) : ℝ) ≤ trCLM Pi := by
    exact real_le_of_tendsto_of_eventually_ge
      (f := fun i => trCLM ((PiSeq ∘ φ) i))
      (l := trCLM Pi)
      (c := ((Module.finrank ℝ V - (k - 1) : ℕ) : ℝ))
      htr_tendsto (fun i => htrace_ge (φ i))
  rcases (isStarProjection_iff_eq_starProjection.mp hPiStarPi) with ⟨K, _hK, rfl⟩
  have htracePi :
      trCLM (K.starProjection) = (Module.finrank ℝ K : ℝ) := by
    have htrace_proj :
        (LinearMap.trace ℝ V) ((K.starProjection : V →L[ℝ] V).toLinearMap)
          = (Module.finrank ℝ K : ℝ) := by
      simpa using
        (LinearMap.IsProj.trace (R := ℝ) (M := V) (p := K)
          (f := ((K.starProjection : V →L[ℝ] V).toLinearMap))
          (isProj_starProjection (K := K))
          )
    simpa [trCLM] using htrace_proj
  have hK_ge_nat : Module.finrank ℝ V - (k - 1) ≤ Module.finrank ℝ K := by
    exact_mod_cast (htracePi_ge.trans_eq htracePi)
  have hsumK : Module.finrank ℝ K + Module.finrank ℝ Kᗮ = Module.finrank ℝ V := by
    exact Submodule.finrank_add_finrank_orthogonal K
  have hle_add' : Module.finrank ℝ K + Module.finrank ℝ Kᗮ ≤ Module.finrank ℝ K + (k - 1) := by
    simpa [hsumK] using (Nat.sub_le_iff_le_add.mp hK_ge_nat)
  have hKorth_le : Module.finrank ℝ Kᗮ ≤ k - 1 := Nat.le_of_add_le_add_left hle_add'
  have hker_bound :
      Module.finrank ℝ (((K.starProjection : V →L[ℝ] V) : V →ₗ[ℝ] V).ker) ≤ k - 1 := by
    rw [Submodule.ker_starProjection K]
    exact hKorth_le
  simpa using hker_bound

lemma convergesTo_of_tendsto {β : Type*} [NormedAddCommGroup β]
    (x : ℕ → β) (l : β)
    (h : Filter.Tendsto x Filter.atTop (nhds l)) :
    ConvergesTo x l := by
  intro ε hε
  have hEv : ∀ᶠ n in Filter.atTop, x n ∈ Metric.ball l ε := by
    exact h.eventually (Metric.ball_mem_nhds l hε)
  rcases (Filter.mem_atTop_sets.mp hEv) with ⟨T, hT⟩
  refine ⟨T, ?_⟩
  intro t ht
  simpa [Metric.mem_ball, dist_eq_norm] using hT t ht

omit [FiniteDimensional ℝ V] in
lemma thicknessAt_antitone [NeZero n]
    (P : V →L[ℝ] V)
    (E : AveragingExecution (V := V) n) :
    Antitone (fun t => thicknessAt P E t) := by
  intro s t hst
  rcases Nat.exists_eq_add_of_le hst with ⟨d, rfl⟩
  have haux : ∀ m : ℕ, thicknessAt P E (s + m) ≤ thicknessAt P E s := by
    intro m
    induction m with
    | zero =>
        simp
    | succ m ihm =>
        have hstep : thicknessAt P E (s + m + 1) ≤ thicknessAt P E (s + m) := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (thicknessAt_monotone (P := P) (E := E) (t := s + m))
        exact le_trans hstep ihm
  exact haux d

omit [FiniteDimensional ℝ V] in
lemma thicknessAt_continuity_bound [NeZero n]
    (P Q : V →L[ℝ] V)
    (E : AveragingExecution (V := V) n)
    (t : Round) :
    |thicknessAt P E t - thicknessAt Q E t|
      ≤ ‖P - Q‖ * pairDiameter (outputSet E t) (outputSet_nonempty (E := E) t) := by
  let hXt : (outputSet E t).Nonempty := outputSet_nonempty (E := E) t
  simpa [thicknessAt_eq (P := P) (E := E) (t := t) hXt,
    thicknessAt_eq (P := Q) (E := E) (t := t) hXt] using
    (lemma_continuity_complete (X := outputSet E t) (hX := hXt) P Q)

omit [FiniteDimensional ℝ V] in
lemma pairDiameter_le_initial [NeZero n]
    (E : AveragingExecution (V := V) n)
    (t : Round) :
    pairDiameter (outputSet E t) (outputSet_nonempty (E := E) t)
      ≤ pairDiameter (outputSet E 0) (outputSet_nonempty (E := E) 0) := by
  let Pid : V →L[ℝ] V := ContinuousLinearMap.id ℝ V
  have hanti := thicknessAt_antitone (P := Pid) (E := E)
  have hle : thicknessAt Pid E t ≤ thicknessAt Pid E 0 := hanti (Nat.zero_le t)
  have hXt : (outputSet E t).Nonempty := outputSet_nonempty (E := E) t
  have hX0 : (outputSet E 0).Nonempty := outputSet_nonempty (E := E) 0
  simpa [thicknessAt_eq (P := Pid) (E := E) (t := t) hXt,
    thicknessAt_eq (P := Pid) (E := E) (t := 0) hX0,
    pairDiameter, thicknessOn] using hle

omit [FiniteDimensional ℝ V] [DecidableEq V] in
lemma adjacent_norm_converges_to_zero
    (x : ℕ → V →L[ℝ] V) (l : V →L[ℝ] V)
    (hx : ConvergesTo x l) :
    ConvergesTo (fun i => ‖x (i + 1) - x i‖) 0 := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  rcases hx (ε / 2) hε2 with ⟨T, hT⟩
  refine ⟨T, ?_⟩
  intro i hi
  have hTi : ‖x i - l‖ < ε / 2 := hT i hi
  have hTsucc : ‖x (i + 1) - l‖ < ε / 2 := hT (i + 1) (le_trans hi (Nat.le_succ i))
  have htri : ‖x (i + 1) - x i‖ ≤ ‖x (i + 1) - l‖ + ‖x i - l‖ := by
    calc
      ‖x (i + 1) - x i‖ = ‖(x (i + 1) - l) - (x i - l)‖ := by abel_nf
      _ ≤ ‖x (i + 1) - l‖ + ‖x i - l‖ := norm_sub_le _ _
  have hlt : ‖x (i + 1) - x i‖ < ε := by linarith
  have hnonneg : 0 ≤ ‖x (i + 1) - x i‖ := norm_nonneg _
  have habs : |‖x (i + 1) - x i‖ - 0| < ε := by
    simpa [abs_of_nonneg hnonneg] using hlt
  simpa [Real.norm_eq_abs] using habs

omit [FiniteDimensional ℝ V] in
lemma paper_delta_contraction_convergence [NeZero n]
    (E : AveragingExecution (V := V) n)
    (M : Round → Finset (Proc n))
    (α : ℝ)
    (hα_pos : 0 < α)
    (hα_lt_one : α < 1)
    (_hmbw : MinimumBroadcastWeight (V := V) E M α)
    (Pi : V →L[ℝ] V)
    (PiSeq : Round → V →L[ℝ] V)
    (φ : ℕ → ℕ)
    (hφmono : StrictMono φ)
    (hφtendsto : Filter.Tendsto (PiSeq ∘ φ) Filter.atTop (nhds Pi))
    (hOneStep : ∀ t, thicknessAt (PiSeq t) E (t + 1) ≤ (1 - α) * thicknessAt (PiSeq t) E t) :
    ConvergesTo (fun t => thicknessAt Pi E t) 0 := by
  let a : ℕ → ℝ := fun i => thicknessAt (PiSeq (φ i)) E (φ i)
  let D : ℝ := pairDiameter (outputSet E 0) (outputSet_nonempty (E := E) 0)
  let eps : ℕ → ℝ := fun i => ‖PiSeq (φ (i + 1)) - PiSeq (φ i)‖ * D
  have hD_nonneg : 0 ≤ D := by
    rcases outputSet_nonempty (E := E) 0 with ⟨x, hx⟩
    have hp : (x, x) ∈ (outputSet E 0).product (outputSet E 0) := by simp [hx]
    have hle : ‖x - x‖ ≤ pairDiameter (outputSet E 0) (outputSet_nonempty (E := E) 0) := by
      dsimp [pairDiameter]
      exact Finset.le_sup' (f := fun p : V × V => ‖p.1 - p.2‖) hp
    have h0 : 0 ≤ ‖x - x‖ := norm_nonneg _
    exact le_trans h0 hle
  have hrec : ∀ i, a (i + 1) ≤ (1 - α) * a i + eps i := by
    intro i
    have hphi : φ i + 1 ≤ φ (i + 1) := Nat.succ_le_of_lt (hφmono (Nat.lt_succ_self i))
    have hmonoA :
        thicknessAt (PiSeq (φ (i + 1))) E (φ (i + 1))
          ≤ thicknessAt (PiSeq (φ (i + 1))) E (φ i + 1) := by
      exact (thicknessAt_antitone (P := PiSeq (φ (i + 1))) (E := E)) hphi
    have hcont_abs :
        |thicknessAt (PiSeq (φ (i + 1))) E (φ i + 1)
            - thicknessAt (PiSeq (φ i)) E (φ i + 1)|
          ≤ ‖PiSeq (φ (i + 1)) - PiSeq (φ i)‖ * D := by
      have hbase :
          |thicknessAt (PiSeq (φ (i + 1))) E (φ i + 1)
              - thicknessAt (PiSeq (φ i)) E (φ i + 1)|
            ≤ ‖PiSeq (φ (i + 1)) - PiSeq (φ i)‖ *
              pairDiameter (outputSet E (φ i + 1)) (outputSet_nonempty (E := E) (φ i + 1)) := by
        exact thicknessAt_continuity_bound (P := PiSeq (φ (i + 1))) (Q := PiSeq (φ i))
          (E := E) (t := φ i + 1)
      have hdiam :
          pairDiameter (outputSet E (φ i + 1)) (outputSet_nonempty (E := E) (φ i + 1)) ≤ D := by
        simpa [D] using pairDiameter_le_initial (E := E) (t := φ i + 1)
      exact le_trans hbase (by gcongr)
    have hcont_le :
        thicknessAt (PiSeq (φ (i + 1))) E (φ i + 1)
          ≤ thicknessAt (PiSeq (φ i)) E (φ i + 1) + eps i := by
      dsimp [eps]
      have hab :
          thicknessAt (PiSeq (φ (i + 1))) E (φ i + 1)
            - thicknessAt (PiSeq (φ i)) E (φ i + 1)
          ≤ ‖PiSeq (φ (i + 1)) - PiSeq (φ i)‖ * D := by
        exact le_trans (le_abs_self _ ) hcont_abs
      linarith
    have hone :
        thicknessAt (PiSeq (φ i)) E (φ i + 1)
          ≤ (1 - α) * thicknessAt (PiSeq (φ i)) E (φ i) := hOneStep (φ i)
    dsimp [a, eps]
    linarith
  have ha_nonneg : ∀ i, 0 ≤ a i := by
    intro i
    dsimp [a]
    exact thicknessAt_nonneg (P := PiSeq (φ i)) (E := E) (t := φ i)
  have hxconv : ConvergesTo (fun i => PiSeq (φ i)) Pi :=
    convergesTo_of_tendsto (x := fun i => PiSeq (φ i)) (l := Pi) hφtendsto
  have hdiff : ConvergesTo (fun i => ‖PiSeq (φ (i + 1)) - PiSeq (φ i)‖) 0 :=
    adjacent_norm_converges_to_zero (x := fun i => PiSeq (φ i)) (l := Pi) hxconv
  have heps : ConvergesTo eps 0 := by
    by_cases hD0 : D = 0
    · simpa [eps, hD0] using convergesTo_const (0 : ℝ)
    · have hD_pos : 0 < D := lt_of_le_of_ne hD_nonneg (Ne.symm hD0)
      intro ε hε
      rcases hdiff (ε / D) (by positivity) with ⟨T, hT⟩
      refine ⟨T, ?_⟩
      intro i hi
      have hlt : ‖PiSeq (φ (i + 1)) - PiSeq (φ i)‖ < ε / D := by
        have hnorm := hT i hi
        have hnonneg : 0 ≤ ‖PiSeq (φ (i + 1)) - PiSeq (φ i)‖ := norm_nonneg _
        exact (abs_lt.mp (by simpa [Real.norm_eq_abs] using hnorm)).2
      have hmul : ‖PiSeq (φ (i + 1)) - PiSeq (φ i)‖ * D < ε := by
          have := mul_lt_mul_of_pos_right hlt hD_pos
          have hdiv : (ε / D) * D = ε := by field_simp [hD0]
          simpa [hdiv]
      have hnonneg : 0 ≤ eps i := by
        dsimp [eps]
        exact mul_nonneg (norm_nonneg _) hD_nonneg
      have hmul_eps : eps i < ε := by
        simpa [eps] using hmul
      have habs : |eps i - 0| < ε := by
        simpa [sub_eq_add_neg, abs_of_nonneg hnonneg] using hmul_eps
      simpa [Real.norm_eq_abs] using habs
  have ha_conv : ConvergesTo a 0 :=
    perturbed_geometric_convergesTo_zero a eps α ⟨hα_pos, hα_lt_one⟩ ha_nonneg hrec heps
  have htransfer : ConvergesTo (fun i => thicknessAt Pi E (φ i)) 0 := by
    intro ε hε
    have hε2 : 0 < ε / 2 := by linarith
    rcases ha_conv (ε / 2) hε2 with ⟨T1, hT1⟩
    let delta : ℕ → ℝ := fun i => ‖Pi - PiSeq (φ i)‖ * D
    have hdelta : ConvergesTo delta 0 := by
      by_cases hD0 : D = 0
      · simpa [delta, hD0] using convergesTo_const (0 : ℝ)
      · have hD_pos : 0 < D := lt_of_le_of_ne hD_nonneg (Ne.symm hD0)
        intro η hη
        rcases hxconv (η / D) (by positivity) with ⟨T, hT⟩
        refine ⟨T, ?_⟩
        intro i hi
        have hnorm : ‖PiSeq (φ i) - Pi‖ < η / D := hT i hi
        have hmul : ‖Pi - PiSeq (φ i)‖ * D < η := by
          have hnorm' : ‖Pi - PiSeq (φ i)‖ < η / D := by simpa [norm_sub_rev] using hnorm
          have := mul_lt_mul_of_pos_right hnorm' hD_pos
          have hdiv : (η / D) * D = η := by field_simp [hD0]
          simpa [hdiv]
        have hnonneg : 0 ≤ delta i := by
          dsimp [delta]
          exact mul_nonneg (norm_nonneg _) hD_nonneg
        have habs : |delta i - 0| < η := by
          simpa [delta, abs_of_nonneg hnonneg] using hmul
        simpa [Real.norm_eq_abs] using habs
    rcases hdelta (ε / 2) hε2 with ⟨T2, hT2⟩
    refine ⟨max T1 T2, ?_⟩
    intro i hi
    have ha_small : ‖a i - 0‖ < ε / 2 := hT1 i (le_trans (le_max_left _ _) hi)
    have hδ_small : ‖delta i - 0‖ < ε / 2 := hT2 i (le_trans (le_max_right _ _) hi)
    have hcont_abs :
        |thicknessAt Pi E (φ i) - a i| ≤ delta i := by
      have hbase :
          |thicknessAt Pi E (φ i) - thicknessAt (PiSeq (φ i)) E (φ i)|
            ≤ ‖Pi - PiSeq (φ i)‖ *
              pairDiameter (outputSet E (φ i)) (outputSet_nonempty (E := E) (φ i)) := by
        exact thicknessAt_continuity_bound (P := Pi) (Q := PiSeq (φ i)) (E := E) (t := φ i)
      have hdiam :
          pairDiameter (outputSet E (φ i)) (outputSet_nonempty (E := E) (φ i)) ≤ D := by
        simpa [D] using pairDiameter_le_initial (E := E) (t := φ i)
      have hmul :
          ‖Pi - PiSeq (φ i)‖ *
              pairDiameter (outputSet E (φ i)) (outputSet_nonempty (E := E) (φ i))
            ≤ delta i := by
        dsimp [delta]
        gcongr
      dsimp [a] at *
      exact le_trans hbase hmul
    have hmain_le :
        ‖thicknessAt Pi E (φ i) - 0‖ ≤ ‖a i - 0‖ + ‖delta i - 0‖ := by
      have hdelta_nonneg : 0 ≤ delta i := by
        dsimp [delta]
        exact mul_nonneg (norm_nonneg _) hD_nonneg
      have hleft : ‖thicknessAt Pi E (φ i) - a i‖ ≤ ‖delta i - 0‖ := by
        have habs : |thicknessAt Pi E (φ i) - a i| ≤ delta i := hcont_abs
        simpa [Real.norm_eq_abs, abs_of_nonneg hdelta_nonneg] using habs
      calc
        ‖thicknessAt Pi E (φ i) - 0‖
            ≤ ‖thicknessAt Pi E (φ i) - a i‖ + ‖a i - 0‖ := by
                simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
                  (norm_add_le (thicknessAt Pi E (φ i) - a i) (a i - 0))
        _ ≤ ‖delta i - 0‖ + ‖a i - 0‖ := add_le_add hleft (le_rfl)
        _ = ‖a i - 0‖ + ‖delta i - 0‖ := by ring
    have hlt : ‖thicknessAt Pi E (φ i) - 0‖ < ε := by linarith
    simpa using hlt
  intro ε hε
  rcases htransfer ε hε with ⟨N, hN⟩
  refine ⟨φ N, ?_⟩
  intro t ht
  have hmonoPi := thicknessAt_antitone (P := Pi) (E := E)
  have hle : thicknessAt Pi E t ≤ thicknessAt Pi E (φ N) := hmonoPi ht
  have hbase : ‖thicknessAt Pi E (φ N) - 0‖ < ε := hN N le_rfl
  have hbase' : thicknessAt Pi E (φ N) < ε := by
    have hnonneg : 0 ≤ thicknessAt Pi E (φ N) := thicknessAt_nonneg (P := Pi) (E := E) (t := φ N)
    have habs : |thicknessAt Pi E (φ N)| < ε := by simpa [Real.norm_eq_abs] using hbase
    exact (abs_lt.mp habs).2
  have hnonneg_t : 0 ≤ thicknessAt Pi E t := thicknessAt_nonneg (P := Pi) (E := E) t
  have ht_lt : thicknessAt Pi E t < ε := lt_of_le_of_lt hle hbase'
  have habs : |thicknessAt Pi E t - 0| < ε := by
    simpa [abs_of_nonneg hnonneg_t] using ht_lt
  simpa [Real.norm_eq_abs] using habs

theorem paper_delta_contraction_bridge [NeZero n]
    (k : Nat)
    (E : AveragingExecution (V := V) n)
    (M : Round → Finset (Proc n))
    (α : ℝ)
    (_hk : 1 ≤ k)
    (hα_pos : 0 < α)
    (hmbw : MinimumBroadcastWeight (V := V) E M α)
    (hcard : ∀ t, (M t).card ≤ k) :
    ∃ Pi : V →L[ℝ] V,
      IsStarProjection Pi ∧
      Module.finrank ℝ (LinearMap.ker (Pi : V →ₗ[ℝ] V)) ≤ k - 1 ∧
      ConvergesTo (fun t => thicknessAt Pi E t) 0 := by
  by_cases hα_lt_one : α < 1
  · let PiSeq : Round → V →L[ℝ] V := fun t => roundProjection E M t
    have hPiStar : ∀ t, IsStarProjection (PiSeq t) := fun t =>
      roundProjection_isStarProjection E M t
    have hPiKer : ∀ t, Module.finrank ℝ (LinearMap.ker ((PiSeq t : V →ₗ[ℝ] V))) ≤ k - 1 :=
      fun t => roundProjection_ker_finrank_le k E M t _hk hcard
    have hOneStep :
        ∀ t, thicknessAt (PiSeq t) E (t + 1) ≤ (1 - α) * thicknessAt (PiSeq t) E t := by
      intro t
      exact roundProjection_one_step E M α t hα_pos (le_of_lt hα_lt_one) hmbw
    rcases lemma_accumulation_point PiSeq hPiStar with ⟨Pi, hPiStarPi, φ, hφmono, hφtendsto⟩
    have hKerPi :
        Module.finrank ℝ (LinearMap.ker (Pi : V →ₗ[ℝ] V)) ≤ k - 1 :=
      kernel_bound_of_accumulation k PiSeq hPiStar hPiKer Pi hPiStarPi φ hφtendsto
    have hConv :
        ConvergesTo (fun t => thicknessAt Pi E t) 0 :=
      paper_delta_contraction_convergence E M α hα_pos hα_lt_one hmbw
        Pi PiSeq φ hφmono hφtendsto hOneStep
    exact ⟨Pi, hPiStarPi, hKerPi, hConv⟩
  · exact
      paper_delta_contraction_bridge_ge_one k E M α _hk hα_pos
        (le_of_not_gt hα_lt_one) hmbw hcard

theorem lemma_Delta_contraction_core [NeZero n]
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
      ConvergesTo (fun t => thicknessAt Pi E t) 0 :=
  paper_delta_contraction_bridge k E M α _hk _hα_pos _hmbw _hcard

end FinalStatement


end AsymptoticSubspace

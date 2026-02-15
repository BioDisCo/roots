-- Internal plumbing module.
-- Reader-facing statements live in `Def*`, `Lem*`, and `Thm*` files.
import AsymptoticSubspace.ComputationalModelCore
import AsymptoticSubspace.PaperFormalizationCore

noncomputable section

namespace AsymptoticSubspace
namespace ModelLemmas

open Set
open ComputationalModel
open PaperFormalization

section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {n : Nat}

/-- Uniqueness of asymptotic limits in normed spaces. -/
theorem convergesTo_unique_aux
    {V' : Type*} {x : Round → V'} {l₁ l₂ : V'}
    [NormedAddCommGroup V']
    (h₁ : ConvergesTo x l₁) (h₂ : ConvergesTo x l₂) :
    l₁ = l₂ := by
  by_contra hne
  have hdist_pos : 0 < ‖l₁ - l₂‖ := by
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  let ε : ℝ := ‖l₁ - l₂‖ / 2
  have hε_pos : 0 < ε := by
    dsimp [ε]
    linarith
  rcases h₁ ε hε_pos with ⟨T₁, hT₁⟩
  rcases h₂ ε hε_pos with ⟨T₂, hT₂⟩
  let T := max T₁ T₂
  have h1 : ‖x T - l₁‖ < ε := hT₁ T (le_max_left _ _)
  have h2 : ‖x T - l₂‖ < ε := hT₂ T (le_max_right _ _)
  have htri : ‖l₁ - l₂‖ ≤ ‖x T - l₁‖ + ‖x T - l₂‖ := by
    calc
      ‖l₁ - l₂‖ = ‖(l₁ - x T) + (x T - l₂)‖ := by abel_nf
      _ ≤ ‖l₁ - x T‖ + ‖x T - l₂‖ := norm_add_le _ _
      _ = ‖x T - l₁‖ + ‖x T - l₂‖ := by simp [norm_sub_rev]
  have hlt : ‖x T - l₁‖ + ‖x T - l₂‖ < ‖l₁ - l₂‖ := by
    have hsum : ‖x T - l₁‖ + ‖x T - l₂‖ < ε + ε := add_lt_add h1 h2
    have hε : ε + ε = ‖l₁ - l₂‖ := by
      dsimp [ε]
      ring_nf
    simpa [hε] using hsum
  exact (not_lt_of_ge htri) hlt

theorem convergesTo_const {V' : Type*} [NormedAddCommGroup V'] (c : V') :
    ConvergesTo (fun _ : Round => c) c := by
  intro ε hε
  refine ⟨0, ?_⟩
  intro t ht
  simpa using hε

theorem convergesToSet_singleton_iff
    {V' : Type*} [NormedAddCommGroup V'] {x : Round → V'} {a : V'} :
    ConvergesToSet x ({a} : Set V') ↔ ConvergesTo x a := by
  constructor
  · intro h ε hε
    rcases h.2 ε hε with ⟨T, hT⟩
    refine ⟨T, ?_⟩
    intro t ht
    simpa [ConvergesToSet, Metric.infDist_singleton, dist_eq_norm] using hT t ht
  · intro h
    refine ⟨Set.singleton_nonempty a, ?_⟩
    intro ε hε
    rcases h ε hε with ⟨T, hT⟩
    refine ⟨T, ?_⟩
    intro t ht
    simpa [ConvergesToSet, Metric.infDist_singleton, dist_eq_norm] using hT t ht

theorem mem_closure_of_convergesTo_and_convergesToSet
    {V' : Type*} [NormedAddCommGroup V']
    {x : Round → V'} {a : V'} {S : Set V'}
    (hTo : ConvergesTo x a)
    (hToSet : ConvergesToSet x S) :
    a ∈ closure S := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  rcases hTo (ε / 2) hε2 with ⟨T₁, hT₁⟩
  rcases hToSet.2 (ε / 2) hε2 with ⟨T₂, hT₂⟩
  let T := max T₁ T₂
  have hx : dist (x T) a < ε / 2 := by
    simpa [dist_eq_norm] using hT₁ T (le_max_left _ _)
  have hdistS : Metric.infDist (x T) S < ε / 2 := hT₂ T (le_max_right _ _)
  rcases (Metric.infDist_lt_iff hToSet.1).1 hdistS with ⟨y, hyS, hxy⟩
  refine ⟨y, hyS, ?_⟩
  calc
    dist a y ≤ dist a (x T) + dist (x T) y := dist_triangle _ _ _
    _ = dist (x T) a + dist (x T) y := by rw [dist_comm a (x T)]
    _ < ε / 2 + ε / 2 := add_lt_add hx hxy
    _ = ε := by ring

/-- Maximum pairwise distance on a finite nonempty set. -/
def pairDiameter (X : Finset V) (hX : X.Nonempty) : ℝ :=
  (X.product X).sup'
    (by
      rcases hX with ⟨x, hx⟩
      exact ⟨(x, x), by simp [hx]⟩)
    (fun p => ‖p.1 - p.2‖)

/-- Thickness of a finite nonempty set under a linear map. -/
def thicknessOn
    (P : V →L[ℝ] V)
    (X : Finset V) (hX : X.Nonempty) : ℝ :=
  (X.product X).sup'
    (by
      rcases hX with ⟨x, hx⟩
      exact ⟨(x, x), by simp [hx]⟩)
    (fun p => ‖P (p.1 - p.2)‖)

/-- Complete formalization of Lemma `lem:continuity` from the paper. -/
theorem lemma_continuity_complete
    (X : Finset V) (hX : X.Nonempty)
    (P Q : V →L[ℝ] V) :
    |thicknessOn P X hX - thicknessOn Q X hX|
      ≤ ‖P - Q‖ * pairDiameter X hX := by
  have hprod : (X.product X).Nonempty := by
    rcases hX with ⟨x, hx⟩
    exact ⟨(x, x), by simp [hx]⟩
  let c : ℝ := ‖P - Q‖ * pairDiameter X hX
  have hP_le : thicknessOn P X hX ≤ thicknessOn Q X hX + c := by
    dsimp [thicknessOn]
    refine Finset.sup'_le (H := hprod) (f := fun p : V × V => ‖P (p.1 - p.2)‖) ?_
    intro p hp
    have hpQ : ‖Q (p.1 - p.2)‖ ≤ thicknessOn Q X hX := by
      exact Finset.le_sup' (f := fun r => ‖Q (r.1 - r.2)‖) hp
    have hpdiam : ‖p.1 - p.2‖ ≤ pairDiameter X hX := by
      exact Finset.le_sup' (f := fun r => ‖r.1 - r.2‖) hp
    have hop : ‖(P - Q) (p.1 - p.2)‖ ≤ ‖P - Q‖ * ‖p.1 - p.2‖ := by
      exact (P - Q).le_opNorm (p.1 - p.2)
    have hmul : ‖P - Q‖ * ‖p.1 - p.2‖ ≤ c := by
      dsimp [c]
      exact mul_le_mul_of_nonneg_left hpdiam (norm_nonneg _)
    have hstep :
        ‖P (p.1 - p.2)‖ ≤ ‖Q (p.1 - p.2)‖ + c := by
      calc
        ‖P (p.1 - p.2)‖ = ‖(P - Q) (p.1 - p.2) + Q (p.1 - p.2)‖ := by
              simp
        _ ≤ ‖(P - Q) (p.1 - p.2)‖ + ‖Q (p.1 - p.2)‖ := norm_add_le _ _
        _ ≤ ‖P - Q‖ * ‖p.1 - p.2‖ + ‖Q (p.1 - p.2)‖ := by
              exact add_le_add hop (le_rfl)
        _ ≤ c + ‖Q (p.1 - p.2)‖ := by
              linarith [hmul]
        _ = ‖Q (p.1 - p.2)‖ + c := by ring
    have hpQ' : ‖Q (p.1 - p.2)‖ + c ≤ thicknessOn Q X hX + c := by
      linarith [hpQ]
    exact le_trans hstep hpQ'
  have hQ_le : thicknessOn Q X hX ≤ thicknessOn P X hX + c := by
    dsimp [thicknessOn]
    refine Finset.sup'_le (H := hprod) (f := fun p : V × V => ‖Q (p.1 - p.2)‖) ?_
    intro p hp
    have hpP : ‖P (p.1 - p.2)‖ ≤ thicknessOn P X hX := by
      exact Finset.le_sup' (f := fun r => ‖P (r.1 - r.2)‖) hp
    have hpdiam : ‖p.1 - p.2‖ ≤ pairDiameter X hX := by
      exact Finset.le_sup' (f := fun r => ‖r.1 - r.2‖) hp
    have hop : ‖(Q - P) (p.1 - p.2)‖ ≤ ‖Q - P‖ * ‖p.1 - p.2‖ := by
      exact (Q - P).le_opNorm (p.1 - p.2)
    have hmul : ‖Q - P‖ * ‖p.1 - p.2‖ ≤ c := by
      calc
        ‖Q - P‖ * ‖p.1 - p.2‖ = ‖P - Q‖ * ‖p.1 - p.2‖ := by simp [norm_sub_rev]
        _ ≤ ‖P - Q‖ * pairDiameter X hX := mul_le_mul_of_nonneg_left hpdiam (norm_nonneg _)
        _ = c := by rfl
    have hstep :
        ‖Q (p.1 - p.2)‖ ≤ ‖P (p.1 - p.2)‖ + c := by
      calc
        ‖Q (p.1 - p.2)‖ = ‖(Q - P) (p.1 - p.2) + P (p.1 - p.2)‖ := by
              simp
        _ ≤ ‖(Q - P) (p.1 - p.2)‖ + ‖P (p.1 - p.2)‖ := norm_add_le _ _
        _ ≤ ‖Q - P‖ * ‖p.1 - p.2‖ + ‖P (p.1 - p.2)‖ := by
              exact add_le_add hop (le_rfl)
        _ ≤ c + ‖P (p.1 - p.2)‖ := by
              linarith [hmul]
        _ = ‖P (p.1 - p.2)‖ + c := by ring
    have hpP' : ‖P (p.1 - p.2)‖ + c ≤ thicknessOn P X hX + c := by
      linarith [hpP]
    exact le_trans hstep hpP'
  rw [abs_sub_le_iff]
  constructor
  · linarith [hP_le]
  · linarith [hQ_le]

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

end

end ModelLemmas
end AsymptoticSubspace

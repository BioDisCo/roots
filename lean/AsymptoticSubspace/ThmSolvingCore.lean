-- Internal plumbing module.
-- Reader-facing statement is in `ThmSolving.lean`.
import AsymptoticSubspace.LemDeltaContraction

noncomputable section

namespace AsymptoticSubspace
namespace ThmSolving

open Set
open ComputationalModel
open ModelLemmas

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {n : Nat}

/--
Validity in set-convergence form for averaging executions:
each trajectory stays in the convex hull of round-0 outputs, hence converges to that set.
-/
theorem averaging_validityAtLimit [NeZero n]
    (E : AveragingExecution (V := V) n) :
    ∀ i : Proc n,
      ConvergesToSet
        (fun t => E.outputs t i)
        (convexHull ℝ (Set.range (E.outputs 0))) := by
  have hmem_all :
      ∀ t : Round, ∀ i : Proc n,
        E.outputs t i ∈ convexHull ℝ (Set.range (E.outputs 0)) := by
    intro t
    induction t with
    | zero =>
        intro i
        exact subset_convexHull ℝ (Set.range (E.outputs 0)) ⟨i, rfl⟩
    | succ t iht =>
        intro i
        have hsucc : E.outputs (t + 1) i ∈ Poly E t :=
          output_succ_mem_poly (E := E) t i
        have hValues_subset : Values E t ⊆ convexHull ℝ (Set.range (E.outputs 0)) := by
          intro x hx
          rcases hx with ⟨j, rfl⟩
          exact iht j
        have hPoly_subset : Poly E t ⊆ convexHull ℝ (Set.range (E.outputs 0)) :=
          convexHull_min hValues_subset (convex_convexHull ℝ (Set.range (E.outputs 0)))
        exact hPoly_subset hsucc
  intro i
  refine ⟨?_, ?_⟩
  · refine ⟨E.outputs 0 i, ?_⟩
    exact hmem_all 0 i
  · intro ε hε
    refine ⟨0, ?_⟩
    intro t _ht
    have hmem : E.outputs t i ∈ convexHull ℝ (Set.range (E.outputs 0)) := hmem_all t i
    have hlt :
        Metric.infDist (E.outputs t i) (convexHull ℝ (Set.range (E.outputs 0))) < ε := by
      refine (Metric.infDist_lt_iff ?_).2 ?_
      · exact ⟨E.outputs 0 i, hmem_all 0 i⟩
      · refine ⟨E.outputs t i, hmem, ?_⟩
        simpa using hε
    exact hlt

lemma output_mem_poly_self [NeZero n]
    (E : AveragingExecution (V := V) n)
    (t : Round) (i : Proc n) :
    E.outputs t i ∈ Poly E t := by
  exact subset_convexHull ℝ (Values E t) ⟨i, rfl⟩

lemma poly_succ_subset [NeZero n]
    (E : AveragingExecution (V := V) n)
    (t : Round) :
    Poly E (t + 1) ⊆ Poly E t := by
  have hValues_subset : Values E (t + 1) ⊆ Poly E t := by
    intro x hx
    rcases hx with ⟨i, rfl⟩
    exact output_succ_mem_poly (E := E) t i
  exact convexHull_min hValues_subset (convex_convexHull ℝ (Values E t))

lemma poly_antitone [NeZero n]
    (E : AveragingExecution (V := V) n) :
    Antitone (fun t => Poly E t) := by
  intro t s hts
  induction hts with
  | refl =>
      intro x hx
      simpa using hx
  | @step s _ ih =>
      exact Set.Subset.trans (poly_succ_subset (E := E) (t := s)) ih

section ProjectionHelpers

variable [DecidableEq V]

lemma proj_dist_le_thickness_of_mem_poly [NeZero n]
    (Pi : V →L[ℝ] V)
    (E : AveragingExecution (V := V) n)
    (t : Round)
    {x y : V}
    (hx : x ∈ Poly E t)
    (hy : y ∈ Poly E t) :
    dist (Pi x) (Pi y) ≤ thicknessAt Pi E t := by
  have hXt : (outputSet E t).Nonempty := outputSet_nonempty (E := E) t
  have hbound :
      ‖Pi (x - y)‖ ≤ thicknessOn Pi (outputSet E t) hXt :=
    diffSet_poly_norm_bound (P := Pi) (E := E) (t := t) hXt (x - y)
      ⟨x, hx, y, hy, rfl⟩
  calc
    dist (Pi x) (Pi y) = ‖Pi (x - y)‖ := by
      simp [dist_eq_norm, map_sub]
    _ ≤ thicknessOn Pi (outputSet E t) hXt := hbound
    _ = thicknessAt Pi E t := by
      symm
      exact thicknessAt_eq (P := Pi) (E := E) (t := t) hXt

lemma dist_proj_outputs_le_thickness [NeZero n]
    (Pi : V →L[ℝ] V)
    (E : AveragingExecution (V := V) n)
    (t s : Round)
    (i j : Proc n)
    (hts : t ≤ s) :
    dist (Pi (E.outputs s i)) (Pi (E.outputs t j)) ≤ thicknessAt Pi E t := by
  have hs_mem_poly_t :
      E.outputs s i ∈ Poly E t := by
    exact (poly_antitone (E := E) hts) (output_mem_poly_self (E := E) s i)
  have ht_mem_poly_t :
      E.outputs t j ∈ Poly E t :=
    output_mem_poly_self (E := E) t j
  exact proj_dist_le_thickness_of_mem_poly (Pi := Pi) (E := E) (t := t) hs_mem_poly_t ht_mem_poly_t

end ProjectionHelpers

section ProjectedLimit

variable [DecidableEq V]

lemma projected_ref_cauchy [NeZero n]
    (Pi : V →L[ℝ] V)
    (E : AveragingExecution (V := V) n)
    (i0 : Proc n)
    (hthick : ConvergesTo (fun t => thicknessAt Pi E t) 0) :
    CauchySeq (fun t => Pi (E.outputs t i0)) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  rcases hthick ε hε with ⟨T, hT⟩
  refine ⟨T, ?_⟩
  intro m hm n hn
  rcases le_total m n with hmn | hnm
  · have hdist :
        dist (Pi (E.outputs n i0)) (Pi (E.outputs m i0))
          ≤ thicknessAt Pi E m :=
      dist_proj_outputs_le_thickness (Pi := Pi) (E := E) (t := m) (s := n) (i := i0) (j := i0) hmn
    have hlt : thicknessAt Pi E m < ε := by
      have hnorm : ‖thicknessAt Pi E m - 0‖ < ε := hT m hm
      have habs : |thicknessAt Pi E m| < ε := by
        simpa [Real.norm_eq_abs] using hnorm
      have hnonneg : 0 ≤ thicknessAt Pi E m := thicknessAt_nonneg (P := Pi) (E := E) m
      simpa [abs_of_nonneg hnonneg] using habs
    exact lt_of_le_of_lt (by simpa [dist_comm] using hdist) hlt
  · have hdist :
        dist (Pi (E.outputs m i0)) (Pi (E.outputs n i0))
          ≤ thicknessAt Pi E n :=
      dist_proj_outputs_le_thickness (Pi := Pi) (E := E) (t := n) (s := m) (i := i0) (j := i0) hnm
    have hlt : thicknessAt Pi E n < ε := by
      have hnorm : ‖thicknessAt Pi E n - 0‖ < ε := hT n hn
      have habs : |thicknessAt Pi E n| < ε := by
        simpa [Real.norm_eq_abs] using hnorm
      have hnonneg : 0 ≤ thicknessAt Pi E n := thicknessAt_nonneg (P := Pi) (E := E) n
      simpa [abs_of_nonneg hnonneg] using habs
    exact lt_of_le_of_lt hdist hlt

lemma projected_ref_exists_limit [NeZero n] [CompleteSpace V]
    (Pi : V →L[ℝ] V)
    (E : AveragingExecution (V := V) n)
    (i0 : Proc n)
    (hthick : ConvergesTo (fun t => thicknessAt Pi E t) 0) :
    ∃ cstar : V, ConvergesTo (fun t => Pi (E.outputs t i0)) cstar := by
  have hcauchy :
      CauchySeq (fun t => Pi (E.outputs t i0)) :=
    projected_ref_cauchy (Pi := Pi) (E := E) (i0 := i0) hthick
  rcases cauchySeq_tendsto_of_complete hcauchy with ⟨cstar, hcstar⟩
  exact ⟨cstar, convergesTo_of_tendsto (x := fun t => Pi (E.outputs t i0)) (l := cstar) hcstar⟩

lemma projected_all_converge_to_ref_limit [NeZero n]
    (Pi : V →L[ℝ] V)
    (E : AveragingExecution (V := V) n)
    (i0 : Proc n)
    (cstar : V)
    (hthick : ConvergesTo (fun t => thicknessAt Pi E t) 0)
    (hconvRef : ConvergesTo (fun t => Pi (E.outputs t i0)) cstar) :
    ∀ i : Proc n, ConvergesTo (fun t => Pi (E.outputs t i)) cstar := by
  intro i ε hε
  have hε2 : 0 < ε / 2 := by linarith
  rcases hthick (ε / 2) hε2 with ⟨T1, hT1⟩
  rcases hconvRef (ε / 2) hε2 with ⟨T2, hT2⟩
  refine ⟨max T1 T2, ?_⟩
  intro t ht
  have ht1 : T1 ≤ t := le_trans (le_max_left T1 T2) ht
  have ht2 : T2 ≤ t := le_trans (le_max_right T1 T2) ht
  have hthick_lt : thicknessAt Pi E t < ε / 2 := by
    have hnorm : ‖thicknessAt Pi E t - 0‖ < ε / 2 := hT1 t ht1
    have habs : |thicknessAt Pi E t| < ε / 2 := by
      simpa [Real.norm_eq_abs] using hnorm
    have hnonneg : 0 ≤ thicknessAt Pi E t := thicknessAt_nonneg (P := Pi) (E := E) t
    simpa [abs_of_nonneg hnonneg] using habs
  have href_lt : ‖Pi (E.outputs t i0) - cstar‖ < ε / 2 := by
    simpa using hT2 t ht2
  have hpair_le :
      dist (Pi (E.outputs t i)) (Pi (E.outputs t i0)) ≤ thicknessAt Pi E t :=
    dist_proj_outputs_le_thickness (Pi := Pi) (E := E) (t := t) (s := t) (i := i) (j := i0)
      le_rfl
  have hpair_lt : dist (Pi (E.outputs t i)) (Pi (E.outputs t i0)) < ε / 2 :=
    lt_of_le_of_lt hpair_le hthick_lt
  have href_dist : dist (Pi (E.outputs t i0)) cstar < ε / 2 := by
    simpa [dist_eq_norm] using href_lt
  have htri :
      dist (Pi (E.outputs t i)) cstar
        ≤ dist (Pi (E.outputs t i)) (Pi (E.outputs t i0))
          + dist (Pi (E.outputs t i0)) cstar :=
    dist_triangle _ _ _
  have hdist_lt : dist (Pi (E.outputs t i)) cstar < ε := by
    linarith
  simpa [dist_eq_norm] using hdist_lt

end ProjectedLimit

/--
TeX label: `thm:solving` (full model-grounded form).

For `d ≥ k ≥ 1`, every averaging execution with minimum broadcasting weight `α > 0`
and `k`-broadcastability converges onto a fixed affine subspace of dimension at most `k-1`,
and satisfies validity at limit.
-/
theorem theorem_solving_core [NeZero n]
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
  classical
  letI : DecidableEq V := Classical.decEq V
  rcases lemma_Delta_contraction (V := V) k hk E M α hα_pos hmbw hcard with
    ⟨Pi0, hPiStar0, hkerPi0, hthick0⟩
  rcases (isStarProjection_iff_eq_starProjection.mp hPiStar0) with ⟨K, _hK, hPiEq⟩
  subst Pi0
  let Pi : V →L[ℝ] V := K.starProjection
  have hkerPi : Module.finrank ℝ (LinearMap.ker (Pi : V →ₗ[ℝ] V)) ≤ k - 1 := by
    simpa [Pi] using hkerPi0
  have hthick : ConvergesTo (fun t => thicknessAt Pi E t) 0 := by
    simpa [Pi] using hthick0
  let i0 : Proc n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
  rcases projected_ref_exists_limit (Pi := Pi) (E := E) (i0 := i0) hthick with
    ⟨cstar, hconvRef⟩
  have hconvProj :
      ∀ i : Proc n, ConvergesTo (fun t => Pi (E.outputs t i)) cstar :=
    projected_all_converge_to_ref_limit
      (Pi := Pi) (E := E) (i0 := i0) (cstar := cstar) hthick hconvRef
  let W : AffineSubspace ℝ V := AffineSubspace.mk' cstar (LinearMap.ker (Pi : V →ₗ[ℝ] V))
  refine ⟨W, ?_, ?_, averaging_validityAtLimit (V := V) (n := n) E⟩
  · have hWdir : W.direction = LinearMap.ker (Pi : V →ₗ[ℝ] V) := by
      simp [W, AffineSubspace.direction_mk']
    rw [hWdir]
    exact hkerPi
  · intro i
    refine ⟨?_, ?_⟩
    · refine ⟨cstar, ?_⟩
      simp [W]
    · intro ε hε
      rcases hconvProj i ε hε with ⟨T, hT⟩
      refine ⟨T, ?_⟩
      intro t ht
      have hproj_lt : ‖Pi (E.outputs t i) - cstar‖ < ε := hT t ht
      let w : V := (E.outputs t i - Pi (E.outputs t i)) + cstar
      have hker_eq :
          LinearMap.ker (Pi : V →ₗ[ℝ] V) = Kᗮ := by
        simp [Pi]
      have horth : E.outputs t i - Pi (E.outputs t i) ∈ Kᗮ := by
        simp [Pi]
      have hw_mem : w ∈ W := by
        change w - cstar ∈ LinearMap.ker (Pi : V →ₗ[ℝ] V)
        rw [hker_eq]
        have hwsub : w - cstar = E.outputs t i - Pi (E.outputs t i) := by
          simp [w, sub_eq_add_neg, add_left_comm, add_comm]
        simpa [hwsub] using horth
      have hinf_le :
          Metric.infDist (E.outputs t i) (W : Set V) ≤ dist (E.outputs t i) w :=
        Metric.infDist_le_dist_of_mem hw_mem
      have hdist_eq : dist (E.outputs t i) w = ‖Pi (E.outputs t i) - cstar‖ := by
        have hsub : E.outputs t i - w = Pi (E.outputs t i) - cstar := by
          simp [w, sub_eq_add_neg, add_left_comm, add_comm]
        simp [dist_eq_norm, hsub]
      have hdist_lt : dist (E.outputs t i) w < ε := by
        simpa [hdist_eq] using hproj_lt
      exact lt_of_le_of_lt hinf_le hdist_lt

end ThmSolving
end AsymptoticSubspace

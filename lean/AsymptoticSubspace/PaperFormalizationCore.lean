-- Internal plumbing module.
-- Reader-facing statements live in `Lem*` and `Thm*` files.
import Mathlib

noncomputable section

namespace AsymptoticSubspace
namespace PaperFormalization

section LineAlgebra

def secantLine (b c rb rc : ℝ) : ℝ → ℝ :=
  fun ξ => ((rb - rc) / (c - b)) * (c - ξ) + rc

def zeroLine (b c rb : ℝ) : ℝ → ℝ :=
  fun ξ => (rb / (c - b)) * (c - ξ)

lemma secantLine_at_b (hbc : b < c) (rb rc : ℝ) :
    secantLine b c rb rc b = rb := by
  have hcb : c - b ≠ 0 := sub_ne_zero.mpr (ne_of_gt hbc)
  simp [secantLine, hcb]

lemma secantLine_at_c (_hbc : b < c) (rb rc : ℝ) :
    secantLine b c rb rc c = rc := by
  simp [secantLine]

lemma zeroLine_at_b (hbc : b < c) (rb : ℝ) :
    zeroLine b c rb b = rb := by
  have hcb : c - b ≠ 0 := sub_ne_zero.mpr (ne_of_gt hbc)
  simp [zeroLine, hcb]

lemma zeroLine_at_c (_hbc : b < c) (rb : ℝ) :
    zeroLine b c rb c = 0 := by
  simp [zeroLine]

lemma zeroLine_sub_secant (hbc : b < c) (rb rc ξ : ℝ) :
    zeroLine b c rb ξ - secantLine b c rb rc ξ = rc * (b - ξ) / (c - b) := by
  have hcb : c - b ≠ 0 := sub_ne_zero.mpr (ne_of_gt hbc)
  dsimp [zeroLine, secantLine]
  field_simp [hcb]
  ring_nf

/-- Algebraic core used in the proof of Lemma 6 (`lem:concave:line:zero`), left side. -/
lemma secant_le_zeroLine_of_nonneg
    {b c rb rc ξ : ℝ} (hbc : b < c) (hrc : 0 ≤ rc) (hξ : ξ ≤ b) :
    secantLine b c rb rc ξ ≤ zeroLine b c rb ξ := by
  have hden : 0 < c - b := sub_pos.mpr hbc
  have hbx : 0 ≤ b - ξ := sub_nonneg.mpr hξ
  have hmul : 0 ≤ rc * (b - ξ) / (c - b) := by
    have h1 : 0 ≤ rc * (b - ξ) := mul_nonneg hrc hbx
    exact div_nonneg h1 (le_of_lt hden)
  have hdiff : 0 ≤ zeroLine b c rb ξ - secantLine b c rb rc ξ := by
    simpa [zeroLine_sub_secant hbc rb rc ξ] using hmul
  linarith

/-- Algebraic core used in the proof of Lemma 6 (`lem:concave:line:zero`), right side. -/
lemma zeroLine_le_secant_of_nonneg
    {b c rb rc ξ : ℝ} (hbc : b < c) (hrc : 0 ≤ rc) (hξ : b ≤ ξ) :
    zeroLine b c rb ξ ≤ secantLine b c rb rc ξ := by
  have hden : 0 < c - b := sub_pos.mpr hbc
  have hbx : b - ξ ≤ 0 := sub_nonpos.mpr hξ
  have hmul : rc * (b - ξ) / (c - b) ≤ 0 := by
    have h1 : rc * (b - ξ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hrc hbx
    exact div_nonpos_of_nonpos_of_nonneg h1 (le_of_lt hden)
  have hdiff : zeroLine b c rb ξ - secantLine b c rb rc ξ ≤ 0 := by
    simpa [zeroLine_sub_secant hbc rb rc ξ] using hmul
  linarith

/-- Complete formalization of Lemma `lem:concave:line` from the paper. -/
theorem lemma_concave_line_complete
    {a b c : ℝ} (hab : a < b) (hbc : b < c) {r : ℝ → ℝ}
    (hconc : ConcaveOn ℝ (Set.Icc a c) r) :
    let f := secantLine b c (r b) (r c)
    (∀ ξ ∈ Set.Icc a b, f ξ ≥ r ξ) ∧ (∀ ξ ∈ Set.Icc b c, f ξ ≤ r ξ) := by
  let f := secantLine b c (r b) (r c)
  refine ⟨?_, ?_⟩
  · intro ξ hξ
    rcases hξ with ⟨hξa, hξb⟩
    have hξc : ξ ≤ c := le_trans hξb (le_of_lt hbc)
    have hb_mem : b ∈ Set.Icc a c := ⟨le_of_lt hab, le_of_lt hbc⟩
    have hc_mem : c ∈ Set.Icc a c := ⟨le_of_lt (lt_trans hab hbc), le_rfl⟩
    have hξ_mem : ξ ∈ Set.Icc a c := ⟨hξa, hξc⟩
    have hcx_pos : 0 < c - ξ := sub_pos.mpr (lt_of_le_of_lt hξb hbc)
    let α : ℝ := (b - ξ) / (c - ξ)
    have hα_nonneg : 0 ≤ α := by
      dsimp [α]
      exact div_nonneg (sub_nonneg.mpr hξb) (le_of_lt hcx_pos)
    have hα_le_one : α ≤ 1 := by
      dsimp [α]
      have hnum_le_den : b - ξ ≤ c - ξ := sub_le_sub_right (le_of_lt hbc) ξ
      exact (div_le_iff₀ hcx_pos).2 (by simpa [one_mul] using hnum_le_den)
    have h1mα_nonneg : 0 ≤ 1 - α := sub_nonneg.mpr hα_le_one
    have hsum : (1 - α) + α = 1 := by ring
    have hb_combo : (1 - α) * ξ + α * c = b := by
      have hcx_ne : c - ξ ≠ 0 := ne_of_gt hcx_pos
      dsimp [α]
      field_simp [hcx_ne]
      ring
    have hconc' := hconc.2 hξ_mem hc_mem h1mα_nonneg hα_nonneg hsum
    have hstep : (1 - α) * r ξ + α * r c ≤ r b := by
      simpa [hb_combo, smul_eq_mul] using hconc'
    have h1mα_pos : 0 < 1 - α := by
      have h : α < 1 := by
        dsimp [α]
        exact (div_lt_one hcx_pos).2 (sub_lt_sub_right hbc ξ)
      linarith
    have hsolve : r ξ ≤ (r b - α * r c) / (1 - α) := by
      rw [le_div_iff₀ h1mα_pos]
      linarith [hstep]
    have htarget : (r b - α * r c) / (1 - α) = f ξ := by
      have hcx_ne : c - ξ ≠ 0 := ne_of_gt hcx_pos
      have hcb_ne : c - b ≠ 0 := sub_ne_zero.mpr (ne_of_gt hbc)
      dsimp [f, secantLine, α]
      field_simp [hcx_ne, hcb_ne]
      ring
    linarith [hsolve, htarget]
  · intro ξ hξ
    rcases hξ with ⟨hbξ, hξc⟩
    have hb_mem : b ∈ Set.Icc a c := ⟨le_of_lt hab, le_of_lt hbc⟩
    have hc_mem : c ∈ Set.Icc a c := ⟨le_of_lt (lt_trans hab hbc), le_rfl⟩
    have hξ_mem : ξ ∈ Set.Icc a c := ⟨le_trans (le_of_lt hab) hbξ, hξc⟩
    let β : ℝ := (ξ - b) / (c - b)
    have hβ_nonneg : 0 ≤ β := by
      dsimp [β]
      exact div_nonneg (sub_nonneg.mpr hbξ) (sub_nonneg.mpr (le_of_lt hbc))
    have hβ_le_one : β ≤ 1 := by
      dsimp [β]
      have hnum_le_den : ξ - b ≤ c - b := sub_le_sub_right hξc b
      exact (div_le_one (sub_pos.mpr hbc)).2 hnum_le_den
    have h1mβ_nonneg : 0 ≤ 1 - β := sub_nonneg.mpr hβ_le_one
    have hsum : (1 - β) + β = 1 := by ring
    have hξ_combo : (1 - β) * b + β * c = ξ := by
      have hcb_ne : c - b ≠ 0 := sub_ne_zero.mpr (ne_of_gt hbc)
      dsimp [β]
      field_simp [hcb_ne]
      ring
    have hconc' := hconc.2 hb_mem hc_mem h1mβ_nonneg hβ_nonneg hsum
    have hstep : (1 - β) * r b + β * r c ≤ r ξ := by
      simpa [hξ_combo, smul_eq_mul] using hconc'
    have htarget : f ξ = (1 - β) * r b + β * r c := by
      have hcb_ne : c - b ≠ 0 := sub_ne_zero.mpr (ne_of_gt hbc)
      dsimp [f, secantLine, β]
      field_simp [hcb_ne]
      ring
    linarith [hstep, htarget]

/-- Complete formalization of Lemma `lem:concave:line:zero` from the paper. -/
theorem lemma_concave_line_zero_complete
    {a b c : ℝ} (hab : a < b) (hbc : b < c) {r : ℝ → ℝ}
    (hconc : ConcaveOn ℝ (Set.Icc a c) r)
    (hnonneg : ∀ x ∈ Set.Icc a c, 0 ≤ r x) :
    let g := zeroLine b c (r b)
    (∀ ξ ∈ Set.Icc a b, g ξ ≥ r ξ) ∧ (∀ ξ ∈ Set.Icc b c, g ξ ≤ r ξ) := by
  let f := secantLine b c (r b) (r c)
  let g := zeroLine b c (r b)
  have hline := lemma_concave_line_complete hab hbc hconc
  have hr_c : 0 ≤ r c := hnonneg c ⟨le_of_lt (lt_trans hab hbc), le_rfl⟩
  refine ⟨?_, ?_⟩
  · intro ξ hξ
    have hf_ge : f ξ ≥ r ξ := (hline.1 ξ hξ)
    have hg_ge_f : g ξ ≥ f ξ := by
      exact
        secant_le_zeroLine_of_nonneg
          (b := b) (c := c) (rb := r b) (rc := r c) (ξ := ξ) hbc hr_c hξ.2
    linarith
  · intro ξ hξ
    have hf_le : f ξ ≤ r ξ := (hline.2 ξ hξ)
    have hg_le_f : g ξ ≤ f ξ := by
      exact
        zeroLine_le_secant_of_nonneg
          (b := b) (c := c) (rb := r b) (rc := r c) (ξ := ξ) hbc hr_c hξ.1
    linarith

end LineAlgebra

section BroadcastAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

lemma rewrite_coeff_sum {α w : ℝ} (hα : α ≠ 1) :
    ((w - α) / (1 - α)) + ((1 - w) / (1 - α)) = 1 := by
  have hα' : 1 - α ≠ 0 := sub_ne_zero.mpr (ne_comm.mp hα)
  field_simp [hα']
  ring

lemma rewrite_coeff_left_nonneg {α w : ℝ} (hα : α < 1) (hαw : α ≤ w) :
    0 ≤ (w - α) / (1 - α) := by
  have hnum : 0 ≤ w - α := sub_nonneg.mpr hαw
  have hden : 0 ≤ 1 - α := sub_nonneg.mpr (le_of_lt hα)
  exact div_nonneg hnum hden

lemma rewrite_coeff_right_nonneg {α w : ℝ} (hα : α < 1) (hw : w ≤ 1) :
    0 ≤ (1 - w) / (1 - α) := by
  have hnum : 0 ≤ 1 - w := sub_nonneg.mpr hw
  have hden : 0 ≤ 1 - α := sub_nonneg.mpr (le_of_lt hα)
  exact div_nonneg hnum hden

/-- Algebraic rewriting used in Lemma 8 (`lem:xi_xip`). -/
lemma weighted_rewrite
    {α w : ℝ} (hα : α ≠ 1) (ξ η : V) :
    w • ξ + (1 - w) • η =
      α • ξ + (1 - α) • (((w - α) / (1 - α)) • ξ + ((1 - w) / (1 - α)) • η) := by
  have hα' : 1 - α ≠ 0 := sub_ne_zero.mpr (ne_comm.mp hα)
  calc
    w • ξ + (1 - w) • η
        = (α + (w - α)) • ξ + ((1 - w)) • η := by
          have hwa : α + (w - α) = w := by ring
          conv_rhs => rw [hwa]
    _ = α • ξ + (w - α) • ξ + ((1 - w)) • η := by
      rw [add_smul]
    _ = α • ξ + ((1 - α) * ((w - α) / (1 - α))) • ξ + ((1 - w)) • η := by
      congr 1
      field_simp [hα']
    _ = α • ξ + (1 - α) • (((w - α) / (1 - α)) • ξ) + ((1 - w)) • η := by
      rw [mul_smul]
    _ = α • ξ + (1 - α) • (((w - α) / (1 - α)) • ξ)
          + ((1 - α) * ((1 - w) / (1 - α))) • η := by
      congr 1
      field_simp [hα']
    _ = α • ξ + (1 - α) • (((w - α) / (1 - α)) • ξ)
          + (1 - α) • (((1 - w) / (1 - α)) • η) := by
      rw [mul_smul]
    _ = α • ξ + (1 - α) •
          ((((w - α) / (1 - α)) • ξ) + (((1 - w) / (1 - α)) • η)) := by
      rw [smul_add, add_assoc]

/-- Difference decomposition used in Lemma 9 (`lem:differences`). -/
lemma difference_decomposition
    (α : ℝ) (x₁ x₂ y₁ y₂ : V) :
    (α • x₁ + (1 - α) • x₂) - (α • y₁ + (1 - α) • y₂)
      = α • (x₁ - y₁) + (1 - α) • (x₂ - y₂) := by
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, add_smul, smul_add]

end BroadcastAlgebra

section EasyPaperLemmas

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The set of all differences `x - y` with `x,y ∈ S`. -/
def diffSet (S : Set V) : Set V := {u | ∃ x ∈ S, ∃ y ∈ S, u = x - y}

/-- Complete formalization of the decomposition step in Lemma 8 (`lem:xi_xip`). -/
theorem lemma_xi_xip_complete
    {P : Set V} (hPconv : Convex ℝ P) {α w : ℝ}
    (hα_lt_one : α < 1)
    (hαw : α ≤ w) (hw_le_one : w ≤ 1)
    {ξ η : V} (hξ : ξ ∈ P) (hη : η ∈ P) :
    ∃ ξ' ∈ P, w • ξ + (1 - w) • η = α • ξ + (1 - α) • ξ' := by
  let β : ℝ := (w - α) / (1 - α)
  let γ : ℝ := (1 - w) / (1 - α)
  have hβ_nonneg : 0 ≤ β := by
    simpa [β] using rewrite_coeff_left_nonneg (α := α) (w := w) hα_lt_one hαw
  have hγ_nonneg : 0 ≤ γ := by
    simpa [γ] using rewrite_coeff_right_nonneg (α := α) (w := w) hα_lt_one hw_le_one
  have hα_ne : α ≠ 1 := by linarith
  have hβγ : β + γ = 1 := by
    simpa [β, γ] using rewrite_coeff_sum (α := α) (w := w) hα_ne
  let ξ' : V := β • ξ + γ • η
  have hξ' : ξ' ∈ P := by
    exact hPconv hξ hη hβ_nonneg hγ_nonneg hβγ
  refine ⟨ξ', hξ', ?_⟩
  calc
    w • ξ + (1 - w) • η
        = α • ξ + (1 - α) • (((w - α) / (1 - α)) • ξ + ((1 - w) / (1 - α)) • η) := by
            simpa using weighted_rewrite (V := V) (α := α) (w := w) hα_ne ξ η
    _ = α • ξ + (1 - α) • ξ' := by
      simp [ξ', β, γ]

/-- Complete formalization of Lemma 9 (`lem:differences`) once two decompositions are given. -/
theorem lemma_differences_complete
    {S P : Set V} {α : ℝ}
    {xᵢ xⱼ ξᵢ ξⱼ ηᵢ ηⱼ : V}
    (hxᵢ : xᵢ = α • ξᵢ + (1 - α) • ηᵢ)
    (hxⱼ : xⱼ = α • ξⱼ + (1 - α) • ηⱼ)
    (hξᵢ : ξᵢ ∈ S) (hξⱼ : ξⱼ ∈ S)
    (hηᵢ : ηᵢ ∈ P) (hηⱼ : ηⱼ ∈ P) :
    ∃ uParallel ∈ diffSet S,
      ∃ uRes ∈ diffSet P,
        xᵢ - xⱼ = α • uParallel + (1 - α) • uRes := by
  refine ⟨ξᵢ - ξⱼ, ?_, ηᵢ - ηⱼ, ?_, ?_⟩
  · exact ⟨ξᵢ, hξᵢ, ξⱼ, hξⱼ, rfl⟩
  · exact ⟨ηᵢ, hηᵢ, ηⱼ, hηⱼ, rfl⟩
  · calc
      xᵢ - xⱼ
          = (α • ξᵢ + (1 - α) • ηᵢ) - (α • ξⱼ + (1 - α) • ηⱼ) := by
              simp [hxᵢ, hxⱼ]
      _ = α • (ξᵢ - ξⱼ) + (1 - α) • (ηᵢ - ηⱼ) := by
            simpa using difference_decomposition (V := V) α ξᵢ ηᵢ ξⱼ ηⱼ

end EasyPaperLemmas

section LowerBound

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/--
Complete formalization of the geometric contradiction used in Theorem `lem:imposs`:
`s + 2` affinely independent limit points cannot all lie in an affine subspace of dimension `s`.
-/
theorem lemma_imposs_complete
    {ι : Type*} [Fintype ι] {s : Nat}
    (xLim : ι → V)
    (hcard : Fintype.card ι = s + 2)
    (hAff : AffineIndependent ℝ xLim) :
    ¬ ∃ E : AffineSubspace ℝ V,
      FiniteDimensional ℝ E.direction ∧
      Module.finrank ℝ E.direction ≤ s ∧
      (Set.range xLim) ⊆ (E : Set V) := by
  intro hE
  rcases hE with ⟨E, hfdim, hdim, hsubset⟩
  letI : FiniteDimensional ℝ E.direction := hfdim
  have hspan_le : affineSpan ℝ (Set.range xLim) ≤ E := affineSpan_le.mpr hsubset
  have hdir_le : vectorSpan ℝ (Set.range xLim) ≤ E.direction := by
    have hdir_le' : (affineSpan ℝ (Set.range xLim)).direction ≤ E.direction :=
    AffineSubspace.direction_le hspan_le
    simpa [direction_affineSpan] using hdir_le'
  have hfinrank_le : Module.finrank ℝ (vectorSpan ℝ (Set.range xLim)) ≤ s :=
    le_trans (Submodule.finrank_mono hdir_le) hdim
  have hcard_le :
      Fintype.card ι ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range xLim)) + 1 :=
    AffineIndependent.card_le_finrank_succ (k := ℝ) (p := xLim) hAff
  have hcard_le' : Fintype.card ι ≤ s + 1 :=
    le_trans hcard_le (Nat.succ_le_succ hfinrank_le)
  have hs : s + 2 ≤ s + 1 := by
    omega
  exact Nat.not_succ_le_self (s + 1) hs

end LowerBound

section HalfspaceDistance

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/--
Complete formalization of Lemma `lem:halfspace:distance:formula` from the paper:
for the open half-space `H = {h | ⟪h - q, v⟫ < 0}`, the point-to-set distance from
`z ∉ H` is `⟪z - q, v⟫ / ‖v‖`.
-/
theorem lemma_halfspace_distance_formula
    {q v z : V} (hv : v ≠ 0)
    (hz : z ∉ {h : V | inner ℝ (h - q) v < 0}) :
    Metric.infDist z {h : V | inner ℝ (h - q) v < 0} = inner ℝ (z - q) v / ‖v‖ := by
  let H : Set V := {h : V | inner ℝ (h - q) v < 0}
  have hvnorm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hvnorm_ne : ‖v‖ ≠ 0 := ne_of_gt hvnorm_pos
  have hvnormsq_pos : 0 < ‖v‖ ^ 2 := sq_pos_of_pos hvnorm_pos
  have hz_nonneg : 0 ≤ inner ℝ (z - q) v := by
    exact le_of_not_gt (by simpa [H] using hz)
  have hH_nonempty : H.Nonempty := by
    refine ⟨q - v, ?_⟩
    have : inner ℝ ((q - v) - q) v = -‖v‖ ^ 2 := by
      simp
    change inner ℝ ((q - v) - q) v < 0
    refine this.trans_lt ?_
    linarith
  have hlower :
      inner ℝ (z - q) v / ‖v‖ ≤ Metric.infDist z H := by
    refine (Metric.le_infDist hH_nonempty).2 ?_
    intro h hh
    have hh' : inner ℝ (h - q) v < 0 := by simpa [H] using hh
    have hdecomp : inner ℝ (z - h) v = inner ℝ (z - q) v - inner ℝ (h - q) v := by
      have hzhs : z - h = (z - q) - (h - q) := by abel_nf
      rw [hzhs, inner_sub_left]
    have hinner_lt : inner ℝ (z - q) v < inner ℝ (z - h) v := by
      rw [hdecomp]
      linarith
    have hcs : inner ℝ (z - h) v ≤ ‖z - h‖ * ‖v‖ := real_inner_le_norm _ _
    have hmul : inner ℝ (z - q) v ≤ ‖z - h‖ * ‖v‖ := (lt_of_lt_of_le hinner_lt hcs).le
    have hdist : inner ℝ (z - q) v / ‖v‖ ≤ ‖z - h‖ := by
      exact (div_le_iff₀ hvnorm_pos).2 (by simpa [mul_comm] using hmul)
    simpa [dist_eq_norm] using hdist
  have hupper : Metric.infDist z H ≤ inner ℝ (z - q) v / ‖v‖ := by
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    let δ : ℝ := ε / ‖v‖
    have hδ_pos : 0 < δ := by
      exact div_pos hε hvnorm_pos
    let hδ : V := z - ((inner ℝ (z - q) v / ‖v‖ ^ 2 + δ) • v)
    have hhδ_mem : hδ ∈ H := by
      change inner ℝ (hδ - q) v < 0
      have hinner_hδ :
          inner ℝ (hδ - q) v = -δ * ‖v‖ ^ 2 := by
        dsimp [hδ]
        calc
          inner ℝ ((z - ((inner ℝ (z - q) v / ‖v‖ ^ 2 + δ) • v)) - q) v
              = inner ℝ (z - q) v - (inner ℝ (z - q) v / ‖v‖ ^ 2 + δ) * ‖v‖ ^ 2 := by
                  simp [inner_sub_left, inner_smul_left, mul_comm]
                  ring
          _ = -δ * ‖v‖ ^ 2 := by
                field_simp [hvnorm_ne]
                ring
      rw [hinner_hδ]
      nlinarith [hδ_pos, hvnormsq_pos]
    have hdist_eq :
        dist z hδ = inner ℝ (z - q) v / ‖v‖ + ε := by
      have hcoeff_nonneg : 0 ≤ inner ℝ (z - q) v / ‖v‖ ^ 2 + δ := by
        exact add_nonneg (div_nonneg hz_nonneg (sq_nonneg ‖v‖)) hδ_pos.le
      dsimp [hδ]
      calc
        dist z (z - ((inner ℝ (z - q) v / ‖v‖ ^ 2 + δ) • v))
            = ‖(inner ℝ (z - q) v / ‖v‖ ^ 2 + δ) • v‖ := by
                simp
        _ = |inner ℝ (z - q) v / ‖v‖ ^ 2 + δ| * ‖v‖ := by
              simp [norm_smul]
        _ = (inner ℝ (z - q) v / ‖v‖ ^ 2 + δ) * ‖v‖ := by
              rw [abs_of_nonneg hcoeff_nonneg]
        _ = (inner ℝ (z - q) v / ‖v‖ ^ 2) * ‖v‖ + δ * ‖v‖ := by ring
        _ = inner ℝ (z - q) v / ‖v‖ + ε := by
              have h₁ : (inner ℝ (z - q) v / ‖v‖ ^ 2) * ‖v‖ = inner ℝ (z - q) v / ‖v‖ := by
                field_simp [hvnorm_ne]
              have h₂ : δ * ‖v‖ = ε := by
                dsimp [δ]
                field_simp [hvnorm_ne]
              rw [h₁, h₂]
    calc
      Metric.infDist z H ≤ dist z hδ := Metric.infDist_le_dist_of_mem hhδ_mem
      _ = inner ℝ (z - q) v / ‖v‖ + ε := hdist_eq
  simpa [H] using le_antisymm hupper hlower

end HalfspaceDistance

section ConvexZeroHyperplane

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

/--
Formalization of paper lemma `lem:convex:zero:hyperplane`.

Mathlib-friendly statement: a convex set has zero Lebesgue volume iff it is contained in a proper
affine subspace (`E ≠ ⊤`).
-/
theorem lemma_convex_zero_hyperplane
    {C : Set V} (hCconv : Convex ℝ C) :
    (∃ E : AffineSubspace ℝ V, E ≠ ⊤ ∧ C ⊆ E) ↔ MeasureTheory.volume C = 0 := by
  constructor
  · rintro ⟨E, hEne, hCE⟩
    have hEzero : MeasureTheory.volume (E : Set V) = 0 :=
      MeasureTheory.Measure.addHaar_affineSubspace MeasureTheory.volume E hEne
    exact MeasureTheory.measure_mono_null hCE hEzero
  · intro hCzero
    have hIntEmpty : interior C = ∅ := by
      by_contra hIntNonempty
      have hIntNe : (interior C).Nonempty := Set.nonempty_iff_ne_empty.mpr hIntNonempty
      have hIntPos : 0 < MeasureTheory.volume (interior C) :=
        IsOpen.measure_pos MeasureTheory.volume isOpen_interior hIntNe
      have hCpos : 0 < MeasureTheory.volume C :=
        lt_of_lt_of_le hIntPos (MeasureTheory.measure_mono interior_subset)
      rw [hCzero] at hCpos
      exact lt_irrefl 0 hCpos
    have hSpanNeTop : affineSpan ℝ C ≠ ⊤ := by
      intro hSpanTop
      have hIntNe : (interior C).Nonempty :=
        (hCconv.interior_nonempty_iff_affineSpan_eq_top).2 hSpanTop
      exact Set.nonempty_iff_ne_empty.mp hIntNe hIntEmpty
    exact ⟨affineSpan ℝ C, hSpanNeTop, subset_affineSpan ℝ C⟩

end ConvexZeroHyperplane

section AccumulationPoint

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- Orthogonal projections on `V`, represented as star projections in `V →L[ℝ] V`. -/
def orthogonalProjections : Set (V →L[ℝ] V) := {P | IsStarProjection P}

/--
Formalization of paper lemma `lem:accumulation_point`.

Given a sequence of orthogonal projections, there exists a subsequence converging to an
orthogonal projection (hence the sequence has an accumulation point in this set).
-/
theorem lemma_accumulation_point
    (PiSeq : ℕ → V →L[ℝ] V)
    (hPi : ∀ t, IsStarProjection (PiSeq t)) :
    ∃ P : V →L[ℝ] V, IsStarProjection P ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Filter.Tendsto (PiSeq ∘ φ) Filter.atTop (nhds P) := by
  let S : Set (V →L[ℝ] V) := orthogonalProjections
  have hclosed_idem : IsClosed {P : V →L[ℝ] V | IsIdempotentElem P} := by
    simpa [IsIdempotentElem] using
      (isClosed_eq (continuous_id.mul continuous_id) continuous_id)
  have hclosed_selfAdj : IsClosed {P : V →L[ℝ] V | IsSelfAdjoint P} := by
    simpa [IsSelfAdjoint] using
      (isClosed_eq (continuous_id.star) continuous_id)
  have hclosedS : IsClosed S := by
    simpa [S, orthogonalProjections, isStarProjection_iff, Set.setOf_and] using
      hclosed_idem.inter hclosed_selfAdj
  have hsubset_ball : S ⊆ Metric.closedBall (0 : V →L[ℝ] V) 1 := by
    intro P hP
    rcases (isStarProjection_iff_eq_starProjection.mp hP) with ⟨K, _hK, rfl⟩
    simpa [Metric.mem_closedBall, dist_eq_norm] using (Submodule.starProjection_norm_le K)
  have hcompactS : IsCompact S :=
    (ProperSpace.isCompact_closedBall (0 : V →L[ℝ] V) 1).of_isClosed_subset hclosedS hsubset_ball
  obtain ⟨P, hPS, φ, hφmono, hφtendsto⟩ := IsCompact.tendsto_subseq hcompactS (fun t => hPi t)
  exact ⟨P, hPS, φ, hφmono, hφtendsto⟩

end AccumulationPoint

section Volumes

/-- Left-truncated profile used in Lemma 7 (`lem:volumes`). -/
def rLeft (r : ℝ → ℝ) (h α : ℝ) : ℝ → ℝ :=
  fun ξ => if ξ ∈ Set.Icc 0 ((1 - α) * h) then r ξ else 0

/-- Right-truncated profile used in Lemma 7 (`lem:volumes`). -/
def rRight (r : ℝ → ℝ) (h α : ℝ) : ℝ → ℝ :=
  fun ξ => if ξ ∈ Set.Icc ((1 - α) * h) h then r ξ else 0

/-- Dimensional normalizing constant `C_{d-1} = π^((d-1)/2) / Γ((d-1)/2 + 1)`. -/
def C_dMinusOne (d : ℕ) : ℝ :=
  Real.rpow Real.pi ((((d - 1 : ℕ) : ℝ) / 2)) /
    Real.Gamma ((((d - 1 : ℕ) : ℝ) / 2) + 1)

/--
Formalization target for paper Lemma 7 (`lem:volumes`).

This statement records the two integral bounds proved from the linear majorant/minorant
constructed in Lemma 6 (`lem:concave:line:zero`).
-/
theorem lemma_volumes
    {d : ℕ} (hd : 1 ≤ d)
    {h α : ℝ} (hh : 0 < h) (hα0 : 0 < α) (hα1 : α < 1)
    {r : ℝ → ℝ}
    (_hmeas : Measurable r)
    (hconc : ConcaveOn ℝ (Set.Icc 0 h) r)
    (hnonneg : ∀ ξ ∈ Set.Icc 0 h, 0 ≤ r ξ)
    (hIntLeft : IntervalIntegrable (fun ξ => (r ξ) ^ (d - 1)) MeasureTheory.volume 0 ((1 - α) * h))
    (hIntRight :
      IntervalIntegrable (fun ξ => (r ξ) ^ (d - 1)) MeasureTheory.volume ((1 - α) * h) h) :
    let r0 := r ((1 - α) * h)
    let C := C_dMinusOne d
    (∫ ξ in 0..((1 - α) * h), C * (r ξ) ^ (d - 1)
      ≤ C * r0 ^ (d - 1) * h / (α ^ (d - 1) * (d : ℝ)) * (1 - α ^ d)) ∧
    (C * r0 ^ (d - 1) * h / (α ^ (d - 1) * (d : ℝ)) * (α ^ d)
      ≤ ∫ ξ in ((1 - α) * h)..h, C * (r ξ) ^ (d - 1)) := by
  let b : ℝ := (1 - α) * h
  let n : ℕ := d - 1
  let r0 : ℝ := r b
  let g : ℝ → ℝ := zeroLine b h r0
  have hb_pos : 0 < b := by
    dsimp [b]
    nlinarith
  have hb_le_h : b ≤ h := by
    dsimp [b]
    nlinarith
  have hbh : b < h := by
    dsimp [b]
    nlinarith
  have hline := lemma_concave_line_zero_complete
    (a := 0) (b := b) (c := h) hb_pos hbh hconc hnonneg
  have hleft_bound : ∀ ξ ∈ Set.Icc 0 b, r ξ ≤ g ξ := by
    intro ξ hξ
    simpa [g] using (hline.1 ξ hξ)
  have hright_bound : ∀ ξ ∈ Set.Icc b h, g ξ ≤ r ξ := by
    intro ξ hξ
    simpa [g] using (hline.2 ξ hξ)
  have hpow_left : ∀ ξ ∈ Set.Icc 0 b, (r ξ) ^ n ≤ (g ξ) ^ n := by
    intro ξ hξ
    have hr_nonneg : 0 ≤ r ξ := hnonneg ξ ⟨hξ.1, le_trans hξ.2 hb_le_h⟩
    exact pow_le_pow_left₀ hr_nonneg (hleft_bound ξ hξ) n
  have hpow_right : ∀ ξ ∈ Set.Icc b h, (g ξ) ^ n ≤ (r ξ) ^ n := by
    intro ξ hξ
    have hr_nonneg : 0 ≤ r ξ := hnonneg ξ ⟨le_trans (le_of_lt hb_pos) hξ.1, hξ.2⟩
    have hr0_nonneg : 0 ≤ r0 := hnonneg b ⟨le_of_lt hb_pos, hb_le_h⟩
    have hden_pos : 0 < h - b := sub_pos.mpr hbh
    have hg_nonneg : 0 ≤ g ξ := by
      dsimp [g, zeroLine]
      refine mul_nonneg (div_nonneg hr0_nonneg hden_pos.le) ?_
      exact sub_nonneg.mpr hξ.2
    exact pow_le_pow_left₀ hg_nonneg (hright_bound ξ hξ) n
  have hg_cont : Continuous g := by
    dsimp [g, zeroLine]
    exact continuous_const.mul (continuous_const.sub continuous_id)
  have hg_int_left : IntervalIntegrable (fun ξ => (g ξ) ^ n) MeasureTheory.volume 0 b :=
    (hg_cont.pow n).intervalIntegrable 0 b
  have hg_int_right : IntervalIntegrable (fun ξ => (g ξ) ^ n) MeasureTheory.volume b h :=
    (hg_cont.pow n).intervalIntegrable b h
  have hr_int_left : IntervalIntegrable (fun ξ => (r ξ) ^ n) MeasureTheory.volume 0 b := by
    simpa [n, b] using hIntLeft
  have hr_int_right : IntervalIntegrable (fun ξ => (r ξ) ^ n) MeasureTheory.volume b h := by
    simpa [n, b] using hIntRight
  have hint_left_cmp :
      ∫ ξ in 0..b, (r ξ) ^ n ≤ ∫ ξ in 0..b, (g ξ) ^ n := by
    refine intervalIntegral.integral_mono_on (a := 0) (b := b) hb_pos.le hr_int_left hg_int_left ?_
    intro ξ hξ
    exact hpow_left ξ hξ
  have hint_right_cmp :
      ∫ ξ in b..h, (g ξ) ^ n ≤ ∫ ξ in b..h, (r ξ) ^ n := by
    refine intervalIntegral.integral_mono_on (a := b) (b := h) hb_le_h hg_int_right hr_int_right ?_
    intro ξ hξ
    exact hpow_right ξ hξ
  have hsub : h - b = α * h := by
    dsimp [b]
    ring
  have hg_formula : ∀ ξ, g ξ = (r0 / (α * h)) * (h - ξ) := by
    intro ξ
    simp [g, zeroLine, hsub]
  have hpow_left_exact :
      ∫ ξ in 0..b, (g ξ) ^ n = (r0 / (α * h)) ^ n * ∫ ξ in 0..b, (h - ξ) ^ n := by
    have hfun :
        (fun ξ => (g ξ) ^ n) = (fun ξ => (r0 / (α * h)) ^ n * (h - ξ) ^ n) := by
      funext ξ
      rw [hg_formula ξ, mul_pow]
    rw [hfun, intervalIntegral.integral_const_mul]
  have hpow_right_exact :
      ∫ ξ in b..h, (g ξ) ^ n = (r0 / (α * h)) ^ n * ∫ ξ in b..h, (h - ξ) ^ n := by
    have hfun :
        (fun ξ => (g ξ) ^ n) = (fun ξ => (r0 / (α * h)) ^ n * (h - ξ) ^ n) := by
      funext ξ
      rw [hg_formula ξ, mul_pow]
    rw [hfun, intervalIntegral.integral_const_mul]
  have hn1 : n + 1 = d := by
    dsimp [n]
    omega
  have hcast : (n : ℝ) + 1 = (d : ℝ) := by
    exact_mod_cast hn1
  have hd_ne_zero_nat : d ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hpow_int_left :
      ∫ ξ in 0..b, (h - ξ) ^ n = (h ^ d - (α * h) ^ d) / (d : ℝ) := by
    calc
      ∫ ξ in 0..b, (h - ξ) ^ n
          = ∫ x in (h - b)..h, x ^ n := by
              simpa using (intervalIntegral.integral_comp_sub_left
                (f := fun x : ℝ => x ^ n) (a := 0) (b := b) (d := h))
      _ = (h ^ (n + 1) - (h - b) ^ (n + 1)) / (n + 1) := by
            simp [sub_eq_add_neg, add_comm]
      _ = (h ^ d - (α * h) ^ d) / (d : ℝ) := by
            simp [hsub, hn1, hcast]
  have hpow_int_right :
      ∫ ξ in b..h, (h - ξ) ^ n = ((α * h) ^ d) / (d : ℝ) := by
    calc
      ∫ ξ in b..h, (h - ξ) ^ n
          = ∫ x in 0..(h - b), x ^ n := by
              simpa [sub_eq_add_neg] using (intervalIntegral.integral_comp_sub_left
                (f := fun x : ℝ => x ^ n) (a := b) (b := h) (d := h))
      _ = ((h - b) ^ (n + 1) - 0 ^ (n + 1)) / (n + 1) := by
            simp [sub_eq_add_neg, add_comm]
      _ = ((α * h) ^ d) / (d : ℝ) := by
            simp [hsub, hn1, hcast, hd_ne_zero_nat]
  have hC_nonneg : 0 ≤ C_dMinusOne d := by
    have harg_nonneg : 0 ≤ (((d - 1 : ℕ) : ℝ) / 2) := by positivity
    have harg_pos : 0 < (((d - 1 : ℕ) : ℝ) / 2) + 1 := by linarith
    have hgamma_pos : 0 < Real.Gamma ((((d - 1 : ℕ) : ℝ) / 2) + 1) := by
      exact Real.Gamma_pos_of_pos harg_pos
    have hrpow_nonneg : 0 ≤ Real.rpow Real.pi ((((d - 1 : ℕ) : ℝ) / 2)) := by
      exact Real.rpow_nonneg Real.pi_pos.le _
    exact div_nonneg hrpow_nonneg hgamma_pos.le
  have hd_ne_zero : (d : ℝ) ≠ 0 := by
    exact_mod_cast hd_ne_zero_nat
  have hα_ne : α ≠ 0 := ne_of_gt hα0
  have hh_ne : h ≠ 0 := ne_of_gt hh
  have hhα_ne : h * α ≠ 0 := mul_ne_zero hh_ne hα_ne
  have hαh_ne : α * h ≠ 0 := mul_ne_zero (ne_of_gt hα0) (ne_of_gt hh)
  have hleft_explicit :
      ∫ ξ in 0..b, (g ξ) ^ n =
        r0 ^ (d - 1) * h / (α ^ (d - 1) * (d : ℝ)) * (1 - α ^ d) := by
    rw [hpow_left_exact, hpow_int_left]
    dsimp [n]
    have hmulpow : (α * h) ^ d = α ^ d * h ^ d := by rw [mul_pow]
    have hdivpow : (r0 / (α * h)) ^ (d - 1) = r0 ^ (d - 1) / (α * h) ^ (d - 1) := by
      rw [div_pow]
    rw [hmulpow, hdivpow]
    field_simp [hαh_ne, hhα_ne, hα_ne, hh_ne, hd_ne_zero]
    have hhpow : h ^ d = h * h ^ (d - 1) := by
      cases d with
      | zero =>
          exact (hd_ne_zero_nat rfl).elim
      | succ k =>
          calc
            h ^ (Nat.succ k) = h ^ k * h := by simp [pow_succ]
            _ = h * h ^ k := by ring
    rw [hhpow]
    ring
  have hright_explicit :
      ∫ ξ in b..h, (g ξ) ^ n =
        r0 ^ (d - 1) * h / (α ^ (d - 1) * (d : ℝ)) * (α ^ d) := by
    rw [hpow_right_exact, hpow_int_right]
    dsimp [n]
    have hmulpow : (α * h) ^ d = α ^ d * h ^ d := by rw [mul_pow]
    have hdivpow : (r0 / (α * h)) ^ (d - 1) = r0 ^ (d - 1) / (α * h) ^ (d - 1) := by
      rw [div_pow]
    rw [hmulpow, hdivpow]
    field_simp [hαh_ne, hhα_ne, hα_ne, hh_ne, hd_ne_zero]
    have hhpow : h ^ d = h * h ^ (d - 1) := by
      cases d with
      | zero =>
          exact (hd_ne_zero_nat rfl).elim
      | succ k =>
          calc
            h ^ (Nat.succ k) = h ^ k * h := by simp [pow_succ]
            _ = h * h ^ k := by ring
    rw [hhpow]
    ring
  refine ⟨?_, ?_⟩
  · calc
      ∫ ξ in 0..b, C_dMinusOne d * (r ξ) ^ (d - 1)
          = C_dMinusOne d * ∫ ξ in 0..b, (r ξ) ^ n := by
              simp [n, intervalIntegral.integral_const_mul]
      _ ≤ C_dMinusOne d * ∫ ξ in 0..b, (g ξ) ^ n := by
            gcongr
      _ = C_dMinusOne d *
          (r0 ^ (d - 1) * h / (α ^ (d - 1) * (d : ℝ)) * (1 - α ^ d)) := by
            rw [hleft_explicit]
      _ = C_dMinusOne d * r0 ^ (d - 1) * h / (α ^ (d - 1) * (d : ℝ)) * (1 - α ^ d) := by
            ring
  · calc
      C_dMinusOne d * r0 ^ (d - 1) * h / (α ^ (d - 1) * (d : ℝ)) * (α ^ d)
          = C_dMinusOne d * ∫ ξ in b..h, (g ξ) ^ n := by
              rw [hright_explicit]
              ring
      _ ≤ C_dMinusOne d * ∫ ξ in b..h, (r ξ) ^ n := by
            gcongr
      _ = ∫ ξ in b..h, C_dMinusOne d * (r ξ) ^ (d - 1) := by
            simp [n, intervalIntegral.integral_const_mul]

end Volumes

end PaperFormalization
end AsymptoticSubspace

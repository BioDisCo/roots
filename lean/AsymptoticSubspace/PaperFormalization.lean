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

end PaperFormalization
end AsymptoticSubspace

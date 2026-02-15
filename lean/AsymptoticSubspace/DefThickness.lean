-- TeX label: def:thickness
-- Definitions of pairDiameter and thicknessOn (projection-based thickness).

import AsymptoticSubspace.ModelBridgeCore

namespace AsymptoticSubspace

def pairDiameter
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (X : Finset V) (hX : X.Nonempty) : ℝ :=
  (X.product X).sup'
    (by
      rcases hX with ⟨x, hx⟩
      exact ⟨(x, x), by simp [hx]⟩)
    (fun p => ‖p.1 - p.2‖)

def thicknessOn
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (P : V →L[ℝ] V)
    (X : Finset V) (hX : X.Nonempty) : ℝ :=
  (X.product X).sup'
    (by
      rcases hX with ⟨x, hx⟩
      exact ⟨(x, x), by simp [hx]⟩)
    (fun p => ‖P (p.1 - p.2)‖)

section Verification

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Verification anchor: local pair-diameter formula matches the model bridge definition. -/
@[simp] theorem pairDiameter_eq_modelLemmas
    (X : Finset V) (hX : X.Nonempty) :
    pairDiameter X hX = ModelLemmas.pairDiameter X hX :=
  rfl

/-- Verification anchor: local thickness formula matches the model bridge definition. -/
@[simp] theorem thicknessOn_eq_modelLemmas
    (P : V →L[ℝ] V)
    (X : Finset V) (hX : X.Nonempty) :
    thicknessOn P X hX = ModelLemmas.thicknessOn P X hX :=
  rfl

end Verification

end AsymptoticSubspace

-- Formalization of the computational model (Section 2).
-- TeX label: sec:model

import AsymptoticSubspace.ComputationalModelCore

namespace AsymptoticSubspace

abbrev Round : Type := ComputationalModel.Round
abbrev Proc (n : Nat) : Type := ComputationalModel.Proc n
abbrev CommGraph (n : Nat) : Type := ComputationalModel.CommGraph n

/--
Reader-facing expansion of a communication graph:
an edge relation plus mandatory self-loops.
-/
def CommGraphSpec (n : Nat) : Type :=
  { edge : Proc n → Proc n → Prop // ∀ i : Proc n, edge i i }

def InNeighbors {n : Nat} (G : CommGraph n) (i : Proc n) : Set (Proc n) :=
  {j | G.edge j i}

def Reachable {n : Nat} (G : CommGraph n) : Proc n → Proc n → Prop :=
  Relation.ReflTransGen G.edge

def IsRootSet {n : Nat} (G : CommGraph n) (R : Finset (Proc n)) : Prop :=
  ∀ i : Proc n, ∃ j : Proc n, j ∈ R ∧ Reachable G j i

def IsKRooted {n : Nat} (G : CommGraph n) (k : Nat) : Prop :=
  ∃ R : Finset (Proc n), R.card ≤ k ∧ IsRootSet G R

abbrev ObliviousMessageAdversary (n : Nat) : Type := ComputationalModel.ObliviousMessageAdversary n

def IsKRootedAdversary {n : Nat} (N : ObliviousMessageAdversary n) (k : Nat) : Prop :=
  ∀ G : CommGraph n, G ∈ N.graphs → IsKRooted G k

abbrev AveragingExecution
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : Nat) :=
  ComputationalModel.AveragingExecution (V := V) n

abbrev DeterministicAlgorithm
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : Nat) :=
  ComputationalModel.DeterministicAlgorithm V n

def AdmissibleTrace {n : Nat}
    (N : ObliviousMessageAdversary n) (Gseq : Round → CommGraph n) : Prop :=
  ∀ t : Round, Gseq t ∈ N.graphs

def ConvergesTo
    {V : Type*} [NormedAddCommGroup V]
    (x : Round → V) (l : V) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ T : Round, ∀ t : Round, T ≤ t → ‖x t - l‖ < ε

def ConvergesToSet
    {V : Type*} [NormedAddCommGroup V]
    (x : Round → V) (S : Set V) : Prop :=
  S.Nonempty ∧
    (∀ ε : ℝ, 0 < ε → ∃ T : Round, ∀ t : Round, T ≤ t → Metric.infDist (x t) S < ε)

def ValidityAtLimit
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : Nat}
    (init limits : Proc n → V) : Prop :=
  ∀ i : Proc n, limits i ∈ convexHull ℝ (Set.range init)

def SubspaceAgreementAtLimit
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : Nat}
    (s : Nat) (limits : Proc n → V) : Prop :=
  ∃ E : AffineSubspace ℝ V,
    FiniteDimensional ℝ E.direction ∧
    Module.finrank ℝ E.direction ≤ s ∧
    ∀ i : Proc n, limits i ∈ (E : Set V)

def SolvesAsymptoticSubspace
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : Nat}
    (A : ComputationalModel.DeterministicAlgorithm V n)
    (N : ObliviousMessageAdversary n) (s : Nat) : Prop :=
  ∀ (Gseq : Round → CommGraph n) (init : Proc n → V),
    AdmissibleTrace N Gseq →
    ∃ E : AffineSubspace ℝ V,
      FiniteDimensional ℝ E.direction ∧
      Module.finrank ℝ E.direction ≤ s ∧
      (∀ i : Proc n, ConvergesToSet (fun t => (A.run Gseq init t) i) (E : Set V)) ∧
      (∀ i : Proc n,
        ConvergesToSet (fun t => (A.run Gseq init t) i) (convexHull ℝ (Set.range init)))

def SolvesAsymptoticSubspaceWithLimits
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : Nat}
    (A : ComputationalModel.DeterministicAlgorithm V n)
    (N : ObliviousMessageAdversary n) (s : Nat) : Prop :=
  ∀ (Gseq : Round → CommGraph n) (init : Proc n → V),
    AdmissibleTrace N Gseq →
    ∃ limits : Proc n → V,
      (∀ i : Proc n, ConvergesTo (fun t => (A.run Gseq init t) i) (limits i)) ∧
      ValidityAtLimit init limits ∧
      SubspaceAgreementAtLimit s limits

section Verification

variable {V : Type*} [NormedAddCommGroup V]
variable {n : Nat}

/-- Verification anchor: round index is exactly `Nat`. -/
@[simp] theorem round_eq_nat : Round = Nat := rfl

/-- Verification anchor: process type is exactly `Fin n`. -/
@[simp] theorem proc_eq_fin (n : Nat) : Proc n = Fin n := rfl

/-- Convert a core graph to its reader-facing edge/self-loop specification. -/
def commGraphToSpec (G : CommGraph n) : CommGraphSpec n :=
  ⟨G.edge, G.self_loop⟩

/-- Build a core graph from the reader-facing edge/self-loop specification. -/
def commGraphFromSpec (S : CommGraphSpec n) : CommGraph n :=
  { edge := S.val, self_loop := S.property }

/-- Verification anchor: `CommGraph` is equivalent to the reader-facing graph spec. -/
def commGraphEquivSpec : CommGraph n ≃ CommGraphSpec n where
  toFun := commGraphToSpec
  invFun := commGraphFromSpec
  left_inv := by
    intro G
    cases G
    rfl
  right_inv := by
    intro S
    cases S
    rfl

/-- Verification anchor: local admissible-trace definition equals core model definition. -/
@[simp] theorem admissibleTrace_iff
    (N : ObliviousMessageAdversary n) (Gseq : Round → CommGraph n) :
    AdmissibleTrace N Gseq ↔ ComputationalModel.AdmissibleTrace N Gseq :=
  Iff.rfl

/-- Verification anchor: local in-neighbor definition equals core model definition. -/
@[simp] theorem inNeighbors_iff
    (G : CommGraph n) (i : Proc n) :
    InNeighbors G i = ComputationalModel.InNeighbors G i :=
  rfl

/-- Verification anchor: local reachability definition equals core model definition. -/
@[simp] theorem reachable_iff
    (G : CommGraph n) :
    Reachable G = ComputationalModel.Reachable G :=
  rfl

/-- Verification anchor: local root-set definition equals core model definition. -/
@[simp] theorem isRootSet_iff
    (G : CommGraph n) (R : Finset (Proc n)) :
    IsRootSet G R ↔ ComputationalModel.IsRootSet G R :=
  Iff.rfl

/-- Verification anchor: local k-rootedness definition equals core model definition. -/
@[simp] theorem isKRooted_iff
    (G : CommGraph n) (k : Nat) :
    IsKRooted G k ↔ ComputationalModel.IsKRooted G k :=
  Iff.rfl

/-- Verification anchor: local adversary k-rootedness equals core model definition. -/
@[simp] theorem isKRootedAdversary_iff
    (N : ObliviousMessageAdversary n) (k : Nat) :
    IsKRootedAdversary N k ↔ ComputationalModel.IsKRootedAdversary N k :=
  Iff.rfl

/-- Verification anchor: local norm-convergence definition equals core model definition. -/
@[simp] theorem convergesTo_iff
    {x : Round → V} {l : V} :
    ConvergesTo x l ↔ ComputationalModel.ConvergesTo x l :=
  Iff.rfl

/-- Verification anchor: local set-convergence definition equals core model definition. -/
@[simp] theorem convergesToSet_iff
    {x : Round → V} {S : Set V} :
    ConvergesToSet x S ↔ ComputationalModel.ConvergesToSet x S :=
  Iff.rfl

/-- Verification anchor: local validity-at-limit definition equals core model definition. -/
@[simp] theorem validityAtLimit_iff
    [NormedSpace ℝ V]
    (init limits : Proc n → V) :
    ValidityAtLimit init limits ↔ ComputationalModel.ValidityAtLimit init limits :=
  Iff.rfl

/-- Verification anchor: local agreement-at-limit definition equals core model definition. -/
@[simp] theorem subspaceAgreementAtLimit_iff
    [NormedSpace ℝ V]
    (s : Nat) (limits : Proc n → V) :
    SubspaceAgreementAtLimit s limits ↔ ComputationalModel.SubspaceAgreementAtLimit s limits :=
  Iff.rfl

/-- Verification anchor: paper-facing solver predicate is exactly the core model predicate. -/
@[simp] theorem solvesAsymptoticSubspace_iff
    [NormedSpace ℝ V]
    (A : DeterministicAlgorithm V n)
    (N : ObliviousMessageAdversary n) (s : Nat) :
    SolvesAsymptoticSubspace A N s ↔
      ComputationalModel.SolvesAsymptoticSubspace A N s :=
  Iff.rfl

/-- Verification anchor: explicit-limits variant is exactly the core model predicate. -/
@[simp] theorem solvesAsymptoticSubspaceWithLimits_iff
    [NormedSpace ℝ V]
    (A : DeterministicAlgorithm V n)
    (N : ObliviousMessageAdversary n) (s : Nat) :
    SolvesAsymptoticSubspaceWithLimits A N s ↔
      ComputationalModel.SolvesAsymptoticSubspaceWithLimits A N s :=
  Iff.rfl

end Verification

end AsymptoticSubspace

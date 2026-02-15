-- Internal plumbing module.
-- Reader-facing statements live in `DefComputationalModel.lean`.
import Mathlib

noncomputable section

namespace AsymptoticSubspace
namespace ComputationalModel

abbrev Round := Nat
abbrev Proc (n : Nat) := Fin n

/-- Round communication graph on `n` processes with mandatory self-loops. -/
structure CommGraph (n : Nat) where
  edge : Proc n → Proc n → Prop
  self_loop : ∀ i : Proc n, edge i i

/-- Incoming neighbors of process `i` in graph `G`. -/
def InNeighbors {n : Nat} (G : CommGraph n) (i : Proc n) : Set (Proc n) :=
  {j | G.edge j i}

/-- Reachability in a communication graph (directed path, including length-0). -/
def Reachable {n : Nat} (G : CommGraph n) : Proc n → Proc n → Prop :=
  Relation.ReflTransGen G.edge

/-- `R` is a root set of `G` if every node is reachable from some node in `R`. -/
def IsRootSet {n : Nat} (G : CommGraph n) (R : Finset (Proc n)) : Prop :=
  ∀ i : Proc n, ∃ j : Proc n, j ∈ R ∧ Reachable G j i

/-- A graph is `k`-rooted if it has some root set of size at most `k`. -/
def IsKRooted {n : Nat} (G : CommGraph n) (k : Nat) : Prop :=
  ∃ R : Finset (Proc n), R.card ≤ k ∧ IsRootSet G R

/-- Oblivious message adversary as a nonempty set of communication graphs. -/
structure ObliviousMessageAdversary (n : Nat) where
  graphs : Set (CommGraph n)
  nonempty : graphs.Nonempty

/-- An oblivious message adversary is `k`-rooted if each of its graphs is `k`-rooted. -/
def IsKRootedAdversary {n : Nat} (N : ObliviousMessageAdversary n) (k : Nat) : Prop :=
  ∀ G : CommGraph n, G ∈ N.graphs → IsKRooted G k

section Model

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {n : Nat}

/--
A complete synchronous execution model specialized to averaging algorithms.

- `graphs t` is the round-`t` communication graph.
- `weights t i j` is process `i`'s weight assigned to value received from `j` in round `t`.
- `outputs t i` is process `i`'s output vector at round `t`.

The fields encode the exact averaging update rule from the paper.
-/
structure AveragingExecution (n : Nat) where
  graphs : Round → CommGraph n
  weights : Round → Proc n → Proc n → ℝ
  outputs : Round → Proc n → V
  weights_nonneg :
    ∀ t i j, 0 ≤ weights t i j
  weights_support :
    ∀ t i j, ¬ (graphs t).edge j i → weights t i j = 0
  weights_row_sum :
    ∀ t i, (∑ j : Proc n, weights t i j) = 1
  update_rule :
    ∀ t i, outputs (t + 1) i = ∑ j : Proc n, (weights (t + 1) i j) • outputs t j

namespace AveragingExecution

variable (E : AveragingExecution (V := V) n)

/-- The explicit round-`(t+1)` averaging equation from the update rule. -/
lemma output_succ_eq_weighted_sum (t : Round) (i : Proc n) :
    E.outputs (t + 1) i = ∑ j : Proc n, (E.weights (t + 1) i j) • E.outputs t j :=
  E.update_rule t i

/-- Nonnegativity of all round weights. -/
lemma weight_nonneg (t : Round) (i j : Proc n) :
    0 ≤ E.weights t i j :=
  E.weights_nonneg t i j

/-- Weights on non-received messages are zero (`w_{ij}(t)=0` if `j ∉ In_i(t)`). -/
lemma weight_eq_zero_of_not_in_neighbor
    (t : Round) (i j : Proc n) (h : j ∉ InNeighbors (E.graphs t) i) :
    E.weights t i j = 0 :=
  E.weights_support t i j h

/-- Row-stochasticity: per process/round the weights sum to `1`. -/
lemma weights_sum_one (t : Round) (i : Proc n) :
    (∑ j : Proc n, E.weights t i j) = 1 :=
  E.weights_row_sum t i

/--
Single-step constant preservation for averaging executions:
if all round-`t` outputs are `c`, then all round-`t+1` outputs are also `c`.
-/
lemma output_succ_eq_const_of_outputs_const
    (t : Round) (i : Proc n) (c : V)
    (hconst : ∀ j : Proc n, E.outputs t j = c) :
    E.outputs (t + 1) i = c := by
  calc
    E.outputs (t + 1) i
        = ∑ j : Proc n, (E.weights (t + 1) i j) • E.outputs t j :=
          E.output_succ_eq_weighted_sum t i
    _ = ∑ j : Proc n, (E.weights (t + 1) i j) • c := by
          simp [hconst]
    _ = (∑ j : Proc n, E.weights (t + 1) i j) • c := by
          rw [Finset.sum_smul]
    _ = c := by
          simp [E.weights_sum_one (t + 1) i]

/--
Global constant preservation for averaging executions:
if round `0` is constant `c`, then every round remains constant `c`.
-/
lemma outputs_eq_const_of_initial_const
    (c : V) (h0 : ∀ i : Proc n, E.outputs 0 i = c) :
    ∀ t : Round, ∀ i : Proc n, E.outputs t i = c := by
  intro t
  induction t with
  | zero =>
      intro i
      exact h0 i
  | succ t ih =>
      intro i
      exact E.output_succ_eq_const_of_outputs_const t i c ih

end AveragingExecution

/-- Deterministic round-based algorithm over vector outputs. -/
structure DeterministicAlgorithm
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] (n : Nat) where
  step : Round → CommGraph n → (Proc n → V) → Proc n → V
  locality :
    ∀ t G x y i,
      (∀ j : Proc n, G.edge j i → x j = y j) →
      step t G x i = step t G y i

namespace DeterministicAlgorithm

variable (A : DeterministicAlgorithm V n)

/-- Run of algorithm `A` for graph sequence `Gseq` and initial outputs `init`. -/
def run (Gseq : Round → CommGraph n) (init : Proc n → V) : Round → Proc n → V
  | 0 => init
  | t + 1 => fun i => A.step (t + 1) (Gseq (t + 1)) (run Gseq init t) i

end DeterministicAlgorithm

/-- A graph sequence is admissible for adversary `N` iff every round graph is in `N`. -/
def AdmissibleTrace
    {n : Nat} (N : ObliviousMessageAdversary n) (Gseq : Round → CommGraph n) : Prop :=
  ∀ t : Round, Gseq t ∈ N.graphs

/-- Asymptotic convergence to `l` in norm (`‖x(t)-l‖ → 0`). -/
def ConvergesTo {V : Type*} [NormedAddCommGroup V] (x : Round → V) (l : V) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ T : Round, ∀ t : Round, T ≤ t → ‖x t - l‖ < ε

/-- Asymptotic convergence onto a set (`dist(x(t), S) → 0`). -/
def ConvergesToSet {V : Type*} [NormedAddCommGroup V] (x : Round → V) (S : Set V) : Prop :=
  S.Nonempty ∧
    (∀ ε : ℝ, 0 < ε → ∃ T : Round, ∀ t : Round, T ≤ t → Metric.infDist (x t) S < ε)

/-- Validity at limits: every process limit lies in the convex hull of initial outputs. -/
def ValidityAtLimit
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : Nat}
    (init limits : Proc n → V) : Prop :=
  ∀ i : Proc n, limits i ∈ convexHull ℝ (Set.range init)

/-- Subspace agreement at limits for target dimension `s`. -/
def SubspaceAgreementAtLimit
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : Nat}
    (s : Nat) (limits : Proc n → V) : Prop :=
  ∃ E : AffineSubspace ℝ V,
    FiniteDimensional ℝ E.direction ∧
    Module.finrank ℝ E.direction ≤ s ∧
    ∀ i : Proc n, limits i ∈ (E : Set V)

/--
Algorithm-level solvability of `d`-to-`s` asymptotic subspace consensus in adversary `N`
using asymptotic convergence (`dist → 0`).
-/
def SolvesAsymptoticSubspaceWithLimits
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : Nat}
    (A : DeterministicAlgorithm V n)
    (N : ObliviousMessageAdversary n) (s : Nat) : Prop :=
  ∀ (Gseq : Round → CommGraph n) (init : Proc n → V),
    AdmissibleTrace N Gseq →
    ∃ limits : Proc n → V,
      (∀ i : Proc n, ConvergesTo (fun t => (A.run Gseq init t) i) (limits i)) ∧
      ValidityAtLimit init limits ∧
      SubspaceAgreementAtLimit s limits

/--
Paper-faithful solver specification:
- all process trajectories converge onto one `s`-dimensional affine subspace,
- and each trajectory converges onto the convex hull of the initial values.
-/
def SolvesAsymptoticSubspace
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : Nat}
    (A : DeterministicAlgorithm V n)
    (N : ObliviousMessageAdversary n) (s : Nat) : Prop :=
  ∀ (Gseq : Round → CommGraph n) (init : Proc n → V),
    AdmissibleTrace N Gseq →
    ∃ E : AffineSubspace ℝ V,
      FiniteDimensional ℝ E.direction ∧
      Module.finrank ℝ E.direction ≤ s ∧
      (∀ i : Proc n, ConvergesToSet (fun t => (A.run Gseq init t) i) (E : Set V)) ∧
      (∀ i : Proc n,
        ConvergesToSet (fun t => (A.run Gseq init t) i) (convexHull ℝ (Set.range init)))

/-- `α`-safe averaging: every received value gets weight at least `α`. -/
def AlphaSafe (E : AveragingExecution (V := V) n) (α : ℝ) : Prop :=
  ∀ t i j, (E.graphs t).edge j i → α ≤ E.weights t i j

/-- `M` is a broadcasting set of `G` if every process has an incoming edge from some node in `M`. -/
def IsBroadcastingSet (G : CommGraph n) (M : Finset (Proc n)) : Prop :=
  ∀ i : Proc n, ∃ j : Proc n, j ∈ M ∧ G.edge j i

/-- Minimum broadcasting weight with broadcasting-set function `M(t)`. -/
def MinimumBroadcastWeight
    (E : AveragingExecution (V := V) n)
    (M : Round → Finset (Proc n)) (α : ℝ) : Prop :=
  (∀ t : Round, IsBroadcastingSet (E.graphs t) (M t)) ∧
    (∀ t i, α ≤ Finset.sum (M t) (fun j => E.weights t i j))

/--
Model-grounded formalization of the paper claim:
in a broadcastable setting, an `α`-safe averaging algorithm has minimum broadcasting weight `α`.
-/
theorem alphaSafe_implies_minimumBroadcastWeight
    (E : AveragingExecution (V := V) n)
    (M : Round → Finset (Proc n))
    (α : ℝ)
    (hsafe : AlphaSafe (V := V) E α)
    (hbroadcast : ∀ t : Round, IsBroadcastingSet (E.graphs t) (M t)) :
    MinimumBroadcastWeight (V := V) E M α := by
  refine ⟨hbroadcast, ?_⟩
  intro t i
  rcases hbroadcast t i with ⟨j, hjM, hjedge⟩
  have hαj : α ≤ E.weights t i j := hsafe t i j hjedge
  have hjle :
      E.weights t i j ≤ Finset.sum (M t) (fun k => E.weights t i k) := by
    exact Finset.single_le_sum (fun k hk => E.weights_nonneg t i k) hjM
  exact le_trans hαj hjle

end Model

end ComputationalModel
end AsymptoticSubspace

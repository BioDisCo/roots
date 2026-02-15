-- Internal plumbing module.
-- Reader-facing statement is in `ThmImposs.lean`.
import AsymptoticSubspace.ModelBridgeCore

noncomputable section

namespace AsymptoticSubspace
namespace ModelLemmas

open Set
open ComputationalModel
open PaperFormalization

section ImpossibilityModel

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {n : Nat}

variable (N : ObliviousMessageAdversary n)
variable (s : Nat)

/-- Reachability-minimal node: every node that reaches it is also reached by it. -/
def IsReachabilityMinimal (G : CommGraph n) (r : Proc n) : Prop :=
  ∀ j : Proc n, Reachable G j r → Reachable G r j

/-- Finite set of all reachability-minimal nodes in `G`. -/
noncomputable def minimalReachers (G : CommGraph n) : Finset (Proc n) := by
  classical
  exact Finset.univ.filter (fun r => IsReachabilityMinimal (n := n) G r)

theorem mem_minimalReachers_iff (G : CommGraph n) (r : Proc n) :
    r ∈ minimalReachers (n := n) G ↔ IsReachabilityMinimal (n := n) G r := by
  classical
  simp [minimalReachers]

theorem exists_minimal_reacher_to
    (G : CommGraph n) (i : Proc n) :
    ∃ r : Proc n,
      IsReachabilityMinimal (n := n) G r ∧ Reachable G r i := by
  classical
  let S : Set (Proc n) := {j : Proc n | Reachable G j i}
  have hSfin : S.Finite := Set.toFinite S
  have hSne : S.Nonempty := ⟨i, Relation.ReflTransGen.refl⟩
  letI : LE (Proc n) := ⟨fun a b => Reachable G a b⟩
  letI : IsTrans (Proc n) (· ≤ ·) := ⟨fun _ _ _ => Relation.ReflTransGen.trans⟩
  obtain ⟨r, hrS, hrMin⟩ := hSfin.exists_minimal hSne
  refine ⟨r, ?_, hrS⟩
  intro j hjr
  have hjS : j ∈ S := Relation.ReflTransGen.trans hjr hrS
  exact hrMin hjS hjr

theorem isRootSet_minimalReachers (G : CommGraph n) :
    IsRootSet G (minimalReachers (n := n) G) := by
  intro i
  rcases exists_minimal_reacher_to (n := n) G i with ⟨r, hrMin, hri⟩
  refine ⟨r, ?_, hri⟩
  exact (mem_minimalReachers_iff (n := n) G r).2 hrMin

theorem isKRooted_of_card_minimalReachers_le
    (G : CommGraph n)
    (hcard : (minimalReachers (n := n) G).card ≤ s + 1) :
    IsKRooted G (s + 1) := by
  refine ⟨minimalReachers (n := n) G, hcard, ?_⟩
  exact isRootSet_minimalReachers (n := n) G

theorem lt_card_minimalReachers_of_not_kRooted
    (G : CommGraph n)
    (hnot : ¬ IsKRooted G (s + 1)) :
    s + 1 < (minimalReachers (n := n) G).card := by
  by_contra hle
  exact hnot (isKRooted_of_card_minimalReachers_le (n := n) (s := s) G (Nat.not_lt.mp hle))

/-- Bidirectional reachability (same SCC under reachability equivalence). -/
def MutualReachable (G : CommGraph n) (a b : Proc n) : Prop :=
  Reachable G a b ∧ Reachable G b a

/-- A canonical representative among reachability-minimal nodes of one SCC class. -/
def IsRepMinimal (G : CommGraph n) (r : Proc n) : Prop :=
  IsReachabilityMinimal (n := n) G r ∧
    ∀ r' : Proc n,
      IsReachabilityMinimal (n := n) G r' →
      MutualReachable (n := n) G r r' →
      r ≤ r'

/-- Finite set of canonical representatives of minimal SCC classes. -/
noncomputable def minimalClassReps (G : CommGraph n) : Finset (Proc n) := by
  classical
  exact Finset.univ.filter (fun r => IsRepMinimal (n := n) G r)

theorem mem_minimalClassReps_iff (G : CommGraph n) (r : Proc n) :
    r ∈ minimalClassReps (n := n) G ↔ IsRepMinimal (n := n) G r := by
  classical
  simp [minimalClassReps]

theorem exists_rep_for_minimal
    (G : CommGraph n) (r : Proc n)
    (hrMin : IsReachabilityMinimal (n := n) G r) :
    ∃ rep : Proc n,
      rep ∈ minimalClassReps (n := n) G ∧
      MutualReachable (n := n) G rep r := by
  classical
  let C : Finset (Proc n) :=
    (minimalReachers (n := n) G).filter (fun x => MutualReachable (n := n) G x r)
  have hrC : r ∈ C := by
    refine Finset.mem_filter.mpr ?_
    refine ⟨(mem_minimalReachers_iff (n := n) G r).2 hrMin, ?_⟩
    exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  obtain ⟨rep, hrepC, hmin⟩ := C.exists_minimal ⟨r, hrC⟩
  have hrepMin : IsReachabilityMinimal (n := n) G rep := by
    have : rep ∈ minimalReachers (n := n) G := by
      exact (Finset.mem_filter.mp hrepC).1
    exact (mem_minimalReachers_iff (n := n) G rep).1 this
  have hrepMutR : MutualReachable (n := n) G rep r := by
    exact (Finset.mem_filter.mp hrepC).2
  have hrepLeAll :
      ∀ r' : Proc n,
        IsReachabilityMinimal (n := n) G r' →
        MutualReachable (n := n) G rep r' →
        rep ≤ r' := by
    intro r' hr'Min hmut
    have hr'C : r' ∈ C := by
      have hrr' : Reachable G r r' :=
        Relation.ReflTransGen.trans hrepMutR.2 hmut.1
      have hr'r : Reachable G r' r :=
        Relation.ReflTransGen.trans hmut.2 hrepMutR.1
      refine Finset.mem_filter.mpr ?_
      refine ⟨(mem_minimalReachers_iff (n := n) G r').2 hr'Min, ?_⟩
      exact ⟨hr'r, hrr'⟩
    by_cases hle : r' ≤ rep
    · exact hmin hr'C hle
    · exact le_of_not_ge hle
  have hrepIsRep : IsRepMinimal (n := n) G rep := by
    refine ⟨hrepMin, hrepLeAll⟩
  refine ⟨rep, ?_, hrepMutR⟩
  exact (mem_minimalClassReps_iff (n := n) G rep).2 hrepIsRep

theorem eq_of_rep_mutual
    (G : CommGraph n)
    {i i' : Proc n}
    (hi : i ∈ minimalClassReps (n := n) G)
    (hi' : i' ∈ minimalClassReps (n := n) G)
    (hmut : MutualReachable (n := n) G i i') :
    i = i' := by
  have hRep : IsRepMinimal (n := n) G i :=
    (mem_minimalClassReps_iff (n := n) G i).1 hi
  have hRep' : IsRepMinimal (n := n) G i' :=
    (mem_minimalClassReps_iff (n := n) G i').1 hi'
  have hii' : i ≤ i' := hRep.2 i' hRep'.1 hmut
  have hi'i : i' ≤ i := hRep'.2 i hRep.1 ⟨hmut.2, hmut.1⟩
  exact le_antisymm hii' hi'i

theorem unique_rep_reached
    (G : CommGraph n)
    {j i i' : Proc n}
    (hi : i ∈ minimalClassReps (n := n) G)
    (hi' : i' ∈ minimalClassReps (n := n) G)
    (hji : Reachable G j i)
    (hji' : Reachable G j i') :
    i = i' := by
  have hRep : IsRepMinimal (n := n) G i :=
    (mem_minimalClassReps_iff (n := n) G i).1 hi
  have hRep' : IsRepMinimal (n := n) G i' :=
    (mem_minimalClassReps_iff (n := n) G i').1 hi'
  have hij : Reachable G i j := hRep.1 j hji
  have hi'j : Reachable G i' j := hRep'.1 j hji'
  have hii' : Reachable G i i' := Relation.ReflTransGen.trans hij hji'
  have hi'i : Reachable G i' i := Relation.ReflTransGen.trans hi'j hji
  exact eq_of_rep_mutual (n := n) G hi hi' ⟨hii', hi'i⟩

theorem isRootSet_minimalClassReps (G : CommGraph n) :
    IsRootSet G (minimalClassReps (n := n) G) := by
  intro i
  rcases exists_minimal_reacher_to (n := n) G i with ⟨r, hrMin, hri⟩
  rcases exists_rep_for_minimal (n := n) G r hrMin with ⟨rep, hrep, hmut⟩
  refine ⟨rep, hrep, ?_⟩
  exact Relation.ReflTransGen.trans hmut.1 hri

theorem isKRooted_of_card_minimalClassReps_le
    (G : CommGraph n)
    (hcard : (minimalClassReps (n := n) G).card ≤ s + 1) :
    IsKRooted G (s + 1) := by
  refine ⟨minimalClassReps (n := n) G, hcard, ?_⟩
  exact isRootSet_minimalClassReps (n := n) G

theorem lt_card_minimalClassReps_of_not_kRooted
    (G : CommGraph n)
    (hnot : ¬ IsKRooted G (s + 1)) :
    s + 1 < (minimalClassReps (n := n) G).card := by
  by_contra hle
  exact hnot (isKRooted_of_card_minimalClassReps_le (n := n) (s := s) G (Nat.not_lt.mp hle))

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
  (∃ A : DeterministicAlgorithm V n, SolvesAsymptoticSubspaceWithLimits A N s) →
    Solves_d_to_s (V := V) (n := n) N s

/-- Witness `w` is realizable by algorithm `A` on some admissible trace from `w.init`. -/
def RealizableWitnessBy (A : DeterministicAlgorithm V n)
    (w : ImpossibilityWitness (V := V) (n := n) N s) : Prop :=
  ∃ Gseq : Round → CommGraph n,
    AdmissibleTrace N Gseq ∧
    (∀ i : Proc n,
      ConvergesTo (fun t => (A.run Gseq w.init t) i) (w.limits i))

/-- Static graph/roots data used by the lower-bound execution construction. -/
structure StaticImpossibilityData where
  graph : CommGraph n
  graph_in_adversary : graph ∈ N.graphs
  graph_not_k_rooted : ¬ IsKRooted graph (s + 1)
  roots : Finset (Proc n)
  roots_card : roots.card = s + 2
  rootLabel : Proc n → Option (Proc n)
  label_mem_roots : ∀ j r, rootLabel j = some r → r ∈ roots
  label_sound : ∀ j r, rootLabel j = some r → Reachable graph j r
  label_complete :
    ∀ j i, i ∈ roots → Reachable graph j i → rootLabel j = some i

/-- Constant trace that repeats one graph at every round. -/
def staticTrace (G : CommGraph n) : Round → CommGraph n := fun _ => G

theorem admissible_staticTrace
    (d : StaticImpossibilityData N s) :
    AdmissibleTrace N (staticTrace (n := n) d.graph) := by
  intro t
  exact d.graph_in_adversary

theorem exists_staticImpossibilityData_of_badGraph
    (G : CommGraph n)
    (hGin : G ∈ N.graphs)
    (hGnot : ¬ IsKRooted G (s + 1)) :
    Nonempty (StaticImpossibilityData N s) := by
  classical
  have hcardGt :
      s + 1 < (minimalClassReps (n := n) G).card :=
    lt_card_minimalClassReps_of_not_kRooted (n := n) (s := s) G hGnot
  have hsize : s + 2 ≤ (minimalClassReps (n := n) G).card := by
    omega
  rcases Finset.exists_subset_card_eq (s := minimalClassReps (n := n) G) hsize with
    ⟨roots, hrootsSub, hrootsCard⟩
  let rootLabel : Proc n → Option (Proc n) := fun j =>
    if h : ∃ i : Proc n, i ∈ roots ∧ Reachable G j i then
      some (Classical.choose h)
    else
      none
  have hLabelMem : ∀ j r, rootLabel j = some r → r ∈ roots := by
    intro j r hEq
    by_cases h : ∃ i : Proc n, i ∈ roots ∧ Reachable G j i
    · have hChooseMem : Classical.choose h ∈ roots := (Classical.choose_spec h).1
      have hEq' : Classical.choose h = r := by
        simpa [rootLabel, h] using hEq
      simpa [hEq'] using hChooseMem
    · simp [rootLabel, h] at hEq
  have hLabelSound : ∀ j r, rootLabel j = some r → Reachable G j r := by
    intro j r hEq
    by_cases h : ∃ i : Proc n, i ∈ roots ∧ Reachable G j i
    · have hChooseReach : Reachable G j (Classical.choose h) := (Classical.choose_spec h).2
      have hEq' : Classical.choose h = r := by
        simpa [rootLabel, h] using hEq
      simpa [hEq'] using hChooseReach
    · simp [rootLabel, h] at hEq
  have hLabelComplete :
      ∀ j i, i ∈ roots → Reachable G j i → rootLabel j = some i := by
    intro j i hi hji
    let h : ∃ u : Proc n, u ∈ roots ∧ Reachable G j u := ⟨i, hi, hji⟩
    have hChooseMem : Classical.choose h ∈ roots := (Classical.choose_spec h).1
    have hChooseReach : Reachable G j (Classical.choose h) := (Classical.choose_spec h).2
    have hChooseRep : Classical.choose h ∈ minimalClassReps (n := n) G :=
      hrootsSub hChooseMem
    have hiRep : i ∈ minimalClassReps (n := n) G := hrootsSub hi
    have hEqRoot : Classical.choose h = i :=
      unique_rep_reached (n := n) G hChooseRep hiRep hChooseReach hji
    simp [rootLabel, h, hEqRoot]
  refine ⟨{
    graph := G
    graph_in_adversary := hGin
    graph_not_k_rooted := hGnot
    roots := roots
    roots_card := hrootsCard
    rootLabel := rootLabel
    label_mem_roots := hLabelMem
    label_sound := hLabelSound
    label_complete := hLabelComplete
  }⟩

/--
Pinning property for a fixed static lower-bound construction:
for any solving algorithm, any limit profile on the static trace from `init`
must match initials on the distinguished root set.
-/
def RootPinningOnStaticData (d : StaticImpossibilityData N s) : Prop :=
  ∀ (A : DeterministicAlgorithm V n),
    SolvesAsymptoticSubspaceWithLimits A N s →
    ∀ (init limits : Proc n → V),
      (∀ i : Proc n,
        ConvergesTo (fun t => (A.run (staticTrace (n := n) d.graph) init t) i) (limits i)) →
      ∀ i : Proc n, i ∈ d.roots → limits i = init i

/-- Initial values are constant on every reacheability cone of each distinguished root. -/
def InitConstantOnRootReachers
    (d : StaticImpossibilityData N s) (init : Proc n → V) : Prop :=
  ∀ i : Proc n, i ∈ d.roots →
    ∀ j : Proc n, Reachable d.graph j i → init j = init i

/--
Concrete bridge: from full solver semantics and a realizable witness run,
derive witness-level subspace agreement on `w.limits`.
-/
theorem agreement_on_realizable_witness
    (A : DeterministicAlgorithm V n)
    (hA : SolvesAsymptoticSubspaceWithLimits A N s)
    (w : ImpossibilityWitness (V := V) (n := n) N s)
    (hreal : RealizableWitnessBy (V := V) (n := n) N s A w) :
    SubspaceAgreementOn (V := V) (n := n) s w.roots w.limits := by
  rcases hreal with ⟨Gseq, hAdm, hConvW⟩
  rcases hA Gseq w.init hAdm with ⟨limitsA, hConvA, hValA, hAgrA⟩
  rcases hAgrA with ⟨E, hfdE, hdimE, hmemE⟩
  refine ⟨E, hfdE, hdimE, ?_⟩
  intro i hi
  have hEq : limitsA i = w.limits i := by
    exact convergesTo_unique_aux (hConvA i) (hConvW i)
  have hmem : limitsA i ∈ (E : Set V) := hmemE i
  simpa [hEq] using hmem

/-- Predecessor closure: if `j` reaches `i` and `k → j`, then `k` also reaches `i`. -/
theorem reachable_pred_closed
    (G : CommGraph n) {i j k : Proc n}
    (hji : Reachable G j i) (hkj : G.edge k j) :
    Reachable G k i :=
  Relation.ReflTransGen.head hkj hji

/--
Indistinguishability on static traces:
if two initial configurations agree on the reachability cone of `i`,
then process `i` has identical states at every round in the two runs.
-/
theorem run_static_eq_on_reachers
    (d : StaticImpossibilityData N s)
    (A : DeterministicAlgorithm V n)
    (init₁ init₂ : Proc n → V)
    (i : Proc n)
    (hEq :
      ∀ j : Proc n, Reachable d.graph j i → init₁ j = init₂ j) :
    ∀ t : Round,
      (A.run (staticTrace (n := n) d.graph) init₁ t) i
        = (A.run (staticTrace (n := n) d.graph) init₂ t) i := by
  have hAll :
      ∀ j : Proc n, Reachable d.graph j i →
        ∀ t : Round,
          (A.run (staticTrace (n := n) d.graph) init₁ t) j
            = (A.run (staticTrace (n := n) d.graph) init₂ t) j := by
    intro j hji t
    induction t generalizing j with
    | zero =>
        exact hEq j hji
    | succ t ih =>
        let x : Proc n → V := A.run (staticTrace (n := n) d.graph) init₁ t
        let y : Proc n → V := A.run (staticTrace (n := n) d.graph) init₂ t
        have hlocal :
            A.step (t + 1) d.graph x j = A.step (t + 1) d.graph y j := by
          apply A.locality (t := t + 1) (G := d.graph) (x := x) (y := y) (i := j)
          intro k hkj
          have hki : Reachable d.graph k i := reachable_pred_closed (n := n) d.graph hji hkj
          have hxk : x k = y k := ih k hki
          simpa [x, y] using hxk
        calc
          (A.run (staticTrace (n := n) d.graph) init₁ (t + 1)) j
              = A.step (t + 1) d.graph x j := rfl
          _ = A.step (t + 1) d.graph y j := hlocal
          _ = (A.run (staticTrace (n := n) d.graph) init₂ (t + 1)) j := rfl
  intro t
  exact hAll i Relation.ReflTransGen.refl t

/--
Root pinning from locality via indistinguishability:
compare the given run to a globally constant initialization and use validity on that run.
-/
theorem root_pinning_of_locality
    (d : StaticImpossibilityData N s)
    (A : DeterministicAlgorithm V n)
    (hA : SolvesAsymptoticSubspaceWithLimits A N s)
    (init limits : Proc n → V)
    (hconv :
      ∀ i : Proc n,
        ConvergesTo (fun t => (A.run (staticTrace (n := n) d.graph) init t) i) (limits i))
    (hconst : InitConstantOnRootReachers (V := V) (n := n) N s d init) :
    ∀ i : Proc n, i ∈ d.roots → limits i = init i := by
  intro i hi
  let initConst : Proc n → V := fun _ => init i
  have hEqCone :
      ∀ j : Proc n, Reachable d.graph j i → init j = initConst j := by
    intro j hji
    simpa [initConst] using hconst i hi j hji
  have htrajEq :
      ∀ t : Round,
        (A.run (staticTrace (n := n) d.graph) init t) i
          = (A.run (staticTrace (n := n) d.graph) initConst t) i :=
    run_static_eq_on_reachers (V := V) (n := n) N s d A init initConst i hEqCone
  have hAdm : AdmissibleTrace N (staticTrace (n := n) d.graph) :=
    admissible_staticTrace (N := N) (s := s) d
  rcases hA (staticTrace (n := n) d.graph) initConst hAdm with
    ⟨limitsConst, hConvConst, hValConst, hAgrConst⟩
  have hconvConstToLimits :
      ConvergesTo
        (fun t => (A.run (staticTrace (n := n) d.graph) initConst t) i)
        (limits i) := by
    intro ε hε
    rcases hconv i ε hε with ⟨T, hT⟩
    refine ⟨T, ?_⟩
    intro t ht
    have hEqt :
        (A.run (staticTrace (n := n) d.graph) initConst t) i
          = (A.run (staticTrace (n := n) d.graph) init t) i := (htrajEq t).symm
    simpa [hEqt] using hT t ht
  have hlimEq : limitsConst i = limits i :=
    convergesTo_unique_aux (hConvConst i) hconvConstToLimits
  have hRangeConst : Set.range initConst = ({init i} : Set V) := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨j, rfl⟩
      simp [initConst]
    · intro hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact ⟨i, by simp [initConst]⟩
  have hVali : limitsConst i ∈ ({init i} : Set V) := by
    simpa [hRangeConst] using hValConst i
  have hConstLimit : limitsConst i = init i := by
    simpa using hVali
  calc
    limits i = limitsConst i := hlimEq.symm
    _ = init i := hConstLimit

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

/-- Extract a concrete bad graph from a non-`(s+1)`-rooted adversary. -/
theorem exists_graph_not_kRooted_of_not_kRootedAdversary
    (hnotRooted : ¬ IsKRootedAdversary N (s + 1)) :
    ∃ G : CommGraph n, G ∈ N.graphs ∧ ¬ IsKRooted G (s + 1) := by
  by_contra hno
  apply hnotRooted
  intro G hG
  by_contra hGbad
  exact hno ⟨G, hG, hGbad⟩

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
From static root-labeling data and `dim(V) > s`, construct an initialization that is both
affinely independent on roots and constant on each root's reachability cone.
-/
theorem exists_init_for_static_data
    (d : StaticImpossibilityData N s)
    (hfin : s < Module.finrank ℝ V) :
    ∃ init : Proc n → V,
      AffineIndependent ℝ (fun p : d.roots => init p) ∧
      InitConstantOnRootReachers (V := V) (n := n) N s d init := by
  rcases exists_init_affineIndependent_of_finrank_gt
      (V := V) (n := n) (s := s) hfin d.roots d.roots_card with
    ⟨initRoot, hAffRoot⟩
  let init : Proc n → V := fun j =>
    match d.rootLabel j with
    | some r => initRoot r
    | none => 0
  have hOnRoots : (fun p : d.roots => init p) = fun p : d.roots => initRoot p := by
    funext p
    have hLbl : d.rootLabel p = some p := d.label_complete p p p.property Relation.ReflTransGen.refl
    simp [init, hLbl]
  have hConst : InitConstantOnRootReachers (V := V) (n := n) N s d init := by
    intro i hi j hj
    have hLbl_j : d.rootLabel j = some i := d.label_complete j i hi hj
    have hLbl_i : d.rootLabel i = some i := d.label_complete i i hi Relation.ReflTransGen.refl
    simp [init, hLbl_j, hLbl_i]
  refine ⟨init, ?_, hConst⟩
  simpa [hOnRoots] using hAffRoot

/--
Build concrete extraction (the former `hextract`) from static data + root-pinning.
-/
theorem hextract_of_static_pinning
    (d : StaticImpossibilityData N s)
    (hpin :
      ∀ (A : DeterministicAlgorithm V n),
        SolvesAsymptoticSubspaceWithLimits A N s →
        ∀ (init limits : Proc n → V),
          (∀ i : Proc n,
            ConvergesTo
              (fun t => (A.run (staticTrace (n := n) d.graph) init t) i)
              (limits i)) →
          ∀ i : Proc n, i ∈ d.roots → limits i = init i) :
    ¬ IsKRootedAdversary N (s + 1) →
    s < Module.finrank ℝ V →
    ∀ A : DeterministicAlgorithm V n, SolvesAsymptoticSubspaceWithLimits A N s →
      ∃ w : ImpossibilityWitness (V := V) (n := n) N s,
        RealizableWitnessBy (V := V) (n := n) N s A w := by
  intro hnotRooted hsfin A hA
  rcases exists_init_affineIndependent_of_finrank_gt
      (V := V) (n := n) (s := s) hsfin d.roots d.roots_card with
    ⟨init, hAff⟩
  let Gseq : Round → CommGraph n := staticTrace (n := n) d.graph
  have hAdm : AdmissibleTrace N Gseq := admissible_staticTrace (N := N) (s := s) d
  rcases hA Gseq init hAdm with ⟨limits, hConv, hVal, hAgr⟩
  let w : ImpossibilityWitness (V := V) (n := n) N s :=
    { graph := d.graph
      graph_in_adversary := d.graph_in_adversary
      graph_not_k_rooted := d.graph_not_k_rooted
      roots := d.roots
      roots_card := d.roots_card
      init := init
      limits := limits
      affine_independent_init := hAff
      validity_on_roots := by
        intro i hi
        exact hpin A hA init limits hConv i hi }
  refine ⟨w, ?_⟩
  refine ⟨Gseq, hAdm, ?_⟩
  intro i
  exact hConv i

/--
Concrete extraction built from more primitive static assumptions:
`init` exists with affine independence on roots and constancy on root-reachers,
and root pinning is derived from locality.
-/
theorem hextract_of_static_local
    (d : StaticImpossibilityData N s)
    (hinit :
      ∃ init : Proc n → V,
        AffineIndependent ℝ (fun p : d.roots => init p) ∧
        InitConstantOnRootReachers (V := V) (n := n) N s d init) :
    ¬ IsKRootedAdversary N (s + 1) →
    s < Module.finrank ℝ V →
    ∀ A : DeterministicAlgorithm V n, SolvesAsymptoticSubspaceWithLimits A N s →
      ∃ w : ImpossibilityWitness (V := V) (n := n) N s,
        RealizableWitnessBy (V := V) (n := n) N s A w := by
  intro hnotRooted hsfin A hA
  rcases hinit with ⟨init, hAff, hConst⟩
  let Gseq : Round → CommGraph n := staticTrace (n := n) d.graph
  have hAdm : AdmissibleTrace N Gseq := admissible_staticTrace (N := N) (s := s) d
  rcases hA Gseq init hAdm with ⟨limits, hConv, hVal, hAgr⟩
  have hPin :
      ∀ i : Proc n, i ∈ d.roots → limits i = init i :=
    root_pinning_of_locality (V := V) (n := n) N s d A hA init limits hConv hConst
  let w : ImpossibilityWitness (V := V) (n := n) N s :=
    { graph := d.graph
      graph_in_adversary := d.graph_in_adversary
      graph_not_k_rooted := d.graph_not_k_rooted
      roots := d.roots
      roots_card := d.roots_card
      init := init
      limits := limits
      affine_independent_init := hAff
      validity_on_roots := by
        intro i hi
        exact hPin i hi }
  refine ⟨w, ?_⟩
  refine ⟨Gseq, hAdm, ?_⟩
  intro i
  exact hConv i

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
  have hbadGraph : ∃ G : CommGraph n, G ∈ N.graphs ∧ ¬ IsKRooted G (s + 1) :=
    exists_graph_not_kRooted_of_not_kRootedAdversary (N := N) (s := s) hnotRooted
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
    ¬ ∃ A : DeterministicAlgorithm V n, SolvesAsymptoticSubspaceWithLimits A N s := by
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
      ∀ A : DeterministicAlgorithm V n, SolvesAsymptoticSubspaceWithLimits A N s →
        ∃ w : ImpossibilityWitness (V := V) (n := n) N s,
          RealizableWitnessBy (V := V) (n := n) N s A w) :
    ¬ ∃ A : DeterministicAlgorithm V n, SolvesAsymptoticSubspaceWithLimits A N s := by
  intro hAex
  rcases hAex with ⟨A, hA⟩
  rcases hextract hnotRooted hfin A hA with ⟨w, hreal⟩
  have hagr : SubspaceAgreementOn (V := V) (n := n) s w.roots w.limits :=
    agreement_on_realizable_witness (V := V) (n := n) N s A hA w hreal
  exact lemma_imposs_model (V := V) (n := n) N s w hagr

/--
Full unsolvability with explicit paper-style static-data assumptions,
without an opaque extraction functional argument.
-/
theorem lemma_imposs_unsolvable_full_static
    (hnotRooted : ¬ IsKRootedAdversary N (s + 1))
    (hfin : s < Module.finrank ℝ V)
    (d : StaticImpossibilityData N s) :
    ¬ ∃ A : DeterministicAlgorithm V n, SolvesAsymptoticSubspaceWithLimits A N s := by
  have hinit :
      ∃ init : Proc n → V,
        AffineIndependent ℝ (fun p : d.roots => init p) ∧
        InitConstantOnRootReachers (V := V) (n := n) N s d init :=
    exists_init_for_static_data (V := V) (n := n) N s d hfin
  apply lemma_imposs_unsolvable_full_concrete (V := V) (n := n) N s hnotRooted hfin
  exact hextract_of_static_local (V := V) (n := n) N s d hinit

/-- Paper-level "model grounded" assumption for the impossibility construction. -/
def ModelGrounded : Prop :=
  Nonempty (StaticImpossibilityData N s)

theorem modelGrounded_of_not_kRootedAdversary
    (hnotRooted : ¬ IsKRootedAdversary N (s + 1)) :
    ModelGrounded (N := N) (s := s) := by
  rcases exists_graph_not_kRooted_of_not_kRootedAdversary (N := N) (s := s) hnotRooted with
    ⟨G, hGin, hGnot⟩
  exact exists_staticImpossibilityData_of_badGraph (n := n) (N := N) (s := s) G hGin hGnot

/--
Model-grounded full unsolvability:
if some static-data witness exists for this non-`(s+1)`-rooted adversary,
then no algorithm can solve asymptotic subspace consensus.
-/
theorem lemma_imposs_unsolvable_full_model_grounded
    (hnotRooted : ¬ IsKRootedAdversary N (s + 1))
    (hfin : s < Module.finrank ℝ V)
    (hgrounded : ModelGrounded (N := N) (s := s)) :
    ¬ ∃ A : DeterministicAlgorithm V n, SolvesAsymptoticSubspaceWithLimits A N s := by
  rcases hgrounded with ⟨d⟩
  exact lemma_imposs_unsolvable_full_static (V := V) (n := n) N s hnotRooted hfin d

theorem lemma_imposs_unsolvable_full_exact
    (hnotRooted : ¬ IsKRootedAdversary N (s + 1))
    (hfin : s < Module.finrank ℝ V) :
    ¬ ∃ A : DeterministicAlgorithm V n, SolvesAsymptoticSubspaceWithLimits A N s := by
  have hgrounded : ModelGrounded (N := N) (s := s) :=
    modelGrounded_of_not_kRootedAdversary (n := n) (N := N) (s := s) hnotRooted
  exact lemma_imposs_unsolvable_full_model_grounded
    (V := V) (n := n) N s hnotRooted hfin hgrounded

/--
Paper-faithful full unsolvability:
if the adversary is not `(s+1)`-rooted and `dim(V) > s`, then no local deterministic
algorithm can satisfy asymptotic set-convergence validity and subspace agreement.
-/
theorem lemma_imposs_unsolvable_full_paper
    (hnotRooted : ¬ IsKRootedAdversary N (s + 1))
    (hfin : s < Module.finrank ℝ V) :
    ¬ ∃ A : DeterministicAlgorithm V n, SolvesAsymptoticSubspace A N s := by
  intro hAex
  rcases hAex with ⟨A, hA⟩
  have hgrounded : ModelGrounded (N := N) (s := s) :=
    modelGrounded_of_not_kRootedAdversary (n := n) (N := N) (s := s) hnotRooted
  rcases hgrounded with ⟨d⟩
  rcases exists_init_for_static_data (V := V) (n := n) N s d hfin with ⟨init, hAff, hConst⟩
  let Gseq : Round → CommGraph n := staticTrace (n := n) d.graph
  have hAdm : AdmissibleTrace N Gseq := admissible_staticTrace (N := N) (s := s) d
  rcases hA Gseq init hAdm with ⟨E, hfdE, hdimE, hToE, hToHull⟩
  have hclosedDir : IsClosed (E.direction : Set V) := by
    letI : FiniteDimensional ℝ E.direction := hfdE
    exact Submodule.closed_of_finiteDimensional (s := E.direction)
  have hclosedE : IsClosed (E : Set V) :=
    (AffineSubspace.isClosed_direction_iff (R := ℝ) (V := V) (P := V) E).1 hclosedDir
  have hsubset :
      Set.range (fun p : d.roots => init p) ⊆ (E : Set V) := by
    intro x hx
    rcases hx with ⟨p, rfl⟩
    have hp : (p : Proc n) ∈ d.roots := p.property
    let initConst : Proc n → V := fun _ => init p
    have hEqCone :
        ∀ j : Proc n, Reachable d.graph j p → init j = initConst j := by
      intro j hjp
      simpa [initConst] using hConst p hp j hjp
    have htrajEq :
        ∀ t : Round,
          (A.run Gseq init t) p = (A.run Gseq initConst t) p :=
      run_static_eq_on_reachers (V := V) (n := n) N s d A init initConst p hEqCone
    rcases hA Gseq initConst hAdm with ⟨Econst, hfdConst, hdimConst, hToEConst, hToHullConst⟩
    have hRangeConst : Set.range initConst = ({init p} : Set V) := by
      ext y
      constructor
      · intro hy
        rcases hy with ⟨j, rfl⟩
        simp [initConst]
      · intro hy
        rcases Set.mem_singleton_iff.mp hy with rfl
        exact ⟨p, by simp [initConst]⟩
    have hToSingletonConst :
        ConvergesToSet (fun t => (A.run Gseq initConst t) p) ({init p} : Set V) := by
      simpa [hRangeConst, convexHull_singleton] using hToHullConst p
    have hToPointConst :
        ConvergesTo (fun t => (A.run Gseq initConst t) p) (init p) :=
      (convergesToSet_singleton_iff).1 hToSingletonConst
    have hToPoint :
        ConvergesTo (fun t => (A.run Gseq init t) p) (init p) := by
      intro ε hε
      rcases hToPointConst ε hε with ⟨T, hT⟩
      refine ⟨T, ?_⟩
      intro t ht
      have hEqt : (A.run Gseq initConst t) p = (A.run Gseq init t) p := (htrajEq t).symm
      simpa [hEqt] using hT t ht
    have hInClosureE :
        init p ∈ closure (E : Set V) := by
      exact mem_closure_of_convergesTo_and_convergesToSet
        (hTo := hToPoint) (hToSet := hToE p)
    have hmemE : init p ∈ (E : Set V) := by
      simpa [hclosedE.closure_eq] using hInClosureE
    simpa using hmemE
  have hcard : Fintype.card d.roots = s + 2 := by
    simpa using d.roots_card
  have hcontra :=
    lemma_imposs_complete
      (xLim := fun p : d.roots => init p)
      hcard
      hAff
  exact hcontra ⟨E, hfdE, hdimE, hsubset⟩

end ImpossibilityModel

end ModelLemmas
end AsymptoticSubspace

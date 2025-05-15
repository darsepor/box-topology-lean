import Mathlib.Topology.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Topology.Order
import Mathlib.Topology.Constructions
import Mathlib
namespace BoxTopology
open Set Filter TopologicalSpace Topology

#check continuous_induced_rng


instance boxTopology {ι : Type*} {Y : ι → Type*} [t : ∀ i, TopologicalSpace (Y i)] :
    TopologicalSpace ((i : ι) → Y i) :=
  .generateFrom <|
  /-{B : Set ((i : ι) → Y i)|∀ (idx : ι), IsOpen ((fun (point : (k : ι) → Y k) => point idx) '' B)∧
    B = Set.pi (Set.univ : Set ι) (fun idx => (fun point => point idx) '' B) }-/
    { B | ∃ (U : ∀ i, Set (Y i)), (∀ i, IsOpen (U i)) ∧ B = Set.pi Set.univ U }

/--/
instance boxTopology' {ι : Type*} {Y : ι → Type*} [t: ∀ i, TopologicalSpace (Y i)] :
    TopologicalSpace ((i : ι) → Y i) where
  IsOpen B := ∀ (point : (i :ι)  → Y i), point ∈ B → ∃ (U : (i:ι) → Set (Y i)),
           (∀ i, IsOpen (U i)) ∧ (∀ i, point i ∈ U i) ∧ (Set.pi Set.univ U ⊆ B)
  isOpen_univ := by
    intro point inu

    use fun i => univ
    simp
  isOpen_sUnion := by

  isOpen_inter := sorry

theorem boxTopology_eq_boxTopology' {ι : Type*} {Y : ι → Type*} [t: ∀ i, TopologicalSpace (Y i)] :
    boxTopology = @boxTopology' ι Y t := by
  rw[boxTopology]
  rw[boxTopology']
  refine TopologicalSpace.ext ?_
  sorry
-/
lemma open_preimage_box {ι : Type*} {Y : ι → Type*} [DecidableEq ι]
  [t : ∀ i : ι, TopologicalSpace (Y i)] {k : ι} (s : Set (Y k)) (f := fun (x : (i : ι) → Y i) => x k):
  IsOpen s → IsOpen (f⁻¹' s) := by
  intro op
  rw[IsOpen]
  rw[TopologicalSpace.IsOpen]
  rw[boxTopology]
  rw[generateFrom]
  simp
  refine GenerateOpen.basic (f ⁻¹' s) ?_
  simp

  use fun i => if h : i = k then h.symm ▸ s else Set.univ --gemini
  simp
  constructor
  · intro idx
    by_cases ieqk : idx = k
    · rw[ieqk]
      simp
      exact op

    · split_ifs
      exact isOpen_univ

  · rw[Set.preimage]

    sorry


lemma box_continuity_transfer  {ι : Type*} {Y : ι → Type*}
    [t : ∀ i : ι, TopologicalSpace (Y i)] (j: ι):
    Continuous fun (point : (k : ι) → Y k) => point j := by
  sorry

--lemma identity_continuity

lemma box_topology_is_finer {ι : Type*} {Y : ι → Type*}
          [t : ∀ i : ι, TopologicalSpace (Y i)] :
           boxTopology ≤ @Pi.topologicalSpace ι Y t := by

  intro s hs
  rw[Pi.topologicalSpace] at hs

  --rw[induced] at hs
  sorry

  done

example  {X :Type} {T1: TopologicalSpace X} {T2:TopologicalSpace X}:
  T1 ≤ T2 ↔ ∀(s: Set X), @IsOpen _ T2 s → @IsOpen _ T1 s := by
    exact Iff.symm isOpen_implies_isOpen_iff

theorem equivalence_to_product_if_finite {ι : Type*} {Y : ι → Type*}
          [t : ∀ i : ι, TopologicalSpace (Y i)] [fin : Fintype ι]  :
  boxTopology = @Pi.topologicalSpace ι Y t := by

  --rw[boxTopology]
  --rw[Pi.topologicalSpace]



  refine TopologicalSpace.ext_iff.mpr ?_
  intro s
  constructor
  ·
    apply isOpen_implies_isOpen_iff.mpr

    exact box_topology_is_finer


  ·
    apply isOpen_implies_isOpen_iff.mpr




    sorry
  done

#check TopologicalSpace.le_def



end BoxTopology

import Mathlib.Topology.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Topology.Order
import Mathlib.Topology.Constructions
import Mathlib
namespace BoxTopology
open Set Filter TopologicalSpace Topology

def boxTopology {ι : Type*} {Y : ι → Type*} [t : ∀ i, TopologicalSpace (Y i)] :
    TopologicalSpace ((i : ι) → Y i) :=
  .generateFrom <|
  {B : Set ((i : ι) → Y i)|∀ (idx : ι), IsOpen ((fun (point : (k : ι) → Y k) => point idx) '' B)∧
    B = Set.pi (Set.univ : Set ι) (fun idx => (fun point => point idx) '' B) }

#check continuouos_induced_rng
lemma box_continuity_transfer  {ι : Type*} {Y : ι → Type*}
    [t : ∀ i : ι, TopologicalSpace (Y i)] (j: ι) (box : boxTopology):
    Continuous fun (x : Π i, Y i) ↦ x j:= by


  sorry


lemma identity_continuity

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

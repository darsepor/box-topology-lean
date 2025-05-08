import Mathlib.Topology.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Topology.Order
import Mathlib.Topology.Constructions

namespace BoxTopology
open Set Filter TopologicalSpace Topology

def boxTopology {ι : Type*} {Y : ι → Type*} [t : ∀ i, TopologicalSpace (Y i)] :
    TopologicalSpace ((i : ι) → Y i) :=
  .generateFrom <|
  {B : Set ((i : ι) → Y i)|∀ (idx : ι), IsOpen ((fun (point : (k : ι) → Y k) => point idx) '' B)∧
    B = Set.pi (Set.univ : Set ι) (fun idx => (fun point => point idx) '' B) }


theorem equivalence_to_product_if_finite {ι : Type*} {Y : ι → Type*} [t : ∀ i : ι, TopologicalSpace (Y i)] [fin : Fintype ι] :
  boxTopology = @Pi.topologicalSpace ι Y t := by
  rw[Pi.topologicalSpace]



  done




end BoxTopology

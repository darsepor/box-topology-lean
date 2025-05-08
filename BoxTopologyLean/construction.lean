import Mathlib.Topology.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Topology.Order
namespace BoxTopology
open Set Filter TopologicalSpace Topology

def boxTopology {ι : Type*} {Y : ι → Type*} [t : ∀ i, TopologicalSpace (Y i)] :
    TopologicalSpace ((i : ι) → Y i) :=
  .generateFrom <|
  {B : Set ((i : ι) → Y i)|∀ (idx : ι), IsOpen ((fun (point : (k : ι) → Y k) => point idx) '' B)∧
    B = Set.pi (Set.univ : Set ι) (fun idx => (fun point => point idx) '' B) }



end BoxTopology

import Mathlib.Topology.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Topology.Order
import Mathlib.Topology.Constructions
import Mathlib
namespace BoxTopology
open Set Filter TopologicalSpace Topology



variable {ι : Type*} {Y : ι → Type*} [t : ∀ i, TopologicalSpace (Y i)] [TopologicalSpace ((i : ι) → Y i)]

def box {ι : Type*} (Y : ι → Type*) := ((i : ι) → Y i)


def boxTopology {ι : Type*} (Y : ι → Type*) [t : ∀ i, TopologicalSpace (Y i)] :
    TopologicalSpace ((i : ι) → Y i) :=
  .generateFrom <|
  /-{B : Set ((i : ι) → Y i)|∀ (idx : ι), IsOpen ((fun (point : (k : ι) → Y k) => point idx) '' B)∧
    B = Set.pi (Set.univ : Set ι) (fun idx => (fun point => point idx) '' B) }-/
    { B | ∃ (U : ∀ i, Set (Y i)), (∀ i, IsOpen (U i)) ∧ B = Set.pi Set.univ U }

instance : TopologicalSpace (box Y):= boxTopology Y
--instance : TopologicalSpace ((i : ι) → Y i) := Pi.topologicalSpace
/-
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
-/

lemma open_preimage_box {ι : Type*} {Y : ι → Type*} [DecidableEq ι]
  [t : ∀ i : ι, TopologicalSpace (Y i)] {k : ι} (s : Set (Y k)):
  IsOpen s → IsOpen ((fun (x : box Y) => x k) ⁻¹' s) := by
  let f := fun (x : box Y) => x k
  intro op
  rw[IsOpen]
  rw[TopologicalSpace.IsOpen]

  rw[instTopologicalSpaceBox]
  rw [boxTopology]
  rw[generateFrom]

  refine GenerateOpen.basic (f ⁻¹' s) ?_

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

  · ext x
    simp

    constructor
    · intro inside

      rw [@univ_pi_eq_iInter]
      simp
      intro idx
      by_cases ieqk : idx = k
      · rw [ieqk]
        simp
        exact inside
      · simp [ieqk]


    · intro cond
      rw [@univ_pi_eq_iInter] at cond
      simp at cond
      specialize cond k
      simp at cond
      exact cond



lemma box_continuity_transfer  {ι : Type*} {Y : ι → Type*} [DecidableEq ι]
    [t : ∀ i : ι, TopologicalSpace (Y i)] (j: ι):
    Continuous fun (point : (box Y)) => point j := by

  refine continuous_def.mpr ?_

  intro s h
  exact open_preimage_box _ h


lemma identity_continuity_box_to_product {ι : Type*} {Y : ι → Type*} [DecidableEq ι]
    [t : ∀ i : ι, TopologicalSpace (Y i)] :
    @Continuous (box Y) ((i : ι) → Y i) (boxTopology Y) Pi.topologicalSpace id := by
    apply continuous_pi

    intro idx
    apply box_continuity_transfer




#check continuous_induced_rng --lean found continuous_pi which is a version of this and
                              --saved a lot of work

theorem box_topology_is_finer {ι : Type*} {Y : ι → Type*} [DecidableEq ι]
    [t : ∀ i : ι, TopologicalSpace (Y i)] :
    boxTopology Y ≤ Pi.topologicalSpace := by
  refine continuous_id_iff_le.mp ?_

  exact identity_continuity_box_to_product

lemma identity_continuity_product_to_box_if_fin {ι : Type*} {Y : ι → Type*} [DecidableEq ι]
    [t : ∀ i : ι, TopologicalSpace (Y i)][fin : Fintype ι] :
    @Continuous  ((i : ι) → Y i) (box Y) Pi.topologicalSpace (boxTopology Y)  id := by
  refine continuous_generateFrom_iff.mpr ?_
  intro s sin
  unfold IsOpen
  unfold TopologicalSpace.IsOpen
  unfold id
  simp



  sorry
--lemma pi_open {ι : Type*} {Y : ι → Type*} [t : ∀ i : ι, TopologicalSpace (Y i)]:



  --sorry
#check pi_generateFrom_eq_finite
--example  {X :Type} {T1: TopologicalSpace X} {T2:TopologicalSpace X}:
--  T1 ≤ T2 ↔ ∀(s: Set X), @IsOpen _ T2 s → @IsOpen _ T1 s := by
--    exact Iff.symm isOpen_implies_isOpen_iff

theorem equivalence_to_product_if_finite {ι : Type*} {Y : ι → Type*} [DecidableEq ι]
          {g: ∀ a : ι, Set (Set (Y a))} {arg:  a → generateFrom (g a)}
          [t : ∀ i : ι, TopologicalSpace (Y i)] [fin : Fintype ι]
          :
   @Pi.topologicalSpace ι Y t =boxTopology Y := by
  have fingen := @pi_generateFrom_eq_finite ι Y g
  unfold boxTopology
  apply fingen
  · sorry
  ·
    sorry


  /-
  refine TopologicalSpace.ext_iff.mpr ?_
  intro s
  constructor
  · intro bop

    sorry
  · apply isOpen_implies_isOpen_iff.mpr

    exact box_topology_is_finer
-/

#check TopologicalSpace.le_def



end BoxTopology

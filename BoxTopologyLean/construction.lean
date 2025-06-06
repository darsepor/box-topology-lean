import Mathlib.Topology.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Topology.Order
import Mathlib.Topology.Constructions
import Mathlib


namespace BoxTopology
open Set Filter TopologicalSpace Topology Metric



variable {ι : Type*} {Y : ι → Type*} [t : ∀ i, TopologicalSpace (Y i)] [TopologicalSpace ((i : ι) → Y i)]

def box {ι : Type*} (Y : ι → Type*) := ((i : ι) → Y i)


def boxTopology {ι : Type*} (Y : ι → Type*) [t : ∀ i, TopologicalSpace (Y i)] :
    TopologicalSpace ((i : ι) → Y i) :=
  .generateFrom <|
  /-{B : Set ((i : ι) → Y i)|∀ (idx : ι), IsOpen ((fun (point : (k : ι) → Y k) => point idx) '' B)∧
    B = Set.pi (Set.univ : Set ι) (fun idx => (fun point => point idx) '' B) }-/
    { B | ∃ (U : ∀ i, Set (Y i)), (∀ i, IsOpen (U i)) ∧ B = Set.pi Set.univ U }

instance : TopologicalSpace (box Y):= boxTopology Y

#check box (fun (_: ℕ) ↦ ℝ)
#synth TopologicalSpace (box (fun (_: ℕ) ↦ ℝ))


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




#check continuous_induced_rng

theorem box_topology_is_finer {ι : Type*} {Y : ι → Type*} [DecidableEq ι]
    [t : ∀ i : ι, TopologicalSpace (Y i)] :
    boxTopology Y ≤ Pi.topologicalSpace := by
  refine continuous_id_iff_le.mp ?_

  exact identity_continuity_box_to_product

#print axioms box_topology_is_finer


#check pi_generateFrom_eq_finite


theorem equivalence_to_product_if_finite {ι : Type*} {Y : ι → Type*} [DecidableEq ι]
         [t : ∀ i : ι, TopologicalSpace (Y i)] [fin : Finite ι]:
         @Pi.topologicalSpace ι Y t = boxTopology Y := by
  let g := fun i => {U : Set (Y i) | @IsOpen (Y i) (t i) U}
  have hg : ∀ a, ⋃₀ g a = univ := by
    intro a
    ext e
    constructor
    · simp

    · intro ins
      simp
      use univ
      simp
      unfold g
      simp

  have fingen := @pi_generateFrom_eq_finite ι Y g fin

  have same: ∀i, t i =  ((fun a ↦ generateFrom (g a)) i) := by
    intro i

    unfold g
    simp
    exact Eq.symm (generateFrom_setOf_isOpen (t i))
  apply fingen at hg
  unfold Pi.topologicalSpace at hg
  simp_rw [← same] at hg
  unfold Pi.topologicalSpace
  rw [hg]
  unfold boxTopology
  exact rfl

#check TopologicalSpace.le_def


#print axioms equivalence_to_product_if_finite
--bounded open
--unbounded open

abbrev bounded_seq: Set (box (fun (_: ℕ) ↦ ℝ)) := {a | ∃M, ∀n, |a n| ≤ M}

abbrev unbounded_seq: Set (box (fun (_: ℕ) ↦ ℝ)) := bounded_seqᶜ


def elements_at_n (n : ℕ) : Set ℝ := Set.image (fun (s : ℕ → ℝ) ↦ s n) bounded_seq

example {n : ℕ}:elements_at_n n = Set.univ := by

  unfold elements_at_n
  unfold bounded_seq
  unfold Set.image
  simp
  refine Eq.symm (ext ?_)
  simp
  intro x
  let const := fun _ : ℕ => x
  use const
  constructor
  · refine mem_setOf.mpr ?_
    use |x|
    simp_rw[const]
    simp
  · simp_rw[const]


#check Metric.ball
def seq_ball (a : ℕ → ℝ) : Set (box (fun (_: ℕ) ↦ ℝ)) := {x | ∀ n : ℕ, x n ∈ Metric.ball (a n) 1}


lemma seq_ball_open_and_around (a : ℕ → ℝ) : IsOpen (seq_ball a) ∧ a ∈ seq_ball a := by
  constructor
  · unfold IsOpen
    unfold TopologicalSpace.IsOpen
    unfold instTopologicalSpaceBox
    unfold boxTopology
    simp_rw[generateFrom]
    refine GenerateOpen.basic (seq_ball a) ?_

    refine mem_setOf.mpr ?_
    let can := fun n : ℕ => Metric.ball (a n) 1
    use can
    constructor
    · intro n
      unfold can
      exact isOpen_ball

    · exact Subset.antisymm (fun ⦃a_1⦄ a i a_2 ↦ a i) fun ⦃a⦄ a n ↦ a n trivial

  · unfold seq_ball

    refine mem_setOf.mpr ?_
    simp



lemma bounded_seq_open_in_box: IsOpen bounded_seq := by
  refine isOpen_iff_forall_mem_open.mpr ?_
  intro a aH
  use seq_ball a
  constructor
  · unfold seq_ball
    unfold bounded_seq
    unfold bounded_seq at aH
    simp at aH
    simp
    intro a1 a1H
    cases' aH with aM aH
    use aM + 1
    intro n
    specialize a1H n
    specialize aH n
    simp_rw[dist] at a1H
    have i1: |a1 n| = |a1 n - a n + a n| := by
      simp
    have i2: |a1 n| ≤ |a1 n - a n| + |a n| := by
      rw[i1]
      exact abs_add_le (a1 n - a n) (a n)
    linarith



  · exact seq_ball_open_and_around a






lemma unbounded_seq_open_in_box: IsOpen unbounded_seq := by
  unfold unbounded_seq
  unfold bounded_seq
  refine isOpen_iff_forall_mem_open.mpr ?_
  intro a aH
  use seq_ball a
  constructor
  · unfold seq_ball
    simp at aH
    simp
    intro a1 a1H
    simp
    intro L
    specialize aH (L + 1)
    simp at a1H
    cases' aH with n aH
    specialize a1H n
    simp_rw[dist] at a1H
    use n
    have i1 : |a n| - |a1 n| ≤ |a n - a1 n| := by exact abs_sub_abs_le_abs_sub (a n) (a1 n)

    have i2 : |a n - a1 n| < 1 := by
      rw [@abs_sub_comm]
      exact a1H

    linarith

  · exact seq_ball_open_and_around a


theorem disconnected_box_seq: ¬PreconnectedSpace (box (fun (_: ℕ) ↦ ℝ)) := by

  by_contra h

  unfold box at h
  simp at h
  have inter: bounded_seq ∩ unbounded_seq = ∅ := by
    exact inter_compl_self bounded_seq

  rw[@preconnectedSpace_iff_univ] at h
  have unio: bounded_seq ∪ unbounded_seq = univ := by
    exact union_compl_self bounded_seq

  rw[←unio] at h
  have unbO : IsOpen unbounded_seq := by
    exact unbounded_seq_open_in_box
  have bO : IsOpen bounded_seq := by
    exact bounded_seq_open_in_box
  simp_rw [IsPreconnected] at h
  simp at h
  specialize h bounded_seq unbounded_seq

  apply h at bO
  apply bO at unbO

  apply unbO at unio

  rw[unbounded_seq] at unio
  rw[unbounded_seq] at inter
  rw[inter] at unio
  have nebO: bounded_seq.Nonempty := by
    rw[bounded_seq]
    refine nonempty_def.mpr ?_
    use fun n: ℕ => 5
    simp
    use 6
    linarith

  apply unio at nebO
  have neunbO: unbounded_seq.Nonempty := by
    rw[unbounded_seq]
    rw[bounded_seq]
    refine nonempty_def.mpr ?_
    use fun n: ℕ => n
    simp
    exact fun x ↦ exists_nat_gt x

  rw[unbounded_seq] at neunbO
  apply nebO at neunbO
  --have f : (∅ : Set (ℕ →  ℝ)).Nonempty → False := by
  simp at neunbO

#print axioms disconnected_box_seq

end BoxTopology

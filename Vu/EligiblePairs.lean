module
public import Vu.PiecePartition

namespace Vu
open Finset

variable {I V : Type*} [Fintype I] [LinearOrder I] [DecidableEq V]

/-- Indices of the pieces containing both vertices, in the chosen order. -/
@[expose] public def jointPieces (P : I → Finset V) (x y : V) : Finset I :=
  univ.filter fun i => x ∈ P i ∧ y ∈ P i

/-- Every covered unordered pair is assigned to the least common piece. -/
public theorem least_joint_piece (P : I → Finset V) (x y : V) (h : (jointPieces P x y).Nonempty) :
    ∃! i, i ∈ jointPieces P x y ∧ ∀ j ∈ jointPieces P x y, i ≤ j := by
  let F := jointPieces P x y
  exact ⟨F.min' h, ⟨min'_mem _ _,fun j hj => min'_le _ _ hj⟩,
    fun j hj => le_antisymm (hj.2 _ (min'_mem _ _)) (min'_le _ _ hj.1)⟩

/-- A pair is exceptional when it lies in two distinct pieces with small
intersection. This is independent of the order of its endpoints. -/
@[expose] public def exceptionalPair (P : I → Finset V) (z : ℝ) (x y : V) : Prop :=
  ∃ i ∈ jointPieces P x y, ∃ j ∈ jointPieces P x y, i ≠ j ∧ ((P i ∩ P j).card : ℝ) ≤ z

/-- Eligibility of two classes in piece i. -/
@[expose] public def eligibleClasses (P : I → Finset V) (z : ℝ) (i : I) (A B : Finset V) : Prop :=
  ∀ j < i, z < ((P i ∩ P j).card : ℝ) → ¬(A ⊆ P j ∧ B ⊆ P j)

/-- Away from exceptional pairs a class pair is eligible exactly in the
piece to which any one of its vertex pairs is assigned. This identifies
eligible blocks for edges and nonedges alike. -/
public theorem eligible_iff_first (P : I → Finset V) (z : ℝ) (i : I) (A B : Finset V)
    (hA : A ⊆ P i) (hB : B ⊆ P i) (x y : V) (hx : x ∈ A) (hy : y ∈ B)
    (clean : ¬ exceptionalPair P z x y)
    (refA : ∀ j < i, z < ((P i ∩ P j).card : ℝ) → A ⊆ P j ∨ Disjoint A (P j))
    (refB : ∀ j < i, z < ((P i ∩ P j).card : ℝ) → B ⊆ P j ∨ Disjoint B (P j)) :
    eligibleClasses P z i A B ↔ i ∈ jointPieces P x y ∧ ∀ j ∈ jointPieces P x y, i ≤ j := by
  have hi : i ∈ jointPieces P x y := mem_filter.mpr ⟨mem_univ _,hA hx,hB hy⟩
  constructor
  · intro he
    refine ⟨hi,?_⟩
    intro j hj
    by_contra! hlt
    have big : z < ((P i ∩ P j).card : ℝ) := lt_of_not_ge (fun h => clean ⟨i,hi,j,hj,hlt.ne',h⟩)
    obtain ⟨hxj,hyj⟩ := (mem_filter.mp hj).2
    exact he j hlt big ⟨(refA j hlt big).resolve_right (fun h => disjoint_left.mp h hx hxj),
      (refB j hlt big).resolve_right (fun h => disjoint_left.mp h hy hyj)⟩
  · intro he j hj _ hab
    exact hj.not_ge (he.2 j (mem_filter.mpr ⟨mem_univ _,hab.1 hx,hab.2 hy⟩))

omit [LinearOrder I] in
/-- Row budget for the two-witness and positive-matrix-entry estimates.
Nonexceptional neighbors occur in at most one eligible piece; every
exceptional neighbor can occur in at most r pieces. -/
public theorem eligible_neighbor_occurrences [Fintype V] (N E : Finset V) (Ns : I → Finset V)
    (r : ℕ) (hsub : ∀ i, Ns i ⊆ N)
    (hunique : ∀ y ∈ N, y ∉ E → ∀ i j, y ∈ Ns i → y ∈ Ns j → i = j)
    (hmult : ∀ y, (univ.filter fun i => y ∈ Ns i).card ≤ r) :
    ∑ i, (Ns i).card ≤ N.card + r*E.card := by
  classical
  let cnt y := (univ.filter fun i => y ∈ Ns i).card
  have rows : ∑ i, (Ns i).card = ∑ y ∈ N, cnt y := by
    have hh i : (Ns i).card = ∑ y ∈ N, if y ∈ Ns i then 1 else 0 := by
      have heq : N.filter (fun y => y ∈ Ns i) = Ns i := by ext; simp; exact fun h => hsub i h
      rw [← card_filter,heq]
    simp_rw [hh]
    rw [sum_comm]
    simp only [cnt,card_filter]
  have hs : ∑ y ∈ N \ E, cnt y ≤ (N \ E).card := by
    apply (sum_le_sum (g := fun _ => 1) ?_).trans_eq (by simp)
    intro y hy
    apply card_le_one.mpr
    intro i hi j hj
    exact hunique y (mem_sdiff.mp hy).1 (mem_sdiff.mp hy).2 i j (mem_filter.mp hi).2 (mem_filter.mp hj).2
  have hi : ∑ y ∈ N ∩ E, cnt y ≤ E.card*r := by
    apply (sum_le_sum (fun y (_ : y ∈ N ∩ E) => hmult y)).trans
    simpa using Nat.mul_le_mul_right r (card_le_card (s := N ∩ E) inter_subset_right)
  rw [rows, ← sum_sdiff (s₁ := N ∩ E) (s₂ := N) inter_subset_left, sdiff_inter_self_left]
  have hcard := card_le_card (sdiff_subset (s := N) (t := E))
  rw [Nat.mul_comm r E.card]
  omega
end Vu

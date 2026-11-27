module
public import Vu.SoftMatrix
namespace Vu.Revised
open Finset
/-- The entries in a row belong to its diagonal, its neighbors, or one of its incident pieces. -/
public theorem support_card {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
    (G H : SimpleGraph V) [DecidableRel G.Adj] (P good : I → Finset V) (cls : I → V → Finset V)
    (D r : ℕ) (z ρ δ : ℝ) (hD : 2*r+2 ≤ D) (hdeg : ∀ x, G.degree x ≤ D)
    (hp : ∀ i, (P i).card ≤ 2*D) (hm : ∀ x, (univ.filter fun i => x ∈ P i).card ≤ r)
    (hsub : H ≤ G) (x : V) :
    (by classical exact (univ.filter fun y => (if H.Adj x y then -1 else softMatrix G P good cls H z ρ δ x y) ≠ 0).card) ≤ D^2 := by
  classical
  let Iₓ := univ.filter fun i => x ∈ P i
  let Q := Iₓ.biUnion P
  have bound : Q.card ≤ r*(2*D) := calc
    _ ≤ ∑ i ∈ Iₓ, (P i).card := card_biUnion_le
    _ ≤ ∑ _i ∈ Iₓ, 2*D := sum_le_sum (fun i _ => hp i)
    _ = Iₓ.card*(2*D) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (hm x)
  apply (card_le_card (t := insert x (G.neighborFinset x ∪ Q)) ?_).trans
  · have a := card_insert_le x (G.neighborFinset x ∪ Q)
    have b := card_union_le (s := G.neighborFinset x) (t := Q)
    rw [SimpleGraph.card_neighborFinset_eq_degree] at b
    have c := Nat.mul_le_mul_right D hD
    nlinarith only [a,b,bound,hdeg x,c,show 1 ≤ D by omega]
  · intro y hy
    by_contra! hn
    simp only [mem_insert,mem_union,SimpleGraph.mem_neighborFinset,not_or] at hn
    have hh : ¬ H.Adj x y := fun e => hn.2.1 (hsub e)
    have hnone : sparsePieces G P good cls z ρ δ x y = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro i hi
      obtain ⟨hx,hy'⟩ := (mem_filter.mp (mem_filter.mp hi).1).2
      exact hn.2.2 (mem_biUnion.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,hx⟩,hy'⟩)
    exact (mem_filter.mp hy).2 (by simp [softMatrix,hh,Ne.symm hn.1,hn.2.1,hnone])
end Vu.Revised

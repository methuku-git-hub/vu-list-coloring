module
public import Vu.HardDecomposition
namespace Vu
open Finset

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
  (G : SimpleGraph V) [DecidableRel G.Adj] (P good : I → Finset V) (cls : I → V → Finset V)

/-- Pieces allowed to supply a positive entry of the signed matrix. Assignment
to the first common piece ensures this set has at most one element. -/
@[expose] public noncomputable def sparsePieces (z ρ δ : ℝ) (x y : V) : Finset I := by
  classical
  exact (jointPieces P x y).filter fun i =>
    (∀ j ∈ jointPieces P x y, i ≤ j) ∧ ¬ exceptionalPair P z x y ∧ x ∈ good i ∧ y ∈ good i ∧
    cls i x ≠ cls i y ∧ ¬ irregularPair G ρ (cls i x) (cls i y) ∧ crossDensity G (cls i x) (cls i y) < 1-δ

public theorem sparse_piece_unique (z ρ δ : ℝ) (x y : V) :
    (sparsePieces G P good cls z ρ δ x y).card ≤ 1 := by
  classical
  exact card_le_one.mpr (fun i hi j hj => le_antisymm ((mem_filter.mp hi).2.1 j (mem_filter.mp hj).1)
    ((mem_filter.mp hj).2.1 i (mem_filter.mp hi).1))

public theorem sparse_pieces_swap (z ρ δ : ℝ) (x y : V) :
    sparsePieces G P good cls z ρ δ x y = sparsePieces G P good cls z ρ δ y x := by
  classical
  have joints (u v : V) : jointPieces P u v = jointPieces P v u := by ext; simp [jointPieces,and_comm]
  have go (u v : V) : sparsePieces G P good cls z ρ δ u v ⊆ sparsePieces G P good cls z ρ δ v u := by
    intro i hi
    obtain ⟨hmem,hfirst,hclean,hgu,hgv,hn,hir,hd⟩ := mem_filter.mp hi
    exact mem_filter.mpr ⟨joints u v ▸ hmem,joints u v ▸ hfirst,
      by simpa only [exceptionalPair,joints v u] using hclean,hgv,hgu,hn.symm,
      fun h => hir (irregular_swap G ρ _ _ h),density_swap G (cls i u) (cls i v) ▸ hd⟩
  exact Subset.antisymm (go x y) (go y x)

/-- Section 4's completed matrix, written entrywise. All positive entries
come from the sparse regular pair of the first piece. -/
@[expose] public noncomputable def softMatrix (H : SimpleGraph V) (z ρ δ : ℝ) (x y : V) : ℝ := by
  classical
  exact if x = y then -1 else if H.Adj x y then 0 else if G.Adj x y then -1 else
    ∑ i ∈ sparsePieces G P good cls z ρ δ x y,
      crossDensity G (cls i x) (cls i y) / (1-crossDensity G (cls i x) (cls i y))

public theorem soft_matrix_symmetric (H : SimpleGraph V) (z ρ δ : ℝ) (x y : V) :
    softMatrix G P good cls H z ρ δ x y = softMatrix G P good cls H z ρ δ y x := by
  classical
  by_cases he : x = y
  · subst y; rfl
  by_cases hh : H.Adj x y
  · simp [softMatrix,he,Ne.symm he,hh,hh.symm]
  have hhs : ¬ H.Adj y x := fun h => hh h.symm
  by_cases hg : G.Adj x y
  · simp [softMatrix,he,Ne.symm he,hh,hhs,hg,hg.symm]
  simp only [softMatrix,if_neg he,if_neg (Ne.symm he),if_neg hh,if_neg (fun (h : H.Adj y x) => hh h.symm),
    if_neg hg,if_neg (fun (h : G.Adj y x) => hg h.symm)]
  rw [sparse_pieces_swap G P good cls z ρ δ x y]
  apply sum_congr rfl
  intro i _
  rw [density_swap G (cls i x) (cls i y)]

public theorem soft_matrix_edge_values (H : SimpleGraph V) (z ρ δ : ℝ) (x y : V) :
    let B := softMatrix G P good cls H z ρ δ
    B x x = -1 ∧ (H.Adj x y → B x y = 0) ∧ (G.Adj x y → ¬ H.Adj x y → B x y = -1) := by
  classical
  refine ⟨by simp [softMatrix],fun h => ?_,fun h hn => ?_⟩
  · simp [softMatrix,h.ne,h]
  · simp [softMatrix,h.ne,hn,h]

public theorem soft_matrix_entry_bounds (H : SimpleGraph V) (z ρ δ : ℝ) (hδ : 0 < δ) (x y : V) :
    let B := softMatrix G P good cls H z ρ δ
    (-1 : ℝ) ≤ B x y ∧ B x y ≤ 1/δ := by
  classical
  have hpos : 0 ≤ 1/δ := by positivity
  intro B
  by_cases he : x = y
  · simp [B,softMatrix,he]; linarith [inv_nonneg.mpr hδ.le]
  by_cases hh : H.Adj x y
  · simpa [B,softMatrix,he,hh] using hpos
  by_cases hg : G.Adj x y
  · simp [B,softMatrix,he,hh,hg]; linarith [inv_nonneg.mpr hδ.le]
  simp only [B,softMatrix,if_neg he,if_neg hh,if_neg hg]
  let F := sparsePieces G P good cls z ρ δ x y
  have hd (i : I) (hi : i ∈ F) : crossDensity G (cls i x) (cls i y) < 1-δ :=
    (mem_filter.mp hi).2.2.2.2.2.2.2
  have hp (i : I) : 0 ≤ crossDensity G (cls i x) (cls i y) := div_nonneg (sum_nonneg (fun _ _ => Nat.cast_nonneg _)) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have lo (i : I) (hi : i ∈ F) : 0 ≤ crossDensity G (cls i x) (cls i y) /
      (1-crossDensity G (cls i x) (cls i y)) := div_nonneg (hp _) (by linarith [hd i hi])
  have hi (i : I) (him : i ∈ F) : crossDensity G (cls i x) (cls i y) /
      (1-crossDensity G (cls i x) (cls i y)) ≤ 1/δ := by
    apply (div_le_div_iff₀ (by linarith [hd i him]) hδ).mpr
    nlinarith [hd i him,mul_le_mul_of_nonneg_right (show crossDensity G (cls i x) (cls i y) ≤ 1 by linarith [hd i him]) hδ.le]
  refine ⟨(by norm_num : (-1:ℝ) ≤ 0).trans (sum_nonneg lo),(sum_le_sum hi).trans ?_⟩
  simp only [sum_const,nsmul_eq_mul]
  have hone : (F.card : ℝ) ≤ 1 := by exact_mod_cast sparse_piece_unique G P good cls z ρ δ x y
  simpa using mul_le_mul_of_nonneg_right hone hpos

/-- Every nonzero entry has graph distance at most four, even when it
is an additional nonedge entry. -/
public theorem soft_matrix_local (H : SimpleGraph V) (z ρ δ : ℝ)
    (hballs : ∀ i, ∃ root, ∀ y ∈ P i, ∃ p : G.Walk root y, p.length ≤ 2)
    (x y : V) (h : softMatrix G P good cls H z ρ δ x y ≠ 0) :
    ∃ p : G.Walk x y, p.length ≤ 4 := by
  classical
  by_cases he : x = y
  · subst y; exact ⟨.nil,by simp⟩
  by_cases ha : G.Adj x y
  · exact ⟨.cons ha .nil,by simp⟩
  have hn : (sparsePieces G P good cls z ρ δ x y).Nonempty := by
    by_contra! hem
    simp [softMatrix,he,ha,hem] at h
  obtain ⟨i,hi⟩ := hn
  obtain ⟨hx,hy⟩ := (mem_filter.mp (mem_filter.mp hi).1).2
  obtain ⟨root,hr⟩ := hballs i
  obtain ⟨px,hx⟩ := hr x hx
  obtain ⟨py,hy⟩ := hr y hy
  exact ⟨px.reverse.append py,by simp only [SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_reverse]; omega⟩

end Vu

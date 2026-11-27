module
public import Vu.RegularMatrixSum
public import Vu.SoftMatrix
namespace Vu
open Finset

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
    (G : SimpleGraph V) [DecidableRel G.Adj] (P : I → Finset V) (R : ∀ i, Finpartition (P i))

@[expose] public def firstPiece (i : I) (x y : V) : Prop :=
  i ∈ jointPieces P x y ∧ ∀ j ∈ jointPieces P x y, i ≤ j

@[expose] public def sparseBlock (K : ℕ) (z ρ δ : ℝ) (i : I) (x y : V) : Prop :=
  x ∈ goodVertices G (R i) ρ K ∧ y ∈ goodVertices G (R i) ρ K ∧
  (R i).part x ≠ (R i).part y ∧ eligibleClasses P z i ((R i).part x) ((R i).part y) ∧
  ¬ irregularPair G ρ ((R i).part x) ((R i).part y) ∧ crossDensity G ((R i).part x) ((R i).part y) < 1-δ

/-- Outside exceptional pairs, any selected block is in the first piece.
The converse membership form is used to identify the positive entries. -/
public theorem sparse_block_assignment (K : ℕ) (z ρ δ : ℝ)
    (href : ∀ i A, A ∈ (R i).parts → ∀ j < i, z < ((P i ∩ P j).card : ℝ) → A ⊆ P j ∨ Disjoint A (P j))
    (i : I) (x y : V) (hn : ¬exceptionalPair P z x y) :
    sparseBlock G P R K z ρ δ i x y ↔ i ∈ sparsePieces G P (fun j => goodVertices G (R j) ρ K)
      (fun j => (R j).part) z ρ δ x y := by
  classical
  constructor
  · rintro ⟨hx,hy,he,hel,hir,hd⟩
    have hxp := (mem_filter.mp hx).1
    have hyp := (mem_filter.mp hy).1
    have ha := (R i).part_mem.mpr hxp
    have hb := (R i).part_mem.mpr hyp
    have hfirst := (eligible_iff_first P z i _ _ ((R i).le ha) ((R i).le hb) x y
      ((R i).mem_part hxp) ((R i).mem_part hyp) hn (href i _ ha) (href i _ hb)).mp hel
    exact mem_filter.mpr ⟨hfirst.1,hfirst.2,hn,hx,hy,he,hir,hd⟩
  · intro hi
    obtain ⟨hp,hfirst,_,hx,hy,he,hir,hd⟩ := mem_filter.mp hi
    refine ⟨hx,hy,he,?_,hir,hd⟩
    intro j hj _ hc
    obtain ⟨hxp,hyp⟩ := (mem_filter.mp hp).2
    exact hj.not_ge (hfirst j (mem_filter.mpr ⟨mem_univ _,hc.1 ((R i).mem_part hxp),hc.2 ((R i).mem_part hyp)⟩))

@[expose] public noncomputable def fallbackPiece (H : SimpleGraph V) (K : ℕ) (z ρ δ : ℝ) (i : I) (x y : V) : ℝ := by
  classical
  exact if G.Adj x y ∧ ¬ H.Adj x y ∧ ¬ exceptionalPair P z x y ∧ firstPiece P i x y ∧
    ¬ sparseBlock G P R K z ρ δ i x y then -1 else 0

/-- On the first piece, an edge outside the hard graph and the sparse
regular rectangles must lie in one class, touch a nongood vertex, or meet
an irregular class pair. -/
public theorem fallback_classification (K : ℕ) (z ρ δ : ℝ) (i : I) (x y : V) :
    let H := hardGraph G P (fun j => goodVertices G (R j) ρ K) (fun j => (R j).part) z
      (fun j => partnerGraph G P j (largeClasses (R j) ρ K) z ρ δ)
    fallbackPiece G P R H K z ρ δ i x y ≠ 0 →
      x ∈ P i ∧ y ∈ P i ∧ ((R i).part x = (R i).part y ∨ x ∉ goodVertices G (R i) ρ K ∨
        y ∉ goodVertices G (R i) ρ K ∨ irregularPair G ρ ((R i).part x) ((R i).part y)) := by
  classical
  intro H h
  unfold fallbackPiece at h
  split at h
  next hh =>
    obtain ⟨hg,hn,he,hfirst,hns⟩ := hh
    obtain ⟨hx,hy⟩ := (mem_filter.mp hfirst.1).2
    refine ⟨hx,hy,?_⟩
    by_contra! hn'
    obtain ⟨hne,hxg,hyg,hir⟩ := hn'
    have hel : eligibleClasses P z i ((R i).part x) ((R i).part y) := by
      intro j hj _ hc
      exact hj.not_ge (hfirst.2 j (mem_filter.mpr ⟨mem_univ _,hc.1 ((R i).mem_part hx),hc.2 ((R i).mem_part hy)⟩))
    by_cases hd : crossDensity G ((R i).part x) ((R i).part y) < 1-δ
    · exact hns ⟨hxg,hyg,hne,hel,hir,hd⟩
    · exact hn ⟨hg,he,i,hfirst.1,hfirst.2,hxg,hyg,(mem_filter.mp hxg).2.1,
        (mem_filter.mp hyg).2.1,hne,hel,hir,le_of_not_gt hd⟩
  next => exact (h rfl).elim

/-- Remove all regular-block occurrences on an exceptional pair and keep
only its prescribed edge entry. The diagonal is inserted separately. -/
@[expose] public noncomputable def exceptionalCorrection (K : ℕ) (z ρ δ : ℝ) (x y : V) : ℝ := by
  classical
  exact if exceptionalPair P z x y then
    (if G.Adj x y then -1 else 0) - ∑ i, regularPieceMatrix G P R K z ρ δ i x y else 0

public theorem matrix_assembly_identity (K : ℕ) (z ρ δ : ℝ) (hδ : 0 < δ)
    (href : ∀ i A, A ∈ (R i).parts → ∀ j < i, z < ((P i ∩ P j).card : ℝ) → A ⊆ P j ∨ Disjoint A (P j))
    (x y : V) :
    let good := fun j => goodVertices G (R j) ρ K
    let cls := fun j => (R j).part
    let H := hardGraph G P good cls z (fun j => partnerGraph G P j (largeClasses (R j) ρ K) z ρ δ)
    softMatrix G P good cls H z ρ δ x y =
      (∑ i, regularPieceMatrix G P R K z ρ δ i x y) + exceptionalCorrection G P R K z ρ δ x y +
      (∑ i, fallbackPiece G P R H K z ρ δ i x y) +
      (by classical exact if G.Adj x y ∧ ¬(jointPieces P x y).Nonempty then (-1:ℝ) else 0) +
      (if x=y then -1 else 0) := by
  classical
  intro good cls H
  let U := sparsePieces G P good cls z ρ δ x y
  let m i := regularPieceMatrix G P R K z ρ δ i x y
  let f i := fallbackPiece G P R H K z ρ δ i x y
  have mf (i : I) : m i = if sparseBlock G P R K z ρ δ i x y then
      centeredEntry G (crossDensity G (cls i x) (cls i y)) x y else 0 := by
    dsimp [m,regularPieceMatrix,sparseBlock,cls]; split <;> rename_i h <;> simp [h]
  change softMatrix G P good cls H z ρ δ x y = (∑ i, m i) + _ + (∑ i, f i) + _ + _
  by_cases he : exceptionalPair P z x y
  · have hn : ¬ H.Adj x y := fun ha => ha.2.1 he
    have hem : U = ∅ := eq_empty_iff_forall_notMem.mpr (fun i hi => (mem_filter.mp hi).2.2.1 he)
    have hcovered : (jointPieces P x y).Nonempty := by obtain ⟨i,hi,_⟩ := he; exact ⟨i,hi⟩
    have hf (i : I) : f i = 0 := by simp [f,fallbackPiece,he]
    simp only [hf,sum_const_zero,add_zero,exceptionalCorrection,if_pos he,softMatrix,if_neg hn,
      hcovered,not_true_eq_false,and_false,ite_false,hem,m,U] at *
    by_cases eq : x=y
    · subst y; simp [regularPieceMatrix,SimpleGraph.irrefl]
    · by_cases ha : G.Adj x y <;> simp [eq,ha] <;> ring
  · have hc : exceptionalCorrection G P R K z ρ δ x y = 0 := by simp [exceptionalCorrection,he]
    rw [hc,add_zero]
    have hm0 (i : I) (hi : i ∉ U) : m i = 0 := by
      rw [mf,if_neg (fun h => hi ((sparse_block_assignment G P R K z ρ δ href i x y he).mp h))]
    by_cases hcov : (jointPieces P x y).Nonempty
    · obtain ⟨i,hi,unique⟩ := least_joint_piece P x y hcov
      have helse (j : I) (hj : j ≠ i) : j ∉ U := by
        intro h; exact hj (unique _ ⟨(mem_filter.mp h).1,(mem_filter.mp h).2.1⟩)
      have hf0 (j : I) (hj : j ≠ i) : f j = 0 := by
        have hn : ¬ firstPiece P j x y := fun h => hj (unique j h)
        simp [f,fallbackPiece,hn]
      rw [sum_eq_single i (fun j _ hj => hm0 j (helse j hj)) (by simp),
        sum_eq_single i (fun j _ hj => hf0 j hj) (by simp)]
      have hf := show firstPiece P i x y from hi
      by_cases hsel : i ∈ U
      · have hsb := (sparse_block_assignment G P R K z ρ δ href i x y he).mpr hsel
        have hden := hsb.2.2.2.2.2
        have hd : 1-crossDensity G (cls i x) (cls i y) ≠ 0 := by
          dsimp [cls]; linarith
        have hne : x ≠ y := fun e => hsb.2.2.1 (congrArg _ e)
        have hn : ¬H.Adj x y := by
          rintro ⟨_,_,j,hj,hmin,_,_,hpartner⟩
          have eq := unique j ⟨hj,hmin⟩
          subst j
          exact hden.not_ge hpartner.2.2.2.2.2
        have hsing : U = {i} := eq_singleton_iff_unique_mem.mpr ⟨hsel,fun j hj => by
          by_contra h; exact helse j h hj⟩
        have hf' : f i = 0 := by simp [f,fallbackPiece,hsb]
        rw [mf,if_pos hsb,hf',add_zero]
        unfold softMatrix
        simp only [if_neg hne,if_neg hn,hcov,not_true_eq_false,and_false,ite_false,add_zero]
        change (if G.Adj x y then -1 else ∑ j ∈ U, _) = _
        rw [hsing,sum_singleton]
        by_cases hg : G.Adj x y <;> simp [centeredEntry,hg,cls] <;> field_simp [cls] at hd ⊢ <;> ring
      · have hem : U = ∅ := eq_empty_iff_forall_notMem.mpr (fun j hj => by
          by_cases heq : j = i; exact hsel (heq ▸ hj); exact helse j heq hj)
        have hns : ¬sparseBlock G P R K z ρ δ i x y := fun h => hsel ((sparse_block_assignment G P R K z ρ δ href i x y he).mp h)
        rw [hm0 i hsel,zero_add]
        have hem' : sparsePieces G P good cls z ρ δ x y = ∅ := hem
        by_cases eq : x=y
        · subst y; simp [softMatrix,f,fallbackPiece,SimpleGraph.irrefl]
        · by_cases ha : G.Adj x y <;> by_cases hh : H.Adj x y <;>
            simp [softMatrix,he,ha,hh,f,fallbackPiece,hcov,hf,hns,hem',eq]
    · have hempty : U = ∅ := eq_empty_iff_forall_notMem.mpr (fun j hj => hcov ⟨j,(mem_filter.mp hj).1⟩)
      have hn : ¬H.Adj x y := fun h => by obtain ⟨_,_,i,hi,_⟩ := h; exact hcov ⟨i,hi⟩
      have hm' (j : I) : m j = 0 := hm0 j (by simp [hempty])
      have hf' (j : I) : f j = 0 := by
        have ha : ¬ firstPiece P j x y := fun h => hcov ⟨j,h.1⟩
        simp [f,fallbackPiece,ha]
      have hem' : sparsePieces G P good cls z ρ δ x y = ∅ := hempty
      by_cases eq : x=y
      · subst y; simp [softMatrix,hm',hf',SimpleGraph.irrefl]
      · by_cases ha : G.Adj x y <;> simp [softMatrix,hm',hf',eq,ha,hcov,hn,hem']
end Vu

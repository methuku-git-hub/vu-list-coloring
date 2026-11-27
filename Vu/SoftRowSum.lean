module
public import Vu.PartialDecomposition
namespace Vu
open Finset

/-- To bound positive entries it suffices to count ALL eligible regular
classes using the relation with density cutoff zero. The repeated-neighbor
estimate and the good-row discrepancy therefore apply to the same sum. -/
public theorem eligible_density_sum {V I : Type*} [Fintype V] [Fintype I] [DecidableEq V] [LinearOrder I]
    (G : SimpleGraph V) [DecidableRel G.Adj] (P : I → Finset V) (R : ∀ i, Finpartition (P i))
    (D r K : ℕ) (ω ρ δ : ℝ) (hω : 0 ≤ ω) (ho : (r:ℝ)^3*ω ≤ δ) (hs : 8*r*√ρ ≤ δ/4)
    (hdeg : ∀ x, G.degree x ≤ D) (hp : ∀ i, (P i).card ≤ 2*D)
    (hm : ∀ x, (univ.filter fun i => x ∈ P i).card ≤ r)
    (href : ∀ i A, A ∈ (R i).parts → ∀ j < i, ω*D < ((P i ∩ P j).card : ℝ) → A ⊆ P j ∨ Disjoint A (P j))
    (x : V) :
    let J := fun i => partnerGraph G P i (largeClasses (R i) ρ K) (ω*D) ρ 1
    let act := (by classical exact univ.filter fun i => x ∈ goodVertices G (R i) ρ K)
    (by classical exact ∑ i ∈ act, ∑ B ∈ (J i).neighborFinset ((R i).part x),
      crossDensity G ((R i).part x) B * B.card) ≤ (1+δ+δ/4)*D := by
  classical
  intro J act
  let good i := goodVertices G (R i) ρ K
  have hin (i : I) : good i ⊆ P i := filter_subset _ _
  have hact : act.card ≤ r := by
    apply (card_le_card (t := univ.filter fun i => x ∈ P i) ?_).trans (hm x)
    exact fun i hi => mem_filter.mpr ⟨mem_univ _,hin i (mem_filter.mp hi).2⟩
  obtain ⟨E,hE,hEx⟩ := exceptional_occurrence_budget P r D ω δ hω ho x (hm x)
  have hrep := full_partner_degree_sum G P good (fun i => (R i).part) (fun i => largeClasses (R i) ρ K)
    (ω*D) ρ 1 r hin hm (by
      intro i A hA y
      have ha := (mem_filter.mp hA).1
      exact ⟨fun hy => ⟨(R i).le ha hy,(R i).part_eq_of_mem ha hy⟩,
        fun ⟨hy,he⟩ => he ▸ (R i).mem_part hy⟩)
    (fun i A ha => href i A (mem_filter.mp ha).1) x E (fun y => (hE y).mpr)
  let N (B : Finset V) := ((B ∩ G.neighborFinset x).card : ℝ)
  let mass i (B : Finset V) := crossDensity G ((R i).part x) B * B.card
  let blocks i := (J i).neighborFinset ((R i).part x)
  have hn : (∑ i ∈ act, ∑ B ∈ blocks i, N B) ≤ (1+δ)*D := by
    have hh := Nat.cast_le (α := ℝ) |>.mpr hrep
    dsimp only at hh
    push_cast at hh
    change (∑ i ∈ act, ∑ B ∈ blocks i, N B) ≤ _ at hh
    linarith [Nat.cast_le (α := ℝ) |>.mpr (hdeg x)]
  have herr : (∑ i ∈ act, ∑ B ∈ blocks i, |N B-mass i B|) ≤ δ*D/4 := by
    apply (sum_le_sum (g := fun _ => 4*√ρ*(2*D)) (fun i hi => ?_)).trans
    · simp only [sum_const,nsmul_eq_mul]
      have hh := mul_le_mul_of_nonneg_right (Nat.cast_le (α := ℝ) |>.mpr hact)
        (by positivity : 0 ≤ 4*√ρ*(2*(D:ℝ)))
      linarith only [hh,mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg D)]
    · apply (good_partner_discrepancy G P i (R i) (ω*D) ρ 1 K x (mem_filter.mp hi).2).trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact_mod_cast hp i
  have hcell (i : I) (B : Finset V) : mass i B ≤ N B + |N B-mass i B| := by
    linarith [neg_abs_le (N B-mass i B)]
  calc
    _ ≤ ∑ i ∈ act, ∑ B ∈ blocks i, (N B + |N B-mass i B|) :=
      sum_le_sum fun i _ => sum_le_sum fun B _ => hcell i B
    _ ≤ _ := by simp only [sum_add_distrib]; linarith

/-- Positive-entry bound on the completed matrix. -/
public theorem soft_matrix_row_sum {V I : Type*} [Fintype V] [Fintype I] [DecidableEq V] [LinearOrder I]
    (G H : SimpleGraph V) [DecidableRel G.Adj] (P : I → Finset V) (R : ∀ i, Finpartition (P i))
    (D r K : ℕ) (ω ρ δ : ℝ) (hD : 0 < D) (hδ : 0 < δ) (hδ₁ : δ ≤ 1/200)
    (hω : 0 ≤ ω) (ho : (r:ℝ)^3*ω ≤ δ) (hs : 8*r*√ρ ≤ δ/4)
    (hdeg : ∀ x, G.degree x ≤ D) (hp : ∀ i, (P i).card ≤ 2*D)
    (hm : ∀ x, (univ.filter fun i => x ∈ P i).card ≤ r)
    (href : ∀ i A, A ∈ (R i).parts → ∀ j < i, ω*D < ((P i ∩ P j).card : ℝ) → A ⊆ P j ∨ Disjoint A (P j))
    (x : V) :
    let B := softMatrix G P (fun i => goodVertices G (R i) ρ K) (fun i => (R i).part) H (ω*D) ρ δ
    ∑ y, |B x y| ≤ 2/δ*D := by
  classical
  intro B
  let good i := goodVertices G (R i) ρ K
  let cls i := (R i).part
  let d i (A : Finset V) := crossDensity G (cls i x) A
  have hd i A : 0 ≤ d i A := div_nonneg (sum_nonneg (fun _ _ => Nat.cast_nonneg _))
    (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  let J := fun i => partnerGraph G P i (largeClasses (R i) ρ K) (ω*D) ρ 1
  let act := univ.filter fun i => x ∈ good i
  let blocks i := (J i).neighborFinset (cls i x)
  let m (y : V) := ∑ i ∈ act, ∑ A ∈ blocks i, if y ∈ A then d i A else 0
  have hmpos (y : V) : 0 ≤ m y := sum_nonneg (fun i _ => sum_nonneg (fun A _ => by split <;> first | exact hd i A | exact le_rfl))
  have hsum : (∑ y, m y) ≤ (1+δ+δ/4)*D := by
    have eq : (∑ y, m y) = ∑ i ∈ act, ∑ A ∈ blocks i, d i A*A.card := by
      simp only [m]
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      rw [sum_comm]
      apply sum_congr rfl
      intro A _
      simp [← sum_filter,mul_comm]
    rw [eq]
    exact eligible_density_sum G P R D r K ω ρ δ hω ho hs hdeg hp hm href x
  let cost (y : V) : ℝ := (if x = y then 1 else 0) + (if G.Adj x y then 1 else 0)
  have hcost (y : V) : 0 ≤ cost y := by dsimp [cost]; split <;> split <;> norm_num
  have hpoint (y : V) : |B x y| ≤ cost y + m y/δ := by
    have hm0 := div_nonneg (hmpos y) hδ.le
    by_cases he : x = y
    · simp [B,softMatrix,cost,he]; simpa [he] using hm0
    by_cases hh : H.Adj x y
    · simpa [B,softMatrix,he,hh] using add_nonneg (hcost y) hm0
    by_cases hg : G.Adj x y
    · simpa [B,softMatrix,cost,he,hh,hg] using hm0
    let F := sparsePieces G P good cls (ω*D) ρ δ x y
    by_cases hF : F.Nonempty
    · obtain ⟨i,hi⟩ := hF
      have hsing := eq_singleton_iff_unique_mem.mpr ⟨hi,fun j hj =>
        card_le_one.mp (sparse_piece_unique G P good cls (ω*D) ρ δ x y) j hj i hi⟩
      obtain ⟨hpi,hfirst,hn,hxg,hyg,hne,hir,hden⟩ := mem_filter.mp hi
      have hb : cls i y ∈ blocks i := by
        apply ((J i).mem_neighborFinset _ _).mpr
        refine ⟨(mem_filter.mp hxg).2.1,(mem_filter.mp hyg).2.1,hne,?_,hir,?_⟩
        · intro j hj _ hc
          obtain ⟨hx,hy⟩ := (mem_filter.mp hpi).2
          exact hj.not_ge (hfirst j (mem_filter.mpr ⟨mem_univ _,hc.1 ((R i).mem_part hx),hc.2 ((R i).mem_part hy)⟩))
        · simpa using hd i (cls i y)
      have hdom : d i (cls i y) ≤ m y := by
        have hy := (R i).mem_part (mem_filter.mp hyg).1
        calc
          _ = (if y ∈ cls i y then d i (cls i y) else 0) := by simp [cls,hy]
          _ ≤ ∑ A ∈ blocks i, if y ∈ A then d i A else 0 := single_le_sum
            (f := fun A => if y ∈ A then d i A else 0) (fun A _ => by split <;> first | exact hd i A | exact le_rfl) hb
          _ ≤ m y := single_le_sum (f := fun j => ∑ A ∈ blocks j, if y ∈ A then d j A else 0)
            (fun j _ => sum_nonneg (fun A _ => by split <;> first | exact hd j A | exact le_rfl)) (mem_filter.mpr ⟨mem_univ _,hxg⟩)
      have heq : B x y = d i (cls i y)/(1-d i (cls i y)) := by
        change softMatrix G P good cls H (ω*D) ρ δ x y = _
        simp only [softMatrix,if_neg he,if_neg hh,if_neg hg]
        change (∑ j ∈ F, d j (cls j y)/(1-d j (cls j y))) = _
        rw [hsing,sum_singleton]
      change d i (cls i y) < 1-δ at hden
      rw [heq,abs_of_nonneg (div_nonneg (hd i _) (by linarith))]
      simp only [cost,if_neg he,if_neg hg,zero_add]
      exact (div_le_div_of_nonneg_left (hd i _) hδ (by linarith)).trans (div_le_div_of_nonneg_right hdom hδ.le)
    · have hem : F = ∅ := not_nonempty_iff_eq_empty.mp hF
      change |softMatrix G P good cls H (ω*D) ρ δ x y| ≤ _
      simp only [softMatrix,if_neg he,if_neg hh,if_neg hg]
      change |∑ i ∈ F, _| ≤ _
      rw [hem,sum_empty,abs_zero]
      exact add_nonneg (hcost y) hm0
  have hcs : (∑ y, cost y) = 1+G.degree x := by
    simp only [cost,sum_add_distrib]
    simp [← sum_filter,SimpleGraph.degree,SimpleGraph.neighborFinset_def]
  apply (sum_le_sum (fun y _ => hpoint y)).trans
  rw [sum_add_distrib,← sum_div,hcs]
  have hsize : (1:ℝ) ≤ D := by exact_mod_cast hD
  have hdeg' := Nat.cast_le (α := ℝ) |>.mpr (hdeg x)
  rw [div_mul_eq_mul_div,add_div' _ _ _ hδ.ne',div_le_div_iff_of_pos_right hδ]
  nlinarith [mul_le_mul_of_nonneg_right (show 1+(G.degree x:ℝ) ≤ 2*D by linarith) hδ.le,
    mul_le_mul_of_nonneg_right hδ₁ (Nat.cast_nonneg D)]
/-- For the constructed partitions the restricted norm in Lemma 4.6
is the sole remaining matrix hypothesis in Proposition 3.1. -/
public theorem decomposition_of_soft_norm {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D r k₀ K k Rmax : ℕ) (lam ω ρ δ b η : ℝ)
    (hD : 0 < D) (hδ : 0 < δ) (hδ₁ : δ ≤ 1/200) (hω : 0 ≤ ω)
    (ho : (r:ℝ)^3*ω ≤ δ) (hs : 8*r*√ρ ≤ δ/4) (hdeg : ∀ x, G.degree x ≤ D)
    (h : HardDecomposition G D r k₀ K k Rmax lam ω ρ δ b η) :
    let B := partitionSoftMatrix G h.pieces h.partition K (ω*D) ρ δ
    (∀ T : Finset V, T.card ≤ D → RowNormLE B T (η*D)) →
    Nonempty (Decomposition G D k Rmax b (max 10 (2/δ)) η) := by
  classical
  intro B hnorm
  apply decomposition_of_soft_matrix_bounds G D r k₀ K k Rmax lam ω ρ δ b η hδ h _ hnorm
  intro x
  letI := pieceOrder h.pieces
  let H := partitionHardGraph G h.pieces h.partition K (ω*D) ρ δ
  apply (soft_matrix_row_sum G H Subtype.val h.partition D r K ω ρ δ hD hδ hδ₁ hω ho hs hdeg
    (fun i => (h.extracted.1 i.val i.property).2.2.1) (fun v => ?_)
    (fun i A ha j _ => h.refines i A ha j.val j.property) x).trans
  · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg D)
  · rw [univ_eq_attach,filter_attach (fun P : Finset V => v ∈ P) h.pieces,card_map,card_attach]
    exact h.multiplicity v
end Vu

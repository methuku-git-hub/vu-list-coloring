module
public import Vu.PartnerGraph
public import Vu.RegularRows
namespace Vu
open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] public noncomputable def regularPartners (G : SimpleGraph V) [DecidableRel G.Adj]
    {P : Finset V} (R : Finpartition P) (ρ : ℝ) (A : Finset V) : Finset (Finset V) := by
  classical exact R.parts.filter fun B => B ≠ A ∧ ¬ irregularPair G ρ A B

@[expose] public noncomputable def regularRowError (G : SimpleGraph V) [DecidableRel G.Adj]
    {P : Finset V} (R : Finpartition P) (ρ : ℝ) (A : Finset V) (x : V) : ℝ :=
  ∑ B ∈ regularPartners G R ρ A, |((G.neighborFinset x ∩ B).card : ℝ) - crossDensity G A B * B.card|

/-- The good-row bound applied to all regular classes of the actual partition. -/
public theorem irregular_row_count (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V)
    (R : Finpartition P) (ρ : ℝ) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) (A : Finset V) (ha : A ∈ R.parts) :
    ((A.filter fun x => 4*√ρ*P.card < regularRowError G R ρ A x).card : ℝ) ≤ √ρ*A.card := by
  classical
  let F := regularPartners G R ρ A
  have hsub : F ⊆ R.parts := filter_subset _ _
  have hsum : ∑ b : ↥F, ((b.val).card : ℝ) ≤ P.card := by
    rw [sum_coe_sort F (fun U : Finset V => (U.card : ℝ))]
    exact_mod_cast (sum_le_sum_of_subset (f := card) hsub).trans_eq R.sum_card_parts
  have hh := bad_rows_of_regular_pairs G A (fun b : ↥F => b.val) ρ P.card
    (nonempty_iff_ne_empty.mpr (R.ne_empty ha))
    (fun b => nonempty_iff_ne_empty.mpr (R.ne_empty (hsub b.property))) hρ hρ₁
    (Nat.cast_pos.mpr (card_pos.mpr ((nonempty_iff_ne_empty.mpr (R.ne_empty ha)).mono (R.le ha)))) hsum (by
      intro b X hx Y hy hX hY
      by_contra! h
      exact (mem_filter.mp b.property).2.2 ⟨X,hx,Y,hy,hX,hY,h⟩)
  have sum_eq (x : V) := sum_coe_sort F (fun b : Finset V => |((G.neighborFinset x ∩ b).card : ℝ) - crossDensity G A b * b.card|)
  simp_rw [sum_eq] at hh
  exact hh

/-- Nonexceptional classes and good vertices as in Section 4. -/
@[expose] public noncomputable def largeClasses {P : Finset V} (R : Finpartition P) (ρ : ℝ) (K : ℕ) :
    Finset (Finset V) := by classical exact R.parts.filter fun A => ρ*P.card/K ≤ A.card

@[expose] public noncomputable def goodVertices (G : SimpleGraph V) [DecidableRel G.Adj]
    {P : Finset V} (R : Finpartition P) (ρ : ℝ) (K : ℕ) : Finset V := by
  classical exact P.filter fun x => R.part x ∈ largeClasses R ρ K ∧ regularRowError G R ρ (R.part x) x ≤ 4*√ρ*P.card

public theorem good_class_has_two (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V)
    (R : Finpartition P) (ρ : ℝ) (K : ℕ) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1)
    (hsize : 2 ≤ (1-√ρ)*(ρ*P.card/K)) (A : Finset V) (ha : A ∈ largeClasses R ρ K) :
    2 ≤ (A ∩ goodVertices G R ρ K).card := by
  classical
  obtain ⟨ha',hlo⟩ := mem_filter.mp ha
  let bad := A.filter fun x => 4*√ρ*P.card < regularRowError G R ρ A x
  have hs : 0 ≤ 1-√ρ := sub_nonneg.mpr (Real.sqrt_le_one.mpr hρ₁)
  have hh := two_good_rows A bad (filter_subset _ _) ρ (irregular_row_count G P R ρ hρ hρ₁ A ha')
    (hsize.trans (mul_le_mul_of_nonneg_left hlo hs))
  apply hh.trans (card_le_card ?_)
  intro x hx
  obtain ⟨hxA,hxBad⟩ := mem_sdiff.mp hx
  have he := R.part_eq_of_mem ha' hxA
  have hgood : regularRowError G R ρ A x ≤ 4*√ρ*P.card :=
    le_of_not_gt (fun h => hxBad (mem_filter.mpr ⟨hxA,h⟩))
  exact mem_inter.mpr ⟨hxA,mem_filter.mpr ⟨R.le ha' hxA,he ▸ ha,he ▸ hgood⟩⟩

/-- For each good vertex there is another good vertex carrying its label. -/
public theorem other_good_carrier (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V)
    (R : Finpartition P) (ρ : ℝ) (K : ℕ) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1)
    (hsize : 2 ≤ (1-√ρ)*(ρ*P.card/K)) (x : V) (hx : x ∈ goodVertices G R ρ K) :
    ∃ y ≠ x, y ∈ goodVertices G R ρ K ∧ R.part y = R.part x := by
  classical
  have ha := (mem_filter.mp hx).2.1
  have hh := good_class_has_two G P R ρ K hρ hρ₁ hsize _ ha
  obtain ⟨y,hy,hyx⟩ := exists_mem_ne (s := R.part x ∩ goodVertices G R ρ K) (by omega : 1 < (R.part x ∩ goodVertices G R ρ K).card) x
  exact ⟨y,hyx,(mem_inter.mp hy).2,R.part_eq_of_mem (mem_filter.mp ha).1 (mem_inter.mp hy).1⟩

/-- At most (ρ+√ρ)|P| vertices of a piece are unavailable as good rows.
This includes the exceptional classes as well as failures of (G). -/
public theorem nongood_vertices_bound (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V)
    (R : Finpartition P) (ρ : ℝ) (K : ℕ) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1)
    (hk : 0 < K) (hparts : R.parts.card ≤ K) :
    ((P \ goodVertices G R ρ K).card : ℝ) ≤ (ρ+√ρ)*P.card := by
  classical
  let tiny (A : Finset V) := if (A.card : ℝ) < ρ*P.card/K then A else ∅
  let bad (A : Finset V) := A.filter fun x => 4*√ρ*P.card < regularRowError G R ρ A x
  have hcover : P \ goodVertices G R ρ K ⊆ R.parts.biUnion tiny ∪ R.parts.biUnion bad := by
    intro x hx
    obtain ⟨hxP,hn⟩ := mem_sdiff.mp hx
    have hclass := R.part_mem.mpr hxP
    have hm := R.mem_part hxP
    by_cases hsmall : ((R.part x).card : ℝ) < ρ*P.card/K
    · exact mem_union_left _ (mem_biUnion.mpr ⟨_,hclass,by simpa [tiny,hsmall] using hm⟩)
    · have hh : 4*√ρ*P.card < regularRowError G R ρ (R.part x) x := by
        apply lt_of_not_ge
        intro he
        exact hn (mem_filter.mpr ⟨hxP,mem_filter.mpr ⟨hclass,le_of_not_gt hsmall⟩,he⟩)
      have hb : x ∈ bad (R.part x) := mem_filter.mpr ⟨hm,hh⟩
      exact mem_union_right _ (mem_biUnion.mpr ⟨R.part x,hclass,hb⟩)
  have hsum (f : Finset V → Finset V) : ((R.parts.biUnion f).card : ℝ) ≤ ∑ A ∈ R.parts, ((f A).card : ℝ) := by
    exact_mod_cast card_biUnion_le
  have hsmall : ((R.parts.biUnion tiny).card : ℝ) ≤ ρ*P.card := by
    apply (hsum tiny).trans
    have hh (A : Finset V) : ((tiny A).card : ℝ) ≤ ρ*P.card/K := by
      dsimp [tiny]; split
      next h => exact h.le
      next => simp; positivity
    apply (sum_le_sum (fun A (_ : A ∈ R.parts) => hh A)).trans
    simp only [sum_const,nsmul_eq_mul]
    apply (mul_le_mul_of_nonneg_right (Nat.cast_le (α := ℝ) |>.mpr hparts) (by positivity)).trans_eq
    field_simp
  have hbad : ((R.parts.biUnion bad).card : ℝ) ≤ √ρ*P.card := by
    apply (hsum bad).trans
    apply (sum_le_sum (fun A hA => irregular_row_count G P R ρ hρ hρ₁ A hA)).trans_eq
    rw [← mul_sum]
    congr 1
    exact_mod_cast R.sum_card_parts
  have hnat := (card_le_card hcover).trans (card_union_le _ _)
  have hh := Nat.cast_le (α := ℝ) |>.mpr hnat
  push_cast at hh
  linarith

/-- Each partner class contributes a term of the discrepancy sum (G). -/
public theorem good_partner_discrepancy {I : Type*} [LinearOrder I] (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : I → Finset V) (i : I) (R : Finpartition (P i)) (z ρ δ : ℝ) (K : ℕ)
    (x : V) (hx : x ∈ goodVertices G R ρ K) :
    let J := partnerGraph G P i (largeClasses R ρ K) z ρ δ
    (by classical exact ∑ B ∈ J.neighborFinset (R.part x),
      |((B ∩ G.neighborFinset x).card : ℝ) - crossDensity G (R.part x) B * B.card|) ≤ 4*√ρ*(P i).card := by
  classical
  intro J
  have sub : J.neighborFinset (R.part x) ⊆ regularPartners G R ρ (R.part x) := by
    intro B hB
    have hab := (J.mem_neighborFinset _ _).mp hB
    exact mem_filter.mpr ⟨(mem_filter.mp hab.2.1).1,hab.2.2.1.symm,hab.2.2.2.2.1⟩
  simp_rw [Finset.inter_comm _ (G.neighborFinset x)]
  apply (sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => abs_nonneg _)).trans
  exact (mem_filter.mp hx).2.2
end Vu

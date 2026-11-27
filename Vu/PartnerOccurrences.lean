module
public import Vu.PartnerGraph
namespace Vu
open Finset

/-- The sum of degrees into *full* partner classes, counting occurrences
in all pieces. Eligibility makes each nonexceptional neighbor count once.
A neighbor need not be good in any piece. -/
public theorem full_partner_degree_sum {V I : Type*} [Fintype V] [Fintype I] [LinearOrder I] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (P good : I → Finset V)
    (cls : I → V → Finset V) (parts : I → Finset (Finset V)) (z ρ δ : ℝ) (r : ℕ)
    (inside : ∀ i, good i ⊆ P i) (hmult : ∀ x, (univ.filter fun i => x ∈ P i).card ≤ r)
    (memclass : ∀ i A, A ∈ parts i → ∀ y, y ∈ A ↔ y ∈ P i ∧ cls i y = A)
    (refines : ∀ i A, A ∈ parts i → ∀ j < i, z < ((P i ∩ P j).card : ℝ) → A ⊆ P j ∨ Disjoint A (P j))
    (x : V) (E : Finset V) (hex : ∀ y, exceptionalPair P z x y → y ∈ E) :
    let J := fun i => partnerGraph G P i (parts i) z ρ δ
    (by classical exact ∑ i ∈ univ.filter (fun i => x ∈ good i), ∑ B ∈ (J i).neighborFinset (cls i x),
      (B ∩ G.neighborFinset x).card) ≤ G.degree x + r*E.card := by
  classical
  intro J
  let N := G.neighborFinset x
  let active := univ.filter fun i => x ∈ good i
  let sel (i : I) := N.filter fun y => x ∈ good i ∧ y ∈ P i ∧ (J i).Adj (cls i x) (cls i y)
  have heq (i : I) (hi : i ∈ active) : (sel i).card =
      ∑ B ∈ (J i).neighborFinset (cls i x), (B ∩ N).card := by
    have h := card_eq_sum_card_fiberwise (s := sel i) (t := (J i).neighborFinset (cls i x)) (f := cls i)
      (by intro y hy; exact ((J i).mem_neighborFinset _ _).mpr (mem_filter.mp hy).2.2.2)
    rw [h]
    apply sum_congr rfl
    intro B hB
    have hab := ((J i).mem_neighborFinset _ _).mp hB
    have hb : B ∈ parts i := hab.2.1
    congr 1
    ext y
    constructor
    · intro hy
      obtain ⟨hy,hcls⟩ := mem_filter.mp hy
      obtain ⟨hN,_,hP,_⟩ := mem_filter.mp hy
      exact mem_inter.mpr ⟨(memclass i B hb y).mpr ⟨hP,hcls⟩,hN⟩
    · intro hy
      obtain ⟨hyB,hyN⟩ := mem_inter.mp hy
      obtain ⟨hp,hc⟩ := (memclass i B hb y).mp hyB
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨hyN,(mem_filter.mp hi).2,hp,hc ▸ hab⟩,hc⟩
  have hfirst (i : I) (y : V) (hy : y ∈ sel i) (hn : y ∉ E) :
      ∀ j ∈ jointPieces P x y, i ≤ j := by
    obtain ⟨_,hg,hp,hab⟩ := mem_filter.mp hy
    have hA : cls i x ∈ parts i := hab.1
    have hB : cls i y ∈ parts i := hab.2.1
    have sub (B : Finset V) (hb : B ∈ parts i) : B ⊆ P i := fun v hv => ((memclass i B hb v).mp hv).1
    exact ((eligible_iff_first P z i _ _ (sub _ hA) (sub _ hB) x y
      ((memclass i _ hA x).mpr ⟨inside i hg,rfl⟩) ((memclass i _ hB y).mpr ⟨hp,rfl⟩)
      (fun he => hn (hex y he)) (refines i _ hA) (refines i _ hB)).mp hab.2.2.2.1).2
  have htotal := eligible_neighbor_occurrences N E sel r (fun _ => filter_subset _ _) (by
    intro y _ hn i j hi hj
    have joint (k : I) (hk : y ∈ sel k) : k ∈ jointPieces P x y := by
      obtain ⟨_,hg,hp,_⟩ := mem_filter.mp hk
      exact mem_filter.mpr ⟨mem_univ _,inside k hg,hp⟩
    exact le_antisymm (hfirst i y hi hn j (joint j hj)) (hfirst j y hj hn i (joint i hi))) (by
    intro y
    apply (card_le_card (t := univ.filter fun i => y ∈ P i) ?_).trans (hmult y)
    intro i hi
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp (mem_filter.mp hi).2).2.2.1⟩)
  change (∑ i ∈ active, ∑ B ∈ (J i).neighborFinset (cls i x), (B ∩ N).card) ≤ _
  calc
    _ = ∑ i ∈ active, (sel i).card := sum_congr rfl (fun i hi => (heq i hi).symm)
    _ ≤ ∑ i, (sel i).card := sum_le_sum_of_subset (subset_univ _)
    _ ≤ _ := htotal

/-- With the manuscript's threshold ωΔ the additional occurrences through
one vertex cost at most δΔ. The bound also applies to nonedges in the
matrix correction, because it counts the exceptional vertex pairs themselves. -/
public theorem exceptional_occurrence_budget {V I : Type*} [Fintype I] [LinearOrder I] [DecidableEq V]
    (P : I → Finset V) (r D : ℕ) (ω δ : ℝ) (hω : 0 ≤ ω) (hδ : (r : ℝ)^3*ω ≤ δ)
    (x : V) (hr : (univ.filter fun i => x ∈ P i).card ≤ r) :
    ∃ E : Finset V, (∀ y, y ∈ E ↔ exceptionalPair P (ω*D) x y) ∧ (r : ℝ)*E.card ≤ δ*D := by
  classical
  let A := univ.filter fun i => x ∈ P i
  let keep (e : I × I) := if e.1 ≠ e.2 ∧ ((P e.1 ∩ P e.2).card : ℝ) ≤ ω*D then P e.1 ∩ P e.2 else ∅
  let E := (A ×ˢ A).biUnion keep
  refine ⟨E,?_,?_⟩
  · intro y
    constructor
    · intro hy
      obtain ⟨⟨i,j⟩,hp,hy⟩ := mem_biUnion.mp hy
      obtain ⟨hi,hj⟩ := mem_product.mp hp
      dsimp [keep] at hy
      split at hy
      next h =>
        exact ⟨i,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hi).2,(mem_inter.mp hy).1⟩,
          j,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hj).2,(mem_inter.mp hy).2⟩,h⟩
      next => simp at hy
    · rintro ⟨i,hi,j,hj,hn,hc⟩
      obtain ⟨hx,hy⟩ := (mem_filter.mp hi).2
      obtain ⟨hx',hy'⟩ := (mem_filter.mp hj).2
      exact mem_biUnion.mpr ⟨(i,j),mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ _,hx⟩,
        mem_filter.mpr ⟨mem_univ _,hx'⟩⟩,by simp [keep,hn,hc,hy,hy']⟩
  · have hsum : (E.card : ℝ) ≤ ∑ e ∈ A ×ˢ A, ((keep e).card : ℝ) := by exact_mod_cast card_biUnion_le
    have hkeep (e : I × I) : ((keep e).card : ℝ) ≤ ω*D := by
      dsimp [keep]; split
      next h => exact h.2
      next => simp [mul_nonneg hω (Nat.cast_nonneg _)]
    have hA : (A.card : ℝ) ≤ r := Nat.cast_le.mpr hr
    have hE : (E.card : ℝ) ≤ (r : ℝ)^2*(ω*D) := by
      apply (hsum.trans (sum_le_sum (fun e _ => hkeep e))).trans
      simpa [pow_two] using mul_le_mul_of_nonneg_right (mul_le_mul hA hA (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (mul_nonneg hω (Nat.cast_nonneg D))
    have hh := mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg r)
    linarith only [hh,mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg D)]
end Vu

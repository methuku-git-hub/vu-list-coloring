module
public import Vu.RegularRefinement
namespace Vu
open Finset Finpartition

/-- Initial partition of a piece according to membership in intersecting
pieces and the size cutoff. A product bound on the number of classes
suffices because it depends only on the prescribed parameters. -/
public theorem initial_piece_partition {V : Type*} [DecidableEq V] (S : Finset V)
    (F : Finset (Finset V)) (k : ℕ) (hk : 0 < k) :
    ∃ Q : Finpartition S, Q.parts.card ≤ k*2^F.card ∧
      (∀ U ∈ Q.parts, U.card ≤ S.card/k+1) ∧
      ∀ U ∈ Q.parts, ∀ T ∈ F, U ⊆ T ∨ Disjoint U T := by
  classical
  have binary (U : Finset V) (hu : U ∈ (atomise S F).parts) (T : Finset V) (ht : T ∈ F) :
      U ⊆ T ∨ Disjoint U T := by
    obtain ⟨B,_,rfl⟩ := (mem_atomise.mp hu).2
    by_cases hb : T ∈ B
    · exact Or.inl (fun x hx => ((mem_filter.mp hx).2 T ht).mp hb)
    · exact Or.inr (Finset.disjoint_left.mpr (fun x hx hxt => hb (((mem_filter.mp hx).2 T ht).mpr hxt)))
  by_cases h : k ≤ S.card
  · obtain ⟨P,he,hc⟩ := exists_equipartition_card_eq S hk.ne' h
    let Q := P ⊓ atomise S F
    refine ⟨Q,(common_refinement_size S _ _).trans (Nat.mul_le_mul hc.le (card_atomise_le ..)),?_,?_⟩
    · intro U hu
      obtain ⟨p,hp,hle⟩ := (show Q ≤ P from inf_le_left) hu
      exact (card_le_card hle).trans (by simpa [hc] using he.card_part_le_average_add_one hp)
    · intro U hu T ht
      obtain ⟨p,hp,hle⟩ := (show Q ≤ atomise S F from inf_le_right) hu
      exact (binary p hp T ht).imp (fun hx => hle.trans hx) (fun hd => hd.mono_left hle)
  · have hc : S.card ≤ k := (Nat.le_of_not_ge h)
    refine ⟨⊥,?_,?_,?_⟩
    · rw [card_bot]
      exact hc.trans (Nat.le_mul_of_pos_right _ (by positivity))
    · intro U hU
      obtain ⟨x,_,rfl⟩ := mem_bot_iff.mp hU
      simp
    · intro U hU T _
      obtain ⟨x,_,rfl⟩ := mem_bot_iff.mp hU
      by_cases hx : x ∈ T <;> simp [hx]

/-- Regular partition with size and membership control simultaneously.
F is the family of intersections with the large-overlap pieces, pulled
back to this piece's vertex type. -/
public theorem regular_piece_partition (ρ : ℝ) (hρ : 0 < ρ) (hρ₁ : ρ < 1/4)
    (k b : ℕ) (hk : 0 < k) :
    ∃ K : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (F : Finset (Finset V)), F.card ≤ b → ∃ R : Finpartition (univ : Finset V),
      R.parts.card ≤ K ∧ (∀ U ∈ R.parts, U.card ≤ Fintype.card V/k+1) ∧
      (∀ U ∈ R.parts, ∀ T ∈ F, U ⊆ T ∨ Disjoint U T) ∧
      (by classical exact ∑ e ∈ (R.parts ×ˢ R.parts).filter (fun e => e.1 ≠ e.2 ∧ irregularPair G ρ e.1 e.2),
        (e.1.card : ℝ)*e.2.card) ≤ ρ*(Fintype.card V : ℝ)^2 := by
  have hm : 1 ≤ k*2^b := Nat.mul_pos hk (by positivity)
  obtain ⟨K,hK⟩ := regular_refinement ρ hρ hρ₁ (k*2^b) hm
  refine ⟨K,?_⟩
  intro V _ _ G _ F hF
  obtain ⟨Q,hq,hs,hmem⟩ := initial_piece_partition (univ : Finset V) F k hk
  obtain ⟨R,href,hr,hreg⟩ := hK V G Q (hq.trans (Nat.mul_le_mul_left k (Nat.pow_le_pow_right (by decide) hF)))
  refine ⟨R,hr,?_,?_,hreg⟩
  · intro U hu
    obtain ⟨p,hp,hle⟩ := href hu
    exact (card_le_card hle).trans (by simpa using hs p hp)
  · intro U hu T ht
    obtain ⟨p,hp,hle⟩ := href hu
    exact (hmem p hp T ht).imp (fun h => hle.trans h) (fun h => h.mono_left hle)

/-- The number of pieces with a large intersection with P is bounded
independently of Δ and of the order of the graph. Counting P itself among
the candidates only strengthens the form needed for the partition step. -/
public theorem large_piece_intersections {V : Type*} [DecidableEq V]
    (F : Finset (Finset V)) (P : Finset V) (r D : ℕ) (ω : ℝ)
    (hmult : ∀ x ∈ P, (F.filter fun Q => x ∈ Q).card ≤ r)
    (hsize : P.card ≤ 2*D) (hD : 0 < D) (hω : 0 < ω) :
    (by classical exact ((F.filter fun Q => ω*D < ((P ∩ Q).card : ℝ)).card : ℝ)) ≤ 2*r/ω := by
  classical
  let L := F.filter fun Q => ω*D < ((P ∩ Q).card : ℝ)
  have htotal : (∑ Q ∈ F, ((P ∩ Q).card : ℝ)) ≤ (P.card : ℝ)*r := by
    have row (Q : Finset V) : ((P ∩ Q).card : ℝ) = ∑ x ∈ P, if x ∈ Q then 1 else 0 := by simp
    simp_rw [row]
    rw [sum_comm]
    simpa [← sum_filter] using sum_le_sum (fun x hx => (Nat.cast_le (α := ℝ)).mpr (hmult x hx))
  have hh : (L.card : ℝ)*(ω*D) ≤ (2*(D : ℝ))*r := by
    calc
      _ = ∑ _Q ∈ L, ω*D := by simp
      _ ≤ ∑ Q ∈ L, ((P ∩ Q).card : ℝ) := sum_le_sum (fun Q hQ => (mem_filter.mp hQ).2.le)
      _ ≤ ∑ Q ∈ F, ((P ∩ Q).card : ℝ) := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.cast_nonneg _)
      _ ≤ _ := htotal.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hsize) (Nat.cast_nonneg _))
  apply (le_div_iff₀ hω).mpr
  apply (mul_le_mul_iff_of_pos_right (Nat.cast_pos.mpr hD : (0 : ℝ) < D)).mp
  linarith only [hh]

/-- Exceptional pair partners and their occurrences in the pieces through x.
With q the integer part of ωΔ these give the r²ωΔ and r³ωΔ bounds in Section 4. -/
public theorem exceptional_piece_pairs {V : Type*} [DecidableEq V]
    (F : Finset (Finset V)) (x : V) (r q : ℕ) (hx : (F.filter fun P => x ∈ P).card ≤ r) :
    ∃ E : Finset V, (∀ y, y ∈ E ↔ ∃ P ∈ F, ∃ Q ∈ F,
      P ≠ Q ∧ x ∈ P ∧ x ∈ Q ∧ y ∈ P ∧ y ∈ Q ∧ (P ∩ Q).card ≤ q) ∧
      E.card ≤ r^2*q ∧ ∑ P ∈ F.filter (fun P => x ∈ P), (P ∩ E).card ≤ r^3*q := by
  classical
  let A := F.filter fun P => x ∈ P
  let keep (e : Finset V × Finset V) := if e.1 ≠ e.2 ∧ (e.1 ∩ e.2).card ≤ q then e.1 ∩ e.2 else ∅
  let E := (A ×ˢ A).biUnion keep
  have hcount : E.card ≤ r^2*q := by
    apply card_biUnion_le.trans
    calc
      _ ≤ ∑ _e ∈ A ×ˢ A, q := by
        apply sum_le_sum
        intro e _
        dsimp [keep]; split
        next h => exact h.2
        next => simp
      _ ≤ _ := by
        simp only [sum_const,nsmul_eq_mul,card_product,pow_two]
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul hx hx)
  refine ⟨E,?_,hcount,?_⟩
  · intro y
    constructor
    · intro hy
      obtain ⟨⟨P,Q⟩,hpq,hy⟩ := mem_biUnion.mp hy
      obtain ⟨hp,hq⟩ := mem_product.mp hpq
      dsimp [keep] at hy
      split at hy
      next h => exact ⟨P,(mem_filter.mp hp).1,Q,(mem_filter.mp hq).1,h.1,
        (mem_filter.mp hp).2,(mem_filter.mp hq).2,(mem_inter.mp hy).1,(mem_inter.mp hy).2,h.2⟩
      next => simp at hy
    · rintro ⟨P,hP,Q,hQ,hn,hxP,hxQ,hyP,hyQ,hcap⟩
      apply mem_biUnion.mpr ⟨(P,Q),mem_product.mpr ⟨mem_filter.mpr ⟨hP,hxP⟩,mem_filter.mpr ⟨hQ,hxQ⟩⟩,?_⟩
      simp [keep,hn,hcap,hyP,hyQ]
  · apply (sum_le_sum (g := fun _ => r^2*q) (fun P _ => (card_le_card (s := P ∩ E) inter_subset_right).trans hcount)).trans
    simp only [sum_const,nsmul_eq_mul]
    exact (Nat.mul_le_mul_right _ hx).trans_eq (by ring)

/-- Apply the regular refinement simultaneously to all extracted pieces.
Each nonempty final class records membership in every large-overlap piece.
The bound K is chosen before the graph, the degree bound, and the pieces. -/
public theorem regular_partitions_of_pieces (ρ ω : ℝ) (hρ : 0 < ρ) (hρ₁ : ρ < 1/4)
    (hω : 0 < ω) (r k : ℕ) (hk : 0 < k) :
    ∃ K : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (F : Finset (Finset V)) (D : ℕ), 0 < D →
      (∀ x, (F.filter fun P => x ∈ P).card ≤ r) → (∀ P ∈ F, P.card ≤ 2*D) →
      ∀ P ∈ F, ∃ R : Finpartition (univ : Finset (↥P)),
        R.parts.card ≤ K ∧ (∀ U ∈ R.parts, U.card ≤ P.card/k+1) ∧
        (∀ U ∈ R.parts, ∀ Q ∈ F, ω*D < ((P ∩ Q).card : ℝ) →
          (∀ x ∈ U, (x : V) ∈ Q) ∨ (∀ x ∈ U, (x : V) ∉ Q)) ∧
        (by classical exact ∑ e ∈ (R.parts ×ˢ R.parts).filter (fun e => e.1 ≠ e.2 ∧
          irregularPair (G.induce (P : Set V)) ρ e.1 e.2), (e.1.card : ℝ)*e.2.card) ≤ ρ*(P.card : ℝ)^2 := by
  classical
  obtain ⟨K,hK⟩ := regular_piece_partition ρ hρ hρ₁ k ⌈2*(r : ℝ)/ω⌉₊ hk
  refine ⟨K,?_⟩
  intro V _ _ G _ F D hD hm hsize P hp
  let L := F.filter fun Q => ω*D < ((P ∩ Q).card : ℝ)
  let cut (Q : Finset V) : Finset (↥P) := univ.filter fun (x : ↥P) => (x : V) ∈ Q
  have hL : L.card ≤ ⌈2*(r : ℝ)/ω⌉₊ := Nat.cast_le.mp
    ((large_piece_intersections F P r D ω (fun x _ => hm x) (hsize P hp) hD hω).trans (Nat.le_ceil _))
  obtain ⟨R,hs,hsmall,hcut,hirr⟩ := hK (↥P) (G.induce (P : Set V)) (L.image cut) (card_image_le.trans hL)
  refine ⟨R,hs,by simpa using hsmall,?_,by simpa using hirr⟩
  intro U hu Q hQ hgt
  rcases hcut U hu (cut Q) (mem_image_of_mem cut (mem_filter.mpr ⟨hQ,hgt⟩)) with yes | no
  · exact Or.inl (fun x hx => (mem_filter.mp (yes hx)).2)
  · exact Or.inr (fun x hx hm => Finset.disjoint_left.mp no hx (mem_filter.mpr ⟨mem_univ _,hm⟩))
end Vu

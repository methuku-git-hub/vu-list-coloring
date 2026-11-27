module
public import Vu.PiecePartition
namespace Vu
open Finset

variable {V : Type*} [DecidableEq V] (P : Finset V)

/-- View a class of a partition of the induced graph as a set of original vertices. -/
@[expose] public def ambientClass (U : Finset (↥P)) : Finset V := U.map (Function.Embedding.subtype _)

@[simp] public theorem ambient_mem (U : Finset (↥P)) (x : ↥P) :
    x.val ∈ ambientClass P U ↔ x ∈ U := by simp [ambientClass]

public theorem ambient_subset (U : Finset (↥P)) : ambientClass P U ⊆ P :=
  fun _ hx => property_of_mem_map_subtype U hx

public theorem ambient_density [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (↥P)) :
    crossDensity G (ambientClass P A) (ambientClass P B) = crossDensity (G.induce (P : Set V)) A B := by
  classical
  let e : (↥P) ↪ V := Function.Embedding.subtype _
  have hrow (x : ↥P) : G.neighborFinset x ∩ ambientClass P B =
      ambientClass P ((G.induce (P : Set V)).neighborFinset x ∩ B) := by
    ext y
    by_cases hy : y ∈ P
    · let u : ↥P := ⟨y,hy⟩
      change u.val ∈ _ ↔ u.val ∈ _
      simp only [mem_inter, ambient_mem, SimpleGraph.mem_neighborFinset]
      rfl
    · exact ⟨fun h => (hy (ambient_subset P B (mem_inter.mp h).2)).elim,
        fun h => (hy (ambient_subset P _ h)).elim⟩
  unfold crossDensity
  simp only [ambientClass,card_map,sum_map, Function.Embedding.subtype_apply]
  congr 1
  apply sum_congr rfl
  intro x _
  change ((G.neighborFinset x.val ∩ ambientClass P B).card : ℝ) = _
  rw [hrow]; simp [ambientClass]

private theorem ambient_subset_lift (U : Finset (↥P)) (X : Finset V)
    (h : X ⊆ ambientClass P U) : ∃ X' ⊆ U, ambientClass P X' = X := by
  simpa only [ambientClass,map_eq_image] using (subset_image_iff.mp (by simpa only [ambientClass,map_eq_image] using h :
    X ⊆ U.image (Function.Embedding.subtype _)))

public theorem ambient_irregular_iff [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset (↥P)) (ρ : ℝ) :
    irregularPair G ρ (ambientClass P A) (ambientClass P B) ↔
      irregularPair (G.induce (P : Set V)) ρ A B := by
  constructor
  · rintro ⟨X,hX,Y,hY,hxs,hys,hd⟩
    obtain ⟨X',hx,rfl⟩ := ambient_subset_lift P A X hX
    obtain ⟨Y',hy,rfl⟩ := ambient_subset_lift P B Y hY
    exact ⟨_,hx,_,hy,by simpa [ambientClass] using hxs,by simpa [ambientClass] using hys,
      by simpa only [ambient_density] using hd⟩
  · rintro ⟨X,hX,Y,hY,hxs,hys,hd⟩
    exact ⟨ambientClass P X,map_subset_map.mpr hX,ambientClass P Y,map_subset_map.mpr hY,
      by simpa [ambientClass] using hxs, by simpa [ambientClass] using hys,by simpa only [ambient_density] using hd⟩

/-- Transport a partition from the piece's own vertex type to the ambient graph. -/
@[expose] public def ambientPartition (R : Finpartition (univ : Finset (↥P))) : Finpartition P := by
  classical
  let parts := R.parts.image (ambientClass P)
  apply Finpartition.ofExistsUnique parts
  · intro U hu
    obtain ⟨A,_,rfl⟩ := mem_image.mp hu
    exact ambient_subset P A
  · intro x hx
    let u : ↥P := ⟨x,hx⟩
    refine ⟨ambientClass P (R.part u),⟨mem_image_of_mem _ (R.part_mem.mpr (mem_univ u)),
      (ambient_mem P _ u).mpr (R.mem_part (mem_univ u))⟩,?_⟩
    rintro U ⟨hU,hxU⟩
    obtain ⟨A,hA,rfl⟩ := mem_image.mp hU
    exact congrArg (ambientClass P) (R.part_eq_of_mem hA ((ambient_mem P _ u).mp hxU)).symm
  · intro h
    obtain ⟨A,hA,he⟩ := mem_image.mp h
    exact R.ne_empty hA (map_eq_empty.mp he)

@[simp] public theorem ambientPartition_parts (R : Finpartition (univ : Finset (↥P))) :
    (ambientPartition P R).parts = R.parts.image (ambientClass P) := rfl

/-- The ordered irregular class rectangles have the same total area in the
induced and ambient graph. -/
public theorem ambient_irregular_mass [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finpartition (univ : Finset (↥P))) (ρ : ℝ) :
    ((by classical exact ∑ e ∈ ((ambientPartition P R).parts ×ˢ (ambientPartition P R).parts).filter (fun e => e.1 ≠ e.2 ∧ irregularPair G ρ e.1 e.2), (e.1.card : ℝ)*e.2.card) : ℝ) =
    ((by classical exact ∑ e ∈ (R.parts ×ˢ R.parts).filter (fun e => e.1 ≠ e.2 ∧
      irregularPair (G.induce (P : Set V)) ρ e.1 e.2), (e.1.card : ℝ)*e.2.card) : ℝ) := by
  classical
  have hinj : Function.Injective (ambientClass P) := map_injective _
  symm
  apply sum_bij (fun e _ => (ambientClass P e.1,ambientClass P e.2))
  · rintro ⟨A,B⟩ h
    obtain ⟨hAB,hne,hir⟩ := mem_filter.mp h
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_image_of_mem _ (mem_product.mp hAB).1,
      mem_image_of_mem _ (mem_product.mp hAB).2⟩,fun he => hne (hinj he),
      (ambient_irregular_iff P G A B ρ).mpr hir⟩
  · rintro ⟨A,B⟩ _ ⟨C,D⟩ _ he
    exact Prod.ext (hinj (congrArg Prod.fst he)) (hinj (congrArg Prod.snd he))
  · rintro ⟨U,W⟩ h
    obtain ⟨hUW,hne,hir⟩ := mem_filter.mp h
    obtain ⟨A,hA,rfl⟩ := mem_image.mp (mem_product.mp hUW).1
    obtain ⟨B,hB,rfl⟩ := mem_image.mp (mem_product.mp hUW).2
    exact ⟨(A,B),mem_filter.mpr ⟨mem_product.mpr ⟨hA,hB⟩,fun he => hne (congrArg (ambientClass P) he),
      (ambient_irregular_iff P G A B ρ).mp hir⟩,rfl⟩
  · intro e _
    simp [ambientClass]

/-- Partitions on the original vertices satisfying all three conclusions of
the piece refinement, with a single positive uniform class bound. -/
public theorem ambient_regular_partitions (ρ ω : ℝ) (hρ : 0 < ρ) (hρ₁ : ρ < 1/4)
    (hω : 0 < ω) (r k : ℕ) (hk : 0 < k) :
    ∃ K : ℕ, 0 < K ∧ ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (F : Finset (Finset V)) (D : ℕ), 0 < D →
      (∀ x, (F.filter fun P => x ∈ P).card ≤ r) → (∀ P ∈ F, P.card ≤ 2*D) →
      ∀ P ∈ F, ∃ R : Finpartition P,
        R.parts.card ≤ K ∧ (∀ A ∈ R.parts, A.card ≤ P.card/k+1) ∧
        (∀ A ∈ R.parts, ∀ Q ∈ F, ω*D < ((P ∩ Q).card : ℝ) → A ⊆ Q ∨ Disjoint A Q) ∧
        (by classical exact ∑ e ∈ (R.parts ×ˢ R.parts).filter (fun e => e.1 ≠ e.2 ∧
          irregularPair G ρ e.1 e.2), (e.1.card : ℝ)*e.2.card) ≤ ρ*(P.card : ℝ)^2 := by
  classical
  obtain ⟨K,hK⟩ := regular_partitions_of_pieces ρ ω hρ hρ₁ hω r k hk
  refine ⟨K+1,by omega,?_⟩
  intro V _ _ G _ F D hD hm hs P hp
  obtain ⟨R,hc,ha,hcut,hreg⟩ := hK V G F D hD hm hs P hp
  refine ⟨ambientPartition P R,(card_image_le.trans hc).trans (Nat.le_succ _),?_,?_,?_⟩
  · intro A hA
    obtain ⟨U,hU,rfl⟩ := mem_image.mp hA
    simpa [ambientClass] using ha U hU
  · intro A hA Q hQ hgt
    obtain ⟨U,hU,rfl⟩ := mem_image.mp hA
    rcases hcut U hU Q hQ hgt with yes | no
    · exact Or.inl (fun y hy => by obtain ⟨x,hx,rfl⟩ := mem_map.mp hy; exact yes x hx)
    · apply Or.inr (Finset.disjoint_left.mpr ?_)
      intro y hy
      obtain ⟨x,hx,rfl⟩ := mem_map.mp hy
      exact no x hx
  · exact (ambient_irregular_mass P G R ρ).le.trans hreg

end Vu

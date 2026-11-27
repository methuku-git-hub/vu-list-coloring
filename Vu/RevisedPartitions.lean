module
public import Vu.AmbientClasses
public import Vu.EnergyIncrement
namespace Vu.Revised
open Finset
public theorem regular_refinement (ρ : ℝ) (hρ : 0 < ρ) (hρ₁ : ρ < 1/4) (m₀ : ℕ) (hm₀ : 1 ≤ m₀) :
    ∃ K : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (Q : Finpartition (univ : Finset V)), Q.parts.card ≤ m₀ →
      ∃ R : Finpartition (univ : Finset V), R ≤ Q ∧ R.parts.card ≤ K ∧
      (by classical exact ∑ e ∈ (R.parts ×ˢ R.parts).filter (fun e => irregularPair G ρ e.1 e.2),
        (e.1.card : ℝ)*e.2.card) ≤ ρ*(Fintype.card V : ℝ)^2  := by
  simpa only [irregularMass] using energy_regular_refinement ρ hρ m₀

public theorem regular_piece_partition (ρ : ℝ) (hρ : 0 < ρ) (hρ₁ : ρ < 1/4)
    (k b : ℕ) (hk : 0 < k) :
    ∃ K : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (F : Finset (Finset V)), F.card ≤ b → ∃ R : Finpartition (univ : Finset V),
      R.parts.card ≤ K ∧ (∀ U ∈ R.parts, U.card ≤ Fintype.card V/k+1) ∧
      (∀ U ∈ R.parts, ∀ T ∈ F, U ⊆ T ∨ Disjoint U T) ∧
      (by classical exact ∑ e ∈ (R.parts ×ˢ R.parts).filter (fun e =>  irregularPair G ρ e.1 e.2),
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

public theorem regular_partitions_of_pieces (ρ ω : ℝ) (hρ : 0 < ρ) (hρ₁ : ρ < 1/4)
    (hω : 0 < ω) (r k : ℕ) (hk : 0 < k) :
    ∃ K : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (F : Finset (Finset V)) (D : ℕ), 0 < D →
      (∀ x, (F.filter fun P => x ∈ P).card ≤ r) → (∀ P ∈ F, P.card ≤ 2*D) →
      ∀ P ∈ F, ∃ R : Finpartition (univ : Finset (↥P)),
        R.parts.card ≤ K ∧ (∀ U ∈ R.parts, U.card ≤ P.card/k+1) ∧
        (∀ U ∈ R.parts, ∀ Q ∈ F, ω*D < ((P ∩ Q).card : ℝ) →
          (∀ x ∈ U, (x : V) ∈ Q) ∨ (∀ x ∈ U, (x : V) ∉ Q)) ∧
        (by classical exact ∑ e ∈ (R.parts ×ˢ R.parts).filter (fun e => 
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

variable {V : Type*} [DecidableEq V] (P : Finset V)
public theorem ambient_irregular_mass [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finpartition (univ : Finset (↥P))) (ρ : ℝ) :
    ((by classical exact ∑ e ∈ ((ambientPartition P R).parts ×ˢ (ambientPartition P R).parts).filter (fun e =>  irregularPair G ρ e.1 e.2), (e.1.card : ℝ)*e.2.card) : ℝ) =
    ((by classical exact ∑ e ∈ (R.parts ×ˢ R.parts).filter (fun e => 
      irregularPair (G.induce (P : Set V)) ρ e.1 e.2), (e.1.card : ℝ)*e.2.card) : ℝ) := by
  classical
  have hinj : Function.Injective (ambientClass P) := map_injective _
  symm
  apply sum_bij (fun e _ => (ambientClass P e.1,ambientClass P e.2))
  · rintro ⟨A,B⟩ h
    obtain ⟨hAB,hir⟩ := mem_filter.mp h
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_image_of_mem _ (mem_product.mp hAB).1,
      mem_image_of_mem _ (mem_product.mp hAB).2⟩,
      (ambient_irregular_iff P G A B ρ).mpr hir⟩
  · rintro ⟨A,B⟩ _ ⟨C,D⟩ _ he
    exact Prod.ext (hinj (congrArg Prod.fst he)) (hinj (congrArg Prod.snd he))
  · rintro ⟨U,W⟩ h
    obtain ⟨hUW,hir⟩ := mem_filter.mp h
    obtain ⟨A,hA,rfl⟩ := mem_image.mp (mem_product.mp hUW).1
    obtain ⟨B,hB,rfl⟩ := mem_image.mp (mem_product.mp hUW).2
    exact ⟨(A,B),mem_filter.mpr ⟨mem_product.mpr ⟨hA,hB⟩,
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
        (by classical exact ∑ e ∈ (R.parts ×ˢ R.parts).filter (fun e => 
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

end Vu.Revised

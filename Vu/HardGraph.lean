module

public import Vu.EligiblePairs
public import Vu.HardTests

namespace Vu
open Finset

variable {I V : Type*} [Fintype I] [LinearOrder I] [DecidableEq V]

/-- Good vertices carry the label of their unique class in that piece. -/
@[expose] public def carriedLabels (good : I → Finset V) (cls : I → V → Finset V) (x : V) :
    Finset (I × Finset V) := (univ.filter fun i => x ∈ good i).image (fun i => (i,cls i x))

public theorem mem_carried (good : I → Finset V) (cls : I → V → Finset V) (x : V) (i : I) (A : Finset V) :
    (i,A) ∈ carriedLabels good cls x ↔ x ∈ good i ∧ cls i x = A := by
  simp [carriedLabels]

omit [LinearOrder I] in
private theorem joint_symm (P : I → Finset V) (x y : V) : jointPieces P x y = jointPieces P y x := by
  ext i; simp [jointPieces,and_comm]

/-- Hard edges are precisely the original nonexceptional edges whose first
piece has good endpoints in partnered classes. -/
@[expose] public def hardGraph (G : SimpleGraph V) (P good : I → Finset V) (cls : I → V → Finset V)
    (z : ℝ) (partner : I → SimpleGraph (Finset V)) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ ¬exceptionalPair P z x y ∧ ∃ i ∈ jointPieces P x y,
    (∀ j ∈ jointPieces P x y, i ≤ j) ∧ x ∈ good i ∧ y ∈ good i ∧ (partner i).Adj (cls i x) (cls i y)
  symm := ⟨by
    intro x y h
    obtain ⟨he,hn,i,hi,hmin,hx,hy,hp⟩ := h
    rw [joint_symm P y x]
    exact ⟨he.symm,by simpa only [exceptionalPair,joint_symm P y x] using hn,
      i,hi,hmin,hy,hx,hp.symm⟩⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩

/-- The first-piece definition and the eligible-block definition agree on
all nonexceptional graph edges, including edges covered by several pieces. -/
public theorem hardGraph_adj_iff (G : SimpleGraph V) (P good : I → Finset V) (cls : I → V → Finset V)
    (z : ℝ) (partner : I → SimpleGraph (Finset V))
    (inside : ∀ i x, x ∈ good i → x ∈ cls i x ∧ cls i x ⊆ P i)
    (refines : ∀ i x, x ∈ good i → ∀ j < i, z < ((P i ∩ P j).card : ℝ) →
      cls i x ⊆ P j ∨ Disjoint (cls i x) (P j))
    (eligible : ∀ i A B, (partner i).Adj A B → eligibleClasses P z i A B) (x y : V) :
    (hardGraph G P good cls z partner).Adj x y ↔ G.Adj x y ∧ ¬exceptionalPair P z x y ∧
      ∃ i, x ∈ good i ∧ y ∈ good i ∧ (partner i).Adj (cls i x) (cls i y) := by
  constructor
  · rintro ⟨he,hn,i,_,_,hx,hy,hp⟩
    exact ⟨he,hn,i,hx,hy,hp⟩
  · rintro ⟨he,hn,i,hx,hy,hp⟩
    obtain ⟨ha,has⟩ := inside i x hx
    obtain ⟨hb,hbs⟩ := inside i y hy
    obtain ⟨hi,hmin⟩ := (eligible_iff_first P z i _ _ has hbs x y ha hb hn
      (refines i x hx) (refines i y hy)).mp (eligible i _ _ hp)
    exact ⟨he,hn,i,hi,hmin,hx,hy,hp⟩

/-- Construct the partner label sets at columns and the sets W of partner
vertices. The same hard-edge label supplies both memberships. -/
public theorem hardGraph_oriented_labels [Fintype V] (G : SimpleGraph V) (P good : I → Finset V)
    (cls : I → V → Finset V) (z : ℝ) (J : I → SimpleGraph (Finset V))
    (r K : ℕ) (hmult : ∀ x, (univ.filter fun i => x ∈ good i).card ≤ r)
    (degree : ∀ i A, (by classical exact (J i).degree A) ≤ K) :
    let L := carriedLabels good cls
    ∃ (partners : V → Finset (I × Finset V)) (W : I × Finset V → Finset V),
      (∀ y, (partners y).card ≤ r*K) ∧
      (∀ a y, y ∈ W a ↔ ∃ b ∈ L y, a.1 = b.1 ∧ (J a.1).Adj a.2 b.2) ∧
      ∀ x y, (hardGraph G P good cls z J).Adj x y → ∃ a ∈ L x, a ∈ partners y ∧ y ∈ W a := by
  classical
  intro L
  let M (b : I × Finset V) := ((J b.1).neighborFinset b.2).image (fun A => (b.1,A))
  let partners y := (L y).biUnion M
  let W (a : I × Finset V) := univ.filter (fun y => ∃ b ∈ L y, a.1 = b.1 ∧ (J a.1).Adj a.2 b.2)
  refine ⟨partners,W,?_,by simp [W],?_⟩
  · intro y
    apply card_biUnion_le.trans
    have hL : (L y).card ≤ r := card_image_le.trans (hmult y)
    calc
      _ ≤ ∑ _b ∈ L y, K := sum_le_sum (fun b _ => card_image_le.trans (by simpa using degree b.1 b.2))
      _ ≤ _ := by simpa using Nat.mul_le_mul_right K hL
  · rintro x y ⟨_,_,i,_,_,hx,hy,hp⟩
    have ha := (mem_carried good cls x i _).mpr ⟨hx,rfl⟩
    have hb := (mem_carried good cls y i _).mpr ⟨hy,rfl⟩
    refine ⟨(i,cls i x),ha,mem_biUnion.mpr ⟨(i,cls i y),hb,?_⟩,
      mem_filter.mpr ⟨mem_univ _,(i,cls i y),hb,rfl,hp⟩⟩
    exact mem_image.mpr ⟨_,((J i).mem_neighborFinset _ _).mpr hp.symm,rfl⟩

end Vu

module
public import Vu.HardGraph
namespace Vu
open Finset

public theorem density_swap {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (A B : Finset V) : crossDensity G A B = crossDensity G B A := by
  simp only [crossDensity_eq_edgeDensity, G.edgeDensity_comm A B]

public theorem irregular_swap {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (ρ : ℝ) (A B : Finset V) : irregularPair G ρ A B → irregularPair G ρ B A := by
  rintro ⟨X,hX,Y,hY,hxs,hys,hbad⟩
  exact ⟨Y,hY,X,hX,hys,hxs,by simpa only [density_swap G Y X,density_swap G B A] using hbad⟩

/-- The actual partner relation of Section 4. Its vertices are ambient
classes, with all other subsets isolated. The allowed classes in this piece
are the nonexceptional classes from the partition. -/
@[expose] public def partnerGraph {V I : Type*} [Fintype V] [DecidableEq V] [LinearOrder I]
    (G : SimpleGraph V) [DecidableRel G.Adj] (P : I → Finset V) (i : I) (parts : Finset (Finset V))
    (z ρ δ : ℝ) : SimpleGraph (Finset V) where
  Adj A B := A ∈ parts ∧ B ∈ parts ∧ A ≠ B ∧ eligibleClasses P z i A B ∧
    ¬irregularPair G ρ A B ∧ 1-δ ≤ crossDensity G A B
  symm := ⟨fun A B h => ⟨h.2.1,h.1,h.2.2.1.symm,
    fun j hj hgt hh => h.2.2.2.1 j hj hgt ⟨hh.2,hh.1⟩,
    fun hbad => h.2.2.2.2.1 (irregular_swap G ρ B A hbad),
    (density_swap G A B) ▸ h.2.2.2.2.2⟩⟩
  loopless := ⟨fun _ h => h.2.2.1 rfl⟩

public theorem partnerGraph_degree {V I : Type*} [Fintype V] [DecidableEq V] [LinearOrder I]
    (G : SimpleGraph V) [DecidableRel G.Adj] (P : I → Finset V) (i : I) (parts : Finset (Finset V))
    (z ρ δ : ℝ) (A : Finset V) :
    (by classical exact (partnerGraph G P i parts z ρ δ).degree A) ≤ parts.card := by
  classical
  let J := partnerGraph G P i parts z ρ δ
  apply card_le_card (s := J.neighborFinset A)
  intro B hB
  exact ((J.mem_neighborFinset A B).mp hB).2.1

/-- The concrete assignment to hard edges provides oriented witnesses with
at most rK candidate partners at each column. -/
public theorem dense_pair_hard_edges {V I : Type*} [Fintype V] [Fintype I] [DecidableEq V] [LinearOrder I]
    (G : SimpleGraph V) [DecidableRel G.Adj] (P good : I → Finset V)
    (cls : I → V → Finset V) (parts : I → Finset (Finset V)) (z ρ δ : ℝ)
    (r K : ℕ) (hmult : ∀ x, (univ.filter fun i => x ∈ good i).card ≤ r)
    (hparts : ∀ i, (parts i).card ≤ K) :
    let J := fun i => partnerGraph G P i (parts i) z ρ δ
    let H := hardGraph G P good cls z J
    let L := carriedLabels good cls
    ∃ (partners : V → Finset (I × Finset V)) (W : I × Finset V → Finset V),
      (∀ y, (partners y).card ≤ r*K) ∧
      (∀ a y, y ∈ W a ↔ ∃ b ∈ L y, a.1 = b.1 ∧ (J a.1).Adj a.2 b.2) ∧
      ∀ x y, H.Adj x y → ∃ a ∈ L x, a ∈ partners y ∧ y ∈ W a := by
  exact hardGraph_oriented_labels G P good cls z _ r K hmult (fun i A =>
    (partnerGraph_degree G P i (parts i) z ρ δ A).trans (hparts i))
end Vu

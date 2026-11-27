module
public import Vu.PartitionTests
public import Vu.GoodClasses
namespace Vu
open Finset

/-- Both hard-neighbor conclusions for the graph cut out by the actual
partition good rows. Each retained class automatically has a second witness. -/
public theorem good_partition_hard_tests (r K : ℕ) (hr : 0 < r) (η : ℝ) (he : 0 < η) :
    ∃ D₀ : ℕ, ∀ D ≥ D₀, ∀ (V I : Type*) [Fintype V] [Fintype I] [DecidableEq V] [LinearOrder I]
      (G : SimpleGraph V) [DecidableRel G.Adj] (P : I → Finset V) (R : ∀ i, Finpartition (P i)) (t : ℕ) (ω ρ δ s : ℝ),
    0 < s → 0 ≤ ω → 0 ≤ δ → δ ≤ 1/200 → (r : ℝ)^3*ω ≤ δ → 8*r*√ρ ≤ δ/4 →
    (t : ℝ)+4*δ*D ≤ s → (∀ x, G.degree x ≤ D) →
    (∀ x y, x ≠ y → Fintype.card (G.commonNeighbors x y) ≤ t) →
    (∀ i, (P i).card ≤ 2*D) → (∀ i, (R i).parts.card ≤ K) →
    (∀ x, (univ.filter fun i => x ∈ P i).card ≤ r) →
    (∀ i A, A ∈ (R i).parts → ∀ j < i, ω*D < ((P i ∩ P j).card : ℝ) → A ⊆ P j ∨ Disjoint A (P j)) →
    0 < ρ → ρ ≤ 1 → (∀ i, 2 ≤ (1-√ρ)*(ρ*(P i).card/K)) →
    let good := fun i => goodVertices G (R i) ρ K
    let cls := fun i => (R i).part
    let J := fun i => partnerGraph G P i (largeClasses (R i) ρ K) (ω*D) ρ δ
    let H := hardGraph G P good cls (ω*D) J
    ∃ U : V → Finset (Finset V),
      (∀ x, (U x).biUnion id = (by classical exact H.neighborFinset x)) ∧
      (∀ x, ∀ B ∈ U x, (B.card : ℝ) ≤ s) ∧ (∀ x, ((U x).card : ℝ) ≤ 2*D/s+1) ∧
      ∀ T : Finset V, T.card ≤ D → ∃ S : V → Finset V, (∀ x ∈ T, S x = ∅ ∨ S x ∈ U x) ∧
        (by classical exact RowNormLE (fun x z => if H.Adj x z ∧ z ∉ S x then 1 else 0) T (η*D)) := by
  classical
  obtain ⟨D₀,hD⟩ := partition_hard_tests r K hr η he
  refine ⟨D₀,?_⟩
  intro D hd V I _ _ _ _ G _ P R t ω ρ δ s hs hω hδ hδ' ho hsq hsave hdeg hcodeg
    hp hk hm href hρ hρ₁ htwo good cls J H
  apply hD D hd V I G P good cls (fun i => largeClasses (R i) ρ K) t ω ρ δ s
    hs hω hδ hδ' ho hsq hsave hdeg hcodeg hp
  · exact fun i => (card_le_card (filter_subset _ _)).trans (hk i)
  · exact fun i => filter_subset _ _
  · exact hm
  · intro i A hA y
    have ha := (mem_filter.mp hA).1
    exact ⟨fun hy => ⟨(R i).le ha hy,(R i).part_eq_of_mem ha hy⟩,
      fun ⟨hy,he⟩ => he ▸ (R i).mem_part hy⟩
  · exact fun i A hA => href i A (mem_filter.mp hA).1
  · exact fun i => other_good_carrier G (P i) (R i) ρ K hρ hρ₁ (htwo i)
  · exact fun i => good_partner_discrepancy G P i (R i) (ω*D) ρ δ K

end Vu

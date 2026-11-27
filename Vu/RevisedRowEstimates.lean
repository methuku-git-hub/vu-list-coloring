module
public import Vu.RevisedOverlap
namespace Vu.Revised.Classes
open Finset
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
  {G : SimpleGraph V} [DecidableRel G.Adj] {D r K : ℕ} {ω ρ δ : ℝ} (d : Classes G D r K ω ρ δ I)

@[expose] public noncomputable def blocks (i : I) (x : V) :=
  (d.partition i).parts.filter (fun B => by classical exact decide (x ∈ d.good i ∧ d.regular i (d.part i x) B) = true)
public theorem mem_blocks (i : I) (x : V) (B : Finset V) :
    B ∈ d.blocks i x ↔ B ∈ (d.partition i).parts ∧ x ∈ d.good i ∧ d.regular i (d.part i x) B := by
  classical simp [blocks]
@[expose] public noncomputable def count (x : V) (B : Finset V) : ℝ := (G.neighborFinset x ∩ B).card
@[expose] public noncomputable def err (i : I) (x : V) (B : Finset V) : ℝ := |count (G := G) x B-crossDensity G (d.part i x) B*B.card|

/-- The two row estimates, on all eligible regular classes, including a class paired with itself. -/
public theorem row_estimates (x : V) (hω : 0 ≤ ω) (ho : (r:ℝ)^2*ω ≤ 1) (hρ : 0 ≤ ρ)
    (hs : 8*r*√ρ ≤ δ) (hdeg : G.degree x ≤ D) :
    (∑ i, ∑ B ∈ d.blocks i x, count (G := G) x B) ≤ 2*D ∧
    (∑ i, ∑ B ∈ d.blocks i x, d.err i x B) ≤ δ*D := by
  classical
  let N := G.neighborFinset x
  let S i := (d.blocks i x).biUnion (fun B => N ∩ B)
  have rep i : (S i).card = ∑ B ∈ d.blocks i x, (N ∩ B).card := by
    apply card_biUnion
    intro A ha B hb hab
    exact ((d.partition i).supIndep.pairwiseDisjoint ((d.mem_blocks ..).mp ha).1
      ((d.mem_blocks ..).mp hb).1 hab).mono inter_subset_right inter_subset_right
  have occ := d.row_occurrences x N S hω (by
    intro i y hy
    obtain ⟨B,hB,hy⟩ := mem_biUnion.mp hy
    obtain ⟨hB,hx,hreg⟩ := (d.mem_blocks ..).mp hB
    obtain ⟨hn,hy⟩ := mem_inter.mp hy
    exact ⟨hn,d.good_subset i hx,(d.partition i).le hB hy,by
      simpa [part,(d.partition i).part_eq_of_mem hB hy] using hreg.1⟩)
  simp_rw [rep,Nat.cast_sum] at occ
  have hN : (N.card:ℝ) ≤ D := by exact_mod_cast (show N.card ≤ D by simpa [N] using hdeg)
  have sumErr (i : I) (hi : x ∈ d.good i) : (∑ B ∈ d.blocks i x, d.err i x B) ≤ 4*√ρ*(d.piece i).card := by
    have hsub : d.blocks i x ⊆ regularPartners G (d.partition i) ρ (d.part i x) := by
      intro B hb
      obtain ⟨hB,_,h⟩ := (d.mem_blocks ..).mp hb
      exact mem_filter.mpr ⟨hB,h.2⟩
    exact (sum_le_sum_of_subset_of_nonneg hsub (fun B _ _ => abs_nonneg _)).trans (mem_filter.mp hi).2
  refine ⟨?_,?_⟩
  · change ∑ i, ∑ B ∈ d.blocks i x, ((N ∩ B).card:ℝ) ≤ 2*D
    linarith only [occ,hN,mul_le_mul_of_nonneg_right ho (Nat.cast_nonneg D)]
  let A := univ.filter fun i => x ∈ d.good i
  rw [←sum_subset (subset_univ A) (fun i _ hi => ?_)]
  · apply (sum_le_sum (fun i hi => (sumErr i (mem_filter.mp hi).2).trans
      (mul_le_mul_of_nonneg_left (by exact_mod_cast d.size i : ((d.piece i).card:ℝ) ≤ 2*D) (by positivity)))).trans
    have hA : A.card ≤ r := (card_le_card (filter_subset_filter _ (by rfl) : A ⊆ A)).trans (by
      apply le_trans (card_le_card (t := univ.filter (fun i => x ∈ d.piece i)) ?_) (d.multiplicity x)
      exact fun i hi => mem_filter.mpr ⟨mem_univ _,d.good_subset i (mem_filter.mp hi).2⟩)
    simp only [sum_const,nsmul_eq_mul]
    apply (mul_le_mul_of_nonneg_right (Nat.cast_le (α := ℝ) |>.mpr hA) (by positivity)).trans
    linarith only [mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg D)]
  · have h : x ∉ d.good i := fun h => hi (mem_filter.mpr ⟨mem_univ _,h⟩)
    have hem : d.blocks i x = ∅ := eq_empty_iff_forall_notMem.mpr (fun B hb => h ((d.mem_blocks ..).mp hb).2.1)
    simp [hem]
end Vu.Revised.Classes

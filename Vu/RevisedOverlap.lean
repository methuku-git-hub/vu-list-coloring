module
public import Vu.RevisedClasses
namespace Vu.Revised.Classes
open Finset
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
  {G : SimpleGraph V} [DecidableRel G.Adj] {D r K : ℕ} {ω ρ δ : ℝ} (d : Classes G D r K ω ρ δ I)

@[expose] public def admissible (i : I) (x y : V) := x ∈ d.piece i ∧ y ∈ d.piece i ∧ d.eligible i (d.part i x) (d.part i y)
public theorem ordinary_admissible {i : I} {x y : V} (h : d.ordinary i x y) : d.admissible i x y :=
  ⟨d.good_subset i h.1,d.good_subset i h.2.1,h.2.2.1.1⟩

/-- Eligible entries assigned earlier lie in a small intersection at the row vertex. -/
public theorem earlier_piece {i : I} {x y : V} (ha : d.admissible i x y) (hn : ¬ d.first i x y) :
    ∃ j, x ∈ d.piece j ∧ y ∈ d.piece i ∩ d.piece j ∧ ((d.piece i ∩ d.piece j).card:ℝ) ≤ ω*D := by
  classical
  have hi : i ∈ jointPieces d.piece x y := mem_filter.mpr ⟨mem_univ _,ha.1,ha.2.1⟩
  have hex : ∃ j ∈ jointPieces d.piece x y, j < i := by
    by_contra! hh
    exact hn ⟨hi,hh⟩
  obtain ⟨j,hj,hlt⟩ := hex
  obtain ⟨hx,hy⟩ := (mem_filter.mp hj).2
  refine ⟨j,hx,mem_inter.mpr ⟨ha.2.1,hy⟩,le_of_not_gt (fun hgt => ?_)⟩
  apply ha.2.2 j hlt hgt
  exact ⟨(d.refines i _ ((d.partition i).part_mem.mpr ha.1) j hlt hgt).resolve_right
    (fun h => disjoint_left.mp h ((d.partition i).mem_part ha.1) hx),
    (d.refines i _ ((d.partition i).part_mem.mpr ha.2.1) j hlt hgt).resolve_right
    (fun h => disjoint_left.mp h ((d.partition i).mem_part ha.2.1) hy)⟩

/-- Lemma on overlapping pieces, with incidences counted separately for each piece. -/
public theorem earlier_occurrences (x : V) (hω : 0 ≤ ω) :
    (by classical exact ∑ i, ((univ.filter (fun y => d.admissible i x y ∧ ¬d.first i x y)).card:ℝ)) ≤ r^2*ω*D := by
  classical
  let active := univ.filter fun i => x ∈ d.piece i
  let bad i := univ.filter (fun y => d.admissible i x y ∧ ¬d.first i x y)
  let small i j := if ((d.piece i ∩ d.piece j).card:ℝ) ≤ ω*D then d.piece i ∩ d.piece j else ∅
  have size i j : ((small i j).card:ℝ) ≤ ω*D := by dsimp [small]; split <;> simp_all [mul_nonneg hω (Nat.cast_nonneg D)]
  have one i : ((bad i).card:ℝ) ≤ active.card*(ω*D) := by
    have sub : bad i ⊆ active.biUnion (small i) := by
      intro y hy
      obtain ⟨j,hx,hy,hs⟩ := d.earlier_piece (mem_filter.mp hy).2.1 (mem_filter.mp hy).2.2
      exact mem_biUnion.mpr ⟨j,mem_filter.mpr ⟨mem_univ _,hx⟩,by simpa [small,hs] using hy⟩
    apply (Nat.cast_le.mpr ((card_le_card sub).trans card_biUnion_le)).trans
    push_cast
    simpa using sum_le_sum (s := active) (fun j _ => size i j)
  have zero (i : I) (hi : i ∉ active) : bad i = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro y hy
    exact hi (mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hy).2.1.1⟩)
  change ∑ i, ((bad i).card:ℝ) ≤ _
  rw [←sum_subset (subset_univ active) (fun i _ hi => by simp [zero i hi])]
  apply (sum_le_sum (fun i _ => one i)).trans
  simp only [sum_const,nsmul_eq_mul]
  have h := Nat.cast_le (α := ℝ) |>.mpr (d.multiplicity x)
  change (active.card:ℝ) ≤ r at h
  calc
    _ = (active.card:ℝ)^2*(ω*D) := by ring
    _ ≤ (r:ℝ)^2*(ω*D) := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) h _) (by positivity)
    _ = _ := by ring

/-- A sum of selected occurrences in any row costs one copy of each column,
plus the incidences already assigned to an earlier piece. -/
public theorem row_occurrences (x : V) (Y : Finset V) (S : I → Finset V) (hω : 0 ≤ ω)
    (hs : ∀ i y, y ∈ S i → y ∈ Y ∧ d.admissible i x y) :
    (∑ i, ((S i).card:ℝ)) ≤ Y.card + r^2*ω*D := by
  classical
  let F i := (S i).filter fun y => d.first i x y
  let E i := (S i).filter fun y => ¬d.first i x y
  have hdis : (↑(univ : Finset I) : Set I).PairwiseDisjoint F := by
    intro i _ j _ hij
    exact disjoint_left.mpr (fun y hi hj => hij (d.first_unique (mem_filter.mp hi).2 (mem_filter.mp hj).2))
  have hf : (∑ i, (F i).card) ≤ Y.card := by
    rw [←card_biUnion hdis]
    apply card_le_card
    intro y hy
    obtain ⟨i,_,h⟩ := mem_biUnion.mp hy
    exact (hs i y (mem_filter.mp h).1).1
  have he i : E i ⊆ univ.filter (fun y => d.admissible i x y ∧ ¬d.first i x y) :=
    fun y h => mem_filter.mpr ⟨mem_univ _,(hs i y (mem_filter.mp h).1).2,(mem_filter.mp h).2⟩
  have hsum i : ((S i).card:ℝ) = (F i).card+(E i).card := by exact_mod_cast (card_filter_add_card_filter_not _).symm
  simp_rw [hsum,sum_add_distrib]
  exact add_le_add (by exact_mod_cast hf) ((sum_le_sum (fun i _ => Nat.cast_le (α := ℝ) |>.mpr (card_le_card (he i)))).trans (d.earlier_occurrences x hω))
end Vu.Revised.Classes

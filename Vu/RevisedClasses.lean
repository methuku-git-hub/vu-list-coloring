module
public import Vu.RevisedRectangles
public import Vu.RevisedGood
namespace Vu.Revised
open Finset
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]

/-- Data used after the regular partitions have been fixed. -/
public structure Classes (G : SimpleGraph V) [DecidableRel G.Adj] (D r K : ℕ) (ω ρ δ : ℝ) (I : Type*) [Fintype I] [LinearOrder I] where
  piece : I → Finset V
  partition : ∀ i, Finpartition (piece i)
  size : ∀ i, (piece i).card ≤ 2*D
  multiplicity : ∀ x, (univ.filter fun i => x ∈ piece i).card ≤ r
  num : ∀ i, (partition i).parts.card ≤ K
  refines : ∀ i A, A ∈ (partition i).parts → ∀ j < i, ω*D < ((piece i ∩ piece j).card:ℝ) →
    A ⊆ piece j ∨ Disjoint A (piece j)
  irregular : ∀ i, (by classical exact ∑ e ∈ ((partition i).parts ×ˢ (partition i).parts).filter (fun e => irregularPair G ρ e.1 e.2), (e.1.card:ℝ)*e.2.card) ≤ ρ*((piece i).card:ℝ)^2

namespace Classes
variable {G : SimpleGraph V} [DecidableRel G.Adj] {D r K : ℕ} {ω ρ δ : ℝ}
  (d : Classes G D r K ω ρ δ I)
@[expose] public noncomputable def good (i : I) := goodVertices G (d.partition i) ρ
@[expose] public noncomputable def part (i : I) (x : V) := (d.partition i).part x
@[expose] public def eligible (i : I) (A B : Finset V) := eligibleClasses d.piece (ω*D) i A B
@[expose] public def first (i : I) (x y : V) := i ∈ jointPieces d.piece x y ∧ ∀ j ∈ jointPieces d.piece x y, i ≤ j
@[expose] public def regular (i : I) (A B : Finset V) := d.eligible i A B ∧ ¬ irregularPair G ρ A B
@[expose] public noncomputable def low (i : I) (A B : Finset V) := d.regular i A B ∧ crossDensity G A B < 1-δ
@[expose] public noncomputable def high (i : I) (A B : Finset V) := d.regular i A B ∧ 1-δ ≤ crossDensity G A B
@[expose] public noncomputable def ordinary (i : I) (x y : V) := x ∈ d.good i ∧ y ∈ d.good i ∧ d.low i (d.part i x) (d.part i y)
@[expose] public noncomputable def dense (i : I) (x y : V) := x ∈ d.good i ∧ y ∈ d.good i ∧ d.high i (d.part i x) (d.part i y)
public theorem first_symm (i : I) (x y : V) : d.first i x y ↔ d.first i y x := by
  have e : jointPieces d.piece x y = jointPieces d.piece y x := by ext; simp [jointPieces,and_comm]
  simp only [first,e]
public theorem first_unique {i j : I} {x y : V} (hi : d.first i x y) (hj : d.first j x y) : i=j :=
  le_antisymm (hi.2 _ hj.1) (hj.2 _ hi.1)
public theorem first_eligible {i : I} {x y : V} (h : d.first i x y) : d.eligible i (d.part i x) (d.part i y) := by
  obtain ⟨hx,hy⟩ := (mem_filter.mp h.1).2
  intro j hj _ hab
  exact hj.not_ge (h.2 j (mem_filter.mpr ⟨mem_univ _,hab.1 ((d.partition i).mem_part hx),hab.2 ((d.partition i).mem_part hy)⟩))
public theorem eligible_swap (i : I) (A B : Finset V) (h : d.eligible i A B) : d.eligible i B A :=
  fun j hj hz hg => h j hj hz ⟨hg.2,hg.1⟩
public theorem regular_swap (i : I) (A B : Finset V) (h : d.regular i A B) : d.regular i B A :=
  ⟨d.eligible_swap i A B h.1,fun hh => h.2 (irregular_swap G ρ B A hh)⟩
public theorem ordinary_swap (i : I) (x y : V) (h : d.ordinary i x y) : d.ordinary i y x :=
  ⟨h.2.1,h.1,d.regular_swap _ _ _ h.2.2.1,(density_swap G _ _) ▸ h.2.2.2⟩
public theorem dense_swap (i : I) (x y : V) (h : d.dense i x y) : d.dense i y x :=
  ⟨h.2.1,h.1,d.regular_swap _ _ _ h.2.2.1,(density_swap G _ _) ▸ h.2.2.2⟩
public theorem good_subset (i : I) : d.good i ⊆ d.piece i := filter_subset _ _
@[expose] public def hardGraph : SimpleGraph V where
  Adj x y := G.Adj x y ∧ ∃ i, d.first i x y ∧ d.dense i x y
  symm := ⟨fun x y ⟨h,i,hf,hd⟩ => ⟨h.symm,i,(d.first_symm i x y).mp hf,d.dense_swap i x y hd⟩⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩
@[expose] public noncomputable def block (i : I) (x y : V) : ℝ := by
  classical exact if d.ordinary i x y then centeredEntry G (crossDensity G (d.part i x) (d.part i y)) x y else 0
@[expose] public noncomputable def beta (x y : V) : ℝ := by
  classical exact if G.Adj x y then -1 else ∑ i, if d.first i x y then d.block i x y else 0
public theorem block_symm (i : I) (x y : V) : d.block i x y = d.block i y x := by
  by_cases h : d.ordinary i x y
  · simp [block,h,d.ordinary_swap i x y h,centeredEntry,density_swap G (d.part i x) (d.part i y),G.adj_comm x y]
  · simp [block,h,show ¬d.ordinary i y x from fun h' => h (d.ordinary_swap i y x h')]
public theorem beta_symm (x y : V) : d.beta x y = d.beta y x := by
  classical
  by_cases h : G.Adj x y
  · simp [beta,h,h.symm]
  simp only [beta,if_neg h,if_neg (fun (hy : G.Adj y x) => h hy.symm)]
  exact sum_congr rfl (fun i _ => by simp only [d.first_symm i x y,d.block_symm i x y])
public theorem block_bound (i : I) (x y : V) (hδ : 0 < δ) : |d.block i x y| ≤ 1/δ := by
  by_cases h : d.ordinary i x y
  · have den := h.2.2.2
    have hu := density_mem_unit G (d.part i x) (d.part i y)
    simp only [block,if_pos h,centeredEntry,abs_div]
    rw [abs_of_pos (by linarith : 0 < 1-crossDensity G (d.part i x) (d.part i y))]
    apply le_trans (div_le_div_of_nonneg_right (b := (1:ℝ)) ?_ (by linarith))
    · exact one_div_le_one_div_of_le hδ (by linarith)
    · split <;> apply abs_le.mpr <;> constructor <;> linarith
  · simp [block,h,hδ.le]

end Classes
end Vu.Revised

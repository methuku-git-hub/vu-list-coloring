module
public import Vu.RevisedOverlap
public import Vu.PartitionMatrix
namespace Vu.Revised
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Decompose a sum over X into its restrictions to the classes of a partition. -/
public theorem sum_parts_inter {P : Finset V} (R : Finpartition P) (X : Finset V) (f : V → ℝ)
    (supp : ∀ x ∈ X, x ∉ P → f x = 0) :
    (∑ A ∈ R.parts, ∑ x ∈ X ∩ A, f x) = ∑ x ∈ X, f x := by
  classical
  have eq (A : Finset V) : (∑ x ∈ X ∩ A, f x) = ∑ x ∈ A, if x ∈ X then f x else 0 := by
    simp only [←sum_filter]
    congr 1; ext; simp [and_comm]
  simp_rw [eq]
  rw [sum_partition_classes,←sum_filter]
  exact sum_subset (fun x hx => (mem_filter.mp hx).2) (fun x hx hn => supp x hx (fun h => hn (mem_filter.mpr ⟨h,hx⟩)))

namespace Classes
variable {I : Type*} [Fintype I] [LinearOrder I] {G : SimpleGraph V} [DecidableRel G.Adj]
  {D r K : ℕ} {ω ρ δ : ℝ} (d : Classes G D r K ω ρ δ I)
public theorem block_support (i : I) (x y : V) (h : x ∉ d.good i ∨ y ∉ d.good i) : d.block i x y = 0 := by
  have hn : ¬d.ordinary i x y := fun h' => h.elim (fun h => h h'.1) (fun h => h h'.2.1)
  simp [block,hn]

public theorem regular_cut (i : I) (X Y : Finset V) (hρ : 0 < ρ) (hδ : 0 < δ) :
    |∑ x ∈ X, ∑ y ∈ Y, d.block i x y| ≤ ρ*((d.piece i).card:ℝ)^2/δ := by
  classical
  let R := d.partition i
  let good := d.good i
  let sub (Z A : Finset V) := (Z ∩ A) ∩ good
  let val (A B : Finset V) := ∑ x ∈ X ∩ A, ∑ y ∈ Y ∩ B, d.block i x y
  have part_sum : (∑ A ∈ R.parts, ∑ B ∈ R.parts, val A B) = ∑ x ∈ X, ∑ y ∈ Y, d.block i x y := by
    have inner (A : Finset V) : (∑ B ∈ R.parts, val A B) = ∑ x ∈ X ∩ A, ∑ y ∈ Y, d.block i x y := by
      unfold val
      rw [sum_comm]
      exact sum_congr rfl (fun x _ => sum_parts_inter R Y _ (fun y _ hy => d.block_support i x y (Or.inr (fun h => hy (d.good_subset i h)))))
    simp_rw [inner]
    exact sum_parts_inter R X _ (fun x _ hx => sum_eq_zero fun y _ => d.block_support i x y (Or.inl (fun h => hx (d.good_subset i h))))
  have localBound A (ha : A ∈ R.parts) B (hb : B ∈ R.parts) : |val A B| ≤ ρ*((A.card:ℝ)*B.card)/δ := by
    have trim : val A B = ∑ x ∈ sub X A, ∑ y ∈ sub Y B, d.block i x y := by
      apply Eq.trans (sum_subset (s₁ := sub X A) inter_subset_left (fun x hx hn => sum_eq_zero fun y _ =>
        d.block_support i x y (Or.inl fun h => hn (mem_inter.mpr ⟨hx,h⟩)))).symm
      exact sum_congr rfl (fun x _ => (sum_subset (s₁ := sub Y B) inter_subset_left (fun y hy hn =>
        d.block_support i x y (Or.inr fun h => hn (mem_inter.mpr ⟨hy,h⟩)))).symm)
    rw [trim]
    have cls {Z A : Finset V} (hA : A ∈ R.parts) {x} (hx : x ∈ sub Z A) : d.part i x = A :=
      R.part_eq_of_mem hA (mem_inter.mp (mem_inter.mp hx).1).2
    by_cases hab : d.low i A B
    · have eq (x) (hx : x ∈ sub X A) (y) (hy : y ∈ sub Y B) :
          d.block i x y = centeredEntry G (crossDensity G A B) x y := by
        simp [block,ordinary,cls ha hx,cls hb hy,hab,show x ∈ d.good i from (mem_inter.mp hx).2,show y ∈ d.good i from (mem_inter.mp hy).2]
      rw [sum_congr rfl (fun x hx => sum_congr rfl (fun y hy => eq x hx y hy))]
      exact regular_pair_rectangle G A B ρ δ hρ hδ hab.2
        (fun X hX Y hY h₁ h₂ => le_of_not_gt fun h => hab.1.2 ⟨X,hX,Y,hY,h₁,h₂,h⟩)
        _ (inter_subset_left.trans inter_subset_right) _ (inter_subset_left.trans inter_subset_right)
    · have eq (x) (hx : x ∈ sub X A) (y) (hy : y ∈ sub Y B) : d.block i x y = 0 := by
        simp [block,ordinary,cls ha hx,cls hb hy,hab]
      rw [sum_eq_zero (fun x hx => sum_eq_zero fun y hy => eq x hx y hy),abs_zero]
      positivity
  rw [←part_sum]
  apply (abs_sum_le_sum_abs ..).trans
  apply (sum_le_sum (fun A ha => (abs_sum_le_sum_abs ..).trans (sum_le_sum (fun B hb => localBound A ha B hb)))).trans_eq
  have area : (∑ A ∈ R.parts, (A.card:ℝ)) = (d.piece i).card := by exact_mod_cast R.sum_card_parts
  simp only [←sum_div,←mul_sum,←sum_mul,area]
  ring
end Classes
end Vu.Revised

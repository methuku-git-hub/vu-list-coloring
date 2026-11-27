module
public import Vu.RevisedBlockCut
namespace Vu.Revised.Classes
open Finset
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
  {G : SimpleGraph V} [DecidableRel G.Adj] {D r K : ℕ} {ω ρ δ : ℝ} (d : Classes G D r K ω ρ δ I)
@[expose] public noncomputable def extra (i : I) (x y : V) : ℝ := by
  classical exact if d.first i x y ∧ G.Adj x y ∧ ¬d.ordinary i x y ∧ ¬d.dense i x y then -1 else 0
public theorem extra_cases (i : I) (x y : V) (he : d.extra i x y ≠ 0) :
    d.first i x y ∧ (x ∉ d.good i ∨ y ∉ d.good i ∨ irregularPair G ρ (d.part i x) (d.part i y)) := by
  classical
  unfold extra at he
  split at he
  next h =>
    refine ⟨h.1,?_⟩
    by_contra! hn
    have hreg : d.regular i (d.part i x) (d.part i y) := ⟨d.first_eligible h.1,hn.2.2⟩
    rcases lt_or_ge (crossDensity G (d.part i x) (d.part i y)) (1-δ) with hl|hh
    · exact h.2.2.1 ⟨hn.1,hn.2.1,hreg,hl⟩
    · exact h.2.2.2 ⟨hn.1,hn.2.1,hreg,hh⟩
  next => exact False.elim (he rfl)
public theorem irregular_pairs_mass (i : I) :
    (by classical exact ∑ x ∈ d.piece i, ∑ y ∈ d.piece i, if irregularPair G ρ (d.part i x) (d.part i y) then (1:ℝ) else 0) ≤ ρ*((d.piece i).card:ℝ)^2 := by
  classical
  let R := d.partition i
  let f (x y : V) : ℝ := if irregularPair G ρ (d.part i x) (d.part i y) then 1 else 0
  change ∑ x ∈ d.piece i, ∑ y ∈ d.piece i, f x y ≤ _
  apply le_trans _ (d.irregular i)
  apply le_of_eq
  rw [←sum_partition_classes R (fun x => ∑ y ∈ d.piece i, f x y),sum_filter,sum_product]
  apply sum_congr rfl
  intro A ha
  simp_rw [←sum_partition_classes R (fun y => f _ y)]
  rw [sum_comm]
  apply sum_congr rfl
  intro B hb
  have eq x (hx : x ∈ A) y (hy : y ∈ B) : f x y = if irregularPair G ρ A B then 1 else 0 := by
    simp only [f,part,R.part_eq_of_mem ha hx,R.part_eq_of_mem hb hy,R]
  rw [sum_congr rfl (fun x hx => sum_congr rfl fun y hy => eq x hx y hy)]
  split <;> simp

public theorem extra_cut (i : I) (X Y : Finset V) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) :
    |∑ x ∈ X, ∑ y ∈ Y, d.extra i x y| ≤ (ρ+2*√ρ)*((d.piece i).card:ℝ)^2 := by
  classical
  let P := d.piece i
  let bad := P \ d.good i
  let ind (x : V) : ℝ := if x ∈ bad then 1 else 0
  let irr (x y : V) : ℝ := if irregularPair G ρ (d.part i x) (d.part i y) then 1 else 0
  have trim : (∑ x ∈ X, ∑ y ∈ Y, d.extra i x y) = ∑ x ∈ X ∩ P, ∑ y ∈ Y ∩ P, d.extra i x y := by
    have out x y (ho : x ∉ P ∨ y ∉ P) : d.extra i x y = 0 := by
      by_contra he
      have h := (mem_filter.mp (d.extra_cases i x y he).1.1).2
      exact ho.elim (fun hn => hn h.1) (fun hn => hn h.2)
    rw [←sum_subset (s₁ := X ∩ P) inter_subset_left (fun x hx hn => sum_eq_zero fun y _ => out x y (Or.inl fun h => hn (mem_inter.mpr ⟨hx,h⟩)))]
    exact sum_congr rfl (fun x _ => (sum_subset (s₁ := Y ∩ P) inter_subset_left (fun y hy hn =>
      out x y (Or.inr fun h => hn (mem_inter.mpr ⟨hy,h⟩)))).symm)
  rw [trim]
  apply (abs_sum_le_sum_abs ..).trans
  apply (sum_le_sum (fun x _ => abs_sum_le_sum_abs (fun y => d.extra i x y) (Y ∩ P))).trans
  have bound x (hx : x ∈ P) y (hy : y ∈ P) : |d.extra i x y| ≤ ind x+ind y+irr x y := by
    have h₁ : |d.extra i x y| ≤ 1 := by unfold extra; split <;> norm_num
    by_cases he : d.extra i x y = 0
    · simp only [he,abs_zero,ind,irr]; split <;> split <;> split <;> norm_num
    apply h₁.trans
    rcases (d.extra_cases i x y he).2 with hn|hn|hir
    · have hh : x ∈ bad := mem_sdiff.mpr ⟨hx,hn⟩
      simp only [ind,if_pos hh,irr]; split <;> split <;> norm_num
    · have hh : y ∈ bad := mem_sdiff.mpr ⟨hy,hn⟩
      simp only [ind,if_pos hh,irr]; split <;> split <;> norm_num
    · simp only [ind,irr,if_pos hir]; split <;> split <;> norm_num
  have nn x y : 0 ≤ ind x+ind y+irr x y := by dsimp [ind,irr]; split <;> split <;> split <;> norm_num
  apply (sum_le_sum (fun x hx => (sum_le_sum (fun y hy => bound x (mem_inter.mp hx).2 y (mem_inter.mp hy).2)).trans
      (sum_le_sum_of_subset_of_nonneg inter_subset_right (fun y _ _ => nn x y)))).trans
  apply (sum_le_sum_of_subset_of_nonneg inter_subset_right (fun x _ _ => sum_nonneg (fun y _ => nn x y))).trans
  have hi : ∑ x ∈ P, ind x = bad.card := by simp [ind,←sum_filter,filter_mem_eq_inter,inter_eq_right.mpr (show bad ⊆ P from sdiff_subset)]
  have hbad := nongood_vertices_bound G P (d.partition i) ρ hρ hρ₁
  change (bad.card:ℝ) ≤ √ρ*P.card at hbad
  have hirr := d.irregular_pairs_mass i
  change (∑ x ∈ P, ∑ y ∈ P, irr x y) ≤ ρ*(P.card:ℝ)^2 at hirr
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,hi,←mul_sum]
  change _ ≤ (ρ+2*√ρ)*(P.card:ℝ)^2
  nlinarith only [mul_le_mul_of_nonneg_right hbad (Nat.cast_nonneg P.card),hirr]
end Vu.Revised.Classes

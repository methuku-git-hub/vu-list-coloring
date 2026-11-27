module
public import Vu.PartitionMatrix
public import Vu.RowNorm
namespace Vu
open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The local Frobenius estimate with both sides restricted to the supporting
piece, in the form needed to sum overlapping errors. -/
public theorem piece_frobenius (P : Finset V) (M : V → V → ℝ) (A : ℝ)
    (hs : ∀ x y, x ∉ P ∨ y ∉ P → M x y = 0)
    (hF : (∑ x ∈ P, ∑ y ∈ P, M x y^2) ≤ A) (f : V → ℝ) :
    (∑ x, (∑ y, M x y*f y)^2) ≤ A*∑ y ∈ P, f y^2 := by
  classical
  have row (x : V) : (∑ y, M x y*f y) = ∑ y ∈ P, M x y*f y :=
    (sum_subset (subset_univ _) (fun y _ hy => by simp [hs x y (Or.inr hy)])).symm
  rw [← sum_subset (subset_univ P) (fun x _ hx => by simp [hs x _ (Or.inl hx)])]
  simp_rw [row]
  apply (sum_le_sum (fun x (_ : x ∈ P) => sum_mul_sq_le_sq_mul_sq P (M x) f)).trans
  rw [← sum_mul]
  exact mul_le_mul_of_nonneg_right hF (sum_nonneg fun _ _ => sq_nonneg _)

/-- Frobenius mass of arbitrary marked entries supported on distinct
irregular class rectangles. The threshold uses ordered class pairs. -/
public theorem irregular_edge_frobenius (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) (R : Finpartition P) (ρ : ℝ) (M : V → V → ℝ)
    (habs : ∀ x y, |M x y| ≤ 1)
    (hs : ∀ x ∈ P, ∀ y ∈ P, M x y ≠ 0 → R.part x ≠ R.part y ∧ irregularPair G ρ (R.part x) (R.part y)) :
    (∑ x ∈ P, ∑ y ∈ P, M x y^2) ≤ (by classical exact ∑ e ∈ (R.parts ×ˢ R.parts).filter (fun e => e.1 ≠ e.2 ∧ irregularPair G ρ e.1 e.2), (e.1.card : ℝ)*e.2.card) := by
  classical
  let bad (A B : Finset V) := A ≠ B ∧ irregularPair G ρ A B
  have block (A B : Finset V) (ha : A ∈ R.parts) (hb : B ∈ R.parts) :
      (∑ x ∈ A, ∑ y ∈ B, M x y^2) ≤ (if bad A B then (A.card : ℝ)*B.card else 0) := by
    by_cases he : bad A B
    · rw [if_pos he]
      calc
        _ ≤ ∑ _x ∈ A, ∑ _y ∈ B, (1:ℝ) :=
          sum_le_sum (fun x _ => sum_le_sum (fun y _ => by simpa using (sq_le_sq.mpr (by simpa using habs x y : |M x y| ≤ |(1:ℝ)|))))
        _ = _ := by simp
    · rw [if_neg he]
      have hz (x : V) (hx : x ∈ A) (y : V) (hy : y ∈ B) : M x y = 0 := by
        by_contra hn
        apply he
        simpa [bad,R.part_eq_of_mem ha hx,R.part_eq_of_mem hb hy] using hs x (R.le ha hx) y (R.le hb hy) hn
      exact le_of_eq (sum_eq_zero (fun x hx => sum_eq_zero (fun y hy => by simp [hz x hx y hy])))
  rw [← sum_partition_classes R (fun x => ∑ y ∈ P, M x y^2)]
  simp_rw [← sum_partition_classes R (fun y => M _ y^2)]
  calc
    _ = ∑ A ∈ R.parts, ∑ B ∈ R.parts, ∑ x ∈ A, ∑ y ∈ B, M x y^2 := by
      apply sum_congr rfl; intro A _; rw [sum_comm]
    _ ≤ ∑ A ∈ R.parts, ∑ B ∈ R.parts, if bad A B then (A.card : ℝ)*B.card else 0 :=
      sum_le_sum (fun A ha => sum_le_sum (fun B hb => block A B ha hb))
    _ = _ := by rw [sum_filter,sum_product]

/-- Entries of magnitude at most one touching nongood vertices use at most
2 |bad| |P| of squared Frobenius mass, even if both endpoints are bad. -/
public theorem bad_vertex_frobenius (P bad : Finset V) (hb : bad ⊆ P) (M : V → V → ℝ)
    (habs : ∀ x y, |M x y| ≤ 1)
    (hs : ∀ x ∈ P, ∀ y ∈ P, M x y ≠ 0 → x ∈ bad ∨ y ∈ bad) :
    ∑ x ∈ P, ∑ y ∈ P, M x y^2 ≤ 2*(bad.card : ℝ)*P.card := by
  classical
  let ind (x : V) : ℝ := if x ∈ bad then 1 else 0
  have hi : ∑ x ∈ P, ind x = bad.card := by
    simp [ind,←sum_filter,filter_mem_eq_inter,inter_eq_right.mpr hb]
  have point (x : V) (hx : x ∈ P) (y : V) (hy : y ∈ P) : M x y^2 ≤ ind x + ind y := by
    have hone : M x y^2 ≤ 1 := by simpa using (sq_le_sq.mpr (by simpa using habs x y : |M x y| ≤ |(1:ℝ)|))
    by_cases h : M x y = 0
    · simp only [h,zero_pow (by decide : 2 ≠ 0),ind]; split <;> split <;> norm_num
    · rcases hs x hx y hy h with a | b
      · simp only [ind,if_pos a]; split <;> linarith
      · simp only [ind,if_pos b]; split <;> linarith
  apply (sum_le_sum (fun x hx => sum_le_sum (fun y hy => point x hx y hy))).trans_eq
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,hi,←mul_sum]

  ring
/-- Turn a global operator bound into a local one for a matrix whose
nonzero columns belong to P. -/
public theorem localize_norm (P : Finset V) (M : V → V → ℝ) (a : ℝ) (hM : RowNormLE M univ a)
    (hs : ∀ x y, y ∉ P → M x y = 0) (f : V → ℝ) :
    (∑ x, (∑ y, M x y*f y)^2) ≤ a^2*∑ y ∈ P, f y^2 := by
  classical
  let g (y : V) := if y ∈ P then f y else 0
  have hrow (x y : V) : M x y*g y = M x y*f y := by by_cases h : y ∈ P <;> simp [g,h,hs]
  have hsum : ∑ y, g y^2 = ∑ y ∈ P, f y^2 := by simp [g,ite_pow,←sum_filter]
  simpa only [hrow,hsum] using hM g

/-- A masked matrix of entries of size at most one, supported within
individual classes, has norm at most the maximum class size. -/
public theorem same_class_norm (P : Finset V) (R : Finpartition P) (M : V → V → ℝ) (L : ℝ)
    (hL : 0 ≤ L) (hsize : ∀ A ∈ R.parts, (A.card:ℝ) ≤ L)
    (habs : ∀ x y, |M x y| ≤ 1) (hs : ∀ x y, M x y ≠ 0 → x ∈ P ∧ y ∈ P ∧ R.part x = R.part y) :
    RowNormLE M univ L := by
  classical
  have hsum (g : V → ℝ) (x : V) (hm : ∀ y, g y ≠ 0 → x ∈ P ∧ y ∈ P ∧ R.part x = R.part y)
      (hb : ∀ y, |g y| ≤ 1) : ∑ y, |g y| ≤ L := by
    by_cases hx : x ∈ P
    · have hy (y : V) (h : y ∉ R.part x) : g y = 0 := by
        by_contra hn
        obtain ⟨_,hy,he⟩ := hm y hn
        exact h (he ▸ R.mem_part hy)
      rw [← sum_subset (subset_univ (R.part x)) (fun y _ h => by simp [hy y h])]
      exact (sum_le_sum (fun y _ => hb y)).trans (by simpa using hsize _ (R.part_mem.mpr hx))
    · have hz (y : V) : g y = 0 := by by_contra hn; exact hx (hm y hn).1
      simpa [hz] using hL
  exact row_norm_of_sums L hL univ (fun x _ => hsum (M x) x (hs x) (habs x))
    (fun y => hsum (fun x => M x y) y (fun x hn =>
      ⟨(hs x y hn).2.1,(hs x y hn).1,(hs x y hn).2.2.symm⟩) (fun x => habs x y))

/-- Fourth-root bounds for the irregular-area and nongood-vertex terms. -/
public theorem fourth_root_errors (ρ : ℝ) (hρ : 0 ≤ ρ) (hr : ρ ≤ 1) :
    let t := ρ^(1/4:ℝ)
    ρ ≤ t^2 ∧ 2*(ρ+√ρ) ≤ (2*t)^2 := by
  intro t
  have he : t^2 = √ρ := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_natCast,← Real.rpow_mul hρ]
    norm_num
  have hs : ρ ≤ √ρ := by
    nlinarith [Real.sq_sqrt hρ,Real.sqrt_le_one.mpr hr,Real.sqrt_nonneg ρ,
      mul_nonneg (Real.sqrt_nonneg ρ) (sub_nonneg.mpr (Real.sqrt_le_one.mpr hr))]
  exact ⟨he ▸ hs,by nlinarith [he]⟩
end Vu

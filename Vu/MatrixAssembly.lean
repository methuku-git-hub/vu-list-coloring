module

public import Vu.OmittedNeighbors

namespace Vu
open Finset

/-- The overlap estimate in Lemma 4.6. The pieces may have different
supports of any sizes, and at most r of them contain each vertex. -/
public theorem sum_piece_matrix_bound {V I : Type*} [Fintype V] [Fintype I] [DecidableEq V]
    (P : I → Finset V) (M : I → V → V → ℝ) (r : ℕ) (K : ℝ)
    (hcount : ∀ v, (univ.filter fun i => v ∈ P i).card ≤ r)
    (hrow : ∀ i x y, x ∉ P i → M i x y = 0)
    (hlocal : ∀ i (f : V → ℝ), ∑ x, (∑ y, M i x y * f y)^2 ≤ K^2 * ∑ y ∈ P i, f y^2)
    (T : Finset V) : RowNormLE (fun x y => ∑ i, M i x y) T (r*K) := by
  classical
  intro f
  let g i x := ∑ y, M i x y * f y
  let incident x := univ.filter fun i => x ∈ P i
  have row (x : V) : (∑ y, (∑ i, M i x y)*f y)^2 ≤ (r : ℝ) * ∑ i, g i x^2 := by
    have eq : (∑ y, (∑ i, M i x y)*f y) = ∑ i ∈ incident x, g i x := by
      simp_rw [sum_mul]
      rw [sum_comm]
      apply (sum_subset (s₁ := incident x) (subset_univ _) ?_).symm
      intro i _ hi
      have : x ∉ P i := fun h => hi (mem_filter.mpr ⟨mem_univ _, h⟩)
      simp [hrow i x _ this]
    rw [eq]
    have hh := sum_mul_sq_le_sq_mul_sq (incident x) (fun _ => (1 : ℝ)) (fun i => g i x)
    simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] at hh
    exact hh.trans (mul_le_mul (Nat.cast_le.mpr (hcount x))
      (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _))
      (sum_nonneg (fun _ _ => sq_nonneg _)) (Nat.cast_nonneg _))
  have overlap : (∑ i, ∑ y ∈ P i, f y^2) ≤ (r : ℝ) * ∑ y, f y^2 := by
    have eq (i : I) : (∑ y ∈ P i, f y^2) = ∑ y, if y ∈ P i then f y^2 else 0 := by simp
    simp_rw [eq]
    rw [sum_comm, mul_sum]
    apply sum_le_sum
    intro y _
    simpa [← sum_filter] using mul_le_mul_of_nonneg_right (Nat.cast_le (α := ℝ) |>.mpr (hcount y)) (sq_nonneg (f y))
  have hmat : (∑ x, ∑ i, g i x^2) ≤ K^2 * ((r : ℝ) * ∑ y, f y^2) := by
    rw [sum_comm]
    apply (sum_le_sum (fun i _ => hlocal i f)).trans
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left overlap (sq_nonneg _)
  calc
    _ ≤ ∑ x ∈ T, (r : ℝ)*∑ i, g i x^2 := sum_le_sum (fun x _ => row x)
    _ ≤ ∑ x : V, (r : ℝ)*∑ i, g i x^2 :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => mul_nonneg (Nat.cast_nonneg _) (sum_nonneg fun _ _ => sq_nonneg _))
    _ ≤ _ := by
      rw [← mul_sum]
      exact (mul_le_mul_of_nonneg_left hmat (Nat.cast_nonneg r)).trans_eq (by ring)

/-- The Frobenius estimate for exceptional vertices and irregular pairs
in Lemma 4.6. Deleting any subset of the permitted entries preserves it. -/
public theorem sparse_matrix_bound {V : Type*} [Fintype V] [DecidableEq V]
    (T : Finset V) (S : V → Finset V) (M : V → V → ℝ) (N : ℕ)
    (hentries : ∀ x ∈ T, ∀ y, |M x y| ≤ 1)
    (hsupp : ∀ x ∈ T, ∀ y ∉ S x, M x y = 0)
    (hcount : ∑ x ∈ T, (S x).card ≤ N) : RowNormLE M T √(N : ℝ) := by
  intro f
  have row (x : V) (hx : x ∈ T) : (∑ y, M x y * f y)^2 ≤
      ((S x).card : ℝ) * ∑ y, f y^2 := by
    apply (sum_mul_sq_le_sq_mul_sq univ (M x) f).trans
    apply mul_le_mul_of_nonneg_right _ (sum_nonneg fun _ _ => sq_nonneg _)
    calc
      _ = ∑ y ∈ S x, M x y ^ 2 := (sum_subset (subset_univ _) (fun y _ hy => by simp [hsupp x hx y hy])).symm
      _ ≤ ∑ _y ∈ S x, (1 : ℝ) := by
        apply sum_le_sum
        intro y _
        simpa using (sq_le_sq.mpr ((hentries x hx y).trans_eq (abs_one : |(1 : ℝ)| = 1).symm))
      _ = _ := by simp
  apply (sum_le_sum row).trans
  rw [← sum_mul, Real.sq_sqrt (Nat.cast_nonneg _)]
  apply mul_le_mul_of_nonneg_right _ (sum_nonneg fun _ _ => sq_nonneg _)
  exact_mod_cast hcount

end Vu

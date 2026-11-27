module
public import Vu.MatrixAssembly
namespace Vu
open Finset
variable {V : Type*} [Fintype V]

public theorem row_norm_mono {M : V → V → ℝ} {T : Finset V} {a b : ℝ}
    (h : RowNormLE M T a) (ha : 0 ≤ a) (hab : a ≤ b) : RowNormLE M T b := by
  intro f
  exact (h f).trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha hab 2) (sum_nonneg fun _ _ => sq_nonneg _))

/-- Triangle inequality in the exact restricted-row formulation of (D3). -/
public theorem row_norm_add {M N : V → V → ℝ} {T : Finset V} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hm : RowNormLE M T a) (hn : RowNormLE N T b) :
    RowNormLE (fun x y => M x y + N x y) T (a+b) := by
  intro f
  let m x := ∑ y, M x y*f y
  let n x := ∑ y, N x y*f y
  let F := ∑ y, f y^2
  have hf : 0 ≤ F := sum_nonneg (fun _ _ => sq_nonneg _)
  have hm' : ∑ x ∈ T, m x^2 ≤ a^2*F := hm f
  have hn' : ∑ x ∈ T, n x^2 ≤ b^2*F := hn f
  have hcross := Real.sum_mul_le_sqrt_mul_sqrt T m n
  have hh := mul_le_mul (Real.sqrt_le_sqrt hm') (Real.sqrt_le_sqrt hn') (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [Real.sqrt_mul (sq_nonneg a),Real.sqrt_mul (sq_nonneg b),Real.sqrt_sq ha,Real.sqrt_sq hb] at hh
  have hmn : (∑ x ∈ T, m x*n x) ≤ a*b*F := by
    apply (hcross.trans hh).trans_eq
    calc
      _ = a*b*(√F)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt hf]
  simp only [add_mul,sum_add_distrib]
  change (∑ x ∈ T, (m x+n x)^2) ≤ (a+b)^2*F
  simp only [add_sq,sum_add_distrib,show ∀ x, 2*m x*n x = 2*(m x*n x) from fun _ => by ring,← mul_sum]
  linarith only [hm',hn',hmn]

/-- Absolute row and column sums bound the operator norm uniformly on any
row set. This also applies after changing signs or deleting entries. -/
public theorem row_norm_of_sums {M : V → V → ℝ} (L : ℝ) (hL : 0 ≤ L) (T : Finset V)
    (hrow : ∀ x ∈ T, ∑ y, |M x y| ≤ L) (hcol : ∀ y, ∑ x ∈ T, |M x y| ≤ L) : RowNormLE M T L := by
  intro f
  have row (x : V) (hx : x ∈ T) : (∑ y, M x y*f y)^2 ≤ L*∑ y, |M x y| * f y^2 := by
    have hh := sum_mul_sq_le_sq_mul_sq univ (fun y => √|M x y|) (fun y => √|M x y| *|f y|)
    simp only [mul_pow,Real.sq_sqrt (abs_nonneg _),sq_abs] at hh
    have heq (y : V) : √|M x y| *(√|M x y| *|f y|) = |M x y*f y| := by
      rw [← mul_assoc,Real.mul_self_sqrt (abs_nonneg _),abs_mul]
    simp_rw [heq] at hh
    apply (sq_le_sq.mpr ?_).trans (hh.trans (mul_le_mul_of_nonneg_right (hrow x hx)
      (sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))))
    rw [abs_of_nonneg (sum_nonneg (s := univ) (fun y _ => abs_nonneg (M x y*f y)))]
    exact abs_sum_le_sum_abs _ _
  apply (sum_le_sum row).trans
  rw [← mul_sum,sum_comm]
  calc
    _ = L*∑ y, (∑ x ∈ T, |M x y|) * f y^2 := by simp only [sum_mul]
    _ ≤ L*∑ y, L*f y^2 := mul_le_mul_of_nonneg_left
      (sum_le_sum fun y _ => mul_le_mul_of_nonneg_right (hcol y) (sq_nonneg _)) hL
    _ = _ := by rw [← mul_sum]; ring

public theorem row_norm_neg {M : V → V → ℝ} {T : Finset V} {a : ℝ} (h : RowNormLE M T a) :
    RowNormLE (fun x y => -(M x y)) T a := by
  intro f
  simpa only [neg_mul,sum_neg_distrib,neg_sq] using h f

public theorem row_norm_diagonal [DecidableEq V] (T : Finset V) :
    RowNormLE (fun x y : V => if x = y then -1 else 0) T 1 := by
  apply row_norm_of_sums _ zero_le_one
  · intro x _
    simp [apply_ite abs] <;> split <;> norm_num
  · intro y
    simp [apply_ite abs] <;> split <;> norm_num
end Vu

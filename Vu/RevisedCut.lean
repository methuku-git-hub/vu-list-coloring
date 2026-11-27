module
public import Vu.Decomposition
namespace Vu.Revised
open Finset
variable {V : Type*} [Fintype V]

/-- Restrict a squared Euclidean estimate to two indicator vectors. -/
public theorem rectangle_of_rows (M : V → V → ℝ) (T U Y : Finset V) (D : ℕ) (K : ℝ)
    (hK : 0 ≤ K) (hT : T.card ≤ D) (hU : U ⊆ T) (hY : Y.card ≤ D)
    (hn : RowNormLE M T K) : |∑ x ∈ U, ∑ y ∈ Y, M x y| ≤ K*D := by
  classical
  let f (x : V) := ∑ y ∈ Y, M x y
  have hc := sum_mul_sq_le_sq_mul_sq U (fun _ => (1:ℝ)) f
  have hcs : (∑ x ∈ U, f x)^2 ≤ U.card * ∑ x ∈ U, (f x)^2 := by simpa using hc
  have ht : (∑ x ∈ T, (f x)^2) ≤ K^2*Y.card := by
    have h := hn (fun y => if y ∈ Y then 1 else 0)
    simpa [f,mul_ite,←sum_filter,ite_pow] using h
  have hu : (U.card:ℝ) ≤ D := by exact_mod_cast (card_le_card hU).trans hT
  have hy : (Y.card:ℝ) ≤ D := by exact_mod_cast hY
  have hsub := sum_le_sum_of_subset_of_nonneg hU (fun x _ _ => sq_nonneg (f x))
  have hall := hcs.trans (mul_le_mul hu (hsub.trans (ht.trans (mul_le_mul_of_nonneg_left hy (sq_nonneg K))))
      (sum_nonneg (fun _ _ => sq_nonneg _)) (Nat.cast_nonneg _))
  change |∑ x ∈ U, f x| ≤ _
  have heq : (D:ℝ)*(K^2*D) = (K*D)^2 := by ring
  rw [heq,←sq_abs] at hall
  exact le_of_pow_le_pow_left₀ (by decide : 2 ≠ 0) (by positivity) hall
end Vu.Revised

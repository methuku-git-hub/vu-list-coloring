module
public import Vu.PairMatrix
public import Vu.RevisedPartitions
namespace Vu.Revised
open Finset
variable {V I : Type*} [Fintype I] [DecidableEq V]

/-- Add local cancellation bounds using the incidence multiplicity on both sides. -/
public theorem sum_piece_rectangles (P : I → Finset V) (X Y : Finset V) (D r : ℕ)
    (c B : ℝ) (hc : 0 ≤ c) (hB : 0 ≤ B) (s : I → ℝ)
    (hX : X.card ≤ D) (hY : Y.card ≤ D) (hp : ∀ i, (P i).card ≤ 2*D)
    (hm : ∀ x, (univ.filter fun i => x ∈ P i).card ≤ r)
    (hlocal : ∀ i, |s i| ≤ c*((P i).card:ℝ)^2)
    (hentry : ∀ i, |s i| ≤ B*((X ∩ P i).card:ℝ)*(Y ∩ P i).card) :
    ∑ i, |s i| ≤ 2*r*D^2*√(c*B) := by
  classical
  let n (S : Finset V) (i : I) : ℝ := (S ∩ P i).card
  have count (S : Finset V) (hS : S.card ≤ D) : ∑ i, n S i ≤ (r:ℝ)*D := by
    have eq (i : I) : n S i = ∑ x ∈ S, if x ∈ P i then (1:ℝ) else 0 := by simp [n]
    simp_rw [eq]
    rw [sum_comm]
    have bound (x : V) : (∑ i, if x ∈ P i then (1:ℝ) else 0) ≤ r := by simpa [←sum_filter] using Nat.cast_le (α := ℝ) |>.mpr (hm x)
    apply (sum_le_sum (fun x (_ : x ∈ S) => bound x)).trans
    simpa [mul_comm] using mul_le_mul_of_nonneg_right (Nat.cast_le (α := ℝ) |>.mpr hS) (Nat.cast_nonneg r)
  have cs := Real.sum_sqrt_mul_sqrt_le (f := n X) (g := n Y) univ (fun i => Nat.cast_nonneg _) (fun i => Nat.cast_nonneg _)
  have conc : ∑ i, √(n X i)*√(n Y i) ≤ (r:ℝ)*D := by
    apply cs.trans
    apply (mul_le_mul (Real.sqrt_le_sqrt (count X hX)) (Real.sqrt_le_sqrt (count Y hY)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).trans_eq
    exact Real.mul_self_sqrt (by positivity)
  have loc (i : I) : |s i| ≤ 2*D*√(c*B)*(√(n X i)*√(n Y i)) := by
    have h := mul_le_mul (hlocal i) (hentry i) (abs_nonneg _) (mul_nonneg hc (sq_nonneg _))
    have hx : 0 ≤ n X i := Nat.cast_nonneg _
    have hy : 0 ≤ n Y i := Nat.cast_nonneg _
    have hs : |s i| ≤ (P i).card*√(c*B)*(√(n X i)*√(n Y i)) := by
      apply le_of_pow_le_pow_left₀ (by decide : 2 ≠ 0) (by positivity)
      simp only [mul_pow,Real.sq_sqrt hx,Real.sq_sqrt hy,Real.sq_sqrt (mul_nonneg hc hB)]
      dsimp only [n]
      nlinarith only [h]
    apply hs.trans
    gcongr
    exact_mod_cast hp i
  apply (sum_le_sum fun i _ => loc i).trans
  rw [←mul_sum]
  exact (mul_le_mul_of_nonneg_left conc (by positivity)).trans_eq (by ring)
end Vu.Revised

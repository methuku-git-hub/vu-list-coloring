module
public import Vu.RegularRows
namespace Vu.Revised
open Finset
variable {I J : Type*} [Fintype J] [DecidableEq J]

private theorem greatest_entries (q : J → ℝ) (n : ℕ) (hn : n ≤ Fintype.card J) :
    ∃ S : Finset J, S.card=n ∧ ∀ j ∉ S, ∀ i ∈ S, q j ≤ q i := by
  classical
  induction n with
  | zero => exact ⟨∅,rfl,by simp⟩
  | succ n ih =>
    obtain ⟨S,hS,hs⟩ := ih (by omega)
    have hex : (univ \ S).Nonempty := by
      apply card_pos.mp
      rw [card_sdiff,inter_univ,card_univ,hS]; omega
    obtain ⟨z,hz,hbest⟩ := exists_max_image (univ \ S) q hex
    refine ⟨insert z S,by simp [(mem_sdiff.mp hz).2,hS],?_⟩
    intro j hj i hi
    have hj' : j ≠ z ∧ j ∉ S := by simpa only [mem_insert,not_or] using hj
    rcases mem_insert.mp hi with rfl|hi
    · exact hbest j (mem_sdiff.mpr ⟨mem_univ _,hj'.2⟩)
    · exact hs j hj'.2 i hi

/-- Extremizing a bounded fractional sum with a fixed total budget
requires at most D columns. -/
private theorem bounded_columns (q w : J → ℝ) (D : ℕ) (A B : ℝ) (hD : 0 < D) (hA : 0 ≤ A)
    (hq : ∀ j, 0 ≤ q j) (hw : ∀ j, 0 ≤ w j ∧ w j ≤ A)
    (hmass : ∑ j, w j ≤ A*D) (hcut : ∀ S : Finset J, S.card ≤ D → ∑ j ∈ S, q j ≤ B) :
    (∑ j, q j*w j) ≤ A*B := by
  classical
  by_cases hcard : Fintype.card J ≤ D
  · apply (sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hw j).2 (hq j))).trans
    rw [←sum_mul,mul_comm]
    exact mul_le_mul_of_nonneg_left (hcut _ (by simpa using hcard)) hA
  obtain ⟨S,hs,horder⟩ := greatest_entries q D (le_of_not_ge hcard)
  obtain ⟨z,hz,hmin⟩ := exists_min_image S q (card_pos.mp (hs.trans_gt hD))
  let m := q z
  have hpoint (j : J) : q j*w j ≤ m*w j+(if j ∈ S then A*(q j-m) else 0) := by
    by_cases hj : j ∈ S
    · simp only [if_pos hj]
      linarith only [mul_nonneg (sub_nonneg.mpr (hmin j hj)) (sub_nonneg.mpr (hw j).2)]
    · simp only [if_neg hj,add_zero]
      exact mul_le_mul_of_nonneg_right (horder j hj z hz) (hw j).1
  apply (sum_le_sum fun j _ => hpoint j).trans
  rw [sum_add_distrib,←mul_sum,←sum_filter]
  simp only [filter_mem_eq_inter,univ_inter,←mul_sum,sum_sub_distrib,sum_const,nsmul_eq_mul,hs]
  linarith only [mul_le_mul_of_nonneg_left hmass (hq z),mul_le_mul_of_nonneg_left (hcut S hs.le) hA]

/-- Lemma 3.1 of the revised manuscript. Both signs of the column
weights and both signs of the resulting row sums are allowed. -/
public theorem weighted_count (T : Finset I) (f : I → J → ℝ) (h : J → ℝ) (D : ℕ)
    (M η : ℝ) (hD : 0 < D) (hM : 0 ≤ M)
    (rect : ∀ U ⊆ T, ∀ Y : Finset J, Y.card ≤ D → |∑ i ∈ U, ∑ j ∈ Y, f i j| ≤ η*D^2)
    (hcap : ∀ j, |h j| ≤ M/D) (hmass : ∑ j, |h j| ≤ M) :
    (∑ i ∈ T, |∑ j, f i j*h j|) ≤ 4*M*η*D := by
  classical
  have hd : (0:ℝ) < D := Nat.cast_pos.mpr hD
  apply (sum_abs_le_twice_cut T _ (M/D*(2*(η*D^2))) ?_).trans_eq
  · field_simp <;> ring
  intro U hu
  let q j := ∑ i ∈ U, f i j
  have he : (∑ i ∈ U, ∑ j, f i j*h j) = ∑ j, q j*h j := by rw [sum_comm]; simp [q,sum_mul]
  rw [he]
  apply (abs_sum_le_sum_abs _ _).trans
  simp_rw [abs_mul]
  apply bounded_columns (fun j => |q j|) (fun j => |h j|) D (M/D) _ hD
    (div_nonneg hM hd.le) (fun _ => abs_nonneg _) (fun j => ⟨abs_nonneg _,hcap j⟩)
    (by simpa only [div_mul_cancel₀ M hd.ne'] using hmass)
  intro S hs
  apply sum_abs_le_twice_cut
  intro Y hy
  dsimp only [q]
  rw [sum_comm]
  exact rect U hu Y ((card_le_card hy).trans hs)
end Vu.Revised

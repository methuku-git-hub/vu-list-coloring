module
public import Vu.AssignedMatrix
public import Vu.RowNorm
namespace Vu
open Finset

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
  (G : SimpleGraph V) [DecidableRel G.Adj] (P : I → Finset V) (R : ∀ i, Finpartition (P i))

public theorem exceptional_pair_swap (z : ℝ) (x y : V) : exceptionalPair P z x y ↔ exceptionalPair P z y x := by
  have hj : jointPieces P x y = jointPieces P y x := by ext; simp [jointPieces,and_comm]
  simp only [exceptionalPair,hj]

/-- Size of each original centered entry, including on exceptional vertex pairs. -/
public theorem regular_piece_abs (K : ℕ) (z ρ δ : ℝ) (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (i : I) (x y : V) : |regularPieceMatrix G P R K z ρ δ i x y| ≤ 1/δ := by
  classical
  dsimp only [regularPieceMatrix]
  split
  next h =>
    let d := crossDensity G ((R i).part x) ((R i).part y)
    have hd : d < 1-δ := h.2.2.2.2.2
    have hpos : 0 ≤ d := div_nonneg (sum_nonneg fun _ _ => Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    have hd1 : 0 < 1-d := by linarith
    change |(d-(if G.Adj x y then 1 else 0))/(1-d)| ≤ 1/δ
    rw [abs_div,abs_of_pos hd1]
    apply (div_le_div_iff₀ hd1 hδ).mpr
    have hn : |d-(if G.Adj x y then 1 else 0)| ≤ 1 := by
      split <;> apply abs_le.mpr <;> constructor <;> linarith
    linarith [mul_le_mul_of_nonneg_right hn hδ.le]
  next => simp [hδ.le]

/-- Exceptional-vertex-pair correction in Lemma 4.6, with the exact
coefficient (r³/δ + r²)ωΔ from the manuscript. -/
public theorem exceptional_correction_norm (D r K : ℕ) (hr : 0 < r) (ω ρ δ : ℝ)
    (hω : 0 ≤ ω) (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hm : ∀ x, (univ.filter fun i => x ∈ P i).card ≤ r) (T : Finset V) :
    RowNormLE (exceptionalCorrection G P R K (ω*D) ρ δ) T (((r:ℝ)^3/δ+r^2)*ω*D) := by
  classical
  let E := exceptionalCorrection G P R K (ω*D) ρ δ
  let m := regularPieceMatrix G P R K (ω*D) ρ δ
  have hpoint (x y : V) : |E x y| ≤ (r:ℝ)/δ+1 := by
    have hab : (∑ i, |m i x y|) ≤ (r:ℝ)/δ := by
      let A := univ.filter fun i => x ∈ P i
      rw [← sum_subset (subset_univ A) (fun i _ hi => by
        have hx : x ∉ P i := fun h => hi (mem_filter.mpr ⟨mem_univ _,h⟩)
        simp [m,regular_piece_supported G P R K (ω*D) ρ δ i x y (Or.inl hx)])]
      apply (sum_le_sum (fun i (_ : i ∈ A) => regular_piece_abs G P R K (ω*D) ρ δ hδ hδ₁ i x y)).trans
      simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right (Nat.cast_le (α := ℝ) |>.mpr (hm x)) (inv_nonneg.mpr hδ.le)
    have he : |(if G.Adj x y then (-1:ℝ) else 0)| ≤ 1 := by split <;> norm_num
    dsimp only [E,exceptionalCorrection]
    split
    next =>
      have h := abs_sub_le (if G.Adj x y then (-1:ℝ) else 0) 0 (∑ i, m i x y)
      simp only [sub_zero,zero_sub,abs_neg] at h
      linarith [abs_sum_le_sum_abs (fun i => m i x y) univ]
    next => simp; positivity
  have hzero (x y : V) (hn : ¬ exceptionalPair P (ω*D) x y) : E x y = 0 := by simp [E,exceptionalCorrection,hn]
  have row (x : V) (g : V → ℝ) (hg : ∀ y, |g y| ≤ (r:ℝ)/δ+1)
      (hs : ∀ y, ¬exceptionalPair P (ω*D) x y → g y = 0) :
      ∑ y, |g y| ≤ ((r:ℝ)^3/δ+r^2)*ω*D := by
    obtain ⟨A,hA,hcard⟩ := exceptional_occurrence_budget P r D ω ((r:ℝ)^3*ω) hω le_rfl x (hm x)
    have hr' : 0 < (r:ℝ) := Nat.cast_pos.mpr hr
    have hsize : (A.card:ℝ) ≤ (r:ℝ)^2*ω*D := by
      apply (mul_le_mul_iff_of_pos_left hr').mp
      exact hcard.trans_eq (by ring)
    rw [← sum_subset (subset_univ A) (fun y _ hy => by simp [hs y (fun h => hy ((hA y).mpr h))])]
    apply (sum_le_sum (fun y (_ : y ∈ A) => hg y)).trans
    simp only [sum_const,nsmul_eq_mul]
    exact (mul_le_mul_of_nonneg_right hsize (by positivity)).trans_eq (by ring)
  apply row_norm_of_sums _ (by positivity) T (fun x _ => row x _ (hpoint x) (hzero x))
  intro y
  apply (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun x _ _ => abs_nonneg (E x y))).trans
  exact row y _ (fun x => hpoint x y) (fun x h => hzero x y (fun h' => h ((exceptional_pair_swap P _ x y).mp h')))
end Vu

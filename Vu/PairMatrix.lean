module

public import Vu.RegularRows
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Vu
open Finset

private theorem weighted_cut {I : Type*} (A : Finset I) (e u : I → ℝ) (Q U : ℝ)
    (hU : 0 ≤ U) (hu : ∀ i ∈ A, |u i| ≤ U)
    (hcut : ∀ X ⊆ A, |∑ i ∈ X, e i| ≤ Q) : |∑ i ∈ A, u i * e i| ≤ U * (2*Q) := by
  calc
    _ ≤ ∑ i ∈ A, |u i * e i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ A, U * |e i| := sum_le_sum (fun i hi => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hu i hi) (abs_nonneg _))
    _ ≤ _ := by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (sum_abs_le_twice_cut A e Q hcut) hU

/-- Bounds on all rectangles give the bilinear bound on the product
of the two boxes, with the factor four in Lemma 4.5. -/
public theorem box_bound_of_rectangles {I J : Type*} (A : Finset I) (B : Finset J)
    (M : I → J → ℝ) (Q : ℝ)
    (hcut : ∀ X ⊆ A, ∀ Y ⊆ B, |∑ i ∈ X, ∑ j ∈ Y, M i j| ≤ Q)
    (u : I → ℝ) (v : J → ℝ) (U W : ℝ) (hU : 0 ≤ U) (hW : 0 ≤ W)
    (hu : ∀ i ∈ A, |u i| ≤ U) (hv : ∀ j ∈ B, |v j| ≤ W) :
    |∑ i ∈ A, u i * ∑ j ∈ B, M i j * v j| ≤ 4*Q*U*W := by
  let e j := ∑ i ∈ A, u i * M i j
  have hrect (Y : Finset J) (hy : Y ⊆ B) : |∑ j ∈ Y, e j| ≤ U*(2*Q) := by
    dsimp [e]
    rw [sum_comm]
    simp_rw [← mul_sum]
    exact weighted_cut A _ u Q U hU hu (fun X hx => hcut X hx Y hy)
  have heq : (∑ i ∈ A, u i * ∑ j ∈ B, M i j * v j) = ∑ j ∈ B, v j * e j := by
    simp only [e, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro j _
    apply sum_congr rfl
    intro i _
    ring
  rw [heq]
  exact (weighted_cut B e v _ W hW hv hrect).trans_eq (by ring)

private noncomputable def length₂ {I : Type*} (A : Finset I) (f : I → ℝ) : ℝ :=
  √(∑ i ∈ A, f i^2)

private theorem length₂_sq {I : Type*} (A : Finset I) (f : I → ℝ) :
    length₂ A f ^ 2 = ∑ i ∈ A, f i^2 := Real.sq_sqrt (sum_nonneg (fun _ _ => sq_nonneg _))

private theorem dot_bound {I : Type*} (A : Finset I) (f g : I → ℝ) :
    |∑ i ∈ A, f i*g i| ≤ length₂ A f * length₂ A g := by
  have h := sum_mul_sq_le_sq_mul_sq A f g
  rw [← length₂_sq, ← length₂_sq, ← mul_pow] at h
  exact (sq_le_sq.mp h).trans_eq (abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))

private theorem length₂_of_bound {I : Type*} (A : Finset I) (f : I → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (h : ∀ i ∈ A, |f i| ≤ B) : length₂ A f ≤ √(A.card : ℝ) * B := by
  have hs : (∑ i ∈ A, f i^2) ≤ (A.card : ℝ) * B^2 := by
    simpa using sum_le_sum (s := A) (fun i hi => (sq_le_sq.mpr ((h i hi).trans_eq (abs_of_nonneg hB).symm)))
  change √_ ≤ _
  rw [← Real.sqrt_sq hB, ← Real.sqrt_mul (Nat.cast_nonneg A.card)]
  exact Real.sqrt_le_sqrt hs

/-- Cut-to-spectral estimate used in Lemma 4.5. For f, put g=Mf and
h=Mᵀg. Then ‖g‖²=⟨f,h⟩, and ‖h‖²=⟨g,Mh⟩. This avoids choosing singular
vectors and works for arbitrary rectangular finite matrices. -/
public theorem spectral_bound_of_rectangles {I J : Type*} (A : Finset I) (B : Finset J)
    (M : I → J → ℝ) (Q E K : ℝ) (hE : 0 ≤ E) (hK : 0 ≤ K)
    (hentry : ∀ i ∈ A, ∀ j ∈ B, |M i j| ≤ E)
    (hcut : ∀ X ⊆ A, ∀ Y ⊆ B, |∑ i ∈ X, ∑ j ∈ Y, M i j| ≤ Q)
    (hparam : 4*Q * (√(A.card : ℝ) * √(B.card : ℝ)) * E^2 ≤ K^3)
    (f : J → ℝ) :
    ∑ i ∈ A, (∑ j ∈ B, M i j*f j)^2 ≤ K^2 * ∑ j ∈ B, (f j)^2 := by
  let g i := ∑ j ∈ B, M i j * f j
  let h j := ∑ i ∈ A, g i * M i j
  let F := length₂ B f
  let G := length₂ A g
  let H := length₂ B h
  have hF : 0 ≤ F := Real.sqrt_nonneg _
  have hG : 0 ≤ G := Real.sqrt_nonneg _
  have hH : 0 ≤ H := Real.sqrt_nonneg _
  have dual (v : J → ℝ) : (∑ i ∈ A, g i * ∑ j ∈ B, M i j * v j) = ∑ j ∈ B, v j * h j := by
    simp only [h, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro j _
    apply sum_congr rfl
    intro i _
    ring
  have hGsq : G^2 ≤ F*H := by
    have hEq : G^2 = ∑ j ∈ B, f j * h j := by simpa only [G, length₂_sq, ← sq, g] using dual f
    rw [hEq]
    exact (le_abs_self _).trans (dot_bound B f h)
  have hg (i : I) (hi : i ∈ A) : |g i| ≤ (√(B.card : ℝ)*E)*F :=
    (dot_bound B (M i) f).trans (mul_le_mul_of_nonneg_right (length₂_of_bound B _ E hE (hentry i hi)) hF)
  have hh (j : J) (hj : j ∈ B) : |h j| ≤ (√(A.card : ℝ)*E)*G := by
    apply (dot_bound A g (fun i => M i j)).trans
    rw [mul_comm _ G]
    exact mul_le_mul_of_nonneg_left (length₂_of_bound A _ E hE (fun i hi => hentry i hi j hj)) hG
  have hHsq : H^2 ≤ K^3 * F*G := by
    have he := box_bound_of_rectangles A B M Q hcut g h _ _ (by positivity) (by positivity) hg hh
    rw [dual h] at he
    simp only [← sq, ← length₂_sq] at he
    calc
      _ ≤ |H^2| := le_abs_self _
      _ ≤ 4*Q*((√(B.card : ℝ)*E)*F)*((√(A.card : ℝ)*E)*G) := he
      _ = (4*Q*(√(A.card : ℝ)*√(B.card : ℝ))*E^2)*F*G := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hparam hF) hG
  change ∑ i ∈ A, g i^2 ≤ K^2 * ∑ j ∈ B, f j^2
  rw [← length₂_sq, ← length₂_sq]
  change G^2 ≤ K^2 * F^2
  by_cases hz : G = 0
  · simpa [hz] using (mul_nonneg (sq_nonneg K) (sq_nonneg F))
  have hgpos := lt_of_le_of_ne hG (Ne.symm hz)
  have h4 : G^4 ≤ ((K*F)^3)*G := by
    calc
      _ = (G^2)^2 := by ring
      _ ≤ (F*H)^2 := pow_le_pow_left₀ (sq_nonneg _) hGsq 2
      _ = F^2 * H^2 := mul_pow .. 
      _ ≤ F^2 * (K^3 * F*G) := mul_le_mul_of_nonneg_left hHsq (sq_nonneg _)
      _ = _ := by ring
  have h3 : G^3 ≤ (K*F)^3 := (mul_le_mul_iff_of_pos_right hgpos).mp (by simpa [pow_succ] using h4)
  have h1 : G ≤ K*F := le_of_pow_le_pow_left₀ (by decide : 3 ≠ 0) (mul_nonneg hK hF) h3
  simpa [mul_pow] using pow_le_pow_left₀ hG h1 2

/-- Entry (M) of the centered graph matrix on a pair of density d. -/
@[expose] public noncomputable def centeredEntry {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℝ) (x y : V) : ℝ := (d - (if G.Adj x y then 1 else 0)) / (1-d)

public theorem edge_rectangle {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V) :
    (∑ x ∈ X, ∑ y ∈ Y, if G.Adj x y then (1 : ℝ) else 0) =
      crossDensity G X Y * ((X.card : ℝ)*Y.card) := by
  classical
  rcases X.eq_empty_or_nonempty with rfl | hx
  · simp
  rcases Y.eq_empty_or_nonempty with rfl | hy
  · simp
  have hzero : (X.card : ℝ)*Y.card ≠ 0 :=
    (mul_pos (Nat.cast_pos.mpr (card_pos.mpr hx)) (Nat.cast_pos.mpr (card_pos.mpr hy))).ne'
  rw [crossDensity, div_mul_cancel₀ _ hzero]
  apply sum_congr rfl
  intro x _
  have he : Y.filter (G.Adj x) = G.neighborFinset x ∩ Y := by ext y; simp [and_comm]
  simp [← he]

public theorem density_mem_unit {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    0 ≤ crossDensity G A B ∧ crossDensity G A B ≤ 1 := by
  unfold crossDensity
  constructor
  · exact div_nonneg (sum_nonneg (fun _ _ => Nat.cast_nonneg _)) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  rcases A.eq_empty_or_nonempty with rfl | ha
  · simp
  rcases B.eq_empty_or_nonempty with rfl | hb
  · simp
  apply (div_le_iff₀ (mul_pos (Nat.cast_pos.mpr (card_pos.mpr ha)) (Nat.cast_pos.mpr (card_pos.mpr hb)))).mpr
  simpa using sum_le_sum (s := A) (fun x _ => Nat.cast_le (α := ℝ) |>.mpr
    (card_le_card (s := G.neighborFinset x ∩ B) inter_subset_right))

/-- On every subrectangle of a sparse regular pair the centered sum has
absolute value at most ρ times the full rectangle area divided by δ. -/
public theorem regular_pair_rectangle {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) (ρ δ : ℝ)
    (hρ : 0 < ρ) (hδ : 0 < δ) (hd : crossDensity G A B < 1-δ)
    (hreg : ∀ X ⊆ A, ∀ Y ⊆ B, ρ * A.card ≤ X.card → ρ * B.card ≤ Y.card →
      |crossDensity G X Y - crossDensity G A B| ≤ ρ)
    (X : Finset V) (hX : X ⊆ A) (Y : Finset V) (hY : Y ⊆ B) :
    |∑ x ∈ X, ∑ y ∈ Y, centeredEntry G (crossDensity G A B) x y| ≤ ρ*((A.card:ℝ)*B.card)/δ := by
  classical
  let d := crossDensity G A B
  let M := centeredEntry G d
  have hd₀ : 0 ≤ d := (density_mem_unit G A B).1
  have hd₁ : d ≤ 1 := (density_mem_unit G A B).2
  have hden : δ ≤ 1-d := by dsimp [d]; linarith only [hd]
  have hpos := hδ.trans_le hden
  change |∑ x ∈ X, ∑ y ∈ Y, M x y| ≤ _
  let a : ℝ := X.card
  let b : ℝ := Y.card
  have ha : 0 ≤ a := Nat.cast_nonneg _
  have hb : 0 ≤ b := Nat.cast_nonneg _
  have hm : a ≤ A.card := Nat.cast_le.mpr (card_le_card hX)
  have hn : b ≤ B.card := Nat.cast_le.mpr (card_le_card hY)
  have hxy : |d-crossDensity G X Y| ≤ 1 := abs_le.mpr (by
    obtain ⟨h₀,h₁⟩ := density_mem_unit G X Y
    constructor <;> linarith)
  have hcut : |d-crossDensity G X Y| * (a*b) ≤ ρ * ((A.card : ℝ)*B.card) := by
    by_cases hlarge : ρ*A.card ≤ a ∧ ρ*B.card ≤ b
    · have hh := hreg X hX Y hY hlarge.1 hlarge.2
      rw [abs_sub_comm] at hh
      exact mul_le_mul hh (mul_le_mul hm hn hb (Nat.cast_nonneg _)) (mul_nonneg ha hb) hρ.le
    · apply (mul_le_mul_of_nonneg_right hxy (mul_nonneg ha hb)).trans
      rw [one_mul]
      push Not at hlarge
      by_cases hrow : ρ*A.card ≤ a
      · calc
          a*b ≤ (A.card : ℝ) * (ρ*B.card) := mul_le_mul hm (hlarge hrow).le hb (Nat.cast_nonneg _)
          _ = _ := by ring
      · calc
          a*b ≤ (ρ*A.card) * B.card := mul_le_mul (le_of_not_ge hrow) hn hb (by positivity)
          _ = _ := by ring
  have heq : (∑ x ∈ X, ∑ y ∈ Y, M x y) =
      (d - crossDensity G X Y) * (a*b) / (1-d) := by
    simp only [M, centeredEntry, div_eq_mul_inv, ← sum_mul, sum_sub_distrib, edge_rectangle]
    simp only [a, b, sum_const, nsmul_eq_mul]
    ring
  rw [heq, abs_div, abs_mul, abs_of_nonneg (mul_nonneg ha hb), abs_of_pos hpos]
  apply (div_le_div_of_nonneg_right hcut hpos.le).trans
  exact div_le_div_of_nonneg_left (by positivity) hδ hden

/-- Graph form of Lemma 4.5 with the exponent 1/3 and the manuscript's constant.
Restricting the two sums to the row and column classes gives the squared
Euclidean operator-norm inequality. -/
public theorem regular_pair_matrix_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) (ρ δ : ℝ)
    (hρ : 0 < ρ) (hδ : 0 < δ) (hd : crossDensity G A B < 1-δ)
    (hreg : ∀ X ⊆ A, ∀ Y ⊆ B, ρ * A.card ≤ X.card → ρ * B.card ≤ Y.card →
      |crossDensity G X Y - crossDensity G A B| ≤ ρ) (f : V → ℝ) :
    ∑ x ∈ A, (∑ y ∈ B, centeredEntry G (crossDensity G A B) x y * f y)^2 ≤
      ((4*ρ)^(1/3 : ℝ) * √((A.card : ℝ)*B.card) / δ)^2 * ∑ y ∈ B, f y^2 := by
  classical
  let d := crossDensity G A B
  let M := centeredEntry G d
  let E : ℝ := 1/δ
  let Q : ℝ := ρ * ((A.card : ℝ)*B.card)/δ
  have hd₀ : 0 ≤ d := (density_mem_unit G A B).1
  have hd₁ : d ≤ 1 := (density_mem_unit G A B).2
  have hden : δ ≤ 1-d := by dsimp [d]; linarith only [hd]
  have hpos := hδ.trans_le hden
  have hE : 0 ≤ E := one_div_nonneg.mpr hδ.le
  have hr : 0 ≤ 4*ρ := by positivity
  have hk : 0 ≤ (4*ρ)^(1/3 : ℝ) * √((A.card : ℝ)*B.card) / δ := by positivity
  apply spectral_bound_of_rectangles A B M Q E _ hE hk
  · intro x _ y _
    change |(d - (if G.Adj x y then 1 else 0)) / (1-d)| ≤ 1/δ
    rw [abs_div, abs_of_pos hpos]
    have hnum : |d - (if G.Adj x y then 1 else 0)| ≤ 1 := by
      split <;> apply abs_le.mpr <;> constructor <;> linarith
    exact (div_le_div_of_nonneg_right hnum hpos.le).trans (one_div_le_one_div_of_le hδ hden)
  · exact regular_pair_rectangle G A B ρ δ hρ hδ hd hreg
  · have ht : ((4*ρ)^(1/3 : ℝ))^(3 : ℕ) = 4*ρ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hr]
      norm_num
    rw [Real.sqrt_mul (Nat.cast_nonneg _)]
    set m := √(A.card : ℝ)
    set n := √(B.card : ℝ)
    have hm : m^2 = A.card := Real.sq_sqrt (Nat.cast_nonneg _)
    have hn : n^2 = B.card := Real.sq_sqrt (Nat.cast_nonneg _)
    simp only [Q, E, div_pow, mul_pow, ht]
    rw [← hm, ← hn]
    exact le_of_eq (by ring)
end Vu

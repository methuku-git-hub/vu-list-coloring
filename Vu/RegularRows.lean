module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic.Linarith

/-! Lemma 4.3. The formal statement uses the degree discrepancy of a row
on each regular partner class and the rectangle inequality obtained by
testing regularity against the entire partner class. -/

namespace Vu
open Finset

/-- A regular pair controls each row subset tested against the whole second
class. For a small subset the entry bound gives the same coarse estimate. -/
public theorem row_subset_discrepancy {V : Type*} (A X : Finset V) (e : V → ℝ)
    (ρ n : ℝ) (hρ : 0 ≤ ρ) (hn : 0 ≤ n) (hX : X ⊆ A)
    (he : ∀ x ∈ A, |e x| ≤ n)
    (hreg : ρ * A.card ≤ X.card → |∑ x ∈ X, e x| ≤ ρ * X.card * n) :
    |∑ x ∈ X, e x| ≤ ρ * A.card * n := by
  by_cases hlarge : ρ * A.card ≤ X.card
  · exact (hreg hlarge).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_le_card hX)) hρ) hn)
  · have habs := abs_sum_le_sum_abs e X
    apply habs.trans
    calc
      _ ≤ ∑ _x ∈ X, n := sum_le_sum (fun x hx => he x (hX hx))
      _ = (X.card : ℝ) * n := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_of_not_ge hlarge) hn

/-- A uniform bound on every subset sum gives an L¹ bound on the whole class. -/
public theorem sum_abs_le_twice_cut {V : Type*} (A : Finset V) (e : V → ℝ) (q : ℝ)
    (hcut : ∀ X ⊆ A, |∑ x ∈ X, e x| ≤ q) : ∑ x ∈ A, |e x| ≤ 2*q := by
  classical
  let P := A.filter fun x => 0 ≤ e x
  let N := A.filter fun x => ¬ 0 ≤ e x
  have hP := (abs_le.mp (hcut P (filter_subset _ _))).2
  have hN := (abs_le.mp (hcut N (filter_subset _ _))).1
  have htotal : ∑ x ∈ A, |e x| = (∑ x ∈ P, e x) - ∑ x ∈ N, e x := by
    rw [← sum_filter_add_sum_filter_not A (fun x => 0 ≤ e x) (fun x => |e x|)]
    have h₁ : ∑ x ∈ P, |e x| = ∑ x ∈ P, e x :=
      sum_congr rfl (fun x hx => abs_of_nonneg (mem_filter.mp hx).2)
    have h₂ : ∑ x ∈ N, |e x| = ∑ x ∈ N, -e x :=
      sum_congr rfl (fun x hx => abs_of_neg (lt_of_not_ge (mem_filter.mp hx).2))
    change (∑ x ∈ P, |e x|) + (∑ x ∈ N, |e x|) = _
    rw [h₁, h₂, sum_neg_distrib, sub_eq_add_neg]
  rw [htotal]
  linarith

/-- Part of Lemma 4.3 that counts vertices failing (G). Here `A` is one
nonexceptional class, `J` indexes its regular partners, `n j` is the size
of partner class j, and `size` is the order of the entire piece.
For a regular pair, `hreg` is the defining density inequality tested
against a subset of A and the entire partner. -/
public theorem bad_rows_card {V J : Type*} [Fintype J] (A : Finset V)
    (e : V → J → ℝ) (n : J → ℝ) (ρ size : ℝ) (hρ : 0 < ρ) (hs : 0 < size)
    (hn : ∀ j, 0 ≤ n j) (hnt : ∑ j, n j ≤ size)
    (he : ∀ x ∈ A, ∀ j, |e x j| ≤ n j)
    (hreg : ∀ j, ∀ X ⊆ A, ρ * A.card ≤ X.card →
        |∑ x ∈ X, e x j| ≤ ρ * X.card * n j) :
    ((A.filter (fun x => 4 * √ρ * size < ∑ j, |e x j|)).card : ℝ) ≤ √ρ * A.card := by
  classical
  let Bad := A.filter (fun x => 4 * √ρ * size < ∑ j, |e x j|)
  have hmean : ∑ x ∈ A, ∑ j, |e x j| ≤ 2 * (ρ * A.card) * size := by
    rw [sum_comm]
    calc
      _ ≤ ∑ j, 2 * (ρ * A.card * n j) := by
        apply sum_le_sum
        intro j _
        exact sum_abs_le_twice_cut A _ _ (fun X hX =>
          row_subset_discrepancy A X _ ρ (n j) hρ.le (hn j) hX
            (fun x hx => he x hx j) (hreg j X hX))
      _ = 2 * (ρ * A.card) * ∑ j, n j := by simp only [mul_assoc, mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hnt (by positivity)
  have hMarkov : (Bad.card : ℝ) * (4 * √ρ * size) ≤ ∑ x ∈ A, ∑ j, |e x j| := by
    calc
      _ = ∑ _x ∈ Bad, 4 * √ρ * size := by simp
      _ ≤ ∑ x ∈ Bad, ∑ j, |e x j| :=
        sum_le_sum (fun x hx => (mem_filter.mp hx).2.le)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => sum_nonneg (fun _ _ => abs_nonneg _))
  change (Bad.card : ℝ) ≤ _
  have hroot := Real.sq_sqrt hρ.le
  apply (mul_le_mul_iff_of_pos_right (mul_pos (Real.sqrt_pos.mpr hρ) hs)).mp
  have hnonneg : 0 ≤ ρ * A.card * size := by positivity
  calc
    _ ≤ 2 * (ρ * A.card) * size / 4 := by linarith [hMarkov.trans hmean]
    _ ≤ ρ * A.card * size := by linarith
    _ = √ρ ^ 2 * A.card * size := by rw [hroot]
    _ = _ := by ring


/-- Edge density between two finite vertex sets, counting ordered incidences. -/
@[expose] public noncomputable def crossDensity {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) : ℝ :=
  (∑ x ∈ A, ((G.neighborFinset x ∩ B).card : ℝ)) / (A.card * B.card : ℝ)

/-- Lemma 4.3, in graph terms. The family consists of precisely the partners
on which regularity is available, with total class size at most the piece size.
The density assumption is ordinary ε-regularity of each pair. -/
public theorem bad_rows_of_regular_pairs {V J : Type*} [Fintype V] [Fintype J] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (B : J → Finset V) (ρ size : ℝ)
    (hA : A.Nonempty) (hB : ∀ j, (B j).Nonempty) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1)
    (hs : 0 < size) (ht : ∑ j, ((B j).card : ℝ) ≤ size)
    (hreg : ∀ j, ∀ X ⊆ A, ∀ Y ⊆ B j, ρ * A.card ≤ X.card → ρ * (B j).card ≤ Y.card →
      |crossDensity G X Y - crossDensity G A (B j)| ≤ ρ) :
    ((A.filter fun x => 4 * √ρ * size <
      ∑ j, |((G.neighborFinset x ∩ B j).card : ℝ) - crossDensity G A (B j) * (B j).card|).card : ℝ)
      ≤ √ρ * A.card := by
  classical
  let deg (x : V) (j : J) : ℝ := (G.neighborFinset x ∩ B j).card
  let d (j : J) := crossDensity G A (B j)
  have hdeg₀ (x : V) (j : J) : 0 ≤ deg x j := Nat.cast_nonneg _
  have hdeg (x : V) (j : J) : deg x j ≤ (B j).card :=
    Nat.cast_le.mpr (card_le_card inter_subset_right)
  have hApos : (0 : ℝ) < A.card := Nat.cast_pos.mpr (card_pos.mpr hA)
  have hBpos j : (0 : ℝ) < (B j).card := Nat.cast_pos.mpr (card_pos.mpr (hB j))
  have hd₀ j : 0 ≤ d j := div_nonneg (sum_nonneg fun x _ => hdeg₀ x j) (mul_pos hApos (hBpos j)).le
  have hd₁ j : d j ≤ 1 := by
    apply (div_le_iff₀ (mul_pos hApos (hBpos j))).mpr
    simpa using sum_le_sum (s := A) (fun x _ => hdeg x j)
  apply bad_rows_card A (fun x j => deg x j - d j * (B j).card) (fun j => (B j).card) ρ size hρ hs
    (fun j => (hBpos j).le) ht
  · intro x _ j
    have hbd : d j * (B j).card ≤ (B j).card := by
      simpa using mul_le_mul_of_nonneg_right (hd₁ j) (hBpos j).le
    have hbot := mul_nonneg (hd₀ j) (hBpos j).le
    exact abs_le.mpr ⟨by linarith [hdeg₀ x j], by linarith [hdeg x j]⟩
  · intro j X hX hlarge
    have hXpos : (0 : ℝ) < X.card := (mul_pos hρ hApos).trans_le hlarge
    have htest := hreg j X hX (B j) (subset_refl _) hlarge
      (by simpa using mul_le_mul_of_nonneg_right hρ₁ (hBpos j).le)
    have hden := mul_pos hXpos (hBpos j)
    have hsum : ∑ x ∈ X, (deg x j - d j * (B j).card) =
        (crossDensity G X (B j) - d j) * (X.card * (B j).card : ℝ) := by
      rw [sum_sub_distrib, sub_mul]
      unfold crossDensity
      rw [div_mul_cancel₀ _ hden.ne']
      simp only [sum_const, nsmul_eq_mul]
      dsimp [deg]
      ring
    rw [hsum, abs_mul, abs_of_pos hden, mul_assoc]
    exact mul_le_mul_of_nonneg_right htest hden.le

/-- The second conclusion of Lemma 4.3, with its size threshold explicit. -/
public theorem two_good_rows {V : Type*} [DecidableEq V] (A Bad : Finset V) (hBA : Bad ⊆ A)
    (ρ : ℝ) (hbad : (Bad.card : ℝ) ≤ √ρ * A.card)
    (hlarge : 2 ≤ (1-√ρ) * A.card) : 2 ≤ (A \ Bad).card := by
  have hsum : (A \ Bad).card + Bad.card = A.card := Finset.card_sdiff_add_card_eq_card hBA
  have hreal : ((A \ Bad).card : ℝ) + Bad.card = A.card := by exact_mod_cast hsum
  have : (2 : ℝ) ≤ (A \ Bad).card := by linarith
  exact_mod_cast this

end Vu

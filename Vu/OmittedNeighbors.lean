module

public import Vu.Reduction
public import Mathlib.Analysis.Real.Sqrt

/-! The counting and matrix inequalities used for the choice of omitted sets
in Lemma 4.8. Rows and columns outside the chosen finite sets have zero entries. -/
namespace Vu
open Finset

/-- An upper bound on the number of rows carrying a fixed label α outside
the selected group. Except for split rows, a missed frequent label must
co-occur with another frequent label in a small intersection. -/
public theorem missed_label_card_le {V A : Type*} [DecidableEq V]
    (miss split : Finset V) (frequent : Finset A) (overlap : A → Finset V) (q : ℕ)
    (hmiss : ∀ x ∈ miss, x ∈ split ∨ ∃ β ∈ frequent, x ∈ overlap β)
    (hsmall : ∀ β ∈ frequent, (overlap β).card ≤ q) :
    miss.card ≤ split.card + frequent.card * q := by
  classical
  have hsub : miss ⊆ split ∪ frequent.biUnion overlap := by
    intro x hx
    simpa only [mem_union, mem_biUnion] using hmiss x hx
  have hcount : (frequent.biUnion overlap).card ≤ frequent.card * q := by
    apply card_biUnion_le.trans
    simpa using (sum_le_sum hsmall)
  exact (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add_left hcount _))

/-- If at most `d` unaccounted rows carry each possible label and each
column has at most `r` possible labels, that column meets at most `r*d` rows. -/
public theorem residual_column_card_le {V A : Type*} [DecidableEq V]
    (rows : Finset V) (labels : Finset A) (miss : A → Finset V) (r d : ℕ)
    (hrow : ∀ u ∈ rows, ∃ α ∈ labels, u ∈ miss α)
    (hlabels : labels.card ≤ r) (hmiss : ∀ α ∈ labels, (miss α).card ≤ d) :
    rows.card ≤ r * d := by
  classical
  have hsub : rows ⊆ labels.biUnion miss := fun u hu => mem_biUnion.mpr (hrow u hu)
  calc
    _ ≤ ∑ α ∈ labels, (miss α).card := (card_le_card hsub).trans card_biUnion_le
    _ ≤ labels.card * d := by simpa using sum_le_sum hmiss
    _ ≤ _ := Nat.mul_le_mul_right d hlabels

/-- The zero-one row/column norm bound used in (D2), expressed without
singular vectors. If row sums are at most R and column sums at most C,
the squared operator norm is at most R*C. -/
public theorem incidence_matrix_bound {V : Type*} [Fintype V] [DecidableEq V]
    (T : Finset V) (N : V → Finset V) (R C : ℕ)
    (hrows : ∀ u ∈ T, (N u).card ≤ R)
    (hcols : ∀ z, (T.filter fun u => z ∈ N u).card ≤ C) (f : V → ℝ) :
    ∑ u ∈ T, (∑ z ∈ N u, f z)^2 ≤ ((R * C : ℕ) : ℝ) * ∑ z, (f z)^2 := by
  classical
  have hrow u (hu : u ∈ T) :
      (∑ z ∈ N u, f z)^2 ≤ (R : ℝ) * ∑ z ∈ N u, f z^2 := by
    have h := sum_mul_sq_le_sq_mul_sq (N u) (fun _ => (1 : ℝ)) f
    simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] at h
    exact h.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hrows u hu))
      (sum_nonneg fun _ _ => sq_nonneg _))
  have htotal : ∑ u ∈ T, ∑ z ∈ N u, f z^2 ≤ (C : ℝ) * ∑ z, f z^2 := by
    calc
      _ = ∑ u ∈ T, ∑ z : V, if z ∈ N u then f z^2 else 0 := by
        apply sum_congr rfl
        intro u _
        simp
      _ = ∑ z : V, ((T.filter fun u => z ∈ N u).card : ℝ) * f z^2 := by
        rw [sum_comm]
        apply sum_congr rfl
        intro z _
        simp [← sum_filter]
      _ ≤ _ := by
        rw [mul_sum]
        exact sum_le_sum (fun z _ => mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hcols z)) (sq_nonneg _))
  calc
    _ ≤ ∑ u ∈ T, (R : ℝ) * ∑ z ∈ N u, f z^2 := sum_le_sum hrow
    _ ≤ _ := by
      rw [← mul_sum, Nat.cast_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left htotal (Nat.cast_nonneg _)

/-- The operator-norm conclusion for the residual neighbors, with explicit constants. -/
public theorem residual_rowNormLE {V : Type*} [Fintype V] [DecidableEq V]
    (T : Finset V) (N : V → Finset V) (R C : ℕ)
    (hrows : ∀ u ∈ T, (N u).card ≤ R)
    (hcols : ∀ z, (T.filter fun u => z ∈ N u).card ≤ C) :
    RowNormLE (fun u z => if z ∈ N u then 1 else 0) T (Real.sqrt (R * C : ℕ)) := by
  intro f
  simp only [ite_mul, one_mul, zero_mul, ← sum_filter, filter_univ_mem,
    Real.sq_sqrt (Nat.cast_nonneg (R*C))]
  exact incidence_matrix_bound T N R C hrows hcols f

end Vu

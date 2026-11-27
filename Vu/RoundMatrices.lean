module
public import Vu.RoundWeights
public import Vu.RowNorm
namespace Vu
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {D k R : ℕ} {b C η : ℝ} (d : Decomposition G D k R b C η)

/-- Comparison matrix after omitting all hard multipliers in one chosen
hard test at each row. -/
@[expose] public noncomputable def comparisonEntry (S : V → Finset V) (x y : V) : ℝ := by
  classical exact if d.H.Adj x y ∧ y ∉ S x then -1 else d.matrix x y

public theorem comparison_bounds (S : V → Finset V) (hC : 1 ≤ C) (x y : V) :
    -1 ≤ comparisonEntry d S x y ∧ comparisonEntry d S x y ≤ C := by
  classical
  dsimp only [comparisonEntry]; split <;> first | exact d.entry_bounds _ _ | constructor <;> linarith

public theorem comparison_row_sum (S : V → Finset V) (hdeg : ∀ x, G.degree x ≤ D) (x : V) :
    ∑ y, |comparisonEntry d S x y| ≤ (C+1)*D := by
  classical
  have hpoint (y : V) : |comparisonEntry d S x y| ≤ |d.matrix x y|+(if G.Adj x y then 1 else 0) := by
    dsimp [comparisonEntry]
    split
    next h => have he := (d.edge_iff x y).mpr (Or.inl h.1); simp [he,d.hard x y h.1]
    next => split <;> linarith
  apply (sum_le_sum fun y _ => hpoint y).trans
  rw [sum_add_distrib]
  have hn : (∑ y, if G.Adj x y then (1:ℝ) else 0) = G.degree x := by
    simp [←sum_filter,SimpleGraph.degree,SimpleGraph.neighborFinset_def]
  rw [hn]
  linarith [d.row_sum x,Nat.cast_le (α := ℝ) |>.mpr (hdeg x)]

public theorem comparison_variance_row (S : V → Finset V) (hC : 1 ≤ C) (hdeg : ∀ x, G.degree x ≤ D)
    (v : V → ℝ) (vmax : ℝ) (hv : ∀ y, v y ≤ vmax) (hmax : 0 ≤ vmax) (x : V) :
    (∑ y, comparisonEntry d S x y^2 * v y) ≤ (C+1)^2*D*vmax := by
  have entry (y : V) : |comparisonEntry d S x y| ≤ C+1 := abs_le.mpr (by
    obtain ⟨hl,hh⟩ := comparison_bounds d S hC x y
    constructor <;> linarith)
  apply (sum_le_sum (g := fun y => (C+1)*|comparisonEntry d S x y| *vmax) (fun y _ => ?_)).trans
  · rw [←sum_mul,←mul_sum]
    have hh := mul_le_mul_of_nonneg_left (comparison_row_sum d S hdeg x) (by linarith : 0 ≤ C+1)
    exact (mul_le_mul_of_nonneg_right hh hmax).trans_eq (by ring)
  · apply (mul_le_mul_of_nonneg_left (hv y) (sq_nonneg _)).trans
    apply mul_le_mul_of_nonneg_right _ hmax
    simpa [←sq, sq_abs] using mul_le_mul_of_nonneg_right (entry y) (abs_nonneg (comparisonEntry d S x y))

/-- For every row set T supply all comparison-matrix properties used
by the one-color variance bound from the decomposition itself. -/
public theorem comparison_for_test (T : Finset V) (hT : T.card ≤ D) (hη : 0 ≤ η) :
    ∃ S : V → Finset V, (∀ x ∈ T, S x = ∅ ∨ S x ∈ d.tests x) ∧
      (∀ x ∈ T, ∀ y ∈ S x, comparisonEntry d S x y = 0) ∧
      (∀ x ∈ T, ∀ y, (if y ∈ S x then -1 else comparisonEntry d S x y) = updateEntry d x y) ∧
      RowNormLE (comparisonEntry d S) T (2*η*D) := by
  classical
  obtain ⟨S,hs,hn⟩ := d.omitted T hT
  have hard (x : V) (hx : x ∈ T) (y : V) (hy : y ∈ S x) : d.H.Adj x y := by
    rcases hs x hx with he | hu
    · simp [he] at hy
    · exact (d.tests_cover x y).mpr ⟨S x,hu,hy⟩
  refine ⟨S,hs,?_,?_,?_⟩
  · intro x hx y hy; simp [comparisonEntry,hy,d.hard x y (hard x hx y hy)]
  · intro x hx y
    by_cases hy : y ∈ S x
    · simp [comparisonEntry,updateEntry,hy,hard x hx y hy]
    · simp [comparisonEntry,updateEntry,hy]
  · have ha := row_norm_add (mul_nonneg hη (Nat.cast_nonneg D)) (mul_nonneg hη (Nat.cast_nonneg D))
      (d.norm_bound T hT) (row_norm_neg hn)
    convert ha using 1
    · funext x y
      by_cases hh : d.H.Adj x y ∧ y ∉ S x <;> simp [comparisonEntry,hh]
      simp [d.hard x y hh.1]
    · ring

public theorem update_variance_row (hC : 1 ≤ C) (hdeg : ∀ x, G.degree x ≤ D)
    (v : V → ℝ) (vmax : ℝ) (hv : ∀ y, v y ≤ vmax) (hmax : 0 ≤ vmax) (x : V) :
    (∑ y, updateEntry d x y^2*v y) ≤ (C+1)^2*D*vmax := by
  have eq : comparisonEntry d (fun _ => ∅) = updateEntry d := by
    funext u y
    have hn : y ∉ (∅ : Finset V) := notMem_empty _
    by_cases h : d.H.Adj u y <;> simp [comparisonEntry,updateEntry,h,hn]
  rw [← eq]
  exact comparison_variance_row d _ hC hdeg v vmax hv hmax x
end Vu

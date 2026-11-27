module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Ring

namespace Vu

/-- If `x` and `y` each miss at most `q` members of `U`, and at most `t`
vertices are adjacent to both, then `U` has size at most `t + 2*q`. -/
public theorem card_le_codegree_add_two_mul {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) (U : Finset V) (t q : ℕ)
    (hxy : Fintype.card (G.commonNeighbors x y) ≤ t)
    (hx : (U \ G.neighborFinset x).card ≤ q) (hy : (U \ G.neighborFinset y).card ≤ q) :
    U.card ≤ t + 2 * q := by
  classical
  let A := G.neighborFinset x
  let B := G.neighborFinset y
  have hcore : (A ∩ B).card = Fintype.card (G.commonNeighbors x y) := by
    change (G.neighborFinset x ∩ G.neighborFinset y).card = _
    rw [← Set.toFinset_card]
    congr 1
    ext v
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, Set.mem_toFinset, SimpleGraph.mem_commonNeighbors]
  have hsub : U ⊆ (A ∩ B) ∪ ((U \ A) ∪ (U \ B)) := by
    intro v hv
    by_cases ha : v ∈ A <;> by_cases hb : v ∈ B <;> simp [ha, hb, hv]
  have h₁ := Finset.card_le_card hsub
  have h₂ := Finset.card_union_le (A ∩ B) ((U \ A) ∪ (U \ B))
  have h₃ := Finset.card_union_le (U \ A) (U \ B)
  change (U \ A).card ≤ q at hx
  change (U \ B).card ≤ q at hy
  omega

/-- The multiplicative factor in the coloring round is at most `exp (-b*p)`. -/
public theorem survival_factor_le (p b : ℝ) :
    Real.exp (p * (1 - b)) * (1 - p) ≤ Real.exp (-(b * p)) := by
  have h : 1 - p ≤ Real.exp (-p) := by
    simpa [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-p)
  calc
    _ ≤ Real.exp (p * (1 - b)) * Real.exp (-p) :=
      mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- A strictly positive saving gives a contraction. -/
public theorem survival_factor_lt_one {p b : ℝ} (hp : 0 < p) (hb : 0 < b) :
    Real.exp (p * (1 - b)) * (1 - p) < 1 := by
  apply lt_of_le_of_lt (survival_factor_le p b)
  exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos hb hp))

end Vu

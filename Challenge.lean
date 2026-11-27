module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Vu's fixed-ratio list-coloring conjecture

The threshold depends on the fixed codegree ratio and on the error. Every pair
of distinct vertices is tested, including nonadjacent pairs. Lists may differ
between vertices, and the palette need not be finite. The integer list size
is the floor of the real-valued upper bound for the list chromatic number.
-/

namespace Vu

/-- For fixed positive `ζ` and `ε`, every graph of sufficiently large maximum
degree bound `D` and pair codegrees at most `ζ * D` admits a proper coloring
from arbitrary vertex lists of size at least `⌊(ζ + ε) * D⌋₊`. -/
public theorem main_result :
    ∀ ζ : ℝ, 0 < ζ → ∀ ε : ℝ, 0 < ε →
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
    ∀ (V C : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (∀ v, G.degree v ≤ D) →
    (∀ x y : V, x ≠ y → (Fintype.card (G.commonNeighbors x y) : ℝ) ≤ ζ * D) →
    ∀ L : V → Finset C, (∀ v, ⌊(ζ + ε) * D⌋₊ ≤ (L v).card) →
    ∃ f : V → C, (∀ v, f v ∈ L v) ∧ ∀ ⦃x y⦄, G.Adj x y → f x ≠ f y := by
  sorry

/-- The real degree-bound formulation in the manuscript. -/
public theorem main_result_real :
    ∀ ζ : ℝ, 0 < ζ → ∀ ε : ℝ, 0 < ε →
    ∃ D₀ : ℕ, ∀ D : ℝ, (D₀ : ℝ) ≤ D →
    ∀ (V C : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (∀ v, (G.degree v : ℝ) ≤ D) →
    (∀ x y : V, x ≠ y → (Fintype.card (G.commonNeighbors x y) : ℝ) ≤ ζ * D) →
    ∀ L : V → Finset C, (∀ v, ⌊(ζ + ε) * D⌋₊ ≤ (L v).card) →
    ∃ f : V → C, (∀ v, f v ∈ L v) ∧ ∀ ⦃x y⦄, G.Adj x y → f x ≠ f y := by
  sorry

end Vu

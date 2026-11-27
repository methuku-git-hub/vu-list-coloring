module
public import Vu.ColoringRound
public import Vu.DegreeFloor
namespace Vu
public theorem real_degree_bound : ∀ ζ : ℝ, 0 < ζ → ∀ ε : ℝ, 0 < ε →
    ∃ D₀ : ℕ, ∀ D : ℝ, (D₀ : ℝ) ≤ D →
    ∀ (V C : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (∀ v, (G.degree v : ℝ) ≤ D) →
    (∀ x y : V, x ≠ y → (Fintype.card (G.commonNeighbors x y) : ℝ) ≤ ζ * D) →
    ∀ L : V → Finset C, (∀ v, ⌊(ζ + ε) * D⌋₊ ≤ (L v).card) →
    ∃ f : V → C, (∀ v, f v ∈ L v) ∧ ∀ ⦃x y⦄, G.Adj x y → f x ≠ f y :=
  real_degree_of_uniform (uniformBound_of_decomposition_and_coloring graph_decomposition (coloring_of_round coloring_round))
end Vu

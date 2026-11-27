module
public import Vu.Bounds
namespace Vu
/-- The manuscript also allows a real maximum-degree bound. Apply the
stronger integral codegree estimate with the floor of the degree bound. -/
public theorem real_degree_of_uniform (bound : UniformBound) : ∀ ζ : ℝ, 0 < ζ → ∀ ε : ℝ, 0 < ε →
    ∃ D₀ : ℕ, ∀ D : ℝ, (D₀ : ℝ) ≤ D →
    ∀ (V C : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (∀ v, (G.degree v : ℝ) ≤ D) →
    (∀ x y : V, x ≠ y → (Fintype.card (G.commonNeighbors x y) : ℝ) ≤ ζ * D) →
    ∀ L : V → Finset C, (∀ v, ⌊(ζ + ε) * D⌋₊ ≤ (L v).card) →
    ∃ f : V → C, (∀ v, f v ∈ L v) ∧ ∀ ⦃x y⦄, G.Adj x y → f x ≠ f y := by
  intro ζ hζ ε hε
  obtain ⟨N,hN⟩ := bound ε hε
  refine ⟨N,?_⟩
  intro D hD V C _ G _ hd ht L hL
  have h0 := (Nat.cast_nonneg N).trans hD
  apply hN ⌊D⌋₊ (Nat.le_floor hD) V C G (fun v => Nat.le_floor (hd v)) ⌊ζ*D⌋₊ (fun x y h => Nat.le_floor (ht x y h)) L
  intro v
  apply le_trans _ (hL v)
  apply Nat.floor_mono
  rw [add_mul]
  exact add_le_add (Nat.floor_le (mul_nonneg hζ.le h0)) (mul_le_mul_of_nonneg_left (Nat.floor_le h0) hε.le)
end Vu

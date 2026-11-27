module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

namespace Vu

/-- The additive bound with an integer upper bound `t` on all pair codegrees. -/
@[expose] public def UniformBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
    ∀ (V C : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (∀ v, G.degree v ≤ D) →
    ∀ t : ℕ, (∀ x y : V, x ≠ y → Fintype.card (G.commonNeighbors x y) ≤ t) →
    ∀ L : V → Finset C, (∀ v, ⌊(t : ℝ) + ε * D⌋₊ ≤ (L v).card) →
    ∃ f : V → C, (∀ v, f v ∈ L v) ∧ ∀ ⦃x y⦄, G.Adj x y → f x ≠ f y

/-- Vu's fixed-ratio bound, with the two constants fixed before the threshold. -/
@[expose] public def FixedRatioBound : Prop :=
    ∀ ζ : ℝ, 0 < ζ → ∀ ε : ℝ, 0 < ε →
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
    ∀ (V C : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (∀ v, G.degree v ≤ D) →
    (∀ x y : V, x ≠ y → (Fintype.card (G.commonNeighbors x y) : ℝ) ≤ ζ * D) →
    ∀ L : V → Finset C, (∀ v, ⌊(ζ + ε) * D⌋₊ ≤ (L v).card) →
    ∃ f : V → C, (∀ v, f v ∈ L v) ∧ ∀ ⦃x y⦄, G.Adj x y → f x ≠ f y

/-- The fixed-ratio form obtained from a bound uniform in the integer codegree
parameter. The proof takes `t = ⌊ζD⌋` and retains both floors exactly. -/
public theorem fixedRatio_of_uniformBound (h : UniformBound) : FixedRatioBound := by
  intro ζ hζ ε hε
  obtain ⟨D₀, hD₀⟩ := h ε hε
  refine ⟨D₀, ?_⟩
  intro D hD V C _ G _ hdeg hcodeg L hL
  apply hD₀ D hD V C G hdeg ⌊ζ * D⌋₊ (fun x y hxy => Nat.le_floor (hcodeg x y hxy)) L
  intro v
  apply le_trans _ (hL v)
  apply Nat.floor_mono
  rw [add_mul]
  exact add_le_add_left (Nat.floor_le (mul_nonneg hζ.le (Nat.cast_nonneg D))) _

/-- Conversely, only finitely many fixed ratios are needed at each accuracy.
Taking the largest of their degree thresholds gives a threshold independent of
the integer codegree bound. -/
public theorem uniformBound_of_fixedRatio (h : FixedRatioBound) : UniformBound := by
  classical
  intro ε hε
  let δ := ε / 2
  have hδ : 0 < δ := half_pos hε
  let ratio (i : ℕ) : ℝ := (i + 1 : ℝ) * δ
  have hratio (i : ℕ) : 0 < ratio i :=
    mul_pos (add_pos_of_nonneg_of_pos (Nat.cast_nonneg i) zero_lt_one) hδ
  choose threshold hthreshold using fun i : ℕ => h (ratio i) (hratio i) δ hδ
  let indices := Finset.range (⌊1 / δ⌋₊ + 1)
  refine ⟨max 1 (indices.sup threshold), ?_⟩
  intro D hD V C _ G _ hdeg t hcodeg L hL
  have hposN : 0 < D := (le_max_left 1 (indices.sup threshold)).trans hD
  have hpos : 0 < (D : ℝ) := Nat.cast_pos.mpr hposN
  let m := min t D
  let a : ℝ := m / (D : ℝ)
  have ha : 0 ≤ a := div_nonneg (Nat.cast_nonneg m) hpos.le
  have ha₁ : a ≤ 1 := by
    apply (div_le_iff₀ hpos).mpr
    rw [one_mul]
    exact Nat.cast_le.mpr (min_le_right t D)
  have haD : a * D = m := div_mul_cancel₀ _ hpos.ne'
  let i := ⌊a / δ⌋₊
  have hi : i ∈ indices :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_mono (div_le_div_of_nonneg_right ha₁ hδ.le)))
  have hd : threshold i ≤ D := (Finset.le_sup hi).trans ((le_max_right _ _).trans hD)
  have haratio : a ≤ ratio i :=
    ((div_lt_iff₀ hδ).mp (Nat.lt_floor_add_one (a / δ))).le
  have hratioUpper : ratio i ≤ a + δ := by
    change ((i : ℝ) + 1) * δ ≤ a + δ
    rw [add_mul, one_mul]
    exact add_le_add_left ((le_div_iff₀ hδ).mp (Nat.floor_le (div_nonneg ha hδ.le))) _
  have hm : ∀ x y : V, x ≠ y → Fintype.card (G.commonNeighbors x y) ≤ m := by
    intro x y hxy
    exact le_min (hcodeg x y hxy) ((G.card_commonNeighbors_le_degree_left x y).trans (hdeg x))
  refine hthreshold i D hd V C G hdeg ?_ L ?_
  · intro x y hxy
    calc
      _ ≤ (m : ℝ) := Nat.cast_le.mpr (hm x y hxy)
      _ = a * D := haD.symm
      _ ≤ _ := mul_le_mul_of_nonneg_right haratio hpos.le
  · intro v
    apply le_trans _ (hL v)
    apply Nat.floor_mono
    calc
      _ ≤ (a + ε) * D := by
        apply mul_le_mul_of_nonneg_right _ hpos.le
        dsimp [δ] at hratioUpper ⊢
        linarith
      _ = (m : ℝ) + ε * D := by rw [add_mul, haD]
      _ ≤ _ := add_le_add_left (Nat.cast_le.mpr (min_le_left t D)) _

/-- Equivalence of the additive and fixed-ratio formulations. -/
public theorem uniformBound_iff_fixedRatioBound : UniformBound ↔ FixedRatioBound :=
  ⟨fixedRatio_of_uniformBound, uniformBound_of_fixedRatio⟩

end Vu

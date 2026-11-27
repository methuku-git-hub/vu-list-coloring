module

public import Vu.Bounds
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Tactic.Linarith

/-! The two propositions of Section 3 and their implication for Theorem 1.1. -/
namespace Vu

/-- Maximum pair codegree. Taking a supremum in the naturals gives zero if
there are no distinct vertices. -/
public noncomputable def maxCodegree {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ℕ := by
  classical
  exact Finset.univ.sup (fun x : V =>
    (Finset.univ.erase x).sup fun y => Fintype.card (G.commonNeighbors x y))

public theorem maxCodegree_le_iff {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (t : ℕ) :
    maxCodegree G ≤ t ↔ ∀ x y : V, x ≠ y → Fintype.card (G.commonNeighbors x y) ≤ t := by
  classical
  simp [maxCodegree, Finset.sup_le_iff, ne_comm]

/-- Squared Euclidean operator-norm bound on the rows of `M` in `T`.
The argument `bound` is used only with nonnegative values in (D2) and (D3). -/
@[expose] public def RowNormLE {V : Type*} [Fintype V] (M : V → V → ℝ)
    (T : Finset V) (bound : ℝ) : Prop :=
  ∀ f : V → ℝ, ∑ u ∈ T, (∑ z, M u z * f z) ^ 2 ≤ bound ^ 2 * ∑ z, (f z) ^ 2

/-- Data and conditions (D1)–(D4), including the edge partition, symmetry,
and the requirement that a nonzero matrix entry has graph distance at most four. -/
public structure Decomposition {V : Type*} [Fintype V] (G : SimpleGraph V)
    (D k R : ℕ) (b C η : ℝ) where
  H : SimpleGraph V
  F : SimpleGraph V
  edge_iff : ∀ x y, G.Adj x y ↔ H.Adj x y ∨ F.Adj x y
  disjoint_edges : ∀ x y, H.Adj x y → ¬ F.Adj x y
  tests : V → Finset (Finset V)
  matrix : V → V → ℝ
  symmetric : ∀ u v, matrix u v = matrix v u
  tests_cover : ∀ v z, H.Adj v z ↔ ∃ U ∈ tests v, z ∈ U
  test_count : ∀ v, (tests v).card ≤ R
  test_size : ∀ v, ∀ U ∈ tests v, (U.card : ℝ) ≤ (1 - b) * k
  omitted : ∀ T : Finset V, T.card ≤ D → ∃ S : V → Finset V,
    (∀ u ∈ T, S u = ∅ ∨ S u ∈ tests u) ∧
    (by classical exact RowNormLE (fun u z => if H.Adj u z ∧ z ∉ S u then 1 else 0) T (η * D))
  entry_bounds : ∀ u v, -1 ≤ matrix u v ∧ matrix u v ≤ C
  row_sum : ∀ u, ∑ z, |matrix u z| ≤ C * D
  diagonal : ∀ u, matrix u u = -1
  soft : ∀ u v, F.Adj u v → matrix u v = -1
  hard : ∀ u v, H.Adj u v → matrix u v = 0
  norm_bound : ∀ T : Finset V, T.card ≤ D → RowNormLE matrix T (η * D)
  local_support : ∀ u v, matrix u v ≠ 0 → ∃ p : G.Walk u v, p.length ≤ 4

/-- Proposition 3.1. The four structural constants precede the choice of η. -/
@[expose] public def GraphDecompositionTheorem : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
  ∃ (a b : ℝ) (R : ℕ) (C : ℝ), (0 < a ∧ a < 1) ∧ (0 < b ∧ b < 1) ∧ 2 ≤ C ∧
  ∀ η : ℝ, 0 < η → ∃ D₀ : ℕ, ∀ D ≥ D₀, ∀ (V : Type) [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj], (∀ v, G.degree v ≤ D) →
    let k := ⌊(maxCodegree G : ℝ) + ε * D⌋₊
    a * D ≤ k ∧ k ≤ 2 * D ∧ Nonempty (Decomposition G D k R b C η)

/-- Proposition 3.2. The admissible tolerance η is uniform over all graphs and lists. -/
@[expose] public def ColoringFromDecompositionTheorem : Prop :=
  ∀ (a b : ℝ) (R : ℕ) (C : ℝ), (0 < a ∧ a < 1) → (0 < b ∧ b < 1) → 2 ≤ C →
  ∃ η : ℝ, 0 < η ∧ ∃ D₀ : ℕ, ∀ D ≥ D₀, ∀ (V P : Type) [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj], (∀ v, G.degree v ≤ D) →
    ∀ k : ℕ, a * D ≤ k → k ≤ 2 * D → Nonempty (Decomposition G D k R b C η) →
    ∀ L : V → Finset P, (∀ v, (L v).card = k) →
    ∃ f : V → P, (∀ v, f v ∈ L v) ∧ ∀ ⦃x y⦄, G.Adj x y → f x ≠ f y

/-- The deduction on page 8 of the manuscript, with the two as-yet-unproved
propositions supplied as explicit hypotheses. -/
public theorem uniformBound_of_decomposition_and_coloring
    (hStructure : GraphDecompositionTheorem) (hColor : ColoringFromDecompositionTheorem) :
    UniformBound := by
  classical
  intro ε hε
  let e := min ε 1
  obtain ⟨a, b, R, M, ha, hb, hM, hS⟩ :=
    hStructure e (lt_min hε zero_lt_one) (min_le_right _ _)
  obtain ⟨η, hη, D₂, hD₂⟩ := hColor a b R M ha hb hM
  obtain ⟨D₁, hD₁⟩ := hS η hη
  refine ⟨max D₁ D₂, ?_⟩
  intro D hD V P _ G _ hdeg t ht L hL
  let k := ⌊(maxCodegree G : ℝ) + e * D⌋₊
  obtain ⟨hkl, hku, dec⟩ := hD₁ D ((le_max_left _ _).trans hD) V G hdeg
  have hcap : k ≤ ⌊(t : ℝ) + ε * D⌋₊ := by
    apply Nat.floor_mono
    exact add_le_add (Nat.cast_le.mpr ((maxCodegree_le_iff G t).mpr ht))
      (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg D))
  choose L' hsub hsize using fun v => Finset.exists_subset_card_eq (hcap.trans (hL v))
  obtain ⟨f, hf, hproper⟩ :=
    hD₂ D ((le_max_right _ _).trans hD) V P G hdeg k hkl hku dec L' hsize
  exact ⟨f, fun v => hsub v (hf v), hproper⟩

/-- Theorem 1.1 follows from Propositions 3.1 and 3.2. -/
public theorem main_of_decomposition_and_coloring
    (hStructure : GraphDecompositionTheorem) (hColor : ColoringFromDecompositionTheorem) :
    FixedRatioBound :=
  fixedRatio_of_uniformBound (uniformBound_of_decomposition_and_coloring hStructure hColor)

end Vu

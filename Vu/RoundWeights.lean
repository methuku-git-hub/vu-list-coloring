module
public import Vu.RoundScalars
public import Vu.WeightTests
namespace Vu
open Finset
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
  {G : SimpleGraph V} [DecidableRel G.Adj] {D k R : ℕ} {b M η : ℝ}
  (d : Decomposition G D k R b M η) {L : V → Finset C} (s : ColoringState G L k)

/-- Option.none represents the full-neighborhood test. Its coefficient and
index are distinct from any hard test with the same vertex set. -/
@[expose] public def testIndices (x : V) : Finset (Option (Finset V)) :=
  insert none ((d.tests x).image some)

@[expose] public def testSet (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) : Option (Finset V) → Finset V
  | none => G.neighborFinset x
  | some U => U

@[expose] public noncomputable def testCoeff (V : Type*) (a b : ℝ) : Option (Finset V) → ℝ
  | none => 1/a
  | some _ => 1-b

public theorem test_indices_bound (x : V) : (testIndices d x).card ≤ R+1 :=
  card_insert_le .. |>.trans (Nat.add_le_add_right (card_image_le.trans (d.test_count x)) _)

public theorem indexed_test_subset (x : V) (i : Option (Finset V)) (hi : i ∈ testIndices d x) :
    testSet G x i ⊆ G.neighborFinset x := by
  cases i with
  | none => exact subset_refl _
  | some U =>
    have hu : U ∈ d.tests x := by simpa [testIndices] using hi
    intro y hy
    exact (G.mem_neighborFinset _ _).mpr ((d.edge_iff _ _).mpr (Or.inl ((d.tests_cover x y).mpr ⟨U,hu,hy⟩)))

public theorem round_bounds_iff_indexed (a τ K : ℝ) :
    RoundBounds s d.tests a b τ K ↔
    (∀ x c, s.weight x c ≤ K) ∧ ∀ x c, 0 < s.weight x c → ∀ i ∈ testIndices d x,
      ∑ y ∈ testSet G x i, s.weight y c ≤ testCoeff V a b i*k*τ := by
  constructor
  · intro h
    refine ⟨h.1,?_⟩
    rintro x c hc (_|U) hi
    · exact (h.2 x c hc).2
    · exact (h.2 x c hc).1 U (by simpa [testIndices] using hi)
  · rintro ⟨hK,ht⟩
    exact ⟨hK,fun x c hc => ⟨fun U hu => ht x c hc (some U) (by simp [testIndices,hu]),
      ht x c hc none (by simp [testIndices])⟩⟩

@[expose] public noncomputable def markProb (p : ℝ) (c : C) (x : V) := p*s.weight x c/k

/-- The entry B-A_H used in the product update (W2). -/
@[expose] public noncomputable def updateEntry (x y : V) : ℝ := by
  classical exact if d.H.Adj x y then -1 else d.matrix x y

public theorem update_entry_bounds (hM : 0 ≤ M) (x y : V) :
    -1 ≤ updateEntry d x y ∧ updateEntry d x y ≤ M := by
  classical
  by_cases h : d.H.Adj x y
  · simp [updateEntry,h]; linarith
  · simpa [updateEntry,h] using d.entry_bounds x y

public theorem update_edge_value (x y : V) (h : G.Adj x y) : updateEntry d x y = -1 := by
  classical
  rcases (d.edge_iff x y).mp h with hh | hf
  · simp [updateEntry,hh]
  · have hn : ¬d.H.Adj x y := fun hh => d.disjoint_edges x y hh hf
    simp [updateEntry,hn,d.soft x y hf]

@[expose] public noncomputable def preWeight (p cap : ℝ) (c : C) (ω : V → Bool) (x : V) : ℝ :=
  min cap (s.weight x c * Bernoulli.multiplier (markProb s p c) (updateEntry d x) ω)

@[expose] public noncomputable def passes (a ν p τ cap : ℝ) (c : C) (ω : V → Bool) (x : V) : Prop :=
  ∀ i ∈ testIndices d x, ∑ y ∈ testSet G x i, preWeight d s p cap c ω y ≤
    testThreshold (testCoeff V a b i) k τ ν p b

@[expose] public noncomputable def keptWeight (a ν p τ cap : ℝ) (c : C) (ω : V → Bool) (x : V) : ℝ := by
  classical exact if passes d s a ν p τ cap c ω x then preWeight d s p cap c ω x else 0

public theorem kept_weight_bounds (a ν p τ cap : ℝ) (hc : 0 ≤ cap) (hM : 0 ≤ M)
    (c : C) (h₀ : ∀ x, 0 ≤ markProb s p c x) (h₁ : ∀ x, markProb s p c x < 1)
    (hsmall : ∀ x, M*(markProb s p c x/(1-markProb s p c x)) ≤ 1) (ω : V → Bool) (x : V) :
    let pre := preWeight d s p cap c ω x
    let kept := keptWeight d s a ν p τ cap c ω x
    0 ≤ kept ∧ kept ≤ pre ∧ pre ≤ cap := by
  classical
  have hpre : 0 ≤ preWeight d s p cap c ω x := le_min hc (mul_nonneg (s.nonneg x c)
    (Bernoulli.multiplier_nonneg _ _ M h₀ h₁ (update_entry_bounds d hM x) hsmall ω))
  have hcap : preWeight d s p cap c ω x ≤ cap := min_le_left _ _
  by_cases h : passes d s a ν p τ cap c ω x <;> simp [keptWeight,h,hpre,hcap]

public theorem kept_zero_of_old_zero (a ν p τ cap : ℝ) (hcap : 0 ≤ cap) (c : C) (ω : V → Bool)
    (x : V) (h : s.weight x c = 0) : keptWeight d s a ν p τ cap c ω x = 0 := by
  classical
  by_cases hh : passes d s a ν p τ cap c ω x <;> simp [keptWeight,preWeight,hh,h,hcap]

public theorem kept_zero_of_neighbor_mark (a ν p τ cap : ℝ) (hcap : 0 ≤ cap) (c : C) (ω : V → Bool)
    (x y : V) (h : G.Adj x y) (hy : ω y = true) : keptWeight d s a ν p τ cap c ω x = 0 := by
  classical
  have hz : Bernoulli.multiplier (markProb s p c) (updateEntry d x) ω = 0 := by
    apply prod_eq_zero (mem_univ y)
    simp [Bernoulli.factor,hy,update_edge_value d x y h]
  by_cases hh : passes d s a ν p τ cap c ω x <;> simp [keptWeight,preWeight,hh,hz,hcap]
end Vu

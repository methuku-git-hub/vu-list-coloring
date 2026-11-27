module
public import Vu.RevisedRound
public import Vu.RevisedFinish
namespace Vu.Revised
open Finset
/-- Proposition 3.1. The four structural constants precede the choice of η. -/
@[expose] public def GraphDecompositionTheorem : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
  ∃ (a b : ℝ) (R : ℕ) (C : ℝ), (0 < a ∧ a < 1) ∧ (0 < b ∧ b < 1) ∧ 2 ≤ C ∧
  ∀ η : ℝ, 0 < η → ∃ D₀ : ℕ, ∀ D ≥ D₀, ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj], (∀ v, G.degree v ≤ D) →
    let k := ⌊(maxCodegree G : ℝ) + ε * D⌋₊
    a * D ≤ k ∧ k ≤ 2 * D ∧ Nonempty (SignedDecomposition G D k R b C η)

/-- Proposition 3.2. The admissible tolerance η is uniform over all graphs and lists. -/
@[expose] public def ColoringFromDecompositionTheorem : Prop :=
  ∀ (a b : ℝ) (R : ℕ) (C : ℝ), (0 < a ∧ a < 1) → (0 < b ∧ b < 1) → 2 ≤ C →
  ∃ η : ℝ, 0 < η ∧ ∃ D₀ : ℕ, ∀ D ≥ D₀, ∀ (V P : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj], (∀ v, G.degree v ≤ D) →
    ∀ k : ℕ, a * D ≤ k → k ≤ 2 * D → Nonempty (SignedDecomposition G D k R b C η) →
    ∀ L : V → Finset P, (∀ v, (L v).card = k) →
    ∃ f : V → P, (∀ v, f v ∈ L v) ∧ ∀ ⦃x y⦄, G.Adj x y → f x ≠ f y

/-- The deduction on page 8 of the manuscript, with the two
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

public theorem initial_round_bounds {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
    (G : SimpleGraph V) [DecidableRel G.Adj] (L : V → Finset C) (D k R : ℕ) (a b M η : ℝ)
    (d : SignedDecomposition G D k R b M η) (ha : 0 < a) (hdeg : ∀ x, G.degree x ≤ D)
    (hak : a*D ≤ k) (hL : ∀ x, (L x).card = k) :
    RoundBounds (initial_state G L k hL) d.tests a b 1 1 := by
  classical
  have count (U : Finset V) (c : C) : (∑ y ∈ U, (initial_state G L k hL).weight y c) ≤ U.card := by
    exact (sum_le_sum (g := fun _ => (1:ℝ)) (fun y _ => by dsimp [initial_state]; split <;> norm_num)).trans_eq (by simp)
  refine ⟨fun x c => by dsimp [initial_state]; split <;> norm_num,fun x c _ => ⟨?_,?_⟩⟩
  · intro U hu; simpa using (count U c).trans (d.test_size x U hu)
  · apply (count _ _).trans
    rw [SimpleGraph.card_neighborFinset_eq_degree,mul_one,one_div,←div_eq_inv_mul]
    exact (Nat.cast_le (α := ℝ) |>.mpr (hdeg x)).trans ((le_div_iff₀ ha).mpr (by linarith))

/-- Proposition 3.2 from the one-round lemma. The finite palette consists
of exactly those colors appearing in the given lists, with no finiteness
assumed on the type of colors in the Challenge. -/
public theorem coloring_of_round (step : ColoringRoundTheorem) : ColoringFromDecompositionTheorem := by
  classical
  intro a b R C ha hb hC
  let ν := b/32
  let p := a*ν
  have hν : 0 < ν := div_pos hb.1 (by norm_num)
  have hp : 0 < p := mul_pos ha.1 hν
  obtain ⟨n,hn⟩ := exists_last_round a b p ha.1 hb.1 hp
  have hex : ∃ j : ℕ, roundTau b p j/a < 1/8 := ⟨n,lt_of_le_of_lt hn (by norm_num)⟩
  let J := Nat.find hex
  have hstop : roundTau b p J/a ≤ 1/8 := (Nat.find_spec hex).le
  obtain ⟨η,hη,D₀,hstep⟩ := step a b R C ha hb hC J
  refine ⟨η,hη,max 1 D₀,?_⟩
  intro D hD V P _ _ G _ hdeg k hak hk ⟨d⟩ L hL
  let palette := univ.biUnion L
  let embed (x : V) : ↥(L x) ↪ ↥palette := {
    toFun := fun c => ⟨c.val,mem_biUnion.mpr ⟨x,mem_univ _,c.property⟩⟩
    inj' := fun _ _ h => Subtype.ext (congrArg (fun d : ↥palette => d.val) h) }
  let L' (x : V) := (L x).attach.map (embed x)
  have hL' (x : V) : (L' x).card = k := by simp [L',hL]
  have hstate (j : ℕ) (hj : j ≤ J) : ∃ s : ColoringState G L' k,
      RoundBounds s d.tests a b (roundTau b p j) (cap a C ν p j) := by
    induction j with
    | zero =>
      exact ⟨initial_state G L' k hL',by simpa [roundTau,cap] using initial_round_bounds G L' D k R a b C η d ha.1 hdeg hak hL'⟩
    | succ j ih =>
      obtain ⟨s,hs⟩ := ih (Nat.le_of_succ_le hj)
      obtain ⟨s',_,hs'⟩ := hstep D ((le_max_right _ _).trans hD) V (↥palette) G L' k d hdeg hak hk hL' j hj s hs
      exact ⟨s',hs'⟩
  obtain ⟨s,hs⟩ := hstate J le_rfl
  have hposD : 0 < D := (le_max_left 1 _).trans hD
  have hpos : 0 < (k:ℝ) := (mul_pos ha.1 (Nat.cast_pos.mpr hposD)).trans_le hak
  obtain ⟨f,hl,_,hprop⟩ := finish_state G L' k (Nat.cast_pos.mp hpos) s _ _ _ _ _ hs hstop
  refine ⟨fun x => (f x).val,?_,?_⟩
  · intro x
    obtain ⟨c,_,he⟩ := mem_map.mp (hl x)
    change (f x).val ∈ L x
    rw [← he]; exact c.property
  · intro x y hxy he; exact hprop hxy (Subtype.ext he)


public theorem uniform_of_structure (hs : GraphDecompositionTheorem) : UniformBound :=
  uniformBound_of_decomposition_and_coloring hs (coloring_of_round coloring_round)
end Vu.Revised

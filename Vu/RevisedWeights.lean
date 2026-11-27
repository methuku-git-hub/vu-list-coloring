module
public import Vu.RevisedVariance
public import Vu.RoundWeights
namespace Vu.Revised
open Finset

/-- The three signed decomposition conditions of the revised manuscript. -/
public structure SignedDecomposition {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (D k R : ℕ) (b M η : ℝ) where
  tests : V → Finset (Finset V)
  test_count : ∀ x, (tests x).card ≤ R
  test_subset : ∀ x, ∀ U ∈ tests x, U ⊆ G.neighborFinset x
  test_size : ∀ x, ∀ U ∈ tests x, (U.card : ℝ) ≤ (1-b)*k
  beta : V → V → ℝ
  symm : ∀ x y, beta x y = beta y x
  edges : ∀ x y, G.Adj x y → beta x y = -1
  bounds : ∀ x y, -1 ≤ beta x y ∧ beta x y ≤ M
  row_sum : ∀ x, ∑ y, |beta x y| ≤ M*D
  support : ∀ x, (by classical exact (univ.filter (fun y => beta x y ≠ 0)).card) ≤ D^2
  omitted : ∀ T : Finset V, T.card ≤ D → ∃ S : V → Finset V,
    (∀ u ∈ T, S u = ∅ ∨ S u ∈ tests u) ∧ ∀ U ⊆ T, ∀ Y : Finset V, Y.card ≤ D →
      |∑ u ∈ U, ∑ z ∈ Y, (if z ∈ S u then 0 else beta u z)| ≤ η*D^2

variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
  {G : SimpleGraph V} [DecidableRel G.Adj] {D k R : ℕ} {b M η : ℝ}
  (d : SignedDecomposition G D k R b M η) {L : V → Finset C} (s : ColoringState G L k)

@[expose] public def indices (x : V) : Finset (Option (Finset V)) := insert none ((d.tests x).image some)
@[expose] public noncomputable def threshold (m k τ p b ν : ℝ) := m*k*τ*Real.exp (p*(1-b+ν))
@[expose] public noncomputable def raw (p : ℝ) (c : C) (ω : V → Bool) (x : V) :=
  s.weight x c * Bernoulli.multiplier (fun z => activation (markProb s p c z)) (d.beta x) ω
@[expose] public noncomputable def passes (a ν p τ : ℝ) (c : C) (ω : V → Bool) (x : V) : Prop :=
  ∀ i ∈ indices d x, ∑ y ∈ testSet G x i, raw d s p c ω y ≤ threshold (testCoeff V a b i) k τ p b ν
@[expose] public noncomputable def kept (a ν p τ cap : ℝ) (c : C) (ω : V → Bool) (x : V) : ℝ := by
  classical exact if raw d s p c ω x ≤ cap ∧ passes d s a ν p τ c ω x then raw d s p c ω x else 0

public theorem index_subset (x : V) (i : Option (Finset V)) (hi : i ∈ indices d x) : testSet G x i ⊆ G.neighborFinset x := by
  cases i with
  | none => rfl
  | some U => exact d.test_subset x U (by simpa [indices] using hi)
public theorem index_card (x : V) : (indices d x).card ≤ R+1 :=
  (card_insert_le ..).trans (Nat.add_le_add_right (card_image_le.trans (d.test_count x)) _)

public theorem bounds_iff (a τ K : ℝ) : RoundBounds s d.tests a b τ K ↔ (∀ x c, s.weight x c ≤ K) ∧
    ∀ x c, 0 < s.weight x c → ∀ i ∈ indices d x, ∑ y ∈ testSet G x i, s.weight y c ≤ testCoeff V a b i*k*τ := by
  constructor
  · intro h
    refine ⟨h.1,?_⟩; rintro x c hw (_|U) hi
    · exact (h.2 x c hw).2
    · exact (h.2 x c hw).1 U (by simpa [indices] using hi)
  · rintro ⟨hK,ht⟩
    exact ⟨hK,fun x c hc => ⟨fun U hu => ht x c hc (some U) (by simp [indices,hu]),ht x c hc none (by simp [indices])⟩⟩

public theorem kept_bounds (a ν p τ cap : ℝ) (hcap : 0 ≤ cap) (hM : 1 ≤ M) (c : C)
    (hl : ∀ z, 0 ≤ markProb s p c z ∧ markProb s p c z ≤ 1/M) (v : V → Bool) (x : V) :
    0 ≤ raw d s p c v x ∧ 0 ≤ kept d s a ν p τ cap c v x ∧
    kept d s a ν p τ cap c v x ≤ raw d s p c v x ∧ kept d s a ν p τ cap c v x ≤ cap := by
  have hr : 0 ≤ raw d s p c v x := mul_nonneg (s.nonneg _ _) ((two_moments M hM _ _ _ hl (d.bounds x) (d.bounds x)).1 v)
  refine ⟨hr,?_⟩
  unfold kept; split
  next h => exact ⟨hr,le_rfl,h.1⟩
  next => exact ⟨le_rfl,hr,hcap⟩

public theorem kept_zero (a ν p τ cap : ℝ) (c : C) (v : V → Bool) (x : V) (h : s.weight x c=0) :
    kept d s a ν p τ cap c v x = 0 := by unfold kept; split <;> simp [raw,h]
public theorem kept_zero_neighbor (a ν p τ cap : ℝ) (c : C) (v : V → Bool) (x y : V) (h : G.Adj x y) (hv : v y=true) :
    kept d s a ν p τ cap c v x = 0 := by
  have hz : raw d s p c v x = 0 := by
    unfold raw Bernoulli.multiplier
    rw [prod_eq_zero (mem_univ y) (by simp [Bernoulli.factor,hv,d.edges x y h]),mul_zero]
  unfold kept; split <;> simp [hz]

/-- Upper bound for the multiplier after restoring the omitted edge factors. -/
public theorem restore_omissions (lam f : V → ℝ) (S : Finset V) (hM : 1 ≤ M)
    (hl : ∀ z, 0 ≤ lam z ∧ lam z ≤ 1/M) (hf : ∀ z, -1 ≤ f z ∧ f z ≤ M) (he : ∀ z ∈ S, f z = -1) (ω : V → Bool) :
    let p z := activation (lam z)
    let g z := if z ∈ S then 0 else f z
    Bernoulli.multiplier p f ω ≤ Real.exp (∑ z ∈ S, lam z)*Bernoulli.multiplier p g ω := by
  intro p g
  let t z := if z ∈ S then Real.exp (lam z) else 1
  have hfac z : 0 ≤ Bernoulli.factor (p z) (f z) (ω z) := by
    cases hz : ω z
    · simp only [Bernoulli.factor,Bool.false_eq_true,ite_false,p,(activation_odds _ (hl z).1).2.2]
      have hm : 0 < M := by linarith
      linarith only [mul_le_mul_of_nonneg_right (hf z).2 (hl z).1,(le_div_iff₀ hm).mp (hl z).2]
    · simp [Bernoulli.factor]; linarith [(hf z).1]
  have hh : Bernoulli.multiplier p f ω ≤ ∏ z, (t z*Bernoulli.factor (p z) (g z) (ω z)) := by
    apply prod_le_prod₀ (fun z _ => hfac z)
    intro z _
    by_cases hz : z ∈ S
    · cases hv : ω z
      · simpa [p,t,g,hz,he z hz,Bernoulli.factor,(activation_odds _ (hl z).1).2.2,add_comm] using Real.add_one_le_exp (lam z)
      · simp [t,g,hz,he z hz,Bernoulli.factor,(Real.exp_pos _).le]
    · simp [t,g,hz]
  apply hh.trans_eq
  rw [prod_mul_distrib]
  congr 1
  simp [t,←Real.exp_sum]
end Vu.Revised

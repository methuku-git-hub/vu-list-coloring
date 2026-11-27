module
public import Vu.RoundMatrices
public import Vu.RoundScalars
namespace Vu
open Finset
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
  {G : SimpleGraph V} [DecidableRel G.Adj] {D k R : ℕ} {a b M η : ℝ}
  (d : Decomposition G D k R b M η) {L : V → Finset C} (s : ColoringState G L k)

/-- Uniform elementary estimates on the odds of an individual mark. -/
public theorem mark_odds_bounds (ν M t : ℝ) (hν : 0 < ν) (hM : 0 ≤ M) (ht : 0 ≤ t)
    (hh : t ≤ 1/2) (htν : t ≤ ν/2) (htM : 2*M*t ≤ 1) :
    t < 1 ∧ t/(1-t) ≤ 2*t ∧ t/(1-t) ≤ (1+ν)*t ∧ M*(t/(1-t)) ≤ 1 := by
  have hden : 0 < 1-t := by linarith
  have h1 : t/(1-t) ≤ 2*t := (div_le_iff₀ hden).mpr (by nlinarith [mul_nonneg ht (sub_nonneg.mpr hh)])
  have h2 : 1/(1-t) ≤ 1+ν := (div_le_iff₀ hden).mpr (by nlinarith [mul_le_mul_of_nonneg_right hh hν.le])
  refine ⟨by linarith,h1,?_,?_⟩
  · simpa [div_eq_mul_inv,mul_comm] using mul_le_mul_of_nonneg_right h2 ht
  · linarith only [mul_le_mul_of_nonneg_left h1 hM,htM]

/-- Lemma 6.1 on the current graph and its actual full update matrix. -/
public theorem preweight_expectation (p ν K : ℝ) (hp : 0 < p) (hν : 0 < ν) (ha : 0 < a)
    (hK : 0 < K) (hM : 1 ≤ M) (hD : 0 < D) (hdeg : ∀ x, G.degree x ≤ D)
    (hw : ∀ x c, s.weight x c ≤ K) (c : C)
    (h₀ : ∀ x, 0 ≤ markProb s p c x) (h₁ : ∀ x, markProb s p c x < 1)
    (hv : ∀ x, markProb s p c x/(1-markProb s p c x) ≤ 2*p*K/(a*D)) (x : V) :
    s.weight x c-ν*p/8 ≤ Bernoulli.expect (markProb s p c)
      (fun ω => preWeight d s p (clipCap a M ν p K) c ω x) := by
  let θ := 2*p*K*(M+1)^2/a
  let vmax := 2*p*K/(a*D)
  have hvp : 0 ≤ vmax := by dsimp [vmax]; positivity
  have hvar := update_variance_row d hM hdeg _ vmax hv hvp x
  have hscale : (M+1)^2*D*vmax = θ := by dsimp [θ,vmax]; field_simp <;> ring
  rw [hscale] at hvar
  have hcp : 0 < clipCap a M ν p K := by dsimp [clipCap]; positivity
  apply le_trans _ (Bernoulli.clipped_weight_lower _ (updateEntry d x) h₀ h₁ (s.weight x c) θ _ hcp hvar)
  apply sub_le_sub_left
  apply (div_le_iff₀ hcp).mpr
  have he : ν*p/8 * clipCap a M ν p K = K^2*Real.exp θ := by
    dsimp [clipCap,θ]; field_simp
  rw [he]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (s.nonneg _ _) (hw x c) 2) (Real.exp_pos _).le

/-- The single-test estimate in Lemma 6.2 for the actual update on a state
satisfying (I2). Its explicit right side is proportional to η². -/
public theorem state_test_tail (p ν τ K cap : ℝ) (ha : 0 < a) (ha₁ : a < 1) (hb : 0 < b) (hb₁ : b < 1)
    (hp : 0 < p) (hν : 0 < ν) (hτ : 0 < τ) (hK : 0 < K) (hM : 1 ≤ M) (hη : 0 ≤ η)
    (hD : 0 < D) (hak : a*D ≤ k) (hdeg : ∀ x, G.degree x ≤ D)
    (hbounds : RoundBounds s d.tests a b τ K) (x : V) (c : C) (hw : 0 < s.weight x c)
    (i : Option (Finset V)) (hi : i ∈ testIndices d x)
    (h₀ : ∀ y, 0 ≤ markProb s p c y) (h₁ : ∀ y, markProb s p c y < 1)
    (hsmall : ∀ y, M*(markProb s p c y/(1-markProb s p c y)) ≤ 1)
    (hνp : ∀ y, markProb s p c y/(1-markProb s p c y) ≤ (1+ν)*markProb s p c y)
    (hv : ∀ y, markProb s p c y/(1-markProb s p c y) ≤ 2*p*K/(a*D)) :
    let θ := 2*p*K*(M+1)^2/a
    let g := ν*p*(1-b)*a*τ
    Bernoulli.prob (markProb s p c) (fun ω => testThreshold (testCoeff V a b i) k τ ν p b <
      ∑ y ∈ testSet G x i, preWeight d s p cap c ω y) ≤
      (Real.exp θ*(8*p*K^3/a))*η^2/g^2 := by
  classical
  intro θ g
  let T := testSet G x i
  let m := testCoeff V a b i
  let W := m*k*τ
  let g₁ := ν*p*W
  let vmax := 2*p*K/(a*D)
  let π := markProb s p c
  let o := p*(1-b)*τ
  have hd' : (0:ℝ) < D := Nat.cast_pos.mpr hD
  have hk' : (0:ℝ) < k := (mul_pos ha hd').trans_le hak
  have hm : 1-b ≤ m := by
    cases i with
    | none => dsimp [m,testCoeff]; apply le_trans (by linarith : 1-b ≤ 1); exact (le_div_iff₀ ha).mpr (by linarith)
    | some U => exact le_rfl
  have hmpos : 0 < m := (sub_pos.mpr hb₁).trans_le hm
  have hW : 0 < W := mul_pos (mul_pos hmpos hk') hτ
  have hg : 0 < g := by dsimp [g]; positivity
  have hg₁ : 0 < g₁ := mul_pos (mul_pos hν hp) hW
  have hscale : g*D ≤ g₁ := by
    have h := mul_le_mul hm hak (mul_nonneg ha.le hd'.le) hmpos.le
    dsimp only [g,g₁,W]; linarith only [mul_le_mul_of_nonneg_right h (mul_nonneg (mul_nonneg hν.le hp.le) hτ.le)]
  have hT : T.card ≤ D := (card_le_card (indexed_test_subset d x i hi)).trans (by simpa using hdeg x)
  obtain ⟨S,hs,hE,heq,hN⟩ := comparison_for_test d T hT hη
  let B (u : ↥T) := comparisonEntry d S u.val
  let w (u : ↥T) := s.weight u.val c
  have hsum : ∑ u : ↥T, w u ≤ W := by
    rw [sum_coe_sort T (fun y => s.weight y c)]
    exact ((round_bounds_iff_indexed d s a τ K).mp hbounds).2 x c hw i hi
  have ho (u : ↥T) (hw' : 0 < w u) : ∑ y ∈ S u.val, π y ≤ o := by
    rcases hs u u.property with he | hu
    · rw [he,sum_empty]; dsimp [o]; positivity
    · have hh := (hbounds.2 u c hw').1 _ hu
      simp only [π,markProb,←sum_div,←mul_sum]
      apply (div_le_iff₀ hk').mpr
      dsimp [o]; linarith only [mul_le_mul_of_nonneg_left hh hp.le]
  have hvp : 0 ≤ vmax := by dsimp [vmax]; positivity
  have hmat (u : ↥T) : ∑ y, B u y^2*(π y/(1-π y)) ≤ θ := by
    apply (comparison_variance_row d S hM hdeg _ vmax hv hvp u).trans_eq
    dsimp [θ,vmax]; field_simp <;> ring
  letI : Nonempty V := ⟨x⟩
  have htest := Bernoulli.prescribed_test_tail π B (fun u => S u.val) w ν M (2*η*D) θ vmax o W g₁ cap
    hν.le hvp hg₁ h₀ h₁ (fun u => s.nonneg _ _) hsum ho
    (fun u => hE u u.property) (fun u => comparison_bounds d S hM u) hsmall hνp hv hmat
    (fun f => by
      rw [sum_coe_sort T (fun y => (∑ z, comparisonEntry d S y z*f z)^2)]
      exact hN f)
  have hw2 : ∑ u : ↥T, w u^2 ≤ (D:ℝ)*K^2 := by
    apply (sum_le_sum (g := fun _ => K^2) (fun (u : ↥T) _ => pow_le_pow_left₀ (s.nonneg u.val c) (hbounds.1 u.val c) 2)).trans
    simpa using mul_le_mul_of_nonneg_right (Nat.cast_le (α := ℝ) |>.mpr hT) (sq_nonneg K)
  have htail : Bernoulli.prob π (fun ω => testThreshold m k τ ν p b < ∑ y ∈ T, preWeight d s p cap c ω y) ≤
      (Real.exp θ*vmax*(2*η*D)^2*∑ u : ↥T, w u^2)/g₁^2 := by
    apply le_trans _ htest
    apply Bernoulli.prob_mono _ h₀ (fun y => (h₁ y).le)
    intro ω hh
    convert hh using 1
    · dsimp [W,g₁,m,o,testThreshold]; ring
    · rw [← sum_coe_sort T (fun y => preWeight d s p cap c ω y)]
      apply sum_congr rfl; intro u _
      have eq : (fun y => if y ∈ S u.val then -1 else B u y) = updateEntry d u := funext (heq u u.property)
      simp only [eq,preWeight,w,π]
  apply htail.trans
  have hh := mul_le_mul_of_nonneg_left hw2 (by positivity : 0 ≤ Real.exp θ*vmax*(2*η*D)^2)
  have coeff : 0 ≤ Real.exp θ*(8*p*K^3/a)*η^2 := by positivity
  have hf : Real.exp θ*vmax*(2*η*D)^2*((D:ℝ)*K^2) = Real.exp θ*(8*p*K^3/a)*η^2*(D:ℝ)^2 := by
    dsimp only [vmax]; field_simp; ring
  apply (div_le_div_of_nonneg_right (hh.trans_eq hf) (sq_nonneg g₁)).trans
  have hpow := pow_le_pow_left₀ (mul_nonneg hg.le hd'.le) hscale 2
  rw [div_le_div_iff₀ (sq_pos_of_pos hg₁) (sq_pos_of_pos hg)]
  nlinarith only [mul_le_mul_of_nonneg_left hpow coeff]
end Vu

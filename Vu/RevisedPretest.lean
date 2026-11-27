module
public import Vu.RevisedWeights
namespace Vu.Revised
open Finset
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
  {G : SimpleGraph V} [DecidableRel G.Adj] {D k R : ℕ} {a b M η : ℝ}
  (d : SignedDecomposition G D k R b M η) {L : V → Finset C} (s : ColoringState G L k)

/-- Single-test failure for the raw updated weights of the revision.
The constant is uniform over the state, test and graph order. -/
public theorem raw_test_tail (ν p τ K A : ℝ) (ha : 0 < a) (ha₁ : a < 1) (hb : 0 < b) (hb₁ : b < 1)
    (hν : 0 < ν) (hp : 0 < p) (hτ : 0 < τ) (hτ₁ : τ ≤ 1) (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hM : 1 ≤ M) (hη : 0 ≤ η) (hD : 0 < D) (hak : a*D ≤ k) (hdeg : ∀ y, G.degree y ≤ D)
    (hbounds : RoundBounds s d.tests a b τ K) (x : V) (c : C) (hw : 0 < s.weight x c)
    (i : Option (Finset V)) (hi : i ∈ indices d x)
    (hl : ∀ z, 0 ≤ markProb s p c z ∧ markProb s p c z ≤ 1/M) (hmax : ∀ z, markProb s p c z ≤ A/D) :
    Bernoulli.prob (fun z => activation (markProb s p c z)) (fun ω =>
      threshold (testCoeff V a b i) k τ p b ν < ∑ y ∈ testSet G x i, raw d s p c ω y) ≤
        4*K^2*Real.exp (A*M^2)*A*M*η/(ν*p*(1-b)*a*τ)^2 := by
  classical
  let T := testSet G x i
  let m := testCoeff V a b i
  let W := m*k*τ
  let lam := markProb s p c
  let π z := activation (lam z)
  have hT : T.card ≤ D := (card_le_card (index_subset d x i hi)).trans ((G.card_neighborFinset_eq_degree x).le.trans (hdeg x))
  obtain ⟨S,hS,hrect⟩ := d.omitted T hT
  let f u z := if z ∈ S u then 0 else d.beta u z
  let Z (ω : V → Bool) := ∑ u ∈ T, s.weight u c*Bernoulli.multiplier π (f u) ω
  have hf u z : -1 ≤ f u z ∧ f u z ≤ M := by dsimp only [f]; split <;> first | exact d.bounds u z | constructor <;> linarith
  have hrow u : ∑ z, |f u z| ≤ M*D := by
    apply le_trans _ (d.row_sum u); apply sum_le_sum; intro z _
    dsimp only [f]; split <;> simp [abs_nonneg]
  have hh := omitted_variance T D η A M K lam (fun y => s.weight y c) f hD hT hA hM hK hl hmax
    (fun y => ⟨s.nonneg _ _,hbounds.1 y c⟩) hf hrow hrect
  have hd : (0:ℝ) < D := Nat.cast_pos.mpr hD
  have hk : (0:ℝ) < k := (mul_pos ha hd).trans_le hak
  have hm : 1-b ≤ m := by cases i <;> dsimp only [m,testCoeff] <;> first | rfl | exact (by linarith : 1-b ≤ 1).trans ((le_div_iff₀ ha).mpr (by linarith))
  have hW₀ : (1-b)*a*(D:ℝ)*τ ≤ W := by
    dsimp only [W]; linarith only [mul_le_mul_of_nonneg_right (mul_le_mul hm hak (mul_pos ha hd).le ((sub_pos.mpr hb₁).le.trans hm)) hτ.le]
  have hW : 0 ≤ W := (by positivity : 0 ≤ (1-b)*a*(D:ℝ)*τ).trans hW₀
  have hE : Bernoulli.expect π Z ≤ W := hh.1.le.trans ((bounds_iff d s a τ K).mp hbounds |>.2 x c hw i hi)
  let scale := Real.exp (p*(1-b))
  have hr (v : V → Bool) (y : V) (hy : y ∈ T) : raw d s p c v y ≤ scale*(s.weight y c*Bernoulli.multiplier π (f y) v) := by
    by_cases hzero : s.weight y c=0
    · simp [raw,hzero]
    have hey z (hz : z ∈ S y) : d.beta y z = -1 := by
      rcases hS y hy with he|he
      · simp [he] at hz
      · exact d.edges y z ((G.mem_neighborFinset y z).mp (d.test_subset y _ he hz))
    have hlS : ∑ z ∈ S y, lam z ≤ p*(1-b) := by
      rcases hS y hy with he|he
      · rw [he,sum_empty]; positivity
      · have hsum := (hbounds.2 y c (lt_of_le_of_ne (s.nonneg _ _) (Ne.symm hzero))).1 _ he
        simp only [lam,markProb,←sum_div,←mul_sum]
        apply (div_le_iff₀ hk).mpr
        linarith only [mul_le_mul_of_nonneg_left hsum hp.le,mul_le_mul_of_nonneg_left hτ₁ (mul_nonneg (mul_pos hp (sub_pos.mpr hb₁)).le hk.le)]
    have hx := restore_omissions lam (d.beta y) (S y) hM hl (d.bounds y) hey v
    have hn := (two_moments M hM lam (f y) (f y) hl (hf y) (hf y)).1 v
    exact (mul_le_mul_of_nonneg_left (hx.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hlS) hn)) (s.nonneg _ _)).trans_eq (by ring)
  let g := ν*p*(1-b)*a*τ
  have hg : 0 < g := by dsimp [g]; positivity
  have hbnd := Bernoulli.chebyshev π (fun z => (activation_odds _ (hl z).1).1) (fun z => (activation_odds _ (hl z).1).2.1.le) Z (mul_pos hg hd)
  apply le_trans _ (hbnd.trans ?_)
  · apply Bernoulli.prob_mono π (fun z => (activation_odds _ (hl z).1).1) (fun z => (activation_odds _ (hl z).1).2.1.le)
    intro v hv
    have hsum := sum_le_sum (fun y hy => hr v y hy)
    rw [←mul_sum] at hsum
    have hx : scale*(Real.exp (ν*p)*W) < scale*Z v := by
      apply lt_of_eq_of_lt _ (hv.trans_le hsum)
      dsimp [threshold,scale,W,m]; rw [←mul_assoc,←Real.exp_add,mul_comm (Real.exp _)]; congr 2 <;> ring
    have hz := (mul_lt_mul_iff_right₀ (Real.exp_pos _)).mp hx
    linarith only [hz,hE,mul_le_mul_of_nonneg_right (Real.add_one_le_exp (ν*p)) hW,
      mul_le_mul_of_nonneg_left hW₀ (mul_pos hν hp).le,show g=ν*p*(1-b)*a*τ from rfl]
  · apply (div_le_div_of_nonneg_right hh.2 (sq_nonneg _)).trans_eq
    change _/(g*D)^2 = _/g^2
    field_simp <;> ring
end Vu.Revised

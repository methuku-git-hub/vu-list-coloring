module
public import Vu.RevisedPretest
public import Vu.SimultaneousRound
namespace Vu.Revised
open Finset
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
  {G : SimpleGraph V} [DecidableRel G.Adj] {D k R : ℕ} {a b M η : ℝ}
  (d : SignedDecomposition G D k R b M η) {L : V → Finset C} (s : ColoringState G L k)

/-- Expectation after discarding an oversize entry or an entry failing
any of the raw-weight tests. This proves the loss used in Lemma 6.3. -/
public theorem retained_mean (ν p τ K cap A σ : ℝ) (hc : 0 < cap) (hM : 1 ≤ M) (hD : 0 < D)
    (hK : 0 ≤ K) (hA : 0 ≤ A) (hσ : 0 ≤ σ) (c : C) (x : V)
    (hweight : s.weight x c ≤ K) (hνp : 0 ≤ ν*p)
    (hl : ∀ z, 0 ≤ markProb s p c z ∧ markProb s p c z ≤ 1/M)
    (hmax : ∀ z, markProb s p c z ≤ A/D) (hcut : K^2*Real.exp (A*M^2)/cap ≤ ν*p/8)
    (hcost : cap*((R:ℝ)+1)*σ ≤ ν*p/8)
    (htests : 0 < s.weight x c → ∀ i ∈ indices d x,
      Bernoulli.prob (fun z => activation (markProb s p c z)) (fun ω => threshold (testCoeff V a b i) k τ p b ν <
        ∑ y ∈ testSet G x i, raw d s p c ω y) ≤ σ) :
    let π z := activation (markProb s p c z)
    let μ := markLaw π (fun z => (activation_odds _ (hl z).1).1) (fun z => (activation_odds _ (hl z).1).2.1.le)
    s.weight x c-ν*p/4 ≤ μ.mean (fun ω => kept d s a ν p τ cap c ω x) := by
  classical
  intro π μ
  by_cases hw : 0 < s.weight x c
  swap
  · have hz := le_antisymm (le_of_not_gt hw) (s.nonneg _ _)
    simp_rw [kept_zero d s a ν p τ cap c _ x hz]
    rw [hz,FiniteLaw.mean_const]; linarith
  let X := Bernoulli.multiplier π (d.beta x)
  let Y := fun ω => raw d s p c ω x
  have hx : μ.mean X = 1 := Bernoulli.expect_multiplier _ _ (fun z => (activation_odds _ (hl z).1).2.1)
  have hy : μ.mean Y = s.weight x c := by dsimp [Y,raw]; rw [FiniteLaw.mean_smul]; change _*μ.mean X = _; rw [hx,mul_one]
  have hd : (0:ℝ) < D := Nat.cast_pos.mpr hD
  have hvar : (∑ z, (d.beta x z)^2*(π z/(1-π z))) ≤ A*M^2 := by
    have hpoint z : (d.beta x z)^2*(π z/(1-π z)) ≤ (A/D*M)*|d.beta x z| := by
      dsimp only [π]; rw [(activation_odds _ (hl z).1).2.2]
      have hab : |d.beta x z| ≤ M := abs_le.mpr ⟨by linarith [(d.bounds x z).1],(d.bounds x z).2⟩
      calc _ = (markProb s p c z*|d.beta x z|)*|d.beta x z| := by rw [mul_assoc,←sq,sq_abs]; ring
           _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul (hmax z) hab (abs_nonneg _) (div_nonneg hA hd.le)) (abs_nonneg _)
    apply (sum_le_sum (fun z _ => hpoint z)).trans
    rw [←mul_sum]
    exact (mul_le_mul_of_nonneg_left (d.row_sum x) (by positivity)).trans_eq (by field_simp <;> ring)
  have hxx := (Bernoulli.expect_multiplier_sq_le π (d.beta x) (fun z => (activation_odds _ (hl z).1).1)
    (fun z => (activation_odds _ (hl z).1).2.1)).trans (Real.exp_le_exp.mpr hvar)
  have hy2 : μ.mean (fun ω => Y ω^2) ≤ K^2*Real.exp (A*M^2) := by
    simp only [Y,raw,mul_pow,FiniteLaw.mean_smul]
    exact mul_le_mul (pow_le_pow_left₀ hw.le hweight 2) hxx (μ.mean_nonneg _ (fun _ => sq_nonneg _)) (sq_nonneg _)
  let fail (ω : V → Bool) := ∃ i ∈ indices d x, threshold (testCoeff V a b i) k τ p b ν < ∑ y ∈ testSet G x i, raw d s p c ω y
  have hfail : μ.chance fail ≤ ((R:ℝ)+1)*σ := by
    apply (μ.chance_exists_le _ _).trans
    apply (sum_le_sum (htests hw)).trans
    simp only [sum_const,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast index_card d x) hσ
  let ind (ω : V → Bool) : ℝ := if fail ω then 1 else 0
  have hind : μ.mean ind = μ.chance fail := by
    unfold FiniteLaw.chance; congr 1; funext ω; by_cases h : fail ω <;> simp [ind,h]
  have hpoint (ω : V → Bool) : Y ω-kept d s a ν p τ cap c ω x ≤ (1/cap)*Y ω^2+cap*ind ω := by
    have hn : 0 ≤ cap*ind ω := by apply mul_nonneg hc.le; dsimp only [ind]; split <;> norm_num
    have hy0 : 0 ≤ (1/cap)*Y ω^2 := by positivity
    have he : fail ω ↔ ¬passes d s a ν p τ c ω x := by simp [fail,passes]
    by_cases hcap : Y ω ≤ cap
    · by_cases hf : fail ω
      · simp only [kept,(he.mp hf),and_false,ite_false,sub_zero,ind,if_pos hf,mul_one]; linarith
      · have hpass := not_not.mp (fun ht => hf (he.mpr ht))
        change raw d s p c ω x ≤ cap at hcap
        simp only [kept,hcap,hpass,and_self,ite_true,Y,sub_self]; exact add_nonneg hy0 hn
    · have hcap' : ¬raw d s p c ω x ≤ cap := hcap
      simp only [kept,hcap',false_and,ite_false,sub_zero]
      have hh : cap*Y ω ≤ Y ω^2 := by nlinarith only [mul_nonneg (sub_nonneg.mpr (le_of_not_ge hcap)) (hc.trans (lt_of_not_ge hcap)).le]
      have hy' : Y ω ≤ Y ω^2/cap := (le_div_iff₀ hc).mpr (by linarith only [hh])
      linarith only [hy',hn,show Y ω^2/cap = 1/cap*Y ω^2 by ring]
  have hloss := μ.mean_mono hpoint
  rw [FiniteLaw.mean_sub,FiniteLaw.mean_add,FiniteLaw.mean_smul,FiniteLaw.mean_smul,hy,hind] at hloss
  have hh := mul_le_mul_of_nonneg_left hy2 (one_div_nonneg.mpr hc.le)
  linarith only [hloss,hcost,hcut,hh,mul_le_mul_of_nonneg_left hfail hc.le,
    show 1/cap*(K^2*Real.exp (A*M^2)) = K^2*Real.exp (A*M^2)/cap by ring]
end Vu.Revised

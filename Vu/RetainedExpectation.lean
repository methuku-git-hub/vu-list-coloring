module
public import Vu.Pretest
public import Vu.MarkLaw
namespace Vu
open Finset

variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
  {G : SimpleGraph V} [DecidableRel G.Adj] {D k R : ℕ} {a b M η : ℝ}
  (d : Decomposition G D k R b M η) {L : V → Finset C} (s : ColoringState G L k)

/-- Uniform threshold ensuring that all marking probabilities meet the
requirements of the product and restoration estimates. -/
public theorem small_mark_threshold (a p ν K M : ℝ) (ha : 0 < a) (hp : 0 < p) (hν : 0 < ν)
    (hK : 0 < K) (hM : 1 ≤ M) :
    ∃ D₀ : ℕ, ∀ D ≥ D₀, 0 < D ∧ ∀ k : ℕ, a*D ≤ k → ∀ w : ℝ, 0 ≤ w → w ≤ K →
      let t := p*w/k
      0 ≤ t ∧ t < 1 ∧ t ≤ p*K/(a*D) ∧ t ≤ ν*p ∧ M*(t/(1-t)) ≤ 1 ∧
        t/(1-t) ≤ (1+ν)*t ∧ t/(1-t) ≤ 2*p*K/(a*D) := by
  let cut := min (min (1/2:ℝ) (ν/2)) (min (1/(2*M)) (ν*p))
  have hM' : 0 < M := by linarith
  have hc : 0 < cut := lt_min (lt_min (by norm_num) (by positivity)) (lt_min (by positivity) (by positivity))
  refine ⟨max 1 ⌈p*K/(a*cut)⌉₊,?_⟩
  intro D hD
  have hd : 0 < D := (le_max_left ..).trans hD
  refine ⟨hd,?_⟩
  intro k hka w hw hcap t
  have hd' : 0 < (D:ℝ) := Nat.cast_pos.mpr hd
  have hak := mul_pos ha hd'
  have hk := hak.trans_le hka
  have ht : t ≤ p*K/(a*D) := div_le_div₀ (mul_nonneg hp.le hK.le) (mul_le_mul_of_nonneg_left hcap hp.le) hak hka
  have hD' := (Nat.le_ceil (p*K/(a*cut))).trans (Nat.cast_le.mpr ((le_max_right ..).trans hD))
  have hcut : p*K/(a*D) ≤ cut := (div_le_iff₀ hak).mpr (by linarith only [(div_le_iff₀ (mul_pos ha hc)).mp hD'])
  have htc := ht.trans hcut
  have h1 : cut ≤ 1/2 := (min_le_left ..).trans (min_le_left ..)
  have h2 : cut ≤ ν/2 := (min_le_left ..).trans (min_le_right ..)
  have h3 : cut ≤ 1/(2*M) := (min_le_right ..).trans (min_le_left ..)
  have h4 : cut ≤ ν*p := (min_le_right ..).trans (min_le_right ..)
  have h₀ : 0 ≤ t := div_nonneg (mul_nonneg hp.le hw) hk.le
  obtain ⟨h₁,ho,hν',hm⟩ := mark_odds_bounds ν M t hν hM'.le h₀ (htc.trans h1) (htc.trans h2)
    (by linarith only [(le_div_iff₀ (by positivity : 0 < 2*M)).mp (htc.trans h3)])
  exact ⟨h₀,h₁,ht,htc.trans h4,hm,hν',ho.trans ((mul_le_mul_of_nonneg_left ht (by norm_num : (0:ℝ) ≤ 2)).trans_eq (by ring))⟩

/-- Choose one positive η for the pretest at the specified round, valid
also for every smaller positive η. -/
public theorem pretest_tolerance (a b p ν K M τ σ : ℝ) (ha : 0 < a) (hb : b < 1) (hp : 0 < p)
    (hν : 0 < ν) (hK : 0 < K) (hτ : 0 < τ) (hσ : 0 < σ) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η, 0 ≤ η → η ≤ η₀ →
      Real.exp (2*p*K*(M+1)^2/a)*(8*p*K^3/a)*η^2/(ν*p*(1-b)*a*τ)^2 ≤ σ := by
  let c := Real.exp (2*p*K*(M+1)^2/a)*(8*p*K^3/a)
  let g := ν*p*(1-b)*a*τ
  have hc : 0 < c := by dsimp [c]; positivity
  have hg : 0 < g := by dsimp [g]; positivity
  let η₀ := √(σ*g^2/c)
  have hpos : 0 < σ*g^2/c := by positivity
  refine ⟨η₀,Real.sqrt_pos.mpr hpos,?_⟩
  intro η hη hη'
  have hsq := pow_le_pow_left₀ hη hη' 2
  rw [show η₀^2 = σ*g^2/c from Real.sq_sqrt hpos.le] at hsq
  apply (div_le_iff₀ (sq_pos_of_pos hg)).mpr
  change c*η^2 ≤ σ*g^2
  simpa only [mul_comm c] using (le_div_iff₀ hc).mp hsq

/-- After testing all sets at one original list entry, its expected
retained weight loses at most νp/4. -/
public theorem kept_weight_expectation (a ν p τ K cap σ : ℝ) (hcap : 0 ≤ cap) (hσ : 0 ≤ σ)
    (c : C) (h₀ : ∀ y, 0 ≤ markProb s p c y) (h₁ : ∀ y, markProb s p c y ≤ 1)
    (x : V)
    (hpre : s.weight x c-ν*p/8 ≤ Bernoulli.expect (markProb s p c) (fun ω => preWeight d s p cap c ω x))
    (htests : 0 < s.weight x c → ∀ i ∈ testIndices d x, Bernoulli.prob (markProb s p c) (fun ω =>
      testThreshold (testCoeff V a b i) k τ ν p b < ∑ y ∈ testSet G x i, preWeight d s p cap c ω y) ≤ σ)
    (hcost : cap*((R:ℝ)+1)*σ ≤ ν*p/8) (hpν : 0 ≤ ν*p) :
    s.weight x c-ν*p/4 ≤ Bernoulli.expect (markProb s p c) (fun ω => keptWeight d s a ν p τ cap c ω x) := by
  classical
  let μ := markLaw (markProb s p c) h₀ h₁
  by_cases hpos : 0 < s.weight x c
  swap
  · have hz : s.weight x c = 0 := le_antisymm (le_of_not_gt hpos) (s.nonneg x c)
    have he (ω : V → Bool) := kept_zero_of_old_zero d s a ν p τ cap hcap c ω x hz
    change s.weight x c-ν*p/4 ≤ μ.mean _
    simp_rw [he]
    rw [FiniteLaw.mean_const,hz]; linarith
  let bad (i : Option (Finset V)) (ω : V → Bool) : Prop := testThreshold (testCoeff V a b i) k τ ν p b <
      ∑ y ∈ testSet G x i, preWeight d s p cap c ω y
  let ind i (ω : V → Bool) : ℝ := if bad i ω then 1 else 0
  let tests := testIndices d x
  have loss (ω : V → Bool) : preWeight d s p cap c ω x-keptWeight d s a ν p τ cap c ω x ≤
      cap*∑ i ∈ tests, ind i ω := by
    by_cases h : passes d s a ν p τ cap c ω x
    · simp only [keptWeight,if_pos h,sub_self]
      apply mul_nonneg hcap (sum_nonneg (fun i _ => ?_)); dsimp [ind]; split <;> norm_num
    · have hf : ∃ i ∈ tests, bad i ω := by simpa only [passes,not_forall,not_le,exists_prop,tests,bad] using h
      obtain ⟨i,hi,hb⟩ := hf
      have h1 : 1 ≤ ∑ i ∈ tests, ind i ω := by
        simpa [ind,hb] using single_le_sum (f := fun j => ind j ω) (fun j _ => by dsimp [ind]; split <;> norm_num) hi
      simp only [keptWeight,if_neg h,sub_zero]
      exact (min_le_left _ _).trans (by simpa using mul_le_mul_of_nonneg_left h1 hcap)
  have hh := μ.mean_mono loss
  rw [FiniteLaw.mean_sub,FiniteLaw.mean_smul,FiniteLaw.mean_sum_finset] at hh
  have hind (i : Option (Finset V)) (hi : i ∈ tests) : μ.mean (ind i) ≤ σ := by
    apply le_trans _ (htests hpos i hi)
    apply Bernoulli.expect_mono _ h₀ h₁
    intro ω
    by_cases h : bad i ω <;> simp [ind,bad] at h ⊢ <;> simp [h]
  have hs : (∑ i ∈ tests, μ.mean (ind i)) ≤ ((R:ℝ)+1)*σ := by
    apply (sum_le_sum hind).trans
    simp only [sum_const,nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ hσ
    exact_mod_cast test_indices_bound d x
  change s.weight x c-ν*p/8 ≤ μ.mean _ at hpre
  change s.weight x c-ν*p/4 ≤ μ.mean _
  linarith only [hh, hpre, mul_le_mul_of_nonneg_left hs hcap, hcost]
end Vu

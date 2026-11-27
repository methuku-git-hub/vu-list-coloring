module
public import Vu.SimultaneousRound
namespace Vu
open Finset

private def RoundStep (a b M : ℝ) (R j : ℕ) (η : ℝ) (D : ℕ) : Prop :=
  let ν := roundNu b
  let p := a*ν
  ∀ (V P : Type) [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P]
    (G : SimpleGraph V) [DecidableRel G.Adj] (L : V → Finset P) (k : ℕ)
    (d : Decomposition G D k R b M η), (∀ x, G.degree x ≤ D) → a*D ≤ k → k ≤ 2*D →
    (∀ x, (L x).card = k) → ∀ s : ColoringState G L k,
    RoundBounds s d.tests a b (roundTau b p j) (roundCap a M ν p j) →
    ∃ s' : ColoringState G L k, (∀ x c, s.color x = some c → s'.color x = some c) ∧
      RoundBounds s' d.tests a b (roundTau b p (j+1)) (roundCap a M ν p (j+1))

private theorem single_round (a b M : ℝ) (R j : ℕ) (ha : 0 < a) (ha₁ : a < 1)
    (hb : 0 < b) (hb₁ : b < 1) (hM : 1 ≤ M) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∃ D₀ : ℕ, ∀ η, 0 < η → η ≤ η₀ → ∀ D ≥ D₀, RoundStep a b M R j η D := by
  classical
  let ν := roundNu b
  let p := a*ν
  let τ := roundTau b p j
  let K := roundCap a M ν p j
  let cap := clipCap a M ν p K
  obtain ⟨hν,hν₁,_⟩ := round_nu_bounds hb
  have hp : 0 < p := mul_pos ha hν
  have hpν : p ≤ ν := (mul_le_mul_of_nonneg_right ha₁.le hν.le).trans_eq (one_mul _)
  have hK : 0 < K := round_cap_pos a M ν p hν hp j
  have hc : 0 < cap := by dsimp only [cap,clipCap]; positivity
  have hτ : 0 < τ := Real.exp_pos _
  have hτ₁ : τ ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have h : 0 ≤ b*p*j := by positivity
    linarith only [h]
  let A := p*K/a
  have hA : 0 ≤ A := (div_pos (mul_pos hp hK) ha).le
  let σ := ν*p/(8*cap*(R+1))
  have hσ : 0 < σ := by dsimp only [σ]; positivity
  have hcost : cap*((R:ℝ)+1)*σ ≤ ν*p/8 := by dsimp only [σ]; apply le_of_eq; field_simp <;> ring
  obtain ⟨η₀,hη₀,hηcut⟩ := pretest_tolerance a b p ν K M τ σ ha hb₁ hp hν hK hτ hσ
  obtain ⟨D₁,hD₁⟩ := small_mark_threshold a p ν K M ha hp hν hK hM
  obtain ⟨κ₂,hκ₂,hu⟩ := uniform_offer_rate a b ν p τ cap A ha ha₁ hb hb₁ hν hp hτ hc.le hA
  let e := ν*p
  let κ₁ := a*(3*e/4)^2/(2*(cap^2+cap*(3*e/4)/3))
  have he : 0 < e := mul_pos hν hp
  have hκ₁ : 0 < κ₁ := by dsimp only [κ₁]; positivity
  let κ := min κ₁ κ₂
  obtain ⟨D₂,hD₂⟩ := round_failure_threshold R κ (lt_min hκ₁ hκ₂)
  refine ⟨η₀,hη₀,max D₁ D₂,?_⟩
  intro η hη hη' D hD V P _ _ _ _ G _ L k d hdeg hak hk₂ hcard s hbounds
  obtain ⟨hd,hmarks⟩ := hD₁ D ((le_max_left ..).trans hD)
  have hk' : (0:ℝ) < k := (mul_pos ha (Nat.cast_pos.mpr hd)).trans_le hak
  have hk : 0 < k := Nat.cast_pos.mp hk'
  have hm (c : P) (y : V) := hmarks k hak (s.weight y c) (s.nonneg y c) (hbounds.1 y c)
  have h₀ c y : 0 ≤ markProb s p c y := (hm c y).1
  have h₁ c y : markProb s p c y < 1 := (hm c y).2.1
  have hsmall c y : M*(markProb s p c y/(1-markProb s p c y)) ≤ 1 := (hm c y).2.2.2.2.1
  have hmax c y : markProb s p c y ≤ A/D := (hm c y).2.2.1.trans_eq (by dsimp [A]; ring)
  have hmark c y : markProb s p c y ≤ ν*p := (hm c y).2.2.2.1
  have ho c y : markProb s p c y/(1-markProb s p c y) ≤ (1+ν)*markProb s p c y := (hm c y).2.2.2.2.2.1
  have hv c y : markProb s p c y/(1-markProb s p c y) ≤ 2*p*K/(a*D) := (hm c y).2.2.2.2.2.2
  let q c := markLaw (markProb s p c) (h₀ c) (fun y => (h₁ c y).le)
  let r := Real.exp (-κ*D)
  have rate {t : ℝ} (ht : κ ≤ t) : Real.exp (-t*D) ≤ r :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg ht) (Nat.cast_nonneg _))
  have htotal (x : V) (hx : s.color x = none) : (FiniteLaw.independent q).chance (badTotal d s a ν p τ cap x) ≤ r := by
    let f (c : P) (v : V → Bool) := keptWeight d s a ν p τ cap c v x
    have hw c v := kept_weight_bounds d s a ν p τ cap hc.le (zero_le_one.trans hM) c (h₀ c) (h₁ c) (hsmall c) v x
    have hsum : ∑ c ∈ L x, s.weight x c = k := (sum_subset (subset_univ _) (fun c _ hn => s.outside x c hn)).trans (s.total x hx)
    have hl := retained_total_tail q (L x) f (s.weight x) D k a e cap ha he hc hk hak (hcard x) hsum
      (fun c _ v => ⟨(hw c v).1,(hw c v).2.1.trans (hw c v).2.2⟩) (by
        intro c _
        apply kept_weight_expectation d s a ν p τ K cap σ hc.le hσ.le c (h₀ c) (fun y => (h₁ c y).le) x
          (preweight_expectation d s p ν K hp hν ha hK hM hd hdeg hbounds.1 c (h₀ c) (h₁ c) (hv c) x)
          _ hcost he.le
        intro hpos i hi
        exact (state_test_tail d s p ν τ K cap ha ha₁ hb hb₁ hp hν hτ hK hM hη.le hd hak hdeg hbounds x c hpos i hi
          (h₀ c) (h₁ c) (hsmall c) (ho c) (hv c)).trans (hηcut η hη.le hη'))
    exact hl.2.trans (rate (min_le_left ..))
  have htests (x : V) (c : P) (_ : 0 < s.weight x c) (i) (hi : i ∈ testIndices d x) :
      (FiniteLaw.independent q).chance (badTest d s a ν p τ cap x c i) ≤ r := by
    have h := hu D k hd hak hk₂ (testCoeff V a b i) (by cases i <;> simp [testCoeff])
    exact (state_offer_tail d s ν p τ K cap A ha hp hpν hν₁ rfl hτ₁ hc.le hA (zero_le_one.trans hM) hk hd
      hdeg hbounds h₀ h₁ hmax hmark hsmall x c i hi h.1).trans (h.2.trans (rate (min_le_right ..)))
  obtain ⟨ω,hω,hgood⟩ := exists_round_marks d s ν p τ cap κ h₀ (fun c y => (h₁ c y).le) hdeg hk₂
    (hD₂ D ((le_max_right ..).trans hD))
    (round_vertex_failure d s ν p τ cap r (Real.exp_pos _).le q hcard htotal htests)
  apply state_of_successful_marks d s ha ha₁ hb hb₁ (zero_le_one.trans hM) hk j ω hω h₀ h₁ hsmall
  · intro x hx
    have hh : ¬badTotal d s a ν p τ cap x ω := fun h => hgood x (Or.inl ⟨hx,h⟩)
    have hlist := le_of_not_gt hh
    exact hlist.trans (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun c _ _ =>
      (kept_weight_bounds d s a ν p τ cap hc.le (zero_le_one.trans hM) c (h₀ c) (h₁ c) (hsmall c) (ω c) x).1))
  · intro x c hw i hi hpre
    have hc' : c ∈ L x := by by_contra hn; exact hw.ne' (s.outside x c hn)
    exact le_of_not_gt (fun h => hgood x (Or.inr ⟨c,hc',hw,i,hi,hpre,h⟩))

/-- Lemma 5.1. One tolerance and one degree threshold work for every
round preceding the specified finite stopping time. -/
public theorem coloring_round : ColoringRoundTheorem := by
  intro a b R M ha hb hM ν p J
  have allJ (n : ℕ) : ∃ t : ℝ, 0 < t ∧ ∃ N : ℕ, ∀ η, 0 < η → η ≤ t → ∀ D ≥ N, ∀ j < n, RoundStep a b M R j η D := by
    induction n with
    | zero => exact ⟨1,zero_lt_one,0,fun _ _ _ _ _ _ h => (Nat.not_lt_zero _ h).elim⟩
    | succ n ih =>
      obtain ⟨t,ht,N,hprev⟩ := ih
      obtain ⟨u,hu,Q,hnext⟩ := single_round a b M R n ha.1 ha.2 hb.1 hb.2 (by linarith)
      refine ⟨min t u,lt_min ht hu,max N Q,?_⟩
      intro η hη hη' D hD j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj|rfl
      · exact hprev η hη (hη'.trans (min_le_left ..)) D ((le_max_left ..).trans hD) j hj
      · exact hnext η hη (hη'.trans (min_le_right ..)) D ((le_max_right ..).trans hD)
  obtain ⟨t,ht,N,hsteps⟩ := allJ J
  refine ⟨t,ht,N,?_⟩
  intro D hD V C _ _ _ _ G _ L k d hdeg hak hk₂ hcard j hj
  exact hsteps t ht le_rfl D hD j hj V C G L k d hdeg hak hk₂ hcard

end Vu

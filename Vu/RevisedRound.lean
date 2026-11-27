module
public import Vu.RevisedSimultaneous
public import Vu.RevisedStateOffers
public import Vu.RevisedRetention
public import Vu.RevisedSumTail
public import Vu.RevisedOutcome
namespace Vu.Revised
open Finset

@[expose] public def ColoringRoundTheorem : Prop :=
  ∀ (a b : ℝ) (R : ℕ) (C : ℝ), (0 < a ∧ a < 1) → (0 < b ∧ b < 1) → 2 ≤ C →
    let ν := b/32
    let p := a*ν
    ∀ J : ℕ, ∃ η : ℝ, 0 < η ∧ ∃ D₀ : ℕ, ∀ D ≥ D₀, ∀ (V P : Type)
      [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P]
      (G : SimpleGraph V) [DecidableRel G.Adj] (L : V → Finset P) (k : ℕ)
      (d : SignedDecomposition G D k R b C η), (∀ x, G.degree x ≤ D) → a*D ≤ k → k ≤ 2*D →
      (∀ x, (L x).card = k) → ∀ j < J, ∀ s : ColoringState G L k,
      RoundBounds s d.tests a b (roundTau b p j) (Vu.Revised.cap a C ν p j) →
      ∃ s' : ColoringState G L k, (∀ x c, s.color x = some c → s'.color x = some c) ∧
        RoundBounds s' d.tests a b (roundTau b p (j+1)) (Vu.Revised.cap a C ν p (j+1))

private def RoundStep (a b M : ℝ) (R j : ℕ) (η : ℝ) (D : ℕ) : Prop :=
  let ν := b/32
  let p := a*ν
  ∀ (V P : Type) [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P]
    (G : SimpleGraph V) [DecidableRel G.Adj] (L : V → Finset P) (k : ℕ)
    (d : SignedDecomposition G D k R b M η), (∀ x, G.degree x ≤ D) → a*D ≤ k → k ≤ 2*D →
    (∀ x, (L x).card = k) → ∀ s : ColoringState G L k,
    RoundBounds s d.tests a b (roundTau b p j) (Vu.Revised.cap a M ν p j) →
    ∃ s' : ColoringState G L k, (∀ x c, s.color x = some c → s'.color x = some c) ∧
      RoundBounds s' d.tests a b (roundTau b p (j+1)) (Vu.Revised.cap a M ν p (j+1))

private theorem single_round (a b M : ℝ) (R j : ℕ) (ha : 0 < a) (ha₁ : a < 1)
    (hb : 0 < b) (hb₁ : b < 1) (hM : 1 ≤ M) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∃ D₀ : ℕ, ∀ η, 0 < η → η ≤ η₀ → ∀ D ≥ D₀, RoundStep a b M R j η D := by
  classical
  let ν := b/32
  let p := a*ν
  let τ := roundTau b p j
  let K := Vu.Revised.cap a M ν p j
  let cap := cutoff a M ν p K
  have hν : 0 < ν := by dsimp [ν]; positivity
  have hν₁ : ν ≤ 1/32 := by dsimp [ν]; linarith
  have hp : 0 < p := mul_pos ha hν
  have hpν : p ≤ ν := (mul_le_mul_of_nonneg_right ha₁.le hν.le).trans_eq (one_mul _)
  have hK : 0 < K := cap_pos a M ν p j
  have hc : 0 < cap := hK.trans_le (le_max_left ..)
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
  let g := ν*p*(1-b)*a*τ
  let B := 4*K^2*Real.exp (A*M^2)*A*M
  have hg : 0 < g := by dsimp only [g]; positivity
  have hA' : 0 < A := div_pos (mul_pos hp hK) ha
  have hB : 0 < B := by dsimp only [B]; positivity
  let η₀ := σ*g^2/B
  have hη₀ : 0 < η₀ := div_pos (mul_pos hσ (sq_pos_of_pos hg)) hB
  have hηcut η (h : η ≤ η₀) : B*η/g^2 ≤ σ := (div_le_iff₀ (sq_pos_of_pos hg)).mpr
    (by linarith only [(le_div_iff₀ hB).mp h])
  obtain ⟨D₁,hD₁⟩ := small_mark_threshold a p ν K M ha hp hν hK hM
  obtain ⟨κ₂,hκ₂,hu⟩ := offer_rate a b ν p τ cap A ha ha₁ hb hb₁ hν hp hτ hA
  let e := ν*p
  let κ₁ := a*(3*e/4)^2/(2*cap^2)
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
  have h₁ c y : markProb s p c y ≤ 1/M := by
    let t := markProb s p c y
    have ht : t ≤ t/(1-t) := le_div_self (h₀ c y) (sub_pos.mpr (hm c y).2.1) (sub_le_self _ (h₀ c y))
    apply (le_div_iff₀ (by linarith : 0 < M)).mpr
    rw [mul_comm]
    exact (mul_le_mul_of_nonneg_left ht (zero_le_one.trans hM)).trans (hm c y).2.2.2.2.1
  have hmax c y : markProb s p c y ≤ A/D := (hm c y).2.2.1.trans_eq (by dsimp [A]; ring)
  have hmark c y : markProb s p c y ≤ ν*p := (hm c y).2.2.2.1
  let π c y := activation (markProb s p c y)
  have hzero c y : 0 ≤ π c y := (activation_odds _ (h₀ c y)).1
  have hone c y : π c y ≤ 1 := (activation_odds _ (h₀ c y)).2.1.le
  let q c := markLaw (π c) (hzero c) (hone c)
  let r := Real.exp (-κ*D)
  have rate {t : ℝ} (ht : κ ≤ t) : Real.exp (-t*D) ≤ r :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg ht) (Nat.cast_nonneg _))
  have htotal (x : V) (hx : s.color x = none) : (FiniteLaw.independent q).chance (badTotal d s a ν p τ cap x) ≤ r := by
    let f (c : P) (v : V → Bool) := kept d s a ν p τ cap c v x
    have hw c v := kept_bounds d s a ν p τ cap hc.le hM c (fun z => ⟨h₀ c z,h₁ c z⟩) v x
    have hsum : ∑ c ∈ L x, s.weight x c = k := (sum_subset (subset_univ _) (fun c _ hn => s.outside x c hn)).trans (s.total x hx)
    have hl := retained_total_tail q (L x) f (s.weight x) D k a e cap ha he hc hk hak (hcard x) hsum
      (fun c _ v => ⟨(hw c v).2.1,(hw c v).2.2.2⟩) (by
        intro c _
        apply retained_mean d s ν p τ K cap A σ hc hM hd hK.le hA hσ.le c x (hbounds.1 x c) he.le
          (fun z => ⟨h₀ c z,h₁ c z⟩) (hmax c) (cutoff_cost a M ν p K hν hp hK) hcost
        intro hpos i hi
        exact (raw_test_tail d s ν p τ K A ha ha₁ hb hb₁ hν hp hτ hτ₁ hK.le hA hM hη.le hd hak hdeg hbounds x c hpos i hi
          (fun z => ⟨h₀ c z,h₁ c z⟩) (hmax c)).trans (hηcut η hη'))
    exact hl.2.trans (rate (min_le_left ..))
  have htests (x : V) (c : P) (_ : 0 < s.weight x c) (i) (hi : i ∈ indices d x) :
      (FiniteLaw.independent q).chance (badTest d s a ν p τ cap x c i) ≤ r := by
    have h := hu D k hd hak (testCoeff V a b i) (by cases i <;> simp [testCoeff])
    exact (state_offer_tail d s ν p τ K cap A ha hp hpν hν₁ rfl hτ₁ hc.le hA hM hk hd
      hdeg hbounds h₀ h₁ hmax hmark x c i hi h.1).trans (h.2.trans (rate (min_le_right ..)))
  obtain ⟨ω,hω,hgood⟩ := exists_round_marks d s ν p τ cap κ hzero hone hdeg hk₂
    (hD₂ D ((le_max_right ..).trans hD))
    (round_vertex_failure d s ν p τ cap r (Real.exp_pos _).le q hcard htotal htests)
  apply state_of_successful_marks d s ha ha₁ hb hb₁ hM hk j ω hω h₀ h₁
  · intro x hx
    have hh : ¬badTotal d s a ν p τ cap x ω := fun h => hgood x (Or.inl ⟨hx,h⟩)
    have hlist := le_of_not_gt hh
    exact hlist.trans (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun c _ _ =>
      (kept_bounds d s a ν p τ cap hc.le hM c (fun z => ⟨h₀ c z,h₁ c z⟩) (ω c) x).2.1))
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

end Vu.Revised

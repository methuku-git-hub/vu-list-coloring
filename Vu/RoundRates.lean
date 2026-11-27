module
public import Vu.StateOffers
namespace Vu

/-- A single exponential rate works for both the full-neighborhood test
and every hard-neighborhood test, independently of the graph. -/
public theorem uniform_offer_rate (a b ν p τ cap A : ℝ) (ha : 0 < a) (ha₁ : a < 1)
    (hb : 0 < b) (hb₁ : b < 1) (hν : 0 < ν) (hp : 0 < p) (hτ : 0 < τ)
    (hc : 0 ≤ cap) (hA : 0 ≤ A) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (D k : ℕ), 0 < D → a*D ≤ k → k ≤ 2*D →
      ∀ m : ℝ, (m = 1-b ∨ m = 1/a) →
      let l := testThreshold m k τ ν p b
      let u := ν*p*l
      0 < l ∧ Real.exp (-u^2/(2*((1+cap^2*(1+A)*p)*D+cap*A*u/3))) ≤ Real.exp (-κ*D) := by
  let f := τ*(1+ν*p)*Real.exp ((1+ν)*p*(1-b)*τ)
  let lo := ν*p*(1-b)*a*f
  let hi := ν*p*(1/a)*2*f
  let c := 1+cap^2*(1+A)*p
  let den := 2*(c+cap*A*hi/3)
  have hf : 0 < f := by dsimp [f]; positivity
  have hlo : 0 < lo := by dsimp [lo]; positivity
  have hhi : 0 < hi := by dsimp [hi]; positivity
  have hden : 0 < den := by dsimp [den,c]; positivity
  refine ⟨lo^2/den,div_pos (sq_pos_of_pos hlo) hden,?_⟩
  intro D k hD hka hk m hm l u
  have hd : (0:ℝ) < D := Nat.cast_pos.mpr hD
  have hk' : (0:ℝ) < k := (mul_pos ha hd).trans_le hka
  have hbig : 1-b ≤ 1/a := (by linarith : 1-b ≤ 1).trans ((le_div_iff₀ ha).mpr (by linarith))
  have hm' : 1-b ≤ m ∧ m ≤ 1/a := by rcases hm with rfl|rfl <;> exact ⟨by first | rfl | exact hbig, by first | rfl | exact hbig⟩
  have hmpos : 0 < m := (sub_pos.mpr hb₁).trans_le hm'.1
  have ht : l = m*k*f := by dsimp [l,testThreshold,f]; ring
  refine ⟨ht ▸ mul_pos (mul_pos hmpos hk') hf,?_⟩
  have hh : (k:ℝ) ≤ 2*D := by exact_mod_cast hk
  have hub : lo*D ≤ u ∧ u ≤ hi*D := by
    dsimp only [lo,hi,u]; rw [ht]
    constructor
    · linarith only [mul_le_mul_of_nonneg_right (mul_le_mul hm'.1 hka (mul_pos ha hd).le hmpos.le) (mul_pos (mul_pos hν hp) hf).le]
    · linarith only [mul_le_mul_of_nonneg_right (mul_le_mul hm'.2 hh hk'.le (by positivity)) (mul_pos (mul_pos hν hp) hf).le]
  have hu := (mul_pos hlo hd).trans_le hub.1
  have hden' : 0 < 2*(c*D+cap*A*u/3) := by dsimp [c]; positivity
  have hz : 2*(c*D+cap*A*u/3) ≤ den*D := by dsimp only [den]; linarith only [mul_le_mul_of_nonneg_left hub.2 (mul_nonneg hc hA)]
  have hrat := div_le_div₀ (sq_nonneg u) (pow_le_pow_left₀ (mul_pos hlo hd).le hub.1 2) hden' hz
  have he : (lo*(D:ℝ))^2/(den*D) = lo^2/den*D := by field_simp <;> ring
  rw [he] at hrat
  apply Real.exp_le_exp.mpr
  change -u^2/(2*(c*D+cap*A*u/3)) ≤ -(lo^2/den)*D
  rw [neg_div,neg_mul]
  exact neg_le_neg hrat

/-- Degree threshold for the Local Lemma after a union over all colors
and tests at vertices within distance twelve. -/
public theorem round_failure_threshold (R : ℕ) (κ : ℝ) (hκ : 0 < κ) :
    ∃ D₀ : ℕ, ∀ D ≥ D₀, ((D:ℝ)+1)^12*(1+2*D*(R+1))*Real.exp (-κ*D) ≤ 1/4 := by
  let c : ℝ := 2^12*(1+2*((R:ℝ)+1))
  let cut := 4*c*(Nat.factorial 14:ℝ)/κ^14
  refine ⟨max 1 ⌈cut⌉₊,?_⟩
  intro D hD
  have h1 : (1:ℝ) ≤ D := by exact_mod_cast (le_max_left ..).trans hD
  have hd : (0:ℝ) < D := by linarith
  have hcut := (Nat.le_ceil cut).trans (Nat.cast_le (α := ℝ) |>.mpr ((le_max_right ..).trans hD))
  have hexp := Real.pow_div_factorial_le_exp _ (mul_pos hκ hd).le 14
  have hfact : (0:ℝ) < Nat.factorial 14 := by positivity
  have hbound : 4*c*(D:ℝ)^13 ≤ Real.exp (κ*D) := by
    apply le_trans _ hexp
    apply (le_div_iff₀ hfact).mpr
    have hz := mul_le_mul_of_nonneg_right ((div_le_iff₀ (pow_pos hκ 14)).mp hcut) (pow_pos hd 13).le
    linarith only [hz]
  have hpoly : ((D:ℝ)+1)^12*(1+2*D*(R+1)) ≤ c*D^13 := by
    have hs : (D:ℝ)+1 ≤ 2*D := by linarith
    have hr : 1+2*(D:ℝ)*(R+1) ≤ (1+2*((R:ℝ)+1))*D := by linarith
    exact (mul_le_mul (pow_le_pow_left₀ (by positivity) hs 12) hr (by positivity) (by positivity)).trans_eq (by dsimp [c]; ring)
  rw [neg_mul,Real.exp_neg,←div_eq_mul_inv,div_le_iff₀ (Real.exp_pos _)]
  linarith only [hpoly,hbound]
end Vu

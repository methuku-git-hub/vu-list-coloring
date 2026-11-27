module
public import Vu.RoundReduction
public import Vu.Bernstein
namespace Vu

@[expose] public noncomputable def testThreshold (m k τ ν p b : ℝ) :=
  m*k*τ*(1+ν*p)*Real.exp ((1+ν)*p*(1-b)*τ)

public theorem round_nu_bounds {b : ℝ} (hb : 0 < b) :
    0 < roundNu b ∧ roundNu b ≤ 1/200 ∧ 80*roundNu b ≤ b :=
  ⟨lt_min (by positivity) (by norm_num),min_le_right _ _,by dsimp [roundNu]; linarith only [min_le_left (b/80) (1/200:ℝ)]⟩

public theorem round_cap_pos (a C ν p : ℝ) (hν : 0 < ν) (hp : 0 < p) (j : ℕ) :
    0 < roundCap a C ν p j := by
  induction j with
  | zero => exact zero_lt_one
  | succ j ih => dsimp [roundCap,clipCap]; positivity

public theorem round_tau_succ (b p : ℝ) (j : ℕ) :
    roundTau b p (j+1) = roundTau b p j*Real.exp (-b*p/2) := by
  dsimp [roundTau]; rw [←Real.exp_add,Nat.cast_add_one]; congr 1; ring

/-- The normalization cost and the net contraction per good outcome in
the last display of Section 6. -/
public theorem round_contraction (b p ν : ℝ) (hb : 0 < b) (hb₁ : b < 1) (hp : 0 < p)
    (hpν : p ≤ ν) (hν : ν ≤ 1/200) (hνb : 80*ν ≤ b) (j : ℕ) :
    0 < 1-ν*p ∧ 1/(1-ν*p) ≤ 2 ∧
    (1/(1-ν*p))*(1-(1-5*ν)*p)*(1+ν*p)*Real.exp ((1+ν)*p*(1-b)*roundTau b p j) ≤
      Real.exp (-b*p/2) := by
  let x := ν*p
  have hν₀ := hp.trans_le hpν
  have hx : 0 ≤ x := mul_nonneg hν₀.le hp.le
  have hx' : x ≤ 1/2 := by
    have hh := mul_le_mul (hν.trans (by norm_num : (1/200:ℝ) ≤ 1)) (hpν.trans hν) hp.le zero_le_one
    dsimp [x]; linarith
  have hpos : 0 < 1-x := by linarith
  refine ⟨hpos,(div_le_iff₀ hpos).mpr (by linarith),?_⟩
  have hinv : 1/(1-x) ≤ Real.exp (2*x) := by
    have he := bernstein_exp_bound (-2*x) 0 (by linarith) (by norm_num)
    norm_num at he
    have h1 : Real.exp (-(2*x)) ≤ 1-x := by
      nlinarith [mul_nonneg hx (sub_nonneg.mpr hx')]
    rw [Real.exp_neg] at h1
    apply (div_le_iff₀ hpos).mpr
    have hh := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (2*x)).le
    simpa [(Real.exp_pos (2*x)).ne'] using hh
  have hrem : 0 ≤ 1-(1-5*ν)*p := by nlinarith [mul_nonneg hν₀.le hp.le]
  have ht : roundTau b p j ≤ 1 := Real.exp_le_one_iff.mpr (by
    have h := mul_nonneg (mul_nonneg hb.le hp.le) (Nat.cast_nonneg j : (0:ℝ) ≤ j); linarith)
  have he' := (mul_le_mul_of_nonneg_left ht (mul_nonneg (mul_nonneg (by linarith : 0 ≤ 1+ν) hp.le) (by linarith : 0 ≤ 1-b)))
  have last : 2*x+(-(1-5*ν)*p)+x+(1+ν)*p*(1-b)*roundTau b p j ≤ -b*p/2 := by
    dsimp only [x]
    nlinarith only [he',mul_le_mul_of_nonneg_right hνb hp.le,mul_nonneg (mul_nonneg hν₀.le hb.le) hp.le,
      mul_nonneg hν₀.le hp.le]
  have remexp : 1-(1-5*ν)*p ≤ Real.exp (-(1-5*ν)*p) := by linarith only [Real.add_one_le_exp (-(1-5*ν)*p)]
  have hexp : 1+x ≤ Real.exp x := by linarith only [Real.add_one_le_exp x]
  change 1/(1-x)*(1-(1-5*ν)*p)*(1+x)*_ ≤ _
  apply (mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul hinv remexp hrem (Real.exp_pos _).le)
    hexp (by linarith) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)) (Real.exp_pos _).le).trans
  simpa only [←Real.exp_add] using (Real.exp_le_exp.mpr last)
end Vu

module
public import Vu.RevisedWeights
namespace Vu.Revised

@[expose] public noncomputable def cutoff (a M ν p K : ℝ) := max K (8*K^2*Real.exp ((p*K/a)*M^2)/(ν*p))
@[expose] public noncomputable def cap (a M ν p : ℝ) : ℕ → ℝ
  | 0 => 1
  | j+1 => 2*cutoff a M ν p (cap a M ν p j)

public theorem cap_pos (a M ν p : ℝ) (j : ℕ) : 0 < cap a M ν p j := by
  induction j with
  | zero => exact zero_lt_one
  | succ j ih => exact mul_pos (by norm_num) (ih.trans_le (le_max_left ..))

public theorem cutoff_cost (a M ν p K : ℝ) (hν : 0 < ν) (hp : 0 < p) (hK : 0 < K) :
    K^2*Real.exp ((p*K/a)*M^2)/cutoff a M ν p K ≤ ν*p/8 := by
  have hh := (div_le_iff₀ (mul_pos hν hp)).mp (le_max_right K (8*K^2*Real.exp ((p*K/a)*M^2)/(ν*p)))
  apply (div_le_iff₀ (hK.trans_le (le_max_left ..))).mpr
  linarith only [hh]

public theorem contraction (b p ν : ℝ) (hb : 0 < b) (hb₁ : b < 1) (hp : 0 < p)
    (hpν : p ≤ ν) (hν : ν=b/32) :
    0 < 1-ν*p ∧ 1/(1-ν*p) ≤ 2 ∧
    1/(1-ν*p)*((1-(1-4*ν)*p)*Real.exp (p*(1-b+ν))) ≤ Real.exp (-b*p/2) := by
  have hn := hp.trans_le hpν
  have hν₁ : ν ≤ 1/32 := by linarith
  have hsmall : ν*p ≤ 1/2 := by nlinarith only [mul_le_mul hν₁ (hpν.trans hν₁) hp.le (by norm_num : (0:ℝ) ≤ 1/32)]
  have hx := mul_pos hn hp
  have hpos : 0 < 1-ν*p := by linarith
  refine ⟨hpos,(div_le_iff₀ hpos).mpr (by linarith),?_⟩
  have he := bernstein_exp_bound (-(2*(ν*p))) 0 (by linarith) (by norm_num)
  norm_num at he
  have hlow : Real.exp (-(2*(ν*p))) ≤ 1-ν*p := by nlinarith only [he,mul_nonneg hx.le (sub_nonneg.mpr hsmall)]
  have hInv : 1/(1-ν*p) ≤ Real.exp (2*(ν*p)) := by
    apply (div_le_iff₀ hpos).mpr
    have ht := mul_le_mul_of_nonneg_left hlow (Real.exp_pos (2*(ν*p))).le
    rwa [←Real.exp_add,add_neg_cancel,Real.exp_zero] at ht
  have h1 : 1-(1-4*ν)*p ≤ Real.exp (-(1-4*ν)*p) := by linarith only [Real.add_one_le_exp (-(1-4*ν)*p)]
  have hnon : 0 ≤ 1-(1-4*ν)*p := by nlinarith only [hν₁,hpν,hx]
  apply (mul_le_mul hInv (mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le)
    (mul_nonneg hnon (Real.exp_pos _).le) (Real.exp_pos _).le).trans
  rw [←Real.exp_add,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith only [mul_nonneg (by linarith only [hν,hb] : 0 ≤ b/2-7*ν) hp.le]

public theorem offer_rate (a b ν p τ cap A : ℝ) (ha : 0 < a) (ha₁ : a < 1)
    (hb : 0 < b) (hb₁ : b < 1) (hν : 0 < ν) (hp : 0 < p) (hτ : 0 < τ) (hA : 0 ≤ A) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (D k : ℕ), 0 < D → a*D ≤ k → ∀ m : ℝ, (m = 1-b ∨ m = 1/a) →
      let l := threshold m k τ p b ν
      let u := ν*p*l
      0 < l ∧ Real.exp (-u^2/(2*((1+cap^2*(1+A)*p)*D))) ≤ Real.exp (-κ*D) := by
  let scale := τ*Real.exp (p*(1-b+ν))
  let lo := ν*p*(1-b)*a*scale
  let den := 2*(1+cap^2*(1+A)*p)
  have hs : 0 < scale := by dsimp [scale]; positivity
  have hl : 0 < lo := by dsimp [lo]; positivity
  have hd : 0 < den := by dsimp [den]; positivity
  refine ⟨lo^2/den,div_pos (sq_pos_of_pos hl) hd,?_⟩
  intro D k hD hak m hm l u
  have hD' : (0:ℝ) < D := Nat.cast_pos.mpr hD
  have hk := (mul_pos ha hD').trans_le hak
  have hm' : 1-b ≤ m := by rcases hm with rfl|rfl; rfl; exact (by linarith : 1-b ≤ 1).trans ((le_div_iff₀ ha).mpr (by linarith))
  have hpos := (sub_pos.mpr hb₁).trans_le hm'
  have hh : l = m*k*scale := by dsimp [l,threshold,scale]; ring
  refine ⟨hh ▸ mul_pos (mul_pos hpos hk) hs,?_⟩
  have hu : lo*D ≤ u := by
    dsimp only [lo,u]; rw [hh]
    linarith only [mul_le_mul_of_nonneg_right (mul_le_mul hm' hak (mul_pos ha hD').le hpos.le) (mul_pos (mul_pos hν hp) hs).le]
  have hsq := div_le_div_of_nonneg_right (pow_le_pow_left₀ (mul_pos hl hD').le hu 2) (mul_pos hd hD').le
  have hid : (lo*(D:ℝ))^2/(den*D)=lo^2/den*D := by field_simp <;> ring
  rw [hid] at hsq
  apply Real.exp_le_exp.mpr
  rw [neg_div,neg_mul]; apply neg_le_neg
  convert hsq using 2 <;> dsimp [den] <;> ring
end Vu.Revised

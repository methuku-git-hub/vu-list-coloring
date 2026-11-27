module

public import Vu.ProductVariance
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Probabilistic estimates for a single color in Section 6.1. -/
namespace Vu.Bernoulli
open Finset

variable {Z I : Type*} [Fintype Z] [DecidableEq Z] [Fintype I]

public theorem expect_mono (p : Z → ℝ) (hp₀ : ∀ z, 0 ≤ p z) (hp₁ : ∀ z, p z ≤ 1)
    {f g : (Z → Bool) → ℝ} (h : ∀ ω, f ω ≤ g ω) : expect p f ≤ expect p g := by
  apply sum_le_sum
  intro ω _
  apply mul_le_mul_of_nonneg_left (h ω)
  apply prod_nonneg
  intro z _
  cases he : ω z <;> simp only [mass, Bool.false_eq_true, ↓reduceIte]
  · exact sub_nonneg.mpr (hp₁ z)
  · exact hp₀ z

private lemma mass_total (p : Z → ℝ) : ∑ ω : Z → Bool, (∏ z, mass (p z) (ω z)) = 1 := by
  rw [← Fintype.prod_sum]
  apply prod_eq_one
  intro z _
  simp [mass]

public theorem expect_linear (p : Z → ℝ) (A B : ℝ) (f g : (Z → Bool) → ℝ) :
    expect p (fun ω => A * f ω + B * g ω) = A * expect p f + B * expect p g := by
  simp only [expect, mul_add, sum_add_distrib, mul_sum, mul_left_comm]

public theorem expect_cmul (p : Z → ℝ) (A : ℝ) (f : (Z → Bool) → ℝ) :
    expect p (fun ω => A * f ω) = A * expect p f := by
  simp only [expect, mul_sum, mul_left_comm]

public theorem expect_weighted_multipliers (p : Z → ℝ) (w : I → ℝ) (B : I → Z → ℝ)
    (hp : ∀ z, p z < 1) :
    expect p (fun ω => ∑ i, w i * multiplier p (B i) ω) = ∑ i, w i := by
  calc
    _ = ∑ i, expect p (fun ω => w i * multiplier p (B i) ω) := by
      simp only [expect, mul_sum]
      exact sum_comm
    _ = _ := by simp only [expect_cmul, expect_multiplier p _ hp, mul_one]

/-- Probability of an event under the same finite Bernoulli product law. -/
@[expose] public noncomputable def prob (p : Z → ℝ) (E : (Z → Bool) → Prop) : ℝ := by
  classical exact expect p (fun ω => if E ω then 1 else 0)

public theorem prob_mono (p : Z → ℝ) (hp₀ : ∀ z, 0 ≤ p z) (hp₁ : ∀ z, p z ≤ 1)
    {E F : (Z → Bool) → Prop} (h : ∀ ω, E ω → F ω) : prob p E ≤ prob p F := by
  classical
  apply expect_mono p hp₀ hp₁
  intro ω
  by_cases he : E ω
  · simp [he, h ω he]
  · simp [he]; split <;> norm_num

/-- One-sided Chebyshev inequality in the explicit finite product space. -/
public theorem chebyshev (p : Z → ℝ) (hp₀ : ∀ z, 0 ≤ p z) (hp₁ : ∀ z, p z ≤ 1)
    (f : (Z → Bool) → ℝ) {d : ℝ} (hd : 0 < d) :
    prob p (fun ω => expect p f + d < f ω) ≤
      (expect p (fun ω => f ω ^ 2) - (expect p f)^2) / d^2 := by
  classical
  let m := expect p f
  have hcenter : expect p (fun ω => (f ω - m)^2) =
      expect p (fun ω => f ω ^ 2) - m^2 := by
    have hmass := mass_total p
    unfold expect
    simp only [sub_sq, mul_add, mul_sub, sum_add_distrib, sum_sub_distrib]
    simp_rw [show ∀ (q x : ℝ), q * (2 * x * m) = (q * x) * (2 * m) by intros; ring]
    rw [← sum_mul, ← sum_mul, hmass, one_mul]
    change _ - m * (2 * m) + m^2 = _ - m^2
    ring
  apply (le_div_iff₀ (sq_pos_of_pos hd)).mpr
  unfold prob
  change expect p (fun ω => if m + d < f ω then 1 else 0) * d^2 ≤ _
  rw [mul_comm _ (d^2), ← expect_cmul, ← hcenter]
  apply expect_mono p hp₀ hp₁
  intro ω
  by_cases h : m + d < f ω
  · simp only [h, ↓reduceIte, mul_one]
    exact pow_le_pow_left₀ hd.le (by linarith : d ≤ f ω - m) 2
  · simpa [h] using sq_nonneg (f ω - m)

/-- Lemma 6.1 with its constants exposed. If the weighted row second moment
is bounded by `exp L`, clipping at `cap` loses at most `w² exp(L)/cap` in expectation. -/
public theorem clipped_weight_lower (p b : Z → ℝ) (hp₀ : ∀ z, 0 ≤ p z)
    (hp : ∀ z, p z < 1) (w L cap : ℝ) (hc : 0 < cap)
    (hL : ∑ z, b z ^ 2 * (p z / (1 - p z)) ≤ L) :
    w - w^2 * Real.exp L / cap ≤ expect p (fun ω => min cap (w * multiplier p b ω)) := by
  let X := multiplier p b
  have hp₁ z := (hp z).le
  have hX : expect p X = 1 := expect_multiplier p b hp
  have hXX : expect p (fun ω => X ω^2) ≤ Real.exp L :=
    (expect_multiplier_sq_le p b hp₀ hp).trans (Real.exp_le_exp.mpr hL)
  have hcap (u : ℝ) : u - u^2 / cap ≤ min cap u := by
    apply le_min
    · have h : (u - cap) * cap ≤ u^2 := by nlinarith [sq_nonneg (u-cap), sq_nonneg u, sq_nonneg cap]
      have := (le_div_iff₀ hc).mpr h
      linarith
    · exact sub_le_self _ (div_nonneg (sq_nonneg _) hc.le)
  have hpoint (ω) : w * X ω + (-(w^2 / cap)) * (X ω)^2 ≤ min cap (w * X ω) := by
    convert hcap (w * X ω) using 1
    ring
  have hmean := expect_mono p hp₀ hp₁ hpoint
  rw [expect_linear, hX, mul_one] at hmean
  apply le_trans _ hmean
  have hc' := mul_le_mul_of_nonneg_left hXX (div_nonneg (sq_nonneg w) hc.le)
  linarith only [hc', show w^2 * Real.exp L / cap = (w^2 / cap) * Real.exp L by ring,
    neg_mul (w^2 / cap) (expect p fun ω => X ω^2)]

/-- Quantitative Chebyshev step in Lemma 6.2. The gap is a real number in
the same units as the weighted sum; coefficients may already include 1/Δ. -/
public theorem multiplier_test_tail [Nonempty Z] (p : Z → ℝ) (B : I → Z → ℝ)
    (a : I → ℝ) (N L vmax d : ℝ) (hvmax : 0 ≤ vmax) (hd : 0 < d)
    (hp₀ : ∀ z, 0 ≤ p z) (hp : ∀ z, p z < 1) (hv : ∀ z, p z / (1-p z) ≤ vmax)
    (hL : ∀ i, ∑ z, B i z ^ 2 * (p z / (1-p z)) ≤ L)
    (hB : ∀ f : Z → ℝ, ∑ i, (∑ z, B i z * f z)^2 ≤ N^2 * ∑ z, f z^2) :
    prob p (fun ω => (∑ i, a i) + d < ∑ i, a i * multiplier p (B i) ω) ≤
      (Real.exp L * vmax * N^2 * ∑ i, a i^2) / d^2 := by
  let F := fun ω => ∑ i, a i * multiplier p (B i) ω
  have h := chebyshev p hp₀ (fun z => (hp z).le) F hd
  have hmean : expect p F = ∑ i, a i := expect_weighted_multipliers p a B hp
  rw [← hmean]
  exact h.trans (div_le_div_of_nonneg_right
    (variance_le p B a N L vmax hvmax hp₀ hp hv hL hB) (sq_nonneg d))

/-- Restoring the omitted hard neighbors in one row costs at most the
exponential of their total mark probability times `1 + ν`. This comparison
is pointwise, including outcomes where a restored neighbor is marked. -/
public theorem restore_hard_factors (p b : Z → ℝ) (S : Finset Z) (ν C : ℝ)
    (hp₀ : ∀ z, 0 ≤ p z) (hp : ∀ z, p z < 1) (hb : ∀ z, -1 ≤ b z ∧ b z ≤ C)
    (hC : ∀ z, C * (p z / (1-p z)) ≤ 1)
    (hEmpty : ∀ z ∈ S, b z = 0)
    (hsmall : ∀ z ∈ S, p z / (1-p z) ≤ (1+ν) * p z)
    (ω : Z → Bool) :
    multiplier p (fun z => if z ∈ S then -1 else b z) ω ≤
      Real.exp ((1+ν) * ∑ z ∈ S, p z) * multiplier p b ω := by
  classical
  let M (z : Z) := if z ∈ S then Real.exp ((1+ν)*p z) else 1
  have h₁ (z : Z) : 0 ≤ factor (p z) (if z ∈ S then -1 else b z) (ω z) := by
    have hv := div_nonneg (hp₀ z) (sub_pos.mpr (hp z)).le
    by_cases hz : z ∈ S <;> cases hbit : ω z <;> simp [factor, hz]
    · linarith
    · exact (mul_le_mul_of_nonneg_right (hb z).2 hv).trans (hC z)
    · linarith [(hb z).1]
  have h₂ (z : Z) :
      factor (p z) (if z ∈ S then -1 else b z) (ω z) ≤ M z * factor (p z) (b z) (ω z) := by
    by_cases hz : z ∈ S
    · cases hbit : ω z
      · simp [factor, hz, M, hEmpty z hz]
        calc
          _ ≤ Real.exp (p z / (1 - p z)) := by simpa [add_comm] using Real.add_one_le_exp (p z / (1-p z))
          _ ≤ _ := Real.exp_le_exp.mpr (hsmall z hz)
      · simp [factor, hz, M, hEmpty z hz, (Real.exp_pos _).le]
    · simp [M, hz]
  have hprod : (∏ z, M z) = Real.exp ((1+ν) * ∑ z ∈ S, p z) := by
    simp [M, ← Real.exp_sum, mul_sum]
  calc
    _ ≤ ∏ z, (M z * factor (p z) (b z) (ω z)) :=
      prod_le_prod₀ (fun z _ => h₁ z) (fun z _ => h₂ z)
    _ = _ := by rw [prod_mul_distrib, hprod]; rfl

/-- The failure probability for a prescribed test in Lemma 6.2.
`B` is the comparison matrix after omission. On `S i` the true row has
coefficient -1. `W` bounds the old total weight, and `s` bounds the sum
of the mark probabilities omitted in each positive-weight row. -/
public theorem prescribed_test_tail [Nonempty Z]
    (p : Z → ℝ) (B : I → Z → ℝ) (S : I → Finset Z) (w : I → ℝ)
    (ν C N L vmax s W gap cap : ℝ) (hν : 0 ≤ ν) (hvmax : 0 ≤ vmax) (hgap : 0 < gap)
    (hp₀ : ∀ z, 0 ≤ p z) (hp : ∀ z, p z < 1) (hw₀ : ∀ i, 0 ≤ w i)
    (hW : ∑ i, w i ≤ W) (hs : ∀ i, 0 < w i → ∑ z ∈ S i, p z ≤ s)
    (hEmpty : ∀ i, ∀ z ∈ S i, B i z = 0)
    (hb : ∀ i z, -1 ≤ B i z ∧ B i z ≤ C)
    (hC : ∀ z, C * (p z / (1-p z)) ≤ 1)
    (hsmall : ∀ z, p z / (1-p z) ≤ (1+ν) * p z)
    (hv : ∀ z, p z / (1-p z) ≤ vmax)
    (hL : ∀ i, ∑ z, B i z ^ 2 * (p z / (1-p z)) ≤ L)
    (hB : ∀ f : Z → ℝ, ∑ i, (∑ z, B i z * f z)^2 ≤ N^2 * ∑ z, f z^2) :
    let actual := fun i z => if z ∈ S i then -1 else B i z
    prob p (fun ω => Real.exp ((1+ν)*s) * (W+gap) <
      ∑ i, min cap (w i * multiplier p (actual i) ω)) ≤
      (Real.exp L * vmax * N^2 * ∑ i, w i^2) / gap^2 := by
  classical
  dsimp only
  apply le_trans _ (multiplier_test_tail p B w N L vmax gap hvmax hgap hp₀ hp hv hL hB)
  apply prob_mono p hp₀ (fun z => (hp z).le)
  intro ω hexcess
  have hrow (i : I) : min cap (w i * multiplier p (fun z => if z ∈ S i then -1 else B i z) ω) ≤
      Real.exp ((1+ν)*s) * (w i * multiplier p (B i) ω) := by
    apply (min_le_right _ _).trans
    obtain hzero | hpos := (hw₀ i).eq_or_lt
    · simp [← hzero]
    have hrestore := restore_hard_factors p (B i) (S i) ν C hp₀ hp (hb i) hC
      (hEmpty i) (fun z _ => hsmall z) ω
    have hExp := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hs i hpos) (by linarith : 0 ≤ 1+ν))
    have hX := multiplier_nonneg p (B i) C hp₀ hp (hb i) hC ω
    calc
      _ ≤ w i * (Real.exp ((1+ν)*s) * multiplier p (B i) ω) :=
        mul_le_mul_of_nonneg_left (hrestore.trans (mul_le_mul_of_nonneg_right hExp hX)) (hw₀ i)
      _ = _ := by ring
  have hsum := hexcess.trans_le (sum_le_sum (fun i _ => hrow i))
  rw [← mul_sum] at hsum
  exact (add_le_add_left hW gap).trans_lt ((mul_lt_mul_iff_of_pos_left (Real.exp_pos _)).mp hsum)

end Vu.Bernoulli

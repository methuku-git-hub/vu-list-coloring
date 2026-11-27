module

public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Finite Bernoulli product spaces and the variance estimate of Lemma 2.1.
The probability distribution is given explicitly by its masses on bit vectors. -/
namespace Vu
namespace Bernoulli

open Finset

variable {I Z : Type*} [Fintype I] [Fintype Z] [DecidableEq Z]

/-- Mass of one coin outcome. -/
@[expose] public def mass (p : ℝ) (bit : Bool) : ℝ := if bit then p else 1 - p

/-- Expectation on the finite space of independent Bernoulli marks. -/
@[expose] public noncomputable def expect (p : Z → ℝ) (f : (Z → Bool) → ℝ) : ℝ :=
  ∑ ω, (∏ z, mass (p z) (ω z)) * f ω

/-- The marked and unmarked values of the multiplicative update in (W2). -/
@[expose] public noncomputable def factor (p b : ℝ) (bit : Bool) : ℝ :=
  if bit then 1 + b else 1 - b * (p / (1 - p))

/-- Row multiplier for a fixed color. -/
@[expose] public noncomputable def multiplier (p : Z → ℝ) (b : Z → ℝ) (ω : Z → Bool) : ℝ :=
  ∏ z, factor (p z) (b z) (ω z)

public theorem factor_eq (p b : ℝ) (hp : p < 1) (bit : Bool) :
    factor p b bit = 1 + b * ((if bit then 1 else 0) - p) / (1 - p) := by
  have h : 1 - p ≠ 0 := ne_of_gt (sub_pos.mpr hp)
  cases bit
  · simp [factor]
    field_simp
    ring
  · simp [factor]
    field_simp

private theorem expect_prod (p : Z → ℝ) (f : Z → Bool → ℝ) :
    expect p (fun ω => ∏ z, f z (ω z)) =
      ∏ z, ∑ b : Bool, mass (p z) b * f z b := by
  classical
  simp only [expect, Fintype.prod_sum, prod_mul_distrib]

private theorem expect_sum (p : Z → ℝ) (f : I → (Z → Bool) → ℝ) :
    expect p (fun ω => ∑ i, f i ω) = ∑ i, expect p (f i) := by
  simp only [expect, mul_sum]
  exact sum_comm

private theorem expect_const_mul (p : Z → ℝ) (c : ℝ) (f : (Z → Bool) → ℝ) :
    expect p (fun ω => c * f ω) = c * expect p f := by
  simp only [expect, mul_sum, mul_left_comm]

public theorem expect_multiplier (p b : Z → ℝ) (hp : ∀ z, p z < 1) :
    expect p (multiplier p b) = 1 := by
  unfold multiplier
  rw [expect_prod]
  apply prod_eq_one
  intro z _
  have h : 1 - p z ≠ 0 := ne_of_gt (sub_pos.mpr (hp z))
  simp [mass, factor]
  field_simp
  ring

public theorem joint_moment (p a b : Z → ℝ) (hp : ∀ z, p z < 1) :
    expect p (fun ω => multiplier p a ω * multiplier p b ω) =
      ∏ z, (1 + a z * b z * (p z / (1 - p z))) := by
  unfold multiplier
  simp only [← prod_mul_distrib]
  rw [expect_prod p (fun z t => factor (p z) (a z) t * factor (p z) (b z) t)]
  apply prod_congr rfl
  intro z _
  have h : 1 - p z ≠ 0 := ne_of_gt (sub_pos.mpr (hp z))
  simp [mass, factor]
  field_simp
  ring

public theorem expect_multiplier_sq_le (p b : Z → ℝ) (hp₀ : ∀ z, 0 ≤ p z)
    (hp : ∀ z, p z < 1) :
    expect p (fun ω => multiplier p b ω ^ 2) ≤
      Real.exp (∑ z, b z ^ 2 * (p z / (1 - p z))) := by
  simp only [pow_two, joint_moment p b b hp]
  exact Real.prod_one_add_le_exp_sum _ (fun z =>
    mul_nonneg (mul_self_nonneg _) (div_nonneg (hp₀ z) (sub_pos.mpr (hp z)).le))

omit [DecidableEq Z] in
public theorem multiplier_nonneg (p b : Z → ℝ) (C : ℝ)
    (hp₀ : ∀ z, 0 ≤ p z) (hp : ∀ z, p z < 1)
    (hb : ∀ z, -1 ≤ b z ∧ b z ≤ C) (hC : ∀ z, C * (p z / (1 - p z)) ≤ 1)
    (ω : Z → Bool) : 0 ≤ multiplier p b ω := by
  apply prod_nonneg
  intro z _
  cases hbit : ω z
  · simp only [factor, Bool.false_eq_true, ↓reduceIte, sub_nonneg]
    exact (mul_le_mul_of_nonneg_right (hb z).2 (div_nonneg (hp₀ z) (sub_pos.mpr (hp z)).le)).trans (hC z)
  · simpa [factor, add_comm] using (neg_le_iff_add_nonneg.mp (hb z).1)

private theorem sum_weight_square (f : I → ℝ) :
    (∑ i, f i)^2 = ∑ i, ∑ j, f i * f j := by
  rw [pow_two, sum_mul]
  simp only [mul_sum]

omit [Fintype Z] [DecidableEq Z] in
private theorem square_prod_sum (a : I → ℝ) (g : I → Z → ℝ) (S : Finset Z) :
    (∑ i, a i * ∏ z ∈ S, g i z)^2 =
      ∑ i, ∑ j, (a i * a j) * ∏ z ∈ S, (g i z * g j z) := by
  rw [sum_weight_square]
  simp only [prod_mul_distrib]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  ring

/-- Parseval identity for the products, proved by expanding pair moments.
No division by the standard deviation is needed for zero-probability columns. -/
public theorem variance_eq_sum (p : Z → ℝ) (B : I → Z → ℝ)
    (a : I → ℝ) (hp₀ : ∀ z, 0 ≤ p z) (hp : ∀ z, p z < 1) :
    let F := fun ω => ∑ i, a i * multiplier p (B i) ω
    let g := fun i z => B i z * Real.sqrt (p z / (1 - p z))
    expect p (fun ω => F ω ^ 2) - (expect p F)^2 =
      ∑ S ∈ (univ : Finset (Finset Z)).erase ∅, (∑ i, a i * ∏ z ∈ S, g i z)^2 := by
  classical
  dsimp only
  let g := fun i z => B i z * Real.sqrt (p z / (1 - p z))
  have hpair (i j : I) (z : Z) : B i z * B j z * (p z / (1 - p z)) = g i z * g j z := by
    dsimp [g]
    rw [show B i z * √(p z / (1 - p z)) * (B j z * √(p z / (1 - p z))) =
        B i z * B j z * (√(p z / (1 - p z)))^2 by ring]
    rw [Real.sq_sqrt (div_nonneg (hp₀ z) (sub_pos.mpr (hp z)).le)]
  have hfirst : expect p (fun ω => ∑ i, a i * multiplier p (B i) ω) = ∑ i, a i := by
    simp only [expect_sum, expect_const_mul, expect_multiplier p _ hp, mul_one]
  have hsecond : expect p (fun ω => (∑ i, a i * multiplier p (B i) ω)^2) =
      ∑ S : Finset Z, (∑ i, a i * ∏ z ∈ S, g i z)^2 := by
    simp only [sum_weight_square (fun i => a i * multiplier p (B i) _), expect_sum,
      show ∀ (r s t u : ℝ), r * s * (t * u) = (r * t) * (s * u) by intros; ring,
      expect_const_mul, joint_moment p _ _ hp, hpair, prod_one_add, powerset_univ, mul_sum,
      square_prod_sum]
    conv_lhs => enter [2, i]; rw [sum_comm]
    rw [sum_comm]
  rw [hfirst, hsecond, ← sum_erase_add _ (fun S : Finset Z => (∑ i, a i * ∏ z ∈ S, g i z)^2)
    (mem_univ (∅ : Finset Z))]
  simp [g]

/-- Remove one column from every nonempty subset. Summing over all possible
removed columns can only increase the sum of squares. The remaining subsets
sum exactly to the product of the individual second moments. -/
private theorem subset_squares_le [Nonempty Z] (g : I → Z → ℝ) (a : I → ℝ) (K : ℝ)
    (hg : ∀ v : I → ℝ, ∑ z, (∑ i, v i * g i z)^2 ≤ K * ∑ i, v i ^ 2) :
    ∑ S ∈ (univ : Finset (Finset Z)).erase ∅, (∑ i, a i * ∏ z ∈ S, g i z)^2 ≤
      K * ∑ i, a i ^ 2 * ∏ z, (1 + g i z ^ 2) := by
  classical
  let pick (S : Finset Z) := if h : S.Nonempty then h.choose else Classical.ofNonempty
  have hpick {S : Finset Z} (h : S ≠ ∅) : pick S ∈ S := by
    have hs := Finset.nonempty_iff_ne_empty.mpr h
    simpa [pick, hs] using hs.choose_spec
  let index (S : Finset Z) := (S.erase (pick S), pick S)
  let terms (S : Finset Z) (z : Z) := (∑ i, (a i * ∏ t ∈ S, g i t) * g i z)^2
  let sets := (univ : Finset (Finset Z)).erase ∅
  have recover {S : Finset Z} (h : S ∈ sets) : insert (index S).2 (index S).1 = S :=
    Finset.insert_erase (hpick (Finset.mem_erase.mp h).1)
  have embed : Set.InjOn index sets := by
    intro S hS T hT heq
    exact (recover hS).symm.trans ((congrArg (fun p : Finset Z × Z => insert p.2 p.1) heq).trans (recover hT))
  calc
    _ ≤ ∑ p : Finset Z × Z, terms p.1 p.2 := by
      refine sum_le_sum_of_injOn index embed (subset_univ _) ?_ (fun _ _ _ => sq_nonneg _)
      intro S hS
      apply le_of_eq
      unfold terms index
      congr 1
      apply sum_congr rfl
      intro i _
      rw [mul_assoc, prod_erase_mul _ _ (hpick (Finset.mem_erase.mp hS).1)]
    _ = ∑ S : Finset Z, ∑ z, terms S z := Fintype.sum_prod_type _
    _ ≤ ∑ S : Finset Z, K * ∑ i, (a i * ∏ t ∈ S, g i t)^2 := by
      apply sum_le_sum
      intro S _
      exact hg (fun i => a i * ∏ t ∈ S, g i t)
    _ = _ := by
      rw [← mul_sum, sum_comm]
      congr 1
      apply sum_congr rfl
      intro i _
      simp only [mul_pow, ← prod_pow, ← mul_sum, prod_one_add, powerset_univ]

omit [DecidableEq Z] in
/-- Convert a squared Euclidean norm bound on a matrix to the same bound on
its transpose by testing the original inequality against the transpose image. -/
public theorem transpose_bound (B : I → Z → ℝ) (N : ℝ)
    (hB : ∀ f : Z → ℝ, ∑ i, (∑ z, B i z * f z)^2 ≤ N^2 * ∑ z, f z ^ 2)
    (v : I → ℝ) : ∑ z, (∑ i, v i * B i z)^2 ≤ N^2 * ∑ i, v i ^ 2 := by
  let f (z : Z) := ∑ i, v i * B i z
  let s := ∑ z, f z ^ 2
  have hbil : ∑ i, v i * ∑ z, B i z * f z = s := by
    simp only [mul_sum, ← mul_assoc]
    rw [sum_comm]
    apply sum_congr rfl
    intro z _
    rw [← sum_mul]
    exact (pow_two (f z)).symm
  have hCS := sum_mul_sq_le_sq_mul_sq univ v (fun i => ∑ z, B i z * f z)
  rw [hbil] at hCS
  have hsv : 0 ≤ ∑ i, v i ^ 2 := sum_nonneg (fun _ _ => sq_nonneg _)
  have hss : 0 ≤ s := sum_nonneg (fun _ _ => sq_nonneg _)
  have hsq : s ^ 2 ≤ (∑ i, v i ^ 2) * (N ^ 2 * s) :=
    hCS.trans (mul_le_mul_of_nonneg_left (hB f) hsv)
  by_cases hs : s = 0
  · change s ≤ _
    rw [hs]
    exact mul_nonneg (sq_nonneg _) hsv
  · change s ≤ _
    apply (mul_le_mul_iff_of_pos_right (lt_of_le_of_ne hss (Ne.symm hs))).mp
    simpa only [pow_two, mul_assoc, mul_left_comm, mul_comm] using hsq

/-- Variance bound of Lemma 2.1. `vmax` and `L` bound the column odds and
the row sums of squared entries weighted by those odds. The hypothesis on
`N` is the defining inequality for the Euclidean operator norm. -/
public theorem variance_le [Nonempty Z] (p : Z → ℝ) (B : I → Z → ℝ) (a : I → ℝ)
    (N L vmax : ℝ) (hvmax : 0 ≤ vmax) (hp₀ : ∀ z, 0 ≤ p z) (hp : ∀ z, p z < 1)
    (hv : ∀ z, p z / (1 - p z) ≤ vmax)
    (hL : ∀ i, ∑ z, B i z ^ 2 * (p z / (1 - p z)) ≤ L)
    (hB : ∀ f : Z → ℝ, ∑ i, (∑ z, B i z * f z)^2 ≤ N^2 * ∑ z, f z ^ 2) :
    let F := fun ω => ∑ i, a i * multiplier p (B i) ω
    expect p (fun ω => F ω ^ 2) - (expect p F)^2 ≤ Real.exp L * vmax * N^2 * ∑ i, a i ^ 2 := by
  classical
  dsimp only
  rw [variance_eq_sum p B a hp₀ hp]
  let v := fun z => p z / (1 - p z)
  let g := fun i z => B i z * √(v z)
  have hv₀ (z : Z) : 0 ≤ v z := div_nonneg (hp₀ z) (sub_pos.mpr (hp z)).le
  have hgSq (i : I) (z : Z) : g i z ^ 2 = B i z ^ 2 * v z := by
    simp [g, mul_pow, Real.sq_sqrt (hv₀ z)]
  have hg (w : I → ℝ) : ∑ z, (∑ i, w i * g i z)^2 ≤ (vmax * N^2) * ∑ i, w i ^ 2 := by
    calc
      _ = ∑ z, (∑ i, w i * B i z)^2 * v z := by
        apply sum_congr rfl
        intro z _
        simp only [g, ← mul_assoc, ← sum_mul, mul_pow, Real.sq_sqrt (hv₀ z)]
      _ ≤ ∑ z, (∑ i, w i * B i z)^2 * vmax :=
        sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left (hv z) (sq_nonneg _))
      _ ≤ _ := by
        rw [← sum_mul]
        calc
          _ ≤ (N^2 * ∑ i, w i ^ 2) * vmax :=
            mul_le_mul_of_nonneg_right (transpose_bound B N hB w) hvmax
          _ = _ := by ring
  calc
    _ ≤ (vmax * N^2) * ∑ i, a i ^ 2 * ∏ z, (1 + g i z ^ 2) :=
      subset_squares_le g a _ hg
    _ ≤ (vmax * N^2) * ∑ i, a i ^ 2 * Real.exp L := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hvmax (sq_nonneg _))
      apply sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply (Real.prod_one_add_le_exp_sum _ (fun z => sq_nonneg (g i z))).trans
      apply Real.exp_le_exp.mpr
      simpa only [hgSq] using hL i
    _ = _ := by rw [← sum_mul]; ring

end Bernoulli
end Vu

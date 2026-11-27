module
public import Vu.MarkLaw
namespace Vu
open Finset
namespace FiniteLaw
variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]

/-- Product law on a finite family of independent coordinates. -/
@[expose] public noncomputable def independent (q : I → FiniteLaw X) : FiniteLaw (I → X) := by
  classical
  exact ⟨fun a => ∏ i, (q i).mass (a i),fun _ => prod_nonneg (fun i _ => (q i).nonneg _),
    by rw [← Fintype.prod_sum]; simp [FiniteLaw.total]⟩

@[expose] public def determinedBy {Y : Type*} (S : Finset I) (f : (I → X) → Y) : Prop :=
  ∀ a b, (∀ i ∈ S, a i = b i) → f a = f b

public theorem independent_product (q : I → FiniteLaw X) (g : I → X → ℝ) :
    (independent q).mean (fun a => ∏ i, g i (a i)) = ∏ i, (q i).mean (g i) := by
  classical
  simp only [independent,mean,Fintype.prod_sum,prod_mul_distrib]

public theorem coordinate_mean (q : I → FiniteLaw X) (i : I) (g : X → ℝ) :
    (independent q).mean (fun a => g (a i)) = (q i).mean g := by
  classical
  let h (j : I) (v : X) := if j=i then g v else 1
  have h1 (a : I → X) : ∏ j, h j (a j) = g (a i) := by simp [h]
  have hh := independent_product q h
  simp_rw [h1] at hh
  rw [hh,prod_eq_single i]
  · simp [h]
  · intro j _ hji; simp [h,hji,mean_const]
  · simp

/-- Functions of disjoint sets of coordinates factor in expectation.
Swapping the T-coordinates of two independent samples preserves their joint
mass and lets the two functions be evaluated on separate samples. -/
public theorem independent_disjoint (q : I → FiniteLaw X) (S T : Finset I)
    (f g : (I → X) → ℝ) (hf : determinedBy S f) (hg : determinedBy T g) (hd : Disjoint S T) :
    (independent q).mean (fun a => f a*g a) = (independent q).mean f * (independent q).mean g := by
  classical
  let μ := independent q
  let swap (a b : I → X) (i : I) := if i ∈ T then b i else a i
  let e : ((I → X) × (I → X)) ≃ ((I → X) × (I → X)) := {
    toFun := fun ab => (swap ab.1 ab.2,swap ab.2 ab.1)
    invFun := fun ab => (swap ab.1 ab.2,swap ab.2 ab.1)
    left_inv := by intro ab; ext i <;> by_cases hi : i ∈ T <;> simp [swap,hi]
    right_inv := by intro ab; ext i <;> by_cases hi : i ∈ T <;> simp [swap,hi] }
  have hmass (a b : I → X) : μ.mass (swap a b) * μ.mass (swap b a) = μ.mass a * μ.mass b := by
    simp only [μ,independent,←prod_mul_distrib]
    apply prod_congr rfl
    intro i _
    by_cases h : i ∈ T <;> simp [swap,h,mul_comm]
  have hswap (a b : I → X) : f (swap a b) = f a ∧ g (swap a b) = g b := by
    exact ⟨hf _ _ (fun i hi => if_neg (fun ht => disjoint_left.mp hd hi ht)),hg _ _ (fun i hi => if_pos hi)⟩
  let A (ab : (I → X) × (I → X)) := (μ.mass ab.1 * μ.mass ab.2)*(f ab.1*g ab.2)
  let B (ab : (I → X) × (I → X)) := (μ.mass ab.1 * μ.mass ab.2)*(f ab.1*g ab.1)
  have eq : ∑ ab, A ab = ∑ ab, B ab := by
    apply Fintype.sum_equiv e
    intro ab
    change _ = (μ.mass (swap ab.1 ab.2) * μ.mass (swap ab.2 ab.1))*(f (swap ab.1 ab.2)*g (swap ab.1 ab.2))
    rw [hmass,(hswap ..).1,(hswap ..).2]
  have ha : ∑ ab, A ab = μ.mean f * μ.mean g := by
    rw [Fintype.sum_prod_type]
    unfold A mean
    rw [sum_mul]
    simp only [mul_sum]
    apply sum_congr rfl; intro a _; apply sum_congr rfl; intro b _; ring
  have hb : ∑ ab, B ab = μ.mean (fun a => f a*g a) := by
    rw [Fintype.sum_prod_type]
    apply sum_congr rfl
    intro a _
    change (∑ b, μ.mass a*μ.mass b*(f a*g a)) = _
    simp_rw [show ∀ b, μ.mass a*μ.mass b*(f a*g a) = (μ.mass a*(f a*g a))*μ.mass b from fun _ => by ring]
    rw [← mul_sum,μ.total,mul_one]
  exact hb.symm.trans (eq.symm.trans ha)
end FiniteLaw
end Vu

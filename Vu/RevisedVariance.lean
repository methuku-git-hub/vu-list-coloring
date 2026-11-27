module
public import Vu.RevisedMoments
public import Vu.RevisedCounting
public import Vu.MarkLaw
public import Vu.ProductLaw
namespace Vu.Revised
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The omitted-set variance estimate in the revised Section 6. The
signed rectangle condition is the only cancellation hypothesis. -/
public theorem omitted_variance (T : Finset V) (D : ℕ) (η A C K : ℝ)
    (lam w : V → ℝ) (f : V → V → ℝ) (hD : 0 < D) (hT : T.card ≤ D)
    (hA : 0 ≤ A) (hC : 1 ≤ C) (hK : 0 ≤ K)
    (hl : ∀ z, 0 ≤ lam z ∧ lam z ≤ 1/C) (hlA : ∀ z, lam z ≤ A/D)
    (hw : ∀ u, 0 ≤ w u ∧ w u ≤ K) (hf : ∀ u z, -1 ≤ f u z ∧ f u z ≤ C)
    (hrow : ∀ u, ∑ z, |f u z| ≤ C*D)
    (rect : ∀ U ⊆ T, ∀ Y : Finset V, Y.card ≤ D → |∑ u ∈ U, ∑ z ∈ Y, f u z| ≤ η*D^2) :
    let p := fun z => activation (lam z)
    let Z := fun ω => ∑ u ∈ T, w u*Bernoulli.multiplier p (f u) ω
    Bernoulli.expect p Z = ∑ u ∈ T, w u ∧
      Bernoulli.expect p (fun ω => Z ω^2)-(Bernoulli.expect p Z)^2 ≤
      4*K^2*Real.exp (A*C^2)*A*C*η*D^2 := by
  classical
  intro p Z
  have hp z := activation_odds (lam z) (hl z).1
  let μ := markLaw p (fun z => (hp z).1) (fun z => (hp z).2.1.le)
  let X u := Bernoulli.multiplier p (f u)
  have hx u : μ.mean (X u) = 1 := Bernoulli.expect_multiplier _ _ (fun z => (hp z).2.1)
  have hm : μ.mean Z = ∑ u ∈ T, w u := by
    change μ.mean (fun ω => ∑ u ∈ T, w u*X u ω) = _
    simp only [FiniteLaw.mean_sum_finset,FiniteLaw.mean_smul,hx,mul_one]
  refine ⟨hm,?_⟩
  let s u v := ∑ z, f v z*(lam z*f u z)
  let B := A*C^2
  have hd : (0:ℝ) < D := Nat.cast_pos.mpr hD
  have habs u z : |f u z| ≤ C := abs_le.mpr ⟨by linarith [(hf u z).1],(hf u z).2⟩
  have hcol u z : |lam z*f u z| ≤ (A*C)/D := by
    rw [abs_mul,abs_of_nonneg (hl z).1]
    exact (mul_le_mul (hlA z) (habs u z) (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hmass u : ∑ z, |lam z*f u z| ≤ A*C := by
    apply (sum_le_sum (fun z _ => (abs_mul ..).le.trans (mul_le_mul_of_nonneg_right ((abs_of_nonneg (hl z).1).le.trans (hlA z)) (abs_nonneg _)))).trans
    rw [←mul_sum]
    exact (mul_le_mul_of_nonneg_left (hrow u) (div_nonneg hA hd.le)).trans_eq (by field_simp)
  have hB u v : |s u v| ≤ B := by
    apply (abs_sum_le_sum_abs _ _).trans
    simp_rw [abs_mul (f v _)]; apply (sum_le_sum fun z _ => mul_le_mul_of_nonneg_right (habs v z) (abs_nonneg _)).trans
    rw [←mul_sum]; exact (mul_le_mul_of_nonneg_left (hmass u) (by linarith)).trans_eq (by dsimp [B]; ring)
  have hsum u : ∑ v ∈ T, |s u v| ≤ 4*(A*C)*η*D := weighted_count T f _ D (A*C) η hD
    (mul_nonneg hA (by linarith)) rect (hcol u) (hmass u)
  have cov u v : μ.mean (fun ω => X u ω*X v ω)-1 ≤ Real.exp B*|s u v| := by
    have hj := (two_moments C hC lam (f u) (f v) hl (hf u) (hf v)).2.2
    have he : μ.mean (fun ω => X u ω*X v ω) ≤ Real.exp (s u v) := by
      apply hj.1.le.trans (hj.2.trans_eq ?_)
      congr 1; apply sum_congr rfl; intro z _; ring
    have t := s u v
    have hneg := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-s u v)) (Real.exp_pos (s u v)).le
    rw [←Real.exp_add,neg_add_cancel,Real.exp_zero] at hneg
    apply (sub_le_sub_right he 1).trans
    apply le_trans (b := s u v*Real.exp (s u v)) (by linarith only [hneg])
    rw [mul_comm (Real.exp B)]
    exact ((mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le)).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ((le_abs_self _).trans (hB u v))) (abs_nonneg _))
  have hsq (ω) : Z ω^2 = ∑ u ∈ T, ∑ v ∈ T, (w u*w v)*(X u ω*X v ω) := by
    simp only [Z,pow_two,sum_mul,mul_sum,X]; apply sum_congr rfl; intro u _
    apply sum_congr rfl; intro v _; ring
  change μ.mean (fun ω => Z ω^2)-(μ.mean Z)^2 ≤ _
  rw [hm]; simp_rw [hsq]
  simp only [FiniteLaw.mean_sum_finset,FiniteLaw.mean_smul,pow_two,sum_mul,mul_sum,←sum_sub_distrib]
  have hc := sum_le_sum (s := T) (fun u _ => sum_le_sum (s := T) (fun v _ =>
      calc (w u*w v)*μ.mean (fun ω => X u ω*X v ω)-w v*w u =
              (w u*w v)*(μ.mean (fun ω => X u ω*X v ω)-1) := by ring
           _ ≤ (w u*w v)*(Real.exp B*|s u v|) := mul_le_mul_of_nonneg_left (cov u v) (mul_nonneg (hw u).1 (hw v).1)
           _ ≤ (K^2*Real.exp B)*|s u v| := by
             rw [mul_assoc (K^2),sq]
             exact mul_le_mul_of_nonneg_right (mul_le_mul (hw u).2 (hw v).2 (hw v).1 hK) (by positivity)))
  apply hc.trans
  simp_rw [←mul_sum]
  have hc' : 0 ≤ K^2*Real.exp B := by positivity
  apply (mul_le_mul_of_nonneg_left (sum_le_sum (fun u (_ : u ∈ T) => hsum u)) hc').trans
  simp only [sum_const,nsmul_eq_mul]
  have he : 0 ≤ 4*(A*C)*η*D := by
    have hh := (abs_nonneg _).trans (rect ∅ (empty_subset _) ∅ (by simp))
    have hη : 0 ≤ η := nonneg_of_mul_nonneg_left hh (sq_pos_of_pos hd)
    positivity
  have hend := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (Nat.cast_le (α := ℝ) |>.mpr hT) he) hc'
  dsimp only [B] at hend ⊢
  convert hend using 1 <;> ring
end Vu.Revised

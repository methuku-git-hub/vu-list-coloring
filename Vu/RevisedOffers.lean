module
public import Vu.RevisedCoverage
public import Vu.RevisedMoments
public import Vu.FixedColorTail
namespace Vu.Revised
open Finset
variable {V C : Type*} [Fintype V] [DecidableEq V]

private theorem no_activation (lam : ℝ) (h : 0 ≤ lam) :
    1-activation lam = (1+lam)⁻¹ ∧ Real.exp (-lam) ≤ 1-activation lam := by
  have hp : 0 < 1+lam := by linarith
  have he : 1-activation lam=(1+lam)⁻¹ := by unfold activation; field_simp; ring
  refine ⟨he,?_⟩
  rw [he,Real.exp_neg]
  exact inv_anti₀ hp (by simpa [add_comm] using Real.add_one_le_exp lam)

private theorem only_one_hit (l : List C) (lam h : C → ℝ) (ν : ℝ) (hl : ∀ d, 0 ≤ lam d)
    (h_upper : ∀ d ∈ l, h d ≤ activation (lam d))
    (h_lower : ∀ d ∈ l, activation (lam d)*Real.exp (-ν) ≤ h d) :
    (l.map lam).sum * Real.exp (-ν) * (l.map (fun d => 1-activation (lam d))).prod ≤
      1-(l.map (fun d => 1-h d)).prod := by
  induction l with
  | nil => simp
  | cons d l ih =>
    have hrest := ih (fun e he => h_upper e (List.mem_cons_of_mem d he)) (fun e he => h_lower e (List.mem_cons_of_mem d he))
    have hd := h_lower d (List.mem_cons_self ..)
    have hd' := h_upper d (List.mem_cons_self ..)
    let t := (l.map (fun e => 1-activation (lam e))).prod
    have ht0 : 0 ≤ t := List.prod_nonneg (by simpa using fun e (_ : e ∈ l) => sub_nonneg.mpr (activation_odds _ (hl e)).2.1.le)
    have prod_one (s : List C) : (s.map (fun e => 1-activation (lam e))).prod ≤ 1 := by
      induction s with
      | nil => simp
      | cons e s ih =>
        simp only [List.map_cons,List.prod_cons]
        exact (mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr (activation_odds _ (hl e)).2.1.le)).trans
          (by simpa using sub_le_self (1:ℝ) (activation_odds _ (hl e)).1)
    have ht1 : t ≤ 1 := prod_one l
    have hnd := (activation_odds (lam d) (hl d)).2.1
    have hid : lam d*(1-activation (lam d)) = activation (lam d) := by rw [(no_activation _ (hl d)).1]; rfl
    have hhit : 0 ≤ h d := (mul_nonneg (activation_odds _ (hl d)).1 (Real.exp_pos _).le).trans hd
    have hsum : 0 ≤ (l.map lam).sum := List.sum_nonneg (by simpa using fun e (_ : e ∈ l) => hl e)
    simp only [List.map_cons,List.prod_cons,List.sum_cons]
    change (lam d+_)*Real.exp (-ν)*((1-activation (lam d))*t) ≤ _
    have hx := mul_le_mul_of_nonneg_right hrest (sub_nonneg.mpr (hd'.trans hnd.le))
    have hy := mul_le_mul_of_nonneg_right (sub_le_sub_left hd' 1)
      (mul_nonneg (mul_nonneg hsum (Real.exp_pos (-ν)).le) ht0)
    have hz := (mul_le_mul_of_nonneg_right hd ht0).trans ((mul_le_mul_of_nonneg_left ht1 hhit).trans_eq (mul_one _))
    change _*_*t ≤ _ at hrest
    change _*_*t*(1-h d) ≤ _ at hx
    linarith only [hx,hy,hz,congrArg (fun z => z*Real.exp (-ν)*t) hid]

/-- The conditional offer estimate of Lemma 6.4. The list comprises the
colors other than the exposed one. The product is the probability of
no offer at x under their independent laws. -/
public theorem another_offer (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) (l : List C)
    (lam : C → V → ℝ) (hl : ∀ d z, 0 ≤ lam d z) (x : V) (hx : x ∈ T)
    (ν p : ℝ) (hν : ν ≤ 1/32) (hp : 0 < p) (hpν : p ≤ ν)
    (hlo : (1-ν)*p ≤ (l.map (fun d => lam d x)).sum)
    (hhi : (l.map (fun d => lam d x)).sum ≤ p)
    (hN : ∀ d ∈ l, 0 < lam d x → ∑ y ∈ G.neighborFinset x, lam d y ≤ ν) :
    let q d := offerLaw G T (fun y => activation (lam d y)) (fun y => (activation_odds _ (hl d y)).1)
      (fun y => (activation_odds _ (hl d y)).2.1.le)
    (1-3*ν)*p ≤ 1-(l.map (fun d => 1-hitProbability (q d) x)).prod := by
  intro q
  let π d y := activation (lam d y)
  have h₀ d y : 0 ≤ π d y := (activation_odds _ (hl d y)).1
  have h₁ d y : π d y ≤ 1 := (activation_odds _ (hl d y)).2.1.le
  have hq d := offer_probability G T (π d) (h₀ d) (h₁ d) x hx
  have upper d : hitProbability (q d) x ≤ π d x := by
    rw [show hitProbability (q d) x = _ from hq d]
    apply mul_le_of_le_one_right (h₀ d x)
    exact prod_le_one₀ (fun y _ => sub_nonneg.mpr (h₁ d y)) (fun y _ => sub_le_self _ (h₀ d y))
  have lower d (hd : d ∈ l) : π d x*Real.exp (-ν) ≤ hitProbability (q d) x := by
    rw [show hitProbability (q d) x = _ from hq d]
    by_cases hh : 0 < lam d x
    · apply mul_le_mul_of_nonneg_left _ (h₀ d x)
      apply (Real.exp_le_exp.mpr (neg_le_neg (hN d hd hh))).trans
      rw [←sum_neg_distrib,Real.exp_sum]
      exact prod_le_prod₀ (fun y _ => (Real.exp_pos _).le) (fun y _ => (no_activation _ (hl d y)).2)
    · have hz := le_antisymm (le_of_not_gt hh) (hl d x)
      simp [π,activation,hz]
  have prodBound (s : List C) : Real.exp (-(s.map (fun d => lam d x)).sum) ≤ (s.map (fun d => 1-π d x)).prod := by
    induction s with
    | nil => simp
    | cons d s ih =>
      simp only [List.map_cons,List.sum_cons,List.prod_cons,neg_add,Real.exp_add]
      exact mul_le_mul (no_activation _ (hl d x)).2 ih (Real.exp_pos _).le (sub_nonneg.mpr (h₁ d x))
  have ht := only_one_hit l (fun d => lam d x) (fun d => hitProbability (q d) x) ν (fun d => hl d x) (fun d _ => upper d) lower
  apply le_trans _ ht
  let m := (l.map (fun d => lam d x)).sum
  have hm : 0 ≤ m := List.sum_nonneg (by simpa using fun d (_ : d ∈ l) => hl d x)
  have hh := mul_le_mul_of_nonneg_left ((Real.exp_le_exp.mpr (neg_le_neg hhi)).trans (prodBound l)) (mul_nonneg hm (Real.exp_pos (-ν)).le)
  apply le_trans _ hh
  rw [mul_assoc,←Real.exp_add]
  have hn := hp.le.trans hpν
  have hcoef : 0 ≤ 1-ν-p := by linarith
  have hcoef' : 1-ν-p ≤ Real.exp (-ν + -p) := by linarith only [Real.add_one_le_exp (-ν + -p)]
  apply le_trans _ (mul_le_mul hlo hcoef' hcoef hm)
  nlinarith only [mul_nonneg hp.le (sub_nonneg.mpr hpν),mul_nonneg (mul_nonneg hp.le hn) (add_nonneg hn hp.le)]
end Vu.Revised

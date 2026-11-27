module
public import Vu.ProductLaw
public import Vu.CoordinateLLL
public import Vu.RetainedExpectation
namespace Vu
open Finset

/-- Exponential lower tail for a sum of independent coordinates with range
[0,K]. Only the coordinates in T contribute to the variance budget. -/
public theorem bounded_sum_chance {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]
    (q : I → FiniteLaw X) (T : Finset I) (f : I → X → ℝ) (K u : ℝ) (hK : 0 < K)
    (hu : 0 < u) (hT : T.Nonempty) (hf : ∀ i ∈ T, ∀ x, 0 ≤ f i x ∧ f i x ≤ K) :
    (FiniteLaw.independent q).chance (fun a => ∑ i ∈ T, f i (a i) ≤ (∑ i ∈ T, (q i).mean (f i))-u) ≤
      Real.exp (-u^2/(2*(T.card*K^2+K*u/3))) := by
  classical
  let v : ℝ := T.card*K^2
  have hv : 0 < v := mul_pos (Nat.cast_pos.mpr (card_pos.mpr hT)) (sq_pos_of_pos hK)
  let d := v+K*u/3
  have hd : 0 < d := by dsimp [d]; positivity
  let θ := u/d
  have hθ : 0 < θ := div_pos hu hd
  have hθK : θ*K < 3 := by dsimp [θ]; rw [div_mul_eq_mul_div,div_lt_iff₀ hd]; dsimp [d]; linarith
  let g (i : I) (x : X) := if i ∈ T then Real.exp (θ*((q i).mean (f i)-f i x)) else 1
  let c := θ^2/(2*(1-θ*K/3))
  have hfactor (i : I) (hi : i ∈ T) : (q i).mean (g i) ≤ Real.exp (c*K^2) := by
    have h := (q i).mean_exp_gain (f i) (fun _ => K) 0 K θ hθ.le hθK (fun x => by simpa using hf i hi x) (by simp)
    simpa [g,hi,c] using h
  have hmgf : (FiniteLaw.independent q).mean (fun a => ∏ i, g i (a i)) ≤ Real.exp (c*v) := by
    rw [FiniteLaw.independent_product]
    apply (prod_le_prod₀ (fun i _ => (q i).mean_nonneg _ (fun x => by dsimp [g]; split <;> positivity))
      (g := fun i => if i ∈ T then Real.exp (c*K^2) else 1) (fun i _ => ?_)).trans_eq
    · simp [← Real.exp_nat_mul,v]; ring
    · by_cases hi : i ∈ T
      · simpa only [if_pos hi] using hfactor i hi
      · simp [g,hi]
  let m := ∑ i ∈ T, (q i).mean (f i)
  have hpoint (a : I → X) : (if ∑ i ∈ T, f i (a i) ≤ m-u then (1:ℝ) else 0) ≤
      Real.exp (-θ*u)*∏ i, g i (a i) := by
    have heq : (∏ i, g i (a i)) = Real.exp (θ*(m-∑ i ∈ T, f i (a i))) := by
      simp [g,←Real.exp_sum,m,mul_sub,sum_sub_distrib,mul_sum]
    rw [heq,←Real.exp_add]
    split
    next h => apply Real.one_le_exp_iff.mpr; nlinarith only [mul_nonneg hθ.le (sub_nonneg.mpr h)]
    next => exact (Real.exp_pos _).le
  apply ((FiniteLaw.independent q).mean_mono hpoint).trans
  rw [FiniteLaw.mean_smul]
  apply (mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le).trans_eq
  rw [←Real.exp_add]; congr 1
  have heq : 1-θ*K/3 = v/d := by dsimp only [θ]; field_simp [hd.ne']; dsimp [d]; ring
  dsimp only [c]; rw [heq]
  change -θ*u+θ^2/(2*(v/d))*v = -u^2/(2*d)
  dsimp only [θ]; field_simp [hd.ne',hv.ne']; ring

/-- Lemma 6.3 for independent color blocks: the failure probability at
each uncolored vertex is exponentially small in the degree parameter. -/
public theorem retained_total_tail {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]
    (q : I → FiniteLaw X) (T : Finset I) (f : I → X → ℝ) (w : I → ℝ) (D k : ℕ)
    (a e K : ℝ) (ha : 0 < a) (he : 0 < e) (hK : 0 < K) (hk : 0 < k)
    (hak : a*D ≤ k) (hcard : T.card = k) (htotal : ∑ i ∈ T, w i = k)
    (hf : ∀ i ∈ T, ∀ x, 0 ≤ f i x ∧ f i x ≤ K)
    (hm : ∀ i ∈ T, w i-e/4 ≤ (q i).mean (f i)) :
    let κ := a*(3*e/4)^2/(2*(K^2+K*(3*e/4)/3))
    0 < κ ∧ (FiniteLaw.independent q).chance (fun b => ∑ i ∈ T, f i (b i) < k*(1-e)) ≤ Real.exp (-κ*D) := by
  classical
  intro κ
  have hkp : 0 < (k:ℝ) := Nat.cast_pos.mpr hk
  let t := 3*e/4
  have ht : 0 < t := by dsimp [t]; positivity
  let c := t^2/(2*(K^2+K*t/3))
  have hc : 0 < c := by dsimp [c]; positivity
  have hkappa : κ = c*a := by dsimp [κ,c,t]; ring
  refine ⟨hkappa ▸ mul_pos hc ha,?_⟩
  have hh := bounded_sum_chance q T f K (t*k) hK (mul_pos ht hkp) (card_pos.mp (hcard.trans_gt hk)) hf
  have hsum := sum_le_sum hm
  rw [sum_sub_distrib,htotal,sum_const,nsmul_eq_mul,hcard] at hsum
  apply le_trans _ (hh.trans ?_)
  · apply (FiniteLaw.independent q).mean_mono
    intro b
    split
    next h =>
      have hh : ∑ i ∈ T, f i (b i) ≤ (∑ i ∈ T, (q i).mean (f i))-t*k := by dsimp [t]; linarith
      simp [hh]
    next => split <;> norm_num
  · apply Real.exp_le_exp.mpr
    rw [hcard,hkappa]
    have hden : 0 < 2*(K^2+K*t/3) := by positivity
    have h1 : -(t*(k:ℝ))^2/(2*((k:ℝ)*K^2+K*(t*k)/3)) = -c*k := by
      rw [show 2*((k:ℝ)*K^2+K*(t*k)/3) = (2*(K^2+K*t/3))*k by ring]
      dsimp [c]; field_simp [hkp.ne',hden.ne'] <;> ring
    rw [h1]
    linarith only [mul_le_mul_of_nonneg_left hak hc.le]
end Vu

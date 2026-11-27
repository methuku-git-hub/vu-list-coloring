module
public import Vu.RevisedCoverage
public import Vu.VertexWeightTail
namespace Vu.Revised
open Finset
variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]

/-- The independent-sum part of the exposure lemma, with the uncentered
second-moment sum in the denominator. -/
public theorem sum_lower_tail (q : I → FiniteLaw X) (T : Finset I) (f : I → X → ℝ)
    (t v : ℝ) (ht : 0 < t) (hv : 0 < v) (hf : ∀ i ∈ T, ∀ x, 0 ≤ f i x)
    (hb : (∑ i ∈ T, (q i).mean (fun x => (f i x)^2)) ≤ v) :
    (FiniteLaw.independent q).chance (fun a => ∑ i ∈ T, f i (a i) ≤ (∑ i ∈ T, (q i).mean (f i))-t) ≤
      Real.exp (-t^2/(2*v)) := by
  classical
  let θ := t/v
  have hθ := (div_pos ht hv).le
  let c := θ^2/2
  let g i (x : X) := if i ∈ T then Real.exp (θ*((q i).mean (f i)-f i x)) else 1
  let m i := (q i).mean (fun x => (f i x)^2)
  have hfactor i : (q i).mean (g i) ≤ if i ∈ T then Real.exp (c*m i) else 1 := by
    by_cases hi : i ∈ T
    · have hh := centered_gain (q i) (f i) (f i) 0 θ hθ (fun x => by simp [hf i hi x])
      simpa [g,hi,c,m] using hh
    · simp [g,hi]
  have hmgf : (FiniteLaw.independent q).mean (fun a => ∏ i, g i (a i)) ≤ Real.exp (c*v) := by
    rw [FiniteLaw.independent_product]
    apply (prod_le_prod₀ (fun i _ => (q i).mean_nonneg _ (fun x => by dsimp [g]; split <;> positivity)) (fun i _ => hfactor i)).trans
    simp only [←prod_filter,filter_mem_eq_inter,univ_inter,←Real.exp_sum,←mul_sum]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hb (by dsimp [c]; positivity))
  let μ := ∑ i ∈ T, (q i).mean (f i)
  have point (a : I → X) : (if ∑ i ∈ T, f i (a i) ≤ μ-t then (1:ℝ) else 0) ≤ Real.exp (-θ*t)*∏ i, g i (a i) := by
    have heq : (∏ i, g i (a i)) = Real.exp (θ*(μ-∑ i ∈ T, f i (a i))) := by
      simp [g,←Real.exp_sum,μ,mul_sub,sum_sub_distrib,mul_sum]
    rw [heq,←Real.exp_add]
    split
    next h => apply Real.one_le_exp_iff.mpr; nlinarith only [mul_nonneg hθ (sub_nonneg.mpr h)]
    next => positivity
  apply ((FiniteLaw.independent q).mean_mono point).trans
  rw [FiniteLaw.mean_smul]
  apply (mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le).trans_eq
  rw [←Real.exp_add]; congr 1
  dsimp [θ,c]; field_simp; ring

/-- Lemma on total retained weight at a vertex. Each color has second
moment at most the squared cutoff, and different colors are independent. -/
public theorem retained_total_tail (q : I → FiniteLaw X) (T : Finset I) (f : I → X → ℝ) (w : I → ℝ) (D k : ℕ)
    (a e K : ℝ) (ha : 0 < a) (he : 0 < e) (hK : 0 < K) (hk : 0 < k)
    (hak : a*D ≤ k) (hcard : T.card = k) (htotal : ∑ i ∈ T, w i = k)
    (hf : ∀ i ∈ T, ∀ x, 0 ≤ f i x ∧ f i x ≤ K) (hm : ∀ i ∈ T, w i-e/4 ≤ (q i).mean (f i)) :
    let κ := a*(3*e/4)^2/(2*K^2)
    0 < κ ∧ (FiniteLaw.independent q).chance (fun b => ∑ i ∈ T, f i (b i) < k*(1-e)) ≤ Real.exp (-κ*D) := by
  classical
  intro κ
  have hkp : 0 < (k:ℝ) := Nat.cast_pos.mpr hk
  let t := 3*e/4
  have ht : 0 < t := by dsimp [t]; positivity
  let c := t^2/(2*K^2)
  have hc : 0 < c := by dsimp [c]; positivity
  have hkappa : κ = c*a := by dsimp [κ,c,t]; ring
  refine ⟨hkappa ▸ mul_pos hc ha,?_⟩
  have hh := sum_lower_tail q T f (t*k) (k*K^2) (mul_pos ht hkp) (by positivity) (fun i hi x => (hf i hi x).1) (by
    have bnd i (hi : i ∈ T) : (q i).mean (fun x => (f i x)^2) ≤ K^2 := by
      rw [←(q i).mean_const (K^2)]
      exact (q i).mean_mono (fun x => pow_le_pow_left₀ (hf i hi x).1 (hf i hi x).2 2)
    simpa [hcard] using sum_le_sum (s := T) bnd)
  have hsum := sum_le_sum hm
  rw [sum_sub_distrib,htotal,sum_const,nsmul_eq_mul,hcard] at hsum
  apply le_trans _ (hh.trans ?_)
  · apply (FiniteLaw.independent q).mean_mono
    intro b
    split
    next h =>
      have he : ∑ i ∈ T, f i (b i) ≤ (∑ i ∈ T, (q i).mean (f i))-t*k := by dsimp [t]; linarith
      simp [he]
    next => split <;> norm_num
  · apply Real.exp_le_exp.mpr
    have eq : -(t*(k:ℝ))^2/(2*(k*K^2)) = -c*k := by dsimp [c]; field_simp <;> ring
    rw [eq,hkappa]
    linarith only [mul_le_mul_of_nonneg_left hak hc.le]
end Vu.Revised

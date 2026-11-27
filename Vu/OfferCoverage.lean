module
public import Vu.Coverage
namespace Vu
open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] public noncomputable def hitProbability (p : FiniteLaw (Finset V)) (x : V) : ℝ :=
  p.mean (fun S => if x ∈ S then 1 else 0)

private theorem hit_range (p : FiniteLaw (Finset V)) (x : V) :
    0 ≤ hitProbability p x ∧ hitProbability p x ≤ 1 := by
  refine ⟨p.mean_nonneg _ (fun S => by split <;> norm_num),?_⟩
  rw [← p.mean_const 1]
  exact p.mean_mono (fun S => by split <;> norm_num)

private theorem mean_sum {I Ω : Type*} [Fintype Ω] (p : FiniteLaw Ω) (s : Finset I) (f : I → Ω → ℝ) :
    p.mean (fun u => ∑ i ∈ s, f i u) = ∑ i ∈ s, p.mean (f i) := by
  simp only [FiniteLaw.mean,mul_sum]; rw [sum_comm]

/-- Exact first moment of the weight of the union, allowing dependencies
among vertices offered the same color. -/
public theorem union_expected_weight (ps : List (FiniteLaw (Finset V))) (w : V → ℝ) (U : Finset V) :
    coverageAverage ps (setWeight w) U =
      ∑ x, w x*(if x ∈ U then 1 else 1-(ps.map fun p => 1-hitProbability p x).prod) := by
  classical
  induction ps generalizing U with
  | nil =>
    simp [coverageAverage,setWeight,mul_ite,←sum_filter]
  | cons p tail ih =>
    simp only [coverageAverage,ih,mean_sum,FiniteLaw.mean_smul,List.map_cons,List.prod_cons]
    apply sum_congr rfl
    intro x _
    congr 1
    by_cases hx : x ∈ U
    · simp [hx,FiniteLaw.mean_const]
    · let m := (tail.map fun p => 1-hitProbability p x).prod
      have he (S : Finset V) : (if x ∈ U ∪ S then (1:ℝ) else 1-m) =
          (1-m)+m*(if x ∈ S then 1 else 0) := by by_cases h : x ∈ S <;> simp [hx,h]
      change p.mean (fun S => if x ∈ U ∪ S then 1 else 1-m) =
        if x ∈ U then 1 else 1-(1-hitProbability p x)*m
      simp only [he,hx,ite_false,FiniteLaw.mean_add,FiniteLaw.mean_const,FiniteLaw.mean_smul,hitProbability]
      ring

private theorem no_hit_bound (ps : List (FiniteLaw (Finset V))) (x : V) :
    (ps.map fun p => 1-hitProbability p x).prod ≤ Real.exp (-(ps.map (hitProbability · x)).sum) := by
  induction ps with
  | nil => simp
  | cons p tail ih =>
    simp only [List.map_cons,List.sum_cons,List.prod_cons,neg_add,Real.exp_add]
    exact mul_le_mul (by linarith only [Real.add_one_le_exp (-hitProbability p x)]) ih
      (List.prod_nonneg (by simpa using fun q (_ : q ∈ tail) => sub_nonneg.mpr (hit_range q x).2))
      (Real.exp_pos _).le

/-- Once colors other than the exposed color supply a total offer probability
of at least (1-ν)²p at each positive-weight vertex, their union covers at
least (1-4ν)p of the weight in expectation. -/
public theorem offer_expected_weight_lower (ps : List (FiniteLaw (Finset V))) (w : V → ℝ)
    (hw : ∀ x, 0 ≤ w x) (p ν : ℝ) (hp : 0 ≤ p) (hpν : p ≤ ν) (hν : ν ≤ 1)
    (hoffer : ∀ x, 0 < w x → (1-ν)^2*p ≤ (ps.map (hitProbability · x)).sum) :
    (1-4*ν)*p*setWeight w univ ≤ coverageAverage ps (setWeight w) ∅ := by
  classical
  let a := (1-ν)^2*p
  have hn : 0 ≤ ν := hp.trans hpν
  have ha : 0 ≤ a := mul_nonneg (sq_nonneg _) hp
  have ha' : a ≤ p := by
    have hsq : (1-ν)^2 ≤ 1 := by nlinarith [mul_nonneg hn (sub_nonneg.mpr hν)]
    exact (mul_le_mul_of_nonneg_right hsq hp).trans_eq (one_mul _)
  have hex := bernstein_exp_bound (-a) 0 (neg_nonpos.mpr ha) (by norm_num)
  have hlow : (1-4*ν)*p ≤ 1-Real.exp (-a) := by
    have h1 : (1-2*ν)*p ≤ a := by dsimp [a]; nlinarith only [mul_nonneg (sq_nonneg ν) hp]
    have h2 : a^2 ≤ p*ν := by simpa [pow_two] using mul_le_mul ha' (ha'.trans hpν) ha hp
    norm_num at hex
    linarith only [hex,h1,h2,mul_nonneg hn hp]
  rw [union_expected_weight]
  simp only [setWeight,notMem_empty,ite_false,mul_sum]
  apply sum_le_sum
  intro x _
  by_cases hh : 0 < w x
  · have hnone := (no_hit_bound ps x).trans (Real.exp_le_exp.mpr (neg_le_neg (hoffer x hh)))
    exact (mul_le_mul_of_nonneg_right (hlow.trans (by linarith only [hnone])) (hw x)).trans_eq (mul_comm ..)
  · simp [le_antisymm (le_of_not_gt hh) (hw x)]

/-- Finite nonasymptotic conditional tail inequality used in Lemma 6.4.
L bounds the weight after the deletion test; the remaining weight is no
larger than the weight outside the union of offers of other colors. -/
public theorem remaining_weight_tail_of_bound (ps : List (FiniteLaw (Finset V))) (w : V → ℝ)
    (hw : ∀ x, 0 ≤ w x) (p ν L M v : ℝ) (hp : 0 < p) (hpν : p ≤ ν) (hν : ν ≤ 1/200)
    (hL : 0 < L) (hmass : setWeight w univ ≤ L) (hM : 0 ≤ M)
    (hmean : ∀ q ∈ ps, q.mean (setWeight w) ≤ M)
    (hoffer : ∀ x, 0 < w x → (1-ν)^2*p ≤ (ps.map (hitProbability · x)).sum) :
    let u := ν*p*L
    (ps.map fun q => q.mean (fun S => setWeight w S^2)).sum ≤ v → 0 < v →
    coverageAverage ps (fun S => if (1-(1-5*ν)*p)*L < setWeight w univ-setWeight w S then 1 else 0) ∅ ≤
      Real.exp (-u^2/(2*(v+M*u/3))) := by
  intro u hvv hv
  have hn : 0 < ν := hp.trans_le hpν
  have h1 : ν ≤ 1 := by linarith
  have hcov := offer_expected_weight_lower ps w hw p ν hp.le hpν h1 hoffer
  have hcoef : 0 ≤ 1-(1-4*ν)*p := by nlinarith [mul_nonneg hn.le hp.le]
  have hupper : setWeight w univ-coverageAverage ps (setWeight w) ∅ ≤ (1-(1-4*ν)*p)*L := by
    linarith only [hcov,mul_le_mul_of_nonneg_left hmass hcoef]
  apply le_trans _ (independent_union_lower_tail_of_bound ps w hw M u v hM (by dsimp [u]; positivity) hmean hvv hv)
  apply coverage_mono
  intro S
  split
  next h =>
    have hh : setWeight w S ≤ coverageAverage ps (setWeight w) ∅-u := by dsimp [u]; linarith
    simp [hh]
  next => split <;> norm_num
public theorem remaining_weight_tail (ps : List (FiniteLaw (Finset V))) (w : V → ℝ)
    (hw : ∀ x, 0 ≤ w x) (p ν L M : ℝ) (hp : 0 < p) (hpν : p ≤ ν) (hν : ν ≤ 1/200)
    (hL : 0 < L) (hmass : setWeight w univ ≤ L) (hM : 0 ≤ M)
    (hmean : ∀ q ∈ ps, q.mean (setWeight w) ≤ M)
    (hoffer : ∀ x, 0 < w x → (1-ν)^2*p ≤ (ps.map (hitProbability · x)).sum) :
    let v := (ps.map fun q => q.mean (fun S => setWeight w S^2)).sum
    let u := ν*p*L
    0 < v →
    coverageAverage ps (fun S => if (1-(1-5*ν)*p)*L < setWeight w univ-setWeight w S then 1 else 0) ∅ ≤
      Real.exp (-u^2/(2*(v+M*u/3))) := by
  intro v u hv
  exact remaining_weight_tail_of_bound ps w hw p ν L M v hp hpν hν hL hmass hM hmean hoffer le_rfl hv
end Vu

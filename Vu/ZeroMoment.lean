module
public import Vu.RevisedSumTail
namespace Vu.Revised
open Finset

private theorem mean_zero_of_sq {Ω : Type*} [Fintype Ω] (p : FiniteLaw Ω) (f : Ω → ℝ)
    (h : p.mean (fun x => (f x)^2) = 0) : p.mean f = 0 := by
  have hh := (sum_eq_zero_iff_of_nonneg (fun x (_ : x ∈ (univ : Finset Ω)) =>
    mul_nonneg (p.nonneg x) (sq_nonneg (f x)))).mp h
  apply sum_eq_zero; intro x _
  rcases mul_eq_zero.mp (hh x (mem_univ x)) with hx|hx
  · simp [hx]
  · simp [sq_eq_zero_iff.mp hx]

/-- When the sum of second moments is zero, the union has expected weight
zero. Even a union of probability zero cannot have negative weight. -/
public theorem union_zero_event {V : Type*} [Fintype V] [DecidableEq V]
    (ps : List (FiniteLaw (Finset V))) (w : V → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hv : (ps.map fun p => p.mean (fun S => setWeight w S^2)).sum = 0)
    (t : ℝ) (ht : 0 < t) : ∀ S, ¬setWeight w S ≤ coverageAverage ps (setWeight w) ∅-t := by
  let W := setWeight w
  have zero (qs : List (FiniteLaw (Finset V))) (hz : (qs.map fun p => p.mean (fun S => W S^2)).sum = 0) :
      coverageAverage qs W ∅ ≤ 0 := by
    induction qs with
    | nil => simp [coverageAverage,W,setWeight]
    | cons p qs ih =>
      let moment (q : FiniteLaw (Finset V)) := q.mean (fun S => W S^2)
      have nonneg (q : FiniteLaw (Finset V)) : 0 ≤ moment q := q.mean_nonneg _ fun _ => sq_nonneg _
      have tail : 0 ≤ (qs.map moment).sum := List.sum_nonneg (by simpa using fun q (_ : q ∈ qs) => nonneg q)
      change moment p+(qs.map moment).sum = 0 at hz
      have hp := mean_zero_of_sq p W (by change moment p = 0; linarith [nonneg p])
      have ht := ih (by change (qs.map moment).sum = 0; linarith [nonneg p])
      have he x : coverageAverage qs W (∅ ∪ x) ≤ W x := by
        have h := (gain_bounds qs w hw ∅ x).2; change _ - coverageAverage qs W ∅ ≤ W x at h
        linarith
      exact (p.mean_mono he).trans hp.le
  intro S
  have hpos : 0 ≤ W S := sum_nonneg fun x _ => hw x
  change ¬W S ≤ coverageAverage ps W ∅-t
  linarith [zero ps hv]

/-- The zero-second-moment case for a sum of independent nonnegative
variables on finite spaces, including outcomes of mass zero. -/
public theorem sum_zero_event {I X : Type*} [Fintype X] (T : Finset I) (q : I → FiniteLaw X)
    (f : I → X → ℝ) (hf : ∀ i ∈ T, ∀ x, 0 ≤ f i x)
    (hv : (∑ i ∈ T, (q i).mean (fun x => (f i x)^2)) = 0)
    (t : ℝ) (ht : 0 < t) : ∀ a : I → X,
      ¬(∑ i ∈ T, f i (a i)) ≤ (∑ i ∈ T, (q i).mean (f i))-t := by
  have hh := (sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ T) => (q i).mean_nonneg _ (fun x => sq_nonneg (f i x)))).mp hv
  have hm := sum_eq_zero fun i hi => mean_zero_of_sq (q i) (f i) (hh i hi)
  intro a
  linarith [sum_nonneg (fun i hi => hf i hi (a i))]
end Vu.Revised

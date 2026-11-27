module
public import Vu.FiniteLaw
namespace Vu
open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Expectation over independent random subsets of V. The list keeps their
individual laws in exposure order. U is the set already covered. -/
@[expose] public noncomputable def coverageAverage :
    List (FiniteLaw (Finset V)) → (Finset V → ℝ) → Finset V → ℝ
  | [], f, U => f U
  | p :: tail, f, U => p.mean fun S => coverageAverage tail f (U ∪ S)

@[expose] public noncomputable def setWeight (w : V → ℝ) (s : Finset V) : ℝ := ∑ x ∈ s, w x

public theorem gain_bounds (ps : List (FiniteLaw (Finset V))) (w : V → ℝ) (hw : ∀ x, 0 ≤ w x)
    (U S : Finset V) :
    coverageAverage ps (setWeight w) U ≤ coverageAverage ps (setWeight w) (U ∪ S) ∧
    coverageAverage ps (setWeight w) (U ∪ S) - coverageAverage ps (setWeight w) U ≤ setWeight w S := by
  induction ps generalizing U with
  | nil =>
    dsimp only [coverageAverage,setWeight]
    exact ⟨sum_le_sum_of_subset_of_nonneg subset_union_left (fun x _ _ => hw x),
      by linarith only [sum_union_inter (s₁ := U) (s₂ := S) (f := w),sum_nonneg (s := U ∩ S) (fun x _ => hw x)]⟩
  | cons p tail ih =>
    have h (X : Finset V) := ih (U ∪ X)
    simp only [coverageAverage]
    have he (X : Finset V) : (U ∪ S) ∪ X = (U ∪ X) ∪ S := by ac_rfl
    simp_rw [he]
    refine ⟨p.mean_mono (fun X => (h X).1),?_⟩
    rw [← p.mean_sub,← p.mean_const (setWeight w S)]
    exact p.mean_mono (fun X => (h X).2)

public theorem coverage_mono (ps : List (FiniteLaw (Finset V))) {f g : Finset V → ℝ}
    (h : ∀ S, f S ≤ g S) (U : Finset V) : coverageAverage ps f U ≤ coverageAverage ps g U := by
  induction ps generalizing U with
  | nil => exact h U
  | cons p _ ih => exact p.mean_mono (fun S => ih (U ∪ S))

public theorem coverage_smul (ps : List (FiniteLaw (Finset V))) (c : ℝ) (f : Finset V → ℝ)
    (U : Finset V) : coverageAverage ps (fun S => c*f S) U = c*coverageAverage ps f U := by
  induction ps generalizing U with
  | nil => rfl
  | cons p tail ih => simp only [coverageAverage,ih,FiniteLaw.mean_smul]

/-- Bernstein exponential-moment bound for the weight of an independent union,
including arbitrary already covered vertices and arbitrary overlap between
different random sets. -/
public theorem independent_union_mgf (ps : List (FiniteLaw (Finset V))) (w : V → ℝ)
    (hw : ∀ x, 0 ≤ w x) (θ M : ℝ) (hθ : 0 ≤ θ) (hθM : θ*M < 3)
    (hmean : ∀ p ∈ ps, p.mean (setWeight w) ≤ M) (U : Finset V) :
    let W := setWeight w
    let variance := (ps.map fun p => p.mean (fun S => W S^2)).sum
    coverageAverage ps (fun S => Real.exp (-θ*W S)) U ≤
      Real.exp (-θ*coverageAverage ps W U + θ^2/(2*(1-θ*M/3))*variance) := by
  let W := setWeight w
  let c := θ^2/(2*(1-θ*M/3))
  induction ps generalizing U with
  | nil => simp [coverageAverage]
  | cons p tail ih =>
    let v := (tail.map fun p => p.mean fun S => W S^2).sum
    let h (S : Finset V) := coverageAverage tail W (U ∪ S)
    have ha (S : Finset V) := ih (fun q hq => hmean q (List.mem_cons_of_mem _ hq)) (U ∪ S)
    have hb := p.mean_exp_gain h W (coverageAverage tail W U) M θ hθ hθM
      (fun S => gain_bounds tail w hw U S) (hmean p (List.mem_cons_self ..))
    change p.mean (fun S => coverageAverage tail (fun X => Real.exp (-θ*W X)) (U ∪ S)) ≤
      Real.exp (-θ*p.mean h + c*(p.mean (fun S => W S^2)+v))
    apply (p.mean_mono ha).trans
    have he (S : Finset V) : Real.exp (-θ*h S+c*v) =
        Real.exp (-θ*p.mean h+c*v)*Real.exp (θ*(p.mean h-h S)) := by rw [← Real.exp_add]; congr 1; ring
    change p.mean (fun S => Real.exp (-θ*h S+c*v)) ≤ _
    simp_rw [he]
    rw [FiniteLaw.mean_smul]
    exact (mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le).trans_eq (by rw [← Real.exp_add]; dsimp only [c]; congr 1; ring)

/-- Lemma 2.2, the stated lower tail with its denominator 2(V+Mu/3).
The finite laws specify the joint law by independent sampling. -/
public theorem independent_union_lower_tail_of_bound (ps : List (FiniteLaw (Finset V))) (w : V → ℝ)
    (hw : ∀ x, 0 ≤ w x) (M u v : ℝ) (hM : 0 ≤ M) (hu : 0 < u)
    (hmean : ∀ p ∈ ps, p.mean (setWeight w) ≤ M) :
    let W := setWeight w
    (ps.map fun p => p.mean (fun S => W S^2)).sum ≤ v → 0 < v → coverageAverage ps (fun S => if W S ≤ coverageAverage ps W ∅ - u then 1 else 0) ∅ ≤
      Real.exp (-u^2/(2*(v+M*u/3))) := by
  intro W hvar hv
  let m := coverageAverage ps W ∅
  let a := v+M*u/3
  have ha : 0 < a := by dsimp [a]; positivity
  let θ := u/a
  have hθ : 0 < θ := div_pos hu ha
  have hθM : θ*M < 3 := by
    dsimp [θ]; rw [div_mul_eq_mul_div,div_lt_iff₀ ha]; dsimp [a]; linarith
  let c := θ^2/(2*(1-θ*M/3))
  have hh := independent_union_mgf ps w hw θ M hθ.le hθM hmean ∅
  have hc : 0 ≤ c := div_nonneg (sq_nonneg _) (by linarith)
  have hmgf : coverageAverage ps (fun S => Real.exp (-θ*W S)) ∅ ≤ Real.exp (-θ*m+c*v) :=
    hh.trans (Real.exp_le_exp.mpr (add_le_add_right (mul_le_mul_of_nonneg_left hvar hc) _))
  have hmark (S : Finset V) : (if W S ≤ m-u then (1:ℝ) else 0) ≤
      Real.exp (θ*(m-u))*Real.exp (-θ*W S) := by
    rw [← Real.exp_add]
    split
    next h => apply Real.one_le_exp_iff.mpr; nlinarith [mul_nonneg hθ.le (sub_nonneg.mpr h)]
    next => exact (Real.exp_pos _).le
  apply (coverage_mono ps hmark ∅).trans
  rw [coverage_smul]
  apply (mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le).trans_eq
  rw [← Real.exp_add]
  congr 1
  have hden : 1-θ*M/3 = v/a := by dsimp [θ]; field_simp [ha.ne']; dsimp [a]; ring
  dsimp only [c]; rw [hden]
  change θ*(m-u)+(-θ*m+θ^2/(2*(v/a))*v) = -u^2/(2*a)
  dsimp only [θ]; field_simp [ha.ne',hv.ne']; ring
/-- Lemma 2.2, the stated lower tail with its denominator 2(V+Mu/3).
The finite laws specify the joint law by independent sampling. -/
public theorem independent_union_lower_tail (ps : List (FiniteLaw (Finset V))) (w : V → ℝ)
    (hw : ∀ x, 0 ≤ w x) (M u : ℝ) (hM : 0 ≤ M) (hu : 0 < u)
    (hmean : ∀ p ∈ ps, p.mean (setWeight w) ≤ M) :
    let W := setWeight w
    let v := (ps.map fun p => p.mean (fun S => W S^2)).sum
    0 < v → coverageAverage ps (fun S => if W S ≤ coverageAverage ps W ∅ - u then 1 else 0) ∅ ≤
      Real.exp (-u^2/(2*(v+M*u/3))) := by
  intro W v hv
  exact independent_union_lower_tail_of_bound ps w hw M u v hM hu hmean le_rfl hv

/-- Zero-second-moment case of Lemma 2.2. The probability of zero covered
weight is exactly one; arbitrary zero-mass subsets may have positive weight. -/
public theorem independent_union_zero (ps : List (FiniteLaw (Finset V))) (w : V → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hv : (ps.map fun p => p.mean (fun S => setWeight w S^2)).sum = 0) :
    coverageAverage ps (fun S => if setWeight w S = 0 then 1 else 0) ∅ = 1 := by
  let W := setWeight w
  have hzero (p : FiniteLaw (Finset V)) (h : p.mean (fun S => W S^2) = 0)
      (S : Finset V) (hS : p.mass S ≠ 0) : W S = 0 := by
    have hn : ∀ X ∈ (univ : Finset (Finset V)), 0 ≤ p.mass X*(W X)^2 :=
      fun X _ => mul_nonneg (p.nonneg X) (sq_nonneg _)
    have hh := (sum_eq_zero_iff_of_nonneg hn).mp h S (mem_univ _)
    exact (sq_eq_zero_iff.mp ((mul_eq_zero.mp hh).resolve_left hS))
  have go (l : List (FiniteLaw (Finset V))) (hl : (l.map fun p => p.mean (fun S => W S^2)).sum = 0)
      (U : Finset V) : coverageAverage l (fun S => if W S = W U then 1 else 0) U = 1 := by
    induction l generalizing U with
    | nil => simp [coverageAverage]
    | cons p tail ih =>
      have hn (q : FiniteLaw (Finset V)) : 0 ≤ q.mean (fun S => W S^2) := q.mean_nonneg _ (fun S => sq_nonneg _)
      have ht : 0 ≤ (tail.map fun q => q.mean (fun S => W S^2)).sum := List.sum_nonneg (by simpa using fun q (_ : q ∈ tail) => hn q)
      simp only [List.map_cons,List.sum_cons] at hl
      have hp : p.mean (fun S => W S^2) = 0 := by linarith [hn p]
      have htail : (tail.map fun q => q.mean (fun S => W S^2)).sum = 0 := by linarith [hn p]
      conv_rhs => rw [← p.mean_const 1]
      apply sum_congr rfl
      intro S _
      by_cases hz : p.mass S = 0
      · simp [hz]
      · have hwS := hzero p hp S hz
        obtain ⟨h1,h2⟩ := gain_bounds ([] : List (FiniteLaw (Finset V))) w hw U S
        change W U ≤ W (U ∪ S) at h1
        change W (U ∪ S)-W U ≤ W S at h2
        have heq : W (U ∪ S) = W U := by linarith
        have hh := ih htail (U ∪ S)
        rw [heq] at hh
        exact congrArg (p.mass S * ·) hh
  have hh := go ps hv ∅
  have he : W ∅ = 0 := by simp [W,setWeight]
  rw [he] at hh
  convert hh using 2
end Vu

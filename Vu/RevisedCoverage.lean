module
public import Vu.Coverage
namespace Vu.Revised
open Finset
variable {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]

/-- One exposure in the revised Lemma 2.2. Only a nonnegative gain and
its second moment enter the exponential estimate. -/
public theorem centered_gain (q : FiniteLaw Ω) (H W : Ω → ℝ) (B θ : ℝ) (hθ : 0 ≤ θ)
    (h : ∀ x, 0 ≤ H x-B ∧ H x-B ≤ W x) :
    q.mean (fun x => Real.exp (θ*(q.mean H-H x))) ≤ Real.exp (θ^2/2*q.mean (fun x => W x^2)) := by
  let Y (x : Ω) := H x-B
  have hm : q.mean Y = q.mean H-B := by simp [Y,FiniteLaw.mean_sub]
  let c := θ^2/2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hpoint x : Real.exp (-θ*Y x) ≤ 1-θ*Y x+c*W x^2 := by
    apply (bernstein_exp_bound (-θ*Y x) 0 (by have ht := mul_nonneg hθ (h x).1; dsimp [Y]; linarith) (by norm_num)).trans
    have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (h x).1 (h x).2 2) hc
    dsimp only [c,Y] at *; linarith
  have ht := q.mean_mono hpoint
  rw [FiniteLaw.mean_add,FiniteLaw.mean_sub,FiniteLaw.mean_const,FiniteLaw.mean_smul,FiniteLaw.mean_smul] at ht
  have he x : Real.exp (θ*(q.mean H-H x)) = Real.exp (θ*q.mean Y)*Real.exp (-θ*Y x) := by
    rw [←Real.exp_add,hm]; dsimp [Y]; congr 1; ring
  simp_rw [he]
  rw [FiniteLaw.mean_smul]
  apply (mul_le_mul_of_nonneg_left ht (Real.exp_pos _).le).trans
  have hb := Real.add_one_le_exp (-θ*q.mean Y+c*q.mean (fun x => W x^2))
  apply (mul_le_mul_of_nonneg_left (by linarith only [hb] : 1-θ*q.mean Y+c*q.mean (fun x => W x^2) ≤ Real.exp (-θ*q.mean Y+c*q.mean (fun x => W x^2))) (Real.exp_pos (θ*q.mean Y)).le).trans_eq
  rw [←Real.exp_add]; congr 1; change θ*q.mean Y+(-θ*q.mean Y+c*q.mean (fun x => W x^2)) = c*q.mean (fun x => W x^2); ring

/-- The revised independent-union lower tail with denominator 2V. -/
public theorem union_lower_tail_of_bound (ps : List (FiniteLaw (Finset V))) (w : V → ℝ) (hw : ∀ x, 0 ≤ w x) (t v : ℝ) (ht : 0 < t) :
    let W := setWeight w
    (ps.map fun q => q.mean (fun S => W S^2)).sum ≤ v → 0 < v → coverageAverage ps (fun S => if W S ≤ coverageAverage ps W ∅-t then 1 else 0) ∅ ≤ Real.exp (-t^2/(2*v)) := by
  intro W hvv hv
  let θ := t/v
  have hθ : 0 ≤ θ := (div_pos ht hv).le
  let c := θ^2/2
  have mgf (qs : List (FiniteLaw (Finset V))) (U : Finset V) :
      coverageAverage qs (fun S => Real.exp (-θ*W S)) U ≤
      Real.exp (-θ*coverageAverage qs W U + c*(qs.map fun q => q.mean (fun S => W S^2)).sum) := by
    induction qs generalizing U with
    | nil => simp [coverageAverage]
    | cons q qs ih =>
      let H S := coverageAverage qs W (U ∪ S)
      let z := (qs.map fun q => q.mean (fun S => W S^2)).sum
      have hg := centered_gain q H W (coverageAverage qs W U) θ hθ (fun S =>
        ⟨sub_nonneg.mpr (gain_bounds qs w hw U S).1,(gain_bounds qs w hw U S).2⟩)
      change q.mean (fun S => coverageAverage qs (fun X => Real.exp (-θ*W X)) (U ∪ S)) ≤
        Real.exp (-θ*q.mean H+c*(q.mean (fun S => W S^2)+z))
      apply (q.mean_mono (fun S => ih (U ∪ S))).trans
      have he S : Real.exp (-θ*H S+c*z) = Real.exp (-θ*q.mean H+c*z)*Real.exp (θ*(q.mean H-H S)) := by
        rw [←Real.exp_add]; congr 1; ring
      change q.mean (fun S => Real.exp (-θ*H S+c*z)) ≤ _
      simp_rw [he]
      rw [FiniteLaw.mean_smul]
      apply (mul_le_mul_of_nonneg_left hg (Real.exp_pos _).le).trans_eq
      rw [←Real.exp_add]; congr 1; dsimp only [c]; ring
  let m := coverageAverage ps W ∅
  have hmark (S : Finset V) : (if W S ≤ m-t then (1:ℝ) else 0) ≤ Real.exp (θ*(m-t))*Real.exp (-θ*W S) := by
    rw [←Real.exp_add]; split
    next h => apply Real.one_le_exp_iff.mpr; linarith only [mul_le_mul_of_nonneg_left h hθ]
    next => exact (Real.exp_pos _).le
  apply (coverage_mono ps hmark ∅).trans
  rw [coverage_smul]
  have hmg : coverageAverage ps (fun S => Real.exp (-θ*W S)) ∅ ≤ Real.exp (-θ*m+c*v) :=
    (mgf ps ∅).trans (Real.exp_le_exp.mpr (add_le_add_right (mul_le_mul_of_nonneg_left hvv (by dsimp [c]; positivity)) _))
  apply (mul_le_mul_of_nonneg_left hmg (Real.exp_pos _).le).trans_eq
  rw [←Real.exp_add]; congr 1
  change θ*(m-t)+(-θ*m+c*v) = -t^2/(2*v)
  dsimp [θ,c]; field_simp; ring
public theorem union_lower_tail (ps : List (FiniteLaw (Finset V))) (w : V → ℝ) (hw : ∀ x, 0 ≤ w x) (t : ℝ) (ht : 0 < t) :
    let W := setWeight w
    let v := (ps.map fun q => q.mean (fun S => W S^2)).sum
    0 < v → coverageAverage ps (fun S => if W S ≤ coverageAverage ps W ∅-t then 1 else 0) ∅ ≤ Real.exp (-t^2/(2*v)) := by
  intro W v hv
  exact union_lower_tail_of_bound ps w hw t v ht le_rfl hv
end Vu.Revised

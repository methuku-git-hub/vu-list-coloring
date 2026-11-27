module
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
namespace Vu

/-- The one-sided exponential estimate used in the proof of Lemma 2.2.
The rational function majorizing exp has logarithmic comparison with
derivative of the sign of x³, on the whole interval x < 3. -/
public theorem bernstein_exp_bound (x M : ℝ) (hx : x ≤ M) (hM : M < 3) :
    Real.exp x ≤ 1+x+x^2/(2*(1-M/3)) := by
  let f (u : ℝ) := ((u^2+4*u+6)/(6-2*u))*Real.exp (-u)
  have derivF (u : ℝ) (hu : u < 3) :
      HasDerivAt f (2*u^3*Real.exp (-u)/(6-2*u)^2) u := by
    have hden : (6:ℝ)-2*u ≠ 0 := by linarith
    have hX := hasDerivAt_id u
    have hnum := (((hX.pow 2).add (hX.const_mul 4)).add_const 6)
    have hden' := (hasDerivAt_const u (6:ℝ)).sub (hX.const_mul 2)
    have hraw := (hnum.div hden' hden).mul hX.neg.exp
    convert hraw using 1
    · rfl
    · dsimp; field_simp; ring
  have hmin : f 0 ≤ f x := by
    by_cases hl : 0 ≤ x
    · let S := Set.Icc (0:ℝ) x
      have du (u : ℝ) (hu : u ∈ S) := derivF u (hu.2.trans_lt (hx.trans_lt hM))
      have hm : MonotoneOn f S := monotoneOn_of_deriv_nonneg (convex_Icc ..)
        (fun u hu => (du u hu).continuousAt.continuousWithinAt)
        (fun u hu => (du u (interior_subset hu)).differentiableAt.differentiableWithinAt) (by
          intro u hu
          have h := interior_subset hu
          rw [(du u h).deriv]
          have hnon : 0 ≤ u := h.1
          positivity)
      exact hm ⟨le_rfl,hl⟩ ⟨hl,le_rfl⟩ hl
    · have hl' := le_of_not_ge hl
      let S := Set.Icc x (0:ℝ)
      have du (u : ℝ) (hu : u ∈ S) := derivF u (hu.2.trans_lt (by norm_num))
      have hm : AntitoneOn f S := antitoneOn_of_deriv_nonpos (convex_Icc ..)
        (fun u hu => (du u hu).continuousAt.continuousWithinAt)
        (fun u hu => (du u (interior_subset hu)).differentiableAt.differentiableWithinAt) (by
          intro u hu
          have h := interior_subset hu
          rw [(du u h).deriv]
          have hn : u^3 ≤ 0 := by nlinarith only [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg u) h.2]
          exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hn) (Real.exp_pos _).le) (sq_nonneg _))
      exact hm ⟨le_rfl,hl'⟩ ⟨hl',le_rfl⟩ hl'
  have hden : 0 < 6-2*x := by linarith
  have hcmp : Real.exp x ≤ (x^2+4*x+6)/(6-2*x) := by
    have h0 : f 0 = 1 := by norm_num [f]
    rw [h0] at hmin
    have haux : 1 ≤ ((x^2+4*x+6)/(6-2*x))/Real.exp x := by
      simpa only [f,Real.exp_neg,div_eq_mul_inv] using hmin
    simpa using (le_div_iff₀ (Real.exp_pos x)).mp haux
  calc
    _ ≤ _ := hcmp
    _ = 1+x+x^2/(2*(1-x/3)) := by
      rw [show 2*(1-x/3) = (6-2*x)/3 by ring,div_div_eq_mul_div]
      rw [add_div' _ _ _ hden.ne']; congr 1; ring
    _ ≤ _ := add_le_add_right (div_le_div_of_nonneg_left (sq_nonneg x) (by linarith : 0 < 2*(1-M/3)) (by linarith : 2*(1-M/3) ≤ 2*(1-x/3))) _
end Vu

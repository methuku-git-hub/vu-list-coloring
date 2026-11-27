module
public import Vu.Bernstein
namespace Vu
open Finset

/-- A probability law on a finite outcome space; zero-mass outcomes are allowed. -/
public structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ u, 0 ≤ mass u
  total : ∑ u, mass u = 1

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω] (p : FiniteLaw Ω)

@[expose] public noncomputable def mean (f : Ω → ℝ) : ℝ := ∑ u, p.mass u*f u

@[simp] public theorem mean_const (c : ℝ) : p.mean (fun _ => c) = c := by simp [mean,←sum_mul,p.total]
public theorem mean_add (f g : Ω → ℝ) : p.mean (fun u => f u + g u) = p.mean f+p.mean g := by simp [mean,mul_add,sum_add_distrib]
public theorem mean_sub (f g : Ω → ℝ) : p.mean (fun u => f u - g u) = p.mean f-p.mean g := by simp [mean,mul_sub,sum_sub_distrib]
public theorem mean_smul (a : ℝ) (f : Ω → ℝ) : p.mean (fun u => a*f u) = a*p.mean f := by simp [mean,mul_left_comm,mul_sum]
public theorem mean_mono {f g : Ω → ℝ} (h : ∀ u, f u ≤ g u) : p.mean f ≤ p.mean g :=
  sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (h u) (p.nonneg u)
public theorem mean_nonneg (f : Ω → ℝ) (h : ∀ u, 0 ≤ f u) : 0 ≤ p.mean f :=
  sum_nonneg fun u _ => mul_nonneg (p.nonneg u) (h u)

/-- A one-step centered exponential bound for a gain depending on one
coordinate. A fixed baseline h₀ may be subtracted before taking the second
moment, retaining a bound in terms of the added set alone. -/
public theorem mean_exp_gain (h w : Ω → ℝ) (h₀ M θ : ℝ) (hθ : 0 ≤ θ) (hθM : θ*M < 3)
    (hb : ∀ u, h₀ ≤ h u ∧ h u-h₀ ≤ w u) (hm : p.mean w ≤ M) :
    p.mean (fun u => Real.exp (θ*(p.mean h-h u))) ≤
      Real.exp ((θ^2/(2*(1-θ*M/3)))*p.mean (fun u => w u^2)) := by
  let v u := h u-h₀
  let z u := p.mean h-h u
  let c := θ^2/(2*(1-θ*M/3))
  have hden : 0 < 2*(1-θ*M/3) := by linarith
  have hc : 0 ≤ c := div_nonneg (sq_nonneg _) hden.le
  have hv : p.mean v = p.mean h-h₀ := by simp only [v,mean_sub,mean_const]
  have hz0 : p.mean z = 0 := by simp only [z,mean_sub,mean_const,sub_self]
  have hu (u : Ω) : z u ≤ M := by
    have hh := (p.mean_mono (fun j => (hb j).2)).trans hm
    change p.mean v ≤ M at hh
    dsimp only [z]; linarith [hb u]
  have hzvar : p.mean (fun u => z u^2) ≤ p.mean (fun u => w u^2) := by
    have hrewrite : (fun u => z u^2) = fun u => v u^2-(2*p.mean v)*v u+(p.mean v)^2 := by
      funext u; rw [hv]; dsimp [v,z]; ring
    rw [hrewrite,mean_add,mean_sub,mean_smul,mean_const]
    have hvm := p.mean_mono (fun u => pow_le_pow_left₀ (sub_nonneg.mpr (hb u).1) (hb u).2 2)
    change p.mean (fun u => v u^2) ≤ _ at hvm
    nlinarith [sq_nonneg (p.mean v)]
  have hpoint (u : Ω) : Real.exp (θ*z u) ≤ 1+θ*z u+c*z u^2 := by
    apply (bernstein_exp_bound (θ*z u) (θ*M) (mul_le_mul_of_nonneg_left (hu u) hθ) hθM).trans_eq
    dsimp only [c]; ring
  apply (p.mean_mono hpoint).trans
  rw [mean_add,mean_add,mean_smul,mean_const,mean_smul,hz0,mul_zero,add_zero]
  exact (add_le_add_right (mul_le_mul_of_nonneg_left hzvar hc) 1).trans (by simpa [add_comm] using Real.add_one_le_exp (c*p.mean (fun u => w u^2)))
end FiniteLaw
end Vu

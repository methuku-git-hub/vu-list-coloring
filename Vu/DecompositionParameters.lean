module
public import Vu.SoftMatrix
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
namespace Vu
open Finset

/-- Choose the auxiliary parameters in Section 4 simultaneously so that
the complete right side of the matrix norm estimate is at most η. -/
public theorem choose_decomposition_parameters (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    let lam := min (η/10) (1/2)
    let r := ⌈1/(lam^2/8)⌉₊
    let δ := ε/200
    ∃ (ω ρ : ℝ) (k₀ D₀ : ℕ), 0 < ω ∧ 0 < ρ ∧ ρ < 1/4 ∧ 0 < k₀ ∧
      (r : ℝ)^3*ω ≤ δ ∧ 8*r*√ρ ≤ δ/4 ∧ ∀ D ≥ D₀,
      lam + ((r:ℝ)^3/δ+r^2)*ω + 2*r/k₀ + (r+1)/(D:ℝ) +
        2*r*((4*ρ)^(1/3:ℝ)/δ+3*ρ^(1/4:ℝ)) ≤ η := by
  intro lam r δ
  have hl : 0 < lam := lt_min (by positivity) (by norm_num)
  have hrn : 0 < r := Nat.ceil_pos.mpr (by positivity)
  have hr : 0 < (r:ℝ) := Nat.cast_pos.mpr hrn
  have hd : 0 < δ := by dsimp [δ]; positivity
  let W := (r:ℝ)^3/δ+r^2
  have hw : 0 < W := by dsimp [W]; positivity
  let ω := min (δ/r^3) (η/(10*W))
  have hω : 0 < ω := lt_min (by positivity) (by positivity)
  let f (x : ℝ) := 8*r*√x + 2*r*((4*x)^(1/3:ℝ)/δ+3*x^(1/4:ℝ))
  have hf : ContinuousAt f 0 := by
    dsimp [f]
    have h₁ : Continuous (fun x : ℝ => (4*x)^(1/3:ℝ)) :=
      (Real.continuous_rpow_const (by norm_num)).comp (continuous_const.mul continuous_id)
    have h₂ := Real.continuous_rpow_const (by norm_num : (0:ℝ) ≤ 1/4)
    exact ((continuous_const.mul Real.continuous_sqrt).add
      (continuous_const.mul ((h₁.div_const _).add (continuous_const.mul h₂)))).continuousAt
  have hf0 : f 0 = 0 := by norm_num [f,Real.zero_rpow]
  let tol := min (δ/4) (η/10)
  have htol : 0 < tol := lt_min (by positivity) (by positivity)
  obtain ⟨d,hd',hsmall⟩ := Metric.continuousAt_iff.mp hf tol htol
  let ρ := min (d/2) (1/8)
  have hρ : 0 < ρ := lt_min (by positivity) (by norm_num)
  have hρ₁ : ρ < 1/4 := (min_le_right _ _).trans_lt (by norm_num)
  have hnear : dist ρ 0 < d := by rw [Real.dist_eq,sub_zero,abs_of_pos hρ]; exact (min_le_left _ _).trans_lt (by linarith)
  have hval := hsmall hnear
  rw [hf0,Real.dist_eq,sub_zero] at hval
  have hsmall' := (le_abs_self _).trans hval.le
  have hterm : 0 ≤ 2*r*((4*ρ)^(1/3:ℝ)/δ+3*ρ^(1/4:ℝ)) := by positivity
  let k₀ := ⌈20*(r:ℝ)/η⌉₊
  let D₀ := ⌈10*((r:ℝ)+1)/η⌉₊
  have hk : 0 < k₀ := Nat.ceil_pos.mpr (by positivity)
  have hD : 0 < D₀ := Nat.ceil_pos.mpr (by positivity)
  refine ⟨ω,ρ,k₀,D₀,hω,hρ,hρ₁,hk,?_,?_,?_⟩
  · have h := (le_div_iff₀ (by positivity : 0 < (r:ℝ)^3)).mp (min_le_left (δ/(r:ℝ)^3) (η/(10*W)))
    simpa [ω,mul_comm] using h
  · dsimp only [f,tol] at hsmall'
    linarith [hsmall'.trans (min_le_left _ _)]
  · intro D hDD
    have h1 : lam ≤ η/10 := min_le_left _ _
    have h2 := (le_div_iff₀ (by positivity : 0 < 10*W)).mp (min_le_right (δ/(r:ℝ)^3) (η/(10*W)))
    change ω*(10*W) ≤ η at h2
    have h3 := (div_le_iff₀ hη).mp (Nat.le_ceil (20*(r:ℝ)/η))
    change 20*(r:ℝ) ≤ k₀*η at h3
    have h4 := (div_le_iff₀ hη).mp ((Nat.le_ceil (10*((r:ℝ)+1)/η)).trans (Nat.cast_le.mpr hDD))
    have hkbound : 2*(r:ℝ)/k₀ ≤ η/10 := (div_le_iff₀ (Nat.cast_pos.mpr hk)).mpr (by linarith)
    have hDbound : ((r:ℝ)+1)/D ≤ η/10 := (div_le_iff₀ (Nat.cast_pos.mpr (hD.trans_le hDD))).mpr (by linarith)
    have h5 := hsmall'.trans (min_le_right _ _)
    have h6 : 0 ≤ 8*(r:ℝ)*√ρ := by positivity
    dsimp only [f] at h5
    change lam + W*ω + _ + _ + _ ≤ η
    linarith only [h1,h2,hkbound,hDbound,h5,h6,hη]
end Vu

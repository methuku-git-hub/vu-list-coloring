module
public import Vu.RevisedParameters
public import Vu.RevisedHard
namespace Vu.Revised
open Finset
/-- For arbitrary ε and η in Proposition 3.1, construct the actual common
witness for (D1), (D2), (D4), all entry conditions, and the parameter
budget in Lemma 4.6. Only the two analytic bounds on this particular
matrix remain to obtain a full Decomposition. -/
public theorem partial_decomposition (ε η : ℝ) (hε : 0 < ε) (hε₁ : ε ≤ 1) (hη : 0 < η) :
    let lam := min (η/10) (1/2)
    let r := ⌈1/(lam/8)⌉₊
    let δ := ε/200
    let Rmax := ⌈4/ε⌉₊+2
    ∃ (ω ρ : ℝ) (k₀ K D₀ : ℕ), 0 < ω ∧ 0 < ρ ∧ ρ < 1/4 ∧ 0 < k₀ ∧ 0 < K ∧
      (r : ℝ)^3*ω ≤ δ ∧ 8*r*√ρ ≤ δ/4 ∧ ∀ (D : ℕ), D ≥ D₀ →
      lam + ((r:ℝ)^3/δ+r^2)*ω + 2*r/k₀ + (r+1)/(D:ℝ) +
        2*r*((4*ρ)^(1/3:ℝ)/δ+3*ρ^(1/4:ℝ)) ≤ η ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        (∀ x, G.degree x ≤ D) →
        let k := ⌊(maxCodegree G : ℝ)+ε*D⌋₊
        ε/2*D ≤ k ∧ k ≤ 2*D ∧
        Nonempty (HardDecomposition G D r k₀ K k Rmax lam ω ρ δ (ε/8) η) := by
  classical
  intro lam r δ Rmax
  obtain ⟨ω,ρ,k₀,D₂,hω,hρ,hρ₁,hk₀,ho,hs,hbudget⟩ := choose_decomposition_parameters ε η hε hη
  have hl : 0 < lam := lt_min (by positivity) (by norm_num)
  have hd : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨K,hK,D₁,hD₁⟩ := hard_decomposition ε η lam ω ρ k₀ hε hε₁ hη hl hω hρ hρ₁ hk₀ ho hs
  refine ⟨ω,ρ,k₀,K,max D₁ D₂,hω,hρ,hρ₁,hk₀,hK,ho,hs,?_⟩
  intro D hD
  refine ⟨hbudget D ((le_max_right _ _).trans hD),?_⟩
  intro V _ _ G _ hdeg k
  obtain ⟨hlo,hhi,⟨h⟩⟩ := hD₁ D ((le_max_left _ _).trans hD) V G hdeg
  exact ⟨hlo,hhi,⟨h⟩⟩

end Vu.Revised

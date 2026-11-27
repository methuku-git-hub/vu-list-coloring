module
public import Vu.ProductVariance
namespace Vu.Revised
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] public noncomputable def activation (lam : ℝ) := lam/(1+lam)

public theorem activation_odds (lam : ℝ) (h : 0 ≤ lam) :
    0 ≤ activation lam ∧ activation lam < 1 ∧ activation lam/(1-activation lam) = lam := by
  have hh : 0 < 1+lam := by linarith
  have hp : lam/(1+lam) < 1 := (div_lt_iff₀ hh).mpr (by linarith)
  refine ⟨div_nonneg h hh.le,hp,?_⟩
  unfold activation
  field_simp
  ring

/-- The two-moment identity of the revised proof (Lemma 2.1), including
the exponential upper bound when signed entries of two rows differ. -/
public theorem two_moments (M : ℝ) (hM : 1 ≤ M) (lam f g : V → ℝ)
    (h : ∀ z, 0 ≤ lam z ∧ lam z ≤ 1/M) (hf : ∀ z, -1 ≤ f z ∧ f z ≤ M)
    (hg : ∀ z, -1 ≤ g z ∧ g z ≤ M) :
    let p := fun z => activation (lam z)
    let X := Bernoulli.multiplier p
    (∀ ω, 0 ≤ X f ω) ∧ Bernoulli.expect p (X f) = 1 ∧
    Bernoulli.expect p (fun ω => X f ω*X g ω) = ∏ z, (1+lam z*f z*g z) ∧
    (∏ z, (1+lam z*f z*g z)) ≤ Real.exp (∑ z, lam z*f z*g z) := by
  intro p X
  have hm : 0 < M := by linarith
  have hp z := activation_odds (lam z) (h z).1
  have hl z : M*lam z ≤ 1 := by linarith only [(le_div_iff₀ hm).mp (h z).2]
  refine ⟨Bernoulli.multiplier_nonneg p f M (fun z => (hp z).1) (fun z => (hp z).2.1) hf (fun z => ?_),
    Bernoulli.expect_multiplier p f (fun z => (hp z).2.1),?_,?_⟩
  · dsimp only [p]; rw [(hp z).2.2]; exact hl z
  · apply (Bernoulli.joint_moment p f g (fun z => (hp z).2.1)).trans
    apply prod_congr rfl; intro z _
    dsimp only [p]; rw [(hp z).2.2]; ring
  · rw [Real.exp_sum]
    apply prod_le_prod₀ _ (fun z _ => by simpa [add_comm] using Real.add_one_le_exp (lam z*f z*g z))
    intro z _
    have hfg : -M ≤ f z*g z := by
      by_cases h1 : 0 ≤ f z
      · nlinarith only [mul_nonneg h1 (by linarith [(hg z).1] : 0 ≤ g z+1),(hf z).2]
      · nlinarith only [mul_nonneg (by linarith : 0 ≤ -f z) (sub_nonneg.mpr (hg z).2),
          mul_nonneg hm.le (by linarith [(hf z).1] : 0 ≤ 1+f z)]
    linarith only [mul_le_mul_of_nonneg_left hfg (h z).1,hl z]
end Vu.Revised

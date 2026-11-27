module
public import Vu.OfferCoverage
public import Vu.ProductVariance
public import Vu.Reduction
namespace Vu
open Finset

namespace FiniteLaw
variable {Ω X : Type*} [Fintype Ω] [Fintype X] [DecidableEq X]

@[expose] public noncomputable def map (p : FiniteLaw Ω) (f : Ω → X) : FiniteLaw X where
  mass x := ∑ u, if f u = x then p.mass u else 0
  nonneg x := sum_nonneg (fun u _ => by split <;> first | exact p.nonneg u | exact le_rfl)
  total := by rw [sum_comm]; simpa using p.total

public theorem mean_map (p : FiniteLaw Ω) (f : Ω → X) (g : X → ℝ) :
    (p.map f).mean g = p.mean (fun u => g (f u)) := by
  simp only [mean,map,sum_mul,ite_mul,zero_mul]
  rw [sum_comm]
  simp

public theorem mean_sum_finset {I : Type*} (p : FiniteLaw Ω) (s : Finset I) (f : I → Ω → ℝ) :
    p.mean (fun u => ∑ i ∈ s, f i u) = ∑ i ∈ s, p.mean (f i) := by
  simp only [mean,mul_sum]; rw [sum_comm]
end FiniteLaw

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Independent marks for one color on the original vertex type.
Taking p(x)=0 outside a list allows all colors to use one sample space. -/
@[expose] public noncomputable def markLaw (p : V → ℝ) (h₀ : ∀ x, 0 ≤ p x) (h₁ : ∀ x, p x ≤ 1) :
    FiniteLaw (V → Bool) where
  mass ω := ∏ x, Bernoulli.mass (p x) (ω x)
  nonneg ω := prod_nonneg (fun x _ => by cases he : ω x <;> simp [Bernoulli.mass,he,h₀,h₁])
  total := by
    rw [← Fintype.prod_sum]
    simp [Bernoulli.mass]

/-- Exact probability that all marks in S are present and that all marks
in the disjoint set N are absent. The formula allows zero probabilities. -/
public theorem mark_cylinder (p : V → ℝ) (h₀ : ∀ x, 0 ≤ p x) (h₁ : ∀ x, p x ≤ 1)
    (S N : Finset V) (hd : Disjoint S N) :
    (markLaw p h₀ h₁).mean (fun ω => if (∀ x ∈ S, ω x = true) ∧ (∀ x ∈ N, ω x = false) then 1 else 0) =
      (∏ x ∈ S, p x)*∏ x ∈ N, (1-p x) := by
  classical
  let ind (x : V) (b : Bool) : ℝ := if (x ∈ S → b = true) ∧ (x ∈ N → b = false) then 1 else 0
  have hind (ω : V → Bool) :
      (if (∀ x ∈ S, ω x = true) ∧ (∀ x ∈ N, ω x = false) then (1:ℝ) else 0) = ∏ x, ind x (ω x) := by
    split
    next h => symm; exact prod_eq_one (fun x _ => if_pos ⟨h.1 x,h.2 x⟩)
    next h =>
      push_neg at h
      symm
      by_cases hm : ∀ x ∈ S, ω x = true
      · obtain ⟨x,hx,hn⟩ := h hm
        exact prod_eq_zero (mem_univ x) (show ind x (ω x) = 0 from if_neg (fun h => (by simpa [hn] using h.2 hx : False)))
      · push_neg at hm
        obtain ⟨x,hx,hn⟩ := hm
        exact prod_eq_zero (mem_univ x) (show ind x (ω x) = 0 from if_neg (fun h => (by simpa [hn] using h.1 hx : False)))

  have hprod (x : V) : (∑ b : Bool, Bernoulli.mass (p x) b * ind x b) =
      (if x ∈ S then p x else 1)*(if x ∈ N then 1-p x else 1) := by
    by_cases hs : x ∈ S
    · have hn : x ∉ N := fun hn => disjoint_left.mp hd hs hn
      simp [ind,hs,hn,Bernoulli.mass]
    · by_cases hn : x ∈ N <;> simp [ind,hs,hn,Bernoulli.mass]
  have he : (markLaw p h₀ h₁).mean (fun ω => ∏ x, ind x (ω x)) =
      ∏ x, ∑ b : Bool, Bernoulli.mass (p x) b*ind x b := by
    simp only [FiniteLaw.mean,markLaw,Fintype.prod_sum,prod_mul_distrib]
  simp_rw [hind]
  rw [he]
  simp_rw [hprod]
  rw [prod_mul_distrib]
  simp

@[expose] public noncomputable def offerSet (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (ω : V → Bool) : Finset V :=
  T.filter fun x => ω x = true ∧ ∀ y ∈ G.neighborFinset x, ω y = false

@[expose] public noncomputable def offerLaw (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) (p : V → ℝ) (h₀ : ∀ x, 0 ≤ p x) (h₁ : ∀ x, p x ≤ 1) : FiniteLaw (Finset V) :=
  (markLaw p h₀ h₁).map (offerSet G T)

/-- Actual offer probability, before the vertex accepts any of its offers. -/
public theorem offer_probability (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V)
    (p : V → ℝ) (h₀ : ∀ x, 0 ≤ p x) (h₁ : ∀ x, p x ≤ 1) (x : V) (hx : x ∈ T) :
    hitProbability (offerLaw G T p h₀ h₁) x = p x * ∏ y ∈ G.neighborFinset x, (1-p y) := by
  unfold hitProbability offerLaw
  rw [FiniteLaw.mean_map]
  simpa [offerSet,hx] using mark_cylinder p h₀ h₁ {x} (G.neighborFinset x) (by simp)

private theorem no_marks_product_lower (p : V → ℝ) (h₀ : ∀ x, 0 ≤ p x) (h₁ : ∀ x, p x ≤ 1)
    (N : Finset V) : 1-∑ y ∈ N, p y ≤ ∏ y ∈ N, (1-p y) := by
  induction N using Finset.induction_on with
  | empty => simp
  | insert y N hy ih =>
    rw [sum_insert hy,prod_insert hy]
    apply le_trans _ (mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr (h₁ y)))
    nlinarith [mul_nonneg (h₀ y) (sum_nonneg (s := N) (fun z _ => h₀ z))]

public theorem offer_probability_lower (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V)
    (p : V → ℝ) (h₀ : ∀ x, 0 ≤ p x) (h₁ : ∀ x, p x ≤ 1) (x : V) (hx : x ∈ T)
    (ν : ℝ) (hN : 0 < p x → ∑ y ∈ G.neighborFinset x, p y ≤ ν) :
    (1-ν)*p x ≤ hitProbability (offerLaw G T p h₀ h₁) x := by
  rw [offer_probability G T p h₀ h₁ x hx,mul_comm (p x)]
  rcases (h₀ x).eq_or_lt with hz | hp
  · simp [←hz]
  · apply mul_le_mul_of_nonneg_right _ hp.le
    exact (sub_le_sub_left (hN hp) 1).trans (no_marks_product_lower p h₀ h₁ _)
end Vu

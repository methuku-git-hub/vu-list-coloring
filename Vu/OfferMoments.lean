module
public import Vu.MarkLaw
namespace Vu
open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

@[expose] public def markIndicator (ω : V → Bool) (x : V) : ℝ := if ω x then 1 else 0
@[expose] public noncomputable def markCount (T : Finset V) (ω : V → Bool) : ℝ := ∑ x ∈ T, markIndicator ω x

public theorem mark_indicator_mean (p : V → ℝ) (h₀ : ∀ x, 0 ≤ p x) (h₁ : ∀ x, p x ≤ 1) (x : V) :
    (markLaw p h₀ h₁).mean (fun ω => markIndicator ω x) = p x := by
  simpa [markIndicator] using mark_cylinder p h₀ h₁ {x} ∅ (by simp)

public theorem mark_count_moments (T : Finset V) (p : V → ℝ) (h₀ : ∀ x, 0 ≤ p x) (h₁ : ∀ x, p x ≤ 1) :
    let μ := markLaw p h₀ h₁
    let lam := ∑ x ∈ T, p x
    μ.mean (markCount T) = lam ∧ μ.mean (fun ω => markCount T ω^2) ≤ lam+lam^2 := by
  classical
  intro μ lam
  have hxy (x y : V) : μ.mean (fun ω => markIndicator ω x*markIndicator ω y) ≤
      p x*p y + (if x=y then p x else 0) := by
    by_cases he : x=y
    · subst y
      have eq (ω : V → Bool) : markIndicator ω x*markIndicator ω x = markIndicator ω x := by
        cases h : ω x <;> simp [markIndicator,h]
      simp only [eq,μ,mark_indicator_mean,ite_true]
      nlinarith [sq_nonneg (p x)]
    · have hh := mark_cylinder p h₀ h₁ {x,y} ∅ (by simp)
      simp only [mem_insert,mem_singleton,forall_eq_or_imp,forall_eq,notMem_empty,
        false_implies,implies_true,and_true,prod_empty,mul_one] at hh
      have hprod (ω : V → Bool) : markIndicator ω x*markIndicator ω y =
          (if (∀ z ∈ ({x,y}:Finset V), ω z = true) then 1 else 0) := by
        cases hx : ω x <;> cases hy : ω y <;> simp [markIndicator,hx,hy]
      simp only [hprod,if_neg he,add_zero]
      apply le_of_eq
      simpa [μ,he] using hh
  refine ⟨?_,?_⟩
  · unfold markCount
    rw [FiniteLaw.mean_sum_finset]; exact sum_congr rfl (fun x _ => mark_indicator_mean p h₀ h₁ x)
  · have heq (ω : V → Bool) : markCount T ω^2 =
        ∑ x ∈ T, ∑ y ∈ T, markIndicator ω x*markIndicator ω y := by
      unfold markCount
      rw [pow_two,sum_mul]; simp only [mul_sum]
    simp only [heq,FiniteLaw.mean_sum_finset]
    apply (sum_le_sum (fun x (_ : x ∈ T) => sum_le_sum (fun y (_ : y ∈ T) => hxy x y))).trans_eq
    simp only [sum_add_distrib,←mul_sum,←sum_mul]
    change _ = lam+lam^2
    simp [lam,pow_two,Finset.sum_ite_eq_of_mem,add_comm]

/-- The M and V inputs of Lemma 2.2 for one actual offer distribution.
The proof uses independence of marks at different vertices within the color;
it does not assume independence of offers at those vertices. -/
public theorem offer_law_moments (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V)
    (p : V → ℝ) (h₀ : ∀ x, 0 ≤ p x) (h₁ : ∀ x, p x ≤ 1) (w : V → ℝ) (K : ℝ)
    (hw : ∀ x, 0 ≤ w x) (hK : 0 ≤ K) (hcap : ∀ x ∈ T, w x ≤ K) :
    let q := offerLaw G T p h₀ h₁
    let lam := ∑ x ∈ T, p x
    q.mean (setWeight w) ≤ K*lam ∧ q.mean (fun S => setWeight w S^2) ≤ K^2*(lam+lam^2) := by
  classical
  intro q lam
  have hmark (ω : V → Bool) : setWeight w (offerSet G T ω) ≤ K*markCount T ω := by
    simp only [setWeight,offerSet,markCount,sum_filter,mul_sum]
    apply sum_le_sum
    intro x hx
    split
    next h => simpa [markIndicator,h.1] using hcap x hx
    next => cases he : ω x <;> simp [markIndicator,he,hK]
  have hsq (ω : V → Bool) : setWeight w (offerSet G T ω)^2 ≤ K^2*markCount T ω^2 := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (sum_nonneg (fun x _ => hw x)) (hmark ω)
  obtain ⟨hm,hv⟩ := mark_count_moments T p h₀ h₁
  change (offerLaw ..).mean _ ≤ _ ∧ (offerLaw ..).mean _ ≤ _
  dsimp only [q,offerLaw]
  simp only [FiniteLaw.mean_map]
  refine ⟨((markLaw p h₀ h₁).mean_mono hmark).trans_eq ?_,((markLaw p h₀ h₁).mean_mono hsq).trans ?_⟩
  · rw [FiniteLaw.mean_smul,hm]
  · rw [FiniteLaw.mean_smul]
    exact mul_le_mul_of_nonneg_left hv (sq_nonneg _)
end Vu

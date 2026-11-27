module
public import Vu.ProductLaw
public import Vu.LocalLemma
namespace Vu
open Finset

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

@[expose] public noncomputable def chance (p : FiniteLaw Ω) (E : Ω → Prop) : ℝ := by
  classical exact p.mean fun a => if E a then 1 else 0

public theorem chance_nonneg (p : FiniteLaw Ω) (E : Ω → Prop) : 0 ≤ p.chance E :=
  p.mean_nonneg _ (fun a => by split <;> norm_num)

public theorem exists_of_chance_pos (p : FiniteLaw Ω) (E : Ω → Prop) (h : 0 < p.chance E) :
    ∃ a, 0 < p.mass a ∧ E a := by
  classical
  by_contra! hn
  have hz (a : Ω) : p.mass a*(if E a then (1:ℝ) else 0) = 0 := by
    by_cases he : E a
    · have hm : p.mass a = 0 := (p.nonneg a).antisymm' (le_of_not_gt (fun h => hn a h he))
      simp [hm]
    · simp [he]
  have h0 : p.chance E = 0 := sum_eq_zero (fun a _ => hz a)
  linarith

/-- Finite product-space Local Lemma with the dependency graph constructed
from the coordinates determining each bad event. -/
public theorem coordinate_local_lemma {I X J : Type*} [Fintype I] [DecidableEq I] [Fintype X]
    [Fintype J] [DecidableEq J] (q : I → FiniteLaw X) (A : J → (I → X) → Prop)
    (S : J → Finset I) (hdet : ∀ j, determinedBy (S j) (A j)) (t : J → ℝ) (ht : ∀ j, 0 ≤ t j ∧ t j < 1)
    (hsmall : ∀ j, (independent q).chance (A j) ≤ t j *
      (by classical exact ∏ k ∈ univ.filter (fun k => ¬Disjoint (S j) (S k)), (1-t k))) :
    ∃ a : I → X, 0 < (independent q).mass a ∧ ∀ j, ¬A j a := by
  classical
  let μ := independent q
  let Γ j := univ.filter (fun k => ¬Disjoint (S j) (S k))
  let ok (T : Finset J) (a : I → X) := ∀ j ∈ T, ¬A j a
  let P (T : Finset J) := μ.chance (ok T)
  have hstep (T : Finset J) (i : J) (_ : i ∉ T) : P T-P (insert i T) ≤ μ.chance (A i)*P (T \ Γ i) := by
    let U := T \ Γ i
    let left (a : I → X) : ℝ := if A i a then 1 else 0
    let right (a : I → X) : ℝ := if ok U a then 1 else 0
    have hleft : determinedBy (S i) left := by
      intro a b h; dsimp [left]; rw [hdet i a b h]
    have hright : determinedBy (U.biUnion S) right := by
      intro a b hab
      have hh : ok U a ↔ ok U b := by
        unfold ok
        apply forall_congr'; intro j
        by_cases hj : j ∈ U
        · rw [hdet j a b (fun x hx => hab x (mem_biUnion.mpr ⟨j,hj,hx⟩))]
        · simp [hj]
      simp only [right,hh]
    have hd : Disjoint (S i) (U.biUnion S) := disjoint_left.mpr (by
      intro v hi hu
      obtain ⟨j,hj,hv⟩ := mem_biUnion.mp hu
      exact (mem_sdiff.mp hj).2 (mem_filter.mpr ⟨mem_univ _,fun h => disjoint_left.mp h hi hv⟩))
    have hind := independent_disjoint q _ _ left right hleft hright hd
    have hind' : μ.mean (fun a => left a*right a) = μ.chance (A i)*P U := by
      apply hind.trans
      congr 2
      funext a
      by_cases h : ok U a <;> simp [right,h]
    rw [← hind']
    change μ.mean _ - μ.mean _ ≤ _
    rw [← mean_sub]
    apply μ.mean_mono
    intro a
    have hi : ok (insert i T) a ↔ ¬A i a ∧ ok T a := by simp [ok]
    by_cases hv : ok T a
    · have hu : ok U a := fun j hj => hv j (mem_sdiff.mp hj).1
      by_cases he : A i a <;> simp [left,right,hi,hv,hu,he]
    · by_cases he : A i a <;> by_cases hu : ok U a <;> simp [left,right,hi,hv,he,hu]
  have hzero : P ∅ = 1 := by simp [P,chance,ok,mean_const]
  have hh := local_lemma_product P (fun i => μ.chance (A i)) t Γ
    (fun T => chance_nonneg μ _) hzero (fun i => (ht i).1) (fun i => (ht i).2.le) hsmall hstep univ
  obtain ⟨a,hm,ha⟩ := exists_of_chance_pos μ (ok univ)
    ((prod_pos (fun j _ => sub_pos.mpr (ht j).2)).trans_le hh)
  exact ⟨a,hm,fun j => ha j (mem_univ _)⟩
public theorem coordinate_lll_small_mass {I X J : Type*} [Fintype I] [DecidableEq I] [Fintype X]
    [Fintype J] [DecidableEq J] (q : I → FiniteLaw X) (A : J → (I → X) → Prop)
    (S : J → Finset I) (hdet : ∀ j, determinedBy (S j) (A j))
    (hp : ∀ j, (independent q).chance (A j) < 1/2)
    (hdep : ∀ j, (by classical exact ∑ k ∈ univ.filter (fun k => ¬Disjoint (S j) (S k)), (independent q).chance (A k)) ≤ (1/4:ℝ)) :
    ∃ a : I → X, 0 < (independent q).mass a ∧ ∀ j, ¬A j a := by
  classical
  let p j := (independent q).chance (A j)
  let Γ j := univ.filter fun k => ¬Disjoint (S j) (S k)
  have ht i : 0 ≤ 2*p i ∧ 2*p i < 1 := ⟨mul_nonneg (by norm_num) (chance_nonneg _ _),by dsimp [p]; linarith [hp i]⟩
  apply coordinate_local_lemma q A S hdet (fun j => 2*p j) ht
  intro i
  have hh := one_sub_sum_le_prod (Γ i) (fun j => 2*p j) (fun j => (ht j).1) (fun j => (ht j).2.le)
  rw [←mul_sum] at hh
  have hd : ∑ j ∈ Γ i, p j ≤ 1/4 := hdep i
  have hlo : 1/2 ≤ ∏ j ∈ Γ i, (1-2*p j) := by linarith
  exact (by ring : p i = (2*p i)*(1/2)).le.trans (mul_le_mul_of_nonneg_left hlo (ht i).1)
end FiniteLaw
end Vu

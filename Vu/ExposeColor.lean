module
public import Vu.CoordinateLLL
public import Vu.Coverage
namespace Vu
open Finset
namespace FiniteLaw
variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]

/-- Expose any one coordinate of an independent family. Inside the
remaining expectation that coordinate has its prescribed value. -/
public theorem expose_coordinate (q : I → FiniteLaw X) (i : I) (F : (I → X) → ℝ) :
    (independent q).mean F = (q i).mean (fun x => (independent q).mean (fun a => F (Function.update a i x))) := by
  classical
  let μ := independent q
  let ind (x : X) (a : I → X) : ℝ := if a i=x then 1 else 0
  let g (x : X) (a : I → X) := F (Function.update a i x)
  have expand (a : I → X) : F a = ∑ x, ind x a*g x a := by simp [ind,g,ite_mul,Function.update_eq_self]
  have fac (x : X) : μ.mean (fun a => ind x a*g x a) = (q i).mass x * μ.mean (g x) := by
    have h := independent_disjoint q {i} (univ.erase i) (ind x) (g x) (by
      intro a b he; simp [ind,he i (by simp)]) (by
      intro a b he; unfold g; congr 1; funext j
      by_cases hj : j=i
      · subst j; simp
      · simp [Function.update_of_ne hj,he j (by simp [hj])]) (by simp)
    apply h.trans
    congr 1
    apply (coordinate_mean q i (fun a => if a=x then (1:ℝ) else 0)).trans
    simp [mean,mul_ite]
  conv_lhs => rw [show F = fun a => ∑ x, ind x a*g x a from funext expand]
  rw [mean_sum_finset]
  exact sum_congr rfl (fun x _ => fac x)

/-- Sampling an independent family of mark vectors by vertex or by
color gives the same full probability law after transposing coordinates. -/
public theorem mean_transpose_marks {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
    (π : C → V → ℝ) (h₀ : ∀ c x, 0 ≤ π c x) (h₁ : ∀ c x, π c x ≤ 1)
    (F : (C → V → Bool) → ℝ) :
    (independent (fun x => markLaw (fun c => π c x) (fun c => h₀ c x) (fun c => h₁ c x))).mean
      (fun a => F (fun c x => a x c)) =
    (independent (fun c => markLaw (π c) (h₀ c) (h₁ c))).mean F := by
  classical
  let e : (V → C → Bool) ≃ (C → V → Bool) := ⟨fun a c x => a x c,fun a x c => a c x,fun _ => rfl,fun _ => rfl⟩
  unfold mean
  apply Fintype.sum_equiv e
  intro a
  simp only [independent,markLaw,e]
  congr 1
  rw [prod_comm]; rfl
end FiniteLaw

/-- Integration of the union of offers from a list of distinct colors is
exactly the finite independent-union law of Lemma 2.2. -/
public theorem mean_union_offers {I X V : Type*} [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]
    [Fintype V] [DecidableEq V] (q : I → FiniteLaw X) (O : I → X → Finset V) (l : List I)
    (hd : l.Nodup) (F : Finset V → ℝ) (U : Finset V) :
    (FiniteLaw.independent q).mean (fun a => F (U ∪ l.toFinset.biUnion (fun i => O i (a i)))) =
    coverageAverage (l.map fun i => (q i).map (O i)) F U := by
  classical
  induction l generalizing U with
  | nil => simp [coverageAverage]
  | cons i l ih =>
    obtain ⟨hin,hnd⟩ := List.nodup_cons.mp hd
    rw [FiniteLaw.expose_coordinate q i]
    simp only [List.map_cons,coverageAverage,FiniteLaw.mean_map]
    congr 1
    funext x
    rw [←ih hnd]
    congr 1
    funext a
    congr 1
    rw [List.toFinset_cons,biUnion_insert,Function.update_self,union_assoc]
    congr 2
    apply biUnion_congr rfl
    intro j hj
    have hji : j ≠ i := fun he => hin (he ▸ List.mem_toFinset.mp hj)
    rw [Function.update_of_ne hji]
end Vu

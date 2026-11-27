module
public import Vu.LabelComponents
namespace Vu.Revised
open Finset
variable {A V : Type*} [Fintype A] [DecidableEq A] (J : SimpleGraph A) [DecidableRel J.Adj]

/-- Endpoints of walks of a specified length from the root. -/
private def endpoints (x : A) : ℕ → Finset A
  | 0 => {x}
  | n+1 => (J.neighborFinset x).biUnion (fun y => endpoints y n)

private theorem end_mem {x y : A} (p : J.Walk x y) : y ∈ endpoints J x p.length := by
  induction p with
  | nil => simp [endpoints]
  | cons h p ih => exact mem_biUnion.mpr ⟨_,(J.mem_neighborFinset ..).mpr h,ih⟩

private theorem endpoints_card (d : ℕ) (hd : ∀ x, J.degree x ≤ d) (n : ℕ) :
    ∀ x, (endpoints J x n).card ≤ d^n := by
  induction n with
  | zero => simp [endpoints]
  | succ n ih =>
    intro x
    apply card_biUnion_le.trans
    calc
      _ ≤ ∑ _ ∈ J.neighborFinset x, d^n := sum_le_sum fun y _ => ih y
      _ ≤ d^(n+1) := by simpa [pow_succ',Nat.mul_comm] using Nat.mul_le_mul_right (d^n) (hd x)

/-- Every component label lies on a simple path of length less than r
from the root. A label set with a unique common carrier determines that
carrier, giving the manuscript's power-set bound. -/
public theorem rooted_component_count (a : A) (d r : ℕ) (hd : ∀ x, J.degree x ≤ d)
    (X : Finset V) (C : V → Finset A) (hroot : ∀ x ∈ X, a ∈ C x)
    (hc : ∀ x ∈ X, (C x).card ≤ r) (hconn : ∀ x ∈ X, (J.induce (C x : Set A)).Preconnected)
    (hi : Set.InjOn C X) : X.card ≤ 2^(∑ n ∈ range r, d^n) := by
  classical
  let N := (range r).biUnion (endpoints J a)
  have hn : N.card ≤ ∑ n ∈ range r, d^n :=
    card_biUnion_le.trans (sum_le_sum fun n _ => endpoints_card J d hd n a)
  have sub : X.image C ⊆ N.powerset := by
    rintro T hT
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hT
    apply mem_powerset.mpr
    intro b hb
    obtain ⟨p,hp⟩ := (hconn x hx).exists_isPath ⟨a,hroot x hx⟩ ⟨b,hb⟩
    let inc : J.induce (C x : Set A) →g J := ⟨Subtype.val,fun h => h⟩
    have hlen : p.length < (C x).card := by simpa using hp.length_lt
    exact mem_biUnion.mpr ⟨p.length,mem_range.mpr (hlen.trans_le (hc x hx)),by
      have hm := end_mem J (p.map inc)
      change b ∈ endpoints J a (p.map inc).length at hm
      rwa [SimpleGraph.Walk.length_map] at hm⟩
  rw [←card_image_of_injOn hi]
  exact (card_le_card sub).trans (by simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hn)
end Vu.Revised

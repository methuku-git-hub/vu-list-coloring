module
public import Vu.CoordinateLLL
public import Vu.RoundWeights
namespace Vu
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Finite ball of walks of length at most n in the original graph. -/
@[expose] public def roundBall (x : V) : ℕ → Finset V
  | 0 => {x}
  | n+1 => roundBall x n ∪ (roundBall x n).biUnion (fun y => G.neighborFinset y)

public theorem roundBall_mono (x : V) {m n : ℕ} (hm : m ≤ n) : roundBall G x m ⊆ roundBall G x n := by
  induction hm with
  | refl => exact subset_refl _
  | step h ih => exact ih.trans subset_union_left

public theorem roundBall_walk (x y : V) (n : ℕ) : y ∈ roundBall G x n ↔ ∃ p : G.Walk x y, p.length ≤ n := by
  induction n generalizing y with
  | zero =>
    simp only [roundBall,mem_singleton,Nat.le_zero]
    constructor
    · rintro rfl; exact ⟨.nil,rfl⟩
    · rintro ⟨p,hp⟩; cases p with
      | nil => rfl
      | cons e p => simp at hp
  | succ n ih =>
    constructor
    · intro h
      rcases mem_union.mp h with hy | hy
      · obtain ⟨p,hp⟩ := (ih y).mp hy; exact ⟨p,by omega⟩
      · obtain ⟨u,hu,hy⟩ := mem_biUnion.mp hy
        obtain ⟨p,hp⟩ := (ih u).mp hu
        exact ⟨p.concat ((G.mem_neighborFinset _ _).mp hy),by simp; omega⟩
    · rintro ⟨p,hp⟩
      cases h : p.reverse with
      | nil =>
        have he := SimpleGraph.Walk.reverse_reverse p
        rw [h] at he
        exact mem_union_left _ ((ih _).mpr ⟨.nil,by simp⟩)
      | @cons y u x hy q =>
        have hlen := p.length_reverse
        rw [h] at hlen
        simp only [SimpleGraph.Walk.length_cons] at hlen
        exact mem_union_right _ (mem_biUnion.mpr ⟨u,(ih u).mpr ⟨q.reverse,by rw [q.length_reverse]; omega⟩,
          (G.mem_neighborFinset _ _).mpr hy.symm⟩)

public theorem roundBall_comp {x y z : V} {m n : ℕ} (hy : y ∈ roundBall G x m)
    (hz : z ∈ roundBall G y n) : z ∈ roundBall G x (m+n) := by
  obtain ⟨p,hp⟩ := (roundBall_walk G _ _ _).mp hy
  obtain ⟨q,hq⟩ := (roundBall_walk G _ _ _).mp hz
  exact (roundBall_walk G _ _ _).mpr ⟨p.append q,by rw [p.length_append]; omega⟩

public theorem roundBall_neighbor {x y : V} (ha : G.Adj x y) : y ∈ roundBall G x 1 :=
  (roundBall_walk G x y 1).mpr ⟨.cons ha .nil,le_rfl⟩

public theorem roundBall_card (D : ℕ) (hdeg : ∀ x, G.degree x ≤ D) (x : V) (n : ℕ) :
    (roundBall G x n).card ≤ (D+1)^n := by
  induction n with
  | zero => simp [roundBall]
  | succ n ih =>
    apply (card_union_le _ _).trans
    have h : ((roundBall G x n).biUnion (fun y => G.neighborFinset y)).card ≤ (roundBall G x n).card*D := by
      apply card_biUnion_le.trans
      simpa using sum_le_sum (s := roundBall G x n) (fun y _ => hdeg y)
    rw [pow_succ,Nat.mul_add,Nat.mul_one]
    exact (Nat.add_le_add ih (h.trans (Nat.mul_le_mul_right D ih))).trans_eq (Nat.add_comm ..)

public theorem roundBall_dependency_count (D : ℕ) (hdeg : ∀ x, G.degree x ≤ D) (x : V) :
    (by classical exact (univ.filter fun y => ¬Disjoint (roundBall G x 6) (roundBall G y 6)).card) ≤ (D+1)^12 := by
  classical
  apply (card_le_card (t := roundBall G x 12) ?_).trans (roundBall_card G D hdeg x 12)
  intro y hy
  obtain ⟨z,hboth⟩ := not_disjoint_iff_nonempty_inter.mp (mem_filter.mp hy).2
  obtain ⟨hx,hz⟩ := mem_inter.mp hboth
  obtain ⟨p,hp⟩ := (roundBall_walk G y z 6).mp hz
  exact roundBall_comp G hx ((roundBall_walk G z y 6).mpr ⟨p.reverse,by simpa using hp⟩)
end Vu

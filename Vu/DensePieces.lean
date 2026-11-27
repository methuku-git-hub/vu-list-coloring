module

public import Vu.Reduction
public import Vu.ProductVariance

namespace Vu

open Finset

/-- A bipartite incidence matrix has squared norm at most the largest row sum
of its Gram matrix. The inner cardinal is the number of rows containing z. -/
public theorem gram_row_bound {I Z : Type*} [Fintype I] [Fintype Z] [DecidableEq Z]
    (N : I → Finset Z) (K : ℝ)
    (h : ∀ i, (∑ z ∈ N i, ((univ.filter fun j => z ∈ N j).card : ℝ)) ≤ K^2)
    (f : Z → ℝ) : ∑ i, (∑ z ∈ N i, f z)^2 ≤ K^2 * ∑ z, f z^2 := by
  classical
  let C (z : Z) := univ.filter fun i => z ∈ N i
  have hdual (v : I → ℝ) : ∑ z, (∑ i ∈ C z, v i)^2 ≤ K^2 * ∑ i, v i^2 := by
    calc
      _ ≤ ∑ z, ((C z).card : ℝ) * ∑ i ∈ C z, v i^2 := by
        apply sum_le_sum
        intro z _
        simpa using sum_mul_sq_le_sq_mul_sq (C z) (fun _ => (1 : ℝ)) v
      _ = ∑ i, (∑ z ∈ N i, ((C z).card : ℝ)) * v i^2 := by
        simp only [mul_sum, sum_mul, C, sum_filter]
        rw [sum_comm]
        apply sum_congr rfl
        intro i _
        simp [mul_ite]
      _ ≤ ∑ i, K^2 * v i^2 := sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (h i) (sq_nonneg _))
      _ = _ := (mul_sum ..).symm
  let B (z : Z) (i : I) : ℝ := if z ∈ N i then 1 else 0
  have hB (v : I → ℝ) : ∑ z, (∑ i, B z i * v i)^2 ≤ K^2 * ∑ i, v i^2 := by
    simpa [B, C, sum_filter, ite_mul] using hdual v
  simpa [B, mul_ite, ← sum_filter] using Bernoulli.transpose_bound B K hB f

/-- A violation on the rows T forces a vertex x in T with more than K²
length-two walks back into T. This includes the walks returning to x. -/
public theorem exists_root_of_norm_failure {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) (K : ℝ)
    (h : ¬ RowNormLE (fun u z => if G.Adj u z then 1 else 0) T K) :
    ∃ x ∈ T, K^2 < ∑ z ∈ G.neighborFinset x, ((T.filter fun y => G.Adj y z).card : ℝ) := by
  classical
  by_contra! hn
  apply h
  intro f
  let N (i : ↥T) := G.neighborFinset (i : V)
  have count (z : V) :
      (univ.filter fun i : ↥T => z ∈ N i).card = (T.filter fun y => G.Adj y z).card := by
    simp only [card_filter, N, SimpleGraph.mem_neighborFinset]
    exact sum_coe_sort T (fun y => if G.Adj y z then (1 : ℕ) else 0)
  have hK (i : ↥T) : (∑ z ∈ N i, ((univ.filter fun j => z ∈ N j).card : ℝ)) ≤ K^2 := by
    simpa only [count, N] using hn i i.property
  have hh := gram_row_bound N K hK f
  rw [sum_coe_sort T (fun u => (∑ z ∈ G.neighborFinset u, f z)^2)] at hh
  apply le_trans ?_ hh
  apply le_of_eq
  apply sum_congr rfl
  intro u _
  have hz : (univ.filter fun z => G.Adj u z) = G.neighborFinset u := by ext; simp
  simp [ite_mul, ← sum_filter, hz]

/-- Twice the number of edges induced by S, expressed as ordered incidences. -/
@[expose] public def internalMass {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : ℝ := ∑ x ∈ S, ∑ y ∈ S, if G.Adj x y then (1 : ℝ) else 0

private theorem row_mass {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V) (S : Finset V) :
    (∑ y ∈ S, if G.Adj x y then (1 : ℝ) else 0) = ((S.filter (G.Adj x)).card : ℝ) := by
  simp

/-- Removing one vertex subtracts precisely twice its internal degree. -/
public theorem internalMass_erase {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (x : V) (hx : x ∈ S) :
    internalMass G (S.erase x) + 2 * ((S.filter (G.Adj x)).card : ℝ) = internalMass G S := by
  classical
  let A (u v : V) : ℝ := if G.Adj u v then 1 else 0
  have hsym u v : A u v = A v u := by simp only [A, G.adj_comm u v]
  have row (u : V) : (∑ v ∈ S.erase x, A u v) + A u x = ∑ v ∈ S, A u v :=
    sum_erase_add _ _ hx
  have col : (∑ v ∈ S.erase x, A v x) = ∑ v ∈ S, A x v := by
    simp_rw [show ∀ v, A v x = A x v from (fun v => hsym v x)]
    simpa [A] using row x
  have h := sum_erase_add S (fun u => ∑ v ∈ S, A u v) hx
  have ht := sum_congr (s₁ := S.erase x) rfl (fun u _ => row u)
  rw [sum_add_distrib, col] at ht
  have hr : (∑ v ∈ S, A x v) = ((S.filter (G.Adj x)).card : ℝ) := row_mass G x S
  change (∑ u ∈ S.erase x, ∑ v ∈ S.erase x, A u v) +
    2 * ((S.filter (G.Adj x)).card : ℝ) = ∑ u ∈ S, ∑ v ∈ S, A u v
  linarith only [ht, h, hr]

/-- Iterative low-degree deletion in Lemma 4.1. Any set whose induced
edge count exceeds q times its size contains a nonempty q-core. -/
public theorem exists_dense_core {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (q : ℝ) (U : Finset V) (h : 2 * q * U.card < internalMass G U) :
    ∃ P ⊆ U, P.Nonempty ∧ ∀ x ∈ P, q ≤ ((P.filter (G.Adj x)).card : ℝ) := by
  classical
  induction U using Finset.strongInductionOn with
  | _ U ih =>
    by_cases good : ∀ x ∈ U, q ≤ ((U.filter (G.Adj x)).card : ℝ)
    · refine ⟨U, Subset.rfl, ?_, good⟩
      by_contra! he
      simp [he, internalMass] at h
    · push Not at good
      obtain ⟨x, hx, hd⟩ := good
      have hmass := internalMass_erase G U x hx
      have hc : ((U.erase x).card : ℝ) + 1 = U.card := by exact_mod_cast card_erase_add_one hx
      have hl : 2 * q * (U.erase x).card < internalMass G (U.erase x) := by
        rw [← hc] at h
        linarith only [h, hmass, hd]
      obtain ⟨P, hP, hp, hr⟩ := ih _ (erase_ssubset hx) hl
      exact ⟨P, hP.trans (erase_subset ..), hp, hr⟩

/-- The first extraction in Lemma 4.1. A failure on T gives a set U of at
most |T| + deg(x) vertices of large induced edge mass in the ball of radius two. -/
public theorem exists_dense_ball_of_norm_failure {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) (K : ℝ)
    (h : ¬ RowNormLE (fun u z => if G.Adj u z then 1 else 0) T K) :
    ∃ x ∈ T, ∃ U : Finset V, U.card ≤ T.card + G.degree x ∧
      (∀ u ∈ U, ∃ p : G.Walk x u, p.length ≤ 2) ∧ K^2 < internalMass G U := by
  classical
  obtain ⟨x, hx, hm⟩ := exists_root_of_norm_failure G T K h
  let N := G.neighborFinset x
  let W := T.filter fun y => ∃ z ∈ N, G.Adj y z
  let U := W ∪ N
  have hW : W ⊆ T := filter_subset _ _
  have hN : N ⊆ U := subset_union_right
  refine ⟨x, hx, U, (card_union_le _ _).trans ?_, ?_, hm.trans_le ?_⟩
  · exact Nat.add_le_add (card_le_card hW) (by simp [N])
  · intro u hu
    rcases mem_union.mp hu with hwu | hnu
    · obtain ⟨z, hz, huz⟩ := (mem_filter.mp hwu).2
      exact ⟨.cons ((G.mem_neighborFinset x z).mp hz) (.cons huz.symm .nil), by simp⟩
    · exact ⟨.cons ((G.mem_neighborFinset x u).mp hnu) .nil, by simp⟩
  · unfold internalMass
    simp_rw [row_mass]
    apply (sum_le_sum (s := N) (g := fun z => ((U.filter (G.Adj z)).card : ℝ)) ?_).trans
      (sum_le_sum_of_subset_of_nonneg hN (fun _ _ _ => Nat.cast_nonneg _))
    intro z hz
    apply Nat.cast_le.mpr (card_le_card ?_)
    intro y hy
    obtain ⟨hyt, hyz⟩ := mem_filter.mp hy
    exact mem_filter.mpr ⟨mem_union_left N (mem_filter.mpr ⟨hyt, z, hz, hyz⟩), hyz.symm⟩

end Vu

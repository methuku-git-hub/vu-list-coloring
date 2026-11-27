module
public import Vu.CoordinateLLL
namespace Vu
open Finset

/-- Section 5.3. Independent choices from the vertex distributions give
a proper coloring using only positive-mass colors. The neighbor hypothesis
is required only at a positive-mass entry. -/
public theorem weighted_coloring_completion {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
    (G : SimpleGraph V) [DecidableRel G.Adj] (q : V → FiniteLaw C)
    (hN : ∀ x c, 0 < (q x).mass c → ∑ y ∈ G.neighborFinset x, (q y).mass c ≤ 1/20) :
    ∃ f : V → C, (∀ v, 0 < (q v).mass (f v)) ∧ ∀ ⦃x y⦄, G.Adj x y → f x ≠ f y := by
  classical
  let μ := FiniteLaw.independent q
  let bad (e : V × V × C) (a : V → C) := G.Adj e.1 e.2.1 ∧ a e.1 = e.2.2 ∧ a e.2.1 = e.2.2
  let S (e : V × V × C) : Finset V := {e.1,e.2.1}
  let prob (x y : V) (c : C) := if G.Adj x y then (q x).mass c*(q y).mass c else 0
  have nonneg x y c : 0 ≤ prob x y c := by dsimp [prob]; split <;> first | exact mul_nonneg ((q x).nonneg _) ((q y).nonneg _) | exact le_rfl
  have sym x y c : prob x y c = prob y x c := by simp [prob,G.adj_comm x y,mul_comm]
  have exactP (x y : V) (c : C) : μ.chance (bad (x,y,c)) = prob x y c := by
    by_cases he : G.Adj x y
    · let ind (x : V) (a : V → C) : ℝ := if a x=c then 1 else 0
      have indm (x : V) : μ.mean (ind x) = (q x).mass c := by
        apply (FiniteLaw.coordinate_mean q x (fun d => if d=c then 1 else 0)).trans
        simp [FiniteLaw.mean,mul_ite]
      have det (x : V) : FiniteLaw.determinedBy {x} (ind x) := by
        intro a b h
        simp only [ind,h x (mem_singleton_self _)]
      have hm := FiniteLaw.independent_disjoint q {x} {y} (ind x) (ind y) (det x) (det y) (by simpa using he.ne)
      change μ.mean (fun a => ind x a*ind y a) = μ.mean (ind x)*μ.mean (ind y) at hm
      rw [indm,indm] at hm
      unfold prob; rw [if_pos he]; apply Eq.trans _ hm
      unfold FiniteLaw.chance
      congr 1; funext a
      by_cases h1 : a x = c <;> by_cases h2 : a y=c <;> simp [bad,he,h1,h2,ind]
    · simp [FiniteLaw.chance,bad,prob,he,FiniteLaw.mean_const]
  have row (x : V) : ∑ y, ∑ c, prob x y c ≤ 1/20 := by
    rw [sum_comm]
    have hc (c : C) : ∑ y, prob x y c ≤ (q x).mass c*(1/20) := by
      change (∑ y, if G.Adj x y then (q x).mass c*(q y).mass c else 0) ≤ _
      rw [←sum_filter,←mul_sum]
      have he : (univ.filter (fun y => G.Adj x y)) = G.neighborFinset x := by ext; simp
      rw [he]
      rcases ((q x).nonneg c).eq_or_lt with hz | hpos
      · simp [←hz]
      · exact mul_le_mul_of_nonneg_left (hN x c hpos) hpos.le
    exact (sum_le_sum (fun c _ => hc c)).trans_eq (by rw [←sum_mul,(q x).total,one_mul])
  have incident (v : V) :
      (∑ e : V × V × C, if v ∈ S e then prob e.1 e.2.1 e.2.2 else 0) ≤ 1/10 := by
    let L (v : V) (x y : V) (c : C) := if v=x then prob x y c else 0
    let R (v : V) (x y : V) (c : C) := if v=y then prob x y c else 0
    have hL : (∑ e : V × V × C, L v e.1 e.2.1 e.2.2) = ∑ y, ∑ c, prob v y c := by
      simp [L,Fintype.sum_prod_type]
    have hR : (∑ e : V × V × C, R v e.1 e.2.1 e.2.2) = ∑ y, ∑ c, prob v y c := by
      simp [R,Fintype.sum_prod_type,sym _ v]
    have point (e : V × V × C) : (if v ∈ S e then prob e.1 e.2.1 e.2.2 else 0) ≤ L v e.1 e.2.1 e.2.2 + R v e.1 e.2.1 e.2.2 := by
      simp only [S,L,R,mem_insert,mem_singleton]
      split_ifs <;> first | contradiction | linarith only [nonneg e.1 e.2.1 e.2.2] | tauto
    apply (sum_le_sum (fun e _ => point e)).trans
    rw [sum_add_distrib,hL,hR]
    linarith [row v]
  have det (e : V × V × C) : FiniteLaw.determinedBy (S e) (bad e) := by
    intro a b h
    dsimp [bad]
    rw [h e.1 (by simp [S]),h e.2.1 (by simp [S])]
  obtain ⟨f,hpos,havoid⟩ := FiniteLaw.coordinate_lll_small_mass q bad S det (by
    rintro ⟨x,y,c⟩
    rw [exactP]
    have hh := single_le_sum (f := fun y => ∑ c, prob x y c) (fun y _ => sum_nonneg (fun c _ => nonneg x y c)) (mem_univ y)
    have hc := single_le_sum (f := fun c => prob x y c) (fun c _ => nonneg x y c) (mem_univ c)
    linarith [row x]) (by
    rintro ⟨x,y,c⟩
    rw [sum_filter]
    let A (z : V) (e : V × V × C) := if z ∈ S e then prob e.1 e.2.1 e.2.2 else 0
    have point (e : V × V × C) : (if ¬Disjoint (S (x,y,c)) (S e) then μ.chance (bad e) else 0) ≤ A x e + A y e := by
      rcases e with ⟨u,v,d⟩
      rw [exactP]
      have eq : ¬Disjoint (S (x,y,c)) (S (u,v,d)) ↔ x ∈ S (u,v,d) ∨ y ∈ S (u,v,d) := by simp [S]; grind
      by_cases hx : x ∈ S (u,v,d) <;> by_cases hy : y ∈ S (u,v,d) <;> simp [eq,A,hx,hy,nonneg]
    apply (sum_le_sum (fun e _ => point e)).trans
    rw [sum_add_distrib]
    have hx : (∑ e, A x e) ≤ 1/10 := incident x
    have hy : (∑ e, A y e) ≤ 1/10 := incident y
    linarith)
  refine ⟨f,?_,?_⟩
  · intro x
    apply lt_of_le_of_ne ((q x).nonneg _) (fun hz => ?_)
    have hzero : (FiniteLaw.independent q).mass f = 0 := prod_eq_zero (mem_univ x) hz.symm
    linarith
  · intro x y ha he
    exact havoid (x,y,f x) ⟨ha,rfl,he.symm⟩
end Vu

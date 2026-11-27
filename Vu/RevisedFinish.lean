module
public import Vu.CoordinateLLL
import Mathlib.Algebra.BigOperators.Field
public import Vu.ColoringState
namespace Vu.Revised
open Finset

/-- Section 5.3. Independent choices from the vertex distributions give
a proper coloring using only positive-mass colors. The neighbor hypothesis
is required only at a positive-mass entry. -/
public theorem completion {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
    (G : SimpleGraph V) [DecidableRel G.Adj] (q : V → FiniteLaw C)
    (hN : ∀ x, ∑ y ∈ G.neighborFinset x, ∑ c, (q x).mass c*(q y).mass c ≤ 1/8) :
    ∃ f : V → C, (∀ v, 0 < (q v).mass (f v)) ∧ ∀ ⦃x y⦄, G.Adj x y → f x ≠ f y := by
  classical
  letI : LinearOrder V := (Fintype.equivFin V).linearOrder
  let μ := FiniteLaw.independent q
  let bad (e : V × V × C) (a : V → C) := (G.Adj e.1 e.2.1 ∧ e.1 < e.2.1) ∧ a e.1 = e.2.2 ∧ a e.2.1 = e.2.2
  let S (e : V × V × C) : Finset V := {e.1,e.2.1}
  let prob (x y : V) (c : C) := if G.Adj x y ∧ x < y then (q x).mass c*(q y).mass c else 0
  have nonneg x y c : 0 ≤ prob x y c := by dsimp [prob]; split <;> first | exact mul_nonneg ((q x).nonneg _) ((q y).nonneg _) | exact le_rfl
  have exactP (x y : V) (c : C) : μ.chance (bad (x,y,c)) = prob x y c := by
    by_cases he : G.Adj x y ∧ x < y
    · let ind (x : V) (a : V → C) : ℝ := if a x=c then 1 else 0
      have indm (x : V) : μ.mean (ind x) = (q x).mass c := by
        apply (FiniteLaw.coordinate_mean q x (fun d => if d=c then 1 else 0)).trans
        simp [FiniteLaw.mean,mul_ite]
      have det (x : V) : FiniteLaw.determinedBy {x} (ind x) := by
        intro a b h
        simp only [ind,h x (mem_singleton_self _)]
      have hm := FiniteLaw.independent_disjoint q {x} {y} (ind x) (ind y) (det x) (det y) (by simpa using he.1.ne)
      change μ.mean (fun a => ind x a*ind y a) = μ.mean (ind x)*μ.mean (ind y) at hm
      rw [indm,indm] at hm
      unfold prob; rw [if_pos he]; apply Eq.trans _ hm
      unfold FiniteLaw.chance
      congr 1; funext a
      by_cases h1 : a x = c <;> by_cases h2 : a y=c <;> simp [bad,he,h1,h2,ind]
    · simp [FiniteLaw.chance,bad,prob,he,FiniteLaw.mean_const]
  have sym x y c : prob x y c + prob y x c = if G.Adj x y then (q x).mass c*(q y).mass c else 0 := by
    by_cases h : G.Adj x y
    · rcases lt_or_gt_of_ne h.ne with hxy|hyx
      · simp [prob,h,h.symm,hxy,not_lt_of_gt hxy]
      · simp [prob,h,h.symm,hyx,not_lt_of_gt hyx,mul_comm]
    · simp [prob,h,show ¬G.Adj y x from fun t => h t.symm]
  have row (x : V) : (∑ y, ∑ c, prob x y c)+(∑ y, ∑ c, prob y x c) ≤ 1/8 := by
    rw [←sum_add_distrib]; simp_rw [←sum_add_distrib,sym]
    simp only [sum_ite_irrel,sum_const_zero,←sum_filter]
    have he : univ.filter (fun y => G.Adj x y) = G.neighborFinset x := by ext; simp
    rw [he]; exact hN x
  have incident (v : V) :
      (∑ e : V × V × C, if v ∈ S e then prob e.1 e.2.1 e.2.2 else 0) ≤ 1/8 := by
    let L (v : V) (x y : V) (c : C) := if v=x then prob x y c else 0
    let R (v : V) (x y : V) (c : C) := if v=y then prob x y c else 0
    have hL : (∑ e : V × V × C, L v e.1 e.2.1 e.2.2) = ∑ y, ∑ c, prob v y c := by
      simp [L,Fintype.sum_prod_type]
    have hR : (∑ e : V × V × C, R v e.1 e.2.1 e.2.2) = ∑ y, ∑ c, prob y v c := by
      simp [R,Fintype.sum_prod_type]
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
    have hn := sum_nonneg (s := (univ : Finset V)) (fun y _ => sum_nonneg (s := (univ : Finset C)) (fun c _ => nonneg y x c))
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
    have hx : (∑ e, A x e) ≤ 1/8 := incident x
    have hy : (∑ e, A y e) ≤ 1/8 := incident y
    linarith)
  refine ⟨f,?_,?_⟩
  · intro x
    apply lt_of_le_of_ne ((q x).nonneg _) (fun hz => ?_)
    have hzero : (FiniteLaw.independent q).mass f = 0 := prod_eq_zero (mem_univ x) hz.symm
    linarith
  · intro x y ha he
    rcases lt_or_gt_of_ne ha.ne with h|h
    · exact havoid (x,y,f x) ⟨⟨ha,h⟩,rfl,he.symm⟩
    · exact havoid (y,x,f y) ⟨⟨ha.symm,h⟩,rfl,he⟩

public theorem finish_state {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
    (G : SimpleGraph V) [DecidableRel G.Adj] (L : V → Finset C) (k : ℕ) (hk : 0 < k)
    (s : ColoringState G L k) (tests : V → Finset (Finset V)) (a b τ cap : ℝ)
    (hb : RoundBounds s tests a b τ cap) (hstop : τ/a ≤ 1/8) :
    ∃ f : V → C, (∀ x, f x ∈ L x) ∧ (∀ x c, s.color x = some c → f x=c) ∧
      ∀ ⦃x y⦄, G.Adj x y → f x ≠ f y := by
  classical
  have hkp : 0 < (k:ℝ) := Nat.cast_pos.mpr hk
  let m x c : ℝ := match s.color x with
    | none => s.weight x c/k
    | some d => if c=d then 1 else 0
  let q (x : V) : FiniteLaw C := {
    mass := m x
    nonneg := fun c => by cases hs : s.color x with
      | none => simp [m,hs,div_nonneg (s.nonneg x c) hkp.le]
      | some d => simp only [m,hs]; split <;> norm_num
    total := by cases hs : s.color x with
      | none => simp [m,hs,←sum_div,s.total x hs,hkp.ne']
      | some d => simp [m,hs] }
  have hN (x : V) (c : C) (hc : 0 < (q x).mass c) : ∑ y ∈ G.neighborFinset x, (q y).mass c ≤ 1/8 := by
    cases hx : s.color x with
    | some d =>
      have heq : c=d := by by_contra hn; simp [q,m,hx,hn] at hc
      subst d
      have hz (y : V) (hy : y ∈ G.neighborFinset x) : (q y).mass c = 0 := by
        have ha := (G.mem_neighborFinset _ _).mp hy
        cases hh : s.color y with
        | none => simp [q,m,hh,s.blocked y x c ha.symm hx]
        | some d =>
          have hn : c ≠ d := fun e => s.proper x y c ha hx (e ▸ hh)
          simp [q,m,hh,hn]
      rw [sum_eq_zero hz]; norm_num
    | none =>
      have hw : 0 < s.weight x c := by
        change 0 < m x c at hc
        simpa only [m,hx,div_pos_iff_of_pos_right hkp] using hc
      have eq (y : V) (hy : y ∈ G.neighborFinset x) : (q y).mass c = s.weight y c/k := by
        cases hh : s.color y with
        | none => simp [q,m,hh]
        | some d =>
          have hn : c ≠ d := fun he => hw.ne' (s.blocked x y c ((G.mem_neighborFinset _ _).mp hy) (he ▸ hh))
          simp [q,m,hh,hn,s.painted y c (by simp [hh])]
      rw [sum_congr rfl eq,←sum_div]
      apply le_trans ((div_le_div_of_nonneg_right (hb.2 x c hw).2 hkp.le).trans_eq ?_) hstop
      field_simp
  have htotal x : ∑ y ∈ G.neighborFinset x, ∑ c, (q x).mass c*(q y).mass c ≤ 1/8 := by
    rw [sum_comm]; simp_rw [←mul_sum]
    apply le_trans (b := ∑ c, (q x).mass c*(1/8)) (sum_le_sum (fun c _ => ?_))
    · rw [←sum_mul,(q x).total,one_mul]
    · rcases ((q x).nonneg c).eq_or_lt with hz|hpos
      · simp [←hz]
      · exact mul_le_mul_of_nonneg_left (hN x c hpos) hpos.le
  obtain ⟨f,hf,hp⟩ := completion G q htotal
  have hext (x : V) (c : C) (hh : s.color x = some c) : f x=c := by
    by_contra hn
    have := hf x
    simp [q,m,hh,hn] at this
  refine ⟨f,?_,hext,hp⟩
  intro x
  cases hx : s.color x with
  | none =>
    by_contra hn
    have := hf x
    simp [q,m,hx,s.outside x _ hn] at this
  | some c => rw [hext x c hx]; exact s.listed x c hx
end Vu.Revised

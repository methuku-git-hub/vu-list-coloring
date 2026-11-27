module
public import Vu.WeightedCompletion
import Mathlib.Algebra.BigOperators.Field
namespace Vu
open Finset

/-- A proper partial list-coloring and the compatible nonnegative weights
of Section 5. Values outside the original lists and at colored vertices are
zero, so neighborhood sums can always run over the original vertices. -/
public structure ColoringState {V C : Type*} [Fintype V] [Fintype C]
    (G : SimpleGraph V) (L : V → Finset C) (k : ℕ) where
  color : V → Option C
  weight : V → C → ℝ
  listed : ∀ x c, color x = some c → c ∈ L x
  proper : ∀ x y c, G.Adj x y → color x = some c → color y ≠ some c
  nonneg : ∀ x c, 0 ≤ weight x c
  outside : ∀ x c, c ∉ L x → weight x c = 0
  painted : ∀ x c, color x ≠ none → weight x c = 0
  blocked : ∀ x y c, G.Adj x y → color y = some c → weight x c = 0
  total : ∀ x, color x = none → ∑ c, weight x c = k

/-- The weight cap and the hard and full neighborhood tests in (I1)–(I2). -/
@[expose] public def RoundBounds {V C : Type*} [Fintype V] [Fintype C]
    {G : SimpleGraph V} [DecidableRel G.Adj] {L : V → Finset C} {k : ℕ}
    (s : ColoringState G L k) (tests : V → Finset (Finset V)) (a b τ cap : ℝ) : Prop :=
  (∀ x c, s.weight x c ≤ cap) ∧ ∀ x c, 0 < s.weight x c →
    (∀ U ∈ tests x, ∑ y ∈ U, s.weight y c ≤ (1-b)*k*τ) ∧
    ∑ y ∈ G.neighborFinset x, s.weight y c ≤ (1/a)*k*τ

/-- Unit list weights give the empty initial coloring. -/
@[expose] public noncomputable def initial_state {V C : Type*} [Fintype V] [Fintype C] [DecidableEq C]
    (G : SimpleGraph V) (L : V → Finset C) (k : ℕ) (hL : ∀ x, (L x).card = k) : ColoringState G L k where
  color _ := none
  weight x c := if c ∈ L x then 1 else 0
  listed := by simp
  proper := by simp
  nonneg := by intros; split <;> norm_num
  outside := by intro x c h; simp [h]
  painted := by simp
  blocked := by simp
  total := by intro x _; simp [←sum_filter,hL]

public theorem initial_round_bounds {V C : Type*} [Fintype V] [Fintype C] [DecidableEq C]
    (G : SimpleGraph V) [DecidableRel G.Adj] (L : V → Finset C) (D k R : ℕ) (a b M η : ℝ)
    (d : Decomposition G D k R b M η) (ha : 0 < a) (hdeg : ∀ x, G.degree x ≤ D)
    (hak : a*D ≤ k) (hL : ∀ x, (L x).card = k) :
    RoundBounds (initial_state G L k hL) d.tests a b 1 1 := by
  classical
  have count (U : Finset V) (c : C) : (∑ y ∈ U, (initial_state G L k hL).weight y c) ≤ U.card := by
    exact (sum_le_sum (g := fun _ => (1:ℝ)) (fun y _ => by dsimp [initial_state]; split <;> norm_num)).trans_eq (by simp)
  refine ⟨fun x c => by dsimp [initial_state]; split <;> norm_num,fun x c _ => ⟨?_,?_⟩⟩
  · intro U hu; simpa using (count U c).trans (d.test_size x U hu)
  · apply (count _ _).trans
    rw [SimpleGraph.card_neighborFinset_eq_degree,mul_one,one_div,←div_eq_inv_mul]
    exact (Nat.cast_le (α := ℝ) |>.mpr (hdeg x)).trans ((le_div_iff₀ ha).mpr (by linarith))

/-- Once the full-neighborhood threshold is reached, the partial coloring
extends to a proper coloring from the original lists, including every color
already fixed in earlier rounds. -/
public theorem finish_state {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
    (G : SimpleGraph V) [DecidableRel G.Adj] (L : V → Finset C) (k : ℕ) (hk : 0 < k)
    (s : ColoringState G L k) (tests : V → Finset (Finset V)) (a b τ cap : ℝ)
    (hb : RoundBounds s tests a b τ cap) (hstop : τ/a ≤ 1/20) :
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
  have hN (x : V) (c : C) (hc : 0 < (q x).mass c) : ∑ y ∈ G.neighborFinset x, (q y).mass c ≤ 1/20 := by
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
  obtain ⟨f,hf,hp⟩ := weighted_coloring_completion G q hN
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
end Vu

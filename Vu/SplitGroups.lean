module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

namespace Vu
open Finset

/-- All singleton-rooted sets obtained by adjoining one neighbor at each
step. Repeated vertices are allowed in this auxiliary enumeration. -/
private def grown {A : Type*} [Fintype A] [DecidableEq A]
    (J : SimpleGraph A) [DecidableRel J.Adj] (root : A) : ℕ → Finset (Finset A)
  | 0 => {{root}}
  | n+1 => (grown J root n).biUnion fun S => (S.biUnion (fun a => J.neighborFinset a)).image fun a => insert a S

private theorem grown_size {A : Type*} [Fintype A] [DecidableEq A]
    (J : SimpleGraph A) [DecidableRel J.Adj] (root : A) (n : ℕ) :
    ∀ S ∈ grown J root n, S.card ≤ n+1 := by
  induction n with
  | zero => simp [grown]
  | succ n ih =>
    intro S hS
    obtain ⟨T, ht, h⟩ := mem_biUnion.mp hS
    obtain ⟨a, _, rfl⟩ := mem_image.mp h
    exact (card_insert_le _ _).trans (Nat.add_le_add_right (ih T ht) 1)

private theorem grown_count {A : Type*} [Fintype A] [DecidableEq A]
    (J : SimpleGraph A) [DecidableRel J.Adj] (root : A) (d : ℕ) (hdeg : ∀ a, J.degree a ≤ d)
    (n : ℕ) : (grown J root n).card ≤ n.factorial * d^n := by
  induction n with
  | zero => simp [grown]
  | succ n ih =>
    apply card_biUnion_le.trans
    calc
      _ ≤ ∑ _S ∈ grown J root n, (n+1)*d := by
        apply sum_le_sum
        intro S hs
        apply card_image_le.trans (card_biUnion_le.trans ?_)
        apply (sum_le_sum (g := fun _ => d) (fun a _ => hdeg a)).trans
        simpa using Nat.mul_le_mul_right d (grown_size J root n S hs)
      _ ≤ (n.factorial*d^n)*((n+1)*d) := by
        simpa using Nat.mul_le_mul_right ((n+1)*d) ih
      _ = _ := by rw [Nat.factorial_succ, pow_succ]; ring

private theorem propagate_along_walk {W : Type*} {J : SimpleGraph W} (P : W → Prop)
    (step : ∀ x y, P x → J.Adj x y → P y) {x y : W} (p : J.Walk x y) : P x → P y := by
  induction p with
  | nil => exact id
  | cons h p ih => exact fun hx => ih (step _ _ hx h)

private theorem grown_contains_connected {A : Type*} [Fintype A] [DecidableEq A]
    (J : SimpleGraph A) [DecidableRel J.Adj] (root : A) (S : Finset A) (hr : root ∈ S)
    (hconn : (J.induce (S : Set A)).Preconnected) : S ∈ grown J root (S.card-1) := by
  classical
  have reach (n : ℕ) (hn : n+1 ≤ S.card) :
      ∃ T ∈ grown J root n, root ∈ T ∧ T ⊆ S ∧ T.card = n+1 := by
    induction n with
    | zero => exact ⟨{root}, by simp [grown], by simp, singleton_subset_iff.mpr hr, by simp⟩
    | succ n ih =>
      obtain ⟨T, ht, hrt, hTS, hsize⟩ := ih (by omega)
      have exists_step : ∃ a ∈ T, ∃ b ∈ S, b ∉ T ∧ J.Adj a b := by
        by_contra! hall
        have hsub : S ⊆ T := by
          intro b hb
          obtain ⟨p⟩ := hconn (⟨root,hr⟩ : ↥S) (⟨b,hb⟩ : ↥S)
          apply propagate_along_walk (fun x : ↥S => x.val ∈ T) ?_ p hrt
          intro x y hx hxy
          by_contra h_out
          exact hall x hx y y.property h_out hxy
        have hcard := card_le_card hsub
        omega
      obtain ⟨a, ha, b, hb, hbt, hab⟩ := exists_step
      refine ⟨insert b T, mem_biUnion.mpr ⟨T, ht, mem_image.mpr ⟨b, ?_, rfl⟩⟩,
        mem_insert_of_mem hrt, insert_subset hb hTS, ?_⟩
      · exact mem_biUnion.mpr ⟨a, ha, (J.mem_neighborFinset a b).mpr hab⟩
      · rw [card_insert_of_notMem hbt, hsize]
  have hs : 0 < S.card := card_pos.mpr ⟨root, hr⟩
  obtain ⟨T, ht, _, hTS, hc⟩ := reach (S.card-1) (by omega)
  exact (eq_of_subset_of_card_le hTS (by omega)) ▸ ht

/-- The connected-set count in Lemma 4.7. It applies to any auxiliary
graph and counts its connected label sets containing a specified label. -/
public theorem rooted_connected_set_count {A : Type*} [Fintype A] [DecidableEq A]
    (J : SimpleGraph A) [DecidableRel J.Adj] (root : A) (d n : ℕ) (hdeg : ∀ a, J.degree a ≤ d)
    (C : Finset (Finset A))
    (hC : ∀ S ∈ C, root ∈ S ∧ S.card = n+1 ∧ (J.induce (S : Set A)).Preconnected) :
    C.card ≤ n.factorial * d^n := by
  apply (card_le_card (t := grown J root n) ?_).trans (grown_count J root d hdeg n)
  intro S hS
  obtain ⟨hr, hc, hcon⟩ := hC S hS
  simpa [hc] using grown_contains_connected J root S hr hcon

/-- Each label set with a unique common carrier accounts for at most one
split vertex. The sum is the explicit polynomial bound used in Lemma 4.7. -/
public theorem split_vertex_count {A V : Type*} [Fintype A] [DecidableEq A]
    (J : SimpleGraph A) [DecidableRel J.Adj] (root : A) (d r : ℕ)
    (hdeg : ∀ a, J.degree a ≤ d) (X : Finset V) (C : V → Finset A) (carries : V → A → Prop)
    (hC : ∀ x ∈ X, root ∈ C x ∧ (C x).card ≤ r ∧ (J.induce (C x : Set A)).Preconnected)
    (hself : ∀ x ∈ X, ∀ a ∈ C x, carries x a)
    (huniq : ∀ x ∈ X, ∀ y ∈ X, (∀ a ∈ C x, carries y a) → y = x) :
    X.card ≤ ∑ n ∈ range r, n.factorial * d^n := by
  classical
  have hi : Set.InjOn C X := by
    intro x hx y hy he
    exact (huniq x hx y hy (fun a ha => hself y hy a (he ▸ ha))).symm
  let parts := fun n => (X.image C).filter fun S => S.card = n+1
  have cover : X.image C ⊆ (range r).biUnion parts := by
    intro S hS
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hS
    obtain ⟨hr, hm, _⟩ := hC x hx
    have hpos := card_pos.mpr ⟨root,hr⟩
    exact mem_biUnion.mpr ⟨(C x).card-1, mem_range.mpr (by omega),
      mem_filter.mpr ⟨mem_image_of_mem C hx, by omega⟩⟩
  rw [← card_image_of_injOn hi]
  apply (card_le_card cover).trans (card_biUnion_le.trans ?_)
  apply sum_le_sum
  intro n _
  apply rooted_connected_set_count J root d n hdeg
  intro S hs
  obtain ⟨hs', hn⟩ := mem_filter.mp hs
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hs'
  exact ⟨(hC x hx).1, hn, (hC x hx).2.2⟩

/-- Summing overlaps is the same as summing label multiplicities through
the vertices of a fixed label. -/
public theorem overlap_degree_bound {V A : Type*} [Fintype A] [DecidableEq V]
    (J : SimpleGraph A) [DecidableRel J.Adj] (L : A → Finset V) (r : ℕ) (D h : ℝ)
    (hD : 0 < D) (hh : 0 < h) (size : ∀ a, ((L a).card : ℝ) ≤ 2*D)
    (multiplicity : ∀ x, (univ.filter fun a => x ∈ L a).card ≤ r)
    (large : ∀ a b, J.Adj a b → D/h^2 ≤ ((L a ∩ L b).card : ℝ)) (a : A) :
    (J.degree a : ℝ) ≤ 2*r*h^2 := by
  classical
  let N := J.neighborFinset a
  have double : (∑ b ∈ N, ((L a ∩ L b).card : ℝ)) ≤ (L a).card * (r : ℝ) := by
    have row (b : A) : ((L a ∩ L b).card : ℝ) = ∑ x ∈ L a, if x ∈ L b then 1 else 0 := by
      simp
    simp_rw [row]
    rw [sum_comm]
    apply (sum_le_sum (g := fun _ => (r : ℝ)) ?_).trans_eq (by simp)
    intro x _
    have hsub : (N.filter fun b => x ∈ L b) ⊆ (univ.filter fun b => x ∈ L b) :=
      filter_subset_filter _ (subset_univ _)
    simpa [← sum_filter] using (Nat.cast_le (α := ℝ)).mpr ((card_le_card hsub).trans (multiplicity x))
  have hm := (sum_le_sum (s := N) (fun b hb => large a b ((J.mem_neighborFinset a b).mp hb))).trans double
  have hg : (J.degree a : ℝ) * (D/h^2) ≤ 2*D*r := by
    simpa [N] using hm.trans (mul_le_mul_of_nonneg_right (size a) (Nat.cast_nonneg _))
  rw [← mul_div_assoc] at hg
  have hnum := (div_le_iff₀ (sq_pos_of_pos hh)).mp hg
  apply (mul_le_mul_iff_of_pos_right hD).mp
  linarith only [hnum]

/-- Explicit form of Lemma 4.7. For h^(2r)=D the constant multiplying D/h²
depends only on the maximum number r of labels at a vertex. -/
public theorem split_vertex_bound {A V : Type*} [Fintype A] [DecidableEq A]
    (J : SimpleGraph A) [DecidableRel J.Adj] (root : A) (r : ℕ) (h D : ℝ) (hr : 1 ≤ r)
    (hh : 1 ≤ h) (hD : h^(2*r) = D) (hdeg : ∀ a, (J.degree a : ℝ) ≤ 2*r*h^2)
    (X : Finset V) (C : V → Finset A) (carries : V → A → Prop)
    (hC : ∀ x ∈ X, root ∈ C x ∧ (C x).card ≤ r ∧ (J.induce (C x : Set A)).Preconnected)
    (hself : ∀ x ∈ X, ∀ a ∈ C x, carries x a)
    (huniq : ∀ x ∈ X, ∀ y ∈ X, (∀ a ∈ C x, carries y a) → y = x) :
    (X.card : ℝ) ≤ (r * (r.factorial : ℝ) * (2*r : ℝ)^(r-1)) * (D/h^2) := by
  let d := ⌊2*(r : ℝ)*h^2⌋₊
  have hd : ∀ a, J.degree a ≤ d := fun a => Nat.le_floor (hdeg a)
  have hc := split_vertex_count J root d r hd X C carries hC hself huniq
  have hc' : (X.card : ℝ) ≤ ∑ n ∈ range r, (n.factorial : ℝ)*(d : ℝ)^n := by exact_mod_cast hc
  have hfloor : (d : ℝ) ≤ 2*r*h^2 := Nat.floor_le (by positivity)
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hbase : 1 ≤ 2*(r : ℝ)*h^2 := by nlinarith [(one_le_pow₀ hh : 1 ≤ h^2), mul_nonneg (sub_nonneg.mpr hr') (sq_nonneg h)]
  have hterm (n : ℕ) (hn : n ∈ range r) :
      (n.factorial : ℝ)*(d : ℝ)^n ≤ (r.factorial : ℝ)*(2*r*h^2)^(r-1) := by
    have hn' := mem_range.mp hn
    apply mul_le_mul (Nat.cast_le.mpr (Nat.factorial_le hn'.le))
      ((pow_le_pow_left₀ (Nat.cast_nonneg _) hfloor n).trans
        (pow_le_pow_right₀ hbase (by omega))) (by positivity) (by positivity)
  have hdiv : D/h^2 = (h^2)^(r-1) := by
    apply (div_eq_iff (by positivity : h^2 ≠ 0)).mpr
    rw [← hD, pow_mul, ← pow_succ, Nat.sub_add_cancel hr]
  apply (hc'.trans (sum_le_sum hterm)).trans_eq
  simp [mul_pow, hdiv, mul_assoc]
end Vu

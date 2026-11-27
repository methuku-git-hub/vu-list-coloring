module
public import Vu.WitnessRefinement
namespace Vu.Revised
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {S : Finset V}
  (G : SimpleGraph V) [DecidableRel G.Adj]

@[expose] public noncomputable def irregularMass (R : Finpartition S) (ρ : ℝ) : ℝ := by
  classical
  exact ∑ e ∈ (R.parts ×ˢ R.parts).filter (fun e => irregularPair G ρ e.1 e.2),
    (e.1.card:ℝ)*e.2.card

private theorem sum_cells (R : Finpartition S) (f : V → V → ℝ) :
    (∑ e ∈ R.parts ×ˢ R.parts, ∑ x ∈ e.1, ∑ y ∈ e.2, f x y) = ∑ x ∈ S, ∑ y ∈ S, f x y := by
  rw [sum_product]
  calc
    _ = ∑ A ∈ R.parts, ∑ x ∈ A, ∑ y ∈ S, f x y := by
      apply sum_congr rfl; intro A _
      rw [sum_comm]; exact sum_congr rfl fun x _ => sum_partition_classes R _
    _ = _ := sum_partition_classes R _

/-- Refining all irregular cells at once increases the unnormalised energy
by at least ρ⁴ times their total area. -/
public theorem refine_energy_gain (R : Finpartition S) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ Q : Finpartition S, Q ≤ R ∧ Q.parts.card ≤ R.parts.card*2^(R.parts.card+1) ∧
      ρ^4 * irregularMass G R ρ ≤ energy G Q - energy G R := by
  classical
  obtain ⟨Q,hq,hs,hw⟩ := witness_refinement G R ρ
  refine ⟨Q,hq,hs,?_⟩
  let gain (e : Finset V × Finset V) :=
    ∑ x ∈ e.1, ∑ y ∈ e.2, (cellDensity G Q x y-cellDensity G R x y)^2
  let old (e : Finset V × Finset V) := ∑ x ∈ e.1, ∑ y ∈ e.2, (cellDensity G R x y)^2
  let new (e : Finset V × Finset V) := ∑ x ∈ e.1, ∑ y ∈ e.2, (cellDensity G Q x y)^2
  have cell (A B : Finset V) (ha : A ∈ R.parts) (hb : B ∈ R.parts) (x : V) (hx : x ∈ A) (y : V) (hy : y ∈ B) :
      cellDensity G R x y = crossDensity G A B := by simp [cellDensity,R.part_eq_of_mem ha hx,R.part_eq_of_mem hb hy]
  have hg e (he : e ∈ R.parts ×ˢ R.parts) :
      gain e = ∑ x ∈ e.1, ∑ y ∈ e.2, (cellDensity G Q x y-crossDensity G e.1 e.2)^2 :=
    sum_congr rfl fun x hx => sum_congr rfl fun y hy => by rw [cell _ _ (mem_product.mp he).1 (mem_product.mp he).2 x hx y hy]
  have hc e (he : e ∈ R.parts ×ˢ R.parts) : gain e = new e-old e := by
    obtain ⟨ha,hb⟩ := mem_product.mp he
    have ho : old e = (e.1.card:ℝ)*e.2.card*(crossDensity G e.1 e.2)^2 := by
      rw [show old e = ∑ x ∈ e.1, ∑ y ∈ e.2, (crossDensity G e.1 e.2)^2 from
        sum_congr rfl fun x hx => sum_congr rfl fun y hy => by rw [cell _ _ ha hb x hx y hy]]
      simp; ring
    rw [hg e he, ←energy_gain_cell G R Q hq _ _ ha hb,ho]
  rw [irregularMass,mul_sum]
  calc
    _ ≤ ∑ e ∈ (R.parts ×ˢ R.parts).filter (fun e => irregularPair G ρ e.1 e.2), gain e := by
      apply sum_le_sum; intro e he
      obtain ⟨he,hbad⟩ := mem_filter.mp he
      obtain ⟨ha,hb⟩ := mem_product.mp he
      obtain ⟨X,Y,h,hx,hy⟩ := hw _ ha _ hb hbad
      rw [hg e he]
      exact witness_energy G Q _ _ X Y ρ hρ (R.le ha) (R.le hb) h.1 h.2.1 hx hy h.2.2.1 h.2.2.2.1
        (R.nonempty_of_mem_parts ha) (R.nonempty_of_mem_parts hb) h.2.2.2.2
    _ ≤ ∑ e ∈ R.parts ×ˢ R.parts, gain e := sum_le_sum_of_subset_of_nonneg (filter_subset ..)
      (fun e _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _)
    _ = _ := by
      rw [sum_congr rfl hc,sum_sub_distrib]
      exact congrArg₂ (· - ·) (sum_cells R _) (sum_cells R _)

/-- Uniform bound for the number of subclasses after a fixed number of steps. -/
@[expose] public def refinementBound (m : ℕ) : ℕ → ℕ
  | 0 => m
  | n+1 => let k := refinementBound m n; k*2^(k+1)

private theorem bound_succ (m n : ℕ) : refinementBound m n ≤ refinementBound m (n+1) :=
  Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)

public theorem energy_regular_refinement (ρ : ℝ) (hρ : 0 < ρ) (m : ℕ) :
    ∃ K : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (R : Finpartition (univ : Finset V)), R.parts.card ≤ m →
      ∃ Q : Finpartition (univ : Finset V), Q ≤ R ∧ Q.parts.card ≤ K ∧
        irregularMass G Q ρ ≤ ρ*(Fintype.card V:ℝ)^2 := by
  classical
  let t := ⌈1/ρ^5⌉₊
  refine ⟨refinementBound m t,?_⟩
  intro W _ _ H _ R hr
  let area := (Fintype.card W : ℝ)^2
  let good (Q : Finpartition (univ : Finset W)) := irregularMass H Q ρ ≤ ρ*area
  have steps (n : ℕ) : ∃ Q : Finpartition (univ : Finset W), Q ≤ R ∧ Q.parts.card ≤ refinementBound m n ∧
      (good Q ∨ n=0 ∨ (n:ℝ)*ρ^5*area < energy H Q) := by
    induction n with
    | zero => exact ⟨R,le_rfl,hr,Or.inr (Or.inl rfl)⟩
    | succ n ih =>
      obtain ⟨P,hP,hs,he⟩ := ih
      by_cases hg : good P
      · exact ⟨P,hP,hs.trans (bound_succ ..),Or.inl hg⟩
      · obtain ⟨Q,hq,hsize,hgain⟩ := refine_energy_gain H P ρ hρ
        have hp : ρ*area < irregularMass H P ρ := lt_of_not_ge hg
        have hinc := (mul_lt_mul_of_pos_left hp (show 0 < ρ^4 by positivity)).trans_le hgain
        have previous : (n:ℝ)*ρ^5*area ≤ energy H P := by
          rcases he with hg'|hn|hlt
          · contradiction
          · simpa [hn] using (energy_bounds H P).1
          · exact hlt.le
        refine ⟨Q,hq.trans hP,hsize.trans (Nat.mul_le_mul hs (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_right hs 1))),
          Or.inr (Or.inr ?_)⟩
        push_cast; nlinarith only [previous,hinc]
  obtain ⟨Q,hq,hs,hend⟩ := steps t
  refine ⟨Q,hq,hs,?_⟩
  rcases hend with hg | ht | he
  · exact hg
  · have : 0 < t := Nat.ceil_pos.mpr (by positivity); omega
  · have ht : 1 ≤ (t:ℝ)*ρ^5 := (div_le_iff₀ (by positivity)).mp (Nat.le_ceil _)
    have hbound : energy H Q ≤ area := by simpa [area] using (energy_bounds H Q).2
    exact ((not_lt_of_ge ((le_mul_of_one_le_left (sq_nonneg _) ht).trans' hbound)) he).elim

end Vu.Revised

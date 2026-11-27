module
public import Vu.PartitionMatrix
namespace Vu.Revised
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {S : Finset V}
  (G : SimpleGraph V) [DecidableRel G.Adj]

@[expose] public noncomputable def cellDensity (R : Finpartition S) (x y : V) : ℝ :=
  crossDensity G (R.part x) (R.part y)

/-- Unnormalised partition energy. A common denominator |S|² cancels at
every step. The sum includes diagonal cells. -/
@[expose] public noncomputable def energy (R : Finpartition S) : ℝ :=
  ∑ x ∈ S, ∑ y ∈ S, (cellDensity G R x y)^2

public theorem energy_bounds (R : Finpartition S) :
    0 ≤ energy G R ∧ energy G R ≤ (S.card:ℝ)^2 := by
  refine ⟨sum_nonneg (fun x _ => sum_nonneg fun y _ => sq_nonneg _),?_⟩
  apply (sum_le_sum (fun x (_ : x ∈ S) => sum_le_sum (g := fun _ => (1:ℝ)) (fun y (_ : y ∈ S) => ?_))).trans_eq
  · simp [pow_two]
  · obtain ⟨h₀,h₁⟩ := density_mem_unit G (R.part x) (R.part y)
    exact (pow_le_pow_left₀ h₀ h₁ 2).trans_eq (by norm_num)

@[expose] public def respects (R : Finpartition S) (X : Finset V) : Prop :=
  ∀ A ∈ R.parts, A ⊆ X ∨ Disjoint A X

public theorem respects_parent (R Q : Finpartition S) (hq : Q ≤ R) {A : Finset V} (ha : A ∈ R.parts) : respects Q A := by
  intro U hU
  obtain ⟨B,hB,hu⟩ := hq hU
  by_cases he : B=A
  · exact Or.inl (he ▸ hu)
  · exact Or.inr ((R.supIndep.pairwiseDisjoint hB ha he).mono_left hu)

public theorem sum_subclasses (R : Finpartition S) (X : Finset V) (hX : X ⊆ S) (hr : respects R X)
    (f : V → ℝ) : ∑ A ∈ R.parts.filter (fun A => A ⊆ X), ∑ x ∈ A, f x = ∑ x ∈ X, f x := by
  classical
  let sub := R.parts.filter fun A => A ⊆ X
  have eq : sub.biUnion id = X := by
    ext x
    constructor
    · rintro hx; obtain ⟨A,hA,hx⟩ := mem_biUnion.mp hx
      exact (mem_filter.mp hA).2 hx
    · intro hx
      have hpart := R.part_mem.mpr (hX hx)
      have hm := R.mem_part (hX hx)
      exact mem_biUnion.mpr ⟨R.part x,mem_filter.mpr ⟨hpart,(hr _ hpart).resolve_right
        (fun h => disjoint_left.mp h hm hx)⟩,hm⟩
  change (∑ A ∈ sub, ∑ x ∈ A, f x) = _
  apply Eq.trans _ (congrArg (fun z : Finset V => ∑ x ∈ z, f x) eq)
  exact (sum_biUnion (s := sub) (t := id) (fun A hA B hB hne => R.supIndep.pairwiseDisjoint
    (mem_filter.mp hA).1 (mem_filter.mp hB).1 hne)).symm

public theorem sum_on_blocks (R : Finpartition S) (X Y : Finset V) (hX : X ⊆ S) (hY : Y ⊆ S)
    (hRX : respects R X) (hRY : respects R Y) (f : V → V → ℝ) :
    (∑ A ∈ R.parts.filter (fun A => A ⊆ X), ∑ B ∈ R.parts.filter (fun B => B ⊆ Y), ∑ x ∈ A, ∑ y ∈ B, f x y) =
    ∑ x ∈ X, ∑ y ∈ Y, f x y := by
  have eq A : (∑ B ∈ R.parts.filter (fun B => B ⊆ Y), ∑ x ∈ A, ∑ y ∈ B, f x y) = ∑ x ∈ A, ∑ y ∈ Y, f x y := by
    rw [sum_comm]
    exact sum_congr rfl (fun x _ => sum_subclasses R Y hY hRY (f x))
  simp_rw [eq,sum_subclasses R X hX hRX]

public theorem cell_average (R : Finpartition S) (X Y : Finset V) (hX : X ⊆ S) (hY : Y ⊆ S)
    (hRX : respects R X) (hRY : respects R Y) :
    (∑ x ∈ X, ∑ y ∈ Y, cellDensity G R x y) = crossDensity G X Y*((X.card:ℝ)*Y.card) := by
  let e (x y : V) : ℝ := if G.Adj x y then 1 else 0
  have per A (hA : A ∈ R.parts) B (hB : B ∈ R.parts) :
      (∑ x ∈ A, ∑ y ∈ B, cellDensity G R x y) = ∑ x ∈ A, ∑ y ∈ B, e x y := by
    have eq x (hx : x ∈ A) y (hy : y ∈ B) : cellDensity G R x y = crossDensity G A B := by
      simp [cellDensity,R.part_eq_of_mem hA hx,R.part_eq_of_mem hB hy]
    rw [sum_congr rfl (fun x hx => sum_congr rfl (fun y hy => eq x hx y hy))]
    dsimp [e]
    rw [edge_rectangle]
    simp; ring
  rw [←edge_rectangle]
  apply Eq.trans (sum_on_blocks R X Y hX hY hRX hRY (cellDensity G R)).symm
  apply Eq.trans _ (sum_on_blocks R X Y hX hY hRX hRY e)
  exact sum_congr rfl (fun A ha => sum_congr rfl fun B hb => per A (mem_filter.mp ha).1 B (mem_filter.mp hb).1)

public theorem energy_gain_cell (R Q : Finpartition S) (hq : Q ≤ R) (A B : Finset V)
    (ha : A ∈ R.parts) (hb : B ∈ R.parts) :
    (∑ x ∈ A, ∑ y ∈ B, (cellDensity G Q x y)^2) - (A.card:ℝ)*B.card*(crossDensity G A B)^2 =
    ∑ x ∈ A, ∑ y ∈ B, (cellDensity G Q x y-crossDensity G A B)^2 := by
  let p := crossDensity G A B
  have av := cell_average G Q A B (R.le ha) (R.le hb) (respects_parent R Q hq ha) (respects_parent R Q hq hb)
  have eq x y : (cellDensity G Q x y-p)^2 = (cellDensity G Q x y)^2 + p^2 - (2*p)*cellDensity G Q x y := by ring
  change _ = ∑ x ∈ A, ∑ y ∈ B, (cellDensity G Q x y-p)^2
  simp_rw [eq,sum_sub_distrib,sum_add_distrib,←mul_sum,av]
  simp only [sum_const,nsmul_eq_mul,p]; ring

/-- An irregular witness occupying at least ρ on either side forces an
increase of ρ⁴ times the area of the whole cell. -/
public theorem witness_energy (Q : Finpartition S) (A B X Y : Finset V) (ρ : ℝ) (hρ : 0 < ρ)
    (hAS : A ⊆ S) (hBS : B ⊆ S) (hX : X ⊆ A) (hY : Y ⊆ B)
    (hRX : respects Q X) (hRY : respects Q Y) (hx : ρ*A.card ≤ X.card) (hy : ρ*B.card ≤ Y.card)
    (hneA : A.Nonempty) (hneB : B.Nonempty) (hbad : ρ < |crossDensity G X Y-crossDensity G A B|) :
    ρ^4*((A.card:ℝ)*B.card) ≤ ∑ x ∈ A, ∑ y ∈ B, (cellDensity G Q x y-crossDensity G A B)^2 := by
  let g (z : V × V) := cellDensity G Q z.1 z.2-crossDensity G A B
  let m := (X.card:ℝ)*Y.card
  let p := crossDensity G X Y-crossDensity G A B
  have hm : 0 < m := mul_pos ((mul_pos hρ (Nat.cast_pos.mpr hneA.card_pos)).trans_le hx)
    ((mul_pos hρ (Nat.cast_pos.mpr hneB.card_pos)).trans_le hy)
  have sumg : (∑ z ∈ X ×ˢ Y, g z) = m*p := by
    simp only [sum_product,g,sum_sub_distrib,sum_const,nsmul_eq_mul]
    rw [cell_average G Q X Y (hX.trans hAS) (hY.trans hBS) hRX hRY]
    simp [m,p,card_product]; ring
  have hcs : (m*p)^2 ≤ m*∑ z ∈ X ×ˢ Y, (g z)^2 := by
    have h := sum_mul_sq_le_sq_mul_sq (X ×ˢ Y) (fun _ => (1:ℝ)) g
    simpa [sumg,card_product,m] using h
  have gain : m*p^2 ≤ ∑ z ∈ X ×ˢ Y, (g z)^2 := (mul_le_mul_iff_of_pos_left hm).mp (by nlinarith only [hcs])
  have harea := mul_le_mul hx hy (mul_nonneg hρ.le (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have hpow : ρ^2 ≤ p^2 := (pow_le_pow_left₀ hρ.le hbad.le 2).trans_eq (sq_abs p)
  have h := mul_le_mul (show ρ^2*((A.card:ℝ)*B.card) ≤ m by dsimp [m]; nlinarith only [harea]) hpow (sq_nonneg ρ) hm.le
  apply le_trans (by nlinarith only [h] : ρ^4*((A.card:ℝ)*B.card) ≤ m*p^2) (gain.trans ?_)
  simp only [sum_product,g]
  apply (sum_le_sum (fun x _ => sum_le_sum_of_subset_of_nonneg hY (fun y _ _ => sq_nonneg _))).trans
  exact sum_le_sum_of_subset_of_nonneg hX (fun x _ _ => sum_nonneg fun y _ => sq_nonneg _)
end Vu.Revised

module
public import Vu.PairMatrix
public import Vu.HardDecomposition
namespace Vu
open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

public theorem sum_partition_classes {P : Finset V} (R : Finpartition P) (f : V → ℝ) :
    ∑ A ∈ R.parts, ∑ x ∈ A, f x = ∑ x ∈ P, f x := by
  calc
    _ = ∑ x ∈ R.parts.biUnion id, f x := (sum_biUnion R.supIndep.pairwiseDisjoint).symm
    _ = _ := by rw [R.biUnion_parts]

/-- Add the block estimates on one partition without any loss depending on
the number of classes. The squared bound c²|A||B| is needed for every
ordered block; the resulting coefficient is exactly c²|P|². -/
public theorem partition_block_matrix_bound (P : Finset V) (R : Finpartition P) (M : V → V → ℝ) (c : ℝ)
    (hsupp : ∀ x y, x ∉ P ∨ y ∉ P → M x y = 0)
    (hblock : ∀ A ∈ R.parts, ∀ B ∈ R.parts, ∀ f : V → ℝ,
      ∑ x ∈ A, (∑ y ∈ B, M x y*f y)^2 ≤ c^2*A.card*B.card*∑ y ∈ B, f y^2)
    (f : V → ℝ) :
    ∑ x, (∑ y, M x y*f y)^2 ≤ (c*P.card)^2 * ∑ y ∈ P, f y^2 := by
  classical
  let v x (B : Finset V) := ∑ y ∈ B, M x y*f y
  have hB (B : Finset V) (h : B ∈ R.parts) : 0 < (B.card : ℝ) :=
    Nat.cast_pos.mpr (card_pos.mpr (R.nonempty_of_mem_parts h))
  have hfull (x : V) : ∑ y, M x y*f y = ∑ B ∈ R.parts, v x B := by
    rw [sum_partition_classes R (fun y => M x y*f y)]
    exact (sum_subset (subset_univ _) (fun y _ hy => by simp [hsupp x y (Or.inr hy)])).symm
  have hrow (x : V) : (∑ B ∈ R.parts, v x B)^2 ≤ (P.card:ℝ)*∑ B ∈ R.parts, (v x B)^2/B.card := by
    have hh := sum_mul_sq_le_sq_mul_sq R.parts (fun B => √(B.card:ℝ)) (fun B => v x B/√(B.card:ℝ))
    have hy (B : Finset V) (hb : B ∈ R.parts) : √(B.card:ℝ)*(v x B/√(B.card:ℝ)) = v x B := by
      field_simp [Real.sqrt_ne_zero'.mpr (hB B hb)]
    simp_rw [div_pow,Real.sq_sqrt (Nat.cast_nonneg _)] at hh
    rw [sum_congr rfl hy] at hh
    have heq : (∑ B ∈ R.parts, (B.card:ℝ)) = P.card := by exact_mod_cast R.sum_card_parts
    rwa [heq] at hh
  have ha (A : Finset V) (hA : A ∈ R.parts) :
      (∑ x ∈ A, ∑ B ∈ R.parts, (v x B)^2/B.card) ≤ c^2*A.card*∑ y ∈ P, f y^2 := by
    rw [sum_comm,← sum_partition_classes R (fun y => f y^2),mul_sum]
    apply sum_le_sum
    intro B hb
    rw [← sum_div]
    apply (div_le_iff₀ (hB B hb)).mpr
    exact (hblock A hA B hb f).trans_eq (by ring)
  have hout (x : V) (hx : x ∉ P) : (∑ y, M x y*f y)^2 = 0 := by
    simp [hsupp x _ (Or.inl hx)]
  rw [← sum_subset (subset_univ P) (fun x _ hx => hout x hx)]
  simp_rw [hfull]
  apply (sum_le_sum (fun x _ => hrow x)).trans
  rw [← mul_sum,← sum_partition_classes R (fun x => ∑ B ∈ R.parts, (v x B)^2/B.card)]
  apply (mul_le_mul_of_nonneg_left (sum_le_sum ha) (Nat.cast_nonneg _)).trans_eq
  rw [← sum_mul,← mul_sum]
  have heq : (∑ A ∈ R.parts, (A.card:ℝ)) = P.card := by exact_mod_cast R.sum_card_parts
  rw [heq]
  ring

/-- The regular-pair portion of Lemma 4.6 on one piece. The relation may
choose any subset of regular sparse blocks; deleting all nongood rows
and columns preserves the estimate. -/
public theorem regular_partition_matrix (G : SimpleGraph V) [DecidableRel G.Adj]
    (P good : Finset V) (R : Finpartition P) (sel : Finset V → Finset V → Prop)
    (ρ δ : ℝ) (hρ : 0 < ρ) (hδ : 0 < δ) (hin : good ⊆ P)
    (hsel : ∀ A B, sel A B → ¬ irregularPair G ρ A B ∧ crossDensity G A B < 1-δ) :
    let M : V → V → ℝ := (by
      classical
      exact fun x y =>
        if x ∈ good ∧ y ∈ good ∧ sel (R.part x) (R.part y) then
          centeredEntry G (crossDensity G (R.part x) (R.part y)) x y else 0)
    ∀ f : V → ℝ, ∑ x, (∑ y, M x y * f y)^2 ≤
      (((4*ρ)^(1/3:ℝ)/δ)*P.card)^2 * ∑ y ∈ P, f y^2 := by
  classical
  intro M f
  apply partition_block_matrix_bound P R M ((4*ρ)^(1/3:ℝ)/δ) _ _ f
  · rintro x y (hx|hy)
    · have hn : x ∉ good := fun h => hx (hin h)
      simp [M,hn]
    · have hn : y ∉ good := fun h => hy (hin h)
      simp [M,hn]
  · intro A hA B hB g
    let f' (y : V) := if y ∈ good then g y else 0
    let v (x : V) := ∑ y ∈ B, centeredEntry G (crossDensity G A B) x y*f' y
    by_cases hab : sel A B
    · obtain ⟨hir,hd⟩ := hsel A B hab
      have hh := regular_pair_matrix_bound G A B ρ δ hρ hδ hd (by
        intro X hX Y hY hx hy
        exact le_of_not_gt (fun h => hir ⟨X,hX,Y,hY,hx,hy,h⟩)) f'
      have hrow (x : V) (hx : x ∈ A) : (∑ y ∈ B, M x y*g y)^2 ≤ (v x)^2 := by
        by_cases hg : x ∈ good
        · apply le_of_eq
          congr 1
          apply sum_congr rfl
          intro y hy
          by_cases hy' : y ∈ good <;> simp [M,hg,hy',R.part_eq_of_mem hA hx,R.part_eq_of_mem hB hy,hab,f']
        · simp [M,hg,sq_nonneg]
      apply ((sum_le_sum hrow).trans hh).trans
      rw [div_pow,mul_pow,Real.sq_sqrt (by positivity : 0 ≤ (A.card:ℝ)*B.card)]
      have hf : (∑ y ∈ B, f' y^2) ≤ ∑ y ∈ B, g y^2 :=
        sum_le_sum (fun y _ => by dsimp [f']; split <;> simp [sq_nonneg])
      apply (mul_le_mul_of_nonneg_left hf (by positivity)).trans_eq
      ring
    · have hz (x : V) (hx : x ∈ A) : (∑ y ∈ B, M x y*g y)^2 = 0 := by
        have hz' (y : V) (hy : y ∈ B) : M x y*g y = 0 := by
          simp [M,R.part_eq_of_mem hA hx,R.part_eq_of_mem hB hy,hab]
        simp [sum_eq_zero hz']
      rw [sum_eq_zero hz]
      positivity
end Vu

module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Vu

/-- Greedy list coloring with a different list and a different degree bound at
each vertex. Empty graphs and empty color types are allowed. -/
public theorem color_of_degree_lt_list_card {V C : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (L : V → Finset C)
    (hL : ∀ v, G.degree v < (L v).card) :
    ∃ f : V → C, (∀ v, f v ∈ L v) ∧ ∀ ⦃x y⦄, G.Adj x y → f x ≠ f y := by
  classical
  cases isEmpty_or_nonempty V with
  | inl h =>
    exact ⟨isEmptyElim, fun v => isEmptyElim v, fun {v} => isEmptyElim v⟩
  | inr h =>
    obtain ⟨v₀⟩ := h
    obtain ⟨c₀, _⟩ := Finset.card_pos.mp (Nat.zero_lt_of_lt (hL v₀))
    have extend (S : Finset V) :
        ∃ f : V → C, (∀ v ∈ S, f v ∈ L v) ∧
          ∀ x ∈ S, ∀ y ∈ S, G.Adj x y → f x ≠ f y := by
      induction S using Finset.induction_on with
      | empty => exact ⟨fun _ => c₀, by simp, by simp⟩
      | @insert x S hx ih =>
        obtain ⟨f, hlist, hproper⟩ := ih
        let N := G.neighborFinset x ∩ S
        have hcard : (N.image f).card < (L x).card :=
          Finset.card_image_le.trans_lt ((Finset.card_le_card Finset.inter_subset_left).trans_lt (hL x))
        obtain ⟨color, hcolor, hfresh⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
        have hdiff (v : V) (hv : v ∈ S) (hadj : G.Adj x v) : color ≠ f v := by
          intro heq
          apply hfresh
          rw [heq]
          exact Finset.mem_image_of_mem f (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x v).mpr hadj, hv⟩)
        let g := Function.update f x color
        refine ⟨g, ?_, ?_⟩
        · intro v hv
          rcases Finset.mem_insert.mp hv with rfl | hv
          · simpa [g] using hcolor
          · have hvx : v ≠ x := fun e => hx (e ▸ hv)
            simpa [g, hvx] using hlist v hv
        · intro v hv w hw hadj
          rcases Finset.mem_insert.mp hv with rfl | hv
          · have hwv : w ≠ v := hadj.ne.symm
            have hwS := Finset.mem_of_mem_insert_of_ne hw hwv
            simpa [g, hwv] using hdiff w hwS hadj
          · have hvx : v ≠ x := fun e => hx (e ▸ hv)
            rcases Finset.mem_insert.mp hw with rfl | hw
            · simpa [g, hvx] using (hdiff v (Finset.mem_of_mem_insert_of_ne hv hvx) hadj.symm).symm
            · have hwx : w ≠ x := fun e => hx (e ▸ hw)
              simpa [g, hvx, hwx] using hproper v hv w hw hadj
    obtain ⟨f, hlist, hproper⟩ := extend Finset.univ
    exact ⟨f, fun v => hlist v (Finset.mem_univ _),
      fun {v w} => hproper v (Finset.mem_univ _) w (Finset.mem_univ _)⟩

/-- The fixed-ratio conclusion for every `ζ ≥ 1`, with the explicit degree
threshold `⌈1 / ε⌉`. Here the lists have at least `D + 1` colors. -/
public theorem fixedRatio_of_one_le {ζ ε : ℝ} (hζ : 1 ≤ ζ) (hε : 0 < ε)
    {D : ℕ} (hD : ⌈1 / ε⌉₊ ≤ D) {V C : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hdeg : ∀ v, G.degree v ≤ D) (L : V → Finset C)
    (hL : ∀ v, ⌊(ζ + ε) * D⌋₊ ≤ (L v).card) :
    ∃ f : V → C, (∀ v, f v ∈ L v) ∧ ∀ ⦃x y⦄, G.Adj x y → f x ≠ f y := by
  have h₁ : 1 ≤ (D : ℝ) * ε := (div_le_iff₀ hε).mp (Nat.ceil_le.mp hD)
  have h₂ : (D : ℝ) ≤ ζ * D := by
    simpa using mul_le_mul_of_nonneg_right hζ (Nat.cast_nonneg D)
  have hfloor : D + 1 ≤ ⌊(ζ + ε) * D⌋₊ := by
    apply Nat.le_floor
    simpa [Nat.cast_add, add_mul, mul_comm ε] using add_le_add h₂ h₁
  exact color_of_degree_lt_list_card G L (fun v => (hdeg v).trans_lt (hfloor.trans (hL v)))

end Vu

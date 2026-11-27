module
public import Vu.ConsecutivePacking
namespace Vu.Revised
open Finset
variable {V A : Type*} [Fintype V] [DecidableEq V] [DecidableEq A]

/-- Pack whole components with a second common vertex. In a component with
only one common vertex, each incident neighbor supplies its own singleton. -/
public theorem pack_components (H : SimpleGraph V) [DecidableRel H.Adj] (J : SimpleGraph A)
    (L partners : V → Finset A) (W : A → Finset V) (D : ℕ) (s : ℝ)
    (hs : 1 ≤ s) (hdeg : ∀ x, H.degree x ≤ D)
    (hw : ∀ x y : V, x ≠ y → ∀ Q : Finset A, Q ⊆ L x → Q ⊆ L y → ((Q.biUnion W).card:ℝ) ≤ s)
    (hl : ∀ x z, H.Adj x z → ∃ a : ↥(L x), a.val ∈ partners z ∧ z ∈ W a) :
    ∃ (U : V → Finset (Finset V)) (test : V → A → Finset V),
      (∀ x, (U x).biUnion id = H.neighborFinset x) ∧
      (∀ x, ∀ B ∈ U x, (B.card:ℝ) ≤ s) ∧ (∀ x, ((U x).card:ℝ) ≤ 2*D/s+1) ∧
      (∀ x a, test x a = ∅ ∨ test x a ∈ U x) ∧
      (∀ x z, H.Adj x z → ∃ a ∈ L x, a ∈ partners z ∧ (x ∈ splitRows J L a ∨ z ∈ test x a)) ∧
      (∀ x a, a ∈ L x → ∀ b ∈ L x, J.Adj a b → test x a = test x b) := by
  classical
  let label x z (he : H.Adj x z) := (hl x z he).choose
  let comp x (a : ↥(L x)) := labelComponent J (L x) a
  let uniqueRow (x : V) (Q : Finset A) := ∀ y, Q ⊆ L y → y=x
  let key x z : Finset A ⊕ V := if he : H.Adj x z then
    let Q := comp x (label x z he)
    if uniqueRow x Q then Sum.inr z else Sum.inl Q
    else Sum.inr z
  have size (x : V) (k : Finset A ⊕ V) :
      (((H.neighborFinset x).filter fun z => key x z = k).card:ℝ) ≤ s := by
    let F := (H.neighborFinset x).filter fun z => key x z = k
    rcases F.eq_empty_or_nonempty with hem|⟨z,hz⟩
    · change (F.card:ℝ) ≤ s
      simpa [hem] using (zero_le_one.trans hs)
    obtain ⟨hn,he⟩ := mem_filter.mp hz
    have haz := (H.mem_neighborFinset x z).mp hn
    cases k with
    | inr v =>
      apply (Nat.cast_le.mpr (card_le_card (t := {v}) ?_)).trans (by simpa using hs)
      intro y hy
      obtain ⟨hy,hk⟩ := mem_filter.mp hy
      have hey := (H.mem_neighborFinset x y).mp hy
      simp only [key,dif_pos hey] at hk
      split at hk
      · simpa using hk
      · contradiction
    | inl Q =>
      have eqcomp (y : V) (hey : H.Adj x y) (hy : key x y = Sum.inl Q) :
          comp x (label x y hey) = Q ∧ ¬uniqueRow x Q := by
        simp only [key,dif_pos hey] at hy
        split at hy
        next => contradiction
        next h => exact ⟨Sum.inl.inj hy,Sum.inl.inj hy ▸ h⟩
      obtain ⟨heq,hn⟩ := eqcomp z haz he
      change ¬∀ y, Q ⊆ L y → y=x at hn
      push Not at hn
      obtain ⟨y,hsub,hne⟩ := hn
      have hx : Q ⊆ L x := heq ▸ filter_subset _ _
      apply (Nat.cast_le.mpr (card_le_card ?_)).trans (hw x y hne.symm Q hx hsub)
      intro t ht
      obtain ⟨ht,hkey⟩ := mem_filter.mp ht
      have het := (H.mem_neighborFinset x t).mp ht
      have qeq := (eqcomp t het hkey).1
      have mem : (label x t het).val ∈ comp x (label x t het) := (component_mem ..).mpr ⟨_,rfl⟩
      exact mem_biUnion.mpr ⟨_,qeq ▸ mem,(hl x t het).choose_spec.2⟩
  choose U pack hcover hsize hnum htest hkey using fun x => pack_fibers_using pack_neighbor_groups (H.neighborFinset x) (key x) D s
    (zero_lt_one.trans_le hs) (by simpa using hdeg x) (size x)
  let test x a := if ha : a ∈ L x then
    let Q := comp x ⟨a,ha⟩
    if uniqueRow x Q then ∅ else pack x (Sum.inl Q)
    else ∅
  refine ⟨U,test,hcover,hsize,hnum,?_,?_,?_⟩
  · intro x a
    by_cases ha : a ∈ L x
    · simp only [test,dif_pos ha]; split <;> first | exact Or.inl rfl | exact htest x _
    · simp [test,ha]
  · intro x z he
    let a := label x z he
    refine ⟨a,a.property,(hl x z he).choose_spec.1,?_⟩
    by_cases h : uniqueRow x (comp x a)
    · left
      simpa [splitRows] using (show ∃ ha : a.val ∈ L x, ∀ y, labelComponent J (L x) ⟨a.val,ha⟩ ⊆ L y → y=x from ⟨a.property,h⟩)
    · apply Or.inr
      simpa [test,a.property,h,key,he,a] using hkey x z ((H.mem_neighborFinset _ _).mpr he)
  · intro x a ha b hb hab
    have eq : comp x ⟨a,ha⟩ = comp x ⟨b,hb⟩ := by
      have hh := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        (G := J.induce (L x : Set A)) (v := ⟨a,ha⟩) (w := ⟨b,hb⟩) hab
      ext c; simp only [comp,component_mem,hh]
    simp only [test,dif_pos ha,dif_pos hb,eq]
end Vu.Revised

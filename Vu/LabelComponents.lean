module

public import Vu.SplitGroups
public import Vu.OmissionChoice

namespace Vu
open Finset
variable {A V : Type*} [DecidableEq A]

/-- Component of a carried label in the overlap graph induced on one vertex's labels. -/
@[expose] public noncomputable def labelComponent (J : SimpleGraph A) (L : Finset A) (a : ↥L) : Finset A := by
  classical
  exact L.filter fun b => ∃ hb : b ∈ L,
    (J.induce (L : Set A)).connectedComponentMk ⟨b,hb⟩ = (J.induce (L : Set A)).connectedComponentMk a

public theorem component_mem (J : SimpleGraph A) (L : Finset A) (a : ↥L) (b : A) :
    b ∈ labelComponent J L a ↔ ∃ hb : b ∈ L,
      (J.induce (L : Set A)).connectedComponentMk ⟨b,hb⟩ = (J.induce (L : Set A)).connectedComponentMk a := by
  classical
  exact ⟨fun h => (mem_filter.mp h).2, fun h => mem_filter.mpr ⟨h.choose,h⟩⟩

public theorem labelComponent_preconnected (J : SimpleGraph A) (L : Finset A) (a : ↥L) :
    (J.induce (labelComponent J L a : Set A)).Preconnected := by
  let K := J.induce (L : Set A)
  let C := K.connectedComponentMk a
  let F : C.toSimpleGraph →g J.induce (labelComponent J L a : Set A) :=
    { toFun := fun v => ⟨v.val.val,(component_mem ..).mpr ⟨v.val.property,v.property⟩⟩
      map_rel' := fun h => h }
  intro x y
  obtain ⟨hx, hx'⟩ := (component_mem ..).mp x.property
  obtain ⟨hy, hy'⟩ := (component_mem ..).mp y.property
  let u : C := ⟨⟨x,hx⟩,hx'⟩
  let v : C := ⟨⟨y,hy⟩,hy'⟩
  exact (C.connected_toSimpleGraph.preconnected u v).map F

/-- Keep a component with a second witness and split a unique-witness component
into singleton labels. -/
@[expose] public noncomputable def labelGroup (J : SimpleGraph A) (L : V → Finset A)
    (x : V) (a : ↥(L x)) : Finset A := by
  classical
  exact if ∃ y ≠ x, labelComponent J (L x) a ⊆ L y then labelComponent J (L x) a else {a.val}

public theorem labelGroup_witnesses (J : SimpleGraph A) (L : V → Finset A)
    (x : V) (a : ↥(L x)) (htwo : ∃ y ≠ x, a.val ∈ L y) :
    a.val ∈ labelGroup J L x a ∧ labelGroup J L x a ⊆ L x ∧
      ∃ y ≠ x, labelGroup J L x a ⊆ L y := by
  classical
  unfold labelGroup
  split
  next h => exact ⟨(component_mem ..).mpr ⟨a.property,rfl⟩, filter_subset _ _, h⟩
  next _ => simpa [a.property] using htwo

/-- The split exception for the *actual* rooted component, on all vertices. -/
@[expose] public noncomputable def splitRows [Fintype V] (J : SimpleGraph A) (L : V → Finset A)
    (a : A) : Finset V := by
  classical
  exact univ.filter fun x => ∃ ha : a ∈ L x, ∀ y, labelComponent J (L x) ⟨a,ha⟩ ⊆ L y → y = x

/-- Two adjacent labels at a vertex belong to the same group unless their
component was split. This gives the separation alternative in Lemma 4.8. -/
public theorem equal_group_of_adj [Fintype V] (J : SimpleGraph A) (L : V → Finset A)
    (x : V) (a b : ↥(L x)) (hab : J.Adj a b) (hn : x ∉ splitRows J L a) :
    labelGroup J L x a = labelGroup J L x b := by
  classical
  have heq := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
    (G := J.induce (L x : Set A)) (v := a) (w := b) hab
  have hcomp : labelComponent J (L x) a = labelComponent J (L x) b := by
    ext z
    rw [component_mem,component_mem,heq]
  have htwo : ∃ y ≠ x, labelComponent J (L x) a ⊆ L y := by
    by_contra! h
    apply hn
    exact mem_filter.mpr ⟨mem_univ _,a.property,fun y hy => Classical.byContradiction (fun ne => h y ne hy)⟩
  simp only [labelGroup, hcomp] at htwo ⊢
  simp [htwo]

/-- Lemma 4.7 specialized to the component computed from the overlap graph. -/
public theorem actual_split_bound [Fintype A] [Fintype V] (J : SimpleGraph A) [DecidableRel J.Adj]
    (L : V → Finset A) (a : A) (r : ℕ) (h D : ℝ) (hr : 1 ≤ r) (hh : 1 ≤ h)
    (hD : h^(2*r) = D) (hdeg : ∀ a, (J.degree a : ℝ) ≤ 2*r*h^2) (hL : ∀ x, (L x).card ≤ r) :
    ((splitRows J L a).card : ℝ) ≤ (r * (r.factorial : ℝ) * (2*r : ℝ)^(r-1)) * (D/h^2) := by
  classical
  let C (x : V) := if ha : a ∈ L x then labelComponent J (L x) ⟨a,ha⟩ else ∅
  apply split_vertex_bound J a r h D hr hh hD hdeg _ C (fun x b => b ∈ L x)
  · intro x hx
    obtain ⟨ha,_⟩ := (mem_filter.mp hx).2
    have heq : C x = labelComponent J (L x) ⟨a,ha⟩ := by simp [C,ha]
    rw [heq]
    exact ⟨(component_mem ..).mpr ⟨ha,rfl⟩, (card_le_card (filter_subset _ _)).trans (hL x),
      labelComponent_preconnected J (L x) ⟨a,ha⟩⟩
  · intro x hx b hb
    obtain ⟨ha,_⟩ := (mem_filter.mp hx).2
    simp [C,ha] at hb
    exact (component_mem ..).mp hb |>.choose
  · intro x hx y _ hy
    obtain ⟨ha,hub⟩ := (mem_filter.mp hx).2
    apply hub y
    intro b hb
    exact hy b (by simpa [C,ha] using hb)
end Vu

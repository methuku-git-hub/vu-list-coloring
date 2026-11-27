module
public import Vu.RevisedPacking
public import Vu.RootedComponents
namespace Vu.Revised
open Finset
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

/-- For fixed h the split exceptions for a label have a bound independent of Δ. -/
public theorem split_bound_fixed (J : SimpleGraph A) [DecidableRel J.Adj] (L : V → Finset A)
    (a : A) (r m : ℕ) (hj : ∀ b, J.degree b ≤ m) (hr : ∀ x, (L x).card ≤ r) :
    (splitRows J L a).card ≤ 2^(∑ n ∈ range r, m^n) := by
  classical
  let C (x : V) := if ha : a ∈ L x then labelComponent J (L x) ⟨a,ha⟩ else ∅
  have mem {x : V} (hx : x ∈ splitRows J L a) : ∃ ha : a ∈ L x, ∀ y, labelComponent J (L x) ⟨a,ha⟩ ⊆ L y → y=x := by simpa [splitRows] using hx
  have shape x (hx : x ∈ splitRows J L a) : a ∈ C x ∧ (C x).card ≤ r ∧
      (J.induce (C x : Set A)).Preconnected := by
    obtain ⟨ha,_⟩ := mem hx
    have he : C x = labelComponent J (L x) ⟨a,ha⟩ := by simp [C,ha]
    rw [he]
    exact ⟨(component_mem ..).mpr ⟨ha,rfl⟩,(card_le_card (filter_subset _ _)).trans (hr x),
      labelComponent_preconnected J (L x) ⟨a,ha⟩⟩
  apply rooted_component_count J a m r hj _ C (fun x hx => (shape x hx).1)
    (fun x hx => (shape x hx).2.1) (fun x hx => (shape x hx).2.2)
  intro x hx y hy eq
  obtain ⟨ha,hub⟩ := mem hx
  obtain ⟨hb,_⟩ := mem hy
  exact (hub y (by
    change labelComponent J (L x) ⟨a,ha⟩ ⊆ L y
    have sub : C y ⊆ L y := by simp only [C,dif_pos hb]; exact filter_subset .. 
    simpa [C,ha] using (eq ▸ sub : C x ⊆ L y))).symm

/-- A frequent label determines a single omission at each row, valid for all columns. -/
public theorem omit_columns (H : SimpleGraph V) [DecidableRel H.Adj] (L P : V → Finset A)
    (U : V → Finset (Finset V)) (test : V → A → Finset V) (T : Finset V) (D r k h B : ℕ)
    (hh : 0 < h) (hD : T.card ≤ D) (hL : ∀ x, (L x).card ≤ r) (hP : ∀ z, (P z).card ≤ k)
    (ht : ∀ x a, test x a = ∅ ∨ test x a ∈ U x)
    (J : SimpleGraph A) (hsplit : ∀ a, (splitRows J L a).card ≤ B)
    (hadj : ∀ a b, a ≠ b → D/(h*h) < (T.filter (fun y => a ∈ L y ∧ b ∈ L y)).card → J.Adj a b)
    (hedge : ∀ x z, H.Adj x z → ∃ a ∈ L x, a ∈ P z ∧ (x ∈ splitRows J L a ∨ z ∈ test x a))
    (heq : ∀ x a, a ∈ L x → ∀ b ∈ L x, J.Adj a b → test x a = test x b) :
    ∃ S : V → Finset V, (∀ x ∈ T, S x = ∅ ∨ S x ∈ U x) ∧ ∀ z,
      (T.filter fun x => H.Adj x z ∧ z ∉ S x).card ≤ k*(B+(r+1)*(D/h)) := by
  classical
  let l := D/h
  let q := D/(h*h)
  let F := univ.filter fun a => l < (T.filter fun x => a ∈ L x).card
  have freq := frequent_label_count T L r l (fun x _ => hL x)
  have hf : F.card ≤ r*h := by
    have hd : D < (l+1)*h := by dsimp [l]; simpa [Nat.mul_comm] using Nat.lt_mul_div_succ D hh
    have hh' := Nat.mul_le_mul_right r hD
    by_contra! hn
    have h₁ := Nat.mul_lt_mul_of_pos_right hn (Nat.zero_lt_succ l)
    change F.card*(l+1) ≤ _ at freq
    nlinarith only [h₁,freq,hh',Nat.mul_le_mul_right r hd.le]
  let has x := ∃ a ∈ L x, a ∈ F
  let S x := if e : has x then test x e.choose else ∅
  refine ⟨S,?_,?_⟩
  · intro x _
    by_cases e : has x
    · simpa [S,e] using ht x e.choose
    · simp [S,e]
  let miss a := T.filter (fun x => a ∈ L x ∧ (x ∈ splitRows J L a ∨ test x a ≠ S x))
  have hmiss a : (miss a).card ≤ B+(r+1)*l := by
    by_cases ha : a ∈ F
    · let overlap b := T.filter fun x => a ∈ L x ∧ b ∈ L x
      let small b := if (overlap b).card ≤ q then overlap b else ∅
      have hbnd : (miss a).card ≤ (splitRows J L a).card + F.card*q := by
        apply missed_label_card_le (miss a) (splitRows J L a) F small q
        · intro x hx
          obtain ⟨hxt,hax,exc|hne⟩ := mem_filter.mp hx
          · exact Or.inl exc
          have e : has x := ⟨a,hax,ha⟩
          obtain ⟨hb,hf⟩ := e.choose_spec
          have hne' : test x a ≠ test x e.choose := by simpa [S,e] using hne
          have hsmall : (overlap e.choose).card ≤ q := by
            by_contra! hn
            apply hne' (heq x a hax _ hb (hadj _ _ (fun he => hne' (he ▸ rfl)) hn))
          exact Or.inr ⟨_,hf,by simp [small,hsmall,overlap,hxt,hax,hb]⟩
        · intro b _; dsimp [small]; split <;> simp_all
      have hq : h*q ≤ l := (Nat.le_div_iff_mul_le hh).mpr (by
        have hval := Nat.div_mul_le_self D (h*h)
        dsimp [q]; simpa [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hval)
      have hu := Nat.mul_le_mul_right q hf
      exact hbnd.trans (by nlinarith only [hsplit a,hu,Nat.mul_le_mul_left r hq,Nat.zero_le l])
    · have hcount : (T.filter fun x => a ∈ L x).card ≤ l := by simpa [F] using ha
      have sub : miss a ⊆ T.filter fun x => a ∈ L x := fun x hx => mem_filter.mpr ⟨(mem_filter.mp hx).1,(mem_filter.mp hx).2.1⟩
      exact ((card_le_card sub).trans hcount).trans (by nlinarith [Nat.zero_le (r*l)])
  intro z
  apply residual_column_card_le _ (P z) miss _ _ ?_ (hP z) (fun a _ => hmiss a)
  intro x hx
  obtain ⟨hxt,he,hn⟩ := mem_filter.mp hx
  obtain ⟨a,hL,hP,exc|hz⟩ := hedge x z he
  · exact ⟨a,hP,mem_filter.mpr ⟨hxt,hL,Or.inl exc⟩⟩
  · exact ⟨a,hP,mem_filter.mpr ⟨hxt,hL,Or.inr (fun e => hn (e ▸ hz))⟩⟩
end Vu.Revised

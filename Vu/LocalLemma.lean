module

public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith

namespace Vu
open Finset MeasureTheory

/-- None of the bad events indexed by `S` occurs. -/
@[expose] public def avoids {I Ω : Type*} (A : I → Set Ω) (S : Finset I) : Set Ω :=
  {ω | ∀ i ∈ S, ω ∉ A i}

private theorem avoidance_chain {I : Type*} [DecidableEq I] (P : Finset I → ℝ)
    (x : I → ℝ) (hx : ∀ i, x i ≤ 1) (S T : Finset I) (hTS : T ⊆ S)
    (step : ∀ U ⊂ S, ∀ i ∉ U, (1-x i)*P U ≤ P (insert i U)) :
    P T * ∏ j ∈ S \ T, (1-x j) ≤ P S := by
  have aux (R : Finset I) (hR : R ⊆ S \ T) :
      P T * ∏ j ∈ R, (1-x j) ≤ P (T ∪ R) := by
    induction R using Finset.induction_on with
    | empty => simp
    | @insert j R hj ih =>
      have hjst := mem_sdiff.mp (hR (mem_insert_self _ _))
      have hr : R ⊆ S \ T := fun z hz => hR (mem_insert_of_mem hz)
      have hu : T ∪ R ⊆ S := union_subset hTS (hr.trans sdiff_subset)
      have hjout : j ∉ T ∪ R := by simp [hj, hjst.2]
      have hstrict : T ∪ R ⊂ S := Finset.ssubset_iff_subset_ne.mpr
        ⟨hu, fun heq => hjout (heq ▸ hjst.1)⟩
      have hinsert : T ∪ insert j R = insert j (T ∪ R) := by ext; simp
      rw [prod_insert hj, hinsert, mul_left_comm]
      exact (mul_le_mul_of_nonneg_left (ih hr) (sub_nonneg.mpr (hx j))).trans
        (step _ hstrict j hjout)
  simpa only [union_sdiff_of_subset hTS] using aux (S \ T) (subset_refl _)

/-- Multiplicative induction underlying the finite asymmetric Local Lemma.
`P S` is the probability of avoiding `S`. The recurrence follows by
dropping dependent events from the conditioning set. -/
public theorem local_lemma_product {I : Type*} [DecidableEq I] (P : Finset I → ℝ)
    (p x : I → ℝ) (Γ : I → Finset I)
    (hP : ∀ S, 0 ≤ P S) (h₀ : P ∅ = 1) (hx₀ : ∀ i, 0 ≤ x i) (hx : ∀ i, x i ≤ 1)
    (hsmall : ∀ i, p i ≤ x i * ∏ j ∈ Γ i, (1-x j))
    (hrec : ∀ S, ∀ i ∉ S, P S - P (insert i S) ≤ p i * P (S \ Γ i)) (S : Finset I) :
    ∏ j ∈ S, (1-x j) ≤ P S := by
  have step (T : Finset I) : ∀ i ∉ T, (1-x i) * P T ≤ P (insert i T) := by
    induction T using Finset.strongInductionOn with
    | _ T ih =>
      intro i hi
      let U := T \ Γ i
      have hchain := avoidance_chain P x hx T U sdiff_subset ih
      have hsub : T \ U ⊆ Γ i := by
        dsimp [U]
        rw [sdiff_sdiff_self_left]
        exact inter_subset_right
      have hprod : (∏ j ∈ Γ i, (1-x j)) ≤ ∏ j ∈ T \ U, (1-x j) :=
        prod_le_prod_of_subset_of_le_one₀ hsub (fun j _ => sub_nonneg.mpr (hx j))
          (fun j _ _ => sub_le_self _ (hx₀ j))
      have hbound : p i * P U ≤ x i * P T := by
        calc
          _ ≤ (x i * ∏ j ∈ Γ i, (1-x j)) * P U := mul_le_mul_of_nonneg_right (hsmall i) (hP U)
          _ = x i * (P U * ∏ j ∈ Γ i, (1-x j)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left
            ((mul_le_mul_of_nonneg_left hprod (hP U)).trans hchain) (hx₀ i)
      have h := (hrec T i hi).trans hbound
      linarith
  have h := avoidance_chain P x hx S ∅ (empty_subset _) (fun T _ => step T)
  simpa [h₀] using h

/-- The asymmetric Lovász Local Lemma (Lemma 2.4). The product lower bound
holds for each subfamily. The equality in `hind` expresses precisely the
joint independence from avoidance of any set of nonneighbors used in the proof. -/
public theorem asymmetric_local_lemma {Ω I : Type*} [MeasurableSpace Ω] [DecidableEq I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : I → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (Γ : I → Finset I) (x : I → ℝ) (hx : ∀ i, 0 ≤ x i ∧ x i < 1)
    (hind : ∀ i S, i ∉ S → Disjoint S (Γ i) →
      μ.real (avoids A S ∩ A i) = μ.real (A i) * μ.real (avoids A S))
    (hsmall : ∀ i, μ.real (A i) ≤ x i * ∏ j ∈ Γ i, (1-x j)) (S : Finset I) :
    (∏ j ∈ S, (1-x j)) ≤ μ.real (avoids A S) ∧ 0 < μ.real (avoids A S) := by
  classical
  have h₀ : μ.real (avoids A ∅) = 1 := by simp [avoids]
  have hrec (T : Finset I) (i : I) (hi : i ∉ T) :
      μ.real (avoids A T) - μ.real (avoids A (insert i T)) ≤ μ.real (A i) * μ.real (avoids A (T \ Γ i)) := by
    have hins : avoids A (insert i T) = avoids A T \ A i := by ext ω; simp [avoids]; tauto
    have hsplit := measureReal_inter_add_sdiff (μ := μ) (s := avoids A T) (hA i)
    have hsub : avoids A T ∩ A i ⊆ avoids A (T \ Γ i) ∩ A i := by
      intro ω hω
      exact ⟨fun j hj => hω.1 j (mem_sdiff.mp hj).1, hω.2⟩
    have hprob := measureReal_mono (μ := μ) hsub
    rw [hind i _ (fun h => hi (mem_sdiff.mp h).1) sdiff_disjoint] at hprob
    rw [hins]
    linarith
  have h := local_lemma_product (fun T => μ.real (avoids A T)) (fun i => μ.real (A i)) x Γ
    (fun _ => measureReal_nonneg) h₀ (fun i => (hx i).1) (fun i => (hx i).2.le) hsmall hrec S
  exact ⟨h, (prod_pos (fun j _ => sub_pos.mpr (hx j).2)).trans_le h⟩


/-- Symmetric form in Lemma 2.4, including dependency degree zero. The
single choice `x = 1 - exp(-1/(d+1))` works throughout. -/
public theorem symmetric_local_lemma {Ω I : Type*} [MeasurableSpace Ω] [DecidableEq I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : I → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (Γ : I → Finset I) (d : ℕ) (q : ℝ) (hdeg : ∀ i, (Γ i).card ≤ d)
    (hind : ∀ i S, i ∉ S → Disjoint S (Γ i) →
      μ.real (avoids A S ∩ A i) = μ.real (A i) * μ.real (avoids A S))
    (hpr : ∀ i, μ.real (A i) ≤ q) (hsmall : Real.exp 1 * q * (d+1 : ℝ) ≤ 1) (S : Finset I) :
    0 < μ.real (avoids A S) := by
  let t : ℝ := 1 / (d+1 : ℝ)
  have hd : 0 < (d+1 : ℝ) := by positivity
  have ht : 0 < t := div_pos zero_lt_one hd
  let y := Real.exp (-t)
  have hy : 0 < y := Real.exp_pos _
  have hy₁ : y ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht.le)
  have hq : q ≤ t * Real.exp (-1) := by
    dsimp [t]
    rw [Real.exp_neg, ← div_eq_mul_inv]
    exact (le_div_iff₀ (Real.exp_pos _)).mpr ((le_div_iff₀ hd).mpr (by linarith only [hsmall]))
  have hdexp : (1-y)*y^d = (Real.exp t - 1) * Real.exp (-1) := by
    have hn : (d : ℝ) * (-t) = t - 1 := by
      dsimp [t]
      field_simp
      ring
    dsimp [y]
    rw [← Real.exp_nat_mul, hn, sub_mul, one_mul, ← Real.exp_add, sub_mul, one_mul, ← Real.exp_add]
    ring_nf
  have hbase : q ≤ (1-y) * y^d := by
    rw [hdexp]
    exact hq.trans (mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp t]) (Real.exp_pos _).le)
  apply (asymmetric_local_lemma μ A hA Γ (fun _ => 1-y)
    (fun _ => ⟨sub_nonneg.mpr hy₁, by linarith⟩) hind _ S).2
  intro i
  simp only [sub_sub_cancel, prod_const]
  exact (hpr i).trans (hbase.trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hy.le hy₁ (hdeg i)) (sub_nonneg.mpr hy₁)))

public theorem one_sub_sum_le_prod {I : Type*} (s : Finset I) (w : I → ℝ)
    (h₀ : ∀ i, 0 ≤ w i) (h₁ : ∀ i, w i ≤ 1) :
    1 - ∑ i ∈ s, w i ≤ ∏ i ∈ s, (1-w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [sum_insert hi, prod_insert hi]
    calc
      _ ≤ (1-w i)*(1-∑ j ∈ s, w j) := by
        nlinarith [mul_nonneg (h₀ i) (sum_nonneg (s := s) (fun j _ => h₀ j))]
      _ ≤ _ := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr (h₁ i))

/-- Local Lemma form used to complete the partial coloring in Section 5.3.
Each neighbor sum at most 1/4 suffices with the choices xᵢ = 2 Pr(Aᵢ). -/
public theorem low_probability_local_lemma {Ω I : Type*} [MeasurableSpace Ω] [DecidableEq I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : I → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (Γ : I → Finset I)
    (hind : ∀ i S, i ∉ S → Disjoint S (Γ i) →
      μ.real (avoids A S ∩ A i) = μ.real (A i) * μ.real (avoids A S))
    (hsmall : ∀ i, μ.real (A i) < 1/2) (hdep : ∀ i, ∑ j ∈ Γ i, μ.real (A j) ≤ 1/4)
    (S : Finset I) : 0 < μ.real (avoids A S) := by
  let x i := 2 * μ.real (A i)
  have hx i : 0 ≤ x i ∧ x i < 1 :=
    ⟨mul_nonneg (by norm_num) measureReal_nonneg, by dsimp [x]; linarith [hsmall i]⟩
  apply (asymmetric_local_lemma μ A hA Γ x hx hind _ S).2
  intro i
  have hprod := one_sub_sum_le_prod (Γ i) x (fun j => (hx j).1) (fun j => (hx j).2.le)
  have hsum : ∑ j ∈ Γ i, x j = 2 * ∑ j ∈ Γ i, μ.real (A j) := by simp [x, mul_sum]
  rw [hsum] at hprod
  have hh : (1 : ℝ)/2 ≤ ∏ j ∈ Γ i, (1-x j) := by linarith [hdep i]
  have := mul_le_mul_of_nonneg_left hh (hx i).1
  dsimp [x] at this ⊢
  linarith

end Vu

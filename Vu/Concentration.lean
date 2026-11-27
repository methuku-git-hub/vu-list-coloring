module

public import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic.Linarith

namespace Vu
open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

/-- Lemma 2.3. This specialization of mathlib's sub-Gaussian bound gives
the one-sided Hoeffding inequality with the factor 2 in the exponent. -/
public theorem hoeffding_lower {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [Nonempty I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : I → Ω → ℝ) (K u : ℝ)
    (hK : 0 < K) (hu : 0 < u) (hindep : iIndepFun Y μ)
    (hm : ∀ i, AEMeasurable (Y i) μ) (hb : ∀ i, ∀ᵐ ω ∂μ, Y i ω ∈ Set.Icc 0 K) :
    μ.real {ω | ∑ i, Y i ω ≤ (∑ i, ∫ x, Y i x ∂μ) - u} ≤
      Real.exp (-2 * u^2 / (Fintype.card I * K^2)) := by
  classical
  let m i := ∫ x, Y i x ∂μ
  let X i ω := m i - Y i ω
  let c : ℝ≥0 := (‖K - 0‖₊ / 2)^2
  have hX : iIndepFun X μ := hindep.comp (fun i t => m i - t) (fun _ => by fun_prop)
  have hmgf (i : I) : HasSubgaussianMGF (X i) c μ := by
    have h := (hasSubgaussianMGF_of_mem_Icc (hm i) (hb i)).neg
    simpa [X, m, c, Pi.neg_def, neg_sub] using h
  have ht := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hX
    (s := univ) (fun i _ => hmgf i) hu.le
  have heq : {ω | ∑ i, Y i ω ≤ (∑ i, ∫ x, Y i x ∂μ) - u} = {ω | u ≤ ∑ i, X i ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, X, m, sum_sub_distrib]
    constructor <;> intro h <;> linarith
  rw [heq]
  apply ht.trans_eq
  congr 1
  simp [c, Real.norm_of_nonneg hK.le]
  ring

/-- The concentration step of Lemma 6.3. An expected loss of at most
ε/4 per list entry gives a lower-tail bound for a loss of ε per entry. -/
public theorem retained_list_weight {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [Nonempty I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : I → Ω → ℝ) (K ε : ℝ)
    (hK : 0 < K) (hε : 0 < ε) (hindep : iIndepFun Y μ)
    (hm : ∀ i, AEMeasurable (Y i) μ) (hb : ∀ i, ∀ᵐ ω ∂μ, Y i ω ∈ Set.Icc 0 K)
    (hmean : (Fintype.card I : ℝ) * (1 - ε/4) ≤ ∑ i, ∫ x, Y i x ∂μ) :
    μ.real {ω | ∑ i, Y i ω < (Fintype.card I : ℝ) * (1-ε)} ≤
      Real.exp (-(9 * ε^2 / (8 * K^2)) * (Fintype.card I : ℝ)) := by
  let k : ℝ := Fintype.card I
  have hk : 0 < k := Nat.cast_pos.mpr Fintype.card_pos
  let u := 3 * k * ε / 4
  have hu : 0 < u := by dsimp [u]; positivity
  have h := hoeffding_lower μ Y K u hK hu hindep hm hb
  have hsub : {ω | ∑ i, Y i ω < (Fintype.card I : ℝ) * (1-ε)} ⊆
      {ω | ∑ i, Y i ω ≤ (∑ i, ∫ x, Y i x ∂μ) - u} := by
    intro ω hw
    change ∑ i, Y i ω < k * (1-ε) at hw
    change k * (1-ε/4) ≤ _ at hmean
    change _ ≤ _ - 3 * k * ε / 4
    linarith
  apply ((measureReal_mono hsub).trans h).trans_eq
  congr 1
  change -2 * (3 * k * ε / 4)^2 / (k*K^2) = -(9*ε^2/(8*K^2))*k
  field_simp
  ring

end Vu

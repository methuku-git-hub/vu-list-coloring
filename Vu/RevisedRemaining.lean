module
public import Vu.RevisedOffers
namespace Vu.Revised
open Finset

private theorem list_sum_map_mono {C : Type*} (l : List C) {f g : C → ℝ}
    (h : ∀ d ∈ l, f d ≤ g d) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons d l ih =>
    simp only [List.map_cons,List.sum_cons]
    exact add_le_add (h _ (List.mem_cons_self ..)) (ih (fun j hj => h j (List.mem_cons_of_mem d hj)))

/-- Fixed-color estimate in Lemma 6.4 with the actual offer distributions
of all other colors, after fixing the exposed color. A bounds Δ times
each individual mark probability; K bounds the retained weights. -/
public theorem fixed_offer_tail {V C : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) (others : List C) (D : ℕ)
    (lam₀ : C → V → ℝ) (h₀ : ∀ d x, 0 ≤ lam₀ d x) (w : V → ℝ)
    (p ν L A K : ℝ) (hD : 0 < D) (hT : T.card ≤ D) (hp : 0 < p) (hpν : p ≤ ν) (hν : ν ≤ 1/32)
    (hL : 0 < L) (hA : 0 ≤ A) (hK : 0 ≤ K) (hw : ∀ x, 0 ≤ w x) (hcap : ∀ x ∈ T, w x ≤ K)
    (hout : ∀ x ∉ T, w x = 0) (hmass : setWeight w univ ≤ L)
    (hmax : ∀ d ∈ others, ∀ x ∈ T, lam₀ d x ≤ A/D)
    (hsum : ∀ x ∈ T, (others.map (fun d => lam₀ d x)).sum ≤ p)
    (hrem : ∀ x, 0 < w x → (1-ν)*p ≤ (others.map (fun d => lam₀ d x)).sum)
    (hneigh : ∀ d ∈ others, ∀ x ∈ T, 0 < lam₀ d x → ∑ y ∈ G.neighborFinset x, lam₀ d y ≤ ν) :
    let π d y := activation (lam₀ d y)
    let laws := others.map fun d => offerLaw G T (π d) (fun y => (activation_odds _ (h₀ d y)).1) (fun y => (activation_odds _ (h₀ d y)).2.1.le)
    let u := ν*p*L
    let V₁ := (1+K^2*(1+A)*p)*D
    coverageAverage laws (fun S => if (1-(1-4*ν)*p)*L < setWeight w univ-setWeight w S then 1 else 0) ∅ ≤
      Real.exp (-u^2/(2*V₁)) := by
  classical
  intro π laws u V₁
  have hzero d y : 0 ≤ π d y := (activation_odds _ (h₀ d y)).1
  have hone d y : π d y ≤ 1 := (activation_odds _ (h₀ d y)).2.1.le
  have hpi d y : π d y ≤ lam₀ d y := div_le_self (h₀ d y) (by linarith [h₀ d y])
  let q d := offerLaw G T (π d) (hzero d) (hone d)
  let lam d := ∑ x ∈ T, lam₀ d x
  have hd : 0 < (D:ℝ) := Nat.cast_pos.mpr hD
  have hν' : 0 ≤ 1-ν := by linarith
  have nonneg d : 0 ≤ lam d := sum_nonneg (fun x _ => h₀ d x)
  have hsingle d (hm : d ∈ others) : lam d ≤ A := by
    apply (sum_le_sum (fun x hx => hmax d hm x hx)).trans
    simp only [sum_const,nsmul_eq_mul]
    exact (mul_le_mul_of_nonneg_right (Nat.cast_le (α := ℝ) |>.mpr hT) (div_nonneg hA hd.le)).trans_eq
      (by field_simp)
  have hcomm (l : List C) : (l.map lam).sum = ∑ x ∈ T, (l.map (fun d => lam₀ d x)).sum := by
    induction l with
    | nil => simp
    | cons d l ih => simp [lam,sum_add_distrib,ih]
  have htotal : (others.map lam).sum ≤ p*D := by
    rw [hcomm]
    apply (sum_le_sum hsum).trans
    simpa [mul_comm] using mul_le_mul_of_nonneg_right (Nat.cast_le (α := ℝ) |>.mpr hT) hp.le
  have hscale (l : List C) (a : ℝ) (f : C → ℝ) : (l.map (fun d => a*f d)).sum = a*(l.map f).sum := by
    induction l with
    | nil => simp
    | cons d l ih => simp [ih,mul_add]
  have hmo d := offer_law_moments G T (π d) (hzero d) (hone d) w K hw hK hcap
  have hv : (laws.map (fun Q => Q.mean (fun S => setWeight w S^2))).sum ≤ V₁ := by
    change ((others.map q).map _).sum ≤ V₁
    rw [List.map_map]
    apply (list_sum_map_mono others (g := fun d => (K^2*(1+A))*lam d) (fun d hm => ?_)).trans
    · rw [hscale]
      have hh := mul_le_mul_of_nonneg_left htotal (by positivity : 0 ≤ K^2*(1+A))
      dsimp only [V₁]; linarith
    · apply (hmo d).2.trans
      have hsumπ : (∑ x ∈ T, π d x) ≤ lam d := sum_le_sum (fun x _ => hpi d x)
      have hnπ : 0 ≤ ∑ x ∈ T, π d x := sum_nonneg (fun x _ => hzero d x)
      have hsq := mul_le_mul hsumπ (hsumπ.trans (hsingle d hm)) hnπ (nonneg d)
      apply mul_le_mul_of_nonneg_left (by nlinarith only [hsq,hsumπ] : (∑ x ∈ T, π d x)+(∑ x ∈ T, π d x)^2 ≤ (1+A)*lam d) (sq_nonneg K) |>.trans_eq
      ring
  have hcov : (1-3*ν)*p*setWeight w univ ≤ coverageAverage laws (setWeight w) ∅ := by
    rw [union_expected_weight]; simp only [setWeight,notMem_empty,ite_false,mul_sum]
    apply sum_le_sum; intro x _
    by_cases hh : 0 < w x
    · have hxT : x ∈ T := by by_contra hn; exact hh.ne' (hout x hn)
      have hprob := another_offer G T others lam₀ h₀ x hxT ν p hν hp hpν (hrem x hh) (hsum x hxT)
        (fun d hd => hneigh d hd x hxT)
      rw [mul_comm _ (w x)]
      dsimp only [laws]; rw [List.map_map]
      exact mul_le_mul_of_nonneg_left hprob (hw x)
    · simp [le_antisymm (le_of_not_gt hh) (hw x)]
  have hνp : 0 < ν := hp.trans_le hpν
  have hcoef : 0 ≤ 1-(1-3*ν)*p := by nlinarith only [hν,hpν,mul_nonneg (hp.le.trans hpν) hp.le]
  have hupper : setWeight w univ-coverageAverage laws (setWeight w) ∅ ≤ (1-(1-3*ν)*p)*L := by
    linarith only [hcov,mul_le_mul_of_nonneg_left hmass hcoef]
  apply le_trans _ (union_lower_tail_of_bound laws w hw u V₁ (by dsimp [u]; positivity) hv (by dsimp [V₁]; positivity))
  apply coverage_mono; intro S
  split
  next h =>
    have hh : setWeight w S ≤ coverageAverage laws (setWeight w) ∅-u := by dsimp [u]; linarith only [h,hupper]
    simp [hh]
  next => split <;> norm_num
end Vu.Revised

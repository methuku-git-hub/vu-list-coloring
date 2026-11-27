module
public import Vu.OfferMoments
namespace Vu
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
public theorem fixed_color_offer_tail {V C : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (T : Finset V) (others : List C) (D : ℕ)
    (π : C → V → ℝ) (h₀ : ∀ d x, 0 ≤ π d x) (h₁ : ∀ d x, π d x ≤ 1) (w : V → ℝ)
    (p ν L A K : ℝ) (hD : 0 < D) (hT : T.card ≤ D) (hp : 0 < p) (hpν : p ≤ ν) (hν : ν ≤ 1/200)
    (hL : 0 < L) (hA : 0 ≤ A) (hK : 0 ≤ K) (hw : ∀ x, 0 ≤ w x) (hcap : ∀ x ∈ T, w x ≤ K)
    (hout : ∀ x ∉ T, w x = 0) (hmass : setWeight w univ ≤ L)
    (hmax : ∀ d ∈ others, ∀ x ∈ T, π d x ≤ A/D)
    (hsum : ∀ x ∈ T, (others.map (fun d => π d x)).sum ≤ p)
    (hrem : ∀ x, 0 < w x → (1-ν)*p ≤ (others.map (fun d => π d x)).sum)
    (hneigh : ∀ d ∈ others, ∀ x ∈ T, 0 < π d x → ∑ y ∈ G.neighborFinset x, π d y ≤ ν) :
    let laws := others.map fun d => offerLaw G T (π d) (h₀ d) (h₁ d)
    let u := ν*p*L
    let V₁ := (1+K^2*(1+A)*p)*D
    coverageAverage laws (fun S => if (1-(1-5*ν)*p)*L < setWeight w univ-setWeight w S then 1 else 0) ∅ ≤
      Real.exp (-u^2/(2*(V₁+K*A*u/3))) := by
  classical
  intro laws u V₁
  let q d := offerLaw G T (π d) (h₀ d) (h₁ d)
  let lam d := ∑ x ∈ T, π d x
  have hd : 0 < (D:ℝ) := Nat.cast_pos.mpr hD
  have hν' : 0 ≤ 1-ν := by linarith
  have nonneg d : 0 ≤ lam d := sum_nonneg (fun x _ => h₀ d x)
  have hsingle d (hm : d ∈ others) : lam d ≤ A := by
    apply (sum_le_sum (fun x hx => hmax d hm x hx)).trans
    simp only [sum_const,nsmul_eq_mul]
    exact (mul_le_mul_of_nonneg_right (Nat.cast_le (α := ℝ) |>.mpr hT) (div_nonneg hA hd.le)).trans_eq
      (by field_simp)
  have hcomm (l : List C) : (l.map lam).sum = ∑ x ∈ T, (l.map (fun d => π d x)).sum := by
    induction l with
    | nil => simp
    | cons d l ih => simp [lam,sum_add_distrib,ih]
  have htotal : (others.map lam).sum ≤ p*D := by
    rw [hcomm]
    apply (sum_le_sum hsum).trans
    simpa [mul_comm] using mul_le_mul_of_nonneg_right (Nat.cast_le (α := ℝ) |>.mpr hT) hp.le
  have hmo d := offer_law_moments G T (π d) (h₀ d) (h₁ d) w K hw hK hcap
  have hscale (l : List C) (a : ℝ) (f : C → ℝ) : (l.map (fun d => a*f d)).sum = a*(l.map f).sum := by
    induction l with
    | nil => simp
    | cons d l ih => simp [ih,mul_add]
  apply remaining_weight_tail_of_bound laws w hw p ν L (K*A) V₁ hp hpν hν hL hmass (mul_nonneg hK hA)
  · intro Q hQ
    obtain ⟨d,hm,rfl⟩ := List.mem_map.mp hQ
    exact (hmo d).1.trans (mul_le_mul_of_nonneg_left (hsingle d hm) hK)
  · intro x hx
    have hxT : x ∈ T := by by_contra hn; exact hx.ne' (hout x hn)
    change _ ≤ ((others.map q).map (hitProbability · x)).sum
    rw [List.map_map]
    apply le_trans _ (list_sum_map_mono others (f := fun d => (1-ν)*π d x) (fun d hm =>
      offer_probability_lower G T (π d) (h₀ d) (h₁ d) x hxT ν (hneigh d hm x hxT)))
    rw [hscale]
    exact (by simpa [pow_two,mul_assoc] using mul_le_mul_of_nonneg_left (hrem x hx) hν')
  · change ((others.map q).map (fun Q => Q.mean (fun S => setWeight w S^2))).sum ≤ V₁
    rw [List.map_map]
    apply (list_sum_map_mono others (g := fun d => (K^2*(1+A))*lam d) (fun d hm => ?_)).trans
    · rw [hscale]
      have hh := mul_le_mul_of_nonneg_left htotal (by positivity : 0 ≤ K^2*(1+A))
      dsimp only [V₁]; linarith
    · apply (hmo d).2.trans
      nlinarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hsingle d hm) (nonneg d)) (sq_nonneg K)]
  · dsimp [V₁]; positivity
end Vu

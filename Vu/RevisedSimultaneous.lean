module
public import Vu.SimultaneousRound
public import Vu.RevisedEvents
public import Vu.VertexWeightTail
namespace Vu.Revised
open Finset
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
  {G : SimpleGraph V} [DecidableRel G.Adj] {D k R : ℕ} {a b M η : ℝ}
  (d : SignedDecomposition G D k R b M η) {L : V → Finset C} (s : ColoringState G L k)

public theorem dependency_count (x : V) : (by classical exact
    (univ.filter fun y => ¬Disjoint (roundBall (influence d) x 3) (roundBall (influence d) y 3)).card) ≤ (D+1)^12 := by
  classical
  let H := influence d
  apply (card_le_card (t := roundBall H x 6) ?_).trans ((roundBall_card H (D^2) (influence_degree d) x 6).trans ?_)
  · intro y hy
    obtain ⟨z,hboth⟩ := not_disjoint_iff_nonempty_inter.mp (mem_filter.mp hy).2
    obtain ⟨hx,hz⟩ := mem_inter.mp hboth
    obtain ⟨p,hp⟩ := (roundBall_walk H y z 3).mp hz
    exact roundBall_comp H hx ((roundBall_walk H z y 3).mpr ⟨p.reverse,by simpa using hp⟩)
  · have hh : D^2+1 ≤ (D+1)^2 := by rw [add_sq]; omega
    exact (Nat.pow_le_pow_left hh 6).trans_eq (by rw [←pow_mul])

/-- The union bound counts only colors in the vertex's original list. -/
public theorem round_vertex_failure (ν p τ cap r : ℝ) (hr : 0 ≤ r) (q : C → FiniteLaw (V → Bool))
    (hc : ∀ x, (L x).card = k)
    (htot : ∀ x, s.color x = none → (FiniteLaw.independent q).chance (badTotal d s a ν p τ cap x) ≤ r)
    (htest : ∀ x c, 0 < s.weight x c → ∀ i ∈ indices d x,
      (FiniteLaw.independent q).chance (badTest d s a ν p τ cap x c i) ≤ r) (x : V) :
    (FiniteLaw.independent q).chance (badAt d s a ν p τ cap x) ≤ (1+k*((R:ℝ)+1))*r := by
  classical
  let μ := FiniteLaw.independent q
  let t := badTotal d s a ν p τ cap x
  let e := badTest d s a ν p τ cap x
  have empty_le : μ.chance (fun _ => False) ≤ r := by simpa [FiniteLaw.chance,FiniteLaw.mean_const] using hr
  have ht : μ.chance (fun ω => s.color x = none ∧ t ω) ≤ r := by
    by_cases h : s.color x = none
    · simpa only [h,true_and] using htot x h
    · simpa only [h,false_and] using empty_le
  have he (c : C) : μ.chance (fun ω => 0 < s.weight x c ∧ ∃ i ∈ indices d x, e c i ω) ≤ ((R:ℝ)+1)*r := by
    by_cases h : 0 < s.weight x c
    · simp only [h,true_and]
      apply (μ.chance_exists_le _ _).trans
      apply (sum_le_sum (htest x c h)).trans
      simp only [sum_const,nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ hr
      exact_mod_cast index_card d x
    · simp only [h,false_and]
      exact empty_le.trans (by nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) R) hr])
  apply (μ.chance_or_le _ _).trans
  apply (add_le_add ht ((μ.chance_exists_le _ _).trans (sum_le_sum (fun c _ => he c)))).trans
  simp [hc]; ring_nf; rfl

/-- The positive-mass mark outcome meets every tested inequality and
uses only entries having positive current weight. -/
public theorem exists_round_marks (ν p τ cap κ : ℝ)
    (h₀ : ∀ c y, 0 ≤ activation (markProb s p c y)) (h₁ : ∀ c y, activation (markProb s p c y) ≤ 1)
    (hdeg : ∀ y, G.degree y ≤ D) (hk : k ≤ 2*D)
    (hcut : ((D:ℝ)+1)^12*(1+2*D*(R+1))*Real.exp (-κ*D) ≤ 1/4)
    (hbad : ∀ x, (FiniteLaw.independent (fun c => markLaw _ (h₀ c) (h₁ c))).chance (badAt d s a ν p τ cap x) ≤
      (1+k*((R:ℝ)+1))*Real.exp (-κ*D)) :
    ∃ ω : C → V → Bool, (∀ x c, ω c x = true → 0 < s.weight x c) ∧
      ∀ x, ¬badAt d s a ν p τ cap x ω := by
  classical
  let π c y := activation (markProb s p c y)
  let q x := markLaw (fun c => π c x) (fun c => h₀ c x) (fun c => h₁ c x)
  let μ := FiniteLaw.independent q
  let A x (f : V → C → Bool) := badAt d s a ν p τ cap x (fun c y => f y c)
  let r := (1+2*(D:ℝ)*(R+1))*Real.exp (-κ*D)
  let N := ((D:ℝ)+1)^12
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hN : 1 ≤ N := one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) D])
  have hsmall : N*r ≤ 1/4 := by dsimp only [N,r]; linarith only [hcut]
  have hprob x : μ.chance (A x) ≤ r := by
    have ht := FiniteLaw.mean_transpose_marks π h₀ h₁
      (fun ω => if badAt d s a ν p τ cap x ω then (1:ℝ) else 0)
    apply le_trans _ ((hbad x).trans ?_)
    · apply le_of_eq
      unfold FiniteLaw.chance
      convert ht using 2
    · apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      gcongr
      exact_mod_cast hk
  obtain ⟨f,hf,hs⟩ := FiniteLaw.coordinate_lll_small_mass q A (fun x => roundBall (influence d) x 3)
    (bad_at_local d s a ν p τ cap) (fun x => by linarith only [hprob x,hsmall,mul_le_mul_of_nonneg_right hN hr]) (by
      intro x
      apply (sum_le_sum (fun y _ => hprob y)).trans
      simp only [sum_const,nsmul_eq_mul]
      apply le_trans _ hsmall
      apply mul_le_mul_of_nonneg_right _ hr
      dsimp only [N]
      exact_mod_cast dependency_count d x)
  refine ⟨fun c x => f x c,?_,hs⟩
  intro x c hm
  apply lt_of_le_of_ne (s.nonneg x c)
  intro hz
  apply hf.ne'
  apply prod_eq_zero (mem_univ x)
  apply prod_eq_zero (mem_univ c)
  simp [hm,π,activation,markProb,←hz,Bernoulli.mass]
end Vu.Revised

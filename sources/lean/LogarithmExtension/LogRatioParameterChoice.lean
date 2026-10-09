import LogarithmExtension.LogRatioParameterDimension

/-!
# A simultaneous finite-dimensional margin for every rational nu > 3

The seed, truncation scale, and half-dimension are selected in this order.
Exceptional rational approximations are not used in these choices.
-/

noncomputable section
namespace LogarithmExtension.LogRatio.ParameterChoice

open Filter ParameterSeeds ParameterDimension
open scoped Topology

variable {nu : ℚ} (P : SeedData nu)

def target : ℝ := (nu : ℝ)*(P.B : ℝ)^2
def lambda (n : ℕ) : ℝ := Real.exp (Real.log (target P) -
  (2*Real.log (target P)+Real.log 64)/(2*(n : ℝ)+2))
def netMargin (n : ℕ) : ℝ :=
  ((2*(n : ℝ)+2)/(2*(n : ℝ)+3))*lambda P n-1-((nu : ℝ)-1)*(P.v : ℝ)

theorem target_pos (hnu : 0 < nu) : 0 < target P := by
  exact mul_pos (by exact_mod_cast hnu) (sq_pos_of_pos P.B_pos_real)

theorem lambda_pos (n : ℕ) : 0 < lambda P n := Real.exp_pos _

theorem lambda_power (hnu : 0 < nu) (n : ℕ) :
    (lambda P n)^(2*n+2) = (target P)^(2*n)/64 := by
  rw [lambda, ← Real.exp_nat_mul]
  have hid : ((2*n+2 : ℕ) : ℝ)*(Real.log (target P)-
      (2*Real.log (target P)+Real.log 64)/(2*(n : ℝ)+2)) =
      ((2*n : ℕ) : ℝ)*Real.log (target P)-Real.log 64 := by
    push_cast
    have hn : 2*(n : ℝ)+2 ≠ 0 := by positivity
    field_simp
    ring
  rw [hid, Real.exp_sub, Real.exp_nat_mul, Real.exp_log (target_pos P hnu),
    Real.exp_log (by norm_num : (0 : ℝ) < 64)]

theorem tendsto_lambda (hnu : 0 < nu) :
    Tendsto (lambda P) atTop (𝓝 (target P)) := by
  have ht : Tendsto (fun n : ℕ => 2*(n : ℝ)+2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 (Tendsto.const_mul_atTop
      (by norm_num : (0 : ℝ) < 2) (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hd := ht.const_div_atTop (2*Real.log (target P)+Real.log 64)
  have h := Real.continuous_exp.continuousAt.tendsto.comp
    ((tendsto_const_nhds (x := Real.log (target P))).sub hd)
  unfold lambda
  simpa only [Function.comp_def, sub_zero, Real.exp_log (target_pos P hnu)] using h

theorem tendsto_netMargin (hnu : 0 < nu) :
    Tendsto (netMargin P) atTop (𝓝 P.gap) := by
  have ht : Tendsto (fun n : ℕ => 2*(n : ℝ)+3) atTop atTop :=
    tendsto_atTop_add_const_right atTop 3 (Tendsto.const_mul_atTop
      (by norm_num : (0 : ℝ) < 2) (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hr : Tendsto (fun n : ℕ => (2*(n : ℝ)+2)/(2*(n : ℝ)+3)) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub (ht.const_div_atTop 1)
    apply (show Tendsto (fun n : ℕ => 1-1/(2*(n : ℝ)+3)) atTop (𝓝 1) by
      simpa only [sub_zero] using h).congr'
    filter_upwards [] with n
    have hn : 2*(n : ℝ)+3 ≠ 0 := by positivity
    field_simp
    ring
  have h := ((hr.mul (tendsto_lambda P hnu)).sub_const 1).sub_const
    (((nu : ℝ)-1)*(P.v : ℝ))
  unfold netMargin
  simpa only [one_mul, target, SeedData.gap] using h

theorem exists_initial_scale : ∃ F : ℚ, (0 : ℝ) < F ∧
    2/(P.v : ℝ) < F ∧ (nu : ℝ)/F < P.gap/8 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (max (2/(P.v : ℝ)) (8*(nu : ℝ)/P.gap)))
  have hF : 1 < (N : ℝ) := lt_of_le_of_lt (le_max_left _ _) hN
  have hv : 2/(P.v : ℝ) < (N : ℝ) :=
    lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hN
  have hnu : 8*(nu : ℝ)/P.gap < (N : ℝ) :=
    lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hN
  refine ⟨N, by exact_mod_cast (show (0 : ℝ) < N by linarith), by exact_mod_cast hv, ?_⟩
  have hF0 : (0 : ℝ) < N := by linarith
  have hh := (div_lt_iff₀ P.gap_pos_real).mp hnu
  simp only [Rat.cast_natCast]
  apply (div_lt_iff₀ hF0).mpr
  nlinarith

structure Choice where
  F : ℚ
  n : ℕ
  F_pos : (0 : ℝ) < F
  F_large : 2/(P.v : ℝ) < F
  initial_margin : (nu : ℝ)/F < P.gap/8
  n_pos : 1 ≤ n
  shrink : (1+(sigma P n : ℝ))*(P.v : ℝ) < 1
  base_gap : 2*((2*n : ℕ)+3 : ℝ)/(sigma P n : ℝ)*(v0 P n : ℝ) < w0 P n
  dimension_margin :
    ((4+Real.log 4)*(F : ℝ)*(2*(n : ℝ))+2*Real.log 2)/(v0 P n : ℝ) +
      100*(K P n : ℝ)/(w0 P n : ℝ) < P.gap/8
  packing_margin : P.gap/2 < netMargin P n

/-- The geometric dimension and all non-auxiliary errors can be fixed before
selecting even one exceptional fraction. -/
theorem exists_choice (hnu : 3 < nu) : Nonempty (Choice P) := by
  obtain ⟨F, hF, hFv, hFm⟩ := exists_initial_scale P
  have ha : 0 ≤ (4+Real.log 4)*(F : ℝ) :=
    mul_nonneg (by have h := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); linarith) hF.le
  have hb : 0 ≤ 2*Real.log 2 := mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))
  have he := eventually_small_error P ((4+Real.log 4)*(F : ℝ)) (2*Real.log 2)
    (P.gap/8) ha hb (div_pos P.gap_pos_real (by norm_num))
  have hg := (tendsto_netMargin P (by linarith : 0 < nu)).eventually
    (lt_mem_nhds (show P.gap/2 < P.gap by linarith [P.gap_pos_real]))
  have hall : ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧
      (1+(sigma P n : ℝ))*(P.v : ℝ) < 1 ∧
      2*((2*n : ℕ)+3 : ℝ)/(sigma P n : ℝ)*(v0 P n : ℝ) < w0 P n ∧
      ((4+Real.log 4)*(F : ℝ)*(2*(n : ℝ))+2*Real.log 2)/(v0 P n : ℝ) +
        100*(K P n : ℝ)/(w0 P n : ℝ) < P.gap/8 ∧ P.gap/2 < netMargin P n := by
    filter_upwards [eventually_ge_atTop 1, eventually_shrink P, eventually_base_gap P, he, hg]
      with n hn hs hb he hg
    exact ⟨hn, hs, hb, he, hg⟩
  obtain ⟨n, hn, hs, hb, he, hg⟩ := hall.exists
  exact ⟨⟨F, n, hF, hFv, hFm, hn, hs, hb, he, hg⟩⟩

theorem exists_seed_and_choice (nu : ℚ) (hnu : 3 < nu) :
    ∃ P : SeedData nu, Nonempty (Choice P) :=
  ⟨explicitSeed nu hnu, exists_choice (explicitSeed nu hnu) hnu⟩

#print axioms lambda_power
#print axioms exists_seed_and_choice

end LogarithmExtension.LogRatio.ParameterChoice

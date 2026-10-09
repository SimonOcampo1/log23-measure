import LogarithmExtension.LogRatioParameterSeeds
import OAI.NumberTheory.PiExponent.LocalAlgebra.Dimension

/-!
# Even-dimensional rational weights for the two-base determinant

The half-dimension is n and the actual auxiliary dimension is 2*n.
The number of centers is a square, preserving rational base weights.
-/

noncomputable section
namespace LogarithmExtension.LogRatio.ParameterDimension

open Filter OAI.PiExponent ParameterSeeds
open scoped Topology

variable {nu : ℚ} (P : SeedData nu)

def J (n : ℕ) : ℕ := dimensionK P.C n
def K (n : ℕ) : ℕ := (J P n)^2
def w0 (n : ℕ) : ℚ := ((P.B^2)^n)⁻¹
def v0 (n : ℕ) : ℚ := 2*(J P n : ℚ)*P.v^n*w0 P n
def sigma (_P : SeedData nu) (n : ℕ) : ℚ := (100*((2*n+2 : ℕ) : ℚ))⁻¹

theorem J_one_le (n : ℕ) : 1 ≤ J P n :=
  dimensionK_one_le P.C (by exact_mod_cast P.C_gt_one.le) n

theorem J_pos (n : ℕ) : (0 : ℝ) < J P n := by
  exact_mod_cast (Nat.zero_lt_one.trans_le (J_one_le P n))

theorem K_pos (n : ℕ) : 0 < K P n := by
  exact pow_pos (Nat.zero_lt_one.trans_le (J_one_le P n)) 2

theorem w0_cast (n : ℕ) : (w0 P n : ℝ) = dimensionW ((P.B : ℝ)^2) n := by
  simp [w0, dimensionW]

theorem v0_cast (n : ℕ) : (v0 P n : ℝ) = dimensionV P.v ((P.B : ℝ)^2) P.C n := by
  simp [v0, dimensionV, J, w0_cast]

theorem w0_pos (n : ℕ) : (0 : ℝ) < w0 P n := by
  rw [w0_cast]
  exact dimensionW_pos _ (sq_pos_of_pos P.B_pos_real) n

theorem v0_pos (n : ℕ) : (0 : ℝ) < v0 P n := by
  rw [v0_cast]
  exact dimensionV_pos _ _ _ P.v_pos_real (sq_pos_of_pos P.B_pos_real)
    (by exact_mod_cast P.C_gt_one.le) n

theorem sigma_cast (n : ℕ) : (sigma P n : ℝ) = 1/(100*(2*(n : ℝ)+2)) := by
  simp [sigma]

theorem sigma_pos (n : ℕ) : (0 : ℝ) < sigma P n := by
  rw [sigma_cast]
  positivity

theorem volume_identity (n : ℕ) :
    (K P n : ℝ)*((w0 P n : ℝ)/v0 P n)^2*(P.v : ℝ)^(2*n) = 1/4 := by
  have h := dimension_volume P.v ((P.B : ℝ)^2) P.C P.v_pos_real
    (sq_pos_of_pos P.B_pos_real) (by exact_mod_cast P.C_gt_one.le) n
  rw [← w0_cast, ← v0_cast] at h
  change (J P n : ℝ)*((w0 P n : ℝ)/v0 P n)*(P.v : ℝ)^n = 1/2 at h
  have hh := congrArg (fun x : ℝ => x^2) h
  simpa only [K, Nat.cast_pow, mul_pow, pow_mul', mul_assoc,
    show (1/2 : ℝ)^2 = 1/4 by norm_num] using hh

theorem inflated_volume_lt_one (n : ℕ) :
    (1+3*(sigma P n : ℝ))^(2*n+2)*
      ((K P n : ℝ)*((w0 P n : ℝ)/v0 P n)^2*(P.v : ℝ)^(2*n)) < 1 := by
  rw [volume_identity]
  have hs := sigma_pos P n
  have he : 1+3*(sigma P n : ℝ) ≤ Real.exp (3*(sigma P n : ℝ)) := by
    simpa only [add_comm] using Real.add_one_le_exp (3*(sigma P n : ℝ))
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1+3*(sigma P n : ℝ)) he (2*n+2)
  rw [← Real.exp_nat_mul] at hp
  have hid : ((2*n+2 : ℕ) : ℝ)*(3*(sigma P n : ℝ)) = 3/100 := by
    rw [sigma_cast]
    push_cast
    have hn : 2*(n : ℝ)+2 ≠ 0 := by positivity
    field_simp
  rw [hid] at hp
  have he3 : Real.exp (3/100) < 3 :=
    (Real.exp_lt_exp.mpr (by norm_num : (3/100 : ℝ) < 1)).trans Real.exp_one_lt_three
  linarith

theorem K_div_w0_le (n : ℕ) :
    (K P n : ℝ)/(w0 P n : ℝ) ≤ (((P.C : ℝ)*P.B)^2)^n := by
  have hJ : (J P n : ℝ) ≤ (P.C : ℝ)^n := dimensionK_le _ P.C_pos_real.le n
  have hs : (J P n : ℝ)^2 ≤ ((P.C : ℝ)^n)^2 :=
    pow_le_pow_left₀ (J_pos P n).le hJ 2
  have h := mul_le_mul_of_nonneg_right hs (pow_nonneg (sq_nonneg (P.B : ℝ)) n)
  rw [pow_right_comm (P.C : ℝ) n 2] at h
  simpa only [K, Nat.cast_pow, w0, Rat.cast_inv, Rat.cast_pow, div_inv_eq_mul,
    mul_pow] using h

theorem v0_geometric_lower (n : ℕ) (hlarge : 2 ≤ (P.C : ℝ)^n) :
    ((P.C : ℝ)*P.v/(P.B : ℝ)^2)^n ≤ (v0 P n : ℝ) := by
  rw [v0_cast]
  exact dimensionV_geometric_lower _ _ _ P.v_pos_real (sq_pos_of_pos P.B_pos_real) n hlarge

theorem v0_div_w0_le (n : ℕ) :
    (v0 P n : ℝ)/(w0 P n : ℝ) ≤ 2*((P.C : ℝ)*P.v)^n := by
  have hJ : (J P n : ℝ) ≤ (P.C : ℝ)^n := dimensionK_le _ P.C_pos_real.le n
  have h := mul_le_mul_of_nonneg_right hJ (pow_pos P.v_pos_real n).le
  have hid : (v0 P n : ℝ)/(w0 P n : ℝ) = 2*(J P n : ℝ)*(P.v : ℝ)^n := by
    simp only [v0, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_pow]
    exact mul_div_cancel_right₀ _ (w0_pos P n).ne'
  rw [hid, mul_pow]
  linarith

theorem tendsto_error_majorant (a b : ℝ) :
    Tendsto (fun n : ℕ => (a*(2*(n : ℝ))+b)/((P.C : ℝ)*P.v/(P.B : ℝ)^2)^n +
      100*((((P.C : ℝ)*P.B)^2)^n)) atTop (𝓝 0) := by
  have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 P.growthBase_gt_one
  have h0 := tendsto_pow_const_div_const_pow_of_one_lt 0 P.growthBase_gt_one
  have hl := (h1.const_mul (2*a)).add (h0.const_mul b)
  have hs : ((P.C : ℝ)*P.B)^2 < 1 :=
    pow_lt_one₀ P.smallBase_pos.le P.smallBase_lt_one (by decide)
  have hg := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (sq_nonneg ((P.C : ℝ)*P.B)) hs).const_mul 100
  convert hl.add hg using 1
  · ext n
    simp only [pow_one, pow_zero]
    ring
  · simp

theorem eventually_small_error (a b epsilon : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      (a*(2*(n : ℝ))+b)/(v0 P n : ℝ) + 100*(K P n : ℝ)/(w0 P n : ℝ) < epsilon := by
  have he := (tendsto_error_majorant P a b).eventually (gt_mem_nhds hepsilon)
  have hf := (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < P.C by
    exact_mod_cast P.C_gt_one)).eventually (eventually_ge_atTop (2 : ℝ))
  filter_upwards [he, hf] with n he hf
  have hp : (0 : ℝ) < ((P.C : ℝ)*P.v/(P.B : ℝ)^2)^n :=
    pow_pos (zero_lt_one.trans P.growthBase_gt_one) n
  have hdiv := div_le_div_of_nonneg_left (by positivity : 0 ≤ a*(2*(n : ℝ))+b) hp
    (v0_geometric_lower P n hf)
  have hk := mul_le_mul_of_nonneg_left (K_div_w0_le P n) (by norm_num : (0 : ℝ) ≤ 100)
  rw [← mul_div_assoc] at hk
  exact (add_le_add hdiv hk).trans_lt he

theorem tendsto_sigma : Tendsto (fun n : ℕ => (sigma P n : ℝ)) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => 100*(2*(n : ℝ)+2)) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 100)
      (tendsto_atTop_add_const_right atTop 2 (Tendsto.const_mul_atTop
        (by norm_num : (0 : ℝ) < 2) (tendsto_natCast_atTop_atTop (R := ℝ))))
  simpa only [sigma_cast] using ht.const_div_atTop 1

theorem eventually_shrink :
    ∀ᶠ n : ℕ in atTop, (1+(sigma P n : ℝ))*(P.v : ℝ) < 1 := by
  have h := ((tendsto_sigma P).const_add 1).mul_const (P.v : ℝ)
  simp only [add_zero, one_mul] at h
  exact h.eventually (gt_mem_nhds (show (P.v : ℝ) < 1 by exact_mod_cast P.v_lt_one))

theorem tendsto_contact_majorant :
    Tendsto (fun n : ℕ => 400*(2*(n : ℝ)+2)*(2*(n : ℝ)+3)*
      ((P.C : ℝ)*P.v)^n) atTop (𝓝 0) := by
  have h0 := tendsto_pow_const_mul_const_pow_of_lt_one 0 P.contactBase_pos.le P.contactBase_lt_one
  have h1 := tendsto_pow_const_mul_const_pow_of_lt_one 1 P.contactBase_pos.le P.contactBase_lt_one
  have h2 := tendsto_pow_const_mul_const_pow_of_lt_one 2 P.contactBase_pos.le P.contactBase_lt_one
  convert ((h2.const_mul 1600).add (h1.const_mul 4000)).add (h0.const_mul 2400) using 1
  · ext n
    simp only [pow_one, pow_zero, one_mul]
    ring
  · simp

theorem eventually_base_gap : ∀ᶠ n : ℕ in atTop,
    2*((2*n : ℕ)+3 : ℝ)/(sigma P n : ℝ)*(v0 P n : ℝ) < w0 P n := by
  have h := (tendsto_contact_majorant P).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [h] with n hn
  have hc : 0 ≤ 200*(2*(n : ℝ)+2)*(2*(n : ℝ)+3) := by positivity
  have hh := mul_le_mul_of_nonneg_left (v0_div_w0_le P n) hc
  have hb : (200*(2*(n : ℝ)+2)*(2*(n : ℝ)+3)) *
      ((v0 P n : ℝ)/(w0 P n : ℝ)) < 1 := by nlinarith [hh]
  have hid : 2*((2*n : ℕ)+3 : ℝ)/(sigma P n : ℝ) =
      200*(2*(n : ℝ)+2)*(2*(n : ℝ)+3) := by
    rw [sigma_cast]
    simp only [Nat.cast_mul, Nat.cast_ofNat, one_div, div_inv_eq_mul]
    ring
  rw [hid]
  have hb' : (200*(2*(n : ℝ)+2)*(2*(n : ℝ)+3)*(v0 P n : ℝ))/(w0 P n : ℝ) < 1 := by
    simpa only [mul_div_assoc] using hb
  simpa only [one_mul] using (div_lt_iff₀ (w0_pos P n)).mp hb'

#print axioms volume_identity
#print axioms eventually_small_error
#print axioms eventually_base_gap

end LogarithmExtension.LogRatio.ParameterDimension

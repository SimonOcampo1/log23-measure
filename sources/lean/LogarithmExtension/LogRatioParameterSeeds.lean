import Mathlib

/-!
# Explicit rational seed parameters for every exponent above three

These are the rational formulas in the working argument. Their positive
margin and all base inequalities are proved uniformly, not by sampling nu.
-/

noncomputable section
namespace LogarithmExtension.LogRatio.ParameterSeeds

structure SeedData (nu : ℚ) where
  v : ℚ
  B : ℚ
  C : ℚ
  v_pos : 0 < v
  v_lt_one : v < 1
  B_pos : 0 < B
  B_lt_one : B < 1
  C_gt_one : 1 < C
  CB_lt_one : C*B < 1
  Bsq_lt_Cv : B^2 < C*v
  Cv_lt_one : C*v < 1
  gap_pos : 0 < nu*B^2-1-(nu-1)*v

set_option maxHeartbeats 1000000 in
/-- The explicit formulas are rational for every rational nu > 3. -/
def explicitSeed (nu : ℚ) (hnu : 3 < nu) : SeedData nu := by
  let e : ℚ := (nu-3)/(2*(2*nu-3))
  let s : ℚ := 1-e
  let v : ℚ := s^3
  let D : ℚ := nu*s^2-1-(nu-1)*s^3
  let B : ℚ := s-D/(4*nu*s)
  let C : ℚ := (B^2/v+1/B)/2
  have hnupos : 0 < nu := by linarith
  have hden : 0 < 2*(2*nu-3) := by linarith
  have hepos : 0 < e := div_pos (by linarith) hden
  have he1 : e < 1 := (div_lt_iff₀ hden).mpr (by linarith)
  have hebalance : e*(2*(2*nu-3)) = nu-3 := div_mul_cancel₀ _ hden.ne'
  have hspos : 0 < s := by dsimp [s]; linarith
  have hs1 : s < 1 := by dsimp [s]; linarith
  have hinner : (nu-1)*s^2-s-1 = (nu-3)/2+(nu-1)*e^2 := by
    dsimp [s]
    nlinarith [hebalance]
  have hinnerpos : 0 < (nu-1)*s^2-s-1 := by
    rw [hinner]
    have hnm : 0 < nu-1 := by linarith
    positivity
  have hDfactor : D = (1-s)*((nu-1)*s^2-s-1) := by dsimp [D]; ring
  have hDpos : 0 < D := by rw [hDfactor]; exact mul_pos (by linarith) hinnerpos
  have hDlt : D < nu*s^2 := by
    dsimp [D]
    have hnm : 0 < nu-1 := by linarith
    have hp := mul_pos hnm (pow_pos hspos 3)
    linarith
  have hfour : 0 < 4*nu*s := by positivity
  have hBpos : 0 < B := by
    have hdiv : D/(4*nu*s) < s := (div_lt_iff₀ hfour).mpr
      (by nlinarith [mul_pos hnupos (sq_pos_of_pos hspos)])
    dsimp [B]
    linarith
  have hBs : B < s := by
    have hp := div_pos hDpos hfour
    dsimp [B]
    linarith
  have hB1 : B < 1 := hBs.trans hs1
  have hvpos : 0 < v := pow_pos hspos 3
  have hv1 : v < 1 := pow_lt_one₀ hspos.le hs1 (by decide)
  have hgapid : nu*B^2-1-(nu-1)*v = D/2+D^2/(16*nu*s^2) := by
    calc
      _ = (nu*B^2-nu*s^2)+D := by dsimp [v, D]; ring
      _ = _ := by
        dsimp [B]
        field_simp
        ring
  have hgap : 0 < nu*B^2-1-(nu-1)*v := by rw [hgapid]; positivity
  have hvBsq : v < B^2 := by
    nlinarith
  have hBcub : B^3 < v := pow_lt_pow_left₀ hBs hBpos.le (by decide)
  have hinterval : B^2/v < 1/B := by
    apply (div_lt_div_iff₀ hvpos hBpos).mpr
    nlinarith
  have hClo : B^2/v < C := by dsimp [C]; linarith
  have hChi : C < 1/B := by dsimp [C]; linarith
  have hC1 : 1 < C := ((lt_div_iff₀ hvpos).mpr (by simpa using hvBsq)).trans hClo
  have hCpos : 0 < C := zero_lt_one.trans hC1
  have hCB : C*B < 1 := (lt_div_iff₀ hBpos).mp hChi
  have hBsqCv : B^2 < C*v := (div_lt_iff₀ hvpos).mp hClo
  have hCv : C*v < 1 := by
    have h1 := mul_lt_mul_of_pos_left hvBsq hCpos
    have h2 := mul_lt_mul_of_pos_right hCB hBpos
    nlinarith
  exact ⟨v, B, C, hvpos, hv1, hBpos, hB1, hC1, hCB, hBsqCv, hCv, hgap⟩

theorem exists_seed (nu : ℚ) (hnu : 3 < nu) : Nonempty (SeedData nu) :=
  ⟨explicitSeed nu hnu⟩

namespace SeedData

variable {nu : ℚ} (P : SeedData nu)

def gap : ℝ := (nu : ℝ)*(P.B : ℝ)^2-1-((nu : ℝ)-1)*(P.v : ℝ)

theorem gap_pos_real : 0 < P.gap := by
  unfold gap
  exact_mod_cast P.gap_pos

theorem v_pos_real : (0 : ℝ) < P.v := by exact_mod_cast P.v_pos
theorem B_pos_real : (0 : ℝ) < P.B := by exact_mod_cast P.B_pos
theorem C_pos_real : (0 : ℝ) < P.C := by exact_mod_cast (zero_lt_one.trans P.C_gt_one)

theorem smallBase_pos : (0 : ℝ) < (P.C : ℝ)*P.B := mul_pos P.C_pos_real P.B_pos_real
theorem smallBase_lt_one : (P.C : ℝ)*P.B < 1 := by exact_mod_cast P.CB_lt_one
theorem growthBase_gt_one : (1 : ℝ) < (P.C : ℝ)*P.v/(P.B : ℝ)^2 := by
  apply (lt_div_iff₀ (sq_pos_of_pos P.B_pos_real)).mpr
  rw [one_mul]
  exact_mod_cast P.Bsq_lt_Cv
theorem contactBase_pos : (0 : ℝ) < (P.C : ℝ)*P.v := mul_pos P.C_pos_real P.v_pos_real
theorem contactBase_lt_one : (P.C : ℝ)*P.v < 1 := by exact_mod_cast P.Cv_lt_one

end SeedData

#print axioms exists_seed

end LogarithmExtension.LogRatio.ParameterSeeds

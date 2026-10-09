import LogarithmExtension.LogRatioScalingAudit

/-!
# Even an optimistic simplex-average correction does not reach 19/8

The original high-index comparison charges 1-v. This audit allows the
smaller cost m/(m+3) * (1-v), suggested by full-simplex average degrees,
without asserting that an arbitrary interpolation minor enjoys that cost.

Under this optimistic comparison, the line-aligned indicator still obeys
L <= (2/3) * (K/w0 + 1/v0). Thus this proposed correction alone cannot pay
even the two unit-coefficient error charges if the collision coefficient
is at most one. This is a restricted ledger obstruction, not a lower bound
on the irrationality exponent.
-/

namespace LogarithmExtension.LogRatio.AverageAudit

noncomputable def averageA (m : ℕ) : ℝ := 8 * (m : ℝ) / (19 * ((m : ℝ) + 3))

theorem averageA_pos_lt_one (m : ℕ) (hm : 0 < m) :
    0 < averageA m ∧ averageA m < 1 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hden : 0 < 19 * ((m : ℝ) + 3) := by positivity
  constructor
  · exact div_pos (by positivity) hden
  · apply (div_lt_one hden).mpr
    nlinarith

theorem cubic_ratio_bound (a v A : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hv : 0 ≤ v) (hA : 0 < A) (hlinear : a + (1-a)*v ≤ A) :
    v^2 / A^3 ≤ 4 / (27*a*(1-a)^2) := by
  have hden : 0 < 27*a*(1-a)^2 := by positivity
  have hfactor : 0 ≤ (2*a - (1-a)*v)^2 * (a + 4*(1-a)*v) := by positivity
  have hcube : (a + (1-a)*v)^3 ≤ A^3 := by gcongr
  apply (div_le_div_iff₀ (by positivity : 0 < A^3) hden).mpr
  nlinarith [hfactor, hcube]

theorem small_dimension_factor (m : ℕ) (hm : 0 < m) (hm11 : m ≤ 11) :
    (4 / (27 * averageA m * (1 - averageA m)^2))^m ≤ 2 := by
  interval_cases m <;> norm_num [averageA]

theorem averaged_gain_shape_bound (m : ℕ) (hm : 0 < m) (A v : ℝ)
    (hA : 0 < A) (hv : 0 ≤ v) (hv1 : v < 1)
    (hgain : ((m : ℝ) / ((m : ℝ)+3)) * (1-v) < (19/8 : ℝ) * (A-v)) :
    (v^2 / A^3)^m ≤ 2 := by
  obtain ⟨ha, ha1⟩ := averageA_pos_lt_one m hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hid : ((m : ℝ) / ((m : ℝ)+3)) * (1-v) =
      (19/8 : ℝ) * (averageA m + (1-averageA m)*v - v) := by
    unfold averageA
    field_simp
    ring
  have hlinear : averageA m + (1-averageA m)*v < A := by
    rw [hid] at hgain
    nlinarith
  by_cases hm11 : m ≤ 11
  · exact (pow_le_pow_left₀ (by positivity)
      (cubic_ratio_bound _ v A ha ha1 hv hA hlinear.le) m).trans
      (small_dimension_factor m hm hm11)
  · have hm12 : (12 : ℝ) ≤ m := by exact_mod_cast (show 12 ≤ m by omega)
    have ha3 : (1/3 : ℝ) ≤ averageA m := by
      apply (le_div_iff₀ (by positivity : 0 < 19*((m : ℝ)+3))).mpr
      nlinarith
    have hlin3 : 1 + 2*v < 3*A := by
      nlinarith [mul_nonneg (show 0 ≤ 3*averageA m-1 by linarith) (sub_nonneg.mpr hv1.le)]
    have hshape := ScalingAudit.high_index_gain_forces_shape 3 A v
      (by norm_num) le_rfl hA hv hv1 (by linarith)
    have hratio : v^2 / A^3 ≤ 1 := (div_le_one (by positivity)).mpr hshape.le
    exact (pow_le_one₀ (by positivity) hratio).trans (by norm_num)

theorem averaged_line_bound (m : ℕ) (hm : 0 < m) (K v v0 w0 A : ℝ)
    (hK : 0 ≤ K) (hv : 0 ≤ v) (hv1 : v < 1)
    (hv0 : 0 < v0) (hw0 : 0 < w0) (hA : 0 < A)
    (hvolume : K * (w0/v0)^2 * v^m ≤ 1)
    (hgain : ((m : ℝ) / ((m : ℝ)+3)) * (1-v) < (19/8 : ℝ) * (A-v)) :
    K * v^m / (v0 * A^m) ≤ (2/3 : ℝ) * (K/w0 + 1/v0) := by
  have hshape := averaged_gain_shape_bound m hm A v hA hv hv1 hgain
  let x := K/w0
  let y := 1/v0
  have hx : 0 ≤ x := by positivity
  have hy : 0 ≤ y := by positivity
  have hbase : 0 ≤ x^2*y := by positivity
  have hvol0 : 0 ≤ K * (w0/v0)^2 * v^m := by positivity
  have hc : (K * v^m / (v0 * A^m))^3 ≤ 2*x^2*y := by
    rw [ScalingAudit.line_aligned_identity m K v v0 w0 A hv0.ne' hw0.ne' hA.ne']
    calc
      _ ≤ x^2*y * (K*(w0/v0)^2*v^m) * 2 :=
        mul_le_mul_of_nonneg_left hshape (mul_nonneg hbase hvol0)
      _ ≤ x^2*y * 1 * 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hvolume hbase) (by norm_num)
      _ = _ := by ring
  have hfactor : 0 ≤ (x-2*y)^2 * (4*x+y) := by positivity
  have hc' : (K * v^m / (v0 * A^m))^3 ≤ ((2/3 : ℝ) * (x+y))^3 := by
    nlinarith [hc, hfactor]
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : 3 ≠ 0)).mp hc'

theorem no_averaged_line_ledger (m : ℕ) (hm : 0 < m) (K v v0 w0 A : ℝ)
    (hK : 0 ≤ K) (hv : 0 ≤ v) (hv1 : v < 1)
    (hv0 : 0 < v0) (hw0 : 0 < w0) (hA : 0 < A)
    (hvolume : K * (w0/v0)^2 * v^m ≤ 1)
    (hgain : ((m : ℝ) / ((m : ℝ)+3)) * (1-v) < (19/8 : ℝ) * (A-v))
    (collisionCoefficient error : ℝ) (hc : collisionCoefficient ≤ 1)
    (he : K/w0 + 1/v0 ≤ error) :
    ¬ 1 + error < collisionCoefficient * (K * v^m / (v0 * A^m)) := by
  have hL := averaged_line_bound m hm K v v0 w0 A hK hv hv1 hv0 hw0 hA hvolume hgain
  have hL0 : 0 ≤ K * v^m / (v0 * A^m) := by positivity
  have hsum0 : 0 ≤ K/w0 + 1/v0 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hc hL0
  simp only [one_mul] at hmul
  intro h
  linarith

#print axioms averaged_line_bound
#print axioms no_averaged_line_ledger

end LogarithmExtension.LogRatio.AverageAudit

import Mathlib

/-!
# Audit of a line-aligned collision improvement

The centers (j log 2, j log 3) lie on one line. An optimistic replacement of
the generic two-variable collision saving leads to the size indicator
L = K v^m / (v0 A^m). The algebra below shows that this stronger indicator
still cannot grow while both error ratios shrink and the volume condition
holds in the parameter range needed for an exponent at most three.

This is an obstruction to this particular estimate/scaling, not a lower
bound for the irrationality exponent, nor a no-go theorem for other methods.
-/

namespace LogarithmExtension.LogRatio.ScalingAudit

theorem line_aligned_identity (m : ℕ) (K v v0 w0 A : ℝ)
    (hv0 : v0 ≠ 0) (hw0 : w0 ≠ 0) (hA : A ≠ 0) :
    (K * v^m / (v0 * A^m))^3 =
      (K / w0)^2 * (1 / v0) * (K * (w0 / v0)^2 * v^m) * (v^2 / A^3)^m := by
  simp only [div_pow, mul_pow, ← pow_mul]
  field_simp
  ring

theorem line_aligned_bound (m : ℕ) (K v v0 w0 A : ℝ)
    (hK : 0 ≤ K) (hv : 0 ≤ v) (hv0 : 0 < v0) (hw0 : 0 < w0) (hA : 0 < A)
    (hvolume : K * (w0 / v0)^2 * v^m ≤ 1) (hshape : v^2 ≤ A^3) :
    (K * v^m / (v0 * A^m))^3 ≤ (K / w0)^2 * (1 / v0) := by
  rw [line_aligned_identity m K v v0 w0 A (ne_of_gt hv0) (ne_of_gt hw0) (ne_of_gt hA)]
  have hp : 0 ≤ (K / w0)^2 * (1 / v0) := by positivity
  have hvolume0 : 0 ≤ K * (w0 / v0)^2 * v^m := by positivity
  have hratio : (v^2 / A^3)^m ≤ 1 :=
    pow_le_one₀ (by positivity) ((div_le_one (by positivity)).mpr hshape)
  calc
    _ ≤ (K / w0)^2 * (1 / v0) * (K * (w0 / v0)^2 * v^m) * 1 :=
      mul_le_mul_of_nonneg_left hratio (mul_nonneg hp hvolume0)
    _ ≤ (K / w0)^2 * (1 / v0) := by
      simpa using mul_le_mul_of_nonneg_left hvolume hp

theorem high_index_gain_forces_shape (nu A v : ℝ)
    (hnu : 0 < nu) (hnu3 : nu ≤ 3) (_hA : 0 < A) (hv : 0 ≤ v) (hv1 : v < 1)
    (hgain : 1 - v < nu * (A - v)) : v^2 < A^3 := by
  have hAv : 0 < A - v := by nlinarith
  have hcompare := mul_le_mul_of_nonneg_right hnu3 hAv.le
  have hlinear : 1 + 2 * v < 3 * A := by nlinarith
  have hcube : (1 + 2 * v)^3 < (3 * A)^3 := by gcongr
  have hfactor : 0 ≤ (1 - v)^2 * (8 * v + 1) := by positivity
  nlinarith [hcube, hfactor]

#print axioms line_aligned_bound
#print axioms high_index_gain_forces_shape

end LogarithmExtension.LogRatio.ScalingAudit

import LogarithmExtension.LogRatioDeterminantAnalytic
import LogarithmExtension.LogRatioPackingAsymptotics

/-!
# Comparing the arithmetic and analytic bounds for the same determinant

All factorial, translation-count and geometric-series overheads disappear
after normalization. For fixed explicit geometric data and exceptional
fractions, the actual nonzero minors imply a numerical necessary inequality.
Constructing data that violate it for every nu > 3 remains a separate step.
-/

noncomputable section
namespace LogarithmExtension.LogRatio.DeterminantComparison

open OAI OAI.PiExponent BoundedJetMatrix CommonTaylor DeterminantAnalytic TaylorPacking Filter
open LogarithmExtension.LogRatio.AnalyticTranslation
open scoped BigOperators Topology

theorem tendsto_log_floor_add_div (v : ℝ) (hv : 0 < v) :
    Tendsto (fun H : ℝ => Real.log ((⌊H/v⌋₊+1 : ℕ) : ℝ)/H) atTop (𝓝 0) := by
  have hf : Tendsto (fun H : ℝ => (H/v+1)/H^1) atTop (𝓝 (1/v)) := by
    have h := (tendsto_const_nhds (x := 1/v)).add (tendsto_id.const_div_atTop (1 : ℝ))
    simp only [add_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
    simp only [pow_one, id_eq]
    field_simp
  have hl := tendsto_log_div_of_normalized_pow hf (one_div_pos.mpr hv)
  apply squeeze_zero' _ _ hl
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
    apply div_nonneg _ hH.le
    apply Real.log_nonneg
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le ⌊H/v⌋₊)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
    apply div_le_div_of_nonneg_right _ hH.le
    apply Real.log_le_log (by positivity)
    have hfloor := Nat.floor_le (div_nonneg hH.le hv.le)
    push_cast
    linarith

def realRowOverhead (d : GeometryData) (H : ℝ) : ℝ :=
  ((⌊H⌋₊+1 : ℕ) : ℝ)^(2*d.m) *
    ((⌊H/(d.curveJetWeights 0 : ℝ)⌋₊+1 : ℕ) : ℝ)^2

theorem rowOverhead_eq_real (d : GeometryData) (H : ℚ) :
    rowOverhead d H = realRowOverhead d H := by
  unfold rowOverhead choiceOverhead scalarOverhead realRowOverhead
  rw [show 2*d.m = d.m+d.m by omega, pow_add]
  ring

theorem log_realRowOverhead (d : GeometryData) (H : ℝ) :
    Real.log (realRowOverhead d H) =
      ((2*d.m : ℕ) : ℝ)*Real.log ((⌊H⌋₊+1 : ℕ) : ℝ) +
        2*Real.log ((⌊H/(d.curveJetWeights 0 : ℝ)⌋₊+1 : ℕ) : ℝ) := by
  rw [realRowOverhead, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  norm_num

theorem tendsto_log_realRowOverhead_div (d : GeometryData) :
    Tendsto (fun H : ℝ => Real.log (realRowOverhead d H)/H) atTop (𝓝 0) := by
  have h0 := (tendsto_log_floor_add_div 1 (by norm_num)).const_mul ((2*d.m : ℕ) : ℝ)
  have hv := (tendsto_log_floor_add_div (d.curveJetWeights 0)
    (by exact_mod_cast d.curveJetWeights_pos 0)).const_mul 2
  have h := h0.add hv
  simp only [mul_zero, add_zero, div_one] at h
  simpa only [log_realRowOverhead, add_div, mul_div_assoc] using h

def realAnalyticRemainder (d : GeometryData) (H : ℝ) : ℝ :=
  (Real.log (realRowCount d H) + Real.log (realRowOverhead d H) -
    2*Real.log (1-quarterRatio))/H

theorem analyticRemainder_eq_real (d : GeometryData) (H : ℚ) :
    analyticRemainder d H = realAnalyticRemainder d H := by
  rw [analyticRemainder, card_Row_eq, rowOverhead_eq_real]
  rfl

theorem tendsto_realAnalyticRemainder (d : GeometryData) (hK : 0 < d.K) :
    Tendsto (realAnalyticRemainder d) atTop (𝓝 0) := by
  have hm := tendsto_log_div_of_normalized_pow (tendsto_realRowCount d) (rowDensity_pos d hK)
  have hq := tendsto_log_realRowOverhead_div d
  have hc := tendsto_id.const_div_atTop (2*Real.log (1-quarterRatio))
  unfold realAnalyticRemainder
  simpa only [sub_div, add_div, add_zero, sub_zero, id_eq] using
    (hm.add hq).sub hc

def packingLimit (d : GeometryData) (nu : ℚ) (lambda : ℝ) : ℝ :=
  (16*lambda^(d.m+3)/((d.m+3).factorial * (nu : ℝ)^d.m *
    ∏ i : Fin d.m, (d.curveDegreeWeights i.succ.succ : ℝ)))/rowDensity d

theorem tendsto_actual_packing_count (d : GeometryData) (nu : ℚ) (lambda : ℝ)
    (hK : 0 < d.K) (hnu : 0 < nu) (hlambda : 0 < lambda)
    (hW : ∀ i, (d.curveDegreeWeights i.succ.succ : ℝ) = MatrixArithmetic.logWeights d.q i) :
    Tendsto (fun H : ℝ => (augmentedCount (combinedWeights (MatrixArithmetic.logWeights d.q) nu)
      (lambda*H) : ℝ)/((realRowCount d H : ℝ)*H)) atTop (𝓝 (packingLimit d nu lambda)) := by
  have h := tendsto_combinedCount_per_row_degree d hK
    (fun i => d.curveDegreeWeights i.succ.succ) nu
    (fun i => d.curveDegreeWeights_pos i.succ.succ) hnu lambda hlambda
  simpa only [hW, packingLimit] using h

theorem finite_necessary_inequality (d : GeometryData) (H : ℚ) (nu lambda F v ws : ℝ)
    (hK : 0 < d.K) (hH : 0 < H) (hnu : 1 ≤ nu) (hF : 0 < F) (hv : 0 < v) (hws : 0 < ws)
    (hwmin : ∀ i, ws ≤ MatrixArithmetic.logWeights d.q i)
    (hW : ∀ i, (d.curveDegreeWeights i.succ.succ : ℝ) = MatrixArithmetic.logWeights d.q i)
    (hV : ∀ i, (d.curveJetWeights i.succ.succ : ℝ) = MatrixArithmetic.logWeights d.q i/v)
    (hr : ∀ i, ‖d.slopes i‖ ≤ 2)
    (happrox : ∀ i, |ratioTheta-(d.p i : ℝ)/d.q i| ≤ (d.q i : ℝ)^(-nu))
    (selection : Row d H → Column d H)
    (hne : (MatrixArithmetic.selectedMinor d
      (MatrixArithmetic.truncationOrders d.q F (d.curveJetWeights 0)) H selection).det ≠ 0) :
    lambda-1-(nu-1)*v ≤
      (augmentedCount (combinedWeights (MatrixArithmetic.logWeights d.q) nu) (lambda*(H : ℝ)) : ℝ)/
        ((realRowCount d H : ℝ)*(H : ℝ)) + ArithmeticBound.arithmeticError d F v ws +
          translationError d nu F ws + CommonTaylor.holomorphicError d ws + realAnalyticRemainder d H := by
  have hl := ArithmeticBound.normalized_determinant_lower_bound d H F v ws hK hH hF.le hv hws
    hwmin hW hV selection hne
  have hu := normalized_determinant_upper_bound d H nu lambda F ws hK hH
    (lt_of_lt_of_le zero_lt_one hnu) hF hws hwmin hW hr happrox selection hne
  have havg := meanRowWeight_le d H v hK hH hv hV
  have hcredit := mul_le_mul_of_nonneg_left havg (sub_nonneg.mpr hnu)
  rw [card_Row_eq, analyticRemainder_eq_real] at hu
  rw [card_Row_eq] at hl
  linarith

/-- A numerical constraint forced by actual interpolation and both bounds.
No interpolation, nonvanishing, analytic-series or determinant estimate is
an additional hypothesis of this endpoint. -/
theorem fixed_data_necessary_inequality (d : GeometryData) (nu : ℚ) (lambda F v ws : ℝ)
    (hK : 0 < d.K) (hnu : 1 ≤ nu) (hlambda : 0 < lambda)
    (hv : 0 < v) (hF : 1/v ≤ F) (hws : 0 < ws)
    (hwmin : ∀ i, ws ≤ MatrixArithmetic.logWeights d.q i)
    (hW : ∀ i, (d.curveDegreeWeights i.succ.succ : ℝ) = MatrixArithmetic.logWeights d.q i)
    (hV : ∀ i, (d.curveJetWeights i.succ.succ : ℝ) = MatrixArithmetic.logWeights d.q i/v)
    (hr : ∀ i, ‖d.slopes i‖ ≤ 2)
    (happrox : ∀ i, |ratioTheta-(d.p i : ℝ)/d.q i| ≤ (d.q i : ℝ)^(-(nu : ℝ))) :
    lambda-1-((nu : ℝ)-1)*v ≤ packingLimit d nu lambda + ArithmeticBound.arithmeticError d F v ws +
      translationError d nu F ws + CommonTaylor.holomorphicError d ws := by
  let R : ℚ := (BlowupGeometry.scale d).radius
  have hR : (0 : ℚ) < R := by
    dsimp only [R]
    exact_mod_cast (BlowupGeometry.scale d).radius_pos
  have hRr : (0 : ℝ) < R := by exact_mod_cast hR
  have hnu0 : 0 < nu := lt_of_lt_of_le zero_lt_one hnu
  have hF0 : 0 < F := (one_div_pos.mpr hv).trans_le hF
  have hdegree : Tendsto (fun n : ℕ => (((n : ℚ)*R : ℚ) : ℝ)) atTop atTop := by
    simpa only [Rat.cast_mul, Rat.cast_natCast] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const hRr
  have hlimit := (((tendsto_actual_packing_count d nu lambda hK hnu0 hlambda hW).add_const
    (ArithmeticBound.arithmeticError d F v ws)).add_const (translationError d nu F ws)).add_const
    (CommonTaylor.holomorphicError d ws)
  have hlimit' := (hlimit.add (tendsto_realAnalyticRemainder d hK)).comp hdegree
  simp only [add_zero] at hlimit'
  apply ge_of_tendsto hlimit'
  filter_upwards [ArithmeticBound.eventually_nonzero_minor_with_lower_bound d F v ws
    hK hv hF hws hwmin hW hV, eventually_ge_atTop (1 : ℕ)] with n hn hn1
  obtain ⟨selection, _, hne, _⟩ := hn
  have hH : (0 : ℚ) < (n : ℚ)*R := mul_pos (by exact_mod_cast (Nat.zero_lt_one.trans_le hn1)) hR
  exact finite_necessary_inequality d ((n : ℚ)*R) nu lambda F v ws hK hH
    (by exact_mod_cast hnu) hF0 hv hws hwmin hW hV hr happrox selection hne

#print axioms tendsto_realAnalyticRemainder
#print axioms fixed_data_necessary_inequality

end LogarithmExtension.LogRatio.DeterminantComparison

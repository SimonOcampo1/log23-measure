import LogarithmExtension.LogRatioTaylorPacking
import LogarithmExtension.LogRatioArithmeticBound

/-!
# Counting limits for direct Taylor packing and a coarse row-credit bound

The only new counting input is an ordinary rational weighted simplex with
one additional coordinate. The mean auxiliary row weight need not have an
asymptotic formula: its already available upper bound by v suffices.
-/

noncomputable section
namespace LogarithmExtension.LogRatio.TaylorPacking

open OAI OAI.PiExponent BoundedJetMatrix Filter
open scoped BigOperators Topology

theorem normalized_limit_dilate (f : ℝ → ℝ) (d : ℕ) (A lambda : ℝ)
    (hf : Tendsto (fun H => f H/H^d) atTop (𝓝 A)) (hlambda : 0 < lambda) :
    Tendsto (fun H => f (lambda*H)/H^d) atTop (𝓝 (A*lambda^d)) := by
  have hd := (hf.comp (Tendsto.const_mul_atTop hlambda tendsto_id)).mul_const (lambda^d)
  apply hd.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
  change (f (lambda*H)/(lambda*H)^d)*lambda^d = f (lambda*H)/H^d
  rw [mul_pow]
  field_simp

theorem tendsto_augmentedCount_rational {d : ℕ} (w : Fin d → ℚ) (hw : ∀ i, 0 < w i) :
    Tendsto (fun H : ℝ => (augmentedCount (fun i => (w i : ℝ)) H : ℝ)/H^(d+1))
      atTop (𝓝 (1/((d+1).factorial * ∏ i, (w i : ℝ)))) := by
  have hp (i : Fin (d+1)) : (0 : ℚ) < Fin.cases 1 w i := by
    cases i using Fin.cases with
    | zero => norm_num
    | succ i => exact hw i
  have he : (fun i : Fin (d+1) => ((Fin.cases (1 : ℚ) w i : ℚ) : ℝ)) =
      Fin.cases 1 (fun i => (w i : ℝ)) := by
    funext i
    cases i using Fin.cases <;> simp
  have h := tendsto_card_realWeightedSimplex_rational (Fin.cases 1 w) hp
  rw [he] at h
  simpa only [augmentedCount, Fin.prod_univ_succ, Fin.cases_zero, Fin.cases_succ, one_mul] using h

theorem tendsto_augmentedCount_dilate {d : ℕ} (w : Fin d → ℚ) (hw : ∀ i, 0 < w i)
    (lambda : ℝ) (hlambda : 0 < lambda) :
    Tendsto (fun H : ℝ => (augmentedCount (fun i => (w i : ℝ)) (lambda*H) : ℝ)/H^(d+1))
      atTop (𝓝 (lambda^(d+1)/((d+1).factorial * ∏ i, (w i : ℝ)))) := by
  simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using
    normalized_limit_dilate (fun H => (augmentedCount (fun i => (w i : ℝ)) H : ℝ))
      (d+1) _ lambda (tendsto_augmentedCount_rational w hw) hlambda

theorem tendsto_combinedCount {m : ℕ} (w : Fin m → ℚ) (nu : ℚ)
    (hw : ∀ i, 0 < w i) (hnu : 0 < nu) (lambda : ℝ) (hlambda : 0 < lambda) :
    Tendsto (fun H : ℝ =>
      (augmentedCount (combinedWeights (fun i => (w i : ℝ)) nu) (lambda*H) : ℝ)/H^(m+3))
      atTop (𝓝 (16*lambda^(m+3)/((m+3).factorial * (nu : ℝ)^m * ∏ i, (w i : ℝ)))) := by
  let rho : Fin (m+2) → ℚ := Fin.cases (1/4) (Fin.cases (1/4) (fun i => nu*w i))
  have hrho (i : Fin (m+2)) : 0 < rho i := by
    cases i using Fin.cases with
    | zero => norm_num [rho]
    | succ i =>
      cases i using Fin.cases with
      | zero => change (0 : ℚ) < 1/4; norm_num
      | succ i => exact mul_pos hnu (hw i)
  have he : (fun i => (rho i : ℝ)) = combinedWeights (fun i => (w i : ℝ)) nu := by
    funext i
    cases i using Fin.cases with
    | zero => norm_num [rho, combinedWeights]
    | succ i =>
      cases i using Fin.cases with
      | zero => change ((1/4 : ℚ) : ℝ) = 1/4; norm_num
      | succ i => exact Rat.cast_mul _ _
  have hp : (∏ i, (rho i : ℝ)) = (nu : ℝ)^m * (∏ i, (w i : ℝ))/16 := by
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    simp only [rho, Fin.cases_zero, Fin.cases_succ, Rat.cast_mul, Rat.cast_div,
      Rat.cast_one, Rat.cast_ofNat, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    ring
  have h := tendsto_augmentedCount_dilate rho hrho lambda hlambda
  rw [hp, he] at h
  convert h using 1
  congr 1
  field_simp

def realRowCount (d : GeometryData) (H : ℝ) : ℕ :=
  d.K * (strictWeightedSimplex (fun i => (d.curveJetWeights i : ℝ)) H).card

theorem card_Row_eq (d : GeometryData) (H : ℚ) :
    Fintype.card (Row d H) = realRowCount d H := by
  simp [Row, realRowCount]

def rowDensity (d : GeometryData) : ℝ :=
  d.K/((d.m+2).factorial * ∏ i, (d.curveJetWeights i : ℝ))

theorem rowDensity_pos (d : GeometryData) (hK : 0 < d.K) : 0 < rowDensity d := by
  apply div_pos (by exact_mod_cast hK)
  exact mul_pos (by exact_mod_cast Nat.factorial_pos (d.m+2))
    (Finset.prod_pos (fun i _ => by exact_mod_cast d.curveJetWeights_pos i))

theorem tendsto_realRowCount (d : GeometryData) :
    Tendsto (fun H : ℝ => (realRowCount d H : ℝ)/H^(d.m+2)) atTop (𝓝 (rowDensity d)) := by
  have h := (tendsto_card_strictWeightedSimplex_rational d.curveJetWeights
    d.curveJetWeights_pos).const_mul (d.K : ℝ)
  simpa only [realRowCount, rowDensity, Nat.cast_mul, div_eq_mul_inv, mul_assoc, one_mul] using h

theorem tendsto_combinedCount_per_row_degree (d : GeometryData) (hK : 0 < d.K)
    (w : Fin d.m → ℚ) (nu : ℚ) (hw : ∀ i, 0 < w i) (hnu : 0 < nu)
    (lambda : ℝ) (hlambda : 0 < lambda) :
    Tendsto (fun H : ℝ =>
      (augmentedCount (combinedWeights (fun i => (w i : ℝ)) nu) (lambda*H) : ℝ)/
        ((realRowCount d H : ℝ)*H)) atTop
      (𝓝 ((16*lambda^(d.m+3)/((d.m+3).factorial * (nu : ℝ)^d.m *
        ∏ i, (w i : ℝ)))/rowDensity d)) := by
  have h := (tendsto_combinedCount w nu hw hnu lambda hlambda).div
    (tendsto_realRowCount d) (rowDensity_pos d hK).ne'
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
  have hH0 := hH.ne'
  dsimp only [Pi.div_apply]
  by_cases hM : (realRowCount d H : ℝ) = 0
  · simp [hM]
  simp only [show d.m+3 = (d.m+2)+1 by omega, pow_succ]
  field_simp

/-- A uniform upper bound on the mean row weight suffices for the final
positive gap; its precise simplex average is not needed. -/
theorem meanRowWeight_le (d : GeometryData) (H : ℚ) (v : ℝ)
    (hK : 0 < d.K) (hH : 0 < H) (hv : 0 < v)
    (hV : ∀ i, (d.curveJetWeights i.succ.succ : ℝ) = MatrixArithmetic.logWeights d.q i/v) :
    ArithmeticBound.meanRowWeight d H ≤ v := by
  have hM : (0 : ℝ) < Fintype.card (Row d H) := by
    exact_mod_cast ArithmeticBound.row_card_pos d H hK hH
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  apply (div_le_iff₀ (mul_pos hM hHr)).mpr
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun row _ => ArithmeticBound.row_weight_le d H v hv hV row)
  simpa only [ArithmeticBound.rowWeightedSum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_comm v, mul_assoc] using hsum

#print axioms tendsto_combinedCount_per_row_degree
#print axioms meanRowWeight_le

end LogarithmExtension.LogRatio.TaylorPacking

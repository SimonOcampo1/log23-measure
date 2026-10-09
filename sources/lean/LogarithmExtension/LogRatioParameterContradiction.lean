import LogarithmExtension.LogRatioPackingCancellation
import OAI.NumberTheory.PiExponent.Approximation.WeightErrorMargin

/-!
# Closing the determinant contradiction once the fractions are selected

This endpoint makes the remaining task precise: construct explicit geometric
data from an unbounded exceptional sequence, with sufficiently large separated
auxiliary weights. The determinant and parameter comparisons are supplied here.
-/

noncomputable section
namespace LogarithmExtension.LogRatio.ParameterContradiction

open OAI.PiExponent ParameterSeeds ParameterDimension ParameterChoice
open PackingCancellation DeterminantComparison CommonTaylor
open LogarithmExtension.LogRatio.AnalyticTranslation
open scoped BigOperators

def weightError (d : GeometryData) (nu v ws : ℝ) : ℝ :=
  (4+Real.log 4)*(∑ i, 1/MatrixArithmetic.logWeights d.q i) +
    (v+nu+Real.log 12+Real.log (600*d.K))/ws

theorem error_decomposition (d : GeometryData) (nu F v ws : ℝ) :
    ArithmeticBound.arithmeticError d F v ws + translationError d nu F ws +
      CommonTaylor.holomorphicError d ws = nu/F +
      (((4+Real.log 4)*F*(d.m : ℝ)+2*Real.log 2)/(d.curveJetWeights 0 : ℝ) +
        100*(d.K : ℝ)/(d.curveDegreeWeights 0 : ℝ)) + weightError d nu v ws := by
  unfold ArithmeticBound.arithmeticError translationError CommonTaylor.holomorphicError coefficientError
    Arithmetic.lcmConstant weightError
  ring

variable {nu : ℚ} (P : SeedData nu) (A : Choice P)

theorem exists_auxiliary_threshold (hnu : 3 < nu) :
    ∃ ws : ℝ, 0 < ws ∧ ∀ w : Fin (2*A.n) → ℝ, (∀ i, ws ≤ w i) →
      (4+Real.log 4)*(∑ i, 1/w i) +
        ((P.v : ℝ)+(nu : ℝ)+Real.log 12+Real.log (600*(K P A.n : ℝ)))/ws < P.gap/8 := by
  have hKr : (1 : ℝ) ≤ K P A.n := by exact_mod_cast K_pos P A.n
  have hS : 0 ≤ (P.v : ℝ)+(nu : ℝ)+Real.log 12+Real.log (600*(K P A.n : ℝ)) := by
    have hv := P.v_pos_real
    have hn : (0 : ℝ) < nu := by exact_mod_cast (show 0 < nu by linarith)
    have hl := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 12)
    have hk := Real.log_nonneg (show (1 : ℝ) ≤ 600*(K P A.n : ℝ) by linarith)
    linarith
  have hL : (0 : ℝ) < 4+Real.log 4 := by
    have h := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    linarith
  obtain ⟨X, hX, hmargin⟩ := exists_uniform_weight_error_margin (2*A.n) (4+Real.log 4)
    ((P.v : ℝ)+(nu : ℝ)+Real.log 12+Real.log (600*(K P A.n : ℝ)))
    (P.gap/8) hL hS (div_pos P.gap_pos_real (by norm_num))
  refine ⟨X+1, by linarith, ?_⟩
  intro w hw
  exact hmargin (X+1) w (by linarith) hw

/-- Conditional only on the explicit finite geometric/approximation data;
neither a determinant nor a determinant estimate is assumed. -/
theorem no_data_with_small_weight_error (hnu : 3 < nu) (d : GeometryData) (ws : ℝ)
    (hm : d.m = 2*A.n) (hK : d.K = K P A.n)
    (hw0 : d.curveDegreeWeights 0 = w0 P A.n)
    (hv0 : d.curveJetWeights 0 = v0 P A.n)
    (hws : 0 < ws) (hwmin : ∀ i, ws ≤ MatrixArithmetic.logWeights d.q i)
    (hW : ∀ i, (d.curveDegreeWeights i.succ.succ : ℝ) = MatrixArithmetic.logWeights d.q i)
    (hV : ∀ i, (d.curveJetWeights i.succ.succ : ℝ) = MatrixArithmetic.logWeights d.q i/(P.v : ℝ))
    (hr : ∀ i, ‖d.slopes i‖ ≤ 2)
    (happrox : ∀ i, |ratioTheta-(d.p i : ℝ)/d.q i| ≤ (d.q i : ℝ)^(-(nu : ℝ)))
    (hsmall : weightError d nu P.v ws < P.gap/8) : False := by
  have hnu0 : 0 < nu := by linarith
  have hKpos : 0 < d.K := hK ▸ K_pos P A.n
  have hF : 1/(P.v : ℝ) ≤ (A.F : ℝ) := by
    have hv := P.v_pos_real
    have hf := A.F_large
    have h12 : 1/(P.v : ℝ) < 2/(P.v : ℝ) := div_lt_div_of_pos_right (by norm_num) hv
    exact (h12.trans hf).le
  have hV' : ∀ i : Fin d.m, (d.curveJetWeights i.succ.succ : ℝ) =
      (d.curveDegreeWeights i.succ.succ : ℝ)/(P.v : ℝ) := by
    intro i
    rw [hW, hV]
  have hroot : (lambda P A.n)^(d.m+2) = (d.K : ℝ)*((nu : ℝ)*P.v)^d.m/
      (16*(d.curveJetWeights 0 : ℝ)^2) := by
    rw [hv0, hK, hm]
    exact chosen_root_identity P hnu0 A.n
  have hpacking := optimal_packingLimit d nu P.v (lambda P A.n) hKpos hnu0 P.v_pos_real hV' hroot
  have hc := fixed_data_necessary_inequality d nu (lambda P A.n) A.F P.v ws hKpos
    (by linarith) (lambda_pos P A.n) P.v_pos_real hF hws hwmin hW hV hr happrox
  rw [hpacking] at hc
  have herrors := error_decomposition d nu A.F P.v ws
  have hmR : (d.m : ℝ) = 2*(A.n : ℝ) := by exact_mod_cast hm
  rw [hmR, hv0, hw0, hK] at herrors
  have hnet : netMargin P A.n = lambda P A.n-1-((nu : ℝ)-1)*(P.v : ℝ) -
      lambda P A.n/((d.m : ℝ)+3) := by
    rw [hmR, netMargin]
    have hn : 2*(A.n : ℝ)+3 ≠ 0 := by positivity
    field_simp
    ring
  have hgap := P.gap_pos_real
  have hi := A.initial_margin
  have hd := A.dimension_margin
  have hp := A.packing_margin
  linarith

#print axioms exists_auxiliary_threshold
#print axioms no_data_with_small_weight_error

end LogarithmExtension.LogRatio.ParameterContradiction

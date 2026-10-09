import LogarithmExtension.LogRatioCurveModelDegrees

/-! Adapted from the upstream pi geometry wrappers (Apache-2.0).
The inputs here are explicit two-base `GeometryData`. -/

namespace LogarithmExtension.LogRatio
open OAI OAI.PiExponent OAI.PiExponentApprox

noncomputable section
namespace BlowupMargin
open AlgebraicGeometry CategoryTheory TopologicalSpace
open BlowupGeometry CurveNormalizationModel
variable (d : GeometryData)

theorem affineCurveDegreeData (C : NumericalAmpleness.IntegralCurve (blowup d))
    (hn : ¬ ∃ x : compactification d, Set.range (C.embedding ≫ projection d) ⊆ {x})
    (hm : ∃ c : C.scheme, (C.embedding ≫ projection d) c ∈ (affineChart d).opensRange) :
    Nonempty (AffineCurveDegreeData d C) := by
  obtain ⟨r⟩ := CurveModel.existsModelData d C hn hm
  exact ⟨CurveModel.degreeData d C r⟩

end BlowupMargin

namespace BlowupGeometry
open AlgebraicGeometry
variable (d : GeometryData)

theorem uniform_curve_margin :
    ∀ C : NumericalAmpleness.IntegralCurve (blowup d),
      uniformMargin d * (NumericalAmpleness.curveDegree (structureMap d) (H d) C : ℝ) ≤
        (NumericalAmpleness.curveDegree (structureMap d) (interpolationBundle d) C : ℝ) :=
  uniform_curve_margin_of_affine_curve_data d (BlowupMargin.affineCurveDegreeData d)

end BlowupGeometry

end

end LogarithmExtension.LogRatio

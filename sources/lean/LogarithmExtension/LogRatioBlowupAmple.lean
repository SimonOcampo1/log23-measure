import OAI.NumberTheory.PiExponent.Ampleness.NumericalAmplenessTheorem
import LogarithmExtension.LogRatioCurveDegreeData

/-! Adapted from the upstream pi geometry wrappers (Apache-2.0).
The inputs here are explicit two-base `GeometryData`. -/

namespace LogarithmExtension.LogRatio
open OAI OAI.PiExponent OAI.PiExponentApprox

noncomputable section
namespace BlowupGeometry
variable (d : GeometryData)

theorem interpolationBundle_ample : (interpolationBundle d).IsAmple :=
  NumericalAmpleness.isAmple_of_uniform_curve_margin (structureMap d)
    (H d) (interpolationBundle d) (H_ample d) (uniformMargin d)
    (uniformMargin_pos d) (uniform_curve_margin d)

end BlowupGeometry

end

end LogarithmExtension.LogRatio

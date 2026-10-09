import LogarithmExtension.LogRatioBlowupAmple
import OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupJetSurjectivity

/-! Adapted from the upstream pi geometry wrappers (Apache-2.0).
The inputs here are explicit two-base `GeometryData`. -/

namespace LogarithmExtension.LogRatio
open OAI OAI.PiExponent OAI.PiExponentApprox

namespace JetSurjectivity
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open BlowupGeometry PiExponent.BlowupJetSurjectivity
attribute [local irreducible] BlowupGeometry.centerIdeal
  BlowupGeometry.hyperplane
variable (d : GeometryData)

theorem blowupBundle_ample :
    (blowupBundle (centerIdeal d) (hyperplane d)).IsAmple := by
  apply PiExponent.AmpleIso.isAmple_of_sheaf_iso (interpolationBundle d)
    (blowupBundle (centerIdeal d) (hyperplane d))
    (moduleTensorComm (A d).sheaf (J d).sheaf)
  exact interpolationBundle_ample d

end
end JetSurjectivity

end LogarithmExtension.LogRatio

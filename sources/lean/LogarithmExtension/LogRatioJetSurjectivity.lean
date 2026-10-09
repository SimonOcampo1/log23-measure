import LogarithmExtension.LogRatioJetAmpleness
import OAI.NumberTheory.PiExponent.Ampleness.BlowupJetSurjectivityComplete

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

theorem eventual_jetRestriction_surjective :
    ∃ N, ∀ n, N ≤ n → Function.Surjective
      (jetRestriction (centerIdeal d) (hyperplane d) n) := by
  exact eventual_blowup_jetRestriction_surjective
    (compactificationStructureMap d) (centerIdeal d) (hyperplane d) (blowupBundle_ample d)

theorem eventually_jetRestriction_surjective :
    ∀ᶠ n in Filter.atTop, Function.Surjective
      (jetRestriction (centerIdeal d) (hyperplane d) n) := by
  obtain ⟨N,hN⟩ := eventual_jetRestriction_surjective d
  exact Filter.eventually_atTop.mpr ⟨N,hN⟩

end
end JetSurjectivity

end LogarithmExtension.LogRatio

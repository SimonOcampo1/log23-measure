import LogarithmExtension.LogRatioBlowupGeometry
import LogarithmExtension.LogRatioJetPackets
import LogarithmExtension.LogRatioJetSurjectivity

/-! Adapted from the upstream pi geometry wrappers (Apache-2.0).
The inputs here are explicit two-base `GeometryData`. -/

namespace LogarithmExtension.LogRatio
open OAI OAI.PiExponent OAI.PiExponentApprox

noncomputable section
namespace GlobalJetPackets
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open BlowupGeometry
open PiExponent.BlowupJetSurjectivity PiExponent.ExceptionalAffineChart
attribute [local irreducible] BlowupGeometry.affineChart BlowupGeometry.hyperplane
  BlowupGeometry.centerIdeal
  AffineJetCoefficientInterface.Frame AffineJetCoefficientInterface.Sections
  AffineJetCoefficientInterface.coefficient
variable (d : GeometryData)

abbrev affineOpen := chartOpen (affineChart d)

def sectionPolynomial (n : ℕ)
    (e : AffineJetCoefficientInterface.Frame (affineChart d) (hyperplane d)) :
    AffineJetCoefficientInterface.Sections (hyperplane d) n → PolynomialFrame.Poly d.m :=
  AffineJetCoefficientInterface.coefficient (affineChart d) (hyperplane d) n e

theorem formalPackets_surjective_of_jetRestriction (n : ℕ)
    (e : AffineJetCoefficientInterface.Frame (affineChart d) (hyperplane d))
    (hjet : Function.Surjective (jetRestriction (centerIdeal d) (hyperplane d) n)) :
    Function.Surjective (fun s j =>
      JetGeometry.rationalCoefficientPacket d.curveJetWeights (n * (scale d).radius)
        (FormalJet.formalJet (d.centerY j) (d.centerZ j) (d.curveCenters j) d.slopes (sectionPolynomial d n e s))) := by
  have he : ∀ i, (scale d).radius ≤ ((scale d).jetPowers i : ℚ) * d.curveJetWeights i := by
    intro i
    rw [mul_comm, (scale d).jetPowers_eq]
  have hs : (((centerIdeal d)^n).support : Set (compactification d)) ⊆
      (affineChart d).opensRange := by
    cases n with
    | zero => simp
    | succ n => simpa using centerIdeal_support_subset_chart d
  exact JetPackets.surjective_of_jetRestriction d.centerY d.centerZ
    d.centerY_ne_zero d.centerZ_ne_zero d.curveCenters d.slopes d.fullCenters_injective
    (logCutoff d) (scale d).jetPowers (scale d).jetPowers_pos
    d.curveJetWeights d.curveJetWeights_pos (fun i => (logCutoff_strict d i).le)
    (fun i => (logCutoff_strict_second d i).le)
    (scale d).radius he n (affineChart d) (centerIdeal d) (hyperplane d) e
    (centerIdeal_restrict d) hs hjet

end GlobalJetPackets
end

end LogarithmExtension.LogRatio

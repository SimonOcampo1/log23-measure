import LogarithmExtension.LogRatioGlobalJetPackets
import OAI.NumberTheory.PiExponent.Approximation.WeightedGlobalSectionBound
import OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixFrame

/-!
# Bounded-degree interpolation at two-base logarithmic centers

The output is simultaneous interpolation WITH the weighted degree bound.
No surjectivity, ampleness, or nonzero-determinant hypothesis is assumed:
all such geometric inputs are derived from `GeometryData`.

The polynomial-space interface is adapted from the upstream interpolation
wrappers (Apache-2.0), but does not use their pi-specific approximation data.
-/

noncomputable section
namespace LogarithmExtension.LogRatio.WeightedInterpolation

open OAI OAI.PiExponent OAI.PiExponentApprox
open AlgebraicGeometry CategoryTheory Filter
open PiExponentSeshadri.Geometry
open BlowupGeometry GlobalJetPackets
open scoped BigOperators

variable (d : GeometryData)

theorem exponent_budget (j : Index d) :
    Finsupp.weight (fun i => (d.curveDegreeWeights i : ℝ)) (exponents d j) ≤
      (scale d).radius := by
  have hq := (scale d).budget d.curveDegreeWeights_pos j
  have hr : (∑ i, (d.curveDegreeWeights i : ℝ) * (exponents d j i : ℝ)) ≤
      (scale d).radius := by exact_mod_cast hq
  simpa only [Finsupp.weight_eq_sum, nsmul_eq_mul, mul_comm] using hr

theorem eventual_supportBound :
    ProjectiveCoefficientBound.EventualBound (affineChart d) (hyperplane d)
      (fun i => (d.curveDegreeWeights i : ℝ)) (scale d).radius := by
  unfold affineChart hyperplane
  exact WeightedGlobalSectionBound.eventual_supportBound (K := ℂ)
    (exponents d) (constantIndex d)
    ((scale d).exponents_constant d.curveDegreeWeights_pos)
    (coordinateIndex d) ((scale d).exponents_coordinate d.curveDegreeWeights_pos)
    (fun i => (d.curveDegreeWeights i : ℝ)) (scale d).radius (exponent_budget d)

theorem frame_exists :
    Nonempty (AffineJetCoefficientInterface.Frame (affineChart d) (hyperplane d)) :=
  AdmissibleMatrixInterpolation.monomialFrame_exists (R := ℂ)
    (exponents d) (constantIndex d)
    ((scale d).exponents_constant d.curveDegreeWeights_pos)
    (coordinateIndex d) ((scale d).exponents_coordinate d.curveDegreeWeights_pos)

def WeightedPolynomials (n : ℕ) :=
  {P : PolynomialFrame.Poly d.m // WeightedSliceDegree.SupportBound
    (fun i => (d.curveDegreeWeights i : ℝ)) ((n : ℝ) * (scale d).radius) P}

def packetMap (n : ℕ) (P : WeightedPolynomials d n) :=
  fun j : Fin d.K => JetGeometry.rationalCoefficientPacket d.curveJetWeights
    ((n : ℚ) * (scale d).radius)
    (FormalJet.formalJet (d.centerY j) (d.centerZ j) (d.curveCenters j) d.slopes P.val)

theorem packetMap_surjective_of_family {α : Type*} (n : ℕ)
    (P : α → PolynomialFrame.Poly d.m)
    (hdegree : ∀ a, WeightedSliceDegree.SupportBound
      (fun i => (d.curveDegreeWeights i : ℝ)) ((n : ℝ) * (scale d).radius) (P a))
    (hpacket : Function.Surjective (fun a => fun j : Fin d.K =>
      JetGeometry.rationalCoefficientPacket d.curveJetWeights
        ((n : ℚ) * (scale d).radius)
        (FormalJet.formalJet (d.centerY j) (d.centerZ j) (d.curveCenters j) d.slopes (P a)))) :
    Function.Surjective (packetMap d n) := by
  intro packets
  obtain ⟨a, ha⟩ := hpacket packets
  exact ⟨⟨P a, hdegree a⟩, ha⟩

/-- The bounded interpolation step; only the explicit geometric conditions
in `GeometryData` are inputs. -/
theorem eventually_packetMap_surjective :
    ∀ᶠ n : ℕ in atTop, Function.Surjective (packetMap d n) := by
  obtain ⟨N, hN⟩ := eventual_supportBound d
  obtain ⟨frame⟩ := frame_exists d
  filter_upwards [JetSurjectivity.eventually_jetRestriction_surjective d,
    eventually_ge_atTop N] with n hn hnN
  apply packetMap_surjective_of_family d n (sectionPolynomial d n frame)
  · intro s
    exact hN n hnN frame s
  · exact formalPackets_surjective_of_jetRestriction d n frame hn

theorem cofinal_packetMap_surjective (L : ℝ) :
    ∃ n : ℕ, L ≤ (n : ℝ) * (scale d).radius ∧ Function.Surjective (packetMap d n) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_packetMap_surjective d)
  let n := max N (Nat.ceil (L / ((scale d).radius : ℝ)))
  have hR : (0 : ℝ) < (scale d).radius := by exact_mod_cast (scale d).radius_pos
  refine ⟨n, ?_, hN n (le_max_left _ _)⟩
  apply (div_le_iff₀ hR).mp
  exact (Nat.le_ceil _).trans (by exact_mod_cast
    (le_max_right N (Nat.ceil (L / ((scale d).radius : ℝ)))))

#print axioms eventually_packetMap_surjective
#print axioms cofinal_packetMap_surjective

end LogarithmExtension.LogRatio.WeightedInterpolation

import LogarithmExtension.LogRatioBlowupGeometry
import LogarithmExtension.LogRatioGeometryData
import OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin
import OAI.NumberTheory.PiExponent.Geometry.CurveNormalizedDegreeTransfer

/-! Adapted from the upstream pi geometry wrappers (Apache-2.0).
The inputs here are explicit two-base `GeometryData`. -/

namespace LogarithmExtension.LogRatio
open OAI OAI.PiExponent OAI.PiExponentApprox

noncomputable section
namespace BlowupMargin
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry NumericalAmpleness
open BlowupGeometry
open OAI.PiExponent.BlowupCurveMargin
variable (d : GeometryData)

theorem margin_of_actual_contact_degrees
    {B : Scheme.{0}} {E : Type*} [Field E] [Algebra ℂ E] [Algebra.EssFiniteType ℂ E]
    (p : B ⟶ Spec (.of ℂ)) [IsProper p] (A J : LineBundle B)
    (a : ℕ) (ha : 1 < a) (hample : ((A.pow a).tensor J).IsAmple)
    (C : IntegralCurve B) (z : Fin (d.m+2) → E)
    (hgen : IntermediateField.adjoin ℂ (Set.range z) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1) (R : ℚ) (hR : 0 < R)
    (hA : (curveDegree p A C : ℝ) = (R : ℝ) * d.poleDegree z htrdeg)
    (hJ : (curveDegree p J C : ℝ) = -(R : ℝ) * d.contactSum z hgen htrdeg) :
    marginCoefficient a d.sigma * (curveDegree p ((A.pow a).tensor J) C : ℝ) ≤
      (curveDegree p (A.tensor J) C : ℝ) := by
  apply margin_of_nonnegative_degree p A J a ha hample d.sigma d.sigma_pos_real C
  rw [hA, hJ]
  have hR' : (0 : ℝ) ≤ R := by exact_mod_cast hR.le
  have h := mul_le_mul_of_nonneg_left (d.curve_inequality z hgen htrdeg) hR'
  nlinarith

structure AffineCurveDegreeData (C : IntegralCurve (blowup d)) where
  E : Type
  [field : Field E]
  [algebra : Algebra ℂ E]
  [essFiniteType : Algebra.EssFiniteType ℂ E]
  coordinates : Fin (d.m+2) → E
  coordinates_generate : IntermediateField.adjoin ℂ (Set.range coordinates) = ⊤
  trdeg_one : Algebra.trdeg ℂ E = 1
  hyperplane_degree : (curveDegree (structureMap d) (A d) C : ℝ) =
    ((scale d).radius : ℝ) * d.poleDegree coordinates trdeg_one
  exceptional_degree : (curveDegree (structureMap d) (J d) C : ℝ) =
    -((scale d).radius : ℝ) * d.contactSum coordinates coordinates_generate trdeg_one

theorem uniform_margin_of_affine_curve_data
    (a : ℕ) (ha : 1 < a) (hample : (((A d).pow a).tensor (J d)).IsAmple)
    (hdata : ∀ C : IntegralCurve (blowup d),
      (¬ ∃ x : compactification d, Set.range (C.embedding ≫ projection d) ⊆ ({x} : Set _)) →
      (∃ c : C.scheme, (C.embedding ≫ projection d) c ∈ (affineChart d).opensRange) →
      Nonempty (AffineCurveDegreeData d C)) :
    ∀ C : IntegralCurve (blowup d),
      marginCoefficient a d.sigma *
          (curveDegree (structureMap d) (((A d).pow a).tensor (J d)) C : ℝ) ≤
        (curveDegree (structureMap d) ((A d).tensor (J d)) C : ℝ) := by
  classical
  intro C
  by_cases hc : ∃ x : compactification d,
      Set.range (C.embedding ≫ projection d) ⊆ ({x} : Set _)
  · obtain ⟨x,hx⟩ := hc
    exact margin_of_contracted (structureMap d) (projection d) (hyperplane d) (J d)
      a ha hample d.sigma d.sigma_pos_real C x hx
  · by_cases hm : ∃ c : C.scheme,
        (C.embedding ≫ projection d) c ∈ (affineChart d).opensRange
    · obtain ⟨r⟩ := hdata C hc hm
      let := r.field
      let := r.algebra
      let := r.essFiniteType
      exact margin_of_actual_contact_degrees d (structureMap d) (A d) (J d)
        a ha hample C r.coordinates r.coordinates_generate r.trdeg_one
        (scale d).radius (by exact_mod_cast (scale d).radius_pos)
        r.hyperplane_degree r.exceptional_degree
    · exact margin_of_image_outside_chart (structureMap d) (centerIdeal d)
        (projection d) (A d) (J d) (exceptionalInclusion d) (exceptional_presents d)
        a ha hample d.sigma d.sigma_pos_real C (affineChart d).opensRange
        (centerIdeal_support_subset_chart d) (fun c hh => hm ⟨c,hh⟩)

theorem exists_positive_uniform_margin_of_affine_curve_data
    (a : ℕ) (ha : 1 < a) (hample : (((A d).pow a).tensor (J d)).IsAmple)
    (hdata : ∀ C : IntegralCurve (blowup d),
      (¬ ∃ x : compactification d, Set.range (C.embedding ≫ projection d) ⊆ ({x} : Set _)) →
      (∃ c : C.scheme, (C.embedding ≫ projection d) c ∈ (affineChart d).opensRange) →
      Nonempty (AffineCurveDegreeData d C)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ C : IntegralCurve (blowup d),
      ε * (curveDegree (structureMap d) (((A d).pow a).tensor (J d)) C : ℝ) ≤
        (curveDegree (structureMap d) ((A d).tensor (J d)) C : ℝ) :=
  ⟨marginCoefficient a d.sigma,marginCoefficient_pos ha d.sigma_pos_real,
    uniform_margin_of_affine_curve_data d a ha hample hdata⟩

end BlowupMargin

end

end LogarithmExtension.LogRatio

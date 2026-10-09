import LogarithmExtension.LogRatioBlowupGeometry
import LogarithmExtension.LogRatioExceptionalDegree

/-! The exceptional degree for the concrete two-base blowup, with all
residue and function-field hypotheses derived from an intrinsic curve.
Adapted portions of the OpenAI and one-base wrappers are Apache-2.0. -/

noncomputable section
namespace LogarithmExtension.LogRatio.ExceptionalDegree

open OAI OAI.PiExponent AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
open CurveNormalizationModel
open scoped BigOperators

theorem geometry_degree_eq_neg_contactSum (d : GeometryData)
    {E : Type} [Field E] [Algebra ℂ E] [Algebra.EssFiniteType ℂ E]
    (z : Fin (d.m+2) → E)
    (hgen : IntermediateField.adjoin ℂ (Set.range z) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1)
    (f : E) (hf : Transcendental ℂ f) :
    letI := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg f hf
    ∀ (g : parameterCurve f hf ⟶ BlowupGeometry.blowup d),
    parameterCurveGenericPoint f hf ≫ g ≫ BlowupGeometry.projection d =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫
        BlowupGeometry.affineChart d →
    ((eulerCharacteristic (parameterCurveStructureMap f hf) 1
        ((BlowupGeometry.J d).pullback g).sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) : ℤ) : ℝ) =
      -((BlowupGeometry.scale d).radius : ℝ) * d.contactSum z hgen htrdeg := by
  let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
  let := hfinite f hf
  intro g hgeneric
  let hres := PlaceLocalRing.residue_integral htrdeg.le
  let hz := CurveGeometry.nonconstant_coordinates z hgen htrdeg
  have h := compactIdeal_degree_eq_neg_contact_sum (K := d.K) f hf d.slopes
    (BlowupGeometry.logCutoff d) (BlowupGeometry.scale d).jetPowers
    (BlowupGeometry.scale d).jetPowers_pos d.curveJetWeights d.curveJetWeights_pos
    (BlowupGeometry.scale d).radius (BlowupGeometry.scale d).jetPowers_eq
    (BlowupGeometry.logCutoff_strict d) (BlowupGeometry.logCutoff_strict_second d)
    (BlowupGeometry.affineChart d) (BlowupGeometry.compactificationStructureMap d)
    (BlowupGeometry.affineChart_over d) (BlowupGeometry.projection d) (BlowupGeometry.J d)
    (BlowupGeometry.exceptionalInclusion d) (BlowupGeometry.exceptional_presents d)
    g z hz hgeneric hres hfinite
  change _ = -((BlowupGeometry.scale d).radius : ℝ) *
    ∑ p ∈ ContactFamily.places hfinite z hz d.K,
      (ContactFamily.contact hres hfinite z hz d.K d.slopes d.curveJetWeights p : ℝ)
  exact_mod_cast h

#print axioms geometry_degree_eq_neg_contactSum

end LogarithmExtension.LogRatio.ExceptionalDegree

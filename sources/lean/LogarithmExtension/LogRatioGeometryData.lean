import LogarithmExtension.LogRatioCurveInequality

/-!
# Explicit geometric data for the two-base interpolation construction

The hypotheses are weight inequalities and reduced rational slopes. There
is no assumed curve bound, interpolation theorem, ampleness statement,
matrix rank, or irrationality-exponent conclusion. The checked two-base
curve inequality supplies the numerical margin for the actual contacts.
-/

noncomputable section
namespace LogarithmExtension.LogRatio

open OAI OAI.PiExponent
open scoped BigOperators

structure GeometryData where
  m : ℕ
  K : ℕ
  p : Fin m → ℕ
  q : Fin m → ℕ
  q_pos : ∀ i, 0 < q i
  coprime : ∀ i, Nat.Coprime (q i) (p i)
  curveDegreeWeights : Fin (m+2) → ℚ
  curveJetWeights : Fin (m+2) → ℚ
  curveDegreeWeights_pos : ∀ i, 0 < curveDegreeWeights i
  curveJetWeights_pos : ∀ i, 0 < curveJetWeights i
  degree_base_eq : curveDegreeWeights 1 = curveDegreeWeights 0
  jet_base_eq : curveJetWeights 1 = curveJetWeights 0
  sigma : ℚ
  sigma_pos : 0 < sigma
  curve_volume : (K : ℝ) * (1+3*(sigma : ℝ))^(m+2) *
    (∏ i, (curveDegreeWeights i : ℝ)) / (∏ i, (curveJetWeights i : ℝ)) < 1
  base_gap : 2 * (1 / ((sigma : ℝ) / ((m : ℝ)+3))) *
    (curveJetWeights 0 : ℝ) < curveDegreeWeights 0
  curve_separated_weight_products : ∀ A B : Finset (Fin (m+2)), A.card = B.card →
    ∀ i, 2 ≤ i.val → i ∈ A → i ∉ B →
    (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
    (A.card : ℝ)^A.card * (1 / ((sigma : ℝ) / ((m : ℝ)+3)))^A.card *
      (∏ j ∈ B, (curveJetWeights j : ℝ)) < ∏ j ∈ A, (curveDegreeWeights j : ℝ)
  curve_coordinate_ratio : ∀ i : Fin m,
    (1+(sigma : ℝ)) * (curveDegreeWeights i.succ.succ : ℝ) < curveJetWeights i.succ.succ
  denominator_ratio : ∀ i : Fin m,
    (1+(sigma : ℝ)) * (curveDegreeWeights 0 : ℝ) < (q i : ℝ) * curveJetWeights 0

namespace GeometryData

variable (d : GeometryData)

def centerY (j : Fin d.K) : ℂ := 2^j.val
def centerZ (j : Fin d.K) : ℂ := 3^j.val
def curveCenters (_ : Fin d.K) (_ : Fin d.m) : ℂ := 0
def slopes (i : Fin d.m) : ℂ := (d.p i : ℂ)/(d.q i : ℂ)

theorem centerY_ne_zero (j : Fin d.K) : d.centerY j ≠ 0 := by simp [centerY]
theorem centerZ_ne_zero (j : Fin d.K) : d.centerZ j ≠ 0 := by simp [centerZ]

theorem sigma_pos_real : (0 : ℝ) < d.sigma := by exact_mod_cast d.sigma_pos

theorem fullCenters_injective : Function.Injective
    (fun j => PlaceContact.center (d.centerY j) (d.centerZ j) (d.curveCenters j)) := by
  intro k l h
  apply Fin.ext
  apply CurveRelations.center_character_injective d.m 0 1 (by decide)
  exact congrArg (fun a : Fin (d.m+2) → ℂ => a 1 ^ 1 / a 0 ^ 0) h

variable {E : Type*} [Field E] [Algebra ℂ E] [Algebra.EssFiniteType ℂ E]

def contactSum (z : Fin (d.m+2) → E)
    (hgen : IntermediateField.adjoin ℂ (Set.range z) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1) : ℝ :=
  let hres := PlaceLocalRing.residue_integral htrdeg.le
  let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
  let hz := CurveGeometry.nonconstant_coordinates z hgen htrdeg
  ∑ p ∈ ContactFamily.places hfinite z hz d.K,
    (ContactFamily.contact hres hfinite z hz d.K d.slopes d.curveJetWeights p : ℝ)

def poleDegree (z : Fin (d.m+2) → E) (htrdeg : Algebra.trdeg ℂ E = 1) : ℝ :=
  CurveContactSum.weightedDegree
    (CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg) z d.curveDegreeWeights

/-- The actual two-base curve bound, with all inputs supplied by the
explicit geometric data rather than an assumed inequality. -/
theorem curve_inequality (z : Fin (d.m+2) → E)
    (hgen : IntermediateField.adjoin ℂ (Set.range z) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1) :
    (1+(d.sigma : ℝ)) * d.contactSum z hgen htrdeg ≤ d.poleDegree z htrdeg := by
  exact CurveInequality.weighted_curve_inequality_intrinsic z hgen htrdeg
    d.p d.q d.q_pos d.coprime d.curveDegreeWeights d.curveJetWeights
    d.curveDegreeWeights_pos d.curveJetWeights_pos d.degree_base_eq d.jet_base_eq
    d.sigma d.sigma_pos d.curve_volume d.base_gap d.curve_separated_weight_products
    d.curve_coordinate_ratio d.denominator_ratio

#print axioms curve_inequality

end GeometryData
end LogarithmExtension.LogRatio

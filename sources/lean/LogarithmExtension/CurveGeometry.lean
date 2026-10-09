import LogarithmExtension.Basic
import LogarithmExtension.CurveInequality
import OAI.NumberTheory.PiExponent.Geometry.CurvePrimeHeight
import OAI.NumberTheory.PiExponent.Geometry.PlaceLocalRing

/-! # Intrinsic curve geometry for logarithmic power centres -/

noncomputable section
namespace LogarithmExtension.CurveGeometry

open OAI OAI.PiExponent OAI.PiExponentApprox
open CurveValuationCenter PlaceValuationRing PersistentWeightComparison
open LogarithmExtension.CurveContactFamily
open scoped BigOperators

variable {E : Type*} [Field E] [Algebra ℂ E]

theorem nonconstant_coordinates {n : ℕ} (z : Fin n → E)
    (hgen : IntermediateField.adjoin ℂ (Set.range z) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1) : ∃ i, Transcendental ℂ (z i) := by
  let : Algebra.Transcendental ℂ E := trdeg_ne_zero_iff.mp (by rw [htrdeg]; exact one_ne_zero)
  exact CurveCenters.exists_transcendental_coordinate z hgen
    (Algebra.Transcendental.transcendental (R := ℂ) (A := E))

theorem complex_power_centres_injective (r : ℝ) (hr : 0 < r) (hr1 : r ≠ 1) (K : ℕ) :
    Function.Injective (fun j : Fin K => (r : ℂ) ^ j.val) := by
  intro j k hjk
  apply Fin.ext
  apply positive_power_centers_injective r hr hr1
  change r ^ j.val = r ^ k.val
  change (r : ℂ) ^ j.val = (r : ℂ) ^ k.val at hjk
  exact_mod_cast hjk

variable [Algebra.EssFiniteType ℂ E]

/-- The finiteness, residue-field, height and nonconstancy inputs to the curve
inequality follow from the intrinsic one-dimensional function-field hypotheses. -/
theorem weighted_curve_inequality_intrinsic {m K : ℕ}
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (hy : ∀ j, y j ≠ 0)
    (hiy : Function.Injective y) (c : Fin K → Fin m → ℂ)
    (hgen : IntermediateField.adjoin ℂ (Set.range z) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1)
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (sigma : ℚ) (hsigma : 0 < sigma)
    (hvol : (K : ℝ) * (1+3*(sigma : ℝ))^(m+1) *
      (∏ i, (w i : ℝ)) / (∏ i, (v i : ℝ)) < 1)
    (hseparated : ∀ A B : Finset (Fin (m+1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      comparisonConstant m sigma * (∏ j ∈ B, (v j : ℝ)) < ∏ j ∈ A, (w j : ℝ))
    (hratio : ∀ i : Fin m, (1+(sigma : ℝ)) * (w i.succ : ℝ) < v i.succ) :
    let hres := PlaceLocalRing.residue_integral htrdeg.le
    let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
    let hz := nonconstant_coordinates z hgen htrdeg
    (1+(sigma : ℝ)) * ∑ p ∈ places hfinite z y c hz,
        (contact hres hfinite z y hy c hz v p : ℝ) ≤
      CurveContactSum.weightedDegree hfinite z w := by
  exact CurveInequality.weighted_curve_inequality _ _ z y hy hiy c
    (nonconstant_coordinates z hgen htrdeg)
    (CurvePrimeHeight.kernel_height_succ_le z hgen htrdeg)
    w v hw hv sigma hsigma hvol hseparated hratio

#print axioms weighted_curve_inequality_intrinsic

end LogarithmExtension.CurveGeometry

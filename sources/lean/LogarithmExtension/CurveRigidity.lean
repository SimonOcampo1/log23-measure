import OAI.NumberTheory.PiExponent.Geometry.CurveFieldRigidity

/-!
# Rigidity at arbitrary nonzero exponential centres

This removes the Y = 1 restriction in the upstream field-rigidity consequence.
All persistence, height, and separation hypotheses remain explicit. In
particular, this does not by itself prove the global interpolation theorem.
-/

noncomputable section
namespace LogarithmExtension

open OAI OAI.PiExponent OAI.PiExponentApprox
open OAI.PiExponent.PersistentWeightComparison
open OAI.PiExponent.CurveCenters OAI.PiExponent.CurveValuationCenter
open OAI.PiExponent.CurveFieldRigidity
open scoped BigOperators

theorem logarithmic_coordinate_eq_center
    {E : Type*} [Field E] [Algebra ℂ E] {m : ℕ}
    (x : Fin (m+1) → E) (a : Fin (m+1) → ℂ) (ha : a 0 ≠ 0)
    (p : NormalizedPlace ℂ E) (hp : Centered x a p)
    (hheight : (coordinateKernel x).height ≤ m)
    (rho : Fin (m+1) → ℚ) (hrho : ∀ i, 0 < rho i)
    (cost : Fin (m+1) → ℝ) (hcost : ∀ i, 0 < cost i)
    (sigma N : ℝ) (hsigma : 0 < sigma) (hN : 0 < N)
    (hrect : UniformRectangles (m+1) cost (sigma / ((m : ℝ)+2)) N)
    (F : FramePolynomial m) (hF0 : F ≠ 0)
    (hF : HasWeightedDegreeLE (fun i => (rho i : ℝ)) N F)
    (hvanish : ∀ word : List (Fin (m+1)), frameWordCost cost word ≤ sigma*N →
      MvPolynomial.aeval x (polynomialFrameWord m word F) = 0)
    (hseparated : ∀ A B : Finset (Fin (m+1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      comparisonConstant m sigma * (∏ j ∈ B, cost j) < ∏ j ∈ A, (rho j : ℝ)) :
    x 0 = algebraMap ℂ E (a 0) := by
  have hx0 : x 0 ≠ 0 := by
    intro hz
    exact ha (hp.constant_coordinate 0 0 (by simpa using hz)).symm
  have hY : MvPolynomial.X (0 : Fin (m+1)) ∉ coordinateKernel x := by
    simpa only [mem_coordinateKernel, MvPolynomial.aeval_X] using hx0
  have hbound : ((m : ℝ)+2) * ((sigma / ((m : ℝ)+2))*N) = sigma*N := by
    have hm : (m : ℝ)+2 ≠ 0 := by positivity
    field_simp
  obtain ⟨c, hc⟩ := CurveComponentRigidity.coordinate_constant_of_persistent_comparison
    (fun i => (rho i : ℝ)) cost (comparisonConstant m sigma)
    ((sigma / ((m : ℝ)+2))*N) (fun i => (hcost i).le) (by positivity)
    F hF0 (coordinateKernel x) inferInstance hheight hY
    (fun word hword => hvanish word (by simpa only [hbound] using hword))
    (logarithmic_persistent_comparison rho hrho cost hcost sigma N hsigma hN hrect
      F hF (coordinateKernel x) hY) hseparated
  have hxc : x 0 = algebraMap ℂ E c := by
    simpa only [mem_coordinateKernel, map_sub, MvPolynomial.aeval_X,
      MvPolynomial.aeval_C, sub_eq_zero] using hc
  rw [hp.constant_coordinate 0 c hxc] at hxc
  exact hxc

/-- A constant first coordinate can meet only one member of a family with
distinct first coordinates. No injectivity of the remaining coordinates is needed. -/
theorem center_index_unique_of_constant_first
    {E J : Type*} [Field E] [Algebra ℂ E] {m : ℕ}
    (x : Fin (m+1) → E) (a : J → Fin (m+1) → ℂ)
    (ha : Function.Injective (fun j => a j 0))
    (c : ℂ) (hc : x 0 = algebraMap ℂ E c)
    (j k : J) (p q : NormalizedPlace ℂ E)
    (hp : Centered x (a j) p) (hq : Centered x (a k) q) : j = k := by
  apply ha
  exact (hp.constant_coordinate 0 c hc).symm.trans (hq.constant_coordinate 0 c hc)

#print axioms logarithmic_coordinate_eq_center
#print axioms center_index_unique_of_constant_first

end LogarithmExtension

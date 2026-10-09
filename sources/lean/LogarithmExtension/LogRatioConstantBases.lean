import LogarithmExtension.LogRatioPlaceContact

/-!
# The constant-base branch of the two-base curve inequality

When both torus coordinates are constant, the logarithmic terms vanish
on each centered branch. A nonconstant auxiliary coordinate therefore
gives the ordinary coordinate-contact comparison, for the actual contact
already defined in LogRatioPlaceContact.
-/

noncomputable section
namespace LogarithmExtension.LogRatio.ConstantBases

open OAI.PiExponent CurveValuationCenter CurveCenters PlaceValuationRing
open PolynomialFrame WeightedPolynomialPole CurveContactSum
open scoped BigOperators

theorem normalizedDifference_C (c : ℂ) (hc : c ≠ 0) :
    BranchEvaluation.normalizedDifference c (PowerSeries.C c) = 0 := by
  simp [BranchEvaluation.normalizedDifference, ← map_mul, hc]

variable {E : Type*} [Field E] [Algebra ℂ E] {m : ℕ}

theorem aux_coordinate_order_lower
    (place : NormalizedPlace ℂ E)
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring place))]
    (x : Fin (m+2) → E) (cy cz : ℂ) (c r : Fin m → ℂ)
    (hcy : cy ≠ 0) (hcz : cz ≠ 0) (hc : Centered x (PlaceContact.center cy cz c) place)
    (hnc : ∃ i, x i ≠ algebraMap ℂ E (PlaceContact.center cy cz c i))
    (v : Fin (m+2) → ℚ) (hv : ∀ i, 0 < v i)
    (hy : x 0 = algebraMap ℂ E cy) (hz : x 1 = algebraMap ℂ E cz)
    (i : Fin m) (hne : x i.succ.succ - algebraMap ℂ E (c i) ≠ 0) :
    v i.succ.succ * PlaceContact.contact place x cy cz c hc r hcy hcz hnc v ≤
      (coordinateOrder place.valuation (x i.succ.succ - algebraMap ℂ E (c i)) : ℚ) := by
  let xr := PlaceCenteredBranch.lift place x (PlaceContact.center cy cz c) hc
  let F : Poly m := MvPolynomial.X i.succ.succ - MvPolynomial.C (c i)
  have hF : MvPolynomial.aeval x F = x i.succ.succ - algebraMap ℂ E (c i) := by simp [F]
  have hn : MvPolynomial.aeval xr F ≠ 0 := by
    intro hh
    apply hne
    rw [← hF, ← PlaceCenteredBranch.lift_aeval place x (PlaceContact.center cy cz c) hc,
      hh, map_zero]
  have hsy := (PlaceContact.series_eq_constant_iff place x cy cz c hc 0 cy).mpr hy
  have hsz := (PlaceContact.series_eq_constant_iff place x cy cz c hc 1 cz).mpr hz
  have hcoordinate : PlaceContact.coordinates place x cy cz c hc r i.succ.succ =
      DVRBranch.expansion ℂ (ring place) (MvPolynomial.aeval xr F) := by
    simp only [PlaceContact.coordinates, BranchEvaluation.coordinates, Fin.cases_succ,
      hsy, hsz, normalizedDifference_C cy hcy, normalizedDifference_C cz hcz,
      PowerSeries.subst_zero_of_constantCoeff_zero PowerSeries.constantCoeff_log,
      sub_zero, mul_zero, add_zero]
    simp only [F, map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C, AlgHom.commutes]
    rfl
  have horder : (PlaceContact.coordinates place x cy cz c hc r i.succ.succ).order =
      ((Module.length (ring place) ((ring place) ⧸ Ideal.span {MvPolynomial.aeval xr F})).toNat : ℕ∞) := by
    rw [hcoordinate, DVRBranch.expansion_order_eq_length ℂ (ring place) hn]
    exact (ENat.natCast_toNat (CurveLocalOrder.principal_colength_ne_top hn)).symm
  have hb := BranchContact.contact_bound v hv (PlaceContact.coordinates place x cy cz c hc r)
    (PlaceContact.coordinates_nonzero place x cy cz c hc r hcy hcz hnc)
    i.succ.succ _ horder
  rw [← hF, PlaceCenteredBranch.coordinateOrder_aeval_eq_length
    place x (PlaceContact.center cy cz c) hc F (hF ▸ hne)]
  simpa only [PlaceContact.contact, Int.cast_natCast, mul_comm] using hb

theorem aux_contact_sum
    (hres : ∀ place : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring place)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : Fin (m+2) → E) (cy cz : ℂ) (c r : Fin m → ℂ)
    (hcy : cy ≠ 0) (hcz : cz ≠ 0)
    (hnc : ∃ i, x i ≠ algebraMap ℂ E (PlaceContact.center cy cz c i))
    (w v : Fin (m+2) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (hy : x 0 = algebraMap ℂ E cy) (hz : x 1 = algebraMap ℂ E cz)
    (i : Fin m) (hne : x i.succ.succ - algebraMap ℂ E (c i) ≠ 0)
    (S : Finset (NormalizedPlace ℂ E))
    (hc : ∀ place ∈ S, Centered x (PlaceContact.center cy cz c) place)
    (mu : NormalizedPlace ℂ E → ℝ)
    (hmu : ∀ place (hp : place ∈ S), letI := hres place;
      mu place = (PlaceContact.contact place x cy cz c (hc place hp) r hcy hcz hnc v : ℝ)) :
    (v i.succ.succ : ℝ) * (∑ place ∈ S, mu place) ≤
      (w i.succ.succ : ℝ) * weightedDegree hfinite x w := by
  let F : Poly m := MvPolynomial.X i.succ.succ - MvPolynomial.C (c i)
  have hF : MvPolynomial.aeval x F = x i.succ.succ - algebraMap ℂ E (c i) := by simp [F]
  apply polynomial_contact_sum_le hfinite x w hw (w i.succ.succ : ℝ) (v i.succ.succ : ℝ)
    (by exact_mod_cast (hw i.succ.succ).le) F
    (CoordinateContactBound.supportBound_X_sub_C (fun j => (w j : ℝ)) i.succ.succ
      (by exact_mod_cast (hw i.succ.succ).le) (c i))
    (hF ▸ hne) S mu
  intro place hp
  let := hres place
  rw [hmu place hp, hF]
  exact_mod_cast aux_coordinate_order_lower place x cy cz c r hcy hcz (hc place hp)
    hnc v hv hy hz i hne

/-- A nonconstant curve with two constant base coordinates has a
nonconstant auxiliary coordinate. -/
theorem exists_nonconstant_aux (x : Fin (m+2) → E)
    (hx : ∃ i, Transcendental ℂ (x i)) (cy cz : ℂ)
    (hy : x 0 = algebraMap ℂ E cy) (hz : x 1 = algebraMap ℂ E cz) :
    ∃ i : Fin m, Transcendental ℂ (x i.succ.succ) := by
  obtain ⟨i, hi⟩ := hx
  cases i using Fin.cases with
  | zero => exact (hi (hy.symm ▸ isAlgebraic_algebraMap _)).elim
  | succ j =>
    cases j using Fin.cases with
    | zero => exact (hi (hz.symm ▸ isAlgebraic_algebraMap _)).elim
    | succ k => exact ⟨k, hi⟩

#print axioms aux_contact_sum

end LogarithmExtension.LogRatio.ConstantBases

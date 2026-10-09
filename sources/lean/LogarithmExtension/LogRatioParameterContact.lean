import LogarithmExtension.LogRatioMonomialParameter
import LogarithmExtension.LogRatioCurveRelations

/-!
# Local power contact and global pole bounds

At a nonzero center in characteristic zero, T^q - t0^q has the same order
as T - t0. Globally, Y = d T^q multiplies pole orders by q. These are the
two distinct inputs to the proposed q-fold curve-contact improvement.
-/

noncomputable section
namespace LogarithmExtension.LogRatio.ParameterContact

open scoped BigOperators
open OAI.PiExponent CurveValuationCenter CurveProductFormula
open WeightedCurveDegree WeightedPolynomialPole CurveContactSum PlaceValuationRing

variable {E : Type*} [Field E] [Algebra ℂ E]

omit [Algebra ℂ E] in
theorem coe_coordinateOrder (v : AddValuation E (WithTop ℤ)) (x : E) (hx : x ≠ 0) :
    (coordinateOrder v x : WithTop ℤ) = v x := by
  simp only [coordinateOrder, dite_eq_right hx, coe_integerOrder, Units.val_mk0]

theorem coordinateOrder_constant_mul_pow (place : NormalizedPlace ℂ E)
    (d : ℂ) (hd : d ≠ 0) (T : E) (hT : T ≠ 0) (q : ℕ) :
    coordinateOrder place.valuation (algebraMap ℂ E d * T^q) =
      (q : ℤ) * coordinateOrder place.valuation T := by
  have hdE : algebraMap ℂ E d ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap ℂ E).injective).mpr hd
  apply WithTop.coe_injective
  rw [coe_coordinateOrder _ _ (mul_ne_zero hdE (pow_ne_zero _ hT))]
  rw [place.valuation.map_mul, valuation_constant_eq_zero place d hd,
    zero_add, place.valuation.map_pow, ← coe_coordinateOrder _ T hT]
  simp only [← WithTop.coe_nsmul, nsmul_eq_mul, WithTop.coe_mul, WithTop.coe_natCast]

section Local

variable (place : NormalizedPlace ℂ E)
  [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring place))]

theorem residue_eq_iff_positive_difference (x : ring place) (c : ℂ) :
    DVRBranch.residueCoefficientMap ℂ (ring place) x = c ↔
      0 < place.valuation ((x : E) - algebraMap ℂ E c) := by
  have he : DVRBranch.residueCoefficientMap ℂ (ring place) x = c ↔
      x - algebraMap ℂ (ring place) c ∈
        RingHom.ker (DVRBranch.residueCoefficientMap ℂ (ring place)).toRingHom := by
    simp [RingHom.mem_ker, map_sub, DVRBranch.residueCoefficientMap, sub_eq_zero]
  rw [he, DVRBranch.residueCoefficientMap_ker]
  exact place.valuation.toValuation.mem_maximalIdeal_iff

theorem valuation_eq_zero_of_residue_ne_zero (x : ring place)
    (hx : DVRBranch.residueCoefficientMap ℂ (ring place) x ≠ 0) :
    place.valuation (x : E) = 0 := by
  apply le_antisymm _ x.property
  by_contra h
  have hp : 0 < place.valuation (x : E) := lt_of_not_ge h
  apply hx
  exact (residue_eq_iff_positive_difference place x 0).mpr (by simpa using hp)

/-- Raising a regular parameter to a positive power is unramified at every
nonzero complex value. The geometric sum is a unit because its residue is
q * c^(q-1), which is nonzero in characteristic zero. -/
theorem power_difference_valuation (x : ring place) (c : ℂ) (hc : c ≠ 0)
    (hx : DVRBranch.residueCoefficientMap ℂ (ring place) x = c)
    (q : ℕ) (hq : 0 < q) :
    place.valuation ((x : E)^q - algebraMap ℂ E (c^q)) =
      place.valuation ((x : E) - algebraMap ℂ E c) := by
  let S : ring place := ∑ i ∈ Finset.range q,
    x^i * (algebraMap ℂ (ring place) c)^(q - 1 - i)
  have hres : DVRBranch.residueCoefficientMap ℂ (ring place) S =
      (q : ℂ) * c^(q - 1) := by
    simp only [S, map_sum, map_mul, map_pow, hx,
      show ∀ a : ℂ, DVRBranch.residueCoefficientMap ℂ (ring place)
        (algebraMap ℂ (ring place) a) = a from
          CurveLocalOrder.residueAugmentation_algebraMap ℂ (ring place)]
    exact geom_sum₂_self c q
  have hS0 : place.valuation (S : E) = 0 :=
    valuation_eq_zero_of_residue_ne_zero place S (by
      rw [hres]
      exact mul_ne_zero (Nat.cast_ne_zero.mpr hq.ne') (pow_ne_zero _ hc))
  have hfactor : (x : E)^q - algebraMap ℂ E (c^q) =
      ((x : E) - algebraMap ℂ E c) * (S : E) := by
    have h := (Commute.all x (algebraMap ℂ (ring place) c)).mul_geom_sum₂ q
    have he := congrArg (fun a : ring place => (a : E)) h
    simpa [S] using he.symm
  rw [hfactor, place.valuation.map_mul, hS0, add_zero]

end Local

/-- Pole control for the monomial parameter, expressed directly in terms of
the existing weighted curve degree, so no unproved degree-of-a-map identity
is needed. -/
theorem parameter_difference_order_lower {ι : Type*} [Fintype ι]
    (place : NormalizedPlace ℂ E) (x : ι → E) (w : ι → ℚ)
    (hw : ∀ i, 0 < w i) (i : ι)
    (T : E) (hT : T ≠ 0) (d : ℂ) (hd : d ≠ 0)
    (q : ℕ) (hq : 0 < q) (hcoordinate : x i = algebraMap ℂ E d * T^q)
    (a : ℂ) (hne : T - algebraMap ℂ E a ≠ 0) :
    -((w i : ℝ) / (q : ℝ)) * (coordinatePole place.valuation x w : ℝ) ≤
      (coordinateOrder place.valuation (T - algebraMap ℂ E a) : ℝ) := by
  have hord : coordinateOrder place.valuation (x i) =
      (q : ℤ) * coordinateOrder place.valuation T := by
    rw [hcoordinate]
    exact coordinateOrder_constant_mul_pow place d hd T hT q
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hwiR : (0 : ℝ) < w i := by exact_mod_cast hw i
  have hp0 : (0 : ℝ) ≤ coordinatePole place.valuation x w := by
    exact_mod_cast weightedPole_nonneg w
      (fun j => (coordinateOrder place.valuation (x j) : ℚ))
  have hy := (div_le_iff₀ (hw i)).mp
    (div_le_weightedPole w (fun j => (coordinateOrder place.valuation (x j) : ℚ)) i)
  change -(coordinateOrder place.valuation (x i) : ℚ) ≤
    coordinatePole place.valuation x w * w i at hy
  rw [hord] at hy
  have hyR : -(q : ℝ) * (coordinateOrder place.valuation T : ℝ) ≤
      (coordinatePole place.valuation x w : ℝ) * (w i : ℝ) := by
    have hh : -((q : ℝ) * (coordinateOrder place.valuation T : ℝ)) ≤
        (coordinatePole place.valuation x w : ℝ) * (w i : ℝ) := by exact_mod_cast hy
    simpa only [neg_mul] using hh
  have hTbound : -((w i : ℝ) / (q : ℝ)) * (coordinatePole place.valuation x w : ℝ) ≤
      (coordinateOrder place.valuation T : ℝ) := by
    apply (mul_le_mul_iff_of_pos_right hqR).mp
    field_simp
    nlinarith
  have hnonpos : -((w i : ℝ) / (q : ℝ)) * (coordinatePole place.valuation x w : ℝ) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hp0
  have hval := (PolynomialPoleBound.realValuation place.valuation).map_le_sub
    (show ((-((w i : ℝ) / (q : ℝ)) * (coordinatePole place.valuation x w : ℝ) : ℝ) :
      WithTop ℝ) ≤ PolynomialPoleBound.realValuation place.valuation T from by
        rw [realValuation_of_ne_zero _ T hT]
        exact WithTop.coe_le_coe.mpr hTbound)
    (show ((-((w i : ℝ) / (q : ℝ)) * (coordinatePole place.valuation x w : ℝ) : ℝ) :
      WithTop ℝ) ≤ PolynomialPoleBound.realValuation place.valuation (algebraMap ℂ E a) from
        (WithTop.coe_le_coe.mpr hnonpos).trans (constants_real_nonneg place a))
  rw [realValuation_of_ne_zero _ _ hne] at hval
  exact WithTop.coe_le_coe.mp hval

theorem contact_sum_power_coordinate {ι : Type*} [Fintype ι]
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : ι → E) (w : ι → ℚ) (hw : ∀ i, 0 < w i) (i : ι)
    (T : E) (hT : T ≠ 0) (d : ℂ) (hd : d ≠ 0)
    (q : ℕ) (hq : 0 < q) (hcoordinate : x i = algebraMap ℂ E d * T^q)
    (a : ℂ) (hne : T - algebraMap ℂ E a ≠ 0)
    (S : Finset (NormalizedPlace ℂ E)) (mu : NormalizedPlace ℂ E → ℝ) (v0 : ℝ)
    (hlocal : ∀ place ∈ S, v0 * mu place ≤
      (coordinateOrder place.valuation (T - algebraMap ℂ E a) : ℝ)) :
    ((q : ℝ) * v0) * (∑ place ∈ S, mu place) ≤
      (w i : ℝ) * weightedDegree hfinite x w := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hwiR : (0 : ℝ) < w i := by exact_mod_cast hw i
  have hb := contact_sum_le_of_principal_sum
    (coordinateOrderDivisor hfinite (T - algebraMap ℂ E a))
    (weightedPoleDivisor hfinite x w)
    (coordinateOrderDivisor_degree_zero hfinite _)
    (fun place => weightedPole_nonneg w
      (fun j => (coordinateOrder place.valuation (x j) : ℚ)))
    S mu ((w i : ℝ) / (q : ℝ)) v0 (by positivity)
    (by simpa only [coordinateOrderDivisor_apply] using hlocal)
    (by
      intro place
      simpa only [weightedPoleDivisor_apply, coordinateOrderDivisor_apply] using
        parameter_difference_order_lower place x w hw i T hT d hd q hq hcoordinate a hne)
  have hh := mul_le_mul_of_nonneg_left hb hqR.le
  change (q : ℝ) * (v0 * (∑ place ∈ S, mu place)) ≤
    (q : ℝ) * (((w i : ℝ) / (q : ℝ)) * weightedDegree hfinite x w) at hh
  convert hh using 1 <;> field_simp

#print axioms power_difference_valuation
#print axioms contact_sum_power_coordinate

end LogarithmExtension.LogRatio.ParameterContact

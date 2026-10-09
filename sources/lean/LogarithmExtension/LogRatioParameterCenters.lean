import LogarithmExtension.LogRatioParameterContact

/-!
# A common monomial-parameter value over a two-base center

The parameter is the explicit Bezout monomial, not an unspecified q-th
root. Its residue is therefore determined by the two coordinate values at
the center, independently of the choice of branch.
-/

noncomputable section
namespace LogarithmExtension.LogRatio.ParameterCenters

open OAI.PiExponent CurveValuationCenter CurveProductFormula
open PlaceValuationRing WeightedPolynomialPole ParameterContact MonomialParameter

variable {E : Type*} [Field E] [Algebra ℂ E]

theorem map_unit_zpow {A F : Type*} [CommRing A] [Field F]
    (f : A →+* F) (u : Aˣ) (n : ℤ) : f ((u^n : Aˣ) : A) = (f (u : A))^n := by
  change ((Units.map f.toMonoidHom (u^n) : Fˣ) : F) = _
  rw [map_zpow, Units.val_zpow_eq_zpow_val]
  rfl

section Local

variable (place : NormalizedPlace ℂ E)
  [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring place))]

theorem exists_unit_lift_centered (x : E) (c : ℂ) (hc : c ≠ 0)
    (hx : 0 < place.valuation (x - algebraMap ℂ E c)) :
    ∃ u : (ring place)ˣ, ((u : ring place) : E) = x ∧
      DVRBranch.residueCoefficientMap ℂ (ring place) (u : ring place) = c := by
  have hx0 : place.valuation x = 0 := by
    have hh := place.valuation.map_eq_of_lt_sub
      (show place.valuation (algebraMap ℂ E c) <
        place.valuation (x - algebraMap ℂ E c) by
          rw [valuation_constant_eq_zero place c hc]
          exact hx)
    simpa only [valuation_constant_eq_zero place c hc] using hh
  let xr : ring place := ⟨x, hx0.ge⟩
  have hres : DVRBranch.residueCoefficientMap ℂ (ring place) xr = c :=
    (residue_eq_iff_positive_difference place xr c).mpr hx
  have hu : IsUnit xr := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit xr).mp
    intro hz
    apply hc
    rw [← hres]
    change (CurveLocalOrder.residueCoefficientEquiv ℂ (ring place)).symm
      (IsLocalRing.residue (ring place) xr) = 0
    rw [hz, map_zero]
  obtain ⟨u, hu⟩ := hu
  exact ⟨u, by rw [hu], by rw [hu]; exact hres⟩

theorem exists_parameter_lift (y z : E) (cy cz : ℂ)
    (hcy : cy ≠ 0) (hcz : cz ≠ 0)
    (hy : 0 < place.valuation (y - algebraMap ℂ E cy))
    (hz : 0 < place.valuation (z - algebraMap ℂ E cz)) (p q : ℕ) :
    ∃ t : ring place, (t : E) = parameter y z p q ∧
      DVRBranch.residueCoefficientMap ℂ (ring place) t = parameter cy cz p q := by
  obtain ⟨yu, hyu, hry⟩ := exists_unit_lift_centered place y cy hcy hy
  obtain ⟨zu, hzu, hrz⟩ := exists_unit_lift_centered place z cz hcz hz
  let tu : (ring place)ˣ := yu^(Nat.gcdA q p) * zu^(Nat.gcdB q p)
  refine ⟨(tu : ring place), ?_, ?_⟩
  · change algebraMap (ring place) E (tu : ring place) = _
    simp only [tu, Units.val_mul, map_mul, map_unit_zpow, parameter]
    exact congrArg₂ (fun a b : E => a^(Nat.gcdA q p) * b^(Nat.gcdB q p)) hyu hzu
  · change (DVRBranch.residueCoefficientMap ℂ (ring place)).toRingHom (tu : ring place) = _
    simp only [tu, Units.val_mul, map_mul, map_unit_zpow, parameter]
    exact congrArg₂ (fun a b : ℂ => a^(Nat.gcdA q p) * b^(Nat.gcdB q p)) hry hrz

/-- Both the parameter value and the order equality are actual consequences
of the centered branch and the primitive character relation. -/
theorem parameter_contact_order (y z : E) (hy0 : y ≠ 0) (hz0 : z ≠ 0)
    (cy cz c : ℂ) (hcy : cy ≠ 0) (hcz : cz ≠ 0) (hc : c ≠ 0)
    (hy : 0 < place.valuation (y - algebraMap ℂ E cy))
    (hz : 0 < place.valuation (z - algebraMap ℂ E cz))
    (p q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime q p)
    (hrel : z^q = algebraMap ℂ E c * y^p) :
    place.valuation (parameter y z p q - algebraMap ℂ E (parameter cy cz p q)) =
      place.valuation (y - algebraMap ℂ E cy) := by
  obtain ⟨t, ht, hres⟩ := exists_parameter_lift place y z cy cz hcy hcz hy hz p q
  obtain ⟨yu, hyu, hry⟩ := exists_unit_lift_centered place y cy hcy hy
  have hY := (parameter_eqs y z hy0 hz0 c hc p q hcop hrel).1
  have hYr : (yu : ring place) =
      algebraMap ℂ (ring place) (c^(-Nat.gcdB q p)) * t^q := by
    apply Subtype.ext
    change ((yu : ring place) : E) =
      algebraMap ℂ E (c^(-Nat.gcdB q p)) * (t : E)^q
    simpa only [hyu, ht] using hY
  have hcenter : cy = c^(-Nat.gcdB q p) * (parameter cy cz p q)^q := by
    have hh := congrArg (DVRBranch.residueCoefficientMap ℂ (ring place)) hYr
    simpa [hry, hres] using hh
  have hfactor : y - algebraMap ℂ E cy =
      algebraMap ℂ E (c^(-Nat.gcdB q p)) *
        ((t : E)^q - algebraMap ℂ E ((parameter cy cz p q)^q)) := by
    calc
      _ = algebraMap ℂ E (c^(-Nat.gcdB q p)) * (parameter y z p q)^q -
          algebraMap ℂ E (c^(-Nat.gcdB q p) * (parameter cy cz p q)^q) :=
        congrArg₂ (fun a b : E => a - b) hY (congrArg (algebraMap ℂ E) hcenter)
      _ = _ := by rw [map_mul, ht]; ring
  rw [hfactor, place.valuation.map_mul,
    valuation_constant_eq_zero place _ (zpow_ne_zero _ hc), zero_add,
    power_difference_valuation place t _ (parameter_ne_zero cy cz hcy hcz p q) hres q hq,
    ht]

end Local

open CurveContactSum
open scoped BigOperators

/-- The q-fold comparison now needs only the ordinary bound on the first
coordinate's order. The shared parameter value and its local order bound
are derived, rather than assumed. -/
theorem contact_sum_primitive_character {ι : Type*} [Fintype ι]
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : ι → E) (w : ι → ℚ) (hw : ∀ i, 0 < w i) (iy iz : ι)
    (hy : Transcendental ℂ (x iy)) (hz0 : x iz ≠ 0)
    (cy cz c : ℂ) (hcy : cy ≠ 0) (hcz : cz ≠ 0) (hc : c ≠ 0)
    (p q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime q p)
    (hrel : (x iz)^q = algebraMap ℂ E c * (x iy)^p)
    (S : Finset (NormalizedPlace ℂ E))
    (hres : ∀ place ∈ S,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring place)))
    (hcenterY : ∀ place ∈ S, 0 < place.valuation (x iy - algebraMap ℂ E cy))
    (hcenterZ : ∀ place ∈ S, 0 < place.valuation (x iz - algebraMap ℂ E cz))
    (mu : NormalizedPlace ℂ E → ℝ) (v0 : ℝ)
    (hlocal : ∀ place ∈ S, v0 * mu place ≤
      (coordinateOrder place.valuation (x iy - algebraMap ℂ E cy) : ℝ)) :
    ((q : ℝ) * v0) * (∑ place ∈ S, mu place) ≤
      (w iy : ℝ) * weightedDegree hfinite x w := by
  have hy0 : x iy ≠ 0 := by
    intro he
    exact hy (he.symm ▸ isAlgebraic_zero)
  let T := parameter (x iy) (x iz) p q
  let a := parameter cy cz p q
  let d := c^(-Nat.gcdB q p)
  have hY : x iy = algebraMap ℂ E d * T^q :=
    (parameter_eqs (x iy) (x iz) hy0 hz0 c hc p q hcop hrel).1
  have hTdiff : T - algebraMap ℂ E a ≠ 0 := by
    intro he
    have hh : x iy = algebraMap ℂ E (d * a^q) := by
      rw [hY, sub_eq_zero.mp he, map_mul, map_pow]
    exact hy (hh.symm ▸ isAlgebraic_algebraMap _)
  have hYdiff : x iy - algebraMap ℂ E cy ≠ 0 := by
    intro he
    exact hy ((sub_eq_zero.mp he).symm ▸ isAlgebraic_algebraMap _)
  apply contact_sum_power_coordinate hfinite x w hw iy T
    (parameter_ne_zero (x iy) (x iz) hy0 hz0 p q) d (zpow_ne_zero _ hc)
    q hq hY a hTdiff S mu v0
  intro place hplace
  let := hres place hplace
  have hord : coordinateOrder place.valuation (T - algebraMap ℂ E a) =
      coordinateOrder place.valuation (x iy - algebraMap ℂ E cy) := by
    apply WithTop.coe_injective
    rw [coe_coordinateOrder _ _ hTdiff, coe_coordinateOrder _ _ hYdiff]
    exact parameter_contact_order place (x iy) (x iz) hy0 hz0 cy cz c hcy hcz hc
      (hcenterY place hplace) (hcenterZ place hplace) p q hq hcop hrel
  rw [hord]
  exact hlocal place hplace

#print axioms parameter_contact_order
#print axioms contact_sum_primitive_character

end LogarithmExtension.LogRatio.ParameterCenters

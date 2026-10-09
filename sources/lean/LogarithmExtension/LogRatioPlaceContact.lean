import LogarithmExtension.LogRatioBranchEvaluation
import LogarithmExtension.LogRatioParameterCenters
import OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateContactBound

/-!
# Two-base contact on actual normalized curve branches

The contact is defined by the minimum of the weighted orders of the
inverse formal-jet coordinates in the completed valuation ring. The
field-order estimate and primitive-character comparison are derived from
this definition, rather than postulated as local-contact assumptions.
-/

noncomputable section
namespace LogarithmExtension.LogRatio.PlaceContact

open OAI.PiExponent CurveValuationCenter CurveCenters PlaceValuationRing
open PolynomialFrame WeightedPolynomialPole CurveContactSum
open scoped BigOperators

def center {m : ℕ} (cy cz : ℂ) (c : Fin m → ℂ) : Fin (m+2) → ℂ :=
  Fin.cases cy (Fin.cases cz c)

@[simp] theorem center_Y {m : ℕ} (cy cz : ℂ) (c : Fin m → ℂ) : center cy cz c 0 = cy := rfl
@[simp] theorem center_Z {m : ℕ} (cy cz : ℂ) (c : Fin m → ℂ) : center cy cz c 1 = cz := rfl
@[simp] theorem center_aux {m : ℕ} (cy cz : ℂ) (c : Fin m → ℂ) (i : Fin m) :
    center cy cz c i.succ.succ = c i := rfl

variable {E : Type*} [Field E] [Algebra ℂ E] {m : ℕ}

section Local

variable (place : NormalizedPlace ℂ E)
  [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring place))]
  (x : Fin (m+2) → E) (cy cz : ℂ) (c : Fin m → ℂ)
  (hc : Centered x (center cy cz c) place)

def series : Fin (m+2) → PowerSeries ℂ :=
  fun i => DVRBranch.expansion ℂ (ring place)
    (PlaceCenteredBranch.lift place x (center cy cz c) hc i)

theorem series_const (i : Fin (m+2)) :
    PowerSeries.constantCoeff (series place x cy cz c hc i) = center cy cz c i := by
  simp only [series, DVRBranch.expansion_constantCoeff, PlaceCenteredBranch.lift_residue]

theorem series_eq_constant_iff (i : Fin (m+2)) (a : ℂ) :
    series place x cy cz c hc i = PowerSeries.C a ↔ x i = algebraMap ℂ E a := by
  constructor
  · intro he
    apply (PlaceCenteredBranch.lift_eq_algebraMap_iff place x (center cy cz c) hc i a).mp
    apply DVRBranch.expansion_injective ℂ (ring place)
    rw [AlgHom.commutes]
    exact he
  · intro he
    rw [series, (PlaceCenteredBranch.lift_eq_algebraMap_iff place x (center cy cz c) hc i a).mpr he,
      AlgHom.commutes]
    rfl

def coordinates (r : Fin m → ℂ) : Fin (m+2) → PowerSeries ℂ :=
  BranchEvaluation.coordinates cy cz c r (series place x cy cz c hc 0)
    (series place x cy cz c hc 1) (fun i => series place x cy cz c hc i.succ.succ)

theorem coordinates_centered (r : Fin m → ℂ) (hcy : cy ≠ 0) (hcz : cz ≠ 0) :
    ∀ i, PowerSeries.constantCoeff (coordinates place x cy cz c hc r i) = 0 :=
  BranchEvaluation.coordinates_centered cy cz hcy hcz c r _ _ _
    (series_const place x cy cz c hc 0) (series_const place x cy cz c hc 1)
    (fun i => series_const place x cy cz c hc i.succ.succ)

theorem coordinates_nonzero (r : Fin m → ℂ) (hcy : cy ≠ 0) (hcz : cz ≠ 0)
    (hnc : ∃ i, x i ≠ algebraMap ℂ E (center cy cz c i)) :
    ∃ i, coordinates place x cy cz c hc r i ≠ 0 := by
  apply BranchEvaluation.coordinates_nonzero cy cz hcy hcz c r
  obtain ⟨i, hi⟩ := hnc
  have hh : series place x cy cz c hc i ≠ PowerSeries.C (center cy cz c i) :=
    fun h => hi ((series_eq_constant_iff place x cy cz c hc i _).mp h)
  cases i using Fin.cases with
  | zero => exact Or.inl hh
  | succ j =>
    cases j using Fin.cases with
    | zero => exact Or.inr (Or.inl hh)
    | succ k => exact Or.inr (Or.inr ⟨k, hh⟩)

def contact (r : Fin m → ℂ) (hcy : cy ≠ 0) (hcz : cz ≠ 0)
    (hnc : ∃ i, x i ≠ algebraMap ℂ E (center cy cz c i)) (v : Fin (m+2) → ℚ) : ℚ :=
  BranchContact.contact v (coordinates place x cy cz c hc r)
    (coordinates_nonzero place x cy cz c hc r hcy hcz hnc)

theorem contact_pos (r : Fin m → ℂ) (hcy : cy ≠ 0) (hcz : cz ≠ 0)
    (hnc : ∃ i, x i ≠ algebraMap ℂ E (center cy cz c i))
    (v : Fin (m+2) → ℚ) (hv : ∀ i, 0 < v i) :
    0 < contact place x cy cz c hc r hcy hcz hnc v :=
  BranchContact.contact_pos v hv _ _ (coordinates_centered place x cy cz c hc r hcy hcz)

theorem word_field_order_lower (r : Fin m → ℂ) (hcy : cy ≠ 0) (hcz : cz ≠ 0)
    (hnc : ∃ i, x i ≠ algebraMap ℂ E (center cy cz c i))
    (v : Fin (m+2) → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ) (P : Poly m)
    (hP : FormalJet.formalJet cy cz c r P ∈
      JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) H)
    (indices : List (Fin (m+2))) (hne : MvPolynomial.aeval x (word m r indices P) ≠ 0) :
    contact place x cy cz c hc r hcy hcz hnc v * (H - (indices.map v).sum) ≤
      (coordinateOrder place.valuation (MvPolynomial.aeval x (word m r indices P)) : ℚ) := by
  let xr := PlaceCenteredBranch.lift place x (center cy cz c) hc
  let s := series place x cy cz c hc
  have heval (F : Poly m) : DVRBranch.expansion ℂ (ring place) (MvPolynomial.aeval xr F) =
      MvPolynomial.aeval (Fin.cases (s 0) (Fin.cases (s 1) (fun i => s i.succ.succ))) F := by
    rw [OrdinaryDVRBranchJet.expansion_aeval]
    apply congrArg (fun f => MvPolynomial.aeval f F)
    funext i
    refine Fin.cases (by rfl) (fun j => ?_) i
    refine Fin.cases (by rfl) (fun k => by rfl) j
  have hn : MvPolynomial.aeval xr (word m r indices P) ≠ 0 := by
    intro hz
    apply hne
    rw [← PlaceCenteredBranch.lift_aeval place x (center cy cz c) hc, hz, map_zero]
  have hns : MvPolynomial.aeval
      (Fin.cases (s 0) (Fin.cases (s 1) (fun i => s i.succ.succ))) (word m r indices P) ≠ 0 := by
    rw [← heval]
    exact (map_ne_zero_iff _ (DVRBranch.expansion_injective ℂ (ring place))).mpr hn
  have hb := BranchEvaluation.word_order_toNat_lower cy cz hcy hcz c r
    (s 0) (s 1) (fun i => s i.succ.succ)
    (series_const place x cy cz c hc 0) (series_const place x cy cz c hc 1)
    (fun i => series_const place x cy cz c hc i.succ.succ)
    v (fun i => (hv i).le) (contact place x cy cz c hc r hcy hcz hnc v) H
    (contact_pos place x cy cz c hc r hcy hcz hnc v hv).le P hP
    (BranchContact.contact_bound v hv _ _) indices hns
  rw [← heval, DVRBranch.expansion_order_eq_length ℂ (ring place) hn] at hb
  rw [PlaceCenteredBranch.coordinateOrder_aeval_eq_length place x (center cy cz c) hc _ hne]
  simpa only [Int.cast_natCast] using hb

theorem first_coordinate_order_lower (r : Fin m → ℂ) (hcy : cy ≠ 0) (hcz : cz ≠ 0)
    (hnc : ∃ i, x i ≠ algebraMap ℂ E (center cy cz c i))
    (v : Fin (m+2) → ℚ) (hv : ∀ i, 0 < v i)
    (hne : x 0 - algebraMap ℂ E cy ≠ 0) :
    v 0 * contact place x cy cz c hc r hcy hcz hnc v ≤
      (coordinateOrder place.valuation (x 0 - algebraMap ℂ E cy) : ℚ) := by
  let F : Poly m := MvPolynomial.X 0 - MvPolynomial.C cy
  have hF : FormalJet.formalJet cy cz c r F ∈
      JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) (v 0) := by
    have he : FormalJet.formalJet cy cz c r F =
        MvPowerSeries.C cy * MvPowerSeries.X 0 := by
      simp only [F, map_sub, FormalJet.formalJet_Y, FormalJet.formalJet_C]
      ring
    rw [he]
    exact (JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) (v 0)).mul_mem_left _
      (CoordinateContactBound.X_mem_rationalWeightedIdeal v (fun i => (hv i).le) 0)
  have heval : MvPolynomial.aeval x F = x 0 - algebraMap ℂ E cy := by simp [F]
  have h := word_field_order_lower place x cy cz c hc r hcy hcz hnc v hv (v 0) F hF []
    (by simpa only [word, List.foldr_nil, heval] using hne)
  simpa only [List.map_nil, List.sum_nil, sub_zero, word, List.foldr_nil, heval, mul_comm] using h

end Local

theorem primitive_character_contact_sum
    (hres : ∀ place : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring place)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : Fin (m+2) → E) (cy cz : ℂ) (c r : Fin m → ℂ)
    (hcy : cy ≠ 0) (hcz : cz ≠ 0)
    (hnc : ∃ i, x i ≠ algebraMap ℂ E (center cy cz c i))
    (w v : Fin (m+2) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (hy : Transcendental ℂ (x 0)) (hz : x 1 ≠ 0)
    (a : ℂ) (ha : a ≠ 0) (p q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime q p)
    (hrel : (x 1)^q = algebraMap ℂ E a * (x 0)^p)
    (S : Finset (NormalizedPlace ℂ E)) (hc : ∀ place ∈ S, Centered x (center cy cz c) place)
    (mu : NormalizedPlace ℂ E → ℝ)
    (hmu : ∀ place (hp : place ∈ S), letI := hres place;
      mu place = (contact place x cy cz c (hc place hp) r hcy hcz hnc v : ℝ)) :
    ((q : ℝ) * (v 0 : ℝ)) * (∑ place ∈ S, mu place) ≤
      (w 0 : ℝ) * weightedDegree hfinite x w := by
  apply ParameterCenters.contact_sum_primitive_character hfinite x w hw 0 1 hy hz
    cy cz a hcy hcz ha p q hq hcop hrel S (fun place _ => hres place)
    (fun place hp => hc place hp 0) (fun place hp => hc place hp 1) mu (v 0 : ℝ)
  intro place hp
  let := hres place
  rw [hmu place hp]
  exact_mod_cast first_coordinate_order_lower place x cy cz c (hc place hp) r hcy hcz hnc v hv
    (by intro h; exact hy ((sub_eq_zero.mp h).symm ▸ isAlgebraic_algebraMap _))

#print axioms word_field_order_lower
#print axioms primitive_character_contact_sum

end LogarithmExtension.LogRatio.PlaceContact

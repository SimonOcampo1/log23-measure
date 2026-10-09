import LogarithmExtension.LogRatioPlaceContact

/-! The finite family of actual two-base contacts at (2^j,3^j,0,...,0). -/

noncomputable section
namespace LogarithmExtension.LogRatio.ContactFamily

open OAI.PiExponent CurveCenters CurveValuationCenter PlaceValuationRing
open PolynomialFrame

variable {E : Type*} [Field E] [Algebra ℂ E] {m : ℕ}

def places
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : Fin (m+2) → E) (hx : ∃ i, Transcendental ℂ (x i)) (K : ℕ) :
    Finset (NormalizedPlace ℂ E) :=
  centerPlaces x (fun j : Fin K => CurveRelations.center m j.val) hx hfinite

theorem mem_places
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : Fin (m+2) → E) (hx : ∃ i, Transcendental ℂ (x i)) (K : ℕ)
    (place : NormalizedPlace ℂ E) :
    place ∈ places hfinite x hx K ↔ ∃ j : Fin K, Centered x (CurveRelations.center m j.val) place :=
  mem_centerPlaces x (fun j : Fin K => CurveRelations.center m j.val) hx hfinite place

def index
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : Fin (m+2) → E) (hx : ∃ i, Transcendental ℂ (x i)) (K : ℕ)
    (place : NormalizedPlace ℂ E) (hp : place ∈ places hfinite x hx K) : Fin K :=
  Classical.choose ((mem_places hfinite x hx K place).mp hp)

theorem centered
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : Fin (m+2) → E) (hx : ∃ i, Transcendental ℂ (x i)) (K : ℕ)
    (place : NormalizedPlace ℂ E) (hp : place ∈ places hfinite x hx K) :
    Centered x (CurveRelations.center m (index hfinite x hx K place hp).val) place :=
  Classical.choose_spec ((mem_places hfinite x hx K place).mp hp)

def contact
    (hres : ∀ place : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring place)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : Fin (m+2) → E) (hx : ∃ i, Transcendental ℂ (x i)) (K : ℕ)
    (r : Fin m → ℂ) (v : Fin (m+2) → ℚ) (place : NormalizedPlace ℂ E) : ℚ := by
  classical
  let := hres place
  exact if hp : place ∈ places hfinite x hx K then
    PlaceContact.contact place x
      (2^(index hfinite x hx K place hp).val) (3^(index hfinite x hx K place hp).val)
      (fun _ => 0) (centered hfinite x hx K place hp) r (by simp) (by simp)
      (Centered.exists_nonzero_difference x _ hx) v
  else 0

theorem contact_eq_of_index
    (hres : ∀ place : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring place)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : Fin (m+2) → E) (hx : ∃ i, Transcendental ℂ (x i)) (K : ℕ)
    (r : Fin m → ℂ) (v : Fin (m+2) → ℚ) (place : NormalizedPlace ℂ E)
    (hp : place ∈ places hfinite x hx K) (j : Fin K)
    (hj : index hfinite x hx K place hp = j)
    (hc : Centered x (CurveRelations.center m j.val) place)
    (hnc : ∃ i, x i ≠ algebraMap ℂ E (CurveRelations.center m j.val i)) :
    letI := hres place;
    contact hres hfinite x hx K r v place =
      PlaceContact.contact place x (2^j.val) (3^j.val) (fun _ => 0) hc r
        (by simp) (by simp) hnc v := by
  subst j
  simp only [contact, dite_eq_left hp]

theorem contact_pos
    (hres : ∀ place : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring place)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : Fin (m+2) → E) (hx : ∃ i, Transcendental ℂ (x i)) (K : ℕ)
    (r : Fin m → ℂ) (v : Fin (m+2) → ℚ) (hv : ∀ i, 0 < v i)
    (place : NormalizedPlace ℂ E) (hp : place ∈ places hfinite x hx K) :
    0 < contact hres hfinite x hx K r v place := by
  let := hres place
  simpa only [contact, dite_eq_left hp] using
    PlaceContact.contact_pos place x
      (2^(index hfinite x hx K place hp).val) (3^(index hfinite x hx K place hp).val)
      (fun _ => 0) (centered hfinite x hx K place hp) r (by simp) (by simp)
      (Centered.exists_nonzero_difference x _ hx) v hv

theorem contact_nonneg
    (hres : ∀ place : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring place)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : Fin (m+2) → E) (hx : ∃ i, Transcendental ℂ (x i)) (K : ℕ)
    (r : Fin m → ℂ) (v : Fin (m+2) → ℚ) (hv : ∀ i, 0 < v i)
    (place : NormalizedPlace ℂ E) : 0 ≤ contact hres hfinite x hx K r v place := by
  by_cases hp : place ∈ places hfinite x hx K
  · exact (contact_pos hres hfinite x hx K r v hv place hp).le
  · simp only [contact, dite_eq_right hp, le_refl]

theorem word_order_lower
    (hres : ∀ place : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring place)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : Fin (m+2) → E) (hx : ∃ i, Transcendental ℂ (x i)) (K : ℕ)
    (r : Fin m → ℂ) (v : Fin (m+2) → ℚ) (hv : ∀ i, 0 < v i)
    (H : ℚ) (F : Poly m)
    (hF : ∀ j : Fin K, FormalJet.formalJet (2^j.val) (3^j.val) (fun _ => 0) r F ∈
      JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) H)
    (indices : List (Fin (m+2))) (hne : MvPolynomial.aeval x (word m r indices F) ≠ 0)
    (place : NormalizedPlace ℂ E) (hp : place ∈ places hfinite x hx K) :
    contact hres hfinite x hx K r v place * (H - (indices.map v).sum) ≤
      (WeightedPolynomialPole.coordinateOrder place.valuation
        (MvPolynomial.aeval x (word m r indices F)) : ℚ) := by
  let := hres place
  have h := PlaceContact.word_field_order_lower place x
    (2^(index hfinite x hx K place hp).val) (3^(index hfinite x hx K place hp).val)
    (fun _ => 0) (centered hfinite x hx K place hp) r (by simp) (by simp)
    (Centered.exists_nonzero_difference x _ hx) v hv H F (hF _) indices hne
  simpa only [contact, dite_eq_left hp] using h

#print axioms word_order_lower

end LogarithmExtension.LogRatio.ContactFamily

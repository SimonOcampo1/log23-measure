import LogarithmExtension.CoordinateScaling

/-! # Contact families with varying nonzero first coordinates -/

noncomputable section
namespace LogarithmExtension.CurveContactFamily

open OAI OAI.PiExponent OAI.PiExponentApprox
open CurveCenters CurveValuationCenter PlaceValuationRing

variable {E : Type*} [Field E] [Algebra ℂ E] {m K : ℕ}

def places
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) : Finset (NormalizedPlace ℂ E) :=
  centerPlaces z (fun j => Fin.cases (y j) (c j)) hz hfinite

theorem mem_places
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) (p : NormalizedPlace ℂ E) :
    p ∈ places hfinite z y c hz ↔ ∃ j : Fin K, Centered z (Fin.cases (y j) (c j)) p := by
  simp only [places, mem_centerPlaces]

def center
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i))
    (p : NormalizedPlace ℂ E) (hp : p ∈ places hfinite z y c hz) : Fin K :=
  Classical.choose ((mem_places hfinite z y c hz p).mp hp)

theorem centered
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i))
    (p : NormalizedPlace ℂ E) (hp : p ∈ places hfinite z y c hz) :
    Centered z (Fin.cases (y (center hfinite z y c hz p hp))
      (c (center hfinite z y c hz p hp))) p :=
  Classical.choose_spec ((mem_places hfinite z y c hz p).mp hp)

def contact
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (hy : ∀ j, y j ≠ 0)
    (c : Fin K → Fin m → ℂ) (hz : ∃ i, Transcendental ℂ (z i))
    (v : Fin (m+1) → ℚ) (p : NormalizedPlace ℂ E) : ℚ := by
  classical
  let := hres p
  exact if hp : p ∈ places hfinite z y c hz then
    CoordinateScaling.contact p (y (center hfinite z y c hz p hp)) (hy _) z
      (c (center hfinite z y c hz p hp)) (centered hfinite z y c hz p hp)
      (Centered.exists_nonzero_difference z _ hz) v
  else 0

theorem contact_pos
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (hy : ∀ j, y j ≠ 0)
    (c : Fin K → Fin m → ℂ) (hz : ∃ i, Transcendental ℂ (z i))
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (p : NormalizedPlace ℂ E) (hp : p ∈ places hfinite z y c hz) :
    0 < contact hres hfinite z y hy c hz v p := by
  let := hres p
  simpa only [contact, dite_eq_left hp] using
    CoordinateScaling.contact_pos p (y (center hfinite z y c hz p hp)) (hy _) z
      (c (center hfinite z y c hz p hp)) (centered hfinite z y c hz p hp)
      (Centered.exists_nonzero_difference z _ hz) v hv

theorem contact_nonneg
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (hy : ∀ j, y j ≠ 0)
    (c : Fin K → Fin m → ℂ) (hz : ∃ i, Transcendental ℂ (z i))
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) (p : NormalizedPlace ℂ E) :
    0 ≤ contact hres hfinite z y hy c hz v p := by
  by_cases hp : p ∈ places hfinite z y c hz
  · exact (contact_pos hres hfinite z y hy c hz v hv p hp).le
  · simp only [contact, dite_eq_right hp, le_refl]

theorem logWord_order_lower
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (hy : ∀ j, y j ≠ 0)
    (c : Fin K → Fin m → ℂ) (hz : ∃ i, Transcendental ℂ (z i))
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (H : ℚ) (F : FramePolynomial m)
    (hF : ∀ j, NormalizedLogJet.formalJet (y j) (c j) F ∈
      JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) H)
    (word : List (Fin (m+1)))
    (hne : MvPolynomial.aeval z (polynomialFrameWord m word F) ≠ 0)
    (p : NormalizedPlace ℂ E) (hp : p ∈ places hfinite z y c hz) :
    contact hres hfinite z y hy c hz v p * (H - (word.map v).sum) ≤
      (WeightedPolynomialPole.coordinateOrder p.valuation
        (MvPolynomial.aeval z (polynomialFrameWord m word F)) : ℚ) := by
  let := hres p
  have h := CoordinateScaling.word_order_lower p (y (center hfinite z y c hz p hp))
    (hy _) z (c (center hfinite z y c hz p hp)) (centered hfinite z y c hz p hp)
    (Centered.exists_nonzero_difference z _ hz) v hv H F (hF _) word hne
  simpa only [contact, dite_eq_left hp] using h

#print axioms logWord_order_lower

end LogarithmExtension.CurveContactFamily

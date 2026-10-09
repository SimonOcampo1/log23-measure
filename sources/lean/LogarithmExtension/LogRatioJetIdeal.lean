import LogarithmExtension.LogRatioContactLength
import LogarithmExtension.CompactNormalizedJetIdeal
import OAI.NumberTheory.PiExponent.Jets.JetProductLocalization

/-!
# Finite-center two-base ideals and their compactification

The product ideal is constructed from the actual two-base polynomial
coordinates. Its support, localization at each center, branch colength,
and extension to a projective compactification are proved here. No support
or local-degree identity is supplied as an additional assumption.

Adapted portions of the pinned OpenAI ideal and localization interfaces
retain their Apache-2.0 attribution.
-/

noncomputable section
namespace LogarithmExtension.LogRatio.JetIdeal

open OAI OAI.PiExponent PolynomialFrame AlgebraicJet
open scoped BigOperators

variable {m : ℕ}

def polynomialIdeal {J : Type*} [Fintype J]
    (cy cz : J → ℂ) (c : J → Fin m → ℂ) (r : Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+2) → ℕ) : Ideal (Poly m) :=
  ∏ j, powerIdeal (cy j) (cz j) (c j) r (CompactJetPolynomial.logPolynomials T) e

def centerPoint (cy cz : ℂ) (c : Fin m → ℂ) : PrimeSpectrum (Poly m) :=
  ⟨WeightedBezout.pointIdeal (center cy cz c), inferInstance⟩

theorem zeroLocus_powerIdeal (cy cz : ℂ) (hcy : cy ≠ 0) (hcz : cz ≠ 0)
    (c r : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+2) → ℕ) (he : ∀ i, 0 < e i) :
    PrimeSpectrum.zeroLocus
      (powerIdeal cy cz c r (CompactJetPolynomial.logPolynomials T) e : Set _) =
        {centerPoint cy cz c} := by
  rw [← PrimeSpectrum.zeroLocus_radical, radical_powerIdeal cy cz hcy hcz c r _
    (CompactJetPolynomial.logPolynomials_eval_zero T) e he]
  exact PrimeSpectrum.zeroLocus_eq_singleton _

theorem zeroLocus_finset_prod {J : Type*} (s : Finset J)
    (cy cz : J → ℂ) (hcy : ∀ j, cy j ≠ 0) (hcz : ∀ j, cz j ≠ 0)
    (c : J → Fin m → ℂ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m+2) → ℕ) (he : ∀ i, 0 < e i) :
    PrimeSpectrum.zeroLocus
      (((∏ j ∈ s, powerIdeal (cy j) (cz j) (c j) r (CompactJetPolynomial.logPolynomials T) e) :
        Ideal (Poly m)) : Set _) =
      (fun j => centerPoint (cy j) (cz j) (c j)) '' (s : Set J) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj, PrimeSpectrum.zeroLocus_mul,
      zeroLocus_powerIdeal (cy j) (cz j) (hcy j) (hcz j) (c j) r T e he, ih]
    simp

theorem zeroLocus_polynomialIdeal {J : Type*} [Fintype J]
    (cy cz : J → ℂ) (hcy : ∀ j, cy j ≠ 0) (hcz : ∀ j, cz j ≠ 0)
    (c : J → Fin m → ℂ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m+2) → ℕ) (he : ∀ i, 0 < e i) :
    PrimeSpectrum.zeroLocus (polynomialIdeal cy cz c r T e : Set (Poly m)) =
      Set.range (fun j => centerPoint (cy j) (cz j) (c j)) := by
  simpa [polynomialIdeal] using zeroLocus_finset_prod Finset.univ cy cz hcy hcz c r T e he

theorem polynomialIdeal_pow_le {J : Type*} [Fintype J]
    (cy cz : J → ℂ) (c : J → Fin m → ℂ) (r : Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+2) → ℕ) (n : ℕ) (j : J) :
    polynomialIdeal cy cz c r T e ^ n ≤
      powerIdeal (cy j) (cz j) (c j) r (CompactJetPolynomial.logPolynomials T) e ^ n := by
  classical
  apply pow_le_pow_left'
  exact Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ j))

theorem formalJet_packet_zero_of_mem_pow {J : Type*} [Fintype J]
    (cy cz : J → ℂ) (hcy : ∀ j, cy j ≠ 0) (hcz : ∀ j, cz j ≠ 0)
    (c : J → Fin m → ℂ) (r : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+2) → ℕ)
    (v : Fin (m+2) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (hT0 : ∀ i, v i.succ.succ ≤ (T i : ℚ) * v 0)
    (hT1 : ∀ i, v i.succ.succ ≤ (T i : ℚ) * v 1)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ) (P : Poly m)
    (hP : P ∈ polynomialIdeal cy cz c r T e ^ n) (j : J) :
    JetGeometry.rationalCoefficientPacket v (n*R) (FormalJet.formalJet (cy j) (cz j) (c j) r P) =
      (fun _ => (0 : ℂ)) :=
  AlgebraicJet.formalJet_packet_zero_of_mem_pow (cy j) (cz j) (hcy j) (hcz j) (c j) r T e
    v hv hT0 hT1 R he n P (polynomialIdeal_pow_le cy cz c r T e n j hP)

section Local

variable {A : Type*} [CommRing A] [IsLocalRing A] [Algebra ℂ A]
  [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]

theorem map_powerIdeal_eq_top_of_residue_ne
    (cy cz : ℂ) (hcy : cy ≠ 0) (hcz : cz ≠ 0) (c r : Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+2) → ℕ) (he : ∀ i, 0 < e i)
    (x : Fin (m+2) → A)
    (hne : ¬ ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = center cy cz c i) :
    (powerIdeal cy cz c r (CompactJetPolynomial.logPolynomials T) e).map
      (MvPolynomial.aeval x).toRingHom = ⊤ := by
  classical
  obtain ⟨i, hi⟩ := not_forall.mp hne
  let P : Poly m := MvPolynomial.X i - MvPolynomial.C (center cy cz c i)
  have hP : P ∈ (powerIdeal cy cz c r (CompactJetPolynomial.logPolynomials T) e).radical := by
    rw [radical_powerIdeal cy cz hcy hcz c r _ (CompactJetPolynomial.logPolynomials_eval_zero T) e he]
    change MvPolynomial.aeval (center cy cz c) P = 0
    simp [P]
  obtain ⟨n, hn⟩ := hP
  have hu : IsUnit (MvPolynomial.aeval x P) := by
    apply (JetProductLocalization.residue_ne_zero_iff_isUnit _).mp
    simpa only [P, map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      CurveLocalOrder.residueAugmentation_algebraMap] using sub_ne_zero.mpr hi
  apply Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hn)
  simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow] using hu.pow n

theorem map_polynomialIdeal_eq_selected {J : Type*} [Fintype J]
    (cy cz : J → ℂ) (hcy : ∀ j, cy j ≠ 0) (hcz : ∀ j, cz j ≠ 0)
    (c : J → Fin m → ℂ) (r : Fin m → ℂ)
    (hcent : Function.Injective (fun j => center (cy j) (cz j) (c j)))
    (T : Fin m → ℕ) (e : Fin (m+2) → ℕ) (he : ∀ i, 0 < e i)
    (x : Fin (m+2) → A) (j : J)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = center (cy j) (cz j) (c j) i) :
    (polynomialIdeal cy cz c r T e).map (MvPolynomial.aeval x).toRingHom =
      (powerIdeal (cy j) (cz j) (c j) r (CompactJetPolynomial.logPolynomials T) e).map
        (MvPolynomial.aeval x).toRingHom := by
  classical
  unfold polynomialIdeal
  change Ideal.mapHom (MvPolynomial.aeval x).toRingHom _ = _
  rw [map_prod]
  apply Finset.prod_eq_single j
  · intro k _ hkj
    rw [Ideal.one_eq_top]
    apply map_powerIdeal_eq_top_of_residue_ne (cy k) (cz k) (hcy k) (hcz k) (c k) r T e he x
    intro hk
    apply hkj
    apply hcent
    funext i
    exact (hk i).symm.trans (hx i)
  · simp

theorem map_polynomialIdeal_eq_top_outside {J : Type*} [Fintype J]
    (cy cz : J → ℂ) (hcy : ∀ j, cy j ≠ 0) (hcz : ∀ j, cz j ≠ 0)
    (c : J → Fin m → ℂ) (r : Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+2) → ℕ) (he : ∀ i, 0 < e i)
    (x : Fin (m+2) → A)
    (hout : ¬ ∃ j, ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) =
      center (cy j) (cz j) (c j) i) :
    (polynomialIdeal cy cz c r T e).map (MvPolynomial.aeval x).toRingHom = ⊤ := by
  unfold polynomialIdeal
  change Ideal.mapHom (MvPolynomial.aeval x).toRingHom _ = _
  rw [map_prod, ← Ideal.one_eq_top]
  apply Finset.prod_eq_one
  intro j _
  rw [Ideal.one_eq_top]
  exact map_powerIdeal_eq_top_of_residue_ne (cy j) (cz j) (hcy j) (hcz j) (c j) r T e he x
    (fun h => hout ⟨j, h⟩)

end Local

open CurveValuationCenter PlaceValuationRing CurveCenters

theorem place_product_colength_eq_contact
    {E : Type*} [Field E] [Algebra ℂ E]
    (place : NormalizedPlace ℂ E)
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring place))]
    {J : Type*} [Fintype J]
    (cy cz : J → ℂ) (hcy : ∀ j, cy j ≠ 0) (hcz : ∀ j, cz j ≠ 0)
    (c : J → Fin m → ℂ) (r : Fin m → ℂ)
    (hcent : Function.Injective (fun j => center (cy j) (cz j) (c j)))
    (j : J) (x : Fin (m+2) → E) (hc : Centered x (PlaceContact.center (cy j) (cz j) (c j)) place)
    (hnc : ∃ i, x i ≠ algebraMap ℂ E (PlaceContact.center (cy j) (cz j) (c j) i))
    (v : Fin (m+2) → ℚ) (hv : ∀ i, 0 < v i)
    (T : Fin m → ℕ) (hT0 : ∀ i, v i.succ.succ < (T i : ℚ) * v 0)
    (hT1 : ∀ i, v i.succ.succ < (T i : ℚ) * v 1)
    (R : ℚ) (e : Fin (m+2) → ℕ) (hepos : ∀ i, 0 < e i)
    (he : ∀ i, v i * (e i : ℚ) = R) :
    ((Module.length (ring place) ((ring place) ⧸ (polynomialIdeal cy cz c r T e).map
      (MvPolynomial.aeval (PlaceCenteredBranch.lift place x
        (PlaceContact.center (cy j) (cz j) (c j)) hc)).toRingHom)).toNat : ℚ) =
      R * PlaceContact.contact place x (cy j) (cz j) (c j) hc r (hcy j) (hcz j) hnc v := by
  rw [map_polynomialIdeal_eq_selected cy cz hcy hcz c r hcent T e hepos _ j
    (PlaceCenteredBranch.lift_residue place x (PlaceContact.center (cy j) (cz j) (c j)) hc)]
  exact ContactLength.place_colength_eq_contact place x (cy j) (cz j) (hcy j) (hcz j)
    (c j) r hc hnc v hv T hT0 hT1 R e he

open CategoryTheory AlgebraicGeometry

abbrev affineSpace (m : ℕ) := CompactNormalizedJetIdeal.affineSpace (m+1)
abbrev base := CompactNormalizedJetIdeal.base
abbrev structureMap (m : ℕ) := CompactNormalizedJetIdeal.structureMap (m+1)

def point (cy cz : ℂ) (c : Fin m → ℂ) : base ⟶ affineSpace m :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (center cy cz c)).toRingHom)

theorem point_section (cy cz : ℂ) (c : Fin m → ℂ) :
    point cy cz c ≫ structureMap m = 𝟙 base := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap ℂ (Poly m)) ≫
      CommRingCat.ofHom (MvPolynomial.aeval (center cy cz c)).toRingHom =
      𝟙 (CommRingCat.of ℂ) := by
    ext a
    simp
  rw [h, Spec.map_id]

theorem range_point (cy cz : ℂ) (c : Fin m → ℂ) :
    Set.range (point cy cz c) = {centerPoint cy cz c} := by
  change Set.range (PrimeSpectrum.comap (MvPolynomial.aeval (center cy cz c)).toRingHom) = _
  rw [range_comap_of_surjective _ _ (by
    intro a
    exact ⟨MvPolynomial.C a, by simp⟩)]
  exact PrimeSpectrum.zeroLocus_eq_singleton (WeightedBezout.pointIdeal (center cy cz c))

def affineIdeal {J : Type*} [Fintype J]
    (cy cz : J → ℂ) (c : J → Fin m → ℂ) (r : Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+2) → ℕ) : (affineSpace m).IdealSheafData :=
  PiExponentSeshadri.IdealPullback.specIdeal (polynomialIdeal cy cz c r T e)

theorem support_affineIdeal {J : Type*} [Fintype J]
    (cy cz : J → ℂ) (hcy : ∀ j, cy j ≠ 0) (hcz : ∀ j, cz j ≠ 0)
    (c : J → Fin m → ℂ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m+2) → ℕ) (he : ∀ i, 0 < e i) :
    ((affineIdeal cy cz c r T e).support : Set (affineSpace m)) =
      ⋃ j, Set.range (point (cy j) (cz j) (c j)) := by
  rw [affineIdeal, CompactLogJetIdeal.support_specIdeal,
    zeroLocus_polynomialIdeal cy cz hcy hcz c r T e he]
  simp only [range_point]
  ext p
  constructor
  · rintro ⟨j, rfl⟩
    exact Set.mem_iUnion.mpr ⟨j, Set.mem_singleton _⟩
  · intro hp
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hp
    exact ⟨j, (Set.mem_singleton_iff.mp hj).symm⟩

def compactIdeal {J : Type*} [Fintype J]
    (cy cz : J → ℂ) (c : J → Fin m → ℂ) (r : Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+2) → ℕ) {X : Scheme} (j : affineSpace m ⟶ X) :
    X.IdealSheafData := CompactJetIdeal.extend (affineIdeal cy cz c r T e) j

theorem restrict_compactIdeal {J : Type*} [Fintype J]
    (cy cz : J → ℂ) (c : J → Fin m → ℂ) (r : Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+2) → ℕ)
    {X : Scheme} (j : affineSpace m ⟶ X) [IsOpenImmersion j] [QuasiCompact j] :
    (compactIdeal cy cz c r T e j).comap j = affineIdeal cy cz c r T e :=
  CompactJetIdeal.restrict_extend _ j

theorem support_compactIdeal {J : Type*} [Fintype J]
    (cy cz : J → ℂ) (hcy : ∀ j, cy j ≠ 0) (hcz : ∀ j, cz j ≠ 0)
    (c : J → Fin m → ℂ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m+2) → ℕ) (he : ∀ i, 0 < e i)
    {X : Scheme} (j : affineSpace m ⟶ X) [QuasiCompact j]
    (pi : X ⟶ base) [IsSeparated pi] (hpi : j ≫ pi = structureMap m) :
    ((compactIdeal cy cz c r T e j).support : Set X) =
      ⋃ a, Set.range (point (cy a) (cz a) (c a) ≫ j) := by
  rw [compactIdeal, CompactJetIdeal.support_extend (affineIdeal cy cz c r T e) j pi
    (fun a => point (cy a) (cz a) (c a)) (fun a => by
      rw [Category.assoc, hpi, point_section]) (support_affineIdeal cy cz hcy hcz c r T e he),
    support_affineIdeal cy cz hcy hcz c r T e he, Set.image_iUnion]
  congr 1
  funext a
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]

theorem compactIdeal_isFinitePresentation {J : Type*} [Fintype J]
    (cy cz : J → ℂ) (c : J → Fin m → ℂ) (r : Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+2) → ℕ)
    {X : Scheme} [IsLocallyNoetherian X] (j : affineSpace m ⟶ X) :
    (PiExponentSeshadri.IdealModule.closedModule (compactIdeal cy cz c r T e j)).IsFinitePresentation :=
  CompactJetIdeal.extend_isFinitePresentation _ j

#print axioms place_product_colength_eq_contact
#print axioms support_compactIdeal

end LogarithmExtension.LogRatio.JetIdeal

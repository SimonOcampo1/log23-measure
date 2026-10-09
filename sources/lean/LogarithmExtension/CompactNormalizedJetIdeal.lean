import LogarithmExtension.NormalizedJetIdeal
import OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal

/-!
# Compactified ideals at distinct nonunit logarithmic centres

The affine ideal is the actual normalized polynomial ideal, not an abstract
ideal with assumed support. Its extension to a compactification has exactly
the prescribed finite support and restricts back to that polynomial ideal.

Adapted from `OAI.PiExponent.CompactLogJetIdeal` (Apache-2.0); the first
coordinate of each centre is now arbitrary.
-/

noncomputable section
namespace LogarithmExtension.CompactNormalizedJetIdeal

open OAI OAI.PiExponent OAI.PiExponentApprox
open CategoryTheory AlgebraicGeometry
open NormalizedJetIdeal
open scoped BigOperators

variable {m : ℕ}

abbrev coordinateRing (m : ℕ) := FramePolynomial m
abbrev affineSpace (m : ℕ) := CompactLogJetIdeal.affineSpace m
abbrev base := CompactLogJetIdeal.base
abbrev structureMap (m : ℕ) := CompactLogJetIdeal.structureMap m

def point (y : ℂ) (c : Fin m → ℂ) : base ⟶ affineSpace m :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (center y c)).toRingHom)

theorem point_section (y : ℂ) (c : Fin m → ℂ) :
    point y c ≫ structureMap m = 𝟙 base := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap ℂ (coordinateRing m)) ≫
      CommRingCat.ofHom (MvPolynomial.aeval (center y c)).toRingHom =
      𝟙 (CommRingCat.of ℂ) := by
    ext a
    simp
  rw [h, Spec.map_id]

theorem range_point (y : ℂ) (c : Fin m → ℂ) :
    Set.range (point y c) = {centerPoint y c} := by
  change Set.range (PrimeSpectrum.comap (MvPolynomial.aeval (center y c)).toRingHom) = _
  rw [range_comap_of_surjective _ _ (by
    intro a
    exact ⟨MvPolynomial.C a, by simp⟩)]
  exact PrimeSpectrum.zeroLocus_eq_singleton (WeightedBezout.pointIdeal (center y c))

theorem zeroLocus_finset_prod {J : Type*} (s : Finset J)
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) :
    PrimeSpectrum.zeroLocus
      (((∏ j ∈ s, powerIdeal (y j) (c j) (CompactJetPolynomial.logPolynomials T) e) :
        Ideal (coordinateRing m)) : Set _) =
      (fun j => centerPoint (y j) (c j)) '' (s : Set J) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj, PrimeSpectrum.zeroLocus_mul,
      zeroLocus_powerIdeal (y j) (c j) _
        (CompactJetPolynomial.logPolynomials_eval_zero T) e he, ih]
    simp

theorem zeroLocus_polynomialIdeal {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) :
    PrimeSpectrum.zeroLocus (polynomialIdeal y c T e : Set (coordinateRing m)) =
      Set.range (fun j => centerPoint (y j) (c j)) := by
  simpa [polynomialIdeal] using zeroLocus_finset_prod Finset.univ y c T e he

def affineIdeal {J : Type*} [Fintype J] (y : J → ℂ) (c : J → Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) : (affineSpace m).IdealSheafData :=
  PiExponentSeshadri.IdealPullback.specIdeal (polynomialIdeal y c T e)

theorem support_affineIdeal {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) :
    ((affineIdeal y c T e).support : Set (affineSpace m)) =
      ⋃ j, Set.range (point (y j) (c j)) := by
  rw [affineIdeal, CompactLogJetIdeal.support_specIdeal, zeroLocus_polynomialIdeal y c T e he]
  simp only [range_point]
  ext p
  constructor
  · rintro ⟨j, rfl⟩
    exact Set.mem_iUnion.mpr ⟨j, Set.mem_singleton _⟩
  · intro hp
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hp
    exact ⟨j, (Set.mem_singleton_iff.mp hj).symm⟩

def compactIdeal {J : Type*} [Fintype J] (y : J → ℂ) (c : J → Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    {X : Scheme} (j : affineSpace m ⟶ X) : X.IdealSheafData :=
  CompactJetIdeal.extend (affineIdeal y c T e) j

theorem restrict_compactIdeal {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    {X : Scheme} (j : affineSpace m ⟶ X) [IsOpenImmersion j] [QuasiCompact j] :
    (compactIdeal y c T e j).comap j = affineIdeal y c T e :=
  CompactJetIdeal.restrict_extend _ j

theorem support_compactIdeal {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i)
    {X : Scheme} (j : affineSpace m ⟶ X) [QuasiCompact j]
    (π : X ⟶ base) [IsSeparated π] (hπ : j ≫ π = structureMap m) :
    ((compactIdeal y c T e j).support : Set X) =
      ⋃ a, Set.range (point (y a) (c a) ≫ j) := by
  rw [compactIdeal, CompactJetIdeal.support_extend (affineIdeal y c T e) j π
    (fun a => point (y a) (c a)) (fun a => by
      rw [Category.assoc, hπ, point_section]) (support_affineIdeal y c T e he),
    support_affineIdeal y c T e he, Set.image_iUnion]
  congr 1
  funext a
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]

theorem compactIdeal_isFinitePresentation {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    {X : Scheme} [IsLocallyNoetherian X] (j : affineSpace m ⟶ X) :
    (PiExponentSeshadri.IdealModule.closedModule (compactIdeal y c T e j)).IsFinitePresentation :=
  CompactJetIdeal.extend_isFinitePresentation _ j

end LogarithmExtension.CompactNormalizedJetIdeal

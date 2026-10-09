import LogarithmExtension.LogRatioJetIdeal

/-!
# Recovering an actual two-base branch from its scheme-theoretic center

This is the center-identification argument for the concrete two-base
coordinate ring. Adapted portions of the OpenAI and one-base logarithm
center-identification proofs retain their Apache-2.0 attribution.
-/

noncomputable section
namespace LogarithmExtension.LogRatio.CenterIdentification

open OAI OAI.PiExponent
open CategoryTheory AlgebraicGeometry
open CurveValuationCenter PlaceValuationRing PolynomialFrame

variable {E : Type} [Field E] [Algebra ℂ E]

theorem centered_of_closedPoint_eq {m : ℕ} (p : NormalizedPlace ℂ E)
    (z : Fin (m+2) → E) (cy cz : ℂ) (c : Fin m → ℂ)
    {X : Scheme} (j : JetIdeal.affineSpace m ⟶ X) [IsOpenImmersion j]
    (q : Spec (CommRingCat.of (ring p)) ⟶ X)
    (hgeneric : Spec.map (CommRingCat.ofHom (algebraMap (ring p) E)) ≫ q =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j)
    (hclosed : q (IsLocalRing.closedPoint (ring p)) =
      j (JetIdeal.centerPoint cy cz c)) :
    CurveCenters.Centered z (PlaceContact.center cy cz c) p := by
  have hr : Set.range q ⊆ Set.range j := by
    rintro _ ⟨a, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint a).map q.continuous).mem_open
      j.isOpenEmbedding.isOpen_range (hclosed ▸ Set.mem_range_self (JetIdeal.centerPoint cy cz c))
  let g := IsOpenImmersion.lift j q hr
  have hg : g ≫ j = q := IsOpenImmersion.lift_fac j q hr
  let φ : Poly m →+* ring p := (Spec.preimage g).hom
  have hgφ : Spec.map (CommRingCat.ofHom φ) = g := Spec.map_preimage g
  have hcomp : CommRingCat.ofHom φ ≫ CommRingCat.ofHom (algebraMap (ring p) E) =
      CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom := by
    apply Spec.map_injective
    rw [Spec.map_comp, hgφ]
    apply (cancel_mono j).mp
    rw [Category.assoc, hg]
    exact hgeneric
  have hgc : g (IsLocalRing.closedPoint (ring p)) = JetIdeal.centerPoint cy cz c := by
    apply j.isOpenEmbedding.injective
    change (g ≫ j) (IsLocalRing.closedPoint (ring p)) = _
    rw [hg, hclosed]
  have hcomap : PrimeSpectrum.comap φ (IsLocalRing.closedPoint (ring p)) =
      JetIdeal.centerPoint cy cz c := by
    change (Spec.map (CommRingCat.ofHom φ)) (IsLocalRing.closedPoint (ring p)) = _
    rw [hgφ, hgc]
  intro i
  let P : Poly m := MvPolynomial.X i - MvPolynomial.C (AlgebraicJet.center cy cz c i)
  have hmem : φ P ∈ IsLocalRing.maximalIdeal (ring p) := by
    change P ∈ (PrimeSpectrum.comap φ (IsLocalRing.closedPoint (ring p))).asIdeal
    rw [hcomap]
    change P ∈ WeightedBezout.pointIdeal (AlgebraicJet.center cy cz c)
    rw [WeightedBezout.mem_pointIdeal]
    simp [P]
  have hpos := p.valuation.toValuation.mem_maximalIdeal_iff.mp hmem
  have heval := congrArg
    (fun f : CommRingCat.of (Poly m) ⟶ CommRingCat.of E => f P) hcomp
  change algebraMap (ring p) E (φ P) = MvPolynomial.aeval z P at heval
  change 0 < p.valuation (algebraMap (ring p) E (φ P)) at hpos
  rw [heval] at hpos
  simpa [P, AlgebraicJet.center, PlaceContact.center] using hpos

#print axioms centered_of_closedPoint_eq

end LogarithmExtension.LogRatio.CenterIdentification

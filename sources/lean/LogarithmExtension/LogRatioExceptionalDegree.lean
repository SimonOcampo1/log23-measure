import LogarithmExtension.LogRatioJetIdeal
import LogarithmExtension.LogRatioContactFamily
import LogarithmExtension.LogRatioCenterIdentification
import OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree

/-!
# The degree of the two-base center ideal on a normalized curve

The actual finite-center ideal is generically nonzero. Its local length is
the actual logarithmic contact, and its divisor is supported precisely at
the finite family of centered places. This identifies the exceptional line
bundle degree needed by the curve-to-interpolation argument.

The generic divisor-degree infrastructure, and adapted portions of the
one-base exceptional-degree interface, retain their Apache-2.0 attribution.
No interpolation or ampleness hypothesis is used in these identities.
-/

noncomputable section
namespace LogarithmExtension.LogRatio.ExceptionalDegree

open OAI OAI.PiExponent
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open OAI.PiExponent.ExceptionalCurveDegree
open CurveNormalizationModel CurveValuationCenter CurvePlaceCenter
open PolynomialFrame
open scoped BigOperators

variable {X Y : Scheme.{0}} {m : ℕ}

theorem localIdeal_compactIdeal {A : Type} [CommRing A] {K : Type} [Fintype K]
    (cy cz : K → ℂ) (c : K → Fin m → ℂ) (r : Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+2) → ℕ)
    (j : JetIdeal.affineSpace m ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (φ : Poly m →+* A) :
    localIdeal (JetIdeal.compactIdeal cy cz c r T e j)
      (Spec.map (CommRingCat.ofHom φ) ≫ j) =
        (JetIdeal.polynomialIdeal cy cz c r T e).map φ := by
  unfold localIdeal
  rw [Scheme.IdealSheafData.comap_comp, JetIdeal.restrict_compactIdeal]
  exact localIdeal_specIdeal _ φ

variable {E : Type} [Field E] [Algebra ℂ E]

theorem map_powerIdeal_eq_top_of_transcendental
    (z : Fin (m+2) → E) (hz : ∃ i, Transcendental ℂ (z i))
    (cy cz : ℂ) (hcy : cy ≠ 0) (hcz : cz ≠ 0) (c r : Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+2) → ℕ) (he : ∀ i, 0 < e i) :
    (AlgebraicJet.powerIdeal cy cz c r (CompactJetPolynomial.logPolynomials T) e).map
      (MvPolynomial.aeval z).toRingHom = ⊤ := by
  obtain ⟨i, hi⟩ := hz
  let P : Poly m := MvPolynomial.X i - MvPolynomial.C (AlgebraicJet.center cy cz c i)
  have hP : P ∈ (AlgebraicJet.powerIdeal cy cz c r
      (CompactJetPolynomial.logPolynomials T) e).radical := by
    rw [AlgebraicJet.radical_powerIdeal cy cz hcy hcz c r _
      (CompactJetPolynomial.logPolynomials_eval_zero T) e he]
    change MvPolynomial.aeval (AlgebraicJet.center cy cz c) P = 0
    simp [P]
  obtain ⟨n, hn⟩ := hP
  have hne : MvPolynomial.aeval z P ≠ 0 := by
    intro h
    have heq : z i = algebraMap ℂ E (AlgebraicJet.center cy cz c i) := by
      simpa [P, sub_eq_zero] using h
    exact hi (heq ▸ isAlgebraic_algebraMap _)
  apply Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hn)
  simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow] using
    (isUnit_iff_ne_zero.mpr hne).pow n

variable (f : E) (hf : Transcendental ℂ f)
variable [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]

theorem compactIdeal_comap_ne_bot_of_generic {K : Type} [Fintype K]
    (cy cz : K → ℂ) (hcy : ∀ k, cy k ≠ 0) (hcz : ∀ k, cz k ≠ 0)
    (c : K → Fin m → ℂ) (r : Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+2) → ℕ) (he : ∀ i, 0 < e i)
    (j : JetIdeal.affineSpace m ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (g : parameterCurve f hf ⟶ X) (z : Fin (m+2) → E)
    (hz : ∃ i, Transcendental ℂ (z i))
    (hgeneric : parameterCurveGenericPoint f hf ≫ g =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j) :
    (JetIdeal.compactIdeal cy cz c r T e j).comap g ≠ ⊥ := by
  have htop : localIdeal (JetIdeal.compactIdeal cy cz c r T e j)
      (parameterCurveGenericPoint f hf ≫ g) = ⊤ := by
    rw [hgeneric, localIdeal_compactIdeal]
    unfold JetIdeal.polynomialIdeal
    change Ideal.mapHom (MvPolynomial.aeval z).toRingHom _ = _
    rw [map_prod]
    have ht : ∀ k : K, (AlgebraicJet.powerIdeal (cy k) (cz k) (c k) r
        (CompactJetPolynomial.logPolynomials T) e).map (MvPolynomial.aeval z).toRingHom = ⊤ :=
      fun k => map_powerIdeal_eq_top_of_transcendental z hz (cy k) (cz k)
        (hcy k) (hcz k) (c k) r T e he
    simp only [Ideal.mapHom_apply, ht]
    rw [← Ideal.one_eq_top]
    exact Finset.prod_const_one
  intro hzero
  have hb : localIdeal (JetIdeal.compactIdeal cy cz c r T e j)
      (parameterCurveGenericPoint f hf ≫ g) = ⊥ := by
    simp only [localIdeal, Scheme.IdealSheafData.comap_comp, hzero,
      Scheme.IdealSheafData.comap_bot]
    exact Ideal.map_bot
  exact bot_ne_top (hb.symm.trans htop)

theorem centerMorphism_eq_centeredLift [X.IsSeparated]
    (j : JetIdeal.affineSpace m ⟶ X)
    (g : parameterCurve f hf ⟶ X) (z : Fin (m+2) → E)
    (hgeneric : parameterCurveGenericPoint f hf ≫ g =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j)
    (p : NormalizedPlace ℂ E) (cy cz : ℂ) (c : Fin m → ℂ)
    (hc : CurveCenters.Centered z (PlaceContact.center cy cz c) p) :
    centerMorphism f hf p ≫ g =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.aeval (PlaceCenteredBranch.lift p z
          (PlaceContact.center cy cz c) hc)).toRingHom) ≫ j := by
  apply centerMorphism_comp_eq_of_generic f hf p g
  rw [hgeneric, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro P
  exact PlaceCenteredBranch.lift_aeval p z (PlaceContact.center cy cz c) hc P

theorem localIdeal_length_eq_contact [X.IsSeparated] {K : Type} [Fintype K]
    (cy cz : K → ℂ) (hcy : ∀ k, cy k ≠ 0) (hcz : ∀ k, cz k ≠ 0)
    (c : K → Fin m → ℂ) (r : Fin m → ℂ)
    (hcent : Function.Injective (fun k => AlgebraicJet.center (cy k) (cz k) (c k)))
    (T : Fin m → ℕ) (e : Fin (m+2) → ℕ) (hepos : ∀ i, 0 < e i)
    (v : Fin (m+2) → ℚ) (hv : ∀ i, 0 < v i)
    (R : ℚ) (he : ∀ i, v i * (e i : ℚ) = R)
    (hT0 : ∀ i, v i.succ.succ < (T i : ℚ) * v 0)
    (hT1 : ∀ i, v i.succ.succ < (T i : ℚ) * v 1)
    (j : JetIdeal.affineSpace m ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (g : parameterCurve f hf ⟶ X) (z : Fin (m+2) → E)
    (hz : ∃ i, Transcendental ℂ (z i))
    (hgeneric : parameterCurveGenericPoint f hf ≫ g =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j)
    (p : NormalizedPlace ℂ E)
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (PlaceValuationRing.ring p))]
    (k : K) (hc : CurveCenters.Centered z (PlaceContact.center (cy k) (cz k) (c k)) p) :
    ((Module.length (PlaceValuationRing.ring p)
      ((PlaceValuationRing.ring p) ⧸
        localIdeal (JetIdeal.compactIdeal cy cz c r T e j)
          (centerMorphism f hf p ≫ g))).toNat : ℚ) =
      R * PlaceContact.contact p z (cy k) (cz k) (c k) hc r (hcy k) (hcz k)
        (CurveCenters.Centered.exists_nonzero_difference z _ hz) v := by
  rw [centerMorphism_eq_centeredLift f hf j g z hgeneric p (cy k) (cz k) (c k) hc,
    localIdeal_compactIdeal]
  exact JetIdeal.place_product_colength_eq_contact p cy cz hcy hcz c r hcent k z hc
    (CurveCenters.Centered.exists_nonzero_difference z _ hz) v hv T hT0 hT1 R e hepos he

theorem centers_injective (m K : ℕ) : Function.Injective
    (fun k : Fin K => AlgebraicJet.center ((2 : ℂ)^k.val) ((3 : ℂ)^k.val)
      (fun _ : Fin m => 0)) := by
  intro k l h
  apply Fin.ext
  apply CurveRelations.center_character_injective m 0 1 (by decide)
  exact congrArg (fun a : Fin (m+2) → ℂ => a 1 ^ 1 / a 0 ^ 0) h

set_option maxHeartbeats 1200000 in
theorem compactIdeal_degree_eq_neg_contact_sum [X.IsSeparated] {K : ℕ}
    (r : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+2) → ℕ) (hepos : ∀ i, 0 < e i)
    (v : Fin (m+2) → ℚ) (hv : ∀ i, 0 < v i)
    (R : ℚ) (he : ∀ i, v i * (e i : ℚ) = R)
    (hT0 : ∀ i, v i.succ.succ < (T i : ℚ) * v 0)
    (hT1 : ∀ i, v i.succ.succ < (T i : ℚ) * v 1)
    (j : JetIdeal.affineSpace m ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (pX : X ⟶ Spec (CommRingCat.of ℂ)) [IsSeparated pX]
    (hj : j ≫ pX = JetIdeal.structureMap m)
    (π : Y ⟶ X) (J : LineBundle Y) (ι : J.sheaf ⟶ PiExponentSeshadri.Frames.O Y)
    (hJ : PresentsPullbackIdeal (JetIdeal.compactIdeal
      (fun k : Fin K => (2 : ℂ)^k.val) (fun k => (3 : ℂ)^k.val)
      (fun _ _ => 0) r T e j) π J ι)
    (g : parameterCurve f hf ⟶ Y) (z : Fin (m+2) → E)
    (hz : ∃ i, Transcendental ℂ (z i))
    (hgeneric : parameterCurveGenericPoint f hf ≫ g ≫ π =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j)
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (PlaceValuationRing.ring p)))
    (hfinite : ∀ t : E, Transcendental ℂ t →
      FiniteDimensional (IntermediateField.adjoin ℂ {t}) E) :
    ((eulerCharacteristic (parameterCurveStructureMap f hf) 1 (J.pullback g).sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) : ℤ) : ℚ) =
      -R * ∑ p ∈ ContactFamily.places hfinite z hz K,
        ContactFamily.contact hres hfinite z hz K r v p := by
  classical
  let cy : Fin K → ℂ := fun k => 2^k.val
  let cz : Fin K → ℂ := fun k => 3^k.val
  let c : Fin K → Fin m → ℂ := fun _ _ => 0
  have hcy : ∀ k, cy k ≠ 0 := by simp [cy]
  have hcz : ∀ k, cz k ≠ 0 := by simp [cz]
  let I := JetIdeal.compactIdeal cy cz c r T e j
  have hg : I.comap (g ≫ π) ≠ ⊥ :=
    compactIdeal_comap_ne_bot_of_generic f hf cy cz hcy hcz c r T e hepos
      j (g ≫ π) z hz hgeneric
  let D := idealDivisor f hf I π J ι hJ g hg
  let P := ContactFamily.places hfinite z hz K
  have hzero (p : NormalizedPlace ℂ E) (hp : p ∉ P) : D p = 0 := by
    have havoid : (centerMorphism f hf p ≫ g ≫ π)
        (IsLocalRing.closedPoint (PlaceValuationRing.ring p)) ∉ I.support := by
      intro hmem
      change _ ∈ ((JetIdeal.compactIdeal cy cz c r T e j).support : Set X) at hmem
      rw [JetIdeal.support_compactIdeal cy cz hcy hcz c r T e hepos j pX hj] at hmem
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hmem
      obtain ⟨a, ha⟩ := hk
      have hap : JetIdeal.point (cy k) (cz k) (c k) a =
          JetIdeal.centerPoint (cy k) (cz k) (c k) := by
        have h := Set.mem_range_self (f := JetIdeal.point (cy k) (cz k) (c k)) a
        rw [JetIdeal.range_point] at h
        exact h
      have hclosed : (centerMorphism f hf p ≫ g ≫ π)
          (IsLocalRing.closedPoint (PlaceValuationRing.ring p)) =
          j (JetIdeal.centerPoint (cy k) (cz k) (c k)) :=
        ha.symm.trans (congrArg j hap)
      have hfield : Spec.map (CommRingCat.ofHom
          (algebraMap (PlaceValuationRing.ring p) E)) ≫
          (centerMorphism f hf p ≫ g ≫ π) =
          Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j := by
        rw [← Category.assoc, centerMorphism_generic]
        exact hgeneric
      apply hp
      apply (ContactFamily.mem_places hfinite z hz K p).mpr
      refine ⟨k, ?_⟩
      exact CenterIdentification.centered_of_closedPoint_eq p z (cy k) (cz k)
        (c k) j (centerMorphism f hf p ≫ g ≫ π) hfield hclosed
    change idealDivisor f hf I π J ι hJ g hg p = 0
    rw [idealDivisor_apply, localIdeal_eq_top_of_not_mem I _ havoid]
    simp
  have hsupport : D.support ⊆ P := by
    intro p hp
    by_contra h
    exact (Finsupp.mem_support_iff.mp hp) (hzero p h)
  have hvalue (p : NormalizedPlace ℂ E) (hp : p ∈ P) :
      (D p : ℚ) = R * ContactFamily.contact hres hfinite z hz K r v p := by
    let := hres p
    have hp' : p ∈ ContactFamily.places hfinite z hz K := hp
    let k := ContactFamily.index hfinite z hz K p hp
    have hcenter := ContactFamily.centered hfinite z hz K p hp
    have h := localIdeal_length_eq_contact f hf cy cz hcy hcz c r (centers_injective m K)
      T e hepos v hv R he hT0 hT1 j (g ≫ π) z hz hgeneric p k hcenter
    change (idealDivisor f hf I π J ι hJ g hg p : ℚ) = _
    rw [idealDivisor_apply]
    simpa only [ContactFamily.contact, dite_eq_left hp', I, k, cy, cz, c] using h
  have hsum : D.sum (fun _ n => (n : ℚ)) =
      R * ∑ p ∈ P, ContactFamily.contact hres hfinite z hz K r v p := by
    rw [D.sum_of_support_subset hsupport (fun _ n => (n : ℚ)) (by simp)]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p hp => hvalue p hp)
  have hd := degree_eq_neg_idealDivisor_sum f hf I π J ι hJ g hg
  have hdq : ((eulerCharacteristic (parameterCurveStructureMap f hf) 1 (J.pullback g).sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) : ℤ) : ℚ) =
      -D.sum (fun _ n => (n : ℚ)) := by
    simpa only [Int.cast_neg, Finsupp.sum, Int.cast_sum, Int.cast_natCast] using
      congrArg (fun a : ℤ => (a : ℚ)) hd
  rw [hsum] at hdq
  simpa only [neg_mul, P] using hdq

#print axioms localIdeal_length_eq_contact
#print axioms compactIdeal_degree_eq_neg_contact_sum

end LogarithmExtension.LogRatio.ExceptionalDegree

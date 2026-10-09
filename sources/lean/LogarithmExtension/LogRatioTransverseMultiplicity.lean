import LogarithmExtension.LogRatioResidueDirections
import OAI.NumberTheory.PiExponent.Jets.TaylorRectangular
import OAI.NumberTheory.PiExponent.Jets.PrimeTaylorCotangent

/-!
# Transverse multiplicity for the actual two-base frame

This adapts the Taylor/localization argument of the pinned Apache-2.0 OpenAI
modules `TaylorRectangular`, `FrameTransverseMultiplicity`, and
`PrimeFrameMultiplicity` to the two-base derivatives defined here. The
generic cotangent and local-length theorems are reused, with their hypotheses
proved for these operators. No multiplicity or interpolation assertion is
introduced as an axiom.
-/

noncomputable section
namespace LogarithmExtension.LogRatio.TransverseMultiplicity

open scoped BigOperators
open OAI.PiExponent OAI.PiExponentApprox
open OAI.PiExponent.CommutingTaylor OAI.PiExponent.TaylorRectangular
open OAI.PiExponent.DerivativeIdeals
open OAI.PiExponentApprox.TransverseMultiplicity
open PolynomialFrame

def rationalFrame (m : ℕ) (r : Fin m → ℂ) (i : Fin (m + 2)) :
    Derivation ℚ (Poly m) (Poly m) :=
  (frame m r i).restrictScalars ℚ

@[simp] theorem rationalFrame_apply (m : ℕ) (r : Fin m → ℂ)
    (i : Fin (m + 2)) (a : Poly m) :
    rationalFrame m r i a = frame m r i a := rfl

theorem word_append (m : ℕ) (r : Fin m → ℂ)
    (u v : List (Fin (m + 2))) (a : Poly m) :
    word m r (u ++ v) a = word m r u (word m r v a) := by
  simp [word, List.foldr_append]

theorem word_replicate (m : ℕ) (r : Fin m → ℂ)
    (i : Fin (m + 2)) (n : ℕ) (a : Poly m) :
    word m r (List.replicate n i) a = iter (rationalFrame m r i) n a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, show word m r (i :: List.replicate n i) a =
      frame m r i (word m r (List.replicate n i) a) from rfl, ih, iter_succ]
    rfl

theorem mixedIter_eq_word (m k : ℕ) (r : Fin m → ℂ)
    (B : Fin k → Fin (m + 2)) (α : Fin k →₀ ℕ) (a : Poly m) :
    mixedIter k (fun i => rationalFrame m r (B i)) α a =
      word m r (derivativeWord k B α) a := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    simp only [mixedIter, LinearMap.comp_apply, derivativeWord, word_append,
      word_replicate]
    exact ih (fun i => B i.succ) α.tail _

theorem residueTaylor_ideal_le {K : Type*} [Field K] [Algebra ℚ K]
    (m k : ℕ) (r : Fin m → ℂ) (B : Fin k → Fin (m + 2))
    (ρ : Poly m →+* K) (I : Ideal (Poly m))
    (cost : Fin (m + 2) → ℝ) (n : Fin k → ℕ) (δ : ℝ)
    (hcost : ∀ i, 0 ≤ cost i)
    (hn : ∑ i, ((n i - 1 : ℕ) : ℝ) * cost (B i) ≤ δ)
    (hvanish : ∀ a ∈ I, ∀ indices : List (Fin (m + 2)),
      wordCost cost indices ≤ δ → ρ (word m r indices a) = 0) :
    I ≤ (rectangularIdeal n).comap
      (residueTaylorFin k (fun i => rationalFrame m r (B i)) ρ) := by
  intro a ha
  apply residueTaylor_mem_rectangular
  intro α hα
  rw [mixedIter_eq_word]
  apply hvanish a ha
  exact derivativeWord_cost_le (m + 1) k B α cost n δ hcost hα hn

/-- A rectangle of independent normal derivatives forces its full cardinality
as a lower bound on the localized intersection length. -/
theorem prime_rectangular_length_lower (m k : ℕ) (r : Fin m → ℂ)
    (Q : Ideal (Poly m)) [Q.IsPrime]
    (hy : primeResidueMap Q (MvPolynomial.X 0) ≠ 0)
    (hz : primeResidueMap Q (MvPolynomial.X 1) ≠ 0)
    (B : Fin k → Fin (m + 2))
    (hB : LinearIndependent Q.ResidueField
      (fun j => (polynomialTangent (primeResidueMap Q) Q).mkQ
        (TwoBaseFrame.frameBasis m
          (primeResidueMap Q (MvPolynomial.X 0))
          (primeResidueMap Q (MvPolynomial.X 1)) hy hz
          (fun i => primeResidueMap Q (MvPolynomial.C (r i))) (B j))))
    (I : Ideal (Poly m)) (cost : Fin (m + 2) → ℝ)
    (n : Fin k → ℕ) (delta : ℝ) (hn : ∀ i, 2 ≤ n i)
    (hcost : ∀ i, 0 ≤ cost i)
    (hbudget : ∑ i, ((n i - 1 : ℕ) : ℝ) * cost (B i) ≤ delta)
    (hvanish : ∀ p ∈ I, ∀ indices : List (Fin (m + 2)),
      wordCost cost indices ≤ delta → word m r indices p ∈ Q) :
    (∏ i, n i : ℕ) ≤
      Module.length (Localization.AtPrime Q)
        (Localization.AtPrime Q ⧸ I.map
          (algebraMap (Poly m) (Localization.AtPrime Q))) := by
  let rho := algebraMap (Localization.AtPrime Q) Q.ResidueField
  let tau0 := residueTaylorFin k (fun i => rationalFrame m r (B i))
    (rho.comp (algebraMap (Poly m) (Localization.AtPrime Q)))
  have hconstant : ∀ a, MvPowerSeries.constantCoeff (tau0 a) =
      rho (algebraMap (Poly m) (Localization.AtPrime Q) a) :=
    fun a => constantCoeff_residueTaylorFin _ _ _ a
  let tau := localizedTaylorMap Q.primeCompl tau0 rho hconstant
  have hzero : ∀ x, MvPowerSeries.constantCoeff (tau x) = rho x :=
    fun x => RingHom.congr_fun
      (localizedTaylorMap_constant Q.primeCompl tau0 rho hconstant) x
  let v := fun j => TwoBaseFrame.frameBasis m
    (primeResidueMap Q (MvPolynomial.X 0))
    (primeResidueMap Q (MvPolynomial.X 1)) hy hz
    (fun i => primeResidueMap Q (MvPolynomial.C (r i))) (B j)
  have hfirst : ∀ j x, MvPowerSeries.coeff (Finsupp.single j 1) (tau x) =
      primeLocalDirectional Q (v j) x := by
    intro j x
    apply prime_localizedTaylor_firstCoefficient Q tau0 hconstant v
    intro l p
    rw [coeff_single_residueTaylorFin]
    change rho (algebraMap (Poly m) (Localization.AtPrime Q) (frame m r (B l) p)) = _
    dsimp only [rho]
    rw [← IsScalarTower.algebraMap_apply]
    exact ResidueDirections.frame_eq_basis_dot m r (primeResidueMap Q).toRingHom
      hy hz (B l) p
  have hCot := prime_rectangular_mapCotangent_surjective Q tau hzero v hB hfirst n hn
  have hP : IsLocalRing.maximalIdeal (Localization.AtPrime Q) ≤ RingHom.ker rho := by
    rw [show RingHom.ker rho = IsLocalRing.maximalIdeal (Localization.AtPrime Q)
      from IsLocalRing.ker_residue]
  apply rectangularTaylor_length_lower n (rectangularPositive n hn) tau rho
    IsLocalRing.residue_surjective hzero
    (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) _ hP hCot
  apply localizedTaylorMap_ideal_le Q.primeCompl tau0 rho hconstant
  apply residueTaylor_ideal_le m k r B _ I cost n delta hcost hbudget
  intro p hp indices hindices
  change rho (algebraMap (Poly m) (Localization.AtPrime Q) (word m r indices p)) = 0
  dsimp only [rho]
  rw [← IsScalarTower.algebraMap_apply]
  exact Ideal.algebraMap_residueField_eq_zero.mpr (hvanish p hp indices hindices)

#print axioms prime_rectangular_length_lower

end LogarithmExtension.LogRatio.TransverseMultiplicity

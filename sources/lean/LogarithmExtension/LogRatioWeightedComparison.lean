import LogarithmExtension.LogRatioTransverseMultiplicity
import OAI.NumberTheory.PiExponent.Jets.NormalBasisProducts
import OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeWeightedBezout

/-!
# Sharp weighted comparison for the two-base derivative frame

The lower multiplicity bound is proved for the actual two-base operators.
Combining it with the generic weighted Bezout theorem gives the sharp
dimension-sensitive factor k^k, needed when the normal space is supported
on the two base coordinates. The argument adapts `TransverseSliceComparison`
from the pinned Apache-2.0 OpenAI development.
-/

noncomputable section
namespace LogarithmExtension.LogRatio.WeightedComparison

open scoped BigOperators
open OAI.PiExponent OAI.PiExponentApprox
open NormalBasisRigidity NormalBasisProducts TransverseWeightedMultiplicity
open OAI.PiExponent.DerivativeIdeals
open PolynomialFrame

theorem comparison_of_normal_basis {m : ℕ} (r : Fin m → ℂ)
    (Q : Ideal (Poly m)) [Q.IsPrime]
    (hy : primeResidueMap Q (MvPolynomial.X 0) ≠ 0)
    (hz : primeResidueMap Q (MvPolynomial.X 1) ≠ 0)
    (A : Finset (Fin (m + 2))) (hk : 0 < A.card)
    (hA : IsNormalBasis (K := Q.ResidueField)
      (fun i => (polynomialTangent (primeResidueMap Q) Q).mkQ
        (Pi.basisFun Q.ResidueField _ i)) A)
    (B : Fin A.card → Fin (m + 2))
    (hB : LinearIndependent Q.ResidueField
      (fun j => (polynomialTangent (primeResidueMap Q) Q).mkQ
        (TwoBaseFrame.frameBasis m
          (primeResidueMap Q (MvPolynomial.X 0))
          (primeResidueMap Q (MvPolynomial.X 1)) hy hz
          (fun i => primeResidueMap Q (MvPolynomial.C (r i))) (B j))))
    {J : Type*} (f : J → Poly m)
    (hQ : Q ∈ (Ideal.span (Set.range f)).minimalPrimes)
    (rho : Fin (m + 2) → ℚ) (hrho : ∀ i, 0 < rho i)
    (cost : Fin (m + 2) → ℝ) (hcost : ∀ i, 0 < cost i)
    (epsilon N : ℝ) (hepsilon : 0 < epsilon) (hN : 0 < N)
    (hdegree : ∀ j, ∀ d ∈ (f j).support,
      (∑ i ∈ d.support, (d i : ℝ) * (rho i : ℝ)) ≤ N)
    (hn : ∀ i, 2 ≤ rectangularCutoff (fun j => cost (B j)) (epsilon * N) i)
    (hvanish : ∀ p ∈ Ideal.span (Set.range f), ∀ indices : List (Fin (m + 2)),
      wordCost cost indices ≤ epsilon * N → word m r indices p ∈ Q) :
    (∏ i ∈ A, (rho i : ℝ)) ≤
      (A.card : ℝ) ^ A.card * (∏ i, cost (B i)) / epsilon ^ A.card := by
  obtain ⟨L, hL, hupper⟩ := PrimeWeightedBezout.weighted_prime_length_bound
    Q A hA f hQ rho hrho N hN.le hdegree
  have hlower := TransverseMultiplicity.prime_rectangular_length_lower m A.card r Q
    hy hz B hB (Ideal.span (Set.range f)) cost
    (rectangularCutoff (fun j => cost (B j)) (epsilon * N)) (epsilon * N) hn
    (fun i => (hcost i).le)
    (rectangularCutoff_budget hk (fun j => cost (B j)) (fun j => hcost _)
      (epsilon * N) (mul_pos hepsilon hN)) hvanish
  change (∏ i, rectangularCutoff (fun j => cost (B j)) (epsilon * N) i : ℕ) ≤
    CoordinateSliceComparison.primeLength Q (Ideal.span (Set.range f)) at hlower
  rw [hL] at hlower
  have hrhoR (i : Fin (m + 2)) : (0 : ℝ) < rho i := by exact_mod_cast hrho i
  have h := weight_comparison_of_rectangular_count hk
    (fun i => (rho (A.equivFin.symm i) : ℝ)) (fun j => cost (B j)) epsilon N L
    (fun i => hrhoR _) (fun j => hcost _) hepsilon hN (by exact_mod_cast hlower)
    (by simpa only [prod_equivFin A (fun i => (rho i : ℝ))] using hupper)
  simpa only [prod_equivFin A (fun i => (rho i : ℝ))] using h

/-- The comparison required by the rigidity theorem, simultaneously for every
pair of normal bases. Its size condition is explicit and uniform in the prime
and the normal bases, and is satisfied once N is sufficiently large. -/
theorem comparison_of_normal_bases {m : ℕ} (r : Fin m → ℂ)
    (Q : Ideal (Poly m)) [Q.IsPrime]
    (hy : primeResidueMap Q (MvPolynomial.X 0) ≠ 0)
    (hz : primeResidueMap Q (MvPolynomial.X 1) ≠ 0)
    {J : Type*} (f : J → Poly m)
    (hQ : Q ∈ (Ideal.span (Set.range f)).minimalPrimes)
    (rho : Fin (m + 2) → ℚ) (hrho : ∀ i, 0 < rho i)
    (cost : Fin (m + 2) → ℝ) (hcost : ∀ i, 0 < cost i)
    (epsilon N : ℝ) (hepsilon : 0 < epsilon) (hN : 0 < N)
    (hdegree : ∀ j, ∀ d ∈ (f j).support,
      (∑ i ∈ d.support, (d i : ℝ) * (rho i : ℝ)) ≤ N)
    (hbudget : ∀ i, ((m : ℝ) + 2) * cost i < epsilon * N)
    (hvanish : ∀ p ∈ Ideal.span (Set.range f), ∀ indices : List (Fin (m + 2)),
      wordCost cost indices ≤ epsilon * N → word m r indices p ∈ Q)
    (A B : Finset (Fin (m + 2)))
    (hA : IsNormalBasis (K := Q.ResidueField)
      (fun i => (polynomialTangent (primeResidueMap Q) Q).mkQ
        (Pi.basisFun Q.ResidueField _ i)) A)
    (hB : IsNormalBasis (K := Q.ResidueField)
      (fun i => (polynomialTangent (primeResidueMap Q) Q).mkQ
        (TwoBaseFrame.frameBasis m
          (primeResidueMap Q (MvPolynomial.X 0))
          (primeResidueMap Q (MvPolynomial.X 1)) hy hz
          (fun j => primeResidueMap Q (MvPolynomial.C (r j))) i)) B) :
    (∏ i ∈ A, (rho i : ℝ)) ≤
      (A.card : ℝ)^A.card * (1 / epsilon)^A.card * ∏ i ∈ B, cost i := by
  classical
  have hcard := hA.card_eq.trans hB.card_eq.symm
  by_cases hk : 0 < A.card
  · have hdim : (A.card : ℝ) ≤ (m : ℝ) + 2 := by
      exact_mod_cast (show A.card ≤ m + 2 by simpa using Finset.card_le_univ A)
    have h := comparison_of_normal_basis r Q hy hz A hk hA
      (enumeration A B hcard) (enumeration_linearIndependent A B hcard hB)
      f hQ rho hrho cost hcost epsilon N hepsilon hN hdegree (by
        intro i
        apply two_le_rectangularCutoff hk _ (fun j => hcost _) i
        exact (mul_le_mul_of_nonneg_right hdim (hcost _).le).trans_lt (hbudget _)) hvanish
    rw [prod_enumeration A B hcard cost] at h
    convert h using 1
    simp only [div_eq_mul_inv]
    ring
  · have hAc : A.card = 0 := by omega
    have hBc : B.card = 0 := hcard.symm.trans hAc
    have hAe := Finset.card_eq_zero.mp hAc
    have hBe := Finset.card_eq_zero.mp hBc
    simp [hAe, hBe]

#print axioms comparison_of_normal_basis
#print axioms comparison_of_normal_bases

end LogarithmExtension.LogRatio.WeightedComparison

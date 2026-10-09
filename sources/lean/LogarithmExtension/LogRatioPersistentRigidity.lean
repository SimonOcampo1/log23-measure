import LogarithmExtension.LogRatioComponentRigidity
import LogarithmExtension.LogRatioWeightedComparison
import OAI.NumberTheory.PiExponent.Approximation.FrameEquationFamily

/-!
# Two-base rigidity with the weighted comparison discharged

The hypotheses concern an actual bounded-degree polynomial, its derivative
ideal, persistence of derivatives in a prime, and explicit weight inequalities.
The normal-product comparison is a conclusion of the local multiplicity and
Bezout arguments, not a hypothesis of the endpoint below.
-/

noncomputable section
namespace LogarithmExtension.LogRatio.PersistentRigidity

open scoped BigOperators
open OAI.PiExponent OAI.PiExponentApprox
open OAI.PiExponent.DerivativeIdeals
open PolynomialFrame

abbrev BoundedWords {m : ℕ} (cost : Fin (m + 2) → ℝ) (bound : ℝ) :=
  {indices : List (Fin (m + 2)) // wordCost cost indices ≤ bound}

def equations {m : ℕ} (r : Fin m → ℂ) (cost : Fin (m + 2) → ℝ)
    (bound : ℝ) (F : Poly m) : BoundedWords cost bound → Poly m :=
  fun indices => word m r indices.1 F

theorem span_equations {m : ℕ} (r : Fin m → ℂ) (cost : Fin (m + 2) → ℝ)
    (bound : ℝ) (F : Poly m) :
    Ideal.span (Set.range (equations r cost bound F)) = ideal m r cost bound F := by
  unfold ideal derivativeIdeal
  congr 1
  ext g
  constructor
  · rintro ⟨indices, rfl⟩
    exact ⟨indices.1, indices.2, rfl⟩
  · rintro ⟨indices, hindices, rfl⟩
    exact ⟨⟨indices, hindices⟩, rfl⟩

theorem equation_degree {m : ℕ} (r : Fin m → ℂ)
    (cost : Fin (m + 2) → ℝ) (bound N : ℝ) (F : Poly m)
    (rho : Fin (m + 2) → ℚ) (hrho : ∀ i, 0 < rho i)
    (hF : HasWeightedDegreeLE (fun i => (rho i : ℝ)) N F)
    (j : BoundedWords cost bound) :
    ∀ d ∈ (equations r cost bound F j).support,
      (∑ i ∈ d.support, (d i : ℝ) * (rho i : ℝ)) ≤ N := by
  have h := degree_word m r hF (fun i => by exact_mod_cast (hrho i).le) j.1
  have hs := (FrameEquationFamily.hasWeightedDegreeLE_iff_supportBound
    (fun i => (rho i : ℝ)) N _).mp h
  simpa only [equations, WeightedSliceDegree.SupportBound, Finsupp.weight_apply, Finsupp.sum,
    nsmul_eq_mul] using hs

theorem constants_of_derivative_persistence {m : ℕ}
    (p q : Fin m → ℤ) (hq : ∀ i, q i ≠ 0)
    (rho : Fin (m + 2) → ℚ) (hrho : ∀ i, 0 < rho i)
    (cost : Fin (m + 2) → ℝ) (hcost : ∀ i, 0 < cost i)
    (epsilon N : ℝ) (hepsilon : 0 < epsilon) (hN : 0 < N)
    (w0 v0 : ℝ) (hw0 : 0 < w0) (hv0 : 0 < v0)
    (hwbase : (rho 0 : ℝ) = w0 ∧ (rho 1 : ℝ) = w0)
    (hvbase : cost 0 = v0 ∧ cost 1 = v0)
    (hbase : 2 * (1 / epsilon) * v0 < w0)
    (hbudget : ∀ i, ((m : ℝ) + 2) * cost i < epsilon * N)
    (F : Poly m) (hF0 : F ≠ 0)
    (hF : HasWeightedDegreeLE (fun i => (rho i : ℝ)) N F)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (Q : Ideal (Poly m)) [Q.IsPrime]
    (hy : primeResidueMap Q (MvPolynomial.X 0) ≠ 0)
    (hz : primeResidueMap Q (MvPolynomial.X 1) ≠ 0)
    (hQ : Q ∈ (ideal m (fun i => (p i : ℂ) / (q i : ℂ)) cost bound F).minimalPrimes)
    (hvanish : ∀ g ∈ ideal m (fun i => (p i : ℂ) / (q i : ℂ)) cost bound F,
      ∀ indices : List (Fin (m + 2)), wordCost cost indices ≤ epsilon * N →
        word m (fun i => (p i : ℂ) / (q i : ℂ)) indices g ∈ Q)
    (hseparated : ∀ A B : Finset (Fin (m + 2)), A.card = B.card →
      ∀ i, 2 ≤ i.val → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      (A.card : ℝ)^A.card * (1 / epsilon)^A.card * (∏ j ∈ B, cost j) <
        ∏ j ∈ A, (rho j : ℝ)) :
    ∃ i : Fin m, (∃ a : ℂ, algebraMap ℂ Q.ResidueField a =
      primeResidueMap Q (MvPolynomial.X 1) ^ q i /
        primeResidueMap Q (MvPolynomial.X 0) ^ p i) ∧
      ∃ b : ℂ, algebraMap ℂ Q.ResidueField b =
        primeResidueMap Q (MvPolynomial.X i.succ.succ) := by
  let : Algebra.EssFiniteType ℂ Q.ResidueField :=
    Algebra.EssFiniteType.comp ℂ (Poly m) Q.ResidueField
  let r : Fin m → ℂ := fun i => (p i : ℂ) / (q i : ℂ)
  have hFQ : F ∈ Q := hQ.le
    (self_mem_derivativeIdeal (frame m r) cost bound F hbound)
  have hQ0 : Q ≠ ⊥ := by
    intro h
    exact hF0 (by simpa only [h, Ideal.mem_bot] using hFQ)
  apply ComponentRigidity.constants_of_weight_comparison (primeResidueMap Q) Q
    (fun _ => Ideal.algebraMap_residueField_eq_zero) hQ0 hy hz p q hq
    (fun i => (rho i : ℝ)) cost w0 v0 (1 / epsilon) hw0 hv0 (by positivity)
    hwbase hvbase hbase ?_ hseparated
  intro A B hA hB
  apply WeightedComparison.comparison_of_normal_bases r Q hy hz
    (equations r cost bound F)
    (by simpa only [span_equations] using hQ)
    rho hrho cost hcost epsilon N hepsilon hN
    (equation_degree r cost bound N F rho hrho hF) hbudget
    (by simpa only [span_equations] using hvanish) A B hA
  simpa [r, MvPolynomial.algHom_C] using hB

#print axioms constants_of_derivative_persistence

/-- The residue-field conclusion is packaged only to quantify over the prime
and its instance. It does not contain any comparison hypothesis. -/
def HasConstantCharacter {m : ℕ} (Q : Ideal (Poly m)) [Q.IsPrime]
    (p q : Fin m → ℤ) : Prop :=
  ∃ i : Fin m, (∃ a : ℂ, algebraMap ℂ Q.ResidueField a =
    primeResidueMap Q (MvPolynomial.X 1) ^ q i /
      primeResidueMap Q (MvPolynomial.X 0) ^ p i) ∧
    ∃ b : ℂ, algebraMap ℂ Q.ResidueField b =
      primeResidueMap Q (MvPolynomial.X i.succ.succ)

/-- A bounded-degree polynomial vanishing to the specified derivative budget
on P has a rigid component containing P. This joins persistence, multiplicity,
the degree comparison and algebraic differential rigidity in one endpoint. -/
theorem exists_rigid_persistent_component {m : ℕ}
    (p q : Fin m → ℤ) (hq : ∀ i, q i ≠ 0)
    (rho : Fin (m + 2) → ℚ) (hrho : ∀ i, 0 < rho i)
    (cost : Fin (m + 2) → ℝ) (hcost : ∀ i, 0 < cost i)
    (epsilon N : ℝ) (hepsilon : 0 < epsilon) (hN : 0 < N)
    (w0 v0 : ℝ) (hw0 : 0 < w0) (hv0 : 0 < v0)
    (hwbase : (rho 0 : ℝ) = w0 ∧ (rho 1 : ℝ) = w0)
    (hvbase : cost 0 = v0 ∧ cost 1 = v0)
    (hbase : 2 * (1 / epsilon) * v0 < w0)
    (hbudget : ∀ i, ((m : ℝ) + 2) * cost i < epsilon * N)
    (F : Poly m) (hF0 : F ≠ 0)
    (hF : HasWeightedDegreeLE (fun i => (rho i : ℝ)) N F)
    (P : Ideal (Poly m)) (hP : P.IsPrime) (hheight : P.height ≤ m + 1)
    (hy : MvPolynomial.X (0 : Fin (m + 2)) ∉ P)
    (hz : MvPolynomial.X (1 : Fin (m + 2)) ∉ P)
    (hvanish : ∀ indices : List (Fin (m + 2)),
      wordCost cost indices ≤ ((m : ℝ) + 3) * (epsilon * N) →
        word m (fun i => (p i : ℂ) / (q i : ℂ)) indices F ∈ P)
    (hseparated : ∀ A B : Finset (Fin (m + 2)), A.card = B.card →
      ∀ i, 2 ≤ i.val → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      (A.card : ℝ)^A.card * (1 / epsilon)^A.card * (∏ j ∈ B, cost j) <
        ∏ j ∈ A, (rho j : ℝ)) :
    ∃ (Q : Ideal (Poly m)) (hQ : Q.IsPrime),
      Q ≤ P ∧ @HasConstantCharacter m Q hQ p q := by
  obtain ⟨a, ha, Q, hQr, hQnext, hQP, hQlo, hQhi, hpersist⟩ :=
    exists_persistent_component m (fun i => (p i : ℂ) / (q i : ℂ)) cost
      (fun i => (hcost i).le) (epsilon * N) (mul_pos hepsilon hN).le F hF0
      P hP hheight hvanish
  let : Q.IsPrime := hQr.isPrime
  have hyQ : primeResidueMap Q (MvPolynomial.X 0) ≠ 0 :=
    fun h => hy (hQP (Ideal.algebraMap_residueField_eq_zero.mp h))
  have hzQ : primeResidueMap Q (MvPolynomial.X 1) ≠ 0 :=
    fun h => hz (hQP (Ideal.algebraMap_residueField_eq_zero.mp h))
  refine ⟨Q, inferInstance, hQP, ?_⟩
  exact constants_of_derivative_persistence p q hq rho hrho cost hcost
    epsilon N hepsilon hN w0 v0 hw0 hv0 hwbase hvbase hbase hbudget F hF0 hF
    ((a : ℝ) * (epsilon * N)) (by positivity) Q hyQ hzQ hQr hpersist hseparated

#print axioms exists_rigid_persistent_component

end LogarithmExtension.LogRatio.PersistentRigidity

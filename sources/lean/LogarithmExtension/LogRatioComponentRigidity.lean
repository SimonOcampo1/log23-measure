import LogarithmExtension.LogRatioNormalComparison
import LogarithmExtension.LogRatioTorusRigidity
import OAI.NumberTheory.PiExponent.Approximation.GenericNormalRigidity

/-!
# Two-base component rigidity from explicit normal-product comparisons

This connects the new normal-space theorem to the algebraic logarithmic
obstruction. In a genuine coordinate function field it proves that one
auxiliary coordinate and its torus character are constant. This module keeps
the normal-product comparisons explicit. `LogRatioPersistentRigidity` derives
them from the actual two-base derivative persistence and degree bounds.
Neither module asserts the full interpolation or irrationality theorem.
-/

noncomputable section
namespace LogarithmExtension.LogRatio.ComponentRigidity

open Module OAI.PiExponent OAI.PiExponent.NormalBasisRigidity
open TwoBaseFrame NormalComparison TorusRigidity
open scoped BigOperators

variable {C E : Type*} [Field C] [CharZero C] [IsAlgClosed C]
  [Field E] [Algebra C E] [Algebra.EssFiniteType C E]

/-- Component rigidity for the actual two-base frame with rational slopes.
No rank, surjectivity-of-interpolation, or irrationality conclusion is assumed. -/
theorem constants_of_weight_comparison {m : ℕ}
    (φ : MvPolynomial (Fin (m + 2)) C →ₐ[C] E)
    (Q : Ideal (MvPolynomial (Fin (m + 2)) C))
    (hker : ∀ P, φ P = 0 ↔ P ∈ Q) (hQ : Q ≠ ⊥)
    (hy : φ (MvPolynomial.X 0) ≠ 0) (hz : φ (MvPolynomial.X 1) ≠ 0)
    (p q : Fin m → ℤ) (hq : ∀ i, q i ≠ 0)
    (w cost : Fin (m + 2) → ℝ) (w0 v0 L : ℝ)
    (hw0 : 0 < w0) (hv0 : 0 < v0) (hL : 0 < L)
    (hwbase : w 0 = w0 ∧ w 1 = w0) (hvbase : cost 0 = v0 ∧ cost 1 = v0)
    (hbase : 2 * L * v0 < w0)
    (hcomparison : ∀ A B : Finset (Fin (m + 2)),
      IsNormalBasis (K := E)
        (fun j => (polynomialTangent φ Q).mkQ (Pi.basisFun E _ j)) A →
      IsNormalBasis (K := E)
        (fun j => (polynomialTangent φ Q).mkQ
          (TwoBaseFrame.frameBasis m (φ (MvPolynomial.X 0)) (φ (MvPolynomial.X 1))
            hy hz (fun i => (p i : E) / (q i : E)) j)) B →
      (∏ j ∈ A, w j) ≤ (A.card : ℝ)^A.card * L^A.card * ∏ j ∈ B, cost j)
    (hseparated : ∀ A B : Finset (Fin (m + 2)), A.card = B.card →
      ∀ i, 2 ≤ i.val → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      (A.card : ℝ)^A.card * L^A.card * (∏ j ∈ B, cost j) < ∏ j ∈ A, w j) :
    ∃ i : Fin m, (∃ a : C, algebraMap C E a =
      φ (MvPolynomial.X 1) ^ q i / φ (MvPolynomial.X 0) ^ p i) ∧
      ∃ b : C, algebraMap C E b = φ (MvPolynomial.X i.succ.succ) := by
  let : CharZero E := Algebra.charZero_of_charZero C E
  obtain ⟨i, hi⟩ := exists_tangent_relation m
    (φ (MvPolynomial.X 0)) (φ (MvPolynomial.X 1)) hy hz
    (fun i => (p i : E) / (q i : E)) (polynomialTangent φ Q).mkQ
    (Submodule.mkQ_surjective _) (polynomialNormal_mkQ_ne_zero_of_kernel φ Q hker hQ)
    w cost w0 v0 L hw0 hv0 hL hwbase hvbase hbase hcomparison hseparated
  have hd := differential_of_tangent φ Q (fun P hP => (hker P).mpr hP)
    i ((p i : E) / (q i : E)) (fun t ht =>
      hi t ((Submodule.Quotient.mk_eq_zero _).mpr ht))
  exact ⟨i, constants_of_relation (φ (MvPolynomial.X i.succ.succ))
    (φ (MvPolynomial.X 0)) (φ (MvPolynomial.X 1)) hy hz (p i) (q i) (hq i) hd⟩

#print axioms constants_of_weight_comparison

end LogarithmExtension.LogRatio.ComponentRigidity

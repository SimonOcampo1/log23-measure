import LogarithmExtension.LogRatioTwoBaseFrame
import OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame
import OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals
import Mathlib.RingTheory.Derivation.Lie

/-!
# Actual commuting polynomial derivatives for the two-base ratio argument

These are the operators underlying the tangent basis, not abstract operators
assumed to commute. Their arbitrary iterates preserve the weighted degree
bound whenever all weights are nonnegative. The degree lemmas and the
single-variable derivative commutation are from the pinned OpenAI sources
(Apache-2.0); the two-base construction and proofs are new here.
-/

noncomputable section
namespace LogarithmExtension.LogRatio.PolynomialFrame

open MvPolynomial OAI.PiExponentApprox
open scoped BigOperators

abbrev Poly (m : ℕ) := MvPolynomial (Fin (m + 2)) ℂ

variable (m : ℕ) (r : Fin m → ℂ)

def dY : Derivation ℂ (Poly m) (Poly m) :=
  (X (0 : Fin (m + 2)) : Poly m) • pderiv (R := ℂ) 0 -
    ∑ i : Fin m, r i • pderiv (R := ℂ) i.succ.succ

def dZ : Derivation ℂ (Poly m) (Poly m) :=
  (X (1 : Fin (m + 2)) : Poly m) • pderiv (R := ℂ) 1 +
    ∑ i : Fin m, pderiv (R := ℂ) i.succ.succ

def frame : Fin (m + 2) → Derivation ℂ (Poly m) (Poly m) :=
  Fin.cases (dY m r) (Fin.cases (dZ m) (fun i => pderiv i.succ.succ))

@[simp] theorem aux_ne_one (i : Fin m) : i.succ.succ ≠ (1 : Fin (m + 2)) := by
  rw [← Fin.succ_zero_eq_one]
  exact fun h => Fin.succ_ne_zero i (Fin.succ_injective _ h)

@[simp] theorem one_ne_aux (i : Fin m) : (1 : Fin (m + 2)) ≠ i.succ.succ :=
  (aux_ne_one m i).symm

@[simp] theorem dY_apply (P : Poly m) :
    dY m r P = X 0 * pderiv 0 P - ∑ i : Fin m, r i • pderiv i.succ.succ P := by
  simp only [dY, Derivation.sub_apply, Derivation.smul_apply,
    derivation_finset_sum_apply, smul_eq_mul]

@[simp] theorem dZ_apply (P : Poly m) :
    dZ m P = X 1 * pderiv 1 P + ∑ i : Fin m, pderiv i.succ.succ P := by
  simp only [dZ, Derivation.add_apply, Derivation.smul_apply,
    derivation_finset_sum_apply, smul_eq_mul]

@[simp] theorem dY_X_zero : dY m r (X 0) = X 0 := by
  simp [pderiv_X]

@[simp] theorem dY_X_one : dY m r (X 1) = 0 := by
  simp [pderiv_X]

@[simp] theorem dY_X_aux (i : Fin m) : dY m r (X i.succ.succ) = C (-r i) := by
  simp [pderiv_X, Pi.single_apply, Algebra.smul_def]

@[simp] theorem dZ_X_zero : dZ m (X 0) = 0 := by
  simp [pderiv_X]

@[simp] theorem dZ_X_one : dZ m (X 1) = X 1 := by
  simp [pderiv_X]

@[simp] theorem dZ_X_aux (i : Fin m) : dZ m (X i.succ.succ) = 1 := by
  simp [pderiv_X, Pi.single_apply]

theorem commute_of_X (d e : Derivation ℂ (Poly m) (Poly m))
    (h : ∀ i, d (e (X i)) = e (d (X i))) (P : Poly m) : d (e P) = e (d P) := by
  have hbracket : ⁅d, e⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro i
    simp only [Derivation.commutator_apply, h, sub_self, Derivation.zero_apply]
  have hp := congrArg (fun D : Derivation ℂ (Poly m) (Poly m) => D P) hbracket
  exact sub_eq_zero.mp hp

theorem dY_dZ_commute (P : Poly m) : dY m r (dZ m P) = dZ m (dY m r P) := by
  apply commute_of_X
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp
  · refine Fin.cases ?_ (fun i => ?_) k
    · simp [Fin.succ_zero_eq_one]
    · rw [dZ_X_aux, dY_X_aux]
      simp only [Derivation.map_one_eq_zero, MvPolynomial.derivation_C]

theorem dY_aux_commute (i : Fin m) (P : Poly m) :
    dY m r (pderiv i.succ.succ P) = pderiv i.succ.succ (dY m r P) := by
  apply commute_of_X
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [pderiv_X]
  · refine Fin.cases ?_ (fun l => ?_) k
    · simp [Fin.succ_zero_eq_one, pderiv_X]
    · simp [pderiv_X, Pi.single_apply, apply_ite]

theorem dZ_aux_commute (i : Fin m) (P : Poly m) :
    dZ m (pderiv i.succ.succ P) = pderiv i.succ.succ (dZ m P) := by
  apply commute_of_X
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [pderiv_X]
  · refine Fin.cases ?_ (fun l => ?_) k
    · simp [Fin.succ_zero_eq_one, pderiv_X]
    · simp [pderiv_X, Pi.single_apply, apply_ite]

theorem frame_commute (i j : Fin (m + 2)) (P : Poly m) :
    frame m r i (frame m r j P) = frame m r j (frame m r i P) := by
  refine Fin.cases ?_ (fun i' => ?_) i
  · refine Fin.cases ?_ (fun j' => ?_) j
    · rfl
    · refine Fin.cases ?_ (fun k => ?_) j'
      · exact dY_dZ_commute m r P
      · exact dY_aux_commute m r k P
  · refine Fin.cases ?_ (fun k => ?_) i'
    · refine Fin.cases ?_ (fun j' => ?_) j
      · exact (dY_dZ_commute m r P).symm
      · refine Fin.cases ?_ (fun l => ?_) j'
        · rfl
        · exact dZ_aux_commute m l P
    · refine Fin.cases ?_ (fun j' => ?_) j
      · exact (dY_aux_commute m r k P).symm
      · refine Fin.cases ?_ (fun l => ?_) j'
        · exact (dZ_aux_commute m k P).symm
        · exact polynomial_pderiv_commute (m + 1) k.succ.succ l.succ.succ P

theorem degree_smul {w : Fin (m + 2) → ℝ} {N : ℝ} {P : Poly m}
    (hP : HasWeightedDegreeLE w N P) (a : ℂ) : HasWeightedDegreeLE w N (a • P) :=
  fun d hd => hP d (MvPolynomial.support_smul hd)

theorem degree_neg {w : Fin (m + 2) → ℝ} {N : ℝ} {P : Poly m}
    (hP : HasWeightedDegreeLE w N P) : HasWeightedDegreeLE w N (-P) := by
  simpa using degree_smul m hP (-1)

theorem degree_frame {w : Fin (m + 2) → ℝ} {N : ℝ} {P : Poly m}
    (hP : HasWeightedDegreeLE w N P) (hw : ∀ i, 0 ≤ w i) (i : Fin (m + 2)) :
    HasWeightedDegreeLE w N (frame m r i P) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · change HasWeightedDegreeLE w N (dY m r P)
    rw [dY_apply, sub_eq_add_neg]
    apply (hP.X_mul_pderiv 0).add
    apply degree_neg
    exact HasWeightedDegreeLE.sum Finset.univ _ (fun i _ =>
      degree_smul m (hP.pderiv_preserves i.succ.succ (hw _)) (r i))
  · refine Fin.cases ?_ (fun k => ?_) j
    · change HasWeightedDegreeLE w N (dZ m P)
      rw [dZ_apply]
      exact (hP.X_mul_pderiv 1).add (HasWeightedDegreeLE.sum Finset.univ _
        (fun i _ => hP.pderiv_preserves i.succ.succ (hw _)))
    · exact hP.pderiv_preserves k.succ.succ (hw _)

def word (indices : List (Fin (m + 2))) (P : Poly m) : Poly m :=
  indices.foldr (fun i f => frame m r i f) P

theorem degree_word {w : Fin (m + 2) → ℝ} {N : ℝ} {P : Poly m}
    (hP : HasWeightedDegreeLE w N P) (hw : ∀ i, 0 ≤ w i)
    (indices : List (Fin (m + 2))) : HasWeightedDegreeLE w N (word m r indices P) := by
  induction indices with
  | nil => exact hP
  | cons i indices ih => exact degree_frame m r ih hw i

open OAI.PiExponent.DerivativeIdeals

def ideal (cost : Fin (m + 2) → ℝ) (bound : ℝ) (F : Poly m) : Ideal (Poly m) :=
  derivativeIdeal (frame m r) cost bound F

/-- Persistence for these actual derivatives. The ambient dimension is m+2,
so the curve prime has height at most m+1 and the budget is (m+3)*delta. -/
theorem exists_persistent_component
    (cost : Fin (m + 2) → ℝ) (hcost : ∀ i, 0 ≤ cost i)
    (delta : ℝ) (hdelta : 0 ≤ delta) (F : Poly m) (hF : F ≠ 0)
    (P : Ideal (Poly m)) (hP : P.IsPrime) (hheight : P.height ≤ m + 1)
    (hvanish : ∀ indices : List (Fin (m + 2)),
      wordCost cost indices ≤ ((m : ℝ) + 3) * delta → word m r indices F ∈ P) :
    ∃ a < m + 3, ∃ Q : Ideal (Poly m),
      Q ∈ (ideal m r cost ((a : ℝ) * delta) F).minimalPrimes ∧
      Q ∈ (ideal m r cost (((a : ℝ) + 1) * delta) F).minimalPrimes ∧
      Q ≤ P ∧ 1 ≤ Q.height ∧ Q.height ≤ m + 1 ∧
      ∀ g ∈ ideal m r cost ((a : ℝ) * delta) F,
        ∀ indices, wordCost cost indices ≤ delta → word m r indices g ∈ Q := by
  have h := exists_persistent_derivative_component (frame m r) cost hcost
    delta hdelta F hF (m + 1) P hP hheight (by
      intro indices hi
      apply hvanish indices
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, show (1 : ℝ) + 2 = 3 by norm_num]
        using hi)
  simpa [ideal, word, wordDerivative, Nat.add_assoc] using h

#print axioms frame_commute
#print axioms degree_word
#print axioms exists_persistent_component

end LogarithmExtension.LogRatio.PolynomialFrame

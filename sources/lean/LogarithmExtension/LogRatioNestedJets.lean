import LogarithmExtension.LogRatioAlgebraicJet
import OAI.NumberTheory.PiExponent.Approximation.RowTranslation

/-!
# Separating base and auxiliary coefficients in the actual two-base jets

The target is a polynomial in the auxiliary variables, with bivariate
formal-series coefficients. The coefficient identification below connects
this convenient row-translation representation to the original polynomial
and hence to the concrete bounded interpolation matrix.
-/

noncomputable section
namespace LogarithmExtension.LogRatio.NestedJets

open MvPolynomial OAI.PiExponent PolynomialFrame
open InterpolationMatrix (exponentVector exponentVector_apply)
open scoped BigOperators

abbrev BaseSeries := MvPowerSeries (Fin 2) ℂ
abbrev Nested (m : ℕ) := MvPolynomial (Fin m) BaseSeries

variable {m : ℕ}

def baseIndex (a : Fin (m+2) →₀ ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 (a 0) + Finsupp.single 1 (a 1)

def auxiliaryIndex (a : Fin (m+2) →₀ ℕ) : Fin m →₀ ℕ :=
  exponentVector (fun i => a i.succ.succ)

@[simp] theorem baseIndex_zero (a : Fin (m+2) →₀ ℕ) : baseIndex a 0 = a 0 := by
  simp [baseIndex]

@[simp] theorem baseIndex_one (a : Fin (m+2) →₀ ℕ) : baseIndex a 1 = a 1 := by
  simp [baseIndex]

@[simp] theorem auxiliaryIndex_apply (a : Fin (m+2) →₀ ℕ) (i : Fin m) :
    auxiliaryIndex a i = a i.succ.succ := by simp [auxiliaryIndex]

theorem indices_injective {a b : Fin (m+2) →₀ ℕ}
    (hbase : baseIndex a = baseIndex b) (haux : auxiliaryIndex a = auxiliaryIndex b) : a = b := by
  ext i
  cases i using Fin.cases with
  | zero => simpa using congrArg (fun x => x 0) hbase
  | succ k =>
    cases k using Fin.cases with
    | zero => simpa using congrArg (fun x => x 1) hbase
    | succ i => simpa using congrArg (fun x => x i) haux

def split : Poly m →ₐ[ℂ] Nested m :=
  aeval (Fin.cases (C (MvPowerSeries.X 0))
    (Fin.cases (C (MvPowerSeries.X 1)) (fun i => X i)))

@[simp] theorem split_C (c : ℂ) : split (C c : Poly m) = C (MvPowerSeries.C c) := by
  simp only [split, aeval_C]
  rfl

@[simp] theorem split_Y : split (X 0 : Poly m) = C (MvPowerSeries.X 0) := by simp [split]

@[simp] theorem split_Z : split (X 1 : Poly m) = C (MvPowerSeries.X 1) := by
  simp only [split, aeval_X]
  rfl

@[simp] theorem split_aux (i : Fin m) : split (X i.succ.succ : Poly m) = X i := by simp [split]

theorem split_monomial_one (a : Fin (m+2) →₀ ℕ) :
    split (monomial a 1) =
      C ((MvPowerSeries.X 0)^a 0 * (MvPowerSeries.X 1)^a 1) *
        monomial (auxiliaryIndex a) 1 := by
  rw [split, aeval_monomial, map_one, one_mul,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_succ,
    Fin.prod_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ, Fin.succ_zero_eq_one, TwoBaseFrame.fin_cases_one]
  have hx : (∏ i : Fin m, (X i : Nested m) ^ a i.succ.succ) =
      monomial (auxiliaryIndex a) 1 := by
    rw [MvPolynomial.monomial_eq, map_one, one_mul,
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    rfl
  rw [hx, map_mul, map_pow, map_pow]
  ring

theorem split_monomial (a : Fin (m+2) →₀ ℕ) (c : ℂ) :
    split (monomial a c) =
      monomial (auxiliaryIndex a) (MvPowerSeries.monomial (baseIndex a) c) := by
  rw [show monomial a c = C c * monomial a 1 by rw [C_mul_monomial, mul_one]]
  rw [map_mul, split_C, split_monomial_one, ← mul_assoc, ← map_mul, C_mul_monomial, mul_one]
  congr 1
  rw [MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq,
    ← MvPowerSeries.monomial_zero_eq_C_apply,
    MvPowerSeries.monomial_mul_monomial, MvPowerSeries.monomial_mul_monomial]
  simp [baseIndex]

/-- The nested coefficient test is exactly the original full coefficient. -/
theorem coeff_split (P : Poly m) (a : Fin (m+2) →₀ ℕ) :
    MvPowerSeries.coeff (baseIndex a) ((split P).coeff (auxiliaryIndex a)) = P.coeff a := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial b c =>
    rw [split_monomial, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    by_cases hb : b = a
    · subst b; simp
    · by_cases haux : auxiliaryIndex b = auxiliaryIndex a
      · have hbase : baseIndex b ≠ baseIndex a := fun h => hb (indices_injective h haux)
        simp [haux, Ne.symm hbase, hb, MvPowerSeries.coeff_monomial]
      · simp [haux, hb]
  | add P Q hP hQ => simp [hP, hQ]

def embeddedPolynomial (i : Fin 2) (G : Polynomial ℂ) : BaseSeries :=
  Polynomial.aeval (MvPowerSeries.X i) G

@[simp] theorem split_polynomial_aeval_zero (G : Polynomial ℂ) :
    split (Polynomial.aeval (X 0) G : Poly m) = C (embeddedPolynomial 0 G) := by
  rw [← Polynomial.aeval_algHom_apply, split_Y]
  induction G using Polynomial.induction_on' with
  | monomial n c => simp [Polynomial.aeval_monomial, embeddedPolynomial, map_mul, map_pow]
  | add P Q hP hQ => simp [embeddedPolynomial, hP, hQ] at *

@[simp] theorem split_polynomial_aeval_one (G : Polynomial ℂ) :
    split (Polynomial.aeval (X 1) G : Poly m) = C (embeddedPolynomial 1 G) := by
  rw [← Polynomial.aeval_algHom_apply, split_Z]
  induction G using Polynomial.induction_on' with
  | monomial n c => simp [Polynomial.aeval_monomial, embeddedPolynomial, map_mul, map_pow]
  | add P Q hP hQ => simp [embeddedPolynomial, hP, hQ] at *

def monomialImage (cy cz : ℂ) (g : Fin m → BaseSeries)
    (a : Fin (m+2) →₀ ℕ) : Nested m :=
  C ((MvPowerSeries.C cy * (1+MvPowerSeries.X 0)) ^ a 0 *
    (MvPowerSeries.C cz * (1+MvPowerSeries.X 1)) ^ a 1) *
    RowTranslation.shift g (monomial (auxiliaryIndex a) 1)

theorem split_forward_monomial (cy cz : ℂ) (r : Fin m → ℂ)
    (G : Fin m → Polynomial ℂ) (a : Fin (m+2) →₀ ℕ) :
    split (AlgebraicJet.forward cy cz (fun _ => 0) r G (monomial a 1)) =
      monomialImage cy cz (fun i => embeddedPolynomial 1 (G i) -
        MvPowerSeries.C (r i) * embeddedPolynomial 0 (G i)) a := by
  rw [AlgebraicJet.forward, aeval_monomial, map_one, one_mul,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_succ,
    Fin.prod_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ, Fin.succ_zero_eq_one, TwoBaseFrame.fin_cases_one,
    map_mul, map_add, map_pow, map_prod, map_sub, split_C, split_Y, split_Z, split_aux,
    split_polynomial_aeval_zero, split_polynomial_aeval_one, map_zero, zero_add, map_one]
  rw [monomialImage, RowTranslation.shift_monomial_one]
  simp only [auxiliaryIndex_apply, map_sub, map_mul, map_pow, map_add, map_one, add_sub_assoc]
  ring

end LogarithmExtension.LogRatio.NestedJets

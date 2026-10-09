import OAI.NumberTheory.PiExponent.Approximation.Arithmetic
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Multivariate denominator clearing for the two-base determinant

Diagonal auxiliary-variable rescaling accounts exactly for the row and
column powers of the approximation denominators.  The integrality lemmas
below work with the image of integer polynomials. Its inclusion in the
Gaussian integers then supplies the upstream determinant norm bound.

The power/product clearing proofs adapt the corresponding univariate
lemmas in the pinned OpenAI `Approximation.Arithmetic` module (Apache-2.0).
-/

noncomputable section
namespace LogarithmExtension.LogRatio.DenominatorClearing

open MvPolynomial
open scoped BigOperators

variable {σ : Type*}

def diagonal (c : σ → ℂ) : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ :=
  aeval (fun i => C (c i) * X i)

@[simp] theorem diagonal_X (c : σ → ℂ) (i : σ) :
    diagonal c (X i) = C (c i) * X i := by simp [diagonal]

theorem diagonal_monomial [Fintype σ] (c : σ → ℂ) (a : σ →₀ ℕ) (r : ℂ) :
    diagonal c (monomial a r) = C (∏ i, c i ^ a i) * monomial a r := by
  rw [diagonal, aeval_monomial, monomial_eq]
  simp only [algebraMap_eq]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod]
  ring

theorem coeff_diagonal [Fintype σ] (c : σ → ℂ) (P : MvPolynomial σ ℂ)
    (a : σ →₀ ℕ) :
    (diagonal c P).coeff a = (∏ i, c i ^ a i) * P.coeff a := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial b r =>
    rw [diagonal_monomial, coeff_C_mul]
    by_cases h : b = a
    · subst b; rfl
    · simp [coeff_monomial, h]
  | add P Q hP hQ => simp [hP, hQ, mul_add]

def integralPolynomials (σ : Type*) : Subring (MvPolynomial σ ℂ) :=
  (MvPolynomial.map (Int.castRingHom ℂ)).range

theorem integral_C (z : ℤ) : C (z : ℂ) ∈ integralPolynomials σ :=
  ⟨C z, by simp⟩

theorem integral_X (i : σ) : X i ∈ integralPolynomials σ :=
  ⟨X i, by simp⟩

theorem integral_C_nat (n : ℕ) : C (n : ℂ) ∈ integralPolynomials σ := by
  exact ⟨C (n : ℤ), by simp⟩

theorem integral_coeff {P : MvPolynomial σ ℂ} (hP : P ∈ integralPolynomials σ)
    (a : σ →₀ ℕ) : P.coeff a ∈ (Int.castRingHom ℂ).range := by
  obtain ⟨Q, rfl⟩ := hP
  exact ⟨Q.coeff a, (coeff_map _ _ _).symm⟩

theorem integral_polynomial_aeval (P : Polynomial ℤ) (i : σ) :
    Polynomial.aeval (X i : MvPolynomial σ ℂ) (P.map (Int.castRingHom ℂ)) ∈
      integralPolynomials σ := by
  induction P using Polynomial.induction_on' with
  | monomial n z =>
    simp only [Polynomial.map_monomial, Polynomial.aeval_monomial, algebraMap_eq]
    exact (integralPolynomials σ).mul_mem (integral_C z)
      ((integralPolynomials σ).pow_mem (integral_X i) n)
  | add P Q hP hQ =>
    simpa only [Polynomial.map_add, map_add] using (integralPolynomials σ).add_mem hP hQ

theorem lcm_mul_log_coeff_integer (T k : ℕ) (hk : k ≤ T) :
    (Nat.lcmUpto T : ℂ) * PowerSeries.coeff k (PowerSeries.log ℂ) ∈
      (Int.castRingHom ℂ).range := by
  by_cases hk0 : k = 0
  · simp [hk0]
  obtain ⟨a, ha⟩ := OAI.PiExponent.Arithmetic.dvd_lcmUpto_of_pos_le (Nat.pos_of_ne_zero hk0) hk
  refine ⟨((-1 : ℤ) ^ (k+1)) * (a : ℤ), ?_⟩
  rw [PowerSeries.coeff_log, ite_eq_right hk0, ha]
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk0
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast, map_div₀, Nat.cast_mul]
  field_simp

theorem exists_cleared_log_trunc_integer (T : ℕ) :
    ∃ P : Polynomial ℤ, P.map (Int.castRingHom ℂ) =
      Polynomial.C (Nat.lcmUpto T : ℂ) * PowerSeries.trunc T (PowerSeries.log ℂ) := by
  apply (Polynomial.mem_map_range (Int.castRingHom ℂ)).mpr
  intro k
  rw [Polynomial.coeff_C_mul, PowerSeries.coeff_trunc]
  split_ifs with hk
  · exact lcm_mul_log_coeff_integer T k hk.le
  · simp

theorem integer_mem_gaussian {z : ℂ} (hz : z ∈ (Int.castRingHom ℂ).range) :
    z ∈ GaussianInt.toComplex.range := by
  obtain ⟨n, hn⟩ := hz
  refine ⟨(n : GaussianInt), ?_⟩
  simpa using hn

theorem cleared_log_aeval_integral (T : ℕ) (i : σ) :
    C (Nat.lcmUpto T : ℂ) *
      Polynomial.aeval (X i : MvPolynomial σ ℂ) (PowerSeries.trunc T (PowerSeries.log ℂ)) ∈
        integralPolynomials σ := by
  obtain ⟨P, hP⟩ := exists_cleared_log_trunc_integer T
  have h := integral_polynomial_aeval P i
  rw [hP, map_mul, Polynomial.aeval_C, algebraMap_eq] at h
  exact h

theorem cleared_power_integral (L e d : ℕ) (f : MvPolynomial σ ℂ) (hd : d ≤ e)
    (hf : C (L : ℂ) * f ∈ integralPolynomials σ) :
    C ((L : ℂ) ^ e) * f ^ d ∈ integralPolynomials σ := by
  have h := (integralPolynomials σ).mul_mem
    ((integralPolynomials σ).pow_mem (integral_C_nat L) (e-d))
    ((integralPolynomials σ).pow_mem hf d)
  rw [show e = (e-d)+d from (Nat.sub_add_cancel hd).symm, map_pow, pow_add]
  simpa only [mul_pow, mul_assoc] using h

theorem cleared_product_integral {ι : Type*} (s : Finset ι)
    (L e d : ι → ℕ) (f : ι → MvPolynomial σ ℂ) (hd : ∀ i ∈ s, d i ≤ e i)
    (hf : ∀ i ∈ s, C (L i : ℂ) * f i ∈ integralPolynomials σ) :
    C (∏ i ∈ s, (L i : ℂ) ^ e i) * (∏ i ∈ s, f i ^ d i) ∈
      integralPolynomials σ := by
  have h := (integralPolynomials σ).prod_mem (fun i hi =>
    cleared_power_integral (L i) (e i) (d i) (f i) (hd i hi) (hf i hi))
  simpa only [← Finset.prod_mul_distrib, map_prod] using h

end LogarithmExtension.LogRatio.DenominatorClearing

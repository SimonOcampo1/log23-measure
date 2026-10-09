import Mathlib

/-!
# Logarithm extension: checked auxiliary lemmas

This file contains proof scripts for subsidiary identities, a concrete definition
of the rational interpolation matrix, and the final scalar comparison lemma.
It does not contain a proof of the logarithm irrationality-exponent theorem.
In particular, none of the geometric or analytic construction is assumed as a
new logical constant. See Target.lean and the proof-obligation ledger.

Adapted from the supplied partial formalization, which was not compiled in its
authoring runtime. This copy compiles with Lean v4.34.1 and Mathlib commit
d13f23b723b8a846827a245b89c10fc7d3f11612. The original package is unchanged.
Python tests elsewhere in the package are not Lean verification.
-/

noncomputable section

namespace LogarithmExtension

open scoped BigOperators

/-- Natural powers of a positive real base provide the required exponential centers. -/
theorem exp_nat_log (a : ℝ) (ha : 0 < a) (j : ℕ) :
    Real.exp ((j : ℝ) * Real.log a) = a ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Nat.cast_succ, add_mul, one_mul, Real.exp_add, ih,
        Real.exp_log ha, pow_succ]

/-- A real-domain identity. The complex analytic estimates are not formalized here. -/
theorem normalized_center_identity (a t : ℝ) (ha : 0 < a)
    (ht : 0 < 1 + t) (j : ℕ) :
    Real.exp ((j : ℝ) * Real.log a + Real.log (1 + t)) =
      a ^ j * (1 + t) := by
  rw [Real.exp_add, exp_nat_log a ha j, Real.exp_log ht]

theorem log_three_center_identity (t : ℝ) (ht : 0 < 1 + t) (j : ℕ) :
    Real.exp ((j : ℝ) * Real.log 3 + Real.log (1 + t)) =
      (3 : ℝ) ^ j * (1 + t) := by
  exact normalized_center_identity 3 t (by norm_num) ht j

/-- The purely exponential complex identity, with no logarithm-branch assumptions. -/
theorem complex_exponential_centers (ell τ : ℂ) (j : ℕ) :
    Complex.exp ((j : ℂ) * ell + τ) =
      (Complex.exp ell) ^ j * Complex.exp τ := by
  have hp : ∀ n : ℕ, Complex.exp ((n : ℂ) * ell) = (Complex.exp ell) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Nat.cast_succ, add_mul, one_mul, Complex.exp_add, ih, pow_succ]
  rw [Complex.exp_add, hp j]

/-- Distinctness of the positive multiplicative centers, including bases below one. -/
theorem positive_power_centers_injective (a : ℝ) (ha : 0 < a) (ha1 : a ≠ 1) :
    Function.Injective (fun j : ℕ => a ^ j) := by
  intro j k hjk
  have hn : Real.log a ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one ha ha1
  have hh : (j : ℝ) * Real.log a = (k : ℝ) * Real.log a := by
    simpa only [Real.log_pow] using congrArg Real.log hjk
  have hc : (j : ℝ) = (k : ℝ) := mul_right_cancel₀ hn hh
  exact_mod_cast hc

/-- Algebraic part of the exact transverse-error substitution. -/
theorem transverse_identity (j r ell g ℓ u : ℝ) :
    j * r + g + u =
      (j * ell + ℓ) + u + j * (r - ell) + (g - ℓ) := by
  ring

/-- Actual coordinate tuple on the rational side (one distinguished Y coordinate). -/
def rationalSide {ι : Type*} (a t : ℝ) (j : ℕ) (r g u : ι → ℝ) :
    Option ι → ℝ
  | none => a ^ j * (1 + t)
  | some i => (j : ℝ) * r i + g i + u i

/-- Actual coordinate tuple after translation to a common exponential curve. -/
def translatedSide {ι : Type*} (a t : ℝ) (j : ℕ) (r g u : ι → ℝ) :
    Option ι → ℝ
  | none => Real.exp ((j : ℝ) * Real.log a + Real.log (1 + t))
  | some i => ((j : ℝ) * Real.log a + Real.log (1 + t)) + u i +
      (j : ℝ) * (r i - Real.log a) + (g i - Real.log (1 + t))

/-- Equality of all coordinates, not a collection of finite numerical instances. -/
theorem coordinate_substitution {ι : Type*} (a t : ℝ) (ha : 0 < a)
    (ht : 0 < 1 + t) (j : ℕ) (r g u : ι → ℝ) :
    rationalSide a t j r g u = translatedSide a t j r g u := by
  funext x
  cases x with
  | none => exact (normalized_center_identity a t ha ht j).symm
  | some i =>
      exact transverse_identity (j : ℝ) (r i) (Real.log a)
        (g i) (Real.log (1 + t)) (u i)

/-- The substitution holds for every multivariable polynomial. This is NOT the
Taylor-row identity or the collision estimate, which remain proof obligations. -/
theorem polynomial_substitution {ι : Type*} (P : MvPolynomial (Option ι) ℝ)
    (a t : ℝ) (ha : 0 < a) (ht : 0 < 1 + t) (j : ℕ) (r g u : ι → ℝ) :
    MvPolynomial.eval (rationalSide a t j r g u) P =
      MvPolynomial.eval (translatedSide a t j r g u) P := by
  rw [coordinate_substitution a t ha ht j r g u]

/-- Extra column scaling for a rational base. Writing the unused center budget
as k avoids truncated natural-number subtraction. -/
theorem clear_center_power (a b : ℚ) (hb : b ≠ 0) (j k h : ℕ) :
    b ^ ((j + k) * h) * ((a / b) ^ j) ^ h =
      a ^ (j * h) * b ^ (k * h) := by
  rw [← pow_mul, Nat.add_mul, pow_add, div_pow]
  field_simp [hb]

/-- The center factor really becomes an integer after scaling. -/
theorem cleared_center_is_integer (a b : ℤ) (hb : b ≠ 0) (j k h : ℕ) :
    ∃ z : ℤ, (z : ℚ) =
      (b : ℚ) ^ ((j + k) * h) * (((a : ℚ) / (b : ℚ)) ^ j) ^ h := by
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  refine ⟨a ^ (j * h) * b ^ (k * h), ?_⟩
  rw [clear_center_power (a : ℚ) (b : ℚ) hbq j k h]
  norm_cast

/-- The truncated rational logarithm used in the actual matrix. -/
def logTaylor (T : ℕ) : Polynomial ℚ :=
  ∑ k ∈ Finset.range T,
    if k = 0 then 0 else
      Polynomial.monomial k (((-1 : ℚ) ^ (k + 1)) / (k : ℚ))

/-- Series for a monomial column after extracting its transverse coefficient. -/
def monomialSeries {m : ℕ} (base : ℚ) (r : Fin m → ℚ)
    (T : Fin m → ℕ) (j h : ℕ) (α β : Fin m → ℕ) : Polynomial ℚ :=
  Polynomial.C (base ^ (j * h) * ∏ i, (Nat.choose (α i) (β i) : ℚ)) *
    (1 + Polynomial.X) ^ h *
    ∏ i, (Polynomial.C ((j : ℚ) * r i) + logTaylor (T i)) ^ (α i - β i)

/-- Actual rational matrix entry. No rank or determinant bound is built into it. -/
def matrixEntry {m : ℕ} (base : ℚ) (r : Fin m → ℚ)
    (T : Fin m → ℕ) (j s h : ℕ) (α β : Fin m → ℕ) : ℚ :=
  if ∀ i, β i ≤ α i then
    (monomialSeries base r T j h α β).coeff s
  else 0

/-- A construction sanity check; not an asymptotic interpolation assertion. -/
theorem constant_column_entry {m : ℕ} (base : ℚ) (r : Fin m → ℚ)
    (T : Fin m → ℕ) (j : ℕ) :
    matrixEntry base r T j 0 0 (fun _ => 0) (fun _ => 0) = 1 := by
  simp [matrixEntry, monomialSeries]

/-- Norm averaging accounts for the number of embeddings on which the analytic
estimate is available. The norm estimate itself is NOT assumed proved by this lemma. -/
theorem norm_averaging (d s cost ar an other : ℝ) (hs : 0 < s)
    (h : -d * cost - ar ≤ s * an + other) :
    -(d / s) * cost - (ar + other) / s ≤ an := by
  have hd : (-d * cost - ar - other) / s ≤ an :=
    (div_le_iff₀ hs).2 (by linarith)
  convert hd using 1
  ring

/-- The final algebraic comparison, with all determinant-estimate hypotheses
explicit. It does not construct a determinant or establish those hypotheses. -/
theorem determinant_comparison
    (κ ν A η θ b ar an c L z : ℝ)
    (hκ : 0 ≤ κ) (hν : κ ≤ ν) (hb : 0 ≤ b) (hbθ : b ≤ θ)
    (hgap : ar + an < ν * (A * (1 - η) - θ) - κ * (1 - θ))
    (hcollision : κ + ar + an < c * L)
    (hlower : -κ * (1 - b) - ar ≤ z)
    (hupper : z ≤ an + max (-c * L) (-ν * (A * (1 - η) - b))) : False := by
  have hκb : 0 ≤ κ * b := mul_nonneg hκ hb
  have hprod : 0 ≤ (ν - κ) * (θ - b) :=
    mul_nonneg (sub_nonneg.mpr hν) (sub_nonneg.mpr hbθ)
  have hfirst : an + (-c * L) < -κ * (1 - b) - ar := by
    nlinarith only [hcollision, hκb]
  have hsecond : an + (-ν * (A * (1 - η) - b)) < -κ * (1 - b) - ar := by
    nlinarith only [hgap, hprod]
  have hmax : an + max (-c * L) (-ν * (A * (1 - η) - b)) <
      -κ * (1 - b) - ar := by
    rcases le_total (-c * L) (-ν * (A * (1 - η) - b)) with h | h
    · simpa only [max_eq_right h] using hsecond
    · simpa only [max_eq_left h] using hfirst
  exact (not_lt_of_ge hlower) (lt_of_le_of_lt hupper hmax)

/-- Exact finite parameter values. This checks only the finite inequalities, not
existence of suitable approximations, separated weights, or asymptotic limits. -/
theorem parameter_witness_19_8 :
    let ν : ℚ := 19 / 8
    let θ : ℚ := 9 / 10
    let A : ℚ := 189 / 200
    let B : ℚ := 947 / 1000
    let C : ℚ := 527 / 500
    let η : ℚ := 1 / 1000
    0 < θ ∧ θ < A ∧ A < B ∧ B < 1 ∧ 1 < C ∧
    C * B < 1 ∧ B < C * θ ∧ C * θ < 1 ∧
    0 < ν * (A * (1 - η) - θ) - (1 - θ) := by
  norm_num

#print axioms normalized_center_identity
#print axioms polynomial_substitution
#print axioms clear_center_power
#print axioms determinant_comparison
#print axioms parameter_witness_19_8

end LogarithmExtension

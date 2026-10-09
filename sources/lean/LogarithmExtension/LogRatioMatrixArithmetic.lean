import LogarithmExtension.LogRatioBoundedJetMatrix
import LogarithmExtension.LogRatioDenominatorClearing
import OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic

/-!
# Arithmetic of the actual bounded two-base jet matrix

The original matrix is the one in `LogRatioBoundedJetMatrix`, not an
independently chosen matrix of assumed rank. Auxiliary diagonal scaling
clears the rational slopes without charging denominators to base orders.
-/

noncomputable section
namespace LogarithmExtension.LogRatio.MatrixArithmetic

open MvPolynomial OAI OAI.PiExponent PolynomialFrame DenominatorClearing
open scoped BigOperators

variable {m : ℕ}

def auxiliaryFactors (c : Fin m → ℂ) : Fin (m+2) → ℂ :=
  Fin.cases 1 (Fin.cases 1 c)

@[simp] theorem auxiliaryFactors_zero (c : Fin m → ℂ) : auxiliaryFactors c 0 = 1 := rfl
@[simp] theorem auxiliaryFactors_one (c : Fin m → ℂ) : auxiliaryFactors c 1 = 1 := rfl
@[simp] theorem auxiliaryFactors_aux (c : Fin m → ℂ) (i : Fin m) :
    auxiliaryFactors c i.succ.succ = c i := rfl

theorem product_auxiliaryFactors (c : Fin m → ℂ) (a : Fin (m+2) →₀ ℕ) :
    (∏ i, auxiliaryFactors c i ^ a i) = ∏ i, c i ^ a i.succ.succ := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp

def clearedForward (j : ℕ) (p q : Fin m → ℕ) (G : Fin m → Polynomial ℂ) :
    Poly m →ₐ[ℂ] Poly m :=
  aeval (Fin.cases (C (2^j) * (1+X 0)) (Fin.cases (C (3^j) * (1+X 1))
    (fun i => X i.succ.succ + C (q i : ℂ) * Polynomial.aeval (X 1) (G i) -
      C (p i : ℂ) * Polynomial.aeval (X 0) (G i))))

@[simp] theorem clearedForward_Y (j : ℕ) (p q : Fin m → ℕ) (G : Fin m → Polynomial ℂ) :
    clearedForward j p q G (X 0) = C (2^j) * (1+X 0) := by simp [clearedForward]

@[simp] theorem clearedForward_Z (j : ℕ) (p q : Fin m → ℕ) (G : Fin m → Polynomial ℂ) :
    clearedForward j p q G (X 1) = C (3^j) * (1+X 1) := by
  simp only [clearedForward, aeval_X]
  rfl

@[simp] theorem clearedForward_aux (j : ℕ) (p q : Fin m → ℕ)
    (G : Fin m → Polynomial ℂ) (i : Fin m) :
    clearedForward j p q G (X i.succ.succ) =
      X i.succ.succ + C (q i : ℂ) * Polynomial.aeval (X 1) (G i) -
        C (p i : ℂ) * Polynomial.aeval (X 0) (G i) := by simp [clearedForward]

theorem rescaled_forward (j : ℕ) (p q : Fin m → ℕ) (hq : ∀ i, q i ≠ 0)
    (G : Fin m → Polynomial ℂ) (P : Poly m) :
    diagonal (auxiliaryFactors (fun i => (q i : ℂ)⁻¹))
      (AlgebraicJet.forward (2^j) (3^j) (fun _ => 0)
        (fun i => (p i : ℂ)/(q i : ℂ)) G
        (diagonal (auxiliaryFactors (fun i => (q i : ℂ))) P)) =
      clearedForward j p q G P := by
  have h : (diagonal (auxiliaryFactors (fun i => (q i : ℂ)⁻¹))).comp
      ((AlgebraicJet.forward (2^j) (3^j) (fun _ => 0)
        (fun i => (p i : ℂ)/(q i : ℂ)) G).comp
        (diagonal (auxiliaryFactors (fun i => (q i : ℂ))))) =
      clearedForward j p q G := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i using Fin.cases with
    | zero => simp [AlgHom.comp_apply, algebraMap_eq]
    | succ k =>
      cases k using Fin.cases with
      | zero => simp [AlgHom.comp_apply, algebraMap_eq]
      | succ i =>
        have hqC : (q i : ℂ) ≠ 0 := by exact_mod_cast hq i
        simp only [AlgHom.comp_apply, diagonal_X, auxiliaryFactors_aux, map_mul,
          algHom_C, AlgebraicJet.forward_aux, map_sub, map_add, map_zero,
          zero_add, ← Polynomial.aeval_algHom_apply, auxiliaryFactors_zero,
          auxiliaryFactors_one, map_one, one_mul, algebraMap_eq, clearedForward_aux]
        have h1 : C (q i : ℂ) * C ((q i : ℂ)⁻¹) = (1 : Poly m) := by
          rw [← map_mul, mul_inv_cancel₀ hqC, map_one]
        have h2 : C (q i : ℂ) * C ((p i : ℂ)/(q i : ℂ)) = (C (p i : ℂ) : Poly m) := by
          rw [← map_mul]
          congr 1
          field_simp
        linear_combination h1 * X i.succ.succ - h2 * Polynomial.aeval (X 0) (G i)
  exact DFunLike.congr_fun h P

theorem scaled_coefficient (j : ℕ) (p q : Fin m → ℕ) (hq : ∀ i, q i ≠ 0)
    (G : Fin m → Polynomial ℂ) (a b : Fin (m+2) →₀ ℕ) :
    (∏ i, (q i : ℂ) ^ a i.succ.succ) * (∏ i, (q i : ℂ) ^ b i.succ.succ)⁻¹ *
      (AlgebraicJet.forward (2^j) (3^j) (fun _ => 0)
        (fun i => (p i : ℂ)/(q i : ℂ)) G (monomial a 1)).coeff b =
      (clearedForward j p q G (monomial a 1)).coeff b := by
  have h := congrArg (fun P : Poly m => P.coeff b)
    (rescaled_forward j p q hq G (monomial a 1))
  rw [diagonal_monomial, product_auxiliaryFactors, map_mul, algHom_C, algebraMap_eq,
    coeff_diagonal, product_auxiliaryFactors, coeff_C_mul] at h
  simp only [inv_pow, Finset.prod_inv_distrib] at h
  convert h using 1
  ring

theorem clearedForward_monomial (j : ℕ) (p q : Fin m → ℕ)
    (G : Fin m → Polynomial ℂ) (a : Fin (m+2) →₀ ℕ) :
    clearedForward j p q G (monomial a 1) =
      (C (2^j) * (1+X 0)) ^ a 0 * (C (3^j) * (1+X 1)) ^ a 1 *
        ∏ i, (X i.succ.succ + C (q i : ℂ) * Polynomial.aeval (X 1) (G i) -
          C (p i : ℂ) * Polynomial.aeval (X 0) (G i)) ^ a i.succ.succ := by
  rw [clearedForward, aeval_monomial, map_one, one_mul,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_succ,
    Fin.prod_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ, Fin.succ_zero_eq_one, TwoBaseFrame.fin_cases_one]
  ring

theorem cleared_auxiliary_integral (T p q : ℕ) (i : Fin m) :
    C (Nat.lcmUpto T : ℂ) *
      (X i.succ.succ + C (q : ℂ) * Polynomial.aeval (X 1) (PowerSeries.trunc T (PowerSeries.log ℂ)) -
        C (p : ℂ) * Polynomial.aeval (X 0) (PowerSeries.trunc T (PowerSeries.log ℂ))) ∈
      integralPolynomials (Fin (m+2)) := by
  let S := integralPolynomials (Fin (m+2))
  have h := S.sub_mem
    (S.add_mem (S.mul_mem (integral_C_nat (Nat.lcmUpto T)) (integral_X i.succ.succ))
      (S.mul_mem (integral_C_nat q) (cleared_log_aeval_integral T 1)))
    (S.mul_mem (integral_C_nat p) (cleared_log_aeval_integral T 0))
  convert h using 1
  ring

theorem cleared_monomial_integral (j : ℕ) (p q T e : Fin m → ℕ)
    (a : Fin (m+2) →₀ ℕ) (ha : ∀ i, a i.succ.succ ≤ e i) :
    C (∏ i, (Nat.lcmUpto (T i) : ℂ) ^ e i) *
      clearedForward j p q (CompactJetPolynomial.logPolynomials T) (monomial a 1) ∈
        integralPolynomials (Fin (m+2)) := by
  let S := integralPolynomials (Fin (m+2))
  have h2 : C (2^j : ℂ) ∈ S := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using integral_C_nat (σ := Fin (m+2)) (2^j)
  have h3 : C (3^j : ℂ) ∈ S := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using integral_C_nat (σ := Fin (m+2)) (3^j)
  have hbase := S.mul_mem
    (S.pow_mem (S.mul_mem h2 (S.add_mem S.one_mem (integral_X 0))) (a 0))
    (S.pow_mem (S.mul_mem h3 (S.add_mem S.one_mem (integral_X 1))) (a 1))
  have hprod := cleared_product_integral Finset.univ
    (fun i => Nat.lcmUpto (T i)) e (fun i => a i.succ.succ)
    (fun i => (X i.succ.succ + C (q i : ℂ) *
      Polynomial.aeval (X 1) (PowerSeries.trunc (T i) (PowerSeries.log ℂ)) -
      C (p i : ℂ) * Polynomial.aeval (X 0) (PowerSeries.trunc (T i) (PowerSeries.log ℂ)) : Poly m))
    (fun i _ => ha i) (fun i _ => cleared_auxiliary_integral (T i) (p i) (q i) i)
  have h := S.mul_mem hbase hprod
  rw [clearedForward_monomial]
  change C _ * (_ * _ * _) ∈ S
  convert h using 1
  unfold CompactJetPolynomial.logPolynomials
  ring

theorem scaled_entry_integral (j : ℕ) (p q T e : Fin m → ℕ)
    (hq : ∀ i, q i ≠ 0) (a b : Fin (m+2) →₀ ℕ) (ha : ∀ i, a i.succ.succ ≤ e i) :
    (∏ i, (Nat.lcmUpto (T i) : ℂ) ^ e i) *
      ((∏ i, (q i : ℂ) ^ a i.succ.succ) * (∏ i, (q i : ℂ) ^ b i.succ.succ)⁻¹ *
        (AlgebraicJet.forward (2^j) (3^j) (fun _ => 0)
          (fun i => (p i : ℂ)/(q i : ℂ)) (CompactJetPolynomial.logPolynomials T)
          (monomial a 1)).coeff b) ∈ (Int.castRingHom ℂ).range := by
  rw [scaled_coefficient j p q hq]
  have h := integral_coeff (cleared_monomial_integral j p q T e a ha) b
  simpa only [coeff_C_mul] using h

export OAI.PiExponent.MatrixArithmetic
  (logWeights columnScale rowScale columnScale_pos rowScale_pos log_columnScale log_rowScale
   truncationOrders ceil_log_weight_pos)

open BoundedJetMatrix
open InterpolationMatrix (exponentVector exponentVector_apply)

def clearingOrders (d : GeometryData) (H : ℚ) (i : Fin d.m) : ℕ :=
  ⌊(H : ℝ) / (d.curveDegreeWeights i.succ.succ : ℝ)⌋₊

def clearingDenominator (d : GeometryData) (T : Fin d.m → ℕ) (H : ℚ) : ℝ :=
  ∏ i, (Nat.lcmUpto (T i) : ℝ) ^ clearingOrders d H i

def selectedMinor (d : GeometryData) (T : Fin d.m → ℕ) (H : ℚ)
    (selection : Row d H → Column d H) : Matrix (Row d H) (Row d H) ℂ :=
  (matrix d T H).submatrix id selection

theorem column_coordinate_le_clearingOrders (d : GeometryData) (H : ℚ)
    (c : Column d H) (i : Fin d.m) : c.val i.succ.succ ≤ clearingOrders d H i := by
  have hw (k : Fin (d.m+2)) : (0 : ℝ) < d.curveDegreeWeights k := by
    exact_mod_cast d.curveDegreeWeights_pos k
  have hc := (mem_realWeightedSimplex hw).mp c.property
  apply Nat.le_floor
  apply (le_div_iff₀ (hw i.succ.succ)).mpr
  have hs := Finset.single_le_sum
    (fun k (_ : k ∈ Finset.univ) => mul_nonneg (hw k).le (Nat.cast_nonneg (c.val k)))
    (Finset.mem_univ i.succ.succ)
  exact (by simpa only [mul_comm] using hs.trans hc)

theorem clearingDenominator_pos (d : GeometryData) (T : Fin d.m → ℕ) (H : ℚ) :
    0 < clearingDenominator d T H := by
  apply Finset.prod_pos
  intro i _
  apply pow_pos
  exact_mod_cast Nat.pos_of_ne_zero (Nat.lcmUpto_ne_zero (T i))

theorem matrix_entry_eq_coefficient (d : GeometryData) (T : Fin d.m → ℕ) (H : ℚ)
    (row : Row d H) (col : Column d H) :
    matrix d T H row col =
      (AlgebraicJet.forward (2^row.1.val) (3^row.1.val) (fun _ => 0)
        (fun i => (d.p i : ℂ)/(d.q i : ℂ)) (CompactJetPolynomial.logPolynomials T)
        (monomial (exponentVector col.val) 1)).coeff (exponentVector row.2.val) := rfl

/-- Clearing the actual matrix costs auxiliary exponents only. -/
theorem matrix_entry_cleared_integer (d : GeometryData) (T : Fin d.m → ℕ) (H : ℚ)
    (row : Row d H) (col : Column d H) :
    (clearingDenominator d T H : ℂ) *
      (rowScale d.q (fun i => row.2.val i.succ.succ) : ℂ) *
        ((columnScale d.q (fun i => col.val i.succ.succ) : ℂ) * matrix d T H row col) ∈
      (Int.castRingHom ℂ).range := by
  have h := scaled_entry_integral row.1.val d.p d.q T (clearingOrders d H)
    (fun i => (d.q_pos i).ne') (exponentVector col.val) (exponentVector row.2.val)
    (fun i => column_coordinate_le_clearingOrders d H col i)
  rw [matrix_entry_eq_coefficient]
  simp only [clearingDenominator, rowScale, columnScale, Complex.ofReal_prod,
    Complex.ofReal_pow, Complex.ofReal_natCast, Complex.ofReal_inv]
  simp only [exponentVector_apply] at h
  convert h using 1
  ring

theorem matrix_entry_cleared (d : GeometryData) (T : Fin d.m → ℕ) (H : ℚ)
    (row : Row d H) (col : Column d H) :
    (clearingDenominator d T H : ℂ) *
      (rowScale d.q (fun i => row.2.val i.succ.succ) : ℂ) *
        ((columnScale d.q (fun i => col.val i.succ.succ) : ℂ) * matrix d T H row col) ∈
      GaussianInt.toComplex.range :=
  integer_mem_gaussian (matrix_entry_cleared_integer d T H row col)

def rowCost (d : GeometryData) (H : ℚ) : ℝ :=
  ∑ row : Row d H, ∑ i, (row.2.val i.succ.succ : ℝ) * Real.log (d.q i)

def columnCost (d : GeometryData) (H : ℚ) (selection : Row d H → Column d H) : ℝ :=
  ∑ row : Row d H, ∑ i, ((selection row).val i.succ.succ : ℝ) * Real.log (d.q i)

/-- An arithmetic lower bound for any nonzero full-row minor of the actual matrix. -/
theorem determinant_log_lower_bound (d : GeometryData) (T : Fin d.m → ℕ) (H : ℚ)
    (selection : Row d H → Column d H) (hdet : (selectedMinor d T H selection).det ≠ 0) :
    -(Fintype.card (Row d H) : ℝ) * Real.log (clearingDenominator d T H) +
      rowCost d H - columnCost d H selection ≤
        Real.log ‖(selectedMinor d T H selection).det‖ := by
  classical
  have h := Arithmetic.cleared_det_log_bound_with_denominator
    (selectedMinor d T H selection)
    (fun row => rowScale d.q (fun i => row.2.val i.succ.succ))
    (fun row => columnScale d.q (fun i => (selection row).val i.succ.succ))
    (clearingDenominator d T H) (clearingDenominator_pos d T H)
    (fun _ => rowScale_pos d.q_pos _) (fun _ => columnScale_pos d.q_pos _) hdet
    (fun row col => matrix_entry_cleared d T H row (selection col))
  simp only [log_rowScale d.q_pos, log_columnScale d.q_pos, Finset.sum_neg_distrib,
    sub_neg_eq_add, rowCost, columnCost] at h ⊢
  exact h

#print axioms matrix_entry_cleared_integer
#print axioms matrix_entry_cleared
#print axioms determinant_log_lower_bound

end LogarithmExtension.LogRatio.MatrixArithmetic

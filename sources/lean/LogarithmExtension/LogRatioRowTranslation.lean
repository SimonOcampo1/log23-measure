import LogarithmExtension.LogRatioNestedJets
import LogarithmExtension.LogRatioMatrixArithmetic
import OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation

/-!
# Exact bivariate row translation for the concrete two-base matrix

The shift is a finite polynomial identity in the auxiliary variables, with
bivariate series as coefficients. No estimate, convergence statement, or
irrationality bound is used to obtain the row identity.
-/

noncomputable section
namespace LogarithmExtension.LogRatio.AnalyticTranslation

open OAI OAI.PiExponent MvPolynomial NestedJets BoundedJetMatrix
open InterpolationMatrix (exponentVector exponentVector_apply)
open OAI.PiExponent.RowTranslation
open scoped BigOperators

variable {m : ℕ}

def logarithm (i : Fin 2) : BaseSeries := (PowerSeries.log ℂ).toMvPowerSeries i

def commonCoordinate (theta : ℂ) : BaseSeries := logarithm 1 - MvPowerSeries.C theta * logarithm 0

def tail (T : ℕ) (i : Fin 2) : BaseSeries :=
  embeddedPolynomial i (PowerSeries.trunc T (PowerSeries.log ℂ)) - logarithm i

def errorSeries (theta : ℂ) (r : Fin m → ℂ) (T : Fin m → ℕ) (i : Fin m) : BaseSeries :=
  MvPowerSeries.C (theta-r i) * logarithm 0 + tail (T i) 1 - MvPowerSeries.C (r i) * tail (T i) 0

def commonImage (cy cz theta : ℂ) (a : Fin (m+2) →₀ ℕ) : Nested m :=
  monomialImage cy cz (fun _ => commonCoordinate theta) a

theorem coordinate_translation (theta : ℂ) (r : Fin m → ℂ) (T : Fin m → ℕ) (i : Fin m) :
    commonCoordinate theta + errorSeries theta r T i =
      embeddedPolynomial 1 (PowerSeries.trunc (T i) (PowerSeries.log ℂ)) -
        MvPowerSeries.C (r i) * embeddedPolynomial 0 (PowerSeries.trunc (T i) (PowerSeries.log ℂ)) := by
  simp only [commonCoordinate, errorSeries, tail, map_sub]
  ring

theorem shift_monomialImage (cy cz : ℂ) (g h : Fin m → BaseSeries) (a : Fin (m+2) →₀ ℕ) :
    shift h (monomialImage cy cz g a) = monomialImage cy cz (fun i => h i + g i) a := by
  simp only [monomialImage, map_mul, shift_C, shift_add]

theorem actual_image_as_shift (cy cz theta : ℂ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (a : Fin (m+2) →₀ ℕ) :
    split (AlgebraicJet.forward cy cz (fun _ => 0) r (CompactJetPolynomial.logPolynomials T)
      (monomial a 1)) = shift (errorSeries theta r T) (commonImage cy cz theta a) := by
  rw [split_forward_monomial, commonImage, shift_monomialImage]
  congr 1
  funext i
  simpa only [CompactJetPolynomial.logPolynomials, add_comm] using
    (coordinate_translation theta r T i).symm

theorem monomialImage_coeff (cy cz : ℂ) (g : Fin m → BaseSeries)
    (a : Fin (m+2) →₀ ℕ) (beta : Fin m →₀ ℕ) :
    (monomialImage cy cz g a).coeff beta =
      ((∏ i, (a i.succ.succ).choose (beta i) : ℕ) : BaseSeries) *
        ((MvPowerSeries.C cy * (1+MvPowerSeries.X 0))^a 0 *
          (MvPowerSeries.C cz * (1+MvPowerSeries.X 1))^a 1) *
        ∏ i, g i ^ (a i.succ.succ-beta i) := by
  rw [monomialImage, coeff_C_mul]
  change _ * shiftCoefficient _ _ _ = _
  rw [shiftCoefficient_eq, Finset.prod_mul_distrib]
  simp only [auxiliaryIndex_apply, Nat.cast_prod]
  ring

theorem monomialImage_support_le (cy cz : ℂ) (g : Fin m → BaseSeries)
    (a : Fin (m+2) →₀ ℕ) {beta : Fin m →₀ ℕ}
    (hbeta : beta ∈ (monomialImage cy cz g a).support) : ∀ i, beta i ≤ a i.succ.succ := by
  intro i
  by_contra hi
  have hc : (∏ k, (a k.succ.succ).choose (beta k) : ℕ) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact Nat.choose_eq_zero_of_lt (by omega)
  have hz : (monomialImage cy cz g a).coeff beta = 0 := by
    rw [monomialImage_coeff, hc]
    simp
  exact (MvPolynomial.mem_support_iff.mp hbeta) hz

theorem commonImage_coeff (cy cz theta : ℂ) (a : Fin (m+2) →₀ ℕ) (beta : Fin m →₀ ℕ) :
    (commonImage cy cz theta a).coeff beta =
      ((∏ i, (a i.succ.succ).choose (beta i) : ℕ) : BaseSeries) *
        ((MvPowerSeries.C cy * (1+MvPowerSeries.X 0))^a 0 *
          (MvPowerSeries.C cz * (1+MvPowerSeries.X 1))^a 1) *
        commonCoordinate theta ^ (∑ i, (a i.succ.succ-beta i)) := by
  rw [commonImage, monomialImage_coeff, Finset.prod_pow_eq_pow_sum]

def rowScalar (h : Fin m → BaseSeries) (beta a : Fin m →₀ ℕ) (ell : Fin 2 →₀ ℕ) : ℂ :=
  ((∏ i, (a i).choose (beta i) : ℕ) : ℂ) *
    MvPowerSeries.coeff ell (∏ i, h i ^ (a i-beta i))

theorem coeff_shiftCoefficient (h : Fin m → BaseSeries) (beta a : Fin m →₀ ℕ)
    (ell : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff ell (shiftCoefficient h beta a) = rowScalar h beta a ell := by
  rw [shiftCoefficient_eq, Finset.prod_mul_distrib]
  have hc : (∏ i, ((a i).choose (beta i) : BaseSeries)) =
      MvPowerSeries.C ((∏ i, (a i).choose (beta i) : ℕ) : ℂ) := by simp
  rw [hc, MvPowerSeries.coeff_C_mul]
  rfl

theorem rowScalar_ne_zero_le (h : Fin m → BaseSeries) (beta a : Fin m →₀ ℕ)
    (ell : Fin 2 →₀ ℕ) (hne : rowScalar h beta a ell ≠ 0) : beta ≤ a := by
  intro i
  by_contra hi
  have hc : (∏ k, (a k).choose (beta k) : ℕ) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact Nat.choose_eq_zero_of_lt (by omega)
  exact hne (by simp [rowScalar, hc])

/-- Exact finite convolution in the two base coefficient indices. -/
theorem row_coefficient_identity (h : Fin m → BaseSeries) (P : Nested m) (beta : Fin m →₀ ℕ)
    (S : Finset (Fin m →₀ ℕ)) (hP : P.support ⊆ S) (ell : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff ell ((shift h P).coeff beta) =
      ∑ a ∈ S, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal ell,
        rowScalar h beta a kl.1 * MvPowerSeries.coeff kl.2 (P.coeff a) := by
  rw [coeff_shift_over h P beta S hP]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [mul_comm, MvPowerSeries.coeff_mul]
  simp only [coeff_shiftCoefficient]

def transverseIndices (d : GeometryData) (H : ℚ) : Finset (Fin d.m →₀ ℕ) :=
  MatrixTranslation.transverseIndices (fun i => (d.curveDegreeWeights i.succ.succ : ℝ)) H

theorem column_auxiliary_weight_le (d : GeometryData) (H : ℚ) (col : Column d H) :
    (∑ i : Fin d.m, (d.curveDegreeWeights i.succ.succ : ℝ) * col.val i.succ.succ) ≤ H := by
  have hw (i : Fin (d.m+2)) : (0 : ℝ) < d.curveDegreeWeights i := by
    exact_mod_cast d.curveDegreeWeights_pos i
  have hc := (mem_realWeightedSimplex hw).mp col.property
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at hc
  simp only [Fin.succ_zero_eq_one] at hc
  have h0 := mul_nonneg (hw 0).le (Nat.cast_nonneg (col.val 0) : (0 : ℝ) ≤ col.val 0)
  have h1 := mul_nonneg (hw 1).le (Nat.cast_nonneg (col.val 1) : (0 : ℝ) ≤ col.val 1)
  linarith

theorem commonImage_support_subset (d : GeometryData) (H : ℚ) (theta : ℂ)
    (row : Row d H) (col : Column d H) :
    (commonImage (d.centerY row.1) (d.centerZ row.1) theta (exponentVector col.val)).support ⊆
      transverseIndices d H := by
  intro a ha
  have hw (i : Fin d.m) : (0 : ℝ) < d.curveDegreeWeights i.succ.succ := by
    exact_mod_cast d.curveDegreeWeights_pos i.succ.succ
  apply (MatrixTranslation.mem_transverseIndices _ _ hw a).mpr
  apply le_trans _ (column_auxiliary_weight_le d H col)
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (hw i).le
  exact_mod_cast monomialImage_support_le _ _ _ _ ha i

/-- Each entry of the actual matrix is a finite sum of common coefficient tests.
The index set and the scalar multiplier do not depend on the selected column. -/
theorem matrix_entry_translation (d : GeometryData) (T : Fin d.m → ℕ) (H : ℚ) (theta : ℂ)
    (row : Row d H) (col : Column d H) :
    matrix d T H row col =
      ∑ a ∈ transverseIndices d H,
        ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal (baseIndex (exponentVector row.2.val)),
          rowScalar (errorSeries theta d.slopes T) (auxiliaryIndex (exponentVector row.2.val)) a kl.1 *
            MvPowerSeries.coeff kl.2
              ((commonImage (d.centerY row.1) (d.centerZ row.1) theta (exponentVector col.val)).coeff a) := by
  rw [LogarithmExtension.LogRatio.MatrixArithmetic.matrix_entry_eq_coefficient,
    ← coeff_split, actual_image_as_shift _ _ theta]
  exact row_coefficient_identity _ _ _ _ (commonImage_support_subset d H theta row col) _

abbrev RowChoice (d : GeometryData) (H : ℚ) (row : Row d H) :=
  ↥(transverseIndices d H) ×
    ↥(Finset.HasAntidiagonal.antidiagonal (baseIndex (exponentVector row.2.val)))

abbrev ChoiceFamily (d : GeometryData) (H : ℚ) := ∀ row : Row d H, RowChoice d H row

def choiceScalar (d : GeometryData) (T : Fin d.m → ℕ) (H : ℚ) (theta : ℂ)
    (row : Row d H) (t : RowChoice d H row) : ℂ :=
  rowScalar (errorSeries theta d.slopes T) (auxiliaryIndex (exponentVector row.2.val)) t.1.val t.2.val.1

def choiceEntry (d : GeometryData) (H : ℚ) (theta : ℂ) (row : Row d H) (col : Column d H)
    (t : RowChoice d H row) : ℂ :=
  MvPowerSeries.coeff t.2.val.2
    ((commonImage (d.centerY row.1) (d.centerZ row.1) theta (exponentVector col.val)).coeff t.1.val)

def choiceMatrix (d : GeometryData) (H : ℚ) (theta : ℂ) (selection : Row d H → Column d H)
    (f : ChoiceFamily d H) : Matrix (Row d H) (Row d H) ℂ :=
  fun row col => choiceEntry d H theta row (selection col) (f row)

theorem matrix_entry_sum_choices (d : GeometryData) (T : Fin d.m → ℕ) (H : ℚ) (theta : ℂ)
    (row : Row d H) (col : Column d H) :
    matrix d T H row col = ∑ t : RowChoice d H row,
      choiceScalar d T H theta row t * choiceEntry d H theta row col t := by
  classical
  rw [matrix_entry_translation d T H theta, Fintype.sum_prod_type]
  rw [← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.sum_coe_sort]
  rfl

/-- Exact finite expansion of the actual determinant into translated determinants. -/
theorem determinant_translation (d : GeometryData) (T : Fin d.m → ℕ) (H : ℚ) (theta : ℂ)
    (selection : Row d H → Column d H) :
    (LogarithmExtension.LogRatio.MatrixArithmetic.selectedMinor d T H selection).det =
      ∑ f : ChoiceFamily d H, (∏ row, choiceScalar d T H theta row (f row)) *
        (choiceMatrix d H theta selection f).det := by
  classical
  have he : LogarithmExtension.LogRatio.MatrixArithmetic.selectedMinor d T H selection =
      (fun row col => ∑ t : RowChoice d H row,
        choiceScalar d T H theta row t * choiceEntry d H theta row (selection col) t) := by
    funext row col
    exact matrix_entry_sum_choices d T H theta row (selection col)
  rw [he]
  exact MatrixTranslation.det_dependent_row_sum _ _

#print axioms matrix_entry_translation
#print axioms determinant_translation

end LogarithmExtension.LogRatio.AnalyticTranslation

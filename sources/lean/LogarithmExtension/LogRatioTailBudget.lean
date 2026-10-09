import LogarithmExtension.LogRatioRowTranslation
import OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds

/-!
# Truncation budgets for the two-base analytic row expansion

The tail counts below are actual summands of the concrete row scalar.
A nonzero coefficient forces their weighted cost to be small. Neither
the approximation bound nor an analytic determinant bound is assumed.
-/

noncomputable section
namespace LogarithmExtension.LogRatio.AnalyticTranslation

open OAI OAI.PiExponent NestedJets
open scoped BigOperators

variable {m : ℕ}

theorem tail_toMvPowerSeries (T : ℕ) (i : Fin 2) :
    tail T i = (RowTranslation.tail T (PowerSeries.log ℂ)).toMvPowerSeries i := by
  simp only [tail, RowTranslation.tail, map_sub,
    AlgebraicJet.polynomial_toMvPowerSeries, embeddedPolynomial, logarithm]

theorem coeff_tail_of_degree_lt (T : ℕ) (i : Fin 2) (ell : Fin 2 →₀ ℕ)
    (h : ell.degree < T) : MvPowerSeries.coeff ell (tail T i) = 0 := by
  rw [tail_toMvPowerSeries, FormalJet.coeff_toMvPowerSeries]
  split_ifs with he
  · apply RowTranslation.coeff_tail_of_lt
    have hd := congrArg Finsupp.degree he
    simp only [Finsupp.degree_single] at hd
    omega
  · rfl

theorem order_tail (T : ℕ) (i : Fin 2) : (T : ℕ∞) ≤ (tail T i).order :=
  MvPowerSeries.nat_le_order (fun ell h => coeff_tail_of_degree_lt T i ell h)

def mixedTail (r : ℂ) (T : ℕ) : BaseSeries :=
  tail T 1 - MvPowerSeries.C r * tail T 0

theorem errorSeries_eq (theta : ℂ) (r : Fin m → ℂ) (T : Fin m → ℕ) (i : Fin m) :
    errorSeries theta r T i =
      MvPowerSeries.C (theta-r i) * logarithm 0 + mixedTail (r i) (T i) := by
  simp only [errorSeries, mixedTail]
  ring

theorem order_mixedTail (r : ℂ) (T : ℕ) : (T : ℕ∞) ≤ (mixedTail r T).order := by
  apply MvPowerSeries.nat_le_order
  intro ell h
  simp only [mixedTail, map_sub, MvPowerSeries.coeff_C_mul,
    coeff_tail_of_degree_lt T 1 ell h, coeff_tail_of_degree_lt T 0 ell h, mul_zero, sub_self]

theorem order_mixedTail_prod (r : Fin m → ℂ) (T b : Fin m → ℕ) :
    ((∑ i, b i * T i : ℕ) : ℕ∞) ≤ (∏ i, mixedTail (r i) (T i) ^ b i).order := by
  calc
    ((∑ i, b i * T i : ℕ) : ℕ∞) = ∑ i, b i • (T i : ℕ∞) := by
      simp [nsmul_eq_mul]
    _ ≤ ∑ i, b i • (mixedTail (r i) (T i)).order :=
      Finset.sum_le_sum (fun i _ => nsmul_le_nsmul_right (order_mixedTail _ _) _)
    _ ≤ ∑ i, (mixedTail (r i) (T i) ^ b i).order :=
      Finset.sum_le_sum (fun i _ => MvPowerSeries.le_order_pow _)
    _ ≤ (∏ i, mixedTail (r i) (T i) ^ b i).order := MvPowerSeries.le_order_prod _ _

/-- Multiplication by an arbitrary formal series cannot recover a forbidden
low-order coefficient of the product of tails. -/
theorem mixedTail_budget_nat (r : Fin m → ℂ) (T b : Fin m → ℕ)
    (g : BaseSeries) (ell : Fin 2 →₀ ℕ)
    (hne : MvPowerSeries.coeff ell (g * ∏ i, mixedTail (r i) (T i) ^ b i) ≠ 0) :
    ∑ i, b i * T i ≤ ell.degree := by
  have ho : ((∑ i, b i * T i : ℕ) : ℕ∞) ≤
      (g * ∏ i, mixedTail (r i) (T i) ^ b i).order := by
    calc
      _ ≤ (∏ i, mixedTail (r i) (T i) ^ b i).order := order_mixedTail_prod r T b
      _ ≤ g.order + (∏ i, mixedTail (r i) (T i) ^ b i).order :=
        le_add_of_nonneg_left (bot_le : (0 : ℕ∞) ≤ g.order)
      _ ≤ _ := MvPowerSeries.le_order_mul
  exact_mod_cast ho.trans (MvPowerSeries.order_le hne)

theorem mixedTail_weight_budget (r : Fin m → ℂ) (T b : Fin m → ℕ)
    (g : BaseSeries) (ell : Fin 2 →₀ ℕ) (w : Fin m → ℝ) (v F : ℝ)
    (hv : 0 ≤ v) (hF : 0 < F) (hT : ∀ i, F * w i ≤ v * T i)
    (hne : MvPowerSeries.coeff ell (g * ∏ i, mixedTail (r i) (T i) ^ b i) ≠ 0) :
    MatrixTranslationBounds.weight w b ≤ v * ell.degree / F := by
  apply (le_div_iff₀ hF).2
  calc
    MatrixTranslationBounds.weight w b * F = ∑ i, (b i : ℝ) * (F * w i) := by
      simp only [MatrixTranslationBounds.weight, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i, (b i : ℝ) * (v * T i) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hT i) (Nat.cast_nonneg _))
    _ = v * ((∑ i, b i * T i : ℕ) : ℝ) := by
      simp only [Nat.cast_sum, Nat.cast_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ v * ell.degree :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast mixedTail_budget_nat r T b g ell hne) hv

def refinedScalar (epsilon r : Fin m → ℂ) (T : Fin m → ℕ) (beta a : Fin m →₀ ℕ)
    (b : ∀ i, Fin (a i-beta i+1)) (ell : Fin 2 →₀ ℕ) : ℂ :=
  ((∏ i, (a i).choose (beta i) * (a i-beta i).choose (b i) : ℕ) : ℂ) *
    (∏ i, epsilon i ^ (a i-beta i-b i)) *
      MvPowerSeries.coeff ell (logarithm 0 ^ (∑ i, (a i-beta i-b i)) *
        ∏ i, mixedTail (r i) (T i) ^ (b i : ℕ))

theorem coefficient_error_mixedTail (epsilon r : Fin m → ℂ) (T n : Fin m → ℕ)
    (ell : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff ell
        (∏ i, (MvPowerSeries.C (epsilon i) * logarithm 0 + mixedTail (r i) (T i)) ^ n i) =
      ∑ b : (∀ i, Fin (n i+1)), ((∏ i, (n i).choose (b i) : ℕ) : ℂ) *
        (∏ i, epsilon i ^ (n i-b i)) *
          MvPowerSeries.coeff ell (logarithm 0 ^ (∑ i, (n i-b i)) *
            ∏ i, mixedTail (r i) (T i) ^ (b i : ℕ)) := by
  rw [RowTranslation.product_add_expansion]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod,
    Finset.prod_pow_eq_pow_sum]
  rw [show ((∏ i, (n i).choose (b i) : ℕ) : BaseSeries) =
    MvPowerSeries.C (((∏ i, (n i).choose (b i) : ℕ) : ℂ)) by simp]
  simp only [mul_assoc, MvPowerSeries.coeff_C_mul]

/-- The tail-refined scalar estimates will therefore bound the actual row
multiplier, rather than a surrogate matrix. -/
theorem rowScalar_eq_sum_refined (theta : ℂ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (beta a : Fin m →₀ ℕ) (ell : Fin 2 →₀ ℕ) :
    rowScalar (errorSeries theta r T) beta a ell =
      ∑ b : (∀ i, Fin (a i-beta i+1)), refinedScalar (fun i => theta-r i) r T beta a b ell := by
  simp only [rowScalar, errorSeries_eq, coefficient_error_mixedTail, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp only [refinedScalar, Finset.prod_mul_distrib, Nat.cast_mul]
  ring

end LogarithmExtension.LogRatio.AnalyticTranslation

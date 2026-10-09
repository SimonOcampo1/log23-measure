import LogarithmExtension.Basic
import OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic
import OAI.NumberTheory.PiExponent.Analysis.Collision

/-!
# Exact analytic transfer and collision bound for logarithmic centres

The nonperiodic exponential contributes base^(j*h) to each matrix entry.
This factor is retained in the common entire functions, not discarded as an
error or treated as a row-only or column-only determinant multiplier.
-/

noncomputable section
namespace LogarithmExtension.AnalyticTranslation

open OAI OAI.PiExponent
open OAI.PiExponent.AnalyticCollision OAI.PiExponent.PeriodAnalytic
open scoped BigOperators

def periodMonomial {m : ℕ} (base : ℂ) (j : ℕ) (ell : ℂ) (h : ℕ)
    (a : Fin m → ℕ) : MvPolynomial (Fin m) (PowerSeries ℂ) :=
  MvPolynomial.C (PowerSeries.C (base ^ (j*h))) * MatrixTranslation.periodMonomial j ell h a

def matrixEntry {m : ℕ} (base : ℂ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (j s : ℕ) (b : Fin m → ℕ) (h : ℕ) (a : Fin m → ℕ) : ℂ :=
  base ^ (j*h) * InterpolationMatrix.entry r (fun i => InterpolationMatrix.truncatedLog (T i)) j s b h a

theorem periodFunction_eq_exponentialMonomial
    (base ell b : ℂ) (hexp : Complex.exp ell = base) (j h d : ℕ)
    {t : ℂ} (ht : ‖t‖ < 1) :
    PeriodAnalytic.periodFunction (b * base ^ (j*h)) ((j : ℂ)*ell) h d t =
      exponentialMonomial b (h : ℂ) d ((j : ℂ)*ell + Complex.log (1+t)) := by
  have ht0 : 1+t ≠ 0 := by
    intro heq
    have heq' : t = -1 := by linear_combination heq
    simp [heq'] at ht
  unfold PeriodAnalytic.periodFunction exponentialMonomial
  rw [Complex.exp_nat_mul, Complex.exp_add, Complex.exp_nat_mul, hexp,
    Complex.exp_log ht0, mul_pow, ← pow_mul]
  ring

theorem rowTest_exponentialMonomial_eq_coeff
    (base ell b : ℂ) (hexp : Complex.exp ell = base) (j h d k : ℕ) :
    rowTest k (fun t => exponentialMonomial b (h : ℂ) d
      ((j : ℂ)*ell + Complex.log (1+t))) =
    PowerSeries.coeff k (PeriodAnalytic.periodSeries (b * base ^ (j*h)) ((j : ℂ)*ell) h d) := by
  rw [← rowTest_periodFunction_eq_coeff]
  apply rowTest_congr_sphere
  intro t ht
  symm
  apply periodFunction_eq_exponentialMonomial base ell b hexp j h d
  have hn : ‖t‖ = (1/2 : ℝ) := by simpa only [Metric.mem_sphere, dist_zero_right] using ht
  rw [hn]
  norm_num

theorem periodMonomial_coeff_eq_rowTest {m : ℕ}
    (base ell : ℂ) (hexp : Complex.exp ell = base) (j h k : ℕ)
    (a : Fin m → ℕ) (A : Fin m →₀ ℕ) :
    PowerSeries.coeff k ((periodMonomial base j ell h a).coeff A) =
      rowTest k (fun t => PeriodAnalytic.columnFunction h a A
        ((j : ℂ)*ell + Complex.log (1+t))) := by
  unfold PeriodAnalytic.columnFunction
  rw [rowTest_exponentialMonomial_eq_coeff base ell _ hexp]
  congr 1
  rw [periodMonomial, MvPolynomial.coeff_C_mul, MatrixTranslation.periodMonomial_coeff]
  simp only [PeriodAnalytic.periodSeries, MatrixTranslation.periodCoordinate, map_mul, map_natCast]
  ring

/-- Full formal row expansion, with the exponential centre factor preserved. -/
theorem matrix_entry_translation_choices {m : ℕ} (base : ℂ)
    (r : Fin m → ℂ) (T : Fin m → ℕ) (j s : ℕ) (ell : ℂ)
    (b : Fin m → ℕ) (h : ℕ) (a : Fin m → ℕ)
    (S : Finset (Fin m →₀ ℕ)) (hp : (MatrixTranslation.periodMonomial j ell h a).support ⊆ S) :
    matrixEntry base r T j s b h a =
      ∑ t : RowTranslation.RowChoices S (InterpolationMatrix.exponentVector b) s,
        RowTranslation.rowScalar (fun i => (j : ℂ) * (r i - ell))
          (fun i => RowTranslation.tail (T i) (PowerSeries.log ℂ))
          (InterpolationMatrix.exponentVector b) t.1.1 t.2.1 t.2.2 *
          PowerSeries.coeff (s - t.2.2) ((periodMonomial base j ell h a).coeff t.1.1) := by
  rw [matrixEntry, MatrixTranslation.matrix_entry_translation_choices r T j s ell b h a S hp,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  simp only [periodMonomial, MvPolynomial.coeff_C_mul, PowerSeries.coeff_C_mul]
  ring

def radiusFactor (ell : ℂ) : ℝ := 100 * (1 + ‖ell‖)

theorem radiusFactor_ge (ell : ℂ) : 100 ≤ radiusFactor ell := by
  unfold radiusFactor
  nlinarith [norm_nonneg ell]

theorem centre_radius_bound (ell : ℂ) {K j : ℕ} (hK : 0 < K) (hj : j < K) :
    ‖(j : ℂ)*ell‖ + 3/4 ≤ (radiusFactor ell * (K : ℝ))/2 := by
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hjK : (j : ℝ) ≤ K := by exact_mod_cast hj.le
  have hp := mul_le_mul_of_nonneg_right hjK (norm_nonneg ell)
  rw [norm_mul, Complex.norm_natCast]
  unfold radiusFactor
  nlinarith [norm_nonneg ell]

def holomorphicError (ell : ℂ) (K : ℕ) (w0 v0 wstar : ℝ) : ℝ :=
  radiusFactor ell * K / w0 + Real.log 2 / v0 + Real.log (2 * radiusFactor ell * K) / wstar

/-- The same quadratic collision saving as for pi, now at nonperiodic centres. -/
theorem formal_logarithm_collision_bound
    {m : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (base ell : ℂ) (hexp : Complex.exp ell = base)
    (group : ι → κ) (transverse : κ → Fin m →₀ ℕ)
    (j k h : ι → ℕ) (a : ι → Fin m → ℕ) (w : Fin m → ℝ)
    {K : ℕ} {H w0 v0 wstar : ℝ}
    (hK : 0 < K) (hH : 0 < H) (hw0 : 0 < w0) (hws : 0 < wstar)
    (hw : ∀ i, wstar ≤ w i) (hj : ∀ r, j r < K)
    (hcol : ∀ c, w0 * h c + ∑ i, w i * a c i ≤ H)
    (hk : ((∑ r, k r : ℕ) : ℝ) ≤ (Fintype.card ι : ℝ) * H / v0) :
    ‖Matrix.det (fun r c => PowerSeries.coeff (k r)
      ((periodMonomial base (j r) ell (h c) (a c)).coeff (transverse (group r))))‖ ≤
      Real.exp (-(Real.log 2 / 4) *
        (∑ A, (Collision.multiplicity Finset.univ group A : ℝ) ^ 2) +
        (Fintype.card ι : ℝ) * H *
          (holomorphicError ell K w0 v0 wstar + Collision.collisionRemainder (Fintype.card ι) H)) := by
  have hfac : 0 < radiusFactor ell := lt_of_lt_of_le (by norm_num) (radiusFactor_ge ell)
  let R : NNReal := ⟨radiusFactor ell * (K : ℝ), by positivity⟩
  have hR : 0 < R := by change (0 : ℝ) < radiusFactor ell * K; positivity
  have hR1 : (1 : ℝ) ≤ R := by
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
    change (1 : ℝ) ≤ radiusFactor ell * K
    nlinarith [radiusFactor_ge ell]
  have hb := AnalyticCollision.translated_row_determinant_exp_bound
    group (fun A c => PeriodAnalytic.columnFunction (h c) (a c) (transverse A))
    (fun r => (j r : ℂ)*ell) k R hR hH
    (fun A c => PeriodAnalytic.differentiable_columnFunction _ _ _)
    (A := (R : ℝ) / w0 + Real.log (2 * (R : ℝ)) / wstar) (v := v0)
    (fun A c z hz => PeriodAnalytic.norm_columnFunction_le (h c) (a c) (transverse A) w
      hR1 hH.le hw0 hws hw (hcol c)
      (by simpa only [Metric.mem_sphere, dist_zero_right] using hz.le))
    (fun r => centre_radius_bound ell hK (hj r)) hk
  have hRv : (R : ℝ) = radiusFactor ell * K := rfl
  rw [hRv] at hb
  simp_rw [periodMonomial_coeff_eq_rowTest base ell hexp]
  convert! hb using 1
  congr 1
  unfold holomorphicError
  rw [← mul_assoc 2 (radiusFactor ell) (K : ℝ)]
  ring

#print axioms matrix_entry_translation_choices
#print axioms formal_logarithm_collision_bound

end LogarithmExtension.AnalyticTranslation

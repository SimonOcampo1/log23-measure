import LogarithmExtension.LogRatioScalarBound
import LogarithmExtension.AnalyticTranslation
import OAI.NumberTheory.PiExponent.Analysis.AnalyticRowSeries

/-!
# The actual common two-base coefficient series

The power of z' - theta*z is expanded into a finite sum of separated
exponential monomials. Products of their absolutely convergent translated
Taylor series give the required series over pairs of Taylor degrees.
The coefficient identity retains both multiplicative center factors.
-/

noncomputable section
namespace LogarithmExtension.LogRatio.CommonTaylor

open OAI OAI.PiExponent NestedJets
open LogarithmExtension.LogRatio.AnalyticTranslation
open OAI.PiExponent.AnalyticCollision
open scoped BigOperators

def binomialScalar (b theta : ℂ) (N l : ℕ) : ℂ :=
  b * (N.choose l : ℂ) * (-theta)^l

def baseMonomial (b cy cz theta : ℂ) (h k N : ℕ) : BaseSeries :=
  MvPowerSeries.C b *
    (MvPowerSeries.C cy * (1+MvPowerSeries.X 0))^h *
    (MvPowerSeries.C cz * (1+MvPowerSeries.X 1))^k * commonCoordinate theta^N

theorem baseMonomial_expansion (b cy cz theta z0 z1 : ℂ) (h k N : ℕ)
    (hcenter : z1 = theta*z0) :
    baseMonomial b cy cz theta h k N =
      ∑ l ∈ Finset.range (N+1), MvPowerSeries.C (binomialScalar b theta N l) *
        ((PeriodAnalytic.periodSeries (cy^h) z0 h l).toMvPowerSeries 0 *
          (PeriodAnalytic.periodSeries (cz^k) z1 k (N-l)).toMvPowerSeries 1) := by
  have he : commonCoordinate theta =
      MvPowerSeries.C (-theta) *
        (PowerSeries.C z0 + PowerSeries.log ℂ).toMvPowerSeries 0 +
        (PowerSeries.C z1 + PowerSeries.log ℂ).toMvPowerSeries 1 := by
    simp only [commonCoordinate, logarithm, map_add, PowerSeries.toMvPowerSeries_C,
      hcenter, map_mul, map_neg]
    ring
  rw [baseMonomial, he, add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  simp only [PeriodAnalytic.periodSeries, binomialScalar, map_mul, map_add, map_pow,
    map_one, PowerSeries.toMvPowerSeries_C, PowerSeries.toMvPowerSeries_X, map_natCast,
    mul_pow]
  ring

theorem coeff_baseMonomial_expansion (b cy cz theta z0 z1 : ℂ) (h k N : ℕ)
    (hcenter : z1 = theta*z0) (ell : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff ell (baseMonomial b cy cz theta h k N) =
      ∑ l ∈ Finset.range (N+1), binomialScalar b theta N l *
        (PowerSeries.coeff (ell 0) (PeriodAnalytic.periodSeries (cy^h) z0 h l) *
          PowerSeries.coeff (ell 1) (PeriodAnalytic.periodSeries (cz^k) z1 k (N-l))) := by
  rw [baseMonomial_expansion b cy cz theta z0 z1 h k N hcenter]
  simp only [map_sum, MvPowerSeries.coeff_C_mul, coeff_separated_series]

def oneTest (center : ℂ) (ell : ℕ) (R : ℝ) (d : ℕ) : ℂ :=
  rowTest ell (fun t => ((center+Complex.log (1+t))/(R : ℂ))^d)

def pairTest (z0 z1 : ℂ) (ell : Fin 2 →₀ ℕ) (R : ℝ) (p : ℕ × ℕ) : ℂ :=
  oneTest z0 (ell 0) R p.1 * oneTest z1 (ell 1) R p.2

def oneCoefficient (h l : ℕ) (R : ℝ) (d : ℕ) : ℂ :=
  normalizedTaylorCoeff (exponentialMonomial 1 (h : ℂ) l) R d

def commonCoefficient (b theta : ℂ) (h k N : ℕ) (R : ℝ) (p : ℕ × ℕ) : ℂ :=
  ∑ l ∈ Finset.range (N+1), binomialScalar b theta N l *
    (oneCoefficient h l R p.1 * oneCoefficient k (N-l) R p.2)

theorem norm_oneCoefficient_le (h l d : ℕ) {R : ℝ} (hR : 0 < R) :
    ‖oneCoefficient h l R d‖ ≤ Real.exp ((h : ℝ)*R)*R^l := by
  apply norm_normalizedTaylorCoeff_le hR
  intro z hz
  have hzR : ‖z‖ ≤ R := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hz.le
  simpa only [norm_one, one_mul, Complex.norm_natCast] using
    norm_exponentialMonomial_le (1 : ℂ) (h : ℂ) l hR.le hzR

theorem hasSum_oneCoefficient (cy center : ℂ) (hexp : Complex.exp center = cy)
    (h l ell : ℕ) {R : NNReal} (hR : 0 < R)
    (hc : ‖center‖+3/4 ≤ (R : ℝ)/2) :
    HasSum (fun d => oneTest center ell R d * oneCoefficient h l R d)
      (PowerSeries.coeff ell (PeriodAnalytic.periodSeries (cy^h) center h l)) := by
  have hs := hasSum_translated_row (differentiable_exponentialMonomial (1 : ℂ) (h : ℂ) l)
    hR (D := Real.exp ((h : ℝ)*R)*(R : ℝ)^l) (by positivity)
    (fun z hz => by
      simpa only [norm_one, one_mul, Complex.norm_natCast] using
        norm_exponentialMonomial_le (1 : ℂ) (h : ℂ) l (show (0 : ℝ) ≤ R from R.2)
          (by simpa only [Metric.mem_sphere, dist_zero_right] using hz.le)) hc ell
  have he := LogarithmExtension.AnalyticTranslation.rowTest_exponentialMonomial_eq_coeff
    cy center 1 hexp 1 h l ell
  simp only [Nat.cast_one, one_mul] at he
  rw [he] at hs
  exact hs

theorem hasSum_pair_mul {f g : ℕ → ℂ} {x y : ℂ}
    (hf : HasSum f x) (hg : HasSum g y) :
    HasSum (fun p : ℕ × ℕ => f p.1*g p.2) (x*y) := by
  exact hf.mul hg (summable_mul_of_summable_norm hf.summable.norm hg.summable.norm)

theorem hasSum_baseMonomial (b cy cz theta z0 z1 : ℂ) (h k N : ℕ)
    (hy : Complex.exp z0 = cy) (hz : Complex.exp z1 = cz) (hcenter : z1 = theta*z0)
    (ell : Fin 2 →₀ ℕ) {R : NNReal} (hR : 0 < R)
    (hc0 : ‖z0‖+3/4 ≤ (R : ℝ)/2) (hc1 : ‖z1‖+3/4 ≤ (R : ℝ)/2) :
    HasSum (fun p => pairTest z0 z1 ell R p * commonCoefficient b theta h k N R p)
      (MvPowerSeries.coeff ell (baseMonomial b cy cz theta h k N)) := by
  have hs (l : ℕ) : HasSum (fun p : ℕ × ℕ => binomialScalar b theta N l *
        ((oneTest z0 (ell 0) R p.1 * oneCoefficient h l R p.1) *
          (oneTest z1 (ell 1) R p.2 * oneCoefficient k (N-l) R p.2)))
      (binomialScalar b theta N l *
        (PowerSeries.coeff (ell 0) (PeriodAnalytic.periodSeries (cy^h) z0 h l) *
          PowerSeries.coeff (ell 1) (PeriodAnalytic.periodSeries (cz^k) z1 k (N-l)))) := by
    have hy' := hasSum_oneCoefficient cy z0 hy h l (ell 0) hR hc0
    have hz' := hasSum_oneCoefficient cz z1 hz k (N-l) (ell 1) hR hc1
    exact (hasSum_pair_mul hy' hz').mul_left (binomialScalar b theta N l)
  have hs' := hasSum_sum (s := Finset.range (N+1)) (fun l _ => hs l)
  rw [← coeff_baseMonomial_expansion b cy cz theta z0 z1 h k N hcenter ell] at hs'
  apply hs'.congr_fun
  intro p
  simp only [pairTest, commonCoefficient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- The norm estimate on the pair of coefficient tests is independent of
the selected polynomial column. -/
theorem norm_pairTest_le (z0 z1 : ℂ) (ell : Fin 2 →₀ ℕ) {R : ℝ} (hR : 0 < R)
    (hc0 : ‖z0‖+3/4 ≤ R/2) (hc1 : ‖z1‖+3/4 ≤ R/2) (p : ℕ × ℕ) :
    ‖pairTest z0 z1 ell R p‖ ≤ (2 : ℝ)^(ell 0+ell 1)*(1/2 : ℝ)^(p.1+p.2) := by
  rw [pairTest, norm_mul]
  apply (mul_le_mul (norm_rowTest_shifted_power_le hR hc0 (ell 0) p.1)
    (norm_rowTest_shifted_power_le hR hc1 (ell 1) p.2) (norm_nonneg _) (by positivity)).trans_eq
  simp only [pow_add]
  ring

theorem commonImage_coeff_eq_baseMonomial {m : ℕ} (cy cz theta : ℂ)
    (a : Fin (m+2) →₀ ℕ) (beta : Fin m →₀ ℕ) :
    (commonImage cy cz theta a).coeff beta =
      baseMonomial ((∏ i, (a i.succ.succ).choose (beta i) : ℕ) : ℂ) cy cz theta
        (a 0) (a 1) (∑ i, (a i.succ.succ-beta i)) := by
  rw [commonImage_coeff]
  simp only [baseMonomial, map_natCast]
  ring

/-- Actual formal common coefficients, rather than an abstract function
postulated to have a Taylor series, satisfy the paired expansion. -/
theorem hasSum_commonImage {m : ℕ} (cy cz theta z0 z1 : ℂ)
    (hy : Complex.exp z0 = cy) (hz : Complex.exp z1 = cz) (hcenter : z1 = theta*z0)
    (a : Fin (m+2) →₀ ℕ) (beta : Fin m →₀ ℕ) (ell : Fin 2 →₀ ℕ)
    {R : NNReal} (hR : 0 < R)
    (hc0 : ‖z0‖+3/4 ≤ (R : ℝ)/2) (hc1 : ‖z1‖+3/4 ≤ (R : ℝ)/2) :
    HasSum (fun p => pairTest z0 z1 ell R p *
      commonCoefficient ((∏ i, (a i.succ.succ).choose (beta i) : ℕ) : ℂ) theta
        (a 0) (a 1) (∑ i, (a i.succ.succ-beta i)) R p)
      (MvPowerSeries.coeff ell ((commonImage cy cz theta a).coeff beta)) := by
  rw [commonImage_coeff_eq_baseMonomial]
  exact hasSum_baseMonomial _ _ _ _ _ _ _ _ _ hy hz hcenter ell hR hc0 hc1

#print axioms hasSum_commonImage
#print axioms norm_pairTest_le

end LogarithmExtension.LogRatio.CommonTaylor

import LogarithmExtension.LogRatioCommonTaylor

/-!
# Uniform bounds on the actual common two-base Taylor coefficients

The finite binomial expansion gives the coefficient bound directly from
univariate Cauchy estimates. The bound is uniform in the auxiliary index,
the Taylor pair and every column in the prescribed weighted simplex.
-/

noncomputable section
namespace LogarithmExtension.LogRatio.CommonTaylor

open OAI OAI.PiExponent
open scoped BigOperators

theorem norm_commonCoefficient_le (b theta : ℂ) (h k N : ℕ) {R : ℝ}
    (hR : 0 < R) (p : ℕ × ℕ) :
    ‖commonCoefficient b theta h k N R p‖ ≤
      ‖b‖*Real.exp (((h+k : ℕ) : ℝ)*R)*((1+‖theta‖)*R)^N := by
  unfold commonCoefficient
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ l ∈ Finset.range (N+1), ‖binomialScalar b theta N l‖ *
        ((Real.exp ((h : ℝ)*R)*R^l) * (Real.exp ((k : ℝ)*R)*R^(N-l))) := by
      apply Finset.sum_le_sum
      intro l _
      simp only [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact mul_le_mul (norm_oneCoefficient_le h l p.1 hR)
        (norm_oneCoefficient_le k (N-l) p.2 hR) (norm_nonneg _) (by positivity)
    _ = ∑ l ∈ Finset.range (N+1),
        (‖b‖*Real.exp (((h+k : ℕ) : ℝ)*R)) *
          ((‖theta‖*R)^l * R^(N-l) * (N.choose l : ℝ)) := by
      apply Finset.sum_congr rfl
      intro l _
      simp only [binomialScalar, norm_mul, norm_pow, norm_neg, Complex.norm_natCast,
        Nat.cast_add, add_mul, Real.exp_add, mul_pow]
      ring
    _ = _ := by
      rw [← Finset.mul_sum, ← add_pow]
      congr 2
      ring

theorem norm_commonCoefficient_exp_budget (b theta : ℂ) (h k N A : ℕ) {R H w0 ws : ℝ}
    (hR : 1 ≤ R)
    (htheta : ‖theta‖ ≤ 2) (hb : ‖b‖ ≤ (2 : ℝ)^A)
    (hh : ((h+k : ℕ) : ℝ) ≤ H/w0) (hN : N ≤ A) (hA : (A : ℝ) ≤ H/ws)
    (p : ℕ × ℕ) :
    ‖commonCoefficient b theta h k N R p‖ ≤
      Real.exp (H*(R/w0+Real.log (6*R)/ws)) := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have h6R : 0 < 6*R := by positivity
  have hlog : 0 ≤ Real.log (6*R) := Real.log_nonneg (by linarith)
  calc
    _ ≤ ‖b‖*Real.exp (((h+k : ℕ) : ℝ)*R)*((1+‖theta‖)*R)^N :=
      norm_commonCoefficient_le b theta h k N hR0 p
    _ ≤ (2 : ℝ)^A * Real.exp ((H/w0)*R) * (3*R)^A := by
      apply mul_le_mul
      · exact mul_le_mul hb (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hh hR0.le))
          (Real.exp_pos _).le (by positivity)
      · exact (pow_le_pow_left₀ (by positivity)
          (mul_le_mul_of_nonneg_right (by linarith : 1+‖theta‖ ≤ 3) hR0.le) N).trans
          (pow_le_pow_right₀ (by linarith : 1 ≤ 3*R) hN)
      · positivity
      · positivity
    _ = Real.exp ((H/w0)*R + (A : ℝ)*Real.log (6*R)) := by
      have hpow : (6*R)^A = (2 : ℝ)^A*(3*R)^A := by
        rw [← mul_pow]
        congr 1
        ring
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log h6R]
      rw [hpow]
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have ha := mul_le_mul_of_nonneg_right hA hlog
      nlinarith [show (H/w0)*R+(H/ws)*Real.log (6*R) = H*(R/w0+Real.log (6*R)/ws) by ring]

def columnCoefficient {m : ℕ} (theta : ℂ) (alpha : Fin (m+2) → ℕ)
    (beta : Fin m → ℕ) (R : ℝ) (p : ℕ × ℕ) : ℂ :=
  commonCoefficient ((∏ i, (alpha i.succ.succ).choose (beta i) : ℕ) : ℂ) theta
    (alpha 0) (alpha 1) (∑ i, (alpha i.succ.succ-beta i)) R p

theorem norm_columnCoefficient_le {m : ℕ} (theta : ℂ) (alpha : Fin (m+2) → ℕ)
    (beta : Fin m → ℕ) (w : Fin m → ℝ) {R H w0 ws : ℝ}
    (hR : 1 ≤ R) (_hH : 0 ≤ H) (hw0 : 0 < w0) (hws : 0 < ws)
    (htheta : ‖theta‖ ≤ 2) (hw : ∀ i, ws ≤ w i)
    (hcol : w0*(alpha 0+alpha 1 : ℕ) + ∑ i, w i*alpha i.succ.succ ≤ H)
    (p : ℕ × ℕ) :
    ‖columnCoefficient theta alpha beta R p‖ ≤
      Real.exp (H*(R/w0+Real.log (6*R)/ws)) := by
  have hwpos (i) : 0 ≤ w i := hws.le.trans (hw i)
  have hsum0 : 0 ≤ ∑ i, w i*alpha i.succ.succ :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hwpos i) (Nat.cast_nonneg _))
  have hh : ((alpha 0+alpha 1 : ℕ) : ℝ) ≤ H/w0 := by
    apply (le_div_iff₀ hw0).mpr
    nlinarith
  have htot : ((∑ i : Fin m, alpha i.succ.succ : ℕ) : ℝ) ≤ H/ws := by
    rw [le_div_iff₀ hws, Nat.cast_sum]
    have hs : ws*(∑ i : Fin m, (alpha i.succ.succ : ℝ)) ≤
        ∑ i, w i*alpha i.succ.succ := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hw i) (Nat.cast_nonneg _))
    have hbase : 0 ≤ w0*((alpha 0+alpha 1 : ℕ) : ℝ) := by positivity
    nlinarith
  apply norm_commonCoefficient_exp_budget _ _ _ _ _ (∑ i : Fin m, alpha i.succ.succ)
    hR htheta _ hh (Finset.sum_le_sum (fun i _ => Nat.sub_le _ _)) htot p
  simpa only [InterpolationMatrix.exponentVector_apply] using
    PeriodAnalytic.norm_binomial_product_le (fun i : Fin m => alpha i.succ.succ)
      (InterpolationMatrix.exponentVector beta)

#print axioms norm_columnCoefficient_le

end LogarithmExtension.LogRatio.CommonTaylor

import LogarithmExtension.LogRatioTailBudget

/-!
# Analytic bounds for the actual bivariate row scalars

Separation of the two base variables reduces the coefficient estimates to
the proved one-variable logarithmic-tail estimates. The tail-order budget
then retains the approximation exponent, with explicit truncation losses.
-/

noncomputable section
namespace LogarithmExtension.LogRatio.AnalyticTranslation

open OAI OAI.PiExponent NestedJets
open scoped BigOperators

variable {m : ℕ}

theorem base_index_decomposition (ell : Fin 2 →₀ ℕ) :
    Finsupp.single 0 (ell 0) + Finsupp.single 1 (ell 1) = ell := by
  ext i
  fin_cases i <;> simp

theorem base_index_degree (ell : Fin 2 →₀ ℕ) : ell.degree = ell 0 + ell 1 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]

theorem coeff_separated_series (f g : PowerSeries ℂ) (ell : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff ell (f.toMvPowerSeries 0 * g.toMvPowerSeries 1) =
      PowerSeries.coeff (ell 0) f * PowerSeries.coeff (ell 1) g := by
  classical
  rw [MvPowerSeries.coeff_mul]
  refine (Finset.sum_eq_single (Finsupp.single 0 (ell 0), Finsupp.single 1 (ell 1)) ?_ ?_).trans ?_
  · intro uv huv hne
    rw [FormalJet.coeff_toMvPowerSeries, FormalJet.coeff_toMvPowerSeries]
    split_ifs with h0 h1
    · exfalso
      apply hne
      have hu := Finset.HasAntidiagonal.mem_antidiagonal.mp huv
      have he0 := congrArg (fun a : Fin 2 →₀ ℕ => a 0) hu
      have he1 := congrArg (fun a : Fin 2 →₀ ℕ => a 1) hu
      rw [h0, h1] at he0 he1
      simp only [Finsupp.add_apply, Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1),
        Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0), add_zero, zero_add] at he0 he1
      exact Prod.ext (h0.trans (congrArg (Finsupp.single 0) he0))
        (h1.trans (congrArg (Finsupp.single 1) he1))
    all_goals simp
  · intro hnot
    exact False.elim (hnot (Finset.HasAntidiagonal.mem_antidiagonal.mpr (base_index_decomposition ell)))
  · simp [FormalJet.coeff_toMvPowerSeries]

theorem univariate_log_eq_neg_tail :
    PowerSeries.log ℂ = -RowTranslation.tail 1 (PowerSeries.log ℂ) := by
  have htrunc : PowerSeries.trunc 1 (PowerSeries.log ℂ) = 0 := by
    ext n
    simp only [PowerSeries.coeff_trunc, Polynomial.coeff_zero]
    split_ifs with h
    · have hn : n = 0 := by omega
      simp [hn, PowerSeries.coeff_log]
    · rfl
  simp [RowTranslation.tail, htrunc]

theorem norm_coeff_log_mul_tails (T b : Fin m → ℕ) (k n : ℕ) (hT : ∀ i, 1 ≤ T i) :
    ‖PowerSeries.coeff n ((PowerSeries.log ℂ)^k *
      ∏ i, RowTranslation.tail (T i) (PowerSeries.log ℂ) ^ b i)‖ ≤ (2 : ℝ)^n := by
  have hb := LogTailAnalytic.norm_coeff_prod_formal_logTail_le Finset.univ
    (Fin.cases 1 T) (Fin.cases k b) (by
      intro i _
      cases i using Fin.cases with
      | zero => simp
      | succ i => exact hT i) n
  rw [Fin.prod_univ_succ] at hb
  simp only [Fin.cases_zero, Fin.cases_succ] at hb
  have he : (PowerSeries.log ℂ)^k *
      (∏ i, RowTranslation.tail (T i) (PowerSeries.log ℂ) ^ b i) =
      PowerSeries.C ((-1 : ℂ)^k) *
        (RowTranslation.tail 1 (PowerSeries.log ℂ)^k *
          ∏ i, RowTranslation.tail (T i) (PowerSeries.log ℂ)^b i) := by
    conv_lhs => arg 1; rw [univariate_log_eq_neg_tail, neg_pow]
    simp only [map_pow, map_neg, map_one]
    ring
  rw [he, PowerSeries.coeff_C_mul, norm_mul, norm_pow]
  simpa using hb

theorem mixedTail_product_expansion (r : Fin m → ℂ) (T b : Fin m → ℕ) (k : ℕ) :
    logarithm 0 ^ k * ∏ i, mixedTail (r i) (T i) ^ b i =
      ∑ c : (∀ i, Fin (b i+1)),
        MvPowerSeries.C (((∏ i, (b i).choose (c i) : ℕ) : ℂ) *
          ∏ i, (-r i) ^ (c i : ℕ)) *
          (((PowerSeries.log ℂ)^k *
            ∏ i, RowTranslation.tail (T i) (PowerSeries.log ℂ) ^ (c i : ℕ)).toMvPowerSeries 0 *
            (∏ i, RowTranslation.tail (T i) (PowerSeries.log ℂ) ^ (b i-c i)).toMvPowerSeries 1) := by
  have he (i : Fin m) : mixedTail (r i) (T i) =
      tail (T i) 1 + MvPowerSeries.C (-r i) * tail (T i) 0 := by
    simp [mixedTail, sub_eq_add_neg]
  simp only [he]
  rw [RowTranslation.product_add_expansion, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod]
  simp only [map_mul, map_pow, map_prod, ← tail_toMvPowerSeries, logarithm, Nat.cast_prod,
    map_natCast]
  ring

/-- Coefficient bound on the bidisk of radius one half, obtained by separating
the variables and using the established univariate Cauchy estimates. -/
theorem norm_coeff_mixedTail_product_le (r : Fin m → ℂ) (T b : Fin m → ℕ)
    (k : ℕ) (ell : Fin 2 →₀ ℕ) (hT : ∀ i, 1 ≤ T i) :
    ‖MvPowerSeries.coeff ell (logarithm 0^k * ∏ i, mixedTail (r i) (T i)^b i)‖ ≤
      (2 : ℝ)^ell.degree * ∏ i, (1+‖r i‖)^b i := by
  rw [mixedTail_product_expansion]
  simp only [map_sum, MvPowerSeries.coeff_C_mul, coeff_separated_series]
  apply (norm_sum_le _ _).trans
  have hs : (∑ c : (∀ i, Fin (b i+1)),
      ((∏ i, (b i).choose (c i) : ℕ) : ℝ) * ∏ i, ‖r i‖^(c i : ℕ)) =
      ∏ i, (1+‖r i‖)^b i := by
    simpa using (RowTranslation.product_add_expansion (fun _ : Fin m => (1 : ℝ))
      (fun i => ‖r i‖) b).symm
  calc
    _ ≤ ∑ c : (∀ i, Fin (b i+1)),
        (((∏ i, (b i).choose (c i) : ℕ) : ℝ) * ∏ i, ‖r i‖^(c i : ℕ)) *
          ((2 : ℝ)^(ell 0) * (2 : ℝ)^(ell 1)) := by
      apply Finset.sum_le_sum
      intro c _
      simp only [norm_mul, norm_prod, norm_pow, norm_neg, Complex.norm_natCast]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul
        (norm_coeff_log_mul_tails T (fun i => c i) k (ell 0) hT)
        (by simpa using norm_coeff_log_mul_tails T (fun i => b i-c i) 0 (ell 1) hT)
        (norm_nonneg _) (by positivity)
    _ = _ := by rw [← Finset.sum_mul, hs, ← pow_add, ← base_index_degree, mul_comm]

theorem norm_coeff_mixedTail_product_le_three (r : Fin m → ℂ) (T b : Fin m → ℕ)
    (k : ℕ) (ell : Fin 2 →₀ ℕ) (hT : ∀ i, 1 ≤ T i) (hr : ∀ i, ‖r i‖ ≤ 2) :
    ‖MvPowerSeries.coeff ell (logarithm 0^k * ∏ i, mixedTail (r i) (T i)^b i)‖ ≤
      (2 : ℝ)^ell.degree * (3 : ℝ)^(∑ i, b i) := by
  apply (norm_coeff_mixedTail_product_le r T b k ell hT).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
  intro i _
  apply pow_le_pow_left₀ (by positivity)
  linarith [hr i]

theorem norm_refinedScalar_le (epsilon r : Fin m → ℂ) (T : Fin m → ℕ)
    (beta a : Fin m →₀ ℕ) (b : ∀ i, Fin (a i-beta i+1)) (ell : Fin 2 →₀ ℕ)
    (hT : ∀ i, 1 ≤ T i) (hr : ∀ i, ‖r i‖ ≤ 2) :
    ‖refinedScalar epsilon r T beta a b ell‖ ≤
      (12 : ℝ)^(∑ i, a i) * (∏ i, ‖epsilon i‖^(a i-beta i-b i)) * (2 : ℝ)^ell.degree := by
  have hbin : ((∏ i, (a i).choose (beta i) * (a i-beta i).choose (b i) : ℕ) : ℝ) ≤
      (4 : ℝ)^(∑ i, a i) := by
    exact_mod_cast RowTranslation.multi_choose_product_le_four_pow
      (fun i => a i) (fun i => beta i) (fun i => (b i : ℕ))
  have hb : (∑ i, (b i : ℕ)) ≤ ∑ i, a i := by
    apply Finset.sum_le_sum
    intro i _
    exact (Nat.le_of_lt_succ (b i).isLt).trans (Nat.sub_le _ _)
  have hcore := (norm_coeff_mixedTail_product_le_three r T (fun i => b i)
    (∑ i, (a i-beta i-b i)) ell hT hr).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hb)
      (by positivity))
  simp only [refinedScalar, norm_mul, norm_prod, norm_pow, Complex.norm_natCast]
  calc
    _ ≤ ((4 : ℝ)^(∑ i, a i) * ∏ i, ‖epsilon i‖^(a i-beta i-b i)) *
        ((2 : ℝ)^ell.degree * (3 : ℝ)^(∑ i, a i)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hbin (by positivity)) hcore
        (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [show (12 : ℝ) = 4*3 by norm_num, mul_pow]
      ring

theorem norm_refinedScalar_exp_basic (epsilon r : Fin m → ℂ) (T : Fin m → ℕ)
    (beta a : Fin m →₀ ℕ) (b : ∀ i, Fin (a i-beta i+1)) (ell : Fin 2 →₀ ℕ)
    (w : Fin m → ℝ) (C nu : ℝ) (hT : ∀ i, 1 ≤ T i) (hr : ∀ i, ‖r i‖ ≤ 2)
    (hepsilon : ∀ i, ‖epsilon i‖ ≤ Real.exp (C-nu*w i)) :
    ‖refinedScalar epsilon r T beta a b ell‖ ≤
      Real.exp (((∑ i, a i : ℕ) : ℝ) * Real.log 12 +
        (∑ i, ((a i-beta i-b i : ℕ) : ℝ) * (C-nu*w i)) +
          (ell.degree : ℝ) * Real.log 2) := by
  apply (norm_refinedScalar_le epsilon r T beta a b ell hT hr).trans
  calc
    _ ≤ (12 : ℝ)^(∑ i, a i) *
        Real.exp (∑ i, ((a i-beta i-b i : ℕ) : ℝ) * (C-nu*w i)) * (2 : ℝ)^ell.degree :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (MatrixTranslationBounds.error_power_product_le epsilon _ w C nu hepsilon)
          (by positivity)) (by positivity)
    _ = _ := by
      rw [Real.exp_add, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul,
        Real.exp_log (by norm_num : (0 : ℝ) < 12),
        Real.exp_log (by norm_num : (0 : ℝ) < 2)]

theorem norm_refinedScalar_exp_weighted (epsilon r : Fin m → ℂ) (T : Fin m → ℕ)
    (beta a : Fin m →₀ ℕ) (b : ∀ i, Fin (a i-beta i+1)) (ell : Fin 2 →₀ ℕ)
    (w : Fin m → ℝ) (C nu H ws v F : ℝ) (hC : 0 ≤ C) (hnu : 0 ≤ nu)
    (hws : 0 < ws) (hv : 0 < v) (hF : 0 < F)
    (hw : ∀ i, ws ≤ w i) (ha : MatrixTranslationBounds.weight w (fun i => a i) ≤ H)
    (hell : (ell.degree : ℝ) ≤ H/v) (hT : ∀ i, 1 ≤ T i)
    (hTw : ∀ i, F*w i ≤ v*T i) (hr : ∀ i, ‖r i‖ ≤ 2)
    (hepsilon : ∀ i, ‖epsilon i‖ ≤ Real.exp (C-nu*w i)) :
    ‖refinedScalar epsilon r T beta a b ell‖ ≤
      Real.exp (-nu * MatrixTranslationBounds.weight w (fun i => a i-beta i) +
        H * (nu/F + Real.log 2/v + (Real.log 12+C)/ws)) := by
  by_cases hz : MvPowerSeries.coeff ell
      (logarithm 0^(∑ i, (a i-beta i-b i)) * ∏ i, mixedTail (r i) (T i)^(b i : ℕ)) = 0
  · simp [refinedScalar, hz, Real.exp_nonneg]
  have hbudget : MatrixTranslationBounds.weight w (fun i => (b i : ℕ)) ≤ H/F := by
    have hb := mixedTail_weight_budget r T (fun i => b i) _ ell w v F hv.le hF hTw hz
    have he : v * (ell.degree : ℝ) ≤ H := by
      nlinarith [(le_div_iff₀ hv).mp hell]
    exact hb.trans (div_le_div_of_nonneg_right he hF.le)
  have hsize := MatrixTranslationBounds.sum_exponents_le w (fun i => a i) H ws hws hw ha
  have hcount : ((∑ i, (a i-beta i-b i) : ℕ) : ℝ) ≤ ((∑ i, a i : ℕ) : ℝ) := by
    exact_mod_cast Finset.sum_le_sum (fun i _ => (Nat.sub_le _ _).trans (Nat.sub_le _ _))
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog12 : 0 ≤ Real.log 12 := Real.log_nonneg (by norm_num)
  apply (norm_refinedScalar_exp_basic epsilon r T beta a b ell w C nu hT hr hepsilon).trans
  apply Real.exp_le_exp.mpr
  rw [MatrixTranslationBounds.residual_exponent_identity]
  calc
    _ ≤ (Real.log 12+C) * ((∑ i, a i : ℕ) : ℝ) -
        nu * MatrixTranslationBounds.weight w (fun i => a i-beta i) +
        nu * (H/F) + (H/v) * Real.log 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hcount hC,
        mul_le_mul_of_nonneg_left hbudget hnu,
        mul_le_mul_of_nonneg_right hell hlog2]
    _ ≤ (Real.log 12+C) * (H/ws) -
        nu * MatrixTranslationBounds.weight w (fun i => a i-beta i) +
        nu * (H/F) + (H/v) * Real.log 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hsize (add_nonneg hlog12 hC)]
    _ = _ := by ring

/-- The coefficient in the exact matrix translation has only a polynomial
overhead beyond the exponential approximation/truncation estimate. -/
theorem norm_rowScalar_exp_weighted (theta : ℂ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (beta a : Fin m →₀ ℕ) (ell : Fin 2 →₀ ℕ) (w : Fin m → ℝ)
    (C nu H ws v F : ℝ) (hC : 0 ≤ C) (hnu : 0 ≤ nu)
    (hws : 0 < ws) (hv : 0 < v) (hF : 0 < F)
    (hw : ∀ i, ws ≤ w i) (hw1 : ∀ i, 1 ≤ w i)
    (ha : MatrixTranslationBounds.weight w (fun i => a i) ≤ H)
    (hell : (ell.degree : ℝ) ≤ H/v) (hT : ∀ i, 1 ≤ T i)
    (hTw : ∀ i, F*w i ≤ v*T i) (hr : ∀ i, ‖r i‖ ≤ 2)
    (hepsilon : ∀ i, ‖theta-r i‖ ≤ Real.exp (C-nu*w i)) :
    ‖rowScalar (errorSeries theta r T) beta a ell‖ ≤
      ((⌊H⌋₊+1 : ℕ) : ℝ)^m *
        Real.exp (-nu * (MatrixTranslationBounds.weight w (fun i => a i) -
          MatrixTranslationBounds.weight w (fun i => beta i)) +
            H * (nu/F + Real.log 2/v + (Real.log 12+C)/ws)) := by
  classical
  have hbound (b : ∀ i, Fin (a i-beta i+1)) :=
    norm_refinedScalar_exp_weighted (fun i => theta-r i) r T beta a b ell w C nu H ws v F
      hC hnu hws hv hF hw ha hell hT hTw hr hepsilon
  have hidx : a ∈ MatrixTranslation.transverseIndices w H :=
    (MatrixTranslation.mem_transverseIndices w H (fun i => lt_of_lt_of_le zero_lt_one (hw1 i)) a).mpr ha
  have hcard : (Fintype.card (∀ i, Fin (a i-beta i+1)) : ℝ) ≤ ((⌊H⌋₊+1 : ℕ) : ℝ)^m := by
    have hc := RowTranslation.card_bounded_indices_le (fun i => a i-beta i) ⌊H⌋₊
      (fun i => (Nat.sub_le _ _).trans (MatrixTranslation.transverseIndices_coordinate_le w H hw1 hidx i))
    simp only [Fintype.card_fin] at hc
    exact_mod_cast hc
  have hdiff := MatrixTranslationBounds.weight_sub_le_weight_tsub w (fun i => a i)
    (fun i => beta i) (fun i => hws.le.trans (hw i))
  rw [rowScalar_eq_sum_refined]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _b : (∀ i, Fin (a i-beta i+1)),
        Real.exp (-nu * MatrixTranslationBounds.weight w (fun i => a i-beta i) +
          H * (nu/F + Real.log 2/v + (Real.log 12+C)/ws)) :=
      Finset.sum_le_sum (fun b _ => hbound b)
    _ ≤ _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      apply mul_le_mul hcard _ (Real.exp_pos _).le (by positivity)
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hdiff hnu]

end LogarithmExtension.LogRatio.AnalyticTranslation

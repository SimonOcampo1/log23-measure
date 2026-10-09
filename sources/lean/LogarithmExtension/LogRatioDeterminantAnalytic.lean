import LogarithmExtension.LogRatioChoiceCollision

/-!
# Analytic upper bound for the original two-base determinant

Combine the exact finite determinant translation, its approximation-sensitive
row scalars, and the proved Taylor packing bound for the actual common rows.
No determinant upper bound or Taylor-series identity is assumed.
-/

noncomputable section
namespace LogarithmExtension.LogRatio.DeterminantAnalytic

open OAI OAI.PiExponent BoundedJetMatrix CommonTaylor
open LogarithmExtension.LogRatio.AnalyticTranslation
open scoped BigOperators

def scalarOverhead (d : GeometryData) (H : ℚ) : ℝ :=
  (((⌊(H : ℝ)⌋₊+1 : ℕ) : ℝ))^d.m

def choiceOverhead (d : GeometryData) (H : ℚ) : ℝ :=
  scalarOverhead d H * (((⌊(H : ℝ)/(d.curveJetWeights 0 : ℝ)⌋₊+1 : ℕ) : ℝ))^2

def rowOverhead (d : GeometryData) (H : ℚ) : ℝ := scalarOverhead d H * choiceOverhead d H

theorem scalarOverhead_pos (d : GeometryData) (H : ℚ) : 0 < scalarOverhead d H := by
  unfold scalarOverhead
  positivity

theorem choiceOverhead_pos (d : GeometryData) (H : ℚ) : 0 < choiceOverhead d H := by
  unfold choiceOverhead
  exact mul_pos (scalarOverhead_pos d H) (by positivity)

theorem rowOverhead_pos (d : GeometryData) (H : ℚ) : 0 < rowOverhead d H :=
  mul_pos (scalarOverhead_pos d H) (choiceOverhead_pos d H)

theorem logWeights_ge_one (d : GeometryData)
    (hW : ∀ i, (d.curveDegreeWeights i.succ.succ : ℝ) = MatrixArithmetic.logWeights d.q i)
    (i : Fin d.m) : 1 ≤ MatrixArithmetic.logWeights d.q i := by
  have hp := ArithmeticBound.logWeights_pos d hW i
  have hn : 1 ≤ ⌈Real.log (d.q i : ℝ)⌉₊ := Nat.one_le_iff_ne_zero.mpr
    (by intro hz; simp [MatrixArithmetic.logWeights, hz] at hp)
  change (1 : ℝ) ≤ (⌈Real.log (d.q i : ℝ)⌉₊ : ℝ)
  exact_mod_cast hn

theorem choiceFamily_card_le_real (d : GeometryData) (H : ℚ)
    (hW : ∀ i, (d.curveDegreeWeights i.succ.succ : ℝ) = MatrixArithmetic.logWeights d.q i) :
    (Fintype.card (ChoiceFamily d H) : ℝ) ≤ (choiceOverhead d H)^Fintype.card (Row d H) := by
  have h := choiceFamily_card_le d H (fun i => by rw [hW]; exact logWeights_ge_one d hW i)
  have hr := (Nat.cast_le (α := ℝ)).mpr h
  simpa only [choiceOverhead, scalarOverhead, Nat.cast_pow, Nat.cast_mul] using hr

/-- The unnormalized analytic bound applies to every full-row selected
minor of the original matrix. Its hypotheses are explicit approximation,
weight and truncation data, not an analytic determinant estimate. -/
theorem norm_selectedMinor_le (d : GeometryData) (H : ℚ) (nu L F ws : ℝ)
    (hK : 0 < d.K) (hH : 0 ≤ H) (hnu : 0 < nu) (hF : 0 < F) (hws : 0 < ws)
    (hwmin : ∀ i, ws ≤ MatrixArithmetic.logWeights d.q i)
    (hW : ∀ i, (d.curveDegreeWeights i.succ.succ : ℝ) = MatrixArithmetic.logWeights d.q i)
    (hr : ∀ i, ‖d.slopes i‖ ≤ 2)
    (happrox : ∀ i, |ratioTheta-(d.p i : ℝ)/d.q i| ≤ (d.q i : ℝ)^(-nu))
    (selection : Row d H → Column d H) :
    ‖(MatrixArithmetic.selectedMinor d
      (MatrixArithmetic.truncationOrders d.q F (d.curveJetWeights 0)) H selection).det‖ ≤
      (rowOverhead d H)^Fintype.card (Row d H) * (Fintype.card (Row d H)).factorial *
        Real.exp (nu*ArithmeticBound.rowWeightedSum d H +
          (Fintype.card (Row d H) : ℝ)*(H : ℝ)*
            (translationError d nu F ws + CommonTaylor.holomorphicError d ws) -
              L*Fintype.card (Row d H) + TaylorPacking.augmentedCount
                (TaylorPacking.combinedWeights (MatrixArithmetic.logWeights d.q) nu) L) *
          ((1-TaylorPacking.quarterRatio)⁻¹)^(2*Fintype.card (Row d H)) := by
  classical
  let M := Fintype.card (Row d H)
  let A : ℝ := (scalarOverhead d H)^M *
    Real.exp (nu*ArithmeticBound.rowWeightedSum d H + (M : ℝ)*(H : ℝ)*translationError d nu F ws)
  let B : ℝ := M.factorial *
    Real.exp ((M : ℝ)*(H : ℝ)*CommonTaylor.holomorphicError d ws - L*M +
      TaylorPacking.augmentedCount (TaylorPacking.combinedWeights (MatrixArithmetic.logWeights d.q) nu) L) *
      ((1-TaylorPacking.quarterRatio)⁻¹)^(2*M)
  have hA : 0 ≤ A := mul_nonneg (pow_nonneg (scalarOverhead_pos d H).le _) (Real.exp_pos _).le
  have hg : 0 < (1-TaylorPacking.quarterRatio)⁻¹ :=
    inv_pos.mpr (sub_pos.mpr TaylorPacking.quarterRatio_lt_one)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hterm (f : ChoiceFamily d H) :
      ‖(∏ row, choiceScalar d (MatrixArithmetic.truncationOrders d.q F (d.curveJetWeights 0))
        H ratioTheta row (f row)) * (choiceMatrix d H ratioTheta selection f).det‖ ≤ A*B := by
    have hs := norm_product_choiceScalar_le d ratioTheta nu F ws H hnu.le hF hws hwmin hW hr happrox f
    have hs' : ‖∏ row, choiceScalar d
        (MatrixArithmetic.truncationOrders d.q F (d.curveJetWeights 0)) H ratioTheta row (f row)‖ ≤
          A*Real.exp (-nu*choiceAuxiliaryWeight d H f) := by
      apply hs.trans_eq
      dsimp only [A, M, scalarOverhead]
      simp only [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    have hc := weighted_choiceMatrix_bound d H nu L ws hK hH hnu hws hwmin hW selection f
    rw [norm_mul]
    calc
      _ ≤ (A*Real.exp (-nu*choiceAuxiliaryWeight d H f)) *
          ‖(choiceMatrix d H ratioTheta selection f).det‖ :=
        mul_le_mul_of_nonneg_right hs' (norm_nonneg _)
      _ = A*(Real.exp (-nu*choiceAuxiliaryWeight d H f) *
          ‖(choiceMatrix d H ratioTheta selection f).det‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hc hA
  rw [determinant_translation d _ H (ratioTheta : ℂ)]
  calc
    _ ≤ ∑ f : ChoiceFamily d H,
        ‖(∏ row, choiceScalar d (MatrixArithmetic.truncationOrders d.q F (d.curveJetWeights 0))
          H ratioTheta row (f row)) * (choiceMatrix d H ratioTheta selection f).det‖ := norm_sum_le _ _
    _ ≤ ∑ _f : ChoiceFamily d H, A*B := Finset.sum_le_sum (fun f _ => hterm f)
    _ = (Fintype.card (ChoiceFamily d H) : ℝ)*(A*B) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (choiceOverhead d H)^M*(A*B) :=
      mul_le_mul_of_nonneg_right (choiceFamily_card_le_real d H hW) (mul_nonneg hA hB)
    _ = _ := by
      dsimp only [A, B, M, rowOverhead]
      have he : nu*ArithmeticBound.rowWeightedSum d H +
          (Fintype.card (Row d H) : ℝ)*(H : ℝ)*
            (translationError d nu F ws + CommonTaylor.holomorphicError d ws) -
              L*Fintype.card (Row d H) + TaylorPacking.augmentedCount
                (TaylorPacking.combinedWeights (MatrixArithmetic.logWeights d.q) nu) L =
          (nu*ArithmeticBound.rowWeightedSum d H +
            (Fintype.card (Row d H) : ℝ)*(H : ℝ)*translationError d nu F ws) +
          ((Fintype.card (Row d H) : ℝ)*(H : ℝ)*CommonTaylor.holomorphicError d ws -
              L*Fintype.card (Row d H) + TaylorPacking.augmentedCount
                (TaylorPacking.combinedWeights (MatrixArithmetic.logWeights d.q) nu) L) := by ring
      simp only [he, Real.exp_add, mul_pow]
      ring

#print axioms norm_selectedMinor_le

theorem overhead_factor_le_exp (M : ℕ) (Q X : ℝ) (hQ : 0 < Q) :
    Q^M * (M.factorial : ℝ) * Real.exp X * ((1-TaylorPacking.quarterRatio)⁻¹)^(2*M) ≤
      Real.exp (X+(M : ℝ)*(Real.log M+Real.log Q-2*Real.log (1-TaylorPacking.quarterRatio))) := by
  have hq : Q^M = Real.exp ((M : ℝ)*Real.log Q) := by
    rw [Real.exp_nat_mul, Real.exp_log hQ]
  have hg0 : 0 < 1-TaylorPacking.quarterRatio := sub_pos.mpr TaylorPacking.quarterRatio_lt_one
  have hg : ((1-TaylorPacking.quarterRatio)⁻¹)^(2*M) =
      Real.exp (((2*M : ℕ) : ℝ)*(-Real.log (1-TaylorPacking.quarterRatio))) := by
    rw [Real.exp_nat_mul, Real.exp_neg, Real.exp_log hg0]
  calc
    _ ≤ Q^M * Real.exp ((M : ℝ)*Real.log M) * Real.exp X *
        ((1-TaylorPacking.quarterRatio)⁻¹)^(2*M) := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (inv_nonneg.mpr hg0.le) _)
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_left (Collision.factorial_le_exp_card_log M) (pow_nonneg hQ.le _)
    _ = _ := by
      rw [hq, hg]
      simp only [← Real.exp_add, Nat.cast_mul, Nat.cast_ofNat]
      congr 1
      ring

def analyticRemainder (d : GeometryData) (H : ℚ) : ℝ :=
  (Real.log (Fintype.card (Row d H)) + Real.log (rowOverhead d H) -
    2*Real.log (1-TaylorPacking.quarterRatio))/(H : ℝ)

theorem normalized_determinant_upper_bound (d : GeometryData) (H : ℚ) (nu lambda F ws : ℝ)
    (hK : 0 < d.K) (hH : 0 < H) (hnu : 0 < nu) (hF : 0 < F) (hws : 0 < ws)
    (hwmin : ∀ i, ws ≤ MatrixArithmetic.logWeights d.q i)
    (hW : ∀ i, (d.curveDegreeWeights i.succ.succ : ℝ) = MatrixArithmetic.logWeights d.q i)
    (hr : ∀ i, ‖d.slopes i‖ ≤ 2)
    (happrox : ∀ i, |ratioTheta-(d.p i : ℝ)/d.q i| ≤ (d.q i : ℝ)^(-nu))
    (selection : Row d H → Column d H)
    (hne : (MatrixArithmetic.selectedMinor d
      (MatrixArithmetic.truncationOrders d.q F (d.curveJetWeights 0)) H selection).det ≠ 0) :
    Real.log ‖(MatrixArithmetic.selectedMinor d
      (MatrixArithmetic.truncationOrders d.q F (d.curveJetWeights 0)) H selection).det‖ /
        ((Fintype.card (Row d H) : ℝ)*(H : ℝ)) ≤
      nu*ArithmeticBound.meanRowWeight d H - lambda +
        (TaylorPacking.augmentedCount (TaylorPacking.combinedWeights
          (MatrixArithmetic.logWeights d.q) nu) (lambda*(H : ℝ)) : ℝ)/
          ((Fintype.card (Row d H) : ℝ)*(H : ℝ)) +
            translationError d nu F ws + CommonTaylor.holomorphicError d ws + analyticRemainder d H := by
  let M := Fintype.card (Row d H)
  let X : ℝ := nu*ArithmeticBound.rowWeightedSum d H +
    (M : ℝ)*(H : ℝ)*(translationError d nu F ws+CommonTaylor.holomorphicError d ws) -
      (lambda*(H : ℝ))*M + TaylorPacking.augmentedCount
        (TaylorPacking.combinedWeights (MatrixArithmetic.logWeights d.q) nu) (lambda*(H : ℝ))
  have hMr : (0 : ℝ) < M := by exact_mod_cast ArithmeticBound.row_card_pos d H hK hH
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hb := norm_selectedMinor_le d H nu (lambda*(H : ℝ)) F ws
    hK hH.le hnu hF hws hwmin hW hr happrox selection
  have he := overhead_factor_le_exp M (rowOverhead d H) X (rowOverhead_pos d H)
  have hlog := (Real.log_le_log (norm_pos_iff.mpr hne) (hb.trans he)).trans_eq (Real.log_exp _)
  apply (div_le_iff₀ (mul_pos hMr hHr)).mpr
  apply hlog.trans_eq
  dsimp only [X, analyticRemainder, ArithmeticBound.meanRowWeight, M]
  have hMne : (Fintype.card (Row d H) : ℝ) ≠ 0 := hMr.ne'
  field_simp [hMne, hHr.ne']
  ring

#print axioms normalized_determinant_upper_bound

end LogarithmExtension.LogRatio.DeterminantAnalytic

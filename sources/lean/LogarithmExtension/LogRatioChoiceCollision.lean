import LogarithmExtension.LogRatioCommonTaylorBounds
import LogarithmExtension.LogRatioPackedCollision
import LogarithmExtension.LogRatioMatrixTranslationBounds

/-!
# Direct Taylor packing for the actual translated logarithm-ratio minor

The common coefficients and all their series identities are constructed,
not supplied as analytic hypotheses. The real parameter is log(3)/log(2).
The bounds hold for every selected column family and every row translation.
-/

noncomputable section
namespace LogarithmExtension.LogRatio.CommonTaylor

open OAI OAI.PiExponent NestedJets BoundedJetMatrix
open LogarithmExtension.LogRatio.AnalyticTranslation
open scoped BigOperators

def ratioTheta : ℝ := Real.log 3 / Real.log 2

theorem ratioTheta_mul_log_two : ratioTheta*Real.log 2 = Real.log 3 :=
  div_mul_cancel₀ _ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'

theorem ratioTheta_pos : 0 < ratioTheta :=
  div_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))

theorem ratioTheta_lt_two : ratioTheta < 2 := by
  apply (div_lt_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) < 2^2)
  rw [Real.log_pow] at h
  simpa only [Nat.cast_ofNat] using h

theorem norm_ratioTheta_le : ‖(ratioTheta : ℂ)‖ ≤ 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ratioTheta_pos]
  exact ratioTheta_lt_two.le

def logCenter (base : ℝ) (j : ℕ) : ℂ := (j : ℂ)*(Real.log base : ℂ)

theorem exp_logCenter (base : ℝ) (hbase : 0 < base) (j : ℕ) :
    Complex.exp (logCenter base j) = (base : ℂ)^j := by
  rw [logCenter, Complex.exp_nat_mul, ← Complex.ofReal_exp, Real.exp_log hbase]

theorem logCenter_relation (j : ℕ) :
    logCenter 3 j = (ratioTheta : ℂ)*logCenter 2 j := by
  have he : (Real.log 3 : ℂ) = (ratioTheta : ℂ)*(Real.log 2 : ℂ) := by
    exact_mod_cast ratioTheta_mul_log_two.symm
  rw [logCenter, logCenter, he]
  ring

theorem logCenter_radius_bound (base : ℝ) (hb1 : 1 ≤ base) (hb3 : base ≤ 3)
    {K j : ℕ} (hK : 0 < K) (hj : j < K) :
    ‖logCenter base j‖+3/4 ≤ (100*(K : ℝ))/2 := by
  have hb0 : 0 < base := lt_of_lt_of_le zero_lt_one hb1
  have hlog0 := Real.log_nonneg hb1
  have hlog2 : Real.log base ≤ 2 := (Real.log_le_sub_one_of_pos hb0).trans (by linarith)
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hjK : (j : ℝ) ≤ K := by exact_mod_cast hj.le
  rw [logCenter, norm_mul, Complex.norm_natCast, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hlog0]
  have hm := mul_le_mul hjK hlog2 hlog0 (Nat.cast_nonneg K)
  linarith

def coefficientError (d : GeometryData) (ws : ℝ) : ℝ :=
  100*d.K/(d.curveDegreeWeights 0 : ℝ) + Real.log (600*d.K)/ws

def holomorphicError (d : GeometryData) (ws : ℝ) : ℝ :=
  coefficientError d ws + Real.log 2/(d.curveJetWeights 0 : ℝ)

theorem column_budget (d : GeometryData) (H : ℚ) (col : Column d H) :
    (d.curveDegreeWeights 0 : ℝ)*(col.val 0+col.val 1 : ℕ) +
      ∑ i : Fin d.m, (d.curveDegreeWeights i.succ.succ : ℝ)*col.val i.succ.succ ≤ H := by
  have hc := (mem_realWeightedSimplex (fun i =>
    show (0 : ℝ) < d.curveDegreeWeights i by exact_mod_cast d.curveDegreeWeights_pos i)).mp col.property
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at hc
  simpa only [Fin.succ_zero_eq_one, d.degree_base_eq, Nat.cast_add, mul_add, add_assoc] using hc

theorem choice_test_degree_le (d : GeometryData) (H : ℚ) (row : Row d H)
    (t : RowChoice d H row) :
    (t.2.val.2.degree : ℝ) ≤ (H : ℝ)/(d.curveJetWeights 0 : ℝ) := by
  have he := Finset.HasAntidiagonal.mem_antidiagonal.mp t.2.property
  have hd := congrArg Finsupp.degree he
  rw [map_add] at hd
  have hle : t.2.val.2.degree ≤ (baseIndex (InterpolationMatrix.exponentVector row.2.val)).degree := by
    omega
  exact (show (t.2.val.2.degree : ℝ) ≤
      (baseIndex (InterpolationMatrix.exponentVector row.2.val)).degree by exact_mod_cast hle).trans
    (row_base_degree_le d H row)

theorem hasSum_choiceEntry (d : GeometryData) (H : ℚ) (hK : 0 < d.K)
    (row : Row d H) (col : Column d H) (t : RowChoice d H row) :
    HasSum (fun p => pairTest (logCenter 2 row.1.val) (logCenter 3 row.1.val) t.2.val.2
        (100*d.K) p * columnCoefficient ratioTheta col.val (fun i => t.1.val i) (100*d.K) p)
      (choiceEntry d H ratioTheta row col t) := by
  let R : NNReal := ⟨100*d.K, by positivity⟩
  have hR : 0 < R := by change (0 : ℝ) < 100*d.K; positivity
  have hy : Complex.exp (logCenter 2 row.1.val) = d.centerY row.1 := by
    simpa only [GeometryData.centerY, Complex.ofReal_ofNat] using
      exp_logCenter 2 (by norm_num) row.1.val
  have hz : Complex.exp (logCenter 3 row.1.val) = d.centerZ row.1 := by
    simpa only [GeometryData.centerZ, Complex.ofReal_ofNat] using
      exp_logCenter 3 (by norm_num) row.1.val
  have hs := hasSum_commonImage (d.centerY row.1) (d.centerZ row.1) ratioTheta
    (logCenter 2 row.1.val) (logCenter 3 row.1.val) hy hz (logCenter_relation row.1.val)
    (InterpolationMatrix.exponentVector col.val) t.1.val t.2.val.2 (R := R) hR
    (logCenter_radius_bound 2 (by norm_num) (by norm_num) hK row.1.isLt)
    (logCenter_radius_bound 3 (by norm_num) (by norm_num) hK row.1.isLt)
  have hRv : (R : ℝ) = 100*(d.K : ℝ) := rfl
  rw [hRv] at hs
  simpa only [columnCoefficient, choiceEntry, InterpolationMatrix.exponentVector_apply] using hs

theorem weighted_choiceMatrix_raw_bound (d : GeometryData) (H : ℚ) (nu L ws : ℝ)
    (hK : 0 < d.K) (hH : 0 ≤ H) (hnu : 0 < nu) (hws : 0 < ws)
    (hwmin : ∀ i, ws ≤ MatrixArithmetic.logWeights d.q i)
    (hW : ∀ i, (d.curveDegreeWeights i.succ.succ : ℝ) = MatrixArithmetic.logWeights d.q i)
    (selection : Row d H → Column d H) (f : ChoiceFamily d H) :
    Real.exp (-nu*choiceAuxiliaryWeight d H f) * ‖(choiceMatrix d H ratioTheta selection f).det‖ ≤
      ((Fintype.card (Row d H)).factorial *
        (Real.exp ((H : ℝ)*coefficientError d ws))^Fintype.card (Row d H) *
          ∏ row : Row d H, (2 : ℝ)^((f row).2.val.2 0+(f row).2.val.2 1)) *
        Real.exp (-L*Fintype.card (Row d H)+
          TaylorPacking.augmentedCount (TaylorPacking.combinedWeights
            (MatrixArithmetic.logWeights d.q) nu) L) *
          ((1-TaylorPacking.quarterRatio)⁻¹)^(2*Fintype.card (Row d H)) := by
  classical
  have hK1 : (1 : ℝ) ≤ d.K := by exact_mod_cast hK
  have hR : (1 : ℝ) ≤ 100*d.K := by linarith
  have hHr : (0 : ℝ) ≤ H := by exact_mod_cast hH
  have hw0 : (0 : ℝ) < d.curveDegreeWeights 0 := by exact_mod_cast d.curveDegreeWeights_pos 0
  apply TaylorPacking.infinite_weighted_collision_bound
    (MatrixArithmetic.logWeights d.q) nu L (ArithmeticBound.logWeights_pos d hW) hnu
    (fun row i => (f row).1.val i)
    (fun row p => pairTest (logCenter 2 row.1.val) (logCenter 3 row.1.val) (f row).2.val.2 (100*d.K) p)
    (fun a p col => columnCoefficient ratioTheta (selection col).val a (100*d.K) p)
    (Real.exp ((H : ℝ)*coefficientError d ws))
    (fun row => (2 : ℝ)^((f row).2.val.2 0+(f row).2.val.2 1)) (Real.exp_pos _).le
    (fun _ => by positivity)
  · intro a p col
    have hc := norm_columnCoefficient_le (ratioTheta : ℂ) (selection col).val a
      (fun i => (d.curveDegreeWeights i.succ.succ : ℝ)) hR hHr hw0 hws norm_ratioTheta_le
      (fun i => by simpa only [hW] using hwmin i) (column_budget d H (selection col)) p
    simpa only [coefficientError, show (6 : ℝ)*(100*d.K) = 600*d.K by ring] using hc
  · intro row p
    exact norm_pairTest_le _ _ _ (lt_of_lt_of_le zero_lt_one hR)
      (logCenter_radius_bound 2 (by norm_num) (by norm_num) hK row.1.isLt)
      (logCenter_radius_bound 3 (by norm_num) (by norm_num) hK row.1.isLt) p
  · intro row col
    exact hasSum_choiceEntry d H hK row (selection col) (f row)

theorem choice_test_product_le (d : GeometryData) (H : ℚ) (f : ChoiceFamily d H) :
    (∏ row : Row d H, (2 : ℝ)^((f row).2.val.2 0+(f row).2.val.2 1)) ≤
      Real.exp ((Fintype.card (Row d H) : ℝ)*(H : ℝ)*Real.log 2/(d.curveJetWeights 0 : ℝ)) := by
  calc
    _ ≤ ∏ _row : Row d H, Real.exp ((H : ℝ)/(d.curveJetWeights 0 : ℝ)*Real.log 2) := by
      apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
      intro row _
      have hd := choice_test_degree_le d H row (f row)
      rw [base_index_degree] at hd
      calc
        _ = Real.exp ((((f row).2.val.2 0+(f row).2.val.2 1 : ℕ) : ℝ)*Real.log 2) := by
          rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        _ ≤ _ := Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right hd (Real.log_nonneg (by norm_num)))
    _ = _ := by
      rw [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]
      congr 1
      ring

theorem weighted_choiceMatrix_bound (d : GeometryData) (H : ℚ) (nu L ws : ℝ)
    (hK : 0 < d.K) (hH : 0 ≤ H) (hnu : 0 < nu) (hws : 0 < ws)
    (hwmin : ∀ i, ws ≤ MatrixArithmetic.logWeights d.q i)
    (hW : ∀ i, (d.curveDegreeWeights i.succ.succ : ℝ) = MatrixArithmetic.logWeights d.q i)
    (selection : Row d H → Column d H) (f : ChoiceFamily d H) :
    Real.exp (-nu*choiceAuxiliaryWeight d H f) * ‖(choiceMatrix d H ratioTheta selection f).det‖ ≤
      (Fintype.card (Row d H)).factorial *
        Real.exp ((Fintype.card (Row d H) : ℝ)*(H : ℝ)*holomorphicError d ws -
          L*Fintype.card (Row d H) + TaylorPacking.augmentedCount
            (TaylorPacking.combinedWeights (MatrixArithmetic.logWeights d.q) nu) L) *
          ((1-TaylorPacking.quarterRatio)⁻¹)^(2*Fintype.card (Row d H)) := by
  apply (weighted_choiceMatrix_raw_bound d H nu L ws hK hH hnu hws hwmin hW selection f).trans
  calc
    _ ≤ ((Fintype.card (Row d H)).factorial *
        (Real.exp ((H : ℝ)*coefficientError d ws))^Fintype.card (Row d H) *
          Real.exp ((Fintype.card (Row d H) : ℝ)*(H : ℝ)*Real.log 2/(d.curveJetWeights 0 : ℝ))) *
        Real.exp (-L*Fintype.card (Row d H)+
          TaylorPacking.augmentedCount (TaylorPacking.combinedWeights
            (MatrixArithmetic.logWeights d.q) nu) L) *
          ((1-TaylorPacking.quarterRatio)⁻¹)^(2*Fintype.card (Row d H)) := by
      have hg : 0 ≤ (1-TaylorPacking.quarterRatio)⁻¹ :=
        inv_nonneg.mpr (sub_nonneg.mpr TaylorPacking.quarterRatio_lt_one.le)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (choice_test_product_le d H f) (by positivity))
          (Real.exp_pos _).le) (pow_nonneg hg _)
    _ = _ := by
      have he : (Fintype.card (Row d H) : ℝ)*(H : ℝ)*holomorphicError d ws -
          L*Fintype.card (Row d H) + TaylorPacking.augmentedCount
            (TaylorPacking.combinedWeights (MatrixArithmetic.logWeights d.q) nu) L =
          ((Fintype.card (Row d H) : ℝ)*((H : ℝ)*coefficientError d ws) +
            (Fintype.card (Row d H) : ℝ)*(H : ℝ)*Real.log 2/(d.curveJetWeights 0 : ℝ)) +
              (-L*Fintype.card (Row d H)+TaylorPacking.augmentedCount
                (TaylorPacking.combinedWeights (MatrixArithmetic.logWeights d.q) nu) L) := by
        dsimp only [holomorphicError]
        ring
      simp only [he, Real.exp_add, Real.exp_nat_mul]
      ring

#print axioms hasSum_choiceEntry
#print axioms weighted_choiceMatrix_raw_bound
#print axioms weighted_choiceMatrix_bound

end LogarithmExtension.LogRatio.CommonTaylor

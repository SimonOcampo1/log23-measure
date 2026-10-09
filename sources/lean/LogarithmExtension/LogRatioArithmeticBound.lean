import LogarithmExtension.LogRatioMatrixArithmetic

/-!
# Normalized arithmetic lower bound for the two-base determinant

The prescribed logarithmic degree weights give an arithmetic charge of
at most one per normalized column.  The row factors return their exact
mean auxiliary weight, up to the explicit ceiling loss.  The lcm constant
here is the (slightly larger) constant proved in the pinned upstream
arithmetic development; no sharp prime-number estimate is needed.
-/

noncomputable section
namespace LogarithmExtension.LogRatio.ArithmeticBound

open OAI OAI.PiExponent MatrixArithmetic BoundedJetMatrix
open scoped BigOperators

def rowWeightedSum (d : GeometryData) (H : ℚ) : ℝ :=
  ∑ row : Row d H, ∑ i, (row.2.val i.succ.succ : ℝ) * logWeights d.q i

def meanRowWeight (d : GeometryData) (H : ℚ) : ℝ :=
  rowWeightedSum d H / ((Fintype.card (Row d H) : ℝ) * H)

def arithmeticError (d : GeometryData) (F v wmin : ℝ) : ℝ :=
  Arithmetic.lcmConstant * F * d.m / (d.curveJetWeights 0 : ℝ) +
    Arithmetic.lcmConstant * ∑ i, 1 / logWeights d.q i + v / wmin

theorem logWeights_pos (d : GeometryData)
    (hW : ∀ i, (d.curveDegreeWeights i.succ.succ : ℝ) = logWeights d.q i)
    (i : Fin d.m) : 0 < logWeights d.q i := by
  rw [← hW]
  exact_mod_cast d.curveDegreeWeights_pos i.succ.succ

theorem column_log_cost_le (d : GeometryData) (H : ℚ)
    (hW : ∀ i, (d.curveDegreeWeights i.succ.succ : ℝ) = logWeights d.q i)
    (col : Column d H) :
    (∑ i, (col.val i.succ.succ : ℝ) * Real.log (d.q i)) ≤ H := by
  have hw (k : Fin (d.m+2)) : (0 : ℝ) < d.curveDegreeWeights k := by
    exact_mod_cast d.curveDegreeWeights_pos k
  have hcol := (mem_realWeightedSimplex hw).mp col.property
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at hcol
  simp only [Fin.succ_zero_eq_one, hW] at hcol
  have h0 : 0 ≤ (d.curveDegreeWeights 0 : ℝ) * col.val 0 :=
    mul_nonneg (hw 0).le (Nat.cast_nonneg _)
  have h1 : 0 ≤ (d.curveDegreeWeights 1 : ℝ) * col.val 1 :=
    mul_nonneg (hw 1).le (Nat.cast_nonneg _)
  have hcost := Arithmetic.column_log_cost_le Finset.univ (fun i => col.val i.succ.succ) d.q
  change (∑ i, (col.val i.succ.succ : ℝ) * Real.log (d.q i)) ≤
    ∑ i, (col.val i.succ.succ : ℝ) * logWeights d.q i at hcost
  have he : (∑ i, (col.val i.succ.succ : ℝ) * logWeights d.q i) =
      ∑ i, logWeights d.q i * (col.val i.succ.succ : ℝ) := by
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  rw [he] at hcost
  linarith

theorem columnCost_le (d : GeometryData) (H : ℚ)
    (hW : ∀ i, (d.curveDegreeWeights i.succ.succ : ℝ) = logWeights d.q i)
    (selection : Row d H → Column d H) :
    columnCost d H selection ≤ (Fintype.card (Row d H) : ℝ) * H := by
  calc
    _ ≤ ∑ row : Row d H, (H : ℝ) :=
      Finset.sum_le_sum (fun row _ => column_log_cost_le d H hW (selection row))
    _ = _ := by simp

theorem row_weight_le (d : GeometryData) (H : ℚ) (v : ℝ) (hv : 0 < v)
    (hV : ∀ i, (d.curveJetWeights i.succ.succ : ℝ) = logWeights d.q i / v)
    (row : Row d H) :
    (∑ i, (row.2.val i.succ.succ : ℝ) * logWeights d.q i) ≤ (H : ℝ) * v := by
  have hw (k : Fin (d.m+2)) : (0 : ℝ) < d.curveJetWeights k := by
    exact_mod_cast d.curveJetWeights_pos k
  have hrow := (mem_strictWeightedSimplex hw).mp row.2.property
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at hrow
  simp only [Fin.succ_zero_eq_one, hV, div_mul_eq_mul_div, ← Finset.sum_div] at hrow
  have h0 : 0 ≤ (d.curveJetWeights 0 : ℝ) * row.2.val 0 :=
    mul_nonneg (hw 0).le (Nat.cast_nonneg _)
  have h1 : 0 ≤ (d.curveJetWeights 1 : ℝ) * row.2.val 1 :=
    mul_nonneg (hw 1).le (Nat.cast_nonneg _)
  have hh : (∑ i, logWeights d.q i * (row.2.val i.succ.succ : ℝ)) / v ≤ H := by linarith
  have hm := (div_le_iff₀ hv).mp hh
  simpa only [mul_comm] using hm

theorem rowCost_lower (d : GeometryData) (H : ℚ) (v wmin : ℝ)
    (hv : 0 < v) (hmin : 0 < wmin) (hwmin : ∀ i, wmin ≤ logWeights d.q i)
    (hV : ∀ i, (d.curveJetWeights i.succ.succ : ℝ) = logWeights d.q i / v) :
    rowWeightedSum d H - (Fintype.card (Row d H) : ℝ) * H * v / wmin ≤ rowCost d H := by
  have hr (row : Row d H) := Arithmetic.row_log_cost_lower Finset.univ
    (fun i => row.2.val i.succ.succ) d.q wmin ((H : ℝ)*v) hmin
    (fun i _ => hwmin i) (row_weight_le d H v hv hV row)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun row _ => hr row)
  simpa only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_div_assoc, mul_assoc, rowWeightedSum,
    LogarithmExtension.LogRatio.MatrixArithmetic.rowCost, logWeights] using hs

theorem clearingDenominator_log_le (d : GeometryData) (F : ℝ) (H : ℚ)
    (hF : 0 ≤ F) (hH : 0 < H)
    (hW : ∀ i, (d.curveDegreeWeights i.succ.succ : ℝ) = logWeights d.q i) :
    Real.log (clearingDenominator d (truncationOrders d.q F (d.curveJetWeights 0)) H) ≤
      (H : ℝ) * (Arithmetic.lcmConstant * F * d.m / (d.curveJetWeights 0 : ℝ) +
        Arithmetic.lcmConstant * ∑ i, 1 / logWeights d.q i) := by
  have hv0 : (0 : ℝ) < d.curveJetWeights 0 := by exact_mod_cast d.curveJetWeights_pos 0
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have h := OAI.PiExponent.MatrixArithmetic.log_denominator_le F (d.curveJetWeights 0) H
    hF hv0 hHR (logWeights_pos d hW)
  simpa only [clearingDenominator, clearingOrders, hW,
    OAI.PiExponent.MatrixArithmetic.denominator] using h

theorem row_card_pos (d : GeometryData) (H : ℚ) (hK : 0 < d.K) (hH : 0 < H) :
    0 < Fintype.card (Row d H) := by
  apply Fintype.card_pos_iff.mpr
  refine ⟨⟨⟨0, hK⟩, ⟨fun _ => 0, ?_⟩⟩⟩
  have hw (k : Fin (d.m+2)) : (0 : ℝ) < d.curveJetWeights k := by
    exact_mod_cast d.curveJetWeights_pos k
  apply (mem_strictWeightedSimplex hw).mpr
  simpa using (show (0 : ℝ) < H by exact_mod_cast hH)

/-- The normalized arithmetic estimate, for the same determinant as interpolation. -/
theorem normalized_determinant_lower_bound (d : GeometryData) (H : ℚ) (F v wmin : ℝ)
    (hK : 0 < d.K) (hH : 0 < H) (hF : 0 ≤ F) (hv : 0 < v) (hmin : 0 < wmin)
    (hwmin : ∀ i, wmin ≤ logWeights d.q i)
    (hW : ∀ i, (d.curveDegreeWeights i.succ.succ : ℝ) = logWeights d.q i)
    (hV : ∀ i, (d.curveJetWeights i.succ.succ : ℝ) = logWeights d.q i / v)
    (selection : Row d H → Column d H)
    (hdet : (selectedMinor d (truncationOrders d.q F (d.curveJetWeights 0)) H selection).det ≠ 0) :
    -(1 - meanRowWeight d H) - arithmeticError d F v wmin ≤
      Real.log ‖(selectedMinor d (truncationOrders d.q F (d.curveJetWeights 0)) H selection).det‖ /
        ((Fintype.card (Row d H) : ℝ) * H) := by
  have hM : (0 : ℝ) < Fintype.card (Row d H) := by exact_mod_cast row_card_pos d H hK hH
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hclear := determinant_log_lower_bound d
    (truncationOrders d.q F (d.curveJetWeights 0)) H selection hdet
  have hrow := rowCost_lower d H v wmin hv hmin hwmin hV
  apply Arithmetic.normalized_arithmetic_bound
    (Fintype.card (Row d H)) H (meanRowWeight d H)
    (Arithmetic.lcmConstant * F * d.m / (d.curveJetWeights 0 : ℝ) +
      Arithmetic.lcmConstant * ∑ i, 1 / logWeights d.q i)
    (v / wmin)
    (Real.log (clearingDenominator d (truncationOrders d.q F (d.curveJetWeights 0)) H))
    (columnCost d H selection) (rowCost d H) _ hM hHR
    (by linarith) (clearingDenominator_log_le d F H hF hH hW)
    (columnCost_le d H hW selection)
  simpa only [meanRowWeight, mul_div_cancel₀ _ (mul_pos hM hHR).ne', mul_div_assoc] using hrow

/-- The prescribed fixed cutoffs satisfy both geometric truncation conditions. -/
theorem truncation_conditions (d : GeometryData) (F v : ℝ)
    (hF : 1/v ≤ F)
    (hW : ∀ i, (d.curveDegreeWeights i.succ.succ : ℝ) = logWeights d.q i)
    (hV : ∀ i, (d.curveJetWeights i.succ.succ : ℝ) = logWeights d.q i / v) :
    (∀ i, d.curveJetWeights i.succ.succ ≤
      (truncationOrders d.q F (d.curveJetWeights 0) i : ℚ) * d.curveJetWeights 0) ∧
    (∀ i, d.curveJetWeights i.succ.succ ≤
      (truncationOrders d.q F (d.curveJetWeights 0) i : ℚ) * d.curveJetWeights 1) := by
  have hv0 : (0 : ℝ) < d.curveJetWeights 0 := by exact_mod_cast d.curveJetWeights_pos 0
  have ht (i : Fin d.m) : d.curveJetWeights i.succ.succ ≤
      (truncationOrders d.q F (d.curveJetWeights 0) i : ℚ) * d.curveJetWeights 0 := by
    have hc := (div_le_iff₀ hv0).mp
      (Nat.le_ceil (F * logWeights d.q i / (d.curveJetWeights 0 : ℝ)))
    have hf := mul_le_mul_of_nonneg_right hF (logWeights_pos d hW i).le
    have hi : (d.curveJetWeights i.succ.succ : ℝ) ≤
        (truncationOrders d.q F (d.curveJetWeights 0) i : ℝ) * d.curveJetWeights 0 := by
      rw [hV]
      unfold truncationOrders
      calc
        _ = (1/v) * logWeights d.q i := by ring
        _ ≤ F * logWeights d.q i := hf
        _ ≤ _ := hc
    exact_mod_cast hi
  exact ⟨ht, fun i => by rw [d.jet_base_eq]; exact ht i⟩

/-- Geometry and arithmetic together produce a nonzero minor with its size bound;
neither nonvanishing nor an arithmetic estimate is assumed at this endpoint. -/
theorem eventually_nonzero_minor_with_lower_bound (d : GeometryData) (F v wmin : ℝ)
    (hK : 0 < d.K) (hv : 0 < v) (hF : 1/v ≤ F) (hmin : 0 < wmin)
    (hwmin : ∀ i, wmin ≤ logWeights d.q i)
    (hW : ∀ i, (d.curveDegreeWeights i.succ.succ : ℝ) = logWeights d.q i)
    (hV : ∀ i, (d.curveJetWeights i.succ.succ : ℝ) = logWeights d.q i / v) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∃ selection : Row d ((n : ℚ) * (BlowupGeometry.scale d).radius) →
          Column d ((n : ℚ) * (BlowupGeometry.scale d).radius),
        Function.Injective selection ∧
        (selectedMinor d (truncationOrders d.q F (d.curveJetWeights 0))
          ((n : ℚ) * (BlowupGeometry.scale d).radius) selection).det ≠ 0 ∧
        -(1 - meanRowWeight d ((n : ℚ) * (BlowupGeometry.scale d).radius)) -
          arithmeticError d F v wmin ≤
          Real.log ‖(selectedMinor d (truncationOrders d.q F (d.curveJetWeights 0))
            ((n : ℚ) * (BlowupGeometry.scale d).radius) selection).det‖ /
            ((Fintype.card (Row d ((n : ℚ) * (BlowupGeometry.scale d).radius)) : ℝ) *
              ((n : ℚ) * (BlowupGeometry.scale d).radius : ℚ)) := by
  obtain ⟨hT0, hT1⟩ := truncation_conditions d F v hF hW hV
  filter_upwards [BoundedJetMatrix.eventually_nonzero_minor d
    (truncationOrders d.q F (d.curveJetWeights 0)) hT0 hT1,
    Filter.eventually_ge_atTop (1 : ℕ)] with n hn hn1
  obtain ⟨selection, hinj, hdet⟩ := hn
  have hn0 : (0 : ℚ) < n := by exact_mod_cast (Nat.zero_lt_one.trans_le hn1)
  have hR : (0 : ℚ) < (BlowupGeometry.scale d).radius := by
    exact_mod_cast (BlowupGeometry.scale d).radius_pos
  refine ⟨selection, hinj, hdet, ?_⟩
  exact normalized_determinant_lower_bound d _ F v wmin hK (mul_pos hn0 hR)
    ((one_div_pos.mpr hv).le.trans hF) hv hmin hwmin hW hV selection hdet

#print axioms normalized_determinant_lower_bound
#print axioms eventually_nonzero_minor_with_lower_bound

end LogarithmExtension.LogRatio.ArithmeticBound

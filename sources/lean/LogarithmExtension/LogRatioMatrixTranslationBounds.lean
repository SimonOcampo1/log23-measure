import LogarithmExtension.LogRatioScalarBound
import LogarithmExtension.LogRatioArithmeticBound

/-!
# Approximation-sensitive scalar bounds for the concrete two-base matrix

This module specializes the scalar estimate to the actual slopes, logarithmic
weights, fixed truncation orders and row choices of the interpolation matrix.
-/

noncomputable section
namespace LogarithmExtension.LogRatio.AnalyticTranslation

open OAI OAI.PiExponent NestedJets BoundedJetMatrix
open InterpolationMatrix (exponentVector exponentVector_apply)
open scoped BigOperators

theorem actual_error_exp (d : GeometryData) (theta nu : ℝ) (hnu : 0 ≤ nu)
    (happrox : ∀ i, |theta-(d.p i : ℝ)/d.q i| ≤ (d.q i : ℝ)^(-nu)) :
    ∀ i, ‖(theta : ℂ)-d.slopes i‖ ≤
      Real.exp (nu-nu*MatrixArithmetic.logWeights d.q i) := by
  intro i
  have hb := (happrox i).trans
    (rpow_neg_le_exp_ceil_log nu hnu (Nat.one_le_iff_ne_zero.mpr (d.q_pos i).ne'))
  rw [← Real.exp_add] at hb
  have he : (theta : ℂ)-d.slopes i = ((theta-(d.p i : ℝ)/d.q i : ℝ) : ℂ) := by
    simp [GeometryData.slopes]
  rw [he, Complex.norm_real, Real.norm_eq_abs]
  simpa only [sub_eq_add_neg, MatrixArithmetic.logWeights, neg_mul] using hb

theorem row_base_degree_le (d : GeometryData) (H : ℚ) (row : Row d H) :
    ((baseIndex (exponentVector row.2.val)).degree : ℝ) ≤
      (H : ℝ)/(d.curveJetWeights 0 : ℝ) := by
  have hw (i : Fin (d.m+2)) : (0 : ℝ) < d.curveJetWeights i := by
    exact_mod_cast d.curveJetWeights_pos i
  have hr := (mem_strictWeightedSimplex hw).mp row.2.property
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at hr
  simp only [Fin.succ_zero_eq_one, d.jet_base_eq] at hr
  have haux : (0 : ℝ) ≤ ∑ i : Fin d.m, (d.curveJetWeights i.succ.succ : ℝ) *
      row.2.val i.succ.succ :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hw i.succ.succ).le (Nat.cast_nonneg _))
  rw [base_index_degree, baseIndex_zero, baseIndex_one, exponentVector_apply,
    exponentVector_apply, Nat.cast_add]
  apply (le_div_iff₀ (hw 0)).mpr
  nlinarith

theorem choice_degree_le (d : GeometryData) (H : ℚ) (row : Row d H)
    (t : RowChoice d H row) :
    (t.2.val.1.degree : ℝ) ≤ (H : ℝ)/(d.curveJetWeights 0 : ℝ) := by
  have he := Finset.HasAntidiagonal.mem_antidiagonal.mp t.2.property
  have hd := congrArg Finsupp.degree he
  rw [map_add] at hd
  have hle : t.2.val.1.degree ≤ (baseIndex (exponentVector row.2.val)).degree := by omega
  exact (show (t.2.val.1.degree : ℝ) ≤ (baseIndex (exponentVector row.2.val)).degree by
    exact_mod_cast hle).trans (row_base_degree_le d H row)

def translationError (d : GeometryData) (nu F ws : ℝ) : ℝ :=
  nu/F + Real.log 2/(d.curveJetWeights 0 : ℝ) + (Real.log 12+nu)/ws

/-- No matrix rank or nonvanishing premise is needed for this analytic bound. -/
theorem norm_choiceScalar_le (d : GeometryData) (theta nu F ws : ℝ) (H : ℚ)
    (hnu : 0 ≤ nu) (hF : 0 < F) (hws : 0 < ws)
    (hwmin : ∀ i, ws ≤ MatrixArithmetic.logWeights d.q i)
    (hW : ∀ i, (d.curveDegreeWeights i.succ.succ : ℝ) = MatrixArithmetic.logWeights d.q i)
    (hr : ∀ i, ‖d.slopes i‖ ≤ 2)
    (happrox : ∀ i, |theta-(d.p i : ℝ)/d.q i| ≤ (d.q i : ℝ)^(-nu))
    (row : Row d H) (t : RowChoice d H row) :
    ‖choiceScalar d (MatrixArithmetic.truncationOrders d.q F (d.curveJetWeights 0)) H theta row t‖ ≤
      ((⌊(H : ℝ)⌋₊+1 : ℕ) : ℝ)^d.m *
        Real.exp (-nu *
          (MatrixTranslationBounds.weight (MatrixArithmetic.logWeights d.q) (fun i => t.1.val i) -
            MatrixTranslationBounds.weight (MatrixArithmetic.logWeights d.q)
              (fun i => row.2.val i.succ.succ)) +
          (H : ℝ)*translationError d nu F ws) := by
  have hv : (0 : ℝ) < d.curveJetWeights 0 := by exact_mod_cast d.curveJetWeights_pos 0
  have hwpos := ArithmeticBound.logWeights_pos d hW
  have hw1 (i : Fin d.m) : 1 ≤ MatrixArithmetic.logWeights d.q i := by
    have hp : (0 : ℝ) < (⌈Real.log (d.q i : ℝ)⌉₊ : ℝ) := hwpos i
    have hn : 1 ≤ ⌈Real.log (d.q i : ℝ)⌉₊ := Nat.one_le_iff_ne_zero.mpr
      (by intro hz; simp [hz] at hp)
    change (1 : ℝ) ≤ (⌈Real.log (d.q i : ℝ)⌉₊ : ℝ)
    exact_mod_cast hn
  have ht : ∀ i, 1 ≤ MatrixArithmetic.truncationOrders d.q F (d.curveJetWeights 0) i := by
    intro i
    exact MatrixTranslationBounds.truncationOrder_pos hF hv (hwpos i)
  have htw : ∀ i, F*MatrixArithmetic.logWeights d.q i ≤
      (d.curveJetWeights 0 : ℝ)*MatrixArithmetic.truncationOrders d.q F (d.curveJetWeights 0) i := by
    intro i
    exact MatrixTranslationBounds.truncationOrder_budget hv
  have ha : MatrixTranslationBounds.weight (MatrixArithmetic.logWeights d.q)
      (fun i => t.1.val i) ≤ H := by
    have htidx := t.1.property
    change t.1.val ∈ MatrixTranslation.transverseIndices
      (fun i => (d.curveDegreeWeights i.succ.succ : ℝ)) H at htidx
    simpa only [hW, MatrixTranslationBounds.weight] using (MatrixTranslation.mem_transverseIndices _ _
      (fun i => by exact_mod_cast d.curveDegreeWeights_pos i.succ.succ) t.1.val).mp htidx
  simpa only [choiceScalar, auxiliaryIndex_apply, exponentVector_apply, translationError] using
    norm_rowScalar_exp_weighted theta d.slopes
      (MatrixArithmetic.truncationOrders d.q F (d.curveJetWeights 0))
      (auxiliaryIndex (exponentVector row.2.val)) t.1.val t.2.val.1
      (MatrixArithmetic.logWeights d.q) nu nu H ws (d.curveJetWeights 0) F
      hnu hnu hws hv hF hwmin hw1 ha (choice_degree_le d H row t) ht htw hr
      (actual_error_exp d theta nu hnu happrox)

theorem antidiagonal_card_le (ell : Fin 2 →₀ ℕ) :
    (Finset.HasAntidiagonal.antidiagonal ell).card ≤ (ell 0+1)*(ell 1+1) := by
  classical
  have hle (t : ↥(Finset.HasAntidiagonal.antidiagonal ell)) (i : Fin 2) : t.val.1 i ≤ ell i := by
    have ht := congrArg (fun a : Fin 2 →₀ ℕ => a i)
      (Finset.HasAntidiagonal.mem_antidiagonal.mp t.property)
    simp only [Finsupp.add_apply] at ht
    omega
  let f : ↥(Finset.HasAntidiagonal.antidiagonal ell) → Fin (ell 0+1) × Fin (ell 1+1) :=
    fun t => (⟨t.val.1 0, Nat.lt_succ_of_le (hle t 0)⟩,
      ⟨t.val.1 1, Nat.lt_succ_of_le (hle t 1)⟩)
  have hf : Function.Injective f := by
    intro t u h
    have h0 := congrArg (fun x : Fin (ell 0+1) × Fin (ell 1+1) => x.1.val) h
    have h1 := congrArg (fun x : Fin (ell 0+1) × Fin (ell 1+1) => x.2.val) h
    have hfirst : t.val.1 = u.val.1 := by
      ext i
      fin_cases i
      · exact h0
      · exact h1
    apply Subtype.ext
    apply Prod.ext hfirst
    apply add_left_cancel (a := t.val.1)
    calc
      t.val.1+t.val.2 = ell := Finset.HasAntidiagonal.mem_antidiagonal.mp t.property
      _ = u.val.1+u.val.2 := (Finset.HasAntidiagonal.mem_antidiagonal.mp u.property).symm
      _ = t.val.1+u.val.2 := by rw [hfirst]
  simpa using Fintype.card_le_of_injective f hf

theorem rowChoice_card_le (d : GeometryData) (H : ℚ)
    (hw : ∀ i : Fin d.m, 1 ≤ (d.curveDegreeWeights i.succ.succ : ℝ)) (row : Row d H) :
    Fintype.card (RowChoice d H row) ≤
      (⌊(H : ℝ)⌋₊+1)^d.m * (⌊(H : ℝ)/(d.curveJetWeights 0 : ℝ)⌋₊+1)^2 := by
  classical
  have hdeg := row_base_degree_le d H row
  rw [base_index_degree] at hdeg
  have h0 : (baseIndex (exponentVector row.2.val)) 0 ≤
      ⌊(H : ℝ)/(d.curveJetWeights 0 : ℝ)⌋₊ := by
    apply Nat.le_floor
    push_cast at hdeg
    linarith [Nat.cast_nonneg ((baseIndex (exponentVector row.2.val)) 1) (α := ℝ)]
  have h1 : (baseIndex (exponentVector row.2.val)) 1 ≤
      ⌊(H : ℝ)/(d.curveJetWeights 0 : ℝ)⌋₊ := by
    apply Nat.le_floor
    push_cast at hdeg
    linarith [Nat.cast_nonneg ((baseIndex (exponentVector row.2.val)) 0) (α := ℝ)]
  rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_coe]
  apply Nat.mul_le_mul
  · exact MatrixTranslation.transverseIndices_card_le _ _ hw
  · exact (antidiagonal_card_le _).trans (by
      rw [pow_two]
      exact Nat.mul_le_mul (Nat.add_le_add_right h0 1) (Nat.add_le_add_right h1 1))

theorem choiceFamily_card_le (d : GeometryData) (H : ℚ)
    (hw : ∀ i : Fin d.m, 1 ≤ (d.curveDegreeWeights i.succ.succ : ℝ)) :
    Fintype.card (ChoiceFamily d H) ≤
      ((⌊(H : ℝ)⌋₊+1)^d.m * (⌊(H : ℝ)/(d.curveJetWeights 0 : ℝ)⌋₊+1)^2)^
        Fintype.card (Row d H) := by
  classical
  rw [Fintype.card_pi]
  calc
    _ ≤ ∏ _row : Row d H,
        ((⌊(H : ℝ)⌋₊+1)^d.m * (⌊(H : ℝ)/(d.curveJetWeights 0 : ℝ)⌋₊+1)^2) :=
      Finset.prod_le_prod (fun row _ => rowChoice_card_le d H hw row)
    _ = _ := by simp

def choiceAuxiliaryWeight (d : GeometryData) (H : ℚ) (f : ChoiceFamily d H) : ℝ :=
  ∑ row, MatrixTranslationBounds.weight (MatrixArithmetic.logWeights d.q) (fun i => (f row).1.val i)

theorem norm_product_choiceScalar_le (d : GeometryData) (theta nu F ws : ℝ) (H : ℚ)
    (hnu : 0 ≤ nu) (hF : 0 < F) (hws : 0 < ws)
    (hwmin : ∀ i, ws ≤ MatrixArithmetic.logWeights d.q i)
    (hW : ∀ i, (d.curveDegreeWeights i.succ.succ : ℝ) = MatrixArithmetic.logWeights d.q i)
    (hr : ∀ i, ‖d.slopes i‖ ≤ 2)
    (happrox : ∀ i, |theta-(d.p i : ℝ)/d.q i| ≤ (d.q i : ℝ)^(-nu))
    (f : ChoiceFamily d H) :
    ‖∏ row, choiceScalar d (MatrixArithmetic.truncationOrders d.q F (d.curveJetWeights 0))
      H theta row (f row)‖ ≤
      (((⌊(H : ℝ)⌋₊+1 : ℕ) : ℝ)^d.m)^Fintype.card (Row d H) *
        Real.exp (-nu * (choiceAuxiliaryWeight d H f - ArithmeticBound.rowWeightedSum d H) +
          (Fintype.card (Row d H) : ℝ)*(H : ℝ)*translationError d nu F ws) := by
  classical
  have hb : (∑ row : Row d H, MatrixTranslationBounds.weight (MatrixArithmetic.logWeights d.q)
      (fun i => row.2.val i.succ.succ)) = ArithmeticBound.rowWeightedSum d H := by
    simp only [MatrixTranslationBounds.weight, ArithmeticBound.rowWeightedSum]
    apply Finset.sum_congr rfl
    intro row _
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  have hexp : (∑ row : Row d H,
      (-nu * (MatrixTranslationBounds.weight (MatrixArithmetic.logWeights d.q)
        (fun i => (f row).1.val i) -
          MatrixTranslationBounds.weight (MatrixArithmetic.logWeights d.q)
            (fun i => row.2.val i.succ.succ)) + (H : ℝ)*translationError d nu F ws)) =
      -nu * (choiceAuxiliaryWeight d H f-ArithmeticBound.rowWeightedSum d H) +
        (Fintype.card (Row d H) : ℝ)*(H : ℝ)*translationError d nu F ws := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hb]
    simp only [choiceAuxiliaryWeight, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [norm_prod]
  calc
    _ ≤ ∏ row : Row d H,
        (((⌊(H : ℝ)⌋₊+1 : ℕ) : ℝ)^d.m *
          Real.exp (-nu * (MatrixTranslationBounds.weight (MatrixArithmetic.logWeights d.q)
            (fun i => (f row).1.val i) -
              MatrixTranslationBounds.weight (MatrixArithmetic.logWeights d.q)
                (fun i => row.2.val i.succ.succ)) + (H : ℝ)*translationError d nu F ws)) :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        (fun row _ => norm_choiceScalar_le d theta nu F ws H hnu hF hws hwmin hW hr happrox row (f row))
    _ = _ := by
      rw [Finset.prod_mul_distrib, ← Real.exp_sum, hexp]
      simp

#print axioms norm_choiceScalar_le
#print axioms rowChoice_card_le
#print axioms norm_product_choiceScalar_le

end LogarithmExtension.LogRatio.AnalyticTranslation

import LogarithmExtension.LogRatioParameterContradiction
import LogarithmExtension.LogRatioApproximationSelection
import LogarithmExtension.LogRatioWeightSeparation

/-!
# Assembling the actual geometric data from reduced exceptional fractions

The order is seed, truncation scale, dimension, global auxiliary threshold,
and only then the successive fractions. No rank or determinant is assumed.
-/

noncomputable section
namespace LogarithmExtension.LogRatio.AdmissibleData

open ParameterSeeds ParameterDimension ParameterChoice ParameterContradiction
open ApproximationSelection WeightSeparation CommonTaylor
open scoped BigOperators

def auxWeight (r : ℕ → ℚ) (i : ℕ) : ℚ := Nat.ceil (Real.log (r i).den)
def degreeWeights (m : ℕ) (w0 : ℚ) (r : ℕ → ℚ) : Fin (m+2) → ℚ :=
  Fin.cases w0 (Fin.cases w0 (fun i => auxWeight r i.val))
def jetWeights (m : ℕ) (v0 v : ℚ) (r : ℕ → ℚ) : Fin (m+2) → ℚ :=
  Fin.cases v0 (Fin.cases v0 (fun i => auxWeight r i.val/v))

@[simp] theorem auxWeight_cast (r : ℕ → ℚ) (i : ℕ) : (auxWeight r i : ℝ) = weight (r i) := by
  simp [auxWeight, weight]
@[simp] theorem degreeWeights_zero (m : ℕ) (w0 : ℚ) (r : ℕ → ℚ) : degreeWeights m w0 r 0 = w0 := rfl
@[simp] theorem degreeWeights_one (m : ℕ) (w0 : ℚ) (r : ℕ → ℚ) : degreeWeights m w0 r 1 = w0 := rfl
@[simp] theorem degreeWeights_aux (m : ℕ) (w0 : ℚ) (r : ℕ → ℚ) (i : Fin m) :
    degreeWeights m w0 r i.succ.succ = auxWeight r i.val := rfl
@[simp] theorem jetWeights_zero (m : ℕ) (v0 v : ℚ) (r : ℕ → ℚ) : jetWeights m v0 v r 0 = v0 := rfl
@[simp] theorem jetWeights_one (m : ℕ) (v0 v : ℚ) (r : ℕ → ℚ) : jetWeights m v0 v r 1 = v0 := rfl
@[simp] theorem jetWeights_aux (m : ℕ) (v0 v : ℚ) (r : ℕ → ℚ) (i : Fin m) :
    jetWeights m v0 v r i.succ.succ = auxWeight r i.val/v := rfl

theorem degreeWeights_cast (m : ℕ) (w0 : ℚ) (r : ℕ → ℚ) (i : Fin (m+2)) :
    (degreeWeights m w0 r i : ℝ) = degreeWeight w0 (normalizedWeight r) i.val := by
  cases i using Fin.cases with
  | zero => simp [degreeWeights, degreeWeight]
  | succ i =>
    cases i using Fin.cases with
    | zero => simp [degreeWeights, degreeWeight]
    | succ i =>
      simp [degreeWeights, degreeWeight, normalizedWeight, show ¬ i.val+1+1 < 2 by omega]

theorem jetWeights_cast (m : ℕ) (v0 v : ℚ) (r : ℕ → ℚ) (i : Fin (m+2)) :
    (jetWeights m v0 v r i : ℝ) = jetWeight v0 v (normalizedWeight r) i.val := by
  cases i using Fin.cases with
  | zero => simp [jetWeights, jetWeight]
  | succ i =>
    cases i using Fin.cases with
    | zero => simp [jetWeights, jetWeight]
    | succ i =>
      simp [jetWeights, jetWeight, normalizedWeight, show ¬ i.val+1+1 < 2 by omega]

theorem degreeWeights_pos (m : ℕ) (w0 : ℚ) (r : ℕ → ℚ) (hw0 : 0 < w0)
    (hw : ∀ i, 0 < auxWeight r i) : ∀ i, 0 < degreeWeights m w0 r i := by
  intro i
  cases i using Fin.cases with
  | zero => exact hw0
  | succ i =>
    cases i using Fin.cases with
    | zero => exact hw0
    | succ i => exact hw i.val

theorem jetWeights_pos (m : ℕ) (v0 v : ℚ) (r : ℕ → ℚ) (hv0 : 0 < v0) (hv : 0 < v)
    (hw : ∀ i, 0 < auxWeight r i) : ∀ i, 0 < jetWeights m v0 v r i := by
  intro i
  cases i using Fin.cases with
  | zero => exact hv0
  | succ i =>
    cases i using Fin.cases with
    | zero => exact hv0
    | succ i => exact div_pos (hw i.val) hv

theorem degreeWeights_prod (m : ℕ) (w0 : ℚ) (r : ℕ → ℚ) :
    (∏ i, (degreeWeights m w0 r i : ℝ)) = (w0 : ℝ)^2*(∏ i : Fin m, weight (r i.val)) := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [degreeWeights, Fin.cases_zero, Fin.cases_succ, auxWeight_cast]
  ring

theorem jetWeights_prod (m : ℕ) (v0 v : ℚ) (r : ℕ → ℚ) :
    (∏ i, (jetWeights m v0 v r i : ℝ)) =
      (v0 : ℝ)^2*(∏ i : Fin m, weight (r i.val))/(v : ℝ)^m := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [jetWeights, Fin.cases_zero, Fin.cases_succ, Rat.cast_div, auxWeight_cast,
    Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

theorem ratioTheta_gt_one : 1 < ratioTheta := by
  apply (lt_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  rw [one_mul]
  exact Real.log_lt_log (by norm_num) (by norm_num)

/-- An unbounded reduced exceptional family cannot exist above exponent three. -/
theorem not_unbounded_exceptional (nu : ℚ) (hnu : 3 < nu) :
    ¬ UnboundedExceptional ratioTheta (nu : ℝ) := by
  intro hbad
  let P := explicitSeed nu hnu
  obtain ⟨A⟩ := exists_choice P hnu
  obtain ⟨ws, hws, hmargin⟩ := exists_auxiliary_threshold P A hnu
  let m := 2*A.n
  let W0 := w0 P A.n
  let V0 := v0 P A.n
  let sig := sigma P A.n
  let eps : ℝ := (sig : ℝ)/((m : ℝ)+3)
  have hW0 : (0 : ℝ) < W0 := w0_pos P A.n
  have hV0 : (0 : ℝ) < V0 := v0_pos P A.n
  have hsig : (0 : ℝ) < sig := sigma_pos P A.n
  have heps : 0 < eps := div_pos hsig (by positivity)
  let D := separationFactor (m+2) eps W0 V0 P.v
  obtain ⟨Q, hQ⟩ := exists_nat_gt ((1+(sig : ℝ))*(W0 : ℝ)/(V0 : ℝ))
  have hnur : (0 : ℝ) < nu := by exact_mod_cast (show 0 < nu by linarith)
  obtain ⟨r, hr, hx, hgrowth⟩ := exists_growing_reduced ratioTheta nu ratioTheta_gt_one
    ratioTheta_lt_two hnur hbad Q ws D
  have hwr (i : ℕ) : 0 < weight (r i) := hws.trans (hr i).2.2.2.2
  have hw (i : ℕ) : (0 : ℚ) < auxWeight r i := by
    have h : (0 : ℝ) < (auxWeight r i : ℝ) := by rw [auxWeight_cast]; exact hwr i
    exact_mod_cast h
  have hW : ∀ i, 0 < degreeWeights m W0 r i :=
    degreeWeights_pos m W0 r (by exact_mod_cast hW0) hw
  have hV : ∀ i, 0 < jetWeights m V0 P.v r i :=
    jetWeights_pos m V0 P.v r (by exact_mod_cast hV0) P.v_pos hw
  have hxbase (i : ℕ) (hi : i < 2) : normalizedWeight r i = 1 := by
    interval_cases i <;> rfl
  have hvolume : (K P A.n : ℝ)*(1+3*(sig : ℝ))^(m+2)*
      (∏ i, (degreeWeights m W0 r i : ℝ))/(∏ i, (jetWeights m V0 P.v r i : ℝ)) < 1 := by
    have hprod : (∏ i : Fin m, weight (r i.val)) ≠ 0 :=
      (Finset.prod_pos (fun i _ => hwr i.val)).ne'
    have hv := P.v_pos_real
    have he : (K P A.n : ℝ)*(1+3*(sig : ℝ))^(m+2)*
        (∏ i, (degreeWeights m W0 r i : ℝ))/(∏ i, (jetWeights m V0 P.v r i : ℝ)) =
        (1+3*(sig : ℝ))^(m+2)*((K P A.n : ℝ)*((W0 : ℝ)/V0)^2*(P.v : ℝ)^m) := by
      rw [degreeWeights_prod, jetWeights_prod]
      field_simp
    rw [he]
    exact inflated_volume_lt_one P A.n
  have hbase : 2*(1/eps)*(V0 : ℝ) < W0 := by
    have h := A.base_gap
    change 2*((m : ℝ)+3)/(sig : ℝ)*(V0 : ℝ) < W0 at h
    have he : 2*(1/eps) = 2*((m : ℝ)+3)/(sig : ℝ) := by dsimp [eps]; field_simp
    rw [he]
    exact h
  have hsep : ∀ A B : Finset (Fin (m+2)), A.card = B.card →
      ∀ i, 2 ≤ i.val → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      (A.card : ℝ)^A.card*(1/eps)^A.card*(∏ j ∈ B, (jetWeights m V0 P.v r j : ℝ)) <
        ∏ j ∈ A, (degreeWeights m W0 r j : ℝ) := by
    intro B C hcard i hi hiB hiC habove
    simp_rw [degreeWeights_cast, jetWeights_cast]
    exact fin_products_separated m eps W0 V0 P.v (normalizedWeight r) heps hW0 hV0
      P.v_pos_real hxbase hx hgrowth B C hcard i hi hiB hiC habove
  have hcoord (i : Fin m) :
      (1+(sig : ℝ))*(degreeWeights m W0 r i.succ.succ : ℝ) <
        jetWeights m V0 P.v r i.succ.succ := by
    simp only [degreeWeights_aux, jetWeights_aux, Rat.cast_div, auxWeight_cast]
    apply (lt_div_iff₀ P.v_pos_real).mpr
    have h := mul_lt_mul_of_pos_right A.shrink (hwr i.val)
    nlinarith
  have hden (i : Fin m) : (1+(sig : ℝ))*(W0 : ℝ) < ((r i.val).den : ℝ)*(V0 : ℝ) := by
    have hq : (Q : ℝ) ≤ (r i.val).den := by exact_mod_cast (hr i.val).1
    exact (div_lt_iff₀ hV0).mp (hQ.trans_le hq)
  let d : GeometryData := {
    m := m
    K := K P A.n
    p := fun i => (r i.val).num.natAbs
    q := fun i => (r i.val).den
    q_pos := fun i => (r i.val).pos
    coprime := fun i => (r i.val).reduced.symm
    curveDegreeWeights := degreeWeights m W0 r
    curveJetWeights := jetWeights m V0 P.v r
    curveDegreeWeights_pos := hW
    curveJetWeights_pos := hV
    degree_base_eq := rfl
    jet_base_eq := rfl
    sigma := sig
    sigma_pos := by exact_mod_cast hsig
    curve_volume := hvolume
    base_gap := hbase
    curve_separated_weight_products := hsep
    curve_coordinate_ratio := hcoord
    denominator_ratio := hden }
  have hrepr (i : Fin m) : (d.p i : ℝ)/(d.q i : ℝ) = (r i.val : ℝ) :=
    positive_numerator_representation _ (zero_lt_one.trans (hr i.val).2.1)
  have hlog (i : Fin m) : MatrixArithmetic.logWeights d.q i = weight (r i.val) := rfl
  have hWaux (i : Fin m) : (d.curveDegreeWeights i.succ.succ : ℝ) = MatrixArithmetic.logWeights d.q i := by
    change (auxWeight r i.val : ℝ) = weight (r i.val)
    exact auxWeight_cast r i.val
  have hVaux (i : Fin m) : (d.curveJetWeights i.succ.succ : ℝ) = MatrixArithmetic.logWeights d.q i/(P.v : ℝ) := by
    change ((auxWeight r i.val/P.v : ℚ) : ℝ) = weight (r i.val)/(P.v : ℝ)
    simp only [Rat.cast_div, auxWeight_cast]
  have hnorm (i : Fin m) : ‖d.slopes i‖ ≤ 2 := by
    have he : d.slopes i = ((r i.val : ℝ) : ℂ) := by
      unfold GeometryData.slopes
      have h := congrArg (fun x : ℝ => (x : ℂ)) (hrepr i)
      simpa only [Complex.ofReal_div, Complex.ofReal_natCast] using h
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (zero_lt_one.trans (hr i.val).2.1)]
    exact (hr i.val).2.2.1.le
  have happ (i : Fin m) : |ratioTheta-(d.p i : ℝ)/d.q i| ≤ (d.q i : ℝ)^(-(nu : ℝ)) := by
    rw [hrepr]
    exact (hr i.val).2.2.2.1
  have hsmall : weightError d nu P.v ws < P.gap/8 := by
    unfold weightError
    simp only [hlog]
    exact hmargin (fun i => weight (r i.val)) (fun i => (hr i.val).2.2.2.2.le)
  exact no_data_with_small_weight_error P A hnu d ws rfl rfl rfl rfl hws
    (fun i => (hr i.val).2.2.2.2.le) hWaux hVaux hnorm happ hsmall

#print axioms not_unbounded_exceptional

end LogarithmExtension.LogRatio.AdmissibleData

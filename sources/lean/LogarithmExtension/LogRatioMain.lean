import LogarithmExtension.LogRatioAdmissibleData
import LogarithmExtension.GeneralExponent

/-!
# The upper bound three for log(3)/log(2)

The upper endpoint is derived from the actual two-base determinant and
the constructed exceptional-approximation data. It does not assert equality
with three. The separate lower bound here is Dirichlet's bound of two.
-/

noncomputable section
namespace LogarithmExtension.LogRatio.Main

open Filter OAI.PiExponent CommonTaylor ApproximationSelection AdmissibleData
open scoped Topology

theorem ratioTheta_irrational : Irrational ratioTheta := by
  rintro ⟨r, hr⟩
  have hrpos : (0 : ℝ) < r := by rw [hr]; exact ratioTheta_pos
  have he : (r.num.natAbs : ℝ)/(r.den : ℝ) = ratioTheta :=
    (positive_numerator_representation r hrpos).trans hr
  have hqpos : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  have hmul : ratioTheta*(r.den : ℝ) = (r.num.natAbs : ℝ) :=
    ((div_eq_iff hqpos.ne').mp he).symm
  have hlinear : (r.den : ℝ)*Real.log 3 = (r.num.natAbs : ℝ)*Real.log 2 := by
    calc
      _ = (r.den : ℝ)*(ratioTheta*Real.log 2) := by rw [ratioTheta_mul_log_two]
      _ = (ratioTheta*(r.den : ℝ))*Real.log 2 := by ring
      _ = _ := by rw [hmul]
  have hexp := congrArg Real.exp hlinear
  rw [Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 3),
    Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hexp
  exact CurveRelations.three_pow_ne_two_pow r.num.natAbs r.den r.pos (by exact_mod_cast hexp)

theorem finite_good_approximations (nu : ℝ) (hnu : 3 < nu) :
    (GoodRationalApproximations ratioTheta nu).Finite := by
  obtain ⟨rho, hrho3, hrhonu⟩ := exists_rat_btwn hnu
  have hrho : (3 : ℚ) < rho := by exact_mod_cast hrho3
  have hn := not_unbounded_exceptional rho hrho
  unfold UnboundedExceptional at hn
  push Not at hn
  obtain ⟨Q, hQ⟩ := hn
  apply (finite_rat_den_le_abs_sub_lt_one ratioTheta Q).subset
  intro r hr
  have hbase : (1 : ℝ) ≤ r.den := by exact_mod_cast r.pos
  have hpow : (r.den : ℝ)^(-nu) ≤ (r.den : ℝ)^(-(rho : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
  have hden : r.den ≤ Q := by
    by_contra hh
    have hbound := hQ r (by omega)
    exact (not_lt_of_ge ((hr.2.2.trans_le hpow).le)) hbound
  refine ⟨hden, hr.2.2.trans_le ?_⟩
  exact Real.rpow_le_one_of_one_le_of_nonpos hbase (by linarith)

theorem finite_strict_approximations (nu : ℝ) (hnu : 3 < nu) :
    {r : ℚ | |ratioTheta-(r : ℝ)| < (r.den : ℝ)^(-nu)}.Finite := by
  apply ((finite_good_approximations nu hnu).union
    (finite_rat_den_le_abs_sub_lt_one ratioTheta 1)).subset
  intro r hr
  by_cases hden : 2 ≤ r.den
  · exact Or.inl ⟨hden, abs_pos.mpr (sub_ne_zero.mpr (ratioTheta_irrational.ne_rat r)), hr⟩
  · refine Or.inr ⟨by omega, hr.trans_le ?_⟩
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast r.pos) (by linarith)

/-- Every exponent strictly above three gives an eventual lower bound, with
no coprimality condition on the input numerator and denominator. -/
theorem logRatio_eventual_lower_bound :
    LogarithmExtension.EventualLowerBound (Real.log 3/Real.log 2) 3 := by
  intro nu hnu
  let S : Set ℚ := {r | |ratioTheta-(r : ℝ)| < (r.den : ℝ)^(-nu)}
  have hS : S.Finite := finite_strict_approximations nu hnu
  have ht := (tendsto_rpow_neg_atTop (show 0 < nu by linarith)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hall : ∀ᶠ q : ℕ in atTop, ∀ r ∈ S, (q : ℝ)^(-nu) ≤ |ratioTheta-(r : ℝ)| := by
    apply hS.eventually_all.mpr
    intro r _
    have hp : 0 < |ratioTheta-(r : ℝ)| :=
      abs_pos.mpr (sub_ne_zero.mpr (ratioTheta_irrational.ne_rat r))
    exact (ht.eventually (gt_mem_nhds hp)).mono (fun _ h => h.le)
  obtain ⟨Q, hQ⟩ := eventually_atTop.mp hall
  refine ⟨max 2 Q, le_max_left _ _, ?_⟩
  intro p q hq
  have hqQ : Q ≤ q := (le_max_right _ _).trans hq
  have hqpos : 0 < q := by omega
  let r : ℚ := Rat.divInt p (q : ℤ)
  have hcast : (r : ℝ) = (p : ℝ)/(q : ℝ) := by
    simp only [r, Rat.cast_divInt, Int.cast_natCast]
  have hden : r.den ≤ q := by
    have hd : (r.den : ℤ) ∣ (q : ℤ) := Rat.den_dvd p q
    exact Nat.le_of_dvd hqpos (by exact_mod_cast hd)
  have hpow : (q : ℝ)^(-nu) ≤ (r.den : ℝ)^(-nu) :=
    Real.rpow_le_rpow_of_nonpos (by exact_mod_cast r.pos)
      (by exact_mod_cast hden) (by linarith)
  change (q : ℝ)^(-nu) ≤ |ratioTheta-(p : ℝ)/(q : ℝ)|
  rw [← hcast]
  by_cases hr : r ∈ S
  · exact hQ q hqQ r hr
  · exact hpow.trans (le_of_not_gt hr)

theorem logRatio_irrationalityExponent_le_three :
    OAI.PiExponent.irrationalityExponent (Real.log 3/Real.log 2) ≤ 3 :=
  irrationalityExponent_le_of_eventualLowerBound logRatio_eventual_lower_bound

theorem logRatio_irrationalityExponent_bounds :
    2 ≤ OAI.PiExponent.irrationalityExponent (Real.log 3/Real.log 2) ∧
      OAI.PiExponent.irrationalityExponent (Real.log 3/Real.log 2) ≤ 3 :=
  ⟨two_le_irrationalityExponent_of_eventualLowerBound logRatio_eventual_lower_bound,
    logRatio_irrationalityExponent_le_three⟩

theorem logRatio_approximation_bound (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Q : ℕ, 2 ≤ Q ∧ ∀ p : ℤ, ∀ q : ℕ, Q ≤ q →
      (q : ℝ)^(-(3+epsilon)) ≤ |Real.log 3/Real.log 2-(p : ℝ)/(q : ℝ)| :=
  logRatio_eventual_lower_bound (3+epsilon) (by linarith)

#print axioms logRatio_eventual_lower_bound
#print axioms logRatio_irrationalityExponent_bounds
#print axioms logRatio_approximation_bound

end LogarithmExtension.LogRatio.Main

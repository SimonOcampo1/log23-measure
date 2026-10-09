import LogarithmExtension.LogRatioParameterChoice
import LogarithmExtension.LogRatioDeterminantComparison

/-!
# Exact cancellation in the actual packing density

The product of auxiliary weights cancels against the row density. The
normalization below is the one used by the checked two-variable bound.
-/

noncomputable section
namespace LogarithmExtension.LogRatio.PackingCancellation

open TaylorPacking DeterminantComparison ParameterSeeds ParameterDimension ParameterChoice
open scoped BigOperators

theorem jet_product (d : GeometryData) (v : ℝ)
    (hV : ∀ i : Fin d.m, (d.curveJetWeights i.succ.succ : ℝ) =
      (d.curveDegreeWeights i.succ.succ : ℝ)/v) :
    (∏ i, (d.curveJetWeights i : ℝ)) = (d.curveJetWeights 0 : ℝ)^2 *
      (∏ i : Fin d.m, (d.curveDegreeWeights i.succ.succ : ℝ))/v^d.m := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  change (d.curveJetWeights 0 : ℝ)*((d.curveJetWeights 1 : ℝ)*
    ∏ i : Fin d.m, (d.curveJetWeights i.succ.succ : ℝ)) = _
  rw [d.jet_base_eq]
  simp_rw [hV]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

theorem packingLimit_eq (d : GeometryData) (nu : ℚ) (v lambda : ℝ)
    (hK : 0 < d.K) (hnu : 0 < nu) (hv : 0 < v)
    (hV : ∀ i : Fin d.m, (d.curveJetWeights i.succ.succ : ℝ) =
      (d.curveDegreeWeights i.succ.succ : ℝ)/v) :
    packingLimit d nu lambda =
      16*(d.curveJetWeights 0 : ℝ)^2*lambda^(d.m+3)/
        (((d.m : ℝ)+3)*(d.K : ℝ)*((nu : ℝ)*v)^d.m) := by
  have hKr : (d.K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hnur : (nu : ℝ) ≠ 0 := by exact_mod_cast hnu.ne'
  have hw : (∏ i : Fin d.m, (d.curveDegreeWeights i.succ.succ : ℝ)) ≠ 0 :=
    (Finset.prod_pos (fun i _ => by exact_mod_cast d.curveDegreeWeights_pos i.succ.succ)).ne'
  have hf : ((d.m+2).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos (d.m+2)).ne'
  have hfact : ((d.m+3).factorial : ℝ) = ((d.m : ℝ)+3)*((d.m+2).factorial : ℝ) := by
    rw [show d.m+3 = (d.m+2)+1 by omega, Nat.factorial_succ]
    push_cast
    ring
  unfold packingLimit rowDensity
  rw [jet_product d v hV, hfact, mul_pow]
  field_simp

theorem optimal_packingLimit (d : GeometryData) (nu : ℚ) (v lambda : ℝ)
    (hK : 0 < d.K) (hnu : 0 < nu) (hv : 0 < v)
    (hV : ∀ i : Fin d.m, (d.curveJetWeights i.succ.succ : ℝ) =
      (d.curveDegreeWeights i.succ.succ : ℝ)/v)
    (hroot : lambda^(d.m+2) = (d.K : ℝ)*((nu : ℝ)*v)^d.m/
      (16*(d.curveJetWeights 0 : ℝ)^2)) :
    packingLimit d nu lambda = lambda/((d.m : ℝ)+3) := by
  have hKr : (d.K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hnur : (nu : ℝ) ≠ 0 := by exact_mod_cast hnu.ne'
  have hbase : (d.curveJetWeights 0 : ℝ) ≠ 0 :=
    (show (0 : ℝ) < d.curveJetWeights 0 by exact_mod_cast d.curveJetWeights_pos 0).ne'
  rw [packingLimit_eq d nu v lambda hK hnu hv hV,
    show d.m+3 = (d.m+2)+1 by omega, pow_succ lambda (d.m+2), hroot]
  field_simp

variable {nu : ℚ} (P : SeedData nu)

theorem chosen_root_identity (hnu : 0 < nu) (n : ℕ) :
    (lambda P n)^(2*n+2) = (K P n : ℝ)*((nu : ℝ)*P.v)^(2*n)/
      (16*(v0 P n : ℝ)^2) := by
  rw [lambda_power P hnu n]
  have hJ := (J_pos P n).ne'
  have hB := P.B_pos_real.ne'
  have hv := P.v_pos_real.ne'
  simp only [target, K, v0, w0, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast,
    Rat.cast_pow, Rat.cast_inv, Nat.cast_pow, mul_pow, pow_mul']
  field_simp
  ring

#print axioms packingLimit_eq
#print axioms optimal_packingLimit
#print axioms chosen_root_identity

end LogarithmExtension.LogRatio.PackingCancellation

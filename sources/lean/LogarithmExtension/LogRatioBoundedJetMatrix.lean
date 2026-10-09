import LogarithmExtension.LogRatioWeightedInterpolation
import LogarithmExtension.LogRatioTruncation
import OAI.NumberTheory.PiExponent.Jets.FormalJetIndices

/-! # Full row rank and a nonzero minor of the bounded two-base jet matrix -/

noncomputable section
namespace LogarithmExtension.LogRatio.BoundedJetMatrix

open OAI OAI.PiExponent OAI.PiExponentApprox
open FormalMatrixBridge InterpolationMatrix
open Truncation BlowupGeometry
open scoped BigOperators

variable (d : GeometryData)

abbrev Row (H : ℚ) :=
  Fin d.K × ↥(strictWeightedSimplex (fun i => (d.curveJetWeights i : ℝ)) (H : ℝ))

abbrev Column (H : ℚ) :=
  ↥(realWeightedSimplex (fun i => (d.curveDegreeWeights i : ℝ)) (H : ℝ))

def jet (T : Fin d.m → ℕ) (j : Fin d.K) :
    PolynomialFrame.Poly d.m →ₐ[ℂ] MvPowerSeries (Fin (d.m+2)) ℂ :=
  AlgebraicJet.truncatedJet (d.centerY j) (d.centerZ j) (d.curveCenters j) d.slopes
    (CompactJetPolynomial.logPolynomials T)

def matrix (T : Fin d.m → ℕ) (H : ℚ) : Matrix (Row d H) (Column d H) ℂ :=
  fun row col => MvPowerSeries.coeff (exponentVector row.2.val)
    (jet d T row.1
      (MvPolynomial.monomial (exponentVector col.val) 1))

theorem mulVec_eq_coeff (T : Fin d.m → ℕ) (H : ℚ) (x : Column d H → ℂ)
    (row : Row d H) :
    (matrix d T H).mulVecLin x row =
      MvPowerSeries.coeff (exponentVector row.2.val)
        (jet d T row.1
          (polynomialOfCoefficients
            (realWeightedSimplex (fun i => (d.curveDegreeWeights i : ℝ)) (H : ℝ)) x)) := by
  classical
  change (∑ col, matrix d T H row col * x col) =
    MvPowerSeries.coeff _ (jet d T row.1
      (∑ col : Column d H, MvPolynomial.monomial (exponentVector col.val) (x col)))
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro col _
  have hm : MvPolynomial.monomial (exponentVector col.val) (x col) =
      x col • (MvPolynomial.monomial (exponentVector col.val) (1 : ℂ)) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hm, map_smul, map_smul]
  exact mul_comm _ _

theorem surjective_of_packets {α : Type*} (T : Fin d.m → ℕ) (H : ℚ)
    (P : α → PolynomialFrame.Poly d.m)
    (hdegree : ∀ a, HasWeightedDegreeLE (fun i => (d.curveDegreeWeights i : ℝ)) (H : ℝ) (P a))
    (hpacket : Function.Surjective (fun a => fun j : Fin d.K =>
      JetGeometry.rationalCoefficientPacket d.curveJetWeights H
        (jet d T j (P a)))) :
    Function.Surjective (matrix d T H).mulVecLin := by
  classical
  intro target
  let idx := rationalJetIndexEquiv d.curveJetWeights d.curveJetWeights_pos H
  let packets : Fin d.K → JetGeometry.RationalCoefficientPacket (R := ℂ) d.curveJetWeights H :=
    fun j a => target (j, idx a)
  obtain ⟨a, ha⟩ := hpacket packets
  let x : Column d H → ℂ := fun col => (P a).coeff (exponentVector col.val)
  refine ⟨x, ?_⟩
  funext row
  rw [mulVec_eq_coeff]
  change MvPowerSeries.coeff (exponentVector row.2.val)
    (jet d T row.1
      (polynomialOfCoefficients _ (fun col => (P a).coeff (exponentVector col.val)))) = target row
  rw [polynomialOfCoefficients_of_weighted _
    (fun i => by exact_mod_cast d.curveDegreeWeights_pos i) _ (P a) (hdegree a)]
  have hh := congrFun (congrFun ha row.1) (idx.symm row.2)
  change MvPowerSeries.coeff (idx.symm row.2).val
    (jet d T row.1 (P a)) =
      packets row.1 (idx.symm row.2) at hh
  simpa only [idx, rationalJetIndexEquiv_symm_val, packets, Equiv.apply_symm_apply] using hh

theorem eventually_surjective (T : Fin d.m → ℕ)
    (hT0 : ∀ i, d.curveJetWeights i.succ.succ ≤ (T i : ℚ) * d.curveJetWeights 0)
    (hT1 : ∀ i, d.curveJetWeights i.succ.succ ≤ (T i : ℚ) * d.curveJetWeights 1) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Function.Surjective (matrix d T ((n : ℚ) * (scale d).radius)).mulVecLin := by
  filter_upwards [WeightedInterpolation.eventually_packetMap_surjective d] with n hn
  apply surjective_of_packets d T ((n : ℚ) * (scale d).radius)
    (fun P : WeightedInterpolation.WeightedPolynomials d n => P.val)
  · intro P a ha
    have h := P.property a ha
    simpa only [HasWeightedDegreeLE, monomialWeight, Finsupp.weight_eq_sum,
      nsmul_eq_mul, Rat.cast_mul, Rat.cast_natCast] using h
  · exact (packets_surjective_iff_truncated d.curveJetWeights
      (fun i => (d.curveJetWeights_pos i).le) ((n : ℚ) * (scale d).radius) d.slopes T hT0 hT1
      d.centerY d.centerZ d.curveCenters
      (fun P : WeightedInterpolation.WeightedPolynomials d n => P.val)).mp hn

theorem eventually_nonzero_minor (T : Fin d.m → ℕ)
    (hT0 : ∀ i, d.curveJetWeights i.succ.succ ≤ (T i : ℚ) * d.curveJetWeights 0)
    (hT1 : ∀ i, d.curveJetWeights i.succ.succ ≤ (T i : ℚ) * d.curveJetWeights 1) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∃ selection : Row d ((n : ℚ) * (scale d).radius) → Column d ((n : ℚ) * (scale d).radius),
        Function.Injective selection ∧
          ((matrix d T ((n : ℚ) * (scale d).radius)).submatrix id selection).det ≠ 0 := by
  classical
  filter_upwards [eventually_surjective d T hT0 hT1] with n hn
  exact InterpolationMatrix.exists_full_row_minor_of_surjective _ hn

#print axioms eventually_surjective
#print axioms eventually_nonzero_minor

end LogarithmExtension.LogRatio.BoundedJetMatrix

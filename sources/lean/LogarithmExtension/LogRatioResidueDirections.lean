import LogarithmExtension.LogRatioPolynomialFrame

/-! The actual two-base polynomial operators induce precisely the previously
defined frame vectors after passage to any residue field. -/

noncomputable section
namespace LogarithmExtension.LogRatio.ResidueDirections

open MvPolynomial PolynomialFrame TwoBaseFrame
open scoped BigOperators

theorem frame_eq_basis_dot {E : Type*} [Field E]
    (m : ℕ) (r : Fin m → ℂ) (φ : Poly m →+* E)
    (hy : φ (X 0) ≠ 0) (hz : φ (X 1) ≠ 0)
    (j : Fin (m + 2)) (P : Poly m) :
    φ (frame m r j P) =
      ∑ i, frameBasis m (φ (X 0)) (φ (X 1)) hy hz
        (fun k => φ (C (r k))) j i * φ (pderiv i P) := by
  refine Fin.cases ?_ (fun k => ?_) j
  · change φ (dY m r P) = _
    rw [dY_apply, map_sub, map_mul, map_sum, Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [frameBasis_zero_zero, Fin.succ_zero_eq_one, frameBasis_zero_one,
      zero_mul, frameBasis_zero_aux, neg_mul, Finset.sum_neg_distrib, zero_add]
    rw [sub_eq_add_neg]
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    simp only [Algebra.smul_def, map_mul]
    rfl
  · refine Fin.cases ?_ (fun i => ?_) k
    · change φ (dZ m P) = _
      rw [dZ_apply, map_add, map_mul, map_sum, Fin.sum_univ_succ, Fin.sum_univ_succ]
      simp only [Fin.succ_zero_eq_one, frameBasis_one_zero, frameBasis_one_one,
        frameBasis_one_aux, zero_mul, zero_add, one_mul]
    · change φ (pderiv i.succ.succ P) = _
      rw [frameBasis_aux]
      simp [Pi.basisFun_apply, Pi.single_apply]

#print axioms frame_eq_basis_dot

end LogarithmExtension.LogRatio.ResidueDirections

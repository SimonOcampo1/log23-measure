import LogarithmExtension.LogRatioAlgebraicJet
import OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation

/-!
# Fixed truncations preserve two-base weighted interpolation

The two logarithmic tails define one triangular formal automorphism fixing
both base variables. It and its inverse preserve every weighted packet as
soon as each tail starts above its auxiliary-coordinate weight. The cutoff
does not grow with the packet radius or the polynomial degree.

The substitution and filtered-packet arguments adapt the pinned OpenAI
`FormalLogTruncation` proof (Apache-2.0).
-/

noncomputable section
namespace LogarithmExtension.LogRatio.Truncation

open OAI OAI.PiExponent MvPowerSeries
open PolynomialFrame AlgebraicJet JetGeometry

variable {m : ℕ}

def tail (r : Fin m → ℂ) (T : Fin m → ℕ) (i : Fin m) : MvPowerSeries (Fin (m+2)) ℂ :=
  (FormalLogTruncation.logTail (T i)).toMvPowerSeries 1 -
    C (r i) * (FormalLogTruncation.logTail (T i)).toMvPowerSeries 0

theorem tail_constantCoeff (r : Fin m → ℂ) (T : Fin m → ℕ) (i : Fin m) :
    constantCoeff (tail r T i) = 0 := by
  simp only [tail, map_sub, map_mul, constantCoeff_C,
    PowerSeries.toMvPowerSeries_apply, constantCoeff_rename]
  change PowerSeries.constantCoeff (FormalLogTruncation.logTail (T i)) -
    r i * PowerSeries.constantCoeff (FormalLogTruncation.logTail (T i)) = 0
  rw [FormalLogTruncation.logTail_constantCoeff, mul_zero, sub_self]

def shiftVars (r : Fin m → ℂ) (T : Fin m → ℕ) (a : ℂ) :
    Fin (m+2) → MvPowerSeries (Fin (m+2)) ℂ :=
  Fin.cases (X 0) (Fin.cases (X 1) (fun i => X i.succ.succ + C a * tail r T i))

theorem shiftVars_hasSubst (r : Fin m → ℂ) (T : Fin m → ℕ) (a : ℂ) :
    HasSubst (shiftVars r T a) := by
  apply hasSubst_of_constantCoeff_zero
  intro i
  cases i using Fin.cases with
  | zero => simp [shiftVars]
  | succ j =>
    cases j using Fin.cases with
    | zero => simp [shiftVars]
    | succ i => simp [shiftVars, tail_constantCoeff]

def shiftMap (r : Fin m → ℂ) (T : Fin m → ℕ) (a : ℂ) :
    MvPowerSeries (Fin (m+2)) ℂ →ₐ[ℂ] MvPowerSeries (Fin (m+2)) ℂ :=
  substAlgHom (shiftVars_hasSubst r T a)

@[simp] theorem shiftMap_apply (r : Fin m → ℂ) (T : Fin m → ℕ) (a : ℂ) (f) :
    shiftMap r T a f = subst (shiftVars r T a) f := substAlgHom_apply _ _

@[simp] theorem shiftMap_C (r : Fin m → ℂ) (T : Fin m → ℕ) (a c : ℂ) :
    shiftMap r T a (C c) = C c := (shiftMap r T a).commutes c

@[simp] theorem shiftMap_X_zero (r : Fin m → ℂ) (T : Fin m → ℕ) (a : ℂ) :
    shiftMap r T a (X 0) = X 0 := by rw [shiftMap, substAlgHom_X]; rfl

@[simp] theorem shiftMap_X_one (r : Fin m → ℂ) (T : Fin m → ℕ) (a : ℂ) :
    shiftMap r T a (X 1) = X 1 := by rw [shiftMap, substAlgHom_X]; rfl

@[simp] theorem shiftMap_X_aux (r : Fin m → ℂ) (T : Fin m → ℕ) (a : ℂ) (i : Fin m) :
    shiftMap r T a (X i.succ.succ) = X i.succ.succ + C a * tail r T i := by
  rw [shiftMap, substAlgHom_X]
  rfl

theorem shiftMap_toMvPowerSeries (r : Fin m → ℂ) (T : Fin m → ℕ) (a : ℂ)
    (b : Fin (m+2)) (hb : b = 0 ∨ b = 1) (f : PowerSeries ℂ) :
    shiftMap r T a (f.toMvPowerSeries b) = f.toMvPowerSeries b := by
  rw [shiftMap, substAlgHom_apply, PowerSeries.subst_toMvPowerSeries (shiftVars_hasSubst r T a)]
  have hbase : shiftVars r T a b = X b := by
    rcases hb with rfl | rfl <;> rfl
  rw [hbase]
  exact PowerSeries.toMvPowerSeries_eq_subst.symm

@[simp] theorem shiftMap_tail (r : Fin m → ℂ) (T : Fin m → ℕ) (a : ℂ) (i : Fin m) :
    shiftMap r T a (tail r T i) = tail r T i := by
  rw [tail, map_sub, map_mul, shiftMap_C,
    shiftMap_toMvPowerSeries r T a 1 (Or.inr rfl),
    shiftMap_toMvPowerSeries r T a 0 (Or.inl rfl)]

theorem shiftMap_inverse (r : Fin m → ℂ) (T : Fin m → ℕ) (a b : ℂ)
    (hab : a+b = 0) (f : MvPowerSeries (Fin (m+2)) ℂ) :
    shiftMap r T a (shiftMap r T b f) = f := by
  simp only [shiftMap_apply]
  rw [subst_comp_subst_apply (shiftVars_hasSubst r T b) (shiftVars_hasSubst r T a)]
  have hvars : (fun i => subst (shiftVars r T a) (shiftVars r T b i)) = X := by
    funext i
    rw [← shiftMap_apply]
    cases i using Fin.cases with
    | zero => exact shiftMap_X_zero r T a
    | succ j =>
      cases j using Fin.cases with
      | zero => exact shiftMap_X_one r T a
      | succ i =>
        change shiftMap r T a (X i.succ.succ + C b * tail r T i) = X i.succ.succ
        rw [map_add, map_mul, shiftMap_X_aux, shiftMap_C, shiftMap_tail]
        calc
          _ = X i.succ.succ + C (a+b) * tail r T i := by rw [map_add]; ring
          _ = _ := by rw [hab, map_zero, zero_mul, add_zero]
  rw [hvars]
  exact congrFun subst_self f

def shiftEquiv (r : Fin m → ℂ) (T : Fin m → ℕ) :
    MvPowerSeries (Fin (m+2)) ℂ ≃ₐ[ℂ] MvPowerSeries (Fin (m+2)) ℂ := by
  refine AlgEquiv.ofAlgHom (shiftMap r T 1) (shiftMap r T (-1)) ?_ ?_
  · apply AlgHom.ext
    intro f
    exact shiftMap_inverse r T 1 (-1) (by ring) f
  · apply AlgHom.ext
    intro f
    exact shiftMap_inverse r T (-1) 1 (by ring) f

@[simp] theorem shiftEquiv_apply (r : Fin m → ℂ) (T : Fin m → ℕ) (f) :
    shiftEquiv r T f = shiftMap r T 1 f := rfl

@[simp] theorem shiftEquiv_symm_apply (r : Fin m → ℂ) (T : Fin m → ℕ) (f) :
    (shiftEquiv r T).symm f = shiftMap r T (-1) f := rfl

theorem tail_mem (r : Fin m → ℂ) (T : Fin m → ℕ)
    (v : Fin (m+2) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (hT0 : ∀ i, v i.succ.succ ≤ (T i : ℚ) * v 0)
    (hT1 : ∀ i, v i.succ.succ ≤ (T i : ℚ) * v 1) (i : Fin m) :
    tail r T i ∈ rationalWeightedIdeal v hv (v i.succ.succ) :=
  Ideal.sub_mem _ (logTail_mem 1 v hv (T i) _ (hT1 i))
    (Ideal.mul_mem_left _ _ (logTail_mem 0 v hv (T i) _ (hT0 i)))

theorem shiftMap_mem (r : Fin m → ℂ) (T : Fin m → ℕ) (a : ℂ)
    (v : Fin (m+2) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (hT0 : ∀ i, v i.succ.succ ≤ (T i : ℚ) * v 0)
    (hT1 : ∀ i, v i.succ.succ ≤ (T i : ℚ) * v 1)
    (H : ℚ) (f : MvPowerSeries (Fin (m+2)) ℂ) (hf : f ∈ rationalWeightedIdeal v hv H) :
    shiftMap r T a f ∈ rationalWeightedIdeal v hv H := by
  rw [shiftMap_apply]
  apply FormalLogTruncation.subst_mem_rationalWeightedIdeal v v hv hv _
    (shiftVars_hasSubst r T a) _ H f hf
  intro i
  cases i using Fin.cases with
  | zero => exact FormalLogTruncation.X_mem_rationalWeightedIdeal v hv 0
  | succ j =>
    cases j using Fin.cases with
    | zero => exact FormalLogTruncation.X_mem_rationalWeightedIdeal v hv 1
    | succ i =>
      exact Ideal.add_mem _ (FormalLogTruncation.X_mem_rationalWeightedIdeal v hv i.succ.succ)
        (Ideal.mul_mem_left _ _ (tail_mem r T v hv hT0 hT1 i))

theorem shiftMap_truncatedJet (cy cz : ℂ) (c r : Fin m → ℂ) (T : Fin m → ℕ)
    (P : Poly m) :
    shiftMap r T 1 (truncatedJet cy cz c r (CompactJetPolynomial.logPolynomials T) P) =
      FormalJet.formalJet cy cz c r P := by
  have he : (shiftMap r T 1).comp
      (truncatedJet cy cz c r (CompactJetPolynomial.logPolynomials T)) =
        FormalJet.formalJet cy cz c r := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i using Fin.cases with
    | zero => simp only [AlgHom.comp_apply, truncatedJet_Y, FormalJet.formalJet_Y,
        map_mul, map_add, map_one, shiftMap_C, shiftMap_X_zero]
    | succ j =>
      cases j using Fin.cases with
      | zero => simp only [Fin.succ_zero_eq_one, AlgHom.comp_apply, truncatedJet_Z,
          FormalJet.formalJet_Z, map_mul, map_add, map_one, shiftMap_C, shiftMap_X_one]
      | succ i =>
        simp only [AlgHom.comp_apply, truncatedJet_aux, FormalJet.formalJet_aux,
          map_add, map_sub, map_mul, shiftMap_C, shiftMap_X_aux, map_one, one_mul,
          ← Polynomial.aeval_algHom_apply, shiftMap_X_zero, shiftMap_X_one]
        simp only [tail, FormalLogTruncation.logTail, map_sub, polynomial_toMvPowerSeries,
          CompactJetPolynomial.logPolynomials, FormalJet.logAt]
        ring
  exact AlgHom.congr_fun he P

/-- The same source family has full row rank before and after a FIXED
two-base logarithmic truncation. This does not change its degree bound. -/
theorem packets_surjective_iff_truncated {α J : Type*}
    (v : Fin (m+2) → ℚ) (hv : ∀ i, 0 ≤ v i) (H : ℚ)
    (r : Fin m → ℂ) (T : Fin m → ℕ)
    (hT0 : ∀ i, v i.succ.succ ≤ (T i : ℚ) * v 0)
    (hT1 : ∀ i, v i.succ.succ ≤ (T i : ℚ) * v 1)
    (cy cz : J → ℂ) (c : J → Fin m → ℂ) (P : α → Poly m) :
    Function.Surjective (fun a j => rationalCoefficientPacket v H
      (FormalJet.formalJet (cy j) (cz j) (c j) r (P a))) ↔
    Function.Surjective (fun a j => rationalCoefficientPacket v H
      (truncatedJet (cy j) (cz j) (c j) r (CompactJetPolynomial.logPolynomials T) (P a))) := by
  let e := shiftEquiv r T
  have he : ∀ F ∈ rationalWeightedIdeal v hv H, e F ∈ rationalWeightedIdeal v hv H :=
    fun F hF => shiftMap_mem r T 1 v hv hT0 hT1 H F hF
  have hi : ∀ F ∈ rationalWeightedIdeal v hv H, e.symm F ∈ rationalWeightedIdeal v hv H :=
    fun F hF => shiftMap_mem r T (-1) v hv hT0 hT1 H F hF
  have hh := FormalLogTruncation.packets_surjective_comp_equiv_iff v hv H e he hi
    (fun a j => truncatedJet (cy j) (cz j) (c j) r (CompactJetPolynomial.logPolynomials T) (P a))
  simpa only [e, shiftEquiv_apply, shiftMap_truncatedJet] using hh

#print axioms shiftEquiv
#print axioms packets_surjective_iff_truncated

end LogarithmExtension.LogRatio.Truncation

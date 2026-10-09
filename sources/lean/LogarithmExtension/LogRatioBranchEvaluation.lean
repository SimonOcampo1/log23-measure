import LogarithmExtension.LogRatioFormalJet
import OAI.NumberTheory.PiExponent.Jets.BranchContact

/-! The formal jet has an actual inverse on centered power-series branches.
The resulting weighted order bound applies to every word in the two-base
polynomial derivatives. -/

noncomputable section
namespace LogarithmExtension.LogRatio.BranchEvaluation

open OAI.PiExponent MvPowerSeries PolynomialFrame FormalJet

def normalizedDifference (c : ℂ) (y : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.C c⁻¹ * y - 1

theorem recover_coordinate (c : ℂ) (hc : c ≠ 0) (y : PowerSeries ℂ) :
    PowerSeries.C c * (1 + normalizedDifference c y) = y := by
  have he : 1 + normalizedDifference c y = PowerSeries.C c⁻¹ * y := by
    unfold normalizedDifference
    ring
  rw [he, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, one_mul]

theorem normalizedDifference_const (c : ℂ) (hc : c ≠ 0) (y : PowerSeries ℂ)
    (hy : PowerSeries.constantCoeff y = c) :
    PowerSeries.constantCoeff (normalizedDifference c y) = 0 := by
  simp [normalizedDifference, hy, hc]

def coordinates {m : ℕ} (cy cz : ℂ) (c r : Fin m → ℂ)
    (y z : PowerSeries ℂ) (x : Fin m → PowerSeries ℂ) : Fin (m+2) → PowerSeries ℂ :=
  Fin.cases (normalizedDifference cy y) (Fin.cases (normalizedDifference cz z)
    (fun i => x i - PowerSeries.C (c i) -
      PowerSeries.subst (normalizedDifference cz z) (PowerSeries.log ℂ) +
      PowerSeries.C (r i) * PowerSeries.subst (normalizedDifference cy y) (PowerSeries.log ℂ)))

theorem coordinates_centered {m : ℕ} (cy cz : ℂ) (hcy : cy ≠ 0) (hcz : cz ≠ 0)
    (c r : Fin m → ℂ) (y z : PowerSeries ℂ) (x : Fin m → PowerSeries ℂ)
    (hy : PowerSeries.constantCoeff y = cy) (hz : PowerSeries.constantCoeff z = cz)
    (hx : ∀ i, PowerSeries.constantCoeff (x i) = c i) :
    ∀ i, PowerSeries.constantCoeff (coordinates cy cz c r y z x i) = 0 := by
  have ht := normalizedDifference_const cy hcy y hy
  have hs := normalizedDifference_const cz hcz z hz
  have hlt : PowerSeries.constantCoeff
      (PowerSeries.subst (normalizedDifference cy y) (PowerSeries.log ℂ)) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero ht _ PowerSeries.constantCoeff_log
  have hls : PowerSeries.constantCoeff
      (PowerSeries.subst (normalizedDifference cz z) (PowerSeries.log ℂ)) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hs _ PowerSeries.constantCoeff_log
  intro i
  refine Fin.cases ht (fun j => ?_) i
  refine Fin.cases hs (fun k => ?_) j
  simp only [coordinates, Fin.cases_succ, map_add, map_sub, map_mul,
    PowerSeries.constantCoeff_C, hx, hlt, hls, sub_self, mul_zero, add_zero]

theorem coordinates_hasSubst {m : ℕ} (cy cz : ℂ) (hcy : cy ≠ 0) (hcz : cz ≠ 0)
    (c r : Fin m → ℂ) (y z : PowerSeries ℂ) (x : Fin m → PowerSeries ℂ)
    (hy : PowerSeries.constantCoeff y = cy) (hz : PowerSeries.constantCoeff z = cz)
    (hx : ∀ i, PowerSeries.constantCoeff (x i) = c i) :
    HasSubst (coordinates cy cz c r y z x) :=
  hasSubst_of_constantCoeff_zero (coordinates_centered cy cz hcy hcz c r y z x hy hz hx)

theorem formalJet_subst {m : ℕ} (cy cz : ℂ) (hcy : cy ≠ 0) (hcz : cz ≠ 0)
    (c r : Fin m → ℂ) (y z : PowerSeries ℂ) (x : Fin m → PowerSeries ℂ)
    (hy : PowerSeries.constantCoeff y = cy) (hz : PowerSeries.constantCoeff z = cz)
    (hx : ∀ i, PowerSeries.constantCoeff (x i) = c i) (P : Poly m) :
    subst (coordinates cy cz c r y z x) (formalJet cy cz c r P) =
      MvPolynomial.aeval (Fin.cases y (Fin.cases z x)) P := by
  let ha := coordinates_hasSubst cy cz hcy hcz c r y z x hy hz hx
  have hlog (i : Fin (m+2)) : substAlgHom ha (logAt i) =
      PowerSeries.subst (coordinates cy cz c r y z x i) (PowerSeries.log ℂ) := by
    rw [substAlgHom_apply, logAt, PowerSeries.subst_toMvPowerSeries ha]
  have hC (a : ℂ) : substAlgHom ha (C a) = PowerSeries.C a := by
    rw [substAlgHom_apply, subst_C]
    rfl
  have he : (substAlgHom ha).comp (formalJet cy cz c r) =
      MvPolynomial.aeval (Fin.cases y (Fin.cases z x)) := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [AlgHom.comp_apply, formalJet_Y, map_mul, map_add, map_one,
        substAlgHom_X, MvPolynomial.aeval_X, Fin.cases_zero, hC]
      exact recover_coordinate cy hcy y
    · refine Fin.cases ?_ (fun k => ?_) j
      · simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, Fin.cases_succ, Fin.cases_zero]
        rw [Fin.succ_zero_eq_one, formalJet_Z, map_mul, map_add, map_one, substAlgHom_X, hC]
        change PowerSeries.C cz * (1 + normalizedDifference cz z) = z
        exact recover_coordinate cz hcz z
      · simp only [AlgHom.comp_apply, formalJet_aux, map_sub, map_add, map_mul,
          substAlgHom_X, hlog, hC, MvPolynomial.aeval_X, Fin.cases_succ]
        change PowerSeries.C (c k) +
          (x k - PowerSeries.C (c k) -
            PowerSeries.subst (normalizedDifference cz z) (PowerSeries.log ℂ) +
            PowerSeries.C (r k) * PowerSeries.subst (normalizedDifference cy y) (PowerSeries.log ℂ)) +
          PowerSeries.subst (normalizedDifference cz z) (PowerSeries.log ℂ) -
          PowerSeries.C (r k) * PowerSeries.subst (normalizedDifference cy y) (PowerSeries.log ℂ) = x k
        ring
  simpa only [AlgHom.comp_apply, substAlgHom_apply] using AlgHom.congr_fun he P

theorem coordinates_nonzero {m : ℕ} (cy cz : ℂ) (hcy : cy ≠ 0) (hcz : cz ≠ 0)
    (c r : Fin m → ℂ) (y z : PowerSeries ℂ) (x : Fin m → PowerSeries ℂ)
    (hnc : y ≠ PowerSeries.C cy ∨ z ≠ PowerSeries.C cz ∨ ∃ i, x i ≠ PowerSeries.C (c i)) :
    ∃ i, coordinates cy cz c r y z x i ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  have ht : normalizedDifference cy y = 0 := hn 0
  have hs : normalizedDifference cz z = 0 := hn 1
  have hy : y = PowerSeries.C cy := by
    have h := recover_coordinate cy hcy y
    simpa only [ht, add_zero, mul_one] using h.symm
  have hz : z = PowerSeries.C cz := by
    have h := recover_coordinate cz hcz z
    simpa only [hs, add_zero, mul_one] using h.symm
  rcases hnc with hnc | hnc | ⟨i, hi⟩
  · exact hnc hy
  · exact hnc hz
  · apply hi
    have hh := hn i.succ.succ
    change x i - PowerSeries.C (c i) -
      PowerSeries.subst (normalizedDifference cz z) (PowerSeries.log ℂ) +
      PowerSeries.C (r i) * PowerSeries.subst (normalizedDifference cy y) (PowerSeries.log ℂ) = 0 at hh
    simpa only [ht, hs, PowerSeries.subst_zero_of_constantCoeff_zero PowerSeries.constantCoeff_log,
      sub_zero, mul_zero, add_zero, sub_eq_zero] using hh

theorem word_order_lower {m : ℕ} (cy cz : ℂ) (hcy : cy ≠ 0) (hcz : cz ≠ 0)
    (c r : Fin m → ℂ) (y z : PowerSeries ℂ) (x : Fin m → PowerSeries ℂ)
    (hy : PowerSeries.constantCoeff y = cy) (hz : PowerSeries.constantCoeff z = cz)
    (hx : ∀ i, PowerSeries.constantCoeff (x i) = c i)
    (v : Fin (m+2) → ℚ) (hv : ∀ i, 0 ≤ v i) (mu H : ℚ) (hmu : 0 ≤ mu)
    (P : Poly m) (hP : formalJet cy cz c r P ∈ JetGeometry.rationalWeightedIdeal v hv H)
    (hcontact : ∀ i (k : ℕ), (coordinates cy cz c r y z x i).order = (k : ℕ∞) →
      mu * v i ≤ (k : ℚ)) (indices : List (Fin (m+2))) :
    (⌈mu * (H - (indices.map v).sum)⌉₊ : ℕ∞) ≤
      PowerSeries.order (MvPolynomial.aeval (Fin.cases y (Fin.cases z x)) (word m r indices P)) := by
  have h := FormalBranchOrder.rational_powerSeries_order_subst_of_mem_weightedIdeal
    v hv mu (H - (indices.map v).sum) hmu
    (formalJet cy cz c r (word m r indices P)) (coordinates cy cz c r y z x)
    (coordinates_hasSubst cy cz hcy hcz c r y z x hy hz hx)
    (formalJet_word_vanishing cy cz c r v hv H P hP indices) hcontact
  rwa [formalJet_subst cy cz hcy hcz c r y z x hy hz hx] at h

theorem word_order_toNat_lower {m : ℕ} (cy cz : ℂ) (hcy : cy ≠ 0) (hcz : cz ≠ 0)
    (c r : Fin m → ℂ) (y z : PowerSeries ℂ) (x : Fin m → PowerSeries ℂ)
    (hy : PowerSeries.constantCoeff y = cy) (hz : PowerSeries.constantCoeff z = cz)
    (hx : ∀ i, PowerSeries.constantCoeff (x i) = c i)
    (v : Fin (m+2) → ℚ) (hv : ∀ i, 0 ≤ v i) (mu H : ℚ) (hmu : 0 ≤ mu)
    (P : Poly m) (hP : formalJet cy cz c r P ∈ JetGeometry.rationalWeightedIdeal v hv H)
    (hcontact : ∀ i (k : ℕ), (coordinates cy cz c r y z x i).order = (k : ℕ∞) →
      mu * v i ≤ (k : ℚ)) (indices : List (Fin (m+2)))
    (hne : MvPolynomial.aeval (Fin.cases y (Fin.cases z x)) (word m r indices P) ≠ 0) :
    mu * (H - (indices.map v).sum) ≤
      ((PowerSeries.order (MvPolynomial.aeval (Fin.cases y (Fin.cases z x))
        (word m r indices P))).toNat : ℚ) := by
  have h := word_order_lower cy cz hcy hcz c r y z x hy hz hx v hv mu H hmu P hP hcontact indices
  have hh := ENat.toNat_le_toNat h (PowerSeries.order_eq_top.not.mpr hne)
  exact Nat.ceil_le.mp (by simpa using hh)

#print axioms formalJet_subst
#print axioms word_order_toNat_lower

end LogarithmExtension.LogRatio.BranchEvaluation

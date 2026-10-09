import LogarithmExtension.LogRatioPolynomialFrame
import OAI.NumberTheory.PiExponent.Jets.FormalAuxiliaryJet
import OAI.NumberTheory.PiExponent.Jets.FormalBranchEvaluation

/-!
# The actual two-base logarithmic formal jet

Y = cy (1+t), Z = cz (1+s),
Xi = ci + ui + log(1+s) - ri log(1+t).

This file proves the derivative identities and weighted losses for that
substitution. They are not hypotheses imported from the one-base argument.
-/

noncomputable section
namespace LogarithmExtension.LogRatio.FormalJet

open MvPowerSeries OAI OAI.PiExponent OAI.PiExponentApprox
open PolynomialFrame
open Filter Topology
open scoped BigOperators

section OneVariable

variable {R σ : Type*} [CommRing R]

theorem coeff_toMvPowerSeries [DecidableEq σ] (i : σ) (f : PowerSeries R) (d : σ →₀ ℕ) :
    coeff d (f.toMvPowerSeries i) =
      if d = Finsupp.single i (d i) then PowerSeries.coeff (d i) f else 0 := by
  classical
  let e : Unit ↪ σ := ⟨fun _ => i, fun a b _ => Subsingleton.elim a b⟩
  change coeff d (rename e f) = _
  by_cases hd : d = Finsupp.single i (d i)
  · rw [ite_eq_left hd]
    have he : Finsupp.embDomain e (Finsupp.single () (d i)) =
        Finsupp.single i (d i) := by rw [Finsupp.embDomain_single]; rfl
    conv_lhs => rw [hd, ← he, coeff_embDomain_rename]
    rfl
  · rw [ite_eq_right hd]
    apply coeff_rename_eq_zero
    rintro ⟨x, hx⟩
    have hx' : x = Finsupp.single () (x ()) := by ext; simp
    rw [hx', Finsupp.mapDomain_single] at hx
    apply hd
    rw [← hx]
    change Finsupp.single i (x ()) =
      Finsupp.single i ((Finsupp.single i (x ()) : σ →₀ ℕ) i)
    simp

theorem pderiv_toMvPowerSeries_self (i : σ) (f : PowerSeries R) :
    pderiv i (f.toMvPowerSeries i) = (PowerSeries.derivative f).toMvPowerSeries i := by
  classical
  ext d
  rw [coeff_pderiv, coeff_toMvPowerSeries, coeff_toMvPowerSeries]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same]
  have he : d + Finsupp.single i 1 = Finsupp.single i (d i + 1) ↔
      d = Finsupp.single i (d i) := by
    constructor
    · intro h
      apply add_right_cancel (b := Finsupp.single i 1)
      simpa only [Finsupp.single_add] using h
    · intro h
      calc
        d + Finsupp.single i 1 = Finsupp.single i (d i) + Finsupp.single i 1 :=
          congrArg (fun e : σ →₀ ℕ => e + Finsupp.single i 1) h
        _ = _ := (Finsupp.single_add i (d i) 1).symm
  simp only [he]
  split_ifs <;> simp [PowerSeries.coeff_derivative, mul_comm]

theorem pderiv_toMvPowerSeries_of_ne (i j : σ) (hji : j ≠ i) (f : PowerSeries R) :
    pderiv j (f.toMvPowerSeries i) = 0 := by
  classical
  ext d
  rw [coeff_pderiv, coeff_toMvPowerSeries, coeff_zero]
  have he : d + Finsupp.single j 1 ≠ Finsupp.single i ((d + Finsupp.single j 1 : σ →₀ ℕ) i) := by
    intro h
    have hj := DFunLike.congr_fun h j
    simp [hji] at hj
  simp only [ite_eq_right he, zero_mul]

end OneVariable

def logAt {σ : Type*} (i : σ) : MvPowerSeries σ ℂ :=
  (PowerSeries.log ℂ).toMvPowerSeries i

@[simp] theorem pderiv_logAt_of_ne {σ : Type*} (i j : σ) (hji : j ≠ i) :
    pderiv j (logAt i) = 0 := pderiv_toMvPowerSeries_of_ne i j hji _

theorem one_add_X_mul_pderiv_logAt {σ : Type*} (i : σ) :
    (1 + X i) * pderiv i (logAt i) = 1 := by
  have h := congrArg (PowerSeries.toMvPowerSeries i)
    (PowerSeries.derivative_log_mul_one_add_X (A := ℂ))
  rw [map_mul, map_add, map_one, PowerSeries.toMvPowerSeries_X] at h
  rw [logAt, pderiv_toMvPowerSeries_self, mul_comm]
  exact h

def formalJet {m : ℕ} (cy cz : ℂ) (c r : Fin m → ℂ) :
    Poly m →ₐ[ℂ] MvPowerSeries (Fin (m+2)) ℂ :=
  MvPolynomial.aeval (Fin.cases (C cy * (1 + X 0))
    (Fin.cases (C cz * (1 + X 1))
      (fun i => C (c i) + X i.succ.succ + logAt 1 - C (r i) * logAt 0)))

@[simp] theorem formalJet_Y {m : ℕ} (cy cz : ℂ) (c r : Fin m → ℂ) :
    formalJet cy cz c r (MvPolynomial.X 0) = C cy * (1 + X 0) := by
  simp [formalJet]

@[simp] theorem formalJet_Z {m : ℕ} (cy cz : ℂ) (c r : Fin m → ℂ) :
    formalJet cy cz c r (MvPolynomial.X 1) = C cz * (1 + X 1) := by
  simp only [formalJet, MvPolynomial.aeval_X]
  rfl

@[simp] theorem formalJet_C {m : ℕ} (cy cz : ℂ) (c r : Fin m → ℂ) (a : ℂ) :
    formalJet cy cz c r (MvPolynomial.C a) = C a := by
  simp [formalJet, MvPowerSeries.algebraMap_apply]

@[simp] theorem formalJet_aux {m : ℕ} (cy cz : ℂ) (c r : Fin m → ℂ) (i : Fin m) :
    formalJet cy cz c r (MvPolynomial.X i.succ.succ) =
      C (c i) + X i.succ.succ + logAt 1 - C (r i) * logAt 0 := by
  simp [formalJet]

def jetFrame (m : ℕ) : Fin (m+2) →
    Derivation ℂ (MvPowerSeries (Fin (m+2)) ℂ) (MvPowerSeries (Fin (m+2)) ℂ) :=
  Fin.cases ((1 + X 0 : MvPowerSeries (Fin (m+2)) ℂ) • pderiv 0)
    (Fin.cases ((1 + X 1 : MvPowerSeries (Fin (m+2)) ℂ) • pderiv 1)
      (fun i => pderiv i.succ.succ))

@[simp] theorem jetFrame_Y (m : ℕ) (f : MvPowerSeries (Fin (m+2)) ℂ) :
    jetFrame m 0 f = (1 + X 0) * pderiv 0 f := by
  simp [jetFrame, Derivation.smul_apply, smul_eq_mul]

@[simp] theorem jetFrame_Z (m : ℕ) (f : MvPowerSeries (Fin (m+2)) ℂ) :
    jetFrame m 1 f = (1 + X 1) * pderiv 1 f := by
  change ((1 + X 1 : MvPowerSeries (Fin (m+2)) ℂ) • pderiv 1) f = _
  simp only [Derivation.smul_apply, smul_eq_mul]

@[simp] theorem jetFrame_aux (m : ℕ) (i : Fin m) (f : MvPowerSeries (Fin (m+2)) ℂ) :
    jetFrame m i.succ.succ f = pderiv i.succ.succ f := rfl

theorem formalJet_frame_X {m : ℕ} (cy cz : ℂ) (c r : Fin m → ℂ)
    (i j : Fin (m+2)) :
    formalJet cy cz c r (frame m r i (MvPolynomial.X j)) =
      jetFrame m i (formalJet cy cz c r (MvPolynomial.X j)) := by
  classical
  have h01 : (0 : Fin (m+2)) ≠ 1 := by
    rw [← Fin.succ_zero_eq_one]
    exact (Fin.succ_ne_zero _).symm
  have h10 := h01.symm
  refine Fin.cases ?_ (fun i' => ?_) i
  · refine Fin.cases ?_ (fun j' => ?_) j
    · change formalJet cy cz c r (dY m r (MvPolynomial.X 0)) =
        (1 + X 0) * pderiv 0 (formalJet cy cz c r (MvPolynomial.X 0))
      rw [dY_X_zero]
      simp [Derivation.leibniz, smul_eq_mul, mul_comm]
    · refine Fin.cases ?_ (fun k => ?_) j'
      · change formalJet cy cz c r (dY m r (MvPolynomial.X 1)) =
          (1 + X 0) * pderiv 0 (formalJet cy cz c r (MvPolynomial.X 1))
        rw [dY_X_one]
        simp [Derivation.leibniz, smul_eq_mul, MvPowerSeries.pderiv_X_of_ne h10]
      · change formalJet cy cz c r (dY m r (MvPolynomial.X k.succ.succ)) =
          (1 + X 0) * pderiv 0 (formalJet cy cz c r (MvPolynomial.X k.succ.succ))
        rw [dY_X_aux]
        simp only [formalJet_C, formalJet_aux, map_sub, map_add, pderiv_C,
          MvPowerSeries.pderiv_X_of_ne (Fin.succ_ne_zero _),
          pderiv_logAt_of_ne _ _ h01,
          Derivation.leibniz, smul_eq_mul, mul_zero, add_zero, zero_sub]
        rw [mul_neg, mul_left_comm, one_add_X_mul_pderiv_logAt, mul_one, map_neg]
  · refine Fin.cases ?_ (fun k => ?_) i'
    · refine Fin.cases ?_ (fun j' => ?_) j
      · change formalJet cy cz c r (dZ m (MvPolynomial.X 0)) =
          (1 + X 1) * pderiv 1 (formalJet cy cz c r (MvPolynomial.X 0))
        rw [dZ_X_zero]
        simp [Derivation.leibniz, smul_eq_mul, MvPowerSeries.pderiv_X_of_ne h01]
      · refine Fin.cases ?_ (fun l => ?_) j'
        · change formalJet cy cz c r (dZ m (MvPolynomial.X 1)) =
            (1 + X 1) * pderiv 1 (formalJet cy cz c r (MvPolynomial.X 1))
          rw [dZ_X_one]
          simp [Derivation.leibniz, smul_eq_mul, mul_comm]
        · change formalJet cy cz c r (dZ m (MvPolynomial.X l.succ.succ)) =
            (1 + X 1) * pderiv 1 (formalJet cy cz c r (MvPolynomial.X l.succ.succ))
          rw [dZ_X_aux]
          simp [Derivation.leibniz, smul_eq_mul,
            MvPowerSeries.pderiv_X_of_ne, pderiv_logAt_of_ne, h10,
            one_add_X_mul_pderiv_logAt]
    · refine Fin.cases ?_ (fun j' => ?_) j
      · simp [frame, Derivation.leibniz, MvPolynomial.pderiv_X,
          MvPowerSeries.pderiv_X_of_ne (Fin.succ_ne_zero _).symm]
      · refine Fin.cases ?_ (fun l => ?_) j'
        · simp [frame, Fin.succ_zero_eq_one, Derivation.leibniz,
            MvPolynomial.pderiv_X, MvPowerSeries.pderiv_X_of_ne]
        · by_cases hkl : k = l
          · subst l
            simp [frame, MvPolynomial.pderiv_X, Derivation.leibniz,
              pderiv_logAt_of_ne]
          · simp [frame, MvPolynomial.pderiv_X, Derivation.leibniz,
              MvPowerSeries.pderiv_X_of_ne, pderiv_logAt_of_ne, Ne.symm hkl]

theorem formalJet_frame {m : ℕ} (cy cz : ℂ) (c r : Fin m → ℂ)
    (i : Fin (m+2)) (P : Poly m) :
    formalJet cy cz c r (frame m r i P) = jetFrame m i (formalJet cy cz c r P) :=
  FormalLogJet.derivation_map_of_X (formalJet cy cz c r) (frame m r i)
    (jetFrame m i) (formalJet_frame_X cy cz c r i) P

def jetWord (m : ℕ) (indices : List (Fin (m+2)))
    (f : MvPowerSeries (Fin (m+2)) ℂ) : MvPowerSeries (Fin (m+2)) ℂ :=
  indices.foldr (fun i g => jetFrame m i g) f

theorem formalJet_word {m : ℕ} (cy cz : ℂ) (c r : Fin m → ℂ)
    (indices : List (Fin (m+2))) (P : Poly m) :
    formalJet cy cz c r (word m r indices P) =
      jetWord m indices (formalJet cy cz c r P) := by
  induction indices with
  | nil => rfl
  | cons i indices ih =>
    change formalJet cy cz c r (frame m r i (word m r indices P)) = _
    rw [formalJet_frame, ih]
    rfl

theorem jetFrame_mem_weightedIdeal {m : ℕ}
    (v : Fin (m+2) → ℚ) (hv : ∀ i, 0 ≤ v i) (H : ℚ)
    (f : MvPowerSeries (Fin (m+2)) ℂ)
    (hf : f ∈ JetGeometry.rationalWeightedIdeal v hv H) (i : Fin (m+2)) :
    jetFrame m i f ∈ JetGeometry.rationalWeightedIdeal v hv (H - v i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact FormalJetDerivatives.mul_pderiv_mem_rationalWeightedIdeal
      v hv H f (1 + X 0) hf 0
  · refine Fin.cases ?_ (fun k => ?_) j
    · exact FormalJetDerivatives.mul_pderiv_mem_rationalWeightedIdeal
        v hv H f (1 + X 1) hf 1
    · exact FormalJetDerivatives.pderiv_mem_rationalWeightedIdeal v hv H f hf k.succ.succ

theorem jetWord_mem_weightedIdeal {m : ℕ}
    (v : Fin (m+2) → ℚ) (hv : ∀ i, 0 ≤ v i) (H : ℚ)
    (f : MvPowerSeries (Fin (m+2)) ℂ)
    (hf : f ∈ JetGeometry.rationalWeightedIdeal v hv H) (indices : List (Fin (m+2))) :
    jetWord m indices f ∈ JetGeometry.rationalWeightedIdeal v hv (H - (indices.map v).sum) := by
  induction indices with
  | nil => simpa [jetWord] using hf
  | cons i indices ih =>
    have h := jetFrame_mem_weightedIdeal v hv (H - (indices.map v).sum)
      (jetWord m indices f) ih i
    simpa only [jetWord, List.foldr_cons, List.map_cons, List.sum_cons, sub_sub, add_comm]
      using h

theorem formalJet_word_vanishing {m : ℕ} (cy cz : ℂ) (c r : Fin m → ℂ)
    (v : Fin (m+2) → ℚ) (hv : ∀ i, 0 ≤ v i) (H : ℚ) (P : Poly m)
    (hP : formalJet cy cz c r P ∈ JetGeometry.rationalWeightedIdeal v hv H)
    (indices : List (Fin (m+2))) :
    formalJet cy cz c r (word m r indices P) ∈
      JetGeometry.rationalWeightedIdeal v hv (H - (indices.map v).sum) := by
  rw [formalJet_word]
  exact jetWord_mem_weightedIdeal v hv H (formalJet cy cz c r P) hP indices

def formalJetEvaluation {m : ℕ} (K : ℕ)
    (V : Fin (m+2) → ℝ) (H : ℝ) (cy cz : Fin K → ℂ)
    (c : Fin K → Fin m → ℂ) (r : Fin m → ℂ) :
    Poly m →ₗ[ℂ] ((Fin K × ↥(strictWeightedSimplex V H)) → ℂ) :=
  LinearMap.pi (fun ρ =>
    (MvPowerSeries.coeff (InterpolationMatrix.exponentVector ρ.2.val)).comp
      (formalJet (cy ρ.1) (cz ρ.1) (c ρ.1) r).toLinearMap)

theorem eventually_exists_auxiliaryPolynomial {m : ℕ}
    (W V : Fin (m+2) → ℚ) (hW : ∀ i, 0 < W i) (hV : ∀ i, 0 < V i)
    (K : ℕ) {a : ℝ} (ha : 0 < a)
    (hvol : (K : ℝ) * a^(m+2) * (∏ i, (W i : ℝ)) / (∏ i, (V i : ℝ)) < 1)
    (cy cz : Fin K → ℂ) (c : Fin K → Fin m → ℂ) (r : Fin m → ℂ) :
    ∀ᶠ N : ℝ in atTop, ∃ P : Poly m, P ≠ 0 ∧
      HasWeightedDegreeLE (fun i => (W i : ℝ)) N P ∧
      ∀ j d, Finsupp.weight (fun i => (V i : ℝ)) d < a*N →
        MvPowerSeries.coeff d (formalJet (cy j) (cz j) (c j) r P) = 0 := by
  filter_upwards [OAI.PiExponent.eventually_exists_auxiliaryPolynomial W V hW hV K ha hvol]
    with N hN
  obtain ⟨P, hP, hw, he⟩ := hN (formalJetEvaluation K (fun i => (V i : ℝ)) (a*N) cy cz c r)
  refine ⟨P, hP, hw, ?_⟩
  intro j d hd
  have hmem : (fun i => d i) ∈ strictWeightedSimplex (fun i => (V i : ℝ)) (a*N) := by
    apply (mem_strictWeightedSimplex (fun i => by exact_mod_cast hV i)).mpr
    simpa [Finsupp.weight_eq_sum, nsmul_eq_mul, mul_comm] using hd
  have hh := congrFun he (j, ⟨(fun i => d i), hmem⟩)
  have hd' : InterpolationMatrix.exponentVector (fun i => d i) = d := by ext i; rfl
  simpa [formalJetEvaluation, hd'] using hh

theorem eventually_exists_auxiliaryPolynomial_nat {m : ℕ}
    (W V : Fin (m+2) → ℚ) (hW : ∀ i, 0 < W i) (hV : ∀ i, 0 < V i)
    (K : ℕ) {a : ℚ} (ha : 0 < a)
    (hvol : (K : ℝ) * (a : ℝ)^(m+2) * (∏ i, (W i : ℝ)) / (∏ i, (V i : ℝ)) < 1)
    (cy cz : Fin K → ℂ) (c : Fin K → Fin m → ℂ) (r : Fin m → ℂ) :
    ∀ᶠ N : ℕ in atTop, ∃ P : Poly m, P ≠ 0 ∧
      HasWeightedDegreeLE (fun i => (W i : ℝ)) N P ∧
      ∀ j, formalJet (cy j) (cz j) (c j) r P ∈
        JetGeometry.rationalWeightedIdeal V (fun i => (hV i).le) (a*N) := by
  have h := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_exists_auxiliaryPolynomial W V hW hV K
      (by exact_mod_cast ha) hvol cy cz c r)
  filter_upwards [h] with N hN
  obtain ⟨P, hP, hw, hv⟩ := hN
  refine ⟨P, hP, hw, ?_⟩
  intro j d hd
  apply hv j d
  have hcast : ((Finsupp.weight V d : ℚ) : ℝ) < (a : ℝ)*(N : ℝ) := by exact_mod_cast hd
  simpa [Finsupp.weight_eq_sum, nsmul_eq_mul] using hcast

#print axioms formalJet_word_vanishing
#print axioms eventually_exists_auxiliaryPolynomial_nat

end LogarithmExtension.LogRatio.FormalJet

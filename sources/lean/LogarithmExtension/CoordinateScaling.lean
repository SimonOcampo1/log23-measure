import LogarithmExtension.NormalizedLogJet
import OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch

/-!
# Transport from a nonzero exponential centre to the unit centre

Polynomial substitution Y ↦ yY commutes with the logarithmic differential
frame. Normalizing a curve by Y ↦ Y/y therefore lets us reuse the upstream
local branch-order theorem, with its hypotheses checked explicitly.
-/

noncomputable section
namespace LogarithmExtension.CoordinateScaling

open OAI OAI.PiExponent OAI.PiExponentApprox
open CurveCenters CurveValuationCenter PlaceValuationRing

def scaleY {m : ℕ} (y : ℂ) : FramePolynomial m →ₐ[ℂ] FramePolynomial m :=
  MvPolynomial.aeval (Fin.cases (MvPolynomial.C y * MvPolynomial.X 0)
    (fun i => MvPolynomial.X i.succ))

@[simp] theorem scaleY_zero {m : ℕ} (y : ℂ) :
    scaleY y (MvPolynomial.X (0 : Fin (m+1))) =
      MvPolynomial.C y * MvPolynomial.X 0 := by simp [scaleY]

@[simp] theorem scaleY_succ {m : ℕ} (y : ℂ) (i : Fin m) :
    scaleY y (MvPolynomial.X i.succ) = MvPolynomial.X i.succ := by simp [scaleY]

theorem scaleY_comp {m : ℕ} (y z : ℂ) :
    (scaleY (m := m) y).comp (scaleY z) = scaleY (y*z) := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i using Fin.cases with
  | zero => simp [AlgHom.comp_apply, map_mul, mul_assoc, mul_comm y z]
  | succ i => simp

@[simp] theorem scaleY_one {m : ℕ} : scaleY (m := m) 1 = AlgHom.id ℂ _ := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i using Fin.cases <;> simp

def scaleEquiv {m : ℕ} (y : ℂ) (hy : y ≠ 0) :
    FramePolynomial m ≃ₐ[ℂ] FramePolynomial m :=
  AlgEquiv.ofAlgHom (scaleY y) (scaleY y⁻¹)
    (by rw [scaleY_comp, mul_inv_cancel₀ hy, scaleY_one])
    (by rw [scaleY_comp, inv_mul_cancel₀ hy, scaleY_one])

theorem scaleY_surjective {m : ℕ} (y : ℂ) (hy : y ≠ 0) :
    Function.Surjective (scaleY (m := m) y) := (scaleEquiv y hy).surjective

theorem scaleY_frame_X {m : ℕ} (y : ℂ) (i j : Fin (m+1)) :
    scaleY y (polynomialFrame m i (MvPolynomial.X j)) =
      polynomialFrame m i (scaleY y (MvPolynomial.X j)) := by
  classical
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => simp [logarithmicDerivation_apply, MvPolynomial.pderiv_X, mul_comm]
    | succ j => simp [logarithmicDerivation_apply, MvPolynomial.pderiv_X, Pi.single_apply]
  | succ i =>
    rw [polynomialFrame_pos m i.succ (Fin.succ_ne_zero i)]
    cases j using Fin.cases with
    | zero => simp [MvPolynomial.pderiv_X_of_ne (Ne.symm (Fin.succ_ne_zero i))]
    | succ j =>
      by_cases hij : i = j
      · subst j; simp
      · simp [MvPolynomial.pderiv_X, hij]

theorem scaleY_frame {m : ℕ} (y : ℂ) (i : Fin (m+1)) (P : FramePolynomial m) :
    scaleY y (polynomialFrame m i P) = polynomialFrame m i (scaleY y P) :=
  FormalLogJet.derivation_map_of_X (scaleY y) (polynomialFrame m i)
    (polynomialFrame m i) (scaleY_frame_X y i) P

theorem scaleY_frameWord {m : ℕ} (y : ℂ) (word : List (Fin (m+1)))
    (P : FramePolynomial m) :
    scaleY y (polynomialFrameWord m word P) = polynomialFrameWord m word (scaleY y P) := by
  induction word with
  | nil => rfl
  | cons i word ih => simp only [polynomialFrameWord_cons, scaleY_frame, ih]

theorem formalJet_scaleY {m : ℕ} (y : ℂ) (c : Fin m → ℂ) (P : FramePolynomial m) :
    FormalLogJet.formalJet c (scaleY y P) = NormalizedLogJet.formalJet y c P := by
  have he : (FormalLogJet.formalJet c).comp (scaleY y) =
      NormalizedLogJet.formalJet y c := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i using Fin.cases <;> simp [AlgHom.comp_apply, ← MvPowerSeries.c_eq_algebraMap]
  exact DFunLike.congr_fun he P

def normalize {E : Type*} [Field E] [Algebra ℂ E] {m : ℕ}
    (y : ℂ) (z : Fin (m+1) → E) : Fin (m+1) → E :=
  Fin.cases (z 0 / algebraMap ℂ E y) (fun i => z i.succ)

@[simp] theorem normalize_zero {E : Type*} [Field E] [Algebra ℂ E] {m : ℕ}
    (y : ℂ) (z : Fin (m+1) → E) : normalize y z 0 = z 0 / algebraMap ℂ E y := rfl

@[simp] theorem normalize_succ {E : Type*} [Field E] [Algebra ℂ E] {m : ℕ}
    (y : ℂ) (z : Fin (m+1) → E) (i : Fin m) : normalize y z i.succ = z i.succ := rfl

theorem aeval_normalize_scaleY {E : Type*} [Field E] [Algebra ℂ E] {m : ℕ}
    (y : ℂ) (hy : y ≠ 0) (z : Fin (m+1) → E) (P : FramePolynomial m) :
    MvPolynomial.aeval (normalize y z) (scaleY y P) = MvPolynomial.aeval z P := by
  have hyE : algebraMap ℂ E y ≠ 0 := (map_ne_zero_iff _ (algebraMap ℂ E).injective).mpr hy
  have he : (MvPolynomial.aeval (normalize y z)).comp (scaleY y) = MvPolynomial.aeval z := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i using Fin.cases with
    | zero =>
      simp only [AlgHom.comp_apply, scaleY_zero, map_mul, MvPolynomial.aeval_C,
        MvPolynomial.aeval_X, normalize_zero]
      field_simp
    | succ i => simp [AlgHom.comp_apply]
  exact DFunLike.congr_fun he P

theorem centered_normalize {E : Type*} [Field E] [Algebra ℂ E] {m : ℕ}
    (y : ℂ) (hy : y ≠ 0) (z : Fin (m+1) → E) (c : Fin m → ℂ)
    (p : NormalizedPlace ℂ E) (hc : Centered z (Fin.cases y c) p) :
    Centered (normalize y z) (Fin.cases 1 c) p := by
  have hyE : algebraMap ℂ E y ≠ 0 := (map_ne_zero_iff _ (algebraMap ℂ E).injective).mpr hy
  intro i
  cases i using Fin.cases with
  | zero =>
    have he : normalize y z 0 - algebraMap ℂ E ((Fin.cases (1 : ℂ) c : Fin (m+1) → ℂ) 0) =
        algebraMap ℂ E y⁻¹ * (z 0 - algebraMap ℂ E y) := by
      simp only [normalize_zero, Fin.cases_zero, map_one, map_inv₀]
      field_simp
    rw [he, p.valuation.map_mul,
      CurveProductFormula.valuation_constant_eq_zero p _ (inv_ne_zero hy), zero_add]
    exact hc 0
  | succ i => exact hc i.succ

theorem normalize_nonconstant {E : Type*} [Field E] [Algebra ℂ E] {m : ℕ}
    (y : ℂ) (hy : y ≠ 0) (z : Fin (m+1) → E) (c : Fin m → ℂ)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E ((Fin.cases y c : Fin (m+1) → ℂ) i)) :
    ∃ i, normalize y z i ≠ algebraMap ℂ E ((Fin.cases 1 c : Fin (m+1) → ℂ) i) := by
  have hyE : algebraMap ℂ E y ≠ 0 := (map_ne_zero_iff _ (algebraMap ℂ E).injective).mpr hy
  obtain ⟨i, hi⟩ := hnc
  refine ⟨i, ?_⟩
  cases i using Fin.cases with
  | zero =>
    intro he
    apply hi
    have he' : z 0 / algebraMap ℂ E y = 1 := by simpa using he
    exact (div_eq_one_iff_eq hyE).mp he'
  | succ i => exact hi

def contact {E : Type*} [Field E] [Algebra ℂ E] {m : ℕ}
    (p : NormalizedPlace ℂ E)
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))]
    (y : ℂ) (hy : y ≠ 0) (z : Fin (m+1) → E) (c : Fin m → ℂ)
    (hc : Centered z (Fin.cases y c) p)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E ((Fin.cases y c : Fin (m+1) → ℂ) i))
    (v : Fin (m+1) → ℚ) : ℚ :=
  PlaceCenteredBranch.logContact p (normalize y z) c
    (centered_normalize y hy z c p hc) (normalize_nonconstant y hy z c hnc) v

theorem contact_pos {E : Type*} [Field E] [Algebra ℂ E] {m : ℕ}
    (p : NormalizedPlace ℂ E)
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))]
    (y : ℂ) (hy : y ≠ 0) (z : Fin (m+1) → E) (c : Fin m → ℂ)
    (hc : Centered z (Fin.cases y c) p)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E ((Fin.cases y c : Fin (m+1) → ℂ) i))
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) :
    0 < contact p y hy z c hc hnc v :=
  PlaceCenteredBranch.logContact_pos p (normalize y z) c _ _ v hv

theorem word_order_lower {E : Type*} [Field E] [Algebra ℂ E] {m : ℕ}
    (p : NormalizedPlace ℂ E)
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))]
    (y : ℂ) (hy : y ≠ 0) (z : Fin (m+1) → E) (c : Fin m → ℂ)
    (hc : Centered z (Fin.cases y c) p)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E ((Fin.cases y c : Fin (m+1) → ℂ) i))
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ) (P : FramePolynomial m)
    (hP : NormalizedLogJet.formalJet y c P ∈
      JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) H)
    (word : List (Fin (m+1)))
    (hne : MvPolynomial.aeval z (polynomialFrameWord m word P) ≠ 0) :
    contact p y hy z c hc hnc v * (H - (word.map v).sum) ≤
      (WeightedPolynomialPole.coordinateOrder p.valuation
        (MvPolynomial.aeval z (polynomialFrameWord m word P)) : ℚ) := by
  have he : MvPolynomial.aeval (normalize y z) (polynomialFrameWord m word (scaleY y P)) =
      MvPolynomial.aeval z (polynomialFrameWord m word P) := by
    rw [← scaleY_frameWord, aeval_normalize_scaleY y hy]
  have h := PlaceCenteredBranch.logWord_field_order_lower p (normalize y z) c
    (centered_normalize y hy z c p hc) (normalize_nonconstant y hy z c hnc)
    v hv H (scaleY y P) (by rwa [formalJet_scaleY]) word (by rwa [he])
  simpa only [he, contact] using h

theorem nonconstant_tail_of_constant_first
    {E : Type*} [Field E] [Algebra ℂ E] {m : ℕ}
    (y : ℂ) (z : Fin (m+1) → E) (c : Fin m → ℂ)
    (hz : z 0 = algebraMap ℂ E y)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E ((Fin.cases y c : Fin (m+1) → ℂ) i)) :
    ∃ i : Fin m, z i.succ ≠ algebraMap ℂ E (c i) := by
  obtain ⟨i, hi⟩ := hnc
  cases i using Fin.cases with
  | zero => exact (hi hz).elim
  | succ i => exact ⟨i, hi⟩

theorem contact_of_constant_first
    {E : Type*} [Field E] [Algebra ℂ E] {m : ℕ}
    (p : NormalizedPlace ℂ E)
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))]
    (y : ℂ) (hy : y ≠ 0) (z : Fin (m+1) → E) (c : Fin m → ℂ)
    (hc : Centered z (Fin.cases y c) p)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E ((Fin.cases y c : Fin (m+1) → ℂ) i))
    (v : Fin (m+1) → ℚ) (hz : z 0 = algebraMap ℂ E y) :
    contact p y hy z c hc hnc v =
      PlaceCenteredBranch.ordinaryContact p (fun i => z i.succ) c
        (fun i => hc i.succ) (nonconstant_tail_of_constant_first y z c hz hnc)
        (fun i => v i.succ) := by
  have hyE : algebraMap ℂ E y ≠ 0 := (map_ne_zero_iff _ (algebraMap ℂ E).injective).mpr hy
  have he : normalize y z = Fin.cases 1 (fun i => z i.succ) := by
    funext i
    cases i using Fin.cases <;> simp [hz, hyE]
  have hcongr {u u' : Fin (m+1) → E} (he : u = u')
      (hu : Centered u (Fin.cases 1 c) p) (hu' : Centered u' (Fin.cases 1 c) p)
      (hnu : ∃ i, u i ≠ algebraMap ℂ E ((Fin.cases 1 c : Fin (m+1) → ℂ) i))
      (hnu' : ∃ i, u' i ≠ algebraMap ℂ E ((Fin.cases 1 c : Fin (m+1) → ℂ) i)) :
      PlaceCenteredBranch.logContact p u c hu hnu v =
        PlaceCenteredBranch.logContact p u' c hu' hnu' v := by
    subst u'
    rfl
  have hcn : Centered (Fin.cases (1 : E) (fun i => z i.succ)) (Fin.cases 1 c) p :=
    he ▸ centered_normalize y hy z c p hc
  have hnn := he ▸ normalize_nonconstant y hy z c hnc
  exact (hcongr he _ hcn _ hnn).trans
    (PlaceCenteredBranch.logContact_one p (fun i => z i.succ) c hcn hnn v)

theorem weightedDegree_constant_first
    {E : Type*} [Field E] [Algebra ℂ E] {m : ℕ}
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (y : ℂ) (hz : z 0 = algebraMap ℂ E y)
    (w : Fin (m+1) → ℚ) :
    CurveContactSum.weightedDegree hfinite z w =
      CurveContactSum.weightedDegree hfinite (fun i : Fin m => z i.succ) (fun i => w i.succ) := by
  have he : CurveContactSum.weightedPoleDivisor hfinite z w =
      CurveContactSum.weightedPoleDivisor hfinite (fun i : Fin m => z i.succ) (fun i => w i.succ) := by
    ext p
    change WeightedPolynomialPole.coordinatePole p.valuation z w =
      WeightedPolynomialPole.coordinatePole p.valuation (fun i : Fin m => z i.succ) (fun i => w i.succ)
    have he' : (fun i => (WeightedPolynomialPole.coordinateOrder p.valuation (z i) : ℚ)) =
        Fin.cases 0 (fun i => (WeightedPolynomialPole.coordinateOrder p.valuation (z i.succ) : ℚ)) := by
      funext i
      cases i using Fin.cases with
      | zero => simp [hz, CurveContactSum.coordinateOrder_constant_eq_zero]
      | succ i => rfl
    unfold WeightedPolynomialPole.coordinatePole
    rw [he']
    exact FibreContact.weightedPole_zero_cons w _
  unfold CurveContactSum.weightedDegree
  rw [he]

#print axioms word_order_lower
#print axioms contact_of_constant_first
#print axioms weightedDegree_constant_first

end LogarithmExtension.CoordinateScaling

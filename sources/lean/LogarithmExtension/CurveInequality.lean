import LogarithmExtension.CurveDerivativeVanishing
import OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateContactBound

/-! # Weighted curve inequality for distinct exponential centres

The excess-to-rigidity step adapts the pinned OpenAI proof (Apache-2.0).
Unlike the common-unit-centre argument, distinct first coordinates will
exclude excess without constructing a second auxiliary polynomial.
-/

noncomputable section
namespace LogarithmExtension.CurveInequality
open OAI OAI.PiExponent OAI.PiExponentApprox
open CurveValuationCenter PlaceValuationRing PersistentWeightComparison
open LogarithmExtension.CurveContactFamily
open Filter Topology
open scoped BigOperators

theorem excess_implies_zeroth_constant
    {E : Type*} [Field E] [Algebra ℂ E] {m K : ℕ}
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (hy : ∀ j, y j ≠ 0)
    (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i))
    (hheight : (CurveFieldRigidity.coordinateKernel z).height ≤ m)
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (sigma : ℚ) (hsigma : 0 < sigma)
    (hvol : (K : ℝ) * (1+3*(sigma : ℝ))^(m+1) *
      (∏ i, (w i : ℝ)) / (∏ i, (v i : ℝ)) < 1)
    (hseparated : ∀ A B : Finset (Fin (m+1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      comparisonConstant m sigma * (∏ j ∈ B, (v j : ℝ)) < ∏ j ∈ A, (w j : ℝ))
    (hexcess : CurveContactSum.weightedDegree hfinite z w <
      (1+(sigma : ℝ)) * ∑ p ∈ places hfinite z y c hz, (contact hres hfinite z y hy c hz v p : ℝ)) :
    ∃ j : Fin K, z 0 = algebraMap ℂ E (y j) := by
  have hvR (i : Fin (m+1)) : (0 : ℝ) < v i := by exact_mod_cast hv i
  have hsR : (0 : ℝ) < sigma := by exact_mod_cast hsigma
  have haux := NormalizedLogJet.eventually_exists_auxiliaryPolynomial_nat w v hw hv K
    (a := 1+3*sigma) (by positivity) (by simpa using hvol) y c
  have hrect := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_uniformRectangles (m+1) (fun i => (v i : ℝ)) hvR
      ((sigma : ℝ)/((m : ℝ)+2)) (by positivity))
  obtain ⟨N, hauxN, hrectN, hN⟩ :=
    (haux.and (hrect.and (eventually_gt_atTop (0 : ℕ)))).exists
  obtain ⟨F, hF0, hF, hjet⟩ := hauxN
  have hwords := logarithmic_words_vanish hres hfinite z y hy c hz
    w v hw hv sigma hsigma N hN F hF hjet hexcess
  have hS : (places hfinite z y c hz).Nonempty := by
    by_contra h
    have he : places hfinite z y c hz = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    rw [he, Finset.sum_empty, mul_zero] at hexcess
    exact (not_lt_of_ge (CurveContactSum.weightedDegree_nonneg hfinite z w)) hexcess
  obtain ⟨p,hp⟩ := hS
  refine ⟨center hfinite z y c hz p hp, ?_⟩
  exact logarithmic_coordinate_eq_center z
    (Fin.cases (y (center hfinite z y c hz p hp)) (c (center hfinite z y c hz p hp)))
    (by simpa only [Fin.cases_zero] using hy (center hfinite z y c hz p hp))
    p (centered hfinite z y c hz p hp) hheight w hw (fun i => (v i : ℝ)) hvR
    sigma N hsR (by exact_mod_cast hN) hrectN F hF0 hF hwords hseparated

theorem no_excess_of_constant_first
    {E : Type*} [Field E] [Algebra ℂ E] {m K : ℕ}
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (hy : ∀ j, y j ≠ 0)
    (hiy : Function.Injective y) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i))
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (sigma : ℚ) (hsigma : 0 < sigma)
    (hratio : ∀ i : Fin m, (1+(sigma : ℝ)) * (w i.succ : ℝ) < v i.succ)
    (hconst : ∃ j : Fin K, z 0 = algebraMap ℂ E (y j)) :
    ¬ CurveContactSum.weightedDegree hfinite z w <
      (1+(sigma : ℝ)) * ∑ p ∈ places hfinite z y c hz,
        (contact hres hfinite z y hy c hz v p : ℝ) := by
  intro hexcess
  obtain ⟨j0, hj0⟩ := hconst
  let S := places hfinite z y c hz
  let μ := fun p => (contact hres hfinite z y hy c hz v p : ℝ)
  let x : Fin m → E := fun i => z i.succ
  have hdeg : CurveContactSum.weightedDegree hfinite z w =
      CurveContactSum.weightedDegree hfinite x (fun i => w i.succ) :=
    CoordinateScaling.weightedDegree_constant_first hfinite z (y j0) hj0 w
  have hex : CurveContactSum.weightedDegree hfinite x (fun i => w i.succ) <
      (1+(sigma : ℝ)) * ∑ p ∈ S, μ p := by
    rw [hdeg] at hexcess
    exact hexcess
  have hsum : 0 < ∑ p ∈ S, μ p := by
    have hn := CurveContactSum.weightedDegree_nonneg hfinite x (fun i => w i.succ)
    have hs : (0 : ℝ) < 1+sigma := by exact_mod_cast (by linarith : (0 : ℚ) < 1+sigma)
    exact (mul_pos_iff_of_pos_left hs).mp (lt_of_le_of_lt hn hex)
  have hcenters : ∀ p (hp : p ∈ S), center hfinite z y c hz p hp = j0 := by
    intro p hp
    apply hiy
    exact ((centered hfinite z y c hz p hp).constant_coordinate 0 (y j0) hj0).symm
  have hcenter : ∀ p ∈ S, CurveCenters.Centered x (c j0) p := by
    intro p hp i
    simpa only [hcenters p hp, Fin.cases_succ] using
      centered hfinite z y c hz p hp i.succ
  have hnc : ∃ i, x i ≠ algebraMap ℂ E (c j0 i) :=
    CoordinateScaling.nonconstant_tail_of_constant_first (y j0) z (c j0) hj0
      (CurveCenters.Centered.exists_nonzero_difference z _ hz)
  obtain ⟨i, hi⟩ := hnc
  have hcoord := CoordinateContactBound.coordinate_contact_sum_le hfinite x (c j0)
    (fun i => w i.succ) (fun i => v i.succ) (fun i => hw i.succ) (fun i => hv i.succ)
    i (sub_ne_zero.mpr hi) S hcenter (fun p _ => hres p) μ (by
      intro p hp
      let := hres p
      have hp' : p ∈ places hfinite z y c hz := hp
      have hconstp : z 0 = algebraMap ℂ E (y (center hfinite z y c hz p hp)) := by
        rw [hcenters p hp]
        exact hj0
      have heq := CoordinateScaling.contact_of_constant_first p
        (y (center hfinite z y c hz p hp)) (hy _) z (c (center hfinite z y c hz p hp))
        (centered hfinite z y c hz p hp)
        (CurveCenters.Centered.exists_nonzero_difference z _ hz) v hconstp
      have hcongr {a b : Fin m → ℂ} (hab : a = b)
          (ha : CurveCenters.Centered x a p) (hna : ∃ i, x i ≠ algebraMap ℂ E (a i))
          (hb : CurveCenters.Centered x b p) (hnb : ∃ i, x i ≠ algebraMap ℂ E (b i)) :
          PlaceCenteredBranch.ordinaryContact p x a ha hna (fun i => v i.succ) =
            PlaceCenteredBranch.ordinaryContact p x b hb hnb (fun i => v i.succ) := by
        subst b
        rfl
      have hcontact := heq.trans (hcongr (congrArg c (hcenters p hp)) _ _
        (hcenter p hp) ⟨i, hi⟩)
      simpa only [μ, contact, dite_eq_left hp'] using
        congrArg (fun q : ℚ => (q : ℝ)) hcontact)
  have hwi : (0 : ℝ) < w i.succ := by exact_mod_cast hw i.succ
  have hb := mul_lt_mul_of_pos_left hex hwi
  have hr := mul_lt_mul_of_pos_right (hratio i) hsum
  nlinarith

/-- The curve inequality at distinct nonzero first coordinates. There is no
common-fibre volume hypothesis and no injectivity requirement on X-centres. -/
theorem weighted_curve_inequality
    {E : Type*} [Field E] [Algebra ℂ E] {m K : ℕ}
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (hy : ∀ j, y j ≠ 0)
    (hiy : Function.Injective y) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i))
    (hheight : (CurveFieldRigidity.coordinateKernel z).height ≤ m)
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (sigma : ℚ) (hsigma : 0 < sigma)
    (hvol : (K : ℝ) * (1+3*(sigma : ℝ))^(m+1) *
      (∏ i, (w i : ℝ)) / (∏ i, (v i : ℝ)) < 1)
    (hseparated : ∀ A B : Finset (Fin (m+1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      comparisonConstant m sigma * (∏ j ∈ B, (v j : ℝ)) < ∏ j ∈ A, (w j : ℝ))
    (hratio : ∀ i : Fin m, (1+(sigma : ℝ)) * (w i.succ : ℝ) < v i.succ) :
    (1+(sigma : ℝ)) * ∑ p ∈ places hfinite z y c hz,
        (contact hres hfinite z y hy c hz v p : ℝ) ≤
      CurveContactSum.weightedDegree hfinite z w := by
  by_contra h
  have hexcess := lt_of_not_ge h
  have hconst := excess_implies_zeroth_constant hres hfinite z y hy c hz hheight
    w v hw hv sigma hsigma hvol hseparated hexcess
  exact no_excess_of_constant_first hres hfinite z y hy hiy c hz
    w v hw hv sigma hsigma hratio hconst hexcess

#print axioms excess_implies_zeroth_constant
#print axioms weighted_curve_inequality

end LogarithmExtension.CurveInequality

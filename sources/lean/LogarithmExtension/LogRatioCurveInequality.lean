import LogarithmExtension.LogRatioContactFamily
import LogarithmExtension.LogRatioConstantBases
import LogarithmExtension.CurveGeometry

/-!
# The complete two-base weighted curve inequality

This assembles the actual logarithmic contacts, auxiliary polynomial,
derivative persistence, primitive-character rigidity and both final curve
cases. No rank or interpolation-surjectivity assertion is a hypothesis.
The proof architecture adapts the pinned OpenAI curve argument (Apache-2.0).
This module is geometric: it does not state an irrationality-exponent bound.
-/

noncomputable section
namespace LogarithmExtension.LogRatio.CurveInequality

open OAI OAI.PiExponent OAI.PiExponentApprox
open CurveValuationCenter PlaceValuationRing CurveCenters CurveFieldRigidity
open OAI.PiExponent.DerivativeIdeals
open PolynomialFrame ContactFamily
open Filter Topology
open scoped BigOperators

variable {E : Type*} [Field E] [Algebra ℂ E] {m K : ℕ}

theorem logarithmic_words_vanish
    (hres : ∀ place : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring place)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : Fin (m+2) → E) (hx : ∃ i, Transcendental ℂ (x i))
    (r : Fin m → ℂ) (w v : Fin (m+2) → ℚ)
    (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (sigma : ℚ) (hsigma : 0 < sigma) (N : ℕ) (hN : 0 < N)
    (F : Poly m) (hF : HasWeightedDegreeLE (fun i => (w i : ℝ)) N F)
    (hjet : ∀ j : Fin K, FormalJet.formalJet (2^j.val) (3^j.val) (fun _ => 0) r F ∈
      JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) ((1+3*sigma)*N))
    (hexcess : CurveContactSum.weightedDegree hfinite x w <
      (1+(sigma : ℝ)) * ∑ place ∈ places hfinite x hx K,
        (contact hres hfinite x hx K r v place : ℝ)) :
    ∀ indices : List (Fin (m+2)),
      wordCost (fun i => (v i : ℝ)) indices ≤ (sigma : ℝ)*N →
        MvPolynomial.aeval x (word m r indices F) = 0 := by
  intro indices hindices
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsR : (0 : ℝ) < sigma := by exact_mod_cast hsigma
  have hcost : (indices.map v).sum ≤ sigma*N := by
    change (indices.map (fun i => (v i : ℝ))).sum ≤ (sigma : ℝ)*N at hindices
    rw [← OAI.PiExponent.CurveDerivativeVanishing.cast_word_cost v indices] at hindices
    exact_mod_cast hindices
  have hdegree : ∀ d ∈ (word m r indices F).support,
      Finsupp.weight (fun i => (w i : ℝ)) d ≤ (N : ℝ) := by
    apply (FrameEquationFamily.hasWeightedDegreeLE_iff_supportBound _ _ _).mp
    exact degree_word m r hF (fun i => by exact_mod_cast (hw i).le) indices
  have hsum : 0 ≤ ∑ place ∈ places hfinite x hx K,
      (contact hres hfinite x hx K r v place : ℝ) := by
    apply Finset.sum_nonneg
    intro place _
    exact_mod_cast contact_nonneg hres hfinite x hx K r v hv place
  apply CurveContactSum.polynomial_eq_zero_of_excess_contact hfinite x w hw
    (N : ℝ) ((1+2*(sigma : ℝ))*N) hNR.le (word m r indices F) hdegree
    (places hfinite x hx K) (fun place => (contact hres hfinite x hx K r v place : ℝ))
  · intro hne place hp
    have hret : (1+2*sigma)*(N : ℚ) ≤ (1+3*sigma)*N - (indices.map v).sum := by
      nlinarith
    have hlocal := word_order_lower hres hfinite x hx K r v hv ((1+3*sigma)*N)
      F hjet indices hne place hp
    have hq := (mul_le_mul_of_nonneg_left hret
      (contact_nonneg hres hfinite x hx K r v hv place)).trans hlocal
    have hr : (contact hres hfinite x hx K r v place : ℝ) * ((1+2*(sigma : ℝ))*N) ≤
        (WeightedPolynomialPole.coordinateOrder place.valuation
          (MvPolynomial.aeval x (word m r indices F)) : ℝ) := by
      exact_mod_cast hq
    simpa only [mul_comm] using hr
  · calc
      (N : ℝ) * CurveContactSum.weightedDegree hfinite x w <
          N * ((1+(sigma : ℝ)) * ∑ place ∈ places hfinite x hx K,
            (contact hres hfinite x hx K r v place : ℝ)) := mul_lt_mul_of_pos_left hexcess hNR
      _ = (1+(sigma : ℝ)) * (N * ∑ place ∈ places hfinite x hx K,
          (contact hres hfinite x hx K r v place : ℝ)) := by ring
      _ ≤ (1+2*(sigma : ℝ)) * (N * ∑ place ∈ places hfinite x hx K,
          (contact hres hfinite x hx K r v place : ℝ)) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hNR.le hsum)
      _ = _ := by ring

/-- Excess contact forces a nonzero constant primitive character on the curve.
The separated-weight comparison has already been proved from multiplicity. -/
theorem excess_implies_character
    (hres : ∀ place : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring place)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : Fin (m+2) → E) (hx : ∃ i, Transcendental ℂ (x i))
    (hheight : (coordinateKernel x).height ≤ m+1)
    (p q : Fin m → ℕ) (hq : ∀ i, 0 < q i)
    (w v : Fin (m+2) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (hwbase : w 1 = w 0) (hvbase : v 1 = v 0)
    (sigma : ℚ) (hsigma : 0 < sigma)
    (hvol : (K : ℝ) * (1+3*(sigma : ℝ))^(m+2) *
      (∏ i, (w i : ℝ)) / (∏ i, (v i : ℝ)) < 1)
    (hbase : 2 * (1 / ((sigma : ℝ) / ((m : ℝ)+3))) * (v 0 : ℝ) < w 0)
    (hseparated : ∀ A B : Finset (Fin (m+2)), A.card = B.card →
      ∀ i, 2 ≤ i.val → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      (A.card : ℝ)^A.card * (1 / ((sigma : ℝ) / ((m : ℝ)+3)))^A.card *
        (∏ j ∈ B, (v j : ℝ)) < ∏ j ∈ A, (w j : ℝ))
    (hexcess : CurveContactSum.weightedDegree hfinite x w <
      (1+(sigma : ℝ)) * ∑ place ∈ places hfinite x hx K,
        (contact hres hfinite x hx K (fun i => (p i : ℂ)/(q i : ℂ)) v place : ℝ)) :
    ∃ (i : Fin m) (a : ℂ), a ≠ 0 ∧
      MvPolynomial.aeval x (CurveRelations.characterPolynomial m (p i) (q i) a) = 0 := by
  let r : Fin m → ℂ := fun i => (p i : ℂ)/(q i : ℂ)
  let eps : ℝ := (sigma : ℝ)/((m : ℝ)+3)
  have hsR : (0 : ℝ) < sigma := by exact_mod_cast hsigma
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hvR (i : Fin (m+2)) : (0 : ℝ) < v i := by exact_mod_cast hv i
  have haux := FormalJet.eventually_exists_auxiliaryPolynomial_nat w v hw hv K
    (a := 1+3*sigma) (by positivity) (by simpa using hvol)
    (fun j => 2^j.val) (fun j => 3^j.val) (fun _ _ => 0) r
  have hbudget : ∀ᶠ N : ℕ in atTop, ∀ i, ((m : ℝ)+2) * (v i : ℝ) < eps*N := by
    rw [Filter.eventually_all]
    intro i
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (eventually_gt_atTop (((m : ℝ)+2) * (v i : ℝ) / eps))] with N hN
    simpa only [mul_comm] using (div_lt_iff₀ heps).mp hN
  obtain ⟨N, hauxN, hbudgetN, hN⟩ :=
    (haux.and (hbudget.and (eventually_gt_atTop (0 : ℕ)))).exists
  obtain ⟨F, hF0, hF, hjet⟩ := hauxN
  have hwords := logarithmic_words_vanish hres hfinite x hx r w v hw hv
    sigma hsigma N hN F hF hjet hexcess
  have hS : (places hfinite x hx K).Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    rw [he, Finset.sum_empty, mul_zero] at hexcess
    exact (not_lt_of_ge (CurveContactSum.weightedDegree_nonneg hfinite x w)) hexcess
  obtain ⟨place, hp⟩ := hS
  have hcenter := centered hfinite x hx K place hp
  have hy : MvPolynomial.X (0 : Fin (m+2)) ∉ coordinateKernel x := by
    simp only [mem_coordinateKernel, MvPolynomial.aeval_X]
    intro hy
    have hc := hcenter.constant_coordinate 0 0 (by simpa using hy)
    simpa using hc.symm
  have hz : MvPolynomial.X (1 : Fin (m+2)) ∉ coordinateKernel x := by
    simp only [mem_coordinateKernel, MvPolynomial.aeval_X]
    intro hz
    have hc := hcenter.constant_coordinate 1 0 (by simpa using hz)
    simpa using hc.symm
  have hbound : ((m : ℝ)+3) * (eps*N) = (sigma : ℝ)*N := by
    dsimp [eps]
    field_simp
  have hrigid := PersistentRigidity.exists_rigid_persistent_component
    (fun i => (p i : ℤ)) (fun i => (q i : ℤ)) (fun i => by exact_mod_cast (hq i).ne')
    w hw (fun i => (v i : ℝ)) hvR eps N heps (by exact_mod_cast hN)
    (w 0 : ℝ) (v 0 : ℝ) (by exact_mod_cast hw 0) (hvR 0)
    ⟨rfl, by exact_mod_cast hwbase⟩ ⟨rfl, by exact_mod_cast hvbase⟩
    hbase hbudgetN F hF0 hF (coordinateKernel x) inferInstance hheight hy hz
    (by
      intro indices hi
      rw [mem_coordinateKernel]
      simpa only [Int.cast_natCast] using hwords indices (by simpa only [hbound] using hi))
    hseparated
  obtain ⟨i, a, b, ha, hchar, _⟩ :=
    CurveRelations.polynomial_relations_of_rigid_component (coordinateKernel x) hy hz p q hrigid
  exact ⟨i, a, ha, (mem_coordinateKernel x _).mp hchar⟩

/-- A primitive constant character excludes excess contact. This includes
both the nonconstant-base q-fold argument and the constant-base case. -/
theorem no_excess_of_character
    (hres : ∀ place : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring place)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : Fin (m+2) → E) (hx : ∃ i, Transcendental ℂ (x i))
    (r : Fin m → ℂ) (w v : Fin (m+2) → ℚ)
    (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (sigma : ℚ) (hsigma : 0 < sigma)
    (hratio : ∀ i : Fin m, (1+(sigma : ℝ)) * (w i.succ.succ : ℝ) < v i.succ.succ)
    (p q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime q p)
    (hqratio : (1+(sigma : ℝ)) * (w 0 : ℝ) < (q : ℝ) * (v 0 : ℝ))
    (a : ℂ) (ha : a ≠ 0)
    (hchar : MvPolynomial.aeval x (CurveRelations.characterPolynomial m p q a) = 0) :
    ¬ CurveContactSum.weightedDegree hfinite x w <
      (1+(sigma : ℝ)) * ∑ place ∈ places hfinite x hx K,
        (contact hres hfinite x hx K r v place : ℝ) := by
  intro hexcess
  let S := places hfinite x hx K
  let mu := fun place => (contact hres hfinite x hx K r v place : ℝ)
  have hex : CurveContactSum.weightedDegree hfinite x w <
      (1+(sigma : ℝ)) * ∑ place ∈ S, mu place := hexcess
  have hsR : (0 : ℝ) < sigma := by exact_mod_cast hsigma
  have hsum : 0 < ∑ place ∈ S, mu place := by
    have hpos := lt_of_le_of_lt (CurveContactSum.weightedDegree_nonneg hfinite x w) hex
    exact (mul_pos_iff_of_pos_left (by linarith : (0 : ℝ) < 1+sigma)).mp hpos
  have hS : S.Nonempty := by
    by_contra h
    simp only [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty, lt_self_iff_false]
      at hsum
  obtain ⟨place0, hp0⟩ := hS
  let j0 := index hfinite x hx K place0 hp0
  have hc0 : Centered x (CurveRelations.center m j0.val) place0 :=
    centered hfinite x hx K place0 hp0
  have hindices : ∀ place (hp : place ∈ S), index hfinite x hx K place hp = j0 := by
    intro place hp
    let := hres place
    let := hres place0
    apply Fin.ext
    exact CurveRelations.branch_center_index_unique m p q hq x a hchar
      _ _ place place0 (centered hfinite x hx K place hp) hc0
  have hc : ∀ place ∈ S, Centered x (CurveRelations.center m j0.val) place := by
    intro place hp
    simpa only [hindices place hp] using centered hfinite x hx K place hp
  have hnc := Centered.exists_nonzero_difference x (CurveRelations.center m j0.val) hx
  have hmu : ∀ place (hp : place ∈ S), letI := hres place;
      mu place = (PlaceContact.contact place x (2^j0.val) (3^j0.val) (fun _ => 0)
        (hc place hp) r (by simp) (by simp) hnc v : ℝ) := by
    intro place hp
    let := hres place
    exact congrArg (fun t : ℚ => (t : ℝ))
      (contact_eq_of_index hres hfinite x hx K r v place hp j0 (hindices place hp)
        (hc place hp) hnc)
  have hrel : (x 1)^q = algebraMap ℂ E a * (x 0)^p := by
    simpa only [CurveRelations.characterPolynomial, map_sub, map_pow, map_mul,
      MvPolynomial.aeval_X, MvPolynomial.aeval_C, sub_eq_zero] using hchar
  by_cases hy : Transcendental ℂ (x 0)
  · have hz : x 1 ≠ 0 := by
      intro hz
      have hh := hc0.constant_coordinate 1 0 (by simpa using hz)
      simpa using hh.symm
    have hb := PlaceContact.primitive_character_contact_sum hres hfinite x
      (2^j0.val) (3^j0.val) (fun _ => 0) r (by simp) (by simp) hnc
      w v hw hv hy hz a ha p q hq hcop hrel S hc mu hmu
    have hwi : (0 : ℝ) < w 0 := by exact_mod_cast hw 0
    have hlt : (w 0 : ℝ) * CurveContactSum.weightedDegree hfinite x w <
        ((q : ℝ) * (v 0 : ℝ)) * ∑ place ∈ S, mu place := by
      calc
        _ < (w 0 : ℝ) * ((1+(sigma : ℝ)) * ∑ place ∈ S, mu place) :=
          mul_lt_mul_of_pos_left hex hwi
        _ < _ := by
          simpa only [mul_assoc, mul_comm, mul_left_comm] using
            mul_lt_mul_of_pos_right hqratio hsum
    exact (not_lt_of_ge hb) hlt
  · have hyalg : IsAlgebraic ℂ (x 0) := not_not.mp hy
    obtain ⟨cy, hcy⟩ := CurveContactSum.exists_constant_of_isAlgebraic (x 0) hyalg
    have hzpow : IsAlgebraic ℂ ((x 1)^q) := by
      rw [hrel, ← hcy, ← map_pow, ← map_mul]
      exact isAlgebraic_algebraMap _
    obtain ⟨cz, hcz⟩ := CurveContactSum.exists_constant_of_isAlgebraic (x 1)
      (hzpow.of_pow hq)
    have hy0 : x 0 = algebraMap ℂ E (2^j0.val) := by
      have he := hc0.constant_coordinate 0 cy hcy.symm
      simpa only [he, CurveRelations.center_zero] using hcy.symm
    have hz0 : x 1 = algebraMap ℂ E (3^j0.val) := by
      have he := hc0.constant_coordinate 1 cz hcz.symm
      simpa only [he, CurveRelations.center_one] using hcz.symm
    obtain ⟨i, hi⟩ := ConstantBases.exists_nonconstant_aux x hx (2^j0.val) (3^j0.val) hy0 hz0
    have hne : x i.succ.succ - algebraMap ℂ E (0 : ℂ) ≠ 0 := by
      intro hh
      exact hi ((sub_eq_zero.mp hh).symm ▸ isAlgebraic_algebraMap _)
    have hb := ConstantBases.aux_contact_sum hres hfinite x (2^j0.val) (3^j0.val)
      (fun _ => 0) r (by simp) (by simp) hnc w v hw hv hy0 hz0 i hne S hc mu hmu
    have hwi : (0 : ℝ) < w i.succ.succ := by exact_mod_cast hw i.succ.succ
    have hlt : (w i.succ.succ : ℝ) * CurveContactSum.weightedDegree hfinite x w <
        (v i.succ.succ : ℝ) * ∑ place ∈ S, mu place := by
      calc
        _ < (w i.succ.succ : ℝ) * ((1+(sigma : ℝ)) * ∑ place ∈ S, mu place) :=
          mul_lt_mul_of_pos_left hex hwi
        _ < _ := by
          simpa only [mul_assoc, mul_comm, mul_left_comm] using
            mul_lt_mul_of_pos_right (hratio i) hsum
    exact (not_lt_of_ge hb) hlt

/-- The actual two-base curve inequality under the explicit geometric
weight, volume and reduced-denominator hypotheses. -/
theorem weighted_curve_inequality
    (hres : ∀ place : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring place)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : Fin (m+2) → E) (hx : ∃ i, Transcendental ℂ (x i))
    (hheight : (coordinateKernel x).height ≤ m+1)
    (p q : Fin m → ℕ) (hq : ∀ i, 0 < q i) (hcop : ∀ i, Nat.Coprime (q i) (p i))
    (w v : Fin (m+2) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (hwbase : w 1 = w 0) (hvbase : v 1 = v 0)
    (sigma : ℚ) (hsigma : 0 < sigma)
    (hvol : (K : ℝ) * (1+3*(sigma : ℝ))^(m+2) *
      (∏ i, (w i : ℝ)) / (∏ i, (v i : ℝ)) < 1)
    (hbase : 2 * (1 / ((sigma : ℝ) / ((m : ℝ)+3))) * (v 0 : ℝ) < w 0)
    (hseparated : ∀ A B : Finset (Fin (m+2)), A.card = B.card →
      ∀ i, 2 ≤ i.val → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      (A.card : ℝ)^A.card * (1 / ((sigma : ℝ) / ((m : ℝ)+3)))^A.card *
        (∏ j ∈ B, (v j : ℝ)) < ∏ j ∈ A, (w j : ℝ))
    (hratio : ∀ i : Fin m, (1+(sigma : ℝ)) * (w i.succ.succ : ℝ) < v i.succ.succ)
    (hqratio : ∀ i : Fin m, (1+(sigma : ℝ)) * (w 0 : ℝ) < (q i : ℝ) * (v 0 : ℝ)) :
    (1+(sigma : ℝ)) * ∑ place ∈ places hfinite x hx K,
        (contact hres hfinite x hx K (fun i => (p i : ℂ)/(q i : ℂ)) v place : ℝ) ≤
      CurveContactSum.weightedDegree hfinite x w := by
  by_contra h
  have hexcess := lt_of_not_ge h
  obtain ⟨i, a, ha, hchar⟩ := excess_implies_character hres hfinite x hx hheight p q hq
    w v hw hv hwbase hvbase sigma hsigma hvol hbase hseparated hexcess
  exact no_excess_of_character hres hfinite x hx (fun i => (p i : ℂ)/(q i : ℂ))
    w v hw hv sigma hsigma hratio (p i) (q i) (hq i) (hcop i) (hqratio i) a ha hchar hexcess

variable [Algebra.EssFiniteType ℂ E]

/-- The geometric function-field conditions discharge residue integrality,
parameter finiteness, nonconstancy and the height bound. -/
theorem weighted_curve_inequality_intrinsic
    (x : Fin (m+2) → E)
    (hgen : IntermediateField.adjoin ℂ (Set.range x) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1)
    (p q : Fin m → ℕ) (hq : ∀ i, 0 < q i) (hcop : ∀ i, Nat.Coprime (q i) (p i))
    (w v : Fin (m+2) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (hwbase : w 1 = w 0) (hvbase : v 1 = v 0)
    (sigma : ℚ) (hsigma : 0 < sigma)
    (hvol : (K : ℝ) * (1+3*(sigma : ℝ))^(m+2) *
      (∏ i, (w i : ℝ)) / (∏ i, (v i : ℝ)) < 1)
    (hbase : 2 * (1 / ((sigma : ℝ) / ((m : ℝ)+3))) * (v 0 : ℝ) < w 0)
    (hseparated : ∀ A B : Finset (Fin (m+2)), A.card = B.card →
      ∀ i, 2 ≤ i.val → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      (A.card : ℝ)^A.card * (1 / ((sigma : ℝ) / ((m : ℝ)+3)))^A.card *
        (∏ j ∈ B, (v j : ℝ)) < ∏ j ∈ A, (w j : ℝ))
    (hratio : ∀ i : Fin m, (1+(sigma : ℝ)) * (w i.succ.succ : ℝ) < v i.succ.succ)
    (hqratio : ∀ i : Fin m, (1+(sigma : ℝ)) * (w 0 : ℝ) < (q i : ℝ) * (v 0 : ℝ)) :
    let hres := PlaceLocalRing.residue_integral htrdeg.le
    let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
    let hx := CurveGeometry.nonconstant_coordinates x hgen htrdeg
    (1+(sigma : ℝ)) * ∑ place ∈ places hfinite x hx K,
        (contact hres hfinite x hx K (fun i => (p i : ℂ)/(q i : ℂ)) v place : ℝ) ≤
      CurveContactSum.weightedDegree hfinite x w := by
  exact weighted_curve_inequality _ _ x (CurveGeometry.nonconstant_coordinates x hgen htrdeg)
    (CurvePrimeHeight.kernel_height_succ_le x hgen htrdeg) p q hq hcop
    w v hw hv hwbase hvbase sigma hsigma hvol hbase hseparated hratio hqratio

#print axioms logarithmic_words_vanish
#print axioms excess_implies_character
#print axioms no_excess_of_character
#print axioms weighted_curve_inequality
#print axioms weighted_curve_inequality_intrinsic

end LogarithmExtension.LogRatio.CurveInequality

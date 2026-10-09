import LogarithmExtension.LogRatioPersistentRigidity
import LogarithmExtension.Basic
import OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch

/-!
# Polynomial relations and unique centers for the two-base construction

A constant rational character in the residue field of a component is first
cleared to a polynomial relation. Only ideal inclusion is then used to pass
to a contained curve; no nonexistent residue-field map is assumed. The actual
centers (2^j, 3^j, 0, ...) are separated by each nontrivial character.
-/

noncomputable section
namespace LogarithmExtension.LogRatio.CurveRelations

open MvPolynomial PolynomialFrame PersistentRigidity
open OAI.PiExponent OAI.PiExponent.CurveCenters OAI.PiExponent.CurveValuationCenter

def characterPolynomial (m p q : ℕ) (a : ℂ) : Poly m :=
  X 1 ^ q - C a * X 0 ^ p

theorem polynomial_relations_of_constant_character {m : ℕ}
    (Q : Ideal (Poly m)) [Q.IsPrime]
    (hy : primeResidueMap Q (X 0) ≠ 0) (hz : primeResidueMap Q (X 1) ≠ 0)
    (p q : Fin m → ℕ)
    (h : HasConstantCharacter Q (fun i => (p i : ℤ)) (fun i => (q i : ℤ))) :
    ∃ (i : Fin m) (a b : ℂ), a ≠ 0 ∧
      characterPolynomial m (p i) (q i) a ∈ Q ∧ X i.succ.succ - C b ∈ Q := by
  obtain ⟨i, ⟨a, ha⟩, ⟨b, hb⟩⟩ := h
  simp only [zpow_natCast] at ha
  have ha0 : a ≠ 0 := by
    intro hzero
    rw [hzero, map_zero] at ha
    exact div_ne_zero (pow_ne_zero _ hz) (pow_ne_zero _ hy) ha.symm
  have hmul : primeResidueMap Q (X 1) ^ q i =
      algebraMap ℂ Q.ResidueField a * primeResidueMap Q (X 0) ^ p i :=
    (div_eq_iff (pow_ne_zero _ hy)).mp ha.symm
  refine ⟨i, a, b, ha0, ?_, ?_⟩
  · apply Ideal.algebraMap_residueField_eq_zero.mp
    change primeResidueMap Q (characterPolynomial m (p i) (q i) a) = 0
    simp only [characterPolynomial, map_sub, map_pow, map_mul, algHom_C, hmul, sub_self]
  · apply Ideal.algebraMap_residueField_eq_zero.mp
    change primeResidueMap Q (X i.succ.succ - C b) = 0
    simp only [map_sub, algHom_C, hb, sub_self]

theorem polynomial_relations_of_rigid_component {m : ℕ}
    (P : Ideal (Poly m)) (hy : X (0 : Fin (m + 2)) ∉ P)
    (hz : X (1 : Fin (m + 2)) ∉ P) (p q : Fin m → ℕ)
    (h : ∃ (Q : Ideal (Poly m)) (hQ : Q.IsPrime), Q ≤ P ∧
      @HasConstantCharacter m Q hQ (fun i => (p i : ℤ)) (fun i => (q i : ℤ))) :
    ∃ (i : Fin m) (a b : ℂ), a ≠ 0 ∧
      characterPolynomial m (p i) (q i) a ∈ P ∧ X i.succ.succ - C b ∈ P := by
  obtain ⟨Q, hQ, hQP, hconstant⟩ := h
  let : Q.IsPrime := hQ
  obtain ⟨i, a, b, ha, hchar, hcoord⟩ := polynomial_relations_of_constant_character Q
    (fun h => hy (hQP (Ideal.algebraMap_residueField_eq_zero.mp h)))
    (fun h => hz (hQP (Ideal.algebraMap_residueField_eq_zero.mp h))) p q hconstant
  exact ⟨i, a, b, ha, hQP hchar, hQP hcoord⟩

def center (m j : ℕ) : Fin (m + 2) → ℂ :=
  Fin.cases (2 ^ j) (Fin.cases (3 ^ j) (fun _ => 0))

@[simp] theorem center_zero (m j : ℕ) : center m j 0 = 2 ^ j := rfl
@[simp] theorem center_one (m j : ℕ) : center m j 1 = 3 ^ j := rfl
@[simp] theorem center_aux (m j : ℕ) (i : Fin m) : center m j i.succ.succ = 0 := rfl

theorem three_pow_ne_two_pow (p q : ℕ) (hq : 0 < q) : (3 : ℕ)^q ≠ 2^p := by
  cases p with
  | zero =>
    have h : (1 : ℕ) < 3^q := one_lt_pow₀ (by norm_num) hq.ne'
    simpa using ne_of_gt h
  | succ p =>
    intro h
    have hmod := congrArg (fun n : ℕ => n % 2) h
    norm_num [Nat.pow_mod, pow_succ, Nat.mul_mod] at hmod

theorem character_base_ne_one (p q : ℕ) (hq : 0 < q) :
    (3 : ℝ)^q / (2 : ℝ)^p ≠ 1 := by
  intro h
  have he : (3 : ℝ)^q = (2 : ℝ)^p := (div_eq_one_iff_eq (by positivity)).mp h
  exact three_pow_ne_two_pow p q hq (by exact_mod_cast he)

theorem center_character_injective (m p q : ℕ) (hq : 0 < q) :
    Function.Injective (fun j : ℕ => center m j 1 ^ q / center m j 0 ^ p) := by
  intro j k hjk
  have he : (((3 : ℝ)^q / (2 : ℝ)^p)^j) = (((3 : ℝ)^q / (2 : ℝ)^p)^k) := by
    have hc : (((3 : ℂ)^q / (2 : ℂ)^p)^j) = (((3 : ℂ)^q / (2 : ℂ)^p)^k) := by
      simpa only [center_one, center_zero, div_pow, ← pow_mul, Nat.mul_comm] using hjk
    apply Complex.ofReal_injective
    push_cast
    exact hc
  exact positive_power_centers_injective _ (by positivity) (character_base_ne_one p q hq) he

theorem center_index_unique (m p q : ℕ) (hq : 0 < q) (a : ℂ) (j k : ℕ)
    (hj : eval (center m j) (characterPolynomial m p q a) = 0)
    (hk : eval (center m k) (characterPolynomial m p q a) = 0) : j = k := by
  apply center_character_injective m p q hq
  have hv (l : ℕ) (hl : eval (center m l) (characterPolynomial m p q a) = 0) :
      center m l 1 ^ q / center m l 0 ^ p = a := by
    apply (div_eq_iff (by simp)).mpr
    simpa only [characterPolynomial, map_sub, map_pow, map_mul, eval_X, eval_C,
      sub_eq_zero] using hl
  exact (hv j hj).trans (hv k hk).symm

/-- Polynomial equations valid on a curve also hold at the center of any
normalized branch. This uses the actual residue map of the valuation ring. -/
theorem eval_center_eq_zero {E ι : Type*} [Field E] [Algebra ℂ E]
    (place : NormalizedPlace ℂ E)
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (PlaceValuationRing.ring place))]
    (x : ι → E) (a : ι → ℂ) (ha : Centered x a place)
    (F : MvPolynomial ι ℂ) (hF : aeval x F = 0) : eval a F = 0 := by
  have hlift : aeval (PlaceCenteredBranch.lift place x a ha) F = 0 := by
    apply (IsFractionRing.injective (PlaceValuationRing.ring place) E)
    rw [map_zero, PlaceCenteredBranch.lift_aeval, hF]
  have he : CurveLocalOrder.residueAugmentation ℂ (PlaceValuationRing.ring place)
      (aeval (PlaceCenteredBranch.lift place x a ha) F) = eval a F := by
    let aug : PlaceValuationRing.ring place →ₐ[ℂ] ℂ :=
      { toRingHom := CurveLocalOrder.residueAugmentation ℂ (PlaceValuationRing.ring place)
        commutes' := CurveLocalOrder.residueAugmentation_algebraMap
          ℂ (PlaceValuationRing.ring place) }
    have hh := MvPolynomial.comp_aeval_apply
      (f := PlaceCenteredBranch.lift place x a ha) aug F
    simpa [aug, PlaceCenteredBranch.lift_residue] using hh
  rw [← he, hlift, map_zero]

theorem branch_center_index_unique {E : Type*} [Field E] [Algebra ℂ E]
    (m p q : ℕ) (hq : 0 < q) (x : Fin (m + 2) → E) (a : ℂ)
    (hchar : aeval x (characterPolynomial m p q a) = 0)
    (j k : ℕ) (place1 place2 : NormalizedPlace ℂ E)
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (PlaceValuationRing.ring place1))]
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (PlaceValuationRing.ring place2))]
    (hj : Centered x (center m j) place1) (hk : Centered x (center m k) place2) : j = k := by
  exact center_index_unique m p q hq a j k
    (eval_center_eq_zero place1 x _ hj _ hchar)
    (eval_center_eq_zero place2 x _ hk _ hchar)

#print axioms polynomial_relations_of_rigid_component
#print axioms branch_center_index_unique

end LogarithmExtension.LogRatio.CurveRelations

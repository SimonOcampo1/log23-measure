import LogarithmExtension.LogRatioTwoBaseFrame

/-!
# Excluding the base-only normal space in the two-base ratio geometry

The multiplicity comparison is kept in its dimension-sensitive form
`k^k L^k`, where `L = (m+3)/sigma` in the intended application. Replacing
this by a large dimension-independent constant would lose the base-only
case needed below. The comparison and weight separation are hypotheses,
not assumed conclusions of an unproved interpolation theorem.
-/

noncomputable section
namespace LogarithmExtension.LogRatio.NormalComparison

open Module OAI.PiExponent.NormalBasisRigidity TwoBaseFrame
open scoped BigOperators

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  (m : ℕ) (y z : K) (hy : y ≠ 0) (hz : z ≠ 0) (r : Fin m → K)

theorem normalBasis_subset_base
    (q : (Fin (m + 2) → K) →ₗ[K] V)
    (haux : ∀ i : Fin m, q (Pi.basisFun K _ i.succ.succ) = 0)
    (A : Finset (Fin (m + 2)))
    (hA : IsNormalBasis (K := K) (fun i => q (Pi.basisFun K _ i)) A) :
    A ⊆ {0, 1} := by
  intro i hi
  rcases Fin.eq_zero_or_eq_succ i with hi0 | ⟨j, hj⟩
  · simp [hi0]
  · rcases Fin.eq_zero_or_eq_succ j with hj0 | ⟨k, hk⟩
    · simp [hj, hj0]
    · exact False.elim (hA.ne_zero hi (by simpa only [hj, hk] using haux k))

theorem frameNormalBasis_subset_base
    (q : (Fin (m + 2) → K) →ₗ[K] V)
    (haux : ∀ i : Fin m, q (Pi.basisFun K _ i.succ.succ) = 0)
    (B : Finset (Fin (m + 2)))
    (hB : IsNormalBasis (K := K) (fun i => q (frameBasis m y z hy hz r i)) B) :
    B ⊆ {0, 1} := by
  intro i hi
  rcases Fin.eq_zero_or_eq_succ i with hi0 | ⟨j, hj⟩
  · simp [hi0]
  · rcases Fin.eq_zero_or_eq_succ j with hj0 | ⟨k, hk⟩
    · simp [hj, hj0]
    · exact False.elim (hB.ne_zero hi (by
        simpa only [hj, hk, frameBasis_aux] using haux k))

/-- A nonzero normal quotient with all auxiliary directions tangent cannot
satisfy the sharp multiplicity comparison when the base weight ratio is > 2L. -/
theorem not_all_aux_tangent
    (q : (Fin (m + 2) → K) →ₗ[K] V) (hq : Function.Surjective q) (hq0 : q ≠ 0)
    (w cost : Fin (m + 2) → ℝ) (w0 v0 L : ℝ)
    (hw0 : 0 < w0) (hv0 : 0 < v0) (hL : 0 < L)
    (hwbase : w 0 = w0 ∧ w 1 = w0) (hvbase : cost 0 = v0 ∧ cost 1 = v0)
    (hbase : 2 * L * v0 < w0)
    (hcomparison : ∀ A B : Finset (Fin (m + 2)),
      IsNormalBasis (K := K) (fun j => q (Pi.basisFun K _ j)) A →
      IsNormalBasis (K := K) (fun j => q (frameBasis m y z hy hz r j)) B →
      (∏ j ∈ A, w j) ≤ (A.card : ℝ)^A.card * L^A.card * ∏ j ∈ B, cost j) :
    ¬ ∀ i : Fin m, q (Pi.basisFun K _ i.succ.succ) = 0 := by
  classical
  intro haux
  obtain ⟨A, _, hA⟩ := exists_normalBasis_subset
    (fun j => q (Pi.basisFun K (Fin (m + 2)) j)) Set.univ
    (by simpa using span_mapped_basis_eq_top (Pi.basisFun K _) q hq)
  obtain ⟨B, _, hB⟩ := exists_normalBasis_subset
    (fun j => q (frameBasis m y z hy hz r j)) Set.univ
    (by simpa using span_mapped_basis_eq_top (frameBasis m y z hy hz r) q hq)
  have hAS := normalBasis_subset_base m q haux A hA
  have hBS := frameNormalBasis_subset_base m y z hy hz r q haux B hB
  have hcard := hA.card_eq.trans hB.card_eq.symm
  have hcardpos : 0 < A.card := by
    by_contra hnot
    have hAe : A = ∅ := Finset.card_eq_zero.mp (by omega)
    have hbt : (⊥ : Submodule K V) = ⊤ := by simpa [hAe] using hA.2
    apply hq0
    apply LinearMap.ext
    intro t
    have ht : q t ∈ (⊥ : Submodule K V) := by rw [hbt]; trivial
    simpa using ht
  have hcardle : A.card ≤ 2 := by
    have hh := Finset.card_le_card hAS
    have hpair : ({0, 1} : Finset (Fin (m + 2))).card ≤ 2 := by simp
    exact hh.trans hpair
  have hpw : (∏ j ∈ A, w j) = w0 ^ A.card := by
    calc
      _ = ∏ _j ∈ A, w0 := Finset.prod_congr rfl (fun j hj => by
        have hmem : j = 0 ∨ j = 1 := by simpa using hAS hj
        rcases hmem with h | h
        · simpa only [h] using hwbase.1
        · simpa only [h] using hwbase.2)
      _ = _ := by simp
  have hpc : (∏ j ∈ B, cost j) = v0 ^ A.card := by
    calc
      _ = ∏ _j ∈ B, v0 := Finset.prod_congr rfl (fun j hj => by
        have hmem : j = 0 ∨ j = 1 := by simpa using hBS hj
        rcases hmem with h | h
        · simpa only [h] using hvbase.1
        · simpa only [h] using hvbase.2)
      _ = v0 ^ B.card := by simp
      _ = _ := by rw [hcard]
  have hc := hcomparison A B hA hB
  rw [hpw, hpc] at hc
  have hcases : A.card = 1 ∨ A.card = 2 := by omega
  rcases hcases with hk | hk
  · norm_num [hk] at hc
    nlinarith [mul_pos hL hv0]
  · norm_num [hk] at hc
    have hp : 0 < (w0 - 2 * L * v0) * (w0 + 2 * L * v0) :=
      mul_pos (sub_pos.mpr hbase) (by positivity)
    nlinarith

/-- The full normal-space step: multiplicity comparison, separated auxiliary
weights and the base ratio force a genuine two-base tangent relation. -/
theorem exists_tangent_relation
    (q : (Fin (m + 2) → K) →ₗ[K] V) (hq : Function.Surjective q) (hq0 : q ≠ 0)
    (w cost : Fin (m + 2) → ℝ) (w0 v0 L : ℝ)
    (hw0 : 0 < w0) (hv0 : 0 < v0) (hL : 0 < L)
    (hwbase : w 0 = w0 ∧ w 1 = w0) (hvbase : cost 0 = v0 ∧ cost 1 = v0)
    (hbase : 2 * L * v0 < w0)
    (hcomparison : ∀ A B : Finset (Fin (m + 2)),
      IsNormalBasis (K := K) (fun j => q (Pi.basisFun K _ j)) A →
      IsNormalBasis (K := K) (fun j => q (frameBasis m y z hy hz r j)) B →
      (∏ j ∈ A, w j) ≤ (A.card : ℝ)^A.card * L^A.card * ∏ j ∈ B, cost j)
    (hseparated : ∀ A B : Finset (Fin (m + 2)), A.card = B.card →
      ∀ i, 2 ≤ i.val → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      (A.card : ℝ)^A.card * L^A.card * (∏ j ∈ B, cost j) < ∏ j ∈ A, w j) :
    ∃ i : Fin m, ∀ t, q t = 0 →
      t i.succ.succ + r i * (t 0 / y) - t 1 / z = 0 := by
  have hexclude : ∀ A B : Finset (Fin (m + 2)),
      IsNormalBasis (K := K) (fun j => q (Pi.basisFun K _ j)) A →
      IsNormalBasis (K := K) (fun j => q (frameBasis m y z hy hz r j)) B →
      ∀ i, 2 ≤ i.val → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) → False := by
    intro A B hA hB i hi2 hiA hiB hlarge
    exact (not_lt_of_ge (hcomparison A B hA hB))
      (hseparated A B (hA.card_eq.trans hB.card_eq.symm) i hi2 hiA hiB hlarge)
  rcases normal_basis_dichotomy m y z hy hz r q hq hexclude with haux | hrel
  · exact False.elim (not_all_aux_tangent m y z hy hz r q hq hq0 w cost w0 v0 L
      hw0 hv0 hL hwbase hvbase hbase hcomparison haux)
  · exact hrel

#print axioms exists_tangent_relation

end LogarithmExtension.LogRatio.NormalComparison

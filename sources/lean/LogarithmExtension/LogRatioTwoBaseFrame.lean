import OAI.NumberTheory.PiExponent.Jets.NormalFrameBasis
import OAI.NumberTheory.PiExponent.Jets.PolynomialTangentDifferential

/-!
# The two-multiplicative-coordinate frame for logarithmic ratios

This is a component of the proposed exponent-three upper-bound argument,
not an irrationality-exponent theorem. The two distinguished coordinates
are Y and Z, followed by the auxiliary coordinates X_i. The actual frame is

  D_Y = Y ∂Y - ∑ r_i ∂X_i,
  D_Z = Z ∂Z + ∑ ∂X_i,
  D_i = ∂X_i.

The normal-basis arguments adapt the pinned OpenAI single-base development
(Apache-2.0). Normal-basis exclusion is an explicit hypothesis: deriving it
from persistence and weighted multiplicity for this frame remains separate.
-/

noncomputable section
namespace LogarithmExtension.LogRatio.TwoBaseFrame

open Module OAI.PiExponent OAI.PiExponent.NormalBasisRigidity
open scoped BigOperators

variable {K : Type*} [Field K] (m : ℕ) (y z : K) (hy : y ≠ 0) (hz : z ≠ 0)
  (r : Fin m → K)

@[simp] theorem fin_cases_one {α : Sort*} (a : α) (f : Fin (m + 1) → α) :
    Fin.cases a f (1 : Fin (m + 2)) = f 0 := rfl

def frameEquiv (hy : y ≠ 0) (hz : z ≠ 0) :
    (Fin (m + 2) → K) ≃ₗ[K] (Fin (m + 2) → K) where
  toFun c := Fin.cases (y * c 0)
    (Fin.cases (z * c 1) (fun i => c i.succ.succ - r i * c 0 + c 1))
  invFun t := Fin.cases (t 0 / y)
    (Fin.cases (t 1 / z) (fun i => t i.succ.succ + r i * (t 0 / y) - t 1 / z))
  left_inv c := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [hy]
    · refine Fin.cases ?_ (fun k => ?_) j
      · simp [hz]
      · simp [hy, hz]; ring
  right_inv t := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cases_zero]
      field_simp
    · refine Fin.cases ?_ (fun k => ?_) j
      · simp only [Fin.cases_succ, fin_cases_one, Fin.cases_zero]
        field_simp
        rw [Fin.succ_zero_eq_one]
      · simp only [Fin.cases_succ, fin_cases_one, Fin.cases_zero]
        ring
  map_add' c d := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [mul_add]
    · refine Fin.cases ?_ (fun k => ?_) j
      · simp [mul_add]
      · simp only [Pi.add_apply, Fin.cases_succ, mul_add]
        ring
  map_smul' a c := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [mul_left_comm]
    · refine Fin.cases ?_ (fun k => ?_) j
      · simp [mul_left_comm]
      · simp only [Pi.smul_apply, Fin.cases_succ, smul_eq_mul, RingHom.id_apply]
        ring

def frameBasis : Basis (Fin (m + 2)) K (Fin (m + 2) → K) :=
  (Pi.basisFun K _).map (frameEquiv m y z r hy hz)

@[simp] theorem frameBasis_repr_aux (t : Fin (m + 2) → K) (i : Fin m) :
    (frameBasis m y z hy hz r).repr t i.succ.succ =
      t i.succ.succ + r i * (t 0 / y) - t 1 / z := by
  change (Pi.basisFun K _).repr ((frameEquiv m y z r hy hz).symm t) _ = _
  rw [Pi.basisFun_repr]
  rfl

@[simp] theorem frameBasis_aux (i : Fin m) :
    frameBasis m y z hy hz r i.succ.succ = Pi.basisFun K _ i.succ.succ := by
  have hone : (1 : Fin (m + 2)) ≠ i.succ.succ := by
    rw [← Fin.succ_zero_eq_one]
    exact fun h => Fin.succ_ne_zero i (Fin.succ_injective _ h).symm
  ext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [frameBasis, frameEquiv, Pi.basisFun_apply]
  · refine Fin.cases ?_ (fun l => ?_) k
    · simp [frameBasis, frameEquiv, Pi.basisFun_apply, Pi.single_apply, hone]
    · simp [frameBasis, frameEquiv, Pi.basisFun_apply, Pi.single_apply, hone]

@[simp] theorem frameBasis_zero_zero : frameBasis m y z hy hz r 0 0 = y := by
  simp [frameBasis, frameEquiv, Pi.basisFun_apply]

@[simp] theorem frameBasis_zero_one : frameBasis m y z hy hz r 0 1 = 0 := by
  simp [frameBasis, frameEquiv, Pi.basisFun_apply]

@[simp] theorem frameBasis_zero_aux (i : Fin m) :
    frameBasis m y z hy hz r 0 i.succ.succ = -r i := by
  simp [frameBasis, frameEquiv, Pi.basisFun_apply]

@[simp] theorem frameBasis_one_zero : frameBasis m y z hy hz r 1 0 = 0 := by
  simp [frameBasis, frameEquiv, Pi.basisFun_apply, Pi.single_apply]

@[simp] theorem frameBasis_one_one : frameBasis m y z hy hz r 1 1 = z := by
  simp [frameBasis, frameEquiv, Pi.basisFun_apply, Pi.single_apply]

@[simp] theorem frameBasis_one_aux (i : Fin m) :
    frameBasis m y z hy hz r 1 i.succ.succ = 1 := by
  have hne : i.succ.succ ≠ (1 : Fin (m + 2)) := by
    rw [← Fin.succ_zero_eq_one]
    exact fun h => Fin.succ_ne_zero i (Fin.succ_injective _ h)
  simp [frameBasis, frameEquiv, Pi.basisFun_apply, Pi.single_apply, hne]

variable {V : Type*} [AddCommGroup V] [Module K V]

/-- The largest nontangent auxiliary index is mandatory even with TWO
exceptional base indices. No relation between their two normal images is assumed. -/
theorem largest_aux_mandatory
    (u v : Fin (m + 2) → V) (hu : Submodule.span K (Set.range u) = ⊤)
    (hvu : ∀ i, 2 ≤ i.val → v i = u i)
    (hexclude : ∀ A B : Finset (Fin (m + 2)),
      IsNormalBasis (K := K) u A → IsNormalBasis (K := K) v B →
      ∀ i, 2 ≤ i.val → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) → False)
    (i : Fin (m + 2)) (hi2 : 2 ≤ i.val) (hi : u i ≠ 0)
    (hlarge : ∀ j, i < j → u j = 0)
    (B : Finset (Fin (m + 2))) (hB : IsNormalBasis (K := K) v B) : i ∈ B := by
  classical
  obtain ⟨A, hiA, hA⟩ := exists_normalBasis_containing u hu i hi
  by_contra hiB
  apply hexclude A B hA hB i hi2 hiA hiB
  intro j hj
  have hj2 : 2 ≤ j.val := by have := Fin.lt_def.mp hj; omega
  have hjA : j ∉ A := fun h => hA.ne_zero h (hlarge j hj)
  have hjB : j ∉ B := fun h => hB.ne_zero h ((hvu j hj2).trans (hlarge j hj))
  simp only [hjA, hjB]

/-- Mandatory normal direction gives the precise signed two-base differential
relation, not the single-base relation from the original frame. -/
theorem mandatory_relation (q : (Fin (m + 2) → K) →ₗ[K] V)
    (hq : Function.Surjective q) (i : Fin m)
    (hi : ∀ A, IsNormalBasis (K := K)
      (fun j => q (frameBasis m y z hy hz r j)) A → i.succ.succ ∈ A)
    (t : Fin (m + 2) → K) (ht : q t = 0) :
    t i.succ.succ + r i * (t 0 / y) - t 1 / z = 0 := by
  have h := mandatory_coordinate_eq_zero (frameBasis m y z hy hz r) q
    (span_mapped_basis_eq_top _ q hq) i.succ.succ hi t ht
  simpa only [frameBasis_repr_aux] using h

/-- Either all auxiliary coordinate directions are tangent, or one of the
two-base logarithmic differential relations holds on the entire tangent space. -/
theorem normal_basis_dichotomy
    (q : (Fin (m + 2) → K) →ₗ[K] V) (hq : Function.Surjective q)
    (hexclude : ∀ A B : Finset (Fin (m + 2)),
      IsNormalBasis (K := K) (fun j => q (Pi.basisFun K _ j)) A →
      IsNormalBasis (K := K) (fun j => q (frameBasis m y z hy hz r j)) B →
      ∀ i, 2 ≤ i.val → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) → False) :
    (∀ i : Fin m, q (Pi.basisFun K _ i.succ.succ) = 0) ∨
      ∃ i : Fin m, ∀ t, q t = 0 →
        t i.succ.succ + r i * (t 0 / y) - t 1 / z = 0 := by
  classical
  let b := Pi.basisFun K (Fin (m + 2))
  let S := Finset.univ.filter (fun i : Fin (m + 2) => 2 ≤ i.val ∧ q (b i) ≠ 0)
  by_cases hS : S.Nonempty
  · let i := S.max' hS
    have hiS : i ∈ S := Finset.max'_mem _ _
    have hi := (Finset.mem_filter.mp hiS).2
    have hlarge : ∀ j, i < j → q (b j) = 0 := by
      intro j hj
      by_contra hjq
      have hj2 : 2 ≤ j.val := by have := Fin.lt_def.mp hj; omega
      have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj2, hjq⟩
      exact (not_lt_of_ge (Finset.le_max' _ _ hjS)) hj
    have hvu : ∀ j : Fin (m + 2), 2 ≤ j.val →
        q (frameBasis m y z hy hz r j) = q (b j) := by
      intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · intro h; simp only [Fin.val_zero] at h; omega
      · refine Fin.cases ?_ (fun l _ => ?_) k
        · intro h; simp only [Fin.val_succ, Fin.val_zero] at h; omega
        · rw [frameBasis_aux]
    have hmand : ∀ B, IsNormalBasis (K := K)
        (fun j => q (frameBasis m y z hy hz r j)) B → i ∈ B :=
      largest_aux_mandatory m (fun j => q (b j))
        (fun j => q (frameBasis m y z hy hz r j))
        (span_mapped_basis_eq_top b q hq) hvu hexclude i hi.1 hi.2 hlarge
    right
    rcases Fin.eq_zero_or_eq_succ i with hi0 | ⟨j, hj⟩
    · have h := hi.1; rw [hi0] at h; simp at h
    · rcases Fin.eq_zero_or_eq_succ j with hj0 | ⟨k, hk⟩
      · have h := hi.1; rw [hj, hj0] at h; simp at h
      · refine ⟨k, ?_⟩
        intro t ht
        apply mandatory_relation m y z hy hz r q hq k ?_ t ht
        intro B hB
        simpa only [hj, hk] using hmand B hB
  · left
    intro i
    by_contra hi
    apply hS
    exact ⟨i.succ.succ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp, hi⟩⟩

section Differential
variable {C E : Type*} [Field C] [Field E] [Algebra C E]

/-- Transfer the actual two-base tangent relation to universal differentials. -/
theorem differential_of_tangent {m : ℕ}
    (φ : MvPolynomial (Fin (m + 2)) C →ₐ[C] E)
    (Q : Ideal (MvPolynomial (Fin (m + 2)) C)) (hQ : ∀ p ∈ Q, φ p = 0)
    (i : Fin m) (r : E)
    (h : ∀ t ∈ polynomialTangent φ Q,
      t i.succ.succ + r * (t 0 / φ (MvPolynomial.X 0)) -
        t 1 / φ (MvPolynomial.X 1) = 0) :
    KaehlerDifferential.D C E (φ (MvPolynomial.X i.succ.succ)) +
      (r / φ (MvPolynomial.X 0)) • KaehlerDifferential.D C E (φ (MvPolynomial.X 0)) -
      (φ (MvPolynomial.X 1))⁻¹ • KaehlerDifferential.D C E (φ (MvPolynomial.X 1)) = 0 := by
  apply (Module.forall_dual_apply_eq_zero_iff E _).mp
  intro l
  let d : Derivation C E E := l.compDer (KaehlerDifferential.D C E)
  have hd := h (fun j => d (φ (MvPolynomial.X j)))
    (derivation_mem_polynomialTangent φ Q hQ d)
  change l (KaehlerDifferential.D C E (φ (MvPolynomial.X i.succ.succ))) +
    r * (l (KaehlerDifferential.D C E (φ (MvPolynomial.X 0))) /
      φ (MvPolynomial.X 0)) -
    l (KaehlerDifferential.D C E (φ (MvPolynomial.X 1))) /
      φ (MvPolynomial.X 1) = 0 at hd
  simpa only [map_add, map_sub, map_smul, smul_eq_mul, div_eq_mul_inv,
    mul_assoc, mul_left_comm, mul_comm] using hd

end Differential

#print axioms normal_basis_dichotomy
#print axioms differential_of_tangent

end LogarithmExtension.LogRatio.TwoBaseFrame

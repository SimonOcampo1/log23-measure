import OAI.NumberTheory.PiExponent.Jets.DifferentialConstant
import Mathlib

/-!
# Algebraic rigidity of the two-base logarithmic relation

The relation dX + (p/q)dY/Y - dZ/Z = 0 implies that both X and
Z^q/Y^p are constant in a finite-type function field over an algebraically
closed characteristic-zero field. This discharges the exact-versus-logarithmic
differential step of the proposed ratio argument, with its hypotheses visible.
It does not establish the interpolation theorem or an irrationality bound.
-/

noncomputable section
namespace LogarithmExtension.LogRatio.TorusRigidity

open OAI.PiExponent KaehlerDifferential

variable {C E : Type*} [Field C] [Field E] [Algebra C E]

theorem logarithmic_zpow (d : Derivation C E E) (u : E) (hu : u ≠ 0) (n : ℤ) :
    d (u ^ n) / u ^ n = (n : E) * (d u / u) := by
  rw [d.leibniz_zpow]
  simp only [zsmul_eq_mul, smul_eq_mul, zpow_sub₀ hu, zpow_one]
  field_simp

theorem logarithmic_character (d : Derivation C E E)
    (y z : E) (hy : y ≠ 0) (hz : z ≠ 0) (p q : ℤ) :
    d (z ^ q / y ^ p) / (z ^ q / y ^ p) =
      (q : E) * (d z / z) - (p : E) * (d y / y) := by
  have hyp := zpow_ne_zero p hy
  have hzq := zpow_ne_zero q hz
  calc
    _ = d (z ^ q) / z ^ q - d (y ^ p) / y ^ p := by
      rw [d.leibniz_div]
      simp only [smul_eq_mul]
      field_simp
    _ = _ := by rw [logarithmic_zpow d z hz q, logarithmic_zpow d y hy p]

variable [CharZero C] [CharZero E] [IsAlgClosed C] [Algebra.EssFiniteType C E]

/-- The rational slope has a nonzero denominator; negative integer numerators
are allowed. Both constants follow, not only the multiplicative character. -/
theorem constants_of_relation (x y z : E) (hy : y ≠ 0) (hz : z ≠ 0)
    (p q : ℤ) (hq : q ≠ 0)
    (h : D C E x + ((p : E) / (q : E) / y) • D C E y - z⁻¹ • D C E z = 0) :
    (∃ a : C, algebraMap C E a = z ^ q / y ^ p) ∧
      ∃ b : C, algebraMap C E b = x := by
  have hqE : (q : E) ≠ 0 := by exact_mod_cast hq
  have hd : D C E ((q : E) * x) = (z ^ q / y ^ p)⁻¹ • D C E (z ^ q / y ^ p) := by
    apply sub_eq_zero.mp
    apply (Module.forall_dual_apply_eq_zero_iff E _).mp
    intro l
    let d : Derivation C E E := l.compDer (D C E)
    have ht := congrArg l h
    simp only [map_add, map_sub, map_smul, map_zero, smul_eq_mul] at ht
    change d x + ((p : E) / (q : E) / y) * d y - z⁻¹ * d z = 0 at ht
    have hc := logarithmic_character d y z hy hz p q
    change l (D C E ((q : E) * x) -
      (z ^ q / y ^ p)⁻¹ • D C E (z ^ q / y ^ p)) = 0
    simp only [map_sub, map_smul, smul_eq_mul]
    change d ((q : E) * x) - (z ^ q / y ^ p)⁻¹ * d (z ^ q / y ^ p) = 0
    rw [d.leibniz]
    simp only [Derivation.map_intCast, smul_eq_mul, mul_zero, add_zero]
    have hc' : (z ^ q / y ^ p)⁻¹ * d (z ^ q / y ^ p) =
        (q : E) * (d z / z) - (p : E) * (d y / y) := by
      simpa only [div_eq_mul_inv, mul_comm] using hc
    rw [hc']
    field_simp at ht ⊢
    linear_combination ht
  obtain ⟨a, ha⟩ := constant_of_logarithmic_differential ((q : E) * x)
    (z ^ q / y ^ p) hd
  refine ⟨⟨a, ha⟩, ?_⟩
  have hchar : D C E (z ^ q / y ^ p) = 0 := by rw [← ha]; simp
  rw [hchar, smul_zero] at hd
  have hx : D C E x = 0 := by
    simpa only [Derivation.leibniz, Derivation.map_intCast, smul_zero,
      add_zero, smul_eq_zero, hqE, false_or] using hd
  exact constant_of_differential_eq_zero x hx

#print axioms constants_of_relation

end LogarithmExtension.LogRatio.TorusRigidity

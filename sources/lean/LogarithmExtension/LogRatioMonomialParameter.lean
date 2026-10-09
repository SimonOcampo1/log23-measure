import Mathlib

/-! A primitive rational character admits a monomial parameter. This is the
algebraic source of the q-fold degree gain in the two-base curve argument. -/

namespace LogarithmExtension.LogRatio.MonomialParameter

theorem bezout_parameter_group {G : Type*} [CommGroup G]
    (y z c : G) (p q a b : ℤ) (hbez : q*a + p*b = 1)
    (hrel : z^q = c * y^p) :
    y = c^(-b) * (y^a * z^b)^q ∧ z = c^a * (y^a * z^b)^p := by
  have hq : (y^a * z^b)^q = c^b * y := by
    calc
      _ = (y^q)^a * (z^q)^b := by
        simp only [mul_zpow, ← zpow_mul, mul_comm a q, mul_comm b q]
      _ = (y^q)^a * (c * y^p)^b := by rw [hrel]
      _ = c^b * y^(q*a + p*b) := by
        simp only [mul_zpow, zpow_add, zpow_mul]
        exact mul_left_comm _ _ _
      _ = c^b * y := by rw [hbez, zpow_one]
  have hp : c^a * (y^a * z^b)^p = z := by
    calc
      _ = (c * y^p)^a * (z^p)^b := by
        simp only [mul_zpow, ← zpow_mul, mul_comm a p, mul_comm b p]
        ac_rfl
      _ = (z^q)^a * (z^p)^b := by rw [← hrel]
      _ = z^(q*a + p*b) := by rw [zpow_add, zpow_mul, zpow_mul]
      _ = z := by rw [hbez, zpow_one]
  refine ⟨?_, hp.symm⟩
  rw [hq, ← mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, one_mul]

def parameter {E : Type*} [Field E] (y z : E) (p q : ℕ) : E :=
  y^(Nat.gcdA q p) * z^(Nat.gcdB q p)

theorem parameter_ne_zero {E : Type*} [Field E] (y z : E)
    (hy : y ≠ 0) (hz : z ≠ 0) (p q : ℕ) : parameter y z p q ≠ 0 :=
  mul_ne_zero (zpow_ne_zero _ hy) (zpow_ne_zero _ hz)

theorem parameter_eqs {C E : Type*} [Field C] [Field E] [Algebra C E]
    (y z : E) (hy : y ≠ 0) (hz : z ≠ 0)
    (c : C) (hc : c ≠ 0) (p q : ℕ) (hcop : Nat.Coprime q p)
    (hrel : z^q = algebraMap C E c * y^p) :
    y = algebraMap C E (c^(-Nat.gcdB q p)) * (parameter y z p q)^q ∧
      z = algebraMap C E (c^(Nat.gcdA q p)) * (parameter y z p q)^p := by
  let a := Nat.gcdA q p
  let b := Nat.gcdB q p
  have hbez : (q : ℤ)*a + (p : ℤ)*b = 1 := by
    simpa only [a, b, hcop.gcd_eq_one, Nat.cast_one] using (Nat.gcd_eq_gcd_ab q p).symm
  let yu := Units.mk0 y hy
  let zu := Units.mk0 z hz
  let cu := Units.mk0 (algebraMap C E c)
    ((map_ne_zero_iff _ (algebraMap C E).injective).mpr hc)
  let tu := yu^a * zu^b
  have hr : zu^(q : ℤ) = cu * yu^(p : ℤ) := by
    apply Units.ext
    simpa only [yu, zu, cu, Units.val_zpow_eq_zpow_val, Units.val_mul,
      Units.val_mk0, zpow_natCast, Units.val_pow_eq_pow_val] using hrel
  obtain ⟨hY, hZ⟩ := bezout_parameter_group yu zu cu (p : ℤ) (q : ℤ) a b hbez hr
  refine ⟨?_, ?_⟩
  · have h := congrArg (fun u : Eˣ => (u : E)) hY
    simpa only [yu, cu, Units.val_mk0, Units.val_mul, Units.val_zpow_eq_zpow_val,
      zpow_natCast, map_zpow₀, tu, Units.val_pow_eq_pow_val, parameter,
      Units.val_zpow_eq_zpow_val, Units.val_mk0, zu, a, b] using h
  · have h := congrArg (fun u : Eˣ => (u : E)) hZ
    simpa only [zu, cu, Units.val_mk0, Units.val_mul, Units.val_zpow_eq_zpow_val,
      zpow_natCast, map_zpow₀, tu, Units.val_pow_eq_pow_val, parameter,
      Units.val_zpow_eq_zpow_val, Units.val_mk0, yu, a, b] using h

theorem exists_monomial_parameter {C E : Type*} [Field C] [Field E] [Algebra C E]
    (y z : E) (hy : y ≠ 0) (hz : z ≠ 0)
    (c : C) (hc : c ≠ 0) (p q : ℕ) (hcop : Nat.Coprime q p)
    (hrel : z^q = algebraMap C E c * y^p) :
    ∃ (T : E) (d e : C), T ≠ 0 ∧ d ≠ 0 ∧ e ≠ 0 ∧
      y = algebraMap C E d * T^q ∧ z = algebraMap C E e * T^p :=
  ⟨parameter y z p q, c^(-Nat.gcdB q p), c^(Nat.gcdA q p),
    parameter_ne_zero y z hy hz p q, zpow_ne_zero _ hc, zpow_ne_zero _ hc,
    parameter_eqs y z hy hz c hc p q hcop hrel⟩

#print axioms exists_monomial_parameter

end LogarithmExtension.LogRatio.MonomialParameter

import LogarithmExtension.Target
import OAI.NumberTheory.PiExponent.Approximation.Exponent

/-!
# From an eventual approximation bound to the exact exponent

This file proves a generic endpoint reduction, not the logarithm-specific
approximation bound. It reuses the same definition of irrationality exponent
as the pinned OpenAI development. The explicit hypotheses are essential.
-/

noncomputable section
namespace LogarithmExtension

/-- Quantification over all integer numerator/denominator pairs makes even a
finite eventual lower-bound exponent incompatible with rationality. -/
theorem irrational_of_eventualLowerBound {x bound : ℝ}
    (h : EventualLowerBound x bound) : Irrational x := by
  rintro ⟨r, rfl⟩
  obtain ⟨Q, hQ, happrox⟩ := h (bound + 1) (by linarith)
  have hQpos : 0 < Q := by omega
  have hq : Q ≤ r.den * Q := by
    simpa using Nat.mul_le_mul_right Q r.pos
  have hQreal : (Q : ℝ) ≠ 0 := by positivity
  have hden : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have heq : ((r.num * (Q : ℤ) : ℤ) : ℝ) / ((r.den * Q : ℕ) : ℝ) = r := by
    push_cast
    rw [Rat.cast_def]
    field_simp
  have hb := happrox (r.num * (Q : ℤ)) (r.den * Q) hq
  rw [heq, sub_self, abs_zero] at hb
  exact (not_le_of_gt (Real.rpow_pos_of_pos (by positivity) _)) hb

/-- The package's exponent-two bound is definitionally the upstream one. -/
theorem eventualLowerBound_two_iff {x : ℝ} :
    EventualLowerBound x 2 ↔ OAI.PiExponent.EventualLowerBound x := Iff.rfl

/-- Both irrationality and the exact exponent follow once the actual eventual
lower bound has been established. No irrationality hypothesis is assumed. -/
theorem irrationalityExponent_eq_two {x : ℝ}
    (h : EventualLowerBound x 2) :
    OAI.PiExponent.irrationalityExponent x = 2 :=
  OAI.PiExponent.irrationalityExponent_eq_two_of_eventualLowerBound
    (irrational_of_eventualLowerBound h) h

theorem logThreeTarget_iff :
    LogThreeTarget ↔ EventualLowerBound (Real.log 3) 2 :=
  ⟨And.right, fun h => ⟨irrational_of_eventualLowerBound h, h⟩⟩

theorem rationalLogarithmTarget_iff :
    RationalLogarithmTarget ↔
      ∀ a b : ℕ, 0 < a → 0 < b → a ≠ b →
        EventualLowerBound (Real.log ((a : ℝ) / (b : ℝ))) 2 := by
  constructor
  · intro h a b ha hb hab
    exact (h a b ha hb hab).2
  · intro h a b ha hb hab
    exact ⟨irrational_of_eventualLowerBound (h a b ha hb hab), h a b ha hb hab⟩

theorem logThreeTarget_of_rationalLogarithmTarget
    (h : RationalLogarithmTarget) : LogThreeTarget := by
  simpa [LogThreeTarget] using h 3 1 (by omega) (by omega) (by omega)

theorem logThree_exponent_of_target (h : LogThreeTarget) :
    OAI.PiExponent.irrationalityExponent (Real.log 3) = 2 :=
  irrationalityExponent_eq_two h.2

#print axioms irrational_of_eventualLowerBound
#print axioms irrationalityExponent_eq_two

end LogarithmExtension

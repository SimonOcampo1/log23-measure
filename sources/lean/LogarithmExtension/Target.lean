import LogarithmExtension.Basic

/-!
# Explicit endpoint propositions

These are proposition definitions, not logical axioms. LogThreeMain.lean
proves LogThreeTarget, RationalLogMain.lean proves RationalLogarithmTarget,
and AlgebraicLogMain.lean proves AlgebraicLogarithmTarget.
LogarithmicRatioTarget remains unproved in this package.
-/
namespace LogarithmExtension

/-- Eventual lower bound on approximation by every integer numerator and
sufficiently large natural denominator. Real.rpow is the exponentiation used. -/
def EventualLowerBound (x bound : ℝ) : Prop :=
  ∀ ν : ℝ, bound < ν → ∃ Q : ℕ, 2 ≤ Q ∧
    ∀ p : ℤ, ∀ q : ℕ, Q ≤ q →
      (q : ℝ) ^ (-ν) ≤ |x - (p : ℝ) / (q : ℝ)|

/-- The log-three result, proved by logThree_target in LogThreeMain.lean.
Together these statements express the optimal exponent via Dirichlet's theorem. -/
def LogThreeTarget : Prop :=
  Irrational (Real.log 3) ∧ EventualLowerBound (Real.log 3) 2

/-- The rational-base conclusion, proved by rationalLogarithm_target in RationalLogMain.lean. -/
def RationalLogarithmTarget : Prop :=
  ∀ a b : ℕ, 0 < a → 0 < b → a ≠ b →
    Irrational (Real.log ((a : ℝ) / (b : ℝ))) ∧
    EventualLowerBound (Real.log ((a : ℝ) / (b : ℝ))) 2

/-- The degree bound for positive real algebraic bases, proved in AlgebraicLogMain.lean. -/
def AlgebraicLogarithmTarget : Prop :=
  ∀ α : ℝ, IsAlgebraic ℚ α → 0 < α → α ≠ 1 →
    Irrational (Real.log α) ∧
      EventualLowerBound (Real.log α) (2 * ((minpoly ℚ α).natDegree : ℝ))

/-- The Collatz-relevant ratio target is a different proposition. NOT PROVED. -/
def LogarithmicRatioTarget : Prop :=
  EventualLowerBound (Real.log 3 / Real.log 2) (19 / 8)

end LogarithmExtension

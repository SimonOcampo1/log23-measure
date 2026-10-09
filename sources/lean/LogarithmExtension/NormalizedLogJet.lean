import OAI.NumberTheory.PiExponent.Jets.FormalAuxiliaryJet

/-!
# Logarithmic jets with a nonunit exponential centre

The original PiExponent formal jet has Y = 1 + t. Here Y = y * (1 + t),
with arbitrary y. The same differential frame and weighted loss remain valid.
The auxiliary polynomial is constructed by the upstream dimension theorem;
its existence is not an additional hypothesis.
-/

noncomputable section
namespace LogarithmExtension.NormalizedLogJet

open OAI OAI.PiExponent OAI.PiExponentApprox MvPowerSeries
open OAI.PiExponent.FormalJetDerivatives
open OAI.PiExponent.FormalLogJet (formalLog)
open Filter Topology
open scoped BigOperators

def formalJet {m : ℕ} (y : ℂ) (c : Fin m → ℂ) :
    FramePolynomial m →ₐ[ℂ] MvPowerSeries (Fin (m+1)) ℂ :=
  MvPolynomial.aeval (Fin.cases (C y * (1 + X 0))
    (fun i => C (c i) + X i.succ + formalLog m))

@[simp] theorem formalJet_Y {m : ℕ} (y : ℂ) (c : Fin m → ℂ) :
    formalJet y c (MvPolynomial.X (0 : Fin (m+1))) = C y * (1 + X 0) := by
  simp [formalJet]

@[simp] theorem formalJet_X {m : ℕ} (y : ℂ) (c : Fin m → ℂ) (i : Fin m) :
    formalJet y c (MvPolynomial.X i.succ) = C (c i) + X i.succ + formalLog m := by
  simp [formalJet]

@[simp] theorem formalJet_one {m : ℕ} (c : Fin m → ℂ) :
    formalJet 1 c = OAI.PiExponent.FormalLogJet.formalJet c := by
  simp only [formalJet, map_one, one_mul, FormalLogJet.formalJet]

theorem formalJet_frame_X {m : ℕ} (y : ℂ) (c : Fin m → ℂ)
    (i j : Fin (m+1)) :
    formalJet y c (polynomialFrame m i (MvPolynomial.X j)) =
      jetFrame m i (formalJet y c (MvPolynomial.X j)) := by
  classical
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero =>
      simp [polynomialFrame_zero, logarithmicDerivation_apply,
        MvPolynomial.pderiv_X, mul_comm]
    | succ j =>
      simp [polynomialFrame_zero, logarithmicDerivation_apply,
        MvPolynomial.pderiv_X, Pi.single_apply,
        MvPowerSeries.pderiv_X_of_ne,
        FormalLogJet.one_add_X_mul_pderiv_formalLog]
  | succ i =>
    rw [polynomialFrame_pos m i.succ (Fin.succ_ne_zero i),
      jetFrame_pos m i.succ (Fin.succ_ne_zero i)]
    cases j using Fin.cases with
    | zero => simp [MvPowerSeries.pderiv_X_of_ne (Ne.symm (Fin.succ_ne_zero i))]
    | succ j =>
      by_cases hij : i = j
      · subst j; simp
      · simp [MvPowerSeries.pderiv_X_of_ne, Ne.symm hij]

theorem formalJet_polynomialFrame {m : ℕ} (y : ℂ) (c : Fin m → ℂ)
    (i : Fin (m+1)) (p : FramePolynomial m) :
    formalJet y c (polynomialFrame m i p) = jetFrame m i (formalJet y c p) :=
  FormalLogJet.derivation_map_of_X (formalJet y c) (polynomialFrame m i)
    (jetFrame m i) (formalJet_frame_X y c i) p

theorem formalJet_polynomialFrameWord {m : ℕ} (y : ℂ) (c : Fin m → ℂ)
    (word : List (Fin (m+1))) (p : FramePolynomial m) :
    formalJet y c (polynomialFrameWord m word p) =
      jetFrameWord m word (formalJet y c p) := by
  induction word with
  | nil => rfl
  | cons i word ih =>
    rw [polynomialFrameWord_cons, formalJet_polynomialFrame, ih]
    rfl

theorem formalJet_polynomialFrameWord_vanishing {m : ℕ}
    (y : ℂ) (c : Fin m → ℂ) (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (H : ℚ) (p : FramePolynomial m)
    (hp : formalJet y c p ∈ JetGeometry.rationalWeightedIdeal v hv H)
    (word : List (Fin (m+1))) :
    formalJet y c (polynomialFrameWord m word p) ∈
      JetGeometry.rationalWeightedIdeal v hv (H - (word.map v).sum) := by
  rw [formalJet_polynomialFrameWord]
  exact jetFrameWord_mem_rationalWeightedIdeal v hv H (formalJet y c p) hp word

def formalJetEvaluation {m : ℕ} (K : ℕ)
    (V : Fin (m+1) → ℝ) (H : ℝ) (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ) :
    FramePolynomial m →ₗ[ℂ] ((Fin K × ↥(strictWeightedSimplex V H)) → ℂ) :=
  LinearMap.pi (fun ρ =>
    (MvPowerSeries.coeff (InterpolationMatrix.exponentVector ρ.2.val)).comp
      (formalJet (y ρ.1) (c ρ.1)).toLinearMap)

theorem eventually_exists_auxiliaryPolynomial {m : ℕ}
    (W V : Fin (m+1) → ℚ) (hW : ∀ i, 0 < W i) (hV : ∀ i, 0 < V i)
    (K : ℕ) {a : ℝ} (ha : 0 < a)
    (hvol : (K : ℝ) * a^(m+1) * (∏ i, (W i : ℝ)) / (∏ i, (V i : ℝ)) < 1)
    (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ) :
    ∀ᶠ N : ℝ in atTop, ∃ p : FramePolynomial m, p ≠ 0 ∧
      HasWeightedDegreeLE (fun i => (W i : ℝ)) N p ∧
      ∀ j d, Finsupp.weight (fun i => (V i : ℝ)) d < a*N →
        MvPowerSeries.coeff d (formalJet (y j) (c j) p) = 0 := by
  filter_upwards [OAI.PiExponent.eventually_exists_auxiliaryPolynomial W V hW hV K ha hvol]
    with N hN
  obtain ⟨p, hp, hw, he⟩ := hN (formalJetEvaluation K (fun i => (V i : ℝ)) (a*N) y c)
  refine ⟨p, hp, hw, ?_⟩
  intro j d hd
  have hmem : (fun i => d i) ∈ strictWeightedSimplex (fun i => (V i : ℝ)) (a*N) := by
    apply (mem_strictWeightedSimplex (fun i => by exact_mod_cast hV i)).mpr
    simpa [Finsupp.weight_eq_sum, nsmul_eq_mul, mul_comm] using hd
  have hh := congrFun he (j, ⟨(fun i => d i), hmem⟩)
  have hd' : InterpolationMatrix.exponentVector (fun i => d i) = d := by ext i; rfl
  simpa [formalJetEvaluation, hd'] using hh

theorem eventually_exists_auxiliaryPolynomial_nat {m : ℕ}
    (W V : Fin (m+1) → ℚ) (hW : ∀ i, 0 < W i) (hV : ∀ i, 0 < V i)
    (K : ℕ) {a : ℚ} (ha : 0 < a)
    (hvol : (K : ℝ) * (a : ℝ)^(m+1) * (∏ i, (W i : ℝ)) / (∏ i, (V i : ℝ)) < 1)
    (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ) :
    ∀ᶠ N : ℕ in atTop, ∃ p : FramePolynomial m, p ≠ 0 ∧
      HasWeightedDegreeLE (fun i => (W i : ℝ)) N p ∧
      ∀ j, formalJet (y j) (c j) p ∈
        JetGeometry.rationalWeightedIdeal V (fun i => le_of_lt (hV i)) (a*N) := by
  have h := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_exists_auxiliaryPolynomial W V hW hV K
      (by exact_mod_cast ha) hvol y c)
  filter_upwards [h] with N hN
  obtain ⟨p, hp, hw, hv⟩ := hN
  refine ⟨p, hp, hw, ?_⟩
  intro j d hd
  apply hv j d
  have hcast : ((Finsupp.weight V d : ℚ) : ℝ) < (a : ℝ)*(N : ℝ) := by exact_mod_cast hd
  simpa [Finsupp.weight_eq_sum, nsmul_eq_mul] using hcast

#print axioms formalJet_polynomialFrameWord_vanishing
#print axioms eventually_exists_auxiliaryPolynomial_nat

end LogarithmExtension.NormalizedLogJet

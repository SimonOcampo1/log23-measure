import LogarithmExtension.CoordinateScaling
import OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial

/-!
# Algebraic jet ideals at nonunit exponential centres

These are concrete polynomial ideals, transported by an explicitly proved
coordinate automorphism. The support is the required centre, and powers of
the ideals kill the required formal coefficient packets.
-/

noncomputable section
namespace LogarithmExtension.NormalizedJetIdeal

open OAI OAI.PiExponent OAI.PiExponentApprox
open CoordinateScaling
open scoped BigOperators

variable {m : ℕ}

def center (y : ℂ) (c : Fin m → ℂ) : Fin (m+1) → ℂ := Fin.cases y c

def powerIdeal (y : ℂ) (c : Fin m → ℂ) (G : Fin m → Polynomial ℂ)
    (e : Fin (m+1) → ℕ) : Ideal (FramePolynomial m) :=
  (CompactJetPolynomial.powerIdeal c G e).comap (scaleY y).toRingHom

theorem eval_center_scaleY (y : ℂ) (c : Fin m → ℂ) :
    (MvPolynomial.aeval (CompactJetPolynomial.center c)).comp (scaleY y) =
      MvPolynomial.aeval (center y c) := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i using Fin.cases <;> simp [AlgHom.comp_apply, center, CompactJetPolynomial.center]

theorem pointIdeal_comap (y : ℂ) (c : Fin m → ℂ) :
    (WeightedBezout.pointIdeal (CompactJetPolynomial.center c)).comap (scaleY y).toRingHom =
      WeightedBezout.pointIdeal (center y c) := by
  ext P
  change MvPolynomial.aeval (CompactJetPolynomial.center c) (scaleY y P) = 0 ↔
    MvPolynomial.aeval (center y c) P = 0
  rw [← AlgHom.comp_apply, eval_center_scaleY]

theorem radical_powerIdeal (y : ℂ) (c : Fin m → ℂ) (G : Fin m → Polynomial ℂ)
    (hG : ∀ i, (G i).eval 0 = 0) (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) :
    (powerIdeal y c G e).radical = WeightedBezout.pointIdeal (center y c) := by
  rw [powerIdeal, ← Ideal.comap_radical, CompactJetPolynomial.radical_powerIdeal c G hG e he,
    pointIdeal_comap]

def centerPoint (y : ℂ) (c : Fin m → ℂ) : PrimeSpectrum (FramePolynomial m) :=
  ⟨WeightedBezout.pointIdeal (center y c), inferInstance⟩

theorem zeroLocus_powerIdeal (y : ℂ) (c : Fin m → ℂ) (G : Fin m → Polynomial ℂ)
    (hG : ∀ i, (G i).eval 0 = 0) (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) :
    PrimeSpectrum.zeroLocus (powerIdeal y c G e : Set _) = {centerPoint y c} := by
  rw [← PrimeSpectrum.zeroLocus_radical, radical_powerIdeal y c G hG e he]
  exact PrimeSpectrum.zeroLocus_eq_singleton _

theorem formalJet_mem_weighted_of_mem_pow (y : ℂ) (c : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m+1) → ℕ) (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ)
    (P : FramePolynomial m) (hP : P ∈ powerIdeal y c (CompactJetPolynomial.logPolynomials T) e ^ n) :
    NormalizedLogJet.formalJet y c P ∈ JetGeometry.rationalWeightedIdeal v hv (n*R) := by
  rw [← formalJet_scaleY]
  apply CompactJetPolynomial.formalJet_mem_weighted_of_mem_pow c T e v hv hT R he n
  exact Ideal.le_comap_pow (scaleY y).toRingHom n hP

theorem formalJet_packet_zero_of_mem_pow (y : ℂ) (c : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m+1) → ℕ) (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ)
    (P : FramePolynomial m) (hP : P ∈ powerIdeal y c (CompactJetPolynomial.logPolynomials T) e ^ n) :
    JetGeometry.rationalCoefficientPacket v (n*R) (NormalizedLogJet.formalJet y c P) =
      (fun _ => (0 : ℂ)) := by
  funext d
  exact formalJet_mem_weighted_of_mem_pow y c T e v hv hT R he n P hP d.val d.property

theorem formalJet_packet_surjective (y : ℂ) (hy : y ≠ 0) (c : Fin m → ℂ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ) :
    Function.Surjective (fun P : FramePolynomial m =>
      JetGeometry.rationalCoefficientPacket v H (NormalizedLogJet.formalJet y c P)) := by
  intro packet
  obtain ⟨P, hP⟩ := AlgebraicJetPackets.formalJet_packet_surjective c v hv H packet
  obtain ⟨Q, hQ⟩ := scaleY_surjective y hy P
  refine ⟨Q, ?_⟩
  dsimp only
  rw [← formalJet_scaleY, hQ]
  exact hP

def polynomialIdeal {J : Type*} [Fintype J] (y : J → ℂ) (c : J → Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) : Ideal (FramePolynomial m) :=
  ∏ j, powerIdeal (y j) (c j) (CompactJetPolynomial.logPolynomials T) e

theorem polynomialIdeal_pow_le {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (n : ℕ) (j : J) :
    polynomialIdeal y c T e ^ n ≤ powerIdeal (y j) (c j) (CompactJetPolynomial.logPolynomials T) e ^ n := by
  classical
  apply pow_le_pow_left'
  exact Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ j))

theorem formalJet_packet_zero_of_mem_polynomialIdeal_pow {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ)
    (P : FramePolynomial m) (hP : P ∈ polynomialIdeal y c T e ^ n) (j : J) :
    JetGeometry.rationalCoefficientPacket v (n*R) (NormalizedLogJet.formalJet (y j) (c j) P) =
      (fun _ => (0 : ℂ)) :=
  formalJet_packet_zero_of_mem_pow (y j) (c j) T e v hv hT R he n P
    (polynomialIdeal_pow_le y c T e n j hP)

#print axioms radical_powerIdeal
#print axioms formalJet_packet_surjective
#print axioms formalJet_packet_zero_of_mem_polynomialIdeal_pow

end LogarithmExtension.NormalizedJetIdeal

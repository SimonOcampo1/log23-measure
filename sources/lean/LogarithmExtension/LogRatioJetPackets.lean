import LogarithmExtension.LogRatioJetIdeal
import OAI.NumberTheory.PiExponent.Jets.JetPowerIdealCoprime
import OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientInterface

/-!
# Simultaneous two-base packets and the global-section interface

Distinct centers give coprime actual jet ideals. Chinese remaindering then
realizes arbitrary full logarithmic packets simultaneously, without a degree
bound. The last theorem transfers a global restriction theorem to these
packets. Establishing that restriction theorem and its degree bound remains
necessary; neither is assumed to have been proved by this module.

Adapted portions of the pinned OpenAI jet-packet interfaces and of the
one-base logarithm extension retain their Apache-2.0 attribution.
-/

noncomputable section
namespace LogarithmExtension.LogRatio.JetPackets

open OAI OAI.PiExponent PolynomialFrame AlgebraicJet
open scoped BigOperators

variable {m : ℕ}

theorem powerIdeal_pairwise_isCoprime {J : Type*}
    (cy cz : J → ℂ) (hcy : ∀ j, cy j ≠ 0) (hcz : ∀ j, cz j ≠ 0)
    (c : J → Fin m → ℂ) (r : Fin m → ℂ)
    (hcent : Function.Injective (fun j => center (cy j) (cz j) (c j)))
    (G : Fin m → Polynomial ℂ) (hG : ∀ i, (G i).eval 0 = 0)
    (e : Fin (m+2) → ℕ) (he : ∀ i, 0 < e i) :
    Pairwise (fun i j => IsCoprime (powerIdeal (cy i) (cz i) (c i) r G e)
      (powerIdeal (cy j) (cz j) (c j) r G e)) := by
  intro i j hij
  have hp : IsCoprime (WeightedBezout.pointIdeal (center (cy i) (cz i) (c i)))
      (WeightedBezout.pointIdeal (center (cy j) (cz j) (c j))) := by
    apply Ideal.isCoprime_of_isMaximal
    intro heq
    exact hij (hcent (JetPowerIdealCoprime.pointIdeal_injective heq))
  apply Ideal.isCoprime_iff_sup_eq.mpr
  apply Ideal.radical_eq_top.mp
  rw [Ideal.radical_sup, radical_powerIdeal (cy i) (cz i) (hcy i) (hcz i) (c i) r G hG e he,
    radical_powerIdeal (cy j) (cz j) (hcy j) (hcz j) (c j) r G hG e he,
    hp.sup_eq, Ideal.radical_top]

theorem formalJet_packet_eq_of_sub_mem_pow
    (cy cz : ℂ) (hcy : cy ≠ 0) (hcz : cz ≠ 0) (c r : Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+2) → ℕ)
    (v : Fin (m+2) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (hT0 : ∀ i, v i.succ.succ ≤ (T i : ℚ) * v 0)
    (hT1 : ∀ i, v i.succ.succ ≤ (T i : ℚ) * v 1)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ) (P Q : Poly m)
    (hPQ : P - Q ∈ powerIdeal cy cz c r (CompactJetPolynomial.logPolynomials T) e ^ n) :
    JetGeometry.rationalCoefficientPacket v (n*R) (FormalJet.formalJet cy cz c r P) =
      JetGeometry.rationalCoefficientPacket v (n*R) (FormalJet.formalJet cy cz c r Q) := by
  apply (FormalLogTruncation.rationalCoefficientPacket_eq_iff v hv (n*R) _ _).mpr
  simpa only [map_sub] using formalJet_mem_weighted_of_mem_pow cy cz hcy hcz c r T e
    v hv hT0 hT1 R he n (P-Q) hPQ

/-- Arbitrary simultaneous packets, with no weighted-degree assertion. -/
theorem formalJet_packets_surjective {J : Type*} [Fintype J]
    (cy cz : J → ℂ) (hcy : ∀ j, cy j ≠ 0) (hcz : ∀ j, cz j ≠ 0)
    (c : J → Fin m → ℂ) (r : Fin m → ℂ)
    (hcent : Function.Injective (fun j => center (cy j) (cz j) (c j)))
    (T : Fin m → ℕ) (e : Fin (m+2) → ℕ) (hepos : ∀ i, 0 < e i)
    (v : Fin (m+2) → ℚ) (hv : ∀ i, 0 < v i)
    (hT0 : ∀ i, v i.succ.succ ≤ (T i : ℚ) * v 0)
    (hT1 : ∀ i, v i.succ.succ ≤ (T i : ℚ) * v 1)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ) :
    Function.Surjective (fun P : Poly m => fun j =>
      JetGeometry.rationalCoefficientPacket v (n*R)
        (FormalJet.formalJet (cy j) (cz j) (c j) r P)) := by
  classical
  intro packets
  choose P hP using fun j => formalJet_packet_surjective (cy j) (cz j) (hcy j) (hcz j)
    (c j) r v hv (n*R) (packets j)
  have hcop : Pairwise (fun i j => IsCoprime
      (powerIdeal (cy i) (cz i) (c i) r (CompactJetPolynomial.logPolynomials T) e ^ n)
      (powerIdeal (cy j) (cz j) (c j) r (CompactJetPolynomial.logPolynomials T) e ^ n)) := by
    intro i j hij
    exact (powerIdeal_pairwise_isCoprime cy cz hcy hcz c r hcent _
      (CompactJetPolynomial.logPolynomials_eval_zero T) e hepos hij).pow
  obtain ⟨Q, hQ⟩ := Ideal.exists_forall_sub_mem_ideal hcop P
  refine ⟨Q, ?_⟩
  funext j
  exact (formalJet_packet_eq_of_sub_mem_pow (cy j) (cz j) (hcy j) (hcz j) (c j) r
    T e v (fun i => (hv i).le) hT0 hT1 R he n Q (P j) (hQ j)).trans (hP j)

theorem packets_surjective_of_polynomialIdeal_quotient {α J : Type*} [Fintype J]
    (cy cz : J → ℂ) (hcy : ∀ j, cy j ≠ 0) (hcz : ∀ j, cz j ≠ 0)
    (c : J → Fin m → ℂ) (r : Fin m → ℂ)
    (hcent : Function.Injective (fun j => center (cy j) (cz j) (c j)))
    (T : Fin m → ℕ) (e : Fin (m+2) → ℕ) (hepos : ∀ i, 0 < e i)
    (v : Fin (m+2) → ℚ) (hv : ∀ i, 0 < v i)
    (hT0 : ∀ i, v i.succ.succ ≤ (T i : ℚ) * v 0)
    (hT1 : ∀ i, v i.succ.succ ≤ (T i : ℚ) * v 1)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ)
    (f : α → Poly m)
    (hf : Function.Surjective (fun a =>
      Ideal.Quotient.mk (JetIdeal.polynomialIdeal cy cz c r T e ^ n) (f a))) :
    Function.Surjective (fun a j => JetGeometry.rationalCoefficientPacket v (n*R)
      (FormalJet.formalJet (cy j) (cz j) (c j) r (f a))) := by
  intro packets
  obtain ⟨P, hP⟩ := formalJet_packets_surjective cy cz hcy hcz c r hcent T e hepos
    v hv hT0 hT1 R he n packets
  obtain ⟨a, ha⟩ := hf (Ideal.Quotient.mk _ P)
  have hdiff : f a - P ∈ JetIdeal.polynomialIdeal cy cz c r T e ^ n :=
    Ideal.Quotient.eq.mp ha
  refine ⟨a, ?_⟩
  funext j
  exact (formalJet_packet_eq_of_sub_mem_pow (cy j) (cz j) (hcy j) (hcz j) (c j) r T e
    v (fun i => (hv i).le) hT0 hT1 R he n (f a) P
    (JetIdeal.polynomialIdeal_pow_le cy cz c r T e n j hdiff)).trans (congrFun hP j)

open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.IdealPullback
open AffineJetCoefficientInterface BlowupJetSurjectivity

/-- This interface assumes global restriction surjectivity explicitly.
The separate geometric ampleness argument must establish it. -/
theorem surjective_of_jetRestriction {X : Scheme} {J : Type} [Fintype J]
    (cy cz : J → ℂ) (hcy : ∀ j, cy j ≠ 0) (hcz : ∀ j, cz j ≠ 0)
    (c : J → Fin m → ℂ) (r : Fin m → ℂ)
    (hcent : Function.Injective (fun j => center (cy j) (cz j) (c j)))
    (T : Fin m → ℕ) (e : Fin (m+2) → ℕ) (hepos : ∀ i, 0 < e i)
    (v : Fin (m+2) → ℚ) (hv : ∀ i, 0 < v i)
    (hT0 : ∀ i, v i.succ.succ ≤ (T i : ℚ) * v 0)
    (hT1 : ∀ i, v i.succ.succ ≤ (T i : ℚ) * v 1)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ)
    (j : Spec (CommRingCat.of (Poly m)) ⟶ X) [IsOpenImmersion j]
    (I : X.IdealSheafData) (A : LineBundle X) (frame : Frame j A)
    (hI : I.comap j = specIdeal (JetIdeal.polynomialIdeal cy cz c r T e))
    (hs : ((I^n).support : Set X) ⊆ j.opensRange)
    (hjet : Function.Surjective (jetRestriction I A n)) :
    Function.Surjective (fun s : Sections A n => fun k =>
      JetGeometry.rationalCoefficientPacket v (n*R)
        (FormalJet.formalJet (cy k) (cz k) (c k) r (coefficient j A n frame s))) := by
  apply packets_surjective_of_polynomialIdeal_quotient cy cz hcy hcz c r hcent T e hepos
    v hv hT0 hT1 R he n (coefficient j A n frame)
  exact AffineJetPolynomial.polynomialQuotient_surjective_of_jetRestriction
    I A n j frame (JetIdeal.polynomialIdeal cy cz c r T e) hI hs hjet

#print axioms formalJet_packets_surjective
#print axioms surjective_of_jetRestriction

end LogarithmExtension.LogRatio.JetPackets

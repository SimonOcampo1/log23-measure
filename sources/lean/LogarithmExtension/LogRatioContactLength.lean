import LogarithmExtension.LogRatioAlgebraicJet
import LogarithmExtension.LogRatioPlaceContact
import OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal

/-!
# Two-base truncation invariance and actual local ideal colength

Both logarithmic tails are strictly above the contact threshold. Their
combination therefore leaves the minimum weighted order unchanged. This
identifies the concrete coordinate-power ideal with the branch contact
used by the proved two-base curve inequality.

The strict-order and ideal-length arguments adapt the pinned OpenAI
`FormalLogTailOrder`, `FormalBranchContact`, and `LogarithmicContactIdeal`
proofs (Apache-2.0). No ideal-length/contact equality is postulated.
-/

noncomputable section
namespace LogarithmExtension.LogRatio.ContactLength

open OAI.PiExponent PolynomialFrame
open BranchEvaluation FormalLogTruncation

variable {m : ℕ}

theorem order_strict_of_le (B : ℚ) (f g : PowerSeries ℂ)
    (hf : ∀ k : ℕ, f.order = (k : ℕ∞) → B < (k : ℚ)) (hfg : f.order ≤ g.order)
    (k : ℕ) (hk : g.order = (k : ℕ∞)) : B < (k : ℚ) := by
  have hle : f.order ≤ (k : ℕ∞) := hfg.trans hk.le
  have hn : f.order ≠ ⊤ := ne_top_of_le_ne_top (by simp) hle
  have he := ENat.natCast_toNat hn
  have hb := hf f.order.toNat he.symm
  have hnat : f.order.toNat ≤ k := by exact_mod_cast he.symm ▸ hle
  exact hb.trans_le (by exact_mod_cast hnat)

theorem order_add_strict (B : ℚ) (f g : PowerSeries ℂ)
    (hf : ∀ k : ℕ, f.order = (k : ℕ∞) → B < (k : ℚ))
    (hg : ∀ k : ℕ, g.order = (k : ℕ∞) → B < (k : ℚ))
    (k : ℕ) (hk : (f+g).order = (k : ℕ∞)) : B < (k : ℚ) := by
  have hmin := (PowerSeries.min_order_le_order_add f g).trans hk.le
  rcases min_le_iff.mp hmin with h | h
  · exact order_strict_of_le B f (f+g) hf (h.trans hk.ge) k hk
  · exact order_strict_of_le B g (f+g) hg (h.trans hk.ge) k hk

theorem order_sub_C_mul_strict (B : ℚ) (f g : PowerSeries ℂ) (r : ℂ)
    (hf : ∀ k : ℕ, f.order = (k : ℕ∞) → B < (k : ℚ))
    (hg : ∀ k : ℕ, g.order = (k : ℕ∞) → B < (k : ℚ))
    (k : ℕ) (hk : (f - PowerSeries.C r * g).order = (k : ℕ∞)) : B < (k : ℚ) := by
  rw [sub_eq_add_neg] at hk
  apply order_add_strict B f (-(PowerSeries.C r * g)) hf _ k hk
  apply order_strict_of_le B g (-(PowerSeries.C r * g)) hg
  rw [PowerSeries.order_neg]
  exact le_add_self.trans (PowerSeries.le_order_mul _ _)

/-- The one-variable tail estimate at any chosen base coordinate and any
target weight. In particular, the base series is allowed to be zero. -/
theorem composed_tail_strict
    (v : Fin (m+2) → ℚ) (hv : ∀ i, 0 < v i)
    (a : Fin (m+2) → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0)
    (ha : ∀ i, PowerSeries.constantCoeff (a i) = 0)
    (b i : Fin (m+2)) (T : ℕ) (hT : v i < (T : ℚ) * v b)
    (k : ℕ) (hk : PowerSeries.order (PowerSeries.subst (a b) (logTail T)) = (k : ℕ∞)) :
    BranchContact.contact v a hne * v i < (k : ℚ) := by
  have hTp : 0 < T := by
    by_contra h
    have hz : T = 0 := by omega
    rw [hz, Nat.cast_zero, zero_mul] at hT
    exact (not_lt_of_ge (hv i).le) hT
  have hb := FormalBranchContact.composed_logTail_order_ge T (a b) (ha b)
  rw [hk] at hb
  have hfinite : (a b).order ≠ ⊤ := by
    intro htop
    have hT0 : (T : ℕ∞) ≠ 0 := by exact_mod_cast hTp.ne'
    simp only [htop, ENat.mul_top hT0] at hb
    simp at hb
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfinite
  rw [← hn] at hb
  have hnat : T*n ≤ k := by exact_mod_cast hb
  have hc := BranchContact.contact_bound v hv a hne b n hn.symm
  have hmu := BranchContact.contact_pos v hv a hne ha
  calc
    BranchContact.contact v a hne * v i <
        BranchContact.contact v a hne * ((T : ℚ) * v b) :=
      mul_lt_mul_of_pos_left hT hmu
    _ = (T : ℚ) * (BranchContact.contact v a hne * v b) := by ring
    _ ≤ (T : ℚ) * (n : ℚ) := mul_le_mul_of_nonneg_left hc (by positivity)
    _ ≤ (k : ℚ) := by exact_mod_cast hnat

def tails (a : Fin (m+2) → PowerSeries ℂ) (r : Fin m → ℂ) (T : Fin m → ℕ) :
    Fin (m+2) → PowerSeries ℂ :=
  Fin.cases 0 (Fin.cases 0 (fun i => PowerSeries.subst (a 1) (logTail (T i)) -
    PowerSeries.C (r i) * PowerSeries.subst (a 0) (logTail (T i))))

theorem tails_strict
    (v : Fin (m+2) → ℚ) (hv : ∀ i, 0 < v i)
    (a : Fin (m+2) → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0)
    (ha : ∀ i, PowerSeries.constantCoeff (a i) = 0)
    (r : Fin m → ℂ) (T : Fin m → ℕ)
    (hT0 : ∀ i, v i.succ.succ < (T i : ℚ) * v 0)
    (hT1 : ∀ i, v i.succ.succ < (T i : ℚ) * v 1) :
    ∀ i (k : ℕ), PowerSeries.order (tails a r T i) = (k : ℕ∞) →
      BranchContact.contact v a hne * v i < (k : ℚ) := by
  intro i k hk
  cases i using Fin.cases with
  | zero => simp [tails] at hk
  | succ j =>
    cases j using Fin.cases with
    | zero => simp [tails, Fin.succ_zero_eq_one] at hk
    | succ i =>
      exact order_sub_C_mul_strict _ _ _ (r i)
        (composed_tail_strict v hv a hne ha 1 i.succ.succ (T i) (hT1 i))
        (composed_tail_strict v hv a hne ha 0 i.succ.succ (T i) (hT0 i)) k hk

def truncatedCoordinates (cy cz : ℂ) (c r : Fin m → ℂ)
    (y z : PowerSeries ℂ) (x : Fin m → PowerSeries ℂ) (T : Fin m → ℕ) :
    Fin (m+2) → PowerSeries ℂ :=
  Fin.cases (normalizedDifference cy y) (Fin.cases (normalizedDifference cz z)
    (fun i => x i - PowerSeries.C (c i) -
      Polynomial.aeval (normalizedDifference cz z) (CompactJetPolynomial.logPolynomials T i) +
      PowerSeries.C (r i) * Polynomial.aeval (normalizedDifference cy y)
        (CompactJetPolynomial.logPolynomials T i)))

theorem truncatedCoordinates_eq_add_tail (cy cz : ℂ) (hcy : cy ≠ 0) (hcz : cz ≠ 0)
    (c r : Fin m → ℂ) (y z : PowerSeries ℂ) (x : Fin m → PowerSeries ℂ) (T : Fin m → ℕ)
    (hy : PowerSeries.constantCoeff y = cy) (hz : PowerSeries.constantCoeff z = cz) :
    truncatedCoordinates cy cz c r y z x T =
      fun i => coordinates cy cz c r y z x i + tails (coordinates cy cz c r y z x) r T i := by
  have hst := PowerSeries.HasSubst.of_constantCoeff_zero' (normalizedDifference_const cy hcy y hy)
  have hss := PowerSeries.HasSubst.of_constantCoeff_zero' (normalizedDifference_const cz hcz z hz)
  funext i
  cases i using Fin.cases with
  | zero => simp [truncatedCoordinates, coordinates, tails]
  | succ j =>
    cases j using Fin.cases with
    | zero => simp [truncatedCoordinates, coordinates, tails, Fin.succ_zero_eq_one]
    | succ i =>
      simp only [truncatedCoordinates, coordinates, tails, Fin.cases_succ, Fin.cases_zero,
        TwoBaseFrame.fin_cases_one, logTail, PowerSeries.subst_sub hss, PowerSeries.subst_sub hst,
        PowerSeries.subst_coe hss, PowerSeries.subst_coe hst, CompactJetPolynomial.logPolynomials]
      ring

theorem truncatedCoordinates_nonzero
    (v : Fin (m+2) → ℚ) (hv : ∀ i, 0 < v i)
    (cy cz : ℂ) (hcy : cy ≠ 0) (hcz : cz ≠ 0)
    (c r : Fin m → ℂ) (y z : PowerSeries ℂ) (x : Fin m → PowerSeries ℂ)
    (hy : PowerSeries.constantCoeff y = cy) (hz : PowerSeries.constantCoeff z = cz)
    (hx : ∀ i, PowerSeries.constantCoeff (x i) = c i)
    (hne : ∃ i, coordinates cy cz c r y z x i ≠ 0)
    (T : Fin m → ℕ) (hT0 : ∀ i, v i.succ.succ < (T i : ℚ) * v 0)
    (hT1 : ∀ i, v i.succ.succ < (T i : ℚ) * v 1) :
    ∃ i, truncatedCoordinates cy cz c r y z x T i ≠ 0 := by
  rw [truncatedCoordinates_eq_add_tail cy cz hcy hcz c r y z x T hy hz]
  exact BranchContact.add_not_all_zero v hv _ _ hne (tails_strict v hv _ hne
    (coordinates_centered cy cz hcy hcz c r y z x hy hz hx) r T hT0 hT1)

theorem contact_truncatedCoordinates_eq
    (v : Fin (m+2) → ℚ) (hv : ∀ i, 0 < v i)
    (cy cz : ℂ) (hcy : cy ≠ 0) (hcz : cz ≠ 0)
    (c r : Fin m → ℂ) (y z : PowerSeries ℂ) (x : Fin m → PowerSeries ℂ)
    (hy : PowerSeries.constantCoeff y = cy) (hz : PowerSeries.constantCoeff z = cz)
    (hx : ∀ i, PowerSeries.constantCoeff (x i) = c i)
    (hne : ∃ i, coordinates cy cz c r y z x i ≠ 0)
    (T : Fin m → ℕ) (hT0 : ∀ i, v i.succ.succ < (T i : ℚ) * v 0)
    (hT1 : ∀ i, v i.succ.succ < (T i : ℚ) * v 1) :
    BranchContact.contact v (truncatedCoordinates cy cz c r y z x T)
      (truncatedCoordinates_nonzero v hv cy cz hcy hcz c r y z x hy hz hx hne T hT0 hT1) =
        BranchContact.contact v (coordinates cy cz c r y z x) hne := by
  have h := BranchContact.contact_add_high_tail v hv (coordinates cy cz c r y z x)
    (tails (coordinates cy cz c r y z x) r T) hne (tails_strict v hv _ hne
      (coordinates_centered cy cz hcy hcz c r y z x hy hz hx) r T hT0 hT1)
  simpa only [← truncatedCoordinates_eq_add_tail cy cz hcy hcz c r y z x T hy hz] using h

section AlgebraicValues

variable {A : Type*} [CommRing A] [Algebra ℂ A]

def truncatedValues (cy cz : ℂ) (c r : Fin m → ℂ) (x : Fin (m+2) → A)
    (T : Fin m → ℕ) : Fin (m+2) → A :=
  fun i => MvPolynomial.aeval x
    (AlgebraicJet.coordinates cy cz c r (CompactJetPolynomial.logPolynomials T) i)

theorem map_powerIdeal (cy cz : ℂ) (c r : Fin m → ℂ) (x : Fin (m+2) → A)
    (T : Fin m → ℕ) (e : Fin (m+2) → ℕ) :
    (AlgebraicJet.powerIdeal cy cz c r (CompactJetPolynomial.logPolynomials T) e).map
      (MvPolynomial.aeval x).toRingHom =
        BranchContactIdeal.powerIdeal (truncatedValues cy cz c r x T) e := by
  rw [AlgebraicJet.powerIdeal, Ideal.map_span, ← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  exact map_pow (MvPolynomial.aeval x) _ _

end AlgebraicValues

theorem values_in_series (cy cz : ℂ) (c r : Fin m → ℂ)
    (s : Fin (m+2) → PowerSeries ℂ) (T : Fin m → ℕ) :
    truncatedValues cy cz c r s T =
      truncatedCoordinates cy cz c r (s 0) (s 1) (fun i => s i.succ.succ) T := by
  funext i
  cases i using Fin.cases with
  | zero =>
    simp only [truncatedValues, AlgebraicJet.coordinates, AlgebraicJet.inverse_Y,
      AlgebraicJet.normalizedY, map_sub, map_mul, map_one, MvPolynomial.aeval_X,
      MvPolynomial.aeval_C, truncatedCoordinates, Fin.cases_zero]
    rfl
  | succ j =>
    cases j using Fin.cases with
    | zero =>
      simp only [Fin.succ_zero_eq_one, truncatedValues, AlgebraicJet.coordinates,
        AlgebraicJet.inverse_Z, AlgebraicJet.normalizedZ, map_sub, map_mul, map_one,
        MvPolynomial.aeval_X, MvPolynomial.aeval_C, truncatedCoordinates]
      rfl
    | succ i =>
      simp only [truncatedValues, AlgebraicJet.coordinates, AlgebraicJet.inverse_aux,
        map_add, map_sub, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
        ← Polynomial.aeval_algHom_apply, AlgebraicJet.normalizedY, AlgebraicJet.normalizedZ,
        map_sub, map_mul, map_one, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
        truncatedCoordinates, Fin.cases_succ]
      rfl

section DVR

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Algebra ℂ A] [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]

theorem expansion_truncatedValues (cy cz : ℂ) (c r : Fin m → ℂ)
    (x : Fin (m+2) → A) (T : Fin m → ℕ) :
    (fun i => DVRBranch.expansion ℂ A (truncatedValues cy cz c r x T i)) =
      truncatedCoordinates cy cz c r (DVRBranch.expansion ℂ A (x 0))
        (DVRBranch.expansion ℂ A (x 1))
        (fun i => DVRBranch.expansion ℂ A (x i.succ.succ)) T := by
  rw [← values_in_series cy cz c r (fun i => DVRBranch.expansion ℂ A (x i)) T]
  funext i
  exact OrdinaryDVRBranchJet.expansion_aeval x _

theorem colength_eq_contact
    (cy cz : ℂ) (hcy : cy ≠ 0) (hcz : cz ≠ 0) (c r : Fin m → ℂ)
    (x : Fin (m+2) → A)
    (hc : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = AlgebraicJet.center cy cz c i)
    (v : Fin (m+2) → ℚ) (hv : ∀ i, 0 < v i)
    (hne : ∃ i, coordinates cy cz c r (DVRBranch.expansion ℂ A (x 0))
      (DVRBranch.expansion ℂ A (x 1)) (fun j => DVRBranch.expansion ℂ A (x j.succ.succ)) i ≠ 0)
    (T : Fin m → ℕ) (hT0 : ∀ i, v i.succ.succ < (T i : ℚ) * v 0)
    (hT1 : ∀ i, v i.succ.succ < (T i : ℚ) * v 1)
    (R : ℚ) (e : Fin (m+2) → ℕ) (he : ∀ i, v i * (e i : ℚ) = R) :
    ((Module.length A (A ⧸
      (AlgebraicJet.powerIdeal cy cz c r (CompactJetPolynomial.logPolynomials T) e).map
        (MvPolynomial.aeval x).toRingHom)).toNat : ℚ) =
      R * BranchContact.contact v (coordinates cy cz c r (DVRBranch.expansion ℂ A (x 0))
        (DVRBranch.expansion ℂ A (x 1)) (fun i => DVRBranch.expansion ℂ A (x i.succ.succ))) hne := by
  let s := fun i => DVRBranch.expansion ℂ A (x i)
  have hy : PowerSeries.constantCoeff (s 0) = cy := by simpa [s, AlgebraicJet.center] using hc 0
  have hz : PowerSeries.constantCoeff (s 1) = cz := by simpa [s, AlgebraicJet.center] using hc 1
  have hx : ∀ i, PowerSeries.constantCoeff (s i.succ.succ) = c i := by
    intro i
    simpa [s, AlgebraicJet.center] using hc i.succ.succ
  have ht := truncatedCoordinates_nonzero v hv cy cz hcy hcz c r (s 0) (s 1)
    (fun i => s i.succ.succ) hy hz hx hne T hT0 hT1
  have hn : ∃ i, truncatedValues cy cz c r x T i ≠ 0 := by
    obtain ⟨i, hi⟩ := ht
    refine ⟨i, ?_⟩
    intro hzero
    apply hi
    change truncatedCoordinates cy cz c r (DVRBranch.expansion ℂ A (x 0))
      (DVRBranch.expansion ℂ A (x 1))
      (fun j => DVRBranch.expansion ℂ A (x j.succ.succ)) T i = 0
    rw [← expansion_truncatedValues]
    change DVRBranch.expansion ℂ A (truncatedValues cy cz c r x T i) = 0
    rw [hzero, map_zero]
  rw [map_powerIdeal, BranchContactIdeal.colength_eq_contact v hv _ hn R e he]
  apply congrArg (fun t : ℚ => R*t)
  unfold BranchContactIdeal.contact
  trans BranchContact.contact v
    (truncatedCoordinates cy cz c r (s 0) (s 1) (fun i => s i.succ.succ) T) ht
  · apply LogarithmicContactIdeal.branchContact_congr
    exact expansion_truncatedValues cy cz c r x T
  · exact contact_truncatedCoordinates_eq v hv cy cz hcy hcz c r (s 0) (s 1)
      (fun i => s i.succ.succ) hy hz hx hne T hT0 hT1

end DVR

open CurveValuationCenter PlaceValuationRing CurveCenters

/-- Local ideal colength equals the actual contact used by the curve theorem,
not a contact introduced just for this algebraic-ideal construction. -/
theorem place_colength_eq_contact
    {E : Type*} [Field E] [Algebra ℂ E]
    (place : NormalizedPlace ℂ E)
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring place))]
    (x : Fin (m+2) → E) (cy cz : ℂ) (hcy : cy ≠ 0) (hcz : cz ≠ 0)
    (c r : Fin m → ℂ) (hc : Centered x (PlaceContact.center cy cz c) place)
    (hnc : ∃ i, x i ≠ algebraMap ℂ E (PlaceContact.center cy cz c i))
    (v : Fin (m+2) → ℚ) (hv : ∀ i, 0 < v i)
    (T : Fin m → ℕ) (hT0 : ∀ i, v i.succ.succ < (T i : ℚ) * v 0)
    (hT1 : ∀ i, v i.succ.succ < (T i : ℚ) * v 1)
    (R : ℚ) (e : Fin (m+2) → ℕ) (he : ∀ i, v i * (e i : ℚ) = R) :
    ((Module.length (ring place) ((ring place) ⧸
      (AlgebraicJet.powerIdeal cy cz c r (CompactJetPolynomial.logPolynomials T) e).map
        (MvPolynomial.aeval (PlaceCenteredBranch.lift place x (PlaceContact.center cy cz c) hc)).toRingHom)).toNat : ℚ) =
      R * PlaceContact.contact place x cy cz c hc r hcy hcz hnc v := by
  exact colength_eq_contact cy cz hcy hcz c r
    (PlaceCenteredBranch.lift place x (PlaceContact.center cy cz c) hc)
    (PlaceCenteredBranch.lift_residue place x (PlaceContact.center cy cz c) hc) v hv
    (PlaceContact.coordinates_nonzero place x cy cz c hc r hcy hcz hnc)
    T hT0 hT1 R e he

#print axioms contact_truncatedCoordinates_eq
#print axioms colength_eq_contact
#print axioms place_colength_eq_contact

end LogarithmExtension.LogRatio.ContactLength

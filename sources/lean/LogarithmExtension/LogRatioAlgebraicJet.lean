import LogarithmExtension.LogRatioFormalJet
import OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial

/-!
# Algebraic coordinates for the two-base jet ideals

The truncated two-base substitution is an explicit polynomial automorphism.
The coordinate-power ideal therefore has exactly the prescribed center as
its support. Local packets can be prescribed without a degree bound; this
is not the bounded simultaneous interpolation theorem.

The ideal and packet arguments adapt the pinned OpenAI
`AlgebraicJetPackets` and `CompactJetPolynomial` modules (Apache-2.0).
-/

noncomputable section
namespace LogarithmExtension.LogRatio.AlgebraicJet

open MvPolynomial OAI.PiExponent PolynomialFrame

variable {m : ℕ}

def normalizedY (cy : ℂ) : Poly m := C cy⁻¹ * X 0 - 1
def normalizedZ (cz : ℂ) : Poly m := C cz⁻¹ * X 1 - 1

def forward (cy cz : ℂ) (c r : Fin m → ℂ) (G : Fin m → Polynomial ℂ) :
    Poly m →ₐ[ℂ] Poly m :=
  aeval (Fin.cases (C cy * (1 + X 0)) (Fin.cases (C cz * (1 + X 1))
    (fun i => C (c i) + X i.succ.succ + Polynomial.aeval (X 1) (G i) -
      C (r i) * Polynomial.aeval (X 0) (G i))))

def inverse (cy cz : ℂ) (c r : Fin m → ℂ) (G : Fin m → Polynomial ℂ) :
    Poly m →ₐ[ℂ] Poly m :=
  aeval (Fin.cases (normalizedY cy) (Fin.cases (normalizedZ cz)
    (fun i => X i.succ.succ - C (c i) - Polynomial.aeval (normalizedZ cz) (G i) +
      C (r i) * Polynomial.aeval (normalizedY cy) (G i))))

@[simp] theorem forward_Y (cy cz : ℂ) (c r : Fin m → ℂ) (G : Fin m → Polynomial ℂ) :
    forward cy cz c r G (X 0) = C cy * (1 + X 0) := by simp [forward]

@[simp] theorem forward_Z (cy cz : ℂ) (c r : Fin m → ℂ) (G : Fin m → Polynomial ℂ) :
    forward cy cz c r G (X 1) = C cz * (1 + X 1) := by
  simp only [forward, aeval_X]
  rfl

@[simp] theorem forward_aux (cy cz : ℂ) (c r : Fin m → ℂ) (G : Fin m → Polynomial ℂ)
    (i : Fin m) : forward cy cz c r G (X i.succ.succ) =
      C (c i) + X i.succ.succ + Polynomial.aeval (X 1) (G i) -
        C (r i) * Polynomial.aeval (X 0) (G i) := by simp [forward]

@[simp] theorem inverse_Y (cy cz : ℂ) (c r : Fin m → ℂ) (G : Fin m → Polynomial ℂ) :
    inverse cy cz c r G (X 0) = normalizedY cy := by simp [inverse]

@[simp] theorem inverse_Z (cy cz : ℂ) (c r : Fin m → ℂ) (G : Fin m → Polynomial ℂ) :
    inverse cy cz c r G (X 1) = normalizedZ cz := by
  simp only [inverse, aeval_X]
  rfl

@[simp] theorem inverse_aux (cy cz : ℂ) (c r : Fin m → ℂ) (G : Fin m → Polynomial ℂ)
    (i : Fin m) : inverse cy cz c r G (X i.succ.succ) =
      X i.succ.succ - C (c i) - Polynomial.aeval (normalizedZ cz) (G i) +
        C (r i) * Polynomial.aeval (normalizedY cy) (G i) := by simp [inverse]

theorem forward_normalizedY (cy cz : ℂ) (hcy : cy ≠ 0)
    (c r : Fin m → ℂ) (G : Fin m → Polynomial ℂ) :
    forward cy cz c r G (normalizedY cy) = X 0 := by
  simp only [normalizedY, map_sub, map_mul, algHom_C, forward_Y, map_one, algebraMap_eq]
  rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hcy, map_one, one_mul]
  ring

theorem forward_normalizedZ (cy cz : ℂ) (hcz : cz ≠ 0)
    (c r : Fin m → ℂ) (G : Fin m → Polynomial ℂ) :
    forward cy cz c r G (normalizedZ cz) = X 1 := by
  simp only [normalizedZ, map_sub, map_mul, algHom_C, forward_Z, map_one, algebraMap_eq]
  rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hcz, map_one, one_mul]
  ring

theorem forward_comp_inverse (cy cz : ℂ) (hcy : cy ≠ 0) (hcz : cz ≠ 0)
    (c r : Fin m → ℂ) (G : Fin m → Polynomial ℂ) :
    (forward cy cz c r G).comp (inverse cy cz c r G) = AlgHom.id ℂ (Poly m) := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i using Fin.cases with
  | zero => simpa using forward_normalizedY cy cz hcy c r G
  | succ j =>
    cases j using Fin.cases with
    | zero => simpa only [Fin.succ_zero_eq_one, AlgHom.comp_apply, inverse_Z,
        AlgHom.id_apply] using forward_normalizedZ cy cz hcz c r G
    | succ i =>
      simp only [AlgHom.comp_apply, inverse_aux, map_add, map_sub, map_mul, algHom_C,
        forward_aux, ← Polynomial.aeval_algHom_apply,
        forward_normalizedY cy cz hcy, forward_normalizedZ cy cz hcz, AlgHom.id_apply,
        algebraMap_eq]
      ring

theorem inverse_comp_forward (cy cz : ℂ) (hcy : cy ≠ 0) (hcz : cz ≠ 0)
    (c r : Fin m → ℂ) (G : Fin m → Polynomial ℂ) :
    (inverse cy cz c r G).comp (forward cy cz c r G) = AlgHom.id ℂ (Poly m) := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i using Fin.cases with
  | zero =>
    simp only [AlgHom.comp_apply, forward_Y, map_mul, map_add, algHom_C, map_one,
      inverse_Y, normalizedY, AlgHom.id_apply, algebraMap_eq]
    rw [show (1 + (C cy⁻¹ * X (0 : Fin (m+2)) - 1) : Poly m) = C cy⁻¹ * X 0 by ring,
      ← mul_assoc, ← map_mul, mul_inv_cancel₀ hcy, map_one, one_mul]
  | succ j =>
    cases j using Fin.cases with
    | zero =>
      simp only [Fin.succ_zero_eq_one, AlgHom.comp_apply, forward_Z, map_mul, map_add,
        algHom_C, map_one, inverse_Z, normalizedZ, AlgHom.id_apply, algebraMap_eq]
      rw [show (1 + (C cz⁻¹ * X (1 : Fin (m+2)) - 1) : Poly m) = C cz⁻¹ * X 1 by ring,
        ← mul_assoc, ← map_mul, mul_inv_cancel₀ hcz, map_one, one_mul]
    | succ i =>
      simp only [AlgHom.comp_apply, forward_aux, map_sub, map_add, map_mul, algHom_C,
        inverse_aux, ← Polynomial.aeval_algHom_apply, inverse_Y, inverse_Z, AlgHom.id_apply,
        algebraMap_eq]
      ring

def polynomialEquiv (cy cz : ℂ) (hcy : cy ≠ 0) (hcz : cz ≠ 0)
    (c r : Fin m → ℂ) (G : Fin m → Polynomial ℂ) : Poly m ≃ₐ[ℂ] Poly m :=
  AlgEquiv.ofAlgHom (forward cy cz c r G) (inverse cy cz c r G)
    (forward_comp_inverse cy cz hcy hcz c r G) (inverse_comp_forward cy cz hcy hcz c r G)

def center (cy cz : ℂ) (c : Fin m → ℂ) : Fin (m+2) → ℂ :=
  Fin.cases cy (Fin.cases cz c)

def coordinates (cy cz : ℂ) (c r : Fin m → ℂ) (G : Fin m → Polynomial ℂ)
    (i : Fin (m+2)) : Poly m := inverse cy cz c r G (X i)

def powerIdeal (cy cz : ℂ) (c r : Fin m → ℂ) (G : Fin m → Polynomial ℂ)
    (e : Fin (m+2) → ℕ) : Ideal (Poly m) :=
  Ideal.span (Set.range (fun i => coordinates cy cz c r G i ^ e i))

theorem eval_center_normalizedY (cy cz : ℂ) (hcy : cy ≠ 0) (c : Fin m → ℂ) :
    aeval (center cy cz c) (normalizedY cy) = 0 := by
  simp [normalizedY, center, hcy]

theorem eval_center_normalizedZ (cy cz : ℂ) (hcz : cz ≠ 0) (c : Fin m → ℂ) :
    aeval (center cy cz c) (normalizedZ cz) = 0 := by
  simp [normalizedZ, center, hcz]

theorem eval_center_inverse (cy cz : ℂ) (hcy : cy ≠ 0) (hcz : cz ≠ 0)
    (c r : Fin m → ℂ) (G : Fin m → Polynomial ℂ) (hG : ∀ i, (G i).eval 0 = 0) :
    (aeval (center cy cz c)).comp (inverse cy cz c r G) =
      aeval (0 : Fin (m+2) → ℂ) := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i using Fin.cases with
  | zero => simpa only [AlgHom.comp_apply, inverse_Y, aeval_X, Pi.zero_apply]
      using eval_center_normalizedY cy cz hcy c
  | succ j =>
    cases j using Fin.cases with
    | zero => simp only [Fin.succ_zero_eq_one, AlgHom.comp_apply, inverse_Z,
        eval_center_normalizedZ cy cz hcz, aeval_X, Pi.zero_apply]
    | succ i =>
      simp only [AlgHom.comp_apply, inverse_aux, map_add, map_sub, map_mul, aeval_X,
        aeval_C, ← Polynomial.aeval_algHom_apply, eval_center_normalizedY cy cz hcy,
        eval_center_normalizedZ cy cz hcz]
      simp [center, Polynomial.coe_aeval_eq_eval, hG i]

theorem span_coordinates (cy cz : ℂ) (hcy : cy ≠ 0) (hcz : cz ≠ 0)
    (c r : Fin m → ℂ) (G : Fin m → Polynomial ℂ) (hG : ∀ i, (G i).eval 0 = 0) :
    Ideal.span (Set.range (coordinates cy cz c r G)) = WeightedBezout.pointIdeal (center cy cz c) := by
  let phi := (inverse cy cz c r G).toRingHom
  have hs : Function.Surjective phi := (polynomialEquiv cy cz hcy hcz c r G).symm.surjective
  have hc : (WeightedBezout.pointIdeal (center cy cz c)).comap phi =
      WeightedBezout.pointIdeal (0 : Fin (m+2) → ℂ) := by
    ext P
    change aeval (center cy cz c) (inverse cy cz c r G P) = 0 ↔
      aeval (0 : Fin (m+2) → ℂ) P = 0
    rw [← AlgHom.comp_apply, eval_center_inverse cy cz hcy hcz c r G hG]
  calc
    Ideal.span (Set.range (coordinates cy cz c r G)) =
        (Ideal.span (Set.range (X (R := ℂ) : Fin (m+2) → _))).map phi := by
      rw [Ideal.map_span, ← Set.range_comp]
      rfl
    _ = (WeightedBezout.pointIdeal (0 : Fin (m+2) → ℂ)).map phi := by
      congr 1
      rw [WeightedBezout.pointIdeal_eq_span]
      simp
    _ = WeightedBezout.pointIdeal (center cy cz c) := by
      rw [← hc, Ideal.map_comap_of_surjective phi hs]

theorem radical_powerIdeal (cy cz : ℂ) (hcy : cy ≠ 0) (hcz : cz ≠ 0)
    (c r : Fin m → ℂ) (G : Fin m → Polynomial ℂ) (hG : ∀ i, (G i).eval 0 = 0)
    (e : Fin (m+2) → ℕ) (he : ∀ i, 0 < e i) :
    (powerIdeal cy cz c r G e).radical = WeightedBezout.pointIdeal (center cy cz c) := by
  apply le_antisymm
  · apply (Ideal.IsPrime.radical_le_iff
      (inferInstance : (WeightedBezout.pointIdeal (center cy cz c)).IsPrime)).mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have hz : coordinates cy cz c r G i ∈ WeightedBezout.pointIdeal (center cy cz c) := by
      rw [← span_coordinates cy cz hcy hcz c r G hG]
      exact Ideal.subset_span ⟨i, rfl⟩
    change aeval (center cy cz c) (coordinates cy cz c r G i ^ e i) = 0
    rw [map_pow, (WeightedBezout.mem_pointIdeal _ _).mp hz, zero_pow (he i).ne']
  · rw [← span_coordinates cy cz hcy hcz c r G hG]
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨e i, Ideal.subset_span ⟨i, rfl⟩⟩

def truncatedJet (cy cz : ℂ) (c r : Fin m → ℂ) (G : Fin m → Polynomial ℂ) :
    Poly m →ₐ[ℂ] MvPowerSeries (Fin (m+2)) ℂ :=
  (MvPolynomial.coeToMvPowerSeries.algHom ℂ).comp (forward cy cz c r G)

@[simp] theorem truncatedJet_Y (cy cz : ℂ) (c r : Fin m → ℂ) (G : Fin m → Polynomial ℂ) :
    truncatedJet cy cz c r G (X 0) = MvPowerSeries.C cy * (1 + MvPowerSeries.X 0) := by
  simp [truncatedJet]

@[simp] theorem truncatedJet_Z (cy cz : ℂ) (c r : Fin m → ℂ) (G : Fin m → Polynomial ℂ) :
    truncatedJet cy cz c r G (X 1) = MvPowerSeries.C cz * (1 + MvPowerSeries.X 1) := by
  simp [truncatedJet]

@[simp] theorem truncatedJet_aux (cy cz : ℂ) (c r : Fin m → ℂ) (G : Fin m → Polynomial ℂ)
    (i : Fin m) : truncatedJet cy cz c r G (X i.succ.succ) =
      MvPowerSeries.C (c i) + MvPowerSeries.X i.succ.succ +
      Polynomial.aeval (MvPowerSeries.X 1) (G i) -
      MvPowerSeries.C (r i) * Polynomial.aeval (MvPowerSeries.X 0) (G i) := by
  change (MvPolynomial.coeToMvPowerSeries.algHom ℂ) (forward cy cz c r G (X i.succ.succ)) = _
  rw [forward_aux]
  simp only [map_sub, map_add, map_mul, ← Polynomial.aeval_algHom_apply]
  simp [MvPowerSeries.algebraMap_apply]

theorem truncatedJet_inverse (cy cz : ℂ) (hcy : cy ≠ 0) (hcz : cz ≠ 0)
    (c r : Fin m → ℂ) (G : Fin m → Polynomial ℂ) (P : Poly m) :
    truncatedJet cy cz c r G (inverse cy cz c r G P) =
      (P : MvPowerSeries (Fin (m+2)) ℂ) := by
  have hh := AlgHom.congr_fun (forward_comp_inverse cy cz hcy hcz c r G) P
  exact congrArg (fun Q : Poly m => (Q : MvPowerSeries (Fin (m+2)) ℂ)) hh

/-- Local, unbounded-degree interpolation only. The global weighted-degree
bound still requires the projective curve-to-interpolation passage. -/
theorem truncatedJet_packet_surjective (cy cz : ℂ) (hcy : cy ≠ 0) (hcz : cz ≠ 0)
    (c r : Fin m → ℂ) (G : Fin m → Polynomial ℂ)
    (v : Fin (m+2) → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ) :
    Function.Surjective (fun P : Poly m =>
      JetGeometry.rationalCoefficientPacket v H (truncatedJet cy cz c r G P)) := by
  intro packet
  obtain ⟨P, hP⟩ := PolynomialJetPackets.polynomial_packet_surjective v hv H packet
  refine ⟨inverse cy cz c r G P, ?_⟩
  simpa only [truncatedJet_inverse cy cz hcy hcz] using hP

theorem polynomial_toMvPowerSeries (i : Fin (m+2)) (P : Polynomial ℂ) :
    (P : PowerSeries ℂ).toMvPowerSeries i = Polynomial.aeval (MvPowerSeries.X i) P := by
  have h : (PowerSeries.toMvPowerSeries (R := ℂ) i).toRingHom.comp
      Polynomial.coeToPowerSeries.ringHom =
      (Polynomial.aeval (MvPowerSeries.X i)).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro z
      simp [MvPowerSeries.algebraMap_apply]
    · simp
  exact RingHom.congr_fun h P

theorem logTail_mem (i : Fin (m+2)) (v : Fin (m+2) → ℚ) (hv : ∀ j, 0 ≤ v j)
    (T : ℕ) (H : ℚ) (hT : H ≤ (T : ℚ) * v i) :
    (FormalLogTruncation.logTail T).toMvPowerSeries i ∈
      JetGeometry.rationalWeightedIdeal v hv H := by
  intro d hd
  rw [FormalJet.coeff_toMvPowerSeries]
  split_ifs with he
  · have hdi : (d i : ℚ) * v i < H := by
      conv at hd => lhs; rw [he]
      simpa only [Finsupp.weight_single, nsmul_eq_mul] using hd
    apply FormalLogTruncation.coeff_logTail_eq_zero
    by_contra hn
    have hh : (T : ℚ) ≤ (d i : ℚ) := by exact_mod_cast Nat.le_of_not_gt hn
    exact (not_lt_of_ge ((mul_le_mul_of_nonneg_right hh (hv i)).trans' hT)) hdi
  · rfl

theorem formalJet_normalizedY (cy cz : ℂ) (hcy : cy ≠ 0) (c r : Fin m → ℂ) :
    FormalJet.formalJet cy cz c r (normalizedY cy) = MvPowerSeries.X 0 := by
  simp only [normalizedY, map_sub, map_mul, FormalJet.formalJet_C,
    FormalJet.formalJet_Y, map_one]
  rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hcy, map_one, one_mul]
  ring

theorem formalJet_normalizedZ (cy cz : ℂ) (hcz : cz ≠ 0) (c r : Fin m → ℂ) :
    FormalJet.formalJet cy cz c r (normalizedZ cz) = MvPowerSeries.X 1 := by
  simp only [normalizedZ, map_sub, map_mul, FormalJet.formalJet_C,
    FormalJet.formalJet_Z, map_one]
  rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hcz, map_one, one_mul]
  ring

theorem formalJet_aux_coordinate (cy cz : ℂ) (hcy : cy ≠ 0) (hcz : cz ≠ 0)
    (c r : Fin m → ℂ) (T : Fin m → ℕ) (i : Fin m) :
    FormalJet.formalJet cy cz c r (coordinates cy cz c r (CompactJetPolynomial.logPolynomials T)
      i.succ.succ) = MvPowerSeries.X i.succ.succ +
        (FormalLogTruncation.logTail (T i)).toMvPowerSeries 1 -
        MvPowerSeries.C (r i) * (FormalLogTruncation.logTail (T i)).toMvPowerSeries 0 := by
  simp only [coordinates, inverse_aux, map_add, map_sub, map_mul, FormalJet.formalJet_aux,
    FormalJet.formalJet_C, ← Polynomial.aeval_algHom_apply,
    formalJet_normalizedY cy cz hcy, formalJet_normalizedZ cy cz hcz]
  simp only [FormalLogTruncation.logTail, map_sub, polynomial_toMvPowerSeries,
    CompactJetPolynomial.logPolynomials, FormalJet.logAt]
  ring

theorem formalJet_coordinate_mem (cy cz : ℂ) (hcy : cy ≠ 0) (hcz : cz ≠ 0)
    (c r : Fin m → ℂ) (T : Fin m → ℕ)
    (v : Fin (m+2) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (hT0 : ∀ i, v i.succ.succ ≤ (T i : ℚ) * v 0)
    (hT1 : ∀ i, v i.succ.succ ≤ (T i : ℚ) * v 1) (i : Fin (m+2)) :
    FormalJet.formalJet cy cz c r
      (coordinates cy cz c r (CompactJetPolynomial.logPolynomials T) i) ∈
        JetGeometry.rationalWeightedIdeal v hv (v i) := by
  cases i using Fin.cases with
  | zero =>
    simp only [coordinates, inverse_Y, formalJet_normalizedY cy cz hcy]
    exact FormalLogTruncation.X_mem_rationalWeightedIdeal v hv 0
  | succ j =>
    cases j using Fin.cases with
    | zero =>
      simp only [Fin.succ_zero_eq_one, coordinates, inverse_Z, formalJet_normalizedZ cy cz hcz]
      exact FormalLogTruncation.X_mem_rationalWeightedIdeal v hv 1
    | succ i =>
      rw [formalJet_aux_coordinate cy cz hcy hcz]
      apply Ideal.sub_mem
      · exact Ideal.add_mem _ (FormalLogTruncation.X_mem_rationalWeightedIdeal v hv _)
          (logTail_mem 1 v hv (T i) _ (hT1 i))
      · exact Ideal.mul_mem_left _ _ (logTail_mem 0 v hv (T i) _ (hT0 i))

/-- Powers of the concrete algebraic ideal kill the required full formal
logarithmic packets, with the truncations fixed before taking the power. -/
theorem formalJet_mem_weighted_of_mem_pow (cy cz : ℂ) (hcy : cy ≠ 0) (hcz : cz ≠ 0)
    (c r : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+2) → ℕ)
    (v : Fin (m+2) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (hT0 : ∀ i, v i.succ.succ ≤ (T i : ℚ) * v 0)
    (hT1 : ∀ i, v i.succ.succ ≤ (T i : ℚ) * v 1)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ) (P : Poly m)
    (hP : P ∈ powerIdeal cy cz c r (CompactJetPolynomial.logPolynomials T) e ^ n) :
    FormalJet.formalJet cy cz c r P ∈ JetGeometry.rationalWeightedIdeal v hv (n*R) := by
  let phi := (FormalJet.formalJet cy cz c r).toRingHom
  have hI : (powerIdeal cy cz c r (CompactJetPolynomial.logPolynomials T) e).map phi ≤
      JetGeometry.rationalWeightedIdeal v hv R := by
    rw [powerIdeal, Ideal.map_span, ← Set.range_comp]
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change FormalJet.formalJet cy cz c r
      (coordinates cy cz c r (CompactJetPolynomial.logPolynomials T) i ^ e i) ∈ _
    rw [map_pow]
    have hi := formalJet_coordinate_mem cy cz hcy hcz c r T v hv hT0 hT1 i
    have hh := JetGeometry.ideal_pow_le_rationalWeightedIdeal v hv
      (JetGeometry.rationalWeightedIdeal v hv (v i)) (v i) le_rfl (e i)
      (Ideal.pow_mem_pow hi (e i))
    intro d hd
    exact hh d (hd.trans_le (he i))
  apply JetGeometry.ideal_pow_le_rationalWeightedIdeal v hv _ R hI n
  rw [← Ideal.map_pow]
  exact Ideal.mem_map_of_mem phi hP

theorem formalJet_packet_zero_of_mem_pow (cy cz : ℂ) (hcy : cy ≠ 0) (hcz : cz ≠ 0)
    (c r : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+2) → ℕ)
    (v : Fin (m+2) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (hT0 : ∀ i, v i.succ.succ ≤ (T i : ℚ) * v 0)
    (hT1 : ∀ i, v i.succ.succ ≤ (T i : ℚ) * v 1)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ) (P : Poly m)
    (hP : P ∈ powerIdeal cy cz c r (CompactJetPolynomial.logPolynomials T) e ^ n) :
    JetGeometry.rationalCoefficientPacket v (n*R) (FormalJet.formalJet cy cz c r P) =
      (fun _ => (0 : ℂ)) := by
  funext d
  exact formalJet_mem_weighted_of_mem_pow cy cz hcy hcz c r T e v hv hT0 hT1 R he n P hP
    d.val d.property

/-- Sufficiently long polynomial truncations agree with the full formal
jet in a specified finite packet. There is no degree-bound assertion. -/
theorem formalJet_sub_truncatedJet_mem (cy cz : ℂ) (c r : Fin m → ℂ) (T : Fin m → ℕ)
    (v : Fin (m+2) → ℚ) (hv : ∀ i, 0 ≤ v i) (H : ℚ)
    (hT0 : ∀ i, H ≤ (T i : ℚ) * v 0) (hT1 : ∀ i, H ≤ (T i : ℚ) * v 1)
    (P : Poly m) :
    FormalJet.formalJet cy cz c r P -
      truncatedJet cy cz c r (CompactJetPolynomial.logPolynomials T) P ∈
        JetGeometry.rationalWeightedIdeal v hv H := by
  let I := JetGeometry.rationalWeightedIdeal (R := ℂ) v hv H
  have h : (Ideal.Quotient.mkₐ ℂ I).comp (FormalJet.formalJet cy cz c r) =
      (Ideal.Quotient.mkₐ ℂ I).comp
        (truncatedJet cy cz c r (CompactJetPolynomial.logPolynomials T)) := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i using Fin.cases with
    | zero => simp only [AlgHom.comp_apply, FormalJet.formalJet_Y, truncatedJet_Y]
    | succ j =>
      cases j using Fin.cases with
      | zero => simp only [Fin.succ_zero_eq_one, AlgHom.comp_apply,
          FormalJet.formalJet_Z, truncatedJet_Z]
      | succ i =>
        change Ideal.Quotient.mk I _ = Ideal.Quotient.mk I _
        apply Ideal.Quotient.eq.mpr
        change FormalJet.formalJet cy cz c r (X i.succ.succ) -
          truncatedJet cy cz c r (CompactJetPolynomial.logPolynomials T) (X i.succ.succ) ∈ I
        rw [FormalJet.formalJet_aux, truncatedJet_aux]
        have he :
            (MvPowerSeries.C (c i) + MvPowerSeries.X i.succ.succ + FormalJet.logAt 1 -
              MvPowerSeries.C (r i) * FormalJet.logAt 0) -
            (MvPowerSeries.C (c i) + MvPowerSeries.X i.succ.succ +
              Polynomial.aeval (MvPowerSeries.X 1) (CompactJetPolynomial.logPolynomials T i) -
              MvPowerSeries.C (r i) * Polynomial.aeval (MvPowerSeries.X 0)
                (CompactJetPolynomial.logPolynomials T i)) =
            (FormalLogTruncation.logTail (T i)).toMvPowerSeries 1 -
              MvPowerSeries.C (r i) * (FormalLogTruncation.logTail (T i)).toMvPowerSeries 0 := by
          simp only [FormalLogTruncation.logTail, map_sub, polynomial_toMvPowerSeries,
            FormalJet.logAt, CompactJetPolynomial.logPolynomials]
          ring
        rw [he]
        exact Ideal.sub_mem I (logTail_mem 1 v hv (T i) H (hT1 i))
          (Ideal.mul_mem_left I _ (logTail_mem 0 v hv (T i) H (hT0 i)))
  exact Ideal.Quotient.eq.mp (AlgHom.congr_fun h P)

/-- Every finite local packet of the genuine two-base logarithmic jet is
realized by a polynomial. Simultaneous bounded-degree interpolation is not
asserted by this local theorem. -/
theorem formalJet_packet_surjective (cy cz : ℂ) (hcy : cy ≠ 0) (hcz : cz ≠ 0)
    (c r : Fin m → ℂ) (v : Fin (m+2) → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ) :
    Function.Surjective (fun P : Poly m =>
      JetGeometry.rationalCoefficientPacket v H (FormalJet.formalJet cy cz c r P)) := by
  let T : Fin m → ℕ := fun _ => max (Nat.ceil (H / v 0)) (Nat.ceil (H / v 1))
  have hT0 : ∀ i, H ≤ (T i : ℚ) * v 0 := by
    intro i
    apply (div_le_iff₀ (hv 0)).mp
    exact (Nat.le_ceil _).trans (by exact_mod_cast
      (le_max_left (Nat.ceil (H / v 0)) (Nat.ceil (H / v 1))))
  have hT1 : ∀ i, H ≤ (T i : ℚ) * v 1 := by
    intro i
    apply (div_le_iff₀ (hv 1)).mp
    exact (Nat.le_ceil _).trans (by exact_mod_cast
      (le_max_right (Nat.ceil (H / v 0)) (Nat.ceil (H / v 1))))
  intro packet
  obtain ⟨P, hP⟩ := truncatedJet_packet_surjective cy cz hcy hcz c r
    (CompactJetPolynomial.logPolynomials T) v hv H packet
  refine ⟨P, ?_⟩
  have he := (FormalLogTruncation.rationalCoefficientPacket_eq_iff v (fun i => (hv i).le)
    H _ _).mpr (formalJet_sub_truncatedJet_mem cy cz c r T v (fun i => (hv i).le) H hT0 hT1 P)
  exact he.trans hP

#print axioms polynomialEquiv
#print axioms radical_powerIdeal
#print axioms truncatedJet_packet_surjective
#print axioms formalJet_packet_zero_of_mem_pow
#print axioms formalJet_packet_surjective

end LogarithmExtension.LogRatio.AlgebraicJet

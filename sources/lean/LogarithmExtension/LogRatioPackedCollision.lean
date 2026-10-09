import LogarithmExtension.LogRatioTaylorPacking
import OAI.NumberTheory.PiExponent.Analysis.FiniteDeterminantCollision

/-!
# Determinant cancellation with direct weighted Taylor packing

The coefficient vectors are indexed jointly by the auxiliary monomial and
the pair of Taylor degrees. Repeated combined indices kill a determinant
term. The remaining terms obey the proved augmented-simplex packing bound.
-/

noncomputable section
namespace LogarithmExtension.LogRatio.TaylorPacking

open OAI OAI.PiExponent
open scoped BigOperators Topology
open Filter

def quarterRatio : ℝ := Real.exp (-1/4)

theorem quarterRatio_pos : 0 < quarterRatio := Real.exp_pos _
theorem quarterRatio_lt_one : quarterRatio < 1 := Real.exp_lt_one_iff.mpr (by norm_num)

theorem quarterRatio_pow (n : ℕ) : quarterRatio^n = Real.exp (-(n : ℝ)/4) := by
  rw [quarterRatio, ← Real.exp_nat_mul]
  congr 1
  ring

theorem half_le_quarterRatio_sq : (1/2 : ℝ) ≤ quarterRatio*quarterRatio := by
  rw [quarterRatio, ← Real.exp_add]
  have h := Real.add_one_le_exp (-1/2)
  norm_num at h ⊢
  exact h

theorem sum_pair_powers_le (S : Finset (ℕ × ℕ)) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (∑ p ∈ S, s^(p.1+p.2)) ≤ ((1-s)⁻¹)^2 := by
  classical
  let N := S.sup (fun p => max p.1 p.2)+1
  have hsub : S ⊆ Finset.range N ×ˢ Finset.range N := by
    intro p hp
    have hmax := Finset.le_sup (f := fun p : ℕ × ℕ => max p.1 p.2) hp
    apply Finset.mem_product.mpr
    constructor <;> apply Finset.mem_range.mpr
    · exact Nat.lt_succ_of_le ((le_max_left _ _).trans hmax)
    · exact Nat.lt_succ_of_le ((le_max_right _ _).trans hmax)
  have hb := Collision.sum_pow_fin_le_inv_one_sub hs0 hs1 N
  rw [Fin.sum_univ_eq_sum_range] at hb
  calc
    _ ≤ ∑ p ∈ Finset.range N ×ˢ Finset.range N, s^(p.1+p.2) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => pow_nonneg hs0 _)
    _ = (∑ k ∈ Finset.range N, s^k)^2 := by
      rw [Finset.sum_product]
      simp only [pow_add, ← Finset.mul_sum, ← Finset.sum_mul, pow_two]
    _ ≤ _ := pow_le_pow_left₀ (Finset.sum_nonneg (fun k _ => pow_nonneg hs0 k)) hb 2

theorem sum_pair_assignments_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset (ℕ × ℕ)) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (∑ f : ι → ↥S, s^(∑ i, ((f i).val.1+(f i).val.2))) ≤
      ((1-s)⁻¹)^(2*Fintype.card ι) := by
  classical
  have hb : (∑ p : ↥S, s^(p.val.1+p.val.2)) ≤ ((1-s)⁻¹)^2 := by
    have h := sum_pair_powers_le S hs0 hs1
    rw [← Finset.sum_coe_sort] at h
    exact h
  calc
    _ = (∑ p : ↥S, s^(p.val.1+p.val.2))^Fintype.card ι := by
      simp_rw [← Finset.prod_pow_eq_pow_sum]
      rw [← Fintype.prod_sum (fun (_ : ι) (p : ↥S) => s^(p.val.1+p.val.2))]
      simp
    _ ≤ (((1-s)⁻¹)^2)^Fintype.card ι :=
      pow_le_pow_left₀ (Finset.sum_nonneg (fun p _ => pow_nonneg hs0 _)) hb _
    _ = _ := (pow_mul _ _ _).symm

theorem weighted_degree_saving {m : ℕ} {ι : Type*} [Fintype ι]
    (w : Fin m → ℝ) (nu L : ℝ) (hw : ∀ i, 0 < w i) (hnu : 0 < nu)
    (a : ι → Fin m → ℕ) (p : ι → ℕ × ℕ)
    (hinj : Function.Injective (fun i => (a i, p i))) :
    Real.exp (-nu*(∑ i, cost w (a i))) * (1/2 : ℝ)^(∑ i, ((p i).1+(p i).2)) ≤
      Real.exp (-L*Fintype.card ι+augmentedCount (combinedWeights w nu) L) *
        quarterRatio^(∑ i, ((p i).1+(p i).2)) := by
  have hp := combined_cost_lower_bound w nu L hw hnu a p hinj
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1/2)
    half_le_quarterRatio_sq (∑ i, ((p i).1+(p i).2))
  calc
    _ ≤ Real.exp (-nu*(∑ i, cost w (a i))) *
        (quarterRatio*quarterRatio)^(∑ i, ((p i).1+(p i).2)) :=
      mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
    _ = (Real.exp (-nu*(∑ i, cost w (a i))) *
          quarterRatio^(∑ i, ((p i).1+(p i).2))) *
            quarterRatio^(∑ i, ((p i).1+(p i).2)) := by rw [mul_pow]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg quarterRatio_pos.le _)
      rw [quarterRatio_pow, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith

theorem finite_weighted_collision_bound {m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : Fin m → ℝ) (nu L : ℝ) (hw : ∀ i, 0 < w i) (hnu : 0 < nu)
    (a : ι → Fin m → ℕ) (B : ι → ℕ × ℕ → ℂ)
    (C : (Fin m → ℕ) → ℕ × ℕ → ι → ℂ) (D : ℝ) (U : ι → ℝ)
    (hD : 0 ≤ D) (hU : ∀ i, 0 ≤ U i)
    (hC : ∀ a p j, ‖C a p j‖ ≤ D)
    (hB : ∀ i p, ‖B i p‖ ≤ U i * (1/2 : ℝ)^(p.1+p.2))
    (S : Finset (ℕ × ℕ)) :
    Real.exp (-nu*(∑ i, cost w (a i))) *
      ‖Matrix.det (fun i j => ∑ p : ↥S, B i p.val * C (a i) p.val j)‖ ≤
      ((Fintype.card ι).factorial * D^Fintype.card ι * ∏ i, U i) *
        Real.exp (-L*Fintype.card ι+augmentedCount (combinedWeights w nu) L) *
          ((1-quarterRatio)⁻¹)^(2*Fintype.card ι) := by
  classical
  let good := (Finset.univ : Finset (ι → ↥S)).filter
    (fun f => Function.Injective (fun i => (a i, (f i).val)))
  let Q := (Fintype.card ι).factorial * D^Fintype.card ι * ∏ i, U i
  have hQ : 0 ≤ Q := by
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hD _))
      (Finset.prod_nonneg (fun i _ => hU i))
  have hexpand : Matrix.det (fun i j => ∑ p : ↥S, B i p.val * C (a i) p.val j) =
      ∑ f ∈ good, (∏ i, B i (f i).val) * Matrix.det (fun i j => C (a i) (f i).val j) := by
    rw [FiniteDeterminantCollision.det_finite_row_sum a
      (fun i (p : ↥S) => B i p.val) (fun a p j => C a p.val j)]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro f _ hf
    have hn : ¬ Function.Injective (fun i => (a i, (f i).val)) := by simpa [good] using hf
    obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hn
    have ha : a i = a j := congrArg Prod.fst hij
    have hp : (f i).val = (f j).val := congrArg Prod.snd hij
    have hz : Matrix.det (fun i j => C (a i) (f i).val j) = 0 := by
      apply Matrix.det_zero_of_row_eq hne
      funext k
      rw [ha, hp]
    simp [hz]
  have hterm (f : ι → ↥S) :
      ‖(∏ i, B i (f i).val) * Matrix.det (fun i j => C (a i) (f i).val j)‖ ≤
        Q * (1/2 : ℝ)^(∑ i, ((f i).val.1+(f i).val.2)) := by
    have hb : (∏ i, ‖B i (f i).val‖) ≤
        ∏ i, U i * (1/2 : ℝ)^((f i).val.1+(f i).val.2) :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hB i (f i).val)
    have hc := FiniteDeterminantCollision.norm_det_le_factorial_mul_pow
      (fun i j => C (a i) (f i).val j) hD (fun i j => hC _ _ _)
    rw [norm_mul, norm_prod]
    apply (mul_le_mul hb hc (norm_nonneg _)
      (Finset.prod_nonneg (fun i _ => mul_nonneg (hU i) (by positivity)))).trans_eq
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    dsimp [Q]
    ring
  rw [hexpand]
  calc
    _ ≤ Real.exp (-nu*(∑ i, cost w (a i))) *
        ∑ f ∈ good, ‖(∏ i, B i (f i).val) * Matrix.det (fun i j => C (a i) (f i).val j)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (Real.exp_pos _).le
    _ ≤ Real.exp (-nu*(∑ i, cost w (a i))) *
        ∑ f ∈ good, Q * (1/2 : ℝ)^(∑ i, ((f i).val.1+(f i).val.2)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun f _ => hterm f)) (Real.exp_pos _).le
    _ = Q * ∑ f ∈ good, Real.exp (-nu*(∑ i, cost w (a i))) *
        (1/2 : ℝ)^(∑ i, ((f i).val.1+(f i).val.2)) := by
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      ring
    _ ≤ Q * ∑ f ∈ good,
        Real.exp (-L*Fintype.card ι+augmentedCount (combinedWeights w nu) L) *
          quarterRatio^(∑ i, ((f i).val.1+(f i).val.2)) := by
      apply mul_le_mul_of_nonneg_left _ hQ
      exact Finset.sum_le_sum (fun f hf =>
        weighted_degree_saving w nu L hw hnu a (fun i => (f i).val) (Finset.mem_filter.mp hf).2)
    _ = (Q * Real.exp (-L*Fintype.card ι+augmentedCount (combinedWeights w nu) L)) *
        ∑ f ∈ good, quarterRatio^(∑ i, ((f i).val.1+(f i).val.2)) := by
      rw [← Finset.mul_sum]
      dsimp [Q]
      ring
    _ ≤ (Q * Real.exp (-L*Fintype.card ι+augmentedCount (combinedWeights w nu) L)) *
        ∑ f : ι → ↥S, quarterRatio^(∑ i, ((f i).val.1+(f i).val.2)) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hQ (Real.exp_pos _).le)
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun f _ _ => pow_nonneg quarterRatio_pos.le _)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_pair_assignments_le S quarterRatio_pos.le quarterRatio_lt_one)
      (mul_nonneg hQ (Real.exp_pos _).le)

/-- Passing to all Taylor pairs requires their actual entrywise HasSum
identity, not an assumed determinant estimate. -/
theorem infinite_weighted_collision_bound {m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : Fin m → ℝ) (nu L : ℝ) (hw : ∀ i, 0 < w i) (hnu : 0 < nu)
    (a : ι → Fin m → ℕ) (B : ι → ℕ × ℕ → ℂ)
    (C : (Fin m → ℕ) → ℕ × ℕ → ι → ℂ) (D : ℝ) (U : ι → ℝ)
    (hD : 0 ≤ D) (hU : ∀ i, 0 ≤ U i)
    (hC : ∀ a p j, ‖C a p j‖ ≤ D)
    (hB : ∀ i p, ‖B i p‖ ≤ U i * (1/2 : ℝ)^(p.1+p.2))
    (T : Matrix ι ι ℂ) (hsum : ∀ i j, HasSum (fun p => B i p * C (a i) p j) (T i j)) :
    Real.exp (-nu*(∑ i, cost w (a i))) * ‖T.det‖ ≤
      ((Fintype.card ι).factorial * D^Fintype.card ι * ∏ i, U i) *
        Real.exp (-L*Fintype.card ι+augmentedCount (combinedWeights w nu) L) *
          ((1-quarterRatio)⁻¹)^(2*Fintype.card ι) := by
  classical
  let A (S : Finset (ℕ × ℕ)) : Matrix ι ι ℂ :=
    fun i j => ∑ p ∈ S, B i p * C (a i) p j
  have hm : Tendsto A atTop (𝓝 T) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact tendsto_pi_nhds.mpr (hsum i)
  have hd := (continuous_id.matrix_det.tendsto T).comp hm
  apply le_of_tendsto' (hd.norm.const_mul (Real.exp (-nu*(∑ i, cost w (a i)))))
  intro S
  change Real.exp (-nu*(∑ i, cost w (a i))) * ‖(A S).det‖ ≤ _
  have ha : A S = (fun i j => ∑ p : ↥S, B i p.val * C (a i) p.val j) := by
    funext i j
    change (∑ p ∈ S, B i p * C (a i) p j) = _
    rw [← Finset.sum_coe_sort]
  rw [ha]
  exact finite_weighted_collision_bound w nu L hw hnu a B C D U hD hU hC hB S

#print axioms infinite_weighted_collision_bound

end LogarithmExtension.LogRatio.TaylorPacking

import OAI.NumberTheory.PiExponent.Polynomials.SimplexRational

/-!
# Direct packing of distinct Taylor/auxiliary indices

One extra integer coordinate counts the positive deficits of any distinct
finite family of weighted indices. This avoids a separate fractional-power
collision estimate and a subsequent cubic variational estimate.
-/

noncomputable section
namespace LogarithmExtension.LogRatio.TaylorPacking

open OAI OAI.PiExponent
open scoped BigOperators

def cost {d : ℕ} (w : Fin d → ℝ) (a : Fin d → ℕ) : ℝ := ∑ i, w i * a i

def augmentedCount {d : ℕ} (w : Fin d → ℝ) (L : ℝ) : ℕ :=
  (realWeightedSimplex (Fin.cases 1 w) L).card

/-- Distinct indices can have total deficit at most the number of lattice
points in the simplex with one additional coordinate of weight one. -/
theorem deficit_le_augmentedCount {d : ℕ} {ι : Type*} [Fintype ι]
    (w : Fin d → ℝ) (hw : ∀ i, 0 < w i) (L : ℝ)
    (a : ι → Fin d → ℕ) (hinj : Function.Injective a) :
    (∑ i, (L-cost w (a i))) ≤ augmentedCount w L := by
  classical
  let good : Finset ι := Finset.univ.filter (fun i => cost w (a i) ≤ L)
  let Fiber (i : ↥good) := Fin (⌊L-cost w (a i.val)⌋₊+1)
  have hweight (i : Fin (d+1)) : (0 : ℝ) < Fin.cases 1 w i := by
    cases i using Fin.cases with
    | zero => norm_num
    | succ i => exact hw i
  let embed : (Σ i : ↥good, Fiber i) → Fin (d+1) → ℕ :=
    fun p => Fin.cases p.2.val (a p.1.val)
  have hmem (p : Σ i : ↥good, Fiber i) : embed p ∈ realWeightedSimplex (Fin.cases 1 w) L := by
      apply (mem_realWeightedSimplex hweight).mpr
      rw [Fin.sum_univ_succ]
      simp only [embed, Fin.cases_zero, Fin.cases_succ, one_mul]
      have hgood : cost w (a p.1.val) ≤ L := (Finset.mem_filter.mp p.1.property).2
      have hn : (p.2.val : ℝ) ≤ L-cost w (a p.1.val) :=
        (Nat.cast_le.mpr (Nat.le_of_lt_succ p.2.isLt)).trans
          (Nat.floor_le (sub_nonneg.mpr hgood))
      change (p.2.val : ℝ)+cost w (a p.1.val) ≤ L
      linarith
  have hembed : Function.Injective embed := by
    rintro ⟨i, ni⟩ ⟨j, nj⟩ h
    have ha : a i.val = a j.val := by
      funext k
      exact congrFun h k.succ
    have hij : i = j := Subtype.ext (hinj ha)
    subst j
    have hn : ni = nj := by
      apply Fin.ext
      exact congrFun h 0
    subst nj
    rfl
  have hcard : Fintype.card (Σ i : ↥good, Fiber i) ≤ augmentedCount w L := by
    exact Finset.card_le_card_of_injOn embed (fun p _ => hmem p) hembed.injOn
  calc
    _ ≤ ∑ i, if cost w (a i) ≤ L then L-cost w (a i) else 0 := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs with h
      · exact le_rfl
      · exact sub_nonpos.mpr (le_of_not_ge h)
    _ = ∑ i ∈ good, (L-cost w (a i)) := by simp only [good, Finset.sum_filter]
    _ ≤ ∑ i ∈ good, ((⌊L-cost w (a i)⌋₊+1 : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact_mod_cast (Nat.lt_floor_add_one (L-cost w (a i))).le
    _ = (Fintype.card (Σ i : ↥good, Fiber i) : ℝ) := by
      simp only [Fintype.card_sigma, Fiber, Fintype.card_fin, Nat.cast_sum]
      rw [← Finset.sum_coe_sort]
    _ ≤ _ := by exact_mod_cast hcard

theorem cost_sum_lower_bound {d : ℕ} {ι : Type*} [Fintype ι]
    (w : Fin d → ℝ) (hw : ∀ i, 0 < w i) (L : ℝ)
    (a : ι → Fin d → ℕ) (hinj : Function.Injective a) :
    L * Fintype.card ι - augmentedCount w L ≤ ∑ i, cost w (a i) := by
  have h := deficit_le_augmentedCount w hw L a hinj
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  linarith

def combinedWeights {m : ℕ} (w : Fin m → ℝ) (nu : ℝ) : Fin (m+2) → ℝ :=
  Fin.cases (1/4) (Fin.cases (1/4) (fun i => nu*w i))

def combinedIndex {m : ℕ} (a : Fin m → ℕ) (p : ℕ × ℕ) : Fin (m+2) → ℕ :=
  Fin.cases p.1 (Fin.cases p.2 a)

theorem combinedWeights_pos {m : ℕ} (w : Fin m → ℝ) (nu : ℝ)
    (hw : ∀ i, 0 < w i) (hnu : 0 < nu) : ∀ i, 0 < combinedWeights w nu i := by
  intro i
  cases i using Fin.cases with
  | zero => norm_num [combinedWeights]
  | succ i =>
    cases i using Fin.cases with
    | zero => change (0 : ℝ) < 1/4; norm_num
    | succ i => exact mul_pos hnu (hw i)

theorem cost_combinedIndex {m : ℕ} (w : Fin m → ℝ) (nu : ℝ)
    (a : Fin m → ℕ) (p : ℕ × ℕ) :
    cost (combinedWeights w nu) (combinedIndex a p) =
      nu*cost w a + (p.1+p.2 : ℕ)/4 := by
  simp only [cost, combinedWeights, combinedIndex, Fin.sum_univ_succ,
    Fin.cases_zero, Fin.cases_succ, Nat.cast_add, mul_assoc, ← Finset.mul_sum]
  ring

theorem combinedIndex_injective {m : ℕ} {ι : Type*}
    (a : ι → Fin m → ℕ) (p : ι → ℕ × ℕ)
    (hinj : Function.Injective (fun i => (a i, p i))) :
    Function.Injective (fun i => combinedIndex (a i) (p i)) := by
  intro i j h
  apply hinj
  apply Prod.ext
  · funext k
    exact congrFun h k.succ.succ
  · apply Prod.ext
    · exact congrFun h 0
    · exact congrFun h 1

theorem combined_cost_lower_bound {m : ℕ} {ι : Type*} [Fintype ι]
    (w : Fin m → ℝ) (nu L : ℝ) (hw : ∀ i, 0 < w i) (hnu : 0 < nu)
    (a : ι → Fin m → ℕ) (p : ι → ℕ × ℕ)
    (hinj : Function.Injective (fun i => (a i, p i))) :
    L * Fintype.card ι - augmentedCount (combinedWeights w nu) L ≤
      nu*(∑ i, cost w (a i)) + ((∑ i, ((p i).1+(p i).2) : ℕ) : ℝ)/4 := by
  have h := cost_sum_lower_bound (combinedWeights w nu) (combinedWeights_pos w nu hw hnu) L
    (fun i => combinedIndex (a i) (p i)) (combinedIndex_injective a p hinj)
  simpa only [cost_combinedIndex, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.sum_div, Nat.cast_sum, Nat.cast_add] using h

#print axioms cost_sum_lower_bound
#print axioms combined_cost_lower_bound

end LogarithmExtension.LogRatio.TaylorPacking

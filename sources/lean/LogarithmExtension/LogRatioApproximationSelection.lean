import Mathlib

/-!
# Reduced exceptional fractions with successive logarithmic weights

The selection is generic for a real target strictly between one and two.
Rational numbers, rather than arbitrary integer pairs, enforce reduction.
-/

noncomputable section
namespace LogarithmExtension.LogRatio.ApproximationSelection

open Filter
open scoped Topology BigOperators

def UnboundedExceptional (theta nu : ℝ) : Prop :=
  ∀ Q : ℕ, ∃ r : ℚ, Q ≤ r.den ∧ |theta-(r : ℝ)| ≤ (r.den : ℝ)^(-nu)

def weight (r : ℚ) : ℝ := (Nat.ceil (Real.log r.den) : ℝ)

theorem exists_large_reduced (theta nu : ℝ) (htheta1 : 1 < theta) (htheta2 : theta < 2)
    (hnu : 0 < nu) (hbad : UnboundedExceptional theta nu) (Q : ℕ) (X : ℝ) :
    ∃ r : ℚ, Q ≤ r.den ∧ 1 < (r : ℝ) ∧ (r : ℝ) < 2 ∧ X < weight r ∧
      |theta-(r : ℝ)| ≤ (r.den : ℝ)^(-nu) := by
  let delta : ℝ := min (theta-1) (2-theta)
  have hd : 0 < delta := lt_min (by linarith) (by linarith)
  have he := ((tendsto_rpow_neg_atTop hnu).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (gt_mem_nhds hd)
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  obtain ⟨B, hB⟩ := exists_nat_gt (Real.exp X)
  obtain ⟨r, hr, happ⟩ := hbad (max Q (max N (max 2 B)))
  have hqQ : Q ≤ r.den := (le_max_left _ _).trans hr
  have hqN : N ≤ r.den := ((le_max_left _ _).trans (le_max_right _ _)).trans hr
  have hqB : B ≤ r.den := ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))).trans hr
  have hsmall : |theta-(r : ℝ)| < delta := happ.trans_lt (hN r.den hqN)
  have h1 : 1 < (r : ℝ) := by
    have hh := (abs_lt.mp hsmall).2
    have hd1 : delta ≤ theta-1 := min_le_left _ _
    linarith
  have h2 : (r : ℝ) < 2 := by
    have hh := (abs_lt.mp hsmall).1
    have hd2 : delta ≤ 2-theta := min_le_right _ _
    linarith
  have hexp : Real.exp X < (r.den : ℝ) := hB.trans_le (by exact_mod_cast hqB)
  have hlog : X < Real.log r.den := by
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos X) hexp
  exact ⟨r, hqQ, h1, h2, hlog.trans_le (Nat.le_ceil _), happ⟩

theorem exists_successive_reduced (theta nu : ℝ) (htheta1 : 1 < theta) (htheta2 : theta < 2)
    (hnu : 0 < nu) (hbad : UnboundedExceptional theta nu) (Q : ℕ) (T : List ℝ → ℝ) :
    ∃ r : ℕ → ℚ, ∀ n, Q ≤ (r n).den ∧ 1 < (r n : ℝ) ∧ (r n : ℝ) < 2 ∧
      |theta-(r n : ℝ)| ≤ ((r n).den : ℝ)^(-nu) ∧ 1 ≤ weight (r n) ∧
      T (((List.range n).reverse).map (fun i => weight (r i))) < weight (r n) := by
  classical
  let Good : ℚ → Prop := fun r => Q ≤ r.den ∧ 1 < (r : ℝ) ∧ (r : ℝ) < 2 ∧
    |theta-(r : ℝ)| ≤ (r.den : ℝ)^(-nu) ∧ 1 ≤ weight r
  have hex (L : List ℚ) : ∃ r : ℚ, Good r ∧ T (L.map weight) < weight r := by
    obtain ⟨r, hq, h1, h2, hw, happ⟩ := exists_large_reduced theta nu htheta1 htheta2
      hnu hbad Q (max 1 (T (L.map weight)))
    exact ⟨r, ⟨hq, h1, h2, happ, ((le_max_left _ _).trans hw.le)⟩,
      (le_max_right _ _).trans_lt hw⟩
  let next : List ℚ → ℚ := fun L => (hex L).choose
  have hnext (L : List ℚ) : Good (next L) ∧ T (L.map weight) < weight (next L) :=
    (hex L).choose_spec
  let hist : ℕ → List ℚ := Nat.rec [] (fun _ L => next L :: L)
  let r : ℕ → ℚ := fun n => next (hist n)
  have hhist (n : ℕ) : hist n = (List.range n).reverse.map r := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change r n :: hist n = (List.range (n+1)).reverse.map r
      rw [ih]
      simp [List.range_succ, List.reverse_append]
  refine ⟨r, fun n => ?_⟩
  have hg : Good (r n) := (hnext (hist n)).1
  refine ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2, ?_⟩
  have hb := (hnext (hist n)).2
  have hmap : (hist n).map weight =
      (List.range n).reverse.map (fun i => weight (r i)) := by
    rw [hhist, List.map_map]
    rfl
  rw [hmap] at hb
  exact hb

theorem reverse_weight_prod (r : ℕ → ℚ) (n : ℕ) :
    (((List.range n).reverse).map (fun i => weight (r i))).prod =
      ∏ j ∈ Finset.range n, weight (r j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.reverse_append]
    simp only [List.reverse_singleton, List.map_append, List.map_singleton,
      List.prod_append, List.prod_cons, List.prod_nil, mul_one]
    rw [Finset.prod_range_succ, ih]
    exact mul_comm _ _

def normalizedWeight (r : ℕ → ℚ) : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | n+2 => weight (r n)

theorem normalized_prefix_prod (r : ℕ → ℚ) (n : ℕ) :
    (∏ j ∈ Finset.range (n+2), normalizedWeight r j) =
      ∏ j ∈ Finset.range n, weight (r j) := by
  induction n with
  | zero => simp [Finset.prod_range_succ, normalizedWeight]
  | succ n ih =>
    rw [show n+1+2 = (n+2)+1 by omega, Finset.prod_range_succ, ih,
      Finset.prod_range_succ]
    rfl

theorem exists_growing_reduced (theta nu : ℝ) (htheta1 : 1 < theta) (htheta2 : theta < 2)
    (hnu : 0 < nu) (hbad : UnboundedExceptional theta nu) (Q : ℕ) (X D : ℝ) :
    ∃ r : ℕ → ℚ,
      (∀ n, Q ≤ (r n).den ∧ 1 < (r n : ℝ) ∧ (r n : ℝ) < 2 ∧
        |theta-(r n : ℝ)| ≤ ((r n).den : ℝ)^(-nu) ∧ X < weight (r n)) ∧
      (∀ i, 1 ≤ normalizedWeight r i) ∧
      (∀ i, 2 ≤ i → D*(∏ j ∈ Finset.range i, normalizedWeight r j) < normalizedWeight r i) := by
  obtain ⟨r, hr⟩ := exists_successive_reduced theta nu htheta1 htheta2 hnu hbad Q
    (fun L => max X (D*L.prod))
  refine ⟨r, ?_, ?_, ?_⟩
  · intro n
    exact ⟨(hr n).1, (hr n).2.1, (hr n).2.2.1, (hr n).2.2.2.1,
      (le_max_left _ _).trans_lt (hr n).2.2.2.2.2⟩
  · intro i
    rcases i with _ | (_ | n)
    · exact le_rfl
    · exact le_rfl
    · exact (hr n).2.2.2.2.1
  · intro i hi
    rcases i with _ | (_ | n)
    · omega
    · omega
    · have h := (le_max_right _ _).trans_lt (hr n).2.2.2.2.2
      rw [reverse_weight_prod, ← normalized_prefix_prod] at h
      exact h

theorem positive_numerator_representation (r : ℚ) (hr : (0 : ℝ) < r) :
    (r.num.natAbs : ℝ)/(r.den : ℝ) = (r : ℝ) := by
  have hp : 0 ≤ r.num := (Rat.num_pos.mpr (by exact_mod_cast hr)).le
  have he : (r.num.natAbs : ℝ) = (r.num : ℝ) := by
    rw [Nat.cast_natAbs, abs_of_nonneg hp]
  rw [he, Rat.cast_def]

#print axioms exists_growing_reduced

end LogarithmExtension.LogRatio.ApproximationSelection

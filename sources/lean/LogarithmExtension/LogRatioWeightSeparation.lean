import Mathlib
import OAI.NumberTheory.PiExponent.Approximation.WeightSeparationProducts

/-!
# Two-base separated weights

A single finite constant controls all normal-basis products in a fixed
dimension. It is chosen before any exceptional approximation denominators.
-/

noncomputable section
namespace LogarithmExtension.LogRatio.WeightSeparation

open scoped BigOperators

def lowScale (w0 : ℝ) : ℝ := min w0 1
def highScale (v0 v : ℝ) : ℝ := max v0 (1/v)
def separationFactor (d : ℕ) (epsilon w0 v0 v : ℝ) : ℝ :=
  1 + ∑ k ∈ Finset.range (d+1), (k : ℝ)^k*(1/epsilon)^k*(highScale v0 v/lowScale w0)^k

def degreeWeight (w0 : ℝ) (x : ℕ → ℝ) (i : ℕ) : ℝ := if i < 2 then w0 else x i
def jetWeight (v0 v : ℝ) (x : ℕ → ℝ) (i : ℕ) : ℝ := if i < 2 then v0 else x i/v

theorem lowScale_pos {w0 : ℝ} (hw0 : 0 < w0) : 0 < lowScale w0 := lt_min hw0 zero_lt_one
theorem highScale_pos {v0 v : ℝ} (hv0 : 0 < v0) : 0 < highScale v0 v :=
  hv0.trans_le (le_max_left _ _)

theorem separationFactor_pos (d : ℕ) (epsilon w0 v0 v : ℝ)
    (hepsilon : 0 < epsilon) (hw0 : 0 < w0) (hv0 : 0 < v0) :
    0 < separationFactor d epsilon w0 v0 v := by
  have hL := lowScale_pos hw0
  have hR := highScale_pos (v := v) hv0
  unfold separationFactor
  have hs : 0 ≤ ∑ k ∈ Finset.range (d+1),
      (k : ℝ)^k*(1/epsilon)^k*(highScale v0 v/lowScale w0)^k := by
    apply Finset.sum_nonneg
    intro k _
    positivity
  linarith

theorem coefficient_le_factor (d k : ℕ) (epsilon w0 v0 v : ℝ)
    (hepsilon : 0 < epsilon) (hw0 : 0 < w0) (hv0 : 0 < v0) (hk : k ≤ d) :
    (k : ℝ)^k*(1/epsilon)^k*(highScale v0 v/lowScale w0)^k ≤
      separationFactor d epsilon w0 v0 v := by
  have hL := lowScale_pos hw0
  have hR := highScale_pos (v := v) hv0
  have hs : (k : ℝ)^k*(1/epsilon)^k*(highScale v0 v/lowScale w0)^k ≤
      ∑ j ∈ Finset.range (d+1), (j : ℝ)^j*(1/epsilon)^j*(highScale v0 v/lowScale w0)^j := by
    apply Finset.single_le_sum (f := fun j : ℕ =>
      (j : ℝ)^j*(1/epsilon)^j*(highScale v0 v/lowScale w0)^j)
    · intro j _
      positivity
    · exact Finset.mem_range.mpr (by omega)
  unfold separationFactor
  linarith

theorem geometric_products_separated
    (d : ℕ) (epsilon w0 v0 v : ℝ) (x : ℕ → ℝ)
    (hepsilon : 0 < epsilon) (hw0 : 0 < w0) (hv0 : 0 < v0) (hv : 0 < v)
    (hxbase : ∀ i, i < 2 → x i = 1) (hx : ∀ i, 1 ≤ x i)
    (hgrowth : ∀ i, 2 ≤ i → separationFactor d epsilon w0 v0 v *
      (∏ j ∈ Finset.range i, x j) < x i)
    (A B : Finset ℕ) (hcard : A.card = B.card) (hbound : B.card ≤ d)
    (i : ℕ) (hi : 2 ≤ i) (hiA : i ∈ A) (hiB : i ∉ B)
    (hbelow : ∀ j ∈ B \ A, j < i) :
    (A.card : ℝ)^A.card*(1/epsilon)^A.card*(∏ j ∈ B, jetWeight v0 v x j) <
      ∏ j ∈ A, degreeWeight w0 x j := by
  let L := lowScale w0
  let R := highScale v0 v
  let D := separationFactor d epsilon w0 v0 v
  have hL : 0 < L := lowScale_pos hw0
  have hR : 0 < R := highScale_pos hv0
  have hD : 0 < D := separationFactor_pos d epsilon w0 v0 v hepsilon hw0 hv0
  have hxpos (j : ℕ) : 0 < x j := zero_lt_one.trans_le (hx j)
  have hdeg (j : ℕ) : L*x j ≤ degreeWeight w0 x j := by
    by_cases hj : j < 2
    · simp only [degreeWeight, ite_eq_left hj, hxbase j hj, mul_one]
      exact min_le_left _ _
    · rw [degreeWeight, ite_eq_right hj]
      exact mul_le_of_le_one_left (hxpos j).le (min_le_right _ _)
  have hjet (j : ℕ) : jetWeight v0 v x j ≤ R*x j := by
    by_cases hj : j < 2
    · simp only [jetWeight, ite_eq_left hj, hxbase j hj, mul_one]
      exact le_max_left _ _
    · rw [jetWeight, ite_eq_right hj]
      calc
        x j/v = (1/v)*x j := by ring
        _ ≤ R*x j := mul_le_mul_of_nonneg_right (le_max_right _ _) (hxpos j).le
  have hjnonneg (j : ℕ) : 0 ≤ jetWeight v0 v x j := by
    unfold jetWeight
    split
    · exact hv0.le
    · exact (div_pos (hxpos j) hv).le
  have hdprod : L^A.card*(∏ j ∈ A, x j) ≤ ∏ j ∈ A, degreeWeight w0 x j := by
    calc
      _ = ∏ j ∈ A, L*x j := by rw [Finset.prod_mul_distrib, Finset.prod_const]
      _ ≤ _ := Finset.prod_le_prod₀ (fun j _ => mul_nonneg hL.le (hxpos j).le)
        (fun j _ => hdeg j)
  have hjprod : (∏ j ∈ B, jetWeight v0 v x j) ≤ R^B.card*(∏ j ∈ B, x j) := by
    calc
      _ ≤ ∏ j ∈ B, R*x j := Finset.prod_le_prod₀ (fun j _ => hjnonneg j) (fun j _ => hjet j)
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const]
  have hcoef : (A.card : ℝ)^A.card*(1/epsilon)^A.card*R^B.card ≤ L^A.card*D := by
    rw [hcard]
    calc
      _ = L^B.card*((B.card : ℝ)^B.card*(1/epsilon)^B.card*(R/L)^B.card) := by
        rw [div_pow R L]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (coefficient_le_factor d B.card epsilon w0 v0 v hepsilon hw0 hv0 hbound)
        (pow_pos hL _).le
  have hsep := OAI.PiExponent.normalized_products_separated x D hx hD A B i hiA hiB hbelow
    (hgrowth i hi)
  have hcpos : 0 ≤ (A.card : ℝ)^A.card*(1/epsilon)^A.card := by positivity
  have hpB : 0 ≤ ∏ j ∈ B, x j := Finset.prod_nonneg (fun j _ => (hxpos j).le)
  calc
    _ ≤ ((A.card : ℝ)^A.card*(1/epsilon)^A.card)*(R^B.card*(∏ j ∈ B, x j)) :=
      mul_le_mul_of_nonneg_left hjprod hcpos
    _ = ((A.card : ℝ)^A.card*(1/epsilon)^A.card*R^B.card)*(∏ j ∈ B, x j) := by ring
    _ ≤ (L^A.card*D)*(∏ j ∈ B, x j) := mul_le_mul_of_nonneg_right hcoef hpB
    _ = L^A.card*(D*(∏ j ∈ B, x j)) := by ring
    _ < L^A.card*(∏ j ∈ A, x j) := mul_lt_mul_of_pos_left hsep (pow_pos hL _)
    _ ≤ _ := hdprod

theorem fin_products_separated (m : ℕ) (epsilon w0 v0 v : ℝ) (x : ℕ → ℝ)
    (hepsilon : 0 < epsilon) (hw0 : 0 < w0) (hv0 : 0 < v0) (hv : 0 < v)
    (hxbase : ∀ i, i < 2 → x i = 1) (hx : ∀ i, 1 ≤ x i)
    (hgrowth : ∀ i, 2 ≤ i → separationFactor (m+2) epsilon w0 v0 v *
      (∏ j ∈ Finset.range i, x j) < x i)
    (A B : Finset (Fin (m+2))) (hcard : A.card = B.card)
    (i : Fin (m+2)) (hi : 2 ≤ i.val) (hiA : i ∈ A) (hiB : i ∉ B)
    (habove : ∀ j, i < j → (j ∈ A ↔ j ∈ B)) :
    (A.card : ℝ)^A.card*(1/epsilon)^A.card*(∏ j ∈ B, jetWeight v0 v x j.val) <
      ∏ j ∈ A, degreeWeight w0 x j.val := by
  let e : Fin (m+2) ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  have hbelow : ∀ j ∈ B.map e \ A.map e, j < i.val := by
    intro j hj
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp (Finset.mem_sdiff.mp hj).1
    have hbA : b ∉ A := by
      intro hh
      exact (Finset.mem_sdiff.mp hj).2 (Finset.mem_map.mpr ⟨b, hh, rfl⟩)
    by_contra hn
    have hne : b ≠ i := by intro he; subst b; exact hiB hb
    have hbi : i < b := by
      apply Fin.lt_def.mpr
      have hneval : b.val ≠ i.val := fun h => hne (Fin.ext h)
      change ¬ b.val < i.val at hn
      omega
    exact hbA ((habove b hbi).mpr hb)
  have hbnd : (B.map e).card ≤ m+2 := by
    simpa only [Finset.card_map, Fintype.card_fin] using Finset.card_le_univ B
  have hh := geometric_products_separated (m+2) epsilon w0 v0 v x hepsilon hw0 hv0 hv
    hxbase hx hgrowth (A.map e) (B.map e) (by simpa using hcard) hbnd i.val hi
    (Finset.mem_map.mpr ⟨i, hiA, rfl⟩) (by
      intro hm
      obtain ⟨j, hj, hji⟩ := Finset.mem_map.mp hm
      have he : j = i := Fin.ext hji
      exact hiB (he ▸ hj)) hbelow
  simpa only [Finset.card_map, Finset.prod_map, e, Function.Embedding.coeFn_mk] using hh

#print axioms fin_products_separated

end LogarithmExtension.LogRatio.WeightSeparation

import Lean
import Lean.Replay

/-!
Fresh-kernel verification of THE UPPER BOUND THREE FOR log(3)/log(2),
including the full two-base geometry, determinant and parameter construction.
The literal endpoint is an eventual lower approximation bound for every
integer numerator and sufficiently large natural denominator, and yields
2 <= mu(log(3)/log(2)) <= 3. No equality with three is asserted.
The persistence endpoint derives its comparison; its actual
polynomial, vanishing and separated-weight hypotheses remain explicit.
The actual formal jets and centered-branch contact are now constructed,
including the q-fold comparison for a primitive torus character.
The full curve inequality now derives persistence and rigidity from excess
actual contact, and closes both the nonconstant- and constant-base cases.
Its intrinsic endpoint derives the residue, finiteness and height inputs.
The actual local ideal lengths, finite support and exceptional degrees are
identified with the contacts in that curve inequality. All integral curve
cases give a uniform margin, proving ampleness and eventual jet restriction.
The polynomial lift has the required weighted-degree bound. A fixed two-base
truncation preserves packet rank and yields a nonzero full-row minor of the
concrete truncated matrix. None of those endpoints assumes interpolation,
ampleness, matrix rank, or a nonzero determinant as additional hypotheses.
The actual matrix entries become integers after the prescribed denominator,
row and column scaling. Their nonzero minors satisfy the normalized
arithmetic lower bound. A combined endpoint derives both nonvanishing and
that lower bound from explicit geometric data and weight identities.
The exact finite row/determinant translation, the mixed-tail order budget,
bivariate scalar norm bounds and polynomial choice counts are also checked.
They concern the same concrete matrix and its prescribed truncation orders.
Direct weighted Taylor packing, the actual two-variable coefficient series,
the uniform coefficient bounds and the determinant upper bound are checked.
The counting limits and all overhead limits connect both bounds for the same
nonzero minors to a fixed-data numerical necessary inequality. Rational seed
parameters, the simultaneous finite-dimension choice for every rational nu > 3,
exact packing-density cancellation, and the determinant contradiction are included.
Reduced exceptional fractions are selected with separated auxiliary weights
and assembled into GeometryData. Rational exponents are extended to all real
exponents above three; unreduced fractions are covered using a finite exceptional
set and the target's independently proved irrationality.

Run sequentially, without rebuilding imports during the replay:
  lake build LogarithmExtension.LogRatioMain LogarithmExtension.LogRatioAverageAudit
  lake env lean --run VerifyLogRatioComponents.lean

The dependency-closure traversal adapts VerifyGeneralLog.lean. No axioms
other than propext, Classical.choice and Quot.sound are accepted.
-/

open Lean

def ratioComponentRoots : Array Name := #[
  `LogarithmExtension.LogRatio.TwoBaseFrame.normal_basis_dichotomy,
  `LogarithmExtension.LogRatio.TwoBaseFrame.differential_of_tangent,
  `LogarithmExtension.LogRatio.TorusRigidity.constants_of_relation,
  `LogarithmExtension.LogRatio.NormalComparison.not_all_aux_tangent,
  `LogarithmExtension.LogRatio.NormalComparison.exists_tangent_relation,
  `LogarithmExtension.LogRatio.ComponentRigidity.constants_of_weight_comparison,
  `LogarithmExtension.LogRatio.PolynomialFrame.frame_commute,
  `LogarithmExtension.LogRatio.PolynomialFrame.degree_word,
  `LogarithmExtension.LogRatio.PolynomialFrame.exists_persistent_component,
  `LogarithmExtension.LogRatio.ResidueDirections.frame_eq_basis_dot,
  `LogarithmExtension.LogRatio.TransverseMultiplicity.prime_rectangular_length_lower,
  `LogarithmExtension.LogRatio.WeightedComparison.comparison_of_normal_basis,
  `LogarithmExtension.LogRatio.WeightedComparison.comparison_of_normal_bases,
  `LogarithmExtension.LogRatio.PersistentRigidity.constants_of_derivative_persistence,
  `LogarithmExtension.LogRatio.PersistentRigidity.exists_rigid_persistent_component,
  `LogarithmExtension.LogRatio.ScalingAudit.line_aligned_bound,
  `LogarithmExtension.LogRatio.ScalingAudit.high_index_gain_forces_shape,
  `LogarithmExtension.LogRatio.CurveRelations.polynomial_relations_of_rigid_component,
  `LogarithmExtension.LogRatio.CurveRelations.branch_center_index_unique,
  `LogarithmExtension.LogRatio.MonomialParameter.parameter_eqs,
  `LogarithmExtension.LogRatio.ParameterContact.power_difference_valuation,
  `LogarithmExtension.LogRatio.ParameterContact.contact_sum_power_coordinate,
  `LogarithmExtension.LogRatio.ParameterCenters.parameter_contact_order,
  `LogarithmExtension.LogRatio.ParameterCenters.contact_sum_primitive_character,
  `LogarithmExtension.LogRatio.FormalJet.formalJet_word_vanishing,
  `LogarithmExtension.LogRatio.FormalJet.eventually_exists_auxiliaryPolynomial_nat,
  `LogarithmExtension.LogRatio.BranchEvaluation.formalJet_subst,
  `LogarithmExtension.LogRatio.BranchEvaluation.word_order_toNat_lower,
  `LogarithmExtension.LogRatio.PlaceContact.word_field_order_lower,
  `LogarithmExtension.LogRatio.PlaceContact.primitive_character_contact_sum,
  `LogarithmExtension.LogRatio.ContactFamily.word_order_lower,
  `LogarithmExtension.LogRatio.ConstantBases.aux_contact_sum,
  `LogarithmExtension.LogRatio.CurveInequality.logarithmic_words_vanish,
  `LogarithmExtension.LogRatio.CurveInequality.excess_implies_character,
  `LogarithmExtension.LogRatio.CurveInequality.no_excess_of_character,
  `LogarithmExtension.LogRatio.CurveInequality.weighted_curve_inequality,
  `LogarithmExtension.LogRatio.CurveInequality.weighted_curve_inequality_intrinsic,
  `LogarithmExtension.LogRatio.AlgebraicJet.polynomialEquiv,
  `LogarithmExtension.LogRatio.AlgebraicJet.radical_powerIdeal,
  `LogarithmExtension.LogRatio.AlgebraicJet.truncatedJet_packet_surjective,
  `LogarithmExtension.LogRatio.AlgebraicJet.formalJet_packet_zero_of_mem_pow,
  `LogarithmExtension.LogRatio.AlgebraicJet.formalJet_packet_surjective,
  `LogarithmExtension.LogRatio.ContactLength.contact_truncatedCoordinates_eq,
  `LogarithmExtension.LogRatio.ContactLength.colength_eq_contact,
  `LogarithmExtension.LogRatio.ContactLength.place_colength_eq_contact,
  `LogarithmExtension.LogRatio.JetIdeal.zeroLocus_polynomialIdeal,
  `LogarithmExtension.LogRatio.JetIdeal.formalJet_packet_zero_of_mem_pow,
  `LogarithmExtension.LogRatio.JetIdeal.map_polynomialIdeal_eq_selected,
  `LogarithmExtension.LogRatio.JetIdeal.map_polynomialIdeal_eq_top_outside,
  `LogarithmExtension.LogRatio.JetIdeal.place_product_colength_eq_contact,
  `LogarithmExtension.LogRatio.JetIdeal.restrict_compactIdeal,
  `LogarithmExtension.LogRatio.JetIdeal.support_compactIdeal,
  `LogarithmExtension.LogRatio.JetIdeal.compactIdeal_isFinitePresentation,
  `LogarithmExtension.LogRatio.JetPackets.formalJet_packets_surjective,
  `LogarithmExtension.LogRatio.JetPackets.surjective_of_jetRestriction,
  `LogarithmExtension.LogRatio.CenterIdentification.centered_of_closedPoint_eq,
  `LogarithmExtension.LogRatio.ExceptionalDegree.compactIdeal_comap_ne_bot_of_generic,
  `LogarithmExtension.LogRatio.ExceptionalDegree.localIdeal_length_eq_contact,
  `LogarithmExtension.LogRatio.ExceptionalDegree.compactIdeal_degree_eq_neg_contact_sum,
  `LogarithmExtension.LogRatio.ExceptionalDegree.geometry_degree_eq_neg_contactSum,
  `LogarithmExtension.LogRatio.GeometryData.curve_inequality,
  `LogarithmExtension.LogRatio.BlowupGeometry.formalJet_packet_zero,
  `LogarithmExtension.LogRatio.BlowupGeometry.uniform_curve_margin,
  `LogarithmExtension.LogRatio.BlowupGeometry.interpolationBundle_ample,
  `LogarithmExtension.LogRatio.JetSurjectivity.eventual_jetRestriction_surjective,
  `LogarithmExtension.LogRatio.WeightedInterpolation.eventually_packetMap_surjective,
  `LogarithmExtension.LogRatio.WeightedInterpolation.cofinal_packetMap_surjective,
  `LogarithmExtension.LogRatio.Truncation.shiftEquiv,
  `LogarithmExtension.LogRatio.Truncation.packets_surjective_iff_truncated,
  `LogarithmExtension.LogRatio.BoundedJetMatrix.eventually_surjective,
  `LogarithmExtension.LogRatio.BoundedJetMatrix.eventually_nonzero_minor,
  `LogarithmExtension.LogRatio.DenominatorClearing.coeff_diagonal,
  `LogarithmExtension.LogRatio.DenominatorClearing.exists_cleared_log_trunc_integer,
  `LogarithmExtension.LogRatio.MatrixArithmetic.rescaled_forward,
  `LogarithmExtension.LogRatio.MatrixArithmetic.scaled_entry_integral,
  `LogarithmExtension.LogRatio.MatrixArithmetic.matrix_entry_cleared_integer,
  `LogarithmExtension.LogRatio.MatrixArithmetic.determinant_log_lower_bound,
  `LogarithmExtension.LogRatio.ArithmeticBound.truncation_conditions,
  `LogarithmExtension.LogRatio.ArithmeticBound.normalized_determinant_lower_bound,
  `LogarithmExtension.LogRatio.ArithmeticBound.eventually_nonzero_minor_with_lower_bound,
  `LogarithmExtension.LogRatio.NestedJets.coeff_split,
  `LogarithmExtension.LogRatio.NestedJets.split_forward_monomial,
  `LogarithmExtension.LogRatio.AnalyticTranslation.matrix_entry_translation,
  `LogarithmExtension.LogRatio.AnalyticTranslation.determinant_translation,
  `LogarithmExtension.LogRatio.AnalyticTranslation.mixedTail_weight_budget,
  `LogarithmExtension.LogRatio.AnalyticTranslation.rowScalar_eq_sum_refined,
  `LogarithmExtension.LogRatio.AnalyticTranslation.norm_coeff_mixedTail_product_le,
  `LogarithmExtension.LogRatio.AnalyticTranslation.norm_choiceScalar_le,
  `LogarithmExtension.LogRatio.AnalyticTranslation.choiceFamily_card_le,
  `LogarithmExtension.LogRatio.AnalyticTranslation.norm_product_choiceScalar_le,
  `LogarithmExtension.LogRatio.TaylorPacking.cost_sum_lower_bound,
  `LogarithmExtension.LogRatio.TaylorPacking.combined_cost_lower_bound,
  `LogarithmExtension.LogRatio.TaylorPacking.infinite_weighted_collision_bound,
  `LogarithmExtension.LogRatio.TaylorPacking.tendsto_combinedCount_per_row_degree,
  `LogarithmExtension.LogRatio.TaylorPacking.meanRowWeight_le,
  `LogarithmExtension.LogRatio.CommonTaylor.baseMonomial_expansion,
  `LogarithmExtension.LogRatio.CommonTaylor.hasSum_commonImage,
  `LogarithmExtension.LogRatio.CommonTaylor.norm_columnCoefficient_le,
  `LogarithmExtension.LogRatio.CommonTaylor.hasSum_choiceEntry,
  `LogarithmExtension.LogRatio.CommonTaylor.weighted_choiceMatrix_bound,
  `LogarithmExtension.LogRatio.DeterminantAnalytic.norm_selectedMinor_le,
  `LogarithmExtension.LogRatio.DeterminantAnalytic.normalized_determinant_upper_bound,
  `LogarithmExtension.LogRatio.DeterminantComparison.tendsto_realAnalyticRemainder,
  `LogarithmExtension.LogRatio.DeterminantComparison.finite_necessary_inequality,
  `LogarithmExtension.LogRatio.DeterminantComparison.fixed_data_necessary_inequality,
  `LogarithmExtension.LogRatio.ParameterSeeds.exists_seed,
  `LogarithmExtension.LogRatio.ParameterDimension.volume_identity,
  `LogarithmExtension.LogRatio.ParameterDimension.inflated_volume_lt_one,
  `LogarithmExtension.LogRatio.ParameterDimension.eventually_small_error,
  `LogarithmExtension.LogRatio.ParameterDimension.eventually_base_gap,
  `LogarithmExtension.LogRatio.ParameterChoice.lambda_power,
  `LogarithmExtension.LogRatio.ParameterChoice.exists_seed_and_choice,
  `LogarithmExtension.LogRatio.PackingCancellation.packingLimit_eq,
  `LogarithmExtension.LogRatio.PackingCancellation.optimal_packingLimit,
  `LogarithmExtension.LogRatio.PackingCancellation.chosen_root_identity,
  `LogarithmExtension.LogRatio.ParameterContradiction.exists_auxiliary_threshold,
  `LogarithmExtension.LogRatio.ParameterContradiction.no_data_with_small_weight_error,
  `LogarithmExtension.LogRatio.ApproximationSelection.exists_growing_reduced,
  `LogarithmExtension.LogRatio.WeightSeparation.fin_products_separated,
  `LogarithmExtension.LogRatio.AdmissibleData.not_unbounded_exceptional,
  `LogarithmExtension.LogRatio.Main.ratioTheta_irrational,
  `LogarithmExtension.LogRatio.Main.finite_good_approximations,
  `LogarithmExtension.LogRatio.Main.logRatio_eventual_lower_bound,
  `LogarithmExtension.LogRatio.Main.logRatio_irrationalityExponent_bounds,
  `LogarithmExtension.LogRatio.Main.logRatio_approximation_bound,
  `LogarithmExtension.LogRatio.AverageAudit.averaged_line_bound,
  `LogarithmExtension.LogRatio.AverageAudit.no_averaged_line_ledger]

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let sourceEnv ← importModules #[
    { module := `LogarithmExtension.LogRatioArithmeticBound },
    { module := `LogarithmExtension.LogRatioDeterminantComparison },
    { module := `LogarithmExtension.LogRatioParameterContradiction },
    { module := `LogarithmExtension.LogRatioMain },
    { module := `LogarithmExtension.LogRatioAverageAudit }] {}
  let mut pending := ratioComponentRoots
  let mut selected : Std.HashMap Name ConstantInfo := {}
  let permitted : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if selected.contains name then
      continue
    let some info := sourceEnv.find? name |
      throw <| IO.userError s!"Missing dependency {name}"
    if info.isUnsafe || info.isPartial then
      throw <| IO.userError s!"Unsafe or partial dependency {name}"
    if info matches .axiomInfo _ then
      unless permitted.contains name do
        throw <| IO.userError s!"Nonstandard axiom {name}"
    selected := selected.insert name info
    for dependency in info.getUsedConstantsAsSet do
      pending := pending.push dependency
    match info with
    | .defnInfo value => pending := pending ++ value.all.toArray
    | .thmInfo value => pending := pending ++ value.all.toArray
    | .inductInfo value => pending := pending ++ value.all.toArray ++ value.ctors.toArray
    | .ctorInfo value => pending := pending.push value.induct
    | .recInfo value => pending := pending ++ value.all.toArray
    | .quotInfo _ => pending := pending.push `Eq
    | _ => pure ()
  IO.println s!"Replaying {selected.size} dependencies of {ratioComponentRoots.size} geometry/determinant/upper-bound roots."
  (← IO.getStdout).flush
  let fresh ← mkEmptyEnvironment
  let checked ← fresh.toKernelEnv.replay selected
  for name in ratioComponentRoots do
    unless (checked.find? name).isSome do
      throw <| IO.userError s!"Component absent after replay: {name}"
  IO.println "PASS: two-base derivatives, multiplicity, persistent rigidity, actual jets, branch contact and q-fold comparison."
  IO.println "PASS: full two-base curve inequality, both curve cases and intrinsic function-field endpoint."
  IO.println "PASS: algebraic jet ideals, ideal-power vanishing and local packets without a degree bound."
  IO.println "PASS: two-tail contact invariance, actual local lengths, finite support and exceptional degrees."
  IO.println "PASS: actual curve degree margin, ampleness, global restriction and bounded weighted interpolation."
  IO.println "PASS: fixed-truncation packet equivalence and nonzero minors of the concrete two-base matrix."
  IO.println "PASS: exact row/column rescaling and integer entries after common denominator clearing."
  IO.println "PASS: normalized arithmetic lower bound for that determinant, with the row-weight credit."
  IO.println "ARITHMETIC: log ‖Δ_H‖ / (M·H) ≥ −1 + b̄_H − E_ar."
  IO.println "ARITHMETIC: E_ar = Λ·F·m/v₀ + Λ·Σᵢ(1/wᵢ) + v/w_min,  Λ = 4 + log 4."
  IO.println "PASS: exact nested coefficients and finite row/determinant translation for the actual matrix."
  IO.println "PASS: mixed-tail order budget and bivariate scalar estimates with explicit polynomial overhead."
  IO.println "ANALYTIC ROW: |scalar| ≤ (⌊H⌋+1)^m · exp(−ν·(w·a−w·β) + H·E_tr)."
  IO.println "ANALYTIC ROW: E_tr = ν/F + log 2/v₀ + (log 12+ν)/w_min."
  IO.println "PASS: actual slope/truncation specialization, choice-family count and product of row scalars."
  IO.println "PASS: direct weighted Taylor packing and cancellation of repeated auxiliary/Taylor indices."
  IO.println "PASS: actual two-variable common coefficient series, absolute convergence and uniform coefficient bounds."
  IO.println "PASS: weighted bound for every translated minor and analytic upper bound for the original determinant."
  IO.println "ANALYTIC: log ‖Δ_H‖ / (M·H) ≤ ν·b̄_H − λ + N(λH)/(M·H) + E_tr + E_hol + ρ_H."
  IO.println "PASS: weighted-simplex counting limit, ρ_H → 0, and the uniform mean-row-weight bound b̄_H ≤ v."
  IO.println "PASS: actual nonzero minors and both bounds imply the fixed-data necessary inequality."
  IO.println "COMPARISON: λ − 1 − (ν−1)·v ≤ packingLimit + E_ar + E_tr + E_hol."
  IO.println "PASS: explicit rational seeds and positive gap G = νB² − 1 − (ν−1)v for every rational ν > 3."
  IO.println "PASS: one finite even dimension satisfies the geometric margins and dimension-error budget."
  IO.println "PACKING: λ^(m+2) = K(νv)^m/(16v₀²) = (νB²)^m/64, and packingLimit = λ/(m+3)."
  IO.println "MARGIN: ĝ_m = [(m+2)/(m+3)]λ − 1 − (ν−1)v > G/2."
  IO.println "PASS: an auxiliary-weight threshold makes the remaining error smaller than G/8."
  IO.println "PASS: explicit finite data with the selected parameters and small weight error imply a contradiction."
  IO.println "PASS: successive reduced positive fractions satisfy all weight, denominator and geometric conditions."
  IO.println "PASS: no unbounded reduced exceptional family exists for any rational exponent ν > 3."
  IO.println "PASS: real exponents above three and all unreduced numerator/denominator pairs are covered."
  IO.println "THEOREM: for every ε > 0, eventually in q, every p ∈ ℤ satisfies"
  IO.println "         |log 3 / log 2 − p/q| ≥ 1 / q^(3 + ε)."
  IO.println "THEOREM: 2 ≤ μ(log 3 / log 2) ≤ 3."
  IO.println "PASS: restricted line-aligned and simplex-average scaling audits."
  IO.println "PASS: complete dependency closure rechecked in an empty Lean kernel environment."
  IO.println "PASS: only propext, Classical.choice and Quot.sound; no unsafe or partial dependencies."
  IO.println "SCOPE: the final upper-bound theorem has no geometric, approximation or determinant hypotheses."
  IO.println "SCOPE: equality μ = 3, an upper bound 19/8, and the Collatz conjecture are not proved."

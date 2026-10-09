AN UPPER BOUND OF THREE FOR THE IRRATIONALITY EXPONENT OF log 3 / log 2
Lean source supplement

THEOREM

  theta = log(3) / log(2)

  For every epsilon > 0, there is Q >= 2 such that

      |theta - p/q| >= 1 / q^(3 + epsilon)

  for every integer p and every natural q >= Q.

  Consequently:  2 <= mu(theta) <= 3.

This is an upper bound, not a proof that the exponent equals three.
The theorem does not assume any interpolation, matrix rank, nonzero
determinant, analytic estimate, or exceptional-approximation hypothesis.

PINNED DEPENDENCIES

  Lean:          leanprover/lean4:v4.34.1
  mathlib:       d13f23b723b8a846827a245b89c10fc7d3f11612
  OpenAI math:   adc7f1241b42e322a6451854ab7e4b4c146bf78a

The OpenAI modules in the local import closure are bundled. mathlib and
its own dependencies are resolved by the included lake-manifest.json.
Do not replace pinned revisions by a moving branch or run lake update
merely to get newer dependencies.

REPRODUCTION

Install the Lean toolchain using elan if needed, then open a terminal
in this directory. With network access for the pinned dependencies:

  lake exe cache get
  lake build -q LogarithmExtension.LogRatioMain \
    LogarithmExtension.LogRatioAverageAudit
  lake env lean PaperStatement.lean
  lake env lean --run VerifyLogRatioComponents.lean

Run these sequentially. In particular, do not rebuild imports while
the last command is replaying their declarations.
The replay can take several minutes and may be silent between its
initial count and final PASS messages. A zero exit code is required.

The main theorem is in:
  LogarithmExtension/LogRatioMain.lean
  namespace LogarithmExtension.LogRatio.Main
  theorem logRatio_approximation_bound

PaperStatement.lean checks the ASCII theorem type printed in the
manuscript against that endpoint.

The kernel verifier traverses all dependencies of 127 selected roots,
checks every referenced axiom, rejects unsafe and partial dependencies,
and replays the closure in an initially empty kernel environment.
The checked snapshot contains 116,922 declarations and permits only:
  propext, Classical.choice, Quot.sound.

STRUCTURE

  Sections 2-3:
    LogRatioWeightedComparison, LogRatioPersistentRigidity,
    LogRatioCurveInequality, LogRatioBlowupGeometry,
    LogRatioJetSurjectivity, LogRatioWeightedInterpolation.
  Section 4:
    LogRatioBoundedJetMatrix, LogRatioDenominatorClearing,
    LogRatioMatrixArithmetic, LogRatioArithmeticBound.
  Sections 5-6:
    LogRatioRowTranslation, LogRatioScalarBound,
    LogRatioTaylorPacking, LogRatioCommonTaylor,
    LogRatioCommonTaylorBounds, LogRatioDeterminantAnalytic,
    LogRatioDeterminantComparison.
  Section 7:
    LogRatioParameterSeeds, LogRatioParameterDimension,
    LogRatioParameterChoice, LogRatioPackingCancellation,
    LogRatioParameterContradiction, LogRatioApproximationSelection,
    LogRatioWeightSeparation, LogRatioAdmissibleData, LogRatioMain.

Only the local import closure and the verifier are included. Some
shared modules retain historical definitions or audit results not used
as theorem assumptions. Their presence is not an additional mathematical
claim of this paper.

INTEGRITY AND LICENSES

  SHA256SUMS.txt: hashes of all supplied source/configuration files.
  SOURCE-INVENTORY.json: original workspace paths and source hashes.
  NOTICE.txt: authorship, adaptations, and dependency provenance.
  LICENSE: Apache 2.0 for the original code contributions.

All third-party notices and licenses are retained in their vendor paths.
No credentials, build caches, unrelated research logs, or .git directories
are included.

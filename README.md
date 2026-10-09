# An upper bound of three for the irrationality exponent of log 3 / log 2

Rohit Kumar Jha · 2026 · Preprint and reproducible Lean sources

[Paper and archived sources](https://doi.org/10.5281/zenodo.23256301) · [Version 1 release](https://github.com/rohitkrjha/log23-measure/releases/tag/v1) · [PDF](release/log23-measure-v1.pdf)

## Result

For θ = log(3)/log(2), the paper establishes

$$2 \leq \mu(\theta) \leq 3.$$

Precisely, for every ε > 0, there is Q ≥ 2 such that, for every integer p and every natural q ≥ Q,

$$\left|\theta-\frac{p}{q}\right|\geq\frac{1}{q^{3+\varepsilon}}.$$

This is an upper bound, not equality with three. The theorem includes unreduced fractions and does not provide an effective numerical denominator cutoff.

The proof combines two-base weighted interpolation, denominator clearing, and a joint auxiliary/Taylor-index packing estimate. It builds on OpenAI's separated-weight and determinant framework. The manuscript cites and distinguishes the author's earlier numerical-bound and individual-logarithm papers, as well as related work of Liu, Jiang, and Zhang. The quotient theorem does not follow just from bounds on the two individual logarithms.

## Files

- `release/`: the exact public-deposit PDF, two source archives, verification record, license scope, readme, and checksums.
- `sources/manuscript/`: the exact extracted TeX archive, containing the preprint and journal-style entry points with a shared mathematical body and AI declaration.
- `sources/lean/`: the exact extracted Lean archive, including 916 local modules, pinned configuration, retained third-party licenses, and the dependency-closure verifier.
- `release-manifest.json`: hashes identifying every release file and the source archive inventories.

Private journal correspondence and browser automation are not part of this repository.

## Reproduce the checks

Check the publication files using Python 3:

```sh
python3 scripts/check_integrity.py
```

Build the manuscripts with a TeX installation including `latexmk`, `pdflatex`, and `amsart`:

```sh
cd sources/manuscript
latexmk -pdf -interaction=nonstopmode -halt-on-error zenodo.tex tlms.tex
```

Install Lean through elan, then run these commands sequentially from `sources/lean`:

```sh
lake exe cache get
lake build -q LogarithmExtension.LogRatioMain LogarithmExtension.LogRatioAverageAudit
lake env lean PaperStatement.lean
lake env lean --run VerifyLogRatioComponents.lean
```

Do not run `lake update` to replace the pinned dependencies. The package uses Lean 4.34.1, mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612`, and OpenAI math revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

The recorded local kernel replay checked 127 roots and 116,922 declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`. The package-configuration build reused pinned local caches; it was not a fresh network installation. Details and exact commands are in [VERIFICATION.txt](release/VERIFICATION.txt). GitHub's **Publication integrity** workflow checks hashes and source identity, not Lean compilation or theorem verification.

## AI declaration and attribution

The author set the precise research direction and directed the investigation. OpenAI Codex (model gpt-6-astra) served as his research assistant in pursuing these directions, developing and testing mathematical arguments, implementing and debugging Lean proofs, preparing the manuscript, and identifying obstructions and unpromising approaches.

The author has personally verified the mathematical proofs and reviewed the accompanying Lean code. He takes full responsibility for the manuscript's accuracy, integrity, originality, and attribution.

See [source attribution](sources/lean/NOTICE.txt) and the manuscript bibliography for mathematical and software provenance. Bundled upstream modules match the pinned OpenAI revision byte-for-byte.

## License and citation

The manuscript and original documentation are licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). Original Lean code and publication scripts are licensed under [Apache 2.0](LICENSES/Apache-2.0.txt). Third-party material retains its own notices and licenses; see [RIGHTS.txt](release/RIGHTS.txt).

Cite the versioned preprint using DOI [10.5281/zenodo.23256301](https://doi.org/10.5281/zenodo.23256301) or the repository's `CITATION.cff`. This release is a preprint, not an accepted journal article.

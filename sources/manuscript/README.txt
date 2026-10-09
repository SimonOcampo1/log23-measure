MANUSCRIPT SOURCE

Rational approximation to log₂ 3
Rohit Kumar Jha

Build either or both versions with a standard TeX Live installation:

  latexmk -pdf -interaction=nonstopmode -halt-on-error zenodo.tex
  latexmk -pdf -interaction=nonstopmode -halt-on-error tlms.tex

zenodo.tex is the standalone article-style preprint.
tlms.tex is an AMS-style manuscript for the
Transactions of the London Mathematical Society.

Both wrappers read the same abstract, body, theorem statements,
proof sections, references, and AI declaration.

The source uses standard article/amsart classes. No private fonts,
external figures, proprietary journal class, or shell escape is needed.
The formal development is supplied separately in the Lean source archive.

See RIGHTS.txt for the CC BY 4.0 manuscript license.
SHA256SUMS.txt identifies the exact source snapshot.

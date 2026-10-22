# A Wilson Loop after the First Renormalisation Step

Version 3 of the manuscript.

- [PDF](WILSON_FIRST_RG_STEP_V3.pdf)
- [LaTeX source](WILSON_FIRST_RG_STEP_V3.tex)

## Pedagogical summary

A 29-page companion to the V3 snapshot saved on 21 October 2026, with a notation guide, explanations of the construction and estimates, and the distinction between the first-step results and the iteration conjecture.

- [Summary PDF](V3_Pedagogical_Summary_2026_10_22.pdf)
- [Summary LaTeX source](V3_Pedagogical_Summary_2026_10_22.tex)

## Build

Use a recent TeX Live or MiKTeX installation with pdfLaTeX:

```sh
pdflatex -interaction=nonstopmode -halt-on-error WILSON_FIRST_RG_STEP_V3.tex
pdflatex -interaction=nonstopmode -halt-on-error WILSON_FIRST_RG_STEP_V3.tex
```

Alternatively, run `latexmk -pdf WILSON_FIRST_RG_STEP_V3.tex`.

The source is self-contained, including its bibliography. It requires no external images, bibliography files or custom style files. Standard LaTeX dependencies are listed in [TEX_PACKAGES.txt](TEX_PACKAGES.txt); install them through your TeX distribution.

The uploaded PDF was built using TeX Live 2025 and has 251 pages. Compilation verifies the document build only.

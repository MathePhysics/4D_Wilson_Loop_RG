# Wilson Loops after the First Renormalisation Step

Version 4 of the manuscript, dated 22 October 2026. It includes the first-step result for one square and its extension to the correlation function of two square loops with no common vertices, with separation-dependent cross terms.

- [Manuscript PDF](WILSON_FIRST_RG_STEP_V4.pdf)
- [Manuscript LaTeX source](WILSON_FIRST_RG_STEP_V4.tex)

## Pedagogical summary

A 30-page companion to V4, with a notation guide, explanations of the construction and estimates, the two-loop result, and the distinction between the first-step results and the iteration conjecture.

- [Summary PDF](V4_Pedagogical_Summary_2026_10_22.pdf)
- [Summary LaTeX source](V4_Pedagogical_Summary_2026_10_22.tex)

## Research programme

An outline of the method, current limitations and proposed work towards iteration and an ultraviolet limit, including the direction developed in the continuation drafts.

- [Research programme PDF](Wilson_Loop_Research_Programme_2026_10_22.pdf)
- [Research programme LaTeX source](Wilson_Loop_Research_Programme_2026_10_22.tex)

## Continuation drafts

The [drafts folder and reading guide](drafts/README.md) contains a 23 October 2026 snapshot of the iteration and cutoff-comparison drafts, the supporting notes, earlier first-step drafts and manuscript insert drafts. The guide distinguishes these working files from the current V4 manuscript.

## Build

Use a recent TeX Live or MiKTeX installation with pdfLaTeX:

```sh
pdflatex -interaction=nonstopmode -halt-on-error WILSON_FIRST_RG_STEP_V4.tex
pdflatex -interaction=nonstopmode -halt-on-error WILSON_FIRST_RG_STEP_V4.tex
```

Alternatively, run `latexmk -pdf WILSON_FIRST_RG_STEP_V4.tex`. The summary and research programme can be built in the same way from their respective `.tex` files.

The manuscript, summary and research programme sources are self-contained, including their bibliographies where applicable. They require no external images, bibliography files or custom style files. Standard LaTeX dependencies are listed in [TEX_PACKAGES.txt](TEX_PACKAGES.txt); install them through your TeX distribution.

The PDFs were built using TeX Live 2025. Compilation verifies the document build only.

## Previous version

- [V3 manuscript](WILSON_FIRST_RG_STEP_V3.pdf) and [source](WILSON_FIRST_RG_STEP_V3.tex)
- [V3 pedagogical summary](V3_Pedagogical_Summary_2026_10_22.pdf) and [source](V3_Pedagogical_Summary_2026_10_22.tex)

# Wilson Loops through the Renormalisation Group

The latest saved manuscripts, research programme and continuation drafts, collected on 27 October 2026. The mathematical source files and notes are copied verbatim from the working files; the PDFs are rebuilt from the included sources.

## Current Manuscripts

- **V5:** [PDF](WILSON_FIRST_RG_STEP_V5.pdf), [LaTeX source](WILSON_FIRST_RG_STEP_V5.tex), and [bibliography](WILSON_FIRST_RG_STEP_V5.bib).
- **Updated V4:** [PDF](WILSON_FIRST_RG_STEP_V4.pdf) and [LaTeX source](WILSON_FIRST_RG_STEP_V4.tex).

V5 is the latest manuscript version. V4 is also updated to its latest saved revision. The [snapshot manifest](SNAPSHOT_MANIFEST.json) records the included source files and their hashes.

## Pedagogical Summary

The latest V4 companion gives a notation guide and explanations of the construction, estimates and two-loop result.

- [Summary PDF](V4_Pedagogical_Summary_2026_10_22.pdf)
- [Summary LaTeX source](V4_Pedagogical_Summary_2026_10_22.tex)

## Research Programme

The latest research programme describes the method, current limitations and proposed work towards iteration and an ultraviolet limit.

- [Research programme PDF](Wilson_Loop_Research_Programme_2026_10_24.pdf)
- [Research programme LaTeX source](Wilson_Loop_Research_Programme_2026_10_24.tex)

## Continuation Drafts

The [drafts folder and reading guide](drafts/README.md) contains the latest iteration and cutoff-comparison drafts, the D2.6 and D2.7 developments, supporting estimates, manuscript insert drafts and earlier first-step drafts.

Start with the [26 October status report](drafts/WILSON_IT1_STATUS_REPORT_2026_10_26.md), then the [IT-1 note](drafts/WILSON_IT1_LINE_DEFECT_2026_10_21.md) and [D2 step map](drafts/WILSON_IT1_D2_STEP_MAP_2026_10_22.md). Their stated assumptions, qualifications and open dependencies remain in force.

## Build

Use a recent TeX Live or MiKTeX installation with pdfLaTeX, BibTeX and latexmk. For V5:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error WILSON_FIRST_RG_STEP_V5.tex
```

The custom [preprint class](preprint.cls) and V5 bibliography are included. The earlier manuscripts, summary and research programme use the standard `article` class. Build them with the same command and the appropriate `.tex` filename. Dependencies are listed in [TEX_PACKAGES.txt](TEX_PACKAGES.txt).

Compilation checks the document build; it does not establish mathematical correctness.

## Earlier Versions

- [V3 manuscript](WILSON_FIRST_RG_STEP_V3.pdf) and [source](WILSON_FIRST_RG_STEP_V3.tex).
- [V3 pedagogical summary](V3_Pedagogical_Summary_2026_10_22.pdf) and [source](V3_Pedagogical_Summary_2026_10_22.tex).
- [Earlier research programme](Wilson_Loop_Research_Programme_2026_10_22.pdf) and [source](Wilson_Loop_Research_Programme_2026_10_22.tex).

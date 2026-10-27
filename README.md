# Wilson Loops through the Renormalisation Group

The latest saved manuscripts, research programme and continuation drafts, collected on 27 October 2026. The mathematical source files and notes are copied verbatim from the working files; the current PDFs are rebuilt from the included sources. Previous versions retain their saved PDFs.

## Current Manuscripts

- **Updated V4:** [PDF](WILSON_FIRST_RG_STEP_V4.pdf) and [LaTeX source](WILSON_FIRST_RG_STEP_V4.tex).

## Manuscripts under Construction

The [Manuscripts under Construction folder](Manuscripts%20under%20Construction/) contains:

- **V5:** [PDF](Manuscripts%20under%20Construction/WILSON_FIRST_RG_STEP_V5.pdf), [LaTeX source](Manuscripts%20under%20Construction/WILSON_FIRST_RG_STEP_V5.tex), and [bibliography](Manuscripts%20under%20Construction/WILSON_FIRST_RG_STEP_V5.bib).
- **Pedagogical summary (V4 companion):** [PDF](Manuscripts%20under%20Construction/V4_Pedagogical_Summary_2026_10_22.pdf) and [LaTeX source](Manuscripts%20under%20Construction/V4_Pedagogical_Summary_2026_10_22.tex).

The summary gives a notation guide and explanations of the construction, estimates and two-loop result. V5 is the latest manuscript version under construction. The [snapshot manifest](SNAPSHOT_MANIFEST.json) records the included source files and their hashes.

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
cd "Manuscripts under Construction"
latexmk -pdf -interaction=nonstopmode -halt-on-error WILSON_FIRST_RG_STEP_V5.tex
```

The V5 folder includes the custom [preprint class](Manuscripts%20under%20Construction/preprint.cls) and V5 bibliography. The earlier manuscripts, summary and research programme use the standard `article` class. Build them with the same command and the appropriate `.tex` filename. Dependencies are listed in [TEX_PACKAGES.txt](TEX_PACKAGES.txt).

Compilation checks the document build; it does not establish mathematical correctness.

## Previous Versions

The [Previous Versions folder](Previous%20Versions/) contains the earlier manuscripts and their saved PDFs.

- **V1:** [PDF](Previous%20Versions/WILSON_FIRST_RG_STEP.pdf) and [LaTeX source](Previous%20Versions/WILSON_FIRST_RG_STEP.tex).
- **V2:** [PDF](Previous%20Versions/WILSON_FIRST_RG_STEP_V2.pdf) and [LaTeX source](Previous%20Versions/WILSON_FIRST_RG_STEP_V2.tex).
- **V3:** [PDF](Previous%20Versions/WILSON_FIRST_RG_STEP_V3.pdf) and [LaTeX source](Previous%20Versions/WILSON_FIRST_RG_STEP_V3.tex).
- **V3 pedagogical summary:** [PDF](Previous%20Versions/V3_Pedagogical_Summary_2026_10_22.pdf) and [LaTeX source](Previous%20Versions/V3_Pedagogical_Summary_2026_10_22.tex).

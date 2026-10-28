# Wilson Loops through the Renormalisation Group

The latest saved manuscripts, research programme and continuation drafts, collected on 28 October 2026. The mathematical content of the sources and notes is copied unchanged from the working files, with repository links adjusted where needed; the current PDFs are rebuilt from the included sources. Previous versions retain their saved PDFs.


## Progress of the Construction

Our work focuses solely on attempting to give a robust construction of the correlation functions of renormalised Wilson loops in **finite volume**. Because the Schwinger functions will have been obtained via a lattice based renormalisation group construction the hypercubic Osterwalder-Schrader axioms will constitute solely routine checks rather than needing new mathematics. We are currently not pursuing an infinite volume constructions, since (as per our personal judgment), the lack of a viable route for proving the existence of a mass gap makes it fundamentally less interesting (other people may disagree with us with good reason).

Our current progress is as follows.

| Main step | Completion | Main remaining work |
|---|---|---|
| [First RG step for one loop and two disjoint loops](Manuscripts%20under%20Construction/WILSON_FIRST_RG_STEP_V5.tex) | **In manuscript** | The stated finite-cutoff theorems and uniform bounds are written. |
| [Small-field iteration and large-field insertions](drafts/WILSON_IT1_D26_CLOSURE_2026_10_24.md) | **Written; verification outstanding** | Verify the analytic-domain, locality and weight estimates used in the induction. |
| [R-steps for single and two-loop insertions](drafts/WILSON_IT1_D27_CLOSURE_2026_10_26.md) | **Conditional** | Complex evaluation bounds, member counting and extent weights; merging of mixed groups for two loops. |
| [Relative weights of large-field contributions](drafts/WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md) | **Written; verification outstanding** | Verify the whole-integral comparison and history-cost estimates at fixed volume. |
| [Cutoff-uniform bounds and subsequential limits](drafts/WILSON_IT1_TWO_LOOPS_UNIFORM_BOUND_2026_10_27.md) | **Conditional** | Complete the R-step induction. Subsequential convergence then follows from compactness. |
| [Comparison of successive ultraviolet cutoffs](drafts/WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md) | **Partial/open** | Complete the stability estimates for the effective measures and loop insertions under lattice refinement. |
| [Full-sequence continuum limits](drafts/WILSON_IT1_CONTINUUM_LIMIT_CLOSURE_2026_10_26.md) | **Not established** | Prove summable bounds on successive cutoff differences, including the mixed terms for two loops. |
| Correlation functions of arbitrarily many disjoint Wilson loops | **Not established** | Extend the RG induction and cutoff comparison to finite products of loop insertions, including groups meeting three or more loops. |
| [Decay of connected two-loop correlations](drafts/WILSON_IT1_TWO_LOOPS_UNIFORM_BOUND_2026_10_27.md) | **Open** | Establish correlation decay for the stopping-scale measure and the relevant remainder terms. |





## Current Manuscripts

- **Updated V4:** [PDF](WILSON_FIRST_RG_STEP_V4.pdf) and [LaTeX source](WILSON_FIRST_RG_STEP_V4.tex).

## Manuscripts under Construction

The [Manuscripts under Construction folder](Manuscripts%20under%20Construction/) contains:

- **V5:** [PDF](Manuscripts%20under%20Construction/WILSON_FIRST_RG_STEP_V5.pdf), [LaTeX source](Manuscripts%20under%20Construction/WILSON_FIRST_RG_STEP_V5.tex), and [bibliography](Manuscripts%20under%20Construction/WILSON_FIRST_RG_STEP_V5.bib).
- **Pedagogical summary (V4 companion):** [PDF](Manuscripts%20under%20Construction/V4_Pedagogical_Summary_2026_10_22.pdf) and [LaTeX source](Manuscripts%20under%20Construction/V4_Pedagogical_Summary_2026_10_22.tex).

The summary gives a notation guide and explanations of the construction, estimates and two-loop result. V5 is the latest manuscript version under construction.

## Research Programme

The research programme, updated on 27 October 2026, describes the method, current limitations and proposed work towards iteration and an ultraviolet limit. Its milestones link directly to the current iteration, relative-weight and cutoff-comparison drafts.

- [Research programme PDF](Research_Outline.pdf)

## Continuation Drafts

The [drafts folder and reading guide](drafts/README.md) contains the latest iteration and cutoff-comparison drafts, the D2.6 and D2.7 developments, supporting estimates, manuscript insert drafts and earlier first-step drafts.

Start with the [27 October status report](drafts/WILSON_IT1_STATUS_REPORT_2026_10_27.md), then the [IT-1 note](drafts/WILSON_IT1_LINE_DEFECT_2026_10_21.md) and [D2 step map](drafts/WILSON_IT1_D2_STEP_MAP_2026_10_22.md). Their stated assumptions, qualifications and open dependencies remain in force.

The [27 October Cauchy-estimate draft](drafts/WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md) develops the proposed one-step stability estimate, coupling and large-field feedbacks, lattice-refinement bounds for background fields and fluctuation covariances, and relative-weight comparison. Its review status is recorded in the draft; parts remain unreviewed. The [cutoff-comparison note](drafts/WILSON_IT1_CONTINUUM_CUTOFF_COMPARISON_2026_10_27.md) records the separate marked-polymer investigation and its unresolved estimates.

The [Bałaban paper-label dictionary](drafts/BALABAN_PAPER_LABELS.md) gives official titles, citations and links for the internal labels used throughout these drafts.



## Detailed Breakdown of Current Progress

Assessment of the working drafts as of 28 October 2026. The linked drafts are included in this repository.

**In manuscript** means a theorem and proof are present under their stated assumptions. **Written** means the derivation exists with its stated verification qualifications. **Conditional** means the conclusion requires an unresolved estimate.

### Single-Loop RG Construction

| Claim | Completion | Outstanding work |
|---|---|---|
| First RG step for a square Wilson loop | **In manuscript** | Exact normalised decomposition, perimeter and corner extraction, and defect and boundary bounds are supplied. See [V5's main theorem](Manuscripts%20under%20Construction/WILSON_FIRST_RG_STEP_V5.tex). |
| First-step leading-term bounds and exponential moment | **In manuscript** | The stated estimates retain contour-length dependence; they do not alone give cutoff-uniform control at fixed physical loop size. |
| Inductive class of Wilson loop insertions | **Written** | Full preservation requires the fluctuation-step and R-step estimates. |
| Small-field RG transformation and contraction of deviation insertions | **Written; verification outstanding** | D2.1–D2.4 contain the transformation, scalar extraction and contraction recursion. Analytic-domain conditions and source transfers require reconciliation with their callers. See the [step map](drafts/WILSON_IT1_D2_STEP_MAP_2026_10_22.md). |
| D2.6: production, propagation and payment of large-field insertions | **Written; verification outstanding** | O4/O5/O6 domain and weight arguments, inherited analytic conditions, and source transfers including R-dec⁺ require verification. See [D2.6](drafts/WILSON_IT1_D26_CLOSURE_2026_10_24.md). |
| Analytic representation of shifted insertions | **Written; verification outstanding** | The frozen-centre representation must remain compatible with the carry argument and every evaluation domain. See [O4](drafts/WILSON_IT1_O4_CLOSURE_2026_10_26.md). |
| Perimeter and corner extraction at subsequent steps | **Written** | D2.3 and D2.7 specify the scalar extraction. Its incorporation into the full induction depends on the R-step estimates. |
| Preservation of the insertion class through arbitrary R-steps | **Conditional** | **R-eval:** bounds at complex evaluation points. **R-round:** counting carried members. **R-att-ext:** extent weights of attached groups. The R-far″ source transfer also requires verification. See [D2.7](drafts/WILSON_IT1_D27_CLOSURE_2026_10_26.md). |
| Cutoff-uniform bound on the renormalised single-loop expectation | **Conditional** | Requires the R-step estimates and inclusion of the R-step scalar remainders and appropriate wrap bounds. |
| Subsequential convergence of single-loop expectations | **Automatic once uniform boundedness holds** | Bounded-sequence compactness and diagonal extraction supply the result. No separate RG estimate is needed. See the [continuum note, §8](drafts/WILSON_IT1_CONTINUUM_LIMIT_CLOSURE_2026_10_26.md). |

### Ultraviolet Cutoff Comparison and the Continuum Limit

| Claim | Completion | Outstanding work |
|---|---|---|
| Exact normalised comparison of consecutive cutoffs | **Written** | The difference formula retains the physical denominator and perimeter/corner normalisations. See the [cutoff-comparison draft](drafts/WILSON_IT1_CONTINUUM_CUTOFF_COMPARISON_2026_10_27.md). |
| Extra-generation contribution and old-scale tails | **Written** | Geometric decay for regular terms and polynomial decay for R-terms are obtained under the running-coupling bounds. See the [Cauchy draft, §4](drafts/WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md). |
| Classical action and minimiser comparison at regular real backgrounds | **Written within that scope** | Extension to the complex configurations and localisation domains used in the activity estimates remains necessary. |
| Gaussian covariance and quadratic-form comparison | **Substantial derivation written** | Transfer to every individual localised, multiscale ingredient remains incomplete. |
| Localised lift between the fine lattices | **Written; unreviewed** | The construction and collar-mismatch tail estimate require verification against their consumers. |
| Complex-domain admissibility of lifted configurations | **Open** | The lift condition is missing at complex fluctuation data and certain composite configurations. Near domains crossing finer layers also require suitable class bounds. |
| Euclidean covariance of the lifted activity sum | **Open** | Marginal extraction and the moment estimate require control of the sum whose terms are evaluated at different local lifts. |
| Relative weights of large-field contributions at the stopping scale | **Written; verification outstanding** | Whole-integral comparison and history-cost payment require verification under the stated fixed-volume and loop/coupling restrictions. See the [Cauchy draft, §11](drafts/WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md). |
| Differences of characteristic functions and cutoff functions | **Written; verification outstanding** | Shell estimates and the soft-cutoff decomposition require consistent source-domain and threshold checks. |
| [Individual localised propagators and walk-factor differences](drafts/WILSON_IT1_WALK_FACTOR_DIFFERENCE_2026_10_28.md) | **Partial/open** | **Wδ-1–Wδ-3:** local operator defects, fine-side comparison and nonlinear fixed-point differences. |
| [Differences of large-field integrands and loop dressings](drafts/WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md) | **Partial/open** | LF-A **(3), (6), (7), (10):** complex variations, interface terms, individual localised terms and boundary terms. |
| [Interface cancellations and multiplier comparison](drafts/WILSON_IT1_LF_GAMMA_REPAIR_ATTEMPTS_2026_10_28.md) | **Partial/conditional** | Requires local complex action bounds, geometric separation estimates and multiplier-response estimates. |
| [Marked component sums and connected exponentiation](drafts/WILSON_IT1_LF_GAMMA_REPAIR_ATTEMPTS_2026_10_28.md) | **Conditional derivation written** | Requires primitive marked-integral bounds, comparison of V(Y), exceptional counting estimates and control of the carried second-class boundary sector. |
| Coupled recursion for activity, R-term and coupling differences | **Conditional derivation written** | Requires the missing depth estimates, the complex R-term class bound and the corresponding source/rate bounds. |
| Summable Cauchy estimate and full-sequence continuum limit | **Not established** | A summable estimate for the actual normalised cutoff difference is required under fully verified hypotheses. |

### Two Wilson Loops

The pair results concern two vertex-disjoint squares. The extension to any finite family of pairwise disjoint loops is listed separately.

| Claim | Completion | Outstanding work |
|---|---|---|
| First RG step for the pair expectation | **In manuscript** | Product of the individual perimeter/corner normalisations, mixed contributions and remainder bounds are supplied. See [V5's two-loop theorem](Manuscripts%20under%20Construction/WILSON_FIRST_RG_STEP_V5.tex). |
| Separation decay of first-step mixed contributions | **In manuscript** | Exponential separation bounds hold for the stated mixed activities and scalar correction. |
| [Inductive pair class and propagation of mixed insertions through fluctuation steps](drafts/WILSON_IT1_TWO_LOOPS_UNIFORM_BOUND_2026_10_27.md) | **Substantial derivation written** | Production and carry estimates require verification together with the inherited single-loop inputs. |
| [R-steps for the pair](drafts/WILSON_IT1_TWO_LOOPS_UNIFORM_BOUND_2026_10_27.md) | **Conditional** | Requires **R-eval**, **R-round**, **R-att-ext**, and **R-member**: a merging rule and weight estimate for mixed insertions shared by several groups. |
| [Cutoff-uniform bound on the renormalised pair expectation](drafts/WILSON_IT1_TWO_LOOPS_UNIFORM_BOUND_2026_10_27.md) | **Conditional** | The explicit estimate requires the unresolved R-step bounds. |
| Subsequential convergence of pair expectations | **Automatic once uniform boundedness holds** | Compactness supplies subsequences; no separate substantive RG estimate is required. |
| Full-sequence continuum limit of the pair expectation | **Not established** | Requires cutoff-comparison estimates for the pair, including its mixed insertion species and their R-step contributions. |
| [Decay of the connected two-loop correlation and factorisation at large separation](drafts/WILSON_IT1_TWO_LOOPS_UNIFORM_BOUND_2026_10_27.md) | **Open** | Requires correlation estimates for the stopping-scale measure and separation decay of the relevant remainder terms. |
| Correlation functions of arbitrarily many disjoint Wilson loops | **Not established** | Extend the insertion class and R-step estimates to any finite family of pairwise disjoint loops, control groups meeting three or more loops, and establish cutoff-uniform bounds and summable cutoff differences after the individual perimeter/corner renormalisations. |

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

## Questions & Comments

adogra [at] mit.edu (Akshunna S. Dogra), martin.peev [at] maths.ox.ac.uk (Martin Peev)

## Licence

Original research material in this repository is dedicated to the public domain under [CC0 1.0 Universal](LICENSE). Third-party material retains its existing copyright and licence notices.

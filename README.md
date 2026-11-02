# Wilson Loops through the Renormalisation Group

Bałaban's renormalisation group construction gives a gauge-fixed lattice measure and a corresponding RG trajectory for Yang–Mills at every finite ultraviolet cutoff. However, the gauge transformations introduced at successive steps accumulate, and seem to hinder convergence of the resulting gauge-fixed fields as the cutoff is removed. 

Therefore, we seek the continuum theory through gauge-invariant observables. The natural candidates – Wilson loops and pointwise traces of powers of the field strength – present a second difficulty: in dimensions greater than two they are ultraviolet singular and cannot simply be treated as ordinary continuum random variables. 

Our programme addresses this problem for correlation functions of Wilson loops in four-dimensional Yang–Mills theory. We aim to identify within the RG the scalar contributions corresponding to the perimeter and corner renormalisations known from the physics literature, and to prove ultraviolet convergence after their extraction.

The [research outline](Research_Outline.pdf) and the [project announcement](Yang_Mills_Announcement.pdf) were written in full by Martin Peev and Akshunna S. Dogra. Our attempt, which began in earnest on 26/08/2026, has not made use of any progress made by concurrent attempts (Sec. 4, research outline). 

We have partially chosen this path so we could test whether expertise+LLM-driven research can compete with brute force LLM methods made possible by academically unviable sums of money (for us, O($100,000) - roughly what a postdoc costs per year). We of course welcome all types of support from external entities (indeed, we have applied for and/or received LLM compute research grants/awards/resources from both academic and corporate entities). The constraint is that support be of a type and come with terms consistent with academic norms for research/collaboration.

All other documents, unless explicitly mentioned otherwise, were generated in **full** by Claude and/or ChatGPT. First and foremost, this includes all potentially novel mathematical work. This work is public and open source (see licence) – not only are others “allowed” to comment/fork/contribute, it is encouraged. 

The only authority we have (in the project's infancy) is deciding who gets to be a maintainer while the Yang–Mills existence proof is being built. As more join, specially when we hopefully make a push towards the mass-gap, this will naturally be diluted too.

Nothing in this repository should be considered an academically rigorous, “publishable” mathematical paper, and we have yet to verify most of it directly.  Mathematical content that is “in the manuscript” has been most extensively checked with the help of LLMs, and it is **our judgment** that it is essentially correct. 

The ongoing work contained in the drafts is of varying status and annotated within the drafts. In parallel, LEAN certificates of this work are also being generated (people who wish to join may find this the easiest and most fertile ground to start with).


## Progress of the Construction

Our work focuses solely on attempting to give a robust construction of the correlation functions of renormalised Wilson loops in **finite volume**. Because the Schwinger functions will have been obtained via a lattice-based renormalisation group construction, the hypercubic Osterwalder-Schrader axioms will constitute solely routine checks rather than needing new mathematics. We are currently not pursuing an infinite-volume construction, since (as per our personal judgment), the lack of a viable route for proving the existence of a mass gap makes it fundamentally less interesting (other people may disagree with us with good reason).

Our current progress is as follows.

| Main step | Completion | Main remaining work |
|---|---|---|
| [First RG step for one loop and two disjoint loops](WILSON_FIRST_RG_STEP_V4.tex) | **Complete** | The stated finite-cutoff theorems and uniform bounds are written. |
| [Small-field iteration and large-field insertions](drafts/WILSON_IT1_D26_CLOSURE_2026_10_24.md) | **Written; verification outstanding** | Verify the complex gauge-covariance, averaged-current, analytic-domain and weight arguments used in the induction, with their stated source readings. |
| [R-steps for single and two-loop insertions](drafts/WILSON_IT1_D27_CLOSURE_2026_10_26.md) | **Conditional** | Verify the written evaluation, rounding and extent estimates; close the three single-loop post-R gaps and the pair’s member-merging and cross-insertion weight gaps. |
| [Relative weights of large-field contributions](drafts/WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md) | **Written; verification outstanding** | Verify the whole-integral comparison and history-cost estimates at fixed volume. |
| [Cutoff-uniform bounds and subsequential limits](drafts/WILSON_IT1_TWO_LOOPS_UNIFORM_BOUND_2026_10_27.md) | **Conditional** | Complete the R-step induction. Subsequential convergence then follows from compactness. |
| [Comparison of successive ultraviolet cutoffs](drafts/WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md) | **Partial/conditional** | Verify the walk-factor, complex-lift, interface and large-field comparison estimates in their current form, and their use in the normalised cutoff comparison. |
| [Full-sequence continuum limits](drafts/WILSON_IT1_CONTINUUM_LIMIT_CLOSURE_2026_10_26.md) | **Not established** | Prove summable bounds on successive cutoff differences, including the mixed terms for two loops. |
| Correlation functions of arbitrarily many disjoint Wilson loops | **Not established** | Extend the RG induction and cutoff comparison to finite products of loop insertions, including groups meeting three or more loops. |
| [Decay of connected two-loop correlations](drafts/WILSON_IT1_TWO_LOOPS_UNIFORM_BOUND_2026_10_27.md) | **Open** | Establish correlation decay for the stopping-scale measure and the relevant remainder terms. |





## Current Manuscripts

- **Updated V4:** [PDF](WILSON_FIRST_RG_STEP_V4.pdf) and [LaTeX source](WILSON_FIRST_RG_STEP_V4.tex).

## Manuscripts under Construction

The [Manuscripts under Construction folder](Manuscripts%20under%20Construction/) contains:

- **V5:** [PDF](Manuscripts%20under%20Construction/WILSON_FIRST_RG_STEP_V5.pdf), [LaTeX source](Manuscripts%20under%20Construction/WILSON_FIRST_RG_STEP_V5.tex), and [bibliography](Manuscripts%20under%20Construction/WILSON_FIRST_RG_STEP_V5.bib).
- **Pedagogical summary (V4 companion):** [PDF](Manuscripts%20under%20Construction/V4_Pedagogical_Summary_2026_10_22.pdf) and [LaTeX source](Manuscripts%20under%20Construction/V4_Pedagogical_Summary_2026_10_22.tex).

The summary gives a notation guide and explanations of the construction, estimates and two-loop result. V4 is the current reference manuscript; V5 remains under construction.

## Research Programme

The research programme, updated on 27 October 2026, describes the method, current limitations and proposed work towards iteration and an ultraviolet limit. Its milestones link directly to the current iteration, relative-weight and cutoff-comparison drafts.

- [Research programme PDF](Research_Outline.pdf)

## Continuation Drafts

The [drafts folder and reading guide](drafts/README.md) contains the latest iteration and cutoff-comparison drafts, the D2.6 and D2.7 developments, supporting estimates, manuscript insert drafts and earlier first-step drafts.

Start with the [D2 step map](drafts/WILSON_IT1_D2_STEP_MAP_2026_10_22.md) and [IT-1 note](drafts/WILSON_IT1_LINE_DEFECT_2026_10_21.md), then the current [large-field](drafts/WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md) and [walk-factor](drafts/WILSON_IT1_WALK_FACTOR_DIFFERENCE_2026_10_28.md) drafts. The [beta-function note](drafts/BETA_FUNCTION_WILSON_LOOPS.md) supplies the coupling estimates used in these drafts. Their stated assumptions, qualifications and open dependencies remain in force.

The [27 October Cauchy-estimate draft](drafts/WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md) develops the proposed one-step stability estimate, coupling and large-field feedbacks, lattice-refinement bounds for background fields and fluctuation covariances, and relative-weight comparison. Its review status is recorded in the draft; parts remain unreviewed. The [cutoff-comparison note](drafts/WILSON_IT1_CONTINUUM_CUTOFF_COMPARISON_2026_10_27.md) records the separate marked-polymer investigation and its unresolved estimates.

The [Bałaban paper-label dictionary](drafts/BALABAN_PAPER_LABELS.md) gives official titles, citations and links for the internal labels used throughout these drafts.



## Detailed Breakdown of Current Progress

Assessment of the working drafts as of 2 November 2026. The linked drafts are included in this repository.

**In manuscript** means a theorem and proof are present under their stated assumptions. **Written** means the derivation exists with its stated verification qualifications. **Conditional** means the conclusion requires an unresolved estimate.

### Single-Loop RG Construction

| Claim | Completion | Outstanding work |
|---|---|---|
| First RG step for a square Wilson loop | **In manuscript** | Exact normalised decomposition, perimeter and corner extraction, and defect and boundary bounds are supplied. See [V4's main theorem](WILSON_FIRST_RG_STEP_V4.tex). |
| First-step leading-term bounds and exponential moment | **In manuscript** | The stated estimates retain contour-length dependence; they do not alone give cutoff-uniform control at fixed physical loop size. |
| Inductive class of Wilson loop insertions | **Written** | Full preservation requires the fluctuation-step and R-step estimates. |
| Small-field RG transformation and contraction of deviation insertions | **Written; verification outstanding** | Verify the complex carry and averaged-current estimates, their analytic domains and the inherited source readings. See the [step map](drafts/WILSON_IT1_D2_STEP_MAP_2026_10_22.md), [complex covariance](drafts/WILSON_IT1_COMPLEX_COVARIANCE_2026_10_29.md) and [averaged current](drafts/WILSON_IT1_RMJ_CLOSURE_2026_10_30.md). |
| D2.6: production, propagation and payment of large-field insertions | **Written; verification outstanding** | O4/O5/O6 domain and weight arguments, inherited analytic conditions, and source transfers including R-dec⁺ require verification. See [D2.6](drafts/WILSON_IT1_D26_CLOSURE_2026_10_24.md). |
| Analytic representation of shifted insertions | **Written; verification outstanding** | Verify the frozen-centre representation, its carry domains and the complex-data estimates. See [O4](drafts/WILSON_IT1_O4_CLOSURE_2026_10_26.md) and [complex covariance](drafts/WILSON_IT1_COMPLEX_COVARIANCE_2026_10_29.md). |
| Perimeter and corner extraction at subsequent steps | **Written** | D2.3 and D2.7 specify the scalar extraction. Its incorporation into the full induction depends on the R-step estimates. |
| Preservation of the insertion class through arbitrary R-steps | **Conditional** | R-eval, R-round and R-att-ext are derived, awaiting review. Three post-R gaps remain: the link-decay payment, the bound on Pol after merges, and O2 at k > N. Verify the R-far″ source reading and the repaired arguments. See [D2.7, item 15.8](drafts/WILSON_IT1_D27_CLOSURE_2026_10_26.md). |
| Cutoff-uniform bound on the renormalised single-loop expectation | **Conditional** | Close the three post-R gaps and verify the written R-step estimates, including the scalar remainders and wrap bounds. |
| Subsequential convergence of single-loop expectations | **Automatic once uniform boundedness holds** | Bounded-sequence compactness and diagonal extraction supply the result. No separate RG estimate is needed. See the [continuum note, §8](drafts/WILSON_IT1_CONTINUUM_LIMIT_CLOSURE_2026_10_26.md). |

### Ultraviolet Cutoff Comparison and the Continuum Limit

| Claim | Completion | Outstanding work |
|---|---|---|
| Exact normalised comparison of consecutive cutoffs | **Written** | The difference formula retains the physical denominator and perimeter/corner normalisations. See the [cutoff-comparison draft](drafts/WILSON_IT1_CONTINUUM_CUTOFF_COMPARISON_2026_10_27.md). |
| Extra-generation contribution and old-scale tails | **Written** | Geometric decay for regular terms and polynomial decay for R-terms use the running-coupling bounds. See the [Cauchy draft, §4](drafts/WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md) and the [beta-function derivations](drafts/BETA_FUNCTION_WILSON_LOOPS.md), with their construction and source assumptions. |
| Classical action and minimiser comparison at regular real backgrounds | **Written; verification outstanding** | The real-background derivation is supplemented by complex-background and multiscale comparisons in the [large-field note](drafts/WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md); verify their domains and use in the localised terms. |
| Gaussian covariance and quadratic-form comparison | **Written; verification outstanding** | Localised operator, shell and nonlinear fixed-point comparisons are derived in the [walk-factor note, §§10–12](drafts/WILSON_IT1_WALK_FACTOR_DIFFERENCE_2026_10_28.md); verify their application to the individual multiscale ingredients. |
| Localised lift between the fine lattices | **Written; unreviewed** | The construction and collar-mismatch tail estimate require verification against their consumers. |
| Complex-domain admissibility of lifted configurations | **Written; verification outstanding** | Complex fluctuation data, composite configurations, finer-layer crossings and the complex R-term class bound have derivations. Verify the lift, current and domain arguments under their stated parameter choices. See the [Cauchy draft, §§5 and 10.5](drafts/WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md). |
| Quadratic moment of the lifted activity sum | **Written; verification outstanding** | Verify the plane-resolved marginal extraction and its boundary-error estimate. The full quadratic tensor is retained; Euclidean covariance of the lifted sum is not assumed. |
| Relative weights of large-field contributions at the stopping scale | **Written; verification outstanding** | Whole-integral comparison and history-cost payment require verification under the stated fixed-volume and loop/coupling restrictions. See the [Cauchy draft, §11](drafts/WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md). |
| Differences of characteristic functions and cutoff functions | **Written; verification outstanding** | Shell estimates and the soft-cutoff decomposition require consistent source-domain and threshold checks. |
| [Individual localised propagators and walk-factor differences](drafts/WILSON_IT1_WALK_FACTOR_DIFFERENCE_2026_10_28.md) | **Written; verification outstanding** | Wδ-1–Wδ-3 and the collar comparison Wδ-4 are derived, awaiting review in their current form. Verify the shell defects, fine-side lift, nonlinear functions and boundary-collar estimates. |
| [Differences of large-field integrands and loop dressings](drafts/WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md) | **Written; verification outstanding** | LF-A (3), (6), (7), (10) and the layer-width condition (11) have derivations awaiting review, together with the inherited walk-factor, complex-domain and parameter conditions. LF-W uses these inputs. |
| [Interface cancellations and multiplier comparison](drafts/WILSON_IT1_LF_GAMMA_REPAIR_ATTEMPTS_2026_10_28.md) | **Written; verification outstanding** | The multiscale alignment, interface π-part and twist estimates are derived in the [large-field note, §4(d)](drafts/WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md). Verify the current, gauge and complex-domain arguments and their constant choices. |
| [Marked component sums and connected exponentiation](drafts/WILSON_IT1_LF_GAMMA_REPAIR_ATTEMPTS_2026_10_28.md) | **Conditional derivation written** | Verify the vacuum cancellation, marked sums and their application to the mixed interacting integral, retaining the full inherited interaction and physical denominator. The [repair note](drafts/WILSON_IT1_LF_GAMMA_REPAIR_ATTEMPTS_2026_10_28.md) still records this application as open. |
| Coupled recursion for activity, R-term and coupling differences | **Conditional derivation written** | Verify the written depth and complex R-term estimates and their source/rate bounds in the actual recursion. The normalised Cauchy estimate remains conditional on these inputs. |
| Summable Cauchy estimate and full-sequence continuum limit | **Not established** | A summable estimate for the actual normalised cutoff difference is required under fully verified hypotheses. |

### Two Wilson Loops

The pair results concern two vertex-disjoint squares. The extension to any finite family of pairwise disjoint loops is listed separately.

| Claim | Completion | Outstanding work |
|---|---|---|
| First RG step for the pair expectation | **In manuscript** | Product of the individual perimeter/corner normalisations, mixed contributions and remainder bounds are supplied. See [V4's two-loop theorem](WILSON_FIRST_RG_STEP_V4.tex). |
| Separation decay of first-step mixed contributions | **In manuscript** | Exponential separation bounds hold for the stated mixed activities and scalar correction. |
| [Inductive pair class and propagation of mixed insertions through fluctuation steps](drafts/WILSON_IT1_TWO_LOOPS_UNIFORM_BOUND_2026_10_27.md) | **Substantial derivation written** | Production and carry estimates require verification together with the inherited single-loop inputs. |
| [R-steps for the pair](drafts/WILSON_IT1_TWO_LOOPS_UNIFORM_BOUND_2026_10_27.md) | **Conditional** | R-eval, R-round and R-att-ext are derived, awaiting review. R-member and R-eval-cr remain open, together with the inherited single-loop post-R gaps. |
| [Cutoff-uniform bound on the renormalised pair expectation](drafts/WILSON_IT1_TWO_LOOPS_UNIFORM_BOUND_2026_10_27.md) | **Conditional** | The explicit bound requires R-member, R-eval-cr and the inherited single-loop post-R estimates, with their review qualifications. |
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

## Licence

Original research material in this repository is licensed under [CC0-1.0](LICENSE). Third-party material retains its existing copyright and licence notices.

## Questions & Comments

adogra [at] mit.edu (Akshunna S. Dogra), martin.peev [at] maths.ox.ac.uk (Martin Peev)

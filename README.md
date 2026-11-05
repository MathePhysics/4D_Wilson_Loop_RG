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
| [R-steps for single and two-loop insertions](drafts/WILSON_IT1_D27_CLOSURE_2026_10_26.md) | **Written; verification outstanding** | Verify R-eval as a whole, the localisation of carried insertions and the post-R acceptance arguments, together with the large-field weighted-response premises. The member-merging and cross-insertion weight arguments have reviews conditional on R-eval. |
| [Relative weights of large-field contributions](drafts/WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md) | **Written; verification outstanding** | Verify the whole-integral comparison and history-cost estimates at fixed volume. |
| [Cutoff-uniform bounds and subsequential limits](drafts/WILSON_IT1_TWO_LOOPS_UNIFORM_BOUND_2026_10_27.md) | **Written; verification outstanding** | Verify the written R-step induction and its inherited inputs. Subsequential convergence follows from compactness once the uniform bound is established. |
| [Comparison of successive ultraviolet cutoffs](drafts/WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md) | **Written; verification outstanding** | Verify the one-loop comparison and the transfers to pairs and finite families, including the marked activities, cross and wrap insertions, scalar constants and large-field terms. |
| [Full-sequence continuum limits](drafts/WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md) | **Written; verification outstanding** | Verify the single-loop argument and the [pair Cauchy extension](drafts/WILSON_IT1_TWO_LOOPS_CAUCHY_2026_11_05.md), together with the [finite-family extension](drafts/WILSON_IT1_N_LOOPS_UNIFORM_BOUND_2026_11_05.md) and their inherited inputs. |
| Correlation functions of arbitrarily many disjoint Wilson loops | **Written; verification outstanding** | A first-step extension, cutoff-uniform bound and full-sequence argument are written for each fixed finite family of disjoint squares in coordinate planes. Verify the counts and inherited pair transfers. See the [multiloop draft](drafts/WILSON_IT1_N_LOOPS_UNIFORM_BOUND_2026_11_05.md). |
| [Decay of connected two-loop correlations](drafts/WILSON_IT1_PAIR_FACTORISATION_2026_11_05.md) | **Partial/open** | Verify the assembled near/far comparison. Complete the far-component cluster-tail check and the stopping-scale covariance bound for loop sizes small relative to their separation at fixed volume. |





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

Assessment of the working drafts as of 5 November 2026. The linked drafts are included in this repository.

**In manuscript** means a theorem and proof are present under their stated assumptions. **Written** means the derivation exists with its stated verification qualifications. **Partial/open** means that part of the argument is written and named estimates remain to be derived.

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
| Preservation of the insertion class through arbitrary R-steps | **Written; verification outstanding** | Verify the full R-eval argument, its source assumptions and the weighted-response premises, R-round, R-att-ext and the localisation of carried insertions. D2.7 item 15.8 supplies the gas-link payment and post-R acceptance derivations, which await review. See [D2.7](drafts/WILSON_IT1_D27_CLOSURE_2026_10_26.md) and the [evaluation estimates](drafts/WILSON_IT1_TWO_LOOPS_UNIFORM_BOUND_2026_10_27.md). |
| Cutoff-uniform bound on the renormalised single-loop expectation | **Written; verification outstanding** | Verify the full R-step induction and its large-field weighted-response premises, including the post-R acceptance arguments, scalar remainders and wrap bounds. |
| Subsequential convergence of single-loop expectations | **Automatic once uniform boundedness holds** | Bounded-sequence compactness and diagonal extraction supply the result. No separate RG estimate is needed. See the [continuum note, §8](drafts/WILSON_IT1_CONTINUUM_LIMIT_CLOSURE_2026_10_26.md). |

### Ultraviolet Cutoff Comparison and the Continuum Limit

| Claim | Completion | Outstanding work |
|---|---|---|
| Exact normalised comparison of consecutive cutoffs | **Written** | The matched decomposition and normalised difference retain the physical denominator and perimeter/corner normalisations. See the [Cauchy draft, §§2–3 and 7](drafts/WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md). |
| Extra-generation contribution and old-scale tails | **Written** | Geometric decay for regular terms and polynomial decay for R-terms use the running-coupling bounds. See the [Cauchy draft, §4](drafts/WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md) and the [beta-function derivations](drafts/BETA_FUNCTION_WILSON_LOOPS.md), with their construction and source assumptions. |
| Classical action and minimiser comparison at regular real backgrounds | **Written; verification outstanding** | The real-background comparison has completed packet 10. Verify its complex and multiscale extensions and their remaining inherited estimates. See the [Cauchy draft, §9](drafts/WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md) and the [large-field note](drafts/WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md). |
| Gaussian covariance and quadratic-form comparison | **Written; verification outstanding** | Localised operator, shell and nonlinear fixed-point comparisons are derived in the [walk-factor note, §§10–12](drafts/WILSON_IT1_WALK_FACTOR_DIFFERENCE_2026_10_28.md); verify their application to the individual multiscale ingredients. |
| Localised lift between the fine lattices | **Written; verification outstanding** | The construction and collar-mismatch tail estimate require verification against their consumers. |
| Complex-domain admissibility of lifted configurations | **Written; verification outstanding** | Complex fluctuation data, composite configurations, finer-layer crossings and the complex R-term class bound have derivations. Verify the lift, current and domain arguments under their stated parameter choices. See the [Cauchy draft, §§5 and 10.5](drafts/WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md). |
| Quadratic moment of the lifted activity sum | **Written; verification outstanding** | Verify the plane-resolved marginal extraction and its boundary-error estimate. The full quadratic tensor is retained; Euclidean covariance of the lifted sum is not assumed. |
| Relative weights of large-field contributions at the stopping scale | **Written; verification outstanding** | Whole-integral comparison and history-cost payment require verification under the stated fixed-volume and loop/coupling restrictions. See the [Cauchy draft, §11](drafts/WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md). |
| Differences of characteristic functions and cutoff functions | **Written; verification outstanding** | Shell estimates and the soft-cutoff decomposition require consistent source-domain and threshold checks. |
| [Individual localised propagators and walk-factor differences](drafts/WILSON_IT1_WALK_FACTOR_DIFFERENCE_2026_10_28.md) | **Written; verification outstanding** | Wδ-1–Wδ-3 and the collar comparison Wδ-4 are derived, awaiting review in their current form. Verify the shell defects, fine-side lift, nonlinear functions and boundary-collar estimates. |
| [Differences of large-field integrands and loop dressings](drafts/WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md) | **Written; verification outstanding** | Verify the remaining large-field and external premises in the [packet plan](drafts/WILSON_IT1_LF_PACKET_PLAN_2026_11_04.md). The weighted-response packets retain their dependency qualifications. Packet 10 is closed at its stated scope. LF-W inherits these inputs. |
| [Interface cancellations and multiplier comparison](drafts/WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md) | **Written; verification outstanding** | The multiscale alignment, interface π-part and twist estimates are derived in the [large-field note, §4(d)](drafts/WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md). Verify the current, gauge and complex-domain arguments and their constant choices. |
| [Marked component sums and connected exponentiation](drafts/WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md) | **Written; verification outstanding** | Verify the marked insertion expansion, its general, odd and quadratic insertion bounds, and its application to the activity differences and large-field quotients with the full interacting measure. See the [Cauchy draft, §§8.5–8.6](drafts/WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md). |
| Coupled recursion for activity, R-term and coupling differences | **Written; verification outstanding** | The recursion and its weighted-norm solution are derived in the [Cauchy draft, §§8.3–8.7](drafts/WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md). Verify the large-field feedback, source/rate bounds and coupling conditions used in that solution. |
| Summable Cauchy estimate and full-sequence continuum limit | **Written; verification outstanding** | For one loop, §7 includes the leading word, scalar constants, transports and wraps in the normalised comparison and its summability. Verify the recent repairs and their large-field, lift and class estimates. See the [Cauchy draft, §7](drafts/WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md). |

### Two Wilson Loops

The pair results concern two vertex-disjoint squares. The extension to any finite family of pairwise disjoint loops is listed separately.

| Claim | Completion | Outstanding work |
|---|---|---|
| First RG step for the pair expectation | **In manuscript** | Product of the individual perimeter/corner normalisations, mixed contributions and remainder bounds are supplied. See [V4's two-loop theorem](WILSON_FIRST_RG_STEP_V4.tex). |
| Separation decay of first-step mixed contributions | **In manuscript** | Exponential separation bounds hold for the stated mixed activities and scalar correction. |
| [Inductive pair class and propagation of mixed insertions through fluctuation steps](drafts/WILSON_IT1_TWO_LOOPS_UNIFORM_BOUND_2026_10_27.md) | **Written; verification outstanding** | The pair class, fluctuation-step production, carry and two-component count are derived in §§2–6A. Verify them with the inherited single-loop inputs. |
| [R-steps for the pair](drafts/WILSON_IT1_TWO_LOOPS_UNIFORM_BOUND_2026_10_27.md) | **Written; verification outstanding** | Verify R-eval as a whole, its complex gauge transformations and large-field weighted-response premises, R-round and R-att-ext. R-member and R-eval-cr have reviews conditional on R-eval. The localisation of carried insertions also awaits review. |
| [Cutoff-uniform bound on the renormalised pair expectation](drafts/WILSON_IT1_TWO_LOOPS_UNIFORM_BOUND_2026_10_27.md) | **Written; verification outstanding** | Verify the full R-step chain and inherited single-loop inputs, including the weighted-response and localisation estimates. The member-merging and cross-insertion weight reviews remain conditional on R-eval. |
| Subsequential convergence of pair expectations | **Automatic once uniform boundedness holds** | Compactness supplies subsequences; no separate substantive RG estimate is required. |
| Full-sequence continuum limit of the pair expectation | **Written; verification outstanding** | The normalised comparison and summability are derived in §§3–7. Verify the repaired interpolation at enlarged amplitudes and lowered decay, the cross and wrap carry, scalar constants and inherited inputs. See the [pair Cauchy draft](drafts/WILSON_IT1_TWO_LOOPS_CAUCHY_2026_11_05.md). |
| [Decay of the connected two-loop correlation and factorisation at large separation](drafts/WILSON_IT1_PAIR_FACTORISATION_2026_11_05.md) | **Partial/open** | Verify long-group locality and the assembled near/far bound. Complete the tail estimate for near cluster terms of far large-field components, #PF3.2-8d1, and the stopping-scale covariance estimates (B1–B4), including large-field labels. The target concerns loop sizes relative to separation on a fixed torus. |
| Correlation functions of arbitrarily many disjoint Wilson loops | **Written; verification outstanding** | Verify the several-component class and counts, §9’s first-step extension and §10’s Cauchy transfers. The scope is each fixed finite family of vertex-disjoint squares in coordinate planes, with constants and coupling thresholds depending on the number of loops. See the [multiloop draft](drafts/WILSON_IT1_N_LOOPS_UNIFORM_BOUND_2026_11_05.md). |

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

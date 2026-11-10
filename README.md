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


## Main Theorem

Our work focuses solely on attempting to give a robust construction of the correlation functions of renormalised Wilson loops in **finite volume**. Because the Schwinger functions will have been obtained via a lattice-based renormalisation group construction, the hypercubic Osterwalder-Schrader axioms will constitute solely routine checks rather than needing new mathematics. We are currently not pursuing an infinite-volume construction, since (as per our personal judgment), the lack of a viable route for proving the existence of a mass gap makes it fundamentally less interesting (other people may disagree with us with good reason).

We believe that we have an LLM-generated proof of the following result.

**Theorem (Continuum Limit of Renormalised Wilson Loops).** Let $G$ be a compact connected simple Lie group and fix a four-dimensional periodic torus admitted by Bałaban's construction. For any integer $n\geqslant 1$, let $C_1,\ldots,C_n$ be a fixed family of pairwise disjoint oriented squares, with sides parallel to coordinate axes, vertices on a common lattice of spacing $uL^{-q}$ for some integer $q\geqslant 0$, and side lengths at most half the torus period. For each $i$, let $\chi_i$ be a normalised irreducible character of $G$. There is a threshold $\bar g_0>0$ such that the following holds for every reference coupling $0<\bar g<\bar g_0$.

At lattice spacing $\varepsilon_K = uL^{-K}$, we can choose the bare coupling $g_0(\varepsilon_K,\bar g)$ so that the running coupling at scale $u$ equals $\bar g$. For each loop $C_i$, there exists a sequence of multiplicative counterterms $\left(\kappa_{C_i}^{(K)} \right)_{K \in \N}$, such that the renormalised correlation function has a finite limit along the full sequence of ultraviolet cutoffs,
$$
F_K(C_1,\ldots,C_n)
\coloneqq
\frac{\mathbb E_{\varepsilon_K}\left[\prod_{i=1}^{n}W_{\chi_i}(C_i)\right]}
{\prod_{i=1}^{n}\kappa_{C_i}^{(K)}}
\;\overset{K \to \infty}{\longrightarrow}\;
\mathcal W_{\mathrm{ren}}(C_1,\ldots,C_n)\in\mathbb C
\;.
$$

The statement holds for every finite number of disjoint loops, the correlation functions are [nonzero](drafts/WILSON_IT1_PAIR_NONVANISHING_2026_11_10.md#the-theorems) and [reflection positive](drafts/WILSON_IT1_PAIR_REFLECTION_POSITIVITY_2026_11_10.md#finite-products). The RG parameters, coupling threshold and bounds may depend on the family, its characters and the torus. 

The proof is written in the [single-loop Cauchy draft](drafts/WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md), §7, the [pair Cauchy draft](drafts/WILSON_IT1_TWO_LOOPS_CAUCHY_2026_11_05.md), §§6–7, and the [multiloop draft](drafts/WILSON_IT1_N_LOOPS_UNIFORM_BOUND_2026_11_05.md), §§8–10.

## Progress of the Construction


Our current progress is as follows.

| Main step | Completion | Details |
|---|---|---|
| [First RG step for one loop and two disjoint loops](WILSON_FIRST_RG_STEP_V4.tex) | **Complete** | The stated finite-cutoff theorems and uniform bounds are written. |
| [Small-field iteration and large-field insertions](drafts/WILSON_IT1_D26_CLOSURE_2026_10_24.md) | **Written** | — |
| [R-steps for single and two-loop insertions](drafts/WILSON_IT1_D27_CLOSURE_2026_10_26.md) | **Written** | — |
| [Relative weights of large-field contributions](drafts/WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md) | **Written** | — |
| [Cutoff-uniform bounds and subsequential limits](drafts/WILSON_IT1_TWO_LOOPS_UNIFORM_BOUND_2026_10_27.md) | **Written** | Subsequential convergence follows from cutoff-uniform boundedness and compactness. |
| [Comparison of successive ultraviolet cutoffs](drafts/WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md) | **Written** | — |
| [Full-sequence continuum limits](drafts/WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md) | **Written** | See the [pair Cauchy extension](drafts/WILSON_IT1_TWO_LOOPS_CAUCHY_2026_11_05.md) and the [finite-family extension](drafts/WILSON_IT1_N_LOOPS_UNIFORM_BOUND_2026_11_05.md). |
| Correlation functions of arbitrarily many disjoint Wilson loops | **Written** | A first-step extension, cutoff-uniform bound and full-sequence argument are written for each fixed finite family of disjoint squares in coordinate planes. See the [multiloop draft](drafts/WILSON_IT1_N_LOOPS_UNIFORM_BOUND_2026_11_05.md). |
| [Decay of connected two-loop correlations](drafts/WILSON_IT1_PAIR_FACTORISATION_2026_11_05.md) | **Partial** | A cutoff-uniform bound is derived. The bound retains terms independent of separation. |


We are currently working on consolidating the markdown files which contain the proofs into a single LaTeX manuscript.


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

Supporting derivations are collected in the [Bałaban proof notes](drafts/balaban_proofs/).

Start with the [D2 step map](drafts/WILSON_IT1_D2_STEP_MAP_2026_10_22.md) and [IT-1 note](drafts/WILSON_IT1_LINE_DEFECT_2026_10_21.md), then the current [large-field](drafts/WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md) and [walk-factor](drafts/WILSON_IT1_WALK_FACTOR_DIFFERENCE_2026_10_28.md) drafts. The [beta-function note](drafts/BETA_FUNCTION_WILSON_LOOPS.md) supplies the coupling estimates used in these drafts. Their stated construction and source assumptions remain in force.

The [27 October Cauchy-estimate draft](drafts/WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md) derives the one-step stability estimate, coupling and large-field feedbacks, lattice-refinement bounds for background fields and fluctuation covariances, and relative-weight comparison. The [cutoff-comparison note](drafts/WILSON_IT1_CONTINUUM_CUTOFF_COMPARISON_2026_10_27.md) records an earlier investigation of the cutoff comparison.

The [Bałaban paper-label dictionary](drafts/BALABAN_PAPER_LABELS.md) gives official titles, citations and links for the internal labels used throughout these drafts.



## Detailed Breakdown of Current Progress

Assessment of the working drafts as of 10 November 2026. The linked drafts are included in this repository.

**In manuscript** means a theorem and proof are present under their stated assumptions. **Written** means the derivation exists. **Partial** means that part of the argument is written and further estimates remain to be derived.

### Single-Loop RG Construction

| Claim | Completion | Details |
|---|---|---|
| First RG step for a square Wilson loop | **In manuscript** | Exact normalised decomposition, perimeter and corner extraction, and defect and boundary bounds are supplied. See [V4's main theorem](WILSON_FIRST_RG_STEP_V4.tex). |
| First-step leading-term bounds and exponential moment | **In manuscript** | The stated estimates retain contour-length dependence; they do not alone give cutoff-uniform control at fixed physical loop size. |
| Inductive class of Wilson loop insertions | **Written** | — |
| Small-field RG transformation and contraction of deviation insertions | **Written** | See the [step map](drafts/WILSON_IT1_D2_STEP_MAP_2026_10_22.md), [complex covariance](drafts/WILSON_IT1_COMPLEX_COVARIANCE_2026_10_29.md) and [averaged current](drafts/WILSON_IT1_RMJ_CLOSURE_2026_10_30.md). |
| D2.6: production, propagation and payment of large-field insertions | **Written** | See [D2.6](drafts/WILSON_IT1_D26_CLOSURE_2026_10_24.md). |
| Analytic representation of shifted insertions | **Written** | See [O4](drafts/WILSON_IT1_O4_CLOSURE_2026_10_26.md) and [complex covariance](drafts/WILSON_IT1_COMPLEX_COVARIANCE_2026_10_29.md). |
| Perimeter and corner extraction at subsequent steps | **Written** | D2.3 and D2.7 specify the scalar extraction. |
| Preservation of the insertion class through arbitrary R-steps | **Written** | D2.7 item 15.8 supplies the gas-link payment and post-R acceptance derivations. See [D2.7](drafts/WILSON_IT1_D27_CLOSURE_2026_10_26.md) and the [evaluation estimates](drafts/WILSON_IT1_TWO_LOOPS_UNIFORM_BOUND_2026_10_27.md). |
| Cutoff-uniform bound on the renormalised single-loop expectation | **Written** | — |
| Subsequential convergence of single-loop expectations | **Written** | Bounded-sequence compactness and diagonal extraction supply the result. No separate RG estimate is needed. See the [continuum note, §8](drafts/WILSON_IT1_CONTINUUM_LIMIT_CLOSURE_2026_10_26.md). |

### Ultraviolet Cutoff Comparison and the Continuum Limit

| Claim | Completion | Details |
|---|---|---|
| Exact normalised comparison of consecutive cutoffs | **Written** | The matched decomposition and normalised difference retain the physical denominator and perimeter/corner normalisations. See the [Cauchy draft, §§2–3 and 7](drafts/WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md). |
| Extra-generation contribution and old-scale tails | **Written** | Geometric decay for regular terms and polynomial decay for R-terms use the running-coupling bounds. See the [Cauchy draft, §4](drafts/WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md) and the [beta-function derivations](drafts/BETA_FUNCTION_WILSON_LOOPS.md), with their construction and source assumptions. |
| Classical action and minimiser comparison at regular real backgrounds | **Written** | The real-background derivation has been reviewed under its stated hypotheses. See the [Cauchy draft, §9](drafts/WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md) and the [review record](drafts/WILSON_IT1_LF_TRIAGE_P10_R35_2026_11_05.md). |
| Gaussian covariance and quadratic-form comparison | **Written** | Localised operator, shell and nonlinear fixed-point comparisons are derived in the [walk-factor note, §§10–12](drafts/WILSON_IT1_WALK_FACTOR_DIFFERENCE_2026_10_28.md). |
| Localised lift between the fine lattices | **Written** | — |
| Complex-domain admissibility of lifted configurations | **Written** | Complex fluctuation data, composite configurations, finer-layer crossings and the complex R-term class bound have derivations. See the [Cauchy draft, §§5 and 10.5](drafts/WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md). |
| Quadratic moment of the lifted activity sum | **Written** | The full quadratic tensor is retained; Euclidean covariance of the lifted sum is not assumed. |
| Relative weights of large-field contributions at the stopping scale | **Written** | See the [Cauchy draft, §11](drafts/WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md). |
| Differences of characteristic functions and cutoff functions | **Written** | — |
| [Individual localised propagators and walk-factor differences](drafts/WILSON_IT1_WALK_FACTOR_DIFFERENCE_2026_10_28.md) | **Written** | Wδ-1–Wδ-3 and the collar comparison Wδ-4 are derived. |
| [Differences of large-field integrands and loop dressings](drafts/WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md) | **Written** | — |
| [Interface cancellations and multiplier comparison](drafts/WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md) | **Written** | The multiscale alignment, interface π-part and twist estimates are derived in the [large-field note, §4(d)](drafts/WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md). |
| [Marked component sums and connected exponentiation](drafts/WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md) | **Written** | See the [Cauchy draft, §§8.5–8.6](drafts/WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md). |
| Coupled recursion for activity, R-term and coupling differences | **Written** | The recursion and its weighted-norm solution are derived in the [Cauchy draft, §§8.3–8.7](drafts/WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md). |
| Summable Cauchy estimate and full-sequence continuum limit | **Written** | For one loop, §7 includes the leading word, scalar constants, transports and wraps in the normalised comparison and its summability. See the [Cauchy draft, §7](drafts/WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md). |

### Two Wilson Loops

The pair results concern two vertex-disjoint squares. The extension to any finite family of pairwise disjoint loops is listed separately.

| Claim | Completion | Details |
|---|---|---|
| First RG step for the pair expectation | **In manuscript** | Product of the individual perimeter/corner normalisations, mixed contributions and remainder bounds are supplied. See [V4's two-loop theorem](WILSON_FIRST_RG_STEP_V4.tex). |
| Separation decay of first-step mixed contributions | **In manuscript** | Exponential separation bounds hold for the stated mixed activities and scalar correction. |
| [Inductive pair class and propagation of mixed insertions through fluctuation steps](drafts/WILSON_IT1_TWO_LOOPS_UNIFORM_BOUND_2026_10_27.md) | **Written** | The pair class, fluctuation-step production, carry and two-component count are derived in §§2–6A. |
| [R-steps for the pair](drafts/WILSON_IT1_TWO_LOOPS_UNIFORM_BOUND_2026_10_27.md) | **Written** | — |
| [Cutoff-uniform bound on the renormalised pair expectation](drafts/WILSON_IT1_TWO_LOOPS_UNIFORM_BOUND_2026_10_27.md) | **Written** | — |
| Subsequential convergence of pair expectations | **Written** | Compactness supplies subsequences; no separate substantive RG estimate is required. |
| Full-sequence continuum limit of the pair expectation | **Written** | The normalised comparison and summability are derived in §§3–7. See the [pair Cauchy draft](drafts/WILSON_IT1_TWO_LOOPS_CAUCHY_2026_11_05.md). |
| [Decay of the connected two-loop correlation and factorisation at large separation](drafts/WILSON_IT1_PAIR_FACTORISATION_2026_11_05.md) | **Partial** | The far-component cluster tails and stopping-scale covariance are bounded in §§3–4. The resulting cutoff-uniform bound retains terms independent of separation. |
| Correlation functions of arbitrarily many disjoint Wilson loops | **Written** | The scope is each fixed finite family of vertex-disjoint squares in coordinate planes, with constants and coupling thresholds depending on the number of loops. See the [multiloop draft](drafts/WILSON_IT1_N_LOOPS_UNIFORM_BOUND_2026_11_05.md). |

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

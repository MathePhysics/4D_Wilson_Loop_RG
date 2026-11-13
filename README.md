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

At lattice spacing $\varepsilon_K = uL^{-K}$, we can choose the bare coupling $g_0(\varepsilon_K,\bar g)$ so that the running coupling at scale $u$ equals $\bar g$. For each loop $C_i$, there exists a sequence of multiplicative counterterms $\left(\kappa_{C_i}^{(K)} \right)_{K \in \mathbb{N}}$, such that the renormalised correlation function has a finite limit along the full sequence of ultraviolet cutoffs,

$$
F_K(C_1,\ldots,C_n)
\mathrel{:=}
\frac{\mathbb E_{\varepsilon_K}\left[\prod_{i=1}^{n}W_{\chi_i}(C_i)\right]}
{\prod_{i=1}^{n}\kappa_{C_i}^{(K)}}
\xrightarrow{K \to \infty}
\mathcal W_{\mathrm{ren}}(C_1,\ldots,C_n)\in\mathbb C
.
$$

The statement holds for every finite number of disjoint loops, the correlation functions are [nonzero](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf) and [reflection positive](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf), with [torus covariance](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf). The RG parameters and the coupling threshold for convergence depend on the loops only through their shape, independently of their lengths and number.

We also establish [non-Gaussianity](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf), in the sense that our correlation functions cannot be obtained from free, i.e. Abelian, Yang–Mills theory.

Theorem 1.5 and Sections 8–11 give the continuum-limit argument in the [manuscript](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf). Supporting estimates are collected in the [Bałaban supplement](Continuum%20Limit%20Manuscript%20Draft/BALABAN_SUPPLEMENT.pdf).

## Progress of the Construction


Our current progress is as follows.

| Main step | Completion | Details |
|---|---|---|
| [First RG step for one loop and two disjoint loops](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf) | **In manuscript** | The stated finite-cutoff theorems and uniform bounds are written. See [Theorem 5.4](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf). |
| [Small-field iteration and large-field insertions](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf) | **In manuscript** | [Section 6](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf). |
| [R-steps for single and two-loop insertions](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf) | **In manuscript** | [§6.12](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf) and [Proposition 7.10](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf). |
| [Relative weights of large-field contributions](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf) | **In manuscript** | [Proposition 8.4](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf). |
| [Cutoff-uniform bounds and subsequential limits](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf) | **In manuscript** | [Theorem 8.7](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf) gives the bound. Subsequential convergence follows by compactness. |
| [Comparison of successive ultraviolet cutoffs](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf) | **In manuscript** | [Theorem 11.1](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf). |
| [Full-sequence continuum limits](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf) | **In manuscript** | [Theorem 1.5](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf) and [Section 11](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf). |
| Correlation functions of arbitrarily many disjoint Wilson loops | **In manuscript** | Every finite family of pairwise vertex-disjoint admissible loops, with RG parameters and convergence threshold depending only on loop shape, independently of loop lengths and number. See [Theorem 1.5](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf). |
| [Decay of connected two-loop correlations](drafts/WILSON_IT1_PAIR_FACTORISATION_2026_11_05.md) | **Partial** | A cutoff-uniform bound is derived. The bound retains terms independent of separation. |


The continuum-limit proof and its supporting estimates are collected in the [Continuum Limit Manuscript Draft folder](Continuum%20Limit%20Manuscript%20Draft/).


## Current Manuscripts

- **Continuum-limit manuscript draft.** [PDF](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf) and [LaTeX source](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.tex).
- **Bałaban supplement.** [PDF](Continuum%20Limit%20Manuscript%20Draft/BALABAN_SUPPLEMENT.pdf) and [LaTeX source](Continuum%20Limit%20Manuscript%20Draft/BALABAN_SUPPLEMENT.tex).

The manuscript folder includes the shared [bibliography](Continuum%20Limit%20Manuscript%20Draft/refs.bib) and [preprint class](Continuum%20Limit%20Manuscript%20Draft/preprint.cls).

- **Updated V4:** [PDF](WILSON_FIRST_RG_STEP_V4.pdf) and [LaTeX source](WILSON_FIRST_RG_STEP_V4.tex).

## Manuscripts under Construction

The [Manuscripts under Construction folder](Manuscripts%20under%20Construction/) contains:

- **V5:** [PDF](Manuscripts%20under%20Construction/WILSON_FIRST_RG_STEP_V5.pdf), [LaTeX source](Manuscripts%20under%20Construction/WILSON_FIRST_RG_STEP_V5.tex), and [bibliography](Manuscripts%20under%20Construction/WILSON_FIRST_RG_STEP_V5.bib).
- **Pedagogical summary (V4 companion):** [PDF](Manuscripts%20under%20Construction/V4_Pedagogical_Summary_2026_10_22.pdf) and [LaTeX source](Manuscripts%20under%20Construction/V4_Pedagogical_Summary_2026_10_22.tex).

The summary gives a notation guide and explanations of the construction, estimates and two-loop result. V4 is the reference for the first RG step. V5 remains under construction.

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

Assessment of the manuscript and supporting drafts as of 12 November 2026. The linked drafts are included in this repository.

**In manuscript** means a theorem and proof are present under their stated assumptions. **Partial** means that part of the argument is written and further estimates remain to be derived.

### Single-Loop RG Construction

| Claim | Completion | Details |
|---|---|---|
| First RG step for an admissible Wilson loop | **In manuscript** | Exact normalised decomposition, perimeter and corner extraction, and defect and boundary bounds are supplied. See [Theorem 5.4](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf). |
| First-step leading-term bounds and exponential moment | **In manuscript** | The stated estimates retain contour-length dependence; they do not alone give cutoff-uniform control at fixed physical loop size. See [V4](WILSON_FIRST_RG_STEP_V4.pdf). |
| Inductive class of Wilson loop insertions | **In manuscript** | [Definition 5.2](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf) and [Theorem 6.1](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf). |
| Small-field RG transformation and contraction of deviation insertions | **In manuscript** | [§6.7](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf) and [§6.9](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf). |
| D2.6: production, propagation and payment of large-field insertions | **In manuscript** | [§6.12](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf) and the [Bałaban supplement](Continuum%20Limit%20Manuscript%20Draft/BALABAN_SUPPLEMENT.pdf). |
| Analytic representation of shifted insertions | **In manuscript** | [§6.1](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf) and [§6.3](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf). |
| Perimeter and corner extraction at subsequent steps | **In manuscript** | [Section 7](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf). |
| Preservation of the insertion class through arbitrary R-steps | **In manuscript** | [Theorem 6.1](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf) and [§6.12](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf). |
| Cutoff-uniform bound on the renormalised single-loop expectation | **In manuscript** | [Theorem 8.7](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf). The bound retains loop-length dependence. |
| Subsequential convergence of single-loop expectations | **In manuscript** | Follows from [Theorem 1.5](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf). |

### Ultraviolet Cutoff Comparison and the Continuum Limit

| Claim | Completion | Details |
|---|---|---|
| Exact normalised comparison of consecutive cutoffs | **In manuscript** | The matched decomposition and normalised difference retain the physical denominator and perimeter/corner normalisations. See [§10.1](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf) and [§11.1](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf). |
| Extra-generation contribution and old-scale tails | **In manuscript** | Geometric decay for regular terms and polynomial decay for R-terms use the running-coupling bounds. See [§11.2](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf) and [Section 4](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf). |
| Classical action and minimiser comparison at regular real backgrounds | **In manuscript** | [Proposition 10.6](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf) and [§11.1](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf). |
| Gaussian covariance and quadratic-form comparison | **In manuscript** | Localised operator, shell and nonlinear fixed-point comparisons are derived in [Section 9](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf) and the [Bałaban supplement](Continuum%20Limit%20Manuscript%20Draft/BALABAN_SUPPLEMENT.pdf). |
| Localised lift between the fine lattices | **In manuscript** | [§9.3](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf), [§10.3](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf) and the [Bałaban supplement](Continuum%20Limit%20Manuscript%20Draft/BALABAN_SUPPLEMENT.pdf). |
| Complex-domain admissibility of lifted configurations | **In manuscript** | Complex fluctuation data, composite configurations, finer-layer crossings and the complex R-term class bound have derivations. See [§10.3](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf) and the [Bałaban supplement](Continuum%20Limit%20Manuscript%20Draft/BALABAN_SUPPLEMENT.pdf). |
| Quadratic moment of the lifted activity sum | **In manuscript** | The full quadratic tensor is retained. See [§11.1](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf). |
| Relative weights of large-field contributions at the stopping scale | **In manuscript** | [§8.3](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf). |
| Differences of the test functions | **In manuscript** | [§10.2](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf). |
| [Individual localised propagators and walk-factor differences](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf) | **In manuscript** | [Section 9](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf) and the [Bałaban supplement](Continuum%20Limit%20Manuscript%20Draft/BALABAN_SUPPLEMENT.pdf). |
| [Differences of large-field integrands and loop dressings](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf) | **In manuscript** | [Section 10](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf) and the [Bałaban supplement](Continuum%20Limit%20Manuscript%20Draft/BALABAN_SUPPLEMENT.pdf). |
| [Interface cancellations and multiplier comparison](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf) | **In manuscript** | The multiscale alignment, interface π-part and twist estimates are derived in [§10.3](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf) and the [Bałaban supplement](Continuum%20Limit%20Manuscript%20Draft/BALABAN_SUPPLEMENT.pdf). |
| [Marked component sums and connected exponentiation](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf) | **In manuscript** | [§11.3](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf) and [§11.5](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf). |
| Coupled recursion for activity, R-term and coupling differences | **In manuscript** | The recursion and its weighted-norm solution are derived in [§11.5](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf) and [Proposition 11.8](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf). |
| Summable Cauchy estimate and full-sequence continuum limit | **In manuscript** | [Theorem 11.1](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf) and [Theorem 1.5](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf). |

### Two Wilson Loops

The continuum-limit results cover two vertex-disjoint admissible loops. The extension to any finite family of pairwise disjoint loops is listed separately.

| Claim | Completion | Details |
|---|---|---|
| First RG step for the pair expectation | **In manuscript** | Product of the individual perimeter/corner normalisations, mixed contributions and remainder bounds are supplied. See [Theorem 5.4](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf). |
| Separation decay of first-step mixed contributions | **In manuscript** | Exponential separation bounds hold for the stated mixed activities and scalar correction. See [V4's two-loop theorem](WILSON_FIRST_RG_STEP_V4.tex). |
| [Inductive pair class and propagation of mixed insertions through fluctuation steps](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf) | **In manuscript** | [Definition 5.2](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf) and [Section 6](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf). |
| [R-steps for the pair](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf) | **In manuscript** | [§6.12](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf) and [Proposition 7.10](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf). |
| [Cutoff-uniform bound on the renormalised pair expectation](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf) | **In manuscript** | [Theorem 8.7](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf). The bound retains loop-length dependence. |
| Subsequential convergence of pair expectations | **In manuscript** | Follows from [Theorem 1.5](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf). |
| Full-sequence continuum limit of the pair expectation | **In manuscript** | [Theorem 1.5](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf) and [§11.9](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf). |
| [Decay of the connected two-loop correlation and factorisation at large separation](drafts/WILSON_IT1_PAIR_FACTORISATION_2026_11_05.md) | **Partial** | The far-component cluster tails and stopping-scale covariance are bounded in §§3–4. The resulting cutoff-uniform bound retains terms independent of separation. |
| Correlation functions of arbitrarily many disjoint Wilson loops | **In manuscript** | Every finite family of pairwise vertex-disjoint admissible loops, with RG parameters and convergence threshold depending only on loop shape, independently of loop lengths and number. See [Theorem 1.5](Continuum%20Limit%20Manuscript%20Draft/WILSON_LOOPS_CONTINUUM_LIMIT.pdf). |

## Build

Use a recent TeX Live or MiKTeX installation with pdfLaTeX, BibTeX and latexmk. Build the continuum-limit manuscript before the supplement so that its external references resolve.

```sh
cd "Continuum Limit Manuscript Draft"
latexmk -pdf -interaction=nonstopmode -halt-on-error WILSON_LOOPS_CONTINUUM_LIMIT.tex
latexmk -pdf -interaction=nonstopmode -halt-on-error BALABAN_SUPPLEMENT.tex
```

For V5:

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

# Stage 4c: regional square scalar and the perimeter/corner extraction

Status (19 October 2026): Sections 1, 2, 5 and 8 are in WILSON_FIRST_RG_STEP_V3.tex in TeX form as the last appendix `app:regional-scalar` (identification `lem:c4c-2-1`, scalar `prop:c4c-5-1`, physical identity `cor:c4c-5-2`; the TeX block is §9 below). The translation was reviewed on 19 October 2026 as one isolated referee packet (`verification/isolated_reviewer/reviews/tr-c4c-20261019-r1/review.txt`) and the TeX repaired from the report (V3 SHA256 abf0d60cc65a5836, 23:36); the TeX in V3 is authoritative where it differs from the TeX block in §9, which is not re-mirrored. Sections 3, 3.1, 4, 6 and 7 are already the proof of `prop:regional-square-extraction` in the manuscript and were not inserted again. The stage 5 section's `\draftref{stage 4C, ...}` citation form is removed; it cites the appendix.

## 1. Claim and conventions

This is a first-step statement. Fix one of the two cutoff prescriptions sigma, the same bare coupling g_0, character, RG1 averaging/mean prescription and designated-bond convention as WILSON_FIRST_RG_STEP_V2.tex. The character is irreducible and normalised. Use the standing compatible-torus and collar conditions of Stage 1. The fine torus periods are N_mu=L K_mu, and C_n is a coarse translate of the counterclockwise square with vertices 0,nLe_1,nL(e_1+e_2),nLe_2, with n coarse segments of length L on each side, with K_mu>=3(n+2). Its physical perimeter is P(C_n)=4nL epsilon.

Let A_cov be the set of histories for which every contour bond belongs to Omega_1 and all its free-input stencils lie in I, as in Stage 1 Lemma covered. Let xi belong to A_cov. Put D=I, the young free-bond carrier, and take D^c relative to the torus free-bond carrier E_{*,T}; distances below use the periodic fine-bond metric of the regional proposition. For segment j in the cyclic set J_C={0,...,4n-1}, K_j is the union of the fixed free-input stencils of its fine traversals. Take R_0 to include the fixed label and covariance ranges from the regional proposition and set

$$
d_j=\max(0,d_T(K_j,D^c)-R_0),\qquad
\iota_T=\max(0,N_{\min}/4-R_0),\qquad
N_{\min}=\min_\mu N_\mu\;.
$$

There is no distance to a side endpoint in d_j. An empty complement has infinite distance, and exp(-infinity)=0. All constants below may depend on the fixed character, group, L and forest parameters; they are independent of n, compatible periods and the shape of D. Choose g_0 sufficiently small after these constants, satisfying the common flat/region thresholds. Tau denotes the marked-forest parameter of eq:marginal-fixed-forest-bound. Enlarging a fixed majorant constant multiplies tau by a fixed factor only; this is absorbed into the constants and coupling threshold below.

The claim is that the existing regional scalar has the representation

$$
S^\circ_{\xi,C_n}
 =\exp[-\delta m^\sigma(g_0,\epsilon)P(C_n)]
   \left(z_{\rm c}^\sigma(g_0,\pi/2)\right)^4
   \exp(E^\circ_\xi)\;,
$$

with the coefficients already defined in eq:marginal-square-mass and eq:corner-square-factor, and

$$
|E^\circ_\xi|\leq C\tau^2
 \left[\sum_{j\in J_C}e^{-c d_j}
       +4n e^{-c\iota_T}+(n+1)e^{-cn}\right]\;.
$$

The scalar and its nonzero logarithm are those of the regional conditional reference integral. No physical history weight or large-field indicator is evaluated at flat fields. The bound does not assume the whole loop is far from the integration boundary: d_j=0 retains a boundary contribution.

## 2. Equality with a regional square integral

Let H_T be the full flat free-field precision used in the manuscript and C_T=H_T^{-1}. Write H_{D,T}=i_D^*H_T i_D and C_{D,T}=H_{D,T}^{-1}. Let P_{D,T}=sum_{v:supp(v) meets D}v(i_DB), using the original primitive labels, including all boundary-crossing action terms, as in eq:regional-weight. Let Theta_D^sigma be the same product of bond indicators. Define

$$
F_{D,C,T}
 =\log\frac{
 \int\Theta_D^\sigma(B)e^{P_{D,T}(B)}
    \chi(\operatorname{Hol}_{U_{g_0}(i_DB)}C_n)\,d\mu_{C_{D,T}}(B)}{
 \int\Theta_D^\sigma(B)e^{P_{D,T}(B)}\,d\mu_{C_{D,T}}(B)}\;.
$$

The logarithm will be defined by the connected source expansion below. The exterior link value in this formula is the identity, but no exterior factor of the physical measure is replaced.

Stage 1 eq:part1-reference-gas identifies S^circ directly with the normalised expectation of the full reference Wilson loop. At identity background the centred kernel has precision H^Omega_{id,II}, potentials evaluated at zero retained input, and the cutoff on I. The regional stencil identity and the collar ensure that every precision/primitive stencil touching I is inside Omega_1. Consequently H^Omega_{id,II}=i_D^*H_Ti_D; this equality includes diagonal contributions from plaquettes crossing D. The row solutions agree as analytic germs at zero by their defining equation and uniqueness. The Stage 1 Hilbert-ball domain and the manuscript max-norm domain have a convex common phase domain containing the closed cutoff box at the common coupling threshold. Analytic continuation on this domain identifies their values throughout that box. Stage 1 groups gauge primitives per centre y, while the manuscript indexes them by (y,x); their sums coincide, since terms with free-input support missing D vanish at i_DB. Every primitive with free support missing D is zero at i_DB, and every primitive meeting D is retained. Covered source rows have their free-input sets inside D, so their fine links equal U_{g_0}(i_DB). This proves

$$
S^\circ_{\xi,C_n}=e^{F_{D,C,T}}\;.
$$

This is the full-square version of eq:regional-kernel-identification: its kernel identification does not use straightness, only the source being a closed contraction with the given input stencils. The Gaussian normaliser cancels within the numerator/denominator ratio, not against the outer physical weight. The boundary map is the identity by the definition Psi^circ=id of the Stage 1 reference data.

## 3. Regional versus full-torus scalar

Use the protected-label forest expansion of the manuscript for the closed square, with all primitive and source labels retaining their original identities and supports restricted to D. Empty restricted source differences vanish. Restrictions preserve the finite input counts and ranges. In all three protected-label gases (regional, torus and bulk), use the manuscript rule: a component receives a shortest cyclic interval containing its source traversals, with ties broken by the fixed base ordering; webs are overlap-connected families of these intervals, and their interval is the union, possibly the whole circle. No Stage 1 group-promotion rule is used in these gases. Equality with S^circ is equality of integral ratios and does not require agreement of the two expansions term by term. A restricted carrier retains the original source traversal and hence its contour contact; the square hull/extent bound uses the same bounded source-to-stencil range. The density and positive-tree estimates of the regional proof apply unchanged. The weighted-load argument below gives convergent vacuum and sourced gas logarithms for the endpoint integrals. Only the indicated finite component integrals are differentiated during the comparison. The difference of their logarithms equals F_{D,C,T}; the source-free terms cancel against the original denominator. The logarithm is continued from zero in the fine-traversal source polynomial of eq:regional-wilson-polynomial. Thus it has no ambiguity and its exponential is the original ratio. Equality to a separately chosen logarithm of the Stage 1 group gas is not needed.

Denote the connected source weight by Phi_{D,C,T}(Gamma), its nonempty set of marked coarse segments by J_Gamma, and its extent by ell(Gamma). Define

$$
a_{D,C,T}(j)=\sum_{\Gamma:j\in J_\Gamma}
          \frac{\Phi_{D,C,T}(\Gamma)}{|J_\Gamma|}\;.
$$

Define a_{C,T}(j) by the identical expansion with D=E_{*,T}. Absolute convergence gives F_{D,C,T}=sum_j a_{D,C,T}(j) and F_{C,T}=sum_j a_{C,T}(j), where F_{C,T}=log(N_{C_n,T}^sigma/D_T^sigma).

The periodic resolvent identity gives

$$
C_{D,T}-(C_T)_{D,D}
 =C_{D,T}(H_T)_{D,D^c}(C_T)_{D^c,D}\;.
$$

Uniform spectral bounds and finite-range exponential decay yield, just as in eq:regional-covariance-difference,

$$
\|C_{D,T}(b,c)-C_T(b,c)\|
 \leq C e^{-a[d_T(b,D^c)+d_T(c,D^c)+d_T(b,c)]}\;.
$$

The row shell sums are bounded uniformly on the torus; no boundary-area factor occurs. Interpolate C_t=(1-t)(C_T)_{D,D}+t C_{D,T}. Its principal marginals have the same spectral interval, scalar colour structure and uniform decay as in the regional proof. The product rule in eq:regional-density-derivative differentiates both the Gaussian density and every forest edge direction, including the determinant. Its integrated majorant retains the source power tau^2 and gives

$$
|\partial_t\Phi_t(\Gamma)|
 \leq C\ell(\Gamma)^2e^{-a d_T(A_\Gamma,D^c)}U(\Gamma),\qquad
\sum_{\Gamma:j\in J_\Gamma}U(\Gamma)e^{\eta_1\ell(\Gamma)}\leq C\tau^2\;.
$$

Here U(Gamma) is the positive cluster majorant defined in the regional proof, with constants fixed for the square geometry; A_Gamma is its union of free carriers. The closed single-mark Schur cancellation survives because both covariances and their difference have scalar colour blocks. Corner-spanning source components therefore obey the same bound; they are not separated into products of side characters.

Let C_net bound the length of the carrier/stencil/contour network by C_net ell(Gamma)+R_0, as in the regional proof and the square hull estimate. Split each rooted sum at ell(Gamma)=d_j/(2C_net), treating d_j<=2R_*+2R_0 by the rooted bounds and enlarging C. The large part costs C tau^2 exp(-c d_j). In a smaller cluster every original source and primitive stencil lies in D and every carrier has distance at least d_j/2 from D^c. Its labels, cyclic source ordering and incompatibilities coincide in the regional and full-torus expansions. Only its covariance differs. Integrating the differentiated bound and paying ell^2 with half the extent reserve proves

$$
|a_{D,C,T}(j)-a_{C,T}(j)|\leq C\tau^2e^{-c d_j}\;.
$$

There is no side-endpoint loss because the comparison contour on both sides is the same closed square. For D=E_{*,T} the difference is identically zero. Summation gives

$$
|F_{D,C,T}-F_{C,T}|
 \leq C\tau^2\sum_{j\in J_C}e^{-c d_j}\;.
$$

This carries the boundary-crossing terms and their covariance effect; it does not replace the restricted precision by a principal marginal without payment.

### 3.1 Weighted regional square sums

This supplies the positive majorant used both in the regional comparison and in Section 4. Fix a common covariance decay exponent mu>0 and entry constant for C_{D,T}, C_T and the short-lift C_infinity marginals. The spectral lower bound is the common lambda=h_L^{-1}. In the component density/edge differentiation proof retain a remaining edge exponent mu_1<=min(mu,a)/8. All constants are fixed before g_0. Use the square geometry constant c_h, enlarged only for the fixed original stencil range, and put

$$
\alpha'=\frac{\mu_1}{1024(1+c_h)},\qquad
\eta'=\frac{\mu_1}{1024},\qquad
A'(p)=|A_p|+\alpha'H_p\;.
$$

Use original primitive identities even when their free supports are intersected with D. A nonzero restricted label contains a retained free bond. At each such bond at most q_* original labels can occur, with support size at most s_* and range at most R_*. Distinct source traversals keep distinct labels and their original positions. Hence on k carrier bonds the label choices are at most 2^{q_*k}; restriction creates no new overlap or source multiplicity. Forest connectivity together with support edges still joins the retained labels, with support-edge lengths at most R_*; contact positions are within R_* of that network. Thus H_gamma<=c_h ell(gamma) also for restricted components, including those meeting a corner.

Let u_gamma be the uniform positive forest majorant after degree payment, with the constants used in the density/edge comparison and with the explicit factor for a distinguished covariance derivative omitted. The latter is the single factor C ell^2 exp(-a d) displayed above. For periodisation it is C ell^2 exp(-c N_min). The same majorant works for all endpoints and interpolation marginals by the common spectral and entry bounds. Enlarging its fixed constant K_2 accounts for the Cauchy-radius reductions of the density derivative.

Multiplying component weights by exp(4|A_gamma|+8alpha'H_gamma+8eta'ell(gamma)) consumes less than the reserved edge decay; its carrier part only enlarges K_2. The label count, unused-edge product and rooted spatial tree sum therefore give the two series

$$
\sum_{k\geq1}K_2^k\tau^{\lceil k/s_*\rceil},\qquad
\sum_{k\geq1}K_2^k\tau^{\max(2,\lceil k/s_*\rceil)}\;.
$$

They bound vacuum and source loads, respectively, at a fixed spatial bond; the second also bounds a fixed traversal load. Group k by ceil(k/s_*) and choose K_2^{s_*}tau<=1/2. Both are bounded by fixed constants times tau and tau^2, respectively. The quadratic source power is retained under the covariance derivative by scalar colour blocks and constant-conjugation invariance; no matrix activity is estimated separately.

For any traversal x in the cyclic component interval, and theta=alpha',

$$
\mathbf1_{\{x\in h_\gamma\}}
 \leq\sum_{y\in S_\gamma}e^{-\theta d_C(x,y)}e^{\theta H_\gamma},\qquad
\sum_y e^{-\theta d_C(x,y)}\leq1+\frac{2}{e^\theta-1}\;.
$$

The extra interval weight is within the preceding 8alpha' reserve, so this converts the traversal-root load into an interval-root load with a fixed constant independent of n. Apply the positive overlap-tree recursion to source components, retaining the original factorials, with node cost alpha'H_gamma. For tau small the summed neighbour load is at most alpha'H_gamma/4, so the recursion is bounded by the component weight times exp(alpha'H_gamma). Unused reserves cover this recursion and the interval-root conversion. Let u_p be the resulting vacuum-component or source-web majorant. There is a constant C_*' independent of D,n,T such that

$$
\sup_b\sum_{p:b\in A_p}u_pe^{2A'(p)+2\eta'\ell(p)}\leq C_*'\tau,\qquad
\sup_x\sum_{W:x\in h_W}u_We^{2A'(W)+2\eta'\ell(W)}\leq C_*'\tau^2\;.
$$

The spatial source-only sum is also at most C_*'tau^2. Choose C_*'tau<=1/4 and C_*'tau^2<=alpha'/4 after all these constants. Carrier and interval intersections then give

$$
\sum_{q\not\sim p}u_qe^{A'(q)+\eta'\ell(q)}
 \leq C_*'\tau|A_p|+C_*'\tau^2H_p
 \leq A'(p)/4\;.
$$

The same pinned-tree proof as eq:marginal-pinned-bound applies to these positive majorants. If U(Gamma) is the absolute Ursell coefficient (including tuple factorial) times their product, sum the pinned estimate over source-web occurrences whose interval meets one of the L fine traversals of segment j. A cluster with j in J_Gamma has at least one such occurrence; overcounting is harmless. The interval-root bound supplies

$$
\sum_{\Gamma:j\in J_\Gamma}U(\Gamma)e^{\eta'\ell(\Gamma)}\leq C\tau^2\;.
$$

It also bounds the endpoint weights |Phi|. The product rule for a cluster sums the single differentiated component/edge occurrence; the sum of its squared extents is at most ell(Gamma)^2. This proves the differentiated bound used in Section 3 with eta_1 replaced by the common eta'. Half of eta' pays that polynomial and the rest pays the spatial boundary tail. For the short lifted periodisation comparison use the same uniform positive majorants on the infinite free lattice. Their bounds depend only on the common decay and spectral constants, so restricting to short clusters only reduces the sums. This proves the corresponding summability required in Section 4; no global interpolated gas is needed.

## 4. Periodic comparison with the bulk square

Let F_{C,infinity}(n) be the convergent infinite-lattice square connected sum identified in eq:corner-fixed-square-limit. Use the lifted square with fine side nL. The condition K_mu>=3(n+2) ensures that it and a distinct periodic image are separated by at least a fixed fraction of N_min in every direction where they can approach. The cyclic ordering and fixed base of its traversal list are retained.

A rooted cluster with C_net ell(Gamma)+R_0<N_min/4 has a unique lift through its root. Its support/interval network cannot wind or connect the square to a different periodic image, and its source labels match those on the chosen lifted square. The difference between the finite- and infinite-volume Gaussian entries on that carrier is controlled by periodisation:

$$
\|C_T(b,c)-C_\infty(\widetilde b,\widetilde c)\|
 \leq C e^{-\mu N_{\min}/2}e^{-\mu d(\widetilde b,\widetilde c)}\;.
$$

This is the same covariance comparison used before eq:regional-torus-bound, on the chosen short lift. Both principal marginals have their common spectral bounds. Apply the same density/edge derivative rule with this covariance difference; a factor polynomial in ell is paid by the reserved extent decay. The small-cluster difference is at most C tau^2 exp(-c iota_T) per root. The complementary clusters, including winding ones, have extent at least a fixed multiple of iota_T and the same bound follows from their extent tails in each gas. The finitely short-period regime iota_T=0 is covered by the uniform rooted bounds. Therefore

$$
|F_{C,T}-F_{C,\infty}(n)|\leq C\tau^2(4n)e^{-c\iota_T}\;.
$$

This is a quantitative upgrade of the fixed-square limit argument, using the already differentiated covariance estimate. It uses no infinite-volume partition function.

## 5. Perimeter/corner identification and error retained in the caller

The manuscript's corner-square extraction gives

$$
F_{C,\infty}(n)=n\sum_{v\in\mathscr V_\square}\kappa_v
 +\sum_{(v,w)\in\mathscr C_\square}\zeta_{v,w}+E_n,\qquad
|E_n|\leq C\tau^2(n+1)e^{-cn}\;.
$$

Its proof retains clusters crossing each bend, with the straight endpoint deficits included in zeta_{v,w}; no equality of the four oriented corner constants is required. By the existing definitions the first sum is -delta m^sigma P(C_n) and the second is 4 log z_c^sigma(g_0,pi/2). Set

$$
E^\circ_\xi=(F_{D,C,T}-F_{C,T})
 +(F_{C,T}-F_{C,\infty}(n))+E_n\;.
$$

Sections 3 and 4 and the square extraction prove the claimed error bound. This construction mirrors RG1 (4.35)--(4.37): changes of the regional kernel and summation range are retained as errors before identifying the translation-invariant coefficients. CRE (1.26)--(1.30) keeps the exterior operation and its boundary terms; the same operation remains here.

In the first-step physical identity the substitution is exactly

$$
\mathbb E_\varepsilon[W_\chi(C_n)]
 =\kappa_{C_n}\mathbb E_h\left[
    \mathbf1_{A_{\rm cov}}e^{E^\circ_\xi}W_\chi(C_n;U_1)\right]
   +E_{\rm def}+E_{\rm bdry}\;.
$$

E_h uses the original outer operation, weight exp(c_xi)I_{xi;1} and physical Z_0. The regional logarithm is a function of the finite geometry at fixed torus and reference parameters, hence measurable in the history labels. It is independent of the remaining field values at fixed labels. Its bound has at most 4n boundary terms, so at fixed cutoff the extra factor is bounded and integrable; no new denominator estimate or cancellation is invoked. The reconstructed fine loop is retained. This does not claim comparison with the bare coarse loop or all-scale convergence.
For the physical identity in Section 5 the errors are the existing Stage 1--4 operands, explicitly

$$
E_{\rm def}=\mathbb E_h\left[\mathbf1_{A_{\rm cov}}
 \sum_{\varnothing\ne\mathfrak B\ {
m compatible}}
 S^{\circ,[\mathfrak B]}_{\xi,C_n}R_\xi(\mathfrak B)\right],\qquad
E_{\rm bdry}=\mathbb E_h\left[
 \mathbf1_{A_{\rm cov}}\mathcal B_\xi[f_\xi]
 +\mathbf1_{A_{\rm cov}^c}F_\xi(1)\right]\;.
$$

The restricted reference sum and signed defects are those of Stage 1 eq:part1-scalar-extraction. This keeps the entire uncovered contribution as well as the exterior-response covariance term.
## 6. Explicit covariance directions, units and domains

For the component derivative let k=|A|, let F be its forest, and let d_b be the forest degree at b. Choose one common positive entry majorant B_{bc}=A_0 exp(-mu_0 d(b,c)) for every interpolated covariance block, with mu_0 below the common decay exponent. The differentiated covariance obeys ||D_A||<=C k h_A and ||D(b,c)||<=C h_A B_{bc}, after enlarging A_0 and lowering mu_0, where h_A=exp(-a d_T(A,D^c)) for the regional comparison. In the periodic comparison h_A=exp(-mu_0 N_min/2) on a short lifted carrier, with the reduced mu_0 chosen in the calculation below. No covariance entry is divided by.

For each forest direction choose

$$
r_e=\frac{\lambda}{32d_bd_cB_{bc}},\qquad e=\{b,c\}\;.
$$

The row sum of all edge perturbations is at most lambda/32, since sum_{c:e in F}1/(d_b d_c)<=1. For the derivative on the covariance centre, add a separate variable with direction D_A circ w^F and radius

$$
r_0=\frac{\lambda}{32C k h_A}\;.
$$

A zero direction gives zero derivative. The Schur mask is positive with unit diagonal, so its operator norm action is contractive; this perturbation also has norm at most lambda/32. The total perturbation is at most lambda/16, and the normalised density (determinant included) has the same product Gaussian majorant as eq:marginal-density-majorant with enlarged fixed constants. The extra Cauchy inverse radius costs C k h_A. For the derivative of an edge direction e, replace that edge's radius by

$$
r_e^{D}=\frac{\lambda}{32d_bd_c C h_A B_{bc}}\;.
$$

The same row-sum bound holds, with the common C absorbed into the radius. Its inverse-radius product is at most C h_A times the original forest product majorant. Summing over the |F| possible edge replacements and the one covariance-centre derivative gives C(k+|F|)h_A times the common component majorant; the weaker C(k+|F|+1)^2h_A bound used in Section 3 follows. The products of inverse radii still contain only the degree weights d_bd_c and exponential edge factors already paid in Section 3.1. The fixed radius reductions only change K_2, chosen before the coupling. This explicitly covers the torus calculation and any vanishing covariance block.

All these densities and directions commute with simultaneous colour conjugation. A component with one selected source mark remains a scalar after integration inside the closed contraction; its scalar is the closed one-mark character difference. Its pointwise first-order term vanishes because d chi_id=0. Differentiating the Gaussian density leaves that source untouched and hence retains the g_0^2 r^2 gain. This verifies the tau^2 source gain for both kinds of density derivative, including a component lying across a corner.

For the free covariance (rather than the reconstructed fine covariance), the Neumann argument in the manuscript gives

$$
\|C_\infty(e,f)\|\leq\gamma_L^{-1}
 e^{-\mu_L\|\ell(e)-\ell(f)\|_\infty}\;.
$$

If d_f is the fine-bond metric, d_f(e,f)<=L||ell(e)-ell(f)||_infinity+2L. Hence, with nu=mu_L/L and A_f=gamma_L^{-1}exp(2mu_L),

$$
\|C_\infty(e,f)\|\leq A_f e^{-\nu d_f(e,f)}\;.
$$

The absolutely convergent periodisation of this free inverse solves H_T C=1, since H_T is the periodisation of the finite-range H_infinity. Invertibility therefore gives C_T(e,f)=sum_z C_infinity(e,f+Nz). For fixed lifts and d=d_f(e,f), the z-th image distance is at least N_min||z||_infinity-d-1 (the fixed orientation offset is absorbed). Summing the shells yields

$$
\|C_T(e,f)-C_\infty(e,f)\|
 \leq C e^{-\nu(N_{\min}-d)}
 \leq C e^{-\nu N_{\min}/2}e^{-\nu d}\;,
$$

where the last inequality uses d<=N_min/4. The shell constant is uniform for N_min>=1 because sum_{z nonzero}exp(-nu(||z||_infinity-1)) is finite. Lower nu once to be compatible with the common component decay exponent. This is the free-covariance fine-unit estimate used in Section 4, not an inference from an estimate on the reconstructed covariance alone.

For the row identification, impose both existing thresholds explicitly. Let C_C=C_mathsfC and vartheta_* be the constants of Stage 2 Lemma c2-uniform-chart(i), and let a_L be the manuscript flat max-norm chart radius. Require

$$
g_0 C_C(2+4r)<\vartheta_*/2,\qquad
g_0(2+4r)<a_L\;.
$$

Their common free-variable domain is the convex intersection of these row phase balls and max-norm polydiscs, containing the closed integration box with a margin. At zero the two implicit solutions have the same germ; the identity theorem identifies their analytic continuations on this common connected domain. Both requirements are satisfied by reducing the coupling under the existing g_0(1+r)^3 smallness condition, with constants fixed first. The source-scaling variables satisfy |t_a|<=2 in all three protected-label gases. The resulting factor 2^{|S|} is absorbed in K_2 before the thresholds in Section 3.1 are chosen. Thus the regional source logarithm and its nonvanishing hold on the same source polydisc as in the manuscript.
## 7. Restricted reassembly and periodic convolution details

The Stage 2 constant C_C=C_mathsfC is chosen in Lemma c2-uniform-chart(i) and satisfies, at the reference background,

$$
\|\mathsf C_{\rm id}B|_{\mathcal E_c}\|_h
 \leq C_C\max_{b\in\mathcal E_c\cap E_*}|B_b|_\sigma\;.
$$

It depends only on L and the group; the stated lower choice includes sqrt(4L^3(L-1)). This is the bound used with the row-phase radius vartheta_* in Section 6. Stage 2 threshold item 3 imposes that inclusion for the enlarged polydisc, and Lemma c2-reference applies the same chart conclusions to identity background. These are existing input-domain statements, not assumptions about the square comparison.

For the restricted gas, zero extension i_D commutes with simultaneous colour conjugation. Hence each v(i_DB), every cutoff, and the closed source difference remains invariant. Keep the original labels when replacing their free supports by intersections with D. The finite forest formula on the carrier D partitions a selected set of labels and forest edges into connected components using the restricted support graph Q_J. Every support edge and forest edge belongs to exactly one component. Join source components by intersection of their manuscript cyclic intervals; each connected union is one web. Conversely a compatible collection of these components and webs has disjoint carriers and disjoint web intervals, so taking its labelled union recovers the same components and webs. No original label is lost or duplicated, including labels with identical restricted supports. Empty restricted scalar primitives vanish; empty restricted source differences vanish; empty unused cutoff labels are omitted. This proves the finite reassembly bijection for the regional integral.

The covariance mask, its forest directions, and its density split by the component partition. Integration over disjoint components is thus a tensor product. Constant conjugation and irreducibility turn each integrated closed slot into its scalar Schur factor, inside the parent closed contraction. If an interval crosses the chosen contour base, cyclicity of the trace moves that base between two disjoint web intervals before the factorisation. The resulting scalar is unchanged. This proves the regional analogues of both gases in eq:marginal-exact-gases. The positive-majorant KP bound of Section 3.1 then identifies the convergent source logarithm on |t_a|<=2.

For completeness the boundary resolvent estimate uses only periodic metric inequalities. If u in D and w in D^c contribute to H_{D,D^c}, then d_T(u,w)<=R_H. For s=d_T(b,u)+d_T(w,c), the three triangle inequalities give

$$
d_T(b,D^c)+d_T(c,D^c)+d_T(b,c)\leq2s+2R_H\;.
$$

The two inverse entries contribute C exp(-mu s). Half of this exponent pays the displayed distances with a=mu/4. The remaining sum is uniformly bounded:

$$
\sum_{u,w:d_T(u,w)\leq R_H}
 e^{-(\mu/2)[d_T(b,u)+d_T(w,c)]}
 \leq N_H\sup_b\sum_u e^{-(\mu/2)d_T(b,u)}\leq C_{\mu,R_H}\;.
$$

Here N_H is the fixed maximum number of free bonds within R_H of one bond. For the last inequality assign each periodic displacement its minimum absolute-coordinate representative. Their shell counts are bounded by the infinite-lattice shell counts (times the fixed bond-direction multiplicity), so the exponential shell sum is uniform in the periods. Restricting u,w to the boundary-crossing pair set only reduces the sum. Multiplying the constants proves the covariance-difference estimate for every D, including a wrapping or disconnected D, without a boundary-area factor.
## 8. Caller scope and separate integrability

Stage 5 (19 October 2026; `V2_STAGE5_COLLAR_RETREAT_DRAFT_2026_10_19.md` §7, reviewed `collar-item-7-20261019-r1`) carries out the identification of Section 2 at the retreated carrier D(Λ) ⊆ I of its labelled terms instead of at D = I: Lemma 7.1 there (S°_Λ = S°_{D(Λ),C,T} on the labelled coverage event A_cov^{fin}, factorwise: precision i*_{D(Λ),T} H_T i_{D(Λ),T}, cutoff, primitives at the sum level, Wilson factor), Corollary 7.2 (S°_Λ = κ_C e^{E°_Λ} with the manuscript's error bound at D(Λ), the crude form Cτ²(9n+1)) and Lemma 7.3 (the label average of the boundary sum Σ_j e^{−c d_j(Λ)} paid by one-point witness probabilities). The caller of this stage's scalar at D = I is the unlabelled branch; stage 5's caller is the labelled term. The ingredients used by both are the same (eq:regional-weight's primitives, the regional stencil identity, the collar); stage 5 lists in its 7.3 what it takes from the manuscript at stated status.

The physical substitution carries all Section1 torus and contour hypotheses and the small-coupling thresholds in Sections3.1 and6. The scalar reference satisfies |S^circ|<=1 by its positive normalised reference integral. Also |F_xi(s)|<=1 for the positive conditional probability kernel, and |f_xi(0)|<=1. Hence |B_xi[f_xi]|=|F_xi(1)-F_xi(0)|<=2 and the summed signed defect |F_xi(0)-S^circ f_xi(0)|<=2. Each term in the physical substitution is therefore integrable against the unchanged probability history weight. After scalar substitution the first integrand is still exactly S^circ f_xi(0); no independent bound on exp(E^circ) is needed to justify this identity.

## 9. TeX form of Sections 1, 2, 5 and 8

The block below is the TeX form of this draft, spliced on 19 October 2026 into WILSON_FIRST_RG_STEP_V3.tex as the last appendix (`app:regional-scalar`, immediately before the bibliography): Section 2 as `lem:c4c-2-1` (the Stage 1 scalar S^circ_{xi,C_n} equals the regional square scalar eq:regional-square-scalar at D = I), Sections 1 and 5 as `prop:c4c-5-1` (S^circ = kappa_C e^{E^circ}, error eq:regional-square-error at D = I) and `cor:c4c-5-2` (the physical identity with E_def of app:signed-defects and E_bdry of app:exterior-chessboard), Section 8 as `rem:c4c-8-1`. Sections 3, 3.1, 4, 6 and 7 are not reproduced: their content is already the proof of prop:regional-square-extraction in V3 (weighted regional sums, boundary resolvent estimate, covariance directions and radii, periodic convolution, restricted reassembly), and the appendix cites that proof. The translation has not been reviewed.

```tex
\section{The Regional Scalar of the Covered Branch}\label{app:regional-scalar}
This appendix identifies the scalar $S^\circ_{\xi,C}$ of the branch identity \eqref{eq:c-one-step-branch-identity}, defined in Section~\ref{sec:joint-extraction} as the reference-gas sum \eqref{eq:part1-reference-gas}, with the regional square scalar \eqref{eq:regional-square-scalar} at the carrier $I$, and thereby with the perimeter/corner coefficient $\kappa_C$ of \eqref{eq:extracted-loop-scalar} up to the error of Proposition~\ref{prop:regional-square-extraction}. It is the statement used in Section~\ref{sec:remaining-physical-comparison} at \eqref{eq:retained-leading-source}; its labelled counterpart at the retreated carrier $D(\Lambda)$ is Lemma~\ref{lem:c5-7-1} with Corollary~\ref{cor:c5-7-2}. The quantitative comparison of the regional square scalar with the bulk square is the proof of Proposition~\ref{prop:regional-square-extraction}, in particular \eqref{eq:regional-square-boundary-comparison} and \eqref{eq:regional-square-periodic-comparison}; nothing is added to it here.

\subsection{Conventions}\label{sec:c4c-1}
Fix one of the two cutoff prescriptions $\sigma$, the bare coupling $g_0$, the irreducible normalised character $\chi$, the averaging and mean prescription of RG1 and the designated-bond convention, as in the rest of the paper, with the standing conditions \eqref{eq:c-standing-conditions} and the collar conditions \eqref{eq:regional-collar-sizes}. The fine periods are $N_\mu=LK_\mu$, and $C=C_n$ is a coarse translate of the counterclockwise square with vertices $0$, $nLe_1$, $nL(e_1+e_2)$, $nLe_2$, with $n$ coarse segments of length $L$ on each side and $K_\mu\geq3(n+2)$ for every coarse period; its physical perimeter is $P(C_n)=4nL\varepsilon$. Let $A_{\mathrm{cov}}$ be the set of covered branches of Lemma~\ref{lem:covered} and let $\xi\in A_{\mathrm{cov}}$. The young carrier is $D=I=D_+(\Lambda_1)$, the set of free bonds with an endpoint in $\Lambda_1$, and $D^c$ is its complement in the torus free carrier $E_{*,T}$; distances are those of the periodic fine-bond metric \eqref{eq:regional-distance}. For a coarse segment $j$ of the cyclic index set $J_C=\{0,\ldots,4n-1\}$ let $K_j$ be the union of the fixed free-input stencils of its fine traversals, and with the fixed range $R_0$ of \eqref{eq:regional-square-distances} put
\begin{equation}\label{eq:c4c-1-1}
    d_j=\max\bigl(0,d_T(K_j,I^c)-R_0\bigr),\qquad\iota_T=\max\bigl(0,N_{\min}/4-R_0\bigr),\qquad N_{\min}=\min_\mu N_\mu\;,
\end{equation}
the distance to the empty set being infinite with $e^{-\infty}=0$; there is no distance to a side endpoint in $d_j$. The constants below depend on the character, the group, $L$ and the forest parameters only, not on $n$, the compatible periods or the shape of $I$; $g_0$ is chosen after them, below the common flat and regional thresholds. $\tau$ is the marked-forest parameter of \eqref{eq:marginal-fixed-forest-bound}; enlarging a fixed majorant constant multiplies $\tau$ by a fixed factor, absorbed in the constants and the coupling threshold.

\subsection{Identification with the regional square integral}\label{sec:c4c-2}
\begin{lemma}[the Stage 1 scalar at the carrier $I$]\label{lem:c4c-2-1}
On $A_{\mathrm{cov}}$, under the conventions of Section~\ref{sec:c4c-1} and the thresholds displayed in the proof of Proposition~\ref{prop:regional-square-extraction} (also \eqref{eq:c5-7-T}(ii)),
\begin{equation}\label{eq:c4c-2-1}
    S^\circ_{\xi,C_n}=S^\circ_{I,C_n,T}=\frac{\displaystyle\int\Theta^\sigma_I(B)e^{P_{I,T}(B)}\chi\bigl(\Hol_{U_{g_0,T}(i_{I,T}B)}C_n\bigr)\,\dd\mu_{C_{I,T}}(B)}{\displaystyle\int\Theta^\sigma_I(B)e^{P_{I,T}(B)}\,\dd\mu_{C_{I,T}}(B)}\;,
\end{equation}
the right side being \eqref{eq:regional-square-scalar} at $D=I$, with every original primitive label retained, including the labels crossing the boundary of $I$, and with the exterior link value the identity.
\end{lemma}

\begin{proof}
By \eqref{eq:part1-reference-gas}, $S^\circ_{\xi,C_n}=\int f^\circ_\xi K^\circ_{\xi;0}\,\dd a/I^\circ_{\xi;0}$, the normalised expectation of the full reference Wilson loop under the centred kernel at the identity background, whose precision is $H^\circ_\xi=\iota_I^*\mathsf H^{\Omega_1}_{\id}\iota_I$, whose potentials are the near primitives evaluated at zero retained input and whose cutoff is the bond cutoff on $I$. Both sides of \eqref{eq:c4c-2-1} are ratios of two integrals over $\mathfrak g^I$, so it suffices to identify the factors of the integrands. Precision: the regional stencil identity and the collar put every precision and primitive stencil touching $I$ inside $\Omega_1$, where the action at the identity is the flat quadratic form, so by Lemma~\ref{lem:c2-reference} the entries of $H^\circ_\xi$ are the flat entries $f_{bb'}(0)$ and $H^\circ_\xi=i_{I,T}^*H_Ti_{I,T}$, the diagonal contributions of the plaquettes crossing the boundary of $I$ included; the Gaussian normaliser of $\mu_{C_{I,T}}$ is common to numerator and denominator and cancels within the ratio, not against the outer physical weight. Reconstruction: the row solutions of Section~\ref{sec:regular-hessian-stencils} at the identity background and those of Section~\ref{sec:regional-identification} agree as analytic germs at zero by their defining equation and uniqueness; the Hilbert-ball domain of Lemma~\ref{lem:charts} (reference version) and the maximum-norm domain of the flat expansion have a convex common phase domain containing the closed cutoff box at the stated thresholds, and analytic continuation on that domain identifies the two solutions throughout the box. Primitives: Section~\ref{sec:source-phase-primitives} groups the gauge primitives by their centre $y$ while \eqref{eq:regional-periodic-weight} indexes them by the pairs $(y,x)$; the sums coincide, the degree-two Taylor residual being linear in the local term, and every primitive whose free support misses $I$ vanishes at $i_{I,T}B$ while every primitive meeting $I$ is retained on both sides. Cutoff: at zero exterior free field the conditional cutoff is $\Theta^\sigma_I$ at the threshold $r=\delta_0/g_0$ in the norm $|\cdot|_\sigma$, as in Section~\ref{sec:regional-identification}. Wilson factor: on a covered branch every contour row has its free-input set in $I$, so with $a$ retained instead of set to zero the argument of Lemma~\ref{lem:covered} gives that each contour link of $f^\circ_\xi(a)$ is its reconstruction from $a$ alone, that is, $U_{g_0,T}(i_{I,T}B)$ at $B=a$; the boundary map is the identity by the reference-data convention $\Psi^\circ=\id$. Numerator and denominator agree factor by factor, so the ratios agree. The equality is one of integral ratios: the reference group gas of Section~\ref{sec:joint-extraction} and the protected-label gas of the proof of Proposition~\ref{prop:regional-square-extraction} (with the shortest-interval rule for its webs and no group-promotion rule) need not agree term by term, and no identification of a separately chosen logarithm of the group gas with the connected source logarithm is used.
\end{proof}

\subsection{The scalar of the branch identity}\label{sec:c4c-5}
\begin{proposition}[the regional scalar of the covered branch]\label{prop:c4c-5-1}
Under the conventions of Section~\ref{sec:c4c-1} and the hypotheses of Proposition~\ref{prop:regional-square-extraction}, on $A_{\mathrm{cov}}$,
\begin{gather}
    S^\circ_{\xi,C_n}=e^{-\delta m^\sigma(g_0,\varepsilon)P(C_n)}\bigl(z^\sigma_{\mathrm c}(g_0,\pi/2)\bigr)^4e^{E^\circ_\xi}=\kappa_{C_n}e^{E^\circ_\xi}\;,\label{eq:c4c-5-1}\\
    |E^\circ_\xi|\leq C\tau^2\Bigl[\sum_{j\in J_C}e^{-cd_j}+4ne^{-c\iota_T}+(n+1)e^{-cn}\Bigr]\;,\notag
\end{gather}
with the coefficients of \eqref{eq:marginal-square-mass} and \eqref{eq:corner-square-factor} and
\begin{equation}\label{eq:c4c-5-2}
    E^\circ_\xi=E^\circ_{I,C_n,T}=(F_{I,C,T}-F_{C,T})+(F_{C,T}-F_{C,\infty}(n))+E^\sigma_n\;,
\end{equation}
the error of Proposition~\ref{prop:regional-square-extraction} at $D=I$. The scalar and its nonzero logarithm are those of the regional conditional reference integral; no physical history weight or large-field indicator is evaluated at flat fields, and the bound does not assume the loop to be far from the integration boundary: $d_j=0$ retains a boundary contribution of size $C\tau^2$.
\end{proposition}

\begin{proof}
Lemma~\ref{lem:c4c-2-1} and Proposition~\ref{prop:regional-square-extraction} at $D=I$, which is covered on $A_{\mathrm{cov}}$ and satisfies $I\subseteq D_+$ with the collar; the three differences of \eqref{eq:c4c-5-2} are \eqref{eq:regional-square-boundary-comparison}, \eqref{eq:regional-square-periodic-comparison} and the corner extraction \eqref{eq:corner-square-extraction-bound}, the first two retaining the changes of kernel and of summation range as errors before the translation-invariant coefficients are identified, as in RG1 (4.35)--(4.37), while the exterior operation and its boundary terms are kept as in CRE (1.26)--(1.30).
\end{proof}

\begin{corollary}[the physical identity with the scalar substituted]\label{cor:c4c-5-2}
Under the hypotheses of Proposition~\ref{prop:c4c-5-1}, with $E_{\mathrm{def}}$ of \eqref{eq:c4-1-1} and $E_{\mathrm{bdry}}$ of \eqref{eq:c3-6-2},
\begin{equation}\label{eq:c4c-5-3}
    \mathbb E_\varepsilon[W_\chi(C_n)]=\kappa_{C_n}\,\mathbb E_{\mathrm h}\bigl[\mathbf 1_{A_{\mathrm{cov}}}e^{E^\circ_\xi}W_\chi(C_n;U_1)\bigr]+E_{\mathrm{def}}+E_{\mathrm{bdry}}\;,
\end{equation}
where $\mathbb E_{\mathrm h}$ uses the original outer operation, the weight $\mathsf w_\xi=e^{c_\xi}I_{\xi;1}$ and the physical $\mathcal Z_0$. Every term is integrable against the normalised history weight, and the reconstructed fine loop $W_\chi(C_n;U_1)$ is retained.
\end{corollary}

\begin{proof}
By \eqref{eq:c4-8-1}, $\mathbb E_\varepsilon[W_\chi(C_n)]=\mathbb E_{\mathrm h}[\mathbf 1_{A_{\mathrm{cov}}}S^\circ_{\xi,C_n}f_\xi(0)]+E_{\mathrm{def}}+E_{\mathrm{bdry}}$, with $f_\xi(0)=W_\chi(C_n;U_1)$ on $A_{\mathrm{cov}}$ (Lemma~\ref{lem:covered}); substitute \eqref{eq:c4c-5-1}. $E^\circ_\xi$ is a function of the finite geometry at fixed torus and reference parameters, hence of the history labels through $I$ alone, and is independent of the field values at fixed labels, so the first term is measurable; its bound has at most $4n$ boundary terms, so at fixed cutoff the factor $e^{E^\circ_\xi}$ is bounded and the term integrable. For the other terms, $|S^\circ_{\xi,C_n}|\leq1$ because it is the normalised integral of a character of modulus at most one against the positive reference kernel $K^\circ_{\xi;0}$; $|F_\xi(s)|\leq1$ for the positive conditional probability kernel and $|f_\xi(0)|\leq1$; hence $|\mathcal B_\xi[f_\xi]|=|F_\xi(1)-F_\xi(0)|\leq2$ and the summed signed defect $|F_\xi(0)-S^\circ_{\xi,C_n}f_\xi(0)|\leq2$, and both are integrable against the unchanged probability history weight. After the substitution the first integrand is still exactly $S^\circ_{\xi,C_n}f_\xi(0)$, so no independent bound on $e^{E^\circ_\xi}$ is needed to justify the identity. No new denominator estimate or cancellation is invoked.
\end{proof}

\begin{remark}[scope]\label{rem:c4c-8-1}
The caller of \eqref{eq:c4c-5-1} at $D=I$ is the unlabelled branch identity, at \eqref{eq:retained-leading-source} and in Appendix~\ref{app:signed-defects}, where $S^\circ_{\xi,C}$ is carried inside the expectation; Section~\ref{sec:one-step-insertion} carries out the same identification at the retreated carrier $D(\Lambda)\subseteq I$ of its labelled terms (Lemma~\ref{lem:c5-7-1}: factorwise agreement of precision, cutoff, primitives and Wilson factor; Corollary~\ref{cor:c5-7-2}: $S^\circ_\Lambda=\kappa_Ce^{E^\circ_\Lambda}$ with the error at $D(\Lambda)$; Lemma~\ref{lem:c5-7-3}: the label average of the boundary sum paid by one-point witness probabilities). The ingredients are the same in both cases: the primitives of \eqref{eq:regional-weight}, the regional stencil identity and the collar. The identity \eqref{eq:c4c-5-3} compares the physical expectation with the reconstructed fine loop at the background $U_1$; a comparison with the bare coarse loop, or convergence over all scales, is not asserted.
\end{remark}
```

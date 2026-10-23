# Stage 4: signed integrated Wilson defects
18 October 2026. This draft addresses E_def from the Stage 1 joint extraction, retaining the original physical history law. It does not replace E_def by a rooted probe norm or claim Delta_1 closure. Status (19 October 2026): Sections 1-12 are in WILSON_FIRST_RG_STEP_V3.tex in TeX form as the last appendix `app:signed-defects` (final estimate `prop:c4-12-3`; the TeX block is §13 below), and the stage 5 section's `\draftref{stage 4, ...}` markers now point to its labels. Review of the translation (19 October 2026, one subsection per isolated referee packet, `verification/isolated_reviewer/reviews/tr-c4-*-20261019-r1/review.txt`): sec:c4-1 to sec:c4-4 reviewed and the TeX repaired from the reports (V3 SHA256 abf0d60cc65a5836, 23:36); sec:c4-6 reviewed and repaired (V3 SHA256 dbdb0dbccdc595ba, 20 October 00:13); sec:c4-7 reviewed and repaired (V3 SHA256 690a93569dccac24, 20 October 00:43); sec:c4-8 reviewed and repaired (V3 SHA256 00f1d48362ebc809, 20 October 01:10; the two-species recursion of lem:c4-8-2(a) is written out instead of citing lem:c4-6-2, which assumes it; the root sum is the displayed animal bound with λ_* ≥ 2C_g log 128; lem:c4-8-3(a) holds for every class before promotion, hypothesis CρLM ≤ η/8; lem:covered states U_ξ(0) = U_1 on the contour); sec:c4-9 to sec:c4-12 reviewed (wave 5B, launched 20 October 02:07 against V3 SHA256 c73335d187e27656; reports tr-c4-9 335 lines, tr-c4-10 319, tr-c4-11 316, tr-c4-12 239) and repaired (V3 SHA256 87cccdb3b28c872d, 20 October 02:43, 204 pages, no undefined references; |S°_{ξ,C}| ≤ 1 is justified from eq:part1-reference-gas, lem:c4-9-2 is restated with the cluster logarithm 𝓛 and the hypotheses of lem:c4-6-3, the Gaussian bounds of sec:c4-10-3 are cited to app:fixed-kernel-payment, the covariance of sec:c4-11-2 is derived from the intertwinings of lem:hessian-gauge-locality, the adjacency convention of sec:c4-12-4 is an allowance in the constant C of lem:c4-6-2, and prop:c4-12-3 names its thresholds). Every section of this draft has now been reviewed once. 20 October 09:16 (V3 SHA256 5dd43b84ae77377c, 208 pages, no undefined references): sec:c4-6-2 gains lem:c4-6-env [footprints and envelopes] (A_F, A_E, the connected envelope E(W), the footprint-to-contour decay and the incompatibility contact), replacing the attempt-file sections 19.1/19.3 cited from Section 9; the remark in sec:c4-12 on the archived straight-side estimate is reduced to the sentence naming the derivative bounds of sec:c4-7 and sec:c4-10; no archived note is cited any more (lem:c4-6-env referee-reviewed 20 October, tr-c4-6-env-20261019-r1: no blocking errors; its ranges, constants and connectivity proof were rewritten in response at 10:40, with the range constant R_e = ⌈2 max(R_h, L)/(LM)⌉ in LM-cubes, A_F = A_E = 9(2R_e+1)⁴, the cubes π₁(ℋ(W)) and the neighbourhoods 𝔑_R; final V3 SHA256 d3d017eb00120d92 at 10:46; the tr-c4-8 B16 gap, the L_f ≤ C|ℋ(W)| link in sec:c4-8-4, is closed by a cross-reference to sec:c4-9-1 at 11:15, V3 SHA256 8845483f56bb7c91; r2 referee tr-c4-6-env-20261019-r2 launched 11:16:25). The TeX in V3 is authoritative where it differs from the TeX block in §13, which is not re-mirrored.

## 1. Operand and retained normalisation

Use exactly the Stage 1 groups W, compatible families mathfrak B, closed pairings A_xi(S), scalar references a_W, restricted reference sums S^{circ,[mathfrak B]}_{xi,C} and joint defects R_xi(mathfrak B). Their authoritative definitions are def:groups, eq:part1-closed-family-pairing, eq:part1-reference-group, eq:part1-joint-defect and prop:joint-extraction in V2_STAGE1_CONSTRUCTION_DRAFT_2026_10_17.md. Every source remains a gauge-invariant closed contraction.

Put

$$
\mathscr R_\xi=\sum_{\substack{\mathfrak B\ne\varnothing\\\mathfrak B\ {\rm compatible}}}
 S^{\circ,[\mathfrak B]}_{\xi,C}R_\xi(\mathfrak B),\qquad
E_{\rm def}=\frac{1}{\mathcal Z_0}\int
 \mathcal O[\mathsf w_\xi\mathbf1_{A_{\rm cov}}\mathscr R_\xi](V)\,dV\;.
$$

The weight is mathsf w_xi=exp(c_xi)I_{xi;1}, the same outer operation O contains the original cutoffs, zeta including its boundary-fluctuation dependence, gauge/Haar factors, Jacobians, vacuum prefactor and deferred integrations. Z_0=int O[mathsf w_xi]dV. E_h and P_h are the normalised expectation and probability for this positive history weight. At fixed finite volume the signed sum converges absolutely by the already proved joint-extraction identity. No new uniform absolute summability estimate is inferred from that fact.

Stage 5 (19 October 2026; `V2_STAGE5_COLLAR_RETREAT_DRAFT_2026_10_19.md`) changes the history law this operand is defined with: on the branches where a second collar test fails, Λ₁ and the carrier I are retreated to a labelled carrier D(Λ), and the branch identity is written for each labelled term with the labelled weight w^lab_ξ (its §6, Lemma 6.1). E_def as defined here uses the original law; its labelled-term reading — the same signed sum with S^{circ,[mathfrak B]}_{xi,C} and R_xi(mathfrak B) formed at D(Λ) and the weight 1_lab e^{c^Λ_ξ} I^Λ_1 — is recorded as open in stage 5's 6.3(2) and is not checked anywhere. Sections 2–20 below are unchanged and refer to the original law.

## 2. Paying histories near the bad region using the full signed sum

Let B_xi=Lambda_1^c be the filled bad region. E(B_xi) consists of positive fine bonds with at least one endpoint in B_xi. Let Gamma_C be Stage 3's deterministic set of contour bonds and free-input templates, with |Gamma_C|<=C_L n_C, where n_C is the number of contour traversals. Distances use the periodic fine-bond metric of Stage 3. For an integer b>=0 define

$$
\mathsf N_b=\{\xi\, | \,
 \operatorname{dist}(\Gamma_C,E(B_\xi))\leq b\}\;,
$$

with distance to the empty set infinite. This is a measurable history event. Its use does not change the covered event or the original law. Write E_def^near=E_h[1_cov 1_{N_b} mathscr R_xi] and E_def^far=E_h[1_cov 1_{N_b complement} mathscr R_xi].

The frozen joint-extraction identity gives mathscr R_xi=F_xi(0)-S^circ_{xi,C} f_xi(0). Both F_xi(0) and S^circ_{xi,C} are normalised integrals of a character of modulus at most one against their real positive conditional kernels. Also |f_xi(0)|<=1. Consequently |mathscr R_xi|<=2. This is used only after summing the joint defects; it is not a separate bound on any R_xi(mathfrak B), any group, or any restricted reference factor.

Stage 3 supplies the one-point estimate for every positive fine bond z,

$$
\mathbb P_h(z\in E(B_\xi))
 =\frac{1}{\mathcal Z_0}\int
  \mathcal O[\mathsf w_\xi\mathbf1_{\{z\in E(B_\xi)\}}](V)\,dV
 \leq e^{-c_*p_*^2},\qquad
p_*=\min(p_0(g_0),p_0(g_1))\;.
$$

There are at most 4(2b+3)^4 positive fine-bond labels within distance b of a fixed fine bond (an overcount on short periods). A union bound gives

$$
\mathbb P_h(\mathsf N_b)
 \leq 4C_L n_C(2b+3)^4e^{-c_*p_*^2}\;.
$$

Use positivity only after the signed sum has been formed. This proves

$$
|E_{\rm def}^{\rm near}|
 =\left|\frac{1}{\mathcal Z_0}\int
  \mathcal O[\mathsf w_\xi\mathbf1_{A_{\rm cov}}\mathbf1_{\mathsf N_b}
                \mathscr R_\xi](V)\,dV\right|
 \leq 8C_L n_C(2b+3)^4e^{-c_*p_*^2}\;.
$$

Choose b=floor(LMR_1/16). For small g_0 this exceeds all fixed source stencils, and log(2b+3)=O(log log(g_0^{-2})). The same source parameter relations used in Stage 3 absorb the polynomial without absorbing n_C. After reducing g_0 at fixed source constants,

$$
|E_{\rm def}^{\rm near}|
 \leq C_L' n_Ce^{-(c_*/2)p_*^2}\;.
$$

The constants are uniform in the compatible even-period tori and all original histories, with fixed source parameters. No physical denominator lower bound is substituted, no conditional scalar is cancelled across histories, and no pointwise smallness of Wilson-loop random variables is claimed.

## 3. Interior calculation being attempted

The remaining operand is E_def^far, with the full signed group-family sum retained under its original weight. A group's random-field support alone is not its background support: its Wilson contraction also carries the background transports along its contour hull. Any local flat comparison must include these intervals, preserving their order. In particular a group meeting separated sides must not be flattened on its random support while silently changing the long intervening transports.

The intended next analytic step is to insert the background derivative of the closed source-containing selected integrals and of their joint vacuum ratio before taking absolute values or summing group families. The existing single straight-side estimate eq:marked-background-curvature-payment is evidence for that derivative mechanism only at its interior-box scope. It does not already prove the joint result. No bound on E_def^far or closure of Stage 4 is asserted here.

## 4. Joint signed selected-integral estimate: the calculation

This section attempts the analytic estimate inside the full signed family, before any separate norm of a probe measure. Its caller is the background-subtracted group sum in mathscr R_xi, not a new standalone rooted-probe target. Every assertion below is a proof attempt pending focused review.

Fix a compatible root family A={D_1,...,D_m}. For each D_j use the selected measure Lambda^f_{xi;ell_j} of Stage 1 eq:probe-selection-measure, where ell_j=(mathcal D_j,mathsf J_j,mathsf P_j,Z_j), Z_j=D_j, and mathsf J_j is nonempty. Put q_j=|mathsf J_j| and q=sum q_j. The centred measure hat nu_D=nu_D-k(D)delta_0 is exactly the sum of these nonempty-probe selections: the empty-probe selections give its mass times delta_0 and disappear under centring. This uses the existing measure identity; it introduces no new expansion.

Define the finite-difference operator on a scalar closed source f by

$$
\Delta_{\mathsf J}f(B)
 =\sum_{K\subseteq\mathsf J}(-1)^{|\mathsf J\setminus K|}
     f(\mathbf1_KB)\;.
$$

Here every unselected young label is zero. For several roots compose these operators on their disjoint labels, denoting the result by Delta_boldJ f. The integrand is a sum of closed Wilson contractions, with the ordering and background transports retained. The source may have a fixed complementary closed holonomy h, transforming by conjugation at the base; all bounds below are uniform in real h in G.

### 4.1 The powers supplied by the signed source

Set u=C_chi g_0(1+r), increasing the fixed row/character constant once. On the real protected box, the row reconstruction depends on g_0B and has analytic derivative bounds on a larger fixed phase chart. Each selected free label affects only a bounded number of reconstructed contour links, and each link has a bounded input set. For the square, traversal multiplicity is bounded. Applying the product rule inside the closed character therefore gives C_chi^q derivative assignments, rather than n_C^q or q!. Derivative orders on any one row are bounded by twice its fixed input count, including the remainders used below. Higher row derivatives needed here are obtained from the existing bounded analytic phase map on its larger fixed phase ball by Cauchy estimates; this does not assume that the finite list of Stage 2 generic derivative constants extends to arbitrary order. The maximum order used on any row is fixed by L. All untouched transports are real unitary matrices inside the same closed contraction. The mixed integral remainder formula consequently gives

$$
\sup|\Delta_{\boldsymbol{\mathsf J}}f|
 \leq u^q\;.
$$

For a root with odd q_j, take the degree-q_j homogeneous term in its selected B variables, leaving all other root variables fixed. It is odd under B_{D_j}->-B_{D_j}. The difference from this leading term has an additional factor u, with a choice of the increment/row supplying the extra power bounded by q_j times a fixed constant; q_j<=2^{q_j} absorbs this into the earlier C_chi. The same argument can be applied simultaneously for any set of odd roots: the product-rule allocation count remains exponential in q because each row has finitely many inputs. Every term remains a closed contraction; no open interval is estimated separately.

Each selected Gaussian kernel is invariant under (B_{D_j},X_{D_j})->(-B_{D_j},-X_{D_j}) when its ordinary interaction labels are removed. This includes its determinant, quadratic cross term, negative compensator, real good and bad cutoffs and spatial Cauchy integrations. The tensor product in Stage 1 eq:fixed-probe-active-pairing gives a separate set of integration variables and separate reversal for each root. Thus the leading odd part cancels in the signed integrated source, including when several roots are present.

Let omega(g_0)=C_0^der g_0(1+r)^3 be the host bound, with C_0^der as defined in Section 7.1, omega_* its fixed potential budget, and R_Upsilon=omega_*/(2omega(g_0)). Choose g_0 so R_Upsilon>=2. In root j multiply its selected ordinary primitives by an independent complex parameter zeta_j, with |zeta_j|<=R_Upsilon; leave the Gaussian kernel, cutoffs and probes unchanged. If mathcal D_j is nonempty its selected integral vanishes at zeta_j=0, and a Cauchy difference between 0 and 1 costs at most 2/(R_Upsilon-1). If mathcal D_j is empty, its density is the even Gaussian/cutoff kernel and the previous reversal applies. Independent parameters on disjoint root components fit the same local potential budget simultaneously. Therefore an odd q_j costs the sum

$$
v=u+\frac{2}{R_\Upsilon-1}\;.
$$

No separate cancellation of a group coefficient is assumed; these cancellations occur within the original signed selected integrals. Both u and v tend to zero at their displayed coupling rates.

### 4.2 Numerical majorants paid with the same Gaussian reserve

For a fixed selected root ell define

$$
M_\ell=\sup_{|\zeta|\leq R_\Upsilon}
  \|\Lambda^{\mathrm f}_{\xi;\ell,\zeta}\|_{\rm TV}\;,
$$

where Lambda_{ell,zeta} means exactly the source-free measure of Stage 1 eq:probe-selection-measure with each selected ordinary primitive replaced by zeta times that primitive. All protected indicators, Gaussian densities/normalisers, compensators, integration carriers, weakening contours and seed data are unchanged. The total variation here is a numerical majorant after the signed source cancellation; it is not a bound on the centred Dirac tensors.

To sum M_ell without assuming a probe-measure estimate, use a positive comparison inside the existing forest majorant. There are at most P_M=4(4M+3)^4 probe labels with any given host, and each probe host has N_0<=s_p=5^4. Choose once, after M and before g_0,

$$
u_* =\min\left(\frac{1}{4},
 \frac{\omega_*e^{-\kappa s_p}}{8P_M}\right)\;.
$$

The number u_* is a fixed comparison weight, not a measure. For every probe label b, insert only in the numerical comparison the dummy potential p_b^+(a)=u_* on its protected host box and zero outside. Its selected Mayer factor e^{u_*}-1 is >=u_*. The summed dummy potential at a host is <=omega_*e^{-kappa d_0(Y)}/8, while the complex ordinary potentials use at most half that budget. Split labels with a common host exactly as in Stage 1's proof of probe measures. The seeds, conditioning carrier and Gaussian kernel depend on those hosts and are unchanged. Sum all split selections with the same active-host set first. Section 7.1 proves that their many-to-one positive numerical sum is dominated by the Stage 2 host majorant; no application of an unproved dummy-potential lemma is made.

Stage 2 eq:fixed-kernel-selected-majorant pays its determinant and compensator with the same Gaussian reserve; eq:native-source-initial-domain-sum, eq:native-source-enlarged-domain-sum and the final Y-prime sum in the proof of Stage2 Lemma activity-bounds then sum its seeds and final domains. This gives

$$
\sum_{\ell\, | \,Z(\ell)=D,\ \mathsf J(\ell)\ne\varnothing}
 u_*^{q(\ell)}M_\ell
 \leq m(D),\qquad
m(D)=\varepsilon_*e^{-\lambda_*\ell_1(D)}\;.
$$

All parameters in m(D) are the existing positive-majorant parameters of Stage 2; a fixed decrease of the remaining decay is allowed when polynomial factors are inserted below. No change is made to the physical potential or to a normalisation in E_def.

Combining reversal, Cauchy differences and the Gaussian reserve proves the proposed joint selected-integral bound

$$
\left|\int \Delta_{\boldsymbol{\mathsf J}}f(B)
       \,d\bigotimes_{j=1}^{m}\Lambda^{\mathrm f}_{\xi;\ell_j}(B_j)\right|
 \leq\prod_{j=1}^{m}
      u^{q_j}v^{q_j\bmod2}M_{\ell_j}\;.
$$

This bound retains the full joint source through each cancellation. For g_0 small enough that u<=u_* and v<=1 define

$$
\rho=\left(\frac{u}{u_*}\right)^2
          +\frac{u}{u_*}v\;.
$$

For every nonempty probe set, (u/u_*)^{q_j}v^{q_j mod2}<=rho. Summing all selected terms of every root yields the proposed integrated family bound

$$
|\mathfrak Q_\xi(\mathcal A;f_\xi)|
 \leq\prod_{D\in\mathcal A}\rho\,m(D)\;.
$$

The gain is O(g_0^2(1+r)^4) with constants fixed before coupling. It is obtained after signed integration, rather than by replacing a probe tensor with its total variation 2^{|mathsf J|}.

### 4.3 Background derivative and the joint vacuum ratio

For use in the flat subtraction, take a real background direction omega in one of the globally small analytic extensions used for a local coefficient comparison in the archived eq:marked-background-curvature-payment. Keep the geometry, carriers, cutoff norm, chosen mean, Gaussian reserve and fixed walk recipe unchanged. Let L_f be the number of contour background links whose local coefficient arguments vary; if a group's relative interval is compared, this includes that interval and its inverse closing transport. Complementary closed holonomies are held fixed. No outer history variable or physical weight is differentiated.

The actual derivatives of the selected Gaussian factors insert a scalar polynomial of degree at most two in (B,X), including the determinant trace; their moment is paid by the existing joint coercive Gaussian bound, at cost C N_1(D)||omega||_infty. Differentiated walk coefficients sum with the existing convergent differentiated series. The derivative of the host Mayer t-integrand is zeta(D_omega V)e^{t zeta V}(1+t zeta V); its t-integral is zeta(D_omega V)e^{zeta V}, zero at zeta=0. A Gaussian derivative remains even under each component reversal, and the leading source derivative retains the same odd parity. The signed powers from Section 4.1 therefore survive the derivative, with the additional factor C||omega||_infty(L_f+sum_D N_1(D)). No division by a primitive, activity or character is used.

In particular the proposed differentiated family estimate is

$$
|\mathscr D_\omega\mathfrak Q_\xi(\mathcal A;f_\xi)|
 \leq C\|\omega\|_\infty
       \left(L_f+\sum_{D\in\mathcal A}N_1(D)\right)
       \prod_{D\in\mathcal A}\rho\,m(D)\;,
$$

The factor N_1(D) from the differentiated Gaussian and host labels is kept explicitly; Section 7.1 pays it with the same fast positive majorant m(D). Additional decay is reserved only when these polynomial factors are later summed.

Keep the vacuum ratio as its joint ratio for the whole root family, not a product of one-root ratios:

$$
q_\xi(\mathcal A)
 =\exp\left[-\sum_{\mathfrak c\, | \,\mathfrak c\ {
m hits}\ \mathcal A}
                       \Phi^{\mathrm v}_\xi(\mathfrak c)\right]\;,
$$

where a cluster hitting several roots is counted once. The derivative is the derivative of this displayed joint exponential. The fixed-budget marked-cluster proof in Section 7.4 gives

$$
|q_\xi(\mathcal A)|\leq
 e^{\sum_{D\in\mathcal A}N_1(D)/8},\qquad
|\mathscr D_\omega q_\xi(\mathcal A)|
 \leq C\|\omega\|_\infty
       \sum_{D\in\mathcal A}N_1(D)
       e^{\sum_{D\in\mathcal A}N_1(D)/8}\;.
$$

That proof differentiates one vacuum activity in its connected-cluster tree majorant, keeping every occurrence and symmetry factor; Section 7.4 marks that single derivative in the fixed positive cluster majorant, without shrinking a previously chosen parameter or dividing by an activity. The extra polynomial is absorbed in unused domain decay. With this derivative included, the proposed bound for the term appearing in the signed source sum is

$$
\left|\mathscr D_\omega
 \left[q_\xi(\mathcal A)\mathfrak Q_\xi(\mathcal A;f_\xi)\right]\right|
 \leq C\|\omega\|_\infty
 \left(L_f+\sum_{D\in\mathcal A}N_1(D)\right)
 \prod_{D\in\mathcal A}
     \left[\rho\,m(D)e^{N_1(D)/8}\right]\;.
$$

The actual joint ratio has been differentiated before estimating. The normaliser I_{xi;0} encoded by this ratio is not cancelled with the physical history factor exp(c_xi)I_{xi;1}.

## 5. What must still be paid in the full signed subtraction

The preceding calculation is meant to supply the derivative estimate when the flat subtraction of each closed group is made inside mathscr R_xi. The group-family summation is carried out in Sections 6, 8 and 9. That requires paying the overlap of contour hulls as well as spatial decorations, and controlling restricted reference sums S^{circ,[mathfrak B]} with their same regional flat kernel. In particular no product of one-component ratios and no uncontrolled exponential in the loop length is an admissible substitute.

The group contraction for this caller must use the interval transport relative to its background interval, closed back to its base, with an arbitrary complementary closed holonomy h. Its flat value is a_W chi(h). The product bound for such closed contractions is the existing Burnside/Schur bound recorded in DELTA1_ATTEMPT Sections 5.4--5.6; no independent open matrix norm is an inductive carrier. The multi-group source factorisation must be checked against Stage 1 eq:part1-closed-family-pairing, not presumed from spatial independence of the physical law.

The signed bound in Section 6.4 remains a proof claim pending the integrated review of these analytic and combinatorial steps.

## 6. The closed group subtraction and its full signed caller

Use the square/torus geometry already imposed in WILSON_FIRST_RG_STEP_V2.tex, Section Extent Weights and the Square Geometry: side s=nL fine bonds, fine periods LK_i with K_i>=3(n+2), and n_C=4s. No new loop separation hypothesis is introduced. Under this geometry, contour hull length is paid by connected spatial extent as in eq:marginal-hull-extent of that section (or its displayed hull estimate): contacts of diameter <s/2 occupy one side or adjacent sides and fit in an arc of length <=4diam+1; otherwise n_C<=8diam. Periodic distances between square contacts equal their lifted distances.

For a group W let n(W) be the sum of N_1 over its marked roots and over every constituent domain in every occurrence of its vacuum-cluster list, counting multiplicities. Let H(W) be its existing contour interval, and define

$$
\mathfrak s(W)=n(W)+\frac{|\mathcal H(W)|}{LM}\;.
$$

The footprint F(W) is the set of LM-cubes meeting a constituent domain, its fixed coefficient stencil halo, or a contour/free-input stencil of a traversal in H(W). The source geometry gives |F(W)|<=C mathfrak s(W). For a component of the roots/cluster-occurrence graph, the union of its domains is wall connected, so its diameter is <=C LM times its total cube count. Its contact hull length is bounded by the square estimate above. Overlapping hulls have connected interval union; this pays the hull of a group by the sum of component counts. If Stage 1 merges all components because some hull is long, the sum of the component sizes in that overlap class costs >=c n_C/(LM). These facts give |H(W)|/(LM)<=C n(W). Coefficients whose local rectangle fails to lift are kept in the large-domain class below.

### 6.1 Closed relative interval functional

For W use only its root variables, with all other young variables zero, in the reconstructed links along H(W). Let T_W(a;U_1) be that interval transport and P_W(U_1) its zero-fluctuation interval transport, with their source orientations. Both begin and end at the same two vertices. Their relative product T_W(a;U_1)P_W(U_1)^{-1} is based and closed at the initial vertex. Define the scalar closed contraction

$$
c_W(U_1;h)=w_\xi(W)\int
 \chi\bigl(T_W(a;U_1)P_W(U_1)^{-1}h\bigr)
 \,d\bigotimes_{D\in\mathcal A(W)}\widehat\nu^{\mathrm f}_{\xi,D}(a)\;,
$$

where h is a complementary closed holonomy at that base and transforms by simultaneous conjugation. No open interval functional is estimated. The product T_W P_W^{-1} and h transform at one base, so every displayed scalar is gauge invariant. Put

$$
d_W(U_1;h)=c_W(U_1;h)-a_W\chi(h),\qquad
\mathfrak d_W(U_1)=\sup_{h\in G}|d_W(U_1;h)|\;.
$$

At the reference data c_W(1;h)=a_W chi(h) by Stage 1's closed Schur identity. The weights and measures in c_W are exactly those in the joint extraction, including all group vacuum-cluster occurrences; they are not a newly normalised conditional law.

Here is the source factorisation needed at the caller. In a compatible group family, a contour traversal in H(W) cannot have a contact with a root of a different group: that other contact hull would intersect H(W). Its reconstructed link thus uses W's root variables only. Every link outside all these intervals is its background link. The product of the root measures and the scalar group weights is precisely the one in eq:part1-closed-family-pairing, so integration of each interval gives a linear closed-contraction functional c_W. Substituting c_W-a_W chi in these same slots expands to exactly the finite signed sum defining R_xi(mathfrak B). This is an algebraic factorisation of the existing polymer integrals, not independence of physical field regions.

Apply the already proved finite-dimensional closed-contraction product inequality (DELTA1_ATTEMPT Sections 5.4--5.6). For the irreducible normalised character there is a constant K_chi such that

$$
|R_\xi(\mathfrak B)|
 \leq\prod_{W\in\mathfrak B}K_\chi\mathfrak d_W(U_1)\;.
$$

All factors on the right are norms defined by gauge-invariant closed contractions. Matrices may be used to prove the finite-dimensional multilinear identity, but no separately estimated endpoint-covariant matrix or open Wilson carrier is introduced.

### 6.2 Positive graph sums needed for the reference factors

This is the summation with the estimates of Sections 4 and 7. It concerns the source-containing groups, not the vacuum gas alone. A vacuum cluster occurrence c has cube cost n(c)=sum_{D in c}N_1(D). Its positive weight is the tree majorant of its Ursell coefficient: for the ordered domain tuple defining c, divide by its tuple factorial and sum the incompatibility spanning trees, multiplying the common vacuum activity majorants. This is precisely the positive tree sum used in the existing vacuum KP proof. Source roots have the weights rho m(D) of Section 4.2. For each W the product of those root weights, the positive vacuum-cluster weights and 1/k(W)! is denoted M(W). It bounds |a_W| and the corresponding undifferentiated closed source functional; both physical and reference data use the same numerical majorant.

Choose a positive eta after the fixed geometry and forest decay constants, small enough that 100 eta times the hull/footprint constants is below the unused domain decay. The proposed source-containing group sum is

$$
\sup_{n\in\mathcal I_C}
 \sum_{W\, | \,n\in\mathcal H(W)}M(W)e^{4\eta\mathfrak s(W)}
 +\sup_{\Delta\in\pi_1}
 \sum_{W\, | \,\Delta\in F(W)}M(W)e^{4\eta\mathfrak s(W)}
 \leq C\rho\;.
$$

Here is the combinatorial payment, rather than an assumption of this display. First form connected components of the roots/vacuum-cluster graph before hull merging. The original factorials are the exponential-generating factorials for these objects: marked roots are an unordered distinct family, and vacuum cluster occurrences carry 1/k!. Dropping the compatibility constraints is an upper bound. A connected graph indicator is at most its sum of incompatibility spanning trees. For a root node D, incident vacuum nodes have total weighted mass <=N_1(D)/8 by the vacuum pinned-tree estimate. For a vacuum node c, sum the same estimate over its constituent domains to obtain <=n(c)/8. The added source-root mass is at most C rho times the same cost, by the exponential animal sum and Section 4.2. For g_0 small it is <=that cost/8. Thus the two-species positive tree recursion is bounded with node cost one quarter of its cube cost. Explicitly, if t_v is a node weight and a_v this cost, the iterates T_v^{(k+1)}=t_v exp(sum_{v' incident v}T_{v'}^{(k)}) satisfy T_v^{(k)}<=t_v e^{a_v}, because sum_{v' incident v}t_{v'}e^{a_{v'}}<=a_v. Their monotone limit sums the rooted trees. This pays all vacuum decorations and leaves a factor rho for a component with a marked root.

The same recursion pays the polynomial loss when a component is rooted at a point in its hull rather than at a contact: its hull length is bounded by its spatial extent, so a root can be within at most C LM times its cube cost of that point. The possible root locations and the resulting polynomial in cube count are absorbed by the unused exponential decay. A spatial footprint pin is handled by a tree path from its marked root to the pinned cube; the square has bounded local traversal density, so the sum over source contacts weighted by that distance is uniform in n_C. The resulting decorated connected components have weighted hull and spatial pin sums <=C rho.

Now merge components whose hull intervals overlap. Sum their connected-overlap indicators by interval spanning trees, using the same recursion. A hull H meets components of total weighted mass <=C rho |H|. Its node cost contains eta |H|/(LM); choosing g_0 so C rho LM<=eta/8 pays this branching. The weighted union size is no larger than the sum of component sizes. The exponential-generating factorials agree with the interleavings of their cluster lists, exactly as in Stage 1's grouped-source construction.

There is one exceptional merge in that construction: if a hull becomes long, every remaining component is merged into the whole-contour group. A long overlap class costs >=c n_C/(LM) in the sum of its component sizes. Summing arbitrary remaining marked components costs at most exp(C rho n_C). At small g_0 this is absorbed into a fraction of the long-component decay; it is not left as a loop-length factor. The unused decay pays the whole-contour interval weight and all polynomial choices. This proves the proposed weighted group sum, provided the joint signed source bound of Section 4 applies with the stated positive majorants; that is the analytic point submitted for review.

Set mathfrak a_W=eta mathfrak s(W). Incompatibility of W and W' implies either contact of their footprints or overlap of their intervals. The two pin sums then give

$$
\sum_{W'\not\sim W}|a_{W'}|e^{a(W')}
 \leq C\rho\bigl(|F(W)|+|\mathcal H(W)|\bigr)
 \leq\frac{1}{8}\mathfrak a_W
$$

after choosing g_0 small, with every constant fixed before the coupling and independently of the loop length. Thus the regional reference group gas has a convergent connected-cluster logarithm and S^circ_{xi,C} is nonzero. Its restricted ratio is the single joint exclusion ratio of that gas. The pinned cluster estimate counts each cluster hitting mathfrak B once and gives

$$
\left|\frac{S^{\circ,[\mathfrak B]}_{\xi,C}}
                  {S^\circ_{\xi,C}}\right|
 \leq \exp\left(\frac{1}{8}\sum_{W\in\mathfrak B}\mathfrak a_W\right)\;.
$$

There is no product-of-ratios assertion. This is the step preventing a bound exp(C rho n_C) from replacing the flat scalar in E_def.

### 6.3 Subtraction and its curvature payment

For a group W, its local comparison box Q_W contains every constituent domain's coefficient halo and every background transport along H(W), including the inverse interval used to close the source. Its lifted side is <=C LM n(W). For the good interior boxes defined in Section 8.4, contained in Lambda_1 and disjoint from S_1, root a tree gauge at the base of the complementary holonomy. The ordered plaquette filling gives a phase bound C diam(Q_W)^2 delta_{Q_W}(U_1), where delta is the maximum plaquette deviation in the same source norm. The source is a closed contraction throughout. Apply Section 4.3 to this coefficient, with its group cluster list and the whole relative interval retained. Its derivative costs n(W)+|H(W)| and the factor rho for each marked root. Integrating the real phase path to the flat projection gives mathfrak d_W<=C delta_{Q_W} diam(Q_W)^2 times that polynomial times M(W), with slightly reduced domain decay. If the phase bound exceeds the fixed interpolation chart, the two undifferentiated endpoint bounds give the same inequality with a larger constant. No g_0-dependent restriction on group size is added.

The regional carrier I is retained in the reference coefficient. The comparison is used only for groups whose box, including every coefficient and source halo, is contained in Lambda_1 and disjoint from S_1. Boxes crossing that integration boundary are kept in the large-domain class, not interpolated. This leaves the target unchanged because their full contribution is paid by the tail below. On an interior box the centred kernel depends on branch fields only through U_1 there; the retained field and the boundary change are absent from its source rows and primitive arguments, and V_0 enters only through that background. Section 8 spells out this local-data verification.
On far histories, dist(Gamma_C,E(Lambda_1^c))>b. Section 8.4 uses the good comparison only when n(W)<b/(4C_Q LM), which ensures that every required stencil lies in an interior lifted box. All remaining groups are kept with n(W)>=b/(4C_Q LM); no assertion about their background continuation is made. Such groups keep both endpoint coefficients and use the undifferentiated estimate instead of an unproved flat comparison. The reserved exponential then pays the large-domain tail. The first group pin sum with one background derivative or this tail yields the proposed bound

$$
\sum_W K_\chi\mathfrak d_W(U_1)e^{\mathfrak a_W/8}
 \leq C_\chi n_C\rho
       \left(\varepsilon_1+e^{-c b/(LM)}\right)\;.
$$

Polynomial factors n(W)^k, the squared box size and the interval length have been paid using the reserved domain decay, not placed in a loop-dependent constant.

### 6.4 Full signed integrated bound reached by the calculation

Use the original mathscr R_xi sum and its closed-group product bound. Only after the flat subtraction is made and the joint reference ratio is retained do we take absolute values. The preceding estimates give

$$
|\mathscr R_\xi|
 \leq |S^\circ_{\xi,C}|
 \left[\exp\left(
 C_\chi n_C\rho(\varepsilon_1+e^{-c b/(LM)})
 \right)-1\right]
$$

on the far histories. This follows by bounding the compatible nonempty family sum by its exponential series after assigning K_chi mathfrak d_W e^{\mathfrak a_W/8} to each member. The original restricted reference sum, not a new vacuum normalisation, supplied the factor S^circ. At no stage was w_xi cancelled across histories.

Together with Section 2 the proposed first-step signed expectation bound is

$$
\begin{aligned}
|E_{\rm def}|&\leq C n_C e^{-c'p_*^2}\\
&\quad+\frac{1}{\mathcal Z_0}\int
 \mathcal O\left[\mathsf w_\xi\mathbf1_{A_{\rm cov}\cap\mathsf N_b^c}
 |S^\circ_{\xi,C}|
 \left(\exp\left(C_\chi n_C\rho
          (\varepsilon_1+e^{-cb/(LM)})\right)-1\right)\right](V)\,dV\;.
\end{aligned}
$$

The displayed form is a proof-attempt target with the payments in Sections 4 and 6, not an accepted result before review. Here b=floor(LMR_1/16), rho is explicitly defined in Section 4.2, and all physical history weights and Z_0 are retained. It leaves the regional reference scalar S^circ inside the expectation; identifying it with the perimeter/corner coefficient is Stage 4c and is not proved by this estimate. The expression also does not replace the reconstructed fine background loop by the coarse loop.

## 7. Explicit repairs of the joint kernel payment

These verifications supply the quantitative steps in Section 4; they do not add a new assumption on E_def.

### 7.1 Host budget and fixed parameter order

C_p bounds one primitive, whereas C_0=N_h C_p exp[kappa(B_h+4)] bounds their sum at a host. Use C_0^der>=C_0 also bounding the host directional derivative divided by ||omega|| on the same small background neighbourhood. This constant is chosen after M and before g_0, just as Stage 2's host constant. Neither omega_* nor epsilon_* nor any earlier choice is shrunk after M. The required derivative bound is obtained from the local formulas: the energy primitive is g_0 times the third-order Taylor remainder in the protected B variables, and its background derivative has the same factor g_0(1+r)^3 because its local analytic coefficients and their background derivatives are bounded on the larger fixed row chart. The Haar primitive and its background derivative start at order g_0^2(1+r)^2; the constraint-Jacobian primitive and its derivative are bounded by C g_0(1+r). Taking C_p^der to be the maximum of these finite local coefficient-derivative bounds, set C_0^der=N_h max(C_p,C_p^der)exp[kappa(B_h+4)]. Summing the same finite host assignments proves sup|D_omega V_xi(Y)|<=C_0^der g_0(1+r)^3 exp[-kappa d_0(Y)]||omega||, rather than assuming it. The host count uses the finite primitive/probe label types, not N_h (which counts primitives assigned to one host). Let N_type be the number of tagged ordinary primitive and probe types based in one fine translation cell of the fixed L-periodic template, and R_h the maximal base-to-host offset. Both are fixed by the displayed Stage 1 host constructions. Distinct active hosts each have such a labelled base in the fixed R_h-neighbourhood of D, so their number is <=H_M N_1(D), with H_M=N_type(LM+2R_h+3)^4; the selected probe count is at most the number of fine bonds in D, hence q<=4(LM+1)^4 sum_D N_1(D). Set omega(g_0)=C_0^der g_0(1+r)^3 and R_Upsilon=omega_*/(2omega(g_0)) throughout Sections 4 and 6. Only the coupling threshold changes.

For a host Y, let n_Y be the number of possible selected probe labels with host Y and put

$$
A_Y=\frac{\omega_*}{2}e^{-\kappa d_0(Y)},\qquad
B_Y=n_Yu_*\leq\frac{\omega_*}{8}e^{-\kappa d_0(Y)}\;.
$$

The bound n_Y<=P_M follows because b lies in its host, whose fine side is at most 4M, and there are four positive directions per site. After taking absolute values inside the real Mayer t-integral its ordinary factor is at most exp(A_Y)-1. Sum over all nonempty subsets of ordinary/probe labels at this fixed host, rather than assign each split selection to a separate unsplit selection. Their positive weight satisfies

$$
\begin{aligned}
\sum_{\varnothing\ne S\subseteq\{\mathrm{ordinary},\mathrm{probes}\}}
 \prod_{\ell'\in S}v_{\ell'}
 &\leq e^{A_Y}(1+u_*)^{n_Y}-1\\
 &\leq e^{A_Y+B_Y}-1\\
 &\leq (A_Y+B_Y)e^{A_Y+B_Y}\\
 &\leq\omega_*e^{1/2}e^{-\kappa d_0(Y)}\;.
\end{aligned}
$$

Here v_ordinary=exp(A_Y)-1 and every v_probe=u_*. The last inequality uses omega_*<=1/2 and A_Y+B_Y<=(5/8)omega_*e^{-kappa d_0(Y)}. This is a positive numerical comparison, not the Mayer factor of a complex combined potential. All split choices of the same active-host set have exactly the same Y_0, seed, conditioning carrier, Gaussian kernel, bad-bond choices and final-domain weakening. Thus their many-to-one sum is dominated at the host before applying the Stage 2 cover/seed sums. This proves the undifferentiated dummy domination claimed in Section 4.2. The final domain sum is the chain eq:native-source-initial-domain-sum, eq:native-source-enlarged-domain-sum and the final Y'-sum in the proof of Stage 2 lem:activity-bounds; no additional named equation is needed.

For a differentiated host the summed weight is bounded instead by

$$
R_\Upsilon\sup|\mathscr D_\omega\mathbf V_\xi(Y)|
 e^{A_Y}(1+u_*)^{n_Y}
 \leq A_Ye^{A_Y+B_Y}\|\omega\|_\infty
 \leq\omega_*e^{1/2}e^{-\kappa d_0(Y)}\|\omega\|_\infty\;.
$$

There are at most H_M N_1(D) active hosts, with the explicit finite-template count H_M defined below. Gaussian and walk derivatives have the same factor after their polynomial moment is paid. Consequently the differentiated sum, executed with the same positive host comparison, is

$$
\sum_{\ell\, | \,Z(\ell)=D}
 u_*^{q(\ell)}
 \sup_{|\zeta|\leq R_\Upsilon}
 \|\mathscr D_\omega\Lambda^{\mathrm f}_{\xi;\ell,\zeta}\|_{\rm TV}
 \leq C_M N_1(D)\|\omega\|_\infty\,
       \varepsilon_*e^{-\lambda_*\ell_1(D)}\;.
$$

In this display the source-free measure derivative includes every Gaussian normaliser and compensator. The uniform Gaussian coercivity gives polynomial moments <=C_M N_1(D) times the same exponential volume majorant, so no fresh exponential reserve is spent. This also gives |D_omega k^f(D)|<=C_M N_1(D)||omega|| m(D) for the vacuum activities, without shrinking epsilon_*.

### 7.2 Written multi-root cancellation

The input f is a single normalised character of the ordered closed reconstructed word, optionally closed with its inverse background interval and a fixed complementary h. For a linear combination, multiply the bound by the sum of the absolute coefficients; an arbitrary unbounded sum is not an input to this lemma. On covered branches its contour input labels lie in I, so the retained A_e and the boundary map do not enter these source rows; the centred kernel at t=0 likewise uses zero retained input. The reference group construction uses the same row/mean convention.

Let O_0 consist of odd-q_j roots whose ordinary selected label set is empty. For each j in O_0 let P_j take the homogeneous degree-q_j Taylor part of Delta_boldJ f in root j's selected variables, with other root variables fixed. These projections commute. Expand product_{j in O_0}(P_j+(1-P_j)). A term containing P_j is odd under reversal of exactly root j and integrates to zero against that root's even source-free density. Only product_{j in O_0}(1-P_j) remains, with one extra u per such root by the mixed Taylor remainder and the fixed row-overlap count. For each remaining odd root O_1, its ordinary selection is nonempty. Its independent zeta_j integral vanishes at zero, so the multivariable Cauchy difference supplies product_{j in O_1}2/(R_Upsilon-1). Together this gives u^q product_{j odd}(u+2/(R_Upsilon-1)), with fixed exponential-in-q constants absorbed into C_chi. The argument applies equally after one background derivative: the Gaussian derivative is even, the leading source derivative has the same parity, and a differentiated Mayer factor still vanishes at zeta_j=0.

Also Delta_boldJ f is identically zero if any selected label does not influence the closed source word. For each surviving root D there is therefore a contact with Gamma_C. This is the pin used in the subsequent A- and W-sums; no sum over unmarked roots in the volume is claimed to be uniform.

### 7.3 The common Hessian bounds are current inputs, not an open archive assumption

On physical branches Stage 2 lem:regular-bounds gives gamma_L/2<=H_xi<=m_L with the native force--constraint and soft gauge terms. For the local coefficient extension, choose tau_b>0 after tau_L,c_L,gamma_L and before g_0, with tau_b<=tau_L/4 and c_L tau_b<=gamma_L/4. The local entry formula f_{bb'}(A) of Stage 2 lem:c2-regional-entry has row and column sums <=m_L on the phase box tau_L, by the definition of m_L in eq:regular-covariance-entry-constants. Its Lipschitz bound is c_L, so a globally small extension e^{itB}, ||B||<=tau_b, has operator difference from H^circ at most c_L tau_b. Thus every compression to the same I satisfies

$$
\frac{3}{4}\gamma_L\,\mathrm{id}
 \leq H_{e^{itB}}\leq m_L\,\mathrm{id}\;.
$$

The existing recipe gamma=gamma_L/2, h_+=m_L therefore works both at the physical endpoint and throughout the extension. No new expansion instantiation or coefficientwise identification of different recipes is used. This discharges, for this caller, the old archive's conditional gamma_in,h_in premise using the current Stage 2 proof. It does not assert global closeness of the physical background to identity.

### 7.4 Differentiating the joint vacuum ratio without a late smallness choice

The archive's Psi_U(c) and Stage 1 Phi^v_xi(c) are the same Ursell expression phi^T(c)product k^f(D)/m!, with exactly the fixed-kernel vacuum activities; only the letter changes. Use that formula directly, so no archived status label is an input.

Let M_v(c) be its positive incompatibility-tree majorant built from m(D)=epsilon_*exp[-lambda_*ell_1(D)], and n(c)=sum_{D in c}N_1(D). The differentiated selection sum in Section 7.1 implies

$$
|\mathscr D_\omega\Phi^v_\xi(\mathfrak c)|
 \leq C_M\|\omega\|_\infty n(\mathfrak c)M_v(\mathfrak c)\;.
$$

This is a sum over the possible differentiated vertices, not division by an activity. Stage 2's numerical KP estimate is for this positive m(D): sum_{D' incompatible D} m(D') exp[(1+6theta)N_1(D')]<=N_1(D)/8. Apply its rooted-tree proof to m(D)exp[N_1(D)/4] with node cost N_1(D)/8; the combined exponent 3/8 is below 1+6theta. Hence

$$
\sum_{\mathfrak c\ {
m hits}\ \mathcal A}
 M_v(\mathfrak c)e^{n(\mathfrak c)/4}
 \leq\frac{1}{8}\sum_{D\in\mathcal A}N_1(D)\;.
$$

The family version follows by summing the single-root positive bound over D in A: clusters hitting multiple roots are overcounted only in this majorant, not in the exact ratio. Since n<=4exp(n/4),

$$
\sum_{\mathfrak c\ {
m hits}\ \mathcal A}
 |\mathscr D_\omega\Phi^v_\xi(\mathfrak c)|
 \leq\frac{C_M}{2}\|\omega\|_\infty
       \sum_{D\in\mathcal A}N_1(D)\;.
$$

Insert this into the derivative of the exact joint exponential q_xi(A). It proves the family ratio-derivative bound of Section 4.3. C_M is an outside prefactor for a single derivative; it is not put into every cluster weight. Thus no M-dependent shrinking of omega_* or epsilon_* is needed after those constants have already been fixed. The same fast m(D) controls the undifferentiated activity and its one-derivative polynomial majorant; the polynomial is paid by the displayed exponential moment.

## 8. Quantitative group and caller checks

### 8.1 Carrier, source and physical weights

All group comparisons and their flat-subtraction identities here are on A_cov. On this event the source rows have their free inputs in I, so Stage 1 lem:covered gives U_xi(0)=U_1 along the whole contour and eliminates A_e and Psi_xi from its fluctuating source rows. Stage 1 lem:collar and eq:c-collar-identity give K_{xi;0} with H=H_{xi,II}, P_{xi,0}(a)=sum_near p(a), and the chosen r-box: every primitive argument has zero retained input. The boundary Jacobian, far primitives and retained quadratic term are in c_xi, not in the centred coefficients. Every fixed-kernel operation, probe measure and vacuum activity is built from those centred objects. Therefore its local background data are U_1, the unchanged carrier geometry, and the fixed coupling/cutoff/mean prescription. V_0 is not replaced in the physical integral; its influence on these local coefficients is through U_1.

The old archive's local-data comparison applies on a box containing all source/coefficient stencils and lying inside Lambda_1, outside S_1. The fixed-kernel support proof places every surviving walk coefficient, seed inverse and primitive stencil there; keep the regional I and Omega_1 on both sides of the interpolation. At the flat endpoint these same local formulas are precisely the reference formulas for a_W, since their arguments contain no retained field, boundary map or additional V_0. This is an equality of the selected coefficient, not an equality of physical densities. The force--constraint and relative soft-gauge terms are the ones in Stage 1's regional Hessian and are included throughout.

Under a simultaneous site gauge, each Hessian entry, restricted inverse and fixed walk coefficient is conjugated by the free-field adjoint action; protected cutoffs are invariant, and the row solution is covariant. Orthogonal changes of integration variables leave the closed selected integrals unchanged, including their spatial Cauchy integrals. Their Laplace transforms give the corresponding covariance of each probe measure. Vacuum activities and their Ursell products are scalar invariants. Finally T_W P_W^{-1} and h are simultaneously conjugated at the interval base. This proves the group closed-contraction gauge law factor by factor; no straight-side assumption is used in that law.

The positive physical scalar exp(c_xi)I_{xi;1} will be denoted mathsf w_xi in this section only, to distinguish it from the group weight w_xi(W). The original O is the positive outer integration/history sum of Stage 1 eq:native-source-explicit-outer-operation; the Haar and constraint factors are measures, and all displayed cutoffs/exponentials are nonnegative. Thus E_h[X]=Z_0^{-1}int O[mathsf w_xi X]dV is a positive normalised functional. Stage 3 controls E_bdry, and the full identity is

$$
\mathbb E_\varepsilon[W_\chi(C)]
 =\mathbb E_h[\mathbf1_{A_{\rm cov}}S^\circ_{\xi,C}f_\xi(0)]
  +E_{\rm def}+E_{\rm bdry}\;.
$$

The far uncovered event is empty: failure of coverage puts one of the deterministic contour/input labels Gamma_C in E(Lambda_1^c), hence A_cov^c is a subset of N_0 and of N_b. The exterior response is not omitted from E_def; it is the separately controlled E_bdry of Stage 3.

### 8.2 Two quantitative pins

A component gamma consists of its nonempty unordered root family A(gamma) and ordered vacuum-cluster occurrence list (c_1,...,c_k), with connected incidence graph as in Stage 1; n_gamma counts every constituent cube with its occurrence multiplicity. Define t_gamma=(rho^{|A(gamma)|}/k!) product_{D in A(gamma)}m(D) product_{j=1}^k M_v(c_j). Summing unordered distinct roots may be overcounted by ordered root tuples divided by their factorial. Connected class data K are unordered families of these components with connected hull-overlap graph; their positive weight t_K is the product of their t_gamma. For the positive recursion their sum is overordered tuples divided by the tuple factorial, dropping the disjointness restrictions. This only enlarges the sum and fixes all multiplicity conventions. It has at least one marked root. Fix

$$
0<\varpi\leq\min\left(\frac{1}{16},\frac{\lambda_*}{64C_g}\right)\;.
$$

The two-species tree proof can be run with weights multiplied by exp(\varpi times node cube count), since the vacuum estimate in Section 7.4 holds with exponent up to 1/2 and node cost N/4 uses at most \varpi+1/4<1/2. The marked-root mass is made <=node cost/8 by choosing rho small; this changes only g_0. It follows for a root D_0 that

$$
\sum_{\gamma\, | \,D_0\in\mathcal A(\gamma)}
 t_\gamma e^{\varpi n_\gamma}
 \leq\rho m(D_0)e^{(\varpi+1/4)N_1(D_0)}\;.
$$

Summing D_0 with a fixed source contact a, using the existing domain animal bound, gives a constant C_pin with

$$
\sup_{a\in\mathcal I_C}
 \sum_{\gamma\, | \,a\in\mathsf T_\gamma}
 t_\gamma e^{\varpin_\gamma}\leq C_{\rm pin}\rho\;.
$$

Choose fixed A_h,A_x so that |H_gamma|<=A_h LM n_gamma and the distance from a source contact to any cube in its connected domain is <=A_x LM n_gamma, including the coefficient halos. These follow from the square geometry and wall connectivity. Put theta_h=\varpi/(4A_hLM) and theta_x=\varpi/(4A_xLM). If a traversal a lies in H_gamma and a' is any contact of gamma, then d_C(a,a')<=A_h LM n_gamma. Hence

$$
\begin{aligned}
\sum_{\gamma\, | \,a\in H_\gamma}
 t_\gamma e^{\varpi n_\gamma/4}
 &\leq\sum_{a'\in\mathcal I_C}e^{-\theta_h d_C(a,a')}
       \sum_{\gamma\, | \,a'\in\mathsf T_\gamma}
                       t_\gamma e^{\varpin_\gamma/2}\\
 &\leq C_{\rm pin}\rho
       \left(1+\frac{2}{e^{\theta_h}-1}\right)\;.
\end{aligned}
$$

For a spatial cube Delta in gamma's domain, the analogous inequality is

$$
\sum_{\gamma\, | \,\Delta\subset X_\gamma}
 t_\gamma e^{\varpi n_\gamma/4}
 \leq C_{\rm pin}\rho
       \sum_{a'\in\mathcal I_C}e^{-\theta_x d_T(a',\Delta)}\;.
$$

For each of the four straight sides the last sum is at most 1+2/(exp(theta_x)-1), up to the fixed cube/halo offset factor. It is bounded by the full one-dimensional periodic lattice sum in that direction, independently of n and the periods. This retains rho even when Delta lies in a vacuum cluster. Adding the contour-hull stencil part of F(gamma) uses at most C LM possible traversals near a cube, times the preceding hull-pin bound; C LM is a fixed constant. Thus both pins have a uniform C rho bound with the displayed enhanced weight.

Let A_s=1+A_h. Choose eta>0 after these fixed constants with 1000 eta A_s<\varpi/8. This makes the component pins valid with e^{100 eta mathfrak s(gamma)} and leaves a fixed exponential margin. All constants are fixed before g_0. The source smallness conditions are C rho LM<=eta/8 and the earlier root-incidence bound.

### 8.3 Short classes and the exceptional whole-contour merge

Run the positive overlap-tree recursion on the decorated components using weights enhanced by exp(64 eta mathfrak s(gamma)). The pin bound controls the overlap sum by C rho |H_gamma|, which is <=eta mathfrak s(gamma)/8 at the chosen source smallness. The rooted recursion therefore gives hull and footprint pins for every overlap-connected class, before the promotion of a long class to the whole contour <=C rho with enhanced weight exp(64 eta sum_gamma mathfrak s(gamma)); the additional node cost is covered by the 100 eta component margin. Summing a root component containing the pin proves these bounds. A short class uses the union of its hull intervals, so its size is bounded by that additive class cost.

If a class K becomes long, let sigma_K=sum_{gamma in K}mathfrak s(gamma). The class-level inequality is

$$
\sigma_K\geq\frac{1}{LM}\sum_{\gamma\in K}|H_\gamma|
                 \geq\frac{n_C}{2LM}\;.
$$

Use a traversal in the union interval to anchor that class. There are at most n_C anchors. The enhanced class pin bound gives

$$
\sum_{K\ {\rm long}}t_K e^{4\eta\sigma_K}
 \leq C\rho n_Ce^{-30\eta n_C/(LM)}\;.
$$

Indeed the remaining exponent 60 eta sigma_K is at least 30 eta n_C/(LM). Once one such class occurs Stage 1 merges all other components into the whole-contour group. The other components, with their 4 eta weights, sum to at most exp(C rho n_C). The whole-contour interval weight costs exp(4 eta n_C/(LM)). Therefore

$$
C\rho n_C
 e^{-30\eta n_C/(LM)}
 e^{4\eta n_C/(LM)}e^{C\rho n_C}
 \leq C\rho n_Ce^{-25\eta n_C/(LM)}
 \leq C'\rho\;.
$$

The middle inequality uses C rho LM<=eta. The final maximum is finite uniformly in n_C because LM and eta are fixed. If a spatial pin lies in an additional component, root that component using its footprint pin; it costs another C rho, while the same anchored long-class factor and remaining exponential are paid by the displayed inequality. If the pin lies in the long class, use its footprint pin instead of its hull pin. Pins lying on the whole contour itself are covered by the total whole-group bound. This proves the exceptional-merge pin estimate without assigning its cost to a single original component.

Together with the short-class recursion these calculations supply the two weighted group pins claimed in Section 6.2. Polynomial moments are allowed by using a smaller part of the same fixed enhanced-weight margin.

### 8.4 Interior boxes, endpoint and differentiated group weight

Let C_Q be a fixed geometric constant for the group footprint and row/contour halos such that a liftable enclosing comparison rectangle has diameter <=C_Q LM n(W). Increase it so that a group with

$$
n(W)<\frac{b}{4C_Q LM}
$$

has its entire rectangle and stencils within b/2 of a source contact and has an injective lift. On a far history this box lies inside Lambda_1, hence inside Omega_1, and outside S_1=(Omega_1 minus Omega_1^{~-1}) union R_1. Its plaquettes satisfy delta_Q(U_1)<=C epsilon_1, with epsilon_1=g_1p_0(g_1), by Stage 2 Lemma c2-plaquette-deviation and the distance check in Section 11.5. The source spectrum/row hypotheses in Section 7.3 hold on the globally small extension used for its local comparison.

All other groups keep their undifferentiated difference, with |c_W|+|a_W chi|<=2M(W). Their occurrence count is at least b/(4C_Q LM). If a rectangle fails to lift, the same lower bound holds since N_min=min_i N_i (where N_i=LK_i is the fine period)>=2LMR_1>32b and a wrapping connected network has length at least a fixed fraction of N_min. This definition avoids any unsupported interpolation across the integration boundary.

For the good box use the exact coefficient locality and covariance established in Section 8.1. Root its tree gauge at the initial interval base, keeping h fixed. The tree gauge, small-phase extension and fundamental theorem of calculus compare c_W(U_1;h) to c_W(1;h)=a_W chi(h). It is the same regional reference coefficient, since I, all selection indices and all local geometry are retained. The old bulk comparison is not used to replace it by a different coefficient.

Differentiate the group weight by the product rule, retaining each occurrence:

$$
\mathscr D_\omega w_\xi(W)
 =\frac{(-1)^{k(W)}}{k(W)!}
 \sum_{j=1}^{k(W)}\mathscr D_\omega\Phi^v_\xi(\mathfrak c_j)
                \prod_{l\ne j}\Phi^v_\xi(\mathfrak c_l)\;.
$$

Section 7.4 bounds this by C_M||omega|| sum_j n(c_j) times the original positive product majorant, without dividing by any Phi. Combining this with the joint source derivative gives C||omega||(n(W)+|H(W)|)M(W), uniformly in h. The curvature phase bound contributes C diam(Q_W)^2 delta_Q. Using |H|<=C LM n(W), all these losses are a fixed constant times epsilon_1 times a fixed polynomial in mathfrak s(W). The enhanced group pin estimate absorbs that polynomial: x^k exp(-eta x)<=k!eta^{-k}.

For a large group the factor exp[-eta b/(8C_Q LM)] is extracted from its reserved exp(eta mathfrak s(W)/2) weight. Combining the two classes and summing over a contour pin yields exactly

$$
\sum_W K_\chi\mathfrak d_W(U_1)e^{\mathfrak a_W/8}
 \leq C_\chi n_C\rho
          \left(\varepsilon_1+e^{-c b/(LM)}\right)\;.
$$

The same matrices and same cutoff norm are used in the physical and flat endpoints. Every source being estimated is the closed c_W functional; no partial interval is replaced by a scalar before its closed subtraction is formed.

## 9. Defined extension and countable-gas limit

### 9.1 Statement of background scope and coefficient path

Sections 4 and 7 give the joint source and one-background-derivative bound both at the physical centred background and on every globally small real extension described here. They apply to each single closed character chi(T_W P_W^{-1}h) uniformly in real h. They do not assert a path from the entire physical background to identity in one global small chart.

Fix a good interior group of Section 8.4. Choose its enclosing fine rectangle Q_W with all coefficient, reconstruction, averaging and physical interval/closing stencils included. The source local coefficient support proof says that, for the fixed selection indices and fixed spatial Cauchy coefficient defining this group, only the background links on this rectangle are used. In particular the restricted seed inverse uses entries on E_0, the walk coefficient has all its coefficient domains in the final component, and the potential/source rows have the displayed finite stencils. The regional I and Omega_1 and every auxiliary parameter are held fixed.

Gauge U_1 on Q_W by its rooted tree gauge g_W, with g_W(base)=id. If C diam(Q_W)^2 delta_Q<=tau_b/2, write its principal phases B_W(b)=(1/i)log U_1^{g_W}(b) on the required rectangle and extend B_W=0 on every other bond of the original fine torus. Define the global coefficient argument and its direction by

$$
U_{W,t}(b)=e^{itB_W(b)},\qquad
\omega_W(b)=B_W(b),\qquad
\|\omega_W\|_\infty=\max_b h(B_W(b)),\qquad 0\leq t\leq1\;.
$$

The norm is the fixed invariant h norm, with the fixed comparison from the cutoff norm already absorbed in C. Set L_f equal to the number of occurrences of background links in the relative word T_W P_W^{-1} on which this argument varies; L_f<=2|H(W)| times the fixed reconstruction-row overlap constant. The complementary closed h is held fixed at the root base.

At each t form H_t=iota_I^* mathsf H^{Omega_1}_{U_{W,t}} iota_I and the row reconstruction q_{U_{W,t}} and the near primitives p_{U_{W,t}}, with all retained input set to zero and the same protected r-box. For a generic noncritical U_{W,t}, the energy primitive is defined by subtracting its constant, linear and quadratic Taylor terms as in Stage 1 eq:native-source-energy-primitives; the Hessian keeps the force--constraint term. The Haar and constraint-Jacobian primitives use their same analytic row formulas. These definitions specify an analytic coefficient extension. We do not identify this auxiliary kernel with the physical CRE integral at t in (0,1), and do not impose the original fixed V constraint along that path. At the physical endpoint each compensated primitive agrees with its defining Taylor-subtracted formula by locality. Criticality is used in the primitive-sum identity for the physical exponent, not to assert that U_{W,1} is a global minimum. At the flat endpoint the formulas agree with the reference formulas.

Section 7.3 proves gamma_L/2<=H_t<=m_L using the finite regional entry formula, flat compression gap and local phase bound. The designated inverses, reconstruction and group means use the fixed smaller row charts since ||B_W||<=tau_b/2 and tau_b<=tau_L/4. The host norms and their derivatives are bounded by C_0^der g_0(1+r)^3 on these common charts. The fixed-kernel Gaussian payment, positive forest budget and source estimates therefore hold uniformly in t with the same recipe. The force term is one of those local entries; it is not omitted off the minimum.

At t=1 the group coefficient agrees with the original one by coefficient locality on Q_W and its simultaneous gauge covariance; values outside Q_W can be replaced in the coefficient argument because no term of that spatial Cauchy coefficient consults them. Root gauge g_W(base)=id leaves h unchanged. At t=0 the coefficient is exactly the regional reference one, with the same I and the same group index W. Consequently

$$
d_W(U_1;h)=\int_0^1
 \mathscr D_{\omega_W}c_W(U_{W,t};h)\,dt\;.
$$

If the sufficient small-phase bound fails, the two endpoint estimates give the same curvature bound as stated in Section 6.3; no continuation is claimed in that regime. This path is the missing connection between the local physical coefficient and the globally small extension, not an assumption of global near-identity physical fields.

The derivative of c_W uses product_{j}Phi^v(c_j) and the root integral. Differentiating the product gives the explicit occurrence sum of Section 8.4, whose majorant is C||omega||(sum_j n(c_j))M(W). Differentiating the root integral gives C||omega||(L_f+sum_root N(D))M(W) by Sections 4 and 7. Thus their sum is C||omega||(L_f+n(W))M(W), exactly the coefficient derivative inserted in the last display. This is a cluster-list bound for the same group weight, not an attempt to identify a one-root vacuum ratio with it. The joint-ratio estimate of Section 7.4 controls the original family normalisation; the group occurrence estimate controls its exact regrouping.

### 9.2 Original parameter and period conventions

All results here inherit Stage 1's standing conditions and Stage 3's even fine periods. In particular every fine period N_i is an even integer multiple of ell_mac=LMR_1. The scale ell_mac is odd, since L,M,R_1 are odd powers of L. If N_i=q_i ell_mac, then q_i is even and positive, so

$$
N_{\min}=\min_i N_i\geq2LMR_1>32\lfloor LMR_1/16\rfloor=32b\;.
$$

The strict middle inequality follows because ell_mac is odd. This is independent of the square-fit condition K_i>=3(n+2); both conditions are retained. The original periods also satisfy the fixed source-row and coarse-grid conditions from Stage 1. Thus the good comparison box and every fixed stencil have a unique lift under the small-group criterion; the periodic failure really is in the large-group class. No condition on the fluctuating field or denominator is added.

Gamma_C consists of individual positive bond labels of the contour and all their fixed input templates. The constant C_L in |Gamma_C|<=C_L n_C already includes the number and size of these templates. The radius-b ball in the near-history union bound is around each of those individual bonds, not around an unexpanded template. Its bound 4(2b+3)^4 therefore needs no further n_C-dependent factor. The Stage 3 input is the one-point probability <=exp(-c_*p_*^2), with p_0(g)=A_0(log g^{-2})^{p_0}, p_0>=5mathfrak r>=10 and p_*=min(p_0(g_0),p_0(g_1)).

Define E_bdry=E_h[1_cov B_xi[f_xi]+1_{cov complement}F_xi(1)], as in Stage 3. It is separately bounded there by C n_C(1+g_0r)exp(-c p_*^2). The present E_def contains only the covered centred-kernel subtraction. This states exactly where the exterior-response and uncovered contributions remain in the full physical identity; neither is dropped.

### 9.3 Countably many group species and differentiation

At a fixed finite torus, enumerate groups by finite cutoffs W_N={W: n(W)<=N}. This is finite: the domain set is finite, n(W) bounds the number of roots, cluster occurrences and members in every occurrence. Its gas satisfies the same KP inequality, since deleting species only decreases the positive sums. Let S_N and L_N be its partition sum and connected-cluster logarithm. The finite-species identity is S_N=exp L_N.

Every group has a nonempty contour interval. The proved pin sum gives

$$
\sum_W|a_W|e^{\mathfrak a_W/8}\leq C\rho n_C<\infty\;.
$$

The positive rooted-tree estimate therefore bounds the total absolute connected-cluster series by this same finite sum, up to a fixed constant. Each finite cluster tuple is present for all sufficiently large N. Absolute domination gives L_N->L. Independently, the full gas sum over finite compatible families is absolutely bounded by exp(sum_W|a_W|). Dominated convergence gives S_N->S^circ_{xi,C}. Hence

$$
S^\circ_{\xi,C}=e^L\ne0\;.
$$

The same argument applies after excluding every species incompatible with a fixed compatible family mathfrak B, giving the restricted partition identity. Their logarithmic difference is exactly the connected-cluster sum of tuples hitting that family, counted once. Its absolute sum is <=sum_WinB mathfrak a_W/8 by the pinned estimate. This proves the ratio used in Section 6.4 for the countable index set, not only for finite truncations.

For background derivatives, Sections 7.1 and 7.4 give summable positive derivative majorants independent of t on the specified extension. On each finite truncation the ordinary product/integral derivatives are justified by uniform Gaussian coercivity and the fixed protected box; the fixed walk derivative series converges on its unchanged contours. The derivative cluster majorant is n(c)M_v(c), paid by its explicit exponential moment, and the group derivative majorant has only the explicit polynomial in mathfrak s(W), paid by its reserved enhanced weight. Uniform absolute convergence permits termwise differentiation and t-integration before passing to the countable limit. No formal differentiation of a conditionally convergent series is used.

### 9.4 Final integrability at the physical caller

The signed near-history contribution is bounded after forming mathscr R_xi, without exchanging its infinite sum with the outer integral. On far histories Sections 6--9 give an absolute group-family majorant <=|S^circ| times the displayed exponential. Since |S^circ|<=1 and the exponential bound is uniform in all branch fields and retained variables, it is integrable against the normalised positive history law at each fixed loop and cutoff. It therefore justifies the required far-history sum/integral exchanges. The physical Z_0 and mathsf w_xi=exp(c_xi)I_{xi;1} remain exactly those in Section 1.

## 10. Analytic inputs for the coefficient extension

### 10.1 Joint background/phase analyticity and primitive derivatives

Fix one of the finitely many row/primitive stencil types, in its translated fine-lattice frame. Write the background on that stencil as U_Z(b)=exp(iZ_b). Background directions use the maximum h-norm on this finite label set. Choose tau_b and a positive phase radius theta_0 so that ||Z||<2tau_b and ||A||<2theta_0 keep every finite path product and relative product entering RG1 (0.4), (0.11) inside the matrix logarithm neighbourhood ||W-id||_op<1/2. This is possible uniformly over the finite types: every word has bounded length and products of exp(iA)exp(iZ) are analytic in both variables.

For the mean in (0.11), write its defining equation sum_j log(W_j M^{-1})=0. At W_j=id, M=id, its derivative in the Lie-algebra parameter of M is minus n times the identity. The parametric analytic implicit-function theorem gives a jointly analytic local mean in the background and fluctuating phases. It agrees with the selected Federbush mean of Stage 1: both take value id at zero and solve that equation within the same smaller IFT neighbourhood. Shrink the joint radii so the specified mean stays in that neighbourhood; no global uniqueness is inferred from a logarithm chart.

The bond constraint on a row c is the joint analytic function

$$
\mathcal Q_Z(A)=\frac{1}{i}\log\left(
 \mathsf M(e^{iA}U_Z,c)\mathsf M(U_Z,c)^{-1}\right),\qquad
LQ_Z=D_A\mathcal Q_Z(0),\qquad
N_Z(A)=\mathcal Q_Z(A)-LQ_ZA\;.
$$

Here mathsf M is the fixed RG1 (0.4) bond average, not the finite-group mean. N_Z(0)=D_A N_Z(0)=0 for every Z. The coefficient alpha_Z of the designated phase in LQ_Z is uniformly invertible on a smaller background polydisc, by the identity-background designated inverse and continuity. Thus h_Z, the designated inverse with LQ_Z h_Z=id, and C_Z=iota_free-h_Z LQ_Z iota_free are analytic in Z, with uniformly bounded first background derivatives. These formulas fix their maps and normalisations without a new free-variable convention.

The row solution is defined by

$$
\widetilde D_Z(A)=N_Z(A-h_Z\widetilde D_Z(A))\;.
$$

On smaller joint balls its right-hand derivative in D has norm <=1/2, uniformly in Z, because D_A N_Z(A)=O(||A||). Uniform analytic contraction, equivalently the parametric IFT, gives joint analyticity and ||Dtilde_Z(A)||<=C||A||^2. Cauchy estimates on the larger joint balls, followed by the order-two zero in A, give for ell=0,1 and each fixed k needed below

$$
\|D_Z^\ell D_A^k\widetilde D_Z(A)\|
 \leq C_{\ell,k}\|A\|^{\max(2-k,0)}\;.
$$

All constants are maxima over finitely many types and are independent of volume, history and g_0. The dimensions of these types depend only on L and G. The protected free input satisfies g_0||C_Za||<theta_0/2 after reducing the coupling. The phase q_Z(a)=g_0C_Za-h_Z Dtilde_Z(g_0C_Za) consequently satisfies

$$
\|D_Zq_Z(a)\|\leq Cg_0(1+r),\qquad
\|D_Z^\ell D_a^kq_Z(a)\|\leq C_{\ell,k}g_0^k
$$

for ell=0,1 and k>=1 up to twice the fixed row input count plus one. These are joint background/young-field derivative bounds, not the assertion that a list of phase-only derivative constants already contains them.

Use analytic traces of X and X^{-1} to extend every Re tr X from real unitary fields: Re tr X equals tr(X+X^{-1})/2 there. The energy and relative gauge expressions are therefore joint analytic finite word functions. For the local energy function E_Z(s) in dimensionless free phase s, the compensated primitive has the exact Taylor-remainder form

$$
p_Z^{\rm E}(a)
 =-\frac{g_0}{2}\int_0^1(1-t)^2
     D_s^3 E_Z(tg_0a)[a,a,a]\,dt\;.
$$

The first background derivative has the same g_0 factor, since D_Z D_s^3 E_Z is uniformly bounded on the smaller joint domain. Hence |p^E|+||D_Zp^E||<=C g_0(1+r)^3. The relative means and soft-gauge term are included in E_Z. The Haar function log(sigma(q)/sigma(0)) is analytic in q and has an order-two zero; composed with q_Z it and its Z derivative are <=C g_0^2(1+r)^2. The constraint-Jacobian logarithm is log det(id-h_Z D_A Dtilde_Z) on a matrix ball of radius <1/2. Its value and its Z derivative are <=C g_0(1+r), because D_A Dtilde_Z=O(g_0(1+r)) and D_ZD_A Dtilde_Z has the same order. The real determinant is positive in this ball, so the analytic logarithm restricts to the required real logarithm, not an uncontrolled absolute-value branch.

Summing the finite primitive types assigned to one host proves the host derivative bound with C_0^der=N_h max(C_p,C_p^der)exp[kappa(B_h+4)] used in Section 7.1. This constant and the finite source derivative constants may be chosen after M and tau_b, before g_0. No earlier Mayer, walk or reserve choice depends on them.

### 10.2 Differentiated fixed walks and exact locality

Use exactly Stage 1 eq:c-weighted-walk-series. Its parameters s_H=2h_+, A_H=id-H/s_H, P_H=A_H^{n_*}, q_H=1-gamma/s_H, beta=V_*q_H^{n_*}, a_*=exp(81kappa_1) and n_* are fixed from the common input bounds; they are not spectral functions re-evaluated at the varied background. Include every geometrically allowed tuple of bond indices in that displayed series, including coefficients that vanish at a particular background. Thus differentiation does not change a nonzero-term index set.

The weights w_omega(sigma) and domains D(omega) depend only on these labels and the fixed geometry. Let c_H bound the Schur row/column norms of D_omega H/||omega||, supplied by the finite analytic entries. Then D_omega A_H=-(D_omega H)/s_H, and

$$
D_\omega A_H^j=\sum_{l=0}^{j-1}
 A_H^l(D_\omega A_H)A_H^{j-1-l}\;.
$$

A block sum of the derivative is bounded by V_j j q_H^{j-1}c_H||omega||/s_H. Put d_*=V_*n_*q_H^{n_*-1}c_H/s_H and let d_ini be the maximum of the corresponding finitely many j<n_* bounds. Differentiating the grouped walk products gives an absolute Schur bound

$$
\|D_\omega S_{Z_0}(\sigma)\|_{\rm Schur}
 \leq C_{\rm w}^{\partial}\|\omega\|_\infty,\qquad
C_{\rm w}^{\partial}
 =s_H^{-1/2}n_*\left(
 \frac{a_*d_{\rm ini}}{1-a_*\beta}
 +\frac{a_*^2V_*d_*}{(1-a_*\beta)^2}\right)\;.
$$

The denominators are positive because a_*beta<=1/4. The same bound holds on the unchanged spatial Cauchy circles. Derivatives of C_E are -C_E(DH_E)C_E, and of Gamma_E are the product rule applied to iota_E^*H Pi_{I minus E}S_{Z_0}; their operator norms are bounded by fixed constants times ||omega||.

For a selected final domain Z, spatial variables outside Z are zero and the protected seed enlargement Z_0' lies in Z. A walk with a coefficient domain meeting a cube outside Z therefore has a zero spatial factor. The same factor remains zero after background differentiation. Every surviving walk, including every hidden fine step in its grouped powers, has its coefficient stencil inside its declared domains, by D_b's fixed halo construction. The restricted inverse C_E consults only entries on the whole seed E, which is already included in the comparison rectangle; it is not a global inverse restricted afterwards. Normalised Gaussian determinants are det C_E, not a determinant of H on all I.

All potential and source stencils and every constituent vacuum domain of c_W are included in Q_W. These facts prove locality at t=1 in Section 9.1, with the fixed regional I: no surviving selected coefficient consults the background outside Q_W, and no field-dependent global spectral quantity appears among its recipe parameters. The common full Gaussian prefactor has already cancelled inside the exact conditional ratio defining F_xi(0); it is not a missing local activity factor. This conditional cancellation does not cancel mathsf w_xi=exp(c_xi)I_{xi;1} or the physical Z_0.

### 10.3 Explicit complex-Gaussian moment payment

On a selected component write E for its seed carrier, J_Z for the auxiliary carrier, H_E=iota_E^*H iota_E, C_E=H_E^{-1}, Gamma=Gamma_1+iGamma_2. The source pairings are complex bilinear. Before cutoffs and Mayer factors, the joint density with respect to real Lebesgue dB dX is the two centred Gaussian normalisations times

$$
\exp\left[-\frac{1}{2}\langle B,H_EB\rangle
 -\langle B,\Gamma X\rangle
 -\frac{1}{2}\langle\Gamma X,C_E\Gamma X\rangle
 -\frac{1}{2}\|X\|^2\right]\;.
$$

Call this density G_sigma. Its columns outside J_Z vanish identically in Gamma and its derivative, by Stage 1's structural component-block identity. Those auxiliary standard Gaussians integrate to one, so no moment cost proportional to |I| is introduced.

Take the existing alpha=alpha_G and C_alpha=(H_E-alpha id)^{-1}. The absolute density multiplied by exp(alpha||B||^2/2) is a positive real Gaussian with the original determinant prefactor. In variables y=B+C_alpha Gamma_1 X its exponent is

$$
-\frac{1}{2}\langle y,(H_E-\alpha)y\rangle
-\frac{1}{2}\langle X,(\mathrm{id}-T_\alpha)X\rangle\;,
$$

where T_alpha=Gamma_1^T(C_alpha-C_E)Gamma_1+Gamma_2^T C_E Gamma_2 is the existing reserve matrix. The available bounds are H_E-alpha>=gamma/2, ||T_alpha||<=1/4 and ||Gamma_1||<=A_* from Stage 2. Therefore, with

$$
c_*=
 \frac{\min(\gamma/2,3/4)}
 {2(1+2A_*/\gamma)^2}>0\;,
$$

the real quadratic form is >=c_*(||B||^2+||X||^2). Its total unnormalised mass is the determinant product bounded by exp(N_1(Z)) in the existing Gaussian payment. Its normalised covariance is <=c_*^{-1}id. If d=d_G(|E|+|J_Z|), this proves the moment inequality

$$
\int(1+\|B\|^2+\|X\|^2)
 e^{\alpha_G\|B\|^2/2}|G_\sigma(B,X)|\,dB\,dX
 \leq(1+d/c_*)e^{N_1(Z)}\;.
$$

Here d<=8d_G(LM+1)^4N_1(Z), so the loss is polynomial in the component count with a fixed M-dependent constant. It uses the positive 3/4 margin in id-T_alpha, not a new exponential reserve.

The logarithmic derivative of the Gaussian normalisation contributes Tr(C_E DH_E)/2. The exponent derivative contributes -<B,DH_E B>/2, -<B,DGamma X> and -D<Gamma X,C_E Gamma X>/2, with DC_E=-C_E DH_E C_E. Each is bounded by C||omega||(d+||B||^2+||X||^2) by Section 10.2. The last displayed moment thus proves the differentiated Gaussian payment C_M N_1(Z)||omega||e^{N_1(Z)} on the same Cauchy circles and carriers. All normalisers and the negative compensator have been differentiated. The protected cutoff domain is fixed throughout; no cutoff translation or surface term is suppressed in this background derivative.

### 10.4 Explicit source remainder bounds

Let J=(b_1,...,b_q) be distinct selected labels and let all other selected root variables be denoted a'. The mixed fundamental theorem gives the exact identity

$$
\Delta_J f(B,a')=
 \int_{[0,1]^q}D_{b_1}\cdots D_{b_q}
 f\left(a'+\sum_{j=1}^qs_jB_{b_j}\right)
 [B_{b_1},\ldots,B_{b_q}]\,d\mathbf s\;.
$$

The sum in the argument means the canonical embedding into the free carrier. Let K be a fixed bound for the number of source rows affected by one free label and the number of inputs of one row. Only the source f_W(a;h)=chi(T_W(a)P_W^{-1}h), or the original full closed Wilson character, is used. Untouched factors are unitary in its representation. The derivative product rule has at most K^q row assignments. The derivatives within a row have order <=2K+1, whose constants from Section 10.1 are fixed. Consequently, with a fixed C_chi enlarged once,

$$
\|D_{b_1}\cdots D_{b_q}f\|
 \leq(C_\chi g_0)^q,\qquad
\sup|\Delta_J f|\leq(C_\chi g_0r)^q\;.
$$

For root j let P_j be its homogeneous degree-q_j projection after taking Delta_{J_j}. Subtract the integrand at zero root input in the preceding mixed formula and integrate its first derivative on the segment t(sB). This gives q_j terms, each with one additional derivative and one additional selected B factor. Thus, for any set O of roots,

$$
\sup\left|\prod_{j\in O}(1-P_j)
                 \Delta_{\boldsymbol J}f\right|
 \leq u^{q+|O|}\;,
$$

where u=C_chi g_0(1+r), with the choices of the extra increment bounded by product q_j<=2^q and absorbed in C_chi. The row-order bound 2K+1 covers these remainders simultaneously because the roots have disjoint selected labels and a row has at most K inputs. A single background derivative hits either a row coefficient or one of the L_f background occurrences of the closed word; Sections 10.1 and the product rule give

$$
\sup\left|D_\omega\prod_{j\in O}(1-P_j)
                 \Delta_{\boldsymbol J}f\right|
 \leq C_\chi\|\omega\|_\infty(L_f+q)
                 u^{q+|O|}\;.
$$

These are the inequalities used in the commuting-projection cancellation of Section 7.2. Roots with an empty ordinary selection retain only these remainders under their even Gaussian integration; roots with an ordinary selection use their independent Cauchy vanishing. This recovers the product u^{q_j}v^{q_j mod2}, and its one-background-derivative version, before any total variation majorant is summed. Every term remains a closed contraction with the same fixed h and original word order.

### 10.5 Tree gauge on a growing comparison rectangle

Let Q be an injectively lifted fine rectangle of largest side R>=1, with any chosen root o in it. For x in Q let P_x run from o to x in coordinate order, with each coordinate run oriented according to its displacement. These paths form a rooted tree. Define g(o)=id and g(x)=U(P_x). Then U^g(b)=U(P_x)U(b)U(P_{x'})^{-1} for b=(x,x') is the based closed transport at o of the fundamental loop.

For a bond of direction mu, move its last mu-step past the later coordinate runs of P_x. Each interchange with a perpendicular fine edge replaces the ordered word by one plaquette transport, conjugated by the preceding word. All plaquettes stay in Q, and the number of interchanges is <=sum_{nu>mu}|x_nu-o_nu|<=3R. Negative coordinate runs reverse a plaquette orientation but do not alter this count. Induction on those interchanges gives the exact nonabelian word

$$
U^g(b)=\prod_{j=1}^{m_b}
 G_jU(\partial p_j)^{\epsilon_j}G_j^{-1},\qquad
m_b\leq3R,\qquad\epsilon_j\in\{1,-1\}\;.
$$

The order is the order of the step interchanges; G_j is the preceding transport to that plaquette, so every factor is a conjugated closed plaquette. No commutative plaquette replacement is used. By unitary invariance and telescoping,

$$
|U^g(b)-\mathrm{id}|_\sigma
 \leq3R\,\delta_Q(U)\;.
$$

This bound has a constant independent of R. Norm conversion to operator norm and the fixed local group logarithm give h(log_G U^g(b))<=3C_G sqrt(N) R delta_Q whenever that distance is inside the group chart. Choose once C_T sufficiently large that C_T R^2delta_Q<=tau_b/2 implies this chart condition and

$$
\max_{b\subset Q}h(B_b)
 \leq C_T R^2\delta_Q(U)\leq\tau_b/2\;.
$$

This is possible with C_T depending only on the fixed group chart and tau_b, since R>=1; for example require C_T>=3C_Gsqrt(N) and C_T>=6sqrt(N)tau_b/r_G. The constants do not grow with b or the RG scale R_1. If this sufficient condition fails, the existing two-endpoint coefficient bound is used, not this interpolation. The lemma therefore covers growing good boxes without imposing their smallness as an extra hypothesis. Root g(o)=id leaves the complementary h fixed in every closed contraction.

## 11. Identification of the centred coefficient and its local extension

This section concerns c_W of Section 6.1, with W fixed on a covered branch. Its first caller is the interpolation identity in Section 9.1. The conclusions below retain the Stage 1 and Stage 2 hypotheses and their fixed choices of charts, carriers, cutoffs and parameters. They do not identify the regional scalar S^circ with the perimeter/corner scalar.

### 11.1 Which exterior dependence is removed

Write the exterior-response parameter as s and the background-path parameter as t. Stage 1 defines

$$
K_{\xi;s}(a)=\Theta_\xi(a)\exp\left(-\frac{1}{2}\langle a,H_{\xi,II}a\rangle-s\langle a,H_{\xi,IJ}A_{\rm e}\rangle+\sum_{\mathfrak p\ {
m near}}\mathfrak p(a+sA_{\rm e})\right)\;.
$$

The field U_1 is held fixed in this s-interpolation. The collar identity and boundary-response identity give, with F_xi(s) defined using the same Wilson function f_xi,

$$
\mathcal J^{\rm a}_\xi[1]=e^{c_\xi}I_{\xi;1},\qquad
F_\xi(1)=F_\xi(0)+\mathcal B_\xi[f_\xi]\;.
$$

On a covered branch every contour row has its entire free-input set in I. Since Psi is the identity on I and A_e vanishes there, row locality implies, for every a in the integration box, that every contour link in f_xi(a) is its reconstruction from a alone at background U_1. This is the proof of Stage 1's covered lemma with a retained instead of set to zero; it uses no estimate. Thus both the source and K_{xi;0} have zero retained free input. The dependence of U_1 itself on the exterior determining data remains.

Every selected measure in c_W is constructed from K_{xi;0}: its potentials are the near primitives at a, its Hessian is H_{xi,II}, and its cutoff is Theta_xi. The factors involving Psi(A_e), the far primitives, and the boundary-map Jacobian are in c_xi, and the interaction between a and A_e is accounted for by B_xi. They are not factors of c_W. Consequently the physical comparison keeps

$$
\frac{1}{\mathcal Z_0}\int\mathcal O\left[e^{c_\xi}I_{\xi;1}F_\xi(0)\right]dV
+\frac{1}{\mathcal Z_0}\int\mathcal O\left[e^{c_\xi}I_{\xi;1}\mathcal B_\xi[f_\xi]\right]dV\;.
$$

It does not replace I_{xi;1} by I_{xi;0}. This is the role of the boundary separation in CRE (1.26)--(1.30), rather than a claim that the exterior input of the original conditional integral vanishes.

### 11.2 Covariance of the selected coefficient

For a site gauge g, let R_g a(b)=Ad_{g(b_-)}a(b) on free bonds. This is orthogonal for h, preserves each free bond subspace, and commutes with geometric restrictions. Stage 1's row-covariance identities give q_{U^g}(R_g a)=R_g q_U(a). Their use includes the branch: the small row solution transforms to a solution of the transformed constraint in the same invariant small ball. Uniqueness there identifies it with the selected solution. The joint fixed point of Section 10.1 is identified with this solution by choosing its phase radius so that its O(|A|^2) bound lies inside Stage 1's uniqueness ball. The inverse and mean branches are those fixed in the row construction.

The action of each plaquette is invariant. Each relative soft-gauge mean is conjugated at its base. Therefore the constant, linear and quadratic Taylor coefficients of their energy primitives transform with their arguments, including the force--constraint term. Subtracting these coefficients preserves covariance of the compensated primitives even at noncritical backgrounds. The Haar density is invariant under conjugation. The constraint-Jacobian endomorphism transforms by conjugation between the same free and designated spaces, so its determinant and its selected logarithm are unchanged. The logarithm branch is fixed by continuation from zero within the nonvanishing chart. Hence each primitive, and each host sum V(Y), is invariant under simultaneous transformation of background and free variables.

The Hessian, each restricted seed inverse, and every fixed walk transform by R_g on their indices, by the entry identities of Stage 1 and the geometric walk formula. All geometric choices, Cauchy variables and Mayer parameters are unchanged. In the selected integral change variables B to R_g B and X to R_g X. Lebesgue and standard Gaussian measures, the two allowed cutoff norms, the conditional Gaussian determinant, and the cross and compensator terms are preserved. Each selected measure is thus pushed forward by R_g. In the probe formula, delta_B-delta_0 is pushed to delta_{R_g B}-delta_0. Summing selections proves

$$
\widehat\nu^{\rm f}_{U^g,D}=(R_g)_*\widehat\nu^{\rm f}_{U,D}\;.
$$

The vacuum activities, their Ursell products and w_U(W) are scalar invariants: the incompatibility graph and every numerical combinatorial factor are field independent. Both T_W P_W^{-1} and the complementary h transform at the initial interval vertex o. Therefore

$$
c_W(U^g;g(o)hg(o)^{-1})=c_W(U;h)\;.
$$

The rooted comparison gauge has g(o)=id. Open transports occur only in this equality inside the closed character; no norm of an open transport is used.

### 11.3 Domain and endpoint

Section 8.4 defines the small interior groups by n(W)<b/(4C_Q LM). Its support includes every root domain, each vacuum-cluster domain occurrence, their coefficient halos, and the whole contour interval H(W), including its closing transport. The hull-extent bound is needed here: a box enclosing only the random inputs would not suffice. Under that bound the enclosing rectangle has diameter at most C_Q LM n(W), lies within b/2 of a source contact, and is injectively liftable under the stated period convention. On the far-history event the box and its halos lie in the regular region. All other groups, including winding or boundary-reaching groups, stay in the large-domain tail of Section 8.4. This is the small-local-domain versus large/distant-domain separation used in RG1 (3.5)--(3.9) and CRE's boundary separation; no interpolation is asserted for a group in the tail.

On a small interior group, first use its rooted tree gauge. If C_T diam(Q_W)^2 delta_{Q_W}(U_1)<=tau_b/2, define B_W and U_{W,t} as in Section 9.1. Choose tau_b with both tau_b<=tau_L/4 and c_L tau_b<=gamma_L/4, as Section 7.3 already specifies. The entry Lipschitz estimate and flat compression gap then supply the same two-sided Hessian bounds throughout this path. The fact that this path need not consist of constrained minima is allowed only because its compensated primitive formulas are defined on the joint chart; physical criticality identifies those formulas at the endpoint, not at intermediate t.

For each selected coefficient, Section 10.2 fixes all walk parameters and restricts every surviving walk and coefficient stencil to its final domain. The seed inverse is the inverse on the seed, not the restriction of a global inverse. Thus, on the supports included in Q_W, the t=1 recipe equals the gauge-transformed physical centred recipe. Its values on bonds outside Q_W cannot enter that coefficient. Applying Section 11.2 returns the coefficient to the original gauge. At t=0 the recipe is the regional reference recipe with exactly the same I, Omega_1, W, cutoffs and constants. This yields the endpoint identities

$$
c_W(U_{W,1};h)=c_W(U_1;h),\qquad
c_W(U_{W,0};h)=a_W\chi(h)\;.
$$

These equalities concern the selected coefficient, not the outer history density. If the tree-gauge phase condition fails, the two-endpoint majorant of Section 6.3 is used; if the box condition fails, the whole group is in the tail. Neither case is assigned an endpoint identity it does not satisfy.

For differentiation under the selected integrals, the norm of X in Section 10.3 is explicitly the norm of X restricted to J_Z. All other auxiliary columns integrate out with mass one and have zero derivative. The common strictly positive c_* supplies a background-independent Gaussian majorant for that finite-dimensional integral and its first derivative. The selected sums and vacuum occurrence sums use the summable majorants of Sections 7.4 and 8.4. These are the dominated-convergence hypotheses needed for the coefficient fundamental theorem of calculus. The group derivative still includes the derivative of w_U(W).

Bałaban's RG1 (3.21), (4.35)--(4.36) estimates changes of reconstruction and domain rather than declaring them zero. No such change is made in the identities above: the regional carrier and each local recipe are fixed. A failure of the stated finite-support or covariance identity would invalidate the endpoint step and would require a retained comparison error. It could not be absorbed by the tree-gauge estimate alone.
### 11.4 Precise endpoint conventions

The endpoint statement is restricted to covered far histories and the small interior groups of Section 8.4. Extend the rooted site gauge from Q_W to the whole torus by the identity on sites outside Q_W. Every background bond consulted by the coefficient has both endpoints inside Q_W; in defining Q_W enlarge the enclosing rectangle to contain both endpoints of each Hessian stencil, row set, block-mean path, plaquette, and interval or closing-path bond. This enlargement is part of the fixed halo included in C_Q. Boundary bonds of the site-gauge extension are not consulted by the coefficient.

Only the finite formula w_U(W)=(-1)^{k(W)}/k(W)! times the product of the specified vacuum cluster occurrences is varied along U_{W,t}. Neither the global partition function Xi_U nor the global exclusion ratio q_U(A) is an operand of this interpolation. Section 7.4 supplies a sum of the occurrence derivative majorants; Section 8.4 applies their finite product rule. The original exclusion ratio was expanded at the original background before the group construction. Thus no identity or positivity statement for a global partition function at U_{W,t} is needed to identify either endpoint.

The same regional scalar a_W is defined in Stage 1's joint-extraction subsection from w^circ(W) and the same root measures at identity background; it is not an infinite-volume coefficient. Its closed Schur identity is the t=0 identity used here.

For the geometric lifting claim, represent each constituent connected domain by a tree of its constituent coarse cubes and adjoining faces. Root the union at a source contact. Each root or cluster-domain tree has at most its number of cubes minus one edges; incompatibility joins have bounded range, and the finite reconstruction halos add a fixed range at their contacts. The contour-hull extent bound bounds the additional contour edges needed to join the components by C LM n(W). The resulting connected bond network thus has a spanning traversal of length at most C LM n(W), with C fixed. If this is less than N_min/4, lift the traversal from its root. Every lifted vertex lies within that distance of the root. Two lifts of the same vertex could differ only by a nonzero period vector, whose length is at least N_min; the two paths giving them have total length less than N_min/2, a contradiction. The enclosing coordinate rectangle and its stipulated halos therefore project injectively. Choose C_Q to include these constants. With n(W)<b/(4C_Q LM) and N_min>=2LMR_1>32b, the small-group criterion implies this sufficient lifting condition. Conversely, failure to lift under this construction cannot occur in the small-group class. No curvature estimate for a winding loop is used.

In applying the entry estimates, take tau_b small enough for both h-max and the stated entry-chart norm, using h<=sigma<=sqrt(N)h before choosing g_0. Geometrically allowed zero walks merely re-index the same series and do not change its value or support domains.
### 11.5 Source and radius specifications

The imported mean covariance is RG1 (0.6), M({u U_j v})=u M({U_j})v, for the specified mean on its small-diameter domain. RG1 (0.10) states that the selected Federbush mean has this property. The use here is for unitary site gauges, with no smallness restriction on the gauge values; the relative distances and the real chart domains are preserved. The cutoff invariance is the conjugation invariance of the operator norm or of the normalised Hilbert--Schmidt norm, respectively, as displayed in eq:marginal-cutoff-invariance of the manuscript.

The curvature citation in Section 8.4 is Stage 2 Lemma c2-plaquette-deviation. For a plaquette of Q_W choose a vertex x in Lambda_1. Within the L-block containing x choose a neighbouring vertex still in that block (L>=3). That internal fine bond is free, since designated bonds join distinct blocks, and belongs to I because it has endpoint x in Lambda_1. The plaquette therefore has a bond within two fine-bond metric units of I. This is within 3R_c, as required by the lemma. This yields the claimed bound on delta_{Q_W}, with the fixed conversion between its stated operator norm and the norm in the tree-gauge estimate.

For the branch identification in Section 11.2, let C_D,joint be the constant in the uniform estimate ||Dtilde_Z(A)||<=C_D,joint||A||^2 on the joint chart of Section 10.1. After choosing that chart, reduce theta_0 so that 2theta_0<=vartheta_*/2 and 4C_D,joint theta_0^2<rho_d. At real backgrounds the joint solution for ||A||<2theta_0 then lies in the uniqueness ball of Stage 2 Lemma c2-uniform-chart and hence is its selected solution. Choose the coupling threshold after these radii so the phase inputs g_0 C_U B of the enlarged free box remain in ||A||<theta_0. No expansion parameter is enlarged after this choice. These conditions specify the radius reductions already used in Section 11.2.

## 12. Quantitative assembly at the signed physical caller

The claim in this section is a first-step estimate for E_def of Section 1. It uses the same Stage 1 and Stage 2 hypotheses, the compatible even-period and square-fit conventions of Section 9.2, and the same irreducible normalised character. Constants below may depend on the fixed group, character, L, M and the fixed expansion and chart choices, but not on the coupling, square length, compatible torus size or history. The coupling is chosen last. The regional scalar S^circ is retained; no identification with a perimeter/corner scalar is asserted.

### 12.1 Joint derivative supplied to the group coefficient

The quantitative derivative used here is obtained from Sections 7.1, 7.2 and 10, rather than from the archived straight-side inequality mentioned in Section 4.3. For each selected root the source is Delta_J f, a closed character difference. Section 10.4 bounds its mixed Taylor remainder by u^q and supplies an extra u for each odd leading term removed by reversal. The root's Gaussian derivative is even in its joint (B,X) variables, including its determinant and compensator derivatives. A derivative of a selected ordinary potential carries a factor zeta and vanishes at zeta=0. Thus the same independent-root parity/Cauchy argument of Section 7.2 applies after one background derivative.

The differentiated host sum of Section 7.1 bounds a differentiated potential without dividing by that potential. Section 10.2 sums derivatives of all geometrically indexed walks with the same spatial contours. Section 10.3 pays each Gaussian derivative by C_M N_1(D) times the same e^{N_1(D)} determinant majorant, with X restricted to J_Z. All other auxiliary variables integrate to one. Host and Gaussian derivatives therefore insert one factor N_1(D), not one new constant per selected label. The source derivative inserts the number L_f of varying contour/closing links plus the number of selected labels; Section 7.1 bounds that latter number by C_M sum_D N_1(D). The resulting joint integral estimate is

$$
|\mathscr D_\omega\mathfrak Q_U(\mathcal A;f_U)|
 \leq C_\chi\|\omega\|_\infty
 \left(L_f+\sum_{D\in\mathcal A}N_1(D)\right)
 \prod_{D\in\mathcal A}\rho m(D)\;.
$$

Here rho and m(D) are the same quantities defined in Section 4.2. This statement is used on the fixed coefficient path of Section 11; it does not differentiate an outer history weight or a global exclusion ratio.

For a vacuum occurrence c, the selected-integral derivative gives |D_omega Phi_U^v(c)|<=C_M||omega|| n(c)M_v(c), as in Section 7.4. Differentiate the finite product w_U(W) by its occurrence product rule in Section 8.4. Adding the root-integral derivative yields, uniformly for h in G,

$$
|c_W(U;h)|\leq M(W),\qquad
|\mathscr D_\omega c_W(U;h)|
 \leq C_\chi\|\omega\|_\infty
       \bigl(n(W)+|H(W)|\bigr)M(W)\;.
$$

The undifferentiated estimate also holds at the original physical background and at the regional flat reference. M(W) contains rho for every marked root and the original factorials. Polynomial factors have not yet been summed or hidden in M(W). The factor from the relative interval's inverse word is at most a fixed multiple of |H(W)| and is included in C_chi.

### 12.2 Explicit payment of the local and tail losses

Write s=mathfrak s(W)>=1 and a_W^{KP}=eta s (the latter denotes the cost mathfrak a_W, not the scalar a_W). The fixed hull and box bounds give n(W)+|H(W)|<=C LM s and diam(Q_W)<=C LM s. The endpoint identity of Section 11 and its plaquette estimate therefore imply, for a small interior group passing the phase test,

$$
\mathfrak d_W(U_1)
 \leq C_\chi\varepsilon_1 s^3M(W)\;.
$$

If that small group's phase test fails, C_T diam(Q_W)^2 delta_Q>tau_b/2. Using delta_Q<=C epsilon_1 and diam(Q_W)<=C LM s gives 1<=C epsilon_1 s^2, with constants fixed before the coupling. The two undifferentiated endpoint bounds then give the same displayed inequality, since s>=1. No curvature comparison is used for a group outside the small interior class; for such a group,

$$
\mathfrak d_W(U_1)\leq2M(W),\qquad
s\geq T_b:=\frac{b}{4C_Q LM}\;.
$$

For the local polynomial payment let

$$
C_{\eta,3}=\sup_{s\geq1}s^3e^{-(31\eta/8)s}<\infty\;.
$$

Then s^3 exp(eta s/8)<=C_{eta,3}exp(4eta s). For the tail, s>=T_b gives exp(eta s/8)<=exp(-2eta T_b)exp(4eta s). Hence the two weighted pin estimates proved in Sections 8.2--8.3 imply

$$
\begin{aligned}
\sum_W K_\chi\mathfrak d_W(U_1)e^{\mathfrak a_W/8}
 &\leq C_\chi\left(\varepsilon_1+e^{-2\eta T_b}\right)
                 \sum_W M(W)e^{4\eta\mathfrak s(W)}\\
 &\leq C_\chi n_C\rho
       \left(\varepsilon_1+e^{-c b/(LM)}\right)\;,
 \qquad c=\frac{\eta}{2C_Q}\;.
\end{aligned}
$$

The last summation uses that every W has a nonempty contour interval: summing the contour-pin estimate over the n_C traversals overcounts every group at least once. The cubic moment and the tail use the existing 4eta weight, not an additional size-dependent hypothesis or a loss in the scalar S^circ. The exceptional whole-contour merge remains the one paid in Section 8.3, where the long class pays both the arbitrary extra components and the whole-contour weight.

### 12.3 Signed family sum and physical expectation

Section 6.2's reference-group cluster estimate supplies the single joint ratio

$$
\left|S^{\circ,[\mathfrak B]}_{\xi,C}/S^\circ_{\xi,C}\right|
 \leq\prod_{W\in\mathfrak B}e^{\mathfrak a_W/8}\;.
$$

Combine it with the closed-contraction product bound of Section 6.1 after forming each d_W. The nonempty compatible-family sum is bounded by the exponential series of the preceding summable one-group weight. For covered far histories this proves the candidate quantitative conclusion

$$
|\mathscr R_\xi|
 \leq |S^\circ_{\xi,C}|
 \left[\exp\!\left(C_\chi n_C\rho
          (\varepsilon_1+e^{-c b/(LM)})\right)-1\right]\;.
$$

The countable-group limit is the dominated finite-species limit of Section 9.3, with the same positive majorant and the nonzero reference partition function supplied by its convergent logarithm. No quotient is formed at a zero partition function.

Combining the near-history estimate of Section 2 with positivity of the original history measure gives

$$
\begin{aligned}
|E_{\rm def}|\leq{}&C_\chi n_Ce^{-c'p_*^2}\\
&+\frac{1}{\mathcal Z_0}\int
\mathcal O\left[\mathsf w_\xi\mathbf1_{A_{\rm cov}\cap\mathsf N_b^c}
 |S^\circ_{\xi,C}|\left(
 e^{C_\chi n_C\rho(\varepsilon_1+e^{-cb/(LM)})}-1\right)\right](V)\,dV\;.
\end{aligned}
$$

All history weights, deferred integrations and physical normalisation are the ones in Section 1. The exact source on the left was summed before taking absolute values. Since the regional reference scalar is a normalised integral of a character of modulus at most one against its positive reference kernel, |S^circ|<=1. The same physical normalisation therefore also yields the numerical consequence

$$
|E_{\rm def}|\leq C_\chi n_Ce^{-c'p_*^2}
 +e^{C_\chi n_C\rho(\varepsilon_1+e^{-cb/(LM)})}-1\;.
$$

Here rho=O(g_0^2(1+r)^4), epsilon_1=g_1p_0(g_1), b=floor(LMR_1/16), and p_*=min(p_0(g_0),p_0(g_1)). The exponential is not replaced by its linear term unless its argument is bounded. In particular no assertion of UV summability for a fixed physical loop is made. The conclusion has exactly the hypotheses and quantitative scope stated at the beginning of this section.
### 12.4 Fixed reserve and adjacency conventions

The exponential vacuum estimate used in Section 8.2 holds with n(c)/2 as well as n(c)/4. Indeed apply the same rooted-tree proof to the numerical activity m(D)exp(N_1(D)/2) with node cost N_1(D)/8. The combined exponent is 5/8, below 1+6theta in the existing numerical KP hypothesis. Thus

$$
\sum_{\mathfrak c\ {m hits}\ \mathcal A}
 M_v(\mathfrak c)e^{n(\mathfrak c)/2}
 \leq\frac{1}{8}\sum_{D\in\mathcal A}N_1(D)\;.
$$

In the footprint incompatibility pin, contact includes wall adjacency, not just intersection of the two cube sets. For each footprint cube sum the spatial pin over its neighbouring cubes as well. Even allowing all cubes touching at any face, edge or corner gives at most 3^4 choices in four dimensions, so the cost is a fixed factor in the constant C multiplying rho. Choose the source smallness condition after incorporating this factor. It does not alter rho, the reserve exponent or the loop-length dependence. The final tail rate in Section 12 is c=eta/(2C_Q); earlier weaker tail displays remain consequences with a reduced positive c.

## 13. TeX form of Sections 1-12

The block below is the TeX translation of Sections 1-12 above, spliced on 19 October 2026 into WILSON_FIRST_RG_STEP_V3.tex as the last appendix (`app:signed-defects`, immediately before the bibliography), with the final estimate of Section 12.3 as `prop:c4-12-3`, the family sum of Section 6.4 as `lem:c4-6-5`, the group pin sum of Section 6.3 as `lem:c4-6-4` (proved in `sec:c4-12-2`) and the tree gauge of Section 10.5 as `lem:c4-10-5`. It omits the review records and process prose; the translation itself has not been reviewed. Notation follows V3 (`\mathcal Z_0`, `\mathcal O`, `\mathsf w_\xi`, `\mathbb E_{\mathrm h}`, `A_{\mathrm{cov}}`, `E_{\mathrm{bdry}}`, `S^\circ_{\xi,C}`, `R_\xi(\mathfrak B)`, `a_W`, `w_\xi(W)`, `\mathcal H(W)`, `\mathfrak Q_\xi`, `\Lambda^{\mathrm f}_{\xi;\ell}`, `\Phi^{\mathrm v}_\xi`, `m(D)`, `N_1(D)`, `\mathbf V_\xi(Y)`, `\pi_*`). Three constants were renamed to avoid clashes with Appendix `app:exterior-chessboard`: the box constant C_Q is `C_{\mathrm{box}}`, the Gaussian coercivity c_* is `c_{\mathrm G}`, the tree-gauge constant C_T is `C_{\mathrm{tg}}`; the near-history exponent is the stage 3 tail exponent `c_*` of `eq:c4-2-2`. Label map: draft section k = `sec:c4-k`, subsection k.j = `sec:c4-k-j`, lemmas `lem:c4-k-j`, displays `eq:c4-k-j`; Section 5 is `rem:c4-5-1` inside `sec:c4-6`.

```tex
\section{The Signed Integrated Wilson Defects}\label{app:signed-defects}
This appendix bounds the defect term of the branch identity \eqref{eq:c-one-step-branch-identity} at the carrier $I$ of Section~\ref{sec:sourced-effective-interaction}, under the original history law: the joint defects $R_\xi(\mathfrak B)$ of \eqref{eq:part1-joint-defect} are summed with their restricted reference sums before absolute values are taken, each closed group is compared with its flat value by one background derivative along a local coefficient path, and the comparison is paid by the Gaussian reserve, the positive host comparison and the positive group summation of Sections~\ref{sec:c4-4}, \ref{sec:c4-7} and~\ref{sec:c4-8}. The result is Proposition~\ref{prop:c4-12-3}: on compatible even fine periods and for the square geometry of Section~\ref{sec:extent-weights},
\begin{equation*}
    |E_{\mathrm{def}}|\leq C'_Ln_Ce^{-(c_*/2)\pi_*^2}+e^{C_\chi n_C\rho(\varepsilon_1+e^{-cb/(LM)})}-1\;,
\end{equation*}
with $\rho=O(g_0^2(1+r)^4)$, $\varepsilon_1=g_1p_0(g_1)$, $b=\lfloor LMR_1/16\rfloor$, $\pi_*=\min(p_0(g_0),p_0(g_1))$, $C'_L$ and the tail exponent $c_*$ from Appendix~\ref{app:exterior-chessboard}, and $C_\chi$, $c$ fixed before the coupling. The regional scalar $S^\circ_{\xi,C}$ is retained inside the expectation and is not identified with the perimeter/corner coefficient here; the exponential is not replaced by its linear term unless its argument is bounded. Section~\ref{sec:one-step-insertion} reads this appendix at the retreated carrier $D(\Lambda)$ with the labelled weight (Section~\ref{sec:c5-6}, item (2) of its scope list); that reading is not carried out here, and Sections~\ref{sec:c4-2}--\ref{sec:c4-12} refer to the original law. The appendix shares the names $\varpi$, $\eta$, $C_{\mathrm{pin}}$, $K_\chi$ and $M(W)$ with Section~\ref{sec:c5-5}, which uses the same positive summation at $D(\Lambda)$; the objects here are those at $I$.

\subsection{Operand and retained normalisation}\label{sec:c4-1}
Use exactly the groups $W$ of Definition~\ref{def:groups}, the compatible families $\mathfrak B$, the closed pairings $A_\xi(\mathcal S)$ of \eqref{eq:part1-closed-family-pairing}, the scalar references $a_W$ of \eqref{eq:part1-reference-group}, the restricted reference sums $S^{\circ,[\mathfrak B]}_{\xi,C}$ and the joint defects $R_\xi(\mathfrak B)$ of Proposition~\ref{prop:joint-extraction}. Every source is a gauge-invariant closed contraction. Put
\begin{equation}\label{eq:c4-1-1}
    \mathscr R_\xi=\sum_{\substack{\mathfrak B\ne\varnothing\\\mathfrak B\ \mathrm{compatible}}}S^{\circ,[\mathfrak B]}_{\xi,C}R_\xi(\mathfrak B),\qquad
    E_{\mathrm{def}}=\frac{1}{\mathcal Z_0}\int\mathcal O\bigl[\mathsf w_\xi\mathbf 1_{A_{\mathrm{cov}}}\mathscr R_\xi\bigr](V)\,\dd V\;.
\end{equation}
The weight is the branch weight $\mathsf w_\xi=e^{c_\xi}I_{\xi;1}$ of \eqref{eq:c-collar-identity}, the outer operation $\mathcal O$ of \eqref{eq:native-source-explicit-outer-operation} contains the original cutoffs, $\zeta_\xi$ with its boundary-fluctuation dependence, the gauge and Haar factors, the Jacobians, the vacuum prefactor and the deferred integrations, $\mathcal Z_0=\int\mathcal O[\mathsf w_\xi]\,\dd V$, and $\mathbb E_{\mathrm h}$, $\mathbb P_{\mathrm h}$ are the history expectation and probability \eqref{eq:c3-6-1} for this positive weight; $A_{\mathrm{cov}}$ is the covered event of Lemma~\ref{lem:covered} (every contour bond is a bond of $\Omega_1$ and every free input of the contour lies in $I$). At fixed finite volume the signed sum \eqref{eq:c4-1-1} converges absolutely by Proposition~\ref{prop:joint-extraction}; no uniform absolute summability is inferred from that fact.

\subsection{Histories near the bad region}\label{sec:c4-2}
Let $B_\xi=\Lambda_1^c$ be the filled bad region and $E(B_\xi)$ the set of positive fine bonds with at least one endpoint in $B_\xi$. Let $\Gamma_C$ be the deterministic set of contour bonds and free-input templates of Section~\ref{sec:c3-7}, with $|\Gamma_C|\leq C_Ln_C$, $n_C$ the number of contour traversals; distances are those of the periodic fine-bond metric. For an integer $b\geq0$ define
\begin{equation}\label{eq:c4-2-1}
    \mathsf N_b=\{\xi\, | \,\operatorname{dist}(\Gamma_C,E(B_\xi))\leq b\}\;,
\end{equation}
with distance to the empty set infinite. This is a measurable history event; it changes neither the covered event nor the law. Write $E^{\mathrm{near}}_{\mathrm{def}}=\mathbb E_{\mathrm h}[\mathbf 1_{A_{\mathrm{cov}}}\mathbf 1_{\mathsf N_b}\mathscr R_\xi]$ and $E^{\mathrm{far}}_{\mathrm{def}}=\mathbb E_{\mathrm h}[\mathbf 1_{A_{\mathrm{cov}}}\mathbf 1_{\mathsf N_b^c}\mathscr R_\xi]$.

\begin{lemma}[near histories]\label{lem:c4-2-1}
Let $b=\lfloor LMR_1/16\rfloor$ and let $q\leq e^{-c_*\pi_*^2}$ be the one-point bound of Lemma~\ref{lem:c3-7-4} and Proposition~\ref{prop:c3-7-5}, on compatible even fine periods and for $g_0<g_*$. Then $|\mathscr R_\xi|\leq2$ pointwise on every branch, and
\begin{equation}\label{eq:c4-2-2}
    \mathbb P_{\mathrm h}(\mathsf N_b)\leq4C_Ln_C(2b+3)^4q,\qquad
    |E^{\mathrm{near}}_{\mathrm{def}}|\leq8C_Ln_C(2b+3)^4q\leq C'_Ln_Ce^{-(c_*/2)\pi_*^2}\;,
\end{equation}
the last inequality for $g_0$ below a threshold depending on $L$, $M$, the group and the source constants.
\end{lemma}

\begin{proof}
By \eqref{eq:part1-scalar-extraction}, $\mathscr R_\xi=F_\xi(0)-S^\circ_{\xi,C}f_\xi(0)$. Both $F_\xi(0)$ and $S^\circ_{\xi,C}$ are normalised integrals of a character of modulus at most one against the real positive kernels $K_{\xi;0}$ and $K^\circ_{\xi;0}$ (\eqref{eq:fixed-probe-centred-source}, \eqref{eq:part1-reference-gas}), and $|f_\xi(0)|\leq1$; hence $|\mathscr R_\xi|\leq2$. This bound is used only after the joint defects have been summed; it is not a bound on any $R_\xi(\mathfrak B)$, group or restricted reference factor. There are at most $4(2b+3)^4$ positive fine-bond labels within distance $b$ of a fixed fine bond (an overcount on short periods), so a union bound over $\Gamma_C$ and the one-point estimate $\mathbb P_{\mathrm h}(z\in E(B_\xi))=p_z\leq q$ of \eqref{eq:c3-7-1} give the first bound; positivity of $\mathsf w_\xi$ and $\mathcal O$, used only after the signed sum has been formed, and $|\mathscr R_\xi|\leq2$ give the second. For the last: $b=\lfloor LMR_1/16\rfloor$ exceeds every fixed source stencil for small $g_0$, and $\log(2b+3)=O(\log\log g_0^{-2})$ since $\ell=LMR_1$ grows as a fixed power of $\log g_1^{-2}$ (\eqref{eq:c5-3-1}), while $\pi_*^2\geq A_0^2(\frac12\log g_0^{-2})^{2p_0}$ with $p_0\geq10$ (proof of Proposition~\ref{prop:c3-7-5}); so $(2b+3)^4e^{-c_*\pi_*^2}\leq e^{-(c_*/2)\pi_*^2}$ for small $g_0$ at fixed source constants. The constants are uniform in the compatible even-period tori and the histories; no lower bound on a physical denominator is used, no conditional scalar is cancelled across histories, and no pointwise smallness of a Wilson-loop random variable is claimed.
\end{proof}

\subsection{The interior operand}\label{sec:c4-3}
The remaining operand is $E^{\mathrm{far}}_{\mathrm{def}}$, with the full signed group-family sum retained under its original weight. A group's random-field support is not its background support: its Wilson contraction carries the background transports along its contour interval $\mathcal H(W)$ as well. Every local flat comparison below includes these transports, in their order; a group meeting separated sides of the square is never flattened on its random support while the intervening transports are changed silently. The analytic step is to insert the background derivative of the closed source-containing selected integrals and of their joint vacuum ratio before taking absolute values or summing group families (Section~\ref{sec:c4-4}), and to sum the groups afterwards (Sections~\ref{sec:c4-6}, \ref{sec:c4-8} and~\ref{sec:c4-9}). The archived single straight-side estimate \draftref{attempt, eq:marked-background-curvature-payment} is evidence for the derivative mechanism at its interior-box scope only and is not an input: the derivative bounds used are those of Sections~\ref{sec:c4-7} and~\ref{sec:c4-10}.

\subsection{The joint signed selected-integral estimate}\label{sec:c4-4}
Fix a compatible root family $\mathcal A=\{D_1,\ldots,D_m\}$. For each $D_j$ use the selected measures $\Lambda^{\mathrm f}_{\xi;\ell_j}$ of \eqref{eq:probe-selection-measure} with $\ell_j=(\mathcal D_j,\mathsf J_j,\mathsf P_j,Z_j)$, $Z_j=D_j$ and $\mathsf J_j\ne\varnothing$; put $q_j=|\mathsf J_j|$ and $q=\sum_jq_j$. The centred measure $\widehat\nu^{\mathrm f}_{\xi,D}=\nu^{\mathrm f}_{\xi,D}-k^{\mathrm f}_\xi(D)\delta_{0,\mathsf L_D}$ of \eqref{eq:fixed-probe-zero-mass} is exactly the sum of the nonempty-probe selections of \eqref{eq:probe-selection-measure}: the empty-probe selections give the mass times $\delta_0$ and disappear under centring. This is the measure identity of Lemma~\ref{lem:probe-measures}; no new expansion is introduced. Define the finite-difference operator on a bounded function $f$ of the young variable by
\begin{equation}\label{eq:c4-4-1}
    \Delta_{\mathsf J}f(B)=\sum_{K\subseteq\mathsf J}(-1)^{|\mathsf J\setminus K|}f(\mathbf 1_KB)\;,
\end{equation}
every unselected young label being zero; for several roots compose these operators on their disjoint label sets, writing $\Delta_{\boldsymbol{\mathsf J}}f$. The integrand is a sum of closed Wilson contractions with the ordering and background transports retained; the source may carry a fixed complementary closed holonomy $h\in G$, transforming by conjugation at the base, and all bounds are uniform in $h$. With \eqref{eq:fixed-probe-active-pairing},
\begin{equation}\label{eq:c4-4-2}
    \mathfrak Q_\xi(\mathcal A;f)=\sum_{(\ell_j)_{j\leq m}\, | \,Z_j=D_j,\ \mathsf J_j\ne\varnothing}\int\Delta_{\boldsymbol{\mathsf J}}f(B)\,\dd\bigotimes_{j=1}^m\Lambda^{\mathrm f}_{\xi;\ell_j}(B_j)\;,
\end{equation}
the integral of each Dirac tensor $\bigotimes_{b\in\mathsf J}(\delta_{B_b}-\delta_0)$ against $f$ being the finite difference \eqref{eq:c4-4-1}.

\subsubsection*{The powers supplied by the signed source}\label{sec:c4-4-1}
Set $u=C_\chi g_0(1+r)$, increasing the fixed row/character constant $C_\chi$ once (Section~\ref{sec:c4-10-4}). On the real protected box the row reconstruction depends on $g_0B$ and has analytic derivative bounds on a larger fixed phase chart (Lemma~\ref{lem:charts}, Lemma~\ref{lem:c2-uniform-chart}). Each selected free label affects a bounded number of reconstructed contour links, each link has a bounded input set, and for the square the traversal multiplicity is bounded; applying the product rule inside the closed character therefore gives $C_\chi^q$ derivative assignments, not $n_C^q$ or $q!$. Derivative orders on any one row are bounded by twice its fixed input count plus one, including the remainders below; the higher row derivatives are obtained from the analytic phase map on its larger fixed ball by Cauchy estimates (Lemma~\ref{lem:c2-uniform-chart}(iii)), and the maximum order used is fixed by $L$. All untouched transports are unitary matrices inside the same closed contraction. The mixed integral remainder formula \eqref{eq:c4-10-7} gives
\begin{equation}\label{eq:c4-4-3}
    \sup|\Delta_{\boldsymbol{\mathsf J}}f|\leq u^q\;.
\end{equation}

For a root with odd $q_j$ take the homogeneous term of degree $q_j$ in its selected variables $B_{D_j}$, the other root variables fixed; it is odd under $B_{D_j}\to-B_{D_j}$, and the difference from it carries an additional factor $u$ (\eqref{eq:c4-10-9}; the choice of the extra increment is bounded by $q_j\leq2^{q_j}$, absorbed in $C_\chi$). The same holds simultaneously for any set of odd roots, the product-rule allocation count remaining exponential in $q$. Every term is a closed contraction; no open interval is estimated separately. Each selected Gaussian kernel \eqref{eq:fixed-kernel-density} with its cutoffs is invariant under $(B_{D_j},X_{D_j})\to(-B_{D_j},-X_{D_j})$ once its ordinary Mayer factors are removed: the determinant, the quadratic cross term, the compensator, the real cutoffs $\chi_b$, $1-\chi_b$ and the spatial Cauchy integrations are even. The tensor product in \eqref{eq:c4-4-2} gives separate integration variables and a separate reversal for each root. Thus the leading odd part integrates to zero in the signed selected integral, also when several roots are present.

Let $\omega(g_0)=C_0^{\partial}g_0(1+r)^3$ with the host derivative constant $C_0^{\partial}\geq C_0$ of Section~\ref{sec:c4-7-1}, let $\omega_*$ be the fixed host budget of \eqref{eq:native-source-vacuum-KP-budget}, and put $R_\Upsilon=\omega_*/(2\omega(g_0))$; choose $g_0$ so that $R_\Upsilon\geq2$. In root $j$ multiply the selected ordinary potentials $\mathbf V_\xi(Y)$, $Y\in\mathcal D_j$, by an independent complex parameter $\zeta_j$, $|\zeta_j|\leq R_\Upsilon$, leaving the Gaussian kernel, cutoffs and probes unchanged. If $\mathcal D_j\ne\varnothing$ the selected integral vanishes at $\zeta_j=0$ (each Mayer factor $\int_0^1\zeta\mathbf V e^{t\zeta\mathbf V}\dd t=e^{\zeta\mathbf V}-1$ does), so the Cauchy difference between $\zeta_j=0$ and $\zeta_j=1$ of the analytic function of $\zeta_j$ costs at most $2/(R_\Upsilon-1)$ times its supremum on the disc; if $\mathcal D_j=\varnothing$ the density is the even Gaussian/cutoff kernel and the reversal applies. Independent parameters on disjoint roots fit the same local potential budget simultaneously (Section~\ref{sec:c4-7-1}). Therefore an odd $q_j$ costs
\begin{equation}\label{eq:c4-4-4}
    v=u+\frac{2}{R_\Upsilon-1}\;.
\end{equation}
No separate cancellation of a group coefficient is assumed; the cancellations occur inside the original signed selected integrals. Both $u$ and $v$ tend to zero at their displayed coupling rates.

\subsubsection*{Numerical majorants paid with the same Gaussian reserve}\label{sec:c4-4-2}
For a selected root $\ell$ define
\begin{equation}\label{eq:c4-4-5}
    M_\ell=\sup_{|\zeta|\leq R_\Upsilon}\|\Lambda^{\mathrm f}_{\xi;\ell,\zeta}\|_{\mathrm{TV}}\;,
\end{equation}
where $\Lambda^{\mathrm f}_{\xi;\ell,\zeta}$ is the measure \eqref{eq:probe-selection-measure} with each selected ordinary potential replaced by $\zeta$ times that potential; the cutoffs, Gaussian density and normalisers, compensator, integration carriers, weakening contours and seed data are unchanged. The total variation is a numerical majorant used after the signed source cancellation; it is not a bound on the centred Dirac tensors.

\begin{lemma}[dummy comparison]\label{lem:c4-4-1}
There are at most $P_M=4(4M+3)^4$ probe labels with a given host, and each probe host $Y_b$ has $N_0(Y_b)\leq s_{\mathrm p}=5^4$ cubes (\eqref{eq:c-probe-host}). Choose once, after $M$ and before $g_0$,
\begin{equation}\label{eq:c4-4-6}
    u_*=\min\Bigl(\frac14,\ \frac{\omega_*e^{-\kappa s_{\mathrm p}}}{8P_M}\Bigr)\;.
\end{equation}
Then for every connected final domain $D$, with $m(D)=\varepsilon_*e^{-\lambda_*\ell_1(D)}$ the majorant of Lemma~\ref{lem:activity-bounds},
\begin{equation}\label{eq:c4-4-7}
    \sum_{\ell\, | \,Z(\ell)=D,\ \mathsf J(\ell)\ne\varnothing}u_*^{q(\ell)}M_\ell\leq m(D)\;.
\end{equation}
\end{lemma}

\begin{proof}
The number $u_*$ is a fixed comparison weight, not a measure. For every probe label $b$ insert, in the numerical comparison only, the dummy potential $p^+_b=u_*$ on its protected host box and zero outside; its selected Mayer factor $e^{u_*}-1$ is at least $u_*$. The summed dummy potential at a host is at most $P_Mu_*\leq\omega_*e^{-\kappa d_0(Y)}/8$ (as $d_0(Y)\leq s_{\mathrm p}$ for a probe host), while the complex ordinary potentials use at most half the budget $\omega_*e^{-\kappa d_0(Y)}$ on $|\zeta|\leq R_\Upsilon$ (Lemma~\ref{lem:c2-potential-size} and $R_\Upsilon\omega(g_0)=\omega_*/2$). Split the labels with a common host exactly as in the proof of Lemma~\ref{lem:probe-measures}; the seeds, conditioning carrier and Gaussian kernel depend on the active hosts only and are unchanged. Sum all split selections with the same active-host set first: Lemma~\ref{lem:c4-7-1} proves that their many-to-one positive sum is dominated hostwise by the undifferentiated majorant \eqref{eq:fixed-kernel-selected-majorant}. That majorant pays its determinant and compensator with the Gaussian reserve $\alpha_G$ (Lemma~\ref{lem:gaussian-payment}(ii)), and the cover and seed sums \eqref{eq:native-source-initial-domain-sum}, \eqref{eq:native-source-enlarged-domain-sum} with the final $Y'$-sum in the proof of Lemma~\ref{lem:activity-bounds} (Appendix~\ref{app:background-estimates}) sum the seeds and final domains to $m(D)$. All parameters in $m(D)$ are the existing positive-majorant parameters; a fixed decrease of the remaining decay is allowed when polynomial factors are inserted in Sections~\ref{sec:c4-7} and~\ref{sec:c4-8}. Nothing is changed in the physical potential or in a normalisation of $E_{\mathrm{def}}$.
\end{proof}

\begin{lemma}[joint selected-integral bound]\label{lem:c4-4-2}
Let $f$ be a normalised character of an ordered closed reconstructed word, optionally closed with its inverse background interval and a fixed complementary $h$ (Section~\ref{sec:c4-7-2}). For $g_0$ small enough that $u\leq u_*$ and $v\leq1$, put
\begin{equation}\label{eq:c4-4-8}
    \rho=\Bigl(\frac{u}{u_*}\Bigr)^2+\frac{u}{u_*}\,v\;.
\end{equation}
Then for every compatible root family $\mathcal A$ and every choice of selections $(\ell_j)$ with $\mathsf J_j\ne\varnothing$,
\begin{equation}\label{eq:c4-4-9}
    \Bigl|\int\Delta_{\boldsymbol{\mathsf J}}f(B)\,\dd\bigotimes_{j=1}^m\Lambda^{\mathrm f}_{\xi;\ell_j}(B_j)\Bigr|\leq\prod_{j=1}^mu^{q_j}v^{q_j\bmod2}M_{\ell_j},\qquad
    |\mathfrak Q_\xi(\mathcal A;f)|\leq\prod_{D\in\mathcal A}\rho\,m(D)\;.
\end{equation}
\end{lemma}

\begin{proof}
The first bound combines the reversal, the Cauchy differences and \eqref{eq:c4-4-3}--\eqref{eq:c4-4-4} as written out in Section~\ref{sec:c4-7-2}: the roots with odd $q_j$ and empty ordinary selection lose their leading odd part to the even kernel and keep the remainder $u^{q_j+1}$, the roots with odd $q_j$ and nonempty ordinary selection pay $u^{q_j}\cdot2/(R_\Upsilon-1)$ by the Cauchy difference in $\zeta_j$ (the supremum on the disc being $u^{q_j}M_{\ell_j}$ by \eqref{eq:c4-4-5}), the roots with even $q_j$ pay $u^{q_j}M_{\ell_j}$. The bound retains the full joint source through each cancellation. For every nonempty probe set $(u/u_*)^{q_j}v^{q_j\bmod2}\leq\rho$ ($q_j=1$ gives $(u/u_*)v$, $q_j\geq2$ gives $(u/u_*)^2$). Summing over the selections of every root with \eqref{eq:c4-4-2} and \eqref{eq:c4-4-7} gives the second bound.
\end{proof}

The gain is $\rho=O(g_0^2(1+r)^4)$ with constants fixed before the coupling; it is obtained after the signed integration, not by replacing a probe tensor by its total variation $2^{|\mathsf J|}$.

\subsubsection*{Background derivative and the joint vacuum ratio}\label{sec:c4-4-3}
For the flat subtraction take a real background direction $\omega$ along one of the globally small analytic extensions of Section~\ref{sec:c4-9-1}; the geometry, carriers, cutoff norm, means, Gaussian reserve and walk recipe are unchanged. Let $L_f$ be the number of occurrences of contour background links in the closed word whose local coefficient arguments vary; when a group's relative interval is compared this includes the interval and its inverse closing transport. Complementary closed holonomies are held fixed, and no outer history variable or physical weight is differentiated. Write $\mathscr D_\omega$ for this derivative.

\begin{lemma}[one background derivative]\label{lem:c4-4-3}
On the extensions of Section~\ref{sec:c4-9-1}, with $\rho$, $m(D)$ of Lemma~\ref{lem:c4-4-2} and a constant $C$ fixed before the coupling,
\begin{equation}\label{eq:c4-4-10}
    |\mathscr D_\omega\mathfrak Q_\xi(\mathcal A;f)|\leq C\|\omega\|_\infty\Bigl(L_f+\sum_{D\in\mathcal A}N_1(D)\Bigr)\prod_{D\in\mathcal A}\rho\,m(D)\;.
\end{equation}
\end{lemma}

\begin{proof}
The derivative of the selected Gaussian factors (density, normaliser, compensator) inserts a scalar polynomial of degree at most two in $(B,X)$, including the determinant trace; its moment is paid by the joint coercive Gaussian bound of Section~\ref{sec:c4-10-3} at cost $CN_1(D)\|\omega\|_\infty$. Differentiated walk coefficients sum in the convergent differentiated series of Section~\ref{sec:c4-10-2}. The derivative of a host Mayer $t$-integrand is $\zeta(\mathscr D_\omega\mathbf V)e^{t\zeta\mathbf V}(1+t\zeta\mathbf V)$, whose $t$-integral $\zeta(\mathscr D_\omega\mathbf V)e^{\zeta\mathbf V}$ vanishes at $\zeta=0$; its size is bounded by the differentiated host comparison of Lemma~\ref{lem:c4-7-1}. A Gaussian derivative is even under each component reversal and the leading source derivative has the parity of the undifferentiated term (\eqref{eq:c4-10-10}), so the signed powers of Section~\ref{sec:c4-4-1} survive one derivative, with the additional factor $C\|\omega\|_\infty(L_f+\sum_DN_1(D))$: the source derivative contributes $L_f$ plus the number of selected labels, the latter at most $4(LM+1)^4\sum_DN_1(D)$ (Section~\ref{sec:c4-7-1}), and the host, Gaussian and walk derivatives contribute one factor $N_1(D)$ each by Lemma~\ref{lem:c4-7-1}. No division by a potential, activity or character is used. The factor $N_1(D)$ is kept explicitly; it is paid by $m(D)$ in Section~\ref{sec:c4-7}.
\end{proof}

The vacuum ratio is kept as the joint ratio of the whole root family, not a product of one-root ratios: by \eqref{eq:fixed-probe-active-pairing} and \eqref{eq:part1-joint-vacuum-exponential},
\begin{equation}\label{eq:c4-4-11}
    q_\xi(\mathcal A)=\exp\Bigl[-\sum_{\mathfrak c\text{ hits }\mathcal A}\Phi^{\mathrm v}_\xi(\mathfrak c)\Bigr]\;,
\end{equation}
a cluster hitting several roots being counted once, and its derivative is the derivative of this exponential.

\begin{lemma}[the joint ratio and its derivative]\label{lem:c4-4-4}
With the constant $C_M$ of Lemma~\ref{lem:c4-7-1},
\begin{equation}\label{eq:c4-4-12}
    |q_\xi(\mathcal A)|\leq e^{\sum_{D\in\mathcal A}N_1(D)/8},\qquad
    |\mathscr D_\omega q_\xi(\mathcal A)|\leq\frac{C_M}{2}\|\omega\|_\infty\sum_{D\in\mathcal A}N_1(D)\,e^{\sum_{D\in\mathcal A}N_1(D)/8}\;,
\end{equation}
and consequently
\begin{equation}\label{eq:c4-4-13}
    \bigl|\mathscr D_\omega[q_\xi(\mathcal A)\mathfrak Q_\xi(\mathcal A;f)]\bigr|\leq C\|\omega\|_\infty\Bigl(L_f+\sum_{D\in\mathcal A}N_1(D)\Bigr)\prod_{D\in\mathcal A}\bigl[\rho\,m(D)e^{N_1(D)/8}\bigr]\;.
\end{equation}
\end{lemma}

\begin{proof}
The first bound is Lemma~\ref{lem:vacuum-clusters}. The second is Lemma~\ref{lem:c4-7-4}, which differentiates one vacuum activity in its connected-cluster tree majorant, keeping every occurrence and symmetry factor and marking the single derivative in the fixed positive cluster majorant, without shrinking a previously chosen parameter or dividing by an activity. The third follows from the product rule with Lemmas~\ref{lem:c4-4-2} and~\ref{lem:c4-4-3}, the polynomial $\sum_DN_1(D)$ being absorbed in the unused domain decay of $m(D)$ (Section~\ref{sec:c4-8-2}).
\end{proof}

The actual joint ratio is differentiated before estimating. The normaliser $I_{\xi;0}$ encoded by this ratio is not cancelled against the physical history factor $\mathsf w_\xi=e^{c_\xi}I_{\xi;1}$.

\subsection{The closed group subtraction and its signed caller}\label{sec:c4-6}
\begin{remark}[what the subtraction must pay]\label{rem:c4-5-1}
Section~\ref{sec:c4-4} supplies the derivative estimate when the flat subtraction of each closed group is made inside $\mathscr R_\xi$. The group-family summation (this section and Sections~\ref{sec:c4-8}, \ref{sec:c4-9}) must pay the overlap of contour intervals and the spatial decorations, and must control the restricted reference sums $S^{\circ,[\mathfrak B]}_{\xi,C}$ with their regional flat kernel; no product of one-component ratios and no uncontrolled exponential in the loop length is admissible. The group contraction for this caller uses the interval transport relative to its background interval, closed back to its base, with an arbitrary complementary closed holonomy $h$; its flat value is $a_W\chi(h)$ by Lemma~\ref{lem:schur}. The product bound for such closed contractions is the finite-dimensional norm equivalence of Lemma~\ref{lem:c4-6-1}; no independent open matrix norm is an inductive carrier, and the multi-group factorisation is checked against \eqref{eq:part1-closed-family-pairing}, not presumed from spatial independence of the physical law.
\end{remark}

\emph{Geometry.} The square/torus geometry of Section~\ref{sec:extent-weights} is in force: $C$ is a coarse square of side $s=nL$ fine bonds on fine periods $LK_i$ with $K_i\geq3(n+2)$, and $n_C=4s$. No loop separation hypothesis is added. Contour hull length is paid by connected spatial extent as in \eqref{eq:marginal-hull-extent}: contacts of diameter $<s/2$ occupy one side or two adjacent sides and fit in an arc of length at most $4\operatorname{diam}+1$; otherwise $n_C\leq8\operatorname{diam}$. Periodic distances between square contacts equal their lifted distances.

For a group $W$ let $n(W)$ be the sum of $N_1$ over its roots and over every constituent domain of every occurrence in its cluster list, with multiplicities, and define
\begin{equation}\label{eq:c4-6-1}
    \mathfrak s(W)=n(W)+\frac{|\mathcal H(W)|}{LM}\;.
\end{equation}
The footprint $F(W)$ is the set of $LM$-cubes meeting a constituent domain, its fixed coefficient stencil halo, or the contour/free-input stencil of a traversal of $\mathcal H(W)$; the source geometry gives $|F(W)|\leq C\mathfrak s(W)$. For a component of the roots/cluster-occurrence graph the union of its domains is wall connected, so its diameter is at most $CLM$ times its cube count, and its contact hull is bounded by the square estimate above; overlapping hulls have a connected interval union, which pays the hull of a group by the sum of its component counts. If all components are merged because some hull is long (Section~\ref{sec:joint-extraction}), the sum of the component sizes in that class is at least $cn_C/(LM)$. Hence $|\mathcal H(W)|/(LM)\leq Cn(W)$. Coefficients whose local rectangle fails to lift are kept in the large-domain class of Section~\ref{sec:c4-8-4}.

\subsubsection*{The closed relative interval functional}\label{sec:c4-6-1}
For $W$ use its root variables only, every other young variable zero, in the reconstructed links along $\mathcal H(W)$. Let $T_W(a;U_1)$ be the ordered product of these links (the interval transport) and $P_W(U_1)$ the same product at zero young variable, both with their source orientations and with the same two endpoint vertices. The relative product $T_W(a;U_1)P_W(U_1)^{-1}$ is based and closed at the initial vertex. Define the scalar closed contraction
\begin{equation}\label{eq:c4-6-2}
    c_W(U_1;h)=w_\xi(W)\int\chi\bigl(T_W(a;U_1)P_W(U_1)^{-1}h\bigr)\,\dd\Bigl(\bigotimes_{D\in\mathcal A(W)}\widehat\nu^{\mathrm f}_{\xi,D}\Bigr)(a)\;,
\end{equation}
$h\in G$ a complementary closed holonomy at that base, transforming by simultaneous conjugation; the product $T_WP_W^{-1}$ and $h$ transform at one base, so the displayed scalar is gauge invariant and no open interval functional is estimated. Put
\begin{equation}\label{eq:c4-6-3}
    d_W(U_1;h)=c_W(U_1;h)-a_W\chi(h),\qquad\mathfrak d_W(U_1)=\sup_{h\in G}|d_W(U_1;h)|\;.
\end{equation}
At the reference data $c_W(\id;h)=a_W\chi(h)$ by Lemma~\ref{lem:schur} (there $T_W=P^\circ_W$ and $P_W=\id$). The weights and measures in $c_W$ are those of the joint extraction, including every cluster occurrence of the group; they are not a newly normalised conditional law.

\begin{lemma}[factorisation and product inequality]\label{lem:c4-6-1}
Let $\pi$ be the irreducible unitary representation with $\chi=\dim(\pi)^{-1}\operatorname{tr}\pi$. (a) There is a constant $K_\chi$ of the character such that $\|\Upsilon\|_{\mathrm{op}}\leq K_\chi\sup_{h\in G}|\dim(\pi)^{-1}\operatorname{tr}(\Upsilon\pi(h))|$ for every $\Upsilon\in\operatorname{End}(V_\pi)$. (b) For a compatible family $\mathfrak B=\{W_1,\ldots,W_m\}$ on a covered branch, $R_\xi(\mathfrak B)$ is the normalised trace of the ordered product of the matrices $\Upsilon_{W_j}G_j$, where $\Upsilon_W=w_\xi(W)\int\pi(T_WP_W^{-1})\,\dd\bigotimes\widehat\nu^{\mathrm f}_\xi-a_W\id$ and $G_j$ is the background transport of the gap after $\mathcal H(W_j)$ composed with $P_{W_j}$. (c) Consequently
\begin{equation}\label{eq:c4-6-4}
    |R_\xi(\mathfrak B)|\leq\prod_{W\in\mathfrak B}K_\chi\mathfrak d_W(U_1)\;.
\end{equation}
\end{lemma}

\begin{proof}
(a) $\Upsilon\mapsto(h\mapsto\operatorname{tr}(\Upsilon\pi(h)))$ is linear and injective on $\operatorname{End}(V_\pi)$, since $\pi(G)$ spans $\operatorname{End}(V_\pi)$ for an irreducible representation (Burnside); so the supremum over $h$ is a norm on the finite-dimensional space $\operatorname{End}(V_\pi)$, equivalent to the operator norm, and $K_\chi$ is the equivalence constant. (b) In a compatible family a traversal of $\mathcal H(W)$ has no contact with a root of a different group (that contact hull would meet $\mathcal H(W)$), so its reconstructed link uses the root variables of $W$ only (Lemma~\ref{lem:row-locality}); a traversal outside every interval has its background link. Number the groups in cyclic order and start the ordered link product at the first traversal of $\mathcal H(W_1)$ (cyclicity of the trace). Expanding $\prod_j(X_j-a_{W_j}\id)$ with $X_j=w_\xi(W_j)\int\pi(T_{W_j}P_{W_j}^{-1})\dd\bigotimes\widehat\nu^{\mathrm f}$ over subsets $\mathcal S$ of slots, a slot of the first kind contributes the links of $\mathcal H(W_j)$ at the root variables followed by the gap transport, a slot of the second kind contributes $-a_{W_j}$ times the links of $\mathcal H(W_j)$ at zero young variable followed by the gap; by multilinearity of the trace and Fubini over the product measure (as in the proof of Lemma~\ref{lem:schur}) the normalised trace of the term of $\mathcal S$ is $(\prod_{W\notin\mathcal S}(-a_W))\,(\prod_{W\in\mathcal S}w_\xi(W))\,\mathfrak Q_\xi(\mathcal A(\mathcal S);f_\xi)=(\prod_{W\notin\mathcal S}(-a_W))A_\xi(\mathcal S)$ by \eqref{eq:part1-closed-family-pairing}, since on a covered branch the links outside the intervals are the background links at $U_1$ (Lemma~\ref{lem:covered}). Summing over $\mathcal S$ reproduces \eqref{eq:part1-joint-defect}. This is an algebraic factorisation of the existing polymer integrals, not independence of physical field regions. (c) $|\operatorname{tr}(Y_1\cdots Y_{2m})|\leq\dim(\pi)\prod\|Y_i\|_{\mathrm{op}}$, the gap transports are unitary, and $\|\Upsilon_W\|_{\mathrm{op}}\leq K_\chi\mathfrak d_W(U_1)$ by (a), since $\dim(\pi)^{-1}\operatorname{tr}(\Upsilon_W\pi(h))=d_W(U_1;h)$. Matrices are used to prove the finite-dimensional multilinear identity; no separately estimated endpoint-covariant matrix or open Wilson carrier is introduced.
\end{proof}

\subsubsection*{Positive graph sums for the reference factors}\label{sec:c4-6-2}
This is the summation with the estimates of Sections~\ref{sec:c4-4} and~\ref{sec:c4-7}; it concerns the source-containing groups, not the vacuum gas alone. A cluster occurrence $\mathfrak c$ has cube cost $n(\mathfrak c)=\sum_{D\in\mathfrak c}N_1(D)$; its positive weight $M_v(\mathfrak c)$ is the tree majorant of its Ursell coefficient: for the ordered tuple defining $\mathfrak c$, divide by the tuple factorial and sum over the incompatibility spanning trees, multiplying the majorants $m(D)$ of the activities (the positive tree sum of the proof of Lemma~\ref{lem:vacuum-clusters}, Section~\ref{app:kp}). Source roots have the weights $\rho\,m(D)$ of Lemma~\ref{lem:c4-4-2}. For each $W$ the product of its root weights, its cluster weights $M_v(\mathfrak c_j)$ and $1/k(W)!$ is denoted $M(W)$; it bounds $|a_W|$, $|w_\xi(W)|\prod_D\|\widehat\nu^{\mathrm f}_{\xi,D}\|$ after the signed integration, and the undifferentiated closed source functional $|c_W(U_1;h)|$, the physical and reference data having the same numerical majorant (Lemma~\ref{lem:c2-reference}).

\begin{lemma}[positive group sums]\label{lem:c4-6-2}
Choose $\eta>0$ after the fixed geometry and forest decay constants, as in Section~\ref{sec:c4-8-2} ($1000\eta A_{\mathrm s}<\varpi/8$ there). Under the smallness conditions $C\rho LM\leq\eta/8$ and the root-incidence bound of Section~\ref{sec:c4-8-2}, which hold for $g_0$ small with constants fixed before the coupling and independent of the loop length,
\begin{equation}\label{eq:c4-6-5}
    \sup_{n\in\mathcal I_C}\sum_{W\, | \,n\in\mathcal H(W)}M(W)e^{4\eta\mathfrak s(W)}+\sup_{\Delta\in\pi_1}\sum_{W\, | \,\Delta\in F(W)}M(W)e^{4\eta\mathfrak s(W)}\leq C_{\mathrm{pin}}\rho\;,
\end{equation}
where $\mathcal I_C$ is the set of contour traversals; the bound holds in the form ``$\leq C_{\mathrm{pin}}\rho$ for every $\rho$ below the threshold'', the conditions being monotone in $\rho$. For footprint contact, wall adjacency and corner contact are included (Section~\ref{sec:c4-12-4}).
\end{lemma}

\begin{proof}
This is the combinatorial payment of Sections~\ref{sec:c4-8-2} and~\ref{sec:c4-8-3}; its structure is as follows. First form the connected components of the roots/cluster-occurrence graph before hull merging. The factorials are the exponential-generating factorials of these objects: roots form an unordered distinct family and cluster occurrences carry $1/k!$. Dropping the compatibility constraints is an upper bound, and a connected graph indicator is at most its sum of incompatibility spanning trees. For a root node $D$ the incident vacuum nodes have weighted mass at most $N_1(D)/8$ by the pinned vacuum estimate \eqref{eq:c2-pinned-vacuum}; for a vacuum node $\mathfrak c$ the same estimate summed over its constituents gives $n(\mathfrak c)/8$; the added source-root mass is at most $C\rho$ times the same cost by the animal sum \eqref{eq:native-source-animal-sum} and Lemma~\ref{lem:c4-4-2}, hence at most that cost$/8$ for small $g_0$. The two-species positive tree recursion is thus bounded with node cost one quarter of the cube cost: if $t_v$ is a node weight and $a_v$ its cost, the iterates $T^{(k+1)}_v=t_v\exp(\sum_{v'\sim v}T^{(k)}_{v'})$ satisfy $T^{(k)}_v\leq t_ve^{a_v}$, because $\sum_{v'\sim v}t_{v'}e^{a_{v'}}\leq a_v$, and their monotone limit sums the rooted trees. This pays the vacuum decorations and leaves a factor $\rho$ for a component with a marked root. The same recursion pays the polynomial loss when a component is pinned at a point of its hull rather than at a contact: the hull length is bounded by the spatial extent, so a root lies within $CLM$ times the cube cost of that point, and the root locations and the polynomial in the cube count are absorbed by the unused exponential decay; a spatial footprint pin is handled by a tree path from the marked root to the pinned cube, and the square has bounded local traversal density, so the sum over source contacts weighted by that distance is uniform in $n_C$. Then merge the components whose hull intervals overlap, summing the connected-overlap indicators by interval spanning trees with the same recursion: a hull $\mathcal H$ meets components of total weighted mass at most $C\rho|\mathcal H|$, its node cost contains $\eta|\mathcal H|/(LM)$, and $C\rho LM\leq\eta/8$ pays the branching; the weighted union size is at most the sum of the component sizes, and the exponential-generating factorials agree with the interleavings of the cluster lists exactly as in Lemma~\ref{lem:grouped-source}. The exceptional merge (a long hull merges every remaining component into the whole-contour group) is paid in Lemma~\ref{lem:c4-8-3}: a long class costs at least $cn_C/(LM)$ in the sum of its component sizes, the arbitrary remaining components cost at most $e^{C\rho n_C}$, and at small $g_0$ this is absorbed into a fraction of the long-class decay, not left as a loop-length factor. Lemmas~\ref{lem:c4-8-2} and~\ref{lem:c4-8-3} carry out these steps with the explicit weights.
\end{proof}

\begin{lemma}[the reference group gas]\label{lem:c4-6-3}
Put $\mathfrak a_W=\eta\mathfrak s(W)$. Under Lemma~\ref{lem:c4-6-2}, for every group $W$,
\begin{equation}\label{eq:c4-6-6}
    \sum_{W'\not\sim W}|a_{W'}|e^{\mathfrak a_{W'}}\leq C\rho\bigl(|F(W)|+|\mathcal H(W)|\bigr)\leq\frac18\mathfrak a_W
\end{equation}
after choosing $g_0$ small, every constant fixed before the coupling and independently of the loop length. Hence the reference group gas \eqref{eq:part1-reference-gas} has a convergent connected-cluster logarithm, $S^\circ_{\xi,C}\ne0$, and for every compatible family $\mathfrak B$
\begin{equation}\label{eq:c4-6-7}
    \Bigl|\frac{S^{\circ,[\mathfrak B]}_{\xi,C}}{S^\circ_{\xi,C}}\Bigr|\leq\exp\Bigl(\frac18\sum_{W\in\mathfrak B}\mathfrak a_W\Bigr)\;.
\end{equation}
\end{lemma}

\begin{proof}
Incompatibility of $W$ and $W'$ means contact of their footprints or overlap of their intervals, so the two pin sums \eqref{eq:c4-6-5} (with $|a_{W'}|\leq M(W')$ and $e^{\mathfrak a_{W'}}\leq e^{4\eta\mathfrak s(W')}$) give the first inequality of \eqref{eq:c4-6-6}, and $|F(W)|+|\mathcal H(W)|\leq CLM\mathfrak s(W)$ with $C\rho LM\leq\eta/8$ gives the second. This is the Kotecký--Preiss criterion for the species $W$ with activities $a_W$ and costs $\mathfrak a_W$; the pinned-tree argument of Section~\ref{app:kp} gives the convergent logarithm and the exclusion identity, whose countable-species form is Lemma~\ref{lem:c4-9-2}. The restricted ratio is the single joint exclusion ratio of that gas, and the pinned cluster estimate counts each cluster hitting $\mathfrak B$ once, giving \eqref{eq:c4-6-7}. There is no product-of-ratios assertion; this is the step that prevents a factor $e^{C\rho n_C}$ from replacing the flat scalar in $E_{\mathrm{def}}$.
\end{proof}

\subsubsection*{Subtraction and its curvature payment}\label{sec:c4-6-3}
For a group $W$ its local comparison box $Q_W$ contains every constituent domain's coefficient halo and every background transport along $\mathcal H(W)$, including the inverse interval used to close the source; its lifted side is at most $CLMn(W)$ (Section~\ref{sec:c4-8-4}). For the good interior boxes of Section~\ref{sec:c4-8-4}, contained in $\Lambda_1$ and disjoint from $S_1$, root a tree gauge at the base of the complementary holonomy. The ordered plaquette filling of Lemma~\ref{lem:c4-10-5} gives a phase bound $C\operatorname{diam}(Q_W)^2\delta_{Q_W}(U_1)$, where $\delta_Q(U)$ is the maximum plaquette deviation $|U(\partial p)-\id|_\sigma$ over the plaquettes of $Q$. The source is a closed contraction throughout. Lemma~\ref{lem:c4-4-4} applied to this coefficient, with its cluster list and the whole relative interval retained, costs $n(W)+|\mathcal H(W)|$ and the factor $\rho$ for each marked root; integrating the real phase path from the flat projection to $U_1$ (Lemma~\ref{lem:c4-9-1}) gives $\mathfrak d_W\leq C\delta_{Q_W}\operatorname{diam}(Q_W)^2$ times that polynomial times $M(W)$, with slightly reduced domain decay. If the phase bound exceeds the fixed interpolation chart, the two undifferentiated endpoint bounds give the same inequality with a larger constant (Section~\ref{sec:c4-12-2}). No $g_0$-dependent restriction on the group size is added.

The regional carrier $I$ is retained in the reference coefficient. The comparison is used only for groups whose box, with every coefficient and source halo, lies in $\Lambda_1$ and misses $S_1$; boxes crossing that integration boundary are kept in the large-domain class and are not interpolated, which leaves the target unchanged because their full contribution is paid by the tail below. On an interior box the centred kernel depends on the branch fields only through $U_1$ there: the retained field and the boundary change are absent from its source rows and primitive arguments, and $V_0$ enters only through that background (Section~\ref{sec:c4-8-1}). On far histories $\operatorname{dist}(\Gamma_C,E(\Lambda_1^c))>b$, and Section~\ref{sec:c4-8-4} uses the good comparison only when $n(W)<b/(4C_{\mathrm{box}}LM)$, which places every required stencil in an interior lifted box; all other groups keep both endpoint coefficients and the undifferentiated estimate, and the reserved exponential pays this tail.

\begin{lemma}[the group pin sum]\label{lem:c4-6-4}
On covered far histories, with $\varepsilon_1=g_1p_0(g_1)$, $b=\lfloor LMR_1/16\rfloor$ and constants $C_\chi$, $c$ fixed before the coupling,
\begin{equation}\label{eq:c4-6-8}
    \sum_WK_\chi\mathfrak d_W(U_1)e^{\mathfrak a_W/8}\leq C_\chi n_C\rho\bigl(\varepsilon_1+e^{-cb/(LM)}\bigr)\;.
\end{equation}
\end{lemma}

The proof is Section~\ref{sec:c4-12-2}, from the local estimate of Section~\ref{sec:c4-8-4} and the pins of Lemma~\ref{lem:c4-6-2}. The polynomial factors $n(W)^k$, the squared box size and the interval length are paid by the reserved domain decay, not placed in a loop-dependent constant.

\subsubsection*{The signed integrated bound}\label{sec:c4-6-4}
\begin{lemma}[the family sum]\label{lem:c4-6-5}
On covered far histories,
\begin{equation}\label{eq:c4-6-9}
    |\mathscr R_\xi|\leq|S^\circ_{\xi,C}|\Bigl[\exp\Bigl(C_\chi n_C\rho\bigl(\varepsilon_1+e^{-cb/(LM)}\bigr)\Bigr)-1\Bigr]\;.
\end{equation}
\end{lemma}

\begin{proof}
Use the sum \eqref{eq:c4-1-1}: absolute values are taken only after the flat subtraction has been made in each $R_\xi(\mathfrak B)$ and the joint reference ratio \eqref{eq:c4-6-7} has been retained. By \eqref{eq:c4-6-4} and \eqref{eq:c4-6-7}, $|S^{\circ,[\mathfrak B]}_{\xi,C}R_\xi(\mathfrak B)|\leq|S^\circ_{\xi,C}|\prod_{W\in\mathfrak B}K_\chi\mathfrak d_W(U_1)e^{\mathfrak a_W/8}$, and the sum over nonempty compatible families is bounded by the exponential series of the one-group sum \eqref{eq:c4-6-8} minus its zeroth term. The restricted reference sums, not a new vacuum normalisation, supply the factor $|S^\circ_{\xi,C}|$; at no stage is $\mathsf w_\xi$ cancelled across histories. The countable-group limit is Lemma~\ref{lem:c4-9-2}.
\end{proof}

Together with Lemma~\ref{lem:c4-2-1} this gives the first form of the defect bound, \eqref{eq:c4-12-7} below, with $\rho$ of \eqref{eq:c4-4-8} and all physical history weights and $\mathcal Z_0$ retained. It leaves the regional scalar $S^\circ_{\xi,C}$ inside the expectation; the identification of that scalar with the perimeter/corner coefficient is Appendix~\ref{app:regional-scalar} at the carrier $I$ and Section~\ref{sec:c5-7} at the retreated carrier, and is not part of this appendix. The reconstructed fine background loop is not replaced by the coarse loop.

\subsection{The joint kernel payment}\label{sec:c4-7}
This section supplies the quantitative steps used in Section~\ref{sec:c4-4}; it adds no assumption on $E_{\mathrm{def}}$.

\subsubsection*{Host budget and fixed parameter order}\label{sec:c4-7-1}
$C_{\mathrm p}$ bounds one primitive (Lemma~\ref{lem:c2-primitive-bounds}) and $C_0=N_{\mathrm h}C_{\mathrm p}e^{\kappa(B_{\mathrm h}+4)}$ bounds their sum at a host (Lemma~\ref{lem:c2-potential-size}). Let $C^{\partial}_{\mathrm p}$ be the maximum of the finite local coefficient-derivative bounds of Section~\ref{sec:c4-10-1}: the energy primitive is $g_0$ times the third-order Taylor remainder in the protected variables, and its background derivative has the same factor $g_0(1+r)^3$ because its local analytic coefficients and their background derivatives are bounded on the larger fixed row chart; the Haar primitive and its background derivative start at order $g_0^2(1+r)^2$; the constraint-Jacobian primitive and its derivative are bounded by $Cg_0(1+r)$. Set
\begin{equation}\label{eq:c4-7-1}
    C^{\partial}_0=N_{\mathrm h}\max(C_{\mathrm p},C^{\partial}_{\mathrm p})e^{\kappa(B_{\mathrm h}+4)},\qquad
    \omega(g_0)=C^{\partial}_0g_0(1+r)^3,\qquad R_\Upsilon=\frac{\omega_*}{2\omega(g_0)}\;,
\end{equation}
chosen after $M$ and before $g_0$, as $C_0$ is; neither $\omega_*$ nor $\varepsilon_*$ nor any earlier choice is shrunk after $M$. Summing the same finite host assignments proves $\sup|\mathscr D_\omega\mathbf V_\xi(Y)|\leq\omega(g_0)e^{-\kappa d_0(Y)}\|\omega\|_\infty$ on the small background neighbourhood, with $\omega(g_0)\geq C_0g_0(1+r)^3$ also bounding $\sup|\mathbf V_\xi(Y)|e^{\kappa d_0(Y)}$ (\eqref{eq:native-source-interaction-size}). Let $N_{\mathrm{type}}$ be the number of tagged ordinary primitive and probe types based in one fine translation cell of the fixed $L$-periodic template and $R_{\mathrm h}$ the maximal base-to-host offset, both fixed by the host constructions \eqref{eq:part1-potential-host}, \eqref{eq:c-probe-host}. Distinct active hosts of a selection with final domain $D$ have a labelled base in the fixed $R_{\mathrm h}$-neighbourhood of $D$, so their number is at most $H_MN_1(D)$ with $H_M=N_{\mathrm{type}}(LM+2R_{\mathrm h}+3)^4$, and the selected probe count is at most the number of fine bonds in $D$, $q\leq4(LM+1)^4\sum_DN_1(D)$. The quantities $\omega(g_0)$ and $R_\Upsilon$ of \eqref{eq:c4-7-1} are used throughout Sections~\ref{sec:c4-4} and~\ref{sec:c4-6}; only the coupling threshold changes.

\begin{lemma}[positive host comparison]\label{lem:c4-7-1}
For a host $Y$ let $n_Y\leq P_M$ be the number of probe labels with host $Y$ and put
\begin{equation}\label{eq:c4-7-2}
    A_Y=\frac{\omega_*}{2}e^{-\kappa d_0(Y)},\qquad B_Y=n_Yu_*\leq\frac{\omega_*}{8}e^{-\kappa d_0(Y)}\;.
\end{equation}
(a) With $v_{\mathrm{ordinary}}=e^{A_Y}-1$ and $v_{\mathrm{probe}}=u_*$, the sum over the nonempty label subsets at $Y$ satisfies
\begin{equation}\label{eq:c4-7-3}
    \sum_{\varnothing\ne S\subseteq\{\mathrm{ordinary},\mathrm{probes}\}}\prod_{\ell'\in S}v_{\ell'}\leq e^{A_Y}(1+u_*)^{n_Y}-1\leq e^{A_Y+B_Y}-1\leq(A_Y+B_Y)e^{A_Y+B_Y}\leq\omega_*e^{1/2}e^{-\kappa d_0(Y)}\;.
\end{equation}
(b) For a differentiated host,
\begin{equation}\label{eq:c4-7-4}
    R_\Upsilon\sup|\mathscr D_\omega\mathbf V_\xi(Y)|\,e^{A_Y}(1+u_*)^{n_Y}\leq A_Ye^{A_Y+B_Y}\|\omega\|_\infty\leq\omega_*e^{1/2}e^{-\kappa d_0(Y)}\|\omega\|_\infty\;.
\end{equation}
(c) There is a constant $C_M$, fixed after $M$ and before $g_0$, such that for every connected final domain $D$
\begin{equation}\label{eq:c4-7-5}
    \sum_{\ell\, | \,Z(\ell)=D}u_*^{q(\ell)}\sup_{|\zeta|\leq R_\Upsilon}\|\mathscr D_\omega\Lambda^{\mathrm f}_{\xi;\ell,\zeta}\|_{\mathrm{TV}}\leq C_MN_1(D)\|\omega\|_\infty\,\varepsilon_*e^{-\lambda_*\ell_1(D)}\;,
\end{equation}
the derivative including every Gaussian normaliser and the compensator; and $|\mathscr D_\omega k^{\mathrm f}_\xi(D)|\leq C_MN_1(D)\|\omega\|_\infty m(D)$ for the vacuum activities, without shrinking $\varepsilon_*$.
\end{lemma}

\begin{proof}
The bound $n_Y\leq P_M$ holds because a probe label $b$ lies in its host, whose fine side is at most $4M$, and there are four positive directions per site. After taking absolute values inside the real Mayer $t$-integral the ordinary factor is at most $e^{A_Y}-1$ on $|\zeta|\leq R_\Upsilon$ (as $R_\Upsilon\omega(g_0)=\omega_*/2$). The last inequality of \eqref{eq:c4-7-3} uses $\omega_*\leq1/2$ (\eqref{eq:native-source-vacuum-KP-budget}) and $A_Y+B_Y\leq\frac58\omega_*e^{-\kappa d_0(Y)}$. This is a positive numerical comparison, not the Mayer factor of a complex combined potential. All split selections with the same active-host set have the same $Y_0$, seed, conditioning carrier, Gaussian kernel, bad-bond choices and final-domain weakening (proof of Lemma~\ref{lem:probe-measures}), so their many-to-one sum is dominated at each host by \eqref{eq:c4-7-3} before the cover and seed sums of Appendix~\ref{app:background-estimates} are applied; this is the domination used in Lemma~\ref{lem:c4-4-1}, the final domain sum being the chain \eqref{eq:native-source-initial-domain-sum}, \eqref{eq:native-source-enlarged-domain-sum} and the final $Y'$-sum in the proof of Lemma~\ref{lem:activity-bounds}. (b) is the same comparison with the differentiated host bound of Section~\ref{sec:c4-7-1}. (c) There are at most $H_MN_1(D)$ active hosts; the Gaussian and walk derivatives have the same factor after their polynomial moment is paid (Sections~\ref{sec:c4-10-2}, \ref{sec:c4-10-3}): the uniform Gaussian coercivity gives polynomial moments at most $C_MN_1(D)$ times the same exponential volume majorant $e^{N_1(D)}$, so no fresh exponential reserve is spent. Executing the differentiated sum with the positive host comparison (b) gives \eqref{eq:c4-7-5}, and the same sum over the selections with $\mathsf J=\varnothing$ gives the vacuum-activity bound.
\end{proof}

\subsubsection*{The multi-root cancellation}\label{sec:c4-7-2}
The input $f$ is a single normalised character of the ordered closed reconstructed word, optionally closed with its inverse background interval and a fixed complementary $h$; for a linear combination the bound is multiplied by the sum of the absolute coefficients, and an arbitrary unbounded sum is not an input. On covered branches its contour input labels lie in $I$, so the retained $A_{\mathrm e}$ and the boundary map do not enter the source rows (Lemma~\ref{lem:covered}); the centred kernel $K_{\xi;0}$ likewise uses zero retained input, and the reference group construction uses the same row and mean conventions.

\begin{lemma}[commuting projections]\label{lem:c4-7-2}
Let $O_0$ be the set of roots with odd $q_j$ and empty ordinary selection, $O_1$ the set of roots with odd $q_j$ and nonempty ordinary selection. Then
\begin{equation}\label{eq:c4-7-6}
    \Bigl|\int\Delta_{\boldsymbol{\mathsf J}}f\,\dd\bigotimes_j\Lambda^{\mathrm f}_{\xi;\ell_j}\Bigr|\leq u^q\prod_{j\in O_0\cup O_1}\Bigl(u+\frac{2}{R_\Upsilon-1}\Bigr)\prod_jM_{\ell_j}\;,
\end{equation}
with the exponential-in-$q$ constants absorbed in $C_\chi$; the same holds after one background derivative with the additional factor of Lemma~\ref{lem:c4-4-3}. Moreover $\Delta_{\boldsymbol{\mathsf J}}f=0$ if some selected label does not influence the closed source word, so every surviving root has a contact with $\Gamma_C$.
\end{lemma}

\begin{proof}
For $j\in O_0$ let $P_j$ take the homogeneous part of degree $q_j$ of $\Delta_{\boldsymbol{\mathsf J}}f$ in the selected variables of root $j$, the other root variables fixed; these projections commute. Expand $\prod_{j\in O_0}(P_j+(1-P_j))$. A term containing $P_j$ is odd under the reversal of exactly root $j$ and integrates to zero against that root's even source-free density; only $\prod_{j\in O_0}(1-P_j)$ remains, with one extra $u$ per such root by the mixed Taylor remainder \eqref{eq:c4-10-9} and the fixed row-overlap count. For $j\in O_1$ the independent $\zeta_j$-integral vanishes at $\zeta_j=0$, so the multivariable Cauchy difference supplies $\prod_{j\in O_1}2/(R_\Upsilon-1)$ times the supremum $\prod M_{\ell_j}$ of \eqref{eq:c4-4-5}. Together this is \eqref{eq:c4-7-6}, and for even $q_j$ only $u^{q_j}M_{\ell_j}$ is paid. After one background derivative the Gaussian derivative is even, the leading source derivative has the same parity (\eqref{eq:c4-10-10}) and a differentiated Mayer factor still vanishes at $\zeta_j=0$, so the argument repeats. The last statement is the telescoping of the $K$-sum \eqref{eq:c4-4-1} over the labels of a root that the word does not see; it is the pin used in the $\mathcal A$- and $W$-sums, and no sum over unmarked roots in the volume is claimed to be uniform.
\end{proof}

\subsubsection*{The common Hessian bounds on the extension}\label{sec:c4-7-3}
\begin{lemma}[Hessian bounds along the coefficient path]\label{lem:c4-7-3}
Choose $\tau_{\mathrm b}>0$ after $\tau_L$, $c_L$, $\gamma_L$ and before $g_0$, with $\tau_{\mathrm b}\leq\tau_L/4$ and $c_L\tau_{\mathrm b}\leq\gamma_L/4$. For every globally small extension $U=e^{itB}U^\circ$ with $\|B\|_\infty\leq\tau_{\mathrm b}$ of the flat background on a comparison box, every compression of the regional Hessian to the same $I$ satisfies
\begin{equation}\label{eq:c4-7-7}
    \frac34\gamma_L\,\id\leq H_{e^{itB}}\leq m_L\,\id\;.
\end{equation}
\end{lemma}

\begin{proof}
On physical branches Lemma~\ref{lem:regular-bounds} gives $\gamma_L/2\leq H_{\xi,II}\leq m_L$ with the force--constraint and soft-gauge terms. The local entry formula $f_{bb'}(A)$ of Lemma~\ref{lem:c2-regional-entry} has row and column sums at most $m_L$ on the phase box $\tau_L$, by the definition of $m_L$ in \eqref{eq:regular-covariance-entry-constants}, and Lipschitz bound $c_L$, so the extension has operator difference from $H^\circ=\mathsf H^{\Omega_1}_{\id}$ at most $c_L\tau_{\mathrm b}\leq\gamma_L/4$; with the flat lower bound $\gamma_L$ (\eqref{eq:covariance-uniform-gap}) this gives \eqref{eq:c4-7-7}. The recipe $\gamma=\gamma_L/2$, $h_+=m_L$ of Section~\ref{sec:fixed-first-kernel} therefore works at the physical endpoint and throughout the extension; no new expansion instantiation or coefficientwise identification of different recipes is used, and nothing is asserted about the global closeness of the physical background to the identity.
\end{proof}

\subsubsection*{Differentiating the joint vacuum ratio}\label{sec:c4-7-4}
$\Phi^{\mathrm v}_\xi(\mathfrak c)$ is the Ursell expression $\varphi^T(\mathfrak c)\prod_jk^{\mathrm f}_\xi(D_j)/m!$ of \eqref{eq:part1-vacuum-cluster} with the fixed-kernel vacuum activities; that formula is used directly.

\begin{lemma}[derivative of the cluster sum]\label{lem:c4-7-4}
Let $M_v(\mathfrak c)$ be the positive incompatibility-tree majorant of $\Phi^{\mathrm v}_\xi(\mathfrak c)$ built from $m(D)$ (Section~\ref{sec:c4-6-2}) and $n(\mathfrak c)=\sum_{D\in\mathfrak c}N_1(D)$. Then
\begin{equation}\label{eq:c4-7-8}
    |\mathscr D_\omega\Phi^{\mathrm v}_\xi(\mathfrak c)|\leq C_M\|\omega\|_\infty\,n(\mathfrak c)M_v(\mathfrak c)\;,
\end{equation}
and for every finite set $\mathcal A$ of connected final domains
\begin{equation}\label{eq:c4-7-9}
    \sum_{\mathfrak c\text{ hits }\mathcal A}M_v(\mathfrak c)e^{n(\mathfrak c)/2}\leq\frac18\sum_{D\in\mathcal A}N_1(D),\qquad
    \sum_{\mathfrak c\text{ hits }\mathcal A}|\mathscr D_\omega\Phi^{\mathrm v}_\xi(\mathfrak c)|\leq\frac{C_M}{2}\|\omega\|_\infty\sum_{D\in\mathcal A}N_1(D)\;.
\end{equation}
\end{lemma}

\begin{proof}
\eqref{eq:c4-7-8} is the product rule over the constituents with the activity derivative bound of Lemma~\ref{lem:c4-7-1}(c): a sum over the possible differentiated vertices, not a division by an activity. The numerical criterion of Lemma~\ref{lem:activity-bounds} is $\sum_{D'\not\sim D}m(D')e^{(1+6\theta)N_1(D')}\leq N_1(D)/8$; apply its rooted-tree proof (Section~\ref{app:kp}) to the activity $m(D)e^{N_1(D)/2}$ with node cost $N_1(D)/8$, the combined exponent $5/8$ being below $1+6\theta$. This gives the first bound of \eqref{eq:c4-7-9}, the family version following by summing the single-root bound over $D\in\mathcal A$ (clusters hitting several roots are overcounted in this majorant only, not in the exact ratio). Since $n\leq4e^{n/4}\leq4e^{n/2}$, inserting \eqref{eq:c4-7-8} gives the second bound. Inserting the second bound into the derivative of the exponential \eqref{eq:c4-4-11} proves \eqref{eq:c4-4-12}: $C_M$ is an outside prefactor for a single derivative and is not put into every cluster weight, so no $M$-dependent shrinking of $\omega_*$ or $\varepsilon_*$ is needed after those constants have been fixed. The same $m(D)$ controls the undifferentiated activity and its one-derivative polynomial majorant, the polynomial being paid by the displayed exponential moment.
\end{proof}

\subsection{Quantitative group and caller checks}\label{sec:c4-8}
\subsubsection*{Carrier, source and physical weights}\label{sec:c4-8-1}
All group comparisons and flat-subtraction identities are made on $A_{\mathrm{cov}}$. There the source rows have their free inputs in $I$, so Lemma~\ref{lem:covered} gives $U_\xi(0)=U_1$ along the whole contour and removes $A_{\mathrm e}$ and $\Psi_\xi$ from the fluctuating source rows; Lemma~\ref{lem:collar} and \eqref{eq:c-collar-identity} give $K_{\xi;0}$ with $H=H_{\xi,II}$, $P_{\xi,0}(a)=\sum_{\mathfrak p\ \mathrm{near}}\mathfrak p(a)$ and the chosen $r$-box, every primitive argument having zero retained input. The boundary Jacobian, the far primitives and the retained quadratic term are in $c_\xi$, not in the centred coefficients, and every fixed-kernel operation, probe measure and vacuum activity is built from those centred objects. Hence the local background data of a coefficient are $U_1$, the unchanged carrier geometry and the fixed coupling/cutoff/mean prescription; $V_0$ is not replaced in the physical integral, and its influence on these local coefficients is through $U_1$.

The local-data comparison of Section~\ref{sec:c4-11} applies on a box containing all source and coefficient stencils and lying in $\Lambda_1$ outside $S_1$. The fixed-kernel support statements (Section~\ref{sec:c4-10-2}) place every surviving walk coefficient, seed inverse and primitive stencil there, and the regional $I$ and $\Omega_1$ are kept on both sides of the interpolation. At the flat endpoint these local formulas are the reference formulas for $a_W$, since their arguments contain no retained field, boundary map or additional $V_0$: an equality of the selected coefficient, not of physical densities. The force--constraint and relative soft-gauge terms are those of the regional Hessian \eqref{eq:c-regional-hessian} and are included throughout.

Under a simultaneous site gauge each Hessian entry, restricted inverse and fixed walk coefficient is conjugated by the free-field adjoint action (Lemma~\ref{lem:hessian-gauge-locality}, Lemma~\ref{lem:walk-series}), the protected cutoffs are invariant, and the row solution is covariant; orthogonal changes of the integration variables leave the closed selected integrals unchanged, including their spatial Cauchy integrals, and their Laplace transforms give the covariance of each probe measure; the vacuum activities and Ursell products are scalar invariants; finally $T_WP_W^{-1}$ and $h$ are simultaneously conjugated at the interval base. This is the gauge law of the group closed contraction factor by factor (Section~\ref{sec:c4-11-2}); no straight-side assumption enters it.

$\mathcal O$ is the positive outer operation \eqref{eq:native-source-explicit-outer-operation}: the Haar and constraint factors are measures and the displayed cutoffs and exponentials are nonnegative, so $\mathbb E_{\mathrm h}$ is a positive normalised functional. With $E_{\mathrm{bdry}}$ of \eqref{eq:c3-6-2}, the full identity is
\begin{equation}\label{eq:c4-8-1}
    \mathbb E_\varepsilon[W_\chi(C)]=\mathbb E_{\mathrm h}\bigl[\mathbf 1_{A_{\mathrm{cov}}}S^\circ_{\xi,C}f_\xi(0)\bigr]+E_{\mathrm{def}}+E_{\mathrm{bdry}}\;,
\end{equation}
by \eqref{eq:c-one-step-branch-identity} and \eqref{eq:native-source-physical-ratio}. The far uncovered event is empty: a failure of coverage puts a label of $\Gamma_C$ in $E(\Lambda_1^c)$, so $A_{\mathrm{cov}}^c\subseteq\mathsf N_0\subseteq\mathsf N_b$. The exterior response is not omitted from $E_{\mathrm{def}}$; it is the separately controlled $E_{\mathrm{bdry}}$ of Appendix~\ref{app:exterior-chessboard}.

\subsubsection*{Two quantitative pins}\label{sec:c4-8-2}
A component $\gamma$ consists of a nonempty unordered root family $\mathcal A(\gamma)$ and an ordered list $(\mathfrak c_1,\ldots,\mathfrak c_k)$ of cluster occurrences with connected incidence graph as in Section~\ref{sec:joint-extraction}; $n_\gamma$ counts every constituent cube with its occurrence multiplicity, $\mathsf T_\gamma$ is the union of the contact sets of its roots, $H_\gamma$ its hull, $X_\gamma$ the union of its domains. Define
\begin{equation}\label{eq:c4-8-2}
    t_\gamma=\frac{\rho^{|\mathcal A(\gamma)|}}{k!}\prod_{D\in\mathcal A(\gamma)}m(D)\prod_{j=1}^kM_v(\mathfrak c_j)\;.
\end{equation}
Summing unordered distinct roots is overcounted by ordered root tuples divided by their factorial. A class $K$ is an unordered family of components with connected hull-overlap graph, with weight $t_K=\prod_{\gamma\in K}t_\gamma$; for the positive recursion the sum over classes is overcounted by ordered tuples divided by the tuple factorial, dropping the disjointness restrictions, which only enlarges the sum and fixes every multiplicity convention. Fix
\begin{equation}\label{eq:c4-8-3}
    0<\varpi\leq\min\Bigl(\frac1{16},\frac{\lambda_*}{64C_{\mathrm g}}\Bigr)\;,
\end{equation}
with $C_{\mathrm g}$ of Lemma~\ref{lem:c2-domain-geometry}.

\begin{lemma}[component pins]\label{lem:c4-8-2}
There are constants $C_{\mathrm{pin}}$, $A_{\mathrm h}$, $A_{\mathrm x}$ fixed before the coupling such that, for $\rho$ below a threshold depending on them: (a) for every root $D_0$,
\begin{equation}\label{eq:c4-8-4}
    \sum_{\gamma\, | \,D_0\in\mathcal A(\gamma)}t_\gamma e^{\varpi n_\gamma}\leq\rho\,m(D_0)e^{(\varpi+1/4)N_1(D_0)},\qquad
    \sup_{a\in\mathcal I_C}\sum_{\gamma\, | \,a\in\mathsf T_\gamma}t_\gamma e^{\varpi n_\gamma}\leq C_{\mathrm{pin}}\rho\;;
\end{equation}
(b) $|H_\gamma|\leq A_{\mathrm h}LMn_\gamma$, and the distance from a source contact of $\gamma$ to any cube of $X_\gamma$, halos included, is at most $A_{\mathrm x}LMn_\gamma$; with $\theta_{\mathrm h}=\varpi/(4A_{\mathrm h}LM)$, $\theta_{\mathrm x}=\varpi/(4A_{\mathrm x}LM)$ and $d_C$ the contour distance,
\begin{gather}
    \sum_{\gamma\, | \,a\in H_\gamma}t_\gamma e^{\varpi n_\gamma/4}\leq\sum_{a'\in\mathcal I_C}e^{-\theta_{\mathrm h}d_C(a,a')}\sum_{\gamma\, | \,a'\in\mathsf T_\gamma}t_\gamma e^{\varpi n_\gamma/2}\leq C_{\mathrm{pin}}\rho\Bigl(1+\frac{2}{e^{\theta_{\mathrm h}}-1}\Bigr)\;,\label{eq:c4-8-5}\\
    \sum_{\gamma\, | \,\Delta\subset X_\gamma}t_\gamma e^{\varpi n_\gamma/4}\leq C_{\mathrm{pin}}\rho\sum_{a'\in\mathcal I_C}e^{-\theta_{\mathrm x}d_T(a',\Delta)}\leq C\rho\;;\label{eq:c4-8-6}
\end{gather}
(c) with $A_{\mathrm s}=1+A_{\mathrm h}$ and $\eta>0$ chosen after these constants with $1000\eta A_{\mathrm s}<\varpi/8$, the pins (b) hold with the weight $e^{100\eta\mathfrak s(\gamma)}$, $\mathfrak s(\gamma)=n_\gamma+|H_\gamma|/(LM)$, leaving a fixed exponential margin.
\end{lemma}

\begin{proof}
(a) The two-species tree recursion of Lemma~\ref{lem:c4-6-2} runs with the weights multiplied by $e^{\varpi n}$: the vacuum estimate \eqref{eq:c4-7-9} holds with exponent up to $1/2$, and node cost $N/4$ uses at most $\varpi+1/4<1/2$; the marked-root mass is made at most one eighth of the node cost by choosing $\rho$ small, which changes only $g_0$. This gives the first bound; summing $D_0$ over the roots with a fixed source contact $a$ by the animal bound \eqref{eq:native-source-animal-sum} (the exponent $\lambda_*-(\varpi+1/4)\cdot5\geq\lambda_*/2$ remaining) gives $C_{\mathrm{pin}}$. (b) The two geometric bounds follow from the square geometry and wall connectivity (Section~\ref{sec:c4-6}). If a traversal $a$ lies in $H_\gamma$ and $a'$ is a contact of $\gamma$, then $d_C(a,a')\leq A_{\mathrm h}LMn_\gamma$, so $e^{\varpi n_\gamma/4}\leq e^{\varpi n_\gamma/2}e^{-\theta_{\mathrm h}d_C(a,a')}$, and the contour sum $\sum_{a'}e^{-\theta_{\mathrm h}d_C(a,a')}\leq1+2/(e^{\theta_{\mathrm h}}-1)$ is uniform in $n_C$. For a cube $\Delta\subset X_\gamma$ the analogous inequality holds with $\theta_{\mathrm x}$ and the torus distance; for each of the four straight sides the sum over $a'$ is at most $1+2/(e^{\theta_{\mathrm x}}-1)$ up to the fixed cube/halo offset, bounded by the full one-dimensional periodic lattice sum independently of $n$ and the periods. This retains $\rho$ even when $\Delta$ lies in a cluster domain. The contour-hull stencil part of $F(\gamma)$ adds at most $CLM$ possible traversals near a cube, times the hull pin. (c) $100\eta\mathfrak s(\gamma)\leq100\eta A_{\mathrm s}n_\gamma<\varpi n_\gamma/8$, so the enhanced weights are dominated by the $e^{\varpi n_\gamma/4}$ of (b) with a margin $e^{\varpi n_\gamma/8}$. All constants are fixed before $g_0$; the source smallness conditions are $C\rho LM\leq\eta/8$ and the root-incidence bound of (a).
\end{proof}

\subsubsection*{Short classes and the exceptional whole-contour merge}\label{sec:c4-8-3}
\begin{lemma}[class pins]\label{lem:c4-8-3}
Under Lemma~\ref{lem:c4-8-2} and $C\rho LM\leq\eta$: (a) for every overlap-connected class $K$ that is not promoted to the whole contour, the hull and footprint pin sums with the weight $e^{64\eta\sum_{\gamma\in K}\mathfrak s(\gamma)}$ are at most $C\rho$; (b) with $\sigma_K=\sum_{\gamma\in K}\mathfrak s(\gamma)$ a long class satisfies
\begin{equation}\label{eq:c4-8-7}
    \sigma_K\geq\frac{1}{LM}\sum_{\gamma\in K}|H_\gamma|\geq\frac{n_C}{2LM},\qquad
    \sum_{K\ \mathrm{long}}t_Ke^{4\eta\sigma_K}\leq C\rho n_Ce^{-30\eta n_C/(LM)}\;;
\end{equation}
(c) the whole-contour groups created by the exceptional merge satisfy
\begin{equation}\label{eq:c4-8-8}
    C\rho n_Ce^{-30\eta n_C/(LM)}e^{4\eta n_C/(LM)}e^{C\rho n_C}\leq C\rho n_Ce^{-25\eta n_C/(LM)}\leq C'\rho\;,
\end{equation}
uniformly in $n_C$. Together with (a) this proves the two weighted group pins \eqref{eq:c4-6-5}.
\end{lemma}

\begin{proof}
(a) Run the positive overlap-tree recursion on the decorated components with the weights enhanced by $e^{64\eta\mathfrak s(\gamma)}$. The pin of Lemma~\ref{lem:c4-8-2}(c) controls the overlap sum of a hull by $C\rho|H_\gamma|\leq\eta\mathfrak s(\gamma)/8$ at the chosen source smallness, so the rooted recursion gives the hull and footprint pins for every class before promotion, the additional node cost being covered by the $100\eta$ margin; a short class uses the union of its hull intervals, so its size is bounded by the additive class cost. (b) The first inequality is the definition of $\mathfrak s$; the second holds because the union of the hulls of a long class has at least $n_C/2$ positions (Section~\ref{sec:joint-extraction}). Anchor the class at a traversal of its union interval; there are at most $n_C$ anchors, and the enhanced class pin gives the second bound of \eqref{eq:c4-8-7}, the remaining exponent $60\eta\sigma_K$ being at least $30\eta n_C/(LM)$. (c) Once a long class occurs, every other component is merged into the whole-contour group; the other components with their $4\eta$ weights sum to at most $e^{C\rho n_C}$, and the whole-contour interval weight costs $e^{4\eta n_C/(LM)}$. The middle inequality of \eqref{eq:c4-8-8} uses $C\rho LM\leq\eta$, and the final maximum is finite uniformly in $n_C$ because $LM$ and $\eta$ are fixed. If a spatial pin lies in an additional component, root that component by its footprint pin at a further cost $C\rho$, the anchored long-class factor and remaining exponential being paid by \eqref{eq:c4-8-8}; if it lies in the long class, use the footprint pin in place of the hull pin; pins on the whole contour are covered by the total whole-group bound. This proves the exceptional-merge pin without assigning its cost to a single original component. Polynomial moments are allowed by using a smaller part of the same fixed enhanced-weight margin.
\end{proof}

\subsubsection*{Interior boxes, endpoints and the differentiated group weight}\label{sec:c4-8-4}
Let $C_{\mathrm{box}}$ be a fixed geometric constant for the group footprint and the row/contour halos such that a liftable enclosing comparison rectangle has diameter at most $C_{\mathrm{box}}LMn(W)$, increased so that a group with
\begin{equation}\label{eq:c4-8-9}
    n(W)<\frac{b}{4C_{\mathrm{box}}LM}
\end{equation}
has its entire rectangle and stencils within $b/2$ of a source contact and an injective lift (Section~\ref{sec:c4-11-4}). On a far history this box lies in $\Lambda_1$, hence in $\Omega_1$, and outside $S_1=(\Omega_1\setminus\Omega_1^{\sim-1})\cup R_1$; its plaquettes satisfy $\delta_{Q_W}(U_1)\leq C\varepsilon_1$ by Lemma~\ref{lem:c2-plaquette-deviation} and the distance check of Section~\ref{sec:c4-11-5}, and the spectrum and row hypotheses of Lemma~\ref{lem:c4-7-3} hold on the globally small extension used for its comparison. All other groups keep their undifferentiated difference, $|c_W|+|a_W\chi|\leq2M(W)$; their occurrence count is at least $b/(4C_{\mathrm{box}}LM)$, and if a rectangle fails to lift the same lower bound holds, since $N_{\min}=\min_iN_i\geq2LMR_1>32b$ (Section~\ref{sec:c4-9-2}) and a wrapping connected network has length at least a fixed fraction of $N_{\min}$. No interpolation is made across the integration boundary.

For a good box use the coefficient locality and covariance of Sections~\ref{sec:c4-8-1} and~\ref{sec:c4-11}: root the tree gauge at the initial interval base, keep $h$ fixed, and compare $c_W(U_1;h)$ with $c_W(\id;h)=a_W\chi(h)$ by the small-phase extension and the fundamental theorem of calculus (Lemma~\ref{lem:c4-9-1}). It is the same regional reference coefficient, with $I$, all selection indices and the local geometry retained. The group weight is differentiated by the product rule, each occurrence retained:
\begin{equation}\label{eq:c4-8-10}
    \mathscr D_\omega w_\xi(W)=\frac{(-1)^{k(W)}}{k(W)!}\sum_{j=1}^{k(W)}\mathscr D_\omega\Phi^{\mathrm v}_\xi(\mathfrak c_j)\prod_{l\ne j}\Phi^{\mathrm v}_\xi(\mathfrak c_l)\;,
\end{equation}
bounded by Lemma~\ref{lem:c4-7-4} by $C_M\|\omega\|_\infty\sum_jn(\mathfrak c_j)$ times the positive product majorant, without dividing by any $\Phi$. With the joint source derivative of Lemma~\ref{lem:c4-4-3} this gives $|\mathscr D_\omega c_W|\leq C\|\omega\|_\infty(n(W)+|\mathcal H(W)|)M(W)$ uniformly in $h$ (\eqref{eq:c4-12-2}); the curvature phase bound contributes $C\operatorname{diam}(Q_W)^2\delta_{Q_W}$, and with $|\mathcal H(W)|\leq CLMn(W)$ all these losses are a fixed constant times $\varepsilon_1$ times a fixed polynomial in $\mathfrak s(W)$, absorbed by the enhanced pin ($x^ke^{-\eta x}\leq k!\eta^{-k}$). For a large group the factor $e^{-\eta b/(8C_{\mathrm{box}}LM)}$ is extracted from its reserved weight $e^{\eta\mathfrak s(W)/2}$. Combining the two classes and summing over a contour pin gives \eqref{eq:c4-6-8}; the computation is Section~\ref{sec:c4-12-2}. The same matrices and the same cutoff norm are used at the physical and flat endpoints, and every source estimated is the closed functional $c_W$: no partial interval is replaced by a scalar before its closed subtraction is formed.

\subsection{The coefficient extension and the countable-gas limit}\label{sec:c4-9}
\subsubsection*{Background scope and the coefficient path}\label{sec:c4-9-1}
Sections~\ref{sec:c4-4} and~\ref{sec:c4-7} give the joint source and one-derivative bounds at the physical centred background and on every globally small real extension described here, for each closed character $\chi(T_WP_W^{-1}h)$ uniformly in $h$; they do not assert a path from the entire physical background to the identity in one global small chart.

Fix a good interior group of Section~\ref{sec:c4-8-4} and its enclosing fine rectangle $Q_W$, which contains all coefficient, reconstruction, averaging and interval/closing stencils. By the support statements of Section~\ref{sec:c4-10-2}, for the fixed selection indices and the fixed spatial Cauchy coefficient defining the group only the background links on $Q_W$ are used: the restricted seed inverse uses entries on $E_0$, every walk coefficient has its domains in the final component, and the potential and source rows have their finite stencils. The regional $I$, $\Omega_1$ and every auxiliary parameter are held fixed. Gauge $U_1$ on $Q_W$ by its rooted tree gauge $g_W$ with $g_W(\mathrm{base})=\id$ (Lemma~\ref{lem:c4-10-5}). If $C_{\mathrm{tg}}\operatorname{diam}(Q_W)^2\delta_{Q_W}\leq\tau_{\mathrm b}/2$, write the principal phases $B_W(b)=\frac1i\log U_1^{g_W}(b)$ on the rectangle and extend $B_W=0$ on every other bond, and define the coefficient argument and its direction by
\begin{equation}\label{eq:c4-9-1}
    U_{W,t}(b)=e^{itB_W(b)},\qquad\omega_W(b)=B_W(b),\qquad\|\omega_W\|_\infty=\max_bh(B_W(b)),\qquad0\leq t\leq1\;;
\end{equation}
the norm is the invariant norm $h$, the comparison with the cutoff norm being absorbed in $C$. Set $L_f$ equal to the number of occurrences of background links in the relative word $T_WP_W^{-1}$ on which this argument varies, $L_f\leq2|\mathcal H(W)|$ times the fixed reconstruction-row overlap constant. The complementary $h$ is held fixed at the root base.

At each $t$ form $H_t=\iota_I^*\mathsf H^{\Omega_1}_{U_{W,t}}\iota_I$, the row reconstruction $q_{U_{W,t}}$ and the near primitives at $U_{W,t}$, with zero retained input and the same protected $r$-box. For a generic noncritical $U_{W,t}$ the energy primitive is defined by subtracting its constant, linear and quadratic Taylor terms as in \eqref{eq:native-source-energy-primitives}, the Hessian keeping the force--constraint term; the Haar and constraint-Jacobian primitives use their analytic row formulas. These definitions specify an analytic coefficient extension. This auxiliary kernel is not identified with the physical CRE integral at $t\in(0,1)$, and the original fixed-$V$ constraint is not imposed along the path; at the physical endpoint each compensated primitive agrees with its Taylor-subtracted formula by locality, criticality being used in the primitive-sum identity \eqref{eq:native-source-primitive-sum} for the physical exponent and not to assert that $U_{W,1}$ is a global minimum; at the flat endpoint the formulas agree with the reference formulas. Lemma~\ref{lem:c4-7-3} gives $\gamma_L/2\leq H_t\leq m_L$; the designated inverses, reconstruction and means use the fixed smaller row charts since $\|B_W\|_\infty\leq\tau_{\mathrm b}/2$ and $\tau_{\mathrm b}\leq\tau_L/4$; the host norms and their derivatives are bounded by $C^{\partial}_0g_0(1+r)^3$ on these charts; so the Gaussian payment, the positive forest budget and the source estimates hold uniformly in $t$ with the same recipe. The force term is one of the local entries and is not omitted off the minimum.

\begin{lemma}[the coefficient path]\label{lem:c4-9-1}
For a good interior group passing the phase test,
\begin{equation}\label{eq:c4-9-2}
    d_W(U_1;h)=\int_0^1\mathscr D_{\omega_W}c_W(U_{W,t};h)\,\dd t\;,
\end{equation}
and $|\mathscr D_{\omega_W}c_W(U_{W,t};h)|\leq C\|\omega_W\|_\infty(L_f+n(W))M(W)$ uniformly in $t$ and $h$.
\end{lemma}

\begin{proof}
At $t=1$ the group coefficient agrees with the original one by coefficient locality on $Q_W$ and simultaneous gauge covariance (Section~\ref{sec:c4-11-3}): the values outside $Q_W$ can be replaced in the argument because no term of the spatial Cauchy coefficient consults them, and the root gauge $g_W(\mathrm{base})=\id$ leaves $h$ unchanged. At $t=0$ the coefficient is exactly the regional reference one, with the same $I$ and the same group index $W$, so $c_W(U_{W,0};h)=a_W\chi(h)$. The fundamental theorem of calculus applies by the dominated-convergence hypotheses of Section~\ref{sec:c4-11-3}. The derivative of $c_W$ differentiates $\prod_j\Phi^{\mathrm v}(\mathfrak c_j)$, giving the occurrence sum \eqref{eq:c4-8-10} with majorant $C\|\omega\|_\infty(\sum_jn(\mathfrak c_j))M(W)$, and the root integral, giving $C\|\omega\|_\infty(L_f+\sum_{D}N_1(D))M(W)$ by Lemmas~\ref{lem:c4-4-3} and~\ref{lem:c4-7-1}; the sum is the displayed bound. This is a cluster-list bound for the same group weight, not an identification of a one-root vacuum ratio with it: the joint-ratio estimate of Lemma~\ref{lem:c4-7-4} controls the original family normalisation, the occurrence estimate controls its regrouping. If the phase test fails, the two endpoint estimates give the curvature bound of Section~\ref{sec:c4-12-2}; no continuation is claimed in that regime. The path is the connection between the local physical coefficient and the globally small extension; it does not assume global near-identity physical fields.
\end{proof}

\subsubsection*{Parameter and period conventions}\label{sec:c4-9-2}
All results inherit the standing conditions \eqref{eq:c-standing-conditions} and the compatible even fine periods of Section~\ref{sec:c3-7}: every fine period $N_i$ is an even integer multiple of $\ell=LMR_1$, and $\ell$ is odd ($L$, $M$, $R_1$ odd powers of $L$). If $N_i=q_i\ell$ then $q_i$ is even and positive, so
\begin{equation}\label{eq:c4-9-3}
    N_{\min}=\min_iN_i\geq2LMR_1>32\lfloor LMR_1/16\rfloor=32b\;,
\end{equation}
the strict middle inequality because $\ell$ is odd. This is independent of the square-fit condition $K_i\geq3(n+2)$; both are retained, with the source-row and coarse-grid conditions of Section~\ref{sec:sourced-effective-interaction}. Thus the good comparison box and every fixed stencil have a unique lift under the small-group criterion \eqref{eq:c4-8-9}, and the periodic failure lies in the large-group class; no condition on the fluctuating field or a denominator is added. $\Gamma_C$ consists of the individual positive contour bonds and all their fixed input templates, $C_L$ including the number and size of the templates, and the radius-$b$ ball of Lemma~\ref{lem:c4-2-1} is around each individual bond, so the count $4(2b+3)^4$ needs no further $n_C$-dependent factor. The input of Appendix~\ref{app:exterior-chessboard} is the one-point probability $p_z\leq q\leq e^{-c_*\pi_*^2}$ with $p_0(g)=A_0(\log g^{-2})^{p_0}$, $p_0\geq5\mathfrak r\geq10$. $E_{\mathrm{bdry}}$ of \eqref{eq:c3-6-2} is bounded separately by Proposition~\ref{prop:c3-7-5}; $E_{\mathrm{def}}$ contains only the covered centred-kernel subtraction, so neither the exterior response nor the uncovered contribution is dropped from \eqref{eq:c4-8-1}.

\subsubsection*{Countably many group species and differentiation}\label{sec:c4-9-3}
\begin{lemma}[countable species]\label{lem:c4-9-2}
At a fixed finite torus let $\mathcal W_N=\{W\, | \,n(W)\leq N\}$, a finite set, with partition sum $S_N$ and connected-cluster logarithm $L_N$, $S_N=e^{L_N}$. Then $L_N\to L$ and $S_N\to S^\circ_{\xi,C}$, so
\begin{equation}\label{eq:c4-9-4}
    \sum_W|a_W|e^{\mathfrak a_W/8}\leq C\rho n_C<\infty,\qquad S^\circ_{\xi,C}=e^L\ne0\;,
\end{equation}
and the restricted identity \eqref{eq:c4-6-7} holds for the countable index set. The background derivatives of Lemmas~\ref{lem:c4-4-3} and~\ref{lem:c4-7-4} may be taken termwise and integrated in $t$ before the countable limit.
\end{lemma}

\begin{proof}
$\mathcal W_N$ is finite: the domain set is finite, and $n(W)$ bounds the number of roots, occurrences and members of every occurrence. Its gas satisfies the same Kotecký--Preiss inequality, deleting species only decreasing the positive sums. Every group has a nonempty contour interval, so the pin \eqref{eq:c4-6-5} summed over the $n_C$ traversals gives the first bound of \eqref{eq:c4-9-4}; the rooted-tree estimate bounds the total absolute connected-cluster series by this finite sum up to a fixed constant; each finite cluster tuple is present for all large $N$, so absolute domination gives $L_N\to L$; independently the full gas sum over finite compatible families is absolutely bounded by $\exp(\sum_W|a_W|)$, and dominated convergence gives $S_N\to S^\circ_{\xi,C}$. The same argument after excluding every species incompatible with a fixed compatible family $\mathfrak B$ gives the restricted identity; the logarithmic difference is the connected-cluster sum of tuples hitting $\mathfrak B$, counted once, with absolute sum at most $\sum_{W\in\mathfrak B}\mathfrak a_W/8$ by the pinned estimate. For the derivatives, Lemmas~\ref{lem:c4-7-1} and~\ref{lem:c4-7-4} give summable positive majorants independent of $t$ on the extension; on each finite truncation the product and integral derivatives are justified by the uniform Gaussian coercivity (Section~\ref{sec:c4-10-3}) and the fixed protected box, and the walk derivative series converges on its unchanged contours (Section~\ref{sec:c4-10-2}); the cluster majorant $n(\mathfrak c)M_v(\mathfrak c)$ is paid by its exponential moment and the group majorant has only the polynomial in $\mathfrak s(W)$, paid by the reserved weight. Uniform absolute convergence permits termwise differentiation and $t$-integration before the countable limit; no conditionally convergent series is differentiated.
\end{proof}

\subsubsection*{Integrability at the physical caller}\label{sec:c4-9-4}
The near-history contribution is bounded after forming $\mathscr R_\xi$, without exchanging its sum with the outer integral (Lemma~\ref{lem:c4-2-1}). On far histories Lemma~\ref{lem:c4-6-5} gives the absolute majorant $|S^\circ_{\xi,C}|$ times the displayed exponential; since $|S^\circ_{\xi,C}|\leq1$ and the exponential is uniform in the branch fields and retained variables, it is integrable against the normalised positive history law at each fixed loop and cutoff, which justifies the far-history sum/integral exchanges. The physical $\mathcal Z_0$ and $\mathsf w_\xi=e^{c_\xi}I_{\xi;1}$ remain those of Section~\ref{sec:c4-1}.

\subsection{Analytic inputs for the coefficient extension}\label{sec:c4-10}
\subsubsection*{Joint background/phase analyticity and primitive derivatives}\label{sec:c4-10-1}
Fix one of the finitely many row/primitive stencil types in its translated fine-lattice frame and write the background on the stencil as $U_Z(b)=e^{iZ_b}$; background directions use the maximum $h$-norm on this finite label set. Choose $\tau_{\mathrm b}$ and a phase radius $\theta_0>0$ so that $\|Z\|<2\tau_{\mathrm b}$ and $\|A\|<2\theta_0$ keep every finite path product and relative product entering the bond average and the mean of RG1 (0.4), (0.11) inside the matrix-logarithm neighbourhood $\|W-\id\|_{\mathrm{op}}<1/2$; this is possible uniformly over the finite types, every word having bounded length and $e^{iA}e^{iZ}$ being analytic in both variables.

For the mean of RG1 (0.11) write its defining equation $\sum_j\log(W_jM^{-1})=0$. At $W_j=\id$, $M=\id$ its derivative in the Lie-algebra parameter of $M$ is $-n\,\id$, so the parametric analytic implicit function theorem gives a jointly analytic local mean in the background and fluctuating phases; it agrees with the mean of Lemma~\ref{lem:c2-uniform-chart}(iv), both taking the value $\id$ at zero and solving that equation in the same smaller neighbourhood. The joint radii are shrunk so that the mean stays in that neighbourhood; no global uniqueness is inferred from a logarithm chart.

The bond constraint on a row $c$ is the jointly analytic function
\begin{equation}\label{eq:c4-10-1}
    \mathcal Q_Z(A)=\frac1i\log\bigl(\mathsf M(e^{iA}U_Z,c)\mathsf M(U_Z,c)^{-1}\bigr),\qquad LQ_Z=D_A\mathcal Q_Z(0),\qquad N_Z(A)=\mathcal Q_Z(A)-LQ_ZA\;,
\end{equation}
$\mathsf M$ the bond average of RG1 (0.4), with $N_Z(0)=D_AN_Z(0)=0$ for every $Z$. The coefficient of the designated phase in $LQ_Z$ is uniformly invertible on a smaller background polydisc, by the identity-background designated inverse (Lemma~\ref{lem:two-block}) and continuity, so the designated inverse $h_Z$ with $LQ_Zh_Z=\id$ and $\mathsf C_Z=\iota_{\mathrm{free}}-h_ZLQ_Z\iota_{\mathrm{free}}$ are analytic in $Z$ with uniformly bounded first background derivatives; their maps and normalisations are those of Section~\ref{sec:regular-hessian-stencils}. The row solution is defined by
\begin{equation}\label{eq:c4-10-2}
    \widetilde D_Z(A)=N_Z\bigl(A-h_Z\widetilde D_Z(A)\bigr)\;.
\end{equation}
On smaller joint balls the derivative of the right side in $\widetilde D$ has norm at most $1/2$ uniformly in $Z$, since $D_AN_Z(A)=O(\|A\|)$; uniform analytic contraction (the parametric implicit function theorem) gives joint analyticity and $\|\widetilde D_Z(A)\|\leq C\|A\|^2$ (Lemma~\ref{lem:c2-uniform-chart}(ii) at each real $Z$). Cauchy estimates on the larger joint balls, followed by the order-two zero in $A$, give for $l=0,1$ and each fixed $k$ needed below
\begin{equation}\label{eq:c4-10-3}
    \|D_Z^lD_A^k\widetilde D_Z(A)\|\leq C_{l,k}\|A\|^{\max(2-k,0)}\;.
\end{equation}
All constants are maxima over finitely many types, independent of the volume, the history and $g_0$; the dimensions of the types depend on $L$ and $G$ only. The protected free input satisfies $g_0\|\mathsf C_Za\|<\theta_0/2$ after reducing the coupling, and the phase $q_Z(a)=g_0\mathsf C_Za-h_Z\widetilde D_Z(g_0\mathsf C_Za)$ satisfies
\begin{equation}\label{eq:c4-10-4}
    \|D_Zq_Z(a)\|\leq Cg_0(1+r),\qquad\|D_Z^lD_a^kq_Z(a)\|\leq C_{l,k}g_0^k
\end{equation}
for $l=0,1$ and $1\leq k\leq2K+1$, $K$ the fixed row input count of Section~\ref{sec:c4-10-4}. These are joint background/young-field derivative bounds; they are not the assertion that the finite list of phase-only derivative constants of Lemma~\ref{lem:c2-uniform-chart} contains them.

Analytic traces of $X$ and $X^{-1}$ extend $\operatorname{Re}\operatorname{tr}X$ from unitary fields, where it equals $\operatorname{tr}(X+X^{-1})/2$; the energy and relative gauge expressions are therefore jointly analytic finite word functions. For the local energy function $E_Z(s)$ in the dimensionless free phase $s$, the compensated primitive has the Taylor-remainder form
\begin{equation}\label{eq:c4-10-5}
    p^{\mathrm E}_Z(a)=-\frac{g_0}{2}\int_0^1(1-t)^2D_s^3E_Z(tg_0a)[a,a,a]\,\dd t\;.
\end{equation}
Its first background derivative has the same factor $g_0$, since $D_ZD_s^3E_Z$ is uniformly bounded on the smaller joint domain; hence $|p^{\mathrm E}|+\|D_Zp^{\mathrm E}\|\leq Cg_0(1+r)^3$, the relative means and the soft-gauge term being included in $E_Z$. The Haar function $\log(\sigma(q)/\sigma(0))$ is analytic in $q$ with an order-two zero, so composed with $q_Z$ it and its $Z$-derivative are at most $Cg_0^2(1+r)^2$. The constraint-Jacobian logarithm is $\log\det(\id-h_ZD_A\widetilde D_Z)$ on a matrix ball of radius $<1/2$; its value and $Z$-derivative are at most $Cg_0(1+r)$, as $D_A\widetilde D_Z=O(g_0(1+r))$ and $D_ZD_A\widetilde D_Z$ has the same order, and the real determinant is positive on that ball, so the analytic logarithm restricts to the real logarithm of Lemma~\ref{lem:c2-uniform-chart}(iii). Summing the finite primitive types assigned to one host gives the host derivative bound with $C^{\partial}_0=N_{\mathrm h}\max(C_{\mathrm p},C^{\partial}_{\mathrm p})e^{\kappa(B_{\mathrm h}+4)}$ of Section~\ref{sec:c4-7-1}; this constant and the finite source derivative constants are chosen after $M$ and $\tau_{\mathrm b}$, before $g_0$, and no earlier Mayer, walk or reserve choice depends on them.

\subsubsection*{Differentiated fixed walks and exact locality}\label{sec:c4-10-2}
Use the series \eqref{eq:c-weighted-walk-series} with its parameters $s_H=2h_+$, $\mathsf A_H=\id-H/s_H$, $\mathsf P_H=\mathsf A_H^{n_*}$, $q_H=1-\gamma/s_H$, $\beta=V_*q_H^{n_*}$, $a_*=e^{81\kappa_1}$ and $n_*$, fixed from the common input bounds and not re-evaluated at the varied background. Include every geometrically allowed tuple of bond indices, including coefficients vanishing at a particular background, so that differentiation does not change the index set. The weights $w_\omega(\sigma)$ and domains $D(\omega)$ depend only on the labels and the fixed geometry. Let $c_H$ bound the Schur row and column norms of $\mathscr D_\omega H/\|\omega\|_\infty$, supplied by the finite analytic entries of Section~\ref{sec:c4-10-1}. Then $\mathscr D_\omega\mathsf A_H=-\mathscr D_\omega H/s_H$ and $\mathscr D_\omega\mathsf A_H^j=\sum_{l=0}^{j-1}\mathsf A_H^l(\mathscr D_\omega\mathsf A_H)\mathsf A_H^{j-1-l}$, a block sum of which is bounded by $V_jjq_H^{j-1}c_H\|\omega\|_\infty/s_H$. Put $d_*=V_*n_*q_H^{n_*-1}c_H/s_H$ and let $d_{\mathrm{ini}}$ be the maximum of the corresponding bounds for $j<n_*$. Differentiating the grouped walk products gives the absolute Schur bound
\begin{equation}\label{eq:c4-10-6}
    \|\mathscr D_\omega S_{Z_0}(\sigma)\|_{\mathrm{Schur}}\leq C^{\partial}_{\mathrm w}\|\omega\|_\infty,\qquad
    C^{\partial}_{\mathrm w}=s_H^{-1/2}n_*\Bigl(\frac{a_*d_{\mathrm{ini}}}{1-a_*\beta}+\frac{a_*^2V_*d_*}{(1-a_*\beta)^2}\Bigr)\;,
\end{equation}
the denominators positive because $a_*\beta\leq1/4$ (\eqref{eq:fixed-kernel-grouping}); the same bound holds on the spatial Cauchy circles. The derivative of $C_{E_0}$ is $-C_{E_0}(\mathscr D_\omega H_{E_0})C_{E_0}$ and that of $\Gamma_{E_0}$ is the product rule on $\iota_{E_0}^*H\Pi_{I\setminus E_0}S_{Z_0}$ (\eqref{eq:fixed-kernel-C-Gamma}); their operator norms are fixed constants times $\|\omega\|_\infty$.

For a selected final domain $Z$ the spatial variables outside $Z$ are zero and the protected seed enlargement $Z_0'$ lies in $Z$; a walk with a coefficient domain meeting a cube outside $Z$ has a zero spatial factor, which remains zero after background differentiation. Every surviving walk, including every hidden fine step in its grouped powers, has its coefficient stencil inside its declared domains by the construction of $D_b$ (Section~\ref{sec:fixed-first-kernel}). The restricted inverse $C_{E_0}$ consults only entries on the seed $E_0$, included in the comparison rectangle; it is not a global inverse restricted afterwards, and the normalised Gaussian determinant is $\det C_{E_0}$, not a determinant of $H$ on all of $I$. All potential and source stencils and every constituent vacuum domain of $c_W$ lie in $Q_W$. These facts prove the locality used at $t=1$ in Lemma~\ref{lem:c4-9-1}, with the fixed regional $I$: no surviving selected coefficient consults the background outside $Q_W$, and no field-dependent global spectral quantity appears among the recipe parameters. The common full Gaussian prefactor $\mathfrak n_\xi$ has cancelled inside the exact conditional ratio defining $F_\xi(0)$ (\eqref{eq:fixed-probe-centred-source}); that cancellation does not cancel $\mathsf w_\xi$ or $\mathcal Z_0$.

\subsubsection*{The complex-Gaussian moment payment}\label{sec:c4-10-3}
On a selected component write $E$ for its seed carrier $E_D$, $J_Z$ for the auxiliary carrier $J_D$ of Lemma~\ref{lem:component-blocks}, $H_E=\iota_E^*H\iota_E$, $C_E=H_E^{-1}$ and $\Gamma=\Gamma_1+i\Gamma_2$ for the block of $\Gamma_{E_0}(\sigma)$, the pairings complex bilinear. Before cutoffs and Mayer factors the joint density with respect to real Lebesgue measure $\dd B\,\dd X$ is the two centred Gaussian normalisations times
\begin{equation}\label{eq:c4-10-11}
    \exp\Bigl[-\frac12\langle B,H_EB\rangle-\langle B,\Gamma X\rangle-\frac12\langle\Gamma X,C_E\Gamma X\rangle-\frac12\|X\|^2\Bigr]\;,
\end{equation}
call it $G_\sigma$. Its columns outside $J_Z$ vanish identically in $\Gamma$ and its derivative by Lemma~\ref{lem:component-blocks}, so the auxiliary standard Gaussians integrate to one and no moment cost proportional to $|I|$ arises. With $\alpha=\alpha_G$ and $C_\alpha=(H_E-\alpha\id)^{-1}$, the absolute density times $e^{\alpha\|B\|^2/2}$ is a positive real Gaussian with the original determinant prefactor; in the variables $y=B+C_\alpha\Gamma_1X$ its exponent is
\begin{equation}\label{eq:c4-10-12}
    -\frac12\langle y,(H_E-\alpha)y\rangle-\frac12\langle X,(\id-T_\alpha)X\rangle\;,\qquad T_\alpha=\Gamma_1^{\mathsf T}(C_\alpha-C_E)\Gamma_1+\Gamma_2^{\mathsf T}C_E\Gamma_2\;,
\end{equation}
the reserve matrix of Section~\ref{app:fixed-kernel-payment}. With the bounds $H_E-\alpha\geq\gamma/2$, $\|T_\alpha\|\leq1/4$ and $\|\Gamma_1\|\leq A_*$ of Lemma~\ref{lem:gaussian-payment} and
\begin{equation}\label{eq:c4-10-13}
    c_{\mathrm G}=\frac{\min(\gamma/2,3/4)}{2(1+2A_*/\gamma)^2}>0\;,
\end{equation}
the real quadratic form is at least $c_{\mathrm G}(\|B\|^2+\|X\|^2)$. Its total unnormalised mass is the determinant product bounded by $e^{N_1(Z)}$ in Lemma~\ref{lem:gaussian-payment}(ii), and its normalised covariance is at most $c_{\mathrm G}^{-1}\id$. With $d=d_G(|E|+|J_Z|)$,
\begin{equation}\label{eq:c4-10-14}
    \int(1+\|B\|^2+\|X\|^2)e^{\alpha_G\|B\|^2/2}|G_\sigma(B,X)|\,\dd B\,\dd X\leq(1+d/c_{\mathrm G})e^{N_1(Z)}\;,
\end{equation}
and $d\leq8d_G(LM+1)^4N_1(Z)$, so the loss is polynomial in the component count with a fixed $M$-dependent constant; it uses the positive $3/4$ margin in $\id-T_\alpha$, not a new exponential reserve. The logarithmic derivative of the Gaussian normalisation contributes $\operatorname{Tr}(C_E\mathscr D_\omega H_E)/2$; the exponent derivative contributes $-\langle B,(\mathscr D_\omega H_E)B\rangle/2$, $-\langle B,(\mathscr D_\omega\Gamma)X\rangle$ and $-\mathscr D_\omega\langle\Gamma X,C_E\Gamma X\rangle/2$ with $\mathscr D_\omega C_E=-C_E(\mathscr D_\omega H_E)C_E$; each is bounded by $C\|\omega\|_\infty(d+\|B\|^2+\|X\|^2)$ by Section~\ref{sec:c4-10-2}. Hence \eqref{eq:c4-10-14} proves the differentiated Gaussian payment $C_MN_1(Z)\|\omega\|_\infty e^{N_1(Z)}$ on the same Cauchy circles and carriers, all normalisers and the compensator differentiated. The protected cutoff domain is fixed throughout; no cutoff translation or surface term is suppressed in this derivative.

\subsubsection*{Source remainder bounds}\label{sec:c4-10-4}
Let $\mathsf J=(b_1,\ldots,b_q)$ be distinct selected labels and let $a'$ denote all other selected root variables. The mixed fundamental theorem of calculus gives the exact identity
\begin{equation}\label{eq:c4-10-7}
    \Delta_{\mathsf J}f(B,a')=\int_{[0,1]^q}D_{b_1}\cdots D_{b_q}f\Bigl(a'+\sum_{j=1}^qs_jB_{b_j}\Bigr)[B_{b_1},\ldots,B_{b_q}]\,\dd\mathbf s\;,
\end{equation}
the sum in the argument meaning the canonical embedding into the free carrier. Let $K$ be a fixed bound for the number of source rows affected by one free label and for the number of inputs of one row. Only the source $f_W(a;h)=\chi(T_W(a)P_W^{-1}h)$, or the original full closed Wilson character, is used; untouched factors are unitary in its representation. The derivative product rule has at most $K^q$ row assignments, and the derivatives within a row have order at most $2K+1$, whose constants \eqref{eq:c4-10-4} are fixed. Consequently, with a fixed $C_\chi$ enlarged once,
\begin{equation}\label{eq:c4-10-8}
    \|D_{b_1}\cdots D_{b_q}f\|\leq(C_\chi g_0)^q,\qquad\sup|\Delta_{\mathsf J}f|\leq(C_\chi g_0r)^q\;.
\end{equation}
For root $j$ let $P_j$ be its homogeneous degree-$q_j$ projection after taking $\Delta_{\mathsf J_j}$. Subtracting the integrand of \eqref{eq:c4-10-7} at zero root input and integrating its first derivative along the segment $t(\mathbf sB)$ gives $q_j$ terms, each with one additional derivative and one additional selected $B$ factor. Thus, for any set $O$ of roots,
\begin{equation}\label{eq:c4-10-9}
    \sup\Bigl|\prod_{j\in O}(1-P_j)\Delta_{\boldsymbol{\mathsf J}}f\Bigr|\leq u^{q+|O|},\qquad u=C_\chi g_0(1+r)\;,
\end{equation}
the choices of the extra increment, at most $\prod_jq_j\leq2^q$, being absorbed in $C_\chi$. The row-order bound $2K+1$ covers these remainders simultaneously because the roots have disjoint selected labels and a row has at most $K$ inputs. A single background derivative hits either a row coefficient or one of the $L_f$ background occurrences of the closed word; \eqref{eq:c4-10-4} and the product rule give
\begin{equation}\label{eq:c4-10-10}
    \sup\Bigl|\mathscr D_\omega\prod_{j\in O}(1-P_j)\Delta_{\boldsymbol{\mathsf J}}f\Bigr|\leq C_\chi\|\omega\|_\infty(L_f+q)\,u^{q+|O|}\;.
\end{equation}
These are the inequalities used in the commuting-projection cancellation of Lemma~\ref{lem:c4-7-2}. Roots with an empty ordinary selection retain only these remainders under their even Gaussian integration; roots with an ordinary selection use their independent Cauchy vanishing. This recovers the product $u^{q_j}v^{q_j\bmod2}$, and its one-background-derivative version, before any total variation majorant is summed; every term remains a closed contraction with the same fixed $h$ and the original word order.

\subsubsection*{Tree gauge on a comparison rectangle}\label{sec:c4-10-5}
\begin{lemma}[tree gauge]\label{lem:c4-10-5}
Let $Q$ be an injectively lifted fine rectangle of largest side $R\geq1$ with a root $o\in Q$, and let $\delta_Q(U)=\max_{p\subset Q}|U(\partial p)-\id|_\sigma$. For $x\in Q$ let $P_x$ run from $o$ to $x$ in coordinate order, each coordinate run oriented by its displacement; these paths form a rooted tree. Put $g(o)=\id$, $g(x)=U(P_x)$, so that $U^g(b)=U(P_x)U(b)U(P_{x'})^{-1}$ for $b=(x,x')$ is the based closed transport at $o$ of the fundamental loop of $b$. Then
\begin{equation}\label{eq:c4-10-15}
    U^g(b)=\prod_{j=1}^{m_b}G_jU(\partial p_j)^{\epsilon_j}G_j^{-1},\qquad m_b\leq3R,\qquad\epsilon_j\in\{1,-1\}\;,
\end{equation}
with every plaquette $p_j$ in $Q$, and
\begin{equation}\label{eq:c4-10-16}
    |U^g(b)-\id|_\sigma\leq3R\,\delta_Q(U)\;.
\end{equation}
There is a constant $C_{\mathrm{tg}}$, depending only on the fixed group chart and $\tau_{\mathrm b}$, such that $C_{\mathrm{tg}}R^2\delta_Q(U)\leq\tau_{\mathrm b}/2$ implies that every $U^g(b)$, $b\subset Q$, lies in the group chart, with principal phase $B_b$ satisfying
\begin{equation}\label{eq:c4-10-17}
    \max_{b\subset Q}h(B_b)\leq C_{\mathrm{tg}}R^2\delta_Q(U)\leq\tau_{\mathrm b}/2\;.
\end{equation}
\end{lemma}

\begin{proof}
For a bond of direction $\mu$, move its last $\mu$-step past the later coordinate runs of $P_x$. Each interchange with a perpendicular fine edge replaces the ordered word by one plaquette transport conjugated by the preceding word; all plaquettes stay in $Q$, and the number of interchanges is at most $\sum_{\nu>\mu}|x_\nu-o_\nu|\leq3R$. Negative coordinate runs reverse a plaquette orientation without altering this count. Induction on the interchanges gives the exact nonabelian word \eqref{eq:c4-10-15}, the order being that of the step interchanges and $G_j$ the preceding transport to the plaquette, so every factor is a conjugated closed plaquette; no commutative plaquette replacement is used. Unitary invariance of $|\cdot|_\sigma$ and telescoping give \eqref{eq:c4-10-16}, with a constant independent of $R$. Norm conversion to the operator norm and the fixed local group logarithm give $h(\log U^g(b))\leq3C_G\sqrt N\,R\,\delta_Q$ whenever that distance is inside the group chart; since $R\geq1$, requiring $C_{\mathrm{tg}}\geq3C_G\sqrt N$ and $C_{\mathrm{tg}}\geq6\sqrt N\tau_{\mathrm b}/r_G$ makes $C_{\mathrm{tg}}R^2\delta_Q\leq\tau_{\mathrm b}/2$ sufficient for the chart condition and for \eqref{eq:c4-10-17}. The constants do not grow with $b$ or the scale $R_1$. If the sufficient condition fails, the two-endpoint coefficient bound is used instead of the interpolation, so no smallness of the box is imposed as a hypothesis. The root $g(o)=\id$ leaves the complementary $h$ fixed in every closed contraction.
\end{proof}

\subsection{Identification of the centred coefficient and its local extension}\label{sec:c4-11}
This section concerns $c_W$ of Section~\ref{sec:c4-6-1}, with $W$ fixed on a covered branch; its first caller is the interpolation identity of Lemma~\ref{lem:c4-9-1}. The conclusions retain the hypotheses of Sections~\ref{sec:sourced-effective-interaction} and~\ref{sec:joint-extraction} and Appendix~\ref{app:background-estimates}, with their fixed charts, carriers, cutoffs and parameters, and do not identify the regional scalar $S^\circ_{\xi,C}$ with the perimeter/corner scalar.

\subsubsection*{Which exterior dependence is removed}\label{sec:c4-11-1}
Write $s$ for the exterior-response parameter and $t$ for the background-path parameter. Section~\ref{sec:sourced-effective-interaction} defines
\begin{equation}\label{eq:c4-11-1}
    K_{\xi;s}(a)=\Theta_\xi(a)\exp\Bigl(-\frac12\langle a,H_{\xi,II}a\rangle-s\langle a,H_{\xi,IJ}A_{\mathrm e}\rangle+\sum_{\mathfrak p\ \mathrm{near}}\mathfrak p(a+sA_{\mathrm e})\Bigr)\;,
\end{equation}
with $U_1$ held fixed in the $s$-interpolation. The collar identity and the boundary-response identity give, with $F_\xi(s)$ defined with the same Wilson function $f_\xi$,
\begin{equation}\label{eq:c4-11-2}
    \mathcal J^{\mathrm a}_\xi[1]=e^{c_\xi}I_{\xi;1},\qquad F_\xi(1)=F_\xi(0)+\mathcal B_\xi[f_\xi]\;.
\end{equation}
On a covered branch every contour row has its entire free-input set in $I$. Since $\Psi_\xi$ is the identity on $I$ and $A_{\mathrm e}$ vanishes there, row locality implies, for every $a$ in the integration box, that every contour link in $f_\xi(a)$ is its reconstruction from $a$ alone at background $U_1$: this is Lemma~\ref{lem:covered} with $a$ retained instead of set to zero, and it uses no estimate. Thus both the source and $K_{\xi;0}$ have zero retained free input, while the dependence of $U_1$ itself on the exterior determining data remains. Every selected measure in $c_W$ is constructed from $K_{\xi;0}$: its potentials are the near primitives at $a$, its Hessian is $H_{\xi,II}$ and its cutoff is $\Theta_\xi$. The factors involving $\Psi_\xi(A_{\mathrm e})$, the far primitives and the boundary-map Jacobian are in $c_\xi$, and the interaction between $a$ and $A_{\mathrm e}$ is accounted for by $\mathcal B_\xi$; they are not factors of $c_W$. Consequently the physical comparison keeps
\begin{equation}\label{eq:c4-11-3}
    \frac1{\mathcal Z_0}\int\mathcal O\bigl[e^{c_\xi}I_{\xi;1}F_\xi(0)\bigr]\dd V+\frac1{\mathcal Z_0}\int\mathcal O\bigl[e^{c_\xi}I_{\xi;1}\mathcal B_\xi[f_\xi]\bigr]\dd V\;,
\end{equation}
and does not replace $I_{\xi;1}$ by $I_{\xi;0}$. This is the role of the boundary separation in CRE (1.26)--(1.30), not a claim that the exterior input of the original conditional integral vanishes.

\subsubsection*{Covariance of the selected coefficient}\label{sec:c4-11-2}
For a site gauge $g$ let $R_ga(b)=\operatorname{Ad}_{g(b_-)}a(b)$ on free bonds; $R_g$ is orthogonal for $h$, preserves each free bond subspace and commutes with geometric restrictions. The row-covariance identities of Lemma~\ref{lem:hessian-gauge-locality} give $q_{U^g}(R_ga)=R_gq_U(a)$, branch included: the small row solution transforms to a solution of the transformed constraint in the same invariant small ball, and uniqueness there identifies it with the selected solution. The joint fixed point of Section~\ref{sec:c4-10-1} is identified with this solution by choosing its phase radius so that its $O(\|A\|^2)$ bound lies inside the uniqueness ball of Lemma~\ref{lem:c2-uniform-chart} (Section~\ref{sec:c4-11-5}); the inverse and mean branches are those fixed in the row construction.

The action of each plaquette is invariant and each relative soft-gauge mean is conjugated at its base, so the constant, linear and quadratic Taylor coefficients of the energy primitives transform with their arguments, the force--constraint term included; subtracting them preserves the covariance of the compensated primitives even at noncritical backgrounds. The Haar density is conjugation invariant. The constraint-Jacobian endomorphism transforms by conjugation between the same free and designated spaces, so its determinant and its selected logarithm are unchanged, the logarithm branch being fixed by continuation from zero within the nonvanishing chart. Hence each primitive and each host sum $\mathbf V_\xi(Y)$ is invariant under the simultaneous transformation of background and free variables.

The Hessian, each restricted seed inverse and every fixed walk transform by $R_g$ on their indices, by the entry identities of Lemma~\ref{lem:hessian-gauge-locality} and the geometric walk formula; all geometric choices, Cauchy variables and Mayer parameters are unchanged. In the selected integral change variables $B\mapsto R_gB$, $X\mapsto R_gX$: Lebesgue and standard Gaussian measures, the two allowed cutoff norms (\eqref{eq:marginal-cutoff-invariance}), the conditional Gaussian determinant and the cross and compensator terms are preserved, so each selected measure is pushed forward by $R_g$, and in the probe formula $\delta_B-\delta_0$ is pushed to $\delta_{R_gB}-\delta_0$. Summing selections,
\begin{equation}\label{eq:c4-11-4}
    \widehat\nu^{\mathrm f}_{U^g,D}=(R_g)_*\widehat\nu^{\mathrm f}_{U,D}\;.
\end{equation}
The vacuum activities, their Ursell products and $w_\xi(W)$ are scalar invariants, the incompatibility graph and every numerical combinatorial factor being field independent. Both $T_WP_W^{-1}$ and the complementary $h$ transform at the initial interval vertex $o$, so
\begin{equation}\label{eq:c4-11-5}
    c_W(U^g;g(o)hg(o)^{-1})=c_W(U;h)\;.
\end{equation}
The rooted comparison gauge has $g(o)=\id$. Open transports occur only in this equality inside the closed character; no norm of an open transport is used.

\subsubsection*{Domain and endpoint}\label{sec:c4-11-3}
Section~\ref{sec:c4-8-4} defines the small interior groups by \eqref{eq:c4-8-9}. The support of such a group includes every root domain, each vacuum-cluster domain occurrence, their coefficient halos and the whole contour interval $\mathcal H(W)$ with its closing transport; the hull-extent bound is needed here, since a box enclosing only the random inputs would not suffice. Under \eqref{eq:c4-8-9} the enclosing rectangle has diameter at most $C_{\mathrm{box}}LMn(W)$, lies within $b/2$ of a source contact and is injectively liftable under the period convention of Section~\ref{sec:c4-9-2}; on the far-history event the box and its halos lie in the regular region. All other groups, including winding or boundary-reaching groups, stay in the large-domain tail of Section~\ref{sec:c4-8-4}. This is the small-local-domain versus large/distant-domain separation of RG1 (3.5)--(3.9) and of CRE's boundary separation; no interpolation is asserted for a group in the tail.

On a small interior group first use its rooted tree gauge. If $C_{\mathrm{tg}}\operatorname{diam}(Q_W)^2\delta_{Q_W}(U_1)\leq\tau_{\mathrm b}/2$, define $B_W$ and $U_{W,t}$ as in \eqref{eq:c4-9-1}. With $\tau_{\mathrm b}\leq\tau_L/4$ and $c_L\tau_{\mathrm b}\leq\gamma_L/4$ (Lemma~\ref{lem:c4-7-3}) the entry Lipschitz estimate and the flat compression gap supply the two-sided Hessian bounds throughout the path. That the path need not consist of constrained minima is allowed only because its compensated primitive formulas are defined on the joint chart; physical criticality identifies those formulas at the endpoint, not at intermediate $t$.

For each selected coefficient Section~\ref{sec:c4-10-2} fixes all walk parameters and restricts every surviving walk and coefficient stencil to its final domain; the seed inverse is the inverse on the seed, not the restriction of a global inverse. Thus, on the supports included in $Q_W$, the $t=1$ recipe equals the gauge-transformed physical centred recipe, its values on bonds outside $Q_W$ cannot enter the coefficient, and \eqref{eq:c4-11-5} returns the coefficient to the original gauge. At $t=0$ the recipe is the regional reference recipe with exactly the same $I$, $\Omega_1$, $W$, cutoffs and constants. This yields the endpoint identities
\begin{equation}\label{eq:c4-11-6}
    c_W(U_{W,1};h)=c_W(U_1;h),\qquad c_W(U_{W,0};h)=a_W\chi(h)\;,
\end{equation}
equalities of the selected coefficient, not of the outer history density. If the tree-gauge phase condition fails, the two-endpoint majorant of Section~\ref{sec:c4-6-3} is used; if the box condition fails, the whole group is in the tail. Neither case is assigned an endpoint identity it does not satisfy.

For differentiation under the selected integrals, the norm of $X$ in Section~\ref{sec:c4-10-3} is the norm of $X$ restricted to $J_Z$; all other auxiliary columns integrate out with mass one and have zero derivative. The common strictly positive $c_{\mathrm G}$ supplies a background-independent Gaussian majorant for that finite-dimensional integral and its first derivative, and the selected sums and vacuum occurrence sums use the summable majorants of Lemma~\ref{lem:c4-7-4} and Section~\ref{sec:c4-8-4}. These are the dominated-convergence hypotheses of Lemma~\ref{lem:c4-9-1}; the group derivative includes the derivative of $w_\xi(W)$. RG1 (3.21), (4.35)--(4.36) estimate changes of reconstruction and domain rather than declaring them zero; no such change is made in the identities above, the regional carrier and each local recipe being fixed. A failure of the stated finite-support or covariance identity would invalidate the endpoint step and would require a retained comparison error, which the tree-gauge estimate alone could not absorb.

\subsubsection*{Endpoint conventions and the lifting claim}\label{sec:c4-11-4}
The endpoint statement is restricted to covered far histories and the small interior groups of Section~\ref{sec:c4-8-4}. Extend the rooted site gauge from $Q_W$ to the whole torus by the identity on sites outside $Q_W$. Every background bond consulted by the coefficient has both endpoints inside $Q_W$: in defining $Q_W$ the enclosing rectangle is enlarged to contain both endpoints of each Hessian stencil, row set, block-mean path, plaquette and interval or closing-path bond, an enlargement that is part of the fixed halo included in $C_{\mathrm{box}}$. Boundary bonds of the site-gauge extension are not consulted by the coefficient.

Only the finite formula $w_\xi(W)=(-1)^{k(W)}/k(W)!$ times the product of the specified vacuum cluster occurrences is varied along $U_{W,t}$; neither the global partition function nor the global exclusion ratio $q_\xi(\mathcal A)$ is an operand of the interpolation. Lemma~\ref{lem:c4-7-4} supplies the sum of the occurrence derivative majorants and \eqref{eq:c4-8-10} applies the finite product rule; the exclusion ratio was expanded at the original background before the group construction. Thus no identity or positivity statement for a global partition function at $U_{W,t}$ is needed to identify either endpoint. The regional scalar $a_W$ is the one defined in Section~\ref{sec:joint-extraction} from $w^\circ_\xi(W)$ and the same root measures at the identity background (\eqref{eq:part1-reference-group}); it is not an infinite-volume coefficient, and its closed Schur identity \eqref{eq:part1-closed-schur} is the $t=0$ identity used here.

For the lifting claim, represent each constituent connected domain by a tree of its constituent coarse cubes and adjoining faces and root the union at a source contact. Each root or cluster-domain tree has at most its number of cubes minus one edges; incompatibility joins have bounded range, and the finite reconstruction halos add a fixed range at their contacts. The contour-hull extent bound bounds the additional contour edges joining the components by $CLMn(W)$. The resulting connected bond network has a spanning traversal of length at most $CLMn(W)$ with $C$ fixed. If this is less than $N_{\min}/4$, lift the traversal from its root: every lifted vertex lies within that distance of the root, and two lifts of the same vertex could differ only by a nonzero period vector, of length at least $N_{\min}$, while the two paths giving them have total length less than $N_{\min}/2$, a contradiction. The enclosing coordinate rectangle and its stipulated halos therefore project injectively. $C_{\mathrm{box}}$ is chosen to include these constants; with \eqref{eq:c4-8-9} and \eqref{eq:c4-9-3} the small-group criterion implies this sufficient lifting condition, and failure to lift cannot occur in the small-group class. No curvature estimate for a winding loop is used. In applying the entry estimates, $\tau_{\mathrm b}$ is taken small enough for both the $h$-maximum and the stated entry-chart norm, using $h\leq\sigma\leq\sqrt Nh$, before $g_0$ is chosen. Geometrically allowed zero walks re-index the same series and do not change its value or support domains.

\subsubsection*{Source and radius specifications}\label{sec:c4-11-5}
The imported mean covariance is RG1 (0.6), $\mathsf M(\{uU_jv\})=u\mathsf M(\{U_j\})v$ for the specified mean on its small-diameter domain, which RG1 (0.10) asserts for the selected mean; it is used for unitary site gauges with no smallness restriction on the gauge values, the relative distances and the real chart domains being preserved. The cutoff invariance is \eqref{eq:marginal-cutoff-invariance}.

The curvature input of Section~\ref{sec:c4-8-4} is Lemma~\ref{lem:c2-plaquette-deviation}. For a plaquette of $Q_W$ choose a vertex $x\in\Lambda_1$; within the $L$-block containing $x$ choose a neighbouring vertex still in that block ($L\geq3$). That internal fine bond is free, since designated bonds join distinct blocks, and belongs to $I$ because it has the endpoint $x\in\Lambda_1$; so the plaquette has a bond within two fine-bond metric units of $I$, within the $3R_{\mathrm c}$ the lemma requires. This yields the bound $\delta_{Q_W}(U_1)\leq C\varepsilon_1$, with the fixed conversion between the lemma's operator norm and the norm $|\cdot|_\sigma$ of Lemma~\ref{lem:c4-10-5}.

For the branch identification of Section~\ref{sec:c4-11-2} let $C_{\mathrm{D,joint}}$ be the constant in $\|\widetilde D_Z(A)\|\leq C_{\mathrm{D,joint}}\|A\|^2$ on the joint chart of Section~\ref{sec:c4-10-1}. After choosing that chart reduce $\theta_0$ so that $2\theta_0\leq\vartheta_*/2$ and $4C_{\mathrm{D,joint}}\theta_0^2<\rho_{\mathrm d}$. At real backgrounds the joint solution for $\|A\|<2\theta_0$ then lies in the uniqueness ball of Lemma~\ref{lem:c2-uniform-chart} and is its selected solution. The coupling threshold is chosen after these radii so that the phase inputs $g_0\mathsf C_UB$ of the enlarged free box remain in $\|A\|<\theta_0$; no expansion parameter is enlarged after this choice.

\subsection{Quantitative assembly at the signed physical caller}\label{sec:c4-12}
This section proves the first-step estimate for $E_{\mathrm{def}}$ of \eqref{eq:c4-1-1}. It uses the hypotheses of Sections~\ref{sec:sourced-effective-interaction} and~\ref{sec:joint-extraction} and Appendix~\ref{app:background-estimates}, the compatible even-period and square-fit conventions of Section~\ref{sec:c4-9-2}, and the same irreducible normalised character. Constants may depend on the fixed group, the character, $L$, $M$ and the fixed expansion and chart choices, but not on the coupling, the square length, the compatible torus size or the history; the coupling is chosen last. The regional scalar $S^\circ_{\xi,C}$ is retained; no identification with a perimeter/corner scalar is asserted.

\subsubsection*{The joint derivative supplied to the group coefficient}\label{sec:c4-12-1}
The quantitative derivative is obtained from Lemmas~\ref{lem:c4-7-1} and~\ref{lem:c4-7-2} and Section~\ref{sec:c4-10}. For each selected root the source is $\Delta_{\mathsf J}f$, a closed character difference; \eqref{eq:c4-10-9} bounds its mixed Taylor remainder by $u^q$ and supplies an extra $u$ for each odd leading term removed by reversal. The root's Gaussian derivative is even in its joint $(B,X)$ variables, including its determinant and compensator derivatives, and a derivative of a selected ordinary potential carries a factor $\zeta$ and vanishes at $\zeta=0$; so the independent-root parity/Cauchy argument of Lemma~\ref{lem:c4-7-2} applies after one background derivative. The differentiated host sum \eqref{eq:c4-7-5} bounds a differentiated potential without dividing by that potential; \eqref{eq:c4-10-6} sums the derivatives of all geometrically indexed walks on the same spatial contours; \eqref{eq:c4-10-14} pays each Gaussian derivative by $C_MN_1(D)$ times the same $e^{N_1(D)}$ determinant majorant, with $X$ restricted to $J_Z$, all other auxiliary variables integrating to one. Host and Gaussian derivatives therefore insert one factor $N_1(D)$, not one new constant per selected label. The source derivative inserts the number $L_f$ of varying contour/closing links plus the number of selected labels, which Section~\ref{sec:c4-7-1} bounds by $C_M\sum_DN_1(D)$. The resulting joint estimate is
\begin{equation}\label{eq:c4-12-1}
    |\mathscr D_\omega\mathfrak Q_\xi(\mathcal A;f)|\leq C_\chi\|\omega\|_\infty\Bigl(L_f+\sum_{D\in\mathcal A}N_1(D)\Bigr)\prod_{D\in\mathcal A}\rho\,m(D)\;,
\end{equation}
with $\rho$ and $m(D)$ of \eqref{eq:c4-4-8} and Lemma~\ref{lem:activity-bounds}; it is used on the fixed coefficient path of Section~\ref{sec:c4-11} and differentiates neither an outer history weight nor a global exclusion ratio. For a vacuum occurrence $\mathfrak c$ the selected-integral derivative gives \eqref{eq:c4-7-8}; differentiating the finite product $w_\xi(W)$ by \eqref{eq:c4-8-10} and adding the root-integral derivative yields, uniformly for $h\in G$,
\begin{equation}\label{eq:c4-12-2}
    |c_W(U;h)|\leq M(W),\qquad|\mathscr D_\omega c_W(U;h)|\leq C_\chi\|\omega\|_\infty\bigl(n(W)+|\mathcal H(W)|\bigr)M(W)\;.
\end{equation}
The undifferentiated estimate holds at the original physical background and at the regional flat reference. $M(W)$ contains $\rho$ for every marked root and the original factorials; polynomial factors have not been summed or hidden in $M(W)$, and the factor from the relative interval's inverse word, at most a fixed multiple of $|\mathcal H(W)|$, is included in $C_\chi$.

\subsubsection*{Payment of the local and tail losses}\label{sec:c4-12-2}
\begin{proof}[Proof of Lemma~\ref{lem:c4-6-4}]
Write $s=\mathfrak s(W)\geq1$, so that $\mathfrak a_W=\eta s$. The fixed hull and box bounds give $n(W)+|\mathcal H(W)|\leq CLMs$ and $\operatorname{diam}(Q_W)\leq CLMs$. The endpoint identities \eqref{eq:c4-11-6}, the path integral \eqref{eq:c4-9-2} with the derivative bound \eqref{eq:c4-12-2} along it, and the plaquette estimate $\delta_{Q_W}(U_1)\leq C\varepsilon_1$ of Section~\ref{sec:c4-11-5} with the phase bound \eqref{eq:c4-10-17} therefore give, for a small interior group passing the phase test,
\begin{equation}\label{eq:c4-12-3}
    \mathfrak d_W(U_1)\leq C_\chi\varepsilon_1s^3M(W)\;.
\end{equation}
If the phase test of such a group fails, then $C_{\mathrm{tg}}\operatorname{diam}(Q_W)^2\delta_{Q_W}>\tau_{\mathrm b}/2$; with $\delta_{Q_W}\leq C\varepsilon_1$ and $\operatorname{diam}(Q_W)\leq CLMs$ this gives $1\leq C\varepsilon_1s^2$ with constants fixed before the coupling, so the two undifferentiated endpoint bounds \eqref{eq:c4-12-2} give \eqref{eq:c4-12-3} again, as $s\geq1$. No curvature comparison is used for a group outside the small interior class; for such a group
\begin{equation}\label{eq:c4-12-4}
    \mathfrak d_W(U_1)\leq2M(W),\qquad s\geq T_b:=\frac{b}{4C_{\mathrm{box}}LM}\;.
\end{equation}
For the local polynomial payment let
\begin{equation}\label{eq:c4-12-5}
    C_{\eta,3}=\sup_{s\geq1}s^3e^{-(31\eta/8)s}<\infty\;,
\end{equation}
so that $s^3e^{\eta s/8}\leq C_{\eta,3}e^{4\eta s}$; for the tail, $s\geq T_b$ gives $e^{\eta s/8}\leq e^{-2\eta T_b}e^{4\eta s}$. Hence the two weighted pin estimates of Lemmas~\ref{lem:c4-8-2} and~\ref{lem:c4-8-3} imply
\begin{equation}\label{eq:c4-12-6}
    \sum_WK_\chi\mathfrak d_W(U_1)e^{\mathfrak a_W/8}\leq C_\chi\bigl(\varepsilon_1+e^{-2\eta T_b}\bigr)\sum_WM(W)e^{4\eta\mathfrak s(W)}\leq C_\chi n_C\rho\bigl(\varepsilon_1+e^{-cb/(LM)}\bigr),\qquad c=\frac{\eta}{2C_{\mathrm{box}}}\;.
\end{equation}
The last summation uses that every $W$ has a nonempty contour interval: summing the contour-pin estimate \eqref{eq:c4-6-5} over the $n_C$ traversals counts every group at least once. The cubic moment and the tail use the existing $4\eta$ weight, not an additional size-dependent hypothesis or a loss in the scalar $S^\circ_{\xi,C}$. The exceptional whole-contour merge is the one paid in Lemma~\ref{lem:c4-8-3}, where the long class pays both the arbitrary extra components and the whole-contour weight. This is \eqref{eq:c4-6-8}.
\end{proof}

\subsubsection*{The signed family sum and the physical expectation}\label{sec:c4-12-3}
\begin{proposition}[the signed defect bound]\label{prop:c4-12-3}
Under the hypotheses stated at the start of this section, with $\rho$ of \eqref{eq:c4-4-8}, $\rho=O(g_0^2(1+r)^4)$, $\varepsilon_1=g_1p_0(g_1)$, $b=\lfloor LMR_1/16\rfloor$, $\pi_*=\min(p_0(g_0),p_0(g_1))$ and the constants $C'_L$, $c_*$ of \eqref{eq:c4-2-2} and $C_\chi$, $c$ of \eqref{eq:c4-6-8},
\begin{equation}\label{eq:c4-12-7}
    |E_{\mathrm{def}}|\leq C'_Ln_Ce^{-(c_*/2)\pi_*^2}+\frac1{\mathcal Z_0}\int\mathcal O\Bigl[\mathsf w_\xi\mathbf 1_{A_{\mathrm{cov}}\cap\mathsf N_b^c}|S^\circ_{\xi,C}|\Bigl(e^{C_\chi n_C\rho(\varepsilon_1+e^{-cb/(LM)})}-1\Bigr)\Bigr](V)\,\dd V\;,
\end{equation}
and consequently
\begin{equation}\label{eq:c4-12-8}
    |E_{\mathrm{def}}|\leq C'_Ln_Ce^{-(c_*/2)\pi_*^2}+e^{C_\chi n_C\rho(\varepsilon_1+e^{-cb/(LM)})}-1\;.
\end{equation}
\end{proposition}

\begin{proof}
Lemma~\ref{lem:c4-6-3} supplies the single joint ratio \eqref{eq:c4-6-7}. Combined with the closed-contraction product bound \eqref{eq:c4-6-4}, formed after each $d_W$, the nonempty compatible-family sum is bounded by the exponential series of the summable one-group weight \eqref{eq:c4-6-8}, which on covered far histories is \eqref{eq:c4-6-9} (Lemma~\ref{lem:c4-6-5}); the countable-group limit is the dominated finite-species limit of Lemma~\ref{lem:c4-9-2}, with the same positive majorant and the nonzero reference partition function supplied by its convergent logarithm, so no quotient is formed at a zero partition function. Combining the near-history estimate \eqref{eq:c4-2-2} with the positivity of the original history measure gives \eqref{eq:c4-12-7}; all history weights, deferred integrations and the physical normalisation are those of \eqref{eq:c4-1-1}, and the exact source on the left was summed before absolute values were taken. The regional reference scalar is a normalised integral of a character of modulus at most one against its positive reference kernel, so $|S^\circ_{\xi,C}|\leq1$, and the same physical normalisation yields \eqref{eq:c4-12-8}.
\end{proof}

The exponential in \eqref{eq:c4-12-8} is not replaced by its linear term unless its argument is bounded; in particular no assertion of UV summability for a fixed physical loop is made. The conclusion has exactly the hypotheses and quantitative scope stated at the beginning of this section.

\subsubsection*{Fixed reserve conventions}\label{sec:c4-12-4}
The exponential vacuum estimate used in Lemma~\ref{lem:c4-8-2} holds with $n(\mathfrak c)/2$ as well as with $n(\mathfrak c)/4$: the rooted-tree proof of Lemma~\ref{lem:activity-bounds} applied to the numerical activity $m(D)e^{N_1(D)/2}$ with node cost $N_1(D)/8$ has combined exponent $5/8$, below the $1+6\theta$ of the numerical Kotecký--Preiss hypothesis \eqref{eq:native-source-vacuum-KP-budget}, which gives the first bound of \eqref{eq:c4-7-9}. No reserve of Appendix~\ref{app:background-estimates} is re-spent and no constant fixed before $M$ is changed. Adjacency convention: two $LM$-cubes are in contact when they share a face, an edge or a corner, not only when they intersect; a cube therefore has at most $3^4-1$ contacts, and $3^4$ is the neighbour factor of the footprint-contact sums in Lemmas~\ref{lem:c4-6-3} and~\ref{lem:c4-8-2}.
```

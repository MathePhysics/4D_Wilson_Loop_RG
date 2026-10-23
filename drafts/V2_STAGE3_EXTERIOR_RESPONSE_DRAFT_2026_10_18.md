# Stage 3: exterior response at the first RG step
TeX form (19 October 2026, 22:11): Sections 1-9 are in `WILSON_FIRST_RG_STEP_V3.tex` as the last appendix `app:exterior-chessboard` (Section 10 below; V3 4088 lines CRLF, SHA256 f5c1737e39bd970b after the 28 `\draftref{stage 3, ...}` markers of sec:one-step-insertion were replaced by `\ref` to the appendix labels at 22:16, 163 pages, no undefined references). Review of the translation (from 19 October 2026, 23:38, one subsection per isolated referee packet, `verification/isolated_reviewer/reviews/tr-c3-*-20261019-r1/review.txt`): sec:c3-1 and sec:c3-2 reviewed and the TeX repaired from the reports (V3 SHA256 cdd0a2a50ffb650f, 20 October 00:02); sec:c3-3 and sec:c3-4 reviewed and repaired (V3 SHA256 049c23543dbf8042, 20 October 00:26; lem:c3-7-4 restated for every threshold in (0, ε₀] at 00:20); sec:c3-5 and sec:c3-6 reviewed and repaired (V3 SHA256 5214beb20f7d92d9, 20 October 00:52; in sec:c3-5 the inequality that needed C_S ≤ C_P is replaced by C_S g₀(1+2r) ≤ C_Sγ/(2C_P) from eq:c3-1-2, the factor 2 for the complex source is explicit, and the C¹ hypothesis of lem:ibp is verified); sec:c3-7 and sec:c3-9 reviewed (wave 5B, launched 20 October 02:07 against V3 SHA256 c73335d187e27656, reports tr-c3-7 356 lines and tr-c3-9 355 lines) and repaired (V3 SHA256 87cccdb3b28c872d, 20 October 02:43, 204 pages, no undefined references; sec:c3-9 no longer uses the full-support reading of (B1), its CRE (2.8) comparisons are two-sided and its Gaussian-tail sum is volume-free; lem:c3-7-3 displays 𝗐_ξ = e^{c_ξ}I_{ξ;1} = ∫e^{c_ξ}K_{ξ;1}, lem:c3-7-4 states its group constants and the ε₀-ball hypothesis, prop:c3-7-5 has the constant C_L max(C_resp,χ S_c, 1) and names its thresholds). Every section of this draft has now been reviewed once. 20 October 09:16 (V3 SHA256 5dd43b84ae77377c, 208 pages, no undefined references): the archived-seed dependence is removed; sec:c3-7-1 now contains lem:c3-7-block [block comparison] and lem:c3-7-seed [witnesses for bad tests] (transcribed from the archived seed with the sources re-read: RG1 (0.4)–(0.11), CRE (1.2)–(1.4), (1.8), (1.10), VAR Thm 1, AVG Prop 1), and lem:c3-7-4's proof carries the reflection-positivity display eq:c3-7-rp and the chessboard estimate eq:c3-7-chessboard (Friedli–Velenik Thm 10.11) instead of the archived chessboard section. These new parts were referee-reviewed 20 October (tr-c3-7-seed-20261019-r1, tr-c3-7-chess-20261019-r1, packets carrying the transcribed RG1/CRE/VAR/CMP98 pages): no blocking errors; the non-blocking defects were repaired by 10:46 (V3 SHA256 d3d017eb00120d92, 209 pages, no undefined references): θ ≤ η₀ added to the hypotheses of lem:c3-7-seed, the U_{1,Q} identification restated from CRE p.256 (2.12) and VAR Thm 1 without the unsupported radius 2k_N²L²ε₀, the block-average covariance derived from RG1 (0.4), the bad R₁ bond located in (Q_w^{[2]})^* after CRE (1.18), and the chessboard sketch of lem:c3-7-4 rewritten (reflection positivity at every antipodal site-plane pair, maximiser over tuples with entries from the normalised functions, translation reduction to p ⊂ C₀, the g₀ threshold of lem:c3-7-2 restated). Second-round referees tr-c3-7-seed-20261019-r2 and tr-c3-7-chess-20261019-r2 launched 11:16:25 against V3 SHA256 8845483f56bb7c91; reports pending. The TeX in V3 is authoritative where it differs from the TeX block in Section 10, which is not re-mirrored.

18 October 2026. The conditional-response argument and history-payment argument have received focused isolated Claude reviews. They establish the displayed bounds relative to the stated Stage 1--2 inputs; Section 9 removes the full-cutoff-support reading of Stage 1 (B1) from the R_1 comparison, using local VAR data and Bałaban's stated gauge-conversion results. Other Stage 1--2 dependencies retain their recorded scopes; no Delta_1 closure is claimed.

## 1. Objects and first caller

Use Stage 1's branch data xi, young carrier I, retained free carrier J, A_e in mathfrak g^J extended by zero on every other free bond, original field U_xi(a), and the same chosen cutoff norm sigma (operator or normalised Hilbert--Schmidt). The real inner product h and product Hilbert norms are those of Stage 1. Write r=delta_0/g_0=(A_1/A_0)p_0(g_0)=A_1(log g_0^{-2})^{p_0}. Thus r tends to infinity but g_0 r=delta_0 tends to zero. Every local derivative, overlap, range and Hessian constant below is independent of g_0 after L, group, character and source parameters have been fixed. This proves that both r>=1 and C_P g_0(1+2r)<=gamma/2 can be obtained by decreasing g_0. The empty-young-carrier case has F_xi(1)=F_xi(0) and response zero; below I is nonempty.

Set H=H_{xi,II}, ell=H_{xi,IJ} A_e, j(a)=<ell,a>, s=1+r+r_{e,xi}<=1+2r, and P_t=P_{xi,t}. The retained radius r_{e,xi} is the maximum of |A_e(b)|_sigma over retained bonds within 3R_c of I, or zero if that set is empty. Stage 1's collar bound gives r_{e,xi}<r there; no bound is imposed on farther retained fields. Every retained input entering H_IJ or a near primitive lies in this collar. This collar bound holds on every branch, independently of contour coverage: Stage 1 lem:collar-coverage(i) places every retained bond within 3R_c of I in G_xi minus S_1^*, where G_xi is the union of the good R_1 test carriers. Its factor in chi_{xi,e} is 1_{|Psi_xi(A_e)(b)|<r}; Psi is identity there, so nonzero retained weight forces |A_e(b)|<r. This is the proof of lem:collar-coverage(iii), not an extra condition on A_cov. On the open product of cutoff balls

$$
D=\{a\in\mathfrak g^I\, | \, |a_b|_\sigma<r\text{ for every }b\in I\}
$$

the conditional probability is exactly

$$
d\nu_t(a)=I_t^{-1}e^{Q_t(a)}\,da,\qquad
Q_t(a)=-\tfrac12\langle a,Ha\rangle-t\langle\ell,a\rangle+P_t(a).
$$

The measure is zero off D. Here I_t is Stage 1's I_{xi;t}, not a flat-reference normaliser. Throughout, f(a)=f_xi(a)=W_chi(C;U_xi(a)), with the exterior data fixed at their branch values. Let L_t=-j+partial_t P_t. Stage 1 gives

$$
\mathcal B_\xi[f]=\int_0^1\operatorname{Cov}_{\nu_t}(f,L_t)\,dt.
$$

All integrals in this draft use the measure at the end; da denotes the product Lebesgue measure for the fixed inner product.

All derivatives and operator norms below use the product h-Hilbert structure (the complexified structure for complex scalar gradients). Any fixed matrix-norm equivalence factors in Stage 2 are absorbed into the constants before g_0 is chosen. The primitive and Hessian inputs are Stage 2 regular-bounds and primitive-bounds, at their stated scopes: gamma I<=H<=m_L I with gamma=gamma_L/2; finite interaction range; and bounded local first and second derivatives on the enlarged box |a_b|_sigma<=2r at the inputs a+t A_e. The proof below uses these estimates at the background of the branch, without evaluating that background at identity.

## 2. Local derivative bounds

Let S_alpha be the full free-input stencil (including retained inputs) of a near primitive. Let N_in bound its size, and N_ov the number of primitive stencils meeting any free bond; both are fixed by L and the group. Choose a fine-bond range R large enough to bound every S_alpha diameter, the precision range and the source-to-input distances; R=8L+8 dominates the first-step stencils in Stage 1. Distances are the periodic maximum-norm distance of the initial sites plus one for differing directions.

Define

$$
K_\xi=\{b\in I:\operatorname{dist}(b,J)\leq R\},\qquad
I_C=\{b\in I:\text{some traversal }r\text{ of }C\text{ has }b\in\mathcal F_r\}.
$$

The source depends on the young field only through I_C. Stage 2's local primitive bounds and the finite overlap give constants C_P,C_S such that on the enlarged box, uniformly in t,

$$
\|D_a^2P_t\|\leq C_Pg_0s,\qquad
h(\nabla_b\partial_tP_t)\leq C_Sg_0s\,r_{e,xi}\mathbf1_{K_\xi}(b).
$$

For the second statement, each summand is D^2 p_alpha applied to a young direction and A_e restricted to S_alpha; it vanishes if that stencil has no retained input. The norm of that retained vector is at most sqrt(N_in) r_{e,xi}, and summing the at most N_ov stencils proves the bound. The support assertion follows from their range R.

Here h<=|.|_sigma for both permitted norms. The cross-row Schur bound of Stage 2 gives

$$
h(\ell_b)\leq m_L r_{e,xi}\mathbf1_{K_\xi}(b).
$$

On the enlarged real box |a_b|_sigma<=2r, with the branch exterior fixed, the rowwise reconstruction and Stage 2 uniform charts give

$$
\sup_a h(\nabla_b f(a))\leq C_{\rm resp,\chi} g_0\mathbf1_{I_C}(b).
$$

To obtain this last estimate, differentiate the scalar closed character of the ordered link product. Each affected link has a phase derivative bounded by C g_0, a fixed input affects a bounded number of links, and a square has bounded traversal multiplicity. The character derivative is bounded in the invariant tangent norm on the compact group. The other links remain unitary inside this closed contraction. No independently estimated open Wilson segment is introduced.

Choose g_0 after these constants so that the enlarged constant in Section 3 satisfies C_P g_0 s<=gamma/2. The energy -Q_t is then strongly convex on D, with Hessian at least rho=gamma/2.

## 3. An extension that stays within the proved chart

The enlarged-box input matters. A radial extension bounded only in h can leave the operator-norm box, and a radius proportional to 3s can exceed the enlarged box. Use the following extension instead.

Let B_sigma={x:|x|_sigma<=1} in the real Lie algebra and let Pi_r be Hilbert metric projection onto (3r/2) B_sigma. This is a closed convex set. Let phi be a nonnegative smooth h-radial mollifier supported in the unit h-ball, with integral one, and put epsilon=1/(4 sqrt(N)), where N is the fixed embedding dimension. Define

$$
T_r(x)=\int \Pi_r(x-y)\,\phi_{\epsilon r}(y)\,dy.
$$

This is a smooth map on the real Lie algebra. It is Ad-equivariant because metric projection and the mollifier commute with the orthogonal adjoint action. It has the properties

$$
T_r(x)=x\quad\text{if }|x|_\sigma\leq r,\qquad
|T_r(x)|_\sigma\leq3r/2,\qquad
\|DT_r\|\leq1,\qquad
\|D^2T_r\|\leq C_\sigma/r.
$$

Indeed h(y)<=epsilon r implies |y|_sigma<=sqrt(N) h(y)<=r/4. Projection is the identity at x-y whenever |x|_sigma<=r (also on a neighbourhood of this ball). Its convolution there equals x, since the mollifier has integral one and zero first moment. The range claim follows by convexity of (3r/2) B_sigma. Hilbert metric projection is 1-Lipschitz; convolution preserves that bound, and differentiation of its bounded weak first derivative against the mollifier bounds the second derivative by C_sigma/r.

Apply T_r bondwise to young inputs only, denoting this product map by T. Define

$$
\widetilde P_t(a)=\sum_{\alpha\ {\rm near}}
 [p_\alpha(Ta+tA_e)-p_\alpha(tA_e)],\qquad
\widetilde f(a)=f_\xi(Ta),\qquad
\widetilde L_t(a)=-\langle\ell,a\rangle+\partial_t\widetilde P_t(a).
$$

The image has young cutoff norm at most 3r/2<2r, so every primitive and every affected reconstruction row remains in the Stage 2 enlarged chart. The exterior fields are left fixed. Real reconstruction gives group-valued links, hence |\widetilde f|<=1. On D the source equals f, while tilde P differs from P only by the scalar -P_t(0); this scalar is removed only in the normalised conditional law. On D, tilde L_t-L_t=-partial_t P_t(0), so the score shift also leaves covariance unchanged.

The extended Hessian contains both D^2p(DT,DT) and Dp D^2T. The first has norm O(g_0 s); the second is O(g_0 s^2/r)=O(g_0 s), because r>=1 and s<=1+2r<=3r. Finite overlap therefore gives both an operator bound and block Schur row/column bounds <=C_P g_0 s for D^2 tilde P_t, after enlarging C_P before choosing the coupling. For the Schur bounds, each input belongs to at most N_ov stencils, each stencil has at most N_in blocks, and every Hessian block has the chain-rule bound just proved; summing at most N_ov N_in blocks fixes this enlarged constant. The support and range remain those of the original primitive stencils. The mixed derivative has no extra second derivative of T, since T is independent of t, so

$$
h(\nabla_b\partial_t\widetilde P_t)
 \leq C_Sg_0s\,r_{e,xi}\mathbf1_{K_\xi}(b).
$$

The global gradient bound on tilde f is the source bound of Section 2, composed with DT of norm at most one.

## 4. Covariance decay without moving the hard boundary

For a positive integer n define

$$
\beta_n(a)=n\sum_{b\in I}
 [\operatorname{dist}_h(\,\cdot\,,rB_\sigma)^2*\phi_{n^{-2}}](a_b),
$$

$$
V_{n,t}(a)=\tfrac12\langle a,Ha\rangle+t\langle\ell,a\rangle
           -\widetilde P_t(a)+\beta_n(a),\qquad
d\nu_{n,t}=Z_{n,t}^{-1}e^{-V_{n,t}(a)}\,da.
$$

Squared distance to a convex set is convex, and convolution preserves convexity. Thus the barrier Hessian is positive and diagonal in the bond index. For each fixed n the potential is smooth with bounded Hessian and Gaussian confinement. Its Hessian is at least rho I. The off-diagonal block row and column sums are at most

$$
M_*=m_L+\gamma/2
$$

and their range is at most R, independently of n,t,volume and branch.

Use the closed-form one-form operator

$$
\mathscr A_{n,t}=\mathscr L_{n,t}\otimes I+D^2V_{n,t},\qquad
\mathscr L_{n,t}=-\Delta+\nabla V_{n,t}\cdot\nabla
$$

on the Hilbert direct sum over b in I of L^2(nu_{n,t};g). It is at least rho I. The Helffer--Sjostrand covariance identity gives, for weighted H^1 functions,

$$
\operatorname{Cov}_{\nu_{n,t}}(u,v)
 =\langle\nabla u,\mathscr A_{n,t}^{-1}\nabla v\rangle_{L^2(\nu_{n,t})}.
$$

Here the identity is used for real functions and extended by splitting the Wilson character into its real and imaginary parts. Define its gradient norm by the sum of the two real gradient norms; the resulting factor at most two is absorbed into C_resp,chi. One rigorous source is Johnsen, Theorem 1.3 at k=0 and the form identification in Section 4, arXiv:1703.10011v2, https://arxiv.org/pdf/1703.10011. The theorem gives the projection onto constants' orthogonal complement as d_0^*(A_1|overline{range d_0})^{-1}d_0 when A_1 is strictly positive on that range. The stronger bound A_1>=rho I holds here. Use Proposition 4.5, which gives precisely the full-inverse covariance formula above. Its conditions are a C^2 normalised potential and closed range of A_0; the latter follows from A_1>=rho I by Theorem 1.3, as explained after (4.39). At fixed n the bounded Hessian identifies the displayed operator with that closed form. The additive log Z_{n,t} normalises the potential and leaves its derivatives unchanged. Our source is bounded and the score grows at most linearly, with bounded gradients, so both belong to weighted H^1.

For a fixed c in I let W_c multiply component b by exp(mu d(b,c)). It is constant in field space, hence commutes with the scalar generator and with every diagonal Hessian block, including the barrier. The off-diagonal Schur bounds give

$$
\|W_c\mathscr A_{n,t}W_c^{-1}-\mathscr A_{n,t}\|
 \leq M_*(e^{\mu R}-1).
$$

Choose mu=R^{-1} log(1+gamma/(4M_*)). The right side is at most rho/2. W_c and its inverse are bounded at each finite volume. A resolvent Neumann series therefore yields

$$
\|\Pi_b\mathscr A_{n,t}^{-1}\Pi_c\|
 \leq(4/\gamma)e^{-\mu d(b,c)},
$$

$$
|\operatorname{Cov}_{\nu_{n,t}}(u,v)|
 \leq(4/\gamma)\sum_{b,c\in I}e^{-\mu d(b,c)}
   \|\nabla_bu\|_2\|\nabla_cv\|_2.
$$

The potentially large diagonal barrier never enters this decay constant.

At fixed finite volume beta_n tends to zero in the closed cutoff body and to infinity outside it. The boundary has Lebesgue measure zero. Gaussian confinement and beta_n>=0 supply an integrable majorant for the source and linear-growth score products. Dominated convergence therefore takes the normalised covariances back to nu_t on the original cutoff box. The gradient bounds used on the right are global and independent of n, so this passage retains uniform constants. It introduces neither a translated cutoff nor a new exterior law.

## 5. The response and the surface terms

Substitute tilde f and tilde L_t into the covariance inequality and pass to the hard cutoff. The score gradient is at most (m_L+C_Sg_0s)r_{e,xi} on K_xi, and zero elsewhere. Periodic shell summation gives

$$
|\operatorname{Cov}_{\nu_t}(f,L_t)|
 \leq C_{\rm resp,\chi} g_0r\sum_{b\in I_C}e^{-(\mu/2)d(b,J)}.
$$

For the shell step, d(c,J)<=R on K_xi. Split exp(-mu d(b,c)) into two factors; one is at most exp(mu R/2) exp[-mu d(b,J)/2], while the sum of the other over all periodic bonds is bounded by the corresponding infinite-lattice shell sum. If J is empty the score is zero and the sum is defined to be zero.

The response constant C_resp,chi may enlarge the character derivative constant; it depends on gamma,m_L,R,N_in,N_ov,C_p,C_sigma,chi,G and fixed source parameters, and is independent of g_0,branch,volume,t and barrier index n. Put D_xi=sum_{b in I_C} exp[-mu d(b,J)/2]. Integrating in t gives the proposed conditional estimate

$$
|\mathcal B_\xi[f_\xi]|\leq C_{\rm resp,\chi} g_0r D_\xi.
$$

The hard-cutoff flux is retained. In the notation of Stage 1, m_xi=H^{-1}ell and, with outward normal n(a) almost everywhere on the Lipschitz boundary,

$$
\mathcal T_{\xi,t}[u]
 =I_t^{-1}\int_{\partial D}u(a)e^{Q_t(a)}
      \langle m_\xi,n(a)\rangle\,d\mathcal H^{d_G|I|-1}(a).
$$

Stage 1's exact integration-by-parts identity says the integrand of the response equals

$$
-\mathbb E_{\nu_t}[D_{m_\xi}f]
+\operatorname{Cov}_{\nu_t}(f,\partial_tP_t-D_{m_\xi}P_t)
+\mathcal T_{\xi,t}[f]
-\mathbb E_{\nu_t}[f]\mathcal T_{\xi,t}[1].
$$

The conditional bound controls this whole expression. Neither flux is set to zero or estimated separately. The smoothing map is identity on a neighbourhood of the cutoff body, and the barrier limit returns its original measure, so the boundary traces and normalised covariance in this identity remain those of Stage 1.

## 6. Physical substitution and next analytic premise

Retain w_xi=e^{c_xi} I_{xi;1}=J^a_xi[1] and the outer operation O of Stage 1. Define E_h[X]=Z_0^{-1} int O[w_xi X]dV and P_h(A)=E_h[1_A]. The event A_cov is determined by Omega_1,R_1 and the fixed contour templates: all contour bonds lie in Omega_1 and every free input lies in I. It and D_xi are measurable functions of the outer branch data, constant in the young integration. Only covered branches are used in the response caller. Positivity gives

$$
\left|\frac1{\mathcal Z_0}\int
 \mathcal O[w_\xi\mathbf1_{A_{\rm cov}}\mathcal B_\xi[f_\xi]](V)\,dV\right|
 \leq C_{\rm resp,\chi} g_0r\,
 \frac1{\mathcal Z_0}\int\mathcal O[w_\xi\mathbf1_{A_{\rm cov}}D_\xi](V)\,dV.
$$

No conditional or flat-reference normaliser replaces Z_0. In particular c_xi remains inside w_xi.

For Stage 1's covered event A_cov, the combined response/uncovered contribution is

$$
E_{\rm bdry}=\mathbb E_h[
 \mathbf1_{A_{\rm cov}}\mathcal B_\xi[f_\xi]
 +\mathbf1_{A_{\rm cov}^c}F_\xi(1)].
$$

The conditional bound, |F_xi(1)|<=1 on the complement and positivity therefore prove

$$
|E_{\rm bdry}|
 \leq C_{\rm resp,\chi} g_0r\,\mathbb E_h[\mathbf1_{A_{\rm cov}}D_\xi]
      +\mathbb P_h(A_{\rm cov}^c).
$$

The target is to pay these two geometric quantities under the same physical history weight, using local cutoff-failure witnesses. That history estimate is not assumed in Sections 1--5. Its proof attempt is the next part of this draft.
## 7. Paying the history average by one-point witnesses

This part uses compatible even fine periods. This is an additional restriction relative to Stage 1's general compatible-period statement; it includes the manuscript's torus with periods 2 L^m when the partitions fit. The conditional estimate of Sections 1--5 needs no parity restriction. No odd-period history bound is asserted here.

Write ell_mac=L M R_1 for the macro side (R_1 here is the scale integer), and B_xi=Lambda_1^c for the filled bad region. Let E(B_xi) be the positive fine bonds with at least one endpoint in B_xi. Write n_C for the number of contour traversals. The deterministic set Gamma_C consists of the contour bonds and all free-input templates of their reconstruction rows, periodically projected from the torus templates before any history is selected. There is a fixed C_L with |Gamma_C|<=C_L n_C; every I_C is contained in Gamma_C. Young designated variables are eliminated, so their free-input stencils, rather than designated bonds as independent variables, are included in Gamma_C.

Define the marked physical probability at a positive bond z by

$$
p_z=\frac{1}{\mathcal Z_0}\int\mathcal O[
 w_\xi\mathbf1_{\{z\in E(B_\xi)\}}](V)\,dV\;.
$$

Here the mark depends on the regions and deterministic filling, not on the young variable. A uniform bound p_z<=q is enough: no component-size exponential or several-witness factorisation is required for this caller. Indeed J is a subset of E(B_xi). For c=mu/2, pointwise on each branch,

$$
D_\xi\leq\sum_{b\in\Gamma_C}\sum_z
 e^{-c d(b,z)}\mathbf1_{\{z\in E(B_\xi)\}}\;.
$$

The periodic bond shell sum S_c=sup_b sum_z exp[-c d(b,z)] is bounded by its infinite-lattice counterpart, uniformly in the periods. Thus E_h D_xi<=C_L S_c n_C q. If coverage fails, either a contour bond leaves Omega_1 or one of its free inputs leaves I. In the first case that bond meets B_xi since Lambda_1 is a subset of Omega_1. In the second case the non-young input is retained in J or outside Omega_1, and hence meets B_xi. Consequently 1_{A_cov complement}<=sum_{b in Gamma_C}1_{b in E(B_xi)}, and P_h(A_cov complement)<=C_L n_C q.

### 7.1 Cutoff failures give local witnesses

Use the seed proof in the archived working note, subsection sec:first-step-seed, eq:seed-layer-sizes through eq:seed-support-inclusion. Its operands are the original unresummed CRE (1.1), (1.4), (1.8), (1.18) cutoffs, before the boundary substitution. The needed conclusion is only this: a bad eligible test forces a fine plaquette deviation >=theta in its neighbourhood, or an active mean-transport variable deviation >=theta there. The P_0 and P_1 alternatives need no gauge-variable witness. The threshold is

$$
\theta=\min\left(\varepsilon_0,
 \frac{\varepsilon_1}{4B_3N^{3/2}L^2},
 \frac{\delta_0}{2C_Q}\right),\qquad
 C_Q=(9K_L+2)(1+2B_3N^{3/2}L^2)\;.
$$

K_L is the maximum number of plaquettes in the fixed two-block path fillings of RG1 (0.4), (0.11), as defined in that proof. The norm is the source cutoff norm, either operator or normalised Hilbert--Schmidt; the mean and comparison constants are chosen for that norm. The seed proof is not replaced with a claim about arbitrary frozen exterior data. It is used only on the original earlier-cutoff and averaging-constraint support. Its common local width w is between L M_2 R_1 and L^2 M_2 R_1; all occurrences use the same convention. The macro widths are ell_mac. These are the conventions of Stage 1's branch hypotheses; no mixed-width version is asserted.

For every eligible R_1 cube, use the comparison proved in Section 9 from the local determining-data problem, uniformly in its good/bad label:

$$
\sup_{b\in(Q_w^{[2]})^*}|U_1(b)U_{1,Q}(b)^{-1}-1|_\sigma
 \leq C\varepsilon_1 e^{-cLM_2R_1}<\delta_0/10\;.
$$

This does not assume that U_1 is in the support of zeta or of the other fine-field cutoffs. The formerly used auxiliary A=0 support argument is superseded. On the native principal chart such a label forces |g_0 A(b)|>=delta_0 at a free bond. The unitary logarithm inequality and the comparison then give

$$
|\widetilde U(b)U_{1,Q}(b)^{-1}-1|
 \geq(2/\pi-1/10)\delta_0>\delta_0/2\;.
$$

When all witnesses are below theta, the seed's two-block comparison gives the opposite bound <=C_Q theta<=delta_0/2. This excludes that label. CRE (1.1), (1.4), (1.8), (1.18) are sharp characteristic partitions at their printed thresholds, so these numeric inequalities imply vanishing of the corresponding bad factor. Off-chart configurations are not added to (1.18): the partition is introduced after the logarithmic reconstruction (1.13)--(1.15).

Before filling, CRE (1.10), (1.20) give the bad region as Q_1'^{~4} union (B(P_1^1)^c)^{~5} union R_1'^{~1}. The containment B(P_1^1)^c subset P_0'^{~2} union P_1'^{~1} is sufficient under either active-set reading recorded in the archived proof. A point of this region is within 10 ell_mac of a bad test. The modification after (1.20) fills only components contained in cubes of side less than 100 ell_mac. Every added point is within 100 ell_mac of an original unfilled bad point. This also holds if small merged components are filled again: by induction every current component contains an original bad point, and each fill is performed inside a cube of side less than 100 ell_mac containing that component. Choose an original bad point in that component; every point of its rectangular hull is within 100 ell_mac of it. Overlapping hulls or later merges preserve the presence of an original point. Thus there is no cumulative distance loss and no dependence on a once-only or iterated convention. CRE (2.9) gives R_0<=L R_1 for small coupling. Including each test's witness neighbourhood and incident bonds, every z in E(B_xi) therefore forces at least one witness within distance K ell_mac of z, with the fixed safe K=256. At most

$$
n_W=7(2K\ell_{\rm mac}+7)^4
$$

plaquette or gauge-variable labels occur in that neighbourhood. The count is an overcount on a small periodic torus, which is harmless.

### 7.2 The marked probability retains Z_0

Reverse Stage 1's changes of variables with the mark 1_{z in E(B_xi)} inserted. The mark commutes with the earlier resummation because the final regions and filling are fixed in that term. In particular the first reverse step uses

$$
w_\xi=e^{c_\xi}I_{\xi;1}
 =\int e^{c_\xi}K_{\xi;1}(a)\,da\;.
$$

The branch constant c_xi and all far primitives are present.
The equality can be checked before taking the young integral. Put A_e^Psi=Psi_xi(A_e), and let E_xi(B) be the pre-boundary-change exponent of CRE (1.15), with its outer prefactor excluded. Stage 1 defines

$$
c_\xi=E_\xi(0)-\frac{1}{2}\langle A_e^\Psi,H_\xi A_e^\Psi\rangle
 +\sum_{\alpha\ {\rm far}}p_\alpha(A_e^\Psi)
 +\log|\det D\Psi_\xi(A_e)|\;.
$$

Psi is identity in every near stencil and has support disjoint from I, so Psi_xi(a+A_e)=a+A_e^Psi. Expand the quadratic form into its II, IJ, JJ blocks, leave every far primitive at A_e^Psi, and retain the boundary determinant. This gives the pointwise identity

$$
e^{c_\xi}K_{\xi;1}(a)
 =\mathbf1_D(a)|\det D\Psi_\xi(A_e)|
    \exp E_\xi(\Psi_\xi(a+A_e))\;.
$$

The composed retained cutoff and zeta multiply both sides. This is the density needed for the inverse boundary substitution. No equality with the old two-parameter I_{xi;1,1} is used. Together with the outer prefactor this integrand recombines into the transformed CRE (1.15) density, including the boundary Jacobian. Undo Psi_xi, the free-variable constraint elimination, the scaling, the nonlinear constraint linearisation of (1.14), the logarithmic chart of (1.13) with its Haar density, and the translation about U_1 in this order. The retained cutoff is composed with Psi_xi and the boundary factor zeta remains in that composition, including its boundary-fluctuation dependence. The resulting marked integral is CRE (1.6) with its four original partitions and site-gauge integration. No determinant or normalisation is discarded. The unmarked same chain is exactly Z_0=e^{-E} int exp[-S(U)/g_0^2]dU.

For each active block centre y and noncentral x let w_yx be its mean transport after gauge change. RG1 (0.6) and CRE (1.5) give the Haar substitution v(x)=w_yx^{-1}h_y U(y,x), with v(y)=h_y. Its Jacobian is one, and its law is

$$
q_g(dw)=z_g^{-1}\mathbf1_{\{|w-1|_\sigma<\varepsilon_0\}}
 e^{-s_G(w)/g_0^2}\,dw,\qquad
s_G(w)=1-\operatorname{Re}\operatorname{tr}_N w\;.
$$

z_g is the integral of the displayed density before division and is precisely CRE's gauge normaliser. For inactive indices add independent q_g variables of integral one. Include independent Haar variables h for the centres and unused sites. The earlier P_0 and P_1 choices depend on U and its coarse gauge orbit, not on these auxiliary variables. The comparison event can now be enlarged to W_z, existence of any plaquette or any auxiliary gauge-variable witness in the deterministic K ell_mac neighbourhood. W_z is independent of the later Q_1,R_1 labels. Only after this enlargement sum their characteristic partitions to one. This yields

$$
p_z\leq(\mu_0\otimes q_g^{\otimes\mathcal I}
                   \otimes\mathrm{Haar}^{\otimes T})(W_z),\qquad
\mu_0(dU)=\mathcal Z_0^{-1}e^{-E}e^{-S(U)/g_0^2}\,dU\;.
$$

Here mathcal I is all pairs (y,x), with y a coarse centre and x a noncentral site in its block. The product is a representation before the history conditions, not an independence claim for those conditions. Plaquette witness norms and the conjugation-invariant gauge-variable norms are gauge-invariant scalars under the simultaneous gauge transformations; no open Wilson contraction is estimated.

### 7.3 One-point tails and summation

Let d_G=dim G and b_G=1/(2N). Then s_G(w)>=b_G|w-1|_sigma^2. There are group-dependent c_H,g_H>0 such that the Haar operator ball of radius g_0<=g_H has mass >=c_H g_0^{d_G}. On the event that every fine link lies in this ball, every plaquette contributes at most 8g_0^2. With V_T the number of fine sites, the physical denominator satisfies

$$
\mathcal Z_0\geq e^{-E}(c_Hg_0^{d_G})^{4V_T}e^{-48V_T}\;.
$$

Only the reflection form, functional chessboard inequality and single-witness tails are imported from the archived subsection sec:component-chessboard; its old marked-integral notation is not imported. That site-plane reflection-positivity and closed-unit-cube chessboard proof applies on compatible even periods. Its single-plaquette case gives

$$
\mu_0(|U(\partial p)-1|_\sigma\geq\theta)\leq z_P,\qquad
z_P=\exp\left[-\frac{b_G\theta^2}{4g_0^2}
 +4d_G\log(g_0^{-1})+4\log(c_H^{-1})+48\right]\;.
$$

For clarity, the reflected dissemination of one plaquette has V_T/4 distinct plaquettes of that orientation; dividing its energy bound by the same Z_0 above and taking the 1/V_T root gives z_P. This is a normalised probability estimate, not a numerator estimate. The independent gauge-variable tail is

$$
q_g(|w-1|_\sigma\geq\theta)\leq z_G,\qquad
z_G=e^{1/2}(c_Hg_0^{d_G})^{-1}
 e^{-b_G\theta^2/g_0^2}\;.
$$

For the latter denominator restrict just one gauge variable to its operator ball of radius g_0, where its action is <=g_0^2/2 and its native cutoff is one. A union bound, without any independence assumption between plaquette witnesses, now proves

$$
p_z\leq q:=n_W\max(z_P,z_G)\;.
$$

Put pi_*=min(p_0(g_0),p_0(g_1)). CRE (2.6)--(2.9) and delta_0=(A_1/A_0)epsilon_0 give theta>=c_theta g_0 pi_* for small coupling. Since ell_mac grows as a fixed power of log(g_1^{-2}), log n_W=O(log log(g_0^{-2})). With CRE's p_0 exponent >=5 mathfrak r>=10, both log(g_0^{-1}) and log n_W are absorbed by pi_*^2. Thus there are c_*,g_*>0, fixed after the source constants, such that q<=exp[-c_* pi_*^2] for 0<g_0<g_*.

Combining Sections 5--7 gives the proposed Stage 3 bound

$$
|E_{\rm bdry}|\leq C_{\rm resp,\chi} n_C(1+g_0r)
 e^{-c_*\pi_*^2}\;.
$$

All constants are uniform in compatible even periods, contour location and first-step histories, with fixed L, group, character, M_1,M_2,M and source constants. The n_C factor is retained. This controls the exterior-response/uncovered term in Stage 1; it does not control its joint closed-source defects or identify its regional scalar with the perimeter/corner coefficient.

## 8. Checkpoint and reviewed scopes

The conditional calculation gives |B_xi[f]|<=C_resp,chi g_0 r D_xi under the Stage 2 Hessian, Schur, enlarged-chart and primitive derivative hypotheses and Stage 1 collar cutoff. Both hard-cutoff surface terms remain in the bounded covariance. Its physical caller is restricted to A_cov. The zero extension A_e in mathfrak g^J and the native retained-cutoff proof of r_e<r on every branch are now explicit.

The one-point history calculation gives |E_bdry|<=C_chi n_C(1+g_0 r)exp[-c_*pi_*^2] on compatible even-period tori, conditional on these inputs and the stated Stage 1 reconstruction/measure identities. It uses only single-witness tails, not the archived component probability theorem. The marked density recombination is displayed without equating the old two-parameter normaliser with the current I_{xi;1}. Filling proximity is valid for either a simultaneous or iterated small-component filling.

The R_1-label transfer now uses Section 9: localise the action to a P_0-good collar with unchanged fine boundary values, verify VAR's mixed data regularity and both regularity bounds, integrate (190) from the boundary-supported data, and restore the source gauge with its averaged normalisation. The full-support reading of (B1) is no longer a premise of this comparison. The remaining source inputs are Bałaban's stated existence, uniqueness, derivative-decay and gauge-conversion results at their verified local hypotheses. The user permits these stated source results to be taken on faith. This is not a proof that the minimum belongs to every characteristic factor of (1.11), and unrelated uses of that stronger claim in Stage 1 are not recertified here.
Review evidence (internal record only):
- Conditional-response r1 failed on a connection reset and has no verdict.
- Conditional-response r2 and r3 completed. Both validate the analytic chain conditionally; the requested radius, norm/domain, zero-extension, collar-support, complex-source and full-inverse clarifications are written into Sections 1--6. They do not certify all Stage 1--2 inputs.
- History-response r1 and r2 completed. The full seed/cutoff excerpts and current collar-density proof were supplied in r2. The remaining R_1 source transfer was reviewed separately.
- R_1-label-transfer r1 completed and validates the support argument conditional on (B1). It does not certify the full history theorem or a new reading of (B1).
- Every completed run passed isolation/transport checks, with one model request, no gateway errors or tool events, and no differences between saved and transmitted packet fields. These checks are operational evidence only.

No edits were made to WILSON_FIRST_RG_STEP_V2.tex. The B1 full-support dependency of the Section 7 comparison is discharged by Section 9 at the reviewed source scopes. This does not globally recertify all Stage 1--2 results or certify Delta_1. The joint marked-source defects and regional perimeter/corner identification are outside this Stage 3 estimate.

Stage 5 (19 October 2026; `V2_STAGE5_COLLAR_RETREAT_DRAFT_2026_10_19.md`, every section through isolated review) partly supersedes this checkpoint. Its history weight is the labelled one of a second collar test with the Λ₁-retreat, and its boundary bound is (5.9R)/(5.10R) with the label accounting (6.3R)/(6.4R): relative to the labelled leading coefficient, the one-point witness cost q of Section 7 becomes q + N_ret q_ϑ (the retreated bonds attributed to marked bad bonds), the response constant C_resp,χ of Sections 1–6 enters its constant C_1, a prefactor r^{d_G} and a family-sum factor e^{n_C ε̄_ph} with ε̄_ph = O(g₀²(1+r)⁴) appear, and the leading coefficient is identified with κ_C e^{E°_Λ} at the retreated carrier D(Λ) (its §7). Sections 1–6 (the conditional response bound), 7.1–7.3 (the single-witness tails) and 9 (the R₁-label transfer) are used by stage 5 as stated; the restriction of the physical caller to A_cov becomes the restriction to the labelled event A_cov^{fin} (its §3.4). The bound |E_bdry| ≤ C_χ n_C (1 + g₀ r) exp[−c_* π_*²] of this section is replaced, not strengthened: stage 5's accounting is linear in n_C with the factors named.

## 9. Removing the full cutoff-support requirement from the minimum comparison

This section replaces the zero-fluctuation support argument in Section 7.1. Its target is only the following deterministic property of the two minima: for every eligible Q subset Omega_1^{~-1}, on its twice enlarged free-bond carrier,

$$
\sup_{b\in(Q_w^{[2]})^*}
 |U_1(b)U_{1,Q}(b)^{-1}-1|_\sigma
 \leq C_{L,G}\varepsilon_1e^{-c_{L,G}LM_2R_1}
 <\delta_0/10\;.
$$

The constants may depend on the fixed L,G,M_1,M_2 and source parameters; they are fixed before g_0, independent of the fluctuation, its R_1 label, exterior history and compatible torus. Compatible fine periods are multiples of ell_mac and even, hence at least 2ell_mac. Since side(Q_w^{[4]})<=9L^2M_2R_1<=9ell_mac/8<2ell_mac, this determining box and its fixed-range stencils have lifted copies before the next periodic image for small coupling. If Omega_1 is the full torus, there is no exterior collar to freeze and the same argument uses the periodic VAR problem. R_1 in the exponential is the scale integer. The inequality concerns a simultaneously gauge-covariant pair of links: their relative product transforms by conjugation at the initial endpoint, so its norm is gauge invariant. It is not an estimate on an open Wilson source.

### 9.1 Required source inputs and the stronger assertion not used

Use the regular critical minimum of CRE (1.12), supplied by VAR Theorem 1, with the prescribed V,V_0 and source axial mean gauge. The localisation argument below verifies the source hypotheses for its existence and regularity near Omega_1; it does not assume them for a distant large-field exterior. Its resulting plaquette regularity on Q_w^{[4]} is <=C_{L,G}epsilon_1 L^{-2}. The local minimum U_{1,Q} is CRE (1.2) with determining set mathfrak B_Q=mathbf B_1(Q_w^{[4]}) and reference data D_Q^0=M^dot(Q_1^{s*}V)|_{mathfrak B_Q}. It has the corresponding VAR mixed-scale regularity (with the scale-zero boundary bound described below) and the same coarse averages V on the interior determining region. These are the hypotheses used in CRE's derivation (3.17)--(3.19); its only field is the minimum, not the integrated fluctuation. At k=0 the fine spacing eta=1 and V^(0)=U_1, V_Q^(0)=U_{1,Q}. No preceding effective interaction is needed for that specialisation.

Here is the local-domain verification needed for that application. Work before the P_0,P_1,Q_1 resummation, at any supported history contributing to the fixed Omega_1,V,V_0. Let Uhat be its fine field. Choose the enlarged fine domain Omega^+=Omega_1^{~1}, with the macro enlargement of CRE (1.10), and fix Uhat=V_0 on the collar Omega^+ minus Omega_1. Outside Omega^+ retain the original field but omit its action terms from the variational problem: every plaquette or block-gauge term containing an unfrozen variable is contained in Omega^+ once ell_mac>2L+4. Omitted terms are constants. This produces exactly the same constrained first variation as (1.12), not a changed boundary condition or integration law.

CRE (1.10) and its following sentence separate Omega_1 from the earlier bad regions by at least two macro layers. Hence every plaquette and averaging stencil in Omega^+ is in the P_0-good region. At this unresummed stage the original field Uhat obeys |Uhat(partial p)-1|<epsilon_0 there. If the canonical outer operation has already omitted these factors, use the exact removal statement immediately before CRE (1.11): those factors equal one on the support of the retained original-field factors. Restoring them therefore changes no integral. Since the history summands are nonnegative, a point of nonzero resummed density has at least one supported unresummed history. This restoration concerns Uhat, not the minimum U_1. In particular this controls the prescribed collar V_0; the arbitrary distant exterior is never required to be regular. Conjugation and a bounded number of incident plaquettes give |D^*_{Uhat} partial Uhat|<=C_d epsilon_0 on the collar and the variable region. At one step, multiplying by the largest of the fixed scale weights L^2,L^3 puts Uhat in VAR's class (6), with radius C_L epsilon_0. Its fixed data are exactly V_0 on the fine collar and V on the interior coarse labels, since the original averaging constraint is retained.

Use positive-bond carriers E(X) consisting of bonds with an endpoint in X. The fixed fine collar carrier is E(Omega^+) minus E(Omega_1), so no crossing bond that is a variable in CRE (1.12) is inadvertently fixed. The hierarchy for VAR has outer fine domain Omega^+, inner block domain Omega_1 and determining set this fine bond-set difference at scale zero together with Omega_1 at scale one, with the source mixed-bond convention of VAR (7). Its spacing condition (1) holds because the separating macro layer has width ell_mac, exceeding the fixed source R M_1 for small coupling. For a mixed determining plaquette, replace every missing fine-side bond by its block average as prescribed in VAR (7). The original constraint makes the resulting loop an ordinary fine plaquette of Uhat, or a coarse plaquette of its block average. CMP98 Proposition 1, (51), bounds the latter by L^2 epsilon_0+C(L^2 epsilon_0)^2<=2L^2 epsilon_0. This is also CRE's explicit bound before (1.2). Thus the entire determining set for this localized problem has VAR data regularity <=C_L epsilon_0. No regularity assertion on the rest of Omega_1^c is involved.

VAR Theorem 1 therefore constructs the regular critical orbit for these same data, with both the plaquette and divergence bounds (2), at radius B_3 C_L epsilon_0. This is the regular minimum used by CRE (1.12), which cites that theorem. The localisation changes the action only by constants for every admissible variation, so it does not select a different critical orbit. After restriction to Q_w^{[4]}, the same bound gives membership in the local uniqueness class, with fixed scale/norm conversions. Since epsilon_0/epsilon_1 is bounded by CRE (2.8), its radius is C_{L,G}epsilon_1, and it lies below VAR's a_0 for small coupling. The fine boundary layer of U_{1,Q} has VAR's scale-zero bound, not an epsilon_1 L^{-2} bound: its straight-extension data have plaquettes either trivial or equal to coarse plaquette holonomies of V, bounded above by 2L^2epsilon_0. Its mixed-scale data are consequently regular with the same fixed C_{L,G}epsilon_1 parameter.
We do not assume that zeta(Omega_1^c), or every characteristic factor of (1.11), remains nonzero when the fine integration variable is replaced globally by U_1. In particular no new branch at A=0 is introduced. The full-support reading of (B1) is not used in this comparison. Existing Stage 1 uses of (B1) elsewhere are not recertified or rewritten by this argument.

### 9.2 Boundary data and their size

Let D_Q=M^dot(U_1)|_{mathfrak B_Q}, and define B_Q on this determining set by

$$
B_Q(e)=\frac{1}{i}\log\bigl(D_Q(e)(D_Q^0(e))^{-1}\bigr)\;.
$$

Both data are already defined by the source averaging operation on this regular configuration. The determining interior carries scale-one coarse bonds, while its boundary layer carries the finer determining variables, as defined after CRE (2.12). For the straight extension of CRE (1.3), every intrablock contour is identity, every centre-to-centre path crossing a specified interface has transport V(c), and every relative closed holonomy in RG1 (0.4) is identity. Its logarithmic correction is therefore zero, proving M(Q_1^{s*}V,c)=V(c) in that averaging formula. On the interior, both data equal V; hence B_Q=0 there. Its support is confined to the boundary layer of width 2LM_1 of Q_w^{[4]}. This is the support statement preceding CRE (3.18).

The principal logarithm is legitimate: the reasoning after CRE (3.17) bounds its argument by C_{L,G}epsilon_1. CRE's printed coefficient 44d^2B_3 pertains to its own regularity coefficient; the enlarged local coefficient obtained here is retained inside the fixed C_{L,G}, not equated with that printed number. The bound follows from the minimum's regularity and equality of coarse averages, rather than from a fluctuation cutoff. At one step it can also be read directly from the fixed two-block comparison: in the axial mean gauge a regular minimum is within C_{L,G}epsilon_1 of the identity on internal bonds and of V(c) on interface bonds, whereas Q_1^{s*}V has exactly those respective values. Mixed determining plaquettes and the local averages are the ones in CRE (1.2),(2.12)--(2.16). Thus

$$
\|B_Q\|_\infty\leq C_{L,G}\varepsilon_1\;.
$$

To meet VAR (172) with its absolute C_1, choose its small parameter alpha=K epsilon_0, where the fixed K dominates all determining-data, uniqueness-class and B_Q bounds. Then |exp(i t B_Q)-1|<=|t B_Q|<=alpha, so C_1=1 suffices. Apply VAR Proposition 9 and (190) with this alpha, not CRE's identically named epsilon_1. Taking g_0 small makes alpha<=a_1 and B_3 alpha<=a_0; CRE (2.8) converts the resulting C alpha bounds back to C'epsilon_1. This uses the printed absolute-C_1 statement without extending it. No bound is imposed on the arbitrary exterior integration variables away from this local regular domain.

### 9.3 Integrating the local derivative estimate

Use the local minimal-configuration map of VAR Proposition 9 on mathfrak B_Q, with reference U_{1,Q}. Denote its relative Landau-gauge logarithm by mathscr H_Q(B), normalised by mathscr H_Q(0)=0. This is exactly the map used in CRE (3.17), including its L^{-1} scale factor at k=0. CRE (3.17) identifies the map at B_Q with the restriction of U_1, up to the source gauge restoration: both have determining data D_Q and lie on the unique regular critical orbit. For the criticality check, a local admissible variation fixes the determining fine layer and the averages on the interior coarse rows. Extend it by zero outside Q_w^{[4]}. The fixed layer is wider than the plaquette and averaging range, so this extension preserves every global average and exterior value in (1.12). The first variation of the global action vanishes; its local part is precisely the local action variation. Also the gauge functional has zero first variation at an axial mean configuration, where each nonnegative summand attains zero. Thus the restriction of U_1 is critical for the local action. The uniqueness-class membership established in Section 9.1 then identifies its orbit with the local analytic solution. The identity is about that orbit; it requires no membership of the integrated field in a cutoff event.

VAR (190), Proposition 9 supplies its functional derivative with the original mixed-scale weights. At one RG step the scale labels are 0 and 1, so all powers of L in those weights are fixed constants. A determination bond e in the outer layer and an interior bond b therefore satisfy the bound by C_{L,G}exp[-c_{L,G}d(b,e)]. The unit-density measure at the finer level and the scale-one determining measure contribute only fixed L-dependent factors. Integrating along t B_Q and summing these labels gives

$$
|\mathscr H_Q(B_Q;b)|
 \leq C_{L,G}\varepsilon_1
       \sum_{e\in\operatorname{supp}B_Q}e^{-c_{L,G}d(b,e)}
 \leq C'_{L,G}\varepsilon_1
       e^{-c'_{L,G}d(b,\operatorname{supp}B_Q)}\;.
$$

For the second inequality split each exponential into two halves and bound the remaining periodic lattice shell sum by its infinite-lattice sum. This pays the whole boundary area without a volume-dependent constant. For b in Q_w^{[2]},

$$
d(b,\operatorname{supp}B_Q)
 \geq 2w-2LM_1-C_L\geq LM_2R_1
$$

once the source collar threshold holds, after decreasing a fixed decay constant if necessary. Here w>=LM_2R_1 and R_1 tends to infinity. The same argument covers either candidate common local width; it never uses a good/bad R_1 label.

### 9.4 Restoring the source gauge with its averaged normalisation

The transformation in VAR Proposition 2 is not centre-fixing. Its printed condition is (overline{R_0 u})^j=1 on Lambda_j, in particular u=1 on the fine determining layer (VAR p.281). At one step its interior condition is overline{R_0 u}(y)=1. It does not imply u(y)=1. The former centre-fixing argument is withdrawn.

Keep the restoring transformation u_Q of CRE (3.17), defined by this source normalisation. At the first step, with CRE's eta=1 and its convention (1.17), the identity on the required bonds is

$$
U_1(b)=u_Q(b_-)^{-1}
 e^{iL^{-1}\mathscr H_Q(B_Q;b)}U_{1,Q}(b)u_Q(b_+)\;.
$$

Here the local inputs verifying the transferred source estimates are the VAR uniqueness/regularity class from Section 9.1, the small supported B_Q of Section 9.2, and the response bound on both endpoint blocks and the crossing bond from Section 9.3. Fix an analytic mean neighbourhood radius rho_av>0 for the finite source contour families, with derivative bounds on its closed half-radius neighbourhood; choose g_0 after this radius so both the reference path-family diameter and its perturbation are less than rho_av/4. This specifies the regular-chart reduction. The block-local gauge inequality below is the transferred source result; the following path description explains its one-step support and constants, rather than asserting the old single-contour formula unchanged for the modified mean.
 The exact equations determining it are CMP98 (77)--(87), with its expression in terms of the relative fields given in (106)--(108). At one step the product in (106) has a single j=0 factor. That factor is a reference-unitary conjugation of the inverse block average followed by a local relative path transport. The nontrivial centre factor is given by (87), not discarded. Unitary conjugations preserve the chosen norm. Each path has length at most C_d L, so the telescoping product identity bounds its relative deviation by C_L times the largest relative-link deviation in that block. The analytic averaging bound used in (161)--(163) bounds its block-average deviation by the same quantity, after reducing the fixed chart. Consequently these source formulas give

$$
\sup_{x\in B(y)}|u_Q(x)-1|_\sigma
 \leq C_{L,G}\sup_{b\in E(B(y))}|\mathscr H_Q(B_Q;b)|_\sigma\;.
$$

The fixed L^{-1} factor from CRE (3.17) is absorbed into this constant. The restoring map is relative to the reference pair: under a simultaneous gauge change h of the field and reference, its conjugated representative is u_Q^h(x)=h(x)u_Q(x)h(x)^{-1}, as follows by conjugating the relative action (VAR (16)--(17)) and its reference-dependent gauge condition. Thus |u_Q(x)-1|_sigma is a conjugation-invariant scalar of this relative construction. It is only used within the gauge-restoration proof, not as a new inductive activity or a Wilson source norm. In particular the centre contribution u_Q(y) is retained in comparing the two minima.

CMP98 uses its older averaging definition. The application here uses Bałaban's explicit extension statement: RG1 after (0.10) states that its earlier results apply to averages satisfying the listed properties; RG1 immediately after (0.12) states that all results of the averaging paper are valid for the modified average, with the indicated modifications of the proofs. Thus the above bound is used for the selected RG1 averaging and mean gauge as that source result, not by asserting that the older individual-contour identities stay verbatim unchanged. CRE (3.17)--(3.19) makes this same gauge-conversion application for the later scheme. No change of the physical averaging operation is made. This extension is also used for gauge conversion within RG1 itself: (3.26)--(3.27) introduce the generalized axial and relative Landau gauges, explicitly using CMP98 (77); (3.39) explicitly invokes CMP98 (97) while retaining the centre-block gauge factors. RG1 reference [12] is identified in its bibliography as Averaging operations for lattice gauge theories, Commun. Math. Phys. 98 (1985). Thus the gauge part of the transfer is confirmed by the later construction, rather than inferred solely from a statement about block averages. These source assertions are accepted at their stated regular-chart hypotheses; no claim to have re-proved Bałaban's averaging paper is made.

For the bond b in the comparison, apply Section 9.3 on both endpoint blocks, the crossing bond b itself, and the paths entering these source gauge factors. This enlarges the input set by a fixed at most 2L+2, already included in C_L in the distance loss. The relative exponential and both endpoint factors then give

$$
|U_1(b)U_{1,Q}(b)^{-1}-1|_\sigma
 \leq C_{L,G}\varepsilon_1 e^{-c_{L,G}LM_2R_1}\;.
$$

Both endpoint gauge factors in CRE (3.18) are retained. The final quantity is the simultaneous-gauge-invariant norm of the relative pair of links. No comparison modulo an unspecified gauge transformation is substituted.
### 9.5 Caller replay and denominator

CRE (2.6),(2.8) bound epsilon_1/delta_0 by fixed source constants, and R_1 grows as a power of log(g_1^{-2}); therefore the last displayed bound is <delta_0/10 for sufficiently small g_0. On a bad (1.18) free-bond test, |g_0 A(b)|>=delta_0. Use the same sigma norm for the (1.18) test, the comparison and the no-witness bound. The eigenvalue inequality |exp(iX)-1|_sigma >=(2/pi)|X|_sigma holds when every eigenvalue of X is in [-pi,pi], as on the native chart; it is valid in both the operator and normalised Hilbert--Schmidt norms without a norm conversion. It then yields |tilde U(b)U_{1,Q}(b)^{-1}-1|_sigma >=(2/pi-1/10)delta_0>delta_0/2, contradicting the no-witness two-block bound <=C_Q theta<=delta_0/2. This proves the R_1 seed implication without the global A=0 support construction.

The physical integral is never altered. For each original history the same minimum comparison is used inside its cutoff-support implication. The numerator remains int O[w_xi 1_{z in E(B_xi)}]dV, w_xi=e^{c_xi}I_{xi;1}; its denominator remains Z_0=int O[w_xi]dV. No zeta factor is removed, evaluated at U_1 or divided out. The surface-term covariance estimate is unchanged. Sections 7.2--7.3 then apply with their existing hypotheses and even-period scope.

The local-domain and derivative argument received focused review stage3-b1-locality-20261018-r2; the source gauge transfer received focused review stage3-b1-gauge-source-20261018-r1. Both are used at their stated scopes, with Bałaban's source statements permitted as background. It does not claim full cutoff-support membership of the minimum or repair unrelated uses of that stronger membership elsewhere.

## 10. TeX form of Sections 1-9

The block below is the TeX translation of Sections 1-9 above, spliced on 19 October 2026 into WILSON_FIRST_RG_STEP_V3.tex as the last appendix (`app:exterior-chessboard`, immediately before the bibliography), with the conditional bound of Section 5 as `lem:exterior-response-bound`, the history bound of Section 7.3 as `prop:c3-7-5`, the minimum comparison of Section 9 as `prop:c3-9-1`, and Section 8 (mathematical scope and the stage 5 supersession) as `rem:c3-8-1`. It omits the review records and process prose; the translation itself has not been reviewed. Notation follows V3 (open box `\mathcal D_I`, law `\nu_{\xi;t}`, normaliser `I_{\xi;t}`, exponent `\mathsf Q_{\xi,t}`, score `L_{\xi,t}`, shell set `\mathsf K_\xi`, branch weight `\mathsf w_\xi`). The archived seed and chessboard subsections are cited as `\draftref{USABLE_NONFLAT_ROUTES, ...}`; Johnsen (IEOT 36, 2000) and the averaging paper (CMP 98, 1985) received bibitems `Johnsen`, `BalabanAVG`. Label map: draft section k = `sec:c3-k` (7.1-7.3 and 9.1-9.5 = `sec:c3-7-j`, `sec:c3-9-j`), lemmas `lem:c3-k-j`, displays `eq:c3-k-j`.

```tex
\section{The Exterior Response and its History Average}\label{app:exterior-chessboard}
This appendix bounds the exterior response $\mathcal B_\xi[f_\xi]$ of \eqref{eq:c-exterior-response} on every branch (Lemma~\ref{lem:exterior-response-bound}, Section~\ref{sec:c3-5}), and pays its history average, together with the uncovered branches of Lemma~\ref{lem:covered}, by one-point witness probabilities on compatible even fine periods (Proposition~\ref{prop:c3-7-5}, Section~\ref{sec:c3-7}). Section~\ref{sec:c3-9} proves the deterministic comparison of the two minima used by the witness argument. The inputs are the Hessian, Schur, chart and primitive bounds of Appendix~\ref{app:background-estimates} and the collar statements of Section~\ref{sec:boundary-law-collar}; Remark~\ref{rem:c3-8-1} records what is and is not controlled. Section~\ref{sec:one-step-insertion} applies Sections~\ref{sec:c3-1}--\ref{sec:c3-5} at the retreated carrier (Lemma~\ref{lem:c5-4-4}) and replaces the history bound of Proposition~\ref{prop:c3-7-5} by its labelled version (Proposition~\ref{prop:c5-6-4}).

\subsection{Objects and the conditional law}\label{sec:c3-1}
Fix a branch with its data $\xi$ (Section~\ref{sec:branch-data}): the young carrier $I$, the retained free carrier $J$, the exterior field $A_{\mathrm e}\in\mathfrak g^J$, extended by zero on every other free bond, the reconstructed field $U_\xi(a)$ of \eqref{eq:c-reconstructed-field}, and the cutoff norm $|\cdot|_\sigma$ (the bond norm $|\cdot|$ of \eqref{eq:literal-cutoff}, operator or normalised Hilbert--Schmidt, fixed once). The inner product $\langle\cdot,\cdot\rangle$, the norm $h$ and the product Hilbert norms are those of Section~\ref{sec:sourced-effective-interaction}; $h\leq|\cdot|_\sigma$ for both permitted norms. The cutoff radius is
\begin{equation}\label{eq:c3-1-1}
    r=\delta_0/g_0=(A_1/A_0)\,p_0(g_0)=A_1(\log g_0^{-2})^{p_0}\;,
\end{equation}
so $r\to\infty$ and $g_0r=\delta_0\to0$ as $g_0\to0$. Every derivative, overlap, range and Hessian constant below is independent of $g_0$ once $L$, the group, the character and the source parameters are fixed; the two conditions
\begin{equation}\label{eq:c3-1-2}
    r\geq1\qquad\text{and}\qquad C_Pg_0(1+2r)\leq\gamma/2\;,
\end{equation}
with $C_P$ the constant of Lemma~\ref{lem:c3-2-1} and $\gamma=\gamma_L/2$, are therefore conditions that $g_0$ lies below a threshold, and they are assumed throughout. If $I=\varnothing$ then $F_\xi(1)=F_\xi(0)$ and the response is zero; below $I\neq\varnothing$.

Write
\begin{equation}\label{eq:c3-1-3}
    H=H_{\xi,II},\qquad \ell_\xi=H_{\xi,IJ}A_{\mathrm e},\qquad j_\xi(a)=\langle\ell_\xi,a\rangle,\qquad s_\xi=1+r+r_{\mathrm e,\xi}\leq1+2r\;,
\end{equation}
with $r_{\mathrm e,\xi}<r$ the retained radius \eqref{eq:convex-native-radius}, the maximum of $|A_{\mathrm e}(b)|_\sigma$ over the retained bonds within $3R_{\mathrm c}$ of $I$ (zero if there is none). No bound is imposed on farther retained fields; every retained input entering $H_{\xi,IJ}$ or a near primitive lies in this collar (Lemma~\ref{lem:collar}(i)). The collar bound holds on every branch, independently of contour coverage: by Lemma~\ref{lem:collar-coverage}(i) every retained bond within $3R_{\mathrm c}$ of $I$ lies in $\mathcal G_\xi\setminus S_1^*$, its factor in $\chi_{\xi,\mathrm e}$ is $\mathbf 1\{|\Psi_\xi(A_{\mathrm e})(b)|<r\}$ and $\Psi_\xi$ is the identity there, so a nonzero retained weight forces $|A_{\mathrm e}(b)|<r$; this is Lemma~\ref{lem:collar-coverage}(iii), not a condition on the covered event. On the open box $\mathcal D_I=\{a\in\mathfrak g^I\, | \,|a_b|_\sigma<r\ \forall b\in I\}$ of \eqref{eq:native-source-boundary-interpolation} the conditional law is, exactly,
\begin{equation}\label{eq:c3-1-4}
    \dd\nu_{\xi;t}(a)=I_{\xi;t}^{-1}e^{\mathsf Q_{\xi,t}(a)}\,\dd a\;,\qquad
    \mathsf Q_{\xi,t}(a)=-\tfrac12\langle a,Ha\rangle-t\langle\ell_\xi,a\rangle+P_{\xi,t}(a)\;,
\end{equation}
zero off $\mathcal D_I$ (\eqref{eq:native-collar-flux}); $I_{\xi;t}$ is the normaliser of \eqref{eq:native-source-boundary-interpolation}, not a flat-reference normaliser, and $\dd a$ is the product Lebesgue measure of the fixed inner product. Throughout $f_\xi(a)=W_\chi(C;U_\xi(a))$ with the exterior data fixed at their branch values, and
\begin{equation}\label{eq:c3-1-5}
    L_{\xi,t}=-j_\xi+\partial_tP_{\xi,t}\;,\qquad
    \mathcal B_\xi[f]=\int_0^1\operatorname{Cov}_{\nu_{\xi;t}}(f,L_{\xi,t})\,\dd t
\end{equation}
(Lemma~\ref{lem:boundary-response}). Derivatives and operator norms refer to the product Hilbert structure, complexified for complex scalar gradients; the fixed matrix-norm equivalence factors of Appendix~\ref{app:background-estimates} are absorbed into the constants before $g_0$ is chosen. The inputs are Lemmas~\ref{lem:regular-bounds} and~\ref{lem:c2-primitive-bounds} at their stated scopes: $\gamma I\leq H\leq m_LI$ with $\gamma=\gamma_L/2$; finite interaction range; and bounded local first and second derivatives of the near primitives on the enlarged box $|a_b|_\sigma\leq2r$ at the inputs $a+tA_{\mathrm e}$, $t\in[0,1]$. They are used at the background of the branch, which is not evaluated at the identity.

\subsection{Local derivative bounds}\label{sec:c3-2}
Let $S_\alpha$ be the full free-input stencil, retained inputs included, of a near primitive $\mathfrak p_\alpha$, let $N_{\mathrm{in}}$ bound its size and $N_{\mathrm{ov}}$ the number of primitive stencils meeting any free bond; both are fixed by $L$ and the group. Let $R=8L+8$, which bounds every stencil diameter, the precision range and the source-to-input distances of the first step ($R\geq\rho_L=4L$, Lemma~\ref{lem:hessian-gauge-locality}; $R\geq2R_{\mathrm{loc}}+4$, Lemma~\ref{lem:collar-coverage}). Distances of bonds are the periodic $\ell^\infty$ distances of their initial sites, plus one for differing directions. Put
\begin{equation}\label{eq:c3-2-1}
    \mathsf K_\xi=\{b\in I\, : \,\operatorname{dist}(b,J)\leq R\}\;,\qquad
    I_C=\{b\in I\, : \,b\in\mathcal F_r\text{ for some traversal }r\text{ of }C\}\;,
\end{equation}
with $\mathcal F_r$ the free-input stencil \eqref{eq:regular-stencil-extension-support} of the contour bond $r$; the source depends on the young field only through $I_C$ (Lemma~\ref{lem:row-locality}).

\begin{lemma}[local bounds]\label{lem:c3-2-1}
There are constants $C_P$, $C_S$, $C_{\mathrm{resp},\chi}$, depending on $L$, the group, the character and the source constants only, such that on the enlarged box $\{|a_b|_\sigma\leq2r\ \forall b\}$, uniformly in $t\in[0,1]$ and in the branch,
\begin{gather}
    \|D^2_aP_{\xi,t}\|\leq C_Pg_0s_\xi\;,\qquad
    h(\nabla_b\partial_tP_{\xi,t})\leq C_Sg_0s_\xi\,r_{\mathrm e,\xi}\mathbf 1_{\mathsf K_\xi}(b)\;,\qquad
    h((\ell_\xi)_b)\leq m_Lr_{\mathrm e,\xi}\mathbf 1_{\mathsf K_\xi}(b)\;,\label{eq:c3-2-2}\\
    \sup_a h(\nabla_bf_\xi(a))\leq C_{\mathrm{resp},\chi}g_0\mathbf 1_{I_C}(b)\;.\label{eq:c3-2-3}
\end{gather}
Under \eqref{eq:c3-1-2} the function $-\mathsf Q_{\xi,t}$ is strongly convex on $\mathcal D_I$ with Hessian at least $\rho=\gamma/2$.
\end{lemma}

\begin{proof}
The first bound of \eqref{eq:c3-2-2} is the second-derivative bound of Lemma~\ref{lem:c2-primitive-bounds} on the enlarged box with the finite overlap $N_{\mathrm{ov}}$. For the second, $\partial_tP_{\xi,t}(a)=\sum_\alpha D\mathfrak p_\alpha(a+tA_{\mathrm e})[A_{\mathrm e}]$, so each summand of $\nabla_b\partial_tP_{\xi,t}$ is $D^2\mathfrak p_\alpha$ applied to a young direction at $b$ and to $A_{\mathrm e}|_{S_\alpha}$; it vanishes unless $S_\alpha$ contains a retained input, which lies in the collar, so $h(A_{\mathrm e}|_{S_\alpha})\leq\sqrt{N_{\mathrm{in}}}\,r_{\mathrm e,\xi}$, and summing the at most $N_{\mathrm{ov}}$ stencils meeting $b$ gives the bound; the support statement follows from the range $R$ of the stencils. The third bound is the cross-row Schur bound of Lemma~\ref{lem:regular-bounds} ($\sum_{b'}\|H_{bb'}\|\leq m_L$) applied to $A_{\mathrm e}$ on the collar, with $(H_{\xi,IJ})_{bb'}=0$ for $d(b,b')>\rho_L\leq R$ (Lemma~\ref{lem:hessian-gauge-locality}). For \eqref{eq:c3-2-3}, differentiate the normalised character of the ordered link product: by the rowwise reconstruction (Lemma~\ref{lem:row-locality}) and the uniform charts (Lemma~\ref{lem:c2-uniform-chart}) on the enlarged box with the exterior fixed, each affected link has a phase derivative bounded by $Cg_0$, a fixed input affects a bounded number of links, a square has bounded traversal multiplicity, the derivative of the character is bounded in the invariant tangent norm on the compact group, and the other links remain unitary inside the closed contraction; no open Wilson segment is estimated separately. The convexity statement is $\gamma I\leq H$ together with $\|D^2P_{\xi,t}\|\leq C_Pg_0s_\xi\leq C_Pg_0(1+2r)\leq\gamma/2$.
\end{proof}

\subsection{An extension within the proved chart}\label{sec:c3-3}
The enlarged-box input matters: a radial extension bounded only in $h$ can leave the operator-norm box, and a radius proportional to $3s_\xi$ can exceed the enlarged box. Let $B_\sigma=\{x\in\mathfrak g\, : \,|x|_\sigma\leq1\}$, let $\Pi_r$ be the Hilbert metric projection onto the closed convex set $\tfrac32rB_\sigma$, let $\phi$ be a nonnegative smooth $h$-radial mollifier supported in the unit $h$-ball with integral one, $\phi_\epsilon(y)=\epsilon^{-d_G}\phi(y/\epsilon)$, and put $\epsilon=1/(4\sqrt N)$. Define
\begin{equation}\label{eq:c3-3-1}
    T_r(x)=\int_{\mathfrak g}\Pi_r(x-y)\,\phi_{\epsilon r}(y)\,\dd y\qquad(x\in\mathfrak g)\;.
\end{equation}

\begin{lemma}[the extension map]\label{lem:c3-3-1}
$T_r$ is smooth and $\operatorname{Ad}$-equivariant, and
\begin{equation}\label{eq:c3-3-2}
    T_r(x)=x\ \text{ if }|x|_\sigma\leq r,\qquad |T_r(x)|_\sigma\leq\tfrac32r,\qquad \|DT_r\|\leq1,\qquad \|D^2T_r\|\leq C_\sigma/r\;,
\end{equation}
with $C_\sigma$ depending on the norm and $N$ only.
\end{lemma}

\begin{proof}
Metric projection and the mollifier commute with the orthogonal adjoint action, which gives the equivariance. If $h(y)\leq\epsilon r$ then $|y|_\sigma\leq\sqrt N\,h(y)\leq r/4$, so for $|x|_\sigma\leq r$ the projection is the identity at $x-y$ (and on a neighbourhood of this ball), and its convolution there equals $x$ because the mollifier has integral one and zero first moment. The range statement is the convexity of $\tfrac32rB_\sigma$. Metric projection is $1$-Lipschitz and convolution preserves this, giving $\|DT_r\|\leq1$; differentiating the bounded weak first derivative of $\Pi_r$ against the mollifier of scale $\epsilon r$ gives $\|D^2T_r\|\leq C_\sigma/r$.
\end{proof}

Apply $T_r$ bondwise to the young inputs only and write $T$ for the product map on $\mathfrak g^I$. Define
\begin{equation}\label{eq:c3-3-3}
    \widetilde P_t(a)=\sum_{\alpha\ \mathrm{near}}\bigl[\mathfrak p_\alpha(Ta+tA_{\mathrm e})-\mathfrak p_\alpha(tA_{\mathrm e})\bigr],\qquad
    \widetilde f(a)=f_\xi(Ta),\qquad
    \widetilde L_t(a)=-\langle\ell_\xi,a\rangle+\partial_t\widetilde P_t(a)\;.
\end{equation}

\begin{lemma}[the extended objects]\label{lem:c3-3-2}
$\widetilde P_t$, $\widetilde f$ and $\widetilde L_t$ are defined and smooth on all of $\mathfrak g^I$, $|\widetilde f|\leq1$, and on $\mathcal D_I$: $\widetilde f=f_\xi$, $\widetilde P_t=P_{\xi,t}-P_{\xi,t}(0)$ and $\widetilde L_t-L_{\xi,t}=-\partial_tP_{\xi,t}(0)$, a constant, so that $\operatorname{Cov}_{\nu_{\xi;t}}(\widetilde f,\widetilde L_t)=\operatorname{Cov}_{\nu_{\xi;t}}(f_\xi,L_{\xi,t})$. After enlarging $C_P$ (before $g_0$ is chosen), uniformly in $t$ and $a\in\mathfrak g^I$: $\|D^2\widetilde P_t\|\leq C_Pg_0s_\xi$, the block Schur row and column sums of $D^2\widetilde P_t$ are at most $C_Pg_0s_\xi$ with range $R$,
\begin{equation}\label{eq:c3-3-4}
    h(\nabla_b\partial_t\widetilde P_t)\leq C_Sg_0s_\xi\,r_{\mathrm e,\xi}\mathbf 1_{\mathsf K_\xi}(b)\;,\qquad
    h(\nabla_b\widetilde f)\leq C_{\mathrm{resp},\chi}g_0\mathbf 1_{I_C}(b)\;.
\end{equation}
\end{lemma}

\begin{proof}
The image $Ta$ has young cutoff norm at most $\tfrac32r<2r$, so every primitive and every affected reconstruction row stays in the enlarged chart of Lemma~\ref{lem:c2-uniform-chart}, the exterior fields being fixed; the real reconstruction gives group-valued links, whence $|\widetilde f|\leq1$. On $\mathcal D_I$, $T$ is the identity (Lemma~\ref{lem:c3-3-1}), which gives the three identities; a constant shift of one operand leaves the covariance unchanged. The Hessian of $\widetilde P_t$ is $D^2\mathfrak p_\alpha(DT\cdot,DT\cdot)+D\mathfrak p_\alpha\,D^2T$ summed over the near primitives: the first term is $O(g_0s_\xi)$ by Lemma~\ref{lem:c3-2-1} and $\|DT\|\leq1$, the second is $O(g_0s_\xi^2/r)=O(g_0s_\xi)$ by the first-derivative bound of Lemma~\ref{lem:c2-primitive-bounds}, $\|D^2T\|\leq C_\sigma/r$, $r\geq1$ and $s_\xi\leq1+2r\leq3r$. Each input belongs to at most $N_{\mathrm{ov}}$ stencils and each stencil has at most $N_{\mathrm{in}}$ blocks, so summing at most $N_{\mathrm{ov}}N_{\mathrm{in}}$ blocks with this chain-rule bound gives the operator and Schur bounds; the supports and the range are those of the original stencils. The mixed derivative $\nabla_b\partial_t\widetilde P_t$ contains no second derivative of $T$, since $T$ does not depend on $t$, so the proof of Lemma~\ref{lem:c3-2-1} gives the first bound of \eqref{eq:c3-3-4} with $\|DT\|\leq1$; the second is \eqref{eq:c3-2-3} composed with $DT$.
\end{proof}

\subsection{Covariance decay at the hard boundary}\label{sec:c3-4}
For a positive integer $n$ define the barrier and the barrier laws
\begin{gather}
    \beta_n(a)=n\sum_{b\in I}\bigl[\operatorname{dist}_h(\,\cdot\,,rB_\sigma)^2*\phi_{n^{-2}}\bigr](a_b)\;,\label{eq:c3-4-1}\\
    V_{n,t}(a)=\tfrac12\langle a,Ha\rangle+t\langle\ell_\xi,a\rangle-\widetilde P_t(a)+\beta_n(a)\;,\qquad
    \dd\nu_{n,t}=Z_{n,t}^{-1}e^{-V_{n,t}(a)}\,\dd a\quad\text{on }\mathfrak g^I\;.\notag
\end{gather}
The squared distance to a convex set is convex and convolution preserves convexity, so the barrier Hessian is positive and diagonal in the bond index. For fixed $n$ the potential is smooth with bounded Hessian and Gaussian confinement, its Hessian is at least $\rho I$ (Lemma~\ref{lem:c3-3-2} and \eqref{eq:c3-1-2}), and its off-diagonal block row and column sums are at most
\begin{equation}\label{eq:c3-4-2}
    M_*=m_L+\gamma/2\;,
\end{equation}
with range at most $R$, independently of $n$, $t$, the volume and the branch (the barrier is diagonal; $m_L$ bounds the Schur sums of $H$ and $\gamma/2\geq C_Pg_0s_\xi$ those of $D^2\widetilde P_t$).

\begin{lemma}[Helffer--Sj\"ostrand identity and decay]\label{lem:c3-4-1}
Let $\mathscr A_{n,t}=\mathscr L_{n,t}\otimes I+D^2V_{n,t}$ with $\mathscr L_{n,t}=-\Delta+\nabla V_{n,t}\cdot\nabla$, on the Hilbert direct sum over $b\in I$ of $L^2(\nu_{n,t};\mathfrak g)$. Then $\mathscr A_{n,t}\geq\rho I$, and for real $u,v$ in the weighted space $H^1(\nu_{n,t})$
\begin{equation}\label{eq:c3-4-3}
    \operatorname{Cov}_{\nu_{n,t}}(u,v)=\langle\nabla u,\mathscr A_{n,t}^{-1}\nabla v\rangle_{L^2(\nu_{n,t})}\;.
\end{equation}
With $\mu=R^{-1}\log(1+\gamma/(4M_*))$ and $\Pi_b$ the projection onto the $b$-component,
\begin{equation}\label{eq:c3-4-4}
    \|\Pi_b\mathscr A_{n,t}^{-1}\Pi_c\|\leq\frac4\gamma e^{-\mu d(b,c)}\;,\qquad
    |\operatorname{Cov}_{\nu_{n,t}}(u,v)|\leq\frac4\gamma\sum_{b,c\in I}e^{-\mu d(b,c)}\|\nabla_bu\|_{L^2(\nu_{n,t})}\|\nabla_cv\|_{L^2(\nu_{n,t})}\;.
\end{equation}
For complex $u$, $v$ the same bound holds with the gradient norm of $u$ read as the sum of the gradient norms of its real and imaginary parts (a factor at most two, absorbed into $C_{\mathrm{resp},\chi}$).
\end{lemma}

\begin{proof}
The identity \eqref{eq:c3-4-3} is \cite[Proposition 4.5]{Johnsen} for the $C^2$ potential $V_{n,t}+\log Z_{n,t}$ (normalised; the additive constant leaves the derivatives unchanged); its hypothesis, the closed range of the exterior derivative, follows from $\mathscr A_{n,t}\geq\rho I$ by \cite[Theorem 1.3 and (4.39)]{Johnsen}, and at fixed $n$ the bounded Hessian identifies the displayed operator with the closed form of \cite[Section 4]{Johnsen}. The source is bounded, the score grows at most linearly, and both have bounded gradients, so both lie in $H^1(\nu_{n,t})$. For a fixed $c\in I$ let $W_c$ multiply the component $b$ by $e^{\mu d(b,c)}$; it is constant in field space, hence commutes with the scalar generator $\mathscr L_{n,t}\otimes I$ and with every diagonal Hessian block, the barrier included, and the off-diagonal Schur bounds give $\|W_c\mathscr A_{n,t}W_c^{-1}-\mathscr A_{n,t}\|\leq M_*(e^{\mu R}-1)\leq\rho/2$ by the choice of $\mu$. $W_c$ and its inverse are bounded at finite volume, so a resolvent Neumann series gives $\|W_c\mathscr A_{n,t}^{-1}W_c^{-1}\|\leq(\rho-\rho/2)^{-1}=4/\gamma$, which is the first bound of \eqref{eq:c3-4-4}; the second follows from \eqref{eq:c3-4-3}. The large diagonal barrier never enters the decay constant.
\end{proof}

\begin{lemma}[the barrier limit]\label{lem:c3-4-2}
For $u,v$ bounded or of linear growth with bounded gradients, $\operatorname{Cov}_{\nu_{n,t}}(u,v)\to\operatorname{Cov}_{\nu_{\xi;t}}(u,v)$ as $n\to\infty$. Consequently the second bound of \eqref{eq:c3-4-4} holds for $\nu_{\xi;t}$ on the hard box $\mathcal D_I$, with the gradient norms taken as global suprema, $\|\nabla_bu\|_\infty\|\nabla_cv\|_\infty$ in place of the $L^2$ norms.
\end{lemma}

\begin{proof}
At finite volume $\beta_n\to0$ on the closed cutoff body $\{|a_b|_\sigma\leq r\ \forall b\}$ and $\beta_n\to\infty$ outside it, the boundary of the body has Lebesgue measure zero, and $\beta_n\geq0$ together with the Gaussian confinement supplies an integrable majorant for the source and the linear-growth score and their products; dominated convergence gives the convergence of the normalised integrals, hence of the covariances, to those of $\nu_{\xi;t}$ on $\mathcal D_I$. The gradient bounds on the right of \eqref{eq:c3-4-4} are global and independent of $n$, so the constants pass to the limit. No translated cutoff and no new exterior law is introduced.
\end{proof}

\subsection{The response}\label{sec:c3-5}
Put
\begin{equation}\label{eq:c3-5-1}
    D_\xi=\sum_{b\in I_C}e^{-\mu d(b,J)/2}\;,
\end{equation}
with $\mu$ of Lemma~\ref{lem:c3-4-1}; $D_\xi=0$ when $J=\varnothing$ (then the score vanishes).

\begin{lemma}[the exterior response]\label{lem:exterior-response-bound}
Under \eqref{eq:c3-1-2}, on every branch and for every $t\in[0,1]$,
\begin{equation}\label{eq:c3-5-2}
    |\operatorname{Cov}_{\nu_{\xi;t}}(f_\xi,L_{\xi,t})|\leq C_{\mathrm{resp},\chi}\,g_0r\sum_{b\in I_C}e^{-\mu d(b,J)/2}\;,\qquad
    |\mathcal B_\xi[f_\xi]|\leq C_{\mathrm{resp},\chi}\,g_0r\,D_\xi\;,
\end{equation}
after enlarging the constant $C_{\mathrm{resp},\chi}$ of Lemma~\ref{lem:c3-2-1}; it depends on $\gamma$, $m_L$, $R$, $N_{\mathrm{in}}$, $N_{\mathrm{ov}}$, $C_P$, $C_S$, $C_\sigma$, the character, the group and the fixed source parameters, and is independent of $g_0$, the branch, the volume, $t$ and the barrier index.
\end{lemma}

\begin{proof}
By Lemma~\ref{lem:c3-3-2}, $\operatorname{Cov}_{\nu_{\xi;t}}(f_\xi,L_{\xi,t})=\operatorname{Cov}_{\nu_{\xi;t}}(\widetilde f,\widetilde L_t)$, and Lemma~\ref{lem:c3-4-2} bounds it by $(4/\gamma)\sum_{b,c\in I}e^{-\mu d(b,c)}\|\nabla_b\widetilde f\|_\infty\|\nabla_c\widetilde L_t\|_\infty$. By \eqref{eq:c3-3-4} and \eqref{eq:c3-2-2}, $\|\nabla_c\widetilde L_t\|_\infty\leq(m_L+C_Sg_0s_\xi)r_{\mathrm e,\xi}\mathbf 1_{\mathsf K_\xi}(c)\leq(m_L+\gamma/2)\,r\,\mathbf 1_{\mathsf K_\xi}(c)$ (as $r_{\mathrm e,\xi}<r$) and $\|\nabla_b\widetilde f\|_\infty\leq C_{\mathrm{resp},\chi}g_0\mathbf 1_{I_C}(b)$. For the shell step, $d(c,J)\leq R$ on $\mathsf K_\xi$, so $d(b,c)\geq d(b,J)-R$ and $e^{-\mu d(b,c)}=e^{-\mu d(b,c)/2}e^{-\mu d(b,c)/2}\leq e^{\mu R/2}e^{-\mu d(b,J)/2}\,e^{-\mu d(b,c)/2}$; the sum of $e^{-\mu d(b,c)/2}$ over all periodic bonds $c$ is bounded by the infinite-lattice shell sum $S_{\mu/2}=\sup_b\sum_ce^{-\mu d(b,c)/2}$, uniformly in the periods. Collecting the constants gives the first bound of \eqref{eq:c3-5-2}; integrating over $t\in[0,1]$ in \eqref{eq:c3-1-5} gives the second.
\end{proof}

\begin{remark}[the surface terms are retained]\label{rem:c3-5-1}
In the notation \eqref{eq:native-collar-mean-direction}--\eqref{eq:native-collar-flux}, Lemma~\ref{lem:ibp} writes the integrand of the response as
\begin{equation}\label{eq:c3-5-3}
    -\mathbb E_{\nu_{\xi;t}}[D_{m_\xi}f_\xi]+\operatorname{Cov}_{\nu_{\xi;t}}(f_\xi,\partial_tP_{\xi,t}-D_{m_\xi}P_{\xi,t})+\mathcal T_{\xi,t}[f_\xi]-\mathbb E_{\nu_{\xi;t}}[f_\xi]\,\mathcal T_{\xi,t}[1]\;,
\end{equation}
with the hard-cutoff flux $\mathcal T_{\xi,t}[u]=I_{\xi;t}^{-1}\int_{\partial\mathcal D_I}u\,e^{\mathsf Q_{\xi,t}}\langle m_\xi,n\rangle\,\dd S$. Lemma~\ref{lem:exterior-response-bound} bounds this whole expression: neither flux is set to zero or estimated separately. The extension $T$ is the identity on a neighbourhood of the cutoff body and the barrier limit returns the original measure, so the boundary traces and the normalised covariance in \eqref{eq:c3-5-3} are those of Section~\ref{sec:boundary-law-collar}.
\end{remark}

\subsection{The physical substitution}\label{sec:c3-6}
Let $\mathsf w_\xi=e^{c_\xi}I_{\xi;1}=\mathcal J^{\mathrm a}_\xi[1]$ be the branch weight \eqref{eq:c-collar-identity} and $\mathcal O$ the outer operation of \eqref{eq:native-source-explicit-outer-operation}, so that $\mathcal Z_0=\int\mathcal O[\mathsf w_\xi](V)\,\dd V$ (\eqref{eq:native-source-physical-ratio}). Define the history expectation and probability
\begin{equation}\label{eq:c3-6-1}
    \mathbb E_{\mathrm h}[X]=\mathcal Z_0^{-1}\int\mathcal O[\mathsf w_\xi X](V)\,\dd V\;,\qquad
    \mathbb P_{\mathrm h}(A)=\mathbb E_{\mathrm h}[\mathbf 1_A]\;,
\end{equation}
for nonnegative or bounded Borel functions $X$ of the branch data, and let $A_{\mathrm{cov}}$ be the set of covered branches of Lemma~\ref{lem:covered}: every contour bond is a bond of $\Omega_1$ and every free input $\mathcal F_r$ of the contour lies in $I$. The event $A_{\mathrm{cov}}$ is determined by $\Omega_1$, $R_1$ and the fixed contour templates; it and $D_\xi$ are measurable functions of the outer branch data, constant in the young integration. The combined exterior-response and uncovered contribution to the Wilson numerator is
\begin{equation}\label{eq:c3-6-2}
    E_{\mathrm{bdry}}=\mathbb E_{\mathrm h}\bigl[\mathbf 1_{A_{\mathrm{cov}}}\mathcal B_\xi[f_\xi]+\mathbf 1_{A_{\mathrm{cov}}^c}F_\xi(1)\bigr]\;,
\end{equation}
the exterior response on the covered branches and the whole conditional expectation on the uncovered ones (\eqref{eq:c-exterior-response}, \eqref{eq:c-one-step-branch-identity}).

\begin{corollary}\label{cor:c3-6-1}
Under \eqref{eq:c3-1-2},
\begin{equation}\label{eq:c3-6-3}
    \Bigl|\mathcal Z_0^{-1}\int\mathcal O\bigl[\mathsf w_\xi\mathbf 1_{A_{\mathrm{cov}}}\mathcal B_\xi[f_\xi]\bigr](V)\,\dd V\Bigr|\leq C_{\mathrm{resp},\chi}\,g_0r\,\mathbb E_{\mathrm h}[\mathbf 1_{A_{\mathrm{cov}}}D_\xi]\;,\qquad
    |E_{\mathrm{bdry}}|\leq C_{\mathrm{resp},\chi}\,g_0r\,\mathbb E_{\mathrm h}[\mathbf 1_{A_{\mathrm{cov}}}D_\xi]+\mathbb P_{\mathrm h}(A_{\mathrm{cov}}^c)\;.
\end{equation}
\end{corollary}

\begin{proof}
$\mathsf w_\xi\geq0$ and $\mathcal O$ is positive, so Lemma~\ref{lem:exterior-response-bound} gives the first bound pointwise on the branches; $|F_\xi(1)|\leq1$ gives the second. No conditional or flat-reference normaliser replaces $\mathcal Z_0$, and $c_\xi$ stays inside $\mathsf w_\xi$.
\end{proof}

\subsection{The history average by one-point witnesses}\label{sec:c3-7}
This section assumes compatible even fine periods: every fine period is a multiple of $\ell=LMR_1$ (\eqref{eq:c-standing-conditions}) and even. This is a restriction relative to the compatible periods of Section~\ref{sec:sourced-effective-interaction}; it includes the torus with periods $2L^m$ when the partitions fit. Lemma~\ref{lem:exterior-response-bound} needs no parity restriction, and no odd-period history bound is asserted.

Write $\ell=LMR_1$ for the macro side ($R_1$ the scale integer), $B_\xi=\Lambda_1^c$ for the filled bad region, $E(X)$ for the set of positive fine bonds with at least one endpoint in a set $X$ of sites, and $n_C$ for the number of contour traversals. Let $\Gamma_C$ be the deterministic set of the contour bonds together with the free-input templates of their reconstruction rows, projected periodically from the torus templates before any history is selected; there is a constant $C_L$ with $|\Gamma_C|\leq C_Ln_C$, and $I_C\subseteq\Gamma_C$ on every branch (the young designated variables are eliminated, so their free-input stencils, not the designated bonds, are the members of $\Gamma_C$). For a positive bond $z$ define the marked probability
\begin{equation}\label{eq:c3-7-1}
    p_z=\mathcal Z_0^{-1}\int\mathcal O\bigl[\mathsf w_\xi\mathbf 1\{z\in E(B_\xi)\}\bigr](V)\,\dd V=\mathbb P_{\mathrm h}(z\in E(B_\xi))\;;
\end{equation}
the mark depends on the regions and on the deterministic filling, not on the young variable.

\begin{lemma}[reduction to one-point marks]\label{lem:c3-7-1}
Let $c=\mu/2$ and $S_c=\sup_b\sum_ze^{-cd(b,z)}$, the periodic bond shell sum, bounded by its infinite-lattice counterpart uniformly in the periods. Pointwise on every branch
\begin{equation}\label{eq:c3-7-2}
    D_\xi\leq\sum_{b\in\Gamma_C}\sum_ze^{-cd(b,z)}\mathbf 1\{z\in E(B_\xi)\}\;,\qquad
    \mathbf 1_{A_{\mathrm{cov}}^c}\leq\sum_{b\in\Gamma_C}\mathbf 1\{b\in E(B_\xi)\}\;.
\end{equation}
Hence, if $p_z\leq q$ for every positive bond $z$,
\begin{equation}\label{eq:c3-7-3}
    \mathbb E_{\mathrm h}[D_\xi]\leq C_LS_cn_Cq\;,\qquad \mathbb P_{\mathrm h}(A_{\mathrm{cov}}^c)\leq C_Ln_Cq\;.
\end{equation}
\end{lemma}

\begin{proof}
$J\subseteq E(B_\xi)$: a free bond not in $I$ has no endpoint in $\Lambda_1$. So each $b\in I_C\subseteq\Gamma_C$ contributes $e^{-cd(b,J)}\leq\sum_{z\in J}e^{-cd(b,z)}\leq\sum_ze^{-cd(b,z)}\mathbf 1\{z\in E(B_\xi)\}$. If coverage fails, either a contour bond is not a bond of $\Omega_1$, and then it meets $B_\xi$ since $\Lambda_1\subseteq\Omega_1$, or a free input of the contour is not in $I$, and then it is retained in $J$ or lies outside $\Omega_1$ and meets $B_\xi$; in both cases some $b\in\Gamma_C$ lies in $E(B_\xi)$. Taking $\mathbb E_{\mathrm h}$ of \eqref{eq:c3-7-2} (Tonelli; all integrands nonnegative) and using $p_z\leq q$ and $|\Gamma_C|\leq C_Ln_C$ gives \eqref{eq:c3-7-3}.
\end{proof}

\subsubsection*{Cutoff failures give local witnesses}\label{sec:c3-7-1}
The witness argument is the first-step seed proof of the archived note \draftref{USABLE\_NONFLAT\_ROUTES, sec:first-step-seed} (its displays from eq:seed-layer-sizes to eq:seed-support-inclusion), whose operands are the original unresummed cutoffs CRE (1.1), (1.4), (1.8), (1.18), before the boundary substitution. Only the following conclusion is used: a bad eligible test forces a fine plaquette with $|U(\partial p)-\id|_\sigma\geq\theta$ in its neighbourhood, or an active mean-transport variable with $|w-\id|_\sigma\geq\theta$ there (the $P_0$ and $P_1$ alternatives need no gauge-variable witness), with the threshold
\begin{equation}\label{eq:c3-7-4}
    \theta=\min\Bigl(\varepsilon_0,\ \frac{\varepsilon_1}{4B_3N^{3/2}L^2},\ \frac{\delta_0}{2C_Q}\Bigr)\;,\qquad
    C_Q=(9K_L+2)(1+2B_3N^{3/2}L^2)\;,
\end{equation}
where $K_L$ is the maximum number of plaquettes in the fixed two-block path fillings of RG1 (0.4), (0.11). The norm is the cutoff norm $|\cdot|_\sigma$, and the mean and comparison constants are chosen for it. The seed is used on the original earlier-cutoff and averaging-constraint support only, not for arbitrary frozen exterior data. Its common local width $w$ lies between $LM_2R_1$ and $L^2M_2R_1$, with one convention throughout, and its macro width is $\ell$; these are the conventions of the branch hypotheses of Section~\ref{sec:branch-data}.

\begin{lemma}[a bad test forces a witness]\label{lem:c3-7-2}
For $g_0$ below a threshold depending on $L$, the group, $M_1$, $M_2$ and the source constants, on the original cutoff support: every bad $P_0$, $P_1$, $Q_1$ or $R_1$ test forces a plaquette or gauge-variable witness at threshold $\theta$ within distance $K\ell$ of every bond $z\in E(B_\xi)$ whose membership it causes, with the fixed $K=256$; and the number of plaquette and gauge-variable labels in such a neighbourhood is at most
\begin{equation}\label{eq:c3-7-5}
    n_W=7(2K\ell+7)^4\;.
\end{equation}
\end{lemma}

\begin{proof}
For the $R_1$ test the seed needs the comparison of the two minima on the twice enlarged carrier of every eligible cube $Q$, uniformly in its label, proved in Proposition~\ref{prop:c3-9-1} below:
\begin{equation}\label{eq:c3-7-6}
    \sup_{b\in(Q_w^{[2]})^*}|U_1(b)U_{1,Q}(b)^{-1}-\id|_\sigma\leq C_{L,G}\varepsilon_1e^{-c_{L,G}LM_2R_1}<\delta_0/10\;.
\end{equation}
It does not assume that $U_1$ lies in the support of $\zeta$ or of the other fine-field cutoffs. On the native principal chart a bad $R_1$ label forces $|g_0A(b)|_\sigma\geq\delta_0$ at a free bond $b$ of the cube; the eigenvalue inequality $|e^{iX}-\id|_\sigma\geq(2/\pi)|X|_\sigma$, valid when every eigenvalue of $X$ lies in $[-\pi,\pi]$ (as on the chart) in both permitted norms, and \eqref{eq:c3-7-6} give, for the gauge-fixed field $\widetilde U$,
\begin{equation}\label{eq:c3-7-7}
    |\widetilde U(b)U_{1,Q}(b)^{-1}-\id|_\sigma\geq(2/\pi-1/10)\delta_0>\delta_0/2\;.
\end{equation}
If every witness in the neighbourhood were below $\theta$, the seed's two-block comparison would give $|\widetilde U(b)U_{1,Q}(b)^{-1}-\id|_\sigma\leq C_Q\theta\leq\delta_0/2$, a contradiction; so the label is excluded. CRE (1.1), (1.4), (1.8), (1.18) are sharp characteristic partitions at their printed thresholds, so these inequalities make the corresponding bad factor vanish; off-chart configurations are not added to (1.18), which is introduced after the logarithmic reconstruction (1.13)--(1.15). For the distances: before filling, CRE (1.10), (1.20) give the bad region as $Q_1'^{\sim4}\cup(B(P_1^1)^c)^{\sim5}\cup R_1'^{\sim1}$, with $B(P_1^1)^c\subseteq P_0'^{\sim2}\cup P_1'^{\sim1}$ under either active-set reading, so a point of this region is within $10\ell$ of a bad test. The modification after (1.20) fills only components contained in cubes of side less than $100\ell$, so every added point is within $100\ell$ of an original unfilled bad point; this also holds if small merged components are filled again, since by induction every current component contains an original bad point and each fill is performed inside a cube of side less than $100\ell$ containing that component (every point of the rectangular hull of such a component is within $100\ell$ of a chosen original bad point of it, and overlapping hulls or later merges preserve the presence of an original point), so there is no cumulative distance loss. CRE (2.9) gives $R_0\leq LR_1$ for small coupling. Including each test's witness neighbourhood and incident bonds, every $z\in E(B_\xi)$ forces a witness within $K\ell$ of $z$ with $K=256$. The count \eqref{eq:c3-7-5} of the plaquette and gauge-variable labels in that neighbourhood is an overcount on a small periodic torus, which is harmless.
\end{proof}

\subsubsection*{The marked probability retains the physical normaliser}\label{sec:c3-7-2}

\begin{lemma}[the marked density and its reversal]\label{lem:c3-7-3}
Let $A^\Psi_{\mathrm e}=\Psi_\xi(A_{\mathrm e})$ and let $\mathscr E_\xi(B)$ be the pre-boundary-change exponent of CRE (1.15), its outer prefactor excluded (\eqref{eq:native-collar-full-exponent}). With $c_\xi$ of \eqref{eq:native-collar-boundary-constant}, pointwise on $\mathfrak g^I$,
\begin{equation}\label{eq:c3-7-8}
    e^{c_\xi}K_{\xi;1}(a)=\mathbf 1_{\mathcal D_I}(a)\,|\det D\Psi_\xi(A_{\mathrm e})|\,\exp\mathscr E_\xi\bigl(\Psi_\xi(a+A_{\mathrm e})\bigr)\;,
\end{equation}
and the composed retained cutoff $\chi_{\xi,\mathrm e}$ and $\zeta_\xi$ multiply both sides. Consequently, on compatible even fine periods, for every positive bond $z$,
\begin{equation}\label{eq:c3-7-9}
    p_z\leq\bigl(\mu_0\otimes q_g^{\otimes\mathcal I}\otimes\mathrm{Haar}^{\otimes T}\bigr)(W_z)\;,\qquad
    \mu_0(\dd U)=\mathcal Z_0^{-1}e^{-\mathsf E}e^{-S(U)/g_0^2}\,\dd U\;,
\end{equation}
where $W_z$ is the event that some plaquette or some auxiliary gauge variable in the deterministic $K\ell$-neighbourhood of $z$ is a witness at threshold $\theta$, $\mathcal I$ is the set of pairs $(y,x)$ of a block centre $y$ and a noncentral site $x$ of its block, $T$ the set of centres and unused sites, and
\begin{equation}\label{eq:c3-7-10}
    q_g(\dd w)=z_g^{-1}\mathbf 1\{|w-\id|_\sigma<\varepsilon_0\}e^{-s_G(w)/g_0^2}\,\dd w\;,\qquad s_G(w)=1-\operatorname{Re}\tr_Nw\;,
\end{equation}
with $z_g$ the integral of the displayed density, CRE's gauge normaliser.
\end{lemma}

\begin{proof}
$\Psi_\xi$ is the identity in every near stencil and its support $S_1^*$ is disjoint from $I$, so $\Psi_\xi(a+A_{\mathrm e})=a+A^\Psi_{\mathrm e}$ (\eqref{eq:c-bondwise-shift}). Expanding the quadratic form of $\mathscr E_\xi$ into its $II$, $IJ$, $JJ$ blocks, leaving every far primitive at $A^\Psi_{\mathrm e}$ and retaining the boundary determinant gives \eqref{eq:c3-7-8}, which is the computation of Lemma~\ref{lem:collar}(ii); the retained cutoff and $\zeta_\xi$ are factors of the integrand outside the $a$-integral. Together with the outer prefactor $\kappa_\xi$ the right side recombines into the transformed CRE (1.15) density, boundary Jacobian included. Now reverse the changes of variables of Section~\ref{sec:branch-data} with the mark $\mathbf 1\{z\in E(B_\xi)\}$ inserted; the mark commutes with the earlier resummation because the final regions and the filling are fixed in each term. Undo $\Psi_\xi$, the free-variable constraint elimination, the scaling, the nonlinear constraint linearisation of (1.14), the logarithmic chart of (1.13) with its Haar density, and the translation about $U_1$, in this order; the retained cutoff stays composed with $\Psi_\xi$ and $\zeta$ remains in that composition, boundary-fluctuation dependence included. The marked integral is then CRE (1.6) with its four original partitions and the site-gauge integration, no determinant or normalisation discarded; the unmarked chain is $\mathcal Z_0=e^{-\mathsf E}\int e^{-S(U)/g_0^2}\,\dd U$. For each active block centre $y$ and noncentral $x$ let $w_{yx}$ be its mean transport after the gauge change; RG1 (0.6) and CRE (1.5) give the Haar substitution $v(x)=w_{yx}^{-1}h_yU(y,x)$, $v(y)=h_y$, with Jacobian one, and the law of $w$ is \eqref{eq:c3-7-10}. Add independent $q_g$ variables of integral one for the inactive indices and independent Haar variables for the centres and unused sites. The earlier $P_0$, $P_1$ choices depend on $U$ and its coarse gauge orbit, not on these auxiliary variables. By Lemma~\ref{lem:c3-7-2} the mark is dominated by $\mathbf 1_{W_z}$, and $W_z$ does not depend on the later $Q_1$, $R_1$ labels; only after this enlargement are the characteristic partitions summed to one. This gives \eqref{eq:c3-7-9}. The product measure is a representation of the integral before the history conditions, not an independence statement about them; plaquette witness norms and the conjugation-invariant gauge-variable norms are gauge-invariant scalars under the simultaneous gauge transformations, and no open Wilson contraction is estimated.
\end{proof}

\subsubsection*{One-point tails and summation}\label{sec:c3-7-3}

\begin{lemma}[single-witness tails]\label{lem:c3-7-4}
Let $d_G=\dim G$, $b_G=1/(2N)$, so that $s_G(w)\geq b_G|w-\id|_\sigma^2$, and let $c_H$, $g_H>0$ be such that the Haar measure of the operator ball of radius $g_0\leq g_H$ is at least $c_Hg_0^{d_G}$. With $V_T$ the number of fine sites,
\begin{equation}\label{eq:c3-7-11}
    \mathcal Z_0\geq e^{-\mathsf E}(c_Hg_0^{d_G})^{4V_T}e^{-48V_T}\;.
\end{equation}
On compatible even fine periods, for every plaquette $p$ and every auxiliary gauge variable $w$,
\begin{gather}
    \mu_0\bigl(|U(\partial p)-\id|_\sigma\geq\theta\bigr)\leq z_P:=\exp\Bigl[-\frac{b_G\theta^2}{4g_0^2}+4d_G\log g_0^{-1}+4\log c_H^{-1}+48\Bigr]\;,\label{eq:c3-7-12}\\
    q_g\bigl(|w-\id|_\sigma\geq\theta\bigr)\leq z_G:=e^{1/2}(c_Hg_0^{d_G})^{-1}e^{-b_G\theta^2/g_0^2}\;,\label{eq:c3-7-13}
\end{gather}
and therefore $p_z\leq q:=n_W\max(z_P,z_G)$ for every positive bond $z$.
\end{lemma}

\begin{proof}
On the event that every fine link lies in the operator ball of radius $g_0$ every plaquette contributes at most $8g_0^2$ to $S$, and there are at most $6V_T$ plaquettes and $4V_T$ links, which gives \eqref{eq:c3-7-11}. For \eqref{eq:c3-7-12} use the site-plane reflection positivity and the closed-unit-cube chessboard estimate of the archived note \draftref{USABLE\_NONFLAT\_ROUTES, sec:component-chessboard} (its reflection form, functional chessboard inequality and single-witness tails only, not its marked-integral notation), which apply on compatible even periods: the reflected dissemination of one plaquette has $V_T/4$ distinct plaquettes of its orientation, each with $s_G\geq b_G\theta^2$; dividing its energy bound by \eqref{eq:c3-7-11} and taking the $1/V_T$-th root gives $z_P$, a normalised probability estimate. For \eqref{eq:c3-7-13} restrict one gauge variable to its operator ball of radius $g_0$, where its action is at most $g_0^2/2$ and its cutoff factor is one, which bounds $z_g$ from below by $c_Hg_0^{d_G}e^{-1/2}$. The union bound over the at most $n_W$ witness labels of Lemma~\ref{lem:c3-7-2}, without any independence between witnesses, and \eqref{eq:c3-7-9} give $p_z\leq q$.
\end{proof}

\begin{proposition}[the exterior-response and uncovered term]\label{prop:c3-7-5}
Let $\pi_*=\min(p_0(g_0),p_0(g_1))$. There are $c_\theta$, $c_*$, $g_*>0$, fixed after $L$, the group, the character, $M_1$, $M_2$, $M$ and the source constants, such that $\theta\geq c_\theta g_0\pi_*$ and $q\leq e^{-c_*\pi_*^2}$ for $0<g_0<g_*$, and on compatible even fine periods, for $0<g_0<g_*$ and under \eqref{eq:c3-1-2},
\begin{equation}\label{eq:c3-7-14}
    |E_{\mathrm{bdry}}|\leq C_{\mathrm{resp},\chi}\,n_C(1+g_0r)\,e^{-c_*\pi_*^2}\;,
\end{equation}
after enlarging $C_{\mathrm{resp},\chi}$ by $C_L\max(S_c,1)$. The constants are uniform in the compatible even periods, the contour location and the first-step histories; the factor $n_C$ is retained.
\end{proposition}

\begin{proof}
CRE (2.6)--(2.9) and $\delta_0=(A_1/A_0)\varepsilon_0$ give $\theta\geq c_\theta g_0\pi_*$ for small coupling: each of the three terms of \eqref{eq:c3-7-4} is at least a fixed constant times $g_0p_0(g_0)$ or $g_1p_0(g_1)$, and $g_1/g_0$ is bounded above and below by CRE (2.6). Since $\ell=LMR_1$ grows as a fixed power of $\log g_1^{-2}$ (\eqref{eq:c5-3-1}), $\log n_W=O(\log\log g_0^{-2})$; with CRE's exponent $p_0\geq5\mathfrak r\geq10$, $\pi_*^2\geq A_0^2(\tfrac12\log g_0^{-2})^{2p_0}$ dominates $4d_G\log g_0^{-1}$ and $\log n_W$ for small $g_0$, so $q=n_W\max(z_P,z_G)\leq e^{-c_*\pi_*^2}$ with $c_*=b_Gc_\theta^2/8$, for $g_0<g_*$. Then Corollary~\ref{cor:c3-6-1}, Lemma~\ref{lem:c3-7-1} and Lemma~\ref{lem:c3-7-4} give $|E_{\mathrm{bdry}}|\leq C_{\mathrm{resp},\chi}g_0r\,C_LS_cn_Cq+C_Ln_Cq$.
\end{proof}

\begin{remark}[scope]\label{rem:c3-8-1}
Lemma~\ref{lem:exterior-response-bound} is proved from the Hessian, Schur, enlarged-chart and primitive derivative bounds of Appendix~\ref{app:background-estimates} and the collar cutoff of Section~\ref{sec:boundary-law-collar}, with both hard-cutoff surface terms inside the bounded covariance; its physical caller is restricted to $A_{\mathrm{cov}}$. Proposition~\ref{prop:c3-7-5} holds on compatible even-period tori, from the single-witness tails of Lemma~\ref{lem:c3-7-4} alone, without a component probability theorem, and uses the reconstruction and measure identities of Section~\ref{sec:sourced-effective-interaction}; the marked density \eqref{eq:c3-7-8} is displayed without equating any older two-parameter normaliser with $I_{\xi;1}$, and the filling proximity of Lemma~\ref{lem:c3-7-2} holds for a simultaneous or an iterated filling of small components. The $R_1$-label step of Lemma~\ref{lem:c3-7-2} rests on Proposition~\ref{prop:c3-9-1}, which uses local VAR data and Ba{\l}aban's stated gauge-conversion results at their verified local hypotheses; it does not use, and does not prove, that the minimum $U_1$ lies in the support of every characteristic factor of CRE (1.11), and other uses of that stronger reading of (B1) are not affected by it. This appendix controls the exterior-response and uncovered term only: it does not control the joint defects $R_\xi(\mathfrak B)$ of \eqref{eq:part1-joint-defect} and does not identify the regional scalar $S^\circ_{\xi,C}$. Section~\ref{sec:one-step-insertion} replaces Proposition~\ref{prop:c3-7-5}: its history weight is the labelled weight of the second collar test with the retreat of $\Lambda_1$, its boundary bound is Proposition~\ref{prop:c5-6-4} with the label accounting \eqref{eq:c5-6-3}--\eqref{eq:c5-6-4}, in which the one-point cost $q$ becomes $q+N_{\mathrm{ret}}q_\vartheta$, the constant $C_{\mathrm{resp},\chi}$ enters its $C_1$, a prefactor $r^{d_G}$ and a family-sum factor appear, and the leading coefficient is identified at the retreated carrier $D(\Lambda)$ (Section~\ref{sec:c5-7}); Sections~\ref{sec:c3-1}--\ref{sec:c3-6}, the tails of Section~\ref{sec:c3-7} and Proposition~\ref{prop:c3-9-1} are used there as stated, with the covered event $A_{\mathrm{cov}}$ replaced by the labelled event $A^{\mathrm{fin}}_{\mathrm{cov}}$ (Section~\ref{sec:c5-3-4}(a)).
\end{remark}

\subsection{The minimum comparison without the cutoff-support premise}\label{sec:c3-9}
This section proves the deterministic comparison \eqref{eq:c3-7-6} of the two minima from local data; it replaces a zero-fluctuation support argument and does not use the full cutoff-support reading of (B1). The sources are VAR \cite{BalabanVAR}, CRE \cite{BalabanCRE}, RG1 \cite{BalabanRG1} and the averaging paper AVG \cite{BalabanAVG}; Ba{\l}aban's stated existence, uniqueness, derivative-decay and gauge-conversion results are used at their verified local hypotheses.

\begin{proposition}[comparison of the global and local minima]\label{prop:c3-9-1}
There are constants $C_{L,G}$, $c_{L,G}>0$, depending on $L$, $G$, $M_1$, $M_2$ and the source parameters and fixed before $g_0$, independent of the fluctuation, its $R_1$ label, the exterior history and the compatible torus, such that for every eligible cube $Q\subseteq\Omega_1^{\sim-1}$, on its twice enlarged free-bond carrier,
\begin{equation}\label{eq:c3-9-1}
    \sup_{b\in(Q_w^{[2]})^*}|U_1(b)U_{1,Q}(b)^{-1}-\id|_\sigma\leq C_{L,G}\varepsilon_1e^{-c_{L,G}LM_2R_1}<\delta_0/10\;,
\end{equation}
the last inequality for $g_0$ small.
\end{proposition}

Compatible fine periods are multiples of $\ell$ and even, hence at least $2\ell$; since $\operatorname{side}(Q_w^{[4]})\leq9L^2M_2R_1\leq9\ell/8<2\ell$, this determining box and its fixed-range stencils have lifted copies before the next periodic image for small coupling. If $\Omega_1$ is the full torus there is no exterior collar to freeze and the same argument uses the periodic VAR problem. The quantity in \eqref{eq:c3-9-1} concerns a simultaneously gauge-covariant pair of links: their relative product transforms by conjugation at the initial endpoint, so its norm is gauge invariant; it is not an estimate on an open Wilson source. The proof occupies the rest of this section.

\subsubsection*{Source inputs and the local-domain verification}\label{sec:c3-9-1}
$U_1$ is the regular critical minimum of CRE (1.12), supplied by VAR Theorem 1 with the prescribed $V$, $V_0$ and the source axial mean gauge; the localisation below verifies the hypotheses for its existence and regularity near $\Omega_1$ and does not assume them for a distant large-field exterior. Its plaquette regularity on $Q_w^{[4]}$ is at most $C_{L,G}\varepsilon_1L^{-2}$. The local minimum $U_{1,Q}$ is CRE (1.2) with determining set $\mathfrak B_Q=\mathbf B_1(Q_w^{[4]})$ and reference data $D^0_Q=\dot M(Q_1^{s*}V)|_{\mathfrak B_Q}$; it has the corresponding VAR mixed-scale regularity, with the scale-zero boundary bound described below, and the same coarse averages $V$ on the interior determining region. These are the hypotheses of CRE's derivation (3.17)--(3.19), whose only field is the minimum, not the integrated fluctuation; at $k=0$ the fine spacing is $\eta=1$ and $V^{(0)}=U_1$, $V^{(0)}_Q=U_{1,Q}$, and no preceding effective interaction is needed.

The local-domain verification. Work before the $P_0$, $P_1$, $Q_1$ resummation, at any supported history contributing to the fixed $\Omega_1$, $V$, $V_0$, with fine field $\widehat U$. Take the enlarged fine domain $\Omega^+=\Omega_1^{\sim1}$ (the macro enlargement of CRE (1.10)) and fix $\widehat U=V_0$ on the collar $\Omega^+\setminus\Omega_1$. Outside $\Omega^+$ retain the original field but omit its action terms from the variational problem: once $\ell>2L+4$, every plaquette or block-gauge term containing an unfrozen variable lies in $\Omega^+$, so the omitted terms are constants, and the constrained first variation is exactly that of (1.12), with no change of boundary condition or integration law. CRE (1.10) and the following sentence separate $\Omega_1$ from the earlier bad regions by at least two macro layers, so every plaquette and averaging stencil in $\Omega^+$ lies in the $P_0$-good region, where at this unresummed stage $|\widehat U(\partial p)-\id|_\sigma<\varepsilon_0$. If the canonical outer operation has already omitted these factors, the exact removal statement immediately before CRE (1.11) says that they equal one on the support of the retained original-field factors, so restoring them changes no integral; since the history summands are nonnegative, a point of nonzero resummed density has at least one supported unresummed history. This restoration concerns $\widehat U$, not the minimum $U_1$, and controls the prescribed collar $V_0$; the distant exterior is never required to be regular. Conjugation and the bounded number of incident plaquettes give $|D^*_{\widehat U}\partial\widehat U|\leq C_{\mathrm d}\varepsilon_0$ on the collar and the variable region, and multiplying by the largest of the fixed scale weights $L^2$, $L^3$ puts $\widehat U$ in VAR's class (6) with radius $C_L\varepsilon_0$. Its fixed data are exactly $V_0$ on the fine collar and $V$ on the interior coarse labels, since the original averaging constraint is retained.

Use the positive-bond carriers $E(X)$. The fixed fine collar carrier is $E(\Omega^+)\setminus E(\Omega_1)$, so no crossing bond that is a variable of CRE (1.12) is fixed. The hierarchy for VAR has outer fine domain $\Omega^+$, inner block domain $\Omega_1$ and determining set this bond-set difference at scale zero together with $\Omega_1$ at scale one, with the mixed-bond convention of VAR (7); its spacing condition (1) holds because the separating macro layer has width $\ell$, exceeding the fixed $RM_1$ of VAR for small coupling. For a mixed determining plaquette, replace every missing fine-side bond by its block average as prescribed in VAR (7): the original constraint makes the resulting loop an ordinary fine plaquette of $\widehat U$ or a coarse plaquette of its block average, and AVG Proposition 1, (51), bounds the latter by $L^2\varepsilon_0+C(L^2\varepsilon_0)^2\leq2L^2\varepsilon_0$, which is also CRE's explicit bound before (1.2). So the entire determining set of the localised problem has VAR data regularity at most $C_L\varepsilon_0$, and no regularity of the rest of $\Omega_1^c$ is involved.

VAR Theorem 1 therefore constructs the regular critical orbit for these data, with both the plaquette and the divergence bounds (2), at radius $B_3C_L\varepsilon_0$. This is the regular minimum used by CRE (1.12), which cites that theorem; the localisation changes the action by constants only, for every admissible variation, so it does not select a different critical orbit. Restricted to $Q_w^{[4]}$ the same bound gives membership in the local uniqueness class, with fixed scale and norm conversions; since $\varepsilon_0/\varepsilon_1$ is bounded by CRE (2.8), the radius is $C_{L,G}\varepsilon_1$, below VAR's $a_0$ for small coupling. The fine boundary layer of $U_{1,Q}$ has VAR's scale-zero bound, not an $\varepsilon_1L^{-2}$ bound: the plaquettes of its straight-extension data are trivial or equal to coarse plaquette holonomies of $V$, bounded by $2L^2\varepsilon_0$, so its mixed-scale data are regular with the same parameter $C_{L,G}\varepsilon_1$. Nothing here assumes that $\zeta(\Omega_1^c)$ or any characteristic factor of (1.11) remains nonzero when the fine integration variable is replaced globally by $U_1$; no branch at $A=0$ is introduced.

\subsubsection*{The boundary data and their size}\label{sec:c3-9-2}
Let $D_Q=\dot M(U_1)|_{\mathfrak B_Q}$ and define on the determining set
\begin{equation}\label{eq:c3-9-2}
    B_Q(e)=\tfrac1i\log\bigl(D_Q(e)D^0_Q(e)^{-1}\bigr)\;.
\end{equation}
Both data are defined by the source averaging operation on this regular configuration; the determining interior carries scale-one coarse bonds and its boundary layer the finer determining variables, as defined after CRE (2.12). For the straight extension of CRE (1.3) every intrablock contour is the identity, every centre-to-centre path crossing a specified interface has transport $V(c)$, and every relative closed holonomy of RG1 (0.4) is the identity, so the logarithmic correction vanishes and $\mathsf M(Q_1^{s*}V)(c)=V(c)$; on the interior both data equal $V$, hence $B_Q=0$ there, and $\operatorname{supp}B_Q$ lies in the boundary layer of width $2LM_1$ of $Q_w^{[4]}$, the support statement preceding CRE (3.18). The principal logarithm is legitimate because the argument of CRE (3.17) bounds its operand by $C_{L,G}\varepsilon_1$ (CRE's printed coefficient $44d^2B_3$ belongs to its own regularity coefficient; the enlarged local coefficient is kept inside $C_{L,G}$). At one step this can also be read from the two-block comparison: in the axial mean gauge a regular minimum is within $C_{L,G}\varepsilon_1$ of the identity on internal bonds and of $V(c)$ on interface bonds, which are exactly the values of $Q_1^{s*}V$. Thus
\begin{equation}\label{eq:c3-9-3}
    \|B_Q\|_\infty\leq C_{L,G}\varepsilon_1\;.
\end{equation}
To meet VAR (172) with its absolute constant $C_1$, take its small parameter $\alpha=K\varepsilon_0$ with $K$ dominating all determining-data, uniqueness-class and $B_Q$ bounds; then $|e^{itB_Q}-\id|\leq|tB_Q|\leq\alpha$ and $C_1=1$ suffices. VAR Proposition 9 and (190) are applied with this $\alpha$, not with CRE's identically named $\varepsilon_1$; for small $g_0$, $\alpha\leq a_1$ and $B_3\alpha\leq a_0$, and CRE (2.8) converts the resulting $C\alpha$ bounds into $C'\varepsilon_1$. No bound is imposed on the exterior integration variables away from this local regular domain.

\subsubsection*{Integrating the local derivative estimate}\label{sec:c3-9-3}
Let $\mathscr H_Q(B)$ be the relative Landau-gauge logarithm of the local minimal-configuration map of VAR Proposition 9 on $\mathfrak B_Q$ with reference $U_{1,Q}$, normalised by $\mathscr H_Q(0)=0$; this is the map of CRE (3.17), with its $L^{-1}$ scale factor at $k=0$. CRE (3.17) identifies the map at $B_Q$ with the restriction of $U_1$ up to the source gauge restoration: both have determining data $D_Q$ and lie on the unique regular critical orbit. For the criticality, a local admissible variation fixes the determining fine layer and the averages on the interior coarse rows; extended by zero outside $Q_w^{[4]}$ it preserves every global average and exterior value in (1.12), because the fixed layer is wider than the plaquette and averaging range. The first variation of the global action vanishes and its local part is the local action variation; the gauge functional has zero first variation at an axial mean configuration, where each nonnegative summand attains zero. So the restriction of $U_1$ is critical for the local action, and the uniqueness class of Section~\ref{sec:c3-9-1} identifies its orbit with the local analytic solution. The identity is about that orbit; it needs no membership of the integrated field in a cutoff event.

VAR (190), Proposition 9, gives the functional derivative with the mixed-scale weights; at one step the scale labels are $0$ and $1$, so the powers of $L$ in those weights are fixed constants, and a determining bond $e$ of the outer layer and an interior bond $b$ satisfy the bound $C_{L,G}e^{-c_{L,G}d(b,e)}$, the unit-density measure at the finer level and the scale-one determining measure contributing fixed $L$-dependent factors. Integrating along $tB_Q$, $t\in[0,1]$, and summing the labels,
\begin{equation}\label{eq:c3-9-4}
    |\mathscr H_Q(B_Q;b)|_\sigma\leq C_{L,G}\varepsilon_1\sum_{e\in\operatorname{supp}B_Q}e^{-c_{L,G}d(b,e)}\leq C'_{L,G}\varepsilon_1e^{-c'_{L,G}d(b,\operatorname{supp}B_Q)}\;,
\end{equation}
where for the second inequality each exponential is split into two halves and the remaining periodic shell sum is bounded by its infinite-lattice sum, paying the whole boundary area without a volume-dependent constant. For $b\in Q_w^{[2]}$,
\begin{equation}\label{eq:c3-9-5}
    d(b,\operatorname{supp}B_Q)\geq2w-2LM_1-C_L\geq LM_2R_1
\end{equation}
once the collar threshold holds ($w\geq LM_2R_1$ and $R_1\to\infty$), after decreasing the decay constant if necessary; this covers either candidate common width $w$ and never uses a good/bad $R_1$ label.

\subsubsection*{Restoring the source gauge}\label{sec:c3-9-4}
The transformation of VAR Proposition 2 is not centre-fixing: its condition is $(\overline{R_0u})^j=\id$ on $\Lambda_j$, in particular $u=\id$ on the fine determining layer (VAR p.281), and at one step its interior condition $\overline{R_0u}(y)=\id$ does not imply $u(y)=\id$. Keep the restoring transformation $u_Q$ of CRE (3.17), defined by this source normalisation. At the first step, with $\eta=1$ and the convention (1.17), on the required bonds
\begin{equation}\label{eq:c3-9-6}
    U_1(b)=u_Q(b_-)^{-1}e^{iL^{-1}\mathscr H_Q(B_Q;b)}U_{1,Q}(b)\,u_Q(b_+)\;.
\end{equation}
The local inputs of the transferred source estimates are the uniqueness and regularity class of Section~\ref{sec:c3-9-1}, the small supported $B_Q$ of Section~\ref{sec:c3-9-2} and the response bound \eqref{eq:c3-9-4} on both endpoint blocks and the crossing bond. Fix an analytic mean neighbourhood radius $\rho_{\mathrm{av}}>0$ for the finite source contour families, with derivative bounds on its closed half-radius neighbourhood, and choose $g_0$ after it so that the reference path-family diameter and its perturbation are both less than $\rho_{\mathrm{av}}/4$; this is the regular-chart reduction. The equations determining $u_Q$ are AVG (77)--(87), with its expression in the relative fields given in (106)--(108): at one step the product in (106) has a single $j=0$ factor, a reference-unitary conjugation of the inverse block average followed by a local relative path transport, and the centre factor (87) is retained. Unitary conjugations preserve the norm, each path has length at most $C_{\mathrm d}L$, so the telescoping product identity bounds the relative deviation by $C_L$ times the largest relative-link deviation in the block, and the analytic averaging bound of (161)--(163) bounds the block-average deviation by the same quantity after reducing the chart. Hence
\begin{equation}\label{eq:c3-9-7}
    \sup_{x\in\mathcal B_y}|u_Q(x)-\id|_\sigma\leq C_{L,G}\sup_{b\in E(\mathcal B_y)}|\mathscr H_Q(B_Q;b)|_\sigma\;,
\end{equation}
the factor $L^{-1}$ of CRE (3.17) absorbed into the constant. The restoring map is relative to the reference pair: under a simultaneous gauge change $h$ of field and reference its representative is $u^h_Q(x)=h(x)u_Q(x)h(x)^{-1}$ (conjugate the relative action, VAR (16)--(17), and its reference-dependent gauge condition), so $|u_Q(x)-\id|_\sigma$ is a conjugation-invariant scalar of the relative construction, used only inside this gauge restoration; the centre contribution $u_Q(y)$ is retained. AVG uses its older averaging definition; the application here rests on Ba{\l}aban's extension statements, RG1 after (0.10) (the earlier results apply to averages with the listed properties) and RG1 after (0.12) (all results of the averaging paper hold for the modified average, with the indicated modifications), so \eqref{eq:c3-9-7} is used for the RG1 averaging and mean gauge as that source result, as CRE (3.17)--(3.19) does for the later scheme, and as RG1 itself does for its gauge conversions ((3.26)--(3.27) with AVG (77), and (3.39) with AVG (97), retaining the centre-block gauge factors; RG1's reference [12] is AVG). No change of the physical averaging operation is made.

For the bond $b$ of \eqref{eq:c3-9-1} apply \eqref{eq:c3-9-4} on both endpoint blocks, on $b$ itself and on the paths entering the gauge factors, which enlarges the input set by at most $2L+2$, already included in the $C_L$ of \eqref{eq:c3-9-5}. The relative exponential and both endpoint factors of \eqref{eq:c3-9-6} then give $|U_1(b)U_{1,Q}(b)^{-1}-\id|_\sigma\leq C_{L,G}\varepsilon_1e^{-c_{L,G}LM_2R_1}$; both endpoint gauge factors of CRE (3.18) are retained, and the quantity is the simultaneous-gauge-invariant norm of the relative pair of links, not a comparison modulo an unspecified gauge transformation.

\subsubsection*{The caller and the denominator}\label{sec:c3-9-5}
CRE (2.6), (2.8) bound $\varepsilon_1/\delta_0$ by fixed source constants and $R_1$ grows as a power of $\log g_1^{-2}$, so the bound is $<\delta_0/10$ for small $g_0$, which completes the proof of Proposition~\ref{prop:c3-9-1}. In Lemma~\ref{lem:c3-7-2} the same norm $|\cdot|_\sigma$ is used for the (1.18) test, the comparison and the no-witness bound, and the eigenvalue inequality $|e^{iX}-\id|_\sigma\geq(2/\pi)|X|_\sigma$ holds in both permitted norms without a norm conversion. The physical integral is never altered: for each original history the comparison is used inside its cutoff-support implication, the numerator of \eqref{eq:c3-7-1} remains $\int\mathcal O[\mathsf w_\xi\mathbf 1\{z\in E(B_\xi)\}]\,\dd V$ with $\mathsf w_\xi=e^{c_\xi}I_{\xi;1}$ and its denominator $\mathcal Z_0$; no $\zeta$ factor is removed, evaluated at $U_1$ or divided out, and the covariance estimate of Section~\ref{sec:c3-5} is unchanged.
```

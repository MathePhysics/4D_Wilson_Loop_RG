# Attempts at the Large-Field Ingredient (γ)

> **Deprecated (5 November 2026).** This file is no longer live. It belongs to the γ stream of 28–30 October, whose route the large-field note `WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` replaces. No live note uses it, and its open lists are not the current gaps. The current status of (LF) is that note's Open Gaps (#S0) and the review plan `WILSON_IT1_LF_PACKET_PLAN_2026_11_04.md`.

**Contents of §§40–72.** The marked mixed-integral estimate, LF ingredient γ, and the Cauchy estimate remain open. §40 settles the old-factor margin question of §39.8 and derives the amplitude in (G.237) for the action channels. §41 derives the vacuum cancellation at the creation integral, with the root bound in relative-decay form and the ratio bound (G.244c). §42 gives the tube norms of the marks up to the run data differences, and §43 a volume-free form of (G.207) with the truncated two-mark bound. §44 bounds the renormalised near-domain terms at the entries: under R-data and the clause of 62.3 each term and its counterterm read the composite, the counterterm defect is zero, and 64.5 bounds the term. §45 treats r^s_z and the far-domain part of r_z under R-near. §46 derives the width of the middle layers of 𝐁″_k, and §47 assigns the counterterm among the domains Y. §49 derives the conditions of the old terms' spaces at U_{k,Λ} and U_1 on Λ^c at real points. §50 takes U_{1,2} as a member of the chain; the fine side and the lift condition at the cut stay open. §51 gives Lemmas A and B from VAR's Theorem 1 at Bałaban's joins. §52 reads the localisation of LFR II pp.372–375. §53 quotes the identities of (1.61)–(1.63) at each run's own members, and §54 lists what is open at interior points of the line. §55 checks the readings against the sources, §§56–61 treat the cut, the current, U_2, and the junctions, §§62–64 and §66 the near domains, §§65 and 67–68 the representation configurations at D(s) and complex points, §69 the lift condition at the composites, §70 the variation group, §71 the top N₀ layers of an R-operation, and §72 the nonlinearity of the lift. The open lists are in the status subsection of each section. See the local new-account handover (`HANDOVER_LF_GAMMA_NEW_ACCOUNT_2026_10_29.md`, not bundled). No author subagents or VS Code were used.

28 October 2026. Separate working note requested by the user. The Cauchy, large-field-depth, and walk-factor notes are not edited. Focused reviews are recorded at their stated scopes; later repairs and other calculations remain unreviewed unless expressly indicated. The note gives partial repairs and their precise remaining dependencies; it does not establish (LF) or the Cauchy estimate.

The current dependency list is §35, with the subsequent reread recorded at the start of §36. It supersedes earlier dependency checkpoints in this note. V4 supplies the machinery mapped in §25; §§26 and 29 derive the bounded-insertion and spatial estimates within its stated scope. The mixed-integral application remains open. The existing retained-field identification, relative-tree count and history reserve are to be reused. The later LF revision leaves parts of the complex lift and the bound along the joint line open; the earlier descriptions of those inputs in §35 must be read with the corrections in §36. The two-loop draft fixes the preliminary insertion's evaluation point and its physical normaliser. Sections 32–34 and 38 remain unproved attempts. Section 37 records the gauge-transport identities and their application limits; its nonlinear covariance is reused from D2.2(6). The latest analytic attempt is the interacting contour estimate in §39: its per-term mechanism passed the focused review at the stated inputs, but its full source application and cluster conclusion did not. Section 39.5 gives the precise scope. Supporting deterministic attempts in §§13–15 remain inactive.

The starting files are:

- [Cauchy estimate](WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md), SHA-256 `8f7a3e6cc5c78419326fd1a650b1c18c485e8d61cdf94f353b664ec5c9ef5c34`.
- [Large-field depth](WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md), SHA-256 `e64619bd303aeafe49364cc23f94d8ffb678da618354708f2afccd2834a16a85`, called the LF note.
- [Walk-factor difference](WILSON_IT1_WALK_FACTOR_DIFFERENCE_2026_10_28.md), SHA-256 `d07788fb9a6d584036ea55b766c9dcd630573cb322c9ca3811967503dadb59c2`, called the walk note.

The LF note was saved externally during this work. An earlier observed SHA-256 was `e692c2f0798734b4a85e42ab6f74463434c2db717501a80f0aa091e51f5d06e8`. The detailed comparisons below retain their historical scopes; §35 records the later draft updates and current dependencies. The externally saved changes were not overwritten.

Paper labels have the meanings in the [bibliographical dictionary](BALABAN_PAPER_LABELS.md). References below are to the local corrected transcriptions and the printed equation numbers. A corrected transcription is source material, not an independent verification of an extension made here.

## 1. The Estimate to Be Supplied

For a young history with birth scales n(X), ingredient (γ) must control the change of the integrands under refinement of the fine lattice. The Cauchy note asks for a relative majorant of the form

$$
\exp\left(\sum_X\sum_m C_M s^{\mathrm{LF}}_{n(X)}L^d|Z_m\cap X|_m\right)-1,
\qquad s^{\mathrm{LF}}_n\leq C_h\widetilde\theta^n\;.
$$

For (LF-1) this multiplies the actual history majorant M_τ. For (LF-2) it must apply on the complex inductive class to the renormalisation numerator and its physical denominator. An estimate of an unnormalised numerator alone does not suffice. The first callers are Cauchy §6.2 and §8.6.

The open parts of the LF note are (3), variation of the old terms at complex configurations; (6), the interface terms; (7), the individual localised terms, including (Wδ-1)–(Wδ-3); and (10), the boundary terms. They share several dependencies. In particular, the complex lift and the local operator comparison cannot be assumed in order to prove themselves.

## 2. Paying for the Shrinking Boundary-Term Margin

This calculation addresses the specific loss in LF-A(10), §4(e), *Complex Backgrounds*. It uses the boundary terms themselves, rather than replacing their measure by a reference measure.

Let B_i(X,·) denote a generation-i boundary term from CRE (2.41). On its stated analyticity domain,

$$
|B_i(X,\cdot)|\leq B_0 e^{-\kappa d_i(X)}\;.
\tag{G.1}
$$

At a point of layer m≤i the coefficient in the domain conditions CRE (2.34)–(2.39) is

$$
c_{i,m}=1-\beta+\beta 2^{-(i-m)}\;.
$$

For an argument satisfying the corresponding conditions at step k+1, k≥i, the difference of these coefficients is

$$
c_{i,m}-c_{k+1,m}
=\beta\left(2^{-(i-m)}-2^{-(k+1-m)}\right)
\geq \frac{\beta}{2}2^{-(i-m)}\;.
\tag{G.2}
$$

This is the relevant margin in the conditioned quantities, not automatically a ball in an arbitrary norm of the fine field. Those quantities include the current and the locally reconstructed configurations and currents.

Consider two arguments p_A and p_B of the same scalar boundary term, in one run's fine-field space. Put m_* equal to the finest layer met by X and r=i−m_*. Let τ_X be a bound on the changes of **all** the quantities in (2.34)–(2.39), divided by their respective α-thresholds and scale factors. Assume there is an analytic interpolation p(z), with p(0)=p_A and p(1)=p_B, for which those changes are bounded by C_*|z|τ_X and the local gauge condition (2.38) is maintained. The constant C_* must be uniform in the history and the number of steps. This interpolation is an explicit remaining input; a bound on the phase and its first derivative alone does not establish it.

Choose a fixed c>0 small enough in terms of β/C_*. When 2^rτ_X≤c, (G.2) allows a disc of radius at least 2 and, more precisely, a radius proportional to 2^{-r}/τ_X. Cauchy's estimate and (G.1) give

$$
|B_i(X,p_B)-B_i(X,p_A)|
\leq C\tau_X 2^r B_0e^{-\kappa d_i(X)}\;.
\tag{G.3}
$$

When 2^rτ_X>c, the endpoint bound (G.1) gives (G.3) with C enlarged to at least 2/c. No interpolation is used in this second case; both endpoints must still lie in the term's domain.

CRE p.264, immediately before (2.47), uses the support condition X∩Ω_i≠∅ to obtain

$$
e^{-d_i(X)}\leq 2^{-(i-1-m_*)}=2^{1-r}
$$

when i>m_*. For i=m_* the next bound holds without this inequality. Thus (G.3) implies

$$
|B_i(X,p_B)-B_i(X,p_A)|
\leq C'\tau_X B_0e^{-(\kappa-1)d_i(X)}\;.
\tag{G.4}
$$

The factor lost in the analyticity radius has been paid by one unit of the boundary support decay. This is precisely the unit CRE otherwise spends on summation over the generations in (2.47). It cannot be spent on that summation a second time.

Consequently, for the same layerwise absolute sums for which CRE (2.42)–(2.48) gives the domain count, and with τ_X≤τ on the terms under consideration, (G.4) leaves at worst the number of contributing generations:

$$
\sum_{i\leq K}\sum_X
|B_i(X,p_B)-B_i(X,p_A)|
\leq C_B K\tau\,\mathcal V\;.
\tag{G.5}
$$

Here the inner sums and the volume \(\mathcal V\) must be those of that layerwise count; (G.5) is not a bound on an unrestricted sum over every polymer in the torus. For the young histories the LF note has K≤8n+j(C). If the interpolation estimate supplies τ≤C n^pθ₀^n with θ₀<\(\widetilde\theta\), then

$$
K\tau\leq C'(1+j(C))\widetilde\theta^n,
\qquad
C' <\infty,
\tag{G.6}
$$

because the supremum of \((8n+j(C))n^p(\theta_0/\widetilde\theta)^n\) is finite. The slack in the exponents displayed in LF §4(d), *The Ratio*, is relevant here. An estimate with θ₀=\(\widetilde\theta\) alone would not justify absorbing K into a constant.

**What this repairs.** The exponentially shrinking margin is not, by itself, a reason that the comparison fails. There is a direct payment for it using the boundary-term decay. This supplies a candidate estimate for the boundary contribution to the history-volume bound.

**What remains.** Establish the interpolation bound for the complete configuration/current data, with endpoints on one common lattice. This is part of LF-A(3). Also check the exact layerwise sum at each occurrence in §8.6. Equation (G.4) has decay κ−1, so it must not be inserted as a bound in a κ-weighted activity norm without paying that loss. The aggregate LF bound and an unchanged κ-norm are different conclusions.

Sources: [CRE p.261](../Balaban/tex/CRE/parts/p261_corrected.tex), [p.264](../Balaban/tex/CRE/parts/p264_corrected.tex), [p.277](../Balaban/tex/CRE/parts/p277_corrected.tex).

## 3. A Dirichlet Right Inverse for the Local Averaging Map

This addresses condition (S) in the walk note. It is an auxiliary construction inside the local operator comparison. It does not replace the gauge-invariant polymer activity by a norm of an open Wilson segment.

Let \(\mathfrak F_A\) and \(\mathfrak F_B\) be the one-form spaces with Dirichlet exterior on the two local domains Ω_A=Ω₀^A(□) and Ω_B=Ω₀^B(□). Let χ_A and χ_B denote their restrictions, with zero extension when composing maps. The averaging map actually used in the local Galerkin identities is

$$
Q_D=\chi_AQ_1\chi_B\colon\mathfrak F_B\longrightarrow\mathfrak F_A\;.
\tag{G.7}
$$

Those identities need Q_D L_D=I. They do not need the zero extension of L_D to invert Q₁ on coarse bonds outside Ω_A.

Write Q₁=Q₀+E, where Q₀ is the straight-path term of CMP 98 (124)–(125). A local right inverse J₀ of Q₀ can be constructed on the coarse bonds in Ω_A as follows. For each positively oriented coarse bond c, put a field on the fine bonds crossing the common face of its two blocks, and zero on all other fine bonds. Each path [x,x′] in (125), x∈B(c₋), crosses that face once. Assign the value Lf(c) on the crossing bond, transported back from the frame at c₋ along a fixed reference path. Call this map J_face. Different coarse faces are disjoint. At the flat background each summand returns Lf(c), so

$$
=(Q_0J_{\rm face}f)(c)
=L^d L^{-(d+1)}L f(c)=f(c)\;.
\tag{G.8}
$$

At a curved background the different paths need not give identical transports. Retain their average: Q₀J_face is a block-diagonal map S, with one Lie-algebra endomorphism S_c for each coarse bond c. It is block-diagonal because the straight paths belonging to c cross only the face belonging to c. Relative to the fixed reference transport, every entry is an average of holonomies of loops inside the two blocks. The plaquette bound and a spanning surface of at most C(d,L) plaquettes give \(\|S_c-I\|\leq C(d,L)\alpha_0\), using the short-loop bounds underlying CMP 98 (124). For this quantity below 1/2, put J₀=J_face S^{-1}. Then Q₀J₀=I exactly. This finite block correction is necessary; flat-background transport cancellation alone would not prove the curved statement. Negative orientations use transported antisymmetry. All maps transform covariantly under simultaneous changes of fine and coarse frames.

In the real-background sup norm, \(\|J_0\|\leq 2L\). On the complex local class the same argument needs the corresponding short-loop and transport bounds; the constant is multiplied by the uniform bound for those transports. The path lengths are bounded in units of the fixed block size L, so these are local bounds rather than constants growing with K or the physical volume. Their applicability on the chosen complex pair class must be retained as an input.

PBG p.408 gives Ω₁^B=Ω₀^A, and an extra collar of width \(2R_0M_0\varepsilon/L\) between Ω₁^B and Ω₀^B. The faces supporting J₀ and the paths defining their averages fit in Ω_B when that collar contains the one-block stencil. Taking, for example, a collar wider than two coarse blocks is a sufficient geometric condition. Its compatibility with the fixed local partitions must be checked before using it for every □.

Set

$$
T=\chi_A E J_0\colon\mathfrak F_A\longrightarrow\mathfrak F_A\;.
$$

CMP 98 p.36 bounds E by C(d,L)α₀ in the one-step regular class. Suppose its composition with J₀ has norm q<1. This is a small-field condition with a fixed constant depending on d and L. Define

$$
L_D=J_0(I+T)^{-1}
=J_0\sum_{r=0}^{\infty}(-T)^r\;.
\tag{G.9}
$$

Every intermediate T acts on \(\mathfrak F_A\), including the projection χ_A. Therefore every term in (G.9) is supported in the same fine-domain image of J₀, inside Ω_B. Also

$$
Q_DL_D=(I+T)(I+T)^{-1}=I,
\qquad
\|L_D\|\leq\frac{\|J_0\|}{1-q}\;.
\tag{G.10}
$$

Analyticity follows from uniform convergence on a class where q is bounded away from 1. The construction does not require an inverse with a fixed finite interaction range. Its kernel may connect distant coarse bonds inside Ω_A, but its output never leaves Ω_B. If T has stencil range R_T, its kernel moreover satisfies a bound proportional to \(q^{\lceil\operatorname{dist}(c,c')/R_T\rceil}/(1-q)\).

**What this repairs.** The support obstruction in (S) can be removed by using a right inverse of the restricted averaging map. A global Neumann inverse, whose output leaks outside Ω_B, is unnecessary for the algebraic identities in walk §4(a)–(b).

**What remains.** The face-supported J₀ is not a regular prolongation: even constant coarse data produces variation at the fine spacing. Thus (G.9) proves support and a sup bound, but not the shellwise C^{1,β} bounds required when L_DG_Af is inserted into (Wδ-1). Nor is L_D the specified derivative dι_X needed by (Wδ-2). These distinctions prevent declaring (Wδ-1) or (Wδ-2) closed.

One possible continuation is to start with a regular local interpolation I_D and use

$$
\widehat L_D
=I_D+L_D(I-Q_DI_D)\;.
\tag{G.11}
$$

It is again a right inverse. The regularity question is now concentrated in the interpolation residual. On a shell of spacing scale a, the needed estimate is of the form

$$
\|(I-Q_DI_D)f\|_\infty
\leq C\varepsilon^{1+\beta}[\nabla f]_{\beta}
 + C\varepsilon^2\|F\|_\infty\|f\|_\infty\;,
\tag{G.12}
$$

with the corresponding boundary-shell norms. The first term follows from affine reproduction only after an actual I_D with that property has been constructed; it is not supplied by (G.9). The second requires the transported version of that construction. This is a concrete next estimate, still unproved here.

Sources: [CMP 98 p.36, (124)–(126)](../Balaban/tex/CMP98/parts/p036_corrected.tex), [PBG p.408](../Balaban/tex/PBG/parts/p408_corrected.tex), walk §4.

## 4. The Nonlinear Fixed Points: An Actual Difference Calculation

The propagator comparison does not on its own prove (Wδ-3). RG II (1.2)–(1.4) gives

$$
\mathbf H=H_0B'+A_0-HD(H_0B'+A_0),
\quad D=C(A'-HD),
\quad A_0=-\widetilde G\,DV(H_0B'+A_0)\;.
\tag{G.13}
$$

The local functions C and DV depend on the run. They must remain in the difference.

Here is the precise contraction estimate needed after both runs have been represented on the common fine-side comparison space. Write D_X=C_X(a_X-H_XD_X), X=A,B, and assume both fixed points lie in the contraction ball. Let \(r_D\) bound their norms, \(L_C\) bound the derivative of C_B on this ball, and \(q_D=L_C\|H_B\|<1\). Define

$$
e_C=\sup_{v\text{ in the comparison ball}}\|C_B(v)-C_A(v)\|\;.
$$

Subtracting the two equations, adding and subtracting C_B(a_A−H_AD_A), and retaining the term containing D_B−D_A gives

$$
\|D_B-D_A\|
\leq
\frac{L_C\bigl(\|a_B-a_A\|+\|H_B-H_A\|r_D\bigr)+e_C}
{1-q_D}\;.
\tag{G.14}
$$

For A₀ write F_X=DV_X, let L_F be a Lipschitz constant of F_B on the relevant ball, and suppose \(q_A=\|\widetilde G_B\|L_F<1\). Put

$$
e_F=\sup_v\|F_B(v)-F_A(v)\|,
\qquad
b_F=\sup_v\|F_A(v)\|\;.
$$

The same subtraction yields

$$
\|A_{0,B}-A_{0,A}\|
\leq
\frac{\|\widetilde G_B\|L_F\|H_{0,B}B'_B-H_{0,A}B'_A\|
 +\|\widetilde G_B\|e_F
 +\|\widetilde G_B-\widetilde G_A\|b_F}
{1-q_A}\;.
\tag{G.15}
$$

Finally, put \(a_X=H_{0,X}B'_X+A_{0,X}\). Then

$$
\|\mathbf H_B-\mathbf H_A\|
\leq\|a_B-a_A\|
 +\|H_B\|\|D_B(a_B)-D_A(a_A)\|
 +\|H_B-H_A\|r_D\;.
\tag{G.16}
$$

These inequalities preserve a small depth factor if every numerator has that factor and the contraction gaps are uniform. They also identify the terms that an appeal to analyticity in the propagators omits: e_C, e_F, and the difference of B′ itself, including its nonlinear correction.

There is an additional representation issue. The nonlinear lift ι does not generally identify a coarse phase A with the fine phase dι·A beyond first order. If the comparison uses the linear map \(L_\iota=d\iota\), its quadratic remainder belongs in e_C or e_F. It cannot be removed by the equality \(Q_1L_\iota=I\). An O(|A|²) remainder without a depth factor is insufficient for (LF).

**Status.** Equations (G.14)–(G.16) give the explicit transfer through the contractions. They do not establish the estimates of e_C and e_F between different fine lattices, nor the required common representation on the whole complex s-polydisc. Wδ-3 remains open at those quantities. This calculation rules out treating it as an automatic consequence of the propagator bound.

Sources: [RG II p.2](../Balaban/tex/RG2/parts/p002_corrected.tex), [p.3](../Balaban/tex/RG2/parts/p003_corrected.tex), [p.5](../Balaban/tex/RG2/parts/p005_corrected.tex), [p.6](../Balaban/tex/RG2/parts/p006_corrected.tex).

## 5. The Exceptional Deep Terms: Recover the Earlier Localisation

The LF note, §4(e), isolates terms with Y′₂=Y′₃=Y′₄=∅ in LFR II (1.61)–(1.66). It describes them as originating from an old domain X disjoint from Z, with no forced connection to Λ. There is an earlier expansion that must be retained when making this argument.

LFR II p.369 first divides the action into terms whose domains meet Z and terms whose domains are disjoint from Z. For an old term in the second part, p.372 applies (1.59) or (1.60) to the **difference** between its values at U″_k and U⁰_k. The fluctuation source B is supported in Λ. Bałaban's localisation then has the following exact property: a nonzero new term has a connected domain Y₀ containing the original near domain and at least one component of Λ^∼. The terms without that connection vanish. The same statement is made there for the boundary terms treated by (1.60).

The reason is visible in RG II (1.9)–(1.10). At zero decoupling parameters outside a component, the propagators and the nonlinear fixed-point equations separate into components. In a component missing the source, the fluctuation field is zero, so the subtracted scalar function

$$
T\bigl(X,e^{i\eta\mathbf H(B)}U\bigr)-T(X,U)
\tag{G.17}
$$

vanishes. Differentiating parameters in other components cannot change this. The source and the original term must therefore lie in one connected localisation domain.

At p.373 Bałaban includes these **new terms with domains Y₀** among the terms to which (1.61)–(1.64) is applied. He then calls a current domain X and requires it to intersect Z. The current X is not, in general, the original old domain. Empty Y′₂,Y′₃,Y′₄ remove the three later enlargements; they do not remove the earlier source connection.

This gives the following candidate repair of the exceptional-term argument.

1. Retain the original source mark and the first localisation domain until the deep/shallow estimate has been made. Keep the four changes of background (1.51), (1.54), (1.57), and (1.58) separate at this stage.
2. For the bracket from (1.51), every surviving constituent has a connection from the old term to Λ. For (1.57) and (1.58), the sources are supported respectively on Z″_k and Λ. For (1.54), retain the **projected** source (1.55), including its boundary-layer term, rather than the unrestricted current J_{1,2}.
3. A constituent meeting an actual old layer and a young component must pay for the intervening layers along that connection. Use the scaled distance of PRT2 (2.46), not distance measured solely in the final coarse scale.
4. Only after that payment, perform the final resummation into V(Y). Terms of the first part whose original domains meet Z already have a connection through that domain; the completion terms of p.377 also have domains meeting Z.

For a retained connection with N intervening layers of scaled width at least RM, an available kernel factor e^{-δd} gives

$$
e^{-\delta d}
\leq e^{-\delta RMN/2}e^{-\delta d/2}\;.
\tag{G.18}
$$

The second factor must control the original sums over the walks, attachment points and domains. It cannot simply be discarded. If N≥k_s/8−c and those sums remain bounded at the halved rate, the first factor gives a geometric contribution in k_s, of the type needed for ν_j in Cauchy §8.6.

**What is established by the source check.** The first localisation for (G.17) has a source connection even when all three later domains are empty. An exceptional constituent cannot be analysed using only the original old X and the later Y′_i. This corrects the support bookkeeping for that family.

**What remains before a quantitative closure.** The domain assigned after resummation can contain an old layer merely because it is an enlargement. Such an enlargement does not prove that the actual source connection crosses that layer. The classification must be made on the constituent's actual dependence or its retained walk, and then reconciled with the existing norms defined on Y. Also check the full support and decay of the projected source (1.55), and the coefficient sums for all four background changes at the retained rate. Thus (G.18) is a proposed payment when the crossing is present, not yet a proof for every exceptional deep V(Y).

Sources: [LFR II p.369](../Balaban/tex/LFR2/parts/p369_corrected.tex), [p.370](../Balaban/tex/LFR2/parts/p370_corrected.tex), [p.371](../Balaban/tex/LFR2/parts/p371_corrected.tex), [p.372](../Balaban/tex/LFR2/parts/p372_corrected.tex), [p.373](../Balaban/tex/LFR2/parts/p373_corrected.tex), [p.376](../Balaban/tex/LFR2/parts/p376_corrected.tex); [RG II p.4](../Balaban/tex/RG2/parts/p004_corrected.tex); [PRT2 p.231](../Balaban/tex/PRT2/parts/p231_corrected.tex).

## 6. Marking the Actual Polymer Expansion

The new boundary terms are defined by LFR I (1.60)–(1.63), not by an independent Gaussian model. The fluctuation integrals include both A_j and B_j, the cutoffs, the quadratic cross-dependence through the conditional law, the old E-, R- and B-terms, and the previously created boundary terms. The latter occur in the subtraction

$$
\mathbb B_k^{(n)}(U_{\rm fluct})-
\mathbb B_k^{(n)}(U_{\rm base})\;.
\tag{G.19}
$$

LFR I (1.62) takes the logarithm of this integral and adds the coupling counterterm. The resulting scalar terms are gauge invariant. A difference must mark the entire subtracted scalar expression (G.19), or the full scalar measure factor that changes. Gauge-dependent factors are not assigned independent polymer activities.

For clarity, the following estimate is proved at the level of the convergent expansion, with its input condition stated explicitly. Expand the products and exponentials in LFR II (1.91), or the corresponding CRE/RG II fluctuation expansion, before taking the difference. Let Γ denote one resulting combinatorial term, including its localisation and integration labels. Let A_Γ≥0 be its absolute majorant obtained with the original conditional integrals and normalisations. Suppose a telescoping of the two runs' term has been justified under these same integral majorants and gives

$$
|F_B(\Gamma)-F_A(\Gamma)|
\leq \delta N_\Gamma A_\Gamma\;,
\tag{G.20}
$$

where N_Γ is the number of marked positions. The integration measures, their normalisations, and the cutoff shells count as positions when they change. An operator occurrence \(\mathbf T'_k(X)\) requires its marked integral estimate; (G.20) is not justified by dividing by a possibly vanishing value of that operator's output.

If the same majorant expansion with every marked position given weight 2 converges, then

$$
\sum_{\Gamma\to X}|F_B(\Gamma)-F_A(\Gamma)|
\leq\delta\sum_{\Gamma\to X}N_\Gamma A_\Gamma
\leq\delta\sum_{\Gamma\to X}2^{N_\Gamma}A_\Gamma\;.
\tag{G.21}
$$

The combinatorial cost is therefore paid by a fixed enlargement of the activity majorants, independently of the number of factors in Γ. This argument applies to the connected cluster series for the logarithm as well: keep its signed coefficients, dominate them absolutely, and mark one of its activity positions. There is no differentiation of a global lower bound for the partition function and no replacement of the physical denominator.

For the R-expansion, LFR II (1.92)–(1.97) exhibits the needed room. Doubling a V-majorant replaces α by 2α. Doubling a component majorant adds log 2 to its cost. The requirements on α, and the negative exponent involving p₀(g_k), are still satisfied for sufficiently small g_k, with the other constants fixed. The connected-series estimate must retain the decay reserved for exponentiation after these replacements. This is a fixed change of constants in the printed expansion, not a factor 2 for every RG step.

The same argument can be expressed through an analytic parameter. For already constructed scalar activities K_A, K_B satisfying \(|K_B-K_A|\leq\delta\widehat K\), set

$$
K_z=K_A+z(K_B-K_A)/\delta\;.
$$

For |z|≤1, the activity is dominated by 2\(\widehat K\). The local connected logarithm is analytic there if the doubled expansion converges. Cauchy's estimate between z=0 and z=δ then supplies a constant times δ in each local connected coefficient. This interpolation is in the scalar activities; it makes no unsupported claim that independently interpolated minimisers form an admissible chain.

### The Preliminary-Integration Recursion

Let c_r be a fixed local majorant norm of the difference of the boundary contribution created at the r-th preliminary integration, with all norms transferred to a common admissible domain. Let s_r bound the new marked sources at that integration: the covariance, cutoff shells, coupling term, background variation, and old terms other than the previously created contributions. If the subtraction (G.19) and the marked expansion give

$$
c_r\leq s_r+\eta_r\sum_{q<r}c_q\;,
\tag{G.22}
$$

then, with B_r=\(\sum_{q\leq r}c_q\), induction gives

$$
B_N\leq\sum_{r=1}^{N}s_r\prod_{q=r+1}^{N}(1+\eta_q)
\leq \exp\left(\sum_{q=1}^{N}\eta_q\right)\sum_{r=1}^{N}s_r\;.
\tag{G.23}
$$

This keeps the sum over earlier contributions, rather than replacing it by an unspecified uniform constant. For the overlapping N₀ terms discussed on LFR I pp.191–192, Bałaban has

$$
\delta'_j\leq (1+\beta_0)^2N_0^{\beta_0}\delta'_k,
\qquad N_0\delta'_j<4N_0^2\delta'_k\;.
$$

Thus, if the marked coefficient really has \(\eta_r\leq C\delta'_{j(r)}\) in the chosen norm, the overlapping part of the exponent in (G.23) is at most \(4CN_0^2\delta'_k\). This is controlled by the same small-coupling mechanism used in the printed proof. Nonoverlapping terms must be counted by their spatial supports; the statement “at most N₀” must not be applied to every integration in the history.

If Cauchy's estimate instead gives \(\eta_r=C\delta'_{j(r)}/m_r\), with an analyticity margin m_r, that denominator stays in (G.23). It is not legitimate to quote the printed N₀²δ′_k payment without checking it. Section 2 gives a possible spatial payment for one such loss, but the resulting norm and decay have to be used consistently.

**What this supplies.** The marked-product and connected-cluster calculation, and the precise recursion through the preliminary integrations, are written out. They show how a small marked input propagates through the actual polymer expansion without a factor exponential in the number of integrations.

**What remains.** Establish (G.20) and (G.22), with uniform constants, for the actual varying local kernels and the full complex classes. These are exactly where the interface comparison, (Wδ-1)–(Wδ-3), and the configuration/current interpolation enter. Treating their norms as small without proof would simply assume ingredient (γ).

Sources: [LFR I pp.188](../Balaban/tex/LFR1/parts/p188_corrected.tex), [189](../Balaban/tex/LFR1/parts/p189_corrected.tex), [191](../Balaban/tex/LFR1/parts/p191_corrected.tex), [192](../Balaban/tex/LFR1/parts/p192_corrected.tex); [RG II pp.12](../Balaban/tex/RG2/parts/p012_corrected.tex), [13](../Balaban/tex/RG2/parts/p013_corrected.tex); [LFR II pp.388](../Balaban/tex/LFR2/parts/p388_corrected.tex), [389](../Balaban/tex/LFR2/parts/p389_corrected.tex).

## 7. Interface Terms: Keep the Complete Second Variation

There is a useful exact organisation of the twist term, although it does not yet give the required decay. Let b be the common fluctuation datum, t a scalar, and in either run write the analytic constrained minimiser as

$$
U_X(t)=\exp\bigl(i\eta_X(t\mathcal A_{1,X}+t^2\mathcal A_{2,X}+O(t^3))\bigr)U_{0,X}\;.
$$

Write the twisted data as

$$
\widetilde b_X(t)=t\widetilde b_{1,X}+t^2\widetilde b_{2,X}+O(t^3)\;.
$$

The second-order constraint gives

$$
Q_X\mathcal A_{2,X}+C_X^{(2)}[\mathcal A_{1,X},\mathcal A_{1,X}]
=\widetilde b_{2,X}\;.
\tag{G.24}
$$

With J_X(1)=Q_X^*ν_X and a plaquette weight w, differentiating the scalar action gives

$$
\left.\frac{d^2}{dt^2}A_X(w,U_X(t))\right|_{t=0}
=\langle\mathcal A_{1,X},\Delta_X^{\mathrm{act}}(w)\mathcal A_{1,X}\rangle
-2\langle C_X^{(2)}[\mathcal A_{1,X},\mathcal A_{1,X}],ν_X\rangle
+2\langle\widetilde b_{2,X},ν_X\rangle
-2\langle\mathcal A_{2,X},J_X(1-w)\rangle\;.
\tag{G.25}
$$

The complete right-hand side is gauge independent, as is the action on the left. Its separate terms depend on the chosen representation. This identity agrees with LF §4(d) and makes clear why the twist term cannot be omitted merely because the untwisted first-order constraint has been solved.

A possible way to avoid calculating the Baker–Campbell–Hausdorff terms individually is to compare the **whole analytic scalar function**

$$
F(t)=A_B(w,U_B(t))-A_A(w,U_A(t))\;.
$$

If a bound |F(t)|≤E_n holds for |t|<R in the common data direction, independently of the desired Hessian comparison, then Cauchy's formula gives

$$
|F''(0)|\leq 2E_n/R^2\;.
\tag{G.26}
$$

Thus a geometric action-difference estimate on a fixed complex data disc yields a geometric bound for the **combined** expression (G.25). It automatically includes the twist and complementary-weight terms. The data variable must be scaled so that R is a physical analytic radius; a radius shrinking with ε would destroy this conclusion.

This is useful for the denominator, where the original weighted action is the integrand of LFR II (1.1). The LF note already compares that denominator as a whole. It does not on its own settle the numerator's isolated form \(\langle DH''B,\zeta DH''B\rangle\), the localised pieces of \(\mathbf C_k\), or the local propagators. Their representations separate terms again. A whole-action bound cannot be substituted for their per-piece bounds without a localisation argument on the same disc.

For the π-part, the single-scale cancellation uses \(\overline D^*ν_\pi=0\). At a multiscale interface the available bound in the LF note is of order ε₁, with no factor \((\varepsilon/a_n)^\gamma\). This cannot imply the required depth decay at fixed ε₁ as ε/a_n tends to zero. The correct attempt is to retain the interface term in the complete constrained second variation and compare that expression, or derive a genuine two-run interface cancellation. No such cancellation has been proved here. PBG (3.114)–(3.115), obtained by linearising the gauge transformation, does not by itself supply the required second-order multiscale identity.

Sources: [VAR p.302, (154)–(156)](../Balaban/tex/VAR/parts/p302_corrected.tex), [PBG p.418](../Balaban/tex/PBG/parts/p418_corrected.tex), [LFR II p.356](../Balaban/tex/LFR2/parts/p356_corrected.tex), LF §4(d).

## 8. What the Threshold Search Actually Checks

A search of the corrected transcriptions of CRE, LFR I, LFR II, RG I and RG II for the literal constants C₀ and C₁ gives the following distinctions.

| Occurrence | Role | Consequence for reducing the analyticity thresholds |
|---|---|---|
| CRE (2.28), p.259 | C₀ and C₁ in α_{0,j} and α_{1,j}; sufficiently large | For any fixed finite set of reduction factors μ, choose the initial constants above μ_max times the required lower bounds. |
| LFR II p.368 | C₁ in an upper bound proportional to the analyticity threshold | Shrinking that threshold does not enlarge this displayed bound. |
| LFR II p.379 | C₀ in the small error from α_{0,k}+α_{1,k} | The error remains small after shrinking. |
| LFR I (1.70), p.192 | C₀ as an activity-bound constant | This is not a reason to divide an activity bound by μ; retain the bound. |
| RG II (1.20), p.6, and its subsequent uses | C₁ in the estimate for B′, explicitly an absolute constant | It is distinct from the threshold coefficient in CRE (2.28); retain it. |
| Expressions C₀^∞ | Test-function spaces | Unrelated to these constants. |

RG I p.280 gives the homogeneous requirements B₃α₃<α₁/2 and 2B₃α₃≤βL^{-2}α₀. They are preserved when α₀, α₁ and α₃ are divided by the same μ. However, the fluctuation requirement at RG II (1.22), \(4B_0C_1e^{16\kappa_1}\varepsilon_1\leq\alpha_2/4\), is not homogeneous if the physical cutoff ε₁ is held fixed. It must be checked anew at α₂/μ. In the LF note's logarithmic hierarchy this amounts to a fixed factor μ in a cutoff-to-radius ratio; it is eventually harmless only when the asserted strict hierarchy of logarithmic powers and the identification of the relevant cutoff are valid.

This search checks direct uses of the names C₀ and C₁. It does not prove every inclusion involving α under another name, and it does not construct the complex lift or the joint chain interpolation. In particular, uniqueness of analytic continuation says that two extensions coincide where both are defined; it does not prove that the smaller fluctuation domain contains the required configurations.

Sources: [CRE p.259](../Balaban/tex/CRE/parts/p259_corrected.tex), [LFR II p.368](../Balaban/tex/LFR2/parts/p368_corrected.tex), [p.379](../Balaban/tex/LFR2/parts/p379_corrected.tex), [RG I p.280](../Balaban/tex/RG1/parts/p280_corrected.tex), [RG II p.7](../Balaban/tex/RG2/parts/p007_corrected.tex).

## 9. Status and the Next Substantive Estimates

| Original item | Result of this attempt | Still required |
|---|---|---|
| LF-A(3), complex variation | The direct threshold occurrences are distinguished; the boundary-margin loss has an explicit payment in §2. | The full complex configuration/current interpolation, the fine lift, and bounds on the admissible resummation along that interpolation. |
| LF-A(6), interfaces | The complete constrained second variation identifies a possible scalar Cauchy route in §7. | A depth estimate for the actual interface contribution, including π, and its localised use. |
| LF-A(7), localised terms | §3 constructs a supported right inverse of the restricted averaging map; §4 writes the nonlinear fixed-point difference with every residual retained. | Shellwise regularity, the fine-side comparison with dι, local operator defects, and e_C and e_F on the complex decoupling polydisc. |
| LF-A(10), boundary terms | §2 pays the shrinking margin; §5 recovers the earlier source connection for the exceptional bracket family; §6 derives the marked-expansion transfer and the preliminary-integration recursion. | The interpolation input, the complete crossing/resummation estimate for exceptional constituents, and the actual marked primitive bounds in the chosen norms. |

The most concrete next step is to prove the shellwise interpolation residual (G.12), including the Dirichlet boundary shell, and then use it in the local bilinear defect of the walk note. For the probabilistic expansion, the next step is (G.20) for the kernels of LFR I (1.60), with the physical normalisation and the scalar boundary mark (G.19) retained. These are separate operands; completing the support construction or the scalar product estimate does not complete either one.

No gap is marked closed in the original notes. No changes have been pushed to GitHub.

## 10. Continuation: The Small Coefficient in the Preliminary Boundary Recursion

The calculation in §6 left η_r unspecified. The present calculation concerns the response of a preliminary integration to a change of its already-created scalar boundary potentials, with the run's geometry, background maps and Gaussian kernels fixed. This is one part of the creation difference of LFR I (1.62). The other part changes those maps and kernels and remains a separate source.

### 10.1 The Operand and the Analytic Parameter

At preliminary integration n+1, put j=h+n. The part of (1.60) containing an already-created boundary potential F is

$$
\mathcal I_F(B_j)
=F\left(U_k^{(n)}\left(\exp i[g_jCB_j-h\widetilde D(g_jCB_j)]V^{(j)}\right)\right)
-F(U_k^{(n+1)})\;.
\tag{G.27}
$$

Any spectator fields in F are fixed at their values in this expression. This formula concerns its dependence through the reconstructed configuration. If an explicit spectator is also integrated or changed, its change is an additional mark; it is not included by suppressing the argument.

Let F be a local scalar input on domain X, analytic and bounded by f_X on the prior-step space \(\widetilde U_k^{(n)c}\). For a frozen difference, f_X is the majorant of that difference in the same space. Scale the **physical** datum ξ_j=g_jCB_j before the nonlinear correction, so the analytic family is

$$
\Phi_F(z)
=F\left(U_k^{(n)}\left(\exp i[z\xi_j-h\widetilde D(z\xi_j)]V^{(j)}\right)\right)\;.
\tag{G.28}
$$

At z=0 the configuration is U_k^{(n+1)}, with the same fixed spectators, and \(\mathcal I_F=\Phi_F(1)-\Phi_F(0)\). Scaling the complete expression by z after applying \(\widetilde D\) would be a different family and would not give the required analytic constraint map.

On the B_j cutoff, \(\|\xi_j\|\leq c_C\delta'_j\), with c_C the fixed norm of C. LFR I (1.44)–(1.45) bounds the resulting phase and its derivative by a fixed multiple of

$$
\delta'_j\exp\bigl(-\delta d(y,D_j)\bigr),
\qquad D_j=\Omega_{j+1}^c\setminus Z''_{j+1}\;.
\tag{G.29}
$$

In (1.46)–(1.48), the changes of the plaquette tests divided by their layer thresholds are controlled by

$$
C\frac{\delta'_j}{\varepsilon_j}
\bigl(1+\sqrt{|j-m|}\bigr)
e^{-\delta d(y,D_j)}
 + C\delta'_j e^{-\delta d(y,D_j)}\;.
\tag{G.30}
$$

The first ratio is the explicit \((A_1/A_0)p_1(g_j)/p_0(g_j)\) in (1.46). On earlier layers, (1.47) turns the distance into decay in |j−m|. The proof chooses M so this dominates both the square-root factor and the domain loss \(2^{-|j-m|}\). For the later layers, the corresponding inclusion uses (1.51)–(1.52). LFR I p.191 explicitly states that the complex-space inclusion and the corresponding current statement are proved by the same (1.44)–(1.52) argument.

For the family (G.28), the linear quantities in (G.29)–(G.30) carry |z|, and higher terms are controlled on the same local analytic ball when \(|z|\delta'_j\) is sufficiently small. Therefore the proposed strengthened inclusion is obtained by retaining the small coefficient in those estimates, rather than immediately replacing it by the fixed αβ of (1.48):

$$
|z|\leq R_j,
\qquad
R_j=c_*\frac{\varepsilon_j}{\delta'_j}\;,
\tag{G.31}
$$

where c_* is small in terms of β, B₃, c_C and the fixed geometric constants. Since \(|z|\delta'_j\leq c_*\varepsilon_j\), the same small-field thresholds control the nonlinear terms. The radius tends to infinity because p₁<p₀.

The plaquette and phase parts of this enlarged-radius argument are explicit in (1.44)–(1.52). Its full complex configuration/current version uses the source's stated extension on p.191. That reading must be checked for the enlarged radius, not only for |z|≤1, before this is used as an accepted LF input. In particular, it must include the reconstructed-current conditions in (1.64)–(1.68). The real-variable estimates alone do not settle that point.

### 10.2 The Frozen-Input Gain

Given that inclusion, \(|\Phi_F(z)|\leq f_X\) for |z|<R_j. For R_j≥2, its Taylor coefficients satisfy \(|a_l|\leq f_XR_j^{-l}\). Hence

$$
|\mathcal I_F|
\leq f_X\sum_{l\geq1}R_j^{-l}
\leq 2c_*^{-1}\frac{\delta'_j}{\varepsilon_j}f_X
=2c_*^{-1}\frac{A_1}{A_0}
\frac{p_1(g_j)}{p_0(g_j)}f_X\;.
\tag{G.32}
$$

This is a negative power of log g_j^{-2}. It does not use oddness of B_j, independence of A_j and B_j, or cancellation under a reference Gaussian. Its scalar mark is inserted in the actual joint integral (1.60). The output carries the marked factor through CRE (3.44)–(3.47) and the corresponding construction for (1.60): the numerator has one marked activity, while the disconnected vacuum polymers cancel against the actual denominator. The linearity in that marked activity preserves the factor in (G.32), subject to the same localisation and norm transfer as the printed boundary expansion.

Thus the candidate coefficient for the configuration-dependent frozen-input contribution is

$$
\eta_j=C_{\mathrm{mark}}\frac{A_1}{A_0}
\frac{p_1(g_j)}{p_0(g_j)}\;.
\tag{G.33}
$$

Here C_mark includes the Cauchy constant and the marked local expansion. It is not asserted to equal the constant for a single-scale small-field integral. Its uniformity requires the mixed-domain resummation of LFR I (1.63), and the complex inclusion just identified. No estimate for the new covariance or background difference is hidden in η_j; those contribute to s_r in (G.22).

### 10.3 The Number of Overlapping Integrations

The weak estimate N₀=O(log g_k^{-2}) would be wasteful for (G.33). LFR I p.192 gives the more precise defining relation and bound

$$
L^{N_0-1}=R_{k-N_0+1}
\leq (L+1)(N_0+1)^{\beta_0}R_k\;.
\tag{G.34}
$$

Taking logarithms, and absorbing \(\beta_0\log(N_0+1)\) into \(\tfrac12N_0\log L\) beyond a fixed finite N₀, yields

$$
N_0\leq C_L+\frac{2}{\log L}\log R_k
\leq C\bigl(1+\log\log g_k^{-2}\bigr)\;.
\tag{G.35}
$$

The last inequality uses the stated upper bound R_k≤L(log g_k^{-2})^r. It holds with constants depending on L, r and β₀, independently of k and K. Write p₀(g)=\((\log g^{-2})^{a_0}\) and p₁(g)=\((\log g^{-2})^{a_1}\), with a₁<a₀; these letters distinguish the exponents from the functions in this calculation. For the N₀ overlapping scales the coupling comparison changes the logarithms only by fixed factors for small coupling. Therefore (G.33) gives

$$
\sum_{\text{overlapping }r}\eta_{j(r)}
\leq C\frac{1+\log\log g_k^{-2}}
{(\log g_k^{-2})^{a_0-a_1}}
\longrightarrow 0\;.
\tag{G.36}
$$

Even an additional N₀ from an explicitly justified counting step is harmless, since

$$
\frac{(1+\log\log g_k^{-2})^2}
{(\log g_k^{-2})^{a_0-a_1}}\longrightarrow0\;.
\tag{G.37}
$$

Substitution in (G.23) gives a bounded cumulative multiplier for this frozen-input part, for example at most e after the sum in (G.36) is at most 1. This addresses the accumulation in the actual preliminary integrations. It supplies no bound for the sum of the new sources s_r unless each source is separately estimated.

### 10.4 Exact Remaining Check

The new calculation extracts the radius (G.31) and hence the small coefficient (G.33) from Bałaban's preliminary-integration domain argument, and uses the exact N₀ relation to control its cumulative effect. Its remaining source-reading checks are the enlarged-radius **current and reconstructed-current** inclusions on p.191 and preservation of the marked coefficient through the mixed-domain resummation (1.63). These are narrower than an unspecified claim that all of (LF) holds. The changes of the background maps and quadratic kernels are still the genuine two-run sources; the preceding calculation has not bounded them.

Sources: [LFR I pp.185](../Balaban/tex/LFR1/parts/p185_corrected.tex), [186](../Balaban/tex/LFR1/parts/p186_corrected.tex), [187](../Balaban/tex/LFR1/parts/p187_corrected.tex), [191](../Balaban/tex/LFR1/parts/p191_corrected.tex), [192](../Balaban/tex/LFR1/parts/p192_corrected.tex), and [CRE pp.277](../Balaban/tex/CRE/parts/p277_corrected.tex)–[278](../Balaban/tex/CRE/parts/p278_corrected.tex).

### 10.5 The A_j Integration: An Omitted Feedback Term

LFR I (1.63) writes the newly created contribution as

$$
\mathbb C_k^{(q)}
=\sum_X\mathbb C_k^{(q)}(X,U_k^{(q)})\;.
\tag{G.38}
$$

Its displayed analytic arguments are the pair (𝕌,𝕁) on the spaces of pp.190–191. It would be incorrect to infer independence of retained fluctuation fields from the suppressed arguments in (1.63). LFR II (1.49), p.369, writes the sum after the preliminary integrations as \(\mathbf B_k''(U_k'',A)\). Thus the newly created terms, as well as the earlier boundary terms, must be checked for dependence on A_j. An earlier version of this subsection inferred independence from (1.63); that inference is withdrawn.

The subtraction in (1.60) evaluates the base term at A_j=0. Accordingly, (G.27) is only its configuration-dependent part. The full joint A_j,B_j law, including its interaction and normalisation, must be kept when estimating the other part.

An inherited term with explicit A_j dependence must instead be split as

$$
F(U(B_j),A_j)-F(U(0),0)
=\bigl[F(U(B_j),A_j)-F(U(0),A_j)\bigr]
 +\bigl[F(U(0),A_j)-F(U(0),0)\bigr]\;.
\tag{G.39}
$$

Only the first bracket has the configuration-dependent structure of (G.27), assuming its bound is uniform over the allowed A_j. The second bracket is a distinct scalar fluctuation insertion. If F is itself a carried difference, the second bracket is linear in that difference and belongs in the feedback coefficient η_r, not in an independent source s_r. Equation (G.32) gives no δ′_j/ε_j gain for it. Until that mark is bounded, (G.33) is a coefficient for one part of the feedback only.

For an earlier q≤n, the descending spaces on p.191 place the step-n class inside the class on which \(\mathbb C_k^{(q)}\) is bounded. Thus using its bound on the prior-step class in (G.28) does not require an additional change of threshold for each q. The enlarged fluctuation disc must still map into that prior-step class, as required in §10.1.

### 10.6 The Variational Current on the Enlarged Disc

There is a stronger source estimate than the first-derivative bound (1.45). VAR (190) bounds the data derivative of the nonlinear minimiser response \(\mathscr H\), its first derivative, and both \(D_U^*D_U\) and \(\Delta_U\) applied to that data derivative. For a datum supported at y′ of layer m′ and an output point x of layer m, the respective powers are

$$
(a_m^{-1},a_m^{-2},a_m^{-3},a_m^{-3})
a_{m'}^{-d}e^{-\delta_0d(y,y')/8}\;.
\tag{G.40}
$$

The data integral uses the weight a_{m′}^d, so the extra factor a_{m′}^{−d} is not a count of all fine sites. Proposition 9 states these bounds also for the analytic extension of the minimiser on its stated regular-background domain.

For a source of size b_j on D_j, integrate the data derivative along the segment from zero to that source. The first two resulting bounds are (G.29); the last two also give, with a smaller fixed decay rate to perform the kernel sums,

$$
a_m^3|D_U^*D_U\mathscr H(x)|
+a_m^3|\Delta_U\mathscr H(x)|
\leq C b_j e^{-\delta' d(y,D_j)}\;.
\tag{G.41}
$$

This uses the same weighted kernel summability as the first two entries, and requires that the data segment remain in Proposition 9's analytic domain. With b_j=|z|δ′_j≤c_*ε_j, that is a fixed small-field requirement.

To apply this to the variational current, take the analytic path U_t supplied by the constrained minimiser and use its left-trivialised tangent K_t. PBG (3.10)–(3.12) writes the action Hessian as D_U^*D_U+Δ′_U, with Δ′_U a local curvature perturbation. The derivative of the current in a fixed left frame differs from this Hessian applied to K_t only by the frame commutator with J. Consequently, on a layer-m regularity patch,

$$
a_m^3\left|\frac{d}{dt}J(U_t)\right|
\leq C\left(a_m^3|D_{U_t}^*D_{U_t}K_t|
 +\epsilon_{\rm reg}a_m|K_t|
 +\eta a_m^3|K_t|\,|J(U_t)|\right)\;.
\tag{G.42}
$$

Here ε_reg bounds the dimensionless curvature on that patch. The short parallel transports in the fixed-frame expression have bounded norms. The nonlinear exponential relating K_t to the derivative of \(\mathscr H\) adds products controlled by its first two entries in (190), while (G.41) controls the second-derivative entry. For a sufficiently small datum this yields

$$
a_m^3|J(U_1)-J(U_0)|
\leq C b_j e^{-\delta''d(y,D_j)}\;.
\tag{G.43}
$$

Thus the actual variational current has the same source factor b_j as the phase. Dividing by its layer threshold α_{0,m}, and using α_{0,m}≥ε_m and the coupling comparison in (1.46), gives the same type of factor as (G.30). The loss in decay from the kernel sums is paid by choosing the fixed geometric separation large enough; the inequality \((1+\sqrt{|j-m|})e^{-c|j-m|}\leq C2^{-|j-m|}\) requires c>log 2.

Two qualifications remain essential. First, the independently supplied current variable 𝕁 in an analyticity space is not automatically the variational current J(𝕌). Formula (G.43) treats the latter. The analytic substitution of the independent current in (1.60) must be checked against the source's extension. Second, the class also tests the reconstructed currents \(J_{p,X}(M^\cdot U_t)\). Applying (190) to that local reconstruction and composing with the derivative of the averaging map is the required next calculation; its factors must reproduce the exact \(L^{m-\min(p,m)}\) in (1.64)–(1.68). It is not enough to cite the phase bound for those quantities.

Sources: [VAR pp.308](../Balaban/tex/VAR/parts/p308_corrected.tex)–[309](../Balaban/tex/VAR/parts/p309_corrected.tex), [PBG pp.392](../Balaban/tex/PBG/parts/p392_corrected.tex)–[393](../Balaban/tex/PBG/parts/p393_corrected.tex), [LFR I p.190](../Balaban/tex/LFR1/parts/p190_corrected.tex).

## 11. Focused Review of §10.1–10.4

The [isolated review](verification/isolated_reviewer/reviews/lf-gamma-boundary-20261028-r1/review.txt) examined §10.1–10.4 before §10.5–10.6 were added. Its [manifest](verification/isolated_reviewer/reviews/lf-gamma-boundary-20261028-r1/manifest.json) records a passed access preflight, one model request, no gateway errors and no tool events. These facts establish the review procedure, not the mathematics.

The reviewer checked the conditional Cauchy estimate and the algebra giving N₀=O(1+log R_k). It did not accept the full creation estimate. Its objections are retained here:

- The enlarged complex inclusion must include the independent current, reconstructed configurations and currents, the changing determining sets, the later layers, and the local gauge condition (1.69). Section 10.6 addresses the variational-current part only.
- The subtraction in (1.60) also sets A_j=0. This is a feedback term when it acts on a carried difference. Section 10.5 now retains it; the earlier inference of independence from the notation (1.63) was invalid, as LFR II (1.49) confirms.
- The marked-expansion constant must be controlled. CRE's O(p₀³) must be identified as an insertion size or accounted for as an operator loss; it cannot be ignored.
- A local norm and the mixed-domain resummation are needed. Summation over the N₀ overlapping integrations does not by itself control the other N−N₀ integrations.
- The interpolation of the logarithm and the coupling counterterm in (1.62) must be included explicitly. The frozen-input calculation does not bound changes of the coupling prescription.

Some source statements needed for these checks were absent from the packet, including the earlier subsection containing (G.22)–(G.23), the CRE bound on R_k, and the definitions of the nonlinear correction. Their absence limits this review and does not supply evidence for those statements. A follow-up must include them rather than ask the reviewer to infer them.

## 12. The Marked Constant and the Explicit Quadratic A_j Terms

### 12.1 The Rooted Expansion Keeps the Physical Denominator

The mark in a difference of logarithms is obtained by interpolation of the **full** integral. For fixed background maps, kernels, couplings and cutoffs, let I_Δ be the full scalar fluctuation subtraction of a varying boundary input, including both brackets of (G.39). If Z_t is the integral (1.60) with that input interpolated, then

$$
\log Z_1-\log Z_0=\int_0^1\frac{\int I_\Delta e^{S_t}\,d\nu}{\int e^{S_t}\,d\nu}\,dt\;.
\tag{G.44}
$$

Here dν includes both integration fields, the displayed Gaussian forms, the gauge constraints and the cutoffs; S_t contains the remaining interactions. The integration is finite dimensional. At complex background data the identity uses the analytic logarithm supplied by the convergent cluster expansion, not positivity of Z_t.

CRE (3.44)–(3.45) implements the quotient in (G.44) explicitly. Write H′_I(Z₀) for the polymer activity with the scalar mark inserted. The same unmarked polymer activities H occur in the numerator away from Z₀ and in the denominator. Thus the contribution of that root is

$$
H'_I(Z_0)\exp\bigl(\log\Xi_{\overline Z_0^c}-\log\Xi\bigr)\;.
\tag{G.45}
$$

The difference of logarithms contains only connected clusters having a polymer incompatible with Z₀. Vacuum clusters disjoint from the root cancel before absolute values. This is the cancellation that prevents a factor proportional to the total physical volume.

The hard-core cluster stage has a precise root estimate. Suppose a positive size function a(P) and the unmarked activities satisfy

$$
\sum_{P:\,P\not\sim Q}|H(P)|e^{a(P)}\leq a(Q)\;.
\tag{G.46}
$$

The usual rooted-tree majorant is bounded by e^{a(Q)}: iterate the tree recursion

$$
T_{r+1}(Q)=\exp\left(\sum_{P:\,P\not\sim Q}|H(P)|T_r(P)\right),
\qquad T_0(Q)=1\;.
$$

If T_r(P)≤e^{a(P)}, (G.46) gives T_{r+1}(Q)≤e^{a(Q)}. Monotone convergence gives the same bound for the sum of rooted trees. The hard-core connected-graph expansion is dominated by this tree sum. Consequently the connected polymers attached to a single mark have a bound proportional to

$$
|H'_I(Z_0)|e^{a(Z_0)}\;.
\tag{G.47}
$$

For spatially weighted bounds, put the desired tree-length weight into the unmarked activities before applying (G.46); the root must have enough remaining decay to pay e^{a(Z₀)}. The activity and geometric estimates in RG II and LFR II supply such a margin for the unmarked expansion. Applying (G.47) to mixed-scale domains requires the same weighted count, rather than a count in the number of finest-lattice points.

This calculation locates the possible coupling dependence. The combinatorial map from H′_I to its attached connected clusters has no compulsory p₀(g)^3 factor. Any such factor must already enter through the size of the root H′_I, the chosen weights in (G.46), or a failure to keep those weights uniform.

CRE p.278 applies the construction to the specific insertion of (3.37), whose displayed bound is O(p₀³(g_k)) before multiplication by g_k. One cannot infer a universal O(p₀³) operator norm from that sentence. Equally, the tree estimate does not prove a uniform bound for H′_I. That primitive marked integral, and its localisation on the common complex polydisc, still have to be bounded for the insertion at hand.

### 12.2 A Quadratic Mark in the Retained Fluctuation Field

The explicit Gaussian boundary contributions have scalar quadratic vertices. On the shared scale-j field space write one such difference, with all transports retained in the coefficient, as

$$
I_2(A)=\frac12\sum_{b,b'}\operatorname{tr}\bigl(A(b)K(b,b')A(b')\bigr)\;.
\tag{G.48}
$$

The kernel transforms at both endpoints so the whole contraction is gauge invariant. The summation convention here is the discrete one in the rescaled Gaussian variable; any lattice weights belong in K. A linear vertex is treated as a whole scalar contraction as well.

Let the real reference Gaussian used in the primitive polymer integral be centred, with diagonal second moments bounded by C_G. No independence of bonds is required. Cauchy–Schwarz for each pair of bonds gives

$$
\int |\operatorname{tr}(A(b)K(b,b')A(b'))|\,d\mu
\leq C_{\mathfrak g}C_G\|K(b,b')\|\;.
\tag{G.49}
$$

Multiplying by any cutoff bounded between zero and one preserves this **unnormalised** estimate. No lower bound such as μ(χ)≥1/2 is needed, even when the root domain has many bonds. The physical normalisation is handled by (G.45), not by dividing this estimate by the mass of a large cutoff event.

If r_j is the A_j cutoff radius, put \(v_{bb'}=r_j^2\|K(b,b')\|\), the natural sup majorant of that individual quadratic vertex on the cutoff ball. Its Gaussian root contribution is then bounded by

$$
C_{\mathfrak g}C_G r_j^{-2}v_{bb'}\;.
\tag{G.50}
$$

The bound is per marked pair of bonds. Keeping that pair as the root avoids replacing it by a supremum over all bonds of a polymer and introducing a logarithm of the polymer volume. The exponential decay of K must control the sum over the second endpoint and the localisation domain. For example, a bound on \(\sup_b\sum_{b'}e^{\mu d(b,b')}\|K(b,b')\|\) supplies the corresponding sum of (G.49).

The cluster terms in which this root is connected to at least one ordinary interaction carry that interaction's activity amplitude. This follows by multiplying the ordinary activities by a parameter ζ, subtracting the value at ζ=0, and applying Cauchy's estimate on the fixed activity ball of the convergent expansion. If that amplitude is a_j and the allowed activity norm is a fixed \(\overline a\), the resulting coefficient is C a_j/\(\overline a\), with the same rooted spatial sums. The candidate gain in this quadratic sector is therefore

$$
\eta_j^{(A,2)}\leq C\bigl(r_j^{-2}+a_j\bigr)\;.
\tag{G.51}
$$

For the original A_j cutoff, r_j is a fixed multiple of p₀(g_j), so the first term tends to zero. A scalar linear vertex has zero centred-Gaussian contribution when the complete Gaussian form and cutoffs are invariant under simultaneous sign reversal of the integrated fields. Its interacting contribution still goes through the connected rooted expansion. If a frozen exterior field creates a linear source in the chosen Gaussian reference, that source must remain an interaction or its nonzero mean must be kept; it cannot be discarded by calling the Gaussian centred.

At complex backgrounds, the primitive integral is the one displayed in RG II (2.14)–(2.15), with a complex covariance and the conditional external-field factor. Its absolute Gaussian comparison includes a determinant ratio and an exponential cost on the root domain. These costs are paid from the localisation reserve in the printed proof. They are not a dimension-independent numerical constant. Establishing the corresponding marked comparison is necessary before (G.51) is claimed on the full complex class.

**Scope of this calculation.** It treats the explicitly identified quadratic kernel vertices. It does not show that an arbitrary bounded function of A_j has gain r_j^{-2}, nor that the whole inherited boundary potential is quadratic. Nonquadratic A_j-dependent terms require their own analytic or marked integral bound. Also, a row norm of K is not automatically controlled by the original scalar sup norm of the complete boundary potential; the quadratic extraction and its norm must be matched to the actual carried difference.

Sources: [CRE pp.270](../Balaban/tex/CRE/parts/p270_corrected.tex)–[271](../Balaban/tex/CRE/parts/p271_corrected.tex), [277](../Balaban/tex/CRE/parts/p277_corrected.tex)–[278](../Balaban/tex/CRE/parts/p278_corrected.tex), [RG II p.15](../Balaban/tex/RG2/parts/p015_corrected.tex), [LFR II p.369](../Balaban/tex/LFR2/parts/p369_corrected.tex).

## 13. A Candidate Exact Cancellation of the Multiscale π-Term

This is a separate attempt at the first interface item of LF-A(6). It uses the gauge covariance of the existing averaging maps and the complete scalar quadratic form. No estimate of open transport segments is introduced. The proposal is that the layerwise divergence used in the LF note is not the appropriate adjoint for the bilinear gauge parameter at an interface.

### 13.1 The Induced Gradient on the Determining Set

Fix one of PBG's determining sets. Let Q be its multiscale bond averaging, Q′ its multiscale scalar averaging, and D the fine covariant gradient. Use the physical lattice weights in all pairings: η^d on the fine lattice and a_j^d at a determining site of layer j. The blocks B^j(y), y∈Λ_j, partition the fine sites by PRT2 (2.4).

The quadratic coefficient C^{(2)} is normalised in the same physical units as Q: on a layer-j bond, the expansion of \(a_j^{-1}(1/i)\log\overline{\overline{e^{i\eta A}}}^{\,j}\) is \(Q_jA+C^{(2)}[A,A]+O(A^3)\). This is the second convention described immediately after PBG (3.127). The gauge parameters and q_j are dimensionless, so their gradients carry the factor a_j^{-1}.

Let E be the transported block-constant scalar lift. On B^j(y),

$$
(E\omega)(x)
=\operatorname{Ad}\bigl(U(\Gamma^{(j)}_{y,x})\bigr)^{-1}\omega(y)\;.
\tag{G.52}
$$

PBG (3.19) gives Q′E=I. With the pairings just specified, E=(Q′)*: the factor η^d/a_j^d in the average is exactly cancelled when taking its adjoint. This remains an algebraic statement for the complex bilinear pairing because the complexified adjoint representation preserves the invariant bilinear form. Fixed exterior gauge variables are excluded, or equivalently assigned value zero, throughout.

PBG (3.115), followed by the statement concerning N(Q′), gives

$$
QD\mu=0\quad\text{if}\quad Q'\mu=0\;.
$$

Define the induced data gradient by

$$
\mathcal D=QDE\;.
$$

Since \(\mu-EQ'\mu\in\ker Q'\),

$$
QD=\mathcal DQ'\;.
\tag{G.53}
$$

On a bond contained in one layer, 𝒟 is the usual covariant difference at that layer. At a bond whose outer endpoint lies in finer determining blocks, its endpoint value is the transported average of those finer scalar values. Its adjoint therefore contains the interface transfer terms. It is not obtained by computing the ordinary divergence of each layer separately and setting all other layers to zero.

If a current has J=Q*ν and D*J=0, then

$$
0=D^*Q^*\nu=(Q')^*\mathcal D^*\nu
=E\mathcal D^*\nu,
\qquad
\mathcal D^*\nu=0\;,
\tag{G.54}
$$

because E is injective. The identity is with the full weighted adjoint, so no factor a_j^d is omitted at an interface.

### 13.2 Coherence of the Bilinear Gauge Parameter

Use the notation of the Cauchy note's (B5). For the j-fold double bar, the induced gauge transformation has logarithm

$$
\frac1i\log w_j
=tQ'_j\mu+st\,q_j(\mu,Y)+O(t^2)+O(s^2t),
\tag{G.55}
$$

where s scales the fluctuation Y and t scales the fine gauge parameter μ. Its first mixed coefficient obeys the composition rule obtained by differentiating CMP 98 (90)–(91):

$$
q_{j+1}(\mu,Y)
=Q'_1\,q_j(\mu,Y)
 +q_1(Q'_j\mu,Q_jY)\;.
\tag{G.56}
$$

The one-step operators and the second term are evaluated at the corresponding level-j background. Equation (G.56) is a chain rule for the actual induced gauge transformations, not a definition by analogy.

Now assume Q′μ=0 on the multiscale determining set. At a data bond of layer j, both endpoint j-blocks are either determining j-blocks or unions of finer determining blocks. They cannot contain a determining block of a coarser layer: bonds touching the inner region belong to that inner region under the star-of-sites convention, and are removed when forming Λ_j. This is the bond convention in PRT2 (2.3). Block compatibility and the separation condition (2.2) ensure that the endpoint blocks can be treated by the nested subdivision.

On every leaf of such a subdivision the corresponding average of μ vanishes. It therefore vanishes at all internal nodes as well. The second term in (G.56) is zero at each averaging of those nodes. Consequently q_j at an endpoint is the transported average of the q-values on its determining leaves.

Define q(μ,Y) on a determining site y of layer j to be q_j(μ,Y)(y). The preceding recursion gives, at every endpoint needed by a layer-j data bond,

$$
q_j(\mu,Y)=Q'_jE\,q(\mu,Y)\;.
\tag{G.57}
$$

This is the crucial coherence statement to check. It uses Q′μ=0; it is not asserted for an arbitrary fine gauge parameter. It also uses the endpoint-block geometry just described. If that geometry fails for a modified determining set used by the caller, the cancellation below has not been established for that set.

The layerwise identity (B5), with its term bilinear in Q′_jμ equal to zero on the required endpoint blocks, now assembles as

$$
2C^{(2)}[D\mu,Y]
=Qc(\mu,Y)+\mathcal Dq(\mu,Y)\;.
\tag{G.58}
$$

The same 𝒟 as in (G.53) appears: on each row, \(\overline D^jQ'_jE=Q_jDE\) by PBG (3.115). Thus (G.54) implies

$$
2\langle C^{(2)}[D\mu,Y],\nu\rangle
=\langle Q^*\nu,c(\mu,Y)\rangle\;.
\tag{G.59}
$$

### 13.3 The π Cancellation and the Aligned Pair

Put μ_A=G′RD*A and PA=A−Dμ_A, as in PBG (3.119), so Q′μ_A=0. The scalar bracket of PBG (3.120) is

$$
\langle A,\Delta'_\pi[J]A\rangle
=\langle J,c(\mu_A,A)+c(\mu_A,PA)\rangle\;.
\tag{G.60}
$$

Bilinearity of C^{(2)} and (G.59) give

$$
2\langle C^{(2)}[PA,PA]-C^{(2)}[A,A],\nu\rangle
=-\langle Q^*\nu,c(\mu_A,A)+c(\mu_A,PA)\rangle\;.
\tag{G.61}
$$

For J=Q*ν these cancel. Since QH=I, this is exactly the cancellation in the scalar π-form used by Cauchy §10.4. Polarisation then gives π=0 as a bilinear form. No bound on an individual interface divergence is needed; its contribution is paired with the coherent scalar data in (G.57).

The aligned current in run A is not its background's own variational current, so (G.54) must also be checked there. Let the matched full multiscale averagings satisfy Q_B=Q_AQ₁ and let the physical run-B current be J_B=Q_B*ν_B. Then J′_A=Q_A*ν_B obeys J_B=Q₁*J′_A. The one-step identity Q₁D_B=D_AQ′₁ and gauge invariance of the run-B action imply

$$
0=D_B^*J_B=(Q'_1)^*D_A^*J'_A\;.
$$

The scalar one-step averaging is onto, so its adjoint is injective, and

$$
D_A^*J'_A=0\;.
\tag{G.62}
$$

Thus the proposed cancellation applies to this aligned pair as well, provided the multiscale chain rule and endpoint geometry are those of the caller. The young histories have no determining layer at the deleted fine scale, which is needed for this common-data factorisation.

This does **not** restore every Landau-gauge identity at the aligned pair. The plain action Hessian still uses the actual current of the aligned background, which may differ from J′_A. The warning in Cauchy §10.4, *The Landau Condition at the Pair*, remains relevant. The present argument concerns only the additional π-form, whose current slot is J′_A.

### 13.4 Status

Equations (G.53)–(G.62) propose an exact resolution of the first interface item in LF-A(6). The delicate step is (G.57): the bilinear gauge parameter must obey the nested averaging rule on the actual determining sets, with the star-of-sites bond convention. This derivation is being subjected to focused review before it is used to remove that item from the list of gaps. The twist term involving the second-order data and the multiscale alignment remain separate questions.

Sources: [PRT2 p.224](../Balaban/tex/PRT2/parts/p224_corrected.tex), [CMP 98 p.31](../Balaban/tex/CMP98/parts/p031_corrected.tex), [PBG pp.393](../Balaban/tex/PBG/parts/p393_corrected.tex), [418](../Balaban/tex/PBG/parts/p418_corrected.tex), [419](../Balaban/tex/PBG/parts/p419_corrected.tex), [420](../Balaban/tex/PBG/parts/p420_corrected.tex); Cauchy §10.1(B5) and §10.4, *The π-Part of β*.

## 14. The Second-Order Twist as a Function of Shared Block Data

The second interface item of LF-A(6) asks for the run difference of the twist term in (G.25). VAR (154) gives its nonlinear map explicitly. At an interface bond c=(x,x′), it is

$$
\mathcal T_c(V)
=\exp\left(-iL^{-d}\sum_{x_1\in B(x)}\frac1i\log V(\Gamma_{x,x_1})\right)V(c)\;.
\tag{G.63}
$$

The field V consists of the block data on the two adjacent levels. In a young history these levels are shared physical lattices in the two runs. The formula, paths and finite number of inputs in (G.63) are consequently the same. There is no remaining dependence on the fine cutoff in the definition of this map. There is dependence through the values of V and through the choice of common frames in which they are compared.

Work on the local regular chart used to derive VAR (154)–(155), with every required contour holonomy inside a fixed logarithm chart. Choose a smaller chart with a fixed positive margin. The radius is a fixed constant depending on d, L and the local geometric constants; it must not shrink with the fine spacing. The small-coupling conditions ensure the real data are inside it. Use of the complex inductive class requires checking that the compared data and the intervening complex neighbourhood stay inside this chart.

Let b_e be dimensionless Lie-algebra data on the edges read by (G.63), with zero values on edges not perturbed. Define

$$
V(t)_e=e^{itb_e}V_e,
\qquad
\frac1i\log\bigl(\mathcal T_c(V(t))\mathcal T_c(V)^{-1}\bigr)
=t\,T_{1,c}(V)b+t^2T_{2,c}(V)[b,b]+O(t^3)\;.
\tag{G.64}
$$

This definition includes the Baker–Campbell–Hausdorff terms of both the contour products and the final product with V(c). They are not discarded or replaced by the square of the linear twist.

Let \(\mathcal S_c\) be the finite set of edges read by (G.63), and set \(\|b\|_c=\max_{e\in\mathcal S_c}|b_e|\). Products, logarithms and exponentials are analytic on the chosen chart. Their first three derivatives are bounded there by constants depending only on that chart and the maximal path length. Therefore there is a constant C_T, independent of the RG depth and fine spacing, such that

$$
|T_{2,c}(V)[b,b]|\leq C_T\|b\|_c^2\;.
\tag{G.65}
$$

For two data configurations joined inside the smaller chart, put

$$
\delta_c=\max_{e\in\mathcal S_c}
\left|\frac1i\log(V^B_e(V^A_e)^{-1})\right|\;.
$$

Differentiate (G.64) twice in t and once along the base-data interpolation. The mixed derivative is bounded by the same finite-dimensional analytic estimate, giving

$$
|T_{2,c}(V^B)[b,b]-T_{2,c}(V^A)[b,b]|
\leq C_T'\delta_c\|b\|_c^2\;.
\tag{G.66}
$$

Equivalently, this follows by Cauchy's formula on a fixed disc in t and a fixed complex neighbourhood of the base data. Its radius in the t-variable is proportional to \(\|b\|_c^{-1}\), producing exactly the two powers in (G.66). Only a finite number of contour factors is involved; no factor proportional to the number of fine bonds between physical scales occurs.

For the physical data convention of §13, \(\widetilde b_{2,c}=a_c^{-1}T_{2,c}(V)[b,b]\), where a_c is the spacing of the bond c. The invariant pairing has weight a_c^d. At common b, telescoping the complete twist contraction gives

$$
\begin{aligned}
&2\left|\sum_c a_c^d\left(
\langle\widetilde b^B_{2,c},\nu^B_c\rangle
-\langle\widetilde b^A_{2,c},\nu^A_c\rangle\right)\right|\\
&\quad\leq C\sum_c a_c^{d-4}
\left[\delta_c\,a_c^3|\nu^B_c|
 +a_c^3|\nu^B_c-\nu^A_c|\right]\|b\|_c^2\;.
\end{aligned}
\tag{G.67}
$$

The power a_c^{d−4} is the product of the pairing weight, the inverse spacing in \(\widetilde b_2\), and the inverse-cubic scaling of the multiplier. In d=4 it is one. When the physical angular datum is g_jb and the action carries g_j^{-2}, these two powers of g_j cancel, exactly as in the quadratic form of (1.2). A different datum in the two runs adds the bilinear contribution bounded by \(C_T(\|b_A\|_c+\|b_B\|_c)\|b_B-b_A\|_c\); that term must be kept when present.

Thus the desired fine-spacing gain follows for this contribution if the already-named data and multiplier comparisons give

$$
\delta_c\leq C\rho_n,
\quad a_c^3|\nu^B_c|\leq C\varepsilon_1,
\quad a_c^3|\nu^B_c-\nu^A_c|\leq C\rho_n\varepsilon_1,
\qquad
\rho_n=(\varepsilon/a_n)^{(1-\varepsilon_0)/3}\;.
\tag{G.68}
$$

The multiplier estimate in (G.68) is the open multiscale alignment item; it is not proved by this calculation. The configuration-data comparison and the common-frame identification must also be the actual ones of the denominator. Nevertheless, no new fine-lattice operator comparison is needed for the second derivative of the twist map itself. Its dependence on the two runs is reduced explicitly to those inputs, with its nonlinear terms retained.

The calculation is performed in the fixed VAR representatives. The twist contraction remains inside the complete gauge-invariant second variation (G.25), including its other terms. The coefficient T₂ is not promoted to a new independently estimated Wilson observable or polymer species.

Source: [VAR p.302, (154)–(156)](../Balaban/tex/VAR/parts/p302_corrected.tex); LF §4(d), *The form of (1.2)* and *The multipliers*.

## 15. Comparing the Multipliers by Differentiating the Minimum Action

The third interface item in LF-A(6) is a comparison of multipliers at different layer data. Gauge covariance only compares gauge-related data. The following construction uses the actual change of data instead. It concerns the variational multipliers of the minimisers, not the independent current variable in an old-term analyticity class.

### 15.1 The Envelope Identity

Let D denote the common dimensionless group-valued data on a fixed determining set, and let U_X(D) be its constrained minimiser in run X. Define the unweighted classical minimum action

$$
S_X(D)=A_X(U_X(D)),\qquad X=A,B\;.
$$

Use the plain constraint initially. If \(J_X=Q_{{\rm pl},X}^*\lambda_X\), differentiation of the constraint and stationarity give, for a dimensionless angular data variation b,

$$
dS_X(D)[b]
=\sum_c a_c^{d-1}\langle\lambda_{X,c},b_c\rangle\;.
\tag{G.69}
$$

The factor a_c^{-1} comes from converting angular data to the physical units of Q_pl. The fine-lattice pairing in dA_X cancels through the adjoint. Both runs have the same a_c and the same data variation. Consequently, at equal D,

$$
a_c^{d-1}(\lambda_{B,c}-\lambda_{A,c})
=\frac{\partial}{\partial b_c}(S_B-S_A)\;,
\tag{G.70}
$$

with the derivative understood by duality in the invariant form. No identification of the two fine field spaces is needed in this scalar identity.

### 15.2 Localising Before Differentiating

A bound on |S_B−S_A| proportional to the entire volume would be insufficient for (G.70). Use a smooth partition of unity w_y, at the physical sizes of the determining blocks, with bounded overlap and a_m|∇w_y|≤C on a layer-m block. The weights are common physical functions in the two runs. Set

$$
F_y(D)=A_B(w_y,U_B(D))-A_A(w_y,U_A(D))\;.
$$

Then S_B−S_A=\(\sum_yF_y\), including any fixed exterior contribution, whose derivative with respect to the data is zero. The weighted action comparison in LF §4(b)–(c) is the input for these quantities. The exact form needed, on a fixed complex data neighbourhood, is

$$
|F_y(D)|\leq C\varepsilon_1^2\rho_{m(y)},
\qquad
\rho_m=\left(\frac{\varepsilon}{a_{\min(m,n)}}\right)^a\;.
\tag{G.71}
$$

The exponent a is the exponent actually established on that complex neighbourhood. One must use the complex exponent, including any two-constants loss, rather than the stronger real exponent. In d=4 each term is dimensionless: the weight support has volume of order a_m^4 and the action density is of order ε₁²a_m^{-4}.

For a variation of one datum at c, use

$$
D_c(z)=e^{izrT}D_c,\qquad |z|<2,
\quad |T|=1,\quad r=c_0\varepsilon_1\;.
\tag{G.72}
$$

All other data are fixed. The constant c₀ is chosen so this disc lies in the analytic minimiser domain for both runs. VAR (190) gives exponential decay of the response to this datum. Differentiating each **one-run weighted action**, whose weighted current has size Cε₁a_m^{-3}, and summing the fine sites in the support of w_y gives

$$
|F_y(D(z))-F_y(D(0))|
\leq C\varepsilon_1r\,e^{-\delta_*d(y,c)}
\leq C'\varepsilon_1^2e^{-\delta_*d(y,c)}\;.
\tag{G.73}
$$

This bound is the sum of two one-run response bounds. It contains **no** small two-run factor, and none is assumed. The data kernel in (190) is integrated with its data-cell measure; the variation of one angular datum already has the corresponding physical scaling. Weighted kernel summability and the bounded overlap of the w_y are required uniformly at interfaces.

On the other hand, (G.71) at z and at zero gives an upper bound \(2C\varepsilon_1^2\rho_{m(y)}\) for the same difference. For 0<θ<1, combine these two bounds using min(u,v)≤u^θv^{1−θ}:

$$
|F_y(D(z))-F_y(D(0))|
\leq C\varepsilon_1^2\rho_{m(y)}^\theta
e^{-(1-\theta)\delta_*d(y,c)}\;.
\tag{G.74}
$$

This is the step that retains locality while differentiating the action-depth estimate. It avoids assuming that the derivative of a small action difference is already a small, local function.

### 15.3 The Layer Sum and the Cauchy Estimate

Suppose c is in a young component whose finest data scale is n. For m≥n, ρ_m=ρ_n. For m<n,

$$
\rho_m^\theta=\rho_n^\theta L^{a\theta(n-m)}\;.
$$

For blocks y separated from c by these finer layers, the scaled distance is at least a fixed multiple of RM(n−m), apart from a bounded number of adjacent layers. Therefore, after enlarging the fixed geometric constants so that

$$
\frac{a\theta\log L}{c_{\rm sep}RM}
\leq\frac12(1-\theta)\delta_*\;,
\tag{G.75}
$$

the extra factor L^{aθ(n−m)} is absorbed by half of the remaining distance exponential. The weighted sum of the other half is bounded by the same type of PRT2 kernel summability used in the minimiser response. One obtains

$$
\sum_y|F_y(D(z))-F_y(D(0))|
\leq C_\theta\varepsilon_1^2\rho_n^\theta\;.
\tag{G.76}
$$

The separation assertion and the weighted sum in this paragraph have to be verified for the caller's determining sets, including any joins and free-region boundary layers. If a fine layer lies immediately adjacent to c without the stated intervening layers, (G.75) cannot be used to charge n−m layers that are not present. This is a geometric hypothesis inherited from the source construction, not a free choice of distance.

Cauchy's formula on |z|=1, applied to the sum after subtracting its value at zero, now gives

$$
a_c^{d-1}|\lambda_{B,c}(D)-\lambda_{A,c}(D)|
\leq C_\theta\varepsilon_1\rho_n^\theta\;.
\tag{G.77}
$$

At d=4 the left side is a_c³ times the multiplier difference, exactly the dimensionless quantity in (G.68).

The loss from a to aθ is explicit. If the available complex action exponent is a=5(1−ε₀)/16, then θ=7/8 gives aθ=35(1−ε₀)/128, strictly larger than (1−ε₀)/4. There is therefore room for polynomial factors before reaching the geometric rate used in (LF). This conclusion requires (G.71) with that exponent on the actual disc (G.72); citing a whole-action bound at one data point does not supply it.

### 15.4 Different Data and the Double-Bar Multiplier

For two different data D_A and D_B, split

$$
\lambda_B(D_B)-\lambda_A(D_A)
=[\lambda_B(D_B)-\lambda_B(D_A)]
 +[\lambda_B(D_A)-\lambda_A(D_A)]\;.
\tag{G.78}
$$

The second bracket is (G.77). The first is the ordinary response of one minimiser to its data. It can be represented by the data derivative of its current and the inverse constraint map, or by a second data derivative of S_B. Its required local estimate is

$$
a_c^3|\lambda_B(D_B)-\lambda_B(D_A)|
\leq C\sum_{c'}e^{-\delta_1d(c,c')}|\delta D(c')|\;,
\tag{G.79}
$$

with the data weights in the kernel convention of VAR (190). The actual values of \(\delta D(c')\) are the data differences propagated through U₀ in LF §4(c). The derivative estimate must include the inverse constraint map with its local bounds; (190) for the phase alone is not a complete proof of (G.79).

Finally, the LF note relates the double-bar multiplier to the plain one by \(\nu=(1-\Xi)^*\lambda\), with the interface twist Ξ. Its difference is

$$
\nu_B-\nu_A
=(1-\Xi_B)^*(\lambda_B-\lambda_A)
 +(\Xi_A-\Xi_B)^*\lambda_A\;.
\tag{G.80}
$$

The twist is a local function of the shared block data, as in §14. Thus its already-written first-order difference and the bounds (G.77)–(G.79) would supply the multiplier estimate needed in (G.67). This comparison permits genuinely different layer data; it does not assume they are related by a gauge transformation.

**Status.** The envelope identity and the interpolation estimate (G.74)–(G.77) are explicit. Applying them to LF-A(6) requires verifying the local weighted action-depth input on the complex data disc, the layer separation for the specific determining sets, and (G.79). These are now the precise inputs for this multiplier route. No conclusion is drawn from an unlocalised total-action bound.

Sources: LF §4(b)–(c), *The weighted defect*, *The propagation*, and *The complex class*; [VAR pp.308](../Balaban/tex/VAR/parts/p308_corrected.tex)–[309](../Balaban/tex/VAR/parts/p309_corrected.tex); [PRT2 p.231](../Balaban/tex/PRT2/parts/p231_corrected.tex).

## 16. Active Probabilistic Attempt: Mark the Composed History Integral

The user redirected the work to the probabilistic estimate. Sections 13–15 remain supporting attempts; they are not counted as a proof of that estimate. The active operand is now the complete normalised component integral, with all preliminary integrations, explicit retained fields and the numerator/denominator distinction preserved.

### 16.1 Unwind the Intermediate Boundary Logarithms

LFR I p.179 performs, in order, the integrations of \(\mathbf T^{(j)}\) over \(Z_{j+1}\setminus Z''_{j+1}\), for j=h,…,k−1. At each stage (1.60) is an exact representation of that integration, and (1.62) expresses the result through a new boundary logarithm and an extracted Wilson coupling term. These new terms encode integrals already performed; they are not additional independent factors of the original joint integrand.

For a fixed admissible labelled history H, write its preliminary integrations in the original physical variables as

$$
N_H^X[O]
=\int O^X(u)\,I_H^X(u)\,d\nu_H(u),
\qquad X=A,B\;.
\tag{G.81}
$$

Here u includes **all** the V_j and A_j variables actually integrated in that history, dν_H is the common product of their Haar and Lebesgue measures after removal of the same gauge constraints, and I_H^X includes the remaining conditional quadratic forms, actions, cutoffs, Jacobians and scalar normalisations. A common measure is used only for the young matched histories whose retained variables occur at shared physical scales. All changes of variables must include their Jacobians. No product-law assumption for the interacting density I_H^X is made.

For intermediate kernels K_r, the identity underlying this representation is

$$
\mu_r(u_{>r})=\int K_r(u_r,u_{>r})\mu_{r-1}(u_r,u_{>r})\,d\nu_r(u_r)\;.
\tag{G.82}
$$

Substituting (G.82) successively gives the joint integral (G.81). The decomposition of log μ_r into a reference action and the terms \(\mathbb C_k^{(q)}\) cancels on substitution. In particular, it is incorrect to insert both the primitive density variation and independent variations of all these generated logarithms into the same joint integral: that would count one change more than once.

For an interpolation of nonzero smooth density factors, differentiation therefore gives

$$
\frac{d}{dt}N_{H,t}[O]
=\int\left(\dot O_t+O_t\left[\partial_t\log\mu_{0,t}
+\sum_r\partial_t\log K_{r,t}\right]\right)
I_{H,t}\,d\nu_H\;.
\tag{G.83}
$$

Equation (G.83) is used at the unnormalised level. It does not divide by an intermediate integral that might be small or vanish at complex data. Cutoff changes are telescoped as differences of cutoff factors and estimated by their shell majorants; their logarithms are never taken. The extracted coupling terms of (1.62) must be returned to the reference action when deriving (G.83), so their change is counted exactly once in the original action coefficient.

This removes the need to estimate the feedback of every generated \(\mathbb C_k^{(q)}\) separately **inside a completed component integral**. It does not remove the need to estimate the primitive marked kernels or the inherited boundary input already present before the preliminary integrations.

### 16.2 A Marked Quotient Bound With the History Reserve

Let d_H^X be the actual local renormalisation denominator of LFR II (1.1), and put q_H^X=N_H^X[1]/d_H^X. Keep the following three inputs explicit:

1. On common cutoff support, the smooth density ratio is \(I_H^B=I_H^Ae^{D_H}\), with \(|D_H|\leq s_HP_H\).
2. The denominator has a specified analytic logarithm and \(|\log d_H^B-\log d_H^A|\leq t_HP_H\).
3. Each run's absolute numerator divided by its denominator obeys a history-resolved majorant

$$
M_H^X:=\frac{\int|I_H^X|\,d\nu_H}{|d_H^X|}
\leq e^{-c_PP_H}\,\overline q_H,
\qquad
P_H=\sum_mL^d|Z_m\cap H|_m\;.
\tag{G.84}
$$

The history reserve in (G.84) is the one to be supplied by the Cauchy note's (11.2) and (11.4), after paying the ordinary history cost. It is not an extra copy of a birth factor. Its validity must be retained separately for each component classification and for every marked hybrid majorant used for a cutoff shell.

First freeze the cutoffs. Set u_H=s_H+t_H. Directly from the quotient identity,

$$
|q_H^B-q_H^A|
\leq (e^{u_HP_H}-1)M_H^A\;.
\tag{G.85}
$$

If u_H≤c_P/2, then

$$
(e^{u_HP_H}-1)e^{-c_PP_H}
\leq u_HP_He^{-(c_P-u_H)P_H}
\leq\frac{2u_H}{e c_P}\;.
\tag{G.86}
$$

If u_H>c_P/2, use both endpoint majorants instead:

$$
|q_H^B-q_H^A|\leq M_H^A+M_H^B
\leq 2\overline q_H
\leq\frac{4u_H}{c_P}\overline q_H\;.
$$

Consequently the smooth part satisfies, without an a priori smallness assumption on u_H,

$$
|q_H^B-q_H^A|
\leq\frac{4}{c_P}(s_H+t_H)\overline q_H\;.
\tag{G.87}
$$

For the shell terms, use the telescoping product of the cutoff differences. If the sum of their absolute marked integrals is bounded by \(v_HP_He^{-c_PP_H}\overline q_H\), then their contribution is at most \(v_H\overline q_H/(e c_P)\), with the appropriate denominator comparison kept in v_H or treated by the same two-case split. No normalised probability conditional on an exceptionally rare history is inserted in this estimate.

The number of integrations N and the number of bonds on the history have disappeared from the prefactor because the mark count is paid by the retained reserve. This is an integrated estimate for the component quotient, not a pointwise bound for each intermediate boundary logarithm.

### 16.3 From One Marked Component to the Connected Polymer

In LFR II (1.91), apply the quotient estimate to the component operator **with its actual test factor present**. At fixed common test factor O, a density-ratio bound in (G.85) remains valid after multiplication by |O| and use of the corresponding absolute majorant. The derivative of the product of component operations is then a sum with one component marked. Marks on V(Y), or on their exponentials in the Mayer representation, are additional terms and remain part of the comparison.

For a polymer with q components, a uniform mark size u gives at most q times its unmarked component majorant. The reserve after (1.93) is \(e^{-3qp_0(g_k)/2}\), before the sum in (1.96). There is a direct payment for the mark count:

$$
q e^{-\frac32qp_0}
=\bigl(qe^{-\frac12qp_0}\bigr)e^{-qp_0}
\leq\frac{2}{e p_0}e^{-qp_0}\;.
\tag{G.88}
$$

However, the same half-p₀ factor is used by the unmarked summation (1.96). To avoid spending it twice, either retain the mark inside that summation and differentiate it, or allocate two smaller fixed portions before the sum. With an allocation of p₀/4 to the mark count and p₀/4 to the component count, the total p₀/2 used is unchanged. The entropy condition must then be checked with the latter rate; small coupling supplies the corresponding exponential smallness. The remaining spatial factor in (1.93) continues to control the geometry. The connected exponentiation is performed after this rooted component sum, with the actual vacuum normaliser cancelled as in (G.45).

This yields a marked connected-activity estimate from primitive marked component and V(Y) estimates, with explicit costs for both marks and unmarked entropy. It does not bound V(Y)^B−V(Y)^A by itself.

### 16.4 Exact Scope of the Reorganisation

There are two limits to this approach that must not be hidden.

- **Changed test factors under unwinding.** If a test O is expressed in the final fluctuation coordinates, unwinding the two runs' changes of variables generally produces O^A and O^B, not one common function of the original physical variables. The difference O^B−O^A is a separate mark in (G.83). For the test factors V(Y) of (1.91), that is part of LF-A(7); for a Wilson loop insertion it is part of LF-W. Comparing the original densities alone is insufficient for these operators.
- **Components whose preliminary integrations stop.** LFR I p.191 leaves their generated boundary terms in the action when a new large field ends the preliminary integration. The completed quotient argument cannot simply be assigned to those carried terms. They must retain their originating component and its remaining weight until a later integration or the final expectation. In particular, a second-class component's reserve cannot be discarded and then reused to pay for a new mark. A rooted-history expansion with that association is still needed for this part.

The immediate probabilistic task is therefore to establish (G.84) with one primitive scalar mark and the actual test factor, including the stopped components, and to identify s_H, t_H and v_H in the caller's norms. Equations (G.81)–(G.88) remove spurious intermediate-logarithm feedback from the completed quotient and state exactly which marks remain. They are not a proof of the full Cauchy estimate.

Sources: [LFR I pp.179](../Balaban/tex/LFR1/parts/p179_corrected.tex), [189](../Balaban/tex/LFR1/parts/p189_corrected.tex), [191](../Balaban/tex/LFR1/parts/p191_corrected.tex); [LFR II pp.356](../Balaban/tex/LFR2/parts/p356_corrected.tex), [378](../Balaban/tex/LFR2/parts/p378_corrected.tex), [388](../Balaban/tex/LFR2/parts/p388_corrected.tex), [389](../Balaban/tex/LFR2/parts/p389_corrected.tex), [390](../Balaban/tex/LFR2/parts/p390_corrected.tex); Cauchy §8.6 and (11.2)–(11.4).

## 17. The Marked Component Sum in LFR II (1.91)–(1.99)

This section estimates the actual component and interaction marks after their primitive integral bounds have been supplied. The small primitive difference is denoted by u. Its derivation remains separate; the calculation here proves that the component count, spatial sum and exponentiation do not introduce a factor growing with the number of RG steps or the volume.

### 17.1 One Marked Renormalised Component

Fix the final polymer X′ and the second-class components Y_i that it contains. Put

$$
V=\left|X'\setminus\bigcup_iY_i\right|,
\qquad
c=\frac{\beta\kappa}{6\cdot2^d}M^{-d},
\qquad
\lambda=100^d(MR_k)^{-d}e^{-p_0(g_k)/2}\;.
\tag{G.89}
$$

These are the volume, the negative volume coefficient in (1.95), and the component-count coefficient in (1.96). After the geometric estimates (1.93)–(1.95), each renormalised component has a factor \(e^{-3p_0(g_k)/2}\). Assume its marked integral, **with the test factor of (1.91)**, is bounded by u times the same majorant. Telescoping q such component factors gives a multiplier qu.

For the part with q≥1, extract one factor e^{-p₀(g_k)}. The remaining component sum is bounded exactly as in (1.96), with the additional q. For λ≤c/2,

$$
\begin{aligned}
\sum_{q\geq1}q\,\frac{(\lambda V)^q}{q!}
&=\lambda V e^{\lambda V},\\
e^{-cV}\lambda V e^{\lambda V}
&\leq \frac{\lambda}{e(c-\lambda)}
\leq\frac{2\lambda}{ec}\;.
\end{aligned}
\tag{G.90}
$$

Thus the marked-component contribution obeys

$$
|\Delta_{\mathrm{comp}}F(X')|
\leq C\,u\,e^{-p_0(g_k)}
e^{-(1+\beta)\kappa d_{k,\cup Y_i}(X')}\;.
\tag{G.91}
$$

The ratio λ/c is bounded by a constant times \(R_k^{-d}e^{-p_0(g_k)/2}/(\beta\kappa)\); M^{-d} cancels. Hence the constant in (G.91) is uniform in k, the fine cutoff and the volume. The condition λ≤c/2 is a fixed strengthening of the small-coupling inequality already used after (1.96).

This calculation is preferable to bounding q separately by an exponential and then spending the same reserve on (1.96). The derivative of the component sum retains the combinatorial factorial and the volume suppression together. A mark on an external second-class factor is not one of these q marks; it remains attached to that factor and must retain its own history reserve.

### 17.2 One Marked V(Y)

At fixed component operators, differentiation of the integrand in (1.91) gives two kinds of terms:

$$
\begin{aligned}
\Delta\left(\prod_{Y\in\mathbf D}V(Y)\right),
\qquad
\left(\prod_{Y\in\mathbf D}V(Y)\right)
\sum_{Y\in\mathbf D}t(Y)\Delta V(Y)\;.
\end{aligned}
\tag{G.92}
$$

The first expression is telescoped without dividing by V(Y). Suppose \(|\Delta V(Y)|\leq u a_Y\), where a_Y is the same absolute majorant used for that factor in (1.92). Then the marks in the product and exponent are bounded by

$$
u\left(|\mathbf D|+\sum_{Y\in\mathbf D}a_Y\right)
\prod_{Y\in\mathbf D}a_Y
\exp\left(\sum_{Y\in\mathbf D}a_Y\right)\;.
\tag{G.93}
$$

The geometric extraction (1.93) is applied before summing these factors. Its remaining positive vertex weights are \(\alpha^{2/3}e^{-\beta\kappa d_{k,Z'}(Y)/2}\). To justify the marked count, expand the last exponential in (G.93) as well and put a parameter ζ on every V-occurrence. Every absolute coefficient is then nonnegative. For a term with N occurrences, N≤2^N−1, so the marked sum is bounded by the positive generating sum at ζ=2 with its zero-vertex term removed. Apply the proof of (1.94) to these doubled weights, not a derivative of an inequality known only at ζ=1. The unrestricted nonempty-family sum is at most \(e^{CaV}-1\leq CaV e^{CaV}\), with a≤C′α^{1/3}M^{-d}. This proves the asserted marked volume factor. The exponent mark in (G.93) is included in this N because it is an occurrence in the expanded exponential. When the original family has no empty term and its c₀=α^{1/3} is needed, retain its distinguished nonempty vertex in the doubled-weight proof of (1.94); this yields the boundary-sector factor c₀ instead of inferring it by subtraction.

Reserve enough of the coefficient c in (G.89) that the total positive coefficient from the unmarked component sum and the two vertex sums is at most c/2. This is possible by the original choices α small, κ large and g_k small. The marked volume factor is then paid by

$$
aV e^{-cV/2}\leq \frac{2a}{ec}\;.
\tag{G.94}
$$

For polymers disjoint from the second-class components, q≥1 and the extracted e^{-p₀(g_k)} remains. Therefore

$$
|\Delta_VF(X')|
\leq C\,u\,e^{-p_0(g_k)}
e^{-(1+\beta)\kappa d_k(X')}\;.
\tag{G.95}
$$

For polymers meeting second-class components, the source uses the α^{1/3} alternative for c₁ in (1.97). Their marked bound has that boundary-sector weight instead of automatically acquiring e^{-p₀}. The estimates of V(Y) wholly contained in a component, governed by (1.69), belong inside the component integral; they are not assigned the small α-weight of (1.68).

### 17.3 Connected Exponentiation

The exponentiated series (1.98)–(1.99) is absolutely convergent with the spatial margin between (1+β)κ and κ. A difference of that series is obtained by marking one polymer activity. The rooted connected-cluster estimate of §12.1 applies to this mark. The same tree-length extraction that gives (1.99) then gives, in the R-sector disjoint from the surviving large-field region,

$$
|\Delta\mathbf R^{(k)}(X)|
\leq C_{\mathrm{cl}}u\,e^{-p_0(g_k)}e^{-\kappa d_k(X)}\;.
\tag{G.96}
$$

Here u is the sum of the component-mark bound in (G.87), the interaction-mark bound used in (G.93), and any separately identified transported-observable marks. The proof is linear in each of these sources. For the boundary sector, the bound retains the appropriate c₁ and relative distance of (1.99); (G.96) must not be extended to that sector by dropping its second-class components.

The normalisation is the one in the exponentiated component expansion, and later the physical expectation uses the connected numerator/denominator cancellation. No product law for the fields inside a component has been used. The prefactor e^{-p₀(g_k)} is the large-field probability gain already paid for by Bałaban's component integrals.

**Remaining verification.** Equations (G.90) and (G.94) make the combinatorial payments explicit. The application of (1.94) with a marked V(Y) must retain the same rooted geometric counting and its exceptional c₀=α^{1/3} case. The primitive marked integrals and the comparison of V(Y) on the required common complex domains remain the substantive inputs to (G.96); this section does not assume they are already proved. It also does not solve the carried second-class boundary sector, which is the next probabilistic case to treat.

Sources: [LFR II pp.388](../Balaban/tex/LFR2/parts/p388_corrected.tex)–[389](../Balaban/tex/LFR2/parts/p389_corrected.tex), [p.390](../Balaban/tex/LFR2/parts/p390_corrected.tex).

## 18. Stopped Components: Carry an Unnormalised Mark

The second-class factors are outside the first-class polymer sum in LFR II (1.72). They include \(\chi_k^c(Y_i^{\sim-6})\), the remaining cutoffs and gauge constraints, and the operator \(\mathbf T'_k(Y_i)\). A mark on one of these factors must remain attached to that operator. Passing immediately to the logarithm of a conditional probability discards precisely the small mass that the estimate needs.

### 18.1 Mass and Conditional Law

When (1.73)–(1.75) applies to a component, write its complex integration kernel as K_X=w_XP_X, with w_X=K_X1 and P_X1=1. The source proves \(w_X\neq0\) and \(\|P_X\|\leq C_\sigma\), where \(C_\sigma=e^{3\sup|\sigma|}\). This norm is the total variation norm of the linear functional, with fixed external data. For two kernels on the same integration space,

$$
|w_B-w_A|\leq\|K_B-K_A\|,
\qquad
\min(|w_A|,|w_B|)\|P_B-P_A\|
\leq(1+C_\sigma)\|K_B-K_A\|\;.
\tag{G.97}
$$

To prove the second inequality, if |w_B|≤|w_A|, use

$$
w_B(P_B-P_A)=(K_B-K_A)-(w_B-w_A)P_A\;.
$$

For the opposite ordering use the same identity with A and B interchanged. No lower bound on the rare component mass enters. The physical mark is the difference of **unnormalised** kernels; its conditional-law part is always multiplied by a component mass.

The norm estimate (G.97) alone is not applied repeatedly to every internal integration. That would create powers of C_σ. Instead, retain the composed kernel and use the product rule at its primitive factors, as follows.

### 18.2 The Kernel Induction

Let K_r^A,K_r^B be the actual kernels of a matched sequence of retained integrations, including their scalar normalisations. Their order is the order of the integrations. Choose positive test envelopes W_r from the unmarked majorant construction. They are allowed to contain the factors needed by the later Mayer integrand; a bound for the test 1 alone is insufficient. Suppose the absolute kernels obey

$$
\overline K_r^X W_r\leq A_rW_{r-1},
\qquad
\overline{K_r^B-K_r^A}\,W_r
\leq u_rp_rA_rW_{r-1}\;,
\tag{G.98}
$$

for both runs and the hybrids required by telescoping. The number p_r counts the scale-r history points assigned to that primitive kernel. The factors A_r are the **actual** costs and gains of the unmarked bound; they are not assumed to be ≤1. A cutoff-shell difference is an additional signed kernel satisfying its own version of the second inequality.

The exact ordered telescoping identity yields

$$
\left\|K_1^B\cdots K_N^B-K_1^A\cdots K_N^A\right\|_{W_N\to W_0}
\leq\left(\sum_{r=1}^{N}u_rp_r\right)\prod_{r=1}^{N}A_r\;.
\tag{G.99}
$$

The notation means the smallest constant C such that the absolute action on W_N is bounded by CW₀. Its proof is the ordered product rule followed by (G.98), one marked factor at a time. Conditional correlations are inside K_r, and no independence of the retained fields is used.

If a component stops after r steps, (G.99) is simply retained for that prefix. At a later integration its signed prefix kernel is composed with the next unmarked kernel, and a new primitive difference gives one further term. One does not add the differences of the intermediate \(\mathbb C_k^{(q)}\) on top of this representation. Those logarithms are an alternative encoding of the same kernel.

When components merge, the marked product is

$$
\dot K_{H_1\cup H_2}
=\dot K_{H_1}K_{H_2}+K_{H_1}\dot K_{H_2}
+\text{the mark of the new joining operation}\;.
\tag{G.100}
$$

This adds mark counts. It does not multiply them. The old histories are disjoint before the merge; the new joining cost is assigned once. If P_H=Σ_rp_r and u_r≤u, a terminal history majorant of the form

$$
\prod_rA_r\leq e^{-c_PP_H}\overline A_H
$$

gives

$$
\left\|\dot K_H\right\|
\leq uP_He^{-c_PP_H}\overline A_H
\leq\frac{u}{ec_P}\overline A_H\;.
\tag{G.101}
$$

The suppression is used at the terminal evaluation of the marked history, not once for each prefix. A second-class re-entry does not erase the accumulated signed kernel. Any update of the unmarked exponent has to be the literal update of the source's history factor, with the remaining reserve recorded there. Equations (G.99)–(G.101) do not grant a new birth factor on re-entry.

### 18.3 What Must Be Proved for the Actual Kernels

This is the measure-valued induction appropriate to the carried second-class terms. To use it, (G.98) must be verified for the primitive kernels and the actual future test envelopes. In particular:

- A retained A_j is part of the kernel state until its integration; its dependent marks are not dropped or relabelled as fixed spectators.
- A change of reconstruction coordinates changes the pulled-back test function as well as the density. That test-function mark remains present.
- A stopped component is not assumed to satisfy the completed R-operator normalisation (1.75). Its prefix kernel can be carried by (G.98) without division by K_H1.
- The history inequality used in (G.101) must hold with the true costs, including complex extensions and the later interaction envelopes. The modified exponent identity of Cauchy (11.4) is the proposed source of this reserve; it must cover the stopped and second-class branches, not only first-class components.

These conditions specify the remaining probabilistic estimate rather than replace it by an individual bound on each generated boundary logarithm. The next mark to evaluate is the primitive insertion coming from the explicit A_j-dependent part of (G.39), under the conditional kernel with the correct future envelope. Section 12.2 treats its explicit quadratic vertices; the full nonquadratic part remains to be derived from the construction.

Sources: [LFR I p.191](../Balaban/tex/LFR1/parts/p191_corrected.tex); [LFR II pp.378](../Balaban/tex/LFR2/parts/p378_corrected.tex)–[380](../Balaban/tex/LFR2/parts/p380_corrected.tex), [p.384](../Balaban/tex/LFR2/parts/p384_corrected.tex); Cauchy (11.2)–(11.4).

## 19. Review Correction: Localised Boundary Pieces Cannot Be Unwound Separately

The [probabilistic review](verification/isolated_reviewer/reviews/lf-gamma-marked-history-20261028-r1/review.txt) checked the quotient arithmetic, q-weighted component sum, positive doubled-weight counting and the structure of the connected exponentiation. Its [manifest](verification/isolated_reviewer/reviews/lf-gamma-marked-history-20261028-r1/manifest.json) records one request and no gateway errors or tool events.

It identified a substantive gap in the application of §16. The exact unwinding there concerns an entire preliminary logarithm. LFR II redistributes its localised pieces between V(X^∼), which is inside \(\mathbf T'_k(X)\), and V(Y) with Y∖Z^∼≠∅, which is outside that operator and enters the Mayer expansion. The exponential of a partial sum of these pieces is not the original preliminary integral. Therefore §16 does not justify removing the creation estimate for the actual localised caller. The use of (G.87) for that caller remains conditional on an explicit representation and cannot be inferred from (G.82) alone.

Other objections also remain: the complex majorant for a fully unwound nested integral is not supplied by (1.73) alone; the density equivalence after reversed gauge fixing is not pointwise equality against arbitrary test factors; all cutoff hybrids need their own bound; and the history reserve must be allocated before, rather than after, the entropy estimate. The source's numerator–denominator Wilson cancellation must be kept inside the primitive mark if its two pieces are individually large.

The following attempt consequently uses the existing localised connected expansions. It neither moves V(Y) into a component where it was not integrated nor counts the same boundary contribution in both representations.

## 20. Substitute the Marked Inner Cluster Into the Outer Expansion

### 20.1 The Localised Identity

Write the creation formula (1.63) with its connected expansion still visible:

$$
\mathbb C_k^{(r)}(X)
=\sum_{\Gamma:\,\operatorname{loc}(\Gamma)=X}c_r(\Gamma)
+\mathbb A_r(X)\;.
\tag{G.102}
$$

The graph Γ is a connected cluster of the preliminary integral (1.60), with all its conditional integration variables and normalisation factors. The term \(\mathbb A_r\) denotes the explicitly localised coupling correction from (1.62). This is not a representation of \(e^{\mathbb C_k^{(r)}(X)}\) as a separate integral. Differentiating the connected series puts one primitive mark in Γ, and differentiates \(\mathbb A_r\) once.

For the boundary inputs, the localisation and resummation into V(Y) are linear in the input term: LFR II p.376 sums the terms with fixed final domain, first over the expansion domains, then over the original domain and generation. Denote this linear map at fixed reconstruction data by \(\mathcal L(Y;r,X)\). The contribution from newly created boundary terms is

$$
V_{\mathbb B''}(Y)
=\sum_{r,X}\mathcal L(Y;r,X)\mathbb C_k^{(r)}(X)\;.
\tag{G.103}
$$

The two-run difference has the exact split

$$
\begin{aligned}
\Delta V_{\mathbb B''}(Y)
={}&\sum_{r,X}\mathcal L_A(Y;r,X)\Delta\mathbb C_k^{(r)}(X)\\
&+\sum_{r,X}(\mathcal L_B-\mathcal L_A)(Y;r,X)\mathbb C_{k,B}^{(r)}(X)\;.
\end{aligned}
\tag{G.104}
$$

The second line is the genuine change of reconstruction/localisation and remains among the primitive sources of LF-A(7). In the first line, insert the **marked connected series** from (G.102), including the coupling mark. Classifying the resulting terms according to whether Y is a component of Z^∼ or extends outside it gives the original V(X^∼)/V(Y) split. No term is present twice, and no part of an inner logarithm is replaced by an unnormalised integral.

Every inner cluster contributing to (1.63) has a domain meeting the integration region \(Z_{j+1}\setminus Z''_{j+1}\). Keep that occurrence as its origin label. When the cluster is inserted in (G.103) or in an outer connected cluster, its origin remains part of the marked graph. Absolute bounds are taken only after the relevant normalised connected series has been formed.

### 20.2 A Bounded-Source Estimate, Without a Spurious Contraction Claim

For a scalar input difference F, the full mark in (1.60) is

$$
I_F=F(U(B_j),A_j)-F(U(0),0)\;.
$$

If F is bounded by f_X on the actual admissible background and retained-field domain, then \(|I_F|\leq2f_X\). This includes the explicit A_j part. No gain δ′_j/ε_j is claimed for it.

Introduce a source parameter z multiplying I_F in the actual integral. For |z|f_X≤a_*, with a_* a fixed small activity size, the new Mayer vertex satisfies

$$
|e^{zI_F}-1|\leq 2e^{2a_*}|z|f_X\;.
\tag{G.105}
$$

If the original activity norm is inside the convergence region with fixed slack, this additional vertex is admissible. Differentiating the connected expansion at z=0 gives a bound linear in f_X, with a constant determined by that slack and the localisation count. The insertion is evaluated at the same real A_j,B_j integration variables as the original integral. Analyticity is needed in the background and in the localisation parameters used by that expansion; this argument does not assume holomorphy in A_j outside its integration domain.

For a precise local norm, take the supremum on those actual domains and sum over localised activities through a fixed determining cube, with the spatial tree weight that is retained for the output. The input must have the additional decay reserved by the unmarked construction for this localisation and cluster sum. In that norm the proposed response bound is

$$
\|D\mathcal C_r[F]\|_{\kappa,\mathrm{out}}
\leq L_r\|F\|_{\kappa+\delta\kappa,\mathrm{in}}\;.
\tag{G.106}
$$

The constants and domain transfer in (G.106) must be extracted from the **mixed-domain** preliminary expansion. Equation (G.105) and the rooted estimate (G.47) justify a bounded source at the graph level; they do not by themselves prove this norm transfer. In particular, a fixed decay loss cannot be repeated N times without accounting for it.

The relevant improvement over the earlier recursion is that L_r need not be less than one. A marked input in a large-field history can be carried with its component's remaining suppression. This is a different conclusion from contraction of the unweighted boundary-potential norm.

### 20.3 Charge Amplification to the History, Once

Suppose the marked inner and outer cluster bounds, in compatible norms, give a multiplicative constant L_r at the r-th integration. For a marked lineage with history point counts p_r≥1 at its active stages,

$$
\prod_r\max(1,L_r)
=\exp\left(\sum_r\log\max(1,L_r)\right)\;.
\tag{G.107}
$$

If L_r is uniformly bounded, this is a fixed exponential cost in history volume, since the number of active stages is at most Σ_rp_r. If L_r is bounded by a fixed power of log g_r^{-2}, its logarithm is of order log log g_r^{-2}, and is bounded by a fixed multiple of \(1+\log g_r^{-2}\), the type of cost already present in LFR II p.380. If instead L_r already contains exp(c p_r), as in (G.163), its logarithm is charged directly; multiplying it by p_r again would create an unnecessary quadratic volume cost. The required reserve is

$$
\text{ordinary history cost}
+\sum_r\log\max(1,L_r)
+c_{\rm mark}P_H
\leq\text{allocated birth gains and propagation reserve}\;.
\tag{G.108}
$$

The last term pays the sum over positions of the primitive mark, as in (G.101). It is not spent at every prefix. A successful component exits to the first-class R-expansion and uses its terminal component factor in (1.93)–(1.96). A component still present at the stopping scale instead uses the pattern-count bound. These are alternative terminal uses of a history, not factors to multiply together. No post-entropy component majorant is fed back into (1.93).

The modified cost in (G.108) has the same logarithmic type as the λ_r cost in Cauchy (11.4), provided the growth of L_r asserted above is actually proved. The parameters in that history inequality would have to be chosen with this cost included. This is not permission to reuse a quarter of p₀ after it has already paid for another part of the same expansion.

### 20.4 Remaining Hard Estimate

The unresolved analytic task in this route is now (G.106), with its explicit mixed-domain weights, and the verification of (G.108) on stopped and second-class histories. The mark contains all of F(U(B_j),A_j)−F(U(0),0), so the A_j omission is removed. The localised identity (G.104) keeps the true V(X^∼)/V(Y) accounting. The reconstruction-change mark in its second line remains LF-A(7), and must be estimated or cancelled in the full normalised expansion; it is not set to zero by this reorganisation.

Sources: [LFR I pp.188](../Balaban/tex/LFR1/parts/p188_corrected.tex)–[192](../Balaban/tex/LFR1/parts/p192_corrected.tex), [LFR II pp.376](../Balaban/tex/LFR2/parts/p376_corrected.tex)–[377](../Balaban/tex/LFR2/parts/p377_corrected.tex), [379](../Balaban/tex/LFR2/parts/p379_corrected.tex)–[380](../Balaban/tex/LFR2/parts/p380_corrected.tex), [388](../Balaban/tex/LFR2/parts/p388_corrected.tex)–[390](../Balaban/tex/LFR2/parts/p390_corrected.tex).

## 21. Conditional Clusters With Their Active Integration Supports

The source variables of a conditional cluster must be distinguished from its background dependence. This distinction is useful for (G.106), because the latter may extend outside the component while only the former are integrated at the current preliminary step.

### 21.1 Exact Conditional Factorisation

Fix all exterior variables v. Suppose the localised conditional representation is written over a product reference measure in variables ξ_i, i∈D, as in the auxiliary Gaussian representation of RG II (2.6). A local factor is labelled by α and has two supports:

- P_α⊂D, the variables ξ on which it depends;
- Y_α, its full spatial localisation domain, including dependence on v.

The fields ξ are the auxiliary product-Gaussian variables of that representation. They are not the original interacting A_j,B_j fields, and no independence of the latter is assumed. A covariance joining two integration regions must occur in a factor whose active support includes both regions, or in the chain of localised factors representing it.

For fixed v, two products of factors with disjoint active supports are independent under this reference product integral even if their Y-supports overlap in exterior variables. Group the Mayer factors into components under overlap of the P-supports. The conditional integral then factorises over those components, and the resulting polymer gas uses incompatibility of active supports. Keep the full Y-support as a label on every activity; it is still needed for locality and for later integrations of the exterior fields.

This follows directly from the product reference measure: each connected component uses a disjoint subset of the ξ_i, so Fubini factors its integral. There is no averaging over the shared exterior parameters in this step. When those parameters are integrated later, the factors may interact and the later expansion has to retain that dependence.

Factors with P_α=∅ are functions of v alone and factor out of the conditional integral. They belong to the frozen exterior action, not to a newly generated fluctuation response. For a subtraction F(U(B_j),A_j)−F(U(0),0), the part independent of every active variable cancels. Its nonzero localised terms therefore have an active root.

### 21.2 The Root Count

Write K(P,Y;v) for an unmarked conditional polymer activity and H_I(P₀,Y₀;v) for one with the scalar insertion I. Choose a spatial tree rate κ_* and suppose the weighted unmarked activities satisfy

$$
\sup_{i\in D}
\sum_{(P,Y):\,i\in P}
\sup_v|K(P,Y;v)|\,\mathsf w_{\kappa_*}(Y)
e^{a|P|}
\leq a\;.
\tag{G.109}
$$

The weight \(\mathsf w_{\kappa_*}\) is chosen with the usual tree submultiplicativity for domains joined through an active point. Fixed joining constants are included in the vertex majorant. One may use the source's linear-size weight with the corresponding fixed geometric constant; it is not legitimate to omit that constant when two cubes touch only along a boundary.

For a root with active support P₀, the sum over activities incompatible with it is at most a|P₀|: sum (G.109) over i∈P₀. The rooted-tree iteration used in (G.46) therefore gives

$$
\sum_{\Gamma\text{ attached to }(P_0,Y_0)}
|\text{weight of }\Gamma|\,\mathsf w_{\kappa_*}(Y_\Gamma)
\leq
\sup_v|H_I(P_0,Y_0;v)|\,\mathsf w_{\kappa_*}(Y_0)
e^{a|P_0|}\;.
\tag{G.110}
$$

Unlike a count by the whole background domain Y₀, the exponential cost is in the active support P₀. The spatial weight of the root is retained on both sides. This is the point at which the actual conditional integration support matters.

For the r-th preliminary integration, P₀ is contained in the A_j and B_j variables being integrated in that component. Their number is bounded by a fixed multiple of the scale-j history point count p_r. Thus

$$
e^{a|P_0|}\leq e^{C_a p_r}\;.
\tag{G.111}
$$

Multiplying these costs along a marked history gives e^{C_aP_H}, a cost of the form explicitly allowed in (G.108). It does not require a new spatial decay loss at every preliminary integration. A fixed constant C_loc from localisation of the primitive mark can also be paid this way, because each active stage has p_r≥1.

### 21.3 The Primitive Mark and the Actual Source Representation

For the full boundary subtraction I_F, the real integration-domain bound is |I_F|≤2f_X. To pass it to H_I, insert it in the primitive integrals before the conditional-Gaussian constructions. In the analogue of RG II (2.14), it remains a scalar factor inside the B-integral; the numerator and denominator factors outside that integral remain exactly those of the source. The analytic localisation in the background variables then attaches the walks of the reconstruction to the mark's domain. It does not change its active-variable status: a factor depending only on the exterior data is still not a random variable at this stage.

The needed quantitative input is

$$
\sum_{P_0,Y_0}
\sup_v|H_{I_F}(P_0,Y_0;v)|\,\mathsf w_{\kappa_*}(Y_0)
\leq C_{\rm loc}\|F\|_{\kappa_*,\rm input},
\tag{G.112}
$$

with the root location or active cube fixed as in the local norm. The same admissible complex background and localisation polydiscs as the one-run construction are required. This is **not** an assertion of holomorphy in all retained fluctuation variables. They remain real integration variables or fixed real spectators where the source treats them that way.

If (G.109) and (G.112) hold for the mixed-domain preliminary representation, then (G.110) proves the weighted form of (G.106), with C_loc e^{C_ap_r} in place of an unweighted constant L_r. The combined history estimate is then

$$
\|\text{marked connected history}\|
\leq C\left(\sum_r u_rp_r\right)
e^{C_aP_H}\,overline M_H\;.
\tag{G.113}
$$

The remaining large-field bound must supply \(\overline M_H\leq e^{-(C_a+c_{\rm mark})P_H}\overline q_H\), with its other costs paid separately. The final mark count is then paid by \(P_He^{-c_{\rm mark}P_H}\), exactly once. The resulting contribution is linear in the primitive marked inputs and uniform in the length of the preliminary history.

### 21.4 What Is New and What Still Needs a Source-Level Proof

The factorisation and rooted-tree inequalities above are proved for the conditional representation with labelled active supports. They show why a norm based only on the full spatial footprint can overcharge a boundary mark: exterior overlap need not create a connected conditional cluster. They also show how bounded, rather than contractive, responses can be sufficient once the mark stays attached to its large-field history.

The outstanding work is to construct that labelled representation for the full mixed A_j,B_j integral (1.60) and prove (G.109)–(G.112) from its actual covariance localisation, cutoffs, and boundary activities. In particular, the Gaussian auxiliary representation must be localised before assigning its active supports; declaring its unlocalised square-root covariance local would be false. The external fields must stay frozen during the factorisation, and all their later dependence must remain in Y. This is the current probabilistic gap in this route.

Sources: [RG II pp.12](../Balaban/tex/RG2/parts/p012_corrected.tex)–[16](../Balaban/tex/RG2/parts/p016_corrected.tex), [CRE pp.277](../Balaban/tex/CRE/parts/p277_corrected.tex)–[278](../Balaban/tex/CRE/parts/p278_corrected.tex), and [LFR I pp.188](../Balaban/tex/LFR1/parts/p188_corrected.tex)–[192](../Balaban/tex/LFR1/parts/p192_corrected.tex).

## 22. The Conditional Gaussian Integral With a Mark: A Root-Dimension Bound

This calculation treats the literal Gaussian structure of RG II (2.14)–(2.26). The factor created by conditional normalisation is retained. It proves the refinement suggested after (2.26): the Gaussian cost can be charged to the dimension of the root integration, rather than to every variable in the enlarged localisation domain.

### 22.1 The Finite-Dimensional Integral

Let B∈ℝⁿ be the conditioned root variables, X∈ℝᵐ the auxiliary product-Gaussian variables, and let C be a complex symmetric covariance. Write

$$
P=C^{-1}=P_R+iP_I,
\quad C=C_R+iC_I,
\quad \Gamma=\Gamma_R+i\Gamma_I\;.
$$

Assume P_R≥γI with γ>0. The covariance C_R is then positive definite. The complex Gaussian measure is normalised with the analytic square-root branch of det P. The Gaussian part of the source integral is

$$
\mathcal G[I]
=\int d\mu_0(X)\,
e^{-\frac12X^T\Gamma^TC\Gamma X}
\int d\mu_C(B)\,e^{-B^T\Gamma X}I(B,X)\;.
\tag{G.114}
$$

For I=1 the two exponentials cancel after the B integration, giving \(\mathcal G[1]=1\). The first exponential is the conditional normalisation from RG II (2.5); dropping it would change the integral and destroy the estimate below.

The unmarked potentials and large-field test used in (2.20)–(2.22) are bounded by a constant exponential e^b times \(e^{\alpha|B|^2/2}\), with 0≤α<γ. First use the bound on the mark on its actual cutoff support; only afterwards may cutoffs bounded by one be omitted. For an additional scalar mark bounded there by M_I, absolute values in (G.114) give

$$
\begin{aligned}
|\mathcal G[I e^{\alpha|B|^2/2}]|
\leq{}&M_I
\left(\frac{|\det P|}{\det(P_R-\alpha I)}\right)^{1/2}\\
&\times\int d\mu_0(X)
\exp\left(\frac12X^TS_\alpha X\right),\\
S_\alpha={}&\Gamma_R^T(P_R-\alpha I)^{-1}\Gamma_R
-\operatorname{Re}(\Gamma^TC\Gamma)\;.
\end{aligned}
\tag{G.115}
$$

The original scalar factor e^b multiplies the right side. It is kept as an ordinary activity cost, not lost in the normalisation.

### 22.2 The Exact Schur Cancellation

From PC=I, its imaginary and real parts give

$$
P_I=-P_RC_IC_R^{-1},
\qquad
P_R^{-1}=C_R+C_IC_R^{-1}C_I\;.
\tag{G.116}
$$

Consequently

$$
\begin{aligned}
S_0&=T^TT,\\
T&=C_R^{1/2}\Gamma_I+C_R^{-1/2}C_I\Gamma_R,\\
S_\alpha&=T^TT+
\Gamma_R^T\bigl[(P_R-\alpha I)^{-1}-P_R^{-1}\bigr]\Gamma_R\;.
\end{aligned}
\tag{G.117}
$$

In particular S_α is positive semidefinite and has rank at most 2n, however large m is. At a real covariance and real Γ, T=0. Thus the entire external-field quadratic cost comes from the complex perturbation and the explicitly retained positive quadratic allowance α.

Suppose

$$
\|T\|\leq\delta,
\quad\|\Gamma_R\|\leq G,
\quad\|P_R^{-1/2}P_IP_R^{-1/2}\|\leq\delta_P,
\quad\alpha\leq\gamma/2\;.
$$

Then

$$
0\leq S_\alpha,
\qquad
\|S_\alpha\|\leq
s:=\delta^2+\frac{2\alpha G^2}{\gamma^2}\;.
\tag{G.118}
$$

For s≤1/2, only the at most 2n nonzero eigenvalues contribute to the determinant, so

$$
\int d\mu_0(X)e^{X^TS_\alpha X/2}
=\det(I-S_\alpha)^{-1/2}
\leq e^{2ns}\;.
\tag{G.119}
$$

For the other determinant in (G.115), diagonalise the real symmetric matrix \(P_R^{-1/2}P_IP_R^{-1/2}\). This gives

$$
\left(\frac{|\det P|}{\det P_R}\right)^{1/2}
\leq e^{n\delta_P^2/4},
\qquad
\left(\frac{\det P_R}{\det(P_R-\alpha I)}\right)^{1/2}
\leq e^{n\alpha/\gamma}\;.
$$

Under all the displayed hypotheses, including s≤1/2, combining the estimates proves

$$
|\mathcal G[I e^{\alpha|B|^2/2}]|
\leq M_I\exp\left[n\left(\frac{\delta_P^2}{4}
+\frac{\alpha}{\gamma}+2s\right)\right]\;.
\tag{G.120}
$$

Again, multiply by e^b for the constant allowance in the potentials. This is an absolute integral bound in the complex background. It does not divide by the mass of a cutoff event and does not assume that the original interacting fields are independent.

### 22.3 Quadratic Marks and Large-Field Tests

The positive joint Gaussian used in (G.115), after completion, has

$$
X\sim N(0,(I-S_\alpha)^{-1}),
\qquad
B\mid X\sim N\bigl(-(P_R-\alpha I)^{-1}\Gamma_RX,
\,(P_R-\alpha I)^{-1}\bigr)\;.
$$

Its marginal B covariance obeys

$$
\|\operatorname{Cov}(B)\|
\leq \frac{2}{\gamma}+\frac{8G^2}{\gamma^2}
=:C_B\;.
\tag{G.121}
$$

For \(I_2(B)=\tfrac12\sum_{b,b'}\operatorname{tr}(B(b)K(b,b')B(b'))\), take \(C_{\mathfrak g}\geq\dim\mathfrak g\), absorbing the harmless factor 1/2. The scalar quadratic mark has the primitive absolute estimate

$$
|\mathcal G[I_2 e^{\alpha|B|^2/2}]|
\leq C_{\mathfrak g}C_B
\left(\sum_{b,b'}\|K(b,b')\|\right)
\exp\left[n\left(\frac{\delta_P^2}{4}
+\frac{\alpha}{\gamma}+2s\right)\right]\;.
\tag{G.122}
$$

This is the complex-background version of the pairwise marked moment used in §12.2. Spatial localisation and the sum over pairs still use the actual decay of K; the Gaussian step itself introduces neither m nor a power of the cutoff radius.

A large-field test on a set P of root bonds is treated as in RG II (2.22):

$$
\chi\bigl(|B(b)|\geq r\text{ for }b\in P\bigr)
\leq e^{-\zeta r^2|P|/2}e^{\zeta\|1_PB\|^2/2}\;.
\tag{G.123}
$$

Include the second factor in the positive quadratic allowance, increasing α by at most ζ, and choose ζ so that α+ζ≤γ/2 and (G.118), with that increased allowance, remains below 1/2. The first factor stays outside the integral. This produces the actual large-field gain for a marked collar term. For a union event at one of several bonds, sum the corresponding one-bond marked estimates rather than assuming independence.

### 22.4 Application to the Preliminary Integral

In (1.60), the Gaussian reference is the displayed product of the A_j and B_j quadratic integrals. Their interactions remain in the potential. One may apply the calculation to the direct-sum Gaussian space, or to the conditional Gaussian blocks in the source's localisation procedure. The dimension n counts the actual root variables being integrated, with Lie-algebra multiplicity; it is bounded by a fixed multiple of the scale-j history point count.

The source estimates (2.16)–(2.21) provide small complex perturbations and a small positive quadratic allowance. To use (G.120) on each localisation polydisc, one must translate them into the bounds on γ, G, δ, δ_P and α above. That translation uses the one-run covariance bounds, not a new comparison of fine-lattice operators. The cost is exponential in n and can therefore enter the history cost (G.108). It does not grow with the enlarged background localisation volume m.

This proves the finite-dimensional Gaussian part of the marked primitive estimate, including its conditional normalisation and its complex absolute majorant. The remaining steps for (G.112) are the localisation sums and their active-support labels, and the insertion's bound on the actual analytic background domains. The matrix estimate does not supply those bounds automatically.

Sources: [RG II pp.12](../Balaban/tex/RG2/parts/p012_corrected.tex)–[13](../Balaban/tex/RG2/parts/p013_corrected.tex), [15](../Balaban/tex/RG2/parts/p015_corrected.tex)–[17](../Balaban/tex/RG2/parts/p017_corrected.tex); [LFR I pp.188](../Balaban/tex/LFR1/parts/p188_corrected.tex)–[189](../Balaban/tex/LFR1/parts/p189_corrected.tex).

### 22.5 Instantiating the Bound From RG II (2.16)–(2.21)

The source already supplies enough control for an O(α₅n) version of (G.120), without separately deriving the sharper quadratic dependence on the imaginary parts. Put

$$
\epsilon_{\rm op}=C e^{-\delta_0M/3}+C(\alpha_0+\alpha_1)\;,
$$

the small coefficient in (2.16). The row and column sums of its exponential kernel are bounded uniformly. Thus the three source differences R₁,R₂,R₃ have operator norms at most C_opε_op. In the notation of §22.1, their meanings give bounds of the following form, with a=C_opε_op:

$$
\begin{aligned}
\|P_R-P_0\|&\leq a,\\
\|\Gamma_R-\Gamma_0\|&\leq a,\\
\|\operatorname{Re}(\Gamma^TC\Gamma)-\Gamma_0^TC_0\Gamma_0\|&\leq a\;.
\end{aligned}
\tag{G.124}
$$

Here C₀ and Γ₀ are the real reference operators at the undeformed localisation parameters, and P₀=C₀^{-1}. A sign in the definition of an R_i does not matter for these norms. Suppose \(\|C_0\|\leq c_C\), \(\|\Gamma_0\|\leq c_\Gamma\), and a≤1/(2c_C), all in the source's rescaled Gaussian units. Then

$$
P_R\geq\frac{1}{2c_C}I,
\qquad
\|P_R^{-1}-C_0\|\leq2c_C^2a\;.
\tag{G.125}
$$

Expanding \(\Gamma_R^TP_R^{-1}\Gamma_R-\Gamma_0^TC_0\Gamma_0\) gives a bound C(c_C,c_Γ)a, and (G.124) therefore yields

$$
0\leq S_0,\qquad
\|S_0\|\leq C_1\epsilon_{\rm op}\;.
\tag{G.126}
$$

The positivity and rank bound are still the exact identities (G.117); only the size estimate has been weakened. Including the positive quadratic allowance from the potentials and large-field test gives

$$
\|S_\alpha\|\leq C_2(\epsilon_{\rm op}+\alpha),
\qquad \operatorname{rank}S_\alpha\leq2n\;.
$$

The determinant factor is bounded in (2.17) by e^{Cε_op n}; the additional shift by α costs e^{Cαn}. With the source's smallness choice, (G.119) proves

$$
|\text{marked Gaussian primitive}|
\leq M_I e^b e^{C(\epsilon_{\rm op}+\alpha)n}\;.
\tag{G.127}
$$

The quantity ε_op+α is of the same type as α₅ in (2.23). Thus in the primitive estimate (2.26), the last factor can be replaced by

$$
\exp\bigl(C\alpha_5\,\dim\mathfrak g\,\#\{\text{root bonds actually integrated}\}\bigr)\;.
\tag{G.128}
$$

For the unrestricted source integral these are the bonds in Z₀. For a conditional domain D, they are the bonds in Z₀∩D. The extension Z\Z₀′ remains in the localisation decay factor; it does not enter the Gaussian determinant cost merely because the background dependence extends there. This is the advertised refinement of (2.26), at the level of its individual primitive integral.

### 22.6 The Mixed A_j,B_j Reference

The two displayed Gaussian integrals in LFR I (1.60) form a direct-sum Gaussian reference. The interaction \(\mathbb P^{(j)}(g_j,A_j,B_j)\) and all boundary inputs remain inside its density; the interacting law is not a product. In the reference, the covariance for the retained A_j block is obtained from a conditional Gaussian quadratic form of the type CRE (2.21).

For a positive precision K≥mI on the original field space, the precision of the remaining variables after integrating a set Λ is

$$
S=K_{DD}-K_{D\Lambda}K_{\Lambda\Lambda}^{-1}K_{\Lambda D}\;.
$$

Its quadratic form is the minimum of the full Gaussian quadratic form over the Λ variables with the D variables fixed. Therefore

$$
S\geq mI\;.
\tag{G.129}
$$

Taking a principal block for one retained component preserves this lower bound. This proves that the conditional A_j reference has a uniform upper covariance bound whenever the original one-run Gaussian does. The B_j reference has the ordinary fluctuation covariance bound. Their direct sum therefore has a uniform gap, and the finite-dimensional estimate applies with the total number of active A_j and B_j root coordinates.

The spatial and complex perturbation bounds for these conditional kernels still have to be taken from the corresponding one-run localisations; (G.129) alone does not prove them. Once those source bounds are in place, (G.127) gives a root-dimension absolute majorant for an arbitrary bounded scalar mark, including the whole A_j-dependent bracket in (G.39). It introduces no contraction factor, but its cost is of the history-volume type needed by (G.108).

### 22.7 Application Directly to the Positive Majorant

The [focused review](verification/isolated_reviewer/reviews/lf-gamma-gaussian-root-20261028-r1/review.txt) checked (G.114)–(G.121) under their stated matrix hypotheses and checked the marked-moment estimate with the definitions and side conditions now stated above. It did not certify the application to the localised covariance: RG II says the deformed operators are not symmetric, and the packet did not establish complex bilinear symmetry. The following argument avoids that extra premise by starting at the source's positive majorant (2.15).

Let Π be the real symmetric precision of the positive B-Gaussian in (2.15), let B_Γ=Re Γ, and let A be the real symmetric matrix representing the first quadratic form in X. Let D_det be the determinant factor already present in (2.15). Thus the relevant positive integral, with the quadratic allowance and a bounded mark, is at most

$$
M_I e^bD_{\rm det}
\int d\mu_0(X)e^{-X^TAX/2}
\int d\mu_{\Pi^{-1}}(B)
e^{-B^TB_\Gamma X+\alpha|B|^2/2}\;.
\tag{G.130}
$$

Only the symmetric parts of real quadratic forms are used in this definition. No assertion about the symmetry of the original complex operators is needed. The first quadratic form factors through the real and imaginary parts of ΓX. Consequently its range is contained in the range of

$$
W^T,\qquad W=\begin{pmatrix}\Gamma_R\\\Gamma_I\end{pmatrix},
\qquad W\colon\mathbb R^m\longrightarrow\mathbb R^{2n}\;.
$$

The same is true of \(B_\Gamma^T(\Pi-\alpha I)^{-1}B_\Gamma\). After the B integration the remaining symmetric matrix is

$$
\widehat S_\alpha
=B_\Gamma^T(\Pi-\alpha I)^{-1}B_\Gamma-A,
\qquad \operatorname{rank}\widehat S_\alpha\leq2n\;.
\tag{G.131}
$$

It need not be positive semidefinite. That is harmless: if \(\|\widehat S_\alpha\|\leq s\leq1/2\), its negative eigenvalues decrease the Gaussian integral, while its positive eigenvalues give

$$
\det(I-\widehat S_\alpha)^{-1/2}\leq e^{2ns}\;.
\tag{G.132}
$$

The undeformed real reference in (2.16)–(2.21) has Π₀=C₀^{-1}, B_{Γ,0}=Γ₀ and A₀=Γ₀^TC₀Γ₀. Hence its Schur remainder is exactly zero. The source's R₁, R₂ and R₃ bound the differences of these three matrices by a=C_opε_op, after taking symmetric parts where necessary. The calculation (G.125)–(G.126), now with Π, gives

$$
\|\widehat S_\alpha\|\leq C(\epsilon_{\rm op}+\alpha)\;.
$$

The determinant D_det is bounded in (2.17) by \(e^{C\epsilon_{\rm op}n}\). The shift from Π to Π−αI adds \(e^{C\alpha n}\). Therefore (G.130) is bounded by

$$
M_I e^b e^{C(\epsilon_{\rm op}+\alpha)n}\;,
\tag{G.133}
$$

provided Π has the stated one-run gap and the smallness choices make \(C(\epsilon_{\rm op}+\alpha)\leq1/2\). The marginal moment bound follows from the same completed positive joint Gaussian, with Π in place of P_R. This supplies the root-dimension improvement directly for the actual absolute majorant used in the paper. It uses (2.17) as the source's determinant bound; it does not rederive that bound or replace the source's complex measure by a newly chosen one.

The remaining mixed-domain application still requires identification of its actual root variables, normalising constants and potential bounds. The original A_j integral has an unnormalised Gaussian factor: when it is written as a normalised Gaussian, its determinant and scalar integral must stay in the vacuum/normalisation factor. They are independent of a frozen boundary-input source, but not of every two-run perturbation. Such variations remain separate marks. The new argument (G.130)–(G.133) has not yet had independent review.

### 22.8 A Direct Refinement of the Printed R₁,R₂,R₃ Argument

The same root-dimension conclusion can be obtained using the paper's estimates literally, without new bounds on imaginary parts or a separate derivation of the norm of Γ. This gives a source-level implementation of the refinement.

In the transition from (2.15) to (2.23), keep the three error forms instead of replacing all of them by multiples of \(\|ZX\|^2+\|Z_0B\|^2\). Use the following facts about the errors before taking absolute values:

- The symmetric real matrix R₁ is the difference of the first quadratic form in X and its undeformed reference \(\Gamma_0^TC_0\Gamma_0\). Its range lies in the span of the ranges of \(\Gamma_R^T,\Gamma_I^T,\Gamma_0^T\). Hence rank R₁≤3n.
- R₂ acts only on the n root variables B.
- R₃ maps the auxiliary variables X to the root variables B, so rank R₃≤n.

The row and column bounds in (2.16) imply, with a=C_opε_op, that all three operator norms are at most a. For a>0,

$$
|B^TR_3X|\leq\frac a2|B|^2
+\frac{1}{2a}|R_3X|^2\;.
\tag{G.134}
$$

For a=0 the term is zero and is omitted. Replace the first error form by its spectral absolute value. Its contribution is bounded by \(X^T|R_1|X/2\), and |R₁| has the same rank as R₁. Thus the external positive allowance can be taken to be

$$
E_X=|R_1|+a^{-1}R_3^TR_3,
\qquad E_X\geq0,
\quad\|E_X\|\leq2a,
\quad\operatorname{rank}E_X\leq4n\;.
\tag{G.135}
$$

The R₂ contribution, the first term of (G.134), the quadratic part of the potentials in (2.20), and the positive quadratic part of the large-field test in (2.22) are all in the B variables. Bound these quadratic terms by \(\widetilde\alpha|B|^2/2\). Choose the unspecified fixed O(1) coefficients in the source's α₅ large enough that \(\widetilde\alpha\leq\alpha_5\) and \(\epsilon_{\rm op}\leq C\alpha_5\), and impose its smallness conditions after this choice. The source's positive reference remainder is monotone in the shift parameter, so its bound at α₅ also bounds the shift by \(\widetilde\alpha\). The constant \(b=C\alpha_4M^{-4}|Y_0|\) from (2.20) remains outside this Gaussian integral as e^b. The determinant costs quoted in (2.17) are retained as \(e^{C\epsilon_{\rm op}|Z_0|}\); a stronger conversion to the number of free coordinates is not assumed.

After integrating B as in (2.24), the remaining positive X-form is

$$
E_X+\Gamma_0^T\bigl[(C_0^{-1}-\widetilde\alpha I)^{-1}-C_0\bigr]\Gamma_0\;.
\tag{G.136}
$$

The B integration requires \(\widetilde\alpha\|C_0\|<1/2\), which is imposed explicitly. The unperturbed conditional form then cancels exactly. The second term in (G.136) has rank at most n. The source's estimate immediately after (2.24) bounds its norm by C\(\widetilde\alpha\). Therefore (G.136) has rank at most 5n and norm at most Cα₅. Also choose α₅ small enough that this last norm is below 1/2. The X integral is then bounded by

$$
\exp(C'\alpha_5 n)\;.
\tag{G.137}
$$

The B determinant shift has the finite-dimensional bound \(e^{C\widetilde\alpha n}\), or the source's stated bound with |Z₀|. A scalar mark bounded uniformly by M_I on the actual cutoff support and on the localisation contours multiplies the absolute estimates by M_I. The full conclusion for (2.26), after the counting and constant-term bookkeeping below, is a last factor \(e^{C\alpha_5|Z_0|}\). The finite-dimensional X-integration bound (G.137) is stronger, but it is not by itself the complete last factor in (2.26).

This proof uses the one-run R_i bounds and the one-run remainder bound after (2.24), both printed on the supplied pages. It does not require complex bilinear symmetry of the deformed C. Taking the spectral absolute value of R₁ is only an estimate of a finite-dimensional integral already assigned to its localisation domain; it introduces no new operator or locality assertion in the construction.

The argument establishes the refinement for the native RG II primitive. To use it for (1.60), one must still exhibit the corresponding three root-factorised error forms for that mixed-domain integral. The direct-sum Gaussian structure supplies the candidate forms, but the complete identification, including all source normalisers and potentials, is a separate application.

### 22.9 Complete Factor Ledger for the Native Primitive

The [second focused review](verification/isolated_reviewer/reviews/lf-gamma-gaussian-root-20261028-r2/review.txt) checked the finite-rank estimates in §22.8, but did not accept the asserted complete n-bound: the constant part of (2.20) and the |Z₀|-form of the determinant bounds had not all been carried through. The corrected conclusion is the geometric root-volume bound stated here.

The covariance \(C^{(k)}(Z_0,\sigma)\) in (2.14) is the matrix on the conditioned B coordinates in Z₀. Localisation changes its matrix entries, not that coordinate space. Its ambient zero extension has the endpoint projections \(1_{Z_0}C(\sigma)1_{Z_0}\), and Γ in the first normalising form means \(1_{Z_0}\Gamma\). More explicitly, PBG Theorem 3.15 gives the kernel and its walk expansion for y,y′∈Λ. Set Λ=Z₀. The localisation rule of RG II (1.6) multiplies each walk coefficient by its s-variables; it does not change the endpoint indices y,y′. Equivalently, every coefficient has the two fixed endpoint projections before those scalar weights are introduced. They therefore persist for complex σ as well. This proves the support statement by the termwise definition, not by an inference from σ=1 alone. No symmetry of the deformed covariance is used.

In RG II (2.30), \(M^{-4}|Y|\) counts the M-cubes of the localisation domain in the rescaled unit lattice. The number n of free real Lie-algebra B coordinates in Z₀ satisfies only the upper bound needed here:

$$
n\leq C_d\dim\mathfrak g\,|Z_0|\;.
\tag{G.142}
$$

For the counting, take |Z₀| to be its unit-cell volume: M^d times the number of M-cubes. Each such cube contains at most 2d(M+1)^d incident unit bonds, so their union has at most 2d·2^d|Z₀| bonds for M≥1. Counting unit sites instead changes this bound only by a fixed dimension-dependent boundary factor. This proves (G.142) for either convention used in the source's O(1) bounds. Removing designated or gauge-fixed bonds decreases n. No lower bound |Z₀|≤Cn is used. Since Y₀⊂Z₀ and M≥1,

$$
b=C\alpha_4M^{-4}|Y_0|
\leq C\alpha_5|Z_0|\;.
\tag{G.143}
$$

The complete ledger is therefore:

| Factor in the bound of (2.14) | Cost retained |
|---|---|
| Cauchy localisation factors | The first factor of (2.26), unchanged |
| Ordinary potential prefactors | The product over Y of (2.26), unchanged |
| Large-field test constant | \(e^{-\gamma_2\varepsilon_1^2g_k^{-2}|P|/2}\), unchanged |
| Both covariance determinant ratios of (2.17) | \(e^{C\epsilon_{\rm op}|Z_0|}\) |
| Constant part of (2.20) | \(e^b\leq e^{C\alpha_5|Z_0|}\) |
| B determinant shift in (2.24) | \(e^{C\widetilde\alpha n}\leq e^{C\alpha_5|Z_0|}\) |
| X integration | \(e^{C\alpha_5n}\leq e^{C\alpha_5|Z_0|}\) by (G.137) and (G.142) |

Thus, with all source smallness conditions and the two Gaussian smallness conditions of §22.8, the native marked primitive has the bound

$$
\begin{aligned}
|\text{marked }(2.14)|\leq{}&M_I
e^{-(\kappa_1-1)(LM)^{-4}|Z\setminus Z_0'|}\\
&\times\prod_{Y\in\mathbf D}
\left[2E_0\varepsilon_1C_1\alpha_4^{-1}M^q e^{C_2\kappa_1}
e^{-(1-3\delta)\kappa d_k(Y)}\right]\\
&\times e^{-\gamma_2\varepsilon_1^2g_k^{-2}|P|/2}
e^{C\alpha_5|Z_0|}\;.
\end{aligned}
\tag{G.144}
$$

For this native marked formula, fix an admissible term of (2.14) with its original Y₀,P,Z₀,Z. Insert I in its root B-integral before the localisation derivatives, and assume its B-dependence is confined to the existing Z₀ coordinates. Do not redefine Y₀ or Z₀ in this assertion. The mark is independent of the ordinary Mayer parameters τ(Y), and is holomorphic on a neighbourhood of the closed background-localisation σ-discs. Cauchy's formula then acts on the product containing I with the same derivative contours. The required bound M_I is uniform over the auxiliary X variables, the real B variables on \(\chi_{k,Y_0}\chi^c_{k,P}\), and all s,t,σ,τ contours. First use \(|I|\chi\leq M_I\chi\); only afterwards apply (2.22). In constructing a numerator expansion one may need a different root containing the mark; its geometric definition and its resummation must then be proved separately. They are not certified by (G.144).

The changes in §§22.8–22.9 after the second review have not yet been re-reviewed. This conclusion concerns the native RG II root volume. Replacing |Z₀| by |Z₀∩D| for a restricted mixed-domain integral requires repeating the potential-constant and determinant counts on that actual integration space; it does not follow solely by renaming n.

The [third focused review](verification/isolated_reviewer/reviews/lf-gamma-gaussian-root-20261028-r3/review.txt) checked the corrected ledger and found no mathematical error in (G.144), conditional on clarifying the root support, volume count and shift parameter. The preceding paragraphs now give the termwise endpoint argument, the elementary cube count and the explicit choice of the O(1) constants. The review also requested the precise mark conditions, now stated above. These final clarifications have not themselves been re-reviewed. No mixed-domain resummation or Cauchy estimate is certified by this result.

## 23. Normalisation and Dimension Accounting for (1.60)

Fix one admissible preliminary history, j=h+n, and all variables not integrated in the next operation. Let D_A be the free A_j bonds in Z_{j+1}∩Ω_{j+1}, and D_B the free B_j bonds in \(\Omega_{j+1}^c\setminus Z''_{j+1}\), restricted to the component in question. The gauge constraints have already been removed by the source's maps. The variables A_j and B_j themselves are real; complex background parameters enter their densities and reconstructed configurations.

Write K_A and K_B for the real-reference precision matrices in the two displayed quadratic forms of (1.60), in those free coordinates. Their coefficients are evaluated at the reference background. All remaining dependence, including any dependence of a quadratic coefficient on the integration variables, belongs in the full scalar interaction \(\mathcal V_n\). With the actual constant z^{(j)}, the integral in the logarithm of (1.62) is exactly

$$
Z_n=\mathcal N_j
\int\chi_A\chi_B e^{\mathcal V_n(A,B)}
\,d\mu_{K_A^{-1}}(A)\,d\mu_{K_B^{-1}}(B),
\tag{G.138}
$$

where, on the real positive reference,

$$
\mathcal N_j
=z^{(j)}(2\pi)^{(n_A+n_B)/2}
(\det K_A)^{-1/2}(\det K_B)^{-1/2}\;.
\tag{G.139}
$$

Here n_A and n_B include Lie-algebra multiplicity. Any scalar Jacobian already present in the source's choice of free-coordinate measure remains in \(\mathcal N_j\) or in the stated source prefactor; it is not dropped. The external factor \(\chi_k^{(n+1)}\exp[A_k^{(n)}(U_k^{(n+1)},A_j=0)+E_0^{(j)}]\) in (1.60) remains outside Z_n, exactly where the source puts it.

This is a product reference measure, not a claim that the interacting fields are independent. All A_j–B_j couplings are retained in \(\mathcal V_n\). If its quadratic part has a non-small mixed term, the positive quadratic allowance of §22 cannot absorb it. One must include that term in the joint reference precision and prove its one-run gap, or retain the corresponding exact conditional Gaussian structure. The rank argument applies to that full reference as well once it is specified.

For a perturbation solely of a prior boundary input F, the reference kernels and the prescribed coupling profile are held fixed. The normalising scalar \(\mathcal N_j\), E₀^{(j)} and the explicit coupling term of (1.62) then have zero derivative with respect to this input parameter. The differentiated creation term is exactly the expectation of the full subtraction (G.39), with both A_j and B_j integrated under (G.138). This statement does not apply to a change of the two runs' couplings or Gaussian operators. In that case one retains, in particular,

$$
\delta\log\mathcal N_j
=\delta\log z^{(j)}
-\frac12\delta\log\det K_A
-\frac12\delta\log\det K_B\;,
\tag{G.140}
$$

and the corresponding source prefactors and coupling counterterms. Their cancellation with the numerator and denominator Wilson terms must be performed before estimating any individually large terms.

For a localised root, let D₀⊂D_A⊔D_B be the root variables that the conditional Gaussian construction integrates. Its dimension satisfies

$$
\dim D_0\leq n_A+n_B
\leq C_d\dim\mathfrak g\,L^d
|Z_{j+1}\cap H|_{j+1}\;.
\tag{G.141}
$$

Indeed the integration variables are scale-j bonds in the component's retained region. Each scale-(j+1) cell contains L^d scale-j sites and a fixed multiple of that number of bonds; the star convention adds only a dimension-dependent boundary factor. The restrictions to the actual integration subdomains and to free bonds can only reduce the count.

Summing (G.141) over the preliminary integrations gives a bound by C_d dim𝔤 times the actual history volume P_H in (G.84). Variables at different scales are counted at their own scales. There is no estimate by the number of finest-lattice sites in an enlarged background localisation domain.

Thus the Gaussian cost (G.137), summed through the history, has the required form e^{Cα₅P_H}. The same statement holds for the determinant and scalar costs of fixed Gaussian normalisation, with their actual logarithmic coupling coefficients retained. The still-needed step is the mixed-domain potential majorant of type (2.20) for all terms of \(\mathcal V_n\), and its localisation with the marked subtraction. The Gaussian calculation does not turn a non-small mixed interaction into a small one.

Sources: [LFR I pp.188](../Balaban/tex/LFR1/parts/p188_corrected.tex)–[189](../Balaban/tex/LFR1/parts/p189_corrected.tex), [CRE p.258](../Balaban/tex/CRE/parts/p258_corrected.tex), [PBG p.432, Theorem 3.15](../Balaban/tex/PBG/parts/p432_corrected.tex), and [RG II pp.15](../Balaban/tex/RG2/parts/p015_corrected.tex)–[17](../Balaban/tex/RG2/parts/p017_corrected.tex).

## 24. Checkpoint Before the V4 Comparison

The completed local calculation is the finite-rank conditional Gaussian bound, with the conditional normalising exponential retained. The focused reviews checked its Gaussian algebra and the native factor ledger. The final endpoint-support, volume-count and mark-domain clarifications are written in §22.9. This establishes a concrete candidate primitive estimate with a cost in |Z₀| instead of |Z|; it is not a bound for the whole mixed large-field operation.

The first remaining substantive estimate is the marked mixed-domain activity norm (G.112) for the **full** insertion F(U(B_j),A_j)−F(U(0),0) in (1.60). Its proof must combine the actual mixed potential bounds and cutoff families with the localised marked primitive, then preserve the V(X^∼)/V(Y) split in (G.104). The proposed active-support bookkeeping in §21 has not been established for that full representation. The stopped-component reserve in (G.108) must then be checked with those actual costs. Until these steps are done, neither LF-A(10) nor ingredient (γ) is closed.

All six isolated reviews launched for this note have completed. Their transmitted packets were checked against their saved packets, with no extra task text or tools in the requests. No mathematical acceptance is inferred from those procedural checks. The original Cauchy and LF drafts have not been edited by this work, and nothing from this note has been pushed.

## 25. Comparison With the Existing V4 Proofs

Checked against [WILSON_FIRST_RG_STEP_V4.tex](../WILSON_FIRST_RG_STEP_V4.tex), SHA-256 `563736a8dfb946b7018b2f5cf5648b9ae7a4bb2322bcac60e7aaeba0c3eaa96c`, on 28 October 2026. The locations below refer to this revision. This is a comparison of the proofs and their hypotheses, not a new acceptance review or a closure of ingredient (γ).

### 25.1 Existing Results to Reuse

| Requirement in this note | Existing V4 result | Scope of reuse |
| --- | --- | --- |
| Conditional Gaussian density, including its compensator and normalisations (§§12, 22) | `lem:conditioning`, `lem:gaussian-payment`, and Appendix `app:fixed-kernel-payment` (lines 945–995, 4356–4398) | The Gaussian payment mechanism is already present. The root-volume refinement in §22 changes the dimension cost in the native RG II estimate; it is not a new construction of the conditional measure. |
| Moments for a varying Gaussian density (§§12, 22–23) | `sec:c4-10-3`, especially `eq:c4-10-14` (lines 5544–5561) | The proof retains and differentiates both the Gaussian normalisation and the compensator. Its moment loss is linear in the selected domain's cube count. No new Gaussian moment argument is needed under these hypotheses. |
| A bounded scalar insertion inside the interacting selected integral (§§20–21) | `lem:c5-5-2`(b)–(d) (lines 2864–2888) | The total-variation majorant applies to every bounded Borel insertion; the dummy comparison sums over selections, and the centred expectation keeps the interacting denominator through the joint vacuum ratio. |
| Cutoff and interaction marks, followed by a connected-cluster difference (§§6, 12, 17, 20–21) | `lem:c5-5-6` and its proof (lines 2945–2975) | The actual product is telescoped with one marked factor. Translated cutoff shells, host marks, selection sums and vacuum-cluster differences are all included. The Gaussian density is fixed during this particular comparison. |
| Cancellation and differentiation of the physical vacuum ratio (§§12, 17, 20–21) | `lem:vacuum-clusters` and `lem:c4-7-4` (lines 1038–1050, 5356–5373) | Rooted connected sums and the marked vertex count are already paid by the available exponential moment. This avoids an independent volume-sized denominator estimate. |
| An analytic parameter without analyticity of the insertion in real fluctuation variables (§§20–21) | `lem:c5-5R-2`(c)–(d) and its proof (lines 3178–3194) | Scaling the ordinary potentials gives an entire selected integral for bounded Borel insertions independent of that parameter. Cutoffs, Gaussian density and normalisers remain fixed. The resulting small factor requires a nonempty ordinary-host selection. |

The last result is particularly relevant to the earlier concern about retained real variables: bounded Borel insertions do not need a holomorphic extension in those variables to use this parameter argument. This does not supply the separate analyticity and spatial localisation of a background-dependent insertion required in (G.112). Nor do the Wilson-specific derivative and parity gains of `lem:c5-5R-1` and `lem:c5-5R-3` become bounds for an arbitrary boundary term merely by citing the bounded-insertion result.

### 25.2 The Remaining Application

The comparison narrows the task. It is not to invent a marked-measure estimate or prove rooted-tree summability again. It is to apply this existing machinery to the literal mixed integral LFR I (1.60), with the full subtraction in (G.39), and then to its outer localisation.

Three differences still need an explicit argument:

1. **Kernel and integration geometry.** V4's fixed-walk construction uses a uniformly gapped finite-range precision, local coefficient stencils and its exact component factorisation (`eq:fixed-kernel-inputs`, lines 890–962). These properties have not been verified here for the mixed preliminary integrations. The proof of `lem:c5-5-6` explicitly leaves the density fixed; changing the two runs' kernels additionally requires the differentiated construction of `sec:c4-10-3`, with its support and uniformity hypotheses checked.
2. **The full inherited integrand.** V4's translated estimates use the enlarged-box primitive bounds and protected hosts of `lem:c5-4-0`, the small-potential hypotheses of `lem:c5-5-2`, and a controlled mean translation. The actual mixed potentials, earlier boundary terms, both cutoff families, coupling corrections and scalar normalisations of (1.60) must be matched to these hypotheses. A bounded insertion estimate alone does not provide the depth-small two-run mark or its complex background class norm.
3. **The multiscale output and reserve.** V4 sums its selected measures by final domain. This does not establish the proposed active-support representation (G.109)–(G.112), the redistribution between V(X^∼) and V(Y), or the stopped-history reserve (G.108). Those are requirements of this application, not missing general Mayer-expansion algebra.

V4 does include physical history integration and large-field estimates in its first-step theorem; describing it as a bare Gaussian or history-free argument would be incorrect. Nevertheless its final `conj:iteration` and `rem:next-step` (lines 3784–3804) explicitly leave general-step closure and the absorption of output history labels to be proved. They cannot be cited as a completed multiscale comparison.

Consequently §§12, 17 and 20–22 contain substantial duplication of mechanisms already in V4. Their generic Gaussian, marked-selection and cluster arguments should be reused by reference, with new work confined to the three application issues above. This comparison does not close LF-A(3), (6), (7) or (10).

## 26. Bounded Boundary Marks Using the Existing Selected Measures

### 26.1 The Estimate Supplied by V4

Here is a consequence of the actual selected-measure and vacuum-cluster bounds, rather than a new Gaussian comparison. Work first under the hypotheses of V4 `lem:c5-5-2`, at a fixed member of its translated family. Write a for its centred integration variable B, so zero here corresponds to the physical variable tm, and S for a finite set of integrated bond labels. The exterior data determining this measure and its shift are real and satisfy that lemma's cutoff hypotheses. Let f(a_S;v) be a bounded Borel scalar function, with bound f_* on the closed box |a_b|≤5r/4 containing the selected measures and all their coordinatewise zeroings. The parameter v may include additional complex arguments of the insertion, with a uniform bound on their stated domain; this alone does not permit a complex exterior datum in the measure. No analyticity in a_S is required. The expectation below has the full density and denominator of V4 `lem:c5-5-2`(d).

Let u_* be V4's fixed dummy-label weight, m(Z) its activity majorant, and θ its cluster-weight constant. For each b choose T_b to be the smallest rectangle of final LM-cubes containing Y_b, using its periodic lift. Nestedness implies that a run of at most four consecutive M-cubes meets at most two LM-cubes in each direction for L≥3. Hence N_1(T_b)≤t_*=2^4. Put

$$
K_\theta=\sup_b\sum_{Z\not\sim T_b}
m(Z)e^{(\theta+1/8)N_1(Z)}\leq t_*/8\;.
\tag{G.145}
$$

The inequality is the numerical positive-majorant criterion used in V4 `lem:activity-bounds`, since θ+1/8≤1+6θ. The test polymer need not carry a nonzero vacuum activity. Its role is only to root that criterion.

Expand the exact joint vacuum ratio in the centred-expectation identity as the exponential of the clusters meeting the selected roots. Expand this exponential too, retaining its factorials. For a term with root family A and attached vacuum-cluster list, let n be the sum of N_1 over all roots and all cluster constituents, counted with multiplicity. Define the absolute expansion sum by taking the absolute value of each resulting integrated scalar coefficient, multiplying by e^{θn}, and summing. This is stronger than an absolute bound on the final expectation; no cancellation between these coefficients is used in the following estimate.

For s=|S|≥1, that expansion of the centred insertion satisfies

$$
\mathfrak A_\theta(f-f(0))
\leq f_*\left(\frac{2}{u_*}\right)^s
\bigl((1+K_\theta)^s-1\bigr)
\leq f_*e^{c_*s}\;,
\qquad c_*=\log(2/u_*)+\log(1+K_\theta)\;.
\tag{G.146}
$$

For S empty the centred insertion and its expansion vanish. The notation c_* in this section is local to this estimate and is not V4's witness constant.

**Proof.** In the exact selected-measure expansion the insertion at a compatible root family is the anchored finite difference Δ_J f, with J the disjoint union of the nonempty selected label sets J_Z. It vanishes if any label of J lies outside S. Otherwise

$$
|\Delta_J f|\leq 2^{|J|}f_*\;,
\qquad |J|\leq s\;.
\tag{G.147}
$$

Insert u_*^{|J_Z|} at each root and its inverse in this inequality. Since 0<u_*≤1, the product of all inverse weights and all finite-difference factors is at most (2/u_*)^s, once for the entire root family. The termwise dummy comparison in V4 `lem:c5-5-2`(c) then sums the remaining selection measures to at most ∏_Z m(Z). It is legitimate to restrict this comparison to nonempty J_Z⊂S and subsequently enlarge its sum.

For the vacuum ratio, V4 `lem:vacuum-clusters`, extended to the translated family by `cor:c5-4-3`, bounds the sum of the absolute cluster weights, with weight e^{2θn}, by Σ_Z N_1(Z)/8. Consequently the absolute sum of the expanded ratio, with weight e^{θn} on its cluster constituents, is at most exp(Σ_Z N_1(Z)/8). This uses the same numerator and denominator as the exact expectation. It does not replace the interacting expectation by the Gaussian law.

Order S once. In each root selection assign the root to the least element of J_Z. Distinct compatible roots have disjoint eligible carriers, so their assigned labels are distinct. A root assigned to b contains Y_b and is incompatible with T_b. Retain this assignment while summing its selection measures; the restricted sum is still at most m(Z). Then discard compatibility and the restrictions on the other probe labels. The sum over these assignments is bounded by

$$
\sum_{\varnothing\neq J_0\subseteq S}
\prod_{b\in J_0}\left(
\sum_{Z\not\sim T_b}m(Z)e^{(\theta+1/8)N_1(Z)}
\right)
\leq (1+K_\theta)^s-1\;.
\tag{G.148}
$$

There is no factorial loss: an unordered root family, with its deterministic assignment, has distinct labels in S. The enlarged sum in (G.148) can count additional families but cannot omit an original one. This proves (G.146).

For the simultaneous site gauge transformations of V4 `sec:c4-8-1`, the density, protected cutoffs, host primitives and fixed walks transform as stated there (line 5381). The shift m=−H^{-1}ℓ transforms with the integrated fields. If f is invariant under this simultaneous transformation, each Δ_J f is also invariant: setting a coordinate to zero commutes with its adjoint action. The same orthogonal changes of the integrated variables therefore leave each selected scalar coefficient invariant, before summing spatial domains.

For the translated family this uses the transformation of the retained input as well. Write R for the bondwise adjoint action. The simultaneous transformation gives H^u=RHR^{-1}, ℓ^u=Rℓ, m^u=Rm and (A^{Λ,Ψ})^u=RA^{Λ,Ψ}. Therefore the argument B+tm+tA^{Λ,Ψ} of each scalar primitive transforms by R, and χ_b^t(RB;m^u)=χ_b^t(B;m). The seed covariance and cross operator transform as C_E^u=R_EC_ER_E^{-1} and Γ^u=R_EΓR_aux^{-1}; the standard auxiliary Gaussian is invariant under R_aux. Both Gaussian normalisations and the compensator are preserved. This proves the pushforward covariance of the translated selection measure from the simultaneous covariance of its primitives, rather than treating a transformation of the background alone as sufficient.

### 26.2 The Full A_j Part of the Boundary Subtraction

In the literal integral LFR I (1.60), keep the one-run background, couplings, cutoffs and Gaussian operators fixed. For a localised old boundary input F_X, split its full subtraction exactly as

$$
\begin{aligned}
I_{F_X}={}&F_X(U(B_j),A_j)-F_X(U(0),A_j)\\
&+F_X(U(0),A_j)-F_X(U(0),0)\;.
\end{aligned}
\tag{G.149}
$$

For this insertion, S_X denotes the integrated A_j labels read by F_X; all other retained variables are frozen at their actual values. The symbol 0 in an application of (G.146) resets precisely those integrated labels. If the source's subtraction also resets a frozen label, its difference is a separate constant insertion and is not covered by the centred bound. The fixed background at the source's subtraction point is U_k^{(n+1)}, independent of both integrations. Identification of this point with U(B_j=0), and the convention for the A_j reset, must be checked in matching the source. The finite-difference argument uses f(a)=F_X(U_k^{(n+1)},a), not a Taylor derivative of F_X in a. In particular it gives no artificial δ'_j/ε_j gain for this part. The common bound f_* must hold at every coordinatewise zeroing in the cutoff box.

If the selected-measure comparison is established for the mixed integral with constants u_*, K_θ uniform in j, its conclusion for this insertion is f_*exp(c_*|S_X|), with the absolute localised expansion norm of (G.146). The number of these labels is bounded by the number of scale-j free bonds integrated in the component:

$$
|S_X|\leq C_dL^d
|Z_{j+1}\cap\Omega_{j+1}|_{j+1}\;.
\tag{G.150}
$$

Here the right-hand side counts scale-(j+1) cells, with the fixed boundary enlargement used for the source's star convention; C_d counts bonds per cell. It does not count all fine sites of the background localisation X. Lie-algebra dimension is already part of the fixed selected-measure constants; S_X counts bond labels. Thus the resulting cost has the history-volume form needed in (G.108). A purely frozen insertion, S_X empty, gives zero for this line of (G.149).

### 26.3 Matching the Mixed Construction

The preceding proof is complete for V4's selected measures. The following is the proposed transfer to (1.60), to be checked separately from that proof.

First, the A_j precision in (1.60) is not a principal restriction of the first-step precision. LFR I p.182 explicitly identifies its form with CRE (2.21), whose exponent is the original quadratic form plus its conditional-completion term. It is a Schur complement. Its Gaussian normalisation cannot be replaced by the normalisation of the B_j factor. Both are retained in (G.138)–(G.140).

Second, the proposed transfer uses Bałaban's mixed one-run expansion, not V4's finite-range square-root series. LFR I pp.187–189 reduces (1.25) to (1.60) and applies CRE §3, with mixed localisation domains. CRE pp.275–278 invokes the generalised random-walk construction for the layered geometry and expands the numerator and physical denominator with identical vacuum activities. The potential bounds, including the cumulation of the earlier boundary terms, are the ones asserted in LFR I pp.191–192. They are inputs from that source; they are not supplied by (G.146).

At fixed localised potentials, insert the selected labels for A_j bonds in S_X by the same split-host construction as V4. A selected label forces its bounded local host into the seed; the measure has no insertion factor yet. Its eventual action is δ_a−δ_0. This does not require differentiating a characteristic function or analytically continuing F_X in A_j. With q_Y labels sharing a host Y and numerical weight u, the host comparison is the elementary positive sum

$$
(e^{A_Y}-1)(1+u)^{q_Y}+
\bigl((1+u)^{q_Y}-1\bigr)
\leq e^{A_Y+q_Yu}-1\;.
\tag{G.151}
$$

Here A_Y is the ordinary host's potential allowance, including its assigned cutoffs. There are boundedly many labels per scale-j host. A uniform u is therefore possible if the mixed primitive/resummation proof has a fixed positive allowance for these extra local hosts. The construction must establish this allowance within the native constants; merely knowing convergence for the original activities does not establish it. After that check, all sums in (G.145)–(G.148) use the same unmarked mixed activities and vacuum ratio, with F_X kept as a single scalar insertion.

The external background dependence on X is kept as a separate label. It does not force integration over X or alter the Gaussian seed. This observation applies to the second line of (G.149). The first line still requires the source's reconstruction localisation before its active coordinates are known. Also, e^{θn} in (G.146) is the explicitly stated expansion weight; its conversion to the precise mixed-domain spatial weight of (G.112) must be checked, not inferred from the unweighted bound. These are application requirements, not conclusions of the bounded-Borel corollary.

Sources: V4 `lem:c5-5-2`, `lem:vacuum-clusters`, `lem:activity-bounds` and `eq:c-probe-host`; [LFR I p.182](../Balaban/tex/LFR1/parts/p182_corrected.tex), [pp.187](../Balaban/tex/LFR1/parts/p187_corrected.tex)–[192](../Balaban/tex/LFR1/parts/p192_corrected.tex); [CRE p.258](../Balaban/tex/CRE/parts/p258_corrected.tex), [pp.275](../Balaban/tex/CRE/parts/p275_corrected.tex)–[278](../Balaban/tex/CRE/parts/p278_corrected.tex).

## 27. The Dummy Labels in the Native Seed Sum

The extra-label allowance left explicit in §26.3 can be analysed directly in RG II (2.26)–(2.38). This avoids inferring a quantitative allowance merely from convergence. The calculation below proves that part of the transfer for the native primitive majorant. Its application to (1.60) still requires that majorant for the mixed selected integrals with enlarged seeds.

Use δ, κ and the other constants of those native equations; these are not the numerical constants chosen in V4. Set a=(1−3δ)κ, and write the ordinary-host factor in (2.26) as

$$
w_o(Y)=b_{\rm reg}e^{-a d_j(Y)}\;,
\qquad
b_{\rm reg}=2E_0\varepsilon_1 C_1\alpha_4^{-1}M^q e^{C_2\kappa_1}\;.
\tag{G.152}
$$

In this display g is the coupling at the fluctuation step and ε_1 is the native small interaction parameter. The later mixed application must use its actual analogue of b_{\rm reg}, including the overlapping earlier boundary terms; it is not obtained by silently replacing all of them by the regular potential.

Attach a bounded local host Y_b to each selected integrated bond b. Let q_Y be the number of eligible labels having a given host, with q_Y≤P_* and d_j(Y)≤B_* whenever q_Y>0. Both constants are fixed by the host geometry at scale j. A selected label contributes the numerical factor u. It contributes no ordinary Mayer factor and no term to the exponent of the actual integration density.

For a fixed selection of ordinary and probe labels, take Y_0 to be the union of all their hosts. The cutoffs on this enlarged Y_0 are retained, and the bad set lies outside it. The conditional Gaussian construction is performed with this enlarged seed, exactly as in V4's split-host measure. At the level of the primitive estimate, the ordinary potential exponent is unchanged. In particular the constant term proportional to |Y_0| in RG II (2.20) is retained with the enlarged Y_0. The Gaussian and bad-bond factors of (2.26) are evaluated for that same enlarged seed. There is no comparison of two seed measures by a Radon–Nikodym bound here.

At a host, sum over its nonempty label subsets. The sum of numerical weights is

$$
w_{\rm lab}(Y)=(1+w_o(Y))(1+u)^{q_Y}-1\;.
\tag{G.153}
$$

For P_*u≤1, the inequalities (1+u)^{q_Y}≤e^{q_Yu} and e^x−1≤ex for 0≤x≤1 give

$$
w_{\rm lab}(Y)
\leq e\bigl(b_{\rm reg}+P_*u e^{aB_*}\bigr)e^{-a d_j(Y)}\;.
\tag{G.154}
$$

If q_Y=0 this follows directly from w_lab=w_o; otherwise multiply the term eP_*u by e^{aB_*}e^{-ad_j(Y)}≥1. Hence choose a fixed amplitude b_*>0 within the native resummation and vacuum-cluster thresholds, and then fix

$$
0<u\leq\min\left(\frac1{P_*},
\frac{b_*e^{-aB_*}}{2eP_*}\right)\;,
\qquad b_{\rm reg}\leq\frac{b_*}{2e}\;.
\tag{G.155}
$$

The second condition is a restriction on the native interaction amplitude, obtained by choosing ?_1 sufficiently small in this regular construction; the first fixes u before the coupling. The subsequent small-coupling choice pays the bad-field factors. In a coupling-dependent cutoff prescription the corresponding amplitude restriction must be checked with that prescription. Equations (G.153)–(G.155) give w_lab(Y)≤b_*e^{-ad_j(Y)} uniformly. In particular it is unnecessary to choose u proportional to b_{\rm reg}, which could introduce an avoidable coupling dependence in the per-label cost of (G.146) when the prescribed interaction amplitude varies with the coupling.

The resummation now uses the same bounds in the same order as the source. In (2.28), replace its ordinary coefficient by b_* and put ε_2=b_*/α_6. Choose b_* so that the displayed condition ε_2e^{5κ}≤1 holds. The sums (2.29)–(2.35) over host families and bad sets then apply to their enlarged union; every seed component still contains an active host or a bad bond. A component containing only dummy labels is paid by its host factor b_*, rather than by an ordinary interaction or a bad bond. The source's lower comparison between the bad-bond suppression and ε_2 is preserved once it holds with this fixed ε_2.

The remaining requirements before (2.37) are fixed upper bounds on ε_2, including 2(L+2)^4 C_enum ε_2e^{5κ}≤1, where C_enum is the fixed domain-count constant in the source's reblocking sum. The final activity amplitude is a fixed multiple of ε_2. Choose b_* smaller, before choosing u and the coupling, so that this amplitude satisfies the vacuum-cluster criterion. All these are upper bounds on one fixed positive b_*; none forces b_* to vanish with g or the lattice volume. The decay exponent is the one in (2.38).

For clarity, the enlarged-seed step in this regular construction can be checked before any resummation. Let Y_ord be the union of the selected ordinary hosts, and let Y_0 be its union with the selected probe hosts. The potential factors and their τ(Y) radii are exactly those of RG II (2.18); there is no τ for a probe. The left side of (2.20) is still the sum over ordinary hosts only. Its proof first bounds it by a quadratic form supported on Y_ord and a constant proportional to |Y_ord|. Enlarging both positive upper bounds to Y_0 is valid. The additional cutoff factors on Y_0∖Y_ord have modulus at most one and do not invalidate any potential bound. Thus (2.19)–(2.20) apply without assigning a quadratic allowance to a nonexistent probe potential.

The bad bonds are selected outside this enlarged Y_0. Construct Z_0 by the same rule as RG II (2.3)–(2.4), including a containing cube on both sides when necessary so that every bad bond lies in the interior. Adding a probe host changes this seed but not that rule. The conditional-Gaussian identity (2.5) is valid for that seed, and the central-domain choice in the generalised walks on p.13 is made for that seed. Bounds (2.16)–(2.26), including both determinant factors and the enlarged constant from (2.20), are consequently the same bounds for the enlarged seed. The total variation is bounded before the selection sums by their absolute Cauchy-integral majorant.

After summing label subsets at each host, Y_0 is exactly the union of the resulting active hosts, whether their labels were ordinary, probes, or both. This restores precisely the union condition used in (2.27)–(2.29). The resummation above therefore yields, for the native regular construction, the termwise numerical majorant

$$
\sum_{\ell:\,Z(\ell)=Z}
u^{|J_\ell|}\|\Lambda_\ell\|_{\rm TV}
\leq m_*(Z)\;,
\tag{G.156}
$$

Here m_*(Z)=D_*b_*exp(−(1−8δ)Lκd_{j+1}(Z)/2), with D_* the fixed resummation factor C_3 divided by 2E_0C_1α_4^{-1}M^qexp(C_2κ_1) in the source's (2.38). It is small by the choice of b_*, and u is independent of g. This is the analogue of the V4 dummy comparison used in (G.146). It is a statement about absolute selected measures, because (2.15)–(2.26) dominate the absolute primitive integrands before the selection sums. Bounds only on the signed activities H(Z) would not suffice for it. The seed and τ details in the preceding two paragraphs were added after the second review.

The original last factor exp(O(α_5)|Z|) in (2.26) is sufficient for this resummation: (2.35)–(2.38) already pay it from the spatial decay and weakening factors. Thus the refinement (G.144) is not needed for this dummy-label argument. A large unpenalised mark is handled by inserting the small fixed numerical weights u and removing them only after using |J|≤|S_X| in (G.147), which costs exp(c_*|S_X|), rather than by removing the seed's spatial decay at the start.

This removes the numerical host-allowance question for a primitive of the native form. The remaining mixed application question is specific: show that the two-species conditional integral of (1.60), with arbitrary selected A_j and B_j bond hosts added to Y_0, has that absolute primitive majorant and component factorisation with the same fixed parameters. LFR I states the one-run mixed expansion; neither its signed output bound (1.70) alone nor the regular-case calculation above is a proof of this stronger selected-measure statement.

## 28. Checks on the Actual Mixed Input

### 28.1 The A_j Cutoff Is a Product Cutoff

LFR I p.183 supplies an important detail not present in the first review packet. Before (1.28), Bałaban explicitly completes the functions (1.9) to the whole integration domain Z_{j+1}∩Ω_{j+1}. The right side of (1.29) then contains their product over that domain. Each factor (1.9) is the indicator that all the bond norms in a specified set are below g_j^{-1}δ_j. Therefore their product is the product of the corresponding single-bond indicators over the union of those sets; repeated indicators are idempotent. The remaining restrictions of (1.3)–(1.8) and χ_k^{(n)} have been removed by (1.29), as confirmed on p.187. The B_j restriction (1.55) is also a product of norm-ball indicators.

Thus the mixed cutoff permits the same bondwise expansion used in RG II (2.3), separately for its two species. Coordinatewise zeroing preserves these two cutoff domains. This establishes the cutoff part of the proposed selected-label construction; it does not establish the bounds for the mixed potentials.

The component convention also needs to be retained: on p.177, Z_j abbreviates Z_j∩Z for the components currently being treated, while the operation on Z^c is unchanged. A zeroing in the centred insertion refers to the current integrated carrier, not to all occurrences of the letter A_j elsewhere in the density. If several components are integrated together and an insertion reads more than one, its selected label set spans those components; one cannot then assert that the insertion factorises between them.

### 28.2 The Obstruction to Applying (G.155) to Every Mixed Host

The original boundary input has only the bound CRE (2.42), B_0e^{-κd_i(X)}, uniformly in its admissible real retained variables. Its dependence on A_j is not assigned a small coupling factor by that statement. CRE pp.276–277 supplies a fluctuation gain for the change in its background argument; that does not by itself control the second line of (G.149) by a quantity tending to zero with g_j.

LFR I pp.191–192 handles the cumulation of the newly created boundary functions through the factor δ'_j and the at most N_0 overlapping terms. The suppressed notation in (1.70) does not remove their dependence on still-retained A variables: LFR II (1.49), p.369, explicitly writes both B_k(U_k'',A) and B_k''(U_k'',A), identifying the latter as the sum created by the preliminary integrations. Consequently the fixed small b_* in (G.155) cannot yet be assigned to every host of the mixed action without matching the source's cumulation argument with these arguments included. In particular, the fact that the *mark* is a bounded insertion does not make all the *unmarked inherited interactions* small.

The source already has a place for bounded, non-small interactions: CRE p.262 permits grouping terms by large-field components, with decay measured outside the component; LFR II (1.68)–(1.69) separates the small interactions extending outside components from a component term bounded by the old determining-set volume. The latter stays inside the full positive component kernel (1.71), whose complex normalised bound is (1.75). Any use of this organisation here must carry the marked inner expansion through the V(X^∼)/V(Y) split of (G.104). It cannot replace a partial component term by the exponential of a complete preliminary logarithm.

These checks identify the first unresolved mixed estimate more precisely than a missing generic KP bound: the selected-integral majorant must retain the bounded A_j-dependent inherited interaction, or first prove a smaller bound for the actual interaction from its construction. Merely substituting the regular b(g) from (G.152) would omit that interaction. No such substitution is made here.

### 28.3 Review Record

The isolated review `verification/isolated_reviewer/reviews/lf-gamma-bounded-mark-20261028-r1-review/review.txt` assessed §26 before §27 was added. It found the finite-difference and least-label summations valid under the supplied V4 selected-measure statements, and did not certify the mixed application. Its centring and real-measure qualifications have been incorporated in §26.1; the uniform test-host bound is now t_*=16. The gauge covariance reference is V4 `sec:c4-8-1`, line 5381. The review also requested supporting dependency excerpts and source evidence for the mixed input. Section 28.1 supplies the previously omitted cutoff construction. The native numerical allowance calculation in §27 and these later clarifications were not part of that review.

Sources: [LFR I p.177](../Balaban/tex/LFR1/parts/p177_corrected.tex), [p.178](../Balaban/tex/LFR1/parts/p178_corrected.tex), [p.183](../Balaban/tex/LFR1/parts/p183_corrected.tex), [p.187](../Balaban/tex/LFR1/parts/p187_corrected.tex); [CRE pp.261](../Balaban/tex/CRE/parts/p261_corrected.tex)–[264](../Balaban/tex/CRE/parts/p264_corrected.tex), [pp.276](../Balaban/tex/CRE/parts/p276_corrected.tex)–[277](../Balaban/tex/CRE/parts/p277_corrected.tex); [LFR II pp.377](../Balaban/tex/LFR2/parts/p377_corrected.tex)–[380](../Balaban/tex/LFR2/parts/p380_corrected.tex).

## 29. Spatial Summation of the Bounded-Insertion Expansion

The cube weight in (G.146) gives a spatial activity estimate in the same V4 setting. This calculation keeps the input's spatial decay rather than spending a fixed fraction of it at every application. It does not extend the underlying measures to the mixed integral or to complex exterior data.

Fix a coarser partition π_m nested over the final-domain partition π_1 of §26; m=1 is allowed. Let X be a connected union of π_m-cubes. For each X, let f_X depend on the integrated labels S_X incident to X and on fixed data in X, with uniform bound f_{*,X} on the domain specified in §26.1. Assume all these S_X lie in a fixed set S_0 of integrated labels, and write s_0=|S_0|. The measure and all its exterior data remain the same while X varies.

Expand the centred expectation of f_X by the selected-measure construction of §26. Every selected root contains a probe host incident to X; every vacuum cluster in the expanded joint ratio meets one of those roots. Let Y be the union of X and the π_m-cubes covering all the root and cluster domains in that term. Nested partitions imply that each π_1-cube belongs to one π_m-cube. Thus Y is wall connected. For every cube q in Y, with n as in §26,

$$
N_m(Y\setminus X)\leq n\;,
\qquad
\operatorname{dist}_m(q,X)\leq n\;.
\tag{G.157}
$$

The distance is the periodic nearest-neighbour distance between cube indices. A field label incident to X has an endpoint in X; its probe host contains a neighbourhood of that endpoint, so the coarse root cover actually meets X. This avoids replacing wall contact by an unproved intersection condition.

The linear size d_m is the continuous-tree size of RG I p.257. Starting with a tree in X of length arbitrarily close to its infimum, connect each component of Y∖X to that tree. A component of q new cubes can be traversed by q−1 centre-to-centre edges; one more edge joins it to an adjacent cube in X, and a segment of length at most √d in cube units joins that cube's centre to the original tree. Its added length is at most q+√d≤(1+√d)q. Consequently

$$
d_m(Y)\leq d_m(X)+(1+\sqrt d)n\;.
\tag{G.158}
$$

This does not use a positive lower bound on d_m for a single cube. In four dimensions 1+√d=3. Choose fixed κ_*>0 and ν>0 satisfying

$$
3\kappa_*+\nu\leq\theta\;.
\tag{G.159}
$$

For example κ_*=θ/6 and ν=θ/2 are allowed. This is the spatial rate proved by this corollary; it is not an assertion that V4's θ pays an arbitrary preassigned rate κ. Combining (G.157)–(G.159) with (G.146), and grouping each integrated scalar coefficient by Y, gives coefficients R_X(Y) with

$$
\sum_{Y\ni q}e^{\kappa_*d_m(Y)}\|R_X(Y)\|
\leq e^{-\nu\operatorname{dist}_m(q,X)}
f_{*,X}e^{\kappa_*d_m(X)}e^{c_*|S_X|}\;.
\tag{G.160}
$$

The norm is the uniform bound over the fixed insertion-data domain from §26.1. The right side of the selected-measure estimate is uniform there, so the same estimate holds with the supremum inside the coefficient sum. It is obtained from the factorwise majorants, not from moving a supremum through an inequality for the final expectation alone.

For a family of inputs define its local spatial norm by

$$
\|f\|_{\kappa_*,m}
=\sup_p\sum_{X\ni p}f_{*,X}e^{\kappa_*d_m(X)}\;.
\tag{G.161}
$$

Sum (G.160) over X and use

$$
e^{-\nu\operatorname{dist}_m(q,X)}
\leq\sum_{p\in X}e^{-\nu\operatorname{dist}_m(q,p)}\;.
\tag{G.162}
$$

For the output family R(Y)=Σ_XR_X(Y), the result is

$$
\|R\|_{\kappa_*,m}
\leq C_{\nu,4}e^{c_*s_0}\|f\|_{\kappa_*,m}\;,
\qquad
C_{\nu,4}\leq
\left(\frac{1+e^{-\nu}}{1-e^{-\nu}}\right)^4\;.
\tag{G.163}
$$

The torus sum is bounded by the corresponding infinite-lattice sum, so the constant is volume independent. The same κ_* occurs on both sides. The fixed prefactor C_{ν,4} and the exponential cost in the actual integrated label count are explicit; no contraction is claimed.

For a sequence of applications for which these same constants and domains are valid, the cost is exp(c_*Σ_rs_r)C_{ν,4}^{r_*}, where s_r is the actual integrated label count and r_* is the number of stages with a nonempty centred mark. Since each such stage has s_r≥1, it is at most exp((c_*+log C_{ν,4})Σ_rs_r). This gives the particular constant needed in (G.108), rather than an unspecified per-stage L_r. Verifying the mixed hypotheses and the source's available history reserve remains necessary before using that constant there.

The reserve can be matched at the level of constants as follows. If the label count in the actual mixed application gives Σ_rs_r≤C_sP_H, put C_ins=C_s(c_*+log C_{ν,4}). Add this to the Cauchy note's existing mark reserve: C_P^{new}=C_P+C_ins, rather than spending the old C_P a second time. With the Cauchy note's notation c_n=C_ℰ+C_λ(1+log g_n^{-2}), its condition (H) for every scale n becomes

$$
\begin{aligned}
3\cdot2^{d-1}L^d(C_{\mathcal E}+C_P^{\rm new})
&\leq R_n\;,\\
2^dL^dM^dR_n^d(c_n+C_P^{\rm new})
&\leq \frac18\gamma_0A_1^2p_0^2(g_n)\;.
\end{aligned}
\tag{G.164}
$$

For any fixed C_ins these are the same types of small-coupling restrictions as the original (H): R_n grows as a fixed power of log g_n^{-2}, while 2p_0>rd+1 under the exponent condition already stated in that note. Thus the potentially large fixed value of c_* does not force a new power of the history volume. It can require a smaller coupling threshold. Under (G.164), the existing history inequality pays the ordinary cost and the extra C_insP_H, and still leaves the original C_PP_H for its original mark-count use. This is the direct-product accounting of (G.107)–(G.108), not the earlier overestimate with p_r log L_r when log L_r itself already contains p_r. No threshold in the original Cauchy file has been changed here, and this reserve calculation does not supply the missing mixed-measure bound or its label count.

This is a spatial estimate for the interacting selected-measure expansion, including the physical vacuum ratio. It applies directly to the A-only centred insertion when that insertion has V4's measure and the common bounded domain. To use it for (G.112), one still needs the mixed absolute selected-measure bound discussed in §28, a common complex domain if the caller requires one, and the corresponding mixed-scale root and cluster weight. Equation (G.163) does not identify a mixed-domain weight with N_1 by refining all frozen coarse cells to the finest integration lattice. That refinement would reintroduce the volume loss the estimate is meant to avoid.

## 30. Keep the Bounded A_j Interaction in Its Actual Marginal

The failure of the direct joint dummy comparison suggests a specific way to organise the mixed integral. Use the literal K_A, K_B, domains and full interaction 𝒱_n of §23. Write a=A_j and b=B_j in this section only. Keep every inherited term and the Wilson coefficient-difference terms in 𝒱_n, and define

$$
V_A(a)=\mathcal V_n(a,0)\;,
\qquad R_B(a,b)=\mathcal V_n(a,b)-\mathcal V_n(a,0)\;.
\tag{G.165}
$$

Define an unnormalised B-kernel on bounded scalar functions h by

$$
\begin{aligned}
\mathcal Q_B(a;h)
&=z^{(j)}\int_{D_B}\chi'^{(j)}(b)
e^{-\frac12\langle b,K_Bb\rangle+R_B(a,b)}h(a,b)\,\mathrm db\;,\\
Z_B(a)&=\mathcal Q_B(a;1)\;,\\
Z&=\int_{D_A}\chi^{(j)}(a)
e^{-\frac12\langle a,K_Aa\rangle+V_A(a)}Z_B(a)\,\mathrm da\;.
\end{aligned}
\tag{G.166}
$$

The domains D_A,D_B here denote the real coordinate carriers from §23; the restrictions on field values remain in the displayed cutoffs. Z is exactly the product of integrals in (1.60), with z^{(j)} retained. Factors outside these integrals that are fixed under the variation of the boundary input cancel only in that input derivative. They must still be differentiated for a change of the run's couplings or Gaussian operators, as in (G.140).

For a perturbation F of the boundary input alone, let I_A(a)=F(U(0),a)−F(U(0),0) and I_B(a,b)=F(U(b),a)−F(U(0),a), with the local reset convention of §26.2. Differentiating the actual integral gives

$$
D_F\log Z
=\frac{1}{Z}\int_{D_A}\chi^{(j)}(a)
e^{-\frac12\langle a,K_Aa\rangle+V_A(a)}
\bigl(I_A(a)Z_B(a)+\mathcal Q_B(a;I_B)\bigr)\,\mathrm da\;.
\tag{G.167}
$$

In particular the potentially non-small term I_A is not a small ordinary Mayer vertex of the B-kernel. All of the unmarked A-only interaction V_A remains in the outer density. In R_B the corresponding inherited boundary contribution is exactly its background-change difference with a held fixed; the A-only value cancels algebraically. This is the place to apply the conditional B expansion and its marked counterpart, rather than treating both terms of (G.149) as if they had the same smallness.

For real physical data, both factors in (G.166) are positive, and the marginal

$$
\mathrm d\nu_A(a)
=Z^{-1}\chi^{(j)}(a)
e^{-\frac12\langle a,K_Aa\rangle+V_A(a)}Z_B(a)\,\mathrm da
\tag{G.168}
$$

is the actual interacting A_j probability measure. Thus the first term of (G.167) has modulus at most sup|I_A|≤2f_* when the input is bounded by f_* on both evaluation sets. This uses neither independence of A_j and B_j nor a Gaussian replacement. It also shows why estimating exp(V_A) and Z_B independently in the numerator, then discarding Z, is unnecessary at real data.

Equation (G.167) was deliberately written without dividing by Z_B(a). At complex backgrounds the nonvanishing of the joint Z does not imply pointwise nonvanishing of Z_B(a); a conditional normalisation by Z_B would require an additional proof. The unnormalised kernel formulation has no such requirement. The bound at real data is not a substitute for the caller's complex spatial activity norm. The remaining calculation for this organisation is a marked localisation of (G.167), with V_A in the marginal and the full Z retained, using the actual small bounds for R_B uniformly in the A_j box. The source's B-field fluctuation estimates do not by themselves prove that marginal localisation.

### Review and Working Status

The second isolated review is `verification/isolated_reviewer/reviews/lf-gamma-bounded-mark-spatial-20261028-r2/review.txt`. It checked the bounded-insertion and spatial summations in §§26 and 29, and the numerical label algebra and constant order in §27. It did not certify the mixed application. Its findings led to the direct-product correction of (G.107)–(G.108), the more explicit seed and τ argument, and the distinction between the native fixed ε_1 and a coupling-dependent cutoff. Those additions, the translated gauge-covariance details, (G.164), and the marginal organisation (G.165)–(G.168) were added after that review.

Both bounded-mark review runs completed with one external request, no gateway errors and no tool events. Their transmitted user packets were compared with the saved JSON packets and matched exactly. These are procedural checks only.

The active issue is therefore the full interacting marginal in (G.167), not another Gaussian moment calculation or another proof of the rooted cluster inequality. Sections 26–29 provide reusable bounds with stated scopes. They do not close LF-A(10), ingredient (γ), or the Cauchy estimate. V4 and the original Cauchy and LF files remain unedited by this work.

## 31. The Gaussian Part of the Inherited A_j Dependence

The actual construction gives more information than the bounded class estimate (2.42) alone. CRE p.258 specifies that the quadratic form in (2.21) is kept in the postponed operation only within each component; its cross-component terms are put into the boundary action. These terms should not be assigned a small ordinary Mayer weight without first identifying their Gaussian role.

At the original j+1 RG step, write H=C*Δ^{(j)}C on its free fluctuation coordinates. Split these into the integrated small-field carrier Λ and its retained complement D inside Ω_{j+1}. In this paragraph Λ means the corresponding free coordinates of Λ_{j+1}. Put

$$
C_\Lambda=H_{\Lambda\Lambda}^{-1}\;,
\qquad
S_D=H_{DD}-H_{D\Lambda}C_\Lambda H_{\Lambda D}\;.
\tag{G.169}
$$

For components D_α of the retained carrier, let S_D^{diag} be the direct sum of its diagonal blocks. The explicitly identified boundary term is

$$
B_{\rm cross}^{(j)}(a)
=-\frac12\sum_{\alpha\neq\beta}
\langle a_\alpha,(S_D)_{\alpha\beta}a_\beta\rangle\;.
\tag{G.170}
$$

Thus the quadratic part carried by the component operations and this boundary term recombine to −⟨a,S_Da⟩/2. This statement concerns the complete cross-component quadratic term specified in CRE (2.21), before any restriction to selected localisation domains.

Let w be the small-field variable integrated on Λ in CRE (3.25). It is not the B_j variable introduced in the later preliminary integration (1.60). The exponent in (3.25) contains the cross term and its compensator. Combining it with the retained quadratic form gives exactly

$$
\begin{aligned}
&-\frac12\langle a,S_Da\rangle
-\frac12\langle w,H_{\Lambda\Lambda}w\rangle
-\langle w,H_{\Lambda D}a\rangle
-\frac12\langle a,H_{D\Lambda}C_\Lambda H_{\Lambda D}a\rangle\\
&\hspace{2em}=-\frac12
\left\langle (w,a),H(w,a)\right\rangle\;.
\end{aligned}
\tag{G.171}
$$

With normalised Gaussian measures the same identity includes the normalisations, since det H=det H_{ΛΛ} det S_D. For any integrable scalar insertion F and the same interaction R and cutoffs χ on both sides,

$$
\begin{aligned}
&\int\chi(w,a)e^{R(w,a)}F(w,a)
e^{-\langle w,H_{\Lambda D}a\rangle
-\frac12\langle a,H_{D\Lambda}C_\Lambda H_{\Lambda D}a\rangle}
\,\mathrm d\mu_{C_\Lambda}(w)\,\mathrm d\mu_{S_D^{-1}}(a)\\
&\hspace{2em}=
\int\chi(w,a)e^{R(w,a)}F(w,a)
\,\mathrm d\mu_{H^{-1}}(w,a)\;.
\end{aligned}
\tag{G.172}
$$

For real regular data this is an identity of positive Gaussian disintegrations. It preserves the full interaction and every cutoff; it does not estimate an interacting integral by a Gaussian expectation. In the source's Lebesgue conventions the corresponding Gaussian determinant and (2π) factors, together with z^{(j)} and the vacuum-energy factors, remain those of the original formula. Equation (G.172) does not discard them from a two-run comparison.

There are two distinct uses of this identity. A mass-one conditional Gaussian can always be inserted to represent the retained Gaussian marginal; doing so leaves all the other inherited boundary interactions untouched. Restoring the original nonlinear small-field integration is stronger: it requires the complete effective-action contribution generated by that integration, together with its counterterms and cutoffs. A localised piece of its logarithm is insufficient. In particular (G.172) does not prove that every A_j-dependent boundary term is quadratic.

The relevant additional source fact is the actual recent history. In LFR I §1, h=k−N; the last N postponed operations have the form (2.21), and their characteristic functions have the simplified form stated on p.178 under the no-new-large-field condition. The input action at scale h depends on the fields A_0,…,A_{h−1}, by CRE (2.23), and not on A_j with j≥h, which have not yet been introduced. Hence the explicit A_j dependence at these later indices must be traced through the intervening conditional fluctuation integrations, their localisations and any action terms they generate. It is not an arbitrary initial bounded function of those later variables.

This identifies the next construction to be checked: retain the connected marked expansions of those defining integrals until the current preliminary integration has been performed, then apply the linear localisation and the V(X^∼)/V(Y) assignment to the marked graph list. Any such regrouping must be justified with absolute bounds before it is used. The exact Gaussian recombination above supplies one part of that construction; neither a uniform bound for the remaining nonlinear marked graphs nor permission to exponentiate a partial logarithm follows from it.

Sources: [CRE p.258, (2.19)–(2.23)](../Balaban/tex/CRE/parts/p258_corrected.tex), [p.270, (3.23)–(3.25)](../Balaban/tex/CRE/parts/p270_corrected.tex), [pp.271](../Balaban/tex/CRE/parts/p271_corrected.tex)–[272](../Balaban/tex/CRE/parts/p272_corrected.tex); [LFR I pp.177](../Balaban/tex/LFR1/parts/p177_corrected.tex)–[178](../Balaban/tex/LFR1/parts/p178_corrected.tex).

## 32. A Component Norm for the Non-Small A_j Interaction

The small ordinary-host comparison of §27 is not needed for the coefficient-algebra exponential inequality below. Its application to the full explicit A_j-dependent boundary interaction is conditional, however. In particular, LFR II (1.99) bounds R-generated boundary terms with relative decay, and the calculation below cannot replace that decay by the full d_m(X). Equations (G.179)–(G.180) have not been established for the complete boundary part of V_A in (G.165).

### 32.1 The Coefficient Norm

Fix one component H being treated by the preliminary operation, with h=k−N and h≤j<k. Let Q be its one-layer enlargement in the final π_k partition, containing the endpoints of the active free A_j bonds. This is a background support, not an integration carrier. The integrated A_j labels are the actual set S_j on D_A=Z_{j+1}∩Ω_{j+1} in (1.60), with the component restriction of LFR I p.177; write s_j=|S_j|.

For families of scalar coefficient functions a(Y), with connected Y∈𝔻_k containing Q, use

$$
\|\mathbf a\|_{Q,\tau}
=\sum_{Y\supseteq Q}
e^{\tau N_k(Y\setminus Q)}\|a(Y)\|_\infty\;.
\tag{G.173}
$$

The supremum uses the actual common one-run background domain and real retained-field cutoff domain of the terms being estimated. Both A_j and its reset to zero must be in the domain, as in (1.60); no complex A_j continuation is assumed. The norm below is taken before integrating A_j. The boundary coefficients are invariant scalar functions, and resetting integrated A_j coordinates commutes with their adjoint gauge transformation.

Multiply two families by taking the pointwise product of their coefficients and grouping by the union of the two supports. The union is connected because both supports contain Q. Since

$$
N_k((Y_1\cup Y_2)\setminus Q)
\leq N_k(Y_1\setminus Q)+N_k(Y_2\setminus Q)\;,
\tag{G.174}
$$

this is a normed algebra with a unit supported on Q, and

$$
\|\mathbf a\mathbf b\|_{Q,\tau}
\leq\|\mathbf a\|_{Q,\tau}\|\mathbf b\|_{Q,\tau}\;,
\qquad
\|e^{\mathbf a}\|_{Q,\tau}
\leq e^{\|\mathbf a\|_{Q,\tau}}\;.
\tag{G.175}
$$

This allows a bounded, non-small interaction in the exponent. It does not assert a small-activity KP criterion for that interaction.

### 32.2 Counting the Terms That Actually Read A_j

Let F_m(X,U,A) be a boundary term on X∈𝔻_m, bounded by b e^{-κd_m(X)}. Form the difference between its value at U=U_k^{(n+1)} and A_j as integrated in (1.60), and its value with precisely those integrated A_j coordinates reset to zero. This difference is zero unless the term reads a label in S_j; otherwise it is bounded by 2b e^{-κd_m(X)}.

Use the source's locality in the retained fields, CRE (2.41)–(2.42), and the corresponding localisation of (1.63). A bond read by a term restricted to X has an endpoint in X under the source's star convention. For each fixed label b∈S_j and each scale m, there are at most two π_m-cubes containing its endpoints. This count is independent of the ratio between the bond's scale and m; it counts labelled endpoints, not all sites along a refined bond.

Assign the term to Y=Q∪cov_k(X), where cov_k takes the smallest union of π_k-cubes covering X. Since X reads an active label with an endpoint in Q, the union is connected. Nestedness gives N_k(cov_k(X))≤N_m(X). Use the nondegenerate cube-count bound N_m(X)≤C_g(d_m(X)+5), including the single-cube case, from V4's localisation-domain geometry. Choose τ>0 so that κ−C_gτ is large enough for the anchored animal sum B(κ−C_gτ) to be finite. Then

$$
e^{\tau N_k(Y\setminus Q)}e^{-\kappa d_m(X)}
\leq e^{5C_g\tau}
e^{-(\kappa-C_g\tau)d_m(X)}\;.
\tag{G.176}
$$

Sum first over X reading a fixed active label and then over that label. The resulting coefficient family obeys

$$
\|\Delta_{A_j}\mathbf F_m\|_{Q,\tau}
\leq 4b\,e^{5C_g\tau}B(\kappa-C_g\tau)s_j\;.
\tag{G.177}
$$

Overcounting a term that reads several labels only enlarges this positive majorant. The elementary endpoint anchoring is what avoids a factor proportional to the number of fine sites in Q.

For the old boundary action B_k, only generations m≥j+1 can explicitly read A_j: A_j is first introduced at the j+1 RG step, as recorded in §31 and CRE (2.23). Thus at most k−j≤N old-generation families contribute, each with the bound B_0 of CRE (2.42).

For B_k^{(n)}, there are at most n≤N preliminary generations. A given such generation has the localisation (1.63) over at most N scale classes between h+1 and k, with bound C_0e^{-(1+3β)κd_m(X)} by (1.70). Its retained-field dependence is not discarded; LFR II (1.49) explicitly retains it. Bound its decay by e^{-κd_m(X)} and apply (G.177) to each scale class. Hence the complete boundary part

$$
V_A^{\partial}(a)
=(B_k+B_k^{(n)})(U_k^{(n+1)},a)
-(B_k+B_k^{(n)})(U_k^{(n+1)},0)
\tag{G.178}
$$

has a component-containing coefficient family with

$$
\|\mathbf V_A^{\partial}\|_{Q,\tau}
\leq C_{\kappa,\tau}(B_0N+C_0N^2)s_j
\leq C_\partial(N+1)^2s_j\;.
\tag{G.179}
$$

Here and in (G.178), all retained coordinates outside the current A_j integration remain unchanged. This estimate uses no δ'_j/ε_j gain and no assumption that the inherited term is small. Combining it with (G.175) gives the actual unmarked interaction bound

$$
\|e^{\mathbf V_A^{\partial}}\|_{Q,\tau}
\leq\exp\bigl(C_\partial(N+1)^2s_j\bigr)\;.
\tag{G.180}
$$

The new ordinary-host threshold in (G.155) is therefore not a condition needed for this part of the numerator. The regular fluctuation part, the Gaussian kernel and the physical denominator must still be combined with (G.180); their factors have not been suppressed in this statement.

### 32.3 The Price in the History Estimate

The exponent in (G.180) is charged once at its integration stage. LFR I p.198 allows N≤C_N(1+log g_k^{-2})^ν. On the weak-coupling window used by the Cauchy note, the couplings increase with the scale, so for j≤k this is at most C_N(1+log g_j^{-2})^ν. The cumulative cost is therefore of the form

$$
C\sum_j(1+\log g_j^{-2})^{2\nu}s_j\;,
\tag{G.181}
$$

provided the sum is over the actual integrations with their original labels. Repeating a prefix history volume at each stage would not give (G.181).

This is a larger logarithmic history cost than the one currently written in the Cauchy note. Paying it would require using a coefficient proportional to (1+log g_j^{-2})^{2ν} in its history allocation and choosing the free exponent p_0 so that p_0>r(d+2)+2ν. This also dominates the small-component requirement 2p_0>rd+2ν. It is compatible with the source conditions ν/2≤p_0−p_1−1 and 2p_1−(d+5)r_0>p_0 once p_0 is chosen sufficiently large; for example it is enough additionally to have p_0>(d+5)r_0+ν+4 so that an integer p_1 can lie between the two required bounds. These are proposed numerical choices within Bałaban's free parameters, not a claim that the presently recorded threshold (H) already pays (G.181).

The remaining analytic task in this route is now to bound the Gaussian-localised numerator and the inverse normaliser in the same component coefficient algebra. In particular, using (G.180) alone as a bound on a normalised expectation would still omit the denominator. The component grouping used here is the alternative explicitly permitted in CRE p.262; transferring it through the outer V(X^∼)/V(Y) assignment must be performed on complete coefficient families.

## 33. The Physical Denominator in the Component Algebra

### 33.1 Localised Representations and Their Products

Complete the coefficient algebra of (G.173). It is useful to allow different localised representations of the same scalar function: quotient by the families whose sum is identically zero on the common admissible data domain, with the quotient norm given by the infimum over representations. This kernel is closed, since evaluation is bounded by (G.173), and is an ideal, since evaluation preserves products. The resulting quotient is a unital Banach algebra. This is a norm on functions with localised representations; it does not identify their individual Y-coefficients.

Use the same construction for bounded functions of the actual real integration variables u=(A_j,B_j), on their cutoff domain, and the external data. Suppose the Gaussian and scalar part of the literal integral has a coefficient representation by finite complex measures μ(Y;v,du). Its norm is

$$
G_Q=\sum_{Y\supseteq Q}
e^{\tau N_k(Y\setminus Q)}
\sup_v\|\mu(Y;v,\cdot)\|_{\rm TV}\;.
\tag{G.182}
$$

The cutoffs are part of this integration operator. The source's scalar z^{(j)} and any Gaussian normalisations used in converting between Lebesgue and Gaussian conventions must be included in μ. Integrating a coefficient a(X;v,u) against μ(Y;v,du) and assigning the result to X∪Y gives an operator G between the two coefficient algebras with norm at most G_Q. It descends to their quotients because a zero integrand integrates to zero. This is a total-variation statement for the actual complex measures, not a positivity assumption.

### 33.2 Using the Already-Constructed Unmarked Logarithm

Let V be the complete interaction in (1.60), with both A_j and B_j dependence retained. Write Z=G(e^V) for exactly the integral referred to by (1.62), and let A_c be the explicit Wilson coupling correction in that equation. Bałaban's one-run creation term C satisfies the identity

$$
Z=e^{C-A_c}\;.
\tag{G.183}
$$

Consequently Z is invertible in the quotient algebra whenever C and A_c have finite coefficient norms, with the explicit representative e^{A_c-C}. There is no need to prove that Z is close to 1 in this norm. In particular,

$$
\|Z^{-1}\|_{Q,\tau}
\leq e^{\|A_c\|_{Q,\tau}+\|C\|_{Q,\tau}}\;.
\tag{G.184}
$$

For a variation of the boundary input alone, the full scalar insertion is I_F=F(U(B_j),A_j)−F(U(0),0). All the other kernel data are held fixed for this derivative. Its normalised response has the localised representative

$$
R_F=e^{A_c-C}\,G(e^V I_F)\;,
\tag{G.185}
$$

and hence

$$
\|R_F\|_{Q,\tau}
\leq G_Q
\exp\bigl(\|A_c\|_{Q,\tau}+\|C\|_{Q,\tau}
+\|V\|_{Q,\tau}\bigr)
\|I_F\|_{Q,\tau}\;.
\tag{G.186}
$$

This estimate permits the non-small contribution (G.179) in V. It keeps the physical denominator through its complete unmarked logarithm, whose one-run existence is a source input. No KP smallness of V_A^∂ is used. One can verify (G.185) directly with a scalar source parameter, or formally to first order with a variable ε satisfying ε²=0: G(e^V(1+εI_F))=Z+εG(e^VI_F), and the first-order part of its logarithm is (G.185). Thus the argument neither requires a uniform finite source-parameter disc nor divides by Z_B(a) at fixed a.

All factors in (G.185) are invariant scalars or integration operators acting on invariant scalars. The construction does not estimate open transport matrices separately. If the source correction A_c or the Gaussian kernel changes between the two runs, its change is a separate mark in this formula; the fixed-input calculation does not cancel those marks.

### 33.3 What the One-Run Creation Bound Supplies

For C=C_k^{(n+1)}, (1.63) assigns domains at scales m≥j+1 up to k, and every domain meets the actual integration region E_j=Z_{j+1}∖Z''_{j+1}. Let p_j count its scale-j sites with the fixed boundary enlargement needed for the star convention. At any m≥j+1, the number of π_m-cubes that meet E_j is at most a fixed multiple of p_j. Anchor a domain to one of these cubes and repeat (G.176)–(G.177), using the stronger decay (1+3β)κ in (1.70). This gives

$$
\|C_k^{(n+1)}\|_{Q,\tau}
\leq C_C(N+1)p_j\;.
\tag{G.187}
$$

The constants include the finite star enlargement and the anchored animal sum. There is no count of all fine sites in Q. This controls the creation-term part of (G.184). The coupling correction A_c is still displayed separately: its coefficient norm must be bounded with its actual profile and scale factors, rather than omitted from (G.186).

Equation (G.187) addresses the creation-logarithm contribution subject to its stated source-domain identification. Equation (G.179) does not yet handle the complete non-small A_j boundary interaction: its use of full-domain decay is not justified for the R-generated relative-size terms. Thus (G.186) remains a conditional algebra estimate. Its application still needs the norm of the full interaction, the measure norm G_Q, the coupling correction and the insertion norm, all on the same admissible data domain and with the actual history-point count.

### 33.4 The Outer Split Is Still Made After the Response

The quotient algebra does not justify taking the exponential of a partial logarithm as a complete integral. Choose the explicit representative on the right side of (G.185), carry its origin labels through the source's outer localisation, and only then assign its terms to V(X^∼) and V(Y). Its total evaluation is the exact normalised response; identifying its individual coefficients with the original per-X derivatives would require an additional compatibility statement. The component-grouped version of the Cauchy comparison can use a different localised representation only after its full output identity and norm transfer have been checked.

There is an additional source representation relevant to that check. LFR II (1.103) factors each surviving component operator into its mass T'_k(Y_i)1 and its normalised operator. It then expands the latter acting on the remaining boundary exponential. Pages 391–392 explicitly allow the resulting representation (1.104) in the induction; the remaining component operations are multiplication by their masses, and the new boundary domains contain a component. This already separates a non-small component mass from the small connecting interactions. The marked extension must retain the normalised operators while treating any inserted observable, rather than replacing them by their masses prematurely.

Sources: [LFR I p.189, (1.62)–(1.63)](../Balaban/tex/LFR1/parts/p189_corrected.tex), [p.192, (1.70)](../Balaban/tex/LFR1/parts/p192_corrected.tex); [CRE p.262](../Balaban/tex/CRE/parts/p262_corrected.tex); [LFR II pp.391](../Balaban/tex/LFR2/parts/p391_corrected.tex)–[392](../Balaban/tex/LFR2/parts/p392_corrected.tex).

## 34. Localising the Actual Mixed Gaussian Integration Operator

The Gaussian integration in (1.60) can be localised with its whole physical integration carrier kept in the seed. This avoids making the seed depend on which bounded boundary terms have been selected. It also separates the Gaussian estimate from the small-activity question that failed in §27.

### 34.1 The Real Precision and the Localised Perturbation

Let D be the disjoint union of the free A_j and B_j coordinate labels in (1.60), and let n_D=dim 𝔤 times the number of these labels. Let p_j be the integration-region point count of §33.3, so n_D≤C_Dp_j. The quadratic form in (1.60) is the block sum of K_A and K_B. Its coefficients are taken at the zero-fluctuation background; the terms produced by expanding the coefficients with respect to B_j belong to P^{(j)}(g_j,A_j,B_j), as part of the expansion of all the expressions described on LFR I p.187. Those terms remain in V, not in this Gaussian estimate.

For real regular data, PBG p.428 gives a uniform positive lower bound for C*Δ^{(j)}C and uniform exponential decay of this precision. Its inverse on the free coordinates is (3.158), with the decay and random-walk construction completed by Theorem 3.15 on p.432. The A_j precision is the retained Schur form of (G.169), with only its component blocks in the postponed operator, as specified after CRE (2.21). Each such block has the same positive lower bound: the Schur quadratic form is the minimum of the parent positive quadratic form over the eliminated coordinates, and is therefore at least γ_0 times the retained squared norm. Further restriction to the actual A_j carrier preserves this lower bound. K_B is the corresponding fluctuation precision. Thus the real reference block matrix K_R has

$$
\operatorname{Re}\langle u,K_Ru\rangle
\geq\gamma_0\|u\|^2\;.
\tag{G.188}
$$

Use the source's generalised random walks for the precision and the restricted propagator in the Schur expression. Products are localised by the union of their walk domains. In particular, every walk contribution to a matrix element of the compressed Schur form has endpoints in D. Take a seed S of LM-cubes covering D with the fixed buffer used in RG II pp.12–13; its cube count is at most C_Sp_j. Weaken only outside S, using the same complex circles as the source. A changed walk with an endpoint in D must traverse the seed buffer. Its exponential decay therefore supplies the small buffer factor, in addition to a summable endpoint kernel.

This is a bound on the compressed Schur expression, not a claim that the entire parent propagator changes little in operator norm when remote coefficients are weakened. The source walk estimates give, after summing the endpoint kernel,

$$
\|K(\sigma)-K_R\|
\leq C_K\bigl(\bar\alpha_j+e^{-cM}\bigr)\;,
\tag{G.189}
$$

where bar α_j denotes the dimensionless complex-background and current bounds entering the one-run operator construction. The N_0-dependent factors in LFR I (1.64)–(1.69) are included in this quantity. They are logarithmic factors by p.192, so bar α_j can be made uniformly small on the stated weak-coupling domain. The constants in (G.189) are those of the uniform one-run walk bounds; the assertion concerns the source's entire localisation polydisc, not arbitrary independent changes of the matrix entries. Choose the usual M and weak-coupling thresholds so that its right side is at most γ_0/2. Then the real part of the quadratic form of K(σ), on real integration variables, is at least γ_0/2.

### 34.2 A Measure Bound With All Cutoffs Retained

Use the literal Lebesgue form of the two Gaussian integrals. This avoids inserting a normalised covariance determinant and then forgetting its inverse. On every localisation circle the measure is

$$
\chi^{(j)}(A_j)\chi'^{(j)}(B_j)z^{(j)}
e^{-\frac12\langle u,K(\sigma)u\rangle}\,\mathrm du\;.
\tag{G.190}
$$

The two cutoff factors are fixed under this localisation and have modulus at most one; the same statement holds for the soft cutoff convention. All non-Gaussian factors are still in V. The z^{(j)} factors are the source's local constraint-normalisation factors on the active blocks. Their usual one-run local bounds, with any explicit coupling powers kept, have logarithm bounded by C_z(1+|log g_j|)p_j. Hence (G.188)–(G.189) give the total-variation bound

$$
\|\mu_\sigma\|_{\rm TV}
\leq e^{C_z(1+|\log g_j|)p_j}
\left(\frac{4\pi}{\gamma_0}\right)^{n_D/2}
\leq e^{C_G(1+|\log g_j|)p_j}\;.
\tag{G.191}
$$

No volume of a background localisation domain occurs in this Gaussian integral. Its dimension is n_D. This is an unnormalised measure estimate; the physical inverse normaliser is the separate factor (G.184).

Let μ(Z) be the coefficient obtained by the source's s-interpolation and Cauchy representation, with all variables outside Z set to zero. Every component of a nonzero Z must meet the seed S: the dependence on a remote cube occurs through walks connected to the physical endpoints. With r_Z=N_1(Z∖S), the Cauchy kernels give

$$
\|\mu(Z)\|_{\rm TV}
\leq e^{C_G(1+|\log g_j|)p_j}
e^{-(\kappa_1-1)r_Z}\;.
\tag{G.192}
$$

This is a measure coefficient before multiplying by an interaction or an insertion. A bounded Borel insertion in A_j consequently does not change the construction of the seed or the Cauchy variables.

### 34.3 Summing the Gaussian Localisations

For completeness, the needed seed-extension count can be made explicit. On the nearest-neighbour graph of LM-cubes, of maximum degree d_*≤2d, give each nonseed cube of Z a parent along a shortest path in Z to S, with fixed tie-breaking. This is a forest rooted at the seed cubes. A rooted ordered tree with t nonroot vertices has at most 4^t shapes and at most d_*^t embeddings. Dropping disjointness between the trees only enlarges the sum. Thus for a>log(4d_*),

$$
\sum_{\substack{Z\supseteq S:\
\text{each component meets }S}}
e^{-aN_1(Z\setminus S)}
\leq\left(1-4d_*e^{-a}\right)^{-|S|}\;.
\tag{G.193}
$$

There is no ambient-volume factor. Coarsening a localisation to the final π_k partition and adjoining Q can only reduce the number of added cubes outside Q; the fixed part of S outside Q, if present because of the star buffer, contributes at most C_Sp_j. Combining (G.192)–(G.193) with a=κ_1−1−τ gives

$$
G_Q\leq e^{C'_G(1+|\log g_j|)p_j}\;.
\tag{G.194}
$$

The constants require κ_1−1−τ>log(4d_*), a fixed strengthening of the ordinary localisation-circle choice. The background core Q has not been refined into integration variables or charged by its fine-lattice volume.

The source-level checks needed before accepting this application are the common walk prescription for the compressed Schur expression in (G.189), the identification of the zero-B_j coefficient used in (G.190), and the z^{(j)} bound in the literal normalisation convention. These are included explicitly because (G.194) is intended for the actual mixed integral, not for a newly chosen Gaussian model. The bound supplies the Gaussian part of (G.186); it does not estimate the remaining interaction or prove the final Cauchy comparison by itself.

Sources: [PBG p.428, (3.156)–(3.158)](../Balaban/tex/PBG/parts/p428_corrected.tex), [p.432, Theorem 3.15](../Balaban/tex/PBG/parts/p432_corrected.tex); [RG II pp.12](../Balaban/tex/RG2/parts/p012_corrected.tex)–[16](../Balaban/tex/RG2/parts/p016_corrected.tex); [LFR I pp.187](../Balaban/tex/LFR1/parts/p187_corrected.tex)–[192](../Balaban/tex/LFR1/parts/p192_corrected.tex); [CRE p.258](../Balaban/tex/CRE/parts/p258_corrected.tex), [p.273, (3.33)](../Balaban/tex/CRE/parts/p273_corrected.tex).

## 35. Updated Dependencies From the Recent Drafts

Updated on 28 October 2026 after reading the underlying derivations in the files below. This is a dependency update, not a new review or an acceptance of their unreviewed results.

### Available Derivations to Check and Reuse

| Input | Current location and content | Use here and limitation |
| --- | --- | --- |
| Multiscale lift and localisation tail | [Large-field draft](WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md), §4(d), *The Fine Side at the Multiscale Chain*, *The Lift ι_Y*, and *The Fine Side at Complex Points* (lines 451–471 and 598–608 in the revision below). The draft gives the real flow, the tail and moment defect, analytic continuation of the flow, and a quantitative complex bound. | These are now available derivations, labelled **derived, unreviewed**. Use them for the common-domain comparison at the stated members; do not keep listing the entire fine-side or tail construction as absent. The half-domain members U_1 and U_2 and the remaining admissibility qualifications are not covered automatically. |
| Current along the chain | Same draft, *The Current at the Multiscale Chain* (lines 472–507). The argument uses a fixed right inverse with a local Neumann correction, then a complex extension and the two-constants estimate. | Candidate input to the current part of the complex comparison. It is **derived, unreviewed**, with the conditions at the other members still relevant. It does not by itself establish the mixed Gaussian measure bound of §34. |
| Bound along the joint line of configurations | Same draft, *The bound of f on the disc*, *(F-H)*, and *The conditions at the other configurations* (lines 512–530). It applies the renormalisation to a minimiser times a regular perturbation. The Hölder treatment allows an O(k) excess and absorbs it by weakening the exponential rate. | The renormalisation and Hölder arguments should be reused and checked, not treated as wholly missing. The draft still routes the outstanding link-image conditions through U_{1,2} and (β). These are **derived/unreviewed reductions**, not an unconditional multi-variable bound for every caller. |
| Literal preliminary insertion | [Two-loop draft](WILSON_IT1_TWO_LOOPS_UNIFORM_BOUND_2026_10_27.md), *The operations keep the support* (lines 140–160). It retains A_j and B_j, evaluates the insertion at U_k^{(0)} of the original variables, and normalises its average by the integral (1.60). It also identifies the scaled cutoff as |g_jB_j|<δ'_j. | Use this account when specifying the numerator in §§23, 30 and 31. It prevents replacing the insertion by its value at the final background or discarding the preliminary average. It does not bound the mixed response or justify unwinding a partial logarithm. |
| Outer R-gas and vacuum cancellation | [D2.7 draft](WILSON_IT1_D27_CLOSURE_2026_10_26.md), item 15.3 (lines 150–154). It gives the ratio of the gas with the insertion to the unmodified gas, with the incompatible-cluster factor and the component operators retained. | Reuse the scalar ratio and cancellation when passing a mark into the outer expansion. Its stated R-evaluation and localisation qualifications remain; no norm on open transport tensors is imported into the gauge-invariant estimate here. |

The two-loop draft's M-factored domain (lines 99–105) is also relevant, but only where the function actually depends on the background through M. Its s=1 minimiser identity does not identify a decoupled s-configuration with a minimiser. The LF draft explicitly rejects the related single-background shortcut for the joint chain: its lifted endpoint generally is not run B's chain at any single background.

### What Still Has to Be Proved for This Attempt

**Source check for the marked activity bound.** FV here means Friedli–Velenik, *Statistical Mechanics of Lattice Systems*, Chapter 5. Theorem 5.4, printed p.224, was checked directly in the [local PDF](../Balaban/Balaban/Friedli_Velenik_2017_Statistical_Mechanics_of_Lattice_Systems.pdf); Theorem 5.8 and its proof are in the retained Chapter 5 extraction, printed p.228. In FV's notation δ is the compatibility factor and ζ=δ−1, so its condition (5.10) uses |ζ|. The roles of the three references are distinct:

- **Bałaban:** CRE (3.44)–(3.47) defines the marked numerator and its division by the unmarked partition function. LFR II (1.91) is the actual component-operator activity; (1.92)–(1.97) use relative spatial decay, and (1.103) keeps the non-small component mass separate from its normalised operator. These are the objects to match, with the preliminary insertion evaluated as specified in the two-loop draft above.
- **V4:** `lem:c5-5-2`, `lem:c5-5-6`, and the proof of `lem:vacuum-clusters` supply an explicit selected-measure majorant, its marked difference, and the joint vacuum cancellation within V4's hypotheses. The marked-difference proof keeps its Gaussian density fixed. Neither that hypothesis nor the selected-measure bound can be silently transferred to (1.60).
- **FV:** Theorem 5.4 bounds the cluster sum with one polymer fixed, once (5.10) is verified for the unmarked activities. Theorem 5.8 requires an analytic activity family and a single positive majorant valid throughout the complex domain. These results do not estimate the marked mixed-field integral. The fixed-root bound does not include the root's own activity, so multiplying it by a marked root leaves the marked root bound to be proved.

Accordingly, the calculation to pursue is the weighted absolute bound on Bałaban's actual H′_{I_F}(Z₀), uniformly over the required complex backgrounds, with the factor e^{a(Z₀)} supplied by FV and the relative spatial weight retained. V4 and FV already cover the subsequent cluster summation when their hypotheses hold. Another Gaussian moment lemma, another abstract KP proof, or real-background positivity alone would not discharge this marked-root estimate.

1. **The mixed interacting response.** Establish the required marked spatial bound for (1.60), including the bounded A_j-dependent interaction and the complete physical denominator. The available V4 results do not supply this application.
2. **The proposed component norm.** The review `verification/isolated_reviewer/reviews/lf-gamma-component-norm-20261028-r1/review.txt` leaves §32 conditional on retained-field locality and domain bounds for the preliminary terms, the old-generation count after R re-expression, the representation in force, and a joint-component reset/counting argument. It also requests constant-level geometry and animal-sum corrections. The newer lift/current calculations do not settle these points.
3. **The remaining entries of (G.186).** Match the Gaussian localisation and scalar normalisations in §34 to the literal mixed kernel, bound the rest of the interaction and the coupling correction in the same norm, and justify the outer V(X^∼)/V(Y) assignment. The coefficient-algebra identity alone is insufficient.
4. **The unresolved comparison inputs.** The [walk-factor draft](WILSON_IT1_WALK_FACTOR_DIFFERENCE_2026_10_28.md) still leaves Wδ-1, Wδ-2 and Wδ-3 open. The LF draft still has qualifications involving U_{1,2}, (β)/(δ), the renormalisation remainders r_z and r_z^s, and boundary-crossing near domains. The creation difference of B_k^{(n)} remains explicitly open in its LF-A(10).
5. **Final payment and observable application.** Verify the history allocation with the costs actually obtained, including stopped components, without repeated charges. D2.7 and the two-loop draft retain R-eval, R-round and R-att-ext qualifications, with R-member additionally present for the pair. Their status headings are not closure evidence for the present goal.

The next mathematical pass should use the preliminary insertion specified in the two-loop draft, check the newer complex-domain inputs at that precise evaluation point, and address the mixed response with the existing outer gas identity. This update does not authorise treating the new inputs as independently reviewed, and does not reopen the inactive deterministic calculations.

### Revisions Used

- LF draft: SHA-256 `7505cdddd650119e9b6c22ae6aa61a5d63591a0616c80b42d13589f5de472466`.
- Two-loop draft: SHA-256 `e6ecd1b00ca5fa469a8a06642f093fef2ee6a66bff51f083b906f6b018d4a557`.
- D2.7 draft: SHA-256 `6ada5ad7a21ed8320853d907a3d8394cc77a14b9c8385101bd3c6f12404027e5`.
- Walk-factor draft: SHA-256 `37ab9a86688ace1d243906ba4e2a2b0296a4b347c36109df8a671999aed4ae50`.

Only this separate repair note was edited for the dependency update.

## 36. Following the Proof of the Preliminary Integration

The argument below follows the proof referred to by LFR I (1.60)–(1.63). Its target is the marked activity in CRE (3.44), before the vacuum cancellation (3.45). The finite expansion is written out; its uniform weighted estimate is not proved. In particular, no assertion from §§32–34 supplies that estimate here.

**Comparison with the current derivations.** The subsequent reread of the notes gives the following inputs to reuse, rather than rederive:

- The LF note, §4(d)(ii), *The fluctuation fields A* (lines 424–431), identifies the surviving real A_j coordinates and their common Lebesgue measure in the two runs. The fields integrated on the component during the preliminary steps are removed before V(Y) is formed; its A argument is the remaining system. Cutoff differences and coupling factors remain separate marks. This identification does not bound the preliminary average.
- The same section, *The count* (line 520), already bounds the sum of the relative-tree connector majorants by C(κ)α times the number of collar cubes. Together with the internal-component bound (1.69), this gives the existing cost per history point. It is a count for the V(Y) representation at its stated arguments, not a bound for that representation at independently varied chain entries, or for the mixed root before V(Y) is formed.
- The Cauchy note §11(c)–(d), (11.2) and (11.4), already retains the exact history exponent through the preparatory case and separates the cost, volume and entropy payments. Use this allocation with the costs actually obtained; do not repeat it or charge an entire prefix history at every preliminary step.
- D2.7, item 15.3, gives the outer ratio-of-gases identity, including Φ(∅). V4's `lem:c5-5-2` gives the bounded-Borel selected-measure estimate under its small-host hypotheses; `lem:c5-5-6` gives its marked differences at the stated fixed Gaussian density. Their applications have the scope recorded in §§25–29.
- The two-loop note, *The operations keep the support* (lines 154–189), retains the preliminary variables and their average normalised by (1.60). Its support and evaluation-point arguments do not establish a complex total-variation bound for that average. D2.7's invocation of (1.75) for the later operation T'_k must not be read as an estimate for the earlier mixed average without the missing transfer.

The newer LF text also narrows the available analytic inputs. In *The Fine Side at Complex Points*, the bound for the flow on the non-critical Picard ball, agreement with the real lift, and the identification of the representative remain open. In *The bound of f on the disc*, the renormalised terms at non-minimising entries and the position sum of the Hölder excess remain open; the latter was previously described here as an available bound. The middle-layer widths of B''_k are now LF-A(11). These qualifications appear in the derivations themselves (lines 526–542 and 609–621, and *The joins*), not just in their status headings. They prevent treating the whole comparison chain as an established complex-domain input.

Thus the source calculation below starts after the existing variable identification, counting and history arguments. The missing step remains the weighted interacting estimate for (G.200) with its physical denominator; the LF note's §4(e), *Where they enter*, still lists the creation difference of C_k^{(n+1)} as open.

### 36.1 Background Variation and the Explicit Fluctuation Argument

Write the integrals inside LFR I (1.60) as \(Z_j(\vartheta)\), with \(\vartheta\) denoting the external fields, determining sets and couplings. Let \(D_A\) and \(D_B\) be the independent integration labels in its first and second integrals, respectively, and put \(u=(A_j,B_j)\). Keep the literal quadratic forms

$$
K_A=C^*\Delta_{\Lambda_{j+1}^c}^{(j)}C,
\qquad K_B=C^*\Delta^{(j)}C,
\qquad Q_j(u)=\langle A_j,K_AA_j\rangle+\langle B_j,K_BB_j\rangle\;.
\tag{G.195}
$$

Here \(K_A\) is the inherited form appearing in (1.60), not a principal restriction of \(K_B\). Write \(V_j\) for \(\mathbb P^{(j)}\) plus the entire curly bracket in that equation. Thus \(V_j\) includes both evaluations of \(\mathbb E_k+\mathbb R_k+\mathbb B_k+\mathbb B_k^{(n)}\), and both coupling-difference Wilson actions. With precisely the source's cutoffs and its factor \(z^{(j)}\),

$$
Z_j(\vartheta)=z^{(j)}\int
\chi_A(A_j)\chi_B(B_j)
\exp\bigl(-Q_j(u)/2+V_j(\vartheta,u)\bigr)\,\mathrm du\;.
\tag{G.196}
$$

The factors \(\chi_k^{(n+1)}\exp(A_k^{(n)}(U_k^{(n+1)},A_j=0)+E_0^{(j)})\) stand outside this integral in (1.60). They cancel between a numerator and denominator using the same preliminary integral; they have not been removed from the physical density. The separate coupling correction in (1.62) remains part of the comparison of \(\mathbb C_k^{(n+1)}\).

For a scalar boundary term \(F_X\), abbreviate its full background and current argument at fluctuation \(B_j\) by \(p(B_j)\), and its subtracted argument in (1.60) by \(p_0\). Every fluctuation argument other than the displayed \(A_j\) remains unchanged. The subtraction has two parts:

$$
\begin{split}
I_X(u)
&=F_X(p(B_j),A_j)-F_X(p_0,0)\\
&=\bigl[F_X(p(B_j),A_j)-F_X(p_0,A_j)\bigr]
 +\bigl[F_X(p_0,A_j)-F_X(p_0,0)\bigr]\;.
\end{split}
\tag{G.197}
$$

RG I (3.6)–(3.17), applied as CRE pp.276–277 prescribe, treats the first bracket with real \(A_j\) fixed. Its analytic substitution must include the current in RG I (3.13), including \(\Delta_{\mathbf U}^{\xi}\mathbf A-P_1\mathbf A+\mathbf F_1\). Controlling the background phase alone is insufficient. The Cauchy radius in (3.15) is fixed by all four quantities in (3.14); the derivative bound (3.17) is the bound on the original scalar divided by that radius. The factor \(\alpha_2^{-1}\) and the scale-dependent margins therefore remain in this adaptation. CRE p.276 then localises using the layer scales and the full PBG Theorems 3.7–3.10.

This proves the source's background-variation estimate only at arguments satisfying those domain conditions. Applying it to the comparison configurations still requires the current and domain checks in §35. It does not estimate the second bracket in (G.197) by a small fluctuation factor. CRE (2.41)–(2.42) gives locality and a uniform bound for the explicit real fluctuation argument, but does not assert its analyticity. If \(F_X\) is bounded by \(b_X\) at the two reset arguments, the available reset bound is \(2b_X\). For a term from a representation with relative tree decay, \(b_X\) retains that relative decay.

Both brackets are gauge-invariant scalars. CRE (2.41) makes the fluctuation argument transform by the adjoint representation; setting its active coordinates to zero commutes with this transformation. This split does not introduce an open-transport observable.

### 36.2 The Marked Mayer Integral With Both Variables Present

Use the localised interaction terms of the source construction, combined by their localisation domains, and write \(V_j=\sum_{Y\in\mathcal H}V_Y\). For a localised scalar insertion \(I\), the marked numerator is

$$
N_j[I]=z^{(j)}\int\chi_A\chi_B
e^{-Q_j/2}I\prod_{Y\in\mathcal H}\bigl(1+(e^{V_Y}-1)\bigr)\,\mathrm du\;.
\tag{G.198}
$$

This is the operation preceding CRE (3.44), with the additional \(A_j\) integration retained. It is initially an identity on the real integration domain. Its complex extension and uniform absolute convergence require the estimates below; writing the product does not establish them.

Fix a selected family \(\mathcal D\subseteq\mathcal H\). Let \(D=D_A\sqcup D_B\), and let \(D_0\subseteq D\) contain every integration label read by \(I\) and by the selected \(V_Y\). For a subset \(E\subseteq D\), set \(\chi_E=\prod_{b\in E}\chi_b\), where \(\chi_b\) is the corresponding source cutoff for its species. RG II (2.3) becomes

$$
\chi_D=\chi_{D_0}\sum_{P\subseteq D\setminus D_0}
(-1)^{|P|}\prod_{b\in P}(1-\chi_b)\;.
\tag{G.199}
$$

Consequently the term with this selected family and bad set is exactly

$$
J^I_{\mathcal D,P}
=(-1)^{|P|}z^{(j)}\int e^{-Q_j(u)/2}
\chi_{D_0}(u)\prod_{b\in P}(1-\chi_b(u))
I(u)\prod_{Y\in\mathcal D}(e^{V_Y(u)}-1)\,\mathrm du\;.
\tag{G.200}
$$

The supports in this formula include both species. The cutoffs on \(D_0\) keep the selected functions inside their fluctuation domains. Outside \(D_0\) the selected functions do not read the variables whose cutoffs have been expanded. For soft product cutoffs the same identity uses their actual complements.

RG II (2.5)–(2.14) next conditions and localises this integral. Its conditional covariance, cross term, compensating exponential and determinant factors must be obtained from (G.195). They cannot be copied from a \(B_j\)-only integral. Only after that operation and the connected resummation does (G.200) contribute to \(H'_I(Z_0)\). In particular, (G.200) is not itself an already localised or normalised polymer activity.

### 36.3 Where the Numerical Estimate Needs an Adaptation

RG II Lemma 2, (1.42)–(1.43), splits each ordinary interaction into a quadratic term with a small coefficient and a bounded small remainder. The enlarged auxiliary radius (2.18) turns those bounds into the quadratic allowance (2.19)–(2.20). This step must bound the interaction in the exponent of (G.200), as well as the marked factor.

The reset in (G.197) occurs in the unmarked action too. Treating the reset of the marked insertion as one bounded root does not remove the other resets from that action. Nor can their smallness follow just by increasing the tree-decay rate: RG I p.257 defines \(d_j(X)\) by a shortest tree intersecting all cubes of \(X\), so a one-cube domain can have zero tree length.

Bałaban's treatment of genuinely non-small terms is instead explicit in LFR II pp.377–379: terms confined to a component are summed into \(V(X^\sim)\), kept in the exponent of \(\mathbf T'_k(X)\) in (1.71), while the remaining connectors satisfy (1.68). Its estimate is then proved with that component's full integration and normalisation. LFR II (1.103) separates the component mass from the normalised operation only after this construction. These formulas explain the required separation; they do not identify the earlier double integral (G.196) with \(\mathbf T'_k\).

At the algebraic level, keeping a chosen family \(\mathcal C\) in the exponent is exact:

$$
I e^{V_j}
=I\exp\left(\sum_{Y\in\mathcal C}V_Y\right)
\prod_{Y\notin\mathcal C}\bigl(1+(e^{V_Y}-1)\bigr)\;.
\tag{G.201}
$$

In (G.200) the resulting root reads the union of the mark's labels and the labels of every term in \(\mathcal C\); all their cutoffs must therefore be included in \(D_0\). To use (G.201), the required adaptation is to assign the actual non-small terms to components, bound the corresponding interacting root on the localisation circles, and prove a small connector bound for everything left outside. The summation and relative spatial weight must follow the representation actually in force, including the relative bounds of LFR II (1.99). Neither a bound on the Gaussian part nor the identity (G.201) supplies this estimate.

Once this root estimate is obtained, CRE (3.44)–(3.46) supplies the cancellation against the original \(Z_j\); FV Theorem 5.4 bounds the attached unmarked clusters, with their root activity supplied by the estimate just described. The same construction with one changed input, cutoff or density factor is needed for the two-run comparison. V4's fixed-density marked-difference result covers only the terms for which that hypothesis is met.

The unresolved step is therefore the interacting estimate between (G.200)–(G.201) and CRE (3.44), with its physical denominator and history payment. The source trace has not closed it. It rules out transferring RG II (2.18) to all of the reset terms, or transferring LFR II (1.75) to the preliminary integral without constructing the corresponding component operation.

Sources: [LFR I pp.188–192](../Balaban/tex/LFR1/parts/p188_corrected.tex); [CRE (2.41)–(2.42)](../Balaban/tex/CRE/parts/p261_corrected.tex), [pp.276–278](../Balaban/tex/CRE/parts/p276_corrected.tex); [RG I p.257](../Balaban/tex/RG1/parts/p257_corrected.tex), [(3.10)–(3.17)](../Balaban/tex/RG1/parts/p272_corrected.tex); [RG II Lemma 2](../Balaban/tex/RG2/parts/p011_corrected.tex), [(2.1)–(2.7)](../Balaban/tex/RG2/parts/p012_corrected.tex), [(2.14)–(2.22)](../Balaban/tex/RG2/parts/p015_corrected.tex); [LFR II (1.68)–(1.75)](../Balaban/tex/LFR2/parts/p377_corrected.tex), [(1.103)–(1.104)](../Balaban/tex/LFR2/parts/p391_corrected.tex).

## 37. Gauge Alignment in the Mixed Integral

This calculation applies the existing alignment before comparing the densities in (G.196). It gives the exact marked numerator to estimate. It does not yet bound that numerator uniformly on the required complex class.

### 37.1 Transport of the Whole Integral

At fixed real external data use the common gauge of the LF note §4(c), *The gauge of the data*, together with the alignment of its §4(d). The Cauchy note §10.3 distinguishes the original axial representative from the Landau representative: the latter's block data are V^w, not V. Thus a change to this representative transports the block data and currents as well as the background. RG I p.276, before (3.29), explicitly also transports the fluctuation argument. For the R-operation, LFR I p.197 specifies the compensating transformations of V_h and V′.

For the following change of integration variables the real gauge transformation v is fixed with respect to the active A_j and B_j. It may depend on the external data of this preliminary step. An alignment chosen afresh from the fluctuated background is not covered by this change of variables. For a complex neighbourhood choose a particular real regular reference configuration used in its defining chart, fix v there and use that same real transformation throughout the neighbourhood. This does not require a canonical real part of every complex configuration. No complex adjoint transformation of the real integration contour is made.

Let R denote its block-diagonal adjoint action on the free A_j and B_j labels. It preserves the invariant Euclidean norms and Lebesgue measures. All exterior fluctuation fields are transported as external arguments, and the gauge-fixing conditions are pulled back with the integrand. The assertion is not that an untransported axial gauge fixing is invariant.

The elimination of constrained coordinates must use the transported chart. Indeed, write L_p for the linear constraints, including that chart's linear gauge conditions, and P_free for restriction to its free coordinates. The completion C_p is characterised by L_pC_p=0 and P_freeC_p=1. Transporting the constraints gives L_{p^v}R_full=R_constrL_p and P_freeR_full=R_freeP_free. Uniqueness of the completion therefore gives

$$
C_{p^v}R_{\mathrm{free}}=R_{\mathrm{full}}C_p\;.
\tag{G.202}
$$

This argument concerns the pulled-back gauge slice, not a newly chosen axial slice. It also transports the retained Schur form: its eliminated and retained coordinate blocks are preserved by the pointwise adjoint action, and conjugation commutes with forming the Schur complement. Thus neither quadratic form in (G.195) acquires a separate gauge error. Their refinement differences are still present.

Write the two actual densities, including z^{(j)}, as χ_A(u)e^{S_A(u)} and χ_B(u)e^{S_B(u)}, with run labels A and B distinguished from the fluctuation species. Pull run B back by R and denote its exponent and insertion by hats. In particular,

$$
\widehat S_B(u)=\log z_B^{(j)}
-\tfrac12\langle u,R^{\mathsf T}K_BRu\rangle+V_B(Ru),
\qquad \widehat I_B(u)=I_B(Ru)\;.
\tag{G.203}
$$

All background, current, remaining-field and gauge-chart arguments in V_B are those of run B; equivalently they can be written in the transported gauge using (G.202). Here K_B is the block matrix of both quadratic forms in run B, not just its B_j precision. There is no Jacobian factor from R. The norm cutoffs in (1.60) are unchanged by this real rotation; their run-dependent thresholds are not identified.

The actual mark on the common support is therefore

$$
D_j(u):=\widehat S_B(u)-S_A(u)
=\log\frac{z_B^{(j)}}{z_A^{(j)}}
-\tfrac12\langle u,(R^{\mathsf T}K_BR-K_A)u\rangle
+V_B(Ru)-V_A(u)\;.
\tag{G.204}
$$

The V terms retain P^{(j)}, the complete old-action subtractions and the coupling-difference actions from (1.60). In gauge-covariant notation their fluctuation arguments are the same u; background and current differences are measured after transport. One must not additionally insert a difference F(U,Ad(v)A_j)−F(U,A_j) while leaving U fixed: that would separate two parts of a simultaneous gauge transformation. If the transported exterior fields do not yet satisfy the matching used in the LF note, that mismatch remains in (G.204); the background alignment alone does not establish it.

### 37.2 Cutoff Marks Without Extending Either Action Beyond Its Domain

Order the finite set of shared integration labels, and write χ_r=∏_bχ_{r,b} for r=A,B. Define χ_{*,b}=min(χ_{A,b},χ_{B,b}) and χ_*=∏_bχ_{*,b}. These are the actual sharp or soft norm cutoffs of the preliminary integral. Put

$$
E_{r,b}=(\chi_{r,b}-\chi_{*,b})
\prod_{c<b}\chi_{r,c}\prod_{c>b}\chi_{*,c}\;.
\tag{G.205}
$$

Telescoping gives χ_r−χ_*=∑_bE_{r,b}. Each E_{r,b} is supported in its own run's cutoff domain, and its distinguished factor is bounded by |χ_{B,b}−χ_{A,b}|. Both actions are defined on the support of χ_*. Consequently the complete density difference is

$$
\begin{split}
\widehat W_B-W_A
={}&\chi_*\int_0^1
e^{(1-t)S_A+t\widehat S_B}D_j\,\mathrm dt\\
&+\sum_bE_{B,b}e^{\widehat S_B}
-\sum_bE_{A,b}e^{S_A}\;.
\end{split}
\tag{G.206}
$$

Here W_A=χ_Ae^{S_A} and \(\widehat W_B=χ_Be^{\widehat S_B}\). The interpolation in the first line is unnormalised. No nonvanishing interpolated partition function is assumed. The last two sums retain one local cutoff-difference mark and stay within the support where their own run's action is controlled. Their products of remaining cutoffs are the explicit hybrids to use in the marked expansion.

### 37.3 The Physical Normalisation

Let I_r be an integrable invariant scalar insertion on its own run's cutoff support, let Z_r be the physical preliminary integral, and let R_r[I_r]=N_r[I_r]/Z_r. The insertions need not be defined on the other run's exclusive support. Write c_A=R_A[I_A]. When the endpoint partition functions are nonzero, the comparison is

$$
\begin{split}
R_B[I_B]-R_A[I_A]
={}&\frac{1}{Z_B}\int\chi_*(\widehat I_B-I_A)e^{\widehat S_B}\,\mathrm du\\
&+\frac{1}{Z_B}\int\chi_*(I_A-c_A)
\int_0^1 e^{(1-t)S_A+t\widehat S_B}D_j\,\mathrm dt\,\mathrm du\\
&+\frac{1}{Z_B}\sum_b\int E_{B,b}(\widehat I_B-c_A)e^{\widehat S_B}\,\mathrm du\\
&-\frac{1}{Z_B}\sum_b\int E_{A,b}(I_A-c_A)e^{S_A}\,\mathrm du\;.
\end{split}
\tag{G.207}
$$

To verify the identity, use χ_r=χ_*+Σ_bE_{r,b} separately in N_B−N_A−c_A(Z_B−Z_A), and use N_A=c_AZ_A. The first two lines evaluate both insertions only on the common support; each shell integral evaluates only its own run's insertion. The resulting marks are an insertion difference, an interacting exponent mark D_j, and the local cutoff marks, all with the physical endpoint normalisation. This is an identity for the full interacting law, not an expectation under a replacement Gaussian. For the creation term (1.62), the target is instead log Z_B−log Z_A plus its explicit coupling correction. The integral of (G.206) gives Z_B−Z_A; bounding its relative size and controlling the logarithm still require the marked estimate.

If the two kernels differ only by a real gauge transformation, with all external fields and gauge conditions transported and equal couplings and thresholds, (G.202)–(G.204) give D_j=0, all E_{r,b}=0 and \(\widehat I_B=I_A\) for the invariant scalar insertion. Every term of (G.207) then vanishes exactly, before any absolute value is taken.

The remaining quantitative calculation is to insert the aligned operator and background differences from Cauchy §10 and the LF note into D_j, and estimate the marked connected expansion of (G.206). The multiscale interface, complex-domain and localisation qualifications of those inputs remain in force. The common gauge for U_0 is already constructed; its use for every preliminary background and every surviving exterior argument must be checked at that step. No new estimate for those unverified cases is asserted here.

**Review scope.** The isolated review `verification/isolated_reviewer/reviews/lf-gamma-gauge-transport-20261028-r1/review.txt` checked the finite pullback and telescoping identities, conditional on their stated covariance and chart hypotheses. It did not verify those hypotheses for every factor of (1.60), identify a suitable v for every preliminary background, or establish the interacting estimate. Its substantive application objections are the remaining-field matching, the fluctuated backgrounds and the connection of the independent-current comparison to the full density. The missing plus sign in (G.204) was corrected. Equation (G.207) was rewritten after review to keep insertions on their own supports; that repair has not received independent review. The review's transport check passed with one request, no tools and exact agreement with the supplied packet.

### 37.4 Separate Gauges on Components

The gauge need not be chosen by a single alignment problem covering all components. CRE (2.19) and LFR I (1.1) factor the integration operations over disjoint components X_i. For each matched component use its own real gauge v_i, fixed with respect to its active integration variables. If the change fixes the external representative, v_i must fix the prescribed exterior data. Otherwise those data and the boundary factors must be transported explicitly. On overlapping collars the gauges must agree, or the overlapping regions must be treated jointly; prescribing two different values at the same site does not define a gauge transformation.

There is already a componentwise choice for the gauge of U_0: the LF note §4(c), *The gauge of the data*, uses run A's axial–Landau gauge at the shared centres in both runs. This construction is applied to each component's own U_0 and its own Λ. LFR I p.197 gives the compensating changes of V_h and V′. This supplies the gauge choice for that stage of the R-operation. It does not by itself supply a small comparison for every earlier fluctuated background in (1.60).

Let D_i be the disjoint free-coordinate sets of the active components and R_i their adjoint transports. On their union take R=⊕_iR_i, with the identity on untransformed labels. This has absolute Jacobian one. For the full run-B quadratic matrix, its transformed blocks and an interaction reading several components are

$$
\widehat K_{i\ell}=R_i^{\mathsf T}(K_B)_{i\ell}R_\ell,
\qquad
\widehat V_Y(u)=V_Y\bigl((R_i u_i)_{i\in I(Y)},u_{\mathrm{ext}}\bigr)\;,
\tag{G.208}
$$

where I(Y) is the set of components whose variables V_Y reads. The external argument in this formula is unchanged only where its gauge is the identity; otherwise it denotes the explicitly transported argument. Thus (G.204)–(G.207) apply with separate component rotations. The integration operations factor; the full interacting density generally does not. In particular CRE p.258 puts the quadratic couplings between distinct retained components into the boundary action. Those terms and every connecting V(Y) must be transported by all the incident v_i before their differences are estimated. No comparison of isolated, independently normalised component integrals replaces the physical denominator in (G.207).

The quantitative target is consequently local: construct an admissible alignment on each component and its necessary collar, and bound the residual connecting activities with the existing relative-tree estimates. Separate gauges remove the requirement for one alignment construction over the entire union; they do not remove the fluctuated-background or boundary-matching estimates. This componentwise application was added after the review above.

### 37.5 Gauges Depending on the Group Integration Variables

The requirement in §37.1 that the gauge be independent of both active species is sufficient, but unnecessarily restrictive. Work first in the variables of LFR I (1.25), before V_j is replaced by B_j. For a complete component kernel, collect its group variables in V and all its pending Lie-algebra integration variables in A. Fix the history labels and external data. The two matched runs have the same shared V and A carriers by the LF note's *The fluctuation fields A*; the extra all-small-field step postpones no additional A variable. Write the kernel as W(V,A) times the common base measure dν(V) dA, retaining every cutoff, scalar normalisation and interaction in W. The measure ν includes the group constraints. No independence of A and V under W is assumed.

For each component choose a measurable real gauge v_i(V), independent of A, and let R(V) be the resulting orthogonal action on the A coordinates. Keep V unchanged. For every absolutely integrable kernel and insertion, Fubini's theorem gives

$$
\begin{split}
\int F(V,A)W(V,A)\,\mathrm dA\,\mathrm d\nu(V)
={}&\int F(V,R(V)A)W(V,R(V)A)\,\mathrm dA\,\mathrm d\nu(V),\\
\int |W(V,R(V)A)|\,\mathrm dA\,\mathrm d\nu(V)
={}&\int |W(V,A)|\,\mathrm dA\,\mathrm d\nu(V)\;.
\end{split}
\tag{G.209}
$$

For fixed V the inverse is A↦R(V)^{-1}A and its absolute Jacobian is one. In particular, no derivative of v_i with respect to V occurs. This is an exact identity for the interacting kernel, including a complex-valued kernel; it costs no factor in its total variation or in any history weight depending only on the fixed labels. Its partition function is unchanged. For complex external data keep the real gauge chosen at a specified real reference chart fixed as a function of V; this is not a complex contour change.

This permits the real alignment from VAR Proposition 2 to be chosen at the actual group data V, wherever the hypotheses of the existing alignment derivation hold. If the transformation brings run A's axial representative into the close Landau representative relative to the averaged run-B background, apply (G.209) to run A with the inverse adjoint action. The convention is fixed by the scalar identity below, not by a choice of which run receives a hat. For a gauge-invariant scalar F of the background/current data p and the explicit real fields,

$$
F(p,R(v)A)=F(p^{v^{-1}},A)\;.
\tag{G.210}
$$

Thus the transported scalar can be compared at the aligned backgrounds and a common A argument without differentiating F in A. This is relevant to the boundary terms, for which CRE (2.41)–(2.42) supplies gauge invariance and a bound at real A, rather than an assumed analytic extension in A. Group-variable gauge-fixing densities are kept in the exact kernel; a factor depending only on V is not changed by (G.209). The transport of the background-dependent completion and of mixed factors must still satisfy the chart conditions of (G.202).

There are two strict scope restrictions. First, A in (G.209) contains every Lie-algebra coordinate being rotated. At a preliminary step with some A coordinates still fixed, either the gauge fixes those coordinates or the formula is applied to the complete joint component kernel in which they are integrated. It cannot silently be applied to a conditional creation coefficient at fixed exterior A. Second, after a common parametrisation V_j=V_j(B_j), the allowed transformation is (A,B_j)↦(R(V_j(B_j))A,B_j). Rotating B_j as well by a B_j-dependent gauge would be a different nonlinear change of variables, whose Jacobian has not been computed.

There is a separate conditional support observation for an already constructed connector. It applies only when the gauge reads surviving arguments of that connector, not preliminary variables already integrated out in forming it. In LFR II p.377, a connector domain Y contains every component of Z^∼ that it meets. Suppose v_i reads surviving group data only in that component of Z^∼ and its fixed boundary data, all included in Y. Replacing the A coordinates of that component by R_i(V)A then introduces no new integration-variable dependence outside Y. For a connector bounded uniformly over the original real-field domain, provided the transported arguments stay in that domain,

$$
\sup|V_Y(V,R(V)A)|\leq\sup|V_Y(V,A)|
\leq\alpha e^{-(1+2\beta)\kappa d_{k,Z}(Y)}\;.
\tag{G.211}
$$

The same statement holds for the internal component bound (1.69). Consequently this substitution does not spend relative-tree decay or add a history-volume cost for such saturated domains. The domain qualification is essential: norm cutoffs are preserved by R(V), while any other restrictions must be pulled back and checked. A gauge reading a larger collar requires that collar in the support, and the collar count of the LF note applies only after that enlargement is accounted for.

Equation (G.209) gives a measure-preserving change on the full kernel when all rotated coordinates are integrated. Equation (G.210) uses only joint invariance, with no derivative in A. Equation (G.211) is a different, conditional statement about a surviving connector's arguments. These statements cannot be chained when the gauge in (G.209) reads preliminary variables absent from V(Y): their integration would produce a mixture of rotations of the remaining fields, not evaluation of V(Y) at one rotated argument. The preliminary marked integral must be controlled before that information is discarded, or the admissible gauge must fix the remaining coordinates.

The isolated review `verification/isolated_reviewer/reviews/lf-gamma-conditional-gauge-20261028-r1/review.txt` confirms the Fubini identity under its carrier and integrability hypotheses and identifies this representation mismatch. It leaves the actual local choice of gauge, domain stability and the residual refinement estimate unproved. It also asks for the free-coordinate covariance supplied by the existing D2.2(6) derivation below. Its transport check passed with one request, no tools and exact agreement with the supplied packet. The distinction between (G.209) and (G.211) was made explicit after that review.

### 37.6 The Nonlinear Constraint Map in the Transported Gauge

This covariance is already derived in `WILSON_IT1_D2_STEP_MAP_2026_10_22.md`, D2.2(6)(b1)–(b2), including C, h, \(\widetilde D\), the weakened operators and the nonlinear background map. The calculation below records its substitution in (G.202); it is not a new interaction estimate. V4's `lem:row-locality` also already proves the rowwise locality of the constraint correction.

The source evidence is RG I pp.265–268. Page 265 states that the transformation of the group field and its background induces B′↦R(v)B′ and preserves the expressions in (2.1). Page 267 defines h by its support on the eliminated bonds b_0(c) and L\widetilde Qh=1; its coefficient h(c) is the inverse pivot coefficient, multiplied by L^{-1}. Page 268 states explicitly that C is determined by V^{(k)}. Thus C is not background-independent. The invertible pivot used to define h also supplies the uniqueness of the linear completion C.

Write p for the background and its gauge chart, R_f for the adjoint action on the full relative-field coordinates, R_c for that on the constraint coordinates, and R_0 for that on the free coordinates. Gauge covariance of the group averaging and covariance of its small logarithm imply covariance of the constraint map

$$
\Phi_p(B)=L\widetilde Q_pB+\widetilde C_p(B),
\qquad
\Phi_{p^v}(R_fB)=R_c\Phi_p(B)\;.
\tag{G.212}
$$

The linear and nonlinear parts separately satisfy this identity. The pivot support is preserved by the pointwise adjoint action. Uniqueness therefore gives h_{p^v}R_c=R_fh_p and C_{p^v}R_0=R_fC_p. The latter is (G.202) for these actual coordinates.

The nonlinear correction in RG I p.267 is the unique small analytic solution of

$$
\widetilde D_p(B)=\widetilde C_p\bigl(B-h_p\widetilde D_p(B)\bigr)\;.
\tag{G.213}
$$

Substitution of R_c\widetilde D_p(B) into the transformed equation, using (G.212) and the covariance of h, proves \(\widetilde D_{p^v}(R_fB)=R_c\widetilde D_p(B)\). In particular, for the actual nonlinear argument in LFR I (1.60),

$$
gC_{p^v}R_0b-h_{p^v}\widetilde D_{p^v}(gC_{p^v}R_0b)
=R_f\bigl(gC_pb-h_p\widetilde D_p(gC_pb)\bigr)\;.
\tag{G.214}
$$

There is no uncancelled nonlinear gauge correction in this identity. At fixed v, differentiating the covariance of \(\widetilde D\) also gives

$$
I-h_{p^v}\widetilde D'_{p^v}(R_fB)
=R_f\bigl(I-h_p\widetilde D'_p(B)\bigr)R_f^{-1}\;.
\tag{G.215}
$$

Hence the determinant in the first term of RG I (2.12) is unchanged. Its analytic logarithm is unchanged on the branch fixed at B=0, where \(\widetilde D'(0)=0\). The Haar density in the relative group coordinates is likewise invariant under the real adjoint action. The constraint delta functions transform by the adjoint action on their outputs, with absolute determinant one. These statements retain the source's normalisation factors; they do not replace the nonlinear measure by a Gaussian measure.

All these are identities for a fixed gauge acting on the arguments. They may be used pointwise when a real gauge has been selected from V. Equation (G.215) is not the Jacobian of b↦R_0(b)b; differentiating that different map would produce additional terms. The admissible variable-dependent change remains the conditional A rotation of (G.209), with V, or its chosen coordinate b, left unchanged.

CRE p.267 says that the fluctuation-field linearisation and removal of delta functions use these same formulas with the operators determined by the multiscale domains. LFR I pp.187–189 applies that construction in the preliminary step. Thus the linear and nonlinear chart transformations have a source-level covariance argument. This does not assert that two refinements have identical charts: their gauge-aligned residual differences in C, h and \(\widetilde D\), as well as their reconstructed backgrounds, still require quantitative control. The calculation above removes a pure-gauge contribution to those differences. It was written after the review of §37.1–§37.3 and is not independently reviewed.

## 38. Estimate With A_j Held Fixed

This attempt returns to the order of integration in (1.25) and (1.60). The claim being tested is uniform convergence of the B_j expansion with A_j a real parameter. It is distinct from, and insufficient by itself for, the final A_j-integrated marked bound.

The review `verification/isolated_reviewer/reviews/lf-gamma-conditional-b-20261028-r1/review.txt` examined §§38.1–38.2. It did not validate or falsify (G.216), and left the Cauchy-domain premise of (G.220) open. It also requested source definitions omitted from that packet, including the cutoff reconciliation already present in the two-loop note and LFR II p.383. Section 38.3 was written after that packet and is not covered by the review. The review transport check passed with one request, no tools and exact agreement with the packet.

### 38.1 The Actual A_j Dependence of the New Potential

Put a=A_j and b=B_j. After the removals in (1.29), the A_j cutoff is the completed norm cutoff (1.9); the remaining group cutoffs and gauge-fixing densities depend on V_j. In CRE (2.23), E_k and R_k do not explicitly depend on A. LFR I p.182 keeps this form after the preliminary steps, adding new boundary terms only. Thus the a-dependence before changing V_j to b consists of its retained quadratic form and B_k+B_k^{(n)}.

Let K_A(b) denote the retained quadratic form of (1.25), evaluated at V_j=exp i[g_jCb−h\widetilde D(g_jCb)]V^{(j)}, before its expansion in b, and let K_A(0) be the form extracted in (1.60). The V_j coordinate change and its Jacobian are independent of a. Accordingly the proposed literal identification of the a-dependent part of P^{(j)} is

$$
P^{(j)}(g_j,a,b)-P^{(j)}(g_j,0,b)
=-\tfrac12\langle a,[K_A(b)-K_A(0)]a\rangle\;.
\tag{G.216}
$$

This identity is to be checked against the source's complete change of variables, in particular any earlier shift of a. It is not an assumption that a is a fresh independent Gaussian. Its reference form is the retained Schur form of (1.25).

Write B_\partial=B_k+B_k^{(n)}, U_b for the background at b in (1.60), and U_0 for its subtracted background. The non-small term

$$
W_A(a)=B_\partial(U_0,a)-B_\partial(U_0,0)
\tag{G.217}
$$

is independent of b. If (G.216) holds, the rest of the exponent, denoted R(a,b), is the sum of P^{(j)}(g_j,0,b), the quadratic correction in (G.216), the E_k and R_k background differences, the two coupling-difference actions, and

$$
B_\partial(U_b,a)-B_\partial(U_0,a)\;.
\tag{G.218}
$$

It vanishes at b=0. In particular, the non-small reset (G.217) is not an ordinary Mayer vertex in the conditional b integral. The corresponding exact organisation, already recorded in §30, is

$$
Z_j=z^{(j)}\int\chi_A(a)e^{-\langle a,K_A(0)a\rangle/2+W_A(a)}
\left[\int\chi_B(b)e^{-\langle b,K_Bb\rangle/2+R(a,b)}\,\mathrm db\right]\,\mathrm da\;.
\tag{G.219}
$$

The bracket is kept unnormalised. No inverse of a conditional partition function is introduced.

### 38.2 The Estimate to Check in the Conditional Expansion

The fresh b potential has the source RG II Lemma 2 bound. For (G.218), a is a fixed real parameter, and the source's background-variation proof applies with the uniform boundary bound at that a. Thus the missing smallness is not a Taylor estimate of the reset in (G.217).

The additional term to check is the quadratic correction in (G.216). Let r_{A,j}=δ_j/g_j and r_{B,j}=δ'_j/g_j be the actual dimensionless cutoff radii. A candidate consequence of the one-run operator analyticity and walk bounds is

$$
\|K_A(b)-K_A(0)\|_{\mathrm{row}}
\leq C_Kg_j\|b\|_\infty,
\qquad
\left|\tfrac12\langle a,[K_A(b)-K_A(0)]a\rangle\right|
\leq C_Kδ'_jr_{A,j}^2\,|D_A|\;.
\tag{G.220}
$$

Here the row norm is sup_xΣ_y|K(x,y)| in the scale-j free coordinates, and |D_A| counts actual integrated labels. The second inequality follows from the first on the cutoff support, up to a fixed group-dimension constant included in C_K. Its coefficient δ'_jr_{A,j}² tends to zero because δ'_j is g_j times a logarithmic power and r_{A,j} is logarithmic.

The proposed proof of the first inequality is to apply Cauchy's estimate to t↦K_A(tb). The operator bounds hold on a larger background domain than the activity bounds (RG II p.15). If the composed mixed-step background remains in that larger domain for |t|≤c/(g_j‖b‖_∞), with its exponentially summable kernel bound, Cauchy's estimate gives (G.220) with a volume-independent C_K. The required domain inclusion must be proved for the actual retained Schur form and the preliminary backgrounds; the larger radius cannot merely be inferred from analyticity on the shrinking activity domain.

Even (G.220) alone is not a local Mayer bound. To use RG II (2.18)–(2.20), the localised correction must have an anchored activity sum of order δ'_jr_{A,j}², uniformly in a and the integration domain. The source walk expansion provides the candidate localisation, but this anchored sum and its mixed-scale coarsening still have to be checked. A bound proportional to the entire |D_A| cannot be substituted for a small bound on each ordinary host.

If these checks succeed, D2.4(10)'s already derived marked-root estimate applies to the conditional b integral with a held fixed, with the enlarged small-potential constant. The remaining task is then the weighted a integration in (G.219), including W_A and the physical Z_j. At present (G.216) and the uniform localised version of (G.220) are the specific claims under examination, not established inputs. No new conditional-b convergence claim or refinement-small estimate is made yet.

### 38.3 Proposed Localised Estimate for the Retained Quadratic Correction

The following is the attempted proof of the local estimate required above. Its source application, particularly the uniform enlarged b-disc for the retained form, remains to be independently checked. The claim concerns an interaction in the actual exponent of (1.60), not a Gaussian moment estimate.

Use the generation-j free coordinates of the retained form in (1.25). The other pending fields remain fixed within their actual cutoff domains. Write the retained form as the restriction to retained component blocks of

$$
H_{DD}-H_{D\Lambda}H_{\Lambda\Lambda}^{-1}H_{\Lambda D},
\qquad H=C^*\Delta^{(j)}C\;,
\tag{G.221}
$$

where Λ is the previously integrated small-field region. This is the form in CRE (2.21). For a real regular reference, H has the uniform gap and exponentially summable kernel discussed at PBG p.428, and its restricted inverse has the bounds and walk expansion of Theorem 3.15. A sufficiently small fixed complex neighbourhood preserves these operator bounds. The norm of (G.221) is bounded by h_*+h_*²c_*, where h_* bounds H in row norm and c_* bounds the restricted inverse; restrictions to component blocks do not increase the row norm.

The b-dependence is induced by the group data in (1.53). In the intrinsic generation-j construction those group data are changed while the coarser data are held fixed. RG II (1.18)–(1.20), together with the current substitution RG I (3.13), bounds the resulting change in all the operator-domain quantities by Cg_j‖b‖_∞ in their generation-j units. The radius used here is the fixed larger operator domain of RG II p.15, not the shrinking domain of an old boundary activity. This must use the actual generation-j background determining K_A, rather than a replacement Hessian at U_k.

Here is the proposed control of the composition, including the step missing from a row-norm argument alone. For an operator family T_X(x,y) localised in connected generation-j domains, use the weighted row sum sup_xΣ_{y,X}e^{sN_j(X)}|T_X(x,y)|. If two such kernels are multiplied, their supports meet at the summed intermediate coordinate. The union is connected, N_j(X_1∪X_2)≤N_j(X_1)+N_j(X_2), and the weighted row sum of the product is at most the product of the two weighted row sums. Restrictions to Λ or D do not enlarge it. Thus the retained form (G.221), including its restricted inverse, has a controlled weighted expansion whenever its H and H_{ΛΛ}^{−1} factors do.

The source walk/Cauchy construction gives an exponential cost for each cube outside the fixed endpoint seeds. For any fixed s, its domain sum is finite after κ_1−1 exceeds s by the anchored-domain entropy and endpoint-count margin. This is the same order of choices as RG II (2.14)–(2.26): the walk scale is then large enough to dominate the weakening factors. It supplies finite weighted row sums for H and for the restricted inverse, independently of the number of integrated labels. No estimate of a whole sum by its number of fine sites is used.

The composition with the fluctuated background must be localised too. Apply RG II (1.13)–(1.18) to its nonlinear response, using the same weakening parameters in its propagators and local equations. Its field coefficients are rooted at their output point and have a weighted sup sum bounded by C_sg_j|t|‖b‖_∞ in the admissible field/current norms. Products of coefficients meeting one local stencil are controlled by support union, with a fixed stencil cost absorbed in C_s. The local analytic coefficient functions of H can therefore be expanded in that response on a fixed small ball of this weighted norm. For the restricted inverse use the series G_0Σ_{n≥0}(−δH G_0)^n, G_0=(H_{ΛΛ}(0))^{−1}, on the same weighted row algebra. It converges when ‖δH‖_s‖G_0‖_s<1/2. Choose r_* so that both this condition and the local coefficient radii hold whenever g_j|t|‖b‖_∞<r_*. All constants are fixed before g_j. This is the proposed derivation of a volume-independent enlarged t-disc for the composed retained form; its application to the actual mixed preliminary determining sets is the source-level point requiring review.

After resumming by support, denote the resulting coefficient by K_{A,X}(tb;x,y). It vanishes unless x,y∈X and reads b only in X. Taking s large enough gives the claimed bound

$$
\bigl|K_{A,X}(tb;x,y)\bigr|
\leq C_*e^{-(\kappa+\lambda+2)d_j(X)}\;,
\tag{G.222}
$$

where λ is fixed large enough for the anchored domain sum. The choice of the walk constants is made before g_j, as in RG II. The entry norm in (G.222) is invariant under its endpoint adjoint actions; the quadratic contraction below is an invariant scalar. This argument uses the weighted response estimate of the preceding paragraph for the actual mixed background, not merely analyticity of K_A at fixed independent background.

Subtract K_{A,X}(0;x,y) using the same coefficient representation. Cauchy's estimate on the enlarged t-disc gives

$$
\bigl|K_{A,X}(b;x,y)-K_{A,X}(0;x,y)\bigr|
\leq C\delta'_j e^{-(\kappa+\lambda+2)d_j(X)}\;.
\tag{G.223}
$$

For g_j small, the radius r_*/(2δ'_j) is greater than two, uniformly on the cutoff. This difference vanishes when X reads no active b label. Define Q_X(a,b) as its contraction with −a_xa_y/2, summed over the active a labels in X. There are at most C(d,L)M^dN_j(X) such labels. The correct cube count includes the degenerate domains: N_j(X)≤C_d(d_j(X)+5). Consequently

$$
\sup_{a,b\text{ on their cutoffs}}|Q_X(a,b)|
\leq C\delta'_jr_{A,j}^2
\bigl(d_j(X)+5\bigr)^2e^{-(\kappa+\lambda+2)d_j(X)}
\leq C'\delta'_jr_{A,j}^2e^{-(\kappa+\lambda)d_j(X)}\;.
\tag{G.224}
$$

The factors M^{2d} and the Lie-algebra dimension are included in C, fixed before the coupling. The same anchored domain count already used in the notes then yields the proposed interaction bound

$$
\sup_{\square\in\pi_j}\sum_{X\supseteq\square}
e^{\kappa d_j(X)}
\sup_{a,b\text{ on their cutoffs}}|Q_X(a,b)|
\leq C_Q\delta'_jr_{A,j}^2\;.
\tag{G.225}
$$

There is no total-volume factor on the right. This would be the small-host bound needed for this part of the conditional b expansion. The counting and Cauchy deductions (G.223)–(G.225) are conditional on the actual uniform operator-disc and localisation assertions above, and (G.216) is needed to identify Q_X with the complete additional a-dependent part of P^{(j)}. The attempt is therefore not recorded as closure of the conditional expansion or of the mixed marked estimate.

## 39. Contour Estimate for a Complex Retained Field

This is an attempt to prove an additional property of the actual boundary terms, rather than to assume arbitrary bounded functions of A_j are perturbative. The immediate target is the CRE (3.25) integral at the step where a retained field is introduced. The later propagation of the resulting analytic domain and its application to the preliminary integral (1.60) are separate requirements. No closure of those requirements is claimed here.

### 39.1 The Compensated Interacting Integral

In CRE (3.25) write a for the retained field on D and b for the integrated field on Λ. Put H=C*ΔC, G=H_{ΛΛ}^{−1} and m=GH_{ΛD}a. The cross term and the compensator in (3.25) satisfy exactly

$$
-\tfrac12\langle b,H_{\Lambda\Lambda}b\rangle
-\langle b,H_{\Lambda D}a\rangle
-\tfrac12\langle a,H_{D\Lambda}GH_{\Lambda D}a\rangle
=-\tfrac12\langle b+m,H_{\Lambda\Lambda}(b+m)\rangle\;.
\tag{G.226}
$$

Let T(a,b) denote the whole remaining interaction in (3.25): P^{(k)}, its curly bracket, and V^{(k)}(S_{k+1}). Retain their literal counterterms. Up to the a-independent source factor z^{(k)} times the Gaussian normalisation, the integral is

$$
\mathcal Z(a)=\int\chi(b)
\exp\bigl(-\tfrac12\langle b+m,H_{\Lambda\Lambda}(b+m)\rangle+T(a,b)\bigr)
\,\frac{\mathrm db}{\mathcal N_H}\;,
\tag{G.227}
$$

where \(\mathcal N_H=\int_{\mathbb R^{\dim\mathfrak g\,|\Lambda|}}e^{-\langle x,H_{\Lambda\Lambda}x\rangle/2}\,\mathrm dx\), on the source's analytic Gaussian branch. The compensator has not been dropped. Without T and χ, (G.227) equals one even for complex a in its Gaussian domain.

Use the actual norm cutoff radius r of this step and a retained-field radius s=c_0r, with c_0 fixed sufficiently small below. The action analyticity required on |a|≤s and on the tube |b|≤2r is the joint action property proved in O6 §§3, 7–8, under its R-m and R-m′ conditions. At weak coupling, 2g_kr lies within that domain since q_1>p_0. This is an assertion about the action, not an invocation of O6's already normalised expectation bound on the much smaller ω-polydisc.

On this tube use the bounded version of the source Mayer majorants. O6 §8 gives a summable bound ω_Y for each T_Y, including its quadratic-in-b part: on |b|≤2r that part is bounded by its coefficient times O(r²). The resulting amplitude is of order g_k times a fixed logarithmic power, including the displayed O(g_k(log g_k^{-2})^{3p_0}) contribution. Consequently |e^{T_Y}−1|≤2ω_Y once ω_Y≤1/2. This avoids enlarging a quadratic allowance and then producing an uncontrolled factor exp(Cr²) from a shift. All interactions are still present in the Mayer expansion.

Any T_Y reading no integrated b coordinate is kept directly as a local term in the exponent outside this expansion. Its exponential is nonzero, and its analyticity and bound are already the action inputs above. Likewise an insertion depending only on a passes through the conditional expectation unchanged. The nontrivial Gaussian polymers considered below therefore have a nonempty integrated-field seed.

### 39.2 Moving the Contour With the Cutoffs Present

For the shifted variable z=b+m, an original cutoff ball becomes the complex translate B_r+m. Replace it by the real translate B_r+Re m and its side boundary under the translation i Im m. Stokes' formula for the holomorphic Gaussian times the selected Mayer factors gives this identity. The side is parameterised by z=ξ+Re m+it Im m, with ξ∈∂B_r and 0≤t≤1. Its integration-form norm is bounded by |Im m| times surface measure. The same identity applies to the complement of the ball, with the opposite side orientation. For a soft radial cutoff, use its positive layer-cake representation by sharp balls and integrate this identity; the estimates below are uniform over its radii.

Perform this operation after selecting a Mayer family. Its ordinary good-field seed Y_0 includes every variable read by the selected interactions and by a holomorphic scalar mark F. Outside Y_0 expand the remaining cutoffs into bad sets P as in RG II (2.3). A contour side can occur only at a label in Y_0∪P. Let S denote its labels. The unrestricted coordinates have no side contribution. Every label in P∪S is consequently either outside a translated real ball or on its side boundary. The geometry does not acquire a new seed outside the existing Y_0∪P.

The side set S is an auxiliary label for the absolute bound. The actual analytic activity remains the original fixed-contour coefficient with labels (𝒟,P,Z_0); the side terms are summed to bound it. No activity is defined by treating Re m or Im m as holomorphic functions of the retained field.

The walk bounds for G and H_{ΛD}, with the common source weakenings, give |m|_∞≤C_m s. Choose c_0 so that C_m s≤r/4. On all the contours above, the original argument b=z−m stays in |b|≤r+C_m s<2r wherever a selected interaction or mark reads it. Hence their original holomorphic tube bounds apply. No indicator function is analytically continued.

### 39.3 The Boundary Term in the Interacting Majorant

Here is the proposed per-selection estimate, at the same operator-localisation circles as RG II (2.14). Keep the source's conditional Gaussian cross term and compensator together. Its real reference joint covariance in the auxiliary X and integrated b variables has a uniform upper bound; the small quadratic allowance of (2.16)–(2.25) preserves that bound and costs exp(Cα_5|Z|). On a contour side, the imaginary part is supported only on S and has norm at most C_m s per label.

For clarity, the finite-dimensional estimate used here is as follows. For a complex Gaussian precision J=A+iB, with A positive and with the source's uniform inverse and row bounds, a point x+iy satisfies

$$
\operatorname{Re}\langle x+iy,J(x+iy)\rangle
=\langle x-A^{-1}By,A(x-A^{-1}By)\rangle
-\langle y,(A+BA^{-1}B)y\rangle\;.
\tag{G.228}
$$

The last term costs at most Cs²|S|. The mean A^{-1}By is at most C's per coordinate by the row bound. Integrating the other real coordinates leaves a Gaussian marginal on P∪S whose covariance and inverse covariance are uniformly bounded. Its density is bounded by C^{|P∪S|} times an exponential decreasing quadratically in those coordinates. On every bad or side coordinate the distance from that mean is at least r/2 if c_0 is small enough. Surface integration contributes at most Csr^{dim 𝔤−1} per side label. Thus the proposed bound for a selected contour term is

$$
\begin{split}
|\mathcal J_{\mathcal D,P,S}[F;a]|
\leq{}&\|F\|_{\mathrm{tube}}
e^{-(\kappa_1-1)N_1(Z\setminus Z'_0)+C\alpha_5|Z|}
\prod_{Y\in\mathcal D}2\omega_Y\\
&\times C^{|P\cup S|}
\bigl(sr^{\dim\mathfrak g-1}\bigr)^{|S|}
e^{-c r^2|P\cup S|+C's^2|S|}\;.
\end{split}
\tag{G.229}
$$

This uses the correlated Gaussian marginal, not independence of the bad coordinates. In particular the imaginary-shift cost is supported on S; it is not exp(Cs²|Z|). Choose c_0 further so that C's²≤cr²/4, and take the weak-coupling threshold so the surface and determinant constants cost at most another cr²/4 per bad label. The final line of (G.229) is then at most exp(−c_1r²|P∪S|).

Sum over S⊂Y_0∪P. The choices on P cost at most 2^{|P|}, paid by part of its bad-field factor. The choices on Y_0∖P give at most (1+e^{−c_1r²})^{|Y_0|}≤exp(e^{−c_1r²}|Y_0|). The proposed result is therefore the source's primitive majorant, with a smaller fixed constant in its bad-field exponent and an exponentially small addition to the seed-volume allowance. It contains the entire selected interaction product and the scalar mark F.

### 39.4 The Remaining Source Application

Here is the proposed localised Gaussian construction for that application. Complete the source square before conditioning. The resulting zero-mean full covariance is the same covariance as without the retained source; the mean field restricted to a selected seed is m_0=(GH_{ΛD}a)|_{Z_0}. Introduce the source's common operator weakenings and denote the seed covariance and conditional cross operator of RG II (2.14) by G_σ and Γ_σ. Localise the mean using its own product of those source walk expansions, obtaining m_σ, with the same value m_0 at unweakened parameters. For a fixed selected family and fixed original cutoff domains, use the Gaussian factor

$$
\begin{split}
\int e^{-\frac12\langle\Gamma_\sigma X,G_\sigma\Gamma_\sigma X\rangle}
\int
\exp\bigl(&-\tfrac12\langle b+m_\sigma,G_\sigma^{-1}(b+m_\sigma)\rangle\\
&-\langle b+m_\sigma,\Gamma_\sigma X\rangle\bigr)
\,\frac{\mathrm db}{\mathcal N_{G_\sigma}}\,\mathrm d\mu_0(X)\;.
\end{split}
\tag{G.230}
$$

The selected interactions, mark and original cutoff domains multiply the integrand in b. Here \(\mathcal N_{G_\sigma}\) normalises the Gaussian with covariance G_σ. At unweakened parameters, (G.230) is the usual conditional representation of the original Gaussian marginal shifted by m_0, so it gives exactly the selected term of (G.227). For general σ it defines the analytic localisation family on the original, fixed b domains. The contour argument is an estimate of this family; it does not define its dependence on Re m_σ.

With z=b+m_σ, the joint precision in (X,z), at the real reference, is

$$
J_0=\begin{pmatrix}
I+\Gamma^{\mathsf T}G\Gamma&\Gamma^{\mathsf T}\\
\Gamma&G^{-1}
\end{pmatrix},
\qquad
J_0^{-1}=\begin{pmatrix}
I&-\Gamma^{\mathsf T}G\\
-G\Gamma&G+G\Gamma\Gamma^{\mathsf T}G
\end{pmatrix}\;.
\tag{G.231}
$$

The source row and column bounds for G and Γ give uniform covariance bounds. The operator perturbations and quadratic allowances of RG II (2.16)–(2.25) preserve them for sufficiently small source constants. This supplies the Gaussian marginal bounds used in (G.228)–(G.229); the total determinant/allowance cost remains exp(Cα_5|Z|). The imaginary displacement in this representation is confined to the contour-side b coordinates S, so its additional quadratic cost remains supported on S.

Use the same G_σ in the seed measure and the X-compensator in (G.230). With no cutoffs, interaction or mark, the b integral over the full real contour, followed by its permitted entire Gaussian translation, cancels the X-compensator exactly. Such a component has mass one for every m_σ. When the common weakenings separate spatial components, the Gaussian operators and the mean's walk expansion separate with them. A component containing no selected host, cutoff label or mark therefore contributes one and produces no polymer. Contour-side labels lie in Y_0∪P, so this construction gives the same seed and connectivity condition as the original primitive expansion. This is the proposed reason the contour estimates can enter the source resummation, rather than only bound a global integral.

The proposed conclusion is that the already derived RG II/D2.4 resummation now gives uniformly convergent unmarked and marked series for |a|≤c_0r. The unmarked series would prove nonvanishing of the physical compensated normaliser; the marked series retains its vacuum ratio. Analyticity in a comes from the original fixed-contour integrals and uniform convergence, not from treating Re m as a holomorphic function. This would provide a growing complex a-domain for the boundary terms at their creation. Propagation through later T and R operations, followed by the moderate/large-A_j split in (1.60), is still required. The contour estimate and the localised-family construction (G.230) are unreviewed; in particular their claimed compatibility with the actual source weakening and support geometry is not yet accepted. No wide-A_j analyticity assumption is inserted into the main argument as a proved fact.

### 39.5 Review, Saved Source Observations and Pause

The completed review is `verification/isolated_reviewer/reviews/lf-gamma-retained-contour-20261028-r1/review.txt`. It found the compensated shift, the contour-side Gaussian marginal calculation and the locality of the imaginary-shift cost mathematically sound under the stated inputs. It explicitly assessed this as a substantive per-term estimate for the interacting kernel. It did not validate the uniform zero-free cluster expansion or its application to (1.60). This paragraph supersedes the preceding pre-review status sentence, not its mathematical qualifications.

The remaining application checks are:

1. Identify the covariance on the free integrated coordinates explicitly. PBG (3.157)–(3.158) distinguishes the full constrained covariance from the free-coordinate inverse. The compensator in CRE (3.25) must use the latter in the block formula (G.226). The earlier §31 calculation is relevant; the review packet did not make this identification explicit enough.
2. Show that the young-field cutoff inside the conditional integral reads only the integrated labels, with every retained-field indicator left in the outer operation. State the dimensionless radius r and its source calibration. The known rescaling corrections must be supplied, not reopened as if they were new discoveries.
3. Address the smooth cutoff g in V^{(k)}. O6 proves analyticity at frozen cutoff values, so it is not enough on its own to infer a wide retained-field complex domain.
4. Construct the mean's weakened walk expansion, prove the uniform circle bound |m_σ|_∞≤C_m s, and show that each component reads only its own retained-field labels. The compensator must use the same Gaussian data.
5. Supply the resummation for polymers meeting Λ^c. D2.4(10)'s interior statement alone excludes exactly these boundary polymers; D2.6 §2.2–§2.4 is needed.
6. State the tube norm of the actual marks. The contour proof does not apply to arbitrary bounded-Borel marks or directly to the distributional cutoff derivative in CRE (3.28).

The small complex ball |a|≤c_0r is deliberately not the whole physical retained-field support. In particular it excludes the physical support of a newly selected large-field event. Applying it later requires an exact moderate/large-field split and a bound for the latter under the interacting law; this has not been done. Propagation of the analytic domain through subsequent T and R operations is also unproved.

Source observations read before the pause, saved without claiming their application is complete:

- CRE pp.251–252 defines the smooth cutoff in (1.22): g(a′)=0 for |a′|≤(4/3)g_k^{-1}δ_k. On the protected bonds the proposed real ball |a|≤c_0r lies in this zero plateau; the candidate analytic germ there is the constant zero. CRE p.269 uses g≡1 on the remaining shifted bonds. This gives a possible resolution of the V^{(k)} issue on the small ball, not an analytic continuation of the smooth transition region.
- CRE p.269, (3.20)–(3.23), separates the young small-field region from R and S. For sharp norm tests the product of overlapping cube tests can be written as a product of distinct bond indicators and split between integrated and retained bonds. This is the candidate exact cutoff assignment to verify against the source's star convention. A soft-cutoff layer cake must have all radii bounded below by a fixed positive multiple of r.
- For the mean, the contemplated construction is to expand G and H_{ΛD} into source walks, multiply their kernels at the intermediate label, and assign the union of their footprints to the product. Mark each cube of that union once. On the source circles the weighted absolute row sums would give C_m≤C_GC_H. A surviving connected footprint includes both the integrated endpoint and the retained endpoint; setting weakenings outside Z to zero would then restrict the retained labels to the same component. This construction and the required weighted row bounds have not yet been written and checked as a complete repair.
- If a wide analytic retained-field bound were eventually proved, Cauchy's estimate on a half-ball would bound a reset F(a)−F(0) by C‖F‖‖a‖/s, and hence by a small coefficient of 1+Σ|a_b|² when s grows. The intended next probabilistic step would put this into the source's quadratic-plus-bounded Mayer estimate and keep |a|≥s/2 as large-field polymers. No interacting tail bound, propagation theorem or closure is inferred from that conditional observation.

All four recent reviews have finished. The latest review's isolation manifest passed, with one request, no tool events or gateway errors, and exact equality between the saved packet and the transmitted packet. These are workflow checks only. Mathematical work and the five-minute heartbeat are paused; no review or author process from this session remains running. The handover and portable bundle preserve the current files and the review evidence.

### 39.6 Source Coordinates, Cutoffs and the Weakened Mean

29 October 2026. The calculation here addresses the source application of (G.229), specifically its use of a uniformly bounded, component-local mean on the localisation circles. Its first caller is (G.230), before any polymer resummation. The covariance and cutoff checks are preparatory; the new estimate is (G.235). This is a proposed repair, awaiting isolated review. It does not assert a marked mixed-integral bound or a zero-free normaliser.

**Coordinates and compensator.** The free bond coordinates are those remaining after eliminating the bonds b₀(c) in RG I p.268. That page explicitly defines C^{(k)}=(C*Δ^{(k)}C)^{-1} on these coordinates. CRE p.267 applies the same elimination and rescaling, with the operators determined by the sequence {Ω_j}; CRE (3.23)–(3.25) then splits these coordinates between Λ=Λ_{k+1} and D=Ω_{k+1}∩Λ_{k+1}^c. Throughout this paragraph restrictions mean restrictions of the free-coordinate matrices, not restrictions after applying C. Thus, with H=C*Δ^{(k)}C,

$$
G_\Lambda=(H_{\Lambda\Lambda})^{-1},
\qquad
m=G_\Lambda H_{\Lambda D}a,
\qquad
Q_D=H_{D\Lambda}G_\Lambda H_{\Lambda D}\;.
\tag{G.232}
$$

The C^{(k)}(Λ_{k+1}) between the two H factors in CRE (3.25) is this free-coordinate Dirichlet covariance, extended by zero. It is not the unreduced covariance denoted C^{(k)} in PBG (3.157): PBG (3.157)–(3.158) gives that unreduced covariance as C G_Λ C*, and its restriction to the free bonds as G_Λ. Inserting C G_Λ C* between the two free-coordinate H factors would count C twice and would not be (G.226). The normalisation is unchanged: if Z_phys is the integral with the cross term but without the negative compensator, and Z_comp is (G.227), both with the same Gaussian normalisation and all interactions, then Z_phys(a)=exp(⟨a,Q_Da⟩/2)Z_comp(a). CRE (3.23) retains the opposite compensator in the outer operation. No physical scalar factor is discarded.

**Cutoff dependence.** Put r=δ_k/g_k, the cutoff of CRE (3.16) in the Gaussian variable after the rescaling A′_k = g_kA_k of p.267 l.42, as LFR II p.380 l.42–45 fixes it (§55.7); in particular r=A₁(log g_k^{-2})^{p₀}. This is the dimensionless cutoff, not δ_k. For the fixed family of good cubes in (3.16), let E be the union of their literal bond sets (□′^{∼2})^{(k)*}, with their original star convention. Because the tests are sharp sup-norm tests, repeated tests on a bond are idempotent. Writing E_Λ=E∩Λ and E_D=E∩D gives exactly

$$
\prod_{\square'\ {m good}}
\mathbf 1_{\sup_{b\in (\square'^{\sim2})^{(k)*}}|A_k(b)|<r}
=\prod_{b\in E_\Lambda}\mathbf 1_{|b_b|<r}
\prod_{d\in E_D}\mathbf 1_{|a_d|<r}\;.
\tag{G.233}
$$

Here b_b denotes the integrated field at the bond labelled b; the original cube sets, rather than a guessed one-layer collar, define E. CRE p.269 guarantees small-field tests on Λ_{k+1}^{∼}; their union covers the integrated coordinates. Its collar can include retained coordinates: the notation χ^{(k)}(Λ_{k+1}) must not be read as proof of independence of a. Allocate every retained indicator to the outer integrand before taking the logarithm of the inner integral. The identity is for the full product, including (3.21); duplicate indicators remain idempotent. The bad-cube tests in (3.21) and χ_k′(S_{k+1}) stay in the outer operation. Their bond sets are disjoint from Λ. This is presupposed by Bałaban's (3.23) and (3.25), which place χ(Ω∩Λ^c,S) in the outer operation. The count of the two layers of □′^{∼2} (L²M₂R_{k+1}-cubes) against the one LMR_{k+1}-layer of (3.20) is not done here. On the real ball |a|_∞≤s=c₀r, c₀<1, the allocated good retained indicators equal one. The proposed holomorphic inner function agrees there with the original inner function; it does not analytically continue any indicator. There is no division by an outer indicator, and no assertion of agreement outside this ball.

CRE pp.251–252, (1.22)–(1.24), and p.269 settle the smooth-cutoff question on the same ball. On the protected bonds (R_{k+1}^{∼2}∩S_{k+1})^{(k)*}, g(a)=0 for |a|≤4r/3. The change Ψ(a)=a, all derivatives of g vanish, and its Jacobian is one there. The analytic germ used on the complex ball is precisely Ψ(a)=a. On S_{k+1}^{(k)*} outside that protected set, the source prescribes g≡1; the BCH change and its Jacobian are analytic in the same chart. S_{k+1}⊂D, so no smooth transition function is evaluated on a deformed integrated coordinate. The action difference still includes every term of the previous action as required by p.269. This establishes the cutoff germ only; the bounds for the composed actions retain O6's R-m and R-m′ hypotheses.

**Mean construction.** Fix the seed Z₀ and its hull Z₀′ from RG II pp.13–15. Use the source walk construction with the distinguished localisation domain inside Z₀′ and the remaining domains separated from Z₀ as on p.13. The finite-range factors C and C* are included in the footprints. Expand G_Λ and H_{ΛD} into their source walk terms G_ω and K_ν, respectively. The construction for G_Λ is PBG (3.185)–(3.187), restricted to the free coordinates by (3.158); that for H uses PBG pp.427–428 and RG II p.13's expansion of the operators determining Δ_k, as already used in D2.6 §2.2(2). A term's footprint F_ω or F_ν is the union of its enlarged localisation domains, including endpoints and the range of C. The source's connected walk or tree structure makes each footprint connected. This uses Bałaban's stated expansions and their absolute estimates; it is not inferred from decay of the summed kernels alone.

Let n(F) be the number of cubes of the localisation partition outside Z₀′ intersecting F. For |σ(Δ)|≤exp(κ₁), define

$$
\begin{split}
m_\sigma(x)
={}&\sum_{y\in\Lambda}\sum_{d\in D}
\sum_{\omega,\nu}
\left(\prod_{\Delta\cap(F_\omega\cup F_\nu)\ne\varnothing\,,\ \Delta\not\subset Z_0'}
\sigma(\Delta)\right)
G_\omega(x,y)K_\nu(y,d)a(d)\;.
\end{split}
\tag{G.234}
$$

The sums include only terms with the indicated nonzero kernels. The source partition and collars are fixed, and every footprint is marked once. At σ=1 the series is absolutely convergent and equals (G_ΛH_{ΛD}a)(x). In general it is not G_{Λ,σ}H_{ΛD,σ}a: that product marks an overlapping cube twice. No inverse identity between separately weakened operators is used. The Gaussian seed covariance in (G.230) is C^{(k)}(Z₀,σ), a different operand from G_Λ in (G.232); it and the X-compensator remain exactly paired as in RG II (2.14).

Here are the quantitative payments in the circle bound. Choose μ>0 below half the exponential rate reserved for endpoint distance in the source walk estimates. For each of the two expansions use the absolute weighted row constants

$$
\begin{split}
B_G&=\sup_x\sum_{y,\omega}
e^{\mu d(x,y)+\kappa_1 n(F_\omega)}\|G_\omega(x,y)\|,\\
B_H&=\sup_y\sum_{d,\nu}
e^{\mu d(y,d)+\kappa_1 n(F_\nu)}\|K_\nu(y,d)\|\;.
\end{split}
\tag{G.235a}
$$

The distance is the unit-lattice distance at this RG step. PBG p.428 states uniform decay and bounds for both unit-lattice operators; the absolute walk estimates supplying these constants, rather than only that summed decay statement, are (3.108), p.427's tree version, (3.185)–(3.187), and RG II (1.7), (1.11). Reserve half the tree exponential for μ and endpoint summation. Use the remaining half, with M chosen after κ₁, to pay exp(κ₁ n(F)). The short-walk case costs the finite exp(C_dκ₁) of (1.11), rather than a small factor; almost-local C enlarges C_d by a fixed amount. The factors O(M₁^{-1/2})^{|ω|} sum the walks. The remaining M₁^{-|ω|/2} pays a choice of an intermediate factor when expanding a composite operator. Consequently B_G and B_H are finite constants depending on d,L,M,M₁,κ₁,μ and the source domain margins, uniformly in the scale, volume and admissible domains. This is the source's order of constants; no choice of c₀ precedes these constants.

Since n(F_ω∪F_ν)≤n(F_ω)+n(F_ν), submultiplicativity of the finite-dimensional matrix norm and the triangle inequality for distance give

$$
\sup_x\sum_{d,y,\omega,\nu}
e^{\mu d(x,d)}e^{\kappa_1 n(F_\omega\cup F_\nu)}
\|G_\omega(x,y)K_\nu(y,d)\|
\leq B_GB_H\;.
\tag{G.235b}
$$

Thus, uniformly on the localisation polydisc and for |a|_∞≤s,

$$
|m_\sigma|_\infty\leq B_GB_Hs\;.
\tag{G.235}
$$

In particular choose c₀≤(4B_GB_H)^{-1}. The series and its local parameter derivatives converge normally on slightly smaller polydiscs; choose the source M with a fixed slack in the circle radius to obtain holomorphy on a neighbourhood of the circles actually used in (2.14). Equation (G.235b) also retains endpoint decay. It does not consume the later relative-tree or history reserve.

**Factorisation and gauge transport.** Set σ=0 outside a union Z containing Z₀′. A surviving term of (G.234) has F_ω∪F_ν⊂Z, in the partition sense used by RG II (1.9)–(1.10). Its two footprints meet at y, so their union is connected and contains x and d. Therefore m_σ at an integrated seed coordinate in a component Z_i depends on a only in that component, with its source collar already in the footprint. It depends on the background only there as well. The weakened seed covariance and Γ have the same component property by RG II pp.13–14. For a selected family whose interaction and cutoff supports are placed in the seed, (G.230) factorises over these components. A component with no selected factor has full real integration contours; integrating its b variables cancels its own X-compensator exactly, so its factor is one even with a complex mean. This does not factorise the interacting measure before selection.

D2.2(6)(b1)–(b2) supplies the gauge covariance of the walk factors and nonlinear chart and is reused here. At the intermediate index y, the two gauge rotations cancel. Each product kernel transforms by R(u)_x on the left and R(u)_d^{-1} on the right; with a transformed at d, m transforms at x. The scalar quadratic forms in (G.230), the cutoffs and the scalar marks are invariant with all background and boundary data transported. The matrix norms in (G.235a)–(G.235b) are invariant under these endpoint orthogonal rotations; they are bounds on operators inside the compensated scalar integral, not an open-Wilson-segment activity. Distinct component gauges are used only after this separation; connecting footprints before separation carry both endpoint transformations.

**Checks and scope.** A walk of length zero still pays its short-footprint constant. An overlapping pair of footprints carries σ once, as (G.234) requires. A retained endpoint in another component is killed by a zero weakening on the connecting footprint. A component without selected factors has mass one, with the physical compensator retained. These checks test the source-localisation application. They neither supply a tube norm for the mixed-integral mark nor establish a bound after summing boundary polymers.

### 39.7 Boundary Resummation: The Cutoff Contribution and the Remaining Application

The following calculation continues at the same creation integral, with the source application of §39.6 awaiting review. The full action is retained; in particular this is not an estimate under the free Gaussian used in place of the interacting measure. It tests whether the new mean requires a non-small boundary potential in the resummation.

Write c_b for the positive final coefficient in the last exponential of (G.229), after its surface and determinant constants have been paid. Summing the side sets S gives, for each original selection (𝒟,P,Z₀),

$$
\begin{split}
\sum_{S\subset Y_0\cup P}e^{-c_b r^2|P\cup S|}
&=2^{|P|}e^{-c_b r^2|P|}
(1+e^{-c_b r^2})^{|Y_0\setminus P|}\\
&\leq e^{-\frac{1}{2}c_b r^2|P|}
e^{e^{-c_b r^2}|Y_0|}\;.
\end{split}
\tag{G.236}
$$

The last inequality requires c_b r²≥2 log 2. Here Y₀ in the side sum means its integrated bond labels; replacing their count by the full seed volume is an upper bound. There is no sum over new retained-field seeds. Retained labels enter the localisation footprint through (G.234), and their connecting cubes are paid by the original Cauchy factor exp(−(κ₁−1)N₁(Z∖Z₀′)). At σ=0 outside Z, this includes exactly the boundary-touching terms, not just Z⊂Λ.

For the covariance-only selection 𝒟=∅ with no mark, P=∅ gives one exactly, independently of a; this is the full-contour cancellation of (G.230). Thus every nonconstant vacuum activity in this selection has P≠∅. Its retained-field dependence can reach Λ^c through the mean, but it retains the factor exp(−c_b r²|P|/2). In particular an a-dependent boundary activity need not contain a selected boundary potential. It would be incorrect to classify all these activities by the O(ε_k) factor of D2.6 §2.3; the bad-cutoff factor pays this additional case. Components with selected potentials retain the entire product ∏_{Y∈𝒟}2ω_Y, including those Y meeting Λ^c.

This matches the bad-set part of RG II (2.26) with a coefficient γ₂^*≤c_b. In the actual resummation the five-part split is now made with γ₂^*r²: one part sums bond choices as in (2.31), one pays the corrected coefficient 18κ for the cubes of Z₀∖Y₀, and the three remaining parts provide the component smallness and the remaining shape sums. The required inequality is γ₂^*r²/20≥18κ, exactly the existing D2.4(10)(d) condition with the reduced coefficient. |Y₀| counts bonds, while RG2's seed-volume allowance is per M-cube. So the extra factor exp(e^{-c_b r²}|Y₀|) adds e^{-c_b r²} times the number of bonds per M-cube to the per-cube allowance, which is negligible for g_k small once M is fixed. The coarse assembly still requires (κ₁−1)/2≥9Lκ. None of these changes spends the relative-tree decay or the history allocation a second time.

For components built from selected interactions, the next required inequality is the **full action** estimate

$$
2\omega_Y\leq\epsilon_2\alpha_6
e^{-(1-3\delta)\kappa d_k(Y)}\;.
\tag{G.237}
$$

The parameters ε₂,α₆ here are the amplitudes of the resummation, not cutoff radii. They must be uniform for the actual multi-domain Y and on the joint contour tube. This is the first input needed in RG II (2.27)–(2.29); (G.236) alone does not prove it. O6 §8 gives the bounded and quadratic parts of the P/regular potentials on that tube, respectively O(g_k(log g_k^{-2})^{p₀}) and O(g_k(log g_k^{-2})^{3p₀}), with the source decay factors. For the old boundary terms, CRE (2.42) is indexed by j and d_j(X), whereas the resummation uses the re-expanded domains Y at the current scale and their retained support. CRE pp.275–277 supplies the multiscale re-expansion and states the extra O(ε_k) bound; D2.6 §2.3 uses that as Bałaban's statement, and the Kotecký–Preiss condition for the full gas, boundary polymers included, is derived at the creation integral in §41 (R-vac(ii-bd) at amplitude ε̄₂; §55.7). The enlargement in a must preserve those bounds for the re-expanded terms, not merely the raw old functions. No conversion of d_j(X) into d_k(Y) without the source localisation is made here.

The side sum (G.236) reuses §39.3's calculation; it is not a new probabilistic estimate. Its application here explicitly includes the a-dependent vacuum terms with no interaction. The full marked bound and physical normaliser are not yet asserted: they still need the source application of (G.237) for all boundary channels and the actual tube norm of the mark. The source counterpart is CRE (3.44)–(3.47): the vacuum factors in the marked numerator must be the same full boundary-inclusive factors as in its denominator, so that their ratio leaves only clusters touching the marked root. D2.6 §2.4's normalisation cannot be replaced by the interior gas. This is the next analytic application, not an already established conclusion of the mean bound.

### 39.8 Pause Checkpoint, 29 October 2026

The user explicitly instructed “Pause”. Calculations have stopped. The proposed source application (G.232)–(G.235), including the union-marked mean, is saved in §39.6 and has not been accepted. Section 39.7 records the boundary-cutoff application and identifies (G.237) for the full re-expanded action as still required. The side summation itself is reused from §39.3. No enlarged retained-field analytic domain, zero-free physical normaliser, marked mixed estimate or Cauchy conclusion has been established.

An isolated Claude review was launched with the authorised model and settings, in `verification/isolated_reviewer/reviews/lf-gamma-source-mean-20261029-r1`. The pending launcher was interrupted on the user's pause, before a report was received. Its packet and transmitted request remain in that directory. No acceptance verdict or completed-manifest check is claimed. The packet was assembled before §39.7 was appended and reviews §39.6 only, with (G.226)–(G.231) as its immediate caller; its saved source hashes identify that revision. Do not automatically retry the interrupted request. The packet builder is `tmp/build_lf_gamma_mean_packet_20261029.py`; do not rerun it unchanged, because its argument extraction currently extends from the §39.6 marker to the end of the live note.

At the pause, the latest source check was of the old boundary-action Cauchy margin. D2.2's step-map line 108 explicitly retains the ratio δ_k/ρ_{α,k}=O((log g_k^{-2})^{p₀−q₁}) for old-factor links, whereas O6 §5's use of a linear fluctuation prefactor must be checked at the actual localised action caller before using (G.237). This is a source-application question, not a demonstrated contradiction or a new bound. Reuse §2's existing shrinking-margin calculation, §36.1's full configuration/current qualification, D2.6 §§2.2–2.4 and the existing relative-tree/history allocation. No calculation of this margin question was completed in this resumed run.

## 40. The Old-Factor Margin and the Amplitude in (G.237)

29 October 2026, resumed at the user's instruction. This section answers the question left at §39.8.
- O6 §5 bounds the 𝐏^{(k)}-terms by their printed bounds, with a fluctuation factor linear in ε_k.
- O6 §5 bounds the bracket terms by the Schwarz lemma on R-m's domain, M_Xρ_k^{-1}, with coefficient of order ε_k/α_{1,k} (O6 l.58, l.62–63).
- The map's D2.2 line 108 retains the ratio δ_k/ρ_{α,k}=O((log g_k^{-2})^{p₀−q₁}) for old-factor links.

The question is which amplitude enters (G.237) on the tube of §39. The calculation is at the creation integral (G.227), on the tube of §39.1–§39.2, with the full action.

### 40.1 Where the Margin Enters the Localised Old Terms

In RG2 the localised piece of an old term is the Cauchy integral (1.23) in t_□ on the circle (1.22), 1/|t_□|=8B₀C₁e^{16κ₁}α₂^{-1}g_k|B|. Its bound (1.24) is this factor times E₀ and the decay factors (RG2 p.7, read). The constant α₂ enters only as the width of the old term's analyticity in the shift: the shift is admissible while it satisfies (I.3.31) with ½α₂ ("We assume that 4B₀C₁e^{16κ₁}ε₁≤¼α₂", p.7). In RG1 and RG2 α₂ is absolute, and the factor is O(g_k|B|) on RG2's domain g_k|B|<ε₁ ((1.20), (1.34)), where ε₁ is an auxiliary constant. The factor O(ε_k) is CRE's real-support situation.

In CRE the old terms are analytic on g-scaled spaces. The widths are α_{1,n}=g_nC₁(log g_n^{-2})^{q₁} (CRE (2.28), p.259), with the layer factors of (2.36)–(2.39) (p.261). The part of the width available for the shift at step k is R-m's: |B′|<r_{α,k}=min(β,1)α_{1,k}/(16B₀e^{16κ_s}) (O6, Notation; map l.697–702; CRE p.277). Running (1.22)–(1.24) with this width in place of α₂, and with half the width on the circle as (1.22) does, the localised piece obeys its sup bound times

$$
\rho_k(B):=\frac{2C_1^{\mathrm{RG2}}\,g_k\sup_Y|B|}{r_{\alpha,k}}
\tag{G.238}
$$

in place of RG2's 8B₀C₁e^{16κ₁}α₂^{-1}g_k|B|. The sup bounds themselves carry no small factor:

- E₀e^{−κd_j(X)} for 𝐄^{(j)} (RG1 (1.18), p.263, kept by CRE p.259 (iv));
- B₀e^{−κd_j(X)} for 𝐁^{(j)} (CRE (2.42), p.261);
- g_j^{κ₀}e^{−κd_j(X)} for 𝐑^{(j)} (CRE (2.31), p.260).

So the smallness of an old-factor link is ρ_k and nothing else. On the tube of §39 the integrated field has |b|≤2r and the retained field |a|≤c₀r<r, with r=δ_k/g_k and δ_k=g_kA₁(log g_k^{-2})^{p₀} (§39.6). Hence g_k sup|B|≤2δ_k and

$$
\rho_k^{\mathrm{tube}}=\frac{4C_1^{\mathrm{RG2}}\delta_k}{r_{\alpha,k}}
=\frac{64B_0e^{16\kappa_s}C_1^{\mathrm{RG2}}}{\min(\beta,1)}\,\frac{A_1}{C_1}\,(\log g_k^{-2})^{p_0-q_1}\;.
\tag{G.239}
$$

This is the ratio of map line 108 at step k. The tube lies in O6's domain 𝒫_k^m: 2δ_k=(2A₁/A₀)ε_k≤c₃ε_k≤ε_k^♯, so O6's (C1) applies. Under O6's (C3), C₁^{RG2}ε_k^♯<r_{α,k}/2, one has ρ_k^{tube}≤2C₁^{RG2}c₃ε_k/r_{α,k}<1, so the circle lies inside the domain.

### 40.2 Neither the Older Layers Nor Localisation Changes (G.239)

*Older layers.* On a bond of the layer Ω_n∖Ω_{n+1}, n<k, the norm of (2.39) is the phase per scale-n bond, L^nξ|A′|. At step k, L^kξ=1. The shift is the fine-bond phase ξ𝐇_k with 𝐇_k bounded in step-k units (RG2 (1.21)), so its scale-n phase is L^{n−k}|𝐇_k|. This is (2.39) as printed, U′ = exp iξA′ with the bound on L^nξ|A′|, and ξ = L^{−j} for the objects of index j (CRE p.256 l.58; (2.35) writes L^{−p} for it at index p), so L^kξ = 1 at j = k; ξ|A′| is the phase of a fine bond, and L^nξ|A′| that of L^n fine bonds (§55.7). The width given up on that layer at step k is β2^{−(k+1−n)}α_{1,n} (the powers of 1/2 in (2.36)–(2.39), p.277), against β2^{−1}α_{1,k} on the current layer. CRE (2.6)–(2.7) (p.255), g_k≤(1+β₀)(k−n)^{1/2}g_n and (log g_k^{-2})^{q₁}≤(1+β₀)(log g_n^{-2})^{q₁}, give α_{1,k}≤(1+β₀)²(k−n)^{1/2}α_{1,n}. The ratio on layer n is therefore at most

$$
\Bigl(\frac{2}{L}\Bigr)^{k-n}(k-n)^{1/2}(1+\beta_0)^2
$$

times the ratio on layer k. This is ≤1 for L≥4 and β₀≤1/7. The gradient part of (2.39) carries L^{2(n−k)} and is smaller still. So the binding width is the current layer's. The computation is ours. p.277 gives a different reason for the powers of 1/2 ("we have to use a part of the analyticity domains of terms in 𝐁_k for the function 𝐇_k"). It attributes their sufficiency to "the localization of the fluctuation field, and the exponential decay of the minimizing function 𝐇_k".

*Current-step terms.* A term 𝐁^{(k)}(X) meets Z_k^∼ ((2.41)). CRE (3.5), Ω_{k+1}=(Q′^{∼2}_{k+1}∪(B^{k+1}(P^1_{k+1})^c)^{∼3})^c, has (B^{k+1}(P^1_{k+1}))^c=P′^{∼}_{k+1}∪Z_k′^{∼5} (p.265). So Ω_{k+1} lies outside Z_k′^{∼8}, at least eight layers of LMR_{k+1}-cubes from Z_k′. A term reaching Ω_{k+1} therefore has d_k(X)≳7LR_{k+1} in M-cube units. Its decay e^{−κd_k(X)}≤e^{−cκLR_{k+1}} is superpolynomially small in g_k, since R_{k+1}≥(log g_{k+1}^{-2})^r with r≥2 (CRE p.245, p.255). A term that stays away from Ω_{k+1} sees 𝐇_k only through its exponential decay (p.277, "the exponential decay of the minimizing function 𝐇_k"; Bałaban's). For the current-step terms (G.239) is therefore a valid bound but far from sharp.

So the widths give ρ_k, and not the printed "additional factor O(ε_k)" of p.277. That printed factor is Bałaban's statement R-fr, accepted as presented (D2.6 closure; map l.736, l.1511; §55.7). Nothing here refutes it, since a Cauchy estimate is only an upper bound. The derivation below does not use p.277's amplitude O(ε_k): it needs ρ_k^{tube} small. It does use R-fr(a), the support r=δ_k/g_k of (3.16) in the Gaussian variable, fixed by LFR II p.380 l.42–45 (§55.7), and that use is load-bearing. The tube |b|≤2r, ρ_k^{tube}, and the bad-set factor e^{−c_br²} of (G.236) with c_br²≥2 log 2 all need r≫1. On the literal rescaled reading r=δ_k they fail.

### 40.3 (G.237) for Each Action Channel on the Tube

Each channel of T in (G.227) is listed with its bound on the tube, at real or complex b, a and with the background in the term's space.

- *𝐏^{(k)}.* These terms are analytic on the absolute domain {e^{16κ₁}|B′|≤a₁} (RG2 p.10). Their factor is linear in g_k|B|≤2δ_k: O(δ_k) for the bounded part, and O(g_k(log g_k^{-2})^{3p₀}) for the quadratic forms on the tube (O6 §5 and §8, with the fluctuation factor at 2δ_k). These are genuinely of order g_k times a polylog.
- *𝐄_k-, 𝐑_k″-, 𝐁_k- and A(·)-brackets with Y⊄Λ_{k+1}.* Each is its sup bound times ρ_k^{tube} times RG2's localisation constants: 2ω_Y≤2E_max ρ_k^{tube}M^qe^{C₂κ₁}e^{−(1−2δ)κd_k(Y)}, with E_max:=max{E₀,B₀}. This is (1.24)–(1.36) of RG2 with the product ε₁C₁, which stands for the factor of (1.22), replaced by ρ_k^{tube}, which already contains C₁^{RG2}. The 𝐑-terms carry an extra g_j^{κ₀}. The A(·)-terms are supported in Z_k and reach Ω_{k+1} only through the decay of 𝐇_k (p.277, "large values … are suppressed by the exponential decay of 𝐇_k"). The passage from d_j(X) to d_k(Y) is Bałaban's re-expansion of pp.275–277, accepted as in D2.6 §2.3, with the amplitude now (G.239) rather than p.277's O(ε_k).
- *𝐄_k- and 𝐑_k-brackets with Y⊂Λ_{k+1}.* The curly bracket of (3.25) also contains these interior terms. They too live on CRE's g-scaled spaces ((2.28), p.259 (ii)), so their gain is also of ρ-type. On Ω_{k+1}⊃Λ_{k+1}, the width available for the shift is the step-k radius minus the step-(k+1) radius, α_{1,k}−α_{1,k+1}/L. This is not a power-of-1/2 difference, but it is at least α_{1,k}/2≥(β/2)α_{1,k} since β≤1 (map l.700). The first inequality needs α_{1,k+1}≤(L/2)α_{1,k}, which holds by (2.28) at weak coupling (g_{k+1}/g_k→1) for L≥3. So the same r_{α,k} is admissible there. The Cauchy estimate of §40.1 then gives the same factor (G.238), and on the tube (G.239). The interior terms obey the bound of the previous bullet: 2ω_Y≤2E_maxρ_k^{tube}M^qe^{C₂κ₁}e^{−(1−2δ)κd_k(Y)}, with E₀ for 𝐄 and g_j^{κ₀}E₀ for 𝐑. All their bonds lie in Ω_{k+1}, so the older-layer comparison of §40.2 is not needed for them.
- *V^{(k)}(S_{k+1}).* O6 §6 applies with sup|F| the bracket sup bound. Its factor is 6C₁^{RG2}h_k/r_{α,k} times O(1), and h_k is e^{−R_k}-small.

Hence (G.237) holds on the tube, uniformly in the multi-domain Y, with RG2's ε₂ = 2E₀ε₁C₁α₄^{-1}α₆^{-1}M^qe^{C₂κ₁} (p.19) replaced by

$$
\varepsilon_2^{(k)}=2E_{\max}\,\rho_k^{\mathrm{tube}}\,\alpha_4^{-1}\alpha_6^{-1}M^qe^{C_2\kappa_1}
+O\bigl(g_k(\log g_k^{-2})^{3p_0}\bigr)\;.
\tag{G.240}
$$

The resummation used is the project's corrected D2.4(10) (map l.1454–1456), not RG2's printed Lemma 3. Its thresholds are (d), (1/20)γ₂t_k²≥18κ, and (e), ε₂e^{max(5,3λ_L)κ}≤1, with λ_L=L/max{2,1+486/L}. Threshold (e) implies RG2's ε₂≤1 and ε₂e^{5κ}≤1 (p.18). In (d), §39.7 puts γ₂^*r² in place of γ₂t_k². The comparison e^{−γ₂ε₁²/(20γ²)}≤ε₂ of p.19 is replaced by the bad-set factor e^{−c_br²} of (G.236), which is superpolynomially small. Under (R-m′), q₁>p₀, the thresholds hold for g_K small at fixed L, κ, κ₁, M, α₄, α₆. At q₁=p₀, ρ_k^{tube} is the constant 64B₀e^{16κ_s}C₁^{RG2}A₁/(min(β,1)C₁). Threshold (e) then holds if half of it is spent on the first term of (G.240), which is the constant condition

$$
\frac{C_1}{A_1}\geq\frac{256\,e^{\max(5,3\lambda_L)\kappa}B_0e^{16\kappa_s}C_1^{\mathrm{RG2}}E_{\max}\alpha_4^{-1}\alpha_6^{-1}M^qe^{C_2\kappa_1}}{\min(\beta,1)}\;.
\tag{G.241}
$$

Here C₁ on the left is CRE's width constant of (2.28), and C₁^{RG2} on the right is RG2's absolute constant. The condition requires CRE's C₁ to be chosen after L, κ, κ₁, M, α₄, α₆; CRE p.259 asks only that C₁ be "sufficiently large", and the order of this choice relative to the other uses of C₁ is not checked here.

### 40.4 Consequences for Other Texts (Recorded Here, Not Edited)

- O6 §5 uses "(1.36) with ε₁→ε_k′" for 𝐕_k″ only (l.60). It bounds the 𝐄_k-, 𝐑_k″-, 𝐁_k- and A(·)-brackets by the Schwarz lemma on R-m's domain, M_Xρ_k^{-1}, with coefficient of order ε_k/α_{1,k} (l.58, l.62–63). (G.238)–(G.239) is a Cauchy-form re-derivation of that bracket coefficient on the δ_k-tube, larger by a factor 2. It is not a correction of O6 §5.
- O6 §8's "O(g_k(log g_k^{-2})^{p₀})≪1" holds for the 𝐏^{(k)}-channels only. O6 §8's last sentence bounds the 𝐁_k- and A(·)-terms by "2c₃ε_k times p.277's absolute constant", which is p.277's amplitude (R-fr). On the bracket channels the amplitude is O((log g_k^{-2})^{p₀−q₁}), small under (R-m′).
- §39.1's sentence "The resulting amplitude is of order g_k times a fixed logarithmic power" holds for the 𝐏^{(k)}-channels. For the bracket channels the amplitude is (G.239).
- D2.6 closure §2.3 and the map (l.736, l.1511) use R-fr's O(ε_k) as Bałaban's claim. A consumer that needs O(ε_k) as a power of g_k, and not only smallness, would have to rest on R-fr; this section does not supply it.

### 40.5 Status and Open List

Derived and isolated-reviewed (no fatal finding; the review's findings are repaired in §§39.6–40):
- the answer to §39.8's margin question, (G.238)–(G.239) and §40.2;
- (G.237) for every action channel of the creation integral on the tube, interior brackets included, with amplitude (G.240).

The interior-bracket bullet of §40.3 and the D2.4(10) form of the thresholds and of (G.241) were written in response to the review. They have not been re-reviewed.

These rest on the following:
- R-m (Bałaban's, CRE p.277 l.3–8) and R-fr(a), the support r=δ_k/g_k (LFR II p.380 l.42–45; §55.7);
- (R-m′), an admissible choice of the constants (§55.7), or else the constant condition (G.241);
- O6 §§5, 6 and 8, whose domain repair has not been re-reviewed (D2.6 closure l.25, l.62);
- Bałaban's re-expansion (CRE pp.275–277) and his statement of the decay of 𝐇_k (p.277).

They do not use p.277's amplitude O(ε_k). Part (ii) of §39.7, that the a-dependent vacuum activities are paid by the bad-set factor, rests in addition on the contour estimate (G.229) and the family (G.230)–(G.231).

Open, in the order of the §39 argument:
1. Acceptance of the contour estimate (G.229) and the family (G.230)–(G.231). The review checked their use, not their proof.
2. The physical vacuum cancellation of CRE (3.44)–(3.47), with D2.6 §2.4's full boundary-inclusive gas in the numerator and the denominator (§41).
3. The tube norm of the actual marks (§39.5, item 6; §§42–43).
4. The moderate/large split of the retained field with its interacting tail, the propagation of the analytic domain through the later T and R operations, and the application to (1.60).
5. The order of the constant choices in (G.241). This matters only at q₁=p₀.
6. The composite-walk payment in (G.235a), "the remaining M₁^{-|ω|/2} pays a choice of an intermediate factor", which is sketched and not written out.

## 41. The Physical Vacuum Cancellation at the Creation Integral

This section treats item 2 of §40.5. The integral is the creation integral (G.227), for |a|≤c₀r, with the full boundary-inclusive gas. The result is a reduction to Bałaban's resummation and to a textbook cluster theorem, once (G.229), (G.236) and (G.237) hold. It is not an estimate of the hard item 4.

### 41.1 The Same Activities in the Numerator and the Denominator

Expand both the compensated normaliser 𝒵(a) of (G.227) and its marked version 𝒵(a)[F] with the family (G.230). The same seed covariance G_σ, the same mean m_σ of (G.234), the same cutoff allocation (G.233) and the same weakenings are used in both. The mark F multiplies the integrand of the selection whose seed contains supp F, and nothing else. After the resummation of RG2 (2.14)–(2.37),

$$
\mathcal Z(a)[F]=\sum_{Z_0\supset\operatorname{supp}F}H'_F(Z_0;a)\sum_{\{Z_1,\dots,Z_n\}}\prod_{i\ge1}H(Z_i;a)\,,
\qquad
\mathcal Z(a)=\sum_{\{Z_1,\dots,Z_n\}}\prod_iH(Z_i;a)\,.
\tag{G.242}
$$

Here the Z_i are localisation domains of 𝐃_{k+1} meeting Λ_{k+1}, those meeting Λ_{k+1}^c included. In the numerator they satisfy Z_i⊂Z̄₀^c, Bałaban's condition in (3.45). The functions H(Z_i;a) are the same functions in both sums. This is CRE p.277's "for n>0 the factors H(Z_i) are the same as in the expansion of the denominator", here at complex a. It holds because the a-dependence enters every activity only through m_σ, the compensator of (G.230), and the selected interactions T_Y(a,·), and all of these are built without reference to F. The selected interactions carry CRE's direct A_k-dependence of P^{(k)}(g_k,(tA_k,A)) and E_k(U_k(…(tA_k,A)…)) in (3.28)–(3.29), which is localised where A_k lives, next to Λ_{k+1}. §39.1 removes the b-independent interactions T_Y(a) from the expansion, so the literal (G.227) is exp(Σ_{Y b-indep.}T_Y(a)) times the polymer sums of (G.242). This factor is analytic and nonvanishing, it is common to the numerator and the denominator, and it cancels in their ratio. The outer scalar exp(⟨a,Q_Da⟩/2) of §39.6 is common to the physical numerator and denominator and cancels in their ratio. In the physical normaliser Z_phys(a)=exp(⟨a,Q_Da⟩/2)𝒵(a) it stays, as CRE (3.23) keeps it.

### 41.2 The Uniform Majorant for the Boundary-Inclusive Gas

On the tube, each selected term obeys (G.229). The side labels sum to (G.236), and every action channel obeys (G.237) with the amplitude ε₂^{(k)} of (G.240) (§40.3). The a-dependent vacuum activities with no selected potential carry the bad-set factor of (G.236) (§39.7). These are the inputs of RG2 (2.26)–(2.37), whose sums over domains meeting Λ_{k+1} are sub-sums of the full-lattice sums, with positive terms. Printed Lemma 3 (p.20, (2.38)) is stated for RG2's measure, with no retained-field source, no complex a and no Λ_{k+1} boundary, so it is not applied as stated. Its proof, pp.17–20, is run with the per-term majorant (G.229)·(G.236)·(G.237) in place of (2.26) and with repair R-L3 (map l.1254). Write ε̄₂ := max(ε₂^{(k)}, e^{−γ₂^*r²/20}). The product (G.229)·(G.236) with (G.237) inserted has (2.26)'s form: the Cauchy factor e^{−(κ₁−1)N₁(Z∖Z₀′)}, the per-Y factor ε̄₂α₆e^{−(1−3δ)κd_k(Y)}, the bad-set factor e^{−½c_br²|P|} in place of e^{−½γ₂ε₁²|P|/g_k²}, and e^{Cα₅|Z|+e^{−c_br²}|Y₀|} in place of e^{O(1)α₅|Z|}. The proof then gives, uniformly for |a|≤c₀r,

$$
|H(Z;a)|\leq2(L+2)^4O_3\,\bar\varepsilon_2\,e^{-(1-8\delta)\frac12L\kappa d_{k+1}(Z)}\,,
\tag{G.243}
$$

for every Z∈𝐃_{k+1} meeting Λ_{k+1}, those meeting Λ_{k+1}^c included. O₃ is R-L3's enlarged constant. The extra factor e^{e^{−c_br²}|Y₀|} is at most exp(4(LM)⁴e^{−c_br²}#_{k+1}(Z)) and is absorbed in A, R-L3's name (map l.1252) for p.20's absolute bound of O(1)(LM)⁴α₅ + exp(−½(κ₁−1)); p.20 prints no A. A is fixed as the old value plus a fixed slack before κ is chosen, and g_K is then taken small. The conditions are R-L3's (map l.1254), read with ε̄₂:
- L≥3, κ≥max(κ_vac,3240A/(L−2)), δκ/2≥κ_{(1.26)} and e^{5κ}≥8e^{20.25}O_{(1.26)};
- (2.32) with 18 in place of 4, so the bad-set threshold is γ₂^*r²/20≥18κ (the five-part split of §39.7), and ½(κ₁−1)≥9Lκ in p.20's adapted use;
- p.19's comparison e^{−γ₂^*r²/20}≤ε̄₂, which holds by the definition of ε̄₂;
- p.20's condition re-read as 2(L+2)⁴O₃ε̄₂e^{5(1−7δ)½Lκ}≤1.

R-L3's further conditions (κ₁−2)/16≥1, p.20's (L+2)⁴O(1)ε₂≤½ and p.18's ε₂e^{5κ}≤1 are implied by these, the first by ½(κ₁−1)≥9Lκ and the others by the last condition, since (1−7δ)½L≥1. The conditions on L, κ and κ₁ are choices of constants in Bałaban's order. Under (R-m′) the conditions on ε̄₂ and r then hold for g_K small, since ε₂^{(k)}→0 and r→∞ as g_K→0 at fixed L, κ, κ₁, M, α₄ and α₆. At q₁=p₀, ε₂^{(k)} is not small, and the last condition follows from threshold (e), ε̄₂e^{max(5,3λ_L)κ}≤1, as follows (derived). With RG2 p.21's δ=(1−2/L)/10, 5(1−7δ)½L=0.75L+3.5. For L≥486, λ_L=L/2 and 3λ_L=1.5L, so (e) gives 2(L+2)⁴O₃ε̄₂e^{5(1−7δ)½Lκ}≤2(L+2)⁴O₃e^{−(0.75L−3.5)κ}≤1 once κ≥log(2(L+2)⁴O₃)/(0.75L−3.5). The project's L₀=5000 (map l.200) satisfies L≥486. L≥486 is sufficient, not necessary: for L<486, λ_L=L²/(L+486) (map l.1454), and 3λ_L exceeds 0.75L+3.5 exactly when 3L²>(0.75L+3.5)(L+486), that is 2.25L²−368L−1701>0, which holds for L≥169, and then (e) gives the condition once (3λ_L−0.75L−3.5)κ≥log(2(L+2)⁴O₃). For L≤168, 3λ_L≤5(1−7δ)½L and (e) does not give it. Threshold (e) at q₁=p₀ is (G.241) for ε₂^{(k)}, and e^{−γ₂^*r²/20}e^{max(5,3λ_L)κ}≤½ for g_K small. The geometric inequality (2.36), 2d_k(Z_i)≥Ld_{k+1}(Z_i′), and RG2's sums are Bałaban's.

Status: (G.243) is a transfer of the proof of Lemma 3, not an application of the printed lemma. It is conditional on (G.229) and the family (G.230) of §§39.2–39.4, and, through (G.237), on the inputs carried by §40.3, checked in §55.7: Bałaban's re-expansion of pp.275–277 (as accepted in D2.6 §2.3), R-𝐁 (derived from CRE (2.41)), R-fr(a) (LFR II p.380), and O6's tube analyticity under R-m (Bałaban's) and (R-m′) (an admissible choice of constants). With these inputs it gives D2.6 closure §2.4's reading R-vac(ii-bd), "the polymers meeting Λ_{k+1}ᶜ satisfy Lemma 3's bound with the O(ε_k) of their boundary potentials and R-L3's constants", at the creation integral on the complex ball, with amplitude ε̄₂ in place of the reading's O(ε_k). ε̄₂ is larger than O(ε_k): ε₂^{(k)} contains g_k(log g_k^{−2})^{3p₀}, and ρ_k^{tube} is only polylog-small under (R-m′). R-vac(ii-bd) is not used in deriving (G.243).

The operative vacuum resummation is R-L3, as R-vac(ii-bd) itself states. D2.4(10)(b) (map l.1455–1456) is a bound for marked polymers, with slot set J(M)≠∅, and has no vacuum instance. It is the operative bound for the root activity H′_F(Z₀;a) of §41.3.

### 41.3 The Ratio and the Zero-Free Normaliser

With (G.243), the Kotecký–Preiss condition (5.10) of Friedli–Velenik Theorem 5.4 (p.224) holds for the real majorant (G.243) with the weight a(Z)=δ½Lκ(d_{k+1}(Z)+1). The weight must be positive, which is why the +1 is there: a single cube has d_{k+1}=0. To check (5.10), note that a polymer incompatible with Z* contains a cube of Z* or one of its wall neighbours. There are at most 9#(Z*) such cubes, where #(Z):=(LM)^{−4}|Z| is the number of π_{k+1}-cubes. By map D2.4(2)(a), #(Z*)≤162(d_{k+1}(Z*)+1). RG2 p.8's printed form M^{−4}|Y|≤3·2³d_k(Y) is false at a single cube (map l.1245) and is not used. Hence (5.10) holds once
9·162·2(L+2)⁴O₃ε̄₂e^{δ½Lκ}C_Σ≤δ½Lκ,  C_Σ:=sup_xΣ_{Z∋x}e^{−(1−9δ)½Lκd_{k+1}(Z)}.
C_Σ is a (1.26)-type sum, over the domains through a fixed cube, finite and volume-free once (1−9δ)½Lκ≥κ_{(1.26)}. Under (R-m′) the condition holds for g_K small. At q₁=p₀ it holds through threshold (e) for κ large, since 3λ_L>δ½L=(L−2)/20 for every L≥3, given the derivation of (G.243) there (§41.2). Two consequences hold uniformly for |a|≤c₀r:
- log 𝒵(a) is an absolutely convergent sum of connected clusters, so 𝒵(a)≠0. Friedli–Velenik Theorem 5.8 (p.228) is stated for one complex variable. Its proof gives analyticity of log 𝒵(a) on the open polydisc in ℂ^{dim𝔤·|D|} by the several-variable Weierstrass theorem, since the convergence is uniform on the closed ball. Each H(Z;a) is analytic as a fixed-contour integral (§39.2), and (G.243) is a uniform majorant. The volume is finite, as Friedli–Velenik Remark 5.5 assumes.
- The clusters attached to a fixed root have a bounded sum. This is Friedli–Velenik Lemma 5.6 ((5.17), p.226). Its proof multiplies (5.12) by |ζ(Z₀,Z₁)||H(Z₁;a)| and sums over Z₁. Before (5.10) is used, this gives the sharper bound in (G.244). The proof uses (5.12) only for gas polymers, so it applies to a root Z₀ that is not a gas polymer.

Dividing (G.242) as in (3.45)–(3.46),

$$
\frac{\mathcal Z(a)[F]}{\mathcal Z(a)}=\sum_{Z_0\supset\operatorname{supp}F}H'_F(Z_0;a)\exp\Bigl[-\sum_{\mathcal C\not\sim Z_0}\phi^T(\mathcal C;a)\Bigr],
\qquad
\Bigl|\sum_{\mathcal C\not\sim Z_0}\phi^T(\mathcal C;a)\Bigr|\leq\sum_{Z\not\sim Z_0}|H(Z;a)|e^{a(Z)}\leq9K\,\#(Z_0)\,,
\qquad K:=2(L+2)^4O_3\,\bar\varepsilon_2e^{\delta\frac12L\kappa}C_\Sigma\,.
\tag{G.244}
$$

Here 𝒞≁Z₀ are the clusters with a polymer meeting Z₀ along a three-dimensional wall at least (p.278). With (5.10) the right side is at most a(Z₀), but that form is lossy by the factor δ½Lκ/(9·162K) and is not used.

The root activity has no decay in the extent of the mark. In what follows D denotes the mark's cubes defined below, not §39.1's retained-field domain, and Z₀ the root polymer, D2.4(10)'s M; the localisation domain of a selection is written Z₀′. The plain term (𝐃,P,Z₀′,Z₀)=(∅,∅,D,D′), with Y₀=D (map l.1449 and l.1484), is the conditioned expectation of F with mean m_σ, restricted to the good-field ball, and for a Wilson-loop-type mark it is of order ‖F‖. The operative bound is D2.4(10)(b)'s (map l.1455–1456), with 𝒳_M replaced by F. Let D be the union of π_k-cubes meeting supp F, and D′ the π_{k+1}-hull of D with its touching π_k-cubes adjoined, as in D2.4(10)(a). F depends on the labels of supp F, and each of them lies in a π_k-cube meeting supp F, so in D; this is the one property of D_J^#(M) that D2.4(10)'s proof uses. Let m_D be the number of wall-components of D, which D2.4(10)(a) calls m(M), and d_{k+1}(Z₀;D′) the contracted linear size of D2.4(10)(a). Every component of Z₀ contains a cube of D, since a component that does not is a vacuum polymer of the gas. Then

$$
|H'_F(Z_0;a)|\leq\|F\|_{\rm tube}\,e^{81A'\#(D')}e^{(5+3\lambda_L)\kappa(m_D-1)}e^{-(1-5\delta)\lambda_L\kappa\,d_{k+1}(Z_0;D')}\,,
\tag{G.244a}
$$

with A′:=O(1)(LM)⁴Cα₅+4(LM)⁴e^{−c_br²}+e^{−½(κ₁−1)}+L⁴(O_{(1.26)}α₆+4M⁴e^{−γ₂^*r²/10}), D2.4(10)(b)'s A with the tube terms. Every term other than the plain expectation carries ϑ:=max{e^{−20δκ},e^{−γ₂^*r²/20},e^{−Lκ/2}}≤e^{−2κ/3}.

*The transfer of D2.4(10)'s proof to the tube (derived, line by line).* D2.4(10) has three parts, (c) the per-term bound, (d) the geometry, and (e) the resummation.
- (c), (2.14). The Cauchy representations in σ(Δ) and τ(Y) act on the operators and on the interactions; F carries no s, σ or τ. So the term is the selection's integral of §39.2 with F multiplying the integrand.
- (c), (2.15). On the fixed contours of §39.2 every label of supp F has |b_ℓ|<r+C_ms<2r and the retained field has |a|_∞≤s, so |F|≤‖F‖_tube there by (G.245). The pointwise bound therefore holds with the factor ‖F‖_tube in front, by |∫f|≤∫|f|.
- (c), (2.16)–(2.26). These are the operator, determinant, potential and indicator bounds. On the tube they are replaced by (G.229), (G.236) and (G.237), as for (G.243), and F enters none of them. So for every (𝐃,P,Z₀′) with Y₀⊇D, 𝐃=∅ and P=∅ included,
  |term| ≤ ‖F‖_tube·e^{−(κ₁−1)#_{k+1}(Z∖Z₀′)}·∏_{Y∈𝐃}ε̄₂α₆e^{−(1−3δ)κd_k(Y)}·e^{−½γ₂^*r²|P|}·e^{Cα₅|Z|+e^{−c_br²}|Y₀|}.
  This is D2.4(10)(c)'s form with ‖𝒳_M‖_sup→‖F‖_tube, ε₂→ε̄₂, γ₂ε₁²/γ²→γ₂^*r² and O(1)α₅|Z|→Cα₅|Z|+e^{−c_br²}|Y₀|.
- (d). The inequalities (2.27′), (2.32′) and (2.36′), the coarse assembly and the count #(X)≤81#(D)+324d(X;D) concern sets of cubes only. They hold unchanged.
- (e), the decay part. The split of each Y-factor into α₆e^{−δκd_k(Y)} and ε̄₂e^{−(1−4δ)κd_k(Y)}, and of each P-factor into one twentieth paying 18κ per cube of Z₀∖Y₀ and three spare twentieths, uses the conditions (1/20)γ₂^*r²≥18κ (§41.2), e^{−γ₂^*r²/20}≤ε̄₂ (by definition), ε̄₂e^{max(5,3λ_L)κ}≤1 (threshold (e)) and ½(κ₁−1)≥2Lκ (implied by ½(κ₁−1)≥9Lκ). With these the payments of the parent edges are those of D2.4(10)(e) verbatim, and the m_D−1 unpaid edges cost e^{(5+3λ_L)κ(m_D−1)}.
- (e), the entropy part. Each P-bond factor is 1+e^{−γ₂^*r²/10}, and the factor e^{Cα₅|Z|+e^{−c_br²}|Y₀|} is at most e^{(O(1)(LM)⁴Cα₅+4(LM)⁴e^{−c_br²})#_{k+1}(Z)}, since |Y₀|≤|Z|. So the total per π_{k+1}-cube is e^{A′}.
- (b), the restriction 324A′≤δλ_Lκ, which holds for M, κ₁ large, α₅, α₆ small and g_K small, as for D2.4(10)'s A.

So (G.244a) holds with the conditions of (G.243) together with 324A′≤δλ_Lκ. It inherits the status of (G.243) and the open item ‖F‖_tube of §41.4.

The attached clusters are paid by the contracted size through a count. Every cube of Z₀ is of one of three kinds:
- a cube of D′, of which there are #(D′);
- a cube that touches D′ but is not in it, of which there are at most 80#(D′);
- a cube disjoint from D′.

A cube C of the third kind lies at distance at least LM from D′, because two disjoint closed cubes of one lattice partition are at least one side apart. Let G be a set admissible for d_{k+1}(Z₀;D′). G meets C at a point p∉D′. The component of G∖D′ that contains p has its closure meeting D′, since G∪D′ is connected. So that component has length at least LM. A connected finite union of segments of length ℓ (in units of LM) has a closed walk of length 2ℓ through all of it. Cut into pieces of length at most 1, that walk gives at most 2ℓ+1≤3ℓ sets of diameter at most LM when ℓ≥1. Each such set meets at most 3⁴=81 cubes. Hence there are at most 243·d_{k+1}(Z₀;D′) cubes of the third kind, and

$$
\#(Z_0)\leq81\,\#(D')+243\,d_{k+1}(Z_0;D')\,.
\tag{G.244b}
$$

With (G.244) and (G.244a), each root term of the ratio is at most

‖F‖_tube·e^{(81A′+729K)#(D′)}e^{(5+3λ_L)κ(m_D−1)}e^{−[(1−5δ)λ_Lκ−2187K]d_{k+1}(Z₀;D′)}.

K is small with ε̄₂, so the rate loses only 2187K. Write ϱ_L:=(1−5δ)λ_Lκ and assume 2187K≤ϱ_L/2.

The roots at fixed D′ are counted as follows. Z₀⊇Z₀′⊇D′ by D2.4(10)(a) (map l.1449 and l.1452). So Z₀ is fixed by two choices: the set of touching cubes it contains, with at most 2^{80#(D′)} choices, and the set W of its cubes of the third kind.

Each touch-component of W, with cubes adjacent when they share a point, contains a cube touching a cube that touches D′. This holds because the path in G from that component to D′ runs through touching cubes of Z₀. Such cubes lie in the ring of at most 5⁴#(D′)=625#(D′) cubes around D′.

In the touch graph every cube has 80 neighbours. A connected set of n cubes containing a given cube is fixed by a closed depth-first walk of length 2(n−1) from that cube along a spanning tree. So there are at most 80^{2(n−1)}=6400^{n−1} such sets.

By (G.244b), #(W)≤243 d_{k+1}(Z₀;D′), so e^{−(ϱ_L/2)d_{k+1}(Z₀;D′)}≤e^{−(ϱ_L/486)#(W)}. An unordered collection of N disjoint components, each rooted at a cube of the ring, appears at least once among the N! orderings. Hence

Σ_{Z₀⊇D′}e^{−(ϱ_L/2)d_{k+1}(Z₀;D′)} ≤ 2^{80#(D′)}exp(625#(D′)c_w),  c_w:=Σ_{n≥1}6400^{n−1}e^{−ϱ_Ln/486}≤2e^{−ϱ_L/486}≤1

once ϱ_L≥486 log 12800 ≈ 4596. This is a κ-threshold and holds for every L≥3 once κ is large enough. For L≥486, ϱ_L=(L+2)κ/4 by D2.4(10)(b), and κ≥38 suffices; the project's L₀=5000 (map l.200) makes the threshold explicit in that way. Summing the root terms over Z₀ gives

$$
\Bigl|\frac{\mathcal Z(a)[F]}{\mathcal Z(a)}\Bigr|\leq\|F\|_{\rm tube}\,e^{(81A'+729K+681)\#(D')}e^{(5+3\lambda_L)\kappa(m_D-1)}\,,
\tag{G.244c}
$$

uniformly for |a|≤c₀r. (G.244c) is volume-free. It is exponential in the number of π_{k+1}-cubes of D′, a factor that depends on supp F only. For a wall-connected D, a Wilson loop's included, m_D=1. The constant 681≥80 log 2+625c_w comes from the touching-cube choices and the far animals; with c_w≤2/12800 it can be lowered to 56. It is not reduced by the plain-expectation term, because D2.4(10)(b) gives one factor ϑ per non-plain term, not one per cube. Whether that factor is acceptable is for the callers (§43, and the Wilson-loop insertion, whose #(D′) is the loop's length in π_{k+1}-cubes).

### 41.4 What This Settles and What It Does Not

Reviewed (lf-gamma-vac3), correct given the premises below, with minor corrections since made: item 2 of §40.5 at the creation integral. Its parts are:
- the identity of the numerator's and the denominator's non-root activities at complex a;
- the uniform bound (G.243) for the boundary-inclusive gas, which gives R-vac(ii-bd) at amplitude ε̄₂, with the derivation of R-L3's p.20 condition at q₁=p₀ for L≥169 and κ large;
- the zero-free, analytic compensated normaliser;
- the attached-cluster bound (G.244), the root bound (G.244a), the count (G.244b), and the ratio bound (G.244c).

Premises:
- (G.229) and the family (G.230) of §§39.2–39.4, which are not accepted yet (§40.5 item 1);
- §§39.6, 39.7 and 40;
- the inputs carried through (G.237), checked in §55.7: Bałaban's re-expansion of pp.275–277, R-𝐁, R-fr(a), and O6's tube analyticity under R-m and (R-m′);
- the proof of RG2 Lemma 3 with repair R-L3 and R-L3's conditions, for (G.243);
- the proof of D2.4(10)(b), transferred to the tube in §41.3, for (G.244a), with 324A′≤δλ_Lκ; D2.4(10) is itself "reviewed: no fatal finding; repairs not re-reviewed" (map l.1447), so its repairs (2.32′) and (2.36′) are unreviewed inputs;
- the smallness conditions of §41.3: 9·162K≤δ½Lκ, 2187K≤ϱ_L/2, (1−9δ)½Lκ≥κ_{(1.26)}, ϱ_L≥486 log 12800 (κ≥38 for L≥486), c_br²≥2 log 2 and γ₂^*≤c_b, and the slack in A for the e^{−c_br²} term;
- at q₁=p₀, L≥169 with κ large for (G.243); the project's L₀=5000 satisfies it;
- Friedli–Velenik Theorem 5.4, Lemma 5.6 and Theorem 5.8;
- at q₁=p₀ only, the order of choice of CRE's C₁ in (G.241) (§40.5 item 5).

The §40.3 bullet on interior brackets uses α_{1,k+1}≤(L/2)α_{1,k}. This holds by CRE (2.28) at weak coupling, since g_{k+1}/g_k→1, for L≥3.

The Kotecký–Preiss weight a(Z)=δ½Lκ(d_{k+1}(Z)+1) differs from the weight of map D2.4(2), which D2.6 closure §2.4 uses downstream, and the amplitude ε̄₂ differs from the O(ε_k) that those callers assume. Consistency of both at those callers is not checked.

Still open:
- item 3, the tube norm ‖F‖_tube of the actual marks. (G.244a) and (G.244c) are bounds for holomorphic marks on the tube only, so a bounded-Borel mark or the cutoff derivative of CRE (3.28) is not covered;
- item 4, the moderate/large split of the retained field with its interacting tail, the propagation of the analytic domain through the later T and R operations, and the application to (1.60).

Item 4 is the hard estimate, and nothing in §§40–41 addresses it.

## 42. The Marks on the Tube

This section treats item 3 of §40.5. It states the tube norm, lists the actual marks of (G.206)–(G.207) and of CRE (3.28), and gives each one's bound or the input it still needs. The marks of (G.207) are integrated at the preliminary integral (1.60). The contour estimate there is part of item 4, so the bounds below are the factors that a (G.229)-type estimate will take once item 4 supplies the tube for (1.60). At the creation integral itself they apply as stated.

### 42.1 The Norm

In (G.229) a mark F enters only through its values on the contours of §39.2, where every label it reads has original argument |b|<r+C_ms<2r and the retained field has |a|_∞≤s. Accordingly

$$
\|F\|_{\mathrm{tube}}:=\sup\bigl\{|F(a,b)|:\ |a|_\infty\le s,\ |b_\ell|\le2r\ \text{for each integrated label }\ell\in\operatorname{supp}F\bigr\},
\tag{G.245}
$$

for F holomorphic on a neighbourhood of this set, with supp F⊂Y₀. A mark that is not holomorphic has no tube norm. It can still be admitted if it is a label restriction of the kind §39.2 already moves, which is the case for the cutoff marks of §42.3.

### 42.2 Holomorphic Marks

*The exponent mark D_j of (G.204).* Suppose D_j=Σ_YD_{j,Y} with pieces supported on connected Y; each piece is then a separate mark. That decomposition is assumed, not constructed: ΔK below is a Schur-complement block matrix, non-local with decay, and V_B∘R−V_A has to be split in the same way. It belongs to open item 1. The constant piece log(z_B/z_A)_Y drops out of every truncated correlation, so including it below is an overbound. For a piece,

$$
\|D_{j,Y}\|_{\mathrm{tube}}\le\Bigl|\log\frac{z^{(j)}_{B,Y}}{z^{(j)}_{A,Y}}\Bigr|
+\tfrac12\,\|(R^{\mathsf T}K_BR-K_A)_Y\|\,(\tfrac32r)^2\,|Y|
+\|V_{B,Y}\circ R-V_{A,Y}\|_{\mathrm{tube}}\;.
\tag{G.246}
$$

The last term reduces to the data difference by Schwarz's lemma. Suppose V_{A,Y} and V_{B,Y}∘R are the values at data θ_A and θ_B of one family V_Y(θ;·) with three properties: it is holomorphic in θ on the disc of radius ρ_θ about θ_A on the complex line through θ_B, it is bounded there on the tube by ω_Y, and |θ_B−θ_A|=η<ρ_θ. Then ‖V_{B,Y}∘R−V_{A,Y}‖_tube≤2ω_Yη/ρ_θ. The real rotation R preserves the complex tube, since |Rz|²=|Rx|²+|Ry|². This is a reduction, not an estimate: neither the θ-analyticity of the transported family nor the size of η is established here. Both are the aligned operator and background differences of Cauchy §10 and the LF note, which §37.3 already lists as their input.

The quadratic term of (G.246) carries the factor (3r/2)²=(9/4)A₁²(log g_k^{-2})^{2p₀}. Its local norm must therefore be o((log g_k^{-2})^{-2p₀}) for D_j's quadratic part to be a Mayer vertex of size less than one on the tube. The interpolated density e^{(1−t)S_A+tŜ_B} of (G.206) changes the Gaussian part to K_t=K_A+tΔK, with ΔK:=R^𝖳K_BR−K_A. If the exponentially weighted row norm of G_AΔK, the norm that carries the walk decay, is at most ½, the full inverse has a Neumann series. Here G_A is run A's free-coordinate covariance, and the weight rate is taken below its walk-bound decay rate, so that G_A is finite in the same weighted norm. The weighted row norm is submultiplicative, by the triangle inequality for the distance, so the Neumann series gives ‖K_t^{−1}‖_w≤2‖G_A‖_w for t∈[0,1]. The unweighted row norm gives boundedness but not decay. This is not yet the walk bounds of §§39.2–39.6. Those are for the localised and restricted covariances, the seed covariance G_σ, H_{ΛD}, and the σ(Δ)-deformed operators of RG2 (2.14). The inverse of a restricted or deformed K_{A,σ}+tΔK_σ is not the restriction of K_t^{−1}, and ‖G_{A,σ}ΔK_σ‖_w is not controlled by ‖G_AΔK‖_w. The interpolated gas needs the Neumann condition for every restricted and deformed covariance the gas uses, uniformly in σ. That condition is open, with η. K_t is positive without further condition, as a convex combination of the positive forms K_A and R^𝖳K_BR.

*Insertions.* Consider an insertion that is a character of a product of link variables, each of the form exp i[g_jCb−hD̃(g_jCb)]V^{(j)} (§38.1). Let ρ be the representation. On the tube |g_jCb|≤C g_jr, which is Cδ_k at j=k, and hD̃ is analytic with hD̃(X)=O(|X|²), so the exponent has size at most C′g_jr. Using ‖exp(Y)‖≤e^{‖Y‖} and |tr_ρM|≤d_ρ‖M‖ gives

$$
\|I\|_{\mathrm{tube}}\le d_\rho\,e^{c_\rho C'g_jr\,n_I}\;,
\tag{G.247}
$$

where n_I is the number of links of the insertion whose variables read integrated or retained coordinates. For a retained coordinate the bound is the same where a enters through the same Lie-algebra exponent, since |a|_∞≤s<2r; a link whose V^{(j)} itself depends on the complex retained field is not unitary and is not covered. Links at real fixed data are unitary and contribute norm one. This uses no property of SU(N): c_ρ is the norm of the complex-linear extension of ρ_* to 𝔤_ℂ, for any compact G and any unitary representation ρ; with the Hermitian norm it is at most √2‖ρ_*‖. The same bound with 2d_ρ holds for the insertion difference Î_B−I_A. At real a with real actions |c_A|≤d_ρ, so ‖I_A−c_A‖_tube≤2d_ρe^{c_ρC′g_jrn_I}. On the complex ball c_A is a complex normalised functional, and (G.244c) gives |c_A|≤d_ρe^{c_ρC′g_jrn_I}e^{(81A′+729K+681)#(D′_I)} instead; (G.255) does not use c_A. Smallness of Î_B−I_A beyond this is again a data difference, treated as for V in (G.246). The links read by I lie in supp I⊂D′, so the factor e^{c_ρC′g_jrn_I} is not paid by the root decay of (G.244a), which is relative to D′. It depends on the insertion only. n_I counts links and can exceed #(D′_I) by a factor of order LM, so the factor is at most e^{#(D′_I)}, of the kind in (G.244c), once g_jr≤#(D′_I)/(c_ρC′n_I); this holds for g_K small at fixed L and M, since g_jr→0.

(G.247) presupposes the link form above. If the insertion sits on a finer lattice than the block lattice, its links are components of U_k(·) in CRE (3.28)'s writing, and their tube bound is then U_k's analyticity bound, not the elementary exponential bound. Which form the actual insertion has is not checked here.

### 42.3 The Cutoff-Difference Marks

The tests of (G.233) are sharp per-bond indicators, so for run r=A,B the bond factor is χ_{r,b}=𝟏_{|b_b|<r_r}, and χ_{*,b}=𝟏_{|b_b|<r_min} with r_min:=min(r_A,r_B). The distinguished factor of E_{r,b} in (G.205) is then

$$
\chi_{r,b}-\chi_{*,b}=\mathbf 1_{|b_b|\ge r_{\min}}-\mathbf 1_{|b_b|\ge r_r}\;,
\tag{G.248}
$$

a difference of two complement-of-ball restrictions at the single label b. Since r_r≥r_min, it is the annulus indicator 𝟏_{r_min≤|b_b|<r_r}. The two complement-of-ball terms are not moved separately. On each of them |b| is unbounded, and §39.2 moves such a restriction only at labels that no selected interaction or mark reads. The label b may be read by a selected interaction of the hybrid gas or by a second mark, such as the insertion when b∈supp I. The annulus is therefore moved as one bounded region. Stokes' formula gives its real translate and its inner and outer sides, and on all of them |b|≤r_max+C_ms. After the move, b is a bad label in the sense of (G.229), at radius at least r_min. Suppose the run thresholds satisfy

$$
\tfrac34\,r_A<r_B\le\tfrac54\,r_A\;,
\tag{G.249}
$$

and put r:=r_A. The constant c₀ is further restricted so that (C_m+C′)s≤r/4. Then every hybrid cutoff of (G.205), and the moved annulus, keeps the labels read by the selected interactions and marks in |b|≤(5/4)r+C_ms≤(3/2)r. For the objects of the two runs in §§42–43 the tube norm is taken over this reach: (G.245) with (3/2)r_A in place of 2r. By §39.2 each run's holomorphic tube is |b|<2r_r with its own threshold, and (3/2)r_A<2r_B by the strict lower bound in (G.249), so this set lies inside both runs' open tubes. It is the set on which the contours of §39.2 read the marks, so (G.244a) holds with this norm. The distance of a moved label from the marginal mean is then at least r_min−(C_m+C′)s≥r/2. So the annulus, its translate and its two sides, costs at most three times the bad-label factor Ce^{−c_1r²} of (G.229), the sides at the side factor of (G.229).

*The annulus as a mark (derived given (G.229) with b in S).* E_{r,b} is not a holomorphic mark. It replaces the restriction at b, so it is a replacement mark, not a factor under the (b−1) gas. Its per-term bound is (G.229) with b added to the set S of labels that the marginal argument of §39.3 treats, as for the surface label of (G.251): the translate of b and each of its two sides contribute at most Ce^{−c₁r²}, together at most 3Ce^{−c₁r²}, and every other factor of (G.229) is unchanged. So the per-term bound of the selection whose seed contains b has the form of the per-term bound in the transfer of §41.3, with ‖F‖_tube replaced by 3Ce^{−c₁r²}. b lies in D⊂Y₀ and not in the bad-bond set P⊂Y₀^{c*}, so the payments of D2.4(10)(e) are unchanged, and the transfer of §41.3 gives (G.244a) with 3Ce^{−c₁r²} in place of ‖F‖_tube. For a single label b, D is the union of the π_k-cubes meeting b. A set of diameter at most one side meets at most 3⁴=81 closed cubes, so #(D′_b)≤81#_k(D)≤81·81=6561 by D2.4(10)(a), and m_D=1. Hence

$$
|H'_{E_{r,b}}(Z_0;a)|\le3C\,e^{-c_1r^2}\,e^{81\cdot6561A'}\,e^{-(1-5\delta)\lambda_L\kappa\,d_{k+1}(Z_0;D'_b)}\;.
\tag{G.250}
$$

For a single-label mark d_{k+1}(Z₀)≤d_{k+1}(Z₀;D′_b)+C, so the decay is also in d_{k+1}(Z₀) up to a constant. The hybrid gas has thresholds that vary from label to label within [r_min,r_max]. (G.243), (G.244) and (G.244a) are used for it with constants uniform over such mixed thresholds. Each bad-label factor only improves with a larger threshold, but the transfer of the proofs of Lemma 3 and D2.4(10)(b) to mixed thresholds is not checked.

The mark costs no holomorphy, and its factor is superpolynomially small in g_k. With r=A₁(log g^{-2})^{p₀} in each run, (G.249) is the condition (log g_B^{-2})/(log g_A^{-2})∈[(3/4)^{1/p₀},(5/4)^{1/p₀}] at the step concerned. It holds trivially when the two runs have the same coupling there, since E_{r,b}=0 then. The comparability of the run couplings is not checked here: it belongs to the coupling matching of the Cauchy note. A cutoff difference at a retained label is not a mark of the inner integral. By (G.233) that indicator is allocated to the outer integrand, and its contribution to the comparison is not bounded in §§42–43 (§42.5 item 6).

The sums Σ_b in (G.207) run over all labels. In lines three and four each term carries the centred insertion. A summable bound in b therefore needs the decay of the connected correlation between the cutoff mark at b and the insertion, which is the two-mark version of (G.244). That version is not derived here.

### 42.4 The Cutoff Derivative of CRE (3.28)

The first expression of (3.28) contains ⟨A_k,C^*Δ^{(k)}CC^{(k)}(Λ_{k+1})δχ^{(k)}/δA⟩. This is the Gaussian integration by parts of the cross term ⟨A,C^*Δ^{(k)}CA_k⟩, so with sharp tests δχ^{(k)}/δA is a surface measure.

*On the route of §§39–41 it is not used.* That route keeps the cross term in the compensated shift (G.226), and §41.3 makes log 𝒵(a) analytic and zero-free on |a|_∞≤s. The A_k-dependence is therefore log 𝒵(a)−log 𝒵(0)=Σ_𝒞[φ^T(𝒞;a)−φ^T(𝒞;0)]. A cluster depends on a through m_σ, the compensator of (G.230), and the selected interactions, which carry the direct A_k-dependence of P^{(k)} and E_k in (3.28)–(3.29) (§41.1). All three are localised next to Λ_{k+1}∩D, so a cluster depends on a only if a footprint reaches there. This is Bałaban's "at least one localization in Ω_{k+1}∖Λ_{k+1}". The terms linear in A_k, and the derivatives in a, follow from Cauchy's estimate: at a with |a|_∞≤s/2 and a direction e with |e|_∞≤1 supported on the labels of one π_{k+1}-cube Q, |∂_e^n log 𝒵(a)|≤n!(s/2)^{−n}·9K·#(Q̂), where Q̂ is the set of cubes whose polymers' activities can depend on a|_Q. For a general e the bound is summed over the cubes meeting supp e. #(Q̂) is finite only if the a-dependence of H(Z;a) is local; §41.1 asserts the localisation through m_σ but does not quantify it, and if m_σ has exponential tails, #(Q̂) is replaced by a weighted sum. That quantification is open. No derivative of an indicator occurs.

The scope is |a|_∞≤s. CRE's small-field condition allows |A_k(b)| up to δ_k, that is, up to r in rescaled units, far beyond s=c₀r. The real range s<|a|_∞≤r is not covered by this route. It belongs to the moderate/large split of item 4.

*If (3.28) is kept, the surface mark is a side label.* By (G.233) each integrated bond carries exactly one indicator, because duplicates are idempotent, so the derivative at a label ℓ is −n_ℓδ(|b_ℓ|−r) times the other indicators. The term is then the integral over the real sphere |b_ℓ|=r of v_ℓ(a)·n_ℓ times the remaining integrand, with v_ℓ(a):=(C^{(k)}(Λ_{k+1})C^*Δ^{(k)}CA_k)_ℓ. It is linear in a, and the walk bound gives |v_ℓ|≤Cs e^{−δ₀ dist(ℓ,∂Λ_{k+1})}. All other labels are moved as in §39.2. At ℓ the original coordinate stays on the real sphere, so the imaginary part of the shifted variable is supported on S∪{ℓ}, with |Im z_ℓ|=|Im m_ℓ|≤C_ms. Then (G.228) and the marginal argument of §39.3 apply with ℓ added to S. The distance from the mean is at least r−C_ms−C′s≥r/2, which gives the factor

$$
C\,r^{\dim\mathfrak g-1}\,Cs\,e^{-\delta_0\operatorname{dist}(\ell,\partial\Lambda_{k+1})}\,e^{-c_1r^2}
\tag{G.251}
$$

at ℓ, the side-label factor of (G.229) with the extra decay. The normaliser Z_t of (3.29) is uncompensated. It is the nonzero scalar exp(⟨ta,Q_Dta⟩/2) times the compensated integral at ta, |ta|_∞≤s, which is zero-free by §41.3. Bałaban's representation therefore also holds on the complex ball, with this bound.

### 42.5 Status

Derived here:
- the norm (G.245);
- the insertion bound (G.247) for character insertions;
- the two-run tube norm on |b|≤(3/2)r_A, inside both runs' tubes under the strict (G.249);
- the cutoff-mark bound (G.250), given the threshold comparability (G.249), with the annulus moved as one region and treated as a replacement mark through (G.229) with b in S;
- the surface-mark bound (G.251), as a per-label factor; the bound on the whole first expression of (3.28), which needs the surface term as a replacement mark with (G.244c)-type root summation and the sum over ℓ, is not done;
- the statement that the §§39–41 route needs no cutoff derivative, with the representation on |a|_∞≤s and the derivative bounds on |a|_∞≤s/2 per cube of supp e, given the locality of the a-dependence (open).

Reviewed (lf-gamma-marks3): the items above are correct at their stated scope after the corrections made; the Neumann transfer and the decomposition D_j=Σ_YD_{j,Y} were unsupported and are now open items.

All rest on §§39–41 and their premises (§41.4).

A reduction only: the tube norm of the exponent mark D_j, (G.246), reduces to the run data difference η and to the quadratic difference ΔK. Their sizes are the inputs of Cauchy §10 and the LF note, and are not estimated here.

No bounded-Borel mark occurs among the actual marks. The cutoffs and their differences are label restrictions (§42.3). The smooth cutoff acts only on S_{k+1}⊂D (§39.6). The insertions are holomorphic (§42.2).

Open:
1. The data difference η, the θ-analyticity of the transported family, the size of ΔK in (G.246), the decomposition D_j=Σ_YD_{j,Y} into connected local pieces, and the decay of ‖D_{j,Y}‖_tube in Y.
2. The comparability (G.249) of the run thresholds, that is, of the run couplings at the step concerned.
3. The two-mark version of (G.244), which the sums Σ_b of (G.207) need. This is derived in §43.3 as (G.254).
4. Item 4 of §40.5, unchanged: the moderate/large split with its interacting tail, the propagation through later T and R, and the application to (1.60).
5. The transfer of the proofs of Lemma 3 (with R-L3) and of D2.4(10)(b) to the hybrid gases with mixed thresholds in [r_min,r_max] and to the interpolated gases of (G.206), with uniform constants (§42.3, §43.2).
6. The cutoff differences at retained labels, which (G.233) allocates to the outer integrand.
7. The link form of the actual insertion: if its links are components of U_k(·), (G.247) is replaced by U_k's analyticity bound on the tube.

## 43. A Volume-Free Form of the Comparison (G.207)

This section treats open item 3 of §42.5 and replaces the use of (G.207) for estimates. It is a statement about the polymer gas of §41, and so applies where that gas is available: at the creation integral now, and at (1.60) once item 4 supplies it there.

### 43.1 Why (G.207) Is Not Bounded Term by Term

Put Z_t^*:=∫χ_*e^{(1−t)S_A+tŜ_B}du, and let R_t^* be the normalised expectation for this density. The second line of (G.207) equals ∫_0^1(Z_t^*/Z_B)R_t^*[(I_A−c_A)D_j]dt. At t=0 the ratio Z_A^*/Z_B is the exponential of a free-energy difference, which one expects to be of order η|Λ|; no estimate of it is given here. Moreover R_t^*[(I_A−c_A)D_j] contains (R_t^*[I_A]−c_A)R_t^*[D_j], and R_t^*[D_j] is a sum over all local pieces. The fourth line carries Z_A/Z_B. These factors cancel between the lines of the exact identity, but not in absolute values. So (G.207) remains a correct identity, but its term-by-term absolute bounds are not volume-free unless Z_t^*/Z_B and Z_A/Z_B are controlled separately, and the bounds below use the normalised form (G.252).

### 43.2 The Normalised Identity

For r=A,B and the ordered labels define the hybrid cutoffs χ_r^{(b)}:=∏_{c≤b}χ_{r,c}∏_{c>b}χ_{*,c}. Then χ_r^{(0)}=χ_*, χ_r^{(N)}=χ_r and χ_r^{(b)}−χ_r^{(b−1)}=E_{r,b} by (G.205). Let 𝒵_r^{(b)} and R_r^{(b)} be the integral and the normalised expectation with density χ_r^{(b)}e^{S_r}, with Ŝ_B for r=B. Write 𝒵_r[E_{r,b}X]:=∫E_{r,b}Xe^{S_r}du, and R[X;Y]:=R[XY]−R[X]R[Y]. When every 𝒵_r^{(b)} and Z_t^* for every t∈[0,1] is nonzero,

$$
\begin{split}
R_B[I_B]-R_A[I_A]
={}&\sum_b\Delta_{B,b}[\widehat I_B]+R_B^*[\widehat I_B-I_A]\\
&+\int_0^1\sum_YR_t^*[I_A;D_{j,Y}]\,\mathrm dt-\sum_b\Delta_{A,b}[I_A]\;,
\end{split}
\tag{G.252}
$$

$$
\Delta_{r,b}[I]:=R_r^{(b)}[I]-R_r^{(b-1)}[I]
=\frac{\mathcal Z_r[E_{r,b}I]-R_r^{(b-1)}[I]\,\mathcal Z_r[E_{r,b}]}{\mathcal Z_r^{(b)}},
\qquad
\frac{\mathcal Z_r^{(b)}}{\mathcal Z_r^{(b-1)}}=1+\frac{\mathcal Z_r[E_{r,b}]}{\mathcal Z_r^{(b-1)}}\;.
\tag{G.253}
$$

The proof has four steps:
- R_B[I_B]=R_B[Î_B] by the pull-back (G.203).
- The cutoff steps telescope from χ_* to χ_r. Each step gives (G.253) from 𝒵_r^{(b)}=𝒵_r^{(b−1)}+𝒵_r[E_{r,b}].
- The insertion is exchanged under R_B^*=R_1^*.
- d/dt R_t^*[X]=R_t^*[X;D_j], because the t-derivative of the exponent is Ŝ_B−S_A=D_j on the support of χ_*, and D_j=Σ_YD_{j,Y}.

Every term of (G.252) is a normalised one-mark or truncated two-mark ratio. The quotient 𝒵_r[E_{r,b}]/𝒵_r^{(b−1)} is a one-mark ratio for the (b−1) gas with a replacement mark: E_{r,b} and χ_r^{(b−1)} agree off b, and at b the annulus restriction (G.248) replaces the ball restriction of χ_r^{(b−1)}, the two having disjoint supports there. Likewise R_r^{(b−1)}[E_{r,b};I] stands for 𝒵_r[E_{r,b}I]/𝒵_r^{(b−1)}−R_r^{(b−1)}[I]𝒵_r[E_{r,b}]/𝒵_r^{(b−1)}. Its polymer form has the root containing b and the non-root activities of the (b−1) gas. By (G.244c) with N(E_{r,b})=3Ce^{−c₁r²} (§42.3) and #(D′_b)≤6561, that ratio is at most 3Ce^{−c₁r²}e^{6561C_Ψ}, with C_Ψ≥81A′+729K+681 of §43.3. This is superpolynomially small in g_k, so 𝒵_r^{(b)}/𝒵_r^{(b−1)}=1+O(e^{−c₁r²}), and its modulus lies in [½,2] for g_k small.

§§43.3–43.4 use more than nonvanishing. For every hybrid gas R_r^{(b)} and every interpolated gas R_t^* they use (G.243) and the Kotecký–Preiss condition of §41.3, hence (G.244)–(G.244c) and (G.254). These are inputs, not derived here (§42.5 item 5). Four things are needed:
- The hybrid thresholds lie in [r_min,r_max]. The proofs of Lemma 3 and D2.4(10)(b) must hold with constants uniform over such mixed thresholds.
- The interpolated activities. Lemma 3's proof uses Cauchy representations in τ(Y), so it needs sup bounds on T_Y over an enlarged τ-disc. The sup of |(1−t)T_{A,Y}+tT_{B,Y}| is at most (1−t)sup|T_{A,Y}|+t sup|T_{B,Y}|, so those bounds hold for the interpolated activities whenever both runs satisfy them.
- The interpolated quadratic form needs §42.2's Neumann condition for every restricted and σ-deformed covariance the gas uses, uniformly in σ, not only for G_AΔK. Its positivity is automatic.
- The marked roots of the hybrid and interpolated gases factorise over their components. RG2 (2.10) proves this for Bałaban's own H. For the compensated family (G.230), with its a-dependent mean m_σ, compensator and seed covariance G_σ, it is a new requirement on (G.230), which RG2 (2.10) does not supply. It is open with (G.230).

The marks of the run-B objects are read on |b|≤(3/2)r_A, inside run B's tube under the strict (G.249) (§42.3), and the annulus marks enter through (G.229) with b in S (§42.3).

If S_A and Ŝ_B are real on the real support, every normaliser is positive. That gives nonvanishing at real a but not the majorant.

### 43.3 The Truncated Two-Mark Bound

Take a gas with activities H(Z) obeying (G.243) and the Kotecký–Preiss condition of §41.3, and two marks F₁, F₂. Each has a size N(F): N(F)=‖F‖_tube for a holomorphic mark, and N(E_{r,b})=3Ce^{−c₁r²} for a cutoff mark (§42.3). For each mark let D_F and D′_F be the sets D and D′ of §41.3, and m_F the number of wall-components of D_F, as D2.4(10)(b) charges them ("per wall-component of D beyond the first", map l.1501).

The marks that occur have m_F=1. The insertion's support and Y are connected, and so is a label. The closed π_k-cubes containing a point form a box of cubes, wall-connected, and overlapping boxes chain together, so D_F is wall-connected. Only m_F=1 is treated. Every component of a root contains a cube of D_F, since a component that contains none is a vacuum polymer (D2.4(10)(a)). With m_F=1, D_F lies in one component, so the root is connected.

By (G.244a) the root activities obey |H′_F(Z)|≤N(F)e^{81A′#(D′_F)}e^{−ϱ_L d(Z;D′_F)}, with ϱ_L:=(1−5δ)λ_Lκ and d=d_{k+1}. For F=F₁F₂ the same holds with D′=D′₁∪D′₂, the factor e^{(5+3λ_L)κ} for m≤2, and N(F₁F₂)≤N(F₁)N(F₂). Put

c′:=δλ_Lκ,  D₁₂:=dist(D′₁,D′₂)/(LM),  Ψ(F):=N(F)e^{C_Ψ#(D′_F)},  C_Ψ:=81A′+2187K′+681,

with K′ defined below; K′≥K.

Two geometric facts are used.
- If a set Z₀⊇D′₁∪D′₂ has a component meeting both D′₁ and D′₂, then d(Z₀;D′₁∪D′₂)≥D₁₂. A set G admissible for d contains a path from D′₁ to D′₂. Its part between the last exit from D′₁ and the first entry into D′₂ lies outside D′₁∪D′₂ and has length at least dist(D′₁,D′₂).
- Two cubes that share a cube or a wall lie in a set of diameter at most 5LM, in the Euclidean norm and in the ℓ¹ norm. So joining two admissible sets at such cubes costs at most 5. This is the join cost of RG2 (2.27), "Σ_{Y∈𝐃}(d_k(Y)+5)≥d_k(Y₀)+5".

Let Φ(Z):=Σ_{𝒞≁Z}φ^T(𝒞), and let Φ₁₂(Z₁,Z₂) be the same sum over the clusters incompatible with both Z₁ and Z₂. For compatible roots Φ(Z₁∪Z₂)=Φ(Z₁)+Φ(Z₂)−Φ₁₂, by inclusion–exclusion over the clusters incompatible with Z₁ or with Z₂.

For compatible connected roots, H′_{F₁F₂}(Z₁∪Z₂)=H′_{F₁}(Z₁)H′_{F₂}(Z₂). For Bałaban's own H, H of a domain is the product over its components (RG2 (2.10), map D2.4(2)), and each mark multiplies only the integrand of the component containing its support (§41.1). For the (G.230)-type gases, with the a-dependent mean m_σ, the compensator and G_σ, this factorisation is the fourth input of §43.2, open with (G.230); the bound below is conditional on it. This uses m_F=1: with m_F>1 a root can have several components, and the factorisation would need the marks to factorise over them.

Expanding numerator and product as in (G.242) and (G.244) gives

$$
R[F_1;F_2]=\sum_{Z_0\supset\operatorname{supp}F_1\cup\operatorname{supp}F_2}H'_{F_1F_2}(Z_0)e^{-\Phi(Z_0)}
+\sum_{Z_1\sim Z_2}H'_{F_1}H'_{F_2}e^{-\Phi(Z_1)-\Phi(Z_2)}\bigl(e^{\Phi_{12}}-1\bigr)
-\sum_{Z_1\not\sim Z_2}H'_{F_1}H'_{F_2}e^{-\Phi(Z_1)-\Phi(Z_2)}\,.
$$

Here Z_i⊇D′_i is connected, and the first sum runs over connected Z₀⊇D′₁∪D′₂. Write d_i:=d(Z_i;D′_i).

*Attached clusters.* By (G.244) and (G.244b), |Φ(Z)|≤9K#(Z)≤9K(81#(D′)+243d(Z;D′)).

*Φ₁₂.* A cluster 𝒞 incompatible with both Z₁ and Z₂ joins them. By the two geometric facts, D₁₂≤d₁+d₂+Σ_{γ∈𝒞}(d(γ)+5)+5. Hence

|Φ₁₂|≤e^{−c′(D₁₂−d₁−d₂−5)}Σ_{𝒞≁Z₁}|ϕ(𝒞)|∏_{γ∈𝒞}w′(γ),  w′(γ):=|H(γ)|e^{c′(d(γ)+5)},

with ϕ(𝒞) the Ursell coefficient alone, Friedli–Velenik's ϕ; elsewhere φ^T(𝒞) includes the activities. The Kotecký–Preiss condition holds for w′ with a′(Z):=c′(d(Z)+1). Indeed w′e^{a′}≤2(L+2)⁴O₃ε̄₂e^{6c′}e^{−(1−10δ)½Lκd}, since λ_L≤L/2, so the check of §41.3 goes through once 9·162·K′≤c′, where K′:=2(L+2)⁴O₃ε̄₂e^{6c′}C′_Σ and C′_Σ is §41.3's sum at rate (1−10δ)½Lκ. With RG2's δ=(1−2/L)/10 that rate is exactly κ, so C′_Σ is finite once κ≥κ_{(1.26)}, which δκ/2≥κ_{(1.26)} of §41.2 implies. Threshold (e) gives ε̄₂e^{3λ_Lκ}≤1, and e^{6c′}≤e^{0.6λ_Lκ}, so the condition holds for κ large. Under (R-m′) it holds for g_K small. The first step of the proof of Lemma 5.6, as in §41.3, then gives

$$
|\Phi_{12}(Z_1,Z_2)|\le9K'\#(Z_1)\,e^{-c'(D_{12}-d_1-d_2-5)}\;,\qquad|\Phi_{12}|\le9K\#(Z_1)\;.
$$

*Collecting.* Assume 6561K′+c′≤ϱ_L/2 and ϱ_L≥486 log 12800, so that the root count of §41.3 applies to every sum below at rate ϱ_L/2.
- One root: d(Z₀;D′)≥D₁₂ by the first geometric fact. Extracting e^{−c′D₁₂} and summing with the root count bounds the first sum by e^{(5+3λ_L)κ}e^{−c′D₁₂}Ψ(F₁)Ψ(F₂).
- Incompatible pairs: D₁₂≤d₁+d₂+5 by the second geometric fact. Extracting e^{−c′(D₁₂−5)} bounds the third sum by e^{5c′}e^{−c′D₁₂}Ψ(F₁)Ψ(F₂).
- Compatible pairs: |e^{Φ₁₂}−1|≤|Φ₁₂|e^{|Φ₁₂|}≤e^{9K′#(Z₁)}e^{9K#(Z₁)}e^{−c′(D₁₂−d₁−d₂−5)}, using x≤e^x for x=9K′#(Z₁). With e^{−Φ(Z₁)−Φ(Z₂)}, Z₁ carries at most e^{27K′#(Z₁)}≤e^{2187K′#(D′₁)}e^{6561K′d₁}. This bounds the second sum by e^{5c′}e^{−c′D₁₂}Ψ(F₁)Ψ(F₂).

Hence

$$
|R[F_1;F_2]|\le C_T\,\Psi(F_1)\Psi(F_2)\,e^{-c'D_{12}}\;,\qquad C_T:=e^{(5+3\lambda_L)\kappa}+2e^{5c'}\;.
\tag{G.254}
$$

The coefficient Ψ(F) is exponential in #(D′_F), as in (G.244c).

### 43.4 The Resulting Bound

By (G.253), Δ_{r,b}[I]=(𝒵_r^{(b−1)}/𝒵_r^{(b)})R_r^{(b−1)}[E_{r,b};I], a truncated two-mark ratio for the (b−1) gas, and 𝒵_r^{(b−1)}/𝒵_r^{(b)}≤2 by §43.2. Insert (G.244c), (G.247), (G.250) and (G.254) into (G.252). With D(b,I) and D(Y,I) the D₁₂ of the respective pairs,

$$
\begin{split}
|R_B[I_B]-R_A[I_A]|\le{}&|R_B^*[\widehat I_B-I_A]|
+2C_T\,\Psi(I)\Bigl[\sum_{r=A,B}\sum_b\Psi(E_{r,b})\,e^{-c'D(b,I)}\\
&+\sup_t\sum_Y\Psi(D_{j,Y})\,e^{-c'D(Y,I)}\Bigr]\;,
\end{split}
\tag{G.255}
$$

with Ψ(I):=max(Ψ(I_A),Ψ(Î_B)), whose supports coincide under the label-wise R, Ψ(E_{r,b})≤3Ce^{−c₁r²}e^{6561C_Ψ}, and Ψ(D_{j,Y})=‖D_{j,Y}‖_tube e^{C_Ψ#(D′_Y)}.

The first term has two bounds. At real a, with real actions, R_B^* is a probability measure and |R_B^*[Î_B−I_A]|≤sup|Î_B−I_A| on the real common support. On the complex domain R_B^* is a complex normalised functional, and the supremum bound fails. There (G.244c) gives |R_B^*[Î_B−I_A]|≤‖Î_B−I_A‖_tube e^{(81A′+729K+681)#(D′_I)}. By §42.2 this has no smallness unless the insertion data difference is reduced like V in (G.246). A Cauchy estimate needs the complex form.

The sum over b is volume-free. The number of labels b with D(b,I)≤n is at most polynomial in n times #(D′_I). The cutoff part is superpolynomially small in g_k, since e^{−c₁r²} beats the constant e^{6561C_Ψ} for g_k small.

The bound on the sum over Y converges if ‖D_{j,Y}‖_tube decays faster than e^{C_Ψ#(D′_Y)} grows. D_Y consists of the π_k-cubes meeting Y, its touching cubes included, so by D2.4(10)(a) and D2.4(2)(a) #(D′_Y)≤81#_k(D_Y)≤81²#_k(Y)≤6561·162(d_k(Y)+1). The sum over Y at a fixed distance also carries the lattice-animal entropy of Y. So a decay rate above 6561·162·C_Ψ+c_anim per unit of d_k(Y) suffices, with c_anim the lattice-animal constant at the scale k. Since C_Ψ≥681 independently of κ, that rate is at least about 7×10⁸. The decay of ‖D_{j,Y}‖_tube in Y belongs to open item 1 of §42.5. If D_{j,Y} decays at a rate of order κ, κ must be chosen above about 10⁹, and the compatibility of that order with the other κ-dependent choices (e^{(5+3λ_L)κ} in C_T, threshold (e)) is not checked. The rate is an artefact of the crude count #(D′_Y)≤81²·162(d_k+1).

The coefficient Ψ(I) is exponential in the number of π_{k+1}-cubes of D′_I, which for a Wilson loop is its length in those cubes. (G.255) contains no partition-function ratio. Its sum over b is volume-free, and its sum over Y is volume-free provided ‖D_{j,Y}‖_tube decays at the rate above (open item 1). The coefficient Ψ(I) is not small and does not shrink with the loop's scale.

For the creation term (1.62) the same steps give the localised form

$$
\log Z_B-\log Z_A=\sum_b\log\frac{\mathcal Z_B^{(b)}}{\mathcal Z_B^{(b-1)}}-\sum_b\log\frac{\mathcal Z_A^{(b)}}{\mathcal Z_A^{(b-1)}}+\int_0^1\sum_YR_t^*[D_{j,Y}]\,\mathrm dt\;,
$$

with each cutoff term O(e^{−c₁r²}) and each R_t^*[D_{j,Y}] a one-mark ratio bounded by (G.244c). The logarithms are defined by continuity along the interpolation, with the principal branch for the factors 1+O(e^{−c₁r²}). Each log ratio depends on the whole label ordering through its hybrid gas. That this dependence on distant labels and on the ordering decays with the clusters is expected but not estimated here, so the form is localised only in the sense that each term is a one-mark ratio. The explicit coupling correction of (1.62) is not treated here.

### 43.5 Status

Reviewed (lf-gamma-marks3), correct as conditional derivations given their inputs, with corrections since made (the annulus constant 3, the per-cube derivative bound, the conditional volume-freeness of the Y-sum):
- the normalised identity (G.252)–(G.253);
- the truncated two-mark bound (G.254) for marks with one wall-component, in the relative-decay form of (G.244a). This closes open item 3 of §42.5;
- the bound (G.255), with its first term in the real and the complex form; volume-free in the sum over b, and in the sum over Y given the decay of ‖D_{j,Y}‖_tube;
- the creation-term identity, with each term a one-mark ratio.

These rest on §§39–42 and their premises (§41.4), on the strict (G.249), and on the inputs of §43.2: (G.243) and the Kotecký–Preiss condition for every hybrid and interpolated gas (§42.5 item 5), the Neumann condition for every restricted and σ-deformed covariance, and the component factorisation of the marked roots of the (G.230)-type gases, a new requirement on (G.230).

Open, in addition to §42.5: the decay of ‖D_{j,Y}‖_tube at a rate above 6561·162·C_Ψ+c_anim, with its order of constants; the decay of the creation-term log ratios in distant labels and in the ordering. They hold for any gas that satisfies these. §43.1's statement about the volume factors of (G.207) is a remark, not an estimate.

The bound (G.255) is an estimate in terms of ‖D_{j,Y}‖_tube and ‖Î_B−I_A‖_tube, which are data differences. It is not yet an estimate of the Cauchy difference, because those data differences (§42.5 items 1–2) are open. The sum over Y needs a decay of ‖D_{j,Y}‖_tube faster than e^{C_Ψ#(D′_Y)}. The coefficient Ψ(I) is exponential in the loop's length in π_{k+1}-cubes. Applying it to (1.60) needs item 4.

## 44. The Non-Minimiser Defect of the Entries (Point (3) of (LF-A))

This section treats the defect named in the LF note's point (3) of (LF-A) and in its bullet *The renormalised terms at the entries*: the entries c(t) = e^{it(ε/L)𝐒_c}c^B of the joint line are not local minimisers of their own data for t ≠ 0, so RG I's renormalisation, which evaluates a term at the local minimiser of its data, does not apply to the renormalised 𝐄- and 𝐑-terms at c(t) as it stands. The LF note names two defects, 𝐄(X, c(t)) − 𝐄(X, U_j(□₀, M^·(c(t)))) and A(h_z, c(t)) − A(h_z, U_j(□₀, M^·(c(t)))). Under the project's layer transposition of Bałaban's extension of the near-domain terms (R-data), with the counterterm reading the configuration that the terms read (the clause of 62.3), both defects are zero, and the renormalised terms at c(t) are bounded on the whole Cauchy disc by their age bound (64.5). The Cauchy estimate of the variation (ii) then gives the product of the age bound and the depth. Notation is the Cauchy note's §5 and the LF note's §4(d): z a point of the layer n, j ≤ n the generation of the term, a_n = εL^n, □₀ the near domain of z at the layer scale, and α_m the class radius of the layer.

### 44.1 The Near-Domain Terms Read the Block Data

RG I p.275 l.1–7 introduces the variables 𝐔, 𝐉 of the near-domain terms as follows: "in the interior averages M^·(U_{k+1}) we replace the configuration U_{k+1} by 𝐔", and "the configuration U_{k+1} is replaced by the configuration U_{k+1}(□₀, M^·(𝐔)), extended as equal to 𝐔 outside □₀" in the function 𝐇_k and the averaging operations Q_j, "in order to get better properties with respect to gauge transformations". The resulting function is (3.24), 𝐄^{(j)}(X, U_j(□₀, exp iB̃_□ M^·(U_{k+1}(□₀, M^·(𝐔))))), and Lemma 4 and the renormalisation of pp.279–290 are proved for it. At a fluctuation B̃_□ = 0 it reads 𝐔 only through M^·(𝐔) on □₀, since X ⊂ □̃², with the composite's own current J_j(□₀, ·) of (3.53): p.275 l.12–13, "we should replace the function 𝐄^{(j)}(X, U_j) by 𝐄^{(j)}(X, U_j, J_j)". CRE p.280 l.14–20 says that (I.3.3), (I.3.18)–(I.3.28) "have a bit different meaning now, because the configuration U_k, or U_{k+1}, restricted to Ω_n∖Ω_{n+1} coincides with a U_n-type configuration, but the difference is seen in bounds only", prints the bounds "in the L^{−n}-scale instead of the η-scale", and specialises "for the proof of Theorem 2 we put 𝐇_k(B′) = 0 in (I.3.28), or 𝐀 = 0 in (I.3.30)" (p.280 l.18–20). It does not print the layer's U_n(□₀, ·) in place of U_{k+1}(□₀, ·): that transposition is the project's adaptation (§55.1). The far-domain terms are extended by direct substitution, (3.13), and need no age bound, since they carry (3.48).

**R-data (Bałaban's at the newest scale; the project's adaptation at the layer, §55.1).** At the step of the R-operation, a renormalised near-domain term of the generation j at a point z of the layer n, as a function of a pair (𝐔, 𝐉) of the class, is

$$
\mathbf E^{(j)}\bigl(X,\,U_j(\square_0,M^{\cdot}(P_n\mathbf U))\bigr),\qquad P_n\mathbf U:=U_n(\square_0,M^{\cdot}(\mathbf U))\ \text{on }\square_0,\quad P_n\mathbf U:=\mathbf U\ \text{outside }\square_0,
\tag{G.256}
$$

with the composite's current, and the counterterm of z, β_jA(h_z, ·), and its per-domain pieces c_X of §47, read P_n𝐔 as well (the clause of 62.3). This is Bałaban's extension of these terms at B̃_□ = 0, transposed to the layer by the project, and taken as the project's definition of V(Y)'s renormalised near-domain terms. The specialisation to B̃_□ = 0 is CRE p.280 l.18–19. At the configurations of the fluctuation-dependent expansions of LFR II (1.59)–(1.60), the near-domain terms are read in the same way at each configuration 𝐔 of the space at which they are evaluated, since (G.256) is a function of 𝐔 alone; the pieces (iv), (α), and (δ) that read them there are treated in §70 and §72. For these terms the current part of the Cauchy note's pair line is absent, since the current is the composite's.

The far-domain terms and the unrenormalised terms keep the pair extension and the pair line's treatment.

### 44.2 The Composite Is the Layer's Local Minimiser

*Feasible sets (derived).* For every 𝐔 of Lemma 4's extended space, U_j(□₀, M^·(P_n𝐔)) = P_n𝐔 on □₀, up to a gauge transformation preserving the data. Let F_n be the feasible set of the layer's local problem, the configurations on □₀ whose averages of the scale p agree with those of 𝐔 on □_{p−1}∖□_p for p ≤ n and on □_n at the scale n, and F_j the feasible set of the scale-j problem at the data of P_n𝐔. A configuration of F_j has the averages of P_n𝐔 at every scale p ≥ j on □_j, because the coarser averages are averages of the scale-j ones (M^p = M^{p−j}∘M^j), and P_n𝐔 ∈ F_n has the averages of 𝐔 there. So F_j ⊂ F_n and P_n𝐔 ∈ F_j. For real 𝐔, P_n𝐔 minimises the action of □₀ over F_n, hence over F_j, and by the uniqueness of the local minimiser at small field (VAR Theorem 1) U_j(□₀, M^·(P_n𝐔)) = P_n𝐔. RG I (3.39) prints the same identity at the newest scale k + 1, citing (97) of [12] (§55.1). At complex 𝐔 the identity is applied to the gauge-invariant functions 𝐄^{(j)}(X, ·), which are analytic in the data on the class, and holds there by analytic continuation from the real configurations. It uses the common cube sequence of RG I p.273 l.40–42.

So by R-data the term at 𝐔 is 𝐄^{(j)}(X, P_n𝐔), a gauge-invariant function of the data M^·(𝐔) on □₀ alone.

*The member at the entries.* Under R-data the term at c(t) is 𝐄^{(j)}(X, P_nc(t)), P_nc(t) = U_n(□₀, M^·(c(t))). The glued configuration Ŵ_z(t) := P_nc(t) on □₀, extended by c(t) outside □₀, agrees with P_nc(t) on X^∼ ∪ supp h_z ⊂ □̃³. RG I Lemma 4 ((3.53), p.280 l.24–32), with 𝐀 = 0 and B′ = 0 and with 𝐔 := c(t), places the pair of P_nc(t) restricted to each near X in U^c_j(X, α₀, α₁), and the functions of (3.53) are analytic in 𝐔 on Lemma 4's space U′^c_{k+1}(□₀, (1 + 2β)α₀, (1 + 2β)α₁). That c(t) lies in this space on the disc is the entries' class, the LF note's *The class at the entries.* (its l.528). At t = 0, P_nc^B = c^B on □₀ up to gauge, by Lemma B of 51.4: c^B is the minimiser of run B's set, and on □₀ the cube's layers satisfy (R) against that set where □₀ satisfies (N). The global minimiser of the data of c(t) is not this composite: on the outer shell □₀ ∖ □₁ the cube data are c(t)'s bond variables (RG I (1.15), REG (1.5)), so the composite equals c(t) there, while a minimiser does not (57.1). At t = 1 the term at ι_Yc^A is the term at the run-B layer composite U^B_n(□₀, D), D = M^·(ι_Yc^A) on □₀. The LF note's l.559 writes the generation composite U^B_{j+1}(□₀, D); under R-data the layer composite takes its place.

### 44.3 The Decomposition

With irr_j(z; 𝐖) := Σ_{X∋z}[𝐄^{(j)}(X, 𝐖) − 𝐄^{(j)}(X, 1)] − β_jA(h_z, 𝐖), the sum over the near domains X of z of the generation j, as in the Cauchy note's irr(Δ) (its l.104 and l.108), R-data and the clause of 62.3 give

$$
\mathrm{ren}_j(z;c(t))=\mathrm{irr}_j\bigl(z;\hat W_z(t)\bigr)=\mathrm{irr}_j\bigl(z;c(t)\bigr)\big|_{\text{R-data}}\,.
\tag{G.257}
$$

By 64.5, |irr_j(z; c(t))| ≤ E₁(α)(L^{j−n})^{4+β′}, the bound of 62.2 and 64.2 taken at c(t) itself, with the inputs of the entry's own class on the disc; the membership of Ŵ_z(t) in 𝒮_z is not used. The other inputs are (5.1c)'s own: the condition (N) on □₀, or 63.3 where □₀ meets the layer n − 1, the top N₀ layers (§71), and the 𝐑 version of (5.1c) at complex configurations. For an 𝐑-term there is no counterterm. Per domain X, (G.257) holds with the per-domain counterterm c_X of §47, which reads P_n𝐔 as well, and §47.4 assembles the per-X pieces.

### 44.4 The Counterterm Under the Clause

Under the clause of 62.3 the counterterm of z at c(t) is β_jA(h_z, P_nc(t)) = β_jA(h_z, Ŵ_z(t)), so the second defect of the LF note is zero, and no mismatch term enters (G.257). The total over z is unchanged by the clause, since the chain of (1.59) ends at the run's configuration, which is the local minimiser of its own cube data where □₀ satisfies (N) (62.3, 66.1).

### 44.5 The Variation (ii) and the r_z Item

On the disc |t| ≤ T := c_ρα_m/σ_c, with σ_c the supremum over the region the term reads, f(t) := ren_j(z; c(t)) is holomorphic: c(t) is holomorphic in t, and the composite and the terms are analytic in 𝐔 on Lemma 4's space (44.2). By (G.257), sup_{|t|≤T}|f| ≤ E₁(α)(L^{j−n})^{4+β′} per point z of the scale j. For T ≥ 2, Cauchy's estimate along the line gives |f(1) − f(0)| ≤ sup_{|s|≤1}|f′(s)| ≤ sup_{|t|≤T}|f|/(T − 1) ≤ 2sup|f|/T, so

$$
\bigl|\mathrm{ren}_j(z;\iota_Yc^A)-\mathrm{ren}_j(z;c^B)\bigr|\le\frac{2\sigma_c}{c_\rho\alpha_m}E_1(\alpha)(L^{j-n})^{4+\beta'}\,.
\tag{G.259}
$$

(G.259) is used for T ≥ 2 only. That is the regime r(Y) ≤ ½ of the LF note's joint line (its l.459), at which its Cauchy estimate in t is made. Summed over the L^{4(n−j)} points of the scale j in a point of the layer n and over the generations j ≤ n,

$$
\sum_{j\le n}\sum_{z}\bigl|\mathrm{ren}_j(z;\iota_Yc^A)-\mathrm{ren}_j(z;c^B)\bigr|\le\frac{2\sigma_cE_1(\alpha)}{c_\rho\alpha_m(1-L^{-\beta'})}
\tag{G.260}
$$

per point of the layer n. This is the product of the age bound and the depth. The decay is in the birth scale of the history, not in the layer. Let n_b be the birth scale, n ≥ n_b the layer of z. By the LF note's l.461 and l.562–563, σ_c ≤ C(ε₀)(a_k/ε)^{ε₀}d̄ with d̄ = C_U(M)(ε/a_{min(j(x),n_b)})^{(1−ε₀)/3}ε₁, and l.563 bounds σ_c/ε_m with the exponent (1 − 25ε₀)/3 of L^{−n_b}, the factor L^{kε₀} with k < 8n_b + j(C) included. (G.260) carries σ_c/α_m, and α_m ≥ ε_m: by CRE (2.28) and p.255, α_{0,m} = g_mC₀(log g_m^{−2})^{q₀} and ε_m = g_mA₀(log g_m^{−2})^{p₀}, so α_m ≥ ε_m for q₀ > p₀ and g small, the provisional reading (R-m′) of the project. With the LF note's conversion of polynomial and polylogarithmic factors into a power of log(k + j(C) + ḡ^{−2}) and "L^{−(1−ε₀)n/3} ≤ θ̃^nL^{−(1−ε₀)n/12} absorbs it" (its l.232 and l.375, where θ̃ ≥ L^{−(1−ε₀)/4}), applied at n_b, (G.260) is ≤ C_hθ̃^{n_b} per point of the layer of a history born at n_b, with C_h depending on ḡ, M, ε₀, and j(C).

*Option (a) of the r_z item.* At t = 1, which lies in the disc for T ≥ 2, the term is read at the run-B layer composite U^B_n(□₀, D) (§44.2), and (G.257) with 64.5 gives |ren^B_j(z; ι_Yc^A)| ≤ E₁(α)(L^{j−n})^{4+β′}. This is the age bound of run B's renormalised terms at the lifted chain that option (a) asks for. Per domain X it is §47.4's form. With (5.1c) for G at c^A, open where (i) is open, the pair (renB(X, ι_Yc^A), renG(X, c^A)) then has the bounds that the device of the Cauchy note's (5.1v) needs at the members of 𝒞 read inside V(Y). The moment defect N_j(c^A) and the coefficient difference (Π^G − β^B)A_ε(h_z, c^A) are inside renG(X, c^A), and the blocking artifact β^Bb_{h_z}(ι_Yc^A) is inside the difference, so none of them is bounded separately.

*The caller under R-data (derived).* The LF note's decomposition of V^B(Y)[c^B] − V^A(Y)[c^A] (its l.440–455) is a telescoping through the intermediate V^B(Y)[ι_Yc^A]: (ii) = V^B(Y)[c^B] − V^B(Y)[ι_Yc^A], followed by the pieces (i), (iii), (iv), (α), (β), and (δ), and r^s_z, which is zero given R-near (§45.2). The telescoping is exact for any definition of run B's terms, provided V^B(Y)[·] is the same function in each occurrence; the endpoint V^B(Y)[c^B] is run B's value by P_nc^B = c^B (44.2). So under R-data the identity holds as written, with every near-domain term of run B read through R-data.
- The joint line f(t) = V^B(Y)[c(t)] reads the near-domain terms at P_nc(t), and it is holomorphic on the disc (above).
- The current part of the joint line, *The current of the line* in the LF note, is absent for these terms. It stays for the far-domain and unrenormalised terms, which keep the pair extension.
- r_z = renB(X, ι_Yc^A) − renG(X, c^A) per X is unchanged as a definition. Option (a) bounds it as a whole for the near domains, and §45.3 bounds its far part. The completions of p.377 l.22–26, single terms at U_k, are read the same way.
- The pieces that read run B's terms at lifted configurations that are not minimisers: (iv) and (α) at the composites and the representation configurations, treated under R-data in §70, and (δ) at the decoupled configurations, treated in §72.

### 44.6 Status

Derived here, not reviewed in this form: 44.2–44.5. Quoted and checked (§55.1): Bałaban's extension of the near-domain terms at the newest scale, RG I p.275 l.2–13, (3.24), and (3.39); the specialisation 𝐀 = 0, CRE p.280 l.18–19; the bounds in the layer scale, CRE p.280 l.14–20. Construction choices: the layer form U_n(□₀, ·) of (G.256), which CRE does not print ("the difference is seen in bounds only"), and the clause of 62.3.

Inputs that these rest on:
- 64.5's bound at c(t), with (N), or 63.3 where □₀ meets the layer n − 1, the top N₀ layers of §71, and the 𝐑 version at complex configurations;
- Lemma B of 51.4 for P_nc^B = c^B, and the Cauchy note's l.124 statement M^p = M^{p−j}∘M^j (derived there, unreviewed);
- the entries' class on the disc (the LF note's l.528), with the condition c_ρα_m < α₃ of its bullet;
- the bound σ_c on the disc. By the LF note's definition at *The joint line.*, σ_c(x) bounds a_{j(x)}|𝐒_c(x)| + a_{j(x)}²|∇_{c^B}𝐒_c(x)|. It is derived at the real members and continued to the complex points by 68.4–68.5;
- (5.1c) for G at c^A, for the r_z item, open where (i) is open.

What this does not give. The age bounds alone still sum to O(E₁) per point of the layer; the product of age and depth comes only from the Cauchy estimate in t, as the Cauchy note designed. The unrenormalised terms and the far-domain terms are unchanged.

### 44.7 The Data of the Entries and the Coefficients

*The data of the entries (derived).* The data of c(t) at the scale p ≤ n are block averages of e^{it(ε/L)𝐒_c}c^B over a block of side a_p ≤ a_n. In the layer scale this is M^p(c(t)) = e^{iB′_p(t)}M^p(c^B), with |B′_p(t)| ≤ K_M|t|a_p sup|𝐒_c|, by a Baker–Campbell–Hausdorff expansion of the averaged transports along paths of length of order a_p, of size a_p|𝐒_c|(1 + O(α)). Moving each factor of the twist along a path to the start of the path conjugates it by a partial transport of the real configuration c^B, which leaves its norm unchanged, and the averaging is Lipschitz in the transports of its paths, with a constant of the averaging only. So |B′_p(t)| ≤ K_M|t|σ_c wherever a_p ≤ a_{j(x)} at the points read, that is, where □₀ meets no layer finer than n at the points read at the scale n. Where □₀ meets the layer n − 1 (63.3), a_p ≤ La_{j(x)}, and the bound holds with LK_M in place of K_M. The gradient of 𝐒_c does not enter: RG I Lemma 4 takes the shift B′ in the sup norm ((3.53)).

*The coefficients (from the Bałaban sidecar's one-loop results).* Bałaban defines β_j as the coefficient of the quadratic moment of the vacuum polarisation tensor ((I.5.42), RG I p.297: "This is the fundamental equality defining the β-function"). CRE (2.6) bounds the coupling ratios g_n/g_m, which encode the sums of the β_j along the flow, and no uniform bound on a single β_j is printed. The Bałaban sidecar proves one for simple G (`BETA_FUNCTION_WILSON_LOOPS.md`):
- Theorem 8.1, the window theorem: |Σ_{j=m+1}^{n}b_j − (11/24π²)κ(n − m)ln L| ≤ 2C for all 0 ≤ m ≤ n, where b_j is the zero-coupling coefficient.
- (P2) of Proposition 2.4, |β_{k+1}(h) − b_{k+1}| ≤ C_ΛC₃ε₁, uniformly in k and the history h ∈ ℋ_γ.

Together they give the window hypothesis (W) of BETA_FUNCTION_WILSON_LOOPS.md §2: b(n − m) − C ≤ Σ_{j=m}^{n−1}β_{j+1} ≤ b′(n − m) + C, with 0 < b ≤ b′. The window n = m + 1 gives b − C ≤ β_{m+1} ≤ b′ + C, hence |β_{m+1}| ≤ max(b′ + C, C − b) ≤ b′ + C =: β̄, uniformly over the histories of ℋ_γ. This is the constant β̄ of the Cauchy note's constant list (its l.952). By Remark 2.3, b = 2c ln L − δ and b′ = 2c ln L + δ, with δ = c ln L the (P2) constant. For a compact G with several simple or abelian factors the uniform bound is not supplied: BETA_FUNCTION_WILSON_LOOPS.md §10 leaves the semisimple case open.

Derived here, not reviewed: the data bound with K_M. The bound on β_j is Theorem 8.1 and (P2) of BETA_FUNCTION_WILSON_LOOPS.md, used as stated there, for simple G.

## 45. The Counterterm of a Point and the Brackets of (1.60)

This section treats the LF note's open item r^s_z and the far-domain part of its r_z item. The counterterm of a point z has its support inside □^{∼2}. By R-near of §45.1 (a construction choice, §55.2), which treats it with the near-domain terms of z, it is therefore never a term of the brackets of (1.60), and r^s_z = 0. The far-domain part of r_z is the lift change of the far domains alone, and it is superexponentially small in the layer. Notation is §44's: z a point of the layer n, j ≤ n the generation, □ ∈ π_n the cube of the layer containing z, and ∼ in the layer scale, by M-cubes of the layer's lattice (LFR II p.372). The scale-j spacing a_j = εL^j is at most a_n.

### 45.1 Where the Counterterm of a Point Sits

*The source (read).*
- CRE (2.25)–(2.27), p.259: 𝐄_k(U_k) = Σ_j[𝐄^{(j)}(Λ_j, U_k) − 𝐄^{(j)}(Λ_j, 1) − β_j(g_{j−1})A(φ_j, U_k)], with 𝐄^{(j)}(Λ_j, U_k) = Σ_z𝐄^{(j)}(Λ_j, U_k, z) and 𝐄^{(j)}(Λ_j, U_k, z) = Σ_{X∋z}𝐄^{(j)}(X, U_k, z). The counterterm is a separate weighted Wilson action, not a part of any 𝐄^{(j)}(X, ·, z). The sum (2.26) runs over z ∈ Λ_j^0, the set left after removing one layer of the MR_j-cubes from Λ_j (p.259 l.30–31).
- CRE (3.65), p.283 l.10–15: A(φ_j, U_k) = Σ_{z∈T^{(j)}}A(h_zφ_j, U_k), "where h_z is defined as in (3.40), but on the lattice T_{L^{−j}}, and with h(t) = max{1 − |t|, 0}"; "For z ∈ Λ_j^0 we have h_zφ_j = h_z". (3.40) is on p.275 l.2–7. The per-point combination is (3.67), p.283 l.28: 𝐄^{(j)}(Λ_j, U_k, z) − 𝐄^{(j)}(Λ_j, 1, z) − β_jA(h_z, U_k) = O((L^jL^{−n})^{5−β}) for z ∈ Λ_j^0 ∩ (Ω_n∖Ω_{n+1}).
- CRE p.279, last paragraph, to p.280, (3.48) and the sentence after it: for z ∈ Λ_j^0 ∩ (Ω_n∖Ω_{n+1}) and □ ∈ π_n containing z, the domains split by (I.3.5) into X ⊂ □^{∼2} and X ⊄ □^{∼2}. For the second kind |𝐄^{(j)}(X, z)| ≤ E₀exp(−κL^{n−j})exp(−½κd_j(X)), and "In the proof of Theorem 2 we simply estimate all these terms using the above bound", the sum over X being O(1)exp(−κL^{n−j}) ≤ O(1)(L^{j−n})^5.
- CRE p.281, the paragraph after (3.56): the identity (3.56) holds for X ⊂ □^{∼2}; it is summed over these X and extended "to all domains X ∈ 𝐃_j for the space L^{−j}Z^d, X containing the point z", the infinite lattice; "The difference between the two sums contributes to the irrelevant terms only, by the bounds (3.48)". The extended coefficient is Π^{(j)} of (3.57), and β_j matches it by (3.61)–(3.64), pp.282–283.
- LFR II p.372: (1.59) for the terms 𝐄^{(j)}(X, U″_k, z) with X ⊂ □^{∼2}, and (1.60) "for the terms with localization domains X not contained in □^{∼2}, and for the boundary terms in the second group". The re-summation "is controlled by the renormalization procedure for 𝐄-terms".

*The support of the counterterm of z (derived).* By (3.65) and (3.40), h_z(x) = Π_μmax(1 − |x_μ − z_μ|, 0) with distances in the units a_j, so supp h_z lies within the sup-distance a_j of z, and the weighted plaquettes add one fine spacing. □^{∼2} contains every point within two M-cubes of the layer, 2Ma_n, of □. Since z ∈ □ and a_j ≤ a_n, supp h_z ⊂ □^∼ ⊂ □^{∼2}. The plane-pair actions of N_j carry the same weights h_z (the Cauchy note's *The plane-resolved moment.*), so N_j has the same support. So A(h_z, ·) and N_j are not in the class of terms to which LFR II p.372 l.21 assigns (1.60), the 𝐄- and 𝐑-terms with X ⊄ □^{∼2} and the boundary terms of the second group.

*The split (derived from the quoted proof).* For a configuration U at which the terms are defined, with the domains classified against the □ of z,

$$
\mathrm{ren}_j(z;U)=\mathrm{ren}^{\mathrm{near}}_j(z;U)+\mathrm{far}_j(z;U),
\tag{G.261}
$$

ren^near_j(z; U) := Σ_{X∋z, X⊂Λ_j, X⊂□^{∼2}}[𝐄^{(j)}(X, U, z) − 𝐄^{(j)}(X, 1, z)] − β_jA(h_z, U),

far_j(z; U) := Σ_{X∋z, X⊂Λ_j, X⊄□^{∼2}}[𝐄^{(j)}(X, U, z) − 𝐄^{(j)}(X, 1, z)].

By (3.48), |far_j(z; U)| ≤ 2C₄₈E₀e^{−κL^{n−j}}, with C₄₈ := sup_zΣ_{X∋z}e^{−½κd_j(X)}, on the analyticity domain of the terms. So ren^near_j has the age bound of ren_j up to 2C₄₈E₀e^{−κL^{n−j}} ≤ C(L^{j−n})^5; this is CRE's accounting for the bound of Theorem 2, and p.280 l.9–10 continues "For the complete analysis we apply the formulas (3.3), (3.6)–(3.13) [I]". The same split holds for G, with Π^G_{22,11}A_ε(h_z, ·) + N_j as its counterterm, and for run B, with β^B_{j+1}A_{ε/L}(h_z, ·). For G it uses G's far terms, which run B's (3.48) bounds at the pair lift. That is the lift condition at the far domains, already an input of (5.1c) for G (the Cauchy note's *What it gives.*). G's terms are indexed by the same domains X as run A's in (i), so the classification X ⊂ □^{∼2} is the same in the three families, with □ the physical cube of the layer of z.

*Where the counterterm goes in the R-operation (R-near, a construction choice, §55.2).* LFR II p.372 names the 𝐄-, 𝐑- and boundary terms as the terms that (1.59) and (1.60) treat, and says that the re-summation is controlled by the renormalisation of the 𝐄-terms; p.376 l.40–41 says that the re-summation "includes renormalization in the form described in the proof of Theorem 2 in Sect. 2 [III]", with [III] = CRE. Nowhere in pp.371–377 does LFR II say which identity is applied to −β_jA(φ_j, ·) or to its pieces A(h_z, ·), and CRE p.283 l.16–17 says only "Analyzing A(h_z, U_k) in the same way as above". The print is silent on the point. R-near is adopted as the construction: the counterterm of z enters with the near-domain terms of z, through (1.59), identically in both runs. It is consistent with LFR II p.372 l.29–31 and p.376 l.39–41, and it is the natural choice, since supp h_z ⊂ □^{∼2}; the print does not determine it. The support property is necessary for the representation of (1.59) through U_j(𝐁_j(□₀), ·) for A(h_z, ·), not sufficient: the representation also needs the configuration to be of U_j-type on □₀, and at the configurations that are not, the difference is the counterterm defect of the LF note's l.13, which the counterterm clause of 62.3 makes zero (the counterterm of z reads the configuration that the near-domain terms of z read). The renormalisation procedure that p.372 l.29–30 names, with the cancellation of CRE p.283 l.22–23, needs the counterterm aligned with the near-domain terms it renormalises. A decoupling of A(h_z, ·) with σ₀ disjoint from its own support only (the "or X" of p.373 l.12–13, stated there for the first-part terms) would not align it. A decoupling with σ₀ disjoint from □₀, which p.372 l.16 takes and l.27 repeats for the far terms, coincides with R-near at the configurations of U_j-type on □₀. Within a fixed Y₀ the cancellation of CRE (3.66) against (3.61) needs the counterterm expanded with the near-domain terms of z, so the identity applied to it is (1.59). If A(h_z, ·) were expanded with the identity of the form (1.60), A(h_z, e^{iη𝐇″}U^0_k) = A(h_z, U^0_k) + [A(h_z, e^{iη𝐇″}U^0_k) − A(h_z, U^0_k)], its bracket at the decoupled configuration W would carry (Π^G_{22,11} − β^B_{j+1})A_ε(h_z, W) + N_j(W) + β^B_{j+1}b_{h_z}(ι_XW), the old r^s_z, a two-run remainder with no age partner. So R-near excludes the misaligned treatment; it is a construction, not a quotation. §45.2 uses R-near.

### 45.2 r^s_z Vanishes

The brackets of (1.60) hold the far-domain terms of each run and the boundary terms of the second group, as differences 𝐄^{(j)}(X, e^{iη𝐇(s)}U, z) − 𝐄^{(j)}(X, U, z), in which the vacuum value cancels. Under R-near (§45.1) the counterterm of z is not among them, so no renormalisation enters a bracket of (1.60) in either run. At run A's decoupled configuration W := e^{iη𝐇^A(s)}c^A, G(X, W, z) = 𝐓^B(X, ι_XW, z) per X, with the pair-lift current, by the definition of G. So for each X ⊄ □^{∼2} the LF note's decomposition of a bracket of (1.60) reads

$$
\mathbf T^B\bigl(X,e^{i\eta\mathbf H^B(s)}\iota_Yc^A\bigr)-\mathbf T^A\bigl(X,e^{i\eta\mathbf H^A(s)}c^A\bigr)=(\mathrm i)\text{ at }W+(\mathrm{iii})+(\delta),
\tag{G.262}
$$

and r^s_z = 0. The three parts of the former r^s_z, (Π^G_{22,11} − β^B_{j+1})A_ε(h_z, ·), N_j, and β^B_{j+1}b_{h_z}, belong to the near parts of z. In V(Y) these enter through the brackets of (1.59), where their run difference is inside the variation group (iv) at the composites. They also enter through the first terms of (1.59) at the members of 𝒞, which is r_z^near of §45.3, treated in §44. The presupposition of the LF note's r^s_z bullet, ι_X at the complex W with Mι_XW = W, is still needed, but only for (i) at W, where it is already listed.

### 45.3 The Far Part of r_z

At a member c of 𝒞 read inside V(Y), (G.261) for run B's term at the pair lift through ι_Y and for G at c^A gives

$$
r_z=r_z^{\mathrm{near}}+\sum_{X\ni z,\ X\not\subset\square^{\sim2}}\ell_X(c^A),
\tag{G.263}
$$

where r_z^near := renB^near(ι_Yc^A) − renG^near(c^A) carries the whole moment defect, N_j, the blocking artifact, and the lift changes of the near domains. Since ι_Y1 = ι_X1 = 1 and J(1) = 0, the vacuum values cancel, and the far part is the lift change of the far domains alone. r_z^near is bounded in §44 and §§62–64: under R-data and the counterterm clause of 62.3 the near terms and the counterterm of z read the composite, whose age bound is (5.1c) at the composite (62.2), so the age bound at ι_Yc^A itself, which the LF note's l.404–405 lacks, is not needed. §44.1 keeps the pair extension for the far-domain terms.

*Two bounds per far domain (derived given the lift condition, the tails, and the current bound).*
- By (3.48) for run B's term at each of the two lifted pairs, |ℓ_X(c^A)| ≤ 2E₀e^{−κL^{n−j}}e^{−½κd_j(X)}. This needs both pairs in run B's domain of the term, the lift condition for ι_Y and for ι_X. It is derived at the real members of 𝒞 (the LF note's *The lift condition of (i).*, unreviewed) and open at complex points.
- The two lifts differ only by their tails. By the Cauchy note's §9.8 (l.529–534) ι_XU = e^{i(ε/L)T_X}ιU and ι_YU = e^{i(ε/L)T_Y}ιU on X^∼, with the same one-step minimiser ιU, and T_X and T_Y with their gradients are each at most C_tε₁e^{−δ₀M₁L^j/2} in the units of a_j (the LF note's l.563, with c = ½; for ι_Y the rate is L^k ≥ L^j). These tails are derived at real configurations only. Let τ_X := sup(|T_Y − T_X| + a_j|∇(T_Y − T_X)|), the sup over X and the bonds within 2L fine spacings of X, which the current slot reads (the Cauchy note's l.534); the tail bounds hold there, ≤ 2C_tε₁e^{−δ₀M₁L^j/2}, and let the joint line be W(s) := e^{i(ε/L)(T_X + s(T_Y − T_X))}ιU, s ∈ ℂ, with the current slot carried along, F(s) := 𝐓^B(X, (W(s), Q₁^{pl}(W(s))*J(U)), z). Then F(0) and F(1) are the two terms of ℓ_X(U), so no current difference has to be bounded separately. W(s) is holomorphic in s, and Q₁^{pl}(W)* = dM(W)* is holomorphic in W, so F is holomorphic where the pair lies in run B's domain. The line moves each plaquette by at most 4|s|τ_X(1 + O(α)), four links per plaquette, and the cube-gauge field, its gradient, and the data of (iv) through (1.17) by at most |s|τ_X, in the units of a_j. Take the quantitative lift condition of the Cauchy note's *The configuration part.*: the base pair at s = 0 has room ¼r_{0,j} in run B's domain. Then for |s| ≤ T := r_{0,j}/(16τ_X(1 + O(α))) the configurations move by at most ¼r_{0,j} from the base pair, plaquettes, cube-gauge field, gradient, and data alike, so they stay inside its room, which is measured in these quantities in the units of a_j; they are therefore configurations of the class in the sense of the Cauchy note's l.112, and there |Q₁^{pl}(W(s))*J(U)| ≤ C_{Q*}|J(U)| < r_{0,j} by the Cauchy note's l.112, given |J(U)| < r_{0,j}/C_{Q*}. The Cauchy note's *The current.* (l.192) gives that bound at run A's single-scale minimiser U^A_k only. At a general member c^A of 𝒞 it is the current item of the LF note's *The lift condition of (i).* (its l.474: VAR (9)–(10) bound the current by O(1)B₃Mε₁a_m^{−3}, and the pair-lift current is at most C_{Q*} times this), derived at real members only; it is an input. So the disc lies in the domain, given that input. For T ≥ 2 Cauchy's estimate gives |F(1) − F(0)| ≤ 2sup|F|/T ≤ 32(τ_X/r_{0,j})E₀e^{−κd_j(X)}. For T < 2 both endpoints are in the domain by the lift condition for ι_X and ι_Y, and |F(1) − F(0)| ≤ 2E₀e^{−κd_j(X)} < 64(τ_X/r_{0,j})E₀e^{−κd_j(X)}. Hence |ℓ_X(c^A)| ≤ C_ℓE₀(ε₁/r_{0,j})e^{−δ₀M₁L^j/2}e^{−κd_j(X)}, with C_ℓ := 128C_t(1 + O(α)). This is the per-domain form of the lift-change size in the LF note's r_z item. It needs only the bound C_{Q*} of Q₁^{pl}(W)* on the class, not a Lipschitz bound of W ↦ Q₁^{pl}(W)*.

The first bound is small at the fine generations, n − j large, and the second at the coarse ones, j large.

*The sum (derived).* Per scale-j point z the far part is at most C₄₈E₀min(2e^{−κL^{n−j}}, C_ℓ(ε₁/r_{0,j})e^{−δ₀M₁L^j/2}). A point of the layer n contains L^{4(n−j)} scale-j points. Split the generations at n/2:
- for j ≤ n/2, m := n − j ≥ n/2 and L^{4m}e^{−κL^m} ≤ C_κe^{−κL^{n/2}/2}, with C_κ := sup_{m≥0}L^{4m}e^{−κL^m/2};
- for j > n/2, L^{4(n−j)} ≤ L^{2n}, e^{−δ₀M₁L^j/2} ≤ e^{−δ₀M₁L^{n/2}/2}, and ε₁/r_{0,j} ≤ C(M)2^{p₀}(1 + β₀)R_k(k − j + 1)^{1/2}, by ε₁ = C(M)R_kε_k, r_{0,j} ≥ ε_j, and CRE (2.6), as at the LF note's l.563. Where the ε₁ of the LF note's §1 is the larger, ε₁/ε_k is at most C(1 + β₀)(k_s − k + 1)^{1/2}(1 + A₁/A₀) in place of C(M)R_k, polynomial in n since k_s − k < 7n (the LF note's l.632).

Per point of the layer n, therefore,

$$
\sum_{j\le n}\sum_{z}\Bigl|\sum_{X\ni z,\ X\not\subset\square^{\sim2}}\ell_X(c^A)\Bigr|\le C_{48}E_0(n+1)\Bigl[2C_\kappa e^{-\kappa L^{n/2}/2}+C_\ell C(M)2^{p_0}(1+\beta_0)R_k(k+1)^{1/2}L^{2n}e^{-\delta_0M_1L^{n/2}/2}\Bigr].
\tag{G.264}
$$

In a history with k < 8n + j(C), the regime of (iv) and of the LF note's l.563, R_k(k + 1)^{1/2} is at most a polynomial in n and in log(ḡ^{−2} + j(C)) times a constant depending on j(C). The alternative factor of the LF note's §1 case is also polynomial in n. A superexponential factor e^{−cL^{n/2}} absorbs these, so (G.264) is ≤ C_hθ̃^n per point of the layer, for every θ̃ ∈ (0, 1), with C_h depending on θ̃, κ, δ₀M₁, L, M, p₀, β₀, r, A₀, A₁, E₀, C₄₈, C_ℓ, j(C), and ḡ, the last through log(ḡ^{−2} + j(C)).

### 45.4 Status

Reviewed twice, correct at the stated scope given R-near: the source quotations, the support property, the split (G.261) and its far bound, r^s_z = 0 and (G.262), (G.263), the two far bounds with C_ℓ = 128C_t(1 + O(α)), and (G.264). The repairs after the reviews are not re-reviewed.

A construction choice (§55.2): R-near of §45.1, that the R-operation treats the counterterm of z with the near-domain terms of z. LFR II p.376 l.40–41 states that the re-summation of the 𝐄- and 𝐑-terms into V(Y) "includes renormalization in the form described in the proof of Theorem 2 in Sect. 2 [III]", with [III] = CRE (LFR II p.392 l.18), and CRE p.283 l.16–17 analyses A(h_z, U_k) "in the same way as above". Neither says which identity is applied to the counterterm. Within a fixed Y₀ the cancellation of (3.66) against (3.61) needs the counterterm expanded with the near-domain terms of z, that is, through (1.59). R-near is a construction choice consistent with p.372 l.29–31 and p.376 l.39–41, not determined by the print, and it is made identically in both runs.

Inputs that these rest on:
- the lift condition for ι_X and ι_Y at the far domains, in its quantitative form (room ¼r_{0,j} for the base pair), derived at the real members of 𝒞 and open at complex points, as before;
- the per-domain tail bound of the two lifts, the Cauchy note's §9.8 with the LF note's *The Lift ι_Y.*, derived at real configurations only;
- the bound C_{Q*} of Q₁^{pl}(W)* on the class (the Cauchy note's l.112);
- the current bound |J(c^A)| < r_{0,j}/C_{Q*} at the members of 𝒞, the current item of the LF note's *The lift condition of (i).* (its l.474), derived at real members only;
- for the age bound of renG^near, the far bound of G, which is the same lift condition;
- the counterterm defect of the LF note's l.13, which under R-near applies to A(h_z, ·) in every bracket of (1.59), at the configurations that are not of U_j-type on □₀; the counterterm clause of 62.3 makes it zero, since the counterterm of z reads the configuration that the near-domain terms of z read.

Open: the counterterm pieces at the points z ∈ T^{(j)}∖Λ_j^0 with h_zφ_j ≠ 0. By (3.65) the counterterm runs over all of T^{(j)}, while (2.26) and (3.67) cover z ∈ Λ_j^0 only, so these pieces −β_jA(h_zφ_j, ·) have no near-domain 𝐄-terms of their own. They lie in the layer of the generation j only (derived, resting on §46.2). For j < n a point of the layer n lies in Ω_n ⊂ Ω_{j+1}, and Ω_{j+1} ∩ (Z′_j)^{∼8} = ∅ with Λ_j^c = Z_j ⊂ Z′_j (§46.2), so every scale-j point whose tent meets the layer n is at distance at least 8LMR_{j+1} − a_j from Λ_j^c, more than the width of the layer of MR_j-cubes that Λ_j^0 removes. At j = n these pieces lie within that layer of Λ_n, next to Z_n = Λ_n^c, and their run difference, the coefficient difference, the blocking artifact, and the lift change of −β_nA(h_zφ_n, ·), is not placed.

What this changes in the LF note's open items (recorded here, not edited):
- The item r^s_z (its l.15 and l.407–409) is closed given R-near: r^s_z = 0. In its decomposition of the brackets of (1.60) (l.444–445 and l.454), "(i), then r^s_z" is (i) alone.
- The item r_z (its l.14 and l.404–406) reduces to r_z^near. Its moment defect, N_j, and blocking artifact are all in r_z^near, which §44 and §§62–64 bound at the composite. The far part, which carried lift changes with no age factor, is (G.264).
- The assignment of the counterterm between the near and far domains of z is settled, given R-near. Its assignment among the domains Y is settled in the brackets of (1.59); for the first-part terms §47 proposes per-domain counterterms, whose term properties on X̂ are open (§47.5).
  - In the brackets of (1.59) (derived, given R-near). The localisation set σ₀ consists of the cubes disjoint from □₀ and Λ^∼ (LFR II p.372). It is the same for every near-domain term of z and for the counterterm of z, since all of them have the same □. The decoupling expansion (6.9)–(6.10) [I], which is RG II (1.9)–(1.10) (p.4), is an interpolation formula in the parameters s(Δ), Δ ∈ σ₀, linear in the function expanded. So the Y₀-piece of the renormalised near combination of z is the renormalised combination of the Y₀-pieces, and the counterterm is not split differently from the terms it renormalises.
  - For the first-part terms, those whose domains meet Z, linearity alone does not settle it. After (1.59) or (1.60), LFR II p.373 represents U^0_k by (1.61) on Y₁, "the smallest localization domain Y₁ ∈ 𝐃_k containing X, and containing these components of Z, which intersect X", and then expands again with σ̃₀ and the domains Y′₂. Y₁ depends on X, so linearity no longer aligns the counterterm's pieces with those of the near-domain terms of z. §47 splits the counterterm of z into per-domain counterterms c_X and assigns each with its X.

What this does not give. (i), (iii), and (δ) at the decoupled configurations, and the lift condition at complex W, are unchanged. The near part r_z^near rests on (5.1c) with its open inputs, as in §44.6.

## 46. The Width of the Middle Layers of 𝐁″_k (Point (11) of (LF-A))

The LF note's point (11) asks for a lower bound on the width of the layers Ω″_j ∖ Ω″_{j+1}, h + 1 ≤ j ≤ k − N₀, of 𝐁″_k, in the units of the scale j. The counts of its §9 need every crossed layer to be at least LM₁ wide (*The joins.*). The result is that every such layer is at least LMR_{j+1} wide, and at least 3LMR_{j+1} wide for j ≤ k − N₀ − 1. Both exceed LM₁, since R_{j+1} ≥ 1. The bound comes from the construction of Ω_{j+1} at the T-operation of the step j + 1.

### 46.1 The Source (Read)

- LFR I (1.10)–(1.12), p.179: Z″_j = (Ω_j^{∼5})^c ∩ Z for h + 1 ≤ j ≤ k − N₀, Z″_{k−N₀+1} = (Ω_{k−N₀+1}^{∼7})^c ∩ Z, and Ω″_j = (Z″_j^c ∩ Z) ∪ (Ω_j ∩ Z^c) for h + 1 ≤ j ≤ k. "Let us recall that the domains Ω_j^{∼n} are unions of L^{−(k−j)}MR_j-cubes of the lattice T_η" (p.179 l.7–8), the cubes of the scale j. (1.10) itself writes Z″_k = (Z′_{k−N₀})^{∼3} = (Ω_{k−N₀+1}^{∼5})^c ∩ Z and Z″_{k−N₀+1} = (Z′_{k−N₀})^{∼} = (Ω_{k−N₀+1}^{∼7})^c ∩ Z (p.179 l.13–14), that is Ω_{k−N₀+1}^c ∩ Z = (Z′_{k−N₀})^{∼8} ∩ Z, the formula (3.5) of the T-operation inside Z.
- CRE p.254 l.44–45: the expansion is "parametrized by sequences of domains in T, of the type described already several times in previous papers, e.g. in (1.3)–(1.6) [14], or (38), (39) [16]", with [14] REG and [16] UV3 (CRE p.285). REG (1.4), p.77: "(L^jη)^{−1}dist(Ω_j^c, Ω_{j+1}) > RM₁", with "R … a sufficiently large positive integer (a power of L)". UV3 (39), p.266: "(L^jη)^{−1}dist(Ω_j^c, Ω_{j+1}) > R(g_j)M₁".
- LFR I p.179 l.19–24: the top N₀ sets are completed "in such a way that the complements of these sets form an admissible sequence of domains based on partitions into M-cubes in the corresponding scales. Thus … Z″_k^c, Z″_{k−1} are separated by one layer of M-cubes. Similarly, … Z″_{k−1}^c, Z″_{k−2} are separated by one layer of L^{−1}M-cubes, and so on." LFR I p.179 l.40: "The sequence {Ω″_j} is an admissible sequence".
- CRE p.264, last paragraph: at the step from j to j + 1 (written there from k to k + 1), "The term has a large field region Z_j = Λ_j^c, and we denote by Z_j′ the union of all LMR_{j+1}-cubes intersecting the region Z_j". These cubes form the partition of the scale j + 1 into MR_{j+1}-cubes, "compatible with all the previous partitions".
- CRE p.265: B^{j+1}(P^1_{j+1}) = (P′^{∼}_{j+1})^c ∩ (Z′^{∼5}_j)^c, and (3.5), Ω_{j+1} = (Q′^{∼2}_{j+1} ∪ (B^{j+1}(P^1_{j+1})^c)^{∼3})^c. The ∼ there adds layers of the same LMR_{j+1}-cubes.
- CRE (2.1), p.254: Ω_j ⊃ Λ_j ⊃ Ω_{j+1}.

### 46.2 The Separation of Ω_{j+1} From Ω_j^c (Derived)

By (2.1), Ω_j^c ⊂ Λ_j^c = Z_j ⊂ Z′_j. By the definition of B^{j+1}(P^1_{j+1}), its complement contains (Z′_j)^{∼5}, so by (3.5) Ω_{j+1}^c contains ((Z′_j)^{∼5})^{∼3} = (Z′_j)^{∼8}. So Ω_{j+1} ∩ (Z′_j)^{∼8} = ∅.

Every ∼ here adds one layer of the cubes of the scale j + 1, of side LMR_{j+1} in the units of the scale j. Ω_{j+1}^{∼n} in LFR I is formed with the same cubes, since they are the MR_{j+1}-cubes of the scale j + 1. Adding n layers to a set disjoint from (Z′_j)^{∼8} gives a set disjoint from (Z′_j)^{∼(8−n)}, for n ≤ 8. So Ω_{j+1}^{∼5} ∩ (Z′_j)^{∼3} = ∅ and Ω_{j+1}^{∼7} ∩ (Z′_j)^{∼} = ∅. A point outside (Z′_j)^{∼m} is separated from Z′_j by at least m full layers of these cubes, so it is at distance at least mLMR_{j+1} from Z′_j.

### 46.3 The Width (Derived)

Fix h + 1 ≤ j ≤ k − N₀. By (1.11)–(1.12),

(Ω″_j)^c = (Z ∩ (Ω_j^{∼5})^c) ∪ (Z^c ∩ Ω_j^c) ⊂ Ω_j^c ⊂ Z′_j.

The top N₀ layers, j > k − N₀, are the M-cube layers of LFR I p.179 and are treated in the LF note. On the other side,

Ω″_{j+1} ⊂ Ω_{j+1}^{∼5} ∪ Ω_{j+1} = Ω_{j+1}^{∼5} for j + 1 ≤ k − N₀, and Ω″_{k−N₀+1} ⊂ Ω_{k−N₀+1}^{∼7}.

Hence, by §46.2, in the units of the scale j:

$$
\operatorname{dist}\bigl(\Omega''_{j+1},(\Omega''_j)^c\bigr)\ge
\begin{cases}3LMR_{j+1}, & h+1\le j\le k-N_0-1,\\ LMR_{j+1}, & j=k-N_0.\end{cases}
\tag{G.265}
$$

The two inclusions hold on the whole lattice. The separation of §46.2 applies to the Ω_j and Ω_{j+1} of the step-k sequence where they are those that entered and left the T-operation of the step j + 1, which (1.10) states inside Z at j = k − N₀ and the next paragraph extends inside Z. So (G.265) is derived inside Z, with M > M₁ (CRE p.245 l.35–37, M₁ < M₂ < M) and R_{j+1} ≥ 1 (CRE (2.5), for g small): every middle layer inside Z is at least LMR_{j+1} > LM₁ wide.

*Inside Z.* Inside Z the step-k domains Ω_{j+1}, h ≤ j ≤ k − 1, are those produced by the T-operations: LFR I p.177, condition (ii), "in the preceding N renormalization steps no new large field regions were created inside this component", with "for such a component all the regions connected with the last N steps are rectangular parallelepipeds". An earlier R-operation that set Λ_j = Ω_j (CRE p.255 l.2–3) still leaves Ω_j^c ⊂ Z_j, so 46.2 holds at the T-operation of the step j + 1 whatever happened before it. That no later R-operation replaced these domains inside Z is the reading of (ii) that (1.10) makes explicit at j = k − N₀; for the other j it is a reading, and the width that the callers use does not depend on it (next paragraph).

*On Z^c and across ∂Z.* There Ω″_j = Ω_j and Ω″_{j+1} = Ω_{j+1} on Z^c, and these domains may come from earlier R-operations on other components, so §46.2 does not apply to them directly. The width there is Bałaban's admissibility. By CRE p.254 l.44–45 the sequences of the expansion are of the type of REG (1.3)–(1.6) and UV3 (38)–(39), and both definitions contain the separation (L^jη)^{−1}dist(Ω_j^c, Ω_{j+1}) > RM₁, R a power of L at least L (REG p.77; in UV3 R(g_j) = R₁r(g_j), large for g small). LFR I p.179 l.40 states that {Ω″_j} is admissible. So, on the whole lattice, dist(Ω″_{j+1}, (Ω″_j)^c) > RM₁ ≥ LM₁ in the units of the scale j. This is Bałaban's stated result (p.179 l.40) with the definition he names; it is used as such, and it is the load-bearing input outside Z.

### 46.4 Status

Derived here, not reviewed: 46.2, and (G.265) inside Z where the step-k domains are the T-operation's products (stated by (1.10) at j = k − N₀).

Used as Bałaban's stated result: the admissibility of every sequence of the expansion, with the separation that its definition contains. The sources are the following.
- CRE (2.18) and the sentence after it (p.257 l.49): the density at the step k is a sum "over the admissible sequences of domains". LFR I p.179 l.40: "The sequence {Ω″_j} is an admissible sequence". So every sequence that enters a step is admissible, whatever R-operations acted before.
- The definition: CRE p.254 l.44–45 names REG (1.3)–(1.6) and UV3 (38)–(39) as the type of the sequences, and both contain (L^jη)^{−1}dist(Ω_j^c, Ω_{j+1}) > RM₁, R a power of L. This gives every layer more than RM₁ ≥ LM₁ in its own units, which is the width that (J-W) and the counts of the LF note's §9 need.
- The form for sequences built on a partition: LFR I p.179 l.19–24 completes the top N₀ sets so "that the complements of these sets form an admissible sequence of domains based on partitions into M-cubes in the corresponding scales. Thus … Z″_k^c, Z″_{k−1} are separated by one layer of M-cubes". Bałaban derives the one-layer separation by the cubes of the partition from admissibility. For the sequences of CRE and LFR I the partition of the scale j + 1 is into MR_{j+1}-cubes (CRE p.264) or, at the top layers, M-cubes, so Ω_{j+1} and Ω_j^c are separated by at least one layer of cubes of side at least M in the units of the scale j + 1. This is the form that 71.3 and §§63–68 use.
- At a T-operation 46.2 gives eight layers of the cubes of the scale j + 1, with no condition on the history; CRE p.256 l.21–24 states a separation 2MR_j for the domains "determined by the j-th renormalization transformation, but not by the R-operation", and is not used for the R-operation's domains.

The weakest step is the passage from Bałaban's definition-level separation RM₁ to the partition form: it rests on the "Thus" of LFR I p.179 l.21, which Bałaban states for the M-cube sequences of the top layers. (G.265) inside Z, away from j = k − N₀, rests in addition on the reading of LFR I p.177 (ii) in *Inside Z.*; the callers do not need it.

What this changes in the LF note (recorded here, not edited): point (11) and the open width in *The join.* and *At the joins W = LM₁.* (its l.193–200) hold by Bałaban's stated admissibility (LFR I p.179 l.40) with the separation of its definition.

## 47. Per-Domain Counterterms and the Assignment Among the Domains Y

§45.4 left open the assignment of the counterterm of a point z among the domains Y, for the first-part terms: LFR II p.373 takes Y₁ as the smallest domain containing the term's own X, so the near-domain terms of z go to different Y₁. This section proposes a representation that avoids the question; its term properties are open (§47.3). The counterterm of z splits over the near domains X by their own second moments. Each near term with its piece c_X has its own age bound, since CRE's identity (3.56) holds domain by domain. What is left, R_z, is one term with the domain supp h_z. So every piece of the counterterm travels with one term, and none is split by the re-summation. Notation is §45's.

### 47.1 The Source (Read)

- CRE p.281, after (3.56): "The identities (3.56) hold for the localization domains X satisfying the condition X ⊂ □^{∼2}". They are identities for each such X. The "irrelevant terms" are bounded by O((L^{j−n})^{5−β})exp(−κd_j(X)) for that X. The first-order terms are moved to z by the Ward–Takahashi identities (I.4.14)–(I.4.15), which use the gauge invariance of each term, CRE p.259 property (iii).
- CRE (3.57) and (3.61)–(3.64): the tensor extended to all X ∋ z of the infinite lattice is Π^{(j)}, and for a covariant family Π^{(j)}_{μν,κλ} = β_jδ_{μν}δ_{κλ} for κ < μ, λ < ν. (3.65)–(3.66): A(φ_j, U_k) = Σ_zA(h_zφ_j, U_k), and A(h_z, U_k) = ½Σ_{μ<ν}tr F²_{μν}(z) + (the irrelevant terms).
- The Cauchy note §3: the plane-pair actions A_{PP′}(h_z, U) and N_j. Its *The moment of the lifted term.* gives the coefficient of one generation-j term along a lift, with the boundary term of the localised lift weighted by exp(−κd_j(X)). Its *Evidence.* (l.212) says "Every step of the proof is linear in the term".

### 47.2 The Per-Domain Counterterm (Derived)

For a near domain X ∋ z, X ⊂ □^{∼2}, let Q^X_{PP′}(z) := 𝐄^{(2)}_{μν,κλ}(X, z), with P = (κ, μ) and P′ = (λ, ν). By (3.56) the marginal part of 𝐄(X, U, z) − 𝐄(X, 1, z) is Σ_{κ<μ,λ<ν}½𝐄^{(2)}_{μν,κλ}(X, z)tr F_{κμ}F_{λν}(z), and A_{PP′}(h_z, U) = ½tr F_PF_{P′}(z) + (irrelevant terms), so Q^X is the matching coefficient, and Σ_{all X∋z}Q^X = Π^{(j)} (resp. Π^G). Put

$$
c_X(z,U):=\sum_{P,P'}Q^X_{PP'}(z)\,A_{PP'}(h_z,U),\qquad \mathrm{ren}_X(z;U):=\mathbf E^{(j)}(X,U,z)-\mathbf E^{(j)}(X,1,z)-c_X(z,U).
\tag{G.266}
$$

By (3.56) for X and the plane-pair form of (3.66), A_{PP′}(h_z, U) = ½tr F_P(z)F_{P′}(z) + (irrelevant terms), which the Cauchy note's N_j already uses,

|ren_X(z; U)| ≤ C_rE₀(L^{j−n})^{5−β−β″}e^{−κ″d_j(X)}

at the configurations where (3.56) is derived, those of U_n-type on the near domain of z (the cube □ ∈ π_n of CRE's first proof, p.279 l.45 to p.283 l.33, with □^{∼2}). Here κ″ < κ absorbs the moment weights |x − z||y − z| ≤ C(1 + d_j(X))² and the count of the pairs (x, y) ∈ X². ren_X has two parts: the irrelevant terms of 𝐄(X) of (3.56), bounded by the print, and the irrelevant part of c_X, the product of Q^X with the irrelevant part of A_{PP′}. The latter is bounded by |Q^X| ≤ (8B₃/α_{2,j})²E₀e^{−κd_j(X)} (RG I (4.5) at the order 2, the Cauchy note's l.210) times the plaquette amplitude squared, which on the class is at most (Cα_{0,n})², times L^{4(j−n)} and the order of the irrelevant part. Since (α_{0,n}/α_{2,j})² ≤ C·max(1, n − j) (the Cauchy note's l.210 with n for k), the factor max(1, n − j) costs an arbitrarily small β″ > 0 in the exponent, and C_r is a constant of d, L, B₃, β, and β″. The same holds for run B, a covariant family, and for G with G's tensor per X by the linearity of the proof, given that G(X, ·) is analytic and bounded by E₀e^{−κd_j(X)} on the polydisc, which is the lift condition (the Cauchy note's (a)). Q^X is not isotropic, and c_X carries its whole plane-pair tensor, as N_j does for G.

The remainder of the point z is

$$
R_z(U):=\mathrm{ct}_z(U)-\sum_{X\ni z,\ X\subset\square^{\sim2}}c_X(z,U),
\tag{G.267}
$$

where ct_z is the family's counterterm at z: β_jA_ε(h_z, ·) for a covariant family, Π^G_{22,11}A_ε(h_z, ·) + N_j for G, and β^B_{j+1}A_{ε/L}(h_z, ·) for run B. With Q^far := Σ_{X∋z, X⊄□^{∼2}}Q^X, the sum over the far domains of the infinite lattice, (3.57) and the definition of N_j give, for G,

R^G_z(U) = Π^G_{22,11}[A_ε(h_z, U) − Σ_PA_{PP}(h_z, U)] + Σ_{P,P′}Q^{G,far}_{PP′}A_{PP′}(h_z, U),

and the same for a covariant family with β_j in place of Π^G_{22,11}, and for run B on T_{ε/L}. The first bracket is the part of the Wilson action of fourth and higher order in the fine plaquette angles. The second is the far tail of the tensor, with |Q^far| ≤ C(j)E₀e^{−κL^{n−j}} by (3.48), where Cauchy's estimate for the second derivative and second moment gives C(j) ∝ (8B₃/α_{2,j})², not uniform in j (the Cauchy note's l.210). The sign of the far tail follows the convention of (G.267); only its size is used.

### 47.3 The Assignment (a Choice of Representation; Its Term Properties Open)

ren_X depends on U on X ∪ supp h_z ⊂ □^{∼2}. Let X̂ be the smallest domain of 𝐃_j containing X ∪ supp h_z; then d_j(X̂) ≤ d_j(X) + c_d, since supp h_z lies in the 3^d scale-j cubes at z. In (1.59)–(1.64), ren_X is to be treated as Bałaban treats a term with the domain X̂, with Y₁ := Y₁(X̂) on p.373. R_z is one term with the domain supp h_z. The far terms carry no counterterm (§45.1). So the counterterm of z is the sum of the pieces c_X, each travelling with its own X̂, and R_z, travelling with supp h_z. No piece is split by the re-summation.

This is a choice of the representation of V(Y), made identically in both runs. The sum over Y is unchanged, since the operations of LFR II pp.372–377 are linear in the terms and the counterterm's total is unchanged. A single V(Y) changes, and run A's V(Y) is then no longer Bałaban's printed V(Y): wherever a later step cites a property of Bałaban's V(Y), it has to be rechecked for this representation.

What the choice needs and does not yet have (open):
- The term properties of ren_X on X̂. Bałaban's terms have (i)–(iv) of CRE p.259 l.40–44, an analytic extension to U_j^c(X̂, α_{0,j}, α_{1,j}) with the bound (I.1.18). ren_X contains c_X, built from A_{PP′}(h_z, ·), whose plaquette logarithms Φ_P = (1/iε²)log U(∂p) are analytic only where the plaquettes are small, while A(h_z, ·) is entire. That ren_X has (i)–(iv) on X̂, on X̂∖X included, at every configuration where (1.59)–(1.64) evaluate it (the mixed-data configurations of (1.61)–(1.62), the decoupled data, and the complex points), is not checked.
- (1.68)–(1.69) for the moved terms. Y₁ is "the smallest localization domain … containing X, and containing these components of Z, which intersect X" (LFR II p.373 l.15–16). So (Y₁(X̂)∖Z) ⊂ (Y₁(X)∖Z) ∪ (at most 3^d cubes), but if X̂∖X meets a component of Z that X does not meet, Y₁(X̂) contains that whole component, and a second-part X ⊂ Z^c can become a first-part X̂. The factor e^{κc_d} is right for the inductive weight e^{−κd_j(X)}, and Bałaban's constant α of (1.68) "can be chosen arbitrarily small for γ small enough" (p.377 l.14).
- The term properties of R_z. R_z = Π[A_ε − Σ_PA_{PP}] + ΣQ^farA_{PP′} contains the same plaquette logarithms Φ_P through A_{PP} and A_{PP′}. Its analytic extension, bounds, and gauge invariance at the configurations of (1.59)–(1.64), and (1.68)–(1.69) in the Y to which it is assigned, are not checked. Whether (1.68)–(1.69) hold for terms moved to a Y with extra Z-components is not checked.

### 47.4 The r_z Item Per Domain (Derived Given §44's Inputs)

At a member c of 𝒞 read inside V(Y), §45.3's r_z^near splits as

$$
r_z^{\mathrm{near}}=\sum_{X\ni z,\ X\subset\square^{\sim2}}r_X-r_{R},\qquad r_X:=\mathrm{ren}^B_X(\iota_Yc^A)-\mathrm{ren}^G_X(c^A),\quad r_R:=R^B_z(\iota_Yc^A)-R^G_z(c^A),
\tag{G.268}
$$

since by (G.266) and (G.267) the renormalised near quantity of z is Σ_Xren_X − R_z in each family.

*The terms r_X.* §44 applies per X: R-data reads each near term at the composite, and by the clause of 62.3 c_X reads the composite too, so the per-X counterterm defect is zero, and 64.5's bound at the entry holds per X by the linearity of its proof. So option (a) of the r_z item holds per X, with (5.1c) for G at c^A per X, open where (i) is open. The moment defect, N_j, and the blocking artifact are inside the per-X renormalised terms and are not bounded separately; the blocking artifact's cancellation in the sum over z, which crosses the domains Y, is not needed for r_X.

*The term r_R.* Per point of the layer n, summed over the L^{4(n−j)} scale-j points and over j ≤ n. The configurations are those of the class at the layer, with the gradient bound α ≤ Cα_{0,n} of the entries (the LF note's l.528), and the constants C(j) and C_Π(j), both ∝ (8B₃/α_{2,j})², enter only multiplied by α², with C(j)α² + C_Π(j)α² ≤ C·max(1, n − j) by (α_{0,n}/α_{2,j})² ≤ C·max(1, n − j) (the Cauchy note's l.210 with n for k).
- The quartic parts. The fine plaquette angles are at most Cα(ε/a_n)², so each quartic part is at most C|coefficient|α⁴(ε/a_n)⁴L^{4(j−n)} per scale-j point, and C|coefficient|α⁴L^{−4n} per point of the layer after the count of the L^{4(n−j)} scale-j points. The coefficients are β^B_{j+1}, at most β̄, and Π^G_{22,11}, at most β̄ + C_Π(j)E₀e^{−δ₀M₁L^j}. So the quartic parts sum to at most C(n + 1)(β̄α⁴ + (n + 1)E₀α²)L^{−4n}.
- The far tails. Their difference is (Q^{B,far} − Q^{G,far})·A_{PP′} + Q^{B,far}·(A^{(ε/L)}_{PP′}(h_z, ι_Yc^A) − A^{(ε)}_{PP′}(h_z, c^A)). Per X, |Q^{B,X} − Q^{G,X}| is at most C_Π(j)E₀e^{−δ₀M₁L^j}e^{−½κd_j(X)}, the per-X form of the Cauchy note's *The moment of the lifted term.* (an input, with the per-X identity Q^{B∘ι,X} = Q^{B,X} of the affine reproduction of the lift), and at most 2C(j)E₀e^{−κL^{n−j}}e^{−½κd_j(X)} by (3.48). With A_{PP′} ≤ Cα²L^{4(j−n)}, the first part sums to at most CE₀Σ_{j≤n}max(1, n − j)min(e^{−κL^{n−j}}, e^{−δ₀M₁L^j}) ≤ CE₀(n + 1)²e^{−min(κ, δ₀M₁)L^{n/2}}, since max(L^{n−j}, L^j) ≥ L^{n/2}. The second part is the plane-pair blocking artifact with the coefficient Q^{B,far}, |Q^{B,far}| ≤ C(j)E₀e^{−κL^{n−j}}. Its weight-change part is at most 768C₀²(ε/a_j)ε₁² per point per generation for an O(1) coefficient and the isotropic artifact (the LF note's r_z item); A_{PP′} carries the weights of A_ε(h_z, ·) (the Cauchy note's l.74), and the plane-pair form of that bound is not written out. Given it, with C(j)ε₁² ≤ C·max(1, k − j) (the Cauchy note's l.210 and l.952), the weight-change part is at most C·max(1, k − j)E₀e^{−κL^{n−j}}L^{−j} per point per generation, and it sums to at most C(1 + k)²L^{−n}. The remaining part is open: the bound 16C_b(ε/a_n)ε₁² for an O(1) coefficient (the Cauchy note's (9.3)–(9.4), the LF note's l.404) holds for the sum over z, Σ_zb_{h_z} = b_1, and a per-z bound with a factor ε/a is not shown. The factor is needed: for j near n, e^{−κL^{n−j}} is O(1), and without ε/a_j the contribution is O(max(1, k − j)) per point rather than ≤ C_hθ̃^n.

The quartic parts, the first part of the far tails, and the weight-change part of the second are ≤ C_hθ̃^n per point of the layer in a history with k < 8n + j(C), since θ̃ ≥ L^{−θ_V/8} > L^{−1} and the factors are polynomial in n and k.

### 47.5 Status

Derived here, not reviewed in this form: 47.2, (G.266)–(G.268), the R_z formula, the invariance of the sum over Y, and the bounds of 47.4 on the quartic parts and the first part of the far tails.

Open:
- the term properties (i)–(iv) of ren_X on X̂ at every configuration where (1.59)–(1.64) evaluate it, and (1.68)–(1.69) for terms moved to a Y with extra Z-components (§47.3);
- the term properties of R_z and (1.68)–(1.69) in the Y to which it is assigned (§47.3);
- the per-z bound of the remaining part of the blocking artifact (§47.4);
- the j = n boundary-layer counterterm pieces of §45.4.

Inputs that these rest on:
- 64.5's bound per X, by the linearity of its proof, with (5.1c)'s own inputs;
- the lift condition, for the per-X (3.56) of G (47.2);
- the per-X form of the Cauchy note's moment of the lifted term, with the per-X affine reproduction;
- the plane-pair form of (3.66), used by the Cauchy note for N_j and not written out there, and the plane-pair form of the weight-change bound of the LF note's r_z item;
- the gradient bound α ≤ Cα_{0,n} of the entries' class.

What this changes in the LF note (recorded here, not edited). The r_z and r^s_z items reduce, given R-near and the clause of 62.3 (construction choices), to §44's inputs, (5.1c), and the lift condition, together with the four open items above. They are not closed.

## 49. The Conditions at U_{k,Λ} and U_1 (the Item of the LF Note's l.20)

The LF note's l.20, with its bullet at l.543, leaves open the conditions of LFR I (1.64)–(1.69) at U_{k,Λ}, U_1, U_2, and U(𝐁″_k(Y₁), D(s)), and 57.3 reduces the near domains at the boundaries of minimisation domains to the same conditions. This section derives them at U_{k,Λ} wherever a term reads it, at real points and along its line, and at U_1 at real points. The device is LFR I's own (1.44)–(1.52): a configuration twisted by exp iη𝐇, with 𝐇 small and decaying off its source, satisfies the conditions of the untwisted one at slightly larger thresholds. The twist is small against the thresholds only after the decay has paid for the gap between the scale k of the source and the layer m of the point, and this uses the separation of Λ from the layers of Z^c.

### 49.1 The Source (Read)

- LFR II (1.56)–(1.58), p.371: U_{k,Λ} = U_k(V″⌈_{Λ^c}, V_Λ^{(A)}); U_1 = (exp iη𝐇_{𝐁₁}(−(1/i)log M^·(U_{k,Λ})⌈_{Z″_k}) U_{k,Λ})^{u_1^{−1}}; U_{k,Λ} = (exp iη𝐇_k(−(1/i)log V′_k⌈_Λ) U_k)^{u_{k,Λ}^{−1}}.
- LFR II p.374, last paragraph: the extended right-hand side of (1.63) "is an analytic function of (𝐔, 𝐉) with a large domain of analyticity". p.375, first paragraph: the two "almost the same" statements, the substitution of the extended (1.63) into (1.62) and 𝐇_{𝐁₁}, and of the extended (1.62) into (1.61). (1.65): the extended U^0_k is analytic on Ũ^c_k(Y₄, α̃₀, α̃₁) with values in Ũ″^c_k(Y₁, α̃₀, α̃₁).
- LFR II p.373, first paragraph: the first terms of (1.59)–(1.60) are expanded again around U_{1,2}, then around U_1 by (1.57), then by (1.58), which gives "almost the whole new action, except the terms with localization domains intersecting the domain Z".
- LFR I p.191, the paragraph after (1.69): the spaces "are invariant with respect to G-valued gauge transformations"; for n = 0 they coincide with Ũ^c_k(X, α̃₀, α̃₁); the twist by exp iη𝐇_k^{(n)} maps the space of n + 1 into that of n, by the proof of (1.44)–(1.52).
- LFR I (1.46), first inequality (p.186): for U′ = exp(iη𝐇)U, |U′(∂p) − 1| ≤ |U(∂p) − 1|(1 + ½η|𝐇|(∂p)) + η²|(D^η_U𝐇)(p)| + ½η²(|𝐇|(∂p))².
- LFR I p.177: Z is the union of a class of connected components of the large field region Λ_k^c, each contained in a cube of the size 100MR_k, with no new large field region created inside it in the preceding N steps (condition (ii)).
- LFR I p.192 and (1.73): k − k₀ = N₀, defined by L^{−N₀+1}R_{k−N₀+1} = 1, so L^{N₀−1} ≤ (L + 1)(N₀ + 1)^{β₀}R_k; Λ = (Ω^{∼4}_{k₀+1})^c ∩ Z, obtained by adding one layer of M-cubes to Z″_k = (Ω^{∼5}_{k₀+1})^c ∩ Z.
- CRE (2.4), (2.5), (2.6), (2.28): ε_j = A₀g_j(log g_j^{−2})^{p₀}, R_k ≤ L(log g_k^{−2})^r, g_n ≤ (1 + β₀)(n − m)^{1/2}g_m and g_m ≤ (1 + β₀)g_n for n > m (p.255), and α_{0,m} = C₀g_m(log g_m^{−2})^{q₀}.

### 49.2 Where the Terms Read U_{k,Λ} and U_1 (Derived From the Text)

There are two kinds of reads.

- Inside the composite. U_{k,Λ} is the background and the argument of 𝐇_{𝐁₁} and, through (1.62), the data M^·(U_{k,Λ}) on (Y₂⁰)^c ∩ Y₂. U_1 is, through (1.61), the data M^·(U_1) on (Y₁⁰)^c ∩ Y₁. These are stages of the extended U^0_k, which LFR II defines as the composite of the substitutions of p.375. A composite is defined at a point only where each stage lies in the domain of the next, so (1.65), which states that the composite is analytic on Ũ^c_k(Y₄, α̃₀, α̃₁), contains the statement that its stages are defined and analytic there. For (1.63) this is also p.374's "large domain of analyticity". This follows from the print (§55.3) and is called R-65c here; the LF note already uses (1.65) at U^0_k, at the thresholds α̃′/2 (*The room at real points.*). Under R-65c the reads inside the composite need no condition of their own, since the second-stage terms read U^0_k only.
- Directly by terms. The first-stage terms whose localisation domains X do not meet Z are expanded again around U_1 and U_{k,Λ} (p.373), so they read U_1 and U_{k,Λ} on X ⊂ Z^c, and the near-domain terms of 57.1 read them on □₀ through R-data. Here the conditions of the term's own space are needed at the configuration on X.

So the conditions are needed at the points of Z^c, in the spaces of the old terms. Their layers there are those of 𝐁_k, which coincide off Λ with those of 𝐁″_k (p.370), and Ω″_j ∩ Z^c = Ω_j ∩ Z^c by LFR I (1.12).

### 49.3 The Twist Moves Each Quantity by a Multiple of h (Derived)

At real data U_k, U_{k,Λ}, and U_1 are G-valued and 𝐇_k and 𝐇_{𝐁₁} are real, so the gauge transformations u_{k,Λ} and u_1 of (1.57)–(1.58) are G-valued: LFR II p.373 l.29–30 cites (106) [12], [12] is CMP 98 (LFR II p.392 l.28), and CMP 98 (105)–(106) write u as a product of parallel transports and of exponentials of contour variables, each G-valued at G-valued configurations near 1. The spaces are invariant under G-valued gauge transformations (LFR I p.191, also for n = 0). So the conditions at U_{k,Λ} are those at U^♮ := exp(iη𝐇_k)U_k. Since U_{k,Λ} = (U^♮)^{u_{k,Λ}^{−1}}, U_1 is a G-valued gauge transform of exp(iη𝐇′)U^♮ with 𝐇′ := Ad_{u_{k,Λ}}𝐇_{𝐁₁}, and |𝐇′| = |𝐇_{𝐁₁}|, |∇𝐇′| = |∇_U𝐇_{𝐁₁}| in the transformed background, ∇ the covariant derivative in the untwisted background as in LFR I (1.45).

*The bound h.* By the LF note's bound for each 𝐇 of the chain (its *The exterior part W_ext*, the list of the four arguments and the paragraph *Each 𝐇*), with a_m := L^mη the spacing of the layer m,

a_{j(x)}|𝐇(x)| + a_{j(x)}²|∇𝐇(x)| ≤ h(x) := C_𝐇ε̂e^{−(δ₀/16)d(y,Λ)}, x ∈ Δ(y),

for 𝐇_k, whose argument lies on Λ, and for 𝐇_{𝐁₁}, whose argument lies on Z″_k ⊂ Λ. For 𝐇_{𝐁₁} the bound is VAR's Proposition 9 with the decay (190) at the background U_{k,Λ}, which is a minimiser of regular data, U_{k,Λ} = U_k(V″⌈_{Λ^c}, V_Λ^{(A)}) (LFR II p.371 l.32–33), so VAR applies there directly and the bound does not use (1.65). Here ε̂ ≤ 2ε₁, and by the LF note's l.349 either ε₁/ε_k = C(M)R_k, or ε₁/ε_k ≤ C(1 + β₀)(k_s − k + 1)^{1/2}(1 + A₁/A₀), with k_s − k < 7n (its l.632).

*The move.* Let U be G-valued and satisfy the conditions of a space of the kind (1.64)–(1.69) at thresholds ≤ 1 times their scale factors, and let U^♮ = exp(iη𝐇)U with 𝐇 real and a_{j(y)}|𝐇(y)| + a_{j(y)}²|∇𝐇(y)| ≤ h(y) ≤ 1 at every y. Then each conditioned quantity of U^♮ at a point x of the layer m exceeds that of U by at most C_twĥ(x) times its scale factor, with ĥ(x) := sup_ye^{−(δ₀/2)d(x,y)}h(y), and C_tw ≥ 14 a constant of d, of G through the Baker–Campbell–Hausdorff series, of the averaging, and of δ₀ through the decay of the local maps.

- The plaquettes. By LFR I (1.46), with |𝐇|(∂p) ≤ 4h/a_m, |(D^η_U𝐇)(p)| ≤ 4h/a_m², and η ≤ a_m, the plaquette moves by ≤ 2h|U(∂p) − 1| + 4hη²a_m^{−2} + 8h²η²a_m^{−2} ≤ 14hη²a_m^{−2}, which is h(x) ≤ ĥ(x) times 14 times the scale factor η²a_m^{−2}.
- The determining-set configurations U_{p,X}(M^·(·)) and their currents J_{p,X}. The twist changes the data M^·(U) by the factor exp iQ̃(η𝐇) of (1.63) on each block bond, which is ≤ a constant of the averaging times h at the block in the data norm of the layer. U_{p,X} and J_{p,X} are nonlocal functions of the data, with the exponential decay e^{−δ₀d(x,y)} of PBG (3.133) and of the multipliers (*The room at real points.*, with the count of (b)). So their move at x is at most CΣ_ye^{−δ₀d(x,y)}h(y) ≤ C′ĥ(x), the sum over y converging with the factor e^{−(δ₀/2)d(x,y)}.
- The current of the configuration. At real points U_{k,Λ} and U_1 are minimal configurations of their data, and their current on every layer is the layer-adapted bound of §59, derived at real points; it is not obtained by a move.
- A′ and ∇A′. At real points U′ = 1 before and after the twist, so these conditions do not move.
- The cube-gauge conditions (1.65), (1.67), and (1.69). With u the gauge transformation of U on a cube □ of the layer, U^u = exp iηA, and (U^♮)^u = exp(iηAd_u𝐇)exp(iηA) = exp iηA^♮ with A^♮ − A = Ad_u𝐇 + O(η|A||𝐇|) by the Baker–Campbell–Hausdorff series. Since a_m|A| and a_m²|∇A| are below BCMα_{0,m} ≤ 1, a_m|A^♮ − A| and a_m²|∇(A^♮ − A)| are ≤ C_twh on the cube, and h ≤ e^{(δ₀/2)·2M}ĥ(x) there, a constant absorbed in C_tw.

Since h(y) ≤ h(x)-type bounds hold with d(y,Λ) ≥ d(x,Λ) − d(x,y), ĥ(x) ≤ C_𝐇ε̂e^{−(δ₀/16)d(x,Λ)}, the same form as h.

### 49.4 The Ratio on Λ^c (Derived)

*The collar of Λ in Z.* Λ ⊂ Ω^c_{k₀+1} ⊂ Λ^c_{k₀+1} = Z_{k₀+1}, by (1.73) and CRE (2.1), with Z_j the large field region of the step j. By §46.2, Ω^c_{j+1} ⊃ (Z′_j)^{∼8} ⊃ Z_j^{∼8}, so Z_{j+1} = Λ^c_{j+1} ⊃ Ω^c_{j+1} ⊃ Z_j^{∼8}, and the regions grow from step to step. N₀ ≥ 2, since L^{N₀−1} = R_{k−N₀+1} > 1. So Λ ⊂ Z_{k₀+1} ⊂ Z_{k−1}, and Z_k ⊃ Λ^{∼8}, with the layers of the cubes of the scale k. Λ^{∼8} is wall-connected to Λ, since the cube neighbourhood of a cube is wall-connected, so it lies in the component class Z that contains Λ. Hence dist(Λ, Z^c) ≥ 8MR_k in the units of the scale k. Also Z ∖ Λ ⊂ Ω″_k, since Z″_k ⊂ Λ, so the collar Z ∖ Λ is of the layer k in 𝐁″_k and in 𝐁_k.

*The separation.* Let y ∈ Z^c be a point of the layer m ≤ k. A path from y to Λ crosses the collar, ≥ 8MR_k in the units of the scale k. If m < k − N₀, the path also runs from y ∉ Ω″_{m+1} into Ω″_k ⊂ Ω″_{k−N₀+1}, so it crosses each shell Ω″_l ∖ Ω″_{l+1}, m + 1 ≤ l ≤ k − N₀, which is ≥ LM wide in the units of the scale l: by admissibility (46.4) for l ≥ h + 1, on Z, on Z^c, and across ∂Z, with (G.265) the sharper bound inside Z, and by §46.2 directly for l ≤ h, where the layers are the old Ω_l and dist(Ω_{l+1}, Ω_l^c) ≥ 8LMR_{l+1}. These pieces of the path are disjoint. The scaled distance counts each extent in the units of the layer it crosses (the LF note's l.663, PRT2 (2.46)). So

d(y, Λ) ≥ 8MR_k + LM·max(0, k − N₀ − m).

*The ratio.* By CRE (2.6), g_k/g_m ≤ (1 + β₀)max(1, (k − m)^{1/2}), and log g_m^{−2} ≥ log g_k^{−2} − 2log(1 + β₀) ≥ ½log g_k^{−2} for γ small. With ε₁ ≤ C(M)R_kε_k·ρ_k, ρ_k := max(1, (k_s − k + 1)^{1/2}) covering both cases of the bound h, R_k ≤ L(log g_k^{−2})^r (a consequence of CRE (2.5)), and α′_{0,m}/2 = α_{0,m}/(8B₃) = C₀g_m(log g_m^{−2})^{q₀}/(8B₃),

h(x)/(α′_{0,m}/2) ≤ 16B₃C_𝐇C′(M)L(A₀/C₀)(1 + β₀)2^{q₀}(log g_k^{−2})^{p₀+r−q₀} · b_m(y), b_m(y) := ρ_k·max(1, (k − m)^{1/2})e^{−(δ₀/16)d(y,Λ)},

with C′(M) := C(M)·C(1 + A₁/A₀). Write n′ := max(0, k − N₀ − m), so k − m ≤ N₀ + n′ and b_m(y) ≤ ρ_k(N₀^{1/2} + n′^{1/2})e^{−(δ₀/2)MR_k}e^{−(δ₀LM/16)n′}. By the definition of N₀, N₀ ≤ C_L(1 + log R_k), so N₀^{1/2}e^{−(δ₀/4)MR_k} ≤ 1 for M ≥ M(δ₀, L), as R_k ≥ 1; n′^{1/2}e^{−(δ₀LM/16)n′} ≤ 1 for δ₀LM ≥ 8; and ρ_ke^{−(δ₀/4)MR_k} ≤ 1, since k_s − k + 1 ≤ 8k + 1 and R_k ≥ (log g_k^{−2})^r ≥ (log(bk))^r by CRE (2.5)–(2.6), so (δ₀/4)MR_k ≥ ½log(8k + 1) for M ≥ M(δ₀, b, r). So b_m(y) ≤ 2, and

h(x) ≤ θ_k·α′_{0,m}/2, θ_k := 32B₃C_𝐇C′(M)L(A₀/C₀)(1 + β₀)2^{q₀}(log g_k^{−2})^{p₀+r−q₀},

at every point x of Z^c. In the collar Z ∖ Λ the layer is m = k, so the factor (k − m)^{1/2} is absent, but the separation is not available, and b_k(y) ≤ ρ_ke^{−(δ₀/16)d(y,Λ)}. So the same bound holds at the collar points with d(y, Λ) ≥ (16/δ₀)log ρ_k, and at every collar point in the case ε₁/ε_k = C(M)R_k of the LF note's l.349, where ρ_k = 1. At the collar points closer to Λ, in the case ε₁/ε_k ≤ C(1 + β₀)(k_s − k + 1)^{1/2}(1 + A₁/A₀), the bound carries the factor ρ_k, which θ_k's power of log g_k^{−2} does not absorb uniformly in k_s − k (open). The same holds for ĥ. θ_k → 0 for γ small, uniformly in k, since q₀ > p₀ + r, the choice of the LF note's (T-Λ) (its l.564), with γ chosen after M.

The thresholds of the old terms' spaces at the layer m are, for the α₀-type quantities, at least ϖα_{0,m}/(1 + β₀) times their scale factors at the reduced thresholds, with the prefactor ϖ > 1 − 4β = ½ of (1.64) and (1.68) at β = 1/8 (LFR I p.190 l.25, p.191 l.7), and the powers of L₀ are ≥ 1 (55.5); the cube-gauge thresholds BCMα_{0,m} are larger. So every move of 49.3 is ≤ θ times the quantity's threshold at α̃′/2, with θ := 2(1 + β₀)C_twθ_k ≤ 1/16 for γ small, at the points governed by (1.64)(i) and (1.68).

*The points of (1.66)(ii).* LFR I (1.66)–(1.67) hold on (Ω_m ∖ Ω_{m+1}) ∩ X for m = k₀ + 1, …, j, with k₀ = k − N₀ (LFR I p.181 l.40), and they are not restricted to Z (p.190 l.48–53). The space is the intersection of all its conditions, so at a point of Z^c of the layer m, k₀ < m ≤ j, the threshold of (1.66) binds where it is smaller. In the scale factors of the layer m it is at least ϖL₀^{2(j−m)}α_{0,j}L^{−3(j−m)} ≥ ϖα_{0,j}L^{−3N₀}, since j − m ≤ k − k₀ = N₀, the cube-gauge threshold of (1.67) likewise. Against α_{0,j} in place of α_{0,m}, the ratio of 49.4 carries g_k/g_j ≤ (1 + β₀)N₀^{1/2} (CRE (2.6)) in place of max(1, (k − m)^{1/2}), and the extra factor L^{3N₀} = L³R_{k−N₀+1}³ (by the definition of N₀, L^{N₀−1} = R_{k−N₀+1}) ≤ C_LR_k³N₀^{3β₀} (CRE (2.8)). These are points of Z^c, so d(y, Λ) ≥ 8MR_k by the separation, the factor e^{−(δ₀/2)MR_k} is available, and ρ_kN₀^{1/2}C_LR_k³N₀^{3β₀}e^{−(δ₀/2)MR_k} ≤ 1 for M ≥ M(δ₀, L, b, r), since N₀ ≤ C_L(1 + log R_k) and (δ₀/4)MR_k ≥ ½log(8k + 1). So the moves at these points are ≤ θ times the threshold of (1.66) at α̃′/2, with the same θ. At the collar points, Z ∖ Λ ⊂ Ω″_k, the configuration's layer is k ≥ j, so the threshold of (1.66) in the scale factors of the layer k is at least ϖα_{0,j}, and the ratio carries g_k/g_j ≤ (1 + β₀)N₀^{1/2}. N₀^{1/2} ≤ C_L(1 + log R_k)^{1/2} grows like (log log g_k^{−2})^{1/2}, which the factor (log g_k^{−2})^{p₀+r−q₀} of θ_k absorbs for γ small, so the collar case above applies with θ_kN₀^{1/2} → 0 for θ_k.

### 49.5 The Conditions (Derived)

- U_{k,Λ} at real points. U_k satisfies the conditions of the old terms' spaces at the thresholds α̃′/2 (*The room at real points.*, through §3(d)'s item on (1.64)–(1.69)). By 49.3 and 49.4, U_{k,Λ} satisfies them on Λ^c, except at the collar points of 49.4 left open, at (1 + θ)α̃′/2 ≤ (17/32)α̃′, the current by §59. This holds in each run, and for run B's chain at run A's data, since (1.57)–(1.58) are identities of each run's minimisation maps with the same bounds (the LF note's *Run B's chain at run A's data*).
- U_1 at real points. The same step applied to exp(iη𝐇′)U^♮ adds a second move of at most θ times each threshold at α̃′/2, since the bound of 49.3 does not depend on where U^♮ lies below its thresholds. So U_1 satisfies the conditions on Λ^c at (1 + 2θ)α̃′/2 ≤ (9/16)α̃′.
- U_{k,Λ} along its line. U_{k,Λ} is a member of the joint line of the LF note (*The joint line.*), with c(t) = U′U, U the real member. The room of *The room at real points.* is ½ϖ ≥ ¼ of the threshold without the prefactor. With the real-point values below (1 + θ)·½ϖ·T, the room is ½ϖ(1 − θ)T > (15/64)T, and on the halved radius each line move is at most ⅛T by the Schwarz lemma, so ⅛T ≤ ½ϖ(1 − θ)T and the line keeps the conditions on |t| ≤ 1/(2r(Y)). The LF note's Cauchy estimate in t (its l.459) is then made on the halved radius, at a factor 2 in the variation, which its constants absorb (recorded here, not edited).

For the near-domain reads the spaces are RG I's, with the conditions of CRE (2.34)–(2.39) (p.261). They are of the kinds of 49.3, with the thresholds α_{c,m} of the same scales, so 49.3 and 49.4 give them at U_{k,Λ} and U_1 on every □₀ ⊂ Λ^c with the same θ. The condition (iv) on □₀ enters as at the other members (§62).

### 49.6 Status

Derived here, not reviewed in this form:
- the conditions of the old terms' spaces at U_{k,Λ} at the points of Z^c and of the collar Z ∖ Λ, except the collar points of 49.4 left open, at (17/32)α̃′ at real points and below α̃′ along its line for |t| ≤ 1/(2r(Y)), the thresholds of (1.66)(ii) included;
- the same at U_1 at real points, at (9/16)α̃′;
- the separation d(y, Λ) ≥ 8MR_k + LM·max(0, k − N₀ − m) at the points y of Z^c of the layer m, and the ratio θ_k, uniform in k in both cases of the LF note's l.349 on Z^c.

Premises: §46.2 and the admissibility of 46.4; the LF note's bound of each 𝐇 of the chain, and VAR's Proposition 9 at U_{k,Λ} for 𝐇_{𝐁₁}; *The room at real points.* with its three premises; the current of §59 at real points; the choice q₀ > p₀ + r; M large after δ₀, L, b, and r, and γ small after M.

Open: the collar points of Z ∖ Λ with d(y, Λ) < (16/δ₀)log ρ_k, in the case ε₁/ε_k ≤ C(1 + β₀)(k_s − k + 1)^{1/2}(1 + A₁/A₀) of the LF note's l.349.

From the print (§55.3): R-65c, under which the reads inside the composite U^0_k are covered by (1.65), in each run. The reads of U_{k,Λ} and the extended (1.62)–(1.63) at run B's entries (the LF note's l.543) are not covered by R-65c; under R-data the near-domain terms read them at the composites (§44, 64.5).

Also open: U_1 along a line and U_2, which belong to the U_{1,2} item (§§56, 61); the representation configuration U(𝐁″_k(Y₁), D(s)) at the decoupled data, which belongs to (iii) (§§65, 67).

What this changes in the LF note (recorded here, not edited): at its l.20, U_{k,Λ} and the extended (1.62)–(1.63) move from open to derived where terms read them directly, and to covered by R-65c inside the composite; U_1 moves to derived at real points.

## 50. The U_{1,2} Item: U_{1,2} as a Member, and the Cut

The LF note's l.18 and l.419–421 list, for U_{1,2} near the cut ∂Ω″^∼_{h+1}: the entries and lifts of U_1 and U_2, the lift–patch commutator, r_z at U_{1,2}, and (5.1c) at the patch on the near domains that meet the cut. This section takes U_{1,2} itself as a member of the chain. That removes the entries. The commutator moves into the fine side and the lift condition at the cut, the near-domain case reduces to §44 and 57.1, and r_z keeps its form with its bound open within reach of the cut.

### 50.1 The Source (Read)

- LFR II (1.52)–(1.53), p.370: 𝐁₁ = 𝐁″_k ∪ 𝐁_h(Ω″^∼_{h+1}), 𝐁₂ = 𝐁″_k ∪ 𝐁_h((Ω″^∼_{h+1})^c); U_{𝐁₁} and U_{𝐁₂} "are supported in the domains Ω″^∼_{h+1}, (Ω″^∼_{h+1})^c correspondingly, and they are introduced in order to break the configuration U^0_k into two independent parts by the boundary conditions at the boundary ∂Ω″^∼_{h+1}" (l.23–25). U_1 carries the data V″ on Λ^c, M^k(U_0^{(AL)}) on Λ ∩ Ω″_k, and 1 on Z″_k ∩ Ω″^∼_{h+1}; U_2 carries 1 on (Ω″^∼_{h+1})^c ∩ Ω″^{∼2}_{h+1} and V″ on (Ω″^{∼2}_{h+1})^c (l.28–29). "In the configuration U_{1,2} the arguments are separated completely across the boundary ∂Ω″^∼_{h+1}. It seems to be singular on a neighborhood of this boundary, but in fact it is regular, and satisfies the regularity conditions typical for an h-order configuration on the domain (Ω″_{h+1})^c ∩ Ω″^{∼2}_{h+1}. It is so, because the arguments of the corresponding functions are equal to 1 on this domain, and the exponential decay properties enforce the additional regularity." (l.35–38)
- LFR II (1.54): U^0_k = (exp iη𝐇″_k(𝐆″_kJ_{1,2}, H″_{1,k}Q̃_·(η𝐀₀)⌈_{Z″_k∩Ω″^{∼2}_{h+1}})U_{1,2})^{(u^0_k)^{−1}}, so U_{1,2} is the background of 𝐇″_k.
- LFR II p.372 l.12–28 and p.373 l.2–3, l.12–13: the expressions of the first stage are localised in domains Y_0 ∈ 𝐃_k that contain □₀, or X when X ⊄ □^{∼2}, and at least one component of Λ^∼ (p.372 l.17–18); the "second set of expressions localized in the domains Y_0, but depending analytically on the background field U_{1,2}" (p.373 l.2–3).
- CRE (2.2), (2.10)–(2.11), p.255–256, and (2.14), p.257: 𝐁₁ and 𝐁₂ are joins, and on the scale-0 part Γ_0 = Ω_1^c of 𝐁_h(Ω) the data are the bond variables themselves.

### 50.2 U_{1,2} as a Member (Derived)

U_{1,2} is one configuration on the whole lattice, since the supports Ω″^∼_{h+1} and its complement partition it. So for each domain Y it gives one configuration on Y^∼, and every function of U_1 and U_2 on their supports is a function of U_{1,2}. This removes the obstruction of the LF note's l.438. That ι_X and ι_Y apply to U_{1,2} is a statement of definability; the properties used at the other members are not transferred by it.

Every direct read of U_1 is a read of U_{1,2}: U_1 is supported in Ω″^∼_{h+1}, where U_{1,2} = U_1, and in particular on Z^c (p.371 l.26–27). U_2 is read only through U_{1,2}, as the LF note's l.420 records. The reads of (1.61), M^·(U_1) on the layer (Y_1^0)^c ∩ Y_1 (p.373 l.20), lie inside the composite U^0_k and are covered by R-65c (§55.3); this section does not show that the layer lies in Ω″^∼_{h+1}. The composites of (1.59), the representation configurations of (1.61)–(1.63), and the decoupled configurations of (1.60) are read by the terms as link images of members, not as members. So the member set 𝒞′ := {U″_k, U^0_k, U_{1,2}, U_{k,Λ}, U_k} carries every configuration that the terms read directly, with the link (1.57) taken at U_{1,2} on Ω″^∼_{h+1}.

With U_{1,2} a member, the pieces of the item become the following.
- The entries. V^B(Y)[c] is defined, with c_{U_{1,2}} one configuration on Y^∼.
- (i) at U_{1,2}. (i) := G(X, U^A_{1,2}) − 𝐓^A(X, U^A_{1,2}) with G(X, ·) = 𝐓^B(X, ι_X ·), the same lift ι_X as at every member, so no second lift enters (i). Its bound by the class norm d_j holds where the lifted pair lies in run B's space, which is the lift condition at U_{1,2}. That condition is not derived at U_{1,2}, on either side of the cut: the LF note's l.410 assigns it at U_1 and U_2 to this item. The lift–patch commutator, ι_Y patch(U^A_1, U^A_2) against patch(U^B_1, U^B_2), is not removed; it is the fine side at the cut (50.3).
- The near domains that meet the cut. Under R-data and the clause of 62.3, the near terms and their counterterms read the composite U_n(□₀, M^·(U_{1,2})) on □₀, the local minimiser of its own block data, so the local-minimiser requirement of 𝒮_z holds by construction and the LF note's l.419 and l.421, which concern U_{1,2} itself, do not enter. §44 and 64.5 then bound irr_j at the composite, with Lemma 4 applied with membership on X only (57.1). The input is the data condition of M^·(U_{1,2}) on □₀ near the cut. Bałaban's regularity statement of p.370 l.35–38 gives it as his stated result, used under the rule for his stated results; the thresholds are those of an h-order configuration on the domain he names, which the statement does not quantify further. This step is derived given that statement and §44's inputs.
- r_z at U_{1,2}. r_z = ren^B(X, ι_Yc^A) − ren^G(X, c^A) at c = U_{1,2} has the same form as at the other members. Its bound within reach of the cut is open: route (a) of the r_z item needs (5.1c) for G at c^A, which the previous bullet gives at the composite under its inputs, and the moment defect needs the lift identity ι(Mc^B) = c^B, which is not shown for the patch within reach of the cut.

### 50.3 The Fine Side at the Cut (Open)

The joint line at U_{1,2} needs ι_YU^A_{1,2} = e^{i(ε/L)𝐒}U^B_{1,2} with σ_{U_{1,2}} := sup(a_{j(x)}|𝐒(x)| + a_{j(x)}²|∇𝐒(x)|) ≤ C(ε₀)d̄(x), as at the other members (the LF note's *The Fine Side at the Multiscale Chain.*).

- Away from the cut. On each side U_{1,2} is the side minimiser U_1 or U_2, and the coarse side covers the joins 𝐁₁ and 𝐁₂ under (J-W) (the LF note's *The joins.*, with the middle-layer width open, its l.192–193). The one-step identity ι(Mc^B) = c^B holds for a member whose run-B constraints factor through M. For the patch it is not shown within the reach of the one-step kernel of the cut, since U^B_1 and U^B_2 minimise with boundary conditions at the cut. A decay rate of the defect away from the cut is not derived here.
- At the cut. By 51.2, the joins carry the scale-0 layer of 𝐁_h(Ω) in the strip Ω ∖ Ω^{∼−2}, at least LM₁ fine spacings wide, and on that layer the data are the bond variables. With the data 1 of (1.53), U_1 = 1 on the scale-0 bonds of its strip inside the cut and U_2 = 1 on those of its strip outside, in each run and up to the gauge freedom of VAR (4), which is trivial on 𝔅. So U^A_{1,2} and U^B_{1,2} have no first-order jump at the cut: the plaquettes of the two strips are trivial. The bonds that cross ∂Ω″^∼_{h+1}, if they belong to neither scale-0 layer, are assigned by the patch, and their values are not discussed in the print. What is open is the bound of 𝐒 at the strips: U^A_{1,2} and U^B_{1,2} agree there, and 𝐒 is the response of the lift ι_Y to the configuration 1 on the strips and to the side minimisers beyond them. That response is not bounded here.
- The data condition (7) at U_2's junction with V″ at ∂Ω″^{∼2}_{h+1} is open, as in 51.5.

### 50.4 Status

Derived here, not reviewed in this form: U_{1,2} as a member (definability), the entries, and the decomposition of (i) with one lift.

Derived given inputs: the near domains at the cut, given Bałaban's regularity statement of p.370 l.35–38 for the data of the composite, used as his stated result, and §44's inputs; the bound of (i), given the lift condition at U_{1,2}.

Open:
- the lift condition at U_{1,2}, on both sides of the cut;
- the fine side of the joint line at the cut, the bound of 𝐒 at the scale-0 strips, which contains the lift–patch commutator;
- the lift identity for the patch within reach of the cut, and with it the bound of r_z at U_{1,2} there;
- the values on the bonds that cross the cut, if they belong to neither scale-0 layer;
- the data condition at U_2's junction with V″ (51.5).

From the print: R-65c for the reads of (1.61) inside the composite (§55.3).

What this changes in the LF note (recorded here, not edited): at its l.438 the entries of U_1 and U_2 are replaced by the member U_{1,2}; at its l.18 and l.419–421 the entries leave the item, (5.1c) at the cut moves to the composite under R-data and the clause, and the commutator, the lift condition, and r_z near the cut stay in the item.

## 51. Two Lemmas From VAR's Theorem 1 at Bałaban's Joins

The first equalities of LFR II (1.61)–(1.63) and the endpoint identities of §53 say that a minimiser of a global problem, restricted to a domain Ω, is the minimiser of the localised problem on Ω at its own data. This section derives that restriction property from VAR's Theorem 1 and the criticality condition (178), for Bałaban's joins CRE (2.14).

### 51.1 Sources (Read)

- VAR p.277: the geometry of a determining set, Ω_j ⊂ T_η, Ω_0 ⊃ Ω_1 ⊃ … ⊃ Ω_k, each Ω_j a union of blocks of the side M₁L^jη, with (1) (L^jη)^{−1}dist(Ω_j^c, Ω_{j+1}) > RM₁ for R ≥ R₁; Λ_j = Ω_j^{(j)} ∖ Ω_{j+1}^{(j)}, and 𝔅_k = ∪_j Λ_j. Bonds and plaquettes belong to a set when they have "at least one end-point" or "at least one corner" in it (p.277 l.17). The scale 0 is admitted.
- VAR p.278: the class 𝔘_k({Ω_j}, ε₀), given by (2), |U(∂p) − 1| < ε₀L^{−2j} and |(D^{η*}_U∂U)(b)| < ε₀L^{−2j}(L^jη)^{−1} on Ω_j; the constraints (3), Ū^j = V on Λ_j; the data condition (7), |(∂V)(p′) − 1| < ε₁ on 𝔅_k; and the remark (l.46) that if the space (6) is non-empty and ε₀ is small, V satisfies (7) with ε₁ = O(ε₀), by Proposition 2 of [4], "Hence our assumption has a meaning only for ε₁ smaller than ε₀".
- VAR p.279, Theorem 1: for V with (7) at ε₁ ≤ a₁, a minimal orbit exists in 𝔘_k({Ω_j}, B₃ε₁) ∩ 𝔙_k(𝔅_k, V), and it is the unique critical orbit in 𝔘_k({Ω_j}, ε₀) ∩ 𝔙_k(𝔅_k, V) when B₃ε₁ ≤ ε₀ ≤ a₀. The regularity (9), (10) holds after "a gauge transformation u defined on a neighborhood of □" (p.279 l.17–18).
- VAR p.306 l.18–26, (178): "⟨δA′, J⟩ = 0 for δA′ : Q(U_k)δA′ = 0, or P₀*(U_k)J = 0", which "does not involve any gauge fixing".
- The averages compose: Ū^{j} is the average of Ū^{j−1} over the blocks of the scale j and the bonds between them (VAR (3), RG I (1.15) with REG (1.5)), so Q^{n+1}(U) = Q(Ū^n)Q^n(U) for the linearisations at U.
- CRE p.256 l.57–64: for a domain Ω, a union of M₁-cubes of T_ξ, ξ = L^{−j}, 𝐁_j(Ω) is "a minimal determining set with a support in Ω", with Ω = Ω₀ ⊃ Ω₁ ⊃ … ⊃ Ω_j, Ω_n a union of L^nξM₁-cubes, dist(Ω_n, Ω^c_{n−1}) ≥ L^nξM₁, and Ω^{∼−2} ⊂ Ω_j. CRE p.257 l.8–16, (2.14): if ∂Ω ⊂ Ω_j ∖ Ω_{j+1} for 𝐁, Ω is a union of M₁-cubes of T_ξ, and the distance from ∂Ω to the boundary of Ω_j, Ω_{j+1} inside Ω is at least 2M₁, then 𝐁 ∪ 𝐁_j(Ω) := (𝐁 ∩ Ω^{∼−2}) ∪ (𝐁_j(Ω) ∩ (Ω ∖ Ω^{∼−2})).
- LFR II pp.370–371: 𝐁₁ and 𝐁₂ of (1.52) are such joins, with the data 1 of (1.53) at the cut; p.370 l.51 to p.371 l.2 states that the 𝐁₁- and 𝐁″_k-conditions coincide "except the boundary layer of the width 2M₁".

### 51.2 The Cut Carries Bałaban's Scale-0 Strips (Quoted)

A join (2.14) carries the layers of 𝐁_j(Ω) of every scale 0, …, j in the strip Ω ∖ Ω^{∼−2}, the finest at ∂Ω. At the cut ∂Ω″^∼_{h+1}, (1.53) gives these layers the data 1, so U_1 = 1 and U_2 = 1 on their scale-0 bonds at the cut, up to the gauge freedom VAR (4), which is trivial on 𝔅 (55.4). A free-boundary model of U_1 and U_2, and a band of finer layers added at the cut, do not describe Bałaban's U_1 and U_2 and are not used.

### 51.3 The Composition of the Constraints (Derived)

Let 𝐁 be a determining set on Ω₀ with domains Ω^𝐁_n, and 𝐁^D a determining set in Ω ⊂ Ω₀ with domains Ω^D_n, both with blocks from the one nested family of partitions. Let δA be a bond field on Ω, extended by 0 outside Ω, with Q_{𝐁^D}(U)δA = 0. The condition is:

(R) every bond of the scale n of 𝐁 is a bond of the scale n of 𝐁^D, or has no endpoint in Ω^D_{n+1}.

Claim: for every n, Q^n(U)δA(b) = 0 on every bond b of the scale n with no endpoint in Ω^D_{n+1}. For n = 0 such a bond lies in Λ^D_0, where Q^0 is the identity and the constraint gives δA(b) = 0, or has no endpoint in Ω, where δA = 0. For the step n → n + 1, let b be a bond of the scale n + 1 with no endpoint in Ω^D_{n+2}. If it has an endpoint in Ω^D_{n+1}, it is a bond of Λ^D_{n+1}, constrained. Otherwise its two blocks of the scale n + 1 lie outside Ω^D_{n+1}, since Ω^D_{n+1} is a union of such blocks, and Q^{n+1}(U)δA(b) is a linear function of Q^n(U)δA on the bonds of the scale n inside and between these blocks, none of which has an endpoint in Ω^D_{n+1}; these vanish by induction. With (R), every constraint of 𝐁 vanishes on δA: Q_𝐁(U)δA = 0.

(R) holds for the joins (2.14), with 𝐁^D := 𝐁 ∪ 𝐁_j(Ω). On Ω^{∼−2} the two sets coincide, so a bond of 𝐁 with an endpoint in Ω^{∼−2} is a bond of 𝐁^D. Every other bond of 𝐁 that has an endpoint in Ω lies in the strip Ω ∖ Ω^{∼−2}, which lies in Ω^𝐁_j ∖ Ω^𝐁_{j+1} at distance at least 2M₁ from Ω^𝐁_{j+1} (the hypothesis of (2.14)), so it is a bond of the scale j. 𝐁_j(Ω) has the scales 0, …, j only, so Ω^D_{j+1} ∩ (Ω ∖ Ω^{∼−2}) = ∅, and an endpoint of such a bond in Ω^{∼−2} is outside Ω^𝐁_{j+1} = Ω^D_{j+1} there. Bonds of 𝐁 with no endpoint in Ω have no endpoint in Ω^D_{j+1} ⊂ Ω. So (R) holds.

### 51.4 Two Lemmas From Theorem 1 (Derived)

Lemma A (restriction). Let U be a critical configuration of the VAR problem on Ω₀ with the determining set 𝐁, in the class 𝔘(ε₀′) of 𝐁's domains. Let 𝐁^D be a determining set in Ω ⊂ Ω₀ with VAR's geometry (1), a layer of the scale 0 at ∂Ω, and (R), and with the scale of 𝐁^D at most that of 𝐁 at every point of Ω. Let the data V^D := M^{𝐁^D}(U) satisfy (7) at ε₁ with ε₁ ≤ a₁, B₃ε₁ ≤ ε₀ ≤ a₀, and ε₀ ≥ ε₀′. Then U|_Ω = U(𝐁^D, V^D), up to a gauge transformation of VAR (4).

Proof. Let δA be a variation on Ω with Q_{𝐁^D}(U)δA = 0. It vanishes on the scale-0 layer, so its support has no endpoint on ∂Ω, and by 51.3 Q_𝐁(U)δA = 0 for δA extended by 0. So δA is admissible for 𝐁 on Ω₀, and (178) for U gives ⟨δA, J(U)⟩ = 0. Every plaquette that meets the support of δA has a corner in Ω, so it is a plaquette of the Ω-problem, and the Ω-problem's current at the bonds of the support is J(U) there. So U|_Ω satisfies (178) for the Ω-problem at the data V^D. Its class: on Ω the plaquettes and the divergences of U|_Ω are those of U, since a plaquette at a bond of Ω has a corner in Ω; on a layer of 𝐁^D of the scale n ≤ the scale m of 𝐁 there, ε₀′L^{−2m} ≤ ε₀L^{−2n} and ε₀′L^{−2m}(L^mη)^{−1} ≤ ε₀L^{−2n}(L^nη)^{−1}. So U|_Ω ∈ 𝔘(ε₀) of 𝐁^D's domains, and it is critical there. By the uniqueness in Theorem 1 it lies on the minimal orbit. ∎

Lemma B (refinement). The same with Ω = Ω₀ and no boundary layer: if (R) holds, then U = U(𝐁^D, M^{𝐁^D}(U)) under the same class and data conditions. The proof is that of Lemma A without the boundary.

*The constants.* The members to which the lemmas apply lie in Theorem 1's class at their own data, 𝔘(B₃ε₁^o), with ε₁^o their data parameter. By VAR p.278 l.46, the data V^D of such a configuration satisfy (7) at ε₁ = C_Pε₀′, ε₀′ := B₃ε₁^o, with C_P the constant of Proposition 2 of [4]. The lemmas then need C_PB₃ε₁^o ≤ a₁ and ε₀ := max(C_P, 1)B₃²ε₁^o ≤ a₀, which hold for ε₁^o small, a condition of d and L on Bałaban's ε₁. The lemmas apply to Bałaban's localised sets 𝐁″_k(Y₁), 𝐁₁(Y₂), and 𝐁_k(Y₃), which are joins (2.14), and to 𝐁₁ and 𝐁₂ at the cut; VAR's geometry (1) for the joins is Bałaban's assertion (CRE p.256 l.49–53, as in 55.4).

### 51.5 Status

Derived here, not reviewed: 51.3 and 51.4. Quoted and checked: 51.1 and 51.2. The data condition (7) at U_2's junction with V″ at ∂Ω″^{∼2}_{h+1} is not given by LFR II p.370 l.22–23, which only takes "the corresponding functions"; it is open as in 55.4.

What this changes in the LF note (recorded here, not edited): the item on U(𝐁″_k(Y₁), D(s)) of its l.20 gets Lemma A as its tool; (1.54), (1.57), and the chain of pp.373–375 stand as printed.

## 52. The Localisation of LFR II pp.372–375

### 52.1 Source (Read)

LFR II pp.373–375: the chain for a first-part term 𝐄(X, U^0_k) with X ∩ Z ≠ ∅.
- Y₁ is the smallest domain of 𝐃_k containing X and the components of Z meeting X (p.373 l.15–16). (1.61) represents U^0_k as U(𝐁″_k(Y₁), M^·(U^0_k)), and Y₁ ∖ Y₁^0 is a boundary layer at ∂Y₁ of width at most 2M₁ (p.373 l.26–27). The data on that layer are written as the averages of U_1 twisted by the factors u^0_k and 𝐇″_k, which are those of (1.54) (p.370 l.41); the print does not cite (1.54) at (1.61).
- The localisation of 𝐇″_k with σ̃₀ gives a domain Y₂′ each component of which belongs to 𝐃_k, contains at least one component of Λ, and intersects the boundary layer (p.373 l.31–35), and terms depending on U_{1,2}|_{Y₂}, Y₂ = Y₁ ∪ Y₂′.
- (1.62) represents U_1 through 𝐁₁(Y₂) and (1.57), with 𝐇_{𝐁₁} small on Y₂ ∖ Y₂^0 (p.375 l.7–8). The localisation of 𝐇_{𝐁₁} gives Y₃′ and terms depending on U_{k,Λ}|_{Y₃} (p.374 l.8–11).
- (1.63) represents U_{k,Λ} through 𝐁_k(Y₃) and (1.58), with 𝐇_k(s(Y₄′)) small on (Y₃^0)^c ∩ Y₃ (p.374 l.41 to p.375 l.2). The localisation of 𝐇_k gives Y₄′ and terms depending on U_k|_{Y₄}, "the final localization" (p.374 l.26–30).
- The extended function U^0_k(𝐔, 𝐉) is built by substituting (1.63) into (1.62) and (1.62) into (1.61), with M^·(U_k), V″ replaced by M^·(𝐔) and V_Λ^{(A)} by V_Λ^{(A)}(M^k(𝐔)) (p.374 l.39–40). Its regularity on (Λ^∼)^c is "almost the same" as that of U(𝐁″_k(Y₁), M^·(𝐔)) (p.375 l.4, l.8, l.12–13); for (1.61) the print gives no reason beyond this statement. "On the domain Λ^∼ the regularity properties are similar to the properties of the configuration U_k″" (p.375 l.13–14).
- (1.65) states the analyticity of the extended function from Ũ^c_k(Y₄, α̃₀, α̃₁) into Ũ″^c_k(Y₁, α̃₀, α̃₁) (p.375 l.17–20). The print says it "has been proved already, in a slightly less general form, in the proof of the equality (1.89) [IV]" and does not repeat the proof (p.375 l.24–27); [IV] is LFR I, and (1.89) is at LFR I p.198.
- The print does not state where the boundary layer Y₁ ∖ Y₁^0 lies relative to Z. Its use of M^·(U_1) there implies that the layer lies where U_{1,2} = U_1.

### 52.2 Status

The chain of pp.373–375 and (1.65) are used as Bałaban's stated results, within their printed scope: (1.65) concerns the extended U^0_k, and the regularity of the intermediate representation configurations is only "almost the same" (p.375 l.4–13), as the LF note's l.20 records. The first equalities of (1.61)–(1.63) are the print's. Lemmas A and B (§51) apply to them only where their hypotheses are checked for U^0_k with 𝐁″_k(Y₁), U_1 with 𝐁₁(Y₂), and U_{k,Λ} with 𝐁_k(Y₃); that check is not made here.

Open, unchanged by this section: the conditions at U_{k,Λ}, U_1, and U_2 where §49 and §50 leave them open; the representation configuration U(𝐁″_k(Y₁), D(s)) at the decoupled data, for which the identity is not available at interior points of the line.

No change to the LF note follows from this section.

## 53. The Representation Configurations at Each Run's Own Members

### 53.1 The Items (Read)

The LF note's l.19 lists the near domains at ∂Y₁, ∂Y₂, ∂Y₃ for the representation configurations U(𝐁″_k(Y₁), ·), U(𝐁₁(Y₂), ·), U(𝐁_k(Y₃), ·), at ∂Ω″^∼_{h+1} for U_1 and U_2, and at ∂□₀ for the composites, where "c^A is not the local minimiser of its own data on □₀". Its l.20 lists the conditions of LFR I (1.64)–(1.69) at U_1, U_2, U_{k,Λ}, and U(𝐁″_k(Y₁), D(s)), with what closes it "a quantitative form of the two 'almost the same' statements at the halved thresholds" of LFR II p.375 l.1–10, and "the conditions at U_{1,2} for the first-stage expressions".

### 53.2 The Identities at Each Run's Own Members (Quoted)

Bałaban prints the first equalities of (1.61)–(1.63) (LFR II p.373 l.20, p.373 l.39, p.374 l.16):

U^0_k = U(𝐁″_k(Y₁), M^·(U^0_k)), U_1 = U(𝐁₁(Y₂), M^·(U_1)), U_{k,Λ} = U(𝐁_k(Y₃), M^·(U_{k,Λ})).

By CRE (2.14)–(2.15) (p.257 l.13–20) the joined sets are supported in Y_i, so the equalities are identities on Y_i, the second on Y₂ ∩ Ω″^∼_{h+1}, since 𝐁₁ is supported in Ω″^∼_{h+1} (p.370 l.22–23). Each holds up to a gauge transformation of VAR (4) for the joined set. They hold in each run at its own members on its own lattice, at real points with unlocalised 𝐇, and on the joint line at t = 0, where c(0) = c^B. They are used as Bałaban's stated results. Lemmas A and B of §51 are not needed for them, and the hypotheses of the lemmas for these joins are not checked here.

At t ≠ 0 the identities fail in general. c(1) = ι_Yc^A is not a minimiser of run B's problem (the LF note's l.13). Since run B's constraints factor through M and Mι_Yc^A = c^A on Y, the data of c(1) at the shared scales ≥ 1 are those of c^B. So U^B(𝐁″_k(Y₁), M^·(c(1))) takes c^B's data off the scale-0 strip at ∂Y₁ and the links of ι_Yc^A on it, and it is not c(1)|_{Y₁} when 𝐒_c ≠ 0 on Y₁. For U_1 and U_2 the joint line is not defined (the LF note's l.18 and l.459).

What 53.2 does not give (open):
- The defect U^B(𝐁^·(Y_i), M^·(c(t))) − c(t)|_{Y_i} at t ≠ 0.
- U_2 on Y₂∖Ω″^∼_{h+1}. (1.62) represents U_1 only; Bałaban says that a term "depends on the background field U_{1,2} restricted to Y₂" (p.373 l.34–35) but gives no representation of U_2 there. The conditions at U_2 are open.
- The two "almost the same" statements of p.375. They concern the extended functions of (𝐔, 𝐉), whose boundary-layer data carry the localised 𝐇(s(Y′)) of the expansions (6.10) (p.374 l.41 to p.375 l.2). The identities hold where the boundary-layer data are the member's averages, that is, at real points with unlocalised 𝐇. At localisation parameters ≠ 1 and at complex points the statements are not closed by them.
- The conditions at U_{1,2} for the first-stage expressions.

The conditions of (1.64)–(1.69) at the members: at U^0_k by the LF note's own derivation (its l.538 and l.567, through (1.65)); at U_{k,Λ} and U_1 on Λ^c at real points by §49.5, at (17/32)α̃′ and (9/16)α̃′, whose rooms ½ϖ(1 − θ) of the threshold suffice for the line's moves on the halved radius (49.5). On Y_i ∩ Λ and at complex points they are not derived here.

### 53.3 Status

Quoted and used as Bałaban's stated results: the identities of 53.2 at each run's own members, at real points with unlocalised 𝐇, and at t = 0 of the joint line.

Open:
- the defect of the identities at t ≠ 0 of the joint line, and the joint line for U_1 and U_2;
- the conditions at U_2, and at U_1 and U_{k,Λ} on Y_i ∩ Λ and at complex points;
- the two "almost the same" statements of p.375 at localisation parameters ≠ 1 and at complex points: the data D(s) differ from the members' averages by the s-localisation of 𝐇″_k, 𝐇_{𝐁₁}, and 𝐇_k on the boundary layers, at every t, and their bound is the smallness of 𝐇 there (p.375 l.2, l.7–8) with |s(Δ)| ≤ e^{κ₁}, not derived here;
- the near domains at ∂Y_i, at ∂Ω″^∼_{h+1}, and at ∂□₀ of l.19: a cube □₀ that meets ∂Y_i extends outside Y_i, where the representation configuration is not the member, and the join's scale-0 strip at ∂Y_i is finer than the cube's layers (57.3);
- the conditions at U_{1,2} for the first-stage expressions.

What this changes in the LF note (recorded here, not edited): at its l.20, the first equalities of (1.61)–(1.63) are identities at each run's own members and at t = 0, at real unlocalised data; l.19 is unchanged.

## 54. The Representation Configurations at Interior Points of the Line

### 54.1 The Setting (Read)

Along the joint line, the configuration read by a first-part term on Y_i is U(𝐁(Y_i), D(s)), with D(s) the data of the line's configuration c(s): the averages M^{𝐁(Y_i)}(c(s)) on Y_i^0, and on the boundary layer the twisted averages of the next member's line, with the localisation parameters of (6.10) [I] where the term carries them. At s = 0, c(0) = c^B and 53.2 applies. At s ≠ 0, c(s) = e^{i(ε/L)s𝐒}c^B in the LF note's form, with σ_c ≤ C(ε₀)d̄ at the real members (its *The Fine Side at the Multiscale Chain.*), and c(s) is not critical, so neither 53.2 nor Lemma A gives an identity.

### 54.2 The Conditions at D(s) (Open)

Write D(s) = D′(s)D(0) with D(0) the data at s = 0. The ratio D′(s) is G^c-valued, and its logarithm B(s) = (1/i)log D′(s) is 𝔤^c-valued. On a block of the layer j away from the boundary layer, a_j|B(s)| ≤ |s|C(ε₀)d̄. On the disc of the line, |s| ≤ 1/r(Y) with r(Y) = sup σ_c/ϱ (the LF note's l.459, l.542), so a_j|B(s)| is up to the room ϱ(x) there, not C(ε₀)d̄, up to the nonlinear correction.

Proposition 9 of VAR (p.309 l.8–13) gives U(𝐁(Y_i), D′(s)D(0)) as an analytic function of G^c-valued small ratios, with the condition (172), |D′ − 1| < C₁ε₁, and (7) at ε₁ for the base D(0), "for ε₁ sufficiently small" (p.305 l.31–36), with C₁ absolute (p.305 l.44) and ε₂ = B₅ε₁, B₅ = 6B₁B₃C₁ absolute ((173)). Four points are open:
- A bound linear in the ratio. (173) gives ε₂ proportional to the data parameter, not to the size of the ratio. A bound linear in the ratio follows from VAR (190) integrated along t ↦ tB: a_j|𝓗(x)| + a_j²|∇𝓗(x)| ≤ O(1)Σ_{y′}e^{−δ₀d(y,y′)/8}|B(y′)|, valid where Proposition 9 applies.
- The parameter of (172). With C₁ absolute, (172) holds at the enlarged parameter ε₁′ := max(ε₁, C(ε₀)C_U(M)ε₁/C₁) at real s, since C(ε₀)d̄ ≤ C(ε₀)C_U(M)ε₁; D(0) satisfies (7) at ε₁ ≤ ε₁′. B₅ stays absolute and ε₂ = B₅ε₁′ carries the factor C(ε₀)C_U(M)/C₁. Every smallness condition of VAR on ε₁ is then needed at ε₁′, which holds for γ small after M, since ε₁ = C(M)R_kε_k. That D(0) satisfies (7) at the required ε₁ is not given by the remark of VAR p.278 l.46–47, which gives (7) only "with ε₁ = O(ε₀)"; it is the data condition of the members, open where 51.5 and 53.3 leave it. On the complex disc, where a_j|B(s)| is up to ϱ(x), the enlarged parameter is of the size of ϱ, a fraction of the thresholds α̃′, and ε₂ = B₅ε₁′ is then not below the thresholds.
- The band term. On the boundary layer the ratio carries the localisation parameters of 𝐇, of the size |𝐇| there, not C(ε₀)d̄. 𝐇_k and 𝐇_{𝐁₁} have the bound h of 49.3; 𝐇″_k of (1.61) has no bound of that kind here.
- The comparison with the thresholds uniformly in k − m. ε₁/α_{0,m} carries max(1, (k − m)^{1/2}) by CRE (2.6), and (ε/a_j)^{(1−ε₀)/3} is about 1 on the finest layers, where k − m is largest. The decay device of 49.4 is absent, since the fine-side twist is not localised away from the points.

The Cauchy note's (T-Λ) (its l.38) uses VAR Sect. G with an M-dependent constant C₁ := max(1, C_X(M)C_Φ(M)/κ_Λ). Against p.305 l.44 this is read as the enlarged parameter of the second point: the M-dependent factor goes into ε₁′ with C₁ absolute, at the cost of a smallness condition on γ after M, and B₅ stays absolute (recorded here, not edited there).

### 54.3 The Near Domains at Interior Points (Open)

The near domains at ∂Y₁, ∂Y₂, ∂Y₃, and ∂Ω″^∼_{h+1} at interior points of the line are open with 57.3 and 53.3. Under R-data and the clause of 62.3 a near-domain term reads the composite U_n(□₀, M^·(·)) on □₀, so the item is the data condition of M^·(U(𝐁(Y_i), D(s))) on □₀, which needs 54.2.

### 54.4 Status

Open:
- the conditions at U(𝐁(Y_i), D(s)) along the line, with the four points of 54.2, including the data condition (7) of D(0) at the required ε₁ and the size of the ratio on the complex disc;
- the near domains at interior points (54.3).

§65 and §67 treat the first, the second, and the fourth point at real points, on Λ^c and inside Z respectively, and the band term; their status is recorded there. Complex points are not treated.

Derived here: the enlarged parameter ε₁′ of the second point at real s, with B₅ absolute.

What this changes in the LF note (recorded here, not edited): nothing; its l.16, l.19, and l.20 remain open at interior points.

## 55. The Readings Checked Against the Sources

This section gives the passages that settle the readings of §§39–54, and the source facts that §§49–51 use. The main consequence is at the cut: Bałaban's joins carry data down to the scale 0 at ∂Ω″^∼_{h+1}, so U_{1,2} has no first-order jump there.

### 55.1 R-data (Quoted at the Newest Scale; the Layer Form Is the Project's Adaptation)

- RG I p.275 l.2–13 and (3.24): the definition of the extension of the near-domain terms through U_{k+1}(□₀, M^·(𝐔)), with the composite's current.
- RG I (3.39), p.278 l.20–22: U_j(□₀, exp iQ(L^{−1}η𝐇_{k+1})) = U_j(□₀, M^·(exp iL^{−1}η𝐇_{k+1})^{v_j^{−1}}) = U_j(□₀, M^·(U_{k+1}(□₀, M^·(𝐔))))^{v_j^{−1}(ū_{k+1})^{−1}v^{−1}} = U_{k+1}(□₀, M^·(𝐔))^{(vū_{k+1}v_j)^{−1}}. The gauge factor sits on both sides of the last equality, and the gauge action is injective, so U_j(□₀, M^·(U_{k+1}(□₀, M^·(𝐔)))) = U_{k+1}(□₀, M^·(𝐔)). This is §44.2's feasible-set identity in print, at the newest scale k + 1.
- CRE p.280 l.18–19: "for the proof of Theorem 2 we put 𝐇_k(B′) = 0 in (I.3.28), or 𝐀 = 0 in (I.3.30), and we replace L^{−1}η𝐇_{k+1} by η𝐇_k". This is the specialisation B̃_□ = 0.
- CRE p.280 l.14–17: "(3.3), (3.18)–(3.28) [I]. They have a bit different meaning now, because the configuration U_k, or U_{k+1}, restricted to Ω_n∖Ω_{n+1} coincides with a U_n-type configuration, but the difference is seen in bounds only." l.19–20: "The function L^nηA, where A is defined by (I.3.30), satisfies the bound (I.3.32), but in the L^{−n}-scale instead of the η-scale".
- CRE p.283 l.48–49, in the second proof of Theorem 2, prints U_k = U_{j,□₀}(M^·(U_k)) at the lower scale j, at real U_k.

CRE keeps the formulas (I.3.18)–(I.3.28) and changes only the bounds. It does not print U_n(□₀, M^·(𝐔)) as the extended function of (3.24) in the variables (𝐔, 𝐉) at a layer n < k. The Cauchy note's l.124 says that "the literal U_k(□₀,·) doesn't work" at the layer and builds U_n(□₀, ·) itself. So (G.256) at the layer n is the project's adaptation of Bałaban's definition, taken as the project's definition of the near-domain terms at the entries. At the newest scale it is Bałaban's definition, and the specialisation B̃_□ = 0 is CRE's.

### 55.2 R-near (a Construction Choice)

- LFR II p.376 l.40–41: the re-summation into V(Y) "for 𝐄-terms and 𝐑-terms … includes renormalization in the form described in the proof of Theorem 2 in Sect. 2 [III]", and [III] is CRE (LFR II p.392 l.18).
- CRE p.283 l.10–23: the counterterm is split by (3.65) into A(h_z, U_k), and A(h_z, U_k) is analysed "in the same way as above". The leading part (3.66) cancels the right-hand side of (3.61), which states that (3.57), the quadratic leading part of the resummed (3.56), equals β′_j·½Σtr F².
- LFR II pp.371–377 apply (1.59) and (1.60) explicitly to the 𝐄-terms, the 𝐑-terms, and the boundary terms only. They do not say which identity is applied to −β_jA(φ_j, ·) or to its pieces A(h_z, ·).

Within a fixed Y₀ the cancellation needs the counterterm of z expanded together with the near-domain terms of z, that is, through (1.59) with σ₀ disjoint from □₀ and Λ^∼; with (1.60), σ₀ is disjoint from X (p.373 l.12–13), and the Y₀-sets of the counterterm and of the near terms differ. So R-near is a construction under which p.372 l.29–30 and p.376 l.40–41 hold. It is adopted as the definition of the procedure, identically in both runs, and §45.2's r^s_z = 0 rests on it.

### 55.3 R-65c (the Composite of the Print)

LFR II p.375 l.5–13 defines the extended U^0_k as the composite of the substitutions (1.63) → (1.62) → (1.61), and (1.65) asserts its analyticity on Ũ^c_k(Y₄, α̃₀, α̃₁). A composite defined on that space has each stage defined there with values in the domain of the next stage, so the stages are defined on the space, from the print. p.374 l.40–41 prints the analyticity of the extended (1.63) "with a large domain of analyticity", without naming that domain. The analyticity of the partial composite (1.62)∘(1.63) is not printed; it follows from the construction, each stage being built from 𝐇-functions, logarithms, and minimisers that are analytic where defined, and it is not used: §49 uses only definedness and no threshold regularity of the stages.

### 55.4 The Cut (Quoted)

- CRE p.256 l.57–63: for a domain Ω, 𝐁_j(Ω) is "a minimal determining set with a support in Ω", with nested domains Ω = Ω₀ ⊃ Ω₁ ⊃ … ⊃ Ω_j, Ω_n a union of L^nξM₁-cubes, and dist(Ω_n, Ω^c_{n−1}) ≥ L^nξM₁, on T_ξ with ξ = L^{−j}, the original lattice in the frame of the step j. Its outermost layer Ω₀∖Ω₁ has the scale 0, at which the data are the bond variables themselves (CRE p.255 l.12–16: Γ₀ = Ω₁^c, Γ_j = Ω_j^{(j)}∖Ω_{j+1}^{(j)}; M^0 the identity, as in CRE (2.2) and VAR's Λ₀).
- CRE p.257 l.13–16: the join (2.14) takes 𝐁_j(Ω) on the strip Ω∖Ω^{∼−2}, and dist(Ω_j, Ω^c) ≤ 2M₁ (p.256 l.62) places all of 𝐁_j(Ω)'s layers in that strip.
- LFR II p.370 l.18–33: 𝐁₁ and 𝐁₂ of (1.52) are such joins, and by (1.53) U_1 has the data 1 on Z″_k ∩ Ω″^∼_{h+1} and U_2 the data 1 on (Ω″^∼_{h+1})^c ∩ Ω″^{∼2}_{h+1}. p.370 l.37–38: "the arguments of the corresponding functions are equal to 1 on this domain", the domain (Ω″_{h+1})^c ∩ Ω″^{∼2}_{h+1}. The strip Ω″^∼_{h+1}∖(Ω″^∼_{h+1})^{∼−2}, of width 2M₁ in M₁-cubes of the frame h, lies in that domain, since the ∼-layers of Ω″ have the width LMR_{h+1} in the units of the scale h (the LF note's *The layers of 𝐁₁.*) and LMR_{h+1} ≥ 2M₁ for M ≥ 2M₁.
- The variational problem (CRE (2.12)) fixes M_𝐁(U) = V, and gauge transformations act with u = 1 on the data sites (VAR (4)). So U_1 = 1 and U_2 = 1 on their scale-0 bonds at the cut, each layer at least LM₁ original spacings thick, and the strips of the scales 1, …, h carry the averages 1.
- LFR I p.199 l.19–26 uses the same device in the proof of (1.89): "introducing the usual boundary conditions at the boundary ∂Ω″^{∼2}_{h+1} through the determining set 𝔹_h(Ω″^{∼2}_{h+1})", with the layer Σ "of thickness 2M₁ (in L^{−h}-scale)". l.34–41 bound the ℍ-function of the expansion in the jump on Σ by B₃exp(−δ(M/M₁)(j − h))exp(−½δMR_h)·23d²ε_h on the layers of Z″. That bound concerns another configuration, U″_{k,Z} localised at ∂Ω″^{∼2}_{h+1}, on domains at a scaled distance of order MR_h from Σ. It shows the same decay mechanism in print; it is not a bound on U_1 or U_2.

Consequences:
- U_{1,2} = 1 on the scale-0 bonds of the two strips at the cut, so it has no first-order jump there (50.3). Bałaban's statement of p.370 l.35–38, "regularity conditions typical for an h-order configuration", stands as his statement; it carries no constants, and no bound at the cut is taken from it.
- Lemmas A and B of 51.4 apply to Bałaban's localised sets 𝐁″_k(Y₁), 𝐁₁(Y₂), and 𝐁_k(Y₃), which are joins by (2.14) and carry the scale-0 strips at ∂Y_i (LFR II p.373 l.17, l.26–27, l.36, p.374 l.13), where their hypotheses are checked (53.2). VAR's geometric condition (1) for the joins is 58.3's: Bałaban applies VAR's theory to them (CRE p.256 l.49–53, p.257 l.11–21), and the layers of 𝐁_j(Ω) satisfy it with R = L, which needs L ≥ R₁.
- R-VAR-h is Bałaban's statement: CRE p.256 l.43–53 introduces U_𝐁(V) for his determining sets as the minimal configuration of (2.12), "For precise definitions and the theory of this variational problem see [15] … we will use all the results of [15]", with [15] = VAR, and p.257 l.17–21 gives the joins their function (2.15).
- The data condition (7) at the junctions. It is not stated by p.370 l.22–23 ("take the corresponding functions"). On the Λ side its source is LFR I (1.83)–(1.84), |M^j(U_0) − 1| < O(1)B₃B₅M⁶ε_k inside Λ in the axial gauge (p.197 l.4–14), so the junction with the value 1 is regular. U_1's junction of V″ with M^k(U_0^{(AL)}) is bounded through M^k(U_0) = V_Λ and (1.78) (59.3). At U_2's junction with V″ at ∂Ω″^{∼2}_{h+1}, (7) needs the data in a gauge close to 1 there, which is not shown: open.

### 55.5 Source Facts for §§49–50

- Thresholds. The prefactor of (1.64) and (1.68) is ϖ > 1 − 4β = ½ at the project's choice β = 1/8 (LFR I p.190 l.25, p.191 l.7); for (1.68) it is > 1 − 2β = ¾, and ½ is used for both. β = 1/8 meets Bałaban's conditions: 0 < β ≤ ½ in (1.24) (p.182 l.17–18), whose "but not too small" is not quantified, and β ≤ ¼ with L₀² ≤ L/3 for the descending spaces (p.191 l.35, p.198 l.16), with 2 ≤ L₀ < ½L (p.182 l.18), so L ≥ 12. The comparison of the moves with the thresholds, including the thresholds of (1.66)–(1.67) on (Ω_m ∖ Ω_{m+1}) ∩ X for k₀ < m ≤ j, which are not restricted to Z, is 49.4's.
- Along the line (49.5). With the real-point values below (1 + θ)·½ϖ·T, the room is ½ϖ(1 − θ)T > ½·½·(15/16)T = (15/64)T, and on the halved radius each line move is at most ⅛T by the Schwarz lemma, so the line keeps the conditions on |t| ≤ 1/(2r(Y)). Cauchy's estimate on the halved radius costs a factor 2 in the variation, which the LF note's constants absorb (recorded here, not edited).
- The current of the configuration. VAR Theorem 1 places a minimal configuration of data satisfying (7) at ε₁ in 𝔘_k({Ω_j}, B₃ε₁), whose condition (2) gives |𝕁| = η^{−2}|D*∂U| < B₃ε₁(L^mη)^{−3} on the layer m, with the single constant ε₁ on all layers. The target at α̃′/2 is ϖα_{0,m}/(8B₃)(L^mη)^{−3}, so the ratio is at most 16B₃²ε₁/α_{0,m}, and by CRE (2.6), g_k/g_m ≤ (1 + g_k²β′(k − m))^{1/2}, this upper bound is not small on the layers with k − m large. So Theorem 1's class does not give the current at the thresholds of the fine layers; §59 gives a layer-adapted bound at real points.
- The source of the 𝐇_{𝐁₁} bound (49.3). VAR applies at U_{k,Λ} directly at real data, since U_{k,Λ} = U_k(V″⌈_{Λ^c}, V_Λ^{(A)}) is a minimiser of regular data and "(1.84) [IV] is satisfied for it" (LFR II p.371 l.32–33).
- G-valuedness of u_{k,Λ} and u_1 at real data. LFR II p.373 l.29–30 cites (106) [12] for the gauge transformations, and [12] is CMP 98 (LFR II p.392 l.28). CMP 98 (105)–(106), p.033 l.43–45, write u as a product of the adjoint actions R(U₀(Γ))^{−1} of parallel transports and of exp[iΣL^{−d}(1/i)log(…)] of contour variables. At G-valued configurations near 1 every factor is G-valued, for a general compact G.
- The covariant derivative. The |∇𝐇| of the h-bound is the covariant derivative in the untwisted background, as in LFR I (1.45), p.186 l.11.
- Quotations. The p.373 quotation continues ", and the new terms of 𝐑^{(k)}, which will be obtained by the ℝ-operation" (l.7–8); "R_k ≤ L(log g_k^{−2})^r" is a consequence of CRE (2.5), which defines R_j as the smallest power of L that is at least (log g_j^{−2})^r, not its text.

### 55.6 Status

Quoted and checked: the newest-scale form and the specialisation of 55.1, and the sources of 55.4. A construction choice: R-near (55.2). The project's adaptation: the layer form of R-data (55.1). From the print: R-65c, as definedness of the stages (55.3). Derived: the consequences of 55.4 for the cut, and the source facts of 55.5.

Open:
- (7) at U_2's junction with V″ at ∂Ω″^{∼2}_{h+1} (55.4);
- the factor 2 of the halved radius in the LF note's constants (recorded here, not edited);
- the items listed in the status subsections of §§49–54 and §§56–58.

### 55.7 The Older Readings of §§39–41 (Checked)

- R-𝐁 (derived). CRE (2.40)–(2.41), p.261 l.47–57, is the inductive assumption for 𝐁_k: every term of 𝐁^{(j)}, j ≤ k, has a localisation domain X ∈ 𝐃_j with X ∩ Ω_j ≠ ∅ and X ∩ Z_j^∼ ≠ ∅, and p.262 l.24–25 adds that "the expressions with indices j<k are exactly as described above". The assumption holds for the density after the k-th ℝT (p.262 l.22–23), by CRE's Theorem 1, completed in LFR II p.392 l.5–6. So at step k every term of 𝐁_k meets Z_j^∼ for the domains of step k, and the D2.6 closure's Z_j^∼ ⊆ Ω_{j+1}^c ⊆ Λ_{k+1}^c (its l.61, from (G1)) gives R-𝐁. The closure's residual item, that the re-expansion keeps a localisation domain containing the old one, is not needed.
- R-fr(a) (an emendation of a print slip). CRE p.267 l.42 performs "the scaling transformation A′_k = g_kA_k", so A_k in (3.16) is the Gaussian variable, and the printed (3.16) (p.268 l.18) cuts it at δ_k. LFR II p.380 l.43–47 states that the complement χ^{(j−1)c}(R_j) of (3.16) "yields the factor exp(−γ₀g_j^{−2}δ_j²(LM₂R_j)^{−d}|R_j|), by the same positivity bound for the quadratic form"; the factor g_j^{−2} requires the cut at g_j|A_j| = δ_j, and with the printed threshold the factor would be exp(−γ₀δ_j²…), which is not small. So the printed δ_k in (3.16) is a slip for δ_k/g_k on the Gaussian variable, |A′| < δ_k in the field variable, as (3.3) and (3.14) use δ_k for the field (p.267 l.22–23), and as the project's TRANSCRIPTION_FINDINGS.md l.191–196 records for CRE (3.16) and LFR I (1.55). Here δ_k = g_k(A₁/A₀)p₀(g_k) = (A₁/A₀)ε_k (p.265 l.39, p.255 l.33).
- R-fr (Bałaban's, accepted). p.277's "estimated as in (2.42), but with the additional factor O(ε_k)" on the support of the integration is presented as true and presupposed by his cluster expansion of (3.27) and (3.29) (pp.277–278); it is used as his statement.
- R-m (Bałaban's). CRE p.277 l.3–8, used as his statement; the comparison of its constants is in READINGS_RECHECK row 9.
- (R-m′) (an admissible choice). CRE p.259 l.47–50 leaves q₀ and q₁ free ("integers greater than 1", C₀ and C₁ "sufficiently large"). The transcribed uses of q₀ and q₁ (CRE, LFR I, LFR II, RG I, RG II, PRT1, PRT2, CMP 98) are CRE p.259 l.47–50, LFR II p.368 l.26–27, and LFR II p.379 l.31. LFR II p.379 l.31, read literally, bounds α_{1,k} by a constant times α_{0,k} up to the factor M^dR_k^{d+2}/|𝐁₀|, an upper bound on q₁ relative to q₀; RG I p.277 l.54 requires B₃²O(1)Mα₀ < ½α₁, a lower bound; and LFR II (1.47), p.368, is "small under the usual conditions on N" (l.31), with L^{−N} ≤ (log g_k^{−2})^{−ν} for ν large (p.363 l.39), ν chosen after q₁. So the choice q₁ = q₀ > p₀ + r of (T-Λ), with C₁ large relative to MC₀, satisfies every printed condition.
- R-L3. A repair of the proof of RG2 Lemma 3, whose (1.28) and (2.30) fail at single cubes: RG I p.257 l.14–15 defines d_j(X) as the length of a shortest tree meeting all cubes, divided by M, so one cube has d = 0, and M^{−4}|Y| ≤ 3·2³d_k(Y) fails. The repair, with d + 1 and C₃′, is derived in READINGS_RECHECK row 27 and D2.4, not in this section.
- R-vac(ii-bd) (derived in §41). §41 derives it at the creation integral, at amplitude ε̄₂, from RG2 Lemma 3 with R-L3 and p.277's activity bound; §41 does not use it as an input.

Readings: none remain in §§39–55. One printed formula is used in emended form, CRE (3.16) in R-fr(a). Bałaban's statements used as presented: R-fr, R-m, the re-expansion of pp.275–277, and (1.65).

What this changes in the D2.6 closure (recorded here, not edited): its "Reading R-𝐁 (labelled, for review)" is derived by the first item. Its "Reading R-vac(ii-bd) (logged, for review)" is replaced by the weaker derived form of §41, not closed in its original form: the amplitude is ε̄₂, only polylog-small under (R-m′), in place of O(ε_k), and the form is stated at the creation integral, before the later T/R propagation. Both the amplitude and the KP weight need replay at the callers of D2.6 §2.4.

## 56. The Fine Side at the Cut

### 56.1 The Two Runs' Collars (Derived From CRE p.256 l.57–60)

CRE p.256 l.57–60 builds 𝐁_j(Ω) from "a sequence of maximal domains Ω = Ω₀ ⊃ Ω₁ ⊃ … ⊃ Ω_j such that Ω_n is a union of L^nξM₁-cubes, and dist(Ω_n, Ω^c_{n−1}) ≥ L^nξM₁", ξ = L^{−j}, on T_ξ. Run A's collar at the cut is 𝐁_h(Ω), Ω = Ω″^∼_{h+1}, on its lattice of spacing ε, and run B's is 𝐁_{h+1}(Ω) on its lattice of spacing ε/L, since run B reaches the same physical scale one step later. In physical units write c_n := L^nM₁ε. Run A's Ω_n is then a maximal union of c_n-cubes at distance ≥ c_n from Ω^c_{n−1}, and run B's Ω_{n+1} is a maximal union of c_n-cubes at distance ≥ c_n from its Ω_n, with run B's Ω₁ a maximal union of c₀-cubes at distance ≥ c₀ from Ω^c. Ω is a union of M₁-cubes of the scale h, so its boundary lies on every one of these grids. Measured as the depth below ∂Ω, the maximal domains begin at the smallest multiple of c_n that is at least the previous depth plus c_n:

- run A: Ω₁ at depth c₁, and Ω_n at depth 2c_n for n ≥ 2, since c₁ + c₂ ≤ 2c₂ and 2c_{n−1} + c_n ≤ 2c_n for L ≥ 2;
- run B: Ω₁ at depth c₀, Ω₂ at depth 2c₁, and Ω_{n+1} at depth 2c_n for n ≥ 1, by the same two inequalities.

A one-dimensional check of these depths for L = 2, 3, 4, 8 and M₁ = 1, 5, up to n = 6, agrees. So run B's layer n + 1 and run A's layer n have the same blocks (of side L^nε) and, at depths ≥ 2c₁, the same domains. The collars differ in two places only:

- (d1) on the depths [0, c₀), run B fixes its fine bonds (its scale 0), where run A fixes its bonds of length ε;
- (d2) on the depths [c₁, 2c₁), run B fixes the averages of the ε-blocks (its scale 1), where run A fixes only the averages of the Lε-blocks (its scale 1).

On [c₀, c₁) run A fixes its ε-bonds and run B the averages of its ε-blocks, which are the same constraint under M. So run A's scale-0 strip is L times wider than run B's in physical units, with the same number LM₁ of bonds across it. The same holds for 𝐁₂ with Ω = (Ω″^∼_{h+1})^c. Both differences lie within the physical distance 2c₁ = 2LM₁ε of the cut.

### 56.2 The Patch Is a Minimal Configuration, and Its Run-B Partner (Derived)

- The combined set. In each run let 𝐁_{1,2} be 𝐁₁ on Ω″^∼_{h+1} together with 𝐁₂ on its complement, with the data of U_1 and U_2. Both joins carry the scale 0 at the cut (51.2), so 𝐁_{1,2} has a band of scale-0 bonds around the cut, on which the data are 1, and its other layers are those of the two joins. Every plaquette that crosses the cut, or lies in the band, has all its bonds in the band. So on the configurations with M_{𝐁_{1,2}}(U) = V the action is the action of the plaquettes of Ω″^∼_{h+1} off the band, plus that of its complement off the band, plus a constant. The two parts depend on disjoint sets of free bonds, and the gauge transformations act with u = 1 on the data sites (VAR (4)). So the minimal orbit of (2.12) for 𝐁_{1,2} is the product of those of 𝐁₁ and 𝐁₂, and U_{1,2} is the minimal configuration U_{𝐁_{1,2}}(V), in each run. The layers of 𝐁_{1,2} are those of the two joins with the two scale-0 strips merged into one band (2LM₁ bonds across in each run), so the widths of the LF note's *The layers of 𝐁₁.* and *The layers of 𝐁₂.* apply.
- Run B's partner. Let 𝐁^♭ be run A's 𝐁^A_{1,2} on run B's lattice, run A's scale n as run B's scale n + 1: the band becomes a layer of ε-blocks, and every layer is at a shared scale ≥ 1. On the whole lattice an empty scale-0 layer satisfies VAR p.277 (1), since Ω₀ = Ω₁ and Ω₀^c = ∅; this is the case of the LF note's members (*The joint line.*). Its other widths are run A's. Let c^♭ := U_{𝐁^♭}(V^B) be the minimal configuration of run B's action at run B's data V^B of U^B_{1,2} on the blocks of 𝐁^♭, which are 1 on the band. The data that contain the block averages of U_0, M^k(U_0^{(AL)}) on Λ ∩ Ω″_k, differ between the runs (the LF note's l.7, l.230, and l.437), so (U^A_{1,2}, c^♭) is a pair of the LF note's kind with the data difference of its §4(c), as for the members: the two sets coincide at the shared scales, and run B's constraints at c^♭ factor through M, so c^♭ = ι(Mc^♭).
- Run B's patch. By 56.1, applied on both sides of the cut, 𝐁^B_{1,2} refines 𝐁^♭ on S := (d1) ∪ (d2) and coincides with it elsewhere. On (d1) run B fixes the fine bonds where 𝐁^♭ fixes ε-block averages, and on (d2) it fixes the ε-block averages where 𝐁^♭ fixes Lε-block averages. c^♭ lies in VAR's class for 𝐁^B_{1,2}, since its lower layer index on S makes the conditions of VAR (2) weaker there, and by Lemma B of 51.4 it is the minimal configuration of 𝐁^B_{1,2} at its own averages V₀ := M_{𝐁^B_{1,2}}(c^♭). V₀ satisfies (7) at the parameter C_PB₃ε₁ of 51.4. Off S these averages are V^B, the data of U^B_{1,2}, and on S the data of U^B_{1,2} are 1. The gauge representative of c^♭ on the fine sites of (d1), which are not data sites of 𝐁^♭, is fixed by the axial gauge within the blocks of S (61.5). So by VAR Proposition 9,
  U^B_{1,2} = (exp iη𝓗(B)c^♭)^{u^{−1}}, B := (1/i)log V₀^{−1} on S, and B := 0 elsewhere.

### 56.3 The Size of B (From 61.5)

LFR II p.370 l.35–38: "the arguments of the corresponding functions are equal to 1 on this domain", the domain (Ω″_{h+1})^c ∩ Ω″^{∼2}_{h+1}, which contains the cut with the margins LMR_{h+1} on each side in the units of the scale h (the LF note's *The layers of 𝐁₁.*). The data of c^♭ are 1 there too.

61.5 bounds B: c^♭'s plaquettes on S are bounded by §59's F, which falls by the factor λ across each collar layer and margin (61.2), and REG Lemma 1 ((1.25), |V′ − 1| < 4d²α₀ + α₁ in the axial gauge (1.24)) turns them into bondwise bounds in the axial gauge within the blocks of S. So

|B| ≤ C_Bε₁λ^{2(h−1)₊} bondwise on S,  C_B := 16d²B₃,  λ := 2^{−(s₁−1)/2} ≤ L^{−3} under (W-3) (61.2).

V′ := exp(iB) on S, 1 elsewhere, satisfies (172) with VAR's absolute C₁ at the parameter ε₁′ := max(ε₁, C_Bε₁/C₁), as in 54.2; B₅ stays absolute.

### 56.4 The Fine Side at U_{1,2} (Derived Away From the Collar Thresholds)

- The pair. By 56.2, (U^A_{1,2}, c^♭) is a pair of minimal configurations of the same multiscale set at shared scales ≥ 1, at data that differ by §4(c)'s data difference, with layers at least LM₁ wide in their own units (56.1, and §46's (G.265) for the middle layers of 𝐁″_k). These are the properties of the members that the LF note's *The Fine Side at the Multiscale Chain.* uses, besides the profile of its (b) and (J-W), which hold at these layers. So ι_YU^A_{1,2} = e^{i(ε/L)𝐒^♭}c^♭ on Y, with a_{j(x)}|𝐒^♭(x)| + a_{j(x)}²|∇𝐒^♭(x)| ≤ C(ε₀)d̄(x), the data difference included as at the members.
- The data change. VAR (190) bounds δ𝓗(x)/δB(y′) by O(1)(L^{j′}η)^{−d}e^{−⅛δ₀d(y,y′)} (p.308 l.37–47). Summing over y′ ∈ S with half the rate, and using the other half, less a further half, for the layer-scale factors, the field η𝓗(B) of 56.2 obeys
  a_{j(x)}|(L/ε)η𝓗(B)(x)| + a_{j(x)}²|∇(L/ε)η𝓗(B)(x)| ≤ σ^{cut}(x) := C_{cut}ε₁λ^{2(h−1)₊}e^{−κd(x, S)},  κ := δ₀/32,
  with C_{cut} := O(1)·2C_Bc_κL^{7/3}, under the width condition
  (W-δ): κLM₁ ≥ (7/3)log L, that is, δ₀LM₁ ≥ 75 log L,
  which absorbs the layer-scale factors as in the LF note's *The weights.* (W-δ) is a lower bound on M₁ after d, L, and δ₀, compatible with (W-3) and (M-V) (61.2), and fixed before γ.
- The difference. By the Baker–Campbell–Hausdorff formula, as in the LF note's *The bound.*, ι_YU^A_{1,2} = e^{i(ε/L)𝐒_c}U^B_{1,2} on Y, in the gauge of U^B_{1,2}, with a_{j(x)}|𝐒_c(x)| + a_{j(x)}²|∇𝐒_c(x)| ≤ 2(C(ε₀)d̄(x) + σ^{cut}(x)) for γ small; the change of the covariant background from c^♭ to U^B_{1,2} is a commutator term of the same order.
- Against d̄. Put ℓ₁ := (s₁ − 1)log 2/(2 log L), so that λ² = L^{−2ℓ₁}, ℓ₂ := κLM₁/log L, and ℓ_* := min{ℓ₁, ℓ₂}. (W-3) gives ℓ₁ ≥ 3, and (W-δ) gives ℓ₂ ≥ 7/3. For x in a layer j ≤ h, λ^{2(h−1)₊} ≤ L^{2ℓ_*}(ε/a_h)^{2ℓ_*} ≤ L^{2ℓ_*}(ε/a_j)^{ℓ_*}. For x in a layer j > h, a path from S to x also crosses the layers h, …, j − 1, each at least LM₁ wide, so e^{−κd(x,S)} ≤ L^{−ℓ_*(j−h)}, and the two factors together are ≤ L^{2ℓ_*}(ε/a_j)^{ℓ_*}. Since d̄(x) ≥ C_U(M)(ε/a_{j(x)})^{(1−ε₀)/3}ε₁ (the LF note's l.461) and ℓ_* ≥ 7/3 > 1/3,
  σ^{cut}(x) ≤ C_{cut}L^{2ℓ_*}C_U(M)^{−1}d̄(x).
  So σ_c ≤ C̃(ε₀)d̄ at U_{1,2}, with C̃(ε₀) := 2C(ε₀) + 2C_{cut}L^{2ℓ_*}C_U(M)^{−1}, a constant of d, L, M₁, M, R, and δ₀, independent of k, h, the layer, the volume, and ε, and fixed before γ.
- The lift condition away from the collar. The LF note's *The lift condition of (i).* uses the move σ_c and the plaquettes, cube-gauge fields, and currents of the run-B configuration, at points x of a layer m ≥ j read by a term of the generation j at the thresholds of the scale j (its l.470 and l.476). At the points of U^B_{1,2} outside the collar layers this holds as at the members, with C̃(ε₀) for C(ε₀).
- The lift condition at the collar (open). The collar layers 0, …, h − 1 of 𝐁_{1,2} lie within 2c_h of the cut, in the history layer h (*The layers of 𝐁₁.* and *The layers of 𝐁₂.*). Terms of the generations up to h read these points of 𝐁_{1,2}-layers m < j, where the factor L^{j−m} works against the radius. At u = 0 the configuration's own conditions hold there at the thresholds of the layer h, by 61.2 under (W-3). The move σ_c at a collar point is bounded in the normalisation of its layer m, and its conversion to the layer h costs up to L^{2(h−m)}, which d̄'s factor (ε/a_m)^{(1−ε₀)/3} does not pay. A bound on 𝐒_c at the collar in the normalisation of the layer h, from the flatness of both runs' configurations near the band, is what the lift condition there needs.

### 56.5 r_z at U_{1,2} (Reduced; Open at the Data Change)

§§45 and 47 use the one-step identity ι(Mc^B) = c^B at the run-B configuration. At the pair of 56.4 it holds exactly, c^♭ = ι(Mc^♭) (56.2). At run B's own configuration U^B_{1,2} it fails, since the fine constraints on (d1) do not factor through M; U^B_{1,2} is the data change of c^♭ by η𝓗(B). So r_z at c^♭ is the r_z item at the members, with C̃(ε₀) for C(ε₀), and the effect of the data change on r_z, through the moment defect and the lift change ℓ_X, is not derived here.

### 56.6 The Current at U_{1,2}

The current part of the joint line moves the current of U_{1,2} by ΔJ := Q₁^{pl}(ι_YU^A_{1,2})*J(U^A_{1,2}) − J(U^B_{1,2}) = ΔJ^♭ + (J(c^♭) − J(U^B_{1,2})), where ΔJ^♭ := Q₁^{pl}(ι_YU^A_{1,2})*J(U^A_{1,2}) − J(c^♭).

- ΔJ^♭. The pair (U^A_{1,2}, c^♭) has the properties that the LF note's *The Current at the Multiscale Chain.* uses: both are minimal configurations of their multiscale sets in 𝒟̄, with the multiplier representation of its (d), and run B's constraints at c^♭ factor through M (56.2). Its weights (LW₀) and (LW) need layers wider than W with ¼δ₀W ≥ log L, which holds at W = LM₁ under (W-δ). The second term of its ΔJ_c uses the fine side ι_YU^A_{1,2} = e^{i(ε/L)𝐒^♭}c^♭ of 56.4. So a_{j(x)}³|ΔJ^♭(x)| ≤ Ĉ_Jd̄(x).
- The data change. c^♭ and U^B_{1,2} are minimal configurations of the same set 𝐁^B_{1,2} (56.2), so the multiplier computation of that paragraph, its (I) and (II), compares them along the line t ↦ (exp iη𝓗(tB)c^♭)^{u_t^{−1}}, t ∈ [0, 1], the line of minimal configurations of Proposition 9. Here the field η𝓗(tB) replaces εA_c, and σ^{cut} replaces d̄. (III) is absent, since both configurations belong to run B. (I) and (II) use only the bounds of the field and of its covariant derivative, which 56.4 gives, and the weight property (LW), which holds for σ^{cut} with any rate κ ≤ ¼δ₀: σ^{cut}(p)e^{−κd(p,x)} ≤ σ^{cut}(x) for every p, since d(p, S) + d(p, x) ≥ d(x, S). The intermediate current and its divergence condition hold as there, with D*J = 0 at both configurations. So a_{j(x)}³|J(c^♭)(x) − J(U^B_{1,2})(x)| ≤ x̂_Jσ^{cut}(x) ≤ x̂_JC_{cut}L^{2ℓ_*}C_U(M)^{−1}d̄(x), with x̂_J of that paragraph.
- The bound. a_{j(x)}³|ΔJ(x)| ≤ Ĉ_J^{1,2}d̄(x), with Ĉ_J^{1,2} := Ĉ_J + x̂_JC_{cut}L^{2ℓ_*}C_U(M)^{−1}, in the normalisation of the layer of x.
- At u = 0. At the collar points the current of U^B_{1,2} is below the thresholds of the layer h with the ratio θ_J, by 61.2 under (W-3); on the configurations' own layers away from the collar it is §59's layer-adapted bound at real points (§60 for U_2). VAR Theorem 1's class alone does not give it (58.2).
- The current part. Away from the collar, the LF note's *The current part.* applies at U_{1,2} as at the members, with Ĉ_J^{1,2} for Ĉ_J and C̃(ε₀) for C(ε₀), and bounds the current part at U_{1,2} by 4r_J(Y) times the bound of f, with r_J(Y) ≤ 4(1 + β₀)Ĉ_J^{1,2}max_{x∈Y}d̄(x)/α_{j(x)}. At the collar points the move ΔJ is bounded in the normalisation of the layer m and the thresholds are those of the layer h, so the current part there has the open item of the collar lift condition (56.4).
- At complex points. The members' *At complex points.* and *The current part at complex points.* use the fine side at complex points and the room at complex points, both open in the LF note (*The Fine Side at Complex Points.*, *The room at complex points (open).*). 56.2 and 56.4 hold at complex data, since c^♭, B, and 𝓗(B) are analytic in the data by Proposition 9; 56.3's bound is derived at real data (61.5, through §59's F), and its extension to the disc of (7) is part of the open complex-point item of 59.5.

### 56.7 Status

Derived here, not reviewed in this form: 56.1, 56.2, the fine side and the lift condition away from the collar (56.4), and the current move ΔJ (56.6), at real points.

Premises:
- quoted: CRE p.256 l.57–60, (2.12), and (2.14); LFR II p.370 l.35–38;
- Bałaban's results used as presented: VAR p.277 (1), (2), (4), (7), (9)–(10), Theorem 1, Proposition 9, (172), (190), and the current J of p.305; REG Lemma 1; LFR I (1.64)–(1.69);
- from this note: Lemma B (51.4), 51.2, 54.2's enlarged parameter, §46's (G.265), 61.2, 61.5, §59, §60;
- from the LF note: *The Fine Side at the Multiscale Chain.*, *The Current at the Multiscale Chain.*, and *The lift condition of (i).* (derived, unreviewed);
- the width conditions (W-3), (W-δ), and (M-V), lower bounds on M₁ before γ.

Open:
- the lift condition and the current part at the collar points, in the normalisation of the layer h (56.4, 56.6);
- the effect of the data change η𝓗(B) on r_z (56.5);
- complex points, with the LF note's open items on the fine side and the room there and 59.5's item;
- (5.1c) on the near domains that meet the cut, which §62 treats at real points under (N) and 63.4 where (N) fails, with their status recorded there.

What this changes in the LF note (recorded here, not edited): in the U_{1,2} part of its l.18 and l.421, the entries, the lifts, and the commutator are replaced by the pair (U^A_{1,2}, c^♭) and the data change of 56.2; the fine side, the lift condition, and the current hold away from the collar at real points; the collar points and r_z at the data change stay open. The separate item of l.18 and l.421, (i) at the decoupled configurations of (1.60), is not a U_{1,2} item and is unchanged.

## 57. The Glued Member

This section states the configuration a near-domain term reads under R-data and what stays open at the boundaries of minimisation domains.

### 57.1 The Term Reads the Glued Configuration

Let 𝐔 be a configuration of the class at which a near-domain term 𝐄^{(j)}(X, ·, z), X ⊂ □^{∼2}, is read: a member U_1, U_2, or U_{k,Λ}, another representation configuration of (1.61)–(1.63), a composite, or an entry c(t). Under R-data the term is 𝐄^{(j)}(X, P_n𝐔), with P_n𝐔 = U_n(□₀, M^·(𝐔)) on □₀ and 𝐔 outside (RG I p.275 l.1–5, "the configuration U_{k+1} is replaced by the configuration U_{k+1}(□₀, M^·(𝐔)), extended as equal to 𝐔 outside □₀"; the layer form is the project's definition, 55.1).
- The data of U_n(□₀, ·) are the averages M^p(𝐔), p ≤ n, on the shells of □₀ ⊃ □₁ ⊃ ⋯ ⊃ □_n, and on the outer shell □₀ ∖ □₁ the bond variables themselves (RG I (1.15), p.262 l.41–50; p.276 l.36; REG (1.5)). The outer shell is a layer of width more than RM₁ (REG (1.4)), not a single layer of bonds.
- P_n𝐔 exists and is analytic in 𝐔 on RG I's space U′^c_{k+1}(□₀, (1 + 2β)α₀, (1 + 2β)α₁): the conditions (i)–(iii) on the whole lattice and (iv) on □₀ (RG I p.275 l.19–21; p.273 l.39–40). RG I Lemma 4 ((3.53), p.280), at 𝐀 = 0 and B′ = 0, places the pair (P_n𝐔, J_n(□₀, M^·(𝐔))) restricted to X in U^c_j(X, α₀, α₁). This is membership on X, not class membership of the glued configuration on the whole lattice.
- The term is not the term at the global minimiser W of 𝐔's determining-set data. W shares with 𝐔 only the averages of the layer's scale, so M^p(W) ≠ M^p(𝐔) on the shells for p < n in general, and P_n𝐔 = W on □₀ holds exactly when the cube data of 𝐔 on □₀ coincide with W's. On the outer shell P_n𝐔 = 𝐔 up to gauge, while W is a minimiser there.
- Bałaban's statement on this configuration is qualitative: "U_{k+1}(□₀, M^·(𝐔)) has approximately the same regularity properties as 𝐔, hence all necessary theorems are valid for operations with this configuration" (RG I p.275 l.6–7). It does not by itself give the age factor of (5.1c).

A quadratic model on the sites 0, …, 5 with the action Σ(u_{i+1} − u_i)² and the block averages on {0, 1}, {2, 3}, {4, 5} shows that they differ in general: the move u₁ ↦ u₁ + η, u₀ ↦ u₀ − η leaves every block average, and so W, unchanged, and it moves the local minimiser of the cube data (u₁ and u₄ fixed, u₂ + u₃ fixed) by η/6. So the term at 𝐔 is not the term at W, and the glued configuration is what the term reads.

The glued configuration at the entry c(t) is

Ŵ_z(t) := P_nc(t) on □₀, c(t) outside □₀.

A near X has X^∼ ⊂ □̃³ ⊂ □₀ (the Cauchy note's l.116), and M^·U_n(□₀, 𝐕) = 𝐕 on the constrained bonds (its l.124), so the near-domain term at c(t) is the term at Ŵ_z(t) exactly. Under the clause of 62.3 the counterterm of z and its pieces c_X read the same composite, so the near part of irr_j at c(t) is the near part at Ŵ_z(t) with zero counterterm mismatch, which is how §44 uses it; the marginal mismatch of the LF note's l.527 arises only when the counterterm reads c(t) itself, which the clause excludes. The far-domain part is §45's. On the outer shell the cube data are c(t)'s bond variables, so in the representative of the G^c-gauge class that is 1 at the data sites, P_nc(t) = c(t) there, and Ŵ_z(t) has no seam at ∂□₀.

At t = 1, run B's cube data of ι_Yc^A on □₀ agree with M^·(c^A) at the scales ≥ 1, since Mι = id there; on the outer shell they are the bond variables of ι_Yc^A. So the term at ι_Yc^A is the term at the run-B composite of those data, and its identification with a function of M^·(c^A) alone needs the equality at the finest level, which is not shown here.

### 57.3 The Near Domains at the Boundaries of Minimisation Domains (Open)

At the minimisers on Y_i or on Ω″^∼_{h+1} whose domain boundary crosses □₀, 𝐔 is not the local minimiser of its cube data, and P_n𝐔 is not a small move of 𝐔 or of a member. RG I's output conditions hold on □̃³ (p.277 l.55, "satisfying the conditions (i), (ii) on the cube □̃³, hence on X") for 𝐔 in Lemma 4's space, which gives (a) on the near domains. (b) on □₀ ∖ □̃³, fields and current, is not derived. The item of the LF note's l.19 is open in this form: the bounds (2.34)–(2.39) of P_n𝐔 on □₀, 𝐔 outside, on □₀ ∖ □̃³, at each such configuration, or an age-carrying bound on 𝐄^{(j)}(X, P_n𝐔) − 𝐄^{(j)}(X, W_𝐔). (i) at these configurations depends on the same item: (5.1v) is stated at the runs' minimisers, and the equality of the two runs' cube data at the finest level is not shown. §62 treats the cut at real points under (N), 63.4 the points where (N) fails, and 64.3 the endpoints at real points; their status is recorded there. The boundaries ∂Y_i at interior points of the line are not treated by them.

### 57.4 Further Points

- σ_c in (G.259) is the supremum over the region the term reads. The absorption uses σ_c ≤ C(ε₀)(a_k/ε)^{ε₀}d̄ with its factor L^{kε₀}, which §44.7 absorbs through the LF note's l.563 exponent (1 − 25ε₀)/3. The first term of (G.260) needs α_m ≥ ε_m, which holds by CRE (2.28) and (2.4), since α_{0,m}/ε_m = C₀(log g_m^{−2})^{q₀}/p₀(g_m) and q₁ ≥ q₀ > p₀ (R-m′), uniformly in m for γ small.
- K_M's gradient part a_p²|∇𝐒_c| is not needed for Lemma 4, which takes the data shift in the sup norm (p.279 l.48–49, "|B′| < α₃"), and §44.7 uses the sup part only.
- irr_j is per point: the whole counterterm of z with the sum over X ∋ z, as in the Cauchy note's l.104 and l.108. B₃ is Bałaban's constant of [15] (RG I p.260 l.37), fixed with d and L, not absolute. (I.5.42) is on RG I p.297.
- The (iv) and (α) identities of the LF note read run B's terms at lifted configurations. Under R-data a near term reads only the cube data on □₀. At the scales ≥ 1 these are equal for ι_{Y_X}𝐔 and 𝐔, since Mι_{Y_X}𝐔 = 𝐔; at the finest level they are the bond variables of ι_{Y_X}𝐔. So the bracket of the identity vanishes given the equality at the finest level, as at t = 1 in 57.1; §70 treats the group.
- Citations: CRE p.255's Λ_j = Ω_j is at l.2–3; M₂ = L²M₁ is Bałaban's "e.g." (CRE p.245 l.37), and M > M₁ suffices for 46.3; CRE p.280 l.19 concerns "the function L^nηA".

### 57.5 Status

Derived here, not reviewed in this form: the term at c(t) is the term at Ŵ_z(t) for the near domains, with the counterterm under the clause of 62.3 (57.1). Quoted and checked: 57.1's sources, RG I p.262, p.273, p.275, p.276, and p.280, and REG (1.4)–(1.5). Premises: R-data (55.1) and the clause of 62.3. The membership of Ŵ_z(t) in 𝒮_z is not an input: 64.5 bounds irr_j at the entry c(t) itself.

Open:
- the equality of the two runs' cube data at the finest level, for the term at t = 1 and for the (iv) and (α) identities;
- the l.19 item of 57.3 at the boundaries ∂Y_i and ∂Ω″^∼_{h+1}, with (i) at those configurations, where §§62–64 do not treat it.

What this changes in the LF note (recorded here, not edited): point (3) of (LF-A) is bounded at the entry c(t) by 64.5 (§44), not through the membership of Ŵ_z(t); its l.19 item keeps its content in the form of 57.3.

## 58. The Current, the Junctions, and the State of §56

§§49–54 carry the cut, the identities of (1.61)–(1.63), and the interior points of the line in their present form. This section gives what they use from elsewhere: the source of the junction condition (7), the choice β = 1/8, the current at real points, the geometry of Bałaban's joins for Lemmas A and B, and the state of §56.

### 58.1 The Cut and the Junctions

- The cut. 51.2 needs the whole strip Ω″^∼_{h+1} ∖ (Ω″^∼_{h+1})^{∼−2} inside Z″_k, where (1.53) assigns the data 1. Bałaban's p.370 l.37–38, "the arguments of the corresponding functions are equal to 1 on this domain", states it, with his "∼" for the cubes of Ω″ and CRE's "∼−2" for M₁-cubes (CRE p.256 l.62–63); the inclusion of the strip in his domain (Ω″_{h+1})^c ∩ Ω″^{∼2}_{h+1} is his statement. That U_1 = U_2 = 1 on the scale-0 bonds of the strips follows from the data on the scale-0 part being the bond variables (CRE (2.2), (2.10)–(2.11)), as in 50.3. Bałaban's sentence "It is so, because …" is his justification of the regularity, used under the rule for his stated results and not as a derivation.
- No size bound at the cut is used. Bałaban's "regularity conditions typical for an h-order configuration" is not quantified, and LFR I p.199 l.19–41 bounds the ℍ-function of another configuration, U″_{k,Z}, at a distance of order MR_h from Σ.
- (7) at the junctions. On the Λ side the source is LFR I (1.83)–(1.84), |M^j(U_0) − 1| < O(1)B₃B₅M⁶ε_k inside Λ in the axial gauge (p.197 l.4–14). (7) at U_2's junction with V″ at ∂Ω″^{∼2}_{h+1} needs a gauge in which V″ is near 1 bondwise there, which is not shown (open).
- β = 1/8 is the note's choice within Bałaban's β ≤ 1/4 (LFR I p.191 l.35, p.198 l.16). With ϖ > 1 − 4β = ½ the room at real points is ½ϖ(1 − θ)T > (15/64)T for θ ≤ 1/16, which covers the move ⅛T of the line on the halved radius 1/(2r(Y)) (49.5).

### 58.2 The Current at Real Points

VAR Theorem 1's class 𝔘_k({Ω_j}, B₃ε₁) has one constant ε₁ = C(M)R_kε_k on all layers, while the threshold of the layer m is α_{0,m} ∝ g_m(log g_m^{−2})^{q₀}. By CRE (2.6), g_k/g_m ≤ (1 + β₀)max(1, (k − m)^{1/2}), so the ratio B₃ε₁/α_{0,m} is bounded by a multiple of max(1, (k − m)^{1/2})θ_k, θ_k as in 49.4, and on Λ^c the difference k − m is not bounded. So Theorem 1's class does not give the current at the thresholds of the fine layers, and a layer-adapted bound is needed. §59 derives one at real points from VAR §F's local proof; its status is recorded there. The current at complex points is not treated in §§58–59 (open).

### 58.3 The Joins in Lemmas A and B

The lemmas of §51 hold up to a VAR (4) gauge transformation. Criticality is (178), stated for the minimal configuration, which suffices since the minimal orbit is unique. Bałaban calls the join (2.14) "a new determining set" and gives it its minimal function (2.15) (CRE p.257 l.11–21), with the theory of VAR, "we will use all the results of [15]" (p.256 l.49–53). The layers of 𝐁_j(Ω) satisfy dist(Ω_n, Ω^c_{n−1}) ≥ L^nξM₁ (p.256 l.60–61), which is VAR's (1) with R = L in the units of the scale n − 1, so VAR applies to them for L ≥ R₁. VAR's (1) across the junction of 𝐁 and 𝐁_j(Ω), at the distance 2M₁ of (2.14), is used as Bałaban's application of VAR's theory to his joins. The data condition of the lemmas is 51.4's, with ε₁ ≤ a₁ and B₃ε₁ ≤ ε₀ ≤ a₀ at the enlarged parameter of 54.2 where the data are twisted.

### 58.4 The State of §56

The bullet "At u = 0" of 56.6 used a current argument from Theorem 1's class, and the conditions at U_2 in 56.6 rested on a representation of U_2 that 53.2 does not give. So the U_{1,2} item is not closed. Derived and unreviewed in §56: the collars of 56.1; the minimal-configuration property and the partner c^♭ of 56.2; the size of B of 56.3, derived in 61.5; the fine side of 56.4; r_z of 56.5; the current move ΔJ of 56.6.

### 58.5 Status

Open:
- the current at complex points, at U_{k,Λ}, U_1, U_2, and U_{1,2};
- (7) at U_2's junction with V″;
- the conditions (1.64)–(1.69) at U_2;
- the interior points of the line (54.4) and the near domains of 57.3 at D(s) and at the composites' far terms.

Treated elsewhere, with their status recorded there: the current at real points on the fine layers (§§59–60); the conditions at U_2 on its own layers and at the strips at the cut (§60, 61.2–61.4); the band term and the layer-uniform threshold comparison of 54.2 at real points (§§65, 67) and at complex points (68.1–68.5); 57.3 (64.3, 67.4, 68.4–68.5, §70).

Used as Bałaban's stated results: the data 1 on the strips at the cut and his regularity statement of p.370; his application of VAR's theory to the joins (2.14). From the print: R-65c (55.3), whose scope is that of 49.6.

What this changes in the LF note (recorded here, not edited): its l.18 U_{1,2} item stays open in the form of 58.5; its l.19 item is 57.3; its l.20 item is open at D(s), at U_2, and at complex points, and at U_{k,Λ} and U_1 on Λ^c at real points it is derived by §49 given the current of §59.

## 59. The Current on the Fine Layers at Real Points

This section treats the first item of 58.4 at real points. VAR proves its regularity bounds cube by cube, from the data near the cube and an a-priori bound near it. Run with bounds that vary from layer to layer, the same proof gives in the layer n a bound of the size R_nε_n, since Bałaban's history data have the bound O(L²)ε_m in the layer m. The current in the layer n is then of the size R_nε_n(L^nη)^{−3}, and its ratio to α_{0,n} is small uniformly in k − n. Notation: η = L^{−k}; the layer n is Ω_n∖Ω_{n+1}; the current of a configuration is J = η^{−2}Im D*∂U (VAR (170)), as in 55.5.

### 59.1 The Sources (Read)

- VAR (2), p.278 l.2–8: 𝔘_k({Ω_j}, ε₀) is defined by |∂U(p) − 1| < ε₀η²(L^jη)^{−2} and |(D*∂U)(b)| < ε₀η²(L^jη)^{−3} on Ω_j. The second condition is the current bound |J| < ε₀(L^jη)^{−3}. VAR (7), p.278 l.35–45, bounds the data plaquettes, with V̄ in place of V on the bonds of a junction plaquette outside Λ_j.
- VAR §F, pp.300–305. For a unit cube Δ₀ = B^j(y) ⊂ B^j(Λ_j) (p.302 l.44–47) the proof of (2) uses two inputs:
  - U satisfies (2) with ε₀ on □̃, where dist(□, □̃^c) = 2R₁M₁L^jη and □̃ ⊂ B^{j−1}(Λ_{j−1}) ∪ B^j(Λ_j) (p.300 l.36–37);
  - the data plaquettes meeting □_k satisfy (7) with ε₁ (p.303 l.11–12 and (160)).

  The local problem (148)–(151) lives on □̃. (152) is its bound there, and the outside part of (161) carries e^{−½δ₀R₁M₁}ε₀. The output is (2) on Δ₀ with max{B₃ε₁, ½ε₀} (p.304 l.33–43). B₃ of (162) depends on d and L only, and the smallness conditions on ε₀ are those of (166). The step is repeated "until we reach the bound B₃ε₁" (p.304 l.42–43). Proposition 8 states the result for every critical configuration.
- CRE p.256 l.26–30: V_{j−1} is defined on the bonds of Ω_j^{(j−1)c}, "and we assume that the field V_{j−1} is regular on Γ_{j−1} in the sense that |∂V_{j−1} − 1| < O(L²)ε_{j−1}". RG I p.251 l.26–28: a set determines the bonds and the plaquettes "which intersect it". CRE (2.21), p.258: 𝐓^{(j)} integrates V_j on Ω_{j+1}^c with δ(V̄_jV_{j+1}^{−1}).
- CRE (2.4)–(2.9) and (2.28): ε_j = g_jA₀(log g_j^{−2})^{p₀}, α_{0,j} = g_jC₀(log g_j^{−2})^{q₀}. For n > m: ε_n ≤ (1 + β₀)(n − m)^{1/2}ε_m, ε_m ≤ (1 + β₀)²(n − m)^{β₀}ε_n, R_n ≤ LR_m, and R_m ≤ (L + 1)(n − m)^{β₀}R_n.
- CRE p.276 l.9–11: "Other bounds involve regularity properties of the configuration U_{k+1} on a neighborhood of Ω_n∖Ω_{n+1}, and these are the same as for U_n-configurations, i.e. they are characterized by the scale L^{−n}." 59.2 derives this statement from VAR's proof.
- LFR I p.177 l.17–33: Z is the union of a class of connected components of Λ_k^c. LFR I (1.73): Λ = (Ω_{k₀+1}^{∼4})^c ∩ Z. LFR I Proposition 1 and (1.78), p.194: for V_k⌈_{Z∩Λ^c} with |∂V_k − 1| < ε on Z ∩ Λ^c, the minimiser V_Λ = V_Λ(V_k⌈_{Z∩Λ^c}) of (1.77) satisfies |V_Λ(∂p′) − 1| < B₅M⁵ε for p′ ∈ Λ. LFR I (1.84), p.197 l.10–15, is a bound on U_0 in the axial gauge in k-blocks; (1.87), p.197 l.31–36, gives U_0^{u_0} = U_0^{(AL)} = exp iη𝔸₀ inside Λ with |𝔸₀| < O(1)B₃²B₅M⁶ε_k on Z″_k, and Z″_k = (Ω^{∼5}_{k₀+1})^c ∩ Z ⊂ Λ (p.192 l.41). p.193 l.23: V_k has |∂V_k − 1| < 2L(L + 1)N₀^{−1}R_kε_k on Ω″_k.

### 59.2 The Bound in Each Layer (Derived From VAR's Proof)

Let U be a critical configuration of VAR (5) in the space (6) with ε₀ ≤ a₅, for data V satisfying (7) with ε₁ ≤ a₁. Let e(p′) := |(∂V)(p′) − 1| for each data plaquette p′. The step of §F uses only the two local inputs of 59.1, and every smallness condition it imposes holds a fortiori for smaller bounds. So for any function E on the unit cubes such that U satisfies (2) on each Δ₀ with E(Δ₀), it gives (2) on Δ₀ with

(TE)(Δ₀) := max{B₃ sup_{p′ meets □_k(Δ₀)} e(p′), ½ sup_{Δ₀′ meets □̃(Δ₀)} E(Δ₀′)}.

Here the (2)-bounds of the cubes of the layers j − 1 and j in □̃ are compared in their own layers' normalisations, as at p.300 l.39–40. For this map:
- Chain distance. Let ρ(Δ₀, p′) := 0 if p′ meets □_k(Δ₀), and otherwise 1 + min ρ(Δ₀′, p′) over the cubes Δ₀′ meeting □̃(Δ₀).
- The function F. Put F(Δ₀) := B₃ sup_{p′} e(p′)2^{−ρ(Δ₀,p′)}. Then TF ≤ F, since ρ(Δ₀, p′) ≤ ρ(Δ₀′, p′) + 1 when Δ₀′ meets □̃(Δ₀).
- The iteration. T is monotone, and T max{F, c} ≤ max{F, ½c}. Starting from VAR Theorem 1's uniform bound B₃ε₁, the iterates fall below F after finitely many steps, since the lattice is finite, when some e(p′) > 0. When every e(p′) = 0 the iterates tend to 0, and the conclusion holds in the limit.

So U satisfies (2) on each Δ₀ with F(Δ₀). For Δ₀ in the layer j, □̃(Δ₀) lies in the layers j − 1 and j (p.300 l.36–37), and its boundary can touch the layers j − 2 and j + 1. So a cube Δ₀′ meeting □̃(Δ₀) lies within two layers of Δ₀, and a data plaquette meeting □_k(Δ₀) lies within two layers of Δ₀. Hence, for Δ₀ in the layer n and p′ in the layer i,

ρ(Δ₀, p′) ≥ ½|i − n| − 1.

### 59.3 The Data in Each Layer (Derived From the Print)

At Bałaban's background U_k every data plaquette of the layer i < k has e(p′) ≤ O(L²)ε_i.
- For the plaquettes inside Γ_i this is CRE p.256 l.26–30, an assumption of Bałaban's inductive representation ("we assume"), used as he presents it. In the R-operation the determining set is 𝔅″_k with the domains Γ″_j (LFR I p.194 l.12–13); the new restrictions change the bound by at most the logarithmic factors of LFR I p.192 l.16–22, which are of the form C·R_i and are absorbed in C_e below.
- A junction plaquette of Γ_i carries V̄ on its bonds outside Λ_i (VAR (7)). By CRE (2.21), V̄ = V_i there. So the plaquette is a plaquette of V_i that intersects Γ_i, and by RG I's convention (p.251 l.26–28, through CRE p.255 l.20) CRE p.256 l.26–30 covers it.

In the layer k, e ≤ 2L(L + 1)N₀^{−1}R_kε_k ≤ 2L(L + 1)R_kε_k on Ω″_k (LFR I p.193 l.23–24).

At U_{k,Λ} and U_1 the data outside Z are the same history data. Inside Z every datum of these two configurations lies on the layer k or equals 1:
- U_{k,Λ} = U_k(V″⌈_{Λ^c}, V_Λ^{(A)}) (LFR II (1.56)). Its data on Z are V_Λ^{(A)} on Λ, a field of the scale k (LFR I (1.83), b ⊂ Λ^{(k)}), and V_k on Z ∖ Λ ⊂ Ω″_k (49.4), also of the scale k. V_Λ is the minimiser V_Λ(V_k⌈_{Z∩Λ^c}) of (1.77), and V_k has |∂V_k − 1| < 2L(L + 1)N₀^{−1}R_kε_k on Z ∩ Λ^c ⊂ Ω″_k (p.193 l.23). So by (1.78), |V_Λ(∂p′) − 1| < 2B₅M⁵L(L + 1)N₀^{−1}R_kε_k for p′ ∈ Λ, which by RG I's convention includes the plaquettes that intersect Λ, with V_k on their outside bonds (LFR I p.195 l.5). The gauge transformation (A) acts at the points of Λ and is 1 outside, so every data plaquette of V_Λ^{(A)} ∪ V_k is a conjugate of one of V_Λ ∪ V_k, the junction at ∂Λ included. So e ≤ 2B₅M⁵L(L + 1)R_kε_k on the layer k.
- U_1 (LFR II (1.53)). Its data on Z are M^k(U_0^{(AL)}) on Λ ∩ Ω″_k, of the scale k, the value 1 on Z″_k ∩ Ω″^∼_{h+1}, and V″ = V_k on Z ∖ Λ as above.
  - On Λ ∩ Ω″_k. Averages are gauge covariant, M^k(U^u) = (M^kU)^{u′} with u′ the restriction of u to the block sites, and M^k(U_0) = V_Λ (LFR I p.197 l.3). So every data plaquette of M^k(U_0^{(AL)}) ∪ V_k is a conjugate of one of V_Λ ∪ V_k, and the bound of the previous item applies: e ≤ 2B₅M⁵L(L + 1)R_kε_k, the junction of Λ ∩ Ω″_k with Z ∖ Λ included.
  - At the junctions with the value 1 whose Λ bonds lie in Z″_k (if any data bond of Λ ∩ Ω″_k lies in Z″_k). The data there are bondwise within O(1)B₃²B₅M⁶ε_k of 1 in the gauge (AL) ((1.87): the average of exp iη𝔸₀ over a k-block bond in Z″_k), and the average of the value 1 over a block bond is 1. A plaquette is a product of at most four such factors, so e ≤ 4O(1)B₃²B₅M⁶ε_k there; the estimate |∏g_i − 1| ≤ Σ|g_i − 1| holds for any compact G in a unitary representation.
  - At the junctions with the value 1 whose Λ bonds lie in the shell Λ ∖ Z″_k, the edges at ∂Z included. (1.87) does not apply there, and the junction with the fixed datum 1 is not gauge invariant. 61.6 bounds them by e ≤ 7O(1)B₃²B₅M⁶ε_k; this bound is an input from 61.6, with the status recorded there.

Write C_e for the largest of these constants, C_e := C(L, M, B₃, B₅), using N₀^{−1} ≤ 1 and the logarithmic factors of the first item.

### 59.4 The Current (Derived)

Let U be U_k, U_{k,Λ}, or U_1, and let x be a point of the layer n of U's determining set. A datum of the layer i has ρ ≥ ½|i − n| − 1 (59.2), and by (2.8)–(2.9) with 2β₀ ≤ ½, R_iε_i ≤ (L + 1)(1 + β₀)²(|i − n| + 1)^{1/2}R_nε_n. Since 2^{−m/2}(m + 1)^{1/2} ≤ 1 for every integer m ≥ 0, F(x) ≤ 2B₃C_e(L + 1)(1 + β₀)²R_nε_n. Where x is controlled by a cube of an adjacent layer n ± 1, the same count gives ρ ≥ ½|i − n| − 3/2, so F ≤ 2√2B₃C_e(L + 1)(1 + β₀)²R_nε_n in the normalisation of that layer, which is at most L³ times the layer-n normalisation for J and L² for the plaquettes.

Hence U satisfies (2) at x with C_FR_nε_n, C_F := 4L³B₃C_e(L + 1)(1 + β₀)², and

|J(x)| ≤ C_FR_nε_n(L^nη)^{−3},  |∂U − 1| ≤ C_FR_nε_nη²(L^nη)^{−2}.

The targets at α̃′/2 of the current and of the plaquettes are ϖα_{0,n}/(8B₃(1 + β₀)) times their scale factors, with ϖ > ½ (49.4). The ratio is therefore at most

θ_J := 16(1 + β₀)B₃C_FL(A₀/C₀)(log ḡ^{−2})^{p₀+r−q₀},  ḡ := max_jg_j,

by ε_n/α_{0,n} = (A₀/C₀)(log g_n^{−2})^{p₀−q₀} (CRE (2.4), (2.28)), R_n ≤ L(log g_n^{−2})^r (a consequence of CRE (2.5); here r is its exponent), and log g_n^{−2} ≥ log ḡ^{−2}. C_F is fixed with d, L, M, B₃, B₅, and β₀ before ḡ. θ_J is uniform in n, k, k − n, and the volume, and θ_J ≤ θ for ḡ small, given q₀ > p₀ + r, the γ note's (T-Λ) choice (55.7), a choice within CRE p.259 l.47–50, which asks only that q₀ and q₁ be integers greater than 1. So the current condition (2.36) and the plaquette condition (2.34) hold with the ratio θ_J on the configuration's own layers.

### 59.5 Status

Derived here, not reviewed in this form: the bound in each layer (59.2), as a consequence of VAR §F's proof; the data bounds in each layer (59.3); the current and the plaquette conditions with the ratio θ_J at every point of the lattice, on the configuration's own layers, at U_k, U_{k,Λ}, and U_1, at real points.

Premises: CRE p.256 l.26–30, the regularity of the history data, an assumption of Bałaban's inductive representation, used as he presents it; LFR I (1.77)–(1.78), (1.83), (1.87), and p.193 l.23–24; 61.6 for the shell junctions of U_1; 49.4 for Z ∖ Λ ⊂ Ω″_k; (M-V) of 61.1 for VAR's (1) and the two-layer property of □̃ at the joins; the targets of 49.4 and the (T-Λ) choice q₀ > p₀ + r (55.7). The weakest step is the shell-junction bound of 61.6.

Treated elsewhere, with their status recorded there: U_2 and U_{1,2} (§60); the conversion to coarser layers on the collar strips at the cut (61.2); the block variables at D(s) (67.3–67.4).

Open:
- the current at complex points, at the members and at Ŵ_z(t): VAR (190), whose fourth and fifth entries bound D*D and Δ of δ𝓗/δB with the decay e^{−δ₀d(y,y′)/8} for complex B satisfying (172), and REG (1.54) (CMP 99 p.85), which expands D*∂(U₁U₀) in a background U₀ as D*∂U₀ + iη²D*_{U₀}D_{U₀}A plus explicit remainders, supply the second differences, but writing the complex configuration in the form (i)–(iii) of CRE p.261 and checking (2.36) there is not done here (§68 treats it);
- (2.35) and (2.37), the block variables, at the configurations of 57.1 (57.3's item); at the configurations of 61.2 they hold on all of X (60.4, 61.4).

What this changes in the LF note (recorded here, not edited): its current item at real points holds at U_k, U_{k,Λ}, and U_1 with the ratio θ_J, uniformly in the layer, given 61.6; at U_2 and U_{1,2} with §60.

## 60. U_2 and U_{1,2} at Real Points

U_2 lives inside Z, and the terms read it on Y₂ ∩ (Ω″^∼_{h+1})^c. Its one new feature is the junction at ∂Ω″^{∼2}_{h+1}, where its data change from 1 to V_h. That junction is regular not by a gauge choice but by Bałaban's characteristic function χ_{h,1/2}, a factor of the integral (1.49), which bounds the plaquettes of the local configuration with exactly these mixed data. With (7) in hand, §59 applies to U_2 on all of its layers. The strips of the two collars at the cut, where the terms' layer h is coarser than the collars' layers, are treated in 61.2–61.4: §59's gauge-invariant bound falls across each collar layer once the layers are wide in VAR's cube unit, without a field bound.

### 60.1 The Sources (Read)

- LFR II (1.52)–(1.53), p.370 l.18–33: 𝐁₂ = 𝐁″_k ∪ 𝐁_h((Ω″^∼_{h+1})^c), and U_2 = U_{𝐁₂}(1⌈_{(Ω″^∼_{h+1})^c ∩ Ω″^{∼2}_{h+1}}, V″⌈_{(Ω″^{∼2}_{h+1})^c}), supported in (Ω″^∼_{h+1})^c. p.371 l.27: U_{1,2} restricted to Z^c equals U_1; by (1.53), (Ω″^∼_{h+1})^c ⊂ Z. p.373 l.31–35: a term of the expansion depends on U_{1,2} restricted to Y₂ = Y₁ ∪ Y′₂, each component of Y′₂ containing a component of Λ.
- LFR II (1.49), p.369: χ_{h,1/2} is a factor of the integrand. LFR I (1.88), p.197 l.39–47, and p.198 l.1–7: χ_{h,1/2}(P^c) is the product over the LM₂R_h-cubes □ ⊂ (Ω″^∼_{h+1})^c ∩ Ω_h of χ({sup_{p⊂□^∼}|U_{h,□}((1, V_h), ∂p) − 1| < ½ε_h(L^{k−h}η)²}), with (1, V_h) := (1⌈_{Ω″^{∼2}_{h+1}}, V_h⌈_{(Ω″^{∼2}_{h+1})^c}). The components with P ≠ ∅ "have new large fields" and are excluded from Z; on the remaining components, which form Z, the function χ_{h,1/2} stands. For a cube inside Ω″^{∼2}_{h+1} not touching its boundary U_{h,□}(1, V_h) = 1, so the product runs over the cubes intersecting (Ω″^{∼2}_{h+1})^c and contained in Ω_h.
- LFR I (1.90), p.198 l.26–29: U_{h,□}(V) = U(𝔹_h(□^{∼4}), M^·(Q_h^{s*}V)). p.198 l.33–34: V″ = V_h on (Ω″^{∼2}_{h+1})^c ∩ □^{∼4}. p.179 l.32–36: Ω″_j = Ω_j for j ≤ h. Also (L^{k−h}η)² = η²(L^hη)^{−2}.
- LFR I (1.3), p.178: on Z, for □ ⊂ (Ω^{∼4}_j ∖ Ω^∼_{j+1}) ∩ Z, sup_{p⊂□^∼}|U_{j,□}(V_j, ∂p) − 1| < ε_j(L^{k−j}η)².
- VAR (7), p.278 l.35–45, and p.278 l.46–47: a non-empty space (6) with ε₀ small gives (7) for V with ε₁ = O(ε₀), "by Proposition 2 [4]". CMP 98 Proposition 2, p.26: if |U(∂p) − 1| < α₀η² with α₀ ≤ c₂, then |Ū^k(∂p) − 1| < α₀ + 2C₀α₀² < 2α₀ for p ⊂ Ω^{(k)}, and "the result is local": for p = ⟨x, y, z, w⟩ the hypothesis on B^k(x) ∪ B^k(y) ∪ B^k(z) ∪ B^k(w) suffices.
- VAR (167)–(169), pp.304–305: the bounds (9)–(10) on a cube □ of the class come from the local step with Δ = □, (167) reading |A|, |∇A|, |∂*∂A|, |ΔA| < ¼M_Δmax{B₃ε₁, ½ε₀} + ⅛M′ε₀, with the inputs (2) on the neighbourhood and (7) near □, as in 59.1.
- VAR (190), p.308: the decay is exp(−⅛δ₀d(y, y′)), with d the distance of PRT2 (2.46), which counts each layer in its own lattice units.
- LFR II p.370 l.35–38: U_{1,2} "satisfies the regularity conditions typical for an h-order configuration on the domain (Ω″_{h+1})^c ∩ Ω″^{∼2}_{h+1}", because "the arguments of the corresponding functions are equal to 1 on this domain, and the exponential decay properties enforce the additional regularity".

### 60.2 The Geometry (Derived From the Print)

- U_2's domain is the core (Ω″^∼_{h+1})^c of Z. 𝐁₂ is the collar 𝐁_h((Ω″^∼_{h+1})^c) on the strip within 2M₁ of the cut, in the units of the scale h, and 𝐁″_k elsewhere (CRE (2.14), 55.4).
- The band (Ω″^∼_{h+1})^c ∩ Ω″^{∼2}_{h+1} and the junction ∂Ω″^{∼2}_{h+1} lie in the layer h of 𝐁″_k: Ω″_h = Ω_h, ∼ enlarges by LMR_{h+1} in the units of the scale h (56.3), and dist(Ω″_{h+1}, Ω_h^c) ≥ 8LMR_{h+1} (§46.2). The junction is at the distance LMR_{h+1} − 2M₁ from the strip, in those units.
- U_2's data are 1 on the collar and on the band, V_h on the layer h outside Ω″^{∼2}_{h+1}, and U″_k's data V″_j on the layers j < h. U_2 has no datum of the level ε_k.

### 60.3 (7) at U_2 (Derived)

Let e(p′) := |(∂V)(p′) − 1| as in 59.2. The data plaquettes of 𝐁₂ are of three kinds.
- Plaquettes all of whose bonds carry 1, on the collar, on the band, and at their junctions: e = 0.
- History plaquettes of 𝐁″_k on (Ω″^{∼2}_{h+1})^c, the junctions between consecutive layers included: e ≤ C_eR_jε_j on the layer j, by 59.3, and inside Z also by (1.3) with CMP 98 Proposition 2.
- The junction plaquettes at ∂Ω″^{∼2}_{h+1}: scale-h plaquettes p′ whose bonds inside Ω″^{∼2}_{h+1} carry 1 and whose bonds outside carry V_h. Let □ be a cube of (1.88) containing a block of p′ outside Ω″^{∼2}_{h+1}. It is one of the cubes of the product, and the four blocks of p′ lie in □^∼, which extends beyond □ by at least one cube of the partition. Put U := U_{h,□}(1, V_h). Its data on the layer h of 𝔹_h(□^{∼4}) are M^h(Q_h^{s*}(1, V_h)) = (1, V_h), so (∂V)(p′) = (M^h(U))(∂p′), the product of U's scale-h averages around p′. The factor χ_{h,1/2} gives |U(∂p) − 1| < ½ε_hη²(L^hη)^{−2} on □^∼. By CMP 98 Proposition 2 at the scale h, with α₀ = ½ε_h ≤ c₂, e(p′) < ε_h.

Hence U_2's data satisfy (7) with e ≤ C_eR_iε_i on every layer i of 𝐁₂, and ε₁ := C_e max_iR_iε_i ≤ C_eA₀Lḡ(log ḡ^{−2})^{p₀+r} ≤ a₁ for ḡ small, since g(log g^{−2})^{p₀+r} increases with g. VAR Theorem 1 applies to 𝐁₂ as Bałaban applies it to his joins (CRE p.256 l.49–53, 55.4); the print does not state VAR's (1) for them (59.5). The gauge of V_h plays no part: (∂V)(p′) is the product of the data around p′, and its distance from 1 is that of the plaquette of U's averages. This closes "(7) at U_2's junction with V″" of 58.1 and 58.4.

### 60.4 The Conditions at U_2 and U_{1,2} on Their Own Layers (Derived)

- Plaquettes and current. By 59.2–59.4 with 𝐁₂'s layers, at every point x of the layer n of 𝐁₂, |∂U_2 − 1| ≤ C_FR_nε_nη²(L^nη)^{−2} and |J(U_2)(x)| ≤ C_FR_nε_n(L^nη)^{−3}, with the ratio θ_J to the thresholds of the layer n, small for ḡ small given q₀ > p₀ + r ((T-Λ), 55.7).
- The cube-gauge conditions (1.65), (1.67) at m = j, and (1.69). VAR's (9)–(10) on a cube □ of the class come from (167) with Δ = □, whose inputs are the (2)-bound on □'s neighbourhood and (7) near □; the proof of (167) is local to □̃ (VAR p.301 l.27–57, p.303). With 59.2's F for the first, whose sup over □̃(□) is at most C_FR_jε_j by 59.4, the adjacent layer included, and B₃e ≤ F for the data meeting the cube, (169) gives |A| < ½MC_FR_jε_j(L^jη)^{−1} on a cube of the layer j, since ¼M·C_FR_jε_j + ⅛M′C_FR_jε_j < ½MC_FR_jε_j for M′ ≤ M, and likewise |∇A| in its units. The global a-priori bound ε₀ = B₃ε₁ that starts the argument is Theorem 1's at 60.3's ε₁. VAR's condition M′·sup F ≤ a₅ holds with CM ≤ M(ε₁) for ḡ small. Against the thresholds L₀^{…}BCMα_{0,j} ≥ BCMα_{0,j} of LFR I (1.65), (1.69), and (1.67) at m = j, with B = B₃ (LFR I p.191 l.28) and C ≤ 2 (p.191 l.23–24), the ratio is at most C_FR_jε_j/(2BCα_{0,j}) ≤ θ_□ := θ_J max{1, (32(1 + β₀)B₃BC)^{−1}}, small for ḡ small by the factor (log ḡ^{−2})^{p₀+r−q₀}.
- The case (ii) of (1.66)–(1.67) for m < j. These conditions hold on (Ω_m ∖ Ω_{m+1}) ∩ X for k₀ < m ≤ j, k₀ = k − N₀, with the cubes of the size CML^jη and the threshold L^jη|A| < L₀^{2(j−m)}BCMα_{0,j} (LFR I p.190 l.48–53). A layer-m bound gives L^jη|A| ≲ CM·C_FR_mε_mL^{2(j−m)}, so the ratio carries (L/L₀)^{2(j−m)}, which θ_J does not absorb. U_2's layers are ≤ h, so these conditions do not arise at U_2 when h ≤ k₀ (LFR I p.181 l.40). Where h > k₀ they are open at U_2.
- The block variables (2.35) and (2.37). For a cube X of CRE (ii)'s class and a p such that 𝐁_p(X) refines 𝐁₂ inside X, which holds when X meets no layer of 𝐁₂ finer than p, Lemma A of 51.4 (with Ω₀ = X, 𝐁_p(X) ∪ {Γ_i}_{i<p}, and the fine data at ∂X; CRE p.256 l.57–63) gives U_{p,X}(M^·(U_2)) = U_2⌈_X up to a VAR (4) gauge transformation. U_{p,X} carries the spacing L^{−p}, so its current is J(U_2) rescaled by L^{3(p−k)}: |J_{p,X}| ≤ C_FR_nε_n(L^{n−p})^{−3}, against the threshold α_{0,n}L^{n−min{p,n}}(L^{n−p})^{−3} of CRE (2.37), with the same ratio θ_J; the plaquettes likewise. With 61.4's layer rule, 𝐁_p(X) ∪ {Γ_i}_{i<p} is coarser than 𝐁₂ somewhere in X only on the strips at the cut, where 𝐁₂'s layer is finer than the terms'. There the conditions are 61.4's.
- U_{1,2}. U_{1,2} is the minimal configuration of 𝐁_{1,2} (56.2), whose data are U_1's on Ω″^∼_{h+1} and U_2's on the complement. The data plaquettes of 𝐁_{1,2} that cross the cut have all their bonds in the band of scale-0 bonds, on which the data are 1 (51.2, 55.4), so e = 0 for them. The other data plaquettes are bounded per layer by 59.3 on U_1's side and 60.3 on U_2's. So the plaquette, current, cube-gauge, and block-variable items above hold at U_{1,2} on the layers of 𝐁_{1,2}, at the thresholds of those layers, with the case (ii) of (1.66)–(1.67) as follows: on U_2's side as for U_2, and on U_1's side, inside Ω_{k₀+1}, it is not given by this comparison; there the conditions at U_1, the case (ii) included, are §49.5's on Z^c and on the collar, with the collar points left open in 49.4. In run B, the data of U^B_{1,2} and of c^♭ at the shared scales are run B's averages, which differ from run A's by the data difference of the LF note's §4(c) (56.2), and (7) holds for them with the same bounds.

### 60.5 The Strips at the Cut, at the Thresholds of the Layer h (See §61)

The terms' layers are 𝐁″_k's (49.2, 53.2). On the strips of the two collars, 2M₁ wide in the units of the scale h, the terms' layer is h while the collars' layers are 0, …, h − 1. At a strip point x of the collar layer j < h the conditions of 60.4 hold at the thresholds of the layer j; the terms need them at those of the layer h, which are smaller by the scale factors L^{−(h−j)}, L^{−2(h−j)}, and L^{−3(h−j)} for the fields, the plaquettes, and the currents. Bałaban asserts these conditions (p.370 l.35–38). §61 derives them: the plaquettes and the current by §59's F with the step count of 61.2, under (M-V) and (W-3); the cube-gauge condition (2.38) from them by VAR (145)–(152) and REG Theorem 2 (61.3); the block variables (2.35) and (2.37) by the layer count and a comparison with the configuration (61.4). VAR Proposition 9 at the background 1 is not used: it needs (172), the bondwise smallness of all data in one gauge (VAR p.305 l.31–44), and (7) does not give it.

### 60.6 Status

Derived at real points, not reviewed in this form, given §59 (F, C_F, θ_J), Lemma A of 51.4, and the choice q₀ > p₀ + r:
- (7) at U_2's junction with V″ (60.3);
- the plaquette, current, cube-gauge, and block-variable conditions (1.64)–(1.69) at U_2 on its own layers (60.4), the case (ii) of (1.66)–(1.67) when h ≤ k₀;
- the same at U_{1,2} on the layers of 𝐁_{1,2}, given 56.2, except the case (ii) on U_1's side, which is §49.5's.

Quoted and checked: the sources of 60.1. Bałaban's results used as presented: VAR Theorem 1, (7), and (167)–(169); CMP 98 Proposition 2; LFR I (1.3) (printed for j = h, …, k − 1), (1.65)–(1.69), and (1.88); CRE (2.14) and (2.35)–(2.37).

Treated elsewhere, with their status recorded there: the strips at the cut (§61).

Open:
- the case (ii) of (1.66)–(1.67) at U_2 when h > k₀;
- complex points: 60.3 is at real data, and the extension of χ_{h,1/2}'s bound to the complex data of the discs is not done here (§68 treats complex points);
- (2.35) and (2.37) at the configurations of 57.1 and at D(s) (57.3's item).

What this changes in the LF note (recorded here, not edited): in its l.18 U_{1,2} item, the conditions (2.34)–(2.38) at U_{1,2} on its own layers and (7) at U_2 hold at real points, the strips being §61's; its other parts (the lift, r_z, the commutator, (5.1c) near the cut) are §§50, 56, and 62's. In its l.20 item, U_2 and U_{1,2} hold at real points on their own layers, as above; U_1 and U_{k,Λ} are §49's.

## 61. The Strips at the Cut, the Joins, and U_1's Junction

This section treats the three items left open by §§59–60: VAR's hypothesis (1) for Bałaban's joins (59.5), the conditions at the strips at the thresholds of the layer h (60.5), with 56.3's bound on B, and the junction of U_1's AL-gauge data with the data 1 (59.3). The strips need no field bound. §59's F is gauge-invariant, and it falls by a fixed factor across each collar layer once the layers are wide in VAR's cube unit. A bound on B then follows from F and REG Lemma 1, inside the hypothesis (172) of Proposition 9. Notation: M₁ is CRE's (p.245 l.35–37), and M₁^{VAR} and R₁ are VAR's (p.277); CRE's R₁ (p.246, a power of L at least (log g₁^{−2})^r) does not enter.

### 61.1 The Joins Satisfy VAR's (1) (Derived)

- The sources. VAR (1), p.277: (L^jη)^{−1}dist(Ω_j^c, Ω_{j+1}) > RM₁^{VAR} with R ≥ R₁. REG p.98 l.19 asks L^{−1}RM > 2dR₁M₁^{VAR}, which holds a fortiori for M ≥ M₁^{VAR} once it holds at M = M₁^{VAR}. CRE p.245 l.35–37: "M₁ is the size of large cubes for which all the theorems of the previous papers, especially those concerning the variational problem, are valid", with M₁ < M₂ = L²M₁ < M. CRE p.256 l.55–63: the joins have dist(Ω_n, Ω^c_{n−1}) ≥ L^nξM₁.
- The reading R-M₁. CRE p.245 l.35–37 describes M₁ as the size of large cubes for which the theorems of the earlier papers are valid. The note keeps VAR's M₁^{VAR} and R₁ fixed and takes CRE's M₁ := L^aM₁^{VAR}, with a ≥ 1 large. This is admissible for three reasons:
  - VAR (1) allows every R ≥ R₁ (p.277);
  - VAR Theorem 1's a₀, a₁, and B₃ depend on d and L only (p.279 l.28);
  - PBG Theorem 3.1 holds "for M ≥ M_1 and for an arbitrary configuration U satisfying … (3.35) with Mα_0 ≤ a_0" (p.397 l.37–38); here M = M₁^{VAR}, and Mα₀ ≤ a₀ holds for g small.

  So those theorems hold for cubes of the size L^aM₁^{VAR}. CRE's other uses of M₁ (pp.251, 255, 257, 266, 268) are layers of M₁-cubes and boundary layers of the width 2M₁ or 2LM₁ inside cubes of the side M. M is chosen after M₁ with M > L²M₁. Every Ω_j is then a union of M₁^{VAR}L^jη-blocks (VAR p.277 l.12), since M₁^{VAR} divides M₁.
- The normalisation. With j = n − 1, (L^{n−1}ξ)^{−1}dist(Ω^c_{n−1}, Ω_n) ≥ LM₁ > R′M₁^{VAR}, R′ := M₁/M₁^{VAR} = L^a, a power of L as REG p.77 l.17 asks.
- The condition. Take

  (M-V): M₁ > 2dLR₁M₁^{VAR}.

  Then R′ > 2dLR₁ ≥ R₁. For every cube parameter M′ that is a multiple of R₁M₁^{VAR} (REG p.98 l.7–9), L^{−1}R′M′ ≥ L^{−1}R′R₁M₁^{VAR} > 2dR₁M₁^{VAR}, which is REG's condition at p.98 l.19.
- The interfaces of the joins. VAR (1) is needed at every pair of consecutive layers of 𝐁₁, 𝐁₂, 𝐁_{1,2}, 𝐁^♭, and 𝐁^B_{1,2}, each in the units of the finer of the two layers. Four kinds occur:
  - Inside a collar 𝐁_h(Ω) the width is at least LM₁ (CRE p.256 l.58–61). Run B's first layer has LM₁ bonds across in its own units (56.1).
  - Between a collar's coarsest layer h and 𝐁″_k's next layer, the margin of LFR II p.370 l.35–38 is LMR_{h+1} − 2M₁ ≥ LM₁ wide in the units of the scale h, since M ≥ 2M₁ (61.2).
  - Inside 𝐁″_k, the history layers are 2MR_j apart in the units of the scale j (CRE p.256 l.21–24), and the shells Z″_k ∖ Z″_{k−1}, … are one layer of M-cubes of their scale wide (LFR I p.179 l.20–21). Both exceed LM₁, since M > L²M₁.
  - In 𝐁_{1,2} the two scale-0 strips merge into one band of 2LM₁ bonds (56.2). 𝐁^♭ and 𝐁^B_{1,2} have run A's and run B's widths (56.1–56.2).

  So every interface has the width at least LM₁ > R′M₁^{VAR} in its units. The joins satisfy VAR's (1) and REG's condition, and VAR Theorem 1, Proposition 9, and the two-layer property of □̃ (p.300 l.36–37) apply to them as VAR states them.
- The constants. PBG Theorem 3.1 fixes M₁^{VAR}, δ₀, a₀, and B₀ by d and L (p.397 l.37–38). R₁ is REG's and VAR's absolute constant (REG p.98 l.8 and l.37, VAR p.277). B₃ is VAR's and depends on d and L only (VAR p.279 l.28). None depends on R′. So (M-V) is a lower bound on a, given d and L; M is then taken with M > L²M₁. The constants that depend on M (C_e, C_F, and the M-dependence of B₅ in 54.2) are fixed before ḡ, as in 59.4.

This closes the item of 59.5 on VAR's (1) for the joins.

### 61.2 The Plaquettes and the Current at the Strips (Derived)

- The step length. For a unit cube Δ₀ of the layer i, the cube □ of §F has the side 2R₁M₁^{VAR}L^iη and contains Δ₀ (VAR p.300 l.28, p.302 l.45), and dist(□, □̃^c) = 2R₁M₁^{VAR}L^iη (p.300 l.36–37). A cube meeting □̃(Δ₀) lies in the layers ≤ i, or is a unit cube of the layer i + 1 at □̃'s boundary (59.2). So a step of 59.2's chain from a cube of the layer i moves at most r_VL^iη, with r_V := √d(4R₁M₁^{VAR} + L), which covers both the sup-metric and the Euclidean one.
- The steps per layer. Let a chain from x to a data plaquette p′ traverse a layer i of the joins, which is at least LM₁ wide in its own units, in either direction. A step from the finer side enters the layer by at most r_VL^{i−1}η, and a step from the coarser side by at most r_VL^{i+1}η. The steps from cubes of the layer i move at most r_VL^iη each, and the last cube reaches p′ within r_VL^iη. So at least s₁ steps start in the layer i, where

  s₁ := ⌊LM₁/r_V⌋ − L − 1.

  The same holds for the margins of LFR II p.370 l.35–38, in the layer h, LMR_{h+1} − 2M₁ ≥ LM₁ wide in its units, since M ≥ 2M₁. The steps counted in different layers are different steps.
- The decay. Let x be a point of a strip at the cut in the collar layer j < h, at U_2, U_1, U_{1,2}, c^♭, or U^B_{1,2}. The data are 1 on the domain (Ω″_{h+1})^c ∩ Ω″^{∼2}_{h+1} (LFR II p.370 l.35–38, 56.3, 60.5), and at U^B_{1,2} also on S (56.2). A chain from x to a data plaquette p′ with e(p′) ≠ 0 crosses either the collar layers j + 1, …, h − 1 and the margin on its side of the cut, or the other collar's layers 0, …, h − 1 and the margin on the other side. So ρ(x, p′) ≥ (h − j)s₁, and ρ(x, p′) ≥ ½|i − j| − 1 for p′ in the layer i (59.2). With e(p′) ≤ C_eR_iε_i (59.3, 60.3, 61.6), R_iε_i ≤ (L + 1)(1 + β₀)²(|i − j| + 1)^{1/2}(h − j + 1)^{1/2}R_hε_h (CRE (2.8)–(2.9), as in 59.4), (m + 1)^{1/2} ≤ 2^{m/2}, and (m + 1)^{1/2}2^{−m/4} ≤ 2^{1/2} for every integer m ≥ 0,

  F(x) ≤ B₃ sup_{p′} e(p′)2^{−ρ(x,p′)/2}2^{−ρ(x,p′)/2} ≤ C_FR_hε_hλ^{h−j},  λ := 2^{−(s₁−1)/2},

  with C_F of 59.4.
- The thresholds of the layer h. By 59.2, U satisfies (2) at x with F(x) in the normalisation of the layer j:

  |∂U − 1| ≤ C_FR_hε_h(L²λ)^{h−j}η²(L^hη)^{−2},  |J(x)| ≤ C_FR_hε_h(L³λ)^{h−j}(L^hη)^{−3}.

  Under

  (W-3): λ ≤ L^{−3},

  these are 59.4's bounds of the layer h, so the plaquette and current conditions (2.34) and (2.36) hold at the strips at the thresholds of the layer h with the ratio θ_J, uniformly in h, j, and k.
- The condition. r_V is fixed by d and L, and under R-M₁ (61.1) s₁ grows linearly in M₁ = L^aM₁^{VAR}. So (W-3) and (M-V) are lower bounds on a given d and L, and they hold together.

### 61.3 The Cube-Gauge Condition (2.38) at the Strips (Derived)

CRE p.261 (ii), (2.38): for each cube □ ⊂ Ω_n ∖ Ω_{n+2} with □ ∩ Ω^c_{n+1} ≠ ∅, of size CML^nξ, there is a gauge with U^u = exp iξA and L^nξ|A|, (L^nξ)²|∇^ξA| < BCMα_{0,n}, B an absolute constant. Let n = h and let □ meet a strip.
- The input. By 61.2 at the strips and 59.4 elsewhere, U satisfies (2) on □ and its neighbourhood in the normalisation of the layer h with ε₀′ := L²(L + 1)(1 + β₀)²C_FR_hε_h. At the points of the layer h + 1 this uses R_{h+1}ε_{h+1}L^{−2} ≤ (1 + β₀)R_hε_h/L (CRE (2.8)–(2.9)). The neighbourhood □_h extends R₁M₁L^hη beyond □ and can meet the layer h − 1 when □ is adjacent to ∂Ω_h; there the factor L² is VAR's ("U_k′ satisfies (2) on □̃ with L²ε₀η²", p.300 l.39–40) and (L + 1)(1 + β₀)² is 59.4's comparison of R_{h−1}ε_{h−1} with R_hε_h. The cubes of (2.38) with n = h − 1, □ ⊂ Ω_{h−1} ∖ Ω_{h+1} meeting a strip near ∂Ω_h, take the same input in the normalisation of the layer h − 1, which is weaker, and the argument below runs at n = h − 1 with the same constants.
- The gauge. VAR (145)–(152), pp.301–302, use only (2) on the cube with its neighbourhood, at one normalisation, and the generalized axial gauge. They are applied here with ℭ_k built in one layer at the scale h: □′_k := ∅ and V″ := Ū′^h on all of □_k^{(h)}. (150) is a definition, and the axial gauge is imposed by the construction, so this is VAR's construction at one layer, not its two-layer split (147)–(150) by the configuration's own layers, which at the strips do not have VAR's two-layer property relative to a cube of the layer h. The cube parameter is enlarged to a multiple of R₁M₁^{VAR} where CM/2 is not one. They give |Ū′ − 1| < 9dL²M′ε₀′ for a cube of side M′L^hη, and by REG Theorem 2 (p.83) a gauge with L^hη|A|, (L^hη)²|∇A|, (L^hη)³|∂*∂A|, (L^hη)³|ΔA| < 9dL²B₁M′ε₀′ on the cube. Criticality is not used. With M′ = CM the smallness condition of REG Theorem 2 is 9dL²CMε₀′ ≤ c₁, which holds for ḡ small.
- The ratio. Against BCMα_{0,h} it is 9dL²B₁ε₀′/(Bα_{0,h}) ≤ 9dL⁵(L + 1)(1 + β₀)²B₁C_F(A₀/C₀)(log ḡ^{−2})^{p₀+r−q₀}/B, small for ḡ small and uniform in h and k given q₀ > p₀ + r (55.7), as θ_J in 59.4. CM cancels.

### 61.4 The Block Variables (2.35) and (2.37) at the Strips (Derived)

Let 𝐔 be one of the configurations of 61.2's decay bullet, X a domain of the terms, p ≥ 1, 𝐁′ := 𝐁_p(X) ∪ {Γ_i}_{i<p}, and U_{p,X} := U(𝐁′, M_{𝐁′}𝐔) (CRE p.261; LFR I p.190). Each 𝐔 of that list is the minimal configuration of its set: U_1 and U_2 of 𝐁₁ and 𝐁₂ (LFR II (1.52)–(1.53)), U_{1,2} and U^B_{1,2} of the combined sets, and c^♭ of 𝐁^♭ (56.2). So Lemma A applies to 𝐔.

- The convention (reading R-pX). CRE p.256 l.57–63 builds 𝐁_j(Ω) on T_ξ, ξ = L^{−j}, with Ω_n a union of L^nξM₁-cubes, so that the scale j is the unit lattice. (2.35) and (2.37) carry L^{−p} where (2.34) and (2.36) carry ξ, and LFR I p.190 (i)–(iii) print the same with η. R-pX: U_{p,X} is written in the units of the step p, where its finest lattice is T_{L^{−p}} and the scale p is the unit. In the units of the step k, η = L^{−k}, its lattice is T_η and a length ℓ of the step-p units is L^{p−k}ℓ. A plaquette deviation is dimensionless and a current scales as a length to the power −3, so (2.35) and (2.37) read
  |∂U_{p,X} − 1| < (1 − β(…))α_{0,n}η²(L^nη)^{−2},  |J_{p,X}| < (1 − β(…))α_{0,n}L^{n−min{p,n}}(L^nη)^{−3}
  on X ∩ (Ω_n ∖ Ω_{n+1}): the threshold of (2.34), and that of (2.36) times L^{n−min{p,n}} ≥ 1. Read on the coarser lattice T_{L^{−p}} of the step-k units, (2.35) would ask the averages of 𝐔 for a curvature L^{2(k−p)} below 𝐔's own threshold; that reading is not used. (2.35) itself needs no reading: L^{−2p}(L^nL^{−p})^{−2} = L^{−2n} in every unit convention. For (2.37) the other literal reading takes L^{−p} with J_{p,X} measured in step-k units, a threshold smaller by L^{3(k−p)}. It is inconsistent with the print. Where 𝐁′ refines 𝐔's set, J_{p,X} = J(𝐔) by Lemma A, and J(𝐔) has the size R_nε_n(L^nη)^{−3}, which exceeds that threshold for k − p large.
- The layers. For x ∈ X let n(x) be the terms' layer, j(x) the layer of 𝐔's set, c(x) the collar index of 𝐁_p(X) (c = p off its collar), m(x) := min{p, n(x), c(x)} the layer of 𝐁′, and m̄(x) := min{p, n(x)}. So m ≤ m̄ ≤ n, and m < m̄ only on 𝐁_p(X)'s collar, which lies within 2M₁ of ∂X in the units of the scale p (CRE p.256, after (2.12)). The layer m changes only across a band of the terms' set or of 𝐁_p(X)'s collar, by at most 1 at each, and in such a band 𝐁′'s layer is at most the band's, which is at least LM₁ wide in its own units. So 61.2's count gives at least s₁ steps of 59.2's chain for U_{p,X} in each band traversed, in either direction. Below, N counts full traversals; a chain between points whose layers of one set differ by D traverses at least D − 1 bands of that set. Bands of different sets may overlap, so a chain that traverses N bands taken from ν of the sets has ρ ≥ s₁N/ν. Under
  (W-3′): λ ≤ L^{−9},
  which implies (W-3), this gives 2^{−ρ} ≤ (λ²/2)^{N/ν} ≤ L^{−18N/ν}. Off the strips j = n (60.5), so R := {y ∈ X : m(y) > j(y)} lies in the strips, and the strips lie in D := (Ω″_{h+1})^c ∩ Ω″^{∼2}_{h+1}, where 𝐔's data are 1 (61.2).
- The data. 𝐁′'s datum at y is M^{m(y)}(𝐔). By 59.4, 60.4, and 61.2 (with (L²λ)^{h−j} ≤ 1), |∂𝐔 − 1| ≤ C_FR_nε_nη²(L^nη)^{−2} at every point of the terms' layer n. CMP 98 Proposition 2 (p.26: |Ū^k(∂p) − 1| < 2α₀ if U's plaquettes are below α₀L^{−2k}) then gives e ≤ C_aC_FR_{n(y)}ε_{n(y)}L^{−2(n(y)−m(y))}, C_a := 8L²(L + 1)(1 + β₀)². The factor L²(L + 1)(1 + β₀)² covers an adjacent terms' layer in the block's neighbourhood (CRE (2.8)–(2.9)). The factor 2 beyond Proposition 2's covers a neighbour Δ₀′ across a boundary of 𝐔's layers: 59.2's recursion ρ(Δ₀, p′) ≤ ρ(Δ₀′, p′) + 1 for Δ₀′ meeting □̃(Δ₀) gives F(Δ₀′) ≤ 2F(Δ₀). Two improvements hold in D. (a) If m ≥ j on the m-block of y and its neighbours inside D, the datum is 1: M^m = M^{m−j}∘M^j (CMP 98 p.24, Ū^{k+1} = \overline{Ū^k}), and the average of 1 is 1. (b) If m(y) < j(y), 61.2 (59.4 where j(y) = h) gives e ≤ C_aC_FR_hε_h(L²λ)^{h−j(y)}L^{−2(h−m(y))}. A datum in D with m(y) ≥ j(y) whose m-block neighbourhood meets 𝐔's layer j(y) + 1, or leaves D, is bounded by (b) with j(y) + 1 in place of j(y).
- The general bound. 𝐁′ satisfies VAR's (1): its layer function is min{p, n, c}, and if two nested layer functions have bands at least LM₁ wide in their own units, so does their minimum, since dist(A₁ ∩ B₁, (A₀ ∩ B₀)^c) is at least the smaller of the two distances; the minimum also preserves unions of M₁^{VAR}-blocks. With 61.1 for each of the two, §59 applies to U_{p,X} on 𝐁′: F_X(x) = B₃ sup_{p′}e(p′)2^{−ρ(x,p′)}. For p′ at y let Δ := (n(x) − m(x)) − (n(y) − m(y)) and let N be the number of bands of the terms' set and of 𝐁_p(X)'s collar crossed. Then |n(x) − n(y)| ≤ N + 1, |Δ| ≤ 2N + 2, and 2^{−ρ} ≤ L^{−9N} (ν = 2). With R_{n(y)}ε_{n(y)} ≤ (L + 1)(1 + β₀)²(N + 2)^{1/2}R_{n(x)}ε_{n(x)} (59.4) and L^{−5N}(N + 2)^{1/2} ≤ √2,
  F_X(x) ≤ C_XR_nε_nL^{−2(n−m)},  C_X := √2L⁴B₃C_aC_F(L + 1)(1 + β₀)²,  n = n(x), m = m(x).
  So |∂U_{p,X} − 1| ≤ F_Xη²(L^mη)^{−2} ≤ C_XR_nε_nη²(L^nη)^{−2}, which is (2.35) at every point of X with the ratio θ_J C_X/C_F of 59.4. Where m(x) = m̄(x), |J_{p,X}(x)| ≤ F_X(L^mη)^{−3} ≤ C_XR_nε_nL^{n−m̄}(L^nη)^{−3}, which is (2.37) with the same ratio.
- The current on R. Let y′ ∈ R, so y′ is in a strip and n(y′) = h. Then F_X(y′) ≤ C_RR_hε_hL^{−3(h−m(y′))}, C_R := 4LC_X. The data of (a) are 1. For a datum of (b) at y, let M* be the largest layer of 𝐁′ on the chain, A := M* − m(y′), B := M* − m(y), and K := (j(y) − M* − 1)₊. The chain traverses (A − 1)₊ + (B − 1)₊ bands of 𝐁_p(X)'s collar or of the terms' set, and, if M* < j(y), the bands of 𝐔's set with the indices M* + 1, …, j(y) − 1 at 𝐁′'s layer at most M*, so 2^{−ρ} ≤ L^{−9(A+B+K)} (ν = 2). With (L²λ)^{h−j(y)} ≤ L^{−(h−j(y))} and j(y) − M* ≤ K + 1, the exponent of L in e(p′)2^{−ρ}L^{3(h−m(y′))}/(C_aC_FR_hε_h) is (j(y) − M*) + 3A − 2B − 9T, where T := (A − 1)₊ + (B − 1)₊ + K″ counts the traversals, K″ := K + 1 if M* < j(y) and K″ := 0 otherwise. If M* < j(y), then j(y) − M* = K + 1 and the exponent is at most −8K − 5 + 3A − 9(A − 1)₊ ≤ 1. If M* ≥ j(y), then B ≥ 1 + M* − j(y), since m(y) < j(y), and the exponent is at most −2 + 3A − 9(A − 1)₊ ≤ 1. For a datum of (b) with j(y) + 1 in its place the same count holds, with K taken at j(y) + 1. For a datum outside D, the chain crosses the margin of LFR II p.370 l.35–38 (layer h, at least LM₁ wide in its units) at 𝐁′'s layers at most M*, the bands of 𝐁_p(X)'s collar up to M*, and |n(y) − h| bands of the terms' set beyond. The margin alone takes at least s₁L^{h−M*} ≥ s₁(h − M* + 1) steps, so with ν = 3 and N ≥ (h − m(y′) + 1) + |n(y) − h|, 2^{−ρ} ≤ L^{−6(h−m(y′)+1)−6|n(y)−h|}, and e(p′)2^{−ρ} ≤ C_aC_F(L + 1)(1 + β₀)²R_hε_hL^{−6(h−m(y′))}. Hence the bound. At y′ ∈ R itself, |J_{p,X}(y′)| ≤ F_X(L^{m(y′)}η)^{−3} ≤ C_RR_hε_h(L^hη)^{−3}, which is (2.37) with the ratio θ_JC_R/C_F.
- The current on 𝐁_p(X)'s finer collar layers off R. Let x ∉ R with m(x) < m̄(x). If R = ∅, 𝐁′ refines 𝐔's set on X, and Lemma A gives U_{p,X} = 𝐔 on X up to gauge (60.4), so J_{p,X}(x) = J(𝐔)(x). Otherwise let 𝐁‴ be the set with the layer min{m, j} on X, which refines 𝐁′ and 𝐔's set there, has bands at least as wide as the narrower of the two, so at least LM₁, and satisfies VAR's (1) as in 61.1. Lemma A gives U(𝐁‴, M_{𝐁‴}𝐔) = 𝐔 on X, and Lemma B gives U(𝐁‴, M_{𝐁‴}U_{p,X}) = U_{p,X}, up to gauge. Their data are equal off R, where 𝐁‴'s layer is m and both are M^m(𝐔). On R, 𝐁‴'s layer is j, 𝐔's datum is 1, and V′ := M^j(U_{p,X}) has its m-block averages equal to M^m(𝐔) = 1. REG Lemma 1 (p.79) is a one-step statement (k = 1), so it is applied scale by scale, as in 61.5's (d2). Let W_i := M^i(U_{p,X}) for j ≤ i ≤ m, taken in the axial gauge within the (i + 1)-blocks, successively for i = m − 1, …, j. These transformations are 1 at the block centres, so they are VAR (4) transformations for 𝐁′, as in 61.5. By CMP 98 Proposition 2 (p.26), W_i satisfies (1.7) with k = 1 at α₀^{(i)} := 2F_XL^{−2(m−i−1)}, and W_m = 1. Lemma 1 with V₀ := 1 and α₁ := sup|W_{i+1} − 1| then gives |W_i − 1| < 4d²α₀^{(i)} + sup|W_{i+1} − 1|, hence |V′ − 1| = |W_j − 1| < 8d²F_XΣ_{t≥0}L^{−2t} ≤ 11d²F_X, and
  |B| ≤ 22d²F_X ≤ 22d²C_RR_hε_hL^{−3(h−μ)}  on R_μ := {y′ ∈ R : m(y′) = μ},  B := (1/i)log V′.
  This is (172) for ḡ small. The data are changed on R_0, R_1, … one at a time. Each intermediate datum differs from M_{𝐁‴}𝐔 by at most 11d²F_X bondwise on R, so it satisfies (7) and (172) at ε₁″ as in 61.5, and Proposition 9 applies at each intermediate base. Applying (G.43) of §10.6 (from VAR (190), Proposition 9, and PBG (3.10)–(3.12)) to each change gives
  |J_{p,X}(x) − J(𝐔)(x)| ≤ C_J(L^mη)^{−3}Σ_μ22d²C_RR_hε_hL^{−3(h−μ)}e^{−δ″d(x,R_μ)},  m = m(x),
  with d the distance of PRT2 (2.46) for 𝐁‴. A path from x to R_μ traverses N bands of the terms' set and of 𝐁_p(X)'s collar, with |n(x) − h| ≤ N + 1 and |μ − m(x)| ≤ N + 1. In each, 𝐁‴'s layer is at most the band's, so PRT2's distance, which counts each layer in its own units, grows by at least LM₁ across it, and d(x, R_μ) ≥ ½LM₁N. Against R_nε_nL^{n−m̄}(L^nη)^{−3}, n = n(x), the exponent of L is 3(n − h) + 3(μ − m(x)) − (n − m̄) ≤ 6N + 12. So the term μ has the ratio at most 22d²L^{12}C_JC_R(L + 1)(1 + β₀)²(N + 2)^{1/2}L^{6N}e^{−½δ″LM₁N}. Under
  (W-4): δ″LM₁ ≥ 16 log L,
  this is at most 22d²L^{12}C_JC_R(L + 1)(1 + β₀)²L^{−2N}(N + 2)^{1/2}, summable over μ since N ≥ |μ − m(x)| − 1. With |J(𝐔)(x)| ≤ C_FR_nε_n(L^nη)^{−3} (59.4, 60.4, 61.2), (2.37) holds at x with the ratio θ_J(1 + C′_J), C′_J := 176d²L^{14}C_JC_R(L + 1)(1 + β₀)²/C_F, the factor 2L² covering the shift by 1 in the sum over μ.
- Conclusion. (2.35) and (2.37) hold at U_{p,X}(M^·𝐔) on all of X, for every p, at the thresholds of the terms' layers, with ratios θ_J times constants of d, L, M₁, B₃, and C_F, small for ḡ small uniformly in h, k, and p. (W-3′) and (W-4) are lower bounds on a given d and L, since under R-M₁ (61.1) s₁ grows linearly in M₁ = L^aM₁^{VAR} and δ″ depends only on δ₀ and d; they hold with (M-V).

### 61.5 The Size of B (Derived)

B of 56.2 lives on S = (d1) ∪ (d2). On (d1), M_{𝐁^B_{1,2}}(c^♭) is c^♭ on run B's fine bonds, and 𝐁^♭ fixes its averages over the ε-blocks, which are 1 (U^A_{1,2}'s band data). On (d2), M_{𝐁^B_{1,2}}(c^♭) is the field of c^♭'s ε-block averages, and 𝐁^♭ fixes its averages over the Lε-blocks, which are 1 (run A's collar data at its scale 1).
- The gauge. Take c^♭ axial within the ε-blocks of (d1), and the field of its ε-block averages axial within the Lε-blocks of (d2), along REG's contours Γ_{y,x} from the block centres. These transformations are 1 at the block centres, which are data sites of 𝐁^♭ there, so they are VAR (4) transformations of 𝐁^♭: c^♭ stays its minimal configuration, and B is computed in this gauge.
- The plaquettes. c^♭ is the minimal configuration of 𝐁^♭ at data satisfying (7) with ε₁ (56.2, 60.3–60.4), on the layers of the joins (61.1). A chain from a point of S to a data plaquette with e ≠ 0 crosses run A's layer 1 beyond the depth 2c₁ (2(L − 1)M₁ wide in its units), its collar layers 2, …, h − 1, and the margin, on one side of the cut or the other (56.1, 56.3). By 61.2's count, ρ ≥ ((h − 1)₊ + 1)s₁, so F ≤ B₃ε₁2^{−((h−1)₊+1)s₁} ≤ α₀ := B₃ε₁λ^{2(h−1)₊} at the points of S, in the normalisation of 𝐁^♭'s layer there (run B's scale 1 on (d1), 2 on (d2)).
- On (d1). REG Lemma 1 (p.79), with V₀ := 1 and V′ := c^♭ on the ε-blocks: both satisfy (1.7) with α₀, (R(1)c^♭)(Γ_{y,x}) = 1 by the gauge, and the averages of c^♭ and of 1 are equal, so α₁ = 0. Hence |c^♭ − 1| ≤ 4d²α₀ on the fine bonds of (d1), (1.24) being strict for every α₁ > 0. The lemma is local: only the bounds on the two blocks of a bond enter. A fine bond from a block of (d1) to a block outside (d1) has that block in the same layer of 𝐁^♭ and inside the chain count above, so both blocks satisfy the hypotheses.
- On (d2). By CMP 98 Proposition 2 the field of c^♭'s ε-block averages satisfies (1.7) with 2α₀ in the normalisation of the Lε-blocks, and its Lε-block averages are 1. REG Lemma 1 at that scale gives |M^1(c^♭) − 1| < 8d²α₀ on (d2).
- The bound. With |(1/i)log V| ≤ 2|V − 1| for |V − 1| ≤ ½,

  |B| ≤ C_Bε₁λ^{2(h−1)₊} bondwise on S,  C_B := 16d²B₃.

- (172). V′ := exp(iB) on S and 1 elsewhere has |V′ − 1| ≤ C_Bε₁ = C₁ε₁′ bondwise on all of 𝔅_k, with ε₁′ := C_Bε₁/C₁. At ε₁″ := max{ε₁, ε₁′} ≤ a₁ for ḡ small, c^♭'s data satisfy (7) and V′ satisfies (172). So 56.2's use of Proposition 9 and 56.4's use of (190) at the background c^♭ are inside their hypotheses, with their constants taken at ε₁″, a factor at most max{1, 16d²B₃/C₁} over ε₁. The axial gauges above are VAR (4) transformations of 𝐁^♭, not of 𝐁^B_{1,2}, and they are 1 off S. In this gauge c^♭ is still the minimal configuration of 𝐁^B_{1,2} at its own averages (Lemma B), and its data off S are unchanged. So 56.2's Proposition 9 applies with B computed in this gauge.

### 61.6 U_1's Junction (Derived, Edges Included)

- The sources. LFR II (1.53), p.370: U_1 = U_{𝐁₁}(V″⌈_{Λ^c}, M^k(U_0^{(AL)})⌈_{Λ∩Ω″_k}, 1⌈_{Z″_k∩Ω″^∼_{h+1}}). LFR I p.197, before (1.83): M^k(U_0) = V_Λ, and (1.83), |V_Λ(b) − 1| < O(1)B₅M⁶ε_k for b ⊂ Λ^{(k)}, in the axial gauge in Λ^{(k)}. LFR I p.197, after (1.86): U_0^{u₀} = U_0^{(AL)} inside Λ, u₀ the gauge transformation of (1.86). REG p.78 l.15: (\overline{U^u}^j)_b = u(b_−)(Ū^j)_bu^{−1}(b_+), so the block averages are covariant with the values of u at the block centres. 59.3: |M^k(U_0^{(AL)})(b) − 1| ≤ O(1)B₃²B₅M⁶ε_k for the k-block bonds b ⊂ Z″_k, from (1.87).
- The plaquettes of the averages. Let p be a plaquette of the scale k in Λ. By the covariance, M^k(U_0^{(AL)}) = M^k(U_0^{u₀}) = (V_Λ)^{u₀} on the k-bonds of Λ, and the product of a configuration around ∂p changes under a gauge transformation only by conjugation with the value at the base point. So |M^k(U_0^{(AL)})(∂p) − 1| = |V_Λ(∂p) − 1|, in any gauge. If the four bonds of p lie in Λ^{(k)}, this is at most 4O(1)B₅M⁶ε_k by (1.83). For a plaquette in Λ in RG I's convention, a corner in Λ, that is not contained in Λ^{(k)}, (1.78) (LFR I p.194 l.43) bounds it by 2B₅M⁵L(L + 1)N₀^{−1}R_kε_k, as in 59.3. This covers the shell Λ ∖ Z″_k and its edges at ∂Z. Neither the layers of 𝔹_k(Λ) nor a bound on u₀ enter.
- The junction. A junction plaquette p of the first two kinds of data carries M^k(U_0^{(AL)}) on its bonds in Λ ∩ Ω″_k and 1 on its bonds in Z″_k ∩ Ω″^∼_{h+1}, at most three of them; all four bonds lie in Λ, since Z″_k ⊂ Λ. For unitary matrices, replacing one factor V of a product by 1 changes the product by |V − 1| in norm. Replacing each datum 1 on a bond b ⊂ Z″_k by M^k(U_0^{(AL)})(b) therefore gives
  e(p) ≤ |M^k(U_0^{(AL)})(∂p) − 1| + Σ_{b ∈ p, datum 1}|M^k(U_0^{(AL)})(b) − 1| ≤ C_JnR_kε_k,  C_Jn := 7O(1)B₃²B₅M⁶ + 2B₅M⁵L(L + 1),
  with B₃ ≥ 1, R_k ≥ 1, and N₀ ≥ 1, the O(1)'s of (1.83) and 59.3 read as one constant. So e ≤ C_eR_kε_k at every such junction, with C_e enlarged to cover C_Jn. The bound uses the smallness of M^k(U_0^{(AL)}) only on the bonds that carry the datum 1, which lie in Z″_k, where 59.3 has it; on the shell bonds only the gauge-invariant plaquette enters.

This closes the junction check of 59.3 and its item in 59.5, the edges of the shell at ∂Z included.

### 61.7 Status

Status: 61.1–61.6 are derived at real points and not reviewed in this form, under the conditions on the constants below and q₀ > p₀ + r (55.7).

Quoted from the print:
- VAR (1) (p.277, l.12), p.279 l.28, p.300 l.28 and l.36–37, p.302 l.45, (145)–(152) (pp.301–302), (172) (p.305), (190) (p.308), (181), and Proposition 9 (p.309);
- REG p.77 l.17, p.78 l.15, Lemma 1 (p.79), Theorem 2 (p.83), and p.98 l.7–9, l.19, and l.37;
- PBG Theorem 3.1 (p.397 l.37–38);
- CMP 98 p.24 (Ū^{k+1} = \overline{Ū^k}) and Proposition 2 (p.26);
- CRE p.245 l.35–37, pp.251, 255, 257, 266, and 268 (the uses of M₁), p.256 l.21–24 and l.55–63, and p.261;
- LFR I p.179 l.20–21, p.190 (i)–(iii), (1.78) (p.194 l.43), (1.83), and (1.86)–(1.87);
- LFR II (1.52)–(1.53).

Readings:
- R-M₁ (61.1): VAR's M₁^{VAR} and R₁ are fixed, and CRE's M₁ := L^aM₁^{VAR}.
- R-pX (61.4): the units of U_{p,X}.
- The layer min{p, n, c} of 𝐁_p(X) ∪ {Γ_i}_{i<p}, which CRE does not print.

Used from the notes: Lemmas A and B of 51.4, 56.1–56.2, §59, and (G.43) of §10.6.

Conditions on the constants: (M-V), (W-3), (W-3′), and (W-4), lower bounds on a given d and L (61.1, 61.2, 61.4).

Derived at real points:
- VAR's (1) for the joins, their interfaces included (59.5);
- the plaquette, current, and cube-gauge conditions (2.34), (2.36), and (2.38) at the strips at the thresholds of the layer h (60.5);
- 56.3's bound on B, and with it the hypothesis (172) of 56.2's and 56.4's uses of Proposition 9 and (190);
- U_1's junction of the data M^k(U_0^{(AL)}) with the data 1 (59.3, 59.5), the edges of the shell Λ ∖ Z″_k at ∂Z included;
- the block-variable conditions (2.35) and (2.37) at U_{p,X}(M^·𝐔) on all of X, for the configurations of 61.2 and every p, X's finer collar layers over the strips included (61.4).

Open:
- complex points: 61.1–61.6 are at real data; §68 treats complex points, with its status recorded there;
- the collar points near Λ of 49.4, which enter U_1's data through §49.5.

Treated elsewhere, with their status recorded there: (5.1c) at the cut (56.7), in §§62, 63, and 68.

What this changes in the LF note (recorded here, not edited): its l.18 U_{1,2} item is derived at real points at the strips at the cut, the block variables included, and at 56.3's bound on B. Its l.20 item is derived at real points at U_1's junction (61.6). 57.3's item stays open at the configurations of 57.1 and at D(s); 61.4 does not reach them, since it uses the data 1 on D and 61.2's decay.

## 62. (5.1c) at the Near Domains That Meet the Cut

This section treats (5.1c) on the near domains that meet the cut, at real points. The term at the composite is controlled by the configuration's own conditions on □₀, so the class conditions of the glued configuration on □₀ ∖ □̃³, which 57.3 asks for, are not needed for it. Under the counterterm clause of 62.3, a construction choice, the counterterm of z reads the configuration that the near-domain terms of z read, and irr(Δ) at the configuration is the term at the composite.

### 62.1 The Sources (Read)

- RG I p.275 l.2–7: "in the interior averages M^·(U_{k+1}) we replace the configuration U_{k+1} by 𝐔. The function 𝐇_k and the averaging operations Q_j in the definition of B̃_□ depend on U_{k+1}. Now we introduce the variables 𝐔, 𝐉 in these expressions in a slightly different way … the configuration U_{k+1} is replaced by the configuration U_{k+1}(□₀, M^·(𝐔)), extended as equal to 𝐔 outside □₀", which has "approximately the same regularity properties as 𝐔" (l.6–7). So 𝐔 enters the interior averages, and the composite enters 𝐇_k and Q_j, through M^·(𝐔). The space U′^c_{k+1}(□₀, …) consists of configurations 𝐔, 𝐉 satisfying (i)–(iv), with (i)–(iii) "on the whole lattice T_η" (l.20–21).
- RG I (3.30)–(3.34), pp.276–277: the term is 𝐄^{(j)}(X, U_j(□₀, exp iQ(ηA))), expanded "in B up to the fifth order", and (3.32) bounds A on □̃⁴. RG I p.273 l.39–42: the cubes □₀ ⊃ □₁ ⊃ ⋯ satisfy (1.3)–(1.6) [14] with R = R₁, hence □̃⁴ ⊂ □_{k+1}.
- CRE p.280 l.14–22, (3.49)–(3.50), and p.281 (3.56)–(3.57): the relevant part is ½Σ_{κ<μ, λ<ν}𝐄^{(2)}_{μν,κλ}(X, z)tr F_{κμ}(z)F_{λν}(z), with F the field strength of the expansion variable B at z. The remainder is O((L^jL^{−n})^{5−β})exp(−κd_j(X)) (p.281 l.44–45).
- LFR II p.372 l.3–12, (1.59): 𝐄^{(j)}(X, U″_k, z) = 𝐄^{(j)}(X, U^0_k, z) + [𝐄^{(j)}(X, U_j(𝐁_j(□₀), exp iQ_·(η𝐇″_k(g_kB))M^·(U^0_k)), z) − 𝐄^{(j)}(X, U_j(𝐁_j(□₀), M^·(U^0_k)), z)], "a somewhat simplified version of the transformation (3.3), (3.18), (3.19) [I]", stated for the terms 𝐄^{(j)}, with 𝐑^{(j)} "considered in the same way" (l.20). p.373 l.2–6 expands around U_{1,2}, then "using the representation (1.57), and then once more using (1.58)", so the expansion points are U_{1,2}, U_{k,Λ}, and U_k, and the result is the original terms "taken at the background field U_k". CRE p.283 l.16–17: "Analyzing A(h_z, U_k) in the same way as above". The print says nothing about applying (1.59) to the counterterm; R-near (45.1, 55.2) does.
- The Cauchy note:
  - irr(Δ) (l.108), with A(h_z, ·) and N read at the configuration's own plaquette field Φ_P (l.74–76);
  - the bound of a plane-pair action by the plaquettes on the support of h_z (l.243), with the Hilbert–Schmidt norm, for which |tr Φ_PΦ_{P′}| ≤ |Φ_P||Φ_{P′}|;
  - the inputs of the near-domain proof, (I.1.11), (I.1.13), (I.1.14), and (iv) on □₀ (l.140–142), with (iv) from (I.1.17) (l.147);
  - the condition (N) (l.144), the comparison of the layers (l.148), and (R-Δ^c-T) (l.154).

### 62.2 The Term at the Composite (Derived)

Let 𝐔 be one of the configurations of 61.2's decay bullet, and let z be a point of the layer n whose near domain □₀ meets a strip at the cut and satisfies (N), □₀ ⊂ Ω_n. The strips lie in Ω_h ∖ Ω_{h+1} (60.5, 61.2), so (N) gives n ≤ h. Under R-data the near terms at 𝐔 are 𝐄^{(j)}(X, P_n𝐔), with P_n𝐔 = U_n(□₀, M^·(𝐔)) on □₀. Let Ŵ := P_n𝐔 on □₀ and 𝐔 outside.
- The input. RG I's Lemma 4 takes 𝐔 itself as its input, "for 𝐔 ∈ U′^c_{k+1}(□₀, (1 + 2β)α₀, (1 + 2β)α₁)" (p.280 l.25). The composite enters only as a function of the data M^·(𝐔), and its background bounds (I.3.26)–(I.3.27) follow from the data bounds. The proof's inputs are (I.1.11), (I.1.13), (I.1.14), and (iv) of 𝐔 on □₀, in the L^{−n}-scale (the Cauchy note's l.140–142); (I.1.14) includes the current bound of 𝐔 on □₀. Ŵ's own conditions on □₀ ∖ □̃³ are not among them.
- The input holds. The plaquettes and the current of 𝐔 on □₀ are within the thresholds of the layer h at α̃′/2 with the ratio θ_J (59.4): off the strips by 59.4 and 60.4, on the strips by 61.2, where (W-3) makes the factors (L²λ)^{h−j} and (L³λ)^{h−j} at most 1. For n ≤ h the thresholds of the layer h are below those of the layer n by the comparison of the Cauchy note's l.148, and θ_J ≤ θ ≤ 1/16, so the inputs lie inside the room (1 + 2β)α_{·,n}/(2B₃) that Lemma 4 asks for. (ii) holds with A′ = 0 at real points. (iv) follows from RG I (1.17) at ξ = L^{−n} with □₀ as Ω₀, as at the Cauchy note's l.147.
- The bound. The proof of (5.1c) then runs as on 𝒮_z, with the background of (I.3.30) at 𝐀 = 0 being the composite's field. Its relevant part is therefore read at Ŵ, whose regularity on □̃⁴ is (I.3.27), and A(h_z, Ŵ) and N(Ŵ) are read at Ŵ's own plaquettes, with supp h_z ⊂ □̃² ⊂ □̃⁴. The far terms are read at 𝐔 and bounded by the condition (a) at 𝐔, 𝐔|_{X^∼} ∈ 𝒫_j(X; r) for every far X, which includes the lift condition at 𝐔. So

  |D_Ŵ| ≤ dE₁(L^{j−n})^{4+β′},  D_Ŵ := Δ(Λ_j, 𝐔, z) − Δ(Λ_j, 1, z) − ΔβA(h_z, Ŵ) − N(Ŵ),

  given the condition (a) at 𝐔 and the lift condition at the composites, both as in the Cauchy note, where they are open for every z and not specific to the cut.

### 62.3 The Counterterm Clause (a Construction)

The literal reading of CRE (2.25), −β_j(g_{j−1})A(φ_j, U_k), and of (3.65), A(φ_j, U_k) = Σ_zA(h_zφ_j, U_k), has the counterterm read the configuration itself. R-near expands the counterterm of z with the near-domain terms of z, through (1.59).

- The identity (1.59). It writes a term at a configuration c′ as the term at an expansion point c plus a bracket, the difference of the term at two composites, at the data of c′ and at the data of c. It is an identity when the terms at c′ and at c are the terms at their composites. At a configuration that is the local minimiser of its own cube data this holds by (I.3.18) at the layer (the Cauchy note's l.124). At an expansion point that is not, such as U_{1,2} on a near domain that meets the cut, it holds by R-data, which reads the term at P_nc; this is the reading, not the print.
- The counterterm. R-near applies (1.59) to A(h_z, ·) and to N, so the bracket carries β_j[A(h_z, P_nc′) − A(h_z, P_nc)] + [N(P_nc′) − N(P_nc)]. If the counterterm of the expansion point reads P_nc, the expansion point and the bracket add up to the counterterm at P_nc′. If it reads c, the sum differs by β_j[A(h_z, c) − A(h_z, P_nc)] + [N(c) − N(P_nc)], which (1.59) does not contain.
- The clause. Under the clause the counterterm of z, with N for G, reads the configuration that the near-domain terms of z read: P_□𝐔 where R-data applies, with P_□ of 66.1 (P_□ = P_n under (N)), and the configuration itself where the term is read there. It is a redefinition of the counterterm, the choice under which every application of (1.59) to A(h_z, ·) and N is exact. It does not change the quantity of either run, for two reasons, derived in 66.1:
  - The endpoints of the chain. The chain U″_k → U^0_k → U_{1,2} → U_{k,Λ} → U_k telescopes, and the term and the counterterm at the first configuration are their values at P_□U″_k. By 66.1's inclusion, a minimal configuration of a determining set whose blocks that meet □₀ are of scales ≥ m(□₀) minimises the action over the smaller constraint set of P_□, and by Lemma A with Ω = □₀ and VAR's uniqueness of the critical orbit, P_□c = c on □₀ up to gauge. This holds for each of U″_k, U^0_k, U_{k,Λ}, and U_k, on near domains that meet the cut included, since m(□₀) is the finest block scale on □₀ over all the members' sets. So the quantity at each z is Bałaban's, and U_1 and U_{1,2} are intermediate expansion points that cancel in the total.
  - The sums over z. At an entry c(t), 0 < t < 1, each z reads its own composite, so Σ_zA(h_z, ·) is not A(φ_j, ·) at one configuration. The sum at one configuration is used for the weight-change part wc of the blocking artifact (the LF note's l.14). 66.1 writes Σ_zwc(h_z, Ŵ_z(t)) = wc(1, c(t)) + Σ_z[wc(h_z, Ŵ_z(t)) − wc(h_z, c(t))], and bounds the second sum per point by C_wcε₁d̄(z), assigned per domain through the c_X of §47.
  The far-domain terms carry no counterterm (45.1). Both runs use the clause, and V^B(Y)[·] is the same function in each occurrence, so the LF note's decomposition telescopes as in 44.1's caller paragraph.
- At the cut. Under the clause,

  irr(Δ)(𝐔) = Δ(Λ_j, 𝐔, z) − Δ(Λ_j, 1, z) − ΔβA(h_z, Ŵ) − N(Ŵ) = D_Ŵ,

  since Ŵ = P_n𝐔 on □₀ ⊃ supp h_z and P_n1 = 1. So 62.2 gives |irr(Δ)(𝐔)| ≤ dE₁(L^{j−n})^{4+β′}. This is a bound on irr(Δ) with the counterterm of the clause. With the counterterm read at 𝐔, as in the Cauchy note's l.108, the difference is the sum defect of the second bullet at c = 𝐔, and the available upper bound on it carries no age factor (below).
- At the entries. At the entries c(t) of §44 the clause gives ren_j(z; c(t)) = irr_j(z; Ŵ_z(t)), the near part with zero counterterm mismatch (57.1). Per domain, c_X of (G.266) reads Ŵ_z(t) too, so the per-X mismatch of 47.4 is zero. r_R of (G.268) reads the run-B composite at t = 1; its quartic parts are bounded as in 47.4, and its far tails compare the run-B composite with c^A, which needs the lift condition at the composites.

The size of the defect at the cut, with the counterterm read at 𝐔:

- The plaquettes on the support of h_z. The support lies within 2a_j ≤ 2L^nη of z, in □̃², where the cube's set has the scale n.
  - Ŵ is VAR's minimal configuration of the cube's set (RG I p.262 (iv)), which satisfies VAR's (1) with R = R₁, so §59 applies to Ŵ. Its data are averages of 𝐔, with e ≤ C_aC_FR_nε_n on the shell of each scale in its own normalisation (61.4), so at a point of the coarsest layer n, F ≤ B₃C_aC_FR_nε_n and |∂Ŵ − 1| ≤ B₃C_aC_FR_nε_nη²(L^nη)^{−2}.
  - 𝐔 is within the thresholds of the layer h with the ratio θ_J (62.2), so |∂𝐔 − 1| ≤ C_FR_hε_hη²(L^hη)^{−2} ≤ C_F(L + 1)(1 + β₀)²(h − n + 1)^{1/2}R_nε_nη²(L^nη)^{−2}, by CRE (2.8)–(2.9) as in 59.4.
  With C_P := C_F max(B₃C_a, (L + 1)(1 + β₀)²(h − n + 1)^{1/2}) both configurations have |∂U − 1| ≤ C_PR_nε_nη²(L^nη)^{−2} there, and |Φ_P| ≤ 2C_PR_nε_n(L^nη)^{−2}, by |log(1 + x)| ≤ 2|x| for |x| ≤ ½, with η the spacing of the lattice.
- The bound. As at the Cauchy note's l.243, a plane-pair action at either configuration is at most ½(2C_PR_nε_n)²(L^nη)^{−4}(2a_j)⁴ = 32C_P²(R_nε_n)²L^{4(j−n)}. A_ε(h_z, ·) is the sum over the 6 planes, and N has 36 plane-pair coefficients c_{PP′}. So the defect is at most 64c_ΔC_P²(R_nε_n)²L^{4(j−n)}, c_Δ := 6|Δβ| + 36 max_{PP′}|c_{PP′}|.
- The order. The bound carries (L^{j−n})⁴ and no factor (L^{j−n})^{β′}. On the strips the cube's set leaves the averages of the scales above the strip layer unconstrained where 𝐔's determining set fixes them, so Ŵ and 𝐔 differ there at the size of the data, and 61.2 and 61.4 give no smallness of Ŵ − 𝐔 on the support of h_z beyond that size. Summed over the generations, Δβ_j's bound C_βd_j carries no decay at the early generations. So the available bounds give no age factor for the defect; the clause removes it.

### 62.4 Status

Derived here, not reviewed in this form: 62.2, and the identity irr(Δ)(𝐔) = D_Ŵ under the clause (62.3). Quoted from the print: RG I p.262 (iv), p.273 l.39–42, p.275 l.2–7, p.280 l.25, and (3.30)–(3.34); CRE p.280 l.14–22, (3.49)–(3.50), (3.56), (3.57), and p.283 l.16–17; LFR II p.372 l.3–20 and p.373 l.2–6.

At real points, where □₀ satisfies (N), (5.1c) holds on the near domains that meet the cut,

  |irr(Δ)(𝐔)| ≤ dE₁(L^{j−n})^{4+β′},

with irr(Δ) taken with the counterterm of the clause.

Conditions of the result:
- R-data and R-near (55.1–55.2), the project's definitions;
- the counterterm clause of 62.3, a construction choice; that it leaves each run's quantity unchanged rests on 66.1's inclusion and its sums over z;
- the condition (a) at 𝐔, including the lift condition at 𝐔, for the far terms;
- the lift condition at the composites, as in the Cauchy note, open for every z;
- the thresholds of 59.4, 60.4, and 61.2 under (W-3), and the Cauchy note's §5 (l.74–76, l.108, l.124, l.140–148, l.243).

Open:
- the conditions of the result that are open: the condition (a) and the lift condition at 𝐔 = U_{1,2} near the cut (50.4, 56.4), and the lift condition at the composites;
- complex points (§68 treats them, with its status recorded there);
- the points whose □₀ violates (N), the points of the layer h + 1 whose near domain meets the strips, which 63.4 and 66.1 treat at the layer n − 1.

At the configurations of 57.1, the clause and 62.2 give (5.1c) wherever the configuration satisfies (I.1.11), (I.1.13), (I.1.14), and (iv) on □₀ and (N) holds; §64 treats the endpoints at ∂Y_i, with its status recorded there.

What this changes in the LF note (recorded here, not edited): the last part of its l.18 item, (5.1c) at the patch on the near domains that meet ∂Ω″^∼_{h+1}, is derived at real points under (N), with the counterterm clause and the conditions above. Under the clause the counterterm defect A(h_z, c(t)) − A(h_z, U_j(□₀, M^·(c(t)))) of its l.13 is zero, as R-data makes the term's defect zero.

## 63. The Near Domains That Meet a Finer Layer ((R-Δ^c-T))

This section treats (R-Δ^c-T) of the Cauchy note (l.14, l.154): (5.1c) at the points z ∈ Ω_n ∖ Ω_{n+1}, n > j, whose near domain □₀ meets a finer layer m < n. The layers below a CRE layer, and below a middle layer of an R-operation, are wider than the reach of □₀. So, away from the top N₀ layers of an R-operation, □₀ meets only the layer n − 1 below its own (63.2), and there the case m = 0 does not occur. On the layer n − 1 every input of RG I's Lemma 4 is larger by at most Ĉ := L³(1+β₀)² in the L^{−n}-scale. The margin of the Cauchy note's *Mixed radii.* absorbs Ĉ at n − j ≥ 5, and the direct bound covers n − j ≤ 4 (63.3). Away from the top N₀ layers the count against |Γ_m| of (2.43) is not needed. The top N₀ layers, n ≥ k′ − N₀ + 2 for an R-operation of the step k′, are §71's.

### 63.1 The Sources (Read)

- CRE p.279, last paragraph: z ∈ Λ_j^0 ∩ (Ω_n ∖ Ω_{n+1}), "the cube □ ∈ π_n such that z ∈ □", and the ∼-operation "in the L^{−n}-scale". CRE p.280 l.14–16: the configuration "restricted to Ω_n∖Ω_{n+1} coincides with a U_n-type configuration, but the difference is seen in bounds only".
- LFR II p.372 l.13: □₀ = □^{∼5}, "the operation ∼ is defined here in terms of M-cubes of the L^{−n}-lattice".
- CRE p.255 (2.5): R_j is the smallest number of the form L^r with R_j ≥ (log g_j^{−2})^r. (2.6)–(2.7): g_m ≤ (1+β₀)g_n and (log g_m^{−2})^p ≤ (1+β₀)(n−m)^{β₀}(log g_n^{−2})^p for n > m.
- CRE p.256 l.21–23: the domains Ω_j, Λ_j of the j-th transformation, "but not by the R-operation, are unions of MR_j-cubes in the lattice T_{L^{−j}}".
- CRE p.261 (2.34)–(2.39): the bounds of the class on X ∩ (Ω_n ∖ Ω_{n+1}).
- LFR I p.179 (1.10)–(1.12): N₀ with L^{−N₀+1}MR_{k−N₀+1} = M; Z″_k = (Z′_{k−N₀})^{∼3} and Z″_{k−N₀+1} = (Z′_{k−N₀})^{∼}, completed "to a sequence Z″_k, Z″_{k−1}, …, Z″_{k−N₀+2}, Z″_{k−N₀+1} in such a way that the complements of these sets form an admissible sequence of domains". LFR I p.179 l.20–24: the R-operation's domains are "based on partitions into M-cubes in the corresponding scales", and consecutive top layers are one M-cube of their own scale apart.
- §46 (46.2, (G.265), 46.4), and the Cauchy note's §5 (l.140–152).

### 63.2 The Near Domain Meets at Most the Layer Below (Derived)

Let z ∈ Ω_n ∖ Ω_{n+1} with n > j, so n ≥ 2. Ω_n is a union of cubes of the scale n, and π_n is compatible with them (CRE p.256 l.21–23, p.264), so □ ⊂ Ω_n. □₀ = □^{∼5} adds five layers of M-cubes, so every point of □₀ lies within 5M of Ω_n, in the units of the scale n. In these units the cubes of 46.2 have side MR_n.
- A layer of a T-operation. Where Ω_n is produced by the T-operation of the step n, 46.2 with j + 1 = n gives Ω_n ∩ (Z′_{n−1})^{∼8} = ∅ and Ω_{n−1}^c ⊂ Z′_{n−1}, so dist(Ω_n, Ω_{n−1}^c) ≥ 8MR_n.
- A middle layer of an R-operation. Where Ω_n is a layer h + 1 ≤ n − 1 ≤ k′ − N₀ of the R-operation of a step k′, (G.265) and 46.4 give dist(Ω″_n, (Ω″_{n−1})^c) ≥ MR_n. At n − 1 = h the same holds: Ω″_{h+1} ⊂ Ω_{h+1}^{∼5} and (Ω″_h)^c = Ω_h^c ⊂ Z′_h, so 46.2 gives 3MR_{h+1} on Z and where no earlier operation acted, and at least MR_{h+1} elsewhere by 46.4.

The condition (R6) is R_n ≥ 6 for every n. It holds for g small, by CRE (2.5). Under (R6) both distances are at least 6M > 5M, so □₀ ⊂ Ω_{n−1}. Hence, in these two cases, □₀ meets the layers n − 1, n, n + 1, … and no finer one: in (R-Δ^c-T), m = n − 1 ≥ 1, and the case m = 0 of the Cauchy note, where □₀ reaches Ω₁^c, does not occur. For an R-operation, □ ⊂ Ω″_n holds by LFR I (1.11)–(1.12) and p.179 l.20–21, since CRE p.256 l.21–23 excludes the R-operation's domains. At the top N₀ layers, n ≥ k′ − N₀ + 2, consecutive layers are one M-cube apart (LFR I p.179 l.21–24), and □₀ can meet several finer layers; these points are §71's.

### 63.3 Lemma 4 at the Enlarged Radii (Derived)

Let □₀ ⊂ Ω_{n−1} as in 63.2.
- The inputs. On the layer n − 1 the bounds (2.34), (2.36), and (2.39), written in the L^{−n}-scale, are those of the layer n times L², L³, and L or L², with α_{·,n−1} in place of α_{·,n}. By (2.6)–(2.7) at n − m = 1, α_{i,n−1} ≤ (1+β₀)²α_{i,n}, and the layer factor 1 − β_C(1 − 2^{−(k−n+1)}) is at most 1. On the layers n, n + 1, … the bounds are at most those of the layer n (Cauchy note l.148). So the restriction of the configuration to □₀ satisfies the conditions that the (N) case derives (Cauchy note l.144–148), with every radius multiplied by Ĉ := L³(1+β₀)². (iv) follows from RG I (1.17) at ξ = L^{−n}, with □₀ as Ω₀, at the multiplied radii, given (1.17)'s condition that α₀′ be sufficiently small (RG I p.263), which at the radius Ĉα_{0,n} is one more condition of g small once L is fixed. So the restriction lies in RG I's space at the radii (1+2β_I)Ĉα_{·,n}.
- RG I's conditions on the radii. B₃²O(1)Mα₀ < ½α₁ is homogeneous in the pair, so it holds. The smallness conditions O(1)MĈα_{1,n} ≤ β_I and (4B₃²O(1)M)²Ĉα_{0,n} ≤ β_I (RG I p.278 l.46 and l.64) hold for g small once L is fixed, since α_{i,n} = g_nC_i(log g_n^{−2})^{q_i}.
- The margin at n − j ≥ 5. With m := n − j, the inequalities of *Mixed radii.* become Ĉ(1+β₀)²m^{1/2}L^{−m} ≤ 1 and (1 + 7β_I)Ĉ(1+β₀)²m^{1/2}L^{−2m} + β_IL^{−2} < 0.97. At L = 2, β₀ ≤ 1/7, β_I ≤ 1/4, and m = 5 the left-hand sides are at most (8/7)⁴·5^{1/2}·2^{−2} ≤ 0.954 and (11/4)(8/7)⁴·5^{1/2}·2^{−7} + 1/16 ≤ 0.145. Both decrease in m ≥ 5 and in L ≥ 2. So each conclusion of the proof holds with the scale-j radii on its right-hand side, as in *Mixed radii.*.
- The bound at n − j ≥ 5. The proof of (5.1c) runs as in the Cauchy note's §5, with the background bounds multiplied by Ĉ. So |B| ≤ O(1)B₃MĈα_{0,n}L^{j−n}, and C_r becomes ĈC_r. The ratio α_{0,n}/α_{2,j} becomes Ĉ times larger, so ρ̄ becomes Ĉρ̄, and C_loc is taken at the ratio bound Ĉc₂^{−1}(1+β₀)²max(1, n−j)^{1/2}. C_α^♮ denotes C_α of the Cauchy note's *The constant.* with these three replacements. It depends on L, M, B₃, β_I, β₀, β_H, and c₂ and on Bałaban's equal-scale constants, and not on j, n, or k.
- The bound at n − j ≤ 4. The direct bound of *Mixed radii.* uses only the condition (a) of the class, so it holds at every n. For Σ_X|Δ| this is the Cauchy note's l.150. For |ΔβA(h_z, 𝐔)| and N(𝐔) it uses the plaquette bounds near z, which (a) gives at the scale-j radii through CRE (2.34) on X ∩ Ω_j for n = j (p.261 l.24), since z ∈ Λ_j⁰ ⊂ Ω_j. So |irr(Δ)| ≤ O(1)(2 + c₂^{−2})dE₀. Since (L^{j−n})^{4+β′} ≥ L^{−20} for n − j ≤ 4 and β′ < 1, this is at most O(1)(2 + c₂^{−2})L^{20}dE₀(L^{j−n})^{4+β′}.

So at the points of 63.2, (5.1c) holds with C_α^T := max(C_α^♮, O(1)(2 + c₂^{−2})L^{20}) in place of C_α, uniformly in j, n, and k. The counterterm with N, the far terms, and the lift condition at the composites are as in the (N) case. The bounds above are bounds on radii, so they hold wherever the (N) derivation holds: at real points, and at complex points under the Cauchy note's reading of (I.3.26).

C_α enters the Cauchy note only through E₁(α) = C_αE₀ and ε*_k = C_XC_KPL⁴C_α[2³C_TC_Gc_kμ_k + 4a_k]. There c_kμ_k and a_k vanish as g_k → 0, so C_α^T in place of C_α moves only the threshold on γ.

### 63.4 At the Cut

The strips lie in the class layer h (60.5, 61.2), that is in (Ω″_{h+1})^c. Let z be a point of a layer n ≥ h + 2.
- If n − 1 ≤ k − N₀, 63.2 gives □₀ ⊂ Ω″_{n−1} ⊂ Ω″_{h+1}.
- If n − 1 > k − N₀, z lies in the top N₀ layers. The separation MR_{k−N₀+1} in the units of the scale k − N₀ + 1 is MR_{k−N₀+1}L^{k−N₀+1−n} = ML^{k−n} in the units of the scale n, by L^{−N₀+1}R_{k−N₀+1} = 1. It is below 6M for L^{k−n} < 6, and M at n = k. The construction gives only lower bounds on the widths of the layers between Ω″_{k−N₀+1} and (Ω″_{h+1})^c, so whether the near domain of a top-layer point meets the strips is not decided here. These points are §71's.

So the near domains of the layers h + 2 ≤ n ≤ k − N₀ + 1 do not meet the strips (the layer k − N₀ + 1 is covered by 63.2's middle-layer bullet). Below the top N₀ layers, the points of 62.4 where (N) fails are the points of the layer h + 1 whose □₀ meets the strips, with m = h. At them the input of 62.2 holds at the radii (1+2β_I)Ĉα_{·,h+1}. On the strips the plaquettes and the current are within the thresholds of the layer h (61.2 under (W-3)), and 63.3's first bullet applies to them as to any point of the layer h. 62.2 and the identity irr(Δ)(𝐔) = D_Ŵ of 62.3 then give

  |irr(Δ)(𝐔)| ≤ dE₁(L^{j−n})^{4+β′},  E₁ := C_α^TE₀,

at real points, with the counterterm clause of 62.3 and the lift condition at the composites as in the Cauchy note.

### 63.5 Status

Derived here, not reviewed in this form: 63.2–63.4, away from the top N₀ layers of an R-operation. Quoted from the print: CRE p.255 (2.5)–(2.7), p.256 l.21–23, p.261 (2.34)–(2.39), p.279 (last paragraph), and p.280 l.14–16; LFR I p.179 (1.10)–(1.12) and l.20–24; LFR II p.372 l.13; RG I p.263 (1.17) and p.278 l.46 and l.64. Used from the notes: §46, the Cauchy note's §5 (l.140–152, *Mixed radii.* and *The constant.*), 61.2, and 62.2–62.3. New conditions: (R6), R_n ≥ 6, and (1.17)'s smallness at the radius Ĉα_{0,n}, both conditions of g small once L is fixed.

(R-Δ^c-T) holds at the points whose □₀ meets a layer of a T-operation or a middle layer of an R-operation, with C_α^T in place of C_α, as conditionally as the (N) case: the lift condition at the composites is §69's, and at complex points the bound holds under the Cauchy note's reading of (I.3.26). At the cut it holds at every point of 62.4 below the top N₀ layers where (N) fails.

Weakest step: the middle-layer separation of 63.2, which rests on 46.4 and (G.265).

Open:
- (R-Δ^c-T) at the top N₀ layers of an R-operation, n ≥ k′ − N₀ + 2, those whose □₀ may meet the strips included (§71);
- the fine side at the composites where □₀ meets more than one layer (the LF note's l.561), which 63.3 does not treat.

What this changes in the Cauchy note (recorded here, not edited): in (R-Δ^c-T) (l.14, l.154), away from the top N₀ layers of an R-operation, m = n − 1, so the case m = 0 does not occur and the count against |Γ_m| of (2.43) is not needed there; (R-Δ^c-T) is derived there with C_α^T in place of C_α.

## 64. The Near Domains at ∂Y_i and ∂Ω″^∼_{h+1} at the Endpoints

This section treats 57.3 at the endpoints of the joint line, at real points and at 𝐇_k(B′) = 0. The near-domain terms are those of R-data (55.1): a near term of z at a configuration 𝐔 is 𝐄^{(j)}(X, P_n𝐔), P_n𝐔 := U_n(□₀, M^·(𝐔)) on □₀ and 𝐔 outside, and by the clause of 62.3 the counterterm of z reads the same P_n𝐔. R-data at the newest scale is RG I p.275 l.1–5; its layer form and the clause are the project's construction, and 66.1 shows that they change no physical quantity. Under them the near-domain bound of 62.2 needs, on □₀, the member's plaquettes with the room of the class and the lift condition at the composite, and not the member's current on □₀ or its local-minimiser property on □₀. The far terms of z read the member itself and need its condition (a), its current included.

### 64.1 The Sources (Read)

- RG I p.262, Definition (i)–(iv), and p.263 l.24–25: the term is a function 𝐄^{(j)}(X, 𝐔, 𝐉) of the pair on U^c_j, and 𝐉 is a variable of the space, bounded by (1.14). (iv) bounds the composite's pair (U_n(M^·(𝐔)), J_n(M^·(𝐔))) by (1.16) on X̃^{−2}. RG I p.263 (1.17): for configurations satisfying (i)–(iii) with constants α₀′ and α₁′ smaller than α₀ and α₁, and the same bounds for U, (1.16) follows from the plaquette bounds through Proposition 9 of VAR, and (iv) holds for α₀′ sufficiently small.
- RG I p.275 l.1–15: in (3.24)–(3.25) "the variable 𝐉 replaces the function J_{k+1} as usual", the configuration enters through M^·(𝐔), and the term is read with the current J_j of its own argument, "determined by the analytic function 𝐄^{(j)}(X, 𝐔, 𝐉), as in (3.13)". RG I p.273 l.2–3: 𝐉 enters the operators of 𝐇_k(B′) (VAR (179)–(180)). RG I p.277 l.35: "In (3.34), which is of main interest for us, we have configurations 𝐔, 𝐀 only."
- RG I p.277 l.44–52 and p.278 (3.41)–(3.42): at 𝐀 = 0 the current of the composite is R(·)(L^{j−1}η)³J_{k+1}(M^·(𝐔)), bounded by (1+3β)α₀(L^{j−1}η)³ on □̃³.
- CRE p.280 l.16–17: "for the proof of Theorem 2 we put 𝐇_k(B′) = 0 in (I.3.28), or 𝐀 = 0 in (I.3.30)".
- LFR II (1.53) (p.370 l.30): U_{1,2} = U_2 off Ω″^∼_{h+1}.
- From the notes: 53.2 (Lemma A at the endpoints), §47 (the counterterm per domain), §49.5, §§59–61, 62.2–62.3, 63.2–63.3, 66.1, and §69.

### 64.2 The Current of 𝐔 on □₀ Is Not an Input of 62.2 (Derived)

With 𝐇_k(B′) = 0, as for (5.1c), the function (I.3.25) is 𝐄^{(j)}(X, U_j(□₀, M^·(U_{k+1}(□₀, M^·(𝐔))))), read with the current of its argument. It depends on the pair (𝐔, 𝐉) only through the data M^·(𝐔) on □₀: 𝐉 enters RG I's construction only through the operators of 𝐇_k(B′), which vanish here (p.277 l.35). The current that the proof bounds, in (3.42), is the composite's J_{k+1}(M^·(𝐔)), and the condition (iv) bounds it from the plaquettes by (1.17). So the inputs of 62.2 on □₀ are:
- (I.1.11);
- the plaquette part of (I.1.14), at α′₀ = (1 + 2β_I)α_{0,n}/(2B₃), the room of the class (the Cauchy note's l.147), so that (1.17) gives (iv) at the radius of the space;
- (ii), A′ = 0 at real points;
- (iv), by (1.17);
- the lift condition at the composites (§69), which places Lemma 4's output in run B's space through the pair lift.

The bound |𝐉| < γ₀ of (I.1.14) is a condition on a variable that the near function does not read, and 𝐉 = 0 meets it. The far terms of the same z read the pair (𝐔, J(𝐔)) through (3.13) and 𝐇_j (RG I p.273 l.2–3), and the condition (a) of the class, which contains the current bound s_{0,j}/C_{Q*} on X^∼ (the Cauchy note's l.110), is a hypothesis of 62.2 for them. So the current of 𝐔 is not used on □₀ by the near terms, and it is used by the far terms wherever their domains lie, □₀ ∖ □̃² included. The localisation remainder of (3.21) reads the current as well and vanishes at 𝐇_k(B′) = 0, since B_□ = 0. The variation groups, where 𝐇_k(B′) ≠ 0, are §70's.

By R-data and the clause of 62.3, the near terms and the counterterm of z at 𝐔 are their values at Ŵ := P_n𝐔 on □₀, 𝐔 outside, so irr(Δ)(𝐔) = D_Ŵ, and 62.2 gives

  |irr(Δ)(𝐔)| ≤ dE₁(L^{j−n})^{4+β′}

at every real configuration 𝐔 of the class with the inputs above and (a), the far terms being read at 𝐔. By 63.2 the near domain □₀ meets the layers n − 1, n, n + 1, … and no finer one, except at the top N₀ layers of an R-operation (§71); the case where □₀ reaches Ω₁^c does not occur. E₁ = C_αE₀ under (N), and E₁ = C_α^TE₀ where □₀ meets the layer n − 1 (63.3, 66.1).

Where 𝐔 is the local minimiser of its cube data on □₀, P_n𝐔 = 𝐔 on □₀ up to gauge, and irr(Δ)(𝐔) is Bałaban's quantity at 𝐔 without R-data: this is the case of the members U″_k, U^0_k, U_{k,Λ}, and U_k, by the inclusion of 66.1, and of run B's c^B at t = 0, by Lemma B of 51.4. At the other configurations the identity irr(Δ)(𝐔) = D_Ŵ is the definition of the near terms and of the counterterm by R-data and the clause, and 66.1's total shows that the fluctuation integral is unchanged by it.

### 64.3 At the Endpoints (Derived for U^0_k, U_{k,Λ}, and U_1)

At the endpoints of the joint line, 53.2 gives U(𝐁″_k^D(Y₁), M^·(U^0_k)) = U^0_k on Y₁, U(𝐁₁^D(Y₂), M^·(U_1)) = U_1 on Y₂ ∩ Ω″^∼_{h+1}, and U(𝐁_k^D(Y₃), M^·(U_{k,Λ})) = U_{k,Λ} on Y₃, each up to a VAR (4) gauge transformation, which the terms do not see (RG I (1.19)). The near domains lie inside Y_i: a term of the (1.59) branch is localised in a domain Y₀ ⊃ □₀ (LFR II p.372 l.17–18), the current domain X of p.373 is such a domain, and Y₁ ⊃ X, Y₂ ⊃ Y₁, and Y₃ ⊃ Y₂ (66.3). Off Ω″^∼_{h+1} the terms on Y₂ read U_{1,2} = U_2 ((1.53)).

One configuration per counterterm. Different near domains X of the same z can be assigned to different stages of LFR II's expansion and read different members. The counterterm of z is the sum of per-domain pieces c_X, each travelling with its own X̂ (47.2–47.3), so each near term Δ(X, ·) and its c_X are read at the one member that X̂'s stage reads, and 62.2's bound holds per X by the linearity of its proof (47.4). The term properties of the per-domain pieces on X̂ ∖ X are open (47.3), and this step rests on them.

The class conditions at real points at these members are derived: U^0_k by the LF note's own derivation; U_1 and U_{k,Λ} on Z^c by §49.5, with the plaquettes and the current on the fine layers by §59. So their plaquettes on □₀ are within the thresholds of the layer with the room of the class, and their pairs satisfy (a). Hence 64.2 applies, and (5.1c) holds on the near domains that meet ∂Y₁, ∂Y₂, and ∂Y₃ at real points at the endpoints, for the members U^0_k, U_{k,Λ}, and U_1, with the lift condition at the composites from §69, given the per-domain term properties of 47.3. At U_1 this excludes the collar points near Λ left open in 49.4.

The near domains that meet ∂Ω″^∼_{h+1}, where the terms read U_2 and U_{1,2}, are those that meet the cut, treated in §62 with the conditions of §60 and 61.2–61.4.

### 64.4 Status

Derived at real points, not reviewed in this form: 64.2 and 64.3, at 𝐇_k(B′) = 0, at the endpoints of the joint line, for the members U^0_k, U_{k,Λ}, and U_1.

Quoted from the print: RG I pp.262–263 (Definition, (1.15)–(1.17), (1.19)), p.273 l.2–3, p.275 l.1–15, p.277 l.35 and l.44–52, and (3.41)–(3.42); CRE p.280 l.16–17; LFR II (1.53) and p.372 l.17–18.

Construction premises: R-data in the layer form (55.1) and the clause of 62.3, with 66.1 for the claim that they change no physical quantity. Used from the notes: 53.2, §47, §49.5, §59, 62.2, 63.2–63.3, 66.1, and §69.

Weakest step: the per-domain assignment of the counterterm in 64.3, whose term properties on X̂ ∖ X are open (47.3).

Open:
- the term properties of the per-domain pieces c_X and R_z (47.3);
- the collar points near Λ at U_1 (49.4);
- the near domains that meet the top N₀ layers of an R-operation (§71).

Treated elsewhere, with their status recorded there: the interior points of the line, D(s) (§§54, 65, and 67); complex points (§68); the variation groups (5.1v) (§70); the near domains that meet the cut (§62); the lift condition at the composites (§69).

What this changes in the LF note (recorded here, not edited): in its l.19 item, the near domains at ∂Y₁, ∂Y₂, and ∂Y₃ at the endpoints, at real points, for U^0_k, U_{k,Λ}, and U_1, are derived given the open items above; the ∂Ω″^∼_{h+1} side is §62's, and D(s) and the complex points are recorded in §§67–68.

### 64.5 The Entries of §44 Without the Glued Member (Derived Under R-Data and the Clause)

irr_j(z; ·) of 44.3 is the sum over the near domains X of z only. At the entry c(t), R-data reads each near term at P_nc(t), and the clause of 62.3 reads the counterterm of z at P_nc(t). So

  ren_j(z; c(t)) = irr_j(z; c(t)) = irr_j(z; Ŵ_z(t)),

and (G.257) holds with its second term zero. At t = 0, P_nc^B = c^B on □₀ up to gauge (Lemma B of 51.4), so there the identity is Bałaban's; at 0 < t ≤ 1 it is the definition by R-data and the clause, with 66.1's total. The bound is taken at c(t) itself. irr_j(z; c(t)) is D_Ŵ of 62.2 at 𝐔 = c(t), in its one-family form, minus the far terms of z at c(t). By 64.2, |D_Ŵ| ≤ E₁(α)(L^{j−n})^{4+β′}, given the plaquettes of c(t) on □₀ within the thresholds of the layer with the room of the class, the bound (ii) on its A′, the lift condition at the composite (§69), and (a) at c(t). By (a) and CRE (3.48), the far terms are at most O(1)E₀(L^jL^{−n})⁵ ≤ O(1)E₀(L^{j−n})^{4+β′}, a sum over X near z, uniform in the volume (CRE p.280 l.7–8). These inputs are the entry's own class on the disc, the LF note's *The class at the entries.* (its l.528). At complex t they are taken under the Cauchy note's reading of (I.3.26) at complex 𝐔, as for every complex configuration of 𝒮_z.

So the bound on the first term of (G.257) does not use the membership of Ŵ_z(t) in 𝒮_z, and it does not use the current (2.36) of Ŵ_z(t) on □₀ ∖ □̃²: Lemma 4 reads only M^·(c(t)), and the composite is the local minimiser of these data by construction. Ŵ_z(t) enters only as the argument of the near terms, where Lemma 4 places it (44.2). That current is therefore not an input of 44.6. The other inputs of 44.6 stand: (N), or 63.3 where □₀ meets the layer n − 1, the top N₀ layers of §71, and the 𝐑 version at complex configurations.

## 65. The Representation Configurations at D(s): Three of the Four Points of 54.2

This section treats the conditions at U(𝐁^D(Y_i), D(s)) at interior points of the joint line, the item that 54.4 leaves open with four points. Points 1 and 2, the linear bound and the margin in VAR (172), are obtained by integrating VAR (190) along the line in steps, given a bound on the line twist. Point 4, the comparison with the thresholds, is reduced on Z^c to the LF note's weighted arguments with an envelope that is layer-adapted, as in §59, and that decays away from Λ, as in 49.4; what is open is listed in 65.4. Point 3, the band with the localisation parameters of 𝐇″_k, and point 4 inside Z are §67's.

### 65.1 The Sources (Read)

- VAR p.305 (172)–(173): for V = V′V₀ with V₀ satisfying (7) and |V′ − 1| < C₁ε₁, U_k(V′V₀)U_k(V₀)^{−1} = exp iη𝓗(B), with (19)–(21) at ε₂ = B₅ε₁, after U_k(V₀) is "transformed to the Landau gauge" (p.305 l.37; p.309 l.10). "We assume that C₁ is an absolute constant, hence B₅ is such a constant also."
- VAR p.308 (190): for x ∈ Δ(y), y ∈ Λ_j, y′ ∈ Λ_{j′}, the derivative δ𝓗_μ(B, x)/δB_ν(y′), its gradient, D*D of it, and Δ of it are bounded by O(1)[(L^jη)^{−1}, (L^jη)^{−2}, (L^jη)^{−3}, (L^jη)^{−3}](L^{j′}η)^{−d}exp(−⅛δ₀d(y, y′)).
- CRE p.256 l.29–31 (the history data |∂V_{j−1} − 1| < O(L²)ε_{j−1} on Γ_{j−1}), and CRE (2.5)–(2.9).
- 49.4 (*The ratio.* and θ_k), §59 (the layer bound R_nε_n), 54.1–54.2, and the LF note's (b) (*The profile.*, *The a priori inequality.*), its (c) (*The weighted bound.*, l.224), and its *The Fine Side at the Multiscale Chain.* (l.460–470).

### 65.2 The Linear Bound and the Margin (Points 1 and 2, Derived)

Write D(s) = e^{iB(s)}D(0), with D(0) the endpoint data of 53.2. Split [0, 1] at t₀ = 0 < t₁ < ⋯ < t_K = 1 so that |(t_{i+1} − t_i)B(s)| < C₁ε₁ on every data bond, with K := ⌈2 sup|B(s)|/(C₁ε₁)⌉ + 1. Each base D_i := e^{it_iB(s)}D(0) satisfies VAR (7) with the constant ε₁ + O(1)sup(a_j|A_s| + a_j²|∇A_s|) ≤ (1 + O(1)C(ε₀)C_U(M))ε₁. This is VAR's ε₁ at a larger value, small for γ small once L, R, M, M₁, and ε₀ are fixed. The bound on A_s used here is the LF note's (b) at the global ε₁, and the relation between B(s) and A_s, B(s) the data of the twist e^{isA_s}, is not written out (65.4). So (172) holds at every step with VAR's absolute C₁, and (173) gives the absolute B₅. The constant that depends on M enters only the smallness of ε₁, which is a threshold on γ.

At each step, VAR (190) holds at the base D_i and along the segment. Integrated along it, it gives U(D_{i+1}) = exp(iη𝓗_i)U(D_i) with

  L^jη|𝓗_i(x)| + (L^jη)²|∇𝓗_i(x)| + (L^jη)³|D*D𝓗_i(x)| ≤ O(1)Σ_{y′}e^{−⅛δ₀d(y,y′)}(t_{i+1} − t_i)|B(s)(y′)|,

the factor (L^{j′}η)^{−d} cancelling the measure of the data point y′. Each 𝓗_i is defined after the Landau gauge transformation at its base D_i, and D*D𝓗_i is covariant at U(D_i). The product over the K steps is exp(iη𝓗) by the Baker–Campbell–Hausdorff formula, with a correction quadratic in the 𝓗_i; the gauge transformations between the steps' Landau gauges and the change of the background of D*D from U(D_i) to U(D(0)) are also quadratic in the 𝓗_i, and they are absorbed with it. Since Σ_i(t_{i+1} − t_i) = 1, the bound holds for 𝓗 with O(1) doubled, for γ small. This is the bound linear in the ratio that point 1 asks for. It carries the current through D*D𝓗, and its constant is absolute.

### 65.3 The Comparison With the Thresholds on Z^c (Point 4, Reduced)

The constant ε₁ of the LF note's *The profile.* and *The Fine Side at the Multiscale Chain.* enters only through the sources: the local regularity of the cubes (the blocking artifact and the residual, at the layer of their point), and the depth of U₀ through (c). §59 bounds the first at a point of the layer m by C_FR_mε_m, from the history data O(L²)ε_m. The LF note's (c) bounds the second by C(M)R_kε_k times e^{−(δ₀/16)d(·,Λ)}. Put

  ê(x) := C_e[R_{j(x)}ε_{j(x)} + R_kε_ke^{−δ_Λd(y,Λ)}], δ_Λ := min(δ₀/16, δ_f/4),

with C_e := max(C_F, C(M)). By CRE (2.8)–(2.9), R_{j′}ε_{j′}/(R_jε_j) ≤ (L+1)²(1+β₀)²max(1, |j−j′|) ≤ (2L+2)^{|j−j′|+2}, using (1+β₀)² ≤ 4 and max(1, m) ≤ (2L+2)^m. By PRT2 (2.60), d(y, y′) ≥ RM(|j − j′| − 1), so ê(y′)/ê(y) ≤ (2L+2)³e^{(log(2L+2)/(RM) + δ_Λ)d(y,y′)}.

The LF note's weighted arguments then hold with the weight π(x)ê(x) in place of π(x)ε₁. Each of them pays the weight ratio with part of the decay of its kernel:
- the propagator count of *The propagator.*, at the rate δ₀;
- the chains of the kernel form, at 27δ₀/128 − δ₀/128;
- the weights Ŵ of *The Fine Side at the Multiscale Chain.*, at ½δ_f.

The new condition is (E-W): log(2L+2)/(RM) ≤ δ₀/128 and ¼δ_fW ≥ (7/3)log L + 3log(2L+2) for W = RM and W = LM₁, the quarter of δ_f left after δ_Λ ≤ δ_f/4 pays the factor e^{δ_Λd} of ê in Ŵ. It holds for M and M₁ large. The constants of these arguments are multiplied by (2L+2)⁵. The smallness conditions (T-π) are on ε₄ ∝ sup ê, which is small for γ small. So the line twist at the layer m satisfies

  a_m|A_s| + a_m²|∇A_s| ≤ d̄_ℓ(x) := C′_U(M)(ε/a_{min(j(x),n)})^{(1−ε₀)/3}ê(x),

with C′_U(M) := (2L+2)⁵C_U(M).

On Z^c the comparison is uniform. The first part of ê gives C_eR_mε_m/α_{0,m} ≤ C_eL(A₀/C₀)(log g_m^{−2})^{p₀+r−q₀}. The second part is 49.4's h(x) with δ_Λ for δ₀/16, and 49.4's bound b_m(y) ≤ 2 holds with δ_Λ under δ_ΛLM ≥ 1 and M ≥ M(δ_Λ, L). So d̄_ℓ(x) ≤ θ′_k α′_{0,m}/2, with θ′_k := 3C′_U(M)C_eL(A₀/C₀)(1+β₀)16B₃2^{q₀}(log γ^{−2})^{p₀+r−q₀} → 0 for γ small, under the (T-Λ) choice q₀ > p₀ + r. No condition on k − m appears. With 65.2, each quantity of (1.64)–(1.69) at U(𝐁^D(Y_i), D(s)) on Y_i^0 ∩ Z^c differs from its value at the member by at most O(1)θ′_k times its threshold at α̃′/2, which is below the slack of 49.5's thresholds for γ small.

### 65.4 Status

Derived here, not reviewed in this form, at real s: 65.2, given the bound on the line twist of the LF note's (b); 65.3's envelope ê and its ratio bound. Quoted from the print: VAR (172)–(173) (p.305, with the Landau gauge of p.305 l.37 and p.309 l.10) and (190) (p.308); CRE p.256 l.29–31 and (2.5)–(2.9); PRT2 (2.60). Used from the notes: 49.4–49.5, §59, 53.2, 54.1–54.2, and the LF note's (b), (c), and *The Fine Side at the Multiscale Chain.*. Conditions: (E-W), which holds for M and M₁ large, and q₀ > p₀ + r (55.7).

Weakest step: 65.3's transfer of the LF note's weighted arguments from the weight π(x)ε₁ to π(x)ê(x).

Open:
- the transfer itself: ε₁ enters the LF note also through (c)'s nonlinear comparison (σ̄ ∝ ε₁², C_Lε₁, the regularity along the segment), through the global ε₁ inside d̄ of its §1, and through VAR Theorem 1's uniform curvature bounds in *The Fine Side at the Multiscale Chain.*, which need §59 as a pointwise bound R_mε_m at every layer m; these uses are not redone with ê;
- the comparison of (1.64)–(1.69) at U(𝐁^D(Y_i), D(s)) with the member for the currents and the J_{p,X} (third order) and for the U_{p,X}(M^·(·)) at the other scales: 65.2's bound carries D*D𝓗, and its transfer to these quantities is not written;
- 65.2's base condition: the bound on the line twist at interior s and the relation between B(s) and A_s, which 65.3 itself derives with ê, so the order of the two steps is to be fixed;
- so points 1, 2, and 4 of 54.2 on Z^c are not closed here.

Treated elsewhere, with their status recorded there: point 3, the boundary band with the localisation parameters of 𝐇″_k (LFR II p.373 l.29–34 and p.376 l.12); point 4 inside Z; (5.1c) at D(s) (§67); complex s (§68).

## 66. The Composite at the Finest Layer Met, the Case n = j, and the Sums Over z

This section treats the composite of the near domains that meet the cut at the finest layer that □₀ meets, the case n = j of 62.2, the total under the clause of 62.3, the points of 63.2, and the sums over z. It fixes the evaluation radius at which the callers read (5.1c), and it states the scope of 64.2–64.3.

### The Sources (Read)

- The Cauchy note's *Mixed radii.* (its l.150): at n = j, Σ_X|Δ(X, U, z)| ≤ O(1)dE₀, since by the condition (a) of the class U lies in the norm class 𝒫_j(X; r) of every X.
- RG I pp.272–281, every occurrence of M:
  - the background bounds B₃O(1)Mα₀ ((3.26)–(3.27), p.275 l.34–35; p.276 l.43; p.277 l.4) and B₃²O(1)Mα₀ (p.277 l.50), and the axial-gauge bounds |V(b) − 1| < O(1)Mα₀ and |v − 1| < O(1)Mα₁ (p.275 l.24), with the assumption that Mα₀ and Mα₁ are small (p.275 l.28);
  - the factor exp(−½δ₀M(L^jη)^{−1}) of (3.17) (p.273 l.26), and the factors exp B₃²O(1)Mα₀ and exp 4B₃²O(1)Mα₀L^{−1}η (p.278 l.40–41 and l.58–59);
  - the smallness conditions (4B₃²O(1)M)²α₀ ≤ β (p.278 l.64), O(1)Mα₁ ≤ β (p.279 l.2), and B₃(B₃O(1)Mα₀)² < βα₀ (p.279 l.12);
  - the ratio condition B₃²O(1)Mα₀ < ½α₁ (p.277 l.54);
  - the distance M(L^jη)^{−1} of the localisation (p.274 l.31).
- RG I p.273 l.2–3 and l.39–42.
- [14] (REG) (1.3)–(1.6), p.77: dist(Ω_p^c, Ω_{p+1}) > RM₁L^pη, and each Ω_p a union of M₁L^pη-cubes.
- CRE p.256 l.21–24: Ω_j and Λ_j, "determined by the j-th renormalization transformation, but not by the R-operation", are unions of MR_j-cubes in T_{L^{−j}}, with boundaries at least 2MR_j apart.
- LFR I (1.12)–(1.13), p.179: Ω″_j = (Z″_j^c ∩ Z) ∪ (Ω_j ∩ Z^c) for j = k, …, h + 1, and Ω″_j = Ω_j for j ≤ h.
- LFR II p.370 l.4–8 (𝐁″_k coincides with 𝐁_k on Λ^c) and (1.53), p.372 l.17–18 ("domains Y₀ ∈ 𝐃_k containing □₀"), and p.373 l.2–3 and l.12–13.
- VAR p.278 (2): the class 𝔘_k({Ω_j}, ε₀), with the plaquette condition and |D*∂U| < ε₀η²(L^jη)^{−3}, and l.32–33: "for ε₀ sufficiently small there is at most one critical orbit".

### 66.1 The Composite at the Finest Layer Met, and the Total Under the Clause (Derived)

For a point z with near domain □₀, let m(□₀) be the finest block scale on □₀ over the determining sets of all the members: 𝐁″_k for U″_k and U^0_k, and 𝐁_k for U_{k,Λ} and U_k. (N) is read for the domains of every member. Where □₀ ⊂ Λ^c, 𝐁″_k = 𝐁_k on □₀ (LFR II p.370 l.4–8), so (N) for the run's Ω_n gives m(□₀) ≥ n, with equality since □₀ ∋ z meets the layer n, and at the points of 63.2 m(□₀) = n − 1. Where □₀ meets Λ, the blocks of 𝐁″_k on □₀ ∩ Λ are those of the domains {Ω″_j} of LFR I (1.12)–(1.13), and (N) is read for {Ω″_j}: □₀ ⊂ Ω″_n. Off Z these domains are the run's, Ω″_j ∩ Z^c = Ω_j ∩ Z^c. Inside Z they are the R-operation's, and the points whose □₀ there meets a layer finer than n − 1 are those of §71, where P_□ is not used. Let P_□ := U_{m(□₀)}(□₀, M^·(·)) be RG I's local function with the cube sequence □₀ ⊃ □₁ ⊃ ⋯ ⊃ □_{m(□₀)} in the L^{−m(□₀)}-scale, extended as equal to its argument outside □₀ (the Cauchy note's l.124, with the scale m(□₀) for n). Under (N), P_□ = P_n.

*The inclusion.* Let c be the minimal configuration of a determining set 𝐁 whose blocks that meet □₀ are of scales ≥ m(□₀). By the choice of m(□₀) this holds for each of the members U″_k, U^0_k, U_{k,Λ}, and U_k. P_□'s constraints fix W = c off □₁ and the averages of the scale p on □_p ∖ □_{p+1}, with each □_p a union of blocks of the scale p (RG I p.273 l.39–42, (1.3) [14]). A block of 𝐁 of the scale q ≥ m(□₀) that meets □₀ splits into blocks of the scales of the shells it meets, each inside one shell, since the grids are L-adic and aligned: every block of the scale p is a union of blocks of the scale p − 1, and every □_p is a union of blocks of the scale p (RG I p.273 l.39–42, (1.3) [14]). A node of 𝐁's averaging tree of the scale r can straddle ∂□_s only if r > s, and each child of such a node lies in a single shell of scale at most the child's scale, so it is fixed through M^{r−s}∘M^s. The averaging paths stay inside the two endpoint blocks. The block's average is the composition of the one-step averages of its pieces, M^q = M^{q−p}∘M^p. So every W in P_□'s constraint set satisfies 𝐁's constraints, and c is in that set. c minimises the action over 𝐁's constraint set, so it minimises it over the smaller set.

The uniqueness goes through Lemma A of 51.4 with Ω₀ = T_η and Ω = □₀. Its hypotheses hold: the band width RM₁η ≥ 2η, the refinement of the descent above, the class condition, and the data condition (VAR p.278). The class condition is VAR's (2), the plaquette condition and the derivative condition |D*∂U| < ε₀η²(L^jη)^{−3}. Both hold since the coarser layer bounds are at least the member's bounds at its own layers, by the same monotonicity. At U″_k it rests on the LF note's §4(d). c is a local minimum on 𝐁's constraint set, so it is critical on the smaller set, and VAR's uniqueness of the critical orbit (p.278 l.32–33) applies. So P_□c = c on □₀ up to a gauge transformation.

The same argument, with the scale j in place of m(□₀), gives U_j(□₀, M^·(P_□𝐔)) = P_□𝐔 for every 𝐔 of the regular real class, and at complex 𝐔 of the class by analytic continuation, which is the identity between the reading of 62.2 and (G.256). It needs m(□₀) ≥ j and U_j's cube sequence equal to the prefix □₀ ⊃ ⋯ ⊃ □_j of P_□'s. The prefix is a choice within [14] (1.3)–(1.6), and m(□₀) ≥ j holds under (N), and at the points of 63.2 for n − 1 ≥ j.

*The total.* Under R-data and the clause of 62.3, read with P_□ for P_n, every application of (1.59) is exact. The chain is U″_k → U^0_k → U_{1,2} = U_1 → U_{k,Λ} → U_k on Z^c ((1.51), (1.54), (1.57), (1.58)). Along it the brackets telescope, and the term and the counterterm at the first configuration are their values at P_□U″_k. By the inclusion this is U″_k on □₀, at every z. So the quantity in the fluctuation integral is Bałaban's at every z. U_1 and U_{1,2} are intermediate expansion points, and they cancel in the total. The brackets with the background U_{1,2} (LFR II p.373 l.2–3) remain separate terms of the new action and take 62.2's bound at P_□U_{1,2}. At t = 0 the LF note's entries are run B's members c^B, and the clause reads them as themselves, by the inclusion. At t = 1 the entry ι_Yc^A is a one-step lift, not a member, and the clause reads it at P_□ι_Yc^A ≠ ι_Yc^A (this is the r_R term of 62.3). V^B(Y)[·] is the same function in each occurrence, so f(1) cancels in the decomposition. The physical quantities are run A's terms at c^A and run B's at c^B, each read at its own run's P_□ and fixed by the inclusion. So the clause changes no physical quantity. The clause preserves gauge invariance, since A(h_z, ·) is G^c-gauge invariant and P_□ is gauge covariant.

*The bound at the points of 63.2.* With P_□ = P_{n−1}, the term is read at the composite of the scale n − 1, and the (N) derivation runs at the layer n − 1. □₀ ⊂ Ω_{n−1} meets no layer finer than n − 1 (63.2), so (N) holds for the layer n − 1. The cube □₀ has the side 11LM in the units of the scale n − 1, so RG I's M becomes LM. By the sources above, the side enters RG I pp.272–281 in the following ways, and each holds at LM:
- The background bounds B₃O(1)LMα₀ and B₃²O(1)LMα₀, the axial-gauge bounds O(1)LMα₀ and O(1)LMα₁, and the factors exp B₃²O(1)LMα₀ and exp 4B₃²O(1)LMα₀L^{−1}η are bounds, not conditions, and LMα₀ and LMα₁ are small for γ small.
- The smallness conditions (4B₃²O(1)LM)²α₀ ≤ β, O(1)LMα₁ ≤ β, and B₃³O(1)²L²M²α₀ < β hold for γ small, since α₀, α₁ ∝ g.
- The ratio condition B₃²O(1)LMα₀ < ½α₁ is not a "g small" condition at q₀ = q₁. It holds by the choice C₁ > 2B₃²O(1)LMC₀, which CRE's "sufficiently large" allows (p.259 l.50). This is the Cauchy note's l.952 condition with LM for M. θ_ι depends on C₁/C₀ and is fixed after this choice.
- The localisation distance M(L^jη)^{−1} of p.274 l.31 and the factor exp(−½δ₀M(L^jη)^{−1}) of (3.17) become LM(L^jη)^{−1} and exp(−½δ₀LM(L^jη)^{−1}), which give more decay.

The age factor is (L^{j−n+1})^{4+β′} ≤ L⁵(L^{j−n})^{4+β′}. At n − 1 = j the direct bound of 66.2 applies. So (5.1c) holds at these points with E₁ := L⁵C_α(LM)E₀, where C_α(LM) is C_α with LM for M. The premise □₀ ⊂ Ω_{n−1} is 63.2, which rests on 46.2 and 46.4. 63.3 stays as a bound at P_n𝐔 for the configurations of 𝒮_z.

*The sums over z.* Under the clause, at an entry c(t) with 0 < t < 1, each z reads its own composite Ŵ_z(t) = P_□c(t), so Σ_zA(h_z, ·) is not A(φ_j, ·) at one configuration. The sum at one configuration is used for the weight-change part wc(h, W) of the blocking artifact (47.4's remaining far tails, the LF note's l.14), which cancels in Σ_z at one configuration since it is linear in h. At fixed W, Σ_zwc(h_z, W) = wc(1, W), so

  Σ_zwc(h_z, Ŵ_z(t)) = wc(1, c(t)) + Σ_z[wc(h_z, Ŵ_z(t)) − wc(h_z, c(t))].

Here z runs over T^{(j)} (CRE (3.65)), and Σ_zh_z = 1 on T_{L^{−j}} (the Cauchy note's l.78). The first term is the sum at one configuration. In the second, wc(h_z, ·) is at most 768C₀²(ε/a_j)ε₁² per point per generation for an O(1) coefficient (47.4), with C₀ §9's field constant, not CRE's C₀ of (2.28). It is a quadratic form in the plaquette fields (47.4), which are ≤ ε₁ in the units of the layer, so with the polarisation factor 2 its derivative is at most 4·768C₀²(ε/a_j)ε₁ per unit move in those units.

Ŵ_z(t) and c(t) share their P_□-data, so their difference is bounded through t = 0, where both are c^B, by the triangle inequality:

  |Ŵ_z(t) − c(t)| ≤ |P_□c(t) − P_□c^B| + |c^B − c(t)| ≤ (K_P + 1)|t|σ_c ≤ 2K_P|t|σ_c.

Here K_P := max(1, C_{65.2}C_av) is the Lipschitz constant of P_□ from the data to the configuration, in the units of the layer: the data of c(t) differ from those of c^B by at most C_av|t|σ_c, and 65.2's linear bound (VAR (174) with the operators of PBG Theorem 3.4) gives the rest. With |t|σ_c ≤ C(ε₀)d̄ (§44.7, with the fine side), each difference is at most 6144C₀²K_PC(ε₀)(ε/a_j)ε₁d̄ per point per generation. Since ε/a_j = L^{−(j−j_ε)} is geometric in j, the sum over the generations is at most 12288C₀²K_PC(ε₀)ε₁d̄ per point. At t = 0 the difference vanishes, by the inclusion. At t = 1 it is the r_R term of 62.3, and the bound above covers it.

*The absorption.* The per-point term is at most C_wcε₁d̄(z) with C_wc := 12288C₀²K_PC(ε₀), and d̄(z) ≤ C_U(M)(ε/a_{min(j(z),n)})^{(1−ε₀)/3}ε₁ (the LF note's l.632; its l.237 is the case of the layers ≥ n). It is assigned per domain: wc(h_z, ·) enters through the counterterm of the near-domain terms of z, which per domain X is the c_X of §47, and §47.4 assembles the per-X pieces into the domain Y ⊃ X of the term (66.3: □₀ ⊂ Y_i). So the term at z goes with the domains Y of the near-domain terms of z, as the LF note's per-point variations do. Its form is that of the LF note's variation, C(ε₀)d̄ per point, with the constant C_wcε₁ ≤ 1 for γ small in place of C(ε₀). At the layers ≥ n the factor (ε/a_n)^{(1−ε₀)/3} absorbs R_k as in the LF note's l.349, per point of the history. At a layer m < n the LF note's l.631–632 split applies verbatim to a quantity of this form: a domain that is not deep has ≤ C_hθ̃^m ≤ C_hθ̃^{k_s/8} per point, and a deep one is bounded in the LF note's (e).

*Complex t.* On the disc |t| ≤ 1/(2r(Y)) the same bound holds with |t|σ_c ≤ ϱ/2 (68.2). The derivative bound of the quadratic form is a bound on the class, and the configurations of the disc lie in it at the evaluation radius (66.4).

### 66.2 The Case n = j (Derived)

(N) at n = j holds: z ∈ Λ_j lies at distance at least 2MR_jL^jη from Ω_j^c (CRE p.256 l.23–24), and □₀ = □^{∼5} lies within sup-distance 6ML^jη of z, since z need not be the centre of □; 6M ≤ 2MR_j for R_j ≥ 3. So □₀ ⊂ Ω_j, and P_□ is at the scale j. CRE's separation is stated for the domains not determined by an R-operation (p.256 l.21–22). For the domains that an R-operation determines, (N) at n = j is §71's and §46.4's.

At n = j the term reads the composite Ŵ := U^A_j(□₀, M^·(𝐔)) under the clause of 66.1. Its data D = M^·(𝐔) at an evaluation point have ε₁(D) ≤ c_D(1 + C₁/C₀)ρ_ev,0 (69.4, with ρ_ev of 66.4 for θ_ιr). By 69.3 and 69.4, Ŵ and ι_XŴ then satisfy the conditions (i)–(iii) on X at

  (c_U(B₃ + B₅) + C_tw^cC_ι)ε₁(D) ≤ ρ_ev/(2B₃θ_ι) = θ_ιr/(2B₃),

by the definition of θ_ι (69.4). (iv) follows by RG I (1.17) at θ_ιr. Run A's current is that of the minimiser at the data D, which is at most O(1)(B₃ + B₅)ε₁(D) in the units of the layer by Proposition 9 and (19)–(21), the B₃ part from the real minimiser U(V₀) and the B₅ part from the twist e^{iη𝓗}. With ε₁(D) ≤ c_D(1 + C₁/C₀)θ_ι²r_{0,j}, this is at most θ_ιr_{0,j}/C_{Q*} by θ_ι ≤ [C_{Q*}O(1)(B₃ + B₅)c_D(1 + C₁/C₀)]^{−1} (69.4). The lift's current follows by the Cauchy note's *Complex domain.* So Ŵ lies in 𝒫_j(X; θ_ιr) for every near X, which is the norm class of d.

The Cauchy note's direct bound then applies at Ŵ: Σ_{X⊂□̃²}|Δ(X, Ŵ, z)| ≤ O(1)dE₀, with d on 𝒫_j(X; θ_ιr). G is analytic there, since 𝒫_j(X; θ_ιr) ⊂ 𝒫_j(X; α′). The far terms are bounded at the evaluation points 𝐔, which lie in the class at ρ_ev = θ_ι²r (66.4), so that their norm d on 𝒫_j(X; θ_ιr) applies. The terms at U = 1, ΔβA(h_z, Ŵ), and N(Ŵ) carry d through Π^Δ, with the factor (α/r)² of the Cauchy note replaced by (α/(θ_ιr))². So (5.1c) holds at n = j with C_α ≥ O(1)(2 + 64B₃²θ_ι^{−2}c₂^{−2}). Lemma 4 is not used at n = j.

### 66.3 The Scope of 64.2 and 64.3 (Derived)

- The current. The current condition (2.36) on □₀ and the 𝐉-bound of (I.1.14) are not inputs of the near-domain term at 𝐇_k(B′) = 0 (64.2). The condition (a) of the class is a hypothesis of 62.2, and it carries the current of the pair on every X ∋ z. The far terms read that current through (3.13) and through 𝐇_j (RG I p.273 l.2–3). The localisation remainder of (3.21) reads it too, and it vanishes at 𝐇_k(B′) = 0 since B_□ = 0. So "without its current" in 64.2 means without the condition on □₀. At D(s) the condition (a), with its current, is needed (67.4). The Cauchy note's l.142 and l.146 and 62.2 list "(2.36) gives the 𝐉-bound of (I.1.14)" as an input of the near-domain term; at 𝐇_k(B′) = 0 it is not one.
- The near domains stay inside Y_i. A term of the first part from the (1.59) branch is localised in a domain Y₀ ⊃ □₀ (LFR II p.372 l.17–18). The terms of the (1.60) branch, with σ₀ disjoint from "□₀, or X" (p.373 l.12–13), are localised in domains containing X; they are far terms with no near domain. For the (1.59) branch, the current domain X of p.373 is such a domain, and Y₁ ⊃ X, Y₂ ⊃ Y₁, Y₃ ⊃ Y₂. So □₀ ⊂ Y_i, and no term lies outside Y_i. This does not keep □₀ out of the boundary layers Y_i ∖ Y_i^0. Those near domains are the near domains at D(t, s), treated in 67.3–67.4 and 68.4.
- The scope of 64.3. The class conditions at the endpoints are those derived at real points: U^0_k by the LF note's own derivation, U_1 and U_{k,Λ} on Z^c by §49.5, U_2 and U_{1,2} by §60 and 61.2–61.4. The identities of 53.2 are at unlocalised 𝐇, and §67 extends them to the localisation parameters at real s as perturbations of the thresholds. The far terms at 1 are subtracted in 64.5 as in irr(Δ). U_{1,2} = U_2 off Ω″^∼_{h+1} is (1.53) (p.370 l.30), not p.373.

### 66.4 The Evaluation Radius (Derived)

d_j is the norm on 𝒫_j(X; θ_ιr) (69.6). The callers evaluate (5.1c) at specific configurations, not on the whole class. Let ρ_ev := θ_ι²r, componentwise. Every evaluation point lies in the class at ρ_ev:
- *Real points.* Their quantities are O(ε_m) at the layer m, and α′_{i,m}/ε_m → ∞ (the LF note's *The room at real points.*). So they lie at ½ρ_ev for γ small, uniformly in the layer, since θ_ι does not depend on γ.
- *The line's disc and complex s.* The moves are at most θ_ι²r_{0,j}/8 by 68.4 with c_ρ of 68.2, and θ^c_k(κ₁) → 0.
- *The points of the Cauchy note's §8.2.* Lemma 4 bounds α₃ only from above (2B₃α₃ ≤ βL^{−2}α₀, B₃α₃ < ½α₁), so α₃ is taken θ_ι² times its value at the radii r of the Cauchy note's §8.2. Then m_k = ½α₃ ≤ βL^{−2}θ_ι²r_{0,k}/(4B₃) ≤ ρ_ev/16, since β ≤ ¼, L ≥ 2, and B₃ ≥ 1. Against §8.2 at the radii r the cost is θ_ι^{−10} in the remainder (I.3.54), whose bound is E₀α₃^{−5}|B|⁵ (p.280 l.39) and which enters C_α through C_r⁵, and θ_ι^{−2} in T₀ = m_k/ϑ_k ≥ 2, which still holds for γ small since T₀ grows as a power of log g^{−2}. Both are constants independent of γ. θ_ι depends on C₁/C₀, B₃, B₅, c_D, C_{Q*}, C_tw^c, and C_ι, not on C_α or γ, so there is no circularity. 69.5's condition holds a fortiori.

### 66.5 Status

Derived, not reviewed in this form, given the open inputs listed below: 66.1–66.4. Quoted from the print: RG I pp.272–281 (the occurrences of M listed in the sources), p.273 l.2–3 and l.39–42, (1.17), and (I.3.54); [14] (1.3)–(1.6), the union-of-blocks property being (1.4); CRE (3.65); VAR (2) and p.278 l.32–33; CRE p.256 l.21–24 and p.259 l.50; LFR I (1.12)–(1.13); LFR II p.370 l.4–8 and (1.53), p.372 l.17–18, and p.373 l.2–3 and l.12–13. Used from the notes: 51.4 (Lemma A), 62.2–62.3, 63.2–63.3, 64.2–64.5, 65.2, 68.2–68.4, 69.3–69.6, §47 and 47.4, the Cauchy note's §5 (l.78, l.124, l.140–152), *Mixed radii.*, *Complex domain.*, §8.2, and §8.6, and the LF note's l.237, l.349, l.631–632, and §4(d).

New conditions: C₁ > 2B₃²O(1)LMC₀ (the Cauchy note's l.952 condition with LM for M); α₃ reduced by θ_ι² against §8.2; θ_ι ≤ 1/(8B₃), with the factor C_{Q*}^{−1}; R_j > 3; K_P ≥ 1 by its definition; the lower bound C_α ≥ O(1)(2 + 64B₃²θ_ι^{−2}c₂^{−2}) of 66.4.

Derived at real points, and at complex t through 68.2, given the open inputs below: the case n = j of 62.2, given §69; the total under the clause, which at U″_k rests on the LF note's §4(d); the composite at the points of 63.2, with E₁ := L⁵C_α(LM)E₀; the sums over z, as a per-point term.

Used from the notes besides those above: §44.7, 46.4, §49.5, §60, 61.2–61.4, §67, §71, and the LF note's *The room at real points* and l.468.

The weakest steps:
- 66.4's reduction of α₃ by θ_ι, whose cost in the Cauchy note's §8.2 is counted in constants only.
- 66.1's absorption at the layers < n through the LF note's l.631–632 split, which rests on that note's unreviewed (e).
- 66.1's reading of (N) inside Λ for the domains {Ω″_j}, which hands the points whose □₀ meets a layer finer than n − 1 there to §71.
- The uniqueness of 66.1, through Lemma A of 51.4.

Open:
- the volume-free bound of the sums over z: 66.1's absorption uses the LF note's l.631–632 split, which rests on that note's open (ii) and, for the per-Y split, (iii); the per-Y assignment of wc(h_z, ·) through §47 is not checked against double counting, and the LF note's l.14 records the assignment of A(h_z, ·) among the Y as open;
- 66.4's change of the polydisc from r to θ_ιr and of the statement from every 𝐔 in 𝒮_z to the points at ρ_ev: its exhaustiveness at the callers and the inductive replay (68.4, 69.6) are not shown, the real-point membership omits the current (the LF note's l.567), and its uniformity in the layer is not shown;
- the class conditions of 64.3 at U_1, U_2, U_{1,2}, and U_{k,Λ}, whose status is recorded in §§49, 60, and 61;
- the conversion from the configuration to the plaquette field in the constants 6144 and 12288, and K_P on the exterior data;
- the mechanism at complex t (the Cauchy factor 2r(Y)), which is not written.

## 67. The Band and the Inside of Z at D(s): Points 3 and 4 of 54.2

This section treats point 3 of 54.2 and point 4 inside Z, at real points of the line and at real localisation parameters; §68 extends both to complex points. The localised 𝐇 keeps its exponential decay from Λ at half the rate, which is enough for 49.4's device on the band, and the band's contribution decays across the layers to every point of Y_i^0. Inside Z the data move only on Λ_0, and the twist there enters the room ratio r(Y) of the LF note.

### 67.1 The Sources (Read)

- LFR II p.373 l.30–36: the localisation operation is applied to 𝐇″_k "with the set σ̃₀ of cubes Δ disjoint with Λ", in the form of the expansion (6.10) [I], over domains Y₂′ such that "each component of Y₂′ … contains at least one component of Λ, and intersects the boundary layer Y₁ ∖ Y₁^0". The same for 𝐇_{𝐁₁} (Y₃′) and 𝐇_k (Y₄′) on p.374. [I]'s (6.x) is RG II's (1.x): RG II (1.31) is the scaling inequality cited as (6.31) [I] on LFR II p.384, and RG II (2.1) is the expansion cited as (7.1) [I] on p.387.
- RG II pp.3–6, (1.7)–(1.18): the term of a walk ω of a propagator is bounded by O(1)O(M₁^{−1/2})^{|ω|}M₁^{−|ω|/2}exp(−δ₀d(ω, y, y′)) (1.7), in the δ₀ of PBG Theorem 3.1; PBG's per-walk bound (3.108) carries e^{−½δ₀d(ω,y,y′)} in PBG's local δ₀. RG II multiplies a walk term by s(Δ₁)⋯s(Δ_m) over the cubes of σ₀ that meet its localisation domain (p.3 l.30–32). (1.11) is the supremum expression B₀|X|sup_ω M₁^{−|ω|/2}exp(−δ₀d(ω))e^{mκ₁}; for |s(Δ)| ≤ e^{κ₁}, "If m is big enough, for example m > 2⁴, then δ₀d(ω) ≥ δ₁mM", and the text after (1.11) gives the bound B₀e^{16κ₁}|X| under δ₁M ≥ κ₁ (p.5 l.13–16). Proposition 4 is asserted for the localised operators (p.5 l.39–40). The contractions (1.12)–(1.17) close with B₀e^{16κ₁} for B₀, with the smallness condition carrying at most (B₀e^{16κ₁})³ ((1.15), p.6), and 𝐇_k(s(Y₀), B′) is analytic, with (1.18).
- The LF note l.224 and l.357–361: the arguments of (1.54), (1.57), and (1.58), with 𝐆″_kJ_{1,2} decaying from Λ, a weighted contraction over 𝔊, the kernel form of VAR Proposition 4, H₁ through PBG (3.133), and HD, and a_{j(x)}|𝐇(x)| + a_{j(x)}²|∇𝐇(x)| ≤ C_𝐇ε̂e^{−(δ₀/16)d(y,Λ)} for each 𝐇 of the chain, 𝐇″_k included. Its l.229 (*The gauge of the data.*): the data of U″_k on Λ ∩ Ω″^{∼2}_{h+1} are M^·(U_0^{(AL)}), in a gauge common to both runs. Its l.230: the run difference of the data of Λ_0 is at most C′_Δ(M)(ε/a_n)^{(1−ε₀)/3}ε₁ at every scale. Its l.353: the points of Λ are points of the history at the layers ≥ n. Its l.384: B, V″, and V_k are shared and fixed along the line. Its l.632: the ratio σ_c/ϱ.
- LFR I p.197 l.29–35, (1.87): U_0^{u₀} = U_0^{(AL)} = exp iη𝔸₀ inside Λ, with |𝔸₀|, |∇^η𝔸₀|, |∂^{η*}∂^η𝔸₀| < O(1)B₃²B₅M⁶ε_k on Z″_k, in each run's own AL gauge, and 𝔸₀ = 𝐇_{k,Λ}((1/i)log M^·(U₀)), analytic in its argument. LFR I p.191: the conditions (1.64)–(1.69) are invariant under G-valued gauge transformations. LFR I p.179 l.20–21: the compressed top layers of an R-operation are separated by one layer of M-cubes.
- VAR (190): δ𝓗_μ(B, x)/δB_ν(y′) is bounded with the prefactor (L^jη)^{−1} of the output's own layer.
- CMP 98 (106): u_k^0 is an explicit analytic function of 𝐇″_k restricted to the block (LFR II p.373 l.28–30).
- PRT2 (2.2): the layers are at least RM wide in their own units. PRT2 (2.58)–(2.59): the counts c_δ and their condition.
- CRE (2.6): the ratios of the α's and ε's of two scales.

The "almost the same" statements of LFR II p.375 are qualitative in the print. Their quantification below and in 68.2 is derived here.

### 67.2 The Localised 𝐇 (Derived)

*At real s.* Let s be the parameters of σ̃₀, real in [0, 1]. Each walk term is multiplied by ∏s(Δ_i) ∈ [0, 1]. PBG's kernel bounds are sums of absolute per-walk bounds, so the localised operators satisfy the original bounds with B₀ and δ₀. The LF note's weighted contraction at the weight e^{(δ₀/16)d(·,Λ)} applies verbatim, 𝐇(s) is real, and h_s ≤ h at real s.

*At complex s.* Let |s(Δ)| ≤ e^{κ₁}. Each operator of the weighted contraction (the LF note's l.224) is a sum over the walks of its localised random-walk expansion: 𝔊, the kernel form of VAR Proposition 4, H₁ through PBG (3.133), and HD. 𝔊, H₁, and H are walk sums. The kernel form of VAR Proposition 4 and HD are not; their rates ⅛δ₀ and δ₀/4 are derived in the LF note's (b) from the kernel rate δ of the operators by Neumann-series counts under PRT2 (2.59), and that derivation is homogeneous in δ: at the input rate δ₀/2 it gives δ₀/16 and δ₀/8, under (2.59) at the halved α. In the bound of a walk the factor e^{mκ₁} is paid by half the decay. Here δ₀ and δ₁ are the per-walk rates of RG II (1.7) and (1.11); the LF note's δ₀ is a kernel rate at most the per-walk rate (its l.223), so half the per-walk rate dominates half the kernel rate. RG II's threshold 2⁴ counts the M-cubes of one scale that a walk of length zero can meet in d = 4. On the multiscale lattice of σ̃₀ such a walk can meet more cubes at a layer interface, at most a fixed number m₀ of d. If m > m₀, δ₀d(ω, y, y′) ≥ δ₀d(ω) ≥ δ₁mM, since d(ω, y, y′) ≥ d(ω) for linear and tree-like walks (PBG (3.93), p.427 l.20), so e^{mκ₁}e^{−δ₀d(ω,y,y′)} ≤ e^{−½δ₀d(ω,y,y′)} for δ₁M ≥ 2κ₁. If m ≤ m₀ the factor is at most e^{m₀κ₁}. So each kernel bound holds with B₀e^{m₀κ₁} for B₀ and at half its rate. Bałaban's own condition δ₁M ≥ κ₁ spends the whole decay; δ₁M ≥ 2κ₁ keeps half of it. At the weight e^{(δ₀/32)d(·,Λ)} the margins stay positive: the kernel form keeps δ₀/16 − δ₀/32, and HD keeps 3δ₀/32 after the weight. The counts at the halved rates are those of PRT2 (2.58) under (2.59) at these rates, which hold for RM large. The contraction's smallness condition carries at most (B₀e^{m₀κ₁})³ (RG II (1.13)–(1.16)), and it holds for γ small after κ₁. So, for each 𝐇 of the chain,

  a_{j(x)}|𝐇(s)(x)| + a_{j(x)}²|∇𝐇(s)(x)| ≤ h_s(x) := C_𝐇(κ₁)ε̂e^{−(δ₀/32)d(y,Λ)}, x ∈ Δ(y),

with C_𝐇(κ₁) the constant C_𝐇 with B₀e^{m₀κ₁} for B₀ and the count at the rate δ₀/32. At real s the bound h of 49.3 holds for 𝐇(s), with the same constant.

*The gauge factors.* By 68.1's bullet on CMP 98 (106), u_± = 1 at 𝐇 = 0, and log u_± moves by at most C_u times the supremum of the twist over the block of x and its three-bond neighbourhood, since u(x) reads the twist on that block. 68.1's bullet uses only the transports and averages of (106), not §67. So the ratio u_±(s; t)u_±(1; 0)^{−1} is within C_u(h̄_s + h̄) of 1 in the units of the layer, with the block suprema h̄_s and h̄.

The new condition is δ₁M ≥ 2κ₁, which holds for M large after κ₁.

### 67.3 The Band (Point 3, Derived)

On the band Y_i ∖ Y_i^0 ⊂ Z^c (52.1), at the line's point t and the parameters s, the data of the representation are D(t, s) = u_−^{−1}exp iQ̃(η𝐇(s; t))R(u_+)M^·(c′(t)), with c′ the next member's line. At the endpoint they are D(0, 1). The ratio D(t, s)D(0, 1)^{−1} on a band bond of the layer m is the product of conjugates of the twists by 𝐇(s; t) and by 𝐇(1; 0)^{−1}, of the gauge factors, and of the ratio of c′'s line, conjugated by the G-valued factors between them, which act isometrically. By 67.2 and 65.3 its logarithm is at most C(h_s + h + d̄_ℓ) in the data norm of the layer, with h of 49.3 and d̄_ℓ of 65.3.

The band lies in Z^c, so 49.4's separation d(y, Λ) ≥ 8MR_k + LM·max(0, k − N₀ − m) holds at its points. 49.4's ratio with δ₀/32 for δ₀/16 gives h_s(y′) ≤ θ_k(κ₁)α′_{0,m′}/2 at a band point y′ of the layer m′, with θ_k(κ₁) := θ_kC_𝐇(κ₁)/C_𝐇. Its bound b_m(y) ≤ 2 holds under δ₀LM ≥ 32 and M ≥ M(δ₀, L). θ_k(κ₁) → 0 for γ small under q₀ > p₀ + r.

The ratio enters U(𝐁^D(Y_i), D(t, s)) through 65.2's linear bound. Let x ∈ Y_i^0 be a point of the layer m, in Z or in Z^c. At x the band contributes O(1)Σ_{y′}e^{−⅛δ₀d(x,y′)}C(h_s + h)(y′). By 68.1's kernel count (CRE (2.4), (2.6)–(2.7), and (2.28)), α′_{0,m′}/α′_{0,m} ≤ 2^{q₀}(1 + β₀)(1 + m′ − m)^{1/2} for m′ > m, and α′_{0,m′}/α′_{0,m} ≤ 1 + β₀ for m′ < m, the latter for log g_m^{−2} ≥ 2q₀ + 2log(1 + β₀). A path from x to y′ crosses the |m − m′| − 1 layers between them. Each is at least M wide in its own units: RM by PRT2 (2.2), LM by (G.265) of §46, and M at the compressed top layers of an R-operation (LFR I p.179 l.21–24). So

  e^{−⅛δ₀d(x,y′)} ≤ e^{−(1/16)δ₀d(x,y′)}e^{−(1/16)δ₀M·max(0,|m−m′|−1)},

as in PRT2 (2.58), and sup over integers x ≥ 0 of (1 + x)^{1/2}e^{−(δ₀M/16)max(0,x−1)} is √2 ≤ 2 for δ₀M ≥ 16. The band's contribution at x is therefore at most

  O(1)C·2^{q₀+1}(1 + β₀)c_{δ₀/16}θ_k(κ₁)·α′_{0,m}/2,

with c_{δ₀/16} the count of PRT2 (2.58) at that rate, under (2.59) with M in place of RM across the M-wide compressed layers. This is O(1)θ_k(κ₁) of the thresholds at every point of Y_i^0, Z included, uniformly in k − m. This count is a decay estimate and uses no width condition beyond M; the open item of 71.3 concerns (5.1c) at the near domains, not this count. The part of d̄_ℓ is 65.3's. So the band term moves each quantity of (1.64)–(1.69) at U(𝐁^D(Y_i), D(t, s)) by at most O(1)(θ_k(κ₁) + θ′_k) times its threshold at α̃′/2. This is point 3 at real t and real s ∈ [0, 1].

At s = 1 the identities of 53.2 hold. At real s ∈ [0, 1] the band term is a perturbation of at most O(1)θ_k(κ₁) of the thresholds; these are not identities.

### 67.4 Inside Z (Point 4, Derived)

For Y₁, with the data of (1.61), the points of Y₁^0 ∩ Z are of three kinds (49.4, the LF note's l.229 and l.353):
- the collar Z ∖ Λ, of the layer k;
- Λ_0 = Λ ∩ Ω″^{∼2}_{h+1}, which contains Λ ∩ Ω″_k, where the data are M^·(U_0^{(AL)});
- the deep part Λ_1, where the data are V″.

For Y₂, (1.62) puts M^·(U_0^{(AL)}) on Λ ∩ Ω″_k and 1 on Z″_k ∩ Ω″^∼_{h+1} (p.373 l.39–40). For Y₃, (1.63) puts V_Λ^{(A)} on Λ (p.374 l.17). In both, the data that depend on the run are those on Λ, built from U_0 and V on Λ in the AL gauge, and the others are fixed. So the argument below, with Λ in place of Λ_0, covers them.

Point 4 asks that the line's move of the data inside Z stays inside the thresholds of the configurations that read it. It does not need the run difference to be a vanishing fraction of the thresholds. 68.2 gives the moves on the disc as room-sized, at most θ_ι²/16 of the thresholds by the choice of c_ρ, on |t| ≤ 1/(2r(Y)), which contains t = 1 when r(Y) ≤ ½. 68.2's bound for the members uses only 68.1, c_ρ, and the base values of 49.5, §59, and 60.4–61.6; it does not use 67.4, so there is no circularity. So what is needed inside Z is that the twist there enters r(Y), with the LF note's ratio.

- *What moves inside Z.* B, V″, and V_k are shared and fixed along the line (the LF note's l.384). So on the collar Z ∖ Λ and on the deep part Λ_1 the data do not move, and inside Z the data move only on Λ_0.
- *The twist on Λ_0.* By l.230, the run difference of the data there is at most C′_Δ(M)(ε/a_n)^{(1−ε₀)/3}ε₁ at every scale. The points of Λ are points of the history at the layers ≥ n (l.353), so d̄(x) = C_U(M)(ε/a_n)^{(1−ε₀)/3}ε₁ there, and the run difference is at most (C′_Δ(M)/C_U(M))d̄(x). The field follows from the data by 65.2's linear bound, summed over the data of Λ_0 with e^{−⅛δ₀d}; d̄ is constant on Λ and non-increasing in the layer, so the sum also covers the points of Y outside Λ_0 that the data move reaches. So the line's field from the data of Λ_0 obeys the fine side's bound σ_c ≤ C(ε₀)d̄, with C(ε₀) multiplied by C_{65.2}C_avc_{δ₀/8}max(1, C′_Δ(M)/C_U(M)). This is a constant of M, independent of k, of the layer, and of γ. The second-order part a_m³|D*D𝐒_c| of σ_c (68.2) follows in the same way from the D*D𝓗 term of 65.2.
- *The ratio.* With this σ_c, the LF note's ratio σ_c/ϱ (its l.632) carries the factor (k − m + 1)^{1/2}. At the layers ≥ n this is at most (1 + j(C))^{1/2}(8n)^{1/2}, and it is absorbed by L^{−(1−97ε₀)n/24} there. So the contribution of the twist inside Z to σ_c/ϱ is at most ½ for n ≥ n₀′, with n₀′ depending on M through C′_Δ(M) as well, and no condition on k − m remains. r(Y) is a supremum over all of Y and over every entry c ∈ 𝒞. On Y ∖ Λ_0 the data do not move inside Z, and σ_c there is the fine side's: σ_c ≤ C(ε₀)d̄ at every point of the determining set of each entry c ∈ {U″_k, U^0_k, U_{k,Λ}, U_k} (the LF note's *The Fine Side at the Multiscale Chain.*). The entries U_1 and U_2 are replaced by the member U_{1,2} (§50, 56.2), whose lift is the run-B partner c^♭ and whose fine side is σ_c ≤ C̃(ε₀)d̄ (56.4). So r(Y) ≤ ½ holds for n ≥ n₀′ with C̃(ε₀) in place of C(ε₀), which changes only n₀′. For n < n₀′ the line is not used (the LF note's real fallback).
- *The base point.* At t = 0 the data D(0, s) on Y_i^0 are those of run B's member, M^·(c′^B). For Y₁ the base point's conditions come from the member's class, LFR II (1.65), below 9/16 of the thresholds, with 67.3 for s ≠ 1. (1.65) concerns U⁰_k only: for Y₂ and Y₃ the base points are U_1 and U_{k,Λ}, whose conditions are 49.5's on Z^c at real points, and inside Z they are open (67.5). In a single run the data of Λ_0 also obey |(1/i)log M^m(U_0^{(AL)})| ≤ O(1)B₃²B₅M⁶L^{−(k−m)}ε_k at a layer-m point of Z″_k, by (1.87) in that run's AL gauge, which is a vanishing fraction of α′_{0,m} uniformly in k − m. That is a bound on these data, not on the conditions of the representation configuration, and it is not used.

(1.87) does not give a run difference with the factor L^{−(k−m)}: VAR (190) carries the prefactor of the output's own layer, the run difference contains l.230's bracket at equal data, and (1.87) holds in each run's own AL gauge.

So inside Z the configurations of the line satisfy the conditions at their base-point values plus at most θ_ι²/16 of the thresholds, on the disc |t| ≤ 1/(2r(Y)).

*(5.1c) at D(s), at real t and s, given §§62.2, 66.1–66.4, 68.4, and 69.* With 65.2–65.3 and 67.3–67.4, U(𝐁^D(Y_i), D(t, s)) satisfies (1.64)–(1.69) on Y_i at real t and s. Its plaquettes on □₀ are within the thresholds of the layer, and its current moves by at most O(1)(θ_k(κ₁) + θ′_k + θ_ι²) times its threshold, through the D*D𝓗 term of 65.2, from the member's current, which is bounded by VAR Theorem 1's class (2) (55.5). So its pair satisfies run A's part of (a) on every X ∋ z, at the evaluation radius of 66.4, and 62.2 and 66.1–66.2 give (5.1c) at D(s), with the lift condition at the composites from §69, at the radii θ_ιr of 68.4.

### 67.5 Status

Derived, not reviewed in this form, as conditional derivations: 67.2–67.4. Quoted from the print: LFR II p.373 l.28–40 and p.374 l.8–30; RG II pp.3–6 and (1.7), (1.10)–(1.18); PBG (3.93), (3.108), (3.133), p.423 l.39 (the kernel rate is at most the rate per walk), and p.427 l.14–21; LFR I (1.87), p.179 l.21–24, p.191 l.32–33, and p.197 l.37–38 (𝔸₀ = ℍ_{k,Λ}(…)); VAR (190); CMP 98 (106); PRT2 (2.2) and (2.58)–(2.59); CRE (2.4), (2.6)–(2.7), and (2.28). Used from the notes: the LF note l.224, l.229–230, l.353–361, l.384, and l.632; 49.3–49.4; 52.1; 55.5; §59; 65.2–65.3; 66.1–66.2 and 66.4; 68.1–68.2 and 68.4.

New conditions: δ₁M ≥ 2κ₁, δ₀LM ≥ 32, δ₀M ≥ 16, ⅛(δ₀/2)RM ≥ 4log L + 1, the counts at δ₀/16, 3δ₀/32, and δ₀/32, (2.59) with M in place of RM across the compressed layers, log g_m^{−2} ≥ 2q₀ + 2log(1 + β₀), and C_U(M) replaced by max(C_U(M), C′_Δ(M)) in the ratio. m₀ and δ₁ depend on d and L. The order is L, κ₁, then R, M, and M₁, then γ.

Derived at real points of the line and real localisation parameters:
- point 3 of 54.2, the band, on Z^c and inside Z;
- the band part of the "almost the same" statements of LFR II p.375 at real s, as perturbations of the thresholds.

Derived given open inputs:
- point 4 inside Z, for n ≥ n₀′, with r(Y) ≤ ½ from the LF note's fine side at U_{k,Λ} and U_{1,2} and from 56.4; the LF note's l.614, l.630, and l.632 rest that use on LFR I (1.64)–(1.69) at those members, whose status is recorded in §§49, 60, and 61 (open there: the collar points near Λ, and the case (ii) at U_2 when h > k₀);
- (5.1c) at D(t, s), given 62.2, §66, 68.4, and §69, away from the near domains of 71.3.

Weakest steps: r(Y) ≤ ½ through the conditions at U_{k,Λ} and U_{1,2}; the halved rates of the kernel form and of HD, which need VAR (70)–(71) replayed at H(s) (the homogeneity in δ is asserted, and a check supports the rates δ₀/16 and δ₀/8); the reading of (1.62)–(1.63) inside Z; the gauge factor through 68.1, with the uniformity of C_u in k from CMP 98 (106) not shown.

Open:
- the base-point conditions for Y₂ and Y₃: LFR II (1.65) concerns U⁰_k only, and the conditions at U_1 and U_{k,Λ} as base points, with the comparison on (Λ^∼)^c, are not derived here; so the "almost the same" statements of p.375 are derived only in their band part;
- (5.1c) at the near domains of 71.3 (§71);
- the multiscale count behind m₀(d, L) and δ₁(δ₀, d, L) (67.2) is not written.

What this changes in the LF note (not edited there): at its l.20, the band part of the conditions at U(𝐁″_k(Y₁), D(s)) is derived at real points, and the rest is as above; the items of its l.20 for U_{k,Λ}, U_1, and U_2 are not treated here; at its l.16, (5.1c) at D(s) is derived given the inputs above, with the lift condition at the composites from §69.

## 68. Complex Points: The Line's Disc and the Localisation Parameters

This section extends §§59–67 from real points to the complex points that the Cauchy estimates use: the joint line at complex t in its disc |t| ≤ 1/(2r(Y)) (49.6), and the localisation parameters at |s(Δ)| ≤ e^{κ₁} (67.2). The device is the LF note's: a real point whose conditions hold with room, plus a complex move bounded by a fraction of the thresholds. The move bound of a complex twist is derived with its constants (68.1). The bounds at complex backgrounds come from Bałaban's printed complex extensions, whose hypotheses (3.35)–(3.38) [5] are checked at the line's backgrounds; for this the second-order size of the line's field is put into σ_c (68.2). The twist on the line's disc is room-sized, so the room constant c_ρ is fixed against the move constants.

### The Sources (Read)

- PBG p.396 l.37–50: the complex class. Configurations U′U with U G-valued in (3.35), U′ = e^{iηA′}, A′ 𝔤^c-valued, |A′| < α₁(L^jη)^{−1} and |∇^η_UA′| < α₁(L^jη)^{−2} on Ω_j (3.37), and |D*D A′| < α₁(L^jη)^{−3} (3.38).
- PBG Theorem 3.4 (p.400 l.7–10): "There exists a positive constant a₁ such that the operators G′(U), (Q′(U)G′²(U)Q′*(U))^{−1}, R(U), G(U) extend to configurations U′U for α₁ ≤ a₁ as analytic functions of A. The extended operators satisfy all the inequalities of Theorems 3.1–3.3 correspondingly." Also p.403 l.39–48, where P(U′U) = P(U) + P′(A) with P′ of order α₁ (3.68), and p.406 l.10: "all the functions and operators introduced above are analytic on the domain (3.37)".
- VAR p.278 (7): |(∂V)(p′) − 1| < ε₁ for p′ ∈ 𝔅_k, "for ε₁ sufficiently small". Here ε₁ is VAR's regularity constant, a number of d and G, written ε₁^V below.
- VAR p.305 (172): |V′ − 1| < C₁ε₁, |B′| < 2C₁ε₁.
- VAR p.309 l.1–4: the functions and operators "can be extended to arbitrary, regular configurations U … They are analytic functions of these configurations, having the properties and bounds as described above". Proposition 9 (p.309): U_k(V′V₀) "has an extension to an analytic function of G^c-valued small configurations V′"; 𝓗(B) "is an analytic function of B, and also of the external gauge field configuration U satisfying the regularity conditions (3.35)–(3.38) [5], or (1.7)–(1.9) [6]", with (19)–(21) at ε₂ = B₅ε₁ (173) and its functional derivative (182) satisfying (190).
- VAR (9)–(10), p.279 l.19–26: at a minimiser, on the cubes of the layer j, in a gauge, |A| < B₃Mε₁a_j^{−1}, |∇A| < B₃Mε₁a_j^{−2}, and |∂*∂A| < B₃Mε₁a_j^{−3}.
- CMP 98 (104)–(106), p.33 l.28–46: u(x) is the product over the scales j of the transports R(U₀(Γ^{(j+1)}_{x_{j+1},x}))^{−1} from the centre x_{j+1} of the (j+1)-block containing x, and of the factors (average)^{−1}·(R̄Ū)(Γ_{x_{j+1},x_j}), the average being the exponential of the average of the logarithms over the block (105).
- LFR I p.190 l.17–18: U_{p,X} and J_{p,X} are the configuration and the current of the determining set 𝐁_p(X) ∪ {Γ_i}_{i<p} at their data.
- LFR I p.191 l.39–43: if 𝕌 ∈ Ũ_k^{(n+1)c}(X, α̃₀, α̃₁), then exp iηℍ_k^{(n)}(·)𝕌 ∈ Ũ_k^{(n)c}(X, α̃₀, α̃₁), with the proof "almost identical" to that of (1.44)–(1.52). This is Bałaban's statement that a complex twist of a configuration of the complex class stays in the class, for his ℍ. 68.1 derives the move bound for the twists used here.
- RG I p.262 l.15–36: the conditions (i) (1.11) and (1.12), (ii) (1.13), and (iii) (1.14) of U^c_j(X, α₀, α₁). RG I (1.17), p.263 l.7–18.
- RG II (1.10), p.4, and p.5 l.5–16: Bałaban's Cauchy formula in s.
- CRE (2.6) and (2.28).
- The LF note: l.459 (σ_c and r(Y)), l.528 (c_ρα_m < min(α₂, α₃)), l.564 (the identity J(e^{i(ε/L)𝐀}c^B) − J(c^B) = D*D𝐀 + O(|F||𝐀|) of the one-step problem), l.566 and Open Gaps (3) (a_{j(x)}³|ΔJ_c(x)| ≤ Ĉ_Jd̄(x) and σ_c ≤ C(ε₀)d̄ at the real members), l.570 (the currents frozen along the line), and l.572 (ϱ(x) ≥ c_ρα_m with c_ρ := 1/(4(1 + β₀)C_p), and the class for |t| ≤ 1/r(Y)).

### 68.1 The Move Bound for a Complex Twist (Derived)

*Norms.* The norm on 𝔤^c is the operator norm in a fixed faithful unitary representation of G, so 𝔤 is represented by anti-Hermitian or, in the convention e^{iηA}, Hermitian matrices. For X = X_r + iX_i with X_r, X_i ∈ 𝔤, |X_r|, |X_i| ≤ |X|, since X_r and X_i are the halves of X and of its image under the involution fixing 𝔤, which is X ↦ X*, an isometry. Also |Ad_{e^{iY}}| ≤ e^{2|Y|}. C_av is the averaging constant of 65.2 (the move of a block average is at most C_av times the move of its argument). It is not the C_av = 1 of the Cauchy note's §11(b).

*Three bounds on the Baker–Campbell–Hausdorff remainder.* All three follow from Cauchy's estimates. For |W − 1| ≤ e^{1/2} − 1 < 0.65, |log W| ≤ −log(1 − 0.65) < 1.05. So on the set |X₁| + ⋯ + |X_n| ≤ ½ the function R_n := log(e^{X₁}⋯e^{X_n}) − ΣX_l is analytic and |R_n| ≤ 1.05 + ½ < 2.
- (Q) Let Σ := Σ|X_l| ≤ ½. ψ(λ) := R_n(λX₁, …, λX_n) is analytic on |λ| ≤ 1/(2Σ), bounded by 2, and vanishes to second order at λ = 0. Schwarz's lemma gives |R_n| = |ψ(1)| ≤ 2(2Σ)² = 8Σ².
- (L) Let R(X, Y, Z) := R₃(X, Y, Z), s := |X| + |Z| ≤ ¼, and y := |Y| ≤ ¼. φ(λ, μ) := R(λX, μY, λZ) is analytic on |λ| ≤ 1/(4s), |μ| ≤ 1/(4y), bounded by 2, and φ(0, μ) = 0. Write φ(λ, μ) = λa(μ) + λ²b(λ, μ). Cauchy's estimate gives |a(μ)| ≤ 8s. a(0) = 0, since φ(λ, 0) = log(e^{λX}e^{λZ}) − λ(X + Z) is O(λ²), so |a(1)| ≤ 8s·4y. On |λ| = 1/(4s), |φ − λa| ≤ 4, so |b(1, 1)| ≤ 64s². Hence |R(X, Y, Z)| ≤ 32sy + 64s² ≤ 64(|X| + |Z|)(|X| + |Y| + |Z|).
- (D) For s + y ≤ ⅛ and a direction δ = (δX, δY, δZ), the bound (L) on the polydisc of radius t := s + y in the direction (δX, 0, δZ), and of radius ⅛ in the direction (0, δY, 0), gives |DR[δ]| ≤ 256[(s + y)(|δX| + |δZ|) + s|δY|]. R is equivariant under conjugation, R(Ad_gX, Ad_gY, Ad_gZ) = Ad_gR(X, Y, Z), so the covariant difference of R along a bond with G-valued transport is the difference of R at the transported arguments, and integrating DR along the segment between them bounds it by 256[t̄(|ΔX| + |ΔZ|) + s̄|ΔY|], with s̄ and t̄ the larger values at the two ends.

*The hypothesis.* Let U = U′U_r be of the complex class. U_r is G-valued and satisfies the real conditions. U′ = e^{iηA′} with a_{j(y)}|A′(y)| + a_{j(y)}²|∇_{U_r}A′(y)| ≤ α_{1,j(y)} at every point y. Its plaquettes satisfy |U(∂p) − 1| ≤ ¼η²a_m^{−2} at the points of the layer m, which RG I (1.14) and LFR I (1.64)(i) give for γ small, outside the top layers of an R-operation (71.3). Let 𝐇 be 𝔤^c-valued with a_{j(y)}|𝐇(y)| + a_{j(y)}²|∇_{U_r}𝐇(y)| ≤ h(y) at every y, with

  h(y) ≤ h₀ := min(1/10240, C₁ε₁^V/(8C_av)),

and let α_{1,m} ≤ 1/10240 and C_avα_{1,m} ≤ ¼C₁ε₁^V, which hold for γ small. Let U^♮ := e^{iη𝐇}U. Write h̄(x) for the maximum of h over the block of the layer of x that contains x and the bonds within three bonds of it. Since η ≤ a_m, the twist and A′ have |η𝐇| ≤ h and |ηA′| ≤ α_{1,m} per bond. Then at a point x of the layer m:

- *The plaquettes.* Let p have the boundary bonds b₁, …, b₄ from its base, and let Γ_l := b₁⋯b_{l−1}. Then U^♮(∂p) = e^{iX₁}⋯e^{iX₄}U(∂p) with X_l := ηAd_{U(Γ_l)}𝐇̂(b_l). Here 𝐇̂(b) is 𝐇(b) for a bond traversed forwards and −Ad_{U(b)^{−1}}𝐇(b) for a bond traversed backwards. The G-valued factors act isometrically, and each of the at most four complex factors U′(b) in the transports below costs at most e^{2α_{1,m}}, so all of them are bounded by κ := e^{8α_{1,m}} < 1.01. X₁ + X₃ and X₂ + X₄ are differences of the values of 𝐇 at two parallel bonds at distance η, transported to the base along paths that differ by the plaquette. Write ∇_U𝐇 for the gradient with the transport of the full configuration U. Then |∇_U𝐇| ≤ |∇_{U_r}𝐇| + 3|A′||𝐇|, since |Ad_{U′(b)} − 1| ≤ 3η|A′(b)|, so a_m²|∇_U𝐇| ≤ (5/4)h̄(x). The difference of the two paths is Ad_{U(∂p)} − 1, at most (8/3)|U(∂p) − 1| ≤ 3η²a_m^{−2} for |U(∂p) − 1| ≤ ¼. So |ΣX_l| ≤ 2κ(η²|∇_U𝐇| + 3η³a_m^{−2}|𝐇|) ≤ 2κ(5/4 + 3η/a_m)h̄η²a_m^{−2} ≤ 9h̄η²a_m^{−2}. With Σ|X_l| ≤ 4κηh̄/a_m ≤ ½, (Q) gives e^{iX₁}⋯e^{iX₄} = e^{iZ} with |Z| ≤ (9 + 8·16.4h̄)h̄η²a_m^{−2} ≤ 10h̄η²a_m^{−2} ≤ 1. Hence

  |U^♮(∂p) − 1| − |U(∂p) − 1| ≤ (e^{|Z|} − 1)|U(∂p) − 1| + |e^{iZ} − 1| ≤ e|Z|(|U(∂p) − 1| + 1) ≤ 2e·10h̄η²a_m^{−2} ≤ 55h̄η²a_m^{−2}.

  So the plaquette move constant is C_pl^c := 55. (It is not the plain-lift constant C_pl of the Cauchy note's l.952.)
- *A′ and ∇A′.* U^♮ = U′_♮U_{r,♮} exactly, with U_{r,♮} := e^{iη𝐇_r}U_r, which is G-valued, and U′_♮ := e^{iη𝐇}e^{iηA′}e^{−iη𝐇_r}. So U′_♮ = e^{iηA′_♮} with A′_♮ = A′ + i𝐇_i + R′, R′ := R(iη𝐇, iηA′, −iη𝐇_r)/(iη). The transports of U_{r,♮} and U_r differ by Ad_{e^{iη𝐇_r}}, so a_m²|∇_{U_{r,♮}}𝐇| ≤ (5/4)h̄ and a_m²|∇_{U_{r,♮}}A′| ≤ (5/4)α_{1,m}, and |∇𝐇_r|, |∇𝐇_i| ≤ |∇𝐇| for a G-valued transport. With s ≤ 2ηh̄/a_m and t ≤ η(α_{1,m} + 2h̄)/a_m ≤ ⅛:
  - by (L), a_m|R′| ≤ 128(η/a_m)h̄(α_{1,m} + 2h̄) ≤ h̄/4;
  - by (D), a_m²|∇_{U_{r,♮}}R′| ≤ 256·5(η/a_m)h̄(α_{1,m} + 2h̄) ≤ h̄/4, since α_{1,m} + 2h̄ ≤ 1/5120;
  - the change of the transport acting on A′ is at most a_m²·3|𝐇_r||A′| ≤ 3h̄α_{1,m} ≤ h̄/4.

  So a_m|A′_♮ − A′| + a_m²|∇_{U_{r,♮}}A′_♮ − ∇_{U_r}A′| ≤ (5/4)h̄ + (5/4)h̄ + ¾h̄ ≤ 4h̄. The thresholds of these conditions are α_{1,m} times their scale factors, and α_{1,m}/α_{0,m} = (C₁/C₀)(log g_m^{−2})^{q₁−q₀} ≥ C₁/C₀ by CRE (2.28) with q₁ ≥ q₀ (the Cauchy note's l.952). In units of α_{0,m} the move is at most (4C₀/C₁)h̄.
- *The cube-gauge conditions* (1.65), (1.67), and (1.69), RG I (1.12), and the plaquette of the G-valued factor (RG I (1.11) and the |∂U − 1| entry of LFR I (1.64)). They concern only the G-valued factor. U_{r,♮} is the real twist of U_r by 𝐇_r, with a_m|𝐇_r| + a_m²|∇_{U_r}𝐇_r| ≤ h̄, so 49.3 applies within its hypotheses, with u held fixed: the move is at most C_twh̄.
- *The gauge transformations of CMP 98 (106).* At a point x of the layer m the blocks of the determining set containing x have the scales j + 1 ≤ m, so the transports of (106) run along paths of at most L^{j+1}η/η bonds, inside the m-block of x. The twist moves each such transport by at most (L^{j+1}η/η)·κηh̄/a_m ≤ 2L^{j+1−m}h̄. The factor (average)^{−1}·(R̄Ū)(Γ_{x_{j+1},x_j}) is e^{−iā}e^{ia(x_j)}, with a the logarithm of R̄Ū along these paths and ā its block average (105). |log W| ≤ 2|W − 1| for |W − 1| ≤ ½ and |e^X − 1| ≤ 2|X| for |X| ≤ ½, so the move of a and of ā is at most 4L^{j+1−m}h̄, and that of the factor at most 8L^{j+1−m}h̄ + 8(8L^{j+1−m}h̄)² by (Q). The ratio u(U^♮)u(U)^{−1} is the product of the factors' moves conjugated by partial products, whose Ad-norms are at most e^{2Σ|A′|η} ≤ 2. Summing over j + 1 ≤ m, Σ_jL^{j+1−m} ≤ 2, and (Q) gives |log(u(U^♮)u(U)^{−1})| ≤ C_uh̄ with C_u := 48. The bound is uniform in k: only the scales up to the layer's own enter at x.
- *The determining-set configurations.* U_{p,X} reads U only through the data M^·(U) (LFR I p.190 l.17–18). Write M^·(U) = V″V₀ with V₀ := M^·(U_r). V₀ is G-valued and satisfies VAR (7) at ε₁^V for γ small, since its block plaquettes are within C_avα_{0,m} of 1. V″ is G^c-valued with |V″ − 1| ≤ 2C_avα_{1,m}. The twist gives M^·(U^♮) = V′V″V₀ with V′ = e^{iB′}, |B′| ≤ C_avh̄. So |V′V″ − 1| ≤ 2C_av(h₀ + α_{1,m}) < C₁ε₁^V, and Proposition 9's first clause (analyticity in G^c-valued small V′ at V₀ satisfying (7)) applies to the total ratio V′V″. No external configuration enters. Its functional derivative satisfies (190) at complex B, which is 65.2's linear bound at G^c-valued ratios, with the kernels of 65.2. So U_{p,X} moves at x by at most C_{65.2}C_avΣ_ye^{−⅛δ₀d(x,y)}h(y) times its scale factor.
- *The currents J_{p,X}.* For |z| ≤ z₀ := C₁ε₁^V/(8C_avh₀), the data e^{izB′}V″V₀ have |e^{izB′}V″ − 1| < C₁ε₁^V, so f(z) := J_{p,X}(e^{izB′}V″V₀) is analytic there by Proposition 9. Its supremum is bounded from the printed bounds, not printed: J_{p,X} is the current of e^{iη𝓗}U₀, which is J(U₀), of order B₃ε₁^V by VAR Theorem 1, plus terms bounded by (19)–(21) at ε₂ = B₅ε₁^V. So sup|f| ≤ (B₃ + O(1)B₅)ε₁^V times the current's scale factor. z₀ ≥ 2 by h₀, and Cauchy's estimate gives |f(1) − f(0)| ≤ sup|f|/(z₀ − 1) ≤ 2sup|f|/z₀. With the per-point form of B′, the move of J_{p,X} at x is at most C_JΣ_ye^{−⅛δ₀d(x,y)}h(y) times the scale factor, C_J := 16C_av(B₃ + O(1)B₅)/C₁. The current of LFR I (1.64)(i) of a configuration U_{p,X} is this J_{p,X}, so it is covered here, at real and complex s alike.

*The kernel count.* Let h(y) := c_ρα_{j(y)}/2, the case used below. For m′ > m, α_{m′}/α_m ≤ 2^{q₁}(1 + β₀)(1 + m′ − m)^{1/2} by CRE (2.6)–(2.7). For m′ < m, let x := g_{m′}/g_m ≤ 1 + β₀ (CRE (2.6)) and ℓ := log g_m^{−2}. Then α_{m′}/α_m = x(1 + 2log(1/x)/ℓ)^{q}, which for ℓ ≥ 2q₁ + 2log(1 + β₀) is non-increasing in log(1/x) ≥ −log(1 + β₀), so it is at most 1 + β₀. A path between the layers m and m′ crosses |m − m′| − 1 layers, each wider than RM in its own units (PRT2 (2.2)), and the decay per layer, ⅛δ₀RM ≥ 4log L + 1 (the Cauchy note's (⋆)), pays the factor (1 + |m − m′|)^{1/2}. So Σ_ye^{−⅛δ₀d(x,y)}h(y) ≤ K_αc_ρα_m/2, and h̄(x) ≤ K_αc_ρα_m/2, with K_α := 2^{q₁}(1 + β₀)c_{δ₀/16}.

So, for h(y) = c_ρα_{j(y)}/2, every conditioned quantity of U^♮ at a point x of the layer m exceeds that of U by at most C_tw^cc_ρα_m/2 times its scale factor, with

  C_tw^c := K_α·max(C_pl^c, 4C₀/C₁, C_tw, C_{65.2}C_av, C_J, C_u),

a constant of d, G, the averaging, VAR's constants, and q₁, β₀, δ₀, independent of γ. For a general pointwise h the same holds with h̄(x) and the kernel sums in place of c_ρα_m/2. With it, 49.4 holds for complex twists with θ^c := (4/3)C_tw^cθ_k.

### 68.2 The Line's Disc (Derived)

*σ_c, ϱ, and r(Y).* In r(Y) := max_c sup_x σ_c(x)/ϱ(x) (the LF note's l.459), σ_c(x) is taken as the maximum of a_m|𝐒_c(x)| + a_m²|∇𝐒_c(x)| and a_m³|D*D𝐒_c(x)|, and ϱ(x) := c_ρα_{j(x)}. Both changes only increase r(Y). The LF note's uses of r(Y) need only its upper bound through d̄: at the real members, by the identity of l.564 at 𝐀 = 𝐒_c, D*D𝐒_c = ΔJ_c − O(|F(c^B)||𝐒_c|), so a_m³|D*D𝐒_c| ≤ Ĉ_Jd̄ + O(1)α_{0,m}C(ε₀)d̄, and the new σ_c is at most (C(ε₀) + Ĉ_J + O(1)C(ε₀))d̄. So r(Y) stays of the order of d̄/(c_ρα), as the LF note uses it.

*The twist.* At |t| ≤ 1/(2r(Y)), the line's configuration is c(t) = e^{i(ε/L)t𝐒_c}c^B. It is the complex twist of the real point c^B = c(0) by 𝐇 := t𝐒_c, with η = ε/L. So no real point c(Re t) with |Re t| > 1 is needed. By the definition of r(Y),

  a_m|t𝐒_c(x)| + a_m²|∇t𝐒_c(x)| ≤ |t|σ_c(x) ≤ σ_c(x)/(2r(Y)) ≤ ϱ(x)/2 = c_ρα_m/2,

and a_m³|D*D t𝐒_c(x)| ≤ c_ρα_m/2 as well. This is half the room at the edge of the disc, whatever θ_k is. So the moves on the disc are room-sized, and the room constant c_ρ has to be fixed against the move constants.

*The choice of c_ρ.* The LF note fixes c_ρ := 1/(4(1 + β₀)C_p) at its l.572 and requires c_ρα_m < min(α₂, α₃) at its l.528. Here

  c_ρ := min{θ_ι²[8(1 + β₀)²(C_tw^c + C_rep)]^{−1}, 1/(4(1 + β₀)C_p), c_ρ^{528}},

with θ_ι of 69.4, C_rep of the representation configurations below, and c_ρ^{528} the constant of the l.528 condition. A smaller c_ρ keeps the LF note's real-point argument valid (each move there is then at most ¼ of its threshold, and the joint line stays in the class at the thresholds α̃′ for |t| ≤ 1/r(Y)), and it enters only r(Y) ∝ 1/c_ρ and n₀′ (l.631). θ_ι is fixed by C_tw^c, C_ι(ε₀), B₃, B₅, and C₁/C₀ before c_ρ (69.4), so there is no circularity. For γ small, c_ρα_m/2 ≤ h₀.

*The members, U_2, U_{1,2}, and the strips.* By 68.1 at the base c^B with h(y) := c_ρα_{j(y)}/2, each conditioned quantity of c(t) exceeds its value at c^B by at most C_tw^cc_ρα_m/2 times its scale factor, the kernel count included in C_tw^c. Every threshold at x is at least α_m/(1 + β₀) times its scale factor (the LF note's *The room at real points.*), so the move is at most θ_ι²/16 ≤ 1/32 of the threshold. At c^B the quantities are at most 9/16 of their thresholds: by 49.5 at U_{k,Λ} and U_1, and by §59, 60.4, and 61.2–61.6 for the others, whose bounds are below the thresholds by the factors θ_J and θ_k. So on the disc they are below 9/16 + 1/32 of the thresholds.

*The representation configurations.* The data are D(t, s) = u_−^{−1}exp iQ̃(η𝐇(s; t))R(u_+)M^·(c′(t)), with c′ the next member's line (67.3). 𝐇(s; t) lives on the band Y_i ∖ Y_i^0 ⊂ Z^c (52.1).
- On Y_i^0 the ratio D(t, s)D(0, s)^{−1} is the average of the twist t𝐒_{c′}, at most C_avc_ρα_m/2.
- The background c′(t) of 𝐇 on the band is U′U with U := c′^B, a real minimiser satisfying (3.35)–(3.36), and A′ := t𝐒_{c′}. By the twist bounds above, A′ satisfies (3.37) and (3.38) at α₁ := c_ρα_m/2 ≤ a₁ in the layer scale, for γ small. So Proposition 9's external clause, PBG Theorem 3.4 for G′, G, and R, and VAR p.309 l.1–4 for 𝔊 and the contraction hold at c′(t) with the real constants. RG II's localisation (1.7)–(1.18) acts walk by walk on these bounds, so 67.2's bound h_s holds at c′(t) on the whole disc |t| ≤ 1/r(Y), on which c′(t) stays in the class.
- 𝐇(s; t) − 𝐇(s; 0) has two parts. The first is the change of 𝐇's argument at the background c′(0). The argument lies on Λ (49.3), where along the line it moves by at most C_tw^cc_ρα_k/2 times its scale factor. So this part is bounded as h_s with this move: at most C_𝐇(κ₁)C_tw^cc_ρα_ke^{−(δ₀/32)d(y,Λ)} in the units of the layer of y. The second is the change of the operators with the background at the fixed argument. It is analytic in t on |t| ≤ 1/r(Y), bounded there by 2h_s(y), and vanishes at t = 0, so by Schwarz's lemma it is at most 2|t|r(Y)·2h_s(y) ≤ 2h_s(y) on the disc. Here h_s(y) ≤ C_𝐇(κ₁)ε̂e^{−(δ₀/32)d(y,Λ)} with ε̂ the size of the argument (67.2), at most a constant times α_k.
- On Z^c, 49.4's separation d(y, Λ) ≥ 8MR_k + LM·max(0, k − N₀ − m) at a point y of the layer m gives e^{−(δ₀/32)d(y,Λ)} ≤ e^{−(δ₀/4)MR_k}e^{−(δ₀/32)LM·max(0,k−N₀−m)}. The second factor pays α_k/α_m ≤ 2^{q₁}(1 + β₀)(1 + k − m)^{1/2} for k − m > N₀, and the first pays it for k − m ≤ N₀, since (1 + N₀)^{1/2} ≤ R_k. The first factor also pays C_𝐇(κ₁) and the constants, for M ≥ M(κ₁, δ₀, L). So the first part is at most C_tw^cc_ρα_m/2 and the second at most α_m/(64(1 + β₀)), independent of c_ρ.
- The gauge factors u_± move by at most C_u times the twist (68.1), so by at most C_uK_α(c_ρα_m/2 + α_m/(64(1 + β₀)C_u)).
- By 65.2's linear bound at G^c-valued ratios (68.1), with the band count of 67.3, the representation configuration moves by at most C_repc_ρα_m/2 + α_m/(64(1 + β₀)) times its scale factor. C_rep is a constant of C_{65.2}, C_av, C_u, K_α, C_tw^c, and the count c_{3δ₀/32}.

By the choice of c_ρ, this move is at most θ_ι²/16 + 1/64 of the threshold. With the real values of 65.2–65.3 and 67.3–67.4 at t = 0, below 9/16 of the thresholds, the conditions (1.64)–(1.69) hold at U(𝐁^D(Y_i), D(t, s)) on the disc, since 9/16 + 1/32 + 1/64 < 1. The twist of c′(t) inside Z is bounded by the same ϱ, since r(Y) is a supremum over Y; 𝐇 has no part inside Z.

*Complex s.* 68.3 adds at most O(1)θ^c_k(κ₁) of each threshold, which tends to 0 as γ → 0 at fixed κ₁. γ is chosen after κ₁. So the "almost the same" statements of LFR II p.375 hold on |s(Δ)| ≤ e^{κ₁} and on the disc |t| ≤ 1/(2r(Y)).

### 68.3 The Localisation Parameters (Derived)

For |s(Δ)| ≤ e^{κ₁}, 67.2 gives h_s with C_𝐇(κ₁), and 𝐇(s) is 𝔤^c-valued. 67.3 then holds with 68.1 in place of 49.3, so the band term at complex s moves each condition by at most O(1)θ^c_k(κ₁) of its threshold, θ^c_k(κ₁) := θ^cC_𝐇(κ₁)/C_𝐇. This is the bound that Bałaban's Cauchy formula in s (RG II (1.10), p.4, and p.5 l.5–16) needs at the configurations of the band. 68.1 applies at the base c(t), which is already complex, since its A′ is at most c_ρα_m/2 + α_{1,m} and satisfies 68.1's hypothesis for γ small. With 68.2, the "almost the same" statements of LFR II p.375 hold on the domain |s| ≤ e^{κ₁} and on the line's disc.

### 68.4 (5.1c) at Complex t and s (Derived Under the Cauchy Note's Reading of (I.3.26))

At a configuration of the line, 62.2 needs on □₀ RG I's conditions (i), that is (1.11) and the cube-gauge condition (1.12), (ii), that is (1.13), and (iii), that is (1.14), together with (iv) and the condition (a). 68.2–68.3 give (i)–(iii) at the reduced thresholds α̃′ = α̃/(4B₃). So 2B₃α₀′ ≤ α₀/2, and (iv) follows by RG I (1.17), which is stated for complex 𝐔. Run A's part of (a) is their membership in 𝒫_j(X; θ_ιr), the current included through the D*D𝓗 term of 65.2. RG I's analysis at complex 𝐔 uses the Cauchy note's reading of (I.3.26), which is already a premise of that note at every complex point.

R-Δ runs on the class at the radii θ_ιr (69.4, 69.6). In the units a_j of a term of the generation j at a point of the layer m ≥ j, the complex-t move is at most L^{j−m}C_tw^cc_ρα_m/2 ≤ θ_ι²r_{0,j}/8. Here L^{j−m}α_m ≤ (1 + β₀)α_j ≤ 2(1 + β₀)r_{0,j}, by CRE (2.6) and since L^{−x}(1 + x)^{1/2} ≤ 1, and α_m := min(α′_{0,m}, α′_{1,m}). So the configurations of the disc lie in the class at the evaluation radius θ_ι²r of 66.4 wherever their real base point lies there at ½θ_ι²r, which holds for γ small (66.4). So (5.1c) holds at the complex points t and s of the near domains that meet the cut (62.2, 66.1–66.2), at D(t, s) (67.4), and at the endpoints (64.3, in 66.3's scope). The constants are those of R-Δ at the radii θ_ιr, and n₀′ carries c_ρ. The lift condition at the composites is §69's, and the variation groups (5.1v) at the near domains are §70's.

### 68.5 The Complex Data of the Polydisc (Derived)

§§68.1–68.4 treat complex t and s at real data 𝐔. At the complex data (𝐔, 𝐉) of the Cauchy note's polydisc the LF note lists three inputs (its l.626–628): the representative, the points n < n₀′, and the members' conditions (1.64)–(1.69). Its fourth line, *The route.*, gives the reason all three fail there. ε₁′ = C(M)R_kε′_k contains C_c(α̂₀ + α̂₁) with α̂_i := max_{m≤k}α_{i,m}, so a single number carries the complex part of the data at every layer. Measured against α_m, it does not tend to 0. Two changes remove this. The complex part is carried layer by layer with the LF note's weights, and the polydisc is the one at θ_ιr of 69.6.

*The complex part, layer by layer.* By the LF note's *The real points.* (l.638), the line z ↦ (𝐔_R + zA′_I) moves the plaquettes, currents, and averages at a point of the layer m by at most C_c(α_{0,m} + α_{1,m}) times the scale factors of (2.34)–(2.37). This is a bound per layer, with no factor R_k. On the polydisc of 69.6 the radii are θ_ια, so the complex part of the data at the layer m is at most θ_ιC_c(1 + C₁/C₀)α_{0,m} times the scale factors (q₀ = q₁).

*The α-weight.* Let Ŵ_α(x) := sup_y e^{−½δ_f|x−y|/ε}(a_{j(x)}/a_{j(y)})²α_{0,j(y)}, with the LF note's δ_f. For y in the layer of x or a coarser one, (a_{j(x)}/a_{j(y)})² = L^{−2(j(y)−j(x))}, and α_{0,j(y)}/α_{0,j(x)} ≤ (1+β₀)²(j(y) − j(x))^{1/2} ≤ L^{2(j(y)−j(x))} by CRE (2.6)–(2.7). For y in a finer layer, α_{0,j(y)} ≤ (1+β₀)²α_{0,j(x)}, and the computation of the LF note's *The weights.* under (F-W) bounds the term by (1+β₀)²L^{7/3}α_{0,j(x)}. So α_{0,j(x)} ≤ Ŵ_α(x) ≤ (1+β₀)²L^{7/3}α_{0,j(x)}. A kernel bounded by e^{−δ_f|x−y|/ε} therefore maps a source bounded by Ŵ_α(y)a_{j(y)}^{−2} to a field with a_{j(x)}|·| + a_{j(x)}²|∇·| ≤ 2c_{δ_f/2}Ŵ_α(x) at x, as in the LF note.

*The members at complex data.* Each member is the minimal configuration of its determining set, at data analytic in (𝐔, 𝐉). Along the segment from the real part of the data to the data, every configuration is the solution at its own data, so it is critical in the analytic sense (VAR Proposition 9: the equations (174)–(175) determine 𝓗). The derivative of the solution in the data at a critical background is the LF note's decomposition of *The bound.*, with the operators of VAR p.309 l.1–4 and PBG Theorem 3.4 on the complex class, as the LF note's *The complex class of ι's problem.* sets them up. So, integrated along the data as in *The bound.*, the member at (𝐔, 𝐉) is its value at the real part of the data moved by a field 𝐇_c with a_{j(x)}|𝐇_c| + a_{j(x)}²|∇𝐇_c| ≤ C_wθ_ια_{0,j(x)}, C_w := 2c_{δ_f/2}C_ℒ′C_c(1 + C₁/C₀)(1+β₀)²L^{7/3}. Here C_ℒ′ is the LF note's constant of the sources of *The bound.*. Nothing of this passes through the Picard iterates of *The flow.* at non-critical backgrounds, which is where the LF note's bound of Φ(W) is open. The real part is a real member, with the room of the LF note's *The Room.* and of §§59–67.

*The members' conditions (1.64)–(1.69) at complex data.* By 68.1 with h(x) := C_wθ_ια_{0,j(x)}, the move changes each condition at the layer m by at most C_tw^cC_wθ_ι(1 + C₁/C₀) times its threshold. The thresholds of (1.64)–(1.69) at a point x are at least (1 + β₀)^{−1} times α_{0,j(x)} and α_{1,j(x)} times the scale factors of the layer j(x) of x in the determining set, the points of (1.66)(ii) included (55.5's thresholds item, LFR I (1.16), CRE (2.28)). So the conditions hold with the room of the real points minus this fraction, once θ_ι ≤ θ_c := [4C_tw^cC_w(1 + C₁/C₀)]^{−1}. This is a constant of d, L, ε₀, δ_f, B₃, and B₅, and 69.6's θ_ι is taken at most θ_c. The lifts of the members follow in the same way: the fine side at complex data is the real fine side moved by the response of ι to 𝐇_c. That response is again the decomposition at critical backgrounds, so it is at most C_wθ_ια_{0,j(x)} in the units of each layer.

*The points n < n₀′.* The LF note's 𝔰/α_m was not small because the two-constants step used 𝔐 = 1. Here the complex point's field is the real one plus the move above, so 𝔰(x) ≤ 2σ′_c(x) + 2C_wθ_ια_{0,j(x)} in the units of the layer of x. At the layer m this gives 𝔰/α_m ≤ 2σ′_c/α_m + 2C_wθ_ι. The first term tends to 0 with γ, as at real points. The second is at most ½(C_tw^c)^{−1} by the choice of θ_c. So the moves of *The room at real points.* hold at every n, and the threshold n₀′ is not needed at complex data.

*The representative.* c^B(i) is Proposition 9's representative in the Landau gauge relative to c₀, and U^0_k(𝐔) is Bałaban's extension. Both are analytic continuations of the same real minimiser, with the orbit identity VAR (181), so c^B(i) = U^0_k(𝐔)^u with u analytic in the data and G-valued at real data. The gauge-fixing maps are analytic with the bounds (190), so u at the data is u at the real part times a factor whose logarithm and its gradient are at most C_g times the complex part of the data in the units of each layer, that is at most C_gθ_ιC_c(1 + C₁/C₀)α_{0,j(x)}. A complex gauge transformation of that size changes A′ by its gradient and the plaquettes through Ad(u) by a factor 1 + O(C_gθ_ια). So the class conditions at c^B(i) and at U^0_k(𝐔) agree up to that fraction of the thresholds, and θ_c with max(C_w, C_gC_c) in place of C_w covers it. The currents transform by J(W^u) = Ad(u)J(W) and agree in the same way.

*The strips, the joins, and the current at complex data.* The configurations of 61.2–61.6, the strips and U_{p,X}(M^·𝐔), are minimisers of their data. So the segment argument above moves each of them by a field of the size C_wθ_ια_{0,j(x)} in the units of each layer, and 68.1 moves their conditions (2.34)–(2.38) by at most the fraction C_tw^cC_wθ_ι(1 + C₁/C₀) ≤ ¼ of the thresholds. The data conditions of the joins, VAR's (1) (61.1), and U_1's junction (61.6) are conditions on the data, whose complex part is θ_ιC_c(1 + C₁/C₀)α_{0,m} at the layer m, so they hold with the same fraction of room. The current of §59 moves by η^{−2}Im D*∂ of the move. That is the second-order part of the move, bounded through the kernel's second differences as the second-order part a_m³|D*D𝐒_c| of σ_c in 68.2, by C_wθ_ια_{0,m} in the units of the layer m. So the conditions of §59 and 61.2–61.6 hold at the complex data of the polydisc, at every n.

*U_2 and U_{1,2}.* On the disc they use the real bounds of 56.2, 56.4, and 60.4–61.6, with 56.2's run-B partner of the patch in place of the half-domain lift of the LF note's l.18. The complex data add the move above, as for every member.

### 68.6 Status

Reduced, not reviewed: 68.1–68.5, to the open items below; 68.1's move bound for a complex twist is derived. Quoted from the print: PBG p.396 l.37–50, Theorem 3.4, p.403 l.39–48, and p.406 l.10; VAR (7), (9)–(10), (172)–(175), (181), (19)–(21), (190), p.309 l.1–4, and Proposition 9; CMP 98 (104)–(106); LFR I (1.64)–(1.69), p.190 l.17–18, and p.191 l.39–43; RG I (1.11)–(1.14) and (1.17); RG II (1.10) and p.5; CRE (2.6)–(2.7) and (2.28). Used from the notes, with their status recorded there: 49.3–49.6, 52.1, 55.5, 56.2, 56.4, §59, 60.4–61.6, 62.2, 65.2–65.3, 66.1–66.4, §67, 69.4, 69.6, 71.3, the LF note's l.459–470 (*The weights.* and (F-W)), l.528, l.564, l.566, l.570, l.572, l.626–638, and *The room at real points.*, and the Cauchy note's l.952 (q₁ ≥ q₀ > p₀ + r, C₁ > 2B₃²O(1)MC₀), (⋆), and its reading of (I.3.26). The provisional q₀ = q₁ of 69.7 enters through 69.4 and 69.6.

New conditions: h₀, α_{1,m} ≤ 1/10240, and C_avα_{1,m} ≤ ¼C₁ε₁^V of 68.1, with z₀ := C₁ε₁^V/(4C_avh₀); c_ρ of 68.2; log g_m^{−2} ≥ 2q₁ + 2log(1 + β₀); θ_ι ≤ θ_c of 68.5. All hold for γ small after the constants, γ after κ₁. M ≥ M(κ₁, δ₀, L) holds for M large, by a constant factor larger for the constant 1/64 of 68.2. σ_c includes the second-order size a_m³|D*D𝐒_c|, and ϱ := c_ρα_{j(x)} (68.2).

Reduced, given the open items:
- at real data 𝐔, complex t on the disc |t| ≤ 1/(2r(Y)) and complex s with |s(Δ)| ≤ e^{κ₁}, the conditions (1.64)–(1.69) at the members, at U_2 and U_{1,2}, at the strips, and at the representation configurations;
- at the complex data of the polydisc at θ_ιr, the members, their conditions, and their lifts, for n ≥ n₀′, with the representative c^B(i) = U^0_k(𝐔)^u (68.5);
- (5.1c) at these points, at R-Δ's radii θ_ιr, under the Cauchy note's reading of (I.3.26).

The weakest step: 68.2's check of PBG (3.38) and of the external clause of VAR Proposition 9 at c′(t), through the second-order part of σ_c.

Open:
- 68.2: the bound a_m³|D*D𝐒_c| ≲ d̄ identifies J(e^{i(ε/L)𝐒_c}c^B) − J(c^B) with ΔJ_c, which omits Q₁*(μ_A − J(c^A)); the LF note's l.564 does not contain this identity, so the checks of (3.38) and of Proposition 9's external clause at c′(t) rest on it;
- 68.5: the points n < n₀′ are not removed, since σ′_c carries ε₁′, which contains C(M)R_kθ_ιC_c(α̂₀ + α̂₁) (the LF note's l.624, l.629, and l.638), and this does not tend to 0 with γ;
- 68.5: the members' move constant C_w uses ι's fine-scale kernel e^{−δ_f|x−y|/ε} in place of the layer-scale kernel (190) of the multistep minimisers, and the current's third-order bound reuses C_w;
- 68.5: the bound C_g of the gauge u of the representative is not derived, since (190) does not bound the gauge-fixing transformation; the LF note's l.626 stays open;
- C_J lacks VAR's factor M, and its per-point form is not derived;
- the prefactor ϖ of the thresholds is not tracked against the fraction 9/16;
- the disc radius 1/(2r(Y)) against 1/r(Y), with α₁ = c_ρα_m there, and 68.1's hypothesis where 68.3 exceeds it, are to be reconciled.

## 69. The Lift Condition at the Composites and at Complex Data

This section treats the Cauchy note's open item at its l.196 in both of its parts: the lifted configuration at complex data, and at the composites of RG I Lemma 4. The device is the last sentence of the Cauchy note's §9.7, run on RG I's cube sequence of the composite and at complex data. Run B's composite is defined on that sequence with a collar of its own, the lift of run A's composite is compared with it at the same data, and the bounds are taken on the innermost cube. Both are minimisers at the scale j, so the difference is smooth at that scale, and the factor L^j of the Cauchy note's l.183 does not arise. VAR's constant C₁ of (172) is written C₁^V, to separate it from CRE's C₁ of (2.28).

### 69.1 The Sources (Read)

- VAR Theorem 1 (p.279 l.8–15): the minimal orbit in 𝔘_k({Ω_j}, B₃ε₁) ∩ 𝔙_k(𝔅_k, V), unique among the critical orbits for B₃ε₁ ≤ ε₀ ≤ a₀. The problem is posed on a sequence of domains {Ω_j}.
- VAR p.278 and (3): on Ω₀ ∖ Ω₁ the bond variables are the data, Ū⁰ = U. VAR (1), p.277: the domain conditions. VAR Theorem 1 does not cover Ω₀ = Ω₁ (the Cauchy note's §9.8).
- VAR p.309 l.1–4: the functions and operators "can be extended to arbitrary, regular configurations U", "they are analytic functions of these configurations, having the properties and bounds as described above, and the equations determine an analytic function 𝓗. All the above considerations and properties are valid for this function also."
- VAR Proposition 9 (p.309): U_k(V′V₀) is analytic in G^c-valued small V′, and U_k(V′V₀)U_k(V₀)^{−1} in the Landau gauge is exp iη𝓗(B), B = (1/i)log V′, with 𝓗 analytic in B and in the external configuration and satisfying (19)–(21) with ε₂ = B₅ε₁.
- VAR (19) (p.281 l.6–10): |A| < ε₂(L^jη)^{−1}, |∇A| < ε₂(L^jη)^{−2}, and |D*DA|, |ΔA| < ε₂(L^jη)^{−3} on Ω_j. The bounds carry (L^jη)^{−p}, so they are layer-weighted.
- VAR (171): 𝔓*(U_k)J = 0, the criticality of the minimiser. VAR (172)–(173): |B′| < 2C₁^Vε₁ and ε₂ = B₅ε₁, with C₁^V an absolute constant. VAR p.307 l.2–4: the gauge transformation to the Landau gauge, analytic in the configuration. VAR p.277 l.17: the bonds of Ω₀ ∖ Ω₁ carry the configuration as data. VAR (9): the cube-gauge regularity of the real minimiser.
- PBG p.395 l.11–13 and p.396 l.33: the operators are those of a domain Ω₀, G(U) = (Δ_a↾Ω₀)^{−1}, with no constraint on U outside Ω₀. PBG (3.37)–(3.38), p.396 l.36–50, and Theorem 3.4 (68's sources).
- RG I p.273 l.2–3: in the operators of VAR (179)–(180) the configurations U_{k+1}, J_{k+1} are replaced by 𝐔, 𝐉.
- RG I p.273 l.39–42: U_j(□₀) is built on "a sequence of cubes {□_n}, n = 0, 1, …, k+1, satisfying the conditions (1.3)–(1.6) [14] … hence □̃⁴ ⊂ □_{k+1}", with □₀ = □̃⁵. The data are scale 0 on □₀ ∖ □₁, scale p on □_p ∖ □_{p+1}, and the innermost scale on the innermost cube, written □_in below, so □̃⁴ ⊂ □_in.
- RG I Lemma 4 (p.280 l.24–32) and its proof (p.279 l.44–p.280 l.21). (3.50) splits 𝐇_j(□₀, τQ + B′) into 𝐇_j(□₀, τQ) and 𝐀₂ with |𝐀₂|, |∇𝐀₂| ≤ B₃|B′|. The restrictions are B₃α₃ < ½α₁ and 2B₃α₃ ≤ βL^{−2}α₀, and (3.51)–(3.52) bound the composite's plaquettes by (1+8β)L^{−2}α₀ξ². RG I (3.39)–(3.40), p.278 l.17–25: the identity and the class hypothesis that the proof uses for run A's composite. RG I (3.30) and (3.48): the composite's data exp i(τB_□ + B′). RG I p.277 l.54: B₃²O(1)Mα₀ < ½α₁.
- RG I (1.11)–(1.14) (p.262): the class conditions (i)–(iii). RG I (1.17).
- CRE (2.28) (p.259 l.47–50): α_{i,j} = g_jC_i(log g_j^{−2})^{q_i} with q₀, q₁ integers greater than 1 and no relation between them. The notes take q₀ = q₁ (the SW closure's §2), so α_{1,j}/α_{0,j} = C₁/C₀.
- CMP 98 Proposition 2: the averages of a configuration in the class.
- The Cauchy note l.178–200, §9.4–§9.8 (§9.8, *The definition.*: ι_XU := U(𝐁_1(X^∼), M^·(Q_1^{s*}U)), with Ω₁ the big blocks of size M₁ε at distance > RM₁ε/L from the complement, and the collar data Q_1^{s*}U, an exact local right inverse of the averaging, M(Q_1^{s*}U) = U), and l.952 (r_{i,j} = α_{i,j}/(8B₃)).

### 69.2 Run B's Composite (Definition)

Let □₀ ⊃ □₁ ⊃ ⋯ ⊃ □_in be RG I's cube sequence for run A, the maximal domains of (iv) satisfying (1.3)–(1.6) [14] "(with k+1, L^{−1}η instead of k, η, R=R₁)" (RG I p.273 l.41, p.262 (iv)). Let D be multiscale data on it, D = M^·(𝐔) on □₀, with the configuration 𝐔 outside □₀, where run A's composite equals 𝐔. Run B's problem lives on T_{ε/L}, so run A's scale p is run B's scale p + 1, and run B needs a scale-0 layer of its own. It is placed outside □₀, where the external configuration supplies its data, so that every other layer of run B is a layer of run A at the same spacing:
- Ω^B_0 := □₀^+, the union of □₀ and the collar C of the run-B blocks outside □₀ within distance w_c of □₀, with w_c > R₁M₁ε/L, so that VAR (1) holds at j = 0 with η = ε/L.
- Ω^B_1 := □₀, and Ω^B_{p+1} := □_p for p ≥ 1.
- The scale-0 data of run B, on the bonds of □₀^+ with no endpoint in □₀, are the configuration Q_1^{s*}𝐔 there (VAR p.277 l.17: Ω₀ ∖ Ω₁ carries the bond data). The scale-(p + 1) data are D's scale-p data on Ω^B_{p+1} ∖ Ω^B_{p+2}. Outside □₀^+ run B's configuration is Q_1^{s*}𝐔.

The layer Ω^B_{p+1} ∖ Ω^B_{p+2} = □_p ∖ □_{p+1} at run B's scale p + 1 has the spacing εL^p of run A's scale p, so it is run A's layer, and VAR (1) holds there with R = R₁ because (1.3)–(1.6) [14] hold for run A with R = R₁. No change of R₁ and no width condition beyond w_c enters. ι_{□₀} below is the one-step lift with Ω^B_1 = □₀ and this collar, and the Cauchy note's ι_X is compared with it on X^∼ by §9.8's tail, as with the global ι. U^B_{j+1}(□₀, D) is the minimiser of this problem. In 69.3–69.6 U^B is a comparison device; run B's own terms in Bałaban's construction read run B's own maximal sequence, and the near-domain reading of run B's terms used in §70 is stated there.

- *The competitor.* MU^B satisfies run A's constraints. On run A's scale-0 bonds of □₀ this is run B's scale-1 constraint. Outside □₀, M(Q_1^{s*}𝐔) = 𝐔 (the Cauchy note's l.521), which is run A's exterior. At the coarser layers it is the composition of the averagings. This is §9.1 at a := a_j.
- *j = 0.* U^B_1(□₀, D) = ι_{□₀}(D), with ι_{□₀} the one-step lift of §9.8 on □₀^+ with Ω^B_1 = □₀.

### 69.3 The Comparison on □_in at Complex Data (Derived)

*The bounds.* Let D = V′V₀ with V₀ G-valued, the factor of D in the polar decomposition G^c = exp(𝔤)·G, with 𝔤 the Hermitian generators in the convention e^{iηA}, A ∈ 𝔤; this holds for every compact connected G. Let B := (1/i)log V′, and let ε₁(D) := max(ε₁(V₀), 2|B|/C₁^V), with ε₁(V₀) the parameter of VAR (7) for V₀ and |B| in VAR's layer-weighted norm. Then |V′ − 1| ≤ 2|B|·½ < C₁^Vε₁(D) for |B| ≤ ½, so (172) holds at ε₁(D), and the polydisc of the identity theorem below, |B| < ½C₁^Vε₁, lies in Proposition 9's domain |V′ − 1| < C₁^Vε₁. Let U^A := U^A_j(□₀, D) and U^B := U^B_{j+1}(□₀, D), the two runs' composites at the same data. VAR Theorem 1 and Proposition 9 give U^· = e^{iη𝓗^·(B)}U^·(V₀) for each run, with η that run's spacing and 𝓗^· satisfying (19)–(21) at ε₂ = B₅ε₁(D). U^·(V₀) is real, with Theorem 1's regularity at B₃ε₁(V₀). VAR's constants do not depend on the number of steps.

These bounds are layer-weighted. In the units of a_j := εL^j they hold on □_in, where the data have the innermost scale. On a layer of the scale p < j they hold in the units of a_p. So on □_in, with |e^X| ≤ e^{|X|}, the plaquettes of U^B and of its real part are at most O(1)(B₃ + B₅)ε₁(D)a_j^{−2}, their first differences at most O(1)(B₃ + B₅)ε₁(D)a_j^{−3}, and 𝓗^B obeys (19). The terms of the fundamental case have X ⊂ □̃², and X^∼ ⊂ □̃³ ⊂ □̃⁴ ⊂ □_in (RG I p.273 l.41). Every use below is on X^∼, or reaches it from outside □_in through kernels that decay at the rate ⅛δ₀ or faster.

*The metric and the weighted norm.* d is the multiscale distance of the kernel bounds of VAR (190) and PBG (3.108), in which a layer of the scale p is at least R₁M₁ wide in its own units (VAR (1)). A point y of a layer of the scale p < j has d(y, □_in) ≥ R₁M₁(j − p), since a path from y to □_in crosses the layers of the scales p, …, j − 1. Let κ := δ₀/16 and, for a field f on □₀^+ with layer-weighted values |f(y)| in the units of its layer,

  ‖f‖_κ := sup_y |f(y)|e^{−κd(y,□_in)}L^{−(3−ε₀)(j−p(y))_+}/ρ_j(D),  ρ_j(D) := C_G(ε₀)L^{−(1−ε₀)j}ε₁(D),

with p(y) the scale of the layer of y. The weight allows a source on the layer p to be larger than ρ_j by L^{(3−ε₀)(j−p)}, which covers ρ_p/ρ_j = L^{(1−ε₀)(j−p)} and the change of units L^{2(j−p)}, and to grow like e^{κd(y,□_in)}. A kernel K(x, y) ≤ Ce^{−⅛δ₀d(x,y)} maps this norm to itself with the norm at most Cc_{δ₀/16}L^{3−ε₀}, since d(y, □_in) ≤ d(x, □_in) + d(x, y) and the layer factor changes by at most L^{(3−ε₀)|p(x)−p(y)|} ≤ e^{(δ₀/16)d(x,y)}·L^{3−ε₀} under the condition (W-κ): (δ₀/16)R₁M₁ ≥ (3 − ε₀)log L + 1, which holds for M₁ large. c_{δ₀/16} is the count of PRT2 (2.58) at that rate.

*The complex-data steps.* All four use the identity theorem fibrewise. For fixed real V₀, two holomorphic maps on the polydisc |B| < ½C₁^Vε₁ in 𝔤^c-valued B that agree for real B agree on the polydisc. The equations are taken in their gauge-invariant form, or in a gauge fixed analytically in D.
- *The fixed point (9.6).* At real D the fixed point W of (9.6), with reference MU^B and block datum 0, is critical for run A's problem at the data D and lies in VAR's ball (115). By Theorem 1 its orbit is the minimal orbit. In the Landau gauge relative to MU^B, W = U^A. The map (9.6) is an analytic contraction, uniformly in D on the polydisc, so its fixed point is analytic in D. Proposition 9's U^A, transformed to the same Landau gauge by the analytic gauge transformation of VAR p.307 l.2–4, is analytic in D as well. The two agree at real D, so they agree on the polydisc.
- *The class of MU^B.* U^B = U′U_r with U_r := U^B(V₀) G-valued and U′ = e^{iη𝓗^B}. U_r satisfies (3.35)–(3.36) by Theorem 1 (9)–(10). U′ satisfies (3.37)–(3.38) on every layer Ω_j, in the layer-weighted form of PBG, with α₁ = B₅ε₁(D), since (19) contains the D*D bound on every layer. The averaging M is a local analytic map, so MU^B = e^{iA_M}M(U_r) with A_M analytic in 𝓗^B, A_M = 0 at 𝓗^B = 0, and A_M and its first two covariant derivatives at most C_av times those of 𝓗^B, layer by layer. This holds by Cauchy's estimate on the layerwise polydisc η|𝓗^B| ≤ ¼, where M is explicitly bounded. M(U_r) satisfies (3.35)–(3.36) by the cube-gauge regularity of the Cauchy note's §9.8. So MU^B lies in PBG's complex class (3.37)–(3.38) on every layer with α₁ = C_avB₅ε₁(D) ≤ a₁ (PBG Theorem 3.4's constant), and PBG Theorem 3.4 and VAR p.309 l.1–4 give the operators of (9.8) there. C_av here is the averaging constant of 65.2, not the C_av = 1 of the Cauchy note's §11(b).
- *The identity (9.7) and the multipliers.* The criticality 𝔓*(U^B)J(U^B) = 0 (VAR (171)) under run B's constraints, and the multiplier identity D_V*λ^B = 0 of the Cauchy note's §10.3, with λ^B := (Q_BQ_B*)^{−1}Q_BJ(U^B), hold at real D. Both sides are analytic in D, so they hold on the polydisc.
- *The right inverse ℒ.* §9.4 gives spectrum(T^{pl}(U_r)) ⊂ [m_Q^{pl}/2, M̃_Q^{pl}] at real U_r, so ‖T^{pl}(U_r)^{−1}‖ ≤ 2/m_Q^{pl}. T^{pl}(U^B) − T^{pl}(U_r) is analytic in 𝓗^B and vanishes at 0. Its operator norm, with the kernel decay of §9.4, is at most C_{T,pl}B₅ε₁(D), since T^{pl} is built from Q^{pl}, which is local and analytic in the configuration. For C_{T,pl}B₅ε₁(D) ≤ m_Q^{pl}/4 the Neumann series gives (T^{pl}(U^B))^{−1} with norm at most (2/m_Q^{pl})/(1 − ½) = 4/m_Q^{pl}, uniformly in the volume, and with the decay of §9.4 at half its rate. (C_{T,pl} is not §8.2's C_T.)

*The coarse half.* Each step of §9.3–9.6 at a := a_j is one of three kinds.
- The Taylor expansion (9.5) of the blocking artifact is per coarse plaquette. It uses the plaquettes of U^B and their first differences, so it holds at ε₁(D) on □_in, and on a layer of the scale p it holds at ρ_p in the units of a_p.
- U^A is the fixed point (9.6) of VAR's map (113)–(121), T(A) = −𝔊J − 𝔊(δV/δA′)(A), at complex data by the fixed-point step above.
- The residual (9.8) uses PBG (3.42) and (3.44) for 𝔊 at the background MU^B, which lies in PBG's complex class by the step above. These hold on the domain □₀ by PBG p.395 l.11–13, and at complex regular configurations by VAR p.309 l.1–4 and RG I p.273 l.2–3.

*The localisation of the fixed point.* The source J of (9.6) is the blocking artifact. By the Taylor step, ‖J‖_κ ≤ C_J′ with C_J′ a constant of the class: on the layers of the scale ≥ j it is at most ρ_j, and on a layer of the scale p < j at most ρ_p in the units of a_p, which the weight of ‖·‖_κ allows. 𝔊 maps ‖·‖_κ to itself with the norm C_Gc_{δ₀/16}L^{3−ε₀} under (W-κ). The nonlinear term δV/δA′ is a local polynomial in A′ and its neighbours with no constant or linear part, so ‖𝔊(δV/δA′)(A)‖_κ ≤ C_Nsup|A|·‖A‖_κ, with sup|A| the unweighted layer-weighted supremum and C_N a constant of the kernel norm and of the local degree. VAR's contraction gives sup|A′*| ≤ O(1)ε₁(D) (PBG (3.41)), so for γ small T is a contraction in ‖·‖_κ on the ball ‖A‖_κ ≤ 2C_Gc_{δ₀/16}L^{3−ε₀}C_J′, and its fixed point, which is VAR's, has ‖A′*‖_κ ≤ 2C_Gc_{δ₀/16}L^{3−ε₀}C_J′. On □_in, d(·, □_in) = 0 and p = j, so a_j|A′*| ≤ C_locρ_j(D) there, with C_loc := 2C_Gc_{δ₀/16}L^{3−ε₀}C_J′. The gradient follows in the same way from the kernel of ∇𝔊. With §9.7's count, a_j|A′*| + a_j²|∇A′*| ≤ 8C_locρ_j(D) on □_in.

So U^A = e^{iεA′*}MU^B with a_j|A′*| + a_j²|∇A′*| ≤ 8C_locρ_j(D) on □_in.

*The fine half and the collar.* Lemma B (51.4) at real data gives U^B = U^B_1(□₀, MU^B). This is run B's one-step problem on (Ω^B_0, Ω^B_1) = (□₀^+, □₀) with block data MU^B on □₀ and collar data Q_1^{s*}𝐔 on C, by 69.2. By the identity theorem as above the identity holds at complex D. ι_{□₀}(U^A) is the one-step problem on the same (□₀^+, □₀), with block data U^A and collar data Q_1^{s*}U^A. On C, Q_1^{s*}U^A reads U^A outside □₀, where U^A = 𝐔. So Q_1^{s*}U^A = Q_1^{s*}𝐔 on C, and the two problems have the same collar data. They differ only in the block data on □₀, U^A against MU^B, which is §9.7's comparison. §9.7 then runs with the reference U₀′ := e^{i(ε/L)ℒA′*}U^B and the one-step operators at complex configurations, as in the coarse half. ℒ has exponential tails, so U₀′ matches the block data up to an error of order e^{−½δ₀w}ρ_j on the blocks at distance w from □_in, within VAR's allowance |Ū₀ − V| < C₁ε₁. This gives ι_{□₀}(U^A) = e^{i(ε/L)A″}U₀′ with ‖A″‖ ≤ C(ε₀)L^{ε₀j}·8C_locρ_j(D) on □_in. Since L^{ε₀j}ρ_j(D) = C_G(ε₀)L^{−(1−2ε₀)j}ε₁(D) ≤ C_G(ε₀)ε₁(D) for ε₀ < ½, this is uniform in j. At j = 0 both sides are ι_{□₀}(D).

*The localisation.* ι_X reads U^A on X^∼ ⊂ □₀ only, and it is the local one-step minimiser on X^∼ with the collar data of the Cauchy note's §9.8. Its distance on X from ι_{□₀}(U^A) is §9.8's tail. At real data ι_{□₀}(U^A_j(□₀, D)) is the minimiser of the X^∼-problem at its own data (51.4, Lemma A). The criticality equation of that problem at its data is analytic in D and holds at real D, so it holds on the polydisc, and §9.8's tail follows with the operators at complex configurations, through CRE (3.6)–(3.7) and VAR (190) at complex regular configurations (VAR p.309 l.1–4).

Hence, with C_ι(ε₀) := O(1)(C(ε₀)C_loc(1 + C_G(ε₀)) + C(ε₀, δ₀M₁)), uniform in j ≥ 0 (this C_ι is the Cauchy note's C_σ̂ with C_loc, not §9.8's tail constant O(1)LC_LC_F),

(69.1) ι_X(U^A_j(□₀, D)) = e^{i(ε/L)𝐒_X(D)}U^B_{j+1}(□₀, D) on X ⊂ □̃², with a_j|𝐒_X(D)| + a_j²|∇𝐒_X(D)| ≤ C_ι(ε₀)ε₁(D).

No factor L^{j−k} enters (69.1), and none is needed: the bound is proportional to ε₁(D), and 69.4 compares ε₁(D) with the radii.

### 69.4 The Lift Condition at the Composites (Derived)

*Run A's data.* The composite's data are exp i(τB_□ + B′), with B_□ = Q(ηA) and A = A(𝐀, L^{−1}𝐇_{k+1}) (RG I (3.30), (3.48)), and with τ and B′ complex in the Cauchy estimates. V₀ is their G-valued factor in the polar decomposition of 69.3. Then |(1/i)log V′| ≤ O(1)θ_ι(|τ|B₃²O(1)Mα₀ + α₁ + α₂ + α₃), and the α₀ term is at most ½|τ|α₁ by RG I p.277 l.54. So |(1/i)log V′| ≤ O(1)θ_ιr_{1,j} on the τ-disc of fixed radius, with α ≡ r as in the Cauchy note's l.122. The plaquettes of D are at most O(1)θ_ιr_{0,j}ξ² by CMP 98 Proposition 2 for the averages of a configuration in the class, and |V₀(∂p) − 1| ≤ |D(∂p) − 1| + O(1)|B| with B := (1/i)log V′, so the plaquettes of V₀ obey the same bound with a larger O(1). So ε₁(D) ≤ c_Dθ_ι(1 + C₁/C₀)r_{0,j}, with c_D any constant at least the O(1) of this bound and at least the bound of 69.5, which we impose, using r_{1,j} = (C₁/C₀)r_{0,j}, which is q₀ = q₁. With q₁ > q₀ this fails, so q₀ = q₁ is essential here. It is the SW closure's §2 choice, accepted provisionally.

*Run B's membership.* Lemma 4's proof (RG I p.277 l.34–p.280 l.21) uses (3.39)–(3.40) for run A's composite. Run B's composite at run A's data D has no counterpart of (3.40). So its membership comes from 69.3's bounds directly, as in RG I (1.17). On □_in, U^B has plaquettes and complex part at most c_U(B₃ + B₅)ε₁(D) in the units of a_j, with c_U the O(1) of 69.3. By (69.1), ι_X(U^A_j(□₀, D)) is U^B_{j+1}(□₀, D) twisted by e^{i(ε/L)𝐒_X} with h := C_ι(ε₀)ε₁(D) in the units of a_j, and by 68.1 the twist moves each conditioned quantity by at most C_tw^cC_ι(ε₀)ε₁(D) times its scale factor, the factor C₀/C₁ of the A′ conditions included in C_tw^c.

*θ_ι.* Let

  θ_ι := min{[2B₃c_D(1 + C₁/C₀)(c_U(B₃ + B₅) + C_tw^cC_ι(ε₀))]^{−1}, [C_{Q*}O(1)(B₃ + B₅)c_D(1 + C₁/C₀)]^{−1}, 1/(8B₃)}.

R-Δ is run on the class at the radii θ_ιr_{i,j} in place of r_{i,j}. Run B's activity domain is not shrunk: the lifted configuration is checked against condition (a) at r_{·,j}/(2B₃), the radius at which Lemma 4 places run B's input, while only R-Δ's evaluation runs at θ_ιr. By the first entry, the lifted configuration satisfies (i), (ii), and the plaquette half of (iii) at r_{·,j}/(2B₃) on X, using r_{0,j} ≤ r_{1,j}. (iv) follows by RG I (1.17), which applies Proposition 9 to the complex data M^·(𝐔) and so needs (ii) as well as the plaquettes. Run A's current is that of the minimiser at the data D, at most O(1)(B₃ + B₅)ε₁(D) in the units of the layer by Proposition 9 and (19)–(21); by the second entry it is at most θ_ιr_{0,j}/C_{Q*} at the evaluation radius of 66.4. The current of the lifted configuration then follows by the Cauchy note's *Complex domain.*, with run A's current bound r_{0,j}/C_{Q*} through that note's reading of *The class*, as at the real minimisers (l.196).

θ_ι depends on d, L, ε₀, B₃, B₅, C_{Q*}, C₁/C₀, C_tw^c, C_G(ε₀), and C(ε₀, δ₀M₁) through C_ι. It is independent of γ because C₁/C₀ is a fixed choice: CRE bounds C₀ and C₁ only from below. The constraint C₁ > 2B₃²O(1)LMC₀ of 66.1 does not involve θ_ι, so there is no circularity. 68.2's c_ρ is defined after θ_ι.

So condition (a) holds at every composite at which R-Δ evaluates the lifted term G. The glued member Ŵ_z of 44.2 agrees with P_j𝐔 = U^A_j(□₀, M^·(𝐔)) on X^∼, so ι_X(Ŵ_z) = ι_X(U^A_j(□₀, M^·(𝐔))), and the same holds there. The callers read (5.1c) at the evaluation radius θ_ι²r of 66.4, so their configurations lie in the class at θ_ιr for γ small, and their composites in Lemma 4's output at θ_ιr. The cost of the smaller radius is in the constants of R-Δ (69.6).

### 69.5 The Complex Data of the Fluctuation Integral (Derived)

The same argument with □₀ replaced by the whole domain of the step and j by k applies to the minimisers U^A_k(𝐕) at complex data 𝐕 = V′V₀. On the all-small-field torus of the Cauchy note's §9 this is direct; on multiscale domains 69.2–69.3 apply with the domain sequence of the step in place of the cube sequence. It gives ι(U^A_k(𝐕)) = e^{i(ε/L)𝐒(𝐕)}U^B_{k+1}(𝐕) with a_k|𝐒| + a_k²|∇𝐒| ≤ C_ι(ε₀)ε₁(𝐕). In the units of a_j the bounds carry L^{j−k}, and r_{0,j} ≥ r_{0,k}L^{j−k}. The localised lift then follows by §9.8's tail as in 69.3.

The sufficient condition is that of 69.4: ε₁(𝐕) ≤ c_Dθ_ι(1 + C₁/C₀)r_{0,k}. The complex points of the Cauchy note's §8.2 come from the disc in t of radius T = m_k/sup_b|g_kCA(b)|. Along it the complex part of the data reaches m_k = α_{3,k}/2, a fixed fraction of the radius, not a fraction that tends to 0. With R-Δ at θ_ιr, m_k is computed at these radii: |B| ≤ m_k ≤ ½α₃(θ_ιr) ≤ βL^{−2}θ_ιr_{0,k}/(4B₃), by Lemma 4's restriction 2B₃α₃ ≤ βL^{−2}α₀. So 2|B|/C₁^V ≤ c_Dθ_ιr_{0,k} for c_D ≥ β/(2B₃C₁^VL²), which is imposed in the choice of c_D in 69.4. ε₁(V₀)/r_{0,k} ≤ C_{ε₁}ε_k/r_{0,k} → 0, since q₀ > p₀. So the condition holds at §8.2's points for γ small.

### 69.6 R-Δ at θ_ιr: The Callers (Derived)

R-Δ runs on 𝒫_j(X; θ_ιr) at every scale. The Cauchy note and the LF note use r in three ways:
- as the radius of Cauchy estimates, where the constants gain powers of θ_ι^{−1};
- as the class in which the evaluation points must lie;
- through d_j, the smallest constant on the class.

The callers are the following.
- *§8.6 and the sums of d_j.* These are sums of per-point bounds whose constants are those of R-Δ. They gain θ_ι^{−p} with p the order of the Cauchy estimates. R-Δ uses at most second derivatives in the field and one Cauchy estimate in t, s, and τ each, so p ≤ 5.
- *The next-scale output class.* Lemma 4's restrictions are homogeneous in the radii, and its smallness conditions are preserved under scaling down. So the output lies in the class at θ_ιr_{·,j+1}, and the induction runs at θ_ιr at every scale.
- *The LF note's (LF-2).* h_n = C_hθ̃^n with C_h enlarged by the same powers of θ_ι^{−1}. θ̃ is unchanged.
- *The evaluation points.* They lie in the class at the evaluation radius θ_ι²r (66.4): the real points for γ small, since α′/ε → ∞, §8.2's complex points by 69.5 and 66.4, the line's points by 68.4, and the composites by 69.4.
- *E₀'s recovery factor.* O(1)α₂^{−1}ε₁ becomes O(1)(θ_ια₂)^{−1}ε₁, which still tends to 0, and T₀ = m_k/ϑ_k ≥ 2 holds for γ small.

So the change of norm costs constants only, and no statement changes its form.

### 69.7 Status

Reduced, not reviewed: 69.2–69.6, to the open items below. Quoted from the print: VAR (1), (3), (7), (9)–(10), (19)–(21), (171)–(173), (190), p.277 l.17, p.278, p.307 l.2–4, p.309 l.1–4, Theorem 1, and Proposition 9; PBG p.395 l.11–13, p.396 l.33–50, (3.37)–(3.38), and Theorem 3.4 (which does not cover 𝔊; the complex 𝔊 rests on VAR p.309 l.1–4 alone); RG I p.262 (iv), p.273 l.2–3 and l.39–42, p.277 l.34–p.280 l.21, p.277 l.54, (1.11)–(1.14), (1.17), (3.30), (3.39)–(3.40), (3.48), and Lemma 4 with its proof; CRE (2.28); CMP 98 Proposition 2. Used from the notes: 44.2, 51.4 (Lemmas A and B), 66.1, 66.4, 68.1–68.2, 68.4, the Cauchy note's §§8.2, 8.6, and 9.1–9.8, §10.3, *Complex domain.*, l.122, and l.952, and the SW closure's q₀ = q₁, a provisional hypothesis.

New conditions: the collar width w_c > R₁M₁ε/L; (W-κ): (δ₀/16)R₁M₁ ≥ (3 − ε₀)log L + 1; C_{T,pl}B₅ε₁(D) ≤ m_Q^{pl}/4; c_D ≥ β/(2B₃C₁^VL²); ε₀ < ½; for the κ-norm lemma, κ ≤ δ₀/32, so that κ and the layer factor leave part of the kernel's ⅛δ₀ decay and the bound is free of the volume. R = R₁ is RG I's own choice and is not changed.

Derived given the open items: (69.1) on X ⊂ □̃² with the bound C_ι(ε₀)ε₁(D), uniformly in j; the lift condition at the composites of Lemma 4 and at the complex points of §8.2. Condition (a) at the composite holds with run A's current at most r_{0,j}/C_{Q*}; the radius bookkeeping between θ_ιr and θ_ι²r is to be rechecked against it.

The weakest step: the fine half of (69.1), the localisation of A″ to □_in.

Open:
- the fine half: the localisation of A″ to □_in is not derived, and the mechanism "U₀′ matches the block data up to an error of order e^{−½δ₀w}ρ_j" does not hold as stated;
- the torus and single-scale results of the Cauchy note used on the multiscale composite: VAR (14) for MU^B, the cube-gauge regularity of M(U_r) (§9.8), the multiplier identity D_V*λ^B = 0 and the 𝒯-part of (9.7) (§10.3), and the spectral bound of T^{pl} (§9.4);
- the multiscale case of 69.5: 69.3 bounds the comparison on □_in only, not layer by layer;
- the collar data Q_1^{s*}𝐔 need the regularity of 𝐔 outside □₀, inside ε₁(D);
- the first two covariant derivatives of the comparison, which the Cauchy estimate gives only with the local-structure argument and the lattice inequality;
- the contraction ball of 69.3 is to be intersected with VAR's sup-ball; δV/δA′ is analytic, not polynomial;
- ε₁ of the polar factor needs an O(m_k) term.

Treated elsewhere, with their status recorded there: (5.1c) at the near domains that meet the cut (§62, 63.4, and 68.4).

## 70. The Variation Group (5.1v) at the Near Domains

The Cauchy note bounds the group irr^B_{j+1}(U^B_{k+1}) − irr^G(U^A_k) through the pair line of its §5. That argument uses four properties of run B's term, and none of them depends on whether the domain is near or far: analyticity on run B's class over the domain on which the term depends, the bound (I.1.18) there, gauge invariance, and the lift condition at the two endpoints. Under R-data a near-domain term depends on 𝐔 through its data on □₀, so its domain of dependence is X ∪ □₀. With the lift localised on that domain, the pair line runs at the near domains as the Cauchy note runs it at the far ones, and no composite of run B at a lifted configuration has to be compared with another.

### 70.1 The Sources (Read)

- CRE p.259 l.40–44: each term (i) depends on U_k restricted to X; (ii) extends to an analytic function 𝐄^{(j)}(X, (𝐔, 𝐉), z) on U^c_j(X, α_{0,j}, α_{1,j}); (iii) is gauge invariant; and (iv) satisfies (I.1.18). RG I p.263 l.23–27 states the same, with the dependence on (𝐔, 𝐉)|_X.
- RG I p.275 l.1–13 and (3.24): in Bałaban's proof the near-domain terms are read through U_{k+1}(□₀, M^·(𝐔)), extended as 𝐔 outside □₀. R-data, (G.256) of this note, is that reading at B̃_□ = 0 (CRE p.280 l.18–19), with the composite's current.
- The Cauchy note: l.64 (ι_X for a localisation domain X, a function of U on X^∼ with Mι_XU = U there, and the pair lift), l.70 (G), §5 (*The lift condition.*, *The pair line.*, *The current along the pair line.*, the action part, *The moment of the lifted term.* at l.210, (5.1v), and the sum over j), l.150 (the case n = j), and l.889–892 (the fluctuation-dependent version on the real diameter).

### 70.2 The Domain of Dependence (Derived)

Let X be a near domain of the cube □₀ at the scale j. Under R-data the term at 𝐔 is 𝐄^{(j)}(X, P_n𝐔) with the composite's current, and P_n𝐔 on X is a function of the data M^·(𝐔) on □₀. So the term depends on 𝐔 restricted to Y_X := X ∪ □₀, and not on 𝐔 elsewhere. Y_X is a union of M-cubes of the scale j that contains X^∼ ∪ supp h_z (44.2).

Its decay weight stays e^{−κd_j(X)}. □₀ = □̃⁵ consists of M-cubes of the scale n, each a union of L^{d(n−j)} blocks of the scale j, so d_j(Y_X) ≤ d_j(X) + O(1)L^{d(n−j)}, and a weight read on Y_X would cost e^{O(1)κL^{d(n−j)}}, which is not uniform for n > j. So the near term is not treated as localised on Y_X for its weight: Y_X is only its domain of dependence, and the bound (I.1.18) is the one on X.

G at a near domain is the Cauchy note's l.70 with the localisation domain Y_X in place of X: G(X, (𝐔, 𝐉), z) := 𝐄^{B,(j+1)}(X, (ι_{Y_X}𝐔, Q₁^{pl}(ι_{Y_X}𝐔)*𝐉), z). ι_{Y_X} is l.64's localised lift for the domain Y_X, a function of 𝐔 on Y_X^∼ with Mι_{Y_X}𝐔 = 𝐔 there. So run B's term reads at the pair lift exactly the data M^·(𝐔) on □₀ that run A's term reads, and no extension of the lift off its domain enters.

The class of a near-domain term is the class on Y_X. Its analyticity and the bound (I.1.18) there are RG I Lemma 4 for the composite, followed by (ii) and (iv) on X. At n = j they are 66.2's run of Lemma 4 at the input radii α(1 − β_IL^{−2})/(1 + 7β_I). For run B the same holds with run B's radii, as in 69.4.

### 70.3 The Pair Line at a Near Domain (Derived)

The Cauchy note's *The pair line.* applies with Y_X in place of X:
- *The representation.* §9.7 and the localised lift give ι_{Y_X}U^A_k = e^{i(ε/L)𝐒_{Y_X}}U^B_{k+1} on Y_X^∼, with 𝐒_{Y_X} and its gradient at most σ̂_{k,j}L^{j−k} in the units of a_j. The tail of the localised lift is measured from ∂Y_X^∼, which is farther from X than ∂X^∼, so σ̂_{k,j} is unchanged.
- *The configuration part.* Along W(s) := e^{is(ε/L)𝐒_{Y_X}}U^B_{k+1}, for |s| ≤ T := r_{0,k}/(16σ̂_{k,j}), W(s) stays within ¼r_{0,j} of U^B_{k+1} on Y_X, so it lies in run B's class on Y_X, where the term is analytic and at most E₀exp(−κd_{j+1}(X)) (70.2). Cauchy's estimate gives the Cauchy note's C_σ(σ̂_{k,j}/r_{0,k})E₀ for T ≥ 2. For T < 2 both endpoints lie in the domain, the endpoint s = 1 by the lift condition on Y_X, and the bound is 2E₀ < 64(σ̂_{k,j}/r_{0,k})E₀. No smallness of σ̂_{k,j}/r_{0,k} is used, so the argument holds on the real diameter of the fluctuated block field, where ε₁ = O(1)α_{0,k} (the Cauchy note's l.889).
- *The current part.* Under R-data the term reads the composite's current and not the current slot. So F(1, 1) = F(1, 0), and the current part is zero at the near domains.
- *The lift condition on Y_X.* At the real minimisers it is the Cauchy note's derivation, which is per localisation domain and uses only the localised lift's tail. At the complex data of the fluctuation integral it is 69.5 on Y_X.

### 70.4 The Moment and the Action Part (Derived)

- *The moment.* The Cauchy note's l.210 argument for ι_{Y_X} in place of ι_X gives the same boundary term, since it uses only the decay of the localised lift's linearisation at 1 from the boundary of its domain, and supp h_z ⊂ Y_X lies at least M blocks of the scale j inside Y_X^∼. So the coefficients of N_j are at most 2C_Π(j)E₀e^{−δ₀M₁L^j}, as there.
- *The action part.* It is the Cauchy note's, at two real minimisers. Under the counterterm clause of 62.3 the counterterm reads P_n of the configuration, which at the stopping-scale pair is the minimiser itself (44.2, and Lemma B of 51.4).
- *The age j = k.* There n = j, and the group is bounded directly: each value is at most E₀exp(−κd(X)) by 70.2, and the age factor (L^{j−k})^{4+β′/2} is 1. This is the Cauchy note's l.150 treatment, and it fits (5.1v) with E_V ≥ 2E₀.

So at the near domains (5.1v) holds as the Cauchy note states it, with the same E_V, the far and near domains together counted by C_X. The 𝐑-terms' young ages are the same, with (2.31) in place of (I.1.18) (CRE p.260 l.18–24), since the argument uses only (i)–(iii) and the sup bound.

### 70.5 The Pairs of LF Members (Derived)

At a pair of LF members the group is the LF note's joint line f(t) = V^B(Y)[c(t)], c(t) = e^{i(ε/L)t𝐒_c}c^B, read on each term's domain of dependence as in 70.2. Its near-domain terms read P_nc(t), whose class on Y_X at complex t is 68.2, and the bound on the line's disc is the LF note's. No comparison of two composites at different data enters.

### 70.6 Status

Derived, not reviewed: 70.2–70.5. Quoted from the print: CRE p.259 l.40–44, p.260 l.18–24, and p.280 l.18–19; RG I p.263 l.23–27, p.275 l.1–13, (3.24), and (1.18). Used from the notes: R-data (G.256), 44.2, 51.4, 62.3, 66.2, 68.2, 69.4–69.5, and the Cauchy note's l.64, l.70, l.150, §5, §9.7, and l.889–892.

G at a near domain uses the localisation domain Y_X = X ∪ □₀. Its other uses, (5.1c) for Δ (§§62–69) and Π^G, read it there too. §69 compares the lift on □_in ⊂ □₀ ⊂ Y_X, so its bounds hold for ι_{Y_X} with the localisation tail measured from ∂Y_X^∼.

The weakest step is the identification of the near term's domain of dependence with X ∪ □₀. It follows from R-data. Under CRE (i) alone the domain would be X, and then G is the Cauchy note's without change.

Open:
- (5.1c) for the redefined G at the near domains for j < k, an input of 70.4(d) that the Cauchy note marks open;
- the replay of the changes that the lift domain Y_X = X ∪ □₀ makes in Δ_j, Π^G, N_j, the norm d_j and its fixed point of the Cauchy note's §8.7, and §§62–69; G now depends on the layer n of z, so the uniformity of d_j in k is to be rechecked;
- the membership of W(s) and of the lift in run B's layer-n input class of Lemma 4 on □₀: it is stated from scale-j estimates on X, and the rescaling to the units a_n, with r_{0,n} ≥ r_{0,k}L^{n−k}, is not written;
- the matching of the two runs' cube sequences on □₀: run B's composite also reads the fine lifted field on the outer shell of □₀, so "the data that run A's term reads" holds only up to that shell;
- R-data for the 𝐑-terms, and the current part of the LF note at the near domains.

## 71. The Top N₀ Layers of an R-Operation: The Geometry and the Print

### 71.1 The Geometry (Derived)

Let z lie in the top layer n = k′ of the R-operation of the step k′, with □₀ = □^{∼5}, 5M wide in the units of the scale n. In these units:
- The top N₀ layers are each one M-cube of their own scale wide (LFR I p.179 l.19–24), so together they are at most M(1 + L^{−1} + L^{−2} + ⋯) ≤ 2M wide.
- The middle layers h + 1 ≤ m ≤ k′ − N₀ are MR_m wide in their own units (46.4), that is MR_mL^{m−n} in the units of the scale n. At m = k′ − N₀ + 1 − i this is MR_mL^{−N₀+1−i}, and L^{N₀−1} = R_{k′−N₀+1}, so these widths are below 2M in total, as 63.4 found.

So □₀ reaches the strips at the cut, and the finest layer met can be h. The ratio of the layer-n radii to those of the finest layer met is then L^{3(n−h)}(1+β₀)^{2(n−h)}, not the L^{3N₀}(1+β₀)^{2N₀} of 63.5. On the middle layers inside Z the configurations carry fluctuations at their own scale m, the term R_mε_m of 65.3's envelope. In the units of the scale n this term is R_mε_mL^{2(n−m)}, which exceeds α_{0,n} once n − m exceeds a multiple of log log g^{−2}. So Lemma 4 at the layer-n radii on □₀ doesn't work there, for the actual configurations as well as for the class.

### 71.2 The Print (Read)

LFR II p.372 l.2–48 and p.373 l.1–40 treat the near domains at an R-operation as follows.
- (1.59) is written for X ⊂ Z^c and X ⊂ □^{∼2}. Its composite is U_j(𝐁_j(□₀), ·), on the term's own determining set at the scale j, and RG I Sects. 3–5 are applied "with η replaced by L^{−n}".
- The bracket of (1.59) carries the whole dependence on 𝐇″_k(g_kB). It is expanded by RG II (1.9)–(1.10) ([I]'s (6.9)–(6.10)) with σ₀ the cubes disjoint from □₀ and Λ^∼. The surviving terms are localised in domains Y₀ ⊃ □₀ that contain a component of Λ^∼. They are resummed for each Y₀ and bounded as boundary terms by (2.42) [III], "small" and exponential in d_k(Y₀) (p.372 l.12–28).
- The first term of (1.59), 𝐄(X, U^0_k, z), passes through the same identities at U_{1,2}, U_1, and finally U_k, where it is a term of the new action (p.372 l.36–44).
- Terms with X meeting Z go through the representations (1.61)–(1.63) (p.372 l.49 onwards) and become boundary terms or 𝐑-terms.
- After the R-operation, the terms V(Y, U_k) of the domains Y that contain components of Z depend on the large-field sequence restricted to those components, and the terms localised in a component of Z^∼ go into the operations 𝐓′_k (LFR II p.379 l.21–25).

The later steps are CRE's. CRE admits Λ_j = Ω_j "as a result of an 𝐑-operation" (p.255 l.1–3). It requires its Ω_j and Λ_j to be unions of MR_j-cubes with boundaries at least 2MR_j apart only for the domains "determined by the j-th renormalization transformation, but not by the 𝐑-operation" (p.256 l.21–23). Its near-domain analysis is stated for every z ∈ Λ_j^0 ∩ (Ω_n ∖ Ω_{n+1}) with □ ∈ π_n, and the configuration on Ω_n ∖ Ω_{n+1} "coincides with a U_n-type configuration, but the difference is seen in bounds only" (p.279 l.43–p.280 l.15). It doesn't give a separate argument for the compressed layers of LFR I p.179, whose widths are one M-cube of their own scale. The depth of the layers that □₀ can meet there is bounded by N, the number of steps before the R-operation, and N is "much greater than N₀" (LFR I p.179 l.9–11).

### 71.3 The Near Domains of a Cube Three Scales Finer (Derived)

The obstruction of 71.1 is the reach of □₀ = □^{∼5}, five M-cubes of the scale n, against layers one M-cube of their own scale wide. At a point z of the layer n the bound is taken with the cube of the scale p := n − 3 that contains z. Its □′₀ reaches only the layer n − 1, so no deep layer enters, and the price is a fixed power of L in the age factor.

*The geometry.* By admissibility (46.4), in every sequence of the expansion Ω_n and Ω_{n−1}^c are separated by one layer of cubes of the scale n of side at least M, whatever R-operations acted before. For the top layers of an R-operation this is LFR I p.179 l.19–24 itself, and a layer of a T-operation has width at least 8MR_n (46.2). So in every case dist(Ω_n, Ω_{n−1}^c) ≥ M in the units of the scale n. Let □′ be the M-cube of π_p that contains z. Ω_p is a union of cubes of π_p, which is compatible with it (CRE p.256 l.21–23, p.264), and z ∈ Ω_n ⊂ Ω_p, so □′ ⊂ Ω_p. □′₀ := □′^{∼5} lies within 6ML^{p−n} = 6ML^{−3} of z in the ℓ^∞ distance of the units of the scale n, and 6L^{−3} < 1 for L ≥ 2. So □′₀ ⊂ Ω_{n−1}, and □′₀ meets the layers n − 1, n, n + 1, … only.

*The construction at z.* For the near domains of z, X ⊂ □′^{∼2}, R-data reads the composite on □′₀. This is a choice of the construction at z, of the same kind as 62.3's clause. At the members it doesn't change the total: by 66.1, P_□c = c on every cube whose layers refine the member's determining set, and □′₀ is such a cube, since it lies inside Ω_{n−1}, where the member's blocks are of the scales n − 1 and coarser. The domain of dependence of a near term is X ∪ □′₀ (70.2).

*The near domains, X ⊂ □′^{∼2}.* All layers that □′₀ meets are coarser than the scale p, so in the units of the scale p their bounds are at most those of the layer p (the Cauchy note's l.148). So the configuration on □′₀ satisfies the conditions of the (N) case at the layer p, with no enlargement of the radii. The Cauchy note's derivation of (5.1c) in the (N) case (l.140–152), with its *Mixed radii.* for p − j ≥ 1 and its direct bound at p = j, then gives Σ_{X⊂□′^{∼2}}|irr(Δ)(X, 𝐔, z)| ≤ dE₁(L^{j−p})^{4+β′}. The counterterm and N_j are read at z, with supp h_z within 2a_j ≤ 2a_p of z, inside □′. For p < j the term is not at an older scale than its point's cube, and the direct bound of l.150, O(1)(2 + c₂^{−2})dE₀, applies. Since (L^{j−p})^{4+β′} = L^{3(4+β′)}(L^{j−n})^{4+β′} ≤ L^{15}(L^{j−n})^{4+β′}, and (L^{j−n})^{4+β′} ≥ L^{−15} when n − j ≤ 3, the near part is at most dE₁L^{15}(L^{j−n})^{4+β′} in both cases.

*The other domains, X ∋ z with X ⊄ □′^{∼2}.* Such an X crosses the two layers of M-cubes of the scale p around □′, so its tree length in M-cubes of the scale j is at least 2L^{p−j} − 1 for p ≥ j. By the condition (a), |Δ(X, 𝐔, z)| ≤ 2E₀exp(−κd_j(X)), and the count of the domains through z gives Σ_X 2E₀exp(−κd_j(X)) ≤ 2C_κE₀exp(−(κ − κ_c)(2L^{n−j−3} − 1)), with κ_c and C_κ Bałaban's counting constants (κ > κ_c, RG I (1.18)). Let C_far := sup_{m≥0} exp(−(κ − κ_c)(2L^{m−3} − 1))L^{(4+β′)m}, which is finite and a constant of L and κ − κ_c. Then this part is at most 2C_κC_farE₀(L^{j−n})^{4+β′} ≤ dC_κC_farE₀(L^{j−n})^{4+β′}, since d ≥ 2, so with the near part the constant of (5.1c) here is C_α^{(71)} := L^{15}C_α^T + C_κC_far, C_α^T that of 63.3. For p < j these domains have no age to lose, and the direct bound applies as above.

So at every point z, in every layer and at every kind of operation, including layers changed by earlier or overlapping R-operations, (5.1c) holds with C_α^{(71)} := L^{15}C_α^T + 2C_κC_far in place of C_α, uniformly in j, n, and k. At real points this holds as in the (N) case. At complex points it holds under the Cauchy note's reading of (I.3.26), as in 68.4. In particular it holds at the near domains that meet the compressed top layers of an R-operation, at the step of the R-operation and at the later steps, where {Ω″_j} is the domain sequence (LFR I p.179 l.40). The enlargement of LFR I (1.49) does not enter, since □′₀ lies in Ω_{n−1}, where the thresholds of the layers n − 1 and coarser are used as they are.

C_α enters the Cauchy note only through E₁(α) = C_αE₀ and ε*_k, as at the end of 63.3, so the change moves only the threshold on γ.

### 71.4 Status

Derived here, not reviewed: 71.1, 71.3. Read: 71.2. Quoted from the print: LFR I p.179 l.9–11, l.19–24, and l.40; CRE (2.5), p.256 l.21–23, and p.264; RG I (1.18). Used from the notes: 46.2, 46.4, 62.3, 63.3, 66.1, 68.4, 70.2, and the Cauchy note's l.140–152.

Reduced, conditional on 46.4 and 66.1 and on the inputs of the (N) case (the lift condition at the composites, §69): (5.1c) at the near domains that meet the top N₀ layers of an R-operation, at the step of the operation and at the later steps, for domain sequences with the one-M separation of 46.4, with the constant C_α^{(71)}. Where 63.2's six-layer bound holds, it gives the smaller constant of 63.3.

Open:
- the M₁-layered determining sets of the composites and of the representation configurations (CRE p.256 l.58–62, LFR II p.373 l.26–27), which do not have the one-M separation;
- the construction change from □ ∈ π_n (LFR II p.372 l.3) to □′ ∈ π_{n−3}: it is not defined for p < j, and it is not replayed through the localisation of the boundary terms in (1.59). The bracket of (1.59) and the terms with X meeting Z are the LF note's (LF-A) (71.2).

The weakest steps:
- The construction choice at z: the near domains are those of the cube of the scale n − 3. It changes R-data's composite at the near domains of z, and 66.1 keeps the total at the members.
- The reading of admissibility in 46.4.

## 72. The Nonlinearity of the Lift at the Decoupled Configurations (the Piece (δ))

The LF note's piece (δ) (its l.453 and l.550) compares run B's term at ι_X(W), W := e^{iη𝐇^A(s)}c^A, with its term at run B's decoupled configuration. After (iii) replaces 𝐇^B(s) by the transferred field ℒ𝐇^A(s), what remains is the nonlinearity of the lift: ι_X(e^{iη𝐇}c^A) against e^{iηℒ𝐇}ι_Yc^A, with 𝐇 := 𝐇^A(s), and the currents. The configuration part is derived here. Its relative size carries the factor ε/a_m, so it is smaller than (iii)'s δ_w. The near terms read no current slot. The far terms' current slot is reduced to the multipliers of the one-step lift.

### 72.1 The Sources (Read)

- The LF note l.453 and l.550: the definition of (δ) and the order of the telescoping, with (iii) before (δ).
- The LF note l.462–466 (*The one-step problem.*, *The kernels.*, *The weights.*, *The bound.*): the derivative of ι at data V in a direction A is δ = ℒ_WA − 𝔊_W(D*Dℒ_WA + O(|F||ℒ_WA|)) at the critical background W = ι(V), with no background-change term; the kernels are bounded by a constant times e^{−δ_f|x−y|/ε} times the scale factor of their entry at the scale ε.
- The Cauchy note l.468 (§9.4): ℒg := Ig + Q₁^{pl}*(T^{pl})^{−1}(g − Q₁^{pl}Ig), with I the multilinear interpolation in the cube gauge, Q₁^{pl} := dM at the background, and T^{pl} of finite range with paths within 2L fine spacings.
- The LF note l.557: (W-δ), with δ_w(ω) ≤ C_w(ε/a_{m(ω)})^{γ_w}, γ_w < 1, and l.552–556: the bound of 𝐇″_k on the t_□ circle, where the argument stays within ¾α₂ with room ¼α₂.

### 72.2 The Configuration Part (Derived)

Let V_u := e^{iuη𝐇}c^A for u ∈ [0, 1], at the fixed s and t_□ of the bracket, and W_u := ι(V_u). Each W_u is the minimal configuration of ι's one-step problem at its data V_u, so it is critical at its own data, and the LF note's formula gives d/du W_u = e^{iηδ_u}W_u to first order, with δ_u := ℒ_{W_u}𝐇 − 𝔊_{W_u}(D*Dℒ_{W_u}𝐇 + O(|F||ℒ_{W_u}𝐇|)). At complex s the same holds on the complex class of ι's problem (the LF note's *The complex class of ι's problem.*), as in 68.5. Hence

  ι(W) = e^{iη(δ_0 + R_δ)}ι(c^A), R_δ := ∫₀¹(δ_u − δ_0)du + R_BCH,

where δ_0 = ℒ_ι𝐇 is the transferred field (the linearisation of ι at c^A), and R_BCH collects the commutators of the ordered product, which are of size η|δ||δ_u − δ_0|.

*The background dependence of the operators.* W_u differs from W_0 by the twist ∫₀^uδ, of size Ch(x) in the units of the layer j(x), where h(x) := a_{j(x)}|𝐇(x)| + a_{j(x)}²|∇𝐇(x)| (*The bound.* with the weights). ℒ depends on the background only through the transports of I and of Q₁^{pl} along paths of length at most 2Lε/L = 2ε in the fine units (§9.4), and a twist of size h/a changes such a transport by at most 2ε·Ch/a. So |(ℒ_{W_u} − ℒ_{W_0})𝐇| ≤ C(ε/a)h·|𝐇|, which in the units of a is C(ε/a)h². The 𝔊-part carries the factor ε² of the one-step kernels (*The kernels.*), so it and its background dependence are of the order (ε/a)²h in the units of a, with the change of order (ε/a)²h² at most. The gradients carry the same factors, by the kernels' gradient bounds (PBG (3.44) as in *The kernels.*). So

  a_{j(x)}|R_δ(x)| + a_{j(x)}²|∇R_δ(x)| ≤ C_δ(ε/a_{j(x)})Ŵ_h(x)²,

with Ŵ_h the weight of *The weights.* built from h, and C_δ a constant of d, L, ε₀, δ_f, and Bałaban's constants. The localised lifts ι_X and ι_Y differ from ι by their tails, at most C_tε₁e^{−½δ₀M₁L^j} in the units of every layer (*The Lift ι_Y.*), so ι_X(W) = e^{iη(ℒ_ι𝐇 + R_δ + R_tail)}ι_Yc^A on X^∼, with R_tail of that size.

*The term.* On the t_□ circle h ≤ ¾α₂ in the units of the term's scale, with room ¼α₂ (the LF note's l.554). Along u ↦ e^{iηu(R_δ + R_tail)}e^{iηℒ_ι𝐇}ι_Yc^A the argument moves by at most |u|(C_δ(ε/a_m)α₂² + C_tε₁e^{−½δ₀M₁L^j}), where a_m is the finest layer that the term reads. So the term is analytic in u on a disc of radius R_δ′ := ¼α₂/(C_δ(ε/a_m)α₂² + C_tε₁e^{−½δ₀M₁L^j}), and Cauchy's estimate bounds the configuration part of (δ) by 2/R_δ′ times the term's bound on the circle. That is at most δ_δ(m) := 8C_δ(ε/a_m)α₂ + 8C_tε₁e^{−½δ₀M₁L^j}/α₂ times the term's bound. Since ε/a_m ≤ (ε/a_m)^{γ_w} and the tail is smaller than any power of ε/a_m at fixed j, δ_δ(m) ≤ C_δ″(ε/a_m)^{γ_w}, and this part is summed over the terms with (iii)'s 12C_Hδ_w.

*The near terms.* Under R-data a near-domain term of X ∋ z reads only the data on □₀ and the composite's current (70.2–70.3). The data of ι_X(W) are W's, since Mι_X = id on its domain. The data of e^{iηℒ_ι𝐇}ι_Yc^A are W's moved by the average of e^{−iη(R_δ + R_tail)}, that is by a data shift B′ with |B′| ≤ K_M(C_δ(ε/a_n)α₂² + C_tε₁e^{−½δ₀M₁L^j}) (§44.7). So the renormalised near terms of z and the counterterm, which reads the same composite (62.3), differ by the composite at shifted data. RG I Lemma 4 makes it analytic in B′ for |B′| < α₃. The point term irr_j(z) is bounded by (5.1c), E₁(L^{j−n})^{4+β′}, at every configuration of the class at the evaluation radius (§§62–71, 68.4–68.5). So, wherever the shifted composites lie in that class, Cauchy's estimate bounds the near part of (δ) at z by (2|B′|/α₃)E₁(L^{j−n})^{4+β′}. This bound is per point and keeps the age factor, so it sums over the generations as (5.1c) does. For the renormalised 𝐄-combinations this replaces the sum of per-term bounds, which the LF note's (iii) leaves open, at the near terms of (δ). The far terms of z are bounded per term by E₀e^{−κd_j(X)}, and their count through z gives the age factor as in 71.3's *The other domains*, so their part of (δ) sums in the same way with δ_δ(m).

### 72.3 The Current Part (Reduced)

Near terms read the composite's current, so their current part is zero (70.3). A far term reads the current slot: Q₁^{pl}(ι_XW)*J(W) at ι_X(W), and at run B's decoupled configuration the current of run B's link maps. ι_X(W) is ι's minimiser at the data W, so its own current is Q₁^{pl}*λ(W) with λ(W) the multipliers of ι's problem (the Euler–Lagrange equation of the one-step problem, as in the Cauchy note's §9.4 and §10.3). So the slot difference contains Q₁^{pl}*(λ(W) − J(W)), the defect between the one-step lift's multipliers and the coarse current at the decoupled configuration. At the members, which are minimisers, it is the pair-lift current bound of the Cauchy note's *The current along the pair line.* and the LF note's *The Current at the Multiscale Chain.*. At W ≠ c^A its first-order part in 𝐇 is (dλ − dJ)[𝐇], the intertwining of the coarse covariant Laplacian with the one-step lift. That is of the type of the intertwining defects of (W-δ) (the LF note's l.557 and `WILSON_IT1_WALK_FACTOR_DIFFERENCE_2026_10_28.md`), and it is open with them.

### 72.4 Status

Reduced, not reviewed: 72.2, to the open premises below; 72.3. Quoted from the print: none new; used from the notes: the LF note's l.453, l.462–466, l.550–557, and *The Lift ι_Y.*; the Cauchy note's §9.4, §10.3, and *The current along the pair line.*; §44.7, 62.3, 68.4–68.5, §§70–71.

The weakest steps:
- The background dependence of ℒ through transports over 2ε, and of 𝔊 through the factor ε², which bound δ_u − δ_0 by (ε/a)h² in the units of a. The gradient part uses PBG (3.44) as the LF note's *The kernels.* does.
- The near part uses (5.1c) at the composites at data shifted by B′; it needs those composites in the class at the evaluation radius, which holds when K_MC_δ(ε/a_n)α₂² is at most a fixed fraction of θ_ι²r, as it is for γ small.

Open:
- The far terms' current part of (δ): the intertwining of the coarse covariant Laplacian with the one-step lift at the decoupled configurations, of the type of (W-δ) (72.3).
- The analyticity room of run B's term in the fine-configuration move: the Cauchy estimate along u uses RG I (3.31)'s room ¼α₂, which includes ‖·‖_{1,β}, while the move is controlled in sup and gradient only.
- The lift condition and the tail of ι_X at the complex decoupled W (Mι_XW = W is used there; the LF note's l.454 and l.478 have them at real members only).
- (5.1c) on the whole α₃-disc of the Cauchy estimate, not only at the actual B′: (5.1c) holds on 𝒮_z under (N).
- The identification of δ_0 = dι(c^A)𝐇 with (iii)'s transfer ℒ_ι = dι_Y(Ũ), Ũ = Mc^B: their first-order difference is not accounted for.
- The background-Lipschitz bounds of 𝔊 and of the O(|F||ℒ𝐇|) term, and the BCH correction in e^{iηR}e^{iηℒ𝐇}.

What this changes in the LF note (recorded here, not edited): its (δ) of l.17 and l.453 reduces, given the open items above, to the current item of 72.3. Its (iii) remains open through (W-δ) and the analyticity in the operators (l.551). For the renormalised 𝐄-combinations, 72.2's per-point form with (5.1c) is the per-term bound that its l.556 asks for, at the near terms of (δ). For (iii) itself it applies wherever the circle of (1.23) lies in the class of (5.1c).

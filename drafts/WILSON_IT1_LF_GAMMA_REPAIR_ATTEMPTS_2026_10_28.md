# Attempts at the Large-Field Ingredient (γ)

28 October 2026. Separate working note requested by the user. The Cauchy, large-field-depth, and walk-factor notes are not edited. Focused reviews are recorded at their stated scopes; later repairs and other calculations remain unreviewed unless expressly indicated. The note gives partial repairs and their precise remaining dependencies; it does not establish (LF) or the Cauchy estimate.

Current work is the probabilistic marked expansion in §§20–22. The latest explicit calculation is the conditional Gaussian root-dimension bound (G.114)–(G.123); its localisation and mixed-domain application are the next steps. Supporting deterministic attempts in §§13–15 are inactive following the user's instruction to focus on the probabilistic bounds. Focused reviews of earlier parts are recorded in §§11 and 19 and do not certify the full argument.

The starting files are:

- [Cauchy estimate](WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md), SHA-256 `8f7a3e6cc5c78419326fd1a650b1c18c485e8d61cdf94f353b664ec5c9ef5c34`.
- [Large-field depth](WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md), SHA-256 `e64619bd303aeafe49364cc23f94d8ffb678da618354708f2afccd2834a16a85`, called the LF note.
- [Walk-factor difference](WILSON_IT1_WALK_FACTOR_DIFFERENCE_2026_10_28.md), SHA-256 `d07788fb9a6d584036ea55b766c9dcd630573cb322c9ca3811967503dadb59c2`, called the walk note.

The LF note was saved externally during this work. Its final observed SHA-256 was `e692c2f0798734b4a85e42ab6f74463434c2db717501a80f0aa091e51f5d06e8`. Its opening list of gaps was rechecked and still lists (3), (6), (7), and (10) with the dependencies addressed below. The detailed comparisons in this note refer to the starting revision above; the externally saved changes were not overwritten.

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
\leq\exp\left(\sum_r p_r\log\max(1,L_r)\right)\;.
\tag{G.107}
$$

If L_r is uniformly bounded, this is a fixed exponential cost in history volume. If L_r is bounded by a fixed power of log g_r^{-2}, its logarithm is of order log log g_r^{-2}, and is bounded by a fixed multiple of \(1+\log g_r^{-2}\), the type of cost already present in LFR II p.380. One can therefore state the required reserve before performing any entropy sum:

$$
\text{ordinary history cost}
+\sum_r p_r\log\max(1,L_r)
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

The R₂ contribution, the first term of (G.134), the potentials in (2.20), and the large-field test in (2.22) are all in the B variables. Bound their sum by \(\widetilde\alpha|B|^2/2\), with \(\widetilde\alpha\leq C\alpha_5\) and α₅ exactly of the type in (2.23). The determinant factors introduced on replacing the complex B measure by the real reference already have cost \(e^{C\epsilon_{\rm op}n}\), by (2.17).

After integrating B as in (2.24), the remaining positive X-form is

$$
E_X+\Gamma_0^T\bigl[(C_0^{-1}-\widetilde\alpha I)^{-1}-C_0\bigr]\Gamma_0\;.
\tag{G.136}
$$

The unperturbed conditional form cancels exactly. The second term in (G.136) has rank at most n. The source's estimate immediately after (2.24) bounds its norm by C\(\widetilde\alpha\). Therefore (G.136) has rank at most 5n and norm at most Cα₅. Choose α₅ small enough that this norm is below 1/2, as in the source's Gaussian integrations. The X integral is then bounded by

$$
\exp(C'\alpha_5 n)\;.
\tag{G.137}
$$

The B determinant shift also costs \(e^{C\widetilde\alpha n}\), as stated after (2.24). A scalar mark bounded by M_I on the cutoff support multiplies these absolute estimates by M_I. The Cauchy-contour factors, the small factors of the unmarked potentials, and the large-field exponential in (2.26) are untouched. Consequently the last Gaussian factor in (2.26) may be replaced by \(e^{C\alpha_5 n}\), with n the root dimension, instead of a cost proportional to |Z|.

This proof uses the one-run R_i bounds and the one-run remainder bound after (2.24), both printed on the supplied pages. It does not require complex bilinear symmetry of the deformed C. Taking the spectral absolute value of R₁ is only an estimate of a finite-dimensional integral already assigned to its localisation domain; it introduces no new operator or locality assertion in the construction.

The argument establishes the refinement for the native RG II primitive. To use it for (1.60), one must still exhibit the corresponding three root-factorised error forms for that mixed-domain integral. The direct-sum Gaussian structure supplies the candidate forms, but the complete identification, including all source normalisers and potentials, is a separate application.

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

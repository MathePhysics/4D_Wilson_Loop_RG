# Small-field Cauchy route for Wilson loops (proposed route, draft)

Started 21 Oct 2026, 11:15. Status: draft for CLI review; revised after the r1, r2 and r3 reviews and the Lipschitz push (§7; `WILSON_CAUCHY_LIPSCHITZ_2026_10_21.md`). Nothing here is in `WILSON_FIRST_RG_STEP_V3.tex` (V3); V3 is cited by label, Bałaban by page and equation.

## OPEN MATHEMATICAL GAPS

- **LIP-1 (analyticity domains; found in the Lipschitz push, `WILSON_CAUCHY_LIPSCHITZ_2026_10_21.md` §5).** The Bałaban project's difference results (D2, D6a, D9) and its $\beta$-bound (P2) use a polarisation constant $C_\Lambda$ that is a Cauchy constant on RG1's *fixed* domains (RG1 Theorem 3, p.264). On CRE's domains $\alpha_{0,j}=g_jC_0(\log g_j^{-2})^{q_0}$ (CRE (2.28)), which this draft uses, $C_\Lambda\propto g_j^{-2}$. So the sensitivity $b_j$ of $\beta$ to activity differences grows like $g_j^{-2}$, and the coupled difference system does not close. *Closes by:* (a) the compared small-field model in RG1's fixed-constant setting (recommended); or (b) a bound on $\Delta\beta$ uniform in $\alpha_0$ via the Gaussian representation of $\Pi^{(j)}$ (C3).
- **R-S1 (dressed-loop class).**
  - *Missing:* a class of loop dressings that a general step maps into itself (V3 rem:next-step (3)(a)–(b) at a general level). The class is a one-dimensional polymer gas of matrix-valued cluster activities with localisation sums (§4.1, repaired after r2).
  - *Sub-items:*
    - (a) the activities must be built from background-covariant objects, or a matrix analogue of CRE p.259 (iii) must be proved;
    - (b) gap transports: $U_{\ell+1}(\mathrm{bg})=U_\ell(V)$ under a level-$\ell$ bond, from the composition property of $M^k$ (N12);
    - (c) a covariance decay rate $\delta$ with $\kappa<\delta/2-c\alpha$;
    - (d) the base case: a pointwise-in-$V$ cluster decomposition of V3's $dN_1/d\rho_1$, in particular of $E_{\rm def}$. V3 controls this only globally, and its local form is unproved (V3 rem:next-step (3)(a)).
  - *Closes by:* standard one-dimensional polymer methods for the formal closure. The general-step input from CRE Section 3 is unlikely to suffice alone, because CRE leaves the general-step operations undefined (W3/W6).
  - *Also from it:* $\kappa^{(K)}(C)=\mathcal W^{(K)}_0(C;1)\neq0$, from the gas split of §1.3 with convergent Mayer expansions (N9).
- **R-S2 (age decay of loop insertions).**
  - *Missing:* the line analogue of CRE Theorem 2 (2.43), in one-step form, on the complexified domain, for cluster activities.
  - *Closes by:* a (3.68)-type bound on a cube containing the support of the insertion, plus the Schwarz lemma (§4.2). (3.68) is printed for the cube $\square^{\sim n-j+1}$ only; the larger cube is to come from VAR (N13).
- **R-S3 (classical convergence).**
  - *Missing:* for fixed coarse $V$, the difference of the classical blocked actions, Hessians and loop transports of the two theories, with age decay, in polymer and analytic form.
  - *Repaired:* the scalar real form follows from the two-sided sandwich of §4.3. It needs only the age-0 difference $D_K$ and the composition property (N12).
  - *Still open:*
    - the zero $F^2$ part of $D_K$ (age 0 only);
    - the localised analytic form, which needs VAR/PRT;
    - the decay of the transport defects $\Delta_b$ (S3(iii-b));
    - S3(iii-a) in family form, over all created terms at all creation levels (§4.5, r3).
  - *Rate:* $\mu=L^{-(1-\beta)}$ for any $\beta>0$ from the printed count, with $\beta$ independent of $\beta_E$. The earlier $L^{-2}$ was a heuristic.
- **R-S4 (one-step creation of differences).**
  - *Missing:* the estimates (P-N), (P-$\beta$), (P-Y) and (P-R) of §4.4, in the universality form with the common cutoff $D_{\ell+1}$, the bounded domain $D^{\mathbb C}_\ell$ and frozen parameters.
  - *Core claim, in variation form (r3; revised in the Lipschitz push):* $\sup_{|w|\leq\rho}\|\mathbf N(I+we)-\mathbf N(I)\|\leq C\omega\rho$, resp. $\leq C\omega_g\rho$ in the $g^{-2}$ direction.
    - It holds in Bałaban's model with $C\omega\rho=2M$, where $M$ is the bound of the *new* terms: $O(1)C_3\varepsilon_1$ by RG2 (2.41). This is D2/D7 of the Bałaban project, through D_HOLO.
    - The r3 objection took $S$ to be the class bound of all terms.
    - By Lemma G (Lipschitz note §3.1) the Lipschitz bound is global on the class, so $\rho\geq4S$ is not needed.
    - The coupling direction is D6a.
  - *The frozen parameters:* the shooting argument is replaced by the a priori Lemma T (Lipschitz note §2), with the parameters frozen from the $K$-independent reference flow $\bar x_\ell$. The continuity of $\Delta\beta$ in $d$ is no longer needed.
  - *Still open:* LIP-1; the N4 transfer (LIP-2, part of R-N4); the reading LIP-3. The constants are fixed in the order $L,\lambda',C_0,E_0,\vartheta_0,\gamma,g$.
- **R-S5 (difference induction).**
  - *Written:* creation-level bookkeeping, since (2.43) is not a per-level contraction (r2), and the weighted estimate (§4.5). The linearity of the algebraic identities behind (2.43) is checked (CRE pp.279–283; RG1 p.284).
  - *Missing:*
    - R-S4 and S3 as inputs;
    - the creation-level identity of loop activities under the nonlinear merging of §4.1 (r3).
  - *Reduced in the Lipschitz push:*
    - $E_1'=(2+\vartheta)E_1/\vartheta$ follows from the linearity of the aging map, by Lemma H (Lipschitz note §3.3). This holds under the class-wide reading of CRE Theorem 2, "Under the assumptions of Theorem 1" (p.263; LIP-3). Re-running the estimates is not needed.
    - (2.43) in analytic form is not needed: D2 carries the history in creation-scale norms.
    - The weighted estimate of §4.5 is replaced by the two-sided system (E), (R), (C) and D9 (Lipschitz note §4). These include the feedback of R-terms into later terms, which §4.5 omitted.
  - *Booked since r3:* the cross term $\beta^{(K+1)}_j[A^{\eta_{K+1}}-A^{\eta_K}]$ is an S3(i)-type source.
- **R-N4 (Bałaban's bounds in the compared model; r3).**
  - *Missing:* the model compared is the N4 model, with the common gauge-invariant cutoff $D_{\ell+1}$ before each step (§1.2). Bałaban's step estimates are printed for his own gauge-fixed cutoffs. These are the Theorem 1 class bounds, $E_0$, (I.1.18), (2.43) and (2.44).
  - *Closes by:* re-running CRE Section 3 and Theorem 2 with the product of local gauge-invariant indicators, plus a REG-type comparison of the two cutoff sets.
  - *The tolerance.* It is Lemma T (Lipschitz note §2), from Corollary 8.2 of the Bałaban project. In the N4 model it needs (P2) and (C) for the N4 step (LIP-2).
  - *The Lipschitz inputs in N4 (LIP-2):*
    - the N4 analogue of RG2 (2.41) and class-wide holomorphy;
    - the a.e. continuity of the gauge-invariant indicators;
    - a shell estimate for the plaquette variable near the threshold (the cutoff part of D6a).
- **N15 (R-terms in the small-field model; r3, checked on CRE pp.263, 279).**
  - The pure small-field model has no $\mathbf B$-terms but does have $\mathbf R$-terms: the $\mathbf R''^{(k+1)}$ from the second expectation value in (3.26), and the terms of the $\mathbf R$-operation (CRE p.279).
  - (2.44) bounds them by $R_1g_j^{\kappa_0}$ per point with no age factor, with $\kappa_0\geq7$ (p.263).
  - *Consequence (corrected in the Lipschitz push):* the rate of the model is polynomial in $K$, not a power of the lattice spacing.
    - With the R-feedback of the system (E), (R), (C), D9 gives $\theta_K\leq C(\log K)^{O(1)}(K+1)^{1-p}$ with $p=3$ for $\kappa_0\geq7$. This is summable, so the Cauchy target survives.
    - The earlier $(\log K)^{O(1)}K^{-\kappa_0/2}$ omitted that feedback and is withdrawn.
    - (R) is (P-R) in corrected form; it still has to be checked against CRE (3.26) and the R-operation.
- **W5 (gauge group).** S0 is printed for $SU(2)$ only.
  - *Imported in the Lipschitz push:* for simple $G$ the matching is `RG1_Thm2_REP` (Bałaban project, `ONE_LOOP_PROOFS.md` Corollary 8.2), with uniqueness from D6. This is proved in RG1's model.
  - *Still open:* in the N4 model it reduces to LIP-2; in CRE's setting (P2) meets LIP-1.
- **Outside this route: the large-field stage (LF).**
  - *Why it is needed.* The expectation-level Cauchy estimate needs Bałaban's $\mathbf R$- and $\mathbf B$-terms. Configurations with no large fields have probability tending to 0 (§3(g), Markov lower bound), so LF is not a correction to be added at the end.
  - *The gauge-fixed cutoffs.* LF also covers the gap between Bałaban's gauge-fixed small-field cutoffs and the common gauge-invariant cutoff that defines the compared model (N4, §6).
  - *How hard it is.* Configurations near the threshold of the cutoffs occur with probability tending to 1 (§3(g)). So the discrepancy between the cutoffs is as hard as LF itself, not a small correction (r3).
  - *Two consequences found in r2 (N14):*
    - The printed (2.44) gives $\mathbf R$-terms no age factor. From printed bounds the physical rate is therefore at best polynomial in $K$, about $(K\log L)^{-\kappa_0/2}$. By N15 this already holds in the small-field model.
    - The large-field contribution per unit length diverges, so it must enter the perimeter counterterm. The physical normalisation is then not the small-field $\kappa^{(K)}$.

## 0. Legend

- [B p.x] Bałaban's result as printed, accepted under the standing rule (presented-as-true results are used unless a counterexample is found).
- [V3 label] proved in V3.
- [E] elementary, to be written out.
- [OPEN] not proved; listed above.
- Notation:
  - $\beta_E<1$ is the exponent of CRE (2.43), written $L^{-\beta_E}$; it is written $\beta$ in §3(a).
  - $\beta,\beta'$ in (0.31) are RG1's constants.
  - $\beta_j$ are the $\beta$-functions.
  - *Indices.* Route level $\ell$ is the lattice of spacing $L^{-\ell}$, so a larger index is finer; Bałaban's step index is $k=K-\ell$. Displays quoted from Bałaban (as in (G2)) keep his indices, with $j<n$ steps and age $n-j$; the route's own displays use levels, with age $j-n$ for levels $n<j$.
  - *Small-field parameters at level $\ell$.* $\varepsilon_\ell:=g^{(K)}_\ell p_0(g^{(K)}_\ell)$, Bałaban's $\varepsilon_{K-\ell}$ (CRE (2.4), p.255). $\tau_\ell$ is V3's $\tau$ (eq:marginal-fixed-forest-bound, $\tau=C[g_0(1+r)^3+e^{-cr^2}]$) with $g_0$ replaced by $g^{(K)}_\ell$, also inside $r=A_1(\log g_0^{-2})^{p_0}$.
  - *Domains.*
    - The real domain is $D_\ell=\{V:|V(\partial p)-1|<c\,\varepsilon_\ell\}$.
    - "The level-$\ell$ domain" is its bounded complex neighbourhood $D^{\mathbb C}_\ell:=\{e^{iA}V_r:\ V_r\in D_\ell,\ |A(b)|<\alpha_{0,\ell}\text{ for every bond }b\}$, with the frozen radius $\alpha_{0,\ell}$ of CRE (2.28) (repaired after r3). Without the per-bond radius the set contains complex gauge transforms and is unbounded.
    - Its relation to Bałaban's $U^c_j(X,\alpha_{0,j},\alpha_{1,j})$ goes through the background map [VAR; part of R-S4].
    - Both are the route's own definitions. RG1 p.259's $V$-condition $|\partial V-1|<\varepsilon_0$ has a fixed $\varepsilon_0$, and is printed as the "technically less convenient" alternative to $|\partial U_k(V)-1|<\varepsilon_0\eta^2$.
  - *Notation clashes.* The route's $\varepsilon_0=g\,p_0(g)$ is not RG1's fixed $\varepsilon_0$. $T^{(k)}$ in a Bałaban quotation is the route's $T^{(K-k)}$. $M$ is Bałaban's cube constant; the torus exponent is $M_T$. $n$ is Bałaban's step index or V3's side length, as the context says.

## 1. Target

### 1.1 Levels, steps, couplings

- Physical torus $\mathbb T=(\mathbb R/2L^{M_T}\mathbb Z)^4$, $M_T$ fixed, so the family of tori is RG1's (p.251) and V3's (H3). Level $\ell\geq0$: the lattice $T^{(\ell)}=(L^{-\ell}\mathbb Z/2L^{M_T}\mathbb Z)^4$ of spacing $L^{-\ell}$. Level $0$ is the unit lattice. (Changed after r3 from period $L^M$.)
- The cutoff-$K$ theory is the Wilson action on $T^{(K)}$ at the bare coupling $g^{(K)}_{\rm b}$. Bałaban's $k$-th step ($k=1,\dots,K$) maps level $K-k+1$ to level $K-k$ (RG1 (0.17), (0.19), p.255).
- Index conversion. For the cutoff-$K$ theory at level $\ell$ put $k=K-\ell$:
  - coupling $g^{(K)}_\ell:=g_{K-\ell}$;
  - background $U^{(K)}_\ell(V):=U_{K-\ell}(V)$, a configuration on $T^{(K)}$ (RG1 (0.21), p.256);
  - regular part $\mathbf E^{(K)}_\ell:=\mathbf E_{K-\ell}$ (CRE (2.25), p.259).
- Coupling matching [B RG1 Theorem 2, p.259]. For small $g$ there is a bare coupling $g_0(\varepsilon,g)$ such that every $g_k\in\,]0,\gamma]$ and $g_K=g$. With $\varepsilon=L^{-K}$ this gives $g^{(K)}_0=g$ for every $K$, and (0.31) reads
  $$\frac1{g^2}+\beta\,\ell\log L\;\leq\;\frac1{(g^{(K)}_\ell)^2}\;\leq\;\frac1{g^2}+\beta'\,\ell\log L .$$
  So the cutoff-$K$ and cutoff-$(K+1)$ theories have equal couplings at level $0$. At level $\ell\geq1$ their couplings lie in the same window but need not be equal.
- *Reading used.* The threshold "for a sufficiently small positive $g$" and the constants $\beta,\beta',\gamma$ are independent of $\varepsilon$, and a choice $g_0(L^{-K},g)$ is fixed for each $K$. Theorem 2's $g_k$ are the couplings of RG1's own small-field model; for the N4 model of §1.2 they are defined by the same extraction RG1 (0.20).
- Scope of the matching:
  - Theorem 2 is printed for $G=SU(2)$; V3 (H1) has $G$ compact, connected and simple.
  - Its proof was never published (LFR II p.355).
  - A repair for simple $G$ is proved in the Bałaban project (registry `RG1_Thm2_REP`; `ONE_LOOP_PROOFS.md` Lemma 2.1, Propositions 2.4 and 2.6, Theorem 8.1, Corollary 8.2), for RG1's model. Since the Lipschitz push it is imported, with uniqueness from D6 and the window form $|x^{(K)}_\ell-\bar x_\ell|\leq\delta\ell+C$, $\bar x_\ell=g^{-2}+\tfrac{11}{24\pi^2}\kappa_G\ell\ln L$ (Lipschitz note §2). The limits on its use are LIP-1 and LIP-2.

### 1.2 The compared objects

- **The model compared (fixed after r3).** It is the N4 model. Before each step the field is restricted by the common gauge-invariant condition $D_{\ell+1}$, a product of conjugation-invariant plaquette conditions, the same for both theories. Bałaban's analysis of this model is R-N4.
- **Both theories at a common level.** At level $\ell$ both theories have a density on gauge fields $V$ on $T^{(\ell)}$.
  - In the pure small-field situation ($\Omega_j=\Lambda_j=$ the whole torus for every $j$) there are no $\mathbf B$-terms. There are $\mathbf R$-terms: the $\mathbf R''$ of CRE p.279 and the terms of the $\mathbf R$-operation (N15).
  - The display below is RG1 (0.22) as printed for Bałaban's model. For the N4 model it is a lemma to be proved (R-N4), with the $\mathbf R$-terms added:
  $$\mathcal A^{(K)}_\ell(V)=-(g^{(K)}_\ell)^{-2}A^{\eta_K}\bigl(U^{(K)}_\ell(V)\bigr)+\mathbf E^{(K)}_\ell\bigl(U^{(K)}_\ell(V)\bigr),\qquad \eta_K=L^{-K}.$$
- **Why the comparison is made in $V$.** The two theories' backgrounds live on different lattices ($T^{(K)}$ and $T^{(K+1)}$), and their fluctuation integrals are gauge-fixed differently at every step. They are therefore compared only as functions of the common block field $V$.
- **Gauge invariance of the compared functions.** Both are gauge-invariant functions of $V$:
  - the localized $\mathbf E$-terms extend to gauge-invariant analytic functions (CRE p.259, property (iii));
  - $A^\eta$ is gauge invariant;
  - the background is defined up to the gauge orbit (RG1 p.256: "exactly one critical orbit"). The orbit is that of the gauge transformations $u$ on $T$ with $u=1$ on $T^{(k)}$ (RG1 p.256). So the residual freedom is trivial at the level-$\ell$ points.
  - *Transport covariance.* For fine paths $\gamma$ between level-$\ell$ points, $U_\ell(V^v)(\gamma)=v(\gamma_-)\,U_\ell(V)(\gamma)\,v(\gamma_+)^{-1}$. This does not follow from p.256 alone (r3). It needs:
    - (a) $M^k(U^{\tilde v})=M^k(U)^v$ for a fine extension $\tilde v$ of $v$: RG1 (0.6) for one step, and N12 for $k$ steps;
    - (b) invariance of the space of regular orbits under fine gauge transformations [REG/VAR];
    - (c) gauge invariance of $A^\eta$.
  - Given (a)–(c), $U\mapsto U^{\tilde v}$ maps the constraint set of $V$ onto that of $V^v$ and preserves the action. Uniqueness then gives $U_k(V^v)\in U_k(V)^{\tilde v}\cdot(\text{residual orbit})$, and the residual is $1$ at $\gamma_\pm$.
- **The loop.** $C$ is a square in $\mathbb T$ of side $s_C\in\mathbb N$ unit bonds, with corners in $T^{(0)}$. $C^{(K)}$ is its realisation on $T^{(K)}$, with $n=s_CL^K$ bonds per side.
- **The loop-carrying density.** $N^{(K)}_\ell(C;V)$ is the result of the same $K-\ell$ steps applied to $W_\chi(C^{(K)};U)\,\rho^{(K)}_{\rm b}(U)$. At the first step it is the small-field branch of V3's $N_1$ (eq:first-step). V3's $N_1$ is the full pushforward before the small-field/large-field decomposition, and V3 does not isolate this branch pointwise in $V$. (Corrected after r3: eq:outgoing-loop is $W_1=dN_1/d\rho_1$.)
- **The relative loop density** $\mathcal W^{(K)}_\ell(C;V):=N^{(K)}_\ell(C;V)/\rho^{(K)}_\ell(V)$ is the conditional expectation of the loop given the level-$\ell$ block field (a Radon–Nikodym derivative, with a version fixed). $|\mathcal W|\leq1$, since $|N|\leq\rho$.
  - It is gauge invariant in the N4 model. V3 lem:global-average (ii) gives $M(U^{\tilde v})=M(U)^v$, so the pushforward of an invariant measure under the blocking after a gauge-invariant cutoff is invariant. $W_\chi$ is a class function, and an invariant version of $dN/d\rho$ is obtained by averaging over the compact gauge group.
  - The covariance is RG1 (0.6) (not (0.4)); V3 L352 gives the designated-bond maps. For Bałaban's own branch, with cutoffs on gauge-fixed fluctuations, invariance would need the covariance of those cutoffs; this is one reason the N4 model is used.

### 1.3 Proposed target (small-field model, level 0)

Each theory uses its own normalisation, defined now, independently of R-S1 (repaired after r3):
$$\kappa^{(K)}(C):=\mathcal W^{(K)}_0(C;1),\qquad Z^{(K)}_\ell(C):=\frac{\mathcal W^{(K)}_\ell(C;1)}{\mathcal W^{(K)}_{\ell+1}(C;1)},\qquad\text{so}\quad\kappa^{(K)}(C)=\prod_{\ell=0}^{K-1}Z^{(K)}_\ell(C),$$
the relative loop density at the flat block field $V=1$. What must be proved is $\kappa^{(K)}(C)\neq0$.
- *In the class of §4.1* (a lemma once R-S1 holds), $T_b=1$ at $V=1$, the hat activities vanish and $\chi_\rho(1)=1$. So $\mathcal W^{(K)}_\ell(C;1)=\prod_{\ell'\geq\ell}Z^{(K)}_{\ell'}(C)$, with $Z_\ell$ the scalar gas of flat values, and
  $$\log Z^{(K)}_\ell(C)=-\delta m^{(K)}_\ell P_\ell(C)+\sum_{c}\log z^{(K)}_{\ell,c}+r^{(K)}_\ell(C),$$
  where $P_\ell(C)$ is the perimeter in level-$\ell$ lattice units.
  - $\delta m$ is the per-period connected Mayer sum (pressure) of the periodic scalar gas on straight segments, averaged over the four oriented sides. The $z_{\ell,c}$ are the four oriented corner factors, which need not be equal and depend on $s_CL^\ell$ mod the period.
  - $r^{(K)}_\ell(C)$ is the $V$-independent finite-size remainder from Mayer clusters touching two corners or wrapping the loop. The expected bound is $|r_\ell|\leq C\tau_\ell^2e^{-\kappa's_CL^\ell}$ (r2, b1 B3), which rests on the §4.1 activity bounds.
- *Comparison with V3.* At the first step the analogue of $Z_{K-1}$ is V3's torus ratio $\mathcal W^{\circ,\sigma}_T(C_n)=\kappa_{C_n}e^{E^\circ_{T,n}}$ (cor:main-factorisation), so V3's residual $E^\circ_{T,n}$ is included. V3's $\delta m^\sigma$, $z^\sigma$ are infinite-volume limits with V3's reference cutoff $\vartheta^\sigma$, and its split $(\delta m^\sigma,z^\sigma,E^\circ_{T,n})$ differs from $(\delta m,z,r)$. Only the products are compared; their equality is R-S1(d)(3). The proposal is that of V3 rem:next-step (2).
- *Meaning.* The renormalisation condition is that the renormalised loop equals $1$ at the flat unit-scale block field, in each theory. The content lies in the $V$-dependence. Only the product enters the target, so no agreement with an infinite-volume $\delta m$ is needed.

- **(T-act)** On the common level-0 domain $D_0=\{V:|V(\partial p)-1|<c\,\varepsilon_0\}$ (§0; modelled on the $V$-condition of RG1 p.259, which has a fixed $\varepsilon_0$; §4.4),
  $$\mathcal A^{(K+1)}_0(V)-\mathcal A^{(K)}_0(V)=c_K+\sum_X D_K(X;V),$$
  where:
  - $c_K$ is a constant;
  - the $D_K(X;\cdot)$ are gauge invariant and analytic on $D^{\mathbb C}_0$, with $|D_K(X;\cdot)|\leq\theta_K e^{-\kappa d_0(X)}$ there;
  - $\sum_K\theta_K<\infty$. Consecutive differences tending to $0$ would not give a Cauchy estimate (r3).
  - $D_K$ includes the classical difference at age $K$, $-g^{-2}\sum_Xa_0(X;V)$ (S3(i)), besides the regular-part and $\mathbf R$-term differences (r3).
- **(T-loop)** On the same domain, $\mathcal W^{(K)}_0(C;V)=\kappa^{(K)}(C)\,\widetilde{\mathcal W}^{(K)}_0(C;V)$ with
  $$\bigl|\widetilde{\mathcal W}^{(K+1)}_0(C;V)-\widetilde{\mathcal W}^{(K)}_0(C;V)\bigr|\leq\theta_K\,n_0(C)\,e^{C\tau_0^2n_0(C)},$$
  where $n_0(C)=4s_C$ is the number of unit bonds of $C$.
  - The absolute form replaces the earlier log form (N7). A log needs $|\chi|$ bounded below, which fails on $D_0$ for loops of area comparable to $\varepsilon_0^{-1}$. The absolute form is what the expectation needs (§4.6).
- **Weakest form (corrected after r3).** The consumer is the model expectation at level 0 (§4.6). It needs only:
  - $\sup_{D_0}|\mathcal A^{(K+1)}_0-\mathcal A^{(K)}_0-c_K|\leq\theta'_K$;
  - $\sup_{D_0}|\widetilde{\mathcal W}^{(K+1)}_0-\widetilde{\mathcal W}^{(K)}_0|\leq\theta''_K$;
  - $\sum_K(\theta'_K+\theta''_K)<\infty$ and $\kappa^{(K)}(C)\neq0$;
  - the level-0 integral restricted to $D_0$ in the model's definition.

  Then, for a fixed $K_0$ and all $K\geq K_0$, telescoping gives $|\widetilde{\mathcal W}^{(K)}_0|\leq|\kappa^{(K_0)}|^{-1}+\sum_{k\geq K_0}\theta''_k$ on $D_0$, uniformly in $K$. This uses $|\mathcal W^{(K_0)}_0|\leq1$. From the polymer form (T-loop), $\theta''_k=\theta_kn_0e^{C\tau_0^2n_0}$. Analyticity on $D^{\mathbb C}_0$, gauge invariance and the polymer form are not needed at level 0. They are lemmas of the induction (§4.5), as are the versions at levels $\ell\geq1$.
- **Expected rate (corrected after r3).**
  - The $\mathbf E$-part and the loop give $C(\log K)^{O(1)}\lambda_*^K$, with $\max(\lambda',\lambda_Y,\mu_{\rm line})<\lambda_*<1$ and $\max(L^{-\beta_E},\mu)<\lambda'<1$ (§4.5). That alone would be a power of the lattice spacing.
  - The $\mathbf R$-terms (N15) do not age in the printed bounds, and they feed later $\mathbf E$- and $\mathbf R$-terms without age decay.
  - *Corrected in the Lipschitz push.* The system (E), (R), (C) with D9 gives $\theta_K\leq C(\log K)^{O(1)}(K+1)^{1-p}$, with $p=3$ for $\kappa_0\geq7$ (CRE p.263). This is polynomial in $K=\log_L\varepsilon^{-1}$ and summable. The earlier $(\log K)^{O(1)}K^{-\kappa_0/2}$ omitted the R-feedback. A power of the spacing would need a proof that $\mathbf R$-terms age.
  - *The corner products.* Each theory divides by its own $\kappa^{(K)}$, so the corner products never enter a difference. Under the route's bounds $|\log z_\ell|\leq C\tau_\ell^2$ they are $\exp(O((\log K)^{6p_0+1}))$, not a power of $K$ (r3).
  - *For comparison.* V3 conj:iteration has error $(k+2)\tau^2\asymp(\log K)^{6p_0}$ for $k\sim K$.
- **What is not claimed.** (T-act) and (T-loop) concern the N4 model. A physical Cauchy statement, with a normaliser that includes the large-field perimeter part (N14), needs LF. It also needs the integration over $V$ at level 0 on the fixed torus $\mathbb T$, where a bounded volume factor $L^{4M_T}$ is allowed.

## 2. Gauge invariance as the mechanism

Gauge invariance is essential but not sufficient (corrected after r3).
- **What it does.**
  - It makes the comparison meaningful (G1).
  - It excludes non-invariant counterterms (G3).
  - It kills the zeroth and first orders at flat configurations (G4).
  - It lets the axial gauge express the field through the curvature (G2).
- **What the aging also needs.**
  - Analyticity on the complex domain of radius $\alpha_{0,j}$ (CRE p.259 (ii), (2.28)), which turns vanishing order into size.
  - Localisation with weights $e^{-\kappa d_j(X)}$. CRE p.284 says the proof "works only if we have the representation (2.26), (2.27)".
  - In the bulk, the removal of the marginal $\mathrm{tr}F^2$ part by $\beta_jA$, through Euclidean covariance, (3.64) and (3.66). Without it there is no gain (G2).
- **The line.** Gauge covariance, analyticity and one-dimensional counting suffice once $Z_\ell(C)$ is extracted. The route relies on this.
- **The classical part** ages by S3's $\mu$, an exogenous input, not by gauge invariance.

- **(G1) Comparability (corrected after r3).** Different theories, and different steps of one theory, use different backgrounds and different gauge fixings.
  - Quantities defined through each theory's gauge-fixed variables have no common meaning across theories. Bałaban's gauge-fixed integrals reproduce the true conditional expectations only for gauge-invariant integrands. So only gauge-invariant functions of $V$ are compared.
  - Gauge-dependent observables are not thereby excluded from a Cauchy property. On the compact lattice $\mathbb E[F]=\mathbb E[\bar F]$, with $\bar F$ the Haar gauge average. For example $F=\chi(U(\gamma))$, with $\gamma$ open and $\chi$ nontrivial irreducible, has $\bar F=0$. The Cauchy question is a question about gauge-invariant observables, and the Wilson loop is the route's target, not a consequence of (G1).
  - The objects entering §4 are gauge-invariant functions of $V$, or covariant ones with a common transformation law at level-$\ell$ points:
    - $\Delta_b$ (§4.3 (iii-b));
    - the activities $\mathbf X_Y$ (§4.1);
    - $T_b-T'_b$ (§4.2).

    That Bałaban's gauge-fixed integrals give this covariance is N11, which is open.
- **(G2) Flat-vanishing gives curvature bounds, by the axial gauge.** Bałaban's second proof of CRE Theorem 2 (pp.283–284) uses "directly the gauge invariance" instead of the Ward–Takahashi identities (CRE p.283).
  - On the cube $\square_0=\square^{\sim n-j+1}$ he puts the field $M^j(U_k)$ in an axial gauge centred at $z$. The resulting $V'$ satisfies the first line of (3.68), in Bałaban's indices ($j<n$, age $n-j$):
    $$|V'-1|<11d^2\varepsilon_n(L^jL^{-n})^2+dM(n-j+2)\,\varepsilon_n(L^jL^{-n})^2 .$$
    The second line of (3.68), $3dM(1+\log L^jL^{-n})\varepsilon_n(L^jL^{-n})^2$, has $\log L^jL^{-n}<0$ as printed. The first line shows that it is to be read as $1+(n-j)\log L$, linear in the age. Only the first line is used.
  - Here $n$ is the level with $z\in\Omega_n\setminus\Omega_{n+1}$. It is the current step, so that $n-j$ is the age, only in the pure small-field model (§3(a)).
  - A Taylor expansion to third order in $B'$ (3.69)–(3.70), and contour variables written as $(\partial B)(\Sigma)$ over a minimal surface $\Sigma$ (3.72), reduce $\mathbf E^{(j)}(\Lambda_j,U_k,z)-\mathbf E^{(j)}(\Lambda_j,1,z)$, for domains $X\subset\square^{\sim n-j}$, to a quadratic form in the curvature plus $O((L^jL^{-n})^5)$. Precisions (r3):
    - the curvature is that of the level-$n$ field on $\square_1\in\pi_n$ (p.284);
    - the far-domain class is bounded separately (p.283);
    - the first-order term of (3.69) vanishes by the analogue of RG1 (4.14) (G4);
    - the outcome is "the representation (3.70), but with the first term on the right-hand side replaced by the expression (3.57)", and "the remaining arguments are as in the first proof" (CRE p.284), i.e. (3.57)–(3.64).
  - **What it gives, per point of the current lattice (corrected after r3).**
    - The quadratic form is $O((L^{j-n})^4)$ per level-$j$ point, and there are $L^{4(n-j)}$ level-$j$ points per level-$n$ point. So before subtraction the result is $O(1)$ per level-$n$ point: marginal, with no gain.
    - After the marginal $\mathrm{tr}F^2$ part is removed by $\beta_jA$ ((3.64), (3.66)), the remainder is $O((L^{j-n})^{5-\beta})$ per level-$j$ point, giving $(L^{j-n})^{1-\beta}$ per level-$n$ point ((2.43), (3.67)).
    - For line insertions, one-dimensional counting gives $L^{-(a-1)(n-j)}$ per coarse bond with no subtraction.
  - So the bulk marginal sector lives in R-S3's zero-$F^2$ part and in (P-$\beta$).
- **(G3) No non-invariant counterterms (corrected after r3).** The renormalised constants are:
  - the vacuum energy (CRE p.279);
  - $\beta_j A$, the coupling, which is marginal (CRE (2.24)–(2.25), printed on p.259 and used on p.279);
  - $\delta m$, the perimeter coefficient;
  - the four oriented corner factors $z_{\ell,c}$;
  - the non-local scalar remainders $r_\ell(C)$ (§1.3) and, at the first step, V3's $E^\circ_{T,n}$.

  Write $B$ for the gauge potential ($A$ is Bałaban's action).
  - There is no bulk $\mathrm{tr}B^2$: simple $G$ has no $\mathfrak u(1)$ factor.
  - There is no renormalisation of the transport's coupling to $B$, by the two-sided covariance (§4.1).
  - Matrix activities linear in $B'$ at leading order do exist (§3(e), (f)). They are irrelevant, with $\alpha_{\rm line}=1$.

  *Completeness by power counting.* The bulk gauge-invariant local terms of dimension $\leq4$ are $1$, $\mathrm{tr}F^2$ and $\mathrm{tr}F\tilde F$. The last is excluded by reflection covariance only, not by gauge invariance [to check: whether CRE (2.29) includes reflections]. On the line only the identity is relevant ($\delta m$), and corners carry the dimension-0 factors $z_{\ell,c}$.
- **(G4) Flat values of insertions.** Two facts follow from invariance.
  - An insertion with values in $\mathfrak g_{\mathbb C}$ that is gauge covariant (transforming by $\mathrm{Ad}$ at its base point) takes at $V=1$ a value fixed by every $\mathrm{Ad}_u$, $u\in G$. That value lies in the centre of $\mathfrak g_{\mathbb C}$, which is $0$ for simple $G$. So such insertions vanish on the gauge orbit of $V=1$ with no subtraction. [E]
    - *Scope (r3).* This does not apply to $\mathrm{End}(V_\rho)$-valued activities. For $G_2$ and $\rho=\mathbf 7$, $\mathbf7\otimes\mathbf7=\mathbf1\oplus\mathbf7\oplus\mathbf{14}\oplus\mathbf{27}$ contains the adjoint once, so matrix activities have a nonzero linear term ($a=2$). Their flat values are scalars (Schur), and their vanishing comes from the extraction of §4.1.
  - The linear term at $V=1$ of a gauge-invariant scalar insertion is, by the same argument, an element of $\bigoplus_b\mathfrak g_{\mathbb C}^*$ with each component $\mathrm{Ad}$-invariant, hence $0$. So scalar insertions start at second order once their constant is extracted. [E] This is printed: RG1 (4.13)–(4.14), p.284, "The group $G$ is semisimple".
  - "Flat" means gauge equivalent to $1$ on the locality domain of the insertion. Flat configurations with nontrivial torus holonomy are not covered; $D_\ell$ contains flat connections with arbitrary commuting holonomies. Domains that wrap the torus give exponentially small non-vanishing pieces, handled like the far-domain term of CRE p.283. This needs $d_j(X)\geq c\cdot$(torus period in level-$j$ units) for wrapping $X$, with the period used only as a lower bound [to check: the definition of $d_j$].

  *Extracted constants (corrected after r3).* They are $\delta m$ on straight segments and the four oriented $z_{\ell,c}$ at corners.
  - Bałaban's localisation uses the cube partitions $\pi_j$ (CRE pp.279, 283). p.259 names $\mathbf D_j$ and the $MR_j$-cubes.
  - The flat values are periodic along a segment with the partition period, if two things hold:
    - every step is covariant under partition-preserving translations [to check: CRE (2.5), (2.29)];
    - the torus periods are divisible by the partition period. This is a permitted restriction on the periods.
  - $\delta m$ is the per-period connected Mayer sum (pressure) of that periodic scalar gas (§1.3), not the average of the flat values.
  - Partial periods go into the corner factors, which therefore depend on $s_CL^\ell$ mod the period.

## 3. Count check (size × count × weight per level)

Ages are counted from the top: a quantity created at level $j$ and seen at level $\ell<j$ has age $j-\ell$. $p_0(g)=A_0(\log g^{-2})^{p_0}$ and $\varepsilon_j=g_jp_0(g_j)$ (CRE (2.4), p.255).

- **(a) Bulk, top source.**
  - Size: the regular part created by the first step of the cutoff-$(K+1)$ theory, of order $E_0$ per localization domain (CRE p.259, property (iv), the bound (I.1.18)). The cutoff-$K$ theory has no such term.
  - Weight: CRE Theorem 2 (2.43), p.263. With no large fields, (2.2) gives $\Gamma_k=\Omega_k^{(k)}=T^{(k)}$ and $\Gamma_n=\emptyset$ for $n<k$, so the irrelevant part of the step-$j$ term is at most $E_1(L^{j-k})^\beta$ per point of the current lattice, for any $\beta<1$, with $E_1=E_1(\beta)$.
  - For the top term ($j=1$, $k=K+1-\ell$) this is $E_1L^{-\beta(K-\ell)}$ per point of $T^{(\ell)}$, and $E_1L^{-\beta K}$ per unit point at level 0. The marginal part $\beta_1A$ is in the coupling.
  - Count: $L^{4M}$ unit points (fixed torus). Small.
- **(b) Bulk, propagated differences.**
  - The step at age $m$ of the cutoff-$(K+1)$ theory has inputs that differ from those of the cutoff-$K$ theory at the same level.
  - *Bookkeeping by creation level (r2 repair).* (2.43) is not a per-level contraction: its constant $E_1(\beta_E)$ is not 1, and $E_1\to\infty$ as $\beta_E\to1$. It bounds each creation level separately. So let $n_{m'}$ be the per-point size of the difference of the terms *created* at age $m'$. The transported difference of those terms at age $m$ is at most $E_1'L^{-\beta_E(m-m')}n_{m'}$, by (2.43) applied to differences (§4.5), with $E_1'$ the constant of (2.43) per unit creation size.
  - *New terms.* The new terms see a regular-part difference only through the fluctuation variation, with a factor $\omega(g)$ (the analyticity margin). They see the classical and background differences with an $O(1)$ factor, but these are sources that nothing feeds back into (§4.4).
  - *Result.* Hence $n_m\leq C\omega E_1'\sum_{m'<m}L^{-\beta_E(m-1-m')}n_{m'}+C(s_m+\omega_g\delta^g)$. This closes with rate $\lambda'$ once $\lambda'>L^{-\beta_E}$ and $C\omega E_1'/(\lambda'-L^{-\beta_E})\leq\tfrac12$, given (P-N) of §4.4 (weak point W1). The smallness comes from $\omega(g)$, not from $L^{-\beta_E}$. The first draft had $\lambda=L^{-\beta}+C\,\mathrm{Lip}$ with one unweighted Lipschitz constant, which is $O(1)$ (r1 review, C2).
- **(c) Classical part.**
  - Size per point of $T^{(\ell)}$: $g_\ell^{-2}\varepsilon_\ell^2=p_0(g_\ell)^2$ on the small-field domain (sup bound).
  - Weight: the relative difference $c_{\rm cl}(K-\ell)$ of the blocked classical actions built from the two finest lattices (R-S3).
    - The axial-gauge mechanism with Bałaban's printed remainders gives $c_{\rm cl}(m)\leq C\mu^m$ with $\mu=L^{-(1-\beta)}$ for any $\beta>0$, with $\beta$ independent of $\beta_E$ (corrected after r3). The count is $O((L^jL^{-n})^{5-\beta})$ per level-$j$ point ((3.67), (3.70)) times $L^{4m}$ points.
    - The earlier $L^{-2m}$ is the dimension-6 count of tree-level artefacts and is not delivered by that mechanism. The route needs only $\mu<1$ (W2).
  - The classical difference is an exogenous source supplied by S3 at every level. It is not a Bałaban $\mathbf E$-term and does not age by (2.43) (r2, M1; §4.4).
  - Not small at young levels ($m\lesssim\log_Lp_0^2$), so the difference at the top is $d_0\lesssim p_0(g^{(K)}_K)^2+E_0$, polylogarithmic in $K$. Since $(g^{(K)}_K)^{-2}\leq g^{-2}+\beta'K\log L$, this is $p_0^2\leq C(\log K)^{2p_0}$.
- **(d) Coupling.**
  - Matching at level 0 and RG1 (0.20) give $\Delta(g_\ell^{-2})=\sum_{\ell'=1}^{\ell}\Delta\beta_{\ell'}$.
  - $\beta_j=\tfrac12\partial^2_{p_1}\Pi^{(j)}_{22}(0)$ is a coefficient of the step output (CRE (3.64), p.283), and it is linear in the function.
  - $|\Delta\beta_{\ell'}|$ must be bounded through the Gaussian representation of $\Pi^{(j)}$: by the covariance difference $O(c_{\rm cl}(K-\ell'))$ plus $\omega(g)$ times the regular-part difference ((P-$\beta$), §4.4).
  - A field-space Cauchy estimate would give only $\varepsilon^{-2}$ times the per-point difference. At the top that is a relative $O(1)$, not $O(1/K)$ (r1 review, C3).
  - Given (P-$\beta$), $|\Delta(g_\ell^{-2})|\lesssim\sum_{\ell'\leq\ell}\lambda'^{K-\ell'}\leq C\lambda'^{K-\ell}$. The two-sided structure (matching at level 0) is handled in §4.5.
  - At the top this is $O(1)$ against $g^{-2}\sim K$: a relative $O(1/K)$ difference. It enters as an input difference, not as a source of growth.
  - This needs (P-$\beta$) at all ages. With (P-$\beta$) only for $m\geq m_*$, the young ages give $|\Delta\beta|\leq2\sup|\beta_j|$ each, so $\delta^g_K=O(1+m_*)=O(\log\log K)$. That is harmless, because young-level coupling differences affect only young levels, which use the trivial bound. To recover $O(1)$, prove (P-$\beta$) for $m<m_*$ too. It does not need the room claim (r2, m1).
- **(e) Loop, top sources.**
  - *Size of the fluctuation dressing (corrected after r2, S1).*
    - V3's $E^\circ_\xi$ is already post-extraction ($\kappa_{C_n}$ is pulled out in thm:main-theorem (i)).
    - In the pure small-field model the large-field complement is empty, so cor:main-factorisation gives $E^\partial_\xi=0$ and $E^\circ_\xi=E^\circ_{T,n}$. That is a history-independent constant, the flat-value residual. It is not flat-vanishing, and it is carried in $Z_\ell(C)$ (§1.3).
    - V3 controls the $V$-dependent first-step correction only through the second term of $E_{\rm def}$, $e^{C_\chi n_C\rho(\varepsilon_1+e^{-cb/(LM)})}-1$. That is a global bound, not small at the top.
    - The per-bond size $\rho\varepsilon_1\leq C\tau^2\varepsilon_1$ is an indicator of the order, not a theorem. The local per-bond form is unproved (V3 rem:next-step (3)(a)). It is the base case of R-S1 (sub-item (d)).
  - *The classical line source (omitted before r2, M2).* At age 0 it compares $\chi(\prod_bU_1(V)(\gamma_b))$ with $\chi(\prod_bV(b))$. Per bond it is an $\mathrm{Ad}$-covariant, flat-vanishing transport defect of size $O(\varepsilon_K)$, larger than $\tau^2$. It is the dominant line source and needs R-S3(iii-b).
  - Weight: $L^{-\alpha_{\rm line}(K-\ell)}$ per level-$\ell$ bond (R-S2).
    - For an $\mathrm{Ad}$-covariant insertion, the axial-gauge bound (3.68) gives $(L^{-m})^2\varepsilon$ per fine bond at age $m$, times a factor linear in $m$ (the first line of (3.68)). The Cauchy normalisation adds $\varepsilon_n/\varepsilon_j\lesssim(1+\beta_0)(j-n)^{1/2}$ up to polylogarithmic factors, by (2.6). There are $L^m$ fine bonds per coarse bond, so $\alpha_{\rm line}=1$. The polynomial factors in $m$ are absorbed by any rate $\lambda_Y>L^{-1}$ (§4.2).
    - Scalar insertions start at second order ((G4)), so $\alpha_{\rm line}\geq3$ for them.
  - Count: $n_\ell=4s_CL^\ell$ bonds at level $\ell$. At level 0: about $4s_C(\varepsilon_K+C\tau^2)L^{-K}\,\mathrm{poly}(K)$. Small, given R-S1, R-S2 and R-S3(iii-b).
- **(f) Corners.**
  - Four per level. Their constants are divided out exactly by each theory's own $Z^{(K)}_\ell(C)$.
  - The corner clusters form a summable two-parameter family $c_{(a,b)}$ (lengths $a,b$ on the two sides), with $|c_{(a,b)}|\leq C\tau^2e^{-\kappa(a+b)}$; there are not finitely many.
  - The flat-vanishing remainder of a corner cluster created at level $j$ has size $C\tau_j^2$ and, at level $\ell<j$, weight $L^{-2(j-\ell)}$. It is a matrix-valued activity linear in the curvature at a point, with no multiplicity ($a=2$ in S2). Summable over $j$. (The index is $j-\ell$, not $K-\ell$: r2, m2.)
- **(g) Large fields (outside the route, for orientation).**
  - A large field in a cube at level $\ell$ costs at most $e^{-c(\log g_\ell^{-2})^{2p_0}}$ (V3 rem:main-regime (1), $\pi_*^2\geq A_0^22^{-2p_0}(\log g_0^{-2})^{2p_0}$).
  - The torus has $L^{4\ell+4M}$ such cubes, and the window (0.31) makes $(\log g_\ell^{-2})^{2p_0}$ only polylogarithmic in $\ell$. So $\sum_\ell L^{4\ell}e^{-c(\log g_\ell^{-2})^{2p_0}}$ diverges.
  - That alone shows only that the union bound cannot exclude large fields: an upper bound on the cost gives no lower bound on the frequency (r2, S2).
  - *Lower bound (elementary; to be checked against CRE's exact large-field condition).*
    - At the finest level the bare Wilson measure is a Markov field, so links with disjoint plaquette neighbourhoods are conditionally independent given the rest.
    - For one link the conditional law is $\propto\exp(g^{-2}\mathrm{Re\,tr}(US))$, with $S$ the sum of the six staples. A one-variable estimate gives conditional probability at least $c\,e^{-Cg^{-2}\varepsilon^2}=c\,e^{-Cp_0^2}$ that an adjacent plaquette violates $|U(\partial p)-1|<\varepsilon$.
    - With at least $cL^{4(K+M)}$ such links, $P(\text{no large field})\leq(1-ce^{-C(\log K)^{2p_0}})^{cL^{4(K+M)}}\to0$.
  - *Reading.* The number of large-field cubes per unit physical volume tends to infinity, while their fraction tends to 0, in the bulk and along the loop ($L^\ell$ cubes per unit length).
  - The pure small-field class is therefore atypical. The large-field effects along straight segments must be shown to be perimeter-local. Since their contribution per unit length, about $L^\ell e^{-c(\log g_\ell^{-2})^{2p_0}}$, diverges, they enter the perimeter counterterm (N14). Corners cost $\sum_\ell e^{-c(\log g_\ell^{-2})^{2p_0}}<\infty$.

**Conclusion (corrected after r3).** In the small-field model, the quantities that do not age are:
- those removed by renormalisation: the vacuum energy, $\beta_jA$, and the scalar gas $Z_\ell(C)$ ($\delta m$, the corner factors and the residual $r_\ell$);
- from the printed bounds, the $\mathbf R$-terms (N15): (2.44) gives them no age factor.

Every other difference carries an age factor, given the conditions below. Then the $\mathbf E$-part and the loop give $C(\log K)^{O(1)}\lambda_*^K$, and the $\mathbf R$-terms, with their feedback into later terms (D9), give $C(\log K)^{O(1)}(K+1)^{1-p}$ with $p=3$. So $\theta_K\leq C(\log K)^{O(1)}(K+1)^{-2}$ (§1.3, §4.5; corrected in the Lipschitz push).
- Conditions (complete list after r3):
  - S0 (the coupling matching; $SU(2)$ only, W5);
  - Bałaban's bounds in the N4 model, with the common cutoff $D_{\ell+1}$ (R-N4);
  - R-S1 with its base case, sub-item (d), and N11;
  - R-S2;
  - R-S3, including S3(iii-a) in family form and S3(iii-b) for the loop;
  - the system (E), (R), (C) with D9 and (P-Y), with the room claim in variation form (Lemma G) and LIP-1, LIP-2, LIP-3 (Lipschitz note);
  - N6 (the frozen parameters from the reference flow, with Lemma T; $R_\ell$ open) (§4.4);
  - R-S5's own items: the analytic polymer form of (2.43), the homogeneity constant $E_1'$, and the creation-level identity under merging (§4.5);
  - the source bookkeeping of S3 at the young levels ($m_*$, §4.4).
- The polylogarithmic factor comes from the young levels $m<m_*$, where only the trivial bound is used. Indeed $m_*\leq1+\log_{1/\mu}(4CC_{\rm cl}p_0^2/\rho)$, so $\lambda'^{-m_*}\leq C(\log K)^{2p_0\log(1/\lambda')/\log(1/\mu)}$, an exponent below $2p_0$ because $\lambda'>\mu$.

## 4. Steps

### 4.0 S0: coupling matching [B]

RG1 Theorem 2, p.259 (§1.1). Scope: W5.

### 4.1 S1: the dressed-loop class [OPEN R-S1]

Revised after the r2 review `cr-b1-s1-20261021-r2` (§7). The first version, a single-bond class $\chi(\prod_be^{iX_b}U_\ell(V)(\gamma_b))\exp(\sum_bf_b+\sum_ch_c)$ with fixed-range insertions, is not closed under a step.

- **Why clusters.** At second order the fluctuation integral of $\chi(\mathrm{hol})$ produces terms $\chi(\cdots T^a\,U(\gamma)\,T^c\cdots)\,C_{ac}(b,b')$. These are two Lie-algebra insertions at different bonds $b,b'$ inside one trace, joined by the covariance.
  - The tensor $\sum C_{ac}T^a\otimes T^c$ is not a product tensor, so no product of single-bond factors expresses it. Even in the abelian case the pair terms are not single-bond at fixed range.
  - *Nearby pairs.* At $V=1$, $C_{ac}(b,b')$ is an $\mathrm{Ad}$-invariant form, hence a multiple of the Killing form for simple $G$, and $\sum_aT^aT^a$ is the Casimir, a scalar. It goes to $\delta m$ on segments and to $z$ at corners; the rest is flat-vanishing.
  - *Distant pairs.* They are suppressed by the decay of the covariance in Euclidean distance. For the square, the shorter arc is at most twice the chord (worst case: midpoints of opposite sides); near a corner the factor is $\sqrt2$.
- **The class $\mathfrak L_\ell$.**
  - Fix an irreducible representation $\rho$ of $G$ with character $\chi$ (V3 (H1)); reducible characters are treated by linearity. $\chi_\rho$ is the normalised trace on $\mathrm{End}(V_\rho)$, and $T_b=\rho(U_\ell(V)(\gamma_b))$, with $\gamma_b$ the fine path of $C^{(K)}$ under the level-$\ell$ bond $b$.
  - The class consists of the functions
    $$\mathcal W(C;V)=\sum_{\{Y_1,\dots,Y_r\}}\chi_\rho\Bigl(\prod_{\text{along }C}\bigl[\,T_{\rm gaps}\cdots\mathbf X_{Y_i}(V)\cdots\bigr]\Bigr).$$
  - The sum is over families of disjoint clusters $Y_i$, each a set of consecutive level-$\ell$ bonds of $C$. The whole loop $C_\ell$ is allowed as a cluster, with its base point at a fixed corner.
  - On each $Y_i$ the background transport is replaced by the activity $\mathbf X_{Y_i}(V)\in\mathrm{End}(V_\rho)$; on the gaps the transports $T_b$ stand.
- **Properties of the activities.**
  - *Covariance.* $\mathbf X_Y\mapsto\rho(u(y_-))\,\mathbf X_Y\,\rho(u(y_+))^{-1}$, with $y_\pm$ the end points of $Y$. The ordered product telescopes to a conjugation at the base point, so $\mathcal W$ is gauge invariant, given the transport covariance of §1.2.
  - *Localisation sums (repaired).* $\mathbf X_Y=\sum_Z\mathbf X_{Y,Z}$, with $\mathbf X_{Y,Z}$ depending on $V|_Z$ only, analytic on $D^{\mathbb C}_\ell$, and $\|\mathbf X_{Y,Z}\|\leq C\tau_\ell^2e^{-\kappa|Y|-\kappa d_\ell(Z)}$ there. This is the line analogue of CRE (2.26)–(2.27) with property (i), p.259, and the weight $e^{-\kappa d_j(X)}$ as used on p.283.
  - *Why not fixed range.* The step output depends on $V$ through the background, which solves a global variational problem, and through the fluctuation covariance, which decays exponentially but does not have finite range.
  - *Complexified gaps.* On $D^{\mathbb C}_\ell$ the gap transports are not unitary: $\|\prod_{\rm gap}T_b\|\leq e^{c\alpha|\text{gap}|}$, with $\alpha$ the per-bond complex radius. This enters the decay condition below.
- **Flat values and extraction.**
  - At $V=1$ constant gauge transformations fix the configuration, so $\mathbf X_Y(1)$ commutes with $\rho(G)$. By Schur's lemma it is a scalar $c_Y$, for any compact $G$ and irreducible $\rho$. Simplicity is used only in (G4) and in the uniqueness of the invariant form above.
  - On segments the $c_Y$ are periodic with the partition period, given translation covariance and divisible periods (§2, end of (G4)). At corners they form a summable family $c_{(a,b)}$ (§3(f)).
  - *Extraction.* Write $\mathbf X_Y=c_YT_Y+\widehat{\mathbf X}_Y$ with $T_Y=\rho(U(\gamma_Y))$. Then $\mathcal W=\sum_F\chi_\rho(\cdots\widehat{\mathbf X}_F\cdots)\,Z(C_\ell\setminus\cup F)$, with $Z$ the scalar gas, and
    $$\frac{Z(C_\ell\setminus\cup F)}{Z(C_\ell)}=\exp\Bigl(-\sum_{\mathcal K\cap\cup F\neq\emptyset}\phi^T(\mathcal K)\Bigr),$$
    which converges because $|c_Y|\leq C\tau^2e^{-\kappa|Y|}$.
  - A Mayer cluster meeting two hat clusters spans the gap between them, so re-expansion merges them into one consecutive cluster. Every resulting activity contains a hat factor, so it vanishes to first order on the gauge orbit of $V=1$.
  - Hence $\mathcal W=Z_\ell(C)\,\widehat{\mathcal W}$, with $Z_\ell(C)$ as in §1.3 and $\widehat{\mathcal W}$ in the *hat class* $\widehat{\mathfrak L}_\ell$, whose activities are flat-vanishing (renormalised and merged, not literally $\widehat{\mathbf X}_Y$).
  - S2 applies to hat activities in its cluster form (§4.2).
- **The single-bond class** is the case $|Y|=1$ with $\mathbf X_b:=e^{f_b+\mathbf 1[b_-=c]h_c}\rho(e^{iX_b}U(\gamma_b))-T_b$.
- **To prove (R-S1): exact closure within the N4 model.**
  - *Statement.* In the model with the common gauge-invariant cutoff $D_{\ell+1}$ before each step (§6, W4/N4): given a level-$(\ell+1)$ density in Bałaban's small-field class and $\widehat{\mathcal W}\in\widehat{\mathfrak L}_{\ell+1}$, the relative loop density at level $\ell$ equals $Z_\ell(C)\widehat{\mathcal W}'$ with $\widehat{\mathcal W}'\in\widehat{\mathfrak L}_\ell$.
  - *Truncation terms, named and assigned to LF:*
    - (t1) the difference between Bałaban's gauge-fixed fluctuation cutoffs and $D_{\ell+1}$;
    - (t2) the large-field complement at each step.
- **What the closure needs (sub-items of R-S1).**
  - (a) *Covariance.* Bałaban's integral is gauge fixed, and V3 lem:two-block already shows a two-point covariance at a non-endpoint. So the activities must be built only from background-covariant propagators, or a matrix-valued analogue of CRE p.259 (iii) must be proved.
  - (b) *Gap transports.* Under a level-$\ell$ bond the level-$(\ell+1)$ background transports must multiply to $T_b$: $U_{\ell+1}(\mathrm{bg}_{\ell+1}(V))=U_\ell(V)$, from the semigroup property $M^{a+b}=M^a\circ M^b$ (N12). Otherwise their difference must be written as flat-vanishing localised activities.
  - (c) *Decay.* Joining activities on $Y_1,Y_2$ by $C(b,b')$ gives a bound $\|\mathbf X_{Y_1}\|\|\mathbf X_{Y_2}\|e^{c\alpha|\text{gap}|}e^{-\delta d(b,b')}$.
    - With the chord–arc bound this decays like $e^{-\min(\kappa,\delta/2-c\alpha)|Y|}$, less a combinatorial loss $e^{c'|Y|}$.
    - Reblocking recovers the loss: a level-$(\ell+1)$ arc of $m\geq2$ bonds is covered by $\lceil m/L\rceil+1\leq m$ level-$\ell$ bonds.
    - So a covariance decay rate $\delta$ with $\kappa<\delta/2-c\alpha$ is needed, from Bałaban's propagator bounds (PRT).
  - (d) *Base case.* V3's first step is the case $\ell+1=K$ with the Wilson action and no activities. Its results (thm:main-theorem, cor:main-factorisation, lem:c4-4-3, eq:c4-4-10, eq:c4-12-2) are identities of expectations, not statements pointwise in $V$ (V3 rem:main-regime (3)). The base case needs:
    1. a pointwise-in-$V$ representation of $W_1=dN_1/d\rho_1$;
    2. a decomposition of the signed defect $E_{\rm def}$ (eq:c4-1-1) into ordered, covariant, localised cluster activities bounded by $C\tau^2e^{-\kappa|Y|}$, including a check that its $e^{-cb/(LM)}$ part vanishes at $V=1$;
    3. the matching of V3's $\delta m^\sigma$, $z^\sigma$ under Bałaban's gauge-fixed cutoffs with the scalars of the N4 model.
  - (e) *General-step density.* CRE Section 3 (p.279: "This ends the inductive proof of this representation"). CRE leaves the general-step operations undefined (pp.254–255; V3 rem:next-step (3)(b)), so this input alone is unlikely to suffice.
- **Corrected diagnosis (r2).**
  - V3's $E^\circ_\xi$ is a function of the history through the carrier alone. In the pure small-field model it is the constant $E^\circ_{T,n}$ (§3(e)).
  - So the open first-step question is not "the locality of $E^\circ$". It is the pointwise cluster decomposition of $dN_1/d\rho_1$, sub-item (d).
  - V3 rem:next-step (3)(a) asks for a coarse loop times the exponential of a fixed-range sum. That is the single-bond type, which is not closed.

### 4.2 S2: age decay of insertions [OPEN R-S2]

Revised after the r2 review `cr-b2-s2s3-20261021-r2` (§7). Route indices throughout: levels $n<j$, age $j-n$.

- **Statement to prove.**
  - Let $\mathbf Y$ be a hat activity of S1 created at level $j$. It is a cluster on consecutive level-$j$ bonds, with base point $y_-$ and the two-sided covariance of §4.1, localised on $Z$, analytic on $D^{\mathbb C}_j$, with supremum at most $C\tau_j^2e^{-\kappa|Y|-\kappa d_j(Z)}$. It vanishes to order $a/2$ on the gauge orbit of $V=1$: $a=2$ for matrix activities, by the extraction of §4.1 (not by (G4), whose first bullet does not apply to $\mathrm{End}(V_\rho)$; r3), and $a=4$ for scalar ones ((G4), second bullet).
  - Evaluated on a background regular at a coarser level $n<j$ ($V\in D^{\mathbb C}_n$, with the axial variables complexified), it satisfies
    $$\|\mathbf Y\|\leq C\tau_j^2\Bigl(\frac{(R_j+|Y|+(j-n))\,\varepsilon_n}{\varepsilon_j}\Bigr)^{a/2}(L^{n-j})^{a}\,e^{-\kappa|Y|}e^{-\kappa d_j(Z)} .$$
  - *Count.* The clusters starting at a given level-$j$ bond sum to the same bound with a new constant. With $L^{j-n}$ level-$j$ bonds per level-$n$ bond this gives $L^{-(a-1)(j-n)}$ per level-$n$ bond: $\alpha_{\rm line}=1$ for $a=2$ and $3$ for $a=4$. The polynomial prefactors in $j-n$ are absorbed by any rate $\lambda_Y>L^{-1}$.
  - *Weakest form.* The consumer, (P-Y) of §4.4 with the creation-level bookkeeping of §4.5, needs only this. An activity created at level $j$ has, at level $n$, per-bond norm at most $C\lambda_Y^{\,j-n}$ times its creation size, for some $\lambda_Y<1$. A one-step version with factor $CL^{-1}<1$ (with $R$ replaced by the support in current-level units) also gives it.
- **Mechanism, in route indices.**
  - A background regular at level $n$ has curvature $\lesssim\varepsilon_nL^{2(n-j)}$ per level-$j$ plaquette.
  - In a complete axial gauge on a union of $\pi_j$-cubes, centred at $y_-$, the axial field on level-$j$ bonds within distance $D$ of $y_-$ is then $\lesssim D\,\varepsilon_nL^{2(n-j)}$. This is the first line of (3.68), whose cube $\square^{\sim n-j+1}$ (Bałaban's indices) has $D\approx$ age$+2$.
  - The Schwarz lemma gives the rest. A sup bound $S$ on the polydisc of radius $c\varepsilon_j$ in the axial bond variables, with vanishing of order $k$ at $0$, gives $|f(w)|\leq S(|w|_\infty/c\varepsilon_j)^k$, with no derivative loss. The polydisc lies in $D^{\mathbb C}_j$, since $|V(\partial p)-1|\lesssim4c\varepsilon_j$ there.
- **Proof plan (corrected).**
  - *The cube.* Use an axial gauge on a cube containing $\mathrm{supp}\,\mathbf Y$, of radius about $R_j+|Y|$ level-$j$ units, with base point $y_-$.
    - (3.68) is printed only for $\square^{\sim n-j+1}$, which at small age is smaller than the support.
    - The larger-cube bound is "the construction of Sect. F [15]" that CRE p.283 invokes (N13). For ages $\geq R_j+|Y|$ the printed cube already contains the support. The distance factor above covers both cases.
  - *The ingredients:* $\mathbf Y=0$ at $B'=0$, because a configuration flat on the cube is exactly $1$ in complete axial gauge, together with the extraction of §4.1 (matrix activities) or (G4) (scalar ones); analyticity in $B'$; the larger-cube (3.68); the Schwarz lemma.
  - *Not needed.* The Taylor expansion (3.69) and the Stokes step (3.72). Bałaban uses them to identify the marginal $\beta_jF^2$ term. The line has no marginal term left once $Z_\ell(C)$ is extracted.
  - *Complex backgrounds.* Complexify the axial variables $B'$ as Bałaban does (p.280, (3.69)).
    - The base point $y_-$ with $u(y_-)=1$ makes the conjugation trivial for single-bond activities.
    - For clusters a factor $\rho(u(y_+))^{\mp1}$ of size at most $e^{C|Y|\cdot(\text{imaginary size})}$ remains. It is absorbed into $e^{-\kappa|Y|/2}$.
    - On real backgrounds the base point is immaterial, since $\|\rho(u)\mathbf X\rho(u')^{-1}\|=\|\mathbf X\|$ for $u,u'\in G$.
- **Comparing dressed loops (corrected).** Two class elements, on backgrounds $T_b$ and $T'_b$, are compared by multilinear telescoping in $\mathrm{End}(V_\rho)$,
  $$\Bigl|\chi_\rho\Bigl(\prod_iA_i\Bigr)-\chi_\rho\Bigl(\prod_iB_i\Bigr)\Bigr|\leq\sum_i\|A_i-B_i\|\prod_{k\neq i}\max(\|A_k\|,\|B_k\|),$$
  summed over polymer families. The terms are:
  - the activity differences;
  - the background-difference term $T_b-T'_b$, which is the cross-theory case S3(iii-b);
  - the scalar factor $Z_\ell(C)$.

  On $D^{\mathbb C}_\ell$, $\|T_b\|\leq e^{c\alpha}$, which gives the factor $e^{C\tau^2n}$ of (T-loop). V3's $\mathrm{Lip}_\chi$ (cor:main-leading-size) covers only Hermitian $X$ on a common background.
- **Scope.** S2 concerns the transported part of an activity, its value at the coarser background: "in the old only a background field is changed" (RG1 p.256). The fluctuation part becomes new activities only through R-S1, which is open.

### 4.3 S3: classical convergence [OPEN R-S3]

Needed, for $V$ regular at level $\ell$, with the two backgrounds $U^{(K)}_\ell(V)$ (on $T^{(K)}$) and $U^{(K+1)}_\ell(V)$ (on $T^{(K+1)}$):

- **(i) The main actions.**
  $$A^{\eta_{K+1}}(U^{(K+1)}_\ell(V))-A^{\eta_K}(U^{(K)}_\ell(V))=\sum_Xa_\ell(X;V),$$
  with the $a_\ell(X;\cdot)$ local, gauge invariant, flat-vanishing, Euclidean covariant, with zero $F^2$ part, analytic on $D^{\mathbb C}_\ell$ with a localisation family common with Bałaban's (§4.5), and $|a_\ell(X;V)|\leq C\,c_{\rm cl}(K-\ell)\,\varepsilon_\ell^2e^{-\kappa d_\ell(X)}$ there, where $c_{\rm cl}(m)\leq C_{\rm cl}\mu^m$ with $\mu=L^{-(1-\beta)}$, $\beta>0$ (§3(c)).
- **(ii) The Hessians.** The same for the Hessians at the background in Schur norm, because the fluctuation covariances depend on them (cf. V3 sec:c4-10-2).
  - (ii) follows from the analytic form of (i) by Cauchy's formula (radius $\sim\varepsilon_\ell$) and a weighted Schur sum; so do the higher vertices.
  - The two theories' critical points differ, so a critical-point difference also enters.
- **(iii) Gauge-invariant local functions (retyped after r2).** The two backgrounds live on $T^{(K+1)}$ and $T^{(K)}$, so one function $F$ cannot take both.
  - **(iii-a)** For $j\leq K$ and gauge-invariant local $F$ on level-$j$ fields: $F(M_jU^{(K+1)}_\ell(V))-F(M_jU^{(K)}_\ell(V))$, where $M_j$ is the average down to level $j$.
  - **(iii-b)** For the loop, put $\Delta_b(V):=\frac1i\log\bigl[U^{(K+1)}_\ell(V)(\gamma^{(K+1)}_b)\,U^{(K)}_\ell(V)(\gamma^{(K)}_b)^{-1}\bigr]$ for each level-$\ell$ bond $b$.
    - It is well defined, because the residual gauge transformations are $1$ on $T^{(\ell)}$ (RG1 p.256).
    - It is covariant at $b_-$ and vanishes at flat $V$.
    - Then, exactly, $W_\chi(C^{(K+1)};U^{(K+1)}_\ell(V))=\chi\bigl(\prod_be^{i\Delta_b}U^{(K)}_\ell(V)(\gamma_b)\bigr)$, a single-bond dressing.
    - What is needed is an age-decay bound on $\Delta_b$. This is a classical statement, not S2: the $\Delta_b$ are $O(\varepsilon_K)$ at age 0, not $C\tau^2$-small.
- **Where to look.** Bałaban PRT1–2 (propagators of the blocked Laplacians), VAR (the variational problem), REG (regularity). Uniformity in $\eta$ is available there (dimensionless lattices); convergence as $\eta\to0$ is not known to be stated.
- **The classical part by a two-sided sandwich (repaired after r2).**
  - *Composition property (N12).* RG1 writes the $k$-step average as $\bar U^k=M^k(U)$ ((0.21), p.256). The one-step average is (0.19), p.255. Needed: $M^{k+1}=M^k\circ M^1$ [to check in RG1 (0.4)–(0.9) and AVG]. CRE p.283 ("$U_k=U_{j,\square_0}(M^{\cdot}(U_k))$") presupposes nested averages.
  - *Minimality.* RG1 p.256 gives "exactly one critical orbit, which is a set of minima" in a space of regular orbits. Read every "min" below as the value on that orbit.
    - This needs the level-$\ell$ background to be regular in the level-$(\ell+1)$ sense, and conversely, and the outer problem to have an interior critical point.
    - Criticality then transfers by the chain rule, and uniqueness of the regular critical orbit identifies the two configurations [VAR/REG; closable].
  - *The sandwich.* Put
    $$\mathcal A^{(K)}_{{\rm cl},\ell}(V'):=A^{\eta_K}(U^{(K)}_\ell(V')),\qquad D_K(V):=\mathcal A^{(K+1)}_{{\rm cl},K}(V)-A^{\eta_K}(V)\ \ (V\text{ on }T^{(K)}),$$
    the age-0 classical difference. With the composition property, $\mathcal A^{(K+1)}_{{\rm cl},\ell}(V')=\min\{A^{\eta_K}(V)+D_K(V):\ M^{K-\ell}(V)=V'\}$.
    - Inserting the cutoff-$K$ minimiser $V=U^{(K)}_\ell(V')$ gives the upper bound.
    - Evaluating at the cutoff-$(K+1)$ minimiser $\widehat V:=M^1(U^{(K+1)}_\ell(V'))$, which satisfies the constraint, gives the lower bound.
    $$D_K(\widehat V)\;\leq\;\mathcal A^{(K+1)}_{{\rm cl},\ell}(V')-\mathcal A^{(K)}_{{\rm cl},\ell}(V')\;\leq\;D_K\bigl(U^{(K)}_\ell(V')\bigr).$$
  - *Consequence.* Both bounds are the age-0 difference $D_K$ at configurations regular at level $\ell$. So the scalar real form of S3(i) reduces to the decay of $D_K$ on smooth configurations, with no quadratic or nonlocal errors.
    - That decay needs $D_K$ gauge invariant (true: the Wilson action is $\geq0$ and $=0$ at flat configurations, and the constraint set is gauge covariant, V3 lem:global-average (ii)), flat-vanishing, and with zero $F^2$ part.
    - It also needs a localised form of $D_K$, for the axial-gauge argument of CRE pp.283–284.
  - *The $F^2$ part (age 0 only) [to prove].* CRE (3.66) fixes $A(h_z,U)=\tfrac12\sum\mathrm{tr}F^2+\dots$ for the unblocked action. So the claim is that the one-step blocked Wilson action has coefficient $\tfrac12$. It is a zero-momentum second derivative ((3.64)), and needs the normalisation of the linearised average on slowly varying fields (RG1 (0.4)) and the localised form of $D_K$. "Both are discretisations of $\tfrac12\int F^2$" is not a proof: the nonlocal blocking could renormalise it.
  - *At age 0* $D_K$ is $O(1)$ relative, between the Wilson action of $V$ and the minimal fine action with one block average equal to $V$. Hence $c_{\rm cl}(0)=O(1)$ and the young-level treatment of §4.4.
  - *What the sandwich does not give.* The polymer and complex-domain form of S3(i), and (ii) and (iii), still need the localisation and analyticity of $U_k(V)$ (VAR/PRT). Bałaban's convergence in $\eta$ is "not known to be stated", so they must be derived.
  - *Superseded (r2).* The first-order recursion of the earlier draft used "error quadratic in the perturbation" where $c_{\rm cl}(0)=O(1)$, and it produced a new nonlocal source at every level. The claim "R-S3 needs no separate source" is withdrawn.

### 4.4 S4: one-step propagation of differences [OPEN R-S4]

Restructured after the r1 review `cr-c-s4s6-20261021-r1` (§7). The earlier "class-wide Lipschitz bound" by interpolating $I^t=(1-t)I^0+tI^1$ was ill-typed and gave only $\mathrm{Lip}=O(1)$.

- **Universality form (repairs N1).**
  - The cutoff-$(K+1)$ theory after its first step is a density $\rho'_K$ on fields on $T^{(K)}$, the lattice on which the cutoff-$K$ theory starts.
  - From level $K$ down, both densities go through the same *untruncated* maps (corrected after r3).
    - Both are the push-forward under the same averaging, on the same lattices.
    - The gauge-fixing factor integrates to $1$ by the Faddeev–Popov argument of RG1 p.255.
    - RG1 (0.19) itself contains more than the averaging kernel: $\chi_k$, the term $-g_k^{-2}\sum[1-\mathrm{Re\,tr}\,U(y,x)]$, $A_k(g_k,U)$ and $N_k$. These depend on the theory's own coupling, and $\chi_k$ acts on gauge-fixed fluctuation variables.
    - So the *truncated* maps coincide only with one common cutoff: the gauge-invariant $D_{\ell+1}$ of the N4 model (§1.2), never Bałaban's $\chi_k$.

    At every level both are densities on fields $V$ on $T^{(\ell)}$.
  - So the comparison is between two initial densities on $T^{(K)}$ under one sequence of maps, with each theory's couplings matched at level 0. No step of one theory is compared with a different step of the other. In Bałaban's indexing the two steps are numbers $K+1-\ell$ and $K-\ell$; this is harmless because the parameters are frozen.
- **Common domain and frozen parameters (N6, N10; corrected after r3).**
  - *Domains.* Differences are taken between functions of $V$ on $D_\ell=\{V:|V(\partial p)-1|<c\,\varepsilon_\ell$ for every plaquette $p$ of $T^{(\ell)}\}$ and on the bounded complexification $D^{\mathbb C}_\ell=\{e^{iA}V_r:V_r\in D_\ell,\ |A(b)|<\alpha_{0,\ell}\}$ (§0).
    - Neither depends on either theory's background. They depend on $V$ and, through $\varepsilon_\ell$, $\alpha_{0,\ell}$, on the cutoff-$K$ coupling.
    - The literal complexification $\{|V(\partial p)-1|<c\varepsilon_\ell\}$ would contain every complex gauge transform of $1$ and be unbounded. This is why the radius is explicit.
  - $D_\ell$ is the route's own definition. RG1 p.259's $V$-condition has a fixed $\varepsilon_0$. Whether $D_\ell$ lies inside the "sufficiently regular configurations" of CRE (2.18), required by Theorem 2 (p.263), is to be checked (r2, m6).
  - *Frozen parameters (corrected in the Lipschitz push).* At each level, $\varepsilon_\ell$, $R_\ell$, $\alpha_{0,\ell}$, $\alpha_{1,\ell}$ and the localisation domains are computed from the reference flow $\bar x_\ell=g^{-2}+\tfrac{11}{24\pi^2}\kappa_G\ell\ln L$. They are used for both theories at all ages.
    - Computing them from the cutoff-$K$ coupling, as before, made the cutoff-$(K+1)$ theory differ between the pairs $(K,K+1)$ and $(K+1,K+2)$, so the telescoping of §1.3 failed (Lipschitz note §2.4).
    - By Lemma T each theory's own parameters are within a factor $e^{\pm2\tau}$ of the reference ones, with $\tau$ independent of $K$.
    - There is no frozen gauge-fixed cutoff $\chi$. "The same $\chi$" around two different backgrounds defines different sets, against (G1). The only cutoff is the common $D_{\ell+1}$.
    - R-S4 therefore needs Bałaban's step estimates with that cutoff (R-N4), and the truncation term (t1) goes to LF.
  - *The tolerance is not printed.* CRE (2.6)–(2.7) relate levels of one coupling sequence; they are not tolerances for running a step with another sequence's $\varepsilon_\ell$, $\alpha_{0,\ell}$, $\alpha_{1,\ell}$. A priori, RG1 (0.31) (p.259) bounds each theory separately, $g^{-2}+\beta\log(L^k\varepsilon)^{-1}\leq g_k^{-2}\leq g^{-2}+\beta'\log(L^k\varepsilon)^{-1}$. So it gives a relative difference of at most $(\beta'-\beta)/\beta$, which p.259 does not make small. A per-theory bound on $\beta_j-\beta_0$ gives a small a priori difference: this is Lemma T below, from the window form of the Bałaban project's Theorem 8.1 with (P2). Deriving a $1+O(\beta_0)$ tolerance "by §4.5" would be circular: §4.5's bound on $\delta^g$ is an output of (P-N) and (P-$\beta$), which need the tolerance.
  - *The tolerance is a priori (Lipschitz push; replaces the shooting argument of r3).*
    - Each theory is fixed by its own matching, the Bałaban project's Corollary 8.2 (for simple $G$). It is unique by D6 ($x_0\mapsto x_K$ strictly increasing).
    - The window form gives Lemma T: $|x^{(K)}_\ell/\bar x_\ell-1|\leq\tau=\delta/\bar b+Cg^2$ for all $K,\ell$, and $|x^{(K+1)}_\ell/x^{(K)}_\ell-1|\leq2\tau/(1-\tau)$.
    - So there is no shooting in $d$ and no intermediate value theorem, and the continuity of $\Delta\beta$ in $d$ is not needed.
    - The two-sided coupling system is closed by D9's contraction (§4.5).
    - In the N4 model, Corollary 8.2 needs (P2) and (C) for the N4 step (LIP-2). In CRE's setting, (P2) meets LIP-1.
  - $R_\ell$ is a power of $L$ by (2.5). For a small relative coupling difference it can differ by one factor $L$. In the transcription of (2.5), $r$ is used both as the power of $L$ and as the exponent of the log.
  - [OPEN, part of R-S4: CRE Section 3 with these frozen values and the cutoff $D_{\ell+1}$ (LIP-2).]
- **Reference representation and exogenous sources (C1, C2 item 1).**
  - The cutoff-$(K+1)$ action at level $\ell$ is written in the cutoff-$K$ representation. This is an identity at every age, by RG1 (0.22) and S3(i); it is *used* from age $m_*$ on (below):
    $$\mathcal A^{(K+1)}_\ell(V)=-(g^{(K+1)}_\ell)^{-2}\Bigl[A^{\eta_K}\bigl(U^{(K)}_\ell(V)\bigr)+\sum_Xa_\ell(X;V)\Bigr]+\mathbf E^{(K+1)}_\ell\bigl(U^{(K+1)}_\ell(V)\bigr),$$
    with $a_\ell$ the classical difference of S3(i).
  - *The classical difference stays exogenous (r2, M1).* It is not part of the regular-part difference $\mathbf E^{(K+1)}_\ell(U^{(K+1)}_\ell(V))-\mathbf E^{(K)}_\ell(U^{(K)}_\ell(V))$ that $e_m$ measures. It is not a Bałaban $\mathbf E$-term, so it does not age by (2.43); its decay is S3's $\mu$.
    - *It is an explicit step input (corrected after r3).* For the step itself, $g^{-2}\sum_Xa_\ell$ must be part of the input, in the enlarged class of the room below. It stays outside $e_m$ only as bookkeeping. At the cutoff-$K$ background it couples linearly to the fluctuation, and that linear term is treated like the linear term of any $\mathbf E$-term.
    - Its size is measured on $D^{\mathbb C}_\ell$, whose radius is Bałaban's $\alpha_{0,\ell}$. For a second-order flat-vanishing term the ratio to the size on the radius-$c\varepsilon_\ell$ domain is $(\alpha_{0,\ell}/\varepsilon_\ell)^2=(C_0/A_0)^2(\log g_\ell^{-2})^{2(q_0-p_0)}$. This changes $m_*$ by only $O(\log\log K)$.
    - *Booking of the shift energy (corrected after r3).* The Gaussian step gives the quadratic shift at the cutoff-$K$ Hessian; the sandwich of §4.3 gives the exact minimum. They agree only to quadratic order. Also the prefactor of $\sum_Xa_\ell$ changes by $\beta_\ell$ from level $\ell$ to level $\ell-1$, which leaves a term $\beta_\ell\sum_Xa_\ell$.
      - So the new terms are *defined* as the step output minus the exact S3 classical part at the next level.
      - The remainder (cubic shift terms and $\beta_\ell\sum_Xa_\ell$) is an $s_m$-type source, named $s^{\rm rem}_m$ below.
  - *Relocalisation of the cutoff-$(K+1)$ regular part (r3, C3(a)).*
    - $\mathbf E^{(K+1)}_\ell\circ U^{(K+1)}_\ell$ must be re-expressed as a function of the cutoff-$K$ background with Bałaban's locality (CRE p.259 (i)) and analyticity on $U^c_j$ (p.259 (ii)).
    - The composite $U^{(K)}\mapsto V=M^{K-\ell}(U^{(K)})\mapsto U^{(K+1)}_\ell(V)$ is nonlocal. It needs relocalisation with exponential tails from VAR/PRT [to check].
    - This is the same operation as Bałaban's own "in the old only a background field is changed" (RG1 p.256).
  - The two expansions integrate over the same set only with the common cutoff $D_{\ell+1}$. That is what identifies the reference-representation output with each theory's own creation-level terms.
  - The classical difference, the Hessian difference and the background differences (S3(i)–(iii)) are *sources*. They are given by S3 at every level and never recomputed from the recursion. They enter the new terms with an $O(1)$ Lipschitz constant, which is harmless because nothing feeds back into them.
  - Only the regular parts, the couplings and the loop insertions are propagated.
- **Young levels (W7).**
  - The classical source is about $p_0^2c_{\rm cl}(m)$ per point ($g_\ell^{-2}\cdot c_{\rm cl}\varepsilon_\ell^2=c_{\rm cl}p_0^2$). It exceeds the room $\rho$ of the regular-part class until age $m_*$.
  - $m_*$ is defined with a monotone bound (corrected after r3; $c_{\rm cl}(m)$ need not be monotone):
    $$m_*:=\min\{m:\ C\,p_0(g^{(K)}_K)^2\,C_{\rm cl}\,\mu^m\leq\rho/4\}.$$
  - For $m<m_*$ no reference representation is used. Each theory is controlled by Bałaban's bound, run with the frozen parameters and the common cutoff $D_{\ell+1}$. The difference is controlled by the trivial bound $2S$, where $S$ is the class bound.
  - Since $c_{\rm cl}(m)\leq C_{\rm cl}\mu^m$ and $p_0(g_K)^2=A_0^2(\log g_K^{-2})^{2p_0}$ with $g_K^{-2}\leq g^{-2}+\beta'K\log L$, we get $m_*\leq1+(2p_0\log\log K+O(1))/\log(1/\mu)=O(\log\log K)$.
  - The cost in the final rate is $\lambda'^{-m_*}\leq C(\log K)^{2p_0\log(1/\lambda')/\log(1/\mu)}$, with exponent below $2p_0$ since $\lambda'>\mu$. Here $C$ and $\rho$ do not depend on $K$.
- **Norms (N3; corrected after r3).**
  - $e_m$: a *route* norm at level $\ell=K-m$.
    - Bałaban's terms are localised and analytic in the background variables on $U^c_j$ (CRE p.259 (i)–(ii)). As functions of $V$ each depends on $V$ globally through $U_\ell(V)$.
    - So the regular-part difference is first relocalised in $V$, with exponential tails from VAR/PRT [to check].
    - $e_m$ is then the supremum over $D^{\mathbb C}_\ell$ of each relocalised term, with weight $e^{\kappa d_\ell(X)}$, after normalisation at the flat configuration.
  - $x_m$: for insertion differences in the class of S1 on the tube of the loop, $\sup_{D^{\mathbb C}_\ell}$ of the operator norm on $\mathrm{End}(V_\rho)$, with weights $e^{\kappa|Y|+\kappa d_\ell(Z)}$, per bond.
  - $\delta^g_\ell:=|(g^{(K+1)}_\ell)^{-2}-(g^{(K)}_\ell)^{-2}|$.
  - $s_m$: a sum of named norms of the S3 sources at age $m$:
    $$s_m:=\|\Delta\mathrm{Hess}_\ell\|_{\rm Schur}+c_{\rm cl}(m)+c_{\rm bg}(m)+s^{\rm rem}_m,$$
    with the Hessian difference (S3(ii)), the classical difference coefficient (S3(i)), the booked remainder above, and $c_{\rm bg}(m)$ the constant of the S3(iii-a) bound on $F(M_jU^{(K+1)}_\ell(V))-F(M_jU^{(K)}_\ell(V))$ (the two backgrounds live on different lattices, so there is no norm of $U^{(K+1)}_\ell-U^{(K)}_\ell$).
    - That $c_{\rm cl}$, not its supremum $p_0^2c_{\rm cl}$, measures the effect on the step is part of the step estimate. The heuristic: the second-order fluctuation effect is $g^{-2}c_{\rm cl}\cdot g^2=c_{\rm cl}$, the first-order term has zero Gaussian mean, and the shift is $c_{\rm cl}^2p_0^2\leq c_{\rm cl}\rho/(4C)$ for $m\geq m_*$.
- **Creation-level quantities (r2, S3).** (2.43) bounds each creation level separately, with constant $E_1(\beta_E)\neq1$, so the estimates are stated per creation level.
  - $n_m$: the $e$-norm of the difference of the two theories' regular-part terms *created* by the step at age $m$.
  - $y_m$: the $x$-norm of the difference of the loop activities created at age $m$.
  - $e_m$ and $x_m$ are the totals at age $m$, over all creation ages $m'\leq m$.
- **Superseded form (Lipschitz push).** The estimates below are kept as the r3 record. They are replaced by the system (E), (R), (C) of the Lipschitz note §4.2, which is D9's (Bałaban project, `DIFFERENCES_PROOFS.md` §3.4). The differences:
  - $\mathbf R$-terms feed later $\mathbf E$- and $\mathbf R$-terms ($BS_l$, $AS_l$);
  - the $\mathbf R$-coefficient is $Cg_l^{\kappa_0}\leq A\omega_l^p$, not $\omega$;
  - the coupling weights are $\eta\omega_l$ with $\omega_l=1/(n-l+1)$;
  - new terms depend on each earlier creation level with weight $\theta^{l-m}$ (D2), not on the aged total $e_m$.
- **The one-step estimates to prove (r3 form).** For $m\geq m_*$:
  $$\text{(P-N)}\quad n_{m+1}\leq C(L)\bigl(\omega(g)\,e_m+s_m+\omega_g(g)\,\delta^g_{K-m}\bigr),$$
  $$\text{(P-}\beta\text{)}\quad |\Delta\beta_{K-m}|\leq C(L)\bigl(s_m+\omega(g)\,e_m+\omega_g(g)\,\delta^g_{K-m}\bigr),$$
  $$\text{(P-Y)}\quad y_{m+1}\leq C(L)\bigl(\omega(g)\,x_m+e_m+s^{\rm line}_m+\omega_g(g)\,\delta^g_{K-m}\bigr),$$
  $$\text{(P-R)}\quad r_{m+1}\leq C(L)\,g_{K-m}^{\kappa_0}\bigl(\omega(g)\,e_m+s_m+\omega_g(g)\,\delta^g_{K-m}\bigr),$$
  together with the aging of what was created earlier:
  $$\text{(A)}\quad e_m\leq\sum_{m'\leq m}E_1'L^{-\beta_E(m-m')}n_{m'}+(\text{S3(iii-a) sources}),\qquad x_m\leq\sum_{m'\leq m}C_Y\lambda_Y^{\,m-m'}y_{m'}+(\text{S3(iii-b) sources}).$$
  - $\beta_E<1$ is the exponent of (2.43), and $\omega(g),\omega_g(g)\to0$ as $g\to0$.
  - *The coupling terms (corrected after r3).* $\beta_j$ is computed with each theory's own $g_{j-1}$, and $g$ enters the holonomy through the rescaled fluctuation. So (P-$\beta$) and (P-Y) carry $\omega_g\delta^g$ like (P-N). This creates a loop $\delta^g\to\Delta\beta\to\delta^g$. It closes in the weighted sup norm of §4.5 if $\omega_g/(1-\lambda')$ is small.
  - The term $e_m$ in (P-Y) has an $O(1)$ constant as an upper bound. It could be $\omega e_m$, since the transported bulk factor cancels in $N/\rho$.
  - *(P-R), the $\mathbf R$-terms (r3, N15).* $r_m$ is the norm of the difference of the two theories' $\mathbf R$-terms created at age $m$. They exist in the pure small-field model: $\mathbf R''^{(k+1)}$ comes from the second expectation value in (3.26) and the R-operation (CRE p.279). (2.44) bounds them by $R_1g_j^{\kappa_0}$ per unit volume with no age factor (CRE p.263, $\kappa_0\geq7$ by (2.46)).
    - (P-R) is the form a difference bound would take if the R-operation is linear in the input regular part, as the (2.44) bound suggests [to check: the definition of the R-operation and (3.26)].
    - Without an age factor, the created $\mathbf R$-differences sum over ages to $\sum_m(\log K)^{O(1)}g_{K-m}^{\kappa_0}\lambda'^{m}$-type terms. These are dominated by the young levels, where $g_{K-m}^{\kappa_0}\sim K^{-\kappa_0/2}$. (This r3 rate is withdrawn, since it omits the R-feedback; see §1.3.)
  - $E_1'$ is the constant of (2.43) per unit creation size [to check, CRE pp.279–284]. Homogeneity in the creation size does not follow from linearity alone:
    - p.263 lets $E_1$ depend on "the other constants occurring in the formulation", which may include $E_0$;
    - linearity of the operations gives homogeneity only if every bound in the proof is linear in the input supremum on a fixed domain.
  - $\lambda_Y<1$ is the rate of S2 in weakest form.
  - The bulk density does not depend on the loop, so (P-N), (P-$\beta$), (P-R) and the first part of (A) contain no $x$ or $y$: the system is triangular.
- **Where the smallness comes from (C2, items 2–3).**
  - *The transported part.* The value of an old term at the new background ages as in (A), through (2.43) applied to the difference per creation level (§4.5). It is not a per-level contraction.
  - *The fluctuation part.* An old term enters a new term only through $\mathbf E(\mathrm{bg}+A)-\mathbf E(\mathrm{bg})$, with $A$ the fluctuation field. By Cauchy's formula on the polydisc, this is bounded by the input difference times (fluctuation size)/(analyticity radius).
    - For Gaussian-typical fluctuations that ratio is $g_k/\alpha_{0,k}=1/(C_0(\log g_k^{-2})^{q_0})$ (CRE (2.28), p.259). It is small through the analyticity margin: polylogarithmically in $g$, not like $g^\kappa$. This is $\omega(g)$.
    - It matches the norm because $D^{\mathbb C}_\ell$ has radius $\alpha_{0,\ell}$ in the $A$-directions (§0; corrected after r3). On a domain of radius $c\varepsilon_\ell$ the same step would give $1/(cp_0(g_\ell))$, also polylogarithmically small, plus a cutoff tail $e^{-cp_0^2}$.
    - "Only through $\mathbf E(\mathrm{bg}+A)-\mathbf E(\mathrm{bg})$" passes over the nonlinearity of $\log\int\exp$. This is harmless per polymer if $\omega\,(E_0+\rho)$ is small.
    - [OPEN: the meaning of $\alpha_{0,j}$ in (I.1.9), and whether $E_0$ depends on $C_0$.]
  - *The coupling (corrected after r3).* It enters through the higher vertices, through $\mathbf E(\mathrm{bg}+g\tilde A)$, through the rescaled cutoff ($\varepsilon_\ell/g$ differs between the theories) and through the normalisations. Each is plausibly small, which gives $\omega_g(g)$.
  - *$\Delta\beta$.* This is the $\beta$ of the difference function, since (3.57)–(3.64) are linear. It must be bounded through the Gaussian representation of the flat second-order kernel $\Pi^{(j)}$ (CRE (3.57), (3.63); (I.5.16)): by the covariance difference, which is $O(s_m)$, plus $\omega(g)e_m$. A field-space Cauchy estimate gives only $|\Delta\beta|\lesssim\varepsilon_k^{-2}e_m$, which loses $g^{-2}$ (C3).
- **Room and the scaled Cauchy step (C1, Plan 4).**
  - *The enlarged class.* Let $\rho$ be such that Bałaban's step estimates hold on $\{I+we:\ I$ in the class, $\|e\|=1$, $w\in\mathbb C,\ |w|\leq\rho\}$ in the affine directions (regular part, $g^{-2}$, the classical input, insertions). The coefficients $w$ are complex, so the step must accept complex-coefficient inputs; that Bałaban's estimates do is part of the claim.
  - *A value bound is not enough (corrected after r3).* Let the new terms be bounded by $S+\omega\rho$ on that disc; the transported part of a perturbation of size $\rho$ is $O(\rho)$ and is not included. The scaled Cauchy estimate then gives $|\Delta O|\leq(2S/\rho+2\omega)\|\Delta I\|$ for $\|\Delta I\|<\rho$. That constant is at least $1/4$ for $\rho=8S$, so it does not give (P-N).
  - *The core claim of R-S4, in variation form.* For $I$ in the class and $\|e\|=1$,
    $$\sup_{|w|\leq\rho}\|\mathbf N(I+we)-\mathbf N(I)\|\leq C\omega(g)\rho\ \ \text{(regular-part direction)},\qquad\leq C\omega_g(g)\rho\ \ \text{($g^{-2}$ direction)},$$
    where $\mathbf N$ denotes the new terms. The Schwarz lemma then gives $\|\Delta\mathbf N\|\leq C\omega\|\Delta I\|$ (resp. $C\omega_g$) for $\|\Delta I\|<\rho$.
  - *Why $\rho\geq4S$.* A priori $e_m\leq2S$ and the insertion differences are at most $2S$, so the differences never leave the disc if $\rho\geq4S$. Then (P-N), (P-$\beta$), (P-Y) hold without a smallness premise (§4.5). The coupling direction is covered by the shooting tolerance above. (r3 record. Since the Lipschitz push neither is needed: see Lemma G and Lemma T below.)
  - *Order of constants.* $\rho\geq4S$ with $S$ at least the class bound means $E_0+\rho\gtrsim5E_0$, which is admissible only if $\rho$ is fixed before $\gamma$ and $g$. The route's order ($L$, then $\lambda'$, then $g$) is extended to $L,\lambda',C_0,E_0,\rho,\gamma,g$. If $E_0$ depends on $C_0$ (a supremum on an $\alpha_0$-domain), then $\omega(E_0+\rho)\to0$ as $g\to0$ still holds, because of the factor $(\log g^{-2})^{q_0}$, provided $C_0$ is fixed first.
  - *Revised in the Lipschitz push (note §3).*
    - *Lemma G.* If the step is holomorphic and bounded by $M$ on the $\rho$-neighbourhood of the class, it is $(4M/\rho)$-Lipschitz between *any* two class points: use D1 when the points are closer than $\rho/2$, the trivial bound $2M$ otherwise. So neither $\rho\geq4S$ nor the a priori $e_m\leq2S$ is needed.
    - *The constant.* $M$ bounds the new terms, $O(1)C_3\varepsilon_1$ (RG2 (2.41)), with $C_3\propto E_0$. So $4M/\rho=O(\varepsilon_1/\vartheta_0)$ with room $\rho=\vartheta_0E_0$, and the order of constants needs only $\vartheta_0$ fixed before $\gamma$ and $g$.
    - *The r3 objection.* The bound $2S/\rho+2\omega$ used the class bound of all terms. The transported part is linear and is aged separately, with $E_1'$ from Lemma H.
    - *The analytic premise.* Holomorphy on the complexified class is D_HOLO (LIP-3), and the N4 version is LIP-2.
    - *In CRE's setting.* The new-term ratio is $\varepsilon_k/\alpha_{0,k}$ [to check: $q_0>p_0$], and LIP-1 applies to $\Delta\beta$.
  - *What the pages do not show.* CRE p.254 says the general-step operations are left undefined: "only their basic general properties are formulated". $E_0$, (I.1.18) and any order of fixing are not on pp.254–263. The claim is a checkable proof obligation in the pure small-field model: re-run RG1's small-field construction with CRE Section 3. It closes if Bałaban's bounds are linear in $E_0$, with smallness entering only through $\gamma$ and $g$. [OPEN, part of R-S4 and R-N4.]

### 4.5 S5: difference induction [OPEN R-S5]

- **(2.43) for differences.**
  - *Linearity of the identities.* I read the first proof (CRE pp.279–283) and the Ward–Takahashi identities it uses (RG1 (4.12)–(4.15), p.284; (4.10)–(4.11) precede them on p.283). The algebraic identities are linear in the function:
    - the Taylor coefficients of (3.49);
    - the identities (3.51)–(3.55), "by the first identity (I.4.15)" (p.281);
    - the resummation to $\Pi^{(j)}$ (3.57), which uses the functions $\mathbf E^{(j)}(U_j,z)$ defined on the whole lattice $L^{-j}\mathbb Z^d$ (p.281);
    - Euclidean covariance (3.58)–(3.61), from (2.29); (3.60) also uses the first Ward–Takahashi identity;
    - the identification (3.62)–(3.64): (3.62) uses translation invariance and (I.4.15) (p.282), and (3.64) uses "(I.5.16), or (I.5.37)" (p.283). By linearity the marginal coefficient of the difference is $\Delta\beta_j$.
  - *The estimates are not shown linear (corrected after r3).* The steps that carry the bounds are:
    - the far-domain bound (3.48), which is the a priori bound (I.1.18). It is a bound, not an operation, and must hold for a difference with $E_0$ replaced by the difference's localised norm;
    - the remainder of (3.49), obtained from the expansion (I.3.34) with remainder (I.3.54)/(I.3.35), the bound (I.3.32), and "other operations" of Sect. 4 [I] (p.280);
    - the expansion (3.66) of the action, used in (3.67).

    Their homogeneity in the input norm is [to check, RG1 Sects. 3–4].
  - *What the identities need.* The Ward–Takahashi identities follow from gauge invariance of $\mathbf E(\exp iB)$ in the level-$j$ field $B$. (I.4.14) also uses semisimplicity of $G$ (RG1 p.284: "The group $G$ is semisimple, hence this is possible only for the element 0"). For simple $G$ the centre of $\mathfrak g^c$ is $0$.
  - *Consequence (corrected after r3).* Applying (2.43) to a difference is a re-run of Bałaban's proof, not his printed theorem [OPEN, R-S5]. It needs:
    - a common localisation family, although $R_\ell$ may differ by a factor $L$ (N6);
    - per-term gauge invariance (CRE p.259 (iii)) and Euclidean covariance;
    - analyticity as functions of the common level-$j$ field $\exp iB$;
    - regularity of the evaluated configuration. The first proof uses that the configuration "coincides with a $U_n$-type" configuration (p.280). For theory $K+1$ the configuration is $U^{(K+1)}_j(B^{(K)})$, whose regularity needs VAR/PRT [to check].
  - *The cross term (r3).* (2.43) (p.263) subtracts $\beta_j(g_{j-1})A(\phi,U_k)$, and each theory subtracts with its own action $A^\eta$ on its own finest lattice. So the first bracket of the split below equals
    $$\Bigl\{\Delta\mathbf E-\Delta\beta_j\,A^{\eta_K}\bigl(\phi_j,U^{(K)}_j(B)\bigr)\Bigr\}-\beta^{(K+1)}_j\Bigl[A^{\eta_{K+1}}\bigl(\phi_j,U^{(K+1)}_j(B)\bigr)-A^{\eta_K}\bigl(\phi_j,U^{(K)}_j(B)\bigr)\Bigr].$$
    - Only $\{\cdots\}$ is proportional to $n_{m'}$ and ages by (2.43), with constant $E_1'$ [to check: $E_1$ "dependent on the other constants" (p.263), possibly $E_0$].
    - $[\cdots]$ is $\beta_j$ times a localised classical difference. It is an S3(i)-type exogenous source, counted once together with $(g^{(K+1)}_\ell)^{-2}\sum_Xa_\ell$ of §4.4.
  - *Not printed.* (2.43) bounds real values on "sufficiently regular configurations ... (2.18)" (p.263). The $e$-norm is an analytic polymer norm on $D^{\mathbb C}_\ell$, so the complex-domain form must be derived (R-S5). p.280 ("replace the background configuration by the corresponding complex variables") suggests it is reachable.
  - *Split of the transported difference.* With $B^{(\cdot)}$ the level-$j$ field of each theory's background at the current level,
    $$\mathbf E^{(K+1)}(B^{(K+1)})-\mathbf E^{(K)}(B^{(K)})=\bigl[\mathbf E^{(K+1)}-\mathbf E^{(K)}\bigr](B^{(K)})+\bigl[\mathbf E^{(K+1)}(B^{(K+1)})-\mathbf E^{(K+1)}(B^{(K)})\bigr].$$
    - The first bracket is treated as in the cross-term bullet.
    - The second needs S3(iii-a) in *family form* (corrected after r3; N5). $F$ ranges over all of theory $K+1$'s created terms, at all creation levels, each of size $E_0$ at creation. The bound required is a Cauchy bound in the level-$j$ field, with constant equal to each term's aged size, times the S3 background difference in units of the analyticity radius, summed over creation levels. This is part of R-S3.
- **The coupling is matched at level 0 (N2).**
  - Each theory moves the marginal part of its new terms into its own coupling (CRE p.279; RG1 (0.20); CRE (2.24)). With both matched at level 0, $\delta^g_\ell\leq\sum_{\ell'=1}^{\ell}|\Delta\beta_{\ell'}|$.
  - The coupling difference at level $K-m$ therefore depends on the ages $m'\geq m$: the system is two-sided, and a forward induction in $m$ is ruled out.
  - *Finiteness (corrected after r3).* For finite $K$ every $e_m$ and $\delta^g_\ell$ is finite, because each theory has its own Bałaban bounds. A linear inequality $N\leq\theta N+c$ with $\theta\leq\frac12$ then gives $N\leq2c$, but only if (P-N), (P-$\beta$), (P-Y) hold without a smallness premise.
    - For the regular part and the insertions this holds because $\rho\geq4S$ and a priori $e_m\leq2S$ (§4.4, room).
    - For the coupling it needs the frozen-parameter tolerance, which is now the a priori Lemma T (§4.4).
    - *Since the Lipschitz push* no smallness premise is needed at all: Lemma G gives the Lipschitz bounds between any two class points (§4.4, room).
- **Replaced (Lipschitz push): the two-sided system.** The weighted estimate below is kept as the r2/r3 record, but its conclusion is withdrawn. It omits the feedback of $\mathbf R$-terms into later terms, and its bound $e_m\leq C\lambda'^m$ fails once the floor $BS$ is present. The replacement is D9 (Bałaban project, `DIFFERENCES_PROOFS.md` §3.4; Lipschitz note §4.3):
  - *Statement.* $\sum_{m\leq n}\theta^{n-m}e_m+S_{n+1}\leq C(n+1)^{1-p}$, with $p=3$ for $\kappa_0\geq7$ and $C$ linear in the source constant.
  - *Proof.* A contraction in a weighted maximum over all levels, which handles the two-sided coupling directly.
  - *Rate.* With the young levels, $\theta_K\leq C(\log K)^{O(1)}(K+1)^{-2}$.
  - *Scope.* It holds as proved on RG1's fixed domains. On CRE's domains, LIP-1.
- **The weighted estimate (creation-level form, repaired after r2; superseded).**
  - Fix $\lambda'$ with $\max(L^{-\beta_E},\mu)<\lambda'<1$, and put $N:=\sup_{m\geq m_*}\lambda'^{-m}n_m$ and $\widehat E:=\sup_{m\geq m_*}\lambda'^{-m}e_m$.
  - *Young creation levels.* Terms created at ages $m'<m_*$ are compared by the trivial bound only. Each theory's own (2.43) still ages them: their difference at age $m$ is at most $2E_1L^{-\beta_E(m-m')}$ per point. Summed over $m'<m_*$, this is at most $CE_1\lambda'^{\,m}\lambda'^{-m_*}$ for $m\geq m_*$. Caveats (r3, C8):
    - $V\in D_\ell$ must lie in each theory's regular set (2.18) (m6);
    - theory $K+1$'s extra top creation level must be included;
    - this is a real-valued bound on a sum over $\Omega$, not the analytic polymer $e$-norm in which $\widehat E$ is defined. Using it inside $\widehat E$ needs the analytic polymer form of (2.43) for each theory separately, and relocalisation into the common family (N6). Both are part of R-S5.
  - *Aging.* (A), the young levels and the S3(iii-a) sources ($\leq C\mu^m$) give
    $$\widehat E\leq\frac{E_1'\lambda'}{\lambda'-L^{-\beta_E}}\,N+CE_1\lambda'^{-m_*}+C .$$
  - *Coupling.* (P-$\beta$), $s_m\leq C\mu^m$ and the two-sided sum $\delta^g_{K-m}\leq\sum_{m'\geq m}|\Delta\beta_{K-m'}|$ give $\delta^g_{K-m}\leq C(L,\lambda')\lambda'^m(1+\omega(g)\widehat E)$. The term $\omega_g\delta^g$ of the corrected (P-$\beta$) is absorbed when $C(L)\omega_g/(1-\lambda')\leq\frac12$.
  - *Creation.* (P-N) then gives $N\leq\theta N+C(L,\lambda')\bigl(\lambda'^{-m_*}E_1+(1-\lambda')^{-1}\bigr)$, with
    $$\theta=\frac{C(L)\,\omega(g)\,E_1'}{\lambda'-L^{-\beta_E}}\Bigl(1+\frac{C(L)\,\omega_g(g)}{1-\lambda'}\Bigr).$$
    $n_{m_*}$, created from a young input, enters through the trivial bound $2S\lambda'^{-m_*}$, which the source term covers.
  - Choose $L$, then $\lambda'$, then $g$ small, so that $\theta\leq\tfrac12$. This needs $E_1'$, $C(L)$ and $C_Y$ independent of $g$, and $\omega$ monotone ($g_\ell\leq g$ by (0.31)). Then the smallness comes from $\omega(g)$ alone, and
    $$n_m,\ e_m\leq C(L,\lambda')(\log K)^{O(1)}\lambda'^m,\qquad\delta^g_{K-m}\leq C(L,\lambda')(\log K)^{O(1)}\lambda'^m\qquad(m\geq m_*).$$
  - *The $\mathbf R$-terms (r3, N15).* By (P-R) and the bounds above, $r_{m+1}\leq C(L,\lambda')(\log K)^{O(1)}g_{K-m}^{\kappa_0}\lambda'^m$ for $m\geq m_*$. For $m<m_*$ each theory's own (2.44) gives $r_m\leq2R_1g_{K-m}^{\kappa_0}$ per point.
    - (2.44) has no age factor, so all of these survive to level 0. Their sum is at most $C(L,\lambda')(\log K)^{O(1)}g_K^{\kappa_0}\leq C(\log K)^{O(1)}K^{-\kappa_0/2}$, dominated by the young levels.
    - Whether $\mathbf R$-terms feed into later $\mathbf E$-terms, which would add a term to (P-N), is [to check: CRE (3.26) and the R-operation].
  - The rate conditions are built in: $\lambda'>\mu$ (r1) and $\lambda'>L^{-\beta_E}$ (r2).
  - At the top, $\delta^g_K=O(\log\log K)$ absolute, from the young levels. It is $O(1)$ if (P-$\beta$) is also proved for $m<m_*$ (§3(d)).
- **The loop (creation-level form).**
  - Fix $\lambda_*$ with $\max(\lambda',\lambda_Y,\mu_{\rm line})<\lambda_*<1$, where $\mu_{\rm line}$ is the decay rate of the transport defects $\Delta_b$ (S3(iii-b)). Put $N_Y:=\sup_{m\geq m_*}\lambda_*^{-m}y_m$.
  - (A) gives $x_m\leq C_Y\lambda_*^m N_Y/(1-\lambda_Y/\lambda_*)$ plus the S3(iii-b) sources and the young levels. The young levels need each theory's own S1/S2.
  - (P-Y) then gives $N_Y\leq\bigl(C(L)\omega(g)C_Y/(\lambda_*-\lambda_Y)\bigr)N_Y+C(L,\lambda_*)(\log K)^{O(1)}$. For $g$ small,
    $$x_m\leq C(L,\lambda_*)(\log K)^{O(1)}\lambda_*^m .$$
  - No finiteness premise is needed: Lemma G applies to the loop step if it is holomorphic in its inputs (part of R-S1), and the coupling term is bounded by Lemma T. The bulk bounds of D9 enter as sources.
  - *Creation levels under merging (r3).* The $Z_\ell$-extraction and the merging re-expansion of §4.1 are nonlinear and mix creation levels. That the creation-level identity of loop activities survives them is not shown. A telescoping bound appears to restore the bookkeeping at a cost at most polynomial in $K$ [OPEN, part of R-S5].
  - $\lambda_Y\approx L^{-1}$ (that is, $\alpha_{\rm line}=1$) rests on R-S2; $\mu_{\rm line}<1$ rests on R-S3(iii-b).

### 4.6 S6: assembly at level 0

- **From the induction (corrected after r3).**
  - With $\delta^g_0=0$ the action difference at level 0 is $\mathcal A^{(K+1)}_0-\mathcal A^{(K)}_0=-g^{-2}\sum_Xa_0(X;V)+(\text{regular-part difference})+(\mathbf R\text{-term difference})$.
    - The regular-part difference is bounded by $e_K$, and the constant $c_K$ is the difference of the vacuum energies.
    - The classical term is S3(i) at age $K$, with $g^{-2}|a_0|\leq Cp_0(g)^2C_{\rm cl}\mu^K$.
    - The regular-part and $\mathbf R$-term differences together are D9's top quantity $\sum_m\theta^{K-m}e_m+S_{K+1}$ (§4.5).
    - So $\theta^{\rm act}_K\leq C\mu^K+C(\log K)^{O(1)}(K+1)^{-2}$ (corrected in the Lipschitz push).
  - $x_K$ gives (T-loop) in absolute form (§1.3), via the telescoping of §4.2, with the $\mathbf E$-part rate $C(L,\lambda_*)(\log K)^{O(1)}\lambda_*^K$. Whether the loop activities carry $\mathbf R$-type remainders is [to check, with N15]. If they do, these enter at the same polynomial order.
- **To the model expectation (C5).**
  - $c_K$ cancels in normalised expectations.
  - Interpolating $\rho^s=\rho^{(K)}e^{sD}$: $\frac{d}{ds}\mathbb E_s[F]=\mathrm{Cov}_s(F,D)$, and $|\mathrm{Cov}_s(F,D)|\leq2\sup|F|\sup|D|$ for real $D$ on the real domain $D_0$. (T-act) gives $\sup|D|\leq\theta_K\sum_Xe^{-\kappa d_0(X)}\leq CL^{4M_T}\theta_K$. Hence $|\Delta\mathbb E[F]|\leq2CL^{4M_T}\sup|F|\,\theta_K$.
  - By §1.3 (weakest form), $\sup_{D_0}|\widetilde{\mathcal W}^{(K)}_0|$ is bounded uniformly in $K$, so the absolute (T-loop) suffices.
  - Only real sup bounds at level 0 are used. Neither the complex polymer form nor gauge invariance is needed at this stage.
  - The domain is the common $D_0$ (m6 still open).
- **The physical statement** needs LF.

## 5. Order and dependencies

- **S0** is given, for $SU(2)$ only (W5).
- **S3** is independent of the other steps in its proof. It needs the composition property of $M^k$ (N12) and VAR/PRT for the polymer and analytic forms. Its output is used by S4 (the size of the sources decides $m_*$), and directly by S5 (the family form of S3(iii-a), the cross term) and S6 (S3(i) at age $K$). Its loop part (iii-b) is a classical transport defect, not an S2 insertion.
- **S1** fixes the class used by S2, by S4 and by the loop part of S5. It needs N11 (covariance of the activities, sub-item (a)), the base case (sub-item (d)), N12 (gap transports) and a covariance decay rate from PRT.
- **S2** needs the class of S1 and the larger-cube (3.68) (N13).
- **S4** needs:
  - S3;
  - the S1 class (for (P-Y));
  - the room claim (Lemma G with D_HOLO);
  - N6 with Lemma T;
  - Bałaban's bounds in the N4 model (R-N4, LIP-2);
  - LIP-1.
- **S5** needs S0 (the matching enters through the two-sided coupling system), S2, S3 and S4, and its own items: the analytic polymer form of (2.43), $E_1'$, and the creation-level identity under merging.
- **S6** needs S5 and S3(i), and LF for the physical statement.
- **Separately workable:** S3, and S2 once $\mathfrak L$ is fixed.

## 6. Weak points (to be repaired, not carried)

Ranked as in the r1 review (`cr-c`, C6), with the items N1–N10 it added. Where a weak point is marked repaired, the repair is in the section named.

- **W4 / N4 (decisive for the physical claim): large fields and the truncation.**
  - (T-act) and (T-loop) are for $\Lambda_j=\Omega_j=$ the torus, which is atypical (§3(g)).
  - Bałaban's small-field cutoffs are imposed on gauge-fixed fluctuation variables, which differ between the theories, and (G1) applies to full integrals, not to truncated ones.
  - *Repair of the definition:* impose the small-field condition on both theories by the common gauge-invariant condition $D_{\ell+1}$ on the level-$(\ell+1)$ field before each step. The cutoff is a product of conjugation-invariant plaquette conditions, so the model is gauge invariant and the same for both theories from level $K$ down. Theory $K+1$'s top cutoff $D_{K+1}$ uses its own $\varepsilon_{K+1}$, since there is no cutoff-$K$ value to freeze.
  - *Consequence (r3), now the named open item R-N4.* Every Bałaban input of §4.5 leaves printed scope: (2.43), the Theorem 1 class bounds, $E_0$ and (I.1.18). Closing R-N4 means re-running CRE Sect. 3 and Theorem 2 with the product of local gauge-invariant indicators, plus a REG-type comparison of the two cutoff sets.
  - *The difference between the two cutoffs* is a large-field quantity only if the gauge-invariant set and Bałaban's gauge-fixed regular set are nested with comparable constants (the REG comparison lemma). The symmetric difference then consists of threshold fields costing $e^{-cp_0^2}$ per cube. By §3(g) such configurations occur with probability tending to $1$, so the discrepancy is as hard as LF, not a small correction.
- **W1 (serious): the contraction.** Reduced to (P-N), (P-$\beta$), (P-Y), (P-R) and the room claim of §4.4 in variation form, with the creation-level aging (A). This is the substance of R-S4. Since r2 the smallness comes from $\omega(g)$ alone, so $E_1(\beta_E)>1$ does no harm. Since r3 the finiteness premise of §4.5 is explicit: $\rho\geq4S$ for the regular part and the insertions, and the shooting tolerance for the coupling.
  - *Since the Lipschitz push:* the finiteness premise is dropped (Lemma G) and the tolerance is Lemma T.
  - The bulk system is D9's (E), (R), (C), proved on RG1's fixed domains.
  - What is left of W1: LIP-1 (CRE domains), LIP-2 (N4), LIP-3 (class-wide readings), and the loop part (P-Y).
- **W3 / W6 (serious): the existence of $\mathfrak L$.**
  - V3's first-step results are identities of expectations. Their pointwise-in-$V$ cluster form (sub-item (d) of R-S1, through $E_{\rm def}$) is not proved.
  - CRE leaves the general-step operations undefined (pp.254–255; V3 rem:next-step (3)(b)).
  - R-S1 is the item the r1 reviewer judged least likely to close. The r2 reviewer judged its formal closure closable by standard one-dimensional polymer methods, given N11, N12 and a decay rate; the base case and the general-step input remain the hard part.
- **N11 (serious, §4.1): covariance of the activities.** Bałaban's integral is gauge fixed. The activities must be built from background-covariant propagators, or a matrix analogue of CRE p.259 (iii) must be proved.
- **N12 (moderate, §4.1, §4.3, §4.5): composition of the averages.** The semigroup property $M^{a+b}=M^a\circ M^b$, with $M^b$ from level $\ell+a+b$ to level $\ell+a$ and $M^a$ from there to level $\ell$, and the identification of the two-stage minimiser. It is used by the gap transports, by the sandwich, and by §4.5's use of $U_k=U_j(M^jU_k)$. To check in RG1 (0.4)–(0.9), AVG and VAR.
- **N13 (moderate, §4.2): the larger axial cube.** (3.68) is printed for $\square^{\sim n-j+1}$ only. S2 needs a cube containing the support ("Sect. F [15]", CRE p.283).
- **N14 (serious for the physical claim, part of LF).** The printed (2.44) gives $\mathbf R$-terms no age factor (p.263), so the physical rate from printed bounds is at best about $(K\log L)^{-\kappa_0/2}$. p.283 gives $(L^jL^{-n})^4g_j^{\kappa_0}$ per level-$j$ point, which is no gain per level-$n$ point. The large-field contribution per unit length diverges and must go into the perimeter counterterm. By N15 the polynomial rate already holds in the small-field model.
- **N15 (serious for the rate, r3).** $\mathbf R$-terms exist in the pure small-field model (CRE p.279) and do not age by the printed (2.44). With their feedback into later terms (D9's (E), (R)), the model's rate is $\theta_K\leq C(\log K)^{O(1)}(K+1)^{1-p}$, with $p=3$, summable since $\kappa_0\geq7$. The earlier $K^{-\kappa_0/2}$ is withdrawn (Lipschitz push). A power of the spacing needs a proof that the $\mathbf R$-terms age. (R) is to be checked against CRE (3.26) and the R-operation. In RG1's fixed-constant setting (LIP-1 repair (a)), whether R-type terms occur at all is to be re-read.
- **R-N4 (serious, r3).** Bałaban's bounds in the compared model, with the cutoff $D_{\ell+1}$ (W4/N4 above).
- **W5 (reduced in the Lipschitz push).** The matching is printed for $SU(2)$ only. For simple $G$, `RG1_Thm2_REP` is now imported: it is proved in RG1's model, with uniqueness from D6. What remains is LIP-2 (N4) and, in CRE's setting, LIP-1.
- **N6 (partly repaired in the Lipschitz push, §4.4).** The tolerance is Lemma T, a priori. The parameters are frozen from the $K$-independent reference flow, which also repairs a pair-dependence of the compared models that broke the telescoping of §1.3 (new finding).
  - *Still open:* $R_\ell$ may differ from a theory's own value by a factor $L$.
  - The shooting argument and the continuity of $\Delta\beta$ in $d$ are no longer needed.
- **W2 (moderate).** R-S3 may not be in Bałaban. The printed count gives $\mu=L^{-(1-\beta)}$ per level-$n$ point for any $\beta>0$, not the heuristic $L^{-2}$. Here $\beta$ is independent of $\beta_E$: (3.67) has exponent $5-\beta$, and p.283 reads "with $1-\beta$, $\beta>0$, instead of $\beta<1$". This is the same family of rates as (2.43). The route needs only $\mu<1$ (corrected after r3).
- **N9 (minor–moderate).** $z^{(K)}_\ell\neq0$ and real $\delta m^{(K)}_\ell$ are needed at every level, which needs R-S1.
  - The statement concerns the scheme-specific ratio $W/\kappa^{(K)}$. Since $\kappa^{(K+1)}/\kappa^{(K)}\not\to1$ (there is an extra level), it says nothing about $W$ alone.
  - This is intended: $W/\kappa$ is the perimeter- and corner-renormalised loop.
- **Repaired:**
  - N1 (universality form, §4.4);
  - N2 (two-sided coupling system: D9's contraction, §4.5, given (C) and Lemma T; LIP-1 in CRE's setting);
  - N3 (norms, §4.4);
  - N5 (background-difference source, §4.5, given S3(iii-a) in family form);
  - N7 ((T-loop) in absolute form, §1.3);
  - N8 (rates, §4.5);
  - N10 (common $V$-domain, §4.4);
  - W7 (young levels, via $m_*$, §4.4).
  - Repaired after r2:
    - (2.43) used as a per-level contraction, replaced by creation-level bookkeeping (§3(b), §4.4, §4.5);
    - the classical difference kept exogenous (§4.4);
    - the first-order classical recursion, replaced by the sandwich (§4.3);
    - S3(iii), retyped (§4.3);
    - the normalisation by the exact scalar gas $Z_\ell(C)$, which includes V3's residual $E^\circ_{T,n}$ (§1.3);
    - fixed-range locality, replaced by localisation sums (§4.1);
    - the V3 diagnosis (§3(e), §4.1);
    - the large-field frequency argument, now a Markov lower bound (§3(g));
    - the corner index (§3(f));
    - the (3.68) index reading (§2);
    - the dressed-loop comparison (§4.2);
    - the complete condition list (§3, Conclusion; completed after r3).
  - Repaired after r3:
    - the normalisation $\kappa^{(K)}:=\mathcal W^{(K)}_0(C;1)$, with the gas split as a lemma (§1.3);
    - the target: $\sum_K\theta_K<\infty$, the weakest level-0 form as real sup bounds, the corner products and the polynomial rate (§1.3);
    - the model compared, N4, and the domains $D_\ell$, $D^{\mathbb C}_\ell$ (§0, §1.2);
    - §2: gauge invariance essential but not sufficient; (G1) Elitzur averaging and covariant objects; (G2) per-point counting; (G3) list, citations and notation; (G4) scope for $\mathrm{End}(V_\rho)$, the pressure, the periodicity conditions;
    - §4.4: untruncated universality, no frozen $\chi$, the shooting argument, the explicit classical input and booked remainders, relocalisation, the monotone $m_*$, named norms, (P-$\beta$) and (P-Y) with $\omega_g\delta^g$, (P-R), the room claim in variation form, $\rho\geq4S$ and the order of constants;
    - §4.5: the estimate steps behind linearity, the cross term, S3(iii-a) in family form, the finiteness premise, the young-level caveats, the $\mathbf R$-term bookkeeping, $C(L,\lambda')$, the loop under merging;
    - §4.6: S3(i) at age $K$ and the $\mathbf R$-terms in (T-act), the linear interpolation bound;
    - §5 dependencies; §6 W4/N4 (R-N4), W2, N6, N12, N14, N15, W5.

## 7. Review record

- **r1 round, launched 21 Oct 2026 at 11:25:17.** Three isolated CLI reviewers (claude-opus-5-5, xhigh, 3600 s), one part per packet:
  - `cr-a-target-20261021-r1`: §1–§3 (target, gauge invariance, count check);
  - `cr-b-s1s3-20261021-r1`: §4.0–§4.3 (S0–S3);
  - `cr-c-s4s6-20261021-r1`: §4.4–§6 (S4–S6, order, weak points).

  Packets: `verification/isolated_reviewer/build_cauchy_route_packets_20261021.py`. Launcher: `launch_cauchy_route_review_20261021.ps1`. Reports go to `verification/isolated_reviewer/reviews/<revision>/review.txt`.
- **Before dispatch.** The §4.2 bound was corrected: log exponent $a/2$, Cauchy normalisation by $\varepsilon_j$, distance factor $R_j$. The reading of $\square^{\sim n-j}$ in (3.68) was checked against the CRE p.284 transcription.
- **r1 results (all finished by 11:45:33).**
  - *`cr-a` and `cr-b` returned no report.* The isolated gateway refused a second model request:
    - `cr-a` broke after about 110k thinking tokens;
    - `cr-b` used the full 128k output tokens on thinking.

    Both packets were too broad. They were split for r2.
  - *`cr-c` returned a 423-line report, read in full.* Verdict: §4.4–§6 not viable as written, viable after restructuring. Findings:
    - S4's interpolation was ill-typed (N1), "constants doubled" was arithmetically too small, and the Cauchy step gave no factor $\|\Delta I\|$, so $\mathrm{Lip}=O(1)$;
    - S5 missed the two-sided coupling system (N2), the background-difference source (N5) and the rate condition $\mu<\lambda$;
    - the norms were wrong (N3), and the truncated model depends on gauge fixing (N4);
    - further points N6–N10;
    - ranking: W4 decisive, then W1, W3/W6, W5.
- **r1 repairs (21 Oct).**
  - §4.4 restructured: universality form, common $V$-domain, frozen parameters, reference representation with exogenous S3 sources, young levels via $m_*$, componentwise norms, the estimates (P-E), (P-$\beta$), (P-X), and the room claim as the core of R-S4.
  - §4.5: linearity of (2.43) checked on CRE pp.279–283 and RG1 (4.10)–(4.15), p.284; the transported difference split; the two-sided coupling system closed by a weighted norm; rates $\max(\lambda',\mu)$ and $\lambda_{\rm line}$.
  - §4.6, §5, §6 updated.
  - §1.3: (T-loop) in absolute form, common domain, rate.
  - §3(b), §3(d) and the conclusion aligned.
  - §0: notation for $\beta_E$.
  - From the discussion with the user, added before r2: the cluster class in §4.1 and the classical recursion in §4.3.
- **r2 round, launched 12:00:56, finished by 12:21:12.**
  - *`cr-a1` and `cr-c`: no report again.* `cr-a1` broke after about 102k thinking tokens; `cr-c` hit the 128k output cap.
  - *`cr-a2` (§3): 287 lines, read in full.* Verdict: viable as a plan for the pure small-field model; no fatal issue within §3.
  - *`cr-a2`, serious findings:*
    - **S1** (e) misreads V3. In the pure small-field model $E^\circ_\xi=E^\circ_{T,n}$ is a history-independent constant (the flat residual). The local per-bond form is V3 rem:next-step (3)(a), which is unproved. $E_{\rm def}$'s $\rho\varepsilon_1$ per bond is only an indicator. *Repair:* make the first-step local form the base case of R-S1.
    - **S2** (g) argues the wrong way: an upper bound on the cost gives no lower bound on the frequency. *Repair:* a Markov-property lower bound at the finest level (conditional probability $\geq ce^{-Cp_0^2}$ per link).
    - **S3** (b) and §4.5: (2.43) is not a per-level contraction, since its constant $E_1(\beta)$ is not 1. *Repair:* creation-level bookkeeping, with $n_m\leq C\omega C_1\sum_{m'<m}L^{-\beta_E(m-1-m')}n_{m'}+\dots$, closing when $\lambda>L^{-\beta_E}$ and $C\omega C_1/(\lambda-L^{-\beta_E})\leq\tfrac12$.
    - **S4** the conclusion's condition list must add R-S1, R-S2, R-S3 (with S3(iii)), the room claim, N6, the bookkeeping of S3, and S0.
  - *`cr-a2`, moderate and minor findings:*
    - **M1** keep the classical difference exogenous rather than inside $\widetilde{\mathbf E}$, or put its gradient effect into $s_m$;
    - **M2** the classical line source (S3(iii)) is the dominant line source, $O(\varepsilon_K)$ per bond at age 0, and is omitted from (e);
    - **m1** $\delta^g_K=O(\log\log K)$ unless (P-$\beta$) is also proved for $m<m_*$;
    - **m2** corner index fix: a remainder created at level $j$ has size $\tau_j^2$ and weight $L^{-2(j-\ell)}$;
    - **m3** the residual $E^\circ_{T,n}$ is not in $\kappa$ and must be carried;
    - **m4** in (3.68), $\log L^jL^{-n}$ reads $(n-j)\log L$, linear in the age;
    - **m5** the axial-gauge route gives $\mu\approx L^{-1}$, not $L^{-2}$, which suffices;
    - **m6** RG1 p.259's $V$-condition uses $\varepsilon_0$, not $\varepsilon_\ell$;
    - **m7** the aggregate $d_m$.
  - *`cr-a2` on the physical statement:* the printed (2.44) gives $\mathbf R$-terms no age factor (CRE p.283: $(L^jL^{-n})^4g_j^{\kappa_0}$ per level-$j$ point). From printed bounds the physical rate is therefore at best polynomial in $K$, about $(K\log L)^{-\kappa_0/2}$.
  - *`cr-b1` (§4.0–4.1): 267 lines, read in full.* Verdict: §4.1 viable as a plan after repairs; §4.0 does not serve general $G$ (W5). The cluster class, its gauge invariance, Schur and the scalar extraction are sound in form. The class as written was not closable, and the V3 diagnosis was wrong. Serious findings:
    1. fixed-range locality fails under a step (background and covariance are not finite range); repair by localisation sums;
    2. the V3 diagnosis: $E^\circ_\xi$ is a carrier function, a constant in the pure small-field model, so the first-step task is the pointwise cluster decomposition of $dN_1/d\rho_1$, through $E_{\rm def}$;
    3. covariance of the activities must be constructed (background-covariant propagators, or a matrix analogue of CRE p.259 (iii));
    4. W5;
    5. "remainders that belong to LF" made the statement conditional; repair by exact closure in the N4 model with named truncation terms;
    6. gap-transport composition (N12).
    - Minor: irreducible $\rho$; corner family infinite but summable; per-period averages; normalise by $Z_\ell(C)$; the single-bond formula; $\tau_\ell$ and the domain undefined; complex growth of gap transports; S2 for clusters; the $\delta m$ definitions of §1.3 and §4.1.
  - *`cr-b2` (§4.2–4.3): 255 lines, read in full.* Verdict: viable as a plan after repairs; no fatal issue within §4.2–4.3. The S2 exponents and counts were checked by hand (Schwarz lemma; $\alpha_{\rm line}=1$, $3$). Serious findings:
    1. "R-S3 needs no separate source" is wrong; repair by the exact two-sided sandwich;
    2. the first-order recursion was used where $c_{\rm cl}(0)=O(1)$;
    3. S3(iii) was ill-typed; repair by (iii-a) and (iii-b), the transport defects $\Delta_b$;
    4. S2's complexified domain was not stated;
    5. S2 omitted the cluster activities;
    6. the zero $F^2$ part was asserted without proof, but is closable at age 0.
    - Minor: index mixing in (3.68); (3.69) and (3.72) not needed; the cube $\square^{\sim n-j+1}$ is too small for the support; the dressed-loop comparison omitted terms; corner exponent; $L^{-2m}$ unsupported, $\mu=L^{-(1-\beta)}$; S2 should be given in weakest (one-step or rate) form.
- **r2 repairs (21 Oct, from 12:28).** All items of `cr-a2`, `cr-b1` and `cr-b2` above were applied or recorded as open, in the sections named in §6 under "Repaired after r2". New open items: N11–N14 and the R-S1 sub-items (a)–(e). Source facts checked on the transcriptions before use:
  - (3.68) first line (CRE p.284);
  - (3.67), (3.70) exponents (CRE pp.283–284);
  - "Sect. F [15]" (CRE p.283);
  - (2.26)–(2.28) with properties (i)–(iv) (CRE p.259);
  - RG1 p.256 (the residual gauge group, $u=1$ on $T^{(k)}$; "in the old only a background field is changed");
  - RG1 p.259 ($V$-condition with fixed $\varepsilon_0$).
- **Not yet reviewed after the r2 repairs (at that time):** §0–§2 (`cr-a1` failed twice) and §4.4–§6 (`cr-c` failed in r2; r1 reviewed the earlier version). Covered by r3.
- **r3 round, launched 12:39:03.** Four narrower packets cut from the r2-repaired draft by `build_cauchy_route_packets_20261021_r3.py`: `cr-a1a-target` (§0–§1), `cr-a1b-gauge` (§2), `cr-c1-s4` (§4.4) and `cr-c2-s5s6` (§4.5–§6), all `-20261021-r3`. Same model and settings, with a stronger budget instruction.
- **r3 results (all four returned by 12:53:15; each read in full).** Every verdict: viable as a plan, no fatal issue within the reviewed part.
  - `cr-a1a-target` (§0–§1):
    - serious: the normaliser was not defined independently of R-S1, hence $\kappa:=\mathcal W_0(C;1)$; and $\theta_K\to0$ is not enough, hence $\sum\theta_K<\infty$;
    - also: the weakest level-0 form; the corner products are $\exp(O((\log K)^{6p_0+1}))$; V3's coefficients are infinite-volume limits, so only products are compared; V3 conj:iteration's error is $(k+2)\tau^2$; the R-terms make the rate polynomial (N15); (T-act) needs S3(i) at age $K$.
  - `cr-a1b-gauge` (§2):
    - serious: "gauge invariance makes every difference age" is overstated. It is essential, but analyticity and localisation are needed too, and in the bulk the removal of $F^2$. On the line it is close to sufficient;
    - (G2) gives $O(1)$ per level-$n$ point before the subtraction;
    - minor: (G1) is false as stated (Elitzur averaging), and §4 uses covariant objects; (G3) has a wrong page, an incomplete list, an unsupported sentence and needs reflections for $\mathrm{tr}F\tilde F$; (G4) bullet 1 fails for $\mathrm{End}(V_\rho)$ ($G_2$, $\mathbf 7\otimes\mathbf 7$); $\delta m$ is the pressure; the periodicity is unsupported; $\pi_j$ is on pp.279/283.
  - `cr-c1-s4` (§4.4):
    - serious: the circular tolerance (D4), repaired by shooting; the room claim did not give $\omega$ (RM3), now in variation form; frozen $\chi$ is inconsistent with N4 (U2/D3); the norm domain was unbounded (N-e/SM2); the step around a non-critical background (R3/R4, C3(a));
    - minor: $\omega_g\delta^g$ in (P-$\beta$), (P-Y); the Cauchy constant $2S/\rho+2\omega$; the monotone $m_*$; $s_m$ and the $x$-norm; young-level parameters; $E_1'$ homogeneity.
  - `cr-c2-s5s6` (§4.5–§6):
    - serious: "no bootstrap" (now the finiteness premise with $\rho\geq4S$ and the shooting tolerance); the N4 re-run as a named open item (R-N4); W5; the R-terms (N15);
    - minor: the cross term $\beta^{(K+1)}_j[A^{\eta_{K+1}}-A^{\eta_K}]$; S3(iii-a) in family form; (T-act) needs S3(i) at age $K$; $\mu=L^{-(1-\beta)}$ with an independent $\beta$; the condition list; §5 dependencies; citations ((4.10)–(4.11) on RG1 p.283, (3.64) also uses (I.5.16)/(I.5.37), the remainder estimates); N12 as a semigroup; the loop creation levels under merging; $C(L,\lambda')$; the weakest level-0 form.
  - *On the user's remark that gauge invariance should be crucial* (`cr-a1b`, A9): it is essential, but not sufficient in the bulk. It legitimises per-step gauge fixing, excludes $\mathrm{tr}B^2$ and charge renormalisation of the line, kills zeroth and first orders at flat configurations, and lets the axial gauge express the field by the curvature. The aging also needs analyticity, localisation and, in the bulk, the $F^2$ subtraction. For the line, gauge covariance with analyticity and one-dimensional counting suffices once $Z_\ell(C)$ is extracted.
- **r3 repairs (21 Oct, after 12:53:15, finished by 13:10:41).** All items above were applied or recorded as open, in the sections named in §6 under "Repaired after r3". New open items: R-N4, N15, (P-R), the shooting continuity, the variation-form room claim, the family form of S3(iii-a), linearity of the estimates behind (2.43), and the loop creation levels under merging. Source facts checked on the transcriptions before use:
  - CRE p.254 (the general-step operations "left undefined, only their basic general properties are formulated");
  - CRE p.263 ((2.43) with $\beta_j(g_{j-1})A(\phi,U_k)$, "dependent on the other constants", (2.44), (2.45));
  - CRE p.280 ("replace the background configuration by the corresponding complex variables"; "coincides with a $U_n$-type");
  - CRE p.282 ((3.62), translation invariance and (I.4.15));
  - CRE p.283 ("(I.5.16), or (I.5.37)"; "with $1-\beta$, $\beta>0$, instead of $\beta<1$");
  - CRE p.284 ("works only if we have the representation (2.26)"; "The remaining arguments are as in the first proof");
  - RG1 p.259 ((0.31) and Theorem 2, existence of the bare coupling only);
  - RG1 p.283 ((4.10)–(4.11)) and p.284 ((4.13)–(4.15), "semisimple").
- **Lipschitz push (21 Oct, from 14:27; `WILSON_CAUCHY_LIPSCHITZ_2026_10_21.md`).** The Bałaban project's coupling-flow and difference results were imported, with their scope.
  - *Imported:*
    - `RG1_Thm2_REP` (`ONE_LOOP_PROOFS.md` §§2, 8);
    - D1, D2 (`DIFFERENCES_PLAN.md` §1);
    - D6a, D6b, D6, D_HOLO, D7, (E), (R), (C), D9 (`DIFFERENCES_PROOFS.md` §§2–3).
  - *Derived here:*
    - Lemma T (an a priori coupling tolerance, replacing the shooting argument);
    - Lemma G (global Lipschitz, dropping $\rho\geq4S$ and the finiteness premise);
    - Lemma H ($E_1'$ by linearity, under the class-wide reading of CRE Theorem 2).
  - *Corrected:*
    - (P-N), (P-$\beta$) and (P-R) are replaced by D9's system, which includes the R-feedback;
    - the rate is $(\log K)^{O(1)}(K+1)^{-2}$, not $K^{-\kappa_0/2}$.
  - *New findings:*
    - pair-dependent frozen parameters broke the telescoping of §1.3; repaired by the reference flow;
    - LIP-1: $C_\Lambda$ is a Cauchy constant on RG1's fixed domains and fails on CRE's (2.28).
  - *Source facts checked before use:*
    - RG1 p.264 (Theorem 3 with fixed $\varepsilon_0,\varepsilon_1,\alpha_0,\alpha_1$);
    - RG1 p.262 ((1.11)–(1.16));
    - CRE p.259 ((2.28), properties (i)–(iv));
    - CRE p.263 (Theorem 2 "Under the assumptions of Theorem 1").
  - *Status of the imports.* They are marked proved in the Bałaban registry. `reviews/REVIEW_LOG.md` has no entry for `DIFFERENCES_PROOFS.md`.
- **Not yet reviewed after the r3 repairs and the Lipschitz push:** all sections. The next round should again use one subsection per packet.

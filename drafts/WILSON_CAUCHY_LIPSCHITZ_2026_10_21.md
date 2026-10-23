# Lipschitz continuity of the RG step for the small-field Cauchy route

Written 21 Oct 2026, from 14:27. Companion to `WILSON_CAUCHY_ROUTE_DRAFT_2026_10_21.md` (the draft), sections 4.4–4.5. It takes the coupling-flow and difference results already proved in the Bałaban project, `D:\University\Oxford PostDoc\Balaban`, and states what the route can use, in which model, and what is still open. Bałaban is cited by page and equation.

## OPEN MATHEMATICAL GAPS

- **LIP-1 (analyticity domains; the main gap found here).**
  - *What is proved where.* The constants of the difference results are proved on RG1's fixed domains: RG1 Theorem 3 (p.264) has fixed constants $\varepsilon_0,\varepsilon_1,\alpha_0,\alpha_1$. These constants are the polarisation constant $C_\Lambda$ of ONE_LOOP_PROOFS Lemma 2.5, $B$ of D2, and $b$ of D9.
  - *The route's domains.* The route uses CRE's thresholds and domains, with $\alpha_{0,j}=g_jC_0(\log g_j^{-2})^{q_0}$ (CRE (2.28), p.259).
  - *What fails there.* A Cauchy bound on the polarisation then carries $\alpha_{0,j}^{-2}\propto g_j^{-2}$. So $b_j$ grows like $x_j=g_j^{-2}$, and D9 does not close (§5).
  - *Closes by* either:
    - (a) running the compared small-field model in RG1's fixed-constant setting (recommended, §5); or
    - (b) a bound on $\Delta\beta$ uniform in $\alpha_0$, from the Gaussian representation of $\Pi^{(j)}$ (the draft's C3).
  - *Adopted:* (a), in the hybrid form (RG1's fixed $\varepsilon_0,\alpha_0,\alpha_1,M,\kappa,\gamma$ with CRE's $\delta_k=g_kr(g_k)$). It is carried out in `WILSON_CAUCHY_LIP1A_2026_10_21.md`. Done there: H-1, the order of the constants, and H-2a (Lemma H-2a). Still open there: H-2b, the join to RG1's domains, and the R-terms.
- **LIP-2 (the N4 model).** Everything in §§2–4 is proved for Bałaban's model, whose cutoffs act on gauge-fixed fluctuations (RG1 (2.9)). In the N4 model it still needs:
  - the step bound (the analogue of RG2 (2.41)) and class-wide holomorphy, both part of R-N4;
  - (C) for the gauge-invariant indicators;
  - the cutoff part of D6a: a shell estimate for the plaquette variable near the threshold.
- **LIP-3 (class-wide readings).** Two statements are used class-wide:
  - CRE Theorem 2 ("Under the assumptions of Theorem 1", p.263) is read as holding for every E-term with the single-term properties of CRE p.259 (i)–(iv), with a bound $(1+\vartheta)E_0$;
  - D_CLASS / D_HOLO: the complexified class.

  The Bałaban project's `THEOREM_C_STATUS.md` §4 records the holomorphy behind D2 and D7 as "argued from the form of the expansions, not re-proved line by line".
- **Unchanged and still open:**
  - N6: the localisation scale $R_\ell$, which can differ by a factor $L$;
  - N15: the R-terms, now with the rate of §4;
  - the loop system: R-S1, R-S2 and (P-Y).

## 1. Sources and their status

| Item | Where | Content |
|---|---|---|
| RG1_Thm2_REP | ONE_LOOP_PROOFS.md §2 (Lemma 2.1, Rem. 2.3, Props 2.4, 2.6, Lemma 2.5), §8 (Thm 8.1, Cor. 8.2) | RG1 Theorem 2 for simple $G$: bare coupling, flow in $]0,\gamma]$, window bounds |
| D1 | DIFFERENCES_PLAN.md §1 | holomorphic and bounded by $M$ on $B(0,\rho)$ implies $4M/\rho$-Lipschitz on $B(0,\rho/2)$ |
| D2 | DIFFERENCES_PLAN.md §1 | small-field step Lipschitz in the history, with age weights |
| D6a, D6b, D6 | DIFFERENCES_PROOFS.md §2 | sensitivity to the coupling; uniqueness of the tuned bare coupling |
| D_HOLO, D7 | DIFFERENCES_PROOFS.md §3.2 | the step is holomorphic on the complexified class; full-step Lipschitz |
| (E), (R), (C), D9 | DIFFERENCES_PROOFS.md §3.4 | the coupled two-sided difference system and its decay |

- *Status.* All are marked proved in the registry (`sidecar/BalabanSidecar/RegistryNew.lean`, `RegistryChain.lean`). The project closed them on 2026-10-07 (`THEOREM_C_STATUS.md`, update after line 198). `reviews/REVIEW_LOG.md` has no entry for `DIFFERENCES_PROOFS.md`.
- *Lean.* The Lean pointers prove abstract cores: Schwarz, discrete Gronwall and the sequence lemma of D9. Bałaban's estimates enter as hypotheses.
- *Inputs from Bałaban (accepted):*
  - RG2 (2.14)–(2.41) (pp.9–21), with (2.22);
  - RG1 Theorem 3;
  - VAR Prop. 9 and (189)–(190); (189) is stated without proof (VAR p.308);
  - PRT1 and PBG, as listed in ONE_LOOP_PROOFS §9.

## 2. Coupling matching and the tolerance (replaces the shooting argument)

**2.1 What Corollary 8.2 gives, in route indices** (level $\ell$ = Bałaban step $K-\ell$, $x:=g^{-2}$). Let $G$ be simple and $g$ small. For every $K$ there is a bare coupling with:
- all $g^{(K)}_\ell\in\,]0,\gamma]$ and $g^{(K)}_0=g$;
- by Lemma 2.1 (i) with Remark 2.3,
$$|x^{(K)}_\ell-\bar x_\ell|\leq\delta\,\ell+C,\qquad\bar x_\ell:=g^{-2}+\bar b\,\ell,\qquad\bar b:=\tfrac{11}{24\pi^2}\kappa_G\ln L .$$

Here:
- $\delta=C_\Lambda C_3\varepsilon_1$ (Prop. 2.4). Every condition on $\varepsilon_1$ is an upper bound, so $\delta/\bar b$ can be made as small as wanted.
- $C$ comes from Theorem 8.1 and does not depend on $K$.
- The bare coupling is unique (D6: $x_0\mapsto x_K$ is strictly increasing).

**2.2 Lemma T (tolerance; derived).** For all $K$ and $0\leq\ell\leq K$,
$$\Bigl|\frac{x^{(K)}_\ell}{\bar x_\ell}-1\Bigr|\leq\tau:=\frac{\delta}{\bar b}+Cg^2,\qquad|x^{(K+1)}_\ell-x^{(K)}_\ell|\leq2(\delta\ell+C),\qquad\Bigl|\frac{x^{(K+1)}_\ell}{x^{(K)}_\ell}-1\Bigr|\leq\frac{2\tau}{1-\tau}.$$
*Proof.* $\bar x_\ell\geq\max(g^{-2},\bar b\ell)$, so $(\delta\ell+C)/\bar x_\ell\leq\delta/\bar b+Cg^2$. Theory $K+1$ satisfies the same window with the same $\bar x_\ell$, since its level $\ell$ is its step $K+1-\ell$. The last bound follows from the triangle inequality and $x^{(K)}_\ell\geq(1-\tau)\bar x_\ell$. ∎

$\tau$ does not depend on $K$ or $\ell$. It tends to $0$ when $\varepsilon_1$ is decreased (at fixed $L$) and then $g$.

**2.3 What Lemma T replaces.**
- *The shooting argument (draft §4.4).* It is not needed, and with it go the intermediate value theorem in $d$ and the open item "continuity of $\Delta\beta$ in $d$".
  - Each theory is fixed by its own matching (Corollary 8.2), uniquely (D6).
  - The tolerance that the shooting argument carried as an inductive hypothesis is Lemma T, a priori.
- *The draft's "[to check]" on a per-theory bound for $\beta_j-\beta_0$.* This is Lemma T. Theorem 8.1's window form replaces a pointwise limit of $b_k$, which is not needed.
- *W5, for simple $G$.* It closes in Bałaban's (RG1) model. In the N4 model it reduces to LIP-2: (P2) and (C) for the N4 step.

**2.4 Pair-dependent models (new finding) and the reference flow (repair).**
- *Finding.* The draft freezes $\varepsilon_\ell,R_\ell,\alpha_{0,\ell},\alpha_{1,\ell}$, the localisation domains and $D_\ell$ from the cutoff-$K$ coupling, for both theories of the pair $(K,K+1)$.
  - The cutoff-$(K+1)$ theory of the pair $(K,K+1)$ then carries $K$'s cutoffs.
  - The cutoff-$(K+1)$ theory of the pair $(K+1,K+2)$ carries its own.
  - These are two different models. The telescoping of draft §1.3 ($\sum_K\theta''_K$) needs consecutive differences of a single sequence of models, so it would need a third comparison for every $K$. r1–r3 did not raise this.
- *Repair.* Compute every frozen parameter from $\bar x_\ell$, which depends only on $g,L,\ell,G$. Then theory $K$ is one model in both of its pairs.
- *The parameters stay close.* By Lemma T, each theory's own parameters are within a factor $e^{\pm2\tau}$ of the reference values once $\log\bar x_\ell\geq2\max(p_0,q_0,q_1)$:
  - for $\varepsilon(x)=x^{-1/2}A_0(\log x)^{p_0}$, $|d\log\varepsilon/d\log x|=|{-\tfrac12}+p_0/\log x|\leq1$;
  - the same holds for $\alpha_{0,\ell}$ and $\alpha_{1,\ell}$.
- *Room.* Bałaban's conditions on $\varepsilon$ are upper bounds, plus the large-deviation conditions on $\varepsilon/g$ (RG2 pp.18–19; in CRE form $\exp(-\gamma_2p_0(g)^2/20)\leq\varepsilon_2$). A factor $e^{\pm2\tau}$ keeps both (D_CLASS room).
- *Still open.* $R_\ell$ is a power of $L$ (CRE (2.5)), so the reference $\bar R_\ell$ can differ from a theory's own $R_\ell$ by a factor $L$. This is still N6.
- In the fixed-constant setting of §5(a) no threshold depends on the level, and this subsection is void.

## 3. One-step Lipschitz bound in the input (the core of R-S4)

**3.1 Lemma G (global Lipschitz; from D1).** Let $S$ be holomorphic, with $\|S\|\leq M$, on the complex $\rho$-neighbourhood of a set $\mathcal C$. Then $\|S(I)-S(I')\|\leq(4M/\rho)\|I-I'\|$ for all $I,I'\in\mathcal C$.

*Proof.*
- If $\|I-I'\|<\rho/2$, apply D1 on $B(I,\rho)$; both points lie in $B(I,\rho/2)$.
- Otherwise $\|S(I)-S(I')\|\leq2M\leq(4M/\rho)\|I-I'\|$. ∎

*Consequence.* No premise that the differences stay inside the disc is needed. The draft's $\rho\geq4S$, its a priori $e_m\leq2S$, and the finiteness premise of draft §4.5 can all be dropped.

**3.2 Why the constant is small.** $M$ bounds the *new* terms of the step on the $\rho$-neighbourhood, not all the terms of the class.
- *In RG1/RG2.* The new E-terms are $O(1)C_3\varepsilon_1e^{-\kappa d}$ (RG2 (2.41), p.21).
  - $C_3=2(L+2)^4O(1)\cdot2E_0C_1\alpha_4^{-1}\alpha_6^{-1}M^qe^{C_2\kappa_1}$ is linear in $E_0$, so $M/E_0=C'\varepsilon_1$ with $C'$ independent of $E_0$ and $\varepsilon_1$.
  - With room $\rho=\vartheta_0E_0$ (D_CLASS, D_HOLO), $\omega:=4M/\rho=4C'(1+\vartheta_0)\varepsilon_1/\vartheta_0$.
- *D2 adds the history structure.* The new-term difference is at most $BE_0\sum_j\theta^{k-j}\|\Psi_j\|$:
  - $B=CC_3\varepsilon_1/E_0$;
  - $\theta=L^{-\alpha}$, from the factor $(L^j\eta)^5L^{4(k-j)}$ of RG2 p.8;
  - each input difference $\Psi_j$ is measured at its own creation scale.

  D7 extends this to the full step, through D_HOLO.
- *The r3 objection.* The draft's r3 objection (a value bound $S+\omega\rho$ gives $2S/\rho+2\omega\geq\frac14$) took $S$ to be the class bound of all terms.
  - The transported part is linear (re-evaluation at the new background) and is booked separately by aging (§3.3).
  - For the new terms, the variation-form claim holds with $\sup_{|w|\leq\rho}\|\mathbf N(I+we)-\mathbf N(I)\|\leq2M$, which is $\leq C\omega\rho$.
- *In CRE's setting.* The same argument gives $M/E_0\sim\varepsilon_k/\alpha_{0,k}=(A_0/C_0)(\log g_k^{-2})^{p_0-q_0}$, the Cauchy ratio of threshold to domain. This tends to $0$ if $q_0>p_0$ [to check on CRE pp.255–259; otherwise it is only small for $C_0/A_0$ large].

**3.3 Lemma H (homogeneity of (2.43) for differences; the draft's $E_1'$).**
- *Setting.* Let $\mathcal T_j$ be the aging map of (2.43), $F\mapsto\sum_z[F(\Lambda_j,U_k,z)-F(\Lambda_j,1,z)]-\Lambda_j(F)\,A(\phi,U_k)$. It is linear in $F$, since $\beta_j=\Lambda_j(F)$ is linear (CRE pp.279–283).
- *Hypothesis.* Assume (2.43) holds for every $F$ with the single-term properties of CRE p.259 (i)–(iv) and a bound $(1+\vartheta)E_0$ in (iv). This is the reading LIP-3.
- *Claim.* If $F,F'$ have these properties with bound $E_0$, and $d:=\|F'-F\|/E_0$, then
$$|\mathcal T_j(F'-F)|\leq\frac{2+\vartheta}{\vartheta}\,d\,E_1\sum_{n=j}^k(L^{j-n})^\beta|\Gamma_n\cap\Omega| .$$

*Proof.* For real $|s|\leq\vartheta/d$, $F+s(F'-F)$ has properties (i)–(iii), which are linear, and bound $(1+\vartheta)E_0$. Take $|s|=\vartheta/d$. Then $|s|\,|\mathcal T_j(F'-F)|\leq|\mathcal T_j(F+s(F'-F))|+|\mathcal T_jF|\leq(2+\vartheta)E_1\sum(\cdots)$. ∎

What this means for the draft:
- $E_1'=(2+\vartheta)E_1/\vartheta$ per unit relative creation size, whatever the dependence of $E_1$ on $E_0$ (p.263).
- Only real coefficients are used.
- The draft's R-S5 item "linearity of the *estimates* behind (2.43)" reduces to the reading LIP-3. No re-run of CRE pp.279–283 is needed.
- R-S5's "(2.43) in analytic polymer form on $D^{\mathbb C}_\ell$" is not needed.
  - The influence of old differences on new terms is D2's, which uses creation-scale analytic norms and RG2's age factor.
  - The real (2.43) is used only for the transported part, whose consumer at level 0 is a real sup bound (draft §1.3, weakest form).

**3.4 The coupling direction (D6a, D6b).**
- *D6a.* $\|E_{\rm fl}(g)-E_{\rm fl}(g')\|\leq\eta_E|x-x'|$ with $\eta_E=C(C_3\varepsilon_1/E_0)g^2$, and $|\Delta\beta|\leq\eta|x-x'|$ with $\eta=C_\Lambda E_0\eta_E$. The proof has two parts:
  - Schwarz on the disc of radius $Rg/4$ in a complex coupling, with $|g-g'|/g\leq4g^2|x-x'|$;
  - a shell estimate for the cutoff; large changes are handled by the trivial bound.
- *In the route.* The draft's $\omega_g(g_\ell)$ is $\eta_E(g_\ell)\leq C\varepsilon_1c_w\,\omega_\ell$, with $\omega_\ell=1/(n-\ell+1)$, using the window weights $g_\ell^2\leq c_w\omega_\ell$ (WINDOW_W, from Corollary 8.2). The draft had called it "plausibly small"; it is now derived, in Bałaban's model (LIP-2 for N4).
- *D6b.* It adds the earlier couplings, through the history.

## 4. The two-sided system (replaces the weighted estimate of draft §4.5)

**4.1 Dictionary.**

| Route | D9 |
|---|---|
| age $m$ | step $l$ (fine to coarse) |
| $n_m$ | $e_l$ |
| $r_m$ | $r_l$, with $S_l:=\sum_{m<l}r_m$ |
| $\delta^g_{K-m}$ | $\delta_l$ |
| the S3 sources $s_m$ | $s_l,\sigma_l\leq C_sr_0^l$ (D5) |
| top: level 0, matched | $n=K$, $\delta_n=0$ |

**4.2 The one-step estimates.** These replace the draft's (P-N), (P-$\beta$) and (P-R):
$$\text{(E)}\quad e_l\leq s_l+\eta\omega_l\delta_l+B\sum_{m<l}\theta^{l-m}e_m+B\,S_l,$$
$$\text{(R)}\quad r_l\leq\min(A'\omega_l^p,s_l)+A\omega_l^p\Bigl(\delta_l+\sum_{m<l}\theta^{l-m}e_m+S_l\Bigr),$$
$$\text{(C)}\quad\delta_l\leq\sum_{j=l}^{n-1}\Bigl[\sigma_j+\eta\omega_j\delta_j+b\Bigl(\sum_{m\leq j}\theta^{j-m}e_m+S_{j+1}\Bigr)\Bigr],\qquad b=C_\Lambda E_0\,O(B).$$

They differ from the draft in four ways:
- R-terms feed later E-terms ($BS_l$) and later R-terms ($AS_l$), conservatively without age decay. The draft's (P-N) had no R-input, and draft §4.5 left it "[to check]".
- The R-coefficient carries no $\omega$.
  - Lemma G against an R-input of room $\vartheta_0g^{\kappa_0}$ gives only $O(1/\vartheta_0)$. So R-differences are measured in absolute units, and their smallness is $Cg_l^{\kappa_0}\leq A\omega_l^p$ with $A\propto\gamma^{\kappa_0-2p}$.
  - The draft's (P-R) had $\omega e_m$.
- The coupling weights are $\eta\omega_l$.
- (C) is two-sided, because the two flows meet at the top.

**4.3 D9.** Let $0\leq\theta<r_0<1$ and $p\geq3$, with the contraction coefficients built from $B,\eta,b,A$ below 1. Then
$$\sum_{m\leq n}\theta^{n-m}e_m+S_{n+1}\leq C(n+1)^{1-p},$$
with $C$ independent of $n$ and linear in $C_s$.
- The proof is a contraction in a weighted maximum over all $l$. It needs no induction in age and no premise beyond the finiteness of a finite maximum.
- $\kappa_0\geq7$ allows $p=3$, since $A\propto\gamma$.

**4.4 Rate.**
- *Why the draft's rate goes.* The draft's §1.3 and §4.5 rate $(\log K)^{O(1)}K^{-\kappa_0/2}$ left out the feedback of the first point of 4.2. Its bound $e_m\leq C\lambda'^m$ is false once the floor $BS$ is present. That derivation is withdrawn.
- *What D9 gives.* The young levels enter through $C_s\lesssim2S\lambda'^{-m_*}=(\log K)^{O(1)}$ (draft §4.4). So $\theta_K\leq C(\log K)^{O(1)}(K+1)^{1-p}$ with $p=3$, which is summable. A sharper exponent is not derived.

**4.5 The loop.**
- The loop system is triangular: the bulk does not depend on the loop.
- Lemma G removes its finiteness premise. D9's bulk bounds enter (P-Y) as sources.
- The loop part is not in the Bałaban project and stays R-S1, R-S2 and (P-Y).

## 5. LIP-1 in detail: fixed versus shrinking domains

**Fixed versus shrinking domains.**
- *RG1.* RG1 Theorem 3 (p.264) holds with "positive constants … $\varepsilon_0$, $\varepsilon_1$, $\alpha_0$, $\alpha_1$" for every coupling sequence in $]0,\gamma]$. The domain $U^c_j(X,\alpha_0,\alpha_1,\gamma_0)$ is given by (1.11)–(1.16) (p.262).
- *CRE.* The E-terms are analytic on $U^c_j(X,\alpha_{0,j},\alpha_{1,j})$, with $\alpha_{0,j}=g_jC_0(\log g_j^{-2})^{q_0}$ (CRE p.259, (2.28)). The bounds (2.34)–(2.37) of p.261 also use $\alpha_{0,n}$.

**What changes on CRE's domains.**
- *The polarisation constant.* ONE_LOOP_PROOFS Lemma 2.5, step 2, uses a Cauchy radius $r$ "depending on $\alpha_0,\alpha_1$ only". On CRE's domains $r\propto\alpha_{0,j}$, so $C_\Lambda\propto\alpha_{0,j}^{-2}\propto x_j(\log x_j)^{-2q_0}$.
- *(P2) and D9.*
  - (P2) becomes $|\beta-b|\lesssim x_j(\log x_j)^{-2q_0}\,M$, which is not small.
  - In D9, $b_j\propto x_j$. Then $\delta_l\lesssim\sum_{j\geq l}x_j\varepsilon\sim(n-l+1)^2\varepsilon$, and the term $\eta\omega_l\delta_l$ of (E) is of order $(n-l+1)\varepsilon$, against $P^e_l=r_0^l+\varepsilon$. The system does not close with D9's weights.
- *The CRE remark in ONE_LOOP_PROOFS.* The remark after Proposition 2.6 (lines 226–230) moves Proposition 2.4 to CRE's threshold $\varepsilon_j=g_jp_0(g_j)$, but it does not account for (2.28). Not edited; it is a file of the Bałaban project.
- *What survives.* $\eta=C_\Lambda E_0\eta_E$, the sensitivity of $\beta$ to the coupling, stays polylogarithmically small, because the $g^2$ of $\eta_E$ cancels $\alpha_0^{-2}$. Only $b$, the sensitivity of $\beta$ to the activities, fails.

**Repair (a): the fixed-constant setting (recommended).** Take the compared small-field model in RG1's setting: fixed thresholds and domains, made gauge invariant as in N4.
- *What it gives.*
  - Lemma 2.5 holds with a fixed $C_\Lambda$, so (P2), Corollary 8.2, D2, D6a, D9 and Lemma T hold as proved, modulo LIP-2.
  - §2.4 becomes void: $D_\ell$ is the same for every $K$.
  - $\omega$ improves to $O(g\,r(g))$, not $O(g)$: the hybrid keeps CRE's cutoff $\delta_k=g_kr(g_k)$ (LIP-1(a) note §3).
  - Lemma T: $\tau=\delta/\bar b+Cg^2$ with $\delta=C_\Lambda C_3\gamma r(\gamma)$ tends to 0 with $g$ alone (LIP-1(a) note §3).
- *Costs.*
  - The young-level classical source is $c_{\rm cl}\varepsilon_0^2x_\ell$ per point, with RG1's fixed plaquette threshold $\varepsilon_0$ (not $\varepsilon_1$; LIP-1(a) note §3), instead of $c_{\rm cl}p_0^2$. So $m_*=O(\log K)$, and the young-level cost is $K^{c}$ with $c=\log(1/\lambda')/\log(1/\mu)<1$. Then $\theta_K\leq CK^{c}(K+1)^{-2}$, still summable.
  - The draft's uses of CRE (2.43), (2.44) and (3.68), and N15, must be re-read in RG1: the aging of RG1 p.258 and (0.29), and whether RG1's small-field model has R-type terms at all.
  - LF then joins a fixed-threshold small-field model to Bałaban's CRE-threshold large-field analysis. This is the REG-type comparison of R-N4, with a different threshold.
- *Check against V3* (`V3_RG1_FIXED_CONSTANTS_CHECK_2026_10_21.md`):
  - V3 cannot take RG1's fixed fluctuation cutoff (its cubic-order conditions fail).
  - V3 can take the fixed plaquette threshold, the domains, $M$, $\kappa$ and $\gamma$.
  - RG1/RG2 pass with CRE's cutoff $\delta_k=g_kr(g_k)$.
  - So (a) is to be read as RG1's fixed $\varepsilon_0,\alpha_0,\alpha_1$ with CRE's $\delta_k$. H-1 and H-2a are closed in the LIP-1(a) note. H-2b is open there.

**Repair (b): keep CRE's setting.** Prove $|\Delta\beta_j|\leq C(\sigma_j+\sum\theta^{j-m}e_m+S_{j+1})$ with $C$ uniform in $\alpha_{0,j}$, through the Gaussian representation of the flat second-order kernel (CRE (3.57), (3.63); RG1 (5.16)). This is the draft's C3, open.

## 6. Status

**Derived here:**
- Lemma T and the reference-flow repair of §2.4;
- Lemma G;
- Lemma H, given LIP-3;
- the dictionary and the corrected system of §4;
- the obstruction LIP-1.

**Imported from the Bałaban project:** RG1_Thm2_REP, D1, D2, D6a, D6b, D6, D_HOLO, D7, D9 (status in §1).

**Not done:**
- the N4 transfer (LIP-2);
- repair (a) of LIP-1, in progress in `WILSON_CAUCHY_LIP1A_2026_10_21.md`: H-1, the order of the constants and H-2a are done; H-2b, the join and the R-terms are open;
- repair (b), not pursued;
- the loop part.

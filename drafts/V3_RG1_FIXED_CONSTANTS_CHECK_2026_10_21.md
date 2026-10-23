# Can V3 use RG1's fixed constants? (check, 21 Oct 2026, from 15:09)

Question: can `WILSON_FIRST_RG_STEP_V3.tex` (V3) be run with RG1's fixed constants? This bears on LIP-1 repair (a) (`WILSON_CAUCHY_LIPSCHITZ_2026_10_21.md` §5).

Sources:
- RG1 and RG2 are read from `Balaban\tex\RG1\parts`, `Balaban\tex\RG2\parts` (`*_corrected.tex`).
- V3 is cited by line.
- Nothing in V3 or in the Bałaban files was edited.

## OPEN MATHEMATICAL GAPS

- **H-1 (RG1 with V3's cutoff).** RG1 Theorem 3 is to be run with the step-dependent fluctuation cutoff $\delta_k=g_kr(g_k)$ in place of the fixed $\varepsilon_1$.
  - Every use of $\varepsilon_1$ in RG1 and RG2 has been checked (§4), and all pass.
  - *Missing:*
    - the $C^\infty$ dependence on the coupling required at RG1 p.263 (lines 24–26), for this cutoff;
    - a re-reading of the Bałaban-project imports (RG1_Thm2_REP, D1–D9) with $\varepsilon_1\to\delta_k$.
- **H-2 (V3 with a fixed plaquette threshold).** V3's CRE imports (B1)–(B4) (L309–L313) are stated for CRE's $\varepsilon_1=g_1p_0(g_1)$. With a fixed threshold they have to be re-read (§3(b)).
- **R-S1(d)** (route draft): unchanged. Under (a) its target domain is RG1's fixed $U^c_1(X,\alpha_0,\alpha_1)$.

## 1. RG1's constants and how RG1 uses them

| RG1 constant | Role | Where |
|---|---|---|
| $\varepsilon_0$ | plaquette threshold of the small-field spaces $U_k(\varepsilon_0)$: $\lvert U(\partial p)-1\rvert<\varepsilon_0\eta^2$; at the first step, the restriction of the bare density | p.260 (lines 27–37), p.259, p.254–255 |
| $\varepsilon_1$ | fluctuation cutoff (2.9), $\lvert B'(b)\rvert<\varepsilon_1$ | p.266 |
| $\alpha_0,\alpha_1$ | analyticity domain $U^c_j(X,\alpha_0,\alpha_1)$ of the E-terms, "absolute constants" | p.262 (1.11)–(1.16), p.263 (1.18) |
| $M,\kappa,\gamma$ | cube size, decay rate, coupling bound $0<g_k\leq\gamma$ | p.264, Theorem 3 |

- *Units.* $B'=(1/i)\log V'$ is unscaled (p.265, line 34). After the scaling $B=g_kB'$ (p.267, line 30), the domain is $\{\lvert B\rvert<\varepsilon_1g_k^{-1}\}$ (RG2 p.9, line 40). So the rescaled cutoff radius is $\varepsilon_1/g_k$.
- *Method.* RG1 p.269 (lines 34–37) says the fluctuation action $\mathbf P^{(k)}$ is bounded by a second-order polynomial in $B$ with $O(\varepsilon_1)$ coefficients, and treats it as a small perturbation of the Gaussian quadratic form.
  - RG2 Lemma 2 (p.11, (1.42)–(1.43)) makes this precise: $\mathbf V_k(Y,B)=\frac12\langle Q(Y,B)B,B\rangle+\mathbf V_k''$, with $\lvert Q\rvert\leq C_3\varepsilon_1M^4e^{C_2\kappa_1}e^{-\dots}$.
  - The quadratic part is absorbed into the Gaussian (RG2 p.16, line 29).
  - The new terms obey $\lvert\mathbf E^{(k+1)}(X)\rvert\leq O(1)C_3\varepsilon_1e^{-\dots}$ (RG2 p.21, line 22).

## 2. V3's corresponding constants and method

| V3 | Value | Counterpart in RG1 |
|---|---|---|
| plaquette thresholds $\varepsilon_0,\varepsilon_1$ | $g_jp_0(g_j)$, CRE (2.4) (L1135–L1140) | $\varepsilon_0$ |
| fluctuation cutoff $\delta_0=g_0r$ | $r=A_1(\log g_0^{-2})^{p_0}$ (L1131, L572) | $\varepsilon_1$ |
| analyticity radii $\tau_L,\vartheta_*,\tau_{\rm b},\theta_0$ | fixed before $g_0$ (L3932, L4844, L1990) | $\alpha_0,\alpha_1$ |
| $M_1$; $\kappa$ | fixed before $g_0$; $M_1$ is CRE's "cube size of the previous papers" (L3932, L3938) | $M$; $\kappa$ |
| $R_1$ | CRE's growing scale, $R_1\geq(\log g_1^{-2})^{\mathfrak r}$ | none |

*Method.* V3 bounds every term on its cutoff box in sup norm:
- "Each regular vertex is bounded on its own cutoff by $Cg_0(1+r)^3$" (L1323);
- the host potentials are bounded by $C^\partial_0g_0(1+r)^3e^{-\kappa d_0(Y)}$, and the Mayer radius is $R_\Upsilon=\omega_*/(2C^\partial_0g_0(1+r)^3)$, which must be $\geq2$ (L3078, L2904, L3942);
- the thresholds appendix states that its estimates use only $r\to\infty$ and $g_0(1+r)^3\to0$ (L3932).

## 3. Constant by constant

### (a) The fluctuation cutoff $\varepsilon_1$: not usable

RG1's cutoff is $r=\varepsilon_1/g_0$, which gives $g_0(1+r)^3\geq\varepsilon_1^3/g_0^2\to\infty$. V3's own conditions with this $r$:

| V3 condition | Where | With $r=\varepsilon_1/g_0$ |
|---|---|---|
| item 3: $4C_{\mathsf C}g_0(1+2r)\leq\vartheta_*/2$ | L3936 | holds if $8C_{\mathsf C}\varepsilon_1<\vartheta_*/2$ |
| item 4(i): $a_{\rm bad}=c_{\rm n}\alpha_Gr^2/4$ large | L3937 | holds (better) |
| item 4(ii): $\omega_t=C_0g_0(1+2r)^3\leq\omega_*/2$ | L3937 | **fails**: $\omega_t\geq8C_0\varepsilon_1^3/g_0^2$ |
| item 4(iii): $C_0g_0(1+3r)^3\leq\min(1,\dots)$ | L3937 | **fails** |
| items 4(iv)–(v): $\rho_t=u_t/u_*$, $u_t=C'_\chi g_0(1+2r)$ | L3937 | hold if $\varepsilon_1$ is small |
| $R_\Upsilon\geq2$ | L3942, L3078 | **fails**: $R_\Upsilon\leq\omega_*g_0^2/(2C^\partial_0\varepsilon_1^3)$ |
| $v=u+2/(R_\Upsilon-1)\leq1$, $\rho=(u/u_*)^2+(u/u_*)v\leq\rho_{\rm pin}$ | L4453, L4482, L3049 | **fails** with $R_\Upsilon$ |
| $\tau=C[g_0(1+r)^3+e^{-cr^2}]<1$, $K_1^{s_*}\tau$ small, $C\tau^2L^4C_K\Phi_c\leq1$ | L122, L3942 | **fails**: $\tau\geq C\varepsilon_1^3/g_0^2$ |
| (c3-1-2): $C_Pg_0(1+2r)\leq\gamma/2$; (c5-7-T): $g_0(2+4r)<a_L$ | L3942 | hold if $\varepsilon_1$ is small |

- *Which conditions fail.* The conditions linear in $g_0(1+r)$ survive. Every condition of cubic order, $g_0(1+r)^3$, fails. These are the Mayer radius, the collar budgets, the marked-forest parameter $\tau$ and everything stated in terms of them: the coefficients of thm:main-theorem, $E^\circ$, and cor:main-factorisation.
- *V3's window.* V3's analytic estimates need a cutoff with $r\to\infty$ and $g_0r^3\to0$. RG1's cutoff, $r\sim g_0^{-1}$, lies outside it.
- *What using it would take.* V3 would have to replace its sup-norm bounds by Bałaban's relative bounds (RG2 Lemma 2): absorb $g_0s^3\leq\varepsilon_1s^2$ into the Gaussian. This affects the Mayer expansion, the walk, collar and forest estimates (Sections 4–5 and the appendices). That is a rewrite of V3's core, not a substitution.
- *Error size after such a rewrite.* With RG2's sup-type bounds the errors would be $O(\varepsilon_1)$, which does not tend to 0. RG2 p.8 (line 28) notes that using $g_k\lvert B\rvert$ in place of $\varepsilon_1$ gives a better bound; that variant is not carried out there.

### (b) The plaquette threshold $\varepsilon_0$: usable, with re-justification

Here V3's $\varepsilon_0,\varepsilon_1$ become fixed small constants, and $r$ stays as it is. Every place V3 uses $\varepsilon_1$ was listed in the earlier answer (handover, 15:09). The outcome:

- *Pure smallness, unchanged:*
  - $\widehat\mu=C_{L,R_c}\varepsilon_1<\min(\tau_L/2,\gamma_L/(4\max(1,c_L)))$ (L259, L3631);
  - $6c_{\rm h}s_{\mathfrak P}\varepsilon_1\leq r_G$ (L3608);
  - VAR's parameter $\alpha=K_\alpha\varepsilon_0\leq a_1$, $B_3\alpha\leq a_0$ (L4362);
  - item 5's $\varepsilon_0$ small (L3938).
- *Witness threshold* $\theta=\min(\varepsilon_0,\varepsilon_1/(4B_3N^{3/2}L^2),\delta_0/(2C_Q))$ (L2357, L4204). Its minimum is the $\delta_0$ entry, so $\theta\geq c_\theta g_0\pi_*$ and $q\leq e^{-c_*\pi_*^2}$ (L4316, L4324) are unchanged.
- *Hierarchy (B3)(i).* "$A_0$ sufficiently larger than $A_1$" (L312) is the ratio of plaquette threshold to fluctuation threshold, $\varepsilon_0/\delta_0=A_0/A_1$. With a fixed $\varepsilon_0$ it becomes $\varepsilon_0/\delta_0\to\infty$. The direction is right; CRE p.248 is to be re-read for this.
- *Comparison (B3)(ii).* $O(1)B_3e^{-\delta_{\rm c}LM_2R_1}\varepsilon_1\ll\delta_0$ (L570, L3938, L4391).
  - V3's justification, $\varepsilon_1/\delta_0\leq(1+\beta_0)A_0/A_1$ (CRE (2.8)), fails for fixed $\varepsilon_1$.
  - The condition itself still holds: $e^{-cLM_2R_1}\leq e^{-cLM_2(\log g_1^{-2})^{\mathfrak r}}$ with $\mathfrak r\geq2$ beats $\delta_0/\varepsilon_1\sim g_0(\log g_0^{-2})^{p_0}/\varepsilon_1$. This needs $R_1$ to keep CRE's growth.
- *Weaker:* the $E_{\rm def}$ term $e^{C_\chi n_C\rho(\varepsilon_1+e^{-cb/(LM)})}-1$ (L141). The per-bond size goes from $C\tau^2g_1p_0(g_1)$ to $C\tau^2\varepsilon_1$; it still tends to 0 through $\rho$.
- *Lost:* the area term $2{\rm Lip}_\chi c_{\rm h}(nL)^2\varepsilon_1$ of cor:main-leading-size (L193) becomes a fixed constant, so $\eta_n\to0$ fails. V3 rem:next-step (f) (L3258) already asks to replace it by $O(\tau^2)$. It is not an input to the route.
- *Sources (H-2):* (B1)–(B4) quote CRE at CRE's $\varepsilon_1$.
  - VAR Theorem 1 (behind (B1)) is a fixed-threshold result, and so is REG Lemma 1 (L309).
  - CRE pp.247–251 (behind (B1)–(B4)) is stated at CRE's thresholds.

### (c) The domains $\alpha_0,\alpha_1$: already of RG1's type

- V3's chart and joint analyticity radii are chosen before the coupling (L1990, "The common chart radius is fixed before the coupling"; L4844).
- V3 does not state its first-step output as E-terms on $U^c_1(X,\alpha_0,\alpha_1)$ with the bound (1.18). Doing so is R-S1(d), which is open in either setting.

### (d) $M$, $\kappa$, $\gamma$: same type

- RG1's $M$ is CRE's $M_1$, fixed before $g_0$ in V3 (L3932). $\kappa$ is fixed before $g_0$.
- RG1's $g_k\leq\gamma$ is V3's "$g_0$ below a threshold".

## 4. The reverse direction: RG1 with V3's cutoff

Set $\delta_k:=g_kr(g_k)=g_kA_1(\log g_k^{-2})^{p_0}$. This is CRE's $\delta_k$ in V3's normalisation (L1135–L1140). Use it in RG1 (2.9) in place of $\varepsilon_1$. Then:
- $\delta_k\leq\gamma r(\gamma)$, small for small $\gamma$;
- $\delta_k/g_k=r(g_k)\geq r(\gamma)$, large for small $\gamma$.

Every occurrence of $\varepsilon_1$ in RG1 and RG2, as a statement about the fluctuation cutoff:

| Place | Use | With $\delta_k$ |
|---|---|---|
| RG1 p.266 (2.9); p.267 line 2 | definition; $O(\varepsilon_1)$ on $B'(b_0(c))$ | definition |
| RG1 p.269 line 37; p.273 line 13; p.276 line 42; p.280 line 49 | "$\varepsilon_1$ sufficiently small" | holds |
| RG2 p.6 lines 54–60; p.7 lines 4–13 | $\lvert B'\rvert\leq C_1g_k\lvert B\rvert<C_1\varepsilon_1$; $e^{32\kappa_1}\varepsilon_1$ small; $4B_0C_1e^{16\kappa_1}\varepsilon_1\leq\frac14\alpha_2$ | holds |
| RG2 p.8 lines 24, 41; p.9 line 50; p.11 lines 2, 24; p.20 line 33; p.21 lines 7–22 | bounds proportional to $\varepsilon_1$ | smaller |
| RG2 p.9 line 40; p.12 line 19 | domain $\lvert B\rvert<\varepsilon_1/g_k$; $\chi^c_{k,P}$ | radius $r(g_k)$ |
| RG2 p.16 line 17 | $1/\lvert\tau(Y)\rvert\propto\varepsilon_1$ | cancels against $\lvert Q\rvert\propto\varepsilon_1$ in line 29 |
| RG2 p.16 line 42; p.18 (2.31) and line 48 | tails $e^{-\frac12\gamma_2(\varepsilon_1^2/g_k^2)\lvert P\rvert}$; $\frac1{20}\gamma_2\varepsilon_1^2/g_k^2\geq4\kappa$ | holds: $\frac1{20}\gamma_2r(\gamma)^2\geq4\kappa$ for small $\gamma$ |
| RG2 p.18 line 9; p.19 (2.33) and line 12 | $\varepsilon_2\leq1$; $e^{-\frac1{20}\gamma_2\varepsilon_1^2/\gamma^2}\leq\varepsilon_2$ | holds per step; see below |
| RG2 p.21 line 25 | $O(1)C_3\varepsilon_1\leq\frac12E_0$ | holds |

The last condition, step by step:
- $\varepsilon_2\propto\delta_k\to0$, so the step-uniform form $e^{-c r(\gamma)^2}\leq\varepsilon_2$ cannot be used.
- The factor in (2.33) is $e^{-\frac1{10}\gamma_2(\delta_k/g_k)^2M^{-4}\lvert Z_0\setminus Y_0\rvert}$, so it can be bounded at the actual $g_k$ by $e^{-c\,r(g_k)^2}$.
- With $p_0\geq1$, $e^{-cA_1^2(\log g_k^{-2})^2}=(g_k^2)^{cA_1^2\log g_k^{-2}}\leq\varepsilon_2$ for small $g_k$.

*Result.*
- Every use is an upper bound on $\varepsilon_1$, a lower bound on $\varepsilon_1/g_k$, or the per-step tail condition above, and all hold for $\delta_k$.
- The new terms are then $O(1)C_3\delta_k\to0$ (RG2 p.21).
- RG1 p.266 (lines 49–51) also says its inductive description covers a second, coupling-dependent cutoff. That cutoff is not V3's $r(g)$ and is not used here.

*Not checked (H-1):*
- RG1's $C^\infty$ dependence on $g_{j-1}$ (p.263, lines 24–26). RG1's own rescaled radius $\varepsilon_1/g_k$ also depends on $g_k$, so the mechanism is the same, but it has not been checked for $r(g_k)$.
- The Bałaban-project imports.
- The N4 transfer (LIP-2) with this tighter cutoff.

## 5. Verdict

1. V3 cannot take RG1's fixed fluctuation cutoff. Its Mayer, collar and forest conditions of cubic order fail (§3(a)).
2. V3 can take RG1's fixed plaquette threshold, domains, $M$, $\kappa$ and $\gamma$. The costs are re-justifying the (B3) conditions, the weaker $E_{\rm def}$ term, losing cor:main-leading-size's smallness, and re-sourcing (B1)–(B4) (H-2).
3. RG1 with CRE's fluctuation cutoff $\delta_k=g_kr(g_k)$ passes the check of every $\varepsilon_1$ use (§4).
4. So LIP-1 repair (a) is consistent with V3 in the form "RG1's fixed $\varepsilon_0,\alpha_0,\alpha_1,M,\kappa,\gamma$; CRE's $\delta_k$ at every step". The open items are H-1 and H-2.

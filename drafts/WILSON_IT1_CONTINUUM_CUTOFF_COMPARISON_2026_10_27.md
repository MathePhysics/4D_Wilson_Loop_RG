# Cutoff Comparison for the Continuum Wilson-Loop Expectation

27 October 2026. Separate continuation of `WILSON_IT1_CONTINUUM_LIMIT_CLOSURE_2026_10_26.md`, as requested. This work does not edit the existing note.

**Status.** This is a partial derivation, not a completed proof of full-sequence convergence. Sections 1–2 construct the exact two-cutoff comparison with its physical denominator and closed Wilson-loop insertions. Section 3 bounds the old centred action terms in a globally small-field geometry, including the polynomial tail of the R-terms. Section 5 proves a deterministic passage from a connection L² estimate and bounded curvature to a fixed Wilson loop, and controls the extra finest blocking step. Its proposed application still needs the uniform energy estimate (17); §5.5 identifies a scale loss in the cited lift argument. The recent fully marked RG comparison, including the large-field terms and selector changes, remains open. No new hypothesis below is claimed to have been proved for the full construction.

## 1. The Actual Two-Cutoff Comparison

Fix the physical torus, a square contour C from the admissible family, the blocking factor L, and the terminal coupling prescribed in the continuum note. Set

$$
\varepsilon_K=uL^{-K},\qquad k_K=K-j(C)\;.
$$

The stopping lattice, of spacing uL^{-j(C)}, is common to all runs. Let E_K be the positive bonds of the lattice of spacing ε_K, and let C_K be the fine-lattice representative of the same physical contour. Product Haar measures are normalised. Use exactly the bare density in the manuscript, including its vacuum scalar:

$$
\rho_{0,K}(U)=\exp\left(-g_{0,K}^{-2}S_K(U)-E_{\varepsilon_K}\right),\qquad
S_K(U)=\sum_{p\in\mathcal P_K}\left(1-\operatorname{Re}\operatorname{tr}_N U(\partial p)\right)\;.
$$

Here $g_{0,K}=g_0(\varepsilon_K,\bar g)$ is the prescribed bare coupling. Define the physical partition function and numerator by

$$
Z_K=\int_{G^{E_K}}\rho_{0,K}(U)\,\mathrm dU,\qquad
N_K(C)=\int_{G^{E_K}}W_\chi(C_K;U)\rho_{0,K}(U)\,\mathrm dU\;.
$$

Since the group is compact, the action is finite and continuous, and the bare density is strictly positive, 0<Z_K<∞. The scalar κ_K below is the original construction's product κ^{(k_K)}, including its perimeter and corner factors and any R-step contributions specified in D2.7. It is nonzero because it is an exponential. The target is

$$
F_K(C)=\frac{N_K(C)}{\kappa_K Z_K}\;.
$$

This notation abbreviates the full renormalised expectation. It does not remove the large-field terms or the remainder of the stopping-scale identity.

### A common lattice for the first comparison

Let M_K map fields at spacing ε_{K+1}=ε_K/L to fields at spacing ε_K. It is the manuscript's global Borel averaging map: the logarithmic average on its chart domain and the straight transport outside that domain. Its defining locations in V5 are `eq:bare-blocking-operator`, `eq:global-average` and `lem:global-average`.

The four measures below are on the same compact space $G^{E_K}$. Two are positive finite measures and two are finite complex measures:

$$
\begin{aligned}
\nu_K^-&=\rho_{0,K}(V)\,\mathrm dV,\\
\omega_K^-&=\kappa_K^{-1}W_\chi(C_K;V)\rho_{0,K}(V)\,\mathrm dV,\\
\nu_K^+&=(M_K)_*\left(\rho_{0,K+1}(U)\,\mathrm dU\right),\\
\omega_K^+&=\kappa_{K+1}^{-1}(M_K)_*\left(W_\chi(C_{K+1};U)\rho_{0,K+1}(U)\,\mathrm dU\right)\;.
\end{aligned}
$$

For example, for every bounded Borel function $h$ on $G^{E_K}$,

$$
\omega_K^+(h)=\kappa_{K+1}^{-1}\int_{G^{E_{K+1}}}h(M_KU)W_\chi(C_{K+1};U)\rho_{0,K+1}(U)\,\mathrm dU\;.
$$

This definition requires no density for the pushforward and no common representation of the two sets of large-field histories. Every insertion is the character of a closed contour. Gauge covariance of M_K and gauge invariance of the bare density and Wilson loop imply gauge invariance of all four measures. Their masses satisfy exactly

$$
\nu_K^-(1)=Z_K,\quad \omega_K^-(1)=Z_KF_K(C),\quad
\nu_K^+(1)=Z_{K+1},\quad \omega_K^+(1)=Z_{K+1}F_{K+1}(C)\;.
$$

These identities follow from the definition of pushforward, or equivalently from the normalisation of the group delta functions in the original T. They make no assertion that Bałaban's later R-operation preserves the law of the current coarse variables.

## 2. The Centred Cutoff Mark and the Denominator

For a positive field-independent number c_K, define the finite complex measure

$$
\mathcal H_K=\omega_K^+-c_K\omega_K^-
-F_K(C)\left(\nu_K^+-c_K\nu_K^-\right)\;.
$$

The scalar c_K allows the same vacuum factor to be removed from the numerator and denominator of the minus run. It does not change either expectation. By the mass identities above,

$$
\begin{aligned}
\mathcal H_K(1)
&=Z_{K+1}F_{K+1}(C)-c_KZ_KF_K(C)
-F_K(C)(Z_{K+1}-c_KZ_K)\\
&=Z_{K+1}\left(F_{K+1}(C)-F_K(C)\right)\;.
\end{aligned}
$$

Consequently the exact quantity that the marked comparison must estimate is

$$
\left|F_{K+1}(C)-F_K(C)\right|
=\frac{|\mathcal H_K(1)|}{Z_{K+1}}\;.
\tag{1}
$$

The term containing the denominator difference is essential. A bound on an unnormalised numerator alone does not prove (1). Nor does choosing c_K=Z_{K+1}/Z_K estimate the remaining numerator difference: that choice only cancels the mass of the denominator mark.

The first T-step is linear, so this comparison is an exact starting point for a marked expansion on the common ε_K lattice. Subsequent R-operations depend on the densities whose normalising quotients they use. One must compare the two actual constructions; there is no identity asserting that a single R acts linearly on \(\mathcal H_K\). The numerator must carry the observable through each operation with the same physical denominator as its corresponding vacuum construction.

The target is the integrated centred mark in (1). Its connected cancellations should be kept inside the gauge-invariant marked expansion. No estimate of the total variation of the full coarse law is assumed or obtained here.

For a comparison on the stopping lattice, the continuum note's exact identity is

$$
F_K(C)=e^{E_{\mathrm{const},k_K}}\mu_{\ell_0}^{[K]}(f_C)+r_K,\qquad
f_C(V)=W_\chi(C^{(k_K)};V)\;.
$$

Thus the same target is

$$
F_{K+1}(C)-F_K(C)
=\left[e^{E_{\mathrm{const},k_{K+1}}}\mu_{\ell_0}^{[K+1]}
-e^{E_{\mathrm{const},k_K}}\mu_{\ell_0}^{[K]}\right](f_C)
+r_{K+1}-r_K\;.
\tag{2}
$$

The relative-weight estimate in the continuum note controls the size of the large-field contribution to each r_K. At fixed terminal coupling that bound is independent of K, so it does not by itself estimate the difference in (2) by a summable sequence. The large-field part of the centred mark remains part of the target.

## 3. An Old-Scale Estimate That Can Be Completed

The geometric estimate quoted in the continuum note is CRE (2.43), for the centred E-terms. CRE (2.44) gives a different age dependence for the centred R-terms. They should be estimated separately.

The following calculation concerns a globally small-field geometry with Γ_n=∅ for n<k and |Γ_k|=N_s^4, and regular configurations in the domains of CRE Theorem 2. It is not an estimate of the sum over arbitrary large-field histories. Let \(\mathcal E_j^{[K]}\) be the complete expression on the left of CRE (2.43), with its F² counterterm subtracted, and let \(\mathcal R_j^{[K]}\) be the centred sum on the left of CRE (2.44). Take Ω to be the whole comparison torus. Then, pointwise on that regular domain,

$$
|\mathcal E_j^{[K]}|\leq E_1N_s^4L^{-\beta(k-j)},\qquad
|\mathcal R_j^{[K]}|\leq R_1N_s^4g_j^{\kappa_0}\;,
\tag{4}
$$

where 0<β<1 and κ₀≥7. These are the actual centred expressions; field-independent vacuum terms are not included in (4).

Use the pairwise running-coupling lower bound already used in D2.6 §5.0:

$$
g_{k-s}^{-2}\geq g_k^{-2}+bs-C_0\;,
\tag{5}
$$

with b>0 and C₀ independent of the cutoff. Its stated source is `ONE_LOOP_PROOFS.md`, Lemma 2.1 with Theorem 8.1 and Corollary 8.2. The applicability of that coupling input to the chosen construction remains a standing assumption here. Choose the small-coupling window so that A_K:=g_k^{-2}-C₀≥A_*>0, uniformly in K, and put p=κ₀/2.

For 1≤m≤k, summing (4) over j≤k−m gives

$$
\left|\sum_{j\leq k-m}\mathcal E_j^{[K]}\right|
\leq\frac{E_1N_s^4}{1-L^{-\beta}}L^{-\beta m}\;.
\tag{6}
$$

For the R-terms, (5) and a decreasing-series integral bound give

$$
\begin{aligned}
\left|\sum_{j\leq k-m}\mathcal R_j^{[K]}\right|
&\leq R_1N_s^4\sum_{s=m}^{\infty}(A_*+bs)^{-p}\\
&\leq R_1N_s^4\left((A_*+bm)^{-p}
+\frac{(A_*+bm)^{1-p}}{b(p-1)}\right)\\
&\leq C N_s^4(1+m)^{1-p}\;.
\end{aligned}
\tag{7}
$$

The constants depend on the fixed coupling window, group, L and the source constants, but not on K or m. Applying the same bounds in the two runs bounds the difference of their old centred E- and R-parts by twice the corresponding right-hand sides on any common regular coarse-field domain.

In particular, for all sufficiently large K one can choose m_K=⌊√K⌋≤k_K. Since p≥7/2,

$$
L^{-\beta m_K}+(1+m_K)^{1-p}
\leq C\left(L^{-\beta\sqrt K}+K^{-5/4}\right)\;,
\qquad
\sum_K\left(L^{-\beta\sqrt K}+K^{-5/4}\right)<\infty\;.
\tag{8}
$$

The constant absorbs the floor in m_K. This completes a summable old-tail estimate for the centred action components in (4). In contrast, choosing only m_K proportional to log K in (7) gives a bound of order (log K)^{1-p}, which is not summable over K. A logarithmic comparison window therefore needs an additional dynamical estimate; the geometric E-tail alone does not justify that choice for all action terms.

To use the growing window m_K in the full proof, the recent-step comparison would have to be uniform over that window. Its constants, the main classical action, the selectors, boundary terms, the marked insertion and the physical denominator still have to be controlled. Equations (6)–(8) do not establish those estimates.

## 4. Checking the Existing Difference Arguments Against This Target

### The small-field Lipschitz estimate

`WILSON_CAUCHY_LIPSCHITZ_2026_10_21.md` §3 derives a Cauchy estimate for a step as a function of its input activities on a common complex domain. This controls changes in two inputs to the same map. It does not estimate the difference between maps whose backgrounds, fine lattices, constraints and selectors differ. That difference is the depth source denoted s_l or σ_l in the earlier difference system; it cannot be removed by applying the Lipschitz estimate to equal activity lists.

The earlier note also distinguishes RG1's fixed-constant setting from the shrinking CRE domains. Its §5 and `WILSON_CAUCHY_LIP1A_2026_10_21.md` investigate that transfer. Nothing in this continuation identifies those different settings without their domain and cutoff checks.

### The proposed depth estimate

`Balaban/DIFFERENCES_PROOFS.md` §1 states a depth-convergence proposition D5. Its non-abelian residual argument is superseded by `Balaban/D5_ENERGY.md`, which explicitly identifies a non-decaying quadratic remainder in that argument.

The energy replacement gives estimates for averaged functionals, including translate-averaged loop fluxes, and states assumptions on regular lifts and coercivity. The Wilson insertion in (1) is a fixed closed contour. A bound for translate-averaged fluxes is not itself a bound for that fixed insertion, or for every complex marked activity in D(k). An application needs the precise transfer to those operands. Similarly, the proposed covariance and Gaussian-activity estimates must be applied with their specified carriers and norms; the recorded abstract resolvent and Cauchy lemmas do not verify those identifications.

These source notes are candidates for the missing depth estimate. They are not imported here as an established full marked-step comparison.

### The coupled difference recursion

`WILSON_CAUCHY_LIPSCHITZ_2026_10_21.md` §4 records a coupled forward/backward difference system and a polynomial decay estimate. The system assumes depth sources with geometric decay and controls history and coupling feedback. It supplies a propagation mechanism once those estimates are available. It does not prove the depth-source hypothesis for (1), and its §4.5 explicitly leaves the loop comparison outside the bulk result.

### The full-measure assembly

`Balaban/DIFFERENCES_PROOFS.md` §4 records a normalised-density assembly, including selector-shell and majorant estimates. Its final paragraphs explicitly say that the proposed assembly uses R_law, a law-preserving modification of Bałaban's R-operation. The present Wilson construction uses the original R with the observable carried through its numerator. Replacing it by R_law would require a separate equivalence and transfer argument and would change the current route. No such substitution is made here.

The first T-step comparison in §1 is legitimate because it uses the manuscript's original T. It does not extend the pushforward interpretation to later R-steps.

The version of the continuum note saved on 27 October at 01:14 adds a different assertion in (9.4)(a): that R merely rewrites ρ_k without changing it, so the two actual runs are compositions of T alone. CRE p.243 explicitly states that R changes effective densities on large-field regions and constructs the sequence by successive RT operations; LFR2 (1.104) displays Rρ_k, not an identity Rρ_k=ρ_k. Consequently that T-only chaining assertion cannot be imported for the current densities without an additional identity. Preservation of an integrated partition function would not establish equality of the densities as functions. This continuation keeps the original R operations and the corresponding marked numerator comparison.

## 5. A Fixed-Loop Estimate from the Energy Comparison

The proposed energy argument controls a bulk norm, whereas the observable is a fixed contour. A uniform curvature bound supplies a way to pass from that bulk norm to the fixed contour. This calculation concerns the actual closed Wilson character at real regular backgrounds.

### 5.1 The fields and the comparison norm

Work in four dimensions on a periodic lattice of physical spacing h. Fix a square contour C, whose physical perimeter is P(C), and a number r₀ smaller than one quarter of every torus period. Let X be a lattice subcomplex containing every translate C+z with z∈(hℤ)⁴ and |z|∞≤r₀. Whenever z and z+he_μ both lie in this translation cube, X also contains every plaquette, edge and vertex of the coordinate ladder joining C+z to C+z+he_μ, including its rungs. Only meshes for which C is a lattice contour are considered. The contour, torus, r₀ and physical neighbourhood containing X are fixed as h tends to zero.

Use a fixed finite-dimensional unitary representation π and the normalised character χ=(dim π)⁻¹Tr π. Matrix norms below are operator norms in this representation. Suppose U and V are two bond fields on X and their plaquettes satisfy

$$
\max_{p\subset X}\left\{\|\pi(U(\partial p))-I\|,
\|\pi(V(\partial p))-I\|\right\}\leq Mh^2\;.
\tag{10}
$$

Define the comparison distance by

$$
\mathfrak d_h(U,V;X)=
\inf_{g\in G^{\operatorname{Vert}(X)}}
\left(h^2\sum_{b\in E(X)}
\|\pi(U(b))-\pi(V^g(b))\|^2\right)^{1/2}\;,
\qquad V^g(b)=g(b_-)V(b)g(b_+)^{-1}\;.
\tag{11}
$$

Here E(X) contains each unoriented bond of X once, in a fixed orientation. The infimum is attained, since the finite product of gauge groups is compact. The quantity in (11) is invariant under independent gauge transformations of U and V: absorb them into g and use the unitary invariance of the matrix norm. The factor h² gives the physical L² norm of the connection difference in four dimensions, since a bond difference is of order h times a potential difference.

### 5.2 Fixed-contour transfer

For h≤r≤r₀ there is a dimensional constant C₄ such that

$$
|W_\chi(C;U)-W_\chi(C;V)|
\leq C_4P(C)\left(Mr+r^{-2}\mathfrak d_h(U,V;X)\right)\;.
\tag{12}
$$

**Proof.** First put V in a gauge attaining (11). Both Wilson characters and (10) are unchanged. Let

$$
S_{h,r}=(h\mathbb Z)^4\cap[0,r]^4\;,
\qquad |S_{h,r}|=(\lfloor r/h\rfloor+1)^4\geq(r/h)^4\;.
$$

Write the oriented bonds of C+z as b₁+z,…,bₙ+z, with n=P(C)/h. Telescoping the two matrix products *inside the normalised trace* expresses their difference as a sum of closed traced contractions

$$
\frac{1}{\dim\pi}\operatorname{Tr}\left(
U_1\cdots U_{i-1}(U_i-V_i)V_{i+1}\cdots V_n\right)\;,
$$

where the matrices are evaluated on the translated bonds. Each contraction is invariant under simultaneous gauge transformations of the two fields. Unitarity and the trace inequality bound it by ‖U_i−V_i‖. Reversing a bond does not change this norm. For each fixed b_i, the translated bonds are distinct, because r₀ is smaller than the torus periods. Therefore Cauchy–Schwarz gives

$$
\begin{aligned}
\frac{1}{|S_{h,r}|}\sum_{z\in S_{h,r}}
|W_\chi(C+z;U)-W_\chi(C+z;V)|
&\leq\sum_{i=1}^n
\left(\frac{1}{|S_{h,r}|}\sum_{z\in S_{h,r}}
\|U_i(z)-V_i(z)\|^2\right)^{1/2}\\
&\leq\frac{P(C)}{h}\frac{h}{r^2}\mathfrak d_h(U,V;X)
=P(C)r^{-2}\mathfrak d_h(U,V;X)\;.
\end{aligned}
\tag{13}
$$

Next translate C by coordinate lattice steps. Between C and C+z the ribbon contains at most n|z|₁/h plaquettes, counted with multiplicity. Expanding the ribbon holonomy as an ordered product of transported plaquettes and telescoping inside the trace gives

$$
|W_\chi(C+z;U)-W_\chi(C;U)|
\leq\frac{P(C)|z|_1}{h^2}\max_p\|\pi(U(\partial p))-I\|
\leq MP(C)|z|_1\;.
\tag{14}
$$

Conjugation by the connector from the old base point to the translated base point disappears inside the trace. Thus this estimate uses only closed gauge-invariant quantities. The same bound holds for V. Since |z|₁≤4r, averaging the triangle inequality and using (13) proves (12), with for example C₄=8. ∎

The averaging in this proof is a deterministic estimate at fixed U and V. It uses no translation invariance or independence of the probability law.

### 5.3 Consequence of a depth-energy estimate

Suppose, uniformly over the coarse data and the real regular domain under consideration,

$$
M\leq M_0,\qquad
\mathfrak d_h(U,V;X)\leq D_0h^\sigma,
\qquad 0<\sigma\leq3\;.
\tag{15}
$$

For sufficiently small h choose r=h⌈h^{σ/3}/h⌉≤2h^{σ/3}≤r₀. Equations (12) and (15) give

$$
|W_\chi(C;U)-W_\chi(C;V)|
\leq C_4'P(C)(M_0+D_0)h^{\sigma/3}\;.
\tag{16}
$$

In particular, the input σ=β/2 from a local energy comparison gives exponent β/6. The energy-to-distance passage that must be verified is explicit. If, in an admissible relative gauge, V^g(b)=exp(iδ_b)U(b), then

$$
\mathfrak d_h(U,V;X)^2\leq h^2\sum_{b\in E(X)}\|\mathrm d\pi(i\delta_b)\|^2\;.
$$

Thus the energy route supplies (15) only after its unit-block Poincaré estimate and local energy bound have established

$$
h^2\sum_{b\in E(X)}\|\mathrm d\pi(i\delta_b)\|^2
\leq C_X\varepsilon_1^2h^\beta\;.
\tag{17}
$$

The constants may depend on the fixed physical neighbourhood X and representation, but must be independent of the mesh and cutoff. This writes the input in the physical units required by the Wilson-loop estimate; a bound for an unspecified unweighted bond norm cannot be substituted for (17).

### 5.4 The extra finest blocking step

The energy route compares Q₁U^{(d+1)} with U^{(d)} on the coarser of the two microscopic meshes. The target also contains the original loop in U^{(d+1)} on the finer mesh. This additional comparison has a direct curvature estimate.

In this subsection lengths are measured in units of the prescribed coarse spacing, so that the coarse data for the variational problem live on a lattice of spacing one. Put h=L^{-d}, with d the reconstruction depth and the dimension still four. Let \(\widetilde U\) have spacing h/L, and set W=Q₁\widetilde U, where Q₁ is the original one-step averaging map M of §1. The fine comparison domain is the subcomplex induced on the union of all fine L-blocks centred at the vertices of X: it includes every fine edge and plaquette whose vertices lie in that union, including those crossing block interfaces. In particular it contains the interfaces between the four blocks around every coarse plaquette of X. For a coarse bond b, let P_b be the straight fine transport between its block centres. The meshes and contours are aligned so that C_{h/L} is the concatenation of these paths along C_h. On the regular chart,

$$
W(b)=e^{i\beta_b}P_b\;.
$$

Here the fine plaquette bound is imposed throughout this enlarged fine domain, in the original faithful matrix representation used to define the logarithm chart: its bound is M(h/L)². The averaging formula is `WILSON_FIRST_RG_STEP_V5.tex`, `eq:nonlinear-average`, or RG1 (0.4). Its logarithm β_b is a convex average over x in the initial block and shortest coordinate paths from each block centre to x and its translate x′. The corresponding closed path consists of these two paths, the straight path [x,x′] and the reverse of the straight centre-to-centre path. Thus it lies in the union of the two L-blocks of b and has length bounded by a constant times L. This union is a lattice box. Coordinate-path deformations and cancellation of reversed steps within that box fill the loop with at most c_fill L² fine plaquettes, where c_fill is an absolute constant in dimension four. The ordered plaquette expansion gives a bound c_fill Mh² on the loop's distance from the identity in the faithful norm. For sufficiently small h it lies in the fixed logarithm chart. The convex average defining β_b and the smoothness of π near the identity therefore give

$$
\|\pi(W(b))-\pi(P_b)\|\leq C_{G,\pi,L}Mh^2\;.
\tag{18}
$$

For any g∈G, ‖π(g)−I‖≤c_{G,π}‖g−I‖_faithful: this follows from the smooth local logarithm near the identity and from compactness away from it. The straight transport around a coarse plaquette is filled by its L² planar fine plaquettes. Its faithful-norm deviation from the identity is at most Mh², and the four averaging corrections contribute at most C Mh². After conversion to π, W therefore satisfies (10) with curvature constant C_{G,π,L}M. Telescoping along the closed contour, again inside the character, gives

$$
|W_\chi(C_{h/L};\widetilde U)-W_\chi(C_h;Q_1\widetilde U)|
\leq C_{G,\pi,L}MP(C)h\;.
\tag{19}
$$

For the application, fix one real coarse field V with every coarse plaquette deviation below ε₁≤a₁, as in VAR (7). At each reconstruction depth n=d or d+1, take Ω_j to be the whole fine torus for 0≤j≤n, Λ_j empty for j<n, and Λ_n the whole prescribed unit lattice. Let U^{(n)}(V) be the VAR minimal configuration for these data, so its only prescribed average is Q_nU^{(n)}=V. VAR (2) and Theorem 1 (8) give curvature constants M≤c₀ε₁ for U^{(d)} on X and for U^{(d+1)} on the enlarged fine domain, because the regularity scale is L^nη=1. Changing between the fixed matrix norms only changes c₀. This does not provide the same uniform bound on arbitrary earlier-scale regions of a large-field history.

Choose h₀≤1 small enough that 2h₀^{β/6}≤r₀ and c_fill c₀a₁h₀² lies inside the fixed logarithm neighbourhood. For h=L^{-d}≤h₀, the energy estimate (17) for \(Q_1 U^{(d+1)}(V)\) and \(U^{(d)}(V)\), uniformly for these same coarse data, would give

$$
|W_\chi(C_{h/L};U^{(d+1)})-W_\chi(C_h;U^{(d)})|
\leq C_*\varepsilon_1 h^{\beta/6}\;.
\tag{20}
$$

Here C_* depends on C, its fixed neighbourhood X, r₀, G, π, L, β, c₀ and the constant C_X in (17), but not on d or the coarse data in this range. We used h≤h^{β/6} for 0<h≤1 and 0<β<1. At the stopping scale of §1 these coarse units have physical length a=uL^{-j(C)}, the depth is d=k_K=K−j(C), and h=ε_K/a=L^{-d}. Thus the proposed rate is geometric, and hence summable, for all sufficiently large K. The finitely many K with h>h₀ are not included in (20) and are not needed for a Cauchy bound on the tail.

The two terms in (20) are the background insertions for the K+1 and K runs at the same V on the stopping lattice: respectively W_χ(C;U_{k_K+1}(V)) and W_χ(C;U_{k_K}(V)), represented on their two fine meshes. This is a comparison across cutoffs, not a telescope from depth zero to k_K within one run. These are the classical insertions f in the continuum note's stopping identity; their measures and fluctuation remainders also vary with K. Equation (20) does not compare those measures, selectors, large-field histories or complex marked activities. It remains conditional on (17).

### 5.5 The lift input still needs a uniform estimate

The energy proof cannot be used solely because it is labelled a proof. Its input (I2) invokes the one-step minimal lift to supply the C^{1,β} regularity needed by its consistency estimate (I1). VAR Theorem 1 (9) must be read with that lift's actual scales.

VAR is written with terminal coarse spacing one. Rescale its lengths by h; in four dimensions the Wilson action is unchanged by this change of physical units. For a one-step lift whose coarse spacing is h, the fine spacing is h/L. Taking j=1 in (9), the physical regularity scale is h. If the coarse plaquette bound is Mh², the theorem's dimensionless input parameter is of order Mh². The physical potential and its first derivative are h⁻¹ and h⁻² times their unit-coarse-scale values. For any fixed permitted cube-size factor in VAR (distinct from the curvature constant M here), its stated bounds therefore have the sizes

$$
|A|\lesssim Mh,\qquad
|\nabla A|\lesssim M,\qquad
\|A\|_{1,\beta}\lesssim Mh^{-\beta}\;.
\tag{21}
$$

These are local gauges on cubes of size proportional to h, as specified immediately before Theorem 1. They do not themselves give a common gauge with a unit-scale C^{1,β} constant independent of h. Substituting the last bound of (21) into an h^β consistency estimate loses its small factor. This does not disprove a sharper lift estimate for smoothly varying coarse data. It identifies the additional estimate that the proposed application of (I2) must prove, rather than infer from the one-step form of (9).

The next analytic task within the energy route is therefore to construct or estimate the exact constrained fine lift of the smooth coarse competitor, with a uniform regularity constant on fixed physical neighbourhoods and a localised action-consistency error tending to zero. The same issue occurs for the local competitor G₂=U^{(1)}(A₂) in D5_ENERGY, E2(ii).

VAR (44)–(55) supplies an analytic correction of the nonlinear averaging constraint through A=A′−HD(A′). Its bounds (46), and the Hölder kernel bound PBG (3.133), retain the factors of the scale L^jη. Applying this correction at the one-step scale h does not by itself remove the loss in (21). An application must start with a suitably smooth fine interpolant and estimate its actual averaging defect before applying H. No such interpolant or defect estimate has been constructed here.

The Poincaré input must also retain its gauge condition. PBG (3.26) defines Δ_a=Δ+DRD*+Q*aQ, and (3.110) imposes both QA=B and RD*A=0. The extra quadratic terms disappear for a tangent variation only when QA=0 and RD*A=0; zero block averages alone do not remove the gauge directions. For the finite relative logarithm in (17), equality of the nonlinear averages gives a nonlinear constraint defect, not QA=0. A use of the tangent estimate must bound that defect in the physical L² norm and retain the boundary conditions. The corresponding estimate on the shells in D5_ENERGY E2 needs its own justification. No such transfer is asserted here.

Until these energy hypotheses are verified, (20) remains conditional on (17). The fixed-loop transfer (12)–(19) supplies the subsequent passage once those inputs are available.

### 5.6 Local action consistency for the actual one-step minimal orbit — candidate under review

This calculation addresses the action error of the lift itself. It does not infer a unit-scale Hölder bound from (21). The proposed replacement is a local affine comparison, using the small dimensionless parameter of the one-step problem and exponential decay at that problem's scale h. The claim below is not yet accepted as an input to (17).

#### The invariant quantity and the constraint

Let η=h/L. Let A_h be a coarse group-valued bond field on the periodic h-lattice, with every plaquette deviation at most εh² in the fixed faithful representation. Fix 0<β<1. On a fixed physical neighbourhood of a unit cube B, assume the local regularity supplied by VAR (9): there is a gauge in which A_h(b)=exp(ih a_μ(x)), with the supremum norms of a and its first physical finite differences, and the β-Hölder seminorm of those differences, bounded by Cε. The constant and neighbourhood are independent of h. Assume 0<ε≤ε_max, with ε_max fixed. The fine and coarse lattices and the cube B are aligned.

Let L_h(A_h) denote the actual one-step minimal orbit of VAR for the original constraint M F=A_h, on the fine η-lattice. Its dimensionless input parameter is O(εh²). For a representative F of this orbit define

$$
e_{h,B}(A_h)=
\sum_{\substack{x\in B\cap T_\eta\\\mu<\nu}}
\left(1-\operatorname{Re}\operatorname{tr}_N F(\partial p_{\mu\nu}^\eta(x))\right)
-\sum_{\substack{y\in B\cap T_h\\\mu<\nu}}
\left(1-\operatorname{Re}\operatorname{tr}_N A_h(\partial p_{\mu\nu}^h(y))\right)\;.
\tag{22}
$$

The half-open cube B partitions plaquettes by their base vertices; their other vertices may lie outside B. Both sums retain the closed plaquette traces. The candidate estimate is

$$
|e_{h,B}(A_h)|\leq C\varepsilon^2 h^{\beta/2}|B|\;.
\tag{23}
$$

Here |B| is physical volume. The constants may depend on the group, L, β and the stated local regularity constant, but not on h, the torus volume or the particular coarse field. The assertion is for sufficiently small h, with the threshold uniform under the stated bounds.

The quantity (22) is gauge invariant before any estimate. If s is a coarse gauge transformation, extend it arbitrarily to the fine vertices. Gauge covariance of M maps the fibre M F=A_h bijectively onto the fibre M F=A_h^s. It preserves the regularity conditions and the action. Uniqueness of the minimal orbit therefore identifies L_h(A_h^s) with the transformed orbit. Different extensions agree at coarse vertices and give the same orbit. Every local plaquette trace is unchanged, so e_{h,B}(A_h^s)=e_{h,B}(A_h).

There is a distinction between this statement and a statement about Landau coordinates. REG p.81 explicitly says that its Landau-gauge image is not contained in the original fixed-average fibre. The constraint becomes REG (1.31), or VAR (20), with the modified averaging function Q(U₀,ηA). VAR Proposition 2 supplies the return to an axial representative in the original fibre. Below the orbit L_h(A_h) is fixed first. Landau coordinates are used to estimate its local plaquette action, which is unchanged by that return; no equality M(exp(iηA)U₀)=A_h is asserted in those coordinates.

#### An affine field in a shrinking neighbourhood

Fix a coarse vertex y₀ in B and use the local regular gauge on a neighbourhood of y₀. Translate y₀ to zero. The further coarse gauge s(y)=exp(i∑_μ y_μ a_μ(0)) makes the four outgoing bonds at zero equal to the identity. Its derivatives are bounded in the fixed physical neighbourhood, so the transformed logarithmic potential, still denoted by a, satisfies the same C^{1,β} bounds up to a fixed constant, with a_μ(0)=0.

Let R≥1 be a sufficiently large integer multiple of the fixed block constants in VAR. We will take R proportional to log(1/h). On a cube of radius 8Rh, the discrete Taylor estimate gives, with b_{μν}=∂_ν^h a_μ(0),

$$
\left|a_\mu(y)-\sum_\nu b_{\mu\nu}y_\nu\right|
\leq C\varepsilon(Rh)^{1+\beta},\qquad
|b_{\mu\nu}|\leq C\varepsilon\;.
\tag{24}
$$

Define an affine fine potential and its group field by

$$
a^{\mathrm{aff}}_\mu(x)=\sum_\nu b_{\mu\nu}x_\nu
-\frac{h-\eta}{2}b_{\mu\mu},\qquad
F^{\mathrm{aff}}(x,x+\eta e_\mu)=\exp(i\eta a^{\mathrm{aff}}_\mu(x))\;.
\tag{25}
$$

The correction in (25) is determined by the actual averaging formula. At its linear part, the translated connector paths cancel after averaging. The centred offsets have mean zero. For an affine potential a^{aff}, the resulting coarse logarithm is exactly

$$
h a^{\mathrm{aff}}_\mu(y)
\frac{h(h-\eta)}{2}b_{\mu\mu}
=h\sum_\nu b_{\mu\nu}y_\nu\;.
$$

Indeed, the straight fine path contributes η∑_{j=0}^{L-1}a^{aff}_μ(y+ηn+jηe_μ); the difference of the two connector averages is linear in the centred offset n and has mean zero. This argument applies to the manuscript's averages over coordinate-path orderings as well as to a fixed translated ordering.

All words in the one-step formula have length bounded in terms of L. On this cube each individual exponent is O(εh²R). Expanding the closed relative word M(F^{aff},b)exp(−ih∑_νb_{μν}y_ν) through its linear term therefore leaves O(ε²h⁴R²). Together with (24), this gives, in the common coarse frame,

$$
\left|\log\left(A_h(b)M(F^{\mathrm{aff}},b)^{-1}\right)\right|
\leq C\left(\varepsilon h^{2+\beta}R^{1+\beta}
+\varepsilon^2h^4R^2\right)\;.
\tag{26}
$$

The relative word is closed at b₋. Its logarithm transforms by conjugation when the two fields are transformed together. The estimate is not assigned to an open transport.

The force of the affine reference is also small. Write J_aff=η⁻² Im D_{F^{aff}}^{η*}∂F^{aff}, as in VAR. The linear plaquette term is the constant η²(b_{νμ}−b_{μν}), whose ordinary divergence vanishes. The remaining plaquette terms have size at most Cε²η²h²R². Applying one fine difference costs at most C/η; the covariant-transport correction to the constant term is at most Cε²hR. Since η=h/L,

$$
|J_{\mathrm{aff}}|\leq C\varepsilon^2 hR^2\;.
\tag{27}
$$

This force and its norm are covariant and invariant, respectively, by REG (1.11).

#### A regular reference field agreeing with the affine field near y₀

The actual one-step minimum F has the weak bounds of VAR (9)–(10) on a cube of radius 8Rh: in a local gauge its fine potential has sizes CεhR, CεR and CεR/h for the potential, first differences and the two second-order operators, respectively. These are only the one-step bounds. Their use is permitted because R≤M(O(εh²)) for the logarithmic choice of R and sufficiently small h.

The coarse average of this local representative and the coarse field in the gauge of (24) have bond logarithms bounded by Cεh²R. Their coarse gauge transition can be normalised to the identity at y₀. Along each coarse bond its increment is at most Cεh²R, so on the cube its distance from the identity is at most Cεh²R². Take its logarithm and extend it to the fine vertices by multilinear interpolation on the coarse cells. Exponentiation gives a fine gauge transformation agreeing with that transition at the coarse vertices. Its first three fine differences are bounded by CεhR², CεR² and CεR²/h, respectively; these bounds follow even from the supremum bound on the logarithm, since η=h/L. Thus F can be put in a local gauge compatible with (24), with bounds of these same polynomial sizes.

In this gauge interpolate its logarithmic potential to (25) with a smooth spatial cutoff: use F^{aff} within radius 4Rh and F outside radius 6Rh. The cutoff is supported in the local gauge patch and is zero on its outer collar, so this defines an actual global group field F₀ agreeing exactly with F outside the patch. The discrete product rule, the preceding bounds and the second-order bounds of VAR show that F₀ satisfies VAR (14) and the PBG regularity hypotheses at the one-step scale h with dimensionless parameter

$$
\delta_h=C\varepsilon h^2R^{12}\;.
\tag{28}
$$

The exponent 12 is a fixed overestimate: the gauge transition costs at most R², the cutoff products only first and second derivatives, and the group product and logarithm are evaluated in one fixed chart. Increasing the fixed constant C absorbs their finitely many products. In particular the global force bound is Cδ_h h⁻³ and the global coarse mismatch is Cδ_h. Near y₀ the sharper bounds (26)–(27) apply. The reference equals the actual minimum elsewhere; its dependence on that minimum is harmless for a deterministic estimate using uniform bounds.

This construction does not select a preferred gauge orbit representative for the physical observable. Under a gauge change of A_h, transport the chosen local gauge by the inverse transformation. The coordinate construction is then identical, and F₀ is transformed with F. All relative coarse words, forces and covariant derivatives used in the comparison transform at their base points; their matrix norms are invariant. The final quantity remains (22).

#### The local comparison from VAR's equation

Apply VAR's reduction about the regular reference F₀. Its actual source is B= (1/i)log(A_h(MF₀)⁻¹), since all prescribed coarse bonds are in Λ₁ and there are no mixed-scale boundary bonds. Let A denote the relative Landau potential representing the orbit of F. VAR (111)–(112) give

$$
A=A_1+H_1B-HD(A'),\qquad A'=A_1+H_1B,\qquad
A_1=-\mathfrak GJ_0-\mathfrak G V'(A')\;.
\tag{29}
$$

These are VAR's operators and modified constraint; they are not a replacement for the original averaging map. The global bound on A′ has dimensionless C¹ size Cδ_h. VAR (55) and Proposition 4, (97)–(98), therefore give |D(A′)|≤Cδ_h² and |V′(A′)|≤Cδ_h²h⁻³.

PBG (3.133) and Theorem 3.13, with the additional h⁻¹ factor for H and H₁, give the following factors for a source supported in one h-block: H₁ has sizes h⁻¹ and h⁻² in the potential and gradient bounds; 𝔊 has sizes h² and h. Each bound has exponential decay in the distance divided by h. The sum of these decay factors is bounded independently of the number of blocks and the torus. Split the sources into the radius-3Rh cube and its complement. On the first part use (26)–(27). On the complement use the global bounds following (28), and the exponential tail. Apply the global nonlinear bounds to the last two terms in (29). On the fixed number of h-cells around y₀ this yields

$$
h^{-1}|A|+|\nabla_{F_0}^{\eta}A|
\leq C\varepsilon\left(h^\beta R^{12}
+\varepsilon h^2R^{24}+R^{12}e^{-cR}\right)\;.
\tag{30}
$$

For clarity, the gradient contributions are h⁻² times (26), h times (27), h⁻²δ_h² from HD, h·δ_h²h⁻³ from 𝔊V′, and at most Cδ_h h⁻²e^{-cR} from the far sources. The potential estimates divided by h have the same sizes. Polynomial block counts in the tail are absorbed by reducing c. No covariant Laplace bound for 𝔊 is used.

Choose R to be the required block multiple nearest above a fixed sufficiently large multiple of log(1/h). Then δ_h→0, 8Rh tends to zero, and the right side of (30) is at most Cεh^{β/2}. All source smallness requirements and local-domain inclusions consequently hold for sufficiently small h.

#### Passage to the closed plaquette actions

Inside the core F₀=F^{aff}, while a gauge transform of F is exp(iηA)F₀. Expanding the relative plaquette as a closed based product, the covariant curl of A contributes at most Cη²|∇_{F₀}A|, and the remaining terms at most Cη²|A|² and Cη|A|·|F₀(∂p)−1|. By (30), the relative plaquette deviation is at most Cεη²h^{β/2}. This comparison is between conjugated based plaquettes; its absolute value is taken only after that closed product has been formed.

The exact identity 1−Re tr_N U=(2N)⁻¹‖U−I‖²_HS for a unitary matrix U, and the O(εη²) plaquette bounds, give an error at most Cε²η⁴h^{β/2} per fine plaquette action. The affine fine field and the coarse affine field have the same constant linear curvature b_{νμ}−b_{μν}. Their nonlinear errors contribute at most Cε³h²R⁴ times the corresponding cell volume. There are L⁴ fine plaquette base points per coarse cell, for each orientation, and L⁴η⁴=h⁴. Thus the fine action of F over the coarse cell differs from the coarse plaquette action by at most Cε²h^{4+β/2}. Summing over the h-cells in B proves the candidate (23).

This argument, if accepted, supplies action consistency for the actual one-step minimal lift without requiring a globally chosen fine C^{1,β} gauge with a uniform constant. It does not yet justify inserting that lift into the depth-(d+1) variational comparison: its admissibility in the regularity class with constraints at the fixed physical scale must be checked, or minimality must be extended to the needed comparison domain. The projected-gauge coercivity and the finite nonlinear constraint defect needed for (17) also remain to be established. These are separate from the gauge invariance of (22).

## 6. What Is Still Required for Full-Sequence Convergence

The exact operand is the centred difference measure in §2, evaluated on 1 after the two actual constructions are represented and compared. For the fixed contour and terminal coupling, the missing conclusion is a summable sequence a_K such that

$$
\frac{|\mathcal H_K(1)|}{Z_{K+1}}\leq a_K,\qquad
\sum_K a_K<\infty\;.
\tag{9}
$$

The mark in (9) includes the vacuum and coupling matching, both perimeter/corner normalisations, all explicit selector changes, the inherited interactions and the Wilson-loop remainders. The marked-polymer expansion must supply a bound for this complete expression, with its original denominator. Neither a bound on the individual runs nor the old-tail estimate (8) supplies the recent-step part of (9).

If (9) is established, the final summation contains no further analytic gap: for J>K,

$$
|F_J(C)-F_K(C)|\leq\sum_{n=K}^{J-1}a_n
\leq\sum_{n=K}^{\infty}a_n\longrightarrow0\;.
$$

The scalar expectations then have a unique limit. This last implication is elementary; (9), for the actual marked construction, is the unresolved mathematical work. No conclusion of full-sequence convergence is claimed in this file.

## Source Locations

- `WILSON_IT1_CONTINUUM_LIMIT_CLOSURE_2026_10_26.md`, §§1–3 and 5–9: the prescribed runs, normalisation, full remainder and existing comparison.
- `WILSON_FIRST_RG_STEP_V5.tex`, `eq:bare-action`, `eq:bare-blocking-operator`, `eq:global-average`, `lem:global-average`: the exact bare measures and the original first blocking map.
- `WILSON_IT1_D2_STEP_MAP_2026_10_22.md`, D2.2, D2.3 and D2.4: the marked construction to which (9) must apply.
- `WILSON_IT1_D26_CLOSURE_2026_10_24.md`, §5.0: the pairwise running bound used for the carry estimate.
- `../Balaban/tex/CRE/parts/p263.tex`, (2.43)–(2.46): the distinct E- and R-term age bounds; `p264.tex`, (2.47)–(2.50): boundary and partition-function bounds.
- `../Balaban/tex/CRE/parts/p243.tex`, Introduction after (0.1), and `../Balaban/tex/LFR2/parts/p391.tex`–`p392.tex`, (1.104): R changes the effective densities; the iteration is RT.
- `../Balaban/ONE_LOOP_PROOFS.md`, Lemma 2.1, Theorem 8.1 and Corollary 8.2: the stated coupling input.
- `WILSON_CAUCHY_ROUTE_DRAFT_2026_10_21.md`, §4.3; `WILSON_CAUCHY_LIPSCHITZ_2026_10_21.md`, §§3–5; `WILSON_CAUCHY_LIP1A_2026_10_21.md`: the earlier classical, Lipschitz and domain-transfer work.
- `../Balaban/DIFFERENCES_PROOFS.md`, §§1 and 4; `../Balaban/D5_ENERGY.md`: the proposed depth comparison, its energy replacement and the scope of the full-measure assembly.
- `../Balaban/tex/VAR/parts/p278.tex`–`p279.tex`, Theorem 1 (8)–(9): the scales in the regularity and lift bounds; `../Balaban/tex/PBG/parts/p397.tex`, (3.40): the Hölder seminorm convention.
- `../Balaban/tex/VAR/parts/p285.tex`–`p286.tex`, (44)–(55), and `../Balaban/tex/PBG/parts/p422.tex`, (3.133): the exact constraint correction and its scale-dependent bounds.
- `../Balaban/tex/PBG/parts/p394.tex`–`p395.tex`, (3.20)–(3.27), and `p417.tex`, (3.110)–(3.111): the projected Landau gauge, the operator and the constrained quadratic form.
- `WILSON_FIRST_RG_STEP_V5.tex`, `eq:nonlinear-average`, and `../Balaban/tex/CMP98/parts/p023.tex`–`p024.tex`, (42)–(43): the averaging formula and its two-block locality.

## Focused Review

The independent review in `verification/isolated_reviewer/reviews/continuum-fixed-loop-20261027-r1/review.txt` checked the fixed-loop proof, its exponent, the finest-step comparison and the lift-scale calculation. It found the derivation of (12)–(16) valid, requested explicit ladder edges, fine-domain coverage and curvature/constants in the application, and did not accept (17) as established by the supplied energy proof. Those scope corrections are included above. The original packet and its revision hash are retained in that review directory. Review does not change the conditional status of (20) or the unresolved status of (9).

A second independent review, `verification/isolated_reviewer/reviews/continuum-finest-block-20261027-r1/review.txt`, checked §5.4 against the manuscript's full averaging formula. It confirmed the estimates (18)–(19) in substance and requested interface plaquettes, the norm conversion, mesh alignment and the small-h range. These are now explicit. The application also specifies the two variational problems at the same V and the K-to-K+1 comparison; it makes no estimate for the finitely many depths outside that range. Both review packets and transport manifests are retained. The energy hypothesis (17) remains unresolved.

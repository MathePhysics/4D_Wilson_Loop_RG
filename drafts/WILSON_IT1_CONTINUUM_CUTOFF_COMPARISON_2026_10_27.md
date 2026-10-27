# Cutoff Comparison for the Continuum Wilson-Loop Expectation

27 October 2026. Separate continuation of `WILSON_IT1_CONTINUUM_LIMIT_CLOSURE_2026_10_26.md`, as requested. This work does not edit the existing note.

**Status.** Work is paused at the user's request. Full-sequence convergence remains unproved. Section 6 concerns the marked probabilistic comparison for (1), with the physical denominator, inherited integrations and original R-operation retained. The vacuum age estimate in §6.8 has been reviewed under its stated inputs. The Wilson extension in §6.10 has an unresolved second-class re-entry payment, so (99)–(101) are not established. The recent-step derivation in §6.11 and the exploratory calculations recorded in §6.12 are unaccepted. The deterministic work in §5 is inactive and supplies no premise of §6; the reviews of §§5.9–5.11 were interrupted.

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

The current continuum note (9.4)(a) now distinguishes the common linear T maps from the two runs' R operations. This agrees with CRE p.243, which states that R changes effective densities on large-field regions, and LFR2 (1.104), which displays Rρ_k. Preservation of an integrated partition function does not identify the densities as functions. The comparison here retains the original R operations and their marked numerators.

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

### 5.6 Local action consistency for the actual one-step minimal orbit

This calculation addresses the action error of the lift itself. It does not infer a unit-scale Hölder bound from (21). A local affine comparison uses the small dimensionless parameter of the one-step problem and exponential decay at that problem's scale h. This establishes the action-consistency estimate below, under the stated source inputs, but does not establish the variational inequality (47) needed for (17).

#### The invariant quantity and the constraint

Use the manuscript's fixed compact connected simple matrix group and odd L>11. In this subsection let h=L^{-n}, with n the refinement depth, and η=h/L; the dimension is four. Let A_h be a coarse group-valued bond field on the periodic h-lattice, with every plaquette deviation at most εh² in the fixed faithful representation. Fix 0<β<1. On a fixed physical neighbourhood of a unit cube B, assume the local regularity supplied by VAR (9): there is a gauge in which A_h(b)=exp(ih a_μ(x)), with the supremum norms of a and its first physical finite differences, and the β-Hölder seminorm of those differences, bounded by Cε. The constant and neighbourhood are independent of h. Assume 0<ε≤ε_max, with ε_max fixed. The fine and coarse lattices and the cube B are aligned.

Let L_h(A_h) denote the actual one-step minimal orbit of VAR for the original constraint M F=A_h, on the fine η-lattice. Its dimensionless input parameter is O(εh²). The geometry is Ω₀=Ω₁=T_η, Λ₀=∅ and Λ₁=T_h; there are no Dirichlet boundary sites and no mixed-scale constraint bonds. VAR p.277's separation condition is vacuous here; the whole-torus choice is explicitly allowed after REG (1.6) and PRT2 (2.4).

For the use of the source theorems, rescale x=h x′. The source fine spacing is then 1/L and its coarse spacing is one. In dimension four the mesh prefactor in the action, VAR (5) and RG1 (0.2), is one, so the action is unchanged. The rescaled torus is again block-compatible; in RG1's power-of-L geometry its side exponent increases by n. Physical potentials, first derivatives and forces scale by h⁻¹, h⁻² and h⁻³, respectively. VAR's constants after (10) and PBG Theorem 3.1 list dependence only on dimension, L and the indicated Hölder exponent. REG fixes B₁ and B₂ through these propagator constants in (1.62)–(1.64), Proposition 3, and fixes the gauge-contraction thresholds in (1.103)–(1.109), Proposition 5. Their dependence is likewise independent of the torus size. The enlargement of the torus under the change of units therefore introduces no new constant. For a representative F of the orbit define

$$
e_{h,B}(A_h)=
\sum_{\substack{x\in B\cap T_\eta\\\mu<\nu}}
\left(1-\operatorname{Re}\operatorname{tr}_N F(\partial p_{\mu\nu}^\eta(x))\right)
-\sum_{\substack{y\in B\cap T_h\\\mu<\nu}}
\left(1-\operatorname{Re}\operatorname{tr}_N A_h(\partial p_{\mu\nu}^h(y))\right)\;.
\tag{22}
$$

The half-open cube B partitions plaquettes by their base vertices; their other vertices may lie outside B. Both sums retain the closed plaquette traces. The estimate is

$$
|e_{h,B}(A_h)|\leq C\varepsilon^2 h^{\beta/2}|B|\;.
\tag{23}
$$

Here |B| is physical volume. The constants may depend on the group, L, β and the stated local regularity constant, but not on h, the torus volume or the particular coarse field. The assertion is for sufficiently small h, with the threshold uniform under the stated bounds.

The quantity (22) is gauge invariant before any estimate. If s is a coarse gauge transformation, extend it arbitrarily to the fine vertices. Gauge covariance of M maps the fibre M F=A_h bijectively onto the fibre M F=A_h^s. It preserves the regularity conditions and the action. Uniqueness of the minimal orbit therefore identifies L_h(A_h^s) with the transformed orbit. Different extensions agree at coarse vertices and give the same orbit. Every local plaquette trace is unchanged, so e_{h,B}(A_h^s)=e_{h,B}(A_h).

The averaging convention is the later symmetric one of RG1 (0.4), exactly the formula in V5. It is not literally the earlier single-path formula. The transfer is an explicit authorial assertion in RG1 pp.253–254, rather than a separately numbered theorem, and is used in RG1 (1.1), p.260: the minimum with constraint M^k(U)=V is identified with VAR Theorem 1. RG1 p.261 then uses PBG's H₁ and Δ₁, and p.263 uses VAR Proposition 9 for this convention. The application here takes that stated transfer as a source input; it does not identify the two formulas algebraically or supply a new proof of the transfer. Likewise PBG (3.132) and the resulting operator bounds are used as printed source inputs.

There is a distinction between this statement and a statement about Landau coordinates. REG p.81 explicitly says that its Landau-gauge image is not contained in the original fixed-average fibre. The constraint becomes REG (1.31), or VAR (20), with the modified averaging function Q(U₀,ηA). VAR Proposition 2 supplies the return to an axial representative in the original fibre. Below the orbit L_h(A_h) is fixed first. Landau coordinates are used to estimate its local plaquette action, which is unchanged by that return; no equality M(exp(iηA)U₀)=A_h is asserted in those coordinates.

#### An affine field in a shrinking neighbourhood

Fix a coarse vertex y₀ in B and use the local regular gauge on a neighbourhood of y₀. Translate y₀ to zero. The further coarse gauge s(y)=exp(i∑_μ y_μ a_μ(0)) makes the four outgoing bonds at zero equal to the identity. This does not require the matrices a_μ(0) to commute.

Here is the bound on the change of local coordinates. Put c_{h,μ}(y)=(1/ih)log(s(y)s(y+he_μ)⁻¹). The apparent division by h is removable at h=0: s(y)s(y+he_μ)⁻¹−I is the integral of a first derivative over a segment of length h. The first three derivatives of s are bounded uniformly on the fixed neighbourhood by the matrix-exponential integral formula. Thus c_{h,μ} has C² norm at most Cε, uniformly for small h. The transformed potential is (1/ih)log(exp(ih Ad_{s(y)}a_μ(y))exp(ih c_{h,μ}(y))). The logarithm of exp(ihX)exp(ihY) minus ih(X+Y) has a double zero in h. Dividing this remainder by h² gives a function analytic jointly in h, X and Y on a fixed neighbourhood, with uniformly bounded first two X,Y derivatives on a smaller fixed ball. The finite-difference product and chain rules therefore bound the transformed C^{1,β} norm by Cε; no h⁻¹ remains. At y=0 the two exponentials are inverse, so the transformed potential is exactly zero there. Denote it again by a.

Let R≥1 be a sufficiently large integer multiple of the fixed block constants in VAR. In this subsection R denotes only the patch radius measured in h-blocks; the projection R(U₀) in the source equations and the fixed geometric separation parameter are distinct. We will take the patch radius proportional to log(1/h). Choose an enclosing VAR-class cube, made of the prescribed big blocks, containing the cube of radius 8Rh; its size is comparable to Rh and it is contained in the fixed regularity neighbourhood for sufficiently small h. All local-gauge bounds are used on this cube, not merely on the neighbourhood where the gauge transformation is defined. The discrete Taylor estimate gives, with b_{μν}=∂_ν^h a_μ(0),

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
h a^{\mathrm{aff}}_\mu(y)+\frac{h(h-\eta)}{2}b_{\mu\mu}
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

The force of the affine reference is also small. Write J_aff=η⁻² Im D_{F^{aff}}^{η*}∂F^{aff}, exactly VAR (28), p.282; projection to the Lie algebra, when needed, is as in RG1 (1.8). The linear plaquette term is the constant η²(b_{νμ}−b_{μν}), whose ordinary divergence vanishes. The remaining plaquette terms have size at most Cε²η²h²R². Applying one fine difference costs at most C/η; the covariant-transport correction to the constant term is at most Cε²hR. Since η=h/L,

$$
|J_{\mathrm{aff}}|\leq C\varepsilon^2 hR^2\;.
\tag{27}
$$

This force and its norm are covariant and invariant, respectively, by REG (1.11).

#### A regular reference field agreeing with the affine field near y₀

The actual one-step minimum F has the weak bounds of VAR (9)–(10) on a cube of radius 8Rh: in a local gauge its fine potential has sizes CεhR, CεR and CεR/h for the potential, first differences and the two second-order operators, respectively. These are only the one-step bounds. Their use is permitted because R≤M(O(εh²)) for the logarithmic choice of R and sufficiently small h.

The coarse average of this local representative and the coarse field in the gauge of (24) have bond logarithms bounded by Cεh²R. Their coarse gauge transition can be normalised to the identity at y₀. Along each coarse bond its increment is at most Cεh²R, so on the cube its distance from the identity is at most Cεh²R². Take its logarithm λ and extend λ to the fine vertices by multilinear interpolation on the coarse cells. Exponentiation gives a fine gauge transformation agreeing with that transition at the coarse vertices and satisfying |ω−I|≤Cεh²R². The original fine bonds in the weak local gauge have deviations at most Cεh²R. Thus |F^ω(b)−I|≤Cεh²R². The local logarithm gives a compatible potential a_F with |a_F|≤CεhR². The ordinary finite-difference inequalities |∂^η f|≤2η⁻¹|f| and |∂^η∂^η f|≤4η⁻²|f|, with η=h/L and L fixed, now give

$$
|a_F|\leq C\varepsilon hR^2,\qquad
|\partial^\eta a_F|\leq C\varepsilon R^2,\qquad
|\Delta^\eta a_F|+|\partial^{\eta*}\partial^\eta a_F|
\leq C\varepsilon R^2/h\;.
\tag{28a}
$$

All fine stencils used here lie in the enclosing local gauge cube. These are deliberately one-step bounds; they make no assertion of uniform second derivatives at the fixed physical scale.

In the compatible gauge put a₀=(1−χ)a_F+χa^{aff}, with χ=1 within radius 4Rh and χ=0 beyond radius 6Rh, and 0≤χ≤1. Let v be the composite local gauge that placed F in this frame. Define the actual global field F₀ on patch bonds by F₀(b)=v(b₋)⁻¹exp(iηa₀(b))v(b₊), and set F₀=F outside. On the collar χ=0 the inverse-gauge formula is exactly F, so the definitions agree literally. All following local potential calculations for F₀ are made in the compatible frame. The bound |a₀|≤CεhR² holds there on the whole gauge cube. Applying the same fine-grid inverse inequalities to its difference stencils gives, including the patching annulus,

$$
\begin{aligned}
|a_0|&\leq C\varepsilon hR^2,\qquad
|\partial^\eta a_0|\leq C\varepsilon R^2,\\
|\Delta^\eta a_0|+|\partial^{\eta*}\partial^\eta a_0|
&\leq C\varepsilon R^2/h\;.
\end{aligned}
\tag{28b}
$$

The cutoff may be chosen smooth, but this verification does not need derivative bounds on it: the target bounds are at the scale h, a fixed multiple of the fine spacing. To apply REG with global hypotheses, take a second scalar cutoff equal to one within radius 7Rh and zero outside radius 8Rh. Multiply a₀ by it in the compatible gauge cube and extend the result by zero to a globally defined Lie algebra field on the fine torus. Its supremum and the inverse-difference bounds (28b) are unchanged up to a fixed constant, so it satisfies REG (1.140) globally with scale h and parameter Cεh²R², and the flat reference satisfies (1.139). REG (1.141)–(1.142) therefore apply globally to this auxiliary field. Every plaquette and force stencil meeting the changed region of F₀ lies in the radius-7Rh cube, where the auxiliary field agrees with F₀ in the compatible gauge. Gauge invariance gives there

$$
|F_0(\partial p)-I|\leq C\varepsilon R^2\eta^2,\qquad
|D_{F_0}^{\eta*}\partial F_0|\leq C\varepsilon R^2\eta^2/h\;.
\tag{28c}
$$

Outside the patch the same bounds follow from the membership F∈𝔘₁(B₃εh²) in VAR (8). Thus VAR (2) holds globally with parameter Cεh²R².

Fix the PBG big-block size M₀ as a multiple of R₁M₁, and fix its localisation-cube enlargement factors before h. Enclose each PBG cube, if necessary, in a REG Proposition 6 cube of comparable fixed size made of R₁M₁-blocks. Every such cube meeting the changed region lies in the compatible gauge patch when R is large enough, and (28b) verifies PBG (3.35)–(3.36) there. Elsewhere use the local gauge of F. There is also a source justification that does not depend on this reading of the cube sizes: (28c) places F₀ in the full gauge-invariant regularity class globally, and REG Proposition 6, (1.135)–(1.136), supplies the required potential, gradient and second-operator bounds on any admissible cube of factor M with 7·4L²Mα₀≤c₁. This proposition applies to arbitrary regular configurations, not just minima. For the fixed localisation family the required smallness follows as α₀=Cεh²R² tends to zero.

For a coarse bond whose two blocks meet the changed region, both F₀ and F have logarithmic fine potentials bounded by CεhR² in the compatible gauge. The one-step map is analytic in a fixed finite family of fine matrices near the identity, with first derivatives bounded by a constant depending on L. Hence its relative coarse output has deviation at most C_Lη|a₀−a_F|≤Cεh²R². Outside these bonds the two outputs coincide by two-block locality. This proves the global mismatch bound in VAR (14).

Use VAR with the enlarged input upper bound ε₁′=δ_h, where

$$
\delta_h=C\varepsilon h^2R^2\;.
\tag{28}
$$

Choose its fixed constant so that the preceding regularity and mismatch bounds imply VAR (14) with one absolute C₁, and take ε₀=C₁B₃δ_h. The data A_h satisfy VAR (7) with this enlarged upper bound since εh²≤δ_h. For sufficiently small h all the source smallness conditions hold. The original minimum F is in this enlarged regular class and remains a critical point of the same constrained action. VAR's uniqueness clause therefore identifies it with the critical orbit obtained in the reduction about F₀. The global force bound is Cδ_h h⁻³ and the global coarse mismatch is Cδ_h, while (26)–(27) apply near y₀. The reference's dependence on the original minimum is harmless for this deterministic use of uniform bounds.

This construction does not select a preferred gauge orbit representative for the physical observable. Under a gauge change of A_h, transport the chosen local gauge by the inverse transformation. The coordinate construction is then identical, and F₀ is transformed with F. All relative coarse words, forces and covariant derivatives used in the comparison transform at their base points; their matrix norms are invariant. The final quantity remains (22).

#### The local comparison from VAR's equation

Apply VAR's reduction about the regular reference F₀. Its actual source is B= (1/i)log(A_h(MF₀)⁻¹), since all prescribed coarse bonds are in Λ₁ and there are no mixed-scale boundary bonds. Let A denote the relative Landau potential representing the orbit of F. VAR (111)–(112) give

$$
A=A_1+H_1B-HD(A'),\qquad A'=A_1+H_1B,\qquad
A_1=-\mathfrak GJ_0-\mathfrak G V'(A')\;.
\tag{29}
$$

These are VAR's operators and modified constraint; they are not a replacement for the original averaging map. The global bound on A′ has dimensionless C¹ size Cδ_h. VAR (55) and Proposition 4, (97)–(98), therefore give |D(A′)|≤Cδ_h² and |V′(A′)|≤Cδ_h²h⁻³.

PBG (3.133) and Theorem 3.13, with the additional h⁻¹ factor for H and H₁, give the following factors for a source supported in one h-block: H₁ has sizes h⁻¹ and h⁻² in the potential and gradient bounds; 𝔊 has sizes h² and h. The distance used here is the explicit definition PRT2 (2.46), p.231; in this single-scale geometry it is the shortest torus ℓ¹ distance divided by h. The exponential row sum is at most ((1+e^{-c})/(1−e^{-c}))⁴; restricting to distances at least R gives Ce^{-cR/2}. These bounds are independent of torus size. The whole-torus choice is allowed by PRT2 (2.1)–(2.4); the Dirichlet complement in PBG is empty. Split the sources into the radius-3Rh cube and its complement. On the first part use (26)–(27). On the complement use the global bounds following (28), and the exponential tail. Apply the global nonlinear bounds to the last two terms in (29). On the fixed number of h-cells around y₀ this yields

$$
h^{-1}|A|+|\nabla_{F_0}^{\eta}A|
\leq C\varepsilon\left(h^\beta R^2
+\varepsilon h^2R^4+R^2e^{-cR}\right)\;.
\tag{30}
$$

For clarity, the gradient contributions are h⁻² times (26), h times (27), h⁻²δ_h² from HD, h·δ_h²h⁻³ from 𝔊V′, and at most Cδ_h h⁻²e^{-cR} from the far sources. The potential estimates divided by h have the same sizes. Polynomial block counts in the tail are absorbed by reducing c. No covariant Laplace bound for 𝔊 is used.

Choose R to be the required block multiple nearest above a fixed sufficiently large multiple of log(1/h). Then δ_h→0, 8Rh tends to zero, and the right side of (30) is at most Cεh^{β/2}. All source smallness requirements and local-domain inclusions consequently hold for sufficiently small h.

#### Passage to the closed plaquette actions

Inside the core F₀=F^{aff}, while a gauge transform of F is exp(iηA)F₀. Expanding the relative plaquette as a closed based product, the covariant curl of A contributes at most Cη²|∇_{F₀}A|, and the remaining terms at most Cη²|A|² and Cη|A|·|F₀(∂p)−1|. By (30), the relative plaquette deviation is at most Cεη²h^{β/2}. This comparison is between conjugated based plaquettes; its absolute value is taken only after that closed product has been formed.

The exact identity 1−Re tr_N U=(2N)⁻¹‖U−I‖²_HS for a unitary matrix U, and the O(εη²) plaquette bounds, give an error at most Cε²η⁴h^{β/2} per fine plaquette action. At the coarse cell's base point y₀=0, a(0)=0 and the definition of b gives a_ν(he_μ)=hb_{νμ}. Consequently the actual coarse plaquette is exp(ih²b_{νμ})exp(−ih²b_{μν}), exactly the corresponding coarse affine plaquette. Its deviation from its constant linear curvature term is O(ε²h⁴). The affine fine plaquettes have the same linear curvature; their remainders are O(ε²η²h²R²). Applying the same squared-norm identity gives an action error bounded by Cε³h²R⁴ times the corresponding cell volume. There are L⁴ fine plaquette base points per coarse cell, for each orientation, and L⁴η⁴=h⁴. Thus the fine action of F over the coarse cell differs from the actual coarse plaquette action by at most Cε²h^{4+β/2}. Summing over the h-cells in B proves (23).

This supplies action consistency for the actual one-step minimal lift without requiring a globally chosen fine C^{1,β} gauge with a uniform constant. Its exponent is β/2, not the β in the earlier energy note: a subsequent action-to-L² estimate would give a distance of order h^{β/4}, and §5.2 would then give the fixed-loop rate h^{β/12}. All are still geometric in the refinement depth. It does not yet justify inserting that lift into the depth-(d+1) variational comparison: its admissibility in the regularity class with constraints at the fixed physical scale must be checked, or minimality must be extended to the needed comparison domain. The local competitor's regularity, the local variation estimate and the remaining energy hypotheses must also be verified. These are separate from the gauge invariance of (22).

### 5.7 Coercivity in the exact constraint coordinates

This calculation concerns the actual Wilson action near a VAR minimum U₀=U_n(V), with η=L^{-n}, Ω₀=⋯=Ω_n=T_η, Λ_j=∅ for j<n and Λ_n=T₁. The field V satisfies VAR (7) in its smallness window. The unit torus has the standing big-block tiling and size requirements: its periods are multiples of M₁ and contain the enlarged VAR cubes of side 2M_*+4R₁M₁, with M_*=R₁M₁ fixed. These are the source geometry requirements already used in the step map; its (TC) bound, with M≥R₁M₁, is stronger than this cube-size bound. The whole-torus choice is permitted by REG (1.3)–(1.6) and PRT2 (2.1)–(2.4), and makes VAR's separation condition vacuous; the Dirichlet complement in PBG is empty. The symmetric averaging convention and the PBG operator bounds are source inputs as specified in §5.6. The argument uses the exact nonlinear constraint coordinates; it does not set the linear average of a finite relative field to zero. Its conclusion is global on the comparison torus, not a shell Poincaré inequality.

Use physical mesh η, the real Lie algebra inner product tr_N(XY) on Hermitian matrices, and the bond inner product η⁴∑_b tr_N(X_bY_b). Let

$$
\mathcal T=\{z\,|\,Qz=0,\ RD_{U_0}^{\eta*}z=0\},\qquad
\|z\|_{\mathsf X}=\max\{|z|,|\nabla_{U_0}^{\eta}z|\}\;.
\tag{31}
$$

Here Q, R and the covariant derivative are exactly the operators of VAR (75)–(83) at U₀. The physical regularity scale is one throughout; all weights in that source norm are therefore one. The dimension is four; n denotes the depth. For z∈𝒯 in the small ball of VAR Proposition 3, set A(z)=z−HD(z). The action in these coordinates is

$$
\mathcal F(z)=S_\eta\left(e^{i\eta A(z)}U_0\right)
=S_\eta(U_0)+\frac12\langle z,\Delta_1z\rangle+V(z)\;.
\tag{32}
$$

This is VAR (141)–(142). Its Δ₁ includes the quadratic term from the nonlinear constraint, with the sign specified by VAR (79) and PBG (3.127)–(3.128). In particular, that term is not dropped as a higher-order error. V has no terms of orders zero, one or two at zero.

Equation (32) defines an action on the small coordinate chart, where Q(U₀,ηA(z))=0 is the modified constraint. The inequalities below do not require a claim that every chart point belongs to VAR's original regularity class. For a field already in that regular fixed-average class, REG Theorem 2 and VAR Proposition 3 supply its Landau representative and these coordinates, with unchanged action. Whether any further comparison field lies in this chart must be proved separately. In particular the displayed Landau representative is not asserted to have the original raw averages.

#### The contraction gives a quadratic-form bound

On 𝒯 the form E(z)=⟨z,Δ₁z⟩ is positive definite. Use G₁ from PBG (3.128), and 𝔊=𝔓G₁ from (3.153), with 𝔓 the G₁⁻¹-orthogonal projection onto 𝒯. On 𝒯 the quadratic form of G₁⁻¹ is that of Δ₁, because the gauge and averaging terms vanish. Consequently ⟨v,Δ₁𝔓G₁f⟩=⟨𝔓v,f⟩=⟨v,f⟩. Thus, for v∈𝒯 and an arbitrary force f,

$$
\langle v,\Delta_1\mathfrak G f\rangle=\langle v,f\rangle\;.
\tag{33}
$$

At the minimum the projected force vanishes. For B=0, VAR (119)–(121) give a Lipschitz constant q=4B₀C₄r for the map z↦−𝔊V′(z) on the convex ball ‖z‖_𝕏<r in 𝒯. Choose r so that 2r≤a₃, 4r≤c₄, 18C₂B₀·4c₁(1/2)·2r≤1 and q≤1/2. The linearising transformation is then defined on the entire complex ball of radius 2r used in the Cauchy argument, not just on the real ball of radius r. All constants are independent of η and torus size.

For any z in this ball define K_z=𝔊V″(z)|_𝒯. Differentiating the Lipschitz bound gives ‖K_z‖_{𝕏→𝕏}≤q. By (33) and symmetry of the real Hessian V″, K_z is self-adjoint in the E inner product. Each of its eigenvalues λ therefore is real and satisfies |λ|≤q: apply the 𝕏-norm bound to its eigenvector. No comparison constant between the 𝕏 norm and the energy norm is used. For every v∈𝒯, the finite-dimensional spectral theorem yields

$$
|\langle v,V''(z)v\rangle|\leq q\langle v,\Delta_1v\rangle\;.
\tag{34}
$$

Integrate the Hessian of (32) along tz, 0≤t≤1, which stays in the same ball. Since the first derivative at zero vanishes on 𝒯,

$$
\frac{1-q}{2}E(z)
\leq\mathcal F(z)-S_\eta(U_0)
\leq\frac{1+q}{2}E(z)\;.
\tag{35}
$$

Thus the contraction estimate supplies a uniform lower bound on the entire small constraint chart, rather than positivity only at its centre.

#### Physical L² control

PBG (3.46), Theorem 3.3 and Theorem 3.13 give the L² operator bound between two unit blocks B_y, B_{y′},

$$
\|1_{B_y}\mathfrak G1_{B_{y'}}\|_{2\to2}
\leq C e^{-c\,\operatorname{dist}(y,y')}\;.
$$

Here the distance is PRT2 (2.46), equal in this geometry to the unit-lattice torus ℓ¹ distance. Its exponential row sum is at most ((1+e^{-c})/(1−e^{-c}))⁴, uniformly in torus size. Schur's bound on the matrix of block norms therefore gives ‖𝔊‖_{2→2}≤C_G, uniformly in η and torus size. To obtain the inverse bound, use (33): ‖z‖₂²=E(z,𝔊z)≤E(z)^{1/2}E(𝔊z)^{1/2}, while E(𝔊z)=⟨𝔊z,z⟩≤C_G‖z‖₂². Cancelling ‖z‖₂ when z≠0 gives

$$
\|z\|_2^2\leq C_G E(z)\;.
\tag{36}
$$

The finite constraint correction also has a uniform L² bound. At unit regularity scale, VAR (73) gives a derivative kernel bounded by Cr e^{-c dist(c,b)} for D′(z), from fine bonds with measure η⁴ to coarse bonds with counting measure. Both its row integral and its column sum are at most Cr; the volume of each unit block is fixed. Hence ‖D′(z)‖_{2→2}≤Cr. Since D(0)=0, integration on the segment tz gives ‖D(z)‖₂≤Cr‖z‖₂. The H kernel in PBG (3.133), at the same unit scale, has bounded row and column sums, so ‖HD(z)‖₂≤C_Hr‖z‖₂. Consequently

$$
\|A(z)\|_2^2\leq(1+C_Hr)^2\|z\|_2^2
\leq\frac{2C_G(1+C_Hr)^2}{1-q}
\left(\mathcal F(z)-S_\eta(U_0)\right)\;.
\tag{37}
$$

For any fixed unitary representation π, let F be any representative of the orbit of exp(iηA(z))U₀. The logarithm δ_b=ηA(z)_b belongs specifically to this Landau representative. The orbit distance is the infimum over fine site gauges of (η²∑_b‖π(F_b)−π(U₀^g(b))‖²)^{1/2}, as in (11). Since ‖π(exp(iδ_b))−I‖≤‖dπ(iδ_b)‖ and matrix norms on the fixed Lie algebra are equivalent, the physical weights give

$$
\mathfrak d_\eta(F,U_0;T)^2
\leq\eta^2\sum_b\|\mathrm d\pi(i\delta_b)\|^2
\leq C_\pi\|A(z)\|_2^2
\leq C\left(S_\eta(F)-S_\eta(U_0)\right)\;,
\tag{38}
$$

No estimate of a prescribed axial-gauge difference is asserted. Under a change of background gauge, z, A(z), their covariant derivatives and the operator kernels transform in the adjoint representation at their base points. For D this follows by uniqueness in its covariant fixed-point equation VAR (49); H and 𝔊 are constructed from the covariant quadratic forms and constraints, as in PBG (3.28)–(3.34). Thus (31)–(37) and the final orbit-distance statement are unchanged. No probability measure is gauge fixed in this argument.

The chart inclusion for the actual blocked background is proved in §5.8. With that inclusion, (38) supplies the global action-to-L² passage needed in the energy route, including the finite nonlinear constraint correction. A vanishing action upper bound is still needed, as specified in (47). This argument does not supply the local shell estimate used in D5_ENERGY E2.

### 5.8 Regularity of the blocked background

The comparison field in §5.7 is W=M U^{(d+1)} on the h-lattice, with fine spacing η=h/L and prescribed coarse spacing one. The geometry and source inputs are those of §5.7. Fix β<β₀<1 and M_*=R₁M₁, and set ε=C_VAR(β₀)M_*ε₁, with C_VAR large enough to cover B₃, B₄(β₀) and the fixed matrix-norm conversions in VAR (9)–(10). All constants below are fixed before the refinement depth. The needed hypothesis is the full regularity condition of REG, including the covariant divergence of the curvature. A plaquette bound alone would not justify the Landau-gauge theorem. The following calculation uses both second-order bounds in VAR (10).

#### A finite-difference bound

On a periodic fine lattice let D_μ=(T_μ−I)/η be the forward difference, let Δ_η=∑_μD_μ*D_μ, and put S_μ=L⁻¹∑_{j=0}^{L-1}T_μ^j. The difference at spacing h is D_μ^h=S_μD_μ. The scalar operator S_μ*S_μ−I is a finite convolution with a double zero at zero frequency, so it equals η²P_{μ,L}D_μ*D_μ, where P_{μ,L} is a finite convolution whose ℓ¹ norm depends only on L.

For every product D^{(4)} of four forward or backward differences, the operator η²D^{(4)}Δ_η⁻¹ on mean-zero functions has ℓ∞ norm bounded independently of η and the torus size. To see this, scale the lattice to spacing one. Its Fourier multiplier is p(θ)/λ(θ), where λ(θ)=4∑_μsin²(θ_μ/2) and p vanishes to order four at zero. On a dyadic annulus |θ| comparable to 2⁻ʲ, derivatives of order m are bounded by C_m2^{j(m−2)}. A smooth partition into these annuli, followed by integration by parts, bounds the Fourier coefficients of the j-th piece by

$$
C_N2^{-6j}(1+2^{-j}|x|)^{-N}\;.
$$

For N>4 their ℓ¹ sum is at most C2⁻²ʲ, which is summable in j. The part away from zero is smooth and has summable Fourier coefficients. The multiplier extends continuously by zero at zero; periodising this ℓ¹ kernel gives the same multiplier on every finite torus and cannot increase its ℓ¹ norm. This proves the claimed uniform bound, including mixed fourth differences. For its application, Δ_ηa has mean zero on the torus, and fourth differences kill constants, so D^{(4)}a=D^{(4)}Δ_η⁻¹Δ_ηa; no constant mode is inverted.

Since Δ_h−Δ_η=η²∑_μP_{μ,L}(D_μ*D_μ)², it follows that

$$
\|\Delta_h a\|_\infty\leq C_L\|\Delta_\eta a\|_\infty\;.
\tag{39}
$$

#### The linear part of the actual average

Work in one of the local gauges of VAR (9)–(10), writing the fine field as exp(iηa). Let B_L be the centred box average over the fine sites of one L-block. Let C_h(a;y) be the mean linear line integral along the coordinate paths from y to those sites. The linear part of the logarithmic group average, divided by h, is

$$
(\mathcal Q_0a)_\mu(y)
=B_LS_\mu a_\mu(y)-D_\mu^h C_h(a;y)\;.
\tag{40}
$$

This is the linear term of RG1 (0.4): the two connector means are C_h(a;y) and C_h(a;y+he_μ), and the translated long path gives B_LS_μa_μ. These are identities inside the local-coordinate computation. The connector term cancels under the curl before any curvature estimate is made.

Write ∂_η for the discrete exterior derivative of a one-form. Commuting the finite convolutions gives

$$
(\partial_h^*\partial_h\mathcal Q_0a)_\mu
=B_LS_\mu\left((\partial_\eta^*\partial_\eta a)_\mu
+\sum_\nu(S_\nu^*S_\nu-I)
\left(D_\nu^*D_\nu a_\mu-D_\nu^*D_\mu a_\nu\right)\right)\;.
\tag{41}
$$

Each extra term is η² times a finite convolution of fourth differences of a. Apply the bound preceding (39) to Δ_ηa. The operator 𝒬₀ itself is a finite convolution with ℓ¹ norm bounded in terms of L, and it commutes with the scalar Δ_h. Therefore

$$
\begin{aligned}
\|\Delta_h\mathcal Q_0a\|_\infty
&\leq C_L\|\Delta_\eta a\|_\infty,\\
\|\partial_h^*\partial_h\mathcal Q_0a\|_\infty
&\leq C_L\left(\|\partial_\eta^*\partial_\eta a\|_\infty
+\|\Delta_\eta a\|_\infty\right)\;.
\end{aligned}
\tag{42}
$$

The first-derivative and Hölder bounds are also preserved by 𝒬₀, since it has finite coefficients and D_μ^h=S_μD_μ. These statements hold locally with a fixed collar: multiply the local potential by a smooth cutoff equal to one on all required stencils, and extend it by zero. The cutoff product rules preserve the bounds on a, its first derivatives, Δ_ηa and ∂_η*∂_ηa, with constants depending only on the fixed collar. This permits the periodic Fourier estimate without assuming a global gauge.

#### The nonlinear remainder and the invariant regularity class

For a finite array X of fine potentials on the two-block stencil, the exact map Ψ_h(X)=(1/ih)log M(exp(iηX)) is analytic when h|X| is sufficiently small. Its linear part is 𝒬₀X. Write Ψ_h(X)=𝒬₀X+R_h(X). Analyticity of the finite matrix products, logarithms and exponential, after scaling their arguments by h, gives

$$
|R_h(X)|\leq C_Lh|X|^2,\qquad
\|DR_h(X)\|\leq C_Lh|X|,\qquad
\|D^2R_h(X)\|\leq C_Lh\;.
\tag{43}
$$

Take the array X_y of translates of the actual local potential a. VAR (9) gives |X_y|≤Cε, |D^hX_y|≤Cε and |D^hD^hX_y|≤Cεh^{β−1}; the last estimate follows by differencing the β-Hölder first derivatives. Applying the finite-difference chain rule to (43) yields

$$
|D^hD^h R_h(X_y)|
\leq C_L\left(h\varepsilon\cdot\varepsilon h^{\beta-1}
+h\varepsilon^2\right)
\leq C_L\varepsilon^2h^\beta\;.
\tag{44}
$$

The same first-difference formula shows that R_h(X_y) has first derivative and β-Hölder first-derivative bounds C_Lhε². Combining (42)–(44), the coarse logarithmic potential a_W defined by W=exp(ih a_W) in the restricted local gauge satisfies

$$
|a_W|+|\partial^h a_W|+\|a_W\|_{1,\beta}
+|\Delta_h a_W|+|\partial_h^*\partial_h a_W|
\leq C_L\varepsilon\;.
\tag{45}
$$

To apply REG with global hypotheses, multiply a_W by a smooth fixed-physical-scale cutoff equal to one on the plaquette and force stencils under consideration, and extend it by zero. The product rules for ∂_h*∂_h involve its value on a_W, first derivatives of a_W multiplied by first cutoff derivatives, and a_W multiplied by second cutoff derivatives. All are O(ε) by (45). Thus this auxiliary global potential satisfies REG (1.140) at scale one with a flat global reference. The inequalities (1.141)–(1.142) apply to it. On the selected stencils it agrees with W in its local gauge, giving |W(∂p)−I|≤Cεh² and |D_W^{h*}∂W|≤Cεh². Equivalently, the stencil-local formulas are REG (1.21), (1.47) and (1.54). Covering the torus by the available local gauges proves full fixed-scale regularity of W with a fixed enlarged constant.

The use of local coordinates here is gauge independent: for a different gauge of the input fine field, compose the chosen local gauge with its inverse. The coordinate potential a and the calculation are then identical. Covariance of M restricts the same transformation to the coarse vertices, and the final curvature and covariant-divergence bounds transform by conjugation. The connector line integrals in (40) are not observables or activities; their curl cancellation is used as an algebraic identity, and no open-loop quantity is propagated into the Wilson estimate.

#### The actual field lies in the constraint chart

Now take the two original reconstructions U^{(d)}(V) and U^{(d+1)}(V), with V in the stated common regular domain, and put W=M U^{(d+1)}. Both U^{(d)} and W satisfy the fixed-scale REG hypotheses by VAR (9)–(10) and (45). All averages are on their regular logarithm branches: CMP98 Proposition 2, in the symmetric convention stated in RG1, bounds the j-th averaged plaquettes by Cε(L^jη)². Each loop used at its next step fills at most C_LL² such plaquettes, so its deviation is below the fixed chart radius when ε is sufficiently small, uniformly up to the terminal spacing one. In the first step the same fact follows directly from the local fine logarithms. Thus the actual averaging composition gives M^dW=M^{d+1}U^{(d+1)}=V exactly.

Choose the common small-field window once so that ε₁≤a₁, C_Lε+B₃ε₁ is below the REG and PBG regularity thresholds, all these loop words stay in the chart, and the resulting Landau bound Cε is at most r/4. The thresholds are independent of d, h and torus volume. Put W in the relative axial gauge first, preserving the original constraint. REG Theorem 2 then gives its relative Landau potential A with modified constraint zero and ‖A‖_𝕏≤Cε. VAR Proposition 3, specifically (62), gives z∈𝒯 with A=z−HD(z) and ‖z‖_𝕏≤2Cε≤r/2. This puts the actual comparison orbit in the chart, uniformly in d.

Consequently (38) applies to the actual blocked background and gives

$$
\mathfrak d_h\left(MU^{(d+1)}(V),U^{(d)}(V);T\right)^2
\leq C\left(S_h(MU^{(d+1)}(V))-S_h(U^{(d)}(V))\right)\;.
\tag{46}
$$

This establishes no vanishing rate for the action gap on the right. Its role is to justify the actual-field and gauge hypotheses of the global action-to-L² passage, rather than leave them as an unnamed Poincaré assumption. It is restricted to the globally small-field comparison; it does not prove a local shell estimate or the full marked-measure comparison.

#### The action upper bound still to be justified

The next required inequality is

$$
S_{h/L}(U^{(d+1)}(V))
\leq S_{h/L}(L_h(U^{(d)}(V)))\;.
\tag{47}
$$

The proposed competitor satisfies the original constraint exactly: M^{d+1}L_h(U^{(d)}(V))=M^dU^{(d)}(V)=V. But its one-step force bound is of physical size Cε/h, whereas the depth-(d+1) regularity class requires Cε. The one-step theorem therefore does not justify (47) by itself. One must prove membership in that stronger regularity class, or show that the competitor's orbit lies in the uniformly small exact constraint chart about U^{(d+1)}, where (35) would give (47). Neither inclusion is asserted here. Once (47) is justified, the two lift action-consistency estimates would bound the right side of (46); the full marked comparison would still remain.

### 5.9 Covariant Hölder regularity of the lift — inactive, unreviewed candidate

This section extracts further consequences of the local comparison (30). Keep the assumptions of §5.6 and put α=β/2. For a real field U at mesh s define the based matrix-valued plaquette deviation

$$
\mathscr K_s(U)_{\mu\nu}(x)
=s^{-2}\left(U(\partial p_{\mu\nu}^s(x))-I\right)\;.
\tag{48}
$$

Its covariant α-Hölder seminorm compares the values at x and z after conjugation by U(Γ_{x,z}), divided by |x−z|^α, for 0<|x−z|≤1. Here Γ_{x,z} is a fixed shortest coordinate path and distance is the physical torus ℓ¹ distance. The orientation μν is kept the same. The full norm includes the supremum norm. Every comparison is of based closed plaquettes at the same point and its matrix norm is gauge invariant. Other shortest coordinate orderings change the comparison by at most Cε²|x−z|² under the curvature bound, by a plaquette filling.

Let F=L_h(A_h), with η=h/L. Let P_c(F) be the straight fine transport along a coarse bond. The candidate consequences of (30) are

$$
\|A_h(c)P_c(F)^{-1}-I\|\leq C\varepsilon h^{2+\alpha},\qquad
\|\mathscr K_\eta(F)\|_{C^\alpha(F)}\leq C\varepsilon\;.
\tag{49}
$$

The notation C^α(F) is exactly the covariant norm just defined, not an ordinary componentwise norm in a prescribed gauge.

#### Straight transport and the coarse frame

In the affine field (25), the linear terms of the average and of the straight path are both h∑_νb_{μν}y_ν. Therefore their closed relative word differs from the identity by at most Cε²h⁴R². For the actual minimum, use its Landau representative relative to F₀ in the core of the patch. The potential A in (30) has size Cεh^{1+α}. The finite word defining the closed relative expression M(F,c)P_c(F)⁻¹ changes by at most C_Lh|A|. The expression is conjugated under a fine gauge transformation, so its norm is unchanged on returning to the original representative. Since M(F)=A_h exactly, this proves the first inequality in (49).

For a fine plaquette based at x in the h-cell with base y, transport its deviation to y along a fixed path inside that cell. The same local comparison yields

$$
\left\|
\operatorname{Ad}_{F(\Gamma_{y,x})}\mathscr K_\eta(F)_{\mu\nu}(x)
-\mathscr K_h(A_h)_{\mu\nu}(y)
\right\|\leq C\varepsilon h^\alpha\;.
\tag{50}
$$

There is a coarse-frame issue in this statement, which must be checked. The Landau transformation used in (30) does not fix the raw coarse data. Its return to the original axial representative has, at a coarse vertex y, the value u(y)=(\overline{R_{0,y}U_1}^{(1)})⁻¹ of CMP98 (86)–(87), with U₁=exp(iηA). Each relative path in this one-step mean has physical length O(h). Telescoping its closed based relative product gives |u(y)−I|≤C_Lh|A|≤Cεh^{2+α}. A preceding relative axial transformation is the identity at these coarse vertices. Hence the change of coarse frame rotates a curvature of size Cε by at most Cε²h^{2+α}. In the normalised coarse gauge the actual coarse plaquette at y has linear part i(b_{νμ}−b_{μν}), as in §5.6, and the affine fine plaquettes have the same part. The relative plaquette estimate from (30), the O(ε²h²R²) affine remainder and the preceding frame correction prove (50). Both terms in (50) transform by conjugation at y.

#### The Hölder estimate

The assumed coarse C^{1,β} charts give |𝒦_h(A_h)|≤Cε and covariant β-Hölder norm Cε. This follows by expanding the coarse plaquette through its linear curl and quadratic products: the curl has the given β-Hölder bound, and the remaining products have C^β norm Cε². Conjugating a plaquette along a coarse path of length r changes it by at most Cε²r in that chart, still bounded by Cεr^β for r≤1.

For two fine vertices at distance r≤h, use one affine comparison patch containing both. In its Landau frame both curvatures differ from the same affine curvature by Cεh^α; transporting one to the other adds at most Cε²h². Since r≥η=h/L, this is at most C_Lεr^α.

For h<r≤1, use (50) to move the two fine plaquettes to their coarse-cell bases. The two errors are Cεh^α. Along a coarse coordinate path of length O(r), the first inequality of (49) bounds the closed relative product of the coarse transport and the concatenated straight fine transport by Cεrh^{1+α}. Its action by conjugation on a curvature contributes at most Cε²rh^{1+α}. The coarse Hölder estimate contributes Cεr^β. Finally, replacing the concatenated path by the prescribed fine coordinate path closes a loop inside a box of diameter O(r); its filling costs Cεr², and its conjugation of a curvature costs Cε²r². Thus the full difference is bounded by

$$
C\left(\varepsilon h^\alpha+\varepsilon r^\beta
+\varepsilon^2rh^{1+\alpha}+\varepsilon^2r^2\right)
\leq C\varepsilon r^\alpha\;.
$$

This proves the second candidate bound in (49). The argument keeps relative transports closed before estimating them. It gives no uniform bound on D_F*∂F; its purpose is the weaker, gauge-invariant input to the continuation below.

### 5.10 Gauge continuation with Hölder curvature — inactive, unreviewed candidate

The proposed use of (49) is restricted to a continuous path of the actual fields. It does not assume a general extension of REG Theorem 2 to all fields with Hölder curvature. Fix the fine mesh η=L^{-k}, terminal spacing one, and a VAR minimum U₀ with terminal data V. Let F_t, 0≤t≤1, be a continuous path of real fine-field orbits, with M^kF_t=V, starting at the orbit of U₀. Suppose the gauge-invariant norms in (48) satisfy ‖𝒦_η(F_t)‖_{C^α(F_t)}≤Cε uniformly in t. The construction of this path for (47) is given in §5.11. Choose 0<θ<α.

The aim is to put every orbit on this path in the small constraint chart of §5.7, with constants independent of η. At a fixed η all spaces are finite dimensional. The mesh-independent estimates enter the a priori bound below, rather than a bound on the number of continuation steps.

#### A priori bound in a Landau representative

Suppose a representative has the form F=e^{iηa}U₀, with |a|≤δ, RD₀*a=0 and Q(U₀,ηa)=0. Here D₀ is the covariant exterior derivative at U₀, on the relevant form degree, and Q is the modified constraint. Let ‖a‖_{X_θ} include |a|, |∇₀a| and the θ-Hölder seminorm of ∇₀a in the PBG convention. The constant δ is fixed and small; ε will be smaller still.

First change the transport in the curvature Hölder norm from F to U₀. A relative transport along a path of physical length r≤1 is a closed based product of transported factors exp(iηa). Its action on a based curvature of size Cε differs from the U₀ transport by at most Cδεr. Thus the Lie-algebra-valued two-form E=η⁻²Π Im(∂F−∂U₀) has U₀-covariant C^α norm at most Cε. Here Π is the fixed projection to the Lie algebra as in RG1 (1.8).

Expand the closed relative plaquette as in REG (1.43), (1.47) and VAR (24)–(25), retaining the entire product before taking its norm. Its linear term is iη²D₀a. All remaining terms, after division by η², contain either two factors of a at neighbouring, parallel-transported bonds, or one a and a background curvature with a factor η. Higher powers have further factors η. Therefore

$$
D_0a=E+N(a),\qquad
\|N(a)\|_{C^\alpha(U_0)}
\leq C(\delta+\varepsilon)\|a\|_{X_\theta}\;.
\tag{51}
$$

For this estimate it is enough that a has bounded first covariant differences: telescoping along paths of length at most one gives ‖a‖_{C^α(U₀)}≤C(|a|+|∇₀a|). Products of the neighbouring values consequently have C^α norm at most Cδ‖a‖_{X_θ}. This avoids replacing the nonlinear term by a fixed O(δ²) error. At fixed mesh the norms are finite before the estimate is applied.

Let G_reg be the inverse of D₀*D₀+D₀RD₀*+Q₀*Q₀ in REG (1.58), where Q₀ is the linear part of the modified average at unit physical scale. The PBG estimates give

$$
\|G_{\mathrm{reg}}D_0^*E\|_{X_\theta}
\leq C\|E\|_{C^\alpha(U_0)},\qquad
\|G_{\mathrm{reg}}Q_0^*b\|_{X_\theta}
\leq C\|b\|_\infty\;.
\tag{52}
$$

Here the first bound uses PBG (3.44)–(3.45) with the positive exponent gap α−θ, summed over fixed unit blocks. For precision, the operator in (1.58) omits the small Δ′ term of PBG's action Hessian. PBG (3.69) bounds that term by Cε as an ℓ∞ operator. A Neumann expansion about the PBG inverse, using its ℓ∞→X_θ bound (3.42)–(3.43), transfers the mixed derivative bound to G_reg. For the second bound, CMP98 (147) and two-block locality give a bounded coarse-ℓ∞ to fine-ℓ∞ map Q₀*, with the physical fine measure in its adjoint; then use the same propagator bound. All block row sums are bounded independently of η and the torus.

The exact constraint gives Q₀a=−C(a), with ‖C(a)‖∞≤C|a|²≤Cδ‖a‖_{X_θ}, by CMP98 Proposition 4. The Landau condition and (51) therefore imply

$$
a=G_{\mathrm{reg}}D_0^*(E+N(a))-G_{\mathrm{reg}}Q_0^*C(a),\qquad
\|a\|_{X_\theta}\leq C\varepsilon+C(\delta+\varepsilon)\|a\|_{X_\theta}\;.
$$

Choose δ and ε so that the last coefficient is at most 1/2. Every such small Landau representative then satisfies

$$
\|a\|_{X_\theta}\leq C_*\varepsilon\;.
\tag{53}
$$

No bound on D_F*∂F was used. The only field whose stronger regularity enters the propagator is the fixed reference minimum U₀.

#### The order of the mean-gauge correction

Write m_j(u)=\overline{R(U₀)u}^{\,j} for the scalar gauge-transformation averages of CMP98 (78)–(80). If Φ is the relative axial representative of an orbit and Φ=(e^{iηa}U₀)^u, the mean-gauge normalisation is m_k(u)=I. Our convention is (U^g)^v=U^{vg}. Applying a correction v⁻¹ to the Landau representative therefore replaces u by uv. The constraint to preserve is m_k(uv)=I, with this order.

The required right-ordered scalar mean has the same quantitative linearisation as the source construction. Here is the check. Suppose m_j(u) satisfy CMP98 (166)–(167) with parameter δ_u, and put v=exp(iλ), with |λ|+|D₀λ|≤ρ, allowing complex λ for the Cauchy estimates. Let s_j=L^jη, Z_j=m_j(u), Y_j=m_j(v), T_j=m_j(uv). CMP98 Proposition 10 with u₁=I gives within-block diameters Cρs_{j+1} for Y_j; the corresponding diameter of Z_j is δ_us_{j+1}.

For the finite one-step group mean, the product error M({Z_xY_x})−M({Z_x})M({Y_x}), expressed in right logarithmic coordinates, vanishes when either array is constant. Left and right covariance and the mixed analytic Taylor formula consequently bound it by C·diam(Z)·diam(Y). Also, the mean's derivative in right logarithmic coordinates has ℓ∞ norm at most 1+C·diam: at a constant array its derivative is the positive weighted average, of norm one. Common group factors are removed by covariance before this derivative estimate, including for complex λ near the real group.

Write T_j=Z_jY_jexp(ir_j), with r₀=0. In right logarithmic coordinates the propagated error has Lipschitz factor 1+C((δ_u+ρ)s_{j+1}+|r_j|), and the new product error is Cδ_uρs_{j+1}². The bootstrap |r_j|≤Cδ_uρs_j² is preserved: after division by s_{j+1}² the old term has factor L⁻²(1+O(δ_u+ρ)), strictly below one. Thus, enlarging the fixed constant and taking the small parameters sufficiently small, one may write

$$
|r_{j+1}|\leq\left(1+C(\delta_u+\rho)s_{j+1}\right)|r_j|
+C\delta_u\rho s_{j+1}^2,\qquad r_0=0\;.
$$

Since ∑_{l≤j}s_l and ∑_{l≤j}s_l² are bounded by fixed multiples of s_j and s_j², respectively, |r_j|≤Cδ_uρs_j². CMP98 (213)–(214), with u₁=I, give (1/i)log Y_j=Q′_jλ+O(ρ²s_j). Hence the terminal right-ordered constraint is

$$
\frac1i\log\left(m_k(u)^{-1}m_k(ue^{i\lambda})\right)
=Q'\lambda+C_{\mathrm R}(u,\lambda),\qquad
|C_{\mathrm R}(u,\lambda)|\leq C(\delta_u+\rho)\rho\;.
\tag{54}
$$

The bounds are analytic on the stated C¹ ball and independent of k. Cauchy differentiation bounds the derivative of the remainder by C(δ_u+ρ). With H′=G′²Q′*(Q′G′²Q′*)⁻¹, as in REG (1.91), solve X=C_R(u,λ−H′X) by contraction. This produces an analytic correction D_R(u,λ), with D_R(u,0)=0, |D_R(u,λ)|≤C(δ_u+ρ)ρ and ‖H′D_R(u,λ)‖_{C¹}≤C(δ_u+ρ)ρ. Since Q′H′=I, λ_phys=λ−H′D_R(u,λ) changes (54) into Q′λ. The exact mean condition is therefore imposed by Q′λ=0.

#### Openness and closedness along the path

Suppose an orbit at t has a Landau representative a_t satisfying (53). Take relative axial representatives Φ_s of the nearby orbits, and apply the same gauge u_t⁻¹ to them. At fixed η the resulting potentials \widetilde a_s converge to a_t in C¹ as s→t. The group means stay in their fixed charts. The associated u_t satisfies the averaged regularity conditions (166)–(167) with δ_u≤C|a_t|: this is the telescoping of CMP98 (105)–(108), as in REG (1.70)–(1.74), using |Q_j(U₀,ηa_t)|≤Cs_j|a_t| and the geometric sum of the s_j. No fine derivative bound on u_t is assumed.

Use the right-ordered linearisation (54), and set ℓ=λ−H′D_R(u_t,λ), v=exp(iℓ). The direct group product in REG (1.81)–(1.82), followed by BCH, gives

$$
a_{\mathrm{new}}
=e^{-i\operatorname{ad}\ell}\widetilde a_s
+g(i\operatorname{ad}\ell)D_0\ell+\eta E_2,\qquad
|E_2|\leq C\left(|D_0\ell|^2+|\widetilde a_s|\,|D_0\ell|\right)\;.
$$

The analytic function g is the one in CMP98 (33), with g(0)=I. The pure gauge quadratic term is retained. Applying D₀* gives g(i ad ℓ)Δ₀ℓ+e^{-i ad ℓ}D₀*\widetilde a_s+E₃, where |E₃|≤C(|D₀ℓ|²+|\widetilde a_s||D₀ℓ|). For the last term use the bounded operator ηD₀* on E₂; the derivative of g contributes another term of size C|D₀ℓ|². These bounds are analytic in the C¹ variables and contain no inverse mesh factor.

Since Q′λ=0, RΔ₀λ=Δ₀λ. On the range of R the operator I+R(g(i ad ℓ)−I)R is invertible by a Neumann series for |ℓ| small. The term Δ₀H′D_R is retained as a remainder. In fact, with K=(Q′G′²Q′*)⁻¹ and unit-scale mass coefficient one, Δ₀H′=G′Q′*K−Q′*, which is bounded from coarse ℓ∞ to fine ℓ∞ by the scalar inverse bounds. After isolating Δ₀λ, every remainder has fine supremum norm at most C(δ_u+ρ+‖\widetilde a_s‖_{C¹})ρ and vanishes at λ=0. Multiplication by G′ and Cauchy differentiation on a slightly larger C¹ ball therefore give

$$
\lambda=-G'RD_0^*\widetilde a_s+\mathcal N_s(\lambda),\qquad
\mathcal N_s(0)=0,\qquad
\operatorname{Lip}_{C^1}\mathcal N_s
\leq C\left(\delta_u+\|\widetilde a_s\|_{C^1}+\rho\right)<\frac12\;.
\tag{55}
$$

The mean projection and scalar inverse have the same fixed-unit-scale bounds as in REG §D. In particular Q′G′R=0, so the map takes values in ker Q′. This calculation uses the potential and its first derivatives only, not a divergence-of-curvature bound on F_s. Since RD₀*a_t=0, the forcing tends to zero as s→t; contraction gives λ→0. The corrected potential has |a_new|<δ and satisfies both the Landau equation and the exact modified constraint, because the total gauge is u_tv and m_k(u_tv)=I. The a priori estimate (53) then applies again. This proves openness of the set of t admitting the small chart representative.

For closedness, work at a fixed η. The site-gauge group is a finite product of compact groups. Along a sequence of such t, choose convergent gauges. The bounds (53) keep the relative logarithms strictly inside one chart. CMP98 (105)–(108) also bound the mean-gauge variables and their averaged increments by Cε, so their logarithms remain inside the same fixed domains. The Landau equation, mean constraint and original field path pass to the limit. With C_*ε<δ, the limit remains an interior small representative. The set is nonempty at t=0, open and closed in [0,1], so it is the whole interval.

Thus the candidate conclusion is that the entire path has relative Landau representatives satisfying (53). Choosing C_*ε≤r/4 and applying VAR Proposition 3 puts every orbit in the exact constraint chart of §5.7. This is a deterministic gauge choice for gauge-invariant actions and orbit distances; it changes no integration measure.

### 5.11 The variational comparison and the real background estimate — inactive, unreviewed candidate

Let U_c=U^{(n)}(V), U_f=U^{(n+1)}(V), h=L^{-n}, η=h/L and W=M U_f. Section 5.8 puts W in the regular unit-scale class and §5.7 gives its exact constraint coordinate z_W about U_c. Its Landau potential is a_W=z_W−HD(z_W). REG Theorem 2 bounds the two second-order operators on a_W. VAR (139)–(140) bound these operators on HB by C|B| at unit scale. Since D(z_W)=O(ε²), the identity z_W=a_W+HD(z_W) therefore gives the same second-order bounds Cε on z_W.

For 0≤t≤1 put z_t=(1−t)z_W and a_t=z_t−HD(z_t). Both first- and second-order bounds stay at Cε. REG Proposition 7 returns e^{iha_t}U_c to its relative axial representative A_t, which is regular at unit scale and satisfies M^nA_t=V exactly. Its local C^{1,β} gauges are supplied by REG Proposition 6, uniformly in t. The path is continuous; the group means and logarithms used in its construction stay in their small domains. Its endpoints are an axial representative of W and U_c.

Take the actual one-step minimal orbits F_t=L_h(A_t). They depend continuously on t by VAR Proposition 9, using local analytic sections along the compact parameter interval; the number of sections may depend on η and is not used in any estimate. Their original constraints give M^{n+1}F_t=M^nA_t=V. By §5.9 their covariant curvature norms C^α(F_t), α=β/2, are bounded by Cε uniformly in t and h.

At t=0 this orbit is the orbit of U_f, up to the extension of the coarse gauge used at W. Indeed, U_f is critical for variations preserving M^{n+1}U_f=V. Variations preserving its first average W are among those variations. It lies in the one-step regularity class for the input W, so uniqueness of the one-step critical orbit in VAR identifies it with L_h(W). This uses criticality and uniqueness, not the variational inequality being proved. Choose the initial representative U₀ accordingly; its action equals S_η(U_f).

The candidate continuation in §5.10 puts F_1=L_h(U_c) in the small exact constraint chart about U₀. Inequality (35) would then yield

$$
S_\eta(U_f)\leq S_\eta(L_h(U_c))\;,
$$

which is exactly (47). This application does not require claiming that F_1 has a unit-scale force bound; (35) was proved on the coordinate chart itself.

Combining (47) with (23) at U_c and at W, and using U_f=L_h(W) as an orbit, would give the global estimates

$$
\begin{aligned}
|S_\eta(U_f)-S_h(U_c)|&\leq C\varepsilon^2h^{\beta/2}|T|,\\
0\leq S_h(W)-S_h(U_c)&\leq C\varepsilon^2h^{\beta/2}|T|,\\
\mathfrak d_h(W,U_c;T)^2&\leq C\varepsilon^2h^{\beta/2}|T|\;.
\end{aligned}
\tag{56}
$$

Here |T| is physical volume at the fixed coarse scale. The lower inequality follows from (46), and the first upper inequality in the opposite direction uses (23) at W. The constants absorb the sum of the two consistency errors. Equations (12) and (19) would consequently give, on each fixed physical torus and for each specified square,

$$
|W_\chi(C_\eta;U_f(V))-W_\chi(C_h;U_c(V))|
\leq C_{C,T}\varepsilon h^{\beta/12}\;.
\tag{57}
$$

This rate is geometric in n and would give uniform convergence of the classical background insertion and of the global minimal action on the common real regular coarse domain. The proof of the continuation, particularly (54)–(55), is new and requires focused review before (47), (56) or (57) are accepted. Even their acceptance would not prove the local shell estimate, complex marked-activity comparison or the full renormalised expectation.

## 6. The Cutoff Mark in the Interacting Polymer Expansion

The object to bound is (1). The first application of the following calculation is the comparison of the numerator and normalising integral in CRE (3.44)–(3.46), and of their Wilson-marked versions. The calculation uses the actual conditional kernel of RG2 (2.5)–(2.14). CRE pp.276–278 explicitly transfers this expansion to the fluctuating region, including the inherited E-, R- and boundary terms. No replacement of the inherited law by its Gaussian part is made.

### 6.1 The differentiated conditional kernel

Fix a selected term of RG2 (2.14): the potential labels, bad-bond set, seed, final domain and weakening parameters are fixed. Write C for its restricted covariance and Γ for its boundary-coupling operator. Put P=C⁻¹. In real orthonormal coordinates on the free Lie algebra variables, its integration density, before the Mayer and weakening integrations, is

$$
\begin{aligned}
K(B,X)
={}&(2\pi)^{-n_B/2}(\det P)^{1/2}
\exp\left(-\frac12 B^{\mathsf T}PB-B^{\mathsf T}\Gamma X
-\frac12X^{\mathsf T}\Gamma^{\mathsf T}C\Gamma X\right)\\
&\quad\cdot\Theta(B)\exp V(B),\qquad
V(B)=\sum_{Y\in\mathcal D}\tau(Y)\mathbf V_k(Y,B)\;.
\end{aligned}
\tag{58}
$$

The measure for X is the standard Gaussian measure in the original conditioning identity, restricted to the final domain as in RG2 (2.14). Θ is exactly its product of small-field and complementary bad-bond indicators, with the selection's sign kept outside K. The inherited interactions enter V through CRE (3.27), (3.29) and p.276. The complex square root of the determinant is continued from the positive real kernel. Transposes and pairings are bilinear on the complex domain.

First consider a differentiable path P_t, Γ_t, V_t on a common carrier, with Θ fixed, and with the original selected-integral bounds valid throughout the path and its weakening contours. This is a calculation of the response to a specified change of these operands. The existence and small size of such a comparison for the two cutoff runs are not assumed to follow from the value bounds on either run.

Let C_t=P_t⁻¹. Differentiating every factor of (58), including its determinant and compensating exponential, gives

$$
\begin{aligned}
\dot K_t&=K_t\mathcal S_t,\\
\mathcal S_t
&=\frac12\operatorname{Tr}(C_t\dot P_t)
-\frac12B^{\mathsf T}\dot P_tB-B^{\mathsf T}\dot\Gamma_tX\\
&\quad-\frac12X^{\mathsf T}
\left(\dot\Gamma_t^{\mathsf T}C_t\Gamma_t+
\Gamma_t^{\mathsf T}C_t\dot\Gamma_t-
\Gamma_t^{\mathsf T}C_t\dot P_tC_t\Gamma_t\right)X
+\dot V_t(B)\;.
\end{aligned}
\tag{59}
$$

This follows from Ċ_t=−C_tṖ_tC_t and ∂_t log det P_t=Tr(C_tṖ_t), directly in the exponent of (58). It requires no symmetry assertion about the analytically continued operators on the weakening contours. In particular the mixed term involving X survives conditioning. There is no replacement of the conditional integral by independent integrals on its subregions. The comparison parameter t is distinct from the Mayer parameters t(Y) of RG2; those parameters are fixed when this derivative is taken.

For a closed, gauge-invariant scalar insertion f_t, put Z_t=∫K_t and F_t=Z_t⁻¹∫f_tK_t, with both B and X integrated. Whenever Z_t≠0, differentiation gives

$$
\dot F_t
=\frac1{Z_t}\int\left[\dot f_t+(f_t-F_t)\mathcal S_t\right]K_t
\,\mathrm dB\,\mathrm d\mu_0(X)\;.
\tag{60}
$$

All products in (60) are formed before estimates. RG1 (2.16) and (3.29) give B(b)↦Ad(u(b₋))B(b), together with the transformed external data. This preserves the free-bond carrier: it changes each fibre and does not change its bond label, so the excluded b₀(c) remain excluded. Geometric restrictions commute with this action. The operator construction intertwines the actions, and the covariance square root in RG2 (2.7) does also, by its resolvent representation; hence X has the same adjoint transformation on its carrier. For real gauges these actions are orthogonal, and each complete quadratic contraction and trace in (59) is invariant. For complex gauges the extension is bilinear-orthogonal; invariance of the integrated selected expressions follows by analyticity, as explicitly stated at the end of RG2 p.21, rather than by an unproved complex change of integration contour. The same gauge transformation is applied to the whole t-path. For a Wilson insertion, gauge factors cancel along successive links inside its ordered closed trace before any estimate.

One selected term can be signed or complex and need not have nonzero integral. Equation (59), rather than a normalised expectation for that term, is inserted into the selected expansion. Equation (60) applies to the positive real conditional functional, or to its nonvanishing analytic continuation after summing the selections. It is not used to divide by an individual selected activity.

### 6.2 Paying for the mark inside the fluctuation integral

Here is a quantitative bound at the selected-integral level. Let n_Z be the number of real B- and X-coordinates read by a selected term, enlarged if necessary to the number available in Z. Let d_Z bound, uniformly over every selection with final domain Z, its original weakening and Mayer contours, and the comparison path, the operator norms of Ṗ_t and Γ̇_t and the bound

$$
|\dot V_t(B)|\leq d_Z(n_Z+|B|^2)\;.
\tag{61}
$$

The definition includes the factors τ(Y) in (58); they are not dropped from the difference norm. Their radii in RG2 (2.18) are large. Thus (61) requires control of the marked potential relative to the selected potential majorant, not merely an absolute bound on each potential difference. Assume the same uniform bounds on C_t and Γ_t as in the selected-integral estimate. Then (59) gives

$$
|\mathcal S_t|\leq C d_Z(n_Z+|B|^2+|X|^2)\;.
\tag{62}
$$

The required moment is paid within RG2 (2.15)–(2.26). After taking absolute values, the determinant quotients, the entire interaction and the complementary-cutoff factors are bounded there by (2.17), (2.20)–(2.22). The remaining Gaussian integral is exactly (2.23). The matrices C and Γ in the next display are its real reference matrices at zero weakening parameters and real external data, not the complex matrices in (58). At α₅=0 its joint precision in (B,X) is

$$
\begin{pmatrix}
P&\Gamma\\
\Gamma^{\mathsf T}&I+\Gamma^{\mathsf T}C\Gamma
\end{pmatrix}\;.
\tag{63}
$$

Its quadratic form is |C⁻¹ᐟ²B+C¹ᐟ²ΓX|²+|X|². The uniform bounds on C, C⁻¹ and Γ give a positive lower bound c_* independent of n_Z. The moment estimate requires α₅≤c_*/2, explicitly, so that the Gaussian measure after the payment has covariance norm at most 2/c_*. Its second moment is at most 2n_Z/c_*. Its normalising integral is bounded by exp(Cα₅|Z|), as in (2.24)–(2.25). With reference operator bounds uniform in M, the constant order is compatible: take M so that the exponential contribution O(e^{−δ₀M/3}) is at most c_*/8, then α₀, α₁, α₄ and γ₂ so their total contribution is at most 3c_*/8 and they satisfy the smaller source bounds (LM)⁴α_i≤1; finally reduce the coupling for (2.31). Uniform reference operator bounds and this margin are part of the hypotheses of the transfer estimate, not consequences of (61).

Let I_sel,t denote the full selected integral (2.14), including the Mayer and weakening integrations, and let B_sel be the right side of (2.26), under the conditions just specified. It includes the bad-bond factor, the factors for every selected potential, and the weakening decay. Carrying the polynomial through the absolute contour integrals gives

$$
\left|\partial_t I_{\mathrm{sel},t}\right|
\leq C d_Z n_Z B_{\mathrm{sel}}\;.
\tag{64}
$$

The small contour factors in B_sel are available after these integrations, not at a fixed point of a contour. This is a moment estimate for a marked term of the interacting expansion: the interaction and selectors have been paid for by the published majorant before the Gaussian moment is evaluated. No Gaussian probability estimate is asserted for the original inherited law.

At the current scale n_Z≤C_{G,L,M}#Z. For a fixed positive reserve ε in the volume exponent, the factor n_Z can be paid using

$$
\#Z\,e^{-\varepsilon\#Z}\leq\frac1{e\varepsilon}\;.
\tag{65}
$$

The reserve can be taken after, rather than inside, the source's resummation. At fixed Z the factors d_Zn_Z are uniform across selections, so the positive sums of (2.26)–(2.38) first give C d_Zn_Z C₃ε₁exp(−(1−8δ)Lκd_{k+1}(Z)/2). The cube-count/tree-size comparison of (2.30), with an additive constant for a smallest support, bounds #Z by C(1+d_{k+1}(Z)). Spend δLκd_{k+1}(Z)/2 at this point to absorb n_Z. The resulting marked activity has exponent (1−9δ)Lκ/2. This extra loss is explicit; it is not one of the margins already spent in the source's (1−3δ) to (1−8δ) sequence. If subsequent exponentiation also requires the two margins of (2.39)–(2.41), take the auxiliary δ smaller from the outset, for example with (1−11δ)L/2≥1. This changes the proof constants, not the physical transformation. A root insertion obeying |f_t|≤M_f on the integration and contour domains multiplies (64) by M_f; a derivative of the insertion has its own selected integral. For the Wilson application the bound must be supplied for the full contracted insertion, with the original perimeter/corner extraction retained.

For an unselected, unrestricted normalised Gaussian kernel, the integral of its part of (59) vanishes. That cancellation does not remove the field-dependent Gaussian normalising prefactor of the physical density. CRE (3.33) keeps that prefactor as a log determinant, and its difference is a separate vacuum/action mark in the outer density. It must remain in the comparison of (1).

This calculation produces a bound in terms of d_Z. It does not prove that d_Z decays with cutoff depth. In particular, replacing Ṗ_t or Γ̇_t by twice their individual bounds supplies no such decay.

### 6.3 Cutoff indicators and the full conditional functional

Hard cutoffs are compared by finite differences. For an ordered finite list of actual selector factors θ_{i,b},

$$
\prod_b\theta_{1,b}-\prod_b\theta_{0,b}
=\sum_b(\theta_{1,b}-\theta_{0,b})
\prod_{c<b}\theta_{1,c}\prod_{c>b}\theta_{0,c}\;.
\tag{66}
$$

The difference factor is kept as a signed selector mark in the original selected integral. It is supported on the symmetric difference of the two tests. For a simple bond threshold it is the corresponding shell, but the full CRE tests also depend on the retained fields and reconstruction. No derivative of an indicator, absolute-continuity assertion for its boundary, or independent probability for a retained variable is used.

For example, keeping the smooth kernel K fixed while changing Θ₀ to Θ₁ gives the exact numerator for a normalised difference

$$
Z_1(F_1-F_0)=\int(f-F_0)(\Theta_1-\Theta_0)K
\,\mathrm dB\,\mathrm d\mu_0(X)\;.
\tag{67}
$$

Changing the insertion contributes ∫(f₁−f₀)Θ₁K. Formula (66) then puts exactly one selector mark in each term. A rare-event bound uniform in the cutoff controls its size only. A Cauchy estimate requires a bound on these marked integrals that tends to zero, or a proved contraction of their inherited contribution.

### 6.4 The connected denominator comparison

The following estimate supplies the denominator part of the marked expansion. It applies directly to the polymer quotient in CRE (3.45), or to the quotient q_ξ(𝒜) in V5, `eq:fixed-probe-active-pairing`. The polymers and incompatibility relation are those of the expansion under consideration; a polymer is incompatible with itself. At fixed volume, let k₀(P), k₁(P) be the two scalar vacuum-activity lists on a common labelled polymer set. A label absent at one endpoint is assigned activity zero. Set

$$
k_t(P)=(1-t)k_0(P)+tk_1(P),\quad
w(P)=|k_0(P)|+|k_1(P)|,\quad
q(P)=|k_1(P)-k_0(P)|\;.
\tag{68}
$$

This interpolation is an algebraic interpolation of the two gas expansions. It asserts no interpolation or factorisation of the physical measures. Let a(P)>0 be charges and d≥0 a difference size. Suppose the following strengthened rooted sums hold for every polymer P:

$$
\sum_{Q\not\sim P}w(Q)e^{2a(Q)}\leq\frac{a(P)}4,\qquad
\sum_{Q\not\sim P}q(Q)e^{2a(Q)}\leq d\,\frac{a(P)}4\;.
\tag{69}
$$

For a fixed root support A, suppose the same two sums over Q incompatible with A are bounded by a_A/4 and da_A/4. For a family of active polymers one may take a_A=∑_{P∈𝒜}a(P) when incompatibility with their union implies incompatibility with at least one member, as for the cube/wall relation in RG2 (2.11). Existing support and tree weights can be included in w and q before (69); they cannot be omitted from its verification. Zero extension of unmatched labels is only an algebraic convention: on those labels q=w, and a small d requires a separate small bound for their contribution. No pairing or smallness of such labels in the two cutoff runs has been established here.

Let Ξ_t be the compatible-family partition function and Ξ_t^[A] its restriction to polymers compatible with A. Absolute cluster convergence follows from (69), and

$$
\frac{\Xi_t^{[A]}}{\Xi_t}=e^{-L_t(A)},\qquad
L_t(A)=\sum_{n\geq1}\frac1{n!}
\sum_{P_1,\ldots,P_n}
\varphi^T(P_1,\ldots,P_n)
\mathbf1_{\{\exists i:P_i\not\sim A\}}
\prod_{i=1}^nk_t(P_i)\;.
\tag{70}
$$

This is the connected cancellation between the two copies of the denominator in CRE (3.45). A derivative of (70) inserts one difference activity into a connected cluster that hits A. The other vertices carry k_t. Disconnected vacuum clusters have already cancelled.

Here is the marked-tree bound with constants. For an unweighted root P, let T(P) be the positive rooted-tree majorant with non-root weights w. Its recursion is T(P)=exp(∑_{Q≁P}w(Q)T(Q)); tree-height truncation and (69) give T(P)≤e^{a(P)/4}. Let T_q(P) be the sum with exactly one non-root vertex carrying q in place of w. Differentiating the finite-height recursion and increasing its height gives

$$
T_q(P)=T(P)\sum_{Q\not\sim P}\bigl(q(Q)T(Q)+w(Q)T_q(Q)\bigr)
\leq d\,a(P)e^{a(P)}\;.
\tag{71}
$$

For the inequality, insert the claimed upper bound on the right at the preceding height. The first sum is at most da(P)/4. In the second use a(Q)e^{a(Q)}≤e^{2a(Q)}, giving another da(P)/4. The resulting upper bound da(P)e^{a(P)/4}/2 is smaller than the claimed one, which closes the height induction. All sums are positive majorants; no cancellation is used after absolute values.

To bound a cluster hitting A, choose one of its hitting vertices as root. This overcounts a cluster only by its number of hitting vertices. The factorial 1/n! becomes the pinned factorial 1/(n−1)!, and the hard-core tree-graph inequality applies. The difference mark is either at the root, with weight q(P)T(P), or below it, with weight w(P)T_q(P). Consequently

$$
|L_t(A)|\leq\frac{a_A}4,\qquad
|\dot L_t(A)|\leq\frac{d a_A}2,\qquad
\left|\frac{\Xi_1^{[A]}}{\Xi_1}-\frac{\Xi_0^{[A]}}{\Xi_0}\right|
\leq\frac{d a_A}2e^{a_A/4}\;.
\tag{72}
$$

The constants in (72) are independent of the total torus volume. The charge belongs to the marked root support, not to every polymer in the torus. This proves the quantitative denominator comparison once the marked activity sum in (69) has been estimated.

For the centred expansion of V5, write Q_i(𝒜;f_i) for its pairing with the product of zero-mass probe measures and q_i(𝒜)=Ξ_i^[∪𝒜]/Ξ_i. On a common compatible-family index set and common probe carriers, its finite-volume identity gives

$$
\begin{aligned}
F_1-F_0={}&f_1(0)-f_0(0)\\
&+\sum_{\varnothing\ne\mathcal A\ {\rm compatible}}
\left(q_1(\mathcal A)\,[Q_1(\mathcal A;f_1)-Q_0(\mathcal A;f_0)]
+[q_1(\mathcal A)-q_0(\mathcal A)]Q_0(\mathcal A;f_0)\right)\;.
\end{aligned}
\tag{73}
$$

For an ordering of 𝒜, the measure difference in the first pairing is the sum over P∈𝒜 of the tensor product with ν̂₁,Q for Q<P, ν̂₁,P−ν̂₀,P at P, and ν̂₀,Q for Q>P. The insertion difference is paired with the product of the endpoint-1 measures. Each scalar pairing contains the full closed contraction before estimation. The contribution of the second term of (73) is at most (d/2)∑_𝒜 a_𝒜e^{a_𝒜/4}|Q₀(𝒜;f₀)|. Controlling this sum requires the marked-pairing bounds, with these weights; (72) alone does not supply them. Thus the difference includes both a Wilson mark and a cutoff mark, either in the active pairing or in a vacuum cluster connected to it. A difference of the reconstructed Wilson functions remains inside (73); no separate classical estimate for it is imported. The exterior-response term in V5, `eq:c-physical-numerator`, must also be compared and is not part of the centred t=0 gas in (73). Neither the common indexing nor the needed uniform pairing bounds have been constructed for the two full cutoff runs.

### 6.5 Large-field normalisation and the inherited law

The original R-operation remains in the calculation. Its local operation T′_k(X) is LFR2 (1.71), with the sums over old regions, integrations over old fields, Haar factor, axial gauge fixing, Wilson action, fluctuation quadratic form, V(X^∼), and every vacuum normaliser. In (1.91) it acts on the product of all the selected interaction factors, not on each factor separately. The component factorisation there is used only where Bałaban's construction establishes it.

At real external data let \(\mathsf T_t\) be this positive integral operation along a change of its full weight on a fixed carrier and fixed selectors. Put m_t=\(\mathsf T_t1\), \(\mathsf F_t=\mathsf T_tf_t/m_t\), and let Ψ_t be the logarithmic derivative of that full weight, including the inherited terms. Then

$$
m_t\dot{\mathsf F}_t
=\mathsf T_t\bigl[\dot f_t+(f_t-\mathsf F_t)\Psi_t\bigr]\;.
\tag{74}
$$

For bounded Ψ_t and f_t, positivity gives the direct, interacting estimate below. Boundedness with a useful uniform constant for the complete large-field score has not been established; (75) cannot be applied to that score merely from the unmarked bound (1.89).

$$
|m_t\dot{\mathsf F}_t|
\leq m_t\|\dot f_t\|_\infty
+2m_t\|f_t\|_\infty\inf_{c\in\mathbb C}\|\Psi_t-c\|_\infty\;.
\tag{75}
$$

The multiplier m_t is kept: LFR2 (1.89) makes it small for an R-component. Dividing this estimate by m_t and then forgetting to restore m_t in (1.91) would lose precisely that gain. At complex data (1.73)–(1.75) give the corresponding factors involving sup|σ|, rather than positivity. A Wilson insertion with attached species is bounded by its actual attached-insertion bound; it is not automatically bounded by one. Field-independent constants in Ψ_t cancel in (74), but field-dependent component masses still enter the outer density.

For changing selectors, use (66) at the unnormalised level. For endpoint integral operations on a common carrier the corresponding exact finite-difference formula is

$$
m_1(\mathsf F_1-\mathsf F_0)
=(\mathsf T_1-\mathsf T_0)(f_0-\mathsf F_0)
+\mathsf T_1(f_1-f_0)\;.
\tag{76}
$$

This formula identifies the centred difference to insert into LFR2 (1.91). Bounds (1.89) and (1.97) on each endpoint alone do not bound (76) by a quantity decaying with cutoff depth.

Finally the exterior branch weights must be compared. At a real, positive common-carrier interpolation of the full physical integral, let ξ denote the entire retained history, w_t(ξ) its outer density, Z_{ξ,t} its conditional partition function and F_{ξ,t} its normalised closed insertion. With

$$
\mathrm d\pi_t(\xi)
=\frac{w_t(\xi)Z_{\xi,t}}{Z_t}\,\mathrm d\xi,\qquad
F_t=\int F_{\xi,t}\,\mathrm d\pi_t(\xi)\;,
$$

ordinary differentiation of the full numerator and denominator yields

$$
\dot F_t
=\int\dot F_{\xi,t}\,\mathrm d\pi_t(\xi)
+\int(F_{\xi,t}-F_t)\,
\partial_t\log(w_t(\xi)Z_{\xi,t})\,\mathrm d\pi_t(\xi)\;.
\tag{77}
$$

Equation (77) is a disintegration identity for the original full law. In particular the second term is an inherited-history mark. It does not vanish merely because the first term has a local connected expansion. When no differentiable interpolation of histories has been constructed, the original finite-difference measure ℋ_K, rather than (77), remains the definition of the comparison.

### 6.6 The coupling mark in the actual R-denominator — awaiting review

The denominator in LFR2 (1.1) is a normalised interacting small-field integral used by the original R-operation. Its coupling response can be bounded probabilistically without a factor g_k⁻² from differentiation on a shrinking field domain. The following calculation concerns this component of the cutoff mark, with its geometry, external data, background construction and selector fixed. Changes of those operands remain separate terms of the same comparison.

Fix one component Λ occurring in LFR2 (1.1), an axial gauge G₀, and its external data. Put x=g_k⁻² and, on the free Haar variables v on Λ, define

$$
\begin{aligned}
S(v)&=A\bigl(\zeta_0,U_{k,Z}(vV_\Lambda)\bigr),\qquad
S_0=A(\zeta_0,U_0),\\
r_x(v)&=\delta_{G_0}(v)\chi(v)e^{-xS(v)},\qquad
D_x=\int r_x(v)\,\mathrm dv,\qquad
\mathrm d\mu_x(v)=D_x^{-1}r_x(v)\,\mathrm dv\;.
\end{aligned}
\tag{78}
$$

The delta functions mean restriction to the source's free axial-gauge variables, not an additional integration factor to estimate. The measure and action in (78) are exactly the denominator of LFR2 (1.1); in particular the nonlinear reconstructed field and Haar density remain present. The current-scale domain is contained in a cube of side 100M, so its number of free real variables is bounded in terms of M and the group, independently of cutoff depth. This is the geometry used explicitly in LFR2 (1.8)–(1.11).

Differentiation in x is at fixed χ and fixed S. At real regular external data, the centred derivative is

$$
\partial_x\mu_x
=-\left(S-\mu_x(S)\right)\mu_x\;.
\tag{79}
$$

The field-independent term S₀ cancels here exactly. To estimate the remaining mark, use the source's actual change of variables v=exp(ig_kB), including its Haar density. LFR2 (1.2) expresses x(S(v)−S₀) as a quadratic form in B plus a linear term and the nonlinear remainder. The quadratic form has a uniform upper bound and the strictly positive lower bound (1.9), both with constants allowed to depend on M. The linear term is uniformly bounded by (1.6), and the nonlinear term is bounded on the full cutoff box by O(g_k^{1−β})|Λ|, as stated immediately after (1.2). For fixed M these last two bounds can be made at most one. The Haar density σ(g_kB), a finite product on this component, is bounded above and below on the box for small g_k. Thus the full residual density is bounded above by a constant times exp(−c_M|B|²), while its integral is bounded below by a positive constant depending on M. The latter is also the real version of (1.10)–(1.11). No omitted inherited factor is part of D_x: the other integrations in (1.1) are in its numerator and remain there.

It follows by integration of the quadratic moment against this majorant that

$$
\int\bigl|x(S-S_0)\bigr|\,\mathrm d\mu_x\leq C_M\;.
\tag{80}
$$

The Gaussian here bounds the already specified nonlinear denominator integral; it is not used as its probability law. From (79)–(80), with total variation denoting the mass of the absolute signed measure,

$$
\|\partial_x\mu_x\|_{\mathrm{TV}}
\leq 2\int|S-S_0|\,\mathrm d\mu_x
\leq\frac{2C_M}{x}=2C_Mg_k^2\;.
\tag{81}
$$

Consequently, on a real coupling interval where these same fixed-selector estimates hold, integration gives

$$
\|\mu_{x_1}-\mu_{x_0}\|_{\mathrm{TV}}
\leq2C_M\left|\log\frac{x_1}{x_0}\right|
\leq\frac{2C_M|x_1-x_0|}{\min(x_0,x_1)}\;.
\tag{82}
$$

The changing-selector contribution is still (66), rather than a derivative of χ in (79). The bound is on this original R-denominator kernel only; it is not a total-variation estimate for the full effective law. The statement so far is for real external data. A complex-domain version must additionally retain the absolute-density and denominator bounds of (1.10)–(1.11); it is not inferred from positivity.

To put this bound into its actual caller, write one term of LFR2 (1.1), before the spectator integrations, as a numerator integral L_t multiplied by the density μ_t of its R-denominator. Let N_t be the same numerator integral with the complete Wilson insertion. Its integration includes every numerator factor in (1.1); the old operations explicitly omitted by Bałaban are still spectator operations and are applied afterwards. Conditional on their variables, the two output densities are L_tμ_t and N_tμ_t. Their derivatives are

$$
\partial_t(L_t\mu_t)=\dot L_t\mu_t+L_t\dot\mu_t,\qquad
\partial_t(N_t\mu_t)=\dot N_t\mu_t+N_t\dot\mu_t\;.
\tag{83}
$$

For a fixed centring constant F, the marked pair is therefore

$$
\partial_t\bigl((N_t-FL_t)\mu_t\bigr)
=(\dot N_t-F\dot L_t)\mu_t+(N_t-FL_t)\dot\mu_t\;.
\tag{84}
$$

The second term is a zero-mass signed kernel on Λ. Equation (81) bounds its coupling part by 2C_Mg_k²|ẋ_t| times the mass of the complete numerator factor |N_t−FL_t|. There is no inverse power of the possibly tiny D_t in this bound. It must be retained when the output is localised and combined with other factors; its zero mass is not a bound on its absolute integral, and cannot justify discarding it under a nonconstant test. The first term in (84) is the difference mark in the full numerator operation, including the inherited histories. Its estimation is still required.

This derives the g_k² coupling gain for the R normalising kernel, an actual factor of the full marked comparison. It does not estimate the change of that kernel's background with cutoff depth, or the other term of (84).

### 6.7 Combining the mark before estimating changes of representation

The precision and interaction marks in (59) need not be estimated separately. In particular, a change of Gaussian reference at fixed physical integrand has an exact cancellation. This is relevant to comparing the two runs under their common physical T-map: it prevents a choice of quadratic splitting from being counted as a new physical cutoff source.

Fix a finite-dimensional free-variable carrier, a selector Θ and the full conditional density Θ(a)e^{-A_t(a)} da. Here A_t includes every inherited interaction, boundary term and Jacobian on this carrier. Let P_t be any differentiable positive symmetric reference precision and write

$$
\begin{aligned}
\mathfrak n_t&=(2\pi)^{n/2}(\det P_t)^{-1/2},\\
V_t(a)&=-A_t(a)+\frac12a^{\mathsf T}P_ta,\\
\Theta(a)e^{-A_t(a)}\,\mathrm da
&=\mathfrak n_t\Theta(a)e^{V_t(a)}\,\mathrm d\mu_{P_t^{-1}}(a)\;.
\end{aligned}
\tag{85}
$$

This is an exact decomposition of the same interacting density, not a change to its probability law. At fixed a, the three contributions to its logarithmic derivative add to

$$
-\frac12\operatorname{Tr}(P_t^{-1}\dot P_t)
+\left(\frac12\operatorname{Tr}(P_t^{-1}\dot P_t)
-\frac12a^{\mathsf T}\dot P_ta\right)
+\left(-\dot A_t(a)+\frac12a^{\mathsf T}\dot P_ta\right)
=-\dot A_t(a)\;.
\tag{86}
$$

Thus the reference-precision mark cancels pointwise with the compensating quadratic interaction and normalising prefactor. If A_t is fixed, their combined mark is identically zero, before integration or absolute values. Multiplication by a complete closed Wilson insertion preserves this identity. It also preserves its gauge invariance: aᵀṖa is a complete invariant contraction when P transforms with the adjoint action on both indices. For changing A_t, the source remaining in (86) is the derivative of the full physical density, not the derivative of the chosen reference precision.

The compensation must be included before the Mayer expansion. The identity e^{V_t}∂_tV_t=∂_te^{V_t}, expanded over the original interaction labels, pairs the quadratic compensation with the reference mark. Its subsequent conditioning and localisation are linear operations on that combined integrand. It would be incorrect to expand the two marks, take absolute activity norms separately, and then appeal to (86). Nor does (86) identify a change of the actual input action between fine cutoffs as a reference change.

Selector partitions admit an equally exact common indexing at the level of the physical T-integral. At fixed volume let {χ^0_h(U)} and {χ^1_l(U)} be the two complete partitions of unity on the same current physical lattice, including their large-field branches. CRE (3.2)–(3.3) gives such partitions explicitly. Their joint refinement is χ^0_hχ^1_l. For any integrable scalar gauge-invariant insertion f and full input density ρ,

$$
\sum_h\int f\rho\,\chi^0_h\,\mathrm dU
=\sum_{h,l}\int f\rho\,\chi^0_h\chi^1_l\,\mathrm dU
=\sum_l\int f\rho\,\chi^1_l\,\mathrm dU\;.
\tag{87}
$$

The same identity holds with a bounded coarse-field test φ(MU) inserted, hence as an identity of measures after T. For two different input densities ρ₀, ρ₁ on this current lattice, the difference is exactly the sum of the jointly labelled integrals of χ^0_hχ^1_l(ρ₁−ρ₀). There is no additional physical source consisting solely of the difference of the two partitions. Earlier integrations inside each ρ_i remain that run's own integrations; (87) introduces no product law for retained fields.

On a joint branch, each endpoint's valid chart can be applied to its own copy of the same physical integration region. The two coordinate expressions for a fixed input integral are equal by change of variables, with their full Jacobians and transformed selector domains. This requires no estimate comparing their reference configurations. It is a statement about the complete branch integral. The joint refinement need not have the product-cutoff form of RG2 (2.14), so (87) does not by itself put its individual terms in the norm used in (69).

The R-operation has a narrower cancellation. For a term written as L_tμ_t, N_tμ_t in (83), changing only its normalised replacement kernel gives L_t∂_tμ_t and N_t∂_tμ_t. Their integrals over the replacement variables vanish. This is the normalisation identity of LFR1 (1.102), applied to both the vacuum and complete numerator. The original R-kernels at the two endpoints are retained. The identity does not make the two R-densities equal and does not bound the absolute values of their localised pieces. In particular it does not remove the first term of (84), which changes the inherited numerator itself.

These cancellations show why estimating every apparent change of background, quadratic splitting and selector separately is unnecessarily strong. For the full Cauchy estimate the nonzero mark must still be localised with the physical input-density and insertion differences kept together. A proof that the joint refinement and this combined mark obey the required connected norm is still needed; the integrated identities alone do not give that norm.

### 6.8 A mark on old large-field histories in the R-gas — reviewed under the stated inputs

There is an age-dependent probabilistic bound available before replacing every large-field factor by its value at the current coupling. It concerns the actual first-class component integrals in LFR2 (1.72), with all their inherited integrations retained. Unlike a uniform small-coupling bound, it tends to zero as the marked history becomes older.

Use the finite nonnegative decomposition obtained by opening every selector sum in the recursive definition of T′_k(X), before any Mayer expansion. Its labels include the P_j, Q_j, R_j tests of LFR2 p.380; the preparatory binary choices on pp.381–383 (1−χ_j^{(n)}, 1−χ′_j, 1−χ_{j,Λ}, 1−χ′); the corresponding choices nested inside T_h and the ζ factors; the induced Ω_j, Λ_j, Z_j and their component genealogies; and the coordinate/tree choices. The continuous old fields remain integrated with their original joint weight. The abbreviated (Ω,Z) list in (1.71) alone is not the definition of a complete history here.

On these labels define b for a newly created component to be its creation step; on a carry use the old b; on a merger use the minimum of the incoming indices, including a new component's index if present. In the preparatory branch where a component is kept and a new bad test occurs inside it, retain the old b. An absorbed first-class component no longer belongs to a later surviving lineage; its subsequent encoded R-terms are outside the event considered here. Thus b(X) is the earliest creation index in X's surviving lineage, the choice of j(X) used in LFR2 p.384. For 1≤m<k, insert the single indicator b(X)≤k−m on this finest nonnegative decomposition and then perform the original sums and integrations. The resulting positive sub-operation is T′_{k,m}(X). No probability law for the old fields is replaced.

Put

$$
P_{k,m}=\inf_{j\leq k-m}p_0(g_j),\qquad
B_k=\frac{2}{1+\beta_0}p_0(g_k),\qquad
\delta_{k,m}=\exp(-2P_{k,m}+B_k)\;.
\tag{88}
$$

The argument below uses only the asymptotic range δ_{k,m}≤1/2, supplied by (95). In particular no extension of CRE (2.7), printed for integer exponents, is needed here to prove δ≤1 for every m. The ordinary bound exp(−B_k) is the printed LFR2 (1.89). Retaining the creation index before its last simplification gives

$$
\mathbf T'_{k,m}(X)1\leq e^{-2P_{k,m}}
=\delta_{k,m}e^{-B_k}\;.
\tag{89}
$$

To see the retention, the factor before (1.80) is exp(−κ_j(Z)−2p₀(g_{b(Z)})). The base case (1.82) has b=1 and leaves 2p₀(g₁) outside κ₁. With no new large fields the subtraction (1.83) changes κ and leaves b unchanged. In the preparatory small-component case on pp.385–386, the new factor exp(−p₀(g_j)) pays the next lifetime, while the earlier exp(−2p₀(g_{b(Z₀)})) remains outside κ; discarding κ_j(Z₀)≥0 there does not discard that separate factor. Thus b remains b(Z₀). At a merger (1.85) subtracts 2p₀(g_{b(Z)}) from the sum of the incoming budgets, leaving this factor outside κ. In the tree step (1.86), b(Z) is one of b(X), b(Y); the uncancelled contribution of the other child is bounded below by 2p₀(g_{j+1})/(1+β₀), exactly the source comparison used in (1.87)–(1.88). Thus the induction works with the earliest creation index retained. When the current component satisfies the R eligibility conditions, (1.80) with zero remaining steps gives κ_k(X)≥0. This proves its bound with exp(−2p₀(g_{b(X)})). The history counting has already been paid in (1.79); restricting that sum to b(X)≤k−m allows the uniform factor exp(−2P_{k,m}) to be extracted before the final supremum. No extra sum over all possible marked birth locations is introduced: the mark is the single indicator of the oldest creation index.

For a paid insertion the same retention is available only after its enlarged budget has been verified at creation, in the preparatory small-component case and at mergers. Creation uses the quadratic p₀² reserve; the other two cases use the linear p₀ reserves in pp.385–387, so the creation inequality alone is insufficient. The Wilson application below uses precisely the enlarged induction and its explicit numerical conditions in D2.6 §§7.2–7.3. Given those conditions, the extra costs are paid inside κ and the unused merging surplus, with 2p₀(g_{b(Z)}) still outside κ. This is not a bound for an arbitrary unbounded score or an assertion that the original coupling window automatically pays any larger cost.

At complex external data the same restriction of the positive real operation can be used in (1.73). Its factor exp(sup|σ|) is the one already paid in (1.92); restricting the sum over histories does not enlarge sup|σ|. Thus the old-history operation has the same extra factor δ_{k,m} in that absolute majorant.

#### The age mark through the complete component gas

In the curly bracket of (1.72), replace each first-class component operation by

$$
\mathbf T'_{k}(X;z)
=\bigl(\mathbf T'_k(X)-\mathbf T'_{k,m}(X)\bigr)
+z\,\mathbf T'_{k,m}(X)\;.
\tag{90}
$$

Write Ξ_{k,m}(z) for this bracket. All the interactions V(Y) remain inside the component operations as in (1.91). At z=1 this is the original gas; at z=0 only the specified old first-class histories are omitted. The V(Y) are real at real data: their construction in LFR2 pp.374–377 consists of real-field action differences, localisation by derivatives integrated over real weakening parameters, and real additions and subtractions completing A′_k. The Cauchy contour representations compute those same real derivatives. Real propagators and the unique small nonlinear solutions are real for real parameters, and the logarithms of positive real integrals take their real branch. Grouping terms by Y therefore preserves reality. Thus exp(Σ_YV(Y)) is positive on real fields. For positive real z the unexpanded integral is a sum of nonnegative weights, with z raised to the number of old first-class components. In particular Ξ_{k,m}(1)>0.

For |z|≤δ_{k,m}^{−1}, positivity, (1.89) and the source's ordinary bound give, at real data,

$$
|\mathbf T'_k(X;z)F|
\leq\bigl(\mathbf T'_k(X)-\mathbf T'_{k,m}(X)\bigr)|F|
+|z|\,\mathbf T'_{k,m}(X)|F|
\leq2e^{-B_k}\|F\|_\infty\;.
\tag{91}
$$

The source's complex factor is included when needed. The bound is on the full integral of F; it is not a density domination of T′_{k,m} by δ_{k,m}T′_k. The latter does not follow and is not used.

For real external fields, the factor 2 in (91) fits inside the source's existing factor e per component in (1.92): that e was reserved for exp(sup|σ|) on complex external data, whereas σ=0 here and 2<e. The tag z can still be complex. Thus the printed cost condition on p.389 suffices, with no extra log 2 charged on top of its +1. The shape and family sums (1.93)–(1.96) are unchanged. The exponentiated cluster expansion of Ξ_{k,m}(z) is consequently analytic on this disc, with a bound

$$
\bigl|\log\Xi_{k,m}(z)\bigr|\leq C_\Xi N_k\;,
\tag{92}
$$

where N_k is the number of M-cubes in the current torus. The logarithm is the branch defined by the cluster series. For the volume factor, root each absolute cluster at a cube outside the fixed second-class components, or at a cube on their boundary if the cluster is a boundary term. The outside-volume factor and tree factors in (1.93), the component-family sum (1.96), and the remaining decay in (1.99) give a fixed sum per root cube; there are at most a fixed multiple of N_k such roots. Boundary polymers use α^{1/3} in (1.97)–(1.99). The constants are uniform over the other variables on the support of the outer operation: those variables are still present in V(Y) when the source states (1.68)–(1.69), and (1.73) is applied to the entire product they enter. These are pointwise source bounds, not averages over the exterior variables. Thus C_Ξ is independent of the fine cutoff, exterior history, m and z under the source hypotheses.

When δ_{k,m}≤1/2, Cauchy's formula on this actual source disc gives

$$
\begin{aligned}
|\log\Xi_{k,m}(1)-\log\Xi_{k,m}(0)|
&\leq2C_\Xi N_k\delta_{k,m},\\
\left|\partial_z\log\Xi_{k,m}(1)\right|
&\leq2C_\Xi N_k\delta_{k,m}\;.
\end{aligned}
\tag{93}
$$

The first bound follows by summing the nonconstant Taylor coefficients, bounded by C_ΞN_kδ_{k,m}^n. For the second use the circle centred at 1 of radius δ_{k,m}^{−1}−1, with a limiting smaller radius if necessary.

At real external data the derivative in (93) is the expected number of old first-class components under the full conditional gas, including its interactions and its physical conditional denominator Ξ_{k,m}(1). Hence

$$
\mathbb P\bigl(\text{at least one first-class component has }b(X)\leq k-m
\mid\text{the exterior variables}\bigr)
\leq2C_\Xi N_k\delta_{k,m}\;.
\tag{94}
$$

The exterior variables include the second-class and unchanged components, their old fields and their histories. They are not declared independent. The conditioning is the literal positive integral in (1.72) before the component operations are evaluated.

To retain the full physical denominator, write the full vacuum integral at this step as ∫Ξ_{k,m}(1;η) dA(η), where dA is the positive outer operation in (1.72), with all spectator variables and histories restored. The reverse Faddeev–Popov step on LFR2 p.378 identifies its integral with the preceding one only after V_k is integrated against a gauge-invariant integrand; this applies to the vacuum integrand. Together with LFR1 (1.102) and T's mass identity it identifies the total mass with the original partition function. Multiplying (94) by Ξ_{k,m}(1;η), integrating with dA and dividing by this same partition function preserves the bound. The event is defined on this post-R representation with labels; no equality with an event of the original fine-field law is asserted. This estimate uses no all-small-field comparison and no residual quotient of the kind (Q) in the earlier continuum note.

#### The resulting cutoff-age rate and its scope

The standing running-coupling input (5), not CRE (2.6)–(2.7) alone, gives g_j⁻²≥A_*+b(k−j). With the source's logarithmic threshold p₀(g)≥c₀(log g⁻²)^{p₀}, and with the current coupling in the fixed stopping-scale window, (88) yields the following for sufficiently large m:

$$
\delta_{k,m}\leq C_{\bar g}\exp\left(-2c_0\bigl[\log(A_*+bm)\bigr]^{p_0}\right)\;.
\tag{95}
$$

Here p₀≥5r>1. At the stopping lattice N_k is fixed as the initial cutoff is refined. For m_K=⌊√K⌋ the right side of (94) is therefore summable in K: for every fixed q>1 it is at most C_qK^{−q} once K is large.

This is a decay estimate for old first-class R histories under the actual full positive integral, not merely a bound on an individual unnormalised numerator. It covers all old fields and history sums inside those component operations. It does not cover surviving or second-class components outside this gas, nor histories whose old component was already removed by an earlier R-step and now occurs through an inherited E-, R- or Wilson insertion.

For a bounded scalar closed insertion f on this full history integral, deleting the event in (94) changes its normalised expectation by at most 2‖f‖_∞ times the probability in (94). For the renormalised Wilson expectation one cannot substitute ‖f‖_∞=1 after division by κ_K. Its application needs the paid Wilson-root expansion with this age mark inserted before local scalar extraction. In particular, if normalised component averages are used in that expansion, their component masses must first be restored: T′_k(X;z)1 can vanish for complex z, whereas the original unnormalised component integral with the whole closed insertion is analytic. The next step is that marked-root estimate with the original perimeter/corner factors, rather than an estimate of separate normalised arcs.

### 6.9 The physical denominator at the fixed stopping scale — window uniformity pending

For a finite-volume Cauchy estimate, the source's global ultraviolet bound can be used directly. The volume in that bound must be read in its original convention. RG1 p.258, immediately before (0.30), explicitly identifies |T_η|=|T₁^{(k)}|; in four dimensions this is η⁴ times the number of fine sites. The displayed summation in (0.30) confirms that convention. It is also explicit in the predecessor UV3 p.256, (3)–(5). Thus the volume in CRE (2.50) and LFR2 (0.1) is fixed at the stopping scale. It is not the number of sites in the original fine lattice.

Write this fixed volume as V_stop, and let E^B_ε be the vacuum counterterm specified in CRE p.262: the sum of the one-step vacuum terms for the whole lattices. If the manuscript's E_ε is different, the actual vacuum and marked integrals both carry the factor exp(E^B_ε−E_ε). T is linear. In the actual R of LFR1 (1.100) and LFR2 (1.1), the replacement denominator is the Wilson-action integral, while a scalar multiplying the input remains in the numerator; hence R is degree-one homogeneous and the scalar stays common to both integrals. This is an identity for the original integrals, not a replacement of the physical denominator. LFR2 (0.1) gives

$$
e^{E^B_\varepsilon-E_\varepsilon}\,
\chi_k\exp\left(-g_k^{-2}A(U_k)-E_-V_{\rm stop}\right)
\leq\rho_k
\leq e^{E^B_\varepsilon-E_\varepsilon}e^{E_+V_{\rm stop}}\;.
\tag{96}
$$

There is a fixed positive Haar measure set on which the lower bound is useful. To see this without prescribing arbitrary exterior data, take all current-scale bonds within distance r of the identity and then take the gauge saturation of this set. Its Haar measure is at least h_G(r)^{|E_k|}, where h_G(r) is the Haar measure of the radius-r identity ball in G and |E_k| is the fixed number of current-scale positive bonds.

The local determining data in CRE (2.16) satisfy the smallness assumptions of VAR Theorem 1 uniformly in the fine depth when r is sufficiently small. Specifically, the block extension Q_k^{s*} of CRE (1.3) is the identity within k-blocks and the corresponding V(c) across a block face. Averaging at an intermediate scale leaves the same block extension at that scale: every path in the average is internal to a block except for the same single crossing, so the logarithmic correction is zero. Each mixed plaquette of its determining data is consequently a word in at most four current bonds. Its distance from the identity is at most 4r. VAR (8), applied to the global and local determining sets, then bounds their plaquettes in the unit-scale interior by 4B₃rη². CRE p.256 specifies that the minimal determining set based on Ω has Ω^{∼−2}⊂Ω_k, where these two layers are M₁-layers. With Ω=□^{∼4}, the test region □^∼ in (2.17) lies in this unit-scale interior. Choose r so that 4r<a₁ and 4B₃r is less than half the smallest ε_k in the fixed stopping-coupling window. Then χ_k=1 on this gauge-invariant set, uniformly in the fine cutoff.

The same source regularity bound gives A(U_k)≤C_Sr²V_stop there: each unitary plaquette contributes half its squared normalised Hilbert–Schmidt distance from the identity, and η⁴ times the number of plaquettes is 6V_stop. This is used only inside the lower bound on the full partition integral. Since g_k is bounded below by a positive number in the stopping window, integration of (96) gives constants z_-, z_+>0, independent of the initial cutoff, such that

$$
e^{E^B_\varepsilon-E_\varepsilon}z_-
\leq Z_K\leq
e^{E^B_\varepsilon-E_\varepsilon}z_+\;.
\tag{97}
$$

For example one may take z_+=exp(E_+V_stop) and z_-=h_G(r)^{|E_k|}exp(−g_min^{-2}C_Sr²V_stop−E_-V_stop). These constants may depend on the fixed torus and terminal coupling. No uniformity in the thermodynamic limit or in g_min→0 is asserted. In a numerator estimate the same vacuum factor in (97) must be retained and cancelled only in the final ratio.

This global lower bound does not prove the conditional exterior-field estimate (Q) in the earlier note. That estimate fixes exterior data up to the boundary of a small-field test, whereas here every current-scale bond is restricted to one smaller neighbourhood of a flat field and the entire physical integral is retained.

### 6.10 The Wilson-root extension: second-class re-entry unresolved

The age-weighted root bound (99), and hence (101), are not established. The focused review identified a missing budget: D2.7 (15.8)(c) pays for a second-class component re-entering the induction by splitting its current factor exp(−2p₀(g_k)/(1+β₀)). That factor comes from the birth reserve used in (89). The retention argument from D2.6 alone therefore does not apply to a lineage passing through this branch. The pole-free contraction identities below remain valid, but their full-history age bounds are conditional on repairing this payment. No summable estimate for the renormalised Wilson expectation is claimed from this section yet.

This step uses the existing D2.6 component-payment estimates (§§5 and 7.2–7.3 of its closure) and the D2.7 closed-loop localisation and group expansion (items 15.3–15.8 of its closure), with their recorded inputs, including R-far″. It does not certify those inputs. The new issue is the tag (90), whose large complex disc cannot be handled by dividing by the individual tagged component masses.

Form the tagged numerator directly from the unnormalised integrals in LFR2 (1.91), with the complete closed Wilson contraction inserted. For a fixed selection of component histories it is a polynomial in z. When the loop visits one component several times, all its visits remain under that one component integral. In particular, do not replace this expression by a product of separately normalised arc averages. If the notation T′(X)1·𝒯_X is used, cancel this product back to T′(X) before introducing z. This removes apparent poles at zeros of T′(X;z)1.

For flat extraction at complex z, let C_g(z) be the scalar flat value of the whole unnormalised group contraction. Constant-conjugation invariance gives this scalar directly, even when a component mass or a vacuum activity vanishes. Define the deviation by subtracting C_g(z) times the background word on the group's span from the full group contraction. This is an exact regrouping of D2.7's off-flat pieces: its difference from subtracting c_g(z)∏F(P;U) is retained in the deviation, not dropped. At flat data C_g(1)=c_g(1)∏F(P;1), so the original flat perimeter and corner coefficients are unchanged. The group gas with activities C_g(z), and its compatible-family expansion, are analytic without division by ∏F(P;1). The new deviation vanishes at flat data for every z and has the same two-term majorant as the original subtraction. Every expression assigned a bound is a completed closed contraction; open slot indices occur only within the exact contraction identity. Groups assigned no scalar part because they meet a remaining large-field component keep C_g=0, as in D2.7.

Within the D2.6 lifetime induction the component payment uses κ_j(Z), Res(Z) and Pol(Z), leaving 2p₀(g_{b(Z)}) outside those accounts. For such a lineage the weighted birth argument gives δ_{k,m} after its attached insertions and exposed segments have been paid. Applying this to every lineage additionally requires the second-class re-entry payment identified above; the supplied D2.7 ledger does not establish it. Conditional on that missing payment, the tagged root majorant on |z|≤δ_{k,m}^{−1} would be at most twice the untagged one. At real external fields this factor 2 fits inside the existing complex-density allowance e per component, as in (91), because the component density has σ=0 even when the inserted localised function is complex.

After this replacement, the remaining sums are precisely the component, link and interleaving-group sums of D2.7 (15.3)–(15.6), with the same supports and incompatibilities. Their positive majorants are independent of z on the whole disc. Consequently the tagged group values, flat cluster coefficients and closed root sums at real external fields have the same bounds as before, up to fixed constants. Cauchy's formula in z then puts a factor 2δ_{k,m} into their differences between z=1 and z=0. A tagged complex-field norm for propagation to further RG steps would require its own field-domain margins. It is not needed or claimed for the stopping-scale value estimate here.

More explicitly, let 𝔅_g be the positive bound for a complete group contraction at real external data, with all its support weights included. Let ‖·‖_real denote the supremum over those data on their original support. With the factor-2 payment incorporated in 𝔅_g, its marked difference satisfies

$$
\|\mathcal A_g(1)-\mathcal A_g(0)\|_{\rm real}
\leq2\delta_{k,m}\mathfrak B_g\;.
\tag{98}
$$

The same holds for the unnormalised flat group and the difference defining a deviation group. The majorant 𝔅_g is uniform in both z and the external fields, so it can be summed with the original root weights before any supremum is interchanged. Vacuum clusters connected to a root receive the age mark by differentiating their full product, including the exclusion quotient. This is the one-mark cluster sum of (70)–(72), with the root kept in the same closed contraction.

At the stopping scale the number of traversals of C and the current torus volume are fixed. The required conclusion of the root payment and of an explicit ultraviolet upper-bound resummation for that majorant is a constant M_C independent of K. Neither the re-entry payment nor this complete majorant resummation has yet been supplied. The proposed bound, for |z|≤δ_{k,m}^{−1}, is

$$
|N_K(z)|
\leq e^{E^B_{\varepsilon_K}-E_{\varepsilon_K}}\,
|\kappa_K|M_C\;.
\tag{99}
$$

Here κ_K is the original normalisation at z=1 and is kept fixed. To identify its factor in (99), all factors extracted before this last R-operation are already factored out in the incoming D(k) expansion. The remaining original R-factor is the exponential of its flat perimeter and corner coefficients. Their absolute cluster bounds in D2.7 (15.4) bound that factor and its inverse by constants depending on the current contour and coupling. Those constants are included in M_C. No estimate using the bare bound |W|≤1 divided by κ_K is used.

The statement (99) needs the absolute root estimates of D2.6–D2.7, not merely the numerical boundedness of the final expectation in the earlier note's (8.1). Its proof must keep the inherited large-field integrals, pay their root factors through every branch, and then re-run the ultraviolet upper-bound count with the remaining budgets. This remains unfinished. The following ratio calculation is conditional on (99).

The tagged vacuum integral has, by the same source-disc argument and the vacuum upper bound, a bound exp(E^B_ε−E_ε)M_0. Cauchy's formula gives

$$
\begin{aligned}
|N_K(1)-N_K(0)|
&\leq2\delta_{k,m}\,
e^{E^B_{\varepsilon_K}-E_{\varepsilon_K}}|\kappa_K|M_C,\\
|Z_K(1)-Z_K(0)|
&\leq2\delta_{k,m}\,
e^{E^B_{\varepsilon_K}-E_{\varepsilon_K}}M_0\;.
\end{aligned}
\tag{100}
$$

Both real partition integrals are positive. By (97), Z_K(1) is at least exp(E^B_ε−E_ε)z_-. Once 2M₀δ_{k,m}≤z_-/2, (100) gives the same lower bound with z_-/2 for Z_K(0). Thus the original ratio subtraction yields

$$
\left|
\frac{N_K(1)}{\kappa_K Z_K(1)}
-\frac{N_K(0)}{\kappa_K Z_K(0)}
\right|
\leq C_{C,T,\bar g}\delta_{k,m}\;.
\tag{101}
$$

The vacuum factors cancel between the actual numerator and denominator bounds. With m=⌊√K⌋, (95) makes (101) summable in K. Its left side compares the original renormalised expectation with the intermediate expression obtained by omitting old first-class histories in the last R-gas, using the same original κ_K in both. It does not identify that intermediate expression with the corresponding one from the (K+1)-run. The recent-step comparison, the inherited contributions left by earlier R-operations, and the surviving and second-class histories still have to be compared.

This summability statement is conditional on the unproved bound (99). It is not an established Wilson-loop estimate.

### 6.11 Recent-step polarisation and the inherited R-contributions — working derivation

The recent-step coupling counterterm is extracted from the second external-field derivative of the logarithm of the actual fluctuation integral. Its variation must retain the connected terms produced by the denominator. On a fixed branch and fixed selector carrier, write the complete exponent, including the Gaussian density and all inherited factors, as H(s,t,a). Here s is an external-field direction at the flat field and t is a variation of the input data. Let brackets and connected cumulants be for the normalised full integral with density exp H. Direct differentiation gives

$$
\partial_t\partial_s^2\log Z
=\langle H_{sst}\rangle
+\operatorname{Cov}(H_{ss},H_t)
+2\operatorname{Cov}(H_{st},H_s)
+\operatorname{Cum}_3(H_s,H_s,H_t)\;.
\tag{102}
$$

The third cumulant is the ordinary centred connected cumulant; it is not replaced by Gaussian Wick contractions. Equation (102) follows by twice differentiating log Z and then using ∂_t⟨F⟩=⟨F_t⟩+Cov(F,H_t). It is inserted into the same connected expansion as (59), with all contractions completed. Changes of hard selectors are still separate finite-difference marks from (66). The source's linear polarisation projection, RG1 (1.20)–(1.22) or CRE (3.57)–(3.64), is applied to (102), not to an unnormalised numerator.

There are two different analytic-domain issues. The native interior E-terms with no R-contribution in their coefficient ancestry use the RG1/RG2 construction. CRE p.278 identifies interior terms with that whole-lattice construction. Keeping the actual fluctuation cutoffs g_j r(g_j) does not require changing the physical plaquette tests: the background variables of a coefficient function can be analytically extended while the original integration cutoff stays fixed. For the R-free coefficient recursion, RG2's proof requires an upper bound on g_j|B|, which is met by g_jr(g_j) below its fixed smallness threshold. Its background-domain constants can then be kept fixed as in RG1.

This does not give a fixed-domain extension of the entire CRE E-term. CRE pp.270–271 explicitly puts older R-terms into E_k. Its k₁ is chosen to restore the required Euclidean covariance; the condition L^{−(k−j)}MR_j≤L is not an analytic-domain estimate. Those R-contributions retain their shrinking CRE domains and must remain marked.

Keep the two contributions distinct by labelling coefficient terms according to whether their ancestry contains a primitive R-term. A primitive R-family is treated as a supplied activity family with its original bound; its internal production need not be unfolded. In unfolding an E-coefficient, retain the label on every descendant and on its vacuum and coupling subtractions. The coupling projection is linear, so these coloured counterterms sum to the original counterterm. Couplings and the classical quadratic operators are held fixed in this activity-input comparison; their variations remain separate marks in (102). This is a decomposition of the convergent coefficient expressions, not a second physical flow with the R-operation removed. In particular the boundary and young-R channels of CRE (3.26) remain in their original channels and are not discarded.

The shrinking-domain loss for the R-labelled part can be budgeted using a feature explicitly available in CRE (2.31): its exponent κ₀ may be chosen arbitrarily large. Fix a target power q>6 and use the source bound at power q+7, with the source parameters chosen once for that exponent. In a local polymer norm with a fixed spare decay exponent, the primitive R-inputs then satisfy

$$
\|R^{(j)}\|_{\kappa,j}\leq Cg_j^{q+7}\;.
\tag{103}
$$

Here the norm is the supremum over a creation-scale cube of the sum over polymers containing that cube, with weight exp(κd_j(X)), and the supremum of each activity on its original CRE complex domain. The source decay exponent is taken larger than κ so that the rooted sum converges. A factor two for endpoint differences is included in C.

Here is the proposed value-level transfer for the R-descendant E-part:

$$
r_k^E\leq C\sum_{j\leq k}g_j^{-2}\|R^{(j)}\|_{\kappa,j}
+\sum_{i<k}a_{k-i}r_i^E,\qquad
a_n\geq0,\qquad\sum_{n\geq1}a_n<1\;.
\tag{104}
$$

For the first term, subtract the vacuum value of each R-input and use the quadratic marginal expansion described after CRE (2.31), and in the proof of (2.44). At creation scale j its two field derivatives cost Cα_j⁻²≤Cg_j⁻². The factor (L^jη)⁴ in that marginal expansion pays the number of j-scale locations in a current-scale cube. The polynomial spatial moments are paid by the spare exponential decay. The extra fluctuation Cauchy factor in the difference R(U_shift)−R(U_background) is bounded under R-m and can be discarded for this upper bound. Thus the direct marked R-input is bounded by the first sum in (104). No field derivative is treated as cost-free.

For the second term, telescope the Mayer factors in a normalised E-input difference. A selected factor is replaced by its difference multiplied by the integral of the exponential along the straight activity interpolation. Every resulting connected term contains one distinguished E-input mark. RG2 (1.24)–(1.29) gives the creation-age factor L^{−(k-i)} after the sum over its positions, together with the fluctuation/domain ratio. Under q₀=q₁>p₀ and R-m, that ratio is at most
ω_* = C sup_j ε_j/min(α_{0,j},α_{1,j}), which tends to zero with the common small-coupling bound. CRE (2.6)–(2.9) bounds the ratios of the creation and current analytic radii by fixed powers of 1+k−i. The five field powers in (1.24) therefore add only a polynomial in that age; it is absorbed by replacing L^{−(k-i)} with L^{−β(k-i)}, with a fixed 0<β<1.

The remaining connected expansion is rooted at this distinguished mark. Its unmarked vertices obey the same Kotecký–Preiss majorant as the original conditional integral; summing the rooted trees multiplies the mark bound by a fixed constant. This yields a_n=Cω_*L^{−βn}. Choosing the coupling small enough that Cω_*L^{−β}/(1−L^{−β})<1 gives the last condition in (104). The coupling subtraction of an E-input is carried with that input before this estimate; separating it would undo the irrelevant-order cancellation used in (1.24). All these estimates are on CRE's actual integration domains and include the inherited interactions in the selected majorants.

This transfer still requires focused verification of the creation-to-current domain comparison and the coloured counterterm recursion. It uses the original R's unnormalised component numerators; its fixed-geometry normalising denominator is the Wilson integral in LFR1 (1.100). No R_law result is imported.

The nonnegative convolution resolvent of (104) has total mass at most (1−∑a_n)⁻¹. Since its forcing sum is nondecreasing in k, the proposed transfer gives

$$
r_k^E\leq C'\sum_{j\leq k}g_j^{q+5}\;.
\tag{105}
$$

The two external-field derivatives in the polarisation projection cost at most Cα_k⁻², with α_k=min(α_{0,k},α_{1,k})≥c g_k. The second spatial moments in CRE (3.57)–(3.64) are paid by the spare exponential polymer decay, as in the existing polarisation estimate. Thus the conditional consequence of (105) is

$$
|\beta_k^{[R]}|
\leq Cg_k^{-2}\sum_{j\leq k}g_j^{q+5}
\leq C'g_k^{q+1}\leq C'g_k^q\;.
\tag{106}
$$

For the middle inequality use the running bound (5), with g_k⁻²−C₀≥g_k⁻²/2 in the small-coupling window, and compare the decreasing sum with the integral of (g_k⁻²/2+bs)^{−(q+5)/2}. This sum is at most Cg_k^{q+3}. The first marginal transport has already consumed two powers in (104); the history sum and the final two field derivatives consume four more. The seventh spare power remains available, for example for a fixed logarithmic loss. The calculation is linear in a primitive R-input mark of relative size d when d multiplies the first term of (104).

The useful distinction is that the native part could use the fixed-domain polarisation constant, while the R-labelled part can afford the shrinking-domain loss. Applying a g_k⁻² Cauchy constant indiscriminately to the native E-difference is not justified by this calculation. Conversely, (106) does not assert cutoff decay: it is an input-stability estimate, conditional on the ancestry decomposition and (104). The actual two-cutoff native-kernel source in (59), and the recent-step Wilson and selector marks, still require estimates.

### 6.12 Exploratory calculations recorded at the pause

These are the remaining calculations and proposed repairs considered before the pause. They are retained here so that the working record includes the unsuccessful and unfinished parts. They are not additional proved inputs to (9), and recording them does not resume the mathematical work.

#### Creation-to-current analytic radii

The source restrictions in RG1 p.280 include B₃α₃<α₁/2 and 2B₃α₃≤βL⁻²α₀. They permit a choice α_{3,j}=c min(α_{0,j},α_{1,j}) for a sufficiently small fixed c. With q₀=q₁, the coupling and logarithm comparisons in CRE (2.6)–(2.7) would then give

$$
\frac{\alpha_{1,k}}{\alpha_{3,j}}
\leq C(1+k-j)^{1/2},\qquad
\left(\frac{\alpha_{1,k}}{\alpha_{3,j}}\right)^5
L^{-(k-j)}
\leq C_\beta L^{-\beta(k-j)}\;.
\tag{107}
$$

This is the proposed polynomial-age payment behind (104). A separate issue remains: RG1 p.272 says that α₂ depends on α₀, but the required quantitative lower bound α_{2,j}≥cα_j was not derived. The displayed restrictions on α₃ alone do not prove all the domain comparisons needed in (104). The matching to R-m and the coloured coupling subtractions also remains unreviewed.

#### The quadratic part of the cutoff mark

The initial cutoff difference has a quadratic contribution which cannot simply be counted as a small nonlinear interaction. For an analytic action contribution Φ with zero constant and linear terms, the formal expansion in the original fluctuation variable is

$$
g^{-2}\Phi(gA)
=\frac12\langle A,\Phi''(0)A\rangle
+O(g|A|^3)\;.
\tag{108}
$$

Thus a difference of quadratic kernels can be of order one even though the higher terms are small in g. The exploration was to retain that quadratic difference in the exact Gaussian part and put its compensating interaction into the combined mark (86). No proof was obtained that the two actual cutoff runs admit a common local representation with a contracting norm for the remaining interaction. In particular, the nonlinear background dependence cannot be declared a pure change of reference: (86) cancels a reference change only when the physical integrand is fixed.

#### A candidate estimate for the free covariance contribution

For the quadratic part only, a block-averaged covariance comparison was considered. On a unit coarse lattice, with N fine subdivisions per direction, the candidate scalar Fourier expression was

$$
\begin{aligned}
q_N(q)&=\prod_{\nu=1}^4
\frac{\sin(q_\nu/2)}{N\sin(q_\nu/(2N))},\\
\omega_N(q)&=4N^2\sum_{\nu=1}^4\sin^2(q_\nu/(2N)),\\
\widehat\Sigma_N(p)&=
\sum_{\substack{n\in\mathbb Z^4\\(p+2\pi n)/N\in[-\pi,\pi)^4}}
\frac{|q_N(p+2\pi n)|^2}{\omega_N(p+2\pi n)}\;.
\end{aligned}
\tag{109}
$$

Limits are intended in a zero component of a sine quotient. The zero mode is excluded from this tentative covariance. The normalisation, phases and the extra link-direction averaging factor for the actual gauge-field average were not fully matched to RG1's operators. Equation (109) is therefore a candidate scalar component calculation, not an identification of the paper's C^{(k)}.

The proposed comparison was to replace ω_N(q) by |q|² and q_N by the product of sinc factors. The small-momentum denominator error is of order N⁻² after its leading singularity cancels; the squared averaging factors give summable alias weights. This suggested an O(N⁻²) operator bound for the covariance difference. A short-range absolute kernel bound does not follow automatically: cancellation of the leading |p|⁻² singularity can leave a bounded direction-dependent symbol at p=0, whose Fourier coefficients need not be absolutely summable. The comparison was consequently to be made first in an operator norm, with harmonic modes kept among the retained variables. For a gauge field, the connector-gradient terms may be removed only after contraction with conserved closed currents. No open-current or separate transport estimate was established.

The missing steps are a proof of the candidate operator bound, its exact identification with the original symmetric averaging and gauge fixing, and its insertion into the full interacting marked estimate. Convergence of (109) by itself would not settle any of those steps.

#### Conditional Gaussian matrix identities

The following finite-dimensional calculation was considered for transferring an averaged-covariance difference to the actual fluctuation covariance. Let Σ₀, Σ₁ be positive covariance matrices on a common carrier and let Q be a fixed surjective averaging map. Define

$$
\mathsf H_i=\Sigma_iQ^*(Q\Sigma_iQ^*)^{-1},\qquad
\mathsf D_i=\Sigma_i-\Sigma_iQ^*(Q\Sigma_iQ^*)^{-1}Q\Sigma_i\;.
\tag{110}
$$

The candidate finite-difference identity is

$$
\mathsf D_1-\mathsf D_0
=(I-\mathsf H_1Q)(\Sigma_1-\Sigma_0)
(I-Q^*\mathsf H_0^*)\;.
\tag{111}
$$

It follows formally by expanding the right side and using Σ_iQ^*=𝖧_i(QΣ_iQ^*) and QΣ_i=(QΣ_iQ^*)𝖧_i^*. The cross terms cancel through the definitions of the two regression maps. Uniform bounds on the regression maps would transfer a covariance operator bound through (111). This calculation has not been independently reviewed, and neither its common carrier nor its gauge-coordinate identification has been supplied for the two nonlinear cutoff runs.

A second proposed step was interpolation between a small operator difference and the separate exponential block bounds supplied by the propagator theory. If those bounds were C N⁻² and Ce^{-cd} for a block separation d, then

$$
\min(CN^{-2},Ce^{-cd})\leq C N^{-1}e^{-cd/2}\;.
\tag{112}
$$

This would give a small weighted kernel after sacrificing half the decay exponent. The applicability of the two assumed bounds to the same pair of actual kernels remains open.

Inverse and square-root dependence were also to be controlled before inserting the mark into (58). In this paragraph D_i denotes a positive covariance on an identified free carrier, not the singular full conditional covariance of (110). The identities considered were P₁−P₀=−P₁(D₁−D₀)P₀ when P_i=D_i⁻¹, and, for positive matrices with a common spectral gap,

$$
\sqrt{D_1}-\sqrt{D_0}
=\frac1\pi\int_0^\infty
t^{1/2}(tI+D_1)^{-1}(D_1-D_0)(tI+D_0)^{-1}
\,\mathrm dt\;.
\tag{113}
$$

These were intended to control the precision, restricted inverse and covariance square root entering Γ in (58), while keeping the compensating exponential and determinant. They were not substituted into the full two-cutoff integral.

#### The full covariance-response remainder

An integration-by-parts form of the covariance mark was considered as an alternative to taking the absolute value of the trace and quadratic terms separately. In a smooth, unrestricted Gaussian integral, varying the covariance acts by one half of its contraction with the second derivative of the inserted function. In the present integral those derivatives must act on the complete product fΘe^V. They produce derivatives of f, mixed derivatives of f and V, connected terms containing V'' and V'⊗V', and contributions from Θ. V remains the full inherited interaction. The hard-cutoff contributions must be represented by the actual shell marks or a justified distributional limit; no bound for those boundary terms was obtained. Thus no interacting remainder estimate was completed by this reformulation.

The same caveat applies to coupling parity. At fixed selectors, if a uniform analytic estimate justified β(g)=β(0)+O(g²), then x=g⁻² would give ∂_xβ=−g³∂_gβ/2=O(g⁴). This does not account for changing cutoff boundaries or establish uniform constants for the inherited inputs.

#### Attempted repairs of second-class re-entry

Three possibilities were considered after the obstruction to (99) was identified. None was established.

- A new failed small-field test on a post-R second-class component might supply a fresh reserve from the Wilson action retained outside T′. This would have to identify the unspent action and the precise integration producing the gain. The existing test and the old action cannot be charged again merely because the component has a new label.
- Carrying the old Pol reserve instead of discarding it might preserve part of the creation-scale suppression. No bound was obtained paying arbitrarily many re-entries from that finite reserve. Redefining the creation index to mean the last re-entry would change the event in (89), rather than prove the claimed estimate for its original event.
- Keeping the vacuum kernel and its Wilson-marked numerator unnormalised could avoid the large factor introduced by their quotient. The exact pair is the one in (83)–(84). A relative mark might then survive the reallocation of the unmarked large-field budget, even when a positive birth-probability bound does not. Such a construction must fit the existing C8 kernels, keep every contraction closed and prove its stability through later T and R operations. No such inductive estimate was completed.

These considerations leave the recent-step signed comparison as the required object. A rare-event estimate for the vacuum histories is not a substitute for that signed estimate.

#### Other incomplete constructions

A common current-lattice representation was considered in which the quadratic covariance difference is retained explicitly and the nonlinear differences are propagated as marked interactions. The same physical T-map and the reference cancellation (86) motivate this, but they do not establish its local norm, its gauge-invariant decomposition or its compatibility with the original R-denominators and scalar extraction. A proposed contraction of the form “irrelevant Gaussian contraction plus a small interacting correction” was not derived for the actual data. No modified R-operation, new physical normalisation or autonomous replacement model was adopted.

Arithmetic mixtures of the two full measures on the common lattice were considered as positive comparison paths. A geometric interpolation of densities would additionally require a justified common density, its support and a local expansion for its logarithm; these were not supplied. A coupling of the two histories conditional on a common coarse field was likewise only an identity-level possibility. It supplies neither independence inside either inherited law nor a small local difference norm.

An exponential moment of the number of retained multiscale variables was also considered for integrating the old action tails under the full history law. With L_ret=∑_{n<k}(1+log g_n⁻²)|Γ_n|, the proposed insertion is e^{uL_ret}. It increases precisely the geometric costs already present in the large-field majorant. A uniform bound would require re-running creation, preparatory, merger and second-class re-entry payments with that extra cost. That re-run was not performed. In particular the already identified re-entry obstruction cannot be bypassed by asserting such a moment bound. The resulting proposed extensions of the old E-, R- and boundary-term tails to the full interacting history law were not established.

The attempted bounds split the E-tail's determining layers at k−m/2. The newer layers would carry L^{−βm/2}; the older layers would require a weighted age estimate for surviving histories. The R-tail would use its coupling sum times the retained-variable moment. For the expectation under the full positive labelled history integral, the unproved candidates were

$$
\begin{aligned}
\mathbb E_K|\mathcal E_{\rm old}|
&\overset{?}{\leq}C\left(L^{-\beta m/2}
+\delta_{k,\lfloor m/2\rfloor-1}\right),\\
\mathbb E_K|\mathcal R_{\rm old}|
&\overset{?}{\leq}C(1+m)^{1-\kappa_0/2},\\
\mathbb E_K|\mathcal B_{\rm old}|
&\overset{?}{\leq}C\delta_{k,m-1}\;.
\end{aligned}
\tag{114}
$$

Here the use of δ would require the age estimate for all the surviving lineages and its weighted moment, not merely the first-class event of (94). Neither that extension nor the exponential moment was proved. Equation (114) records the unfinished calculation only and is not used in the Cauchy argument.

### 6.13 The remaining estimate in this expansion

Equations (59), (64), (66), (72), (73), (76) and (84) specify the kernel, selector and normalisation marks that must be inserted into the existing marked-polymer induction. The bounds (64) and (72) establish how a small local difference is paid for in that expansion, including its denominator contribution. Equation (81) supplies the g_k² gain for the coupling variation of the actual R-denominator kernel. These calculations do not establish the complete small local difference between the two actual cutoff runs.

The unsolved step is a bound on the connected marked coefficients obtained after the full inherited integrations, with the Wilson insertion and the difference of its perimeter/corner factors included, whose propagation to the stopping scale gives a summable sequence in K. For the kernel contribution, (61) exposes the missing input explicitly: a cutoff-small bound for the marked precision, boundary coupling and full interaction, or a cancellation of their combined score inside the marked integral strong enough to replace those separate bounds. The selector marks (66), the R-component marks (76) and the inherited-history term (77) must be controlled in the same comparison. None is discarded as a uniformly small error at fixed terminal coupling.

The present derivation therefore does not prove the Cauchy estimate (9). It advances the direct probabilistic calculation to these marked integrals and their connected norm; no conclusion from §5 is used to supply their cutoff decay.

In matching to (1), a variation of the insertion includes the scalar term −(∂_t log κ_t)f_t when f_t=κ_t⁻¹W_t. It cannot be absorbed into a vacuum normaliser. A field-independent vacuum variation cancels in the centred density mark, consistently with the freedom in c_K; the perimeter/corner variation does not. An assembly proving (9) must identify its summed marked integral with ℋ_K(1) and divide by Z_{K+1}, including these scalar terms. The calculations here do not yet construct that assembly, the intermediate common labelling, or a contracting recursion for the actual cutoff marks.

## 7. What Is Still Required for Full-Sequence Convergence

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

- For §6: RG2, `../Balaban/tex/RG2/parts/p011.tex`–`p021.tex`, (1.41)–(1.43), (2.1)–(2.41), for the actual selected kernels, moment payment, resummation and gauge invariance; RG1 `p269.tex` and `p276.tex`, (2.16), (3.29), for the gauge actions. CRE `p271.tex`–`p278.tex`, (3.27)–(3.47), supplies the inherited interactions and normalised expectation expansion.
- For §6.6: `../Balaban/tex/LFR1/parts/p201.tex`, (1.100)–(1.102), and `../Balaban/tex/LFR2/parts/p356.tex`–`p358.tex`, (1.1)–(1.11), identify the actual R-denominator, nonlinear fluctuation integral, component geometry and normalising bound. LFR2 `p378.tex`–`p390.tex`, (1.71)–(1.100), retains the inherited numerator and gives the large-field polymer expansion.

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
- `../Balaban/tex/RG1/parts/p252.tex`–`p254.tex`, (0.2)–(0.12), and `p260.tex`–`p263.tex`: the symmetric averaging convention, its stated transfer and the use of VAR/PBG in that convention.
- `../Balaban/tex/REG/parts/p077.tex`–`p087.tex`, (1.3)–(1.64): the regularity class, gauge transformations, Landau representation and constants; `p097.tex`–`p100.tex`, Propositions 6–7: local gauges for arbitrary regular fields and the inverse regularity bound.
- `../Balaban/tex/VAR/parts/p288.tex`–`p299.tex`, (73), (79), (97)–(121), (139)–(142): the nonlinear constraint kernel, contraction and exact action expansion; `../Balaban/tex/PBG/parts/p421.tex`–`p426.tex`, (3.128)–(3.153): the constrained propagator and its carrier.
- `../Balaban/tex/PRT2/parts/p224.tex`, (2.1)–(2.4), and `p231.tex`, (2.46): whole-torus geometry and the weighted distance.
- For the new continuation under review: `../Balaban/tex/CMP98/parts/p031.tex`–`p033.tex`, (86)–(108), `p039.tex`–`p041.tex`, (138)–(155), and `p044.tex`–`p050.tex`, (166)–(214); `../Balaban/tex/REG/parts/p088.tex`–`p097.tex`, (1.69)–(1.125); `../Balaban/tex/PBG/parts/p404.tex`, (3.69).

## Focused Review

The age-mark review is `verification/isolated_reviewer/reviews/continuum-old-r-mark-20261027-r1/review.txt`. It found (88)–(95) valid conditional on the standing coupling input and the stated source premises, and confirmed that this supplies actual decay with age for the first-class vacuum gas. It requested the finest nonnegative history labels, the preparatory induction case, reality of the bracket weights, rooted-count uniformity and the reverse Faddeev–Popov mass identity. Those clarifications are incorporated in §6.8. Its probability is on the post-R representation with labels; it is not asserted to be an event of the original fine-field law.

The subsequent review is `verification/isolated_reviewer/reviews/continuum-old-r-root-20261027-r1/review.txt`. It found the vacuum age argument sound under its inputs and the fixed-stopping-volume denominator argument coherent. For (97), uniformity of E_± over the stopping-coupling window still needs confirmation; the near-flat block-extension argument is this note's calculation rather than a quoted source theorem. Most importantly, the review did not establish (99). It identified the second-class re-entry budget spending the birth reserve, the missing ultraviolet count for the insertion-carrying absolute majorant, and the need for an explicit real-data sum or a properly paid complex-data estimate. The formulae (100)–(101) are correct only conditional on (99). Section 6.10 records that failure and does not claim a Wilson-loop age estimate.

Section 6.11 and the exploratory calculations in §6.12 have not been independently reviewed. No review or mathematical calculation is running at the pause.

The focused probabilistic review is `verification/isolated_reviewer/reviews/continuum-marked-kernel-20261027-r1/review.txt`. It verifies (72) under the explicit rooted hypotheses and the exact finite-difference and normalisation identities. It accepts the selected-integral moment mechanism conditionally and requests the direct score formula on complex contours, contour bookkeeping, a uniform marked norm, and an explicit decay reserve; those corrections are incorporated above. It does not verify cutoff smallness, common intermediate carriers, a scale contraction or the Cauchy conclusion. Its assessment is that this is progress on transfer of a marked estimate, not on the missing cutoff decay itself. Section 6.6 was developed while that review was running and was not in its packet; it remains awaiting review. The original packet and manifest fix exactly what was reviewed.

The independent review in `verification/isolated_reviewer/reviews/continuum-fixed-loop-20261027-r1/review.txt` checked the fixed-loop proof, its exponent, the finest-step comparison and the lift-scale calculation. It found the derivation of (12)–(16) valid, requested explicit ladder edges, fine-domain coverage and curvature/constants in the application, and did not accept (17) as established by the supplied energy proof. Those scope corrections are included above. The original packet and its revision hash are retained in that review directory. Review does not change the conditional status of (20) or the unresolved status of (9).

A second independent review, `verification/isolated_reviewer/reviews/continuum-finest-block-20261027-r1/review.txt`, checked §5.4 against the manuscript's full averaging formula. It confirmed the estimates (18)–(19) in substance and requested interface plaquettes, the norm conversion, mesh alignment and the small-h range. These are now explicit. The application also specifies the two variational problems at the same V and the K-to-K+1 comparison; it makes no estimate for the finitely many depths outside that range. Both review packets and transport manifests are retained. The energy hypothesis (17) remains unresolved.

The local lift action estimate was reviewed in `continuum-lift-action-20261027-r1` and `continuum-lift-action-20261027-r2` under the same review directory. Their checks covered the affine average, force, kernel factors and closed-plaquette summation. The named remaining premises were reviewed in `continuum-lift-premises-20261027-r1`; its findings on inverse-gauge gluing, the uniform BCH remainder, cube compatibility and source constants are incorporated in §5.6. The source transfer from RG1 is stated as an input, not reproved. Equation (23) is retained at that scope.

The exact-constraint argument was reviewed in `continuum-constraint-coercivity-20261027-r1`, and the full chain through the actual blocked background in `continuum-blocked-background-20261027-r1`. The latter found no invalid step in (31)–(46), including the Fourier kernel estimate, nonlinear averaging and actual chart inclusion. Its requested radius, geometry, mean-zero, local-extension and smallness details are included above. These results give (46), not a vanishing action upper bound. Sections 5.9–5.11 are new work requiring focused review; (47), (56) and (57) remain unaccepted until that review and any repairs are complete.

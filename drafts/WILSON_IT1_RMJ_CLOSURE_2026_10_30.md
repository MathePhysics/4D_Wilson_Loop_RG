# RMJ: The Averaged Current at the Evaluation Points of (4)(f)

**Status: derived, not reviewed.** This note derives the step map's premise RMJ (map #MOMGD.50, #MD2.2.6.142). Its inputs are those of the map's derivation of (2.35) (#MD2.2.6.142): 𝐁_p(X)'s definition (CRE p.256 l.57–63), the provisional q₀ = q₁ and q₀ > p₀, CRE (2.6)–(2.7) (printed, p.255), RG2 p.5's all-norms bound (printed), CRE p.277's 𝐇-decay (Bałaban's, CRE p.267 l.42–44, p.277 l.6–8), and the T_Y condition of (4)(f) with C′ enlarged by a factor depending on d and L only (§6). (2.35) and (2.37) at the evaluation points are proved together by one continuity argument (§3), so the map's (2.35) no longer takes RMJ as an input. The loss L^{n−p} that the sup-norm route through VAR (190) incurs (#MD2.2.6.142-14) does not arise: an exact identity (§4) turns the change of the current into a block-level expression in which only the first derivative of the deformation enters.

## 1. The Statement

At every evaluation point of (4)(f), for every factor domain X (the non-𝐃_k domains Z included) and every p = 1, …, j (the range of RG1 (iv)'s n, map #MD2.2.6.142-11), the averaged current 𝐉_{p,X}(M^·(𝐔)) satisfies CRE (2.37) with the step-k constant on each layer n of X. In η-units (#MD2.2.6.142, *(c2) units*), with j_n := min{p, n} the localisation index of U_{p,X} on layer n:

|J| < (1 − β(1 − 2^{−(k−n)}))·α_{0,n}L^{n−j_n}(L^nη)^{−3}.

The index j_n is derived from the definition of 𝐁_p(X). 𝐁_p(X) is the minimal determining set on X's maximal sequence X = Ω_0 ⊃ Ω_1 ⊃ … ⊃ Ω_p (CRE p.256 l.57–63). By CRE (2.2) (p.255) with p in place of k, it is Γ_n = Ω_n^{(n)}∖Ω_{n+1}^{(n)} for 1 ≤ n < p and Γ_p = Ω_p^{(p)}. So U_{p,X} has scale-n data on layer n < p and scale-p data on every layer n ≥ p, which is j_n = min{p, n}.

## 2. Setting

The notation is that of the map's (c0)–(c3) (#MD2.2.6.142-16 and the lines after it).
- The path is 𝐔_t = e^{iη𝐇(s, (t·t_Y)B′)}e^{iηa′}U_{k+1}, t ∈ [0, 1], from the base 𝐔_0 = e^{iηa′}U_{k+1} to the evaluation point 𝐔_1; every evaluation point is such an endpoint, and every 𝐔_t is itself an evaluation point.
- U_t := U_{p,X}(M^·(𝐔_t)), taken on each p-block in the axial gauge Ax_k (REG p.79). Its current is J_t := 𝐉_{p,X}(M^·(𝐔_t)) = D*_{U_t}F(U_t), with F(U) = η^{−2}π Im ∂U: RG1 (1.8) (p.261) with the units of RG1 (1.15) (p.262).
- ∂_tU_t = iη(𝒜_t + D_{U_t}ω_t)U_t. Here 𝒜_t is the linearised minimiser applied to the data derivative b_t := Q_{U_t}H_t + δ_t, ω_t is the infinitesimal gauge keeping U_t in Ax_k, with |ω_t| ≤ O(1)ȟ_n, and δ_t is (c3)'s mismatch.
- On layer n, L^nη|H_t| and (L^nη)²|∇H_t| are ≤ O(1)ȟ_n. Here ȟ_k := B₀e^{16κ_s}(T_Y|B′|_Y + sup|B′|) on Ω_k, and ȟ_n := O(1)(2θ)^{k−n}h_k^{(0)} on an older layer, with θ = e^{−δ₀RM₁/32} and h_k^{(0)} as in the map's *Older layers* (#MD2.2.6.143).
- The margin on layer n is the difference of the step-k and step-(k+1) constants: m_n := β2^{−(k+1−n)}α_{0,n}L^{n−j_n}(L^nη)^{−3}.
- The base point satisfies (2.35) and (2.37) with the step-(k+1) constant on X's own domain, Z included. Both are posed by D(k+1)(iii) for the averaged configurations (map #MD2.2.6.133).

## 3. The Joint Continuity Argument

Let T be the set of t ∈ [0, 1] such that, for every s ≤ t, U_s satisfies (2.35) and (2.37) with ≤ in place of < and with the step-(k+1) right sides plus twice the respective margins (non-strict, so that T is closed).
- **0 ∈ T,** by §2's base condition.
- **T is closed,** because U_t, hence ∂U_t and J_t, are continuous in t (the map's (c0): U_t depends analytically on t).
- **T is open,** because on T the bounds below give (2.37) with the step-(k+1) right side plus m_n/2, and the map's *Assembly* (#MD2.2.6.142-68, #MD2.2.6.142-69) gives (2.35) with the original margin. Both lie strictly inside the doubled bounds. So T = [0, 1].

On T, |J_s| ≤ 2α_{0,n}L^{n−j_n}(L^nη)^{−3} ≤ 2α_{0,n}(L^{j_n}η)^{−3} on layer n. This gives three things:
- the path form of the current that the map's (c0′) uses for Δ^{(2)}, with constant 2;
- PBG's regularity condition (3.36) for U_s, with Mα₀ ≥ 2max_n α_{0,n}: (3.36) (PBG p.396) is |∂^{η*}∂^ηA| < O(1)Mα₀(L^jη)^{−3} on □, for U_s = e^{iηA} in the axial gauge of □; there J = D*F = ∂^{η*}∂^ηA + O(1)(|A||∇^ηA| + η|A|²|∇^ηA|)-terms, and (3.35)'s bounds on A and ∇^ηA (from (2.35) and VAR Theorem 1) make the correction O(1)α₀²(L^jη)^{−3}, so the display above gives (3.36) with the doubled O(1);
- with (2.35) and VAR Theorem 1 (p.279, (9)), the regularity under which PBG Theorems 3.1–3.4 and 3.12 apply to U_s.

The current bound used inside the argument is T's own, so nothing is assumed about J at the evaluation points.

## 4. The Derivative of the Current

**(a) The gauge part.** J is gauge covariant. The infinitesimal gauge ω_t therefore contributes i[ω_t, J_t], of size ≤ 2|ω_t||J_t| ≤ O(1)ȟ_n|J_t|.

**(b) The linear part.**
- For the variation U ↦ e^{iηs𝒜}U, the plaquette variables give δF = D_U𝒜 + E with |E| ≤ O(1)η|𝒜||F|.
- The parallel transports in D*_U give (δD*_U)F of size O(1)|𝒜||F|.
- A lattice divergence costs at most 2/η, so |D*_UE| ≤ O(1)|𝒜| sup|F| over the neighbouring bonds.

Hence

∂_tJ_t = D*_{U_t}D_{U_t}𝒜_t + i[ω_t, J_t] + 𝒞_t,  |𝒞_t| ≤ O(1)|𝒜_t|·sup|F_t|,

with the sup over a neighbourhood of fixed lattice size. No derivative of F enters.

**(c) The linearised minimiser is VAR's H₁.** Write G := Δ_a^{−1} and G̃ := G − GQ*(QGQ*)^{−1}QG (the map's (c1)). Let G₁ := (Δ_a − Δ^{(2)})^{−1} = (Δ₁ + DRD* + Q*Q)^{−1} with Δ₁ := Δ − Δ^{(2)}: this is VAR's G₁ (p.294: "We denote by G₁ an inverse operator to the operator Δ₁ + DRD* + aQ*Q", a = 1), with Δ in place of Δ_π as on VAR p.297. It is not PBG's π-extended operator of (3.128), (3.138), and PBG p.426's "QG₁DR = 0" is not used for it.
- The map's (c0′) gives 𝒜_t = (I − G̃Δ^{(2)})^{−1}H_0b_t, so A := 𝒜_t satisfies A = H_0b_t + G̃Δ^{(2)}A.
- By Δ_aH_0 = Q*(QGQ*)^{−1} and Δ_aG̃ = I − Q*(QGQ*)^{−1}QG, (Δ_a − Δ^{(2)})A is a Q*-image.
- QA = b_t, since QG̃ = 0.
- So A = G₁Q*μ with QG₁Q*μ = b_t, i.e. 𝒜_t = G₁Q*(QG₁Q*)^{−1}b_t =: H₁b_t.

*RD*G₁Q* = 0, from VAR's Landau-gauge variational problem.* U_t is the minimiser for its own block data, so VAR's procedure applies with U₀ = U_t (VAR p.305, (172)–(174): "We take U₀ = U_k(V₀) … At first we fix the Landau gauge"). For block data near those of U_t, the minimiser in the Landau gauge relative to U_t is exp iη𝓗(B), with RD*𝓗 = 0 (VAR (76), p.289: "RD*(A′ − HD(A′)) = RD*A′ = 0") and the constraint L^jηQ𝓗 = B. By VAR p.297, the functional is constant on the gauge submanifolds, so the critical configuration satisfies (127) "for all δA′ satisfying QδA′ = 0", not only those with RD*δA′ = 0; since RD*𝓗 = 0, (127) is (128): Δ_a𝓗 − Δ^{(2)}𝓗 + J + (δV/δA′)(𝓗) ∈ Im Q*, Δ_a = Δ + DRD* + Q*Q. V begins at third order (VAR (176)), so differentiating in B at B = 0 gives, for the first-order term ∂𝓗 (VAR (177): "the expansion of 𝓗 begins with the first order term H₁B"): (Δ_a − Δ^{(2)})∂𝓗 ∈ Im Q*, Q∂𝓗 = (L^jη)^{−1}·id and RD*∂𝓗 = 0. G₁ and QG₁Q* are invertible (§5), so the first two determine ∂𝓗 = G₁Q*(QG₁Q*)^{−1}(L^jη)^{−1}, and the third gives RD*G₁Q*(QG₁Q*)^{−1} = 0, hence RD*G₁Q* = 0. Its adjoint is QG₁DR = 0 (G₁ is self-adjoint). In particular 𝒜_t = H₁b_t is the derivative of the Landau-gauge minimiser in the data direction b_t, and RD*𝒜_t = 0.

**(d) The identity.** Δ_a = D*D + Δ′ + DRD* + Q*Q (#MD2.2.6.142). By (c), RD*𝒜_t = 0. With Q𝒜_t = b_t, and λ₁ := (QG₁Q*)^{−1}b_t:

D*D𝒜_t = Q*(λ₁ − b_t) + Δ^{(2)}𝒜_t − Δ′𝒜_t.

Write b_t = QH_t + δ̂_t (δ̂_t: δ_t in the units of QH_t). QH_t = QG₁(Δ_a − Δ^{(2)})H_t and QG₁DR = 0, so

λ₁ − b_t = (QG₁Q*)^{−1}QG₁(D*(DH_t) + Δ′H_t − Δ^{(2)}H_t) + (QG₁Q*)^{−1}δ̂_t − δ̂_t.

The deformation enters only through DH_t, H_t and δ̂_t. No second derivative of H_t is taken: the operator QG₁D* acts on the 2-form DH_t.

## 5. The Bounds

**Kernels.** G = Δ_a^{−1} satisfies Theorem 3.3 of PBG, in particular (3.42) (VAR p.297: "For the operator Δ_a^{−1} = G we have proved Theorem 3.3 in [5], and especially the bounds (3.42) for the second order operator"), and H₀ satisfies (3.133) (VAR (129)). VAR's G₁ = Σ_n G(Δ^{(2)}G)^n converges as a Neumann series, since Δ^{(2)} has a local kernel of size O(1)α₀ under (3.36) (§3), so G₁ satisfies (3.42) with O(1) changed. (QGQ*)^{−1} obeys the bound (3.132), stated in PBG's text on p.422 and assumed on p.426 (a Bałaban claim, accepted); QG₁Q* = QGQ* + QG(Δ^{(2)}G₁)Q*, the second term O(α₀) times QGQ*'s bound, so (QG₁Q*)^{−1} obeys (3.132) with O(1) changed, and H₁ = G₁Q*(QG₁Q*)^{−1} obeys (3.133). At complex data, VAR p.309, ll.2–4: "These functions and operators can be extended to arbitrary, regular configurations U … They are analytic functions of these configurations, having the properties and bounds as described above". In (3.126)'s normalisation, Q and Q* are averages of sup norm ≤ 1 against the block weight (L^{j′}η)^d. The following bounds hold, each summed against e^{−δ₂d(y,y′)}:
- |(QG₁Q*)^{−1}(y, y′)| ≤ O(1)(L^jη)^{−2}(L^{j′}η)^{−d}e^{−δ₁d(y,y′)}, by (3.132);
- |QG₁D*μ| ≤ B₀L^{j′}η·Σe^{−δ₀d}|μ|, by (3.42)'s G∇* entry and PBG p.398's remark that ∇_U and ∇*_U are interchangeable;
- |QG₁f| ≤ B₀(L^jη)²·Σe^{−δ₀d}|f|, by (3.42)'s first entry;
- |H₁b| ≤ O(1)|b|, by (3.133).

Here j = j_n is the localisation index.

**Inputs on layer n.**
- On T, |F_t| ≤ O(1)α_{0,n}(L^nη)^{−2}, by (2.35) in η-units.
- |𝒜_t| ≤ O(1)|b_t| ≤ O(1)ȟ_n(L^nη)^{−1}.
- |δ̂_t| ≤ O(1)α_{0,n}L^{2(j−n)}ȟ_n(L^nη)^{−1}, by (c3).
- |Δ^{(2)}A| ≤ O(1)C₃L^jη·sup|J_t|·|A| ≤ O(1)C₃α_{0,n}(L^nη)^{−2}|A| on T, by the map's (c0′) and CMP98 (149).
- |D_{U_t}H_t| ≤ O(1)ȟ_n(L^nη)^{−2}. In the axial gauge, the link variables of U_t and of 𝐔_t are e^{iηA} with |A| ≤ O(1)L^jη·sup|F| ≤ O(1)α_{0,n}L^{j−n}(L^nη)^{−1}: the holonomy of the loop closed by the tree paths, by (2.35) and (2.34). So D_{U_t}H_t and the derivative in which H_t's bound is stated differ by O(1)α_{0,n}ȟ_n(L^nη)^{−2}.

**The terms,** each as a multiple of α_{0,n}L^{n−j}(L^nη)^{−3} = α_{0,n}(L^jη)^{−1}(L^nη)^{−2}, the scale of m_n:
- Q*(QG₁Q*)^{−1}QG₁D*(DH_t): ≤ O(1)(L^jη)^{−2}·B₀L^jη·O(1)ȟ_n(L^nη)^{−2}, i.e. O(1)B₀ȟ_n/α_{0,n}. This is the main term. The relaxation L^{n−j} of (2.37) is exactly the ratio L^nη/L^jη that it needs.
- (QG₁Q*)^{−1}QG₁Δ′H_t and Δ′𝒜_t: Δ′ is linear in F_t, so these are ≤ O(1)B₀α_{0,n}(L^nη)^{−2}·ȟ_n(L^nη)^{−1}, i.e. O(1)B₀ȟ_nL^{j−n}.
- (QG₁Q*)^{−1}QG₁Δ^{(2)}H_t and Δ^{(2)}𝒜_t: ≤ O(1)B₀C₃α_{0,n}ȟ_n(L^nη)^{−3}, i.e. O(1)B₀C₃ȟ_nL^{j−n}.
- (QG₁Q*)^{−1}δ̂_t − δ̂_t: ≤ O(1)(L^jη)^{−2}α_{0,n}L^{2(j−n)}ȟ_n(L^nη)^{−1} = O(1)α_{0,n}ȟ_n(L^nη)^{−3}, i.e. O(1)ȟ_nL^{j−n}.
- 𝒞_t: ≤ O(1)ȟ_n(L^nη)^{−1}·α_{0,n}(L^nη)^{−2}, i.e. O(1)ȟ_nL^{j−n}.
- The gauge part: ≤ O(1)ȟ_n·2α_{0,n}L^{n−j}(L^nη)^{−3}, i.e. O(1)ȟ_n.

With α_{0,n} ≤ 1 and L^{j−n} ≤ 1, at a point of layer n,

|∂_tJ_t| ≤ C_J·Σ_{n′}w_{n,n′}ȟ_{n′}·(L^jη)^{−1}(L^nη)^{−2},  C_J := O(1)(B₀(1 + C₃) + 1).

w_{n,n′} is the layer weight of the map's (c0′): the current's L^{3(n−n′)} for the finer layers against e^{−δ₂R₁M₁(|n−n′|−1)}, summable once δ₂R₁M₁ > 3log L + 1. Across localisation indices, PRT2 (2.58)–(2.59) gives the same. The constants depend on d and L only.

## 6. The Margin and the Constant Condition

Integrating over t ∈ [0, 1], |J_1 − J_0| ≤ sup_t|∂_tJ_t|. It is enough that sup_t|∂_tJ_t| ≤ m_n/2 on each layer n.

**The layer n = k.** The T_Y condition gives ȟ_k ≤ (1 + o(1))min(β, 1)α_{0,k}/C′ (the map's (c0)). The inner layers carry no larger ȟ. So the condition holds once C′ ≥ 8C_J·O(L³), the O(L³) being the layer sum.

**An older layer n = k − m.** ȟ_{n′} ≤ O(1)(2θ)^{k−n′}h_k^{(0)} with h_k^{(0)} ≤ min(β, 1)α_{0,k}(4/C′ + o(1)) (#MD2.2.6.143, the o(1) from q₀ > p₀). Against m_n ∝ 2^{−(k+1−n)}α_{0,n}:
- For n′ ≥ n, the ratio is (2θ)^{k−n′}2^{k+1−n} = 2(4θ)^{k−n′}2^{n′−n}, and 2^{n′−n} is absorbed by e^{−δ₂R₁M₁(n′−n−1)}.
- For n′ < n, ȟ_{n′} is smaller still.
- CRE (2.6)–(2.7), first lines (printed, p.255), give α_{0,n} ≥ α_{0,k}/((1+β₀)²√m).

The condition therefore follows from three facts:
- 4θ ≤ 1/2, true for g_K small since θ = e^{−δ₀RM₁/32} and R ≥ (log g₁^{−2})^r → ∞ (CRE (2.5));
- √m·x^m ≤ x for x ≤ 1/2;
- C′ ≥ O(1)C_J(1+β₀)²L³, with g_K small for the o(1).

So (4)(f)'s T_Y condition with C′ enlarged by C_{(2.37)}/C := O(1)C_J(1+β₀)²L³/C gives the statement of §1. The factor depends on d, L, the bound β₀ ≤ 1/2 and the Ad-norm constants of G only, and L is fixed before κ_s and M (map #MD2.4.13.19). The T_Y factor per component of D2.4's count (map #MD2.2.4.80) stays ≤ 1: its added part is O((log g_k^{−2})^{p₀−q₀}) → 0 for q₀ > p₀, as in #MD2.2.6.142-69.

## 7. Scope

- **Layers below the localisation index.** On layers n < p, j_n = n (§1) and the same bounds hold with p replaced by n (the map's (c3), last sentence).
- **Layer 0 of X.** Layer 0 contains ∂X, where CRE poses no condition. There the current bound is VAR Theorem 1 (p.279, (9)–(10)) for the minimiser U_t on X, at the layer-0 scale, and the Dirichlet jump of H_t at ∂X is at that scale too, so §5's term bounds hold on layer 0 with n = 0.
- **The domains Z.** For each factor domain X, including the domains Z of RG2 p.15's covariance operators, the derivation uses only what the map's (2.35) derivation uses for that X:
  - VAR Theorem 1 and Proposition 9 for U_t;
  - PBG Theorems 3.1–3.4 and 3.12 on X's truncated sequence {Ω_0, …, Ω_p}: this sequence is the one of 𝐁_p(X)'s definition (CRE p.256 l.57–63, §1), RG1 (iv) builds the U_n on REG (1.3)–(1.6)'s sequence (p.262 l.41–43), and REG p.77 l.3 places that sequence in PBG's setting, "see also [2.II, 4]" (Bałaban's, accepted);
  - the base conditions posed on X's own domain (map #MD2.2.6.133).
- **Gauge group.** No property of SU(N) is used. The group enters through Ad, π and the Lie-algebra norms only.

## 8. What Is Bałaban's and What Is Derived

**Quoted and checked:**
- RG1 (1.8), (1.15);
- VAR Theorem 1 (9), Proposition 9, (182), (188);
- PBG (3.42), (3.126), (3.133), Theorem 3.3 and the text bound (3.132) (p.422); VAR (76) (p.289), p.294's G₁, (127)–(129) (p.297), (172)–(177) (pp.305–306) and p.309, ll.2–4; RD*G₁Q* = 0 is derived in §4(c) from VAR's Landau-gauge problem;
- CRE (2.2), (2.5)–(2.7), (2.34)–(2.37), and p.256 l.57–63's definition of 𝐁_j(Ω);
- RG2 p.5's all-norms bound;
- PRT2 (2.58)–(2.59).

**Bałaban's, accepted:** CRE p.277's 𝐇-decay (CRE p.267 l.42–44, p.277 l.6–8); PBG's text bound (3.132); REG p.77 l.3's placement of the sequence in PBG's setting.

**Derived here:**
- the localisation index j_n = min{p, n} (§1);
- the identification 𝒜_t = H₁b_t;
- the identity of §4(d);
- the derivative bound of §4(b);
- the term bounds of §5;
- the joint continuity argument;
- the constant condition of §6.

**Not reviewed.**

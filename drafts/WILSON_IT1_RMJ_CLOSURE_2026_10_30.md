# RMJ: The Averaged Current at the Evaluation Points of (4)(f)

{#RMJ.0} This note derives the step map's premise RMJ (map #MOMGD.50, #MD2.2.6.142-75), jointly with (2.35) at the same points. The inputs are 𝐁_p(X)'s definition (CRE p.256 l.57–63), q₀ = q₁ > p₀, CRE (2.6)–(2.7) (p.255), RG2 p.5's all-norms bound, CRE p.277's 𝐇-decay (CRE p.267 l.42–44, p.277 l.6–8), and (4)(f)'s T_Y condition (#MD2.2.6.142-74, #MD2.2.4.80-1) with C′ ≥ C_{(2.37)} (§6).

## 1. The Statement

{#RMJ.1.1} At every evaluation point of (4)(f), for every factor domain X (the non-𝐃_k domains Z included) and every p in the range of RG1 (iv)'s n (map #MD2.2.6.142-11), the averaged current 𝐉_{p,X}(M^·(𝐔)) satisfies CRE (2.37) (p.261) with the step-k constant, on X ∩ (Ω_n∖Ω_{n+1}) for n = 1, …, k−1 and on X ∩ Ω_k for n = k. In the units η := L^{−p} of §2, with j_n := min{p, n}:

  |𝐉_{p,X}(M^·(𝐔))| < (1 − β(1 − 2^{−(k−n)}))·α_{0,n}L^{n−j_n}(L^nη)^{−3}.

{#RMJ.1.2} *The index j_n.* 𝐁_p(X) is the minimal determining set on X's maximal sequence X = Ω_0 ⊃ Ω_1 ⊃ … ⊃ Ω_p (CRE p.256 l.57–63). By CRE (2.2) (p.255) with p in place of k, its pieces are Γ_0 = Ω_1^c (within X), Γ_n = Ω_n^{(n)}∖Ω_{n+1}^{(n)} for 1 ≤ n < p, and Γ_p = Ω_p^{(p)}. So U_{p,X} carries scale-n data on layer n < p and scale-p data on every layer n ≥ p, which is j_n = min{p, n}.

## 2. Setting

{#RMJ.2.1} The notation is the map's: (c0) #MD2.2.6.142-16–21, (c0′) #MD2.2.6.142-36–44, (c1) #MD2.2.6.142-52–55, (c2) #MD2.2.6.142-56–58 and #MD2.2.6.142-65–67, (c3) #MD2.2.6.142-59–65. The units are η := L^{−p}, those of U_{p,X}: CRE (2.35) and (2.37) print the scales as L^nL^{−p}, and RG1 (1.15) (p.262) defines the current with L^{−p} in place of ξ. On layer n, j := j_n is the localisation index.
- {#RMJ.2.2} *The path.* 𝐔_t = e^{iη𝐇(s, (t·t_Y)B′)}e^{iηa′}U_{k+1}, t ∈ [0, 1], runs from the base 𝐔_0 = e^{iηa′}U_{k+1} to the evaluation point 𝐔_1. Since |t·t_Y| ≤ T_Y, every 𝐔_t is itself an evaluation point (#MD2.2.6.142-17). ∂_t𝐔_t = iηH_t𝐔_t.
- {#RMJ.2.3} *The averaged configuration and its current.* U_t := U_{p,X}(M^·(𝐔_t)), taken on each j-block in the axial gauge Ax_k (REG (1.19)–(1.22), p.79). Its current is J_t := 𝐉_{p,X}(M^·(𝐔_t)) = D*_{U_t}F(U_t), with F(U) := η^{−2}π Im ∂U (RG1 (1.8), p.261).
- {#RMJ.2.4} *Averaging and data.* Q = Q_j(U_t) is PBG's averaging on the Λ_j-blocks, and Q* its adjoint from the block inner product with weight (L^jη)^d to the field inner product; both have sup norm ≤ O(1). PBG p.393 defines Q*aQ by ⟨A, Q*aQA⟩ = Σ_j aΣ_{b∈Λ_j}(L^jη)^{d−2}|(Q_jA)(b)|², with a = 1; so Q*aQ = Q*𝔞Q with 𝔞 := (L^jη)^{−2} on Λ_j.
- {#RMJ.2.4-1} VAR (75) (p.289) writes the averaging constraint as L^jηQ_jA′ = B, so ∂_tM^·(𝐔_t) = Q_{𝐔_t}H_t with Q_Y := L^jηQ_j(Y) (#MD2.2.6.142-32). Put b_t := (L^jη)^{−1}Q_{𝐔_t}H_t = QH_t + δ̂_t, with δ̂_t := (L^jη)^{−1}δ_t and δ_t := (Q_{𝐔_t} − Q_{U_t})H_t, (c3)'s mismatch (#MD2.2.6.142-33).
- {#RMJ.2.5} *The motion of U_t.* ∂_tU_t = iη(𝒜_t + D_{U_t}ω_t)U_t (#MD2.2.6.142-32). Here 𝒜_t is the linearised minimiser at U_t applied to b_t, and ω_t is the infinitesimal gauge transformation keeping U_t in Ax_k, with |ω_t| ≤ O(1)ȟ_n.
- {#RMJ.2.6} *The deformation sizes* (#MD2.2.6.142-19). On layer n, L^nη|H_t| ≤ O(1)ȟ_n and (L^nη)²|∇H_t| ≤ O(1)ȟ_n. Here ȟ_k := B₀e^{16κ_s}(T_Y|B′|_Y + sup|B′|) on Ω_k, and ȟ_n := O(1)(2θ)^{k−n}h_k^{(0)} on an older layer n < k, with θ := e^{−δ₀RM₁/32} (#MD2.2.4.83-1) and h_k^{(0)} of #MD2.2.6.143-2.
- {#RMJ.2.7} *The margin.* On layer n it is the difference of the step-k and step-(k+1) constants of (2.37): m_n := β2^{−(k+1−n)}α_{0,n}L^{n−j}(L^nη)^{−3}, since β(1 − 2^{−(k+1−n)}) − β(1 − 2^{−(k−n)}) = β2^{−(k+1−n)}.
- {#RMJ.2.8} *The base point.* U_0 satisfies (2.35) and (2.37) with the step-(k+1) constant on X's own domain, Z included: D(k+1)(iii) poses both for the averaged configurations (map #MD2.2.6.133).

## 3. The Joint Continuity Argument

{#RMJ.3.1} Let T be the set of t ∈ [0, 1] such that for every s ≤ t, U_s satisfies (2.35) and (2.37) with ≤ in place of <, and with right sides equal to the step-(k+1) right sides plus twice the respective margins: m_n for (2.37), and β2^{−(k+1−n)}α_{0,n}L^{−2n} for (2.35) (#MD2.2.6.142-34).
- {#RMJ.3.1-1} *0 ∈ T*, by #RMJ.2.8.
- {#RMJ.3.1-2} *T is closed*, since U_t, hence ∂U_t and J_t, depend continuously on t (U_t depends analytically on t, #MD2.2.6.142-21), and the conditions are non-strict.
- {#RMJ.3.1-3} *T is open in [0, 1].* For s ∈ T, §4–§6 give |J_s| ≤ (step-(k+1) right side) + m_n/2, and the map's *Assembly* (#MD2.2.6.142-68–69) gives (2.35) with the step-(k+1) right side plus one margin. Both are strictly inside the doubled bounds, so by continuity they persist on a neighbourhood of s. Hence T = [0, 1].
- {#RMJ.3.1-4} At t = 1, |J_1| ≤ (step-(k+1) right side) + m_n/2 < (step-k right side), which is the statement of #RMJ.1.1.

{#RMJ.3.2} On T, |J_s| ≤ 2α_{0,n}L^{n−j}(L^nη)^{−3} ≤ 2α_{0,n}(L^jη)^{−3} on layer n: the step-(k+1) constant is ≤ 1, 2m_n ≤ βα_{0,n}L^{n−j}(L^nη)^{−3} with β ≤ 1, and L^{n−j}(L^nη)^{−3} ≤ (L^jη)^{−3} since j ≤ n. This gives three things.
- {#RMJ.3.2-1} The path form of the current used by the map's (c0′) for Δ^{(2)}, with constant 2 (#MD2.2.6.142-24).
- {#RMJ.3.2-2} PBG's condition (3.36) for U_s, with Mα₀ ≥ 2max_n α_{0,n}. PBG (3.36) (p.396) asks |∂^{η*}∂^ηA| < O(1)Mα₀(L^jη)^{−3} on each cube □ of index j, for U_s^u = e^{iηA} with some gauge transformation u on □, where O(1) is a number ≥ 10 (p.396). Take u axial. Then J = ∂^{η*}∂^ηA + N(A), where every term of N(A) has at least two factors from {A, ∇^ηA}, further lattice differences carrying a factor η each. With |η∇^ηf| ≤ 2|f| and (3.35) (from (2.35) and VAR Theorem 1 (9), p.279), |N(A)| ≤ O(1)(Mα₀)²(L^jη)^{−3}, so |∂^{η*}∂^ηA| ≤ (Mα₀ + O(1)(Mα₀)²)(L^jη)^{−3} < 10Mα₀(L^jη)^{−3}.
- {#RMJ.3.2-3} With (3.35) from (2.35) and VAR Theorem 1 (9), and (3.37) at complex data (#MD2.2.6.142-21), U_s is regular in PBG's sense, so PBG Theorems 3.1–3.4 and 3.12 apply to U_s.

{#RMJ.3.3} The current bound used inside the argument is T's own, so nothing is assumed about J at the evaluation points.

## 4. The Derivative of the Current

{#RMJ.4.1} *(a) The gauge part.* J is gauge covariant and its norm is Ad-invariant. The term D_{U_t}ω_t of ∂_tU_t is an infinitesimal gauge transformation, so its contribution to ∂_tJ_t is the rotation ±i[ω_t, J_t], of norm ≤ 2|ω_t||J_t| ≤ O(1)ȟ_n|J_t|.

{#RMJ.4.2} *(b) The linear part.* Vary U ↦ e^{iηs𝒜}U.
- {#RMJ.4.2-1} The plaquette variables give δF = D_U𝒜 + E with |E| ≤ O(1)η|𝒜||F|. Indeed δ∂U = iη²X∂U, where X differs from D_U𝒜 by O(η^{−1}|𝒜||∂U − 1|) = O(η|𝒜||F|), the partial products along the plaquette differing from the transports of D_U by O(|∂U − 1|); and η^{−2}π Im(iη²X∂U) = X + O(|X||∂U − 1|), with |X| ≤ O(1)η^{−1}|𝒜|.
- {#RMJ.4.2-2} The parallel transports in D*_U give (δD*_U)F, of norm O(1)|𝒜||F|.
- {#RMJ.4.2-3} D*_U has 2(d−1) terms of weight η^{−1} per bond, so |D*_UE| ≤ O(1)η^{−1}sup|E| ≤ O(1)sup|𝒜|·sup|F| over the neighbouring bonds and plaquettes.

Hence

  ∂_tJ_t = D*_{U_t}D_{U_t}𝒜_t ± i[ω_t, J_t] + 𝒞_t,  |𝒞_t| ≤ O(1)sup|𝒜_t|·sup|F_t|,

with the sups over a neighbourhood of fixed lattice size. No derivative of F enters.

{#RMJ.4.3} *(c) The linearised minimiser.* Write G := Δ_a^{−1} and G̃ := G − GQ*(QGQ*)^{−1}QG (the map's (c1)), and H₀ := GQ*(QGQ*)^{−1} (PBG (3.126), p.420; VAR (129), p.297, with its factor (L^jη)^{−1} absorbed in b_t). Let G₁ := (Δ_a − Δ^{(2)})^{−1} = (Δ₁ + DRD* + Q*aQ)^{−1} with Δ₁ := Δ − Δ^{(2)}. This is VAR p.294's G₁ ("We denote by G₁ an inverse operator to the operator Δ₁ + DRD* + aQ*Q"), with Δ in place of Δ_π as in VAR (128), p.297. PBG's G₁ of (3.128) and (3.138) is a different operator. G₁ exists by §5.
- {#RMJ.4.3-1} The map's (c0′) (#MD2.2.6.142-37) gives 𝒜_t = (I − G̃Δ^{(2)})^{−1}H₀b_t, so A := 𝒜_t satisfies A = H₀b_t + G̃Δ^{(2)}A.
- {#RMJ.4.3-2} Δ_aH₀ = Q*(QGQ*)^{−1} and Δ_aG̃ = I − Q*(QGQ*)^{−1}QG give (Δ_a − Δ^{(2)})A = Q*(QGQ*)^{−1}(b_t − QGΔ^{(2)}A), a Q*-image. QH₀ = I and QG̃ = 0 give QA = b_t.
- {#RMJ.4.3-3} So A = G₁Q*μ with QG₁Q*μ = b_t, that is, 𝒜_t = G₁Q*(QG₁Q*)^{−1}b_t =: H₁b_t.

{#RMJ.4.4} *RD*G₁Q* = 0, from VAR's Landau-gauge variational problem.* Let U_t be real. It is the minimiser for its own block data, so VAR's construction applies with U₀ = U_t (VAR p.305, (172)–(174): "We take U₀ = U_k(V₀) … At first we fix the Landau gauge"). For block data near those of U_t, the minimiser is exp(iη𝓗(B))U_t (VAR p.305 l.37–39), with 𝓗 = A′ − HD(A′) and A′ = 𝒜₁ + H₁B (VAR (174), p.305). Here L^jηQ_jA′ = B (VAR (75)), RD*A′ = RD*𝓗 = 0 (VAR (76), p.289), and D(A′) begins at second order (VAR pp.289–290).
- {#RMJ.4.4-1} The functional is constant on the gauge submanifolds (VAR p.297), so the critical point satisfies (127) "for all δA′ satisfying QδA′ = 0", and, as RD*A′ = 0, (128): J + Δ_aA′ − Δ^{(2)}A′ + (δV/δA′)(A′) ∈ (ker Q)^⊥ = Im Q*. Here Δ_a = Δ + DRD* + Q*aQ, J is U_t's current, and V begins at third order (VAR p.282, (80), p.290).
- {#RMJ.4.4-2} Differentiate in B at B = 0, where A′ = 0. Then (Δ_a − Δ^{(2)})∂A′ ∈ Im Q*, Q∂A′ = (L^jη)^{−1}·id, RD*∂A′ = 0, and ∂𝓗 = ∂A′. G₁ and QG₁Q* are invertible (§5), so the first two give ∂A′ = G₁Q*(QG₁Q*)^{−1}(L^jη)^{−1}, the first-order term of 𝓗 (VAR (177), p.306: "the expansion of 𝓗 begins with the first order term"). The third gives RD*G₁Q*(QG₁Q*)^{−1} = 0, hence RD*G₁Q* = 0. Taking adjoints, QG₁DR = 0, since G₁ and R are symmetric.
- {#RMJ.4.4-3} *Complex data.* Both sides are analytic in the configuration (VAR p.309, ll.2–4: "They are analytic functions of these configurations"). The domain of PBG (3.37) is invariant under A′ ↦ sA′, s ∈ [0, 1], so each of its components contains G-valued configurations, and these form a maximal totally real submanifold. An analytic function on a connected open set that vanishes on a nonempty open subset of a maximal totally real submanifold vanishes identically, so RD*G₁Q* = 0 and QG₁DR = 0 hold at complex U_t as well.
- {#RMJ.4.4-4} Hence 𝒜_t = H₁b_t is the derivative of the Landau-gauge minimiser in the data direction b_t, and RD*𝒜_t = 0.

{#RMJ.4.5} *(d) The identity.* Δ_a = D*D + Δ′ + DRD* + Q*𝔞Q, with Δ′ linear in F_t (#MD2.2.6.142-39, #RMJ.2.4). By (c), RD*𝒜_t = 0 and Q𝒜_t = b_t. With λ₁ := (QG₁Q*)^{−1}b_t, (Δ_a − Δ^{(2)})𝒜_t = Q*λ₁ gives

  D*D𝒜_t = Q*(λ₁ − 𝔞b_t) + Δ^{(2)}𝒜_t − Δ′𝒜_t.

- {#RMJ.4.5-1} Write b_t = QH_t + δ̂_t. Since QH_t = QG₁(Δ_a − Δ^{(2)})H_t, (QG₁Q*)^{−1}QH_t − 𝔞QH_t = (QG₁Q*)^{−1}QG₁((Δ_a − Δ^{(2)})H_t − Q*𝔞QH_t), and QG₁DR = 0 removes DRD*H_t. Hence

  λ₁ − 𝔞b_t = (QG₁Q*)^{−1}QG₁(D*(DH_t) + Δ′H_t − Δ^{(2)}H_t) + (QG₁Q*)^{−1}δ̂_t − 𝔞δ̂_t.

- {#RMJ.4.5-2} The deformation enters only through DH_t, H_t, and δ̂_t. The operator QG₁D* acts on the 2-form DH_t, so no second derivative of H_t is taken.

## 5. The Bounds

{#RMJ.5.1} *Kernels.* G satisfies PBG Theorem 3.3 except the Laplacian entry of (3.42) (PBG p.422; VAR p.297: "For the operator Δ_a^{−1} = G we have proved Theorem 3.3 in [5], and especially the bounds (3.42) for the second order operator"). H₀ satisfies (3.133) (p.422), and (QGQ*)^{−1} satisfies the bound (3.132) (p.422).
- {#RMJ.5.1-1} *G₁.* On T, |Δ^{(2)}A| ≤ O(1)C₃L^jη·sup|J_t|·|A| ≤ O(1)C₃α_{0,n}(L^nη)^{−2}|A|, by the map's (c0′) (#MD2.2.6.142-38–43, CMP98 (149), p.40) and #RMJ.3.2, with a local kernel. With (3.42)'s first entry and j ≤ n, the kernel of GΔ^{(2)} has norm ≤ O(1)B₀C₃α_{0,n} ≤ 1/2 for the couplings small. So G₁ = Σ_{m≥0}G(Δ^{(2)}G)^m converges, and G₁ satisfies the entries of (3.42) used below with B₀ and δ₀ replaced by O(1)B₀ and δ₀/2 (the convolutions summed by PRT2 (2.58)–(2.59), p.233). VAR p.306 l.37–38 states the same for this operator: "Δ^{(2)} is a small perturbation of Δ_a, and the new operator G has exactly the same properties as Δ_a^{−1}".
- {#RMJ.5.1-2} *(QG₁Q*)^{−1} and H₁.* QG₁Q* = QGQ*(I + K) with K := (QGQ*)^{−1}QGΔ^{(2)}G₁Q*, and by (3.132), (3.42), and #RMJ.5.1-1, K has kernel norm ≤ O(1)B₀²C₃α_{0,n} ≤ 1/2. So (QG₁Q*)^{−1} = (I + K)^{−1}(QGQ*)^{−1} obeys (3.132) with O(1) changed and δ₁ replaced by δ₂ := min(δ₀, δ₁)/4, and H₁ = G₁Q*(QG₁Q*)^{−1} obeys (3.133) likewise. At complex data the same holds by PBG Theorem 3.4 under (3.37) and VAR p.309, ll.2–4.
- {#RMJ.5.1-3} With Q, Q* of sup norm ≤ O(1) against the block weight (L^{j′}η)^d, the following hold, each summed against e^{−δ₂d(y,y′)}:
  - |(QG₁Q*)^{−1}(y, y′)| ≤ O(1)(L^jη)^{−2}(L^{j′}η)^{−d}e^{−δ₂d(y,y′)}, by #RMJ.5.1-2;
  - |QG₁D*μ| ≤ O(1)B₀L^{j′}η·Σe^{−δ₂d}|μ|, by (3.42)'s G∇*_U entry, D* being a finite combination of ∇*_U components (PBG p.398 l.49–50: "we may always replace ∇_U by ∇_U^*, and vice versa");
  - |QG₁f| ≤ O(1)B₀(L^jη)²·Σe^{−δ₂d}|f|, by (3.42)'s first entry;
  - |H₁b| ≤ O(1)|b|, by #RMJ.5.1-2.

{#RMJ.5.2} *Inputs on layer n,* on T.
- {#RMJ.5.2-1} |F_t| ≤ O(1)α_{0,n}(L^nη)^{−2}, by (2.35) in η-units.
- {#RMJ.5.2-2} |𝒜_t| ≤ O(1)|b_t| ≤ O(1)ȟ_n(L^nη)^{−1}, by #RMJ.5.1-3, |QH_t| ≤ O(1)|H_t|, and #RMJ.5.2-3.
- {#RMJ.5.2-3} |δ̂_t| ≤ O(1)α_{0,n}L^{2(j−n)}ȟ_n(L^nη)^{−1}: (c3) gives |δ_t| ≤ O(1)α_{0,n}L^{2(j−n)}·L^jη|H_t| (#MD2.2.6.142-63, and #MD2.2.6.142-65 for n < p).
- {#RMJ.5.2-4} |Δ^{(2)}A| ≤ O(1)C₃α_{0,n}(L^nη)^{−2}|A|, by #RMJ.5.1-1.
- {#RMJ.5.2-5} |D_{U_t}H_t| ≤ O(1)ȟ_n(L^nη)^{−2}. In the axial gauge the link variables of U_t and of 𝐔_t are e^{iηA}, where ηA is the holonomy of the loop closed by the tree paths, of area ≤ O(1)L^jη·η. By (2.35) and (2.34), |A| ≤ O(1)L^jη·sup|F| ≤ O(1)α_{0,n}L^{j−n}(L^nη)^{−1}. So D_{U_t}H_t and the derivative in which H_t's bound is stated differ by O(1)|A||H_t| ≤ O(1)α_{0,n}ȟ_n(L^nη)^{−2}.

{#RMJ.5.3} *The terms* of ∂_tJ_t (#RMJ.4.1, #RMJ.4.2, #RMJ.4.5), each as a multiple of α_{0,n}L^{n−j}(L^nη)^{−3} = α_{0,n}(L^jη)^{−1}(L^nη)^{−2}, the scale of m_n:
- {#RMJ.5.3-1} Q*(QG₁Q*)^{−1}QG₁D*(DH_t): ≤ O(1)(L^jη)^{−2}·B₀L^jη·O(1)ȟ_n(L^nη)^{−2}, that is, O(1)B₀ȟ_n/α_{0,n}. This is the main term; the relaxation L^{n−j} of (2.37) is the ratio L^nη/L^jη that it needs.
- {#RMJ.5.3-2} Q*(QG₁Q*)^{−1}QG₁Δ′H_t and Δ′𝒜_t: |Δ′f| ≤ O(1)|F_t||f|, so these are ≤ O(1)B₀α_{0,n}(L^nη)^{−2}·ȟ_n(L^nη)^{−1}, that is, O(1)B₀ȟ_nL^{j−n}.
- {#RMJ.5.3-3} Q*(QG₁Q*)^{−1}QG₁Δ^{(2)}H_t and Δ^{(2)}𝒜_t: ≤ O(1)B₀C₃α_{0,n}ȟ_n(L^nη)^{−3}, that is, O(1)B₀C₃ȟ_nL^{j−n}.
- {#RMJ.5.3-4} Q*((QG₁Q*)^{−1}δ̂_t − 𝔞δ̂_t): ≤ O(1)(L^jη)^{−2}α_{0,n}L^{2(j−n)}ȟ_n(L^nη)^{−1} = O(1)α_{0,n}ȟ_n(L^nη)^{−3}, that is, O(1)ȟ_nL^{j−n}.
- {#RMJ.5.3-5} 𝒞_t: ≤ O(1)ȟ_n(L^nη)^{−1}·α_{0,n}(L^nη)^{−2}, that is, O(1)ȟ_nL^{j−n}.
- {#RMJ.5.3-6} The gauge part: ≤ O(1)ȟ_n·2α_{0,n}L^{n−j}(L^nη)^{−3}, that is, O(1)ȟ_n.

{#RMJ.5.4} With α_{0,n} ≤ 1 and L^{j−n} ≤ 1, at a point of layer n,

  |∂_tJ_t| ≤ C_J·Σ_{n′}w_{n,n′}ȟ_{n′}·(L^jη)^{−1}(L^nη)^{−2},  C_J := O(1)(B₀(1 + C₃) + 1).

w_{n,n′} is the layer weight of the map's (c0′) (#MD2.2.6.142-50–51): the current's L^{3(n−n′)} for the finer layers n′ < n against e^{−δ₂R₁M₁(|n−n′|−1)}, with Σ_{n′}w_{n,n′} = O(L³) once δ₂R₁M₁ > 3log L + 1. Across localisation indices, PRT2 (2.58)–(2.59) gives the same. The constants depend on d and L only.

## 6. The Margin and the Constant Condition

{#RMJ.6.1} Integrating over t ∈ [0, 1], |J_1| ≤ |J_0| + sup_t|∂_tJ_t|. It is enough that sup_t|∂_tJ_t| ≤ m_n/2 on each layer n.

{#RMJ.6.2} *The layer n = k.* Here m_k/2 = (β/4)α_{0,k}(L^jη)^{−1}(L^kη)^{−2}. The T_Y condition gives ȟ_k ≤ (1 + o(1))min(β, 1)α_{0,k}/C′ (#MD2.2.6.142-19-1). The older layers n′ < k carry ȟ_{n′} ≤ O(1)(2θ)^{k−n′}h_k^{(0)} with h_k^{(0)} ≤ min(β, 1)α_{0,k}(4/C′ + o(1)), which is ≤ min(β, 1)α_{0,k}/C′ for θ and the couplings small. So the condition holds once C′ ≥ 8C_J·O(L³), the O(L³) being the layer sum.

{#RMJ.6.3} *An older layer n = k − m, m ≥ 1.* ȟ_{n′} ≤ O(1)(2θ)^{k−n′}h_k^{(0)}, where h_k^{(0)} ≤ min(β, 1)α_{0,k}(4/C′ + o(1)) (#MD2.2.6.143-2; the o(1) is ε_k/α_{0,k} → 0 for q₀ > p₀). Against m_n ∝ 2^{−(k+1−n)}α_{0,n}:
- {#RMJ.6.3-1} For n′ ≥ n, the ratio is (2θ)^{k−n′}2^{k+1−n} = 2(4θ)^{k−n′}2^{n′−n}, and 2^{n′−n} is absorbed by e^{−δ₂R₁M₁(n′−n−1)}.
- {#RMJ.6.3-2} For n′ < n, the ratio is (2θ)^{k−n′}2^{k+1−n} ≤ 2(4θ)^{k−n}.
- {#RMJ.6.3-3} CRE (2.6)–(2.7), first lines (p.255), give g_n ≥ g_k/((1+β₀)√m) and (log g_n^{−2})^{q₀} ≥ (log g_k^{−2})^{q₀}/(1+β₀), so α_{0,n} ≥ α_{0,k}/((1+β₀)²√m) by CRE (2.28) (p.259), α_{0,j} = g_jC₀(log g_j^{−2})^{q₀}.

{#RMJ.6.4} The condition therefore follows from three facts:
- {#RMJ.6.4-1} 4θ ≤ 1/2, true for the couplings small, since θ = e^{−δ₀RM₁/32} with R one of the R_j of CRE (2.5), R_j ≥ (log g_j^{−2})^r → ∞;
- {#RMJ.6.4-2} √m·x^m ≤ x for x ≤ 1/2 and m ≥ 1;
- {#RMJ.6.4-3} C′ ≥ O(1)C_J(1+β₀)²L³, with the couplings small for the o(1).

{#RMJ.6.5} So the statement of §1 holds under (4)(f)'s T_Y condition with C′ ≥ C_{(2.37)} := O(1)C_J(1+β₀)²L³, covering #RMJ.6.2 and #RMJ.6.4-3 (#MD2.2.4.80-1). C_{(2.37)} depends on d, L, the bound β₀ ≤ 1/2, and the Ad-norm constants of G only, and L is fixed before κ_s and M (map #MD2.4.13.19). The T_Y factor per component of D2.4's count (map #MD2.2.4.80) stays ≤ 1: its added part is O((log g_k^{−2})^{p₀−q₀}) → 0 for q₀ > p₀, as in #MD2.2.6.142-69.

## 7. Scope

- {#RMJ.7.1} *Layers below the localisation index.* On layers n < p, j = n (#RMJ.1.2), and the same bounds hold with p replaced by n (#MD2.2.6.142-65).
- {#RMJ.7.2} *Layer 0 of X.* Layer 0 contains ∂X, where CRE (2.34)–(2.37) pose no condition. There the current bound is VAR Theorem 1 ((10), p.279) for the minimiser U_t on X, at the layer-0 scale, and the Dirichlet jump of H_t at ∂X is at that scale too, so §5's term bounds hold on layer 0 with n = 0.
- {#RMJ.7.3} *The domains Z.* For each factor domain X, including the domains Z of RG2 p.15's covariance operators, the derivation uses only what the map's (2.35) derivation uses for that X:
  - VAR Theorem 1 and Proposition 9 (p.309) for U_t;
  - PBG Theorems 3.1–3.4 and 3.12 on X's truncated sequence {Ω_0, …, Ω_p}. This sequence is the one of 𝐁_p(X)'s definition (CRE p.256 l.57–63), RG1 (iv) builds the U_n on REG (1.3)–(1.6)'s sequence (RG1 p.262 l.41–43), and REG p.77 l.3 places that sequence in PBG's setting ("see also [2.II, 4]"; #MD2.2.6.142-46–47);
  - the base conditions posed on X's own domain (map #MD2.2.6.133).
- {#RMJ.7.4} *Gauge group.* No property of SU(N) is used. The group enters through Ad, π, and the Lie-algebra norms only.

## 8. What Is Bałaban's and What Is Derived

{#RMJ.8.1} *Bałaban's, quoted and checked at the pages cited:*
- {#RMJ.8.1-1} RG1 (1.8) (p.261), (1.15) (p.262), and p.262 l.41–43;
- {#RMJ.8.1-2} VAR Theorem 1 ((9)–(10), p.279), (75)–(76) (p.289), p.282 and (80) (p.290), p.294's G₁, (127)–(129) (p.297), (172)–(177) (pp.305–306), p.306 l.37–38, Proposition 9 and p.309, ll.2–4;
- {#RMJ.8.1-3} PBG p.393 (Q*aQ), (3.35)–(3.37) (p.396), (3.42) (p.397), p.398 l.49–50, Theorems 3.1–3.4 and 3.12, (3.126) (p.420), (3.133) (p.422), and (3.137) (p.423); CMP98 (149) (p.40);
- {#RMJ.8.1-4} CRE (2.2), (2.5)–(2.7) (p.255), p.256 l.57–63, (2.28) (p.259), and (2.34)–(2.37) (p.261); REG (1.3)–(1.6) (p.77) and (1.19)–(1.22) (p.79); PRT2 (2.58)–(2.59) (p.233); RG2 p.5's all-norms bound.

{#RMJ.8.2} *Bałaban's, accepted (stated without proof in print):* PBG's (3.132) (p.422: "We will not repeat these considerations here, let us write only bounds"); CRE p.277's 𝐇-decay (CRE p.267 l.42–44, p.277 l.6–8); REG p.77 l.3's placement of the sequence in PBG's setting.

{#RMJ.8.3} *Derived here:* the localisation index j_n = min{p, n} (§1); the normalisation Q*aQ = Q*𝔞Q and the data b_t (§2); the joint continuity argument and PBG (3.36) on T (§3); the derivative of the current (§4(a)–(b)); 𝒜_t = H₁b_t, RD*G₁Q* = 0 at real and complex data, and the identity of §4(d); the bounds on G₁, (QG₁Q*)^{−1}, H₁, and the terms (§5); and the constant condition C′ ≥ C_{(2.37)} (§6).

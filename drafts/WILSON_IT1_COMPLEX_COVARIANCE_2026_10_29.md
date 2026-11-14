# Complex Gauge Covariance of the Carried Insertions

This note proves the step map's item #MOMGD.5 (D2.4(12)(b) *It carries*, (12)(f), (13)(d)): the carried dev insertions satisfy D(k+1)(iii)'s complex-data bound uniformly in k (§1–§4), with no gauge on the region of SW closure §6(6c) (§5). Map citations are the tags #M… of WILSON_IT1_D2_STEP_MAP_2026_10_22.md. C₀ and C₁ are CRE's constants in α_{i,k} = g_kC_i(log g_k^{−2})^{q_i} (p.259), with q₀ = q₁ > p₀ (SW closure §2) and C₁ = λ_RC₀, λ_R = K_RLM + 1 (CRE p.262 l.43–46 with RG1 p.277 l.54; table #T2.24). B₃ and B₅ are VAR's constants, which depend on d and L only, and C_av := 2(B₃ + 2c_dB₅) is the averaging constant of (K3).

*Inputs.* (T-dev) with its inputs (map #MD2.4.5.12–13); (2.38) for U_{k+1} (SW §6(6d)); D2.2(4)(f)'s chain condition with CRE p.277's margin (map #MD2.2.4.66–90), with (2.35) and (2.37) at the evaluation points from map #MD2.2.6.142 and WILSON_IT1_RMJ_CLOSURE_2026_10_30.md; CRE (2.6)–(2.7) (p.255); the averaging bound (K3); and the slot independence of the dev insertions (D2.6 closure 4.2(iii), class (3)).

**Checks (K1)–(K3).**
- (K1) CRE p.261 (ii) poses (2.38) "for each cube □ ⊂ Ω_n∖Ω_{n+2}, □ ∩ Ω_{n+1}^c ≠ ∅, n = 1, …, j−1, of the size CML^nξ, or □ ⊂ Ω_j and of the size CM", on □ ∩ X, so for every cube of the stated size. In Ũ^c_{k+1} (L^{k+1}ξ = 1) the top-domain cubes are the cubes of side CM in Ω_{k+1}, and the layer-k cubes are the cubes of side CM/L in Ω_k that meet Ω_{k+1}ᶜ. At n = j−1 = k the set Ω_{n+2} = Ω_{k+2} is not among the domains of step k+1; the class with Ω_{k+2} := ∅ is used, which contains the class for every later choice Ω_{k+2} ⊆ Ω_{k+1}. (2.38) holds for U = U_{k+1} by SW §6(6d).
- (K2) From CRE pp.254–256 and (3.5).
  - *Partition cubes.* By p.256, Ω_j and Λ_j "are unions of MR_j-cubes in the lattice T_{L^{−j}}". At j = k+1 these are cubes of side MR_{k+1} in step-(k+1) units, and R_{k+1} ≥ (log g_{k+1}^{−2})^r ≥ C for g_K small ((2.5)).
  - *Collar.* p.254 gives Ω_k ⊃ Λ_k, so Z_k = Λ_kᶜ ⊃ Ω_kᶜ. (3.5) and p.265 give Ω_{k+1} ⊂ ((B^{k+1}(P¹)ᶜ)^{∼3})ᶜ, and B^{k+1}(P¹)ᶜ ⊃ Z_k′^{∼5} ⊃ Z_k, so Ω_{k+1} ⊂ (Z_k′^{∼8})ᶜ. The layers are LMR_{k+1}-cubes of T_η, which are MR_{k+1}-cubes in step-(k+1) units (p.264: "the corresponding partition of the lattice T_{L^{−1}η} into MR_{k+1}-cubes").
  - *Conclusion.* Every point of Ω_{k+1} is at distance ≥ 8MR_{k+1} > CM/L from Ω_kᶜ.
- (K3) (2.35) and (2.37) at the path and disc points of §3 follow from the curvature bound there by the averaging bound below.
  - *Source.* RG1 p.263 (1.17): for complex (𝐔, 𝐉) satisfying (i)–(iii) of RG1's definition with α′₀, α′₁ in place of α₀, α₁, "M^·(𝐔) = 𝐔̄^p on Λ_p, |∂𝐔̄^p − 1| < 2α′₀(L^pξ)²", and "From Proposition 9 [15]" (VAR), |∂U_n(M^·(𝐔)) − 1| < 2B₃α′₀ξ² and |J_n(M^·(𝐔))| < 2B₃α′₀(L^nξ)² on X̃^{−2}; "for α′₀ sufficiently small the above estimates imply the condition (iv)", which is RG1's (1.16), the single-domain form of CRE (2.35) and (2.37).
  - VAR Proposition 9 (p.309) gives the analytic extension of U_k(V′V₀) to G^c-valued small V′, and VAR Theorem 1 (p.279) is multi-domain, 𝔘_k({Ω_j}, B₃ε₁), with one ε₁ for all block plaquettes (VAR (7), p.278). Proposition 9 prints ε₂ = B₅ε₁ with B₅ = 6B₁B₃C₁^{VAR} (VAR (173), p.305), C₁^{VAR} VAR's absolute constant, B₁ = 5dLB₀ (VAR p.296 l.11), and B₃ depends on d and L only (VAR p.279 l.28). B₃ ≥ 1, enlarging VAR's B₃ if necessary, so C_av ≥ 2.
  - *Averaging bound.* Let j ≥ 2 and X ⊂ Ω_j, and let 𝐔 have the real factor U_{k+1}, satisfy (2.39) on X, and have (2.34)-curvature < α′ per plaquette on X, where C_avα′ ≤ α_{0,j}L^{−2j}. Then CRE (2.35) and (2.37) hold for 𝐔 on X ∩ Ω_j.
  - *Proof: the dictionary.* CRE's spaces are defined "similarly as in (I.1.11)–(I.1.16)" (CRE p.261 l.2–3). RG1's U_n(M^·(𝐔)) is CRE's U_{p,X}(M^·(𝐔)), the minimiser on the determining set 𝐁_p(X) of CRE p.256 l.57–63, RG1's n being the number of levels of 𝐁_p(X), which is p, and ξ = L^{−j}. RG1's current normalisation α₀(L^nξ)² is CRE's (2.37) at n = j for every p ≤ j, with the coefficient α_{0,j} in both (α₀L^{−2(j−p)} = α_{0,j}L^{j−p}(L^{j−p})^{−3}).
  - *RG1's hypotheses.* The curvature parts (1.11) and (1.14) follow from the curvature hypothesis, since (2.34) bounds both U and 𝐔, and RG1's (ii) is (2.39). (1.12), |A|, |∇^ξA| < O(1)LMBα′₀ for the G-valued factor U of 𝐔 = U′U (RG1 p.262), holds with α′₀ := α′L^{2j} = α_{0,j}/C_av at U = U_{k+1}.
    VAR Theorem 1 (9), |A| < B₃Mε₁(L^jη)^{−1} with ε₁ = O(L²)ε_{k+1} (SW §6(6d); CRE p.267 (3.12)), converted to RG1's step-j normalisation (RG1's cubes of size O(1)LM step-j units lie inside (6d)'s cubes), gives |A| ≤ O(1)B₃Mε₁L^{−m} and |∇^ξA| ≤ O(1)B₃Mε₁L^{−2m}, m := k+1−j.
    And ε₁L^{−m}/α′₀ ≤ O(L²)C_av(1+β₀)²m^{1/2}L^{−m}(A₀/C₀)(log g_j^{−2})^{p₀−q₀} → 0 uniformly in m (§0's ratios; CRE (2.4), (2.8), (2.28); q₀ > p₀; m^{1/2}L^{−m} ≤ 1/2), so (1.12) holds for g_K small; near ∂Ω_{k+1} the same holds with L^{1−m} (the layer-k cubes of (6d)). The same conversion gives (2.38) for U_{k+1} in the step-j normalisation (CRE p.261 l.26–33 at n = j).
  - *Up to ∂X.* RG1 (1.16)–(1.17) state the bounds on X̃^{−2} (RG1 p.262 l.52, l.59), while CRE prints (2.35) and (2.37) on X ∩ Ω_j. VAR gives them on all of X ∩ Ω_j, with X as Ω₀ (RG1 (iv), p.262 l.41): VAR's action sums over the plaquettes p ⊂ Ω₀ (VAR (5), p.278), and Theorem 1 puts the minimal orbit in 𝔘_k({Ω_j}, B₃ε₁) (VAR (8), p.279), whose conditions (2), |∂U(p) − 1| < B₃ε₁L^{−2j} on every plaquette of Ω_j and |(D_U^{η*}∂U)(b)| < B₃ε₁L^{−2j}(L^jη)^{−1} on every bond of Ω_j (p.278 l.2–8), hold up to ∂Ω₀.
    At complex data, with 𝐔 = U′U, V₀ := M^·(U) real and V′ := M^·(𝐔)V₀^{−1}, Proposition 9 gives U_k(V′V₀) = e^{iη𝓗(B)}U_k(V₀) with |A|, |∇A|, |D*DA| < ε₂(L^jη)^{−1}, ε₂(L^jη)^{−2}, ε₂(L^jη)^{−3} on every Ω_j ((19), p.281 l.6–10), ε₂ = B₅ε₁ (p.309), again up to ∂Ω₀.
    Hence |∂U_{p,X}(M^·(𝐔)) − 1| ≤ (B₃ + 2c_dB₅)ε₁L^{−2j}, and the current's bound with the same constant, hold on X ∩ Ω_j, where c_d is the constant of |∂(e^{iηA}U) − ∂U| ≤ c_d(η²|∇_UA| + η²|A|²) and of its D*-analogue (ε₂ ≤ 1). With ε₁ = 2α′, from the averages' curvature (RG1 p.263 l.10), this is the averaging bound with C_av = 2(B₃ + 2c_dB₅). ∎
  - *No 𝐉-average.* J_{p,X}(M^·(𝐔)) is a function of 𝐔 alone: RG1 (1.15) defines J_n(M^·(𝐔)) "by the formula (1.8) with U_n(M^·(𝐔)) instead of U_j". So the rotation R(u)𝐉 enters only (2.36), checked in §3(a)–(b), and the bound |𝐉| < γ₀ of RG1 (1.14) is not used by (1.17).

## 0. Setting

Step k+1, k ≥ 1. W is a carried dev insertion made at step j ≤ k, m := k+1−j ≥ 1, with X_W ⊂ (Q^#_W)⁺ ⊂ Ω_{k+1} (the scope of (12)(b) *It carries* and of (T-dev), #MD2.4.5.18; for a group of (4), Q^#_𝒢 = X(𝒢)). Its insertion Y_W(𝐔, 𝐉) obeys Cov(j) (#MD2.2.4.3–5):

  Y_W(𝐔^v, R(v)𝐉) = π(v(x_W))Y_W(𝐔, 𝐉)π(v(x′_W))^{−1} for G-valued v,

where I_W is its interval from x_W to x′_W; at j = 1 there is no 𝐉. Y_W does not depend on the slot values (D2.6 closure 4.2(iii), class (3)), so the slot argument is omitted throughout.
- Y_W is analytic on its production domain 𝒟_W, D(j)(iii)'s domain on X_W: CRE's Ũ^c_j for j ≥ 2 (#MD2.0.3.54), and the sup-only domain of #MD2.0.3.53–#MD2.0.3.53-1 for j = 1. 𝒟_W is invariant under G-valued gauge transformations (RG1 p.263: "The spaces U_j^c(X,α_0,α_1) are, by the definition, gauge invariant also"; #MD2.2.6.45-9).
- Its production size is S_W := sup_{𝒟_W}‖Y_W‖. S_W ≤ S_𝒢 of D2.4(4) (#MD2.4.4.17–18) fixes b_W and β_W = b_Wℓ_Wη_j^{−2} (#MD2.4.5.7); the β_W are summed per traversal in (ii-t) (#MD2.4.5.7–8) and carried in (5) *It carries* (#MD2.4.5.18) given (T-dev), and §4 sums S_W through the production (ii-w) sum (#MD2.4.12.4–5, #MD2.4.12.9).

The step-(k+1) datum is 𝐔 = e^{iηA′}U with η := η_{k+1}, A′ 𝔤^c-valued (CRE (iii), p.261), and U = U_{k+1}. Units are fine bonds; a step-(k+1) unit is L^{k+1} fine bonds. On X_W ⊂ Ω_{k+1}, the top layer of D(k+1)(iii), (2.39) and (2.36) give:
- |ηA′(b)| ≤ a, with a := α_{1,k+1}L^{−(k+1)};
- a covariant change of ηA′ per fine step of at most aL^{−(k+1)};
- |𝐉| < r_J^{(k+1)} and |J| < r_J^{(k+1)}, hence |𝐉 − J| < 2r_J^{(k+1)}, where r_J^{(n)} := α_{0,n}(L^nξ)^{−3}, ξ the fine spacing, is (2.36)'s top-layer radius at step n.

*Geometry.* A π_j-cube has side M step-j units, which is ML^{−m} step-(k+1) units, or ML^j fine bonds. X_W is a ∗-connected union of #_j(W) ≤ σ_j(W) such cubes (#MD2.4.12.23–23-1 at step j). A path through a cube costs at most d = 4 sides, and consecutive cubes share a corner, so any two sites of X_W are joined in X_W by a lattice path of length at most

  δ_W := 4ML^{−m}σ_j(W)

step-(k+1) units. Since σ_j = #_j + n_j/M (#MD2.4.3.2) with n_j the step-j traversals of the interval, |I_W| ≤ ML^{−m}σ_j(W) = δ_W/4. Also δ_W ≥ 4ML^{−m}, since σ_j(W) ≥ 1.

*Ratios.* CRE (2.6)–(2.7), p.255, give g_n ≤ (1+β₀)(n−m)^{1/2}g_m and g_m ≤ (1+β₀)g_n for n > m, so (log g_n^{−2})^q ≤ (1+β₀)(log g_m^{−2})^q for g small, and α_{i,k+1}/α_{i,j} ≤ (1+β₀)²m^{1/2}. At production X_W ⊂ Λ_j ⊂ Ω_j (D2.6 closure 2.1(i): a dev group meets no cube within one layer of Λ_jᶜ; CRE p.254), so on X_W the production radii are the top-layer ones, with the factor 1 (SW §3(b1); CRE p.261):
- the sup radius ϱ_j := α_{1,j}L^{−j} ≥ L^ma/((1+β₀)²m^{1/2});
- the per-step allowance α_{1,j}L^{−2j};
- the current radius r_J^{(j)} ≥ L^{3m}r_J^{(k+1)}/((1+β₀)²m^{1/2}).

Since L^m/m^{1/2} ≥ L for L ≥ 2, the condition L ≥ 12(1+β₀)² gives ϱ_j ≥ 12a, r_J^{(j)} ≥ 12r_J^{(k+1)}, 2(1+β₀)²m^{1/2}L^{−m} ≤ 1/6, and 9a² ≤ α_{1,j}²L^{−2j}. It holds under the map's L ≥ L₀ = 5000 with β₀ ≤ 1/2 (#MD2.2.6.204).

## 1. Lemma 1 (Complexified Covariance)

Let F be analytic on an open set 𝒟 of (𝐔, 𝐉) on X_W that is invariant under G-valued gauge transformations, and suppose F(q^v) = π(v(x_W))F(q)π(v(x′_W))^{−1}, q^v := (𝐔^v, R(v)𝐉), for every q ∈ 𝒟 and every G-valued v. Let p ∈ 𝒟, and let u_t, t ∈ [0, 1], be a path in (G^c)^{sites(X_W)} with u₀ = 1 and p^{u_t} ∈ 𝒟 for all t. Then F(p^{u₁}) = π(u₁(x_W))F(p)π(u₁(x′_W))^{−1}.

*Proof.* π extends holomorphically to G^c, and u ↦ p^u is holomorphic. Ψ(u) := π(u(x_W))^{−1}F(p^u)π(u(x′_W)) − F(p) is therefore analytic on the open set 𝒰 := {u : p^u ∈ 𝒟}, which contains G^{sites} by invariance, and Ψ = 0 on G^{sites} by the law at p. G is compact, so G^c = G·exp(i𝔤) and T_gG^c = T_gG ⊕ iT_gG: G^{sites} is a totally real submanifold of maximal dimension, and an analytic function vanishing on it vanishes near it. So Ψ vanishes on the connected component of 𝒰 containing 1, which contains the path u_t. Hence Ψ(u₁) = 0. ∎

Cov(j) is this law on 𝒟_W (#MD2.2.4.3–5), so the lemma applies to every insertion on its production domain, the new groups of step k+1 included, and the step owes no covariant clause beyond Cov(k+1) and D(k+1)(iii). For closed words it is (6)(b7)'s *G^c-valued u* (#MD2.2.6.86-12).

**The base-point form.** Put Ŷ_W := Y_Wπ(𝐔(I_W))^{−1}. Since 𝐔^v(I_W) = v(x_W)𝐔(I_W)v(x′_W)^{−1}, Ŷ_W obeys the law with x′_W replaced by x_W. Lemma 1 then gives, for u(x_W) = 1:

  Ŷ_W(𝐔^u, R(u)𝐉) = Ŷ_W(𝐔, 𝐉).

## 2. Lemma 2 (Gauge Reduction of the Complex Part)

Let δ_W ≤ δ̄ := min(1/2, CM/(2L)). Then there is ω: sites(X_W) → 𝔤^c with ω(x_W) = 0 and |ω| ≤ 4α_{1,k+1}δ_W. With u_t := exp(itω) it gives 𝐔^{u_t} = e^{iηA″_t}U, with the same real base U, where on X_W:
- |ηA″₁| ≤ K₁aδ_W;
- |ηA″_t| ≤ 3a for t ∈ [0, 1];
- the covariant change of ηA″_t per fine step is ≤ K₂aL^{−(k+1)}.

Here K₁ := 2(1+2b̂) + c(α_{1,k+1} + b̂) and K₂ := 1 + c(Lb̂ + α_{1,k+1}), with b̂ := LBCM·max(α_{0,k}, α_{0,k+1}) and c a constant of the group. So 2 ≤ K₁ ≤ 3 and K₂ ≤ 2 for g_K small, with L and M fixed before g.

*(a) The smooth gauge.* Let B be the smallest ℓ∞-cube containing X_W; its side is ≤ δ_W ≤ δ̄ ≤ CM/(2L).
- If B meets Ω_{k+1}ᶜ: a cube of side CM/L containing B meets Ω_{k+1}ᶜ, and each of its points is within CM/L of X_W ⊂ Ω_{k+1}, so it lies in Ω_k by (K2). It is a layer-k cube of (2.38) (K1).
- If B ⊂ Ω_{k+1}: the partition cubes meeting B form a box of at most 2⁴ cubes, all in Ω_{k+1}, of side ≥ MR_{k+1} ≥ CM in each direction (K2). The box contains a top-layer cube of side CM that contains B.

In either case (2.38) gives a G-valued v on the cube with U^v = exp iξA, |ξA| ≤ b̂L^{−(k+1)} per fine bond and a change ≤ Lb̂L^{−2(k+1)} per fine step (CRE p.261: L^nξ|A|, (L^nξ)²|∇^ξA| < BCMα_{0,n}, at n = k the larger). The sup and the covariant change are gauge invariant, and R(v) is real orthogonal, so the computation below is made in this gauge.

*(b) The construction.* For each direction μ, let a_μ := ηA′(b_μ) at a fixed bond b_μ of X_W in direction μ (a_μ := 0 if there is none). Put ω(x) := Σ_μa_μ(x − x_W)_μ. Then |ω| ≤ a·4δ_WL^{k+1} = 4α_{1,k+1}δ_W.

For b = (x, x+e_μ) ⊂ X_W, with X := ω(x), Y := ηA′(b), Z := ξA(b) and ω(x+e_μ) = X + a_μ:

  e^{iηA″₁(b)} = e^{iX}e^{iY}e^{iZ}e^{−iX−ia_μ}e^{−iZ}.

The first-order exponent is i(Y − a_μ). The bonds b_μ and b are joined by a chain of bonds of direction μ in X_W, each a unit translate of the previous one, with at most 2δ_WL^{k+1} steps: inside one closed cube of side s := ML^j two such bonds are joined by at most ds translations; two cubes sharing a corner v contain bonds b′ ∋ v and b″ ∋ v of direction μ with b″ ∈ {b′, b′ ± e_μ}; and a chain through at most σ_j(W) cubes has at most σ_j(W)(ds + 1) ≤ 2δ_WL^{k+1} steps (δ_WL^{k+1} = 4sσ_j(W)).
Each step changes ηA′ by at most the covariant change plus the commutator with ξA, aL^{−(k+1)} + 2|ξA|a ≤ aL^{−(k+1)}(1 + 2b̂). So |Y − a_μ| ≤ 2δ_Wa(1 + 2b̂).

The second-order exponent is −½([X, 2Y − a_μ] + 2[X, Z] − [Y, a_μ] − 2[Z, a_μ]). Its size is at most c(|ω|a + |ω||ξA| + a² + a|ξA|), and the four terms are ≤ aδ_W times 4α_{1,k+1}, 4b̂, α_{1,k+1}, and b̂ respectively; for the last two this uses δ_W ≥ 4ML^{−m}, so a/δ_W ≤ α_{1,k+1}L^{−j}/(4M) and |ξA|/δ_W ≤ b̂L^{−j}/(4M). Higher orders are smaller, since |X|, |Y|, |Z| ≪ 1. This gives the first bound.

At t ∈ [0, 1] the first-order exponent is i(Y − ta_μ), of size ≤ 2a, plus the same corrections. The per-step changes are:
- of Y: ≤ aL^{−(k+1)}(1 + 2b̂);
- of a_μ: 0;
- of the commutators: ≤ |ΔX|(|Y| + |Z|) + |X|(|ΔY| + |ΔZ|), with |ΔX| ≤ a and |ΔZ| ≤ Lb̂L^{−2(k+1)}, which is ≤ aL^{−(k+1)}(α_{1,k+1} + b̂ + 4δ_W(α_{1,k+1} + Lb̂)).

With the commutator of ηA″_t with ξA (≤ 6b̂aL^{−(k+1)}) this gives K₂. ∎

## 3. Lemma 3 (The Carried Complex-Data Excess)

Let μ := min(1, MC₀/(2C_avC₁)) and δ_W ≤ δ̄₀ := min(δ̄, μ). Take u := u₁ of Lemma 2, and put R_A := μϱ_j/(2K₁aδ_W), R_J := r_J^{(j)}/(6r_J^{(k+1)}) and R := min(R_A, R_J). Then R ≥ 2 and

  ‖Y_W(𝐔, 𝐉)‖ ≤ 2·(4/R)S_We^{νσ_j(W)/8192} + ‖Y_W(U, J)‖·(1 + 2c_π′α_{1,k+1}|I_W|),  4/R ≤ (1+β₀)²m^{1/2}L^{−m}(8K₁δ_W/μ + 24L^{−2m}).

*R and 4/R.* Since δ_W ≤ μ and K₁ ≤ 3, R_A ≥ ϱ_j/(2K₁a) ≥ 2, and R_J ≥ 2 (§0). Also 4/R ≤ 4/R_A + 4/R_J = 8K₁aδ_W/(μϱ_j) + 24r_J^{(k+1)}/r_J^{(j)}, and §0's ratios give the second display.

The second term of the bound is the real-point part; the first is the complex-data excess. Its factor 2 bounds ‖π(𝐔(I_W))‖, and e^{νσ_j(W)/8192} bounds the inverse transport at the disc points ((b)), paid in §4.

*(a) Covariance.* Since u(x_W) = 1, the base-point form gives Y_W(𝐔, 𝐉) = Ŷ_W(𝐔^u, R(u)𝐉)π(𝐔(I_W)). Lemma 1 applies on 𝒟_W once the path points (𝐔^{u_t}, R(u_t)𝐉), t ∈ [0, 1], lie in 𝒟_W:
- the sup is |ηA″_t| ≤ 3a ≤ ϱ_j/4 (Lemma 2, §0);
- the per-step change is ≤ K₂aL^{−(k+1)} ≤ μα_{1,j}L^{−2j}/(4M), within (2.39)'s allowance: δ_W ≥ 4ML^{−m} and δ_W ≤ μ give L^{−m} ≤ μ/(4M), so K₂aL^{−(k+1)} = K₂α_{1,k+1}L^{−2j}L^{−2m} ≤ 2(1+β₀)²m^{1/2}L^{−m}·(μ/(4M))α_{1,j}L^{−2j};
- the real factor U = U_{k+1} = U_j(V_j^*) is a step-j base point (#MD2.4.5.13 (2), one of (T-dev)'s inputs);
- |R(u_t)𝐉 − J| ≤ |𝐉 − J| + 2c_Ge^{2c_G|ω|}|ω||𝐉| ≤ 3r_J^{(k+1)} ≤ r_J^{(j)}/4, by §0 and |ω| ≤ 4α_{1,k+1}δ_W, for g_K small;
- (2.34), (2.35) and (2.37) as in (b).

For j = 1 only the sup bound counts (§0).

*(b) The disc.* Put f(z) := Ŷ_W(e^{izηA″₁}U, J + z(R(u)𝐉 − J)) for |z| < R; then f(1) = Ŷ_W(𝐔^u, R(u)𝐉) and f(0) = Ŷ_W(U, J). On the disc:
- the sup is < RK₁aδ_W ≤ μϱ_j/2;
- the 𝐉-deviation is < 3Rr_J^{(k+1)} ≤ r_J^{(j)}/2;
- the per-step change is < RK₂aL^{−(k+1)} ≤ μϱ_jK₂L^{−(k+1)}/(2K₁δ_W) ≤ μα_{1,j}L^{−2j}K₂/(8K₁M) ≤ μα_{1,j}L^{−2j}/(4M), by δ_W ≥ 4ML^{−m} and ϱ_j = α_{1,j}L^{−j}.

*Curvature at the path and disc points.* For 𝐔′ = e^{iηA″}U the exponent of ∂𝐔′(p)∂U(p)^{−1} is the sum of the covariant differences of ηA″ across the two pairs of opposite sides of p plus second-order terms, so per plaquette |∂𝐔′ − 1| ≤ (1 + O(α_{1,j}))(|∂U − 1| + 2·(per-step change)) + c_d|ηA″|². At the path and disc points this is ≤ T₁ + T₂ + T₃, with:
- T₁ := 3B₃ε_{k+1}L^{−2(k+1)}, from |∂U_{k+1} − 1| < 2B₃ε_{k+1}(L^{−1}η)² on Ω_{k+1} (CRE p.268 l.38–39; map #MD2.2.6.136);
- T₂ := μα_{1,j}L^{−2j}/M, from the per-step bounds above;
- T₃ := c_dα_{1,j}²L^{−2j}, from |ηA″| ≤ max(3a, μϱ_j/2) and 9a² ≤ α_{1,j}²L^{−2j} (§0).

C_avT₂ ≤ α_{0,j}L^{−2j}/2 by the choice of μ, since α_{1,j}/α_{0,j} = C₁/C₀ at q₀ = q₁. C_av(T₁ + T₃) ≤ α_{0,j}L^{−2j}/4 for g_K small, since ε_{k+1}L^{−2m}/α_{0,j} ≤ (1+β₀)²m^{1/2}L^{−2m}(A₀/C₀)(log g_j^{−2})^{p₀−q₀} → 0 uniformly in m (CRE (2.8), p.256; (2.28), p.259; p.255: ε_j = g_jA₀(log g_j^{−2})^{p₀}; q₀ > p₀) and α_{1,j}²/α_{0,j} = (C₁²/C₀)g_j(log g_j^{−2})^{q₁} → 0.
So the C_av-weighted curvature is ≤ (3/4)α_{0,j}L^{−2j}. This gives (2.34) on the top layer (factor 1, C_av ≥ 2) and, by the averaging bound (K3), (2.35) and (2.37). So the path and disc points lie in 𝒟_W. No condition on M is used: M ≥ 2C_avC₁/C₀ = 2C_avλ_R cannot hold, since λ_R grows with M.

*The estimate.* Since Ŷ_W = Y_Wπ(𝐔(I_W))^{−1}, sup_{disc}‖f‖ ≤ S_W·sup_{disc}‖π(𝐔_z(I_W))^{−1}‖, 𝐔_z := e^{izηA″₁}U. The phase per fine bond at a disc point is < μϱ_j/2 ≤ α_{1,j}L^{−j}/2, and I_W has at most |I_W|L^{k+1} ≤ ML^jσ_j(W) fine bonds (§0). By ‖π(e^{iX})‖ ≤ e^{c_π′|X|} (map #MD2.1.4.27) the inverse transport is ≤ e^{(c_π′/2)α_{1,j}Mσ_j(W)} ≤ e^{νσ_j(W)/8192}, by c_π′α_{1,j}·4096M ≤ ν (map #MD2.4.13.19).
Cauchy's integral formula on |z| = ρ, ρ ↑ R, gives ‖f(1) − f(0)‖ ≤ sup‖f‖/(R − 1) ≤ (4/R)S_We^{νσ_j(W)/8192}. Finally ‖Y_W(𝐔, 𝐉)‖ ≤ (‖f(1) − f(0)‖ + ‖f(0)‖)‖π(𝐔(I_W))‖, where ‖f(0)‖ = ‖Y_W(U, J)‖, π(U(I_W)) being unitary, and ‖π(𝐔(I_W))‖ ≤ e^{c_π′α_{1,k+1}|I_W|} ≤ min(2, 1 + 2c_π′α_{1,k+1}|I_W|), since the phase along I_W is ≤ a|I_W|L^{k+1} = α_{1,k+1}|I_W| and |I_W| ≤ δ_W/4 ≤ 1/8. ∎

**The non-covariant bound.** For every W, with no condition on δ_W, ‖Y_W(𝐔, 𝐉) − Y_W(U, J)‖ ≤ 4c_nc(1+β₀)²m^{1/2}L^{−m}S_W, with c_nc below.
- *The disc.* Put f(z) := Y_W(e^{izηA′}U, J + z(𝐉 − J)) and R′ := min(ϱ_j/(2a), (C₀/(C_avC₁))L^{2m}/(16(1+β₀)²m^{1/2}), (r_J^{(j)} − r_J^{(k+1)})/(4r_J^{(k+1)})). For |z| < 2R′:
  - the sup is < 2R′a ≤ ϱ_j, and the per-step change is < 2R′aL^{−(k+1)} ≤ α_{1,j}L^{−2j}L^{−m};
  - |J + z(𝐉 − J)| < r_J^{(k+1)} + 4R′r_J^{(k+1)} ≤ r_J^{(j)};
  - the C_av-weighted curvature is ≤ C_av(T₁ + T₃) + (1 + O(α_{1,j}))C_av·4R′α_{1,k+1}L^{−2(k+1)} ≤ (3/4)α_{0,j}L^{−2j}, by the middle entry and α_{1,k+1} ≤ (1+β₀)²m^{1/2}(C₁/C₀)α_{0,j} (§0, q₀ = q₁), with T₃ as in (b) since 2R′a ≤ ϱ_j.

  So the disc lies in 𝒟_W, as in (b); the transport is inside S_W, so sup‖f‖ ≤ S_W.
- *For m ≥ m₀.* The three entries of R′ are bounded below by functions of m alone (§0): ϱ_j/(2a) ≥ L^m/(2(1+β₀)²m^{1/2}), the middle entry is one, and the third is ≥ (L^{3m}/((1+β₀)²m^{1/2}) − 1)/4. Each increases with m for L ≥ 2, since L^m/m^{1/2} does. Let m₀ be the least integer m₀ ≥ 1 such that all three are ≥ 2 for every m ≥ m₀; it depends on L, C_avC₁/C₀ and β₀ only, and R′ ≥ 2 for m ≥ m₀.
  Then ‖f(1) − f(0)‖ ≤ S_W/(2R′ − 1) ≤ (4/R′)S_W, and, entry by entry, 4/R′ ≤ 8(1+β₀)²m^{1/2}L^{−m}max(1, 8C_avC₁/(C₀L)): the first gives 8a/ϱ_j; the middle gives 64(1+β₀)²m^{1/2}(C_avC₁/C₀)L^{−2m}; the third, where it is the minimum (so r_J^{(j)} ≥ 9r_J^{(k+1)}), gives 16r_J^{(k+1)}/(r_J^{(j)} − r_J^{(k+1)}) ≤ 18r_J^{(k+1)}/r_J^{(j)} ≤ 18(1+β₀)²m^{1/2}L^{−3m}.
- *For m < m₀.* ‖Y_W(𝐔, 𝐉)‖ + ‖Y_W(U, J)‖ ≤ 2S_W. At step-(k+1) data a carried insertion is its production function at the composite point reached through the evaluation maps of the steps k, …, j, and that point lies in 𝒟_W by D2.2(4)(f)'s chain condition (map #MD2.2.4.66–85, with #MD2.2.6.142 and the RMJ closure for (2.35) and (2.37)) applied at i = k, k−1, …, j, the step-i point having its base in D(i+1)(iii)'s domain by the previous application.
  For an insertion untouched since step j the composite point is (𝐔, 𝐉) itself ((4)(e) at s = 0, with 𝐉 carried by (4)(f) *Carrying 𝐉*, map #MD2.2.4.86–90), so both branches bound the same difference. This branch uses neither (K3) nor R′.
- *The constant.* c_nc := max(2max(1, 8C_avC₁/(C₀L)), max_{m<m₀}L^m/(2(1+β₀)²m^{1/2})), finite and independent of k.

## 4. The Carry, Uniformly in k

Fix a step-(k+1) traversal n′. The generation-j insertions meeting n′ meet one of its L^m step-j traversals ((12)(b) *It carries*, iterated). Let P_j be the production (ii-w) sum per step-j traversal, with the weight e^{θ + ν_rσ + ν_e·ext}, so P_j ≤ N^{(j)}ρ_jpl_j. Here N^{(j)} is the constant of the new groups of step j: N^{(j)} ≤ 2C_winC_M + s_{j−1}C^{(j−1)}, where s_{j−1} := (1+β₀)⁷[(β) term + quadratic term] is that part of (12)(f)'s θ_{j−1} (#MD2.4.12.50), and N^{(1)} := C^{(1)}.

The complex-data part of the carried insertions is stated with the reserve weight (15/16 − 1/8192)ν_rσ in place of ν_rσ: ν_r/16 pays δ_W and ν/8192 = ν_r/8192 (ν_r = ν, map #MD2.0.3.32, #MD2.4.12.6) pays Lemma 3's inverse transport. The free eighth of the reserve budget (#MD2.4.12.27-4: 7/8 used) covers both, and the consumers' 7/8 still fit. Then σe^{−(ν_r/16)σ} ≤ 16/(eν_r), so the weighted sum of δ_W = 4ML^{−m}σ_j(W) is at most (64M/(eν_r))L^{−m} times the unweighted one.

For δ_W > δ̄₀ the non-covariant bound is used: there σ_j(W) > δ̄₀L^m/(4M), so e^{−(ν_r/16)σ} ≤ e^{−ν_rδ̄₀L^m/(64M)}. Summing Lemma 3 and the non-covariant bound over the generation-j insertions at the L^m step-j traversals of n′:

  E_j ≤ (1+β₀)²m^{1/2}[1024K₁(M/(eν_rμ))L^{−m} + 48L^{−2m} + 4c_nce^{−ν_rδ̄₀L^m/(64M)}]·P_j.

With ρ_j ≤ (1+β₀)^{6m}ρ_{k+1} and pl_j ≤ (1+β₀)^m pl_{k+1} (#MD2.4.12.49-5; CRE (2.7)):

  Σ_{j≤k}E_j ≤ Ĉ·max_{j≤k}N^{(j)}·ρ_{k+1}pl_{k+1},

  Ĉ := Σ_{m≥1}(1+β₀)^{9m}m^{1/2}[1024K₁(M/(eν_rμ))L^{−m} + 48L^{−2m} + 4c_nce^{−ν_rδ̄₀L^m/(64M)}].

Ĉ is finite for L > (1+β₀)⁹; the last series converges for every L > 1, since δ̄₀ does not depend on m. With K₁ ≤ 3 (§2), Ĉ depends only on L, M, ν_r, β₀, (2.38)'s cube constant C (through δ̄, fixed, not absolute, map #MD2.2.6.189), and C_avC₁/C₀ = C_avλ_R (through c_nc, m₀ and μ), not on k or g.

**The recursion of (12)(f).** The complex-data part is bounded from the production constants directly, so:

  C^{(k+1)} ≤ (1+Ĉ)·max_{j≤k+1}N^{(j)} + L^{−1}(1+β₀)^{15}C^{(k)}.

Let L^{−1}(1+β₀)^{15} ≤ 1/8 (#MD2.4.12.51), and C_S′ := max(2(1+Ĉ)C^{(1)}, 8(1+Ĉ)C_winC_M). Let s̄ be the sup over j of s_j evaluated with C^{(j)} ≤ C_S′; then s̄ → 0 as g_K → 0 (q₀ = q₁ > p₀; C_S′ρ_j → 0), and (1+Ĉ)s̄ ≤ 1/4 for g_K small. Then C^{(k)} ≤ C_S′ for all k ≤ K, by induction: the term j = 1 of the max is (1+Ĉ)C^{(1)} ≤ C_S′/2; for j ≥ 2, N^{(j)} ≤ 2C_winC_M + s̄C_S′ by the induction hypothesis, and:
- (1+Ĉ)2C_winC_M ≤ C_S′/4;
- (1+Ĉ)s̄C_S′ ≤ C_S′/4;
- L^{−1}(1+β₀)^{15}C_S′ ≤ C_S′/8.

In either case the total is at most 5C_S′/8 ≤ C_S′. (S-w), the KP condition for the reference gas, (Z)'s C̄_Z, and (T′) follow as in (12)(f)–(g) and (13), with this C_S′; the KP smallness C_S′ρ_{k+1}pl ≤ ν/(64·81M) holds for g_K small.

## 5. The Region of SW §6(6c)

SW §6(6c)'s region 𝒬^{(j)}_n(W)^{∼5} is, in step-(k+1) units, in general smaller than a π_{k+1}-cube, so (LPG′) at step k+1 does not apply to it. The bound of §3 and §4 uses no gauge on it.
- *The real-point part.* At the real base, π(U(I_W)) is unitary, so ‖Ŷ_W(U_{k+1}, J_{k+1})‖ = ‖Y_W(U_{k+1}, J_{k+1})‖, which (T-dev), #MD2.4.5.12, bounds. (T-dev) is derived at the background of step j:
  - #MD2.4.5.13 (1) runs (4)'s Cauchy step with (LPG′) at step j for U_j(V_j^*);
  - the region is in step-j units (SW §5(e)'s per-traversal region at step j, a union of π_j-cubes), which is (LPG′)'s own cube class at step j;
  - #MD2.4.5.13 (2) gives U_j(V_j^*) = U_{k+1}.
- *The excess.* For δ_W ≤ δ̄₀ it uses the real smooth gauge of (2.38) on a cube of side CM or CM/L ((K1), (K2)), Lemma 1 on 𝒟_W, and Cauchy's estimate there. For δ_W > δ̄₀ it uses Cauchy's estimate alone.

Hence the carried insertions satisfy, on 𝒟_{k+1}^{sub} and per insertion,

  e^{θ(W)}‖Y_W(𝐔, 𝐉)‖ ≤ (1 + 2c_π′α_{1,k+1}|I_W|)·b_WDev_W(U_{k+1}) + e^{θ(W)}ε_W,

where ε_W is the excess of Lemma 3 or of the non-covariant bound, and, by §4, Σ_{j≤k}Σ_{W of generation j meeting n′}e^{θ(W)}ε_W ≤ Ĉ·max_{j≤k}N^{(j)}·ρ_{k+1}pl_{k+1}.
- The first term is the per-insertion form, with Dev_W in step-j normalisation (#MD2.4.5.6) over the per-traversal region of SW §4.
- The second term is in the sup form in which SW §6(6b) states the new groups' clause, which is all the consumers use.

This is D(k+1)(iii)-dev for the carried insertions.

**Constants added by this note.**
- L ≥ 12(1+β₀)² (§0, §3) and L > (1+β₀)⁹ (§4), both implied by the map's L ≥ L₀ = 5000 with β₀ ≤ 1/2.
- The disc factor μ := min(1, MC₀/(2C_avC₁)) and the regime δ̄₀ := min(δ̄, μ) (§3), in place of a condition on M.
- c_nc and m₀ (§3).
- The reserve weight (15/16 − 1/8192)ν_rσ for the complex-data part (§4), in σ_j(W), which dominates the consumers' weight in σ_k(W) (#MD2.4.12.27-4), since σ_k(W) ≤ σ_j(W) (coarser π-cubes and arc lengths in coarser bonds).
- c_π′α_{1,j}·4096M ≤ ν for every j ≥ 1 (map #MD2.4.13.19, stated at index k+1 at each step k ≥ 0), for the disc transport (§3(b)).
- B₃ ≥ 1 ((K3)) and g_K small.

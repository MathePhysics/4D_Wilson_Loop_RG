# Complex Gauge Covariance of the Carried Insertions

*Status: derived, not reviewed.* This note derives the step map's item at l.168 (D2.4(12)(b) *It carries*, (12)(f), (13)(d)): the uniformity in k of the carried insertions at complex data (§1–§4), and the region of SW closure §6(6c) (§5). It is derived given (T-dev)'s own inputs (l.1353), SW §6(6d)'s (2.38) for U_{k+1}, D2.2(4)(f)'s chain condition with reading R-m, with (2.35) and (2.37) at the evaluation points from map l.928's joint derivation with R-mJ (R-m's (2.37) part, wider than the print; WILSON_IT1_RMJ_CLOSURE_2026_10_30.md), given R-p (forced, map l.928), the provisional q₀ = q₁ > p₀, and the accepted readings R-dec, R-cpl₀ and R-adm (not reviewed; used by §3's trivial branch, already among the map's global conditions, l.1614), and R-av of (K3), which reads RG1 p.263 (1.17) (averaging constant C_av := 2(B₃ + 2c_dB₅), VAR Proposition 9) in CRE's notation on the top layer Ω_j, with one uniform constant (l.13); no per-layer form is used. The carried dev insertions do not depend on the slot values (§0, derived given rule change (5) of the D2.6 closure, for review), so (K4) and §3(c) are not needed. Map line numbers refer to WILSON_IT1_D2_STEP_MAP_2026_10_22.md (1614 lines). C₀ and C₁ are R-m's constants in α_{i,k} = g_kC_i(log g_k^{−2})^{q_i}. K₁ and K₂ are this note's constants, and C_av := 2(B₃ + 2c_dB₅) is the averaging constant of (K3), B₃ VAR's constant (d and L only).

**Checks (K1)–(K4) ((K1), (K2) derived; (K3) derived given R-av; (K4) not needed, §0):**
- (K1) CRE p.261 (ii) poses (2.38) "for each cube □ ⊂ Ω_n∖Ω_{n+2}, □ ∩ Ω_{n+1}^c ≠ ∅, n = 1, …, j−1, of the size CML^nξ, or □ ⊂ Ω_j and of the size CM", on □ ∩ X: every cube of the stated size. In Ũ^c_{k+1} (L^{k+1}ξ = 1), the top-domain cubes are therefore the cubes of side CM in Ω_{k+1}. The layer-k cubes are the cubes of side CM/L in Ω_k that meet Ω_{k+1}ᶜ. Ω_{k+2} is not defined at index k+1 and is read as ∅. The bounds of §2(a) are (2.38)'s at n = k and n = k+1, converted to fine bonds. (2.38) holds for U = U_{k+1} by SW §6(6d).
- (K2) Derived from CRE pp.254–256 and (3.5).
  - Partition cubes. By p.256, Ω_j and Λ_j "are unions of MR_j-cubes in the lattice T_{L^{−j}}". At j = k+1 these are cubes of side MR_{k+1} in step-(k+1) units. R_{k+1} ≥ (log g_{k+1}^{−2})^r ≥ C for g_K small ((2.5)).
  - Collar. p.254 gives Ω_k ⊃ Λ_k, so Z_k = Λ_kᶜ ⊃ Ω_kᶜ. (3.5) and p.265 give Ω_{k+1} ⊂ ((B^{k+1}(P¹)ᶜ)^{∼3})ᶜ, and B^{k+1}(P¹)ᶜ ⊃ Z_k′^{∼5} ⊃ Z_k. So Ω_{k+1} ⊂ (Z_k′^{∼8})ᶜ. The layers are LMR_{k+1}-cubes of T_η, which are MR_{k+1}-cubes in step-(k+1) units (p.264: "the corresponding partition of the lattice T_{L^{−1}η} into MR_{k+1}-cubes").
  - Conclusion. Every point of Ω_{k+1} is at distance ≥ 8MR_{k+1} > CM/L from Ω_kᶜ.
- (K3) (2.35) and (2.37) at the path and disc points of §3, with C_av := 2(B₃ + 2c_dB₅) (derived, R-av below).
  - *Source.* RG1 p.263 (1.17): for complex (𝐔, 𝐉) satisfying (i)–(iii) of RG1's definition with α′₀, α′₁ in place of α₀, α₁, "M^·(𝐔) = 𝐔̄^p on Λ_p, |∂𝐔̄^p − 1| < 2α′₀(L^pξ)²", and "From Proposition 9 [15]" (VAR), |∂U_n(M^·(𝐔)) − 1| < 2B₃α′₀ξ² and |J_n(M^·(𝐔))| < 2B₃α′₀(L^nξ)² on X̃^{−2}; "for α′₀ sufficiently small the above estimates imply the condition (iv)", which is RG1's (1.16), the single-domain form of CRE (2.35) and (2.37). VAR Proposition 9 (p.309) gives the analytic extension of U_k(V′V₀) to G^c-valued small V′, and VAR Theorem 1 (p.279) is already multi-domain, 𝔘_k({Ω_j}, B₃ε₁), with one ε₁ for all block plaquettes (VAR (7), p.278). Proposition 9 prints ε₂ = B₅ε₁ with B₅ = 6B₁B₃C₁ (VAR (173), p.305), so the B₃ of (1.17) at complex 𝐔 is RG1's constant; B₃ and B₅ depend on d and L only (VAR p.279 l.28 for B₃; B₁ = 5dLB₀, VAR p.296 l.11, with C₁^{VAR} := VAR's absolute constant C₁ of (173), not R-m's C₁).
  - *R-av (top layer, uniform).* If X ⊂ Ω_j, the (2.34)-curvature per plaquette on X is < α′ with C_avα′ ≤ α_{0,j}L^{−2j}, and (2.38), (2.39) hold, then CRE (2.35) and (2.37) hold on X ∩ Ω_j (on X̃^{−2} by RG1 (1.17), on X ∖ X̃^{−2} by the last part of this bullet). This is RG1 (1.17) with VAR Theorem 1 and Proposition 9 in CRE's notation, CRE's spaces being defined "similarly as in (I.1.11)–(I.1.16)" (CRE p.261 l.2–3): it takes CRE's U_{p,X}(M^·(𝐔)) for RG1's U_n(M^·(𝐔)) (CRE defines 𝐁_p(X) only through that sentence), and, for (2.37), RG1's J-normalisation α₀(L^nξ)², with RG1's n read as CRE's p and ξ = L^{−j}, with CRE's (2.37) at n = j for every p ≤ j (α₀L^{−2(j−p)} = α_{0,j}L^{j−p}(L^{j−p})^{−3}, coefficient α_{0,j} in both). RG1's hypotheses (i)–(ii) with α′ are supplied as follows: the curvature parts (1.11), (1.14) by the hypothesis on the (2.34)-curvature, since (2.34) bounds both U and 𝐔; (ii) by (2.39); and (1.12) with RG1's coefficient α′₀ := α′L^{2j} = α_{0,j}/C_av (ξ = L^{−j}), |A|, |∇^ξA| < O(1)LMBα′₀, which RG1 p.262 poses on the G-valued factor U of 𝐔 = U′U. At the base U = U_{k+1}, VAR Theorem 1 (9), |A| < B₃Mε₁(L^jη)^{−1}, with ε₁ = O(L²)ε_{k+1} (SW closure §6(6d); cf. CRE p.267 (3.12)), converted to RG1's step-j field normalisation (RG1's cubes of size O(1)LM step-j units lie inside (6d)'s cubes), gives |A| ≲ B₃Mε₁L^{−m} and |∇^ξA| ≲ B₃Mε₁L^{−2m}; and ε₁L^{−m}/α′₀ ≤ O(L²)·C_av(1+β₀)m^{1/2}L^{−m}(A₀/C₀)(log g_j^{−2})^{p₀−q₀} → 0 uniformly in m, since m^{1/2}L^{−m} ≤ 1/2 (CRE (2.4), (2.8), (2.28); q₀ > p₀), so B₃Mε₁L^{−m} ≪ O(1)LMBα′₀ for g_K small, and likewise with L^{1−m} near ∂Ω_{k+1} (the scale-k class of (6d)) and with L^{−2m} for the gradient. The L^{−m} gain is necessary: ε_{k+1}/α_{0,j} itself is not bounded uniformly in m (it grows like g_{k+1}/g_j). The same conversion and comparison give R-av's hypothesis (2.38) for U_{k+1} in the step-j normalisation (CRE p.261 l.26–33 at n = j), which (K1) states only at n = k and n = k+1. Every path and disc point of §3 has the same real factor U_{k+1} (§2, §3(b), and the non-covariant disc e^{izηA′}U), the displacement entering only RG1's (ii), so (1.12) with α′₀ holds there as at the base. The 𝐉-bound |𝐉| < γ₀ of (1.14) is not used by (1.17), since J_n(M^·(𝐔)) is a function of 𝐔 alone (RG1 (1.15), *No 𝐉-average* below). No per-layer form is used or claimed. *On X ∖ X̃^{−2} (derived).* RG1 (1.16)–(1.17) state the bounds on X̃^{−2} (RG1 p.262 l.52 and l.59), and CRE (2.35), (2.37) are printed on all of X ∩ Ω_j. The whole of X follows from VAR directly, with X as Ω₀ (RG1 (iv), p.262 l.41): VAR's configurations live on Ω₀, its action sums over the plaquettes p ⊂ Ω₀ (VAR (5), p.278), and Theorem 1 puts the minimal orbit in 𝔘_k({Ω_j}, B₃ε₁) (VAR (8), p.279), whose conditions (2), |(∂U)(p) − 1| < B₃ε₁L^{−2j} on every plaquette p ∈ Ω_j and |(D_U^{η*}∂U)(b)| < B₃ε₁L^{−2j}(L^jη)^{−1} on every bond b ∈ Ω_j (p.278 l.2–8), hold up to ∂Ω₀; at complex data, 𝐔 = U′U with the real V₀ := M^·(U) and V′ := M^·(𝐔)V₀^{−1}, Proposition 9 gives U_k(V′V₀) = e^{iη𝓗(B)}U_k(V₀) with (19), |A|, |∇A|, |D*DA| < ε₂(L^jη)^{−1}, (L^jη)^{−2}, (L^jη)^{−3} on Ω_j for every j (p.281 l.6–10), ε₂ = B₅ε₁ (p.309), again up to ∂Ω₀. So |∂U_{p,X}(M^·(𝐔)) − 1| ≤ (B₃ + 2c_dB₅)ε₁L^{−2j} and the current's bound with the same constant hold on all of X ∩ Ω_j, c_d the constant of |∂(e^{iηA}U) − ∂U| ≤ c_d(η²|∇_UA| + η²|A|²) and of its D*-analogue (ε₂ ≤ 1); with ε₁ = 2α′ from the averages' curvature (RG1 p.263 l.10) this is R-av's conclusion on all of X ∩ Ω_j with C_av := 2(B₃ + 2c_dB₅) in place of 2B₃, a constant of d and L only. §3's choices use C_av only through μ := min(1, MC₀/(2C_avC₁)) and the smallness of C_av(T₁ + T₃), both valid for any such constant.
  - *No 𝐉-average.* J_{p,X}(M^·(𝐔)) is a function of 𝐔 alone: RG1 (1.15) defines J_n(M^·(𝐔)) "by the formula (1.8) with U_n(M^·(𝐔)) instead of U_j". So the rotation R(u)𝐉 enters only (2.36), checked in §3(a)–(b).
  - *At the disc points.* The curvature per plaquette is ≤ T₁ + T₂ + T₃ (§3(b)), with T₁ := 2B₃ε_{k+1}L^{−2(k+1)} at the real base U_{k+1} = U_j(V_j^*) (CRE p.268 l.38–39; l.1353 (2)), T₂ := μα_{1,j}L^{−2j}/(2M) the per-step term, with §3's disc factor μ := min(1, MC₀/(2C_avC₁)), and T₃ := O(α_{1,j}²)L^{−2j}. Then C_avT₂ = (C_av/2)μ(C₁/C₀)α_{0,j}L^{−2j}/M ≤ α_{0,j}L^{−2j}/4 by the choice of μ (C_av = 2(B₃ + 2c_dB₅); q₀ = q₁, SW closure §2; q₀ > p₀ is the premise of SW §6(6e)). No condition on M is used: C₁ = λ_RC₀ with λ_R = K_RLM + 1 (CRE p.262 l.43–46 with RG1 p.277 l.54; table #T2.24), so M ≥ 2C_avC₁/C₀ cannot hold. And C_av(T₁ + T₃) ≤ α_{0,j}L^{−2j}/4 for g_K small, since ε_{k+1}L^{−2m}/α_{0,j} ≤ (1+β₀)m^{1/2}L^{−2m}(A₀/C₀)(log g_j^{−2})^{p₀−q₀} → 0 uniformly in m (CRE (2.8), p.256; (2.28), p.259; p.255: ε_j = g_jA₀(log g_j^{−2})^{p₀}; q₀ > p₀) and α_{1,j}²/α_{0,j} = O(g_j(log g_j^{−2})^{q₁}). The sum is ≤ α_{0,j}L^{−2j}/2 ≤ (1−β)α_{0,j}L^{−2j}, so R-av gives (2.35) and (2.37) on X_W ⊂ Ω_j (top layer n = j).
- (K4) l.961 with 8c_G in place of 4c_G reads 32c_GC_w′(2θ)^{k−j−1}h_k(|σ_{j,0}|/r_{ω,j} + 1) ≤ 1. l.963 bounds the left side by C·g_k^{1/2}(log g_k^{−2})^{q₁+p₀}(2θ)^{k−j−1}(1 + β′(k−j))^{1/4}(1 + log(1 + β′(k−j)))^{p₀}. That bound is small uniformly in k for g_K small, so the doubled constant holds, and half of each step's slot margin would be left for §3(c). Not needed: carried dev insertions do not depend on σ (§0, derived given rule change (5) of the D2.6 closure, for review), so §3(c) uses no slot margin, l.164's half stands, and l.961 keeps 4c_G.

## 0. Setting

Step k+1, k ≥ 1. W is a carried dev insertion made at step j ≤ k, m := k+1−j ≥ 1, with X_W ⊂ (Q^#_W)⁺ ⊂ Ω_{k+1} (the scope of (12)(b) *It carries* and of (T-dev), l.1358; for a group of (4), Q^#_𝒢 = X(𝒢)). Y_W(𝐔, 𝐉, σ) is its matrix-valued insertion, with Cov(j) (l.622–624):

  Y_W(𝐔^v, R(v)𝐉, R(v)σ) = π(v(x_W))Y_W(𝐔, 𝐉, σ)π(v(x′_W))^{−1} for G-valued v,

where I_W is its interval from x_W to x′_W. *Carried dev insertions do not depend on the slot values (derived).* The slot values are the outer variables ω′ = (ω, σ_k) (map l.813). The proof is by induction on the production step j. *Step 1.* A dev insertion made at step 1 is built from Υ⁰_W of a good group, a^Λ_W·id and the background transport of its interval (map l.278, l.629), the last two slot-free; Υ⁰_W's traces against π(h) are c⁰_W − a^Λ_Wχ (IT-1 note §3a(1)). c⁰_W consults no outer variable (A_e, a_old, the step-1 outer variable of map l.631; V₀ is part of 𝐔): every input of the rows of ℋ(W) lies in D(Λ), and every selected measure and vacuum occurrence in c_W is built from the kernel at exterior parameter zero (IT-1 note §3d(4), L3080, L4943). a^Λ_W is the reference recipe's coefficient, the same on every term (§3d(4)(c), Lemma c5-5-3(b)). π is irreducible (V3 (H1), map l.1037; V4 lem:c5-5-7), so by Burnside's theorem π(G) spans End(V_π) over ℂ for any compact G, the map Υ ↦ (h ↦ tr(Υπ(h))) is injective, and Υ⁰_W is determined by these traces; so it is ω₀-free. A step-1 insertion depends on the slots only through ω₀ (untouched members are evaluated at (U_{k+1}, ω), D2.2(4)(e); D2.6 closure 4.2(iii)), so it is slot-free at every later step. *Step j ≥ 2, given every dev insertion of step < j slot-free.* A dev insertion made at step j comes from a dev group 𝒢. By D2.6 closure 2.1(i), read structurally, no polymer component and no member's domain of 𝒢 meets the one-cube neighbourhood of Λ_jᶜ, while by 2.2 every domain through which the step's ω′-channels enter meets that neighbourhood (the source term with C's range, the potentials, the 𝐁-terms, A(·), V^{(j−1)}, and the touched members through B′ = g_{j−1}C(σ_{j−1}, A) − hD̃(·) in 𝐇(s, tB′), localised on the touching component by D2.1(4)(b); the ranges of C and D̃ lie within one layer of π_j-cubes, D2.6 closure 2.1; the confinement of the localised action terms' σ_{j−1}-dependence to the terms with Y ⊄ Λ_j is derived in WILSON_IT1_O6_CLOSURE_2026_10_26.md l.17 ("What that forces") and §2); this rests on rule change (5) of the D2.6 closure (the structural test, for review); the vacuum and scalar links of the reference extraction D2.2(6)(c) whose clusters meet Coll_j are att, not dev (2.1(d)), so the dev part contains none; and its members are all dev (2.1 *Merged groups*), hence slot-free by the induction hypothesis. So the activity of 𝒢, an integral of slot-free factors against 𝒢's Gaussian factor dμ_{C^{(j−1)}(Λ_j)} with χ^{(j−1)}, which is σ-free (the σ-dependent factors of the step's measure are local terms that do not belong to 𝒢: the factors e^{−x_X} − 1 of the source term, 2.2(2), the localised potential terms with Y ⊄ Λ_j (𝐏^{(j−1)}, the 𝐄-bracket, 𝐑, 𝐁, A(·), and V^{(j−1)}), and Bałaban's terms with a localisation in Ω_j∖Λ_j, CRE p.272), is slot-free (D2.6 closure 4.2(iii), class (3)). Independence holds at real slot values and therefore, the insertion being analytic on the slot polydisc, on the whole polydisc. Hence Y_W(𝐔, 𝐉, σ) is constant in σ, and the slot argument below is notation only. §3(c)'s cocycle changes no value of Y_W, so §3(c) and (K4)'s doubling are not needed; the regime δ̄_m is kept as a valid narrowing of Lemma 2's, no longer forced; and §5's real-point part is (T-dev) verbatim. It is analytic on its production domain 𝒟_W, which is D(j)(iii)'s domain on X_W with the slot polydisc in the production frame σ̂ = R(c₀^{(j)}(𝐔))^{−1}σ (l.314). Its production size is S_W := sup over 𝒟_W of ‖Y_W‖. It satisfies S_W ≤ S_𝒢 of D2.4(4) (map l.1329–1330), which fixes b_W and hence β_W = b_Wℓ_Wη_j^{−2} (l.1347); the β_W are summed per traversal in (ii-t) (l.1347–1348) and carried in (5) *It carries* (l.1358) given (T-dev), and §4 sums S_W through the production (ii-w) sum (map l.1529–1530, l.1534).

The step-(k+1) datum is 𝐔 = e^{iηA′}U with η := η_{k+1}, A′ 𝔤^c-valued (CRE (iii), p.261), and U = U_{k+1}. Units are fine bonds; a step-(k+1) unit is L^{k+1} fine bonds. On X_W ⊂ Ω_{k+1}, the top layer of D(k+1)(iii), (2.39) gives:
- |ηA′(b)| ≤ a, with a := α_{1,k+1}L^{−(k+1)};
- a covariant change of ηA′ per fine step of at most aL^{−(k+1)};
- |𝐉| < r_J^{(k+1)} (CRE (2.36), which bounds |𝐉|), with |J| < r_J^{(k+1)} as well, since the factors are evaluated at 𝐉 = J; hence |𝐉 − J| < 2r_J^{(k+1)}.

A π_j-cube has side ML^{−m} step-(k+1) units (l.1551 at m = 1). X_W is connected and made of #_j(W) ≤ σ_j(W) such cubes, so any two of its sites are joined in X_W by a lattice path of length at most δ_W step-(k+1) units, where

  δ_W := 4ML^{−m}σ_j(W).

Also |I_W| ≤ ML^{−m}σ_j(W) (l.1551).

CRE (2.6)–(2.7), p.255, give α_{i,k+1}/α_{i,j} ≤ (1+β₀)²m^{1/2}, since g_n ≤ (1+β₀)(n−m)^{1/2}g_m and (log g_n^{−2})^p ≤ (1+β₀)(log g_m^{−2})^p for n > m. X_W lies in Ω_{k+1} now and lay in the top layer Ω_j of its production step (l.15); the inclusion Ω_{k+1} ⊂ Ω_j is not used, since an R-step between enlarges the regions (Ω′_j = Ω_j ∪ Z, LFR II (1.33)). On X_W the production radii are therefore ϱ_j ≥ (1−β)α_{1,j}L^{−j} ≥ (1−β)L^m a/((1+β₀)²m^{1/2}), and r_J^{(j)} ≥ (1−β)L^{3m}r_J^{(k+1)}/((1+β₀)²m^{1/2}).

## 1. Lemma 1 (Complexified Covariance)

Let F be analytic on an open set 𝒟 of (𝐔, 𝐉, σ) on X_W. Suppose F satisfies the law F(q^v) = π(v(x_W))F(q)π(v(x′_W))^{−1}, q^v := (𝐔^v, R(v)𝐉, R(v)σ), for G-valued v at the real points q of 𝒟 with q^v ∈ 𝒟. Let p ∈ 𝒟 be joined to a real point of 𝒟 by a path in 𝒟. Let u_t, t ∈ [0, 1], be a path in (G^c)^{sites(X_W)} with u₀ = 1 and p^{u_t} ∈ 𝒟 for all t. Then F(p^{u₁}) = π(u₁(x_W))F(p)π(u₁(x′_W))^{−1}.

*Proof.* G is compact and connected, so G^c = G·exp(i𝔤) and T_gG^c = T_gG ⊕ iT_gG. The real points are therefore a totally real submanifold of maximal dimension, in the configuration and slot variables and in (G^c)^{sites}, and an open piece of one is a uniqueness set for analytic functions. π extends holomorphically to G^c.
- (i) Real v near 1, at p. Let γ be the path from a real point p₀ to p. By compactness of γ there is a neighbourhood N of 1 in G^{sites} with γ(s)^v ∈ 𝒟 for all s and all v ∈ N. For v ∈ N, Φ_v(q) := π(v(x_W))^{−1}F(q^v)π(v(x′_W)) − F(q) is analytic on the open set {q ∈ 𝒟 : q^v ∈ 𝒟} ⊃ γ, and it vanishes at the real points near p₀. So it vanishes on the component containing γ, and in particular at p.
- (ii) Complex u. Ψ(u) := π(u(x_W))^{−1}F(p^u)π(u(x′_W)) − F(p) is analytic on the open set {u : p^u ∈ 𝒟}, and it vanishes on N by (i). The path u_t lies in the component containing N, so Ψ(u₁) = 0. ∎

The lemma uses only Cov at real points and analyticity. For closed words it is (6)(b7)'s *G^c-valued u* (l.869). For every insertion with Cov(j) and D(j)(iii) it holds on the production domain, the new groups of step k+1 included. So the step needs to deliver no covariant clause beyond Cov(k+1) and D(k+1)(iii). This is the second half of l.168's crux.

**The base-point form.** Put Ŷ_W := Y_Wπ(𝐔(I_W))^{−1}. Since 𝐔^v(I_W) = v(x_W)𝐔(I_W)v(x′_W)^{−1}, Ŷ_W obeys the law with x′_W replaced by x_W. Lemma 1 then gives, for u(x_W) = 1:

  Ŷ_W(𝐔^u, R(u)𝐉, R(u)σ) = Ŷ_W(𝐔, 𝐉, σ).

## 2. Lemma 2 (Gauge Reduction of the Complex Part)

Let δ_W ≤ δ̄ := min(1/2, CM/(2L)). Then there is ω: sites(X_W) → 𝔤^c with ω(x_W) = 0 and |ω| ≤ 4α_{1,k+1}δ_W. With u_t := exp(itω) it gives 𝐔^{u_t} = e^{iηA″_t}U, with the same real base U, where on X_W:
- |ηA″₁| ≤ K₁aδ_W;
- |ηA″_t| ≤ 3a for t ∈ [0, 1];
- the covariant change of ηA″_t per fine step is ≤ K₂aL^{−(k+1)}.

Here K₁ := 4(1+2b̂) + c(α_{1,k+1} + b̂) and K₂ := 1 + c(Lb̂ + α_{1,k+1}), with b̂ := LBCM·max(α_{0,k}, α_{0,k+1}). So K₁ ≤ 5 and K₂ ≤ 2 for g_K small, with L and M fixed before g.

*(a) The smooth gauge.* Let B be the smallest ℓ∞-cube containing X_W; its side is ≤ δ̄ ≤ CM/(2L).
- If B meets Ω_{k+1}ᶜ: the cube of side CM/L containing B and meeting Ω_{k+1}ᶜ lies in Ω_{k+1}^∼ ⊂ Ω_k (K2). It is a layer-k cube of (2.38) (K1).
- If B ⊂ Ω_{k+1}: the partition cubes meeting B form a box of at most 2⁴ cubes, all in Ω_{k+1}, of side ≥ CM in each direction (K2). The box contains a top-layer cube of side CM that contains B.

In either case (2.38) gives a G-valued v on the cube with U^v = exp iξA, with |ξA| ≤ b̂L^{−(k+1)} per fine bond and a change ≤ Lb̂L^{−2(k+1)} per fine step (the layer-k bounds, the larger ones). By Cov at real v (a real orthogonal R(v) keeps the norms and the slot polydisc, (b7)) the computation below is made in this gauge.

*(b) The construction.* For each direction μ, let a_μ := ηA′(b_μ) at a fixed bond b_μ of X_W in direction μ (a_μ := 0 if there is none). Put ω(x) := Σ_μa_μ(x − x_W)_μ. Then |ω| ≤ a·4δ_WL^{k+1} = 4α_{1,k+1}δ_W.

For b = (x, x+e_μ) ⊂ X_W, with X := ω(x), Y := ηA′(b), Z := ξA(b) and ω(x+e_μ) = X + a_μ:

  e^{iηA″₁(b)} = e^{iX}e^{iY}e^{iZ}e^{−iX−ia_μ}e^{−iZ}.

The first-order exponent is i(Y − a_μ). |Y − a_μ| is at most the length δ_WL^{k+1} of a path in X_W from b_μ to b times the ordinary change per fine step, which is ≤ aL^{−(k+1)} + 2|ξA|a ≤ aL^{−(k+1)}(1 + 2b̂). So |Y − a_μ| ≤ 4δ_Wa(1 + 2b̂), the 4 counting the parallel transfers of the bond between directions.

The second-order exponent is −½([X, 2Y − a_μ] + 2[X, Z] − [Y, a_μ] − 2[Z, a_μ]). Its size is at most c(|ω|a + |ω||ξA| + a² + a|ξA|), and each of the four terms is ≤ aδ_W times α_{1,k+1}, b̂, α_{1,k+1}, and b̂ respectively. For the last two this uses δ_W ≥ 4ML^{−m}, so a/δ_W ≤ α_{1,k+1}L^{−j}/(4M) and |ξA|/δ_W ≤ b̂L^{−j}/(4M). Higher orders are smaller, since |X|, |Y|, |Z| ≪ 1. This gives the first bound.

At t ∈ [0, 1] the first-order exponent is i(Y − ta_μ), of size ≤ 2a, plus the same corrections. The per-step changes are:
- of Y: ≤ aL^{−(k+1)}(1 + 2b̂);
- of a_μ: 0;
- of the commutators: ≤ |ΔX|(|Y| + |Z|) + |X|(|ΔY| + |ΔZ|), with |ΔX| ≤ a, which is ≤ aL^{−(k+1)}(α_{1,k+1} + b̂ + 4δ_W(α_{1,k+1} + Lb̂)).

This gives K₂. ∎

## 3. Lemma 3 (The Carried Complex-Data Excess)

Let μ := min(1, MC₀/(2C_avC₁)), the disc factor of (b), and let δ_W ≤ δ̄_m := min(δ̄, μ4^{−m}). This is the regime of Lemma 2, narrowed in (c). Take u = u₁. With R_A := μϱ_j/(2K₁aδ_W), R_J := r_J^{(j)}/(6r_J^{(k+1)}) and R := min(R_A, R_J) ≥ 2:

  ‖Y_W(𝐔, 𝐉, σ)‖ ≤ 2·(4/R)S_We^{νσ_j(W)/8192} + ‖Ŷ_W(U, J, σ″)‖·(1 + 2c_πα_{1,k+1}|I_W|),

where the slot σ″ is σ displaced as in (c), and

  4/R ≤ (1+β₀)²m^{1/2}(1−β)^{−1}L^{−m}(8K₁δ_W/μ + 24L^{−2m}).

The second term is the real-point part at a real configuration. Its transport factor comes from |I_W| ≤ δ_W/4 ≤ 1/8, and it carries with (12)(b)'s real-point factor. The first term is the complex-data excess; its factor 2 bounds the transport e^{c_πα_{1,k+1}|I_W|}, and e^{νσ_j(W)/8192} bounds the inverse transport at the disc points ((b)), paid in §4.

*(a) Covariance.* Y_W(𝐔, 𝐉, σ) = Ŷ_W(𝐔^u, R(u)𝐉, R(u)σ)π(𝐔(I_W)) by §1, since u(x_W) = 1. The hypotheses of Lemma 1 hold on 𝒟_W:
- the current point is joined to the real point (U, J, Re σ̂) by the straight path, of sup ≤ a;
- the path points 𝐔^{u_t} = e^{iηA″_t}U have sup ≤ 3a ≤ ϱ_j/2 and gradient ≤ K₂aL^{−(k+1)} ≤ half the step-j allowance (1−β)α_{1,j}L^{−2j}, for L^m ≥ 6(1+β₀)²m^{1/2}/(1−β), which holds for every m ≥ 1 once L ≥ L₀;
- the real base U = U_{k+1} = U_j(V_j^*) is a step-j base point by l.1353 (2), one of (T-dev)'s inputs;
- |R(u_t)𝐉 − J| ≤ |𝐉 − J| + 2c_Ge^{2c_G|ω|}|ω||𝐉| ≤ 3r_J^{(k+1)}, by |𝐉 − J| < 2r_J^{(k+1)} (§0) and |ω| = O(α_{1,k+1}δ_W);
- the slot points are as in (c);
- (2.34) for 𝐔^{u_t} is as in (b), and (2.35), (2.37) are (K3).

*(b) The disc.* Put f(z) := Ŷ_W(e^{izηA″₁}U, J + z(R(u)𝐉 − J), ·) for |z| ≤ R, at the hat slot κ^{−1}σ̂ of (c) held fixed along the disc; then f(1) is the transformed point and f(0) the real one, at real (U, J) with actual slot R(c₀(U))κ^{−1}σ̂, which is in the slot polydisc because R(c₀(U)) is real orthogonal. On the disc:
- the sup is ≤ RK₁aδ_W ≤ μϱ_j/2 ≤ ϱ_j/2;
- the 𝐉-deviation is ≤ r_J^{(j)}/2;
- the per-step change is ≤ RK₂aL^{−(k+1)} ≤ μϱ_jK₂L^{−(k+1)}/(2K₁δ_W) ≤ μϱ_jL^{−j}K₂/(8K₁M) ≤ μ(1−β)α_{1,j}L^{−2j}/2, using δ_W ≥ 4ML^{−m}.

(2.34) for the disc points: per plaquette |∂𝐔 − 1| ≤ |∂U − 1| + 2(per-step change) + |ηA″|² ≤ α_{0,k+1}L^{−2(k+1)} + μα_{1,j}L^{−2j}/(2M) + α_{1,j}²L^{−2j}. The middle term is ≤ α_{0,j}L^{−2j}/(4C_av) ≤ α_{0,j}L^{−2j}/8 by the choice of μ (R-m's α₁/α₀ = (C₁/C₀)(log g^{−2})^{q₁−q₀}, with q₀ = q₁, SW closure §2; the same bound gives (2.35) and (2.37) through (K3)), so the sum is ≤ (1−β)α_{0,j}L^{−2j} for g_K small and L ≥ L₀. The disc points are thus in 𝒟_W, with (2.35) and (2.37) by (K3). Since Ŷ_W = Y_Wπ(𝐔(I_W))^{−1}, sup_{disc}‖f‖ ≤ S_W·sup_{disc}‖π(𝐔_z(I_W))^{−1}‖. The phase per fine bond at a disc point is ≤ ϱ_j/2 ≤ α_{1,j}L^{−j}/2, and I_W has ≤ ML^jσ_j(W) fine bonds (§0), so the inverse transport is ≤ e^{(c_π/2)α_{1,j}Mσ_j(W)} ≤ e^{νσ_j(W)/8192} by c_πα_{1,j}·4096M ≤ ν (map l.1614, imposed at every step). Cauchy's estimate gives ‖f(1) − f(0)‖ ≤ (2S_W/(R−1))e^{νσ_j(W)/8192} ≤ (4S_W/R)e^{νσ_j(W)/8192}.

*(c) The slots.* In the production frame, Cov reads Ŷ(𝐔^u, R(u)𝐉, ·) at the hat-slot κ^{−1}σ̂, with κ := R(c₀(𝐔))^{−1}R(u)^{−1}R(c₀(𝐔^u)) and c₀ := c₀^{(j)}. c₀ is analytic on 𝒟_W with |log c₀| = O(α_{1,j}) (map (d′) Step 8's size bound, l.196). c₀^{(j)} reads 𝐔 on step-j blocks, which may protrude from X_W by up to L^{−m} step-(k+1) units; there 𝐔^u is defined with the linear extension of ω, at a cost O(L^{−m}) in the bounds below. Along the path, Cauchy's estimate in the A″-direction gives |log c₀(𝐔^u) − log c₀(𝐔)| ≤ cα_{1,j}·3a/ϱ_j ≤ c′α_{1,k+1}L^{−m}m^{1/2}. Hence:

  |κ − 1| ≤ c(α_{1,k+1}δ_W + α_{1,k+1}L^{−m}m^{1/2}).

The displacement |κ − 1|(|σ̂_{j,0}| + r_{ω,j}) is ≤ r_{ω,j}2^{−(m+1)}, half of the step's margin of l.961 (K4), once the inequality below holds. Since carried dev insertions do not depend on σ (§0), this displacement changes no value of Y_W, and (c) is recorded only for the slot-dependent species; it spends no margin, and l.164's half stands. The inequality:

  c(δ_W + L^{−m}m^{1/2})α_{1,k+1}(|σ_{j,0}|/r_{ω,j} + 1) ≤ 2^{−(m+1)}.

The right side decays in m, so δ_W ≤ δ̄ is not enough for old insertions. At δ_W near δ̄ the left side is of order α_{1,k+1}|σ_{j,0}|/r_{ω,j}, which does not decay in m. Hence the regime δ_W ≤ δ̄_m.
- The computation of l.963 bounds h_k through α_{1,k}, and α_{1,k+1} ≤ (1+β₀)²α_{1,k} (CRE (2.6)–(2.7) for g and the logarithm), the extra factor absorbed in C. It therefore gives α_{1,k+1}(|σ_{j,0}|/r_{ω,j} + 1) ≤ Λ_m, with Λ_m := Cg_{k+1}^{1/2}(log g_{k+1}^{−2})^{q₁+p₀}(1 + β′m)^{1/4}(1 + log(1 + β′m))^{p₀}.
- For L ≥ 8, L^{−m}m^{1/2} ≤ 4^{−m}, so the left side is ≤ 2cΛ_m4^{−m}.
- 4cΛ_m2^{−m} ≤ 1 for every m once g_K is small, since sup_m(1 + β′m)^{1/4}(1 + log(1 + β′m))^{p₀}2^{−m} is a constant.

σ″ is the slot of this displaced hat value. ∎

**The non-covariant bound.** Cauchy's estimate directly in A′ and 𝐉 on the production domain gives the excess ≤ 4c_nc(1+β₀)²m^{1/2}(1−β)^{−1}L^{−m}S_W for every W, with no restriction on δ_W. The disc is R′ := min(ϱ_j/(2a), (C₀/(C_avC₁))L^{2m}/(8K₂(1+β₀)²m^{1/2}), (r_J^{(j)} − r_J^{(k+1)})₊/(4r_J^{(k+1)})), with the hat slot held fixed as in (b). The Cauchy disc is |z| ≤ 2R′, and, Y_W being read directly (the transport inside S_W, so sup_{disc}‖f‖ ≤ S_W), Cauchy's estimate as in (b) gives ‖f(1) − f(0)‖ ≤ 2S_W/(2R′ − 1) ≤ 2S_W/R′ ≤ (4/R′)S_W for R′ ≥ 1; the factor 2 in 2R′ below is this radius. The third entry gives |J + z(𝐉 − J)| ≤ r_J^{(k+1)} + 2R′·2r_J^{(k+1)} ≤ r_J^{(j)} at the disc points |z| ≤ 2R′ (|J|, |𝐉| < r_J^{(k+1)}, r_J being (2.36)'s absolute radius), and where it is small the m falls in the trivial branch below, which needs no disc. The sup at the disc points is ≤ 2R′a ≤ ϱ_j by the first entry, and the per-step change of zηA′ is ≤ 2R′aL^{−(k+1)} ≤ ϱ_jL^{−(k+1)} ≤ α_{1,j}L^{−2j}L^{−m}, within (2.39)'s step-j allowance (1−β)α_{1,j}L^{−2j} for L^m ≥ (1−β)^{−1}; for (2.34) the per-step change is bounded by 2R′K₂α_{1,k+1}L^{−2(k+1)} (K₂ ≥ 1, l.28), with no 1/M gain since there is no δ_W, and α_{1,k+1} ≤ (1+β₀)²m^{1/2}(C₁/C₀)α_{0,j} (CRE (2.6)–(2.7) with (2.28) and q₀ = q₁, as at l.37); the middle entry makes C_av times it ≤ α_{0,j}L^{−2j}/4, so the per-plaquette change, twice the per-step change (l.110), has C_av times it ≤ α_{0,j}L^{−2j}/2; with C_av(T₁ + T₃) ≤ α_{0,j}L^{−2j}/4 as in (b), the C_av-weighted total is ≤ (3/4)α_{0,j}L^{−2j}, within R-av's hypothesis (l.13) and the top-layer conditions (factor 1 at n = j), so (2.34) (with B₃ ≥ 1, which enlarging VAR's B₃ allows, so that C_av ≥ 2B₃ ≥ 3/4) and, through (K3), (2.35) and (2.37) hold, with T₁, T₃ unchanged since R′ ≤ ϱ_j/(2a). For the m with R′ ≥ 2, Cauchy's estimate gives the excess ≤ (4/R′)S_W ≤ 8(1+β₀)²m^{1/2}(1−β)^{−1}L^{−m}max(1, 4K₂C_avC₁/(C₀L))S_W (first entry: 8a/ϱ_j ≤ 8(1+β₀)²m^{1/2}(1−β)^{−1}L^{−m}; middle entry: 32K₂(1+β₀)²m^{1/2}C_avC₁/(C₀L^{2m}) ≤ 8(1+β₀)²m^{1/2}L^{−m}·4K₂C_avC₁/(C₀L), m ≥ 1; third entry, where it is the minimum and ≥ 2 (so ρ := r_J^{(j)}/r_J^{(k+1)} ≥ 9): 16/(ρ − 1) ≤ 18/ρ ≤ 18(1+β₀)²m^{1/2}(1−β)^{−1}L^{−3m} ≤ 8(1+β₀)²m^{1/2}(1−β)^{−1}L^{−m} for L ≥ 2, by l.37). The entries of R′ are not functions of m alone (ϱ_j, a and r_J depend on g_j and g_{k+1}, K₂ on k), but by l.37 and K₂ ≤ 2 (l.60) they are bounded below by functions of m only: ϱ_j/(2a) ≥ (1−β)L^m/(2(1+β₀)²m^{1/2}), the middle entry ≥ (C₀/(C_avC₁))L^{2m}/(16(1+β₀)²m^{1/2}), and the third ≥ ((1−β)L^{3m}/((1+β₀)²m^{1/2}) − 1)₊/4. Each grows with m for L ≥ 2 (L^m/m^{1/2} increases, since L(m/(m+1))^{1/2} ≥ √2). Let m₀ be the least integer m₀ ≥ 1 such that all three lower bounds are ≥ 2 for every m ≥ m₀; it depends on L, C_avC₁/C₀, β₀ and β only, and R′ ≥ 2 for m ≥ m₀. With K₂ ≤ 2 the excess bound above is ≤ 8(1+β₀)²m^{1/2}(1−β)^{−1}L^{−m}max(1, 8C_avC₁/(C₀L))S_W. For the finitely many m < m₀ the trivial bound excess ≤ ‖Y_W(𝐔)‖ + ‖Y_W(U)‖ ≤ 2S_W holds: at step-(k+1) data a carried insertion is its production function evaluated at the composite point reached through the evaluation maps of the steps k, …, j, and that point lies in 𝒟_W (D(j)(iii)'s domain on X_W; Ũ^c_j for j ≥ 2, V3's sup-only domain at j = 1, map l.975) by D2.2(4)(f)'s chain condition (map l.690–709, with l.928 for (2.35)) applied at each step i = k, k−1, …, j, the step-i point having its base in D(i+1)(iii)'s domain by the previous application. For an insertion left untouched since step j the composite point is (𝐔, 𝐉) itself ((4)(e) at s = 0, with 𝐉 carried as in (4)(f) *Carrying 𝐉*, map l.710–714), so both branches bound the same excess ‖Y_W(𝐔, 𝐉) − Y_W(U, J)‖. This uses neither (K3) nor R-av, so it holds for every m < m₀ whatever the size of R′'s middle entry; it rests on (4)(f) with reading R-m, and, for (2.35) and (2.37), on l.928's joint derivation with R-mJ given l.928's inputs (R-p, q₀ = q₁ > p₀, R-dec, R-cpl₀, R-adm; not reviewed; map l.928, l.214), premises already among (S)'s global conditions (map l.1614). Hence c_nc := max(2max(1, 8C_avC₁/(C₀L)), max_{m<m₀}(1−β)L^m/(2(1+β₀)²m^{1/2})), finite and independent of k. The transport is inside S_W. This is the a*-, j*-carry that l.168 records. Lemma 3 multiplies it by 4K₁δ_W/μ + 12L^{−2m}.

## 4. The Carry, Uniformly in k

Fix a step-(k+1) traversal n′. The generation-j insertions meeting n′ meet one of its L^m step-j traversals ((12)(b) *It carries*, iterated). Let P_j be the production (ii-w) sum per step-j traversal, with the weight e^{θ + ν_rσ + ν_e·ext}, so P_j ≤ N^{(j)}ρ_jpl_j. Here N^{(j)} is the constant of the new groups of step j: N^{(j)} ≤ 2C_winC_M + s_{j−1}C^{(j−1)}, where s_{j−1} := (1+β₀)⁷[(β) term + quadratic term] is that part of (12)(f)'s θ_{j−1} (l.1581), and N^{(1)} := C^{(1)}.

The complex-data part of the carried insertions is stated with the reserve weight (15/16 − 1/8192)ν_rσ in place of ν_rσ: ν_r/16 for the gain below and ν/8192 = ν_r/8192 (ν_r = ν, map l.292, l.1531) for Lemma 3's inverse transport. The free eighth of the reserve budget (l.1555: 7/8 used) pays this, and the consumers' 7/8 still fit. Then σe^{−(ν_r/16)σ} ≤ 16/(eν_r) bounds the weighted sum of δ_W ≤ 4ML^{−m}σ_j(W) by (64M/(eν_r))L^{−m} times the unweighted one.

For δ_W > δ̄_m, use the non-covariant bound: there σ_j(W) > δ̄_mL^m/(4M), so e^{−(ν_r/16)σ} ≤ e^{−ν_rδ̄_mL^m/(64M)}. Summing over the generation-j insertions at n′:

  E_j ≤ (1+β₀)²m^{1/2}(1−β)^{−1}[1024K₁(M/(eν_rμ))L^{−m} + 48L^{−2m} + 4c_nce^{−ν_rδ̄_mL^m/(64M)}]·P_j.

For the young generations, with 4ML^{−m} ≳ 1, the bracket is ≤ 4c_nc + 1024K₁M/(eν_rμ). They get no gain from §3, but there are only about log_L M of them. With ρ_j ≤ (1+β₀)^{6m}ρ_{k+1} and pl_j ≤ (1+β₀)^m pl_{k+1} ((6); CRE (2.7)):

  Σ_{j≤k}E_j ≤ Ĉ·max_{j≤k}N^{(j)}·ρ_{k+1}pl_{k+1},

  Ĉ := (1−β)^{−1}Σ_{m≥1}(1+β₀)^{9m}m^{1/2}[1024K₁(M/(eν_rμ))L^{−m} + 48L^{−2m} + 4c_nce^{−ν_rδ̄_mL^m/(64M)}].

Ĉ is finite for L > (1+β₀)⁹. The last series converges for L > 4 and any M and ν_r, since δ̄_mL^m = μ(L/4)^m for large m. With K₁ ≤ 5 (Lemma 3's factor, l.60) it depends on L, M, ν_r, β₀, β, (2.38)'s cube constant C (through δ̄ = min(1/2, CM/(2L)), l.55; fixed, not absolute, map l.975), and (through c_nc, m₀, and μ, §3) C_avC₁/C₀ = C_avλ_R only, not on k or g. The sum over generations is thus bounded uniformly in k. The young generations contribute a bounded number of terms, and the older ones decay like L^{−m}. M/L need not be small.

**The recursion of (12)(f).** The complex-data part no longer passes through C^{(k)}: it is bounded from the production constants directly. So:

  C^{(k+1)} ≤ (1+Ĉ)·max_{j≤k+1}N^{(j)} + L^{−1}(1+β₀)^{15}C^{(k)}.

Let s̄ := sup_j s_j, which → 0 for g_K small ((R-m′); C^{(k)}ρ_k → 0 once C^{(k)} is bounded). Let L^{−1}(1+β₀)^{15} ≤ 1/8 (l.1582). The induction then closes with

  C^{(k)} ≤ C_S′ := max(2(1+Ĉ)C^{(1)}, 8(1+Ĉ)C_winC_M) for all k ≤ K,

once (1+Ĉ)s̄ ≤ 1/4 for g_K small. The term j = 1 of the max is (1+Ĉ)N^{(1)} = (1+Ĉ)C^{(1)} ≤ C_S′/2. For j ≥ 2, N^{(j)} ≤ 2C_winC_M + s̄C_S′ by the induction hypothesis, and:
- (1+Ĉ)2C_winC_M ≤ C_S′/4;
- (1+Ĉ)s̄C_S′ ≤ C_S′/4;
- L^{−1}(1+β₀)^{15}C_S′ ≤ C_S′/8.

In either case the total is at most 5C_S′/8 ≤ C_S′. (S-w), the KP condition for the reference gas, (Z)'s C̄_Z, and (T′) follow as in (12)(f)–(g) and (13), with this C_S′. The KP smallness C_S′ρ_{k+1}pl ≤ ν/(64·81M) holds for g_K small, as before.

## 5. The Region of SW §6(6c)

SW §6(6c) ran the Cauchy step of (6b) for a carried W at U_{k+1} on 𝒬^{(j)}_n(W)^{∼5}, with the gauge of (LPG′) for U_{k+1} on that region. In step-(k+1) units this region is in general smaller than a π_{k+1}-cube, so (LPG′) at step k+1 does not apply to it. The bound of §3 and §4 does not use that step.

- *The real-point part.* At the real base, π(U(I_W)) is unitary, so ‖Ŷ_W(U_{k+1}, J_{k+1}, σ″)‖ = ‖Y_W(U_{k+1}, J_{k+1}, σ″)‖. Since Y_W does not depend on σ (§0), this is bounded by (T-dev), l.1352, verbatim, which has no slot argument. (T-dev) is derived at the background of step j:
  - l.1353 (1) runs (4)'s Cauchy step with (LPG′) at step j for U_j(V_j^*);
  - the region is in step-j units (SW §5(e)'s per-traversal region at step j, a union of π_j-cubes), which is (LPG′)'s own cube class at step j;
  - l.1353 (2) gives U_j(V_j^*) = U_{k+1}.

  No (LPG′) at step k+1 enters.
- *The excess.* For δ_W ≤ δ̄_m it uses three things: the real smooth gauge of (2.38) on a cube of side CM or CM/L ((K1), (K2)); Lemma 1 on the production domain 𝒟_W; and Cauchy's estimate there. For δ_W > δ̄_m it uses Cauchy's estimate alone. None of these needs a gauge on 𝒬^{(j)}.

Hence the carried insertions satisfy, on 𝒟_{k+1}^{sub} and per insertion,

  e^{θ(W)}‖Y_W(𝐔, 𝐉, σ)‖ ≤ (1 + 2c_πα_{1,k+1}|I_W|)·b_WDev_W(U_{k+1}) + e^{θ(W)}ε_W,

where ε_W is the excess of Lemma 3 or of the non-covariant bound. By §4, Σ_{j≤k}Σ_{W of generation j meeting n′}e^{θ(W)}ε_W ≤ Ĉ·max_{j≤k}N^{(j)}·ρ_{k+1}pl_{k+1}.
- The first term is the per-insertion form, with Dev_W in step-j normalisation (l.1346) over the per-traversal region of SW §4.
- The second term is in the sup form in which SW §6(6b) states the new groups' clause, and which is all the consumers use.

This is D(k+1)(iii)-dev for the carried insertions. The π_{k+1}-hull of 𝒬^{(j)} is not needed. The clause is derived given (T-dev)'s own inputs (l.1353: D2.6's carrier item, R-J, R-ζ, and the step-1 base); SW §6(6d)'s (2.38) for U_{k+1}, under q₀ > p₀, which the new groups' clause also uses; D2.2(4)(f)'s chain condition with R-m, and map l.928's (2.35) and (2.37), derived jointly with R-mJ given l.928's inputs (R-p, q₀ = q₁ > p₀, R-dec, R-cpl₀, R-adm; not reviewed) (§3's trivial branch); and R-av of (K3) in its top-layer uniform form (C_av := 2(B₃ + 2c_dB₅) from RG1 p.263 (1.17) with VAR Theorem 1 and Proposition 9). The slot independence of the carried dev insertions is derived in §0.

**Constants added by this note.** L ≥ 8 and L > (1+β₀)⁹ (§3(c), §4); L ≥ L₀ for the disc margins (§3(a)–(b)); the disc factor μ := min(1, MC₀/(2C_avC₁)) in R_A and δ̄_m (§3, (K3)), in place of a condition on M, since C₁ = λ_RC₀ with λ_R = K_RLM + 1 (table #T2.24); c_nc and m₀ in the non-covariant bound (§3); the reserve weight (15/16 − 1/8192)ν_rσ for the complex-data part (§4), in σ_j(W), which dominates the consumers' weight in σ_k(W) (l.1555) since σ_k(W) ≤ σ_j(W) (coarser π-cubes and arc lengths in coarser bonds), with c_πα_{1,j}·4096M ≤ ν for every j ≥ 1 (map l.1614 states it at index k+1 at each step k ≥ 0) for the disc transport (§3(b)); g_K small. (8c_G in l.961, (K4), is not needed, §0.)

# Inputs of the Live Wilson-Loop Notes: Derived or Printed

Every input below is derived where stated, quoted from the print and checked, or a printed claim of Bałaban's accepted; nothing is open. The files covered: the map, the D2.6, D2.7, O6, SW, class-activities, and background closures, the covariance note (WILSON_IT1_COMPLEX_COVARIANCE_2026_10_29.md), the LF (WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md), the Cauchy note, and the IT-1 note (WILSON_IT1_LINE_DEFECT_2026_10_21.md). A two-loops #x is in the two-loops note or in one of its BP_TL files in balaban_proofs/ (LABELS_TWO_LOOPS.md gives the file); a BLL #x is in balaban_proofs/BP_LFR2_LOOP_LOCALISATION.md.

## Derived, Awaiting Review

| Item | Where | Derivation |
|---|---|---|
| σ on the enlarged current domain 𝒟^c of LF #4.289.1 | LF #4.291–#4.294-1 | the old terms read at G^c-gauge representatives in Ũ″^c_k(Y₁, α̃₀, α̃₁), by the room 8B₃ and Proposition 9 at the boundary-layer data (#4.293.3–#4.293.5-1); both parts of σ bounded by Schwarz's lemma on the disc abs(z) ≤ R^U (#4.294–#4.294-0.2) |
| The 𝐑-step chain's n = 0 space | two-loops #157; used by two-loops #17 and D2.7 item 5(b) through two-loops #7 | at n = 0, j = h < k₀ (LFR I p.179 l.10, l.27, p.181 l.40), so (i) has no L₀ powers and (ii) is empty (p.191 l.31–32), and (i) with (1.68) gives CRE (2.34)–(2.37), (2.39) with f_m on the layers m < k and 3 on Ω_k, so Ũ^{(0)c}(X) ⊂ 𝒟^3_k (#157-1–#157-3); the 3 on Ω_k is absorbed where the members are evaluated (#6.12.5, #6.14-0, #130.15.2 (4)) |
| The 𝐑-step chain's start and normalisation | two-loops #86, #88.1; used as the row above | (1.51)'s 𝐇_k″ step is the starting difference against the printed chain from U_k^0 (#86.1–#86.3, under q₀ > p₁ + θ_Lν_L, #86.3-2); the G^c normalisations by covariance and the identity theorem (#88.1-1–#88.1-4) |
| LFR II's localisation expansion applied to the loop's letters, home tensors, and carried insertions | D2.7 15.5(ii)(α)–(α-1), (γ), 15.9(a); BLL; used by two-loops #3.3 | the expansion (LFR II p.372 l.12–28, p.373 l.13–p.376 l.13) is made for any term (p.373 l.14–15); the covariance (γ) from PBG (3.28)–(3.34), RG2 p.3 l.27–33, and (1.3)–(1.4) |
| The expansion's (s, z)-points | BLL #BLL.15, #BLL.20-6–#BLL.23-1; used as the row above | every (s, z)-point is the zero point times a fine phase of at most (1/64)α_{1,k}L^{−k}, inside the room left at two-loops #7's points (#BLL.21–#BLL.23), so it is an evaluation point of the class, where the members are analytic and bounded (two-loops #6.12–#6.13, #6.13-2); rests on two-loops #7 |
| The layer decay of 𝐇 at the complex backgrounds 𝐕 ∈ 𝓜^c_{k+1} | two-loops #130.19 | the computation with VAR Proposition 9 (p.309); its premise is Bałaban's printed claim, accepted: U_{k+1}(□₀, M·(𝐔)) "has approximately the same regularity properties as 𝐔, hence all necessary theorems are valid for operations with this configuration" (RG I p.275 l.6–7) |
| The payment of Π_iE(Y_i): the bound of χ_k^c(Y_i^{∼−6}) as the factor exp(−p₀(g_k)) of Bałaban's small-domain branch at j = k ((1.79)'s Π′) | two-loops #819, #819.1–#819.1-2; D2.7 15.8(c) | on the support of χ_k^c(Y_i^{∼−6}) some plaquette p′ ⊂ Y_i has abs(V_k(∂p′) − 1) ≥ (O(1)B₃M²)^{−1}ε_k (CRE (2.17), p.257 l.39; VAR Theorem 1 as at LFR I p.193 l.20, l.28–29), the condition of Bałaban's Wilson-action factor for 1 − χ_{k,Λ} (LFR I p.193 l.30–31), which gives exp(−¼g_k^{−2}(O(1)B₃M²)^{−1}ε_k²) ≤ exp(−A₁²p₀²(g_k)) ≤ exp(−p₀(g_k)) (LFR II p.381 l.29–31), one factor per component |
| RMJ: the averaged current at the evaluation points of (4)(f) | WILSON_IT1_RMJ_CLOSURE_2026_10_30.md; map #MOMGD.50, #MD2.2.6.142 | derived in that note |
| The replacement of U_{k,Z} by U_k | two-loops #160; used by two-loops #17 and D2.7 item 5(b) through two-loops #7 | abs(δ^{re}) ≤ O(1)(dKM₀ + 1)ε_k per block of 𝐁_k″(Y₁) (balaban_proofs/BP_LFR2_REPLACEMENT.md #160.1–#160.8); LFR II p.365 l.35–36 prints only "some new small terms" |

## Derived and Reviewed, or Printed

| Input | How |
|---|---|
| The deep-layer bound, two-loops #3.2 | derived and reviewed |
| LF pairing term e_a, Landau defect ν_a, and RG I's data at a real base (LF #A.11.1.4.4.4–#A.11.1.4.4.4.2, #A.11.1.4.3.4) | derived and reviewed; N(a) from VAR (190) and p.307 l.17–18, Bałaban's, accepted |
| The cross insertions' weights at the 𝐑-steps' evaluation points, two-loops #220 | derived and reviewed, given two-loops #7 where it uses #7's points, and given #86 and #88.1 (awaiting review, above) |
| p.375's inclusion, two-loops #17 | printed: LFR II p.375 l.29–31, "the space Ũ_k″^c(Y₁, α̃₀, α̃₁) is contained in the analyticity domain of the term 𝐄(X) we consider", with its reason for the old terms at l.32–34 |
| CRE p.277's support bound (D2.6 closure 2.3) | Bałaban's, accepted |
| CRE p.277's K′ bound (O6 §5a(i)) | Bałaban's, quoted and checked |
| CRE p.277's margin for the 𝐄_k- and 𝐑_k″-brackets (O6 §5) | printed: RG1 p.272 l.30–44, carried to the {Ω_j}-scales by CRE p.276 l.12–13; its inequality 8B₀e^{16κ_s}O(1)ε_k < min(β,1)α_{1,k}/2 (map #MOMGD.49) holds for g small under q₁ > p₀ (map #MD2.2.4.78) |
| CRE p.277's 𝐇-decay (map #MOMGD.55, #MD2.2.6.143-1) | Bałaban's, accepted |
| The real base U_{k+1}'s regularity on the older layers | the curvature and gradient conditions (2.34), (2.38) derived through the response chain U_m = (e^{iη𝐇_m(A′_m)}U_{m+1})^{g_m} (CRE (3.10)–(3.11), (3.14); VAR Prop. 9) with CRE p.277's 𝐇-decay, rooted at k = 1 on the layer n = 1 (VAR Theorem 1) and at p.268's top-layer bound on the layers n ≥ 2 (map #MD2.2.6.190); CRE p.276 l.10–12 ("the same as for U_n-configurations") and p.277 l.3–8 are Bałaban's printed statements, accepted, and not used for these conditions |
| RG2 p.6's B′-range | Bałaban's, accepted with CRE p.277's 𝐇-decay: the decay's B′-range is that of its sources, RG2's abs(B′) < ε₃ (p.6 l.16) and VAR (172), both absolute, so it contains abs(B′) ≤ ε_H; CRE p.276 l.18–22 runs RG2 Sect. 1 on the multi-domain walks (PBG Theorem 3.7, p.409, and (3.42)–(3.47)) |
| The gluing (D2.6 closure 8.1 *The gluing*) | derived |
| The row-domain bound (D2.6 closure 6.1 *The ω-polydisc*) | derived |
| (3.17) at 𝒬 and Theorem 1 at the local sup | derived, SW §5(2) and §5(5), from VAR Theorem 1 (p.279) and CRE (1.3), p.246, with CMP98 p.31's M^k (printed) |
| The gauge transformation in CRE (3.6) | printed: U_{k,□} = (exp iη𝐇_{k,□}(…)U_{k+1,□′})^{u_{k,□}^{−1}}, p.266 |
| The covariance C^{(k)} | printed: C^{(k)} = (C*Δ^{(k)}C)^{−1}, RG1 p.268 l.3; C^{(k)}(Z₀), RG2 p.13 |
| H_{1,1}'s walk expansion (map #MOMST.54-4) | printed: H₁ by PBG (3.127)–(3.129), p.421, and its walk expansion, tree-like with the estimates of (3.108), p.427 l.14–21 |
| No analyticity domain in A_k on CRE pp.270–278 (D2.6 closure 2.2 *Complex σ_k*) | checked against the print: A_k occurs only at p.270 l.5–33, p.271 l.22–41, p.272 l.4–18, p.276 l.38, none giving an analyticity domain in A_k |
| LF #A.11.1.4.4.1, the pairing | the chain takes RG I's own pairing, the averages (0.4) with Ax_k "as in Sect. G [15]" (REG (1.19) on single contours, VAR p.280 l.44–45). Bałaban's, accepted, in this pairing: the minimisers, their regularity, the class-cube gauges, and the analytic extension (RG I p.265 l.37–40; LFR II p.357 l.19, p.367 l.30, l.47–48), and Sect. G's Landau form in B = (1/i)log V′ with (19), (21), and (190) (RG I (3.3), p.270 l.32; RG II (1.2), p.2, and p.3 l.2–4; layered, CRE p.276 l.2–16 and l.18–20) |
| LF's first-order identity in this pairing | derived: a = H₁(U)Q(U)a + e_a + D_Uν_a (#A.11.1.4.4.4–#A.11.1.4.4.4.2), with e_a = 0 at U = 1 and e_a ≤ C(L, M′)ε₁θ_{B₁}, which δ_U covers (#A.11.1.4.1.1, #A.11.1.5.3-2); ξ_ω is bounded through the curvature (#A.11.1.4.3.3) |
| The source bound at real data (D2.6 closure 2.2) | Bałaban's practice on CRE pp.271–272, accepted |
| CRE p.261's boundary potentials (D2.6 closure 2.3) | clause (1) derived from RG1 (3.6)–(3.7) and RG2 pp.4–7; the localisation of 𝐁_k Bałaban's, CRE p.276 l.42–44, accepted |
| CRE p.277 l.19–23's boundary-polymer bound (D2.6 closure 2.4 *Vacuum gas*) | Bałaban's, CRE p.277 l.19–23, accepted, with (3.27) p.271 l.20–23, p.277 l.7–9, RG2 Lemma 3 (2.38) p.20, p.277 l.30 |
| CRE p.267's ζ resummation (map #MOMGD.29-5; D2.6 closure 8.2) | Bałaban's, accepted |
| The layer bound (D2.6 closure 8.3 *The layer bound*) | derived from REG Lemma 1 (p.79 l.39–50, (1.24)–(1.25)) in its local form (p.80 l.5–6), iterated by REG p.87 l.37–40 |
| "Regular" in CRE (2.12) (map #MD2.2.6.190-11) | quoted and checked: CRE p.256 l.49 refers (2.12) to [15] = VAR ("For precise definitions and the theory of this variational problem see [15]"), whose space (6) is its regular configurations (2) with fixed averages (p.277 abstract, p.278 (2), (6)); the minimal orbit is the same at every admissible radius by Theorem 1's uniqueness (p.279 l.15) |
| Positivity of the step map at real fields (background closure §1.6) | derived for the CRE-form steps k ≤ N from CRE (2.18)–(2.23), pp.257–258: each labelled term is a product of characteristic functions, of 𝐓_k, a composition of integrals (2.21) against δ-functions, the nonnegative ζ and χ, and the exponential of a real quadratic form, and of exp A_k; beyond N, D2.7's |
| Cauchy note B_J (table #T3.13) | its existence and uniformity in j Bałaban's printed claim, RG I p.280 l.21 ("The second is proved in the same way", the first with abs(∇^ξ𝐀₂) ≤ B₃abs(B′), p.280 l.3–4); its value is not printed and may depend on M through □₀ = □̃⁵ (p.273 l.40), so B₃⁺ := max(B₃, 2B_J) and c₂ ≤ c_* are fixed after M |
| The averaging bound (K3) | derived, covariance note (K3): from RG1 (1.17), p.263, with VAR Proposition 9 (p.309) and Theorem 1 (p.279); C_av := 2(B₃ + 2c_dB₅) |
| 𝐁_p(X)'s definition | printed, CRE p.256 l.57–63 (the determining set 𝐁_j(Ω)) |
| IT-1: Q̃ = Q_{U₁} and the δ-identity row by row | derived, IT-1 §3c(2)(a): Q̃ = Q_{U₁} by definition (RG1 (2.4), p.267 l.26; V4 (native-source-constraint-normalisation)), and the δ-identity row by row is RG1 p.268 l.1–2's elimination |
| IT-1: E₁ | a definition; p.264's bound kept, the constant being c₀ and L^{4d_G} per row, at most 2d·abs(Γ₁) rows (IT-1 §3c(2)(a)) |
| IT-1 off-Λ rows | placed in A₁ as 𝐁^{(1)}-terms, CRE (2.41)–(2.42) checked (domain, (i)–(iv), analytic on Ũ^c₁ with abs(f_c) ≤ log 2, and ≤ 2C + 1 at the rows crossing ∂Ω₁, whose fields off Ω₁ are real and in the domain of integration of (1.11), CRE p.248 l.37–38, p.249 l.31, p.261 l.68–71); B₀ enlarged by a constant of d, L, M, G; T₁ keeps the printed form (2.21) (IT-1 §3c(2)(a)) |
| IT-1: ζ in (1.29) | derived: (1.29) carries ζ once, so under (2.19) (Bałaban's, accepted) each factor carries ζ's part; components (common walls, RG1 p.257 l.8–10) are ∗-connected (IT-1 §3c(2)(b)) |
| IT-1: the two versions of (1.22) | derived: both act bond by bond with the same parameter 𝐇_{1,Ax}(b) (p.251, (1.21), p.253), so the product structure of (2.19) transfers (IT-1 §3c(2)(b)) |
| IT-1: the three identifications with (1.28) | the labels constraint and ζ's scope forced by the print; the J/I grouping of the good-cube tests derived by idempotence (IT-1 §3c(2)(d)) |
| IT-1 bond convention | printed, RG1 p.251 l.27: the bonds of a set are those meeting it, i.e. with an endpoint in it (IT-1 §3c(2) *Variables*) |
| IT-1: the readings named in V4's (H4) (sec:main-result) | IT-1 §3c(2)(d): the undisplayed constants quoted (VAR p.279 l.28, p.291 l.16, p.299 l.26, RG1 p.255 l.14); the representative Bałaban's (p.247 l.35); "in the domain of integration" quoted and checked (p.247 l.37–38); the minimal configuration printed (pp.256–257); the outer rows, the Ω₁ᶜ bonds, the χ₁ convention, v from (1.14) and "z ≠ y" forced by the print; D̃ = φ derived; δ₀ printed (p.247 l.50); the partitions a choice; σ, M₁ and B(P₁¹)ᶜ not needed; X^∼ the plain sense of "touching" (CRE p.245 l.41); "regular" as in CRE (2.12) above |
| IT-1 §3c(4″)'s check of CRE's k = 1 construction | derived and reviewed: the construction uses no property of Λ₁ beyond the listed ones (RC_PROOF_PASS Pass 6 (e); IT-1 §3c(4″)) |
| IT-1: the LFR II p.380 bad-cube factor at threshold ϑδ₀ | derived and reviewed, IT-1 §3f(2) (R1 with (D0)–(D2)), for §3c(4‴); its location and the rates of p.380 quoted and checked |
| CRE p.279's same-way clause (i′) (map #MD2.4.2.2) | Bałaban's, accepted: CRE pp.276, 277, 279 |
| Uniformity of the constants (D2.6 closure 4.2) | printed for a₁ (VAR p.279, p.304); derived for VAR Sect. G from the printed constant dependences |
| (190)'s decay | Bałaban's, accepted: (190) bounds the derivative of 𝓗, a function on (172) (VAR p.307 l.2), whose decay p.307 l.17–19 states |
| The combination of χ_k factors, two-loops #206 (cited by D2.7's #7 block) | derived: χ_k(Ω) of CRE (2.17) (p.257 l.39–42) is a product over the cubes of one partition of indicators, so χ² = χ gives χ_k(A)χ_k(B) = χ_k(A ∪ B) for unions A, B of these cubes |

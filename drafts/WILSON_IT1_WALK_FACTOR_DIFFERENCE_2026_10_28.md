# The Walk-Factor Difference (W-δ): The Two Runs' Walk Terms and Their Intertwined Comparison

{#WP.1} Own working note on the inequality (W-δ) of `WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md` (the LF note), §4(d), *The functions of the configurations.*, sub-bullet (iii).
{#WP.1-2} Bałaban is cited by printed page and line, checked on the transcriptions in `Balaban\tex\<paper>\parts`.
{#WP.1-3} RG II's references are RG I's list (RG II p.2 l.2–3): [13] is PBG (CMP 99, 389–434) and [15] is VAR (CMP 102, 277–309) (RG I p.299 l.13–15).
{#WP.1-4} PBG's [4] is PRT2 (CMP 96, 223–250) (PBG p.433 l.53).
{#WP.1-5} The LF note is cited by its tags (#4.60 and the like) and by section.
{#WP.1-6} The Cauchy note is cited by its tags (#C5.3-2 and the like), by section, and by display, and this note's own lines by their tags (#W6.4 and the like).
{#WP.1-7} Notation: a_j := εL^j is the spacing of the shared scale j in run A's units, run A's fine lattice is T_ε with k averaging steps, run B's is T_{ε/L} with k + 1, and the shared scale j is run A's scale j and run B's scale j + 1.

## 1. The Factors R_α(X) {#WS1}

{#W1.1} (a) *The propagators of RG II.* By "the results of Sect. G [15]", 𝐇_k(B′) = H₀B′ + 𝐀₀ − HD(H₀B′ + 𝐀₀) (RG II (1.2), p.2 l.25–30), with D(A′) = C(A′ − HD(A′)) (1.3) and 𝐀₀ + G̃(δV/δA′)(H₀B′ + 𝐀₀) = 0 (1.4), V of VAR (80) (p.2 l.41–43).
{#W1.1-1} These are VAR (179)–(180) (VAR p.306 l.28–41), with H the lift of VAR (45)–(46) (p.285 l.19–29): HB minimises ½⟨A, ΔA⟩ under L^jηQ_jA = B on Λ_j and RD*A = 0, so H maps data on 𝔅_k to fields on the fine lattice.
{#W1.1-2} H₀ is the lift of the condition (178) without gauge fixing (VAR p.306 l.16–30), also from data to fields, and G̃ maps sources on the fine lattice to fields there (VAR (180)).
{#W1.1-3} D takes values on 𝔅_k (VAR p.285 l.36).
{#W1.1-4} The propagators may be replaced by "arbitrary operators having the same regularity properties and satisfying the same bounds" (RG II p.3 l.2–4).

{#W1.2} (b) *The walk expansion of RG II.* "A propagator is represented by the sum (3.107) [13]", Σ_ωR₀(X₀)R_{α₁}(X₁)⋯R_{α_n}(X_n) (RG II (1.6), p.3 l.9–13), with simple localisation domains X_i of size M₁, built from cubes of π_k(1) (l.14–15).
{#W1.2-1} Each factor depends on the external field on X̃_j⁵, and its kernel vanishes in a neighbourhood of ∂X_j of width ⅓M₁ (l.16–17).
{#W1.2-2} The term of a walk is bounded, "as (3.108) [13]", by O(1)O(M₁^{−1/2})^{|ω|}M₁^{−½|ω|}exp(−δ₀d(ω, y, y′)) (1.7) (l.18–21), in "all operator norms in formulations of theorems in [13]" (l.23).
{#W1.2-3} The s-dependence multiplies the term of ω by s(Δ₁)⋯s(Δ_m), the cubes of σ₀ that meet its localisation domain (p.3 l.30–32).
{#W1.2-4} The bound (1.11) of H(s(Y₀))X on |s(Δ)| ≤ e^{κ₁} is B₀e^{16κ₁}|X| (p.5 l.6–16).

{#W1.3} (c) *The local propagators of PBG Sect. C.* For □ ∈ 𝒟_j PBG takes the sequence {Ω_n(□)}_{n=0,…,j+1}: Ω_{j+1}(□) = □̃³ ∩ B^{j+1}(Λ_{j+1}) when □̃³ meets the coarser layer, Ω_j(□) = □̃⁴, and Ω_n(□) a cube with the same centre and dist(Ω_n(□)^c, Ω_{n+1}(□)) = 2R₀M₀L^nη, so that Ω₀(□) ⊂ □̃⁵ (PBG p.408 l.29–35).
{#W1.3-1} This sequence satisfies PRT2 (2.1)–(2.2) after rescaling (p.408 l.34).
{#W1.3-2} Its layers are Λ_n = Ω_n^{(n)} ∖ Ω_{n+1}^{(n)}, with Λ₀ = Ω₀ ∖ Ω₁ at the scale 0 of T_η (p.393 l.18–20), where (3.16) puts the term a(η)^{d−2}|A(b)|² on the bonds of Λ₀ (p.393 l.21–24).
{#W1.3-3} Every operator is taken with Dirichlet boundary conditions on Ω₀^c and depends on U on Ω₀ only (p.394 l.29–36, p.395 l.10).
{#W1.3-4} The operators G′_□, C_□ = (Q′G′²_□Q′*)^{−1}, and G_□ of this sequence satisfy Theorems 3.1–3.3 through Corollary 3.6 (p.408 l.6–9), whose hypothesis (3.35) on a cube containing Ω₀(□) is derived in §7 for every cube (*The cubes next to the finer layer.*), in place of p.409 l.2's class statement; at the cubes whose □̃³ meets Ω_j^c the sequence is intersected with the global domains (same place).
{#W1.3-5} R₀M₀ is "a pair … of smallest possible numbers satisfying conditions needed in the proofs" of [4], with M = KR₀M₀ (p.408 l.26–28).

{#W1.4} (d) *The factors.* G′₀, C₀, and G₀ are the sums Σ_□h_□(·)_□h_□ over the partition 𝒟 with Σh_□² = 1 (PBG (3.87), p.408 l.22–23).
{#W1.4-1} The factors are built as follows.
- {#W1.5} G′: Δ′_aG′₀ = I − R′ with R′ = Σ_□K(h_□)G′_□h_□ (p.409 (3.88)), each term bounded by O(M^{−1})e^{−δ₀(L^jη)^{−1}|y−y′|}|λ| (3.89), and G′ = Σ_ωh_{□₀}G′_{□₀}h_{□₀}∏K(h_{□_i})G′_{□_i}h_{□_i} (3.90) (Theorem 3.7).
- {#W1.6} (Q′G′²Q′*)^{−1}: the series (3.96) with G′ replaced by its expansion for the locally modified partitions 𝒟′, so that the factors are products such as h′G′h′K(h′)G′h′, K(h′_{□₀})G′_{□₀}h′_{□₀}h_□C_□h_□, the commutator □̃Q′[G′_{□₀}, h′²_{□₀}]G′_{□₀}Q′*h_□C_□h_□, and the difference (3.97) □̃Q′(G′²_{□₀} − G′²_□)Q′*h_□C_□h_□ (pp.411–412).
  {#W1.6-1} Each factor is a product of several operators localised in a connected family of cubes, R′₀(□) = h_□C_□h_□ (p.412 l.32–p.413 l.8), and (3.98)–(3.99) (Theorem 3.9) bound the whole terms.
- {#W1.7} G: Δ_aG₀ = I − R (3.105), with the terms K(h_□)G_□h_□, (1 − ζ_{□̃})DPD*h_□G_□h_□, ζ_{□̃}(DPD* − DP_□D*)h_□G_□h_□, and ζ_{□̃}P_{□,1}(∂h_□)G_□h_□ (p.414 l.38–47), and P = G′Q′*(Q′G′²Q′*)^{−1}Q′G′ replaced by its expansion (p.415 l.2–28), which gives (3.107) with the bound (3.108) (Theorem 3.10, p.416 l.2–16).
- {#W1.8} G₁ and H₁ of PBG Sect. D, and with them VAR's H, have expansions of the same form, with tree-like walks where the vertices C^{(2)} of Δ^{(2)} meet three chains (p.427 l.14–21).

{#W1.9} PBG states the factor bounds only up to the power of the scale: "satisfies a bound of the type (3.89), possibly with an additional power of L^jη" (p.413 l.10–11), and then bounds whole terms instead (p.413 l.11).
{#W1.9-1} So (1.7) is a bound of whole walk terms, not of factors.

## 2. What the Two Runs Share {#WS2}

- {#W2.1} *Shared.* The data of every layer of the 𝐑-operation's sets lie at shared scales j ≥ k/2 − 1 ≥ 1 (LF note §4(d), *The lifts and the chain rule.*).
  {#W2.1-1} The big blocks of 𝒟_j are cells of ML^jηℤ^d, and ML^jε = ML^{j+1}(ε/L), so the partitions 𝒟, the cubes □, □̃ⁿ, the functions h_□ and ζ_{□̃} as functions of the point of space, the localisation domains X, the walks ω, the cubes σ₀ of RG II, and the s-weights are the same in both runs.
  {#W2.1-2} PBG takes "the partition of unity {h_□} defined at the end of Sect. A in [4]" (PBG p.408 l.22–23). PRT2 builds it from "the corresponding family of functions h described in (1.118)", rescaled to the cubes' scales (PRT2 p.229 l.12), and (1.118) is h_z(x) = Π_μh((x_μ − z_μ)/M₀) with one fixed h ∈ C₀^∞(]−⅔, ⅔[) (PRT1 p.36 l.43–53). With the normalisation of #W7.16-11, which gives Σh_□² = 1 where layers meet, each h_□ is a function on ℝ^d determined by h and the cubes.
  {#W2.1-2-1} ζ_{□̃} ∈ C₀^∞(□̃) is "defined similarly to h_□", equal to 1 on a cube containing □ (PBG p.414 l.46–47), and both runs take the same function on ℝ^d (#W7.22-1). So, the cubes being shared, each of these functions is the restriction of one function on ℝ^d to T_ε in run A and to T_{ε/L} in run B.
- {#W2.2} *Not shared.* The factors act on, or take values in, fields and sources on each run's own fine lattice, T_ε ∩ Ω₀^A(□) or T_{ε/L} ∩ Ω₀^B(□): G̃ and every factor K(h)G_□h act between fine sources and fine fields, and H and H₀ map data to fine fields (§1(a), (d)).
- {#W2.3} *The two local sequences.* For □ at the shared scale j, run A's sequence is {Ω_n^A(□)}_{n=0,…,j+1} with η = ε, and run B's is {Ω_{n′}^B(□)}_{n′=0,…,j+2} with η = ε/L.
  {#W2.3-1} By PBG p.408 l.32, dist(Ω_n^c, □̃⁴) = 2R₀M₀L^nη(L^{j−n} − 1)/(L − 1).
  {#W2.3-2} For run B at n′ = n + 1 this is 2R₀M₀L^nε(L^{j−n} − 1)/(L − 1), run A's value at n.
  {#W2.3-3} So Ω_{n+1}^B(□) = Ω_n^A(□) for n = 0, …, j + 1, the shells of the two runs at a common spacing L^nε coincide, and run B has one extra outer shell Ω₀^B ∖ Ω₁^B of width 2R₀M₀ε/L at the spacing ε/L, where run A's operators have their Dirichlet exterior.
  {#W2.3-4} On run A's shell 0 the two runs' spacings agree only after one averaging step: run A's field lives there on T_ε itself, and run B's field on T_{ε/L} is averaged once.

## 3. The Forms of (W-δ) {#WS3}

{#W3.1} (a) *Per walk term.* (W-δ) is stated per walk term (the LF note's (iii), #4.432 and #4.439): (1.7) bounds whole walk terms, PBG stating no bound per factor (#W1.9–#W1.9-1), and the two runs' factors act between different spaces (§2), except the factors h_□C_□h_□ of (3.98), which act from data to data.
{#W3.1-3} The cubes, the localisation domains, and the factors s(Δ₁)⋯s(Δ_m) are the same in both runs (§2), and so is the fluctuation variable B on the data space; the fields in which the walk terms of H, H₀, and G̃ take values are not.

{#W3.2} (b) *The averaged form.* Let W^X_ω denote the term of the walk ω in run X's expansion of H, H₀, or G̃, at run X's background.
{#W3.2-1} Let Q₁ := Q̄₁(U^B) be the linear part of the one-step double bar at run B's background, as in the Cauchy note's §10.4, and ℒ a right inverse of Q₁.
{#W3.2-2} The averaged form is, per walk term,

  {#W3.3} |(Q₁W^B_ω − W^A_ω𝒥)λ(x)| ≤ δ_w(ω)·O(1)(L^jη)^pO(M^{−1/2})^{|ω|}M^{−½|ω|}e^{−(δ₀/6)d(ω,y,y′)}|λ|,

  {#W3.4} with 𝒥 the identity on data (H and H₀) and 𝒥 = ℒ* on sources (G̃), (L^jη)^p the power of (3.108) for the norm in question, and the same for the norms of (3.42)–(3.47).
  {#W3.4-1} The rate δ₀/6 (δ₀′/54 after 10.3) is that of the local constituents of G and G′ in their own metric; in PRT2's global distance it is δ₀′/(54L) (§7, *The bound (1.11).*).
  {#W3.4-2} For the composite walks of §11, H₀ among them (§7), the walk factors O(M^{−1/2})^{|ω|}M^{−½|ω|}e^{−(δ₀/6)d(ω,y,y′)} are replaced by weights summable over the walks with the constant B_T and the decay e^{−δ_min d_T(ω,y,y′)} (§11, *The junction sums.*).
  {#W3.4-3} By the Cauchy note's §10.4, Q₁ maps run B's constraint set {Q^B𝒜 = B} into run A's, so (b) is the comparison through the chain rule.

{#W3.5} (c) *The fine form.* Let ι_Y be the localised lift of V(Y) (LF note (i); the Cauchy note's *The lift.* before its §1, §9.7, and §9.8). Its data derivative at the aligned background Ũ is dι_Y = H₁𝔡 + D_Bγ (#W10.5.7–#W10.5.9), and a gauge transformation of the pair lift, under which the terms are invariant, removes the gauge term D_Bγ (#W10.5.100–#W10.5.101). With ℒ_ι := H₁𝔡 at Ũ, the Landau part of dι_Y, the fine form is, per walk term,

  {#W3.6} |(W^B_ω − ℒ_ιW^A_ω𝒥′)λ(x)| ≤ δ_w(ω) times the bound of (b) in run B's norms,

  {#W3.7} with 𝒥′ the identity on data and 𝒥′ = ℒ_ι* on sources, the adjoint of the lift for the two runs' pairings, which maps run B's sources to run A's.
  {#W3.7-1} Since Q₁ℒ_ι = id on the data of Λ₁ (#W10.5.34), applying Q₁ to (c) gives (b) with ℒ = ℒ_ι in its source map 𝒥 = ℒ*, and δ_w multiplied by the norm of Q₁.

{#W3.8} (d) *Which form the consumer needs.* The consumer is Σ_YV(Y), whose terms are numbers.
{#W3.8-1} Each is built from a function 𝐄(□₀, 𝐔, 𝐀) of RG II (1.8), analytic in the fine field 𝐀 on the domain (I.3.31), at 𝐀^X(s) := (tζ̃_□ + t_□ζ_□)𝐇^X_k(s), which satisfies (I.3.31) with ½α₂ on the t_□ circle (RG II p.7 l.8–11).
{#W3.8-2} Here 𝐄^X and 𝐀^X(s) are run X's own, on its own fine lattice.
{#W3.8-3} Each localised term is a Cauchy integral in s on |s(Δ)| = e^{κ₁} (RG II (1.23), p.7 l.17–23), so the run difference must be bounded on the whole polydisc, not only at s = 1.
{#W3.8-4} The difference of values splits as

  {#W3.9} 𝐄^B(𝐔^B, 𝐀^B(s)) − 𝐄^A(𝐔^A, 𝐀^A(s)) = [𝐄^B(𝐔^B, 𝐀^B(s)) − 𝐄^B(𝐔^B, ℒ_ι𝐀^A(s))] + [𝐄^B(𝐔^B, ℒ_ι𝐀^A(s)) − 𝐄^A(𝐔^A, 𝐀^A(s))].

  {#W3.10} The second bracket is a frozen difference of the kind of the LF note's (i), at a run-A argument, with the fine side carried by ι and ℒ_ι.
  {#W3.10-1} The first bracket is run B's function at two run-B fluctuation fields.
  {#W3.10-2} Cauchy's estimate in 𝐀 on (I.3.31) bounds it by a multiple of the size of 𝐀^B(s) − ℒ_ι𝐀^A(s) relative to ½α₂, which is the form (c) together with (Wδ-3).
  {#W3.10-3} The part of 𝐀^B(s) − ℒ_ι𝐀^A(s) in ker Q₁ is invisible to (b). At s = 1 the chain's alignment controls it, since the decoupled field there is the minimiser's and ι(MU^B) = U^B; at complex s the decoupled field is not a minimiser's (LF note #4.146). So the consumer uses (c); this is (Wδ-2).

## 4. The Intertwined Galerkin Identities {#WS4}

{#W4.1} Fix □ at the shared scale j and one of the local operators of §1(c): 𝒪^X := Ω₀Δ_aΩ₀ (for G_□) or Ω₀Δ′_aΩ₀ (for G′_□), on the space 𝔉^X of fields on the bonds (or sites) of T^X ∩ Ω₀^X(□), with run B's background U^B and run A's aligned background Ũ := MU^B.
{#W4.1-1} The pairings ⟨·,·⟩_X carry the weights η_X^d of PBG p.393 l.46 and are bilinear, so 𝒪^X is symmetric on the complex domain (3.37) as the analytic extension of a symmetric form.
{#W4.1-2} G^X := (𝒪^X)^{−1} on 𝔉^X.
{#W4.1-3} Let χ_A be the characteristic function of Ω₀^A(□), and let ℒ be a right inverse of Q₁ with

  {#W4.2} (S) ℒ maps 𝔉^A into 𝔉^B.

{#W4.3} The local bilinear defect is β_□(ℱ, 𝒜) := ⟨χ_AQ₁ℱ, 𝒪^Aχ_AQ₁𝒜⟩_A − ⟨ℱ, 𝒪^B𝒜⟩_B for ℱ, 𝒜 ∈ 𝔉^B, and β_□(·, 𝒜)^♯ is the source on T_{ε/L} ∩ Ω₀^B(□) that represents ℱ ↦ β_□(ℱ, 𝒜) on 𝔉^B.

{#W4.4} (a) *The coarse side.* For every source g on T_{ε/L} ∩ Ω₀^B(□),

  {#W4.5} χ_AQ₁G^Bg − G^Aχ_Aℒ*g = G^Aχ_Aℒ*β_□(·, G^Bg)^♯.

  {#W4.6} Proof.
  {#W4.6-1} Put u_B := G^Bg and u_A := G^Aχ_Aℒ*g.
  {#W4.6-2} For X ∈ 𝔉^A, ℒX ∈ 𝔉^B by (S), and χ_AQ₁ℒX = X. So ⟨X, 𝒪^Au_A⟩_A = ⟨ℒX, g⟩_B = ⟨ℒX, 𝒪^Bu_B⟩_B and ⟨X, 𝒪^Aχ_AQ₁u_B⟩_A = ⟨χ_AQ₁ℒX, 𝒪^Aχ_AQ₁u_B⟩_A.
  {#W4.6-3} Their difference is β_□(ℒX, u_B) = ⟨X, ℒ*β_□(·, u_B)^♯⟩_A.
  {#W4.6-4} Both χ_AQ₁u_B − u_A and the right side lie in 𝔉^A, X is arbitrary there, and 𝒪^A is invertible on 𝔉^A.

{#W4.7} (b) *The fine side.* For every source f on T_ε ∩ Ω₀^A(□),

  {#W4.8} ℒG^Af − G^BQ₁*χ_Af = −G^Bβ_□(·, ℒG^Af)^♯.

  {#W4.9} Proof.
  {#W4.9-1} Put u_A := G^Af and u_B := G^BQ₁*χ_Af.
  {#W4.9-2} For Y ∈ 𝔉^B, ⟨Y, 𝒪^Bu_B⟩_B = ⟨χ_AQ₁Y, f⟩_A = ⟨χ_AQ₁Y, 𝒪^Au_A⟩_A = ⟨χ_AQ₁Y, 𝒪^Aχ_AQ₁ℒu_A⟩_A, since χ_AQ₁ℒu_A = u_A by (S).
  {#W4.9-3} So ⟨Y, 𝒪^B(ℒu_A − u_B)⟩_B = −β_□(Y, ℒu_A), and ℒu_A − u_B ∈ 𝔉^B.

  {#W4.10} With ℒ = ℒ_ι this is the identity of the form (c).
  {#W4.10-1} The Cauchy note's representation E = G₁^Qℒ*β(·, 𝒜^B) of §10.4 is the analogue of (a) for the data lift H₁ on the whole lattice.

{#W4.11} (c) *Where the defect is small.* For a field 𝒜 that alternates at the spacing ε/L inside one block, with Q₁𝒜 = 0, β_□(𝒜, 𝒜) = −⟨𝒜, 𝒪^B𝒜⟩_B, which is of order (ε/L)^{−2}‖𝒜‖².
{#W4.11-3} So β_□ is small only as a bilinear form between fields regular at the scale of their shell, through the oscillation, and the identities of (a) and (b) use it only there: β_□ is paired with G^Bg or ℒG^Af, which are C^{1,β} by (3.43) for G^B, and for ℒG^Af by (3.43) for G^A together with the regularity of the lift ((H_ℒ) of 10.1 on the coarse side; for ℒ_ι, part of (Wδ-2)).
{#W4.11-4} The functional form (Wδ-1) is what turns this into kernel bounds (§5(c)).

{#W4.12} (d) *The condition (S).* For the scalar operators (G′_□), (S) holds with the transported block-constant lift ℒ′f(x) := R(U^B(Γ_{y,x}))^{−1}f(y) for x ∈ B(y): by (3.19), Q′(U^B)ℒ′f(y) = Σ_{x∈B(y)}L^{−d}f(y) = f(y), so ℒ′ is an exact right inverse of finite range one block.
{#W4.12-1} Ω₀^A(□) is a union of blocks B(y) of T_ε, y ∈ Ω₀^A, and the margin 2R₀M₀ε/L of §2 exceeds one block of T_ε when 2R₀M₀ ≥ L, so ℒ′ maps 𝔉^A into 𝔉^B. ℒ′ is also an isometry, ⟨ℒ′f, ℒ′f′⟩_B = ⟨f, f′⟩_A, since the bilinear trace form is invariant under Ad of the complexified group, so the Gram defect of the lift in Q′G′²Q′* vanishes for this ℒ′.
{#W4.12-2} For one-forms, Q₁ = Q̄₁(U^B) is the main term of CMP 98 (124), the straight-path average of the tube, plus terms that vanish at U = 1 but not at a regular U^B.
{#W4.12-3} The tube-constant lift inverts the main term exactly, but its right inverse for Q̄₁(U^B) obtained by a Neumann series has exponentially decaying tails, as do the Cauchy note's ℒ and dι.
{#W4.12-4} The cut-off χ_Bℒ of any right inverse satisfies (S) under R₀M₀ ≥ L (10.1).

## 5. The Shells of the Local Problems {#WS5}

{#W5.1} Shells are indexed by run A's n: run A's shell n and run B's shell n + 1 coincide (§2), and run B's extra shell is indexed n = −1.
{#W5.1-1} For a block y of the shell n, ‖𝒜‖_{1,β;y} := sup((L^nη)^{−1}|𝒜| + |∇𝒜|) + (L^nη)^β‖∇𝒜‖_β, taken over the blocks within weighted distance 2 of y, with the Hölder quotient of PBG (3.40); this is the norm of (Wδ-1).

{#WOG.1} **(Wδ-1) The per-shell defect of the local operators.** The local propagators G′_□, C_□, and G_□ of PBG (3.87) are inverses of operators on each run's own fine lattice, on a nested sequence of shells that reaches the scale 0 inside X̃⁵ (§1(c)).
{#WOG.1-1} (Wδ-1) is the functional form of their bilinear defect, shell by shell: there is a constant C_df(β), independent of the shell n, the scale k, the volume, the block y, and 𝒜 (at the instances of §10 it is C′_L(β) + 8d + a of #W10.2.28–#W10.2.29 and C_{[h,O]}(β) and C_{[h,DR_□D*]}(β) of #W10.4.62), such that for each 𝒜 in run B's local field space there are fields s₀, s₁, and s₂ on T_{ε/L} ∩ Ω₀^B(□) with

  {#WOG.2} β_□(ℱ, 𝒜) = ⟨D_B*ℱ, s₂⟩ + ⟨∇ℱ, s₁⟩ + ⟨ℱ, s₀⟩ for every ℱ, and on each block y of the shell n, sup_{Δ(y)}(|s₁| + |s₂| + L^nη|s₀|) ≤ C_df(β)ϖ_n‖𝒜‖_{1,β;y} (for the gauge-fixing part of G_□, with the decay-weighted norm ⟨𝒜⟩_y of 10.4 in place of ‖𝒜‖_{1,β;y}),

  {#WOG.3} with ϖ_n := L^{−βn} on the shells n ≥ 1 of run A's local sequence, ϖ := 1 on run A's shell 0 and on run B's extra shell, and the same with the two slots exchanged, at aligned backgrounds and on the analyticity domain (3.37) (§4).
  {#WOG.3-1} For the gradient entries of (3.42)–(3.44) the sources s₁ and s₂ need in addition a Hölder bound at the scale of their shell.

{#W5.2} (a) *The averaging terms.* The a-terms are where the chain rule acts.
- {#W5.3} Q*aQ of (3.16) carries the plain a and the weight (L^nη)^{d−2} on the bonds of Λ_n.
  {#W5.3-1} Run B's layer Λ^B_{n+1} is run A's Λ^A_n, with the weight (L^{n+1}ε/L)^{d−2} = (L^nε)^{d−2}, and Q^B_{n+1}(U^B) = Q^A_n(Ũ)Q₁ by (B4), exactly (the Cauchy note's §10.4), with Q^A₀ the identity on run A's shell 0 (the 0-fold composition of (3.15)).
  {#W5.3-2} For n ≥ 1, Q^A_n averages inside Ω^A₁(□), and for n = 0 the factor χ_A is 1 on Λ^A₀, so χ_A changes nothing.
  {#W5.3-3} Hence the a-part of β_□ is exactly −aΣ_{b∈Λ^B₀}(ε/L)^{d−2}⟨ℱ(b), 𝒜(b)⟩, supported on run B's extra shell, with s₀ of size ≤ a(ε/L)^{−1}‖𝒜‖_{1,β;y} there in the normalisation of (Wδ-1).
- {#W5.4} Q′*aQ′ of (3.24) carries a_n, with a_{n+1} = aa_n/(aL^{−2} + a_n) and a₁ = a₀ = a (p.394 l.29), so 1/a_n = (1/a)Σ_{i=0}^{n−1}L^{−2i} for n ≥ 1.
  {#W5.4-1} The chain rule Q′^B_{n+1} = Q′^A_nQ′(U^B) is the composition (3.19), with the averaged configurations of (3.19) identified with the aligned ones as in (B1) and (B4).
  {#W5.4-2} The composition is exact at the plain average.
  {#W5.4-3} At the double bar it holds after the gauge rotation v₁ of (B1), so Q′₁ := R(v₁)^{−1}Q′(U^B), with ℒ′ rotated by R(v₁) in the same way; the rotation is a gauge transformation at the coarse sites, real at real backgrounds, and at complex backgrounds it changes the bounds by at most the factor 2 of Ad (10.2).
  {#W5.4-4} Run A's shell n carries a_n and run B's the same shell a_{n+1}.
  {#W5.4-5} They agree at n = 0, and for n ≥ 1, 1/a_{n+1} − 1/a_n = L^{−2n}/a, so |a_{n+1} − a_n|/a_n ≤ L^{−2n}/(1 − L^{−2}).
  {#W5.4-6} So the scalar a-part has the form of (Wδ-1) with ϖ_n replaced by L^{−2n}/(1 − L^{−2}) ≤ 2L^{−βn} for β ≤ 2, plus the extra-shell term as above.

{#W5.5} (b) *The other terms.* The chain rule does not act on D*D (Δ_U for scalars), on the curvature term Δ′ of (3.10), or on DRD* = DD* − DPD* (p.414 l.3).
{#W5.5-1} On run A's shells n ≥ 1 their defect is the oscillation of the Cauchy note's §10.4 at the ratio ε/(L^nε) = L^{−n}, which 10.2 and 10.4 derive for the local multiscale operators.
{#W5.5-2} DPD* is nonlocal through P = G′Q′*(Q′G′²Q′*)^{−1}Q′G′, so its defect needs the scalar comparisons first, then P, then G. On run A's shell 0 and on run B's extra shell nothing relates the two runs' operators: there run A's D*D on T_ε meets run B's averaged once, and run B's extra shell meets run A's Dirichlet exterior.
{#W5.5-3} So, shell by shell, the chain rule reduces the averaging terms of every shell, the scale-0 shell included, to the shared lattice, and it does not reduce the Laplacian, curvature, and gauge-fixing parts of the scale-0 shells.
{#W5.5-4} (c) shows that these parts need no reduction: with ϖ = 1 there, the decay through the shells makes their contribution of relative order L^{−j} = ε/a_j.

{#W5.6} (c) *The reduction.* Let ℒ satisfy (S) with range one block of T_ε and with Σ_{z∈Δ(y)}η_B^d(|∇_Bℒv(z)| + (L^nη)^{−1}|ℒv(z)|) ≤ C_ℒΣ_{y‴}Σ_{w∈Δ(y‴)}η_A^d(|∇_Av(w)| + (L^nη)^{−1}|v(w)|), the sum over the 3^d blocks y‴ next to y.
{#W5.6-1} Let y, y′ be blocks of □ (layers j and j + 1 of the local sequence), x ∈ Δ(y), and supp g ⊂ Δ(y′).
{#W5.6-2} The conditions on PBG's R₀ and M₀ are

  {#W5.7} (W-c) (2.59) at α = ⅓ for the local sequences, with the shell width 2R₀M₀ in place of RM, (1/6)δ₀R₀M₀ > 2d log c₀(1/6) + 1; and 4δ₀R₀M₀ ≥ 3(1 + β)log L; and R₀M₀ ≥ L and δ_QR₀M₀ ≥ 12 log L (for §4(d) and 10.1).
  {#W5.7-1} For the one-form G_□, δ₀′ = min(δ₀, ¼δ_Q, ¼δ₁, ¼δ_c) (10.6) replaces δ₀ in these conditions and in the rate (10.1).
  {#W5.7-2} The conditions for C_□ and for the defect at general points are stated in 10.2–10.3 and collected in §8, *The conditions on the constants.*

  {#W5.8} Then

  {#W5.9} |(χ_AQ₁G^B_□ − G^A_□χ_Aℒ*)g(x)| ≤ C_□(β)(ε/a_j)^β(L^jη)²e^{−(δ₀/3)d(y,y′)}|g|,

  {#W5.10} C_□(β) := 6c₀^d(1/6)c_βC₃, C₃ := 9·3^de^{4δ₀}(1 + L)C_ℒC_df(β)B₀B₀(β), with C_df(β) of (Wδ-1) (#WOG.1-1), and c_β := L^{1+β}(3 + L^β + L^{1+β}/(L − 1)), where the factor L^{1+β} covers the intersected sequences of §7 (*The shell sums of §5(c).*) and is kept for every cube.

  {#W5.11} Proof.
  {#W5.11-1} By §4(a) the left side is |(G^Aχ_Aℒ*(D_Bs₂ + ∇_B*s₁ + s₀))(x)|, with the sources of (Wδ-1) for 𝒜 = u_B := G^B_□g, split over the blocks y″ of the shells.
  - {#W5.12} Leg 2.
    {#W5.12-1} For y″ in the shell n, (3.42) and (3.43) for G^B_□ (Corollary 3.6), with the factor of the receiving layer, give ‖u_B‖_{1,β;y″} ≤ 3e^{2δ₀}B₀(β)(L^nη)e^{−δ₀d(y″,y′)}|g|.
    {#W5.12-2} The factor e^{2δ₀} covers the blocks within distance 2, and B₀ ≤ B₀(β).
    {#W5.12-3} So by (Wδ-1), sup_{Δ(y″)}(|s₁| + |s₂| + L^nη|s₀|) ≤ 3e^{2δ₀}C_df(β)ϖ_nB₀(β)(L^nη)e^{−δ₀d(y″,y′)}|g|.
  - {#W5.13} Leg 1.
    {#W5.13-1} For a source σ on Δ(y″), (G^Aχ_Aℒ*∇_B*σ)(x) = ⟨∇_Bℒ[G^A(·, x)], σ⟩_B by the symmetry of G^A, so it is ≤ sup|σ| times the block sum of ∇_BℒG^A(·, x).
    {#W5.13-2} By the bound on ℒ and (3.42) for G^A (the entries G∇* and G, the block sum of a kernel row being the operator bound on sources bounded on the block), this is ≤ sup|σ|·3^de^{2δ₀}C_ℒB₀[(L^jη) + (L^jη)²(L^nη)^{−1}]e^{−δ₀d(y,y″)}.
    {#W5.13-3} The same holds for D_B in place of ∇_B* (p.398 l.49–50).
    {#W5.13-4} For s₀ the factor is 3^de^{2δ₀}C_ℒB₀(L^jη)²e^{−δ₀d(y,y″)}, that is (L^jη)²(L^nη)^{−1} times L^nη|s₀|.
    {#W5.13-5} Since n ≤ j + 1, (L^jη) ≤ L(L^jη)²(L^nη)^{−1}.
  - {#W5.14} The product.
    {#W5.14-1} The factor (L^nη)^{−1} of leg 1 cancels the factor L^nη of leg 2, so the shell n contributes ≤ C₃ϖ_n(L^jη)²Σ_{y″}e^{−δ₀[d(y,y″) + d(y″,y′)]}|g|.
    {#W5.14-2} One third of the decay gives e^{−(δ₀/3)d(y,y′)} by the triangle inequality (2.54).
    {#W5.14-3} One third gives the count Σ_{y″}e^{−(δ₀/3)d(y,y″)} ≤ 6c₀^d(1/6) over one layer, by (2.58) at α = ⅓ under the first condition of (W-c).
    {#W5.14-4} The last third is ≤ e^{−(4/3)δ₀R₀M₀(j−n−1)₊}, since by (2.60) the weighted distance from a block of □ to the shell n is ≥ 2R₀M₀(j − n − 1), and both legs cross the shells.
    {#W5.14-5} This is ≤ L^{−(1+β)(j−n−1)₊} by the second condition.
  - {#W5.15} The sum over the shells.
    {#W5.15-1} The shells j and j + 1 give ≤ 2L^{−βj}.
    {#W5.15-2} The shells 1 ≤ n ≤ j − 1 give Σ_nL^{−βn}L^{−(1+β)(j−n−1)} = L^{1+β}L^{−βj}Σ_nL^{−(j−n)} ≤ L^{1+β}L^{−βj}/(L − 1).
    {#W5.15-3} The shell 0 (ϖ = 1) gives L^{−(1+β)(j−1)} ≤ L^βL^{−βj}, and run B's extra shell (ϖ = 1, distance ≥ 2R₀M₀j, with d(y, y″) for y″ in the extra shell measured to the nearest block of run A's shell 0) gives ≤ L^{−βj}.
    {#W5.15-4} So Σ_nϖ_nL^{−(1+β)(j−n−1)₊} ≤ c_βL^{−βj}, and L^{−j} = ε/a_j in run A's units.

  {#W5.16} The fine side (§4(b)) is the same computation with the roles exchanged, with ℒ_ιG^Af in leg 2, which needs the C^{1,β} bound of ℒ_ι (Wδ-2).
  {#W5.16-1} The gradient entries of (3.42)–(3.44) at x need ∇G^A∇* in leg 1, which (3.44) bounds only through a Hölder norm of the source, so they need the Hölder bound of s₁ and s₂ that (Wδ-1) includes.
  {#W5.16-2} C_□ is not covered by this computation: the two runs' data spaces differ by run B's extra data layer, and its bound is of the form (3.48), not (3.42). 10.3 gives the exact identity and the reduction.
  {#W5.16-3} The bound above, with the rate δ₀/3, holds for an ℒ of range one block, which covers the scalar G′_□ with ℒ′.
  {#W5.16-4} For the one-form G_□, the lift has exponential tails, and 10.1 gives the same bound with C_ℒ′ and the rate δ₀′/3.

{#W5.17} (d) *The multiscale domains.* A cube □ of a walk in X lies in a global layer j ≥ m(X) of the 𝐑-operation's set or at its interface with j + 1, so (ε/a_j)^β ≤ (ε/a_{m(X)})^β, and the coarser layers contribute less.
{#W5.17-1} The shells at the scales n < j of the local sequence are PBG's construction inside □̃⁵, not layers of the global set; (c) shows that they cost only the factor c_β, so they do not move the bound to a finer scale.

## 6. The Background Part {#WS6}

{#W6.1} A walk term W^A_ω depends on the configuration on ∪_iX̃_i⁵ (Theorem 3.10, p.416 l.7–8).
{#W6.1-1} By the LF note's (ii), *The Fine Side at the Multiscale Chain.*, *The coarse side.* (#4.314), U^A = e^{iεA}Ũ with a_{j(x)}|A(x)| + a_{j(x)}²|∇A(x)| ≤ d̄(x) := C_U(M)(ε/a_{min(j(x),n)})^{(1−ε₀)/3}ε₁.
{#W6.1-2} Put d̄(ω) := sup_{x∈∪X̃_i⁵}d̄(x) and U(t) := e^{itεA}Ũ.
- {#W6.2} *The domain.* For |t| ≤ α₁/(2d̄(ω)), U(t) satisfies (3.37) layer by layer for the global layers (LF note §4(d), *The multipliers.*, #4.32).
  {#W6.2-1} For the local sequence of a cube, (3.37) asks |A| < α₁(L^nη)^{−1} on the shell n, which is weaker on the finer shells since L^nη ≤ a_{j(x)}.
- {#W6.3} *Analyticity with the bounds.* The local propagators extend analytically to this domain with the inequalities of Theorems 3.1–3.3 (Theorem 3.4, p.400 l.8–9, whose proof (3.82)–(3.86) uses only Theorems 3.1–3.3 at U, p.407 l.40, and these hold for the local sequences by Corollary 3.6).
  {#W6.3-1} The explicit local operators are analytic in U by their formulas (3.88), (3.101)–(3.103).
  {#W6.3-2} PBG's proof of (3.108) uses only the constituent bounds (p.410 l.13–30), so W^A_ω(U(t)) is analytic for |t| < α₁/(2d̄(ω)), with the bound (3.108) there.
- {#W6.4} *Cauchy's estimate.* With r := α₁/(2d̄(ω)) ≥ 2, |W^A_ω(U^A) − W^A_ω(Ũ)| ≤ sup_{|t|≤1}|∂_tW^A_ω(U(t))| ≤ sup_{|t|=r}|W^A_ω(U(t))|/(r − 1) ≤ (4d̄(ω)/α₁) times the bound (3.108), in each norm of (3.108).
- {#W6.5} *The current.* The operators of PBG Sect. D (G₁ and H₁, and with them VAR's H) carry the current.
  {#W6.5-1} For them the path is the pair path (U(t), 𝐉(t)), 𝐉(t) := J′ + tδ𝐉, δ𝐉 := J(U^A) − J′, with J′ the intermediate current of the LF note at the multiscale chain of #W6.1-1, paired with Ũ (its #4.356, where δ𝐉 is δ𝐉_c), so the path runs from (Ũ, J′) at t = 0 to (U^A, J(U^A)) at t = 1.
  {#W6.5-1-1} The currents obey a_{j(x)}³|δ𝐉(x)| ≤ x̂_Jd̄(x) and a_{j(x)}³|J′(x)| ≤ B̄′_Jε₁ (LF #4.357), and the analyticity holds on the pair class 𝒟̄ (LF #4.60).
  {#W6.5-2} The pair class bounds the current by α_Ja_{j(x)}^{−3} with α_J := Mα₀ (LF #4.60), so α_J is fixed with α₀.
  {#W6.5-3} Put α_*′ := min(α₁, α_J/x̂_J) and take the pair (U(t), 𝐉(t)), with r := α_*′/(2d̄(ω)) ≥ 2 in place of the r of #W6.4.
  {#W6.5-4} For |t| ≤ r, a_{j(x)}³|𝐉(t)(x)| ≤ a_{j(x)}³|J′(x)| + |t|a_{j(x)}³|δ𝐉(x)| ≤ B̄′_Jε₁ + rx̂_Jd̄(ω) ≤ B̄′_Jε₁ + ½α_J.
  {#W6.5-5} So under 4B̄′_Jε₁ ≤ α_J the current is at most ¾α_Ja_{j(x)}^{−3}, the pair stays in 𝒟̄, and the estimate of #W6.4 holds with α_*′ in place of α₁.
{#W6.6} The background part is therefore ≤ 4d̄(ω)/α_*′ ≤ 4C_U(M)ε₁(ε/a_{m(ω)})^{(1−ε₀)/3}/α_*′ times the bound of the walk term, with m(ω) the finest global layer that ∪X̃_i⁵ meets, under 4d̄(ω) ≤ α_*′.
{#W6.6-1} The LF note's (iii) carries the change of background separately, through r(Y), and uses only the lattice part of §5.

## 7. The Walk Term, the Telescoping, and (1.11) {#WS7}

- {#W7.1} *Constituents.* A walk term is a product of factors, and each factor is a product of at most N_c constituents.
  {#W7.1-1} N_c is an absolute number: "several" operators, at worst three attached to one (PBG p.412 l.3–6, l.34–35, p.415 l.28–30).
  {#W7.1-2} The constituents are the local propagators of §1(c), the multiplications by h_□, by the h′_□ of the partitions 𝒟′ and 𝒟″, by ζ_{□̃}, and by characteristic functions, the explicit local operators K′(h_□), K(h_□) (which contains S_j(∂h_□), PBG (3.103)–(3.104)), P_{□,1}(∂h_□), the scalar averaging commutators [h_□, Q′] of the third sum of (3.95), D, D*, Q′, and Q′*, the differences G′²_{□₀} − G′²_□ of (3.97), G′_{□₀} − G′_□, C_{□₀} − C_□, and h′_{□₀} − ζ_{□̃} (p.412 l.19–28, p.415 l.17–19), and the commutators [G′_{□₀}, h′²_{□₀}] (p.412 l.15–17), [ζ_{□̃}, C_□], and [ζ_{□̃}, G′_□] (p.415 l.23).
  {#W7.1-3} N_c counts the constituents after the expansions of these commutators below ([ζ_{□̃}, C_□] gives four products, each containing C_□ twice); it remains a fixed number.
- {#W7.2} *Intertwining of the explicit constituents.* Q and Q′ intertwine exactly by (B4) and (3.19), and D by the covariance Q̄₁D_B = D_AQ′₁, PBG (3.114)–(3.115) at n = 1.
  {#W7.2-1} For a multiplication by a function h of the point, Q₁(hf)(b) − h(b)(Q₁f)(b) is a sum over the fine bonds b′ of the tube of b of (h(b′) − h(b))f(b′) with the weights of Q₁.
  {#W7.2-1-1} For □ ∈ 𝒟_j, |∂^kh_□| ≤ c_h(ML^jη)^{−k} for k ≤ 3, with c_h := L³c and c of #W7.16-11-3: in the bulk the cubes of 𝒟 that meet □ lie in the layers j − 1, j, and j + 1 (PRT2 (2.2), #W7.16-4), so j(h_□) ≥ j − 1.
  {#W7.2-2} By the gradient bound |∂h| ≤ c_h(ML^jη)^{−1} (#W7.2-1-1; the h′_□ of 𝒟′ and 𝒟″ satisfy it with c_h* at their own layers, *The differences and the further commutators.* below), this is at most 3(2d + 1)c_hε/(ML^jη) = 3(2d + 1)c_h(ε/a_j)/M relative to the term (the total weight w_Q ≤ 3 of Q₁ times the ℓ¹ radius (2d + 1)ε of its kernel from the point where h is taken, as in 10.4).
  {#W7.2-3} The same holds for ℒ* with the factor C_ℒ when ℒ has range one block, and for ℒ̃* = ℒ_N*χ_B of 10.1 with the factor C_ℒ′m_Q, m_Q := 1 + sup_bΣ_cd_ε(b, c)e^{−¼δ_Qd_ε(b,c)}, a constant of d and δ_Q: the kernel difference is ℒ̃(b, c)(h(b) − h(c)) with |h(b) − h(c)| ≤ |∂h|εd_ε(b, c), and the tails are summed as in 10.1, *The cost in §5(c).* The characteristic functions among the constituents are those of □̃ and 1 − □̃ in (3.95) (p.411 l.8–9), which multiply data, the output of Q′, on which the two runs agree since Q′_B = Q′_AQ′₁; so they intertwine exactly.
  {#W7.2-4} The characteristic functions of the blocks Δ(y) of p.410 l.14 are not constituents: they are a partition of unity inserted to bound a term, so each run's bound inserts them on its own lattice, and they need no intertwining.
  {#W7.2-5} The scalar averaging commutator [h, Q′] maps scalar fine fields to data, and by Q′_AQ′₁ = Q′_B its intertwining defect is exactly [h, Q′_A]Q′₁ − [h, Q′_B] = −Q′_A[h, Q′₁], at most 4dεc_h(ML^jη)^{−1} times the sup of its argument (the factor 2 for Q′_A at complex backgrounds), against the bound c_KM^{−1} of [h, Q′_B] relative to Q′_B;
  {#W7.2-6} so its relative defect is at most 4dc_K^{−1}c_h(ε/a_j), with no loss of M. The adjoint [Q′*, h] maps data to scalar fine fields, and by Q′_B* = Q′₁*Q′_A* and Q′₁Q′₁* = 1 its defect is exactly Q′₁[Q′_B*, h] − [Q′_A*, h] = Q′₁[Q′₁*, h]Q′_A*, at most 8dεc_h(ML^jη)^{−1} times the sup of its argument (one Ad factor 2 more, for Q′₁), so its relative defect is at most 8dc_K^{−1}c_h(ε/a_j), which bounds both.
  {#W7.2-7} K′(h), K(h) (with S_j(∂h)), and P_{□,1}(∂h) are built from the operators with one factor ∂h (PBG (3.88), (3.101)–(3.105)), so their defects are of the type of β_□ and belong to (Wδ-1); they are derived in 10.4 (*The commutator factors K(h), P_{□,1}(∂h), and S_j(∂h)*), as commutators of h with operators whose defects are derived there.
- {#W7.3} *The differences and the further commutators.* PBG bounds G′²_{□₀} − G′²_□ by the usual factors of its propagators times e^{−2δ₀M} ≤ (2δ₀M)^{−1}, since the two local operators differ only outside □̃₀, at a distance ≥ M from □̃ on the scale L^jη (p.412 l.19–28, by [2]), and uses the bound with (2δ₀M)^{−1} as the factor's bound.
  {#W7.3-1} For G′_{□₀} − G′_□ and C_{□₀} − C_□ it says that they "are small by the same reason as before" (p.415 l.18–19).
  {#W7.3-2} The reason is that of (3.97): a difference of propagators defined on two domains carries, besides the usual factors, an exponential factor in the distance between the localisations and a closest point where the domains differ, proved in [2] from the random walk expansions and so valid for all of [4]'s propagators and for the cube sequences (p.412 l.23–27; restated at p.426 l.35–37, which names (3.97) as such a use).
  {#W7.3-3} Here the localisations lie in □̃ (the factors carry ζ_{□̃} and h_□), and the operators of □ and □₀ "may differ" only "outside □̃₀, and the distance from □̃ to □̃₀^c is at least M" (p.412 l.27–28), so the factor is again e^{−2δ₀M} ≤ (2δ₀M)^{−1}.
  {#W7.3-5} The two runs' differences are taken on the same cubes □ and □₀, which are scale-k objects (§2).
  {#W7.3-6} The defect of a difference is the difference of the two propagators' defects.
  {#W7.3-7} For G′ and C each is at most C_□(β)(ε/a_j)^β times the usual factors (§5(c), 10.1, 10.3, at the rate δ₀′/3 or δ₀/27), for the propagators of □₀ and of 𝒟″'s cube □̃₀² as well.
  {#W7.3-8} Those derivations use two properties of the cube's sequence: Corollary 3.6 holds for it at the run's background, and it satisfies PRT2 (2.1)–(2.4) at the size R₀M₀ (consecutive domains at the distance ≥ 2R₀M₀L^nη, unions of R₀M₀-blocks of their scale).
  {#W7.3-9} The second gives (2.58)–(2.60), the separation of the innermost shell (10.3, *All distances are run B's weighted distance*, there obtained from K ≥ 2 for p.408's sequence), and the margin 2R₀M₀ε/L of (S) (§2, §4(d)); (W-c) are conditions on R₀M₀ alone.
  - {#W7.4} In the first case of p.411 l.22–23, □₀ = □̃² of the layer j, we take for □₀ the sequence of □ itself (p.408 l.28–35, intersected with the global domains when □̃³ meets Ω_j^c, *The cubes next to the finer layer.* below), so G′_{□₀} = G′_□, C_{□₀} = C_□, and the differences vanish.
    {#W7.4-1} This is a valid choice for the expansion (3.90) on 𝒟′, which needs of the operator of □₀ only that its sequence agree with PBG's global sequence on a neighbourhood of supp h′_{□₀}, through the local identity (3.88). supp h′_{□₀} = supp φ lies within the sup distance (17/6)ML^jη of □, so in □̃³ at the sup distance ≥ (1/6)ML^jη from its boundary (*G′² is a composition* below, the construction of the partitions).
    {#W7.4-2} On □̃³ □'s sequence agrees with the global one (*The cubes next to the finer layer.*), and the stencils of the averagings at points of supp h′_{□₀}, of side ≤ L^{j+1}η ≤ (1/6)ML^jη under M ≥ 6L, stay in □̃³.
    {#W7.4-3} Corollary 3.6 and (2.1)–(2.2) hold for this sequence (*The cubes next to the finer layer.*).
  - {#W7.5} *The cubes next to the finer layer.* PBG's dichotomy at p.408 l.29–30, that □̃³ either lies in B^j(Λ_j) or also meets B^{j+1}(Λ_{j+1}), omits a third case.
    {#W7.5-1} For j ≥ 1, a cube □ ∈ 𝒟_j within three big blocks of Ω_j^c has □̃³ meeting Ω_j^c, so the layer j − 1: the cubes of 𝒟_j need only one big block in B^j(Λ_j) (p.408 l.20–21), and □̃³ extends □ by 3ML^jη.
    {#W7.5-2} There PBG's sequence, with Ω_j(□) = □̃⁴ at the scale j, does not agree with the global one on □̃³, and p.409 l.2's statement that □̃⁵ lies in a cube of the class of (3.35) fails, since the class cubes lie in B^{j′}(Λ_{j′}) ∪ B^{j′+1}(Λ_{j′+1}) (p.396 l.14–16).
    {#W7.5-3} For the cubes of this case the sequence is intersected with the global domains, a choice made in both runs: Ω′_n(□) := Ω_n(□) ∩ Ω_n for n ≤ j, and Ω′_{j+1}(□) := ∅.
    {#W7.5-4} In the bulk the two runs' global domains are aligned (§11), so the two runs' choices correspond. p.409 l.2's class statement is not used below, for any cube.
    - {#W7.6} Geometry.
      {#W7.6-1} For □ ∈ 𝒟_j in the bulk, the points of □̃^n lie within the sup distance (n + 1)ML^jη of □'s big block in B^j(Λ_j), which lies in Ω_j and outside Ω_{j+1} (PRT2 (2.3)).
      {#W7.6-2} PRT2 (2.2) gives the ℓ¹ separations dist(Ω_{j−1}^c, Ω_j) > RML^{j−1}η, dist(Ω_j^c, Ω_{j+1}) > RML^jη, and dist(Ω_{j+1}^c, Ω_{j+2}) > RML^{j+1}η.
      {#W7.6-3} Under R ≥ 12dL, □̃⁵, within the ℓ¹ distance 6dML^jη of that block, lies in Ω_{j−1}, and □̃³, within the ℓ¹ distance 4dML^jη, misses Ω_{j+2}.
      {#W7.6-4} If □̃³ meets Ω_j^c, then □̃³ ∩ Ω_{j+1} = ∅, since two points of □̃³ are at the ℓ¹ distance ≤ 8dML^jη < RML^jη.
    - {#W7.7} Agreement on □̃³.
      {#W7.7-1} Ω_n(□) ⊇ □̃⁴ for n ≤ j (p.408 l.30–32).
      {#W7.7-2} If □̃³ meets Ω_j^c, then Ω′_n(□) ∩ □̃³ = Ω_n ∩ □̃³ for n ≤ j, and both are empty on □̃³ for n ≥ j + 1.
      {#W7.7-3} Otherwise □̃³ ⊂ Ω_j and □̃³ ∩ Ω_{j+2} = ∅, so the global domains on □̃³ are Ω_n ⊇ □̃³ for n ≤ j, Ω_{j+1} ∩ □̃³ = B^{j+1}(Λ_{j+1}) ∩ □̃³ (PRT2 (2.3)–(2.4)), and ∅ for n ≥ j + 2, as PBG's sequence has (Ω_{j+1}(□) = □̃³ ∩ B^{j+1}(Λ_{j+1}), p.408 l.30, and empty in the first case of the dichotomy).
      {#W7.7-4} Either way □'s sequence agrees with the global one on □̃³, which contains supp h_□ ⊂ □ and supp h′_{□₀} with the margin ≥ (1/6)ML^jη that the stencils need under M ≥ 6L.
    - {#W7.8} PRT2 (2.1)–(2.4) at the size R₀M₀.
      {#W7.8-1} For n < j, dist(Ω′_n(□)^c, Ω′_{n+1}(□)) ≥ min(dist(Ω_n(□)^c, Ω_{n+1}(□)), dist(Ω_n^c, Ω_{n+1})) ≥ min(2R₀M₀, RM)L^nη = 2R₀M₀L^nη.
      {#W7.8-2} Ω_n(□) is a union of R₀M₀-blocks of the scale n (p.408 l.34), and Ω_n is a union of M-blocks of the scale n with M = KR₀M₀, so Ω′_n(□) is a union of R₀M₀-blocks of the scale n.
      {#W7.8-3} The coarsest domain Ω′_j(□) = □̃⁴ ∩ Ω_j is a union of big blocks of the scale j, and there is no shell at the index j + 1.
      {#W7.8-4} So (2.58)–(2.60) and the margin of (S) hold as for PBG's sequences.
    - {#W7.9} Corollary 3.6.
      {#W7.9-1} Ω′_0(□) ⊂ Ω₀(□) ⊂ □̃⁵ (p.408 l.35), a cube of 12 big blocks of the scale j in Ω_{j−1}.
      {#W7.9-2} The axial-gauge argument of the item *Corollary 3.6.* below (§11's, from VAR (9)–(10) on VAR's class cubes of the index m or m − 1 at each point of a layer m, under O(1)L⁴C₀ε₁ ≤ α₀ and ε₁ ≤ a₁/(3L)) gives (3.35) on □̃⁵ at the index j, with O(1)L²Mα₀ for |A| and O(1)L³Mα₀ for |∇A|.
      {#W7.9-3} The coarsest index of the intersected sequence is j, so α₁ = O(1)L³Mα₀.
      {#W7.9-4} For PBG's own sequences of the other cubes, whose coarsest index is j + 1, the same argument with the shift from j to j + 1 gives α₁ = O(1)L⁵Mα₀.
      {#W7.9-5} Both are within §8's smallness O(1)L⁵Mα₀ ≤ a₁.
      {#W7.9-6} So Theorems 3.1–3.3 hold for the operators of every bulk cube through Corollary 3.5 (p.407 l.45–47), without p.409 l.2.
      {#W7.9-7} Every bound of PBG's that carries O(1)Mα₀ through (3.35) (the reduction of p.408 l.3–4, (3.131), the factors Δ^{(2)} of p.422) is read here with c_uMα₀, c_u = O(1)L³, at the index j, and with O(1)L⁵Mα₀ at the index j + 1. α₀ is fixed after L and M, so the smallness conditions that contain these products keep their form as upper bounds on α₀.
    - {#W7.10} The shell sums of §5(c).
      {#W7.10-1} For an intersected sequence, blocks of □ and points of supp h_□ can lie in the local shell j − 1, and there is no shell j + 1.
      {#W7.10-2} §5(c)'s sum over the shells then has the term ϖ_{j−1} = L^β(ε/a_j)^β, and the count of crossed shells is one smaller, so the constant 3 + L^β + L^{1+β}/(L − 1) takes a factor ≤ L^{1+β} at these cubes (at most L^β by a direct count: the shells j − 1 and j give (1 + L^β)L^{−βj}, the shells 1 to j − 2 give L^{1+2β}L^{−βj}/(L − 1), the shell 0 at most L^{2β}L^{−βj}, and the extra shell at most L^βL^{−βj}).
      {#W7.10-3} §5(c)'s c_β is defined with this factor, so C_□(β) carries it.
    - {#W7.11} The cells.
      {#W7.11-1} For 𝒟″'s cube □″ with j_Q = j (the first case, Q̃ = □̃⁵), Q's sequence is intersected in the same way when Q̃ meets Ω_j^c: Ω′_n(Q) := Ω_n(Q) ∩ Ω_n for n ≤ j, and Ω′_{j+1}(Q) := ∅.
      {#W7.11-2} Q̃, Q̃³, and Q̃⁵ extend □ by 5ML^jη, 7ML^jη, and 9ML^jη (p_Q = □̃²), so Q̃⁵ lies within the ℓ¹ distance 10dML^jη of □'s big block, hence in Ω_{j−1}, and if Q̃ meets Ω_j^c, then Q̃³, of the side 16ML^jη, misses Ω_{j+1} (16d < 12dL).
      {#W7.11-3} Ω_n(Q) ⊇ Q̃⁴ ⊇ Q̃ for n ≤ j, so the agreement on Q̃, PRT2 (2.1)–(2.4), and Corollary 3.6 (Ω′_0(Q) ⊂ Q̃⁵, the index j, α₁ = O(1)L³Mα₀) follow as for □.
      {#W7.11-4} If Q̃ ⊂ Ω_j, Q's sequence is not intersected, and Q̃ ∩ Ω_{j+2} = ∅ since Q̃ lies within the ℓ¹ distance 6dML^jη of □'s big block.
      {#W7.11-5} The cells with j_Q = j + 1 have Q̃ ⊂ Ω_j (*Agreement.* below) and are not intersected.
  - {#W7.12} In the second case, □₀ = □̃₁² with □₁ ∈ 𝒟_{j+1} (p.411 l.24–25), and for 𝒟″'s cube □̃₀² with "the boundary conditions outside □̃₀⁵" (p.415 l.9; in terms of □ the print gives □̃⁸, where the sizes of p.408 l.23–24 give □̃⁷ for □₀ = □̃²; neither is used here), PBG does not write the sequences out.
    {#W7.12-1} They are constructed here, a choice made in both runs.
    {#W7.12-2} The sequence of p.408 at □₀'s own layer j + 1 would not do: it assigns the scale j + 1 to the layer-j blocks of □, so the operators of □ and □₀ would differ inside □̃.
    {#W7.12-3} Let Q be □₀ (second case) or 𝒟″'s cube □″ := □̃₀² (either case), and p_Q the cube that Q replaces: □₁ for □₀ (p.411 l.24–25) and □₀ for □″ (p.415 l.8).
    {#W7.12-4} Let j_Q be the coarsest layer among p_Q and the cubes removed for Q (those meeting □̃₁, p.411 l.24–25, or □̃₀, p.415 l.8), and Q̃^n the cube that extends p_Q by (n + 2)ML^{j_Q}η.
    {#W7.12-5} So Q̃^n = □̃₁^{n+2} for □₀, and Q̃^n = □̃₀^{n+2} for □″ when j_Q is □₀'s scale, as on p.408 l.23–24. j ≤ j_Q ≤ j + 1: a cube of 𝒟_{j+2} has a big block in Ω_{j+2} and the side 2ML^{j+2}η, while □̃₁ and □̃₀, which the removed cubes meet, lie within the ℓ¹ distance (8 + 2/L)dML^{j+1}η of □'s big block in B^j(Λ_j), outside Ω_{j+1}, and dist(Ω_{j+1}^c, Ω_{j+2}) > RML^{j+1}η ≥ (8d + 2d/L + 2dL)ML^{j+1}η under R ≥ 12dL and L ≥ 4 (PRT2 (2.2)).
    {#W7.12-6} Q's sequence is p.408's recipe at the layer j of □, centred at p_Q: Ω_{j+1}(Q) := Q̃³ ∩ B^{j+1}(Λ_{j+1}), Ω_j(Q) := Q̃⁴, and, for n < j, the cubes Ω_n(Q) centred at p_Q with dist(Ω_n(Q)^c, Ω_{n+1}(Q)) = 2R₀M₀L^nη, so that Ω₀(Q) ⊂ Q̃⁵ as on p.408 l.30–35.
    {#W7.12-7} This construction and the items below are for the cells in the bulk, those whose cubes □̃⁵ and Q̃⁵ lie in global layers that PRT2 (2.2) separates with R ≥ 12dL.
    {#W7.12-8} On the collar of 𝐁₁, whose layers are only about L big blocks of their scale wide (§12, *The collar's layers.*), a cube of 𝒟_{j+2} can meet □̃₁, and the cells whose □̃⁵ or Q̃⁵ meets a collar layer are built on restricted sequences (§12, *The cells of 𝒟′ and 𝒟″ on the collar.*).
    - {#W7.12-9-0} Agreement.
    {#W7.12-9} Let Ω_n be the global domains.
    {#W7.12-10} If j_Q = j, then Q = □″ in the first case with Q̃ = □̃⁵, and Q's sequence agrees with the global one on Q̃ by the item *The cells.* of *The cubes next to the finer layer.* Otherwise j_Q = j + 1, and a cube of 𝒟_{j+1} (□₁, or one removed for □″) meets □̃₁ or □̃₀; Q̃ (□̃₁³ for □₀; □̃₁⁵, or □₀ extended by 3ML^{j+1}η, for □″) lies within the sup distance 8ML^{j+1}η, so within the ℓ¹ distance 8dML^{j+1}η, both of that cube's big block in B^{j+1}(Λ_{j+1}) ⊂ Ω_{j+1} and of □'s big block in B^j(Λ_j), which lies outside Ω_{j+1} (B^j(Λ_j) ∩ Ω_{j+1} = ∅ by PRT2 (2.3)).
    {#W7.12-11} Since dist(Ω_j^c, Ω_{j+1}) > RML^jη and dist(Ω_{j+1}^c, Ω_{j+2}) > RML^{j+1}η (PRT2 (2.2)), R ≥ 8dL gives Q̃ ⊂ Ω_j and Q̃ ∩ Ω_{j+2} = ∅.
    {#W7.12-12} Hence Ω_n(Q) ∩ Q̃ = Ω_n ∩ Q̃ for every n: both contain Q̃ for n ≤ j, Ω_{j+1}(Q) ∩ Q̃ = Ω_{j+1} ∩ Q̃ since Q̃ ⊂ Q̃³, and both are empty on Q̃ for n ≥ j + 2.
    {#W7.12-13} Q̃ contains supp h′_Q with the margin (1/6)ML^{j_Q}η ≥ L^{j+1}η (*G′² is a composition* below, the construction of the partitions), which the stencils of the averagings need, so the local identity (3.88) holds for Q's operator.
    {#W7.12-14} Q̃ also contains □̃³.
    {#W7.12-15} For □₀ (second case), Q̃ = □̃₁³, and the points of □̃³ lie within 6ML^jη ≤ 3ML^{j+1}η of □₁, which meets □̃.
    {#W7.12-16} For □″, Q̃ extends p_Q = □₀ by 3ML^{j_Q}η ≥ 3ML^jη.
    {#W7.12-17} In the first case □₀ = □̃², so Q̃ ⊇ □̃⁵.
    {#W7.12-18} In the second case j_Q = j + 1 and Q̃ = □̃₁⁵ ⊇ □̃₁³ ⊇ □̃³.
    {#W7.12-19} On □̃³, □'s own sequence agrees with the global one (*The cubes next to the finer layer.*).
    {#W7.12-20} So the sequences of □ and Q agree on □̃³, the two operators differ only outside □̃³, at the distance ≥ 2M from □̃ on the scale L^jη, and the factor of (3.97) and of p.415 is at most e^{−2δ₀M}, as PBG states (p.412 l.27–29, p.415 l.18–19).
    - {#W7.13} PRT2 (2.1)–(2.4) at the size R₀M₀ ((2.3)–(2.4) are definitions).
      {#W7.13-1} The shells n < j have the width 2R₀M₀L^nη by construction.
      {#W7.13-2} The innermost shell Q̃⁴ ∖ Ω_{j+1}(Q) has the width ≥ ML^{j_Q}η ≥ 2R₀M₀L^jη, by K ≥ 2 in M = KR₀M₀, as for p.408's sequence (10.3).
      {#W7.13-3} PBG prints only that K is a positive integer (p.408 l.28).
      {#W7.13-4} K ≥ 2 is imposed here, and §8 lists K ≥ 4, which §12 uses.
      {#W7.13-5} The domains are unions of big blocks of their scales, and the sequence satisfies PRT2 (2.1)–(2.2) rescaled to the L^{−j}-lattice, as p.408 l.34 states for □'s sequence.
      {#W7.13-6} So (2.58)–(2.60), the separation of the innermost shell (10.3), and the margin of (S) hold as for □'s sequence.
    - {#W7.14} Corollary 3.6.
      {#W7.14-1} Ω₀(Q) ⊂ Q̃⁵, a cube of at most 20 big blocks of the scale j_Q.
      {#W7.14-2} Corollary 3.6's proof uses only (3.35) on a cube containing Ω₀, through the gauge transformation u and Corollary 3.5 (p.408 l.1–9), and (3.37) for the sequence then needs |A| < α₁(L^nη)^{−1} and |∇A| < α₁(L^nη)^{−2} on Ω_n(Q) for n ≤ j + 1 (p.396), so at the coarsest index j + 1 of the sequence.
      {#W7.14-3} (3.35) holds on Q̃⁵ at the index j_Q, with O(1)L²Mα₀ for |A| and O(1)L³Mα₀ for |∇A|, by the axial-gauge argument of §11 for its 16-block cubes (*Complex s*, the bullet *So the telescoping holds term by term*), with R ≥ 12dL in place of 8dL: Q̃⁵ lies within the ℓ¹ distance 12dML^{j_Q}η of a big block of Ω_{j_Q} (that of the cube of 𝒟_{j+1} in the agreement item, or □'s for j_Q = j), so it lies in Ω_{j_Q−1}, where the curvature bounds hold at the scale j_Q − 1 or coarser.
      {#W7.14-4} The case j_Q = 0 does not occur in the bulk.
      {#W7.14-5} The cells of §7 are bulk cells, where the global finest domains are the whole lattice (the LF note's #1.1, Ω_i = T for i < j₀, with j₀ ≥ 2 there, so Ω₁ = T), and ∂Ω is treated in §12.
      {#W7.14-6} So the layer 0, T₁ ∖ Ω₁ (p.408 l.22), is empty, 𝒟₀ has no cubes, and j_Q ≥ j ≥ 1.
      {#W7.14-7} PBG's restriction of (3.35) to its Ω₀ (p.396 l.33) is therefore moot here, and the class of p.396 l.14–17 is not used.
      {#W7.14-8} For j_Q = j + 1 the index needs no shift, and α₁ = O(1)L³Mα₀.
      {#W7.14-9} For j_Q = j (𝒟″'s cube in the first case) the shift from the index j to j + 1 costs L for |A| and L² for |∇A|, so α₁ = O(1)L⁵Mα₀; when Q's sequence is intersected (*The cubes next to the finer layer.*), its coarsest index is j, and no shift is needed.
      {#W7.14-10} The smallness is O(1)L⁵Mα₀ ≤ a₁, an upper bound on α₀ imposed after L and M. R ≥ 12dL and this smallness are among §8's conditions.
    {#W7.15} So the bounds that PBG states for these propagators (p.412 l.25–28, p.411 l.28–30) hold for this choice, and the defect derivations of §5(c), 10.1, and 10.3 apply to Q's sequence as to □'s.
  - {#W7.16} G′² is a composition: with def(G′) := χ_AQ′₁G′^B − G′^Aχ_AQ′₁ in the form of §4(d), χ_AQ′₁(G′^B)² − (G′^A)²χ_AQ′₁ = def(G′)G′^B + G′^A def(G′), so its defect is at most 2c_∘C_□(β)(ε/a_j)^β times the usual factors, with c_∘ the count and rate constant of one composition ((Comp) of 10.3).
    {#W7.16-1} So, relative to the factor's bound, the defect of a difference is at most 8δ₀Mc_∘C_□(β)(ε/a_j)^β. h′_{□₀} − ζ_{□̃} is the multiplication by a function f with |f| ≤ 1, treated as h above with |∂^kf| ≤ |∂^kh′_{□₀}| + |∂^kζ_{□̃}|.
    {#W7.16-2} The commutators reduce to the factors of 10.4 and above: [G′, f] = G′K′(f)G′ with K′(f) = [f, Δ′_a] for f = h′²_{□₀} and ζ_{□̃}, and [ζ, C_□] = C_□[Q′G′²_□Q′*, ζ]C_□ with [Q′G′²Q′*, ζ] = [Q′, ζ]G′²Q′* + Q′(G′[G′, ζ] + [G′, ζ]G′)Q′* + Q′G′²[Q′*, ζ], ζ multiplying data and fine fields as the same function of the point.
    {#W7.16-3} So they are sums of products of local constituents with the factors K′(f), [f, Q′], and [Q′*, f], whose defects are those of 10.4 with Lc_h* in place of c_h and those of the scalar averaging commutators with c_h* in place of c_h.
    {#W7.16-4} The factor L: 10.4 reads ℓ_n|∂h| ≤ c_hL/M at the shells n ≤ j_c + 1 of the cube of the layer j_c that carries f, and cubes of 𝒟, 𝒟′, and 𝒟″ that meet lie in adjacent global layers (PRT2 (2.2), as in the agreement above), so j(f) ≥ j_c − 1 and ℓ_n|∂f| ≤ c_h*L^{n−j(f)}/M ≤ Lc_h*·L/M. 10.4 also uses ℓ_n²|∂²h| ≤ c_hL/M and the factor 1 + 3L/M of C_Q, which come from the second and third derivatives under M ≥ L. For f they become ℓ_n²|∂²f| ≤ c_h*L⁴/M² ≤ Lc_h*·L/M, under M ≥ L², and the factor 1 + 3L²/M, which §8's C_w carries.
    {#W7.16-5} On the collar the factor L is obtained pointwise (§12, *The cells of 𝒟′ and 𝒟″ on the collar.*).
    {#W7.16-6} Here c_h* is the largest of the constants c with |∂^kf| ≤ c(Mℓ_{j(f)})^{−k}, k ≤ 3, for f = h_□ (□ ∈ 𝒟), h′_□ (□ ∈ 𝒟′ or 𝒟″), h′²_{□₀}, ζ_{□̃}, and h′_{□₀} − ζ_{□̃}, with ℓ_{j(f)} the scale L^{j(f)}η of the finest layer j(f) among f's cube and the cubes of its partition that meet it (for h′²_{□₀} and h′_{□₀} − ζ_{□̃}, the finest among those of h′_{□₀} and of □).
    {#W7.16-7} The cubes that meet f's cube lie in the enlargement X̃_i⁵ of the localisation X_i of the factor that carries f, so j(f) ≥ m(ω), and the relative defects at the layer j(f) are bounded by their values at m(ω).
    {#W7.16-8} The partitions of unity {h′_□} of 𝒟′ and 𝒟″ are "the corresponding partition of unity" (p.411 l.25–26) of these partitions, with h′_{□₀} = 1 on □̃ "by the construction of the partition 𝒟′" (p.412 l.12).
    {#W7.16-9} PBG does not write them out.
    {#W7.16-10} They are constructed here, a choice made in both runs.
    {#W7.16-11} The partition of 𝒟 is built from PRT1's (1.118) function h, rescaled to each cube (PRT2 p.229 l.12), and normalised so that PRT2's (2.36) holds where layers meet. For □ ∈ 𝒟_{j′} with centre y put φ_□(x) := Π_μh((x_μ − y_μ)/(ML^{j′}η)) for x ∈ ℝ^d, N_𝒟 := (Σ_{□′∈𝒟}φ_{□′}²)^{1/2}, and h_□ := φ_□/N_𝒟.
    {#W7.16-11-1} N_𝒟 ≥ 1 on ℝ^d. The sets B^i(Λ_i) are unions of big blocks that partition T (p.408 l.19–22), so x lies in a closed big block b ⊂ B^i(Λ_i) of some scale i. The nonzero terms of Σ_zh_z(x)² = 1 of (1.118) at the scale i have |x_μ − z_μ| < (2/3)ML^iη for every μ, so z is a vertex of b; the cube of 2^d big blocks centred at a vertex of b contains b, so it lies in 𝒟_i (p.408 l.19–21). So the scale i alone gives N_𝒟(x)² ≥ 1.
    {#W7.16-11-2} Hence Σ_□h_□² = 1, 0 ≤ h_□ ≤ φ_□ ≤ 1 (h takes values in [0, 1], #W7.22-2), and supp h_□ = supp φ_□ lies within the sup distance (2/3)ML^{j′}η of y.
    {#W7.16-11-3} At a point of supp φ_□, the cubes □′ with φ_{□′} ≠ 0 meet □, at most 2^d of them at each scale i, and |∂^kφ_{□′}²| ≤ c_k(ML^iη)^{−k}. The sum over the scales i ≥ j(h_□) gives |∂^kN_𝒟²| ≤ 2^{d+1}c_k(Mℓ_{j(h_□)})^{−k}, and with N_𝒟 ≥ 1, |∂^kh_□| ≤ c(Mℓ_{j(h_□)})^{−k} for k ≤ 3, j(h_□) as in #W7.16-6 and c a constant of h and d.
    {#W7.16-11-4} Each h_□ is a function on ℝ^d determined by h and the cubes of 𝒟.
    {#W7.16-12} If the cubes removed at p.411 l.23–25 are dropped and the others keep their h_□, then Σ_kept h_□² = 1 outside the union S of the supports of the removed h_□.
    - {#W7.17} Let j₀ be the scale of □₀ (j in the first case, j + 1 in the second) and p the cube □ (first case) or □₁ (second case).
      {#W7.17-1} Let φ be a fixed profile with values in [0, 1], rescaled to the scale ML^{j₀}η, equal to 1 within the sup distance (8/3)ML^{j₀}η of p, supported within (17/6)ML^{j₀}η of p, with transitions of the width (1/6)ML^{j₀}η.
    - {#W7.18} φ = 1 on S and on □̃.
      {#W7.18-1} A removed cube meets □̃ (first case) or □̃₁ (second case) and has the side ≤ 2ML^{j₀}η, so its h_□ is supported within (5/3)ML^{j₀}η of □̃ or □̃₁, that is, within (8/3)ML^{j₀}η of p; and □̃ ⊂ □̃₁ in the second case for L ≥ 4. supp φ lies in Q̃ of the second case (□̃³ for □₀ = □̃², □̃₁³ for □̃₁²) with the margin (1/6)ML^{j₀}η ≥ L^{j+1}η for M ≥ 6L.
    - {#W7.19} Put N_{□₀} := (φ² + Σ_kept h_□²)^{1/2}, h′_{□₀} := φ/N_{□₀}, and h′_□ := h_□/N_{□₀} for the kept cubes.
      {#W7.19-1} Then 1 ≤ N_{□₀}² ≤ 2, since Σ_kept h_□² = 1 off S and φ = 1 on S. So Σh′_□² = 1, the h′_□ take values in [0, 1], and the partition coincides with 𝒟's off supp φ. h′_{□₀} = 1 on □̃, since the kept cubes do not meet □̃, so their h_□ vanish there.
      {#W7.19-2} Each h′_□ is a polynomial in φ, the h_□, and N_{□₀}^{−1}, with N_{□₀} ∈ [1, √2].
      {#W7.19-3} So |∂^kh′_□| ≤ c(Mℓ_{j′})^{−k}, k ≤ 3, with j′ the finest layer among its cube, the cubes of its partition that meet it, and □₀, and c a constant of PRT1's h and φ's profile.
      {#W7.19-4} This holds in the mixed-layer case as well.
    - {#W7.20} 𝒟″'s partition is built in the same way: □″ in place of □₀, □₀ in place of p, the cubes of 𝒟′ removed at p.415 l.8 (those meeting □̃₀) in place of those of p.411, and the scale j_Q of the second case in place of j₀.
      {#W7.20-1} The removed supports lie within ML^{j₀}η + (5/3)ML^{j_Q}η ≤ (8/3)ML^{j_Q}η of □₀, and supp φ within (17/6)ML^{j_Q}η of □₀, inside Q̃ with the margin (1/6)ML^{j_Q}η.
    - {#W7.21} PBG uses the factors K(h′_□)G′_□h′_□ of these expansions with the bound (3.89) (p.411 l.28), whose factor O(M^{−1}) comes from these derivative bounds.
    {#W7.22} What the bounds use is that each h′_□ takes values in [0, 1] and satisfies these derivative bounds.
    {#W7.22-1} PBG defines ζ_{□̃} "similarly to h_□" (p.414 l.46–47), with ζ = 1 on a cube whose boundary is at distance ≥ (2/3)M from ∂□ and supp ζ ⊂ □̃, which extends M beyond □ (p.408 l.23–24), so its transition band has width ≤ M/3 on the scale L^jη. ζ_{□̃} is chosen as a fixed profile with values in [0, 1], rescaled to □̃, with its transition band of width M/6.
    {#W7.22-2} PRT1's h is taken with values in [0, 1].
    {#W7.22-3} This is a choice within (1.118): h(t) := cos(½πψ(|t|)) for 1/3 ≤ |t| ≤ 2/3, h := 1 for |t| ≤ 1/3 and 0 for |t| ≥ 2/3, with ψ smooth on [1/3, 2/3] with values in [0, 1], 0 near 1/3, 1 near 2/3, and ψ(t) + ψ(1 − t) = 1, lies in C₀^∞(]−2/3, 2/3[), and for 1/3 ≤ t ≤ 2/3, h²(t) + h²(t − 1) = cos²(½πψ(t)) + sin²(½πψ(t)) = 1, while on [0, 1/3] only h(t) = 1 is nonzero among the h(t − n).
    {#W7.22-4} So the h′ take values in [0, 1], and c_h* is a fixed constant of ζ's profile, φ's profile, and PRT1's h, with |h′_{□₀} − ζ_{□̃}| ≤ 1.
- {#W7.23} *Telescoping.* Q₁W^B_ω − W^A_ω𝒥 is a sum, over the constituents c of the walk term, of the product with run A's constituents to the left of c, the intertwining defect of c, and run B's constituents to the right, with Q₁, ℒ*, or the identity between constituents according to the slot (fine field, fine source, or data).
  {#W7.23-1} There are at most N_c(|ω| + 1) such terms.
  {#W7.23-2} Suppose that each defect satisfies the bounds of its constituent times 𝔡_c (the LF note's δ_c; here 𝔡_c, since δ_c is a rate in 10.5), at the rate δ₀/3 of §5(c).
  {#W7.23-3} Then PBG's proof of (3.94) and (3.108) applies to each term: it inserts the localisations Δ(y_i), bounds each factor, and sums over the y_i with half of each exponential (p.410 l.13–30).
  {#W7.23-4} So each term is ≤ 𝔡_c times the bound (3.108) with the rate δ₀/6 in place of ½δ₀.
  {#W7.23-5} Once C_□ enters at δ₀/27 (10.3) and G_□ at δ_gf′/3 (10.4), the rate is at least δ₀′/54, since δ_gf′/6 = min(δ₀/2916, δ₀′/6) ≥ δ₀′/54 by δ₀′ ≤ δ₀/64, which is used below as a common lower bound.
  {#W7.23-6} The walk term's difference is ≤ N_c(|ω| + 1)max_c𝔡_c(1 + max_c𝔡_c)^{N_c(|ω|+1)−1} times that bound, the last factor from the mixed terms, in which run B's constituents carry their bound times 1 + 𝔡_c.
  {#W7.23-7} For N_cmax_c𝔡_c ≤ log(3/2) this is ≤ 3·2^{|ω|}N_cmax_c𝔡_c times that bound (the LF note's (iii)).
  {#W7.23-8} Otherwise N_cmax_c𝔡_c > log(3/2) > 2/5, and the two sides are bounded separately: Q₁W^B_ω by c₁ times that bound and W^A_ω𝒥 by c₂ times it, with c₁ := 3 ≥ w_Q, the total weight of Q₁ at complex backgrounds (10.4, *The two commutators with Q₁ at the local entries.*) and c₂ the constant of the slot map 𝒥 (1 on data, C_ℒ′ for 𝒥 = ℒ* on sources, 10.1).
  {#W7.23-9} For the form (c), c₁ := 1 and c₂ is the product of the constants of ℒ_ι and 𝒥′ = ℒ_ι* in the norms of (3.108) (10.5, (H_ℒ)).
  {#W7.23-10} The sum c₁ + c₂ is ≤ (5/2)(c₁ + c₂)N_cmax_c𝔡_c.
  {#W7.23-11} So the walk term's difference is ≤ C_tel2^{|ω|}N_cmax_c𝔡_c times that bound, C_tel := max(3, (5/2)(c₁ + c₂)), a constant of d, L, and the lift constants, with no smallness condition on the defects in the telescoping; this matters at the finest layers, where ε/a_j is not small against the factor M of the commutator factors (10.4).
  {#W7.23-12} This is the per-walk-term form (b), and the same argument with ℒ_ι gives (c).
- {#W7.24} *The absorption.* (|ω| + 1) ≤ 2^{|ω|}, so the factor O(M₁^{−1/2})^{|ω|} of (1.7) becomes (2O(M₁^{−1/2}))^{|ω|}.
  {#W7.24-1} These factors "are used to control the sum over ω, and they determine the constant B₀" (RG II p.3 l.23–24).
  {#W7.24-2} So the sum converges for M₁ four times Bałaban's lower bound, with B₀′, the constant B₀ with the doubled factor, in place of B₀.
  {#W7.24-3} For the composite walks of §11, whose series-level groups carry no factor M₁^{−1/2}, the doubling is kept inside their constituent walks, and the series-level groups are paid by the per-group factor of (J) (§11, *The junction sums.*).
- {#W7.25} *The bound (1.11).* Bałaban's argument (p.5 l.13–16) uses δ₀d(ω) ≥ δ₁mM for m > 2⁴, with δ₁ depending on δ₀ only, and δ₁M ≥ κ₁.
  {#W7.25-1} At the rate δ₀/6 this needs (W-M) δ₁(δ₀/6)M ≥ κ₁, a condition on M. The rates δ₀/6 here and δ₀′/54 after 10.3 are those of the local constituents G′_□, C_□, and G_{a,□}, in the metric of the cube's own sequence; in PRT2's global distance they are divided by L (§11, *The condition on M.*, the definition of δ_min).
  {#W7.25-2} So (W-M) is read at the global rate δ₀′/(54L), with RG II's δ₁ linear in the rate.
  {#W7.25-3} §11's condition M ≥ 4κ₁/(ρδ_g) implies (W-M), since δ_min ≤ δ₀′/(54L) and δ_g ≤ δ₁.
  {#W7.25-4} Then on |s(Δ)| ≤ e^{κ₁}, |(Q₁H^B(s) − H^A(s))X| ≤ C_telδ_w(Y)B₀′e^{16κ₁}|X|, with δ_w(Y) the supremum of N_cmax_c𝔡_c over the walks in Y, as the LF note's δ_w(ω) := N_cmax_cδ_c.
  {#W7.25-5} The same holds for G̃(s), H₀(s), and the fine form (c), with the composites' constants below.
  {#W7.25-6} This is the inequality of the LF note's (iii), the telescoping over N_c(|ω| + 1) constituents, with N_c and B₀′ in place of 2 and B₀.
  {#W7.25-7} It holds as stated for the walks of G and G′, PBG's base walks.
  {#W7.25-8} H₀ = G_aQ*(QG_aQ*)^{−1} (VAR (129), p.297 l.35–38) contains the inverse (QG_aQ*)^{−1}, which PBG does not expand (p.422 l.15–16); its local inverses (QG_{a,□}Q*)^{−1} are the base inverse of §11, with the constant 2C_D and the rate ½δ_D′, and their defect is the block identity of §11 (*The defect of D_□.*) with G_{a,□} in place of G_□, at the rate δ_D′/6.
  {#W7.25-9} So H₀(s), H(s), and G̃(s) are composites (§11): for them it holds with B_T for B₀′, the rate δ_min, e^{2·6^dκ₁} for e^{16κ₁}, and §11's condition M ≥ 4κ₁/(ρδ_g) in place of (W-M) (§11, *The condition on M.*).
  {#W7.25-10} A walk in Y meets only the layers of Y, so m(ω) ≥ m(Y) and (ε/a_{m(ω)})^{γ} ≤ (ε/a_{m(Y)})^{γ}.

## 8. The Bound (W-δ) and the Conditions on the Constants {#WS8}

{#W8.1} By (Wδ-1) (§5, §10), (Wδ-2) (10.5), and (Wδ-3) (§11), §§4–7 give the fine per-walk-term form (c), and with it (b), with

  {#W8.2} δ_w(ω) ≤ C_w(ε/a_{m(ω)})^{γ_w}, γ_w := min(β, (1 − ε₀)/3), C_w := N_c[(1 + 8δ₀Mc_∘)C_□(β) + 3(2d + 1)c_h*(1 + C_ℒ′m_Q)/M + 8dc_K^{−1}c_h* + c_K^{−1}MC_{[h]}(β)] + 4C_U(M)ε₁/α_*′ + C_w^{(11–12)},

{#W8.3} where β < 1 is the Hölder exponent at which (Wδ-1) holds, C_□(β) is the largest of the constants of the local propagators G′_□ and G_□ (§5(c), 10.1) and of C_□ (10.3), and 8δ₀Mc_∘C_□(β) bounds the relative defects of the differences of (3.97) and p.415 (§7).
{#W8.3-1} C_{[h]}(β) is the constant of the commutator factors (10.4, *The commutator factors K(h), P_{□,1}(∂h), and S_j(∂h)*), with Lc_h* for c_h and 1 + 3L²/M for the factor 1 + 3L/M of C_Q (§7); 3(2d + 1)c_h*(1 + C_ℒ′m_Q)/M bounds the relative defect of the multiplications, and 8dc_K^{−1}c_h* that of the scalar averaging commutators [f, Q′] and [Q′*, f] (§7); m(ω) is the finest global layer that ∪X̃_i⁵ meets.

{#W8.4} C_w^{(11–12)} collects the enlargements that §§11–12 state for their own terms:

  {#W8.5} C_w^{(11–12)} := O(1)(C(ε₀) + C₀′/C₀) + O(1)(1 + C_ℒ)L¹¹ + (1 + C_ℒ)L^{h₀}.

- {#W8.6} O(1)C(ε₀) is the run difference of the currents, ∇b₁ in divergence form, at U^B (§11, *The term G̃Δ^{(2)}H₀B*, second bullet).
  {#W8.6-1} O(1)C₀′/C₀ is the same term at the pairs of 𝐇″_k (§12, *§11's oscillation at U_{1,2}*), with C₀′ε₁ := K_ℬ(C₀ + C(ε₀))ε₁ + C_ℬC(β₂)ε₂ of its bootstrap.
  {#W8.6-2} By ε₂ ≤ B₁(O(1)B₃³B₅M⁶ε_k + C₁ε₁) (§12, *The band regularity of U_{1,2}*), C₀′/C₀ ≤ K_ℬ(1 + C(ε₀)/C₀) + C_ℬC(β₂)B₁(O(1)B₃³B₅M⁶ + C₁)/C₀ under ε_k ≤ ε₁, K_ℬ the bootstrap's constant of d, L, δ₁, and δ_ι (#W12.77-1).
  {#W8.6-3} The ε₁ of ε₂'s bound is U_{1,2}'s membership parameter, the larger of the data bound over C₁ and U_i's data bounds ε_U^{(i)}; with C₁ = L³ ≥ 1 and ε_U^{(i)} ≤ O(1)B₃²B₅M⁶ε_k (§12, *The band regularity of U_{1,2}.*), it is at most V₀'s data parameter, the ε₁ of C₀′ε₁, with the O(1)s taken equal. ε_k ≤ ε₁ is among the conditions below.
  {#W8.6-4} It holds since the ε₁ of (9.2) there is the data parameter of V₀'s problem, O(1)B₃²B₅M⁶ε_k (§12, *§11's oscillation at U_{1,2}*), an upper bound that is taken ≥ ε_k.
- {#W8.7} O(1)(1 + C_ℒ)L¹¹ is the walk terms that meet the strip Ω ∖ Ω^A_2 (§12, *The strip*, *The bound.*) and those that meet the finest-scale strips of the sets 𝐁(Y_i) (#W12.254-6).
- {#W8.8} (1 + C_ℒ)L^{h₀} is the strip terms at the finitely many h ≤ h₀ (§12, *The strip* and *The representation with the gain*), with h₀ the least integer such that L^{h₀} > max(2M₁/M, L(d + 1)).

{#W8.10} For the composites of §11 (𝐇_k(s), G̃(s), and H₀(s)), C_w carries in addition the factor S_δ^{r₀} (§11, *Complex s*), and for 𝐇_k(s) the constant is C_𝔡B₀′(β′) (below).

{#W8.11} In §§7–8 and 10, M without an index is PBG's block size KR₀M₀, which §§11–12 write M₁.
{#W8.11-1} In C_U(M), in (W-M), and in the conditions on M of §§11–12 (M ≥ 4κ₁/(ρδ_g), M ≥ 16N_DM₁, M ≥ 4M₁), and in §12's ε₁ bounds O(1)B₃²B₅M⁶ε_k and B₅M⁵ε_k below and the ε₂ bound O(1)B₃³B₅M⁶ε_k of C₀′ and C₀ in C_w^{(11–12)}, M is RG II's cube size.
{#W8.11-2} The letter K is PBG's integer in M = KR₀M₀ in §§7–8 and in §12's collar cells, the LF note's final scale K = k_s + j(C) where it is named so, and CRE's integer in M₁ = KM′ in §12's *The band regularity of U_{1,2}* (its block size, contraction, and chains), and K := B₀(C₄ + 4C₂)(36dL²B₁)², the coefficient of VAR's (165) (VAR p.304 l.17–19, printed with the factor (R₁M₁)²(M′ε₀)², where VAR's M′ = M/(R₁M₁) equals 1 for the cubes of size R₁M₁) in θ and in the condition 4KM′²B₃ε_U^{(i)} ≤ ½L^{−3}, whose M′ is the block size M′ = R₁M₁ of the notes, not VAR's ratio.
{#W8.11-3} At #W12.28-9 K also names CRE's integer in "K > 4d", as in CRE's M₁ = KM′.
{#W8.11-4} The constant of §12's bootstrap in *§11's oscillation at U_{1,2}* is written K_ℬ; it depends only on d, L, δ₁, and δ_ι.
{#W8.11-5} R₁M₁ is everywhere the product of VAR and REG (VAR's M₁ at p.277 l.12, its R ≥ R₁ at l.17), also in C₀ = 4R₁M₁(B₃ + B₄(1)) and in M(ε₁) = R₁M₁a₁/ε₁.
{#W8.11-6} In the conventions of BP_JOINS_BLOCK_SIZE #4.22–#4.26-2, PBG's cubes are taken at the size M′, VAR's cube parameter R₁M₁ is M′, and the global layers are R′M′ wide in the units of their scale, R′ = LK − 1 with CRE's K. So PBG's block size, written M in §§7–8 and 10 and M₁ in §§11–12, is M′ = R₁M₁, and R ≥ 12dL reads R′ ≥ 12dL, that is CRE's K ≥ 12d + 1.
{#W8.11-7} M₁ alone is PBG's block size M′, except in M₁ = KM′, in §11's passage on the collar (from "The collar lies within 2M₁a_h"), in §12's collar widths, in the conditions M ≥ 4M₁, M ≥ 2dM₁, and M ≥ 2(d + 1)L²M₁, in the (J-W) clause at the width R′M′ ≥ ½LM₁ and its M₁ ≥ 2M_J(d, L) (LF #4.24 and #4.29), and in the distance M₁a_k from Y to (Y^∼)^c (10.5's *The inclusion.*, §11's bridge, §12's localisation χ, and §12's *The lift's R_ι.*; Y^∼ is the LF note's operation ∼ for CRE's M₁-cubes, LF #4.329), where it is CRE's M₁ = KM′ ≥ M′.
{#W8.11-8} Using M′ in place of CRE's M₁ is conservative only for the distances M₁a_k, which are lower bounds on distances; the lower bounds on M and the collar widths are taken at CRE's M₁.
{#W8.11-9} ε₀ is the exponent in γ_w and C(ε₀), except in §11's comparison with VAR, where VAR's ε₀ = α₀ (VAR p.280 l.51–52) is named as VAR's, and in §12's *The band regularity of U_{1,2}.*, where ε₀ is VAR's bound (2) and contains no exponent, and in §12's *No loop through M*, where CRE's δ₀ = (A₁/A₀)ε₀ (CRE p.247 l.50) is quoted with CRE's ε₀ and δ₀.
{#W8.11-10} In §12's *10.5's premise at 𝐇″_k.* and the field bound of *§11's oscillation at U_{1,2}*, VAR's 𝔘-parameter of (19) is written ε₀^𝔘, since the exponent ε₀ occurs there too. a₁ in O(1)L⁵Mα₀ ≤ a₁/2, α₁^A ≤ a₁/2, and B₅ε₁ ≤ a₁/2 is PBG's threshold of Corollary 3.5 and Theorem 3.4; in ε₁ ≤ a₁/7, ε₁ ≤ a₁/(3L), and M(ε₁) it is VAR's threshold of Theorem 1.
{#W8.11-11} C_w is a constant of PBG's block size, CRE's M₁ = KM′ (through the factor C_ιe^{δ_ι(R_ι/L + 2)M₁} of C(ε₀), #W12.42-6 and #W12.43), RG II's cube size, β, β₂, β′, ε₀, ε₁, L, d, and Bałaban's constants.
{#W8.11-12} Each ε₁ in C_w is taken at a bound independent of k.
{#W8.11-13} The ε₁ of §12 is O(1)B₃²B₅M⁶ε_k (*The background pairs.*) or B₅M⁵ε_k (*The collar of 𝐁₁.*, its bullet on the gain at the scale k, VAR (7) for U_{k,Λ}), and ε_k = ĝ_kp₀(ĝ_k) ≤ g_kp₀(g_k) = A₀g_k(log g_k^{−2})^{p₀} (CRE (2.4) at ĝ_k, Cauchy #CP.13–#CP.14) ≤ Cḡp₀(ḡ), the k-independent bound of the LF note's §1 (*The regularity of the data.*, by CRE (2.4) and (2.6)): g_k ≤ (1 + β₀)ḡ by CRE (2.6), g ↦ gp₀(g) is increasing for small g, and C carries the factor 1 + β₀.
{#W8.11-14} The ε₁ of the LF note's alignment is the larger of that bound and C(M)R_kε_k, with R_k ≤ 2L(log g_k^{−2})^r (the tube's R, Cauchy #CP.14); g ↦ g(log g^{−2})^{p₀+r} is increasing for small g, so C(M)R_kε_k is likewise at most a constant times its value at ḡ.
{#W8.11-15} So C_w does not depend on k, the final scale K = k_s + j(C) of the LF note, ε, or the volume, since every constant above is local, and it depends on PBG's integer K only through PBG's block size.
{#W8.11-17} K ≥ 4 is used in the form K ≥ 2L/(L − 1), and K is taken as a power of L, a choice made in both runs, as PBG takes its sizes as powers of L (p.408 l.26).
{#W8.11-18} With K ≥ 4 > 1 this gives K ≥ L, so the M-blocks of the scale j are unions of R₀M₀-blocks of the scale j + 1, as the coarsest domains Ω_{j+1}(□) = □̃³ ∩ B^{j+1}(Λ_{j+1}) and their analogues for the cells need. γ_w > 1/4 holds if β > 1/4 and ε₀ < 1/4.
{#W8.11-19} For the LF note's (iii), which carries the background change through r(Y) (#W6.6-1), the exponent is β.
{#W8.11-20} The telescoping of the LF note's (iii) holds as derived in §7, through its branch without smallness, with N_c and B₀′ in place of 2 and B₀, the constant C_tel of §7 in place of 3, and the rate δ₀/6 in (1.11), under (W-M).
{#W8.11-21} The telescoping needs no smallness condition on δ_w(ω); the consumer's own smallness, the LF note's C_{Δ𝐇}ϑ_H ≤ 1/6 in (iii), holds for n ≥ n_H(M) there, and below n_H the LF note bounds the difference as a whole.

{#W8.12} *The conditions on the constants.* Each condition is stated and used where its source in parentheses derives it.
{#W8.12-1} The constants are chosen in stages, each after the previous ones: (0) the exponents; (1) L; (2) the rates and constants computed from d, L, G, and Bałaban's constants (δ₀, δ₁, B₀–B₅, δ₀′, δ_c, δ_gf′, δ_D′, δ_ι, δ_min, δ_g, δ_br, δ_br^c, c_u, c_G, r_G, r_υ, and the like; most depend on L, PBG p.397 l.37, VAR p.279 l.28), which depend on none of the later choices; (3) Bałaban's κ (#T3.34), then RG II's κ₁ by its lower bounds in κ and L (½(κ₁ − 1) ≥ 2Lκ, RG II p.20 l.17; #W12.181-1),
{#W8.12-1a} then the sizes, by lower bounds, in the order R₀M₀, then PBG's K, hence M′ = KR₀M₀ (K ≥ 4 a floor; the lower bounds on M′ are met by K large, and no condition on R₀M₀ involves K), then CRE's K with R, whose threshold R_thr is taken at the block size M′ (BP_JOINS_BLOCK_SIZE #4.22-2-1), then RG II's M, each in terms of stages 0–2, κ, κ₁, and the sizes before it, a condition on two sizes, such as δ₁RM₁ ≥ 12 log L, being met at the later one (M′ ≥ R₀M₀, M ≥ 4KM′, and (D2) with C_ι(M′) use earlier sizes);
{#W8.12-2} (4) PBG's α₀ and α₁, by upper bounds, with α_J := Mα₀ (LF #4.60) fixed with α₀; (5) VAR's ε₃, then ε₁, the fixed ε₁ of 10.5, and the fixed ε₁^{(1)} of 10.5's one-step problem at 𝐇″_k, by upper bounds (U_i's data bounds ε_U^{(i)} of §12 are γ-dependent, not fixed); (6) γ small.
{#W8.12-3} RG I's thresholds α₀, α₁, α₂, and α₃ in §12's ratio of (D2) are not PBG's: they are CRE's γ-dependent α̃_{0,k}, α̃_{1,k} = λ_Rα̃_{0,k} (CRE (2.28), p.259 l.45–50), RG I's radius α₂ := c₂α̃_{0,k} of (3.14), and RG I's α₃ := β_IL^{−2}α̃_{0,k}/(2B₃⁺C_{Q*}) of Lemma 4, as in the Cauchy note (its #C5.37-4, with C_{Q*} of its #C5.6-5; the factor 1/C_{Q*} for the reduced current threshold of its norm class, its #C5.28-19 and #C5.37-5), with β_I RG I's class parameter β.
{#W8.12-4} They are homogeneous in α̃_{0,k} and taken at the radii of the run: here Bałaban's thresholds, in the Cauchy and LF notes the radii r of RΔ^c, also when Lemma 4 is run at input radii in [r, r⁺] (the Cauchy note's #C5.15-4, #C5.28-13, and #C8.2.2-3; the LF note's #4.397, #4.458).
{#W8.12-5} The relations among them are fixed by c₂ (stages 2 and 3′) and λ_R (stage 3), and their values enter only at stage 6 (§12, the ratio of (D2)).
{#W8.12-6} VAR's a₀, a₁, and a₅, and with them M(ε₁), depend on R₁M₁ = M′ once VAR's product is raised to M′ (VAR (166), p.304 l.21–26 and l.52–54); they are fixed after stage 3 and enter only upper bounds on α₀ and ε₁, so the order holds.
{#W8.12-7} No condition bounds α₀ or α₁ above by ε₁, ε_k, or ϱ.
{#W8.12-8} VAR's M_V ≤ M(ε₁) = R₁M₁a₁/ε₁ is an upper bound on ε₁. 10.5's ε₁ is a fixed value between the data parameter and a₁, below that upper bound: (7) at the data parameter gives (7) at every such ε₁, so Theorem 1 applies with it (#T3.19-1), and its minimal orbit, the unique critical orbit, does not depend on the choice (BP_DERIVED_CONFIGS #BC.1-4-3). It and ε₁^{(1)} are fixed after α₀, M′, and K and before γ.
{#W8.12-9} Every condition of stage 5 holds for γ small at the data parameter, which is ≤ Cḡp₀(ḡ).
{#W8.12-10} The premises (S) (§4) and the eight choices of §12 are not conditions on the constants.
- {#W8.13} Stage 0, the exponents: 0 < ε₀ < 1/125 (the LF note's bounds of (ii) and its scale threshold n₀′ for r(Y) ≤ 1/64, LF #4.425, #4.456, #4.521, #4.553–#4.554; it covers ε₀ < 1/4 for γ_w > 1/4 and the consumer's exponent, and §12's ε₀ < 2/5); β ∈ [3/4, 1) (§8 above, the consumer's (γ_H − 4β′)/2 > θ_V/8, which β ≥ 1/2 ensures; the LF note's (δ), *Where the current enters.*, β_o − β″ > ½ for the two-constants bounds of the smoothed current at complex points, which β ≥ 3/4 gives with β_o = min(β, 1 − 2ε₀) ≥ 3/4; it covers §12's β ∈ ((1 − ε₀)/3, 1); (Wδ-1) (#WOG.1) holds for every β < 1);
  {#W8.13-1} the LF note's β″ ∈ (0, 1/20], the crude lattice Hölder exponent of the second differences in its (δ) (*Where the current enters.*; it covers its β″ ≤ ½ of *The disc.*, its #4.312); β₂ = (1 + β)/2 (10.5); §11's β′ with 0 < β′ ≤ min(1/60, β_o − γ_w), β_o := min(β, 1 − 2ε₀) (§8 above, §12's bootstrap); CRE's coefficient β₀ of (2.6), which "can be chosen arbitrarily small, if g is sufficiently small" (CRE p.255 l.50), fixed as β₀ := 1/7 and realised by γ small in stage 6;
  {#W8.13-2} it gives β₀ ≤ 1/7 (LF #3.56; the Cauchy note's #CP.26, #C5.27, #C5.28-6, and #C11c.3-2), β₀ ≤ ½ (LF #3.68, #4.527, #4.537, and #4.605), and (1 + β₀)² = 64/49 ≤ 4/3 (stage 2's C_{αs} ≤ 2); it is not RG I's Hölder bound β₀ of (3.31) (#W12.222-1) nor VAR's β₀ = 1 (#W12.33-1); CRE's exponents with q₁ = q₀ > p₀ + 3r, q₀ an integer, within the LF note's choice q₁ ≥ q₀ > p₀ + 3r (LF #4.420-1.1 for q₀ > p₀ + 3r, LF #4.480 for q₁ ≥ q₀; CRE (2.28) asks q₀, q₁ to be integers greater than 1), used in §12's ratio of (D2).
- {#W8.14} Stage 1, on L: the lower bounds of table #T1.3. Of these, this note uses L ≥ 4 (§7); L > 5, hence L ≥ 6 (§12, *The crossings.*, and the collar cells); L > 2d (§12, *The collar's layers.*); L ≥ 8d + 4 (§12, the distance from Y to C at R_ι = 4dL + 1, and 10.5's M₁(L − 1 − R_ι/L) > 3 with M₁ ≥ 4); L ≥ 12d + 6 (§12, the localisation χ of *§11's oscillation at U_{1,2}*, M₁(L/3 − 1 − R_ι/L) > 3 with M₁ ≥ 4); L² > 9d (§12, *The cells of 𝒟′ and 𝒟″ on the collar.*);
  {#W8.14-1} and (1 + β₀)² ≤ L with CRE's β₀ = 1/7 of stage 0 (§12, the ratio of (D2), the cross-index comparison). L ≥ 12d + 6 gives all of these, as (12d + 6)² > 9d and (1 + β₀)² = 64/49. The other bounds of #T1.3 serve the map, two-loops, and the LF note: L odd and L > 11, L ≥ L₀^× (which covers L ≥ 12d + 6), L ≥ 6d + c_b, L ≥ 128(1 + β₀), and (L-V). BLL's (κ-loc) follows from L ≥ L₀^× and RG II's ½(κ₁ − 1) ≥ 2Lκ (#BLL.29) and adds no condition.
- {#W8.15} Stage 2, on RG I's β_I and c₂: β_I := 2^{−7}, RG I's class parameter β (the Cauchy note's #C5.26, for 1 + 8β_I = 17/16 and β_IL^{−2} ≤ 2^{−9} in its #C5.28-16 and #C5.28-18 (the bounds 0.35 and 0.174 and the B′-part 2^{−9}), e^{β_I}·¼ < 0.26 and 0.92 + (1 + O(α_{1,k}))e^{β_I}/128 < 1 in its §8.2 (#C8.2.2-35, #C8.2.2-72), (1 + 2^{−9})² ≤ e^{β_I} (#C5.26-13), and e^{2β_I}·½ < 0.51 for the lift gauges of its #C5.5–#C5.7 and #C5.47),
  {#W8.15-0} with (1 + 8β_I)L^{−2} ≤ 1 (RG I (3.52), p.280 l.18, which gives the first inequality of the condition (iii), |∂𝐔 − 1| < α₀ξ², p.262 l.37), hence (1 + 7β_I)L^{−2} ≤ 1 (p.279 l.28) and β_IL^{−2} ≤ 1;
  {#W8.15-1} c₂ ≤ 1, c₂ within the rooms ½α₀, ½α₁, and (1 − L^{−3})α₀ of RG I's (3.13) (a constant of d, L, and B₃, the Cauchy note's #C5.36-11), and c₂ ≤ c_N := (128B₃²C₁₃C_{Q*}O(1))^{−1}, with C₁₃ ≥ 1 the constant of the moves of (I.3.13) and the O(1) at least max(1, B₅/B₃) times the constant of the data moves, B₅ the constant of VAR (173) through Proposition 9 [15] (the Cauchy note's #C5.8-28), so that the points (N) and (R3) of the Cauchy note's evaluation set lie in its norm class and its §8.2's moves fit the rooms (its #C5.8-27 and #C8.2.2);
  {#W8.15-2} and c₂ ≤ (43B₃(4C_δ(ε₀)L^{7/3} + C_{Q*}(1 + 3C_φ)))^{−1} and c₂ ≤ ½ (the LF note's #4.284, for its C_{αs} = (1 + β₀)²(1 + c₂) ≤ (64/49)(3/2) < 2, not the Cauchy note's C_α, at stage 0's β₀ = 1/7; implied by the first when B₃ ≥ 1/43),
  {#W8.15-3} with the LF note's C_δ(ε₀) (its #4.320, a constant of d, L, ε₀, B₀, B₀′(ε₀), C_ℒ′, and c_{δ_f/2}), the Cauchy note's C_{Q*} (its #C5.6-5), and the LF note's C_φ of the gauge-fixing addition D_Aφ_A (its #4.284.2-1), which do not involve c₂, for the t_□ part of the decoupled scale-j field on Bałaban's circle (3.15), whose entries are ⅓α₂, and its part C_φα₂ of D_Aφ_A (the LF note's (i) at the decoupled configurations and the lift half's *The conditions.*).
  {#W8.15-4} These are homogeneous in α̃_{0,k} and do not involve γ.
- {#W8.16} Stage 3, on the walk problems' R and PBG's integer K: R ≥ 12dL (§7's cells and cubes, §11's cube fitting), which at the joins reads CRE's K ≥ 12d + 1, a power of L, and covers R ≥ 8dL and R ≥ (2d + 1)L (§12, U^0_k on Λ^∼); K ≥ 4, a power of L, in PBG's M = KR₀M₀ (§7; it covers 10.3's K ≥ 2); R_ι = 4dL + 1 for the lift's one-step problem (#W12.237-6), with the product conditions of PRT2 (2.59) at RM = R_ιM₁ and VAR p.304 at R₁M₁ = M′ (#T2.7-1);
  {#W8.16-1} REG's Sect. F reach R > 4dLR₁ at M = R₁M₁, R counted in blocks of VAR's M₁ (#W12.237-3), which at R₁M₁ = M′ holds for the walk problems by R′ ≥ 12dL (BP_JOINS_BLOCK_SIZE #4.24-2) and for the lift by #W12.237-6.
  {#W8.16-2} CRE's K ≥ C(d) + 1 (the LF note's #4.22.1, the passage at a real base, whose RM ≥ C(d)R₁M₁L reads (LK − 1)M′ ≥ C(d)LM′ at R = R′ = LK − 1 and M = M′; its M′ ≥ L and RM ≥ L² follow from stage 3's M′ ≥ max(L², 6L) and K ≥ 2) and K ≥ C(L), a lower bound that does not involve M′ (LF #4.22.3, the background comparison at a real base); CRE's K ≥ R_thr(d, L)/L + 1 (LF #4.22-2, any separate threshold on R in PRT2, PBG, and VAR at the block size M′, which R′ = LK − 1 then meets). The LF note writes CRE's K as K_{M′}.
- {#W8.17} Stage 3, on R₀M₀: R₀ a power of L with R₀ > 5dL (§11); R₀M₀ ≥ L (10.1); (W-c) (§5(c)); (W-c′) (2/3)δ₀R₀M₀ ≥ (2 + β)log L (10.2); (2.59) at α = 1/9 and 1/27 with (2/27)δ₀R₀M₀ ≥ (β + d + 5)log L (10.3); (2.59) at α = 1/243, 1/972, and 1/1458 with (1/486)δ₀R₀M₀ ≥ (β + d + 7)log L (10.4); δ_D′R₀M₀ ≥ 12β log L (§11, *The defect of D_□.*); ½δ₁R₀M₀ ≥ 4 log L and δ_ιR₀M₀ ≥ (3/2)log L (10.5, the fine-side lift); δ_cR₀M₀ ≥ 16 log L and R₀M₀ ≥ 40L² (10.5, the complex chain configurations); (J0) (§11; its part ⅛δ_minRM₁ > 2d log(16/δ_min) + 1 follows from its part on R₀M₀, since RM₁ ≥ 2R₀M₀);
  {#W8.17-1} the conditions of the compositions (Comp) in 10.2–10.4, which the conditions of 10.3 and 10.4 above imply.
- {#W8.18} Stage 3, on PBG's block size M′ (M in §§7–8 and 10, M₁ in §§11–12): M′ ≥ max(M₁^{PBG}, R₀M₀, R₁M₁), a power of L (the LF note's *The block size M′.*); M′ ≥ max(L², 6L) (§7 and the collar cells); M₁ ≥ 4 (§12); δ₀M₁ ≥ 1 (§12, run B's regularity on □̃⁵); δ_ιM₁ ≥ 1 with the tail rate δ_ι (§12, the layered tail and the tail away from X in *§11's oscillation at U_{1,2}*, where it also bounds K_T); δ_minM₁ ≥ 6c_d log L, c_d = 2d(3^d + 1), which covers δ_minM₁ ≥ 6 log L (§12, the crossing decay and the strip crossings); (163′) B₃e^{−½δ₀M′} ≤ ½L^{−3} (§12, *The band regularity of U_{1,2}.*);
  {#W8.18-1} the lower bound on M₁ in (J) (§11); δ_brM₁ ≥ 2L^{1/3} and δ_br^cM₁ ≥ max(2L^{1/3}, L²/e) (§11, the bridge and its complex conclusion); δ_QRM₁ ≥ 6 log L, δ_brRM₁ ≥ 6 log L, δ_br^cRM₁ ≥ 6 log L, and δ₁RM₁ ≥ 12 log L (§11, the layer crossings of the bridge); (F-ι) ¼δ₁LM₁ ≥ (3 + β₂)log L + log 2 (§12, *§11's oscillation at U_{1,2}*); (F-W) at W = LM₁, ½δ_fLM₁ ≥ (7/3)log L (LF #4.318 and #4.322; its part at W = RM is on RG II's M below); (T-M₁) M₁ ≥ M₁^τ := (6/(eδ₀))(512B₃(1 + β₀)²C_ι/C_F)^{1/3}, a constant of d, L, and G (LF #4.323, the class tail of ι_X at every generation);
  {#W8.18-2} (J-W), (2.59) at α = 1/128 and ⅛δ_*LM₁ ≥ 4 log L + 1 (LF #4.18; §12's joins and the crossing decay), also at the width R′M′ ≥ ½LM₁, R′ = LK − 1, through M₁ ≥ 2M_J(d, L) (LF #4.24 and #4.29; the LF note's composites, LF #4.444); (1/16)δ_*M′ > 2d log c₀(⅛) + 1 at δ_* = min(δ₀^{PBG}, δ₀^{PRT2}), PRT2 (2.59) at α = ¼ with RM = M′ (the LF note's strip count at the composites, LF #4.22 and #4.445);
  {#W8.18-3} δ₀M′ ≥ 64 log L and (1/128)δ₀M′ > 2d log c₀(1/64) + 1, PRT2 (2.59) at α = 1/32 with RM = M′, both with VAR's δ₀ of (190) (the LF note's *The age factor.*: the layer factors of VAR (190) on RG I's sequence on □₀, whose layers are more than R₁M₁ = M′ wide by REG (1.4), the sum (2.61) at α = 1/32, and the factor L^{−4} per layer crossed by the strip parts outside □₀).
  {#W8.18-4} ½δ_Q^{pl}LM₁ ≥ 3 log L + 1 with the local rate δ_Q^{pl} of ℒ (LF #4.40.2-2 and #4.29, the profile-weighted non-local link ℒ at the joins and the top N₀ layers of 𝐁″_k, whose crossing lengths are ≥ LM₁).
- {#W8.19} Stage 3, on RG II's cube size M: (F-W) at W = RM, ½δ_fRM ≥ (7/3)log L (LF #4.318 and #4.322), and at W = M for LFR I's frozen layers (LFR I p.179 l.22–24), which follows from (F-W) at LM₁ by M ≥ 2(d + 1)L²M₁ below; M ≥ 4M₁ with CRE's M₁ = KM′ (the collar fits of §§11–12), which gives VAR's M ≥ 4R₁M₁ (§12, VAR's cubes in Λ); M ≥ 2dM₁ with CRE's M₁ (the LF note's strip response of run B at the representation configurations, LF #4.449, and at the composites, LF #4.445), which covers M ≥ 4M₁ for d ≥ 2;
  {#W8.19-1} M ≥ 2(d + 1)L²M₁ with CRE's M₁ (the LF note's strip of misaligned layers at ∂□₀ and ∂Y_i, of the ℓ¹ width (d + 1)M₁a_2, kept at the distance ≥ 2Ma_n from the points read, LF #4.445 and #4.449), which covers M ≥ 2dM₁; M ≥ 16N_DM₁ (§11); M ≥ 4κ₁/(ρδ_g) and e^{−(1/3)δ₀M}e^{2·6^dκ₁} < 1 (§11, the κ₁ replay); min(δ₀, δ₁)M ≥ 8 log L (§12, the far data of the one-step lift); (W-M) (§7);
  {#W8.19-2} M ≥ 2R_*, R_* the least R ≥ 1 with C_tlR^de^{−δ₀R} ≤ 1/16 for the tail C_tlR^de^{−δ₀R} of PBG (3.42) (the LF note's *The age factor.*, which puts its cut-off balls B(z, 2R_*a_{m′}) inside □₁, at the distance ≥ Ma_{m′} from its complement); (D2) (§12, *Analyticity and bounds.*); Bałaban's own lower bounds on M, listed in §12's *No loop through M*: RG I's M ≥ M(κ) (Theorem 3, p.264 l.38–39), RG II's δ₀M ≥ κ (p.21 l.36) and δ₁M ≥ κ₁ (p.5 l.15), CRE's "M = L^m is sufficiently large" (p.245 l.34), and LFR I's δ(M/M₁) ≥ 2 (p.186 l.35) and O(1)B₃B₅M⁵e^{−4δM} ≤ α with α ≤ 1/8 (p.200 l.14–21).
  {#W8.19-3} CRE's conditions on MR₁ and M₂R₁ (p.250 l.47–48, p.251 l.39–40) hold for M fixed and γ small and are stage-6 conditions; λ_R = K_RLM + 1 with K_R ≥ 4B₃²O(1) and K_R ≥ O(1)(1 + B₃O(1)), which give RG I's B₃²O(1)Mα₀ < ½α₁ (p.277 l.54) and O(1)(α₂ + B₃O(1)Mα₀) < α₁ with LM in place of M, as the near domains at a finer layer read them (the Cauchy note's #C5.34-4) (p.285 l.17, and the same form in (4.18), p.285 l.23, and in |B| < α₁L^jη, p.280 l.44, K_R taking the largest of their O(1)s) at RG I's ratio α₁/α₀ = λ_R and α₂ = c₂α₀ ≤ α₀ (§12, *Analyticity and bounds.*, the ratio of (D2)).
  {#W8.19-4} ⅛δ₀RM ≥ 4 log L + 1 and PRT2 (2.59) at α = ½ and at α = 1/128, with Bałaban's R and M of PRT2 (2.2) for CRE's domains (LF #4.9-2, #4.31, and #4.33: the row sums c_K of the residual's kernel, the ratio η_π ≤ δ₀/32, and the kernel form of VAR Proposition 4), and ½δ_Q^{pl}RM ≥ 3 log L + 1 (LF #4.40.2-1). At the joins and the top N₀ layers of 𝐁″_k they are read with LM₁ in place of RM, and (J-W) and ½δ_Q^{pl}LM₁ ≥ 3 log L + 1 of stage 3 cover them (LF #4.18-2, #4.40.2-2).
- {#W8.20} Stage 3′, after M, on B₃⁺ and a further upper bound on c₂: B₃⁺ is the Cauchy note's (#C5.37-18), with B_J's existence and uniformity in j Bałaban's printed claim (#C5.37-9), and B_J possibly depending on M through the cube □₀ = □̃⁵ (#C5.37-10);
  {#W8.20-1} c₂ ≤ c_* := β_IL^{−2}/(2B₃⁺C_{Q*}O(1)) with the absolute O(1) of RG I (3.49), so that O(1)α₂ ≤ α₃ (RG I p.279 l.44–49; §12, the ratio of (D2)).
  {#W8.20-2} Stages 1–3 use c₂ only through stage 2's upper bounds (c₂ ≤ 1 in K_R's clause), so the further upper bound keeps them.
- {#W8.21} Stage 4, upper bounds on PBG's α₀ and α₁ after L and the sizes: PBG's smallness of Mα₀ (p.396 l.32, for the class (3.35)–(3.36); used in Theorem 3.12, p.423 l.34, which asks α₀ sufficiently small, and at p.428 l.28) read at 2Mα₀, for the terms on the LF note's enlarged domain 𝒟^c (its *The induction.*); O(1)L⁵M′α₀ ≤ a₁/2 with PBG's a₁ (§7, §11's 16-block cubes; Corollary 3.6 at the real U₀; the half leaves the room for stage 5's ε₁ part of 10.5's O(1)L⁵M′(α₀ + O(1)LB₅ε₁) ≤ a₁);
  {#W8.21-1} α₁^A ≤ a₁/2 below, B₅ε₁ ≤ a₁/2, and B₅ε₁^{(1)} ≤ a₁/2 (10.5, *G₁ and H₁*, the Cauchy polydisc of radius (a₁/2)(L^jη)^{−1} about the real points, inside PBG's domain at a₁); O(L²α₀) ≤ ½ (10.4, the weight w_Q ≤ 3 of Q₁); α₀ ≤ a₀ with VAR's a₀ (§11, VAR's ε₀ ≤ a₀ at α₀ = ε₀); O(1)C_D(L⁵M₁α₀ + α₁) ≤ ½ (§11, *The inverse.* and the boundary data cubes); (J) (§11); O(1)B₀C₃Mα₀ ≤ ½ (§11, *The form (c) for G̃ with the Δ^{(2)} term*); α₁^A = 4L²(C_L + 1)(c_uMα₀ + α₁) ≤ a₁/2, 4C₂εr ≤ 1, and 2Lc_Gc_uMα₀ ≤ 1 (10.1);
  {#W8.21-2} C_ax·d(R_Q + 3)c_Fc_uMα₀ ≤ m_Q/4, 4Lα₁ ≤ r_G, and C_Qe^{½δ_Qr_T}C_ax′α₁ ≤ ½ (10.1, the lift); 8dc_Gα₁ ≤ log 2, C_tr′δ_T(0) ≤ 1, and c_F(Mα₀ + α₁ + α₁²) ≤ 1 with c_F ≥ 8L³(c_u + 1)/r_G, in effect O(1)L⁶(Mα₀ + α₁ + α₁²) ≤ r_G (10.2, 10.4); k_lc_F(Mα₀ + α₁ + α₁²) ≤ 1 and 32dc_F(Mα₀ + α₁ + α₁²) ≤ r_G (10.4); R₀M₀Mα₀ ≤ 1 (10.5); O(1)B₀²C_D(c_πα₀ + C₃Mα₀) ≤ ¼ (§11, *The inverse.*); η|A′| ≤ 1 for the Baker–Campbell–Hausdorff chart at the complex backgrounds (10.4); α_*′ of #W6.5-3 (#T3.15), with α_J = Mα₀ (§6).
- {#W8.22} Stage 5, upper bounds on ε₁ after α₀: O(1)L⁴C₀ε₁ ≤ α₀ and ε₁ ≤ a₁/(3L) with C₀ := 4R₁M₁(B₃ + B₄(1)) (§11, the axial-gauge (3.35) from VAR (9)–(10) on VAR's class cubes of the index m or m − 1); ε₁ ≤ a₁/7 for VAR's cubes with M_V = 7M′ (§12, the collar cells and the collar cubes); ε₁ ≤ a₁ with VAR's a₁ and B₅ε₁ ≤ a₁/2 with PBG's a₁ (10.5); O(1)L⁶M′B₅ε₁ ≤ a₁/2, its O(1) the product of the two O(1)s of 10.5's O(1)L⁵M′(α₀ + O(1)LB₅ε₁), so that with stage 4's O(1)L⁵M′α₀ ≤ a₁/2 the configuration of 10.5 satisfies O(1)L⁵M′(α₀ + O(1)LB₅ε₁) ≤ a₁, the smallness PBG requires of O(1)Mα₀ (10.5);
  {#W8.22-1} O(1)(R₀M₀)²L⁴C₀ε₁ ≤ 1 (10.5); C_ιε₁ ≤ min(α₁, Mα₀) (10.5); LC_ιε₁ ≤ O(1)M₁α₀ (§11, the bridge); the ε₃ of VAR (186)–(190) in VAR's range (10.5), that is 2ε₃ ≤ a₃ (VAR Proposition 4, p.292 l.50, at the doubled radius of the Cauchy estimate that gives (186), p.307 l.37–p.308 l.12) and 18C₂B₀ε₃ ≤ 1 (VAR p.286 l.20), with O(1)C_ℒ^gB₀C₂ε₃ ≤ ¼ and O(1)B₀C₂ε₃ ≤ 1 (§11, the fixed points D and the contraction); O(1)C_ℒ^gB₅ε₁ ≤ ε₃/2 (§11, the points A′^A in the identity's domain, and the circles of Cauchy's estimate in VAR (186));
  {#W8.22-2} O(1)B₅ε₁ ≤ r_G/2, which gives r ≤ r_G/2 for the cell domain 𝒫 at the complex W of §11's Taylor formula, r := max(|A′^A|_{(−1)}, |∇A′^A|_{(−2)}) = O(B₅ε₁) (§11: r at #W11.149-1 and #W11.168-3, the size of A′^A at #W11.63-1, and r ≤ r_G/2 at #W11.166-7 and #W11.170-6); 4B̄′_Jε₁ ≤ α_J (§6, #W6.5-5);
  {#W8.22-2-1} κ_V = O(1)B₀C₄C_ℒ^g(B₅ + B₀C₁B₃)ε₁ ≤ ½ with VAR's C₁ (§11, the contraction for 𝐀₀, read at B_T and 2·6^d); O(1)S_wB_TC₄B₅ε₁ ≤ ½ with S_w := sup_xΣ_ye^{−⅛δ_min d(x,y)} (the rate ⅛δ_min, the LF note's κ_w, not the walk-term defect δ_w(ω)), a constant of d, L, and δ_min (the LF note's (δ), *The weighted rerun.*, #4.284.14, the Neumann series of VAR (188) in the weighted norm);
  {#W8.22-3} B₅ε₁^{(1)} ≤ a₁/2 with PBG's a₁ and O(1)(R₀M₀)²L⁴C₀ε₁^{(1)} ≤ 1 (§12, 10.5's conditions at the one-step problem of 𝐇″_k); O(1)L³B₃ε₁^{(1)} ≤ α₀, O(1)L⁴C₀ε₁^{(1)} ≤ α₀, and ε₁^{(1)} ≤ a₁/(3L) (§12, the collar's (3.35) for U_{1,2} and VAR (9) for V₀; the first O(1) is that of VAR's Sect. F, as VAR p.280 l.51–52 takes α₀ = ε₀, VAR's ε₀, for U₀ ∈ 𝔘_k(L³B₃ε₁)).
- {#W8.23} Stage 6, for γ small: g small enough for CRE (2.6) with β₀ = 1/7 (stage 0; CRE p.255 l.50); the data parameter O(1)B₃²B₅M⁶ε_k at most the fixed ε₁ of 10.5 and at most ε₁^{(1)} (10.5, §12), which gives ε_k ≤ ε₁ (§8 above); 4d̄(ω) ≤ α_*′ (§6), with d̄ from the LF note's *The coarse side.* (its #4.314), an input whose conditions are the LF note's, stated there with the profile of its (b) and *The coarse side.* ((J-W) at the joins is in stage 3, and its ε₁ is the k-independent bound of the paragraph before this list);
  {#W8.23-1} the alignment's r(Y) ≤ ½ (#W10.5.45-22) is not a condition on the constants but the scale threshold n ≥ n₀′ of the LF note (its #4.553), which exists under ε₀ < 1/125 (stage 0);
  {#W8.23-2} O(1)C₀′ε₁ ≤ 1 and c_κ(C₀′ε₁)² ≤ 1 at the data parameter ε₁ = O(1)B₃²B₅M⁶ε_k of (9.2), not the fixed ε₁ of 10.5 (§12, the bootstrap, the transport term, and the source s_ι, #W12.55-2, #W12.83-3, and #W12.249-7);
    {#W8.23-2-1} O(1)C₀^cε₁″ ≤ 1 at the LF note's ε₁″ := C(M)ε′_k (its #4.560), the parameter of VAR's classes at the real points of its class at the full radii, for the base there (its *Real points.* of (δ), #4.281–#4.281-1), with C₀^c the bootstrap's C₀′ read with the target's and the base's parameters both at most O(1)ε₁″, a constant of M and the earlier stages, which holds for γ small since ε₁″ → 0, with the bootstrap's companion conditions read there too;
  {#W8.23-3} O(1)L⁵M′α₀^W ≤ a₁/2 and PBG's series condition at α₀^W := O(1)d²L²C₀^cε₁″, and C_ℒ″C_ℬε₂ ≤ 1 at ε₂ ≤ O(1)B₁ε₁″, all holding for γ small; O(1)L⁵M′α₀^W ≤ a₁/2 with PBG's a₁ at α₀^W := O(1)d²L²C₀′ε₁, and α₀^W below the absolute constant for which PBG's series (3.138) converges (Theorem 3.12's "α₀ sufficiently small", p.423 l.29–30, l.34) (§12, *The bootstrap.*, PBG's class at W_s); 4KM′²B₃ε_U^{(i)} ≤ ½L^{−3} with K the notes' name for the coefficient of VAR's (165) and U_i's data bounds ε_U^{(i)} ≤ O(1)B₃²B₅M⁶ε_k (§12, *The band regularity of U_{1,2}.*);
  {#W8.23-4} 4C_♯B₀C₄ε₄ ≤ ½ and ε₄ ≤ a₄ at ε₄ := 3B₀C₁B₃ε₁ with VAR's C₁, Proposition 6's printed value, with the data parameter ε₁ of (9.2), VAR's conditions at p.295 l.42 and l.20, l.45 at B = 0 for the ball (115), with C_♯ the constant of L and d of *The base at the layer j.* (§12); ε_U^{(i)} ≤ ε₁^{(1)}, so that stage 5's O(1)L³B₃ε₁^{(1)} ≤ α₀ gives the collar's (3.35) for U_{1,2} at its membership parameter L³B₃ε_U^{(i)} (§12, *The background pairs.*);
  {#W8.23-5} RG II's conditions on its ε₂, read at B_T and 2·6^d (§11): 4C₂B_Te^{2·6^dκ₁}ε₂ ≤ 1 (RG II p.5 l.30, for (1.13)–(1.14) and the bound |A| < 2ε₂ of l.39) and ε₂ ≤ a₃ (Proposition 4 of VAR with ε₃ replaced by ε₂, p.5 l.40); e^{32κ₁}ε₁ below RG II's absolute constant (RG II p.7 l.7, the premise of (1.21); §3, the t_□ circle), and e^{4·6^dκ₁}ε₁ below it for the composites of run B, where 16 stands for 2·6^d and so 32 for 4·6^d (§11, #W11.122-18 and #W11.134-3);
  {#W8.23-6} the Ad factors at complex points, each within a factor 2 of isometric when c_G times the imaginary part of its argument is ≤ log 2: c_G·O(1)C_HC_Ŷ(α̃_{0,k} + α̃_{1,k}) ≤ log 2 for the gauge factors u and ũ (#W12.174-1, #W12.209-2, #W12.215-3), c_GC_I(α̃_{0,k} + α̃_{1,k}) ≤ log 2 for w_y (#W12.176-5), and c_G·O(1)dM(1 + C_G)C_HC_Ŷ(α̃_{0,k} + α̃_{1,k}) ≤ log 2 for the transports along the contours (#W12.176-9, #W12.215-1) (§12, *Analyticity and bounds.*);
  {#W8.23-7} the conditions on ϱ̄ and ϱ of §11's bridge: O(1)Lϱ̄ ≤ C₁ε₁/4 with VAR's C₁ (VAR (172)), O(1)Lc_G(1 + B₀)ϱ̄ ≤ ½ log 2 (the complex return gauge and its Ad), O(1)c_GL^{d+3}(1 + B₀)ϱ̄ ≤ ½ (the series of V), and O(1)(1 + C_ℋ)ϱ ≤ C₀ε₁/2 with the Cauchy note's C₀ (the curvature of U₁), and the three conditions on κ_ℋ := O(1)c_G(1 + C_ℋ)ϱ̄ for its Neumann series at U₁ (#W11.37-2, #W11.37-8–#W11.37-10), O(1)B₀K_opS_{δ₁}κ_ℋ ≤ ½, O(1)C_Q′S_{δ_Q}κ_ℋ ≤ ½, and O(1)C_{QGQ}S_{δ₁/2}B₀K_opκ_ℋ ≤ ½;
  {#W8.23-7-1} O(1)L²R₀M₀α_c ≤ C₁ε₁/2 and O(1)ϱ ≤ C₁ε₁/4 with VAR's C₁, and ϱ ≤ O(1)α₁^A/L (10.5, with half the right sides in §12, the room for ε₂);
  {#W8.23-8} c_GLR₀M₀α_c ≤ 1, O(1)LR₀M₀α_c ≤ r_υ, 2c_G·O(1)LR₀M₀α_c ≤ ½log 2, and O(1)c_GLC_VC_aα_c ≤ ¼log 2 (10.5); O(1)LC_VC_aα_c ≤ ¼log 2, which gives O(1)L sup|ηℋ| ≤ ¼log 2 for the return gauge g of the complex chain configurations, since sup|ηℋ| ≤ C_V sup a ≤ O(1)C_VC_aα_c on the blocks of a pair of 10.5's Hölder quotient (#W10.5.51, #W10.5.56-2, #W10.5.71-4, #W10.5.85-2); C_ℒ″C_ℬε₂ ≤ 1 (§12, the bootstrap);
  {#W8.23-8-1} the factors O(1)α₂^{−1}ε_k of RG I's Cauchy estimates small (p.273 l.25, p.280 l.49), RG I's field in the class (3.31) and in (3.14) with ⅓α₂ (p.276 l.42, p.273 l.13), and RG II's 4B₀C₁e^{16κ₁}ε₁ ≤ ¼α₂ with RG II's absolute C₁ (RG II p.7 l.9; §3, the t_□ circle),
  {#W8.23-9} with 4B_TC₁e^{2·6^dκ₁}ε₁ ≤ ¼α₂ for the composites of run B (§11, #W11.134-3), and 4B_T′C₁e^{2·6^dκ₁}ε₁ ≤ ¼α₂, (3.14) with ⅓α₂ (p.273 l.13), and VAR's ball condition of (115), 2B_T′C₁B₃ε₁ ≤ a₄ with VAR's C₁ (an absolute bound, which holds since the data parameter tends to 0 with γ), at B_T′ := (3/2)B_T, for run B's terms of (1.60) along the k-field segment of the LF note's (iii) (its *The conditions along the segment.*);
  {#W8.23-10} the ratio conditions hold by ε_k/α₂ = (A₀/(c₂C₀))(log ĝ_k^{−2})^{p₀−q₀} with CRE's C₀ (both at ĝ_k, #W12.183-3), small under q₀ > p₀ + 3r, and the ball condition since ε_k = (ε_k/α₂)α₂ with α₂ → 0 (§12, the ratio of (D2));
  {#W8.23-10-1} RG I's bounds on its α₀ and α₁ at α₀ = α̃_{0,k}, α₁ = λ_Rα̃_{0,k}: O(1)Mα₁ ≤ β_I (RG I p.278 l.46, p.279 l.1–2), (4B₃²O(1)M)²α₀ ≤ β_I (p.278 l.64), and B₃(B₃O(1)Mα₀)² < β_Iα₀ (p.279 l.12), each also with LM in place of M at the radii of the layer n − 1 for the near domains at a finer layer (the Cauchy note's #C5.34-4), the O(1) of O(1)Mα₁ ≤ β_I taken at least that of the gauge bound ‖Ad(g)‖ ≤ exp(O(1)Mα₁) of the Cauchy note's #C5.26-8;
  {#W8.23-11} the error term O(1)(M⁶R_k(α̃_{0,k} + α̃_{1,k}) + exp(−R_k)) of LFR II (1.7) (p.358 l.4, with ε_k → O(1)(α̃_{0,k} + α̃_{1,k})) at most the lower bound γ₀^{LFR}(2d(100M)⁵)^{−1} of (1.9), half of the bound γ₀^{LFR}(d(100M)⁵)^{−1} that (1.8) gives for γ₀^{LFR}‖∂B′‖²/‖B′‖² (p.358 l.4, l.11, l.20; (1.8)'s exponent d + 1 is 5 at d = 4; γ₀^{LFR} is LFR II's constant of (1.7), not RG I's bound on 𝐉);
  {#W8.23-11-1} this holds for γ small, since R_k ≤ 2L(log g_k^{−2})^r and α̃_{i,k} = O(g_k(log g_k^{−2})^{q₀}) (#W12.183-3, with ĝ_k ≤ g_k and log ĝ_k^{−2} ≤ log g_k^{−2} + log ρ_γ, Cauchy #CP.14) give M⁶R_k(α̃_{0,k} + α̃_{1,k}) = O(g_k(log g_k^{−2})^{q₀+r}), and R_k → ∞ (§12, *Analyticity and bounds.*);
  {#W8.23-12} O(1)c_G(1 + B₀)ϱ̄ ≤ ¼log 2 (§11, the transports e^{iηℋ} at U₁); (D1), (C_s + C_Λ + C_Ŷ)(α̃_{0,k} + α̃_{1,k}) ≤ r_V with r_V the least of VAR's radius of absolute smallness in Propositions 4 and 6, the radius of the logarithm charts, and r_H := min{(16dLB₀²C₄)^{−1}, (24dLB₀²C₂)^{−1}} (§12, *Analyticity and bounds.*).
  {#W8.23-13} (T-π): 8B₀C_NLc_tot(1/128)c″_Kε₄ ≤ 1, 2C_{HD}Lc_tot(1/128)ε₄ ≤ 1, and ε₄ ≤ ¼a₃, at ε₄ := 3B₀C₁B₃ε₁ with VAR's C₁ and the data parameter ε₁ of (9.2), with ε₄ ≤ a₄ as above (LF #4.37–#4.38, the layer-weighted a priori inequality for VAR's fixed point; C_N, C_{HD}, c″_K, and c_tot(1/128) are constants of d, L, and Bałaban's constants, LF #4.32–#4.36).

{#W8.24-1} The passage from the propagators to 𝐇_k(s) through (Wδ-3) costs 2β′, β′ > 0 arbitrary, in the exponent of the gradient terms of the fixed point 𝐀₀ (§11, (a) and (b)), so for 𝐇_k(s) the exponent is γ_H − 2β′, with γ_H = βγ_w/(1 + β) of §11's form (c) for H and the constant C_𝔡B₀′(β′), C_𝔡 the constant of 𝔡_H there (it contains 2C_w and the constants of ϑ_ℒ, ϑ, and C_bϑ_b).
{#W8.24-2} Since 𝔡_H is built from global suprema, these exponents are in powers of L^{−j_min}, j_min ≥ k/2 − 1 the finest layer of the history, and in powers of ε/a_n, n ≤ k, they halve (§11, *The form (c) for VAR's H.*).
{#W8.24-3} The consumer, the LF note's (iii), needs (ε/a_n)^{(γ_H − 4β′)/2} ≤ θ̃^nL^{−cn} for some c > 0 (a further 2β′ is lost there in the second kind of smoothed current functional, LF *The divergence part.*), which holds since θ̃ ≥ L^{−θ_V/8} (the Cauchy note's §8.7) once (γ_H − 4β′)/2 > θ_V/8, θ_V/8 = β′_C/(16(4 + β′_C)) ≤ 1/144, since the Cauchy note's own parameter β′_C := ½min(β_H, 1 − β_E) (its #C5.3-2 and #CK.1-13; a different parameter from §11's β′) lies in [19/40, ½] and θ_V/8 increases in it.
{#W8.24-4} For β ≥ 1/2 and ε₀ < 1/4, γ_H ≥ 1/12, so for §11's β′ ≤ 1/60 the left side is ≥ 1/120 and this holds.
{#W8.24-5} The conditions (W-c) and (W-M) are lower bounds on PBG's R₀M₀ and on M. PBG takes R₀M₀ as the smallest pair satisfying the conditions of [4] (p.408 l.26–28), which are lower bounds, and B₀ and δ₀ depend on d and L only (Theorem 3.1, p.397 l.37).
{#W8.24-6} A larger R₀M₀ leaves every step of PBG valid: "In [4] we have proved all theorems under the assumption that R, M are sufficiently large", and R₀, M₀ are "a pair … of smallest possible numbers satisfying conditions needed in the proofs" (PBG p.408 l.26–27), so the theorems hold for every larger pair.
{#W8.24-7} The rates and constants used here do not depend on R₀M₀ (§11, PRT2 Proposition 2.6, (2.83)–(2.85), p.237 l.3).

## 10. The Condition (S), the Local Operators, and the Fine-Side Lift {#WS10}

### 10.1 The Aligned Background and the Condition (S) for One-Forms {#WS10.1}

{#W10.1.1} *The aligned background.* §§4–5 apply PBG's Theorems 3.1–3.3 to run A's local operators at Ũ := M(U′U^B), where U^B is real and satisfies (3.35) on □̃⁵ at the index j (§7, *The cubes next to the finer layer.*, in place of PBG p.409 l.2–3), and U′ = e^{i(ε/L)A′} satisfies (3.37) for run B's local sequence. Ũ lies in the domain of PBG Corollary 3.5 (p.407 l.45–47, "If a configuration U′ is in the domain (3.37) with U = 1 and α₁ ≤ a₁, then Theorems 3.1–3.3 hold"), after a real gauge transformation, with

  {#W10.1.2} α₁^A := 4L²(C_L + 1)(c_uMα₀ + α₁), under α₁^A ≤ a₁/2 (§8; Corollary 3.5 needs α₁^A ≤ a₁, and the half leaves 10.5's polydisc its room),

{#W10.1.3} where c_u := O(1)L³ is the constant of (3.35) on □̃⁵ at the index j that §7 derives (O(1)L²Mα₀ for |A| and O(1)L³Mα₀ for |∇A|, *The cubes next to the finer layer.*, in place of PBG's O(1)), so the smallness conditions below that contain c_uMα₀ are upper bounds on α₀ imposed after L and M, and C_L is the sum of the absolute weights of the plain linear average.
{#W10.1.3-1} Run A's operators at Ũ are the gauge transforms of those at Ũ^u by the real u, so Theorems 3.1–3.3 hold for them too.
{#W10.1.3-2} After the transformation back, the background of the covariant derivative in these bounds is the pure gauge 1^{u^{−1}}, not M(U^B).
{#W10.1.3-3} The two covariant derivatives differ by at most 2c_G|A| times the field, which is the relative factor 1 + 2Lc_Gc_uMα₀ ≤ 2 at the scale of each shell, as in the complex factor below.
- {#W10.1.4} *The gauge.* Let u be the real gauge transformation of PBG p.408 l.4 for U^B on the cube.
  {#W10.1.4-1} Then (U^B)^u = e^{i(ε/L)A}, with A satisfying (3.35) at run B's index of □, j + 1.
  {#W10.1.4-2} Since L^{j+1}(ε/L) = L^jε, this gives |A| < c_uMα₀(L^jε)^{−1} and |∇A| < c_uMα₀(L^jε)^{−2}.
- {#W10.1.5} *The complex factor.* In the same gauge, (U′U^B)^u(b) = Ad(u(x_b))U′(b)·(U^B)^u(b), with x_b the initial point of b, so A′^u(b) = Ad(u(x_b))A′(b) and |A′^u| = |A′|.
  {#W10.1.5-1} The derivative in (3.37) is the covariant ∇_U^η (p.396 l.43).
  {#W10.1.5-2} It transforms into ∇_{U^u}^η, which differs from the plain difference by at most 2c_G|A||A′|.
  {#W10.1.5-3} On run B's Ω_m with m ≤ j + 2, L^mε/L ≤ L^{j+1}ε, so (L^jε)^{−1} ≤ L(L^mε/L)^{−1}.
  {#W10.1.5-4} So on run B's Ω_m, |A′^u| < α₁(L^{m}ε/L)^{−1} and |∇A′^u| < α₁(1 + 2Lc_Gc_uMα₀)(L^{m}ε/L)^{−2} ≤ 2α₁(L^{m}ε/L)^{−2} under 2Lc_Gc_uMα₀ ≤ 1.
  {#W10.1.5-5} By the Baker–Campbell–Hausdorff formula, e^{i(ε/L)A′^u}e^{i(ε/L)A} = e^{i(ε/L)A″}, where A″ = A + A′^u + O((ε/L)|A||A′|) and ∇A″ = ∇A + ∇A′^u up to terms of the same relative order.
- {#W10.1.6} *The average.* By the gauge covariance of the averaging (CMP 98 (11)), Ũ^u = M(e^{i(ε/L)A″}) = e^{iεÃ} on the coarse bonds, with Ã = Ā″ + C(A″). Ā″ is the plain linear average, a translation-invariant weighted sum of A″ over the fine bonds within 2L fine spacings.
  {#W10.1.6-1} C is the nonlinear part, analytic, with |C(X)| ≤ C₂ε|X|².
  {#W10.1.6-2} This follows from the plain average CMP 98 (15) and the Baker–Campbell–Hausdorff formula, for εL|X| below the radius of the logarithm, as in VAR (44) at j = 1 and the Cauchy note's §9.8 (CMP 98 (122)–(123) state it for the double bar).
  {#W10.1.6-3} Hence |Ā″| ≤ C_L sup|A″| and |∇Ā″| ≤ C_L sup|∇A″|, the sups taken over the stencil.
  {#W10.1.6-4} Let r be the sup of |A″| over the stencil.
  {#W10.1.6-5} By Cauchy's estimate on the ball of radius 2r, |dC(X)| ≤ 4C₂εr for |X| ≤ r.
  {#W10.1.6-6} Since the plain average commutes with the translations of T_ε (the Cauchy note's *The Remainder of the Coarse Curvature.*), the coarse differences of C(A″) are differences C(τA″) − C(A″), with |τA″ − A″| ≤ ε|∇A″|.
  {#W10.1.6-7} Under 4C₂εr ≤ 1 this gives |C(A″)| ≤ r and |∇C(A″)| ≤ sup|∇A″|.
- {#W10.1.7} *The shells.* Run A's bounds on Ω^A_n are run B's on Ω^B_{n+1} = Ω^A_n (§2), since L^{n+1}(ε/L) = L^nε.
  {#W10.1.7-1} The stencil of a coarse bond near ∂Ω^A_n reaches fine bonds of Ω^B_n ∖ Ω^B_{n+1}, where run B's bounds are larger by the factor L for the sup and L² for the gradient, and for n = 0 these bonds lie in Ω₀^B by the margin below.
  {#W10.1.7-2} So |Ã| < α₁^A(L^nε)^{−1} and |∇Ã| < α₁^A(L^nε)^{−2} on Ω^A_n, which is (3.37) with U = 1 for run A's local sequence.

{#W10.1.8} So Theorems 3.1–3.3 hold for run A's local operators at Ũ, as §§4–5 use them; Corollary 3.5 asks for (3.37) only.

{#W10.1.9} *The lift.* Let N be the set of coarse bonds within ℓ^∞-distance 2ε of Ω₀^A(□), P_N the restriction to N, and Q₁ = Q̄₁(U′U^B).
{#W10.1.9-1} Let T_N := P_NQ₁Q₁*P_N on the fields on N, and put

  {#W10.1.10} ℒ_N := I + Q₁*P_NT_N^{−1}P_N(1 − Q₁I),

{#W10.1.11} with I the Cauchy note's interpolation (*Regularity of the Lifts.*).
{#W10.1.11-1} Then P_NQ₁ℒ_Nv = P_NQ₁Iv + T_NT_N^{−1}P_N(v − Q₁Iv) = P_Nv, so Q₁ℒ_N = 1 on N exactly. ℒ_N satisfies the following condition, which leg 1 of §5(c) uses.
{#W10.1.11-2} Here n is run A's shell index of the coarse bond c.

  {#W10.1.12} (H_ℒ) |ℒ_N(b, c)| ≤ C_ℒe^{−½δ_Qd_ε(b,c)}, and |∇_Bℒ_Nv(b)| ≤ Σ_c[k₁(b, c)|∇_Av(c)| + k₀(b, c)|v(c)|] with k₁(b, c) ≤ C_ℒe^{−½δ_Qd_ε(b,c)} and k₀(b, c) ≤ C_ℒ(Mα₀ + α₁)L^{−n}(L^nε)^{−1}e^{−½δ_Qd_ε(b,c)}.

{#W10.1.13} The second part is a bound, not a linear decomposition of ∇_Bℒ_N; §5(c) uses only the bound.

{#W10.1.14} The proof follows the Cauchy note's *Regularity of the Lifts.*, which is written at a real, globally regular background.
{#W10.1.14-1} Two changes make it local and complex.
- {#W10.1.15} *The real background.* T_N(U^B) is a compression of T(U^B), so its lower bound on the fields supported in N is that of T(U^B).
  {#W10.1.15-1} The Cauchy note's box argument is local: it uses ε²|F| ≤ C₀ε₁ only on the boxes of side R_Qε that meet N and on the paths of Q₁ that start in them.
  {#W10.1.15-2} These lie within (R_Q + 4)ε of Ω₀^A(□), hence in □̃⁵, since Ω₀^B lies at distance at least (K − 2)R₀M₀L^jε from the complement of □̃⁵, and there (3.35) gives ε²|F| ≤ c_Fc_uMα₀.
  {#W10.1.15-3} So the spectrum of T_N(U^B) lies in [m_Q/2, M̃_Q] under C_ax·d(R_Q + 3)c_Fc_uMα₀ ≤ m_Q/4, and its Neumann series gives |T_N(U^B)^{−1}(c, c′)| ≤ (2/m_Q)e^{−δ_Qd_ε(c,c′)}.
- {#W10.1.16} *The complex perturbation.* Each entry Q₁(c, b) of Q̄₁ (CMP 98 (124)) is built from the link variables on the bonds within 2ε of c: the transports along the paths, the power series in ad_Y and ad_{Y_x}, and the logarithm.
  {#W10.1.16-1} These series converge for link variables e^{iX} with |X| ≤ r_G, a constant of G and L, so the entry is analytic in the finitely many A′(b′) on the polydisc |(ε/L)A′(b′)| ≤ r_G/2 about the real background, and bounded there by a constant M_Q of L, d, and G. On run A's local sequence, (3.37) gives |(ε/L)A′| ≤ Lα₁L^{−n} ≤ Lα₁.
  {#W10.1.16-2} Cauchy's estimate on the line t ↦ Q₁(e^{it(ε/L)A′}U^B), analytic on |t| ≤ r_G/(2Lα₁), gives |Q₁(U′U^B)(c, b) − Q₁(U^B)(c, b)| ≤ 4M_QLα₁/r_G under 4Lα₁ ≤ r_G.
  {#W10.1.16-3} This covers the transports and the configuration-dependent operator factors together.
  {#W10.1.16-4} So ΔT := T_N(U′U^B) − T_N(U^B) = ΔQ₁Q₁* + Q₁ΔQ₁* + ΔQ₁ΔQ₁* has range r_T and row sums at most C_ax′α₁, with C_ax′ a constant of L, d, and G. Let ‖K‖_w := sup_cΣ_{c′}|K(c, c′)|e^{½δ_Qd_ε(c,c′)}, which is submultiplicative by the triangle inequality.
  {#W10.1.16-5} Then ‖T_N(U^B)^{−1}‖_w ≤ C_Q, the Cauchy note's constant, and ‖ΔT‖_w ≤ e^{½δ_Qr_T}C_ax′α₁.
  {#W10.1.16-6} Under C_Qe^{½δ_Qr_T}C_ax′α₁ ≤ ½, the series T_N^{−1} = Σ_{k≥0}(−T_N(U^B)^{−1}ΔT)^kT_N(U^B)^{−1} converges in ‖·‖_w, with ‖T_N^{−1}‖_w ≤ 2C_Q.
  {#W10.1.16-7} So |T_N^{−1}(c, c′)| ≤ 2C_Qe^{−½δ_Qd_ε(c,c′)}.
- {#W10.1.17} *The gradient.* In the axial gauge about a coarse point, Iv is a convex combination of transported coarse values, and its fine differences are interpolated coarse differences of v up to 2C_trε|F||v| (the Cauchy note's first bullet, with the size of F only).
  {#W10.1.17-1} (1 − Q₁I) annihilates fields constant in the axial gauge, so |(1 − Q₁I)v| ≤ C₁ε|∇_Av| + max(C₁, 1)C_trε²|F||v|, with C₁ a constant of d bounding the total weight of the first differences in the remainder, by first-order Taylor in place of the second-order one of the Cauchy note's #C10.4.110–#C10.4.110-0, whose transport count holds with C₁ for C.
  {#W10.1.17-2} The fine differences of Q₁*w are at most 4(1 + 2dL^{d−1})(L/ε)sup|w| on the stencil.
  {#W10.1.17-3} With ε|F| ≤ c_F(Mα₀ + α₁ + α₁²)L^{−n}(L^nε)^{−1}, this gives (H_ℒ) with C_ℒ a constant of L, d, G, m_Q, and c_F.
  {#W10.1.17-4} At the complex background, the column-sum bound of Q₁* and the interpolation I in the G^c-valued axial gauge differ from their values at U^B by the entry bound of the complex perturbation, and they are covariant by the next paragraph.

{#W10.1.18} G^c-covariance is used here and in 10.2.
{#W10.1.18-1} Every operator used here is built algebraically from the link variables: D_U, Δ_U, Q̄₁ (transports, power series in ad_Y, and the logarithm), I, and T_N.
{#W10.1.18-2} Each satisfies the covariance identity for G^c-valued gauge transformations g wherever both sides are defined, because transports transform by g(x)Γg(y)^{−1}, f(ad_{Ad(g)Y}) = Ad(g)f(ad_Y)Ad(g)^{−1} for power series f, and log(gXg^{−1}) = g log(X)g^{−1} where both logarithms are given by their series.
{#W10.1.18-3} The inverses G′, (Q′G′²Q′*)^{−1}, G, and T_N^{−1} inherit the identity by the uniqueness of inverses.

{#W10.1.19} *The condition (S).* Put

  {#W10.1.20} ℒ̃ := χ_Bℒ_N, χ_B the characteristic function of Ω₀^B(□).

{#W10.1.21} Then (S) holds for ℒ̃ in the form that §4 uses: ℒ̃ maps 𝔉^A into 𝔉^B, and χ_AQ₁ℒ̃X = X for every X ∈ 𝔉^A.
{#W10.1.21-1} Proof.
{#W10.1.21-2} The kernel Q₁(c, b) vanishes unless the fine bond b lies within ℓ^∞-distance 2ε of the coarse bond c: the paths of Q̄₁, the tube's straight paths together with the paths Γ inside the blocks and the non-main terms of CMP 98 (124), stay within 2L fine spacings (the Cauchy note's *Regularity of the Lifts.*, the range r_T).
{#W10.1.21-3} By §2 the margin between Ω₀^A(□) = Ω₁^B(□) and the complement of Ω₀^B(□) is 2R₀M₀ε/L.
{#W10.1.21-4} Under R₀M₀ ≥ L this margin is at least 2ε, so χ_AQ₁(1 − χ_B) = 0.
{#W10.1.21-5} Hence χ_AQ₁ℒ̃X = χ_AQ₁ℒ_NX = χ_AX = X for X ∈ 𝔉^A, Ω₀^A lying in N. The proofs of §4(a)–(b) use (S) only through these two properties, so the identities hold with ℒ̃, and ℒ̃* = ℒ_N*χ_B.

{#W10.1.22} *The cost in §5(c).* In leg 1, ℒ̃ is applied to a row w := G^A(·, x) with x ∈ Δ(y), y a block of □.
{#W10.1.22-1} By (H_ℒ), |∇_Bℒ̃w| ≤ Σ_cC_ℒe^{−½δ_Qd_ε(·,c)}(|∇_Aw(c)| + (L^nε)^{−1}|w(c)|) away from ∂Ω₀^B, with n the shell of c.
{#W10.1.22-2} A block of the shell n has side L^nε ≥ ε, so the kernel decays at least at the rate ½δ_Q per block.
{#W10.1.22-3} The sources at the output point b are bounded at the scale of b's shell n_b, the bracket at that of c's shell n_c; the ratio of the two scales and of their factors ϖ is at most L^{2|n_b−n_c|}, and one more power L^{|n_b−n_c|} enters for the commutator factor K of 10.4 with a coarser □′.
{#W10.1.22-4} Since d_ε(b, c) ≥ 2R₀M₀(|n_b − n_c| − 1)₊, an eighth of the rate pays all three: e^{−⅛δ_Qd_ε(b,c)}L^{3|n_b−n_c|} ≤ L³ under δ_QR₀M₀ ≥ 12 log L. With δ₀′ in place of δ₀ in §5(c), δ₀′ ≤ min(δ₀, ¼δ_Q) (its full definition, min(δ₀, ¼δ_Q, ¼δ₁, ¼δ_c), is in 10.6), one quarter of the rate transfers the weight, e^{−¼δ_Qd_ε(b,c)}e^{−δ₀d(y,y_c)} ≤ e^{−δ₀′d(y,y_b)} up to the factor e^{2δ₀}, and the remaining eighth counts.
{#W10.1.22-5} The count runs over the coarse bonds c, which form the single lattice of spacing ε, so the block sums against e^{−δ₀′d(y,·)} cost the factor C_ℒ′ := L³C_ℒL^dC_Σ, C_Σ := sup_bΣ_ce^{−⅛δ_Qd_ε(b,c)} ≤ dΣ_{m∈ℤ^d}e^{−⅛δ_Q|m|_∞}, a constant of d and δ_Q.
{#W10.1.22-6} This C_ℒ′ replaces the 3^dC_ℒ of the range-one-block assumption.
{#W10.1.22-7} The jump of χ_B at ∂Ω₀^B adds to ∇_Bℒ̃ a term at most (L/ε)|ℒ_Nw| on the bonds that cross ∂Ω₀^B.
{#W10.1.22-8} These lie in run B's extra shell, where (ε/L)^{−1} is the factor of the shell's own norm and ϖ = 1, and §5(c) already bounds that shell by L^{−βj}.
{#W10.1.22-9} So §5(c) holds with ℒ̃ under R₀M₀ ≥ L, with C_ℒ′ in place of 3^dC_ℒ and the rate δ₀′ in place of δ₀ throughout: in §5(c) (δ₀′/3), in (W-c), in 10.3, in §7's telescoping, and in (W-M).

{#W10.1.23} The fine side needs the same for χ_Bℒ_ι, with ℒ_ι of §3(c), in place of ℒ in §4(b): the bound (H_ℒ) for ℒ_ι; the tail (1 − χ_B)ℒ_ιG^Af of ℒ_ι outside Ω₀^B; and the exactness χ_AQ̄₁ℒ_ι = 1 on 𝔉^A.
{#W10.1.23-1} Since ι inverts the plain average, dι_Y is a right inverse of dM = Q̄₁ − D̄Θ₁ (the Cauchy note's (B1)), so Q̄₁dι_Y = 1 + D̄Θ₁dι_Y; 10.5 treats the three.
{#W10.1.23-2} It splits dι_Y = H₁b(v) + D_Bγ₀, with H₁ PBG's lift for the double bar, applies §4 to the aligned pair (ι_Yc^A, c^A) that the LF note's split prescribes, and derives (H_ℒ), its Hölder bound, the tail, and the exactness for ℒ_ι = H₁𝔡 at the real chain configurations.
{#W10.1.23-3} The gauge term and the complex chain configurations are treated in 10.5.

{#W10.1.24} 10.1 uses R₀M₀ ≥ L and δ_QR₀M₀ ≥ 12 log L of (W-c), lower bounds on PBG's R₀M₀ like the other conditions of (W-c) (PBG p.408 l.26–28, #W8.24-5–#W8.24-6).

### 10.2 The Bilinear Defect of Δ′_a (the Operator of G′_□) {#WS10.2}

{#W10.2.1} *Setting.* Scalar fields take values in 𝔤^c on the sites of T^X ∩ Ω₀^X(□), with the pairings of PBG p.393 l.46.
{#W10.2.1-1} By PBG (3.23)–(3.24) (p.394 l.19–29), Δ′_a = (Δ_U^η + Q′*aQ′) restricted to Ω₀ with Dirichlet conditions, Δ_U^η = D_U^{η*}D_U^η, and

  {#W10.2.2} ⟨λ, Q′*aQ′λ⟩ = Σ_na_nΣ_{y∈Λ_n}(L^nη)^{d−2}|(Q′_n(U)λ)(y)|², a_{n+1} = aa_n/(aL^{−2} + a_n), a₁ = a₀ = a.

{#W10.2.3} The background is run B's U′U^B on Ω₀^B, with U^B real satisfying (3.35) and U′ = e^{i(ε/L)A′} satisfying (3.37), and run A's is the aligned Ũ = M(U′U^B), which lies in the domain of PBG Corollary 3.5 for run A's local sequence (10.1).
{#W10.2.3-1} The defect is

  {#W10.2.4} β′_□(ℱ, 𝒜) := ⟨χ_AQ′₁ℱ, Δ′^A_aχ_AQ′₁𝒜⟩_A − ⟨ℱ, Δ′^B_a𝒜⟩_B, ℱ, 𝒜 ∈ 𝔉^B,

{#W10.2.5} with Q′₁λ(y) = L^{−d}Σ_{x∈B(y)}Ad(U(Γ_{y,x}))λ(x), the one-step average of gauge parameters at run B's background (CMP 98 (78)–(79)).

{#W10.2.6} *Transports.* Fix a point z and the cell of fine bonds within ℓ¹-distance 4dε of z.
{#W10.2.6-1} In a complex axial gauge of U′U^B about z (U′U^B has values in G^c, and the operators are covariant under G^c-valued gauge transformations by the argument of 10.1), every transport along a path of at most 3dL fine bonds in the cell has adjoint action within δ_T(n) of 1, where n is run A's shell index at z.
{#W10.2.6-2} By (3.35) and (3.37) on the shell n, the curvature of U′U^B there is at most c_F(Mα₀ + α₁ + α₁²)(L^nε)^{−2}, with c_F a constant of d, G, and L. It includes the factor L² for the cells near ∂Ω^A_n, which reach run B's shell n, where (3.37) at run B's index n is weaker by L² than at n + 1.
{#W10.2.6-3} As in the Cauchy note's *Transports.*, the holonomy argument gives

  {#W10.2.7} δ_T(n) ≤ 32d²ε²c_F(Mα₀ + α₁ + α₁²)(L^nε)^{−2} = 32d²c_F(Mα₀ + α₁ + α₁²)L^{−2n}.

{#W10.2.8} The gauge transformation to the axial gauge has imaginary part at most 4dα₁L^{−n} on the cell, by (3.37), so Ad of it has norm at most e^{8dc_Gα₁} ≤ 2 under 8dc_Gα₁ ≤ log 2, with c_G a constant of G. At real backgrounds, δ_T is the Cauchy note's 32d²ε²|F|.

{#W10.2.9} *The averaging terms.* These are §5(a), restated in the present form.
{#W10.2.9-1} Q′^B_{n+1} = Q′^A_nQ′₁ exactly (CMP 98 (80); the Cauchy note's identity (i) of §10.4), with Q′^A₀ = 1.
{#W10.2.9-2} The averaging blocks of the points of Λ^A_n lie in Ω₀^A, so χ_A changes nothing there.
{#W10.2.9-3} Run A's layer Λ^A_n carries a_n and the weight (L^nε)^{d−2}, and run B's layer Λ^B_{n+1}, the same set, carries a_{n+1} and (L^{n+1}ε/L)^{d−2} = (L^nε)^{d−2}.
{#W10.2.9-4} Hence the averaging part of β′_□ is ⟨ℱ, s₀^{av}⟩_B, with

  {#W10.2.10} s₀^{av} := Σ_{n≥0}(a_n − a_{n+1})(L^nε)^{−2}Q′^{B*}_{n+1}1_{Λ^A_n}Q′^B_{n+1}𝒜 − a(ε/L)^{−2}1_{Λ^B_0}𝒜.

{#W10.2.11} Q′^B_{n+1} averages values transported along paths of at most d(n + 1)L^{n+1} fine bonds inside one block of the shell n.
{#W10.2.11-1} By (3.37) the imaginary part of such a transport is at most dL^{n+1}(ε/L)·α₁(L^nε)^{−1} ≤ dα₁, uniformly in n, so its adjoint action has norm at most e^{2c_Gdα₁} ≤ 2 under 2c_Gdα₁ ≤ log 2, which 8dc_Gα₁ ≤ log 2 implies.
{#W10.2.11-2} So Q′^B_{n+1} and its adjoint for the weighted pairings each have sup norm at most 2, and Q′^{B*}_{n+1}Q′^B_{n+1} at most 4.
{#W10.2.11-3} Each site lies in the averaging blocks of one layer only, so one n contributes at each point.
{#W10.2.11-4} By §5(a), |a_n − a_{n+1}| ≤ aL^{−2n}/(1 − L^{−2}) ≤ 2aL^{−2n}, and a_n − a_{n+1} = 0 at n = 0.
{#W10.2.11-5} So on a block of the shell n ≥ 1, L^nε|s₀^{av}| ≤ 8aL^{−2n}‖𝒜‖_{1,β;y}.
{#W10.2.11-6} On run B's extra shell, (ε/L)|s₀^{av}| ≤ a‖𝒜‖_{1,β;y}.

{#W10.2.12} *The Laplacian term.* There are three cases.
- {#W10.2.13} A coarse bond c with both ends in Ω₀^A.
  {#W10.2.13-1} By the identity (iii) of the Cauchy note's §10.4, D_AQ′₁φ = Q^{str}D_Bφ + X(φ), where Q^{str} averages the fine differences over the straight paths of the tube of c.
  {#W10.2.13-2} X is linear, with kernels supported within ℓ^∞-distance 2ε of c, and its absolute row sums satisfy |X(φ)(c)| ≤ C_tr′δ_T(n)ε^{−1}sup_{cell}(|φ| + ε|D_Bφ|).
  {#W10.2.13-3} Here C_tr′ := 16.
  {#W10.2.13-4} In the axial gauge, the three transported values of D_AQ′₁φ(c) (the two block averages and the coarse link) are each within δ_T(n) of their untransported forms, and the fine transports of Q^{str}D_Bφ(c) add at most δ_T(n)ε^{−1}sup|φ| in total after telescoping along the straight paths.
  {#W10.2.13-5} This gives the count 4.
  {#W10.2.13-6} The factor 4 is that of Ad of the complex axial gauge, since the gauge transformation and its inverse each contribute a factor at most 2.
  {#W10.2.13-7} Its column sums are at most C_{5L}C_tr′δ_T(n)ε^{−1}, with C_{5L} = (5L)^d as in the Cauchy note's (10.6c).
- {#W10.2.14} A coarse bond c with one end in Ω₀^A and one outside.
  {#W10.2.14-1} Then D_A(χ_AQ′₁φ)(c) = ±ε^{−1}(transported)Q′₁φ(y_in).
  {#W10.2.14-2} These bonds lie in run A's shell 0, since Λ^A₀ = Ω₀^A ∖ Ω₁^A has width 2R₀M₀ε ≥ ε.
- {#W10.2.15} The fine bonds of run B, paired as ⟨D_Bℱ, D_B𝒜⟩_B.

{#W10.2.16} Q^{str*}Q^{str} =: P is an average.
{#W10.2.16-1} Each fine bond b of direction μ lies on exactly L of the straight paths of the tubes of direction μ, so ⟨Q^{str}v, w⟩_A = ⟨v, Q^{str*}w⟩_B with Q^{str*}w(b) = L^{−1}Σ w(c) over these L pairs (c, path) (with the transports).
{#W10.2.16-2} Restricted to the interior coarse bonds, P is sub-Markov, and Markov at the fine bonds all of whose L tubes are interior.
{#W10.2.16-3} Its kernel is supported within Euclidean distance 3√dε.
{#W10.2.16-4} Hence

  {#W10.2.17} β′_□(ℱ, 𝒜) − ⟨ℱ, s₀^{av}⟩_B = ⟨D_Bℱ, s₁⟩_B + ⟨ℱ, s₀^{lap}⟩_B,

{#W10.2.18} with

  {#W10.2.19} s₁ := (P − 1)D_B𝒜 + Q^{str*}X(𝒜) + εX₁*(D_AQ′₁𝒜),

{#W10.2.20} and s₀^{lap} := X₀*(D_AQ′₁𝒜) plus the boundary term ε^{−2}Q′₁*(transported Q′₁𝒜) at the outer bonds of Ω₀^A.
{#W10.2.20-1} Here X(φ) = X₀φ + X₁(εD_Bφ) splits X by its two kernels, so ⟨X₁(εD_Bℱ), w⟩_A = ⟨D_Bℱ, εX₁*w⟩_B, and the starred operators are the adjoints for the pairings of the two runs.

{#W10.2.21} *The bounds.* Let y be a block of run A's shell n, and let ‖𝒜‖ := ‖𝒜‖_{1,β;y}, the norm of (Wδ-1) (§5), built with the Hölder quotient of PBG (3.40) at the scale L^nε.
- {#W10.2.22} At a fine bond b of Δ(y) whose L tubes are interior, (P − 1)D_B𝒜(b) is an average of differences of transported values of D_B𝒜 over a set of Euclidean diameter at most 3√dε.
  {#W10.2.22-1} A lattice path of at most 3d segments, each of length at most ε, joins any two of these points.
  {#W10.2.22-2} The Hölder quotient of (3.40) applies to each segment, since ε ≤ L^nε is within its range (|x − x′| at most one spacing of the scale), and each segment adds at most 2δ_T(n)‖𝒜‖ through the transports.
  {#W10.2.22-3} So (P − 1)D_B𝒜(b) is at most 3d[L^{−βn} + 2δ_T(n)]‖𝒜‖.
  {#W10.2.22-4} At the other fine bonds, which lie in run A's shell 0 or in run B's extra shell, it is at most 2|D_B𝒜| ≤ 2‖𝒜‖.
- {#W10.2.23} |Q^{str*}X(𝒜)| ≤ 2C_tr′δ_T(n)ε^{−1}(|𝒜| + ε|D_B𝒜|) ≤ 2C_tr′δ_T(n)(L^n + 1)‖𝒜‖ ≤ 4C_tr′δ_T(n)L^n‖𝒜‖, by |𝒜| ≤ L^nε‖𝒜‖.
- {#W10.2.24} |D_AQ′₁𝒜| ≤ (1 + C_tr′δ_T(0))·2‖𝒜‖ ≤ 4‖𝒜‖ under C_tr′δ_T(0) ≤ 1.
  {#W10.2.24-1} So |εX₁*(D_AQ′₁𝒜)| ≤ 4C_{5L}C_tr′δ_T(n)‖𝒜‖ and L^nε|X₀*(D_AQ′₁𝒜)| ≤ 4C_{5L}C_tr′δ_T(n)L^n‖𝒜‖.
- {#W10.2.25} The boundary term lies in run A's shell 0.
  {#W10.2.25-1} A site has at most d outer bonds, and the transported link, Q′₁, and Q′₁* each have norm at most 2.
  {#W10.2.25-2} So in the normalisation L^0ε|s₀| it is at most εε^{−2}·8d|𝒜| ≤ 8d‖𝒜‖.

{#W10.2.26} With δ_T(n)L^n ≤ 32d²c_F(Mα₀ + α₁ + α₁²)L^{−n} ≤ 32d²c_F(Mα₀ + α₁ + α₁²)L^{−βn}, this gives, on every block y of run A's shell n ≥ 1,

  {#W10.2.27} sup_{Δ(y)}(|s₁| + L^nε|s₀|) ≤ C′_L(β)L^{−βn}‖𝒜‖_{1,β;y},
  {#W10.2.28} C′_L(β) := 3d + 8a + 32d²c_F(Mα₀ + α₁ + α₁²)(6d + 4C_tr′(1 + 2C_{5L})),

{#W10.2.29} and on run A's shell 0 and run B's extra shell the same with ϖ = 1 and the constant C′_L(β) + 8d + a.
{#W10.2.29-1} So (Wδ-1) holds for Δ′_a with s₂ = 0 (scalar fields have no D*-slot), s₁ and s₀ as above, and ϖ_n = L^{−βn}.

{#W10.2.30} *The Hölder bound of the sources.* For the gradient entries the sources need a Hölder bound at the scale of their shell.
{#W10.2.30-1} Let 0 < β′ < β.
{#W10.2.30-2} For points x, x′ of Δ(y):
- {#W10.2.31} If |x − x′| ≥ ε, the quotient of s₁ is at most 2sup|s₁|ε^{−β′}, and (L^nε)^{β′} times it is at most 2C′_L(β)L^{−(β−β′)n}‖𝒜‖.
- {#W10.2.32} If ε/L ≤ |x − x′| < ε, then (P − 1)D_B𝒜 changes by at most |x − x′|^β(L^nε)^{−β}‖𝒜‖ through D_B𝒜 itself, and by at most 4dε^β(L^nε)^{−β}‖𝒜‖ through P, whose stencils at x and x′ both lie in a set of diameter 4√dε, joined by chains of at most 4d segments of length at most ε as in the first bullet of the bounds.
  {#W10.2.32-1} Dividing by |x − x′|^{β′} ≥ (ε/L)^{β′} gives (L^nε)^{β′} times the quotient at most (1 + 4dL^{β′})L^{−(β−β′)n}‖𝒜‖.
- {#W10.2.33} The X-parts are bounded through their sup, as in the first case, with (ε/L)^{−β′}.
  {#W10.2.33-1} This adds 2C′_L(β)L^{β′}L^{−(β−β′)n}‖𝒜‖.

{#W10.2.34} So (L^nε)^{β′}‖s₁‖_{β′} ≤ C″_L(β, β′)L^{−(β−β′)n}‖𝒜‖_{1,β;y}, with C″_L := 2C′_L(β)(1 + L^{β′}) + 1 + 4dL^{β′}.
{#W10.2.34-1} The gradient entries therefore hold at the rate ϖ_n = L^{−(β−β′)n}.
{#W10.2.34-2} Since (3.43) holds for every β < 1 (PBG p.398 l.2–8), this changes only the exponent: γ_w ≤ β − β′ in §8 for those entries.

{#W10.2.35} *The coarse side of G′_□.* §5(c) applies with Δ′_a, the scalar lift ℒ′ of §4(d) (exact, finite range one block), (3.42)–(3.43) for G′_□ (PBG Corollaries 3.5 and 3.6, at the backgrounds of 10.1), and the sources above. ℒ′ transports along paths inside one block, so its norm is at most 2 at complex backgrounds, by the bound on Q′^B_{n+1} above.
{#W10.2.35-1} The leg-1 operator is D_B in place of ∇_B*, as §5(c) allows.
{#W10.2.35-2} So, under (W-c) with R₀M₀ ≥ L, for x in a block y of □ and supp g in a block y′ of □,

  {#W10.2.36} 𝔈 := χ_AQ′₁G′^B_□ − G′^A_□χ_Aℒ′*, |𝔈g(x)| ≤ C′_□(β)(ε/a_j)^β(L^jη)²e^{−(δ₀/3)d(y,y′)}|g|,

{#W10.2.37} with C′_□(β) the constant C_□(β) of §5(c) with C′_L(β) + 8d + a for C_df(β) (the larger of the constants of #W10.2.28–#W10.2.29) and C_ℒ = 2.
{#W10.2.37-1} The entries G′∇*, ∇G′, and ∇G′∇* are not used below.

{#W10.2.38} *The coarse side at general points (E-gen).* Let x ∈ Δ(y) with y a block of run A's shell m ≥ 0, and supp g ⊂ Δ(y′) with y′ any block of run A's local sequence.
{#W10.2.38-1} Under

  {#W10.2.39} (W-c′) (2/3)δ₀R₀M₀ ≥ (2 + β)log L, besides the first condition of (W-c) and R₀M₀ ≥ L,

  {#W10.2.40} |𝔈g(x)| ≤ C_gen(β)L^{−βm}(L^mη)²e^{−(δ₀/3)d(y,y′)}|g|, C_gen(β) := 6c₀^d(1/6)c′_βC₃′,

{#W10.2.41} with C₃′ := 18·3^de^{4δ₀}C_ℒ(C′_L(β) + 8d + a)B₀B₀(β), C_ℒ = 2, and c′_β := 3L^{1+β} + L^β + 5.
{#W10.2.41-1} The source constant C′_L(β) + 8d + a is the larger of 10.2's constants, the boundary shells (run A's shell 0 and run B's extra shell) carrying C′_L(β) + 8d + a.
{#W10.2.41-2} Proof.
{#W10.2.41-3} The computation of §5(c), with the block of □ replaced by y.
{#W10.2.41-4} All bounds are operator bounds on sources supported on one block, the form in which (3.42) states them; a source bounded on a union of blocks is split into its block pieces, so no kernel row sums, and no factor depending on dim 𝔤, enter.
{#W10.2.41-5} Leg 2 decays in run B's weighted distance d^B and leg 1 in run A's d^A.
{#W10.2.41-6} Run A's admissible contours are run B's with the same weights (Λ^B_{n+1} = Λ^A_n and L^{n+1}(ε/L) = L^nε), so d^B ≤ d^A, and the bound holds with d = d^B.
- {#W10.2.42} Leg 2 is unchanged.
  {#W10.2.42-1} A block y″ of the shell n receives ‖u_B‖_{1,β;y″} ≤ 3e^{2δ₀}B₀(β)(L^nη)e^{−δ₀d(y″,y′)}|g|, the factor being that of the receiving layer.
- {#W10.2.43} In leg 1, (3.42) for G′^A with the factor of x's layer m gives B₀[(L^mη) + (L^mη)²(L^nη)^{−1}]e^{−δ₀d(y,y″)} per unit source.
  {#W10.2.43-1} Times the factor L^nη of leg 2, this is (L^mη)²(1 + L^{n−m}) ≤ 2(L^mη)²max(1, L^{n−m}).
- {#W10.2.44} Only leg 1 is known to cross the shells between m and n.
  {#W10.2.44-1} By (2.60), d(y, y″) ≥ 2R₀M₀(|n − m| − 1)₊, so the last third of the decay gives e^{−(2/3)δ₀R₀M₀(|n−m|−1)₊} ≤ L^{−(2+β)(|n−m|−1)₊} under (W-c′).
- {#W10.2.45} The sum over the shells, with ϖ_n = L^{−βn} for n ≥ 1 and ϖ = 1 on run A's shell 0 and run B's extra shell, is S(m) := Σ_nϖ_nmax(1, L^{n−m})L^{−(2+β)(|n−m|−1)₊}.
  {#W10.2.45-1} The shells with |n − m| ≤ 1 give at most 3L^{1+β}L^{−βm}.
  {#W10.2.45-2} The shells n ≤ m − 2 give L^{−βm}L^{2+β}Σ_{k≥2}L^{−2k} ≤ L^{−βm}, and the boundary shells, at distance at least 2R₀M₀(m − 1) from y, give at most (L^β + 1)L^{−βm}.
  {#W10.2.45-3} The shells n ≥ m + 2 give L^{−βm}L^{2+β}Σ_{k≥2}L^{−(1+2β)k} ≤ 2L^{−βm}.
  {#W10.2.45-4} So S(m) ≤ c′_βL^{−βm}.
{#W10.2.46} The count over one layer and the factor e^{−(δ₀/3)d(y,y′)} are as in §5(c).
{#W10.2.46-1} For m = 0 the bound is relatively of order 1, as it must be on run A's shell 0.
{#W10.2.46-2} 10.3 does not use the entries G′∇*, ∇G′, and ∇G′∇* at general points.

### 10.3 The Operator C_□ {#WS10.3}

{#W10.3.1} The data spaces of C_□ = (Q′G′²_□Q′*)^{−1} are not the same in the two runs.
{#W10.3.1-1} Run B's data space is 𝔇^A ⊕ 𝔇^B_0, where 𝔇^A, the data on the layers Λ^B_{n+1} = Λ^A_n, is run A's data space, and 𝔇^B_0 is the data on the sites of run B's extra shell, where Q′^B_0 = 1.
{#W10.3.1-2} Let K^X := Q′^XG′^{X2}_□Q′^{X*}, and write K^B in blocks (K_{11}, K_{12}; K_{21}, K_{22}) for this splitting, and C^B_□ in blocks [C^B_□]_{ik} likewise.

{#W10.3.2} The bound used is PBG (3.48), Theorem 3.2 (p.398, transcription l.61–66), at the backgrounds of 10.1 through Corollaries 3.5 and 3.6:

  {#W10.3.3} |(Q′G′²Q′*)^{−1}(y, y′)| ≤ B₀(L^jη)^{−4}(L^{j′}η)^{−d}e^{−δ₀d(y,y′)}, y ∈ Λ_j, y′ ∈ Λ_{j′}.

{#W10.3.4} Here j and j′ are the layer indices of the points y and y′, not the scale of □.

{#W10.3.5} *Per-block bounds.* Write ℓ_m := L^mε for run A's layer m; run B's layer m + 1 has the same scale and is written with ℓ_m as well.
{#W10.3.5-1} The norm on 𝔤^c is the Hermitian norm of the invariant inner product (PBG p.393 l.46), for which transposition below is exact.
{#W10.3.5-2} For an operator A, let |A(z←z′)| be the sup of |(Av)(z)| over v with |v| ≤ 1 supported on the block of z′.
{#W10.3.5-3} These bounds compose: |AB(z←z′)| ≤ Σ_w|A(z←w)||B(w←z′)|, the sum over the blocks w.
{#W10.3.5-4} In this form:
- {#W10.3.6} (3.48) gives |C^X_□(z←z′)| ≤ B₀ℓ_m^{−4}e^{−δ₀d(z,z′)} for z ∈ Λ_m, the data weight ℓ_{m′}^d of z′ cancelling (L^{j′}η)^{−d};
- {#W10.3.7} (3.42) gives |G′^X_□(x←x′)| ≤ B₀ℓ_m²e^{−δ₀d(x,x′)} for x in the layer m;
- {#W10.3.8} (E-gen) gives |𝔈(x←x′)| ≤ C_gen(β)L^{−βm}ℓ_m²e^{−(δ₀/3)d(x,x′)};
- {#W10.3.9} on the data spaces, where a block is a single point z of weight ℓ_m^d, transposition for the weighted bilinear pairing gives exactly |T^T(z←z′)| = (ℓ_{m′}/ℓ_m)^d|T(z′←z)| for z ∈ Λ_m and z′ ∈ Λ_{m′}, since |T(z←z′)| = ℓ_{m′}^d|t(z, z′)| for the kernel t.
  {#W10.3.9-1} For operators on the fine lattice this rule fails: the block sum over the target controls only the block average of the transposed quantity, not its sup, so it is used for data operators only;
- {#W10.3.10} N(δ₀/k) := 6c₀^d(1/(2k)), the bound of (2.58) under (2.59) at α = 1/k, which gives sup_zΣ_{z″}e^{−(δ₀/k)d(z,z″)} ≤ N(δ₀/k)e^{−|m−m″|} over the layer m″ of z″ and hence ≤ 3N(δ₀/k) over all layers, of the form of the first condition of (W-c); N(δ₀/3) = 6c₀^d(1/6).

{#W10.3.11} All distances are run B's weighted distance d^B, run A's bounds holding with it because d^B ≤ d^A (10.2, (E-gen)).
{#W10.3.11-1} By (2.60), blocks of the layers m and m′ are at weighted distance at least 2R₀M₀(|m − m′| − 1)₊.
{#W10.3.11-2} For the innermost shell □̃⁴ ∖ Ω_{j+1}(□) this needs its width ML^jη to be at least 2R₀M₀L^jη.
{#W10.3.11-3} With PBG's M = KR₀M₀, K a positive integer (p.408 l.28), that is the condition K ≥ 2.

{#W10.3.12} *(Comp), the composition with an intermediate layer power.* Let |A(z←w)| ≤ aℓ_{m_w}^qe^{−κd(z,w)} and |B(w←z′)| ≤ bℓ_{m_w}^pe^{−κd(w,z′)}, with only the power of the intermediate layer m_w displayed.
{#W10.3.12-1} Then, under (2/3)κR₀M₀ ≥ (|p + q| + 1)log L and (2.59) at the rate κ/3,

  {#W10.3.13} Σ_w|A(z←w)||B(w←z′)| ≤ ab(3 + 2/(L − 1))L^{|p+q|}N(κ/3)ℓ_{m_z}^{p+q}e^{−(κ/3)d(z,z′)}.

{#W10.3.14} Proof. ℓ_{m_w}^{p+q} ≤ ℓ_{m_z}^{p+q}L^{|p+q||m_w−m_z|}.
{#W10.3.14-1} Split the decay e^{−κ[d(z,w)+d(w,z′)]} into thirds.
{#W10.3.14-2} One third gives e^{−(κ/3)d(z,z′)} by the triangle inequality.
{#W10.3.14-3} One third gives the count N(κ/3) over the blocks of each layer.
{#W10.3.14-4} One third gives e^{−(2/3)κR₀M₀(|m_w−m_z|−1)₊} ≤ L^{−(|p+q|+1)(|m_w−m_z|−1)₊}.
{#W10.3.14-5} So the layer m_w contributes at most L^{|p+q|}L^{−(|m_w−m_z|−1)₊}, and the sum over the layers is at most (3 + 2/(L − 1))L^{|p+q|}.
{#W10.3.14-6} The same holds with the power moved to z′'s layer, with d(w, z′) in place of d(z, w) for the crossing.

- {#W10.3.15} *The exact identity.* The 𝔇^A-row of C^B_□K^B = 1 reads [C^B_□]_{11}K_{11} + [C^B_□]_{12}K_{21} = 1.
  {#W10.3.15-1} With Δ_K := K_{11} − K^A and K^AC^A_□ = 1 on 𝔇^A, multiplying on the right by C^A_□ gives

  {#W10.3.16} [C^B_□]_{11} − C^A_□ = −[C^B_□]_{11}Δ_KC^A_□ − [C^B_□]_{12}K_{21}C^A_□.

  {#W10.3.17} Its factors are blocks of C^B_□ and C^A_□, bounded by (3.48) in each run, the block K_{21} of K^B, bounded by (3.42) for G′^B_□ and the counts of §5(c), and Δ_K.
- {#W10.3.18} *Δ_K.* By Q′^B_{n+1} = Q′^A_nQ′₁ on 𝔇^A, Q′₁G′^B_□ = 𝔈 + G′^A_□ℒ′* on Ω₀^A, the symmetry of G′ for the bilinear pairing, and ℒ′* = Q′₁ with Q′₁ℒ′ = 1 (§4(d); the bilinear trace form is Ad(G^c)-invariant, so this holds at complex backgrounds),

  {#W10.3.19} Δ_K = Q′^A[𝔈ℒ′G′^A_□ + G′^A_□ℒ′*𝔈^T + 𝔈𝔈^T]Q′^{A*}.

  {#W10.3.20} Q′^A and its adjoint have sup norm at most 4 at Ũ: 10.2 (*The averaging terms.*) bounds Q′^B_{n+1} by 2, and Q′^A_n = Q′^B_{n+1}ℒ′ with |ℒ′| ≤ C_ℒ = 2. ℒ′ reads one site, in the block of its output point, which costs at most e^{2δ₀} in the decay (slack).
  {#W10.3.20-1} Let z ∈ Λ^A_m and z′ ∈ Λ^A_{m′} be data points, and c₃ := 3 + 2/(L − 1) ≤ 5.
  {#W10.3.20-2} The averaging blocks of z lie in run A's shell m, so (E-gen) applies to 𝔈 at the points they average, with the relative factor L^{−βm}.
  {#W10.3.20-3} The three terms are bounded as follows.
  - {#W10.3.21} *𝔈ℒ′G′^A_□.* Its intermediate kernel is |ℒ′G′^A_□Q′^{A*}(w←z′)| ≤ 4e^{2δ₀}B₀ℓ_{m_w}²e^{−δ₀d(w,z′)}.
    {#W10.3.21-1} (Comp) at κ = δ₀/3 and p + q = 2, with the power moved to z′'s layer, and the factor 2 of Q′^A give at most 8e^{2δ₀}c₃L²N(δ₀/9)C_genB₀L^{−βm}ℓ_m²ℓ_{m′}²e^{−(δ₀/9)d(z,z′)}.
  - {#W10.3.22} *G′^A_□ℒ′*𝔈^T.* With Q′^{A*} = (Q′^A)^T, the symmetry of G′^A_□, and (ℒ′*)^T = ℒ′, the operator Q′^AG′^A_□ℒ′*𝔈^TQ′^{A*} is the data-level transpose of Q′^A𝔈ℒ′G′^A_□Q′^{A*}.
    {#W10.3.22-1} By the transposition rule on data, it is at most (ℓ_{m′}/ℓ_m)^d times the first bound at (z′, z), that is 8e^{2δ₀}c₃L²N(δ₀/9)C_genB₀L^{−βm′}ℓ_m²ℓ_{m′}²L^{d|m−m′|}e^{−(δ₀/9)d(z,z′)}.
    {#W10.3.22-2} No fine-side bound on 𝔈^T enters.
  - {#W10.3.23} *𝔈𝔈^T.* No smallness of 𝔈^T is used; the factor L^{−βm} comes from the left factor 𝔈.
    {#W10.3.23-1} On run A's fine fields, 𝔈^T = G′^B_□ℒ′χ_A − ℒ′χ_AG′^A_□, whose output lies on run B's Ω₀^B.
    {#W10.3.23-2} For w a block of run A's local sequence, (3.42) in each run gives |𝔈^TQ′^{A*}(w←z′)| ≤ 8e^{2δ₀}B₀ℓ_{m_w}²e^{−δ₀d(w,z′)}, and the composition with (E-gen) is as in the first term, with the constant 16e^{2δ₀}c₃L²N(δ₀/9)C_genB₀.
    {#W10.3.23-3} For w a site of run B's extra shell, the second part vanishes and the first is at most 4e^{2δ₀}B₀(ε/L)²e^{−δ₀d(w,z′)}.
    {#W10.3.23-4} There ℒ′*g = 0, so 𝔈g = χ_AQ′₁G′^B_□g, and (3.42) in run B gives |𝔈(x←w)| ≤ 2B₀ℓ_m²e^{−δ₀d(x,w)}.
    {#W10.3.23-5} By (2.60), d(x, w) ≥ 2R₀M₀m, and two thirds of the decay give e^{−(4/3)δ₀R₀M₀m} ≤ L^{−βm} under (W-c′).
    {#W10.3.23-6} With the count N(δ₀/9) over run B's layer 0, the rate δ₀/9, (ε/L)² ≤ ℓ_{m′}², and the factor 2 of Q′^A, this part is at most 16e^{2δ₀}N(δ₀/9)B₀²L^{−βm}ℓ_m²ℓ_{m′}²e^{−(δ₀/9)d(z,z′)}.

  {#W10.3.24} The three bounds are written with the factor 2 for each of Q′^A and Q′^{A*}; with the factor 4 each, they are four times larger.
  {#W10.3.24-1} The sum of the three terms, with L^{d|m−m′|} ≤ L^{(d+2)|m−m′|}, is

  {#W10.3.25} |Δ_K(z←z′)| ≤ c_KL^{−βmin(m,m′)}ℓ_m²ℓ_{m′}²L^{(d+2)|m−m′|}e^{−(δ₀/9)d(z,z′)}, c_K := 640e^{2δ₀}B₀(B₀ + C_gen(β))L²N(δ₀/9),

  {#W10.3.26} under (2/9)δ₀R₀M₀ ≥ 3 log L, (2.59) at α = 1/9, and (W-c′).
- {#W10.3.27} *The main term.* Let y and y′ lie in the support of h_□, which is where R′₀(□) = h_□C_□h_□ reads C_□ (§1(d)), in the layers j or j + 1, and let z ∈ Λ^A_m and z′ ∈ Λ^A_{m′}, with m, m′ ≤ j + 1.
  {#W10.3.27-1} By the three bounds,

  {#W10.3.28} |[C^B_□]_{11}(y←z)||Δ_K(z←z′)||C^A_□(z′←y′)| ≤ B₀²c_Kℓ_j^{−4}L^{−βmin(m,m′)}(ℓ_m/ℓ_{m′})²L^{(d+2)|m−m′|}e^{−(δ₀/9)[d(y,z)+d(z,z′)+d(z′,y′)]}.

  {#W10.3.29} Relative to ℓ_j^{−4}L^{−βj}, the powers are at most L^{β(j−m)}L^{(β+d+4)|m−m′|}, since j − min(m, m′) ≤ (j − m) + |m − m′| and ℓ_m/ℓ_{m′} ≤ L^{|m−m′|}.
  {#W10.3.29-1} One third of the decay gives e^{−(2/27)δ₀R₀M₀[(j−m−1)₊ + (|m−m′|−1)₊]}, which is at most L^{−(β+d+5)[(j−m−1)₊ + (|m−m′|−1)₊]} under (2/27)δ₀R₀M₀ ≥ (β + d + 5)log L. Each term is then at most L^{2(β+d+5)}L^{−(j−m−1)₊−(|m−m′|−1)₊}, and the sum over m ≤ j + 1 and m′ is at most L^{2(β+d+5)}(3 + 2/(L − 1))².
  {#W10.3.29-2} One third gives the counts N(δ₀/27)² over the blocks of the two layers, and one third the rate δ₀/27.
- {#W10.3.30} *The extra-shell term.* [C^B_□]_{12}(y←w) has w a site of run B's extra shell, which is run B's layer 0, a data point of weight (ε/L)^d since Q′^B_0 = 1.
  {#W10.3.30-1} The per-block bound of (3.48) is B₀ℓ_{j_B}^{−4}e^{−δ₀d(y,w)} ≤ B₀ℓ_j^{−4}e^{−δ₀d(y,w)}, run B's layer of y being j + 1 or j + 2, with ℓ ≥ ℓ_j.
  {#W10.3.30-2} K_{21}(w←z′) = (G′^B_□)²Q′^{B*}(w←z′) composes G′^B_□ at w, with the factor (ε/L)² of run B's layer 0, and G′^B_□Q′^{B*} with the factor 2B₀ℓ_{m_v}² of the intermediate layer.
  {#W10.3.30-3} (Comp) at κ = δ₀ and p + q = 2, with the power moved to z′'s layer, gives |K_{21}(w←z′)| ≤ 2c₃L²N(δ₀/3)B₀²(ε/L)²ℓ_{m′}²e^{−(δ₀/3)d(w,z′)}.
  {#W10.3.30-4} With C^A_□(z′←y′) ≤ B₀ℓ_{m′}^{−4}e^{−δ₀d(z′,y′)} and (ε/L)² ≤ ℓ_{m′}², the product is at most 2c₃L²N(δ₀/3)B₀⁴ℓ_j^{−4}e^{−(δ₀/3)[d(y,w)+d(w,z′)+d(z′,y′)]}.
  {#W10.3.30-5} By (2.60), run B's layer of y being at least j + 1 and w lying in its layer 0, d(y, w) ≥ 2R₀M₀j.
  {#W10.3.30-6} One third of the decay gives e^{−(2/9)δ₀R₀M₀j} ≤ L^{−βj} under (2/9)δ₀R₀M₀ ≥ β log L, and one third the rate δ₀/9.
  {#W10.3.30-7} The last third gives the count N(δ₀/9) over w and, z′ ranging over all layers, the count 3N(δ₀/9) over z′, by the factor e^{−|j−j′|} of (2.58) and 1 + 2/(e − 1) ≤ 3.

{#W10.3.31} Hence, at y and y′ in the support of h_□, in the per-block form,

  {#W10.3.32} |([C^B_□]_{11} − C^A_□)(y←y′)| ≤ C_C(β)(ε/a_j)^βB₀ℓ_j^{−4}e^{−(δ₀/27)d(y,y′)},
  {#W10.3.33} C_C(β) := B₀c_KL^{2(β+d+5)}c₃²N(δ₀/27)² + 6c₃L²B₀³N(δ₀/3)N(δ₀/9)²,

{#W10.3.34} under (2.59) at α = 1/9 and 1/27, (2/27)δ₀R₀M₀ ≥ (β + d + 5)log L, which implies (2/9)δ₀R₀M₀ ≥ 3 log L, (2/9)δ₀R₀M₀ ≥ β log L, and (W-c′), and K ≥ 2, besides R₀M₀ ≥ L and the smallness conditions of 10.1 and 10.2 for the backgrounds and the averaging.
{#W10.3.34-1} The rate δ₀/27 replaces δ₀/3 for C_□ in §7's telescoping, which then holds at a rate ≥ δ₀′/54, G_□ entering at δ_gf′/3 (10.4), and (W-M) is required with δ₀′/54, which is a rate in the metric of the cube's own sequence, δ₀′/(54L) in PRT2's global distance (§7, *The bound (1.11).*).
{#W10.3.34-2} The per-block form is what §7 uses, the kernel form following by the data weight of y′.

{#W10.3.35} *General points.* The same computation at y ∈ Λ^A_{j_y} and y′ ∈ Λ^A_{j_{y′}}, with ℓ_{j_y}^{−4} in place of ℓ_j^{−4}, gives the relative factor L^{−βmin(j_y,j_{y′})}.
{#W10.3.35-1} The sums over m and m′ now run on both sides of j_y and j_{y′}.
{#W10.3.35-2} The crossings (|j_y − m| − 1)₊, (|m − m′| − 1)₊, and (|m′ − j_{y′}| − 1)₊ absorb the powers L^{β(min(j_y,j_{y′}) − min(m,m′))} ≤ L^{β(|j_y−m| + |m−m′| + |m′−j_{y′}|)}, under the same condition.
{#W10.3.35-3} The extra-shell term gives e^{−(2/9)δ₀R₀M₀j_y} ≤ L^{−βj_y}.
{#W10.3.35-4} There are two summation indices, so the constant is C_C(β).
{#W10.3.35-5} The blocks [C^B_□]_{21} and [C^B_□]_{22}, which read or return run B's extra data layer, have no counterpart in run A. They are bounded by (3.48) alone and are relatively of order 1, as ϖ = 1 on that layer.

### 10.4 The One-Form Operator of G_□ {#WS10.4}

{#W10.4.1} Δ_a = D*D + Δ′ + DRD* + Q*aQ of PBG (3.82) on one-forms has four parts.
{#W10.4.1-1} Q*aQ is exact by §5(a): only the extra-shell term remains, of the form of s₀^{av}.
{#W10.4.1-2} The action part D*D + Δ′ is derived below, using only the size of the background curvature.
{#W10.4.1-3} The gauge-fixing part DRD* is derived after it, in a decay-weighted norm.

{#W10.4.2} *The action part: the identity.* D*D + Δ′ is the second variation of the Wilson action at the background in the direction W ↦ e^{iηζ}W, with Δ′ the curvature terms of PBG (3.10).
{#W10.4.2-1} Let b_□ be the Cauchy note's blocking artifact b = A_ε∘M̄ − A_{ε/L} (*The Action Part of β.*), restricted to the coarse plaquettes of Ω₀^A and the fine plaquettes of Ω₀^B, at the background U′U^B.
{#W10.4.2-2} CMP 98 (122)–(123) state the double bar at a real background V₀ with a complex fluctuation.
{#W10.4.2-3} The complex background reduces to that case: e^{iηX}U′U^B = e^{iηZ}U^B with Z = Z(A′, X) given by the Baker–Campbell–Hausdorff series, analytic in (A′, X) for η(|A′| + |X|) ≤ r_G/2, with dZ = 1 + O(c_Gη|A′|) and |d²Z| ≤ c_Gη at X = 0 under η|A′| ≤ 1.
{#W10.4.2-4} So M̄ is analytic at U′U^B, dM̄ = Q₁ = Q̄₁(U′U^B), and (B3) holds there, by the identity theorem from the real slice A′ ∈ 𝔤.
{#W10.4.2-5} Its quadratic part C₁^{(2)} at U′U^B is the second derivative in X of the linear average of Z plus C(Z).
{#W10.4.2-6} Cauchy's estimate for C on a ball of radius ρ ≥ |Z| about Z inside the domain of CMP 98 (123), where |C| ≤ C₂ε(2ρ)², gives |d²C| ≤ 2C₂ε(2ρ)²/ρ² = 8C₂ε, so |C₁^{(2)}[ℱ, 𝒜]| ≤ C₂′ε|ℱ||𝒜| with C₂′ := 16C₂ + c_GC_L.
{#W10.4.2-7} The identity of b_□, differentiated at U′U^B with dM̄ = Q₁ and d²M̄ = 2C₁^{(2)}, gives

  {#W10.4.3} β_act(ℱ, 𝒜) := ⟨χ_AQ₁ℱ, (D*D + Δ′)^Aχ_AQ₁𝒜⟩_A − ⟨ℱ, (D*D + Δ′)^B𝒜⟩_B = d²b_□[ℱ, 𝒜] − 2⟨J^A, C₁^{(2)}[ℱ, 𝒜]⟩_A + β_∂(ℱ, 𝒜),

{#W10.4.4} with J^A = D_A*F^A the current of Ũ (PBG (3.11)–(3.12)). β_∂ collects the plaquettes that χ_A cuts and the fine plaquettes whose column sum Σ_pw_{p,p′} falls short of L^{−d}, all in run A's shell 0 or run B's extra shell, where ϖ = 1.
{#W10.4.4-1} The Cauchy note's expansion of d²b (*The Second Variation of b.*) is an identity of analytic functions of the configuration.
{#W10.4.4-2} Its pairings are the bilinear trace form, which is Ad(G^c)-invariant, so the expansion holds at the complex background U′U^B as at real ones.
{#W10.4.4-3} Its Cauchy estimates use the polydisc |ζ| ≤ 2r_G about the plaquette holonomy, which contains the complex backgrounds under 32dc_F(Mα₀ + α₁ + α₁²) ≤ r_G, the analogue of the Cauchy note's 16dC₀ε₁ ≤ r_G with the Ad factor 2.
{#W10.4.4-4} The bound |d^iκ_η(X)| ≤ c_κη⁴|X|^{4−i} of the quartic remainder holds for complex X by the same Cauchy estimate.
{#W10.4.4-5} At each coarse plaquette p it is

  {#W10.4.5} −Cov_p(Tf′, Tf) − Cov_p(TF, Tf″) + X_tr + X_r + (quartic terms),

{#W10.4.6} with f′ = dF_{p′}[ℱ], f = dF_{p′}[𝒜], f″ = d²F_{p′}[ℱ, 𝒜], T the transports along the paths γ_{p′}, and the weights w_{p,p′} of (9.11).

{#W10.4.7} *The action part: the bounds.* Let y be a block of run A's shell n ≥ 1, ‖𝒜‖ := ‖𝒜‖_{1,β;y}, and ν_n := c_F(Mα₀ + α₁ + α₁²)L^{−n}.
{#W10.4.7-1} On the cells of the shell n, ε²|F| ≤ εL^nε|F| ≤ ν_n, by (3.35) and (3.37) (10.2, *Transports.*), and δ_T(n) ≤ 32d²ν_n.
{#W10.4.7-2} Each term is a sum over the cell of products of a linear expression in the values of ℱ, ∇_Bℱ, or D_Bℱ with one in 𝒜.
{#W10.4.7-3} In functional form, the coefficients of these three are s₀, s₁, and s₂.
{#W10.4.7-4} A pairing over coarse plaquettes is moved to the fine bonds by Σ_pε^dw_{p,p′} = (ε/L)^d, at the cost of the column-sum factor C_{5L} where the expression reads ℱ at the base bonds of a cell.
{#W10.4.7-5} Below, Ad of a transport costs the factor 2 at complex backgrounds, as in 10.2.
- {#W10.4.8} *Cov_p(Tf′, Tf).* Since Σ_{p′}w_{p,p′}(Tf_{p′} − M_pTf) = 0, with M_pX := Σ_{p′}w_{p,p′}X_{p′}, Cov_p(Tf′, Tf) = Σ_{p′}w_{p,p′}⟨Tf′_{p′}, Tf_{p′} − M_pTf⟩.
  {#W10.4.8-1} Here f′ = dlog_h[(D_Bℱ)(p′)], linear in the curl D_Bℱ, so this is ⟨D_Bℱ, s_c⟩_B with s_c(p′) := L^dΣ_pw_{p,p′}(dlog_h)^TT^T(Tf_{p′} − M_pTf), using Ad-invariance to move T. The column sums L^dΣ_pw_{p,p′} = 1 make s_c an average of differences, so |s_c| ≤ 4(1 + k_lν_n)·osc_p(Tf) ≤ 8osc_p(Tf) under k_lν_n ≤ 1.
  {#W10.4.8-2} The Hölder quotient of (3.40) allows |x − x′| ≤ 1, and the box of (9.11) has Euclidean diameter at most ε(d + 6)^{1/2}, so one pair gives the factor k_b := (d + 6)^{β/2}.
  {#W10.4.8-3} The curl D_B𝒜 consists of two differences, so osc(D_B𝒜) ≤ 2k_bL^{−βn}‖𝒜‖.
  {#W10.4.8-4} The transports add 8δ_T(n)‖𝒜‖ and f − D_B𝒜 adds 8k_lν_n‖𝒜‖, with the Ad factor 2.
  {#W10.4.8-5} Hence |s_c| ≤ 8[2k_bL^{−βn} + (256d² + 8k_l)ν_n]‖𝒜‖.
  {#W10.4.8-6} The curl slot is not the slot D_B*ℱ of (Wδ-1).
  {#W10.4.8-7} Since (D_Bℱ)_{μν} = ∇_μℱ_ν − ∇_νℱ_μ (PBG (3.9)), ⟨D_Bℱ, s_c⟩_B = ⟨∇_Bℱ, s₁⟩_B with |s₁| ≤ 2|s_c|, so this term enters (Wδ-1) as an s₁-source with |s₁| ≤ 16[2k_bL^{−βn} + (256d² + 8k_l)ν_n]‖𝒜‖.
- {#W10.4.9} *Cov_p(TF, Tf″).* Here only sup|F| is used.
  {#W10.4.9-1} Cov_p(TF, Tf″) = Σ_{p′}w_{p,p′}⟨TF_{p′} − M_pTF, Tf″_{p′}⟩, with |TF − M_pTF| ≤ 4|F|.
  {#W10.4.9-2} Split f″ by bilinearity with the cell-constant fields ℱ_c and 𝒜_c of the Cauchy note's *The Variations of r_p.* (the axial-gauge values at the bonds from y_p): f″[ℱ, 𝒜] = f″[ℱ − ℱ_c, 𝒜] + f″[ℱ_c, 𝒜 − 𝒜_c] + f″[ℱ_c, 𝒜_c].
  - {#W10.4.10} f″[ℱ_c, 𝒜_c] is the same at all p′ of the box up to k₂′(δ_T(n) + ν_n)|ℱ_c||𝒜_c|, the fields being constant in the axial gauge, where k₂′ is a constant of d, L, and G (through m_G and r_G) from the Cauchy estimates of d²F at the plaquette holonomy.
    {#W10.4.10-1} With |𝒜_c| ≤ 2|𝒜| at complex backgrounds, its part is at most 8|F|k₂′(δ_T(n) + ν_n)|ℱ_c||𝒜|.
    {#W10.4.10-2} It is an s₀-term with L^nε|s₀| ≤ 8C_{5L}k₂′(L^nε)²|F|(δ_T(n) + ν_n)‖𝒜‖ ≤ 8C_{5L}k₂′(1 + 32d²)ν_n‖𝒜‖, by (L^nε)²|F| ≤ c_F(Mα₀ + α₁ + α₁²) ≤ 1.
  - {#W10.4.11} |𝒜 − 𝒜_c| ≤ 4dε|∇_B𝒜| + δ_T(n)|𝒜| (*The Variations of r_p.*).
    {#W10.4.11-1} The pairing carries the transport of f″ and the axial-gauge values ℱ_c, which add the Ad factor 2 twice, so the part of f″[ℱ_c, 𝒜 − 𝒜_c] is an s₀-term with L^nε|s₀| ≤ 16C_{5L}k₂L^nε|F|(4dε + δ_T(n)L^nε)‖𝒜‖ ≤ 16C_{5L}k₂(4d + 32d²)ν_n‖𝒜‖.
  - {#W10.4.12} ℱ − ℱ_c is a sum along at most 4dL fine bonds of (ε/L) times transported values of ∇_Bℱ, plus at most δ_T(n)|ℱ|.
    {#W10.4.12-1} So the part of f″[ℱ − ℱ_c, 𝒜] is an s₁-term with |s₁| ≤ 16dC_{5L}k₂ε|F||𝒜| ≤ 16dC_{5L}k₂ν_n‖𝒜‖, plus an s₀-term with L^nε|s₀| ≤ 4C_{5L}k₂δ_T(n)‖𝒜‖ ≤ 128d²C_{5L}k₂ν_n‖𝒜‖.
- {#W10.4.13} *X_tr, X_r, and the quartic terms.* Each is linear in ℱ at fixed 𝒜, and the Cauchy note bounds it by K𝔰′𝔰 (#C10.4.56–#C10.4.58, with a factor ν_F, εℓ|F|, or ε²|F| in K), using of ℱ only |ℱ| ≤ ℓ𝔰′, |∇ℱ| ≤ 𝔰′, and |Dℱ| ≤ 2𝔰′ on the cell of p (#C10.4.46-1), with ℓ the scale; its bound of ℱ − ℱ_c follows from the first two (#C10.4.36-1).
  {#W10.4.13-1} With 𝔰′ := ‖ℱ‖_cell := max(sup|ℱ|/ℓ, sup|∇ℱ|, sup|Dℱ|) over the cell, the term is a linear functional λ of ℱ with |λ(ℱ)| ≤ K𝔰‖ℱ‖_cell. ‖·‖_cell is the norm of ℱ ↦ (ℱ/ℓ, ∇ℱ, Dℱ) in the maximum of three sup norms, whose dual norm is the sum of three ℓ¹ norms, so the Hahn–Banach theorem gives λ(ℱ) = ℓ^{−1}⟨ξ₀, ℱ⟩ + ⟨ξ₁, ∇ℱ⟩ + ⟨ξ₂, Dℱ⟩ with ‖ξ₀‖₁ + ‖ξ₁‖₁ + ‖ξ₂‖₁ ≤ K𝔰.
  {#W10.4.13-2} The terms of p read only the bonds of the box of (9.11) and the paths γ_{p′}, all within ℓ^∞-distance 2ε of p. So a fine bond meets the terms of at most 5^d base points and d² orientations, and the change from ε^d to (ε/L)^d costs L^d.
  {#W10.4.13-3} The curl entries ξ₂ become s₁-entries of at most twice their size, as in the first bullet (#W10.4.8-7).
  {#W10.4.13-4} At ℓ = L^nε these are sources with sup(|s₁| + L^nε|s₀|) ≤ 32d²C_{5L}k_νν_n‖𝒜‖, with k_ν the sum of the coefficients of ν_F in the Cauchy note's bounds of X_tr, X_r, and the quartic terms ((10.6a)), the factor 16 for the Ad factors, and the factor 2 for the curl.
- {#W10.4.14} *The current term.* PBG's current is J^A = D_A*F^A with F^A := η^{−2}Im ∂Ũ (PBG (3.11)), D* being the adjoint of D for the weighted bilinear pairing ((3.8)–(3.9)); F^A is the Cauchy note's F̂, not the logarithm Φ_p.
  {#W10.4.14-1} So summation by parts on Ω₀^A gives ⟨J^A, C₁^{(2)}[ℱ, 𝒜]⟩_A = ⟨F^A, D_AC₁^{(2)}[ℱ, 𝒜]⟩_A, plus boundary terms in run A's shell 0.
  {#W10.4.14-2} C₁^{(2)} is local and bilinear, with |C₁^{(2)}[ℱ, 𝒜]| ≤ C₂′ε|ℱ||𝒜|.
  {#W10.4.14-3} Its coarse curl is a sum of differences between neighbouring coarse bonds.
  {#W10.4.14-4} These are differences of its arguments over one coarse spacing, at most ε|∇_Bℱ| and ε|∇_B𝒜|, and differences of its background.
  {#W10.4.14-5} By the translation covariance of the average (10.1), the latter are C₁^{(2)} at τA″ against A″, with |τA″ − A″| ≤ ε sup|∇A″|.
  {#W10.4.14-6} Cauchy's estimate in the background on the polydisc of radius r_G/(2εL) bounds them by C₂′ε|ℱ||𝒜| times δ_C(n) := 2ε²L sup|∇A″|/r_G ≤ 8L³(c_uMα₀ + α₁)L^{−2n}/r_G ≤ ν_n, the last step with c_F ≥ 8L³(c_u + 1)/r_G.
  {#W10.4.14-7} So |D_AC₁^{(2)}[ℱ, 𝒜]| ≤ 4C₂′(ε|∇_Bℱ||𝒜| + ε|ℱ||∇_B𝒜| + (δ_T(n) + δ_C(n))|ℱ||𝒜|).
  {#W10.4.14-8} By 10.1, Ũ satisfies (3.37) with U = 1 and α₁^A on run A's shell n, so |F^A| ≤ c_F(α₁^A + (α₁^A)²)(L^nε)^{−2} ≤ c_FK_A(Mα₀ + α₁)(L^nε)^{−2}, K_A := 8L²(C_L + 1)(c_u + 1), using α₁^A ≤ 1.
  {#W10.4.14-9} With the factor 2 of −2⟨J^A, C₁^{(2)}⟩, this gives sources with |s₁| + L^nε|s₀| ≤ 8C₂′C_{5L}K_A(3 + 32d²)ν_n‖𝒜‖.
  {#W10.4.14-10} No bound on J itself is used.

{#W10.4.15} Since ν_n ≤ c_F(Mα₀ + α₁ + α₁²)L^{−βn}, on every block y of run A's shell n ≥ 1,

  {#W10.4.16} sup_{Δ(y)}(|s₁| + L^nε|s₀|) ≤ C_act(β)L^{−βn}‖𝒜‖_{1,β;y},
  {#W10.4.17} C_act(β) := 32k_b + c_F(Mα₀ + α₁ + α₁²)C_{5L}K_act, K_act := 16(256d² + 8k_l) + 8k₂′(1 + 32d²) + 16k₂(4d + 32d²) + 16dk₂ + 128d²k₂ + 32d²k_ν + 8C₂′K_A(3 + 32d²),

{#W10.4.18} and the action part has no s₂-source.
{#W10.4.18-1} On run A's shell 0 and run B's extra shell, β_∂ and the terms above hold with ϖ = 1.
{#W10.4.18-2} There each bound above holds with L^{−βn} and ν_n replaced by 1, since ν_0 ≤ 1; the fine Hessian on the extra shell gives |s₁| ≤ 4‖𝒜‖ from the curl and (ε/L)|s₀| ≤ O(1)‖𝒜‖ from Δ′ under (3.37), and the cut coarse plaquettes give ε|s₀| ≤ O(C_{5L})‖𝒜‖ as in 10.2's boundary bullet.
{#W10.4.18-3} The Hölder bound of the sources at β′ < β follows through their sup: distinct points of T_{ε/L} are at least ε/L apart, so the Hölder quotient at the scale L^nε is at most 2(L^nε)^{β′}(ε/L)^{−β′} times the sup, with the factor 2 of the transports at complex backgrounds, which gives the rate L^{β′}L^{−(β−β′)n}.

{#W10.4.20} *DRD*: the weighted form.* The sources of the gauge-fixing part depend on 𝒜 through G′_□ and C_□, so they are not bounded by the norm of 𝒜 on the same block.
{#W10.4.20-1} For a block y of the shell n let

  {#W10.4.21} ⟨𝒜⟩_y := sup_{y‴}e^{−δ_gfd(y,y‴)}(ℓ_n/ℓ_{n‴})‖𝒜‖_{1,β;y‴}, δ_gf := δ₀/486,

{#W10.4.22} with n‴ the shell of y‴.
{#W10.4.22-1} The local norm is at most ⟨𝒜⟩_y, so the parts above satisfy the weighted form too.
{#W10.4.22-2} §5(c) uses the weighted form unchanged except for the rate.
{#W10.4.22-3} Leg 2 gives ⟨u_B⟩_{y″} ≤ 3e^{2δ₀}B₀(β)ℓ_ne^{−δ_gfd(y″,y′)}|g|, since ℓ_n/ℓ_{n‴} times the factor ℓ_{n‴} of ‖u_B‖_{1,β;y‴} is ℓ_n, and e^{−δ_gfd(y″,y‴)−δ₀d(y‴,y′)} ≤ e^{−δ_gfd(y″,y′)}.
{#W10.4.22-4} Leg 1 runs at δ₀′ (10.1), so §5(c) holds for G_□ at the rate δ_gf′/3, δ_gf′ := min(δ_gf, δ₀′), with the conditions of (W-c) at δ_gf′.
{#W10.4.22-5} Its count condition is (2.59) at the rate δ_gf′/3, which is α = 1/1458 relative to δ₀ when δ_gf′ = δ_gf.

{#W10.4.23} *DRD*: the identity.* R_X = 1 − G′_XQ′_X*C_XQ′_XG′_X (PBG (3.20)–(3.25), p.394, at the local operators), and R_X is symmetric for the bilinear pairing at complex backgrounds by analyticity.
{#W10.4.23-1} As in the Cauchy note's *The Gauge-Fixing Part of β.* and *Functional Form.*,

  {#W10.4.24} β_gf(ℱ, 𝒜) := ⟨D_A*χ_AQ₁ℱ, r_A⟩_A − ⟨D_B*ℱ, r_B⟩_B, r_X := R_Xf_X, f_A := D_A*χ_AQ₁𝒜, f_B := D_B*𝒜.

{#W10.4.25} With D_A*Q₁ℱ = Q′₁D_B*ℱ + e_f(ℱ), e_f(ℱ) := D_A*(Q^{str} − Q̂_f)ℱ + X_f(ℱ) (the Cauchy note's identity (iii) and *Functional Form.*),

  {#W10.4.26} β_gf(ℱ, 𝒜) = ⟨D_B*ℱ, s₂⟩_B + ⟨e_f(ℱ), r_A⟩_A, s₂ := Q′₁*r_A − r_B = Q′₁*δr − (1 − Q′₁*Q′₁)r_B, δr := r_A − Q′₁r_B.

{#W10.4.27} The term ⟨e_f(ℱ), r_A⟩_A gives s₁ and s₀ as in the Cauchy note: |s₁| ≤ C_ld sup_{cell}ε|D_Ar_A| + C_{5L}C_trε²|F||r_A| and |s₀| ≤ C_{5L}C_trε|F||r_A|, C_ld := 2 + 4dL^{d−1}.
{#W10.4.27-1} The identity stays exact with X_f(ℱ) including the terms D_A*((χ_A − 1)Q₁ℱ) at the bonds cut by χ_A.
{#W10.4.27-2} They lie in run A's shell 0, where ϖ = 1, and are of order one there: they give sources with ε|s₀| ≤ 8dC_{5L}|r_A|.
{#W10.4.27-3} The bound of X_f below holds away from them.

{#W10.4.28} *DRD*: the defect of the projection.* Write μ_X := C_XQ′_XG′_Xf_X and φ_X := G′_XQ′_X*μ_X, so r_X = f_X − φ_X.
{#W10.4.28-1} Split μ_B = (μ_B¹, μ_B⁰) along 𝔇^A ⊕ 𝔇^B_0, so that Q′_B*μ_B = Q′₁*Q′_A*μ_B¹ + μ_B⁰.
{#W10.4.28-2} By Q′₁G′_B = 𝔈 + G′_AQ′₁ on Ω₀^A (§4(d), 10.3) and Q′₁Q′₁* = 1 (the Cauchy note's identity (i)),

  {#W10.4.29} δr = e_f(𝒜) − G′_AQ′_A*(μ_A − μ_B¹) + 𝔈Q′₁*Q′_A*μ_B¹ + Q′₁G′_Bμ_B⁰,
  {#W10.4.30} μ_A − μ_B¹ = (C^A − [C^B]_{11})Q′_AG′_Af_A − [C^B]_{11}Q′_A(𝔈f_B − G′_Ae_f(𝒜)) − [C^B]_{12}(G′_Bf_B)⁰,

{#W10.4.31} using f_A = Q′₁f_B + e_f(𝒜) and (Q′_BG′_Bf_B)¹ = Q′_AQ′₁G′_Bf_B.
{#W10.4.31-1} Each term carries one small factor:
- {#W10.4.32} e_f(𝒜): (Q^{str} − Q̂_f)𝒜 is a weighted sum of ε times fine difference quotients ∇𝒜, of total weight at most C_ldε per fine bond, so its coarse divergence is a difference of averages of ∇𝒜 within one cell.
  {#W10.4.32-1} By the chains of 10.2 it is at most 2dC_ld·3d(L^{−βn} + 2δ_T(n))⟨𝒜⟩_y, and X_f(𝒜) adds at most 2C_trν_n⟨𝒜⟩_y;
- {#W10.4.33} C^A − [C^B]_{11}: the relative factor L^{−βmin} of 10.3 at general points;
- {#W10.4.34} 𝔈: the relative factor L^{−βm} of (E-gen), m the layer of its output point.
  {#W10.4.34-1} In [C^B]_{11}Q′_A𝔈f_B, 𝔈 also acts on f_B on run B's extra shell.
  {#W10.4.34-2} There χ_Aℒ′*g = 0, so 𝔈g = χ_AQ′₁G′_Bg, and the proof of (E-gen) applies unchanged, since the source block enters it only through leg 2;
- {#W10.4.35} μ_B⁰ and [C^B]_{12}: an intermediate point v of the composition lies on run B's extra shell, the layer −1.
{#W10.4.36} In the per-block form of 10.3, |f_X| ≤ 2d⟨𝒜⟩_y, |G′f| ≤ B₀ℓ²·2d⟨𝒜⟩, |μ| ≤ B₀²ℓ^{−2}·2d⟨𝒜⟩, and |φ| ≤ B₀³·2d⟨𝒜⟩, each at the layer of the point, with the counts and the Ad factor 2 of Q′ and Q′* at complex backgrounds.
{#W10.4.36-1} The factors Q′ and Q′* have range one block and add only the factor L^d, so each term of δr is, up to them, a product of at most three decaying kernels: G′ (rate δ₀), C^A − [C^B]_{11} or a block of C^B (rate δ₀/27, 10.3), and G′ or 𝔈 (rate δ₀/3).
{#W10.4.36-2} The first composition is at κ = δ₀/27 and gives the rate δ₀/81; the second is at κ = δ₀/81 and gives the rate δ₀/243.

{#W10.4.37} The smallness of each term sits at an intermediate point or at the input point, and it is extracted inside (Comp) of 10.3.
{#W10.4.37-1} The relative factor L^{−βmin(j_y,j_{y′})} of C^A − [C^B]_{11} at its data points y and y′ (#W10.3.35) is max(L^{−βj_y}, L^{−βj_{y′}}) ≤ L^{−βj_y} + L^{−βj_{y′}}, so that term splits into two, each with the factor of one data point, at the cost of a factor 2; y is the intermediate point of the first composition and y′ that of the second. The factor L^{−βm} of 𝔈 sits at its output point, which is x in 𝔈Q′₁*Q′_A*μ_B¹ and an intermediate point in [C^B]_{11}Q′_A𝔈f_B.
{#W10.4.37-2} A factor at x is L^{−βn} already; one at an intermediate point w is the power (ℓ_{m_w}/ε)^{−β} and is moved to the layer of x by (Comp), at the cost L^{|p+q|}.
{#W10.4.37-3} Each per-block bound carries its layer power at its output point: ℓ² for G′ and 𝔈 (#W10.3.7, #W10.3.8), ℓ^{−4} for C and its blocks (#W10.3.6, #W10.3.30-1, #W10.3.32), none for Q′ and Q′*. So the left factor of each composition has no power at the intermediate point, and p + q is the output power of the right factor, minus β if a smallness factor sits there: −4 or −4 − β in the first composition, 2 or 2 − β in the second, in every term of #W10.4.29–#W10.4.30. Hence |p + q| ≤ 4 + β ≤ d + 6 + β, the value the constants below are written with.
{#W10.4.37-4} For μ_B⁰ and [C^B]_{12}, the crossing third of (Comp) gives the layer m_v = −1 of the intermediate point the factor L^{|p+q|}L^{−(|m_v − m_x| − 1)₊} ≤ L^{|p+q|}L^{−n}.
{#W10.4.37-5} After the second composition sums the remaining intermediate layer, this is at most (n + 2)L^{2(d+7)}L^{−(n−1)} ≤ C_v(β)L^{−βn}, with C_v(β) := L^{2d+15}sup_n(n + 2)L^{−(1−β)n}.
{#W10.4.37-6} So the kernel K of each term from the field f_X to δr satisfies |K(x←w)| ≤ c(β)L^{−βn}ℓ_{m_x}^{p}e^{−(δ₀/243)d(x,w)}, under (2/243)δ₀R₀M₀ ≥ (d + 8)log L and (2.59) at α = 1/243.

{#W10.4.38} The pairing with the weighted norm uses ‖f_X‖ at w ≤ 2d(ℓ_{n_w}/ℓ_n)e^{δ_gfd(y,w)}⟨𝒜⟩_y for x ∈ Δ(y).
{#W10.4.38-1} Since δ_gf = δ₀/486 is half the kernel rate, e^{−(δ₀/243)d(x,w)+δ_gfd(y,w)} ≤ e^{δ_gf diam Δ(y)}e^{−(δ₀/486)d(x,w)}.
{#W10.4.38-2} Half of the remaining rate gives the count N(δ₀/972).
{#W10.4.38-3} The other half absorbs what sits at the input point w: the layer ratio ℓ_{n_w}/ℓ_n and the factor L^{−βn_w} of e_f(𝒜)(w), at the cost (3 + 2/(L − 1))L^{β+1}.
{#W10.4.38-4} This holds under (1/486)δ₀R₀M₀ ≥ (β + d + 7)log L, which implies the conditions of the compositions.
{#W10.4.38-5} So |δr| ≤ c_δL^{−βn}⟨𝒜⟩_y under (1/486)δ₀R₀M₀ ≥ (β + d + 7)log L and (2.59) at α = 1/972.
{#W10.4.38-6} Here c_δ is the sum of the four contributions.
{#W10.4.38-7} Each is a product of B₀, C_gen(β), C_C(β), C_v(β), L^d, the Ad factors, the counts N(δ₀/k) for k ≤ 972, (Comp)'s factors (3 + 2/(L − 1))L^{d+7}, the pairing's factor, 2d, and the factor 2 of #W10.4.37-1, and e_f contributes 2dC_ld·3d(1 + 64d²) + 2C_tr.

{#W10.4.39} *DRD*: the other sources.*
- {#W10.4.40} (1 − Q′₁*Q′₁)r_B is the deviation of r_B from its average over a block of side ε.
  {#W10.4.40-1} For f_B = D_B*𝒜, a sum of d differences, the chains of 10.2 give at most 2d·d(L^{−βn} + 2δ_T(n))⟨𝒜⟩_y.
  {#W10.4.40-2} For φ_B the deviation needs ℓ¹-chains of length up to dε, and the block average transports along the paths Γ_{y,x}, so it is at most dε|∇φ_B| + δ_T(n)|φ_B| ≤ (dL^{−n} + δ_T(n))B̂₀·2d⟨𝒜⟩_y, by the ∇G′ entry of (3.42) and ε/ℓ_n = L^{−n}.
  {#W10.4.40-3} Here B̂₀ is B₀³ times the counts and the Ad factors of the per-block bounds above.
- {#W10.4.41} ε|D_Ar_A|: the coarse differences of f_A are differences of averages of ∇𝒜 within a 4-cell, at most 4d·4d(L^{−βn} + 2δ_T(n))⟨𝒜⟩_y, and the non-main terms of Q₁ add at most 4C_trν_n⟨𝒜⟩_y (the Cauchy note's *Functional Form.*).
  {#W10.4.41-1} Those of φ_A are at most L^{−n}B̂₀·2d⟨𝒜⟩_y.
  {#W10.4.41-2} The link transports add δ_T(n)|r_A|.
- {#W10.4.42} |r_A| ≤ (1 + B̂₀)2d⟨𝒜⟩_y, so the transport sources satisfy ℓ_n|s₀| + C_{5L}C_trε²|F||r_A| ≤ 2C_{5L}C_trν_n(1 + B̂₀)2d⟨𝒜⟩_y.
{#W10.4.43} Hence, on every block y of run A's shell n ≥ 1,

  {#W10.4.44} sup_{Δ(y)}(|s₂| + |s₁| + ℓ_n|s₀|) ≤ C_gf(β)L^{−βn}⟨𝒜⟩_y,

{#W10.4.45} with

  {#W10.4.46} C_gf(β) := 2c_δ + 2d²(1 + 64d²) + 2dB̂₀(d + 32d²) + C_ld[16d²(1 + 64d²) + 4C_tr + 2dB̂₀ + 64d³(1 + B̂₀)] + 4dC_{5L}C_tr(1 + B̂₀),

{#W10.4.47} using |s₂| ≤ 2|δr| + |(1 − Q′₁*Q′₁)r_B| (the factor 2 for Q′₁* at complex backgrounds), δ_T(n) ≤ 32d²ν_n, and ν_n ≤ L^{−n} ≤ L^{−βn} under c_F(Mα₀ + α₁ + α₁²) ≤ 1.
{#W10.4.47-1} On the boundary shells the same holds with ϖ = 1.
{#W10.4.47-2} The Hölder bound of s₂ at β′ < β follows as in 10.2 through its sup, at the rate L^{−(β−β′)n}.

{#W10.4.48} *The current.* The local operators of PBG Sect. C carry no current.
{#W10.4.48-1} The background's own current enters the action part only through the identity above, where summation by parts moves D* onto C₁^{(2)}.
{#W10.4.48-2} The current of the pair class enters G₁ and H₁ of Sect. D, which §6 treats.

{#W10.4.49} *The commutator factors K(h), P_{□,1}(∂h), and S_j(∂h).* These are the explicit factors of the walk terms that carry ∂h_□ (PBG (3.88), (3.101)–(3.105)), whose defects §7 assigns to (Wδ-1).
{#W10.4.49-1} Each is a commutator of h := h_□ with an operator whose defect is derived above.
- {#W10.4.50} *The identities.* By (3.88), the scalar factor of G′_□ is K′(h) = [h, Δ′_a].
  {#W10.4.50-1} By (3.101), P₁(∂h) = [DPD*, h], and by (3.104), K(h) = [h, Δ_a] − P₁(∂h) = [h, O_loc], O_loc := Δ_a + DPD* = D*D + Δ′ + DD* + Q*aQ, since DRD* = DD* − DPD* (p.414 l.3).
  {#W10.4.50-2} In the same way P_{□,1}(∂h) = [DP_□D*, h] = [DD*, h] − [DR_□D*, h], with R_□ the R_X of *DRD*: the identity.* at the local operators; (3.105) follows from (3.104) with this P_{□,1}, (1 − ζ)h_□ = 0, and the agreement h_□Δ_a = h_□Δ_{a,□} + h_□(DP_□D* − DPD*) of the global and local entries on supp h_□ and one block more, which (3.105) uses as printed.
  {#W10.4.50-3} S_j(∂h) of (3.102) enters only through [h, Q*aQ] = S*aQ − Q*aS ((3.103)), so it is part of the entry Q*aQ of O_loc.
  {#W10.4.50-4} PBG's K(h) is the commutator with the global Δ_a and DPD*.
  {#W10.4.50-5} Every entry of O_loc is a local operator of range at most one block, so [h, O_loc] reads O_loc only within one block of supp ∂h_□, where the global entries carry the global layers n′ at these points, n′ ≤ j + 1 in the present notation, j the scale of □ (§12, *The partition functions of a corner cube.*, where the letters are exchanged).
  {#W10.4.50-6} The defect computations below are per point, so they hold for these entries unchanged; at a finer global layer n′ < j the gain is ϖ_{n′} in place of ϖ_j, and supp ∂h_□ ⊂ X̃ gives n′ ≥ m(ω).
  {#W10.4.50-7} The factor [□̃Q′G′²_□Q′*, h_□]C_□h_□ of the third sum of (3.95) reduces, by [G′_□, h] = G′_□K′(h)G′_□ ((3.88)) and the Leibniz rule, to a sum of four products with the factors K′(h), the scalar averaging commutators [h, Q′], and their adjoints [Q′*, h], which §7 treats; the telescoping applies to each product, and the factor 4 is absorbed in the factor's O(M^{−1}).
  {#W10.4.50-8} Here K′(h) is the commutator with □'s local Δ′_a, which equals the global one on supp h_□ and one block more by the agreement above.
- {#W10.4.51} *The exact form.* For an explicit operator 𝒦, restricted to Ω₀ as 𝒪^X is, put k_𝒦(ℱ, 𝒜) := ⟨χ_AQ₁ℱ, 𝒦^Aχ_AQ₁𝒜⟩_A − ⟨ℱ, 𝒦^B𝒜⟩_B, as β_□ is defined for 𝒪 in §4. h is one smooth function of the point in both runs, multiplication by it is symmetric for the bilinear pairings and commutes with χ_A, and hχ_AQ₁ℱ = χ_AQ₁(hℱ) + χ_A[h, Q₁]ℱ.
  {#W10.4.51-1} So for 𝒦 = [h, O],

  {#W10.4.52} k_{[h,O]}(ℱ, 𝒜) = β_O(hℱ, 𝒜) − β_O(ℱ, h𝒜) + ⟨χ_A[h, Q₁]ℱ, O^Aχ_AQ₁𝒜⟩_A − ⟨χ_AQ₁ℱ, O^Aχ_A[h, Q₁]𝒜⟩_A,

  {#W10.4.53} exactly, with β_O the defect of O.
- {#W10.4.54} *The entries O.* Each β_O has the form of (Wδ-1): Δ′_a by 10.2, D*D + Δ′ by the action part above, Q*aQ by §5(a), exact up to run B's extra shell (the one-form Q*aQ carries the plain a; the weights a_n are those of the scalar Q′*aQ′ in Δ′_a), and DR_□D* by the gauge-fixing part above, in the weighted norm ⟨𝒜⟩_y.
  {#W10.4.54-1} DD* is the case R_X = 1 of *DRD*: the identity.*: there r_X = f_X and δr = e_f(𝒜), and the sources are the f-parts of *DRD*: the other sources.*, |s₂| ≤ 2|e_f(𝒜)| + 2d²(L^{−βn} + 2δ_T(n))‖𝒜‖_{1,β;y}, with s₁ and s₀ from ⟨e_f(ℱ), f_A⟩_A as there with f_A for r_A.
  {#W10.4.54-2} No G′_X or C_X enters, so these sources are bounded through 𝒜 on y and its adjacent blocks, with no decay weight.
  {#W10.4.54-3} Write C_O for the constant of β_O.
- {#W10.4.55} *The two h-terms.* On each run's lattice D_B*(hℱ) = hD_B*ℱ + (∂h)⋆ℱ and ∇(hℱ) = h∇ℱ + (∂h)⋆ℱ, with (∂h)⋆ the products with the lattice differences of h at points shifted by at most one bond.
  {#W10.4.55-1} So β_O(hℱ, 𝒜) has the sources hs₂, hs₁, and hs₀ + (∂h)⋆(s₁ + s₂).
  {#W10.4.55-2} The shells of □'s local sequence have n ≤ j + 1. h_□ is the partition function of #W7.16-11, with |∂^kh| ≤ c_h(Mℓ_j)^{−k} for k ≤ 3 (#W7.2-1-1; at the corner cubes, §12, *The partition functions of a corner cube.*), and ℓ_n|∂h| and ℓ_n²|∂²h| are ≤ c_hL/M, using M ≥ L. The shifted points can read the sources of an adjacent block y′ in the shell n ± 1.
  {#W10.4.55-3} Its bound C_Oϖ_{n±1}‖𝒜‖_{1,β;y′} converts to y through the layer ratio ≤ L, the ratio ϖ_{n−1}/ϖ_n = L^β, and the blocks within distance 3 of y in place of 2, which costs leg 2 of §5(c) the factor e^{δ₀}.
  {#W10.4.55-4} Hence these sources obey the bound of β_O times 1 + 2dc_hL^{2+β}/M in ‖·‖_{1,β;y}, read at the blocks within distance 3 of y; in the bound of the factor, leg 2 pays these blocks with e^{δ₀}, so the source term enters C_{[h,O]} below with 2dc_hL^{2+β}e^{δ₀}/M.
  {#W10.4.55-5} In ⟨·⟩_y the ℓ-ratio and the ϖ-ratio combine to at most L^{1−β}e^{δ_gf} ≤ 2L, so there the factor is at most 1 + 4dc_hL²/M.
  {#W10.4.55-6} For β_O(ℱ, h𝒜), the Hölder quotient of (3.40) runs over pairs of points in the blocks within distance 2 of y, so |x − x′| ≤ 5√dLℓ_n, and ℓ_n^β[h]_β ≤ (5√dL)^{1−β}ℓ_n|∂h|.
  {#W10.4.55-7} With |h| ≤ 1, the terms ℓ_n|∂h||𝒜| of the sup part and [h]_β|∇𝒜|, |∂h|[𝒜]_β, and [∂h]_β|𝒜| of the Hölder part give ‖h𝒜‖_{1,β;y} ≤ (1 + 4c_hL(5√dL)^{1−β}/M)‖𝒜‖_{1,β;y}, and ⟨h𝒜⟩_y ≤ (1 + 4c_hL(5√dL)^{1−β}/M)⟨𝒜⟩_y in the same way, since the supremum defining ⟨·⟩_y runs over shells n‴ ≤ j + 1.
  {#W10.4.55-8} The Hölder bounds of the sources at β′ < β carry these factors with β′ for β, since [hs]_{β′} ≤ [s]_{β′} + [h]_{β′}sup|s| and ℓ_n^{β′}[h]_{β′} ≤ (5√dL)^{1−β′}c_hL/M.
- {#W10.4.56} *The two commutators with Q₁ at the local entries.* Q₁ averages over fine bonds b′ within the ℓ∞ distance 2ε of the coarse bond b (10.1, *The condition (S).*, which covers the non-main terms of CMP 98 (124)) with total weight at most w_Q := 2(1 + O(L²α₀)) ≤ 3 at complex backgrounds: the main term has weight 1, and each non-main term of (124) is a sum over the L^d points x ∈ B(c₋) of L^{−(d+1)} times an operator of norm O(L²α₀) (CMP 98 p.36 l.31–33) applied to a path sum of at most dL bonds, so of weight O(L²α₀), as (126) states; both are multiplied by the Ad factor 2, and O(L²α₀) ≤ ½ (§8, stage 4).
  {#W10.4.56-2} The fine bonds b′ lie within the ℓ¹ distance (2d + 1)ε of the base point of b, where h(b) is taken (PBG (3.102) takes h at c₋), so [h, Q₁]u(b) = Σ_{b′}w(b, b′)(h(b) − h(b′))u(b′) and |[h, Q₁]u| ≤ 3(2d + 1)ε|∂h|sup_{tube}|u|.
  {#W10.4.56-3} For the adjoints the row sums become column sums.
  {#W10.4.56-4} In the pairings the coarse bonds carry the weight ε^d and the fine bonds (ε/L)^d, so Q₁* has the kernel L^dw(b, b′) from the coarse bond b to the fine bond b′, and [Q₁*, h] = [h, Q₁]* the kernel L^dw(b, b′)(h(b) − h(b′)).
  {#W10.4.56-5} A fine bond b′ is within the ℓ∞ distance 2ε of at most 6·5^{d−1} coarse bonds of each direction (5 base-point values in each transverse coordinate, 6 in the bond's own), and each |w(b, b′)| is at most the total weight w_Q ≤ 3, with the non-main terms of (124) included.
  {#W10.4.56-6} So the column sums Σ_bL^d|w(b, b′)| are at most C_col := 18d5^{d−1}L^d, |Q₁*v| ≤ C_col sup|v|, and |[Q₁*, h]v| ≤ C_col(2d + 1)ε|∂h|sup|v|, the supremum over the coarse bonds within 2ε of the output bond.
  {#W10.4.56-7} Both terms live within one block of supp ∂h_□, at local shells n ≤ j + 1 (n < j is possible for the intersected sequences of §7 and §12), away from the bonds cut by χ_A unless n = 0, where ϖ = 1.
  {#W10.4.56-8} Let O be one of the local entries Δ′_a, D*D + Δ′, DD*, and Q*aQ, of second order on run A's lattice with the coefficient bound C′_O.
  {#W10.4.56-9} On a field u that is C^{1,β} at the shell n its second differences at the spacing ε are at most ε^{−1}L^{−βn}‖u‖_{1,β;y}, its lower-order terms being smaller (for Q*aQ, |Q*aQu| ≤ aℓ_n^{−2}|u| ≤ aε^{−1}L^{−n}‖u‖_{1,β;y}).
  {#W10.4.56-10} Those of χ_AQ₁𝒜 are averages of those of 𝒜 up to the link transports, at most (1 + 64d²)ε^{−1}L^{−βn}‖𝒜‖_{1,β;y} (δ_T(n) ≤ 32d²ν_n, as in *DRD*: the other sources.*).
  {#W10.4.56-11} In the second differences of [h, Q₁]𝒜 the differences fall either on 𝒜, giving 3(2d + 1)ε|∂h| times those of 𝒜, or on the differences of h, giving at most 3(2d + 1)ε(2|∂²h||∇𝒜| + |∂³h||𝒜|), which relative to the first is at most 3L/M by the bounds on ∂^kh.
  {#W10.4.56-12} Each commutator term is therefore ⟨ℱ, s₀⟩ with s₀ = [Q₁*, h]χ_AO^Aχ_AQ₁𝒜 or Q₁*χ_AO^Aχ_A[h, Q₁]𝒜, and ℓ_n|s₀| ≤ C_QC′_Oc_hL^{n−j}M^{−1}L^{−βn}‖𝒜‖_{1,β;y} ≤ C_QC′_Oc_hLM^{−1}ϖ_n‖𝒜‖_{1,β;y}, C_Q := 4C_col(2d + 1)(1 + 64d²)(1 + 3L/M), the first term carrying the factor C_col(2d + 1) of [Q₁*, h] and the second the factor C_col of Q₁* times 3(2d + 1)(1 + 3L/M) of [h, Q₁].
- {#W10.4.57} *The nonlocal entry DR_□D*.* R_□ contains G′ and C, so DR_□D* has no coefficient bound.
  {#W10.4.57-1} Its two commutator terms are bounded in ⟨·⟩_y through the bounds of *DRD*: the other sources.* and the per-block bounds of *DRD*: the defect of the projection.*.
  - {#W10.4.58} The first term.
    {#W10.4.58-1} It is ⟨χ_A[h, Q₁]ℱ, D_Ar_A⟩_A with r_A = R_□f_A, f_A = D_A*χ_AQ₁𝒜, so s₀ = [Q₁*, h]χ_AD_Ar_A.
    {#W10.4.58-2} *DRD*: the other sources.* gives ε|D_Ar_A| ≤ C_rL^{−βn}⟨𝒜⟩_y on Δ(y), with C_r := 16d²(1 + 64d²) + 4C_tr + 2dB̂₀ + 64d³(1 + B̂₀), the bracket of C_gf(β).
    {#W10.4.58-3} With the adjacent blocks, whose weights cost e^{2δ_gf} ≤ 2 and whose layer ratio is at most L, and the column sums C_col of [Q₁*, h], ℓ_n|s₀| ≤ 2C_col(2d + 1)LC_rc_hL^{n−j}M^{−1}L^{−βn}⟨𝒜⟩_y ≤ 2C_col(2d + 1)C_rc_hL²M^{−1}L^{−βn}⟨𝒜⟩_y.
  - {#W10.4.59} The second term.
    {#W10.4.59-1} By DR_□D* = DD* − DP_□D*, it is the local entry DD* above minus ⟨D_A*χ_AQ₁ℱ, φ_v⟩_A, with v := χ_A[h, Q₁]𝒜 and φ_v := G′Q′*CQ′G′D_A*v at run A's local operators (P_□ = G′Q′*CQ′G′, *DRD*: the identity.*).
    {#W10.4.59-2} By D_A*Q₁ℱ = Q′₁D_B*ℱ + e_f(ℱ) this is ⟨D_B*ℱ, Q′₁*φ_v⟩_B + ⟨e_f(ℱ), φ_v⟩_A.
    {#W10.4.59-3} So it gives the source s₂ = Q′₁*φ_v and, as for r_A in *DRD*: the identity.* with φ_v for r_A, sources with |s₁| ≤ C_ld sup_{cell}ε|D_Aφ_v| + C_{5L}C_trε²|F||φ_v| and |s₀| ≤ C_{5L}C_trε|F||φ_v|, and with ε|s₀| ≤ 8dC_{5L}|φ_v| at the bonds cut by χ_A, where ϖ = 1.
  - {#W10.4.60} The size of φ_v. φ_v is needed at every block y of run A's local sequence, since the slot map ℒ̃ reads the sources everywhere (*The entry into the telescoping.*).
    {#W10.4.60-1} Let y lie in the shell n and x ∈ Δ(y). v lives within one block of supp ∂h_□, at local shells n_w ≤ j + 1 (n_w < j is possible for the intersected sequences of §7 and §12), where |v(w)| ≤ 3(2d + 1)ε|∂h||𝒜(w)| and |𝒜(w)| ≤ ℓ_{n_w}(ℓ_{n_w}/ℓ_n)e^{δ_gfd(y,w)}⟨𝒜⟩_y.
    {#W10.4.60-2} G′D_A* has the bound B₀ℓ of the entry G∇* of (3.42), so, with the per-block bounds of *DRD*: the defect of the projection.* and its intermediate layers summed by (Comp) of 10.3, the kernel of G′Q′*CQ′G′D_A* from v at w to φ_v at x is at most B̃₀ℓ_{n_w}^{−1}L^{|n−n_w|}e^{−(δ₀/243)d(x,w)}, with B̃₀ the B̂₀ of *DRD*: the other sources.* times (Comp)'s factor, and the factor L^{|n−n_w|} moving the power of ℓ between the layers of the two end points; εD_A at x adds at most the factor ε/ℓ_n ≤ 1.
    {#W10.4.60-3} Since ℓ_{n_w}/ℓ_j ≤ L, the product is at most 3(2d + 1)B̃₀c_h(ε/ℓ_j)(ℓ_{n_w}/ℓ_n)L^{|n−n_w|}M^{−1} ≤ 3(2d + 1)LB̃₀c_h(ε/ℓ_n)L^{|n−n_w|}M^{−1}.
    {#W10.4.60-4} The pairing is that of *DRD*: the defect of the projection.*: δ_gf is half the kernel rate, which leaves e^{−(δ₀/486)d(x,w)} after the factor e^{δ_gf diam Δ(y)}; half of the rest gives the count N(δ₀/972), and the other half pays the layer factor.
    {#W10.4.60-5} By (2.60), d(x, w) ≥ 2R₀M₀(|n − n_w| − 1)₊, and the same holds for the intersected sequences, which satisfy PRT2 (2.1)–(2.4) at the size R₀M₀ (§7, *The cubes next to the finer layer.*; §12, *PBG's bounds for them.*).
    {#W10.4.60-6} So L^me^{−(δ₀/486)R₀M₀(m−1)₊} ≤ L for m := |n − n_w| under (1/486)δ₀R₀M₀ ≥ (β + d + 7)log L, the condition of that bullet.
    {#W10.4.60-7} Hence, at every block y of the shell n, |φ_v| + ε|D_Aφ_v| ≤ c_φc_hLM^{−1}L^{−n}⟨𝒜⟩_y on Δ(y), c_φ := 12(2d + 1)LB̃₀N(δ₀/972), the factor 4 being 2 for |φ_v| + ε|D_Aφ_v| and 2 for e^{δ_gf diam Δ(y)}.
    {#W10.4.60-8} The factor ε of [h, Q₁] against the derivative in G′D_A* gives ε/ℓ_n = L^{−n} ≤ L^{−βn}, which supplies ϖ_n at the output block; on the boundary shells ϖ = 1.
  - {#W10.4.61} Together, with the F-terms as in *DRD*: the identity.*, sup_{Δ(y)}(|s₂| + |s₁| + ℓ_n|s₀|) ≤ C″_gfc_hLM^{−1}ϖ_n⟨𝒜⟩_y for the two commutator terms of DR_□D*, C″_gf := 2C_col(2d + 1)LC_r + C_QC′_{DD*} + (2 + C_ld + 2C_{5L}C_tr + 8dC_{5L})c_φ.
    {#W10.4.61-1} The Hölder bounds of the new sources s₂ = Q′₁*φ_v and s₁ at β′ < β follow as in 10.2 through their sup, at the rate L^{−(β−β′)n}, as for s₂ in *DRD*: the other sources.*
- {#W10.4.62} *The result.* k_{[h,O]} has the form of (Wδ-1) with the constant C_{[h,O]}(β) := (2 + (2dL^{2+β}e^{δ₀} + 4L(5√dL)^{1−β})c_h/M)C_O + 2C_QC′_Oc_hL/M in ‖·‖_{1,β;y} for the local entries, and C_{[h,DR_□D*]}(β) := (2 + (4dL² + 4L(5√dL)^{1−β})c_h/M)C_gf(β) + C″_gfc_hL/M in ⟨·⟩_y for DR_□D*.
  {#W10.4.62-1} This holds for K′(h) with O = Δ′_a, for K(h) with O = O_loc, and for P_{□,1}(∂h) as the difference of the entries DD* and DR_□D*, with C_{[h,DD*]} + C_{[h,DR_□D*]} in ⟨·⟩_y.
  {#W10.4.62-2} O and h are symmetric, so [h, O] is antisymmetric and k_{[h,O]}(𝒜, ℱ) = −k_{[h,O]}(ℱ, 𝒜); the form with the two slots exchanged holds with the same constant.
- {#W10.4.63} *The entry into the telescoping.* K and P_{□,1} map fine fields to fine sources, so their intertwining defect in §7 is ℒ*𝒦^B − 𝒦^Aχ_AQ₁, and ⟨X, (𝒦^Aχ_AQ₁ − ℒ*𝒦^B)𝒜⟩_A = k_𝒦(ℒX, 𝒜) for X ∈ 𝔉^A, since χ_AQ₁ℒX = X by (S).
  {#W10.4.63-1} In PBG's series (3.105)–(3.107) every factor K(h_□)G_□h_□ or ζ_{□̃}P_{□,1}(∂h_□)G_□h_□ stands to the right of h_{□′} preceded by a local propagator G_{□′}, of G₀ or of the next factor of R, and the same holds for K′ in (3.90) and in the C-series (pp.411–412). ζ_{□̃} cuts P_{□,1}'s output to □̃, so for P_{□,1} X is supported on □̃; for K, X = h_{□′}G_{□′}(x, ·) is not cut, but the sources of K(h_□) are local (below).
  {#W10.4.63-2} For one-forms the slot map is ℒ̃ = χ_Bℒ_N of 10.1, whose kernel has the tails e^{−½δ_Qd_ε}, so k_𝒦(ℒ̃X, 𝒜) reads the sources at every point of Ω₀^B, weighted by these tails.
  {#W10.4.63-3} For the local entries Δ′_a, D*D + Δ′, DD*, and Q*aQ, and for the first term of DR_□D*, the sources vanish beyond one block of supp ∂h_□, since [h, O] and [h, Q₁] are local there.
  {#W10.4.63-4} For the rest of DR_□D*, the terms β_{DR_□D*}(hℱ, 𝒜) − β_{DR_□D*}(ℱ, h𝒜) and the φ_v term, the sources are bounded at every block of run A's local sequence: by *DRD*: the other sources.* on every block of the shells n ≥ 1, with ϖ = 1 on the boundary shells, and by *The size of φ_v.* So the tails of ℒ̃ are summed as in 10.1, *The cost in §5(c).*, with C_ℒ′ in place of 3^dC_ℒ, the rate δ₀′, and the jump of χ_B at ∂Ω₀^B in run B's extra shell, where ϖ = 1 and §5(c) bounds that shell by L^{−βj}.
  {#W10.4.63-5} So the defect enters as β_□ enters §5(c): leg 2 with u_B = G^B_□h_□g and (Wδ-1) in the form above, and leg 1 with the row w of G_{□′}, by (3.42) for □′'s sequence.
  {#W10.4.63-6} Leg 1 decays in □′'s own metric, as G_{□′} does in the bound of the product (3.108), whose factors each carry the decay of their own cube.
  {#W10.4.63-7} In (H_ℒ) the bracket is taken at the input point c of ℒ̃, with n the shell of c, and the scale of the output point b, where the source is read, enters through the ratio that the tail of ℒ̃ pays (10.1, *The cost in §5(c).*).
  {#W10.4.63-8} At such a point c, let ℓ′ be its scale in □′'s sequence and ℓ_n that in □'s.
  {#W10.4.63-9} At the points of □̃ these differ by at most one layer (for the intersected sequences of §7 both are the global layer, and for those of §12 both are the collar's layer), so ℓ′ ≤ Lℓ_n.
  {#W10.4.63-10} The bracket ℓ′ + ℓ′²/ℓ_n of §5(c)'s leg 1, the gradient entry and the entry (L^nε)^{−1}|w| of (H_ℒ), is then at most (1 + L)ℓ′, against 2ℓ′ when the layers agree: relative to the row's own bound B₀ℓ′, the cost is the factor (1 + L)/2 ≤ L. For K, X = h_{□′}G_{□′}(x, ·) lives on supp h_{□′}, and when □′ is a cube of the layer j + 1 its points c outside □̃³ lie in □'s finer local shells (§7, *The cubes next to the finer layer.*: □'s local sequence equals the global one on □̃³, whose layers there are j and j + 1, or j − 1 and j).
  {#W10.4.63-11} They enter only through the tail of ℒ̃ from the output points b near supp ∂h_□, where the sources of K(h_□) live, and there ℓ′/ℓ_{n_c} ≤ L^{|n_b−n_c|+2}.
  {#W10.4.63-12} So the bracket costs at most L^{|n_b−n_c|+2}; the factor L^{|n_b−n_c|} is the third power that 10.1's tail share pays (*The cost in §5(c).*), and L² goes into C_{[h]}(β).
  {#W10.4.63-13} For the local entries the shell sum of §5(c) reduces to the local shells within one block of supp ∂h_□; for DR_□D* it is §5(c)'s full sum in the weighted form.
  {#W10.4.63-14} That computation gives ≤ C_{[h]}(β)(ε/a_j)^β times the bound of the product with the factor's small O(M^{−1}) of (3.89), or of P₁'s (3.49) bound (p.414 l.12–13), replaced by 1.
  {#W10.4.63-15} Here C_{[h]}(β) is L² times the C_□(β) of §5(c) with C_{[h,O]}(β) for C_df(β) for K′ and K, and for P_{□,1} L times the constant of §5(c) in the weighted form that the gauge-fixing part above uses, at the rate δ_gf′/3, with C_{[h,DD*]} + C_{[h,DR_□D*]}.
  {#W10.4.63-16} With c_KM^{−1} for these O(M^{−1}), the relative defect is therefore 𝔡_c ≤ c_K^{−1}MC_{[h]}(β)(ε/a_{min(j,n′)})^β ≤ c_K^{−1}MC_{[h]}(β)(ε/a_{m(ω)})^β, n′ the finest global layer at supp ∂h_□, and C_w of §8 gains N_cc_K^{−1}MC_{[h]}(β), a constant of M, β, L, d, and Bałaban's constants.
  {#W10.4.63-17} The factor M needs no smallness at the layers in the telescoping: §7's telescoping holds for every value of max_c𝔡_c, with the constant C_tel.
  {#W10.4.63-18} The consumer's smallness C_{Δ𝐇}ϑ_H ≤ 1/6 is met through the LF note's threshold n_H(M) (its (iii), *The condition C_Hϑ_H ≤ 1/6.*).

### 10.5 The Fine-Side Lift ℒ_ι {#WS10.5}

{#WOG.4} **(Wδ-2) The fine side at the decoupled field.** The consumer, the run difference of the localised terms of V(Y), compares functions of each run's own fine field.
{#WOG.4-1} At the chain's configurations the frozen difference handles the fine side through ι, since ι(MU^B) = U^B for a minimiser U^B (LF note (i)).
{#WOG.4-2} The decoupled configuration 𝐔^B(s) at complex s is not a minimiser (LF note (iii), #4.427), so ι(M𝐔^B(s)) ≠ 𝐔^B(s), and the averaged comparison (b) of §3 leaves run B's old term at 𝐔^B(s) against its value at ι_Y𝐔^A(s) uncompared, with ι_Y the one lift of all terms of V(Y) (LF note (i)).
{#WOG.4-3} (Wδ-2) is the fine-side form (c) of §3, per walk term, |(W^B_ω − ℒ_ιW^A_ω𝒥)λ| ≤ δ_w(ω) times the bound (3.108) in run B's norms, with ℒ_ι of §3(c).
{#WOG.4-14} The nonlinearity of the lift at the decoupled configurations of (1.60) is not a walk-factor difference; the LF note treats it as the piece (δ) of its (ii).

{#W10.5.1} *The identification.* ι_YU is Bałaban's local minimiser on Y^∼ with block data U on Ω₁ and collar data Q_1^{s*}U on the fine bonds Λ₀ (the Cauchy note's §9.8).
{#W10.5.1-1} This is PBG's local problem at k = 1, with Ω₀ = Y^∼, η = ε/L, and Q₀ = 1, so that the condition (3.110) at j = 0 prescribes the fine field on Λ₀ (PBG p.417 l.6–18).
{#W10.5.1-2} VAR §G gives the data derivative at a minimiser background U₀: the Landau-gauge field is 𝓗 = 𝒜₁ + H₁B − HD(𝒜₁ + H₁B) (VAR (174)), whose expansion "begins with the first order term H₁B" (VAR p.306 l.9, (177)), with H₁ the solution operator of Δ₁ = Δ_π − Δ_π^{(2)} (VAR p.290 l.19).
{#W10.5.1-3} This is PBG's quadratic form (3.127)–(3.128) under (3.110), and its solution operator is

  {#W10.5.2} H₁B = G₁Q*(QG₁Q*)^{−1}B (PBG (3.129), p.421 l.16–28),

{#W10.5.3} with G₁ the operator of the quadratic form (3.128).
{#W10.5.3-1} VAR computes the minimiser in the Landau gauge of (179)–(180), whose lift H imposes R D*A = 0 as (3.110) does, and transforms it back to the axial gauge by a gauge transformation analytic in the data (VAR p.307 l.1–5).
{#W10.5.3-2} So

  {#W10.5.4} dι_Yv = H₁b(v) + D_Bγ₀(v),

{#W10.5.5} with b(v) the derivative of VAR's data B of (20) and γ₀ the derivative of the return to the axial gauge.
{#W10.5.5-1} On Λ₀, b(v) = 𝔡v := dQ_1^{s*}v, since u = 1 there (VAR p.281 l.2–3).

{#W10.5.6} *The data on Λ₁.* VAR's minimiser U_k(V) has plain-average data, Ū^j = V on Λ_j (VAR (3), p.278 l.10–13), so it is the analogue of ι_Y, and for the local problem ι_Y(V) is VAR's minimiser itself.
{#W10.5.6-1} Its Landau representative U₁ = U′^{u^{−1}} relative to U₀, with \overline{R₀u}^j = 1, has the double bar (Ū̄₁^j)_b = V_b(Ū₀^j)_b^{−1} =: V′_b on the bonds b inside Λ_j (CMP 99 (1.30), p.081, through CMP 98 (92)), and VAR (20) takes B_b = (1/i)log V′_b there (CMP 99 (1.31), p.082 l.2–15).
{#W10.5.6-2} The bonds that cross from Λ₀ to Λ₁ carry the interface twist of the second line of CMP 99 (1.31), which reads the collar data and has vanishing derivative for v vanishing near the collar, the restriction used below.
{#W10.5.6-3} The return to the axial gauge is u(y) = (\overline{R_{0,y}U₁})^{−1} at the coarse sites (CMP 98 (86)–(87), p.031).
{#W10.5.6-4} So b(v) = v on Λ₁, and

  {#W10.5.7} dι_Y[v] = H₁(ι_Yc^A)𝔡v + D_Bγ(v),

{#W10.5.8} with γ the derivative of the return gauge, γ = Θ₁H₁𝔡v at the coarse sites (CMP 98 (87) linearised).
{#W10.5.8-1} The covariance ι_Y(V^υ) = ι_Y(V)^{ῡ}, with ῡ constant on the blocks (equal to υ on Λ₀, hence to 1 there for the υ used here, which is 1 near the collar), is VAR (181) (p.307 l.6–14), extended there to G^c-valued υ near G by analyticity.
{#W10.5.8-2} The constraint of §4 is Q₁ := Q̄₁(ι_Yc^A), for which ℒ_ι (§3(c)) is an exact right inverse on the data of Λ₁.

{#W10.5.9} Write 𝔡v := (dQ_1^{s*}v on Λ₀, v on Λ₁).
{#W10.5.9-1} This subsection treats ℒ_ι of §3(c), in the gauge of RG II's propagators (§1(a)).

{#W10.5.10} In logarithmic units dQ_1^{s*}v equals Lv(c) on the one fine bond of B(c) that carries U(c), and 0 on the other bonds, so |𝔡v| ≤ L|v|.
{#W10.5.10-1} The factor (L^{j′}η)^{−1} of (3.133) below cancels against the scale L^{j′}η of the data of (3.110): in 10.1's connection units ℒ_ι is H₁ in the normalisation of (3.126), for which (3.133) holds without that factor.

{#W10.5.11} *Bounds at real backgrounds.* PBG Theorem 3.12 (p.423 l.33–37): if U satisfies (3.35) and (3.36) with α₀ small, Theorems 3.3, 3.10, and 3.11 hold for G and G₁, except the covariant-Laplacian entry of (3.42), and (3.133) holds for H and H₁.
{#W10.5.11-1} For the variational normalisation of (3.110), (3.133) carries the additional factor (L^{j′}η)^{−1} (p.422 l.31–33), which cancels as stated above.
{#W10.5.11-2} At k = 1 the scales are η on Λ₀ and Lη = ε on Λ₁.
{#W10.5.11-3} Against the pairing measure this gives, at a real background satisfying (3.35)–(3.36) at the scale ε,

  {#W10.5.12} |ℒ_ιv(x)| ≤ B_ιΣ_ce^{−½δ₁d_ε(x,c)}|v(c)|, |∇_Bℒ_ιv(x)| ≤ B_ιε^{−1}Σ_ce^{−½δ₁d_ε(x,c)}|v(c)|,

{#W10.5.13} with B_ι := O(1) of (3.133) and δ₁ of (3.132).
{#W10.5.13-1} The first is the first part of (H_ℒ) for ℒ_ι, at the rate ½δ₁ in place of ½δ_Q.
{#W10.5.13-2} The second is too weak for (H_ℒ): on run A's shell n it loses the factor L^n against (L^nε)^{−1}.

{#W10.5.14} *The refined gradient.* For a coarse field v let Iv be the interpolation of 10.1, and let C̃₁ := G₁ − H₁QG₁.
{#W10.5.14-1} Then C̃₁ is symmetric, C̃₁Q* = 0, and (1 − H₁Q)A = C̃₁G₁^{−1}A for every A, by the algebra of (3.129).
{#W10.5.14-2} Hence

  {#W10.5.15} ℒ_ιv = Iv + H₁(𝔡v − QIv) − C̃₁G₁^{−1}Iv.

- {#W10.5.16} ∇_BIv is bounded as in 10.1's gradient bullet.
- {#W10.5.17} |𝔡v − QIv| ≤ C₁ε|∇_Av| + max(C₁, 1)C_trε²|F||v| on Λ₁, by 10.1's first-order Taylor bound, with I, Q, and F taken at the background ι_Yc^A of H₁ (10.1's U′U^B, the exactness paragraph below).
  {#W10.5.17-1} On Λ₀ this fails: at U = 1 and constant v, Iv is constant on every fine bond while dQ_1^{s*}v is a step field, so 𝔡v − Iv is of order |v| with ∇_Av = 0.
  {#W10.5.17-2} So the bound, and everything below, is for v vanishing on the coarse bonds within one block of those whose fine bonds meet Λ₀; for such v, 𝔡v = Iv = 0 on Λ₀, and the Dirichlet edge ∂Y^∼ is not reached.
  {#W10.5.17-3} With the crude ∇H₁ bound above, ∇_BH₁(𝔡v − QIv) has the form of (H_ℒ), with k₀ carrying ε|F| ≤ c_F(Mα₀ + α₁ + α₁²)L^{−n}(L^nε)^{−1}.
- {#W10.5.18} G₁^{−1} = Δ_π − Δ_π^{(2)} + DRD* + Q*aQ (PBG (3.128), (3.134)–(3.135)).
  {#W10.5.18-1} The term Q*aQIv is annihilated by C̃₁.
- {#W10.5.19} Δ_πIv = P_π*ΔP_πIv with P_π := 1 − DG′RD* ((3.128)), and ΔP_πIv = D*DP_πIv + Δ′P_πIv.
  {#W10.5.19-1} The 2-form DP_πIv is bounded, in the exponentially weighted sup that the final Σ_c form carries, by 2|∇_Av| plus curvature terms of size ε|F||v|, since DDG′RD*Iv = [F, G′RD*Iv].
  {#W10.5.19-2} So C̃₁D*(DP_πIv) is a mixed second derivative of C̃₁ applied to a bounded field.
  {#W10.5.19-3} (3.44) (p.398 l.12–17) bounds ∇G′∇*λ by B₀′(ε_H)e^{−δ₀d}(‖λ‖^{ξ′}_{ε_H} + |λ|) for any Hölder exponent ε_H > 0, with ∇ and ∇* exchangeable in any place (p.398 l.49–50), and Theorem 3.12 transfers it to G₁.
  {#W10.5.19-4} On the fine lattice every bounded field λ has ‖λ‖^{ξ′}_{1/2} ≤ 2L^{1/2}sup|λ| at the scale ε, since distinct points are at least η apart.
  {#W10.5.19-5} So (3.44) at ε_H = ½ for G₁, together with (3.133) and (3.132) for H₁QG₁, bounds ∇_BC̃₁D*(DP_πIv) by O(1)B₀′(½)L^{1/2}Σ_ce^{−½δ₁d_ε}(|∇_Av| + ε|F||v|).
  {#W10.5.19-6} The factor P_π* adds C̃₁DRG′D*(D*DP_πIv).
  {#W10.5.19-7} By the lattice identity D*D* = [F, ·] on 2-forms, D*(D*DP_πIv) is of size |F| times the bound of DP_πIv, and RG′ gains ε², so ε²|F| is the small factor, RG′D*(·) is a bounded scalar, and this term is of the same type.
- {#W10.5.20} DRD*Iv: D*Iv is bounded by |∇_Av| + ε|F||v|, the divergence of an interpolation, so ∇_BC̃₁D(RD*Iv) has the same bound by (3.44).
- {#W10.5.21} Δ′P_πIv is of size |F||v|, and ∇C̃₁ is of size ε against the pairing ((3.42) for G₁ and (3.133)), so its part is at most O(1)ε|F||v|, of the form of k₀.
- {#W10.5.22} Δ_π^{(2)}Iv: by (3.136), its size is C₂ε|Iv| times |H*J|.
  {#W10.5.22-1} The other terms of (3.135) carry the bounded operators DG′RD* and DRG′D* and are treated in the same way.
  {#W10.5.22-2} J is the current of the background of H₁, ι_Y(MU^B) = e^{i(ε/L)T}U^B up to a real gauge transformation, under which J and the bounds below transform covariantly (the Cauchy note's §9.8, *The tail.*), not of U^B.
  {#W10.5.22-3} At a point of run A's shell n, run B's (3.36) on its shell n + 1 gives |J(U^B)| ≤ O(1)Mα₀(L^nε)^{−3}, and the T-part of J enters (3.136) only through H*J (p.422 l.46–47).
  {#W10.5.22-4} J = D*X with X := ξ^{−2}π Im ∂U (RG I p.261 l.33–39), so H*J = (DH)*X, and DH has the gradient bound of (3.133).
  {#W10.5.22-5} The T-part of X reads first differences of T only, |X_T| ≤ O(1)(|∇T| + |F^B||T|) up to terms quadratic in T, smaller by the factor C_ιε₁, and the Cauchy note's §9.8 (*The decay.*) gives |∇T| ≤ C_ι(ε/a)(ε₁/(aε))e^{−δ_ιdist(·,Ω₁^c)/ε}, δ_ι the rate there.
  {#W10.5.22-6} On run A's shell n, dist(·, Ω₁^c) ≥ Σ_{m<n}2R₀M₀L^mε ≥ 2R₀M₀nε by the shell widths of PBG p.408 l.29–35 and the inclusion below, so e^{−δ_ιdist/ε} ≤ L^{−3n} under δ_ιR₀M₀ ≥ (3/2)log L. So |H*J_T| ≤ O(1)C_ιε₁(ε/a)²ε^{−3}L^{−3n}, which is below the bound of the next sentence under C_ιε₁ ≤ Mα₀.
  {#W10.5.22-7} The decay of H at the scale ε transfers the bound to H*J with the factor L³ across shell boundaries, under ½δ₁R₀M₀ ≥ 4 log L. With ∇C̃₁ of size ε, this part is at most O(1)L³C₂Mα₀ε²(L^nε)^{−3}|v| ≤ O(1)L³C₂Mα₀L^{−2n}(L^nε)^{−1}|v|, of the form of k₀.

{#W10.5.23} So, at the background ι_Yc^A = e^{i(ε/L)T}U^B of a real chain configuration c^A = MU^B, with U^B satisfying (3.35) and (3.36) on run B's shells and the T-part of the current as in the last bullet, ℒ_ι satisfies (H_ℒ) for v vanishing near the collar as above, with C_{ℒ,ι} a constant of L, d, G, B₀, B₀′(½), B_ι, C₂, and c_F, at the rate ½δ₁ in place of ½δ_Q, and with δ₀′ := min(δ₀, ¼δ_Q, ¼δ₁, ¼δ_c) in §5(c), the term ¼δ_c for the complex chain configurations below.
{#W10.5.23-1} The callers apply ℒ_ι to G^A(·, x) and G^Af, which are supported in Ω₀^A(□); so the restriction suffices when Ω₀^A(□), enlarged by one block and the margin 2ε, lies in Ω₁(Y^∼).

{#W10.5.24} *The inclusion.* Ω₀^A(□) ⊂ Ω₀^B(□) ⊂ □̃⁵ (PBG p.408 l.29–35), and □̃⁵ ⊂ X̃⁵ for the cube □ of a factor R_α(X), which reads the field on X̃⁵ (RG II p.3 l.16–17).
{#W10.5.24-1} A walk term carries s(Δ) for every cube Δ of σ that meets its localisation domain ∪X̃_i⁵ (RG II p.3 l.30–33), and the localisation expansion keeps in V(Y) only the terms whose cubes Δ lie in Y, so ∪X̃_i⁵ ⊂ Y, since also □̃⁴ ⊂ Y: the cubes of σ are disjoint from the interior of □̃⁴ (RG II p.3 l.28–29), and Y(σ) = □̃⁴ ∪ (∪_{Δ∈σ}Δ), whose component Y₀ contains □̃⁴ (RG II p.4 l.10–15).
{#W10.5.24-2} Y^∼ is Y with the adjacent M₁-cubes of the scale k, so dist(Y, (Y^∼)^c) ≥ M₁a_k (the LF note's *The Lift ι_Y*), with a_k ≥ Lε.
{#W10.5.24-3} A point within 3ε of Y has its big block of side M₁ε at ℓ^∞-distance at least M₁a_k − 3ε − M₁ε from (Y^∼)^c, which exceeds R_ιM₁ε/L under M₁(L − 1 − R_ι/L) > 3, with R_ι = 4dL + 1 the parameter R of VAR (1) for the lift's one-step problem (*The lift's R_ι.*); it holds under L ≥ 8d + 4 and M₁ ≥ 4.
{#W10.5.24-4} So Ω₀^A(□) enlarged by 3ε lies in Ω₁(Y^∼).

{#W10.5.25} *The Hölder bound.* Leg 2 of §5(c) on the fine side needs ‖ℒ_ιu‖_{1,β;y″} for u := G^Af or G^A(·, x), on the blocks y″ of run A's shell n, at the spacing L^nε.
{#W10.5.25-1} Fix β₂ := (1 + β)/2.
{#W10.5.25-2} By (3.43) for G^A at the exponent β₂ (Corollary 3.6, with B₀(β₂)), (L^nε)^{β₂}‖∇_Au‖_{β₂} is bounded like the sup part of the norm.
- {#W10.5.26} *The lattice lemma.* If |∇_Bf| ≤ Kε^{β₂} on the ε-neighbourhood of the blocks of the norm, then (L^nε)^β‖∇_Bf‖_β ≤ 2KL^β(L^nε)^{β₂}, since distinct points of T_{ε/L} are at least ε/L apart and ε ≤ L^nε.
  {#W10.5.26-1} The same holds for |∇_Bf| ≤ K′ with the factor 2K′L^βL^{nβ}.
- {#W10.5.27} Iu: by the oscillation bullet of the Cauchy note's *Regularity of the Lifts.* (#C10.4.109-5), the fine differences of Iu oscillate over a fine 4-cell by at most the oscillation of ∇_Au over a coarse cell of side 6ε plus 4C_trε|F||u|, its transport term being (6d + 3)·32d²ε²|F|sup|∇_Au| ≤ 576d³ε|F||u| by |∇_Au| ≤ 2|u|/ε, with 4d + 256d² + 576d³ ≤ 4C_tr, and at distances r ≥ 4ε they are interpolated coarse differences.
  {#W10.5.27-1} So (L^nε)^β‖∇_BIu‖_β ≤ 6L^β(L^nε)^{β₂}‖∇_Au‖_{β₂} + 8C_trL^βL^{nβ}ε|F||u|.
- {#W10.5.28} H₁h, h := 𝔡u − QIu: with the nodes of the Cauchy note (#C10.4.108-1–#C10.4.108-2), Q^{str}I reproduces affine fields at U = 1, and its Taylor bullet (#C10.4.110) with the oscillation remainder in place of ε²|∇∇g| gives |h| ≤ Cε(6ε)^{β₂}‖∇_Au‖_{β₂} + max(C, 1)C_trε²|F||u| on Λ₁.
  {#W10.5.28-1} With (3.133), |∇_BH₁h| ≤ 6CB_ιε^{β₂}‖∇_Au‖_{β₂} + max(C, 1)B_ιC_trε|F||u| up to the decay, and the lattice lemma applies.
- {#W10.5.29} C̃₁D*λ, λ := DP_πIu: in the axial gauge about a point x, D* annihilates the constant 2-form λ_x at U = 1, and the background adds at most O(1)|z − x||F||λ_x| at z.
  {#W10.5.29-1} (3.44) at ε_H = ½ with the lattice trick of the bullet above, applied to λ − λ_x on the blocks at distance R from x, where |λ − λ_x| ≤ (R + 2ε)^{β₂}‖λ‖_{β₂}, gives |∇_BC̃₁D*λ(x)| ≤ O(1)B₀′(½)L^{1/2}ε^{β₂}‖λ‖_{β₂} + O(1)ε²|F||λ|, and ‖λ‖_{β₂} ≤ 6L‖∇_Au‖_{β₂} plus curvature terms by the Iu bullet at β₂.
  {#W10.5.29-2} The curvature part [F, G′RD*Iu] of λ has its sup bounded by |F| times O(1)ε sup|u|, and by the second form of the lattice lemma its β₂-quotient is at most 2(L/ε)^{β₂} times that sup.
  {#W10.5.29-3} Its contribution therefore carries the factor ε²|F| ≤ c_F(Mα₀ + α₁ + α₁²)L^{−2n}, which absorbs L^{nβ} as in the last bullet.
  {#W10.5.29-4} The lattice lemma applies.
- {#W10.5.30} C̃₁DRD*Iu: R = 1 − P, P := G′Q′*CQ′G′ is a projection, and P1 = 1 at U = 1, since Δ1 = 0 and Q′1 = 1 give 1 = G′Q′*(a·1).
  {#W10.5.30-1} So, with μ := D*Iu, |Rμ(z)| ≤ |R(μ − μ_z)(z)| + |Rμ_z(z)| ≤ O(1)(1 + ‖P‖_w)ε^{β₂}‖μ‖_{β₂} + C_Rε|F||μ| at every z, with ‖P‖_w the weighted norm of P from (3.42) and (3.48) and C_R the axial comparison of *Transports.* Then |∇_BC̃₁D(Rμ)| ≤ O(1)B₀′(½)L^{1/2}sup|Rμ| by (3.44), and the lattice lemma applies.
- {#W10.5.31} The terms of size ε|F||u|, Δ_π^{(2)}Iu, and the factor P_π* have gradients bounded by k₀-type multiples of |u| carrying L^{−n}, L^{−2n}, or L^{−3n}; the lattice lemma's second form multiplies them by 2L^βL^{nβ}, which these factors absorb.
{#W10.5.32} So, at the real chain configurations, ‖ℒ_ιu‖_{1,β;y″} ≤ C_{ℒ,β}Σ_{y‴}e^{−¼δ₁d(y″,y‴)}‖u‖_{1,β₂;y‴}, with C_{ℒ,β} a constant of L, d, G, B_ι, C_tr, C_R, C, B₀′(½), and ‖P‖_w, and leg 2 holds with B₀(β₂) in place of B₀(β) and the rate ¼δ₁, which δ₀′ allows.

{#W10.5.33} *The tail.* ℒ_ιG^Af is supported in Y^∼, not in Ω₀^B.
{#W10.5.33-1} Outside Ω₀^B it reads G^Af on run A's shell 0 and beyond, at distance at least 2R₀M₀ε/L.
{#W10.5.33-2} G^Af there is bounded by the decay of G^A from the block y of □ to shell 0, which §5(c) already counts in the shell-0 contribution at ϖ = 1 and bounds by L^{−βj}.
{#W10.5.33-3} So (1 − χ_B)ℒ_ιG^Af is of the form of that contribution, with the factor 3B_ιN(½δ₁), N(½δ₁) the bound of (2.58) under (2.59) at α = δ₁/(2δ₀), and under ½δ₁R₀M₀ ≥ 4 log L for the shells crossed.

{#W10.5.34} *The exactness.* PBG's averaging is the double bar (PBG (3.13), p.392 l.44–52), so the constraint of (3.110) is Q̄A = B and Q̄₁ℒ_ι = 1 on the data of Λ₁ exactly, with Q̄₁ at the background of H₁.
{#W10.5.34-1} The background at which the fine form (c) is used is fixed by the LF note's split of the bracket (its (ii), the pieces of the re-summation through (δ)): (iii) compares run B's walk terms at run B's background ι_Yc^A with ℒ_ι applied to run A's at c^A = Mι_Yc^A, c^A the chain configuration, and the passage from ι_Yc^A to run B's decoupled field is the piece (δ) of that note, not part of (W-δ).
{#W10.5.34-2} So §4 and 10.1 are applied to the aligned pair (ι_Yc^A, c^A): 10.1's U′U^B is ι_Yc^A, Q₁ := Q̄₁(ι_Yc^A), and ℒ_ι is the Landau part of dι_Y at c^A (*The data on Λ₁.*), whose constraint is this Q₁, taken at ι_Yc^A, the background of H₁.
{#W10.5.34-3} With the cut-off χ_B and the margin of 10.1, (S) holds for χ_Bℒ_ι with this Q₁, with no correction.
{#W10.5.34-4} At a real chain configuration c^A = MU^B (the LF note's (i)), ι_Yc^A = e^{i(ε/L)T}U^B (the Cauchy note's §9.8, *The tail.*), and 10.1's premise holds with U′ := e^{i(ε/L)T}, which is real: on run A's shell n, |T| ≤ C_ιε₁ε^{−1}(ε/a)²L^{−3n} and |∇T| ≤ C_ιε₁ε^{−2}(ε/a)²L^{−3n} (the Cauchy note's §9.8, *The decay.*, #C9.8.15-1, for both, with the factor L^{−3n} from dist(·, Ω₁^c) ≥ 2R₀M₀nε under δ_ιR₀M₀ ≥ (3/2)log L, as derived above in 10.5), which is within (3.37) under C_ιε₁ ≤ α₁.
{#W10.5.34-5} ι's constraint is the plain average, so Q₁^{pl}dι_Y = 1.
{#W10.5.34-6} By (B1)–(B2), Q₁^{pl}ℒ_ι = 1 − D̄Θ₁ℒ_ι and Q₁^{pl}D_Bγ = D̄(γ at the coarse sites).
{#W10.5.34-7} Since dι_Y = ℒ_ι + D_Bγ, Q₁^{pl}D_Bγ = D̄(γ at the coarse sites) gives γ = Θ₁ℒ_ι at the coarse sites, which is CMP 98 (87) linearised, and the difference between the plain average and the double bar lies entirely in the gauge term.

{#W10.5.35} *Complex chain configurations.* At the complex points c(t) of the joint line (the LF note's *The joint line.*), which are the complex chain configurations, ι_Yc^A is complex.
{#W10.5.35-1} Theorem 3.12 assumes a real background, and PBG defers the passage from (3.37)–(3.38) to (3.35)–(3.36) (p.396 l.51–53).
{#W10.5.35-2} VAR's Sect. G gives the structure: for c^A = V′V₀ with V₀ real satisfying VAR (7) and |B′| < 2C₁ε₁ (VAR (172), p.305 l.31–35), U₀ := U_k(V₀) is real, U_k(V′V₀)U₀^{−1} = exp iηℋ(B) in the Landau gauge, and ℋ = 𝒜₁ + H₁B − HD(𝒜₁ + H₁B) (VAR (173)–(175), p.305 l.36–52), with H₁ and H at U₀, 𝒜₁ the analytic solution of (175), of second order in H₁B by (176) (p.306 l.1–6), and ℋ satisfying VAR (19) with ε₂ = B₅ε₁.
  {#W10.5.43} VAR (190) (p.308 l.36–47) bounds δℋ/δB, with its gradient and Hölder entries, at the rate ⅛δ_V (δ_V VAR's rate) and at the scales of the k = 1 problem, with no gain on run A's shells: on the shell n the gradients it gives are of order ε^{−1}|v|, against the (L^nε)^{−1}|v| that 10.1's cost paragraph uses (it uses k₀ only through k₀ ≤ C_ℒ(L^nε)^{−1}).
  {#W10.5.43-2} So (H_ℒ) at the complex chain configurations needs the shell gain L^{−n}, and leg 2 needs L^{−2n}: a Hölder quotient at the scale ε with the relative size L^{−n} is L^{nβ}L^{−n}ε^{−1} after the factor (L^nε)^β, which cancels ϖ_n = L^{−βn} in the shell sum of §5(c) at n near j.
  {#W10.5.43-3} The bullets below obtain both from (190), without a weighted version of VAR's proofs.
  - {#W10.5.44} *The weighted-kernel lemma.* Let w(x) := L^{n(x)}, n(x) run A's shell index of x.
    {#W10.5.44-1} A kernel with |K(x, z)| ≤ C_Ke^{−δ_cd(x,z)/ε} satisfies sup_xΣ_z|K(x, z)|w(x)/w(z) ≤ LC_KN(δ_c/2) under δ_cR₀M₀ ≥ log L: from the shell m to the shell n > m the shells strictly between are crossed, at the distance Σ_{i=m+1}^{n−1}2R₀M₀L^iε ≥ 2R₀M₀(n − m − 1)ε, so w(x)/w(z) ≤ Le^{(δ_c/2)d(x,z)/ε}, and w(x)/w(z) ≤ 1 when n(z) ≥ n(x).
    {#W10.5.44-2} Pointwise products satisfy sup w|XY| ≤ (sup w|X|)sup|Y|.
  - {#W10.5.45} *The base and the local gauge.* The complex chain configurations are c^A = M(U′U^B), with U^B real and U′ as in 10.1.
    {#W10.5.45-1} Let V₀ be run A's real chain configuration at the real point of the line, and take U^B := ι(V₀), the global one-step lift, so that MU^B = V₀ exactly.
    {#W10.5.45-2} U^B is the one-step minimiser at the data V₀, unique up to gauge (VAR Theorem 1 at one step).
    {#W10.5.45-3} Its regularity on run B's shells is that of the LF note's *The Fine Side at the Multiscale Chain.*, *The one-step problem.*: VAR Theorem 1 bounds the minimiser V₀ = c^A (not the data, whose hypothesis is only (7)): |A| < B₃Mε₁a_j^{−1}, |∇A| < B₃Mε₁a_j^{−2}, and ‖A‖_{1,β} < B₄(β)Mε₁a_j^{−2−β} for 0 ≤ β ≤ 1 (VAR (9)), and |∂*∂A| < B₃Mε₁a_j^{−3} (VAR (10)).
    {#W10.5.45-4} The argument of the Cauchy note's §9.7 carries |A|, |∇A|, and |∂*∂A| to U^B; the Hölder part is used only for V₀ itself, in the first differences of B″ below with the sources bounded pointwise by their layer.
    {#W10.5.45-5} This gives PBG's (3.35) on run B's shells from VAR (9), and (3.36) from VAR (10).
    {#W10.5.45-6} The Cauchy note's §9.8, *The tail.*, gives ι_Y(V₀) = e^{i(ε/L)T}U^B, with the real tail T bounded at the Cauchy note's #C9.8.15-1 (§9.8, *The decay.*) and in the paragraph *The exactness.* above.
    {#W10.5.45-7} These are the premises that the real-case bounds above use, and they need V₀ to be a real chain configuration with VAR's bounds (9)–(10), as the members c^A (VAR Theorem 1) and the backgrounds of §12 are, not that V₀ be M of run B's own member (the runs' members differ by the coarse profile e^{iεA_c} of the LF note's (b)).
    {#W10.5.45-8} The real-case bounds above (H_ℒ and the Hölder bound of leg 2) then hold for ℒ_ι(V₀), and write c^A = V′V₀ with V′ = e^{iB′}.
    {#W10.5.45-9} From here to the end of the B″ bullets c^A denotes the complex coarse point Mc(t); since c(1) = ι_Y(V₀) and Mι_Y(V₀) = V₀, the sentences that write c^A for the real member V₀ are its value at t = 1, where B′ = 0.
    {#W10.5.45-10} By 10.1's average bullet, in the real gauge u of 10.1, B′ is ε(Ã − Ã_r) up to Baker–Campbell–Hausdorff terms, with Ã_r the average of the real field, so on run A's shell n, |B′| ≤ O(1)α₁^AL^{−n}, and the coarse plaquette logarithms of c^A and V₀ differ by at most O(1)α₁^AL^{−2n}, from |∇Ã|, |∇Ã_r| ≤ α₁^A(L^nε)^{−2}.
    {#W10.5.45-11} The complex chain configurations that the consumer reads are the points c(t) of the LF note's joint line (its *The joint line.*), c(t) = e^{it(ε/L)𝐒_c}c^B.
    {#W10.5.45-12} With V₀ = c^A, ι_Yc^A = e^{i(ε/L)𝐒_c}c^B and ι_Y(V₀) = e^{i(ε/L)T}U^B (*The tail.*) give c(t) = U′(t)U^B with U′(t) := e^{it(ε/L)𝐒_c}e^{−i(ε/L)𝐒_c}e^{i(ε/L)T}.
    {#W10.5.45-13} Off Y, U′(t) = e^{i(ε/L)T}, the tail, small by §9.8.
    {#W10.5.45-14} By BCH, the field of U′(t) is (t − 1)𝐒_c + T plus commutator terms, and for |t| < 1/r(Y), r(Y) ≤ 1, a_{j(x)}|(t − 1)𝐒_c(x)| + a_{j(x)}²|∇(t − 1)𝐒_c(x)| ≤ (1 + r(Y))ϱ(x) ≤ 2ϱ(x).
    {#W10.5.45-15} Exactly, c(t) = e^{i(t−1)(ε/L)𝐒_c}ι_Y(V₀), since e^{it(ε/L)𝐒_c} and e^{−i(ε/L)𝐒_c} are exponentials of multiples of the same element on each bond, and Mι_Y(V₀) = V₀, since ι's constraint is the plain average (*The exactness.*).
    {#W10.5.45-16} With W := ι_Y(V₀) and X := (t − 1)(ε/L)𝐒_c, e^{iB′(b)} = M(e^{iX}W)(b)(MW)(b)^{−1}, and M is RG I (0.4): at a coarse bond c, MU(c) = e^{iY_c}U(c), with U(c) the transport along the L fine bonds of c and Y_c a convex combination of the logarithms of the loop holonomies h_{c,x}^{Γ,Γ′} = U(γ_{c,x}^{Γ,Γ′})U(c)^{−1} over x ∈ B(c₋) and the contour pairs (Γ, Γ′) (the Cauchy note's #C10.1.4-0-2).
    {#W10.5.45-17} So, to first order, B′ is the same convex combination of the path sums of X transported at W, and the BCH corrections are at most c_G times the path sums of |X| times (the path sums of |X| plus |log h_{c,x}^{Γ,Γ′}(W)|), the last of the size of W's curvature.
    {#W10.5.45-18} The tail T enters B′ only through the transports and these holonomies, and B′ = 0 on the coarse bonds all of whose paths miss Y. Each path γ_{c,x}^{Γ,Γ′} has at most (d + 1)L fine bonds (|n_ν| ≤ L/2, the Cauchy note's #C10.1.4-0-1), each carrying at most (ε/L)|(t − 1)𝐒_c|.
    {#W10.5.45-19} This section bounds ℒ_ι at the coarse point M(U′(t)U^B) = Mc(t).
    {#W10.5.45-20} This contains the point at which the LF note's (iii) reads ℒ_ι.
    {#W10.5.45-21} (iii) compares run A's walk term at c^A with run B's at ι_Yc^A through dι_Y, at the coarse point Mι_Yc^A = c^A.
    {#W10.5.45-22} On the joint line of its *The joint line.*, c(1) = e^{i(ε/L)𝐒_c}c^B = ι_Yc^A, so this point is Mc(1), with |1| < 1/r(Y) for r(Y) ≤ ½.
    {#W10.5.45-23} So on all of Y^∼, at the global layer j(x), |B′| ≤ O(1)ϱ(x)ε/a_{j(x)} and the first differences of B′ are at most O(1)ϱ(x)(ε/a_{j(x)})², and VAR's (172) holds for B′ on all of Y^∼ under O(1)ϱ ≤ C₁ε₁/4.
    {#W10.5.45-24} Put ϱ̄ := sup_{Y^∼}ϱ and α_c := C_cϱ̄, with C_c the larger constant O(1) of these two bounds.
    {#W10.5.45-25} On run A's shell n, a_{j(x)} ≥ L^nε, except on the innermost local shell, which may meet the finer global layer, where a_{j(x)} ≥ L^{n−1}ε.
    {#W10.5.45-26} So |B′| ≤ α_cL^{−n} and the first differences of B′ are at most α_cL^{−2n} at points of the shell n, with the factors L and L² on the innermost local shell; the bullets below carry these factors as those of the shell n − 1.
    {#W10.5.45-27} These bounds replace the bounds O(1)α₁^AL^{−n} and O(1)α₁^AL^{−2n} of 10.1's average bullet in the bullets below, which read B′ only through its size and its first differences, so they are written with α_c.
    {#W10.5.45-28} In particular no bound below carries the real background's size c_uMα₀ of α₁^A.
    {#W10.5.45-29} Fix a coarse site x₀ of run A's shell n ≥ 1, and put δ_c := (1/16)min(δ_V, δ₀, δ₁) and ρ_n := R₀M₀L^{n−1}ε.
    {#W10.5.45-30} Let ℓ be the coarse G^c-valued function ℓ(y) := Σ_με^{−1}(y − x₀)_μR_{V₀}(Γ_{y,x₀})B′(b_μ(x₀)), with b_μ(x₀) the coarse bond from x₀ in the direction μ and Γ_{y,x₀} the coordinate path from x₀ to y in a fixed order of the directions, transported at V₀.
    {#W10.5.45-31} So D_{V₀}ℓ is the value of B′ at x₀, transported, up to the holonomies of V₀ around the loops of these paths.
    {#W10.5.45-32} Let χ be equal to 1 within ρ_n/2 of x₀ and to 0 beyond ρ_n, with coarse first and second differences at most 2ε/ρ_n and 4(ε/ρ_n)².
    {#W10.5.45-33} Put θ := χℓ, υ := e^{iθ}, and V₁ := (c^A)^{υ^{−1}} = e^{iB″}V₀; this is VAR's transformation (16), which keeps the real base V₀.
    {#W10.5.45-35} The ball of radius ρ_n about x₀ reaches at most the shells n − 1, n, and n + 1, since the shell n − 1 has the width 2R₀M₀L^{n−1}ε > ρ_n.
    {#W10.5.45-36} Then:
    - {#W10.5.46} within ρ_n/2 of x₀, B″(b) = B′(b) − (D_{V₀}ℓ)(b) up to the BCH commutators of θ with B′, of size c_G|θ||B′|.
      {#W10.5.46-1} The first differences of B′ are at most O(1)L²α_cL^{−2n} in every direction on the ball (the factor L² for the shell n − 1), so, summing them along Γ_{b₋,x₀}, |B′(b) − R_{V₀}(Γ)B′(b_μ(x₀))| ≤ O(1)L²α_c(1 + d_ε(x₀, b))L^{−2n}.
      {#W10.5.46-2} The holonomy of V₀ around a loop of area at most d_ε(x₀, b)ε² is at most O(1)Lα₀L^{−2n}d_ε(x₀, b) ≤ O(1)Mα₀L^{−2n}d_ε(x₀, b) (the net factor L is L³ from the cube fitting's O(1)L³C₀ε₁a_m^{−2}, L² from a_m ≥ L^{n−1}ε, and L^{−4} from O(1)L⁴C₀ε₁ ≤ α₀; and M ≥ L), by VAR (9) for V₀ on the layers (§11, the axial-gauge paragraph of *So the telescoping holds term by term*, under O(1)L⁴C₀ε₁ ≤ α₀), which multiplies |ℓ| ≤ d_ε(x₀, b)·O(1)Lα_cL^{−n}; with d_ε ≤ R₀M₀L^n this is ≤ O(1)LR₀M₀Mα₀α_cd_ε(x₀, b)L^{−2n}.
      {#W10.5.46-3} The commutators are at most c_Gd_ε(x₀, b)O(1)L²α_c²L^{−2n}.
      {#W10.5.46-4} So |B″(b)| ≤ O(1)L²α_c(1 + d_ε(x₀, b))L^{−2n} under R₀M₀Mα₀ ≤ 1 and c_Gα_c ≤ 1;
    - {#W10.5.47} the first differences of B″ along any bond within ρ_n/2 are those of B′, at most O(1)L²α_cL^{−2n}, plus the differences of the holonomy and commutator terms.
      {#W10.5.47-1} Moving the bond to a neighbour translates the ladder of up to d_ε plaquettes, so the holonomy difference is bounded through the curvature gradient of V₀; where the translation changes the ladder's length by one plaquette, it adds ε²|F||ℓ| ≤ O(1)Mα₀R₀M₀α_cL^{−2n}, within the bound below under R₀M₀Mα₀ ≤ 1, and the change of ℓ along the move, multiplied by the holonomy, adds at most O(1)Lα₀R₀M₀L^{−n−1}·O(1)Lα_cL^{−n}, smaller under the same condition.
      {#W10.5.47-2} By VAR (9) at β = 1 on VAR's class cubes (§11's axial-gauge paragraph), |∇F| ≤ O(1)L⁴C₀ε₁a_m^{−3} at the points of a global layer m, and on the ball, which reaches the shells n − 1, n, and n + 1, a_m ≥ L^{n−1}ε, so |∇F| ≤ O(1)L⁷C₀ε₁(L^nε)^{−3}.
      {#W10.5.47-3} With d_ε ≤ R₀M₀L^{n−1}/2 the difference is at most d_ε²ε³|∇F|·O(1)Lα_cL^{−n} ≤ O(1)(R₀M₀)²L⁶C₀ε₁α_cL^{−2n}.
      {#W10.5.47-4} This is ≤ O(1)L²α_cL^{−2n} under O(1)(R₀M₀)²L⁴C₀ε₁ ≤ 1.
      {#W10.5.47-5} The commutator differences contain [θ, ΔB′] with |θ| ≤ O(1)LR₀M₀α_c and the commutators [θ, D_{V₀}θ], so they are at most O(1)c_GL³R₀M₀α_c²L^{−2n}.
      {#W10.5.47-6} So the first differences are at most O(1)L²(1 + c_GLR₀M₀α_c)α_cL^{−2n};
    - {#W10.5.48} between ρ_n/2 and ρ_n, B″ = B′ − χD_{V₀}ℓ − (∇χ)ℓ up to the same terms, and beyond ρ_n, B″ = B′.
      {#W10.5.48-1} Here |∇χ||ℓ| ≤ (2ε/ρ_n)(ρ_n/ε)O(1)Lα_cL^{−n}, and |D_{V₀}ℓ| ≤ O(1)(L + R₀M₀L^{−1})α_cL^{−n}: with d_ε ≤ ρ_n/ε = R₀M₀L^{n−1}, the holonomy part is at most d_ε·d_εO(1)Lα₀L^{−2n}·O(1)Lα_cL^{−n} ≤ O(1)(R₀M₀)²α₀α_cL^{−n}, and (R₀M₀)²α₀ ≤ R₀M₀L^{−1} under R₀M₀Mα₀ ≤ 1 and M ≥ L.
      {#W10.5.48-2} The commutators are at most c_G|θ||B′| ≤ O(1)c_GL²R₀M₀α_c²L^{−n} (#W10.5.49), so |B″| ≤ O(1)(L + R₀M₀L^{−1} + c_GL²R₀M₀α_c)α_cL^{−n} ≤ O(1)L²R₀M₀α_cL^{−n} between ρ_n/2 and ρ_n under c_Gα_c ≤ 1; this is the bound used below.
      {#W10.5.48-3} Its first differences are at most the bound of the previous item plus (2ε/ρ_n)O(1)(L + R₀M₀L^{−1})α_cL^{−n} + 4(ε/ρ_n)²(ρ_n/ε)O(1)Lα_cL^{−n} ≤ O(1)L²(1 + c_GLR₀M₀α_c)α_cL^{−2n}, since ε/ρ_n = L^{1−n}/(R₀M₀) ≤ L^{1−n}.
      {#W10.5.48-4} Beyond ρ_n, |B″(y)| ≤ O(1)Lα_cL^{−n(y)}, with n(y) the shell of y, and its first differences are those of B′;
    - {#W10.5.49} with ℓ(x₀) = 0, |θ| ≤ (ρ_n/ε)O(1)Lα_cL^{−n} ≤ O(1)LR₀M₀α_c on the ball;
    - {#W10.5.50} the amplitude a(x) := Σ_ye^{−δ_cd_ε(x,y)}|B″(y)| satisfies, for d_ε(x, x₀) ≤ ρ_n/(4ε),
      {#W10.5.51} a(x) ≤ C_a(1 + d_ε(x, x₀))α_cL^{−2n}, C_a := O(1)L⁴R₀M₀(N₁(δ_c) + N(δ_c/4)), N₁(δ) := sup_xΣ_y(1 + d_ε(x, y))e^{−δd_ε(x,y)}.
      {#W10.5.52} For y within ρ_n/2 of x₀, 1 + d_ε(x₀, y) ≤ (1 + d_ε(x₀, x))(1 + d_ε(x, y)).
      {#W10.5.52-1} For y beyond ρ_n/2, d_ε(x, y) ≥ ρ_n/(4ε), so e^{−δ_cd_ε} ≤ e^{−δ_cR₀M₀L^{n−1}/8}e^{−(δ_c/2)d_ε} ≤ L^{−2n}e^{−(δ_c/2)d_ε} under δ_cR₀M₀ ≥ 16 log L, since n ≤ L^{n−1}, and |B″(y)| ≤ O(1)L²R₀M₀α_cL^{−n(y)} with n(y) the shell of y, so the weighted-kernel lemma at the rate δ_c/2 bounds this part by O(1)L⁴R₀M₀α_cN(δ_c/4)L^{−2n}.
      {#W10.5.52-2} The factor R₀M₀ goes into C_a, and the factor L⁴ also covers x in the shell n − 1.
    {#W10.5.53} At n = 0, θ := 0 and a(x) ≤ C_aα_c.
    {#W10.5.53-1} For n ≥ 1, the ball of radius ρ_n about x₀ lies at distance at least 2R₀M₀L^{n−1}ε − ρ_n = ρ_n from Ω_{n−1}(□)^c ⊇ Ω₀(□)^c, the local domains of □'s sequence, and Ω₀^A(□) enlarged by 3ε lies in Ω₁(Y^∼) (10.5, *The inclusion.*), so υ = 1 near the collar, including the reach 2ε of Q_1^{s*} and the interface twist of CMP 99 (1.31).
    {#W10.5.53-2} By VAR (181) (p.307 l.6–14), ι_Y(V^υ) = ι_Y(V)^{ῡ} for G^c-valued υ near G; υ = 1 near the collar keeps the collar data fixed.
    {#W10.5.53-3} With the G^c-covariance of H₁ and of 𝔡 (the step field of Q_1^{s*} is covariant under the block-constant ῡ), ℒ_ι(c^A) = Ad(ῡ)ℒ_ι(V₁)Ad(υ)^{−1}.
    {#W10.5.53-4} The covariant derivatives and the Hölder quotient of PBG (3.40), with the transports R(U(Γ_{x,x′})) of the fine background, are exactly covariant, and Ad(ῡ) and Ad(υ)^{−1} have norm at most e^{2c_Gsup|θ|} ≤ √2.
    {#W10.5.53-5} So, with w := Ad(υ)^{−1}u, the norms of ℒ_ι(c^A)u in c^A's frame are those of ℒ_ι(V₁)w in V₁'s frame, up to the factor 2.
    {#W10.5.53-6} Two quantities are bounded below: ℒ_ι(V₁) − ℒ_ι(V₀) near x₀, and ℒ_ι(V₀) applied to the rotated data w.
  - {#W10.5.54} *Localised differences.* At V₁ = e^{iB″}V₀, VAR's §G applies with the real U₀ := ι_Y(V₀): ι_Y(V₁) = (exp(iηℋ(B″))U₀)^g, with ℋ in VAR's gauge (20)–(21) relative to U₀ and g the return to the axial gauge.
    {#W10.5.54-1} Let K(B) := δℋ/δB.
    - {#W10.5.55} (190) bounds K(B) at every B satisfying (172) by the entries of (3.133) for H₁, with a Hölder entry, at the rate ⅛δ_V.
      {#W10.5.55-1} Bałaban states this as "regularity and decay properties identical to the propagator H, or H₀" (VAR p.307 l.17–18).
      {#W10.5.55-2} In the normalisation of the display above, |K(B)w(x)| ≤ C_VΣ_ce^{−⅛δ_Vd_ε(x,c)}|w(c)|, with ε^{−1} for ∇ and ε^{−1−β} for the Hölder quotient.
    - {#W10.5.56} The field.
      {#W10.5.56-1} For |e^{iB″} − 1| < C₁ε₁/2 on every bond, the segment tB″, 0 ≤ t ≤ 1, lies in (172), with room.
      {#W10.5.56-2} Since ℋ(0) = 0, ℋ(B″) = ∫₀¹K(tB″)B″dt, so |ηℋ(B″)(x)| ≤ C_Va(x), with its gradient at most C_Vε^{−1}a(x), at the rate ⅛δ_V ≥ 2δ_c.
      {#W10.5.56-3} Only this first-derivative bound of (190) is used below.
    - {#W10.5.57} The local factors.
      {#W10.5.57-1} VAR's §G takes ℋ as a function of the field B of V′ = e^{iB} in (172); here that field is B″, of V₁ = e^{iB″}V₀, and CMP 99 (1.31) (p.082 l.2–8) gives B_b = (1/i)log V′_b on the bonds inside Λ_j.
      {#W10.5.57-2} So the data derivative is db = Φ(B″)w, with Φ the inverse of the derivative of the exponential map on each bond, local, with |Φ(B″) − 1| ≤ O(1)|B″|.
      {#W10.5.57-3} On Λ₀ the data is 𝔡v, so db = Φ(B″)𝔡v there, and this settles db against 𝔡.
      {#W10.5.57-4} The decomposition dι_Y = H₁db + D_Bγ of *The data on Λ₁.* holds at real configurations, and both sides are analytic in the configuration, so it holds at V₁ by the identity theorem on the connected domain (172), which contains the real points.
      {#W10.5.57-5} So ℒ_ι(V₁) = H₁(U₁)𝔡₁, with 𝔡₁ the data derivative relative to V₁ itself, and the factor Φ(B″) enters through 𝔡₁ = Φ(B″)𝔡.
      {#W10.5.57-6} Here U₁ := ι_Y(V₁) = (exp(iηℋ(B″))U₀)^g, g the return to the axial gauge, block-local, with g = 1 at B″ = 0 and |Ad(g) − 1| ≤ O(1)L sup_{block}|ηℋ| by CMP 98 (86)–(87).
    - {#W10.5.58} The comparison of H₁ at U₁ and U₀, without a re-fixing of the gauge.
      {#W10.5.58-1} H₁ is G^c-covariant: PBG (3.33)–(3.34) give the covariance of G′, R, Δ_a, and G under real gauge transformations, and H₁ = G₁Q*(QG₁Q*)^{−1} is built from these and from covariant local operators.
      {#W10.5.58-2} For real g, Q(U^g) = Ad(ḡ)Q(U)Ad(g)^{−1} and G₁(U^g) = Ad(g)G₁(U)Ad(g)^{−1} give H₁(U^g) = Ad(g)H₁(U)Ad(ḡ)^{−1} by substitution, with Ad unitary.
      {#W10.5.58-3} At complex g the operators are the analytic continuations of the real ones: PBG extends "the operators to configurations with values in the complexified group G^c" and proves "the usual complex analyticity" (p.399 l.37–38; p.396 l.37), with Q* continued as the transpose.
      {#W10.5.58-4} So both sides are analytic in g, and they agree on G, a totally real submanifold of maximal dimension of G^c.
      {#W10.5.58-5} By the identity theorem they agree on the connected neighbourhood of G where both are defined.
      {#W10.5.58-6} So H₁((exp(iηℋ)U₀)^g) = Ad(g)H₁(exp(iηℋ)U₀)Ad(ḡ)^{−1}, and Ad(g) − 1 and Ad(ḡ) − 1 are local factors of size O(1)L|ηℋ| on the block.

{#W10.5.59} For H₁(exp(iηℋ)U₀) − H₁(U₀), PBG's formula (3.129), H₁ = G₁Q*(QG₁Q*)^{−1}, with G₁^{−1} the operator of the form (3.128), writes H₁ through products and inverses of the following:
- {#W10.5.60} the local operators D, D*, Δ, Q, Q′, and C^{(2)}, and the current J;
- {#W10.5.61} the nonlocal G′, R = 1 − P, P = G′Q′*(Q′G′²Q′*)^{−1}Q′G′ (the C̃₁DRD*Iu bullet above), and the projection A ↦ A − DG′RD*A of the second form of (3.128);
- {#W10.5.62} H = GQ*(QGQ*)^{−1} in the term HC^{(2)}J, with G of (3.130) and (QGQ*)^{−1}.

{#W10.5.63} ηℋ(B″) lies in (3.37) about the real U₀ at the scales of the k = 1 problem by VAR (19) with ε₂ = B₅ε₁, under B₅ε₁ ≤ a₁/2, the half leaving room for the polydisc of *G₁ and H₁* below.
{#W10.5.63-1} The complex extension of these operators with their bounds is as follows.
- {#W10.5.64} G′, R, P, and (Q′G′²Q′*)^{−1}: printed (p.403 l.4–6 and l.36–42, "and satisfy the same bounds").
- {#W10.5.65} G₀ = (Δ + DRD* + Q*aQ)^{−1}, the operator of PBG's earlier sections (p.421, before (3.130)): Theorems 3.1–3.3, the Hölder entries (3.43)–(3.44) included, hold at the real U₀ satisfying (3.35)–(3.36) (Corollary 3.6, p.408 l.6–11, on small domains, and the general theorems that PBG proves from p.408 l.14 on by localisation), and Theorem 3.4 (p.400) continues them to the domain (3.37) about U₀, printed.
  {#W10.5.65-1} Theorem 3.4 continues this G₀ only.
- {#W10.5.66} G of (3.130), H, and (QGQ*)^{−1}: PBG writes G = G₀(I − Δ′_πG₀)^{−1} = Σ_nG₀(Δ′_πG₀)^n (3.130), with Δ′_π of (3.120) bounded in (3.131) by c_πα₀ (PBG prints O(1)Mα₀; c_π carries §7's factor c_u, as in §11, *The form (c) for G̃*) through Theorem 3.1 for G′, the inequality (3.49), and the current.
  {#W10.5.66-1} With Theorem 3.3 for G₀, the series converges "in all norms appearing on the left-hand sides of the inequalities (3.42)–(3.47), except the inequality involving the Laplace operator in (3.42)" (p.422 l.12–13).
  {#W10.5.66-2} (QGQ*)^{−1} satisfies (3.132) (p.422 l.15–21, proved "in the same way as the operator (Q′G′²Q′*)^{−1}"), and (3.132) with Theorem 3.3 for G gives (3.133) for H. At U₁ every input is continued above (G₀, G′, R, and P) or is local with the current bound J(U₁) of the G₁ bullet below, so (3.131), the series (3.130), (3.132), and (3.133) hold at U₁ with α₀ + O(1)LB₅ε₁ in place of α₀.
- {#W10.5.67} G₁ and H₁: PBG proves Theorem 3.12 for G₁ through the series (3.138) (p.423 l.25–31).
  {#W10.5.67-1} Its inputs are Theorem 3.3 for G, the bounds of the local operators, and the smallness of J; the series "is convergent for α₀ restricted by a small, absolute constant" and "in all norms appearing in the formulation of Theorem 3.3", and (3.129) with (3.132) for G₁ then gives (3.133) for H₁.
  {#W10.5.67-2} At U₁ = exp(iηℋ)U₀ the same inputs hold: Theorem 3.3 for G and (3.133) for H by the bullet above, the local operators by their formulas, and J(U₁) − J(U₀).
  {#W10.5.67-3} The field strength changes by O(1)|∇ℋ| ≤ O(1)B₅ε₁(L^jη)^{−2} by VAR (19).
  {#W10.5.67-4} The current is a lattice divergence of it, at most 2η^{−1} times the change.
  {#W10.5.67-5} So J(U₁) − J(U₀) is ≤ O(1)L^jB₅ε₁(L^jη)^{−3} ≤ O(1)LB₅ε₁(L^jη)^{−3} at the scales j ≤ 1 of the k = 1 problem, and J(U₁) satisfies the bound of (3.36) with α₀ + O(1)LB₅ε₁ in place of α₀ (VAR (19), |D*Dℋ| < ε₂(L^jη)^{−3}, gives the same directly).
  {#W10.5.67-6} The smallness (3.137) of Δ^{(2)} also rests on the bound of C_j^{(2)} ("(149) in [5]").
  {#W10.5.67-7} C_j^{(2)} is the second-order part of an analytic function of the configuration, so at U₁ the same bound holds with a larger constant, by Cauchy's estimate on a polydisc about U₀ of twice the radius of (3.37), under the corresponding halving of PBG's a₁ (α₁^A ≤ a₁/2 and B₅ε₁ ≤ a₁/2); the averages, and with them C_j, are analytic on the first inequality of (3.37) by Proposition 6 of [5] (PBG p.406 l.21–22).
  {#W10.5.67-8} PBG's proof therefore runs at U₁ unchanged and gives Theorem 3.12 for G₁(U₁) and H₁(U₁), under the condition that O(1)L⁵M(α₀ + O(1)LB₅ε₁) is as small as PBG requires of O(1)Mα₀ ("O(1)Mα₀ is still a sufficiently small number", p.396 l.32), that is ≤ a₁ (Corollary 3.6, p.408 l.6), the factor L⁵ for §7's sequences; §8 splits it into O(1)L⁵Mα₀ ≤ a₁/2 and O(1)L⁶MB₅ε₁ ≤ a₁/2.
  {#W10.5.67-9} Here J(U₁) is the holomorphic extension of η^{−2}Im D*∂U, with U^{−1} in place of U*, and J(U₁) − J(U₀) also contains (D*_{U₁} − D*_{U₀})F(U₀), of size O(1)|ηℋ||F(U₀)|η^{−1}, which the same bound covers.
  {#W10.5.67-11} Expand the difference of each product by X₁Y₁ − X₀Y₀ = (X₁ − X₀)Y₁ + X₀(Y₁ − Y₀), and each inverse by the resolvent identity X(U₁)^{−1} − X(U₀)^{−1} = −X(U₁)^{−1}(X(U₁) − X(U₀))X(U₀)^{−1}.
  {#W10.5.67-12} Every term of the expansion is then a product of kernels with the decay of their bounds (at the rate ½δ₀ of (3.68), or δ₀ for the local ones) and exactly one difference of a local operator or of J, at an intermediate point z.
  {#W10.5.67-13} A local operator at U₁ and at U₀ differs by coefficients O(1)(|ηℋ| + η|∇(ηℋ)|) at z, and J by O(1)η^{−2}|∇(ηℋ)| plus O(1)|ηℋ| times the background curvature terms of J on the plaquettes at z (second differences on the lattice are at most 2η^{−1} times first differences).
  {#W10.5.67-14} By the field bullet, both are at most O(1)(1 + L)C_Va(z) in the units of the operator: on Λ₀, of spacing η ≤ ε, η|∇(ηℋ)| ≤ C_Va and η^{−2}|∇(ηℋ)| ≤ η^{−3}C_Va, and on Λ₁, of spacing Lη = ε (#W10.5.11-2), the same quantities at the spacing Lη are at most L times these.
    {#W10.5.68} The intermediate sum is localised.
    {#W10.5.68-1} A term with its difference at z has the kernel e^{−δd_ε(x,z) − δd_ε(z,c)} ≤ e^{−(δ/2)d_ε(x,z)}e^{−(δ/2)d_ε(x,c)} from x to the data point c, with δ := min(½δ₀, ½δ₁) ≥ 8δ_c, since (3.132)–(3.133) decay at δ₁ and ½δ₁.
    {#W10.5.68-2} With a(z) ≤ C_a(1 + d_ε(x, x₀))(1 + d_ε(x, z))α_cL^{−2n} for z within ρ_n/(4ε) of x₀, and a ≤ O(1)L⁴R₀M₀α_cN(δ_c/4) elsewhere, Σ_ze^{−(δ/2)d_ε(x,z)}a(z) ≤ N₁(δ/2)C_a(1 + d_ε(x, x₀))α_cL^{−2n} + e^{−(δ/4)ρ_n/(8ε)}N(δ/4)sup a for x within ρ_n/(8ε) of x₀.
    {#W10.5.68-3} The last factor is ≤ L^{−2n} under δ_cR₀M₀ ≥ 16 log L. So, for x within ρ_n/(8ε) of x₀,
      {#W10.5.69} H₁(U₁) − H₁(U₀) has the bounds of (3.133) at the scale ε (sup, ε^{−1} for the gradient, and ε^{−1−β} for the Hölder quotient, from the outer factor of each term, which is a factor at U₁ or U₀ with the bounds above, with (3.43)–(3.44) and the lattice trick of the refined gradient), at the rate δ/2, multiplied by C_ΔC_a(1 + d_ε(x, x₀))α_cL^{−2n},
    {#W10.5.70} with C_Δ := O(1)C_V(1 + L)(N₁(δ/2) + N(δ/4))c_P, c_P the number of factors in the expansion of (3.129) times the product of their bound constants, at the rate δ_c.
    {#W10.5.70-1} The factor Φ(B″) − 1 = O(|B″|) is local on the data side, and |B″| ≤ a.
    {#W10.5.70-2} The covariant derivatives at V₁ and V₀ differ by the connections B″/ε on the data side and ηℋ(B″)/η on the fine side; these are terms of the type k₀ with the same factor.
  - {#W10.5.71} *The conclusion at the complex chain configurations.* Put C_♮ := C_ΔC_a.
    {#W10.5.71-1} Let x be a point of run A's shell n ≥ 1 and x₀ the coarse site nearest to x, and work in the frame of x₀.
    {#W10.5.71-2} The region that the norm ‖·‖_{1,β;y″} reads at x has diameter at most 5L^{n′}ε, with n′ the shell of y″; n′ = n + 1 only near the boundary of the shell n, where the block of x belongs to the coarser shell.
    {#W10.5.71-3} So the diameter is at most 5L^{n+1}ε ≤ ρ_n/8 under R₀M₀ ≥ 40L², and where n′ = n + 1 the ranges r ≤ 5L^nε below read r ≤ 5L^{n+1}ε, which changes the numerical constants by at most the factor L³ (L² in the second Hölder part, L³ in the third), uniformly in n.
    {#W10.5.71-4} So every point x′ of a pair is within ρ_n/(8ε) of x₀, with 1 + d_ε(x′, x₀) ≤ 2 + r/ε, where r := |x − x′|.
    {#W10.5.71-5} Write:
    - {#W10.5.72} f := ∇ℒ_ι(c^A)u, f₁ := ∇ℒ_ι(V₁)w, f₀ := ∇ℒ_ι(V₀)w, and g := f₁ − f₀, each covariant derivative at its own fine background;
    - {#W10.5.73} R_c, R₁, and R₀ for the fine transports of PBG (3.40) along Γ = Γ_{x,x′} at ι_Y(c^A), ι_Y(V₁), and ι_Y(V₀).
    {#W10.5.74} By the localised differences, |g(x)| ≤ 2C_♮α_cL^{−2n}ε^{−1}Σ_ce^{−δ_cd_ε}|w(c)|, |g(x′)| ≤ C_♮(2 + r/ε)α_cL^{−2n}ε^{−1}Σ_ce^{−δ_cd_ε}|w(c)|, and the Hölder quotient of g at the scale ε carries ε^{−1−β} in place of ε^{−1}.
    - {#W10.5.75} The rotated data, through V₁'s frame.
      {#W10.5.75-1} Since V₁ = (c^A)^{υ^{−1}} and w = Ad(υ)^{−1}u, the coarse covariant derivative at V₁ satisfies ∇_{V₁}w = Ad(υ)^{−1}∇_{c^A}u exactly, and the V₁-transports are the c^A-transports conjugated by Ad(υ).
      {#W10.5.75-2} So ∇θ does not enter, and in V₁'s frame ‖w‖_{1,β₂;y‴} ≤ 2‖u‖_{1,β₂;y‴} by the factor √2 of Ad(υ)^{−1} at each end.
      {#W10.5.75-3} The passage from V₁'s frame to V₀'s reads only V₁ − V₀, that is B″: |∇_{V₀}w − ∇_{V₁}w| ≤ 2c_G(|B″|/ε)|w|, and the transports of the Hölder quotient differ by at most 2c_GΣ_{b∈Γ}|B″(b)| along a coarse path Γ of at most r/ε + 1 bonds.
      {#W10.5.75-4} The norm reads w on every block y‴, with the decay e^{−¼δ₁d(y″,y‴)}.
      {#W10.5.75-5} The bounds of B″ are:
      - {#W10.5.76} within ρ_n, |B″| ≤ O(1)L²R₀M₀α_cL^{−n}, and its first differences along every bond, in every direction, are at most O(1)L²α_cL^{−2n}, by the bullets on B″ of *The base and the local gauge.*: the linear gauge subtracts a transported constant, so these are the differences of B′ (at most ε²|∇Ã| up to BCH terms), the holonomy and commutator terms, and the cut-off terms;
      - {#W10.5.77} beyond ρ_n, B″ = B′, with |B′| ≤ O(1)Lα_cL^{−m} and first differences at most O(1)L²α_cL^{−2m} on the shell m.
      {#W10.5.78} So |B″|/ε ≤ O(1)L²R₀M₀α_c(L^mε)^{−1} on every block of the shell m, and the Hölder quotient of (B″/ε)w at the block scale is of the same size: for r ≤ 5L^mε, (L^mε/r)^{β₂}(r/ε)L^{−2m} ≤ 5L^{−m}, at the exponent β₂ of the norm ‖·‖_{1,β₂}.
      {#W10.5.78-1} The transport differences give, by (L^mε/r)^β(r/ε + 1)L^{−m} ≤ 10, a term at most O(1)c_GL²R₀M₀α_c times the gradient entry of w.
      {#W10.5.78-2} So, in V₀'s frame, ‖w‖_{1,β₂;y‴} ≤ C_fr‖u‖_{1,β₂;y‴} on every block y‴, with u in c^A's frame and C_fr := 2(1 + O(1)L²R₀M₀α_c), uniform in n (C_fr is the frame constant of this bullet, not §8's C_w).
    - {#W10.5.79} (H_ℒ), in the form that 10.1's cost paragraph uses, k₀ ≤ C(L^nε)^{−1}.
      {#W10.5.79-1} Here f(x) = Ad(ῡ(x))f₁(x), |f₀(x)| is bounded by the real (H_ℒ) applied to w, both its k₀ entry and its k₁|∇w| entry, the latter read by the gradient entry of the norm of w, and |g(x)| ≤ 2C_♮α_c(L^nε)^{−1}Σ_ce^{−δ_cd_ε}|w(c)|, since L^{−2n}ε^{−1} ≤ (L^nε)^{−1}.
      {#W10.5.79-2} So k₀ ≤ 2(C_{ℒ,ι}C_fr + 2C_♮α_c)(L^nε)^{−1}, with n the shell of x.
      {#W10.5.79-3} The cost paragraph reads (L^{n(c)}ε)^{−1}|w(c)| with n(c) the shell of c; for n(c) > n + 1 the conversion is the weighted-kernel lemma, which halves the rate, so the rate here is ½δ_c.
      {#W10.5.79-4} The sup entry sup(L^nε)^{−1}|ℒ_ιu| of leg 2's norm follows in the same way from the sup entry of the localised differences and the sup entry of the real bound at V₀.
      {#W10.5.79-6} The rotation term of order α_c(L^nε)^{−1}|u| is part of k₀.
    - {#W10.5.80} The Hölder quotient.
      {#W10.5.80-1} By exact covariance, f(x) − R_c(Γ)f(x′) = Ad(ῡ(x))[f₁(x) − R₁(Γ)f₁(x′)], and
      {#W10.5.81} f₁(x) − R₁(Γ)f₁(x′) = [f₀(x) − R₀(Γ)f₀(x′)] + [g(x) − R₁(Γ)g(x′)] + (R₀(Γ) − R₁(Γ))f₀(x′).
      {#W10.5.82} Each part is multiplied by (L^nε/r)^β.
      - {#W10.5.83} The first is the real Hölder quotient at V₀ for the data w.
        {#W10.5.83-1} It is ≤ C_{ℒ,β}Σ_{y‴}e^{−¼δ₁d(y″,y‴)}‖w‖_{1,β₂;y‴} ≤ C_{ℒ,β}C_frΣ_{y‴}e^{−¼δ₁d(y″,y‴)}‖u‖_{1,β₂;y‴}.
      - {#W10.5.84} The second, for r ≤ ε, is at most 3C_♮α_cL^{−2n}ε^{−1−β}r^β·Σ, and (L^nε/r)^β times this is ≤ 3C_♮α_cL^{nβ−2n}ε^{−1}Σ ≤ 3C_♮α_c(L^nε)^{−1}Σ.
        {#W10.5.84-1} For ε < r ≤ 5L^nε it is at most |g(x)| + √2|g(x′)| ≤ 3C_♮(2 + r/ε)α_cL^{−2n}ε^{−1}Σ, and (L^nε/r)^β(2 + r/ε) ≤ 3L^{nβ}(r/ε)^{1−β} ≤ 15L^n.
        {#W10.5.84-2} So it is ≤ 45C_♮α_c(L^nε)^{−1}Σ.
      - {#W10.5.85} The third.
        {#W10.5.85-1} R₁(Γ) = Ad(g(x))R′(Γ)Ad(g(x′))^{−1}, with R′ the transports of exp(iηℋ(B″))U₀ and g the block-local return to the axial gauge.
        {#W10.5.85-2} The fine path has at most L(r/ε + 1) bonds, so |R₀(Γ) − R₁(Γ)| ≤ O(1)L(sup_{y(x)}|ηℋ| + sup_{y(x′)}|ηℋ|) + 2c_GΣ_{b∈Γ}|ηℋ(b)|, the suprema over the blocks of x and x′ on which g is defined, ≤ O(1)LC_VC_aα_c(2 + r/ε)²L^{−2n}, under 2c_GΣ_{b∈Γ}|ηℋ(b)| ≤ ¼log 2 and O(1)L sup|ηℋ| ≤ ¼log 2, which give |R₁(Γ)| ≤ √2 (|R′(Γ)| ≤ 2^{1/4} and |Ad(g)^{±1}| ≤ 2^{1/8}).
        {#W10.5.85-3} With |f₀(x′)| ≤ C_{ℒ,ι}C_frΣ_ce^{…}(k₁|∇w(c)| + k₀|w(c)|), the full (H_ℒ) bound, which the full norm absorbs (written (L^nε)^{−1}Σ below for its k₀ entry), and (L^nε/r)^β(2 + r/ε)²L^{−2n} ≤ 9L^{(n+1)β}L^{−2n} ≤ 9L for r ≤ ε and ≤ 9L^{nβ}(r/ε)^{2−β}L^{−2n} ≤ 225 for ε < r ≤ 5L^nε, it is ≤ O(1)L²C_VC_aC_{ℒ,ι}C_frα_c(L^nε)^{−1}Σ.
    {#W10.5.86} The second and third parts are absorbed by the term (L^nε)^{−1}|u| of the norm.

    {#W10.5.87} So (H_ℒ), in the form that 10.1's cost paragraph uses, and the Hölder bound of leg 2 hold at the complex chain configurations.
    {#W10.5.87-1} The constants are 2(C_{ℒ,ι}C_fr + 2C_♮α_c) and √2[C_{ℒ,β}C_fr + O(1)(C_♮ + L²C_VC_aC_{ℒ,ι}C_fr)α_c], uniform in n.
    {#W10.5.87-4} At n = 0, θ := 0, V₁ = c^A, and the same computation with L^{−2n} = 1 gives a constant uniform at the scale ε, where ϖ = 1.
    {#W10.5.87-5} The rate is ½δ_c after the conversion to the shell of c (the kernels above decay at δ/2 ≥ 4δ_c), so δ₀′ := min(δ₀, ¼δ_Q, ¼δ₁, ¼δ_c).
    {#W10.5.87-6} The conditions are:
    - {#W10.5.88} O(1)L²R₀M₀α_c ≤ C₁ε₁/2 (B″ satisfies (172) with room), a condition on ϱ̄, and B₅ε₁ ≤ a₁/2;
    - {#W10.5.89} O(1)L⁵M(α₀ + O(1)LB₅ε₁) as small as PBG requires of O(1)Mα₀ (p.396 l.32), the factor L⁵ for §7's sequences (G, H, G₁, and H₁ at U₁);
    - {#W10.5.90} R₀M₀Mα₀ ≤ 1, O(1)(R₀M₀)²L⁴C₀ε₁ ≤ 1, and c_GLR₀M₀α_c ≤ 1 (the holonomy terms of the linear gauge, their first differences through VAR (9) at β = 1 for V₀, and the commutator terms), O(1)ϱ ≤ C₁ε₁/4 (VAR's (172) for B′ on all of Y^∼), and ϱ ≤ O(1)α₁^A/L (the joint-line moves within 10.1's premise (3.37), by a_{j(x)} ≥ L^nη);
    - {#W10.5.91} O(1)LR₀M₀α_c ≤ r_υ (υ in VAR's neighbourhood of G) and 2c_G·O(1)LR₀M₀α_c ≤ ½log 2 (the factors Ad(υ)^{±1}, Ad(ῡ)^{±1});
    - {#W10.5.92} O(1)c_GLC_VC_aα_c ≤ ¼log 2 (the transports R₁, with |R₁| ≤ √2);
    - {#W10.5.93} δ_cR₀M₀ ≥ 16 log L and R₀M₀ ≥ 40L²;
    - {#W10.5.94} V₀ = MU^B satisfying VAR (7) and VAR's bounds (9)–(10), and the ε₃ of (186)–(190) in VAR's range.
      {#W10.5.94-1} V₀'s membership comes from its data through VAR Theorem 1 (*The base and the local gauge.*), not from (3.35), so no condition bounds α₀ by ε₁;
    - {#W10.5.95} M_V ≤ M(ε₁) for VAR's cube parameter, and VAR's ε₁ ≤ a₁ (VAR Theorem 1); the a₁ of "B₅ε₁ ≤ a₁/2" above is PBG's, the smallness of (3.37) in PBG Theorem 3.4.    {#W10.5.96} The ε₁ of these conditions is a parameter of V₀'s VAR (7) fixed between V₀'s data parameter and a₁, which VAR Theorem 1 admits as in #W8.12-8.
    {#W10.5.96-1} It is fixed after α₀, under the upper bounds on ε₁ above and in §8 (*The conditions on the constants.*).
    {#W10.5.96-2} The conditions that contain ϱ̄ or α_c, among them O(1)L²R₀M₀α_c ≤ C₁ε₁/2 and O(1)ϱ ≤ C₁ε₁/4, then hold for γ small, since ϱ = c_ρα_m tends to 0 with γ (the LF note's *The joint line.*), and so does the data parameter, which is ≤ Cḡp₀(ḡ) (§8).

{#W10.5.97} *The gauge choice.*
- {#W10.5.98} The split of §3(d) holds for any linear lift ℒ, but its first bracket evaluates 𝐄^B(𝐔^B, ·) at fixed 𝐔^B, which is not invariant under a fine gauge shift of 𝐀 alone beyond first order.
  {#W10.5.98-1} So ℒ must be the lift for which the second bracket is the frozen difference of the LF note's (i).
  {#W10.5.98-2} That frozen difference is built with ι in VAR's axial gauge, hence with dι_Y = H₁𝔡 + D_Bγ.

  {#W10.5.100} The gauge invariance of the terms removes the gauge term from the lift.
  {#W10.5.100-1} The functions 𝐕_k(Y, 𝐔, 𝐉, B) and the terms 𝐄^{(j)}(X, U) are invariant under the simultaneous transformations 𝐔 → 𝐔^u, 𝐉 → R(u)𝐉, and B → R(u)B of RG I (3.29), for G^c-valued u in a small neighbourhood of the G-valued ones (RG II p.011 l.27–28; RG I p.257 l.25, p.276 l.17–22).
  {#W10.5.100-2} So the frozen difference G − 𝐓^A of the LF note's (i) is unchanged when the pair lift (ι_YV, Q₁^{pl}(ι_YV)*J(V)) is replaced by (ι_YV^{u(V)}, R(u(V))Q₁^{pl}(ι_YV)*J(V)), with every fluctuation argument B of the terms rotated to R(u(V))B, for any u(V) analytic in V with values in that neighbourhood.
  {#W10.5.100-3} Write V = Ũe^{v} near the aligned background and take u(V) := exp(−γ(v)), so that u(Ũ) = 1.
  {#W10.5.100-4} Then:
  - {#W10.5.101} by this gauge transformation, the transformed lift has the derivative dι_Y − D_Bγ = ℒ_ι at c^A, with no gauge term, so the bounds of this subsection apply to it as they stand;
  - {#W10.5.102} the cost moves into the current, whose derivative gains the commutator −[γ(v), Q₁^{pl}(ι_YŨ)*J(Ũ)], which reads γ itself, not its differences;
  - {#W10.5.103} γ is bounded at zeroth order.
    {#W10.5.103-1} On each block the axial condition gives D_Bγ = −ℒ_ιv on the bonds of the axial tree, a path of at most dL bonds of length ε/L from the coarse site, where γ = Θ₁ℒ_ιv.
    {#W10.5.103-2} With the factor 2 for Ad of a transport, |γ(x)| ≤ (O(1) + 2d)ε sup_{B(x)}|ℒ_ιv| ≤ (O(1) + 2d)εB_ιΣ_ce^{−½δ₁d_ε(x,c)}|v(c)| at real backgrounds, so u(V) lies in the neighbourhood for v in the domain of the terms.

  {#W10.5.104} What the transfer adds to the LF note's (δ):
  - {#W10.5.105} The commutator.
    {#W10.5.105-1} It is of first order in v and not δ-small by itself.
    {#W10.5.105-2} Split the pair-lift current at the lifted decoupled configuration ι_YW, W := e^{iη𝐇^A(s)}c^A, as Q₁^{pl}(ι_YW)*J(W) = J^B(ι_YW) + δJ(W), with J^B run B's own current (RG I p.261 l.33–39) and δJ the pair-lift current defect, which the LF note's (δ) already compares (its piece (δ) of (ii)).
    {#W10.5.105-3} J^B is covariant, J^B(U^u) = R(u)J^B(U), for G^c-valued u near G, since ∂U is conjugated by u, D* is covariant, and Im is the analytic extension of PBG p.391 l.42–45.
    {#W10.5.105-4} So R(u)J^B(ι_YW) = J^B((ι_YW)^u), the own current of the transformed configuration, with no commutator, and the commutator is −[γ(v), δJ(W)] alone.
    {#W10.5.105-5} The terms are analytic in the current, so its effect on a term f is at most 2 sup|γ| times the J-derivative bound of f times |δJ(W)|, that is, 2 sup|γ| ≤ 2(O(1) + 2d)ε sup|ℒ_ιv| times the bound of (δ)'s current part, when that bound is of the form ‖∂_Jf‖|δJ|.
    {#W10.5.105-6} Since 2 sup|γ| carries the factor ε/a_j, a bound |δJ| ≤ O(1)(a_j/ε)^{1−β_J}a_j^{−3} with β_J > 0 suffices.
    {#W10.5.105-7} The part Q₁^{pl}*J(W) of δJ is bounded by the class at W; the part J^B(ι_YW), the own current of the lifted configuration, is bounded with β_J = 2β_o/3 through the constraint identity J^B = Q₁^{pl}*(J(W) + ∇Δ(W)), §12's oscillation bound at real points, and the two-constants theorem at complex points (the LF note's *The gauge terms of the transformed pair lift.*, *The part at ι_XW.*).
  - {#W10.5.106} The rotation of B. In RG II, B′ of 𝐇_k(B′) is the local function of B of (I.3.2) (RG II p.3 l.33–34), so γ is linear in the fluctuation, and R(u)^{−1}B − B = −[γ_c, B] + ⋯, with γ_c := γ at the coarse sites, is of second order in it.
    {#W10.5.106-1} It is not a lift nonlinearity or a current difference.
  - {#W10.5.107} The configuration.
    {#W10.5.107-1} The gauge factor u(W) of (ι_YW)^{u(W)} beyond first order in the fluctuation.
  {#W10.5.108} The transfer leaves the value of (δ) unchanged: by the invariance quoted above, run B's term at the pair lift equals its value at the transformed pair lift ((ι_YW)^{u(W)}, R(u)Q₁^{pl}(ι_YW)*J(W), R(u)B), with ι_X in place of ι_Y for the term of the polymer X, as in the LF note's piece (δ) of (ii).
  {#W10.5.108-1} Written at the transformed pair lift, which is the form in which (δ) meets ℒ_ι, (δ) contains the three terms above.
  {#W10.5.108-2} The LF note's (δ) is stated in this form (its #4.275.5–#4.275.5-2), and it stays outside (W-δ), bounded there (its #4.275).
  {#W10.5.108-3} Within (Wδ-2), the form (c), the gauge term is removed by this transfer.

### 10.6 Dependencies and Rates {#WS10.6}

{#W10.6.17} The derivations of 10.1–10.5 are not circular. They use run B's own conditions at the chain configurations ((3.35), (3.36), and (3.37), from the LF note's member and joint-line sections), the Cauchy note's §9.8 and §10.4, PBG, VAR, CRE, RG I, and RG II.
{#W10.6.17-1} None of these uses (W-δ).
{#W10.6.17-2} The Cauchy note consumes (LF), and (W-δ) is an input of (LF), but the Cauchy note's §§9–10, which are all that is used here, contain no reference to (LF) or (W-δ), and read the LF note only for its parameter choices (#4.22–#4.25, #D.R_ι, and #D.M₁), which contain no estimate.
{#W10.6.17-3} From the LF note, 10.5 reads the form c(t) = e^{it(ε/L)𝐒_c}c^B of the joint line's points and the room ϱ that it reads (#4.301, #4.301-3), VAR (9)–(10) at the real member (#4.315), and the collar of Y^∼ (#4.329); these cite this note only for §8's stages, §12's #W12.22 and #W12.237, and the one-step problem at k = 1 as a method, and none of them uses (W-δ). The current along the joint line (#4.307–#4.312), which reads the LF note's (δ) and through it §11, is not read by 10.5.
{#W10.6.17-4} (Wδ-2) uses the coarse side of (Wδ-1) only through the functional form of β_□, which contains no lift; the fine side of (Wδ-1) is the fine form (c), which (Wδ-2) supplies.
{#W10.6.17-5} (Wδ-2) uses run B's own fixed points D and 𝒜₁ (VAR (49)–(50), (175)), not their run difference, which is (Wδ-3); (Wδ-3) uses (Wδ-2), not conversely.

{#W10.6.19} The rates are δ₀′ = min(δ₀, ¼δ_Q, ¼δ₁, ¼δ_c) in §5(c), (W-c), §7, and (W-M), the terms ¼δ₁ and ¼δ_c for the fine-side lift (10.5), δ_c := (1/16)min(δ_V, δ₀, δ₁); δ₀′/54 for C_□ (10.3) in §7 and (W-M); and δ_gf′/3, δ_gf′ = min(δ₀/486, δ₀′), for G_□ in §5(c) and (W-c), and correspondingly in §7 and (W-M), δ_D′ being independent of R₀M₀ (§11, *The junction sums.*). 10.5 also uses (3.43) for G^A at β₂ = (1 + β)/2.

## 11. The Nonlinear Functions Between the Runs (Wδ-3) {#WS11}

{#WOG.5} **(Wδ-3) The nonlinear functions between the runs.** 𝐇_k of RG II (1.2) is built from the propagators through the fixed points D of (1.3) and 𝐀₀ of (1.4), whose local functions C_j (VAR (44), (49)) and δV/δA′ (VAR (80)) are each run's own.
{#WOG.5-1} The decoupling replaces only the propagators (RG II p.3 l.30–33), so the two runs' 𝐇_k(s) also differ through these functions.
{#WOG.5-2} By (B4) of the Cauchy note's §10.1 the n-fold double bar of run B is the (n − 1)-fold one of run A applied to the one-step double bar.

{#W11.1} Notation as in VAR §C (p.285–286) and RG II (1.2)–(1.5).
{#W11.1-1} In each run, Q_j(ηA) = L^jηQ_jA + C_j(L^jηA) on Λ_j (VAR (44)), with Q₀ = 1 and C₀ = 0.
{#W11.1-2} For a field A write C(A) for the data C_j(L^jηA) on Λ_j, j = 0, …, k, and Q̂ for the linear multiscale average (L^jηQ_j)_j, so that Q̂H = 1 by (45) for the original propagator.
{#W11.1-3} Run B has η_B = ε/L and the background U^B := ι_Yc^A of the aligned pair; run A has η_A = ε and the background c^A = MU^B.
{#W11.1-4} The scale j + 1 of run B is the scale j of run A: Λ^A_j = Λ^B_{j+1} for all j, and Λ^A_0 = Λ^B_0 = Λ^B_1 = ∅ (*The alignment of the global sets.* below).
{#W11.1-5} Q₁ := Q̄₁(U^B) is the linear part of the one-step double bar at U^B.

{#W11.2} *The global lift.* ℒ is the lift of the Cauchy note's §10.4 (its #C10.4.1-2, with the correction of #C10.4.110-1), ℒg := Ig + Q₁*(Q₁Q₁*)^{−1}(g − Q₁Ig), with the gauge-covariant interpolation I of its *Regularity of the Lifts.* (#C10.4.108).
{#W11.2-1} Q₁ℒ = 1 holds exactly on Y^∼, for every I, with Q₁ taken on the coarse bonds whose stencils (both endpoint blocks) lie in Y^∼ (*The bridge to ℒ_ι.* below).
{#W11.2-2} Its bound in VAR's norms is as follows.
- {#W11.3} I carries the coarse values to the fine bonds by the transports of U^B, with weights summing to 1, so |Ig| ≤ |g|.
  {#W11.3-1} In the gauge of VAR's cube at the global index j, in which PBG's (3.35) for U^B at the global layers (*The domain and the global-layer inputs.* of the bridge below) bounds the field, the background field is < c_uMα₀(L^jε)^{−1}, so |∇_BIg| ≤ O(1)(|∇_Ag| + c_Gc_uMα₀(L^jε)^{−1}|g|).
- {#W11.4} Q₁I reproduces affine fields at U^B = 1 (the Cauchy note's #C10.4.108-2), and Q₁ at U^B differs from Q₁ at 1 by O(ε) times the background field.
  {#W11.4-1} Hence |g − Q₁Ig| ≤ O(1)(ε|∇_Ag| + c_uMα₀L^{−j}|g|).
- {#W11.5} The spectrum of Q₁Q₁* lies in [m_Q/2, M̃_Q], with the decay rate δ_Q, by the Cauchy note's *Regularity of the Lifts.* (#C10.4.111–#C10.4.113-1), whose input ε²|F| ≤ C₀ε₁ holds at U^B on Y^∼ by *The domain and the global-layer inputs.* of the bridge below.
  {#W11.5-1} So (Q₁Q₁*)^{−1} is bounded in sup norm by C_Q′ := O(1)m_Q^{−1}Σ_ze^{−δ_Qd(0,z)} (the Cauchy note's C_Q with the rate δ_Q in place of ½δ_Q).
  {#W11.5-2} Across a boundary of VAR's global layers the weights of the norms change by at most L^{2+β₂} for the gradient and Hölder entries and by L³ for the current terms, so by at most L³ per boundary.
  {#W11.5-3} By VAR (1) (p.277), (L^jε)^{−1}dist(Ω_j^c, Ω_{j+1}) > RM₁ in run A's units, so the layer i has width more than RM₁L^iε ≥ RM₁ε, a point of the layer j lies at distance more than RM₁ε from the layers j ± 2, and every further boundary crossed adds at least RM₁ε.
  {#W11.5-4} The factor L³ of the adjacent layer goes into the constant.
  {#W11.5-5} Half of the rate, e^{−½δ_Qd_ε}, absorbs the factor L³ of each further boundary under δ_QRM₁ ≥ 6 log L, and the other half remains for the sums.
  {#W11.5-6} So the weighted bound holds with C_Q′ replaced by O(1)L³C_Q′ and the rate ½δ_Q.
- {#W11.6} Q₁* is tube-constant up to the non-main terms of CMP 98 (124) (the Cauchy note's #C10.4.113-4–#C10.4.113-6), with |Q₁*h| ≤ 2(1 + 2dL^{d−1})|h| (#C10.4.113-3, #C10.4.113-7).
  {#W11.6-1} Since each fine difference is the difference of two such values, |∇_BQ₁*h| ≤ 4(1 + 2dL^{d−1})(L/ε)|h|.

{#W11.7} Since L^{j+1}η_B = L^jε, the weights of the norms |·|_{(−1)} and |∇·|_{(−2)} agree on aligned sets.
{#W11.7-1} So

  {#W11.8} (H_ℒ^g) max(|ℒg|_{(−1)}, |∇ℒg|_{(−2)}) ≤ C_ℒ^g max(|g|_{(−1)}, |∇g|_{(−2)}), C_ℒ^g := O(1)L^{d+3}C_Q′(1 + c_Gc_uMα₀),

{#W11.9} a constant of L, d, and G: the gradient of the second term of ℒg is at most 4(1 + 2dL^{d−1})(L/ε) times O(1)L³C_Q′ (#W11.5-6) times the bound of #W11.4-1, and in the weight (L^jε)² this is O(1)L^{d+3}C_Q′(1 + c_uMα₀)max(|g|_{(−1)}, |∇g|_{(−2)}), since (L^jε)²(L/ε)(ε|∇g| + c_uMα₀L^{−j}|g|) = L|∇g|(L^jε)² + Lc_uMα₀|g|L^jε.

{#W11.10} For the local forms (c), §5(c) uses the cut-off χ_Bℒ_N of the right inverse ℒ_N of 10.1, not this ℒ, and the form (c) itself is stated with ℒ_ι of §3(c).
{#W11.11} *The bridge to ℒ_ι.*
- {#W11.12} The domain and the global-layer inputs.
  {#W11.12-1} U^B = ι_Yc^A is defined on Y^∼ only (the Cauchy note's #C9.8.13–#C9.8.13-2, read at X = Y), so Q₁ is taken on the coarse bonds whose stencils (both endpoint blocks) lie in Y^∼, as 10.1 compresses Q₁ for T_N.
  {#W11.12-2} The fields that the bridge acts on are supported in Y^∼ (*The support.* below).
  {#W11.12-3} In §11, U^B always means ι_Yc^A; 10.5's global lift of V₀ is written ι(V₀) here.
  {#W11.12-4} At the real chain configuration c^A = V₀, 10.5's *The base and the local gauge* gives ι(V₀) with PBG's (3.35) and (3.36) at the global layer index j(x) of VAR's layers, from V₀'s layer bounds (VAR (9)–(10)) through the argument of the Cauchy note's §9.7, and U^B = ι_Yc^A = e^{i(ε/L)T}ι(V₀) with the tail T of the Cauchy note's §9.8.  {#W11.12-6} By the Cauchy note's #C9.8.15-1 (§9.8, *The decay.*), |∇T| ≤ C_ιε₁a^{−2}, with the further bounds of 10.5's *The exactness.* So, on Y^∼, ε²|F| ≤ C₀ε₁ and |F| ≤ O(1)Mα₀a_{j(x)}^{−2} at U^B, at the global layer of each point.
  {#W11.12-7} The layered current bound |J| ≤ O(1)Mα₀a_{j(x)}^{−3} holds for ι(V₀).
  {#W11.12-8} At U^B it holds on the support of the fields of *The support.* below, which lies at a distance at least M₁a_k minus the collar's width (≤ RM₁ε/L + M₁ε) from the collar.
  {#W11.12-9} Near the collar the fine second differences of T give only |J| ≤ O(1)LC_ιε₁ε^{−3}.
  {#W11.12-10} That crude bound is all that the inner-scale inputs of Theorem 3.12 use, and it gives (3.36) at the scale ε under LC_ιε₁ ≤ O(1)Mα₀.
  {#W11.12-11} The data bound below reads J only through H₁*J-type terms and local Δ′ terms at points of the support, so the collar enters only through kernels with the decay e^{−δ_brM₁L^k}/O(1).
  {#W11.12-12} The ratio of the crude current bound to the layered weight is at most L^{3k+1}.
  {#W11.12-13} With x := L^k, x³e^{−δ_brM₁x} ≤ (3/(eδ_brM₁))³, so L^{3k+1}e^{−δ_brM₁L^k} ≤ L(3/(eδ_brM₁))³ ≤ 1 under δ_brM₁ ≥ 2L^{1/3}.
  {#W11.12-14} The boxes of the localisation of the Cauchy note's #C10.4.112 then read U^B only on Y^∼, so the spectrum of Q₁Q₁* lies in [m_Q/2, M̃_Q] there, with the decay rate δ_Q of #C10.4.113-1.
  {#W11.12-15} PBG Theorem 3.12 for the one-step problem on Y^∼ needs only (3.35)–(3.36) at the inner scale ε, which these bounds give.
  {#W11.12-16} All curvature and current terms below are taken with these global-layer bounds, and not with 10.5's bounds on the local shells of □.
- {#W11.13} The support.
  {#W11.13-1} At the decoupled parameters s, the kernels of H(s), G̃(s), and H₀(s) vanish unless both arguments are in the interior of one component of Y(σ), at distance more than M₁ from its boundary, and 𝐀₀ vanishes on a neighbourhood of Y(σ)^c (RG II p.4 l.18–24).
  {#W11.13-2} So every field on which the bridge acts below, namely H^A(s)c, H₀^A(s)B′, G̃^A(s)μ, 𝐇^A(s), and the sources of G̃^B(s), is supported in Y, at distance at least M₁a_k from the collar Λ₀ of the one-step problem on Y^∼ (10.5, *The inclusion.*).
  {#W11.13-3} No cut-off is needed, and the bounds below hold at every point, so in the global norms |·|_{(−1)} and |∇·|_{(−2)}.
- {#W11.14} ℒ_ι. ℒ_ι is §3(c)'s, at the background U^B = ι_Yc^A of this section.
  {#W11.14-1} Its constraint is the same Q₁, and Q₁ℒ_ι = 1 on the data of Λ₁ exactly (10.5, *The exactness.*), so (ℒ − ℒ_ι)u ∈ ker Q₁ on Λ₁.
  {#W11.14-2} The gauge term of dι_Y is removed by 10.5's *The gauge choice.*, not by this bridge.
- {#W11.15} The formula.
  {#W11.15-1} Let u be a run-A field supported in Y, at distance more than one block from the coarse bonds whose fine bonds meet Λ₀, so that u = 0 outside Y^∼ and near the collar, and ℒ_ιu is extended by 0 outside Y^∼.
  {#W11.15-2} Let h := u − Q₁Iu on Λ₁, the h of 10.5's *The Hölder bound.* Then 10.5's *The refined gradient.* gives ℒ_ιu = Iu + H₁h − C̃₁G₁^{−1}Iu with C̃₁ := G₁ − H₁Q₁G₁, and the definition gives ℒu = Iu + Q₁*(Q₁Q₁*)^{−1}h.
  {#W11.15-3} So
  {#W11.16} (ℒ − ℒ_ι)u = (Q₁*(Q₁Q₁*)^{−1} − H₁)h + C̃₁G₁^{−1}Iu.
  {#W11.17} Both terms vanish at U^B = 1 for fields affine near the point, since Q₁I reproduces affine fields (the Cauchy note's #C10.4.108-2) and (Δ + DRD*)Iu = 0 for affine u, with Q₁*aQ₁ annihilated by C̃₁.
- {#W11.18} The data bound. 10.5's *The Hölder bound.*, at the exponent β₂ < 1, bounds |h| ≤ Cε(6ε)^{β₂}‖∇_Au‖_{β₂} + max(C, 1)C_trε²|F||u| on Λ₁, and the gradients of H₁h and of C̃₁G₁^{−1}Iu (its bullets on H₁h, C̃₁D*λ, C̃₁DRD*Iu, and the k₀-type terms) by C′ε^{β₂}‖∇_Au‖_{β₂} plus terms of size ε|F||u| and of the k₀-type with L^{−n}, L^{−2n}, or L^{−3n}, up to the decay e^{−½δ₁d_ε}.
  {#W11.18-1} Their sup is at most O(1)ε times the same, since H₁ and C̃₁ gain a factor ε in sup against their gradient ((3.133), and (3.42) for G₁).
  {#W11.18-2} By the Cauchy note's #C10.4.113-1 and #C10.4.113-3 and the last bullet of *The global lift.*, |Q₁*ν| ≤ 2(1 + 2dL^{d−1})|ν| and |∇_BQ₁*ν| ≤ 4(1 + 2dL^{d−1})(L/ε)|ν|, with the decay e^{−δ_Qd_ε} of (Q₁Q₁*)^{−1}.
  {#W11.18-3} With N_n(u) := max((L^nε)|u|, (L^nε)²|∇_Au|, (L^nε)^{2+β₂}‖∇_Au‖_{β₂}) on the blocks of run A's layer n, and (L^nε)²·ε^{β₂}(L^nε)^{−2−β₂} = (ε/a_n)^{β₂}, this gives at a point x of the layer n
  {#W11.19} (L^nε)|(ℒ − ℒ_ι)u(x)| + (L^nε)²|∇_B(ℒ − ℒ_ι)u(x)| ≤ C_br(ε/a_n)^{β₂}Σ_ye^{−δ_brd_ε(x,y)}N_{n(y)}(u),
  {#W11.20} with δ_br := min(¼δ_Q, ¼δ₁), C_br := O(1)L^{d+4}(C + C′ + C_Q′C + C_tr + B₀ + (C_Q′ + B_ι)(r_I² + C_trMα₀) + O(1)Mα₀), where C′ includes the constant B₀′(½)L^{1/2} of (3.44) for the entries C̃₁D* and C̃₁D, and B₀ + (C_Q′ + B_ι)(r_I² + C_trMα₀) is the source side's (#W11.21-10).
  {#W11.20-1} The weights of N_{n(y)} and of the left side differ by at most L^{2+β₂} per boundary of VAR's global layers for the gradient and Hölder entries, and by L³ for the current terms.
  {#W11.20-2} The adjacent layer's factor L³ is in C_br; each further boundary adds at least RM₁ε to the distance (VAR (1)), and half of the rate absorbs its factor L³ under δ_brRM₁ ≥ 6 log L, as in the spectrum bullet of *The global lift.*, with δ_br the rate that remains.
  {#W11.20-3} In 10.5's bullets the curvature and current enter through ε|F| and ε²|J|.
  {#W11.20-4} They are taken with the global-layer bounds of the first bullet at the layer n of the point: (L^nε)·ε|F| ≤ O(1)Mα₀(ε/a_n) and (L^nε)·ε²|J| ≤ O(1)Mα₀(ε/a_n)², both ≤ O(1)Mα₀(ε/a_n)^{β₂}.
  {#W11.20-5} The Hölder and sup bounds of H₁, C̃₁, and G₁ used there are those of PBG Theorem 3.12 and (3.42)–(3.44), with B₀′(½) in (3.44), for the one-step problem on Y^∼ at the inner scale ε, which read only these bounds.
- {#W11.21} The source side.
  {#W11.21-1} For a run-B source λ, (ℒ − ℒ_ι)*λ = (1 − I*Q₁*)((Q₁Q₁*)^{−1}Q₁ − H₁*)λ + I*G₁^{−1}C̃₁λ, from ℒ* = I* + (1 − I*Q₁*)(Q₁Q₁*)^{−1}Q₁ and ℒ_ι* = H₁*.
  {#W11.21-2} Both parts are run-A sources of divergence form.
  {#W11.21-3} For the first, 1 − Q₁I has finite range r_I and annihilates affine fields at U^B = 1, so each column (1 − I*Q₁*)δ_c is finitely supported and orthogonal to the affine fields.
  {#W11.21-4} It is therefore ∇_A*∇_A*K_c with K_c supported in the same range and |K_c| ≤ O(1)r_I²ε², and the background adds C_trε²|F| times a source.
  {#W11.21-5} For the second, G₁^{−1}C̃₁λ = (1 − Q₁*H₁*)λ, and the term Q₁*aQ₁ of G₁^{−1} drops, since Q₁C̃₁ = 0.
  {#W11.21-6} So it is D_B*(D_BC̃₁λ) + D_B(RD_B*C̃₁λ) plus the Δ′, Δ_π′, and Δ_π^{(2)} terms.
  {#W11.21-7} These are fine derivatives, a divergence and a gradient, of fields bounded by O(1)|∇_BC̃₁λ| ≤ O(1)B₀εΣe^{−½δ₁d_ε}|λ| (#W11.30-2), plus the Δ′, Δ′_π, and Δ_π^{(2)} terms, which carry ε²|F| or ε³|J| at the global layer of the point, so O(1)Mα₀(ε/a_j)² or O(1)Mα₀(ε/a_j)³ relative to |λ|, by the first bullet.
  {#W11.21-8} I* carries a fine divergence ∇_B*f or gradient ∇_Bf to a coarse one, ∇_A*f̃ or ∇_Af̃, with |f̃| ≤ O(1)|f|, since the fine differences of Iv are interpolated coarse differences of v up to curvature terms (10.1's gradient bullet).
  {#W11.21-9} PBG (3.42) for the entry G∇* gains one factor (L^jε)^{−1} less than G. The factor (Q₁Q₁*)^{−1}Q₁ − H₁* contributes C_Q′ + B_ι.
  {#W11.21-10} So |G̃^A(ℒ − ℒ_ι)*λ| ≤ O(1)(B₀ + (C_Q′ + B_ι)(r_I² + C_trMα₀) + Mα₀)(ε/a_j) times the bound of G̃^A on the source Σ_ye^{−δ_brd_ε(·,y)}|λ(y)| in |·|_{(−1)}: the first part gives (C_Q′ + B_ι)r_I² through the entry G∇* on ∇_A*K_c, of size O(1)r_I²ε, and (C_Q′ + B_ι)C_trMα₀(ε/a_j)² from the background; the second gives B₀ through G∇*, and Mα₀(ε/a_j)² from the Δ′ terms; and ε ≤ a_j.
  {#W11.21-11} The term (ℒ − ℒ_ι)*λ itself is not supported in Y, since (Q₁Q₁*)^{−1} spreads it; it enters only through G̃^A(s), whose kernel restricts the source variable to Y(σ) (*The support.*), so it is paired with fields that vanish near the collar.
  {#W11.21-12} In |∇·|_{(−2)} the entry ∇G∇* of (3.44) with the crude lattice Hölder bound of (a) below gives (ε/a_j)^{1−β′}, any β′ ∈ (0, 1).
- {#W11.22} The applications.
  {#W11.22-1} The propagator terms of §11 are rewritten as
  {#W11.23} H^B − ℒH^A = (H^B − ℒ_ιH^A) − (ℒ − ℒ_ι)H^A, H₀^B − ℒH₀^A likewise, and
  {#W11.24} G̃^B − ℒG̃^Aℒ* = (G̃^B − ℒ_ιG̃^Aℒ_ι*) − (ℒ − ℒ_ι)G̃^Aℒ_ι* − ℒG̃^A(ℒ − ℒ_ι)*.
  {#W11.25} The first term of each is the form (c) (§3(c), with 𝒥′ = ℒ_ι* on sources) and carries δ_w.
  {#W11.25-1} The others are the bridge applied to H^Ac, H₀^AB′, G̃^Aℒ_ι*λ, and λ.
  {#W11.25-2} The fields H^Ac, H₀^AB′, and G̃^Aμ have the C^{1,β₂} bound N_n at the layer n by (3.133) and (3.43) at the exponent β₂, with B₀(β₂), and the walk-decoupled H(s(Y₀))X is analytic in s on |s(Y₀)| ≤ e^{κ₁} and "bounded by B₀e^{16κ₁}|X| in all norms of Theorems 3.1.–3.10 [13]" (RG II p.5 l.15–16), with the same for H₀(s) and G̃(s) by the same walk expansion.
  {#W11.25-3} So these terms carry C_bre^{16κ₁}(ε/a_j)^{β₂}, or C_bre^{16κ₁}(ε/a_j)^{1−β′} on the source side.
  {#W11.25-4} The output of §11 is Δ_𝐇 = 𝐇^B − ℒ𝐇^A.
  {#W11.25-5} The consumer's §3(d) needs 𝐇^B − ℒ_ι𝐇^A = Δ_𝐇 + (ℒ − ℒ_ι)𝐇^A. 𝐇^A(s) has the bound N_n from the propagator bounds: H₀(s) and H(s) on the data and D, and G̃(s) for 𝐀₀, each with its Hölder entry, with the sup bound |D(H(s(Y₀)), A′)| ≤ 4C₂|A′|² of RG II (1.14) (p.5) and the bounds of δV/δA′ from Proposition 4 of [15], which "holds for it (with ε₃ replaced by ε₂)" (RG II p.5 l.40–41).
  {#W11.25-6} So the last term carries C_bre^{16κ₁}(ε/a_j)^{β₂}.
- {#W11.26} The complex chain configurations.
  {#W11.26-1} At a point c(t) of the joint line, the bridge is rerun at U₁ := ι_Y(Mc(t)), the one-step minimiser on Y^∼ at the complex data Mc(t), with all norms in the frame of the representative U₁ below.
  {#W11.26-2} The formula and the source-side identities are algebraic and hold at U₁ unchanged.
  {#W11.26-3} The inputs at U₁ are derived from the real background U^B, with no rerun of PBG at a complex background, as follows.
  - {#W11.27} The representation.
    {#W11.27-1} On Y and within 2L fine spacings of it, c(t) = e^{itη𝐒_c}c^B and U^B = ι_Yc^A = e^{iη𝐒_c}c^B (the LF note's *The Lift ι_Y.*; 10.5, *The base and the local gauge*), with η = ε/L.
    {#W11.27-2} There the two exponents on each bond are multiples of one element of the Lie algebra, so c(t) = e^{iηW̃}U^B exactly, with W̃ := (t − 1)𝐒_c, and a_{j(x)}|W̃(x)| + a_{j(x)}²|∇W̃(x)| ≤ 2ϱ̄ for |t| < 1/r(Y), with ϱ̄ := sup_Yϱ, on Y; within 2L fine spacings off Y the same bound holds with an extra factor O(L), since there it needs σ_c and ϱ at neighbouring points.
    {#W11.27-3} The terms of V(Y) read the line only on Y (the localised term "depends on 𝐔, 𝐉 restricted to Y₀ ∪ □₀", RG II p.5 l.2–3), and r(Y) is a supremum over Y, so off this neighbourhood of Y the line is extended by the t-independent ι_Yc^A, as 10.5 does ("Off Y, U′(t) = e^{i(ε/L)T}").
    {#W11.27-4} So W̃ := 0 there, and Mc(t) = c^A on the data off it, the collar Λ₀ included.
    {#W11.27-5} At ∂Y, W̃ jumps by at most O(L)ϱ̄/a over one fine bond of spacing η = ε/L, so there only the crude bounds η|W̃| ≤ O(1)ϱ̄ε/a and |∇W̃| ≤ O(1)L²ϱ̄/(aε) hold.
    {#W11.27-6} Every field of *The support.* lies at a distance > M₁a_k from ∂Y, since Y₀ ⊂ Y. So the jump enters the bounds at the support only through kernels with the decay e^{−δ_br^cM₁L^k}, at the rate δ_br^c of the conclusion below.
    {#W11.27-7} This beats the ratio O(1)L²a/ε ≤ O(1)L^{k+2} of the crude bound to the layered one, since L^{k+2}e^{−δ_br^cM₁L^k} ≤ L²/(eδ_br^cM₁) ≤ 1 under δ_br^cM₁ ≥ L²/e.
    {#W11.27-8} The Neumann series of *The operators at U₁.* read ℋ only through η|ℋ| and ε²|∇ℋ| (#W11.37-2), and these stay within κ_ℋ at the jump: Θ₁ integrates along at most dL fine bonds of length η, so |D̄(Θ₁W̃)| ≤ O(1)sup|W̃| and |B| ≤ O(L)ϱ̄/a there by #W11.28; hence ε²|∇H₁B| ≤ O(1)LB_ιϱ̄ and η|H₁B| ≤ O(1)B_ιϱ̄, both ≤ κ_ℋ since C_ℋ ≥ O(1)L⁴B_ι, and 𝒜₁ and HD begin at second order in H₁B (#W11.31-1).
    {#W11.27-9} M is the plain average (ι's constraint is Q₁^{pl}dι_Y = 1, 10.5), while VAR (44) (p.285) expands the double bar Q₁ := Q̄₁(U^B).
    {#W11.27-10} By CMP 98 (88)–(89) (p.031) the plain ratio is the double-bar ratio between the return factors (\overline{R_{0,c_±}V₁}) of the two endpoint blocks.
    {#W11.27-11} Their linear parts give the gauge term of (B1)–(B2) of the Cauchy note's §10.1, so Mc(t) = e^{iεB}c^A with
    {#W11.28} B = Q₁W̃ − D̄(Θ₁W̃) + O(c_Gε|W̃|²), |D̄(Θ₁W̃)| ≤ O(1)Lε|∇W̃| + O(1)ε²|F||W̃|.
    {#W11.29} B satisfies VAR (172) (p.305 l.31–35) on Y^∼ under O(1)Lϱ̄ ≤ C₁ε₁/4, so VAR's Sect. G (p.305 l.31–52), with the real base U₀ := U^B = ι_Y(c^A), gives U₁ = exp(iηℋ)U^B in the Landau gauge.
    {#W11.29-1} Here ℋ = 𝒜₁ + H₁B − HD(𝒜₁ + H₁B) (VAR (174)), with 𝒜₁ the solution of (175), and H₁, H, and 𝔊 are taken at the real U^B.
    {#W11.29-2} The data change vanishes on Λ₀ by the extension above.
    {#W11.29-3} The output is VAR's Landau representative.
    {#W11.29-4} The frame of ι_Y(Mc(t)) differs from it by the complex return gauge g of the block, with |Ad(g)| ≤ e^{O(1)Lc_G sup|ηℋ|} ≤ 2 under O(1)Lc_G(1 + B₀)ϱ̄ ≤ ½ log 2 (as for g in 10.5).
    {#W11.29-5} All bounds below are taken in the Landau frame and carry this factor 2 in the frame of ι_Y(Mc(t)).
    {#W11.29-6} On the data side, the frame changes from c^A to Mc(t), and ∇_{Mc(t)} − ∇_{c^A} is of size c_G|εB|.
    {#W11.29-7} This multiplies N_n by at most 1 + O(1)c_Gϱ̄.
  - {#W11.30} The first-order field.
    {#W11.30-1} From C̃₁ = G₁ − H₁Q₁G₁, 1 − H₁Q₁ = C̃₁G₁^{−1}, so H₁B − W̃ = −C̃₁G₁^{−1}W̃ + H₁(B − Q₁W̃).
    {#W11.30-2} Since Q₁C̃₁ = 0 and C̃₁ is symmetric at the real U^B, the term Q₁*aQ₁ of G₁^{−1} drops, and C̃₁G₁^{−1}W̃ = C̃₁D*(DW̃) + C̃₁D(RD*W̃) + C̃₁(Δ′ + Δ′_π + Δ_π^{(2)})W̃, as in *The source side.* At the real U^B, PBG Theorem 3.12 and (3.130)–(3.133), with the entries (3.42)–(3.44) at the inner scale ε, give |∇C̃₁h| ≤ O(1)B₀εΣ_ye^{−½δ₁d_ε(x,y)}|h(y)|, and, for C̃₁D* and C̃₁D, one factor ε less with the constant B₀″ := B₀′(½)L^{1/2}(1 + B_ι)B₀ of (3.44) and the lattice Hölder trick (10.5).
    {#W11.30-3} With |DW̃|, |RD*W̃| ≤ O(1)ϱ̄a^{−2} and the Δ′ terms carrying ε²|F| or ε³|J| relative to |W̃|, this gives |∇C̃₁G₁^{−1}W̃| ≤ O(1)B₀″(1 + Mα₀)Σ_ye^{−½δ₁d_ε}ϱ̄a_{j(y)}^{−2}.
    {#W11.30-4} The second term is H₁(B − Q₁W̃) = −H₁D̄(Θ₁W̃) + H₁O(c_Gε|W̃|²).
    {#W11.30-5} Since ∇H₁ is at most B_ιε^{−1} times a decaying kernel, |∇H₁D̄(Θ₁W̃)| ≤ O(1)B_ιΣe^{−½δ₁d_ε}(L|∇W̃| + ε|F||W̃|) ≤ O(1)B_ι(L + Mα₀)Σe^{−½δ₁d_ε}ϱ̄a^{−2}, and the quadratic part gives O(1)B_ιc_GΣe^{−½δ₁d_ε}ϱ̄²a^{−2}.
    {#W11.30-6} The sums go to the layer of x as in *The data bound.*, with the adjacent layer's L³ in the constant and δ₁RM₁ ≥ 12 log L for the rest.
    {#W11.30-7} So |∇(H₁B − W̃)| ≤ O(1)L³(B₀″(1 + Mα₀) + B_ι(L + Mα₀) + B_ιc_Gϱ̄)ϱ̄a_{j(x)}^{−2}, and the sup is a factor ε smaller.
  - {#W11.31} The second-order terms.
    {#W11.31-1} By (176)–(177), 𝒜₁ and HD begin at second order in H₁B.
    {#W11.31-2} Put A′ := 𝒜₁ + H₁B; by the previous bullet, |A′| ≤ O(1)(1 + B₀)ϱa^{−1} and |∇A′| ≤ O(1)L³(1 + B₀)ϱa^{−2} at the layer of the point.
    {#W11.31-3} The fine second differences are at most 2η^{−1} = 2L/ε times the first.
    {#W11.31-4} VAR (80) (p.290 l.27–28) is V(A′) = −⟨HD₃(A′), J⟩ − ⟨A′, Δ_πHD(A′)⟩ + ½⟨HD(A′), Δ_πHD(A′)⟩ + V₀(A′ − HD(A′)), and its cubic part V^{(3)} has three kinds of terms.
    - {#W11.32} The local cubic part of V₀.
      {#W11.32-1} Its gradient is a sum of terms η[A′, ∇∇A′] and η[∇A′, ∇A′] up to transports, at most O(1)c_GL⁷(1 + B₀)²ϱ̄²a^{−3}.
    - {#W11.33} −⟨A′, Δ_πHC^{(2)}(A′)⟩, with C^{(2)} the quadratic part of D. Its gradient is Δ_πHC^{(2)}(A′) + (dC^{(2)})*H*Δ_πA′.
      {#W11.33-1} The first lies in range(Q*) + range(DR), since G^{−1}H = Q*(QGQ*)^{−1} and G^{−1} = Δ_π + DRD* + Q*aQ. 𝔓* annihilates that range, being the adjoint of the projection onto the tangent space (83) {QA = 0, RD*A = 0}, so it does not enter 𝔊 = G₁𝔓*.
      {#W11.33-2} In the second, |dC^{(2)}(A′)| ≤ O(1)c_Gε|A′| by VAR (44), |Δ_πA′| ≤ O(1)(L/ε)|∇A′|, and H* is sup-bounded by O(1)L^dB₀, the dual of (3.133), so it is at most O(1)c_GL^{d+4}B₀(1 + B₀)²ϱ̄²a^{−3}.
    - {#W11.34} −⟨HD₃^{(3)}(A′), J⟩, the cubic part of the first term.
      {#W11.34-1} Its gradient (dD₃^{(3)}(A′))*H*J has |dD₃^{(3)}(A′)| ≤ O(1)c_Gε²|A′|² and |H*J| ≤ O(1)L^dB₀Mα₀a^{−3}.
      {#W11.34-2} So it is at most O(1)c_GL^dB₀Mα₀(1 + B₀)²ϱ̄²(ε/a)²a^{−3}.
      {#W11.34-3} D₃ starts at third order (VAR (78)), so this term has no quadratic part.
    {#W11.35} ½⟨HD, Δ_πHD⟩ is of fourth order.
    {#W11.35-1} So |(δ/δA′)V^{(3)}(A′)| ≤ O(1)c_GL^{d+7}(1 + B₀)³(1 + Mα₀)ϱ̄²a^{−3}.
    {#W11.35-2} Since |∇𝔊g| ≤ O(1)B₀εΣe^{−½δ₁d_ε}|g|, the contraction of (175) gives |∇𝒜₁| ≤ O(1)c_GB₀L^{d+7}(1 + B₀)³(1 + Mα₀)ϱ̄²(ε/a)a^{−2}.
    {#W11.35-3} The terms of order m ≥ 4 of V carry m − 1 factors of A′ or its differences, so each further order has a further factor O(1)c_GL^{d+3}(1 + B₀)ϱ̄, and the series converges under O(1)c_GL^{d+3}(1 + B₀)ϱ̄ ≤ ½.
    {#W11.35-4} D begins with C^{(2)}, the second-order part of the averaging, which is local of size O(1)c_Gε|A′|², so |∇HD| ≤ O(1)B_ιc_G(1 + B₀)²ϱ̄²a^{−2}.
  - {#W11.36} The curvature and the current.
    {#W11.36-1} So |∇(ℋ − W̃)| ≤ C_ℋϱa_{j(x)}^{−2} and |ℋ| ≤ O(1)(1 + B₀)ϱa_{j(x)}^{−1}, with C_ℋ := O(1)L³(B₀″(1 + Mα₀) + B_ι(L + Mα₀) + c_G(B_ι + B₀L^{d+4})(1 + B₀)³(1 + Mα₀)ϱ̄), and ϱ̄ in place of ϱ in this bullet.
    {#W11.36-2} The plaquettes of exp(iηℋ)U^B give |F(U₁) − F(U^B)| ≤ |∇ℋ| + O(1)c_Gη|ℋ|(|F(U^B)| + |∇ℋ|) ≤ O(1)(1 + C_ℋ)ϱa_{j(x)}^{−2}.
    {#W11.36-3} So |F(U₁)| ≤ O(1)(Mα₀ + (1 + C_ℋ)ϱ)a_{j(x)}^{−2} at the global layer of each point, and ε²|F(U₁)| ≤ ε²|F(U^B)| + C₀ε₁/2 ≤ (3/2)C₀ε₁ under O(1)(1 + C_ℋ)ϱ ≤ C₀ε₁/2, by the base's ε²|F(U^B)| ≤ C₀ε₁; the bounds below that take C₀ε₁ at U₁ hold with (3/2)C₀ in place of C₀, absorbed in their O(1), and §8's thresholds that read C₀ε₁ at U₁ are stated with O(1)s that include this factor 3/2 (its square where C₀ε₁ enters squared).
    {#W11.36-4} J(U₁) − J(U^B) is the fine divergence of F(U₁) − F(U^B), at most O(1)(L/ε)(1 + C_ℋ)ϱa^{−2}, plus (D*_{U₁} − D*_{U^B})F(U^B), at most O(1)c_G|ℋ||F(U^B)| ≤ O(1)c_G(1 + B₀)Mα₀ϱa^{−3}.
    {#W11.36-5} So (L^nε)·ε²|J(U₁) − J(U^B)| ≤ O(1)L(1 + C_ℋ)ϱ(ε/a_n), which the data bound's current terms absorb with the gain (ε/a_n).
    {#W11.36-7} The gain ε/a_n comes from W̃, which already carries the data, so ℋ − W̃ is driven by the second differences of W̃, and C̃₁ gains one factor ε on them.
  - {#W11.37} The operators at U₁.
    {#W11.37-1} Q₁, Q₁Q₁*, and the local parts of G₁^{−1} (Δ_U, the averaging term Q₁*aQ₁, and the Δ′ terms) differ at U₁ from their values at U^B by local operators of range at most 2ε.
    {#W11.37-2} Their coefficients change through the transports e^{iηℋ} and through F(U₁) − F(U^B), by a relative size at most κ_ℋ := O(1)c_G(1 + C_ℋ)ϱ̄ at the scale ε^{−2}, with first differences of the same relative size.
    {#W11.37-3} G₁^{−1} = Δ_π − Δ_π^{(2)} + DRD* + Q*aQ (PBG (3.128), (3.134)–(3.135); 10.5) also contains nonlocal factors: G′ in P_π = 1 − DG′RD*, the projection R = 1 − G′Q′*(Q′G′²Q′*)^{−1}Q′G′, and H through H*J in Δ_π^{(2)} (PBG (3.135)–(3.136), p.422 l.37–48).
    {#W11.37-4} As in 10.5's resolvent identities, each of these at U₁ minus its value at U^B is a sum of products of their decaying kernels at U^B, each product containing at least one local difference of relative size κ_ℋ or one current difference.
    {#W11.37-5} G′ and Q′G′²Q′* are themselves inverted by Neumann series about U^B, with the local difference of Δ′.
    {#W11.37-6} So G₁^{−1}(U₁) − G₁^{−1}(U^B) =: δ is a kernel operator with |δ(x, y)| ≤ K_opκ_ℋε^{−2}e^{−δ₁d_ε(x,y)}, with K_op := O(1)B₀′(½)L^{1/2}(1 + C_{G′} + C_R + B_ι)², and the same for its first differences, where C_{G′} and C_R are the constants of G′ and R at U^B (PBG Corollary 3.6 and (3.24)).
    {#W11.37-7} Kernels e^{−rd} compose to e^{−(r/2)d} times Σ_ze^{−(r/2)d_ε(0,z)} =: S_r.
    {#W11.37-8} So the Neumann series G₁(U₁) = Σ_n G₁(U^B)(−δG₁(U^B))^n, in the weighted norms of (3.42)–(3.44) with the derivatives moved to neighbouring factors as in PBG (3.138), converges at the rate ½δ₁ with 2B₀, under O(1)B₀K_opS_{δ₁}κ_ℋ ≤ ½.
    {#W11.37-9} In the same way (Q₁Q₁*)^{−1} at U₁ has 2C_Q′ and the rate ½δ_Q, under O(1)C_Q′S_{δ_Q}κ_ℋ ≤ ½ (as in 10.1, #W10.1.16-4–#W10.1.16-7).
    {#W11.37-10} (Q₁G₁Q₁*)^{−1} at U₁, which H₁ needs, is a Neumann series about its value at U^B (PBG (3.130)–(3.133)), with the difference Q₁δ_GQ₁* + (Q₁ terms), δ_G := G₁(U₁) − G₁(U^B), at the rate ¼δ₁, under O(1)C_{QGQ}S_{δ₁/2}B₀K_opκ_ℋ ≤ ½, with C_{QGQ} the constant of (Q₁G₁Q₁*)^{−1} at U^B.
    {#W11.37-11} So H₁ = G₁Q₁*(Q₁G₁Q₁*)^{−1} and C̃₁ = G₁ − H₁Q₁G₁ at U₁ have the bounds of PBG Theorem 3.12 with constants O(1) times those at U^B and the rate ⅛δ₁, the products costing one halving each.
  - {#W11.38} I and the Taylor bound of Q₁I at U₁: these are the same local operators, with the transports e^{iηℋ} bounded by √2 under O(1)c_G(1 + B₀)ϱ̄ ≤ ¼log 2, and with |F(U₁)| from the curvature bullet.
  {#W11.39} So the bridge holds at the complex chain configurations with C_br replaced by O(1)C_br(1 + L(1 + C_ℋ)ϱ̄) and δ_br replaced by δ_br^c := min(δ_Q, δ₁)/32, at most a quarter of the rates ⅛δ₁ and ½δ_Q above.
  {#W11.39-1} The conditions that read δ_br are replayed at δ_br^c: δ_br^cRM₁ ≥ 6 log L for the layer crossings, and δ_br^cM₁ ≥ max(2L^{1/3}, L²/e), the first for the collar estimate L^{3k+1}e^{−δ_br^cM₁L^k} ≤ 1 (sup over u = L^k of Lu³e^{−xu} is L(3/(ex))³) and the second for the jump at ∂Y above.
  {#W11.39-2} Both are lower bounds on RM₁ and M₁.
{#W11.40} So every ℒ-form in §11 differs from the consumer's ℒ_ι-form by terms carrying ϑ_ℒ := C_bre^{16κ₁}sup_x(ε/a_{j(x)})^{min(β₂, 1−β′)}.
{#W11.40-1} With β₂ ≥ ½ and β′ ≤ ½, ϑ_ℒ ≤ C_bre^{16κ₁}L^{(1−k/2)/2} on the young histories.
{#W11.40-2} In powers of L^{−j_min}, j_min ≥ k/2 − 1, its exponent min(β₂, 1 − β′) ≥ ½ is above γ_w, so it enters ϑ below without lowering the exponent in those powers; in powers of ε/a_{m(ω)} per walk it is a global supremum and gives no per-walk exponent.

{#W11.41} *The composition of the averagings.* By CMP 98 (90)–(91), the (j + 1)-fold double bar about U^B is the j-fold double bar about the plain average Ū₀ = MU^B, applied to the one-step double bar about U^B ((B4) of the Cauchy note's §10.1, at the nonlinear level).
{#W11.41-1} By (B3), M̄_{U^B}(U^B) = MU^B = c^A, so run A's objects below (Q^A_j, C^A, H^A, D^A, V^A, and 𝐀₀^A) are taken directly at c^A.
{#W11.41-2} For a run-B field X let εY := Q^B_1(η_BX), the one-step average as a field on T_ε, so that Y = Q₁X + ε^{−1}C^B_1(εX).
{#W11.41-3} Then Q^B_{j+1}(η_BX) = Q^A_j(εY) on Λ^A_j.
{#W11.41-4} The linear parts agree, L^{j+1}η_BQ^B_{j+1} = L^jεQ^A_jQ₁, so the nonlinear parts compose as

  {#W11.42} C^B_{j+1}(L^{j+1}η_BX) = C^A_j(L^jεY) + L^jQ^A_jC^B_1(εX) on Λ^A_j, j ≥ 0, that is, C^B(X) = C^A(Y) + Q̂^Aε^{−1}C^B_1(εX).

{#W11.43} *The inverse of the linearising transformation.* VAR's transformation is A = A′ − HD(A′), with D(A′) the unique fixed point of (50) on the set (51).
{#W11.43-1} Its inverse is explicit: A′ = A + HC(A).
{#W11.43-2} Indeed, for A′ := A + HC(A) the data X := C(A) satisfies C(A′ − HX) = C(A) = X, so it is a fixed point of (50) at A′, and by uniqueness D(A′) = C(A), provided A′ and C(A) lie in the set (51).
{#W11.43-3} This holds when |A|_{(−1)} ≤ ε₃/2 under VAR's condition 18C₂B₀ε₃ ≤ 1: then C(A) = 0 on Λ₀ (C₀ = 0), |C(A)| ≤ C₂|A|²_{(−1)} ≤ C₂ε₃²/4 < ε₃/B₀ by (44), and |A′|_{(−1)} ≤ ε₃/2 + B₀C₂ε₃²/4 < ε₃ by (46).
{#W11.43-4} Nothing here uses Q̂H = 1, so the inverse holds for every operator H with which the contraction (53)–(54) runs, in particular for the decoupled propagators H(s) of RG II (1.5).

{#W11.44} *The two runs' linear coordinates.* Let A^B be a run-B field with |A^B|_{(−1)} ≤ ε₃/2 in run B's norm whose one-step average Y has |Y|_{(−1)} ≤ ε₃/2 in run A's norm.
{#W11.44-1} Let A′^B := A^B + H^BC^B(A^B) be its run-B coordinate and A′_Y := Y + H^AC^A(Y) the run-A coordinate of Y. The composition and the inverse give, on the aligned sets, the exact identities

  {#W11.45} D^B(A′^B) = D^A(A′_Y) + Q̂^Aε^{−1}C^B_1(εA^B),

  {#W11.46} Q₁A′^B − A′_Y = −R₁ + Q₁(H^B − ℒH^A)C^B(A^B), R₁ := (1 − H^AQ̂^A)ε^{−1}C^B_1(εA^B).

{#W11.47} For the second, Q₁A^B − Y = −ε^{−1}C^B_1(εA^B), and Q₁H^B = H^A + Q₁(H^B − ℒH^A) by Q₁ℒ = 1, applied to C^B(A^B) = C^A(Y) + Q̂^Aε^{−1}C^B_1(εA^B).
{#W11.47-1} Both identities hold for arbitrary operators H^A and H^B, hence for the decoupled H^A(s) and H^B(s).
{#W11.47-2} The one-step remainder ε^{−1}C^B_1(εA^B) is bounded by VAR (44) at j = 1 and by the Cauchy note's §9.8, |C^B_1(εA^B)| ≤ C₂ε²|A^B|², and H^AQ̂^A by (46).

{#W11.48} *The size of the remainder terms.* The propagator term Q₁(H^B − ℒH^A)C^B(A^B) is, by the bridge, the form (c) for H applied to the data C^B(A^B) plus the bridge term, so it carries the factor 𝔡_H (*The form (c) for VAR's H.*).
{#W11.48-1} The term R₁ carries the factor of the layer instead.
{#W11.48-2} The one-step remainder acts at the finest spacing ε, while the norm |·|_{(−1)} weighs a point x of the layer j(x) with L^{j(x)}ε.
{#W11.48-3} So by VAR (44) at j = 1,

  {#W11.49} L^{j(x)}ε|ε^{−1}C^B_1(εA^B)(x)| ≤ L^{j(x)}εC₂ε|A^B(x)|² ≤ C₂L^{−j(x)}|A^B|²_{(−1)},

{#W11.50} since |A^B(x)| ≤ |A^B|_{(−1)}(L^{j(x)}ε)^{−1} (L^{j+1}η_B = L^jε).
{#W11.50-1} At a coarse bond whose averaging stencil reaches run B's finer layer, |A^B| is larger by the factor L there (10.1, *The shells.*), so the constant is C₂L² at such bonds.
{#W11.50-2} With (46) for H^AQ̂^A, whose data at the layer j are L^jεQ_j of the field, |R₁|_{(−1)} ≤ (1 + O(1)B₀)C₂L² sup_xL^{−j(x)}|A^B|²_{(−1)}.
{#W11.50-4} In a young history every layer has j ≥ k/2 − 1.
{#W11.50-5} So R₁ is smaller than D, which has no such factor (VAR (55)), by the ratio ε/a_j of the form (c) at β = 1.
{#W11.51} *The fine form of the field.* The consumer of §3(d) compares the fields themselves, 𝐇^B − ℒ𝐇^A, where 𝐇^X := A′^X − H^XD^X(A′^X) and A′^X := H₀^XB′ + 𝐀₀^X (RG II (1.2)–(1.4), at s or at s = 1).
{#W11.51-1} By the inverse, D^X(A′^X) = C^X(𝐇^X).
{#W11.51-2} Let Y be the one-step average of 𝐇^B and c₁ := ε^{−1}C^B_1(ε𝐇^B).
{#W11.51-3} By the composition, C^B(𝐇^B) = C^A(Y) + Q̂^Ac₁, and Y − 𝐇^A = Q₁(𝐇^B − ℒ𝐇^A) + c₁ by Q₁ℒ = 1.
{#W11.51-4} Hence Δ_𝐇 := 𝐇^B − ℒ𝐇^A satisfies

  {#W11.52} Δ_𝐇 = (H₀^B − ℒH₀^A)B′ + Δ₀ − (H^B − ℒH^A)C^B(𝐇^B) − ℒH^A[C^A(𝐇^A + Q₁Δ_𝐇 + c₁) − C^A(𝐇^A)] − ℒH^AQ̂^Ac₁,

{#W11.53} with Δ₀ := 𝐀₀^B − ℒ𝐀₀^A as below.
{#W11.53-1} By VAR (44) and Cauchy's estimate on the disc of (51), C^A has the Lipschitz constant 4C₂ max(|𝐇^A|_{(−1)}, |𝐇^A + Q₁Δ_𝐇 + c₁|_{(−1)}) in |·|_{(−1)} (compare VAR (54)).
{#W11.53-2} With (46) for H^A, (H_ℒ^g), and |Q₁| ≤ O(1), the bracket term is a contraction in Δ_𝐇 with constant ≤ ½ under O(1)C_ℒ^gB₀C₂ε₃ ≤ ¼.
{#W11.53-3} So

  {#W11.54} |Δ_𝐇|_{(−1)} ≤ 2|(H₀^B − ℒH₀^A)B′|_{(−1)} + 2|Δ₀|_{(−1)} + 2|(H^B − ℒH^A)C^B(𝐇^B)|_{(−1)} + O(1)C_ℒ^gB₀(1 + C₂ε₃)‖c₁‖,

{#W11.55} with ‖c₁‖ := max(|c₁|_{(−1)}, |∇c₁|_{(−2)}), since (H_ℒ^g) reads both entries, and the same with |∇·|_{(−2)}.
{#W11.55-1} The first and third terms are the form (c) and the bridge, and the second is the 𝐀₀ contraction below.
{#W11.55-2} The last is the one-step remainder of 𝐇^B.
{#W11.55-3} By the bound above, |c₁|_{(−1)} ≤ C₂L² sup_xL^{−j(x)}|𝐇^B|²_{(−1)}. |∇c₁|_{(−2)} has the same bound with |𝐇^B|_{(−1)}|∇𝐇^B|_{(−2)} by Cauchy's estimate on the disc of (44), plus the variation of C^B_1 with the background between neighbouring blocks, which is at most O(1)c_uMα₀L^{−j}C₂L²|𝐇^B|²_{(−1)} and keeps the factor L^{−j}.
{#W11.55-4} So it carries the factor ε/a_j of the layer, and the D part of (Wδ-3) is bounded by the forms (c) for H₀ and H, the 𝐀₀ difference, and this remainder.
{#W11.55-5} The same bound applies to the run difference Q̂^Ac₁ of D at corresponding arguments.

{#W11.56} *The functional V.* RG II (1.4) is VAR's equation (180) of Sect. G (RG II p.2 cites Sect. G before (1.2) and (80) after (1.4)), and (180) is obtained from (143) (VAR p.306), which comes from (127).
{#W11.56-1} For (127) VAR applies the linearising transformation on the larger space (126), where RD*A′ = f is free, and gets "the functional (74), with the operator Δ instead of Δ_π" (VAR p.297, the paragraph before (126)).
{#W11.56-2} So the V of (127), (143), (180), and RG II (1.4) is (80) with Δ in place of Δ_π.
{#W11.56-3} Let 𝔉 denote (74) with Δ, on the set (77), without the gauge condition (76).
{#W11.56-4} By (26), which holds for every A without a gauge condition, 𝔉(A′) is exactly the action at e^{iηA}U₀, A = A′ − HD(A′).
{#W11.56-5} Since D = C^{(2)} + D₃ by (78), the difference of 𝔉 and V is, identically in A′,

  {#W11.57} 𝔉(A′) − V(A′) = A(U₀) + ⟨A′, J⟩ + ½⟨A′, ΔA′⟩ − ⟨HC^{(2)}(A′), J⟩,

{#W11.58} a polynomial of degree two.
{#W11.58-1} V vanishes to second order at A′ = 0, since each term of (80) is of order ≥ 3 (D is of order ≥ 2, and V₀ is of order ≥ 3 by (26)).
{#W11.58-2} Let T₃ denote the Taylor remainder of order three at A′ = 0, that is, a function minus its Taylor polynomial of degree two.
{#W11.58-3} Then V = T₃𝔉 on the whole set (77), and no gauge condition enters.
{#W11.59} Let A′ be in the set (77) of run A, A^B := ℒA′ − H^BD^B(ℒA′) the run-B field of the coordinate ℒA′, Y its one-step average with |Y|_{(−1)} ≤ ε₃/2, and E := A′_Y − A′.
{#W11.59-1} By the second identity above and Q₁ℒ = 1, E = R₁ − Q₁(H^B − ℒH^A)C^B(A^B), of order ≥ 2.
{#W11.59-2} The run-B action is A_{ε/L} = A_ε∘M̄ − b, with b the blocking artifact of the Cauchy note's *The Action Part of β.* (its #C10.4.18).
{#W11.59-3} A_ε(M̄(e^{iη_BA^B}U^B)) = A_ε(e^{iεY}c^A) is run A's action at the coordinate A′_Y, since Y = A′_Y − H^AD^A(A′_Y) by the inverse above.
{#W11.59-4} Hence

  {#W11.60} 𝔉^B(ℒA′) = 𝔉^A(A′_Y) − b(e^{iη_BA^B}U^B), 𝔉^A(A′) = A_ε(e^{iε(A′ − H^AD^A(A′))}c^A).

{#W11.61} T₃ commutes with the linear ℒ and removes polynomials of degree two.
{#W11.61-1} Write P^A := 𝔉^A − V^A, the polynomial above.
{#W11.61-2} Then

  {#W11.62} V^B(ℒA′) − V^A(A′) = T₃[P^A(A′ + E) − P^A(A′)] + [V^A(A′ + E) − V^A(A′)] − T₃[b(e^{iη_BA^B}U^B)],

{#W11.63} identically on the open set of run A's (77) where ℒA′ lies in run B's (77) and |Y|_{(−1)} ≤ ε₃/2, which contains the ball max(|A′|_{(−1)}, |∇A′|_{(−2)}) < ε₃/(2C_ℒ^g) under O(1)B₀C₂ε₃ ≤ 1.
{#W11.63-1} The points A′^A of size O(B₅ε₁) lie in it under O(1)C_ℒ^gB₅ε₁ ≤ ε₃/2, so the gradient of the identity at A′^A is σ in every direction, as RG II (1.4) and VAR (127) need.
{#W11.63-2} Here T₃[P^A(A′ + E) − P^A(A′)] = T₃⟨E, J^A⟩ + ⟨A′, Δ^AE⟩ + ½⟨E, Δ^AE⟩ − ⟨H^A(2C^{(2)A}(A′, E) + C^{(2)A}(E)), J^A⟩, with C^{(2)}(·, ·) the polarisation.
{#W11.63-3} Every term of it, and V^A(A′ + E) − V^A(A′), contains E. The two runs' currents J^X and quadratic forms Δ^X therefore never meet: their degree-two parts cancel exactly.
{#W11.64} *The fixed point 𝐀₀.* Let A′^X := H₀^XB′ + 𝐀₀^X in each run, at the shared data B′, and let σ := ℒ*(δV^B/δA′)(ℒA′^A) − (δV^A/δA′)(A′^A), the gradient of V^B∘ℒ − V^A at A′^A.
{#W11.64-1} By RG II (1.4) in both runs, Δ₀ := 𝐀₀^B − ℒ𝐀₀^A satisfies

  {#W11.65} Δ₀ = −G̃^B[(δV^B/δA′)(A′^B) − (δV^B/δA′)(ℒA′^A)] − (G̃^B − ℒG̃^Aℒ*)(δV^B/δA′)(ℒA′^A) − ℒG̃^Aσ,

{#W11.66} with A′^B − ℒA′^A = (H₀^B − ℒH₀^A)B′ + Δ₀.
{#W11.66-1} The first term is Lipschitz on the segment between A′^B and ℒA′^A.
{#W11.66-2} VAR (187) bounds G̃δ²V at the single point 𝒜₀ + H₀B, of size O(B₅ε₁), through (186), whose r is the ratio of max(|A′|_{(−1)}, |∇A′|_{(−2)}) to the size of the domain of Proposition 4 (p.308 l.7–13); by (185) and (98) the constant scales with the size of the point, as (187)'s B₅ε₁ shows.
{#W11.66-3} By (H_ℒ^g), the points of the segment have size ≤ C_ℒ^gB₅ε₁, so the constant is κ_V := O(1)B₀C₄B₅C_ℒ^gε₁, and the circles of Cauchy's estimate in (186) stay in the domain of VAR Proposition 4 under O(1)C_ℒ^gB₅ε₁ ≤ ε₃.
{#W11.66-4} The condition κ_V ≤ ½ makes ε₁ small depending on C_ℒ^g, a constant of L, d, G, and Mα₀ ((H_ℒ^g)).
{#W11.66-5} So

  {#W11.67} |Δ₀| ≤ 2κ_V|(H₀^B − ℒH₀^A)B′| + 2|(G̃^B − ℒG̃^Aℒ*)(δV^B/δA′)(ℒA′^A)| + 2|ℒG̃^Aσ|

{#W11.68} in the max norm max(|·|_{(−1)}, |∇·|_{(−2)}) of run B, in which the contraction holds (VAR (186) reads both entries through r).
{#W11.68-1} By the bridge, the first term is the form (c) for H₀ plus bridge terms and carries δ_w + ϑ_ℒ (H₀ of VAR (129) is built from G_a = Δ_a^{−1}).
{#W11.68-2} The second is the form (c) for the G̃ of VAR (180) and carries 𝔡_H (*The form (c) for G̃ with the Δ^{(2)} term.*).
{#W11.68-3} The decoupled propagators of RG II (1.5) enter only through these bounds, which hold at complex s by *Complex s.* below.
{#W11.68-4} RG II's bound for H(s), G̃(s), and H₀(s) carries the factor e^{16κ₁}, so κ_V carries it too, and the condition κ_V ≤ ½ depends on κ₁.

{#W11.69} *The current term of VAR (143).* VAR's Sects. A–E take a background U₀ more general than a minimiser, under VAR's condition (14), U₀ ∈ 𝔘_k({Ω_j}, C₁B₃ε₁) and |Ū₀^j − V| < C₁ε₁ (VAR p.280 l.15–20).
{#W11.69-2} For it 𝐀₀ solves VAR (143) (p.300 l.14–17), A₀ = −G̃J + G̃Δ^{(2)}(A₀ + H₀B) − G̃(δV/δA′)(A₀ + H₀B), with J the current of U₀ and G̃ built from G_a = Δ_a^{−1}.
{#W11.69-3} RG II (1.4) is the case of a critical background, where VAR (178) holds.
{#W11.69-4} The problems of LFR II (1.54) and (1.57) are of the general kind (§12), so the comparison above is extended to (143).
- {#W11.70} The scope condition.
  {#W11.70-1} The backgrounds of (1.54) and (1.57) satisfy the first condition of (14).
  {#W11.70-2} Away from ∂Ω″^∼_{h+1} they are minimisers.
  {#W11.70-3} Near it, U_{1,2} "satisfies the regularity conditions typical for an h-order configuration" on (Ω″_{h+1})^c ∩ Ω″^{∼2}_{h+1} (LFR II p.370 l.35–38), and regularity at the scale h implies it at the finer scales.
  {#W11.70-4} The second condition is on the data.
  {#W11.70-5} For (1.57), the data on Z″_k are 1, against the averages M^·(U_{k,Λ}) of the background, and |M^j(U_{k,Λ}) − 1| < O(1)B₃B₅M⁶ε_k inside Λ by LFR I (1.84).
  {#W11.70-6} Bałaban states this for U_{k,Λ} and uses it to write (1.57) (LFR II p.371 l.32–33).
  {#W11.70-7} For (1.54), the background U_{1,2} has the data 1 on Z″_k ∩ Ω″^∼_{h+1} ((1.53)), and the argument of U^0_k there is M^·(U_0^{(AL)}) = exp iQ̃_·(η𝐀₀) (LFR II p.370 l.15–16), the averages of U_0 in the axial–Landau gauge.
  {#W11.70-8} LFR I (1.87) (p.197) gives |𝐀₀|, |∇𝐀₀|, |∂*∂𝐀₀| < O(1)B₃²B₅M⁶ε_k on Z″_k, so |M^j(U_0^{(AL)}) − 1| ≤ O(1)B₃²B₅M⁶ε_k there; (1.84) is for the axial gauge in k-blocks and does not apply to these data.
  {#W11.70-9} Bałaban obtains (1.54) "from the results of Sects. D, E [15]" (p.370 l.38–39).
  {#W11.70-11} So the data condition holds for both problems, with a bound independent of the size of Λ.
  {#W11.70-12} Off the collar, the data of the problem are the background's own.
  - {#W11.71} What else is taken from p.370 l.35–38.
    {#W11.71-1} VAR's Sects. A–E also use PBG's (3.35)–(3.36) at U_0.
    {#W11.71-3} (3.35) is "The additional regularity condition (3.35) in (1.33)" of VAR p.280 l.51–52, where (1.33) is REG (1.33) (REG p.082 l.33), and the "Sect. F" there is REG's, *Removal of the Additional Regularity Assumption*, which proves (3.35) from U_0 ∈ 𝔘_k({Ω_j}, α₀) alone, with no criticality (REG p.097 l.29–30 and p.099 l.34–37).
    {#W11.71-5} (3.36) follows from the same membership by REG's Proposition 6, which bounds (L^jη)³|∂^{η*}∂^ηA| and (L^jη)³|Δ^ηA| by 7dL²B₁Mα₀ on □_j in the gauge of Sect. F (REG (1.135)–(1.136), p.099 l.41–48, with REG's cube parameter M = R₁M₁), and VAR p.309 l.12 accepts REG's (1.7)–(1.9) in place of PBG's (3.35)–(3.38).
    {#W11.71-6} So both follow from 𝔘-membership.
    {#W11.71-7} §11 uses the curvature bounds (9.2) of the Cauchy note (|F| ≤ O(1)C₀ε₁a_j^{−2}, |∇F| ≤ O(1)C₀ε₁a_j^{−3}) in the oscillation of ∇b₁.
    {#W11.71-8} Near the cut, the 𝔘-membership is Bałaban's statement that U_{1,2} "is regular, and satisfies the regularity conditions typical for an h-order configuration" there. "Regularity conditions" and "regular" are REG's terms: REG's conditions (1.7)–(1.9) define its "spaces of regular field configurations" 𝔘_k (REG p.077 l.31).
    {#W11.71-9} What is used of the statement is 𝔘-membership at the index h on the band, and this membership is derived at the parameter L³B₃ε_U^{(i)}, which tends to 0 with γ: U_{1,2} = 1 on the finest strips at the cut, and Sect. F's step at the block size M′ of the joins, with (163) taken as B₃e^{−½δ₀M′} ≤ ½L^{−3}, carries the decay across the refinement layers (§12, *The band regularity of U_{1,2}.*).
    {#W11.71-10} (3.35)–(3.36) follow as above. 10.5's further inputs at U_{1,2} come from the minimiser base V₀ = (U_k^0)^{u_k^0} of (1.54), and the oscillation of the artifact at ι_Y(U_{1,2}) is bounded through that base with (ε/a_j)^{β_o}, β_o := min(β, 1 − 2ε₀), in place of ε/a_j (same place).
  - {#W11.72} The run-B background.
    {#W11.72-1} The comparison runs at the aligned pairs (ι(V₀), V₀) of §12, so run B's background is ι(U^A_{1,2}) or ι(U^A_{k,Λ}), not a background printed by Bałaban.
    {#W11.72-2} (14) for it, the 𝔘-bounds and the data condition, comes from 10.5 and the first bullet of the bridge, whose input is again V₀'s layer bounds (VAR (9)–(10), applied as above near the cut).
- {#W11.73} The form with the J term.
  {#W11.73-1} For an invertible symmetric K with QK^{−1}Q* invertible, G̃_Kf is the unique u with Qu = 0 and Ku − f ∈ Ran Q*.
  {#W11.73-2} (143) gives QA₀ = 0 and Δ_aA₀ − Δ^{(2)}A₀ − f ∈ Ran Q*, with f := −J + Δ^{(2)}H₀B − (δV/δA′)(A₀ + H₀B).
  {#W11.73-3} So A₀ = G̃f exactly, with G = (Δ_a − Δ^{(2)})^{−1} in G̃, that is, A₀ = −G̃J + G̃Δ^{(2)}H₀B − G̃(δV/δA′)(A₀ + H₀B), the form of (180) with the J term.
  {#W11.73-4} QGQ* is invertible for this G by VAR p.306 l.37–38.
- {#W11.74} The contraction. −G̃J does not depend on A₀, so the contraction runs as above.
  {#W11.74-1} Under (14), |J| ≤ C₁B₃ε₁(L^jη)^{−3}, so the point is shifted by G̃J, of size O(1)B₀C₁B₃ε₁ in max(|·|_{(−1)}, |∇·|_{(−2)}) by PBG (3.42).
  {#W11.74-2} Then κ_V = O(1)B₀C₄C_ℒ^g(B₅ + B₀C₁B₃)ε₁, under a smallness condition of the same kind (ε₁ small depending on C_ℒ^g).
- {#W11.75} The run difference.
  {#W11.75-1} Δ₀ gains −(G̃^B − ℒG̃^Aℒ*)J^B − ℒG̃^A(ℒ*J^B − J^A), with J^X the current of run X's background.
  - {#W11.76} The first is the form (c) for G̃ (*The form (c) for G̃ with the Δ^{(2)} term.*), paired with |J^B| ≤ C₁B₃ε₁a_j^{−3} at the global layer.
    {#W11.76-1} It carries 𝔡_H.
  - {#W11.77} The second is ℒG̃^A∇b₁, by ℒ*J^B − J^A = −∇b₁ (*The term G̃Δ^{(2)}H₀B.*, second bullet), the first-order part of 𝔉^B(ℒA′) = 𝔉^A(A′ + E) − b, which uses no criticality.
    {#W11.77-1} As there, it is bounded in divergence form after the conversion to run A. This gives O(1)(ε/a_j)C₀ε₁ relative to the comparator in |·|_{(−1)}, and (ε/a_j)^{1−β′} in place of ε/a_j in |∇·|_{(−2)}.
- {#W11.78} σ.
  {#W11.78-1} The identity of *The functional V.* holds without criticality and already carries the currents J^A and J^B (the terms T₃⟨E, J^A⟩ and ⟨H^AC^{(2)A}, J^A⟩).
  {#W11.78-2} So σ and its bounds (a) and (b) are unchanged; (a) uses the (14) bound of J^A.
- {#W11.79} The complex step. 10.5 reads VAR's Sect. G through the representation (173)–(175) of 𝒜₁ at a minimiser U₀ = U_k(V₀) (#W10.5.35-2), which is critical.
  {#W11.79-1} For the B-derivatives of 𝒜₀ at a non-critical background, (182)–(184) and (188) (p.307 l.17–36, p.308 l.24–26) keep their form at the shifted point, since J does not depend on B.

{#W11.80} *The term G̃Δ^{(2)}H₀B.* RG II (1.4) (p.2 l.37–40) prints no Δ^{(2)} term, while VAR (180) (p.306 l.31–40), from which RG II takes it ("by the results of Sect. G"), carries −G̃Δ^{(2)}H₀B, with G = (Δ_a − Δ^{(2)})^{−1} in G̃.
{#W11.80-1} The term is bounded here, so the estimate holds with it.
{#W11.80-2} Its run difference is
  {#W11.81} (G̃^B − ℒG̃^Aℒ*)Δ^{(2)B}H₀^BB′ + ℒG̃^A[ℒ*Δ^{(2)B}(H₀^B − ℒH₀^A)B′ + (ℒ*Δ^{(2)B}ℒ − Δ^{(2)A})H₀^AB′].
  {#W11.82} On run-B sources, ℒ* is bounded by |ℒ*s|_{(−3)} ≤ O(1)C_ℒ^g|s|_{(−3)} of run A: ℒ = I + Q₁*(Q₁Q₁*)^{−1}(1 − Q₁I) has a kernel with the exponential decay of (Q₁Q₁*)^{−1} and O(1) sums in the volume normalisations of the two lattices (*The global lift.*), and its transpose has the same.
  {#W11.82-1} Then G̃^Aℒ* is bounded by PBG (3.42) for the entries G and ∇G on run A's sources, times O(1)C_ℒ^g.
{#W11.83} The first two parts are the forms (c) with the bridge, times |Δ^{(2)}| ≤ O(1)C₃Mα₀(L^jη)^{−2} relative to Δ (PBG (3.137), with C₃ from the bilinear bound before it).
{#W11.83-1} The last is a bilinear defect of Δ^{(2)}, defined by ⟨A, Δ^{(2)}A⟩ = 2⟨HC^{(2)}(A), J⟩ (PBG (3.134)), and it satisfies an exact identity.
{#W11.83-2} The second-order part of the composition gives C^{(2)B}(ℒA) = C^{(2)A}(A) + Q̂^Aε^{−1}C^{(2)B}_1(εℒA), by Q₁ℒ = 1.
{#W11.83-3} So
  {#W11.84} ½⟨ℒA, Δ^{(2)B}ℒA⟩ − ½⟨A, Δ^{(2)A}A⟩ = ⟨(H^B − ℒH^A)C^{(2)A}(A), J^B⟩ + ⟨H^AC^{(2)A}(A), ℒ*J^B − J^A⟩ + ⟨H^BQ̂^Aε^{−1}C^{(2)B}_1(εℒA), J^B⟩.
- {#W11.85} The first term is the form (c) for H with the bridge, paired with |J^B| ≤ O(1)Mα₀(L^{j+1}η_B)^{−3} = O(1)Mα₀a_j^{−3} (run A's layer j is run B's layer j + 1; at a (143) background, |J^B| ≤ C₁B₃ε₁a_j^{−3} by VAR (28) instead).
  {#W11.85-1} By *The form (c) for VAR's H.*, it carries 𝔡_H.
- {#W11.86} The second reads the run difference of the currents.
  {#W11.86-1} The first-order part of 𝔉^B(ℒA′) = 𝔉^A(A′ + E) − b, with E of order ≥ 2, gives ℒ*J^B − J^A = −∇b₁, the first variation of the blocking artifact at the background.
  {#W11.86-2} By the identity of *The artifact through covariances.*, its variance part is dVar_p[v] = 2Cov_p(X, X′_v).
  {#W11.86-3} This is a linear functional of the fine curl of v, with coefficients bounded by osc_pX (*The artifact through covariances.* in (b) below; the Cauchy note's #C10.4.45 and #C10.4.54 give |Cov_p| ≤ osc·osc), and osc_pX ≤ 4dε|∇F| + 4δ_T|F| with δ_T ≤ 32d²ν_F (the Cauchy note's #C10.4.49-2 and #C10.4.50).
  {#W11.86-4} The ρ-terms of that identity are of the same form.
  {#W11.86-5} The κ-terms have first variations of the relative order (ε/a_j)⁴ and are bounded in the same way.
  {#W11.86-6} The curvature bounds are |F| ≤ O(1)C₀ε₁a_j^{−2} and |∇F| ≤ O(1)C₀ε₁a_j^{−3} (the Cauchy note's (9.2), its #C10.4.46-3) at the (k + 1)-step minimiser U^B with the data of the pair.
  {#W11.86-7} The background here is the lift W = ι(U^A), which is not that minimiser.
  {#W11.86-8} By the Cauchy note's §9.7, W = e^{i(ε/L)(ℒA′* + A″)}U^B with sup and gradient bounds ‖ℒA′* + A″‖ ≤ C(ε₀)(ε/a_j)^{1−2ε₀}ε₁ in the units of the layer (§9.7's argument at the layer j, with a_j for a).
  {#W11.86-9} So |F(W) − F(U^B)| ≤ O(1)C(ε₀)(ε/a_j)^{1−2ε₀}ε₁a_j^{−2}, and osc_pX at W exceeds its value at U^B by at most twice that.
  {#W11.86-10} The gain of K below is therefore (ε/a_j)^{1−2ε₀} instead of ε/a_j, which fits δ_w(ω) of §8, since γ_w ≤ (1 − ε₀)/3 ≤ 1 − 2ε₀ for ε₀ ≤ 2/5.
  {#W11.86-11} As a pointwise source, ∇b₁ has no small factor, since the transposed curl costs η_B^{−1}.
  {#W11.86-12} It is used in divergence form, ∇b₁ = ∇_A*K + s with |K| ≤ O(1)(ε/a_j)^{1−2ε₀}C(ε₀)C₀ε₁a_j^{−2}, after the conversion of *The conversion to run A.* in (b) below.
  {#W11.86-13} Paired with a field, or with G̃ applied through its entry G∇*, it carries O(1)C(ε₀)(ε/a_j)^{1−2ε₀} times the comparator C₀ε₁a_j^{−3}.
  {#W11.86-14} In the gradient entry ∇G∇* of (3.44), with the crude lattice Hölder bound, it carries (ε/a_j)^{1−2ε₀−β′}, which fits δ_w for β′ ≤ 1 − 2ε₀ − γ_w.
- {#W11.87} The third has the one-step remainder at second order, C₂L²L^{−j} as for R₁, times |H^{B*}J^B|.
{#W11.88} So the defect form carries 𝔡_H, which dominates ϑ + C_bϑ_b with ϑ of (a) below and ϑ_b of *The artifact through covariances.*, times O(1)(C₃Mα₀ + C₀ε₁) relative to Δ; the ∇b₁ part carries C₀ε₁ in place of C₃Mα₀, and ε/a_j ≤ ϑ_b.
{#W11.88-1} Its polarisation at A = H₀^AB′ is applied to the directions through the derivatives of C^{(2)}, pointwise as in VAR (85)–(86), and ℒG̃^A of it is bounded by PBG (3.42) and (H_ℒ^g).
{#W11.88-2} The defect enters with the factor Mα₀, which is small, and with ϑ.

{#W11.89} *The form (c) for G̃ with the Δ^{(2)} term.* VAR (180) takes G = (Δ_a − Δ^{(2)})^{−1} in G̃, while the forms (c) of (Wδ-1)–(Wδ-2) are derived for G_a := Δ_a^{−1}.
{#W11.89-1} By (3.137) and the bilinear bound before it, Δ^{(2)} is bounded by O(1)C₃Mα₀ relative to Δ_a, with M PBG's block size and C₃ containing the factor c_u = O(1)L³ by which §7 reads PBG's O(1)Mα₀ bounds through (3.35) (O(1)L⁵ at the index j + 1 of PBG's own sequences; §7, *The cubes next to the finer layer.*); the constant c_π of Δ′_π below contains the same factor.
{#W11.89-2} So G = Σ_{m≥0}G_a(Δ^{(2)}G_a)^m converges under O(1)B₀C₃Mα₀ ≤ ½, an upper bound on α₀ after L and M, as PBG's series (3.130) does.
{#W11.89-3} It converges in the norms of (3.42)–(3.44) except the Laplace entry of (3.42), which is not used (as for (3.130), p.422 l.12–15).
{#W11.89-4} Δ^{(2)} is of order zero, so no derivative crosses it: the derivative and Hölder entries fall on the outer factors.
{#W11.89-5} In each run, the term m is X_m := G_a(Δ^{(2)}G_a)^m.
{#W11.89-6} Let W_i := (G_a^BΔ^{(2)B})^iℒ(G_a^AΔ^{(2)A})^{m−i}G_a^Aℒ*, so W_0 = ℒX_m^Aℒ*.
{#W11.89-7} Then X_m^B − W_m = (G_a^BΔ^{(2)B})^m(G_a^B − ℒG_a^Aℒ*), and for i = 1, …, m,
  {#W11.90} W_i − W_{i−1} = (G_a^BΔ^{(2)B})^{i−1}[(G_a^B − ℒG_a^Aℒ*)Δ^{(2)B}ℒ + ℒG_a^A(ℒ*Δ^{(2)B}ℒ − Δ^{(2)A})](G_a^AΔ^{(2)A})^{m−i}G_a^Aℒ*.
  {#W11.91} So X_m^B − ℒX_m^Aℒ* is a sum of m + 1 terms with one factor G_a^B − ℒG_a^Aℒ* and m terms with one polarised defect ℒ*Δ^{(2)B}ℒ − Δ^{(2)A}.
  {#W11.91-1} The first kind are the forms (c) for G_a with the bridge, which carry δ_w + ϑ_ℒ.
  {#W11.91-2} The second kind are the polarised defect of Δ^{(2)} of the paragraph above, which carries 𝔡_H times O(1)C₃Mα₀.
  {#W11.91-3} Every other factor is bounded by B₀ (G_a, by (3.42)), by O(1)C₃Mα₀B₀ (Δ^{(2)}G_a), or by C_ℒ^g (ℒ and ℒ*, by (H_ℒ^g) and the source bound of the bridge).
  {#W11.91-4} The m + 1 + m terms of the term m therefore sum to at most (2m + 1)(O(1)B₀C₃Mα₀)^m times B₀(C_ℒ^g)² times 𝔡_H, and the sum over m converges under the same condition.
  {#W11.91-5} Then G̃ = G − GQ*(QGQ*)^{−1}QG.
  {#W11.91-6} Q* needs no comparison: L^{j+1}η_BQ^B_{j+1} = L^jεQ^A_jQ₁ (*The composition of the averagings.*) and Q₁ℒ = 1 give Q^Bℒ = Q^A, so Q^{A*} = ℒ*Q^{B*}.
  {#W11.91-7} With F(X) := X − XQ^{B*}(Q^BXQ^{B*})^{−1}Q^BX, G̃^B = F(G^B) and ℒG̃^Aℒ* = F(P) with P := ℒG^Aℒ*, since Q^BPQ^{B*} = Q^AG^AQ^{A*}.
  {#W11.91-8} So each term of G̃^B − ℒG̃^Aℒ* = F(G^B) − F(P) contains one factor G^B − P, directly or through (Q^BG^BQ^{B*})^{−1} − (Q^AG^AQ^{A*})^{−1} = −(Q^BG^BQ^{B*})^{−1}Q^B(G^B − P)Q^{B*}(Q^AG^AQ^{A*})^{−1}.
  {#W11.91-9} The other factors are bounded by (3.132) for the new G (VAR p.306 l.37–38).
  {#W11.91-10} So G̃^B − ℒG̃^Aℒ* carries 𝔡_H, and the uses of G̃ in *The fixed point 𝐀₀.* and *The term G̃Δ^{(2)}H₀B.* hold with it.

{#W11.92} *The form (c) for VAR's H.* VAR's H, the H of the linearising transformation, of (179), and of PBG (3.134), is the minimiser of ½⟨A, ΔA⟩ under QA = B and RD*A = 0 (VAR (45)–(46), PBG (3.109)–(3.110)).
{#W11.92-1} So HB = G_πQ*(QG_πQ*)^{−1}B with G_π^{−1} = Δ_π + DRD* + Q*aQ (PBG (3.122), (3.126)), and G_π = Σ_nG_a(Δ′_πG_a)^n (PBG (3.130)), with Δ′_π of (3.120).
{#W11.92-2} The series is not the Δ^{(2)} series above.
{#W11.92-3} The same telescoping applies with Δ′_π in place of Δ^{(2)}, with (3.131) in place of (3.137).
{#W11.92-4} (3.131) puts D* on one argument, so the factors Δ′_πG_a are bounded through the entry ∇G of (3.42), as in PBG's convergence proof.
{#W11.92-5} What it needs is the polarised run defect of Δ′_π.
- {#W11.93} The identity.
  {#W11.93-1} By (3.120), ⟨A, Δ′_πA⟩ = ⟨K(A), J⟩ with K(A)(b) := i[ω(b_−), A(b)] − i[A(b), R_bω(b_+)] − i[ω(b_−), (Dω)(b)] and ω := G′RD*A, R_b the parallel transport along b.
  {#W11.93-2} Since ⟨ℒK^A(A), J^B⟩ = ⟨K^A(A), ℒ*J^B⟩,
  {#W11.94} ⟨ℒA, Δ′^B_πℒA⟩ − ⟨A, Δ′^A_πA⟩ = ⟨K^B(ℒA) − ℒK^A(A), J^B⟩ + ⟨K^A(A), ℒ*J^B − J^A⟩.
- {#W11.95} The second term is the current difference −∇b₁ of *The term G̃Δ^{(2)}H₀B.*, paired in divergence form.
  {#W11.95-1} The pairing ⟨K^A(A), ∇_A*K_b⟩ = ⟨∇_AK^A(A), K_b⟩ contains ∇D_Aω^A, the second differences of G′RD*A, which are bounded through the crude lattice Hölder bound of (a) at the exponent β′, so this term carries (ε/a_j)^{1−β′}C₀ε₁, which is ≤ 𝔰^{β/(1+β)} for β′ ≤ 1/2.
- {#W11.96} The first term.
  {#W11.96-1} Write ω^B := G′^BR^BD_B*ℒA and ω^A := G′^AR^AD_A*A.
  {#W11.96-3} The intermediate is I′, the transported multilinear interpolation of scalars, I′f(x) := Σ_yλ_y(x)R(U^B(Γ_{y,x}))^{−1}f(y), with λ_y the multilinear weights of the corners y of the run-A cell of x, and Γ_{y,x} the coordinate-ordered axial path of T_{ε/L} from y to x, which depends only on (y, x), so I′ is well defined on shared cell faces and gauge covariant.
  {#W11.96-4} Then K^B(ℒA) − ℒK^A(A) = [K^B(ℒA; ω^B) − K^B(ℒA; I′ω^A)] + [K^B(ℒA; I′ω^A) − ℒK^A(A; ω^A)].
  - {#W11.97} The first bracket is bilinear, with one factor e := ω^B − I′ω^A and one factor D_Be.
    {#W11.97-1} Its sup: e = (ω^B − ℒ′ω^A) + (ℒ′ − I′)ω^A.
    {#W11.97-2} The first part is the form (c) for G′RD*, assembled from the coarse side of G′_□ (§4(d), *The coarse side of G′_□.*) with the walk telescoping of §7 for G′, the resolvent identity for (Q′G′²Q′*)^{−1} in R = 1 − P (as for (QGQ*)^{−1} above), and the coarse-side intertwining of D* (§5).
    {#W11.97-3} It carries δ_w + ϑ_ℒ + O(1)(ε/a_j) in the sup entry.
    {#W11.97-4} The source D_B*ℒA is not a lift ℒ′f, so the reduction to the coarse-side entry of 10.1–10.2 is as follows: D_B*ℒA = ℒ′D_A*A + (D_B*ℒ − ℒ′D_A*)A.
    {#W11.97-5} The first part is a lifted source, for which 10.1–10.2 give the sup entry δ_w + ϑ_ℒ.
    {#W11.97-6} The second, f := (D_B*ℒ − ℒ′D_A*)A, is the fine fluctuation of D_B*ℒA, pointwise of order L|A|/a_j.
    {#W11.97-7} Split it on each run-A cell into its cell mean and the rest.
    {#W11.97-8} The rest has zero mean on the cell, so it is ∇_B*g with g supported in the cell and |g| ≤ O(1)ε sup_cell|f| ≤ O(1)L(ε/a_j)|A|; through R^B, which is bounded with decay, and the single-run entry G′∇* of (3.42) in run B, it contributes at most O(1)LB₀(ε/a_j)a_j sup|A|.
    {#W11.97-9} The cell mean of D_B*ℒA is the flux of ℒA through the cell's faces, and that of ℒ′D_A*A is the coarse divergence of the tube averages Q₁ℒA = A; for the C^{1,β} field ℒA (the entries of (3.42)–(3.44) and the regularity of the lift) the face fluxes and the tube averages agree up to O(1)L^β(ε/a_j)^β|A|/a_j, the L^β from the jumps of the interpolation's gradient across the cell faces.
    {#W11.97-10} With the background U^B the cell mean is taken after parallel transport to a common point of the cell, and the holonomy correction is O(ε²|F|)|A|/a_j ≤ O(1)C₀ε₁(ε/a_j)²|A|/a_j.
    {#W11.97-11} Through G′ of (3.42) this mean contributes at most O(1)L^βB₀(ε/a_j)^βa_j sup|A|.
    {#W11.97-12} The second part is ≤ O(1)ε|∇ω^A| ≤ O(1)(ε/a_j)B₀a_j sup|A|, since ℒ′ and I′ agree at the corners.
    {#W11.97-13} So sup|e| ≤ 𝔰B₀a_j sup|A|, 𝔰 := δ_w + ϑ_ℒ + O(1)L^{1+β}(ε/a_j)^β.
    {#W11.97-14} Since γ_w ≤ β, the term (ε/a_j)^β does not lower the exponent γ_w of the sum, and 𝔰 ≥ ε/a_j still holds.
    {#W11.97-15} Its gradient: the entries of (3.42)–(3.44) give ‖ω^B‖_{1,β} and ‖ω^A‖_{1,β} ≤ O(1)B₀ in the units of the layer j, and the multilinear interpolation keeps this up to L^β, since its gradient jumps across the run-A cell faces by the Hölder oscillation of ∇ω^A over one cell.
    {#W11.97-16} The lattice interpolation inequality |∇f| ≤ O(1)(sup|f|/ℓ + ℓ^β[∇f]_β), at ℓ := a_j𝔰^{1/(1+β)} ≥ ε/L (since 𝔰 ≥ ε/a_j), gives |∇e| ≤ O(1)L^βB₀𝔰^{β/(1+β)} sup|A| in the scaling of max(|A|_{(−1)}, |∇A|_{(−2)}).
    {#W11.97-17} So the first bracket carries 𝔰^{β/(1+β)}.
  - {#W11.98} The second bracket compares a local bilinear expression of the smooth fields ℒA, I′ω^A, and D_BI′ω^A with the lift of the expression. ℒ = I + Q₁*(Q₁Q₁*)^{−1}(1 − Q₁I) is the interpolation plus a correction with the exponential tail of (Q₁Q₁*)^{−1} at the rate δ_Q (*The global lift.*).
    {#W11.98-1} On a field with a bounded Hölder norm, (1 − Q₁I) is of relative size O(1)(ε/a_j)^β, since the averages of the interpolation reproduce the coarse values up to the Hölder oscillation over a block.
    {#W11.98-2} The same holds for D_BI′f − I D_Af and for the product rule I(fg) − (If)(Ig).
    {#W11.98-3} So the difference is ≤ O(1)(1 + B₀)²(ε/a_j)^β relative to the size of K, plus the background term c_uMα₀L^{−j} of the global lift's second bullet.
- {#W11.99} So ½⟨ℒA, Δ′^B_πℒA⟩ − ½⟨A, Δ′^A_πA⟩ carries 𝔰^{β/(1+β)} + ϑ_b, the term (ε/a_j)^β of the second bracket being ≤ 𝔰^{β/(1+β)} since 𝔰 ≥ ε/a_j, times O(1)L^β(1 + B₀)²(Mα₀ + C₀ε₁) relative to Δ.
  {#W11.99-1} Here |J^B| ≤ O(1)Mα₀a_j^{−3} by PBG (3.36), and the ∇b₁ part carries C₀ε₁.
- {#W11.100} The localised bilinear form.
  {#W11.100-1} The callers, the telescoped series (3.130) and (3.138), the kernel bounds (3.42)–(3.44) for H, G̃, 𝔊, and G₁, and the telescoping at complex s, use the polarised defect in the localised form of the kernel of G_aΔ′_πG_a, as PBG's estimates after (3.131) and on p.423 use it (PBG (3.131) itself localises A₁ and A₂; here the sources are localised): for A₁ = G_a f₁ and A₂ = G_a f₂ with f₁ supported in Δ(y) and f₂ in Δ(y′), and per walk at complex s.
  {#W11.100-2} Every step above is local.
  {#W11.100-3} K is a pointwise bilinear expression at each bond b paired with J(b). ω_i := G′RD*A_i is a walk sum whose terms decay from Δ(y) at the telescoped rate of §7 after 10.3, and the form (c) for G′RD* is itself a per-walk bound with that decay.
  {#W11.100-4} The interpolation inequality acts on balls of radius ℓ ≤ a_j, so at b it reads sup|e| and [∇e]_β on the ball of radius a_j about b only.
  {#W11.100-5} The second bracket is pointwise up to the exponential tail of (Q₁Q₁*)^{−1}.
  {#W11.100-6} So at each b the defect is at most O(1)L^β(1 + B₀)²(Mα₀ + C₀ε₁)𝔰^{β/(1+β)}e^{−δ_π(d(b, y) + d(b, y′))} times the local sup norms of f₁ and f₂ in the units of (3.131), with δ_π := min(δ₀′/(54L), δ_Q)/4, a quarter of the smallest rate of the factors K, ω_i, and the second bracket: δ₀′/(54L) that of §7's telescoping after 10.3, which the form (c) for G′RD* uses (§7 runs at δ₀′ ≤ δ₀, 10.1, and at δ₀′/54 once C_□ enters at δ₀/27, 10.3;
  {#W11.100-7} the rate δ₀′/54 is in the metric of the cube's own sequence, and the factor 1/L converts it to PRT2's global distance, as for δ_min below), and δ_Q that of (Q₁Q₁*)^{−1} (½δ_Q in the layer-weighted units of (3.131), *The global lift.*, which does not change the minimum, since δ₀′/(54L) ≤ δ_Q/(216L)).
  {#W11.100-8} D_□ is not a factor of Δ′_π; its rate enters through (QGQ*)^{−1} below.
  {#W11.100-9} A composition of kernels keeps a rate only when the other kernels decay strictly faster, with a constant that depends on the gap, and the factor ¼ gives that gap; the ball enlargement by a_j costs only a constant e^{O(1)}.
  {#W11.100-10} The sum over b gives e^{−δ_πd(y, y′)/2} times a volume-free constant, the localised kernel form that the callers use.
  {#W11.100-11} At complex s the same holds walk by walk: each walk term ω_W of ω_i satisfies sup and Hölder bounds equal to its walk bound ("in all norms of Theorems 3.1.–3.10", RG II p.5 l.15–16), and its difference e_W satisfies the sup bound 𝔰 times the walk bound by the per-walk form (c), so the interpolation inequality applies to e_W with the same ℓ and gives 𝔰^{β/(1+β)} times the walk bound.
- {#W11.101} Then H^B − ℒH^A.
  {#W11.101-1} As for G̃, Q^Bℒ = Q^A gives ℒH^A = PQ^{B*}(Q^BPQ^{B*})^{−1} with P := ℒG_π^Aℒ*, so H^B − ℒH^A contains one factor G_π^B − P in each term.
  {#W11.101-2} G_π^B − P telescopes as above into forms (c) for G_a and polarised defects of Δ′_π.
  {#W11.101-3} So H^B − ℒH^A carries 𝔡_H := (δ_w + ϑ_ℒ + ϑ + C_bϑ_b + L sup_x(ε/a_{j(x)})^β)^{β/(1+β)}, the last term from the cell means in 𝔰 and of the exponent β ≥ γ_w, and the uses of H in *The term G̃Δ^{(2)}H₀B.*, in E, and in Δ_𝐇 hold with 𝔡_H in place of δ_w + ϑ_ℒ + ϑ + C_bϑ_b. 𝔡_H is built from global suprema (ϑ_ℒ and the term sup_xL^{−j(x)} of ϑ), so it is a power of L^{−j_min}, j_min ≥ k/2 − 1 the finest layer of the history, not of ε/a_{m(ω)} per walk.
  {#W11.101-4} With ϑ written out, the base of 𝔡_H is 2δ_w + 2ϑ_ℒ + C₂L² sup_xL^{−j(x)} + C_bϑ_b + L sup_x(ε/a_{j(x)})^β, and each of its five terms is at most its constant times L^{−γ_wj_min}: δ_w ≤ C_wL^{−γ_wj_min} by §8, since m(ω) ≥ j_min; ϑ_ℒ ≤ C_bre^{16κ₁}L^{−γ_wj_min}, since min(β₂, 1 − β′) ≥ ½ ≥ γ_w, where ϑ_ℒ's bound passes through the composites H(s), H₀(s), and G̃(s), so C_br carries B_T for B₀ and e^{16κ₁} stands for e^{2·6^dκ₁}, as everywhere for the composites (§11, *So the composite walk terms are summable*); the last two by β_H ≥ γ_w (*The localised 𝔡_H.*) and β ≥ γ_w.
  {#W11.101-5} So 𝔡_H ≤ C_𝔡L^{−γ_Hj_min}, with γ_H := βγ_w/(1 + β) and C_𝔡 := (2C_w + 2C_bre^{16κ₁} + C₂L² + C_b + L)^{β/(1+β)}, a constant of the same quantities as C_w and of C_b, C_br, κ₁, and C₂.
  {#W11.101-6} In powers of ε/a_n, n ≤ k ≤ 2j_min + 2, this is at most C_𝔡L^{γ_H}(ε/a_n)^{γ_H/2}.

{#W11.102} *Complex s.* At complex s, H(s), G̃(s), and H₀(s) are defined walk by walk.
{#W11.102-1} Each operator is the sum (3.107) of [13] over generalised random walks ω, and the term of ω is multiplied by the s-variables of the σ₀-cubes that meet its localisation domain X̃₀⁵ ∪ … ∪ X̃_n⁵ (RG II p.3 l.8–14 and l.27–33).
{#W11.102-2} So G̃(s) is not the series in G_a(s) and Δ^{(2)}(s), and the telescoping above is applied per walk.
- {#W11.103} G and G_π.
  {#W11.103-1} Their walks are the composite walks of their series: PBG replaces each operator of (3.130) by its random walk expansion (p.422 l.13–14, after (3.131)), with Δ^{(2)} or Δ′_π as a joining factor.
  {#W11.103-2} Δ^{(2)} is local as an operator in A, of the range of several blocks ((3.137)), with the coefficient H*J.
  {#W11.103-3} Its H is itself replaced by its walk expansion, as PBG does for the localisation in U ("To have a localization in U we have to expand this operator also", p.427 l.14–21), so each composite walk contains walks of H as constituents and depends on the background only on its localisation domain, as RG II p.3 l.16–17 and l.30–32 require for the locality of the decoupled terms (p.5 l.2–3).
  {#W11.103-4} The same holds for the G′RD* inside Δ′_π.
- {#W11.104} (QGQ*)^{−1}.
  {#W11.104-1} G̃ = G − GQ*(QGQ*)^{−1}QG and H = G_πQ*(QG_πQ*)^{−1} also contain (QGQ*)^{−1}, whose expansion PBG does not print: "The operators (QGQ*)^{−1}, or (QG₁Q*)^{−1}, can be analyzed in the same way as the operator (Q′G′²Q′*)^{−1}" (p.422 l.15–16; also p.421 l.2).
  {#W11.104-2} That operator is expanded as C₀(I − R)^{−1} = Σ_nC₀R^n (3.96), with C₀ the parametrix of (2.82) of [4] built from the local inverses C_□, and I − R given by (3.95) as the sum of I and three sums, of (1 − □̃)Q′G′²Q′*h_□C_□h_□, of □̃Q′(G′² − G′_□²)Q′*h_□C_□h_□, and of the commutators [□̃Q′G′_□²Q′*, h_□]C_□h_□ (p.411 l.6–12).
  {#W11.104-3} R is small "By the same estimates as in [4], especially (2.83)–(2.85)" (p.411 l.13), and replacing G′ by (3.90) gives the walk expansion (3.98) (p.413).
  {#W11.104-4} For (QGQ*)^{−1} PBG prints no constituents; PRT2 prints the same construction for (QGQ*)^{−1} with G_□ in place of G′(□̃)² ("We form the equality for QGQ*C in exactly the same way as in (2.82) replacing … Q′, G′(□̃)², G′² by Q, G_□, G", p.249 l.7–9, Proposition 2.7), and the following transfers it to the composite G. G_□ is the series of G with G_a replaced by PBG's local propagator G_{a,□} of (3.87), which lives on the sequence {Ω_n(□)} with Dirichlet conditions outside Ω₀(□), □̃⁴ ⊂ Ω₀(□) ⊂ □̃⁵ (p.408 l.29–35;
  {#W11.104-5} for the intersected sequences of §7, Ω′_0(□) = Ω₀(□)), and with the walks of H in H*J and of G′RD* restricted to those localised in Ω₀(□).
  {#W11.104-6} The local inverses are D_□ := (QG_□Q*)^{−1}.
  {#W11.104-7} They exist and are bounded: QG_□Q* = QG_{a,□}Q* + Q(G_□ − G_{a,□})Q*, and the first has a bounded inverse with decay, as follows.
  {#W11.104-8} By (3.35) on □̃⁵ at the index j (§7, *The cubes next to the finer layer.*) there is a gauge transformation u on □̃⁵ with U^u = e^{iηA}, |A| ≤ c_uM₁α₀(L^jη)^{−1}, c_u = O(1)L³, so QG_{a,□}(U)Q* is u-conjugate to QG_{a,□}(1)Q* up to O(1)L⁵M₁α₀ relative to it (the shift to the coarsest index j + 1 included), as in PBG's reduction of Theorems 3.1–3.3 to the propagators without external field.
  {#W11.104-9} At U = 1, QG_{a,□}(1)Q* is PRT2's QGQ* for the sequence {Ω_n(□)}, with Dirichlet conditions outside Ω₀(□).
  {#W11.104-10} PRT2 states of its Theorem "this theorem holds for the operators G(Ω) with Dirichlet boundary conditions on Ω^c, Ω ⊃ Ω₁" (p.248 l.4), and Ω = Ω₀(□) ⊃ Ω₁(□).
  {#W11.104-11} The proof for QGQ* starts from (2.136), the Theorem's bound, through (2.142) (p.248 l.4–12), which therefore hold with the Dirichlet conditions; PRT2 p.228 l.18–33 also shows that the variational problem with Dirichlet operators outside a neighbourhood Ω of Ω₁ has the same solution.
  {#W11.104-12} The local lower bound is the exact identity (2.145)–(2.146), ⟨B, QGQ*B⟩ = ⟨B₁, C̃_Λ^{(j)}B₁⟩, with C̃ bounded below by the inverse of an upper bound of the form (2.120).
  {#W11.104-13} It concerns the local C_□ = ((QG_□Q*)⌈_□)^{−1}, built from PRT2's torus-local G_□ (Proposition 2.5, on the torus T_□), which the outer Dirichlet condition does not affect.
  {#W11.104-14} The parametrix C = Σh_□C_□h_□ then gives the inverse, with the remainder R estimated as in the proof without boundary at the cubes away from the Dirichlet boundary.
  {#W11.104-15} PRT2 states that "All the reasonings and the results of this paper hold, with minor and obvious changes, for the operators G(Ω)" (p.228 l.43), the Dirichlet operators of p.228 l.18–33, so Proposition 2.7 for {Ω_n(□)} with the Dirichlet condition outside Ω₀(□) is Bałaban's statement.
  {#W11.104-16} The changes at the data cubes □ adjacent to the Dirichlet boundary are spelled out below: there the torus-local G_□ is replaced.
  - {#W11.105} These cubes are layer-0 cubes.
    {#W11.105-1} PBG's local sequence has "Ω_n(□) … a cube with a center at the center of □ and dist(Ω_n(□)^c, Ω_{n+1}(□)) = 2R₀M₀L^nη" (p.408 l.30–32; unchanged at n ≤ j − 1 by §7's intersection), so Λ₀(□) = Ω₀(□) ∖ Ω₁(□) has width 2R₀M₀η, and the data cubes of PRT2's partition for this sequence have side 2M₀η (PRT2 p.229 l.9–10, with M₀ for M).
    {#W11.105-2} PRT2's partition covers the whole lattice, so a data cube adjacent to ∂Ω₀(□) may protrude into Ω₀(□)^c.
    {#W11.105-3} A data cube that meets a block adjacent to Ω₀(□)^c is disjoint from Ω₁(□) once 2R₀ exceeds its ℓ¹ diameter plus one block, 2d + 1, in units of M₀; R₀ ≥ 2d suffices.
    {#W11.105-4} Its data in Ω₀(□) are then layer-0 data, with Q₀ = 1 (PBG (3.16)), and the fields vanish outside Ω₀(□) by PBG's Dirichlet convention (p.394 l.36).
    {#W11.105-5} The cubes of the layers j ≥ 1 and their tori T_□ = □̃³ (PRT2 p.238 l.51) stay away from the Dirichlet boundary: a cube of the layer j meets Ω_j(□), which lies at the ℓ¹ distance ≥ 2R₀M₀L^{j−1}η from Ω₀(□)^c, and □̃³ with one further block of its own scale reaches at most 10M₀L^jη in ℓ∞ from that cube's block, so R₀ > 5dL keeps it inside Ω₀(□) with one block to spare.
    {#W11.105-6} So the condition is that R₀ is a power of L with R₀ > max(2d, 5dL) = 5dL, a lower bound of the kind already on R₀ (PRT2 (2.2): R "a big positive integer"; PBG p.408 l.26–27: R₀ and M₀ are powers of L).
  - {#W11.106} The operator.
    {#W11.106-1} There let G^D_□ := (Δ^D_a)^{−1} on PRT2's torus T_□ with the Dirichlet condition on T_□ ∖ Ω₀(□), every constituent of Δ_a, the projection R included, "defined by operators with Dirichlet boundary conditions" (PRT2 p.228 l.32).
    {#W11.106-2} PRT2's Theorem "holds for the operators G(Ω) with Dirichlet boundary conditions on Ω^c, Ω ⊃ Ω₁" (p.248 l.4), so G^D_□ has the random-walk representation and the decay of the Theorem, Proposition 2.6 (p.247 l.22–31), at its rate δ₃, which depends on d and L only.
    {#W11.106-3} Proposition 2.6 is printed for the torus T_η; T_η is an arbitrary torus, and on T_□ = □̃³ with a single scale (T_□ ∩ Ω₁(□) = ∅ by the condition on R₀ above) and the Dirichlet condition on T_□ ∖ Ω₀(□) its proof applies unchanged.
    {#W11.106-4} Let C_□ := (G^D_□⌈_{□∩Ω₀(□)})^{−1}, since Q = 1 on □: for a cube protruding into Ω₀(□)^c, C_□ and K below act on the bonds of □ ∩ Ω₀(□) only, since G^D_□ vanishes outside Ω₀(□).
  - {#W11.107} Upper bound.
    {#W11.107-1} For the positive operator P := Δ^D_a, the block-inverse formula gives (P^{−1}⌈_□)^{−1} = P_{□□} − P_{□□^c}(P_{□^c□^c})^{−1}P_{□^c□}, a Schur complement, so 0 < C_□ ≤ P_{□□}.
    {#W11.107-2} P contains the nonlocal ∂R∂*, but R is an orthogonal projection, so P ≤ D*D + DD* + |a| and C_□ ≤ (D*D + DD* + |a|)⌈_□, a local majorant, with ‖C_□‖ ≤ 4dη^{−2} + |a|.
    {#W11.107-3} The identity (2.145)–(2.146) is not used at these cubes.
  - {#W11.108} Kernel decay (the analogue of (2.148)).
    {#W11.108-1} PRT2 obtains the decay of its C_□ from an upper bound with decay and a lower bound of the operator it inverts (p.237 l.1–7).
    {#W11.108-2} The same argument runs here for K := G^D_□⌈_□.
    {#W11.108-3} Rescale to η = 1.
    {#W11.108-4} K has the decay of G^D_□, |K(y, y′)| ≤ O(1)e^{−δ₃|y−y′|}, and K ≥ γ := (4d + |a|)^{−1} by the upper bound on C_□.
    {#W11.108-5} For a vector v with |v| ≤ ½δ₃, the conjugate K_v := e^{⟨v,·⟩}Ke^{−⟨v,·⟩} has ‖K_v − K‖ ≤ sup_y Σ_{y′}|K(y, y′)|(e^{|v||y−y′|} − 1) ≤ O(1)|v|δ₃^{−d−1} by the Schur test.
    {#W11.108-6} If O(1)|v|δ₃^{−d−1} ≤ ½γ, then ‖K_v^{−1}‖ ≤ 2/γ, so |C_□(y, y′)| ≤ (2/γ)e^{−⟨v, y−y′⟩}.
    {#W11.108-7} Taking v along y − y′ gives |C_□(y, y′)| ≤ (2/γ)e^{−δ₄^D|y−y′|} with δ₄^D := d^{−1/2}min(½δ₃, γδ₃^{d+1}/O(1)), a rate of d, L, and |a| only, independent of M₀ and R₀.
    {#W11.108-8} In (2.83) the rate of C must be at most a quarter of that of QGQ*; δ₄^D ≤ d^{−1/2}·½δ₃ ≤ ¼δ₃ for d ≥ 4.
    {#W11.108-9} Undoing the scaling, |C_□(b, b′)| ≤ O(1)η^{−d−2}e^{−δ₄^Dη^{−1}|b−b′|}, the form of (2.148) at j = 0.
  - {#W11.109} The remainder.
    {#W11.109-1} The diagonal remainder at □, h_□(QG(Ω₀)Q* − QG^D_□Q*)h_□C_□, compares two operators with the same Dirichlet condition near □ that differ only through the periodisation of T_□.
    {#W11.109-2} Their walk representations, both from the Theorem with Dirichlet conditions, agree on the walks that stay in the region where T_□ and the global domain coincide.
    {#W11.109-3} The change-of-domain estimate of PRT2 p.238 l.2–4 (the factor e^{−δ₀M} "of the type (1.12) [3] connected with a change of a domain") then bounds it, as at the interior cubes.
    {#W11.109-4} The off-diagonal terms R_{□,□′}C_{□′}h_{□′}, □ ≠ □′, are bounded by (2.83)–(2.84) (p.237), whose factor e^{−(1/8)δ₀M} comes from y ∉ □′ (p.237 l.45).
    {#W11.109-5} They use the kernel decay of C_{□′} (p.237 l.37–38), which holds at both kinds of cubes, at the rate min(δ₄, δ₄^D).
    {#W11.109-6} The commutator terms [h_□, □̃QG^D_□Q*] at the boundary cubes need only the decay of G^D_□ and |∂h_□| = O(M₀^{−1}), as at the interior cubes.
  - {#W11.110} The inverse.
    {#W11.110-1} So R is bounded as in the proof without boundary, with min(δ₄, δ₄^D) in place of δ₄, as PBG Corollary 3.6 uses PRT2 on its local sequences (p.408 l.1–11).
    {#W11.110-2} The sequence satisfies PRT2 (2.1)–(2.4): PBG's sequence satisfies (2.1)–(2.2) rescaled to the L^{−j}-lattice (p.408 l.34), (2.3)–(2.4) are definitions, and the intersected sequences satisfy them by §7, *The cubes next to the finer layer.*
      {#W11.110-2-1} So PRT2 Proposition 2.7, (2.149), applied to {Ω_n(□)}, gives (QG_{a,□}(1)Q*)^{−1} with the bound (2.149), |(QGQ*)^{−1}(b, b′)| ≤ C_D(L^jη)^{−2}(L^{j′}η)^{−d}e^{−δ_Dd(b,b′)} for b ∈ Λ_j, b′ ∈ Λ_{j′} (PRT2 p.249 l.11–14), with C_D := the O(1) of (2.149) and δ_D := ½δ₄, δ₄ the rate printed there; the inverse is the global one of that sequence, formed through the parametrix of p.249 l.7–9.
    {#W11.110-3} This is the use that PBG Corollaries 3.5–3.6 make of [4] for G′, (Q′G′²Q′*)^{−1}, and G. The relative bound of the u-conjugate at U, O(1)L⁵M₁α₀ with a decay at a rate slightly below ½δ₀, follows from PBG Theorem 3.4, which prints the bound (3.85) for VG (p.407), with the expansion of F₂ (p.406), the reduction of p.408 l.3–4 (α₁ = O(1)M₁α₀ in PBG, O(1)L⁵M₁α₀ with §7's constants), and the gauge covariance (3.32) (p.396 l.7) and (3.34); the Neumann series in O(1)C_DL⁵M₁α₀ ≤ ½ transfers the inverse to U with 2C_D and the rate ½δ_D′, δ_D′ := min(δ_D, ¼δ₀).
    {#W11.110-4} Here ¼δ₀ is below the perturbation's rate, which is slightly below ½δ₀ after the conjugation by u, so ½δ_D′ is at most half the smaller of the two rates.
    {#W11.110-5} The second part is at most O(1)B₀²(c_πα₀ + C₃Mα₀) relative to it, by the series (3.130) for G_π, whose factors Δ′_π are small with α₀ (PBG p.422 l.14–15, with a constant c_π), and by the series of VAR (180) for G, G = (Δ_a − Δ^{(2)})^{−1}, whose factors Δ^{(2)} carry O(1)C₃Mα₀ (PBG p.422 l.50–52).
    {#W11.110-6} Here c_π contains M₁ and §7's factor c_u (O(1)L⁵ at the index j + 1), since (3.131) carries O(1)Mα₀ through (3.35), and C₃ contains the same factor (*The form (c) for G̃ with the Δ^{(2)} term*).
    {#W11.110-7} The two series decay at a rate slightly below ½δ₀, that of their factors, so the Neumann series converges under O(1)B₀²C_D(c_πα₀ + C₃Mα₀) ≤ ¼ and gives |D_□| ≤ 4C_D at the rate ¼δ_D′.
    {#W11.110-8} At the complex backgrounds of PBG (3.37), the same Neumann series runs with O(1)L⁵M₁α₀ + α₁ in place of L⁵M₁α₀, under O(1)C_D(L⁵M₁α₀ + α₁) ≤ ½, which §8 lists.
    {#W11.110-9} C_D and δ_D are not the constant C_Q and the rate δ_Q of (Q₁Q₁*)^{−1}.
    {#W11.110-10} The defect of the composite G_□ between the runs is not the defect of PBG's G_□ that 10.1 treats; it is telescoped walk by walk as G is, with the polarised defects of Δ′_π and Δ^{(2)} of this section.
    {#W11.110-11} The three sums of (3.95) are formed with G and G_□ in place of G′² and G′_□².
    {#W11.110-12} R is small by the estimates (2.83)–(2.85) of [4], whose inputs are the decay of G and G_□ at the rate of (3.89), the smallness of G − G_□ on □̃ (its walks leave □̃² or reach a cube outside it, so they carry e^{−δ·dist(□̃, (□̃²)^c)}), and the gradient of h_□ for the commutators.
    {#W11.110-13} G and G_□ have these properties by (3.130), (3.131), and the decay of the walks of G_a, H, and G′.
    {#W11.110-14} So the walks of (QGQ*)^{−1} have as constituents the localisation functions h_□ and □̃, the local inverses D_□, and the walks of G and G_□.
    {#W11.110-15} These are shared by the runs, since the partitions and cubes are (§2).
- {#W11.111} *The defect of D_□.* On the data inside Y^∼, where the walks of the localised terms lie at decoupled s (*The support.* of the bridge), Q^Bℒ = Q^A on run A's data.
  {#W11.111-1} The two runs' local data spaces differ as those of C_□ in 10.3.
  {#W11.111-2} Run B's is 𝔇^A ⊕ 𝔇^B_0, with 𝔇^B_0 the data on run B's extra shell of the local sequence, where Q^B_0 = 1.
  {#W11.111-3} Let K^X := Q^XG^X_□Q^{X*}, with K^B in blocks for this splitting, P₁ the projection onto 𝔇^A, and Δ_K := K_{11} − K^A = P₁Q^B(G^B_□ − ℒG^A_□ℒ*)Q^{B*}P₁*.
  {#W11.111-4} The 𝔇^A-row of D^B_□K^B = 1, multiplied on the right by D^A_□, gives
    {#W11.112} [D^B_□]_{11} − D^A_□ = −[D^B_□]_{11}Δ_KD^A_□ − [D^B_□]_{12}K_{21}D^A_□
  {#W11.113} exactly, as 10.3's identity for C_□.
  - {#W11.114} The walks read run B's D_□ only through [D^B_□]_{11}.
    {#W11.114-1} In the parametrix and in the sums (3.95), D_□ stands between factors h_□, or enters through K_□D_□ = 1, which holds in each run on its own data space. h_□ vanishes on run B's extra shell, which lies outside □̃⁴ ⊃ supp h_□.
  - {#W11.115} The first term is the coarse-side intertwining defect of the composite G_□, telescoped as above, between two bounded local inverses.
    {#W11.115-1} It is a flattened composite walk with one primitive defect constituent among the walks of G_□, and with [D^B_□]_{11} and D^A_□ as ordinary constituents at ¼δ_D′.
    {#W11.115-2} So it decays at the composite rate δ_min of *The junction sums.*, which the entries δ_π/4, δ₀′/(54L), δ_gf′/(6L), and δ_D′/(12L) of δ_min cover.
  - {#W11.116} The second term is the extra-shell term, bounded as in 10.3.
    {#W11.116-1} [D^B_□]_{12}(y←w) and D^A_□(z′←y′) are entries of the composite inverses, bounded by 4C_D at the rate ¼δ_D′ (the second Neumann series above).
    {#W11.116-2} Since Q^B_0 = 1, K_{21}(w←z′) = (G^B_□Q^{B*})(w←z′), bounded by the kernel bound of G_□ at the rate ½δ₀ of its series (as G's, PBG (3.131), p.422 l.1–9), with the layer powers moved as in 10.3.
    {#W11.116-3} Let r := ¼δ_D′ ≤ (1/16)δ₀.
    {#W11.116-4} A sixth of the decay pays the junction sums over w and z′, a sixth gives the gain, and two thirds are kept. y lies in supp h_□, at run B's layer ≥ j + 1 of the local sequence, and w in its layer 0, so d(y, w) ≥ 2R₀M₀j by the shell widths of the local sequence (as (2.60) in 10.3).
    {#W11.116-5} Then e^{−(r/6)2R₀M₀j} = e^{−(δ_D′/12)R₀M₀j} ≤ L^{−βj} = (ε/a_j)^β under δ_D′R₀M₀ ≥ 12β log L. So the extra-shell term is at most C_D′(ε/a_j)^β times the bound of D_□ at the rate ⅔r = δ_D′/6, with C_D′ a constant of d, L, C_D, B₀, and δ_D′.
    {#W11.116-6} For H₀'s local inverses (QG_{a,□}Q*)^{−1}, the base inverse at ½δ_D′, the same split holds with room to spare.
  - {#W11.117} So the defect of D_□ has the factor (ε/a_j)^β and the rate δ_D′/6.
    {#W11.117-1} The other constituents have the defects of §7.
- {#W11.118} So the telescoping holds term by term for every walk of G, G_π, G̃, H, H₀, H₁, and 𝔊, with one constituent defect per term.
  {#W11.118-1} The resolvent identity F(G^B) − F(P) above is used only at s = 1 and only on Y^∼.
  {#W11.118-2} The s-weight of a walk is a common factor of its run-A and run-B terms.
  {#W11.118-3} Summed over the walks with the decay (1.7) of RG II, the telescoping gives the bounds above with the factor e^{16κ₁} of RG II's bound for H(s), G̃(s), and H₀(s).
  {#W11.118-4} RG II's argument for that factor reads "If m is big enough, for example m > 2⁴, then δ₀d(ω) ≥ δ₁mM, for a positive constant δ₁ depending on δ₀ only" (p.5 l.13–15), with m the number of s-parameters of the walk (this δ₁ is RG II's, not the rate δ₁ of (3.132) in §9), and uses e^{−δ₀d(ω)} against e^{mκ₁}.
  {#W11.118-5} The defect terms decay at the rate δ_min, which is at most half the smallest kernel rate of their constituents, by the composition gap above, δ_min := min(δ_π/4, δ₀′/(54L), δ_gf′/(6L), δ_D′/(12L)): δ_π/2 the kernel rate of the localised bilinear form, δ₀′/27 for C_□ in §7 (10.3 gives δ₀/27, and δ₀′ ≤ δ₀), δ_gf′/3 that of G_□ in §5(c) after the DRD* condition of 10.4, δ_gf′ = min(δ₀/486, δ₀′), and δ_D′/6 that of D_□ in (QGQ*)^{−1}, with its extra-shell term (*The defect of D_□.*).
  {#W11.118-6} Since δ₀′ = min(δ₀, ¼δ_Q, ¼δ₁, ¼δ_c) ≤ ¼δ_Q and δ₀′ ≤ ¼δ_c ≤ δ₀/64, with δ_c = (1/16)min(δ_V, δ₀, δ₁) (10.5), δ_π/4 = δ₀′/(864L) is below δ₀′/(54L) and δ_gf′/(6L), so δ_min = min(δ₀′/(864L), δ_D′/(12L)) ≤ δ₀/(55296L).
  {#W11.118-7} Here δ_D′ is the smallest of the rates of the local inverses of the G, G₁, and G_π problems, whose (QG₁Q*)^{−1} and (QG_πQ*)^{−1} are built in the same way.
  {#W11.118-8} The factor 1/L converts the local constituents' rates to PRT2's global distance.
  {#W11.118-9} C_□, G_□, the local G_{a,□}, D_□, and the local composites decay in the weighted distance of their cube's own sequence {Ω_n(□)}, for □ ∈ 𝒟_j with the weight (L^nη)^{−1} on its shells n < j, (L^jη)^{−1} on □̃⁴ ∖ Ω_{j+1}(□), and (L^{j+1}η)^{−1} on Ω_{j+1}(□) = □̃³ ∩ B^{j+1}(Λ_{j+1}) (PBG p.408 l.29–35).
  {#W11.118-10} They act between points of □̃⁵: supp h_□ ⊂ □ (PRT1 (1.118), to which PRT2 p.229 l.12 points; PBG p.414 l.46 for ζ_{□̃}), the sums (3.95) and (3.97) act between □̃ and supp h_□ (p.412 l.20), the modified partitions use □₀ = □̃² or □̃₁² with □₁ ∈ 𝒟_{j+1} (p.411 l.22–26), and the internal junctions of the local composites range over Ω₀(□) ⊂ □̃⁵.
  {#W11.118-11} The rule is applied per constituent at its own scale j′: j′ = j for □ ∈ 𝒟_j and for the 𝒟′ cell □₀ = □̃², which uses □'s own sequence, and j′ = j_Q for the cubes Q of §7's second case (□₀ = □̃₁², with j_Q = j + 1, and 𝒟″'s cube □″), whose propagators live on Q's sequence of §7: p.408's recipe at the layer j of □, centred at p_Q, with the extensions of the scale j_Q, for the cells in the bulk, and §12's restricted sequences for the cells on the collar (PBG p.412 l.23–28: "valid for propagators defined by sequences {Ω_j} with Ω₀ contained in a cube for which the condition (3.25) is satisfied",
  {#W11.118-12} with (3.25) printed for the regularity condition (3.35)).
  {#W11.118-13} PBG prints the sequence {Ω_n(□)} for □ ∈ 𝒟_j (p.408 l.29–35 and p.409 l.1–3), with Ω₀(□) ⊂ □̃⁵, and not for the 𝒟′ and 𝒟″ cells.
  {#W11.118-14} So Ω₀(□) ⊂ □̃⁵ and Ω₀(Q) ⊂ Q̃⁵, at most eight big blocks of the scale j′ in the sup norm from a block of B^{j′}(Λ_{j′}) for □ and □₀ = □̃² (for □̃₁², the block of □₁ in B^{j+1}(Λ_{j+1})), and at most twelve for □″.
  {#W11.118-15} In PRT2's ℓ¹ distance (p.223 l.15–16) these sets lie within 8dM₁L^{j′}η of that block (12dM₁L^{j′}η for □″).
  {#W11.118-16} The layer Λ_{j′−1} has an ℓ¹ width > RM₁L^{j′−1}η = (R/L)M₁L^{j′}η (VAR (1), PRT2 (2.2)), so under R ≥ 8dL (R ≥ 12dL for □″) the domain of each local constituent lies in the global layers j′ − 1, j′, and j′ + 1.
  {#W11.118-17} There the local weight is at least 1/L times the global weight of PRT2 (2.46) at every point.
  {#W11.118-18} On the local shells n < j′ it is at least (L^{j′−1}η)^{−1}, which is at least the global weight there.
  {#W11.118-19} On □̃⁴ ∖ Ω_{j′+1}(□) it is (L^{j′}η)^{−1} ≥ L^{−1}(L^{j′−1}η)^{−1} (on Q̃⁴ ∖ Ω_{j+1}(Q) for j_Q = j + 1 it is (L^jη)^{−1} = (L^{j′−1}η)^{−1}, larger still).
  {#W11.118-20} On Ω_{j′+1}(□) the two agree, and outside Ω₀(□) the constituent does not act.
  {#W11.118-21} So a local rate δ is at least δ/L in the global d. □̃₀⁵ is a cube of 16 big blocks (Q̃⁵ of 20 for □″, treated in §7 with R ≥ 12dL), larger than the class constant 12 that PBG takes (p.409 l.2); PBG's class allows any constant ≥ 10 (p.396 l.16).
  {#W11.118-22} PBG's class also asks that a cube of the index j lie in B^j(Λ_j) ∪ B^{j+1}(Λ_{j+1}) (p.396 l.14–17), which a 16-block cube may violate by meeting the layer j′ − 1.
  {#W11.118-23} Class membership is not used: Corollary 3.6's proof uses only (3.35) on a cube containing Ω₀, through the gauge transformation u and Corollary 3.5 (p.408 l.1–9), as PBG says of the propagator differences (p.412 l.25–28) and as §12 uses on the collar.
  {#W11.118-24} (3.35) on a cube follows, in the axial gauge from its centre, from the curvature bounds on that cube, with a constant proportional to its side.
  {#W11.118-25} The curvature bounds used for 10.1's backgrounds come from VAR (9)–(10) on VAR's class cubes.
  {#W11.118-26} VAR's 𝔘_k alone bounds only F and the current (VAR p.278 l.5–6), so the |∇F| half needs VAR (9).
  {#W11.118-27} A class cube of the index j is a union of big blocks of the scale j of the side 2M_VL^jη, M_V a multiple of R₁M₁, whose cube □̃ of the side (2M_V + 4R₁M₁)L^jη with the same centre is contained in Ω_j ∖ Ω_{j+2} and not in Ω_{j+1} (VAR p.278 l.50–51 and p.279 l.2–4).
  {#W11.118-28} On such a cube VAR (9) at β = 1 and (10) give |F| ≤ C₀(M_V)ε₁a^{−2}, |∇F| ≤ C₀(M_V)ε₁a^{−3}, and the current ≤ C₀(M_V)ε₁a^{−3} at the spacing a = L^jη, with C₀(M_V) := 4M_V(B₃ + B₄(1)), as in the Cauchy note's (9.2), where C₀ := C₀(R₁M₁).
  {#W11.118-29} Every point x of a global layer m lies in a class cube of the index m or m − 1.
  {#W11.118-30} Here big blocks have a side at most R₁M₁L^jη, R ≥ 12dL, R₁M₁ ≤ M₁ (with equality, R₁M₁ = M′ = M₁, in the LF note's conventions, derived there, §8), and the layers have ℓ¹ widths > RM₁L^{m}η (VAR (1), PRT2 (2.2)), hence sup-norm widths > RM₁L^mη/d.
  - {#W11.119} If the sup-norm distance from x to Ω_m^c is at least 5R₁M₁L^mη, take the index m and M_V = R₁M₁, with x ∈ □. □̃ lies within 4R₁M₁L^mη of x, so □̃ ⊂ Ω_m, and □̃ misses Ω_{m+2}, which is at a sup-norm distance > RM₁L^{m+1}η/d ≥ 12L²R₁M₁L^mη. □̃ is not in Ω_{m+1}, since x ∉ Ω_{m+1}.
  - {#W11.120} Otherwise take the index m − 1 and M_V = 3LR₁M₁, so that □ has the side 6R₁M₁L^mη.
    {#W11.120-1} A point y ∈ Ω_m^c lies within 5R₁M₁L^mη of x, so a union □ of big blocks of the scale m − 1 of that side contains both x and y (the blocks have a side ≤ R₁M₁L^{m−1}η, and 5R₁M₁L^m + R₁M₁L^{m−1} ≤ 6R₁M₁L^m).
    {#W11.120-2} Then □̃ is not in Ω_m. □̃ lies within 6R₁M₁L^mη + 2R₁M₁L^{m−1}η ≤ 7R₁M₁L^mη of x.
    {#W11.120-3} Ω_{m−1}^c is at a sup-norm distance > RM₁L^{m−1}η/d ≥ 12R₁M₁L^mη from x, and Ω_{m+1} at a distance > RM₁L^mη/d − 5R₁M₁L^mη ≥ (12L − 5)R₁M₁L^mη ≥ 7R₁M₁L^mη.
    {#W11.120-4} So □̃ ⊂ Ω_{m−1} ∖ Ω_{m+1}.
    {#W11.120-5} This cube parameter needs 3LR₁M₁ ≤ M(ε₁) = R₁M₁a₁/ε₁ (VAR p.279 l.28), that is ε₁ ≤ a₁/(3L).
  {#W11.121} So at every point of the layer m, at the spacing a_m := L^mη of that layer, |F| ≤ O(1)L³C₀ε₁a_m^{−2}, and |∇F| and the current are ≤ O(1)L⁴C₀ε₁a_m^{−3}, the factors L², L³ from a_{m−1} = a_m/L and L from C₀(3LR₁M₁) = 3LC₀.
  {#W11.121-1} The axial gauge therefore gives (3.35) with O(1)L⁴C₀ε₁ in place of α₀, and (3.35) with α₀ holds under O(1)L⁴C₀ε₁ ≤ α₀.
  {#W11.121-2} This is an upper bound on ε₁, as is ε₁ ≤ a₁/(3L).
  {#W11.121-3} Both are imposed after α₀ (α₀ is fixed after L, M, and M₁, and C₀ is a constant of R₁M₁ and Bałaban's constants), and they hold for γ small at the data parameter, which is ≤ Cḡp₀(ḡ) (§8).
  {#W11.121-4} §8 lists them.
  {#W11.121-5} Under R ≥ 8dL a 16-block cube meets at most two consecutive layers, since the layer j′ is wider than 16M₁L^{j′}η.
  {#W11.121-6} On the layer j′ − 1 the bounds hold at the scale j′ − 1, which is weaker than at the scale j′ by L² for |F| and L³ for |∇F| and the current.
  {#W11.121-7} So (3.35) holds on these cubes at the index j′ with O(1)L²M₁α₀ for |A| and O(1)L³M₁α₀ for |∇A|, which reads |∇F|, and (3.36) with O(1)L³M₁α₀, and with the shift to the coarsest index j + 1 of PBG's sequences the smallness O(1)L⁵M₁α₀ ≤ a₁ is required (§7, *The cubes next to the finer layer.*).
  {#W11.121-8} This is an upper bound on α₀ imposed after L and M. R ≥ 12dL and this smallness are listed in §8.
  {#W11.121-9} On the collar of 𝐁₁ the layers are thinner, and the constituents of the cubes there are built on the intersected sequences {Ω′_m(□)} of §12 (*The collar at ∂Ω and at the reflex edges.*), whose weighted distance d′ satisfies d′ ≥ d_col/c_d − 1, so a local rate δ is a rate δ/c_d in d_col (§12, *The crossing decay at every point.*).
  {#W11.121-10} The cubes Q̃² ⊇ Ω′_0(Q) of the collar's cells Q, built on §12's restricted sequences (*The cells of 𝒟′ and 𝒟″ on the collar.*), lie where the scale-h regularity holds.
  {#W11.121-11} That regularity holds on the band (Ω″_{h+1})^c ∩ Ω″^{∼2}_{h+1} (§12, *The background pairs.*).
  {#W11.121-12} The domains Ω_j^{∼n} are unions of L^{−(k−j)}MR_j-cubes of T_η (LFR I p.179 l.8–9), and ∼ adds the adjacent cubes of that size (the operation defined at CRE p.245 l.40–43 and used at p.256 l.57–63), so the cut ∂Ω″^∼_{h+1} lies at an ℓ∞ distance ≥ MR_{h+1}a_{h+1} from both boundaries of the band.
  {#W11.121-13} The collar lies within 2M₁a_h of the cut.
  {#W11.121-14} A collar cell has j′ = j_Q ≤ h, and Q̃² ⊂ Q̃⁵, which meets the collar and has the side at most 20M₁a_{j′} ≤ 20M₁a_h, so Q̃² lies within 22M₁a_h of the cut.
  {#W11.121-15} All distances here are ℓ∞ distances, and in this passage on the collar (from "The collar lies within 2M₁a_h" to the end of the bullet), M₁ is CRE's M₁ = KM′, the unit of the collar's width, which is at least PBG's block size M′ (§8), so the bounds 20M₁a_{j′} and 22M₁a_h hold with it.
  {#W11.121-16} Since 24M₁a_h ≤ MR_{h+1}a_{h+1} under M ≥ 4M₁, as 4LR_{h+1} ≥ 24 for L > 5 (R_{h+1} ≥ 1), the cube lies in the band, at the distance ≥ 2M₁a_h from its boundaries, and the regularity at the scale h ≥ j′ gives (3.35) there at the index j′: for U_{1,2} this is Bałaban's PBG (3.35)–(3.36) at the layer h near the cut (§12, *The background pairs.*: REG's 𝔘-membership at the index h, with (3.35)–(3.36) by REG's Sect. F and Proposition 6, at the constant of VAR (14)), which bounds |∇A| at the scale h and so at the index j′ ≤ h with the factors L² and L³ above,
  {#W11.121-17} and for ι(U_{1,2}) it is the bridge of §12 from the minimiser base V₀, which satisfies VAR (9)–(10) by VAR Theorem 1, since V₀ is a genuine minimiser and the cut is not a boundary of its problem.
  - {#W11.122} The distance of a composite walk.
    {#W11.122-1} The constituent walks are of two kinds.
    {#W11.122-2} Chains decay in PBG's path distance (3.93), the infimum of the lengths of the paths from y to y′ through points y_i ∈ □_i ∩ 𝔅.
    {#W11.122-3} The Δ^{(2)}- and Δ_π^{(2)}-type composites (G and G̃ of VAR (180), G₁, H₁, 𝔊, H₀, (QGQ*)^{−1}, (QG₁Q*)^{−1}, (QG_aQ*)^{−1}, and the local G_□) are trees, with d(ω, y, y′) "a length of a shortest tree intersecting all domains X_i in ω" (PBG p.427 l.14–21), in the distance of PRT2 (2.46).
    {#W11.122-4} That the tree contains y and y′ follows from its construction from the chains of (3.93).
    {#W11.122-5} PBG builds these expansions by inserting the chain expansions of type (3.107) into the operators of (3.138) and (3.134)–(3.135), where three chains meet in a localisation domain of C^{(2)} (p.427 l.14–20).
    {#W11.122-6} Each chain is bounded by (3.108) in the distance (3.93), the infimum over y_i ∈ □_i of d(y, y_1) + … + d(y_n, y′), which contains its endpoints (p.410 l.26–31).
    {#W11.122-7} The bound of the composite is the product of the chain bounds, summed over the junction points with part of the exponent, as in §11's *The junction sums.* So its exponent is the length of a tree through y, y′, the junction points, and points of every X_i.
    {#W11.122-8} RG II's d(ω) is of this kind.
    {#W11.122-9} RG II's geometric inequality, printed for its walks (p.5 l.13–15), holds for d_T with changed constants.
    {#W11.122-10} The domains of the new constituents are of the type of PBG's (3.96): unions of at most N_D cubes □̃⁵ of their layer j ≤ k, and connected: "each domain is a union of a connected, finite family of cubes", two cubes of the family joined by a chain of intersecting cubes (PBG p.413 l.3–5).
    {#W11.122-11} So the diameter is ≤ 12N_DM₁a_j for the cubes □̃⁵ of □ ∈ 𝒟_j, of side 12M₁a_j (PBG p.408 l.23–24), and ≤ 16N_DM₁a_{j′} for the 𝒟′ cells, whose cubes □̃₀⁵ have 16 big blocks of the scale j′ ≤ k; so it is ≤ Ma_k under M ≥ 16N_DM₁.
    {#W11.122-12} Each domain meets the tree, so the M-cubes of the scale k that the domains meet lie within the distance Ma_k of the tree.
    {#W11.122-13} A tree of the physical length ℓ, made of bonds of length ≤ a_k, splits greedily from its leaves into at most ℓ/(Ma_k) + 1 subtrees, each of length < 2Ma_k + a_k.
    {#W11.122-14} At a vertex where several pendant branches, each with its edge shorter than Ma_k + a_k, end, the branches are grouped, adding branches until the group reaches the length Ma_k; each group is a subtree through the shared vertex, so the pieces of length ≥ Ma_k number at most ℓ/(Ma_k), plus one remainder.
    {#W11.122-15} A subtree of length < 2Ma_k + a_k has coordinate extent < 2Ma_k + a_k in each direction, so the set within the distance Ma_k of it lies in a box of side < 4Ma_k + a_k < 5Ma_k (M > 1), and a box of side strictly below 5Ma_k meets at most 6 closed intervals of the partition per direction, so at most 6^d M-cubes, closed contact included.
    {#W11.122-16} So the tree has at most 6^d(ℓ/(Ma_k) + 1) M-cubes within the distance Ma_k of it, and d_T ≥ ℓ/a_k, since the weights of PRT2 (2.46) are ≥ 1/a_k at the layers ≤ k.
    {#W11.122-17} So m ≤ 6^d(d_T/M + 1), and for m > 2·6^d, δ₀d_T ≥ δ₁′mM with δ₁′ := δ₀/(2·6^d).
    {#W11.122-18} The argument of (1.11) then runs with δ₁′ for δ₁ and the factor e^{2·6^dκ₁} for e^{16κ₁}; the factor is written e^{16κ₁} below, with 16 standing for 2·6^d at the composites, and δ_g := min(δ₁, δ₁′) denotes the geometric constant, RG II's δ₁ or δ₁′, to keep it apart from the rate δ₁ of PBG (3.132).
    {#W11.122-19} The domains are taken over all constituents, N_D their largest number of cubes, and the distances in the sup norm of the lattice.
    {#W11.122-20} A path through the domains is such a tree, so both distances dominate the tree length d_T(ω, y, y′).
    {#W11.122-21} A composite kernel A(x, z)B(z, y) joins a walk ω_A of A, whose tree or path contains x and z, and a walk ω_B of B, whose tree or path contains z and y.
    {#W11.122-22} Their union is connected, contains x and y, and meets every domain of the composite walk ω, so d_T(ω, x, y) ≤ d(ω_A, x, z) + d(ω_B, z, y).
  - {#W11.123} The junction sums.
    {#W11.123-1} The constituents decay at rates ≥ 2δ_min.
    {#W11.123-2} Of each constituent's rate, ½δ_min pays the sum over the junction point z, ½δ_min produces the small factors O((δ_minM₁)^{−1}) where the defect constituent sits in a group of the expansions (3.96) (below), and δ_min gives the decay of the composite.
    {#W11.123-3} The kernels decay in PBG's weighted multiscale distance d (PRT2 (2.46)).
    {#W11.123-4} By PRT2 (2.56)–(2.58) at the rate ½δ_min, the sum over the junction point costs at most S_δ := O(1)sup_yΣ_{y′∈𝔅}e^{−½δ_min d(y, y′)} ≤ O(1)c₁, c₁ = 12c₀^d < 12(16/δ_min)^d (PRT2 p.233 l.37 and l.46–48), per joint, uniformly in the volume and in k.
    {#W11.123-5} The O(1) covers the offsets of the points of 𝔅 and of the finite-range operators Q, Q*, D, D*, and h_□ at the joint.
    {#W11.123-6} PRT2's (2.57) uses the separation RM of the domains of its (2.2), so the analogue of its (2.59) is stated for the separations of the layers on which the joints lie: RM₁ for the global layers (VAR (1), p.277 l.14, "(L^jη)^{−1}dist(Ω_j^c, Ω_{j+1}) > RM₁") and 2R₀M₀ for PBG's local sequences {Ω_n(□)} (PBG p.408 l.29–35):
    {#W11.124} (J0) ⅛δ_minRM₁ > 2d log(16/δ_min) + 1 and ¼δ_minR₀M₀ > 2d log(16/δ_min) + 1.
    {#W11.125} These are lower bounds on RM₁ and on R₀M₀, imposed after δ_min and before M₁ = KR₀M₀.
    {#W11.125-1} The rate δ_min left over gives e^{−δ_min d_T(ω, x, y)}.
    {#W11.126} The joints are unbounded in number in the chains of the series:
    - {#W11.127} the series (3.130) for G_π, G₁'s series (3.138), and the note's Neumann expansion of G = (Δ_a − Δ^{(2)})^{−1} of VAR (180), with the factors c_πα₀ and C₃Mα₀;
    - {#W11.128} the series of the local composite propagators G_□, G_{π,□}, and G_{1,□}, with the factors c_πα₀ and C₃Mα₀ of their global analogues;
    - {#W11.129} the two Neumann series for D_□ and its G₁ analogue, with O(1)C_D(L⁵M₁α₀ + α₁) for the transfer of (QG_{a,□}(1)Q*)^{−1} to U (*The inverse.*, α₁ at the complex backgrounds) and O(1)B₀²C_D(c_πα₀ + C₃Mα₀) for the second;
    - {#W11.130} the expansions (3.96) of (QGQ*)^{−1}, (QG₁Q*)^{−1}, the inverse (QG_πQ*)^{−1} in H = G_πQ*(QG_πQ*)^{−1}, and the inverse (QG_aQ*)^{−1} in H₀ = G_aQ*(QG_aQ*)^{−1}, with their local inverses and the Neumann series of these, built in the same way, with PBG's small factors produced by spending exponential decay (p.411 l.27–32, "we attach the factor 8δ₀^{−1}M^{−1}", and p.412 l.27–28), or by the commutator with ∂h (p.412 l.17).
      {#W11.130-1} These are M₁^{−1} in RG II's application (RG II p.3 l.27–28, M₁ ≤ M/R₁).
      {#W11.130-2} Where the defect constituent sits in such a group, its rate is 2δ_min, and the share ½δ_min over the step of the length ≥ M₁ of (3.96) gives e^{−½δ_minM₁} ≤ 2(½δ_minM₁)^{−1}, the factor O((δ_minM₁)^{−1}), as PBG's e^{−¼δ₀M} ≤ 3!(¼δ₀M)^{−3} gives its factor.
      {#W11.130-3} PBG's commutator terms with ∂h (p.412 l.17) carry their factor O(M^{−1}) from the derivative of h_□, not from decay, and the same holds at the defect, with O(M₁^{−1}) ≤ O((δ_minM₁)^{−1}).
    {#W11.131} These chains also occur nested in the fixed formulas inside series factors (H inside each Δ^{(2)}, G′RD* inside each Δ′_π, P_π inside Δ_π^{(2)}).
    {#W11.131-1} The nesting is finite: Δ^{(2)} → H → G_π → Δ′_π → G′RD* → (3.98), with no return to G or G₁.
    {#W11.131-2} So each small factor is grouped, as PBG groups the factors of its expansions so that each group has a small factor (p.412 l.3–8), with at most r_* joints: its own and those of the fixed formulas nested in it at the top level, r_* ≤ N_c + 1 + N_f(r₀ + 1), with r₀ the largest number of top-level joints of a fixed formula, plus one joint attaching it to the group (as the coefficient H*J of Δ^{(2)} is Σ_zH(z, ·)J(z)), and N_f ≤ 3 the largest number of fixed formulas at the top level of one small factor (Δ_π^{(2)} = P_π*Δ^{(2)}P_π carries two factors P_π and the H of Δ^{(2)}).
    {#W11.131-3} The series nested deeper inside a fixed formula, such as (3.130) for G_π inside H, form their own groups.
    {#W11.131-4} The group is small under
    {#W11.132} (J) O(1)S_δ^{r_*}(B₀′²C_DL(δ_minM₁)^{−1} + C_D(L⁵M₁α₀ + α₁) + B₀′(c_πα₀ + C₃Mα₀) + B₀′²C_D(c_πα₀ + C₃Mα₀)) ≤ ¼,
    {#W11.133} with B₀′ (the constituent walks are summed with the doubled constant of §7, bounded uniformly for M₁ above Bałaban's threshold), and B₀′²C_D in the first term, since each factor of (3.96) that contains R contains a D_□ with |D_□| ≤ 4C_D and up to two propagator-type operators (PBG p.411 l.28–29; G, G_□, G₁, or G_π, whose constant is B₀′ or the composite's).
    {#W11.133-1} C_D and the rate δ_D come from PRT2 at (R₀, M₀) and do not depend on M₁ or on a larger R₀M₀.
    {#W11.133-2} The positivity constant γ₀ of (QG_□Q*)↾_□ depends "on d and L only" (PRT2 p.248, (2.147)), and so do the rate δ₃ and the O(1) of Proposition 2.6 (p.247 l.23 and l.31).
    {#W11.133-3} The upper bound and the decay that C_□'s bound and the rate δ₄ of (2.148) use (p.248 l.48–p.249 l.2) are those of the kernel of (QG_□Q*)↾_□ with PRT2's torus-local G_□, from its bounds (2.133) at the rate δ₂; δ₂ "depends on d and L only" (PRT2 p.246 l.35), and so does δ₄.
    {#W11.133-4} For C_□^ξ the print says "This implies the same properties for C_□^ξ with the corresponding bounds and a decay rate δ₄" (p.248 l.48–p.249 l.2).
    {#W11.133-5} There the rate δ₁ depends "on δ₀ and the bound γ₀" (p.237 l.3–7), by a conjugation with e^{⟨a,·⟩} that uses only the lower bound and the kernel's upper bound and decay.
    {#W11.133-6} Here these are γ₀ and the bound (2.133) at δ₂, both of d and L only, and neither depends on R₀M₀ or on the size of □.
    {#W11.133-7} The inverse of (2.149) is the Neumann series of the parametrix (2.82)–(2.85), whose remainder R obeys |R(y,y′)| ≤ O(M^{−1})e^{−δ₁d(y,y′)}(L^{j′}η)^{−d} (2.85), with δ₁ depending on δ₀ and γ₀ (p.237 l.3; the rate of the parametrix of Q′G′²Q′*, whose analogue in Proposition 2.7 is δ₄) and the factors e^{−⅛δ₀M} and O(M^{−1}) of (2.83)–(2.85) decreasing in M. So above PRT2's threshold a larger M or R₀M₀ only decreases ‖R‖, the series constant stays ≤ 2, and C_D and δ_D = ½min(δ₄, δ₄^D) are uniform, δ₄^D being a rate of d, L, and |a| only (the boundary cubes above).
    {#W11.133-8} So the ordering of (J0) after δ_min is not circular.
    {#W11.133-9} The step of (3.96) has the length ≥ M₁ in the local metric of the scale j (PBG p.411 l.30–31).
    {#W11.133-10} Where the defect sits in a local constituent, the share ½δ_min is taken in the local metric at its rate ≥ 2Lδ_min; where it sits in a global composite spanning the step, the step is ≥ M₁/L in the global distance, since □ may protrude into Λ_{j+1}.
    {#W11.133-11} The factor L of the first term covers the second case.
    {#W11.133-12} (J) carries the walk-count constants, the number of composite structures of a group (a constant of the finite nesting), and the factors of the mixed telescoping terms over the group's own constituents in the O(1): the position multiplicity ≤ r_* + 1, the factor (3/2)^{r_*}, the leftover factor 3/2 per non-defect constituent walk, and a factor 2 per nested series instance, all constants of the finite nesting (as in the LF note's telescoping of the transferred walk terms, at N_cmax_c𝔡_c ≤ log(3/2);
    {#W11.133-13} where that fails, each run's whole composite term, not each group, is bounded separately, as in §7, *Telescoping.*, so the constant C_tel enters once per composite term, with c₂ the constant of the composite's slot map, 1 on data and C_ℒ′ on sources as in §7).
    {#W11.133-14} The term B₀′(c_πα₀ + C₃Mα₀) is the global series factors of (3.130) and VAR (180).
    {#W11.133-15} The telescoping runs over all primitive constituents, one defect per term.
    {#W11.133-16} Those inside the constituent walks of G_a, H, and G′, N_c(|ω_i| + 1) for a constituent walk ω_i, a number unbounded in |ω_i|, are paid as in §7's *The absorption.*, by doubling the factor O(M₁^{−1/2})^{|ω_i|} of each constituent walk (B₀′).
    {#W11.133-17} Those of the series-level groups and of their top-level fixed formulas, at most r_* per group, are paid by the per-group constant above, and the number of groups that can carry the defect, at most n + 1 for n groups, is summed by Σ_n(n + 1)2^{−n} < ∞ against the remaining factor 2 per group.
    {#W11.133-18} So the doubling is kept inside the constituent walks, and (J) pays the series-level groups, which carry no factor M₁^{−1/2}.
    {#W11.133-19} (J) is a lower bound on M₁ and, given M, an upper bound on α₀ of the kind of RG I's "Mα₀, Mα₁ are still small" (p.275 l.28); δ_min depends on neither.
    {#W11.133-20} In VAR's application α₀ = ε₀ (VAR p.280 l.52), and VAR's Theorem 1 assumes B₃ε₁ ≤ ε₀ and ε₀ ≤ a₀ (p.279 l.15; the remark at p.278 l.46–47 gives ε₁ = O(ε₀) in any case).
    {#W11.133-21} At α₀ = ε₀ the first follows from §11's O(1)L⁴C₀ε₁ ≤ α₀, since C₀ ≥ 4R₁M₁B₃ ≥ B₃, and the second is α₀ ≤ a₀, VAR's a₀, an upper bound on α₀ after L, listed in §8.
    {#W11.133-22} The bridge's LC_ιε₁ ≤ O(1)M₁α₀, with M₁ PBG's block size M′ (the O(1)M₁α₀ is PBG's (3.36) size) and C_ι = O(1)L²C_LC_F of the Cauchy note (#C9.8.15-3; its C_F is VAR Theorem 1's one-step constant, not §12's C_F^Λ), is an upper bound on ε₁ imposed after α₀, M′, and L, and it holds for γ small whatever the dependence of C_F on R₁M₁.
    {#W11.133-23} The joints of the fixed formulas at the top level of a composite are bounded in number by r₀, so they cost S_δ^{r₀}, a constant in C_w.
    {#W11.134} So the composite walk terms are summable over the walks, with a constant B_T and the decay e^{−δ_min d_T(ω, x, y)}.
    {#W11.134-1} B_T := O(1)B₀′S_δ^{r₀}(1 + 4C_D)Σ_n(n + 1)2^{−n}: B₀′ for the constituent walks, S_δ^{r₀} for the top-level joints, at most ¼ per group under (J), and 4C_D for D_□.
    {#W11.134-2} It depends on d, L, δ_min, and PBG's and PRT2's constants, and is uniform in the volume, in k, in M and M₁ above their thresholds, and in κ₁.
    {#W11.134-3} Wherever §11 and §12 quote RG II's B₀e^{16κ₁} for the composites H(s), G̃(s), and H₀(s) (*The bridge*, *The applications.*, *The fixed point 𝐀₀.*, and (a) of the form (c)), B₀ stands for B_T and 16 for 2·6^d, and the smallness conditions read there (κ_V ≤ ½ and the ε₂ conditions of RG II (1.13)–(1.14), spelled out in §8, stages 5 and 6) are read with B_T.
    {#W11.134-4} This is the form that RG II's κ₁ argument uses (p.5 l.13–16 and (1.11), where the supremum over the walks is bounded by 1).
  - {#W11.135} The condition on M. Put ρ := δ_min/δ₀, with δ₀ PBG's rate.
    {#W11.135-1} RG II's δ₀ is half of it ((1.7), with PBG's ½δ₀).    {#W11.135-4} The geometric inequality, derived above for d_T(ω), holds with δ_g.
    {#W11.135-5} Of the composite rate δ_min, ¼δ_min is spent on the s-weights, ¼δ_min is kept for the consumer's form (c), and ½δ_min is kept for the layer crossings of §12's strips (*The crossings.*).
    {#W11.135-6} The geometric inequality scales with the rate, ρδ₀d_T(ω) ≥ ρδ_gmM, so the condition becomes ¼ρδ_gM ≥ κ₁, the lower bound M ≥ 4κ₁/(ρδ_g) on M, of the same kind as Bałaban's.
    {#W11.135-7} It also gives RG II's e^{−(1/3)δ₀M}e^{16κ₁} < 1 (p.16 l.7) with 16 standing for 2·6^d, a further lower bound on M of the same kind.

{#W11.136} *The Sects. D–E form (111).* At a background U₀ satisfying VAR (14), VAR's Sects. D–E represent the critical configurations through (111), A₁ + 𝔊J + 𝔊(δV/δA′)(A₁ + H₁B) = 0, with 𝔊 = G₁𝔓* the operator of PBG (3.148) (VAR p.294 l.20–28), and (112), 𝐇 = A₁ + H₁B − HD(A₁ + H₁B) (Proposition 5).
{#W11.136-3} VAR states that (143) "cannot replace Eq. (111)" (p.300 l.18–20); the two give the same 𝐇 at s = 1 when (143) has a unique solution in VAR's ball, but their walk-decoupled versions are different functions of s.
{#W11.136-4} §12 needs the (111) form for 𝐇″_k.
{#W11.136-5} The comparison runs as for 𝐀₀ and the current term above, with (A₁, 𝔊, H₁) in place of (𝐀₀, G̃, H₀):
- {#W11.137} G₁.
  {#W11.137-1} PBG (3.138) gives G₁ = Σ_nG₀((Δ′_π + Δ_π^{(2)})G₀)^n with G₀ = G_a, and (3.135) gives Δ_π^{(2)} = P_π*Δ^{(2)}P_π with P_π = 1 − DG′RD*.
  {#W11.137-2} The telescoping of *The form (c) for G̃ with the Δ^{(2)} term.* applies with Δ′_π + Δ_π^{(2)} in place of Δ^{(2)}.
  {#W11.137-3} Its defects are the polarised defect of Δ′_π (*The form (c) for VAR's H.*) and that of Δ_π^{(2)}.
  {#W11.137-4} The latter splits into the polarised defect of Δ^{(2)} (*The term G̃Δ^{(2)}H₀B.*) and the defect of P_π, P_π^Bℒ − ℒP_π^A = −D_Be − (D_BI′ − ℒD_A)ω^A, with e = ω^B − I′ω^A.
  {#W11.137-5} Its first part is the gradient entry of e of *The form (c) for VAR's H.*, which carries 𝔰^{β/(1+β)}, and its second is the D-intertwining of the smooth interpolation in the second bracket there, of relative size O(1)(ε/a_j)^β.
  {#W11.137-6} The derivatives in Δ′_π + Δ_π^{(2)} are moved onto the neighbouring G₀ factors as in PBG's estimate after (3.138) (p.423), through the entries ∇G and ∇G∇* of (3.42)–(3.44), the latter with the crude lattice Hölder bound at the exponent less 2β′, since the gain is the global δ_w attached to m(ω).
- {#W11.138} H₁ = G₁Q*(QG₁Q*)^{−1} (PBG (3.129)).
  {#W11.138-1} As for H, Q^Bℒ = Q^A puts one factor G₁^B − ℒG₁^Aℒ* in each term of H₁^B − ℒH₁^A.
- {#W11.139} 𝔊.
  {#W11.139-1} By PBG (3.153) (p.426 l.18–22), 𝔊 = G₁𝔓* = G₁ − G₁DRD*G₁ − G₁Q*(QG₁Q*)^{−1}QG₁.
  {#W11.139-2} The first and last terms are compared as G̃ is.
  {#W11.139-3} The middle term telescopes exactly into forms (c) for G₁ and ℒG₁^A(ℒ*D_BR^BD_B*ℒ − D_AR^AD_A*)G₁^Aℒ*, the global gauge-fixing defect in sandwich form.
  {#W11.139-4} That defect is not a per-shell defect of (Wδ-1).
  {#W11.139-5} With R = 1 − P, P := G′Q′*(Q′G′²Q′*)^{−1}Q′G′, its "1" part is ℒ*D_BD_B*ℒ − D_AD_A*.
  {#W11.139-6} Its P part reduces to the defects of G′, of (Q′G′²Q′*)^{−1}, and of Q′, through the walk expansions (3.90) and (3.98), whose constituents G′_□ and C_□ have the coarse-side defects of §4(d), 10.1, and 10.3, telescoped as in §7, and through the isometry ℒ′*ℒ′ = 1 of the scalar lift (§4(d)), which cancels the "1" of R on the scalar side.
  {#W11.139-7} In the sandwich form both parts are bounded with D moved onto the neighbouring G₁ factors, as for P_π: with f := D_B*ℒG₁^Aℒ*g and f′ := I′D_A*G₁^Aℒ*g, the difference f − f′ = (D_B*ℒ − I′D_A*)G₁^Aℒ*g contains no propagator difference; it is the D*-intertwining of the lift on the C^{1,β} field G₁^Aℒ*g, of relative size O(L)(ε/a_j)^β, as in the second bracket there.
  {#W11.139-8} The "1" part also needs ⟨I′φ, I′φ′⟩_B − ⟨φ, φ′⟩_A; I′ is not an isometry, but it is within O(ε/a_j) of ℒ′, which is, so this is O(ε/a_j) relative.
  {#W11.139-9} The forms (c) for G₁ of the telescoping carry 𝔡_H.
  {#W11.139-10} So the defect carries 𝔡_H.
- {#W11.140} The functional.
  {#W11.140-1} (111) uses VAR's V of (80) with Δ_π (VAR p.290 l.26–30), while §11's σ-identity is derived for V with Δ.
  {#W11.140-2} The difference V_π − V_Δ = ⟨A′, Δ′_πHD⟩ − ½⟨HD, Δ′_πHD⟩ has a gradient whose pairing with any slice direction 𝔓δA at a slice point A₁ + H₁B vanishes: every polarised Δ′_π term contains ω = G′RD* of a slice vector, which is 0.
  {#W11.140-3} So at s = 1 in each run (111) holds with V_Δ in place of V_π.
  {#W11.140-4} At complex s the decoupled 𝔊(s) and H₁(s) do not satisfy 𝔊(s) = G₁(s)𝔓*(s) or RD*H₁(s)B = 0, so the swap is not made there.
  {#W11.140-5} The decoupled (111) is Bałaban's, with V_π, in both runs.
  {#W11.140-6} Its σ is the σ of V_Δ plus the run difference of the gradient of V_π − V_Δ, ∇(V^B_π − V^B_Δ)(ℒA′) − ℒ∇(V^A_π − V^A_Δ)(A′).
  {#W11.140-7} That difference is the polarised defect of Δ′_π with the arguments A′ and HD(A′) and their derivatives in A′, so it is bounded as in *The form (c) for VAR's H.*, together with the forms (c) for H and for the D-identities of §11 for HD.
  {#W11.140-8} It carries 𝔡_H times O(1)L^β(1 + B₀)²(Mα₀ + C₀ε₁) relative to the size of the V terms, with the factor e^{16κ₁} at complex s, since every operator in it is walk-decoupled as in *Complex s.* The source 𝔊(s)∇(V_π − V_Δ) itself is common to the comparison and needs no bound of its own.
- {#W11.141} The fixed point.
  {#W11.141-1} Δ₁ := A₁^B − ℒA₁^A satisfies the identity of *The fixed point 𝐀₀.* with 𝔊 for G̃ and H₁ for H₀, plus the current term −(𝔊^B − ℒ𝔊^Aℒ*)J^B − ℒ𝔊^A(ℒ*J^B − J^A).
  {#W11.141-2} The contraction is VAR's for (111), with the size scaling of (185) and (98) as above, so the bounds of *The fixed point 𝐀₀.* and *The current term of VAR (143).* hold with these substitutions.
  {#W11.141-3} The term HD(A₁ + H₁B) of (112) is compared through §11's identities for D and the form (c) for H.
- {#W11.142} Complex s.
  {#W11.142-1} The walks of G₁ are those of its series (PBG p.423 l.30: "Replacing the operators in (3.138) by their random walk expansions").
  {#W11.142-2} Those of H₁ and 𝔊 add (QG₁Q*)^{−1}, expanded as in *Complex s.*, with the local inverses (QG_{1,□}Q*)^{−1}, and R through (3.90) and (3.98).
  {#W11.142-3} All are shared by the runs, so *Complex s.* applies.
{#W11.143} So 𝐇^B − ℒ𝐇^A for the (111) function carries 𝔡_H in its sup entries and 𝔡_H with the loss 2β′ in the exponent in its gradient entries (through the crude lattice Hölder bound on ∇G∇* in G₁), as for the (180) function, with the factor e^{16κ₁} at complex s.

{#W11.144} *The parts of σ.* G̃ = G − GQ*(QGQ*)^{−1}QG with G = (Δ_a − Δ^{(2)})^{−1} of VAR (180), Δ_a = Δ + DRD* + Q*aQ (VAR p.297 and p.300 l.4–11); the computation below writes G_a = Δ_a^{−1} for the identities G̃_aΔ_a = P₀ (VAR (131)) and G̃_aΔ = P₀ − G̃_aDRD*, the latter since G̃_aQ* = 0, and treats the Δ^{(2)} term separately.
{#W11.144-1} It contains the gauge-fixing term, so it acts on σ in every direction.
{#W11.144-2} σ is the gradient at A′^A of the right side of #W11.62, in every direction (#W11.63-1).
{#W11.144-3} It has two parts.
- {#W11.145} The terms that contain E: E = R₁ − Q₁(H^B − ℒH^A)C^B(A^B).
  {#W11.145-1} The propagator part is the form (c) with the bridge and carries 𝔡_H (*The form (c) for VAR's H.*).
  {#W11.145-2} R₁ carries the factor L^{−j} of the layer (*The size of the remainder terms.*).
- {#W11.146} The artifact T₃[b].
{#W11.147} There are no Landau parts, since 𝔉 is the action itself.

{#W11.148} *The middle layers and the choices.* Every use of PBG (3.42)–(3.44) on the 𝐑-operation's multiscale sets needs the width of 𝐁″_k's middle layers (PBG's cube class, p.396 l.14–17), which the LF note derives (its #4.317-0). The alignment covers 𝐁″_k on the young histories; the collar of 𝐁₁ is treated in §12.
{#W11.148-6} Two choices enter, made in both runs: the 𝒟′-cell sequences, with (3.35) on their 16-block cubes, and the Dirichlet local sequences in Proposition 2.7, which is Bałaban's statement (#W11.104-15), with the changes at the layer-0 cubes adjacent to the Dirichlet boundary derived at #W11.104-16–#W11.110-3 under R₀ > 5dL.

{#W11.149} (a) The E-terms.
{#W11.149-1} Write r := max(|A′^A|_{(−1)}, |∇A′^A|_{(−2)}) and ϑ := δ_w + ϑ_ℒ + C₂L² sup_xL^{−j(x)}.
{#W11.149-2} The propagator part of E carries 𝔡_H, by *The form (c) for VAR's H.*, so max(|E|_{(−1)}, |∇E|_{(−2)}) ≤ C_E𝔡_Hr² and dE has the bound C_E𝔡_Hr per unit direction, with C_E := O(1)B₀C₂(C_ℒ^g)²(1 + B₀)²(1 + C_𝔡)²(1 + Mα₀ + C₀ε₁), the factor 1 + Mα₀ + C₀ε₁ from the Δ′_π defect (the form (c) for the propagator part, applied to C^B(A^B) with |C^B(A^B)| ≤ 4C₂(C_ℒ^gr)² by VAR (55)) and the factor (1 + C_𝔡)² from R₁ (*The size of the remainder terms.*), which carries ϑ.
{#W11.149-3} Indeed the base 𝔡_H^{(1+β)/β} of 𝔡_H (#W11.101-4), and with it each of its terms, ϑ included, is ≤ (1 + C_𝔡)²𝔡_H: it is ≤ 𝔡_H if 𝔡_H ≤ 1, and ≤ C_𝔡^{1/β}𝔡_H ≤ (1 + C_𝔡)²𝔡_H otherwise, by 𝔡_H ≤ C_𝔡 (#W11.101-5) and 1/β ≤ 2.
{#W11.149-4} The E-terms of σ are the gradients at A′^A of V^A(A′ + E) − V^A(A′) and of T₃[P^A(A′ + E) − P^A(A′)].
{#W11.149-5} They are bounded in four groups.
- {#W11.150} V^A(A′ + E) − V^A(A′).
  {#W11.150-1} Its gradient is [∇V^A(A′ + E) − ∇V^A(A′)] + dE*∇V^A(A′ + E).
  {#W11.150-2} VAR (186)–(187) bound the second variation of V by O(1)C₄ times the size of the point, so the first part is ≤ O(1)C₄C_E𝔡_Hr³ in |·|_{(−3)}.
  {#W11.150-3} The adjoint dE* acts pointwise on (−3) objects as 𝔇*H* does in VAR (89)–(90), through the transpose of the form (c), which §3(c) states as a pointwise kernel bound per walk term, so the second part is ≤ O(1)B₀C₄C_E𝔡_Hr³.
- {#W11.151} The current terms of T₃[P^A(A′ + E) − P^A(A′)]: T₃⟨E, J^A⟩ and −⟨H^A(2C^{(2)A}(A′, E) + C^{(2)A}(E)), J^A⟩.
  {#W11.151-1} Their gradients are dE*J^A less its value at the quadratic part of E, and H^{A*}J^A paired with the derivatives of C^{(2)}, both pointwise as in VAR (85)–(86).
  {#W11.151-2} With |J^A| ≤ C₁B₃ε₁(L^jη)^{−3}, they are ≤ O(1)C₁B₃(1 + B₀C₂)C_Eε₁𝔡_Hr² in |·|_{(−3)}.
- {#W11.152} The divergence form.
  {#W11.152-1} By PBG (3.10) (p.392), Δ^A = D_A*(1 + c)D_A + 𝒦.
  {#W11.152-2} Here c := Re U(∂p) − 1 on the plaquettes, matrix-valued inside the trace, the quadratic coefficient of tr((DA)(p))² in PBG (3.7) less 1, so |c| ≤ O(1)ε⁴|F|² ≤ O(1)(C₀ε₁)².
  {#W11.152-3} It comes from the first part of Δ′ (with D¹_U in place of D; the η^{−2} of (3.10) goes with D¹_U).
  {#W11.152-4} D¹_U and D_U differ by transports, and the difference gives the first-order terms D_A*c(D¹_U − D_U) and (D¹_U − D_U)*cD_A, whose zeroth-order factors c(D¹_U − D_U) are of size O(ε|F|) times the coefficients: a divergence of a zeroth-order term, which goes into K, and a zeroth-order term applied to D_A, which goes into the source s below.
  {#W11.152-5} PBG states (3.7)–(3.10) for configurations "with values in a compact Lie group G ⊂ U(N)" (p.389 l.12; CMP 98 p.18 l.22: "a Lie subgroup G of a unitary group U(N)"), with tr and Re U(∂p) taken in that embedding.
  {#W11.152-6} Every compact Lie group has such an embedding by the Peter–Weyl theorem, so they hold for every compact G. 𝒦 comes from its commutator part, is of order zero, and has |𝒦| ≤ O(1)|F|.
  {#W11.152-7} So K below always includes the factor 1 + c.
  {#W11.152-8} PBG (3.42) and (3.44) bound G̃^A on localised sup-norm or Hölder sources, not columns of G̃^A, so the source dE*D_A*K is written as a run-A divergence ∇_A*f of a sup-bounded field plus a sup-bounded source s, and those entries are applied to f and s.
  {#W11.152-9} From E = R₁ − Q₁(H^B − ℒH^A)C^B(A^B), with R₁ = (1 − H^AQ̂^A)ε^{−1}C^B_1(εA^B) and A^B = ℒA′ − H^BD^B(ℒA′), dE = 𝒮m𝒯 for each part.
  {#W11.152-10} Here 𝒯 := (1 − H^BdD^B)ℒ, m := dC^B at A^B (for R₁, m := ε^{−1}dC^B_1 at εA^B), and 𝒮 := −Q₁(H^B − ℒH^A), −H^AQ̂^A, or the 1 of R₁.
  {#W11.152-11} So dE*D_A*K = 𝒯*m*(D_A𝒮)*K, and the factors are bounded as follows.
  - {#W11.153} The smoothing parts of 𝒮.
    {#W11.153-1} Q₁(H^B − ℒH^A) and H^AQ̂^A act on coarse data.
    {#W11.153-2} A datum on a block of the layer j is a localised source of sup 1, and the data pair with the block volume (L^jε)^d, so the bounds for localised sources give the transpose pointwise with no loss of volume.
    {#W11.153-3} For H^AQ̂^A, (3.133) gives |(D_AH^A)*K| ≤ O(1)B₀a_j^{−1}Σe^{−δ₀d}|K|, and Q̂^{A*} spreads block data over the block.
    {#W11.153-4} For Q₁(H^B − ℒH^A), the gradient entry of the form (c) with the bridge, together with |D_AQ₁g| ≤ O(1)(|∇_Bg| + c_uMα₀a_j^{−1}|g|) over the two stencils, gives the same with the factor δ_w + ϑ_ℒ (§3(c) states the form (c) per walk term for localised sources).
    {#W11.153-5} So (D_A𝒮)*K is a sup-bounded function, with no divergence left.
  - {#W11.154} The local part, the 1 of R₁.
    {#W11.154-1} Here 𝒮*D_A*K = D_A*K stays a divergence. m = ε^{−1}dC^B_1(εA^B) averages the fine field over the stencil of each coarse bond, with coefficients of size O(1)C₂ε|A^B| (VAR (44), and Cauchy's estimate on its disc).
    {#W11.154-2} So D_Am = m′D_B + n, with m′ the same averages of the fine differences and n of the size of the coefficients' differences, O(1)C₂ε|∇A^B|.
    {#W11.154-3} Hence m*D_A*K = D_B*(m′*K) + n*K, with |m′*K| ≤ O(1)C₂ε|A^B||K| and |n*K| ≤ O(1)C₂ε|∇A^B||K|.
    {#W11.154-4} Both carry ε/a_j against a_j|A^B| and a_j²|∇A^B|, and that is the factor L^{−j} of R₁.
  - {#W11.155} m* on the sup parts. dC^B_j averages over a block of size L^jη_B with coefficients O(1)C₂L^jη_B|A^B| (VAR (44)), so |m*g| ≤ O(1)C₂C_ℒ^gr|g| pointwise at the layer of the point.
    {#W11.155-1} For R₁, m = ε^{−1}dC^B_1 has the coefficients O(1)C₂ε|A^B| ≤ O(1)C₂(ε/a_j)C_ℒ^gr, and that factor ε/a_j, at most the term L sup_x(ε/a_{j(x)})^β of the base of 𝔡_H and so ≤ (1 + C_𝔡)²𝔡_H (#W11.149-3), gives the part −H^AQ̂^A of s its factor 𝔡_H.
  - {#W11.156} 𝒯* = ℒ*(1 − (dD^B)*H^{B*}).
    {#W11.156-1} On a sup source, ℒ* and H^{B*} are sup-bounded with decay (*The global lift.*, and (3.133) for H^B on data as above), and |dD^B| ≤ O(1)C₂C_ℒ^gr by the Cauchy estimate behind RG II (1.14).
    {#W11.156-2} On the divergence D_B*g of the local part, D_Bℒ = 𝒞∇_A + 𝒩.
    {#W11.156-3} The coefficients 𝒞 are O(1)L with the decay e^{−δ_Qd}, and |𝒩| ≤ O(1)c_Gc_uMα₀a_j^{−1}, since D_Bℒ vanishes on constant fields at U^B = 1 (the conversion bullet of (b) below).
    {#W11.156-4} So ℒ*D_B*g = ∇_A*(𝒞*g) + 𝒩*g.
    {#W11.156-5} The term (dD^B)*(D_BH^B)*g is sup-bounded by (3.133) as above, with the factor a_j^{−1}.
  {#W11.157} So dE*D_A*K = ∇_A*f + s with |f| ≤ O(1)L C₂(ε/a_j)r|K| and |s| ≤ O(1)C_E𝔡_Hra_j^{−1}Σe^{−½min(δ₀,δ_Q)d}|K|, at the layers of the points, with the layer crossings as in *The data bound.* of §11.
  {#W11.157-1} The entries G∇* and G of PBG (3.42), at B₀e^{16κ₁} for G̃^A(s) (RG II p.5 l.15–16), then give |G̃^AdE*D_A*K|_{(−1)} ≤ O(1)e^{16κ₁}B₀LC_E𝔡_Hr|K|_{(−2)}.
  {#W11.157-2} The gradient entry applies (3.44) to f, ∇G∇*, with the crude lattice Hölder bound below, ‖f‖^{ξ′}_{β′} ≤ 3L^{j′β′}sup|f|, and the entry ∇G of (3.42) to s.
  {#W11.157-3} So it holds with the exponent lowered by 2β′, as in #W11.160-8.
  {#W11.157-4} No second differences of E enter.
- {#W11.158} The quartic term ½⟨E, Δ^AE⟩.
  {#W11.158-1} Its gradient is dE*Δ^AE = dE*D_A*((1 + c)D_AE) + dE*𝒦E, by PBG (3.10) (#W11.152-1).
  {#W11.158-2} The first is the divergence form with K := (1 + c)D_AE, |K|_{(−2)} ≤ O(1)C_E𝔡_Hr² by (a)'s bound on E and |c| ≤ 1, so G̃^A of it is ≤ O(1)e^{16κ₁}B₀LC_E²𝔡_H²r³ in |·|_{(−1)} (#W11.157-1).
  {#W11.158-3} The second is pointwise: |𝒦| ≤ O(1)|F| ≤ O(1)C₀ε₁a_j^{−2} by (9.2) and |E|_{(−1)} ≤ C_E𝔡_Hr², so with the factor C_E𝔡_Hr of dE* it is ≤ O(1)C₀ε₁C_E²𝔡_H²r³ in |·|_{(−3)}.
- {#W11.159} The cubic term ⟨A′, Δ^AE⟩.
  {#W11.159-1} Its gradient is Δ^AE + dE*Δ^AA′.
  {#W11.159-2} The second is dE*D_A*((1 + c)D_AA′^A) + dE*𝒦A′^A, the divergence form with K := (1 + c)D_AA′^A, |K|_{(−2)} ≤ 2r by the definition of r, so G̃^A of it is ≤ O(1)e^{16κ₁}B₀LC_E𝔡_Hr² in |·|_{(−1)} (#W11.157-1), plus a pointwise term ≤ O(1)C₀ε₁C_E𝔡_Hr² in |·|_{(−3)}.
  {#W11.159-3} No bound of Δ^AA′^A itself is used.
  {#W11.159-4} The term Δ^AE has no pointwise bound with a small factor.
  {#W11.159-5} It enters Δ₀ only through ℒG̃^A, and G̃^AΔ^A is explicit.
  {#W11.159-6} With G = Δ_a^{−1}, Δ_a = Δ + DRD* + Q*aQ, G̃Q* = GQ* − GQ*(QGQ*)^{−1}QGQ* = 0 and G̃G^{−1} = 1 − GQ*(QGQ*)^{−1}Q = P₀ (VAR (131)).
  {#W11.159-7} Hence G̃^AΔ^AE = P₀^AE − G̃^AD_AR^AD_A*E.
  {#W11.159-8} With the G = (Δ_a − Δ^{(2)})^{−1} of (180), the further term G̃^AΔ^{(2)A}E appears, bounded by PBG (3.137) as a small perturbation.
  {#W11.159-9} P₀^AE ≤ (1 + B₀)|E| in |·|_{(−1)}, and likewise for its gradient in |∇·|_{(−2)} by VAR (46). |R^AD_A*E| ≤ O(1)|∇E| carries 𝔡_H, with no gauge condition on A′^A or on H^A(s) (at complex s, R^AD_A*H^A(s) = 0 is not available).
  {#W11.159-10} By the entries GD of PBG (3.42) (D in place of ∇*, p.398 l.49–50), |G̃^AD_AR^AD_A*E|_{(−1)} ≤ O(1)B₀C_E𝔡_Hr².
{#W11.160} So every E-term of ℒG̃^Aσ carries 𝔡_H in |·|_{(−1)}.
{#W11.160-1} In |∇·|_{(−2)} the same holds for all but ∇G̃^AD_AR^AD_A*E and the gradient entries of the divergence forms, which are treated alike.
{#W11.160-2} The gradient entry ∇GD is bounded as in PBG (3.44) (D in place of ∇*), through ‖w‖^{ξ′}_{β′} + |w|, for any β′ ∈ (0, 1], with the constant B₀′(β′) and w := R^AD_A*E on the block of y′ in the layer j′, ξ′ = L^{−j′}.
{#W11.160-3} The norm ‖·‖^{ξ′}_{β′} of (3.40) measures distances on the ξ′-lattice, where two distinct points are at least ξ′ apart.
{#W11.160-4} So, crudely, ‖w‖^{ξ′}_{β′} ≤ 3ξ′^{−β′}sup|w| = 3L^{j′β′}sup|w|, with |R(U(Γ))| ≤ 2 at complex backgrounds in PBG's domain (3.37) with α₁ small.
{#W11.160-5} No regularity of E beyond |∇E|_{(−2)} enters.
{#W11.160-6} Hence |∇G̃^AD_AR^AD_A*E|_{(−2)} ≤ O(1)B₀′(β′)B₀C_E sup_{j′}L^{j′β′}·𝔡_Hr², with 𝔡_H built from global suprema (#W11.101-3).
{#W11.160-7} 𝔡_H ≤ C_𝔡L^{−γ_Hj_min} (#W11.101-5), with j_min ≥ k/2 − 1 on the young histories (*The alignment of the global sets.*), while j′ ≤ k.
{#W11.160-8} So L^{j′β′} ≤ L^{2β′}L^{2j_minβ′}, and L^{j′β′}𝔡_H ≤ C_𝔡L^{2β′}L^{−(γ_H−2β′)j_min}.
{#W11.160-9} Any β′ ∈ (0, γ_H/2) leaves a positive exponent, at the cost of B₀′(β′), finite for β′ > 0.
{#W11.160-10} So the E-terms of Δ₀ carry 𝔡_H, with the exponent γ_H − 2β′ in place of γ_H for this one gradient term, β′ > 0 arbitrary, as §8 uses it (#W8.24-1).


{#W11.161} (b) The artifact (bounded in *The artifact through covariances.* below).
{#W11.161-1} The blocking-artifact term is b beyond its second order.
{#W11.161-2} It is local: by the column-sum property of (9.11), the Cauchy note writes b, as an identity in W, as the sum over the coarse plaquettes p of the cell functions ε⁴[½|Φ_p|² − ½Σ_{p′}w_{p,p′}|F_{p′}|² + κ_ε(Φ_p) − Σ_{p′}w_{p,p′}κ_η(F_{p′})] (its *The Second Variation of b.*, with Φ_p = F^w_p + εr_p, the κ_η terms distributed by Σ_pw_{p,p′} = η⁴/ε⁴ at d = 4), each analytic on the cell domain 𝒫 of its *Analyticity.*, so every derivative of b is a sum of terms supported on single cells, and the derivatives of b(e^{iη_BA^B(ℒA′)}U^B) in A′ carry the decay of H^B and D^B.
{#W11.161-12} The comparator is VAR (97)–(98), |δV/δA′|_{(−3)} ≤ C₄max(|A′|_{(−1)}, |∇A′|_{(−2)})².
{#W11.161-13} Relative to it the artifact carries the factor ϑ_b of (#W11.177), which comes from the covariance structure of b, as in the Cauchy note's *The Second Variation of b.*, one order higher.

{#W11.162} *The artifact through covariances.* Notation as in the Cauchy note's #C10.4.24–#C10.4.59, at the run-B configurations W = e^{iη𝒜}U^B, η = η_B, in the axial gauge of its *Analyticity.* on each cell.
{#W11.162-1} The ingredients are as follows.
- {#W11.163} The identity.
  {#W11.163-1} Let X_{p′} := TF_{p′} with T := Ad(W(γ_{p′})), so that F^w_p = Σ_{p′}w_{p,p′}X_{p′} and Φ_p = F^w_p + ρ_p with ρ_p := εr_p.
  {#W11.163-2} The invariant bilinear form satisfies ⟨TX, TY⟩ = ⟨X, Y⟩ for complex W as well.
  {#W11.163-3} With Var_p(X) := Cov_p(X, X), as an identity in W on 𝒫,

  {#W11.164} ½⟨Φ_p, Φ_p⟩ − ½Σ_{p′}w_{p,p′}⟨F_{p′}, F_{p′}⟩ = −½Var_p(X) + ⟨F^w_p, ρ_p⟩ + ½⟨ρ_p, ρ_p⟩.

  {#W11.165} So b = Σ_pε⁴[−½Var_p(X) + ⟨F^w_p, ρ_p⟩ + ½⟨ρ_p, ρ_p⟩] + Σ_pε⁴κ_ε(Φ_p) − Σ_{p′}η⁴κ_η(F_{p′}).
- {#W11.166} The Taylor formula.
  {#W11.166-1} Let β(𝒜) := b(e^{iη𝒜}U^B) and 𝔅 := β∘A^B, with A^B(A′) = ℒA′ − H^BD^B(ℒA′).
  {#W11.166-2} For an analytic function, the gradient of its Taylor remainder of order three is d(T₃𝔅)(x)[ξ] = ∫₀¹(1 − t)d³𝔅(tx)[x, x, ξ]dt.
  {#W11.166-3} So ⟨σ_b, ξ⟩ is this integral at x = A′^A.
  {#W11.166-4} By the chain rule, d³𝔅[x, x, ξ] = d³β[u, u, Ξ] + d²β[ü, Ξ] + 2d²β[u, Ξ̇] + dβ[Ξ̈].
  {#W11.166-5} Here u := dA^B[x], Ξ := dA^B[ξ], ü := d²A^B[x, x], Ξ̇ := d²A^B[x, ξ], and Ξ̈ := d³A^B[x, x, ξ].
  {#W11.166-6} Since D is of order ≥ 2, ü, Ξ̇, and Ξ̈ are H^B applied to derivatives of D^B, bounded by VAR (73) and Cauchy's estimate on the disc of (51).
  {#W11.166-7} Every configuration e^{iηA^B(tx)}U^B lies in 𝒫, since η|A^B| ≤ O(1)C_ℒ^gB₅ε₁L^{−j−1} ≤ r_G/2.
- {#W11.167} The variations of Var. d³Var_p[u, u, v] = 2Cov_p(X″_{uu}, X′_v) + 4Cov_p(X″_{uv}, X′_u) + 2Cov_p(X, X‴_{uuv}), d²Var_p[u, v] = 2Cov_p(X′_u, X′_v) + 2Cov_p(X, X″_{uv}), and dVar_p[v] = 2Cov_p(X, X′_v).
  {#W11.167-1} The primes denote the variations of X in the indicated directions. |Cov_p(Y, Z)| ≤ osc_pY·osc_pZ.
  {#W11.167-2} When Z is linear in the direction v, Cov_p(Y, Z) = Σ_{p′}w_{p,p′}⟨Y_{p′} − Σ_{q′}w_{p,q′}Y_{q′}, Z_{p′}⟩ is a linear functional of Z on the cell with coefficients bounded by osc_pY.
- {#W11.168} The sizes.
  {#W11.168-1} In the cell variable ζ = η𝒜, Cauchy's estimate on 𝒫 gives |d³(η²F_{p′})| ≤ k₃ with k₃ := O(1)m_G/r_G³, so |X‴_{uuv}| ≤ k₃η|u|²|v|, with the transport terms of the Cauchy note's #C10.4.48. |X″_{uv}| ≤ k₂|u||v| plus transport terms with the factor |a| ≤ 4dε|u|.
  {#W11.168-2} X′_v = Tf_v + i[a_v, TF], with f_v the fine curl of v up to the factor dlog_h (the Cauchy note's #C10.4.47) and |a_v| ≤ 4dε|v|.
  {#W11.168-3} At a point of the layer j, |u| ≤ C_ℒ^gra_j^{−1} and |∇u| ≤ C_ℒ^gra_j^{−2} by (H_ℒ^g), with r := max(|A′^A|_{(−1)}, |∇A′^A|_{(−2)}). |F| ≤ O(1)(C₀ε₁ + C_ℒ^gr)a_j^{−2}.
  {#W11.168-4} The oscillation of F at complex W is bounded in *The oscillations.* below, with the factor (ε/a_j)^{β_H}.
- {#W11.169} The oscillations. osc_pX ≤ 4dε|∇F| + 4δ_T|F| (the Cauchy note's #C10.4.50). osc_pu ≤ 4dε|∇u| + δ_T|u| (*The Variations of r_p.*).
  {#W11.169-1} For the direction, v − v_c with v_c the axial-gauge value at y_p is a linear function of the differences of v on the cell, |v − v_c| ≤ 4dε|∇v| + δ_T|v|.
  {#W11.170} These bounds of the Cauchy note are proved at the real W = U^B.
  {#W11.170-1} At the complex W = e^{iηA^B(tx)}U^B of the Taylor formula they are rerun as follows.
  {#W11.170-2} The plaquettes of W are those of U^B changed by the covariant curl of ηA^B plus BCH terms, so F(W) = F(U^B) + D_{U^B}∧A^B + O(|A^B|²) + O(η|F||A^B|), with |A^B| ≤ C_ℒ^gra_j^{−1}, |∇A^B| ≤ C_ℒ^gra_j^{−2}, and the Hölder entry of ∇A^B at the exponent β_H by (3.133) for the H-fields and (3.43) for the G̃-fields, carried through ℒ by the Cauchy note's *Regularity of the Lifts.* (#C10.4.109–#C10.4.110).
  {#W11.170-3} So osc_pF(W) ≤ 4dε|∇F(U^B)| + O(1)(6ε)^{β_H}ra_j^{−2−β_H} + O(1)εr²a_j^{−3} + O(1)C_ℒ^g(η/a_j)r|F|, the last from twice the supremum of the term O(η|F||A^B|), which carries the factor (ε/a_j)^{β_H} against |F| ≤ O(1)(C₀ε₁ + r)a_j^{−2}.
  {#W11.170-4} The transports of W along the cell's paths differ from those of U^B by O(1)ε|A^B| ≤ O(1)C_ℒ^gr(ε/a_j), so δ_T(W) ≤ δ_T + O(1)C_ℒ^gr(ε/a_j).
  {#W11.170-5} *The Variations of r_p.* use only these plaquette and transport bounds.
  {#W11.170-6} So the three oscillation bounds hold at the complex W with |F|, |∇F| ε, and δ_T replaced by these, and every oscillation factor below carries (ε/a_j)^{β_H}, as ϑ_b requires, under r ≤ r_G/2 for the cell domain 𝒫.
{#W11.171} Each term of d³β[u, u, Ξ] is then bounded with one explicit factor ε or η, relative to the comparator's size r²a_j^{−3} for a source and r²a_j^{−2} for a coefficient of ∇Ξ:
- {#W11.172} Cov_p(X, X‴_{uuΞ}) ≤ (4dε|∇F| + 4δ_T|F|)k₃η|u|²|Ξ|, a source with the relative factor O(1)k₃(ε/a_j)(η/a_j)(C₀ε₁ + L²C_ℒ^gr)(C_ℒ^g)² ≤ O(1)k₃L(1 + C₀ε₁)(C_ℒ^g)²(ε/a_j), by η/a_j = L^{−j−1} and C_ℒ^gr ≤ O(1)C_ℒ^gB₅ε₁ ≤ ε₃ (#W11.63-1);
- {#W11.173} Cov_p(X″_{uΞ}, X′_u) ≤ 2|X′_u|·[k₂(osc_pu|Ξ| + |u||Ξ − Ξ_c|) + transport terms].
  {#W11.173-1} The part with osc_pu is a source with the relative factor O(1)k₂(C_ℒ^g)²ε/a_j.
  {#W11.173-2} The part with Ξ − Ξ_c is a linear functional of the differences of Ξ, with coefficient O(1)k₂(C_ℒ^g)²εr²a_j^{−3}, the relative factor ε/a_j;
- {#W11.174} Cov_p(X″_{uu}, X′_Ξ) has coefficients osc_pX″_{uu} ≤ 2k₂osc_pu|u| + O(1)c_{br}ε|u||∇u| on the fine curls of Ξ, so the relative factor is O(1)(k₂ + c_{br})(C_ℒ^g)²ε/a_j.
  {#W11.174-1} The term i[a_Ξ, TF] is a source with the factor 4dε|F|.
{#W11.175} The ρ-terms are bounded by *The Variations of r_p.* and the third variation of εr_p by Cauchy's estimate (≤ k₃η|u|²|Ξ|), each paired with |F^w| ≤ |F| or with a variation carrying ε|F|, δ_T, or an oscillation, hence the relative factor O(1)(k₂ + k₃ + c_{r1} + c_{r3})(ε/a_j).
{#W11.175-1} The κ-terms carry ε⁴|Φ|·|dΦ|² and smaller, by |d^iκ| ≤ c_κη⁴|X|^{4−i} and Cauchy's estimate for i = 3, so the relative factor is O(1)c_κ(ε/a_j)⁴.
{#W11.175-2} The chain-rule terms d²β[ü, Ξ], 2d²β[u, Ξ̇], and dβ[Ξ̈] have the second and first variations of b, which are covariances with one oscillation factor each (the Cauchy note's #C10.4.43–#C10.4.59, with osc_pX′_{ü} ≤ 2ω + k_oν_F|∇ü| and the Hölder bound of the H-outputs ü and Ξ̇ by PBG (3.133), the entry ‖ζ∇H‖_β, and osc X for Ξ̈), times B₀(β_H)(C₂ + C₃)r from D (C₃ from d³D₃).
{#W11.175-3} So their relative factor is O(1)B₀(β_H)(C₂ + C₃)(ε/a_j)^{β_H}, with β_H < 1 the Hölder exponent used for H.

{#W11.176} The conversion to run A. Ξ = ℒξ − H^BdD^B[ℒξ].
{#W11.176-1} The H^B part is a source in ξ by PBG (3.133) for ∇H.
{#W11.176-2} For the ℒ part, the map ξ ↦ (D_Bℒξ, ℒξ − (ℒξ)_c) on a cell vanishes, at U^B = 1, on fields constant on all of run A's lattice, and on fields constant only near the cell up to the decaying tails of (Q₁Q₁*)^{−1}: for constant ξ, Iξ is constant, Q₁I reproduces it (the Cauchy note's #C10.4.108-2), and the correction h = (Q₁Q₁*)^{−1}(ξ − Q₁Iξ) receives only the differences of ξ.
{#W11.176-3} So it is a combination of run A's differences ∇_Aξ, with coefficients O(1)L summed with the decay e^{−δ_Qd} of (Q₁Q₁*)^{−1}, plus a source O(1)c_Gc_uMα₀a_j^{−1}|ξ| from the background, as in (H_ℒ^g).
{#W11.176-4} Hence σ_b = ∇_A*K_b + s_b on run A's lattice, with

  {#W11.177} |K_b|_{(−2)} + |s_b|_{(−3)} ≤ C_bϑ_br², ϑ_b := sup_x(ε/a_{j(x)})^{β_H}, C_b := O(1)LC_Q′(C_ℒ^g)²(1 + C₀ε₁)(1 + k₂ + k₃ + c_{br} + c_{r1} + c_{r3} + c_κ)²(1 + B₀(β_H)(C₂ + C₃)),

{#W11.178} pointwise with the factor of the source layer.
{#W11.178-1} By PBG (3.42) for the entries G∇* and G (and the term GQ*(QGQ*)^{−1}QG of G̃ likewise), |G̃^Aσ_b|_{(−1)} ≤ O(1)B₀C_bϑ_br².
{#W11.178-2} By PBG (3.44) with the crude lattice Hölder bound of (a), |∇G̃^Aσ_b|_{(−2)} ≤ O(1)B₀′(β′)C_b sup_{j′}(L^{j′β′}ϑ_{b,j′})r², for any β′ ∈ (0, β_H).
{#W11.178-3} With (H_ℒ^g) for ℒ, the artifact part of 2|ℒG̃^Aσ| is at most O(1)C_ℒ^gB₀′(β′)C_b sup_{j′}(ε/a_{j′})^{β_H−β′}r², the supremum over the source layers.
{#W11.178-4} Here the layer-local factor is available: the cell functions and the Hölder bound of the H-outputs are local in the target block. β_H < 1 is arbitrary in PBG (3.43), with the constant B₀(β_H).
{#W11.178-5} So (b) holds with the exponent β_H − β′.

{#W11.179} *The alignment of the global sets.* The consumer evaluates (W-δ) on the young histories of the Cauchy note's §6.2.
{#W11.179-1} Every component of a young pair is born at a scale > k/2 (the Cauchy note's #C6.2.12-2), so the finest layer of the 𝐑-operation's set is at a scale n ≥ k/2 − 1 of run A, and n ≥ 1 for k ≥ 4 (derived in the LF note's §1, *The configurations.*, "every layer of X lies at a scale ≥ j₀ − 1 ≥ k/2 − 1", and used in its *The joins* and *The lifts and the chain rule.*; none of these uses (W-δ)).
{#W11.179-2} By §2, the layers are unions of cells of ML^jεℤ^d = ML^{j+1}(ε/L)ℤ^d, the same physical sets in both runs.
{#W11.179-3} Hence Ω^A_j = Ω^B_{j+1} for every j ≥ 0, and Ω^B_0 = Ω^B_1 = Ω^A_0 is the domain of the problem.
{#W11.179-4} The finest data sets are empty: Λ^A_0 = Λ^B_0 = Λ^B_1 = ∅.
{#W11.179-5} In the all-small-field problem of the Cauchy note's §9.2 the same holds with the single data set Λ^B_{k+1} = Λ^A_k = T_a.
{#W11.179-6} So the composition of the averagings, and with it the identities for D, for the linear coordinates, and for V, hold on all of run A's data sets of the 𝐑-operation's set 𝐁″_k on the young histories.
{#W11.179-7} They do not hold on the collar of 𝐁₁, whose layers reach the finest scale (§12).

{#W11.180} (2) R₁ outside (Wδ-3).
{#W11.180-1} The LF note's (δ) compares the configurations ι_X(e^{iη𝐇^A(s)}c^A) and e^{iη𝐇^B(s)}ι_Yc^A themselves, so it contains R₁ and the D difference as they stand (its piece (δ) of (ii)).
{#W11.180-2} Both carry the factor L^{−j(x)} ≤ L^{1−k/2} of *The size of the remainder terms.* on the young histories, so neither needs matching against ι_X's kernel.

{#W11.181} §11 is not circular: it uses neither (W-δ) nor the LF note's (δ), and that note's piece (δ) of (ii) cites §11 for the size of R₁, not conversely.

## 12. The Localisation Functions of (1.61)–(1.64) {#WS12}

{#W12.1} The LF note's piece (β) (its #4.241) is the run difference of the functions of the localisation expansions of LFR II (1.61)–(1.64) and of the gauge transformations in them.
{#W12.1-1} This section reduces it to (W-δ) at three problems, and derives the gauge part.

{#W12.2} *The three functions (quoted).*
- {#W12.3} 𝐇″_k, the function of the problem of 𝐁″_k about U_{1,2}, from VAR's Sects. D–E (LFR II (1.54), p.370 l.40–42).
  {#W12.3-2} It enters (1.61) restricted to Y_1 and is localised with the cubes σ̃₀ disjoint from Λ (p.373 l.31–34).
- {#W12.4} 𝐇_{𝐁₁}(−(1/i)log M^·(U_{k,Λ})⌈_{Z″_k}), the function of the problem of 𝐁₁ in the representation (1.62) of U_1 about U_{k,Λ} (p.374 l.3–6), localised with σ̃₀ (l.8–10).
- {#W12.5} 𝐇_k(−(1/i)log V′_k⌈_Λ) of (1.63)–(1.64), the function of the problem of 𝐁_k about U_k, localised with σ̃₀ (p.374 l.26–29).
{#W12.6} Each is a function of its own problem: the operators of that problem's determining set at its background (H, H₀, and G̃ for the (180) form; H, H₁, and 𝔊 for the (111) form) and the fixed points.
{#W12.6-1} Its localisation substitutes walk-decoupled propagators into the functionals of the fixed points, as in RG II (1.5), and Bałaban writes each expansion "in the form of the expansion (6.10) [I]" (p.373 l.33, p.374 l.10 and l.28).
{#W12.6-2} The representations (1.54), (1.57), and (1.58) (p.370 l.40–42, p.371 l.36–47) have the form (exp iη𝐇U)^{u^{−1}}.
{#W12.6-3} For (1.58) this is VAR's representation of the minimiser about a minimiser (VAR (172) and (179), p.305–306).
{#W12.6-4} For (1.54) it is the Sects. D–E representation (112) about a background satisfying VAR (14).
{#W12.6-6} The factor u^{−1} is LFR's; VAR writes these in the Landau gauge without it.
{#W12.6-7} Their fixed points are as follows.
- {#W12.7} 𝐇_k is VAR's Sect. G function of the 𝐁_k problem about its minimiser U_k, with (179)–(180).
- {#W12.8} 𝐇″_k is introduced by "From the results of Sects. D, E [15] we obtain" (p.370 l.40).
  {#W12.8-2} Its background U_{1,2} is a patch of the minimisers of the 𝐁₁ and 𝐁₂ problems and is not critical for 𝐁″_k.
  {#W12.8-3} Bałaban prints the function with the current as an argument, 𝐇″_k(𝐆″_kJ_{1,2}, …) (p.370 l.41), and localises 𝐆″_kJ_{1,2} through 𝐆″_kQ*_{𝐁″_k} = 0 and the criticality of J_{1,2} = J_1 on Ω″^∼_{h+1} for 𝐁₁ (p.370 l.45–52, p.371 l.1–25).
  {#W12.8-4} The arguments 𝐆″_kJ_{1,2} and H″_{1,k}Q̃(η𝐀₀) are those of VAR (111)–(112), with 𝐆″_k the 𝔊 of PBG (3.148) (p.370 l.49) and H″_{1,k} VAR's H₁.
  {#W12.8-5} So 𝐇″_k is the (111) function at the background U_{1,2} with J = J_{1,2}, compared by §11's *The Sects. D–E form (111).* By (1.55), 𝐆″_kJ_{1,2} = 𝐆″_k(1 − θ)Q*_{𝐁₁}θ₁H*_{𝐁₁}J₁ + 𝐆″_kθJ_{1,2} (p.371 l.20–22), so the localised 𝐇″_k contains H_{𝐁₁}, an operator of the 𝐁₁ problem (*The source of (1.55).* below).
- {#W12.9} 𝐇_{𝐁₁} expands U_1, the minimiser of the 𝐁₁ problem on Ω″^∼_{h+1}, about U_{k,Λ}, the minimiser of the 𝐁_k problem.
  {#W12.9-1} Its current J(U_{k,Λ}) need not satisfy P₀*(𝐁₁)J = 0; neither Bałaban nor this note shows that it does.
  {#W12.9-2} Bałaban prints no operator form at (1.57).
  {#W12.9-3} It is taken here in the (111) form, as 𝐇″_k is printed; this is a choice of representation, by analogy with (1.54), and (111) and (143) give the same function at s = 1 by VAR's uniqueness (p.300 l.18).
{#W12.10} §11 covers 𝐇_k by *The fixed point 𝐀₀.* (J = 0) and the other two by *The Sects. D–E form (111).* The gauge transformation u^0_k is given by CMP 98 (106) as an analytic function of 𝐇″_k restricted to one block (p.373 l.29–30), and u_1 by "The same remarks" (p.373 l.44–p.374 l.2).
{#W12.10-2} For u_{k,Λ}, Bałaban introduces the decoupling variables into the localised 𝐇_k of (1.63), "hence into u_{k,Λ}" (p.374 l.38–39), and (106) is used for it in the same way.
{#W12.10-3} (106) is printed for a single domain; its layered form is Bałaban's usage at p.373 l.29–30.

{#W12.11} *What §§3–11 use of the problem.* §§3–11 use the determining set and the background through five inputs:
- {#W12.12} the alignment Ω^A_j = Ω^B_{j+1} with empty finest data sets (§11, *The alignment of the global sets.*);
- {#W12.13} a real background pair (U^B, V₀ := MU^B) with U^B := ι(V₀) satisfying PBG (3.35)–(3.36) on run B's shells and the tail of the Cauchy note's §9.8 (10.5, *The base and the local gauge.*);
- {#W12.14} PBG's and VAR's bounds for the problem's operators at that background, by PBG Corollary 3.6, which assumes (2.1)–(2.4) of PRT2 for the sequence of domains (PBG p.408 l.2), layer widths included;
- {#W12.15} the fixed-point equation: VAR (180) for 𝐇_k, and VAR (111) with the background's current for 𝐇″_k and 𝐇_{𝐁₁} (§11, *The current term of VAR (143).* and *The Sects. D–E form (111).*);
- {#W12.16} for the localised operators, the boundaries of the localisation domains, which §4 treats without boundary terms given (S).
{#W12.17} They hold for the three problems as follows.
- {#W12.18} The alignment. 𝐁″_k and 𝐁_k have every layer at a shared scale ≥ 1 in a young history (the LF note's *The configurations.* and *The lifts and the chain rule.*). 𝐁₁ = 𝐁″_k ∪ 𝐁_h(Ω″^∼_{h+1}) adds the collar 𝐁_h(Ω), Ω := Ω″^∼_{h+1}.
  {#W12.18-1} CRE builds it on T_ξ, ξ = L^{−h}, the lattice of the layer h in that layer's units (CRE p.256 l.21–23 and l.57–62), with domains Ω = Ω_0 ⊃ … ⊃ Ω_h, Ω_n a union of L^nξM₁-cubes.
  {#W12.18-2} So its layers n = 0, …, h run from the finest scale at ∂Ω to the scale h, all within 2M₁ of ∂Ω, as the LF note's *The layers of 𝐁₁.* reads it: the layers j ≤ h − 1 of 𝐁₁ are the collar's. 𝐁₁'s finest data set is therefore not empty, and run B's collar carries data at its scales 0 and 1 there.
  - {#W12.19} *The collar's layers.* The misalignment is confined to a strip at ∂Ω.
    {#W12.19-1} CRE's 𝐁_j(Ω) is "a sequence of maximal domains" with Ω_n a union of L^nξM₁-cubes and dist(Ω_n, Ω_{n−1}^c) ≥ L^nξM₁ (CRE p.256 l.57–62).
    {#W12.19-2} The distance is the lattice distance |x − y| = Σ_μ|x_μ − y_μ| (PRT2 p.223 l.16).
    {#W12.19-3} Run A builds 𝐁_h(Ω) and run B builds 𝐁_{h+1}(Ω) from the same set Ω = Ω″^∼_{h+1}, a union of M₁a_h-cubes.
    {#W12.19-4} In physical units, run A's Ω^A_n uses cubes of the side c_n := L^nεM₁, and run B's Ω^B_{n+1} uses the same cubes c_n, while its Ω^B_1 uses c_0 = εM₁.
    {#W12.19-5} So Ω^A_n is the union of the c_n-cubes Q with dist(Q, (Ω^A_{n−1})^c) ≥ c_n, and likewise Ω^B_{n+1} with Ω^B_n.
    {#W12.19-6} The partitions are nested, so the ℓ¹ distance from a c_n-cube to Ω^c is a multiple of c_n, up to d lattice spacings.
    {#W12.19-7} (Ω^A_1)^c and (Ω^B_2)^c contain Ω^c and lie within the ℓ¹ distance d·2c_1 of it, since each removes at most two layers of c_1-cubes.
    {#W12.19-8} Take a c_2-cube Q. If Q touches Ω^c, it is selected in neither run.
    {#W12.19-9} If dist(Q, Ω^c) = c_2, it is selected in neither run, since a removed c_1-layer lies between Q and Ω^c.
    {#W12.19-10} If dist(Q, Ω^c) ≥ 2c_2, it is selected in both, since 2c_2 − 2dc_1 ≥ c_2 for L > 2d.
    {#W12.19-11} So Ω^A_2 = Ω^B_3, and by induction Ω^A_n = Ω^B_{n+1} for every n ≥ 2.
    {#W12.19-12} The two runs' collars therefore agree, layer by layer, at the shared scales n ≥ 2 of run A. They differ only on the strip Ω ∖ Ω^A_2, of the width at most 2c_2 = 2M₁a_2 at ∂Ω in the ℓ∞ distance and (d + 1)c_2 in the ℓ¹ distance (below, "the width 2M₁a_2" stands for this, the factor d + 1 changing constants only), which carries run A's layers 0 and 1 and run B's layers 0, 1, and 2.
    {#W12.19-13} The same holds for every piece 𝐁_j(Y_i) of the boundary-layer sets, built by the same rule.
    {#W12.19-15} The boundary-layer sets 𝐁(Y_i) ∪ · of p.373 l.17 and l.36 and p.374 l.13 are CRE's 𝐁 ∪ 𝐁(Ω): for a boundary ∂Ω contained in several domains Ω_j ∖ Ω_{j+1}, CRE constructs "the corresponding determining sets restricted to the domains" and joins them by (2.14) (CRE p.257 l.22–26), with a boundary layer "of the width 2M₁ at most, for the corresponding scale" (LFR II p.373 l.26–27).
    {#W12.19-16} Their pieces are the 𝐁_j(Y_i) of CRE p.256 l.57–62, so their layers run from the scale 0 at ∂Y_i up, and every boundary layer Y_i ∖ Y_i^0 has a finest-scale strip with no run-A counterpart.
- {#W12.20} The background pairs.
  {#W12.20-1} For 𝐇_k the background is U_k, and for 𝐇_{𝐁₁} it is U_{k,Λ}; both are run A's real chain configurations with VAR's layer bounds (VAR Theorem 1 for their problems), so V₀ := U^A_k or U^A_{k,Λ} and U^B := ι(V₀) satisfy the premise of 10.5.
  {#W12.20-2} For 𝐇″_k the background is U_{1,2}.
  {#W12.20-3} On Ω″^∼_{h+1} it is U_1 and on the complement U_2, each the minimiser of its problem, so VAR Theorem 1 gives the layer bounds on each side, at the collar's finer scales near the cut.
  {#W12.20-4} Near the cut Bałaban states that U_{1,2} "is regular, and satisfies the regularity conditions typical for an h-order configuration on the domain (Ω″_{h+1})^c ∩ Ω″^{∼2}_{h+1}.
  {#W12.20-5} It is so, because the arguments of the corresponding functions are equal to 1 on this domain, and the exponential decay properties enforce the additional regularity" (p.370 l.35–38).
    - {#W12.21} *The hypotheses of VAR's Sects. D–E at U_{1,2}.* The sentence after p.370 l.35–38 reads "We construct the expansion of U_k^0 around the configuration U_{1,2}. From the results of Sects. D, E [15] we obtain" (1.54), so U_{1,2} is the base U_0 of VAR's Sects. D–E for 𝐁″_k's problem.
      {#W12.21-17} Their hypotheses on the base are VAR (14), U_0 ∈ 𝔘_k({Ω_j}, C₁B₃ε₁) and |Ū₀^j − V| < C₁ε₁ "for some absolute constant C₁" (VAR p.280 l.15–21), one C₁ for both halves, and "the additional regularity condition (3.35)" (VAR p.280 l.48–53), REG's, with VAR p.280 l.42's smallness of the constants; the second-order operators of Sects. D–E and Proposition 9 use (3.36) as well (PBG p.396 l.33–34; VAR p.309 l.8–14).
      {#W12.21-2} 𝔘_k({Ω_j}, α₀) is REG's space of "regular field configurations", defined by its conditions (1.7)–(1.9) (REG p.077 l.31), and VAR (2) is this membership (REG (1.7) and (1.9)). For U_{1,2} it is taken for the sequence of 𝐁″_k, whose layer at the cut is h, so on the band at the index h.
      {#W12.21-9} (3.35) follows from the 𝔘-membership alone by REG's Sect. F, which needs no criticality (REG p.097 l.29–30, p.099 l.34–37), as VAR p.280 l.51–52 uses it, and REG's Proposition 6 gives (3.36) with it: in a gauge u on □̃, L^jη|A|, (L^jη)²|∇^ηA|, (L^jη)³|∂^{η*}∂^ηA|, and (L^jη)³|Δ^ηA| are < 7dL²B₁M_Rα₀ on □_j, with REG's cube parameter M_R a multiple of R₁M₁ (REG (1.135)–(1.136), p.099 l.41–48), at the 𝔘-parameter α₀ of the membership.
      {#W12.21-10} REG's proof of (3.35) takes M_R = R₁M₁ ((1.134)).
      {#W12.21-11} On §11's 16-block cubes and PBG's class cubes M_R is a multiple of R₁M₁ at least the cube's side in big blocks, with 7dL²M_Rα₀ ≤ c₁ there; this changes constants only.
      {#W12.21-12} Sect. F works on the cube □̃ enlarged by 2R₁M₁ at its own scale (REG p.098 l.12–18); in the band this margin is within the room of §11's 16-block cubes, since 18M₁a_h + 2R₁M₁a_h ≤ 20KM′a_h ≤ MR_{h+1}a_{h+1}, as M₁ ≤ KM′ and R₁M₁ = M′ (§8), under M ≥ 4KM′ (the condition M ≥ 4M₁ with CRE's M₁ = KM′) and 4LR_{h+1} ≥ 24 for L > 5.
      {#W12.21-30} So VAR (2) at the index h gives (3.35)–(3.36) at α₀ = C₁B₃ε₁, and its second line gives the current bound used on the strip. The Hölder entry of VAR (9) and |∇F|, which 10.5 reads, are taken at the minimiser base V₀ below.
      {#W12.21-24} Off the band the membership holds at B₃ε_U^{(i)} for the minimisers U_i (VAR Theorem 1), ε_U^{(i)} their data bounds, and the averages against the data of (1.54) are those of §11's scope condition (LFR II p.370 l.15–16, LFR I (1.87)).
      {#W12.21-25} On the band it holds at L³B₃ε_U^{(i)} (*The band regularity of U_{1,2}.* below), so C₁ := L³. VAR's constants, B₃ included, depend on d and L, and C₁ is of this kind; the downstream bounds carry it as C₁ (|J| ≤ C₁B₃ε₁(L^jη)^{−3}, §11).
      {#W12.21-22} Here ε₁ is the parameter of (14) for 𝐁″_k's problem. The data half asks C₁ε₁ > O(1)B₃²B₅M⁶ε_k, the bound |M^j(U_0^{(AL)}) − 1| of §11's scope condition, so ε₁ is the larger of this bound over C₁ and the ε_U^{(i)}.
      {#W12.21-28} Hence ε₁ ≤ O(1)B₃²B₅M⁶ε_k by #W12.22-3, and ε₁ tends to 0 with γ, as *10.5's premise at 𝐇″_k* needs (ε₂ → 0 against the fixed ε₁^{(1)}).
      {#W12.21-33} VAR (14) at U_{1,2} is used for PBG's and VAR's operators of 𝐇″_k at U_{1,2} and for the current gain on the strip.
    - {#W12.22} *The band regularity of U_{1,2}.* Bałaban's reason (p.370 l.37–38) has two parts: the arguments of U_1 and U_2 are 1 on the band, and the exponential decay enforces the regularity.
      {#W12.22-2} The result is VAR (2) at the index h on the band, for 𝐁″_k's sequence, with L³B₃ε_U^{(i)} on the side of U_i, ε_U^{(i)} the data bound of U_i's problem.
      {#W12.22-3} The data of U_1 are M^k(U_0^{(AL)}) on Λ ∩ Ω″_k, V″ on Λ^c, and 1, and those of U_2 are 1 and V″ (p.370 l.28–29), so ε_U^{(i)} ≤ O(1)B₃²B₅M⁶ε_k, the bound of §11's scope condition (LFR I (1.87)) with its O(1) taken at least the constant of the small-field conditions of order ε_k that V″ satisfies (as in *10.5's premise at 𝐇″_k* and *The collar of 𝐁₁.*). ε_U^{(i)} is not 10.5's fixed ε₁^{(1)}.
      - {#W12.23} The strips.
        {#W12.23-1} By (1.52) and the joining (2.14) [III] (CRE p.257 l.7–16), 𝐁₁ carries on Ω̃ ∖ Ω̃^{∼−2}, Ω̃ := Ω″^∼_{h+1}, the determining set 𝐁_h(Ω̃) of CRE p.256 l.57–63.
        {#W12.23-2} This is the sequence Ω̃ = Ω_0 ⊃ Ω_1 ⊃ … ⊃ Ω_h, with Ω_n a union of L^nηM₁-cubes and dist(Ω_n, Ω_{n−1}^c) ≥ L^nηM₁.
        {#W12.23-3} So its layer n, Ω_n ∖ Ω_{n+1}, has a width ≥ M₁L^{n+1}η, and its finest layer is a strip of width ≥ LM₁ bonds along ∂Ω̃, whose variables are the bond variables themselves (VAR (3)–(4): Ū^0 = U on Λ_0, and the residual gauge group has u = 1 on 𝔅_k ⊃ Λ_0; CRE p.256 l.26). 𝐁₂ has the same structure on the other side, from 𝐁_h((Ω̃)^c).
        {#W12.23-4} The refinement blocks carry the arguments 1 of (1.53), and p.370 l.37 states that the arguments are 1 on the band.
        {#W12.23-5} In detail, with the domains of (1.52)–(1.53) taken within Z (the LF note's convention (RZ), *The chain.*), the band is (Ω″_{h+1})^c ∩ Ω″^{∼2}_{h+1} ∩ Z, and Ω″_{h+1} ∩ Z = Z ∖ Z″_{h+1} by LFR I (1.12) (p.179 l.35), so the band lies in Z″_{h+1} ⊂ Z″_k (LFR I p.195 l.42).
        {#W12.23-6} On its part in Ω̃ the data of U_1 are 1⌈_{Z″_k∩Ω̃}, and the other arguments of U_1, M^k(U_0^{(AL)}) on Λ ∩ Ω″_k and V″ on Λ^c, sit off the band, since Ω″_k ⊂ Ω″_{h+1} and Λ^c ⊂ (Z″_k)^c.
        {#W12.23-7} On its part in Ω̃^c the data of U_2 are 1⌈_{(Ω̃)^c∩Ω″^{∼2}_{h+1}}.
        {#W12.23-8} Both strips lie in the band: the collar 𝐁_h(Ω̃) lies within 2M₁ of ∂Ω̃ at the scale h (CRE p.256 l.62, "Ω^{∼−2} ⊂ Ω_j"; LFR II p.371 l.2), and the band extends one layer of the ∼-cubes on each side of ∂Ω̃, MR_{h+1} at the scale h + 1 (LFR I p.179 l.7–8), with 2M₁ ≤ LMR_{h+1}; the same holds for 𝐁_h(Ω̃^c).
        {#W12.23-9} Under (RZ), U_1 lives on Ω̃ ∪ Z^c and U_2 on Ω̃^c ∩ Z, so the only interface between them is ∂(Ω̃^c ∩ Z).
        {#W12.23-10} It lies in Z, away from ∂Z: Ω̃^c ∩ Z ⊂ Z″_{h+1} ⊂ Ω^c_{h+1} ∩ Z, and every point of Z^c lies at a distance ≥ dist(Ω_k, Ω^c_{k−1}) ≥ 8MR_ka_k from Ω^c_{k₀+1} ∩ Z ⊃ Ω^c_{h+1} ∩ Z (the LF note's §4(d), *The cubes □₀ at Z.*).
        {#W12.23-11} So the only interface that meets the band is ∂Ω̃ ∩ Z.
      - {#W12.24} The band lies in the layer h of 𝐁″_k.
        {#W12.24-1} On Z, Ω″_{h+1} = Ω^{∼5}_{h+1} ∩ Z by LFR I (1.11)–(1.12), and Ω″^{∼2}_{h+1} adds two layers of the MR_{h+1}-cubes of the scale h + 1, so the band lies in Ω^{∼7}_{h+1} ∖ Ω_{h+1}.
        {#W12.24-2} The LF note's *The middle layers.* (its #4.317-0) gives dist(Ω_{h+1}, Ω_h^c) ≥ 8MR_{h+1}a_{h+1}, from CRE (3.5) together with the construction of Z′_j there (also LFR I p.177 l.18–19: "Each renormalization step adds at least ten layers of MR_k-cubes").
        {#W12.24-3} So Ω^{∼7}_{h+1} ∩ Z ⊂ Ω_h ∩ Z ⊂ Ω″_h, and the band lies in Ω″_h ∖ Ω″_{h+1}, 𝐁″_k's layer h.
      - {#W12.25} The cut.
        {#W12.25-1} Every configuration with these averages is 1 on the bonds of both finest strips, so U_{1,2} = 1 there, whatever representative of the minimal orbits is taken. ∂Ω̃ is a union of faces of cubes, so each plaquette lies in the closure of Ω̃ or in that of its complement, and the bonds on ∂Ω̃ are 1 from both sides.
        {#W12.25-2} A plaquette or a current that reads bonds of both U_1 and U_2 reads only bonds within one bond of ∂Ω̃.
        {#W12.25-3} So there ∂U_{1,2}(p) = 1 and D*∂U_{1,2} = 0, and no crossing term remains.
      - {#W12.26} Off the strips.
        {#W12.26-1} On the band outside the strips, the layers of 𝐁₁ and 𝐁₂ are 𝐁″_k's, and VAR Theorem 1 for U_i gives (2) at the index h with B₃ε_U^{(i)}.
      - {#W12.27} The block size.
        {#W12.27-1} The collar's layers are only LM₁ wide in their own units, so VAR's Sect. F cube □̃, at the distance 2R₁M₁L^nη around a cube of the side 2R₁M₁L^nη (p.300 l.28–37), would reach through all the finer layers to the cut at the block size M₁.
        {#W12.27-2} As everywhere at the joins, VAR is applied with its product R₁M₁ = M′, its block size M₁^{VAR} kept and its R₁ raised to M′/M₁^{VAR}, and CRE's M₁ := KM′ with K ≥ 12d + 1 (BP_JOINS_BLOCK_SIZE #4.22–#4.24).
        {#W12.27-4} This is not Bałaban's literal usage, which applies VAR at CRE's M₁ (CRE p.245 l.35–37, p.256 l.52–53).
        {#W12.27-6} Theorem 1 at R₁M₁ = M′ supplies the starting own-layer bounds on the collar.
        {#W12.27-7} The collar then satisfies VAR (1) with R = R′R₁ blocks of M₁^{VAR} (BP_JOINS_BLOCK_SIZE #4.23-0), R′ = LK − 1 > 4dL, which is VAR's ratio condition R > 4dLR₁ for its Sect. F cubes (#W12.237-3), so □̃ ⊂ B^{n−1}(Λ_{n−1}) ∪ B^n(Λ_n) ⊂ Ω_{n−1} (p.300 l.37).
        {#W12.27-8} VAR prints the step at j = k, "a general case can be obtained by obvious rescalings" (p.300 l.37), and it is used at the collar's layer n in that sense.
        {#W12.27-9} Below, R₁M₁ in VAR's Sect. F stands for M′, and B₃, δ₀, B₀, B₁, C₂, and C₄ are VAR's constants at that size in this sense, of d and L.
      - {#W12.28} On the strips: the step of Sect. F. Theorem 1 gives (2) only at the strip's own layer n < h.
        {#W12.28-1} At the index h the conditions are stronger by L^{2(h−n)} for the plaquettes and by L^{3(h−n)} for the currents (VAR (2): ε₀L^{−2j}η² and ε₀L^{−2j}(L^jη)^{−1}).
        {#W12.28-2} The decay comes from Sect. F, whose step is not a fixed halving.
        {#W12.28-3} (161)–(162) (VAR p.303) bound the linear part on Δ₀ by ¼max{B₃ε₁, B₃e^{−½δ₀R₁M₁}ε₀}, where ε₁ is the data plaquette bound on □_k and ε₀ the bound (2) outside □_k, and (165) adds K(R₁M₁)²ε₀², K := B₀(C₄ + 4C₂)(36dL²B₁)².
        {#W12.28-5} With (168), which doubles the bound for (2) on Δ₀, and ½x + y ≤ max(x, 2y), one step gives (2) on Δ₀ with max{B₃p^{loc}, θe^{old}}, θ := B₃e^{−½δ₀R₁M₁} + 4K(R₁M₁)²e^{old}.
        {#W12.28-6} Here p^{loc} is the data plaquette bound on □_k and e^{old} is the supremum over □̃ of the (2)-bounds, each normalised at its own layer; VAR's (145) already absorbs the factor L² of the finer layer ("with L²ε₀η² on the right-hand side", p.300 l.39–40), and evaluating a coarser layer at its own-layer value only discards a gain.
        {#W12.28-7} Through the 𝔘-membership in (150), the current condition of the finer layer carries L³ in place of L²; this changes only constants such as K, absorbed by (163′) and the smallness for γ small.
        {#W12.28-8} The cubes are taken in VAR's class: a cube of the index n meets Ω_n but not Ω_{n+1} (p.300 l.28), so a block of the layer n near Ω_{n+1} is treated by a cube of the index n + 1, whose output, normalised at the index n + 1, is stronger than needed at the layer n: its chain count starts at the index n + 1, and the conversion to the layer n gains the factor L^{−3} for the currents and L^{−2} for the plaquettes, which covers the count's loss.
        {#W12.28-9} Such a cube exists for every block: an index-n cube with □_k and □̃ off Ω_{n+1}, or else an index-(n + 1) cube, since K > 4d and L > 2d.
        {#W12.28-10} For the index-(n + 1) cube the block lies in the finer part □′_k of its local problem, where VAR prints no output (Δ₀ ⊂ B^j(Λ_j), p.302 l.45); there the local index of (152) at the points of □′_k costs at most factors of L in B₃ and K, which are absorbed before M′ is fixed.
        {#W12.28-11} So the local determining set (148)–(149) of every step carries the original data on □_k.
      - {#W12.29} The contraction.
        {#W12.29-1} B₃ and δ₀ depend on d and L only ((162), p.303), so VAR's (163), B₃e^{−½δ₀R₁M₁} ≤ ½ ("We may assume that R₁M₁ is sufficiently big", p.304 l.2), is taken at the collar in the stronger form (163′) B₃e^{−½δ₀M′} ≤ ½L^{−3}, a lower bound on M′, hence on CRE's M₁ = KM′, of the same kind as CRE's conditions on M₁, which are lower bounds (the LF note's *The block size M′.*).
        {#W12.29-2} Under (163′) and 4KM′²B₃ε_U^{(i)} ≤ ½L^{−3}, which holds for γ small, θ ≤ L^{−3} at every step, since the bounds only decrease.
      - {#W12.30} The chains.
        {#W12.30-1} As in the LF note's layered rerun (its *The real part.*, *The iteration.*), the limit bound at a block is at most the supremum over chains of steps of θ^{length}B₃p^{loc} at the chain's end, since the term θ^mε₀ of the starting bound tends to 0.
        {#W12.30-2} A step at a block of the layer n reads □̃ ⊂ Ω_{n−1}, which lies within 6M′L^nη of it in the ℓ∞ distance, 6dM′L^nη in the ℓ¹ distance (p.300 l.28–37).
        {#W12.30-3} The layer n + 1 is at least LM₁ = LKM′ wide in its units L^{n+1}η (CRE p.256 l.57–62), more than 6dM′L^nη, so □̃ does not meet the layer n + 2, and one step moves the layer by at most one.
        {#W12.30-4} On the strips and on the band the original data are 1, so in the generalised axial gauge V′ = 1 on □_k and p^{loc} = 0.
        {#W12.30-5} The non-trivial data of U_i lie on 𝐁″_k's blocks off the band, which meet the strip only beyond its layer h − 1.
        {#W12.30-6} So a chain from a block of the layer n ending at a non-zero p^{loc} has length ≥ h − 1 − n, and (2) holds there at the layer n with θ^{h−1−n}B₃ε_U^{(i)} ≤ L^{−3(h−1−n)}B₃ε_U^{(i)}.
        {#W12.30-7} At the index h this is ≤ L³B₃ε_U^{(i)}.
      - {#W12.31} So U_{1,2} satisfies VAR (14) on the band at the index h with C₁ = L³, a constant of d and L, and ε₁ the larger of the ε_U^{(i)} and the data bound over C₁.
        {#W12.31-1} PBG's (3.35)–(3.36) follow from it by REG's Sect. F and Proposition 6, as above.
        {#W12.31-2} The conditions added are (163′) on M′ and the smallness of ε_U^{(i)} for γ small.
    - {#W12.32} *10.5's premise at 𝐇″_k.* 10.5 also reads the Hölder entry of VAR (9) and |∇F| at its real base (*The base and the local gauge.*).
      {#W12.32-1} VAR (2) does not contain these, so they are not taken at U_{1,2}.
      {#W12.32-2} Bałaban's expansion (1.54) (p.370) reads U_k^0 = (exp iη𝐇″_k(𝐆″_kJ_{1,2}, H″_{1,k}Q̃_·(η𝐀₀)⌈_{Z″_k∩Ω″^{∼2}_{h+1}})U_{1,2})^{(u_k^0)^{−1}}.
      {#W12.32-3} Here U_k^0 is the configuration (1.50) at B = 0, the minimiser of 𝐁″_k's problem at its data: Bałaban defines it as the minimiser function U_{𝐁″_k} at the data of (1.50) (p.370 l.14) and uses it as such, with VAR Theorem 1.
      {#W12.32-4} So, bond by bond, U_{1,2} = e^{iB′}V₀ with V₀ := (U_k^0)^{u_k^0} and B′ := −η𝐇″_k(…).
      - {#W12.33} V₀ is a real minimiser up to a gauge transformation.
        {#W12.33-1} So VAR (9)–(10) hold for it at 𝐁″_k's layers, which at the cut is the layer h, with β up to β₀ = 1 (VAR p.279 l.23), and (9.2) follows at β₀ = 1.
      - {#W12.34} B′ is real.
        {#W12.34-1} VAR (19) for 𝐇″_k gives |B′| < ε₂η(L^jη)^{−1} and first differences < ε₂η²(L^jη)^{−2} on 𝐁″_k's layers.
        {#W12.34-2} That is the form |B′| ≤ ϱε/a_j with first differences ≤ ϱ(ε/a_j)² that 10.5 accepts at its points V′V₀, with ϱ = ε₂ in its units.
        {#W12.34-3} VAR (19) holds at the background U_{1,2} by VAR (14) there, derived in *The band regularity of U_{1,2}.*, with ε₂ as below.
      - {#W12.35} So 10.5 is run at 𝐇″_k with the base V₀ and the real point U_{1,2} = V′V₀, V′ := e^{iB′}, with ϱ + ε₂ in place of ϱ, also in ϱ̄ and α_c.
        {#W12.35-1} Its conditions O(1)(ϱ + ε₂) ≤ C₁^{(1)}ε₁^{(1)}/4 and O(1)(ϱ + ε₂) ≤ α₁^A/L hold for γ small once 10.5's conditions on ϱ hold with half the right sides, a condition of the same kind, in §8's list: ε₁^{(1)}, C₁^{(1)}, and α₁^A, the ε₁ and C₁ of 10.5's one-step problem and its threshold, are fixed before γ (its conditions B₅ε₁^{(1)} ≤ a₁/2 and O(1)(R₀M₀)²L⁴C₀ε₁^{(1)} ≤ 1 contain no coupling).
        {#W12.35-2} One fixed ε₁^{(1)} serves both the one-step problem and VAR (9) for V₀, by #W8.12-8. 10.5 reads V₀'s VAR (9)–(10) only through §11's pointwise cube fitting (VAR's class cubes of the index m or m − 1 at each point of a layer m, with M_V = R₁M₁ or 3LR₁M₁), whose M_V ≤ M(ε₁^{(1)}) = R₁M₁a₁/ε₁^{(1)} (VAR p.279 l.28) asks ε₁^{(1)} ≤ a₁/(3L), one more upper bound on ε₁^{(1)}.
        {#W12.35-3} These bounds, with O(1)L⁴C₀ε₁^{(1)} ≤ α₀, are imposed after α₀, M′, and K, so ε₁^{(1)} is fixed after them, and before γ. ε₂ is VAR's (19), ε₂ ≥ B₁(ε₀^𝔘 + C₁ε₁) (VAR p.281 l.19, there written ε₀), at the base U_{1,2}, with ε₀^𝔘 the 𝔘-parameter of the target U_k^0 and C₁ε₁ that of the base: ε₂ = B₁(B₃ε₁(U_k^0) + C₁ε₁).
        {#W12.35-4} Here B₃ε₁(U_k^0) is the regularity of the minimiser U_k^0 by VAR Theorem 1 at its data, whose bound O(1)B₃²B₅M⁶ε_k on Z″_k is that of §11's scope condition (LFR I (1.87)) and which off Z″_k are V″ under the small-field conditions of the order ε_k, and C₁ε₁ is the base's parameter of *The hypotheses of VAR's Sects. D–E at U_{1,2}.* So ε₂ ≤ B₁(O(1)B₃³B₅M⁶ε_k + C₁ε₁), which tends to 0 with γ by *The band regularity of U_{1,2}.* Its premise reads only V₀'s layer bounds, and U_{1,2} enters through V′.
        {#W12.35-5} In 10.5's notation U^B := ι(V₀), the lift of the base.
        {#W12.35-6} Run B's background ι(U_{1,2}) is ι(e^{iB′}V₀) = e^{i(ε/L)𝐒′}U^B, with a_{j(x)}|𝐒′(x)| + a_{j(x)}²|∇𝐒′(x)| ≤ 2C_δ(ε₀)L^{7/3}·O(1)ε₂ by the flow of the LF note's *The Fine Side at the Multiscale Chain.*, *The bound.*, run from V₀ along e^{itB′}V₀ with B′/ε in place of A_c (V₀ satisfies VAR (9)–(10), and B′ has the layered bounds above).
        {#W12.35-7} So run B's background is a point U′U^B of 10.5 with ϱ + O(1)C_δ(ε₀)L^{7/3}ε₂ in place of ϱ, within the conditions above for γ small.
        {#W12.35-8} The function compared is the (111) function with the current J_{1,2}, at the pair (ι_YU_{1,2}, U_{1,2}) of (iii).
    - {#W12.36} *§11's oscillation at U_{1,2}.* §11 bounds the first variation of the blocking artifact through osc_p(TF) ≤ 4dε|∇F| + 4δ_T|F| (the Cauchy note's #C10.4.50), with F the fine curvature of the lift and |∇F| ≤ C₀ε₁a_j^{−3} from (9.2).
      {#W12.36-1} At U_{1,2} the second differences of B′ are not bounded at the scale of the layer: VAR (19) bounds only its first differences, ∂*∂, and Δ.
      {#W12.36-2} So the oscillation is split at the base.
      - {#W12.37} Let c_t := e^{itB′}V₀, 0 ≤ t ≤ 1, so c_0 = V₀ and c_1 = U_{1,2}, and W_t := ι_Y(c_t).
        {#W12.37-1} The fine curvature satisfies F(W_1) = F(W_0) + ∫₀¹(D_{W_t}ℒ_ι(c_t)B′ + Q_t)dt.
        {#W12.37-2} Here ℒ_ι(c_t)B′ is the fine field of the derivative of the lift in the direction B′; it is H₁𝔡B′ + D_Bγ plus the interface-twist term of CMP 99 (1.31) at the bonds crossing from Λ₀ to Λ₁, which 10.5 drops for data vanishing near the collar and which here lies at distance ≥ M₁a_k from X, so it is bounded with the (1 − χ)v tail below.
        {#W12.37-3} Q_t collects the commutator terms, at most c_{br}·4dε|ℒ_ι(c_t)(B′/ε)||F(W_t)| per fine plaquette (the Cauchy note's #C10.4.48-1, with the connection field B′/ε of the dimensionless logarithm B′).
      - {#W12.38} W_0 = ι_Y(V₀) is the lift of a minimiser, as at the other pairs: (9.2) holds at the (k + 1)-step minimiser with V₀'s data, and W_0 differs from it by the field of the Cauchy note's §9.7 at the layer j (*The base at the layer j.* below) and by the tail of ι_Y against ι (the Cauchy note's §9.8, *The tail.* and *The consequences.*), rerun with a layered input.
        - {#W12.39} §9.8's input is homogeneous: the mismatch B of *The collar mismatch.* is bounded through |F| ≤ C_Fε₁/a² at one scale a.
          {#W12.39-1} Here the points of Y^∼ carry |F| ≤ C_Fε₁a_{j′}^{−2} at their own layers j′, with a_{j′} ≥ ε, so B is at most LC_LC_Fε₁/ε per fine bond.
          {#W12.39-2} That is (a/ε)² times the homogeneous bound LC_LC_F(ε/a)ε₁/a for every a, and it is read below at a = a_k, as in the Cauchy note's #C9.8.17-3–#C9.8.17-4.
        - {#W12.40} Y^∼ exceeds Y by M₁a_k ≥ M₁a_j, so on X and within 2L fine spacings of it the decay of *The decay.*, at its rate δ_ι (written δ₀ there), gives e^{−δ_ιM₁a_k/ε} in place of e^{−δ_ιM₁L^j}, with the same factor e^{δ_ι(R_ι/L + 2)M₁} in C(ε₀).
          {#W12.40-1} *The consequences.* then bound the tail by (a_k/ε)²C(ε₀, δ_ιM₁)ε₁e^{−δ_ιM₁a_k/(2ε)}L^{j−k}, with C(ε₀, δ_ιM₁) = 2C(ε₀)/(eδ_ιM₁) ≤ C(ε₀) under δ_ιM₁ ≥ 1, and the factor L^{j−k} ≤ 1 is dropped.
        - {#W12.41} Half of the remaining decay pays the factor (a_k/ε)²: x²e^{−δ_ιM₁x/4} ≤ (8/(eδ_ιM₁))² ≤ 9 for x ≥ 0.
          {#W12.41-1} The other half gives e^{−δ_ιM₁a_k/(4ε)} ≤ e^{−L^j/4} ≤ L^{−j} = ε/a_j, since a_k ≥ a_j, δ_ιM₁ ≥ 1, and L^j ≥ 4j log L for L ≥ 9, which stage 1's L ≥ 12d + 6 covers.
        - {#W12.42} So the tail is at most 9C(ε₀)(ε/a_j)^{1−2ε₀}ε₁ at every layer j ≥ 0, and the 9 is absorbed into C(ε₀).
          {#W12.42-1} *Away from X.* The tail is bounded through the weight ω of *The bootstrap.* below.
          {#W12.42-2} The mismatch is at most LC_LC_Fε₁/ε per fine bond, since a_{j′} ≥ ε, so *The decay.* at a = ε gives |T| ≤ C_ιε₁ε^{−1}e^{−δ_ιdist(·,Ω₁^c)/ε}, and with the fine differences ≤ 2L|T|/ε the curvature of W_0 changes by |F_T(x)| ≤ O(L)C_ιε₁ε^{−2}e^{−δ_ιdist(x,Ω₁^c)/ε}.
          {#W12.42-3} Let δ′ := min(δ_ι, ⅛δ₁) and D := d_ε(x, Y); d_ε counts lattice steps, so εd_ε dominates the distance in dist, and dist(x′, Ω₁^c) ≥ dist(x, Ω₁^c) − εd_ε(x, x′), here and in the transfer of #W12.62-6.
          {#W12.42-4} Since dist(x, Ω₁^c) ≥ 0 and, by the count of *The consequences.*, dist(x, Ω₁^c)/ε ≥ M₁a_k/ε − D − (R_ι/L + 2)M₁, e^{−δ_ιdist/ε} ≤ e^{δ′(R_ι/L + 2)M₁}e^{−δ′(M₁a_k/ε − D)}.
          {#W12.42-5} If ω(x) = (a_j/ε)², j = j(x), the bound e^{−δ_ιdist/ε} ≤ 1 gives |F_T(x)| ≤ O(L)C_ιε₁a_j^{−2}ω(x).
          {#W12.42-6} Otherwise ω(x) = e^{⅛δ₁D} ≥ e^{δ′D}, and (a_j/ε)²e^{−δ′M₁a_k/ε} ≤ (a_k/ε)²e^{−δ′M₁a_k/ε} ≤ (2/(eδ′M₁))² gives |F_T(x)| ≤ O(L)C_ιe^{δ′(R_ι/L + 2)M₁}(2/(eδ′M₁))²ε₁a_j^{−2}ω(x) ≤ O(L)C_ιe^{δ_ι(R_ι/L + 2)M₁}(2/(eδ′M₁))²ε₁a_j^{−2}ω(x), since δ′ ≤ δ_ι.
          {#W12.42-7} With K_T := max{1, (2/(eδ′M₁))²}, |F_T(x)| ≤ O(L)C(ε₀)K_Tε₁a_j^{−2}ω(x) at every x of Y^∼, with no upper bound on D. K_T is a constant of L and δ₁ under δ_ιM₁ ≥ 1 (§8, stage 3) and (F-ι), which gives ⅛δ₁M₁ ≥ ((3 + β₂)log L + log 2)/(2L).
      {#W12.43} The Cauchy note's C(ε₀) contains C_ιe^{δ_ι(R_ι/L + 2)M₁} (its #C9.8.17-3, with its rate δ₀ the rate δ_ι), so it grows with M₁ and enters no lower bound on M₁.
      {#W12.43-1} So the oscillation of F(W_0) over a cell of the layer j is at most 4d(1 + 32d)C₀ε₁εa_j^{−3} + O(1)C(ε₀)(ε/a_j)^{1−2ε₀}ε₁a_j^{−2}.
      - {#W12.44} *The base at the layer j.* The Cauchy note's §9.4–9.7 take Ω_j to be the whole lattice, but each bound there is a bound in VAR's norms |·|_{(α)} of PBG (3.41), which are weighted layer by layer, and the inputs are local: (9.2)–(9.3) are VAR (9) at the layer of the point, and the sources r₁, r₀ of §9.3 satisfy |r₁| ≤ C_r(ε/a_j)ε₁a_j^{−2} and |r₀| ≤ C_r(ε/a_j)ε₁²a_j^{−3} at the layer j.
        {#W12.44-1} Let s := 1 − ε₀ and |A|^♯_{(α)} := ε^{−s}|A|_{(α−s)}, so that a bound C(ε/a_{j(x)})^sε₁a_{j(x)}^α at every x reads |A|^♯_{(α)} ≤ Cε₁; then |r₁|^♯_{(−2)} ≤ C_rε₁ and |r₀|^♯_{(−3)} ≤ C_rε₁², since ε/a_j ≤ (ε/a_j)^s.
        {#W12.44-2} The kernel sums of (9.8), (3.42), and (3.44) for 𝔊 (PBG Theorem 3.13) are summed over the layers of the source with Lemma 2.1 of [4] as in PBG's remark on p.398, which trades (L^jη)^α for (L^jη)^{α′}(L^{j′}η)^{α−α′} at a fixed fraction of δ₀, and the global form (3.47) holds for every γ ∈ [−4, 4].
        {#W12.44-3} The Hölder factor 2(a/ε)^{ε₀} of (9.8) is taken at the layer of the source, where the shift by s = 1 − ε₀ absorbs it.
        {#W12.44-4} So ‖𝔊J‖^♯ ≤ C_G(ε₀)ε₁, with C_G(ε₀) enlarged by a constant of L and d.
        - {#W12.45} The fixed point needs only a bound at one argument, not a contraction in the shifted norm.
          {#W12.45-1} With B = 0, A₁* = −𝔊J − 𝔊(δV/δA′)(A₁*) (the Cauchy note's §9.4, VAR (116)), and (δV/δA′)(0) = 0, as (9.6) uses in T(0) = −𝔊J.
          {#W12.45-2} Let ε₄ be VAR's ball parameter of (115), max{|A₁|_{(−1)}, |∇A₁|_{(−2)}} < ε₄ (VAR p.294 l.59–60), subject to 2B₀C₁B₃ε₁ ≤ ε₄ ≤ a₄ (p.295 l.20); it is taken as ε₄ := 3B₀C₁B₃ε₁, the value Proposition 6 prints (p.295), with the data parameter ε₁ of (9.2). The single-argument bound |(δV/δA′)(A)|^♯_{(−3)} ≤ O(1)C₄ε₄‖A‖^♯ follows by rerunning the proof of VAR Proposition 4, used in (116)–(121) at B = 0, as in the LF note's #4.238, with the scale power ε^{−s}a_{j(b)}^{s} of |·|^♯ in place of its weight w.
          {#W12.45-3} The shifted norm |·|^♯_{(α)} = ε^{−s}|·|_{(α−s)} is VAR's layered norm at the exponent α − s ∈ [−4, 4], times ε^{−s}.
          {#W12.45-4} The rerun of the proof of VAR Proposition 4 in the shifted norm (#W12.45-2) uses four properties of the weight, each of which holds here.
          {#W12.45-5} First, a local factor next to the output point b carries the weight: the local derivative of C_j in 𝔇 at the block of b, V₀′ and its derivative at a plaquette of b, and the pointwise commutators (91)–(96).
          {#W12.45-6} The points of a block or plaquette lie in at most two adjacent layers, so the scale power changes there by at most L^s ≤ L. Second, the factors at the far end of a kernel, the current at b′ and the factors at c₁ in (85)–(86), are taken unshifted, the current in |·|_{(−3)}, ≤ C₁B₃ε₁ ≤ ε₄ (VAR's C₁; the second inequality is 3B₀ ≥ 1, B₀ an upper-bound constant taken ≥ 1/3 when it is fixed), and the factors at c₁ in |·|_{(−1)} and |∇·|_{(−2)}, ≤ ε₄, and the kernel's decay e^{−δ₀d} or e^{−½δ₀d} pays the sums over b′ and c₁ in VAR's layered norms, as in VAR.
          {#W12.45-7} Third, where A enters through HD(A), the weight sits on D, and |HD(A)|^♯_{(−1)} ≤ O(1)B₀|D(A)|^♯ by the kernel bound (3.133) of H summed by Lemma 2.1 of [4] (PBG p.398), the layer changes along H traded at a fixed fraction of δ₁; where D(A′) stands behind (QGQ*)^{−1} in VAR (88), the same holds with the decay (3.132) at the rate δ₁.
          {#W12.45-8} Fourth, no weight crosses the Neumann kernel (71).
          {#W12.45-9} So |(δV/δA′)(A)|^♯_{(−3)} ≤ O(1)C₄ε₄‖A‖^♯, ‖A‖^♯ := max{|A|^♯_{(−1)}, |∇A|^♯_{(−2)}}, with the factor L and the fractions of δ₀ and δ₁ in the O(1), a constant of L and d.
          {#W12.45-10} With (3.47) for 𝔊 at the shifted γ, ‖𝔊(δV/δA′)(A₁*)‖^♯ ≤ ½‖A₁*‖^♯ under 4C_♯B₀C₄ε₄ ≤ ½, VAR's condition 4B₀C₄(ε₄ + 2dLB₀C₁ε₁) ≤ ½ for the constant ½ (p.295 l.42) at B = 0, with C_♯ ≥ 1 a constant of L and d that contains both the enlargement of (3.47) for 𝔊 in the shifted norm and the O(1) of the single-argument bound (§8, stage 6, for γ small). ‖A₁*‖^♯ is finite on the finite lattice, so ‖A₁*‖^♯ ≤ 2‖𝔊J‖^♯.
        - {#W12.46} The fine side of §9.7 is the same with s := 1 − 2ε₀.
          {#W12.46-1} Its source J(U₀′) − J(U^B) is the divergence of ℒA′* plus a bounded source, at each point bounded through the coarse side's ‖A₁*‖^♯ at the layer j′ of the point.
          {#W12.46-2} (3.42) and (3.44) for 𝔊_B give §9.7's extra factor (a/ε)^{ε₀}, at the fine spacing (La_{j′}/ε)^{ε₀}, taken at the layer of the source; the shift s = 1 − 2ε₀ absorbs (a_{j′}/ε)^{ε₀}, and L^{ε₀} goes into C(ε₀).
          {#W12.46-3} The background-change term 𝔓*_{U₀′}J(U^B) is relatively O(ρ(ε/a)²ε₁) by the Cauchy estimate of §10.3 (§9.7), at each layer, and is absorbed in C(ε₀).
      {#W12.47} So at x in the layer j the field of §9.7 has sup ≤ C(ε₀)(ε/a_j)^{1−2ε₀}ε₁/a_j and gradient ≤ C(ε₀)(ε/a_j)^{1−2ε₀}ε₁/a_j², with C(ε₀) enlarged by a constant of L and d.
      {#W12.47-1} This is the transfer that §11 states for the currents.
      - {#W12.48} The points c_t are of 10.5's form V′V₀ with the real V′ = e^{itB′}.
        {#W12.48-1} So 10.5's real-point bounds hold at c_t: (H_ℒ), and the Hölder bound of leg 2 at the exponent β with the data norm at β₂ = (1 + β)/2 (*The Hölder bound.*).
        {#W12.48-2} The data norm of B′ needs its β₂-Hölder gradient. 𝐇″_k's derivative in its arguments is composed of H, H₁, 𝐆″_k = 𝔊, and the derivative of the (111) fixed point.
        {#W12.48-3} Each term ends in an operator with a Hölder entry for sup-bounded arguments, so no Hölder bound of a multiplication operator is needed:
        - {#W12.49} The fixed point is A₁ = −𝔊J − 𝔊N(A₁), N(A) := (δV/δA′)(A + H₁B) (VAR (111), (116)), and the field is A₁ + H₁B − H𝔇(A₁ + H₁B) (VAR (112), with 𝔇 the operator printed there as D).
          {#W12.49-1} Its derivative in the arguments is δA₁ = −𝔊λ, λ := δJ + N′(A₁)(δA₁ + H₁δB), plus H₁δB − H𝔇′(A₁ + H₁B)(δA₁ + H₁δB).
        - {#W12.50} The sup of λ is bounded as in VAR (117) and (120), by Proposition 4: |λ|_{(−3)} ≤ |δJ|_{(−3)} + 4C₄(ε₄ + B₀|B|)(max{|δA₁|_{(−1)}, |∇δA₁|_{(−2)}} + B₀|δB|).
          {#W12.50-1} The contraction (121) gives max{|δA₁|_{(−1)}, |∇δA₁|_{(−2)}} ≤ 2B₀(|δJ|_{(−3)} + 4C₄(ε₄ + B₀|B|)B₀|δB|).
        - {#W12.51} PBG (3.43) holds for 𝔊 by PBG Theorem 3.13 (through Theorem 3.3), which assumes (3.132) (PBG p.426 l.28), at the background U_{1,2}, which satisfies (3.35)–(3.36) by the derived membership.
          {#W12.51-1} It bounds the β₂-Hölder quotient of ζ∇𝔊λ, ζ ∈ C₀^∞(Δ̃(y)), y ∈ Λ_j, by B₀(β₀)(L^jη)^{1−β₂}(‖ζ‖^ξ_{β₂} + |ζ|)Σ_{y′}e^{−δ₀d(y,y′)}|λ|_{Δ(y′)}, which needs only the sup of λ.
          {#W12.51-2} The terms H₁δB and HD(·) carry the Hölder entry of PBG (3.133), which holds for H and H₁ by PBG Theorem 3.12, again with sup-bounded arguments.
        - {#W12.52} The layers j′ of y′ are summed with the remark after PBG Theorem 3.1 (Lemma 2.1 of [4], p.398), which trades (L^jη)^α for (L^jη)^β(L^{j′}η)^γ, β + γ = α, at the cost of a fixed fraction of the decay rate δ₀.
          {#W12.52-1} This gives the layer factor (L^jη)^{−2−β₂} times the size of the data.
      {#W12.53} So B′ = −η∫₀¹(δ𝐇″_k)(·)dt by the integral formula of 10.5's field bullet. The data have size O(1)B₃(ε₀^𝔘 + C₁ε₁) ≤ O(1)(B₃/B₁)ε₂ by ε₂ ≥ B₁(ε₀^𝔘 + C₁ε₁) (VAR p.281 l.19), with ε₀^𝔘 the 𝔘-parameter of the target; the ratio B₃/B₁ of Bałaban's constants is included in the O(1) and in C(β₂) below. Hence, at the layer j and in the covariant derivatives of U_{1,2}, |B′| ≤ O(1)ε₂ε/a_j and the first differences of B′ are ≤ O(1)ε₂(ε/a_j)².
      {#W12.53-1} Their β₂-Hölder quotient is ≤ C(β₂)ε₂(ε/a_j)²a_j^{−β₂}. The conversion to ∇_A at c_t costs a commutator of relative order c_{br}ε₂, since |B′| ≤ O(1)ε₂ε/a_j against the factor ε/a_j of a first difference.
      - {#W12.54} Hence the fine curl of ℒ_ι(c_t)B′ has, on the box of side 2ε of a coarse plaquette, an oscillation at most C_ℬ(ε/a_j)^βC(β₂)ε₂a_j^{−2}, from the Hölder quotient of the gradient entry of ‖ℒ_ιB′‖_{1,β} over a distance ≤ (d + 6)^{1/2}ε.
        {#W12.54-1} Q_t adds O(1)c_{br}ε₂(ε/a_j)C₀′ε₁a_j^{−2}, under the bootstrap below.
        {#W12.54-2} These boxes, and those of the bullets below, are the boxes within 2ε of X, where the frozen term and its current slot live (the Cauchy note's §9.8, *The consequences.*), and where the weight ω of the bootstrap is at most e^{δ₁/4}; the factor e^{δ₁/4} is absorbed into the O(1)s and into C_ℬ.
      - {#W12.55} The transport term 4δ_T|F| of osc_p(TF), with δ_T = 32d²ν_F, ν_F the supremum of ε²|F| over the paths of the plaquette (the Cauchy note's #C10.4.49-2 and #C10.4.50), is read at W_1.
        {#W12.55-1} There |F(W_1)| ≤ |F(W_0)| + sup_t(|D_{W_t}ℒ_ι(c_t)B′| + |Q_t|) ≤ O(1)C₀′ε₁a_j^{−2}, by the bootstrap below at t = 1 with ω ≤ e^{δ₁/4}, with C₀′ε₁ as below.
        {#W12.55-2} So the transport term is at most 128d²(O(1)C₀′ε₁)²(ε/a_j)²a_j^{−2}, which is below the bound of the gradient term, since (ε/a_j)² ≤ (ε/a_j)^β and O(1)C₀′ε₁ ≤ 1 for γ small.
      - {#W12.56} So, with the lift bounds at the global layer (below), osc_p(TF) at ι_Y(U_{1,2}) ≤ O(1)C₀′ε₁(ε/a_j)^{β_o}a_j^{−2}, β_o := min(β, 1 − 2ε₀), with (ε/a_j)^{β_o} in place of ε/a_j; the base term of W_0 is in C₀′ε₁ (defined in the bootstrap below).
        {#W12.56-1} The divergence-form bound of ∇b₁ at the pairs of 𝐇″_k therefore reads |K| ≤ O(1)(ε/a_j)^{β_o}C₀′ε₁a_j^{−2}.
        {#W12.56-2} The terms built from it carry (ε/a_j)^{β_o} ≤ (ε/a_{m(ω)})^{γ_w} in place of ε/a_j, since j ≥ m(ω) and γ_w = min(β, (1 − ε₀)/3) ≤ β_o for ε₀ ≤ 2/5.
        {#W12.56-3} This is within δ_w(ω) of §8, with C_ℬ, C(β₂), and C(ε₀), constants of L, d, G, β, ε₀, and Bałaban's constants (#W12.76; B_ι depends on d and L only, PBG p.423 l.28), and C(ε₀) also of M₁, M′ (through C_ι), and R_ι (#W12.42-6), in C_w.
      - {#W12.57} *The lift bounds at the global layer.* 10.5's real-point bounds at V′V₀, (H_ℒ) and the Hölder bound of leg 2, are stated for data G^Af and G^A(·, x) vanishing near the collar of Y^∼ (10.5, *The bound.*), with norms at the local-shell scale L^nε.
        {#W12.57-1} Here the data v := B′/ε are global and are read at the global layer a_j.
        {#W12.57-2} The bounds are rerun in this normalisation.
        - {#W12.58} The collar.
          {#W12.58-1} Let χ be the function of the coarse sites equal to 1 at distance ≤ ⅓M₁a_k from Y, to 0 at distance ≥ ⅔M₁a_k, and linear in the distance between, so |∇χ| ≤ 3(M₁a_k)^{−1}.
          {#W12.58-2} The count of 10.5's *The inclusion.* with ⅓M₁a_k for M₁a_k puts the (⅔M₁a_k + 3ε)-neighbourhood of Y in Ω₁(Y^∼) under M₁(L/3 − 1 − R_ι/L) > 3, with R_ι = 4dL + 1 as in *The inclusion.*; it holds under L ≥ 12d + 6 and M₁ ≥ 4, since then L/3 − 1 − R_ι/L ≥ 1 − 1/L ≥ 5/6.
          {#W12.58-3} So χv vanishes near the collar, as 10.5 requires.
          {#W12.58-4} Since a_j ≤ a_k, |χv| ≤ |v| and |∇(χv)| ≤ |∇v| + 3|v|(M₁a_k)^{−1}, at most O(1) times the bounds of v below at the same layer for M₁ ≥ 3 (the bounds of |v| and |∇v| carry different O(1)s).
          {#W12.58-5} The β₂-quotient of ∇(χv) is at most O(1) times that of v, except on the shell ⅓M₁a_k ≤ dist(·, Y) ≤ ⅔M₁a_k, where the jumps of ∇χ give it at most 6|v|(M₁a_k)^{−1}ε^{−β₂} more: |∇χ(x) − ∇χ(y)| ≤ 2 sup|∇χ|, since the gradient of the distance to Y can reverse its direction inside the shell.
          - {#W12.59} The constant.
            {#W12.59-1} Let K_M := e^{δ₁/2}max{1, (72/(eδ₁M₁))³}.
            {#W12.59-2} Since x^ne^{−cx} ≤ (n/(ec))^n for x ≥ 0, it bounds (a_k/ε)²e^{−δ₁M₁a_k/(24ε)} ≤ (48/(eδ₁M₁))² and e^{δ₁/2}(a_k/ε)³e^{−δ₁M₁a_k/(12ε)} ≤ e^{δ₁/2}(36/(eδ₁M₁))³, the two uses below, since (48y)² ≤ max{1, (72y)³} for y > 0.
            {#W12.59-3} By (F-ι) below, δ₁M₁ ≥ 4((3 + β₂)log L + log 2)/L, so K_M is at most a constant of L and δ₁, which C_ℒ″ of *The terms.* contains.
          - {#W12.60} The shell.
            {#W12.60-1} As a local quantity at a shell point c, ε^{β₂} times the excess is at most O(1)ε₂a_{j(c)}^{−1}(M₁a_k)^{−1} ≤ O(1)ε₂a_{j(c)}^{−2}, since a_{j(c)} ≤ a_k and M₁ ≥ 1.
            {#W12.60-2} On the shell d_ε(c, Y) ≥ ⅓M₁a_k/ε, so e^{⅛δ₁d_ε(c,Y)} ≥ e^{δ₁M₁a_k/(24ε)} ≥ K_M^{−1}(a_{j(c)}/ε)², and the weight ω of *The bootstrap.* satisfies ω(c) ≥ K_M^{−1}(a_{j(c)}/ε)².
            {#W12.60-3} So the excess is at most O(1)K_Mε₂a_{j(c)}^{−2}(ε/a_{j(c)})^βω(c), since (a/ε)^β ≤ (a/ε)².
            {#W12.60-4} It enters the sums of *The layers.* as the other weakened local quantities of *The normalisation.* do.
          - {#W12.61} The crude part.
            {#W12.61-1} (1 − χ)v vanishes within ⅓M₁a_k of Y. At a point x of Y^∼ let D := d_ε(x, Y), and let D′ be the distance of x from the support of (1 − χ)v in the units ε, so D + D′ ≥ ⅓M₁a_k/ε. 10.5's crude bound |∇_Bℒ_ιw(x)| ≤ B_ιε^{−1}Σ_ce^{−½δ₁d_ε(x,c)}|w(c)|, with a rate ¼δ₁ of the kernel paying the sum over c, gives it at most O(1)B_ιε^{−1}e^{−¼δ₁D′}sup|v| ≤ O(1)B_ιε₂ε^{−2}e^{−¼δ₁D′}, with sup|v| ≤ O(1)ε₂/a_{min} and a_{min} ≥ ε.
            {#W12.61-2} At every x, relative to ε₂a_j^{−2}ω(x), j = j(x), this is at most O(1)B_ι if ω(x) = (a_j/ε)², and otherwise, with ω(x) = e^{⅛δ₁D}, at most O(1)B_ι(a_j/ε)²e^{−⅛δ₁(D + D′)} ≤ O(1)B_ι(a_k/ε)²e^{−δ₁M₁a_k/(24ε)} ≤ O(1)B_ιK_M.
            {#W12.61-3} At x within 2ε of X ⊂ Y, D ≤ 2, so D′ ≥ ⅓M₁a_k/ε − 2, and relative to ε₂a_j^{−2}(ε/a_j)^β it is at most O(1)B_ι(a_j/ε)^{2+β}e^{−¼δ₁D′} ≤ O(1)B_ιe^{δ₁/2}(a_k/ε)³e^{−δ₁M₁a_k/(12ε)} ≤ O(1)B_ιK_M, since a_j ≤ a_k and β < 1.
            {#W12.61-4} Its oscillation is at most twice its supremum.
            {#W12.61-5} The interface-twist term of dι_Y lies outside the (⅔M₁a_k)-neighbourhood of Y, by the inclusion above, and is bounded in the same way.
        - {#W12.62} The normalisation. 10.5's pointwise bounds, the refined gradient and the bullets of *The Hölder bound.*, are sums Σ_ce^{−½δ₁d_ε(x,c)} of local quantities at c.
          {#W12.62-1} These are |∇_Av(c)|, ε^{β₂}‖∇_Av‖_{β₂} near c, ε|F||v|(c), the term ε²|H*J||v|(c) of Δ_π^{(2)}, and the shell excess of *The collar.* The scale L^nε enters only through the shell bounds of ε|F| and of the current, and through the final normalisation (L^nε)^β.
          {#W12.62-2} At a point c of the global layer j(c) the bounds of B′ above give |v| ≤ O(1)ε₂a_{j(c)}^{−1}, |∇_Av| ≤ O(1)ε₂a_{j(c)}^{−2}, and ‖∇_Av‖_{β₂} ≤ C(β₂)ε₂a_{j(c)}^{−2−β₂}.
          {#W12.62-3} The curvature is ε|F(W_t)| ≤ 2C₀′ε₁εa_{j(c)}^{−2}ω(c) under the bootstrap below.
          {#W12.62-4} The current satisfies |H*J(W_t)| ≤ O(1)L³[M′α₀a_j^{−3} + B_ιC(ε₀)ε₁(ε/a_j)^{1−2ε₀}ε^{−1}a_j^{−2} + B_ιC_ℬε₂ε^{−1}a_j^{−2}ω(c) + LC_ιε₁ε^{−3}e^{−δ′dist(c,Ω₁^c)/ε}] at c in the layer j = j(c), with α₀ PBG's parameter of §8, stage 4 (not the bootstrap's α₀^W).
          {#W12.62-5} Its four parts are run B's class current (3.36) at the (k + 1)-step minimiser with V₀'s data, PBG's O(1)Mα₀(L^jη)^{−3} (p.396 l.29) with PBG's M the block size M′; the T-part of W_0, the field of *The base at the layer j.*, read through H*J = (DH)*X with |X_T| ≤ O(1)(|∇T| + |F||T|) as in 10.5's last bullet, where (DH)* at the one-step scale costs ε^{−1}; the change from W_0 to W_t, through the first differences of ℒ_ι(c_s)B′, with the same cost ε^{−1};
          {#W12.62-6} and the tail of ι_Y against ι away from X (the W_0 bullet above), read in the same way through |∇T| ≤ 2L|T|/ε ≤ 2LC_ιε₁ε^{−2}e^{−δ_ιdist/ε} ≤ 2LC_ιε₁ε^{−2}e^{−δ′dist/ε} at the source points c′; (DH)* has the rate ½δ₁ (PBG (3.133)), so moving the profile from c′ to c costs e^{δ′d_ε(c,c′)} ≤ e^{⅛δ₁d_ε(c,c′)}, the factor e^{−⅛δ₁d_ε(c,c′)} of the kernel pays it, and the remaining rate ⅜δ₁ pays the sum over c′, whose constant is at most the crude part's sum constant at the rate ¼δ₁ in C_ℒ″ (#W12.61-1, #W12.76).
          {#W12.62-7} After the factor ε²|v| of Δ_π^{(2)}, with |v| ≤ O(1)ε₂a_j^{−1}, the four parts contribute O(1)L³ times M′α₀(ε/a_j)², B_ιC(ε₀)ε₁(ε/a_j)^{2−2ε₀}, B_ιC_ℬε₂(ε/a_j)ω(c), and LC_ιε₁(a_j/ε)e^{−δ′dist(c,Ω₁^c)/ε} relative to ε₂a_j^{−2}.
          {#W12.62-8} The last is at most LC(ε₀)K_Tε₁(ε/a_j)ω(c), with the factor C_ιe^{δ_ι(R_ι/L + 2)M₁} in C(ε₀) as in the W_0 bullet (#W12.42-5–#W12.42-7), by the two cases of that bullet: (a_j/ε) = (ε/a_j)ω(c) if ω(c) = (a_j/ε)², and otherwise (a_j/ε) ≤ (ε/a_j)(a_k/ε)² and (a_k/ε)²e^{−δ′(M₁a_k/ε − D)} ≤ K_Te^{δ′D} ≤ K_Tω(c).
          - {#W12.63} The weakening.
            {#W12.63-1} Before the sums, each local quantity other than |∇_Av| is weakened to the form Kε₂a_{j(c)}^{−2}(ε/a_{j(c)})^βω(c), using ω ≥ 1, so that its bound scales as a_{j(c)}^{−2−β}; |∇_Av| ≤ O(1)ε₂a_{j(c)}^{−2}ω(c) scales as a_{j(c)}^{−2}.
            {#W12.63-2} For ε^{β₂}‖∇_Av‖_{β₂} ≤ C(β₂)ε₂a^{−2}(ε/a)^{β₂} this uses β < β₂; for ε|F||v| ≤ O(1)C₀′ε₁ε₂a^{−2}(ε/a)ω it uses C₀′ε₁ ≤ 1; for the four parts of ε²|H*J||v| it uses M′α₀ ≤ 1 by R₀M₀M′α₀ ≤ 1 (§8, stage 4, where 10.5 writes M for M′), C(ε₀)ε₁ ≤ C(ε₀)K_Tε₁ ≤ C₀′ε₁ ≤ 1 with K_ℬ ≥ K_T ≥ 1 (*The bootstrap.*), C_ℬε₂ ≤ C_ℒ″C_ℬε₂ ≤ 1 with C_ℒ″ ≥ 1, and the exponents 2, 2 − 2ε₀, 1, and 1, all ≥ β; the shell excess has this form by *The collar.* The factors O(1)L⁴, B_ι, and K_M are in C_ℒ″ of *The terms.*
        - {#W12.64} The layers.
          {#W12.64-1} The kernel's rate ½δ₁ is split as ¼δ₁ + ⅛δ₁ + ⅛δ₁.
          {#W12.64-2} Across a layer boundary the bound of a weakened local quantity changes by the factor L^{2+β} ≤ L^{3+β₂}, and that of |∇_Av| by L².
          {#W12.64-3} The weight satisfies ω(c) ≤ ω(x)max{e^{⅛δ₁d_ε(x,c)}, L^{2(j(c)−j(x))}}, since d_ε(c, Y) ≤ d_ε(x, Y) + d_ε(x, c) and (a_{j(c)}/ε)² = L^{2(j(c)−j(x))}(a_{j(x)}/ε)².
          - {#W12.65} Towards a coarser c, j(c) > j(x), the bound of the local quantity falls by at least L^{−2(j(c)−j(x))}, which pays the second entry, and the rate ⅛δ₁ pays the first.
          - {#W12.66} Towards a finer c, j(c) < j(x), the second entry is below 1 and the rate ⅛δ₁ pays the first.
            {#W12.66-1} The bound of the local quantity grows by at most L^{3+β₂} per layer boundary.
            {#W12.66-2} The layers are at least LM₁ wide in their own units, hence in the units ε of d_ε, so the rate ¼δ₁ pays the growth under
            {#W12.67} (F-ι) ¼δ₁LM₁ ≥ (3 + β₂)log L + log 2,
            {#W12.68} a lower bound on LM₁ of the same kind as the LF note's (F-W), met by the same choices before γ.
          - {#W12.69} The remaining rate ⅛δ₁ pays the sum over c, a constant of δ₁ and d in C_ℒ″.
          {#W12.70} So the sums are at most O(1)L^{3+β₂} times the bounds at the layer j of x, with ω(x) in place of ω(c), at every x of Y^∼.
        - {#W12.71} The terms.
          {#W12.71-1} Every term of 10.5's decomposition ℒ_ιv = Iv + H₁(𝔡v − QIv) − C̃₁G₁^{−1}Iv other than Iv has, at every x of Y^∼, a supremum at most O(1)L^{3+β₂}C_ℒ″(1 + C(β₂))ε₂a_j^{−2}(ε/a_j)^βω(x), by *The weakening.* and the sums of *The layers.* The crude part of *The collar.* adds at most O(1)B_ιK_Mε₂a_j^{−2}ω(x) at every x, and O(1)B_ιK_Mε₂a_j^{−2}(ε/a_j)^β at x within 2ε of X. The bounds come from these sources:
          - {#W12.72} H₁(𝔡v − QIv), through |h| ≤ Cε(6√dε)^{β₂}‖∇_Av‖_{β₂} + max(C, 1)C_trε²|F||v|;
          - {#W12.73} C̃₁D*(DP_πIv) and C̃₁DRD*Iv, through (3.44) at ε_H = ½ applied to λ − λ_x and μ − μ_z, so that the local constant of the source is subtracted and only ε^{β₂}‖λ‖_{β₂} and O(1)ε²|F||λ| remain;
          - {#W12.74} Δ′P_πIv, through ε|F||v|; and
          - {#W12.75} Δ_π^{(2)}Iv, through ε²|H*J||v|.
          {#W12.76} Here C_ℒ″ ≥ 1 is a constant of L, d, G, δ₁, B₀, B₀′(½), B_ι, C₂, C_tr, and c_F; it contains the factors O(1)L⁴, B_ι, and K_M of *The normalisation.* and *The collar.*, the constant of the sum over c in *The layers.* and that of the crude part's sum over c at the rate ¼δ₁ in *The collar.*, and the factor L² between the units of F and of the first differences (*The bootstrap.*).
          {#W12.76-1} The fine differences of Iv oscillate over a box of side 2ε by at most the oscillation of ∇_Av over a coarse cell of side 6ε, plus 4C_trε|F||v| (the Cauchy note's #C10.4.109-5, with its transport term as in #W10.5.27).
          {#W12.76-2} That is at most (6√dε)^{β₂}C(β₂)ε₂a_j^{−2−β₂} + O(1)C_trC₀′ε₁ε₂(ε/a_j)a_j^{−2}ω(x), by |v| ≤ O(1)ε₂a_j^{−1} and ε|F| ≤ 2C₀′ε₁εa_j^{−2}ω (#W12.62-2, #W12.62-3).
        - {#W12.77} The bootstrap.
          {#W12.77-1} Let C₀′ε₁ := K_ℬ(C₀ + C(ε₀))ε₁ + C_ℬC(β₂)ε₂ with K_ℬ a fixed constant of d, L, δ₁, and δ_ι, at least O(L)K_T (the base bound carries the L-powers of §11's cube fitting and the tail away from X of the W_0 bullet), C_ℬ := O(1)L^{3+β₂}C_ℒ″(1 + C(β₂)) (a constant of this bullet, distinct from 10.1's C_ℒ′), and impose C_ℒ″C_ℬε₂ ≤ 1, a smallness condition met for γ small.
          {#W12.77-2} Here and below the first differences of a field of link variables are in the units ε^{−2}: ε^{−2} times the dimensionless differences of the link variables, so that the bound ε₂(ε/a_j)² of B′ above reads ε₂a_j^{−2}.
          {#W12.77-3} The fine curvature F on T_{ε/L} is (L/ε)² times the dimensionless plaquette angle, so the two conventions differ by the factor L², which C_ℒ″ and C_ℬ contain.
          - {#W12.78} The weight.
            {#W12.78-1} Let ω(c) := min{(a_{j(c)}/ε)², e^{⅛δ₁d_ε(c,Y)}} at the points and plaquettes c of Y^∼.
            {#W12.78-2} Then 1 ≤ ω(c) ≤ (a_{j(c)}/ε)², and ω ≤ e^{δ₁/4} within 2ε of Y.
          - {#W12.79} The hypothesis.
            {#W12.79-1} Suppose that for s ≤ t, at every c of Y^∼, |F(W_s)(c)| < 2C₀′ε₁a_{j(c)}^{−2}ω(c) and the first differences of ℒ_ι(c_s)B′ at c are less than 2C_ℬε₂a_{j(c)}^{−2}ω(c), the latter entering the current part of *The normalisation.* Since ω ≤ (a_j/ε)², |F(W_s)| < 2C₀′ε₁ε^{−2} on all of Y^∼.
          - {#W12.80} The class.
            {#W12.80-1} Then W_s is in PBG's class (3.35)–(3.36) (p.396 l.15–32) of the one-step problem, whose layers have the spacings ε/L and ε and whose cubes □ have the side O(1)M′ε.
            {#W12.80-2} In the axial gauge of each □, |A| ≤ O(1)M′ε|F|; |∇A| ≤ O(1)dLM′|F|, since the lattice gradient at the spacing ε/L gives |∇F| ≤ (2L/ε)|F|; and |∂*∂A| ≤ (4dL/ε)|∇A|.
            {#W12.80-3} With |F| < 2C₀′ε₁ε^{−2} (ε₁ the data parameter of (9.2) as below) and ε/L ≤ L^iη ≤ ε at the layer i of □, these are the bounds of (3.35)–(3.36) with α₀^W := O(1)d²L²C₀′ε₁ in place of PBG's α₀, on all of Y^∼.
            {#W12.80-4} PBG asks that O(1)M′α₀^W be small (p.396 l.32); here this is §8's O(1)L⁵M′α₀^W ≤ a₁/2.
            {#W12.80-5} PBG Theorem 3.12 asks α₀^W sufficiently small (p.423 l.29–30, l.34), below the absolute constant for which the series (3.138) converges.
            {#W12.80-6} Both hold for γ small (§8, stage 6).
            {#W12.80-7} So PBG Theorem 3.12 applies at W_s.
          - {#W12.81} The closure.
            {#W12.81-1} The terms give, at every x of Y^∼, sup|D_{W_t}ℒ_ι(c_t)B′| ≤ C_ℬε₂a_j^{−2}ω(x) and first differences of ℒ_ι(c_t)B′ at most C_ℬε₂a_j^{−2}ω(x), the current part entering with the factor ε₂(ε/a_j), and |Q_t| ≤ O(1)c_{br}ε₂(ε/a_j)2C₀′ε₁a_j^{−2}ω(x). |F(W_0)| ≤ O(1)(C₀ + C(ε₀))ε₁a_j^{−2} + O(L)C(ε₀)K_Tε₁a_j^{−2}ω(x) ≤ O(L)K_T(C₀ + C(ε₀))ε₁a_j^{−2}ω(x) by (9.2), *The base at the layer j.*, and the tail away from X of the W_0 bullet, since ω ≥ 1 and K_T ≥ 1.
            {#W12.81-2} So |F(W_t)| ≤ |F(W_0)| + C_ℬε₂a_j^{−2}ω(x) + |Q_t| < 2C₀′ε₁a_j^{−2}ω(x) for K_ℬ at least the O(L)K_T of the base and γ small, since C(β₂) ≥ 1. dF/dt is bounded uniformly in t and in the plaquettes by the same bounds, so the suprema of |F|/(a_j^{−2}ω) are continuous in t; the first differences of ℒ_ι(c_t)B′, the second bootstrap quantity, are continuous in t on the finite lattice by the analyticity of the lift in the data (VAR Proposition 9, whose hypothesis, the smallness of V′, holds for all t);
            {#W12.81-3} both strict bounds hold at t = 0, where the change from W_0 vanishes and |F(W_0)| is bounded without the hypothesis; so the bounds carry to t = 1.
        - {#W12.82} The result.
          {#W12.82-1} At a box of side 2ε within 2ε of X, where ω ≤ e^{δ₁/4}, the oscillation of the fine curl of ℒ_ι(c_t)B′ is at most C_ℬC(β₂)ε₂(ε/a_j)^βa_j^{−2}, by *The terms.*, with the crude part there at x within 2ε of X, and the fine differences of Iv, since β < β₂ and C₀′ε₁ ≤ 1, with e^{δ₁/4} absorbed into C_ℬ.
          {#W12.82-2} The bound |F(W_1)| ≤ O(1)C₀′ε₁a_j^{−2} of the transport bullet is the bootstrap at t = 1 at these boxes.
          {#W12.82-3} These are the inputs used above, at the global layer and on the whole band, the cut included, since χ, the layers, and §9.7 use no property of the cut.
      - {#W12.83} Q_t includes the gauge part D_Bγ, the dlog term, and the change of frame T_1/T_0 between W_0 and W_1, all of order ≤ O(dL)c_{br}ε₂(ε/a_j)C₀′ε₁a_j^{−2}; the gauge part rotates the TF of the box together.
        {#W12.83-1} In the gradient entry ∇G∇*, (ε/a_j)^{β_o} becomes (ε/a_j)^{β_o−β′}, which fits δ_w for 0 < β′ ≤ β_o − γ_w.
        {#W12.83-2} This needs β_o > γ_w, so the Hölder exponent needs β ∈ ((1 − ε₀)/3, 1) with ε₀ < 2/5, which §8's stage 0 (β ∈ [3/4, 1), 0 < ε₀ < 1/125) covers.
        {#W12.83-3} The smallness O(1)C₀′ε₁ ≤ 1 holds for γ small: the ε₁ of (9.2) here is the data parameter of V₀'s problem, O(1)B₃²B₅M⁶ε_k by *The background pairs.*, which tends to 0 with γ, and ε₂ tends to 0 with γ (*10.5's premise at 𝐇″_k.*).
      {#W12.84} The pair is (ι_Y(U_{1,2}), U_{1,2}), reached from the base pair (ι_YV₀, V₀) along c_t, with the localised lift ι_Y throughout.
- {#W12.85} The operators.
  {#W12.85-1} PBG's Theorems 3.1–3.3 and (3.133) hold for each problem at its background, by PBG Corollary 3.6 and the general theorems at real configurations satisfying (3.35)–(3.36), given the layer widths.
  {#W12.85-2} For 𝐁″_k's middle layers h + 1 ≤ j ≤ k − N₀ the width is at least 3LMR_{j+1} in their own units (the LF note's *The middle layers.*, its #4.317-0); at the joins the widths are LM₁, under (J-W).
  {#W12.85-3} For 𝐁₁, Bałaban separates U_{𝐁₁} from U_{𝐁₂} "by the boundary conditions" (p.370 l.22–25): the problem is posed on Ω″^∼_{h+1}, with the collar's fine data layers inside it.
  {#W12.85-4} Its operators carry the Dirichlet condition outside Ω″^∼_{h+1}, in the same sense as all of PBG's operators on their Ω₀ (PBG p.394 l.29–36: "All operators we will consider will be defined by using Dirichlet boundary conditions on Ω_0").
  {#W12.85-5} The difference from the local problems of one cube □ is that at ∂Ω″^∼_{h+1} the two runs' finest domains share their boundary, so the margin of the local shells that gives 10.1's (S) (*The condition (S).*) is missing there.
  {#W12.85-7} The collar's strip, where (S) is missing, is bounded run by run without (S) in *The collar and the strips.* below, and the walks whose local problems reach ∂Ω″^∼_{h+1} are compared without (S) in *The collar at ∂Ω and at the reflex edges.*
- {#W12.86} The fixed points.
  {#W12.86-1} §11, with *The current term of VAR (143).* and *The Sects. D–E form (111).*, holds for any determining set with the alignment above and any operators with VAR's bounds (*The inverse of the linearising transformation.* uses no property of H beyond (53)–(54)).
{#W12.87} So (β) reduces to (W-δ) and §11 at the aligned pairs on the layers at shared scales ≥ 1: for 𝐇_k at (ι(U^A_k), U^A_k), for 𝐇″_k at (ι(U^A_{1,2}), U^A_{1,2}) in the (111) form, and for 𝐇_{𝐁₁} at (ι(U^A_{k,Λ}), U^A_{k,Λ}) in the (111) form.
{#W12.87-1} The collar of 𝐁₁ and the finest-scale strips of the sets 𝐁(Y_i) are bounded run by run below, and the source of (1.55) in 𝐇″_k, which reads the 𝐁₁ problem, is compared below.

{#W12.88} *The gauge transformations.* CMP 98 (106) writes u(x) as an ordered product over the scales j = k − 1, …, 0 of one-step factors.
{#W12.88-1} The factor of the scale j is R(U₀(Γ^{(j+1)}_{x_{j+1},x}))^{−1} times the return to the axial gauge of the j-fold double bar on the block of x_{j+1}, a function of the configuration on that block.
{#W12.88-2} In run B the product has one more factor, of its scale 0.
{#W12.88-3} By CMP 98 (91), the (j + 1)-fold double bar of run B is the j-fold double bar about MU^B of the one-step double bar ((B4) of the Cauchy note's §10.1).
{#W12.88-4} So run B's factors of the scales j + 1 ≥ 1 are run A's factors of the scales j, evaluated at the one-step double bar e^{iεY}MU^B of run B's configuration e^{iη_B𝐇^B}U^B (Y is defined through the double bar, whose linear part is §11's Q₁), and
  {#W12.89} u^B(x) = u^A[e^{iεY}V₀](x)·f^B_0(x)
{#W12.90} at run A's sites x, the only sites read on the layers at shared scales ≥ 1, with f^B_0 run B's factor of the scale 0, the return to the axial gauge of one fine block.
{#W12.90-1} At a general fine site, with x₁ the run-A site of its block, u^B(x) = R(U^B(Γ_{x₁,x}))^{−1}[u^A[e^{iεY}V₀](x₁)]·f^B_0(x).
{#W12.90-2} Throughout, run B's background is ι_YV₀, the background of ℒ_ι, and Q₁ := Q̄₁(ι_YV₀).
{#W12.90-3} Then:
- {#W12.91} f^B_0 depends only on the configuration on one block of side ε.
  {#W12.91-1} It is (R_{0,x}U₁)‾^{−1} of CMP 98 (82) and (87) at one step, an average of products of at most O(1)L fine bonds, so |Ad(f^B_0) − 1| ≤ O(1)Lη_B sup_{block}|𝐇^B|, as for g in 10.5.
  {#W12.91-2} Since |𝐇^B| ≤ |𝐇^B|_{(−1)}a_j^{−1} at the layer j, this is ≤ O(1)(ε/a_j)|𝐇^B|_{(−1)}, with the factor ε/a_j of the layer.
- {#W12.92} The argument.
  {#W12.92-1} By §11, Y = Q₁𝐇^B + c₁ and Y − 𝐇^A = Q₁(𝐇^B − ℒ𝐇^A) + c₁ = Q₁(𝐇^B − ℒ_ι𝐇^A) + c₁, since Q₁ℒ = 1 on the bonds of Y^∼ (§11, *The global lift.*) and Q₁ℒ_ι = 1 on the data of Λ₁ (10.5, *The exactness.*), which contain the bonds read by u: these lie in Y_i ⊂ Y, at distance ≥ M₁a_k from Λ₀.
  {#W12.92-2} Put δ := Q₁(𝐇^B − ℒ_ι𝐇^A) + c₁.
  {#W12.92-3} At a point x of the layer j(x), (106) is applied on the block of 𝐁″_k containing x, of the scale j(x), and runs over the scales j′ < j(x).
  {#W12.92-4} This is Bałaban's statement: "u^0_k(x) is an analytic function of 𝐇″_k restricted to this block of the set 𝐁″_k, to which the point x belongs.
  {#W12.92-5} This function is given by the explicit formula (106) [12]" (LFR II p.373 l.30–31).
  {#W12.92-6} The block of the scale j′ containing x lies in the block of the scale j(x) containing x, hence in Ω_{j(x)}, where |δ| ≤ |δ|_{(−1)}a_{j(x)}^{−1}.
  {#W12.92-7} The factor of the scale j′ is an analytic function of the configuration on its block, whose linear part is the block average.
  {#W12.92-8} It has the Lipschitz constant O(1)L^{j′+1}ε.
  {#W12.92-9} In the units of the block of the scale j(x), the field has |A| ≤ |𝐇|_{(−1)}, and CMP 98 Proposition 4 (p.38–39) makes the angles Q_{j′}(U_0, ηA) of the j′-fold double bar analytic in A for |A| < c₄, with |Q_{j′}(U_0, ηA)| < 2α₁L^{j′}η for |A| < α₁ ((131), p.38).
  {#W12.92-10} A Cauchy estimate on |A| < ½α₁ gives the Lipschitz constant 4L^{j′}η for these angles.
  {#W12.92-11} By (105)–(106) (p.33), the factor of the scale j′ is a product near 1 of the inverse block average of at most O(d)L such angles and of the angles along Γ_{x_{j′+1},x_{j′}}, of length at most dL, which gives O(1)L^{j′+1}η with η = ε/a_{j(x)} in these units.
  {#W12.92-12} So the factor changes by at most O(1)L^{j′+1−j(x)}|δ|_{(−1)}, and the sum over j′ < j(x), at most L/(L − 1), gives |u^A[e^{iεY}V₀](x) − u^A[e^{iε𝐇^A}V₀](x)| ≤ O(1)|δ|_{(−1)}.
  {#W12.92-13} The identity u^B = u^A[e^{iεY}V₀]·f^B_0 also omits a small term: the prefactors R(U_0(Γ^{(j+1)}_{x_{j+1},x}))^{−1} of (106) are transports of the fine background, of ι_YV₀ along run-B contours in run B and of V₀ = MU^B along run-A contours in run A. V₀ is an average, not a restriction, so they differ by O(ε/a_j) per scale (the flux through the area between the contours, as in *The run difference of the gauge change.*), which enters multiplied by the deviation of the scale-j′ factor from 1, at most the size of its angle, O(1)ε_k.
  {#W12.92-14} Summed over the scales j′ < j(x) with the ratio L^{−1}, this adds O(1)(ε/a_{j(x)})ε_k to the run difference of u, which fits δ_w(ω) as the other terms of order ε/a_j do.
- {#W12.93} The fine side. u enters (1.61)–(1.63) as (u)_−^{−1}exp i Q̃(η𝐇)R((u)_+), acting on the data of the boundary layer (p.373 l.20, l.39; p.374 l.17).
  {#W12.93-1} On the layers at shared scales ≥ 1 these values are read at run A's sites, the values compared above.
  {#W12.93-2} At a finest-scale layer of a boundary-layer set, run B has an extra layer with no counterpart in run A; it is bounded run by run in *The collar and the strips.* below.
{#W12.94} So, on the layers at shared scales ≥ 1, the run difference of u^0_k, u_1, and u_{k,Λ} is bounded by (W-δ) for the corresponding function (the form (c) with the bridge, and §11's Δ_𝐇), by C₂L²L^{−j} from c₁, and by O(1)(ε/a_j) from f^B_0.
{#W12.94-1} On the young histories every layer index is ≥ k/2 − 1 (§11, *The alignment of the global sets.*), so every one of these carries a positive power of L^{1−k/2}.
{#W12.94-2} At a scale-0 layer, ε/a_0 = 1 and the factor is lost.

{#W12.95} *The collar and the strips.*
{#WOG.6} **(Wδ-4) The collar of 𝐁₁ at the reflex edges of Ω and at ∂Ω.** The strip Ω ∖ Ω^A_2 at ∂Ω, Ω := Ω″^∼_{h+1}, is bounded below run by run through the crossing decay from the strip to the collar's layers n ≥ 2.
{#WOG.6-1} The collar's layers are CRE's maximal domains, separated in the ℓ¹ distance (CRE p.256 l.57–62, PRT2 p.223 l.16), and are only one cube of the next scale wide.
{#WOG.6-2} First, near a reflex edge of Ω (a face of ∂Ω of codimension ≥ 2 along which Ω^c is locally a convex wedge), for every n′ ≤ h a cube of 𝒟_{n′} touches the edge while it contains a block of the layer n′: for Ω^c = {x₁, x₂ ≤ 0} near the edge, □ = [0, 2c_{n′}]^d contains Q = [c_{n′}, 2c_{n′}]^d, whose ℓ¹ distance from the complement of the domain of the layer n′ − 1 is at least 2c_{n′} − dc_{n′}/(L − 1) ≥ c_{n′} for L > 2d.
{#WOG.6-4} So the decay of such a cube's local operator, read at the single scale n′, gives no crossing between the strip and the layer n′.
{#WOG.6-5} Second, the walks whose cubes have Ω₀(□) meeting ∂Ω are compared through local problems that reach ∂Ω, where 10.1's (S) is not available.
{#WOG.6-6} These cubes are not a corner effect: at a flat face, Ω₀(□) ⊇ □̃⁴ meets ∂Ω for a fraction of order 4/L of every collar layer n′ = 2, …, h − 1.
{#WOG.6-7} Third, §11's 𝔡_H is built from global suprema, which for 𝐁₁ include the strip, so for H_{𝐁₁}, 𝔊, 𝐇_{𝐁₁}, and the source of (1.55) it has no decay in h.
{#WOG.6-8} The same occurs at the reflex edges and the boundaries of the boundary-layer sets Y_i (the finest-scale strips of the 𝐁(Y_i)).
{#WOG.7} *The requirement.* The consumer charges each point of a history with h_n = C_hθ̃^n, n the history's birth scale (the Cauchy note, #C8.6.2-6), and the cut lies in the history's layer h ≥ n.
{#WOG.7-1} So a collar term needs a run difference ≤ C(ε/a_h)^γ times Bałaban's bound of the term, for an exponent γ > 0 for which the other terms already fit (§8); no new rate enters θ̃.
{#W12.96} *The collar at ∂Ω and at the reflex edges.* The paragraphs below on the collar use the following, which holds at the reflex edges and at the boundary of the set concerned (Ω or Y_i).
{#W12.96-1} These paragraphs are *The strip.*, *The enlargement-only walks.*, *The representation with the gain.*, *The sources.*, *The weight.*, (D2), the run difference of the source of (1.55), and the finest-scale strips of the sets 𝐁(Y_i).
{#W12.96-2} The collar of Y^∼ does not enter V(Y): run B's terms are functions of the right side of (1.55) (*The source of (1.55).*, *Run B's terms contain no d^B*).
{#W12.96-3} It is stated for Ω := Ω″^∼_{h+1}.
{#W12.96-4} For Y_i it holds with their collars, built by the same construction (CRE p.256–257).
{#W12.96-5} Here m(x) denotes the collar's layer of a point x, indexed by run A's scales, with m(x) := h at the layers of 𝐁″_k ≥ h outside the collar, and ε/a_m = L^{−m}.
  - {#W12.97} The local problems.
    {#W12.97-1} Let □ be a cube of the collar's layer n′ whose Ω₀(□) leaves Ω or meets the collar's layers below n′ − 1, or whose □̃³ meets the layer n′ − 1, in particular a cube touching a reflex edge.
    {#W12.97-2} The last case makes □'s sequence agree with the collar's on □̃³, which the cells of 𝒟′ and 𝒟″ use (*The cells of 𝒟′ and 𝒟″ on the collar.* below).
    {#W12.97-3} (3.88) asks the local operator to agree with the global one where h_□ ≠ 0, including the layer index, the a_j, and the blocks B^j(y), and PBG's centred sequence does not achieve this there.
    {#W12.97-4} So its local problem is posed on Ω′_m(□) := Ω_m(□) ∩ Ω^{col}_m, the intersection of PBG's sequence with the collar's domains Ω^{col}_m of the scale m (Ω^{col}_0 := Ω), with Dirichlet conditions outside Ω′_0(□), in each run with its own collar.
    {#W12.97-5} This is the 𝐁₁ problem's constraint structure of *The operators.*, with the fine data layers inside Ω and the Dirichlet condition outside its finest domain (PBG p.394 l.29–36; PRT2 p.248 l.4), restricted to Ω₀(□).
  - {#W12.98} PBG's bounds for them.
    {#W12.98-1} The intersected sequence satisfies PRT2 (2.1)–(2.4) at the size R₀M₀: dist((Ω′_m)^c, Ω′_{m+1}) ≥ min(2R₀M₀, LM₁)L^mη = 2R₀M₀L^mη, and the domains are unions of R₀M₀-blocks of their scale.
    {#W12.98-2} Corollary 3.6 also asks that Ω′_0(□) lie in a cube of the class of (3.35) (p.408 l.6–9), whose cubes lie in two consecutive layers (p.396 l.14–17), while Ω′_0(□) spans the collar's layers 0, …, n′.
    {#W12.98-3} The proof of the corollary uses only (3.35) at the index n′ on a cube containing Ω′_0(□), through the gauge transformation u and Corollary 3.5 (p.408 l.1–5).
    {#W12.98-4} That regularity holds on □̃⁵. □̃⁵ lies in the collar, in 𝐁″_k's layer h near the cut, where the backgrounds are regular at the scale h: Bałaban's statement at LFR II p.370 l.35–38 for U_{1,2}, REG's 𝔘-membership at the index h with VAR (14)'s constant and with it PBG's (3.35)–(3.36) (*The background pairs.*), and VAR (9)–(10) at the layer h for U_k and U_{k,Λ}.
    {#W12.98-5} Regularity at the scale h ≥ n′ gives (3.35) at the index n′, in the axial gauge of the cube.
    {#W12.98-6} The cube fits for every n′ ≤ h.
    {#W12.98-7} In this passage M₁ is CRE's M₁ = KM′, the unit of the collar's width (§8), and PBG's cubes have the side 2M′a_{n′} ≤ 2M₁a_{n′}, with PBG's block size M′.
    {#W12.98-8} One big block of □ lies in B^{n′}(Λ_{n′}), within 2M₁a_h of the cut, and □ protrudes from it by at most its side 2M′a_{n′} ≤ 2M₁a_h, so □ lies within 4M₁a_h of the cut; □̃⁵ adds at most 5M′a_{n′} ≤ 6M₁a_h, so □̃⁵ lies within 10M₁a_h of the cut, at a distance ≥ 14M₁a_h from the band's boundaries, since the cut lies at a distance ≥ MR_{h+1}a_{h+1} ≥ 4LR_{h+1}M₁a_h ≥ 24M₁a_h from them under M ≥ 4M₁ and L > 5 (§11, the collar passage).
    {#W12.98-9} All these distances are ℓ∞ distances; where a separation is given in ℓ¹, its ℓ∞ value is at least 1/d of it, and the factor d is absorbed by R ≥ 12dL.
    {#W12.98-10} For VAR (9)–(10), □̃⁵ has the side 12M′a_{n′} ≤ 12M′a_h, so it lies in the cube of the side 12M′a_h concentric with □, and that cube lies in a cube of the side 14M′a_h that is a union of big blocks of the scale h (the grid of the side M′a_h; one block per side covers the offset), a cube of VAR's class of the side 2M_Va_h with M_V = 7M′ (VAR p.279 l.2 asks for unions of big blocks).
    {#W12.98-11} Here M_V is VAR's cube parameter, "a multiple of R₁M₁" with M_V ≤ M(ε₁) = R₁M₁(a₁/ε₁) (VAR p.279 l.2 and l.17, l.28), chosen per cube; it is not RG II's M. With R₁M₁ = M′ (§8), M_V = 7M′ is such a multiple, admissible once M(ε₁) ≥ 7M′, that is ε₁ ≤ a₁/7, as for the collar cells.
    {#W12.98-12} VAR's cube extends beyond □ by at most 6M′a_h − M′a_{n′} + 2M′a_h ≤ 8M′a_h ≤ 8M₁a_h (the concentric cube's excess and the alignment), so it lies within 12M₁a_h of the cut, and its concentric cube of the side (2M_V + 4R₁M₁)a_h adds 2M′a_h ≤ 2M₁a_h on each side, so it lies within 14M₁a_h of the cut and so in the two layers at the cut, at a distance ≥ 10M₁a_h from the band's boundaries.
    {#W12.98-13} Run B's background has the same regularity on Ω′^B_0(□) ⊂ □̃⁵. 10.5's *The base and the local gauge* derives (3.35)–(3.36) for ι(V₀) from V₀'s layer bounds through the argument of the Cauchy note's §9.7.
    {#W12.98-14} That argument is local in V₀ up to the tails of the one-step lift, which decay at its rate δ₀ in the fine units.
    {#W12.98-15} Run with V₀'s scale-h bounds on the band, it gives the scale-h regularity of ι(V₀) on □̃⁵.
    {#W12.98-16} The part of V₀ outside the band enters through those tails, at a distance ≥ 8M₁a_h.
    {#W12.98-17} With V₀'s crude bound ε₁ε^{−2} there, its contribution relative to the scale-h bound is at most L^{2h}e^{−8δ₀M₁L^h} ≤ (1/(4eδ₀M₁))² for the curvature, and, with the crude bound ε₁ε^{−3}, at most L^{3h}e^{−8δ₀M₁L^h} ≤ (3/(8eδ₀M₁))³ for the gradient and current entries of (3.36), by x^me^{−cx} ≤ (m/(ec))^m.
    {#W12.98-18} Both are ≤ 1 under δ₀M₁ ≥ 1.
    {#W12.98-19} The same argument applies to every collar cube whose Ω₀(□) does not lie in a cube of the class of (3.35).
    {#W12.98-20} These include the cubes that are not intersected but whose □̃⁵ enters the layer n′ − 1, since the collar's layers are only about L big blocks wide.
    {#W12.98-21} The argument uses only (3.35) at the index n′ on □̃⁵.
    {#W12.98-22} So Theorems 3.1–3.3 hold for these local operators, in the weighted distance d′ of PRT2 (2.46) for {Ω′_m(□)}.
  - {#W12.99} The cells of 𝒟′ and 𝒟″ on the collar.
    {#W12.99-1} §7 builds the sequences of the cells Q (□₀ in the second case, and 𝒟″'s cube □″) for the cells in the bulk, where PRT2 (2.2) separates the layers with R ≥ 12dL.
    {#W12.99-2} The collar's layers are only about L big blocks of their scale wide (CRE p.256 l.57–62), so a cube coarser than □₁ can meet □̃ or □̃₁ there, and a cube of the first case can meet a coarser cube.
    {#W12.99-3} The cells whose □̃⁵ or Q̃⁵ meets a layer of the collar are built as follows.
    {#W12.99-4} Each run builds them from its own collar by the same rule, so at the shared scales n ≥ 2 the two runs' sequences agree (Ω^A_n = Ω^B_{n+1}, *The collar's layers.*; run B's C^B_{n+1} is run A's C_n, and run B's C^B_0 adds the extra shell 2R₀M₀ε/L of §2), and where Ω′_0(Q) meets the strip they differ only at the strip's points, as for the intersected sequences (*The enlargement-only walks.*).
    {#W12.99-5} M₁ is PBG's block size KR₀M₀ (the M of §7), a_n = L^nη in run A's units, and distances are ℓ∞ distances unless stated.
    - {#W12.100} The cells and their partitions.
      {#W12.100-1} For □ ∈ 𝒟_j let j₀ be the coarsest layer among □₀ and the cubes removed at p.411 l.23–25.
      {#W12.100-2} If □₀ = □̃² and j₀ = j, □₀ takes □'s own sequence, as in §7's first case; this needs only that □'s sequence agree with the collar's on □̃³ (the agreement item below).
      {#W12.100-3} Otherwise □₀ is a cell Q with the base cube □ (first case) or □₁ (second case) and j_Q := j₀. 𝒟″'s cube □″ is a cell Q with the base cube □₀ and j_Q the coarsest layer among □₀ and the cubes of 𝒟′ removed at p.415 l.8. p_Q is the smallest union of big blocks of the scale j_Q that contains the base cube.
      {#W12.100-4} It is the base cube when the base cube's scale is j_Q.
      {#W12.100-5} Otherwise the base cube has a scale j′ < j_Q and is □ or □₁, of the side 2M₁a_{j′} ≤ M₁a_{j_Q}, so p_Q consists of at most 2^d big blocks of the scale j_Q, or □₀ = □̃² or □̃₁², of the side 6M₁a_{j′} ≤ 2M₁a_{j_Q} for L ≥ 3, so p_Q has the side ≤ 3M₁a_{j_Q}.
      {#W12.100-6} In every case p_Q contains the base cube, has the side ≤ 6M₁a_{j_Q}, and is a union of big blocks of the scale j_Q.
      {#W12.100-7} Q̃^n is the cube that extends p_Q by (n + 2)M₁a_{j_Q}, a union of big blocks of the scale j_Q.
      {#W12.100-8} The partition of a cell is §7's, with j_Q in place of j₀: a removed cube meets □̃, □̃₁, or □̃₀, which lie within M₁a_{j_Q} of p_Q, and has the side ≤ 2M₁a_{j_Q}, so its h_□ is supported within (8/3)M₁a_{j_Q} of p_Q. φ, at the scale j_Q, is 1 there and on □̃ (□̃ ⊂ □̃₁ for L ≥ 4), and supp φ lies in Q̃ with the margin (1/6)M₁a_{j_Q}.
      {#W12.100-9} The kept cubes do not meet □̃, so h′_Q = 1 on □̃, and the derivative bounds hold as in §7.
    - {#W12.101} The scales.
      {#W12.101-1} A cell with j_Q ≥ h + 1 is in the bulk: §7's Corollary 3.6 item, which uses only the separations of the layers ≥ h, puts its Q̃⁵ in Ω_{j_Q−1} ⊂ Ω_h.
      {#W12.101-2} A cube of a layer ≥ h + 1 lies in Ω_h at the distance ≥ (R/d)M₁a_h − M₁a_{h+1} ≥ 11M₁a_{h+1} from Ω_h^c under R ≥ 12dL, which no □̃, □̃₁, or □̃₀ of a cube of a layer ≤ h − 1 reaches, since these lie within 3M₁a_{h−1} + 5M₁a_h ≤ 6M₁a_h of Ω_h^c.
      {#W12.101-3} So the collar's cells have j_Q ≤ h.
      {#W12.101-4} Q̃⁵ meets Ω_h^c and has the side ≤ 20M₁a_h, while Ω_{h+1} lies at the distance > (R/d)M₁a_h ≥ 12M₁a_{h+1} from Ω_h^c, so Q̃⁵ ∩ Ω_{h+1} = ∅.
    - {#W12.102} The restricted sequence.
      {#W12.102-1} Let n_Q be the coarsest layer that meets Q̃, so n_Q ≤ h.
      {#W12.102-2} Let C_n := Q̃ for n ≥ n_Q, C_n the cube that extends Q̃ by Σ_{i=n}^{n_Q−1}2R₀M₀a_i for n < n_Q, and Ω′_n(Q) := Ω^{col}_n ∩ C_n, with Ω^{col}_n the collar's domains of *The local problems.* (Ω^{col}_0 := Ω).
      {#W12.102-3} Q̃ lies within 9M₁a_{j_Q} of a big block of a layer ≤ j_Q (that of □ or □₁, which p_Q contains, since p_Q has the side ≤ 6M₁a_{j_Q}).
      {#W12.102-4} For j_Q + 1 < h the layer j_Q + 1 has the ℓ¹ width ≥ M₁a_{j_Q+2} (CRE p.256 l.57–62), so the ℓ∞ width ≥ (L²/d)M₁a_{j_Q}.
      {#W12.102-5} Hence n_Q ≤ j_Q + 1 under L² > 9d.
      {#W12.102-6} Then Σ_{i<n_Q}2R₀M₀a_i < 2R₀M₀a_{j_Q+1}/(L − 1) = (2L/(K(L − 1)))M₁a_{j_Q} ≤ M₁a_{j_Q} under K ≥ 4, so Ω′_0(Q) ⊂ C₀ ⊂ Q̃², a cube of at most 14 big blocks of the scale j_Q.
    - {#W12.103} PRT2 (2.1)–(2.4) at the size R₀M₀.
      {#W12.103-1} For n < n_Q, dist(Ω′_n(Q)^c, Ω′_{n+1}(Q)) ≥ min(dist((Ω^{col}_n)^c, Ω^{col}_{n+1}), dist(C_n^c, C_{n+1})) ≥ min(LM₁, 2R₀M₀)a_n = 2R₀M₀a_n, the first in ℓ¹ (CRE p.256 l.57–62) and the second in ℓ∞, hence in ℓ¹.
      {#W12.103-2} For n ≥ n_Q, Ω′_{n+1}(Q) = Ω^{col}_{n+1} ∩ Q̃ = ∅.
      {#W12.103-3} Ω^{col}_n is a union of M₁-blocks of the scale n.
      {#W12.103-4} For n ≤ j_Q, C_n is a union of R₀M₀-blocks of the scale n, since Q̃ is a union of M₁-blocks of the scale j_Q and the extensions are multiples of R₀M₀a_n.
      {#W12.103-5} Ω′_{j_Q+1}(Q) = Ω^{col}_{j_Q+1} ∩ Q̃ is a union of M₁-blocks of the scale j_Q, as PBG's Ω_{j+1}(□) = □̃³ ∩ B^{j+1}(Λ_{j+1}) is (p.408 l.30, l.34) and the intersected sequences are.
      {#W12.103-6} So (2.58)–(2.60), the separation of the innermost shell, and the margin of (S) hold as for §7's sequences.
    - {#W12.104} Agreement.
      {#W12.104-1} Ω′_n(Q) ∩ Q̃ = Ω^{col}_n ∩ Q̃ for every n, since C_n ⊇ Q̃ and Ω^{col}_n ∩ Q̃ = ∅ for n > n_Q.
      {#W12.104-2} The stencils of the averagings at the points of supp h′_Q, of the layers ≤ n_Q ≤ j_Q + 1, have the side ≤ a_{j_Q+1} ≤ (1/6)M₁a_{j_Q} under M₁ ≥ 6L, so they stay in Q̃, and the local identity (3.88) holds for Q's operator.
      {#W12.104-3} Q̃ ⊇ □̃³, since Q̃ extends p_Q by 3M₁a_{j_Q} ≥ 3M₁a_j, and p_Q contains □, or □₀ ⊇ □̃², or □₁, which meets □̃, with the points of □̃³ within 6M₁a_j ≤ 3M₁a_{j+1} of □₁. □'s sequence agrees with the collar's on □̃³.
      {#W12.104-4} If it is intersected, Ω′_m(□) ∩ □̃³ = Ω^{col}_m ∩ □̃³ for m ≤ j, since Ω_m(□) ⊇ □̃⁴.
      {#W12.104-5} At m = j + 1, Ω′_{j+1}(□) ∩ □̃³ = B^{j+1}(Λ_{j+1}) ∩ □̃³ = Ω^{col}_{j+1} ∩ □̃³, since Ω^{col}_{j+1} = B^{j+1}(Λ_{j+1}) ∪ Ω^{col}_{j+2} (PRT2 (2.3)) and Ω^{col}_{j+2} ∩ □̃³ = ∅.
      {#W12.104-6} The last holds since □̃³ lies within 5M₁a_j of □'s big block in the layer j, and the layer j + 1 has the ℓ∞ width ≥ (L²/d)M₁a_j > 5M₁a_j.
      {#W12.104-7} If □'s sequence is not intersected, □̃³ lies in the layers j and j + 1 (the criterion of *The local problems.*), and PBG's sequence agrees with the collar's there in the same way.
      {#W12.104-8} So the operators of □ and Q agree on □̃³, and the factor e^{−2δ₀M₁} of (3.97) and p.415 follows as in §7's agreement item.
    - {#W12.105} Corollary 3.6.
      {#W12.105-1} Q̃² lies in the band, at the distance ≥ 2M₁a_h from its boundaries (#W12.105-6–#W12.105-8), where the backgrounds are regular at the scale h ≥ n_Q.
      {#W12.105-2} So (3.35) holds on Q̃² at every index n ≤ h, in the axial gauge of Q̃², as for the collar cubes in *PBG's bounds for them.*, with Q̃², of the side ≤ 14M₁a_{j_Q} ≤ 14M₁a_h, in place of □̃⁵.
      {#W12.105-3} Here the side of Q̃² is ≤ 14M′a_{j_Q}, with PBG's block size M′, and VAR's product is R₁M₁ = M′ (#T2.7-1).
      {#W12.105-4} VAR's cube there has M_V = 7M′, a multiple of R₁M₁, admissible once M(ε₁) = R₁M₁(a₁/ε₁) ≥ 7M′, that is ε₁ ≤ a₁/7, a smallness of ḡ through §8's bounds on ε₁.
      {#W12.105-5} Such a cube, a union of big blocks of the scale h (VAR p.279 l.2), contains Q̃²: for j_Q = h, Q̃² is itself a union of scale-h big blocks of the side ≤ 14M′a_h, since p_Q is snapped to the scale j_Q; for j_Q < h, its side is ≤ 14M′a_h/L ≤ 13M′a_h, so it lies in an aligned cube of the side 14M′a_h.
      {#W12.105-6} Its enlargement □̃ has the side 18M′a_h at most, and Q̃² lies within 22M₁a_h of the cut, with CRE's M₁ = KM′ ≥ M′, so □̃ reaches at most 40M₁a_h from the cut.
      {#W12.105-7} The cut lies at the distance ≥ MR_{h+1}a_{h+1} ≥ 4LR_{h+1}M₁a_h from the band's boundaries under M ≥ 4M₁.
      {#W12.105-8} R_{h+1} ≥ L, since R_{h+1} is a power of L with R_{h+1} ≥ (log g_{h+1}^{−2})^r > 1 (CRE (2.5)), so 4LR_{h+1} ≥ 144 ≥ 40 for L ≥ 6, and the cube fits in the two layers at the cut.
      {#W12.105-9} The tails of the one-step lift from outside the band enter at the distance ≥ 2M₁a_h and give at most L^{2h}e^{−2δ₀M₁L^h} ≤ (1/(eδ₀M₁))² and L^{3h}e^{−2δ₀M₁L^h} ≤ (3/(2eδ₀M₁))³, both ≤ 1 under δ₀M₁ ≥ 1.
      {#W12.105-10} Since every index of Q's sequence is ≤ n_Q ≤ h, (3.37) holds for it with α₁ = O(1)M₁α₀, within the smallness O(1)L⁵M₁α₀ ≤ a₁ of §8.
    - {#W12.106} The factor L of c_h*, pointwise.
      {#W12.106-1} On the collar, cubes that meet need not lie in adjacent layers, so §7's j(f) ≥ j_c − 1 is replaced by a bound at each point.
      {#W12.106-2} A cube of 𝒟_{j′} protrudes at most one big block of its scale, M₁a_{j′}, beyond B^{j′}(Λ_{j′}) (PBG p.408 l.20–21), less than the ℓ∞ width ≥ (L²/d)M₁a_{j′} of the layer j′ + 1.
      {#W12.106-3} So the cubes whose h_□ is nonzero at a point x of the layer m(x) have j′ ≥ m(x) − 1. ∂^kf(x) involves only φ (at the scale j_Q, with m(x) ≤ n_Q ≤ j_Q + 1 on supp φ), ζ_{□̃} (at the scale j, with m(x) ≤ j + 1 on □̃), these h_□, and N_{□₀} (#W7.19). So |∂^kf(x)| ≤ c_h*(M₁a_{m(x)−1})^{−k}, k ≤ 3, with the same constant c_h* as in §7.
      {#W12.106-4} At these points the local layer of the sequence of the cube that carries f is m(x): Q's sequence agrees with the collar's on Q̃, and every collar cube's sequence agrees with it on that cube's □̃³ (*The local problems.* and the agreement item above), which contains the supports of its h_□, h′_□, and ζ_{□̃}.
      {#W12.106-5} Hence ℓ_n|∂f| ≤ c_h*L/M₁, ℓ_n²|∂²f| ≤ c_h*L²/M₁², and the ratio of the third-derivative terms is ≤ 3L/M₁.
      {#W12.106-6} These are within §7's Lc_h* and the factor 1 + 3L²/M₁ that §8's C_w carries.
  - {#W12.107} The crossing decay at every point.
    {#W12.107-1} At each point of Ω′_0(□) the local layer is at most the collar's.
    {#W12.107-2} So each contour's length in the weights of d′ is at least its length in the weights of d_col, the weighted distance (2.46) of 𝐁₁'s sequence.
    {#W12.107-3} (2.46) admits only coarse bonds in coarse layers, so a d′-contour Γ through points where the local layer is finer than the collar's is compared with d_col piece by piece, not segment by segment, since Γ may re-enter a collar layer many times.
    {#W12.107-4} Cut Γ into consecutive pieces of collar-weighted length between 1 and 2, with one shorter remainder; there are at most ℓ_col(Γ) + 1 of them, with ℓ_col(Γ) ≤ d′ the length of Γ in the collar's weights.
    {#W12.107-5} A piece cannot cross a whole collar layer, whose weighted width is ≥ LM₁ > 2 (below), so it meets at most two adjacent layers, and its part in each layer s has an ℓ¹ length ≤ 2L^sξ.
    {#W12.107-6} Its endpoints are therefore joined by an admissible path of at most c_d := 2d(3^d + 1) coarse bonds of their layers, built along the piece itself.
    {#W12.107-7} In each layer s it meets, the piece's part is a connected curve of ℓ¹ length ≤ 2L^sξ, so its ℓ∞ extent is ≤ 2L^sξ and it meets at most 3 blocks of the side L^sξ per coordinate, at most 3^d blocks of that layer.
    {#W12.107-8} These blocks belong to the layer, since the layers are unions of its blocks, and their closures form a connected set, since the curve passes through them.
    {#W12.107-9} A shortest path along the edges of these closed blocks, from a corner of the endpoint's block to a corner of the block where the curve leaves the layer, passes each block at most once and uses at most d coarse bonds in each, so at most d·3^d bonds, with at most d more to move the endpoint to a corner.
    {#W12.107-10} This gives at most d(3^d + 1) bonds per layer and c_d for the two layers.
    {#W12.107-11} The path stays in the closed blocks the piece meets, so it is admissible near a reflex edge as well.
    {#W12.107-12} So d_col ≤ c_d(d′ + 1), that is, d′ ≥ d_col/c_d − 1 on Ω′_0(□): a local rate δ is a rate δ/c_d in d_col, up to the factor e^{δ}.
    {#W12.107-13} The crossing bounds below keep their form: a crossed collar layer has the weighted length ≥ LM₁, and e^{−½δ_minLM₁/c_d} ≤ L^{−3} under δ_minM₁ ≥ 6(c_d/L) log L, which holds under δ_minM₁ ≥ 6c_d log L. This lower bound on M₁ is in §8, *The conditions on the constants.* CRE's maximal domains satisfy dist(Ω^{col}_s, (Ω^{col}_{s−1})^c) ≥ L^sM₁ξ (CRE p.256).
    {#W12.107-14} So a contour from (Ω^{col}_{s−1})^c to Ω^{col}_s has an ℓ¹ length ≥ L^sM₁ξ inside the layer of the scale s − 1, and a weighted length ≥ LM₁.
    {#W12.107-15} This uses only the separation of the domains, not the shape of ∂Ω, so it holds at the reflex edges.
    {#W12.107-16} Every kernel of a walk term therefore decays in d_col between the points it connects, at its rate for the kernels on 𝐁₁'s own sequence and at its rate divided by c_d for the local constituents on the intersected sequences.
    {#W12.107-17} Between a point of the strip and a point of the collar's layer n, a contour crosses at least n − 3 full layers, at e^{−½δ_minLM₁/c_d} ≤ L^{−3} each (#W12.107-13).
    {#W12.107-18} So the count of *The crossings.* holds at the reflex edges, in d_col in place of the count of cubes.
    {#W12.107-19} The per-layer decay that *The sources.*, *The weight.*, and (D2) use holds there too.
  - {#W12.108} The partition functions of a corner cube.
    {#W12.108-1} The partition is §7's normalised one, h_□ = φ_□/N_𝒟 with N_𝒟 ≥ 1 and Σ_□h_□² = 1 (#W7.16-11–#W7.16-11-2), defined in the same way at the reflex edges as at the flat interfaces. K(h_□) of (3.88) reads a_j and B^j(y) at the points of supp ∂h_□, and supp h_□ lies within the ℓ∞-distance (2/3)M₁a_{n′} of the centre of □ (#W7.16-11-2).
    {#W12.108-2} Near a reflex edge the points of supp h_□ can lie in a layer j ≠ n′. At a point u of the layer j, the cubes with φ_□(u) ≠ 0 have scales i ≥ j − 1 (#W12.106-3), at most 2^d of each scale (#W7.16-11-3), and near a reflex edge several coarser scales can occur.
    {#W12.108-3} Let |∂φ_□| ≤ c_φ(M₁a_i)^{−1} for □ ∈ 𝒟_i, c_φ a constant of h and d. Then Σ_□|∂φ_□(u)|² ≤ 2^dc_φ²Σ_{i≥j−1}(M₁a_i)^{−2} ≤ 2^{d+1}c_φ²(M₁a_{j−1})^{−2}, and |∂N_𝒟| ≤ (Σ_□|∂φ_□|²)^{1/2} by 2N_𝒟∂N_𝒟 = Σ_□2φ_□∂φ_□ and Cauchy–Schwarz.
    {#W12.108-4} From ∂h_□ = ∂φ_□/N − φ_□∂N/N², N ≥ 1, and Σ_□φ_□² = N², Σ_□|∂h_□(u)|² ≤ 2Σ_□|∂φ_□|² + 2|∂N|² ≤ 2^{d+3}c_φ²(M₁a_{j−1})^{−2}. In the same way Σ_□|∂²h_□(u)|² ≤ O(1)(M₁a_{j−1})^{−4}, using |∂²N| ≤ (Σ_□|∂²φ_□|²)^{1/2} + 2Σ_□|∂φ_□|², from ∂²(N²) = 2N∂²N + 2(∂N)² = Σ_□2(φ_□∂²φ_□ + (∂φ_□)²).
    {#W12.108-5} At a point u of the layer j, the last term of (3.88) for □ is at most a_j(L^jη)^{−2}·dL^jη|∂h_□(u)|·|G′_□λ|, and (3.42) for the local sequence at the layer j of u (the local layer is the collar's there, #W12.106-4) gives |G′_□λ| ≤ B₀(L^jη)²|λ| for λ on a block.
    {#W12.108-6} Each step R′ = Σ_□K(h_□)G′_□h_□ of the expansion (3.90) (PBG p.409) carries h_□ at its right end, and Σ_□|∂h_□(u)|h_□(v) ≤ (Σ_□|∂h_□(u)|²)^{1/2}(Σ_□h_□(v)²)^{1/2} ≤ 2^{(d+3)/2}c_φ(M₁a_{j−1})^{−1}. So the sum over □ of these terms is at most O(1)a_jdB₀(L/M₁)|λ|, whatever the number of scales that overlap at u, and the gradient and Laplacian terms of (3.88) likewise.
    {#W12.108-7} So (3.89) holds for these cubes with the decay e^{−δ₀d′} and the factor O(L/M₁), within §7's factor Lc_h*/M₁ (#W7.16-4).
  - {#W12.109} The comparison without (S) at ∂Ω.
    {#W12.109-1} Let ℒ̃ := χ_Bℒ_N as in 10.1, with χ_B the characteristic function of Ω′^B_0(□). 10.1's margin argument gives χ_AQ₁(1 − χ_B) = 0, except on the coarse bonds within 2ε of ∂Ω, where Q̄₁ reads fine bonds outside Ω.
    {#W12.109-2} Put r := χ_AQ₁(1 − χ_B)ℒ_N, supported on those bonds, with |r(c, c′)| ≤ C_ℒe^{−½δ_Qd_ε(c,c′)} by (H_ℒ).
    {#W12.109-3} Then χ_AQ₁ℒ̃X = X − rX, and the proofs of §4(a)–(b) give the identities with one more term each: G^Ar*𝒪^Aχ_AQ₁G^Bg in (a) and G^BQ₁*χ_A𝒪^ArG^Af in (b), up to sign.
    {#W12.109-4} A field v of 𝔉^A vanishes outside Ω′^A_0(□), so |v| ≤ 3ε sup|∇v| within 2ε of ∂Ω, and there, in run A's finest layer, |𝒪^Av| ≤ O(1)ε^{−1}‖v‖_{1,β;y}.
    {#W12.109-5} So the extra terms are sources of the form ϖ = 1 on run A's shell 0 at ∂Ω, of the kind of run B's extra-shell term of §5(a).
    {#W12.109-6} The strip's other differences are of the same kind, at its points: run B's extra fine layer, the averaging of the two runs' layers 0 and 1 there, and K(h_□) at the points of supp ∂h_□ on the strip.
  - {#W12.110} The strip's data block.
    {#W12.110-1} Each run's data space of the inverses (QGQ*)^{−1} and (QG_πQ*)^{−1} in H, G̃, and 𝔊 is split as 𝔇^X = 𝔇_1 ⊕ 𝔇^X_2.
    - {#W12.111} 𝔇_1 holds the data on run A's layers n ≥ 2.
      {#W12.111-1} These are run B's layers n + 1, on the same sites (*The collar's layers.*).
    - {#W12.112} 𝔇^X_2 holds each run's data at the sites of the strip Ω ∖ Ω^A_2: run A's layers 0 and 1, and run B's layers 0, 1, and 2.
    - {#W12.113} The mixed refined layers, where Q^Bℒ ≠ Q^A, lie in 𝔇^X_2.
      {#W12.113-1} They are not compared.
    - {#W12.114} On 𝔇_1, Q^B = Q^AQ₁ exactly (CMP 98 (80), as in §5's *The averaging terms.*).
      {#W12.114-1} With K^X := Q^XG^XQ^{X*}, this gives K^B_{11} − K^A_{11} = Q^A(Q₁G^BQ₁* − G^A)Q^{A*}.

    {#W12.115} Let D^X := (K^X)^{−1}, in blocks.
    {#W12.115-1} Take row 1 of K^BD^B = 1, multiplied on the left by [D^A]_{11}.
    {#W12.115-2} Take column 1 of D^AK^A = 1, multiplied on the right by [D^B]_{11}.
    {#W12.115-3} Subtracting gives the exact identity
    {#W12.116} [D^B]_{11} − [D^A]_{11} = −[D^A]_{11}(K^B_{11} − K^A_{11})[D^B]_{11} + [D^A]_{12}K^A_{21}[D^B]_{11} − [D^A]_{11}K^B_{12}[D^B]_{21}.
    {#W12.117} It needs no composing projection on the strip, and no extra-shell identity.
    {#W12.117-1} The same holds with G_π in place of G.
    - {#W12.118} The first term is the form (b) for G, Q₁G^BQ₁* − G^A, between blocks of the two runs' inverses.
      {#W12.118-1} It is bounded per point by the bullets above.
    - {#W12.119} The second and third terms pass through 𝔇_2 and are bounded absolutely, with no difference between runs: the second is a product of two run-A blocks and one run-B block of D^X and K^X, the third of one run-A block and two run-B blocks.
      {#W12.119-1} Their kernels decay at the composite rate δ_min (§11), of which ½δ_min is kept for the crossings at complex s, as in *The strip.* So a term evaluated at x₀ that reads data at z carries e^{−½δ_min(d_col(x₀, S) + d_col(S, z))}, with S the strip.
      {#W12.119-2} As in *The crossings.* of *The strip.*, this is at most L^{−3(m(x₀)−5)₊}L^{−3(m(z)−5)₊}.
      {#W12.119-3} The data at z carry (a_{m(z)}/a_h) (*The data.*), and none at the layers ≥ h, where m(z) = h.
      {#W12.119-4} So these terms are at most O(1)L^{15}(ε/a_h) times their bound.
      {#W12.119-5} This is ≤ O(1)L^{15}(ε/a_h)^{γ_H}.
    - {#W12.120} The rows and columns of 𝔇^X_2 in H = GQ*D, and in G̃ and 𝔊, enter likewise, run by run.
      {#W12.120-1} Strip data carry (a_2/a_h) ≤ L²(ε/a_h) (*The data.*), and they reach x₀ through the crossings.
      {#W12.120-2} In 𝔊 = G − GQ*DQG the data that D acts on are QG applied to the current and the nonlinear sources, and their gain on the strip is that of *The sources.*, in the weighted norm |·|_g.

    {#W12.121} So the strip's data enter 𝔡_H(x₀) with at most O(1)L^{15}(ε/a_h).
  - {#W12.122} The per-point bound.
    {#W12.122-1} The run difference of a walk term is therefore a sum over the defect points p of its constituents, each with the weight ϖ(p) = L^{−βn_loc(p)} of (Wδ-1) between the walk's kernels, which decay in d_col through p. Here n_loc(p) is the local shell at p, which on Ω′_0(□) ∖ □ can be finer than m(p).
    {#W12.122-2} There §5(c)'s shell-crossing decay from □ to p, L^{−(1+β)(n′−n_loc(p)−1)₊} under 4δ₀R₀M₀ ≥ 3(1 + β) log L, gives ϖ(p)L^{−(1+β)(n′−n_loc(p)−1)₊} ≤ L^{1+2β}L^{−βm(p)}, since n_loc(p) ≤ n′ and m(p) ≤ n′ + 1.
    {#W12.122-3} On the strip, ϖ(p) ≤ 1 and m(p) ≤ 2.
    {#W12.122-4} Let z be a point at which the term reads its data, which carry the gain (a_{m(z)}/a_h) (*The data.*; no gain at m(z) = h).
    {#W12.122-5} Between p and z a contour crosses at least |m(p) − m(z)| − 3 layers, at L^{−3} each.
    {#W12.122-6} So, relative to its bound, the term is at most L^{10+2β}L^{−βm(p)}L^{−3|m(p)−m(z)|}L^{m(z)−h}.
    - {#W12.123} If m(p) ≥ m(z), the exponent is at most (1 − β)m(z) − h ≤ −βh.
    - {#W12.124} If m(p) < m(z), it is (3 − β)m(p) − 2m(z) − h ≤ (1 − β)m(z) − h ≤ −βh.

    {#W12.125} So each term is at most L^{10+2β}(ε/a_h)^β times its bound, at every point of the collar, at the reflex edges and at ∂Ω.
    {#W12.125-1} This holds for the walks compared by alignment, for the walks with a cube on the strip, and for the enlargement-only walks.
    {#W12.125-2} The sum over the defect points and the constituents is as in §7.
    {#W12.125-3} For the walk operators (G′, C_□, G_a, G, H₀, and their constituents) the exponent is β ≥ γ_w.
  - {#W12.126} The localised 𝔡_H.
    {#W12.126-1} For the operators compared through *The form (c) for VAR's H.* (H, G̃, 𝔊, H₁, H_{𝐁₁}, and the fixed points), §11's 𝔡_H is a power of global suprema, which for 𝐁₁ include the strip.
    {#W12.126-2} For a point x₀, let |f|_{x₀} be the supremum of e^{−δ′d_col(x₀,x)}|f(x)| over x, with the Hölder entries local at x and δ′ := ¼δ_min.
    - {#W12.127} Every operator of that derivation is bounded in |·|_{x₀} with its constant changed by O(1), since its kernel decays at a rate ≥ ¾δ_min ≥ 3δ′, as for ω′ in *The weight.*
    - {#W12.128} The interpolation inequality is local, and the weight changes by at most e^{δ′} across a block.
    - {#W12.129} So the derivation gives the run difference at x₀ with 𝔡_H(x₀): §11's 𝔡_H with each global supremum sup_xq(x) replaced by sup_xe^{−δ′d_col(x₀,x)}q(x).
      {#W12.129-1} Each q(x) is at most O(1)L²(ε/a_{m(x)})^{γ_w}, and at most O(1) on the strip.
      {#W12.129-2} The exponents are as follows.
      - {#W12.130} δ_w at x carries γ_w = min(β, (1 − ε₀)/3).
      - {#W12.131} ϑ_ℒ carries min(β₂, 1 − β′) ≥ ½ > γ_w.
      - {#W12.132} ϑ carries these and ε/a.
      - {#W12.133} ϑ_b carries β_H.
        {#W12.133-1} Any β_H < 1 is allowed (*The artifact through covariances.*), and β_H ≥ γ_w is taken.
      - {#W12.134} The cell-mean term carries β ≥ γ_w.

      {#W12.135} The derivation multiplies at most two factors at a point, such as q(x) and a field.
      {#W12.135-1} In such a product each factor is taken in |·|_{x₀} at δ′/2 = δ_min/8, and the bounds below hold with that rate.
    - {#W12.136} For m(x) < m(x₀), d_col(x₀, x) ≥ (m(x₀) − m(x) − 1)LM₁, and e^{−δ_minLM₁/8} ≤ L^{−3L/4} ≤ L^{−3/2} under δ_minM₁ ≥ 6 log L and L ≥ 2, with the O(d) of *The crossing decay at every point.* absorbed in the constant.
      {#W12.136-1} Since 3/2 > γ_w, the weighted suprema are at most O(1)L^{7/2}(ε/a_{m(x₀)})^{γ_w}.
      {#W12.136-2} So 𝔡_H(x₀) ≤ C(ε/a_{m(x₀)})^{γ_H}, with γ_H = βγ_w/(1 + β) as in §11.
    - {#W12.137} The data read at z enter with e^{−δ′d_col(x₀,z)}(a_{m(z)}/a_h).
      {#W12.137-1} This is at most L^{3/2}(a_{m(x₀)}/a_h) for m(z) ≥ m(x₀), and at most (a_{m(x₀)}/a_h) otherwise.
    - {#W12.138} So the run difference at x₀ is at most C′L^{−γ_Hm(x₀)}L^{m(x₀)−h} ≤ C′(ε/a_h)^{γ_H} times its bound, and the fixed points carry γ_H − 2β′, as in §8.
  - {#W12.139} The consumer.
    {#W12.139-1} A history's birth scale n satisfies n ≤ h (*The requirement.* of (Wδ-4)), so (ε/a_h)^γ ≤ (ε/a_n)^γ.
    {#W12.139-2} The collar's terms therefore fit the weight that §8 gives the other terms, with no new rate in θ̃.
- {#W12.140} The collar of 𝐁₁.
  {#W12.140-1} Its layers reach the finest scale within 2M₁ of ∂Ω″^∼_{h+1}.
  {#W12.140-2} The layers at run A's scales n ≥ 2 are aligned (*The collar's layers.*), so the remaining part is the strip of the width 2M₁a_2 at ∂Ω″^∼_{h+1}.
  {#W12.140-3} There the alignment of §11 fails, run B has an extra fine layer with no counterpart in run A, the young-history factor ε/a_j is O(1), and 10.1's (S) is not available at that boundary.
  {#W12.140-4} *The strip.* below bounds each run's terms on the strip separately, within the consumer's weight, in the representation of U₁ with the gain, and the run difference of that representation's gauge factor is derived after it. ∂Λ does not meet the strip (*The representation with the gain.*).
  {#W12.140-5} The collar also enters 𝐇″_k and u^0_k through (1.55).
  {#W12.140-6} The localised source 𝐆″_k(1 − θ)Q*_{𝐁₁}θ₁H*_{𝐁₁}J₁ contains H_{𝐁₁}, the operator of the whole 𝐁₁ problem, collar included, and θ₁ sits a few h-blocks from the collar's fine layers.
  {#W12.140-7} *The source of (1.55).* below shows that run B's terms at the pair read the right side of (1.55), and bounds the run difference of that source.
  {#W12.140-8} The cut lies in 𝐁″_k's layer h, so h ≥ j₀ − 1 ≥ k/2 − 1 in a young history (the LF note's *The configurations.*), and on (Ω″_{h+1})^c ∩ Ω″^{∼2}_{h+1} the backgrounds are regular at the scale h (*The band regularity of U_{1,2}.* for U_{1,2}; VAR's (9)–(10) for U_k and U_{k,Λ}).
  {#W12.140-9} Then every term of either run located in the collar's layer n carries a factor (a_n/a_h)^p from that regularity (p = 3 for the current J, p = 1 for a field), or the crossing decay L^{−4(h−n−1)} of (J-W) from the layers ≥ h, so the terms in the collar's finest layers need no comparison, while those in its layers n ≥ 2 are compared with δ_w(n)(a_n/a_h)^p ≤ (ε/a_h)^γ for p ≥ γ.
  {#W12.140-10} It uses two inputs: the size of 𝐇_{𝐁₁}'s data field −(1/i)log M^·(U_{k,Λ}) on Z″_k ∩ Ω″^∼_{h+1} (LFR II (1.57); Z″_k reaches the cut, p.370 l.28) in the collar's fine-layer norms, set by Bałaban's axial gauge in Λ (p.371 l.32–33) and bounded independently of the size of Λ, and the lower bound M₁ ≥ 4R₀M₀, which keeps the local domains Ω₀(□) of the cubes in the collar's layers n ≥ 2 off the finest layer and off ∂Ω″^∼_{h+1}.
  {#W12.140-11} The second input holds.
  {#W12.140-12} CRE's M₁ "is the size of large cubes for which all the theorems of the previous papers, especially those concerning the variational problem, are valid" (CRE p.245 l.34–36).
  {#W12.140-13} PBG proves its theorems for big blocks of the size M = KR₀M₀, with K a positive integer and "M … much bigger than M₀" (PBG p.408 l.25–27).
  {#W12.140-14} So M₁ = KR₀M₀ in PBG's notation is a condition imposed on M₁ (PBG p.408 l.26–28; CRE p.245 l.35–36), and K ≥ 4 gives M₁ ≥ 4R₀M₀.
  {#W12.140-15} CRE's R₀ of p.245 l.32, the smallest power of L with R₀ ≥ (log g₀^{−2})^r, is a different constant from PBG's R₀.
  {#W12.140-16} The first input has two parts, the size of the data and their gain.
  {#W12.140-17} Z″_k ⊂ Λ, and Bałaban states that U_{k,Λ} satisfies LFR I (1.84) (LFR II p.371 l.32–33), |M^j(U_{k,Λ}) − 1| < O(1)B₃B₅M⁶ε_k inside Λ at every scale j (LFR I p.197), with Λ in a cube of the size 100M by condition (i) (LFR I p.192).
  {#W12.140-18} So the data angles of 𝐇_{𝐁₁} are at most O(1)B₃B₅M⁶ε_k at every layer, independently of the size of Λ.
  {#W12.140-19} The gain (a_n/a_h) for these data in the collar's layers n < h holds with p = 1 for the data fields and p = 3 for the current:
  - {#W12.141} (1.84) is uniform in j and does not give the gain, and Bałaban's gauge does not either, since there Q_k^{s*} puts the whole angle V(c) on the bonds between k-blocks (CRE (1.3), p.246).
  - {#W12.142} The gain holds in a gauge that is smooth at the scale k.
    {#W12.142-1} U_{k,Λ} = U_k(V″⌈_{Λ^c}, V_Λ^{(A)}) is VAR's minimiser for data at the single scale k.
    {#W12.142-2} Its data satisfy VAR (7) (p.278) with ε₁ := B₅M⁵ε_k: on Λ by (1.78) (LFR I p.194), and on Λ^c because V″ and the determining set there are those of the new configuration U_k (LFR II p.370 l.5–7), which satisfies the small-field conditions of its scales.
    {#W12.142-3} The data on Λ ⊂ Z are at the scale k, the scale of the large-field variables, so Λ lies in the layer k of this problem.
    {#W12.142-4} VAR (9)–(10) at the layer k hold on the cubes of VAR's class there (VAR p.279 l.2–4): cubes □ of the side 2M_Va_k, M_V a multiple of R₁M₁ (VAR writes M), whose concentric cube of the side (2M_V + 4R₁M₁)a_k lies in the layer.
    {#W12.142-5} Z″_k is a union of M-cubes, and Λ adds one layer of M-cubes to it (LFR I p.192 l.41–47).
    {#W12.142-6} VAR's cube size parameter is any multiple of R₁M₁, and it is taken equal to R₁M₁ here, so that the cubes are aligned with the grid of the side R₁M₁a_k and are unions of big blocks: each □ of the side 2R₁M₁a_k is a union of 2^d grid cubes.
    {#W12.142-7} Each point x of Z″_k lies in such a □, and its concentric cube □̃ of the side 6R₁M₁a_k lies in the ℓ∞-ball of the radius 4R₁M₁a_k about x. x lies at the ℓ∞-distance ≥ Ma_k from Λ^c, since Λ adds one layer of M-cubes to Z″_k, so □̃ ⊂ Λ once M ≥ 4R₁M₁.
    {#W12.142-8} VAR's further condition, that □̃ is not contained in B^{j+1}(Λ_{j+1}), is vacuous at the layer k, the top layer of this problem.
    {#W12.142-9} M ≥ 4R₁M₁ is a lower bound on M of the kind VAR's own condition is, and it follows from §12's condition M ≥ 4M₁ with CRE's M₁ = KM′, since R₁M₁ = M′ ≤ KM′ (§8, *The conditions on the constants.*).
    {#W12.142-10} The points read below lie in Z″_{h+1}, at a distance ≥ Ma_k from ∂Λ (*The representation with the gain.*).
    {#W12.142-11} So VAR (9)–(10) give, gauge-invariantly at these points, |F| ≤ O(1)B₃B₅M⁶ε_ka_k^{−2}, |∇F| ≤ O(1)B₄(1)B₅M⁶ε_ka_k^{−3}, and |J| ≤ O(1)B₃B₅M⁶ε_ka_k^{−3}.
  - {#W12.143} Z″_k is a rectangular parallelepiped, "the new large field region" (LFR I p.192 l.40–41), contained in Λ, which lies in a cube of the size 100M at the scale k (p.192 l.46–47).
    {#W12.143-1} So the fine axial contours from a corner of Z″_k to its points stay in Z″_k, whose points are at a distance ≥ Ma_k from Λ^c, and the regularity of VAR (9)–(10) holds along the whole contour.
    {#W12.143-2} In the fine axial gauge from that corner, the field A of U_{k,Λ} therefore has |A| ≤ O(1)dMa_k|F| ≤ O(1)B₃B₅M⁷ε_ka_k^{−1}.
    {#W12.143-3} Its data angle at a bond of the layer n is a_nQ_nA + C_n(a_nA) (VAR (44)), at most O(1)B₃B₅M⁷ε_k(a_n/a_k) ≤ O(1)B₃B₅M⁷ε_k(a_n/a_h), since n < h ≤ k.
    {#W12.143-4} Then (3.133) for H_{𝐁₁} at the layer n gives the field and its gradient in the layer-n norms with the same factor (a_n/a_h), with the layer crossings of §11's *The data bound.* Also a_n³|J| ≤ O(1)B₃B₅M⁶ε_k(a_n/a_h)³.
  - {#W12.144} The data field H″_{1,k}Q̃(η𝐀₀) of (1.54).
    {#W12.144-1} LFR I (1.87) (p.197) gives |𝐀₀|, |∇𝐀₀|, |∂*∂𝐀₀| < O(1)B₃²B₅M⁶ε_k on Z″_k in the units of the scale k, for the background whose average LFR II takes as exp iQ̃(η𝐀₀) (p.370 l.15–16).
    {#W12.144-2} So a_n|Q̃_n𝐀₀| ≤ O(1)B₃²B₅M⁶ε_k(a_n/a_k), and (3.133) for H″_{1,k} gives the same gain.
    {#W12.144-3} The cut-off of the data at ∂Z″_k costs only a jump of this size, so p = 1 holds there too.
  - {#W12.145} *The strip.* On the strip Ω ∖ Ω^A_2 the two runs are not compared.
    {#W12.145-1} Each run's terms there are bounded separately, and the bound fits the consumer's weight.
    - {#W12.146} Where the strip lies. ∂Ω lies in the layer h of 𝐁″_k, at a distance ≥ 2M₁a_h from that layer's boundary inside Ω (CRE p.257 l.9–11: "this boundary of Ω_j, Ω_{j+1}, which is contained in Ω"; the LF note's *The joins*, *The layers of 𝐁₁.*).
      {#W12.146-1} The strip lies inside Ω, so this is the boundary that matters.
      {#W12.146-2} The strip, of the width ≤ (d + 1)M₁a_2, therefore lies in that layer once L^{h−2} > d + 1; the finitely many smaller h are absorbed in C_w as at the end of *The representation with the gain.*, and it carries the collar's layers of 𝐁₁ at the physical spacings ≤ a_2 in both runs (run A's layers 0 and 1, run B's layers 0, 1, and 2).
      {#W12.146-3} So a walk ω whose ∪X̃_i⁵ meets the strip has m(ω) ≤ h, with m(ω) read in the global layers of 𝐁″_k, as the consumer reads it (its young-history factor is (ε/a_{m(Y)})^γ in 𝐁″_k's layers), and its weight in §8 is at least (ε/a_h)^{γ_w}.
    - {#W12.147} The data.
      {#W12.147-1} In each run, the bullets above, applied to that run's problem, give the data of 𝐇_{𝐁₁} and of H″_{1,k}Q̃(η𝐀₀) at a bond of physical spacing a the factor (a/a_h), and the current the factor (a/a_h)³.
      {#W12.147-2} On the strip this is at most (a_2/a_h) = L²(ε/a_h).
    - {#W12.148} The crossings.
      {#W12.148-1} A walk term meets the strip if one of its cubes X_i meets the strip, or its evaluation or source point lies in it; the count below starts from that cube, and the spare layer of the count covers this.
      {#W12.148-2} A walk whose only contact with the strip is through an enlargement X̃_i⁵ is aligned, except when an intersected Ω₀(□) of its cubes meets the strip or ∂Ω, where it is compared through the boundary source with the per-point bound (*The enlargement-only walks.* below).
      {#W12.148-3} Let a walk term meet the strip and read data at the collar's layer n ≥ 2 through a cube X_i of the layer n′.
      {#W12.148-4} X_i and X̃_i⁵ reach at most 6M₁a_{n′} in ℓ∞ from a big block of X_i in the layer n′, less than the ℓ∞ width ≥ (L²/d)M₁a_{n′} of the layer n′ + 1 (its ℓ¹ width ≥ M₁a_{n′+2}, CRE p.256 l.57–62) under L² > 9d, so n ≤ n′ + 1.
      {#W12.148-5} The decay of (3.108) is in the distance through points of the X_i (PBG (3.93), p.410; the tree length d_T of §11 for the composites), and a path from a point of the strip to a point of X_i crosses the layers 2, …, n′ − 2 at least, since a cube of 𝒟_{n′} may protrude one big block into the layer n′ − 1 (its 2^d big blocks need only one in B^{n′}(Λ_{n′}), PBG p.408 l.20–21), and the passage between CRE's ℓ¹ distances and the cube-wise layers costs at most one more layer, so at least n′ − 4 ≥ n − 5 of them.
      {#W12.148-6} Near the flat parts of ∂Ω and its convex edges this count is the count of cubes.
      {#W12.148-7} At a reflex edge of Ω, where cubes of 𝒟_{n′} touch ∂Ω for every n′ ≤ h, it holds in the collar's weighted distance d_col instead, by *The crossing decay at every point.* of *The collar at ∂Ω and at the reflex edges.*, with the per-point bound there in place of the bound below.
      {#W12.148-8} Each layer is ≥ M₁ wide in its own units (CRE p.256 l.57–62).
      {#W12.148-9} The walks of H, G̃, H₁, and 𝔊 are composites, whose constituents include the terms of the re-expansions (3.96) of (QGQ*)^{−1} and (QG₁Q*)^{−1} (§11), D_□ at ¼δ_D′, and G_□ at δ_gf′/3, so their constituents decay at rates ≥ 2δ_min, with δ_min of §11's κ₁ replay, and the composites at the rate δ_min (§11, *The junction sums.*).
      {#W12.148-10} Of that rate, ¼δ_min goes to the s-weights (the κ₁ replay, which covers these run-by-run terms as well), ¼δ_min is kept for the form (c), and ½δ_min is kept for the crossings (§11, *The condition on M.*).
      {#W12.148-11} It gives e^{−½δ_minM₁} ≤ L^{−3} per crossing under δ_minM₁ ≥ 6 log L. This is a lower bound on M₁ = KR₀M₀, met by K large, since δ_min is fixed by δ₀, δ_π, δ₀′, δ_gf′, and δ_D′, before M₁.
      {#W12.148-12} So the data it reads carry (a_n/a_h)L^{−3(n−5)} = L^{13−2n}(a_2/a_h) ≤ L⁹(a_2/a_h) for 2 ≤ n < h.
      {#W12.148-13} Data at the layers ≥ h carry no gain, but they lie at least h − 5 crossings away, and L^{−3(h−5)} = L^{13−2h}(a_2/a_h) ≤ L⁹(a_2/a_h) for h ≥ 2.
    - {#W12.149} The sources.
      {#W12.149-1} The walk terms of H, H₀, and G̃ act on the data and the current, and also on the nonlinear sources of the fixed points: δV/δA′ of VAR (80), the C_j terms of D, and the E-terms of σ.
      {#W12.149-2} On the strip each source is a sum of products of 𝐇 with the background's field, curvature, and current, of order ≥ 2 in 𝐇 or with a factor of the background's current.
      {#W12.149-3} Let ω_g(x) := max(1, a_h/a(x)), a(x) the spacing at x, and let |𝐇|_g be VAR's norm with each entry weighted by ω_g: sup_xω_g(x)(a(x)|𝐇(x)| + a(x)²|∇𝐇(x)| + a(x)^{2+β}[∇𝐇]_{β,x}), the Hölder entry local at x as in VAR's contraction (VAR (186) reads both entries).
      {#W12.149-4} The max is needed because 𝐁₁ has layers above h, on Z″_k ∩ Ω″^∼_{h+1}, where data need no gain.
      {#W12.149-5} The weight ratio of two points is ≤ L^{|n−n′|}, which the crossing decay L^{−3} per layer beats.
      {#W12.149-6} The kernels of H, H₀, and G̃ and their gradient and Hölder entries (3.42)–(3.44) have that decay, so these operators are bounded in |·|_g with constants changed by a factor of L. The sources of the fixed point are products of 𝐇 and ∇𝐇 with the background's field and curvature (the cubic local terms of V₀ contain ∇A′, *The second-order terms.*), and a product with at least two factors of 𝐇 obeys ω_g·a³|s| ≤ C|𝐇|_g|𝐇|_{(−1)} ≤ C|𝐇|_g², and likewise in the gradient and Hölder entries, since ω_g ≥ 1.
      {#W12.149-7} VAR's contraction (Proposition 6) therefore holds in |·|_g, and the fixed point carries the gain of its data.
      {#W12.149-8} The background's current carries (a/a_h)³ (VAR (10) at U_{k,Λ}, and the derived band regularity of §12 for U_{1,2}).
      {#W12.149-9} So the sources carry the gain.
      {#W12.149-10} The bound is at the actual argument of each run's fixed point, the argument that the consumer in §3(d) evaluates; it is not an operator bound.
    - {#W12.150} The bound.
      {#W12.150-1} Each run's walk term ω meeting the strip is therefore at most O(1)L¹¹(ε/a_h) times its bound (3.108) at the rate ¼δ_min kept for the form (c).
      {#W12.150-2} In the form (c), run A's term enters through ℒ_ι𝒥, with the C^{1,β} constant C_ℒ.
      {#W12.150-3} So the difference is at most O(1)(1 + C_ℒ)L¹¹(ε/a_h) ≤ O(1)(1 + C_ℒ)L¹¹(ε/a_{m(ω)})^{γ_w}, since ε/a_h ≤ 1, γ_w ≤ 1, and a_{m(ω)} ≤ a_h.
      {#W12.150-4} This is δ_w(ω) of §8, with C_w enlarged by O(1)(1 + C_ℒ)L¹¹ and the rate of the form (c) unchanged.
      {#W12.150-5} Neither (S), nor the alignment, nor the young-history factor of the strip's own layers enters.
    - {#W12.151} *The enlargement-only walks.* A walk whose cubes and evaluation and source points lie off the strip, while some X̃_i⁵ meets it, has its cubes in Ω^A_2 = Ω^B_3, at run A's layers n ≥ 2, where the two runs' layers agree (*The collar's layers.*).
      {#W12.151-1} PBG builds the local operator of a cube □ of the layer n on its own sequence {Ω_m(□)}: Ω_{n+1}(□) = □̃³ ∩ B^{n+1}(Λ_{n+1}), Ω_n(□) = □̃⁴, and each finer Ω_m(□) is a cube centred at the centre of □, with Ω₀(□) ⊂ □̃⁵ (PBG p.408 l.29–35 and p.409 l.1–3), and "the operators constructed for this sequence" are G′_□, C_□, and G_□ (p.409 l.1–3).
      {#W12.151-2} So the local operator depends on □, on □̃³ ∩ B^{n+1}, and on the background and data on Ω₀(□), and not on the global layers inside □̃⁵.
      {#W12.151-3} PBG takes every operator with Dirichlet conditions on its Ω₀^c (p.394 l.29–36), but its local construction (p.408) does not treat cubes whose Ω₀(□) meets that boundary; where Ω₀(□) meets ∂Ω, the local problem is posed here on the intersected sequence {Ω′_m(□)} of *The collar at ∂Ω and at the reflex edges.*, with the Dirichlet condition of the 𝐁₁ problem, in both runs.
      {#W12.151-4} A walk term also contains the factors K(h_□) of (3.88)–(3.90), which read the global layer structure (the a_j and the blocks B^j(y)) on supp ∂h_□ ⊂ □.
      {#W12.151-5} For a cube □ of the layer n ≥ 2 that support lies in Ω^A_2 = Ω^B_3, where the runs are aligned. □, B^{n+1} with n + 1 ≥ 3, and Ω are the same in both runs, and the two runs' local sequences differ as on the aligned layers, run B's having one finer cube layer by the same rule.
      {#W12.151-6} So the walk is compared by (W-δ) as an aligned walk, as on *The collar's layers.*, and the strip enters only through the points of Ω₀(□) at which the walk reads the background pair and the data.
      {#W12.151-7} There the data carry (a/a_h) ≤ (a_2/a_h) ≤ (a_n/a_h) (*The data.*), and the background pair satisfies 10.5's premise (*The background pairs.*).
      {#W12.151-8} So the strip's misalignment does not enter these walks.
      {#W12.151-9} This holds for the cubes □ whose sequence is not intersected (*The local problems.*) and whose Ω₀(□) does not meet ∂Ω in either run (run B's Ω₀^B(□) has one more margin of 2R₀M₀η_B).
      {#W12.151-10} An intersected sequence reads the collar's domains on Ω₀(□).
      {#W12.151-11} Where Ω₀(□) misses the strip, these agree in the two runs (Ω^A_n = Ω^B_{n+1} for n ≥ 2), and the walk is aligned as above.
      {#W12.151-12} Where Ω₀(□) meets ∂Ω, or an intersected Ω₀(□) meets the strip, the two runs' domains differ only at the strip's points, PBG's bounds for the local problem on the intersected sequence hold by *PBG's bounds for them.* of *The collar at ∂Ω and at the reflex edges.*, and the comparison is made there without (S), through the boundary source r, with the per-point bound.
  - {#W12.153} *The representation with the gain.* The argument X := −(1/i)log M^·(U_{k,Λ})⌈_{Z″_k} of (1.57) is the deviation of U_{k,Λ}'s data from U₁'s data, which are 1 on Z″_k and agree with U_{k,Λ}'s elsewhere (the first line of (1.57)).
    {#W12.153-1} Under a gauge transformation of both, the deviation at a bond is conjugated, so |X| does not depend on the gauge; in Bałaban's gauge its entries have the size ε_k (#W12.141), so the gain needs a relative regauging of the two data sets at the data points of Z″_k.
    {#W12.153-4} The regauging of U₁'s data by h below is one, and it gives a second representation of U₁.
    {#W12.153-5} Let w be the gauge function that takes U_{k,Λ} to the fine axial gauge of Z″_k: w(x) is the transport of U_{k,Λ} along the fine axial contour from a corner of Z″_k to x, for x in Z″_k.
    {#W12.153-6} Let h := w at the endpoints of the data bonds of Z″_k ∩ Ω″^∼_{h+1} and h := 1 at all other endpoints of data bonds of 𝐁₁ (whose data are V″ on Λ^c, M^k(U^{(AL)}_0) on Λ ∩ Ω″_k, and 1 on Z″_k ∩ Ω″^∼_{h+1}, by (1.53), p.370).
    {#W12.153-7} The sets Γ_j of CRE (2.2) (p.255) are sets of points and bonds, so a bond of one layer and a bond of the next may share an endpoint.
    {#W12.153-8} There h takes the value w, and the bond of the other layer, with data V″ or M^k, is changed at that end by w(x).
    {#W12.153-9} Let h̃ be an extension of h to the fine lattice.
    {#W12.153-10} U_{𝐁₁} is supported in Ω″^∼_{h+1} (p.370 l.22–25), so no outside configuration constrains h̃.
    {#W12.153-11} With U^g(b) = g_xU(b)g_y^{−1}, the data of U₁^{h̃^{−1}} are w_x^{−1}w_y on Z″_k ∩ Ω″^∼_{h+1}, and they agree with U_{k,Λ}'s elsewhere, except on the bonds of the other layers that share an endpoint with Z″_k.
    {#W12.153-12} On Z″_k, M^·(U_{k,Λ})(b) = w_x^{−1}M^·(U^{ax})(b)w_y, with U^{ax} := U_{k,Λ}^{w}, by the covariance of the averages.
    {#W12.153-13} So, on a bond b = (x, y) of Z″_k, the deviation of U_{k,Λ}'s data from those of U₁^{h̃^{−1}} is X_s := −(1/i)log((w_x^{−1}w_y)^{−1}M^·(U_{k,Λ})(b)) = −(1/i)log(w_y^{−1}M^·(U^{ax})(b)w_y), with |X_s| = |log M^·(U^{ax})(b)|.
    {#W12.153-14} This carries the gain (a_n/a_k) of #W12.143-3.
    {#W12.153-15} On the interface bonds of the other layers the deviation is w(x), with no gain.
    {#W12.153-16} These lie at the two interfaces of Z″_k ∩ Ω″^∼_{h+1}.
    {#W12.153-17} The interface with the layer k, Λ ∩ Ω″_k, is at a distance ≥ 2M₁a_h from the cut, since ∂Ω″^∼_{h+1} lies in the layer h at that distance from its boundaries (CRE p.257 l.9–15) and Ω″_k ⊂ Ω″_{h+1}.
    {#W12.153-18} So a walk that meets the strip reads these interface bonds only through a cube of a layer ≥ h − 1, across at least h − 5 of the collar's layers, as in *The crossings.* of *The strip.*, in d_col at the reflex edges of Ω.
    {#W12.153-19} A walk that does not meet the strip and reads these bonds is aligned (*The enlargement-only walks.*), with its cubes at layers ≥ h − 1, where its young-history factor (ε/a_{m(ω)})^{γ_w}, with m(ω) ≥ h − 1, is within L of (ε/a_h)^{γ_w} and needs no gain.
    {#W12.153-20} There is no interface with Λ^c.
    {#W12.153-21} The domains are nested, Λ ⊃ Z″_k ⊃ … ⊃ Z″_{h+1} ⊃ (Ω″^{∼2}_{h+1})^c (LFR I p.195 l.43).
    {#W12.153-22} Λ is Z″_k with one more layer of M-cubes of the scale k added (LFR I (1.73), p.192).
    {#W12.153-23} The intersection with Z in Λ = (Ω^{∼4}_{k₀+1})^c ∩ Z and Z″_k = (Ω^{∼5}_{k₀+1})^c ∩ Z is inactive near ∂Z.
    {#W12.153-24} Z is a component of Λ_k^c (CRE p.255 l.25), so the points of Z^c next to Z lie in Λ_k ⊂ Ω_k ⊂ Ω_{k₀+2}, with k₀ + 2 ≤ k since N₀ ≥ 2 (LFR I p.179 l.10, with R_{k−N₀+1} ≥ L).
    {#W12.153-25} And (Ω^{∼4}_{k₀+1})^c ⊂ Ω^c_{k₀+1}, which the layer k₀ + 1, wider than RM in its own units (PRT2 (2.2)), separates from Ω_{k₀+2}.
    {#W12.153-26} So Λ, Z″_k, and the cut lie at a distance ≥ RMa_{k₀+1} from ∂Z, and Λ is Z″_k with one layer of M-cubes added all around.
    {#W12.153-27} So the data bonds of Z″_k are at a distance ≥ Ma_k from Λ^c, and no endpoint of theirs is shared with a bond of Λ^c.
    {#W12.153-28} The part of the cut in Z lies in Z″_k too (LFR I p.195 l.42).
    {#W12.153-29} Off Z, Ω″_{h+1} = Ω_{h+1} (LFR I (1.12)), so parts of the cut and its strip may lie outside Z; there the background of the 𝐁₁ problem (1.57) is still U_{k,Λ} (LFR II p.371 l.29, l.36–37), the cut lies in 𝐁_k's layer h since Ω″_{h+1} = Ω_{h+1}, and VAR (10) at the layer h for U_{k,Λ}, a VAR minimiser for 𝐁_k with data satisfying VAR (7), gives the current gain (a/a_h)³ used in *The sources.* The tilde enlarges a small-field domain (Λ = (Ω^{∼4}_{k₀+1})^c ∩ Z ⊃ Z″_k = (Ω^{∼5}_{k₀+1})^c ∩ Z), so (Ω″^∼_{h+1})^c ∩ Z ⊂ (Ω″_{h+1})^c ∩ Z = Z″_{h+1} (LFR I (1.12), p.179).
    {#W12.153-30} So ∂Λ is at a distance ≥ Ma_k from the cut, and it does not meet the strip, whose width is 2M₁a_2 < Ma_k, since k ≥ h + 1, once L^{h−1} > 2M₁/M.
    {#W12.153-31} For the finitely many h ≤ h₀ below that threshold, ε/a_h ≥ L^{−h₀}, so each run's strip term is at most L^{h₀γ_w}(ε/a_h)^{γ_w} times its bound, and, with run A's term through ℒ_ι𝒥 as in *The strip.*, the difference fits δ_w(ω) with C_w enlarged by (1 + C_ℒ)L^{h₀}.
    {#W12.153-32} By the covariance of U_{𝐁₁}, U₁^{h̃^{−1}} = U_{𝐁₁}(data(U_{k,Λ})e^{iX_s}) up to a gauge transformation that is 1 at the data points, where X_s also includes the deviations w(x) on the interface bonds of the other layers that share an endpoint with Z″_k, so
    {#W12.154} U₁ = (exp iη𝐇_{𝐁₁}(X_s)U_{k,Λ})^{u_s^{−1}}, u_s := u′h̃^{−1},
    {#W12.155} with u′ the gauge factor of the representation at X_s, and U^g(b) = g_xU(b)g_y^{−1}.
    {#W12.155-1} This is the form of (1.57) with X_s for X and u_s for u₁.
    - {#W12.156} The change of construction.
      {#W12.156-1} At s = 1 both representations give U₁.
      {#W12.156-2} At complex s they do not.
      {#W12.156-3} The localisation expansion of (1.62) (p.374 l.8–10) decouples the operators of 𝐇_{𝐁₁} walk by walk, and the expansions at X and at X_s have different terms, with equal sums only at s = 1.
      {#W12.156-4} So the X_s representation is a change of Bałaban's construction, made in both runs.
      {#W12.156-6} The properties of LFR II's terms that the later steps use are their localisation, their analyticity on the class, and their bounds, and they hold for the X_s representation:
      - {#W12.157} Localisation.
        {#W12.157-1} A term of the X_s representation depends on (𝐔, 𝐉) through U_{k,Λ}, as in Bałaban's, and also through w, a product of U_{k,Λ}'s links along contours in Λ.
        {#W12.157-2} Every domain Y of the re-summation that meets Z has Y ∩ Z^∼ a union of components of Z^∼ (p.377 l.5–8).
        {#W12.157-3} So a term whose domain meets Λ ⊂ Z contains Λ already, and the dependence of w on the contours in Λ changes no domain.
      - {#W12.158} No complex gauge transformation. w is a product of the links of U_{k,Λ}(𝐔), analytic on the class, but G^c-valued at complex 𝐔: on the class the links are e^{iηA′}U with U G-valued and |A′| bounded by the class radius α̃_{1,k} in the units of the scale k (CRE (2.39)), and over the ≤ O(1)dMa_k/ε fine bonds of a contour Im log w reaches O(1)dMα̃_{1,k}, which is O(dM) times the class radius.
        {#W12.158-1} So h̃ and u_s cannot be applied to configurations through the complex gauge invariance of the terms, which holds only for u near G (CRE p.259 (iii), RG II p.011 l.27–28).
        {#W12.158-2} For a gauge-invariant analytic function of the single configuration U₁ the gauge factor can be dropped: at real 𝐔 and s = 1 the values at U₁^{X_s}(1) := exp(iη𝐇_{𝐁₁}(X_s)(1))U_{k,Λ} and at U₁ agree, both sides are analytic on the class, which is connected and contains the real configurations as a totally real submanifold of maximal dimension, and the identity theorem extends the equality.
      - {#W12.159} *The boundary-layer data of (1.62).* LFR II's terms are not functions of U₁ alone.
        {#W12.159-1} In (1.62) (p.373 l.37–43) the boundary-layer data are u_{1,−}^{−1}exp iQ̃(η𝐇_{𝐁₁})R(u_{1,+})M^·(U_{k,Λ}), while the interior data V″, M^·(U_0^{(AL)}), and 1 are the original variables, and Bałaban states that this gauge factor cannot be removed, "because we use the two different representations for fields at the boundary of the boundary layer" (p.373 l.27–29, applied to (1.62) at l.44).
        {#W12.159-2} The X_s representation keeps this structure, with 𝐇_{𝐁₁}(X_s) for 𝐇_{𝐁₁} and u′ for u₁, because the boundary layers of the domains Y₂ do not meet Z″_k, and h̃ = 1 there.
        - {#W12.160} Y₂ contains every component of Λ it meets.
          {#W12.160-1} Each component of Y₂′ contains a component of Λ (p.373 l.33–34).
          {#W12.160-2} The localisation expansion of 𝐇_{𝐁₁} decouples only on the cubes of σ̃₀, which are disjoint with Λ (p.373 l.32), so a domain of the expansion that meets a component Λ_c contains it.
          {#W12.160-3} In (6.10) [I] = RG II (1.10) (RG II p.4 l.3–16) only the cubes of σ ⊂ σ₀ are decoupled, and every domain Y(σ) contains the cubes outside σ₀, as it contains □̃⁴.
          {#W12.160-4} With σ̃₀ in place of σ₀, every cube meeting Λ lies in every Y(σ).
          {#W12.160-5} A component Λ_c is connected by bonds, which are axial, so the cubes meeting it are connected through (d − 1)-dimensional walls, and the component of Y(σ) that meets Λ_c contains all of them.
          {#W12.160-6} This agrees with Bałaban's description of the domains Y₂′, each component of which "contains at least one component of Λ" (p.373 l.34–35).
          {#W12.160-7} Y₁ is the smallest domain of 𝐃_k containing X and the components of Z that X meets (p.373 l.15–16).
          {#W12.160-8} If X meets the component Z_c ⊃ Λ_c, then Y₁ ⊃ Z_c ⊃ Λ_c.
          {#W12.160-9} If not, the rounding of X to 𝐃_k adds M-cubes of the scale k that meet X, and these do not reach Λ_c, since Λ_c lies at a distance ≥ RMa_{k−1} from ∂Z_c (the layers k₀ + 1, …, k − 1 separate Λ_k ⊂ Ω_k from (Ω^{∼4}_{k₀+1})^c ⊃ Λ, *The representation with the gain.*), and RMa_{k−1} > 2dMa_k for R ≥ 2dL (the factor d converts between the ℓ¹ and the Euclidean distance), which holds for g small, since R_j ≥ (log g_j^{−2})^r (CRE (2.5)).
        - {#W12.161} So ∂Y₂ does not pass through the interior of any component of Λ, and the boundary layer Y₂ ∖ Y₂⁰, of the width ≤ 2M₁ at its scale (p.373 l.26–27), at most 2M₁a_k since 𝐁₁ has no scale above k, lies within 2M₁a_k of Λ^c wherever it meets Λ.
          {#W12.161-1} Z″_k lies at a distance ≥ Ma_k from Λ^c (Λ is Z″_k with one layer of M-cubes of the scale k added, LFR I (1.73)), and M > L²M₁ > 4M₁ ("M₁ < M₂ < M … we can take M₂ = L²M₁, and M will be chosen much larger than M₂", CRE p.245 l.35–37), so the boundary layers lie at a distance ≥ ½Ma_k from Z″_k.
        - {#W12.162} h̃ is defined at the data points by h = w on those of Z″_k ∩ Ω″^∼_{h+1} and h = 1 elsewhere, and its extension to the fine lattice is free (*The representation with the gain.*).
          {#W12.162-1} Take h̃ = h at every data point, h̃ = w at the other fine points at a distance < a_k from Z″_k, and h̃ = 1 at the remaining fine points.
          {#W12.162-2} The scale-k data points of Λ ∩ Ω″_k at the distance a_k from Z″_k keep h̃ = h = 1.
          {#W12.162-3} Then h̃ = 1 on every boundary layer, so there u_s = u′, the gauge factor of the representation at X_s.
          {#W12.162-4} By CMP 98 (106), u′ at x is the same local analytic function of 𝐇_{𝐁₁}(X_s) restricted to the block of x as u₁ is of 𝐇_{𝐁₁}(X), as Bałaban uses at p.373 l.30–31.
        - {#W12.163} At s = 1, U₁ = (exp iη𝐇_{𝐁₁}(X_s)U_{k,Λ})^{u′^{−1}} near each boundary layer.
          {#W12.163-1} So U₁'s boundary-layer data are u′_−^{−1}exp iQ̃(η𝐇_{𝐁₁}(X_s))R(u′_+)M^·(U_{k,Λ}), and (1.62) holds with 𝐇_{𝐁₁}(X_s) and u′, with the same interior data.
          {#W12.163-2} At complex s, this is the function substituted into the term. 𝐇_{𝐁₁}(X_s)(s) has the bounds of 𝐇_{𝐁₁}(X)(s) up to O(1)M (*Analyticity and bounds.* below).
          {#W12.163-3} Bałaban's smallness on the boundary layers is by decay: "The function 𝐇_{𝐁₁} is very small on Y₂∖Y₂⁰, again by the exponential decay and the localization of its argument" (p.375 l.7–8).
          {#W12.163-4} For 𝐇_{𝐁₁}(X_s) it follows from Bałaban's smallness of 𝐇_{𝐁₁}(X) and from the decay of D := 𝐇_{𝐁₁}(X_s) − 𝐇_{𝐁₁}(X) away from Z″_k.
          - {#W12.164} The support.
            {#W12.164-1} X_s − X is supported on the data bonds of Z″_k and on the interface bonds that share an endpoint with them.
          - {#W12.165} The weight.
            {#W12.165-1} Let ω′(x) := exp(δ_ωd′(x)), with d′(x) the distance from Z″_k in the units of 𝐁₁'s layers and δ_ω := δ_min/2, with δ_min of §11's κ₁ replay, two thirds of the rate ¾δ_min that the composite kernels of the problem's operators keep at complex s (*The decoupled functions.* below).
            {#W12.165-2} Let |·|_{ω′} be VAR's norm with each entry weighted by ω′(x), the Hölder entry local at x, as |·|_g in *The strip.* Then ω′ = 1 on the data bonds of Z″_k and ω′ ≤ e^{δ_ω} on the interface bonds of the support, a factor absorbed into the O(1) below. ω′(x)/ω′(y) ≤ exp(δ_ωd′(x, y)), which the kernel decay beats, so the operators are bounded in |·|_{ω′} with constants changed by O(1).
          - {#W12.166} The equation.
            {#W12.166-1} D solves the difference of the (111) equations.
            {#W12.166-2} Its data source is X_s − X, and the current term of the background U_{k,Λ} cancels.
            {#W12.166-3} The other sources are differences of products, each with a factor D and a factor 𝐇_{𝐁₁}(X_s), 𝐇_{𝐁₁}(X), or the background's current J. So ω′|s| ≤ C(|𝐇_{𝐁₁}(X_s)|_{(−1)} + |𝐇_{𝐁₁}(X)|_{(−1)} + |J|)|D|_{ω′}, and |D|_{ω′} ≤ 2C_{H₁}|X_s − X|.
          - {#W12.167} The decoupled functions.
            {#W12.167-1} At complex s, |s(Δ)| ≤ e^{κ₁}, a walk term of 𝐇_{𝐁₁}(·)(s) carries at most e^{mκ₁}, m the number of its s-parameters.
            {#W12.167-2} RG II spends the whole decay δ₀d(ω) on this factor (p.5 l.13–16), so it prints no decay at complex s.
            {#W12.167-3} The operators of 𝐇_{𝐁₁} (H, H₁, and 𝔊) are composites, whose walks decay at the rate δ_min (§11, *The junction sums.*).
            {#W12.167-4} Here only a quarter of δ_min is spent on the s-factors, as in §11's *The condition on M.*: by the geometric inequality for d_T (§11, *The distance of a composite walk.*), e^{−¼δ_min d_T}e^{mκ₁} ≤ 1 for m above the threshold under M ≥ 4κ₁/(ρδ_g), and e^{mκ₁} is bounded by the constant written e^{16κ₁} below it.
            {#W12.167-5} So 𝐇_{𝐁₁}(·)(s) has kernel bounds in the form of (3.108) at the rate ¾δ_min, times e^{16κ₁}, and ¾δ_min exceeds δ_ω = δ_min/2 by ¼δ_min, the margin of the weighted contraction below.
            {#W12.167-6} The same holds for D(s).
            {#W12.167-7} This use of the rate is separate from the form (c) and the crossings of the strips, which bound other terms.
          {#W12.168} The boundary layers of Y₂ lie at a distance ≥ ½Ma_k from Z″_k (*The boundary-layer data of (1.62).*), so there |D(s)| ≤ 2C_{H₁}(|X_s| + |X|)e^{−δ_ωM/2} in the units of their layers.
          {#W12.168-1} At complex points the absolute bounds on X_s and X and the comparison of this decay with the room of the boundary-layer entries are (D1) and (D2) of *Analyticity and bounds.* below.
          {#W12.168-2} No complex gauge factor with a large imaginary part enters the boundary-layer data.
          {#W12.168-3} The factor h̃ acts only inside Z″_k's neighbourhood, through the data X_s of the fixed point.
      - {#W12.169} Analyticity and bounds.
        {#W12.169-1} X_s enters only as the data of 𝐇_{𝐁₁}, and the X_s representation differs from Bałaban's only where 𝐇_{𝐁₁}(X_s)(s) is read.
        - {#W12.170} *Where it is read.* In (1.62) (p.373 l.37–43) 𝐇_{𝐁₁} enters only through the boundary-layer data u′_−^{−1}exp iQ̃(η𝐇_{𝐁₁})R(u′_+)M^·(U_{k,Λ}) on Y₂ ∖ Y₂⁰; the interior data V″, M^·(U_0^{(AL)}), and 1 are the original variables.
          {#W12.170-1} (1.62) enters (1.61) through its averages on the boundary layer (Y₁^0)^c ∩ Y₁ (p.373 l.18–22), and the first-stage terms read U₁ on X ⊂ Z^c (p.372 l.39–p.373 l.6).
          {#W12.170-2} The boundary layers of Y₂ lie at a distance ≥ ½Ma_k from Z″_k (*The boundary-layer data of (1.62).*).
          {#W12.170-3} The boundary layer of Y₁ lies far from Λ: if X meets the component Z_c ⊃ Λ_c, then Y₁ ⊃ Z_c and ∂Y₁ lies outside Z_c, at a distance ≥ RMa_{k−1} from Λ_c; if not, every point of Y₁ lies within 2dMa_k of Z_c^c, so at a distance ≥ RMa_{k−1} − 2dMa_k from Λ_c (*The boundary-layer data of (1.62).*).
          {#W12.170-4} Z^c lies at a distance ≥ RMa_{k₀+1} from Λ (*The representation with the gain.*).
          {#W12.170-5} So, where it is read, the X_s representation differs from Bałaban's by D(s) := 𝐇_{𝐁₁}(X_s)(s) − 𝐇_{𝐁₁}(X)(s) on blocks at a distance ≥ ½Ma_k from Z″_k, by the change of u′ against u₁ that D(s) causes there (both are the same local analytic function of 𝐇_{𝐁₁} on the block, CMP 98 (106)), and, through (1.61), by the response of (1.62)'s minimiser to these data changes, bounded by VAR (9)–(10) in the size of the change.
          {#W12.170-6} U₁^{X_s}(s) itself is not read on Z″_k.
        - {#W12.171} *The absolute bound at complex points.* Let 𝐔 = U′U be the decomposition of CRE (2.39) (p.261), with U G-valued and U′ = exp iεA′.
          {#W12.171-1} At a complex point the data of U_{k,Λ}(𝐔) are M^·(𝐔) on Λ^c and V_Λ^{(A)}(M^k(𝐔)) on Λ (LFR II p.374 l.40–41), the axial representative of the minimal orbit of LFR I Proposition 1 (p.194) at complex data.
          {#W12.171-2} Proposition 1 prints no bound at complex data, so its proof is run there.
          {#W12.171-3} Bałaban proves it (LFR II p.359 l.2–28) through the equation (1.13) for V_Λ = exp(iB′)V_k on Λ, in the axial gauge G₀ of Λ, with V_k an extension of the data into Λ: P₀H*_{1,k}Δ₁H_{1,k}P₀ is invertible with the bound γ₀^{−1}2d(100M)⁵ by (1.9), the source is the current J_{k,Z} of U_{k,Z}(V_k), and the contraction (with VAR's Proposition 4) gives |B′| ≤ 2γ₀^{−1}2d(100M)⁵B₃²4ε_k. "The above equations, bounds and statements are valid for 𝐠^c-valued fields" (p.359 l.26), and at complex points Bałaban takes V_k := M^k(𝐔),
          {#W12.171-4} "and all the bounds above hold with ε_k replaced by O(α_{0,k} + α_{1,k})" (p.358 l.27–29, for 𝐔 in the class at the scale k).
          {#W12.171-5} Run at the complex data: the extension is M^k(𝐔) on Λ, and |∂M^k(𝐔) − 1| ≤ O(1)α̃_{0,k}, since CRE (2.34) bounds the complex plaquettes of 𝐔 directly and (2.39) bounds the imaginary parts of the conjugating transports by O(1)α̃_{1,k}.
          {#W12.171-6} The source and the error term O(1)(M⁶R_kε_k + exp(−R_k)) of (1.7) (p.358 l.4) take ε_k → O(1)(α̃_{0,k} + α̃_{1,k}), and the error term stays ≤ γ₀(2d(100M)⁵)^{−1}, half of the lower bound γ₀(d(100M)⁵)^{−1}‖B′‖² that (1.8) gives for γ₀‖∂B′‖², so (1.9) holds for γ small (γ₀ is LFR II's constant of (1.7)), since M⁶R_k(α̃_{0,k} + α̃_{1,k}) = O(g_k(log g_k^{−2})^{q₀+r}) and R_k → ∞ (#W8.23-11-1).
          {#W12.171-7} So
          {#W12.172} V_Λ(M^k(𝐔)) = exp(iB′)M^k(𝐔) on Λ, |B′| ≤ C_Λ(α̃_{0,k} + α̃_{1,k}), C_Λ := O(1)γ₀^{−1}d(100M)⁵B₃²,
          {#W12.173} for γ small.
          {#W12.173-1} The multiscale class enters through α̃_{i,n} ≤ (1 + β₀)α̃_{i,k} for n ≤ k (g_n ≤ (1 + β₀)g_k by CRE (2.6), and g ↦ g(log g^{−2})^q is increasing for g small).
          {#W12.173-2} At the real configuration U the same proof gives the real minimiser U^r := U_{k,Z}(V_Λ(M^k(U))). By LFR I (1.78) at ε = O(1)α̃_{0,k} (the generalisation from ε_k to ε that LFR II p.359 l.27–28 calls obvious), |∂V_Λ − 1| < O(1)B₅M⁵α̃_{0,k} on Λ, so the plaquettes of U^r are < O(1)B₃B₅M⁵α̃_{0,k}(ε/a)² by VAR Theorem 1.
          {#W12.173-3} VAR Theorem 1 assumes VAR (7) for the data (p.279 l.9), and VAR obtains (7) "by Proposition 2 [4]" (p.278 l.46), [4] being CMP 98 (VAR p.309 l.24). CMP 98 (53)–(54) (p.26 l.27–53) bound |Ū^j(∂p) − 1| < 2α₀ from the plaquette condition (52) on U alone, locally on the blocks of p. The data are averages M^·(U) of the one fine configuration U, so every (∂V)(p′) of VAR (7), the mixed plaquettes with V̄ included, is a plaquette of a j-fold average of U. So the class's plaquette bound gives (7) with ε₁ = O(1)α̃_{0,k}; VAR (2)'s current condition is not used.
          {#W12.173-4} Let Ŷ := −i log(𝐕V^{−1}), with 𝐕 and V the complex and the real data, so that e^{iŶ} is the V′ of VAR (172) for this pair. At a data bond of the layer n on Λ^c, |Ŷ| ≤ O(1)α̃_{1,n}, since the bond averages a_n/ε fine bonds of U′, each with ε|A′| < α̃_{1,n}ε/a_n. On Λ, Ŷ = −i log(e^{iB′(𝐔)}e^{iZ}e^{−iB′(U)}) with e^{iZ} := M^k(𝐔)M^k(U)^{−1} and |Z| ≤ O(1)α̃_{1,k}, so within the logarithm charts of (D1) |Ŷ| ≤ 2(|B′(𝐔)| + |B′(U)|) + O(1)α̃_{1,k}.
          {#W12.173-5} So |Ŷ| ≤ C_Ŷ(α̃_{0,k} + α̃_{1,k}), C_Ŷ := O(1) + 4C_Λ.
          {#W12.173-6} VAR's representation of the minimiser about a minimiser ((172)–(175), p.305 l.31–53), in which ℋ is an analytic function of B (p.305 l.11–12, p.306 l.1–2), continues analytically to the complex data and gives U_{k,Λ}(𝐔) = (exp(iη𝐇_c)U^r)^{u^{−1}}, with |𝐇_c|_{(−1)} and its gradient entry a²|∇𝐇_c| ≤ C_H|Ŷ| and u the gauge factor of CMP 98 (106), local to the k-blocks.
          {#W12.173-8} Proposition 6's ε₄ = 3B₀C₁B₃ε₁ (p.295 l.49, with VAR's own C₁) is not linear in |B|, because of the current term B₀|J|_{(−3)} < B₀C₁B₃ε₁ of (117) (p.295 l.12).
          {#W12.173-10} About a minimiser U₀ = U_k(V₀) the current satisfies 𝔓*(U₀)J = 0 ((170)–(171), p.305 l.15–29), and the equation (175) for 𝒜₁ has no current term.
          {#W12.173-11} So, in the norm max{|·|_{(−1)}, |∇·|_{(−2)}}, (117) bounds the map 𝒜 ↦ −𝔊(δV/δA′)(𝒜 + H₁B) on the ball |𝒜| ≤ ρ by B₀C₄(ρ + B₀|B|)², and (120) gives it the contraction constant 4B₀C₄(ρ + B₀|B|). Let ρ := 4B₀³C₄|B|² and B₀|B| ≤ (16B₀C₄)^{−1}. Then ρ ≤ ¼B₀|B|, so B₀C₄(ρ + B₀|B|)² ≤ (25/16)B₀³C₄|B|² ≤ ρ and 4B₀C₄(ρ + B₀|B|) ≤ 5/16. Hence the solution 𝒜₁ of (175), unique in VAR's space (115), satisfies |𝒜₁| ≤ 4B₀³C₄|B|².
          {#W12.173-12} In (174), ℋ = 𝒜₁ + H₁B − HD(𝒜₁ + H₁B), with |H₁B| ≤ B₀|B| (Theorem 3.13 of [5], as on p.295 l.9). So x := max{|𝒜₁ + H₁B|_{(−1)}, |∇(𝒜₁ + H₁B)|_{(−2)}} ≤ (5/4)B₀|B|, and VAR (57)–(58) (p.286 l.38 – p.287 l.6), from (55), bound both norms of ℋ by x + 4B₀C₂x² for x ≤ (18C₂B₀)^{−1}.
          {#W12.173-13} VAR's B and B′ = Ŷ satisfy |B| ≤ dL sup|Ŷ|, the relation of p.295 l.15. Let |Ŷ| ≤ r_H := min{(16dLB₀²C₄)^{−1}, (24dLB₀²C₂)^{−1}}, which (D1) secures. Then B₀|B| ≤ (16B₀C₄)^{−1} and B₀|B| ≤ (24B₀C₂)^{−1}, so x ≤ (18C₂B₀)^{−1}, 4B₀C₂x ≤ ¼, and x + 4B₀C₂x² ≤ (25/16)B₀|B|. Hence |ℋ|_{(−1)}, |∇ℋ|_{(−2)} ≤ C_H|Ŷ| with C_H := 2dLB₀.
          {#W12.173-14} The representation (179)–(180) has the same function ℋ (p.306 l.47).
        - {#W12.174} *The data X and X_s.* The plaquettes of U^r are < O(1)B₃B₅M⁵α̃_{0,k}(ε/a)², and exp(iη𝐇_c) moves them by ≤ O(1)C_H|Ŷ|(ε/a)².
          {#W12.174-1} The plaquette holonomies of U_{k,Λ}(𝐔) are those of exp(iη𝐇_c)U^r conjugated by values of u, whose imaginary part is of the size of 𝐇_c.
          {#W12.174-2} So they are ≤ O(1)(B₃B₅M⁵ + C_HC_Ŷ)(α̃_{0,k} + α̃_{1,k})(ε/a)².
          {#W12.174-3} The data angle of U^{ax} = U_{k,Λ}^w at a bond b of the layer n is the holonomy of the loop made of the two axial contours to the endpoints of b and of b itself.
          {#W12.174-4} By the lattice Stokes formula it is a product of plaquette holonomies conjugated by transports along the contours, over an area ≤ O(1)dMa_ka_n.
          {#W12.174-5} Under §8's Ad conditions for u and for the transports along the contours (stage 6), the conjugations by u and by these transports, along contours of the length ≤ O(1)dMa_k, distort by at most 2.
          {#W12.174-6} So
          {#W12.175} |X_s| ≤ C_s(a_n/a_k)(α̃_{0,k} + α̃_{1,k}), C_s := O(1)dM(B₃B₅M⁵ + C_HC_Ŷ),
          {#W12.176} at real and complex points alike, on the data bonds of Z″_k.
          {#W12.176-1} On the interface bonds that share an endpoint with Z″_k, X_s − X is log w(x) at that endpoint, with no gain.
          {#W12.176-2} In Bałaban's gauge of Λ, U^r = U(𝐁_k(Λ), M^·(U^r)) by (1.85) (LFR I p.197 l.16–19), and its data are within O(1)d²B₃B₅M⁶α̃_{0,k} of 1 by (1.83) and the estimate of p.197 l.10 at ε = O(1)α̃_{0,k}: this is (1.84) with the factor 11d² of l.10 kept.
          {#W12.176-3} So by VAR's representation its links are exp(iη𝐀^r) up to the local gauge factor, with a_k|𝐀^r| ≤ O(1)d²C_HB₃B₅M⁶α̃_{0,k}, and 𝐇_c adds C_HC_Ŷ(α̃_{0,k} + α̃_{1,k}). w(x) is a product of ≤ O(1)dMa_k/ε fine links, so |log w(x)| ≤ C_I(α̃_{0,k} + α̃_{1,k}), C_I := O(1)d³MC_H(B₃B₅M⁶ + C_Ŷ).
          {#W12.176-4} C_s is taken ≥ C_I, so |X_s| ≤ C_s(α̃_{0,k} + α̃_{1,k}) holds on the interface bonds as well, without the gain.
          {#W12.176-5} The same bound gives |Im log w_y| ≤ C_I(α̃_{0,k} + α̃_{1,k}), so under §8's Ad condition for w_y (stage 6) the conjugation Ad(w_y) in X_s = −(1/i)log(w_y^{−1}M^·(U^{ax})(b)w_y) distorts by at most 2.
          {#W12.176-6} Bałaban's data X are those of U_{k,Λ}(𝐔) in his axial gauge of Λ (LFR I p.197 l.2–12).
          {#W12.176-7} At real points his finer data M^j(U₀) deviate from Q^{s*}_{k−j}V_Λ, which puts the scale-k angle on the bonds that cross k-block faces and 1 inside the k-blocks, by "< 11d²O(1)B₃B₅M⁵ε_k" (p.197 l.10), an estimate by the Stokes formula along his contours ((1.80) and (1.65) of [14]).
          {#W12.176-8} At complex points the same Stokes formula holds for the G^c-valued configuration: the deviation is a product of plaquette elements lassoed to the base point along his contours, and their number is the area count of the real estimate, a geometric count.
          {#W12.176-9} The lassos conjugate by transports along contours in Λ whose imaginary parts are ≤ O(1)dM(1 + C_G)C_HC_Ŷ(α̃_{0,k} + α̃_{1,k}) (*The curvature.* below), so under §8's Ad condition for the transports along the contours (stage 6) each Ad is within a factor 2 of isometric, and the complex plaquettes are ≤ O(1)(B₃B₅M⁵ + C_HC_Ŷ)(α̃_{0,k} + α̃_{1,k})(ε/a_k)² on Λ, as for X_s.
          {#W12.176-10} This gives |X| ≤ (1 + 22d²)C_s(α̃_{0,k} + α̃_{1,k}) at real and complex points.
          {#W12.176-11} VAR Proposition 6 needs only the absolute smallness of its data, which (D1) gives.
          {#W12.176-12} So 𝐇_{𝐁₁}(X_s)(s) and 𝐇_{𝐁₁}(X)(s) are analytic on the class, with the bounds of Proposition 6 and (3.133) at complex s, as in §3(d).
        - {#W12.177} *The domain.* U₁^{X_s}(s) = exp(iη𝐇_{𝐁₁}(X_s)(s))U_{k,Λ}(𝐔) is not read on Z″_k (*Where it is read.*), and U_{k,Λ}(𝐔) is the same function, the background, in both representations.
          {#W12.177-1} So the X_s representation lies in Bałaban's domain once the changes it makes where it is read (D(s), the change of u′, and the responses of the minimisers of (1.62) and (1.61)) stay below a fixed fraction c of the room of the entries they move.
          {#W12.177-2} Two conditions give this, with C_{H₁} the constant of the bounds of 𝐇_{𝐁₁}(·)(s):
          - {#W12.178} (D1) Absolute smallness.
            {#W12.178-1} (C_s + C_Λ + C_Ŷ)(α̃_{0,k} + α̃_{1,k}) ≤ r_V, with r_V the least of the radius of absolute smallness in VAR's Propositions 4 and 6, the radius of the analytic charts of the logarithms above, and r_H, the threshold of the linear bound of ℋ (#W12.173-13); this holds for γ small.
            {#W12.178-2} It also places U_{k,Λ}(𝐔) in PBG's complex domain (3.35)–(3.37), whose constants are fixed, so the operators of 𝐇_{𝐁₁} there have PBG's bounds.
          - {#W12.179} (D2) The decay against the room. 𝐇_{𝐁₁} lives on the layers n ≤ k of 𝐁₁.
            {#W12.179-1} A data point of the layer n on a boundary layer of Y₂ lies at the physical distance ≥ ½Ma_k from Z″_k.
            {#W12.179-2} For n = k this gives d′ ≥ M/2.
            {#W12.179-3} For n < k the point lies outside Λ, which belongs to the layer k, so a path from Z″_k to it runs ≥ (M − 2M₁)a_k ≥ ½Ma_k inside Λ (M ≥ 4M₁), which counts ≥ M/2 in the units a_k.
            {#W12.179-4} It then crosses each layer m = n + 1, …, k − 1, each at least M₁ ≥ 1 wide in its own units (CRE p.256 l.57–62), so d′ ≥ M/2 + (k − n − 1).
            {#W12.179-5} There |D(s)| ≤ 2C_{H₁}(|X_s| + |X|)e^{−δ_ωd′} ≤ 48d²e^{δ_ω}C_{H₁}C_s(α̃_{0,k} + α̃_{1,k})e^{−δ_ω(M/2 + k − n)}, with 2 + 22d² ≤ 24d².
            {#W12.179-6} The room there is α̃_{1,n} for A′, which D moves with its real and imaginary parts, and α̃_{0,n} for the plaquettes, which D moves by |D|(ε/a)².
            {#W12.179-7} CRE (2.6) gives g_k² ≤ (1 + g_k²β′(k − n))g_n² ≤ (k − n + 1)g_n² for g_k²β′ ≤ 1. Since g ↦ g(log g^{−2})^q is increasing for g small, α̃_{i,k}/α̃_{i,n} ≤ 1 if g_k ≤ g_n, and otherwise α̃_{i,k}/α̃_{i,n} ≤ g_k/g_n. So α̃_{i,k}/α̃_{i,n} ≤ (k − n + 1)^{1/2}.
            {#W12.179-8} With c_ω := sup_{t≥0}(1 + t)^{1/2}e^{−δ_ωt/2} and α̃_{1,k} = λ_Rα̃_{0,k} (the choice below), both moves are below c times their room when
            {#W12.180} O(1)d²C_{H₁}C_sc_ω(1 + λ_R)e^{−δ_ωM/4} ≤ c.
            {#W12.181} C_s and λ_R grow polynomially in M. C_H and δ₀ are constants of VAR and PBG, which depend on d and L only (PBG Theorem 3.1, p.397 l.37: "M₁, δ₀, a₀, B₀ dependent on d and L only", for M ≥ M₁).
            {#W12.181-1} C_{H₁} carries in addition RG II's factor e^{16κ₁} (RG II p.5 l.16). κ₁ is fixed by lower bounds in κ, δ, and L only: ¼(κ₁ − 1) ≥ (1 − δ)κ (RG II p.9 l.16), (1/16)κ₁ ≥ (1 − 2δ)κ (p.9 l.26), ⅛(κ₁ − 1) ≥ (1 − 3δ)κ (p.16 l.20), ½(κ₁ − 1) ≥ 2Lκ (p.20 l.17), and "κ₁ sufficiently large" (p.8 l.17). κ is fixed before M ("we take M sufficiently large, so that δ₀M ≥ κ", p.21 l.36), and RG II's conditions that tie M to κ₁ are lower bounds on M (p.5 l.15, p.16 l.7).
            {#W12.181-2} So κ₁ does not depend on M. RG II's M-dependent factors, such as E₀(α₁/α₃)⁵ (p.7 l.27) and O(M^q) (p.8 l.24), multiply ε₁ and are absorbed for γ small, so they feed back into no lower bound on M. So LFR's M enters none of C_H, C_{H₁}, and δ₀, and (D2) is a lower bound on M.
            {#W12.182} The change of u′ is O(1)|D(s)| at the same points, since u′ is a local analytic function of 𝐇_{𝐁₁} on the block (CMP 98 (106)).
            {#W12.182-1} The minimisers of (1.62) and (1.61) are analytic in their data (VAR Proposition 6, last statement, p.296 l.2), so each response is O(1) times the change of its data, and it decays away from the changed data: the linear part is H₁ applied to the change, with H₁'s kernel decay, and the nonlinear part is bounded in the weighted norm |·|_{ω′} by the contraction, as for D in *The weight.* and *The equation.*
            {#W12.182-2} (1.62)'s response enters (1.61) only through the averages on the boundary layer of Y₁.
            {#W12.182-3} (1.61)'s minimiser U^0_k responds on all of Y₁, Λ^∼ included, where 𝐄(X, U^0_k) reads it.
            {#W12.182-4} The boundary layer of Y₁ lies at a distance ≥ RMa_{k−1} − 2dMa_k ≥ Ma_k from Λ_c (#W12.170-3) once R ≥ (2d + 1)L, which holds for g small by CRE (2.5), as in #W12.160-9.
            {#W12.182-5} So on Λ^∼ the response of U^0_k is below the response at the boundary layers times e^{−δ_ωM/2}.
            {#W12.182-6} These three effects are absorbed into the O(1) of (D2).
          - {#W12.183} The ratio.
            {#W12.183-1} (D2) needs α̃_{1,k}/α̃_{0,k} bounded uniformly in k.
            {#W12.183-2} This holds with q₁ := q₀ and C₁ := λ_RC₀, λ_R := K_RLM + 1, the factor L for the near domains at a finer layer, where RG I's M reads LM (the Cauchy note's #C5.34-4 and #C5.35-1), with K_R ≥ 4B₃²O(1) and K_R ≥ O(1)(1 + B₃O(1)), with the leading O(1)s of RG I p.277 l.54 and the largest of those of p.285 l.17, p.285 l.23, and p.280 l.44; the lower bound on M is (D2).
            {#W12.183-3} Here RG I's α₀ and α₁ are CRE's thresholds α̃_{0,k} = ĝ_kC₀(log ĝ_k^{−2})^{q₀} and α̃_{1,k} = λ_Rα̃_{0,k} (CRE (2.28), p.259 l.45–50, at ĝ_k in the tube, Cauchy #CP.13); none of them is PBG's α₀ or α₁, and the C₀, C₁ of this paragraph are CRE's, not the Cauchy note's.
            {#W12.183-4} CRE applies RG I at the thresholds (2.28), with q₀, q₁ integers greater than 1 and C₀, C₁ "sufficiently large positive numbers" (p.259 l.50), and Bałaban presents the resulting bounds as proved.
            {#W12.183-5} The choice here is within (2.28): q₁ = q₀, an integer greater than max(1, p₀ + 3r), C₀ ≥ λ_QC₀^{low}, and C₁ = λ_RC₀ ≥ λ_QC₁^{low}, with λ_Q the LF note's factor (its #4.460) and C₀^{low}, C₁^{low} Bałaban's lower bounds ("sufficiently large", p.259 l.50); C₀ := λ_Qmax(C₀^{low}, C₁^{low}/λ_R) gives both.
            {#W12.183-6} A lower bound on C₁ proportional to C₀, as the Cauchy note's C₁ > 2B₃²O(1)MC₀ (its #C5.36-3), is met by λ_R alone (K_R ≥ 4B₃²O(1)) and is not part of C₁^{low}.
            {#W12.183-7} RG I's α₂ and α₃ are the Cauchy note's (its #C5.36-11, #C5.37-4, and #C5.37-18): α₂ := c₂α̃_{0,k} and α₃ := β_IL^{−2}α̃_{0,k}/(2B₃⁺C_{Q*}), with β_I RG I's class parameter β and C_{Q*} the Cauchy note's (its #C5.6-5), the factor 1/C_{Q*} keeping the B′-part of Lemma 4's output current below the reduced current threshold of its norm class (its #C5.28-17, #C5.28-19, and #C5.37-19).
            {#W12.183-8} These are the thresholds of the terms of index k.
            {#W12.183-9} A term of index j < k has CRE's α_{i,j} (CRE p.259 l.41–47), and the step-k quantities compared with them carry α̃_{i,k}/α̃_{i,j} ≤ (1 + β₀)²(k − j)^{1/2} (CRE (2.6), as in the Cauchy note's #C5.36-1).
            {#W12.183-10} CRE's bounds for these terms are Bałaban's statements at the thresholds (2.28), and the choice here lies within (2.28), so they apply as presented.
            {#W12.183-11} RG I's displays carry the factors L^{j−k} that pay the ratio (L^jη in (3.17), p.273 l.25; L^{j−1}η in (3.37), p.277 l.49; η replaced by L^{−n} in CRE, p.276 l.6–12).
            {#W12.183-12} Where a display drops the factor before the comparison, as (3.51) replaces (L^{j−1}η)² by L^{−2} (p.280 l.10–11), the comparison holds with the factor kept: at η = L^{−k}, α̃_{0,k}(L^{j−k−1})² ≤ (1 + β₀)²(k − j)^{1/2}L^{2(j−k)}L^{−2}α̃_{0,j} ≤ L^{−2}α̃_{0,j}, since (k − j)^{1/2} ≤ L^{k−j} and (1 + β₀)² ≤ L ≤ L^{k−j} for k > j.
            {#W12.183-13} The items below are written at the index k.
            - {#W12.184} α₂ = c₂α₀ is a radius of (3.14).
              {#W12.184-1} RG I takes (3.13) on U^c_j(X, ½α₀, ½α₁, α₀) and needs its arguments in the term's domain U^c_j(X, α₀, α₁, γ₀), γ₀ = α₀ (p.263 l.2–3), whose current bound is |𝐉| < γ₀ (p.262 l.37).
              {#W12.184-2} The 𝐉 entry of (3.13) is (L^{j−1}η)³𝐉 plus terms that vanish at 𝐀 = 0 (p.272 l.27–36), and (L^{j−1}η)³ ≤ L^{−3}, so the rooms are ½α₀, ½α₁, and (1 − L^{−3})α₀, all proportional to α₀ since α₁ = λ_Rα₀ ≥ α₀.
              {#W12.184-3} So c₂ depends at most on d, L, and B₃ (the Cauchy note's #C5.36-11, and #C5.36-13 for the room in (iv) through Proposition 9).
            - {#W12.185} α₃ satisfies RG I's two conditions: B₃α₃ ≤ B₃⁺α₃ = ½β_IL^{−2}α̃_{0,k}/C_{Q*} < ½α̃_{1,k} (p.280 l.6), since β_IL^{−2} ≤ 1 < λ_R (stage 2) and C_{Q*} ≥ 1, and 2B₃α₃ ≤ 2B₃⁺α₃ = β_IL^{−2}α̃_{0,k}/C_{Q*} ≤ β_IL^{−2}α̃_{0,k} (p.280 l.16), with B₃⁺ of the Cauchy note's #C5.37-18.
            - {#W12.186} "α₂ sufficiently small" (p.279 l.47).
              {#W12.186-1} RG I proves (3.36) for |B′| < α₃ (p.279 l.48–49) and applies it at B′ = τQ′, with |Q′| < O(1)α₂L^jη by (3.49) (p.279 l.44) and L^jη ≤ 1.
              {#W12.186-2} This needs O(1)α₂ ≤ α₃, that is c₂ ≤ c_* := β_IL^{−2}/(2B₃⁺C_{Q*}O(1)) with the absolute O(1) of (3.49), a homogeneous condition at stage 3′ (#W8.20-1) that does not involve γ.
            - {#W12.187} The class (3.31) and (3.14) contain the field: "for ε₁ sufficiently small" (p.276 l.42) and "ε₁ is so small that 𝐇_j(B(t)) satisfies (3.14) with 1/3α₂" (p.273 l.13).
              {#W12.187-1} Here RG I's ε₁ is the restriction |B′(b)| < ε₁ on the fluctuation field (p.266 l.46), which in CRE is O(ε_k): CRE's restriction 2δ_k, δ_k = (A₁/A₀)ε_k (CRE (3.3), p.265 l.26–39; ε_k of (2.4), p.255 l.31–34), gives |A′_k| < O(1)ε_k (p.267 l.27–28), and CRE speaks of "O(ε_k) arising from the bound of the fluctuation field" (p.277 l.9).
              {#W12.187-2} So the ratio is O(1)ε_k/α₂ = O(1)(A₀/(c₂C₀))(log ĝ_k^{−2})^{p₀−q₀}, small for γ small by the LF note's choice q₀ > p₀ + 3r (LF #4.420-1.1), after c₂ and C₀ are fixed.
            - {#W12.188} The term O(1)α₂ of p.285 l.17, the same form behind (4.18) (p.285 l.23–25, "by similar considerations as in the proof of (4.17)"), and |B| < α₁L^jη (p.280 l.44): O(1)(α₂ + B₃O(1)LMα₀) ≤ O(1)(1 + B₃O(1))LMα₀ < (K_RLM + 1)α₀ = α₁ under c₂ ≤ 1, LM ≥ 1, and K_R ≥ O(1)(1 + B₃O(1)), with LM in place of M as at a finer layer and a fortiori with M. RG I's B₃²O(1)Mα₀ < ½α₁ (p.277 l.54), with LM in place of M, reads B₃²O(1)LM < ½λ_R, which K_R ≥ 4B₃²O(1) gives.
            - {#W12.189} The factors α₂^{−1}ε₁. RG I's (3.17) carries 6α₂^{−1}L^jηB₀B₃|ζ_□𝐇_k(B′)| with |𝐇_k(B′)| = O(ε₁) (p.273 l.25–26), and p.280 l.49 reads "this differentiation yields a factor O(1)α₂^{−1}ε₁, and taking ε₁ sufficiently small we can get the required constant". Here O(1)α₂^{−1}ε_k = O(1)(A₀/(c₂C₀))(log ĝ_k^{−2})^{p₀−q₀}, small for γ small as in #W12.187-2.
            - {#W12.190} The factor (2n²B₃/α₂)^n of (4.5) (p.282 l.13) multiplies |ζ̃_□B|^m|(1 − ζ̃_□)B|^{n−m} with |B| < α₁L^jη, so it is at most (2n²B₃λ_R/c₂)^n(L^jη)^n, paid by the factor e^{−δ₀M(L^jη)^{−1}} of p.282 l.18 as in RG I, with λ_R/c₂ in place of α₁/α₂.
            - {#W12.191} The ratios α₁/α₂ = λ_R/c₂ in (8B₃α₁/α₂)⁴ (p.286 l.12–20) and α₁/α₃ = 2B₃⁺C_{Q*}λ_RL²/β_I in E₀α₃^{−5}|B|⁵ ≤ E₀(α₁/α₃)⁵(L^jη)⁵ of (3.54) (p.280 l.39–44) are constants of M, K_R, d, L, B₃, B₃⁺, c₂, and β_I, uniform in k.
              {#W12.191-1} RG I recovers E₀ through the factor O(1)α₂^{−1}ε₁ of p.280 l.47–49, so they enter only the γ-small condition of the previous items.
            - {#W12.192} The LF note's other restrictions on C₀ and C₁ are lower bounds, upper bounds that hold for γ small, and homogeneous relations (*Bałaban's Statements at the Reduced Thresholds*).
              {#W12.192-1} So C₀ := λ_Qmax(C₀^{low}, C₁^{low}/λ_R) and C₁ := λ_RC₀ satisfy all of them, and q₁ = q₀ is within the LF note's choice q₁ ≥ q₀.
          - {#W12.193} No loop through M.
            {#W12.193-1} CRE's C₁ = λ_RC₀ of (2.28) depends on M, so the choice is consistent only if no lower bound on M involves CRE's C₀ or C₁.
            {#W12.193-2} In CRE they occur in (2.28) (p.259 l.47–50), and C₁ also in (3.43)'s A-radius, which no note uses (table #T11.12-2, #T11.12-2-1), so it enters no lower bound on M.
            {#W12.193-3} VAR's absolute C₁ of (14), which enters B₅ = 6B₁B₃C₁ ((173)), RG II's absolute C₁ (p.6 l.54–57), and 10.5's C₁^{(1)} are other constants, not changed by the sixth choice.
            {#W12.193-4} The conditions on M in RG I, RG II, CRE, LFR I, and LFR II are the following, and none of them involves CRE's C₀ or C₁:
            - {#W12.194} RG I's M ≥ M(κ), with γ, ε₀, ε₁, α₀, and α₁ chosen after κ and M (Theorem 3, p.264 l.38–39);
            - {#W12.195} RG II's δ₀M ≥ κ (p.21 l.36), δ₁M ≥ κ₁ (p.5 l.15), and e^{−δ₀M/3}e^{16κ₁} < 1 (p.16 l.7), with κ₁ fixed by lower bounds in κ, δ, and L (*(D2)* above);
            - {#W12.196} CRE's "M = L^m is sufficiently large" (p.245 l.34), and the conditions on MR₁ and M₂R₁ (p.250 l.47–48, p.251 l.39–40), which compare O(1)B₃e^{−δMR₁}ε₁ with δ₀ = (A₁/A₀)ε₀ (p.247 l.50) and hold for M fixed and γ small because R₁ ≥ (log g₁^{−2})^r tends to infinity (p.246 l.24–25); they involve A₀/A₁, not C₀ or C₁;
            - {#W12.197} LFR I's δ(M/M₁) ≥ 2 (p.186 l.35) and the smallness of p.200 l.14–21, which makes O(1)B₃B₅M⁵exp(−δ dist(p, Λ)) of (1.98) small (p.200 l.5–8); it involves B₃B₅M⁵, with VAR's absolute C₁ inside B₅, and not CRE's C₀ or C₁;
            - {#W12.198} §8's list, whose constants in the conditions on M are those of d, L, κ₁, ρ, δ₀, δ₁, δ_g, M₁, CRE's K, R₁, N_D, C_ι, B₃, and K_R; (D2) is a lower bound on M, since C_s and λ_R are polynomial in M.
            {#W12.199} RG I's relations between M and the α's, B₃²O(1)Mα₀ < ½α₁ (p.277 l.54) and p.285 l.17, are what λ_R satisfies after M; they bound no M from below.
            {#W12.199-1} The LF note's λ_Q and C_mem contain no M. So the constants are fixed in the order L, κ, κ₁, M, then CRE's C₀ and C₁ := λ_RC₀ with q₁ = q₀, and γ last, and the sixth choice closes no loop M → C₁ → M.
          {#W12.200} This is the sixth choice of §12.
          {#W12.201} The boundary-layer data are those of (1.62) with 𝐇_{𝐁₁}(X_s)(s) and u′ (*The boundary-layer data of (1.62).*), and move with s by the size of 𝐇_{𝐁₁}(X_s)(s) on the boundary layers, as in Bałaban's representation.
          {#W12.201-1} So the terms satisfy LFR II's analyticity and the bounds (1.66) on the class, at real and complex points, with constants changed by factors O(1)M, under (D1) and (D2) with c = ½.
          {#W12.201-2} The margin is that of Bałaban's statements at the constants 2C₀ and 2C₁.
          {#W12.201-3} The LF note's *Bałaban's Statements at the Reduced Thresholds* derives his statements at the thresholds α_{i,j}/μ from two facts: the construction does not involve C₀ and C₁, and each restriction on them is a lower bound, an upper bound that holds for γ small, or a homogeneous relation.
          {#W12.201-4} At μ = ½ the lower bounds hold a fortiori and the upper bounds hold for γ small, so the same argument gives his statements at 2C₀ and 2C₁, with the extensions at the larger thresholds restricting to his.
          {#W12.201-5} So, for 𝐔 in the class at C₀ and C₁, Bałaban's U^0_k(𝐔) lies in the space of (1.65) at C₀ and C₁ (his (1.65)).
          {#W12.201-6} The X_s representation moves its entries by at most half of their room there, on the boundary layers and on Y₁, Λ^∼ included.
          {#W12.201-7} So the moved configuration lies in the space of (1.65) at 2C₀ and 2C₁, on which the terms are analytic with Bałaban's bounds (1.66) at these constants.
    {#W12.202} With *The boundary-layer data of (1.62).*, which places every boundary layer at a distance ≥ ½Ma_k from Z″_k, the strip bound of *The strip.* holds for the terms of the X_s representation, in both runs.
  - {#W12.203} *The run difference of the gauge change.* In each run, h is built from that run's U_{k,Λ}, with run B's pair U^B := ι(V₀), V₀ := U^A_{k,Λ} (*The background pairs.* above).
    {#W12.203-1} At a site x of run A, both runs take the transport along the same straight segments of the fine axial contour, run A over its bonds of the spacing ε and run B over its sub-bonds of the spacing ε/L.
    {#W12.203-2} Since MU^B = V₀ exactly (the LF note's (i)), V₀(b) is the one-step average of U^B over the paths across b.
    {#W12.203-3} Each such path differs from the straight one by a flux through an area ≤ dε², so |log(V₀(b)^{−1}U^B(Γ_b))| ≤ O(1)dε²|F(U^B)|.
    {#W12.203-4} The bi-invariant distance of products adds these, and the contour has at most O(1)dMa_k/ε bonds, since Λ lies in a cube of the size 100M at the scale k (LFR I p.192 l.47). 10.5 gives |F(U^B)| ≤ O(1)Mα₀a_k^{−2} at the global layer k of the points of Λ (10.5, the curvature at U^B).
    {#W12.203-5} This gives
    {#W12.204} |h^B(x)h^A(x)^{−1} − 1| ≤ O(1)d²M²α₀(ε/a_k)
    {#W12.205} at every data point x of run A in Z″_k, at real 𝐔.
    {#W12.205-1} Under the bi-invariant distance, d(u′^B(h̃^B)^{−1}, u′^A(h̃^A)^{−1}) ≤ d(u′^B, u′^A) + d(h̃^B, h̃^A).
    {#W12.205-2} So the run difference of u_s is that of u′, covered by *The gauge transformations.* for the representation at X_s, plus this bound.
    {#W12.205-3} The data X_s depend on h as well: X_s^X = −(1/i)log(((h^X_x)^{−1}h^X_y)^{−1}M^·(U^X_{k,Λ})(b)) on a bond b = (x, y) of Z″_k.
    {#W12.205-4} So X_s^B and X_s^A differ, besides the data difference that (W-δ) compares, by the conjugation with h^B(h^A)^{−1} at the two endpoints, so by ΔX_s ≤ O(1)d²M²α₀(ε/a_k) at real 𝐔, with 10.5's curvature bound at U^B as above.
    {#W12.206} At complex 𝐔 run B's background is the one-step lift ι(V₀(𝐔)). h^B and X_s^B depend on it only through its orbit under the gauge transformations that are 1 at the points of the ε-lattice, since transports between these points and the data are invariant under them.
    {#W12.206-1} So neither the gauge of run B's representative nor run B's class conditions at the thresholds α̃ enters here; the LF note's lift items at complex points (*The lift condition at complex points.*) concern these. ι's problem is VAR's at one step (the LF note's *The one-step problem.*).
    - {#W12.207} The complex lift.
      {#W12.207-1} Let V_r := U^r, the real minimiser of *The absolute bound at complex points.* Its plaquettes at the spacing ε are < ε₁^ι := O(1)B₃B₅M⁵α̃_{0,k}(ε/a_k)², so VAR Theorem 1 at one step gives the real lift ι(V_r), with |F(ι(V_r))| ≤ O(1)B₃Mε₁^ιε^{−2} (VAR (9)–(10), as the LF note's *The one-step problem.* uses them).
      {#W12.207-2} V₀(𝐔) = (exp(iη𝐇_c)U^r)^{u^{−1}}, so its ε-bond data deviate from those of V_r, after the gauge factor u, by B(𝐔) with |B(𝐔)| ≤ O(1)(ε/a_k)C_HC_Ŷ(α̃_{0,k} + α̃_{1,k}).
      {#W12.207-3} VAR Proposition 9 (p.309 l.8–14) states the solution map ℋ of (179)–(180) analytic in B, for G^c-valued small V′, and in the external configuration on PBG's class, with (190); p.309 l.1–3 extends its operators "to arbitrary, regular configurations U".
      {#W12.207-4} So VAR's representation about the minimiser ι(V_r) gives ι(V₀(𝐔)) = (exp(i(ε/L)𝐇^ι)ι(V_r))^{ũ^{−1}}, 𝐇^ι := ℋ(B(𝐔)), with |𝐇^ι|_{(−1)} ≤ C_H|B(𝐔)| and ũ the extension of u given by gauge covariance, an identity of analytic functions that holds at real 𝐔.
      {#W12.207-5} At real 𝐔 this is the real lift, so its orbit is the holomorphic extension of the real one, and MU^B = V₀ holds at complex 𝐔 too.
    - {#W12.208} The curvature.
      {#W12.208-1} VAR Theorem 1 is printed for G-valued data, and the one-step bound |𝐇^ι|_{(−1)} ≤ C_H|B(𝐔)| at the spacing ε controls ∇𝐇^ι only up to C_H|B|ε^{−2}, so the curvature is bounded through the smoothness of B.
      {#W12.208-3} The operators are those of the real background ι(V_r), and only the data are complex.
      - {#W12.209} The data.
        {#W12.209-1} The gauge factor u of V₀(𝐔) acts at ε-sites (CMP 98 (106)), so the orbit invariance above does not remove it.
        {#W12.209-2} By the gauge covariance of the lift (VAR (181)), ι(V^{u^{−1}}) = ι(V)^{ũ^{−1}}, so F(ι(V₀(𝐔))) is F(ι(exp(iε𝐇_c)U^r)) conjugated by ũ, whose Ad costs at most a factor 2 for γ small (*The bound.*).
        {#W12.209-3} Hence u can be dropped: V₀(𝐔) = exp(iε𝐇_c)U^r on the ε-bonds, and B(b) = ε𝐇_c(b). 𝐇_c is bounded in VAR's layer norm, which reads a(x)|𝐇_c(x)| and a(x)²|∇𝐇_c(x)|, by the bound C_HC_Ŷ(α̃_{0,k} + α̃_{1,k}) that gives |B(𝐔)|.
        {#W12.209-4} So |𝐇_c| ≤ C_HC_Ŷα̃a_k^{−1} and |∇𝐇_c| ≤ C_HC_Ŷα̃a_k^{−2} on Λ, and ε²|∇𝐇_c| ≤ C_HC_Ŷα̃ at every point, with α̃ := α̃_{0,k} + α̃_{1,k} and ∇ the covariant difference at U^r.
      - {#W12.210} The interpolant.
        {#W12.210-1} Let A_e be the field on the fine bonds of the spacing ε/L that takes, on a fine bond b′, the value of 𝐇_c at the ε-bond parallel to b′ and nearest to it, transported to b′ by ι(V_r), corrected on the fine bonds of each ε-bond b by a local right inverse of Q so that QA_e = 𝐇_c exactly, Q the one-step averaging operator linearised at ι(V_r).
        {#W12.210-2} The correction is O(1)ε|∇𝐇_c|, the oscillation of 𝐇_c over the block.
        {#W12.210-3} Neighbouring fine bonds carry values of 𝐇_c at the same or neighbouring ε-bonds, so the fine differences of A_e are ≤ O(1)ε|∇𝐇_c|, and its fine curl DA_e and divergence D*A_e are ≤ O(1)L|∇𝐇_c|, the differences divided by ε/L.
        {#W12.210-4} Also |A_e| ≤ O(1)|𝐇_c|.
      - {#W12.211} The linear part.
        {#W12.211-1} The one-step H₁ is PBG's constrained solution operator H₁B = G₁Q*(QG₁Q*)^{−1}B (PBG (3.129)), the operator of §§10–11, with G₁ defined by the quadratic form (3.128): G₁^{−1} = K + aQ*Q, where K collects the terms ⟨A, Δ_πA⟩ − 2⟨HC_π^{(2)}(A), J⟩ + ‖RD*A‖² of (3.128).
        {#W12.211-2} Since H₁QG₁Q* = G₁Q*(QG₁Q*)^{−1}QG₁Q* = G₁Q*, the term aQ*Q of G₁^{−1} drops from (I − H₁Q)G₁G₁^{−1}, and
        {#W12.212} H₁QA_e = A_e − G₁KA_e + H₁QG₁KA_e,
        {#W12.213} an identity of linear operators.
        {#W12.213-1} K is a sum of terms D*f and Dg: Δ_π = (I − DG′RD*)*Δ(I − DG′RD*) by (3.128), Δ is D*D up to terms with a factor of F(ι(V_r)), the projection term DG′RD* is bounded by (3.42) for G′ (|G′∇*λ| ≤ B₀L^jη) and the bound of R (PBG Theorem 3.2 and (3.48)), and the J-term carries the background current of VAR (10).
        {#W12.213-2} So KA_e = D*f + Dg with |f|, |g| ≤ O(1)(1 + B₀)²L|∇𝐇_c| plus terms with a factor F(ι(V_r)) or J, which are smaller.
        {#W12.213-3} PBG Theorem 3.12 gives G₁ the bounds of Theorem 3.3, so (3.42) at the spacing L^jη = ε of the one-step problem: |(∇G₁J′)(x)| and |(G₁∇*λ)(x)| ≤ B₀εe^{−δ₀d(y,y′)}|·| for sources supported in Δ(y′).
        {#W12.213-4} A source D*f or Dg costs at most O(1)(L/ε) times the sup of f or g on Δ(y′), and Σ_{y′}e^{−δ₀d(y,y′)} ≤ O(1)δ₀^{−d}.
        {#W12.213-5} So |∇G₁KA_e(x)| ≤ O(1)LB₀(1 + B₀)²δ₀^{−d} times a weighted sup of L|∇𝐇_c| with the weights e^{−δ₀d(y,y′)}.
        {#W12.213-6} For the third term, |G₁KA_e| ≤ O(1)εLB₀(1 + B₀)²δ₀^{−d} times the same sup, Q is an average, and (3.133) for H₁ (by (3.129) with (3.132) for G₁, p.423 l.25–31) gives |∇H₁b| ≤ O(1)ε^{−1}δ₁^{−d} times a sup of b weighted by e^{−½δ₁d}, so |∇H₁QG₁KA_e(x)| obeys the same bound times O(1)δ₁^{−d}.
        {#W12.213-7} Let C_G := O(1)LB₀(1 + B₀)²δ₀^{−d}(1 + δ₁^{−d}).
        {#W12.213-8} The data of the ε-bonds at a distance ≤ ½Ma_k from the point x read lie at a distance ≥ ½Ma_k from Λ^c, with the gain a_k^{−2} (the points read lie in Z″_k, at a distance ≥ Ma_k from Λ^c).
        {#W12.213-9} The others carry |∇𝐇_c| ≤ C_HC_Ŷα̃ε^{−2} = C_HC_Ŷα̃a_k^{−2}L^{2k}, with the weight at most e^{−½min(δ₀, δ₁)d}.
        {#W12.213-10} Half of that weight sums over these bonds to O(1)min(δ₀, δ₁)^{−d}, which C_G absorbs, and the other half is at most e^{−⅛min(δ₀, δ₁)ML^k} at the distance ≥ ½Ma_k = ½ML^kε.
        {#W12.213-11} L^{2k}e^{−⅛min(δ₀, δ₁)ML^k} ≤ 1 once min(δ₀, δ₁)M ≥ 8 log L, since the exponent is then ≥ L^k log L ≥ 2k log L, a lower bound on M. So |∇(H₁B/ε)(x)| ≤ O(1)C_GLC_HC_Ŷα̃a_k^{−2} at these points.
      - {#W12.214} The nonlinear part. 𝐇^ι solves VAR's fixed point at one step, (111)–(112) about the real minimiser ι(V_r): 𝐇^ι = A₁ + H₁B − HD(A₁ + H₁B), A₁ = −𝔊J − 𝔊(δV/δA′)(A′).
        {#W12.214-1} The current J of ι(V_r) obeys VAR (10), |J| ≤ O(1)B₃Mε₁^ιε^{−3} = O(1)B₃²B₅M⁶α̃a_k^{−2}ε^{−1}, and ∇𝔊 costs O(1)B₀ε by (3.42), which gives O(1)B₀B₃²B₅M⁶α̃a_k^{−2}.
        {#W12.214-2} The sources δV/δA′ and HD are at least quadratic in A′ (VAR (98), RG II (1.13)), with |A′|_{(−1)} ≤ O(1)C_H|B| ≤ O(1)C_H²C_Ŷα̃(ε/a_k) in the one-step norm, so their contribution to ∇𝐇^ι is ≤ O(1)B₀ε^{−2}(C_H²C_Ŷα̃ε/a_k)² ≤ O(1)B₀C_H⁴C_Ŷ²α̃²a_k^{−2}.
      - {#W12.215} The bound.
        {#W12.215-1} So |∇𝐇^ι| ≤ O(1)(C_GLC_HC_Ŷ + B₀B₃²B₅M⁶)α̃a_k^{−2}, with the fine difference ∇ at ι(V_r), and |𝐇^ι| ≤ O(1)(1 + C_G)C_HC_Ŷα̃a_k^{−1}.
        {#W12.215-2} The curvature of exp(i(ε/L)𝐇^ι)ι(V_r) at a fine plaquette is F(ι(V_r)) plus the covariant curl of 𝐇^ι plus terms ≤ O(1)(|𝐇^ι|² + (ε/L)|𝐇^ι||F(ι(V_r))|), and |F(ι(V_r))| ≤ O(1)B₃Mε₁^ιε^{−2} = O(1)B₃²B₅M⁶α̃a_k^{−2}.
        {#W12.215-3} The gauge factor ũ is G^c-valued with imaginary part of the size of 𝐇_c, so its Ad changes |F| by a factor ≤ 2 for γ small.
    {#W12.216} So |F(U^B)| ≤ C_F^Λ(α̃_{0,k} + α̃_{1,k})a_k^{−2} on Λ, C_F^Λ := O(1)(B₀B₃²B₅M⁶ + C_GLC_HC_Ŷ) (it depends on M and is distinct from the Cauchy note's C_F, which enters C_ι), at real and complex 𝐔, and |F(U_{k,Λ}(𝐔))| obeys the same bound by *The data X and X_s.* The imaginary parts of both runs' transports along the contours sum to ≤ O(1)dM(1 + C_G)C_HC_Ŷ(α̃_{0,k} + α̃_{1,k}), the quantity of §8's Ad condition for these transports (stage 6).
    {#W12.216-1} So their Ad is within a factor 2 of isometric, and the flux sum gives
      {#W12.217} |h^B(x)h^A(x)^{−1} − 1|, |ΔX_s| ≤ O(1)d²MC_F^Λ(α̃_{0,k} + α̃_{1,k})(ε/a_k)
      {#W12.218} at complex 𝐔, with the logarithms in their analytic chart for γ small.
      {#W12.218-1} This carries ε/a_k ≤ (ε/a_{m(ω)})^{γ_w} for every m(ω) ≤ k.
      {#W12.218-2} Through the Lipschitz bound of 𝐇_{𝐁₁} in its data (VAR Proposition 6), this is an absolute change of 𝐇_{𝐁₁} of the size of these bounds times the Lipschitz constant, a run-B term carrying ε/a_k.
      {#W12.218-3} Its part linear in the data is a sum of walk terms with the source ΔX_s, each at most these bounds times the walk bound (3.108) with a normalised source, as in *The strip.*, so it fits δ_w(ω).
      - {#W12.219} The nonlinear part.
        {#W12.219-1} It is bounded on the s-polydisc as §11 bounds the fixed point 𝐀₀ (*The fixed point 𝐀₀.*), without a per-walk decomposition.
        - {#W12.220} The identity.
          {#W12.220-1} Let D_h(s) := 𝐇^B_{𝐁₁}(X_s^B)(s) − 𝐇^B_{𝐁₁}(X̂_s)(s), both run B's function, with X̂_s run B's data with h^A in place of h^B at run A's data points, and X̂_s := X_s^B at run B's extra finest data bonds of 𝐁₁'s collar strip, where h^A does not exist (so ΔX_s := 0 there; those terms are bounded run by run by *The strip.*, which holds for the X_s representation in each run with that run's own w).
          {#W12.220-2} VAR's (111) and (112) (p.294) read A₁ + 𝔊J + 𝔊(δV/δA′)(A₁ + H₁B) = 0 and 𝐇 = A₁ + H₁B − HD(A₁ + H₁B), and the data B enter only through A′ = A₁ + H₁B.
          {#W12.220-3} So D_h(s) = H₁(s)ΔB + [N(s)(A′^B) − N(s)(Â′)] − [H(s)D(A′^B) − H(s)D(Â′)], with N(s) := −𝔊(s)(δV/δA′)(·), V that of VAR (80) with its current and D terms, and ΔB the data difference ΔX_s in VAR's normalisation.
          {#W12.220-4} The term 𝔊J is the same in both evaluations (the same background, s, and 𝔊(s)) and cancels.
        - {#W12.221} The contraction.
          {#W12.221-1} N is Lipschitz in A′ with the constant κ_V ≤ ½ of *The fixed point 𝐀₀.*, in the max norm max(|·|_{(−1)}, |∇·|_{(−2)}) of run B, at every s with |s(Δ)| ≤ e^{κ₁}; RG II's bound for the decoupled operators carries the factor e^{16κ₁}, which κ_V carries as there.
          {#W12.221-2} HD is at least quadratic, with Lipschitz constant O(1)B₀e^{16κ₁}C₂ε₂ as in RG II (1.13).
          {#W12.221-3} So |D_h(s)| ≤ (2 + O(ε))|H₁(s)ΔB| ≤ O(1)B₀e^{16κ₁}|ΔB| on the whole polydisc in these two entries, with |ΔB| the bound of *The run difference of the gauge change.*: O(1)d²M²α₀(ε/a_k) at real 𝐔, and O(1)d²MC_F^Λ(α̃_{0,k} + α̃_{1,k})(ε/a_k) at complex 𝐔.
        - {#W12.222} The Hölder entry.
          {#W12.222-1} RG I's domain (3.31) (p.276) asks ‖·‖_{1,β} for 0 ≤ β ≤ β₀ < 1, so the Hölder entry is taken without exponent loss.
          {#W12.222-2} RG II bounds H₁(s) in all norms, so ‖H₁(s)ΔB‖_{1,β} ≤ O(1)B₀e^{16κ₁}|ΔB|.
          {#W12.222-3} The second bracket is H(s) applied to the difference of the quadratic D-terms, with the same bound in all norms times O(1)C₂ε₂ times the max-norm difference.
          {#W12.222-4} The first bracket is 𝔊(s) applied to the difference of the sources δV/δA′.
          {#W12.222-5} VAR Proposition 4 bounds the whole source, its divergence-form parts included, in the sup norm |·|_{(−3)} by the max norm ((98), p.293), and VAR (119)–(120) do the same for differences.
          {#W12.222-6} So the source difference has the sup ≤ O(1)ε₂|A′^B − Â′|_{max}, which the contraction bounds by O(1)|H₁(s)ΔB|. 𝔊(s) maps sup-bounded sources into the Hölder entry at every β < 1: PBG (3.43) (p.398 l.2–8), through Theorems 3.3 and 3.13 (p.399 l.18–19, p.426 l.29–31), which are stated at real configurations satisfying (3.35)–(3.36), and at the complex 𝐔 through PBG's extension of the operators to the domain (3.37) (p.399 l.31, p.402 l.56, p.406 l.10).
          {#W12.222-7} PBG states the analyticity and the bounds of Theorems 3.1–3.3 on (3.37); the Hölder bound of 𝔊 there is obtained by running its perturbation series (3.130) and (3.138) at the complex 𝐔 in the norms of (3.43), as Theorem 3.13 runs them at real 𝐔.
          {#W12.222-9} RG II prints "in all norms" for H(s(Y₀)) (p.5 l.16). For the decoupled 𝔊(s) the same argument applies: 𝔊's walk terms satisfy the bounds of all these norms with the walk decay, the decoupling multiplies each walk term by its s-factors, and the sum over the walks is bounded as for H(s), with the split of the decay of *The decoupled functions.* So ‖D_h(s)‖_{1,β} ≤ O(1)B₀e^{16κ₁}|ΔB| for 0 ≤ β ≤ β₀, with the same factor ε/a_k as the other two entries.
        - {#W12.223} The consumer.
          {#W12.223-1} Each localised term is a Cauchy integral in s on |s(Δ)| = e^{κ₁} (§3(d), RG II (1.23)), so it reads D_h only through this bound on the polydisc, as it reads Δ₀.
          {#W12.223-2} The factor ε/a_k is ≤ (ε/a_{m(Y)})^{γ_w} for every m(Y) ≤ k, so the bound fits the weight of every term that reads it.
          {#W12.223-3} For 𝐇_{𝐁₁}, a background function, the relevant radius is the class radius, not the t_□ rescaling of RG II (1.23), and at the class radius the absolute bound suffices.
          {#W12.223-4} In RG II (1.23) t_□ multiplies the fluctuation function 𝐇_k(B′). 𝐇_{𝐁₁} = 𝐇_{𝐁₁}(−(1/i)log M^·(U_{k,Λ})⌈_{Z″_k}) carries no such parameter (LFR II p.374 l.4–8).
          {#W12.223-5} Bałaban expresses each term "as a function of the variables (𝐔, 𝐉)", with M^·(𝐔) and V_Λ^{(A)}(M^k(𝐔)) in place of the data, "an analytic function of (𝐔, J) with a large domain of analyticity" (p.374 l.37–42).
          {#W12.223-6} So the terms read 𝐇_{𝐁₁} at the 𝐔 of the class.
          {#W12.223-7} At run B's extra finest data bonds of 𝐁₁'s collar strip in Z″_k, h^B enters X_s^B with no run-A counterpart; there ΔX_s := 0, and the terms are bounded run by run by *The strip.*
- {#W12.224} *The source of (1.55).* Bałaban obtains (1.55) (LFR II p.371) from two facts.
  {#W12.224-1} First, 𝐆″_k(1 − θ)(1 − Q*_{𝐁₁}H*_{𝐁₁})Q*_{𝐁₁} = 0, since H_{𝐁₁} satisfies Q_{𝐁₁}H_{𝐁₁} = 1.
  {#W12.224-2} Second, "the above condition for J₁", which gives d := 𝐆″_k(1 − θ)(1 − Q*_{𝐁₁}H*_{𝐁₁})J₁ = 0.
  {#W12.224-3} Then θ₁ is inserted because 𝐆″_k kills Ran Q*_{𝐁″_k} and Q_{𝐁₁} = Q_{𝐁″_k} off the boundary layer (p.370 l.49 to p.371 l.2).
  {#W12.224-4} The first fact and the insertion of θ₁ are structural and hold in run B at any background.
  {#W12.224-5} So, at the pair, run B's 𝐆″^BJ^B_{1,2} differs from the right side of (1.55) in run B by d^B := 𝔊^B(1 − θ)(1 − Q^{B*}H^{B*})J^B, with 𝔊 := 𝐆″_k and H := H_{𝐁₁}, while d^A = 0 by Bałaban.
  {#W12.224-6} Run B's terms read only the right side, so d^B enters no term:
  - {#W12.248} Run B's terms contain no d^B.
    {#W12.248-1} Bałaban writes (1.55) before the localisation (LFR II p.371 l.2: "We use this fact to localize the considered expression"), localises 𝐇″_k (p.373 l.31–32), which by p.371 is its right side, and expresses every term of the expansion "as a function of the variables (𝐔, 𝐉)" (p.374 l.37–38).
    {#W12.248-2} So run B's terms are functions of RHS(1.55)_B, defined on run B's configurations alone and independent of the pair and of Y, and the term of the domain Y at ι_Yc^A is that function evaluated there; no term of V(Y) reads d^B.
  - {#W12.225} θ and θ₁.
    {#W12.225-1} Bałaban fixes them only by their support properties: θ = 1 on (Ω″^∼_{h+1})^c and on the boundary layer of the width 2M₁ at the scale h, changing to 0 near its inner boundary, and θ₁ = 1 where θ ≠ 0, 1 (p.371 l.2–4, l.21).
    {#W12.225-2} Bałaban also requires θ ∈ C₀^∞((Ω″_{h+1})^c).
    {#W12.225-3} These sets are physical sets at the scale h, the same in both runs, since the cut lies in the layer h at a shared scale.
    {#W12.225-4} Both runs are therefore taken with the same functions θ and θ₁ of physical space, smooth at the scale h; this is a choice, permitted because Bałaban fixes them only by these properties, and it leaves them no run difference.
  - {#W12.226} *The current difference.*
    {#W12.226-1} Run B's configuration at the pair is the lift ι_Y of run A's, run B's local minimiser with the data of its argument on Y^∼.
    {#W12.226-2} Write S_B(W) = S_A(MW) − b(W) with b the blocking artifact and ∇_Wb its fine gradient.
    {#W12.226-3} Differentiating, J^B = M*J^A − ∇_Wb at W = ι_Yc^A, with M* the transpose of the linearised one-step average, with no criticality needed.
    {#W12.226-4} Since Mι_YU = U on the coarse bonds of Y^∼, (dι_Y)*M* = 1 there, so (dι_Y)*J^B − J^A = −κ there, with κ := (dι_Y)*∇_Wb, the data gradient of the gauge-invariant function b∘ι_Y. The gauge term D_Bγ of dι_Y (10.5) adds nothing to κ, since the gauge invariance of b gives D_B*∇_Wb = 0.
    {#W12.226-5} The terms of V(Y) read the currents only at points of Y, which lie in Y^∼: V(Y, U_k) "depends on the new background field U_k restricted to Y" (LFR II p.377 l.7), and the walk kernels of a term with the domain Y are supported in Y (RG II p.4 l.18–24).
    {#W12.249-3} Here κ is not RG II's activity rate κ, and κ_ε, κ_η, and c_κ below are the blocking-artifact function of §11 and its constant. κ is §11's ∇b₁ = ℒ*∇_Wb with ℒ_ι in place of ℒ; the divergence form of §11, ∇b₁ = ∇_A*K + s with |K| ≤ O(1)osc_pX (#W11.86-3), uses only the covariance identity of the artifact and the sup, gradient, and Hölder bounds of the lift, which ℒ_ι has by *The bridge to ℒ_ι.*, so κ = ∇_A*K_ι + s_ι with |K_ι| ≤ O(1)(ε/a_j)^{β_o}C₀′ε₁a_j^{−2}, by the oscillation bound at ι_Y(U_{1,2}) (#W12.56–#W12.56-1).
    {#W12.249-4} The source part has three pieces: the background term of *The conversion to run A.* in (b), O(1)c_Gc_uMα₀a_j^{−1} times the coefficient field, at most O(1)c_Gc_uMα₀(ε/a_j)^{β_o}C₀′ε₁a_j^{−3}; the transport parts i[a_v, TF] of the covariance form; and its ρ-terms, these two at most O(1)(ε/a_j)²(C₀′ε₁)²a_j^{−3}, since |F| ≤ O(1)C₀′ε₁a_j^{−2} there (#W12.55-1).
    {#W12.249-5} The κ-terms of b, κ_ε(Φ_p) − Σwκ_η(F_{p′}), have first variations linear in the fine curls of v up to transport terms: the variation of a coarse holonomy of MW, converted to fine curls by the nonabelian Stokes formula, carries commutator terms with the coefficient O(ε|F|), which are of the kind of s_ι and are bounded with it.
    {#W12.249-6} The linear part enters K_ι in divergence form, with the coefficient dκ_ε.
    {#W12.249-7} By §11's bound |d^iκ_η| ≤ c_κη⁴|X|^{4−i} at η = ε and i = 1, |dκ_ε| ≤ c_κε⁴|F|³ ≤ O(1)c_κ(ε/a_j)⁴(C₀′ε₁)²|F|, so they add at most O(1)c_κ(C₀′ε₁)²(ε/a_j)C₀′ε₁a_j^{−2} to |K_ι|, within its bound once c_κ(C₀′ε₁)² ≤ 1, which holds for γ small (§8, stage 6).
    {#W12.249-8} So |s_ι| ≤ O(1)(c_Gc_uMα₀ + C₀′ε₁)(ε/a_j)^{β_o}C₀′ε₁a_j^{−3}; it enters 𝔊^B through the entry G of (3.42) with no derivative to move, and carries (ε/a_j)^{β_o} as K_ι does.
    {#W12.249-9} So κ enters the walk terms as §11's ∇b₁ does (#W11.86-12–#W11.86-14), with K_ι and s_ι in place of K and s and β_o in place of 1 − 2ε₀: (ε/a_j)^{β_o} ≤ (ε/a_{m(ω)})^{γ_w} (#W12.56-2), and the gradient entry's (ε/a_j)^{β_o−β′} is within the exponent γ_w − 2β′ that §8 uses (#W11.160-10).
    {#W12.249-20} At complex backgrounds κ is bounded as §11's current term is, through the ∇b₁ bound of that term.
    - {#W12.237} *The lift's R_ι.* R_ι is a parameter of the lift's one-step problem, separate from the R of the walk problems' sequences (R ≥ 12dL, and R_j ≥ (log g_j^{−2})^r of CRE (2.5)).
      {#W12.237-1} VAR's Sect. F construction, which places the minimiser in the space (8), takes a cube □ of size 2ML^jη with M = R₁M₁ and the cube □̃ with dist(□, □̃^c) = 2R₁M₁L^jη, and states □̃ ⊂ B^{j−1}(Λ_{j−1}) ∪ B^j(Λ_j) ⊂ Ω_{j−1} (VAR p.300 l.28–37).
      {#W12.237-2} Its source states the condition: "We assume that RM is bigger than R₁M₁, for example L^{−1}RM > 2dR₁M₁, thus we have □̃ ⊂ Ω_{k−1}" (REG p.098 l.18).
      {#W12.237-3} In VAR's units, with big blocks of size M₁, the ℓ¹ reach d(2M + 2R₁M₁)L^jη of □̃ beyond Ω_j must stay inside the layer j − 1, of width RM₁L^{j−1}η by VAR (1), so R > 2dL(M/M₁ + R₁) = 4dLR₁ at M = R₁M₁.
      {#W12.237-4} This is a condition on the ratio R/R₁, not on a product.
      {#W12.237-5} The other printed conditions are lower bounds on RM or R₁M₁ (PRT2 (2.59), p.233 l.40–42, and its layer sums, p.235 l.10; VAR p.304 l.2–5), or smallness conditions fixed after them (VAR p.304 l.24 on a₅).
      {#W12.237-6} The lift's layer is R_ι := 4dL + 1 blocks of CRE's M₁ wide, and VAR's product is R₁M₁ = M′ ≤ CRE's M₁ with VAR's block size M₁^{VAR} (#T2.7-1; BP_JOINS_BLOCK_SIZE #4.23), so the layer is R = R_ιM₁/M₁^{VAR} ≥ R_ιR₁ > 4dLR₁ blocks of M₁^{VAR} wide, with CRE's M₁ large for the product conditions (PRT2 pp.224 and 233–235, VAR pp.277, 279, and 300–304, REG p.098).
      {#W12.237-7} The two-layer cube conditions of PBG p.396 l.14–17 and PRT2 p.235 l.29–35 hold at one step for PBG's class.
      {#W12.237-8} PRT2's "We assume that either □̃ ⊂ B^j(Λ_j), or it intersects B^{j+1}(Λ_{j+1}) also" (p.235 l.35) is the case assumption of the bound (2.71) on C_□, with j the index of its scaling.
      {#W12.237-9} It holds with j the finest layer that □̃ meets, whenever □̃ meets at most two consecutive layers, which the layer widths ≥ LM₁ > 4M give.
      {#W12.237-10} A layer-1 cube next to the collar, whose □̃ reaches layer 0, takes j = 0.
      {#W12.237-11} It is not a condition on R. The choice R_ι = 4dL + 1 is the eighth choice of §12.
  - {#W12.250} The run difference of the source.
    {#W12.250-1} The two runs' sources 𝐆″(1 − θ)Q*θ₁H*_{𝐁₁}J₁ differ by the forms (c) for 𝔊 (§11, *The Sects. D–E form (111).*) and for H_{𝐁₁} (§11's form (c) for H, with the strips of *The strip.*); by the commutators of ℒ and ℒ* with θ and θ₁;
    {#W12.250-2} and by the current difference, which at the pair is (dι_Y)*J^B − J^A = −κ, bounded in divergence form (*The current difference.*). θ and θ₁ are smooth at the scale h, so the commutators are of relative size O(1)(ε/a_h) by the exponential tail of ℒ at the rate δ_Q (*The global lift.*).
    {#W12.250-3} H^{B*} reads the collar only through H_{𝐁₁}'s kernel, bounded by *The strip.* So the source difference carries 𝔡_H + O(1)(ε/a_h)^{β_o} times the bound of the source term, the power β_o of K_ι and s_ι (*The current difference.*), on the boundary layer of the scale h where θ₁ lives; this fits δ_w, since γ_w ≤ β_o (#W12.56-2).
- {#W12.251} The finest-scale strips of the sets 𝐁(Y_i) (CRE p.257 l.22–26).
  {#W12.251-1} Every boundary layer Y_i ∖ Y_i^0 has one, with no run-A counterpart.
  {#W12.251-2} These strips are bounded run by run below, as in *The strip.*
  - {#W12.252} The data.
    {#W12.252-1} In (1.61) and (1.62) (p.373), the data on the boundary layer (Y_i^0)^c ∩ Y_i are the averages of U = (exp iη𝐇U_b)^{u^{−1}}, with U_b the background and u the gauge factor.
    {#W12.252-2} The other data in Y_i are those of the other representation, and only data in Y_i enter.
    {#W12.252-3} By the covariance of the averages, these boundary-layer data are the averages of exp(iη𝐇)U_b, transformed by u at the data points of the layer.
    {#W12.252-4} Bałaban keeps u "because we use the two different representations for fields at the boundary of the boundary layer" (p.373 l.28–29).
    {#W12.252-5} Bonds of the layer and of Y_i^0 share endpoints at the inner boundary of the layer (CRE (2.2), p.255).
  - {#W12.253} The regauging.
    {#W12.253-1} Let h := u at the endpoints of the layer's data bonds, inner shared endpoints included, and h := 1 at the other endpoints in Y_i.
    {#W12.253-2} The representation at data^h is the representation at the data, gauge-transformed by an extension h̃ of h, up to a transformation that is 1 at the data points.
    {#W12.253-3} The effective action is gauge invariant (LFR II p.378 l.16–17; CRE p.274 l.41 for the terms of (3.38)), so every term 𝐄(X, ·) takes the same value at both, at real configurations.
    {#W12.253-4} At complex s, u(s) is G^c-valued.
    {#W12.253-5} Each term is analytic on its class, which is invariant under G-valued gauge transformations (LFR I p.191 l.32), and for (𝐔, 𝐉) in the class, g ↦ 𝐄(X, (𝐔, 𝐉)^g) − 𝐄(X, (𝐔, 𝐉)) is analytic on a connected neighbourhood of the G-valued g on which (𝐔, 𝐉)^g stays in the class.
    {#W12.253-6} It vanishes on the G-valued g, a totally real submanifold of maximal dimension of G^c, so it vanishes on the whole neighbourhood. u(s) lies in that neighbourhood, since its imaginary part is of the size of 𝐇(s), far inside the class radius.
    {#W12.253-7} So the invariance holds at complex s as well.
    {#W12.253-8} In data^h, the layer carries the averages of exp(iη𝐇)U_b.
    {#W12.253-9} Their deviation from U_b's averages at a bond of the physical spacing a_n is ≤ O(1)a_n sup|𝐇| ≤ O(1)(a_n/a_j)|𝐇|_{(−1)}, with j the global layer of ∂Y_i, the scale of the boundary layer (p.373 l.26–27).
    {#W12.253-10} Only the bonds of Y_i^0 at the shared inner endpoints change, by u(x), with no gain.
  - {#W12.254} The bound.
    {#W12.254-1} The strip has the width ≤ (d + 1)M₁a_2 at ∂Y_i.
    {#W12.254-2} The inner boundary of the layer, ∂Y_i^0 with Y_i^0 = Y_i^{∼−2} (CRE (2.14), p.257 l.14), is at a distance ≥ 2M₁a_j from ∂Y_i, by the definition of Y^{∼−2} as the set of points at a distance ≥ 2M₁a_j from Y^c at the scale j.
    {#W12.254-3} The layers 2, …, j − 1 of the layer's pieces lie between, so a walk that meets the strip (a cube, or the evaluation or source point, in it) reads the bonds changed by u(x) only through a cube of a layer ≥ j − 1, across at least j − 5 of them away from the reflex edges of Y_i, as in *The crossings.* of *The strip.* A walk that meets the strip only through an enlargement is aligned, by *The enlargement-only walks.*, applied to the pieces 𝐁_j(Y_i), which are built by the same rule.
    {#W12.254-4} Its crossings and bound then give, for each run's walk term ω that meets the strip, at most O(1)L¹¹(ε/a_j)(1 + |𝐇|_{(−1)}) times its bound at the rate ¼δ_min kept for the form (c) (*The strip.*).
    {#W12.254-5} The term 1 is the background's own current on the strip, relative to the problem of 𝐁(Y_i), with the factor (a_n/a_j)³ of VAR (10) at U_k and U_{k,Λ}, and of the derived band regularity (*The band regularity of U_{1,2}.*) at U_{1,2}.
    {#W12.254-6} A walk that meets the strip meets the global layer j, so m(ω) ≤ j, and this is within δ_w(ω) of §8 with C_w enlarged by O(1)(1 + C_ℒ)L¹¹.
  - {#W12.255} 𝐇_{𝐁₁} in its collar.
    {#W12.255-1} Where the boundary layer of Y_2 lies in 𝐁₁'s collar, the norm |·|_{(−1)} weights a point by the collar's spacing there, which gives no factor a_n/a_j.
    {#W12.255-2} There the gain of the field is that of *The sources.* in the X_s representation, |𝐇_{𝐁₁}|_g, with the factor (a_n/a_h), and h ≤ j.
  - {#W12.256} Scope.
    {#W12.256-1} This bounds the strips of the representations of 𝐇″_k, 𝐇_{𝐁₁}, and 𝐇_k in (1.61), (1.62), and the (1.63) of p.374, and the fine side of their gauge transformations there.
    {#W12.256-2} Away from the strips, *The gauge transformations.* compares u on the shared layers.
    {#W12.256-3} For 𝐇_{𝐁₁} the data of the strip of Y_2 are those of (1.57), with the representation of the collar.
{#W12.257} *The choices.* Eight choices are made: the (111) form for 𝐇_{𝐁₁}, the X_s representation, the same functions θ and θ₁, the extension h̃, the intersected local sequences {Ω′_m(□)} at ∂Ω and at the reflex edges, the constants q₁ = q₀ and C₁ = λ_RC₀ of CRE (2.28) (*Analyticity and bounds.*), the artifact exponent β_H ≥ γ_w (*The localised 𝔡_H.*), all made in both runs, and the lift's parameter R_ι = 4dL + 1 (#W12.237-6).

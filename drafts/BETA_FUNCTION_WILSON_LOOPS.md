# The Beta Function for the Wilson-Loop Analysis

{#BP.1} This file contains the coupling-flow results that the Wilson-loop renormalisation-group analysis uses, with their
{#BP.2} proofs.
{#BP.2-1} It is extracted from `D:\University\Oxford PostDoc\Balaban\ONE_LOOP_PROOFS.md`.
{#BP.2-2} The proofs use Bałaban's papers,
{#BP.3} cited by printed page and equation, with the printed text quoted where a step depends on its wording or pinned in a sidecar
{#BP.4} contract (`D:\University\Oxford PostDoc\Balaban\sidecar\BalabanSidecar\`), and arguments given here.
- {#BP.6} RG1 = CMP 109; RG2 = CMP 116; CRE = CMP 119; LFR1 = CMP 122 175–202; LFR2 = CMP 122 355–392;
- {#BP.7} PRT1 = CMP 95; PRT2 = CMP 96 223–250; CMP98 (also AVG) = CMP 98 17–51; REG = CMP 99 75–102; PBG = CMP 99 389–434;
  {#BP.8} UV3 = CMP 102 255–275; VAR = CMP 102 277–309.

{#BP.9} G is a compact simple group, d = 4, and L is an odd integer > 11 (RG1 p.251 l.14–15).
{#BP.9-1} §10 treats semisimple G: Proposition 10.2 reduces additive actions to
{#BP.10} the simple factors, Proposition 10.3 treats one bare coupling, and Proposition 10.4 treats factors that a symmetry permutes transitively.
{#BP.10-1} **Open items.** For semisimple G, RG1's construction on G with a coupling vector for non-additive actions without such a symmetry (§10, *What is OPEN*, #B10.88–#B10.93). For simple G there are none.
{#BP.10-2} §0's inputs 1, 2, 3, 5, and 6 are statements of Bałaban's papers given there without a complete proof, used as printed; §0 gives, at each input, the page and line of the passages that are not proved (for RG1's own proof of input 3, examples of them). Input 4 is derived in this file, and so is input 3's transfer to CRE's cutoffs δ_j with its changed constants and domains (#B0.37-3), except two changes derived in BP_RG2_COMPLEX_B.md (#B9.60–#B9.61) and BP_RG2_CUBE_COUNT.md (#B9.53–#B9.54), not yet through review.

## 0. The Result {#BS0}

{#B0.1} The coupling flow is RG1 (2.15), p.268, as in RG1 (0.20):

  {#B0.2} 1/g_k² = 1/g_{k+1}² + β_{k+1}(g_0, …, g_k),

{#B0.3} where β_{k+1}, RG1's β_{k+1}(g_k), is defined by RG1 (1.20)–(1.22), p.264, from the step term E^{(k+1)} of RG1 (1.6); (2.12) (p.268 l.6–16, l.21) builds E^{(k+1)} from g_k and the earlier steps' E_k, so β_{k+1} is written with the history (#B2.1-1). b_{k+1} is its value at
{#B0.4} zero coupling (Remark 2.3).
{#B0.4-1} The step terms are those of RG1's construction run with CRE's fluctuation cutoff
{#B0.5} δ_k := g_k(A₁/A₀)p₀(g_k), the cutoff of CRE (3.16) (p.268; δ_k is defined at p.265 l.39) and #T3.27's ϑ_k, with p₀(g) of #T10.2 and CRE's constants A₀ ≫ A₁ of #T3.27-0, on RG1's fixed domains (§0, *Input 3*).
{#B0.5-1} Let κ > 0 be defined by
{#B0.6} K = κ·tr (Lemma 1.1), and put c := (11/48π²)κ.
{#B0.6-1} Notation: Tr is the trace of a linear map (of matrices, on g^c, on fields and on step variables), and tr the normalised trace of the defining representation (#T10.18). Many letters carry several meanings, each fixed by its context, as in the sources; the table's §10 lists every symbol of this note that has more than one meaning, or that occurs in its earlier sections with another meaning, with where each meaning is used and the meanings it must not be confused with (#T10.1).
{#B0.6-3} §7's a is #T10.9's, and its R and 𝒩 are #T10.10's; RG1's U_k(V), J_k, (𝐔, 𝐉) and U_k(ε₀) are #T10.28-1's, #T10.28-1-0's and #T10.28-1-1's, with M^k of #T10.13-3 and #T10.13-3-1 and D^η_U of #T10.13-2; CRE's further parameters are #T10.28-2's; RG1's E₀ and RG2's B₀, C₁, C₂ and q are #T10.28-3's, α₂ is #T10.28-3-0's, M₁, α₄, γ₂ and α₆ are #T10.28-3-2's, C₁′ (RG2's C₁ of (1.20)) is #T10.28-3-1's, δ_{RG2} is #T10.28-3-1-1's, and κ₁ is #T10.56-2's. Any other symbol defined inside a proof (such as S, H or C) is local to that proof.

{#B0.14} **Theorem 0.1 (Coupling Flow).** There are constants γ > 0, C, C_rem and δ ∈ (0, 2c ln L), independent of k, of the history (#B2.1-1)
{#B0.15} and of the torus, with the following properties (RG1 (0.31), LFR2 p.386 l.38–40, CRE (2.6); proofs below).
1. {#B0.16} *Window* (Theorem 8.1).
   {#B0.16-1} For all 0 ≤ m ≤ n, |Σ_{j=m+1}^{n} b_j − 2c(n − m) ln L| ≤ C.
2. {#B0.17} *Matching* (Corollary 8.2, the matching of RG1 Theorem 2 for simple G).
   {#B0.17-1} Put γ′ := (γ^{−2} + C)^{−1/2}.
   {#B0.17-2} For every K and every
   {#B0.18} renormalised coupling g ∈ (0, γ′] there is a bare coupling g_0(ε, g), ε = L^{−K}, independent of the torus, whose
   {#B0.19} flow has g_K = g and g_k ∈ (0, γ] for 0 ≤ k ≤ K.
3. {#B0.20} *Logarithmic window* (Corollary 8.2). For 0 ≤ k ≤ K,
   {#B0.21} g^{−2} + (2c ln L − δ)(K − k) − C ≤ g_k^{−2} ≤ g^{−2} + (2c ln L + δ)(K − k) + C.
   {#B0.22} This is RG1 (0.31) with β = 2c − δ/ln L and β′ = 2c + δ/ln L, up to an additive constant.
4. {#B0.23} *Near-monotonicity* (Corollary 8.2). g_k^{−2} ≥ g_l^{−2} − C for k ≤ l. This gives the comparison of thresholds after LFR2 (1.86), p.386 l.38–40
   {#B0.24} (Remark 2.2), and for γ small the flow satisfies CRE (2.6) (Corollary 8.2).
5. {#B0.25} *Remainder.* With CRE's fluctuation cutoff δ_k (#B0.5),
   {#B0.26} |β_{k+1}(h) − b_{k+1}| ≤ C_rem g_k² for every history h with entries in (0, γ] (Proposition 2.9). So 1/g_{k+1}² = 1/g_k² − b_{k+1} + O(g_k²).

{#B0.27} Corollary 8.2 gives both δ = c ln L and δ = C_remγ²; Proposition 2.9(a) on 𝔖_γ holds on 𝔖_{γ̃} ⊂ 𝔖_γ for every γ̃ ≤ γ with the same C_rem, so the rate
{#B0.28} in item 3 tends to 2c ln L as γ → 0 (RG1 (0.31)).

{#B0.29} Theorem 0.1 uses the following inputs.
{#B0.29-1} §9 lists them with the other inputs taken from Bałaban.

{#B0.31} Inputs:
1. {#B0.32} VAR (189), stated in VAR without proof (VAR p.308 l.30, quoted at #B2.1.38) and proved in VAR's setting in balaban_proofs/BP_VAR_189.md (not yet through review), enters through Lemma 2.5 (sidecar node VAR_189) and, through input 3, wherever RG1 Theorem 3 is used (RG1 p.271 l.33).
2. {#B0.33} RG2's sketches for the terms of P^{(k)}, RG1's part of the exponent from the action and the measure (RG1 p.268 l.19–20), other than its example (1/g_k²)V(H₁B′), V the function (80) of VAR (RG2 p.10 l.5–6) ("it can be done in the same way for all terms in 𝐏^{(k)}", p.11 l.5) and for the term (I.3.21) of RG2 Lemma 1 ("expanded and analyzed in almost the same way as the last term in (I.3.34), so we do not repeat these considerations", p.9 l.28).
   {#B0.33-1} Both are parts of RG2 Lemmas 1–2, so they enter wherever input 3 uses these lemmas (#B0.37-2), and through it items 2–5; directly, in Proposition 2.6, step 2 (#B2.1.59, #B2.1.88-1), in Lemma 2.7, steps 1–2 (#B2.2.27), and in the complex-B form of these lemmas (#B9.60–#B9.61; balaban_proofs/BP_RG2_COMPLEX_B.md #BH.5-11, #BH.6-0 and #BH.6-5, not yet through review).
3. {#B0.34} The parts of RG1 Theorem 3 with RG2 that §§2.1–2.2 use (the bound RG1 (1.18), and the analyticity of the step terms
   {#B0.35} in (U, J) on RG1's fixed domains), run with CRE's fluctuation cutoffs δ_j (#B0.5), enter items 2–5:
   {#B0.36} through (P2) and (C) (the remark after Proposition 2.6) and through Proposition 2.9.
   {#B0.36-1} RG1 Theorem 3 is Bałaban's, proved in the rest of RG1 ("In the rest of the paper we will be proving this theorem", p.264 l.44) and in RG2 §§1–2 (completed RG2 p.22 l.4), with inputs 1, 2, 5, and 6, the unproved steps quoted in #B0.37-1, #B0.37-1a and #B0.37-1c, and steps RG1 §§3–4 argue by analogy with earlier ones, among them p.273 l.34 ("apply almost without a change"), p.274 l.32 and l.44–45, p.276 l.43, p.279 l.29, p.280 l.21 and l.46–47 ("we do not repeat them"), p.285 l.26, and p.286 l.23.
   {#B0.36-2} It is used as printed, with the changes that #B0.37-3 lists, and its transfer to the cutoffs δ_j is derived below (*Input 3*).
   {#B0.37-0} The chain is the renormalisation steps of RG1, RG2 and CRE, which average with RG1 (0.4) or (0.12) (RG1 pp.253–254, both "equally good", p.254 l.9; CRE p.243 l.24–25).
   {#B0.37-1} RG2's proof applies PBG at the chain's backgrounds: the walk expansion (1.6) of the chain's propagators with the bound (1.7), applied "as (3.108) [13]" (p.3 l.18; "This bound holds for all operator norms in formulations of theorems in [13]", l.23); the bound (1.11) on H(s(Y₀))X (p.5 l.5–16), after which "Similarly the other inequalities and statements of Sect. C [15] hold in this case", with Proposition 4 [15] (p.5 l.38–40); and the walk expansion of C^{(k)}(Z_0), "discussed in [13]" (p.13 l.19), which is PBG Theorem 3.15's by (3.185) (p.432 l.33–40).
   {#B0.37-1a} RG2 p.13 l.19–35 expands (C^{(k)})^{1/2}, which [13] does not cover, through (2.7) and the resolvent 𝒫(xI + 𝒫*Δ^{(k)}𝒫)^{−1}𝒫* (𝒫 is RG1's C, #T10.28-4; RG2 writes Δ^{(k)} as Δ_k, l.24), represented by (3.185) [13] with an added term and G̃_3(x) in place of G̃_2 (l.31–33); "The operator G̃_3(x) has the same properties as G̃_2" (l.34) is not proved there.
   {#B0.37-1b} For the chain's dressed average, balaban_proofs/BP_PBG_COMPLEX.md (#BX.1-5) proves the analyticity and the bound (3.187), with a rate ϱ > 0 for δ₀, of these resolvents, uniformly in x ∈ [0, γ₁], and convergent expansions with its own localisation cubes, not yet through review. The terms of those expansions are taken at the G-valued factor U of RG1's (i) (#BX.1-5b), so they do not give l.34 in the form RG2 §2 uses, with terms that are functions on the orbits [(𝐔, 𝐉)] (RG1 p.262 l.9–14; (1.19), p.263 l.34–39). RG2's localisation domains around Z_0 (l.15–18) are used as printed.
   {#B0.37-1c} The terms other than the last of (I.3.34) are "bounded similarly as in (1.24)" (p.8 l.30–34).
   {#B0.37-2} These, and the bounds RG2 §§1–2 build from them ((1.18)–(1.43), (2.14)–(2.41), Lemmas 1–3), enter at the chain's backgrounds wherever §2 cites RG2; §§3–8 do not cite RG2; §10 cites it in Proposition 10.4 for G as printed, and in Lemmas 10.14–10.16 for the family, with PBG's operators as (P-PBG) (#B9.29-3) and re-running RG2's arguments.
   {#B0.37-3} They enter as printed, or with the changed constants and domains that #B9.60–#B9.61, Lemmas 2.7–2.8, *Input 3*, Proposition 2.11, steps 3–4, and *The Step with Complex Multiples of the R-Terms* derive, and with RG2's cube count (1.28), (2.30) and p.9 l.23 replaced by #BK.1 of balaban_proofs/BP_RG2_CUBE_COUNT.md, not yet through review (#B2.1.49-1).
4. {#B0.38} The bounds of Proposition 7.1(c) (#B7.82, #B7.84) on the first- and second-order parts in B of (QGQ*)^{−1}(U) and on the
   {#B0.39} first-order part of H(U), at U = U^L, VAR's Landau-gauge form of U_k(e^{iB}), at which F_k is evaluated (#B7.47-1–#B7.47-3), for the operators of §7's Setting, built from the dressed average with the
   {#B0.40} variables (0.11) (#B9.40-3d), are derived in this file from PBG's operators at U = 1 (#B7.81-1–#B7.81-5, #B7.86-1–#B7.86-27, with Lemma 7.3, step 8), with VAR Proposition 9's bound (19) at V₀ = 1 (#B7.79-2, #B7.81-3; #B9.50, input 5).
   {#B0.40-1} Bałaban applies PBG's theorems to the chain's operators (§9, #B9.29-1–#B9.40-3e), without re-running PBG's proofs for RG1's average, and not to operators with this dressing, which he does not define; so his applications do not supply these bounds as printed. §10's Lemmas 10.11–10.16 use PBG for the chain's dressed average and at complex U as (P-PBG) (#B9.29-3–#B9.29-4), and Lemma 10.12 uses REG's results for the chain's average (#BFP.160-2); these are proved in balaban_proofs/BP_PBG_DRESSED.md, BP_PBG_COMPLEX.md and BP_REG_DRESSED.md, not yet through review.
   {#B0.41-1} Proposition 4.2, and through it 5.3, uses PBG only at U = 1: C^{(k)}(1) is bounded in #B4.147-1–#B4.147-9, and the U-derivatives at 1 of H, G′, and R are written out in #B4.196-1–#B4.197-8. The other uses of PBG are listed in §9 (#B9.29-1–#B9.31).
5. {#B0.42} VAR Theorem 1 uses REG's sketched Theorem 8 at one step, VAR p.297 l.9–13 (repeated at p.302 l.30), which balaban_proofs/BP_REG_DRESSED.md proves without it, not yet through review (#B9.41).
   {#B0.42-1} VAR Theorem 1 enters, through input 3, wherever RG1 Theorem 3 is used (VAR Thm 1 at RG1 p.260 l.23, VAR Prop. 9 at RG1 p.271 l.33), and it enters §§5 and 7 through the uniqueness of the minimal orbit (VAR Thm 1, VAR p.279 l.15, as RG1 (0.21)–(0.22), p.256, states it: Proposition 5.3, step 1, #B5.74–#B5.75, #B5.89–#B5.91; #B7.47-5), and §§2, 5, and 7 through the analyticity of U_k(V) (VAR Prop. 9; in §2, Lemma 2.5, step 1, and Proposition 2.12(b)).
   {#B0.43} RG1 states VAR's results for its own chain, whose averaging is RG1 (0.4) or (0.12) (#B0.37-0); their uses are listed in §9 (#B9.44–#B9.51-1).
6. {#B0.43-1} PBG (3.132), stated without proof on PBG p.422 l.15–19 and used as printed, with a proof for G-valued U of PBG's class on sequences with Ω₀ = T, not yet through review, in balaban_proofs/BP_PBG_3132.md, enters at U = 1 as the kernel bound on (QGQ*)^{−1}(1) (#B4.147-9, #B4.197-8, #B4.206–#B4.208, #B4.220, #B7.74–#B7.74-1, #B7.86-9) and through (3.133), which PBG p.422 derives from it with Theorem 3.3 for G (#B9.4–#B9.5, #B9.25–#B9.26).
   {#B0.43-2} Away from U = 1 it enters §§1–8 wherever inputs 1, 3, and 5 do (VAR p.291 l.36 and p.297 l.40, at each of VAR's backgrounds U₀, §G's included, #B9.29-2a; RG2 p.5 l.40, p.6 l.2, and p.13 l.19; #B9.29-2). In §10 it enters at U = 1, in Propositions 10.2–10.4 wherever inputs 1, 3 and 5 enter them (#B9.29-2), and in Lemmas 10.11–10.16 through (P-PBG) (#B9.29-3–#B9.29-3a-2, #B9.29-3d).

{#B0.44} *Scope.* CRE Theorem 1 (CRE p.262) takes the coupling inequalities "(I.0.33)" as its hypothesis: if the sequence {g_k}
{#B0.45} of the renormalisation group equations satisfies them, the densities ρ_k satisfy CRE's inductive assumptions.
{#B0.45-1} RG1 has
{#B0.46} no (0.33); its introduction ends at (0.32), and CRE p.246 l.15–17 takes γ₀^{−2} = γ^{−2} + β log ε^{−1} from the upper bound of "the inequality (0.33) [I]",
{#B0.47} which is RG1's printed (0.31), p.259.
{#B0.47-1} Item 3 has the form of (0.31).
{#B0.47-2} Item 1 is the input from which Lemma 2.1 derives items 2,
{#B0.48} 3, and 4; item 2 provides the flow on which items 3 and 4 hold; and item 4 gives the comparison after LFR2 (1.86).
{#B0.48-1} Theorem 0.1
{#B0.49} is stated for the coefficients β_j of the construction named before it.
{#B0.49-1} For semisimple G with an additive action,
{#B0.50} Proposition 10.2 gives the tube-construction form of it (the statements after the list of inputs) for each simple factor of
{#B0.51} the product construction on ∏_iρ_i(G), with one bare coupling per factor; for one bare coupling with fixed weights, Proposition 10.3 gives it for one factor of the largest rate c_i/w_i, which may depend on (K, g), at its share of the target, and for the factors of that rate unitarily conjugate to it, and weaker bounds for the others; Proposition 10.4 gives Theorem 0.1 itself, with one coupling, when a symmetry permutes the simple factors transitively, the action being additive or not; §10, *What is OPEN*, lists the rest.

{#B0.52} CRE's flow equation (2.24), p.259, uses its own coefficients β_j(g_{j−1}), which CRE (2.25), p.259, subtracts from its
{#B0.53} step terms (and p.279 for j = k+1).
{#B0.53-1} They differ from ours by the contribution of the R-terms (*Identification* and *The
{#B0.54} R-terms* below).
{#B0.54-1} CRE's coefficient β_{k+1}(g_k) is built from the whole-lattice term E^{(k+1)} (CRE (3.57), p.281;
{#B0.55} p.278), and g_{k+1} enters step k only through the localisation of the new density.
{#B0.55-1} CRE's printed construction is not known to be a
{#B0.56} continuous function of the history: its integer parameters (R_j, k₁, N₀, and the depth N) jump with the couplings, and its thresholds
{#B0.57} and domain radii move with them (*CRE's Construction as a Function of the History*, §2.2).
{#B0.57-1} The
{#B0.58} *tube construction* for a target (K, g) evaluates all of these parameters at couplings fixed by the target, and it
{#B0.59} places the threshold of the function χ′^{(j)} of LFR1 (1.55) on the unscaled field, |g_jB_j(b)| < δ′^T_j, #T3.40's δ′_j at ĝ_j (#B2.2.222), where LFR1
{#B0.60} prints the scaled variable (*LFR1 (1.55)*, before Lemma 2.10; Lemma 2.10).
{#B0.60-1} For it:
- {#B0.61} the R-terms shift β_{k+1} by at most C_Rg_k^{κ₀−4} relative to RG1's construction run with the tube cutoffs δ_j^T
  {#B0.62} (Proposition 2.11), on the histories of the tube H_k (#B2.2.159); Propositions 2.4 and 2.9 hold for the latter on H_k
  {#B0.63} (Lemma 2.10, step 7).
  {#B0.63-1} So on H_k the per-step bound (P2) of Remark 2.3 (#B2.28) holds with the tube's δ′ = C_ΛC₃γp₀(γ) + C_Rγ^{κ₀−4} (#B2.2.165) in place of
  {#B0.64} δ, and with it (W) for b = 2c ln L − δ′ and b′ = 2c ln L + δ′ (#B2.2.503–#B2.2.505), and item 5 holds with C_rem + C_Rγ^{κ₀−6} in place of C_rem (*Consequence*, after Proposition 2.11);
- {#B0.65} its β_{k+1} is continuous on H_k (Proposition 2.12), and item 2 holds (Proposition 2.13), with γ′ as in item 2; item 3
  {#B0.66} holds along the matched flow of Proposition 2.13 with δ′ in place of δ, and item 4 holds along it;
- {#B0.67} the bare coupling of item 2 is independent of the torus, because β_j^T, like CRE's β_j, is defined by RG1's
  {#B0.68} definition (I.1.22) (CRE p.282), that is, by the limit of the polarisation as T^{(j)} ↗ ℤ^d (RG1 (1.21), p.264),
  {#B0.69} computed from (2.26) for Λ_j = L^{−j}ℤ^d (CRE (3.63), p.282).
  {#B0.69-1} The limit exists, and is approached uniformly in the
  {#B0.70} history, by the localisation through the random-walk expansions (Proposition 2.12, step 5).
{#B0.71} These statements are for the tube construction, at every depth k < K of each target.
{#B0.71-1} They are not statements about CRE's
{#B0.72} printed construction (*What Is Proved for β_j*, after Proposition 2.13).
{#B0.72-1} They rest on the inputs that §9 lists for the
{#B0.73} tube construction (#B9.55–#B9.58), on inputs 1–3 through Propositions 2.4 and 2.9 with δ_j^T, on inputs 1 and 5 through Lemma 2.5 in Proposition 2.11, step 5, and in Proposition 2.12(b) (#B2.2.467-1, #B2.2.526-1; #B9.47-1–#B9.51), on input 6 wherever inputs 1, 3 and 5 enter (#B0.43-2), and,
{#B0.74} through Theorem 8.1 in Proposition 2.13, step 2 (#B2.2.830), on inputs 4 and 5 (#B0.42-1), on input 6 at U = 1 (#B0.43-1), and on §9's inputs for §§3–8 (#B9.2–#B9.15, #B9.44–#B9.51).

{#B0.80} *Input 3 (derived).* The estimates of §§2.1–2.2 use RG1 Theorem 3 with CRE's fluctuation cutoff
{#B0.81} δ_k (#B0.5) in place of the fixed cutoff ε₁ of RG1 (2.9), p.266, on RG1's fixed
{#B0.82} domains U^c_{k+1}(X, α₀, α₁) (#B2.1.31–#B2.1.35).
{#B0.82-2} The cutoff
{#B0.83} applies to the field-scale fluctuation g_kA_k, so its unit-scale form is δ_k/g_k = A₁(log g_k^{−2})^{p₀}
{#B0.84} (CRE p.267; the argument is #B9.62–#B9.62-2).
{#B0.84-1} CRE's ε_k = g_kp₀(g_k) (#T3.27) is the plaquette threshold,
{#B0.85} the analogue of RG1's ε₀ (CRE (3.2), p.265), and it is not the fluctuation cutoff.
{#B0.85-1} The proof of RG1 Theorem 3
{#B0.86} (RG1 §§2–3, RG2 §§1–2) uses the cutoff in four ways only:
- {#B0.87} *Upper bounds on ε₁.* These are listed at #B2.1.23–#B2.1.28; elsewhere (RG1 p.269, coefficients O(ε₁); RG2 p.8 l.24, p.9 l.50 and p.16 l.17) ε₁ enters only as a factor of a bound.
  {#B0.89-1} RG2's conditions on its auxiliary constant ε₃ (p.6 l.16–21) bound ε₃ above by constants independent of ε₁, once p.5's auxiliary ε₂ (l.23, not p.19's ε₂) is fixed, and RG2 applies them to |B′| < C₁′ε₁ (p.7 l.4 against p.6 l.41), that is with
  {#B0.90} ε₃ = C₁′ε₁ (inferred, not printed); so they are upper bounds on ε₁ of the same kind.
  {#B0.90-1} They hold with δ_k for γ small, because δ_k ≤ ε_k ≤ γp₀(γ) → 0 as γ → 0.
- {#B0.91} *Lower bounds on ε₁/g_k (the Gaussian tail).* These are RG2 p.12 (χ^c_{k,P}), (2.22), (2.26), (2.31), p.16 (the tail
  {#B0.92} bound), p.17, p.18 (the bracket and γ₂ε₁²/(20γ²) ≥ 4κ), (2.33) and (2.34), p.19.
  {#B0.92-1} With δ_k the ratio is
  {#B0.93} δ_k/g_k = A₁(log g_k^{−2})^{p₀} ≥ A₁(log γ^{−2})^{p₀}, which tends to ∞ as γ → 0.
  {#B0.93-1} RG2 prints the conditions of
  {#B0.94} pp.18–19 with γ in place of g_k: it passes from exp(−γ₂ε₁²/(20g_k²)) to exp(−γ₂ε₁²/(20γ²)) through g_k ≤ γ
  {#B0.95} (RG2 p.18, "(1/20)γ₂ε₁²/g_k² ≥ (1/20)γ₂ε₁²/γ² ≥ 4κ", and (2.33)–(2.34), pp.18–19).
  {#B0.95-1} With a cutoff that tends to 0 with g_k, the γ-form fails for g_k ≪ γ, so the conditions are re-derived at g_k
  {#B0.96} from the same estimates.
  {#B0.96-1} RG2 p.19 prints "ε₂ = 2E₀ε₁C₁α₄^{−1}α₆^{−1}M^q exp C₂κ₁", so ε₂ is proportional to the
  {#B0.97} cutoff, and the condition of p.19 becomes exp(−γ₂A₁²(log g_k^{−2})^{2p₀}/20) ≤ c_εδ_k with
  {#B0.98} c_ε := 2E₀C₁α₄^{−1}α₆^{−1}M^q e^{C₂κ₁}.
  {#B0.98-1} Since 2p₀ > 1, the left side is smaller than any power of g_k for g_k small, so it holds for
  {#B0.99} g_k ≤ γ small, as in Proposition 2.9, step 6.
  {#B0.99-1} The condition of p.18, γ₂δ_k²/(20g_k²) ≥ 4κ, holds once
  {#B0.100} γ₂A₁²(log γ^{−2})^{2p₀} ≥ 80κ.
- {#B0.100-1} *Invariance.* RG1 p.269 l.8–9: the characteristic function is invariant under the transformations of B′, which are local and orthogonal, so (2.13) is gauge invariant.
- {#B0.101} *Comparisons within one step.* For a bond c of T^{(k+1)}, b₀(c) and the blocks B(y) are #T10.13-1's. RG1's cutoff (2.9), p.266 l.46, acts on the step variables B′(b) (#B4.53-1), b ∉ {b₀(c)}, and RG1 p.267 l.1–2 bounds the eliminated B′(b₀(c)) by O(ε₁), with the cutoff of the same step.

{#B0.102} The inductive assumptions RG1 (1.1)–(1.22) do not contain ε₁, and no estimate compares the cutoffs of two steps.
{#B0.102-1} So the
{#B0.103} parts of RG1 Theorem 3 that §§2.1–2.2 use, the bound (1.18) and the analyticity of the step terms in (U, J) on the fixed
{#B0.104} domains, hold with the cutoffs δ_j for γ small.
{#B0.104-1} The gauge invariance and Euclidean covariance of the step terms, which
{#B0.105} the definition of β by RG1 (1.21)–(1.22) and the scalar Π of Lemma 2.5 use, rest on the invariance of #B0.100-1 and hold for any cutoff that is invariant under
{#B0.106} Ad(G) and the lattice symmetries, as δ_j is.
{#B0.106-1} The clauses of RG1 p.263 l.26 (E^{(j)} is a C^∞, or analytic, function of g_{j−1}) and p.264 l.32 (β_j is smooth, or analytic, on [0, γ]), which p.266 l.49–50 ties to the choice of cutoff,
{#B0.107} are not transferred to a coupling-dependent cutoff and are not used; continuity in the couplings is
{#B0.108} Proposition 2.6.

{#B0.109} *Identification with CRE's construction.* CRE builds its step terms with the formulas of RG1: "All the applied formulas
{#B0.110} are the same as in Sect. 2 [I], only the symbols represent different operators, determined by the sequence {Ω_j}" (CRE
{#B0.111} p.267).
{#B0.111-1} Of the result it states: "the terms E₀^{(k+1)}(Λ_{k+1}, X, z) of this representation, for X ⊂ Λ_{k+1}, do not
{#B0.112} depend on Λ_{k+1}, and coincide with the corresponding terms arising from the expressions defined on the whole lattice,
{#B0.113} i.e. in the framework of [I]" (CRE p.278). "The framework of [I]" means RG1's whole-lattice formulas, run with CRE's
{#B0.114} inputs (its cutoff δ_k and E_k with R′_k of #B0.127 folded in), not RG1's construction itself.
{#B0.114-1} The last logarithm of CRE (3.28) "is formally given by the same formula as
{#B0.115} the term E^{(k+1)} in [I] [see (2.12), (2.13)], but the integral is restricted to Λ_{k+1}, and operators are determined
{#B0.116} by the sequence {Ω_j}" (CRE p.272), and for Ω_j = Λ_j = T_η "the expressions (3.37) coincide with the expressions in the
{#B0.117} inductive assumption" (CRE p.274).
{#B0.117-1} Those expressions include R′_k (p.271), and their Euclidean covariance (3.39)
{#B0.118} follows from (2.29) and from (2.32), p.260, the covariance of the R-terms (p.274).
{#B0.118-1} CRE (2.24) defines the couplings
{#B0.119} g_{j−1} "as in (I.0.20)" (p.259), with CRE's own β_j.
{#B0.119-1} CRE's coefficient is built from the whole-lattice step term alone: Π^{(j)} in CRE
{#B0.120} (3.57), p.281, is "given by the formula (3.50), but with E^{(j)}(X, U_j, z) replaced by E^{(j)}(U_j, z) defined on the
{#B0.121} whole lattice", so the terms R″^{(k+1)} and B^{(k+1)}, the other two of the three terms into which CRE divides the logarithm of the fluctuation integral (3.25) (p.279 l.19–23), do not enter it.
{#B0.121-1} With Π^{(j)}_{μν,κλ} := Σ_{x,y}Π^{(j)}_{μν}(x, y, z)(x_κ − z_κ)(y_λ − z_λ) (p.281 l.56), CRE (3.61), p.282, defines β′_j := Π^{(j)}_{22,11},
{#B0.122} and CRE proves that "it coincides with the definition (I.1.22)": (3.62) uses translation invariance and the identity
{#B0.123} (I.4.15), and the identity (3.63), Σ_zΠ^{(j)}_{μν}(x, y, z) = Π^{(j)}_{μν}(x − y), whose right side is the tensor of RG1 (1.20) and (5.1) (RG1 p.264 l.4–6, p.292 l.17–19), is obtained "From the equality (2.26) for Λ_j=L^{−j}Z^d, and from the definitions (I.1.20), (I.5.1)" (CRE p.282 l.54–56); CRE (3.64), p.283 l.4, gives β′_j = −½Σ_xΠ^{(j)}_{22}(x)x_1² = β_j.
{#B0.123-1} With h_z(x) := ∏_μ max{1 − |x_μ − z_μ|, 0} on T_{L^{−j}} (CRE (3.40), p.275 l.4, as modified at p.283 l.15), CRE (3.67), p.283 l.28–31, then asserts that
{#B0.124} E^{(j)}(Λ_j, U_k, z) − E^{(j)}(Λ_j, 1, z) − β_jA(h_z, U_k) = O((L^jL^{−n})^{5−β}), with CRE's exponent β > 0 (printed so, not a coefficient), for z ∈ Λ_j^0 ∩ (Ω_n∖Ω_{n+1}), with Λ_j^0 the set Λ_j^{(j)} less one layer of MR_j-cubes (CRE p.259 l.30–31) and Ω_n the n-th set of CRE's sequence {Ω_j} (p.255 l.12); since A(h_z, U_k) is marginal ((3.66), p.283 l.19), CRE's β_j is the marginal coefficient
{#B0.125} of CRE's own E^{(j)}.
{#B0.125-1} CRE p.253 points to "(1.41)–(1.43)" of [I] for β₁; RG1 §1 ends at (1.22), and
{#B0.126} the pointer is not used.

{#B0.127} *The R-terms.* Before step k+1, CRE folds R′_k := Σ_{j=1}^{k₁}R^{(j)}, the sum of the R-terms R^{(j)} of the steps j ≤ k₁ (#B0.129-1), with k₁ "the largest integer satisfying L^{−(k−k₁)}MR_j ≤ L" (CRE p.270 l.49–50), into E_k: "It has the same covariance
{#B0.128} property as the expression determined by E_k, and we include it into E_k" (CRE p.271).
{#B0.128-1} So the bracket
{#B0.129} {E_k(U_k(…)) − E_k(U_{k+1})} whose fluctuation integral gives E^{(k+1)} contains R-terms.
{#B0.129-1} The R-terms do not vanish on
{#B0.130} the small-field density: for ρ(V) = Σ_Zρ(Z, V) over large-field regions Z = Z′ ∪ Z″, with Z″ the components whose small factors control the next steps and Z′ those that require a renormalisation (LFR1 (0.2), p.176 l.7 and l.10–14), the R-operation (LFR1 (0.3)) integrates out Z′ and leaves
{#B0.131} the quotients on ρ(Z″, V) as exp Σ_X ℝ(X, V), a sum over polymers X meeting Z″^c (LFR1 (0.5)–(0.6), p.176), also for Z″ = ∅.
{#B0.131-1} Hence CRE's
{#B0.132} β_j = β_j^δ + β_j^R, where β_j^δ is the coefficient of RG1's construction run with δ_j (the β_j of §§2.1–2.2) and β_j^R
{#B0.133} is the change of the coefficient caused by the R′-terms.
{#B0.133-1} For the tube construction the same split holds with β_j^{δ,T},
{#B0.134} the coefficient of RG1's construction run with the tube cutoffs δ_j^T, in place of β_j^δ, and Proposition 2.11 bounds
{#B0.135} the R-part: |β^T_{k+1} − β^{δ,T}_{k+1}| ≤ C_R g_k^{κ₀−4} on the histories of the tube, with κ₀ ≥ 7 (CRE (2.31), p.260;
{#B0.136} (2.46), p.263).
{#B0.136-1} Propositions 2.4 and 2.9 hold for β^{δ,T} on the histories of the tube (Lemma 2.10, step 7).
{#B0.136-2} Item 5,
{#B0.137} with C_rem + C_Rγ^{κ₀−6}, and (P2) and (W), with the tube's δ′ (#B0.63-1), then hold on the histories of the
{#B0.138} tube (Proposition 2.11, *Consequence*); item 2, and items 3 (with δ′) and 4 along the matched flow, hold by
{#B0.139} Propositions 2.12 and 2.13.

{#B0.140} *CRE's Step Terms and β_j (checked against CRE pp.259, 267, 268, 271, 272, 274, 278, 279, and 281–283, corrected transcriptions).*
- {#B0.141} The step is RG1's whole-lattice construction (RG1 §2): "All the applied formulas are the same as in Sect. 2 [I]"
  {#B0.142} (p.267), and the last logarithm of (3.28) "is formally given by the same formula as the term E^{(k+1)} in [I]" (p.272).
- {#B0.143} Its cutoff is CRE's δ_k (#B0.5): the characteristic function of (3.16), p.268.
- {#B0.144} The only additional input is R′_k, which "we include … into E_k" (p.271).
  {#B0.144-1} The R-terms otherwise get "the vacuum
  {#B0.145} energy renormalization only" (p.259).
  {#B0.145-1} Once R′_k is inside E_k, its contribution to the fluctuation integral of the
  {#B0.146} next step enters E^{(k+1)} and is coupling-renormalised with it ((3.57), p.281).
- {#B0.147} β_j is built from the whole-lattice E^{(j)} ((3.57), p.281), so R″^{(j)} and B^{(j)} do not enter it, while the R′-part
  {#B0.148} does.
  {#B0.148-1} It is the second moment of the polarisation of that E^{(j)} ((3.61)–(3.64), pp.282–283).
- {#B0.149} CRE (3.67), p.283, leaves only an irrelevant remainder after β_jA(h_z, U) is subtracted, which holds only for the
  {#B0.150} coefficient of CRE's own E^{(j)}.

{#B0.151} CRE p.259 l.40–42 (property (ii)) states analyticity of CRE's step terms on smaller domains, with the radii (2.28), α_{0,j} = g_jC^α_0(log g_j^{−2})^{q₀} (CRE's C₀, renamed at #B2.2.177), for its
{#B0.152} localised bounds.
{#B0.152-1} CRE's localised pieces (CRE (3.37), (3.41), (3.44)–(3.47)) are not RG2's (RG2 (2.1)–(2.13)).
{#B0.152-2} Without R-terms
{#B0.153} (s = 0 in Proposition 2.11) their sums coincide with RG2's whole-lattice terms up to log Z^{(k)} and an additive constant: CRE's side
{#B0.154} contains the Gaussian term log Z^{(k)} (#B2.1.1), CRE's log[z^{(k)}∫dA exp(−½⟨A, 𝒫*Δ^{(k)}𝒫A⟩)] (CRE p.273 l.23–28, printed with C for 𝒫, #T10.28-4), localised by (3.38)–(3.42) (pp.274–275), which RG2's step term excludes; the constant does
{#B0.155} not contribute to β, which is a second derivative in B, and log Z^{(k)} enters β on both sides through
{#B0.156} β_{k+1} = Λ(log Z^{(k)}) + Λ(E^{(k+1)}_fl) (Proposition 2.4, step 1; Remark 2.3, *What β is*). β^δ depends only on the second
{#B0.157} derivatives of the sum at B = 0 (RG1 (1.20)), and §§2.1–2.2 bound it through RG2's own pieces on the fixed domains.
{#B0.157-1} So
{#B0.158} (2.28) is not needed for β^δ.
{#B0.158-1} On the domains of (2.28) alone the Cauchy radius of Lemma 2.5 would be proportional to
{#B0.159} min(α_{0,j}, α_{1,j}) (as in Proposition 2.11, step 5, #B2.2.469), and Proposition 2.4 would not give a small bound (`WILSON_CAUCHY_LIPSCHITZ_2026_10_21.md`, *What changes on
{#B0.160} CRE's domains*).
{#B0.160-1} The R-part β^R is bounded on the domains of (2.28), with the tube radii; there only the size
{#B0.161} C_Rg_k^{κ₀−4} is needed, which the factor g_k^{κ₀} supplies (Proposition 2.11, step 3 for the radius ρ = θg_k^{2−κ₀}, and steps 5–6).

## 1. One β for Simple G {#BS1}

{#B1.1} Let G ⊂ U(N) be compact simple, with Lie algebra g.

{#B1.2} **Lemma 1.1.** Every Ad(G)-invariant bilinear form on g, real or complex valued, is a multiple of the Killing form K, K(X, Y) := Tr(ad X ad Y) with ad X := [X, ·] the matrix commutator on g^c := g ⊗ ℂ ⊂ gl(N, ℂ), in either convention for g (anti-Hermitian, or RG1's Hermitian). In particular the
{#B1.3} trace form tr(XY) of the defining representation (normalised trace, tr 1 = 1) is κ^{−1}K, with κ > 0 defined by
{#B1.4} K = κ·tr.

{#B1.5} *Proof.* Ad(G) acts irreducibly on g, over ℝ, and its complexification is irreducible because g is compact simple.
{#B1.5-1} By
{#B1.6} Schur's lemma an invariant form, written as K(T·, ·) with T commuting with Ad(G) on g^c, is a multiple of K. ∎
{#B1.7} References (page images read): B. Simon, *Representations of Finite and Compact Groups* (AMS GSM 10, 1996): invariance
{#B1.8} of K, Prop. VIII.2.1(b); K negative definite, Prop. VIII.2.2; uniqueness of the invariant inner product for irreducible
{#B1.9} orthogonal representations, with the Schur remark, Prop. VIII.2.3; Ad irreducible ⇔ g simple, and the definition of
{#B1.10} simple, Thm. VIII.2.4.

{#B1.11} Example: for SU(N) ⊂ U(N), K(X, Y) = 2N Tr(XY) for traceless X, Y: gl(N, ℂ) ≅ ℂ^N ⊗ (ℂ^N)* gives Tr_{gl(N,ℂ)}(ad X ad Y) = 2N Tr(XY) − 2Tr X Tr Y, and ad X vanishes on ℂ1. With tr = Tr/N, κ = 2N²; these are complex-bilinear identities on g^c, so they hold in either convention.

{#B1.12} **Consequences.**
1. {#B1.13} RG1 twice uses that an element of g ⊗ g invariant under every R(v) ⊗ R(v), v ∈ G, R(v)B = vBv^{−1} the constant gauge transformation acting on g (inferred from "V → R(v)V, or B → R(v)B", p.264 l.10, not printed), is proportional to the identity matrix: for the vacuum polarisation Π^{ab}_{j+1,μν}(g_j, x, x′) of (1.20) (p.264 l.9–12), and for 𝐄^{(2)}_{μ,ν}(x, y) in (4.33) (p.289 l.29–37).
   {#B1.13-1} Identify g ⊗ g with the bilinear forms on g by the scalar product tr, which every R(v) preserves; an invariant element is then an Ad(G)-invariant form, so by Lemma 1.1 a multiple of tr, and its matrix in a tr-orthonormal basis is a multiple of δ^{ab}.
   {#B1.14} So Π^{ab}_{j+1,μν}(g_j, x, x′) = δ^{ab}Π_{j+1,μν}(g_j, x − x′) with one real function Π_{j+1,μν} (RG1 (1.21), p.264 l.14–21; the dependence on x − x′ and the rotation property come from the Euclidean invariance of p.264 l.12–13), from which RG1 (1.22), p.264 l.22–30, defines one β_{j+1}(g_j); and the matrix of 𝐄^{(2)}_{μ,ν}(x, y) is a multiple of δ_{ab}, so ⟨𝐄^{(2)}_{μ,ν}(x, y), A ⊗ B⟩ is a multiple of tr AB (p.289 l.36–37).
2. {#B1.15} That the effective actions have the form RG1 (1.3), p.260 l.38–44, and (1.6), p.261 l.14–17, with the single counterterm Σ_{j<k} β_{j+1}(g_j)A(U_k) for the Wilson action A(U) = Σ_p [1 − Re tr U(∂p)], is part of the inductive assumptions (1.1)–(1.22). RG1 Theorem 3 (p.264 l.37–42) states them for 0 < g_k ≤ γ and the actions A_k defined by the transformations (0.17)–(0.20), whose couplings follow RG1 (0.20), p.256 l.2–5, and RG1 announces it as proved for every compact semisimple G ⊂ U(N) (p.259 l.23–24).
   {#B1.16} Its proof uses the proportionality of #B1.13–#B1.14, which needs more than Ad(G)-invariance when G has two or more simple factors (#B10.77-1); for G as in #B1.1 Lemma 1.1 supplies it, so for such G the theorem holds and the action carries one coupling at each step.

## 2. The Flow Lemma (Window Form) {#BS2}

{#B2.1} Work with x_k := g_k^{−2}.
{#B2.1-1} The flow RG1 (0.20), with β_{k+1} written as a function of the history (#B0.3), is x_k = x_{k+1} + β_{k+1}(h_k), where h_k := (g_0, …, g_k) is the
{#B2.2} history.
{#B2.2-1} Fix γ > 0, and let 𝔖_γ be the set of histories with all entries in (0, γ].

{#B2.3} **Hypotheses.**
- {#B2.4} **(W)** There are constants 0 < b ≤ b′ and C such that for all 0 ≤ m ≤ n and all histories in 𝔖_γ:
  {#B2.5} b(n−m) − C ≤ Σ_{j=m}^{n−1} β_{j+1} ≤ b′(n−m) + C. This is the window of RG1 (0.31), stated for β.
- {#B2.6} **(C)** Each β_{j+1} is continuous on 𝔖_γ.

{#B2.7} **Lemma 2.1.** Assume (W) and (C).
{#B2.7-1} Let γ′ := (γ^{−2} + C)^{−1/2}.
{#B2.7-2} For every K and every g ∈ (0, γ′] there is a bare
{#B2.8} coupling g_0 whose flow stays in 𝔖_γ up to step K and has g_K = g.
{#B2.8-1} Moreover, for all 0 ≤ k ≤ K (RG1 (0.31)):
- {#B2.9} (i) g^{−2} + b(K−k) − C ≤ g_k^{−2} ≤ g^{−2} + b′(K−k) + C, i.e. RG1 (0.31) with β = b/ln L, β′ = b′/ln L, up to an
  {#B2.10} additive constant;
- {#B2.11} (ii) g_k^{−2} ≥ g_l^{−2} − C for k ≤ l (near-monotonicity).

{#B2.12} *Proof.* The type-checked Lean core is `BalabanFormal.flow_lemma`.
{#B2.12-1} It is stated for a vector of couplings, with the
{#B2.13} Poincaré–Miranda theorem as a hypothesis; for one coupling that hypothesis is the intermediate value theorem.
1. {#B2.14} *Clamping.* Let c(x) := max(x, γ^{−2})^{−1/2} ∈ (0, γ].
   {#B2.14-1} Define the clamped flow by
   {#B2.15} x_{k+1} := x_k − β_{k+1}(c(x_0), …, c(x_k)).
   {#B2.15-1} It is defined for all x_0 ∈ ℝ and is continuous in x_0 by (C).
   {#B2.15-2} Let
   {#B2.16} f_K(x_0) := x_K.
2. {#B2.17} *The interval.* Let t := g^{−2}.
   {#B2.17-1} Clamped histories lie in 𝔖_γ, so (W) with m = 0, n = K gives
   {#B2.18} f_K(x_0) ∈ [x_0 − b′K − C, x_0 − bK + C].
   {#B2.18-1} At x_0 = t + bK − C this gives f_K(x_0) ≤ t, and at x_0 = t + b′K + C it
   {#B2.19} gives f_K(x_0) ≥ t.
3. {#B2.20} *Intermediate values.* f_K is continuous on [t + bK − C, t + b′K + C], so it takes the value t at some x_0 there.
4. {#B2.21} *The clamping is inactive.* For this solution, (W) on the window [k, K) gives
   {#B2.22} x_k = t + Σ_{j=k}^{K−1}β_{j+1} ≥ t + b(K−k) − C ≥ γ^{−2}, using t ≥ γ^{−2} + C. So c(x_k) = x_k^{−1/2} at every step,
   {#B2.23} and the clamped flow is the true flow, inside 𝔖_γ.
   {#B2.23-1} Then (i) is (W) on [k, K), and (ii) is (W) on [k, l). ∎

{#B2.24} **Remark 2.2 (What the Comparison after LFR2 (1.86) Needs).** Part (ii) and g_l^{−2} ≥ γ^{−2} give
{#B2.25} log g_k^{−2} ≥ log g_l^{−2} + log(1 − Cγ²) ≥ log g_l^{−2} − 2Cγ² for k ≤ l, once Cγ² ≤ ½.
{#B2.25-1} Hence
{#B2.26} p₀(g_k) ≥ (1+β₀)^{−1} p₀(g_l), with β₀ of CRE (2.6) (#B2.2.155), once γ is small, which is the comparison after LFR2 (1.86), p.386 l.38–40.

{#B2.27} **Remark 2.3 (From b to β).** Suppose that the zero-coupling coefficients satisfy (W) with constants 2c ln L, 2c ln L and
{#B2.28} C₀ (the bound 2C of Theorem 8.1, #B8.4), and that (P2) holds: |β_{j+1}(h) − b_{j+1}| ≤ δ on 𝔖_γ.
{#B2.28-1} Then (W) holds for β with
{#B2.29} b = 2c ln L − δ, b′ = 2c ln L + δ and C = C₀, and b > 0 for δ < 2c ln L. So RG1 Theorem 2 (RG1 p.259), with (0.31) up to an additive constant (#B8.38-2), reduces to
{#B2.30} Theorem 8.1 together with (P2) and (C), which §2.1 derives.
{#B2.30-1} The type-checked Lean core is
{#B2.31} `BalabanFormal.coupling_flow_of_stepBound`.

{#B2.32} *What β is.*
- {#B2.33} β_{j+1} is #B0.3's; its step term E^{(j+1)} contains the Gaussian
  {#B2.34} term log Z^{(j)} (compare RG1 (1.3), p.260).
- {#B2.35} By RG1 (1.3), (1.6) and (2.12)–(2.13), pp.260–268, up to a constant in U, E^{(j+1)}(g_j, U) = log Z^{(j)}(U) + log ∫ χ_j exp[P^{(j)} + {…}] dμ_{C^{(j)}(U)}(B).
  {#B2.36} Here C, C^{(j)}, P^{(j)} and the curly bracket {…} are #T10.28-4's, RG1's step index k being j here.
- {#B2.37} The earlier couplings enter only through {…}: the previous interaction at the fluctuating configuration, minus its
  {#B2.38} value at the background.
- {#B2.39} At g_j = 0 the exponent vanishes (p.268 l.27), and the cutoff χ_j = Π_b χ({|g_j(CB)(b)| < ε₁}) of RG1 (2.9), over the bonds b of T^{(j)} other than the b₀(c), is identically 1.
  {#B2.40} Hence β_{j+1}(g_0, …, g_{j−1}, 0) = b_{j+1} exactly, for all g_0, …, g_{j−1}.

{#B2.41} Neither (P2) nor (C) is stated in RG1 or RG2.
{#B2.41-1} The smoothness statement after RG1 (1.22) comes without proof.
{#B2.41-2} §2.1
{#B2.42} derives both from RG2's published bounds.

### 2.1 The History Dependence: (P2) and (C) {#BS2.1}

{#B2.1.1} Write Z^{(k)}(U) := ∫dB δ(Q̃B)exp[−½⟨B, Δ^{(k)}(U)B⟩], RG1's normalisation factor (1.4) at j = k (p.260 l.46–50; p.267 l.38–40), and E^{(k+1)}_fl for the fluctuation integral RG1 (2.13), so that the RG1 (1.6)-form step term is
{#B2.1.2} [log Z^{(k)}(U) − log Z^{(k)}(1)] + E^{(k+1)}_fl.
{#B2.1.2-1} RG2 represents E^{(k+1)}_fl = Σ_X E^{(k+1)}_fl(X) by an exponentiated
{#B2.1.3} cluster expansion.
{#B2.1.3-1} G is simple, so there is one coupling.

{#B2.1.4} **Proposition 2.4 (P2).** There are constants C_Λ and C₃, independent of k, of the history and of the cutoff ε₁, such
{#B2.1.5} that for every k and every history h ∈ 𝔖_γ (RG2 (2.41); proof below)
  {#B2.1.6} |β_{k+1}(h) − b_{k+1}| ≤ C_Λ C₃ ε₁.

{#B2.1.7} Every condition on ε₁ in RG1–RG2 is an upper bound (step 4).
{#B2.1.7-1} So ε₁ can be chosen with
{#B2.1.8} C_Λ C₃ ε₁ ≤ c ln L, and γ is then chosen small.
{#B2.1.8-1} This gives (P2) with δ = c ln L.

{#B2.1.9} *Proof.*
1. {#B2.1.10} *Split.* β is linear in the step term (RG1 (1.20)–(1.22)).
   {#B2.1.10-1} Write Λ for this linear map, so that
   {#B2.1.11} β_{k+1}(h) = Λ(log Z^{(k)}) + Λ(E^{(k+1)}_fl(·; h)).
   {#B2.1.11-1} At g_k = 0 the exponent in RG1 (2.13) vanishes and χ_k ≡ 1, so
   {#B2.1.12} E^{(k+1)}_fl = 0.
   {#B2.1.12-1} Hence b_{k+1} = Λ(log Z^{(k)}), the zero-coupling coefficient of Theorem 8.1, and
   {#B2.1.13} β_{k+1}(h) − b_{k+1} = Λ(E^{(k+1)}_fl(·; h)).
2. {#B2.1.14} *The step bound.* RG2 (2.41), p.21, gives on U^c_{k+1}(X, α₀, α₁):
     {#B2.1.15} |E^{(k+1)}_fl(X)| ≤ O(1) C₃ ε₁ exp(−κ d_{k+1}(X)),  C₃ = 2(L+2)⁴O(1)·2E₀C₁α₄^{−1}α₆^{−1}M^q e^{C₂κ₁}
   {#B2.1.16} (RG2 p.20 l.25, (2.41) p.21 l.22), using (1−10δ_{RG2})½L ≥ 1. This file fixes δ_{RG2} := (1 − 2L^{−1})/12, so (1 − 12δ_{RG2})½L = 1 (#B2.2.78), in place of RG2's (1 − 2L^{−1})/10 (p.21 l.25): RG2 §2 uses its last assumption (1 − 10δ_{RG2})½L = 1 only to bound exp(−(1 − 10δ_{RG2})½Lκd_{k+1}) by exp(−κd_{k+1}) (p.21 l.22–29).
   {#B2.1.16-a} RG2's conditions ¼(κ₁ − 1) ≥ (1 − δ_{RG2})κ (p.9 l.16, with δ_{RG2} ∈ (0, 1) as RG2 requires), (1/16)κ₁ ≥ (1 − 2δ_{RG2})κ (p.9 l.25–26) and ⅛(κ₁ − 1) ≥ (1 − 3δ_{RG2})κ (p.16 l.20) hold, since ½(κ₁ − 1) ≥ 2Lκ (p.20 l.17) gives κ₁ > 4Lκ > 16κ (L > 11, #BP.9). Its conditions "for δκ sufficiently large" (p.9 l.20, and the counts of #BK.6) and "for κ sufficiently large and α₆ sufficiently small" (p.18 l.17) are lower bounds on κ, met at δ_{RG2} for κ large depending on L, and the choice of RG2's small constant α₆, made before ε₁, whose conditions contain α₆^{−1} (#B2.1.25).
   {#B2.1.16-0} Here E₀, B₀, C₁′, C₁, C₂, q, α₂, M₁, α₄, γ₂, α₆, δ_{RG2} and κ₁ are RG2's (#B0.6-3); κ₁ is RG2's own decoupling parameter (|s(Δ)| ≤ e^{κ₁}, RG2 p.5 l.7–8), not the choice of #B10.177-0.
   {#B2.1.16-1} The factor ε₁ comes from Lemmas 1–3 of RG2.
   {#B2.1.16-2} On the cutoff region the unscaled
   {#B2.1.17} fluctuation is |g_kCB| < ε₁, so the interaction V_k is O(ε₁): RG2 (1.36), (1.43); RG1 p.269 ("coefficients of the
   {#B2.1.18} order O(ε₁)").
   {#B2.1.18-1} The cutoff complement contributes exp(−γ₂ε₁²/(20γ²)) ≤ ε₂ (RG2 (2.22), (2.33)).
   {#B2.1.18-2} The earlier
   {#B2.1.19} couplings enter only through E_k.
   {#B2.1.19-1} RG1 Theorem 3 gives E_k the inductive bounds RG1 (1.18) for every sequence in
   {#B2.1.20} (0, γ], so RG2 (2.41) is uniform in the history.
3. {#B2.1.21} *Polarisation.* Lemma 2.5 gives |Λ(F)| ≤ C_Λ A for localised F with |F(X)| ≤ A e^{−κd_{k+1}(X)}.
   {#B2.1.21-1} Take
   {#B2.1.22} A = O(1)C₃ε₁ (RG2 (2.41)).
4. {#B2.1.23} *Constants.* The conditions on ε₁ are all upper bounds, given κ, κ₁, M, the α's, E₀ and L; RG2's conditions in ε₁²/γ² (p.18 l.40, p.19 l.12) are upper bounds on γ, which is fixed after ε₁ (#T1.9):
   - {#B2.1.24} RG2 p.7 l.7 and l.9: e^{32κ₁}ε₁ below a constant RG2 calls absolute, of stage 2 with #T10.28-3-1's C₁′ (#BH.5), and 4B₀C₁′e^{16κ₁}ε₁ ≤ ¼α₂; RG2 p.10 l.37 with p.11 l.2: e^{16κ₁}C₁′ε₁ ≤ ⅓a₁, with a₁ of #T10.28-4-5 (inferred, not printed: (1.40) holds for e^{16κ₁}abs(B′) ≤ ⅓a₁ and is applied to abs(B′) < C₁′ε₁; #BH.5-1 of balaban_proofs/BP_RG2_COMPLEX_B.md); for complex B, the further conditions on ε₁ of #BH.1;
   - {#B2.1.25} RG2 p.18 l.9: 2E₀ε₁C₁α₄^{−1}α₆^{−1}M^q e^{C₂κ₁}e^{5κ} ≤ 1;
   - {#B2.1.26} RG2 p.20 l.6: 2(L+2)⁴O(1)ε₂e^{5κ} ≤ 1;
   - {#B2.1.27} RG2 p.21 l.11: "ε₁ sufficiently small" for the cluster expansion of (2.39) that gives (2.41); RG2 p.21 l.25: O(1)C₃ε₁ ≤ ½E₀, with #T10.28-3-3's C₃;
   - {#B2.1.28} RG1 p.265 l.18–19 and l.33–34 (χ_k of (2.9), which bounds abs(B′) by ε₁ (p.266 l.46), restricts U_k(V) to U_k(ε₀) and B′ to "a sufficiently small neighborhood of 0"), RG1 p.273, RG1 p.276 and RG1 p.280: "ε₁ is so small", "ε₁ sufficiently small".

   {#B2.1.29} γ enters only through exp(−γ₂ε₁²/(20γ²)) ≤ ε₂ and γ₂ε₁²/(20γ²) ≥ 4κ (RG2 pp.18–19), conditions on γ chosen last.
   {#B2.1.30} C_Λ depends on κ, δ₀, α₀, α₁, d, M and L, and C₃ on the constants listed.
   {#B2.1.30-1} Neither depends on ε₁. ∎

{#B2.1.31} **Lemma 2.5 (The Polarisation Is Bounded).** Let F = Σ_X F(X), with F(X) analytic on the space U^c_{k+1}(X, α₀, α₁) of
{#B2.1.32} RG1 (1.11)–(1.16) and depending on (U, J) restricted to X, and |F(X)| ≤ A e^{−κd_{k+1}(X)}, as in RG2 (2.41).
{#B2.1.32-1} Put
{#B2.1.33} Π(x) := ∂²F(U_{k+1}(e^{iB}))/∂B_μ(0)∂B_ν(x) at B = 0, and Λ(F) := Σ_x Π(x)x_μx_ν (μ ≠ ν).
{#B2.1.33-1} Then |Λ(F)| ≤ C_Λ A.

{#B2.1.34} *Proof.* Write u(B) for the configuration (U_{k+1}(e^{iB}), J_{k+1}(e^{iB})) restricted to X, and ‖·‖ for the norms in which
{#B2.1.35} the conditions of U^c_{k+1}(X, α₀, α₁) are stated.
1. {#B2.1.36} *The background map.* B ↦ U_{k+1}(e^{iB}) is analytic for small complex B. Its functional derivative decays
   {#B2.1.37} exponentially, with rate δ₀ (VAR Prop. 9, p.309, and VAR (190); RG1 p.271).
   {#B2.1.37-1} So ‖∂u/∂B_ν(y)‖ ≤ C e^{−δ₀ dist(y,X)} for every site y and direction ν, B_ν(y) the variable on the bond (y, y + e_ν).
   {#B2.1.38} *Input status.* VAR p.308 derives VAR (190) from VAR (189), and VAR (189) is stated without proof ("We do not
   {#B2.1.39} perform these calculations here").
   {#B2.1.39-1} balaban_proofs/BP_VAR_189.md proves it in VAR's setting (not yet through review; sidecar node
   {#B2.1.40} VAR_189).
   {#B2.1.41} Apply Cauchy's estimate in the single variable B_{ν′}(y′), on a disc of fixed radius, to ∂u/∂B_ν(y).
   {#B2.1.41-1} This gives
   {#B2.1.42} ‖∂²u/∂B_ν(y)∂B_{ν′}(y′)‖ ≤ C e^{−δ₀ dist(y,X)}.
   {#B2.1.42-1} By symmetry the same holds with dist(y′, X), so the bound is
   {#B2.1.43} C e^{−δ₀(dist(y,X) + dist(y′,X))/2}.
2. {#B2.1.44} *Cauchy in the configuration.* Restrict F(X) to the lines u + t v and u + t v + s w.
   {#B2.1.44-1} This gives
   {#B2.1.45} |DF(X)[v]| ≤ A e^{−κd_{k+1}(X)}‖v‖/r and |D²F(X)[v, w]| ≤ 4A e^{−κd_{k+1}(X)}‖v‖‖w‖/r², the latter on the polydisc |t| ≤ r/(2‖v‖), |s| ≤ r/(2‖w‖), with r > 0 depending on α₀, α₁ only.
3. {#B2.1.46} *Chain rule.* Π(x) = Σ_X (D²F(X)[∂_{B_μ(0)}u, ∂_{B_ν(x)}u] + DF(X)[∂²_{B_μ(0)B_ν(x)}u]).
   {#B2.1.46-1} By steps 1 and 2, the X-term is
   {#B2.1.47} at most C A r^{−2} e^{−κd_{k+1}(X)} e^{−δ₀(dist(0,X) + dist(x,X))/2}.
4. {#B2.1.48} *Sum.* Σ_x |x|² e^{−δ₀ dist(x,X)/2} ≤ C(1 + diam X + dist(0, X))^{d+2}.
   {#B2.1.48-1} The remaining sum over X of
   {#B2.1.49} e^{−κd_{k+1}(X) − δ₀dist(0,X)/2} times this polynomial converges for κ large: diam X ≤ M(2d_{k+1}(X) + 4) (#BK.1), so the polynomial is at most C(M)(1 + d_{k+1}(X))^{d+2}(1 + dist(0, X))^{d+2}; sum first over the X containing a given cube □, the cube of X nearest to 0, by RG2 (1.26), p.008 l.5, and then over □, with dist(0, X) = dist(0, □). ∎
   {#B2.1.49-1} #BK.1 (balaban_proofs/BP_RG2_CUBE_COUNT.md, not yet through review) is the count M^{−4}|X| ≤ 2⁹(1 + d_j(X)) of the cubes of X ∈ 𝐃_j, in place of RG2's (1.28), p.008 l.19, (2.30), p.018 l.25, and p.009 l.23, which fail at d_j(X) = 0; #BK.6–#BK.7 check RG2's uses of it.

{#B2.1.50} This is the argument behind RG1 p.264 (existence of the limit RG1 (1.21) and boundedness of β).
{#B2.1.50-1} It is linear in A.

{#B2.1.51} **Proposition 2.6 (C).** For each k, h ↦ β_{k+1}(h) is continuous on (0, γ]^{k+1}.

{#B2.1.52} *Proof.* Induction on k.
{#B2.1.52-1} The claim S_k is: for every X, E^{(k+1)}_fl(X; h) is continuous in h at each
{#B2.1.53} (U, J) ∈ U^c_{k+1}(X, α₀, α₁).
1. {#B2.1.54} *Where the couplings enter.* In RG2's representation RG2 (2.1)–(2.14), the operators, covariances and measures
   {#B2.1.55} (C^{(k)}, Γ_k, dμ₀ and the s-dependent propagators) depend on (U, J) only.
   {#B2.1.55-1} The couplings enter in two ways:
   - {#B2.1.56} (a) the potentials V_k(Y, B) of RG2 Lemma 2 (p.11);
   - {#B2.1.57} (b) the indicators χ_{k,Y₀} and χ^c_{k,P}, whose threshold is ε₁/g_k (RG2 (2.3)).
2. {#B2.1.58} *(a) is continuous at h⁰ at each B with g_k⁰abs(B) < ε₁ on Y.* Fix (U, J) and h⁰ = (g_0⁰, …, g_k⁰) ∈ (0, γ]^{k+1}.
   - {#B2.1.59} P^{(k)} is an explicit analytic function of g_k and g_kCB (RG1 (2.12)). The localisation in RG2 (1.10), (1.23) and (1.38) uses s-integrals over [0, 1] and Cauchy integrals over fixed circles, which preserve continuity at each configuration, the bounds being uniform in the history; so P^{(k)}'s terms in V_k(Y) (RG2 p.11 l.5–6) are continuous in g_k.
   - {#B2.1.60} {…} = Σ_Y V′_k(Y, U_{k+1}, B) (RG2 Lemma 1, (1.33)). Its configuration U_k(exp iB′V^{(k)}) depends on g_k and B only through g_kCB (B′ of RG1 (3.2), p.270 l.18), E_k depends only on g_0, …, g_{k−1} (#B2.37), and RG2 pp.4–9 use B only through B′ (p.4 l.24–25), so V′_k(Y) = W_Y(g_kB; g_0, …, g_{k−1}) (inferred, not printed).
     {#B2.1.60-1} W_Y is continuous in g_0, …, g_{k−1} at fixed g_kB, since E_k is so at each configuration by S_j for j < k and the continuity of β_j, and the localisation preserves this.
     {#B2.1.61} W_Y is holomorphic in g_kB on the polydisc abs(g_kB) < ε₁ on Y with RG2 (1.36)'s bound, uniform in the history (#B9.60, #B2.1.19-1). Cauchy's estimate makes W_Y Lipschitz in g_kB on the closed polydisc of radius ½(ε₁ + g_k⁰max_Y abs(B)) < ε₁, which contains g_kB for g_k near g_k⁰, uniformly in g_0, …, g_{k−1}; so V′_k(Y), hence V_k(Y), is continuous at h⁰.
3. {#B2.1.64} *(b) is continuous almost everywhere.* Fix B with |B(b)| ≠ ε₁/g_k⁰ for all b.
   {#B2.1.64-1} Then the indicators are constant for
   {#B2.1.65} g_k near g_k⁰.
   {#B2.1.65-1} The exceptional set is a finite union of sets {|B(b)| = t}, which are null for the nondegenerate
   {#B2.1.66} Gaussian measures in RG2 (2.14).
4. {#B2.1.67} *Dominated convergence.* The integrand of RG2 (2.14) has the majorant RG2 (2.15)–(2.25).
   {#B2.1.67-1} It is integrable and uniform
   {#B2.1.68} in the history and in (U, J).
   {#B2.1.68-1} At each B of step 3 the integrand is continuous at h⁰: near g_k⁰ it vanishes unless χ_{k,Y₀} = 1 at g_k⁰, and then step 2 applies, the V_k of RG2 (2.1) having Y ⊂ Y₀. So each term RG2 (2.14) is continuous in h at each (U, J).
5. {#B2.1.69} *Uniform convergence.* The sums over D, P and Z₀, and the polymer series RG2 (2.12)–(2.13), are dominated by
   {#B2.1.70} RG2 (2.26)–(2.41) uniformly in the history.
   {#B2.1.70-1} So E^{(k+1)}_fl(X; ·) is continuous: this is S_k.
   {#B2.1.70-2} The base case S_0 has
   {#B2.1.71} {…} = 0.
6. {#B2.1.72} *β.* β_{k+1}(h) − b_{k+1} = Λ(E^{(k+1)}_fl(·; h)).
   {#B2.1.72-1} Λ is a Cauchy integral over fixed circles followed by a sum over
   {#B2.1.73} X dominated as in Lemma 2.5, uniformly in h.
   {#B2.1.73-1} So β_{k+1} is continuous.
   {#B2.1.73-2} The infinite-volume limit RG1 (1.21) is
   {#B2.1.74} uniform by the same domination. ∎

{#B2.1.75} RG1 p.266 mentions a second cutoff, g_k/γ_k·ε₁ in place of ε₁, which makes E^{(j)} and β_j analytic in the couplings.
{#B2.1.76} Propositions 2.4 and 2.6 use the cutoff RG1 (2.9) as published and do not need it.

{#B2.1.77} *The cutoff of CRE.* CRE's fluctuation cutoff at step j is δ_j (#B0.5); its unit-scale form is
{#B2.1.79} δ_j/g_j = A₁(log g_j^{−2})^{p₀} (#B9.62–#B9.62-2).
{#B2.1.79-1} With this cutoff, Proposition 2.4
{#B2.1.80} reads |β_{k+1}(h) − b_{k+1}| ≤ C_ΛC₃δ_k ≤ C_ΛC₃γp₀(γ), which tends to 0 with γ: δ_k = (A₁/A₀)g_kp₀(g_k) ≤ g_kp₀(g_k) as A₁ < A₀ (#T3.27-0), and g ↦ gp₀(g) = A₀g(log g^{−2})^{p₀} (#T10.2) has derivative A₀(log g^{−2})^{p₀−1}(log g^{−2} − 2p₀) > 0 on (0, γ] once log γ^{−2} > 2p₀, so g_k ≤ γ gives g_kp₀(g_k) ≤ γp₀(γ), and γp₀(γ) → 0 as γ → 0.
{#B2.1.80-1} So no change of the cutoff is needed,
{#B2.1.81} only γ small, RG2's conditions of pp.18–19 holding at g_k on RG1's fixed domains (§0, *Input 3*, #B0.91–#B0.100).

{#B2.1.85} Proposition 2.6 holds with δ_j.
{#B2.1.85-1} In its step 3 the threshold ε₁/g_k becomes δ_k/g_k = A₁(log g_k^{−2})^{p₀}, which is
{#B2.1.86} continuous in g_k ∈ (0, γ].
{#B2.1.86-1} For B with |B(b)| ≠ δ_k/g_k at g_k = g_k⁰ for all b, the indicators are constant for g_k
{#B2.1.87} near g_k⁰, and the exceptional set is again a finite union of sets {|B(b)| = t}, null for the Gaussian measures of
{#B2.1.88} RG2 (2.14).
{#B2.1.88-1} In step 2, V′_k(Y) is holomorphic in g_kB on abs(g_kB) < δ_k (*Input 3*), the same function W_Y for every g_k, as RG2's construction does not involve the threshold, which enters only the domain (1.34) (inferred, not printed); since δ_k = (A₁/A₀)g_kp₀(g_k) increases with g_k (#B2.1.80) and g_k⁰max_Y abs(B) < δ_k at g_k⁰, step 2 runs with ε₁ replaced by the value of δ_k at a coupling below g_k⁰ and close to it. Steps 1 and 4–6 do not involve the threshold.

### 2.2 The Remainder at Order g_k² {#BS2.2}

{#B2.2.1} This section bounds the remainder R_{k+1}(h) := β_{k+1}(h) − b_{k+1} = Λ(E^{(k+1)}_fl(·; h)) (Proposition 2.4, step 1)
{#B2.2.2} by a multiple of g_k², for RG1's cutoff (2.9) with CRE's δ_k (#B0.5) in place of ε₁.
{#B2.2.2-1} Proposition 2.4
{#B2.2.3} gives O(δ_k) = O(g_kp₀(g_k)).
{#B2.2.3-1} Two facts give the extra power: the step integral is even in a complex coupling that
{#B2.2.4} replaces g_k in the exponent while the cutoff is held fixed, and the cutoff costs only a Gaussian tail.

{#B2.2.5} *Setting.*
- {#B2.2.6} Fix k and the history h, and put p := δ_k/g_k = A₁(log g_k^{−2})^{p₀}.
  {#B2.2.6-1} The cutoff of RG1 (2.9), p.266 runs over the bonds
  {#B2.2.7} b ∉ {b₀(c)}, where h_BD̃ = 0 (h_B of #T10.21), and depends on the Gaussian variable only through |B(b)| < p (RG2 (2.3), p.12).
- {#B2.2.8} For a threshold q and complex z, χ_q := ∏_b χ({|B(b)| < q}) over the same bonds.
  {#B2.2.8-1} W(z, B) := Σ_Y V_k(Y; z, B) is RG2's localised exponent (1.41) with g_k replaced by z: RG2's pieces of
  {#B2.2.9} P^{(k)} at z (Lemma 2.7, step 2), and Σ_Y V′_k(Y, (z/g_k)B) for the bracket {…} (step 1).
  {#B2.2.9-1} The cutoff is not changed.
- {#B2.2.10} E(z; q) := log ∫ χ_q exp W(z, B) dμ_{C^{(k)}}(B).
  {#B2.2.10-1} Then E^{(k+1)}_fl = E(g_k; p), by RG1 (2.13) and RG2 (1.41), used at real B.
- {#B2.2.11} *Parity.* In RG1 (2.12), p.268, every term of the exponent is a function of g_kCB,
  {#B2.2.12} or g_k^{−2} times such a function of order at least three (V and G₃ are of order at least three,
  {#B2.2.13} and D̃ starts at order two, RG1 p.267); G₃'s argument, printed g_kB (p.268 l.10) and g_kCB in the corrected transcript, is a function of g_kCB either way, B being the restriction of CB to the bonds b ∉ {b₀(c)} (p.268 l.2).
  {#B2.2.13-1} RG2's pieces keep this form with z for g_k, being functions of zCB with the prefactor z^{−2} or 1 (Lemma 2.7, step 2), and V′_k(Y, (z/g_k)B) is a function of zB; so W(−z, B) = W(z, −B).
  {#B2.2.13-2} The Gaussian measure is centred and χ_q is even,
  {#B2.2.14} so E(−z; q) = E(z; q) as functions of (U, J).

{#B2.2.15} **Lemma 2.7 (Complex Coupling).** Let ε* be such that A_χε* satisfies every condition on ε₁ listed in Proposition 2.4, step 4, where A_χ := (1 + 2¹²(M + 1)⁴)(1 + 1/(δ_{RG2}κ)) is used in Lemma 2.8 (#B2.2.73); ε* satisfies them too, as A_χ ≥ 1 and they are upper bounds (#B2.1.7). Let
{#B2.2.16} q_th be the constant fixed in Lemma 2.8.
{#B2.2.16-1} Let q ≥ q_th and |z|q < ε*.
{#B2.2.16-2} Then RG2's expansion (2.1)–(2.13) applies to
{#B2.2.17} E(z; q) = Σ_X E(X; z, q).
{#B2.2.17-1} Each E(X; z, q) is analytic in z on |z| < ε*/q and in (U, J) on U^c_{k+1}(X, α₀, α₁), whose U are taken as e^{iξA′}U with U G-valued (#B10.124-1).
{#B2.2.18} It satisfies RG2 (2.41) with ε* in place of ε₁: |E(X; z, q)| ≤ O(1)C₃ε* exp(−κd_{k+1}(X)).
{#B2.2.18-1} At z = g_k and q = p,
{#B2.2.19} E(X; z, q) is RG2's E^{(k+1)}(X).

{#B2.2.20} *Proof.*
1. {#B2.2.21} *The bracket.* {…} depends on (g_k, B) only through g_kCB (RG1 (2.12)), and RG2 (1.33) localises it at real B as Σ_Y V′_k(Y, B).
   {#B2.2.21-1} W's bracket term Σ_Y V′_k(Y, B̃), B̃ := (z/g_k)B, is this sum at the
   {#B2.2.22} real coupling g_k and the complex field B̃, and is RG1's bracket at z = g_k.
   {#B2.2.22-1} V′_k is holomorphic, with RG2 (1.36), on the complex polydisc |B̃| < ε*/g_k (RG2 (1.34) and #B9.60–#B9.61,
   {#B2.2.23} with ε* for ε₁; #BH.1's conditions on α₀, α₁ bound them by constants of d, L, G, RG1's average and β (#T10.28-4-1-1; #BH.3-2d), as RG1's own are, with M (p.275 l.28; p.264 l.40–41), so they are met when RG1's absolute α₀, α₁ (p.263 l.25) are chosen, before ε₁ (#B2.1.23)).
   {#B2.2.23-2} So V′_k(Y, (z/g_k)B) is analytic in z and satisfies RG2 (1.36) with ε*,
   {#B2.2.24} for |z||B| < ε* on Y.
2. {#B2.2.25} *The action terms.*
   - {#B2.2.26} RG2 builds the localisation of P^{(k)} from the pieces (1.38) of (1/g_k²)V(H₁B′).
     {#B2.2.26-1} These are functions of the unscaled fluctuation B′,
     {#B2.2.27} analytic for e^{16κ₁}|B′| ≤ a₁ (RG2 p.10 l.22; a₁ of #T10.28-4-5), and bounded by RG2 (1.39), p.10. "It can be done in the same way for all
     {#B2.2.28} terms in P^{(k)}" (RG2 p.11 l.5); these other terms depend on B also through g_kCB and D̃(g_kCB) (#BH.6-1).
   - {#B2.2.29} The factor g_k^{−2} of the pieces is removed by the second-order expansion RG2 (1.40) in B′, whose coefficients are bounded
     {#B2.2.30} by a multiple of |B′|.
   - {#B2.2.31} The coupling enters only through g_kCB and B′ = g_kCB − h_BD̃(g_kCB) (RG2 (1.19), p.6).
     {#B2.2.31-1} The bound (1.20) and the circle
     {#B2.2.32} (1.22) are stated through g_k|B| (RG2 pp.6–7).
   - {#B2.2.33} With z in place of g_k, every term is the same analytic function of zCB and B′ = zCB − h_BD̃(zCB), holomorphic in (z, B, A′, J) (BP_RG2_COMPLEX_B.md #BH.1-1 with #BH.6-0a for the (1.38) pieces as functions of B′, and #BH.1-2).
     {#B2.2.33-1} The prefactor
     {#B2.2.34} cancels by z^{−2}⟨Q̂B′, B′⟩ = ⟨Q̂B′/z, B′/z⟩, Q̂ being the quadratic form of (1.40), with coefficients ∫₀¹(1 − t)∂²(1.38)(tB′)dt.
     {#B2.2.34-1} The map B′/z = CB − z^{−1}h_BD̃(zCB) is analytic in z, also at z = 0, as D̃(zCB) is holomorphic in z with |D̃(zCB)| ≤ 4c_{C̃}|z|²|CB|² (#BH.1-2; #T10.28-3-1-3).
     {#B2.2.34-2} The other terms with the prefactor z^{−2} are of order ≥ 3 in zCB, so they are quadratic forms in CB whose coefficients are analytic in z, also at z = 0, and bounded by a multiple of |z||B| (#BH.6-5-1–#BH.6-5-1b); the terms without it satisfy (1.36) (#BH.6-5-2–#BH.6-5-2b).
   - {#B2.2.35} RG2 (1.20), with |z| in place of g_k (#BH.1-2), gives |B′| ≤ C₁′|z||B| < C₁′ε* and |B′/z| ≤ C₁′|B|.
     {#B2.2.35-1} So RG2 (1.43) and (1.36)
     {#B2.2.36} hold with ε* in place of ε₁ on |z||B| < ε*, and each V_k(Y; z, B) is analytic in z there.

   {#B2.2.37} RG2 states Lemmas 1–2 for real g_k only. Step 1 uses Lemma 1 at the real g_k (#BH.1). At complex coupling, V's (1.38) pieces are holomorphic in B′ (#BH.1-1, #BH.6-0a), composed with #BH.1-2's B′(z, B, A′) and bounded by #B2.2.34–#B2.2.35; the other terms of 𝐏^{(k)} are #BH.1-2 with #BH.6-5–#BH.6-5-2b, which carries RG2's localisation of them (p.11 l.5) to complex B (inferred, not printed).
3. {#B2.2.40} *The expansion.* RG2 section 2 (pp.12–21) uses the potentials only in two ways:
   - {#B2.2.41} through RG2 (1.42), (1.43), (1.36) and the cube count (1.28), as corrected in #BK.1 and #BK.6-2, in (2.18)–(2.20) on p.16;
   - {#B2.2.42} through the analyticity of V_k in (U, J) on U^c_{k+1}(Y, (1 + β)α₀, (1 + β)α₁, α₀) (RG2 (1.34)), used on p.15; β is RG1's enlargement factor of (3.16), #T10.28-4-1-1.
     {#B2.2.43} z does not enter the (U, J)-dependence, so this holds at every z.

   {#B2.2.44} It uses the cutoff only through the factor χ_{k,Y₀}χ^c_{k,P}, with values in [0, 1], and the tail bound RG2 (2.22).
   - {#B2.2.45} The potentials are evaluated only on the support of χ_{k,Y₀} (RG2 (2.3)).
     {#B2.2.45-1} There |z||B| < |z|q < ε*.
   - {#B2.2.46} The threshold enters RG2's conditions only as ε₁/g_k in (2.22), (2.31), (2.33) and (2.34).
     {#B2.2.46-1} With q in its place,
     {#B2.2.47} these are lower bounds on q, and they hold for q ≥ q_th.

   {#B2.2.48} So RG2 (2.1)–(2.41) hold with ε* in place of ε₁ and q in place of ε₁/g_k.
4. {#B2.2.49} *Analyticity.* Each term RG2 (2.14) is an integral of a function analytic in z.
   {#B2.2.49-1} It is dominated by RG2 (2.26),
   {#B2.2.50} uniformly on compact subsets of |z| < ε*/q, so it is analytic in z.
   {#B2.2.50-1} The sums (2.35)–(2.41) converge uniformly
   {#B2.2.51} there. ∎

{#B2.2.52} **Lemma 2.8 (Threshold Differences).** There is a constant q_th, depending on ε*, κ, M, γ₂ and the constants of RG2,
{#B2.2.53} with the following property. ε* is fixed first: the condition exp(−γ₂q²/20) ≤ ε₂ of RG2 (2.33) involves ε₂, which is
{#B2.2.54} proportional to ε* here.
{#B2.2.54-1} Let q_th ≤ q′ < q″ ≤ 2q′ and |z|q″ < ε*.
{#B2.2.54-2} Then E(z; q″) − E(z; q′) = Σ_X Δ(X; z), where each
{#B2.2.55} Δ(X; z) is analytic in z and in (U, J) on U^c_{k+1}(X, α₀, α₁).
{#B2.2.55-1} With constants C₄ and C₅ that do not depend on k,
{#B2.2.56} the history, q′, q″ or z, the following bounds hold.
- {#B2.2.57} RG2 (2.41) has the analogue |Δ(X; z)| ≤ C₄ exp(−γ₂q′²/4) exp(−κd_{k+1}(X)).
- {#B2.2.58} At z = 0, |E(X; 0, q)| ≤ C₅ exp(−γ₂q²/20) exp(−κd_{k+1}(X)) for q ≥ q_th.

{#B2.2.59} *Proof.*
1. {#B2.2.60} *Same index sets.* The families D, the sets P ⊂ Y₀^{c*}, and the domains Z₀ and Z of RG2 (2.1)–(2.13) do not depend
   {#B2.2.61} on the threshold (RG2 (2.1)–(2.3)).
   {#B2.2.61-1} So, term by term in (2.14), the activities at q″ and q′ differ only in the
   {#B2.2.62} factor χ_{k,Y₀}χ^c_{k,P}.
   {#B2.2.62-1} Write χ″ = χ″_{Y₀}χ″^c_P and χ′ = χ′_{Y₀}χ′^c_P for this factor at the two thresholds.
2. {#B2.2.63} *The difference of the cutoffs.* χ″ − χ′ = (χ″_{Y₀} − χ′_{Y₀})χ″^c_P + χ′_{Y₀}(χ″^c_P − χ′^c_P).
   - {#B2.2.64} The first term is nonzero only if some b ∈ Y₀ has |B(b)| ≥ q′.
   - {#B2.2.65} The second term is nonzero only if P ≠ ∅ and every b ∈ P has |B(b)| ≥ q′.
   - {#B2.2.66} By RG2 (2.3), p.12 l.14–19, χ_{k,Y₀^c} is the product over Y₀^{c*}, so χ_{k,Y₀} is the product over the other bonds of RG1 (2.9), p.266 l.46; let N_χ(Y₀) be their number. They and P are distinct bonds of Z₀ (F(Z₀, B) depends on B only through Z₀B, RG2 (2.5)).
     {#B2.2.66-1} Bound each indicator as in RG2 (2.22) by 1{|B(b)| ≥ q′} ≤ exp(−½γ₂q′² + ½γ₂|B(b)|²), the first term by a sum over its bond b with |B(b)| ≥ q′, and use ½(1 + |P|) ≥ ¼ + ¼|P| in the first term and ½|P| ≥ ¼ + ¼|P| in the second. This gives
     {#B2.2.67} |χ″ − χ′| ≤ (N_χ(Y₀) + 1) exp(−γ₂q′²/4) exp(−¼γ₂q′²|P| + ½γ₂‖Z₀B‖²).
3. {#B2.2.68} *RG2's chain.*
   - {#B2.2.69} The factor exp(½γ₂‖Z₀B‖²) is absorbed into the Gaussian as in RG2 (2.23), whose room α₅ contains γ₂ and
     {#B2.2.70} multiplies ‖Z₀B‖².
   - {#B2.2.71} The factor exp(−¼γ₂q′²|P|) runs the sums RG2 (2.31)–(2.34) with γ₂/2 in place of γ₂.
     {#B2.2.71-1} q_th is taken so large that
     {#B2.2.72} they hold.
   - {#B2.2.73} Each bond of χ_{k,Y₀} meets the closed set Y₀ and so has an endpoint in it (the cubes of π_k are (k+m)-blocks of side M = L^m centred at points of T_M^{(k+m)} (RG1 p.257 l.2–3, #T11.27-1); such a block is M k-blocks wide with M odd as L is (#T10.43), so its centre is a point of the unit lattice T_1^{(k)} (RG2 p.10 l.3) and its walls lie in hyperplanes of half-integer coordinates). A lattice point is an endpoint of 8 bonds, and a closed cube of side M contains at most (M + 1)⁴ lattice points.
     {#B2.2.73-1} So, by #BK.1 and Y₀ = ⋃_{Y∈𝐃}Y (RG2 (2.2)), N_χ(Y₀) ≤ 8(M + 1)⁴M^{−4}|Y₀| ≤ Σ_{Y∈𝐃}2¹²(M + 1)⁴(1 + d_k(Y)). With 1 + Σ_Y a_Y ≤ ∏_Y(1 + a_Y) for a_Y ≥ 0 and 1 + t ≤ (1 + 1/(δ_{RG2}κ))e^{δ_{RG2}κt} for t ≥ 0, N_χ(Y₀) + 1 ≤ ∏_{Y∈𝐃}A_χe^{δ_{RG2}κd_k(Y)}, A_χ of Lemma 2.7.
     {#B2.2.74} Each factor joins the factor of Y in RG2 (2.26), which becomes 2E₀A_χε*C₁α₄^{−1}M^q e^{C₂κ₁}exp(−(1 − 4δ_{RG2})κd_k(Y)). As A_χε* satisfies RG2's condition of p.18 l.9 (#B2.1.25, Lemma 2.7), (2.27) gives (2.28) with A_χε* for ε₁ and 1 − 5δ_{RG2} for 1 − 4δ_{RG2}.
   - {#B2.2.75} The rest of the chain RG2 (2.29)–(2.38) runs with A_χε* in place of ε₁ in ε₂ (p.19 l.2) and one more δ_{RG2} in every exponent.
     {#B2.2.75-1} It bounds H″(Z) − H′(Z) by RG2 (2.38), so modified, times O(1)exp(−γ₂q′²/4).
4. {#B2.2.76} *The polymer series.* In RG2 (2.13), ∏H″(Z_i) − ∏H′(Z_i) is a sum of n products, each with one factor H″ − H′.
   - {#B2.2.77} The bound RG2 (2.39)–(2.41) gives the claim, with one more δ_{RG2} in the exponent.
   - {#B2.2.78} With δ_{RG2} = (1 − 2L^{−1})/12 (#B2.1.16), (1 − 12δ_{RG2})½L = 1 absorbs it.
   - {#B2.2.79} In RG2 section 2, δ_{RG2} enters only the estimates (for instance, the radii (2.18) of Cauchy formulas).
     {#B2.2.79-1} So no activity
     {#B2.2.80} changes.
5. {#B2.2.81} *z = 0.* Every localized potential vanishes at z = 0.
   {#B2.2.81-1} In Lemma 1, H_k(s, 0) = 0 (RG2 (1.18), p.6), so the
   {#B2.2.82} integrand of RG2 (1.23) does not depend on t_□, and the Cauchy integral in t_□ is 0.
   {#B2.2.82-1} In the action terms B′ = 0 at z = 0, and the
   {#B2.2.83} coefficients of RG2 (1.40) are O(|B′|). The terms without the prefactor g_k^{−2}, Tr log(I − h_B(δD̃/δZ)) and log σ (RG1 p.268 l.9–10), vanish at B′ = 0 for every configuration: (δD̃/δZ)(0) = 0, as D̃ starts at order two, and the σ there is (σ_H/σ_H(0))(B′) (#T10.36-4), equal to 1 at B′ = 0.
   {#B2.2.83-1} So V_k(Y; 0, B) = 0 for every Y, and only D = ∅
   {#B2.2.84} contributes to RG2 (2.1).
   {#B2.2.84-1} Then Y₀ = ∅, and every nonzero term has P ≠ ∅.
   {#B2.2.85} RG2 (2.33) gives the factor exp(−(1/20)γ₂q²) per component in place of max{ε₂, …}, and RG2 (2.37)–(2.41) give
   {#B2.2.86} the bound with C₅. ∎

{#B2.2.87} **Proposition 2.9 (The Remainder at Order g_k²).** Take RG1's cutoff (2.9) with CRE's δ_k (#B0.5) in place of ε₁.
{#B2.2.88-1} There are constants C_rem, C_a, C′_rem, and γ > 0, independent of k and of the history, such that for every k
{#B2.2.89} and every history h ∈ 𝔖_γ (RG1 (2.13), CRE p.265):

  {#B2.2.90} (a) |β_{k+1}(h) − b_{k+1}| ≤ C_rem g_k²;
  {#B2.2.90-1} (b) with R(z; q) := Λ(E(·; z, q)) (#B2.2.10, Lemma 2.5), the limit a_{k+1}(h) := lim_{q→∞} ½∂_z²R(0; q) exists, |a_{k+1}(h)| ≤ C_a, and |β_{k+1}(h) − b_{k+1} − a_{k+1}(h)g_k²| ≤ C′_rem g_k⁴.

{#B2.2.91} *Proof.*
1. {#B2.2.92} *The function.* R(z; q) of (b) is defined for |z|q < ε*.
   - {#B2.2.93} Λ is a Cauchy integral followed by a sum dominated as in Lemma 2.5.
     {#B2.2.93-1} So, by Lemma 2.7, R(·; q) is analytic on
     {#B2.2.94} this disc, and |R(z; q)| ≤ C_Λ O(1)C₃ε* =: M₀ (RG2 (2.41)).
   - {#B2.2.95} R(·; q) is even, because each activity E(X; z, q) is even in z and Λ is linear.
     - {#B2.2.96} The parity of #B2.2.13-1 holds term by term in each V_k(Y; z, B).
       {#B2.2.96-1} Hence
       {#B2.2.97} V_k(Y; −z, −B) = V_k(Y; z, B).
     - {#B2.2.98} In RG2 (2.14), the change of variables (B, X) ↦ (−B, −X), X being RG2's auxiliary Gaussian field of dμ₀(X) there (p.15 l.13), not a polymer, leaves the centred measures, the coupling
       {#B2.2.99} exp(−⟨B, Γ_kX⟩), and χ_{k,Y₀}χ^c_{k,P} invariant.
     - {#B2.2.100} So each H(Z) is even in z, and by RG2 (2.13) so is each E(X; z, q).
   - {#B2.2.101} Proposition 2.4, step 1, gives β_{k+1}(h) − b_{k+1} = R(g_k; p).
2. {#B2.2.102} *Even functions.* Let f be even and analytic on |z| < r_f, with |f| ≤ M_f there.
   {#B2.2.102-1} Then φ(z) := (f(z) − f(0))/z² is
   {#B2.2.103} analytic.
   {#B2.2.103-1} By the maximum principle on the circles about 0 of radius below r_f, |f(g) − f(0)| ≤ 2M_fg²/r_f² for 0 ≤ g < r_f.
   {#B2.2.103-2} Here f is
   {#B2.2.104} R(·; q), and M_f is M₀ from RG2 (2.41) (step 4), or a bound from Lemma 2.8 (step 5).
3. {#B2.2.105} *Telescoping.* Let J be the least integer with 2^Jq_th ≥ p. Put p_j := 2^jq_th for 0 ≤ j < J and p_J := p, and
   {#B2.2.106} D_j(z) := R(z; p_{j+1}) − R(z; p_j).
   {#B2.2.106-1} Then
   {#B2.2.107} R(g_k; p) = R(0; p) + [R(g_k; q_th) − R(0; q_th)] + Σ_{j<J} [D_j(g_k) − D_j(0)].
4. {#B2.2.108} *The main term.* R(·; q_th) is even and analytic on |z| < ε*/q_th, and bounded by M₀ there (Lemma 2.7, RG2 (2.41)).
   {#B2.2.109} Step 2 gives |R(g_k; q_th) − R(0; q_th)| ≤ 2M₀q_th²g_k²/ε*².
5. {#B2.2.110} *The threshold terms.*
   - {#B2.2.111} D_j is even and analytic on |z| < ε*/p_{j+1}, and |D_j| ≤ C_ΛC₄ exp(−γ₂p_j²/4) there (Lemmas 2.5 and 2.8, from
     {#B2.2.112} RG2 (2.26)–(2.41)).
   - {#B2.2.113} g_k lies in this disc, because g_kp_{j+1} ≤ g_kp = δ_k < ε*.
   - {#B2.2.114} Step 2 and p_{j+1} ≤ 2p_j give |D_j(g_k) − D_j(0)| ≤ 8C_ΛC₄ p_j² exp(−γ₂p_j²/4) g_k²/ε*².
   - {#B2.2.115} Summed over j, the bound is 8C_ΛC₄Sg_k²/ε*², with S := Σ_{j≥0} 4^jq_th² exp(−γ₂4^jq_th²/4), which is finite.
6. {#B2.2.116} *The cutoff term.*
   - {#B2.2.117} R(0; p) = Λ(log μ_{C^{(k)}}(χ_p)).
     {#B2.2.117-1} Lemmas 2.5 and 2.8 (z = 0) give |R(0; p)| ≤ C_ΛC₅ exp(−γ₂p²/20).
   - {#B2.2.118} p = A₁(log g_k^{−2})^{p₀} (CRE p.265), with p₀ a positive integer (CRE p.244).
     {#B2.2.118-1} So (γ₂/20)p² ≥ log g_k^{−2} once
     {#B2.2.119} (γ₂/20)A₁²(log g_k^{−2})^{2p₀−1} ≥ 1, which holds for g_k ≤ γ small.
   - {#B2.2.120} Then |R(0; p)| ≤ C_ΛC₅g_k².
7. {#B2.2.121} *Constants.*
   - {#B2.2.122} C_rem := 2M₀q_th²/ε*² + 8C_ΛC₄S/ε*² + C_ΛC₅.
   - {#B2.2.123} The constants are fixed in this order: ε*, then q_th, then γ. γ is taken so small that, for g ≤ γ,
     {#B2.2.124} A₁(log g^{−2})^{p₀} ≥ q_th, gA₁(log g^{−2})^{p₀} < ε*, and step 6 holds (CRE pp.244, 246, 265).
   - {#B2.2.125} None of these depends on k or on the history. This proves (a).
8. {#B2.2.125-1} *Order g_k⁴.* Let f be as in step 2. Its Taylor coefficients satisfy |c_{2n}| ≤ M_f/r_f^{2n} (Cauchy), so |½f″(0)| ≤ M_f/r_f², and for 0 ≤ g ≤ r_f/2, |f(g) − f(0) − ½f″(0)g²| ≤ M_f(g/r_f)⁴/(1 − (g/r_f)²) ≤ (4/3)M_fg⁴/r_f⁴.
   - {#B2.2.125-2} *The limit.* Put q_j := 2^jq_th for all j ≥ 0 (so q_j = p_j for j < J). Lemma 2.8 needs only q_th ≤ q′ < q″ ≤ 2q′ and |z|q″ < ε*, so for every j ≥ 0 and every q ∈ (q_j, q_{j+1}], R(·; q) − R(·; q_j) has the bound of step 5 on |z| < ε*/q_{j+1}, and its ½∂_z² at 0 is at most 4C_ΛC₄q_j²exp(−γ₂q_j²/4)/ε*². These bounds are summable (S of step 5 is finite), so the limit a_{k+1}(h) exists, and |a_{k+1}(h)| ≤ C_a := M₀q_th²/ε*² + 4C_ΛC₄S/ε*².
   - {#B2.2.125-3} *The expansion.* Take γ so small that g_kq_th ≤ ε*/2 and δ_k ≤ ε*/2, so that g_k ≤ r_f/2 for R(·; q_th) (r_f = ε*/q_th, M_f = M₀) and for each D_j of step 3, j < J, with step 3's p_J = p (r_f = ε*/p_{j+1}, M_f = C_ΛC₄exp(−γ₂p_j²/4); g_kp_{j+1} ≤ g_kp = δ_k). In step 3, ½∂_z²R(0; p) = ½∂_z²R(0; q_th) + Σ_{j<J}½D_j″(0), so the bound above gives |β_{k+1}(h) − b_{k+1} − R(0; p) − ½∂_z²R(0; p)g_k²| ≤ (4/3)(M₀q_th⁴ + 16C_ΛC₄S₄)g_k⁴/ε*⁴, with S₄ := Σ_{j≥0}q_j⁴exp(−γ₂q_j²/4) < ∞.
   - {#B2.2.125-4} *The tail and the cutoff term.* Going from p to a_{k+1}(h) along p, 2^Jq_th, 2^{J+1}q_th, … (each at most twice the previous, and 2^Jq_th < 2p), the bound of the limit step, with q′ running through these points, bounds the jumps of ½∂_z²R(0; ·) by T_n := 4C_ΛC₄x_nexp(−γ₂x_n/4)/ε*², x_0 := p², x_n := 4^{n−1}(2^Jq_th)² for n ≥ 1.
     {#B2.2.125-4a} Once γ₂p²/4 ≥ 1, T_1 ≤ T_0, as x ↦ xexp(−γ₂x/4) decreases for γ₂x/4 ≥ 1, and T_{n+1}/T_n = 4exp(−3γ₂x_n/4) ≤ 4e^{−3} < ½ for n ≥ 1; so |½∂_z²R(0; p) − a_{k+1}(h)| ≤ T_0 + 2T_1 ≤ 3T_0 = 12C_ΛC₄p²exp(−γ₂p²/4)/ε*². With p = A₁(log g_k^{−2})^{p₀} and 2p₀ > 1, this is at most g_k², and |R(0; p)| ≤ C_ΛC₅exp(−γ₂p²/20) ≤ g_k⁴ (step 6), for γ small.
   - {#B2.2.125-5} So (b) holds with C′_rem := 2 + (4/3)(M₀q_th⁴ + 16C_ΛC₄S₄)/ε*⁴. a_{k+1}(h) is a limit in q, so it does not depend on the cutoff of step k; it depends on the history only through the input E_k of step k. ∎

{#B2.2.126} In the coupling flow RG1 (2.15) this reads 1/g_{k+1}² = 1/g_k² − b_{k+1} + O(g_k²), uniformly in the history.

{#B2.2.127} *Inputs.*
- {#B2.2.128} VAR (189), through Lemma 2.5 as in Proposition 2.4, proved in balaban_proofs/BP_VAR_189.md (not yet through review; sidecar node VAR_189).
- {#B2.2.129} RG2 Lemmas 1–2 and section 2, RG2's sketch on p.11 l.5 (§0, input 2, #B0.33; Lemma 2.7, step 2), RG1 (2.12), and CRE pp.244–246 and (2.4), as cited.
- {#B2.2.135} The bound RG1 (1.18) and the analyticity of the step terms in (U, J) on RG1's fixed domains, from RG1 Theorem 3
  {#B2.2.136} run with CRE's cutoffs δ_j (#B0.5; the remark after Proposition 2.6; the transfer is derived in §0,
  {#B2.2.137} *Input 3*).
- {#B2.2.130} Bałaban does not print the parity, the complex-coupling transfer (Lemma 2.7), the threshold differences
  {#B2.2.131} (Lemma 2.8), or the telescoping; their proofs are in this section.

{#B2.2.138} *CRE's Construction as a Function of the History.* CRE's coefficient β_{k+1}(g_k) (CRE p.279) is built from the
{#B2.2.139} whole-lattice term E^{(k+1)} ((3.57), p.281; p.278: the localised terms "do not depend on Λ_{k+1}"), which uses the
{#B2.2.140} cutoff δ_k and the input R′_k.
{#B2.2.140-1} The next coupling g_{k+1} enters step k only through the localisation and the
{#B2.2.141} analyticity statements of the new density (the threshold ε_{k+1} of CRE (3.2), p.265, (3.8), p.266, and p.268; the
{#B2.2.142} scale R_{k+1} of p.264; and the domains (2.28) at scale k+1).
{#B2.2.142-1} Continuity in the history is not known for this construction, because its integer
{#B2.2.143} parameters jump with the couplings; its thresholds and domains move with them:
- {#B2.2.144} R_j (CRE (2.5)), k₁ (CRE p.270), N₀ (LFR1 p.179), and the depth N of the R-operation are integers that jump with the
  {#B2.2.145} couplings.
  {#B2.2.145-1} N is "to the positive power of log g_k^{−2}" (LFR1 p.198), N ≥ (ν/log L) log log g_k^{−2} (LFR2 p.363),
  {#B2.2.146} and LFR2 p.384 takes N = R_j (the two exponents ν: #B9.63–#B9.64-1).
  {#B2.2.146-1} Since R′_k = Σ_{j≤k₁}R^{(j)}
  {#B2.2.147} (CRE p.271), a jump of k₁ moves a whole R-term between R′ and R″, and only the R′-part enters β_{k+1} (#B0.147).
- {#B2.2.148} The thresholds ε_j, δ_j, and δ′_j (#T3.27, #B0.5, #T3.40), the threshold 2ε_kη² of LFR1 (1.75), and the supports of the bump functions of the
  {#B2.2.149} changes of variables CRE (1.22) (pp.252, 269) move with the couplings, so the characteristic functions under the
  {#B2.2.150} integrals depend on the history.

{#B2.2.151} The construction below evaluates every such parameter at a value fixed by the target (K, g).
{#B2.2.151-1} Then no characteristic
{#B2.2.152} function depends on the history, and the couplings enter only through the densities.

{#B2.2.153} *The Class of Tubes.* A tube is given by constants 0 < b ≤ b′ and C ≥ 0 and a target (K, g), with
  {#B2.2.154} c ln L ≤ b ≤ b′ ≤ min((3/2)b, 3c ln L),  t := g^{−2} ≥ max(γ^{−2} + C, 4C/β₀), so that 8C ≤ t (β₀ < ½),
{#B2.2.155} with β₀ ≤ √2 − 1 the constant of CRE (2.6) (*Lower bounds from the action*, Lemma 2.10, step 6).
{#B2.2.155-1} Put ρ_γ := max(b′/b, (t + C)/(t − 2C)); on the class ρ_γ ≤ 3/2.
{#B2.2.155-2} Put ρ̄ := 15/8,
{#B2.2.156} the factor of the action comparison on the class (*Histories that are not flows*).
{#B2.2.157} For 0 ≤ k ≤ K put
  {#B2.2.158} ℓ_k := t + b(K−k) − C,  u_k := t + b′(K−k) + C,  T_k := [ℓ_k, u_k],  ĝ_k := u_k^{−1/2},
{#B2.2.159} and let H_k be the set of (x_0, …, x_k) with x_j ∈ T_j for j ≤ k and b(n−m) − C ≤ x_m − x_n ≤ b′(n−m) + C for
{#B2.2.160} 0 ≤ m < n ≤ k.
{#B2.2.160-1} H_k is closed and convex.
{#B2.2.160-2} It contains x_j := t + ½(b + b′)(K−j), and the sequence (u_j) lies in H_K.
{#B2.2.161} The constants of Lemma 2.10 and of Propositions 2.4, 2.9, and 2.11 below (C_Λ, C₃, C_rem, C′, C_Σ, K_V, and C_R) are uniform
{#B2.2.162} over the class, and so is the smallness of γ required in Lemma 2.10, because they depend on the tube only through
{#B2.2.163} the bounds c ln L ≤ b ≤ b′ ≤ 3c ln L, C ≤ (β₀/4)t, ρ_γ ≤ 3/2, and the action comparison with ρ̄ (for instance, Lemma 2.10, step 2, needs
{#B2.2.164} (b′ + C)/(t − C) ≤ β₀, and step 3 needs (1 + log(1 + b′)/log γ^{−2})^r ≤ 1 + 1/L); C is not bounded by a constant (Proposition 10.3 uses C ∝ K).

{#B2.2.165} *The Tube of a Target.* Put δ′ := δ + C_Rγ^{κ₀−4}, with δ = C_ΛC₃γp₀(γ) the bound of Proposition 2.4 and C_R that of
{#B2.2.166} Proposition 2.11, both with the constants of the class.
{#B2.2.166-1} For γ small, δ′ ≤ (2/5)c ln L. Put b := 2c ln L − δ′,
{#B2.2.167} b′ := 2c ln L + δ′, and C := C₀ (Remark 2.3).
{#B2.2.167-1} Then c ln L ≤ b ≤ b′ ≤ 3c ln L and b′/b ≤ 3/2, and
{#B2.2.168} t ≥ γ′^{−2} = γ^{−2} + C ≥ 4C/β₀ for γ small, so the tube of the target (K, g) lies in the class.
{#B2.2.168-1} For it ρ_γ → 1 as
{#B2.2.169} γ → 0.
{#B2.2.169-1} These constants do not depend on K or g, and the
{#B2.2.170} definition is not circular, because C_R and δ are fixed on the class before b and b′ are.

{#B2.2.171} The tube construction of a tube of the class (for the tube of the target (K, g), the tube construction for (K, g)) is CRE's construction in which every parameter that CRE, LFR1, and LFR2 define from
{#B2.2.172} a coupling g_j is defined from ĝ_j = u_j^{−1/2} instead:
- {#B2.2.173} R_j^T is the smallest power of L with R_j^T ≥ (log ĝ_j^{−2})^r, the depth is N_k^T := R_k^T, and k₁ and N₀ are
  {#B2.2.174} defined from R^T by the formulas of CRE p.270 and LFR1 p.179;
- {#B2.2.175} ε_j^T := ĝ_jp₀(ĝ_j), δ_j^T := (A₁/A₀)ε_j^T, the threshold of LFR1 (1.75) is 2ε_k^Tη², and the domains of
  {#B2.2.176} CRE (2.28) are α^T_{0,j} := ĝ_jC^α_0(log ĝ_j^{−2})^{q₀} and α^T_{1,j} := ĝ_jC^α_1(log ĝ_j^{−2})^{q₁}, where C^α_0
  {#B2.2.177} and C^α_1 are the constants that CRE (2.28) prints as C₀ and C₁ (renamed here, since C₀ is the constant of
  {#B2.2.178} Theorem 8.1 and C₁ the constant of RG2 Lemma 1, #T10.28-3);
- {#B2.2.179} every other threshold, every factor p₀, p₁, q₀, or q₁ in a threshold, a scale, or a domain, and the supports of the
  {#B2.2.180} bump functions of CRE (1.22) are taken at ĝ_j.

{#B2.2.181} The factors g_j^{±1} that convert between scaled and unscaled fields stay the couplings of the history.
{#B2.2.181-1} So the
{#B2.2.182} thresholds act on unscaled fields (the plaquette variables U(∂p) and the fluctuation fields g_kA_k) with values fixed
{#B2.2.183} by the target.
- {#B2.2.184} *LFR1 (1.55).* LFR1 (1.55), p.188, prints χ′^{(j)} = χ({|B_j(b)| < δ′_j}) for the scaled variable B_j, with
  {#B2.2.185} δ′_j and p₁(g) of #T3.40 (LFR1 p.183).
  {#B2.2.185-1} LFR2 prints no large-field factor for the components that LFR1 p.188 excludes
  {#B2.2.186} from Z with 1 − χ′^{(j)}: the factors of the preparatory steps on LFR2 pp.380–383 are those of 1 − χ_j^{(n)}, of
  {#B2.2.187} 1 − χ′_m of LFR1 (1.27), of the second function of the decomposition LFR1 (1.28) ("yields the same final factor",
  {#B2.2.188} p.381), of 1 − χ_{j,Λ}, and of 1 − χ′ of LFR1 (1.82).
  {#B2.2.188-1} The construction here takes
  {#B2.2.189} χ′^{(j)} := χ({|g_jB_j(b)| < δ′_j}), with the threshold on the unscaled field; the identity
  {#B2.2.190} 1 = χ′^{(j)} + (1 − χ′^{(j)}) holds for every threshold.
  {#B2.2.190-1} The same choice is made for CRE's fluctuation threshold:
  {#B2.2.191} CRE (3.16), p.268, prints χ({sup|A_k(b)| < δ_k}) after the scaling A′_k = g_kA_k (CRE p.267), and its threshold is
  {#B2.2.192} read at field scale (#B9.62–#B9.62-2), the value that LFR2's factor exp(−γ₀(1/g_j²)δ_j²(LM₂R_j)^{−d}|R_j|) (p.380 l.43–45)
  {#B2.2.193} for it carries.
  {#B2.2.193-1} LFR1 (1.9), p.178, prints the fluctuation threshold as |A_j(b)| < g_j^{−1}δ_j, and LFR1 (1.82),
  {#B2.2.194} p.196, prints δ′_k on the unscaled field B′, V′ = exp iB′.
  {#B2.2.194-1} Four steps use the threshold.
  - {#B2.2.195} *The expansion.* Since δ_j = g_j(A₁/A₀)p₀(g_j) (#B0.5), δ′_j/δ_j = A₀p₁(g_j)/p₀(g_j) < 1 for g small, as
    {#B2.2.196} p₁ < p₀.
    {#B2.2.196-1} The bound |B′_j| < 6δ′_j, B′_j = g_jB_j, holds on the whole integration domain by (1.54), p.187, and LFR1
    {#B2.2.197} p.187 expands the action on it, so the expansion holds on both kinds of components.
    {#B2.2.197-1} The small-field components,
    {#B2.2.198} |g_jB_j| < δ′_j, lie in the small-field domain |g_jA| < δ_j of CRE (3.25), p.270, read as in #B9.62.
  - {#B2.2.199} *The removal of χ′_j.* The small-field integral of LFR1 p.188 carries χ′^{(j)} but not χ′_j of (1.27),
    {#B2.2.200} |V_j(V^{(j)}_Z)^{−1} − 1| < 2δ′_j. On the small-field components χ′_j = 1: V_j(V^{(j)}_Z)^{−1} =
    {#B2.2.201} V′_jV^{(j)}(V^{(j)}_Z)^{−1} with V′_j = exp ig_jB_j by (1.53), and V^{(j)}(V^{(j)}_Z)^{−1} = exp i𝐇^{(j)}_Z by (1.58),
    {#B2.2.202} with 𝐇^{(j)}_Z bounded by O(1)exp(−R_j)ε_j, "smaller than any positive power of g_j" (p.188).
    {#B2.2.202-1} So
    {#B2.2.203} |V_j(V^{(j)}_Z)^{−1} − 1| ≤ |g_jB_j| + O(1)exp(−R_j)ε_j < δ′_j + O(1)exp(−R_j)ε_j < 2δ′_j for g small.
  - {#B2.2.204} *The Gaussian tails.* LFR1 p.189 treats the small-field integral (1.60) as "of the same type as the integral
    {#B2.2.205} studied in Sect. 3 [III]", and that analysis needs the lower bounds on the unit-scale cutoff of §0, *Input 3*.
    {#B2.2.206} Here the unit-scale cutoff is δ′_j/g_j = A₁(log g_j^{−2})^{p₁}.
    {#B2.2.206-1} The condition of RG2 p.19 becomes
    {#B2.2.207} exp(−γ₂A₁²(log g_j^{−2})^{2p₁}/20) ≤ c_εδ′_j, which holds for g_j ≤ γ small because 2p₁ > 1: LFR2 p.383 assumes
    {#B2.2.208} 2p₁ − (d+5)r₀ > p₀, and p₀ > 2 (Lemma 2.10, step 4), so 2p₁ > p₀ > 2.
    {#B2.2.208-1} The condition of RG2 p.18 holds once
    {#B2.2.209} γ₂A₁²(log γ^{−2})^{2p₁} ≥ 80κ, and the other lower bounds of *Input 3* hold because δ′_j/g_j ≥ A₁(log γ^{−2})^{p₁}
    {#B2.2.210} tends to ∞ as γ → 0.
  - {#B2.2.211} *The large-field factor.* On the large-field components some bond b has |g_jB_j(b)| ≥ δ′_j, that is
    {#B2.2.212} |B_j(b)| ≥ g_j^{−1}δ′_j = A₁p₁(g_j). The B_j-integral of LFR1 p.188 has the quadratic form ⟨B_j, C^*Δ^{(j)}CB_j⟩ of
    {#B2.2.213} CRE's fluctuation integrals.
    {#B2.2.213-1} For the threshold of CRE (3.16), LFR2 p.380 obtains the factor above "by the same
    {#B2.2.214} positivity bound for the quadratic form", a lower bound of the kind of PRT2 (2.157), p.250,
    {#B2.2.215} ⟨B′, C^*Δ_kCB′⟩ ≥ γ′₀‖B′‖² with γ′₀ = (γ₀/12d²)L^{−d−1}.
    {#B2.2.215-1} The same bound, with δ′_j in place of δ_j and the single
    {#B2.2.216} bond b in place of the cubes of R_j, gives the factor exp(−c_lf(1/g_j²)δ′_j²) = exp(−c_lfA₁²p₁²(g_j)) for each such
    {#B2.2.217} component, with c_lf > 0 depending on d and L only.
    {#B2.2.217-1} The normalisation of the Gaussian integral on the component gives
    {#B2.2.218} a constant e^{O(1)} per variable, of the kind that LFR2 p.380 charges to the volume ("every large field domain Z_j
    {#B2.2.219} contributes the constant O(1)log g_j^{−2}|Z_j|").
    {#B2.2.219-1} LFR2 p.383 assumes 2p₁ − (d+5)r₀ > p₀, so 2p₁ > p₀, and the
    {#B2.2.220} factor is at most exp(−p₀(g_j)) for g small, the bound to which LFR2 p.383 reduces the factors of the preparatory
    {#B2.2.221} steps.

  {#B2.2.222} In the tube construction χ′^{(j)} is χ({|g_jB_j(b)| < δ′^T_j}).
  {#B2.2.222-1} The four steps hold there with δ′^T_j: the
  {#B2.2.223} comparison δ′^T_j < δ^T_j and the removal of χ′_j are relations at ĝ_j, the unit-scale cutoff is
  {#B2.2.224} δ′^T_j/g_j ≥ ρ̄^{−1/2}A₁(log ĝ_j^{−2})^{p₁} by Lemma 2.10 (a), and the large-field factor enters Lemma 2.10, step 6,
  {#B2.2.225} with the other lower bounds from the action.
- {#B2.2.226} *Histories that are not flows.* CRE (2.24), p.259, defines the position-dependent couplings by
  {#B2.2.227} 1/g²_{j−1}(x) = 1/g_j²(x) + β_j(g_{j−1})φ_j(x), with φ_j ∈ C_0^∞(Λ_j), φ_j = 1 on Λ_j^{∼−1} (p.259 l.20–21), and g_j²(x) = g_j² on the last domain; this holds along a flow.
  {#B2.2.227-1} For an
  {#B2.2.228} arbitrary history h = (g_0, …, g_k) the tube construction uses the same relation counted from the top:
    {#B2.2.229} 1/g_k²(x) := 1/g_k² + Σ_{j=1}^{k} β^T_j(h_{j−1})(1 − φ_j(x)),
  {#B2.2.230} which agrees with (2.24) along a flow (by (2.24) and the flow, the difference 1/g_j²(x) − 1/g_j² decreases by
  {#B2.2.231} β_j(1 − φ_j(x)) from j to j − 1, and it vanishes at j = 0).
  {#B2.2.231-1} The density of step k is CRE's (2.18) with A_k(1/g_k²(·), U_k) and the
  {#B2.2.232} terms E_k (CRE's regular part 𝐄_k), 𝐑_k (the R-terms) and 𝐁_k (the boundary terms) of A_k (CRE p.258 l.50; p.259 l.4–8, l.8–10 and l.10–11) produced by the steps 0, …, k−1 of the history; this is RG1's convention, in which the
  {#B2.2.233} Wilson term carries the current coupling and the earlier steps enter through the effective action (Remark 2.3,
  {#B2.2.234} *What β is*).
  {#B2.2.234-1} The formula involves the history only through the β^T_j, and on H_j each β^T_j satisfies the same
  {#B2.2.235} per-step bounds as along a flow (Proposition 2.11, *Consequence*).
  {#B2.2.235-1} So every bound that CRE, LFR1, and LFR2 derive
  {#B2.2.236} for g_k(x) from bounds on the β_j, such as 1/(g″_k(·))² − 1/g_k² = O(N) (LFR2 p.366), holds.
  {#B2.2.236-1} Where they use the
  {#B2.2.237} flow identity 1/g_k²(x) = 1/g_m² for x ∈ Λ_m^{∼−1} outside Λ_{m+1}, {Λ_j} being CRE's localisation domains (2.1) (p.254 l.50), the top-down value is
  {#B2.2.238} 1/g_k² + Σ_{j=m+1}^{k}β^T_j: the domains are nested (CRE (2.1), p.254), so x ∉ Λ_j and φ_j(x) = 0 for j > m, and
  {#B2.2.239} x ∈ Λ_m^{∼−1} ⊂ Λ_j^{∼−1} (Λ_m ⊂ Λ_j, and the operation ∼ removes cubes of size L^jMR^T_j at scale j, CRE
  {#B2.2.240} pp.245, 256, which are no larger than those of scale m, since L^jR^T_j ≤ L^mR^T_m for j ≤ m by Lemma 2.10 (c)) and
  {#B2.2.241} φ_j(x) = 1 for j ≤ m (#B2.2.227).
  {#B2.2.241-1} On the
  {#B2.2.242} boundary layers the formula is CRE's own expression Σ_jβ_j(1 − φ_j(x)) with β^T_j in place of the flow's β_j, so
  {#B2.2.243} CRE's treatment of the layers applies with the same bounds.
  {#B2.2.243-1} The coefficient y of the Wilson action at such x,
  {#B2.2.244} whether 1/g_m² or the top-down value, is compared with the tube coupling u_m = ĝ_m^{−2} of scale m.
  {#B2.2.244-1} For y = x_m,
  {#B2.2.245} u_m/x_m ≤ ρ_γ by Lemma 2.10, step 1.
  {#B2.2.245-1} For the top-down value y = x_k + Σ_{j=m+1}^{k}β^T_j, Proposition 2.11 with the
  {#B2.2.246} class constants gives |β^T_j − b_j| ≤ δ′ ≤ (2/5)c ln L at the depths below k (as in its *Consequence*), and (W)
  {#B2.2.247} for the b_j (Remark 2.3) gives Σ_{j=m+1}^{k}b_j ≥ 2c ln L(k−m) − C₀.
  {#B2.2.247-1} With x_k ≥ ℓ_k = t + b(K−k) − C,
    {#B2.2.248} y ≥ t − C − C₀ + b(K−k) + (8/5)c ln L(k−m),  u_m ≤ t + C + b′(K−k) + b′(k−m),
  {#B2.2.249} and b′ ≤ (3/2)b, b′ ≤ 3c ln L, 8C ≤ t, and t ≥ γ^{−2} give, by the mediant inequality,
    {#B2.2.250} u_m/y ≤ max(3/2, 15/8, (t + C)/(t − C − C₀)) = ρ̄ for γ small, since (9/8)/(7/8 − C₀γ²) ≤ 15/8.
  {#B2.2.251} For the tube of a target the windows of H_k contain those of Remark 2.3, so the top-down value lies in
  {#B2.2.252} [x_k + b(k−m) − C, x_k + b′(k−m) + C], and u_m/y ≤ (t + b′(K−m) + C)/(t + b(K−m) − 2C) ≤ ρ_γ.
  {#B2.2.252-1} These are the
  {#B2.2.253} comparisons that the lower bounds from the action use (Lemma 2.10, step 6).
  {#B2.2.253-1} The same coefficient enters the
  {#B2.2.254} Gaussian densities of the fluctuation fields at scale m.
  {#B2.2.255} The order of the argument is a joint induction on k: the convention at depth k uses the bounds on β^T_j for j ≤ k
  {#B2.2.256} (Proposition 2.11, *Consequence*, at depths below k), and those use Lemma 2.10 at depths below k.
- {#B2.2.257} *Where the history enters.* The couplings g_j of the history enter only through the densities: the Wilson action
  {#B2.2.258} with the couplings g_k(x); the counterterms β^T_j; the Gaussian densities of the unscaled fluctuation fields, with
  {#B2.2.259} covariance proportional to g_j²; the axial gauge-fixing weight exp[−(1/g_k²)G] and its normaliser z(g_k, ε^T_k)
  {#B2.2.260} (CRE (1.5)–(1.7), p.247, used at scale k "as in (1.5), with V_k, ε_k, g_k instead of U, ε₀, g₀", p.265;
  {#B2.2.261} LFR1 (1.5)–(1.6)); the scaling Jacobians d(𝔤) log g_k|·| (CRE p.267; LFR2 (1.10); UV3
  {#B2.2.262} p.261); the R-operation densities and normalisers of LFR1 (1.100), p.201; and the terms of the effective action of
  {#B2.2.263} the earlier steps.

{#B2.2.264} **Lemma 2.10 (The Tube Construction Is Admissible).** Let γ be small, take a tube of the class, and let
{#B2.2.265} ρ_γ = max(b′/b, (t+C)/(t−2C)) ≤ 3/2 be as in *The Class of Tubes* (ρ_γ → 1 as γ → 0 for the tube of a target).
{#B2.2.265-1} For
{#B2.2.266} every (x_0, …, x_k) ∈ H_k, with g_j := x_j^{−1/2}:
- {#B2.2.267} (a) ρ_γ^{−1/2} ≤ ĝ_j/g_j ≤ 1 and log g_j^{−2} ≤ log ĝ_j^{−2} ≤ log g_j^{−2} + log ρ_γ;
- {#B2.2.268} (b) CRE (2.6) holds, with β′ := b′ + C;
- {#B2.2.269} (c) (log g_j^{−2})^r ≤ R_j^T ≤ 2L(log g_j^{−2})^r, R^T_{j+1} ∈ {R^T_j, L^{−1}R^T_j}, and CRE (2.9) holds for R^T;
- {#B2.2.270} (d) N_k^T satisfies the conditions of LFR1 p.198 and LFR2 p.363, and N_k^T > N₀;
- {#B2.2.271} (e) ε_j^T ≤ ε_j, and ε_j^T/g_j, δ_j^T/g_j, and α^T_{i,j}/g_j lie between ρ_γ^{−1/2} and (1 + log ρ_γ/log γ^{−2})^{p}
  {#B2.2.272} times CRE's values at g_j, with p the exponent of the logarithm in each.

{#B2.2.273} The estimates of CRE, LFR1, and LFR2 hold for the tube construction on the histories of H_k, with changed constants,
{#B2.2.274} and Propositions 2.4, 2.6, and 2.9 hold for RG1's construction run with the cutoffs δ_j^T.

{#B2.2.275} *Proof.*
1. {#B2.2.276} *(a).* x_j ≤ u_j, so ĝ_j ≤ g_j.
   {#B2.2.276-1} By the mediant inequality u_j/ℓ_j ≤ ρ_γ, so u_j ≤ ρ_γx_j.
2. {#B2.2.277} *(b).* For m < n, x_m ≤ x_n + b′(n−m) + C ≤ x_n + β′(n−m), which is the first inequality of (2.6), and
   {#B2.2.278} (1 + g_n²β′(n−m))^{1/2} ≤ (1 + β₀)(n−m)^{1/2} once g_n²β′ ≤ (1+β₀)² − 1. This holds: g_n² ≤ 1/ℓ_n ≤ 1/(t − C), t ≥ γ^{−2}, and C ≤ (β₀/4)t give g_n²β′ ≤ (b′γ² + β₀/4)/(1 − β₀/4) ≤ β₀ for γ small.
   {#B2.2.278-1} And x_n ≤ x_m + C ≤ (1 + β₀/3)x_m, since x_m ≥ t − C, so g_m ≤ (1 + β₀)g_n.
3. {#B2.2.280} *(c).* R_j^T ≥ (log ĝ_j^{−2})^r ≥ (log g_j^{−2})^r, and R_j^T < L(log ĝ_j^{−2})^r ≤ 2L(log g_j^{−2})^r by (a).
   {#B2.2.280-1} The
   {#B2.2.281} sequence u_j decreases, so R^T_{j+1} ≤ R^T_j, and u_j = u_{j+1} + b′ ≤ (1 + b′γ²)u_{j+1} gives
   {#B2.2.282} R^T_j/R^T_{j+1} < L(1 + b′γ²/log γ^{−2})^r < L², so the ratio, a power of L, is 1 or L. For the second inequality
   {#B2.2.283} of (2.9) let s := n − m and λ := log γ^{−2}.
   {#B2.2.283-1} Then R^T_m/R^T_n < L(log u_m/log u_n)^r and
   {#B2.2.284} u_m ≤ (1 + b′sγ²)u_n, so R^T_m/R^T_n < L(1 + log(1 + b′sγ²)/λ)^r.
   - {#B2.2.285} For s ≤ γ^{−2} the bracket is at most (1 + log(1 + b′)/λ)^r ≤ 1 + 1/L for γ small.
   - {#B2.2.286} For s > γ^{−2} put y := log s > λ.
     {#B2.2.286-1} Then 1 + b′sγ² ≤ (1 + b′)sγ², and the bracket is at most
     {#B2.2.287} ((y + log(1 + b′))/λ)^r.
     {#B2.2.287-1} This is at most 1 + 1/L at y = λ, and its logarithmic derivative in y is at most
     {#B2.2.288} r/λ ≤ β₀ for γ small, so it is at most (1 + 1/L)s^{β₀}.
   {#B2.2.289} In both cases R^T_m ≤ (L+1)s^{β₀}R^T_n.
4. {#B2.2.290} *(d).* LFR1 p.198 requires "N ≤ O(1)(log g_k^{−2})^ν" and N sufficiently large; LFR2 p.363 requires
   {#B2.2.291} N ≥ (ν/log L) log log g_k^{−2}, with a different exponent ν (#B9.63–#B9.64-1).
   {#B2.2.291-1} With N = R_j both hold for g small (#B9.63),
   {#B2.2.292} and by (c) they hold for N_k^T = R_k^T, whose upper bound 2L(log g_k^{−2})^r has the form O(1)(log g_k^{−2})^ν once
   {#B2.2.293} r ≤ ν.
   {#B2.2.293-1} The exponents admit this: LFR1 p.198 takes ½ν ≤ p₀ − p₁ − 1 and LFR2 p.383 takes 2p₁ − (d+5)r₀ > p₀, with
   {#B2.2.294} r₀ = r the exponent of R_j (UV3 p.257 writes R = R₁(1 + log g_0^{−1})^{r₀}).
   {#B2.2.294-1} LFR1 p.198 takes ν a positive
   {#B2.2.295} integer, so put ν := ⌈r⌉; then r ≤ ν, and ν ≤ 2(p₀ − p₁ − 1) together with 2p₁ > p₀ + (d+5)r needs
   {#B2.2.296} p₁ ∈ ((p₀ + (d+5)r)/2, p₀ − 1 − ⌈r⌉/2), which is nonempty when p₀ > (d+5)r + ⌈r⌉ + 2.
   {#B2.2.296-1} CRE bounds p₀ only from below
   {#B2.2.297} ("p₀ ≥ 5r", CRE p.246), so p₀ is taken above (d+5)r + ⌈r⌉ + 2 and p₁ in that interval.
   {#B2.2.297-1} The ν of LFR2 p.363 is a different exponent, with ν ≥ 2p₀ + dr₀; there N ≥ (ν/log L)
   {#B2.2.298} log log g_k^{−2} holds for N = R^T_k ≥ (log g_k^{−2})^r and g small.
   {#B2.2.298-1} N₀ satisfies L^{N₀−1} = R^T_{k−N₀+1} ≤ (L+1)(N₀+1)^{β₀}R^T_k (LFR1 p.192 l.18–19,
   {#B2.2.299} with (c)), so N₀ = O(log R^T_k) < N_k^T for γ small.
5. {#B2.2.300} *(e).* ε(g) = gA₀(log g^{−2})^{p₀} increases on (0, γ] for γ small, since its logarithmic derivative is
   {#B2.2.301} g^{−1}(1 − 2p₀/log g^{−2}) > 0, so ε_j^T ≤ ε_j by (a).
   {#B2.2.301-1} The ratios follow from (a), since each parameter is ĝ_j or
   {#B2.2.302} 1 times a power of log ĝ_j^{−2}.
6. {#B2.2.303} *Where the parameters enter.* Every line of the corrected transcriptions of CRE (pp.244–284), LFR1 (pp.175–201),
   {#B2.2.304} and LFR2 (pp.356–391) that contains R_j, k₁, N₀, N, ε_j, δ_j, δ′_j, α_{0,j}, α_{1,j}, p₀(·), p₁(·), q₀(·), or q₁(·)
   {#B2.2.305} was read; LFR2's references [III] and [IV] are CRE and LFR1 (LFR2 p.392).
   {#B2.2.305-1} The three papers import further results,
   {#B2.2.306} and those were read too:
   - {#B2.2.307} UV3 ([16], CMP 102, pp.255–275), every line with one of its parameters (ε₁, p(g), R, r(g), and log g).
     {#B2.2.307-1} They are of the same kinds: the definitions
     {#B2.2.308} ε₁ = g_0p(g_0) and R = R₁r(g_0) (p.257) and their scale-k versions (pp.266–267), the distance conditions (p.266),
     {#B2.2.309} the factors exp(−R₁r(g_0)) (p.264), the normalisations d(𝔤) log g_k|·| (pp.261, 265, 269, 271), and the
     {#B2.2.310} chain ≥ (1/(2g_j²))|V_j(∂p′) − 1|² − O(1)g_jp³(g_j) ≥ ½p²(g_j) − O(1)g_jp³(g_j) ≥ ¼p²(g_j) of p.273, for
     {#B2.2.311} |V_j(∂p′) − 1| ≥ g_jp(g_j). This is a lower bound from the action; with the action coefficient y ≥ ĝ_j^{−2}/ρ̄ in
     {#B2.2.312} place of 1/g_j² and the tube threshold ĝ_jp(ĝ_j) it gives y(½(ĝ_jp(ĝ_j))² − O(1)(g_jp(g_j))³) ≥ ¼ρ̄^{−1}p²(ĝ_j), for γ small.
     {#B2.2.312-1} Here the cubic term of UV3 (70) is at most O(1)(g_jp(g_j))³ whether its thresholds are read at g_j or at ĝ_j (inferred, not printed: UV3 prints it at g_j), since gp(g) increases for g small (step 5's argument, with p(g) = b₀(1 + log g^{−1})^{p₀}, p.257 l.43). And (g_jp(g_j))² ≤ ρ_γ(ĝ_jp(ĝ_j))², by (a) and p(ĝ_j) ≥ p(g_j).
   - {#B2.2.313} CMP98 ([12]), REG ([14]), and VAR ([15]) are statements about lattice gauge fields, averaging operators, and
     {#B2.2.314} variational problems under a smallness condition on the field (a threshold ε with ε small).
     {#B2.2.314-1} They contain no
     {#B2.2.315} coupling, so they apply to the tube thresholds, which are smaller than CRE's (by (e)).
   - {#B2.2.316} The other imported results contain no coupling either: PBG ([13]; Theorems 3.7–3.10, CRE p.276, and LFR2
     {#B2.2.317} pp.357, 361, 362, and 370) and PRT1 and PRT2 ([10], [11]; LFR2 pp.358 and 376) are propagator and random-walk
     {#B2.2.318} estimates, CRE's [6] supplies the combinatorics of its Sect. 3 (CRE p.264), and CRE's [18] the definition (4.5.3)
     {#B2.2.319} of Q^{s*}_1 (CRE p.246); LFR2's [26] (Cammarota) is cited for "a standard proof of the convergence of the
     {#B2.2.320} expansion" (LFR2 p.391).
     {#B2.2.320-1} The parameters at these citations appear on the citing pages of CRE and LFR2, which
     {#B2.2.321} were read.
   - {#B2.2.322} Sects. 3–7 of [I], that is RG1 §§3–5 and, as Sects. 6–7 [I], RG2 §§1–2 (*The Step with Complex Multiples of the R-Terms*), are run by
     {#B2.2.323} CRE on its own cover, with the (2.28) domains and the regularity thresholds ε_n ("Sects. 3–5 [I]", "Sect. 6
     {#B2.2.324} [I]", and "Lemmas 5, 6 [I]", CRE p.276; "Sect. 7 [I]", CRE p.277), and by LFR2 on its large-field localisations
     {#B2.2.325} (LFR2 pp.372, 376, and 390).
     {#B2.2.325-1} Their parameters enter there as smallness conditions on the thresholds, as the
     {#B2.2.326} cutoff δ_j relative to the radii α_{0,j}, α_{1,j}, or as relations among the parameters, so they fall under the
     {#B2.2.327} kinds below, read on CRE's and LFR2's pages; RG1's fixed domains are covered by step 7 and by §0, *Input 3*.
   {#B2.2.328} Every occurrence is of one of four kinds.
   - {#B2.2.329} *Relations among the parameters alone*, of one index or of several.
     {#B2.2.329-1} Examples: the cube sizes and the
     {#B2.2.330} compatibility of the partitions (CRE pp.245–270, LFR1 p.177, LFR2 pp.384–387); the definitions of k₁ (CRE
     {#B2.2.331} p.270) and N₀ (LFR1 p.179), and the bounds L^{N₀−1} ≤ (L+1)(N₀+1)^{β₀}R_k and R_k^{−α₀} (LFR1 pp.192, 200);
     {#B2.2.332} (2.7) (CRE p.255) and (2.9) (CRE p.256); δ′_j ≤ (1+β₀)²(k−j)^{β₀}δ′_k (LFR1 p.192);
     {#B2.2.333} δ′_j/δ_j = A₀p₁(g_j)/p₀(g_j) (with the definitions of LFR1 p.183); the comparisons of ε_{k+1} with ε_k
     {#B2.2.334} (CRE pp.266–268, LFR1 pp.184–200); N^{1/2}p₁(g_h)/p₀(g_h) small (LFR1 pp.198–199); the margins
     {#B2.2.335} 2p₁ − (d+5)r₀ > p₀ between the exponents (LFR2 p.383 l.28), 2(1+β₀)^{−1}p₀(g_{j+1}) against O(1)3(100M)^dR_{j+1}^{d+2} (LFR2 (1.88), p.387 l.23), and
     {#B2.2.336} −2(1+β₀)^{−1}p₀(g_k) + 1 + 2κ(100R_k)^d ≤ −(3/2)p₀(g_k) (LFR2 p.389 l.16); and bounds through p₀(γ), p₁(γ) (LFR1 p.186).
     {#B2.2.336-1} In the
     {#B2.2.337} tube construction all of these are evaluated on the sequence (ĝ_j).
     {#B2.2.337-1} That sequence satisfies the hypotheses CRE
     {#B2.2.338} places on coupling sequences: its entries lie in (0, γ], it satisfies (2.6) because (u_j) ∈ H_K (step 2), and its
     {#B2.2.339} R^T satisfies (2.9) by (c).
     {#B2.2.339-1} So these relations hold as printed.
   - {#B2.2.340} *Lower bounds from the action.* A threshold τ_j forces a suppression exp(−c_τyτ_j²), with a constant c_τ > 0 of the source and y the coefficient of the
     {#B2.2.341} action at scale j: 1/g_j², or the top-down value of *Histories that are not flows*, which satisfies
     {#B2.2.342} y ≥ u_j/ρ̄ = ĝ_j^{−2}/ρ̄ there on every tube of the class.
     {#B2.2.342-1} Examples: exp[−(1/g_0²)[1 − Re tr U(∂p)]] ≤ exp(−p₀(g_0)) (LFR1 p.175) and ≤ exp(−½p₀²(g_0))
     {#B2.2.343} (CRE p.244), for |U(∂p) − 1| ≥ g_0p₀(g_0); the large-field factors of
     {#B2.2.344} LFR2 pp.380–383, including exp(−γ₀(1/g_m²)(2δ′_m)²) ≤ exp(−γ₀A₁²p₁²(g_j)) (p.381) and the factor
     {#B2.2.345} exp(−¼g_j^{−2}(24R_j⁴)^{−2}δ′_j²) (p.382); the factor exp(−c_lf(1/g_j²)δ′_j²) of the components excluded by
     {#B2.2.346} 1 − χ′^{(j)} (*LFR1 (1.55)*); and the Gaussian tails of RG2 (§0, *Input 3*).
     {#B2.2.346-1} Since
     {#B2.2.347} y ≥ ĝ_j^{−2}/ρ̄ (by (a) when y = 1/g_j², as ρ_γ ≤ ρ̄), yτ_j(ĝ_j)² ≥ ρ̄^{−1}τ_j(ĝ_j)²/ĝ_j², so each such factor
     {#B2.2.348} holds with c_τ replaced by c_τ/ρ̄ = 8c_τ/15, that is, with γ₀ replaced by 8γ₀/15.
     {#B2.2.348-0} In the LFR2 displays below, p₀(g_j) stands for (log g_j^{−2})^{p₀}, without CRE's factor A₀, as p₁(g_j) = (log g_j^{−2})^{p₁} does in LFR1 p.183 l.2 (inferred, not printed): LFR2 p.381 l.19–23 bounds ¼g_m^{−2}B₃^{−2}½ε_m², with ε_m = A₀g_m(log g_m^{−2})^{p₀} (CRE (2.4), p.255 l.33), below by ⅛B₃^{−2}(1+β₀)^{−2}A₀²p₀²(g_j), which is this reading with (log g_m^{−2})^{p₀} ≥ (1+β₀)^{−1}(log g_j^{−2})^{p₀} (Remark 2.2). The conditions on the constants at #B2.2.353 and #B2.2.356 are stated in this reading.
     {#B2.2.348-1} The conditions on the constants that
     {#B2.2.349} compare such factors at the same order are then imposed with the factor ρ̄ on the side of the action:
     - {#B2.2.350} the creation factor exp(−γ₀min{½B₃^{−2}A₀², 2A₁², A₁²}p₀²(g_j)(d′ + 1)) ≤ exp(−½γ₀A₁²p₀²(g_j)(d′ + 1) − 2p₀(g_j)) (LFR2
       {#B2.2.351} p.381 l.5–6, d′ := d′_j(Z_j^{(i)}) ≥ 0, LFR2's linear size of the component, p.380 l.28), whose margin is a factor 2 in the leading term: with ρ̄ = 15/8 the left side is at most
       {#B2.2.352} exp(−(8/15)γ₀A₁²p₀²(g_j)(d′ + 1)), and (1/30)γ₀A₁²p₀²(g_j) ≥ 2p₀(g_j) for g_j small;
     - {#B2.2.353} A₀ ≫ A₁ in exp(−⅛B₃^{−2}(1+β₀)^{−2}A₀²p₀²(g_j)) ≤ exp(−A₁²p₀²(g_j)) (LFR2 p.381, #T3.27-0);
     - {#B2.2.354} 4(1+β₀)^{−2} ≥ ρ̄ in exp(−γ₀(1/g_m²)(2δ′_m)²) ≤ exp(−γ₀4(1+β₀)^{−2}A₁²p₁²(g_j)) ≤ exp(−γ₀A₁²p₁²(g_j)) (LFR2 p.381),
       {#B2.2.355} which holds for β₀ ≤ √2 − 1, since then 4(1+β₀)^{−2} ≥ 2;
     - {#B2.2.356} A₀² ≥ 4ρ̄O(1)B₃M²A₁² in exp(−¼(1/g_j²)(O(1)B₃M²)^{−1}ε_j²) ≤ exp(−A₁²p₀²(g_j)) (LFR2 p.381);
     - {#B2.2.357} A₁ ≥ 48√ρ̄ in exp(−¼(1/g_j²)(24R_j⁴)^{−2}δ′_j²) = exp(−A₁²48^{−2}R_j^{−8}p₁²(g_j)) ≤ exp(−R_j^{−8}p₁²(g_j))
       {#B2.2.358} (LFR2 p.382);
     - {#B2.2.359} ¼γ₀14^{−d}A₁²p₀²(g₁) ≥ O(1)2·64^dM^dL^{d+1}R₁^{d+2} (LFR2 p.385), which has in addition the margin
       {#B2.2.360} p₀²(g₁) ≫ R₁^{d+2} of a power of log g_1^{−2}.
     {#B2.2.361} Every other such comparison has a margin of a positive power of log g_j^{−2}.
   - {#B2.2.362} *Upper bounds relative to the action.* Fluctuations bounded by a threshold enter the expansion of the action in
     {#B2.2.363} g_jB, giving terms such as (1/g_k²)O(1)|𝐁₀|δ′_k³ ≤ g_kO(1)M^dR_k^{d+2}A₁³p₁³(g_k) (LFR2 p.361), (1/g_k²)(α_{0,k} + α_{1,k})ε_k
     {#B2.2.364} (LFR2 p.368), and p₁²(g_k)(α_{0,k} + α_{1,k}) (LFR2 p.379).
     {#B2.2.364-1} By (e) these ratios change by at most the factor
     {#B2.2.365} 1 + o(1), and ε^T_j ≤ ε_j.
   - {#B2.2.366} *Conversions between scaled and unscaled fields*, such as |A(b)| < g_0^{−1}δ_0 (CRE p.250), |A_j(b)| < g_j^{−1}δ_j
     {#B2.2.367} (LFR1 (1.9), p.178), |B′| < M₀^{LFR2}g_k^{−1}ε_k (LFR2's constant M₀, p.356 l.37), and |B(b)| ≥ g_j^{−1}δ′_j (LFR2 p.383).
     {#B2.2.367-1} The factor g_j^{±1}
     {#B2.2.368} is the coupling of the history, and the threshold is the tube parameter, so in the unscaled field the threshold
     {#B2.2.369} is δ^T_0, δ^T_j, M₀^{LFR2}ε^T_k, or δ′^T_j.
     {#B2.2.369-1} The analyticity domain (3.43) of CRE p.276 bounds the scaled fluctuation
     {#B2.2.370} field by C^α_1p₁(ĝ_k); it is a domain on which analyticity and bounds are asserted, not a threshold under an
     {#B2.2.371} integral, and it enters as the other domains of analyticity do (Proposition 2.12, the real points of the
     {#B2.2.372} boundary terms).
   {#B2.2.373} Two further uses are not comparisons of a threshold with the action, and they hold for the same reasons.
   - {#B2.2.374} Quantities of the history bounded by a parameter, such as the bound on 1/(g″_k(·))² − 1/g_k² by O(N) (LFR2
     {#B2.2.375} p.366), the bounds on the background fields by thresholds (LFR2 pp.357, 378), and the terms "bounded by any
     {#B2.2.376} positive power of g" (CRE pp.252, 269; LFR1 p.188).
     {#B2.2.376-1} The history side is bounded by the β^T_j and by the couplings
     {#B2.2.377} g_j ≥ ĝ_j, and the parameter side is a tube parameter, which differs from CRE's by the factors of (e).
   - {#B2.2.378} The geometry: the domains Λ_j, Ω_j, the partitions, and the scales R^T_j are fixed by the target and the
     {#B2.2.379} configuration, so the combinatorial bounds (numbers of polymers, of cubes, and of partitions) hold as printed
     {#B2.2.380} with R^T in place of R.
   {#B2.2.381} The lower bounds on R_j, such as exp(−R_k) and exp(−δ2M₂R_k) small (CRE p.250 l.47, p.251 l.39, p.266 l.18–19, p.268 l.41–51, p.269 l.44) and
   {#B2.2.382} log g_j^{−2} ≤ R_j (LFR2 p.380), hold by (c).
   {#B2.2.382-1} The threshold 2ε_kη² of (1.75) enters LFR1 p.193 (the definition
   {#B2.2.383} and the large-field side), pp.195 and 200 (the bounds |U_0(∂p) − 1|, |U″_{k,Z}(∂p) − 1| < (2ε_kη² + …)), and
   {#B2.2.384} p.199 (the comparison ε_kη² ≤ (1+β₀)(k−j)^{1/2}L^{−2(k−j)}ε_j(L^{k−j}η)², a relation among parameters), and
   {#B2.2.385} LFR2 p.359 (extensions satisfying (1.75)), p.363, p.378 ("This is clear for χ_{k,Λ}"; the bound |∂V_k − 1| < 2ε_k
   {#B2.2.386} there comes from χ_k), and p.381.
   {#B2.2.386-1} The function χ_{k,Λ} itself enters further LFR1 pp.194, 196, 198, and 200 and
   {#B2.2.387} the densities of LFR2 pp.356, 369, 377, and 390, and, as χ_{k,Λ_i}, LFR1 p.201, LFR2 (1.72), p.379, and the formula
   {#B2.2.388} for 𝐑ρ_k on p.391.
   {#B2.2.388-1} All of these are statements about unscaled plaquette variables, with ε_k^T in each,
   {#B2.2.389} so they hold as printed.
   {#B2.2.389-1} The R-terms come out of LFR2 with |R′^{(k)}(X)| ≤ exp(−p₀(ĝ_k))exp(−κd_k(X)) (LFR2 p.390), and
   {#B2.2.390} exp(−p₀(ĝ_k)) ≤ ĝ_k^{2(log ĝ_k^{−2})^{p₀−1}} ≤ ĝ_k^{κ₀}, with or without the factor A₀ ≥ 1 in p₀(·) (#B2.2.348-0), ≤ g_k^{κ₀} for γ small, so CRE (2.31) holds with the
   {#B2.2.391} couplings of the history for the new R-terms.
   {#B2.2.391-1} The R-terms of earlier steps, in R′_k and in R″_k alike, keep their
   {#B2.2.392} bounds by CRE's induction ("These terms satisfy all the conditions of the inductive assumption", CRE p.279), which
   {#B2.2.393} in the tube construction runs over the histories of H_k with the tube domains α^T_{i,j}: the R-operation of LFR1
   {#B2.2.394} (1.100), p.201, acts on the step's analyticity domain, which is the tube domain, so its output is analytic and
   {#B2.2.395} bounded there.
7. {#B2.2.396} *RG1 with δ_j^T.* Propositions 2.4, 2.6, and 2.9 use the cutoff only through δ_j ≤ γp₀(γ), through
   {#B2.2.397} δ_j/g_j = A₁(log g_j^{−2})^{p₀} in the Gaussian tails (Proposition 2.9, steps 4–8, and §0, *Input 3*), and
   {#B2.2.398} through the continuity of δ_j/g_j in g_j, and Proposition 2.6, step 2, uses that δ_k does not decrease as g_k increases (#B2.1.88-1).
   {#B2.2.398-1} On the histories of H_k, by (e), δ_j^T/g_j lies between ρ_γ^{−1/2} and
   {#B2.2.399} 1 + o(1) times A₁(log g_j^{−2})^{p₀}, and it is continuous in g_j; δ_k^T is fixed by the tube, so it does not depend on g_k.
   {#B2.2.399-1} So Propositions 2.4, 2.6, and 2.9 hold for
   {#B2.2.400} RG1's construction run with δ_j^T on the histories of H_k; off H_k the tube parameters are not compared with the
   {#B2.2.401} couplings, and no claim is made there. ∎

{#B2.2.402} **Proposition 2.11 (The R-Terms Shift β by O(g_k^{κ₀−4})).** Let γ be small, k < K, (x_0, …, x_k) ∈ H_k, and
{#B2.2.403} h = (g_0, …, g_k) with g_j = x_j^{−1/2}.
{#B2.2.403-1} Let β^T_{k+1}(h) be the coefficient of the tube construction (CRE (3.61)–(3.64),
{#B2.2.404} pp.282–283) and β^{δ,T}_{k+1}(h) the coefficient of RG1's construction run with the cutoffs δ_j^T on the same history.
{#B2.2.405} Then
  {#B2.2.406} |β^T_{k+1}(h) − β^{δ,T}_{k+1}(h)| ≤ C_R g_k^{κ₀−4},
{#B2.2.407} with C_R independent of k, K, g, the history, and the tube of the class, and κ₀ ≥ 7 the exponent of CRE (2.31).

{#B2.2.408} *Proof.*
1. {#B2.2.409} *The R-terms.* CRE (2.30)–(2.31), p.260: R_k = Σ_j[R^{(j)}(Λ_j, U_k) − R^{(j)}(Λ_j, 1)], with the properties
   {#B2.2.410} (i)–(iii) of CRE p.259 (property (ii) is analyticity on U^c_j(X, α_{0,j}, α_{1,j})) and
   {#B2.2.411} |R^{(j)}(X, (U, J))| ≤ g_j^{κ₀}exp(−κd_j(X)). (2.31) is an inductive assumption; "κ₀ can be chosen arbitrarily
   {#B2.2.412} large, similarly as κ, if the other parameters are fixed properly, as in [I]" (CRE p.260), and CRE (2.46), p.263, uses κ₀ ≥ 7.
   {#B2.2.412-1} The
   {#B2.2.413} histories of H_k satisfy CRE (2.6) (Lemma 2.10(b)).
2. {#B2.2.414} *The family.* Take the whole-lattice R-terms R^{(j)}(U_j) = Σ_X R^{(j)}(X, U_j) of CRE (2.33), p.260, of the tube
   {#B2.2.415} construction for the history h.
   {#B2.2.415-1} For s ∈ ℂ, run the whole-lattice regular recursion of the tube construction (RG1's
   {#B2.2.416} formulas with δ_j^T, CRE pp.267, 272, 274) with sR^{(j)} in place of R^{(j)} wherever CRE includes R′ into E
   {#B2.2.417} (CRE p.271), and with the counterterms β_j(s) computed from its own step terms by CRE (3.61).
   {#B2.2.417-1} Write E^{(j)}(s) and
   {#B2.2.418} β_j(s).
   {#B2.2.418-1} At s = 1 this is the regular part of the tube construction, so β_{k+1}(1) = β^T_{k+1}(h); at s = 0 no R-term
   {#B2.2.419} enters, so β_{k+1}(0) = β^{δ,T}_{k+1}(h).
3. {#B2.2.420} *The size of the R-part.* By the windows of H_k, x_j ≥ x_k + b(k−j) − C ≥ ½x_k + c ln L·(k−j) for j ≤ k,
   {#B2.2.421} since b ≥ c ln L and C ≤ t/8 ≤ x_k/7 (x_k ≥ ℓ_k ≥ t − C) on the class of tubes.
   {#B2.2.421-1} So
     {#B2.2.422} Σ_{j≤k} g_j^{κ₀} ≤ Σ_{m≥0}(½x_k + mc ln L)^{−κ₀/2} ≤ C_Σ g_k^{κ₀−2},  C_Σ := 2^{κ₀/2}(1 + 2/((κ₀−2)c ln L)).
   {#B2.2.423} C_Σ, and hence C_R below, is uniform over the class of tubes, so δ′ = δ + C_Rγ^{κ₀−4} ≤ (2/5)c ln L for γ small
   {#B2.2.424} is not circular (*The Tube of a Target*).
   {#B2.2.425} Each R′-term satisfies a bound of the form (1.18), since |s|g_j^{κ₀} ≪ E₀, but the R′-part lacks the factor
   {#B2.2.426} (L^jη)⁵ of the irrelevant terms (RG2 (1.24), p.7) that RG2 uses to sum over j (RG2 p.8) before Lemma 1, (1.36),
   {#B2.2.427} p.9: after the vacuum-energy renormalisation it consists of marginal terms, with bounds
   {#B2.2.428} O(1)(L^jη)⁴g_j^{κ₀}exp(−κd_j(X)).
   {#B2.2.428-1} CRE controls it by its own bound instead: "The sum over X is controlled by the exponential factor, and by the factor (L^jη)⁴.
   {#B2.2.428-2} The sum over j is
   {#B2.2.429} controlled by g_j^{κ₀}" (CRE p.260), and (2.44), p.263 l.24–26, bounds the R-terms of step j over the X meeting Ω by
   {#B2.2.430} R₁g_j^{κ₀}Σ_{n=j}^{k}|Γ_n ∩ Ω|, with CRE's absolute constant R₁ (p.263 l.22–23; not UV3's R₁ of #B2.2.294), Ω a domain of 𝐃_k in B^j(Λ_j^0) (p.263 l.5) and Γ_n = Ω_n^{(n)}∖Ω_{n+1}^{(n)}, Γ_k = Ω_k^{(k)} (CRE p.255 l.15–16).
   {#B2.2.430-1} The potential V′ of RG2 Lemma 1, through which the R′-part enters the step, is linear in the constant
   {#B2.2.431} of (2.31): V′ is built linearly from the bracket of E_k (RG2 (1.33)), and the sums over X and j are controlled as
   {#B2.2.432} quoted.
   {#B2.2.432-1} The later expansions of the step, such as the products of RG2 (2.26), p.17, are not linear in it; they use
   {#B2.2.433} only the resulting bound (1.36) with 2E₀ and the smallness condition of RG2 p.18, and the R′-part enters them
   {#B2.2.434} through the modulus of the interaction (*The Step with Complex Multiples of the R-Terms*, below).
   {#B2.2.434-1} Let K_V be the
   {#B2.2.435} constant such that an R′-input of step j whose terms satisfy (2.31) with g_i^{κ₀} replaced by a_ig_i^{κ₀} enters
   {#B2.2.436} the potential V′ of RG2 Lemma 1 with K_VΣ_{i≤j}a_ig_i^{κ₀} in the place of E₀ in (1.36), p.9: its part of V′ is
   {#B2.2.437} at most K_VΣ_{i≤j}a_ig_i^{κ₀}ε₁C₁M^q exp C₂κ₁ exp(−(1−2δ_{RG2})κd_j(Y)).
   {#B2.2.437-1} So the input side of the step, regular part and
   {#B2.2.438} R′-part together, is bounded as in (1.36) with E₀ + K_VΣ_{i≤j}a_ig_i^{κ₀} in place of E₀.
   {#B2.2.438-1} K_V (not RG1's K_R of #T2.24) depends only on the
   {#B2.2.439} constants of CRE's step and on κ, so it is uniform over the class of tubes.
   {#B2.2.440} Every R′-term that has entered E up to step k, at any earlier step, carries the factor s, so a_i = |s|.
   {#B2.2.440-1} Put
   {#B2.2.441} θ := E₀/(K_VC_Σ) and ρ := θg_k^{2−κ₀}.
   {#B2.2.441-1} For j ≤ k, Σ_{i≤j}g_i^{κ₀} ≤ Σ_{i≤k}g_i^{κ₀} ≤ C_Σg_k^{κ₀−2} by the first
   {#B2.2.442} display, so for |s| ≤ ρ
     {#B2.2.443} K_V|s|Σ_{i≤j}g_i^{κ₀} ≤ K_VρC_Σg_k^{κ₀−2} = K_VθC_Σ = E₀
   {#B2.2.444} at every step j ≤ k, and the input side is bounded with 2E₀ in place of E₀.
   {#B2.2.444-1} The argument is an induction over j = 0, …, k at the fixed radius ρ = ρ_k: if the regular
   {#B2.2.445} part of the input of step j satisfies (1.18) with E₀ and is analytic in s on |s| < ρ, then the input side is
   {#B2.2.446} bounded with 2E₀, and by step 4 the output E^{(j+1)}(s) satisfies (1.18) with E₀ (the fluctuation part at most
   {#B2.2.447} ½E₀ by RG2 pp.20–21, the part from log Z^{(j)} at most ½E₀) and is analytic in s; β_{j+1}(s) is analytic on
   {#B2.2.448} |s| < ρ by step 5 at scale j+1. At j = 0 there is no R-term and no s.
4. {#B2.2.449} *The step with 2E₀ and complex s.* CRE's step accepts these inputs (*The Step with Complex Multiples of the
   {#B2.2.450} R-Terms*, below).
   {#B2.2.450-1} The conditions that involve E₀ are upper bounds on the cutoff relative to the domain radii: RG2 p.18,
   {#B2.2.451} 2E₀ε₁C₁α₄^{−1}α₆^{−1}M^q e^{C₂κ₁}e^{5κ} ≤ 1; RG2 p.20; and RG2 p.21, O(1)C₃ε₁ ≤ ½E₀ with C₃ linear in E₀
   {#B2.2.452} (Proposition 2.4, step 2).
   {#B2.2.452-1} Two further conditions involve E₀ and only get weaker when E₀ is doubled: the tail
   {#B2.2.453} condition exp(−γ₂ε₁²/(20γ²)) ≤ ε₂ of RG2 p.19, with ε₂ = 2E₀ε₁C₁α₄^{−1}α₆^{−1}M^q exp C₂κ₁, a lower bound on
   {#B2.2.454} ε₁/g_k (§0, *Input 3*), and C₃′ ≤ E₀C₁ of RG2 p.16 l.20, where C₃′ is the absolute constant RG2 prints as C₃ in (1.39) (p.10 l.28), not #B2.1.15's C₃ of p.20 l.25.
   {#B2.2.454-1} On CRE's domains the cutoff enters relative to α_{0,j},
   {#B2.2.455} through δ_j/α_{0,j} = (A₁/C^α_0)(log g_j^{−2})^{p₀−q₀}, and CRE takes C^α_0 and C^α_1 "sufficiently large"
   {#B2.2.456} (p.259).
   {#B2.2.456-1} This ratio is small for g_j small when q₀ > p₀, and likewise
   {#B2.2.457} δ_j/α_{1,j} when q₁ > p₀.
   {#B2.2.457-1} CRE (2.28), p.259, prints q₀ and q₁ as "integers greater than 1", and says on p.262
   {#B2.2.458} that "some of the restrictions on constants, e.g. on constants κ, M, ε_j, α_{0,j}, α_{1,j}, come from the paper
   {#B2.2.459} [I]".
   {#B2.2.459-1} RG1 and RG2 print no upper restriction on q₀, q₁: RG2's assumption that (LM)⁴α₀ and (LM)⁴α₁ are "bounded by a constant independent of M, for example by 1" (p.20 l.23) holds for
   {#B2.2.460} CRE's α_{i,j} = g_jC^α_i(log g_j^{−2})^{q_i} (CRE (2.28), p.259 l.47) once g_j is small, whatever q_i; nor do LFR2 pp.358, 368, and 379,
   {#B2.2.461} where α_{0,k} + α_{1,k} enters multiplied by small factors (Lemma 2.10, step 6, *upper bounds relative to the
   {#B2.2.462} action*).
   {#B2.2.462-1} So q₀ and q₁ are taken greater than p₀ (#T6.17, #T10.28-2).
   {#B2.2.462-2} These conditions are imposed for 2E₀ when C^α_0, C^α_1, and the cutoff are chosen.
   {#B2.2.462-3} The step
   {#B2.2.463} output is given by convergent expansions whose terms are analytic in the exponent, uniformly for |s| ≤ ρ, so
   {#B2.2.464} E^{(j+1)}(X; s) is analytic in s.
   {#B2.2.464-1} The parameter s is not CRE's parameter s of (3.26)–(3.27), p.271, which
   {#B2.2.465} multiplies R″_k; that one stays as in CRE.
5. {#B2.2.466} *Polarisation on the tube domains.* E^{(k+1)}_fl(X; s) is analytic on U^c_{k+1}(X, α^T_{0,k+1}, α^T_{1,k+1}) and
   {#B2.2.467} bounded by E₀e^{−κd_{k+1}(X)}.
   {#B2.2.467-1} In the proof of Lemma 2.5 the domain enters only through the Cauchy radius r of step 2, and steps 2–4 give C_Λ as an r^{−2} term plus an r^{−1} term, with coefficients independent of the domain, so C_Λ ≤ C_Λ(1)r^{−2} for r ≤ 1, C_Λ(1) being the value at r = 1.
   {#B2.2.468} The point u(0) = (1, 0) satisfies (i)–(iv) of #T11.7 with every bounded quantity zero, and along u(0) + tv with ‖v‖ ≤ 1 and |t| ≤ 1 each quantity is at most C_cen|t| in the units of its condition, with C_cen depending only on L, M and the averages of (iv).
   {#B2.2.469} So r := min(α^T_{0,k+1}, α^T_{1,k+1})/C_cen is admissible, and r ≤ 1 for γ small.
   {#B2.2.469-1} With q_* := min(q₀, q₁) ≥ 2 and x̂ := ĝ_{k+1}^{−2} = u_{k+1} ≤ u_k ≤ ρ_γx_k ≤ 2x_k (Lemma 2.10(a)), α^T_{i,k+1} ≥ min(C^α_0, C^α_1)x̂^{−1/2}(log x̂)^{q_*} (#T10.34), so with C′ := C_Λ(1)C_cen²/min(C^α_0, C^α_1)²
     {#B2.2.470} |β_{k+1}(s) − b_{k+1}| = |Λ(E^{(k+1)}_fl(·; s))| ≤ C_Λ(1)r^{−2}E₀ ≤ C′E₀x̂(log x̂)^{−2q_*} ≤ 2C′E₀g_k^{−2}.
   {#B2.2.471} The domain is fixed by the target, so no bound on the next coupling is needed.
   {#B2.2.471-1} The infinite-volume limit of Λ is
   {#B2.2.472} uniform in s by the domination of Lemma 2.5, so s ↦ β_{k+1}(s) is analytic on |s| < ρ.
6. {#B2.2.473} *Cauchy in s.* For γ small, ρ = θg_k^{2−κ₀} > 2 because κ₀ ≥ 7.
   {#B2.2.473-1} For s₀ ∈ [0, 1] the closed disc of radius ρ/2
   {#B2.2.474} about s₀ lies in |s| < ρ, since 1 + ρ/2 < ρ, so |β′_{k+1}(s₀)| ≤ 4C′E₀g_k^{−2}/ρ, and
   {#B2.2.475} |β_{k+1}(1) − β_{k+1}(0)| ≤ 4C′E₀g_k^{−2}/ρ = 4C′K_VC_Σg_k^{κ₀−4} =: C_Rg_k^{κ₀−4}. ∎

{#B2.2.476} *The Step with Complex Multiples of the R-Terms (checked against CRE pp.260, 264, 271, 276–279, and RG2 pp.15–18).*
- {#B2.2.477} CRE's step uses the inductive assumption on E_k: "Using the inductive assumption we write" (CRE p.264), and it
  {#B2.2.478} takes R′_k in as part of E_k (p.271).
  {#B2.2.478-1} Its output satisfies the inductive bounds: "These terms satisfy all the
  {#B2.2.479} conditions of the inductive assumption" (p.279).
- {#B2.2.480} R′_k itself, carried in E_k, gets no counterterm.
  {#B2.2.480-1} Its contribution to the fluctuation integral of step k enters the
  {#B2.2.481} whole-lattice E^{(k+1)}, from which the counterterm of step k+1 is computed (CRE (3.57), p.281; p.279), so only
  {#B2.2.482} that contribution is coupling-renormalised; this is the part that the family of step 2 multiplies by s inside the
  {#B2.2.483} step terms.
  {#B2.2.483-1} The R-terms that stay R (R″_k) get no coupling
  {#B2.2.484} counterterm: R_k "is treated in exactly the same way as E_k, except the second renormalization connected with the
  {#B2.2.485} coupling constant renormalization counterterm, which is not needed here" (p.276).
  {#B2.2.485-1} This sentence concerns R″_k in the
  {#B2.2.486} measure (3.27), which CRE multiplies by its own real parameter s ∈ [0, 1] (p.271), and it rests on the factor g_j^{κ₀}
  {#B2.2.487} ("The sum over j is controlled by g_j^{κ₀}", p.260).
  {#B2.2.487-1} The family of Proposition 2.11 multiplies only the R′-part, and
  {#B2.2.488} step 3 keeps the R′-parts, summed over all earlier steps, at most E₀.
- {#B2.2.489} "The final step in constructing localized expansions of the expectation values is the exponentiated cluster
  {#B2.2.490} expansion of Sect. 7 [I], or rather its appropriate generalization", and the normalization factor of (3.28) "is
  {#B2.2.491} expanded in exactly the same way as in Sect. 7 [I]" (p.277).
  {#B2.2.491-1} CRE's [I] is RG1 (CRE
  {#B2.2.492} p.285), whose sections are 0–5.
  {#B2.2.492-1} RG2 numbers its own sections 1 and 2, but the equations that CRE cites with
  {#B2.2.493} sections 6 and 7 of [I] are RG2's equations of sections 1 and 2: (I.7.12)–(I.7.13) are RG2 (2.12)–(2.13), and
  {#B2.2.494} (I.6.34) is RG2 (1.34).
  {#B2.2.494-1} So "Sect. 7 [I]" is RG2 §2.
  {#B2.2.494-2} That expansion is already analytic in complex multipliers of the interaction.
  {#B2.2.495} RG2 (2.14) carries exp[Σ_Y τ(Y)V_k(Y, B)] with complex τ(Y), and RG2 (2.15) bounds it through
  {#B2.2.496} exp[Σ_Y |τ(Y)||V_k(Y, B)|].
  {#B2.2.496-1} The only positivity used is that of the Gaussian measure at (U, 0): "For the pair (U, 0)
  {#B2.2.497} the operators are symmetric, and the measure is positive … The general case is handled by a perturbative argument"
  {#B2.2.498} (RG2 p.15).
  {#B2.2.498-1} The interaction, which contains the bracket of E_k, enters only through its modulus.
  {#B2.2.498-2} So a complex scalar s
  {#B2.2.499} on the R′-part of E_k enters the same way as τ, and it preserves the properties (i)–(iii) of CRE p.259 and the
  {#B2.2.500} covariance (2.29).

{#B2.2.501} *Consequence (the Bounds of (W) and Item 5 for the Tube Construction).* For every tube of the class and every history of
{#B2.2.502} its H_k, Proposition 2.11 with Propositions 2.4 and 2.9 for the cutoffs δ_j^T (Lemma 2.10, step 7) gives
  {#B2.2.503} |β^T_{k+1} − b_{k+1}| ≤ δ + C_Rγ^{κ₀−4} = δ′  and  |β^T_{k+1} − b_{k+1}| ≤ (C_rem + C_Rγ^{κ₀−6})g_k².
{#B2.2.504} For the tube of the target (K, g), (W) holds for β^T on the histories of H_K, with b = 2c ln L − δ′, b′ = 2c ln L + δ′, and C = C₀ (Remark 2.3), and
{#B2.2.505} δ′ < 2c ln L for γ small.
{#B2.2.505-1} Item 1 concerns b_j only.
{#B2.2.505-2} Item 5 holds on H_k with C_rem + C_Rγ^{κ₀−6}.
{#B2.2.505-3} Items 3 and 4 hold
{#B2.2.506} along the matched flow of Proposition 2.13, which lies in H_K.

{#B2.2.507} **Proposition 2.12 (Continuity of the Tube Construction).** Let γ be small.
{#B2.2.507-1} For each k < K, the coefficient
{#B2.2.508} β^T_{k+1}(h) of the tube construction for (K, g) is continuous on the histories h = (x_0^{−1/2}, …, x_k^{−1/2}) with
{#B2.2.509} (x_0, …, x_k) ∈ H_k.

{#B2.2.510} *Proof.* Induction on j.
{#B2.2.510-1} The terms of the density ρ_{j+1} produced by the steps 0, …, j are the regular terms (the
{#B2.2.511} part E_{j+1} with the R′-part), the R-terms R^{(i)}, the boundary terms B_{j+1}, and the operations T_{j+1} of CRE
{#B2.2.512} (2.18)–(2.23).
{#B2.2.512-1} A term F(X) produced at the step i is an analytic function of the configurations (𝐔, 𝐉) of scale i + 1
{#B2.2.513} on its own domain D_F, with the radii of its own generation: U^c_{i+1}(X, α^T_{0,i+1}, α^T_{1,i+1}) for the regular
{#B2.2.514} terms (CRE (2.26)–(2.27)(ii), p.259), the same space with the bound CRE (2.31), p.260, for the R-terms, and the spaces
{#B2.2.515} of CRE (3.43), p.276, with the fluctuation field A on Y ∩ Λ^{(i)*}_{i+1}, for the boundary terms.
{#B2.2.515-1} A real point of D_F
{#B2.2.516} is a point (U, J) with U G-valued and J real (and A real for the boundary terms).
{#B2.2.516-1} The domain (3.43) bounds the
{#B2.2.517} unscaled field by g_iC^α_1p₁(ĝ_i), continuous in h, so for the boundary terms the real points at h⁰ are those whose
{#B2.2.518} unscaled field is below g⁰_iC^α_1p₁(ĝ_i), g⁰_i the coupling of h⁰; they are real points of D_F for all h near h⁰.
{#B2.2.518-1} The
{#B2.2.519} claim S_j is that the coefficients β_i, i ≤ j + 1, are continuous at every h⁰ ∈ H_j, and that at every h⁰ ∈ H_j:
- {#B2.2.520} (a) *Real points.* Every such term F satisfies F(X, U, J; h) → F(X, U, J; h⁰) as h → h⁰, at every real point
  {#B2.2.521} (U, J) of D_F.
- {#B2.2.522} (b) *Polydiscs.* Every regular term and every R-term F satisfies the following.
  {#B2.2.522-1} Let u_i(B) := (U_{i+1}(e^{iB}), J_{i+1}(e^{iB})),
  {#B2.2.523} call a real field B⁰ admissible for F when
  {#B2.2.524} u_i(B⁰) lies in the real part of U^c_{i+1}(X, ½α^T_{0,i+1}, ½α^T_{1,i+1}) (B⁰ = 0 is admissible), and let
  {#B2.2.525} P_i(B⁰) := {|B − B⁰| < r_i}, r_i := c_pd·min(α^T_{0,i+1}, α^T_{1,i+1}), with c_pd > 0 so small that u_i maps every P_i(B⁰) into
  {#B2.2.526} D_F.
  {#B2.2.526-1} Such a c_pd exists by RG1 (1.15)–(1.16), p.262 l.45–52, and Lemma 2.5, step 1, whose derivative bound comes from VAR Prop. 9 and VAR (190),
  {#B2.2.527} stated for every external configuration satisfying "the regularity conditions (3.35)–(3.38) [5], or (1.7)–(1.9) [6]"
  {#B2.2.528} (VAR p.309 l.8–13).
  {#B2.2.528-1} Then F(X, u_i(B); h) → F(X, u_i(B); h⁰) uniformly on compact subsets of P_i(B⁰), for every
  {#B2.2.529} admissible B⁰.

{#B2.2.530} Lemma 2.5, and so the polarisation map of #B2.1.10-1, uses (b) for the regular terms of step k at B⁰ = 0; the localisations of the later steps use (a).
{#B2.2.530-1} A term
{#B2.2.531} depends on h only through the entries of the history up to the step that produces it (*Where the history enters*),
{#B2.2.532} and the later steps read it without changing it, so (a) and (b), once proved at that step, hold at every later
{#B2.2.533} stage.
{#B2.2.533-1} At the stage j, steps 2–3 below prove (a) for the terms produced by step j and step 4 proves (b) for its
{#B2.2.534} regular terms and R-terms (the R-terms 𝐑^{(i)}, i ≤ k₁, form the R′-part that CRE p.271 includes into E_k, and the others are read through
{#B2.2.535} the s-integral of CRE (3.26)), and step 5 proves the continuity of β_{j+1}; then E_{j+1}, which contains −β_{j+1}A(φ_{j+1}, ·) (CRE (2.25)), satisfies (a) and
{#B2.2.536} (b) too.
{#B2.2.536-1} With the terms of the earlier steps, this is S_j.
{#B2.2.536-2} We write u := u_j, r := r_j, and P(B⁰) := P_j(B⁰).
0. {#B2.2.537} *Base case.* The density ρ_0 is the Wilson density exp(−(1/g_0²)A(U)) with no earlier terms and no β; it is
   {#B2.2.538} continuous in g_0 at fixed U, so S_{−1} holds.
1. {#B2.2.539} *What depends on h.* In the tube construction every threshold, scale, depth, and partition, and every domain
   {#B2.2.540} radius α^T_{i,j}, is fixed by (K, g) (Lemma 2.10); the one radius that moves with h is that of the domain (3.43) in
   {#B2.2.541} the unscaled field (the real points of the boundary terms above).
   {#B2.2.541-1} In unscaled fields the characteristic functions do not depend on h:
   - {#B2.2.542} the background-field functions χ_k(Ω_k) of CRE (2.17), with threshold ε^T_kη² on the plaquettes of the background
     {#B2.2.543} fields U_{k,□}(V_k) of CRE (2.16), which are defined from the fields alone;
   - {#B2.2.544} the inf–sup function χ_{k,Λ} of LFR1 (1.75), with threshold 2ε^T_kη²;
   - {#B2.2.545} the fluctuation-field functions, whose thresholds act on g_jA_j and on exp(ig_jB_j(b)) (for example
     {#B2.2.546} |exp ig_jB_j(b) − 1| < 2δ′_j in LFR1 (1.59), p.188, and |g_jB_j(b)| < δ′_j for χ′^{(j)}, whose print in LFR1 (1.55)
     {#B2.2.547} has the scaled variable and which the construction places on the unscaled field, *LFR1 (1.55)* before Lemma
     {#B2.2.548} 2.10), with δ^T_j and δ′^T_j.
   {#B2.2.549} The changes of variables of CRE (1.22)–(1.23), pp.251–252, of CRE p.269 at the step k ("the change of variables
   {#B2.2.550} given by the formula (1.22), with 𝐇^{(k)}(b) instead of 𝐇_{1,Ax}(b)", for the bonds of (R^{∼2}_{k+1} ∩ S_{k+1})^{(k)*},
   {#B2.2.551} and the simpler change with g(A′_k(b)) replaced by 1 on the remaining bonds of S^{(k)*}_{k+1}), and of LFR1 p.188
   {#B2.2.552} read, in unscaled fields, exp(iB) = exp(iB′)exp(−iφ_b(B′)H), where φ_b is the C^∞ bump of CRE p.252 (printed g there) with supports fixed
   {#B2.2.553} by δ^T_0 at step 0, by δ^T_k at the step k, and by δ′^T_j in the change of variables of LFR1 p.188, and H is an
   {#B2.2.554} analytic function of the background fields (H_{1,Ax} of CRE (1.21), 𝐇^{(k)} of CRE (3.22), p.269, and ℍ_Z^{(j)} of
   {#B2.2.555} LFR1 (1.58)).
   {#B2.2.555-0} CRE fixes the bump only on two sets (p.252 l.2–3); take φ_b(B′) := φ_1(|B′|/δ^T), with δ^T the cutoff of the change (δ^T_0, δ^T_k or δ′^T_j above), |·| the Hilbert–Schmidt norm, which is the norm of CRE's conditions (CRE p.244 l.8–9 takes its definitions from RG1 and the earlier papers it cites; PBG p.390 l.7 fixes |X| as Hilbert–Schmidt), for one fixed smooth φ_1 on [0, ∞) with 0 ≤ φ_1 ≤ 1, φ_1 = 0 on [0, 4/3], and φ_1 = 1 on [5/3, ∞).
   {#B2.2.555-0a} This is admissible: φ_b is smooth on g, as φ_1 vanishes near 0, and |exp iB′ − 1| ≤ |B′| for B′ ∈ g (both are diagonal in one orthonormal basis, with entries e^{iλ} − 1 and λ, and |e^{iλ} − 1| ≤ |λ|), so φ_b = 1 where |exp iB′ − 1| ≥ 5δ^T/3. It is invariant under every unitary conjugation preserving g.
   {#B2.2.555-1} These maps and
   {#B2.2.556} their Jacobians (CRE (1.24)) do not depend on h.
   {#B2.2.556-1} The block-averaging constraints and the Haar measures do not depend
   {#B2.2.557} on h either.
   {#B2.2.557-1} The couplings of the history therefore enter only through the densities: the Wilson action with the
   {#B2.2.558} couplings g_j(x) (the top-down formula), the Gaussian densities of the unscaled fluctuation fields with covariance
   {#B2.2.559} ∝ g_j², the axial gauge-fixing weight exp[−(1/g_k²)G] and its normaliser z(g_k, ε^T_k), the scaling Jacobians,
   {#B2.2.560} the R-operation densities and normalisers of LFR1 (1.100), the counterterms β_i, and the terms of the effective
   {#B2.2.561} action of the earlier steps (the list of *Where the history enters*).
2. {#B2.2.562} *Where step j reads the earlier terms.* The terms of step j are defined by Bałaban's formulas as functions of the
   {#B2.2.563} variables (𝐔, 𝐉), which replace U_{k+1} and J_{k+1} in the operators (RG1 p.272).
   {#B2.2.563-1} The formulas read the earlier
   {#B2.2.564} terms at three kinds of arguments:
   - {#B2.2.565} (i) in RG1 (3.13), for the expressions (3.7) and their extensions (3.15), at exp iξ𝐀𝐔 and
     {#B2.2.566} (L^{j−1}η)³𝐉 + Δ^ξ_𝐔𝐀 − P₁𝐀 + 𝐅₁(𝐔, 𝐀), on U_j^c(X, ½α₀, ½α₁, α₀) for 𝐀 in (3.14) (RG1 p.272), with
     {#B2.2.567} 𝐀 = 𝐇_j(B(t)) + t_□δ𝐇_j, where 𝐇_j and δ𝐇_j are the localised functions of RG1 p.273 ("Later we will change
     {#B2.2.568} these functions by a localization procedure", after (3.17)) with the s-variables of RG2 p.8;
   - {#B2.2.569} (ii) in RG1 (3.33)–(3.36) and Lemma 4, (3.53), p.280, at (U_j(□₀, exp iw), J_j(□₀, exp iw)) ∈ U_j^c(X, α₀, α₁),
     {#B2.2.570} w = τB + B′, τ ∈ [0, 1], |B′| < α₃, with B = Q(ηA) and A of (3.30) built from 𝐀 = (tζ̃_□ + t_□ζ_□)𝐇_k(s, B′)
     {#B2.2.571} (RG2 (1.8) and (1.23)); CRE p.276 applies the same formulas to the boundary terms;
   - {#B2.2.572} (iii) in the large-field steps, in the first localisation of LFR2 (1.59)–(1.60), p.372, and its repetitions
     {#B2.2.573} with the representations (1.54), (1.57), and (1.58) (pp.372–373), at the configurations U of the passes (U^0_k,
     {#B2.2.574} U_{1,2}, U_{k,Λ}, and U_k), and, for τ ∈ [0, 1], at exp iτη𝐇 U and at U_j(𝐁_j(□₀), exp iτQ_·(η𝐇)M^·(U)) (the
     {#B2.2.575} points of the Taylor remainder of RG1 (3.34), which lie in the domain of the term by RG1 (3.36), p.277, through
     {#B2.2.576} "all the transformations and estimates of Sects. 3–5 [I]", LFR2 p.372), 𝐇 being the localised
     {#B2.2.577} function of the pass (𝐇″_k(g_kB) of (1.51), 𝐇″_k of (1.54), 𝐇_{𝐁₁} of (1.57), and 𝐇_k of (1.58)); and in the terms V(Y) and V(X^∼) of
     {#B2.2.578} LFR2 (1.70)–(1.72), at the configurations LFR2 (1.61)–(1.63), pp.373–374, which contain the gauge transformations u^0_k, u_{1,±}, and (u_{k,Λ})_± "given by
     {#B2.2.579} the explicit formula (106) [12]" (LFR2 p.373), [12] being CMP98.

   {#B2.2.580} At real (𝐔, 𝐉) and real values of the auxiliary variables (t, t_□, s, τ, B′) every one of these arguments is a
   {#B2.2.581} real point of the domain of the earlier term.
   {#B2.2.581-1} The localised operators are walk sums whose terms are multiplied by
   {#B2.2.582} the numbers s(Δ) (RG2 p.3), so 𝐇_j, δ𝐇_j, and 𝐇_k(s, B′) are real, and so are LFR2's localised functions 𝐇″_k,
   {#B2.2.583} 𝐇_{𝐁₁}, and 𝐇_k at real s and real B, which are built in the same way from the operators of PBG and VAR (LFR2
   {#B2.2.584} (1.54) and (1.57)–(1.58)).
   {#B2.2.584-1} The gauge transformations v and u_{k+1} of
   {#B2.2.585} RG1 (3.26)–(3.27), p.275, which bring M^·(𝐔) into the generalised axial gauge and U_{k+1}(□₀, V) into the Landau
   {#B2.2.586} gauge, are "explicitly given analytic functions of 𝐔" (RG1 p.276); at real 𝐔 they are the gauge transformations
   {#B2.2.587} of these G-valued configurations, so they are G-valued, and 𝐇_{k+1}(□₀, (1/i)log V) is real.
   {#B2.2.587-1} Hence the variables
   {#B2.2.588} R(u_{k+1}^{−1})R(v^{−1})𝐉 and R(u_{k+1}^{−1})R(v^{−1})B that replace 𝐉 and B in 𝐇_k(B′) (RG1 p.276) are real,
   {#B2.2.589} and so are A and B of (3.30).
   {#B2.2.589-1} The operators Δ^ξ_𝐔 and P₁ are real at real 𝐔, and 𝐅₁ collects 𝐅 of (3.11), an
   {#B2.2.590} identity between real quantities "for any regular configuration U", and the local lower-order operator from the
   {#B2.2.591} replacement of D*D (RG1 p.272).
   {#B2.2.591-1} U_j(□₀, ·) and J_j(□₀, ·) are the background field and current of a real field.
   {#B2.2.592} In CMP98 (106), p.33, u(x) is the product over j of the operators R(U₀(Γ^{(j+1)}_{x_{j+1},x}))^{−1} applied to
   {#B2.2.593} brackets of two factors: the inverse of the average (105), the exponential of a real average of logarithms of
   {#B2.2.594} contour products, and the contour product (R̄^j_{0,x_{j+1}}Ū̄^j_1)(Γ_{x_{j+1},x_j}).
   {#B2.2.594-1} Here R is conjugation,
   {#B2.2.595} "R(X)Y=XYX^{-1}" (CMP98 (56), p.27), and R(U₀(Γ^{(j+1)}_{x_{j+1},x})) is the composite of the operations R_{0,y},
   {#B2.2.596} "(R_{0,y}v)(x)=R(V_0(Γ_{y,x}))v(x)" (p.27), and of their analogues R̄^i_{0,·} defined by the averages Ū^i_0 of U₀
   {#B2.2.597} (p.29, the identity after (76)).
   {#B2.2.597-1} At G-valued configurations the averages, exponentials of real averages of
   {#B2.2.598} logarithms, are G-valued, the brackets are G-valued, and conjugation by G-valued contour products keeps them in G,
   {#B2.2.599} so u^0_k, u_{1,±}, and (u_{k,Λ})_± are G-valued.
   {#B2.2.599-1} Every term read at these arguments is continuous in h there: a
   {#B2.2.600} term of an earlier step by (a) of S_{j−1}, and a term produced earlier in step j by (a) for that term, which step 3
   {#B2.2.601} proves in the order in which step j produces its terms.

   {#B2.2.602} *Derivatives at real points.* Let F be a term read in (i)–(iii) that satisfies (a), and let p be a real point of
   {#B2.2.603} D_F at h⁰.
   {#B2.2.603-1} There is a complex polydisc P around p in D_F for all h near h⁰: D_F does not depend on h, except for
   {#B2.2.604} the boundary terms, whose radius in the unscaled field is continuous in h and is not attained at p. On P, F is
   {#B2.2.605} bounded uniformly for h near h⁰ by the bound of its class: RG1 (1.18) for the regular terms, CRE (2.31), p.260,
   {#B2.2.606} for the R-terms, CRE (2.42), p.261, for the boundary terms, LFR1 (1.70), p.192, for the boundary terms 𝐁″_k of the
   {#B2.2.607} N preliminary integrations (LFR2 p.369), LFR2 (1.11), p.358, and (1.47)–(1.48), p.368, for 𝐂_k, and the bound
   {#B2.2.608} (2.42) [III] in d_k(Y₀) of LFR2 p.372 for the terms with localisation domains Y₀ of the first localisation; the
   {#B2.2.609} constants are independent of the history (Lemma 2.10) or continuous in the couplings.
   {#B2.2.609-1} The real points of P are
   {#B2.2.610} real points of D_F for h near h⁰ (the paragraph before (a)), where F converges by (a).
   {#B2.2.610-1} By Montel's theorem and the
   {#B2.2.611} identity theorem, as in step 4, F_h → F_{h⁰} uniformly on compact subsets of P, with all derivatives in the
   {#B2.2.612} configuration variables.
   {#B2.2.612-1} Finitely many such polydiscs cover a compact set of real points of D_F at h⁰, so the field
   {#B2.2.613} derivatives of F converge uniformly on it.

   {#B2.2.614} The localisations also integrate over circles in the auxiliary variables: t_□ with
   {#B2.2.615} |t_□|max{|δ𝐇_j|_X, …} = ⅓α₂ in RG1 (3.15), p.273, t_□ with |t_□|4B₀C₁′e^{16κ₁}g_k|B| = ½α₂ in RG2 (1.22)–(1.23),
   {#B2.2.616} p.7, and σ^ℂ(Δ), RG2's σ(Δ), with |σ^ℂ(Δ)| = e^{κ₁} (RG2 p.7, and RG2 p.8 for (3.15)).
   {#B2.2.616-1} These integrals are the derivatives at
   {#B2.2.617} t_□ = 0 and at s ∈ [0, 1]^{Y₀} of φ_h(t_□, s), the integrand read as a function of (t_□, s) (RG2 (1.9)–(1.10), p.4;
   {#B2.2.618} "We differentiate it with respect to t_□, at t_□ = 0, and we represent all derivatives by the Cauchy formula",
   {#B2.2.619} p.7).
   {#B2.2.619-1} Let D be the open polydisc |t_□|4B₀C₁′e^{16κ₁}g_k|B| < ½α₂ (|t_□|max{|δ𝐇_j|_X, …} < ⅓α₂ for (3.15)),
   {#B2.2.620} |s(Δ)| < e^{κ₁}. On D the field 𝐀 stays in the class (3.31) strictly below α₂ (½α₂ from tζ̃_□ and less than ½α₂
   {#B2.2.621} from t_□ζ_□, RG2 p.7), or in (3.14) (⅓α₂ from 𝐇_j(B(t)) and less than ⅓α₂ from t_□δ𝐇_j, bounds that the localised
   {#B2.2.622} functions keep, RG1 p.273), so φ_h is analytic on D and bounded there by RG1 (3.54) and (3.17), with constants
   {#B2.2.623} independent of the history (Lemma 2.10).
   {#B2.2.623-1} In case (ii), φ_h is the last term of RG1
   {#B2.2.624} (3.34), an integral over
   {#B2.2.625} τ ∈ [0, 1] of fifth B-derivatives, or a term obtained from the Taylor terms of (3.34).
   {#B2.2.625-1} The function
   {#B2.2.626} w ↦ 𝐄^{(j)}(X, U_j(□₀, exp iw)) is analytic on the connected open set 𝒩_w of the w above, bounded by E₀exp(−κd_j(X))
   {#B2.2.627} (RG1 (3.53)–(3.54)), and converges at the real points of 𝒩_w by the paragraph above.
   {#B2.2.627-1} By Vitali's theorem it converges
   {#B2.2.628} uniformly on {τB + B′ : τ ∈ [0, 1], |B′| ≤ ½α₃}, with all its derivatives.
   {#B2.2.628-1} Hence the τ-integral of (3.34) and its
   {#B2.2.629} Taylor terms converge at every real A. The transformations of RG1 §4 act only on the Taylor terms at B = 0 ("such
   {#B2.2.630} expressions only appear in the sum (4.6)", RG1 p.284).
   {#B2.2.630-1} By (4.2)–(4.3), p.281, and the Ward–Takahashi identities
   {#B2.2.631} (4.9)–(4.15), pp.283–284, they are sums of the derivatives δ^n𝐄^{(j)}(X, U_j(□₀, 1))/δB^n, n ≤ 4, at w = 0,
   {#B2.2.632} contracted with B, its differences, and the cutoffs ζ̃_□, which do not depend on h.
   {#B2.2.632-1} So in cases (i) and (ii) φ_h converges at
   {#B2.2.633} the real points of D, which form an open subset of the real points of the connected set D. By Vitali's theorem
   {#B2.2.634} φ_h → φ_{h⁰} uniformly on compact subsets of D, with all its derivatives.
   {#B2.2.634-1} The points t_□ = 0, s ∈ [0, 1]^{Y₀} form a
   {#B2.2.635} compact subset of D, since e^{κ₁} > 1, so the derivatives converge uniformly in s, the integrals ∫_0^1 ds(Δ) of RG2
   {#B2.2.636} (1.10) converge, and the sums over Y₀ converge uniformly in h with the bounds (1.24)–(1.25), p.7, as majorants.

   {#B2.2.637} Case (iii) is treated at real s only.
   {#B2.2.637-1} LFR2 localises twice.
   - {#B2.2.638} *The first localisation* (LFR2 pp.372–373) applies to a term the identity (1.59) or (1.60), "all the
     {#B2.2.639} transformations and estimates of Sects. 3–5 [I]" to the bracket, and "the expansion (6·9) [I]" with σ₀ the cubes
     {#B2.2.640} Δ disjoint with □₀ (or X) and Λ^∼, written "in the form (6.10) [I]" and "estimated as in (6.24)–(6.29) [I]".
     {#B2.2.640-1} It
     {#B2.2.641} treats first the terms of the second part of (1.49), then, with the representations (1.54), (1.57), and (1.58),
     {#B2.2.642} their first terms, and then the remaining terms of the first part of (1.49) and the new terms with localisation
     {#B2.2.643} domains Y₀.
     {#B2.2.643-1} The localised function 𝐇(s) is 𝐇″_k(s, g_kB) of (1.51) in the first pass, around U^0_k, and 𝐇″_k
     {#B2.2.644} of (1.54), 𝐇_{𝐁₁} of (1.57), and 𝐇_k of (1.58) in the repetitions, around U_{1,2}, U_{k,Λ}, and U_k.
   - {#B2.2.645} *The second localisation* (LFR2 pp.373–379) constructs "the localization expansion" of 𝐇″_k, 𝐇_{𝐁₁}, and 𝐇_k
     {#B2.2.646} with the cubes Δ of σ̃₀ disjoint with Λ, "in the form of the expansion (6.10) [I]" (LFR2 pp.373–374), in a term
     {#B2.2.647} 𝐄(X, U^0_k), which "may be any term in the sum" (p.373), at the extended function U^0_k(s) of LFR2 (1.61)–(1.65)
     {#B2.2.648} with the localised functions 𝐇″_k, 𝐇_{𝐁₁}, and 𝐇_k(s(Y′₄)).

   {#B2.2.649} (6.9)–(6.10) [I] are RG2 (1.9)–(1.10), p.4, obtained by "the fundamental theorem of calculus" in each variable
   {#B2.2.650} s(Δ): a term is Π_{Δ∈σ} ∫_0^1 ds(Δ) ∂/∂s(Δ) of the expression at s(σ^c) = 0, and each factor ∫_0^1 ds(Δ) ∂/∂s(Δ)
   {#B2.2.651} is, by that theorem, the difference of the values at s(Δ) = 1 and at s(Δ) = 0.
   {#B2.2.651-1} So a term is the finite alternating
   {#B2.2.652} sum Σ_{Z⊂σ} (−1)^{|σ∖Z|} of the expression at s = 1_Z, the indicator function of Z, a point at which the printed
   {#B2.2.653} expansion evaluates it.
   {#B2.2.653-1} No derivative in s and no complex s is used.
   - {#B2.2.654} The localised functions at s = 1_Z do not depend on the history.
     {#B2.2.654-1} U^0_k is "the configuration in (1.50) with
     {#B2.2.655} B = 0" (LFR2 p.370), a function of the gauge field variables V″ and U^{(AL)}_0 through the background-field map
     {#B2.2.656} U_{𝐁″_k}; U_{1,2}, U_{k,Λ}, and U_k are the background-field maps of (1.53), (1.56), and LFR2 p.365 applied to V″,
     {#B2.2.657} V′_k, M^k(U^{(AL)}_0), V^{(A)}_Λ, and 1 (LFR2 (1.34)–(1.35)), which contain no coupling and are G-valued at G-valued arguments; the localised
     {#B2.2.658} functions come from the results of Sects. D, E of VAR with operators of PBG (LFR2 (1.51),
     {#B2.2.659} (1.54), p.370, and (1.57)–(1.58), p.371), which contain no coupling, and 𝐇″_k(s, g_kB) is read at the unscaled
     {#B2.2.660} field g_kB; and Λ, σ₀, σ̃₀, Ũ^c_k, and Ũ″^c_k carry the parameters of the tube, fixed by the target.
     {#B2.2.660-1} At real
     {#B2.2.661} (𝐔, 𝐉), real B, and s = 1_Z, the configurations of (iii) are real, by the paragraph after the list (i)–(iii).
   - {#B2.2.662} In the second localisation the expression at s = 1_Z is 𝐄(X, U^0_k(1_Z)), a term read at a real point of its
     {#B2.2.663} domain, and it converges by (a) for that term.
   - {#B2.2.664} In the first localisation the expression at s = 1_Z is the bracket of (1.59) or (1.60) with 𝐇(1_Z),
     {#B2.2.665} transformed as in RG1 §§3–5.
     {#B2.2.665-1} As in RG1 (3.34), p.277, these transformations give the Taylor terms of order n ≤ 4
     {#B2.2.666} of the term at the real configuration of the second member of the bracket, contracted with a real field built
     {#B2.2.667} from 𝐇(1_Z), and the integral over τ ∈ [0, 1] of its fifth derivatives at the real configurations between the
     {#B2.2.668} two members, with the weight (1 − τ)⁴/4!; RG1 §4 acts on the Taylor terms as in case (ii).
     {#B2.2.668-1} The term of RG2 (1.10)
     {#B2.2.669} is differentiated in t_□ at t_□ = 0 (RG2 p.7), and this derivative is, by the chain rule, a finite sum of further
     {#B2.2.670} field derivatives at the same real points, contracted with real fields built from 𝐇(1_Z).
     {#B2.2.670-1} These real points form
     {#B2.2.671} a compact set, so each of these expressions converges, by *Derivatives at real points*.

   {#B2.2.672} The sums over Y₀ and the resummations of the first localisation converge with the bounds as in RG2 (1.24)–(1.29),
   {#B2.2.673} pp.7–8, uniform in h by Lemma 2.10, as majorants, the resummation being "controlled by the renormalization procedure
   {#B2.2.674} for 𝐄-terms, the renormalization and the bounds (2.31) [III] for 𝐑-terms, and the bounds (2.42) [III] for
   {#B2.2.675} 𝐁-terms" (LFR2 p.372).
   {#B2.2.675-1} The sums over Y′₂, Y′₃, and Y′₄ and the resummations into the terms V(Y) of the second
   {#B2.2.676} localisation converge with the factors (1.66), LFR2 p.376, which are uniform in h by Lemma 2.10, as majorants, and
   {#B2.2.677} so does the resummed V(X^∼), "in the way discussed in connection with the other terms V(Y)" (LFR2 p.379).
3. {#B2.2.678} *The terms of step j at real points.* At a real point (𝐔, 𝐉) the terms of step j are given as follows.
   - {#B2.2.679} *Fluctuation integrals.* The integrands are the densities of step 1 at real unscaled fields, restricted by the
     {#B2.2.680} characteristic functions to the small fields, whose plaquettes are below ε^T_jη² and whose fluctuation fields obey
     {#B2.2.681} |exp ig_jB_j(b) − 1| < 2δ′^T_j. These fields lie in the real part of the domains, since ε^T_j/α^T_{i,j} and
     {#B2.2.682} δ^T_j/α^T_{i,j} are of order (log ĝ_j^{−2})^{p₀−q_i} and q₀, q₁ > p₀.
     {#B2.2.682-1} The densities are continuous in h by the
     {#B2.2.683} continuity of β_i, i ≤ j, through the top-down formula for g_j(x) (*Histories that are not flows*), by step 2 for
     {#B2.2.684} the localised terms, and by S_{j−1}; the characteristic functions are fixed.
     {#B2.2.684-1} The integrands are bounded uniformly
     {#B2.2.685} for h near h⁰, since the estimates of CRE, LFR1, and LFR2 hold on H_j with constants independent of the history
     {#B2.2.686} (Lemma 2.10), and dominated convergence gives the continuity of each integral.
   - {#B2.2.687} *Small-field terms.* E^{(j+1)}(X) is the exponentiated cluster expansion RG2 (2.13), p.14, at RG2's k = j, in the activities H(Z)
     {#B2.2.688} of RG2 (2.14), p.15: integrals over s(Δ), t(Y) ∈ [0, 1] of Cauchy integrals over circles in σ^ℂ(Δ) and τ(Y), of
     {#B2.2.689} Gaussian integrals over X and B in which "the operators in it are not symmetric, and the second measure is
     {#B2.2.690} complex" (RG2 p.15).
     {#B2.2.690-1} In unscaled fields, at a real point (𝐔, 𝐉) and fixed (σ^ℂ, τ) on the circles, h enters the
     {#B2.2.691} integrand only through the coupling g_k in the Gaussian densities exp(−Q_{σ^ℂ}/(2g_k²)) and their normalisations,
     {#B2.2.692} where the quadratic form Q_{σ^ℂ} of (X, B) does not depend on h (step 1), and through the potentials 𝐕_k(Y, B), read
     {#B2.2.693} at real B and continuous in h by step 2 and S_{j−1}; the characteristic functions χ_{k,Y₀} and χ^c_{k,P} are
     {#B2.2.694} fixed.
     {#B2.2.694-1} So the integrand converges pointwise.
     {#B2.2.694-2} RG2 (2.15)–(2.23), pp.15–17, bound its modulus pointwise by e^C
     {#B2.2.695} times the integrand of (2.23): the forms are compared with those at σ^ℂ(Z) = 0, 𝐔 = U, 𝐉 = 0, and the differences
     {#B2.2.696} and the potentials are bounded by α₅(‖ZX‖² + ‖Z₀B‖²) plus constants ((2.16)–(2.21)), with α₅ so small that the
     {#B2.2.697} form of (2.23) stays positive (RG2 p.17, (2.24)–(2.25)).
     {#B2.2.697-1} In unscaled fields this majorant is a positive Gaussian
     {#B2.2.698} density in which the coupling enters as g_k^{−2} in front of a nonnegative form, so for ½g⁰_k ≤ g_k ≤ 2g⁰_k it is
     {#B2.2.699} at most 4^n times its value at 2g⁰_k, n the number of integration variables.
     {#B2.2.699-1} Dominated convergence over (X, B),
     {#B2.2.700} (σ^ℂ, τ), and (s, t) gives the continuity of H(Z).
     {#B2.2.700-1} By RG2 Lemma 3, (2.38), p.20,
     {#B2.2.701} |H(Z)| ≤ C₃ε₁exp(−(1 − 8δ_{RG2})½Lκd_{k+1}(Z)), uniformly in h, and the series (2.13) is "estimated in the standard
     {#B2.2.702} way" with it (RG2 p.20), so it converges uniformly in h.
   - {#B2.2.703} *R-operation.* The quotients of LFR1 (0.3) and (0.5), p.176, with the densities and normalisers of LFR1 (1.100),
     {#B2.2.704} p.201, are taken at real gauge fields V. Their denominators are integrals of positive densities over nonempty
     {#B2.2.705} domains ("the densities are positive, and the integration domains … are nonempty, hence the denominators are
     {#B2.2.706} positive", LFR1 p.176), continuous in h by the first item, so each quotient and each term R(X, V) of (0.5) is
     {#B2.2.707} continuous.
     {#B2.2.707-1} The new R-terms and boundary terms, LFR2's 𝐑′^{(k)}(X) of (1.98)–(1.100) split by their localisation
     {#B2.2.708} domains (LFR2 p.390), as functions of (𝐔, 𝐉), are the series (1.98) "given by the
     {#B2.2.709} convergent series (7.13) [I]" (LFR2 p.390), that is RG2 (2.13), in the activities F(X′) of LFR2 (1.91), p.388,
     {#B2.2.710} sums over q, the families {X_{j_h}}, and 𝐃 of ∫_0^1 dt(Y) ∏_h T′_k(X_{j_h}) ∏_Y V(Y) exp Σ_Y t(Y)V(Y).
     {#B2.2.711} T′_k(X) is the operation LFR2 (1.71), pp.378–379: an integral over the field B on X with the weight
     {#B2.2.712} (σ_H/σ_H(0))(g_kB)δ_{rT}(B)χ′(X), and over the gauge field V_h with χ_{h,1/2}, of T_h(Z_h ∩ X) applied to the exponential of
     {#B2.2.713} −½⟨DH″_{1,k,X}B, ζDH″_{1,k,X}B⟩ − A((g″_k(·))^{−2}ζ₁⌈_X, U″_{h+2}(exp ig_kB, V″)) + V(X^∼, U_k) + E_k(X) and the
     {#B2.2.714} normalisation constants.
     {#B2.2.714-0} Here σ_H is UV3's Haar density of one bond, a function on 𝔤, and σ₀ = σ_H(0) (#T10.36-4, #T10.36-4-3). LFR2's σ in (1.71) is (σ_H/σ_H(0))(g_kB), the product of (σ_H/σ_H(0))(g_kB(b)) over the bonds b (#T10.36-4) (inferred, not printed): on a bond b, the Haar measure in A = g_kB(b) is σ₀g_k^{dim 𝔤}(σ_H/σ_H(0))(g_kB(b))dB(b), and log(σ₀g_k^{dim 𝔤}) is (1.71)'s −½d(𝐠)log g_k^{−2} + log σ₀ per bond of (𝐁₀∖T₀) ∩ X, d(𝐠) = dim 𝔤 (LFR2 p.379 l.5).
     {#B2.2.714-0a} δ_{rT}(B) fixes B on the bonds of the axial-gauge tree rT of LFR2 p.379 l.9–11.
     {#B2.2.714-1} T_h(Z_h ∩ X) is the ordered product CRE (2.20) of the operations (2.21) of the earlier
     {#B2.2.715} steps, integrals over gauge fields V_j with the Haar measure and over fluctuation fields A_j with Gaussian
     {#B2.2.716} densities.
     {#B2.2.716-1} Of these expressions only the quadratic form in B and V(X^∼) depend on (𝐔, 𝐉) ("only the quadratic
     {#B2.2.717} form in B and the term V(X^∼) depend on (𝐔,𝐉)", LFR2 p.379).
     {#B2.2.717-1} At a real point the integration variables are real,
     {#B2.2.718} and the modulus of the integrand is (σ_H/σ_H(0))(g_kB), bounded on the small unscaled fields that χ′(X) allows, times the exponential of the real part of its exponent.
     {#B2.2.718-1} That real part is bounded
     {#B2.2.719} above uniformly for h near h⁰: the quadratic
     {#B2.2.720} form in B and the Wilson action are nonnegative (ζ, ζ₁ ≥ 0), V(X^∼) is read at the real arguments (iii) of step 2
     {#B2.2.721} and bounded by LFR2 (1.69), and the counterterms and normalisation constants are bounded as on LFR2 p.380, by
     {#B2.2.722} O(log g_j^{−2}) per site of Z_j.
     {#B2.2.722-1} The gauge fields range over compact groups, and the A_j-integrals are the
     {#B2.2.723} Gaussian integrals of LFR2 p.380, whose densities in unscaled fields are exp(−⟨A_j, M_jA_j⟩/(2g_j²)) with M_j
     {#B2.2.724} independent of h (step 1), dominated for g_j ≤ 2g⁰_j by their value at 2g⁰_j.
     {#B2.2.724-1} This gives an integrable majorant,
     {#B2.2.725} uniform for h near h⁰, and dominated convergence gives the continuity of T′_k(X).
     {#B2.2.725-1} The V(Y) are continuous by
     {#B2.2.726} step 2 and bounded by (1.68), so each F(X′) is continuous, and the series converge uniformly in h with
     {#B2.2.727} (1.92)–(1.97) and (1.99)–(1.100) as majorants.
   - {#B2.2.728} *The terms 𝐂_k.* 𝐂_k is "the sum of all these terms, including the term I(U_0) from the denominator" (LFR2
     {#B2.2.729} p.369), the terms "obtained by expanding some Wilson actions" (LFR2 p.369; the expansions are on pp.359–368).
     {#B2.2.729-1} A Wilson action A(c, U) is
     {#B2.2.730} linear in its coupling function c, here (g″_k(·))^{−2} or g_k^{−2}, and the expanded configurations are built
     {#B2.2.731} from the 𝐇-functions of VAR and PBG and the unscaled field g_kB, which contain no coupling (step 1).
     {#B2.2.731-1} So at a real
     {#B2.2.732} point these terms are finite sums of plaquette functions at G-valued configurations with coefficients
     {#B2.2.733} (g″_k(x))^{−2} or g_k^{−2}, continuous in h by the top-down formula (*Histories that are not flows*).
     {#B2.2.733-1} By LFR2
     {#B2.2.734} (1.10), p.358, I(U_0) = E_k(Λ) − (1/g_k²)A(ζ₀, U_0) − log I_Λ, where I_Λ is the integral over V′ on Λ of
     {#B2.2.735} δ_{G₀}(V′)χ exp[−(1/g_k²)A(ζ₀, U_{k,Z}(V′V_Λ))]; δ_{G₀} fixes V′ on the bonds of the graph G₀ (the
     {#B2.2.736} remaining bonds are counted by |Λ^{(k)}∖G₀|, LFR2 p.356), and the remaining variables
     {#B2.2.737} range over a product of copies of G with the Haar measure, on which the integrand is nonnegative, continuous in
     {#B2.2.738} g_k, and bounded by 1.
     {#B2.2.738-1} By LFR2 p.356, I_Λ is exp[−(1/g_k²)A(ζ₀, U_0) + E_k(Λ)] times an integral over B′ that
     {#B2.2.739} LFR2 p.358 bounds below by exp(−O(1)|Λ|), so I_Λ > 0.
     {#B2.2.739-1} Hence I_Λ is continuous in h by dominated convergence, and
     {#B2.2.740} so is I(U_0).
   - {#B2.2.741} *The order of production.* Step j produces its terms in the following order.
     - {#B2.2.742} The N preliminary integrations n = 1, …, N of LFR1: each is a fluctuation integral, "of the same type as the
       {#B2.2.743} integral studied in Sect. 3 [III]", whose result ℂ^{(n)}_k is written "as a sum of localized terms" by the
       {#B2.2.744} results of that section (LFR1 p.189; cases (i)–(ii) of step 2), reading the terms of the earlier steps and
       {#B2.2.745} ℂ^{(i)}_k, i < n; their sum is 𝐁″_k (LFR1 (1.61), p.189).
     - {#B2.2.746} 𝐂_k.
     - {#B2.2.747} The first localisation and its repetitions, of the second part of (1.49), then of the remaining terms of the
       {#B2.2.748} first part and of the new terms with domains Y₀ (step 2, case (iii)).
     - {#B2.2.749} The second localisation, which gives V(Y) and V(X^∼) (step 2, case (iii)).
     - {#B2.2.750} The R-operation, which acts on ρ_j (LFR2 p.391).
     - {#B2.2.751} The renormalisation transformation j → j + 1 of CRE §3 (the fluctuation integrals and small-field terms above,
       {#B2.2.752} cases (i)–(ii) of step 2), which reads the R-terms of that R-operation: they are among the terms
       {#B2.2.753} 𝐑^{(i)}, k₁ < i ≤ j, of R″_j, which CRE p.271 "treated separately", through the s-integral of CRE (3.26),
       {#B2.2.754} p.271, while only R′_j = Σ_{i≤k₁}𝐑^{(i)} is included into E_j.

     {#B2.2.755} Each operation reads only terms of the earlier steps and terms produced before it, so (a) holds for each term by
     {#B2.2.756} the item that treats it, taken in this order.
   {#B2.2.757} So every term produced by step j satisfies (a).
4. {#B2.2.758} *Polydiscs.* Let F be a regular term or an R-term produced by step j, B⁰ admissible, and f_h(B) := F(X, u(B); h)
   {#B2.2.759} on P = P(B⁰).
   {#B2.2.759-1} For real B ∈ P, u(B) is a real point of D_F, so f_h(B) → f_{h⁰}(B) by step 3.
   {#B2.2.759-2} On P, f_h is analytic
   {#B2.2.760} and bounded uniformly for h near h⁰, since u(P) ⊂ D_F, where F satisfies RG1 (1.18), or CRE (2.31), p.260, for
   {#B2.2.761} the R-terms, with constants independent of the history (Lemma 2.10).
   {#B2.2.761-1} By Montel's theorem every sequence h_n → h⁰ has a subsequence along which f_{h_n} converges locally
   {#B2.2.762} uniformly on P. Every limit agrees with f_{h⁰} on the real points of P, which form a nonempty open subset of the
   {#B2.2.763} real space of B, and P is connected; an analytic function on a connected open subset of a complex space that vanishes on a
   {#B2.2.764} nonempty open subset of its real points vanishes identically.
   {#B2.2.764-1} So every limit is f_{h⁰}, and f_h → f_{h⁰} locally
   {#B2.2.765} uniformly on P. This is (b).
5. {#B2.2.766} *The coefficient.* β^T_{k+1} is computed by CRE (3.57) and (3.61), pp.281–282, from the whole-lattice E^{(k+1)},
   {#B2.2.767} through the infinite-volume limit of the polarisation map of #B2.1.10-1, as the torus T^{(k+1)} ↗ ℤ^d ("This limit exists by the localized
   {#B2.2.768} representation (1.7)", RG1 (1.21), p.264).
   {#B2.2.768-1} The limit is taken of Π_{k+1}(x, x′) at fixed x, x′, and β is
   {#B2.2.769} Σ_x Π_{k+1}(x)x_μx_ν (RG1 (1.22)).
   {#B2.2.769-1} Bałaban states the existence of the limit for each history and prints no rate.
   {#B2.2.770} A rate uniform in h comes from the mechanism the sentence names.
   {#B2.2.770-1} RG2 localises the fluctuation-field effective
   {#B2.2.771} action "using the generalized random walk expansions for propagators" (p.1): each propagator is the sum (1.6) over
   {#B2.2.772} walks ω = ((0, X_0), (α_1, X_1), …, (α_n, X_n)) of products R_0(X_0)R_{α_1}(X_1)⋯R_{α_n}(X_n) of local operators on
   {#B2.2.773} simple localisation domains, the term of a walk is bounded by "O(1)O(M₁^{−1/2})^{|ω|}M₁^{−1/2|ω|}exp(−δ₀d(ω, y, y′))"
   {#B2.2.774} (RG2 (1.7), p.3, from PBG (3.107)–(3.108)), the term of ω is multiplied by the decoupling variables s(Δ) of the cubes
   {#B2.2.775} it meets (RG2 p.3), and the localised terms are the s-derivatives and the exponentiated cluster expansion of RG2 §2
   {#B2.2.776} built from these (RG2 pp.13, 21).
   {#B2.2.776-1} Each factor depends on the external configurations restricted to its domain X̃^5_m
   {#B2.2.777} and is built from local inverses: G = G₀(I − R)^{−1} = Σ_n G₀R^n (PBG (3.106), p.414), with R of PBG (3.105) a sum
   {#B2.2.778} over cubes □ of operators formed from the cube-local inverses G_□, the cutoffs h_□ and ζ_□̃, and the projection P,
   {#B2.2.779} which PBG p.415 replaces by its own random walk expansion with local inverses G′ on enlarged cubes and boundary
   {#B2.2.780} conditions outside them (RG2's application of PBG's construction to the chain's propagators, #B9.38–#B9.40-3e).
   {#B2.2.781} Each such factor does not depend on the torus once its side λ_T (in lattice units of the step) exceeds diam X̃^5_m.
   {#B2.2.781-1} So
   {#B2.2.782} within one step, for a fixed polymer X, the torus enters only through walks of total length at least a fixed
   {#B2.2.783} multiple of λ_T, and these are bounded by the same bounds times e^{−c_torλ_T}, with c_tor > 0 fixed by δ₀ and that multiple.
   {#B2.2.784} The inputs of the step also come from the torus: the effective action of the earlier steps, with the R-terms
   {#B2.2.785} R^{(i)} summed over X "in T_ξ" (CRE (2.33), p.260), which the R-operation of LFR1 (0.3)–(0.6) produced.
   {#B2.2.785-1} This is
   {#B2.2.786} handled by induction over the steps, with the claim W_j: every localised regular term and R-term F(X) produced by
   {#B2.2.787} the steps 0, …, j with diam X at most λ_T/3 differs from the term of the same construction
   {#B2.2.788} on L^{−j}ℤ^d, to which CRE extends the sums ("to all domains X ∈ D_j for the space L^{−j}Z^d", CRE p.281), by at
   {#B2.2.789} most C_We^{−c_torλ_T} times its bound, uniformly in h on H_j.
   {#B2.2.789-1} W_{−1} is empty.
   {#B2.2.789-2} In step j+1 the new terms are
   {#B2.2.790} analytic functions of the inputs on the domains of CRE p.259, bounded by the inductive bounds, so by Cauchy
   {#B2.2.791} estimates a change of the inputs by e^{−c_torλ_T} times their bounds changes the outputs by Ce^{−c_torλ_T} times
   {#B2.2.792} theirs; the step's own expansions, including the polymer expansions (0.5) of the R-operation, whose activities
   {#B2.2.793} decay as exp(−κd(X)) (LFR2 pp.388–389), add the winding contributions bounded as above; and terms that wrap the
   {#B2.2.794} torus are bounded by exp(−κd_j(X)) with d_j(X) at least a fixed multiple of λ_T.
   {#B2.2.794-1} The constants are those of
   {#B2.2.795} the steps, uniform in h on H_k (Lemma 2.10).
   {#B2.2.795-1} C_W may grow with j, but only k + 1 steps enter at depth k, and only
   {#B2.2.796} uniformity in h at fixed k is needed here.
   {#B2.2.797} So each term of Π_{k+1}(x; h) = Σ_X Π_X(x; h), the sum over all polymers X (also those not containing 0, which enter
   {#B2.2.798} through the derivatives of the background map, Lemma 2.5, step 3), converges on the torus to its limit at fixed X
   {#B2.2.799} and x uniformly in h.
   {#B2.2.799-1} The proof of Lemma 2.5, steps 3–4, on the tube domains gives the pointwise majorant
   {#B2.2.800} |Π_X(x; h)||x|² ≤ m(X, x) := CE₀r^{−2}e^{−κd_{k+1}(X)}e^{−δ₀(dist(0,X) + dist(x,X))/2}|x|², uniform in h and in
   {#B2.2.801} the torus (with torus distances there), with Σ_{X,x}m(X, x) ≤ C_ΛE₀ < ∞ on ℤ^d.
   {#B2.2.801-1} On the torus of side λ_T, x is
   {#B2.2.802} represented in the fundamental domain (−λ_T/2, λ_T/2]^d, which defines x_μx_ν.
   {#B2.2.802-1} For ε > 0 let 𝓕_ε be a finite set of pairs
   {#B2.2.803} (X, x) of ℤ^d, all within distance R_ε of 0, with Σ_{(X,x)∉𝓕_ε}m(X, x) < ε on ℤ^d.
   {#B2.2.803-1} For λ_T > 8R_ε the pairs of 𝓕_ε are
   {#B2.2.804} identified with torus pairs, and their X have diam X ≤ 2R_ε < λ_T/3, as W_k requires.
   {#B2.2.804-1} Take the torus pairs with
   {#B2.2.805} diam X, dist(0, X), and |x| all at most λ_T/8.
   {#B2.2.805-1} Lift x into the fundamental domain, and X along its paths from a lift of a
   {#B2.2.806} point nearest to 0, at distance ≤ λ_T/8 from 0; then the lifts of x and X lie in the ball of radius λ_T/4 about 0.
   {#B2.2.806-1} So any
   {#B2.2.807} two of their points differ by at most λ_T/2 in each coordinate, and then no translate by λ_Tℤ^d brings them closer in
   {#B2.2.808} any coordinate.
   {#B2.2.808-1} Hence the torus distances dist(0, X), dist(x, X), and diam X equal the ℤ^d distances of the lifts, and so
   {#B2.2.809} does d_{k+1}(X) when its tree graphs have length below λ_T/4 in lattice units (the other pairs go to the remainder
   {#B2.2.810} below): a tree graph is simply connected, so it lifts to ℤ^d with the same length from a point of the lift of X;
   {#B2.2.811} the lifted tree stays within λ_T/4 + λ_T/4 = λ_T/2 of 0 in each coordinate, as no coordinate changes along it by more than its length in any norm of #BK.1, while the other translates of X lie beyond λ_T − λ_T/4 in some coordinate, so
   {#B2.2.812} it meets the cubes of the lift of X, and the ℤ^d value is at most the torus value; the converse inequality is the
   {#B2.2.813} projection.
   {#B2.2.813-1} The lift
   {#B2.2.814} is injective with the same x_μx_ν, so these pairs not in 𝓕_ε contribute less than ε.
   {#B2.2.814-1} Every other torus pair has
   {#B2.2.815} diam X, dist(0, X), or |x| greater than λ_T/8, or only tree graphs of length at least λ_T/4.
   {#B2.2.815-1} In the first case one of dist(0, X), diam X, and dist(x, X) exceeds λ_T/24 (when |x| > λ_T/8, because their sum is at least |x|); d_{k+1}(X) ≥ diam X/(4M) once diam X ≥ 8M, by diam X ≤ M(2d_{k+1}(X) + 4) (#BK.1-1, whose proof holds verbatim with torus distances); and in the second case d_{k+1}(X) ≥ λ_T/(4M), as d_{k+1}(X) is the shortest tree length divided by M.
   {#B2.2.816} So for λ_T ≥ 192M, with c_tor decreased to at most min(δ₀/48, κ/(192M)), the majorant of each such pair carries a factor e^{−c_torλ_T} from its factor e^{−δ₀(dist(0,X) + dist(x,X))/2} or from half of its factor e^{−κd_{k+1}(X)}, and the
   {#B2.2.817} sum of the majorants over them is at most C·poly(λ_T)e^{−c_torλ_T}, with the polymer count absorbed by the other half of the factor
   {#B2.2.818} e^{−κd_{k+1}(X)} as in Lemma 2.5.
   {#B2.2.818-1} On 𝓕_ε the torus terms converge to the ℤ^d terms uniformly in h by W_k (the B-terms
   {#B2.2.819} do not enter Π_{k+1}, which is computed from E^{(k+1)}).
   {#B2.2.819-1} So Σ_xΠ_{k+1}(x; h)x_μx_ν on the torus converges to its
   {#B2.2.820} limit uniformly in h near h⁰.
   {#B2.2.820-1} Each finite-volume value is continuous in h by steps 1–4.
   {#B2.2.820-2} So β^T_{k+1} is continuous. ∎

{#B2.2.821} **Proposition 2.13 (Matching for the Tube Construction).** Let γ be small, and γ′ := (γ^{−2} + C)^{−1/2}.
{#B2.2.821-1} For every K
{#B2.2.822} and every g ∈ (0, γ′] there is a bare coupling g_0 such that the flow of the tube construction for (K, g) has g_K = g
{#B2.2.823} and (x_0, …, x_k) ∈ H_k for all k ≤ K. Along this flow (i) and (ii) of Lemma 2.1 hold.

{#B2.2.824} *Proof.*
1. {#B2.2.825} *Projecting onto the tube.* Let P_k be the Euclidean projection of ℝ^{k+1} onto the closed convex set H_k.
   {#B2.2.825-1} It is
   {#B2.2.826} nonexpansive, hence continuous.
   {#B2.2.826-1} Define the projected flow by x_{k+1} := x_k − β^T_{k+1}(P_k(x_0, …, x_k)), with
   {#B2.2.827} β^T_{k+1} evaluated at the history of the projected point.
   {#B2.2.827-1} Then x_K =: f_K(x_0) is continuous in x_0 by
   {#B2.2.828} Proposition 2.12.
2. {#B2.2.829} *The interval.* By the *Consequence* above, |β^T_{j+1} − b_{j+1}| ≤ δ′ at every history of H_j, so
   {#B2.2.830} Σ_{j=m}^{n−1}β^T_{j+1} ∈ [b(n−m) − C, b′(n−m) + C] for the projected flow, by Theorem 8.1 (Remark 2.3).
   {#B2.2.830-1} This uses
   {#B2.2.831} only that the arguments of β^T lie in H_j, not that the flow itself does.
   {#B2.2.831-1} With m = 0 and n = K,
   {#B2.2.832} f_K(x_0) ∈ [x_0 − b′K − C, x_0 − bK + C].
   {#B2.2.832-1} So f_K(ℓ_0) ≤ t ≤ f_K(u_0), and f_K takes the value t at some x_0 ∈ T_0.
3. {#B2.2.833} *The projection is inactive.* For this solution, step 2 on [m, n) gives b(n−m) − C ≤ x_m − x_n ≤ b′(n−m) + C for
   {#B2.2.834} 0 ≤ m < n ≤ K, and with n = K, x_m ∈ [t + b(K−m) − C, t + b′(K−m) + C] = T_m.
   {#B2.2.834-1} So (x_0, …, x_k) ∈ H_k, P_k is the
   {#B2.2.835} identity at every step, and the projected flow is the flow of the tube construction.
   {#B2.2.835-1} Since ℓ_k ≥ t − C ≥ γ^{−2},
   {#B2.2.836} its couplings lie in (0, γ].
   {#B2.2.836-1} Then (i) is the bound x_k ∈ T_k, and (ii) is the window bound on [k, l). ∎

{#B2.2.837} *What Is Proved for β_j.* For every target (K, g) with g ≤ γ′, the tube construction for (K, g) is CRE's construction
{#B2.2.838} with its parameters evaluated at the couplings ĝ_j of the tube (Lemma 2.10), with the threshold of χ′^{(j)} of LFR1
{#B2.2.839} (1.55) on the unscaled field (*LFR1 (1.55)*, before Lemma 2.10), and with the position-dependent couplings of a
{#B2.2.840} history that is not a flow given by the top-down formula of *Histories that are not flows*.
{#B2.2.840-1} For it:
- {#B2.2.841} item 1 concerns the zero-coupling coefficients b_j only, and holds as stated (Theorem 8.1);
- {#B2.2.842} at every depth k < K, its β^T_{k+1} satisfies (P2) with δ′, and so (W), and item 5 with
  {#B2.2.843} C_rem + C_Rγ^{κ₀−6} on the histories of H_k (*Consequence*);
- {#B2.2.844} at every depth k < K, β^T_{k+1} is continuous on H_k (Proposition 2.12); the tube is not defined at K + 1, and no
  {#B2.2.845} β^T_{K+1} is used;
- {#B2.2.846} item 2 holds: a bare coupling g_0 gives the flow with g_K = g inside H_K (Proposition 2.13);
- {#B2.2.847} items 3 (with δ′ in place of δ) and 4 hold along that matched flow.
{#B2.2.848} This is not a statement about CRE's printed construction, whose parameters jump or move with the couplings, so that
{#B2.2.849} its β_{k+1} is not known to be a continuous function of the history (*CRE's Construction as a Function of the History*).
{#B2.2.849-1} The construction depends on the target (K, g): the parameters, the
{#B2.2.850} densities ρ_k, the effective actions, the coefficients β^T, the couplings g_k, and the bare coupling g_0 are those of
{#B2.2.851} the tube of (K, g), and objects of different targets are not identified with each other.
{#B2.2.851-1} The constants in the bounds (C_Λ, C₃, C_rem, C′, C_Σ, K_V,
{#B2.2.852} C_R, δ′, and C₀) are independent of K and g.
{#B2.2.852-1} Statements that combine several targets, such as a limit K → ∞ at fixed
{#B2.2.853} physical scale, use only these uniform bounds and the properties of each target's own construction.

{#B2.2.854} **Proposition 2.14 (The Second-Order Form of β^T).** There are numbers ā_1, ā_2, … with |ā_k| ≤ C_a, depending on k and on no coupling, cutoff, or tube, and a constant C_e, uniform over the class of tubes, such that for γ small, every tube of the class, every k < K, and every (x_0, …, x_k) ∈ H_k, with h = (x_0^{−1/2}, …, x_k^{−1/2}),
  {#B2.2.855} β^T_{k+1}(h) = b_{k+1} + ā_{k+1}g_k² + e_{k+1}(h),  |e_{k+1}(h)| ≤ C_eg_k³.

{#B2.2.856} *Proof.*
1. {#B2.2.857} *The Gaussian input.* In RG1 (1.3), p.260, the input of step k consists, for each j < k, of −β_{j+1}A(U_k), the Gaussian term log Z^{(j)}(U_k) − log Z^{(j)}(1), and the fluctuation term E^{(j+1)}_fl(U_k) − E^{(j+1)}_fl(1) (#B2.1.1–#B2.1.2). Let E_k^{(0)} be this input with every fluctuation term replaced by 0 and every β_{j+1} by b_{j+1}.
   {#B2.2.857-1} Its fluctuation terms vanish, its Gaussian terms are those of RG1's construction, bounded by ½E₀ (#B2.2.447), and each counterterm −b_{j+1}A(U_k) is paired with its Gaussian term, b_{j+1} = Λ(log Z^{(j)}) (Proposition 2.4, step 1), the pairing that gives RG2 (1.24) its factor (L^jη)⁵.
   {#B2.2.857-2} So it satisfies RG1 (1.18) with this pairing, and Proposition 2.9(b), whose proof uses the input of step k only through these and the analyticity on RG1's domains (Proposition 2.4, step 2; Lemma 2.7), gives the coefficient ā_{k+1} of this input, with |ā_{k+1}| ≤ C_a. E_k^{(0)} contains no coupling and no cutoff (b_{j+1} and log Z^{(j)} are Gaussian), and ā_{k+1} is a limit in the cutoff of step k, so ā_{k+1} depends on k only.
2. {#B2.2.858} *Split.* With β^{δ,T} as in Proposition 2.11 and a_{k+1}(h) its coefficient from Proposition 2.9(b), e_{k+1}(h) = [β^T_{k+1} − β^{δ,T}_{k+1}] + [β^{δ,T}_{k+1} − b_{k+1} − a_{k+1}(h)g_k²] + [a_{k+1}(h) − ā_{k+1}]g_k².
   {#B2.2.858-1} The first term is at most C_Rg_k^{κ₀−4} ≤ C_Rg_k³ (Proposition 2.11, κ₀ ≥ 7), and the second at most C′_remg_k⁴ (Proposition 2.9(b) for RG1's construction with δ_j^T on H_k, Lemma 2.10, step 7).
3. {#B2.2.859} *The history part of the input.* The input of step k of β^{δ,T} is E_k^{(0)} + Σ_{j<k}F^h_j, where F^h_j is the fluctuation term of step j together with −(β_{j+1} − b_{j+1})A(U_k). The activities E(X; z, p_j) of step j, p_j := δ_j^T/g_j, are even and analytic in z on |z| < ε*/p_j and bounded there by O(1)C₃ε*exp(−κd_{j+1}(X)) on U^c_{j+1}(X, α₀, α₁) (Lemma 2.7), and at z = 0 by C₅exp(−γ₂p_j²/20)exp(−κd_{j+1}(X)) ≤ g_j⁴exp(−κd_{j+1}(X)) (Lemma 2.8; Proposition 2.9, step 6).
   {#B2.2.859-1} Since g_jp_j = δ_j^T ≤ ε*/2, step 2 of Proposition 2.9 bounds the fluctuation term of step j by C_Fp_j²g_j²exp(−κd_{j+1}(X)), with C_F := 2O(1)C₃/ε* + 1 + C_rem; and |β_{j+1} − b_{j+1}| ≤ C_remg_j² (Proposition 2.9(a)). The counterterm of F^h_j is Λ of its fluctuation term (Proposition 2.4, step 1), as RG1 §§4–5 pair them (RG1 p.298 l.4–5).
   {#B2.2.859-2} On H_k, x_j ≥ x_k − C ≥ (6/7)x_k for j < k (C ≤ x_k/7, as in Proposition 2.11, step 3), p_j ≤ 2A₁(log x_j)^{p₀} and p_k ≥ ρ_γ^{−1/2}A₁(log x_k)^{p₀} (Lemma 2.10(e)), and x ↦ (log x)^{2p₀}/x is decreasing for log x ≥ 2p₀. So p_j²g_j² ≤ 4·(7/6)ρ_γp_k²g_k² ≤ 7p_k²g_k². With ε_k^F := 7C_Fp_k²g_k²/E₀, the fluctuation term of every F^h_j satisfies RG1 (1.18) with ε_k^FE₀ in place of E₀, and its counterterm coefficient is at most C_remg_j² ≤ (7/6)C_remg_k² ≤ ε_k^FE₀, as C_F ≥ C_rem and p_k ≥ 1 for γ small.
4. {#B2.2.860} *Cauchy in s.* For s ∈ ℂ let step k run with the input E_k^{(0)} + sΣ_{j<k}F^h_j. Λ is linear, so the counterterm of sF^h_j is Λ of its fluctuation term, as in step 3.
   {#B2.2.860-1} For |s| < 1/ε_k^F this input satisfies RG1 (1.18) with 2E₀, which the step accepts (Proposition 2.11, step 4, and *The Step with Complex Multiples of the R-Terms*), and the activities are analytic in s (as in Proposition 2.11, step 4).
   {#B2.2.860-1a} Proposition 2.9(b), run with ε′* ≤ ε* such that A_χε′* satisfies the conditions of Proposition 2.4, step 4 with 2E₀ in place of E₀ (among them RG2 p.18 l.9 and p.20 l.6) and then q′_th ≥ q_th under those of Lemma 2.8 for ε′*, gives a_{k+1}(s), a uniform limit of analytic functions, hence analytic on |s| < 1/ε_k^F, with |a_{k+1}(s)| ≤ C′_a, the constant C_a with ε′*, q′_th, and 2E₀ for E₀ (in C₃, hence M₀, and in C₄); a_{k+1}(s) is a limit in q, so it does not depend on the radius used to bound it; a_{k+1}(1) = a_{k+1}(h) and a_{k+1}(0) = ā_{k+1}.
   {#B2.2.860-2} Take γ so small that ε_k^F ≤ ¼. The disc of radius 1/(2ε_k^F) about each s₀ ∈ [0, 1] lies in |s| < 1/ε_k^F, so |a′_{k+1}(s₀)| ≤ 2C′_aε_k^F and |a_{k+1}(h) − ā_{k+1}| ≤ 2C′_aε_k^F.
5. {#B2.2.861} *Constants.* |e_{k+1}(h)| ≤ C_Rg_k³ + C′_remg_k⁴ + 14C′_aC_Fp_k²g_k⁴/E₀ ≤ C_eg_k³, with C_e := C_R + C′_rem + 14C′_aC_F/E₀, once p_k²g_k ≤ 1, which holds for γ small. Each constant is uniform over the class. ∎

{#B2.2.862} Along a history of H_K, ℓ_k = t + b(K−k) − C ≥ (7/8)t + c ln L·(K−k), so Σ_{k<K}g_k³ ≤ Σ_{k≤K}ℓ_k^{−3/2} ≤ ((7/8)t)^{−3/2} + 2((7/8)t)^{−1/2}/(c ln L), and Σ_{k<K}|e_{k+1}| ≤ 3C_et^{−1/2}(1 + 1/(c ln L)) along every tube flow.

## 3. Exact One-Loop Decomposition {#BS3}

### 3.1 Linear-Algebra Setting {#BS3.1}

{#B3.1.1} All spaces are finite-dimensional real inner-product spaces.
{#B3.1.1-1} In the applications they are the fields on one momentum
{#B3.1.2} coset 𝒪 ≠ ℤp of a finite torus, and infinite volume is handled in Remark 3.4.
- {#B3.1.3} X: fine Lie-algebra-valued 1-forms.
  {#B3.1.3-1} Y: fine 0-forms, taken orthogonal to ker D.
- {#B3.1.4} D: Y → X, injective; this is D_U, the linearised gauge action at the background U.
- {#B3.1.5} h: X → X symmetric, with h ≥ 0, hD = 0, and h positive definite on (ran D)^⊥.
- {#B3.1.6} Q: X → Z onto, the linearised k-fold average (Z: level-k coarse 1-forms).
- {#B3.1.7} P: Y → Ȳ, restriction to level-k sites (L is odd, RG1 p.251 l.14, so these are fine sites).
  {#B3.1.7-1} PPᵀ = 1.
- {#B3.1.8} D̄: Ȳ → Z, injective (orthogonal to coarse constants).
- {#B3.1.9} **Covariance:** QD = D̄P.
  {#B3.1.9-1} (The chain's average is RG1 (0.4) or (0.12) (CRE p.243).
  {#B3.1.9-2} In both, the averaged loops are
  {#B3.1.10} based at c₋: Γ ∪ [x, x′] ∪ (−Γ′) ∪ (−c) in (0.4), and the loop of the contour variables of RG1 (0.11) in (0.12),
  {#B3.1.11} which transform as U(y, x) ↦ u(y)U(y, x)u(x)^{−1} by (0.6).
  {#B3.1.11-1} So Ū^u(c) = u(c₋)Ū(c)u(c₊)^{−1}; QD = D̄P is its
  {#B3.1.12} linearisation, iterated over the k steps.)
- {#B3.1.13} Y_0 := ker P, the residual gauge algebra (gauge transformations trivial at level-k sites); D_0 := D|_{Y_0}.

{#B3.1.14} **One-loop factor.** In Bałaban's normalisation (axial gauge in blocks, Faddeev–Popov determinant 1, group δ-function
{#B3.1.15} linearised to δ(QA)), the one-loop factor of the k-step constrained integral is

  {#B3.1.16} Z_k[h] = c_sl · det(QQᵀ)^{−1/2} · det(h|_W)^{−1/2} · det(D_0ᵀD_0)^{1/2},  W := ker Q ⊖ D(Y_0).

{#B3.1.17} Here c_sl does not depend on the background.
{#B3.1.17-1} *Reason.* The axial slice meets each residual orbit once, and the map
{#B3.1.18} (slice, ω) ↦ A_s + Dω has block-triangular Jacobian with determinant det D_tree, D_tree being ω ↦ Dω restricted to the bonds of the axial-gauge trees; with the tree bonds ordered from the level-k sites outwards, D_tree is triangular with orthogonal diagonal blocks, so |det D_tree| = 1.
{#B3.1.18-1} So the slice integral equals
{#B3.1.19} ∫ e^{−½⟨A,hA⟩} δ(QA) dA divided by ∫_{Y_0} dω.
{#B3.1.19-1} The δ-integral equals det(QQᵀ)^{−1/2} ∫_{ker Q}.
{#B3.1.19-2} Splitting
{#B3.1.20} ker Q = W ⊕ D(Y_0) with the induced orbit measure det(D_0ᵀD_0)^{1/2} dω gives the formula.

{#B3.1.21} **Definitions.** For each level j:
- {#B3.1.22} Δ_j is the quadratic form on Z_j given by ⟨z, Δ_j z⟩ := min{⟨A, hA⟩ : Q_j A ∈ z + ran D̄_j}; it depends only on z modulo ran D̄_j, and det_⊥(Δ_j) is its determinant on Z_j ⊖ ran D̄_j.
  {#B3.1.22-1} It is the
  {#B3.1.23} gauge-invariant coarse action of level j.
  {#B3.1.23-1} At U = 1 it is Bałaban's ⟨B, Δ_j B⟩ = ⟨∂H_jB, ∂H_jB⟩ (PRT1 (1.65), p.29 l.14; ∂ as in §4's Notation).
- {#B3.1.24} F_j := ½ log det_⊥(Δ_j) − ½ log det(D̄_jᵀD̄_j).
- {#B3.1.25} At level 0 (Q_0 = 1, D̄_0 = D): Δ_0 = h, as hD = 0, so F_0 = ½ log det_⊥(h) − ½ log det(DᵀD), det_⊥ the determinant on (ran D)^⊥.

### 3.2 The Identity {#BS3.2}

{#B3.2.1} **Proposition 3.1.** log Z_k[h] = F_k − F_0 + const.

{#B3.2.2} *Proof.* Let K := ker Q and Δ_F := h + DDᵀ, which is invertible.
{#B3.2.2-1} Then Δ_F D = D(DᵀD), hence
{#B3.2.3} Δ_F^{−1}D = D(DᵀD)^{−1}.
{#B3.2.3-1} Write S := QΔ_F^{−1}Qᵀ and R := P(DᵀD)^{−1}Pᵀ.

1. {#B3.2.4} *Feynman form.* Define h_F := Π_K(h + D_0D_0ᵀ)Π_K on K, where D_0D_0ᵀ = D(1−PᵀP)Dᵀ.
   {#B3.2.4-1} Decompose
   {#B3.2.5} K = W ⊕ D(Y_0).
   {#B3.2.5-1} Then h(D Y_0) = 0, ⟨Dω, hw⟩ = 0, and D_0ᵀw = 0 for w ∈ W. So h_F = h|_W ⊕ (D_0D_0ᵀ)|_{D(Y_0)} and
   {#B3.2.6} det h_F = det(h|_W)·det(D_0ᵀD_0).
   {#B3.2.6-1} Therefore

     {#B3.2.7} log Z_k = −½ log det(QQᵀ) − ½ log det h_F + log det(D_0ᵀD_0) + const.

2. {#B3.2.8} *Ghost (Schur).* On Y = Y_0 ⊕ ran Pᵀ: det(DᵀD) = det(D_0ᵀD_0) · det((P(DᵀD)^{−1}Pᵀ)^{−1}).
   {#B3.2.8-1} Hence

     {#B3.2.9} det(D_0ᵀD_0) = det(DᵀD) · det R.

3. {#B3.2.10} *Constraint.* h_F = Π_K(Δ_F − DPᵀPDᵀ)Π_K.
   {#B3.2.10-1} Two standard identities:
   - {#B3.2.11} det(Π_KΔ_FΠ_K) = det Δ_F · det S / det(QQᵀ) (constrained Gaussian);
   - {#B3.2.12} the matrix determinant lemma: det h_F = det(Π_KΔ_FΠ_K) · det_Ȳ(1 − N_Ȳ), with N_Ȳ := PDᵀ C DPᵀ and
     {#B3.2.13} C := Δ_F^{−1} − Δ_F^{−1}QᵀS^{−1}QΔ_F^{−1} (the inverse of Π_KΔ_FΠ_K on K, extended by 0).

   {#B3.2.14} Using Δ_F^{−1}D = D(DᵀD)^{−1} and QΔ_F^{−1}D = D̄P(DᵀD)^{−1}:
   - {#B3.2.15} DᵀCD = 1 − (DᵀD)^{−1}PᵀD̄ᵀS^{−1}D̄P(DᵀD)^{−1};
   - {#B3.2.16} hence 1 − N_Ȳ = R D̄ᵀ S^{−1} D̄ R, and det_Ȳ(1 − N_Ȳ) = (det R)² det(D̄ᵀS^{−1}D̄).
4. {#B3.2.17} *Collecting.* The factors det(QQᵀ) cancel, and so do the factors det R (−½·2 log det R + log det R = 0):

     {#B3.2.18} log Z_k = [−½ log det Δ_F + log det(DᵀD)] + [−½ log det S − ½ log det(D̄ᵀS^{−1}D̄)] + const.

5. {#B3.2.19} *First bracket.* On X = ran D ⊕ (ran D)^⊥, Δ_F = (DDᵀ)|_{ran D} ⊕ h|_⊥.
   {#B3.2.19-1} So the first bracket equals
   {#B3.2.20} −½ log det_⊥ h + ½ log det(DᵀD) = −F_0.
6. {#B3.2.21} *Second bracket.* Let M := S^{−1}, so ⟨z, Mz⟩ = min{⟨A, Δ_F A⟩ : QA = z}.
   {#B3.2.21-1} Decompose Z = ran D̄ ⊕ (ran D̄)^⊥:
   - {#B3.2.22} det M = det(M_∥) · det(M/M_∥), with det(M_∥) = det(D̄ᵀMD̄)/det(D̄ᵀD̄).
   - {#B3.2.23} So the second bracket equals ½ log det(M/M_∥) − ½ log det(D̄ᵀD̄).
   - {#B3.2.24} The Schur complement is (M/M_∥)(z) = min over A with QA ∈ z + ran D̄ of ⟨A, (h + DDᵀ)A⟩.
     {#B3.2.24-1} That set is invariant under
     {#B3.2.25} A ↦ A + Dω (QDω = D̄Pω ∈ ran D̄).
     {#B3.2.25-1} Since h is gauge-invariant, choose ω = −(DᵀD)^{−1}DᵀA to make DᵀA = 0.
     {#B3.2.25-2} So
     {#B3.2.26} M/M_∥ = Δ_k, and the second bracket equals F_k.

{#B3.2.27} Check: k = 0 gives log Z_0 = 0 (the constraint fixes everything). ∎

{#B3.2.28} **Corollary 3.2 (Steps).** Let Q̃ be the linearised one-step average from level k to level k + 1 and P̃ the restriction from level-k to level-(k+1) sites, so that Q_{k+1} = Q̃Q_k (the averages compose, #T10.13-3) and P_{k+1} = P̃P_k. Let Z^{(k)}[h], the one-loop factor of step k + 1, be #B3.1.16 with one step at level k: X, h, Y, D, Q, P and D̄ replaced by Z_k, Δ_k, Ȳ_k (§3.1's Ȳ at level k), D̄_k, Q̃, P̃ and D̄_{k+1}. Then

  {#B3.2.31} **log Z^{(k)}[h] = F_{k+1} − F_k + const,**

{#B3.2.29} and Σ_{j<k} log Z^{(j)}[h] = log Z_k[h] + const. *Proof.* The replacements satisfy §3.1's hypotheses: Δ_k vanishes on ran D̄_k and is positive on its orthogonal complement (Lemma 3.3 below, whose proof does not use this corollary), so Δ_kD̄_k = 0; Q̃ is onto, as Q_{k+1} = Q̃Q_k is; P̃P̃ᵀ = 1; D̄_k and D̄_{k+1} are injective; and Q̃D̄_kP_k = Q̃Q_kD = Q_{k+1}D = D̄_{k+1}P̃P_k, with P_k onto, gives Q̃D̄_k = D̄_{k+1}P̃.
{#B3.2.29-1} So Proposition 3.1 applies with one step. Its level-0 functional is ½ log det_⊥(Δ_k) − ½ log det(D̄_kᵀD̄_k) = F_k. Its level-1 form is min{⟨z′, Δ_kz′⟩ : Q̃z′ ∈ z + ran D̄_{k+1}} = min{⟨A, hA⟩ : Q_{k+1}A ∈ z + ran D̄_{k+1}} = ⟨z, Δ_{k+1}z⟩, as Q̃(ran D̄_k) = D̄_{k+1}P̃(Ȳ_k) ⊂ ran D̄_{k+1} (take z′ = Q_kA for the converse); so its level-1 functional is F_{k+1}.
{#B3.2.30} Summing over j < k and comparing with Proposition 3.1 gives the second identity. ∎

{#B3.2.32} **Lemma 3.3 (Full-Space Form).** Δ_k vanishes on ran D̄ and is positive on (ran D̄)^⊥.
{#B3.2.32-1} *Proof.* Δ_k ≥ 0 depends only on z modulo ran D̄ (#B3.1.22), so, by polarisation, it vanishes on ran D̄ and maps (ran D̄)^⊥ into itself. If ⟨z, Δ_kz⟩ = 0, a minimiser A (on a finite-dimensional affine subspace, a convex quadratic function bounded below attains its infimum) has ⟨A, hA⟩ = 0; as hD = 0 and h is positive definite on (ran D)^⊥, A = Dω for some ω, and z ∈ Q_kDω + ran D̄ = D̄Pω + ran D̄ = ran D̄. Hence, as D̄D̄ᵀ vanishes on (ran D̄)^⊥ and has determinant det(D̄ᵀD̄) on ran D̄,
{#B3.2.33} log det_⊥ Δ_k = log det(Δ_k + D̄D̄ᵀ) − log det(D̄ᵀD̄), and

  {#B3.2.34} **F_k = ½ log det(𝒟_k) − log det(D̄ᵀD̄),  𝒟_k := Δ_k + D̄D̄ᵀ.**

{#B3.2.35} **Remark 3.4 (Finite Tori and Infinite Volume).** The symbols of §§4–8 are infinite-volume momentum integrals.
{#B3.2.35-1} A
{#B3.2.36} finite torus serves only to prove identities between them, and it is used one momentum coset at a time.
- {#B3.2.37} *The defect at U = 1.* Let T be the coarsest lattice of the quantity at hand (T^{(k+1)} in §4, the top lattice in
  {#B3.2.38} §§5–8), a torus of side N. Let B = t(a e^{ip·y} + c.c.) be a plane wave with p ∈ (2π/N)ℤ⁴, p ≢ 0 mod 2π, and
  {#B3.2.39} a ∈ g^c ⊗ ℂ⁴.
  {#B3.2.39-1} At U = 1, ker D consists of the constant 0-forms, and the constant 1-forms lie in (ran D)^⊥ ∩ ker h.
  {#B3.2.40} For t ≠ 0, ker D_U consists of the parallel sections.
  {#B3.2.40-1} For a = e₁w with 0 ≠ w ∈ g and p₂ ≢ 0, some plaquette holonomies
  {#B3.2.41} are exp(sw) with small s ≠ 0, so these sections take values in the centraliser z(w), a proper subspace of g.
  {#B3.2.41-1} So on
  {#B3.2.42} the whole torus Y, Π_⊥, and h jump at t = 0.
  {#B3.2.42-1} D_UᵀD_U has dim g − dim z(w) nonzero eigenvalues of order at most t²
  {#B3.2.43} (from the constants orthogonal to z(w)), so log det(D_UᵀD_U) is unbounded as t → 0, and §3.1's hypotheses fail.
- {#B3.2.44} *Cosets.* B is invariant under the translations in T_p := {y ∈ T : e^{ip·y} = 1}.
  {#B3.2.44-1} Every operator of §§3–7 (D_U, Q(U),
  {#B3.2.45} P, D̄_V, Hess A(U), Π_⊥, h, Bałaban's Δ^{(k)}(U), 𝒫, 𝐆^{(2)}, their inverses, and the minimiser maps) is a
  {#B3.2.46} translation-covariant function of the background, so it commutes with T_p; so does J(U).
  {#B3.2.46-1} Decompose the fields of
  {#B3.2.47} every level into Bloch fibres of quasi-momentum p′ ∈ (2π/N)ℤ⁴ mod 2π under the translations of T. Each fibre is
  {#B3.2.48} finite-dimensional.
  {#B3.2.48-1} The characters of T that are trivial on T_p are the multiples of p, so every such operator is
  {#B3.2.49} block-diagonal in the cosets 𝒪 := p′ + ℤp.
  {#B3.2.49-1} Write X_𝒪, Y_𝒪, … for the real fields with quasi-momenta in 𝒪 ∪ (−𝒪).
- {#B3.2.50} *Away from the zero coset.* Let 𝒪 ≠ ℤp.
  {#B3.2.50-1} Then no fibre in 𝒪 ∪ (−𝒪) is 0 mod 2π.
  {#B3.2.50-2} On a nonzero fibre at U = 1, D and D̄
  {#B3.2.51} are injective, and h is positive on (ran D)^⊥, since its kernel there consists of harmonic 1-forms, which are
  {#B3.2.52} constant.
  {#B3.2.52-1} The space X_𝒪 is finite-dimensional.
  {#B3.2.52-2} Every T_p-invariant background U leaves X_𝒪 invariant, and the
  {#B3.2.53} operators are real-analytic functions of the link variables, with inverses taken where invertible.
  {#B3.2.53-1} So for
  {#B3.2.54} T_p-invariant U in a neighbourhood of 1 (depending on N and p), these properties persist, and the restrictions to
  {#B3.2.55} X_𝒪 of all the operators are real-analytic in U, hence in t, and in j for T_p-invariant fine 1-forms j.
  {#B3.2.55-1} So §3.1's
  {#B3.2.56} hypotheses hold on 𝒪, with Y = Y_𝒪 (QD = D̄P holds for all 0-forms, and PPᵀ = 1 fibrewise).
  {#B3.2.56-1} Proposition 3.1,
  {#B3.2.57} Corollary 3.2, and Lemma 3.3 hold on 𝒪, with constants independent of U.
- {#B3.2.58} *Coset sums.* On 𝒪 ≠ ℤp, the second-order Taylor coefficient in t of each quantity of §§3–7, restricted to X_𝒪, is
  {#B3.2.59} Σ_{p′∈𝒪∪(−𝒪)} ℳ(p′, p).
  {#B3.2.59-1} Here ℳ is the one-loop integrand of its Bloch form, with internal lines at p′ and p′ + p:
  {#B3.2.60} Proposition 4.2(d) for J^{(k)}, Proposition 7.1(f) for F_k with k ≥ 1, and, for F_0, the form below.
  {#B3.2.60-1} For N larger than the ranges of the local operators, the fibre of each operator at
  {#B3.2.61} U = 1 is its infinite-volume symbol, since inverses, projections, and Schur complements are taken fibrewise.
  {#B3.2.61-1} Put
  {#B3.2.62} Π^N(p) := N^{−4} Σ_{p′∉ℤp} ℳ(p′, p).
  {#B3.2.62-1} The sets 𝒪 ∪ (−𝒪) with 𝒪 ≠ ℤp partition the p′ ∉ ℤp, so the identities of
  {#B3.2.63} Proposition 3.1, Corollary 3.2, and Lemma 3.3, which hold on each of them, hold exactly for Π^N.
- {#B3.2.64} *The form of F_0.* At level 0 (Q = 1, D̄ = D), Proposition 7.1(a) reads, on each 𝒪 ≠ ℤp, with T₀ := (ran D(1))^⊥
  {#B3.2.65} and P_T its projection, F_0 = ½ log det_{T₀}(P_ThP_T) − ½ log det_{T₀}(P_TΠ_UP_T) − ½ log det(D_UᵀD_U).
  {#B3.2.65-1} At U = 1,
  {#B3.2.66} P_TD = 0, DᵀP_T = 0, and Hess A(1)D = 0.
  - {#B3.2.67} Write h = Hess A − Π_DHess A − Hess AΠ_D + Π_DHess AΠ_D with Π_D = D(DᵀD)^{−1}Dᵀ, and expand P_ThP_T to second
    {#B3.2.68} order.
    {#B3.2.68-1} A D next to P_T, a Dᵀ next to P_T, and a Dᵀ Hess A or Hess A D at U = 1 vanish.
    {#B3.2.68-2} So the first-order vertex is
    {#B3.2.69} P_T(Hess A)₁P_T, which is regular, and every second-order term contains at most one (DᵀD)^{−1}, between two factors
    {#B3.2.70} that each carry an external leg.
    {#B3.2.70-1} The propagator (P_ThP_T)^{−1} on T₀ is the inverse of the coexact Laplacian.
  - {#B3.2.71} The second-order part of log det_{T₀}(P_TΠ_UP_T) is −Tr(P_TD₁(DᵀD)^{−1}D₁ᵀP_T), as in Proposition 7.1(e), and
    {#B3.2.72} log det(D_UᵀD_U) has propagators (DᵀD)^{−1} with vertices (DᵀD)₁ and (DᵀD)₂.
  - {#B3.2.73} So in this form every factor of degree 2 sits on one internal line, and the integrand has degree at most 2 at
    {#B3.2.74} each of p′ = 0 and p′ = −p.
- {#B3.2.75} *Infinite volume.* ℳ(·, p) is continuous away from p′ ∈ {0, ∓p} mod 2π, and has singularities of degree at most 2
  {#B3.2.76} there (Proposition 4.2(d), degree count; Proposition 7.1(f); for F_0, the form above).
  - {#B3.2.77} Since d = 4, the grid points within distance r of a singular point contribute at most Cr² to Π^N, uniformly in N.
  - {#B3.2.78} p is fixed along the sequence of N, so p ∈ 2πℚ⁴ has a fixed order m₀ in ℝ⁴/2πℤ⁴, and ℤp consists of m₀ points
    {#B3.2.79} independent of N. Apart from 0 and ∓p they are not singular, so |ℳ| ≤ C_p there, and ℤp would contribute at most
    {#B3.2.80} C_pm₀N^{−4}.
  - {#B3.2.81} Hence Π^N(p) → ∫_{[−π,π]⁴} ℳ(p′, p) d⁴p′/(2π)⁴ as N → ∞ through the N with p ∈ (2π/N)ℤ⁴.
    {#B3.2.81-1} These integrals are the
    {#B3.2.82} symbols of §§4–8.
    {#B3.2.82-1} In §7 the external momentum is p₀ and the internal one p.
  - {#B3.2.83} The integrals are continuous in p ≢ 0: for p in a compact set avoiding 2πℤ⁴, the integrals of the bounds over
    {#B3.2.84} r-neighbourhoods of the singular points are O(r²) uniformly in p. So the identities extend from the dense set
    {#B3.2.85} ⋃_N (2π/N)ℤ⁴ to every p ≢ 0.
    {#B3.2.85-1} The symbol of J^{(k)} (Proposition 4.2) extends continuously to p = 0 (Lemma 4.3).

### 3.3 Which h Is Meant: J-Terms {#BS3.3}

{#B3.3.1} Bałaban's step Gaussian is taken at the constrained minimiser U* = U_{k+1}(e^{iB}), where ∇A(U*) = Qᵀλ ≠ 0.
{#B3.3.1-1} Its
{#B3.3.2} quadratic form is the Lagrangian Hessian h_L = Hess A − ⟨λ, Hess M^{k+1}⟩ on the constraint tangent space, modulo the
{#B3.3.3} residual gauge directions, with M^{k+1} the (k+1)-fold average map (#T10.13-3), whose differential at U* is the Q of §3.1 with k + 1 in place of k, and λ the Lagrange multiplier.
{#B3.3.3-1} RG1 (1.5), p.261 l.5–6, writes this out: the J-term is −2⟨H_{1,j}h_BC̃^{(2)}(Ū^j_k, B), J⟩, with H_{1,j} and h_B as in #T10.21 (h_B, RG1's operator h, is not this section's h), C̃^{(2)} as in #T10.21-2, and J the current
{#B3.3.4} (RG1 (1.8)).

{#B3.3.5} Throughout, h := Π_⊥ Hess A(U) Π_⊥ (Π_⊥ onto (ran D_U)^⊥).
{#B3.3.5-1} This form is gauge-invariant (hD = 0), the same for all
{#B3.3.6} levels, and involves no λ.
{#B3.3.6-1} The Hessian of a gauge-invariant function transforms covariantly even off-shell, because
{#B3.3.7} the coordinates X ↦ U e^{iX} transform linearly.
{#B3.3.7-1} Differentiating ⟨∇A, Dω⟩ ≡ 0 shows that
{#B3.3.8} h_L − h = (terms linear in ∇A(U) or λ), and λ = (QQᵀ)^{−1}Q∇A.
{#B3.3.8-1} Define the **step J-term**

  {#B3.3.9} J^{(k)}(U) := log Z^{(k)}(U) − (F_{k+1} − F_k)(U),  Z^{(k)}(U) Bałaban's step factor (#T10.13-4).

## 4. The J-Terms Do Not Contribute to the Marginal Coefficient {#BS4}

{#B4.1} **Notation.** "Symbol" means the Fourier multiplier on the coarse lattice (unit spacing, momentum p ∈ [−π, π]⁴) of a
{#B4.2} translation-covariant linear map, or of a quadratic form's kernel.
{#B4.2-1} The second-order Taylor coefficient in B of a
{#B4.3} function of the coarse field B has the symbol Π(p) (the polarisation).
{#B4.3-1} The marginal coefficient is read off from the
{#B4.4} O(|p|²) part of Π(p) (RG1 (1.22)).
{#B4.4-1} Write v_ν(p) := e^{ip_ν} − 1, so that pure-gauge coarse fields are
{#B4.5} B = v(p)ω̂ e^{ipy}.
{#B4.5-1} ∂ is PRT1's lattice exterior derivative at U = 1, at the spacing ε of the lattice it acts on: the gradient (∂λ)(b) = ε^{−1}(λ(b₊) − λ(b₋)) on 0-forms (PRT1 (1.4), p.18 l.29; (1.9), p.19 l.12, is its instance at spacing L) and the curl (∂A)(p) = ε^{−1}A(∂p) on 1-forms (PRT1 p.18 l.12); ∂* is PRT1's divergence ∂*A = Σ_μ∂*_μA_μ (p.21 l.11); that ∂* is the adjoint of ∂ for the pairings Ση^d is inferred, not printed. ∂^η marks the fine spacing η.

{#B4.6} **Lemma 4.1 (Second-Order Vanishing).** Let T(p) (4×4 in the vector index, ⊗ 1 on g) satisfy T(p)v(p) = 0 for all p.
- {#B4.7} (a) If T is C² on a ball around p = 0, with ‖D²T(q)[u, u]‖ ≤ C|u|² for q in the ball and u ∈ ℝ⁴, and T is covariant
  {#B4.8} under the hyperoctahedral group (signed permutations R), T(Rp) = ρ(R, p)T(p)ρ(R, p)^{−1}, with ρ(R, ·) unitary and
  {#B4.9} differentiable and ρ(R, 0) the signed permutation matrix of R, then ‖T(p)‖ ≤ (C/2)|p|² on that ball.
  {#B4.9-1} (For bond variables at the
  {#B4.10} initial site, ρ(R, p) carries phases e^{±ip_λ}; with pure signs ρ(R, p) = ρ(R, 0) for all p, covariance under R_λ and
  {#B4.11} T(R_λp)v(R_λp) = 0 give T(p)ρ(R_λ, 0)v(R_λp) = 0, whose difference with T(p)v(p) = 0 is (2cos p_λ − 2)T(p)e_λ = 0, so T(p)e_λ = 0 where p_λ ≢ 0 and, by continuity, T ≡ 0.)
- {#B4.12} (b) If ‖T(p) − T(0)‖ ≤ M|p|^γ for all p, with γ > 0, then T(0) = 0 and ‖T(p)‖ ≤ M|p|^γ.
{#B4.13} Part (a) is used in §6 (the affine part of Ψ_tb), and part (b) for the J-coefficient τ of Proposition 4.2.
{#B4.13-1} The
{#B4.14} type-checked Lean core of (b) is `symbol_holder_bound`, used in `BalabanFormal.jterm_holder`.

{#B4.15} *Proof of (a).*
1. {#B4.16} At p = 0, covariance says T(0) commutes with every signed permutation matrix.
   {#B4.16-1} Commuting with the sign changes forces
   {#B4.17} T(0) to be diagonal, and commuting with the permutations forces T(0) = t·1.
2. {#B4.18} Differentiate T(p)v(p) = 0 at 0 in the direction e_μ.
   {#B4.18-1} Since v(0) = 0 and ∂_μv(0) = i e_μ, this gives i t e_μ = 0,
   {#B4.19} so t = 0.
3. {#B4.20} Let a_ρ := ∂_ρT(0).
   {#B4.20-1} Differentiate the covariance under the reflection R_λ (p_λ ↦ −p_λ) at p = 0.
   {#B4.20-2} Since T(0) = 0,
   {#B4.21} the derivatives of ρ(R_λ, ·) drop out, and ρ(R_λ, 0) is the sign change of the λ-th component.
   {#B4.21-1} This gives
   {#B4.22} (a_ρ)_{μν} = (−1)^{[ρ=λ]+[μ=λ]+[ν=λ]} (a_ρ)_{μν} for every λ.
4. {#B4.23} Sum the exponents over λ = 1, …, 4: the total is 3, which is odd.
   {#B4.23-1} So for at least one λ the exponent is odd, and that
   {#B4.24} entry vanishes.
   {#B4.24-1} Hence ∇T(0) = 0.
5. {#B4.25} Taylor's theorem on the ball then gives ‖T(p)‖ ≤ (C/2)|p|² there. ∎

{#B4.26} *Proof of (b).* (Lean core `symbol_holder_bound`.) For 0 < s < 1, v(se_μ) = (e^{is} − 1)e_μ with e^{is} ≠ 1, so
{#B4.27} T(se_μ)e_μ = 0.
{#B4.27-1} Hence |T(0)e_μ| = |(T(0) − T(se_μ))e_μ| ≤ Ms^γ, and s → 0 gives T(0)e_μ = 0 for every μ.
{#B4.27-2} So T(0) = 0,
{#B4.28} and ‖T(p)‖ = ‖T(p) − T(0)‖ ≤ M|p|^γ. ∎

{#B4.29} **Lemma 4.3 (A One-Loop Lipschitz Bound).** For q ∈ ℝ⁴ let d(q) be the distance from q to 2πℤ⁴.
{#B4.29-1} Let a, b ≥ 0 with
{#B4.30} a + b ≤ 2, and let f(q, p) be defined where d(q) > 0 and d(q + p) > 0, 2π-periodic in q, and continuously
{#B4.31} differentiable in p, with

  {#B4.32} |f(q, p)| ≤ M d(q)^{−a}d(q + p)^{−b},  |∂_pf(q, p)| ≤ M d(q)^{−a}d(q + p)^{−b}(1 + d(q + p)^{−1}).

{#B4.33} Then I(p) := ∫_{[−π,π]⁴} f(q, p) d⁴q satisfies |I(p)| ≤ C_IM for all p and |I(p) − I(0)| ≤ C_IM|p| for |p| ≤ π,
{#B4.34} with C_I absolute.
{#B4.34-1} For a sum of n such f, with the pairs (a, b) varying from term to term, the bounds hold with nC_I in place of C_I.

{#B4.35} *Proof.* On [−π, π]⁴, d(q) = |q| ≤ 2π, and ∫_{|q|<ρ}|q|^{−s}d⁴q = 2π²ρ^{4−s}/(4 − s) for s < 4.
{#B4.35-1} Since d is
{#B4.36} 2πℤ⁴-periodic, ∫_E d(q + p)^{−s}d⁴q ≤ ∫_{d(q′)<ρ}d(q′)^{−s} over one period when E ⊂ {d(q + p) < ρ}.
1. {#B4.37} *The bound on I.* Where d(q + p) ≥ |q|, the integrand is at most M|q|^{−a−b}; where d(q + p) < |q|, it is at most
   {#B4.38} Md(q + p)^{−a−b}.
   {#B4.38-1} Since a + b ≤ 2 < 4, both parts integrate to at most CM.
2. {#B4.39} *Region A: |q| ≥ 2|p|.* For t ∈ [0, 1], d(q + tp) ≥ |q| − |p| ≥ |q|/2.
   {#B4.39-1} By the mean value theorem,
   {#B4.40} |f(q, p) − f(q, 0)| ≤ |p| sup_t|∂_pf(q, tp)| ≤ 2^bM|p||q|^{−a−b}(1 + 2|q|^{−1}) ≤ 2^b(2π + 2)M|p||q|^{−a−b−1}.
   {#B4.41} Since a + b + 1 ≤ 3 < 4, the integral over A is at most CM|p|.
3. {#B4.42} *Region B: |q| < 2|p|.* There |f(q, 0)| ≤ M|q|^{−a−b}, with integral at most CM|p|^{4−a−b}.
   {#B4.42-1} For f(q, p), split as in
   {#B4.43} step 1: where d(q + p) ≥ |q| the bound is the same; where d(q + p) < |q| < 2|p|, the integrand is at most
   {#B4.44} Md(q + p)^{−a−b} on a set where d(q + p) < 2|p|, with integral at most CM|p|^{4−a−b} by periodicity.
   {#B4.44-1} Since
   {#B4.45} 4 − a − b ≥ 2 and |p| ≤ π, the integral over B is at most CM|p|.
{#B4.46} Steps 2–3 give |I(p) − I(0)| ≤ C_IM|p|. ∎

{#B4.47} **Proposition 4.2 (J-Terms).** Let J^{(k)} be the step J-term of §3.3, evaluated on the background U = U_{k+1}(e^{iB}).
{#B4.48} The symbol Π_J^{(k)}(p) of its second-order Taylor coefficient in B satisfies ‖Π_J^{(k)}(p)‖ ≤ C|p|³ for |p| ≤ π and
{#B4.49} ‖Π_J^{(k)}(p)‖ ≤ C for all p, with C depending only on d, L, G, and PBG's constants, not on k.
{#B4.49-1} Hence, for every α ∈ (0, ½), ‖Π_J^{(k)}(p)‖ ≤ C_α|p|^{2+2α} on
{#B4.50} [−π, π]⁴ with C_α := C max(π^{1−2α}, π^{−2−2α}), and J^{(k)} contributes nothing to b_{k+1}.

{#B4.51} **Setting.** Units are those of T^{(k+1)}, so p ∈ [−π, π]⁴ is the coarse momentum of §4's Notation.
{#B4.51-1} The fine objects
{#B4.52} 𝐇, J, h, K, φ_A, Π_D, D, Q, Q′, R, G′, Δ′_π, G, and H are those of §7's Setting at the chain level k, and C_G denotes
{#B4.53} §7's C_G := G − GQ*(QGQ*)^{−1}QG.
{#B4.53-1} The step variable B′ is a g-valued function on the bonds of T^{(k)}, h_B is #T10.21's (RG1's
{#B4.54} operator h, written h_B to distinguish it from §3's h), C̃^{(2)}, C̃ and D̃^{(2)} = C̃^{(2)} are #T10.21-2's, with the
{#B4.55} labelled reading of RG1 (2.4) of #B4.174-1 ((d), *The step objects*), C^{(2)} is the second-order part of the dressed average Q
{#B4.57} (Lemma 7.3), which enters Δ^{(2)}_π through PBG (3.134), 𝐆^{(2)} is twice the quadratic part of the axial gauge-fixing
{#B4.58} term, 𝐆 = ½𝐆^{(2)} + 𝐆₃ (RG1 (2.5), p.266), and 𝒫, the parametrisation of {Q̃B′ = 0}, is #T10.28-4's
{#B4.59} (RG1 writes it C).
{#B4.59-1} By constant-gauge covariance at U = 1 (step (b)), every symbol at U = 1 below commutes with Ad(G) on
{#B4.60} g^c ⊗ ℂ⁴.
{#B4.60-1} Since g is simple, Ad is irreducible on g^c, so by Schur's lemma these symbols have the form T₀(p) ⊗ 1, as
{#B4.61} Lemma 4.1 takes them.

{#B4.62} *Proof.*

{#B4.63} *(a) Bałaban's step form.* In Z^{(k)}(U) (#B2.1.1), in the variable B′, by RG1 (1.5) with j = k, and (2.11) with p.267 l.38–40,
{#B4.64} the form is

  {#B4.65} ⟨B′, Δ^{(k)}B′⟩ = ⟨H₁B′, Δ₁H₁B′⟩ − 2⟨H₁h_BC̃^{(2)}(B′), J⟩ + 𝐆^{(2)}(B′),

{#B4.66} where 𝐆^{(2)} replaces the δ-function gauge fixing of PBG (3.156).
{#B4.66-1} Eliminating the variables B′(b₀(c)) by δ(Q̃B′) gives
{#B4.67} B′ = 𝒫B″, Z^{(k)}(U) = 𝔧(U)·det(𝒫*Δ^{(k)}(U)𝒫)^{−1/2}, and C^{(k)} = (𝒫*Δ^{(k)}𝒫)^{−1} (p.268 l.2–3).
{#B4.67-1} Here 𝔧(U) is
{#B4.68} the Jacobian of the elimination, the product over c ∈ T^{(k+1)} of |det|^{−1} of the coefficient of B′(b₀(c)) in
{#B4.69} (Q̃B′)(c) (p.267 l.21–23).
{#B4.69-1} It depends on V^{(k)} only through Q̃, not on the quadratic form.
- {#B4.70} H₁ and Δ₁ are PBG's (3.127)–(3.129) (RG1 p.266 l.39: "see the definitions (3.127), (3.128) [13]").
  {#B4.70-1} So
  {#B4.71} ⟨H₁B′, Δ₁H₁B′⟩ = ⟨B′, (QG₁Q*)^{−1}B′⟩ − a|B′|² = min{⟨A, G₁^{−1}A⟩ : QA = B′} − a|B′|², with H₁ = G₁Q*(QG₁Q*)^{−1}
  {#B4.72} the minimiser (PBG (3.122), (3.129)).
- {#B4.73} By (3.128), (3.120), and (3.134)–(3.135), with PBG's Δ = 𝐇 = h + K,

    {#B4.74} G₁^{−1} = h + DRD* + aQ*Q + X(U, J),  X(U, j) := K(U, j) − Δ′_π(U, j) − Δ^{(2)}_π(U, j).  (4.1)

  {#B4.75} Here K(U, j), Δ′_π(U, j), and Δ^{(2)}_π(U, j) are (7.1), (3.120), and (3.134)–(3.135) with an independent fine adjoint
  {#B4.76} 1-form j in place of J. Each is linear in j, with coefficients that are functions of U.

{#B4.77} *(b) The J-term as a determinant.* For a fine adjoint 1-form j put

  {#B4.78} ⟨B′, Δ^{(k)}(U, j)B′⟩ := min{⟨A, (h + DRD* + aQ*Q + X(U, j))A⟩ : QA = B′} − a|B′|² + Y(U, j)(B′) + 𝐆^{(2)}(B′),

{#B4.79} with Y(U, j)(B′) := −2⟨H₁(U, j)h_BC̃^{(2)}(B′), j⟩ and H₁(U, j) the minimiser map of the minimum, and

  {#B4.80} F(U, j) := −½ log det(𝒫*Δ^{(k)}(U, j)𝒫) + ½ log det(𝒫*Δ^{(k)}(U, 0)𝒫).

{#B4.81} By (a), Δ^{(k)}(U, J(U)) = Δ^{(k)}(U), so
{#B4.82} log Z^{(k)}(U) = F(U, J(U)) + log 𝔧(U) − ½ log det(𝒫*Δ^{(k)}(U, 0)𝒫) + const.
- {#B4.83} At j = 0, X = 0 and Y = 0, and the argument of Proposition 7.1(b) gives ⟨B′, Δ^{(k)}(U, 0)B′⟩ = ⟨B′, Δ_kB′⟩ +
  {#B4.84} 𝐆^{(2)}(B′), with §3's Δ_k on the level-k field B′.
- {#B4.85} On {Q̃B′ = 0}, the gauge directions of Δ_k are the ω vanishing at the sites of T^{(k+1)} (QD = D̄P, §3.1).
  {#B4.85-1} They shift
  {#B4.86} B̃′(y, x) (#B4.177), defined by Ṽ′ = 1 + B̃′ + … (RG1 p.266 l.10), by −i·Ad(V^{(k)}(y, x))ω(x), Ad being orthogonal at real V^{(k)}. So the Gaussian integral over these directions against
  {#B4.87} e^{−½𝐆^{(2)}} is a constant, and the axial slice has Faddeev–Popov determinant 1 (§3.1).
  {#B4.87-1} The integral
  {#B4.88} ∫dB′ δ(Q̃B′) exp[−½⟨B′, Δ^{(k)}(U, 0)B′⟩] carries the same Jacobian 𝔧(U), so
  {#B4.89} log 𝔧(U) − ½ log det(𝒫*Δ^{(k)}(U, 0)𝒫) = log Z^{(k)}[h] + const = (F_{k+1} − F_k)(U) + const on each coset
  {#B4.90} 𝒪 ≠ ℤp, by Corollary 3.2 and Remark 3.4.
- {#B4.91} So J^{(k)}(U) = F(U, J(U)) + const, and F(U, 0) = 0.
- {#B4.92} *Gauge covariance.* F(U^g, Ad(g)j) = F(U, j) for every fine gauge transformation g.
  {#B4.92-1} All operators in (4.1) and in
  {#B4.93} Y are gauge-covariant.
  {#B4.93-1} The averages are covariant: the chain's average by the form of RG1 (0.4) or (0.12) with
  {#B4.94} (0.6) (Q̃D = D̄P, §3.1; Proposition 5.3, step 1), and the dressed average also through its dressing factors in PBG
  {#B4.95} (3.113), since (R_yU′)(y, x) ↦ Ad(g(y))(R_yU′)(y, x) under U ↦ U^g by (0.6) on (0.11) (QD = D̄Q′, §7's Setting).
  {#B4.96} The step variables transform by Ad(g) at the sites of T^{(k)}, which is orthogonal, and 𝐆^{(2)} is Ad-invariant.
  {#B4.96-1} Also J(U^g) = Ad(g)J(U).

{#B4.97} *(c) Second order in B.* Let B be a plane wave of momentum p ≢ 0 on a torus, and 𝒪 ≠ ℤp a coset (Remark 3.4).
{#B4.97-1} Below,
{#B4.98} F, Θ, and F_jj are restricted to X_𝒪, j ranges over T_p-invariant fine 1-forms, and the symbols are the limits of
{#B4.99} the coset sums.
{#B4.99-1} On X_𝒪, F is real-analytic in (t, j) near (0, 0), with U = U_{k+1}(e^{iB}) analytic in t (§5,
{#B4.100} analyticity of the background).
{#B4.100-1} Every operator in (b), restricted to X_𝒪, depends analytically on (t, j) there
{#B4.101} (Remark 3.4).
{#B4.101-1} The minimum in (b) is a Schur complement of a form positive on ker Q at (1, 0), where it is G(1)^{−1}, and
{#B4.102} 𝒫*Δ^{(k)}(1, 0)𝒫 = C^{(k)}(1)^{−1} is invertible.
{#B4.102-1} Only the Taylor coefficients at (1, 0) are used, and (d) computes
{#B4.103} them explicitly.
{#B4.103-1} The constant gauge transformations and the gauge transformations e^{itω′} with T_p-invariant ω′ used
{#B4.104} below preserve each coset.
{#B4.104-1} Write
{#B4.105} ∂_jF(U, 0)[j] =: ⟨j, Θ(U)⟩ and F_jj := ∂²_jF(1, 0).
{#B4.105-1} By gauge covariance,
{#B4.106} Θ(U^g) = Ad(g)Θ(U).
{#B4.106-1} Expand J(U_{k+1}(e^{iB})) = j₁(B) + j₂(B) + ….
{#B4.106-2} Since F(U, 0) = 0 and J(1) = 0, the second-order part
{#B4.107} of J^{(k)} is ⟨j₂, Θ(1)⟩ + ⟨j₁, Θ₁B⟩ + ½F_jj[j₁, j₁], where Θ₁ is the linearisation of B ↦ Θ(U_{k+1}(e^{iB})).
- {#B4.108} Θ(1) = 0: Θ(1) = Ad(u)Θ(1) for every constant u, so each Θ(1)(b) is an Ad-invariant vector of the simple Lie
  {#B4.109} algebra g, hence zero.
  {#B4.109-1} So the first term vanishes.
- {#B4.110} *The leg A₁.* The linearisation A₁ of U_{k+1}(e^{iB}) minimises ‖∂A‖² on {Q̃_{k+1}A = B}, with Q̃_{k+1} the
  {#B4.111} first-order average of the chain (Proposition 5.3, step 1).
  {#B4.111-1} So A₁ has the curvature of H_{k+1}B, which is H(1)B with
  {#B4.112} H at the chain level k + 1 (Lemma 7.2, step 1, at level k + 1).
  {#B4.112-1} On quasi-momentum p ≢ 0 a curl-free Bloch wave is a
  {#B4.113} gradient, so A₁ = H(1)B + ∂ω′.
  {#B4.113-1} By covariance, Θ₁ annihilates gradients:
  {#B4.114} the derivative of Θ(1^{e^{itω′}}) = Ad(e^{itω′})Θ(1) = 0 at t = 0.
  {#B4.114-1} So Θ₁B is the derivative of Θ at 1 in the
  {#B4.115} direction A₁ := H(1)B, whose kernel decays exponentially (PBG (3.133)).
- {#B4.116} *The gradient j₁.* j₁ = 𝐇(1)A₁ = ∂ᵀ∂H_{k+1}B, with PRT1's H_{k+1}, because A₁ and H_{k+1}B have the same
  {#B4.117} curvature (Proposition 5.3, step 1, with k + 1 in place of k).
  {#B4.117-1} Since H_{k+1}B minimises ‖∂A‖² subject to
  {#B4.118} Q_{k+1}A = B (Proposition 5.3, step 1, third fact), ∂ᵀ∂H_{k+1}B = Q_{k+1}ᵀλ_B for a Lagrange multiplier λ_B.
  {#B4.118-1} Then
  {#B4.119} ⟨B, Δ_{k+1}B⟩ = ‖∂H_{k+1}B‖² = ⟨B, λ_B⟩ (PRT1 p.29), and polarisation gives λ_B = Δ_{k+1}B, so
  {#B4.120} j₁ = Q_{k+1}ᵀΔ_{k+1}B.
  {#B4.120-1} Since 0 ≤ ⟨B, Δ_{k+1}B⟩ ≤ γ₁⟨∂₁B, ∂₁B⟩ (PRT1 (1.67)) and |∂¹_μ(p)| ≤ |p_μ|,
  {#B4.121} ‖Δ_{k+1}(p)‖ ≤ Cγ₁|p|², with C absolute and γ₁ depending on d only.
- {#B4.122} Hence the second-order part is ⟨Δ_{k+1}B, τB⟩ + ½⟨Δ_{k+1}B, R̃Δ_{k+1}B⟩ with τ := Q_{k+1}Θ₁ and
  {#B4.123} R̃ := Q_{k+1}F_jjQ_{k+1}ᵀ, and ‖Π_J^{(k)}(p)‖ ≤ ‖Δ_{k+1}(p)‖‖τ(p)‖ + ½‖Δ_{k+1}(p)‖²‖R̃(p)‖.

{#B4.124} *(d) Loop integrals at U = 1.* Let 𝒞(U) := (𝒫*Δ^{(k)}(U, 0)𝒫)^{−1} and H_h(U) := H₁(U, 0).
{#B4.124-1} At U = 1, J = 0, so
{#B4.125} 𝒞(1) = C^{(k)}(1), H_h(1) = H(1), and K(1, ·), Δ′_π(1, ·) are given by (7.1) and (3.120) at U = 1.
- {#B4.126} *Θ.* The minimum in (b) is stationary at its minimiser, so the j-linear part of Δ^{(k)}(U, j) is
  {#B4.127} V(U, j)(B′) := ⟨H_h(U)B′, X(U, j)H_h(U)B′⟩ − 2⟨H_h(U)h_BC̃^{(2)}(B′), j⟩.
  {#B4.127-1} Hence
  {#B4.128} ⟨j, Θ(U)⟩ = −½Tr(𝒞(U)𝒫*V(U, j)𝒫).
  {#B4.128-1} In the direction A₁, the U-derivative falls on 𝒞, 𝒫, H_h, X, h_B, or C̃^{(2)}.
  {#B4.129} By §3.3, h(U) = 𝐇(U) − K(U, J(U)) with ∂J(1)[A₁] = 𝐇(1)A₁, so ∂_Uh(1)[A₁] = ∂𝐇(1)[A₁] − K(1, 𝐇(1)A₁).
  {#B4.129-1} In K, the
  {#B4.130} derivative of φ_A at fixed A is (∂ᵀ∂)^{−1}[D₁ᵀΠ_⊥A − ∂ᵀD₁φ_A], as in Proposition 7.1(d), T4.
- {#B4.131} *F_jj.* ½F_jj[j, j] = −½Tr(𝒞𝒫*V₂(j)𝒫) + ¼Tr(𝒞𝒫*V(1, j)𝒫𝒞𝒫*V(1, j)𝒫) at U = 1, with V₂(j) the j-quadratic part
  {#B4.132} of Δ^{(k)}(1, j).
  {#B4.132-1} The constrained Gaussian gives the j-quadratic part of the minimum as
  {#B4.133} −⟨H(1)B′, X(1, j)C_GX(1, j)H(1)B′⟩ (as in Proposition 7.1(b)).
  {#B4.133-1} The j-quadratic part of Y is
  {#B4.134} −2⟨∂_jH₁[j]h_BC̃^{(2)}(B′), j⟩, with ∂_jH₁[j] = −C_GX(1, j)H(1) by differentiating H₁ = G₁Q*(QG₁Q*)^{−1}.
- {#B4.135} *Bloch form.* At U = 1 every operator commutes with the translations of T^{(k+1)}.
  {#B4.135-1} For B of momentum p, each trace
  {#B4.136} is ∫_{[−π,π]⁴} Tr ℳ(q, p) d⁴q/(2π)⁴, the limit of the coset sums (Remark 3.4), with q the quasi-momentum of the internal line on which no external leg has
  {#B4.137} acted, and q + p that of the other line. ℳ(q, p), the product of the Bloch symbols of the trace's factors, is a linear map on the step variables of one cell of T^{(k+1)}, which number
  {#B4.138} dL^d dim g, and Tr is its trace (#B0.6-1), so |Tr ℳ| ≤ dL^d dim g ‖ℳ(q, p)‖, and ‖ℳ‖ is at most the product of the fibre norms of its factors
  {#B4.139} (§7's Bloch norms).
  {#B4.139-1} The integrands are 2πℤ⁴-periodic in q.
- {#B4.140} *Regular factors (L).* Their Bloch symbols are bounded with bounded q-derivative, uniformly in k, by exponential
  {#B4.141} decay of their kernels and the Schur test: 𝒞(1) = C^{(k)}(1) (by #B4.147-1 instead), 𝒫, H, G, G′, C_G, R, Q, Qᵀ, A₁, D₁, Δ′_π (through
  {#B4.142} λ_A = G′RD*A), Δ^{(2)}_π, h_B, C̃^{(2)}, 𝐆^{(2)}, ∂𝐇(1)[A₁] (after its fine quotients are moved, #B4.171-1, #B4.198), the local factors of T in (7.1), and the U-derivatives
  {#B4.143} at 1 in the direction A₁ of 𝒫, R, Q, Qᵀ, D, the transports R(U_b), h_B, C̃^{(2)}, C^{(2)}, and 𝐆^{(2)}.
  {#B4.143-1} Sources: PBG Thms 3.1, 3.2
  {#B4.144} (for R, p.399 l.4), 3.3, and 3.12 and (3.131)–(3.133) at U = 1, where H, G, G′, C_G, R, Q, and (QGQ*)^{−1} are PBG's own operators by
  {#B4.145} §7's Setting.
  {#B4.145-a} Δ′_π (third term of (3.120)) and Δ^{(2)}_π (through (3.135)) contain ∇G′∇*, whose kernel PBG does not bound pointwise ("not regular enough", p.423 l.14). For it the decay is that of the block-to-block L² norms, ≤ B₀e^{−δ₀d(y,y′)} by (3.46) (p.398) at U = 1, and the Schur test over the blocks gives the bounds on the symbol and its q-derivative.
  {#B4.145-1} For Δ^{(2)}_π, PBG (3.134)–(3.135) with Lemma 7.3: |⟨A′, Δ^{(2)}(1, j)A⟩| ≤
  {#B4.146} 2‖C^{(2)}(1; A′, A)‖_1‖H(1)*j‖_∞ ≤ C‖j‖_∞‖A‖_2‖A′‖_2 by (3.133), and its finite range bounds the q-derivative.
  {#B4.147} Lemma 7.3 also gives the U-derivatives at 1 of Q, Qᵀ, and C^{(2)}.
  - {#B4.147-1} *𝒞(1) = C^{(k)}(1).* Its Bloch symbol is bounded with bounded q-derivative, uniformly in k, by steps 1–4 below, which use PBG only at U = 1.
    {#B4.147-2} Step 1. At (1, 0), J = 0 and G₁ = G(1) (#B4.212-1), with G(1)^{−1} = 𝐇(1) + ∂R∂* + aQ_k*Q_k (#B7.138-1). So #B4.65 and #B4.71 give ⟨B′, Δ^{(k)}(1, 0)B′⟩ = min{⟨A, (𝐇(1) + ∂R∂*)A⟩ : Q_kA = B′} + 𝐆^{(2)}(B′).
    {#B4.147-3} R is a projection, so ∂R∂* ≥ 0. At J = 0, 𝐇(1) = h(1), and {Q_kA = B′} lies in {QA ∈ B′ + ran D̄}, so the minimum is ≥ ⟨B′, Δ_kB′⟩ (#B3.1.22, #B7.20-1) ≥ γ₀′‖∂₁B′‖² (#B3.1.23-1; PRT1 (1.67)), with ∂₁B′ the curvature of B′ on the plaquettes of T^{(k)} and γ₀′ > 0 PRT1's γ₀ in the units of T^{(k+1)}, depending only on d and L.
    {#B4.147-4} Step 2 (local coercivity). Let c be a bond of T^{(k+1)} and P the set of bonds of T^{(k)} with both ends in B(c₋) ∪ B(c₊). The linear map T_c : B′|_P ↦ (∂₁B′ on the plaquettes of P, B̃′(y, x) for y = c_±, x ∈ B(y), and Q̃B′(c)) at V^{(k)} = 1 is injective.
    {#B4.147-5} Indeed, let T_cB′ = 0. In each block, B′ has zero curvature, so B′ = ∂ω there (a cube is simply connected), and the contours of 𝐆(y, x) stay in B(y) (#B4.185), so B̃′(y, x) = i(ω(x) − ω(y)) (#B4.178) = 0; hence B′ = 0 on the bonds inside the blocks.
    {#B4.147-6} Two crossing bonds at neighbouring sites s, s + e_ν of the face bound a plaquette whose other two bonds lie inside the blocks, so all L^{d−1} crossing bonds carry the same value β. Each crossing bond has coefficient L^{−d} in Q̃B′(c) (the argument of #B4.184-1–#B4.186), so Q̃B′(c) = L^{−1}β = 0, and B′ = 0 on P.
    {#B4.147-7} T_c is a fixed linear map on a space of dimension at most n(d, L)·dim g, the same for every c and k and acting as the identity on g, so |B′|_P|² ≤ C_{d,L}|T_cB′|². Each bond lies in at least one set P, and each plaquette and block in at most 2d; summing over c gives ‖B′‖² ≤ 2dC_{d,L}(‖∂₁B′‖² + 𝐆^{(2)}(B′) + ‖Q̃B′‖²).
    {#B4.147-8} Step 3. 𝒫B″ lies in {Q̃B′ = 0} and equals B″ on the bonds other than the b₀(c) (#B4.177), so ‖𝒫B″‖ ≥ ‖B″‖. Steps 1–2 give C^{(k)}(1)^{−1} = 𝒫*Δ^{(k)}(1, 0)𝒫 ≥ c_𝒞 := min(γ₀′, 1)/(2dC_{d,L}); so every fibre of the symbol of C^{(k)}(1) has norm ≤ 1/c_𝒞.
    {#B4.147-9} Step 4. The symbol of 𝒫*Δ^{(k)}(1, 0)𝒫 is 𝒫̂*[(QG₁Q*)^{−1} − a + 𝐆̂^{(2)}]𝒫̂ (#B4.71). (QG(1)Q*)^{−1} has kernel ≤ Ce^{−δ₁|y−y′|} (PBG (3.132) at U = 1, §0's input 6), and 𝒫, 𝐆^{(2)} have finite range, so its q-derivative is bounded; then ∂_qĈ = −Ĉ(∂_q Ĉ^{−1})Ĉ is bounded by C/c_𝒞².
  - {#B4.148} *Explicit local factors.* With D_Uλ(b) = η^{−1}(R(U_b)λ(b₊) − λ(b₋)) (PBG (3.50), p.400, and p.418) and
    {#B4.149} U(t) = exp(itηA₁ + O(t²)), the U-derivative of D is D₁λ(b) = i[A₁(b), λ(b₊)], of range 1, with sup norm
    {#B4.150} ≤ 2‖A₁‖_∞‖λ‖_∞ and ℓ² norm ≤ 2√d‖A₁‖_∞‖λ‖_2 (each site is b₊ of d positively oriented bonds).
    {#B4.150-1} The transports
    {#B4.151} R(U_b) in T of (7.1) and in PBG (3.120) have U-derivative iη ad_{A₁(b)}, of range 0 and norm ≤ 2η‖A₁‖_∞.
    {#B4.152} 𝐇(U) is the Hessian of the Wilson action W in the chart A ↦ e^{iηA}U.
    {#B4.152-1} Since e^{isηA}e^{itηA₁} =
    {#B4.153} exp iη(sA + tA₁ + (i/2)ηst[A, A₁] + …) and 1 is a critical point of W,
    {#B4.154} ⟨A, ∂𝐇(1)[A₁]A⟩ = W‴(1)[A₁, A, A] + iη⟨[A, A₁], 𝐇(1)A⟩, with W‴ the third derivative of X ↦ W(e^{iηX}) at 0.
    - {#B4.155} With U = e^{iηX} the plaquette logarithm is iη²(d_ηX + q(X)) + O(η³), with (d_ηX)(p) := η^{−1}Σ_{b∈∂p}X(b) the fine lattice curl over the oriented bonds of p and q(X) a sum of commutators [X(b), X(b′)]
      {#B4.156} of bonds of the plaquette, and 1 − Re tr e^{iY} has no cubic term (tr Y³ is real).
      {#B4.156-1} So the cubic part of the
      {#B4.157} action is, up to constants and orientation signs, η^d Σ_p tr(d_ηX·q(X)): each term of W‴(1)[A₁, ·, ·] has one
      {#B4.158} fine difference quotient d_η, on A₁ or on one of the two other arguments, and a commutator with the remaining
      {#B4.159} two, and it has finite range.
    - {#B4.160} The chart term.
      {#B4.160-1} As an operator, the chart part of ∂𝐇(1)[A₁] is the symmetric (iη/2)[ad_{A₁}, 𝐇(1)], with
      {#B4.161} polarised form (iη/2)(⟨[A′, A₁], 𝐇(1)A⟩ + ⟨[A, A₁], 𝐇(1)A′⟩) (the srt coefficient of
      {#B4.162} W(e^{iη(sA+rA′)}e^{itηA₁}) minus W‴(1)[A₁, A, A′]).
      {#B4.162-1} Here ⟨[A′, A₁], 𝐇(1)A⟩ = ⟨d_η[A′, A₁], d_ηA⟩ up to a constant, since 𝐇(1) is a
      {#B4.163} multiple of d_η*d_η.
      {#B4.163-1} On a plaquette in the μν-plane, (d_η[A′, A₁])(p) is η^{−1} times the signed sum of
      {#B4.164} [A′(b), A₁(b)] over its four bonds.
      {#B4.164-1} Grouping the two μ-bonds and the two ν-bonds (the discrete Leibniz rule), it is
      {#B4.165} a sum of terms (difference quotient of A′_ν or A′_μ)×(A₁ at a bond of p) and A′(b)×(difference quotient of A₁_ν
      {#B4.166} or A₁_μ).
      {#B4.166-1} The other half is the same with A and A′ exchanged.
      {#B4.166-2} So the chart term is η times a range-1 form of two
      {#B4.167} kinds: one difference quotient on each of A′ and A, with coefficient ≤ C(d)‖A₁‖_∞; or one on A or on A′ only,
      {#B4.168} with coefficient ≤ C(d)‖∇A₁‖_∞.
    {#B4.169} Here A₁ = H_{k+1}(1)B, with (c)'s operator H at chain level k + 1 (Proposition 4.2(c), the leg A₁: Θ₁ annihilates
    {#B4.170} gradients), so a quotient on A₁ and the factor ‖∇A₁‖_∞ are bounded by ‖∇H_{k+1}(1)B‖_∞ ≤ C‖B‖_∞: PBG (3.133),
    {#B4.171} p.422, at U = 1 with L^{k+1}η = 1 gives |∇H_{k+1}(x, y′)| ≤ O(1)e^{−δ₁d(y,y′)/2}.
    {#B4.171-1} A quotient on another argument is moved onto the adjacent factor (last sub-bullet).
  - {#B4.172} *The step objects.* h_B, C̃^{(2)}, 𝒫, and 𝐆^{(2)} are RG1's explicit one-step objects, functions of
    {#B4.173} V^{(k)} = M^k(U) (RG1 (2.3), p.265).
    {#B4.173-1} Write f(B′) := (1/i)log[M(V′V^{(k)})M(V^{(k)})^{−1}] = Q̃(B′) of RG1 (2.4),
    {#B4.174} p.266.
    {#B4.174-1} We read f as RG1's LQ̃B′ + C̃(B′) of p.267 l.26, the function that p.267 l.24–26 linearizes (inferred, not printed; BP_RG2_COMPLEX_B.md #BH.3-0), so the linear operator Q̃ is L^{−1} times the linear part of f,
    {#B4.175} and C̃^{(2)} is the quadratic part of f (p.261 l.10–11; D̃^{(2)} = C̃^{(2)}, p.267 l.29). h_B(c) is L^{−1} times
    {#B4.176} the inverse of the coefficient of B′(b₀(c)) in (Q̃B′)(c), so that LQ̃h_B = I, and 𝒫 solves Q̃B′ = 0 for the
    {#B4.177} variables B′(b₀(c)) (p.267 l.18–23, p.268 l.2–3). 𝐆^{(2)} is the sum over y and x ∈ B(y) of |B̃′(y, x)|², with B̃′(y, x) the linear part of
    {#B4.178} (V′V^{(k)})(y, x)(V^{(k)}(y, x))^{−1} (RG1 (2.5), p.266).
    {#B4.178-1} So each coefficient of these maps at a coarse bond c (at a
    {#B4.179} coarse site y for 𝐆^{(2)}) is a fixed analytic function Φ of the level-k bond variables of V^{(k)} on the blocks
    {#B4.180} B(c₋) ∪ B(c₊) (on B(y)).
    {#B4.180-1} These variables
    {#B4.181} are a fixed number n(d, L) of bonds, and Φ is defined on a complex polydisc of radius r₀(d, L, G) around 1,
    {#B4.182} since the averages are defined on G^c (RG1 p.252 l.37, p.253 l.16).
    {#B4.182-1} At V^{(k)} = 1 the coefficient of B′(b₀(c))
    {#B4.183} in f(B′)(c) is L^{1−d}·1, and so in (Q̃B′)(c) it is L^{−d}·1, with h_B(c) = L^{d−1}.
    {#B4.183-1} Indeed b₀(c) is the bond of c
    {#B4.184} that crosses from B(c₋) to B(c₊).
    {#B4.184-1} In RG1 (0.4) it lies on the L lines [x, x′] with x = c₋ + mL^{−1}e_μ,
    {#B4.185} |m| ≤ (L − 1)/2, each of weight L^{−d}; on no contour of 𝐆(c₋, x) or 𝐆(c₊, x′), which stay in B(c₋) and B(c₊);
    {#B4.186} and on c itself, which enters each loop as −c (total weight −1) and the factor 𝐔(c) (weight +1), which cancel.
    {#B4.187} For RG1 (0.12), p.254, the coefficient is the same, since its linear part at 1 equals that of (0.4).
    {#B4.187-a} Write U = exp iA and A(Γ) := Σ_{b∈Γ} A(b), the linear part of (1/i)log U(Γ) (Baker–Campbell–Hausdorff). By RG1 (0.8), (1/i)log U(c₋, x) of (0.11) has linear part (1/|𝐆(c₋,x)|)Σ_{Γ∈𝐆(c₋,x)} A(Γ).
    {#B4.187-b} U(x′, c₊) is the variable (0.11) of 𝐆(x′, c₊). RG1 p.252's construction started at x′, over all orders of the axes, gives the contours of 𝐆(c₊, x′) run backwards, so U(x′, c₊) = U(c₊, x′)^{−1} by RG1 (0.5). So its logarithm has linear part −(1/|𝐆(c₊,x′)|)Σ_{Γ′∈𝐆(c₊,x′)} A(Γ′).
    {#B4.187-c} So the linear part of (0.12)'s exponent is Σ_{x∈B(c₋)} L^{−d}[avg_Γ A(Γ) + A([x, x′]) − avg_{Γ′} A(Γ′) − A(c)].
    {#B4.187-d} In (0.4), (1/i)log U(Γ ∪ [x, x′] ∪ (−Γ′) ∪ (−c)) has linear part A(Γ) + A([x, x′]) − A(Γ′) − A(c), and its average over Γ and Γ′ with the weights 1/|𝐆| gives the same exponent. In both, the factor U(c) adds A(c).
    {#B4.187-1} So
    {#B4.188} the coefficient is invertible on a smaller polydisc, of radius r₁(d, L, G) ≤ r₀, where h_B and 𝒫 are analytic
    {#B4.189} too.
    {#B4.189-1} The units are those of T^{(k+1)}, so the level-k spacing is L^{−1} for every k.
    {#B4.189-2} Along
    {#B4.190} U(t) = exp(itηA₁ + O(t²)), the level-k bond logarithms of V^{(k)}(t) are tL^{−1}a₁ + O(t²) with
    {#B4.191} ‖a₁‖_∞ ≤ (1 + d)‖A₁‖_∞ (Lemma 7.3, step 5, at chain level k + 1).
    {#B4.191-1} Cauchy estimates bound every coefficient of the
    {#B4.192} U-derivatives at 1 by n·sup|Φ|·r^{−1}·L^{−1}(1 + d)‖A₁‖_∞, with the sup over the polydisc of radius r, where r = r₀
    {#B4.193} for C̃^{(2)} and 𝐆^{(2)} and r = r₁ for h_B and 𝒫.
    {#B4.193-1} The maps have
    {#B4.194} finite range, so their Bloch symbols are bounded with bounded q-derivative, uniformly in k.
    {#B4.194-1} None of this uses #B9.38.
  - {#B4.195} The U-derivative of X(U, j) also needs those of H and G′: Δ′_π contains λ_A = G′RD*A, and Δ^{(2)}_π contains H
    {#B4.196} through (3.134) and G′ through (3.135).
    {#B4.196-1} The U-derivatives at 1 of H, G′, and R (the projection of #B7.8-2, not the transports) are written out below
    {#B4.197} from the operators at U = 1, which are PBG's own (§7's Setting); ∂ is the derivative at U = 1 in the direction A₁.
    - {#B4.197-1} ∂Q′. Q′ = Q′^{(k)}⋯Q′^{(1)} (#B7.14), and Q′^{(j)} depends on U through R(Ū^{j−1}(y, x)), whose logarithm at U(t) has linear part ta_j(y, x), the contour mean of the level-(j − 1) bond logarithms ts_jQ̃_{≤j−1}(1)A₁ (#B7.191; s_j the level-(j − 1) spacing, #B7.166).
      {#B4.197-2} A contour of 𝐆(y, x) has at most (L − 1)d/2 bonds (#B7.194), and the level-(j − 1) bond logarithms have sup ≤ (1 + d)s_j‖A₁‖_∞ (#B7.199); so |a_j(y, x)| ≤ (d + d²)(L − 1)s_j‖A₁‖_∞/2.
      {#B4.197-3} So ∂Q′ = Σ_{j=1}^k Q′_{(j+1→k)}(1)M_jQ′_{(1→j−1)}(1), with M_jλ(y) = Σ_{x∈B(y)}L^{−d}i·ad(a_j(y, x))λ(x) and Q′_{(i→l)} := Q′^{(l)}⋯Q′^{(i)} (1 for l < i). The averages at 1 are contractions in ‖·‖_p, p = 1, 2, ∞, ‖ad(a)‖ ≤ c_𝐠|a| with c_𝐠 depending only on G, and Σ_j s_j ≤ 1/(L − 1) in top units (#B7.190-1), so ‖∂Q′‖_{p→p} ≤ c_𝐠(d + d²)‖A₁‖_∞/2.
    - {#B4.197-4} ∂G′. G′ = (Δ_U + Q′*aQ′)^{−1} (PBG (3.23)–(3.24), where Q′*aQ′ has the coefficient a_k at L^kη = 1), so ∂G′ = −G′(D₁*D + D*D₁ + a_k∂Q′*Q′ + a_kQ′*∂Q′)G′, with D₁ of #B4.149 and the derivative in D moved onto G′ (#B4.199).
    - {#B4.197-5} ∂R. By PBG (3.25), R = I − G′Q′*S′^{−1}Q′G′ with S′ := Q′G′²Q′*. So ∂R is the sum of the five terms in which ∂ falls on one of G′, Q′*, S′^{−1}, Q′, G′, with ∂S′^{−1} = −S′^{−1}(∂Q′G′²Q′* + Q′∂(G′²)Q′* + Q′G′²∂Q′*)S′^{−1}.
    - {#B4.197-6} ∂H. As in #B4.218 with G for G_𝐌: ∂H = −C_G∂(G^{−1})H(1) + C_G∂Q*(QGQ*)^{−1} − H(1)∂QH(1), where ∂(G^{−1}) = ∂𝐇(1)[A₁] − ∂Δ′_π + ∂(DRD*) + a∂(Q*Q).
      {#B4.197-7} Δ′_π is linear in J and J(1) = 0 (#B4.212-1), so ∂Δ′_π = Δ′_π(1, 𝐇(1)A₁) (#B4.219). And ∂(DRD*) = D₁RD* + D∂RD* + DRD₁*.
      {#B4.197-7a} The U-derivative of Δ′_π(U, j) at fixed j, in X(U, j), comes from (3.120) through ∂λ_A = (∂G′RD* + G′∂RD* + G′RD₁*)A, through ∂R_b = iη ad_{A₁(b)} of the transport in its second term (#B4.151), and through D₁ in place of D in its third term (#B4.149).
    - {#B4.197-8} Every factor in these formulas is a regular factor of #B4.140–#B4.147 at U = 1 (with Q′(1), the block average; S′^{−1} by PBG Thm 3.2, (QGQ*)^{−1} by (3.132)), or a local factor D₁, ∂Q, ∂Q′ bounded by C‖A₁‖_∞, once D, D*, and the fine quotients of ∂𝐇(1)[A₁] are moved onto the adjacent G′, H, or C_G as in #B4.198–#B4.203, so they enter the degree count of #B4.221–#B4.229 like the other insertions.
  - {#B4.198} The fine derivatives in ∂𝐇(1), Δ′_π, and D, D* are moved onto the adjacent factors H, G, G′, or C_G.
    - {#B4.199} A derivative next to G′ is taken by G′: ∇G′ and G′∇* by PBG Thm 3.1, (3.42), p.397.
      {#B4.199-1} This covers the D* in
      {#B4.200} DRG′D*.
    - {#B4.201} Where R stands between G′ and the derivative, the derivative is moved onto the outer factor on its side: the D*
      {#B4.202} in λ_A = G′RD*A and in the DG′RD* terms of (3.135) onto the factor on its right, the D of DRG′D* and the D* of
      {#B4.203} λ_{A′} (the left argument of the polarised Δ′_π) onto the factor on its left, H(1)* or C_G.
    - {#B4.204} These outer factors are bounded with their derivatives: H by (3.133); G by PBG Thm 3.3, which gives G the
      {#B4.205} bounds (3.42)–(3.47) of G′, among them ∇G∇* in (3.46), p.398 (and (3.131) for its Δ′_π part); and
      {#B4.206} C_G = G − GQ*(QGQ*)^{−1}QG through G and (3.132).
      {#B4.206-1} C_G may carry one derivative on each side, as in
      {#B4.207} −⟨H(1)B′, XC_GXH(1)B′⟩ and in ⟨∂H_hB′, XHB′⟩: ∇C_G∇* = ∇G∇* − (∇GQ*)(QGQ*)^{−1}(QG∇*), by (3.46), (3.42),
      {#B4.208} and (3.132).
    - {#B4.209} The external factors Q_{k+1}(p) and A₁(p) are of this kind in p.
- {#B4.210} *The U-derivatives of 𝒞 and H_h.* These are not PBG objects away from U = 1, since h(U) = 𝐇(U) − K(U, J(U)).
  {#B4.210-1} They
  {#B4.211} are written out.
  {#B4.211-1} Put 𝐌 := h + DRD* + aQ*Q, G_𝐌 := 𝐌^{−1} = G₁(U, 0), and S := QG_𝐌Q* at j = 0, so the minimum in
  {#B4.212} (b) is ⟨B′, S^{−1}B′⟩ and H_h = G_𝐌Q*S^{−1}.
  {#B4.212-1} G_𝐌 is not §7's G away from U = 1, but G_𝐌(1) = G(1), since K and Δ′_π
  {#B4.213} are linear in J and J(1) = 0.
  {#B4.213-1} Since Q = Q(U), the constraint QA = B′ moves with U. All derivatives below are at
  {#B4.214} U = 1 in the direction A₁, ∂G_𝐌 = −G_𝐌∂𝐌 G_𝐌, and ∂𝐌 contains a(∂Q*Q + Q*∂Q).
  - {#B4.215} ∂𝒞 = −𝒞(∂(𝒫*Δ^{(k)}(·, 0)𝒫))𝒞.
  - {#B4.216} ∂⟨B′, Δ^{(k)}(·, 0)B′⟩ = ⟨H(1)B′, ∂𝐌 H(1)B′⟩ − 2⟨S^{−1}B′, ∂Q H(1)B′⟩ + ∂𝐆^{(2)}(B′), from
    {#B4.217} ∂S^{−1} = −S^{−1}(∂Q G_𝐌Q* + QG_𝐌∂Q* − QG_𝐌∂𝐌G_𝐌Q*)S^{−1}.
  - {#B4.218} ∂H_h = −C_G∂𝐌 H(1) + C_G∂Q*S^{−1} − H(1)∂Q H(1), using C_G = G_𝐌 − G_𝐌Q*S^{−1}QG_𝐌 at U = 1.
  - {#B4.219} Here ∂_Uh(1)[A₁] = ∂𝐇(1)[A₁] − K(1, 𝐇(1)A₁), whose K-part has singular degree ≤ 1 and is counted below.
    {#B4.219-1} The other
    {#B4.220} parts, including the ∂Q terms (S^{−1} = (QGQ*)^{−1} decays exponentially, PBG (3.132)), are regular.
- {#B4.221} *Singular factors.* These are diagonal in the aliases: Π_D of degree 0, φ = (∂ᵀ∂)^{−1}∂ᵀ and ∂(∂ᵀ∂)^{−1} of
  {#B4.222} degree 1, and (∂ᵀ∂)^{−1} of degree 2.
  {#B4.222-1} A factor of degree s at quasi-momentum q has fibre norm ≤ Cd(q)^{−s} and
  {#B4.223} q-derivative ≤ Cd(q)^{−s}(1 + d(q)^{−1}), by Δ(q) ≥ (4/π²)|q|² (§7's Bloch norms), uniformly in η.
- {#B4.224} *Degree count.* Each insertion of X(1, j) has degree ≤ 1: in (7.1) each term contains one φ, the third also Dφ of
  {#B4.225} degree 0, and Δ′_π and Δ^{(2)}_π are regular.
  {#B4.225-1} The U-derivative raises the degree by at most 1: K(1, 𝐇(1)A₁) has
  {#B4.226} degree ≤ 1, and replacing φ_A by its derivative, or Dφ_A by D₁φ_A + ∂(∂ᵀ∂)^{−1}[D₁ᵀΠ_⊥A − ∂ᵀD₁φ_A], raises the
  {#B4.227} degree of that term by at most 1.
  {#B4.227-1} Θ₁ has one j and one U-derivative, and F_jj two j's and none.
  {#B4.227-2} So every integrand
  {#B4.228} has degrees (a, b) at (q, q + p) with a + b ≤ 2, and its p-derivative raises b by at most 1 or falls on a regular
  {#B4.229} factor.
- {#B4.230} By Lemma 4.3, with M and n bounded in terms of d, L, G, and PBG's constants: ‖τ(p) − τ(0)‖ ≤ C|p| for |p| ≤ π, and
  {#B4.231} ‖τ(p)‖, ‖R̃(p)‖ ≤ C for all p.

{#B4.232} *(e) Pure gauge.* For B = D̄ω, the minimum of ‖∂A‖² on {Q̃_{k+1}A = D̄ω} is 0, attained at a gradient (QD = D̄P,
{#B4.233} §3.1).
{#B4.233-1} So A₁ has zero curvature, hence is a gradient for p ≠ 0, Θ₁B = 0 by (c), and τ(p)v(p) = 0 for p ≠ 0; at p = 0,
{#B4.234} v(0) = 0.

{#B4.235} *(f) Conclusion.* τ is 2πℤ⁴-periodic and bounded, so ‖τ(p) − τ(0)‖ ≤ C|p| holds for all p. By (e) and Lemma 4.1(b)
{#B4.236} with γ = 1, ‖τ(p)‖ ≤ C|p|.
{#B4.236-1} By (c) and (d), ‖Π_J^{(k)}(p)‖ ≤ C|p|·C|p|² + C|p|⁴ for p ≢ 0, and Π_J^{(k)} = 0 at p ≡ 0, since it is periodic and continuous there (#B3.2.85-1) and the right side tends to 0 as p → 0; so ‖Π_J^{(k)}(p)‖ ≤ C|p|³ for |p| ≤ π, and
{#B4.237} ‖Π_J^{(k)}(p)‖ ≤ C for all p. Since |p|³ ≤ π^{1−2α}|p|^{2+2α} for |p| ≤ π and 1 ≤ π^{−2−2α}|p|^{2+2α} for |p| ≥ π, the
{#B4.238} bound by C_α|p|^{2+2α} follows.
{#B4.238-1} The Lean core of the first bound of #B4.236-1 is `BalabanFormal.jterm_holder` with γ = 1.
{#B4.238-2} Its hypothesis
{#B4.239} ‖Δ(p)‖ ≤ MΔ|p|² is the bound of (c) (#B4.121), its hypothesis ‖τ(p) − τ(0)‖ ≤ Mτ|p| is the Lipschitz bound above, its hypothesis τ(p)v(p) = 0 is (e),
{#B4.240} and its hypothesis ‖Π_J(p)‖ ≤ K₁‖Δ(p)‖‖τ(p)‖ + K₂‖Δ(p)‖² for all p is the last bullet of (c) with K₂ a multiple of sup_p‖R̃(p)‖ (#B4.231), at p ≡ 0 as in #B4.236-1.
{#B4.240-1} The marginal coefficient is
{#B4.241} determined by the O(|p|²) part (RG1 (1.22)). ∎

## 5. The k-Step Total, and the J-Terms Seen from the Top {#BS5}

{#B5.1} **Conventions.**
- {#B5.2} Top units: T^{(k)} is the unit lattice, and the bare spacing is η_k = L^{−k}.
- {#B5.3} For a functional 𝔉 of the top field B, write 𝔉(e^{iB}) = 𝔉(1) + ½⟨B, Π_𝔉 B⟩ + O(B³), and call Π_𝔉(p) its
  {#B5.4} polarisation symbol.
- {#B5.5} A(U_k(e^{iB})) = ½⟨B, Δ_k B⟩ + O(B³).
  {#B5.5-1} Here Δ_k is Bałaban's coarse operator (PRT1 (1.65)–(1.67)): its symbol is
  {#B5.6} analytic, it annihilates pure gauge, and γ₀⟨∂₁B, ∂₁B⟩ ≤ ⟨B, Δ_k B⟩ ≤ γ₁⟨∂₁B, ∂₁B⟩ (PRT1 (1.67)) with γ₀, γ₁ depending only on d, ∂₁ being PRT1's unit-lattice differentiation (p.027 l.32), the curl on the 1-form B.
- {#B5.7} **𝔅_r**: the complex ball of top fields with sup|B| ≤ r and sup|∂̄B| ≤ r (top units), ∂̄B := (∂_μB_ν)_{μ,ν} being the forward lattice differences of all components of B.
- {#B5.8} **Analyticity of the background.** For r small, U_k(e^{iB}) with B ∈ 𝔅_r lies in the complex regularity spaces
  {#B5.9} U_j^c(X, α_0, α_1) of RG1 (1.11)–(1.16), for every j ≤ k (VAR Thm 1, §G and (181); RG1 p.263).
  {#B5.9-1} So every functional
  {#B5.10} below that Bałaban proves analytic on those spaces is analytic in B ∈ 𝔅_r.
- {#B5.11} **Cauchy estimate.** Let 𝔉(B) be analytic on 𝔅_r, translation-covariant, and bounded by M_𝔉 per top unit cube.
  {#B5.11-1} Then its
  {#B5.12} polarisation symbol satisfies ‖Π_𝔉(p)‖ ≤ 16M_𝔉/r² for all p. For unit vectors v, w put B := ve^{ip·Y} and B′ := we^{−ip·Y}. For |s|, |t| ≤ r/4, sB + tB′ has sup|·| ≤ r/2 and sup|∂̄·| ≤ r, as |e^{iθ} − 1| ≤ 2, so it lies in 𝔅_r, where |𝔉| ≤ M_𝔉|T|, |T| the number of top unit cubes.
  {#B5.13} The st-coefficient of 𝔉(sB + tB′) is ⟨B′, Π_𝔉B⟩ = |T|wᵀΠ_𝔉(p)v, by translation covariance, and Cauchy's estimate on |s| = |t| = r/4 bounds it by 16M_𝔉|T|/r²; the supremum over v, w is ‖Π_𝔉(p)‖. It is applied to the localized terms of RG1 (0.29).

{#B5.14} **Proposition 5.1 (Total).** Let ℒ_k(B) := Σ_{j=1}^{k} E^{(j)}(0, U_k(e^{iB})), the zero-coupling step terms of
{#B5.15} RG1 (1.6) evaluated at the top background, i.e. the k-step Gaussian.
{#B5.15-1} Then (RG1 (0.28)–(0.30); proof below)
  {#B5.16} Π_{ℒ_k}(p) = Φ_k Δ_k(p) + ℰ_k(p),  Φ_k := Σ_{j=1}^{k} b_j,  sup_p ‖ℰ_k(p)‖ ≤ C,
{#B5.17} with C independent of k.

{#B5.18} *Proof.*
1. {#B5.19} By RG1 (0.28), E^{(j)}(U_k) = β_jA(U_k) + Σ_{X∈D_j} V^{(j)}(X, U_k).
2. {#B5.20} Each V^{(j)}(X, ·) is analytic on U_j^c, with |V^{(j)}(X, U)| ≤ O(1)(L^jη)^{4+α} e^{−κ d_j(X)} (RG1 (0.29), α > 0).
   {#B5.21} As in RG1 (0.30), the sum over X meeting a fixed top unit cube is at most C(L^jη)^α.
3. {#B5.22} By the Cauchy estimate, the polarisation of Σ_X V^{(j)} is bounded by C(L^{j−k})^α.
   {#B5.22-1} Summing over j ≤ k gives at
   {#B5.23} most C(1 − L^{−α})^{−1}.
4. {#B5.24} At zero coupling β_j = b_j, and the polarisation of A(U_k(e^{iB})) is Δ_k. ∎

{#B5.25} **Lemma 5.2 (Alias Summability).** At U = 1, for every k and every coarse momentum p (top units),
  {#B5.26} Σ_{l} |(d_ηH_k)^∧(p + l)| · |p + l|^α ≤ C,
{#B5.27} where the sum runs over the aliases p + l of p in the fine Brillouin zone, (d_ηH_k)^∧ is the symbol of B ↦ d_η(H_kB) (d_η of #B5.123-1 at ε = η), α ∈
{#B5.28} (0,1) is fixed once, and C depends only on d and α.
{#B5.28-1} PRT1 pp.28–29 states a bound of this kind after PRT1 (1.63), with
{#B5.29} the exponent α not defined on that page; the proof below derives it from PRT1 (1.63) for every α ∈ (0, 1).

{#B5.30} *Proof.* We use PRT1's units: the coarse lattice has spacing 1, the fine lattice spacing η = L^{−k}, p ∈ [−π, π)^d, and
{#B5.31} l_μ = 2πm_μ with |m_μ| ≤ (L^k − 1)/2 (PRT1 p.23).
{#B5.31-1} Write q := p + l, Δ(q) = Σ_μ|∂_μ(q)|² with ∂_μ(q) = (e^{iηq_μ} − 1)/η,
{#B5.32} Δ₀(p) = Σ_μ|∂¹_μ(p)|² with ∂¹_μ(p) = e^{ip_μ} − 1, u(q) = ∏_μ ∂¹_μ(p)/∂_μ(q), and v_μ(q) = ∂¹_μ(p)/∂_μ(q) (PRT1 (1.31),
{#B5.33} (1.61), and p.24).
1. {#B5.34} *Elementary bounds.* Since |e^{ix} − 1| = 2|sin(x/2)| lies between (2/π)|x| and |x| for |x| ≤ π, and |ηq_μ| ≤ π,
   - {#B5.35} (2/π)|q_μ| ≤ |∂_μ(q)| ≤ |q_μ|, so (4/π²)|q|² ≤ Δ(q) ≤ |q|², and (4/π²)|p|² ≤ Δ₀(p) ≤ |p|²;
   - {#B5.36} |∂¹_μ(p)| ≤ |p_μ| ≤ |q_μ|, since |p_μ| ≤ π ≤ |p_μ + l_μ| when l_μ ≠ 0; so |v_μ(q)| ≤ π/2, |u(q)| ≤ (π/2)^d, and
     {#B5.37} |∂_μ(q)||v_μ(q)| = |∂¹_μ(p)| ≤ 2;
   - {#B5.38} |q_μ| ≥ |l_μ|/2, so |q| ≥ |l|/2;
   - {#B5.39} if l_μ ≠ 0, then |l_μ| ≥ 2π and |v_μ(q)| ≤ (π/2)|p_μ|/|q_μ| ≤ π²/|l_μ| ≤ c_v(1 + |l_μ|)^{−1}, with
     {#B5.40} c_v := π² + π/2; with |v_μ(q)| ≤ π/2 when l_μ = 0, this gives |v_μ(q)| ≤ c_v(1 + |l_μ|)^{−1} for all l, and
     {#B5.41} |u(q)| ≤ c_v^d∏_μ(1 + |l_μ|)^{−1}. This is PRT1 (1.36), p.24, with a constant depending only on d;
   - {#B5.42} at q = p, |v_μ(p)| ≥ 2/π and |u(p)| ≥ (2/π)^d (extended by continuity where p_μ = 0).
   {#B5.43} PRT1 p.28 prints 0 < γ₀ ≤ Δ₀(p)φ_μ(p) ≤ γ₁ for all p, with φ_μ(p) = Σ_{l′}|u(p + l′)|²|v_μ(p + l′)|²/Δ(p + l′)
   {#B5.44} (PRT1 (1.62)), and does not state how γ₀ and γ₁ depend on k.
   {#B5.44-1} The bullets above give such bounds with constants
   {#B5.45} c₀, c₁ depending only on d.
   {#B5.45-1} The term l′ = 0 of Δ₀(p)φ_μ(p) is Δ₀(p)|u(p)|²|v_μ(p)|²/Δ(p); it is at least
   {#B5.46} (4/π²)(2/π)^{2d}(2/π)² = (2/π)^{2d+4} =: c₀ and at most (π²/4)(π/2)^{2d+2}.
   {#B5.46-1} For l′ ≠ 0, Δ(p + l′) ≥ (4/π²)|l′|²/4 and
   {#B5.47} Δ₀(p) ≤ dπ², so Δ₀(p)/Δ(p + l′) ≤ dπ⁴/|l′|² ≤ dπ²/4, and the term is at most (dπ²/4)c_v^{2d+2}∏_ν(1 + |l′_ν|)^{−2}.
   {#B5.48} So c₀ ≤ Δ₀(p)φ_μ(p) ≤ c₁ := (π²/4)(π/2)^{2d+2} + (dπ²/4)c_v^{2d+2}(Σ_{m∈ℤ}(1 + 2π|m|)^{−2})^d.
   {#B5.49} Put N(p) := Σ_{l″}|u(p + l″)|²Δ₀(p)²/Δ(p + l″)².
   {#B5.49-1} Its term l″ = 0 gives N(p) ≥ (2/π)^{2d}(4/π²)² =: c_N.
2. {#B5.50} *The symbol of H_k.* PRT1 (1.63) writes (H_kB)^∧_μ(q) as T₁ + T₂, both linear in B̂(p).
   - {#B5.51} T₁ = (Δ₀(p)/Δ(q))ū(q)v̄_μ(q)(Δ₀(p)φ_μ(p))^{−1}B̂_μ(p), so |T₁| ≤ (π/(2c₀))Δ₀(p)|u(q)|Δ(q)^{−1}|B̂(p)|.
   - {#B5.52} T₂ is ∂_μ(q)ū(q)Δ(q)^{−1} times Σ_{l′≠l}|u(p + l′)|²Δ₀(p)²Δ(p + l′)^{−1}[|v_μ(p + l′)|²Δ(q)^{−1} −
     {#B5.53} |v_μ(q)|²Δ(p + l′)^{−1}], times N(p)^{−1}(Δ₀(p)φ_μ(p))^{−1}, times b(p) := (Σ_ν|∂¹_ν(p)|²/(Δ₀(p)²φ_ν(p)))^{−1}
     {#B5.54} Σ_λ \overline{∂¹_λ(p)}(Δ₀(p)φ_λ(p))^{−1}B̂_λ(p).
     {#B5.54-1} The first sum of the bracket, extended to all l′, is Δ₀(p)²φ_μ(p)Δ(q)^{−1} ≤
     {#B5.55} c₁Δ₀(p)Δ(q)^{−1}; the second, extended to all l′, is |v_μ(q)|²N(p).
     {#B5.55-1} Since Σ_ν|∂¹_ν(p)|²/(Δ₀(p)²φ_ν(p)) ≥
     {#B5.56} Δ₀(p)/(c₁Δ₀(p)) = 1/c₁ and Σ_λ|∂¹_λ(p)|(Δ₀(p)φ_λ(p))^{−1} ≤ √d|∂¹(p)|/c₀, |b(p)| ≤ (c₁√d/c₀)|∂¹(p)||B̂(p)|.
     {#B5.56-1} So
       {#B5.57} |T₂| ≤ (c₁√d/c₀²)|∂_μ(q)||u(q)|Δ(q)^{−1}[c₁Δ₀(p)/(c_NΔ(q)) + |v_μ(q)|²]|∂¹(p)||B̂(p)|.
3. {#B5.58} *The term l = 0.* Here q = p, and by step 1 the factors Δ₀(p)/Δ(p), |∂_μ(p)||∂¹(p)|/Δ(p), and |v_μ(p)| are bounded
   {#B5.59} by constants depending on d.
   {#B5.59-1} So |(H_kB)^∧(p)| ≤ C₁|B̂(p)|, and |(d_ηH_k)^∧(p)||p|^α ≤ 2|∂(p)|C₁|p|^α ≤ C₂, with
   {#B5.60} |p| ≤ π√d.
4. {#B5.61} *The terms l ≠ 0.* Here |q| ≥ π.
   {#B5.61-1} By step 1, |T₁| ≤ C|u(q)||q|^{−2}; in T₂, |∂_μ(q)|Δ(q)^{−2} ≤ C|q|^{−3} and
   {#B5.62} |∂_μ(q)||v_μ(q)|² ≤ π, so |T₂| ≤ C|u(q)||q|^{−2}, all times |B̂(p)|. The curvature (d_ηA)_{μν} has the symbol
   {#B5.63} ∂_μ(q)Â_ν(q) − ∂_ν(q)Â_μ(q), and Σ_{μ,ν}|a_μb_ν − a_νb_μ|² ≤ 4|a|²|b|², so |(d_ηH_k)^∧(q)| ≤ 2|∂(q)||(H_kB)^∧(q)|/|B̂(p)| ≤ 2√d|q|max_μ|(H_kB)^∧_μ(q)|/|B̂(p)| ≤ C|u(q)||q|^{−1}, and
     {#B5.64} Σ_{l≠0}|(d_ηH_k)^∧(q)||q|^α ≤ C Σ_{l≠0}|q|^{α−1}|u(q)| ≤ C Σ_{l≠0}|l|^{α−1}∏_μ(1 + |l_μ|)^{−1}.
   {#B5.65} Since ∏_μ(1 + |l_μ|) ≤ (1 + |l|)^d ≤ (2|l|)^d and α − 1 < 0, |l|^{α−1} ≤ 2^{1−α}∏_μ(1 + |l_μ|)^{(α−1)/d}, and the sum
   {#B5.66} is at most 2^{1−α}(Σ_{m∈ℤ}(1 + 2π|m|)^{−1−(1−α)/d})^d, which is finite and depends only on d and α.
{#B5.67} With step 3 this gives C = C(d, α), independent of k and p. ∎

{#B5.68} **Proposition 5.3 (J-Terms, Total).** Let 𝒥_k(B) := Σ_{j=0}^{k−1} J^{(j)}(U_k(e^{iB})), with J^{(j)} as in §3.3.
{#B5.68-1} Then
{#B5.69} sup_p ‖Π_{𝒥_k}(p)‖ ≤ C, uniformly in k (from PRT1 (1.63) and Lemma 5.2; proof below).
{#B5.69-1} The summation of steps 2–5 is the
{#B5.70} type-checked Lean core `BalabanFormal.jterm_assembly`.

{#B5.71} *Proof.* Fix j and set m := j+1 ≤ k.
1. {#B5.72} *Reduction to level m.* Let V*(B) := (U_k(e^{iB}))^{(m)}.
   {#B5.72-1} For B small, V*(B) is near 1, so U_m(V*(B)) is defined.
   {#B5.73} U_k(e^{iB}) and U_m(V*(B)) agree up to a gauge transformation equal to 1 on T^{(m)}.
   {#B5.73-1} Indeed, M^k is M^{k−m} after
   {#B5.74} M^m, so a minimiser on {U : M^k(U) = e^{iB}} also minimises on the subset {U : M^m(U) = V*(B)}, and the minimal orbit
   {#B5.75} there is unique under the gauge transformations equal to 1 on T^{(m)} (RG1 (0.21)–(0.22), p.256).
   {#B5.75-1} J^{(j)} is
   {#B5.76} invariant under every fine gauge transformation g, since J^{(j)}(U) = F(U, J(U)) + const with F(U^g, Ad(g)j) =
   {#B5.77} F(U, j) and J(U^g) = Ad(g)J(U) (Proposition 4.2(b)).
   {#B5.77-1} So J^{(j)}(U_k(e^{iB})) = J^{(j)}(U_m(V*(B))).
   {#B5.77-2} The first-order
   {#B5.78} part of V*(B) is iL^{m−k}Q_mH_kB, with Q_m the straight average of #B5.141 and L^{m−k} the level-m spacing in top units, up to a level-m field of zero curvature (*Zero-curvature terms* below).
   {#B5.78-1} J^{(j)} ∘ U_m has
   {#B5.79} zero first-order coefficient at the trivial background (Proposition 4.2(c)).
   {#B5.79-1} So the top polarisation of
   {#B5.80} J^{(j)}(U_k(e^{iB})) is ⟨V_1, Π_J^{(j)} V_1⟩ with V_1 := Q_m H_k B, the level-m pairing of the level-m bond logarithm L^{m−k}V_1 (step 2 converts it to top units). Here Π_J^{(j)} is the level-m symbol of
   {#B5.81} Proposition 4.2, for the step J-term J^{(j)} of §3.3: for a fixed
   {#B5.82} α ∈ (0, ½), ‖Π_J^{(j)}(p′)‖ ≤ C_α|p′|^{2+2α} on the whole level-m zone, and it is transverse
   {#B5.83} (Π_J^{(j)}(p′)v(p′) = 0, since Δ_{m}(p′)v(p′) = 0 and τ(p′)v(p′) = 0 in Proposition 4.2(c), (e)).

   {#B5.84} *Zero-curvature terms.* The first-order part of V*(B) differs from iL^{m−k}Q_mH_kB by a level-m field
   {#B5.86} of zero curvature (next paragraph and step 4).
   {#B5.86-1} Such a field is a gradient plus a constant.
   {#B5.86-2} Π_J^{(j)} annihilates it:
   {#B5.87} transversality kills the gradient, and the factor |p′|^{2+2α} of Proposition 4.2 kills the constant.
   {#B5.87-1} So it does not change
   {#B5.88} ⟨V_1, Π_J^{(j)} V_1⟩.

   {#B5.89} *The first-order background.* By RG1 (0.21)–(0.22), p.256 (contract RG1_021_orbit), U_k(V) lies in the unique regular
   {#B5.90} orbit of minimisers of the Wilson action on {U : M^k(U) = V}, under the gauge transformations equal to 1 on T^{(k)},
   {#B5.91} which leave M^k unchanged.
   {#B5.91-1} At V = 1 the configuration 1 is such a minimiser (its action is zero), so the representative
   {#B5.92} can be chosen with U_k(1) = 1.
   {#B5.92-1} Then U(t) := U_k(e^{itB}) = exp(itηA_1 + O(t²)) bondwise, analytic in t (VAR §G).
   {#B5.92-2} Let Q̃_k
   {#B5.93} be the first-order part of M^k at U = 1, in the normalisation of step 4.
   {#B5.93-1} Step 4's computation with m = k gives
   {#B5.94} Q̃_kA = Q_kA + ∂ω_k(A), with ω_k linear and ∂ the gradient on T^{(k)}.
   {#B5.94-1} The constraint gives Q̃_kA_1 = B, so Q̃_k is
   {#B5.95} onto.

   {#B5.96} Three facts give d_ηA_1 = d_ηH_kB.
   - {#B5.97} A_1 minimises ‖d_ηA‖² over {A : Q̃_kA = B}.
     {#B5.97-1} Since Q̃_k is onto and M^k is analytic near 1, the implicit function
     {#B5.98} theorem gives, for each such A, regular U_t = exp(itηA + O(t²)) with M^k(U_t) = e^{itB}.
     {#B5.98-1} At U = 1 the quadratic part
     {#B5.99} of the Wilson action (RG1 p.252) is ½‖d_ηX‖² := ½Σ_pη^d tr((d_ηX)(p)²), with U = e^{iηX}, PRT1 (1.3)'s form with #T6.23's ‖X‖² = tr X*X on Hermitian g in place of PRT1's |·|²: U(∂p) = exp(iη²((d_ηX)(p) + O(X²))), and 1 − Re tr e^{iY} = ½tr Y² + O(Y⁴), as tr Y³ is real.
     {#B5.99-1} Minimality, divided by ½, gives
     {#B5.100} t²‖d_ηA_1‖² + O(t³) ≤ t²‖d_ηA‖² + O(t³); divide by t² and let t → 0.
   - {#B5.101} The sets {d_ηA : Q̃_kA = B} and {d_ηA : Q_kA = B} coincide.
     {#B5.101-1} A gauge transformation A ↦ A − ∂^ηλ changes Q_kA by
     {#B5.102} −∂Q′_kλ (PRT1 (1.20), p.20).
     {#B5.102-1} By the gauge covariance of RG1 (0.4) and (0.12) (RG1 (0.6) for (0.11)), it changes Q̃_kA by the gradient of −λ on
     {#B5.103} T^{(k)}.
     {#B5.103-1} Either change can be chosen to cancel ∂ω_k(A), and neither changes d_ηA.
     {#B5.103-2} The common set is affine, so
     {#B5.104} ‖·‖² has exactly one minimiser on it.
   - {#B5.105} H_kB attains that minimum.
     {#B5.105-1} PRT1 p.29 gives H_kB as a minimiser of ½⟨∂A, ∂A⟩ on {Q_kA = B, R∂*A = 0}.
     {#B5.105-2} That slice
     {#B5.106} meets every orbit of the gauge transformations λ with Q′_kλ = 0.
     {#B5.106-1} R is the orthogonal projection onto ΔN(Q′_k)
     {#B5.107} (PRT1 p.25), so λ ∈ N(Q′_k) with Δλ = R∂*A gives R∂*(A − ∂λ) = 0.
     {#B5.107-1} PRT1's blocks are corner blocks (PRT1 p.18),
     {#B5.108} RG1's are centred: the centred Q_k is PRT1's Q_k composed with a fixed fine translation T, so the centred H_k is
     {#B5.109} T^{−1} composed with PRT1's H_k, and R transforms in the same way.
     {#B5.109-1} Minimality and curvature norms are
     {#B5.110} translation invariant, so the fact holds for the centred blocks.

   {#B5.111} So A_1 − H_kB has zero curvature, and its level-m average plus the gradient of step 4 has zero curvature too.
   {#B5.111-1} The same
   {#B5.112} three facts give the expansion A(U_k(e^{iB})) = ½⟨B, Δ_kB⟩ + O(B³) of the conventions, since PRT1 p.29 defines
   {#B5.113} ⟨B, Δ_kB⟩ as ⟨∂H_kB, ∂H_kB⟩.
2. {#B5.114} *Change of units.* Write V_1 in top units: modes q with |q_μ| ≤ π L^{k−m}, and level-m momentum p′ = L^{−(k−m)}q.
   {#B5.115} A level-m bond carries L^{−(k−m)} times the top amplitude, and there are L^{4(k−m)} level-m sites per top site.
   {#B5.115-1} So,
   {#B5.116} with |p′|^{2+2α} = L^{−(2+2α)(k−m)}|q|^{2+2α},
     {#B5.117} |⟨V_1, Π_J^{(j)} V_1⟩| ≤ C_α L^{2(k−m)} Σ_q |p′|^{2+2α} |V̂_1(q)|² = C_α L^{−2α(k−m)} Σ_q |q|^{2α} |q|² |V̂_1(q)|².
3. {#B5.118} *Transversality.* Let Ṽ_1(q) be the component of V̂_1(q) orthogonal to v(p′). Π_J^{(j)}(p′) is Hermitian and annihilates v(p′) (step 1), so ⟨V̂_1, Π_J^{(j)}V̂_1⟩ = ⟨Ṽ_1, Π_J^{(j)}Ṽ_1⟩, and step 2 holds with Ṽ_1 in place of V̂_1. The symbol of d̄'s difference in direction μ is L^{k−m}(e^{iL^{m−k}q_μ} − 1) = L^{k−m}v_μ(p′), so Lagrange's identity Σ_{μ<ν}|a_μV_ν − a_νV_μ|² = |a|²|V|² − |Σ_μa_μV̄_μ|² gives |(d̄V_1)^∧|² = L^{2(k−m)}|v(p′)|²|Ṽ_1|². As L^{k−m}|v_μ(p′)| ≥ (2/π)|q_μ| for |L^{m−k}q_μ| ≤ π, |q|²|Ṽ_1|² ≤ C_⊥|(d̄V_1)^∧|² with C_⊥ := π²/4.
   {#B5.118-1} So
     {#B5.119} |⟨V_1, Π_J^{(j)} V_1⟩| ≤ C_αC_⊥ L^{−2α(k−m)} Σ_q |q|^{2α} |(d̄V_1)^∧(q)|²
   {#B5.120} (hypothesis `hunits` of `BalabanFormal.jterm_assembly`).
4. {#B5.121} *Alias summability.* Set η := L^{−k}; L is odd (RG1 p.251 l.14), so L^m is odd.
   {#B5.121-1} In top units the fine lattice has spacing η and the
   {#B5.122} level-m lattice has spacing L^{m−k}.
   {#B5.122-1} Fields are in physical normalisation: a bond of length ε carries the
   {#B5.123} logarithm εA_μ.
   {#B5.123-1} The lattice curl at spacing ε is (d_εA)_{μν}(x) := ε^{−1}(A_ν(x + εe_μ) − A_ν(x) − A_μ(x + εe_ν) +
   {#B5.124} A_μ(x)), and d̄V_1 means d_{L^{m−k}}V_1.

   {#B5.125} *The first-order level-m average.* The chain averages with RG1 (0.4), p.253, or (0.12), p.254 (#B0.37-0).
   {#B5.125-1} Its m-th order average
   {#B5.126} is the m-fold iterate of the one-step average by construction: each step's kernel is the one-step
   {#B5.127} δ(Ū(c)V^{−1}(c)) (RG1 (0.17), (0.19), p.255).
   {#B5.127-1} At U = 1, on a coarse bond c with c₊ = c₋ + Le_μ, the first-order part
   {#B5.128} of the logarithm in RG1 (0.4), and in (0.12), whose linear part is the same (#B4.187), is

     {#B5.129} Σ_{x∈B(c₋)} L^{−d} A([x, x′]) + ω(c₋) − ω(c₊),  ω(y) := Σ_{x∈B(y)} L^{−d} |G(y, x)|^{−1} Σ_{Γ∈G(y,x)} A(Γ),

   {#B5.130} with A(Γ) the sum of the bond logarithms along Γ.
   {#B5.130-1} Indeed, the loop logarithm is A(Γ) + A([x, x′]) − A(Γ′) − A(c) to
   {#B5.131} first order, the term −A(c) cancels against the factor U(c), and x ↦ x′ = x + Le_μ maps B(c₋) onto B(c₊), so the
   {#B5.132} average of −A(Γ′) over G(c₊, x′) sums to −ω(c₊).
   {#B5.132-1} This is L times PRT1 (1.8), p.19 (PRT1 normalises per unit coarse length), with the single contour
   {#B5.133} replaced by the average over G(y, x).
   {#B5.133-1} Its first term is L times PRT1's straight average PRT1 (1.11), and its endpoint
   {#B5.134} terms form a coarse gradient.

   {#B5.135} A straight average of a gradient is the gradient of the block means, so later averaging steps carry gradients to
   {#B5.136} gradients.
   {#B5.136-1} The composition of m straight averages over centred blocks is the straight average over the centred block
   {#B5.137} of side L^m. PRT1 (1.16)–(1.18), p.20, states this for corner blocks ("It is easily seen").
   {#B5.137-1} For corner and centred
   {#B5.138} blocks alike the path offsets sL + t run once over {0, …, L² − 1}, and for centred blocks the offsets Lr + o,
   {#B5.139} with r and o in the centred block of side L, run once over the centred block of side L².
   {#B5.139-1} So the first-order level-m
   {#B5.140} bond logarithm is L^{m−k}Q_mA plus a level-m gradient, where

     {#B5.141} (Q_mA)_μ(Y) := |B_m|^{−1} Σ_{r∈B_m} L^{−m} Σ_{t=0}^{L^m−1} A_μ(η(L^mY + r + te_μ)),  B_m := {−(L^m − 1)/2, …, (L^m − 1)/2}⁴.

   {#B5.142} The gradient has zero curl, and Π_J^{(j)} is transverse (step 1), so the gradient drops out of ⟨V_1, Π_J^{(j)}V_1⟩.
   {#B5.143} RG1's blocks are centred at the coarse points (RG1 p.252), and PRT1's blocks need not be.
   {#B5.143-1} A translation of the blocks
   {#B5.144} multiplies every Fourier coefficient by a unit phase, so none of the absolute values below changes.

   {#B5.145} *The curvature identity.* The curl of a straight-path average is the sum of the fine plaquettes in the L^m × L^m square
   {#B5.146} that the path sweeps out (discrete Stokes).
   {#B5.146-1} Hence d_{L^{m−k}}Q_mA = P_m d_ηA, where

     {#B5.147} (P_mF)_{μν}(Y) := |B_m|^{−1} L^{−2m} Σ_{r∈B_m} Σ_{a,b=0}^{L^m−1} F_{μν}(η(L^mY + r + ae_μ + be_ν)).

   {#B5.148} The weights of P_m are nonnegative and sum to one.
   {#B5.148-1} On a fine
   {#B5.149} plane wave of momentum p, P_m therefore acts as a symbol P̂_m(p) with |P̂_m(p)| ≤ 1, times the level-m character of p.

   {#B5.150} *Folding.* Π_{𝒥_k}(p) is Hermitian, so its norm is the supremum of |⟨B̂, Π_{𝒥_k}(p)B̂⟩|/‖B̂‖², and it suffices to take a single top mode B = B̂(p)e^{ip·Y}, with every pairing normalised per top site.
   {#B5.150-1} At U = 1 the fine field H_kB is then a finite sum of plane waves with momenta
   {#B5.151} p_a = p + l_a, with l_a running over the aliases of Lemma 5.2 (PRT1 (1.63)).
   {#B5.151-1} Write ĉ_{μν}(a) for the coefficient of (d_ηH_kB)_{μν} at p_a.
   {#B5.151-2} Subtract
   {#B5.152} from each component of p_a a multiple of 2πL^{k−m} to land in (−πL^{k−m}, πL^{k−m}]; call the result q(a).
   {#B5.152-1} On the level-m
   {#B5.153} lattice p_a and q(a) have the same character, and |q(a)| ≤ |p_a| in the Euclidean norm.
   {#B5.153-1} Distinct representatives give
   {#B5.154} distinct characters, so the Fourier coefficient of (d̄V_1)_{μν} at q is Σ_{a: q(a)=q} P̂_m(p_a)ĉ_{μν}(a).
   {#B5.154-1} Hence, with
   {#B5.155} the last step from Lemma 5.2,
     {#B5.156} Σ_q |q|^{2α}‖(d̄V_1)^∧_{μν}(q)‖² ≤ Σ_q (Σ_{a: q(a)=q} |p_a|^α‖ĉ_{μν}(a)‖)² ≤ (Σ_a |p_a|^α‖ĉ_{μν}(a)‖)² ≤ C²‖B̂(p)‖².

   {#B5.157} Here C = C(d, α) is the constant of Lemma 5.2, which bounds the curvature symbol itself: ‖ĉ_{μν}(a)‖ ≤ |(d_ηH_k)^∧(p_a)|‖B̂(p)‖.
   {#B5.157-1} The
   {#B5.158} norms are the invariant norms on the Lie algebra: at U = 1, H_k acts on every Lie-algebra component in the same way.

   {#B5.159} Summing over the six planes μ < ν gives, by Lemma 5.2,
     {#B5.160} Σ_q |q|^{2α}‖(d̄V_1)^∧(q)‖² ≤ 6C²‖B̂(p)‖²,
   {#B5.161} uniformly in k and m, which is the bound step 3 needs.
5. {#B5.162} *Sum.* Σ_{m≤k} L^{−2α(k−m)} ≤ (1 − L^{−2α})^{−1} (`BalabanFormal.jterm_assembly`). ∎

## 6. The Bare-Lattice One-Loop Polarisation {#BS6}

{#B6.1} **Notation.** Lattice units (bare spacing 1), momenta ξ, k ∈ T⁴ = [−π, π]⁴, s(k) := Σ_μ 4 sin²(k_μ/2) = |k|² + O(|k|⁴).
{#B6.1-1} Λ is a finite torus of the bare lattice in these units and |Λ| its number of sites; as in Remark 3.4, the symbols are the limits of its momentum sums |Λ|^{−1}Σ_k, written ∫_{T⁴} d⁴k/(2π)⁴.

### 6.1 The Infrared Lemma {#BS6.1}

{#B6.1.1} **Lemma 6.1.** Let N(k, ξ) be a matrix-valued trigonometric polynomial in (k/2, ξ/2) with N(−k, −ξ) = N(k, ξ) and N(0, 0) = 0.
{#B6.1.1-1} Write N = N_2 + N_r,
{#B6.1.2} where N_2 is a homogeneous polynomial of degree 2 in (k, ξ) and |N_r| ≤ C(|k| + |ξ|)³ near 0 (`SmoothNum.lemma61`).
{#B6.1.2-1} Set
  {#B6.1.3} I(ξ) := ∫_{T⁴} N(k, ξ) / (s(k) s(k+ξ)) d⁴k/(2π)⁴.
{#B6.1.4} Then, as ξ → 0,
  {#B6.1.5} I(ξ) = a_0 + a_1·ξ + Σ(ξ) ln(1/|ξ|) + O(|ξ|²),  Σ(ξ) := (2π)^{−4} ∫_{S³} f_2(ω, ξ) dσ(ω),
{#B6.1.6} where f_2(k, ξ) is the part quadratic in ξ of the Taylor expansion of f(k, ξ) := N_2(k, ξ)/(|k|²|k+ξ|²) at ξ = 0, for k ∈ ℝ⁴ ∖ {0}.
{#B6.1.7} Single-propagator integrals ∫ Ñ(k, ξ)/s(k) with Ñ a trigonometric polynomial in (k/2, ξ/2) are C^∞ in ξ.
{#B6.1.7-1} In fact a_0 = I(0) and a_1 = 0.

{#B6.1.8} The type-checked Lean core `SmoothNum.lemma61` covers steps 0–4 below, for scalar N that is C³, even and zero at 0,
{#B6.1.9} with the bounds of step 0 derived rather than assumed.
{#B6.1.9-1} The hypotheses hold for N(k, ξ) = Σ_μ sin k_μ sin(k_μ + ξ_μ).

{#B6.1.10} *Proof.* Let G(k, ξ) := N(k, ξ)/(s(k)s(k+ξ)) and Δ²G(k) := G(k, ξ) + G(k, −ξ) − 2G(k, 0).
{#B6.1.10-1} The substitution k ↦ −k,
{#B6.1.11} with the parity of N and of s, gives I(−ξ) = I(ξ).
{#B6.1.11-1} Hence a_1 = 0 and
  {#B6.1.12} I(ξ) − I(0) = ½ ∫_{T⁴} Δ²G(k) d⁴k/(2π)⁴.

{#B6.1.13} Take
{#B6.1.14} 0 < |ξ| ≤ π/16.
{#B6.1.14-1} Work entrywise, so N is scalar, and use the norm |(k, ξ)| := max(|k|, |ξ|) on ℝ⁴ × ℝ⁴
{#B6.1.15} (`SmoothNum.lemma61`).
0. {#B6.1.16} *Bounds on N.* Only three properties of N are used: N is C³, N is even, and N(0, 0) = 0.
   - {#B6.1.17} Evenness gives DN(0) = 0, so the Taylor polynomial forces N_2 = ½D²N(0).
   - {#B6.1.18} Let M_N bound |D²N| and |D³N| on the ball of points q = (k, ξ) with |q| ≤ 2π + 1.
     {#B6.1.18-1} This ball contains every (k, ξ) with k ∈ [−π, π]⁴ and
     {#B6.1.19} |ξ| ≤ π/8.
   - {#B6.1.20} The mean-value theorem on the ball of radius |q|, applied in turn to DN, N, D²N_r, DN_r and N_r (each vanishes
     {#B6.1.21} at 0), gives |DN(q)| ≤ M_N|q|, |N(q)| ≤ M_N|q|², and |DᵗN_r(q)| ≤ M_N|q|^{3−t} for t = 0, 1, 2.
   - {#B6.1.22} For F ∈ {N, N_r}, the mean-value theorem along v ↦ (k, v), |v| ≤ |ξ|, gives
     {#B6.1.23} |F(k, ξ) − F(k, 0)| ≤ |ξ| sup|DF|. Applied to v ↦ F(k, v) − DF(k, 0)(0, v), it gives
     {#B6.1.24} |Δ²F| ≤ 2|ξ|² sup|D²F|; the linear terms cancel in Δ².
   - {#B6.1.25} If |ξ| ≤ |k|/2, every point of the segment has norm |k|.
     {#B6.1.25-1} Hence N ∈ DC(2) and N_r ∈ DC(3) on
     {#B6.1.26} {0 < |k| ≤ π/2, |ξ| ≤ |k|/2}, with constant 2M_N.
   - {#B6.1.27} On the outer region (k ∈ [−π, π]⁴, |k| ≥ π/2, |ξ| ≤ π/8), the same estimates with |k| ≤ 2π + 1 give N ∈ DC(0),
     {#B6.1.28} with constant 2M_N(2π + 1)².
     {#B6.1.28-1} Also |N(k, ξ)| ≤ M_N|(k, ξ)|² ≤ M_N(|k| + |ξ|)².
1. {#B6.1.29} *Second-difference calculus.* On {0 < |k| ≤ R, |ξ| ≤ |k|/2}, say F ∈ DC(m) if
   - {#B6.1.30} |F| ≤ C|k|^m,
   - {#B6.1.31} |F(k, ξ) − F(k, 0)| ≤ C|ξ||k|^{m−1},
   - {#B6.1.32} |Δ²F| ≤ C|ξ|²|k|^{m−2}.

   {#B6.1.33} The class DC is stable under the following operations (`SmoothNum.lemma61`):
   - {#B6.1.34} sums;
   - {#B6.1.35} products, by Δ²(F₁F₂) = Δ²F₁·F₂(k, 0) + F₁(k, 0)·Δ²F₂ + Δ⁺F₁Δ⁺F₂ + Δ⁻F₁Δ⁻F₂, with Δ^±F := F(k, ±ξ) − F(k, 0);
   - {#B6.1.36} reciprocals of functions with |F| ≥ c|k|^m, by 1/x₊ + 1/x₋ − 2/x₀ = (−x₀(x₊ + x₋ − 2x₀) − 2(x₊ − x₀)(x₋ − x₀))/(x₊x₋x₀) with x_± := F(k, ±ξ), x₀ := F(k, 0).

   {#B6.1.37} On bounded regions DC(m) ⊂ DC(m′) for m′ ≤ m.
   {#B6.1.37-1} Elementary trigonometry gives |k+ξ|² ∈ DC(2), s(k+ξ) ∈ DC(2) and
   {#B6.1.38} r_s(k+ξ) ∈ DC(4), with r_s(p) := |p|² − s(p) (`SmoothNum.lemma61`).
   {#B6.1.38-1} The ingredients are:
   - {#B6.1.39} cos(k ± ξ) = cos k cos ξ ∓ sin k sin ξ;
   - {#B6.1.40} |x − sin x| ≤ 2|x|³;
   - {#B6.1.41} |2 − 2cos y − y²| ≤ 5y⁴.

   {#B6.1.42} Also s(p) ≥ (36/25π²)|p|² when all |p_μ| ≤ 5π/4.
   {#B6.1.42-1} So h_s(p) := 1/s(p) − 1/|p|² = r_s(p)/(s(p)|p|²) satisfies h_s(k+ξ) ∈ DC(0)
   {#B6.1.43} (`SmoothNum.lemma61`).
2. {#B6.1.44} *Outer region* |k| ≥ π/2.
   {#B6.1.44-1} Here G = N·s(k)^{−1}·s(k+ξ)^{−1} ∈ DC(−4), so |Δ²G| ≤ C|ξ|².
   {#B6.1.44-2} The region contributes
   {#B6.1.45} O(|ξ|²) (`SmoothNum.lemma61`).
3. {#B6.1.46} *Inner ball* |k| < 2|ξ|.
   {#B6.1.46-1} From |N(k, η)| ≤ M_N(|k| + |η|)² (#B6.1.28-1), |ξ| ≤ |k| + |k+η| for η = ±ξ, and s ≥ c|·|² (#B6.1.42),
   {#B6.1.47} |G(k, η)| ≤ C(|k|^{−2} + |k+η|^{−2}) for η ∈ {ξ, −ξ, 0}. Since ∫_{|k|<r}|k|^{−2} d⁴k = 2|B₁|r², the region
   {#B6.1.48} contributes O(|ξ|²) (`SmoothNum.lemma61`).
4. {#B6.1.49} *Annulus* 2|ξ| < |k| < π/2.
   {#B6.1.49-1} Exactly,
     {#B6.1.50} G = f + F_r,  F_r = N_r/(|k|²|k+ξ|²) + N[h_s(k)/|k+ξ|² + h_s(k+ξ)/|k|² + h_s(k)h_s(k+ξ)].
   - {#B6.1.51} By step 1, F_r ∈ DC(−1), so |Δ²F_r| ≤ C|ξ|²|k|^{−3}.
     {#B6.1.51-1} Also ∫_{2|ξ|<|k|<π/2}|k|^{−3} d⁴k ≤ 2π|B₁|
     {#B6.1.52} (`SmoothNum.lemma61`).
   - {#B6.1.53} For the homogeneous part write a = |k|², u = ⟨k, ξ⟩, w = |ξ|² and N_2 = n₀ + n₁ + n₂, with n₀ quadratic in k,
     {#B6.1.54} n₁ bilinear in (k, ξ) and n₂ quadratic in ξ.
     {#B6.1.54-1} Then
       {#B6.1.55} f_2 = n₂/a² − 2n₁u/a³ − n₀w/a³ + 4n₀u²/a⁴,
     {#B6.1.56} and the exact identity
       {#B6.1.57} Δ²f − 2f_2 = 2[n₀(a²w² + aw³ − 12awu² − 4w²u² + 16u⁴) + 2n₁ua(2aw + w² − 4u²) + n₂(−a³w − a²w² + 4a²u²)]
                    {#B6.1.58} / (a⁴|k+ξ|²|k−ξ|²)
     {#B6.1.59} gives |Δ²f − 2f_2| ≤ C|ξ|⁴|k|^{−6} (`SmoothNum.lemma61`).
     {#B6.1.59-1} Its integral over the annulus is O(|ξ|²).
   - {#B6.1.60} f_2(·, ξ) is homogeneous of degree −4.
     {#B6.1.60-1} In polar coordinates,
     {#B6.1.61} ∫_{2|ξ|<|k|<π/2} f_2 = ln(π/(4|ξ|)) ∫_{S³} f_2(ω, ξ) dσ(ω), and Σ(ξ) = O(|ξ|²).

   {#B6.1.62} So the annulus contributes ½∫Δ²G d⁴k/(2π)⁴ = Σ(ξ) ln(π/(4|ξ|)) + O(|ξ|²) = Σ(ξ) ln(1/|ξ|) + O(|ξ|²), and adding the three regions in (#B6.1.12) gives I(ξ) − I(0) = Σ(ξ) ln(1/|ξ|) + O(|ξ|²).
5. {#B6.1.63} *Single-propagator integrals.* 1/s is integrable and Ñ is smooth in ξ. ∎

### 6.2 Application to the Bare Lattice Functional {#BS6.2}

{#B6.2.1} Let B_tb(U) := −½ log det(Hess A(U) + D_UD_Uᵀ) + log det(D_UᵀD_U), with D_U of #B3.1.4.
{#B6.2.1-1} This is the lattice background-field one-loop
{#B6.2.2} functional in Feynman gauge, with the Wilson action and normalised trace.
{#B6.2.2-1} It is gauge-invariant, because the
{#B6.2.3} coordinates X ↦ Ue^{iX} transform linearly under gauge transformations, so the Hessian is covariant even off-shell.
{#B6.2.4} Its polarisation symbol Ψ_tb(ξ) in the direction of a fine background b is a finite sum of:
- {#B6.2.5} bubbles Tr(GV¹GV¹), sums over k of fibre traces of products of symbols (#B6.2.22), whose numerators are of the type in Lemma 6.1;
- {#B6.2.6} tadpoles Tr(GV²) (#B6.2.24-1).

{#B6.2.6-1} tr_f is Tr (#B0.6-1) over the fibre of the symbols, (g^c)⁴ or g^c (#B6.2.8-3), not over the fields; it is unnormalised, unlike the tr of #B6.2.2.

{#B6.2.7} Here G = s(k)^{−1}·1, because at U = 1 both Hess A(U) + D_UD_Uᵀ and D_UᵀD_U are the lattice Laplacian, with symbol s(k) on each component.
{#B6.2.7-1} V¹ and V² are the first- and second-order background vertices of M̃ := H̃ + ĎĎᵀ and of the ghost operator D_UᵀD_U at U = e^{ib}, where H̃ is the Hessian of X̃ ↦ A(e^{i(b+X̃)}) at X̃ = 0 and Ď the linearised gauge action in the chart X̃ ↦ e^{i(b+X̃)};
{#B6.2.8} B_tb's own chart is reduced to this one in #B6.2.16–#B6.2.21.
{#B6.2.8-1} *Symbols.* On Λ put e_k(x) := |Λ|^{−1/2}e^{i⟨k, x⟩} on 0-forms and (e_k)_μ(x) := |Λ|^{−1/2}e^{i⟨k, x + e_μ/2⟩} on the μ-component of 1-forms, with the phase at the midpoint of the bond (x, x + e_μ), and b̂_μ(ξ) := Σ_x e^{−i⟨ξ, x + e_μ/2⟩}b_μ(x).
{#B6.2.8-2} For β ∈ (g ⊗ ℂ)⁴ let m_ξβ be the 1-form (m_ξβ)_μ(x) := |Λ|^{−1}β_μe^{i⟨ξ, x + e_μ/2⟩}, so that b = Σ_ξ m_ξb̂(ξ). Write V¹[·] for V¹ as a linear map of b and V²[·, ·] for the symmetric bilinear map with V²[b, b] = V², both extended complex-linearly.
{#B6.2.8-3} The symbols are v¹(k, ξ)[β] := |Λ|⟨e_{k+ξ}, V¹[m_ξβ]e_k⟩ and v²(k, ξ)[β′, β] := |Λ|²⟨e_k, V²[m_{−ξ}β′, m_ξβ]e_k⟩, matrices on the fibre ((g ⊗ ℂ)⁴ for 1-forms, g ⊗ ℂ for 0-forms). By translation covariance ⟨e_{k′}, V¹[m_ξβ]e_k⟩ = 0 unless k′ = k + ξ, so ⟨e_{k+ξ}, V¹e_k⟩ = |Λ|^{−1}v¹(k, ξ)[b̂(ξ)].

{#B6.2.9} **Lemma 6.2 (Naive Continuum Limit).** The symbols v¹ and v² are trigonometric polynomials in (k/2, ξ/2), and v¹(−k, −ξ) = −v¹(k, ξ).
{#B6.2.10-1} So the lowest-order Taylor part of v¹ at (0, 0) is linear in (k, ξ), and it is the symbol of the first-order part in b of
{#B6.2.11} the continuum operators −D_b²·1 − 2i ad F_b (vector) and −D_b² (ghost), with D_b := ∂ + i ad b, F_b := F(b), F(b)_μν := ∂_μb_ν − ∂_νb_μ + i[b_μ, b_ν] and (ad F X)_ν := Σ_μ[F_νμ, X_μ], in RG1's Hermitian convention for g (#B1.2).

{#B6.2.12} *Proof.* *Trigonometric polynomials.* A(e^{i(b+X̃)}) is a sum over plaquettes of functions of the four bond variables of each, and Ď and D_U map the values of a 0-form at the two ends of a bond to that bond, with coefficients analytic in b at that bond.
{#B6.2.12-1} So M̃ and D_UᵀD_U are finite sums of shifts with coefficients analytic in the values of b within distance 2, and their parts of order n = 1, 2 in b are finite sums of terms that multiply ψ(· + a₀) by a coefficient multilinear in b(· + a₁), …, b(· + a_n) and matrix-valued on the fibre.
{#B6.2.12-2} With the phases of #B6.2.8-1 at sites and bond midpoints, the symbol of each such term is its coefficient times a product of exponentials e^{i⟨k, a⟩} and e^{i⟨ξ, a′⟩} with a, a′ ∈ ½ℤ⁴.
{#B6.2.13} *Parity.* Let 𝔦 be the point inversion x ↦ −x: (𝔦U)_μ(x) := U_μ(−x − e_μ)^{−1} on configurations, (𝔦₁X)_μ(x) := −X_μ(−x − e_μ) on 1-forms and (𝔦₀ω)(x) := ω(−x) on 0-forms; 𝔦₁ and 𝔦₀ are orthogonal involutions.
{#B6.2.13-1} Write (x; μ, ν), μ < ν, for the plaquette with corners x, x + e_μ, x + e_ν, x + e_μ + e_ν. The holonomy of 𝔦U around (−x − e_μ − e_ν; μ, ν) is conjugate to that of U around (x; μ, ν), so A∘𝔦 = A; 𝔦(e^{i(b+X̃)}) = e^{i(𝔦₁b + 𝔦₁X̃)}; and 𝔦 carries the gauge transform of U by u to that of 𝔦U by 𝔦₀u.
{#B6.2.13-2} Hence H̃(𝔦₁b) = 𝔦₁H̃(b)𝔦₁, Ď(𝔦₁b) = 𝔦₁Ď(b)𝔦₀, and M̃(𝔦₁b) = 𝔦₁M̃(b)𝔦₁.
{#B6.2.13-3} In B_tb's chart 𝔦(Ue^{iX}) = (𝔦U)e^{iX′} with X′_μ(x) = −Ad(U_μ(−x − e_μ))X_μ(−x − e_μ), an isometry O_U of the 1-forms, so D_{𝔦U} = O_UD_U𝔦₀ and D_{𝔦U}ᵀD_{𝔦U} = 𝔦₀D_UᵀD_U𝔦₀.
{#B6.2.13-4} Comparing the parts of first order in b, V¹[𝔦₁b] = 𝔦₁V¹[b]𝔦₁ for M̃ and V¹[𝔦₁b] = 𝔦₀V¹[b]𝔦₀ for D_UᵀD_U. Now 𝔦₀e_k = e_{−k}, 𝔦₁e_k = −e_{−k} and (𝔦₁b)^(ξ) = −b̂(−ξ), so −v¹(k, ξ)[b̂(−ξ)] = v¹(−k, −ξ)[b̂(−ξ)] for every b, that is, v¹(−k, −ξ) = −v¹(k, ξ).
{#B6.2.14} *Linear parts.* With Ξ := b + X̃ and, for the plaquette p = (x; μ, ν), Ξ₁ := Ξ_μ(x), Ξ₂ := Ξ_ν(x + e_μ), Ξ₃ := Ξ_μ(x + e_ν) and Ξ₄ := Ξ_ν(x), U_p = e^{iΞ₁}e^{iΞ₂}e^{−iΞ₃}e^{−iΞ₄} = e^{iΞ_p}.
{#B6.2.14-1} The Baker–Campbell–Hausdorff formula gives Ξ_p = (dΞ)_p + (i/2)[Ξ, Ξ]_p + O(Ξ³), with (dΞ)_p := Ξ₁ + Ξ₂ − Ξ₃ − Ξ₄ and [Ξ, Ξ]_p := [Ξ₁, Ξ₂] − [Ξ₁, Ξ₃] − [Ξ₁, Ξ₄] − [Ξ₂, Ξ₃] − [Ξ₂, Ξ₄] + [Ξ₃, Ξ₄]; and 1 − Re tr e^{iΞ_p} = ½tr Ξ_p² + O(Ξ_p⁴), as tr Ξ_p = 0 (g = [g, g]) and tr Ξ_p³ is real.
{#B6.2.14-2} So the part of A(e^{iΞ}) of order two in X̃ and one in b is that of Σ_p(i/2)tr((dΞ)_p[Ξ, Ξ]_p).
{#B6.2.14-3} Its symbol is a sum of products of the symbol of one difference, of X̃ or of b, which vanishes at (0, 0), and the symbol of a commutator in [Ξ, Ξ]_p; the linear part keeps the linear part of the first and the value at (0, 0) of the second, that is, all four Ξ_a at one point, where [Ξ, Ξ]_p = 2[Ξ_μ, Ξ_ν].
{#B6.2.14-4} The linear part of the symbol of (dΞ)_p is that of ∂_μΞ_ν − ∂_νΞ_μ, so the linear part of the symbol of H̃'s first-order part is that of the continuum form Σ_{μ<ν}½∫tr(∂_μΞ_ν − ∂_νΞ_μ + i[Ξ_μ, Ξ_ν])² = ¼Σ_{μν}∫tr F(Ξ)_μν² at the same order.
{#B6.2.15} By the same formula, e^{iω(x)}e^{ib_μ(x)}e^{−iω(x+e_μ)} = e^{i(b_μ(x) + (Ďω)_μ(x) + O(ω²))} with (Ďω)_μ(x) = ω(x) − ω(x + e_μ) − (i/2)[b_μ(x), ω(x) + ω(x + e_μ)] + O(b²ω), whose symbol has linear part that of −D_bω; with D_U = TĎ and TᵀT = 1 + O(b²) (#B6.2.16-1, #B6.2.17), the first-order parts of ĎĎᵀ and D_UᵀD_U have the linear parts of those of D_bD_bᵀ and D_bᵀD_b = −D_b².
{#B6.2.15-1} The continuum Hessian of ¼Σ_{μν}∫tr F(b + X)_μν² + ½∫tr(D_bᵀX)² is −D_b²·1 − 2i ad F_b (#B6.2.38-1–#B6.2.39). ∎

{#B6.2.16} *The chart of B_tb.* B_tb at U = e^{ib} uses the chart X ↦ e^{ib}e^{iX}. Define X = φ(X̃) bondwise by e^{ib}e^{iφ(X̃)} = e^{i(b+X̃)}; the Baker–Campbell–Hausdorff formula gives φ(X̃) = X̃ − (i/2)[b, X̃] + O(b²X̃, bX̃²), so T := Dφ(0) = 1 − (i/2) ad b + O(b²), with ad b acting on the μ-component of a 1-form as ad b_μ.
{#B6.2.16-1} Since i ad b is antisymmetric for tr, Tᵀ = 1 + (i/2) ad b + O(b²), and TᵀT = 1 + O(b²).
- {#B6.2.17} With Ã(X̃) := A(e^{i(b+X̃)}), Hess A = T^{−ᵀ}H̃T^{−1} + Gr, Gr := ⟨∇Ã(0), D²φ^{−1}(0)⟩; ∇Ã(0) and D²φ^{−1}(0) are O(b), so Gr is O(b²) and contains no differences of X. Both charts parametrise the same gauge orbit through U, so D_U = TĎ.
  {#B6.2.18} Hence Hess A + D_UD_Uᵀ = T^{−ᵀ}(M̃ + E)T^{−1} with E := TᵀTĎĎᵀTᵀT − ĎĎᵀ + TᵀGrT = O(b²), and −½ log det(Hess A + D_UD_Uᵀ) = −½ log det(M̃ + E) + log det T.
- {#B6.2.19} log det T is the sum over the bonds of log det of the factor of T at that bond, a linear map on g^c analytic in the value of b at that bond alone; its first-order part, −(i/2)Tr(ad b) summed over the bonds, is 0, as Tr ad X = 0 on g^c (i ad X is antisymmetric for tr when X ∈ g, #B6.2.16-1, and X ↦ Tr ad X is complex-linear), and its second-order part has a symbol independent of ξ, so it carries no logarithm.
- {#B6.2.20} As M̃^{−1} = G + O(b), E enters the second-order term once, as Tr(GE₂) with E₂ the second-order part of E: a tadpole, whose symbol (as v² in #B6.2.8-3) is a trigonometric polynomial in (k/2, ξ/2), E being built from bond-local factors and the finite differences in Ď and Gr (#B6.2.12-1).

{#B6.2.21} So the second-order term of B_tb is that of −½ log det(M̃ + E) + log det(D_UᵀD_U) up to a term without logarithm, and its bubbles are built from the first-order vertices of M̃ and D_UᵀD_U.

{#B6.2.22} By #B6.2.8-3, Tr(GV¹GV¹) = |Λ|^{−2}Σ_{k,ξ} s(k)^{−1}s(k + ξ)^{−1} tr_f[v¹(k + ξ, −ξ)[b̂(−ξ)] v¹(k, ξ)[b̂(ξ)]].
{#B6.2.22-1} Hence each bubble numerator N(k, ξ), the bilinear form (β′, β) ↦ tr_f[v¹(k + ξ, −ξ)[β′] v¹(k, ξ)[β]] written as a matrix, satisfies the hypotheses of Lemma 6.1: it is a trigonometric
{#B6.2.23} polynomial in (k/2, ξ/2), even, because v¹ is odd (Lemma 6.2), and zero at 0.
{#B6.2.23-1} Its N_2 is the product of the linear parts of the two vertices, which is the numerator
{#B6.2.24} of the continuum Feynman-gauge background-field bubble.
{#B6.2.24-1} The tadpoles Tr(GV²) = |Λ|^{−2}Σ_{k,ξ} s(k)^{−1} tr_f v²(k, ξ)[b̂(−ξ), b̂(ξ)] have one propagator and, by Lemma 6.2, a numerator that is a trigonometric polynomial in (k/2, ξ/2), so by the last part of
{#B6.2.25} Lemma 6.1 they are C^∞ in ξ and carry no logarithm.
{#B6.2.25-1} The logarithm in Ψ_tb is therefore fixed by the continuum vertices.

{#B6.2.26} **Lemma 6.5 (Angular Coefficient).** Fix a background mode b̂_μ(ξ) ∈ g ⊗ ℂ.
{#B6.2.26-1} Put ⟨X, Y⟩ := tr(XY), which is positive
{#B6.2.27} definite on g in RG1's Hermitian convention (#B1.2), and B_μν(ξ) := ⟨conj b̂_μ(ξ), b̂_ν(ξ)⟩, conj being the conjugation of g ⊗ ℂ.
{#B6.2.27-1} The second-order term of B_tb in this mode has logarithmic part

  {#B6.2.28} c ln(1/|ξ|²) · ½(|ξ|²δ_μν − ξ_μξ_ν) B_μν(ξ),  **c = (11/48π²) κ,**

{#B6.2.29} up to the factor |Λ|^{−1} common to all modes.
{#B6.2.29-1} The same mode of the quadratic part of the Wilson action A is
{#B6.2.30} ½(|ξ|²δ − ξξ)B up to O(|ξ|³)Σ_μB_μμ.
{#B6.2.30-1} Hence the logarithmic part of Ψ_tb (#B5.3), the sum over its bubbles of the parts Σ(ξ) ln(1/|ξ|) of Lemma 6.1, is c ln(1/|ξ|²)(|ξ|²δ − ξξ), c ln(1/|ξ|²) times the leading part of the polarisation symbol of A, and c > 0.

{#B6.2.31} *Proof.* By Lemma 1.1, Tr(ad X ad Y) = K(X, Y) = κ⟨X, Y⟩ on g, extended bilinearly to g ⊗ ℂ.
{#B6.2.31-1} Since b is real,
{#B6.2.32} b̂(−ξ) = conj b̂(ξ).
1. {#B6.2.33} *Expansion.* If Δ = Δ⁰ + V¹ + V² + O(b³) and G = (Δ⁰)^{−1}, then
   {#B6.2.34} log det Δ = log det Δ⁰ + Tr GV¹ + Tr GV² − ½Tr(GV¹GV¹) + O(b³).
   {#B6.2.35} Tr GV² is a tadpole.
   {#B6.2.35-1} So the logarithmic part of the second-order term of B_tb = −½ log det Δ_v + log det T + log det Δ_gh (#B6.2.18), with the vector and ghost operators Δ_v := M̃ + E and Δ_gh := D_UᵀD_U at U = e^{ib}, V_v¹, V_gh¹ their first-order vertices, and log det T without logarithm (#B6.2.19), is that of
   {#B6.2.36} ¼Tr(GV_v¹GV_v¹) − ½Tr(GV_gh¹GV_gh¹).
2. {#B6.2.37} *Continuum vertices.* For the field b + X, the part of ¼∫|F_μν|² quadratic in X, plus the Feynman term ½∫|D_μX_μ|², is
   {#B6.2.38} ½⟨X, (−D² − 2i ad F)X⟩ with D := D_b and F := F_b (#B6.2.11), and by Lemma 6.2 this operator is the lowest-order part of Δ_v.
   {#B6.2.38-1} This follows by integration by parts from
   {#B6.2.39} [D_μ, D_ν] = i ad F_μν and ⟨F, [X_μ, X_ν]⟩ = ⟨[F, X_μ], X_ν⟩, with F(b + X)_μν − F(b)_μν = D_μX_ν − D_νX_μ + i[X_μ, X_ν].
   {#B6.2.39-1} The lowest-order part of Δ_gh is −D² (#B6.2.15).
   {#B6.2.39-2} The parts linear in b
   {#B6.2.40} have matrix elements, with ξ = k′ − k and b̂ = b̂(ξ):
   - {#B6.2.41} convective, (k + k′)_μ ad b̂_μ/|Λ|, on each of the four components for Δ_v;
   - {#B6.2.42} magnetic (Δ_v only), W_νμ = 2 ad(ξ_νb̂_μ − ξ_μb̂_ν)/|Λ|, since F̂_νμ = i(ξ_νb̂_μ − ξ_μb̂_ν) at first order.
3. {#B6.2.43} *Traces.* Put k′ = k + ξ.
   {#B6.2.43-1} Each trace below is κ|Λ|^{−1}Σ_ξ times a lattice bubble ∫N/(s(k)s(k+ξ)) d⁴k/(2π)⁴, whose
   {#B6.2.44} N_2 is the continuum numerator listed.
   - {#B6.2.45} Ghost: N_2 = (2k+ξ)_μ(2k+ξ)_ν B_μν.
     {#B6.2.45-1} The sign: the vertex factors are real, and K(b̂_μ(−ξ), b̂_ν(ξ)) = κB_μν.
   - {#B6.2.46} Vector, convective: four times the ghost trace (four components).
   - {#B6.2.47} Vector, mixed: zero, since the vector-index trace of W is Σ_ν W_νν = 0.
   - {#B6.2.48} Vector, magnetic: N_2 = 4Σ_μν|ξ_μb̂_ν − ξ_νb̂_μ|² = 8(|ξ|²δ − ξξ)_μν B_μν.
4. {#B6.2.49} *Angular averages.* By Lemma 6.1 each bubble has logarithmic part Σ(ξ) ln(1/|ξ|) = (1/16π²)⟨f_2(·, ξ)⟩ ln(1/|ξ|²),
   {#B6.2.50} where ⟨·⟩ is the average over S³ and (2π)^{−4}|S³| = 1/8π².
   {#B6.2.50-1} The moments are ⟨ω_μω_ν⟩ = δ_μν/4 and
   {#B6.2.51} ⟨ω_μω_νω_ρω_σ⟩ = (δ_μνδ_ρσ + δ_μρδ_νσ + δ_μσδ_νρ)/24:
   - {#B6.2.52} permutations and sign changes of the coordinates leave only ⟨ω_1²⟩, ⟨ω_1⁴⟩ and ⟨ω_1²ω_2²⟩;
   - {#B6.2.53} Σ_μ ω_μ² = 1 gives ⟨ω_1²⟩ = 1/4, and Σ_μν ω_μ²ω_ν² = 1 gives 4⟨ω_1⁴⟩ + 12⟨ω_1²ω_2²⟩ = 1;
   - {#B6.2.54} rotation by π/4 in the (1, 2)-plane gives ⟨ω_1⁴⟩ = 3⟨ω_1²ω_2²⟩.

   {#B6.2.55} With u = ⟨ω, ξ⟩ and w = |ξ|², as in Lemma 6.1's step 4 at |k| = 1:
   - {#B6.2.56} convective: f_2 = ξ_μξ_ν − 4u(ω_μξ_ν + ξ_μω_ν) − 4wω_μω_ν + 16u²ω_μω_ν, so
     {#B6.2.57} ⟨f_2⟩ = ξξ − 2ξξ − wδ + ⅔(wδ + 2ξξ) = −⅓(|ξ|²δ − ξξ);
   - {#B6.2.58} magnetic: N_2 is already quadratic in ξ, so f_2 = N_2/|ω|⁴ and ⟨f_2⟩ = 8(|ξ|²δ − ξξ)B.
5. {#B6.2.59} *Sum.* In units of κ|Λ|^{−1}(1/16π²) ln(1/|ξ|²)(|ξ|²δ − ξξ)B, the logarithmic part is
   {#B6.2.60} ¼[4·(−⅓) + 8] − ½·(−⅓) = 5/3 + 1/6 = 11/6.
   {#B6.2.60-1} This is (11κ/96π²) ln(1/|ξ|²)(|ξ|²δ − ξξ)B, which is
   {#B6.2.61} c ln(1/|ξ|²)·½(|ξ|²δ − ξξ)B. ∎

{#B6.2.62} The type-checked Lean core `BalabanFormal.angular_coefficient` covers steps 4–5: the invariance of the S³ integral under
{#B6.2.63} isometries, the moments, both averages and the constant 11/(48π²).

{#B6.2.64} So the k-step rate 2c ln L per step is (11/24π²)κ ln L, the universal one-loop running.
- {#B6.2.65} *Sign.* c > 0 is asymptotic freedom; it matches RG1 (0.20), because log Z ≈ +b·A.
- {#B6.2.66} *Affine part.* In the conventions of #B6.2.8-1, Ψ_tb(ξ)v̌(ξ) = 0 with v̌_μ(ξ) := 2i sin(ξ_μ/2), the symbol of the gradient: the first-order term of B_tb(e^{ib}) is an Ad-invariant linear form in b̂(0), so 0 as g is simple, and the part of order one in b and one in ω of B_tb(u·e^{ib}) = B_tb(e^{ib}), u = e^{iω} (#B6.2.2-1), is then −⟨b, Ψ_tb ∂₁ω⟩ = 0, as Ďω = −∂₁ω + O(bω) (#B6.2.15), with (∂₁ω)_μ(x) = ω(x + e_μ) − ω(x) the unit-lattice gradient (#B5.6); and Ψ_tb(Rξ) = RΨ_tb(ξ)R^{−1} for every signed permutation R, which maps bond midpoints to bond midpoints, so that ρ(R, ξ) = R.
  {#B6.2.66-1} Steps 1–4 of the proof of Lemma 4.1(a) use v only through v(0) = 0 and ∂_μv(0) = ie_μ, which v̌ has. Applied to the
  {#B6.2.67} affine part a_0 + a_1ξ of Ψ_tb (the logarithmic part c ln(1/|ξ|²)(|ξ|²δ − ξξ) is covariant and annihilates v̌ up to O(|ξ|⁵ ln), and the rest is O(|ξ|²)), they force a_0 = 0 and
  {#B6.2.68} a_1 = 0.

{#B6.2.69} **Proposition 6.3 (Bare Polarisation).** Let F_0 be §3's level-0 functional (#B3.1.25), built from h = Π_⊥ Hess A Π_⊥ (#B3.3.5).
{#B6.2.70} The polarisation symbol of −F_0 is Ψ_0 = d̂*Ψ̃_0 d̂, with d̂ the symbol of the lattice curl on 1-forms, (d̂X)_μν = v̌_μX_ν − v̌_νX_μ in the conventions of #B6.2.8-1 and #B6.2.66, with the phase of a 2-form plane wave at the plaquette centre x + (e_μ + e_ν)/2, and Ψ̃_0 acting on ran d̂.
{#B6.2.70-1} Let c = (11/48π²)κ
{#B6.2.71} (Lemma 6.5).
{#B6.2.71-1} Then

  {#B6.2.72} Ψ̃_0(ξ) = c ln(1/|ξ|²)·1 + R_0(ξ),  sup_{ξ ∈ T⁴∖0} ‖R_0(ξ)‖ < ∞.

{#B6.2.73} *Proof.*
{#B6.2.74} Write H := Hess A(U), D := D_U, Π_D := D(DᵀD)^{−1}Dᵀ, Π := 1 − Π_D (the Π_⊥ of #B3.3.5), h_⊥ for h on (ran D)^⊥, S := (DᵀD)^{−2}, and
{#B6.2.75} J := ∇A(U).
{#B6.2.75-1} Differentiating ⟨∇A(U), D_Uω⟩ ≡ 0 along U ↦ Ue^{iX} gives HD = 𝒩_U(J).
{#B6.2.75-2} Here 𝒩_U(j) is linear in j, local,
{#B6.2.76} contains no lattice difference, depends on U only through the bond transports, and is gauge-covariant; in PBG's
{#B6.2.77} coordinates it is the T of §7.
{#B6.2.77-1} All operators are restricted to a coset 𝒪 ≠ ℤξ (Remark 3.4).
{#B6.2.77-2} The loop momentum k is that
{#B6.2.78} of the 0-form line, a := |k|, and a′ := |k + ξ|, both taken mod 2π.
{#B6.2.78-1} At U = e^{ib}, a subscript ₙ on H, h, J, D, S, 𝒩, 𝒲 or a bracket marks its part of order n in b, so H₀ and h₀ are their values at U = 1; factors |b̂| are not written.

1. {#B6.2.79} *One log-determinant.* −F_0 − B_tb = −½[log det(h + DDᵀ) − log det(H + DDᵀ)].
   - {#B6.2.80} In (ran D)^⊥ ⊕ ran D, h + DDᵀ = h_⊥ ⊕ DDᵀ, and H + DDᵀ has the diagonal blocks h_⊥ and Π_DHΠ_D + DDᵀ.
     {#B6.2.80-1} The Schur
     {#B6.2.81} complement of h_⊥ is DDᵀ + Π_DH_SΠ_D, with H_S := H − HΠh_⊥^{−1}ΠH.
   - {#B6.2.82} On ran D, (DDᵀ)^{−1} = DSDᵀ.
     {#B6.2.82-1} By Sylvester's identity det(1 + AB) = det(1 + BA),

       {#B6.2.83} −F_0 − B_tb = ½ log det_Y(1 + S𝒲),  𝒲 := DᵀH_SD = Dᵀ𝒩_U(J) − 𝒩_U(J)ᵀΠh_⊥^{−1}Π𝒩_U(J).

     {#B6.2.84} The second form follows from HD = 𝒩_U(J).
     {#B6.2.84-1} The two forms are one expression, so they have the same integrand.
2. {#B6.2.85} *The integrand.* 𝒲₀ = 0, so the second-order term is ½Tr(S𝒲₂) + ½Tr(S₁𝒲₁) − ¼Tr(S𝒲₁S𝒲₁), with integrand I(k, ξ), the fibre trace tr_f of its symbol (#B6.2.6-1).
   - {#B6.2.86} *Schur form.* H_S vanishes at U = 1, since H₀ = ΠH₀Π.
     {#B6.2.86-1} Its first-order part is Π_DH₁Π_D: the projection
     {#B6.2.87} derivatives drop out because Π(Π)₁Π = 0 and H₀(Π)₁Π = 0, and the derivative of h_⊥^{−1} gives +ΠH₁Π.
     {#B6.2.87-1} Hence
     {#B6.2.88} 𝒲₁ = D₀ᵀH₁D₀ and 𝒲₂ = D₀ᵀ(H₂ − H₁Πh_⊥^{−1}ΠH₁)D₀ + D₁ᵀΠ_DH₁Π_DD₀ + D₀ᵀΠ_DH₁Π_DD₁, since H₀D₀ = 0.
   - {#B6.2.89} *Symbol bounds.* |D₀| ≤ a, s ≥ (4/π²)a², and h₀ = s on coclosed 1-forms.
     {#B6.2.89-1} D₁ contains no difference, |H₂| ≤ C,
     {#B6.2.90} and |(DᵀD)₁| ≤ C(a + a′).
     {#B6.2.90-1} H₁ is a trigonometric polynomial that vanishes at zero momenta, since A is quartic in
     {#B6.2.91} constant fields, so |H₁| ≤ C(a + a′).
   - {#B6.2.92} *Degrees.* The five terms are bounded by Ca^{−2}, C(a + a′)²a^{−2}a′^{−2}, C(a + a′)a^{−3},
     {#B6.2.93} C(a + a′)²(a^{−1}a′^{−3} + a^{−3}a′^{−1}), and C(a + a′)²a^{−2}a′^{−2}.
     {#B6.2.93-1} The degree is at most 3 at k = 0 and at k = −ξ.
     {#B6.2.93-2} So, as in Remark 3.4 (grid
     {#B6.2.94} points within r of a singular point now contribute at most Cr), Ψ_0 − Ψ_tb = ∫_{T⁴} I(k, ξ) d⁴k/(2π)⁴.
   - {#B6.2.95} *J-form.* With J₀ = 0, I is the integrand of ½Tr(SD₀ᵀ𝒩₀(J₂)) plus I_lin + I_quad, where
     - {#B6.2.96} I_lin := θ₁(k, ξ)[b̂, Ĵ₁], θ₁ being the first-order part in b at fixed j of the integrand of ½Tr(SD_Uᵀ𝒩_U(j));
     - {#B6.2.97} I_quad is the integrand of −½Tr(S𝒩₀(J₁)ᵀΠh_⊥^{−1}Π𝒩₀(J₁)) − ¼Tr(SD₀ᵀ𝒩₀(J₁)SD₀ᵀ𝒩₀(J₁)).

     {#B6.2.98} Only the zero-momentum part of J₂ reaches the trace.
     {#B6.2.98-1} For constant j, 𝒩₀(j) = Σ_ν A_ν(j) ⊗ n_ν(k), with A_ν(j) a
     {#B6.2.99} multiple of ad j_ν, and every other factor is scalar on g.
     {#B6.2.99-1} On the fibre (g^c)⁴ = g^c ⊗ ℂ⁴, or g^c (#B6.2.8-3), the fibre trace of A ⊗ P, with A a linear map on g^c and P a matrix on ℂ⁴, or a number, is Tr A times the trace of P, and Tr ad = 0 (#B6.2.19), so the J₂ term vanishes for every k.
     {#B6.2.100} J₁ = H₀b has symbol O(|ξ|²), so |Ĵ₁| ≤ C|ξ|² and |𝒩₀(J₁)| ≤ C|ξ|².
3. {#B6.2.101} *Size of the difference.* Let |ξ| ≤ ξ₀, with ξ₀ small.
   - {#B6.2.102} *Inner region |k| < 2|ξ|.* Here a + a′ ≤ 5|ξ|, and the bounds of the Schur form apply. ∫a^{−2} ≤ C|ξ|² and
     {#B6.2.103} |ξ|∫a^{−3} ≤ C|ξ|². For p, q ≤ 3 with p + q = 4, the substitution k = |ξ|ℓ gives
     {#B6.2.104} |ξ|²∫a^{−p}a′^{−q} = |ξ|²∫_{|ℓ|<2}|ℓ|^{−p}|ℓ + ξ/|ξ||^{−q} d⁴ℓ, which is C|ξ|² with C independent of the direction.
   - {#B6.2.105} *Outer region, quadratic part.* Here a′ ≥ a/2, so |I_quad| ≤ C|ξ|⁴a^{−6}, whose integral is at most C|ξ|².
   - {#B6.2.106} *Outer region, linear part.* |θ₁(k, tξ)| ≤ Ca^{−4} and |∂_ξθ₁(k, tξ)| ≤ Ca^{−5} for t ∈ [0, 1].
     {#B6.2.106-1} The three pieces
     {#B6.2.107} S D₁ᵀ𝒩₀, S D₀ᵀ𝒩₁, and S₁D₀ᵀ𝒩₀ are bounded by Ca^{−4}, Ca^{−3}, and C(a + a′)a^{−6}a′, and a derivative in ξ costs
     {#B6.2.108} at most one factor a^{−1}.
     {#B6.2.108-1} So θ₁(k, ξ) − θ₁(k, 0) contributes at most C|ξ|³∫_{a≥2|ξ|}a^{−5} ≤ C|ξ|².
   - {#B6.2.109} *The constant-background integrand.* θ₁(k, 0)[β, j] is the integrand for constant β and constant j.
     {#B6.2.109-1} To first order
     {#B6.2.110} in β, U_β := (e^{iβ_μ}) is the gauge transform of 1 by g(x) := e^{−iβ·x} on ℤ⁴.
     {#B6.2.110-1} By covariance,
     {#B6.2.111} D_{U_β} = gD₀g^{−1} and 𝒩_{U_β}(j) = g𝒩₀(Ad(g)^{−1}j)g^{−1}.
     {#B6.2.111-1} Conjugation by g and the x-dependence of Ad(g)^{−1}j
     {#B6.2.112} enter through commutators with the coordinates x_μ, and [x_μ, P] has symbol i∂_{k_μ}P for translation-invariant
     {#B6.2.113} P. The terms multiplied by x_μ cancel, since U_β is translation invariant.
     - {#B6.2.114} What remains is a sum of two kinds of term.
       {#B6.2.114-1} In the first, one factor P of the U = 1 product is replaced by a
       {#B6.2.115} fixed multiple of ad β_μ ∂_{k_μ}P.
       {#B6.2.115-1} In the second, the only factor that is not scalar on g is ad[β_μ, j].
     - {#B6.2.116} After tr_f the second kind vanish, by the factorisation of #B6.2.99-1.
       {#B6.2.116-1} By Leibniz, the first give θ₁(k, 0)[β, j] = Σ_{μν} C_{μν}∂_{k_μ}Φ_ν(k),
       {#B6.2.117} with C_{μν} a fixed multiple of Tr(ad β_μ A_ν(j)) and Φ_ν(k) := tr_f[S(k)D₀(k)*n_ν(k)].
     - {#B6.2.118} Φ_ν is smooth on T⁴∖0, and |Φ_ν| ≤ Ca^{−3}.
       {#B6.2.118-1} The faces of [−π, π]⁴ cancel by periodicity, so
       {#B6.2.119} |∫_{a≥2|ξ|}∂_{k_μ}Φ_ν| = |∫_{a=2|ξ|}Φ_ν ω_μ dσ| ≤ C. With |Ĵ₁| ≤ C|ξ|², this part is O(|ξ|²).

   {#B6.2.120} So Ψ_0 − Ψ_tb = O(|ξ|²) for |ξ| ≤ ξ₀.
   {#B6.2.120-1} For |ξ| ≥ ξ₀ the singularities of I(·, ξ) have degree at most 3, locally
   {#B6.2.121} uniformly in ξ, so Ψ_0 − Ψ_tb is continuous and bounded there.
4. {#B6.2.122} *Transversality.* On each 𝒪 ≠ ℤξ, F_0 is invariant under the gauge transformations that commute with T_ξ, since
   {#B6.2.123} these preserve the cosets and every operator of F_0 is gauge-covariant.
   {#B6.2.123-1} Its first-order coefficient at U = 1 vanishes
   {#B6.2.124} on T_ξ-invariant backgrounds: a mode of momentum ξ′ ∈ ℤξ, ξ′ ≢ 0, couples different fibres and has zero trace, and a
   {#B6.2.125} constant mode gives an Ad-invariant element of g, which is 0 since g is simple.
   {#B6.2.125-1} Differentiating
   {#B6.2.126} ⟨∇F_0(U), D_Uλ⟩ ≡ 0 at U = 1 therefore gives Ψ_0(ξ)v̌(ξ) = 0 for the gradient symbol v̌ of #B6.2.66, on each coset and hence
   {#B6.2.127} in the limit.
   {#B6.2.127-1} Ψ_0(ξ) is Hermitian, so it acts on the 1-forms orthogonal to v̌(ξ), on which d̂ is injective for ξ ≢ 0, as d̂*d̂ = |v̌|²·1 there; so Ψ_0 = d̂*Ψ̃_0d̂.
5. {#B6.2.128} *Conclusion.* By §6.2, Ψ_tb(ξ) = c ln(1/|ξ|²)(|ξ|²δ − ξξ) + O(|ξ|²) near 0.
   {#B6.2.128-1} Also d̂*d̂(ξ) = |v̌|²δ − conj(v̌)v̌ᵀ = |ξ|²δ − ξξ + O(|ξ|⁴), and c ln(1/|ξ|²)·O(|ξ|⁴) = O(|ξ|²), so d̂*R_0d̂ = Ψ_0 − c ln(1/|ξ|²)d̂*d̂ = O(|ξ|²) by step 3 and #B6.2.128;
   {#B6.2.129} and on the 1-forms orthogonal to v̌, d̂*d̂ = |v̌|² ≥ (4/π²)|ξ|², since 4 sin²(ξ_μ/2) is at least 4ξ_μ²/π²
   {#B6.2.130} for |ξ_μ| up to π. As R_0 is Hermitian, ‖R_0(ξ)‖ ≤ C near 0.
   {#B6.2.130-1} Away from 0, Ψ_0 is continuous and bounded. ∎

### 6.3 The Bare Functional Seen from the Top {#BS6.3}

{#B6.3.1} **Proposition 6.4.** For fixed p₀ ≠ 0 (top units), Π_{−F_0}^{top}(p₀) = c ln(1/η_k²) Δ_k(p₀) + O_{p₀}(1), uniformly
{#B6.3.2} in k, where η_k = L^{−k}.
{#B6.3.2-1} The type-checked Lean core of the summation is `BalabanFormal.bare_assembly`.

{#B6.3.3} *Proof.*
1. {#B6.3.4} *Composition.* The top polarisation is ⟨H_kB, Ψ_0 H_kB⟩ = Σ_l ⟨(d_ηH_kB)^∧(q), Ψ̃_0(η_k q)(d_ηH_kB)^∧(q)⟩, summed over
   {#B6.3.5} the aliases q = p₀ + l (top units).
   {#B6.3.5-1} Here (d_ηH_kB)^∧ has PRT1's corner phases (#B5.31-1), and Ψ̃_0 is read in them: passing from the centre phases of #B6.2.70 conjugates Ψ̃_0 by a diagonal unitary, which keeps c ln(1/|ξ|²)·1 and ‖R_0‖.
2. {#B6.3.6} *Insert Proposition 6.3.* This gives c ln(1/η_k²)Σ_l|(d_ηH_kB)^∧(q)|² + cΣ_l ln(1/|q|²)|(d_ηH_kB)^∧(q)|² + R-terms.
3. {#B6.3.7} *First term.* Σ_l |(d_ηH_kB)^∧(q)|² = ‖d_ηH_kB‖² = ⟨B, Δ_k B⟩ by PRT1 (1.65).
4. {#B6.3.8} *Second term.* For l ≠ 0, |q| ≥ π.
   {#B6.3.8-1} Hence, for every l, |ln(1/|q|²)| ≤ |ln(1/|p₀|²)| + α^{−1}|q|^{2α}, with Lemma 5.2's α (ln t < t at t = |q|^{2α}), and the term is at most
   {#B6.3.9} C(p₀)(Σ_l|q|^α|(d_ηH_k)^∧(q)|)²|B̂|², which is O_{p₀}(1)|B̂|² by Lemma 5.2.
5. {#B6.3.10} *R-terms.* They are at most sup‖R_0‖·‖d_ηH_kB‖², which is bounded by PRT1 (1.67). ∎

## 7. The Top-Level Part Is Bounded at a Fixed Momentum {#BS7}

{#B7.1} **Proposition 7.1.** For fixed p₀ ≠ 0, sup_k ‖Π_{F_k}(p₀)‖ < ∞.

{#B7.2} **Setting.** The background is U = U_k(e^{iB}), B ∈ 𝔅_r (§5), in top units, and V = e^{iB}.
{#B7.2-1} The loop momentum is p, a
{#B7.3} coarse momentum with |p_μ| ≤ π; q = p + l are its aliases, and |p̂| := |∂¹(p)|, with ∂¹_μ(p) = e^{ip_μ} − 1 (the v(p) of §4, not Lemma 5.2's v_μ(q)), so
{#B7.4} (2/π)|p| ≤ |p̂| ≤ |p|.
- {#B7.5} *PBG's objects.* We use PBG's coordinates e^{iηA}U; passing from §3's U e^{iX} is the bondwise linear map
  {#B7.6} X = η Ad(U)^{−1}A, which carries Hessians to Hessians.
  {#B7.6-1} On the chain all PBG domains Ω_j are the whole torus, so only
  {#B7.7} level k occurs, and L^kη = 1.
  {#B7.7-1} Then 𝐇 := Hess A(U) is PBG's Δ (3.10), J := ∇A(U) is PBG's J (3.11), and h = Π_⊥𝐇Π_⊥
  {#B7.8} (§3.3).
  {#B7.8-1} D = D_U.
  {#B7.8-2} N(Q′), R (the orthogonal projection onto Δ_U^ηN(Q′), Δ_U^η PBG's covariant Laplacian (3.23), not 𝐇), and G′ are #T11.20's, as in PBG
  {#B7.9} (3.21)–(3.24) and p.394 l.43, with Q and Q′ as follows; with an argument or a bond index, R(U)X := UXU^{−1} and R_b := R(U_b) are PBG's adjoint action (p.390 l.25), and R_yU′ and R̄_c are PBG's transported configuration and transport of p.418 l.6–13, as printed.
- {#B7.10} *The average.* Write Q̃ for §3.1's Q, the linearised k-fold average of the chain (RG1 (0.4) or (0.12)), with
  {#B7.11} Q̃D = D̄P.
  {#B7.11-1} PBG works with a dressed average instead (PBG p.392 l.45–46: CMP98 (89)–(92)), and §7 does the same for the
  {#B7.12} chain.
  {#B7.12-1} Q := Q(U) is the linear part of PBG's one-step average Ū̄′_c (p.418 l.5–7, with the dressing factors (3.113)), with Ū the chain's average and the contour
  {#B7.13} variables U(y, x) of RG1 (0.11) in place of U(Γ_{y,x}), composed over the k steps as in PBG (3.15).
  {#B7.13-1} Q′ is PBG (3.19)
  {#B7.14} with the same replacement: Q′λ(y) = Σ_{x∈B(y)}L^{−d}R(U(y, x))λ(x), composed over the k steps. Q^{(j)}, Q̃^{(j)} and Q′^{(j)} are the step-j factors of Q, Q̃ and Q′, and Q_{≤j} := Q^{(j)}Q_{≤j−1}, Q̃_{≤j} := Q̃^{(j)}Q̃_{≤j−1}, with Q_{≤0} = Q̃_{≤0} = 1, so Q = Q_{≤k} and Q̃ = Q̃_{≤k}.
  - {#B7.15} *QD = D̄Q′.* PBG's derivation (3.113)–(3.115), p.418, uses only the point covariance of Ū (§3.1) and the
    {#B7.16} covariance U(y, x) ↦ u(y)U(y, x)u(x)^{−1} of the contour variables (RG1 (0.6) for (0.11)).
  - {#B7.17} *Q − Q̃ ∈ ran D̄.* The dressing factors ρ_{c₋}(U′)^{−1} and ρ_{c₊}(U′) of PBG p.418 l.6, with ρ_y(U′) := exp[iΣ_{x∈B(y)}L^{−d}(1/i)log(R_yU′)(y, x)] the average (3.113) (l.9–11) of the transported configuration R_yU′ (printed with an overline over R_yU′, and with Γ_{y,x} where the chain has the contour variable (y, x), #B7.12-1), equal 1 at U′ = 1.
    {#B7.17-1} So the
    {#B7.18} one-step linear part is Q̃^{(1)}A + D̄ω_d(A), with ω_d(A)(y) the linear part of (1/i)log ρ_y(U′).
    {#B7.18-1} Over the steps,
    {#B7.19} Q_{≤j} − Q̃_{≤j} = Q^{(j)}(Q_{≤j−1} − Q̃_{≤j−1}) + (Q^{(j)} − Q̃^{(j)})Q̃_{≤j−1}, and Q^{(j)}D̄ = D̄Q′^{(j)}, so the difference
    {#B7.20} stays in ran D̄ at every level.
    {#B7.20-1} Hence {QA ∈ z + ran D̄} = {Q̃A ∈ z + ran D̄}, and §3's Δ_k and F_k are the same
    {#B7.21} for Q and Q̃.
  - {#B7.22} *At U = 1, Q = Q_k,* the composite of the straight one-step averages (PRT1 (1.16)–(1.18)), with centred blocks.
    {#B7.23} Indeed, at U = 1 let A(Γ) and A(y, x) be the linear parts in A of (1/i)log U′(Γ) and (1/i)log U′(y, x); by RG1
    {#B7.24} (0.8), A(y, x) is the mean of A(Γ) over Γ ∈ 𝐆(y, x).
    {#B7.24-1} Then ω_d(A)(y) = Σ_{x∈B(y)}L^{−d}A(y, x), since R_y is the
    {#B7.25} identity at U = 1.
    {#B7.25-1} The contour factors contribute +ω_d(A)(c₋) − ω_d(A)(c₊) to Q̃^{(1)}A(c): in (0.4) directly, and
    {#B7.26} in (0.12) because A(x′, c₊) = −A(c₊, x′) (#B4.187-b).
    {#B7.26-1} The
    {#B7.27} dressing contributes −ω_d(A)(c₋) + ω_d(A)(c₊).
    {#B7.27-1} Also Q′(1) is the centred block average Q′_k (PRT1 (1.20)).
  - {#B7.28} So at U = 1, G, G′, R, H, C_G, and (QGQ*)^{−1} below are PBG's own operators at U = 1, conjugated by the fixed fine
    {#B7.29} translation from CMP98's corner blocks (CMP98 (2)) to RG1's centred ones: PBG's average also has Q(1) = Q_k
    {#B7.30} (CMP98 (124)) and the block average as Q′(1) (PBG (3.19)).
    {#B7.30-1} PBG's bounds at U = 1 apply without #B9.38.
- {#B7.31} *The defect of the Hessian.* 𝒩 := 𝐇D.
  {#B7.31-1} Comparing first-order terms in λ in PBG (3.117) gives
  {#B7.32} ⟨A, 𝒩λ⟩ = ½⟨i[λ(b₋), A(b)] − i[A(b), R_bλ(b₊)], J⟩ =: T(J, λ, A).
  {#B7.32-1} This is linear in J, local, and contains no
  {#B7.33} derivative: |T(J, λ, A)| ≤ c_𝒩 Σ_b η⁴|J(b)||A(b)|(|λ(b₋)| + |λ(b₊)|), with c_𝒩 absolute.
  {#B7.33-1} For Bloch waves the sum runs over a cell, of volume 1, in which each site is an end of 2d bonds, so Cauchy–Schwarz gives Σ_bη⁴|A(b)| ≤ √d‖A‖_2 and Σ_bη⁴(|λ(b₋)| + |λ(b₊)|) ≤ 2d‖λ‖_2; hence |T(J, λ, A)| ≤ 2dc_𝒩‖J‖_∞ min(‖λ‖_∞‖A‖_2, ‖A‖_∞‖λ‖_2).
- {#B7.34} *K.* K := 𝐇 − h = Π_D𝐇 + 𝐇Π_D − Π_D𝐇Π_D, with Π_D := D(DᵀD)^{−1}Dᵀ.
  {#B7.34-1} Put φ_A := (DᵀD)^{−1}DᵀA.
  {#B7.34-2} Since 𝐇D = 𝒩,

    {#B7.35} ⟨A′, KA⟩ = T(J, φ_{A′}, A) + T(J, φ_A, A′) − T(J, φ_A, Dφ_{A′}).  (7.1)

  {#B7.36} So K is linear in J, and it is nonlocal through φ.
- {#B7.37} *PBG's propagators.* Δ_π is PBG's gauge-invariant extension (3.119), and Δ′_π := 𝐇 − Δ_π is given by PBG (3.120).
  {#B7.38} Δ_π is invariant only under λ ∈ N(Q′).
  {#B7.38-1} Every term of (3.120) contains λ_A := G′RD*A.
  {#B7.38-2} G := (Δ_π + DRD* + aQ*Q)^{−1}
  {#B7.39} (PBG (3.122)), H := GQ*(QGQ*)^{−1} (PBG (3.126)), and C_G := G − GQ*(QGQ*)^{−1}QG.
  {#B7.39-1} By PBG (3.124), RD*H = 0, so
  {#B7.40} λ_{Hz} = 0.
- {#B7.41} *Bloch norms.* A field X is a Bloch wave of quasi-momentum p if X(x + y) = e^{ip·y}X(x) for coarse translations y.
  {#B7.42} Matrix elements between Bloch waves are taken per top unit cell.
  {#B7.42-1} Put ‖X‖_∞ := sup|X| and
  {#B7.43} ‖X‖_2 := (Σ_{x∈cell} η⁴|X(x)|²)^{1/2}, so ‖X‖_2 ≤ ‖X‖_∞ and ‖X‖_∞ ≤ Σ_l|X̂(p + l)|.
  {#B7.43-1} If three Bloch waves have
  {#B7.44} quasi-momenta adding to 0, then Σ_{cell} η⁴|fgh| ≤ ‖f‖_∞‖g‖_∞‖h‖_2.
  {#B7.44-1} At U = 1, on quasi-momentum p, the
  {#B7.45} symbols satisfy Δ(q) ≥ (4/π²)|q|² and |q| ≥ |p|.
  {#B7.45-1} So ‖(DᵀD)^{−1}‖ ≤ (π²/4)|p|^{−2}, ‖(DᵀD)^{−1}Dᵀ‖ ≤ (π/2)|p|^{−1},
  {#B7.46} and ‖Π_D‖ ≤ 1.

{#B7.47} *Proof.*
{#B7.47-1} *Gauge.* Let u be a fine gauge transformation that is a coarse-translation covariant function of B, as VAR's is (#B7.47-5). F_k (#B3.2.34) on the fields of 𝒪 ∪ (−𝒪) does not change when the background U is replaced by U^u: V becomes V^û, with û := u on the top lattice (#B3.1.11-1).
{#B7.47-2} Indeed Q̃(U^u)Ad(u) = Ad(û)Q̃(U) by #B3.1.11-1, h(U^u) = Ad(u)h(U)Ad(u)^{−1} (#B3.3.6-1), and D̄_{V^û} = Ad(û)D̄_VAd(û)^{−1}, with Ad(u) acting bondwise; so Δ_k, 𝒟_k, and D̄_VᵀD̄_V are conjugated by Ad(û), which is orthogonal for real B (#B7.86-1).
{#B7.47-2a} For fixed B, u is periodic under the translations that fix B, so Ad(u) and Ad(û) shift quasi-momenta only by ℤp₀ and map the fields of 𝒪 ∪ (−𝒪) onto themselves; the conjugations above are therefore conjugations of the coset operators.
{#B7.47-3} The proof runs at U^L := U^u, with u the inverse of VAR's transformation of #B7.47-5 (VAR p.281 l.3: U₁ = U′^{u^{−1}}), so U^L is VAR's Landau-gauge form of U_k(e^{iB}) (#B7.78-1), with V^L := V^û; the Setting holds at any background. Below, U and V denote U^L and V^L, except in #B7.125–#B7.126-1, where log det(D̄_VᵀD̄_V), unchanged by #B7.47-2–#B7.47-2a, is taken at V = e^{iB}.
{#B7.47-4} U^L and V^L = Ū(U^L) are coarse-translation covariant functions of B (#B7.47-5); so their τ-coefficients have momenta in ℤp₀, which is all that the coset structure of (a) uses.
{#B7.47-5} VAR p.281 l.2–3 gives "exactly one gauge transformation u satisfying R̄₀u^j = 1 on Λ_j" such that U′^{u^{−1}} satisfies REG (1.36)–(1.39). At U₀ = 1, with every Ω_j the whole torus, these conditions are invariant under top-lattice translations, and so is the axial gauge of U_k(e^{iB}), whose orbit is unique (VAR p.279 l.15); so VAR's u and its inverse, and with them U^L, are covariant.

{#B7.48} *(a) A fixed transverse space.* Let T₀ := (ran D̄_0)^⊥, with D̄_0 the coarse gauge action at V = 1, and orthogonal projection P_T, and let Π_V be the orthogonal
{#B7.49} projection onto (ran D̄_V)^⊥.
- {#B7.50} Let B be a plane wave of momentum p₀ ≢ 0 on a torus, and 𝒪 ≠ ℤp₀ a coset (Remark 3.4).
  {#B7.50-1} Steps (a) and (b) are
  {#B7.51} restricted to the fields on 𝒪 ∪ (−𝒪).
  {#B7.51-1} There D̄_V is injective for small real B, so (ran D̄_V)^⊥ has constant
  {#B7.52} dimension, and Π_V → P_T as B → 0.
  {#B7.52-1} Hence Π_V maps T₀ isomorphically onto (ran D̄_V)^⊥.
- {#B7.53} By Lemma 3.3, Δ_k = Π_VΔ_kΠ_V, so det_{T₀}(P_TΔ_kP_T) = det_⊥(Δ_k) · det_{T₀}(P_TΠ_VP_T).
- {#B7.54} Hence

    {#B7.55} F_k = ½ log det_{T₀}(P_TΔ_kP_T) − ½ log det_{T₀}(P_TΠ_VP_T) − ½ log det(D̄_VᵀD̄_V).

  {#B7.56} The last two terms are bounded independently of k (step (e)).
  {#B7.56-1} By Remark 3.4, the limits of the coset sums of the
  {#B7.57} second-order coefficients are the momentum integrals at p₀ ≠ 0 of steps (e) and (f).

{#B7.58} *(b) Representation.* For every coarse z,

    {#B7.59} ⟨z, Δ_kz⟩ = min{⟨A, (h + DRD* + aQ*Q)A⟩ : QA = z} − a|z|².

- {#B7.60} §3's ⟨z, Δ_kz⟩ is the minimum of ⟨A, hA⟩ over {Q̃A ∈ z + ran D̄}, which is {QA ∈ z + ran D̄} (Setting).
- {#B7.61} Every A with QA ∈ z + ran D̄ is moved by a gauge direction Dω to QA = z, because QD = D̄Q′ and Q′ is onto. h is
  {#B7.62} gauge-invariant.
- {#B7.63} Some λ ∈ N(Q′) with Δλ = RD*A exists, because RD*A ∈ ΔN(Q′).
  {#B7.63-1} The move A ↦ A − Dλ leaves QA and h unchanged and
  {#B7.64} gives RD*A = 0 (PBG p.419).
  {#B7.64-1} There DRD* vanishes, and DRD* ≥ 0 everywhere.

{#B7.65} Since 𝐇 = Δ_π + Δ′_π and h = 𝐇 − K, we have h + DRD* + aQ*Q = G^{−1} − K′ with K′ := K − Δ′_π.
{#B7.65-1} Here K′ is linear in J
{#B7.66} and invariant under N(Q′).
{#B7.66-1} For t ∈ ℂ let

    {#B7.67} m_t(z) := min{⟨A, (G^{−1} − tK′)A⟩ : QA = z} − a|z|².

{#B7.68} Then Δ_k = m_1.
{#B7.68-1} The constrained Gaussian (Schur complement) gives the t^n term of m_t as −t^n H*K′(C_GK′)^{n−1}H for
{#B7.69} n ≥ 1, with t⁰ term (QGQ*)^{−1} − a.
{#B7.69-1} On the fields of a coset 𝒪 ≠ ℤp₀ (step (a)), K′ = O(B), so for small B the map t ↦ m_t is analytic on |t| ≤ 2,
{#B7.70} and the t^n term is of order n in B. Moreover H*Δ′_πH = 0: polarising (3.120), every term contains λ_{Hz} = 0 or
{#B7.71} λ_{Hz′} = 0.
{#B7.71-1} So, up to terms of order three in B,

    {#B7.72} Δ_k = [(QGQ*)^{−1} − a] − H*KH − H*K′C_GK′H.  (7.2)

{#B7.73} *(c) Inputs.*
- {#B7.74} At U = 1, (QGQ*)^{−1} has kernel ≤ Ce^{−δ₁|y−y′|} (PBG (3.132), p.422, §0's input 6), and H has the bounds (3.133).
  {#B7.74-1} By the Schur test, ‖(QGQ*)^{−1}‖ ≤ C on ℓ² of coarse fields.
  {#B7.75-1} So sup|Hz| ≤ C|ẑ| for
  {#B7.76} a coarse plane wave z.
- {#B7.78-1} In VAR's Landau-gauge form U^L of U_k(e^{iB}) (#B7.47-3),
  {#B7.79} U = exp(iη𝓗(B)) with |𝓗| < B₅ε₁, VAR's ε₂ (VAR Proposition 9 with (19) and (173), pp.281, 305, 309).
  {#B7.79-1} For B ∈ 𝔅_r and r small, V′ := e^{iB} and V₀ := 1 meet VAR's assumptions for §G (p.305 l.31–33): V₀ satisfies (7) (p.278 l.36) trivially, and |V′ − 1| ≤ re^r < C₁ε₁, which is (172).
  {#B7.79-2} Proposition 9 (p.309 l.9–13) states that 𝓗(B) is "an analytic function of B" for "G^c-valued small configurations V′" and satisfies (19)–(21) with B₅ε₁ for their ε₂. So (19) holds on 𝔅_r; this is used as printed.
- {#B7.80} The first- and second-order parts in the plane-wave directions b, b̄ are bounded as follows: those of the analytic function 𝓗 of B by Cauchy estimates (𝔅-norm ≤ (1 + π)|b|), those of J by #B7.81-1–#B7.81-5, the others by #B7.86-1–#B7.86-27.
  - {#B7.81} j₁ and j₂, the first- and second-order parts of J in VAR's Landau gauge (#B7.78-1), have ‖j₁‖_∞ ≤ C|b| and ‖j₂‖_∞ ≤ C|b|².
    {#B7.81-1} In the notation of #B7.86-2, J = D_U*πΦ with Φ(p) := η^{−2}Im U(∂p), D_U* the adjoint (3.9) of the plaquette derivative (3.4) at U, and π as in #T10.28-1-0: for g-valued A, ⟨A, J⟩ = ⟨A, D_U*Φ⟩ (PBG (3.11), printed without π) = ⟨D_UA, Φ⟩ = ⟨D_UA, πΦ⟩, as π is tr-orthogonal, and J and D_U*πΦ are g-valued. Φ^{[0]} = 0, and (πΦ)^{[n]} = πF_p^{[n]} = F_p^{[n]} for n = 1, 2 (#B7.86-15–#B7.86-16), as F_p^{[n]} ∈ g.
    {#B7.81-2} So J^{[1]} = d_η^*d_ηA₁ and J^{[2]} = d_η^*d_ηA₂ + d_η^*F^{com} + (D*)^{[1]}F^{[1]}, with d_η^* the adjoint (3.9) at U = 1 of the fine curl d_η (#B7.86-15), and F^{com}_p := (i/2)Σ_{j<l}[x_j, x_l], the commutator part of F_p^{[2]} (#B7.86-15).
    {#B7.81-3} At U₀ = 1, VAR (19) with j = k and L^kη = 1 gives |D*D𝓗| = |d_η^*d_η𝓗| < B₅ε₁ on Ω_k, so Cauchy estimates as in #B7.83-1 give ‖d_η^*d_ηA_n‖_∞ ≤ Cβ_n (β_n of #B7.86-4).
    {#B7.81-4} By (3.8)–(3.9) at U = 1, (d_η^*F^{com})(b) is a sum of at most d terms η^{−1}(F^{com}_{p′} − F^{com}_p), p′ the translate of p by −ηe_ν. The bond values on ∂p′ and ∂p differ by η∇A₁, so each term is ≤ 6c_𝐠‖A₁‖_∞‖∇A₁‖_∞ ≤ Cβ₂ (#B7.83, #B7.83-1).
    {#B7.81-5} (D*)^{[1]} replaces one transport R(U(x, x − ηe_ν)) in (3.8)–(3.9) by its τ-coefficient iη ad A₁ (#B7.86-11), so |(D*)^{[1]}F^{[1]}| ≤ dc_𝐠‖A₁‖_∞‖F^{[1]}‖_∞ ≤ Cβ₂, as |F^{[1]}| = |d_ηA₁| ≤ 2‖∇A₁‖_∞. With #B7.86-3, this is #B7.81.
  - {#B7.82} H₁z, the first-order part of H(U)z, is a sum of two Bloch waves (quasi-momenta p ± p₀), each with ‖·‖_2 ≤ C|b||ẑ| (#B7.86-26).
  - {#B7.83} A₁, the first-order part of 𝓗, has ‖A₁‖_∞ ≤ C|b|.
    {#B7.83-1} A₂, the second-order part, has ‖A₂‖_∞ ≤ C|b|², and ‖∇A₁‖_∞ ≤ C|b|, ‖∇A₂‖_∞ ≤ C|b|², with ∇ the fine difference quotients: VAR (19) gives |∇𝓗| < B₅ε₁ on Ω_k (U₀ = 1, L^kη = 1).
  - {#B7.84} The first- and second-order parts of (QGQ*)^{−1}(U) have ℓ² norms ≤ C|b| and ≤ C|b|² (#B7.86-25).
- {#B7.85} At U = 1, ‖G‖ ≤ C and ‖G′‖ ≤ C. By #B7.28, the kernel bounds of PBG Theorems
  {#B7.86} 3.1 and 3.3 (B₀e^{−δ₀d(y,y′)} in top units) and the Schur test apply.
- {#B7.86-1} *Taylor coefficients at U = 1.* Π_{F_k}(p₀) and the vertices V¹, V² of (d) are Taylor coefficients at B = 0, so real B suffice for them.
  {#B7.86-2} For real B put A(τ) := 𝓗(τB) = τA₁ + τ²A₂ + O(τ³) and U(τ) := exp(iηA(τ)) (VAR's Landau gauge), and for an operator X(U) let X^{[n]} be the τ^n coefficient of X(U(τ)), so X^{[0]} = X(1).
  {#B7.86-2a} The superscript [n] is not the subscript of Q_k or of the composites Q_{≤j} (#B7.14), and τ is not the t of m_t in (b); C_G is the operator of #B7.39, and C a constant.
  {#B7.86-3} On the finite torus the operators of the Setting are real-analytic in τ near 0, since the inverses in them exist at τ = 0. X^{[n]} is homogeneous of degree n in B; the bounds below hold for its polarisations at be and b̄ē, since each formula is multilinear in A₁ and A₂.
  {#B7.86-4} Put β₁ := |b|, β₂ := |b|², β₀ := 1. Here ‖·‖ is the ℓ² norm on the whole torus (weight η⁴ on fine fields, 1 on coarse ones) and the operator norm it defines; for Bloch waves a bound in this norm gives the same bound in ‖·‖_2 per top cell.
  - {#B7.86-5} *Energy norms.* For fine 1-forms put ‖A‖_E := ⟨A, G^{−1}A⟩^{1/2}, and for gauge parameters ‖λ‖_{E′} := ⟨λ, G′^{−1}λ⟩^{1/2}, with G = G(1) and G′ = G′(1).
    {#B7.86-6} Then ‖A‖ ≤ ‖G‖^{1/2}‖A‖_E, and a^{1/2}‖QA‖ ≤ ‖A‖_E since G^{−1} = 𝐇(1) + ∂R∂* + aQ*Q with 𝐇(1), ∂R∂* ≥ 0 (#B7.138-1). PBG (3.46) for G (Theorem 3.3) at U = 1, summed over the cubes Δ(y), gives ‖∇G∇*‖ ≤ C, i.e. ∇*∇ ≤ CG^{−1}; so ‖∇A‖ ≤ C‖A‖_E, and ‖∂*A‖ ≤ √d‖∇A‖.
    {#B7.86-7} Likewise ‖λ‖ ≤ ‖G′‖^{1/2}‖λ‖_{E′} and ‖∂λ‖ ≤ ‖λ‖_{E′}, since G′^{−1} = ∂*∂ + Q′*aQ′ at U = 1 (PBG (3.23)–(3.24)).
    {#B7.86-8} For a functional f put ‖f‖_{E*} := sup_A|⟨f, A⟩|/‖A‖_E = ‖G^{1/2}f‖. Then ‖Gf‖_E = ‖f‖_{E*}, ‖Q*w‖_{E*} ≤ a^{−1/2}‖w‖, and ‖X*w‖_{E*} ≤ ‖G‖^{1/2}‖X‖‖w‖ for X bounded on ℓ²; the same holds for E′ and G′.
  - {#B7.86-9} *Factors at U = 1.* S := QGQ* has ‖S‖ ≤ a^{−1}, since aQ*Q ≤ G^{−1}, and ‖S^{−1}‖ ≤ C (#B7.74-1). S′ := Q′G′²Q′* has ‖S′^{−1}‖ ≤ C (PBG Thm 3.2 at U = 1, (3.48) with L^kη = 1, and the Schur test).
    {#B7.86-10} H = GQ*S^{−1} has ‖Hw‖_E² = ⟨w, S^{−1}w⟩ ≤ ‖S^{−1}‖‖w‖². C_G = G^{1/2}(I − P)G^{1/2}, with P := G^{1/2}Q*S^{−1}QG^{1/2} an orthogonal projection, so C_G ≥ 0 and ‖C_Gf‖_E ≤ ‖f‖_{E*}.
  - {#B7.86-11} *Local factors.* R(U_b(τ)) = exp(iη ad A(τ)(b)) has τ-coefficients iη ad A₁(b) and iη ad A₂(b) − (η²/2)(ad A₁(b))², with |ad X| ≤ c_𝐠|X| (#B4.197-3).
    {#B7.86-12} So the coefficients D^{[n]} (n = 1, 2) of D_Uλ(b) = η^{−1}(R(U_b)λ(b₊) − λ(b₋)) (#B4.148), of D_U*, and of the plaquette derivative (3.4) on 1-forms contain no difference quotient, have range 1, and have ℓ² norms ≤ Cβ_n.
    {#B7.86-13} Q^{[n]} and Q′^{[n]} have ℓ² norms ≤ Cβ_n (Lemma 7.3 with #B7.165-1–#B7.165-2; #B4.197-3). J^{[0]} = 0 (#B4.212-1) and ‖J^{[n]}‖_∞ ≤ Cβ_n (#B7.81).
  - {#B7.86-14} *The Hessian.* By PBG (3.10), 𝐇 = D*D + Δ′, with D the plaquette derivative (3.4). Δ′ has two terms: tr((D¹A)(p))²η^{−2}(Re U(∂p) − 1), with D¹ = ηD by comparison with (3.7), and the commutators of the transported bond values of PBG (3.6) against η^{−2}Im U(∂p).
    {#B7.86-15} Write U(∂p) = exp(iη²F_p). By Baker–Campbell–Hausdorff, F_p has τ-coefficients F_p^{[1]} = (d_ηA₁)(p) and F_p^{[2]} = (d_ηA₂)(p) + (i/2)Σ_{j<l}[x_j, x_l], with d_η the fine curl (#B5.123-1 at ε = η) and x_j the signed values of A₁ on the bonds of ∂p in order; so |F_p^{[n]}| ≤ Cβ_n (#B7.83-1).
    {#B7.86-16} So η^{−2}Im U(∂p) = η^{−2}sin(η²F_p) has τ-coefficients F_p^{[1]} and F_p^{[2]}, and Re U(∂p) − 1 = cos(η²F_p) − 1 has 0 and −η⁴(F_p^{[1]})²/2. The transports in these transported bond values have τ-coefficients ≤ Cηβ_n.
    {#B7.86-17} Hence |⟨A′, 𝐇^{[n]}A⟩| ≤ Σ_{i+j=n}‖D^{[i]}A′‖‖D^{[j]}A‖ + Cβ_n(‖A′‖‖A‖ + ‖d_ηA′‖‖d_ηA‖) ≤ Cβ_n‖A′‖_E‖A‖_E, with D^{[0]} = d_η and ‖d_ηA‖ ≤ 2‖∇A‖.
  - {#B7.86-18} *G′ and R.* M′ := G′(U)^{−1} = D*D + Q′*aQ′ on gauge parameters has |⟨λ′, M′^{[n]}λ⟩| ≤ Cβ_n‖λ′‖_{E′}‖λ‖_{E′} (#B7.86-7, #B7.86-12, #B7.86-13).
    {#B7.86-19} G′^{[1]} = −G′M′^{[1]}G′ and G′^{[2]} = G′M′^{[1]}G′M′^{[1]}G′ − G′M′^{[2]}G′, so ‖G′^{[n]}f‖_{E′} ≤ Cβ_n‖G′^{1/2}f‖, and ‖G′^{[n]}‖, ‖∂G′^{[n]}‖ ≤ Cβ_n for n = 0, 1, 2.
    {#B7.86-20} By PBG (3.25), R = I − G′Q′*S′^{−1}Q′G′ at every U, with (S′^{−1})^{[1]} = −S′^{−1}S′^{[1]}S′^{−1} and (S′^{−1})^{[2]} = S′^{−1}S′^{[1]}S′^{−1}S′^{[1]}S′^{−1} − S′^{−1}S′^{[2]}S′^{−1}. Expanding the products, ‖S′^{[n]}‖, ‖R^{[n]}‖ ≤ Cβ_n.
    {#B7.86-21} So RD* and Λ := G′RD* (the map A ↦ λ_A, #B7.38-1) have ‖(RD*)^{[n]}A‖, ‖Λ^{[n]}A‖, ‖(DΛ)^{[n]}A‖ ≤ Cβ_n‖A‖_E for n = 0, 1, 2, by ‖∂*A‖ ≤ C‖A‖_E and ‖∂G′^{[i]}f‖ ≤ Cβ_i‖f‖.
  - {#B7.86-22} *G^{−1}.* By PBG (3.120) and (3.122), M := G(U)^{−1} = 𝐇 − Δ′_π + (RD*)*(RD*) + aQ*Q at every U, since R is an orthogonal projection.
    {#B7.86-23} Δ′_π is linear in J and built from Λ, DΛ, and the transports R_b (3.120). Since J^{[0]} = 0, (Δ′_π)^{[1]} is (3.120) at U = 1 with J^{[1]}, and (Δ′_π)^{[2]} is the same with J^{[2]} plus the τ-coefficient of the U-dependence at J^{[1]}.
    {#B7.86-24} With Σ_bη⁴|J(b)||X(b)||Y(b′)| ≤ C‖J‖_∞‖X‖‖Y‖ for neighbouring b, b′, and #B7.86-21, |⟨A′, (Δ′_π)^{[n]}A⟩| ≤ Cβ_n‖A′‖_E‖A‖_E. With #B7.86-17, #B7.86-21, and #B7.86-13, |⟨A′, M^{[n]}A⟩| ≤ μ_n‖A′‖_E‖A‖_E with μ_n ≤ Cβ_n.
  - {#B7.86-25} *S^{−1} and H.* G^{[1]} = −GM^{[1]}G and G^{[2]} = GM^{[1]}GM^{[1]}G − GM^{[2]}G, so ‖G^{[n]}f‖_E ≤ Cβ_n‖f‖_{E*}. S^{[n]} is the sum of Q^{[i]}G^{[j]}Q^{[l]}* over i + j + l = n, and |⟨w′, Q^{[i]}G^{[j]}Q^{[l]}*w⟩| ≤ ‖Q^{[i]}*w′‖_{E*}‖G^{[j]}Q^{[l]}*w‖_E ≤ Cβ_n‖w′‖‖w‖ by #B7.86-8.
    {#B7.86-25a} So (S^{−1})^{[1]} = −S^{−1}S^{[1]}S^{−1} and (S^{−1})^{[2]} = S^{−1}S^{[1]}S^{−1}S^{[1]}S^{−1} − S^{−1}S^{[2]}S^{−1} have ‖(S^{−1})^{[n]}‖ ≤ Cβ_n, which is #B7.84.
    {#B7.86-26} From H = GQ*S^{−1}, H^{[1]} = −C_GM^{[1]}H + C_GQ^{[1]}*S^{−1} − HQ^{[1]}H (#B4.197-6). By #B7.86-8–#B7.86-10, ‖H^{[1]}w‖_E ≤ μ_1‖Hw‖_E + ‖Q^{[1]}*S^{−1}w‖_{E*} + ‖S^{−1}‖^{1/2}‖Q^{[1]}Hw‖ ≤ Cβ_1‖w‖ (#B7.86-13), and ‖H^{[1]}w‖ ≤ ‖G‖^{1/2}‖H^{[1]}w‖_E.
    {#B7.86-26a} H^{[1]} = H₁ is linear in A₁, and A₁ is the sum of its Bloch waves at ±p₀ (coarse translation covariance of 𝓗, #B7.47-5), so H₁z splits as in #B7.82, with the same bound for each part; this is #B7.82.
    {#B7.86-27} Only PBG's operators at U = 1, the local factors, and PBG's identities (3.10), (3.25), (3.120), (3.122), and (3.126), which hold at every U, enter; none of this uses #B9.38.

{#B7.87} All these C depend on d, L, G, r, a, VAR's B₅ε₁, and PBG's constants, and not on k.

{#B7.88} *(d) Vertices.* On T₀ write P_TΔ_kP_T = Δ⁰ + V¹[B] + V²[B, B] + ….
{#B7.88-1} Δ⁰ is PRT1's Δ_k on transverse modes, so
{#B7.89} γ₀|p̂|² ≤ Δ⁰(p) ≤ γ₁|p̂|² (PRT1 (1.66)–(1.67)).
{#B7.89-1} Let z = ẑe^{ip·y} and z′ be transverse plane waves, and B = be^{ip₀·y} + c.c.
{#B7.90} Each term of (7.2) is bounded as follows.
{#B7.90-1} Step (c) gives ‖Hz‖_∞ ≤ C|ẑ|, and Lemma 7.2 gives ‖φ_{Hz}‖_∞,
{#B7.91} ‖Dφ_{Hz}‖_∞ ≤ C|ẑ|.
{#B7.91-1} We claim
{#B7.92} |⟨z′, V¹z⟩| ≤ C|b||ẑ||ẑ′| (z′ of momentum p + p₀) and

    {#B7.93} |⟨z′, V²[b, b̄]z⟩| ≤ C(1 + |(p + p₀)^|^{−2} + |(p − p₀)^|^{−2})|b|²|ẑ||ẑ′|  (z′ of momentum p).
- {#B7.94} *T0, the analytic term.* (QGQ*)^{−1} − a contributes to V¹ and V² at most C|b||ẑ||ẑ′| and C|b|²|ẑ||ẑ′| (step (c)).
- {#B7.95} *T1, first order in J at U = 1.* −⟨Hz′, K(1, j₁)Hz⟩ is the J-part of V¹.
  {#B7.95-1} By (7.1) and #B7.33-1 it is at most
  {#B7.96} 2dc_𝒩‖j₁‖_∞(‖φ_{Hz′}‖_∞‖Hz‖_2 + ‖φ_{Hz}‖_∞‖Hz′‖_2 + ‖φ_{Hz}‖_∞‖Dφ_{Hz′}‖_2) ≤ C|b||ẑ||ẑ′|.
- {#B7.97} *T2, the second-order part of J.* −⟨Hz′, K(1, j₂)Hz⟩ ≤ C|b|²|ẑ||ẑ′| in the same way.
- {#B7.98} *T3, the term H*K′C_GK′H at U = 1.*
  - {#B7.99} Let X := K′(1, j)Hz with j ∈ {j₁[b], j₁[b̄]}; its quasi-momentum is p′ = p ± p₀.
  - {#B7.100} C_G ≥ 0, and on ker Q it is the inverse of G^{−1}.
    {#B7.100-1} So ⟨X, C_GX⟩ = sup{2Re⟨X, Y⟩ − ⟨Y, G^{−1}Y⟩ : Y ∈ ker Q},
    {#B7.101} with Y a Bloch wave of quasi-momentum p′.
  - {#B7.102} ⟨X, Y⟩ = ⟨Hz, KY⟩ − ⟨Hz, Δ′_πY⟩.
    {#B7.102-1} By (7.1) and #B7.33-1, |⟨Hz, KY⟩| ≤ 2dc_𝒩‖j‖_∞(‖φ_{Hz}‖_∞‖Y‖_2 + (‖Hz‖_∞ +
    {#B7.103} ‖Dφ_{Hz}‖_∞)‖φ_Y‖_2) ≤ C(1 + |p̂′|^{−1})|b||ẑ|‖Y‖_2.
  - {#B7.104} Polarising (3.120) with λ_{Hz} = 0 gives ⟨Hz, Δ′_πY⟩ = ½⟨i[λ_Y(b₋), Hz(b)] − i[Hz(b), R_bλ_Y(b₊)], j⟩.
    {#B7.104-1} So
    {#B7.105} |⟨Hz, Δ′_πY⟩| ≤ 2dc_𝒩‖j‖_∞‖Hz‖_∞‖λ_Y‖_2 (#B7.33-1).
  - {#B7.106} At U = 1, Δ_π = 𝐇(1) = d_η^*d_η ≥ 0 (#B7.81-2), so ⟨Y, G^{−1}Y⟩ ≥ ‖RD*Y‖² and ⟨Y, G^{−1}Y⟩ ≥ ‖G‖^{−1}‖Y‖².
    {#B7.106-1} Also
    {#B7.107} ‖λ_Y‖ ≤ ‖G′‖‖RD*Y‖.
  - {#B7.108} Hence ⟨X, C_GX⟩ ≤ C(1 + |p̂′|^{−1})²|b|²|ẑ|², and by Cauchy–Schwarz for C_G ≥ 0 the T3 terms are at most
    {#B7.109} C(1 + |(p + p₀)^|^{−2} + |(p − p₀)^|^{−2})|b|²|ẑ||ẑ′|.
- {#B7.110} *T4, first order in J and in U.* This is the first-order part in U of −⟨H(U)z′, K(U, j₁)H(U)z⟩; the Δ′_π part
  {#B7.111} vanishes at every U by (3.124).
  - {#B7.112} When the derivative falls on H, (7.1) gives terms such as T(j₁, φ_{H₁z′}, Hz), T(j₁, φ_{Hz}, H₁z′), and
    {#B7.113} T(j₁, φ_{Hz}, Dφ_{H₁z′}), and the same with z and z′ exchanged.
    {#B7.113-1} Here ‖φ_{H₁z′}‖_2 ≤ (π/2)|p′|^{−1}‖H₁z′‖_2 at the
    {#B7.114} quasi-momentum p′ = p ± p₀ of H₁z′, and ‖Dφ_{H₁z′}‖_2 ≤ ‖H₁z′‖_2.
    {#B7.114-1} These terms are at most
    {#B7.115} C(1 + |p̂′|^{−1})|b|²|ẑ||ẑ′|.
  - {#B7.116} When the derivative falls on D_U, D₁λ(b) = i[A₁(b), λ(b₊)] has no derivative, and the derivative of 𝒩 carries a
    {#B7.117} factor η.
    {#B7.117-1} At fixed A, the derivative of φ_A is (DᵀD)^{−1}[D₁ᵀΠ_⊥A − DᵀD₁φ_A].
    {#B7.117-2} On quasi-momentum p′, its norm is at
    {#B7.118} most C‖A₁‖_∞(|p′|^{−2}‖A‖_2 + |p′|^{−1}‖φ_A‖_∞).
    {#B7.118-1} With A = Hz, Hz′, (7.1) and Lemma 7.2 bound these terms by
    {#B7.119} C(1 + |p̂′|^{−2})|b|²|ẑ||ẑ′|.

{#B7.120} The four kinds of term give the two claimed bounds.
{#B7.120-1} All constants are independent of k.

{#B7.121} *(e) The top-level terms.* They are explicit functions on the unit lattice of B^L_1 (the Π_V term) and of B (the D̄ᵀD̄ term, #B7.47-3).
{#B7.121-1} B^L_1 := a^{(k)}_1, the τ-coefficient of the normalised logarithm of V^L (#B7.206), is Q̃(1)A₁, a Bloch wave at ±p₀ (Q̃(1) commutes with coarse translations) with ‖B^L_1‖_∞ ≤ (1 + d)‖A₁‖_∞ ≤ C|b| (#B7.206-3, #B7.83); so its amplitudes are ≤ C|b|.
- {#B7.122} P_TD̄_V = P_TD̄_1[B^L_1] + O(B²), where D̄_1[B^L_1]ω(c) = i[B^L_1(c), ω(c₊)] (as D₁ in #B4.149) has no derivative.
  {#B7.122-1} So
  {#B7.123} log det_{T₀}(P_TΠ_VP_T) = −Tr(P_TD̄_1(D̄_0ᵀD̄_0)^{−1}D̄_1ᵀP_T) + O(B³), and its symbol at p₀ is at most
  {#B7.124} C∫|p̂|^{−2}d⁴p.
- {#B7.125} For log det(D̄_VᵀD̄_V), the first- and second-order vertices of D̄_VᵀD̄_V are at most C(|p̂| + |(p + p₀)^|) and
  {#B7.126} C(1 + |p̂|).
  {#B7.126-1} So its symbol at p₀ is at most C∫(|p̂|^{−2} + |p̂|^{−2}|(p + p₀)^|^{−2}(|p̂| + |(p + p₀)^|)²)d⁴p.

{#B7.127} *(f) Integration.* The second-order coefficient of ½ log det_{T₀}(Δ⁰ + V¹ + V²) is
{#B7.128} ½Tr(Δ⁰^{−1}V²) − ¼Tr(Δ⁰^{−1}V¹Δ⁰^{−1}V¹).
{#B7.128-1} By (d) and γ₀|p̂|² ≤ Δ⁰,

    {#B7.129} ‖Π_{F_k}(p₀)‖ ≤ C ∫_{[−π,π]⁴} [|p̂|^{−2}(1 + |(p + p₀)^|^{−2} + |(p − p₀)^|^{−2}) + |p̂|^{−2}|(p + p₀)^|^{−2}] d⁴p
      {#B7.130} + (the terms of (e)) < ∞.

{#B7.131} The integrals converge because d = 4 and p₀ ≠ 0, which separates the singular points 0 and ∓p₀. ∎

{#B7.133} **Lemma 7.2 (The Gauge Parameter of H at U = 1).** Let z = ẑe^{ip·y} be a coarse plane wave with p ≠ 0 and |p_μ| ≤ π,
{#B7.134} and let H = H(1).
{#B7.134-1} If z is transverse (Σ_μ \overline{∂¹_μ(p)}ẑ_μ = 0, with ∂¹_μ(p) = e^{ip_μ} − 1 the v_μ(p) of §4, that
{#B7.135} is, z ∈ T₀), then φ := (∂*∂)^{−1}∂*Hz satisfies ‖φ‖_∞ + ‖∂φ‖_∞ ≤ C|ẑ|.
{#B7.135-1} Here C depends only on d and L.

{#B7.136} *Proof.* We use the notation of Lemma 5.2: q = p + l, Δ(q), Δ₀(p), u, v_μ, φ_μ, c₀, c₁, c_N.
1. {#B7.137} *H is PRT1's H_k.* At U = 1, Q = Q_k with centred blocks (§7's Setting), J = 0, and Δ_π = 𝐇(1) by PBG (3.119),
   {#B7.138} since 𝐇(1)∂ = 0; ⟨A, 𝐇(1)A⟩ = ‖∂A‖².
   {#B7.138-1} G^{−1} = 𝐇(1) + ∂R∂* + aQ_k*Q_k is positive definite (G is bounded, PBG
   {#B7.139} Theorem 3.3), so Hz is the unique minimiser of ⟨A, G^{−1}A⟩ on {Q_kA = z} (PBG p.420).
   - {#B7.140} On that set ⟨A, G^{−1}A⟩ = ‖∂A‖² + ‖R∂*A‖² + a|z|² ≥ ‖∂A‖² + a|z|².
   - {#B7.141} H_kz minimises ‖∂A‖² on {Q_kA = z} (Proposition 5.3, step 1, third fact), and R∂*H_kz = 0 (PRT1 p.29).
     {#B7.141-1} So H_kz
     {#B7.142} attains the lower bound, and Hz = H_kz.
     {#B7.142-1} (The centred blocks change Fourier coefficients by unit phases only.)
   - {#B7.143} Hence φ = φ_k := (∂*∂)^{−1}∂*H_kz.
2. {#B7.144} *PRT1's gauge parameter.* Take N(p) of #B5.49, and put S(p) := Σ_ν|∂¹_ν(p)|²/(Δ₀(p)²φ_ν(p)) and
   {#B7.145} β(p) := Σ_λ \overline{∂¹_λ(p)}(Δ₀(p)φ_λ(p))^{−1}ẑ_λ.
   - {#B7.146} Apply ∂* to the first form of PRT1 (1.63).
     {#B7.146-1} Use \overline{∂_μ(q)}\overline{v_μ(q)} = \overline{∂¹_μ(p)} and
     {#B7.147} Σ_μ|∂_μ(q)|² = Δ(q).
     {#B7.147-1} The B̂_μ term and the ∂¹_μ term then cancel, and

       {#B7.148} (∂*H_kz)^(q) = \overline{u(q)}Δ₀(p)N(p)^{−1}S(p)^{−1}β(p)/Δ(q).

   - {#B7.149} So φ_k has φ̂_k(q) = \overline{u(q)}Δ₀(p)N(p)^{−1}S(p)^{−1}β(p)/Δ(q)².
   - {#B7.150} With N ≥ c_N, S ≥ 1/c₁, and the bounds of Lemma 5.2, step 1, this gives
     {#B7.151} Σ_l(1 + |∂(q)|)|φ̂_k(q)| ≤ C|β(p)||p|^{−2}.
   - {#B7.152} Next, |Δ₀(p)φ_λ(p) − 1| ≤ C|p|².
     - {#B7.153} Write s(x) := sin x/x.
       {#B7.153-1} Then |∂¹_μ(p)|² = p_μ²s(p_μ/2)² and |∂_μ(p)|² = p_μ²s(ηp_μ/2)².
       {#B7.153-2} Since s ∈ [2/π, 1] and
       {#B7.154} |s(x)² − 1| ≤ x²/3 for |x| ≤ π/2, the term l′ = 0 is a product of factors 1 + O(|p|²).
     - {#B7.155} For l′ ≠ 0, some l′_ν ≠ 0 gives |v_ν(p + l′)|² ≤ C|p|²(1 + |l′_ν|)^{−2}, and Δ₀(p)/Δ(p + l′) ≤ π²|p|²/|l′|².
       {#B7.155-1} So
       {#B7.156} these terms add up to at most C|p|⁴.
   - {#B7.157} For transverse z, β = Σ_λ \overline{∂¹_λ}((Δ₀φ_λ)^{−1} − 1)ẑ_λ, so |β| ≤ C|p|³|ẑ|.
     {#B7.157-1} Hence ‖φ_k‖_∞ + ‖∂φ_k‖_∞ ≤
     {#B7.158} C|p||ẑ| ≤ 2πC|ẑ|, and φ = φ_k by step 1. ∎

{#B7.159} **Lemma 7.3 (The Second-Order Part of the Dressed Average).** Let C^{(2)}(U; A, A′) be the symmetric bilinear
{#B7.160} second-order part in A of the dressed k-fold average of §7's Setting, normalised as in PBG (3.13)–(3.14), with the
{#B7.161} one-step averages of #B7.12-1 composed as in CMP98 (91).
{#B7.161-1} Let U(t) = exp(itηA₁ + O(t²)) bondwise, for a fine 1-form A₁.
{#B7.162} For a field X at spacing s put ‖X‖_p^p := Σ_b s^d|X(b)|^p over the bonds of one top cell.
{#B7.162-1} Then for Bloch waves A, A′
  {#B7.163} ‖C^{(2)}(1; A, A′)‖_1 ≤ C‖A‖_2‖A′‖_2,  ‖∂_tC^{(2)}(U(t); A, A′)|_{t=0}‖_1 ≤ C‖A₁‖_∞‖A‖_2‖A′‖_2,
{#B7.164} and ‖∂_tQ(U(t))|_{t=0}A‖_p ≤ C‖A₁‖_∞‖A‖_p for p = 1, 2.
{#B7.164-1} Here C depends only on d, L, and G. At a top bond c these
{#B7.165} depend only on the fields on B^k(c₋) ∪ B^k(c₊).
{#B7.165-1} If U(t) = exp(iη(tA₁ + t²A₂ + O(t³))), the t² coefficients Q^{[2]} of Q(U(t)) and Q′^{[2]} of Q′(U(t)) (not the composites Q_{≤j} of #B7.14) satisfy ‖Q^{[2]}A‖_p ≤ C(‖A₂‖_∞ + ‖A₁‖_∞²)‖A‖_p and ‖Q′^{[2]}λ‖_p ≤ C(‖A₂‖_∞ + ‖A₁‖_∞²)‖λ‖_p for p = 1, 2.
{#B7.165-2} These bounds, the bound on ∂_tQ, and that of #B4.197-3 on ∂_tQ′ hold also with ‖·‖_p summed over the whole torus.

{#B7.166} *Proof.* Step j (1 ≤ j ≤ k) maps level-(j − 1) fields, of spacing s_j := L^{j−1−k}, to level-j fields, of spacing
{#B7.167} ε_j := Ls_j.
1. {#B7.168} *One step.* Ū̄′_c is built from the level-(j − 1) bond variables of the fluctuation and of the background on the
   {#B7.169} bonds ℛ_c of B(c₋) ∪ B(c₊) and of the lines [x, x′], by products, inverses, conjugations, the group average M of
   {#B7.170} RG1 (0.10), and averages exp(iΣ w log).
   {#B7.170-1} These are defined and analytic near 1 on the complexified group G^c (RG1
   {#B7.171} p.252 l.37, p.253 l.16), and no length enters them.
   {#B7.171-1} So there is one analytic Ψ: (g^c)^n × (g^c)^n → g^c on a complex
   {#B7.172} polydisc of radius r₀(d, L, G), with n = |ℛ_c| depending on d and L, such
   {#B7.173} that (1/i)log Ū̄′_c = Ψ(s_ja, s_jB) for every j, k, and c, where a and B are the background and fluctuation
   {#B7.174} logarithms on ℛ_c.
   {#B7.174-1} Ψ(a, 0) = 0: at U′ = 1 the dressing factors (3.113) are 1, so p.418 l.6 gives Ū̄′_c = Ū_c(Ū_c)^{−1}R̄_c1 = 1, R̄_c = R(Ū_c) acting on the right factor (read from l.13, (U′U)‾_c(Ū_c)^{−1} = u(c₋)R̄_cu^{−1}(c₊); inferred, not printed).
   {#B7.174-2} The normalised step is
   {#B7.175} ε_j^{−1}Ψ(s_ja, s_jB).
2. {#B7.176} *Kernels.* By Cauchy estimates, the Taylor coefficients of Ψ of order N are at most K_N := sup|Ψ|r₀^{−N}, with
   {#B7.177} the sup over the complex polydisc.
   {#B7.177-1} So, at
   {#B7.178} a = ta₁ + O(t²), the second-order part c_j^{(2)} of the normalised step has kernel entries at most K₂s_j²/ε_j =
   {#B7.179} K₂s_j/L on ℛ_c × ℛ_c.
   {#B7.179-1} Its t-derivative has entries at most K₃ns_j³ε_j^{−1}‖a₁‖_∞, and the t-derivative of the
   {#B7.180} linear part has entries at most K₂ns_j‖a₁‖_∞/L on ℛ_c.
3. {#B7.181} *Norms.* Let each bond lie in at most m(d, L) of the sets ℛ_c.
   {#B7.181-1} For a bilinear kernel with entries at most K on
   {#B7.182} ℛ_c × ℛ_c, 2|X||Y| ≤ τ|X|² + τ^{−1}|Y|² and the count give an L¹-norm at most L^dKnm(τ‖B‖_2² + τ^{−1}‖B′‖_2²), so
   {#B7.183} at most 2L^dKnm‖B‖_2‖B′‖_2.
   {#B7.183-1} A linear kernel with entries at most K has L²-norm at most L^{d/2}K(nm)^{1/2} and
   {#B7.184} L¹-norm at most L^dKm.
4. {#B7.185} *Composition at U = 1.* At U = 1 every background is 1, and the linear part of each step is the straight average
   {#B7.186} Q^{(j)} (§7's Setting).
   {#B7.186-1} It is an L¹-, L²-, and L^∞-contraction: each level-(j − 1) bond lies on exactly L lines
   {#B7.187} [x, x′], each with weight s_j^dL^{−1}, and (Q^{(j)}B)(c) is a mean of L^{d+1} values.
   {#B7.187-1} Expanding the composite to
   {#B7.188} second order gives
     {#B7.189} C^{(2)}(1; A, A′) = Σ_{j=1}^k Q^{(k)}⋯Q^{(j+1)} c_j^{(2)}(Q_{≤j−1}A, Q_{≤j−1}A′).
   {#B7.190} By steps 2–3, the j-th term is at most 2L^{d−1}K₂nm s_j‖A‖_2‖A′‖_2.
   {#B7.190-1} Also Σ_{j=1}^k s_j ≤ 1/(L − 1).
5. {#B7.191} *The background of step j* is the raw average Ū^{j−1}(U(t)) (PBG (3.15)), with logarithms tQ̃_{≤j−1}(1)A₁ + O(t²).
   - {#B7.192} At U = 1, Q̃^{(i)}B = Q^{(i)}B − D̄ω^{(i)}(B), with ω^{(i)}(B) the contour mean ω_d of §7's Setting for the
     {#B7.193} field B, and
     {#B7.194} the contours of 𝐆(y, x) have at most (L − 1)d/2 bonds.
     {#B7.194-1} (B(y) consists of the points of spacing s_i in the cube of
     {#B7.195} side ε_i centred at y (RG1 (0.3)), so with L odd (RG1 p.251 l.14) x − y = Σ_μ s_in_μe_μ has |n_μ| ≤ (L − 1)/2; RG1 p.252 l.29
     {#B7.196} prints "L − 1/2".) So |ω^{(i)}(B)| ≤ (L − 1)d s_i sup|B|/2.
   - {#B7.197} By Q̃^{(i)}D̄ = D̄P, Q̃_{≤i}A = Q_{≤i}A − D̄ω_i(A) with ω_i := Pω_{i−1} + ω^{(i)}(Q_{≤i−1}A).
     {#B7.197-1} Since
     {#B7.198} Σ_{i<j}s_i ≤ ε_{j−1}/(L − 1), we get sup|ω_{j−1}| ≤ (d/2)ε_{j−1}sup|A|.
     {#B7.198-1} So the normalised level-(j − 1) gradient is
     {#B7.199} at most d·sup|A|, and ‖Q̃_{≤j−1}(1)A₁‖_∞ ≤ (1 + d)‖A₁‖_∞.
6. {#B7.200} *The derivative.* The t-derivative of the composite falls on one Q^{(i)}, on c_j^{(2)}, or on Q_{≤j−1}.
   {#B7.200-1} By steps 2,
   {#B7.201} 3, and 5 these contribute at most C‖A₁‖_∞ times Σ_j s_jΣ_i s_i, Σ_j s_j², and Σ_j s_jΣ_{i<j}s_i respectively.
   {#B7.201-1} Each
   {#B7.202} of these is bounded independently of k.
   {#B7.202-1} The derivative of Q(U(t)) is the sum over i of the middle factors, with
   {#B7.203} the same bound.
7. {#B7.204} *Locality.* The contours of 𝐆(y, x) lie in B(y), and the lines [x, x′] join B(c₋) to B(c₊), so each step at c
   {#B7.205} uses only the fields on B^k(c₋) ∪ B^k(c₊).
8. {#B7.206} *Second coefficients.* Let a^{(j)}(t) be the normalised level-j logarithms of the raw average Ū^j(U(t)) (step 5), so a^{(0)} = A(t) := tA₁ + t²A₂ + O(t³), and let a^{(j)}_1 and a^{(j)}_2 be their t and t² coefficients.
   {#B7.206-1} The raw step is a fixed analytic function Ψ̃ as in step 1, with a^{(j)} = ε_j^{−1}Ψ̃(s_ja^{(j−1)}), whose normalised linear part is Q̃^{(j)}. So a^{(j)}_2 = Q̃^{(j)}a^{(j−1)}_2 + (s_j/L)Ψ̃_2(a^{(j−1)}_1), with |Ψ̃_2(x)| ≤ K̃₂n²‖x‖_∞² by Cauchy estimates, K̃₂ being step 2's K₂ for Ψ̃.
   {#B7.206-2} Iterating, a^{(j)}_2 = Q̃_{≤j}(1)A₂ + Σ_{i≤j}Q̃_{(i+1→j)}(s_i/L)Ψ̃_2(a^{(i−1)}_1), where Q̃_{(i+1→j)} is the composite of steps i + 1, …, j at U = 1.
   {#B7.206-3} Step 5's argument (Q̃ = Q − D̄ω, with the straight averages L^∞-contractions) applies to any field, so ‖Q̃_{(i+1→j)}X‖_∞ ≤ (1 + d)‖X‖_∞. With ‖a^{(i)}_1‖_∞ ≤ (1 + d)‖A₁‖_∞ (step 5) and Σ_is_i ≤ 1/(L − 1), ‖a^{(j)}_2‖_∞ ≤ C(‖A₂‖_∞ + ‖A₁‖_∞²).
   {#B7.206-4} *Q^{[2]}.* The linear part of step j has entries L^{−1}∂_BΨ(s_ja^{(j−1)}(t), 0) (step 1). Their t² coefficients are at most L^{−1}(K₂ns_j‖a^{(j−1)}_2‖_∞ + K₃n²s_j²‖a^{(j−1)}_1‖_∞²) by step 2's Cauchy estimates, and step 3 turns these entries into ℓ^p norms.
   {#B7.206-5} Q^{[2]} is the sum of the terms with the t² coefficient of one step, or the t-coefficients of two steps i < j, between straight averages (contractions, step 4). So ‖Q^{[2]}‖_{p→p} ≤ C(Σ_js_j(‖A₂‖_∞ + ‖A₁‖_∞²) + (Σ_js_j)²‖A₁‖_∞²) ≤ C(‖A₂‖_∞ + ‖A₁‖_∞²).
   {#B7.206-6} *Q′^{[2]}.* Q′^{(j)} is λ ↦ Σ_{x∈B(y)}L^{−d}R(e^{iθ_j(y,x)})λ(x), with θ_j(y, x) the logarithm of the contour variable of Ū^{j−1}, a fixed analytic function of the level-(j − 1) bond logarithms on the contours of 𝐆(y, x) (#B4.197-1).
   {#B7.206-7} Its linear part is the contour mean, so, with θ_{j,1} and θ_{j,2} its t and t² coefficients, |θ_{j,1}| ≤ s_jd(1 + d)(L − 1)‖A₁‖_∞/2 (#B4.197-2) and |θ_{j,2}| ≤ s_jd(L − 1)‖a^{(j−1)}_2‖_∞/2 + Cs_j²‖a^{(j−1)}_1‖_∞², with Σ_js_j ≤ 1/(L − 1).
   {#B7.206-8} R(e^{iθ_j}) = exp(i ad θ_j) has t² coefficient i ad θ_{j,2} − ½(ad θ_{j,1})², of norm ≤ c_𝐠|θ_{j,2}| + c_𝐠²|θ_{j,1}|²/2. Summing over one or two steps as for Q gives ‖Q′^{[2]}‖_{p→p} ≤ C(‖A₂‖_∞ + ‖A₁‖_∞²).
   {#B7.206-9} The counts of steps 3–4 and of #B4.197-3 are local, so they hold over the whole torus as over one cell. ∎

## 8. The Window Theorem {#BS8}

{#B8.1} **Theorem 8.1.** There is a C such that for all k (from PRT1 (1.67) and Propositions 5.1, 5.3, 6.4 and 7.1)
  {#B8.2} |Φ_k − (11/24π²) κ k ln L| ≤ C,
{#B8.3} and therefore, for all 0 ≤ m ≤ n,
  {#B8.4} **| Σ_{j=m+1}^{n} b_j − (11/24π²) κ (n−m) ln L | ≤ 2C.**

{#B8.5} *Proof.*
1. {#B8.6} *Identity.* ℒ_k is the k-step Gaussian Σ_{j<k}[log Z^{(j)}(U_k) − log Z^{(j)}(1)] (Proposition 5.1, #B2.1.1). On each coset 𝒪 ≠ ℤp₀, where the F_j are defined (Remark 3.4), the definition #B3.3.9 of J^{(j)} makes this sum telescope: ℒ_k = F_k − F_0 + 𝒥_k + const
   {#B8.7} for the restrictions to the fields on 𝒪 ∪ (−𝒪), hence for the coset sums and their limits.
   {#B8.7-1} So at p₀ ≠ 0:
   {#B8.8} Π_{ℒ_k}(p₀) = Π_{F_k}(p₀) + Π_{−F_0}^{top}(p₀) + Π_{𝒥_k}(p₀).
   {#B8.9} These limits are the symbols that step 2 inserts, for the following reasons.
   - {#B8.10} Π_{F_k} is computed on the same cosets (Proposition 7.1(a)).
   - {#B8.11} Π_{ℒ_k} (Proposition 5.1) is the polarisation of Bałaban's step factors on the whole torus.
     {#B8.11-1} Their quadratic forms
     {#B8.12} are built from PBG's G₁, H₁, Δ₁, G′, R, h_B, C̃^{(2)}, and 𝐆^{(2)} (PBG (3.128)–(3.129); Proposition 4.2(a)), and
     {#B8.13} contain no (DᵀD)^{−1}; C^{(j)}(1), j < k, is invertible on the whole torus, and the Jacobian 𝔧(U) is site-local.
     {#B8.13-1} So
     {#B8.14} the block ℤp₀ is regular, its fibres are
     {#B8.15} the m₀ points of ℤp₀ (Remark 3.4), and it adds O(N^{−4}) to the full-torus coefficient.
   - {#B8.16} Π_{𝒥_k} (Proposition 5.3) and Π_{−F_0}^{top} (Proposition 6.4) are alias sums of level-m symbols, m = j + 1 or
     {#B8.17} m = 0, composed with the first-order lift V₁ of B. The fields of level m decompose under the top translations, so
     {#B8.18} each top coset is a union of level-m fibres.
     {#B8.18-1} The level-m first-order coefficient vanishes at U = 1 (Ad-invariance,
     {#B8.19} as for Θ(1) in Proposition 4.2(c)), so on a top coset the top second-order coefficient is the level-m
     {#B8.20} second-order form evaluated on V₁, whose quasi-momenta q = p₀ + l all lie in the top fibre of p₀.
     {#B8.20-1} At U = 1 every
     {#B8.21} level-m operator conserves level-m quasi-momentum, so terms pairing different aliases vanish fibre by fibre.
     {#B8.21-1} So
     {#B8.22} the top coset sum is Σ_l of the level-m coset sums at external momentum q, over the level-m quasi-momenta above
     {#B8.23} top fibres outside ℤp₀.
   - {#B8.24} Those level-m quasi-momenta exclude ℤq and, besides, at most m₀L^{4(k−m)} further points, a number independent of
     {#B8.25} N. They form the set (ℤp₀ + 2πℤ⁴) ∖ ℤq mod 2πL^{k−m} (top units), which does not depend on N and avoids the singular points 0 and ∓q ∈ ℤq of the level-m integrands, so the integrands are bounded on it, as in #B3.2.79.
     {#B8.25-1} So, at fixed k, the
     {#B8.26} limits are the alias sums of the level-m symbols of Propositions 4.2 and 6.3, of which there are L^{4(k−m)}.
2. {#B8.27} *Insert the estimates.* Take p₀ = (π/2, 0, 0, 0) and a unit vector e ⊥ v(p₀).
   {#B8.27-1} Propositions 5.1, 7.1, 6.4 and 5.3
   {#B8.28} give Φ_k⟨e, Δ_k(p₀)e⟩ = c ln(1/η_k²)⟨e, Δ_k(p₀)e⟩ + O(1).
3. {#B8.29} *Divide.* The curl of B = e e^{ip₀·y} has squared symbol |p̂₀|²|e|² − |⟨v(p₀), e⟩|² = |p̂₀|² = 2 (Lagrange's identity, as in step 3 of Proposition 5.3's proof; p̂₀ as in #B7.3), so PRT1 (1.67) gives ⟨e, Δ_k(p₀)e⟩ ∈ [2γ₀, 2γ₁], with γ₀ > 0 independent of k.
   {#B8.29-1} Since
   {#B8.30} ln(1/η_k²) = 2k ln L and 2c = (11/24π²)κ, the claim follows. ∎

{#B8.31} **Corollary 8.2 (RG1 Theorem 2 for Simple G, with (0.31) up to an Additive Constant).** Take ε₁ as in Proposition 2.4, or CRE's cutoff δ_k (#B0.5) in its place.
{#B8.31-1} Theorem 8.1 is hypothesis (W) of §2 at
{#B8.32} zero coupling, and Propositions 2.4 and 2.6 give (P2) with δ = c ln L and (C), for δ_k once γ is small (#B2.1.79-1–#B2.1.80, #B2.1.85); for δ_k, Proposition 2.9 also gives (P2) with δ = C_remγ² (RG1 (0.31), CRE p.265), and γ is taken so small that C_remγ² ≤ c ln L, which is possible since C_rem is fixed before γ (#B2.2.122–#B2.2.123).
{#B8.32-1} By Remark 2.3, Lemma 2.1 gives, for
{#B8.33} every small renormalised coupling g and every ε = L^{−K}:
- {#B8.34} a bare g_0(ε, g), independent of the torus;
- {#B8.35} g_K = g, and all g_k in ]0, γ];
- {#B8.36} RG1 (0.31) with β = 2c − δ/ln L ≥ c and β′ = 2c + δ/ln L, up to an additive constant;
- {#B8.37} the near-monotonicity that the comparison after LFR2 (1.86), p.386 l.38–40, uses (Remark 2.2);
- {#B8.38} CRE (2.6), with b′ + C in place of CRE's constant β′ (p.255 l.44), for each β₀ > 0 once γ is small depending on β₀. With x_j = g_j^{−2} (#T10.29) and m < n, (W) with Remark 2.3's b′ and C gives x_m = x_n + Σ_{j=m}^{n−1}β_{j+1} ≤ x_n + (b′ + C)(n−m), which is g_n ≤ (1 + g_n²(b′ + C)(n−m))^{1/2}g_m.
  {#B8.38-1} 1 + g_n²(b′ + C)(n−m) ≤ (1 + g_n²(b′ + C))(n−m) as n − m ≥ 1, and 1 + g_n²(b′ + C) ≤ 1 + γ²(b′ + C) ≤ (1 + β₀)²; Lemma 2.1(ii) and x_m ≥ γ^{−2} give x_n ≤ x_m + C ≤ (1 + Cγ²)x_m, so g_m ≤ (1 + Cγ²)^{1/2}g_n ≤ (1 + β₀)g_n.
{#B8.38-2} RG1 states Theorem 2 for G = SU(2) (p.259 l.29) and leaves its proof to "a separate paper" (l.38); Corollary 8.2 proves it for simple G with (0.31) up to an additive constant. The upper bound of (0.31) holds exactly, with (b′ + C₀)/ln L in place of β′, as n − m ≥ 1 in #B8.38. The exact lower bound would follow from inf_j b_{j+1} > δ, while Theorem 8.1 places b_{j+1} only within C₀ of 2c ln L (#B8.4 at n = m + 1; #T10.33-2); it is not claimed, and it is not needed.
  {#B8.38-3} Every use of the lower bound takes it up to the constant: t ≥ γ^{−2} + C (Lemma 2.1) gives g_k^{−2} ≥ γ^{−2} + b(K−k), so g_k² ≤ C′/(K − k + 1) with C′ := 1/min(γ^{−2}, b). The other uses need only the upper bound or the near-monotonicity (#B8.37–#B8.38-1).

## 9. Inputs {#BS9}

{#B9.1} **Inputs taken from Bałaban without re-proof, with their caveats.**
- {#B9.2} PRT1 (1.31), (1.61)–(1.63), and the alias decomposition of PRT1 p.23 (for Lemma 5.2, whose bounds (1.36) of PRT1 p.24 l.19–20 and
  {#B9.3} γ₀ ≤ Δ₀φ_μ ≤ γ₁ of PRT1 p.28 l.29 are derived there with constants depending only on d), and PRT1 (1.65)–(1.67); PBG Thms
  {#B9.4} 3.1, 3.2, 3.3, 3.12 at U = 1; PBG (3.117)–(3.137) and (3.156), of which (3.132), stated without proof on p.422, is
  {#B9.5} used as printed, with a proof, not yet through review, in balaban_proofs/BP_PBG_3132.md (#B0.43-1); RG1 (0.28)–(0.30), RG1 (1.8)–(1.9), RG1 pp.262–263
  {#B9.6} (analyticity domains); VAR Thm 1 and §G.
  {#B9.6-1} PBG (3.105)–(3.106) (#B2.2.777); PBG (3.107)–(3.108) and (3.185), which RG2 applies to the chain's operators (RG2 p.003 l.9, l.18, p.013 l.31, l.33); and PBG Theorem 3.15, through the walk expansion of C^{(k)}(Z₀) that RG2 takes from [13] (§0, input 3, #B0.37-1–#B0.37-1a).
- {#B9.7} For Proposition 4.2: Bałaban's step form RG1 (1.4)–(1.5), with (2.5), p.266, (2.10)–(2.11), p.267, the replacement
  {#B9.8} of the δ-function gauge fixing of PBG (3.156) by the exponential term 𝐆^{(2)} (p.267 l.38–39), and the elimination
  {#B9.9} B′ = 𝒫B″ with C^{(k)} = (𝒫*Δ^{(k)}𝒫)^{−1} (p.268 l.2–3).
- {#B9.10} For Proposition 5.3, steps 1 and 4, Proposition 4.2, step (c) (#B4.119), §7's Setting (#B7.22, #B7.27-1), Lemma 7.2 (#B7.141), Lemma 7.3, step 5 (#B7.195), with Proposition 4.2(d) through it (#B4.197-2), and §6 (#B6.3.5-1): PRT1's corner blocks (p.18), its averages (1.8) and
  {#B9.11} (1.11), p.19, and (1.16)–(1.18), p.20; the gauge covariance (1.20), p.20; the projection R onto ΔN(Q′_k) (pp.24–25);
  {#B9.12} the properties of H_kB on p.29 (Q_kH_kB = B, R∂*H_kB = 0, and H_kB a minimum of ½⟨∂A, ∂A⟩ on
  {#B9.13} {A : Q_kA = B, R∂*A = 0}); the Wilson action RG1 (0.2) and the centred blocks
  {#B9.14} RG1 (0.3), p.252, with L odd (p.251 l.14, p.252 l.29); RG1 (0.17) and (0.19), p.255; and RG1 (0.21)–(0.22), p.256 (the unique critical orbit of minima,
  {#B9.15} proved in VAR); and, wherever they appear, PRT1's ∂ and ∂* (#B4.5-1).
- {#B9.16} PBG was written for the averaging of AVG (CMP 98), and PRT1 for the Abelian averages PRT1 (1.8), p.19 l.4, along contours, and (1.11), l.20, straight,
  {#B9.17} which agree on the axial slice A(Γ_{y,x}) = 0 (l.16); (1.11) is the main term (125) of AVG's linear form at V₀ = 1 (CMP98 (124)–(125), p.36 l.31–35: it "resembles the definition
  {#B9.18} of the averaging operation Q in [2]", [2] = PRT1).
  {#B9.18-1} RG1 uses the Euclidean-symmetric average RG1 (0.4) or (0.12) (#B0.37-0).
  {#B9.18-2} At U = 1 the
  {#B9.19} first-order part of either (#B4.187) is PRT1's straight average up to a gradient and a fine translation (Proposition 5.3,
  {#B9.20} steps 1 and 4), so Lemma 5.2 and PRT1 (1.65)–(1.67) apply to the chain at U = 1.
  {#B9.21} Through Proposition 5.3, step 1, the argument also uses the unique minimal orbit
  {#B9.22} and the analyticity in t (the bullet on VAR below). The sentence on RG1 p.253 that the earlier results hold for any
  {#B9.23} average with the listed properties (l.42–43) concerns the group averages M of RG1 (0.5)–(0.10); §10 uses it only to take the average (0.10) (#B10.87-8).
- {#B9.24} At U = 1, the linear parts of the dressed average of the chain and of PBG's dressed average agree up to a fine
  {#B9.25} translation, and both are Q_k (§7's Setting; CMP98 (124)); their second-order parts differ.
  {#B9.25-1} So PBG's bounds at
  {#B9.26} U = 1 on G, G′, H, C_G, R, and (QGQ*)^{−1} (Propositions 4.2(d) and 7.1(c)) hold for the chain as printed.
  {#B9.26-1} The
  {#B9.27} second-order part of the chain's dressed average at U = 1 and its U-derivative, and the U-derivative at 1 of its linear
  {#B9.28} part Q, are bounded directly (Lemma 7.3), and so are the U-derivatives at 1 of D and of RG1's step objects h_B,
  {#B9.29} C̃^{(2)}, 𝒫, and 𝐆^{(2)} (Proposition 4.2(d)).
  {#B9.29-1} Propositions 4.2, 5.3, and 7.1(c) do not use PBG's bounds for these operators away from U = 1.
  {#B9.29-2} Away from U = 1, PBG's bounds enter §§1–8 and Propositions 10.2–10.4 (for G and the H_i) only through Bałaban's results (Lemmas 10.11–10.16 use PBG as (P-PBG), #B9.29-3): RG1 Theorem 3 with RG2's proof in §2 (§0, input 3, #B0.37-1–#B0.37-2); CRE's estimates for the tube construction (#B9.55–#B9.58; CRE p.276); and VAR's results as RG1 states them for the chain (§0, inputs 1 and 5).
  {#B9.29-2a} VAR applies PBG at its background U₀ = U_{k−1}(V₀) (VAR p.280 l.2), at any U₀ with (14) (p.280 l.15–20), and in §G at U₀ = U_k(V₀) (p.305 l.36).
  {#B9.29-2a-1} It uses (3.7) and (3.10), Theorem 3.3 with (3.42), Theorems 3.12 and 3.13, and (3.25), (3.49), (3.69), (3.119)–(3.120), (3.126), (3.132), (3.133), (3.137) and (3.148) (VAR p.283 l.8, p.284 l.37–38, p.285 l.25, p.291 l.36, p.294 l.24, p.295 l.9, p.296 l.22, p.297 l.32 and l.40, p.298 l.27 and l.41–51, p.299 l.3 and l.13, p.306 l.37).
  {#B9.29-2a-2} It also uses PBG's operators at U₀: H(U₀) and its analyticity domain in U₀ (p.287 l.33 and l.36–37); H's kernel bound in (69) (p.288 l.41), by which VAR solves (68) with a Neumann series that PRT2's Lemma 2.1 makes convergent (p.288 l.46–p.289 l.2, l.15); and the projection R(U₀) of the Landau gauge (21) (p.281 l.19). The "additional regularity condition (3.35) in (1.33)" at U₀ is REG's: VAR cites "the result of Sect. F" while applying REG's Theorem 2 (p.280 l.51–52), and REG's Sect. F derives it from U₀ ∈ 𝔘_k (REG p.97 l.29–30; Proposition 6, p.99 l.41).
  {#B9.29-2a-3} Without naming items, VAR takes all of PBG's results at R₁, M₁ (p.277 l.17), "the results of that paper" for the form ½⟨A, ΔA⟩ (p.284 l.37), and the extension of its operators to regular U, with (3.35)–(3.38) for the external U of Proposition 9 (p.309 l.2, l.12). The PBG theorems it names are 3.3 with (3.42), 3.12 and 3.13 (p.285 l.25, p.295 l.9, p.296 l.22, p.297 l.32).
  {#B9.29-2a-4} For the chain's dressed average, (P-PBG) gives the PBG items VAR names at G-valued configurations, where VAR uses them, (3.42) included at U₀ (#B9.29-3; p.297 l.32–p.298 l.6), and H's analyticity in U₀ (#B9.29-3a); balaban_proofs/BP_REG_DRESSED.md (not yet through review) gives REG's Proposition 6 (#B9.29-3b). For §G's G = (Δ_a − Δ^{(2)})^{−1} at U_k(V₀), VAR transfers (3.42) from Δ_a^{−1} by (3.137) (p.306 l.37–38), as printed for the chain and by balaban_proofs/BP_FAMILY_PBG_VAR.md #BFP.167-0 (not yet through review) for the family.
  {#B9.29-2a-5} At complex configurations #B9.29-3a-1 excludes (3.42)'s covariant-Laplacian inequality, so the extension to complex U of p.309 l.2–3 is not covered, and Lemma 10.12 takes Proposition 9 apart from (190) with its operators at G-valued configurations (BP_FAMILY_PBG_VAR.md #BFP.167-0a, #BFP.167-1).
  {#B9.29-3} Lemmas 10.11–10.16 use PBG for the family per factor group in the following form, called (P-PBG), proved in balaban_proofs/ and not yet through review. At G-valued U of PBG's class for a sequence {Ω_j} with Ω₀ = T, with the chain's dressed average (#B9.40-3d), Q′ being built from the averages (p.393 l.34–40), PBG's Theorems 3.1–3.13, (3.131)–(3.137) and (3.147)–(3.153), and the steps of their proofs, hold as PBG states them, and so do the analogs of CMP98 (143) and (149) these proofs use: BP_PBG_DRESSED.md (#BD.1-1).
  {#B9.29-3a} At complex configurations, with the chain's dressed average and the current 𝐉 a variable of the domain with the bound γ of #BX.1 (#T12.28), and for M ≥ M₃, the operators of Theorem 3.4 and G, H, G₁, H₁, (QGQ*)^{−1}, (QG₁Q*)^{−1} and 𝔊 := G₁ − G₁DRD*G₁ − G₁Q*(QG₁Q*)^{−1}QG₁ (G₁𝔓* at the real points, (3.153)) extend analytically to PBG's class (3.37) for these sequences with Mα₀ + α₁ + γ ≤ a_cx (#BX.1-2), M₃ and a_cx depending on d, L and G_i, with their bounds and expansions uniformly there.
  {#B9.29-3a-0} On tori of side at least 20M they extend so to RG1's I.(i)–(iii) at scale j with every Ω_n = T, with (1.12) also on the cubes of side 20M and O(1)LMBα₀ + α₁ + γ₀ ≤ a_cx, γ₀ the bound on 𝐉 of RG1 (1.14), p.262 l.37 (#T10.6-2), and on a domain Y the expansions' terms localised in Y are bounded on Y alone (#BX.1-4).
  {#B9.29-3a-1} There Theorem 3.3 holds without the covariant-Laplacian inequality of (3.42) and the fourth of (3.47): for G and G₁ with ⅜δ₀ for δ₀, and for 𝔊 with ½δ₁′ for δ₀ and without the bounds of 𝔊∇*λ for λ only bounded, and (3.132) and (3.133) with δ₁′ := min(δ_cx, ½δ₀)/8 for δ₁, δ_cx ≤ δ₁ the rate of #BX.7-1a: BP_PBG_COMPLEX.md (#BX.1-2–#BX.1-4).
  {#B9.29-3a-2} As the bounds hold at each (𝐔, 𝐉), they hold with 𝐉 replaced by a current analytic in (𝐔, 𝐉) that meets the bound on 𝐉 and whose value at each bond b depends on (𝐔, 𝐉) within distance O(1)η of b; the operators are then analytic by composition, and a term's domain is formed as in #BX.9-1 with class cubes that contain also these neighbourhoods of the bonds at which a factor 𝐉 or a kernel of Δ′_π takes the current. §10 substitutes so J♮(𝐔, 𝐉) (#B10.177-1) and (t_iJ_{c,i}(𝐔))_i (#BFR.209-1b).
  {#B9.29-3b} Lemma 10.12 (#BFP.160-2) takes CMP98's Propositions 4–5 for the chain's dressed average from BP_PBG_DRESSED.md; REG's results for this average, which #BFP.160-1 lists, from BP_REG_DRESSED.md (#BFP.160-2).
  {#B9.29-3d} The statements of Lemmas 10.11–10.14 and 10.16 say that they rest on (P-PBG) (Lemma 10.15 through Lemma 10.14). The rest of §10 uses PBG only for definitions, at U = 1, through Bałaban's results for G and the H_i as #B9.29-2 says (Propositions 10.2–10.4), or through bounds this file proves.
  {#B9.29-4} For Lemma 10.16, per factor group, for M large depending on d, L and G_i, and on these domains with T^{(k)} of side at least 20M (20LM for configurations of scale k + 1) and O(1)LMBα₀ + α₁ + γ₀ ≤ a_R, a_R ≤ a_cx depending on d, L and G_i, RG1's C^{(k)} with the exponential gauge fixing (#B9.40-2) and the resolvents (xI + 𝒫*Δ^{(k)}𝒫)^{−1} of RG2 (2.7), 0 ≤ x ≤ γ₁ (p.013 l.25; #T10.6-2), are analytic, have (3.187) with a rate ϱ > 0 for δ₀ and expansions whose terms are taken at the G-valued factor U of RG1's (i), uniformly in x (#BX.1-5, #BX.1-5b).
  {#B9.29-4-1} At the real points (U, 0) the forms xI + 𝒫*Δ^{(k)}𝒫 are ≥ ½c_𝒞, with c_𝒞 > 0 of #B4.147-8 (#BX.1-5a, where it is written c₁).
  {#B9.29-4a} For comparison, Bałaban prints of these complex extensions: with PBG's averages, Theorem 3.4 for G′, (Q′G′²Q′*)^{−1}, R and G₀ (PBG's G, #T12.24) (p.400 l.7–10) and VAR's operators (VAR p.309 l.2–3).
  {#B9.29-4a-1} For the chain it prints RG2 §1's operators H₀ and G̃ of (1.2) and (1.4), which RG2 takes "By the results of Sect. G [15]" (p.002 l.25–43). They are VAR's H₀ and G̃ of (179)–(180), p.306 l.30 and l.40, with H₀B = GQ*(QGQ*)^{−1}(L^jη)^{−1}B (p.297 l.37) and G̃ = G − GQ*(QGQ*)^{−1}QG (p.300 l.10), where for (180) VAR takes the new G = (Δ_a − Δ^{(2)})^{−1} (p.306 l.37–38).
  {#B9.29-4a-2} It prints also their bounds, uniform on I.(i)–(iii) (RG2 p.006 l.44–45), the analyticity of C^{(k)} and its forms (RG2 p.015 l.4–5), and C^{(k)}'s definition (RG1 p.268 l.2–3) and expansion (RG2 p.013 l.19–35).
  {#B9.30} Propositions 4.2 and 5.3 use them at U = 1, with C^{(k)}(1), whose gauge-fixing term is exponential, bounded in #B4.147-1–#B4.147-9;
  {#B9.31} Proposition 7.1(c) derives what it needs from U = 1 (§0, input 4); and the realness in Proposition 2.12 (#B2.2.580–#B2.2.587) uses only that the chain's operators are real at real arguments.
  {#B9.31-1} For comparison,
  {#B9.32} Bałaban applies PBG's results to the chain (#B0.37-0):
  {#B9.33} RG1 p.261 (the operators H_{1,j}, Δ₁, "defined in Sect. D [13]", l.10, and the analyticity "from results of that paper" under PBG
  {#B9.34} (3.35)–(3.38)); RG1 pp.266–267 (PBG (3.127)–(3.128) and (3.156)); RG2 p.3 (the expansion PBG (3.107)–(3.108),
  {#B9.35} whose bound "holds for all operator norms in formulations of theorems in [13]"); RG2 p.5 ("in all norms of Theorems
  {#B9.36} 3.1.-3.10 [13]"); RG2 p.13 (random walk expansions "discussed in [13] for all operators determining Δ_k, and for
  {#B9.37} C^{(k)}(Z_0)", with PBG (3.185)); and CRE p.276 ("we apply Theorems 3.7–3.10 [13] in their full generality").
  {#B9.38} These applications do not print PBG's results for the operators of §7's dressed average, at G-valued U ≠ 1
  {#B9.39} or at the complex backgrounds of RG1's domains; how the file takes them instead is #B9.29-1–#B9.29-4.
  {#B9.40} They name operator norms of [13]'s theorems, Theorems 3.1–3.10, Theorems 3.7–3.10, and [13]'s construction for the operators determining Δ^{(k)} (RG2's Δ_k) and for C^{(k)}(Z_0), with (3.185) modified by G̃_3(x) for the resolvent (RG2 p.13 l.19, l.31–33); Bałaban's papers do not re-run PBG's proofs for RG1's average; and the dressing is defined only here (#B9.40-3d).
    {#B9.40-1} PBG states Thms 3.12, 3.15, and (3.132) for real U (pp.423, 432, 422). What Bałaban prints of their complex form is listed in #B9.29-4a–#B9.29-4a-2 (also RG1 p.261 l.20–21). PBG p.393 l.15 states that its definitions of the averages (3.13)–(3.15) "extend straightforwardly to configurations U, A with values in the complexified group G^c".
    {#B9.40-2} The C^{(k)} of RG1 p.268 and RG2 p.013 has the exponential gauge-fixing term. PBG states its decay for the δ-function form and real U ((3.187) with Thm 3.15, p.432). The uses of the chain's C^{(k)} are #B0.37-1–#B0.37-2, #B9.29-4 and #B9.30.
    {#B9.40-3} RG1 takes H_{1,j} and Δ₁ from PBG's Sect. D ("defined in Sect. D [13]", RG1 p.261 l.10), with PBG (3.127)–(3.128) (RG1 p.266 l.39), and Δ^{(k)} from PBG (3.156) (RG1 p.267 l.38), which is in PBG's Sect. E (p.427 l.23). Their averaging is CMP98's dressed average (89)–(92) (PBG p.392 l.45–46), here for RG1's average.
    {#B9.40-3-1} RG1 p.254 l.7–8 states CMP98's results for (0.12) ("all results of the paper [12] are valid for it"), which l.9 calls "equally good" as (0.4); for (0.4) no page states them explicitly, though l.7 presupposes them and p.252 l.38–39 calls (0.4) "the simplest, immediate extension of the definition of averages in [12]".
    {#B9.40-3a} CMP98's dressing contours are those of its axial gauge conditions (58), p.27, (R_{0,y}V′)(Γ_{y,x}) = 1: the dressing factor v(y) of (62)–(63), p.28, is "determined uniquely by the gauge conditions (58)" and (61).
    {#B9.40-3b} RG1 replaces the contour variables of the axial gauge fixing by U(y, x) of (0.11) (RG1 p.253 l.12–13; p.254 l.25–26: "we have to use other expressions than the contour variables U(Γ_{y,x}). We use the variables U(y, x)").
    {#B9.40-3c} RG1 uses a dressed average for the chain without defining its dressing factors: RG1 (3.3), p.270 l.27–32 ("the equality (97) [12]", l.32), and (3.39), p.278 l.17–24 ("Using (97) [12]", l.17), apply CMP98 (97), Ũ₁^j = (\bar{\bar U}₁^j)^{v_j}, as a nonlinear identity: the Q_j of (3.3), in exp iQ_j(η𝐇_k(B′)) (p.270 l.28), is PBG's Q_j(U, ηA) = (1/i)log of the dressed j-step average (PBG (3.13), p.392 l.49). RG1 p.265 l.40–41 also applies CMP98 (106) to the chain, expressing the gauge transformation u_k through 𝐇_k(B′) "by the formula (106) in [12] with U₁ = exp iη𝐇_k".
    {#B9.40-3d} This file supplies the definition: the dressing factors of PBG (3.113) with the variables (0.11) that replace the axial contours (#B9.40-3b). This is the dressed average of §7's Setting (#B7.12-1–#B7.14), and its covariance QD = D̄Q′ and Q(1) = Q_k are proved there (#B7.15–#B7.27-1).
    {#B9.40-3e} CMP98 (97) holds for it: CMP98's proof, (93)–(98), p.32, uses the recursion (68), the definitions (89) and (91), and "the other definitions" (p.032 l.8, l.14, l.36, l.47), in which the dressing factors of (89) (there the averages of R_{0,c±}V₁, here those of #B9.40-3d) enter only algebraically, and the gauge covariance (93) of the undressed average.
    {#B9.40-3e-1} CMP98 (106), derived in (101)–(105) from (97), (99) and the axial-gauge formulas (77) and (87) for u (p.032 l.65–p.033 l.44), holds for the chain with the variables (0.11) by balaban_proofs/BP_REG_DRESSED.md (#BR.4-1–#BR.4-2), not yet through review.
    {#B9.40-3f} (93) holds for RG1 (0.4), since each logarithm in (0.4) is of a loop closed at c₋ (RG1 p.253 l.5–6), so a gauge transformation u multiplies M(𝐔, c) by u(c₋) on the left and u(c₊)^{−1} on the right. It holds for (0.12) because the variables (0.11) are covariant by (0.6) (l.20) (§3.1).
- {#B9.41} VAR Thm 1 uses REG's Theorem 8, which REG sketches (p.101 l.2–10: "Inspecting the proofs … almost without any changes"), only in its step off the Landau slice, VAR p.297 l.9–13, repeated at p.302 l.30: there VAR solves VAR (125), REG Sect. D with f on the right, to show that its critical configuration is critical without the Landau condition (`D:\University\Oxford PostDoc\Balaban\BALABAN_DEPENDENCE_TREE.md`, D3).
  {#B9.42} That conclusion follows from REG's Proposition 5 at f = 0, gauge invariance and the surjectivity of RD* along the gauge directions, proved in balaban_proofs/BP_REG_DRESSED.md (#BR.13a–#BR.13a-7, #BR.1-2), not yet through review, for CMP98's averages and for the chain's.
  {#B9.42-1} Where it enters: §0, input 5 (#B0.42).
- {#B9.44} VAR was written for the averaging of CMP98.
  {#B9.44-1} RG1 states VAR Thm 1's unique regular minimal orbit for its own M^k
  {#B9.45} (RG1 (1.1), p.260, "see Theorem 1 there"; RG1 (0.21), p.256), and it applies VAR Prop. 9 (p.309: U_k(V) analytic
  {#B9.46} in B = (1/i)log V′) to U_n(M^·(𝐔)) on complex configurations (RG1 (1.17), p.263), and VAR Prop. 9 with (190) to
  {#B9.47} the derivative δ𝐇_j/δB (RG1 p.271 l.33).
  {#B9.47-1} Apart from LFR2's functions built from VAR's results, which enter with
  {#B9.48} LFR2 (the tube-construction bullet below), §§2–8 use VAR for the chain averaging with RG1 (0.4) or (0.12) only through
  {#B9.49} these statements: Proposition 5.3, step 1 (the orbit and analyticity in t), the analyticity of the background in
  {#B9.50} §5, Proposition 7.1's gauge paragraph (#B7.47-5: the gauge transformation u of VAR p.281 l.2–3 and the unique orbit of VAR p.279 l.15), Proposition 7.1(c) (the Landau gauge of VAR Prop. 9), Lemma 2.5, step 1 (VAR (190)), and Proposition 2.12(b)
  {#B9.51} (VAR Prop. 9 and (190) at every admissible real B⁰).
  {#B9.51-1} §10 uses VAR Theorem 1 with (2) and (8) for RG1's minimal configuration (Lemma 10.7, #B10.119, #B10.124), VAR (8), (9), (14) and (28) (Lemma 10.14(a), #B10.178; #BFR.211-2a), and VAR §§A–G re-run for the chain's dressed average (Lemma 10.12, #B10.159-1 and BP_FAMILY_PBG_VAR.md #BFP.160–#BFP.167).
- {#B9.52} VAR (189): §0, input 1 (#B0.32), with RG1 Theorem 3's use of (190) at p.271 l.33 (#B9.46–#B9.47).
- {#B9.53} From RG1 Theorem 3 with RG2 Lemmas 1–3 and RG2 (2.41): the bound RG1 (1.18) and the analyticity of the step terms in
  {#B9.54} (U, J) on RG1's fixed domains, for §§2.1–2.2, as printed or with the changes that #B0.37-3 lists, among them RG2's cube count replaced by #BK.1 of balaban_proofs/BP_RG2_CUBE_COUNT.md, not yet through review (#B2.1.49-1).
- {#B9.55} For the tube construction: CRE's inductive estimates as printed, in particular CRE (2.30)–(2.31), p.260, (2.44) and
  {#B9.56} (2.46), p.263, and the statement that the step output satisfies the inductive assumption (CRE p.279), and the
  {#B9.57} estimates of LFR1 and LFR2, including LFR2 (1.79)–(1.80), pp.383–384, and of UV3, CMP98, REG, and VAR as CRE uses
  {#B9.58} them.
- {#B9.59} Inputs whose printed form needs an argument, given here and checked against the print:
  - {#B9.60} The B-set {B : |B| < ε₁g_k^{−1} on Y} of RG2 (1.34), p.9, can be taken as the complex polydisc, with (1.34) read as in #BH.2-1: the functions V′_k and V_k of RG2 Lemmas 1–2, with (1.36) and (1.42)–(1.43), are jointly holomorphic in (𝐔, 𝐉, B) for g^c-valued B there, for α₀, α₁ and ε₁ small with the conditions of #BH.1 (used in Proposition 2.6, step 2, and Lemma 2.7, steps 1–2), and the action terms are holomorphic in a complex coupling z in place of g_k, with z^{−2} for g_k^{−2}, on |z||B| < ε₁, also at z = 0, with the same bounds (#BH.1-1, #BH.1-2; used in Lemma 2.7, step 2).
    {#B9.60-1} The identities (1.33) and (1.41) are used at real B only (#B2.2.8-1).
    {#B9.61} The proof, which follows RG2 pp.3–11 and checks that each map there is holomorphic in complex B, is balaban_proofs/BP_RG2_COMPLEX_B.md (#BH.1–#BH.6-5-2b), not yet through review.
  - {#B9.62} The threshold on the unit-scale fluctuation A_k at step k is g_k^{−1}δ_k = A₁(log g_k^{−2})^{p₀} (#B0.5, #T10.2).
    {#B9.62-1} Bałaban prints this form twice: CRE (1.18), p.250, has χ({sup|A(b)| < g₀^{−1}δ₀}) at step 0, and (1.19) multiplies it by the factor with exp ig₀A(b).
    {#B9.62-1a} LFR1 (1.9), p.178, writes out CRE's one-step operations ("the formula (2.21) [III]") and has χ({sup|A_j(b)| < g_j^{−1}δ_j}), beside (1.8)'s exp ig_jA_j(b).
    {#B9.62-1b} CRE (3.16), p.268, prints χ({sup|A_k(b)| < δ_k}) for the same field: A_k is unit scale there, since it enters (3.15) as g_kCA_k after the scaling A′_k = g_kA_k (CRE p.267). The factor g_k^{−1} is missing in (3.16), and this file uses the form of (1.18) and LFR1 (1.9) (§0, *Input 3*).
    {#B9.62-2} The neighbouring prints agree with g_k^{−1}δ_k: CRE (3.3), p.265, puts 2δ_k on the field-scale |V_k(V^{(k)}_{□′})^{−1} − 1|, and LFR2's factor exp(−γ₀g_j^{−2}δ_j²(LM₂R_j)^{−d}|R_j|) from χ^{(j−1)c}(R_j) (p.380 l.43–45) carries δ_j/g_j.
  - {#B9.63} LFR1 p.198 and LFR2 p.363 use two different exponents ν, and with N = R_j both conditions hold for small g
    {#B9.64} (*CRE's Construction as a Function of the History*; Lemma 2.10, step 4).
    {#B9.64-1} LFR1's ν satisfies ½ν ≤ p₀ − p₁ − 1, and LFR2's needs ν ≥ 2p₀ + dr₀. As one number they would give 2p₁ + 2 + dr₀ ≤ 0, while 2p₁ > p₀ + (d+5)r₀ > 0 (LFR2 p.383).
- {#B9.72} RG2's sketches on p.11 l.5 and p.9 l.28 (§0, input 2, #B0.33).

{#B9.109} **Lean cores.** The type-checked Lean cores named above (`BalabanFormal.flow_lemma`,
{#B9.110} `BalabanFormal.coupling_flow_of_stepBound`, `BalabanFormal.symbol_holder_bound`,
{#B9.111} `BalabanFormal.jterm_holder`, `BalabanFormal.jterm_assembly`, `BalabanFormal.bare_assembly`, `BalabanFormal.SmoothNum.lemma61`, and
{#B9.112} `BalabanFormal.angular_coefficient`) are abstract statements.
{#B9.112-1} The hypotheses of `symbol_holder_bound` and `jterm_holder` are
{#B9.113} those stated in Lemma 4.1 (b) and Proposition 4.2 (#B4.6, #B4.12, #B4.238-2–#B4.240).
{#B9.113-1} Those of `jterm_assembly` are 1 < L, 0 < α, C_J ≥ 0, A ≥ 0, the splitting of Π_{𝒥_k} into the step terms, the bound `hunits` with the factor (L^{k−m})^{−2α} (#B5.120), and the alias bound `halias` (Proposition 5.3, step 4).
{#B9.113-2} Those of `coupling_flow_of_stepBound` are Poincaré–Miranda for the set of simple factors (proved for one factor by `BalabanFormal.poincareMiranda_of_unique`), a `BalabanInputs` for each factor, all with the same L (`hLeq`), a step bound giving (P2) with its smallness against 2c ln L, the continuity (C) (Remark 2.3), and the constants and target of the flow.
{#B9.113-2-1} The Proposition 5.3 fields of `BalabanInputs` are α with 0 < α (`hα0`) and 2α < 1 (`hα1`), the data `J`, `modes`, `ρJ` and `wJ`, the constants `CJ` ≥ 0 and `AJ` ≥ 0 (`hCJ`, `hAJ`), the splitting `jsplit` of Π_{𝒥_k} into the step terms, `junits` with #B9.113-1's factor (L^{k−m})^{−2α}, and `jalias`.
{#B9.114} Those of the other four are listed in `D:\University\Oxford PostDoc\Balaban\sidecar\BalabanSidecar\Instantiation.lean`, whose entries for `jterm_assembly` and `coupling_flow_of_stepBound` are those of the `balaban` versions, with the factor (L^{k−m})^{−2} and a zone hypothesis.
{#B9.114-0} The Lean modules give ℝ⁴ and ℂ⁴ the sup norm (`Mom` and `Vec` in SecondOrder.lean), within a factor 2 of the Euclidean norm, so a hypothesis or conclusion stated here changes into the Lean one by an absolute factor in its constant.
{#B9.114-1} They check the finite algebra and
{#B9.115} analysis of the steps that cite them.
{#B9.115-1} Each of those steps also has its proof written out here.

{#B9.116} The Lean modules of these cores are in the standalone project
{#B9.117} `C:\Users\marti\Documents\Scientia\Mathematics\Lean\Projects\ym_beta_function` (28 modules of namespace `BalabanFormal`,
{#B9.118} importing only each other and Mathlib; `lake build` there, and `#print axioms` of each name above gives propext,
{#B9.119} Classical.choice and Quot.sound only).
{#B9.119-1} The modules SecondOrder, L3, Assembly, Inputs, and Examples carry the Hölder
{#B9.120} forms of Lemma 4.1(b) and Propositions 4.2 and 5.3.
{#B9.120-1} The other modules are verbatim copies of the modules of the same
{#B9.121} names in `C:\Users\marti\Documents\Scientia\Mathematics\Lean\Projects\balaban`, which the Bałaban sidecar's gates check; of these, P2C.lean imports the Hölder Inputs.lean, so its `coupling_flow_of_stepBound` is over the Hölder `BalabanInputs`.

## 10. Semisimple G {#BS10}

{#B10.1} Let G ⊂ U(N) be compact, connected, and semisimple, with Lie algebra g = g_1 ⊕ ⋯ ⊕ g_r (simple ideals).
{#B10.1-1} RG1 states its
{#B10.2} construction and Theorem 1 for this case (p.251 l.30–p.252 l.2, p.259 l.23–24), with one coupling; a step that needs
{#B10.3} r = 1 is the inference of "proportional to δ^{ab}" from Ad(G)-invariance on p.264 l.11–12 (Lemma 10.1; under a symmetry, Proposition 10.4 gives the conclusion).

{#B10.4} **Lemma 10.1.** Every Ad(G)-invariant bilinear form on g, real or complex valued, has the form Σ_i ϑ_i K_i (ϑ_i real or complex), where K_i is the Killing form
{#B10.5} of g_i, taken as in Lemma 1.1.
{#B10.5-1} In particular the trace form of G ⊂ U(N) is Σ_i (κ_i^N)^{−1} K_i, with κ_i^N > 0 defined by K_i = κ_i^N·tr on
{#B10.6} g_i.

{#B10.7} *Proof.* Let β be invariant and i ≠ j, and let G_i^∘ be the connected subgroup of G with Lie algebra g_i.
{#B10.7-1} For fixed
{#B10.8} Y ∈ g_j, each of the functionals X ↦ β(X, Y) and X ↦ β(Y, X) on g_i is invariant under Ad(G_i^∘) (G_i^∘ acts trivially on g_j), hence zero, since a simple g_i has no nonzero invariant vectors.
{#B10.8-1} Each Ad(g), g ∈ G, preserves g_i (G is connected, and Ad(exp X) = e^{ad X} preserves ideals), and Ad(G) acts irreducibly on g_i and on g_i ⊗ ℂ, since an invariant subspace is an ideal of the compact simple g_i or of its simple complexification; so the proof of Lemma 1.1, with g_i in place of g,
{#B10.9} gives β|_{g_i} = ϑ_i K_i. ∎

{#B10.10} **Proposition 10.2 (Additive Actions Reduce to Simple Factors).** Let ρ_i: G → U(N_i), i = 1, …, r, be unitary
{#B10.11} representations with dρ_i injective on g_i and zero on g_j for j ≠ i, and let the bare action be
{#B10.12} S(U) = Σ_i g_{0,i}^{−2}A_i(ρ_i(U)), where A_i is the Wilson action RG1 (0.2) of U(N_i).
{#B10.12-1} Put H_i := ρ_i(G),
{#B10.13} G_× := H_1 × ⋯ × H_r, and Φ := (ρ_1, …, ρ_r): G → G_×. Then:
- {#B10.14} (a) Φ is onto, with finite central kernel Z, each H_i ⊂ U(N_i) is compact with simple Lie algebra dρ_i(g_i), and
  {#B10.15} Φ_*μ_G = ⊗_iμ_{H_i} (μ the normalised Haar measures).
- {#B10.16} (b) For bounded measurable F on G_×^E (E the bonds of the torus), ∫ F(Φ(U))e^{−S(U)}dμ_G^E(U) = ∫ F(V)∏_ie^{−g_{0,i}^{−2}A_i(V_i)}dμ_{G_×}^E(V), and for F = ∏_iF_i(V_i)
  {#B10.17} the right side is the product of the factors' integrals.
  {#B10.17-1} For bounded measurable F on G^E, let PF(U) be the average
  {#B10.18} of F(zU) over z ∈ Z^E ((zU)_b := z_bU_b), with the uniform measure.
  {#B10.18-1} Then PF = F̃∘Φ^E for a bounded measurable F̃ on
  {#B10.19} G_×^E, and ⟨F⟩_G = ⟨F̃⟩_{G_×}, the expectation of the product theory on G_×.
- {#B10.20} (c) Let σ be an irreducible representation of G and C a loop.
  {#B10.20-1} If σ is trivial on Z, then σ = (σ_1 ⊗ ⋯ ⊗ σ_r)∘Φ with
  {#B10.21} σ_i irreducible on H_i, and ⟨tr σ(U(C))⟩_G = ∏_i⟨tr σ_i(V_i(C))⟩_{H_i}.
  {#B10.21-1} If σ(z) ≠ 1 for some z ∈ Z and C traverses
  {#B10.22} some bond exactly once, then ⟨tr σ(U(C))⟩_G = 0.
- {#B10.23} (d) For a target (K, g^{(1)}, …, g^{(r)}) with g^{(i)} ∈ (0, γ_i′], run on each H_i ⊂ U(N_i) the tube construction of
  {#B10.24} §0 for the target (K, g^{(i)}), and take the product.
  {#B10.24-1} Then for each i there is a bare coupling g_{0,i}(ε, g^{(i)}),
  {#B10.25} independent of the torus and of the other targets, with g_{K,i} = g^{(i)} and g_{k,i} ∈ (0, γ_i] for 0 ≤ k ≤ K, whose
  {#B10.26} flow satisfies what §0 (after the list of inputs) states for the tube construction of H_i: item 1, items 3 and 4 along the
  {#B10.27} matched flow with δ′_i in place of δ_i, δ′_i being §0's tube constant δ′ = C_ΛC₃γp₀(γ) + C_Rγ^{κ₀−4} (#B0.63-1) for H_i, and item 5 with C_rem,i + C_Rγ_i^{κ₀−6} in place of
  {#B10.28} C_rem,i.
  {#B10.28-1} Here γ_i, γ_i′, C_i, δ_i, C_rem,i, and c_i = (11/48π²)κ_i are the constants of Theorem 0.1 for H_i, with
  {#B10.29} K_i = κ_i·tr on dρ_i(g_i) ⊂ u(N_i) (tr the normalised trace of U(N_i)); for the Wilson action of a defining representation (*Which actions are
  {#B10.30} additive*), κ_i^N = (N/N_i)κ_i.

{#B10.31} *Proof.*
1. {#B10.32} *Covering.* dΦ = ⊕_idρ_i is injective, because on g_j only the component dρ_j is nonzero and it is injective there;
   {#B10.33} and Lie(H_i) = dρ_i(g) = dρ_i(g_i), so dΦ is onto ⊕_iLie(H_i).
   {#B10.33-1} Hence Φ(G) contains a neighbourhood of 1 in G_×, so it
   {#B10.34} is an open, hence closed, subgroup of the connected group G_×, and equals G_×. Z = ker Φ is closed with Lie algebra
   {#B10.35} ker dΦ = 0, so discrete and, being compact, finite; it is central, because for z ∈ Z the map g ↦ gzg^{−1} is a
   {#B10.36} continuous map from the connected G into the discrete Z.
2. {#B10.37} *Haar measure.* Φ_*μ_G is a probability measure on G_×, invariant under left translation by every Φ(g), that is, by
   {#B10.38} every element of G_×; by uniqueness, Φ_*μ_G = μ_{G_×} = ⊗_iμ_{H_i}.
3. {#B10.39} *Action.* Φ is a homomorphism, so ρ_i(U)(∂p) = ρ_i(U(∂p)) and S(U) = Σ_ig_{0,i}^{−2}A_i(Φ(U)_i).
   {#B10.39-1} This and 2 give the
   {#B10.40} integral identity of (b); the product form is Fubini.
   {#B10.40-1} For the average: Φ is a surjective homomorphism of Lie groups
   {#B10.41} with finite kernel, so Φ^E: G^E → G_×^E is a finite covering map, whose fibres are the cosets Z^EU (Φ(U′_b) = Φ(U_b)
   {#B10.42} if and only if U′_bU_b^{−1} ∈ Z).
   {#B10.42-1} PF is constant on them, so PF = F̃∘Φ^E, with F̃ Borel because Φ^E has local
   {#B10.43} continuous sections.
   {#B10.43-1} For each z ∈ Z^E the substitution U ↦ zU preserves μ_G^E (a translation) and S (Φ(zU) = Φ(U)),
   {#B10.44} so ⟨F⟩_G = ⟨F(z·)⟩_G; averaging over z gives ⟨F⟩_G = ⟨PF⟩_G, and the integral identity, with F̃ and with 1, gives
   {#B10.45} ⟨PF⟩_G = ⟨F̃⟩_{G_×}.
4. {#B10.46} *Representations.* σ(z) is a scalar ω(z) for z ∈ Z (Schur).
   {#B10.46-1} If ω ≡ 1, σ factors through G/Z ≅ G_×. An irreducible
   {#B10.47} representation of H_1 × H′ is τ_1 ⊗ M: H′ commutes with H_1, so it preserves the H_1-isotypic components, and
   {#B10.48} irreducibility leaves one, τ_1 ⊗ M with M = Hom_{H_1}(τ_1, σ), on which H′ acts irreducibly (an invariant M′ ⊂ M
   {#B10.49} gives the invariant τ_1 ⊗ M′).
   {#B10.49-1} By induction σ ≅ σ_1 ⊗ ⋯ ⊗ σ_r, normalised traces multiply, and (b) gives the
   {#B10.50} product of expectations, since numerator and normaliser both factor.
   {#B10.50-1} If ω(z) ≠ 1 and C traverses b exactly once,
   {#B10.51} the substitution U_b ↦ zU_b preserves μ_G and S (Φ(z) = 1) and multiplies tr σ(U(C)) by ω(z)^{±1}, the sign being
   {#B10.52} the direction in which C traverses b, z being central; since ω(z)^{±1} ≠ 1, the expectation vanishes.
5. {#B10.53} *Flow.* By (b) with F = 1, the partition function of G is that of G_×, whose action is a sum over factors with
   {#B10.54} independent integration variables.
   {#B10.54-1} The product construction is therefore the tube construction of §0 run
   {#B10.55} separately on each H_i: the RG kernels multiply, the effective action at each step is the sum of the factors'
   {#B10.56} effective actions, and the flow of factor i involves only factor i's couplings and target.
   {#B10.56-1} Each H_i ⊂ U(N_i) is
   {#B10.57} a closed subgroup of U(N_i) (the setting of RG1 p.252 l.2), compact and connected (the image of G), with a simple Lie algebra and the Wilson action of its defining representation, so Theorem 0.1 applies to
   {#B10.58} it, in the form §0 gives for the tube construction. ∎

{#B10.59} The construction in (d) is defined on G_×. It is not RG1's construction on G with one coupling.
{#B10.59-1} The effective couplings
{#B10.60} are not observables, and by (b) every expectation of the G theory is an expectation of the product theory on G_×.

{#B10.61} *Which actions are additive.* Let G ⊂ U(N) carry the Wilson action of its defining representation ρ.
{#B10.61-1} If every
{#B10.62} irreducible summand of ρ is nontrivial on at most one factor, the action is additive with ρ_i the sum of the summands
{#B10.63} nontrivial on factor i, and g_{0,i}^{−2} = (N_i/N)g_0^{−2}: with N_triv the dimension of the trivial summands,
{#B10.64} 1 − Re tr ρ(V) = Σ_i(N_i/N)[1 − Re tr ρ_i(V)], because Σ_iN_i + N_triv = N. dρ_i is injective on g_i, because
{#B10.65} dρ|_{g_i} is dρ_i|_{g_i} plus zero blocks and dρ is injective.
{#B10.65-1} If some summand is nontrivial on two factors, the action is not additive, because irreducible
{#B10.66} characters of the simply connected cover ∏_iG̃_i (G̃_i the simply connected group with Lie algebra g_i) are linearly
{#B10.67} independent.
{#B10.67-1} Examples: SU(2) × SU(3) ⊂ U(5) acting
{#B10.68} block-diagonally is additive.
{#B10.68-1} SO(4) ⊂ U(4) is not additive, because its vector representation is the tensor product
{#B10.69} of the spin-½ representations of the two SU(2) factors.
{#B10.69-1} The adjoint Wilson actions ρ_i = Ad|_{g_i} give an additive
{#B10.70} action on every G. One bare coupling with fixed weights w_i does not match all factors when the ratios c_i/w_i differ,
{#B10.71} with c_i as in (d), because the factors run at the rates 2c_i ln L (item 1); for a defining representation,
{#B10.72} c_i/w_i = (11/48π²)κ_i^N, so the condition is that the κ_i^N differ (for SU(2) × SU(3) ⊂ U(5), κ_i^N = 20 and 30).
{#B10.72-1} Proposition 10.2(d) therefore takes one bare coupling per
{#B10.73} factor; Proposition 10.3 treats one bare coupling, which matches one factor of the largest rate c_i/w_i.

{#B10.73-1} **Proposition 10.3 (One Bare Coupling, Additive Actions).** In the setting of Proposition 10.2, let g_{0,i}^{−2} = w_ig_0^{−2}, with one bare coupling g_0 and fixed weights w_i > 0 (for the Wilson action of a defining representation, w_i = N_i/N, *Which actions are additive*). Let c_i, γ_i, γ_i′, and δ′_i be the constants of Proposition 10.2(d) for H_i, C_{0,i} the bound of Theorem 8.1 on the window sums for H_i (C₀ of Remark 2.3, 2C in #B8.4), μ := max_i c_i/w_i, and I := {i : c_i/w_i = μ}; fix i₁ ∈ I.
{#B10.73-2} Put θ_i := 2 ln L·(w_iμ − c_i), which is positive for i ∉ I, and C_i^I := max_{i′∈I}(w_i/w_{i′})C_{0,i′}. If the γ_i are small, there is γ_* > 0 such that for every K and every g ∈ (0, γ_*] there are a bare coupling g_0, independent of the torus, and an index i* ∈ I with:
- {#B10.73-3} (a) g_{K,i*}^{−2} = (w_{i*}/w_{i₁})g^{−2}, the statements of Proposition 10.2(d) for the target (K, g_{K,i*}) hold for factor i*, and every i ∈ I with a unitary W such that N_i = N_{i*} and WH_{i*}W* = H_i has the flow of factor i*;
- {#B10.73-4} (b) every factor i not covered by (a) runs the tube construction of a tube of the class (*The Class of Tubes*), with C = C_{0,i} + 2 for i ∈ I and C = δ′_iK + C_{0,i} for i ∉ I, and its flow from g_{0,i} lies in that tube's H_k for every k ≤ K; along it g_{k,i} ∈ (0, γ_i], the per-step bounds of (W) with δ′_i and item 5 with C_rem,i + C_Rγ_i^{κ₀−6} hold, and the estimates of CRE, LFR1, and LFR2 hold (Lemma 2.10); and g_{K,i}^{−2} ≥ (w_i/w_{i₁})g^{−2} − 2 for i ∈ I, g_{K,i}^{−2} ≥ (w_i/w_{i₁})g^{−2} + ½θ_iK − C_i^I − C_{0,i} for i ∉ I;
- {#B10.73-6} (c) every expectation of the G theory is the corresponding expectation of the product of these factor theories (Proposition 10.2(b)–(c)).

{#B10.73-7} *Proof.* The constants b_{k,i}, ā_{k,i}, C_a, and C_e are those of Theorem 8.1, Proposition 2.9, and Proposition 2.14 for H_i, and τ := g^{−2}/w_{i₁}.
1. {#B10.73-8} *Factors.* By Proposition 10.2(b) the G theory is the product theory on G_× with the bare couplings g_{0,i}^{−2} = w_ig_0^{−2}, and the flow of factor i depends only on g_{0,i} and on the construction run on H_i (Proposition 10.2, step 5).
2. {#B10.73-9} *The recursion.* For ξ_0 > 0 let ξ_{k+1} := ξ_k − b_{k+1,i} − ā_{k+1,i}/ξ_k. The map ξ ↦ ξ − b_{k+1,i} − ā_{k+1,i}/ξ is increasing for ξ² > C_a, so ξ_k ≥ ξ′_k for all k when ξ_0 ≥ ξ′_0 and the recursion from ξ′_0 stays above C_a^{1/2}.
   {#B10.73-10} Let a flow (x_k) have its histories in the H_k of a tube of the class for H_i, with parameter t, and let ξ start at ξ_0 = x_0. By Proposition 2.14, d_k := x_k − ξ_k satisfies d_{k+1} = d_k(1 + ā_{k+1,i}/(x_kξ_k)) − e_{k+1}. While |d_j| ≤ 1 for j ≤ k, ξ_j ≥ ℓ_j − 1 ≥ ℓ_j/2, so |d_{k+1}| ≤ exp(2C_aΣ_jℓ_j^{−2})Σ_{j≤k}|e_{j+1}|.
   {#B10.73-11} Here Σ_jℓ_j^{−2} ≤ ((7/8)t)^{−2} + ((7/8)t)^{−1}/(c_i ln L), and Σ_j|e_{j+1}| ≤ 3C_et^{−1/2}(1 + 1/(c_i ln L)) (#B2.2.862), with t ≥ γ_i^{−2}. So for γ_i small, |x_k − ξ_k| ≤ 1 for all k ≤ K.
3. {#B10.73-12} *Choice of i*.* Take γ_* so small that (w_iτ)^{−1/2} ≤ γ′_i for i ∈ I. For i ∈ I, Proposition 10.2(d) gives a bare x^m_{0,i}, independent of the torus, whose flow x^m_{k,i} for the target (K, (w_iτ)^{−1/2}) lies in the H_k of that target's tube and ends at w_iτ. Let i* ∈ I maximise x^m_{0,i}/w_i, and put g_0^{−2} := x^m_{0,i*}/w_{i*}. Then g_{0,i*}^{−2} = x^m_{0,i*}, factor i* runs the matched flow, and g_{K,i*}^{−2} = w_{i*}τ.
   {#B10.73-13} Let i ∈ I and W be as in (a). Conjugation by W carries tr and the Killing form of H_{i*} to those of H_i, so κ_i = κ_{i*} and c_i = c_{i*}; as both lie in I, w_i = w_{i*} and g_{0,i} = g_{0,i*}. The map V ↦ WVW* takes H_{i*}^E onto H_i^E, Haar measure to Haar measure, and A_{i*} to A_i; run on H_i the image of factor i*'s tube construction, whose flow is factor i*'s. This proves (a).
4. {#B10.73-14} *The other factors of I.* Let i ∈ I not be covered by (a), x_k := g_{k,i}^{−2}, and ξ, ξ^m the recursions from x_0 and x^m_{0,i}. By the choice of i*, x_0 = w_ix^m_{0,i*}/w_{i*} ≥ x^m_{0,i}. Step 2 for the matched flow, and its window x^m_{k,i} − x^m_{K,i} ≥ b(K−k) − C_{0,i} in the H_K of the target's tube (#B2.2.167), give ξ^m_k ≥ x^m_{k,i} − 1 ≥ w_iτ − C_{0,i} − 1, so ξ_k ≥ ξ^m_k for all k, and t̂ := ξ_K ≥ ξ^m_K ≥ w_iτ − 1.
   {#B10.73-15} Take the tube with target (K, t̂^{−1/2}), b := 2c_i ln L − δ′_i, b′ := 2c_i ln L + δ′_i, and C^T := C_{0,i} + 2. For γ_* small, t̂ ≥ max(γ_i^{−2} + C^T, 4C^T/β₀), and b and b′ satisfy the bounds of the class as for the tube of a target (*The Tube of a Target*), so the tube lies in the class.
   {#B10.73-16} ξ_l ≥ ξ^m_l ≥ ½w_iτ, so for γ_* small Σ_{l=m}^{n−1}|ā_{l+1,i}|/ξ_l ≤ 2C_a(n−m)/(w_iτ) ≤ δ′_i(n−m), and with Theorem 8.1, ξ_m − ξ_n ∈ [b(n−m) − C_{0,i}, b′(n−m) + C_{0,i}] for 0 ≤ m < n ≤ K; with n = K, ξ_m ∈ [t̂ + b(K−m) − C_{0,i}, t̂ + b′(K−m) + C_{0,i}].
   {#B10.73-17} x_0 = ξ_0 lies in T_0. If (x_0, …, x_k) ∈ H_k, k < K, step 2 bounds |x_j − ξ_j| ≤ 1 for j ≤ k + 1, since it uses e_{j+1} only at histories in H_j, j ≤ k; with the windows of ξ, x_m − x_n ∈ [b(n−m) − C^T, b′(n−m) + C^T] and x_j ∈ T_j, so (x_0, …, x_{k+1}) ∈ H_{k+1}.
   {#B10.73-18} Along the flow x_k ≥ ℓ_k ≥ γ_i^{−2}; the per-step bounds and item 5 are the *Consequence* after Proposition 2.11, the estimates of CRE, LFR1, and LFR2 are Lemma 2.10, and x_K ≥ t̂ − 1 ≥ w_iτ − 2, the bound of (b).
5. {#B10.73-19} *The tube of a slow factor.* Let i ∉ I and x_k := g_{k,i}^{−2}. Proposition 2.13 gives x_{0,i*} ≥ w_{i*}τ + (2c_{i*} ln L − δ′_{i*})K − C_{0,i*}, and c_{i*} = μw_{i*}, so t_i := x_0 − 2c_iK ln L = (w_i/w_{i*})x_{0,i*} − 2c_iK ln L ≥ w_iτ − C_i^I + (θ_i − (w_i/w_{i*})δ′_{i*})K.
   {#B10.73-20} Take the tube with target (K, t_i^{−1/2}), b := 2c_i ln L − δ′_i, b′ := 2c_i ln L + δ′_i, and C^T := δ′_iK + C_{0,i}. Take the γ's so small that max_{i′∈I}(w_i/w_{i′})δ′_{i′} + (4/β₀ + 1)δ′_i ≤ ½θ_i (δ′ → 0 as γ → 0), and γ_* so small that w_iγ_*^{−2}/w_{i₁} − C_i^I ≥ (4/β₀ + 1)C_{0,i} + γ_i^{−2}.
   {#B10.73-21} Then t_i ≥ (4/β₀)C^T + γ_i^{−2} + C^T, so t_i ≥ max(γ_i^{−2} + C^T, 4C^T/β₀); b and b′ satisfy the bounds of the class as for the tube of a target. So the tube lies in the class.
   {#B10.73-22} x_0 = t_i + 2c_i ln L·K lies in T_0. Let (x_0, …, x_k) ∈ H_k with k < K. By the *Consequence*, |β^T_{j+1} − b_{j+1}| ≤ δ′_i at the histories (x_0, …, x_j) ∈ H_j, j ≤ k, and Theorem 8.1 for H_i gives |Σ_{j=m}^{n−1}b_{j+1} − 2c_i(n−m) ln L| ≤ C_{0,i}.
   {#B10.73-23} So for 0 ≤ m < n ≤ k + 1, x_m − x_n lies in [b(n−m) − C_{0,i}, b′(n−m) + C_{0,i}], and with m = 0, x_n lies within δ′_in + C_{0,i} ≤ δ′_i(K−n) + C^T of t_i + 2c_i ln L(K−n), the centre of T_n. As C_{0,i} ≤ C^T, (x_0, …, x_{k+1}) ∈ H_{k+1}.
   {#B10.73-24} Along the flow x_k ≥ ℓ_k ≥ t_i − C^T ≥ γ_i^{−2}; the per-step bounds and item 5 are the *Consequence*, and the estimates of CRE, LFR1, and LFR2 are Lemma 2.10. With n = K, x_K ≥ t_i − δ′_iK − C_{0,i}, which with the bound on t_i gives the bound of (b).
6. {#B10.73-25} *Expectations.* (c) is Proposition 10.2(b)–(c). ∎

{#B10.74} The rest of this section concerns RG1's construction run directly on G, as needed for non-additive actions.

{#B10.75} **What carries over.**
- {#B10.76} The vacuum polarisation of RG1 (1.20) is block-diagonal: on g_i ⊗ g_i it is a multiple of the trace form, and the
  {#B10.77} blocks g_i ⊗ g_j (i ≠ j) vanish.
  {#B10.77-1} RG1's inference of "proportional to δ^{ab}" from Ad(G)-invariance alone (p.264 l.11–12) holds only for r = 1; under the symmetry of Proposition 10.4 the conclusion holds for r ≥ 2.
- {#B10.78} The marginal terms, the quadratic terms of RG1 (1.21), p.264 l.16, and (4.33), p.289 l.30–32, are given by an Ad(G)-invariant form on g, so by Lemma 10.1 by Σ_iϑ_iK_i: a combination of the quadratic parts of the per-factor actions Ã_i of Lemma 10.5 (#B10.116), whose quadratic part on g_i is ½tr = ½(κ_i^N)^{−1}K_i, and there is no invariant marginal cross
  {#B10.79} term.
  {#B10.79-1} So there is one coupling and one β per simple factor, and the flow RG1 (0.20) becomes
  {#B10.80} 1/g_{k,i}² = 1/g_{k+1,i}² + β_{k+1,i}(g_0, …, g_k), i = 1, …, r, where g_j = (g_{j,1}, …, g_{j,r}) and the β's depend
  {#B10.81} on the whole vector history.
  {#B10.81-1} The bare action g_0^{−2}A gives g_{0,i}^{−2} = w_ig_0^{−2}, with w_i = N_i/N for the A_i of Proposition 10.2 in the additive case (*Which actions are additive*), and w_i = 1 for the Ã_i, since A = Σ_iÃ_i + C (#B10.116).
- {#B10.82} For additive actions §§3–8 hold per factor, through the product construction of Proposition 10.2, with factor i's rate c_i = (11/48π²)κ_i in its coupling g_{k,i} (#B10.28-1), so that for a defining representation w_i^{−1}g_{k,i}^{−2} runs at c_i/w_i = (11/48π²)κ_i^N, in Lemma 10.1's normalisation (#B10.72); under the symmetry of Proposition 10.4 they hold with one coupling and c = (11/48π²)κ.
  {#B10.83} For a coupling vector and a non-additive action without such a symmetry they are part of the open item #B10.93, as the cross term C of the action (Lemma 10.5) couples the factors at a nontrivial background (#B10.147-1, #B10.131-1).
- {#B10.84} With r independent bare couplings g_{0,i} in place of w_ig_0^{−2}, the flow lemma holds for the coupling vector when (C) and (W) hold per factor: there are 0 < b_i ≤ b_i′ and C′ with b_i(n − m) − C′ ≤ Σ_{j=m}^{n−1}β_{j+1,i} ≤ b_i′(n − m) + C′ for all 0 ≤ m ≤ n, all i, and all vector histories with g_{j,i} ∈ (0, γ] (RG1 (0.31) per factor; Lean core #B2.12–#B2.13).
  {#B10.84-1} Clamp each component
  {#B10.85} as in Lemma 2.1, write f_{K,i}(x_0) for the i-th component at step K of the clamped map of x_0 = (x_{0,1}, …, x_{0,r}) (#B2.15–#B2.16), and take the box Π_i [(g^{(i)})^{−2} + b_iK − C′, (g^{(i)})^{−2} + b_i′K + C′] for the targets g^{(i)} (#B10.25), as #B2.18 takes it for one coupling.
  {#B10.85-1} (W) gives f_{K,i} ≤ (g^{(i)})^{−2} on the face
  {#B10.86} x_{0,i} = (g^{(i)})^{−2} + b_iK − C′ and f_{K,i} ≥ (g^{(i)})^{−2} on the face x_{0,i} = (g^{(i)})^{−2} + b_i′K + C′, whatever the other components are.
  {#B10.86-1} The
  {#B10.87} Poincaré–Miranda theorem then gives a solution in the box, and step 4 of Lemma 2.1 applies componentwise.

{#B10.87-1} **Proposition 10.4 (Factors Permuted by a Symmetry).** Let G be as in Lemma 10.1, with the Wilson action A of its defining representation, additive or not. Assume that there are unitaries W_1, …, W_m with W_lGW_l* = G whose automorphisms Ad_{W_l} of g permute the simple ideals g_1, …, g_r transitively. Then:
- {#B10.87-2} (a) every bilinear form on g, real or complex valued, invariant under Ad(G) and under every Ad_{W_l} is a multiple of tr; in particular K = κ·tr on g, with κ := κ_1^N = ⋯ = κ_r^N;
- {#B10.87-3} (b) RG1's construction on G with one coupling, and the tube construction, commute with U ↦ W_lUW_l*: every step term satisfies E^{(j)}(X; W_lUW_l*, W_lJW_l*) = E^{(j)}(X; U, J);
- {#B10.87-4} (c) RG1 (1.21), p.264, and the proportionality to δ_{ab} at (4.33), p.289 l.35–37, hold for G, and Theorem 0.1, with what §0 states for the tube construction, holds for G with the proof given for simple G.

{#B10.87-5} *Proof.*
1. {#B10.87-6} *(a).* By Lemma 10.1 an Ad(G)-invariant form is Σ_iϑ_iK_i = Σ_iϑ_iκ_i^N tr|_{g_i}, the ideals being orthogonal for it. Ad_{W_l} is an automorphism of g, so it maps each g_i onto some g_{σ_l(i)} and preserves K; it preserves tr, W_l being unitary. So invariance gives ϑ_{σ_l(i)}κ_{σ_l(i)}^N = ϑ_iκ_i^N, and K itself gives κ_{σ_l(i)}^N = κ_i^N; transitivity makes both constant in i.
2. {#B10.87-7} *(b).* Put ψ_l(U) := W_lUW_l*. It maps G and G^c onto themselves and g onto g, preserves Haar measure, tr, and the Euclidean norm of the coordinates in a tr-orthonormal basis (PBG p.389 l.20), and commutes with products, inverses, exp, log, Ad, and brackets.
   {#B10.87-8} Every object of the construction is given by a formula in these operations and in lattice data alone, or as the unique solution of an equation so built, and so commutes with ψ_l: the averages (0.4), (0.12) and (0.10) and the variables (0.11), pp.253–254 (RG1 p.253 l.42–43 allows any average with (0.5)–(0.9); take (0.10)); the domains (1.11)–(1.14), p.262; the integrand of (2.1), p.265 (dV, the δ-function of the average, χ_k, 𝐆, A, E_k);
   {#B10.87-9} the critical configuration V^{(k)} and the minimal configuration U_{k+1}(W), W the block variable of (2.1), unique by p.265 l.26–30; the axial and Landau gauges and 𝐇_k (p.265 l.37–41, through formula (106) of RG1's reference [12]); the operators of PBG at a configuration U (H, D, Δ, Δ_1, C), which are linear in the fields and built from Ad(U), the plaquette matrices U(∂p) of the defining representation under tr (Δ, by PBG (3.7), p.391 l.35–38), and lattice differences;
   {#B10.87-9a} the expansions and Cauchy integrals in auxiliary parameters of RG1 §3 and RG2 §§1–2, and RG1 §4's Taylor expansion of the localised terms in B, written through tr (pp.288–289);
   {#B10.87-10} CRE's and LFR's cutoff functions and large-field decompositions, which depend on the configuration through |∂U − 1|, |B|, and |J| on lattice sets; the changes of variables of CRE (1.22), p.251, of CRE p.269, and of LFR1 p.188, with the bump φ_b of #B2.2.555-0, a function of the Hilbert–Schmidt norm, and their Jacobians (CRE (1.24), p.252);
   {#B10.87-10a} LFR1's R-operation (0.3)–(0.6), p.176, with the densities (1.100)–(1.101), p.201: quotients of integrals with Haar measure, the axial-gauge δ-functions of graphs in the sets Λ_i (p.201 l.28), the thresholds χ(|(1/i)log V′| < M₀ε_k), and exp[−g_k^{−2}A], followed by a polymer expansion over lattice sets; and the tube construction's δ^T_k and β^T_k, which are numbers.
   {#B10.87-11} By induction on j, with E^{(0)} = 0: if the input of step j commutes with ψ_l, the substitution V ↦ ψ_l(V) in (2.1) and in each expansion of the step shows that its output does.
3. {#B10.87-12} *(c).* By (b), Π_{j+1}(x, x′) of RG1 (1.20) is invariant under Ad(G) ⊗ Ad(G) and under every Ad_{W_l} ⊗ Ad_{W_l}, so by (a) it is a multiple of tr; this is (1.21), and (4.33) is the same statement for 𝐄^{(2)}_{μ,ν}(X, x, y). Simplicity enters the proof for simple G only through:
   {#B10.87-13} Lemma 1.1 and its Consequences (#B1.2–#B1.16), replaced by (a) and by (1.21) and (4.33), which make the marginal terms a multiple of tr, that is of the quadratic part of A; #B2.1.3-1 (one coupling), by the same; #B4.60-1, where the symbols at U = 1 commute with Ad(G), hence are ⊕_iT_i(p) ⊗ 1_{g_i}, and with Ad_{W_l}, the step objects commuting with ψ_l by step 2, hence T_i = T₀;
   {#B10.87-14} #B4.108, #B6.2.66 and #B6.2.125, which use only that g has no nonzero Ad-invariant vector, true for semisimple g; and Corollary 8.2, which uses Theorem 8.1 with c = (11/48π²)κ. RG1 states its construction, which RG2, CRE, LFR1, and LFR2 continue, for compact semisimple G ⊂ U(N) (p.251 l.30–p.252 l.2), and PBG for compact G ⊂ U(N) (p.389 l.12). ∎

{#B10.87-15} Example: SO(4) ⊂ U(4), which is not additive (*Which actions are additive*), with W = diag(−1, 1, 1, 1); conjugation by this reflection exchanges the two su(2) ideals of so(4) (self-dual and anti-self-dual parts).

{#B10.88} **What is OPEN.** RG1's one-coupling form g_k^{−2}A(U_k) of the effective action on G, for which RG1 states Theorem 1 (p.259 l.23–24), fails when the c_i/w_i differ: the marginal part of the step terms is a combination of the quadratic parts of the A_i (Lemma 10.1), which one coupling absorbs only when its coefficients are in the ratio of the bare weights, and at zero coupling this needs the c_i/w_i, that is the κ_i^N, to be equal. Not covered:
- {#B10.93} RG1's construction on G, with a coupling vector, for non-additive actions without a symmetry as in Proposition 10.4, such as SU(2) × SU(3) ⊂ U(6) acting on ℂ² ⊗ ℂ³, where κ_1^N = 8 and κ_2^N = 18. The inputs proved so far are the lemmas from Lemma 10.5 to the end of this section (#B10.104 onwards); what of the construction remains open is stated in #B10.131-1, #B10.147-2, #B10.199-1, #B10.212-1 and #B10.221.

{#B10.94} For these actions, the coupling-dependent thresholds of CRE and LFR2, which the construction of Theorem 0.1 uses in place of
{#B10.95} RG1's fixed ε₀ and ε₁ (§0, *Input 3*), are functions of a single coupling g_k: ε_k = g_kp₀(g_k) in CRE (2.4), δ_k on CRE p.265,
{#B10.96} and p₀(g_k) in LFR2 (1.86).
{#B10.97-1} More than these thresholds changes: A differs from every combination of
{#B10.98} Wilson actions of representations of G each nontrivial on one ideal only (as for SO(4), by 2 at the plaquette value −1 ∈ SO(4), which every such representation maps to 1), so RG1's form g_k^{−2}A(U_k) of the effective action,
{#B10.99} the background field as the minimiser of one action, and the large-field bounds have to be restated.
{#B10.104} **The classical actions for a coupling vector.** For the actions of #B10.93, G is from here on as in Lemma 10.1, connected, with the defining representation G ⊂ U(N), and tr is the normalised trace of RG1 (0.2). Lemmas 10.11–10.17 are not yet through review.

{#B10.105} **Lemma 10.5 (Comparison Actions).** For u ∈ G put a(u) := 1 − Re tr u, and for each simple ideal g_i put ã_i(u) := ν_i(1 − tr_i Ad(u)|_{g_i}), with tr_i the normalised trace on End(g_i) and ν_i > 0 the constant for which a(e^{iX}) and ã_i(e^{iX}) have the same quadratic part for X ∈ g_i. Put c_⊗ := a − Σ_iã_i. Then:
- {#B10.106} (a) each ã_i is a real class function on G with ã_i ≥ 0, ã_i(u) = 0 if and only if Ad(u)|_{g_i} = 1, and ã_i(e^{iX}) depends on X ∈ g only through its g_i-component X_i;
- {#B10.107} (b) c_⊗(e^{iX}) = 1 − tr cos X − Σ_iν_i(1 − tr_i e^{iad X_i}) is even and entire in X ∈ g^c, and |c_⊗(e^{iX})| ≤ C_c|X|⁴ for |X| ≤ x_c, with constants C_c, x_c depending on G;
- {#B10.108} (c) a(u) = ½|u − 1|², |·| the normalised Hilbert–Schmidt norm, and a ≥ c_aΣ_iã_i on G for a constant c_a ∈ (0, 1];
- {#B10.109} (d) for 0 < θ ≤ min_ih_i, θa + Σ_i(h_i − θ)ã_i ≥ θa and ≥ c_aΣ_ih_iã_i.

{#B10.110} *Proof.*
1. {#B10.111} *(a).* Ad(u) preserves each ideal and is orthogonal for the trace form, so tr_i Ad(u)|_{g_i} is real, at most 1, and equal to 1 exactly when Ad(u)|_{g_i} = 1; conjugating u conjugates Ad(u)|_{g_i}.
   {#B10.111-1} For X ∈ g, Ad(e^{iX}) = e^{iad X}, and ad X_j vanishes on g_i for j ≠ i, so Ad(e^{iX})|_{g_i} = e^{iad X_i}|_{g_i}. The quadratic parts of a(e^{iX}) = 1 − tr cos X and of 1 − tr_i Ad(e^{iX})|_{g_i}, as forms in X ∈ g, are Ad(G)-invariant, since both functions of u are class functions, so by Lemma 10.1 each restricts to g_i as a multiple of K_i, nonzero as both are positive definite on g_i; so ν_i exists.
2. {#B10.112} *(b).* a(e^{iX}) = 1 − tr cos X is even and entire in X; ã_i(e^{iX}) = ν_i(1 − tr_i e^{iad X_i}) is even, since iad X_i is antisymmetric for the trace form and tr_i e^{M} = tr_i e^{M^T} = tr_i e^{−M}; both extend to X ∈ g^c by the same formulas. The quadratic part of a(e^{iX}) is ½tr X² = ½Σ_itr X_i², since the ideals are orthogonal for the trace form (Lemma 10.1), and this equals the sum of the quadratic parts of the ã_i by the choice of ν_i. So c_⊗(e^{iX}) has no terms of order 0 or 2 and none of odd order, which gives the bound.
3. {#B10.113} *(c).* 1 − Re tr u = ½tr(u − 1)*(u − 1) for unitary u. Near 1, u = e^{iX} with X ∈ g small, Σ_iã_i(u) ≥ c_ã|X|², with c_ã > 0 as the quadratic parts are positive definite, and |c_⊗(u)| ≤ C_c|X|⁴ by (b), so a ≥ ½Σ_iã_i once C_c|X|² ≤ c_ã/2. Away from that neighbourhood, a ≥ a_* > 0, since a vanishes only at 1, and Σ_iã_i ≤ 2Σ_iν_i. Take c_a := min{½, a_*/(2Σ_iν_i)}.
4. {#B10.114} *(d).* θa + Σ_i(h_i − θ)ã_i ≥ θa, as h_i ≥ θ and ã_i ≥ 0; and, by (c), it is ≥ θc_aΣ_iã_i + Σ_i(h_i − θ)ã_i ≥ c_aΣ_ih_iã_i, as c_a ≤ 1. ∎

{#B10.115} The coefficient θ of a in (d) is needed, as c_⊗ can take negative values. For SU(n_i) factors acting on a tensor product, the adjoint character |χ|² − 1 gives tr_i Ad(u)|_{g_i} = (n_i²|t_i|² − 1)/(n_i² − 1), ν_i = (n_i² − 1)/(2n_i²), and ã_i(u) = ½(1 − |t_i|²), t_i the normalised trace of the i-th tensor factor of u.
   {#B10.115-1} For SU(2) × SU(2) × SU(3) ⊂ U(12) on ℂ² ⊗ ℂ² ⊗ ℂ³ at u = diag(i, −i) ⊗ diag(i, −i) ⊗ diag(1, ω, ω²), ω = e^{2πi/3}, every t_i = 0, so a = 1, every ã_i = ½, c_⊗ = −½, and, for real counterterm coefficients λ_i, g_0^{−2}a − Σ_iλ_iã_i = g_0^{−2}c_⊗ + Σ_ih_iã_i = ½(Σ_ih_i − g_0^{−2}) < 0 for h_i := g_0^{−2} − λ_i once Σ_ih_i < g_0^{−2}.

{#B10.116} *Notation.* For a configuration U on G, Ad_iU is the configuration b ↦ Ad(U(b))|_{g_i}; A(U) := Σ_pa(U(∂p)), Ã_i(U) := Σ_pã_i(U(∂p)), and C(U) := Σ_pc_⊗(U(∂p)) = A(U) − Σ_iÃ_i(U), sums over the plaquettes of the lattice of spacing η as in VAR (5) (d = 4).

{#B10.117} **Lemma 10.6 (Averages and Factor Images).** The averages (0.4), (0.12) and (0.10) of RG1, pp.253–254, and the contour variables (0.11), commute with Ad_i on configurations near 1: M(Ad_i𝐔) = Ad_iM(𝐔). So for every configuration U and every g_i-valued δ, the blocks of e^{iηtδ}U have the same Ad_j-images as those of U for j ≠ i, and, for t small, they equal those of U exactly when their Ad_i-images do. The linearisation L at U of the block constraints maps g_i-valued δ to g_i-valued block variations, so the kernel of L is the direct sum of its g_i-valued parts.

{#B10.118} *Proof.* Ad_i extends to a holomorphic homomorphism G^c → GL(g_i ⊗ ℂ), with Ad_i(e^{iY}) = e^{i ad_iY} for Y ∈ g^c, ad_iY := ad Y|_{g_i ⊗ ℂ}; for Y small, (1/i)log Ad_i(e^{iY}) = ad_iY, and Y ↦ ad_iY is linear.
   {#B10.118-1} If 𝐔 solves (0.10) for {𝐔_j}, applying ad_i to Σ_j(1/i)log 𝐔_j𝐔^{−1} = 0 shows that Ad_i𝐔 solves (0.10) for {Ad_i𝐔_j}, and that solution near the 𝐔_j is unique (RG1 p.253 l.34–38), as the left side of (0.10) has derivative −n + O(max_j|𝐔_j𝐔^{−1} − 1|) in the direction of 𝐔, in any matrix group. (0.11) is M applied to contour variables, which Ad_i maps to contour variables.
   {#B10.118-1a} (0.4) is exp[i·(an average of (1/i)log of contour variables)]𝐔(c), and (0.12) the same with the products 𝐔(c₋, x)𝐔([x, x′])𝐔(x′, c₊)𝐔(−c) of variables (0.11) and bond variables; so Ad_i of either is the same formula for Ad_i𝐔.
   {#B10.118-2} Ad_j(e^{iηtδ}) = 1 for j ≠ i, as δ takes values in g_i. The kernel of u ↦ (Ad(u)|_{g_j})_j is Z(G), which is finite; two blocks near each other with equal images under every Ad_j differ by an element of Z(G) near 1, hence are equal.
   {#B10.118-3} For g_i-valued δ, a block of e^{iηtδ}U is e^{iY(t)} times that block of U, with Y(0) = 0 and Y smooth, and its Ad_j-image is constant in t for j ≠ i, so ad_jY′(0) = ad(Y′(0)_j)|_{g_j} = 0, and Y′(0)_j = 0, since z(g_j) = 0. So L(δ_i) is g_i-valued for g_i-valued δ_i, and L(Σ_iδ_i) = 0 exactly when every L(δ_i) = 0, as the ideals are linearly independent. ∎

{#B10.119} **Lemma 10.7 (Linear Terms at RG1's Background).** Let U be a critical configuration of A on a constraint set {U : Ū^j = V on Λ_j} as in VAR (6), such as RG1's minimal configuration U_k(V) (VAR Theorem 1). For g-valued δ let ⟨δ, J_i⟩ := (d/dt)Ã_i(e^{iηtδ}U)|_{t=0} and ⟨δ, J_c⟩ := (d/dt)C(e^{iηtδ}U)|_{t=0}, for the pairing ⟨δ, J⟩ = Σ_bη^d tr δ(b)J(b) of VAR (27).
   {#B10.119-1} Then ⟨δ, J_i⟩ = −⟨δ, J_c⟩ for every g_i-valued δ in the tangent space of that set at U, the kernel of the linearised block constraints (Lemma 10.6), and, for every G- or G^c-valued configuration U with max_{p∋b}|U(∂p) − 1| ≤ x_c′, |J_c(b)| ≤ 2(d − 1)C_c′η^{1−d}max_{p∋b}|U(∂p) − 1|³ times the largest ‖Ad(u)‖ over the transports u of step 3 (1 for G-valued U), with C_c′, x_c′ depending on G.

{#B10.120} *Proof.*
1. {#B10.121} For j ≠ i, Ã_j(e^{iηtδ}U) = Ã_j(U), by Lemma 10.5(a), since Ad_j(e^{iηtδ}) = 1. So A(e^{iηtδ}U) = Σ_{j≠i}Ã_j(U) + Ã_i(e^{iηtδ}U) + C(e^{iηtδ}U).
2. {#B10.122} δ is tangent to the constraint set and U is critical there, so (d/dt)A(e^{iηtδ}U)|_{t=0} = 0, which is the identity by step 1.
3. {#B10.123} For δ supported on b, Lemma 10.9(b), whose proof uses only Lemma 10.5(b) and runs plaquette by plaquette, gives |dC[δ]| ≤ C_c″Σ_{p∋b}|X_p|³|X_p′|, X_p(t) := (1/i)log (e^{iηtδ}U)(∂p), once |U(∂p) − 1| ≤ x₀. For p ∋ b, (e^{iηtδ}U)(∂p) = e^{iηtY}U(∂p) with Y = ±Ad(u)δ(b), u the transport along p to b, so |Y| ≤ ‖Ad(u)‖|δ(b)| in the normalised Hilbert–Schmidt norm (#B10.108), with equality for G-valued U; for |U(∂p) − 1| ≤ x_c′ ≤ x₀, small depending on G, the logarithm series gives |X_p| ≤ O(1)|U(∂p) − 1| and |X_p′| ≤ O(1)η|Y|.
   {#B10.123-1} The pairing brings η^{−d}. The norm is self-dual for it on g, and a g^c-valued J = J₁ + iJ₂, J₁, J₂ g-valued, has |J|² = |J₁|² + |J₂|², so its dual norm against g-valued δ(b) is at least |J|/√2. Each bond lies in 2(d − 1) plaquettes, so C_c′ := √2·O(1)C_c″. ∎

{#B10.124} *Size.* RG1's minimal configuration U = U_k(V) lies in the space VAR (2) with ε₀ = B₃ε₁ (VAR Theorem 1, (8), p.279 l.8–12), so |U(∂p) − 1| < B₃ε₁L^{−2j} for every plaquette p with a corner in Ω_j (VAR (2), p.278 l.5), hence for every p containing a bond of Ω_j, which has an end-point in Ω_j (VAR p.277 l.17), and, for B₃ε₁ ≤ x_c′, (L^jη)³|J_c| ≤ 2(d − 1)C_c′(B₃ε₁)³L^{−3j}. Where all Ω_j coincide (no large-field region) |J_c| = O(ε₁³η³), η = L^{−k}.
   {#B10.124-1} RG1's complex domains are unions of orbits of pairs (𝐔, 𝐉) satisfying four conditions (p.262 l.13–14); the consumers' sets (#B10.177-0a, #B10.200-1) and the bound use (i)–(iii) (l.15–38), with 𝐔 = e^{iξA′}U, U G-valued, |A′| < α₁ and |∂𝐔 − 1| < α₀ξ² ((1.11), (1.13), (1.14)). A transport of Lemma 10.7 is a product of at most four bond variables or their inverses, U(∂p) for the last bond of p (#B6.2.14), so ‖Ad(u)‖ ≤ e^{O(1)α₁} ≤ 2 for α₁ small depending on G, and for α₀ ≤ x_c′ (ξ = L^{−j} ≤ 1, #T10.28-1-0) the same bounds hold with α₀ in place of B₃ε₁ and 2C_c′ in place of C_c′.

{#B10.125} **Lemma 10.8 (The Plaquette Action Family).** For h = (h_1, …, h_r) with h_i > 0 and θ := min_ih_i put s_h := θa + Σ_i(h_i − θ)ã_i and S(h; U) := Σ_ps_h(U(∂p)) = θA(U) + Σ_i(h_i − θ)Ã_i(U). Then:
- {#B10.126} (a) S((g_0^{−2}, …, g_0^{−2}); U) = g_0^{−2}A(U), the bare action;
- {#B10.127} (b) S(h; U) ≥ θA(U) and S(h; U) ≥ c_aΣ_ih_iÃ_i(U), plaquette by plaquette (Lemma 10.5(d));
- {#B10.128} (c) S(h; U) − S(h′; U) = Σ_i(h_i − h_i′)Ã_i(U) + (θ − θ′)C(U), and |θ − θ′| ≤ max_i|h_i − h_i′|;
- {#B10.129} (d) the quadratic part of s_h(e^{iX}) is ½Σ_ih_itr X_i², and at a critical configuration U as in Lemma 10.7, for δ tangent to the constraint set at U, written δ = Σ_iδ_i with each δ_i tangent and g_i-valued (Lemma 10.6), the linear term of S(h; e^{iηtδ}U) in δ is −Σ_i(h_i − θ)⟨δ_i, J_c⟩.

{#B10.130} *Proof.* (a) and (b) are immediate. (c): θA + Σ_i(h_i − θ)Ã_i − θ′A − Σ_i(h_i′ − θ′)Ã_i = Σ_i(h_i − h_i′)Ã_i + (θ − θ′)(A − Σ_iÃ_i), and min is 1-Lipschitz for the maximum norm. (d): the quadratic parts of a and ã_i are ½Σ_itr X_i² and ½tr X_i² (Lemma 10.5); the linear term of θA vanishes at a critical U; Ã_i(e^{iηtδ}U) = Ã_i(e^{iηtδ_i}U), ã_i(u) being a function of Ad(u)|_{g_i} (Lemma 10.5), since Ad_i(e^{iηtδ(b)}) = e^{iηt ad_iδ(b)} = e^{iηt ad_iδ_i(b)} (#B10.118), ad_i vanishing on the other ideals; and Lemma 10.7 gives the rest. ∎

{#B10.131} *Use (open).* In the construction that #B10.93 asks for, S(h^k; ·) takes the place of g_k^{−2}A in RG1 (1.3), with h_i^k = g_{k,i}^{−2}. By (c), the per-step change is the counterterm Σ_iβ_{k+1,i}Ã_i, per factor as the marginal part is (Lemma 10.1), plus (θ_k − θ_{k+1})C, which is local, analytic, gauge invariant, and, with β_max := max_{j≤k+1, i}|β_{j,i}|, of size O(β_maxα₀⁴η⁴) per unit cube on RG1's domains (Lemma 10.5(b)), the form of RG1 (1.18)–(1.19).
   {#B10.131-0} At RG1's background U_k(V), A's minimal configuration, the linear term is given by (d) and, for B₃ε₁ ≤ x_c′, #B10.124; the bare h^0 having equal entries (a), h_i^k − θ_k ≤ 2kβ_max, and the term is O(kβ_maxη³α₀³g) in fluctuation units. At the minimal configuration of S(h^k; ·) it vanishes; that is the background Lemma 10.11 fits (#B10.158), and it exists by Lemma 10.12.
   {#B10.131-1} What Lemmas 10.11–10.17 do not give is the open part of #B10.93: RG1 §3 and RG2 for E^{(k+1)} (#B10.212-1), the domain of #B10.199-2, running RG1's induction, and CRE and LFR1–LFR2 with the thresholds of #B10.94–#B10.96; so are the value and form of the β_{k+1,i}, which through the Hessian of θ_kC may depend on the ratios h_i^k/h_{i′}^k.

{#B10.132} **Lemma 10.9 (Derivatives of the Family per Factor).** Let U be a configuration with |U(∂p) − 1| ≤ x₀ for every plaquette p, put X_p := (1/i)log U(∂p), and for g-valued δ = Σ_iδ_i, δ_i g_i-valued, let X_p(t) := (1/i)log (e^{iηtδ}U)(∂p), X_p′ := X_p′(0), X_p″ := X_p″(0), and d^nF[δ] := (d^n/dt^n)F(e^{iηtδ}U)|_{t=0}. Then, for x₀ small enough depending on G:
- {#B10.133} (a) S(h; ·) = Σ_ih_iÃ_i + θC, and d^nS(h; ·)[δ] = Σ_ih_id^nÃ_i[δ_i] + θd^nC[δ] for n = 1, 2;
- {#B10.134} (b) |dC[δ]| ≤ C_c″Σ_p|X_p|³|X_p′| and |d²C[δ]| ≤ C_c″Σ_p|X_p|²(|X_p′|² + |X_p||X_p″|), with C_c″ depending on G;
- {#B10.135} (c) G_i := {Ad(u)|_{g_i} : u ∈ G} is a compact connected group of unitaries of g_i ⊗ ℂ for the inner product tr Y*Z, with Lie algebra ad_ig_i ≅ g_i in RG1's Hermitian convention, simple; Ã_i(U) = ν_iA^{(i)}(Ad_iU), with A^{(i)} the action VAR (5) for G_i and the normalised trace tr_i; Ad_i(e^{iηtδ}U) = e^{iηt ad_iδ_i}Ad_iU; and ν_i tr_i(ad_iX ad_iY) = tr XY for X, Y ∈ g_i.

{#B10.136} *Proof.*
1. {#B10.137} *(a).* s_h = θ(c_⊗ + Σ_iã_i) + Σ_i(h_i − θ)ã_i = Σ_ih_iã_i + θc_⊗. For each j, Ã_j(e^{iηtδ}U) = Ã_j(e^{iηtδ_j}U), as in the proof of Lemma 10.8(d).
2. {#B10.138} *(b).* c_⊗(e^{iX}) is entire in X ∈ g^c, with |c_⊗(e^{iX})| ≤ C_c|X|⁴ for |X| ≤ x_c (Lemma 10.5(b)). For 0 < |X| ≤ x_c/2, n ≤ 3 and unit h₁, …, h_n, the polydisc X + Σ_lζ_lh_l, |ζ_l| ≤ |X|/n, lies in the ball of radius 2|X| ≤ x_c, where |c_⊗(e^{i·})| ≤ 16C_c|X|⁴, so Cauchy's estimate in ζ₁, …, ζ_n gives |∇^nc_⊗(X)[h₁, …, h_n]| ≤ 16n^nC_c|X|^{4−n} ≤ C_c″|X|^{4−n}, C_c″ := 432C_c; at X = 0 both sides vanish, c_⊗ having no terms of order below 4. |X_p| ≤ x_c/2 for x₀ small.
   {#B10.138-1} The chain rule gives d c_⊗(e^{iX_p(t)})/dt = ∇c_⊗(X_p)[X_p′] and d²c_⊗(e^{iX_p(t)})/dt² = ∇²c_⊗(X_p)[X_p′, X_p′] + ∇c_⊗(X_p)[X_p″] at t = 0; sum over p.
3. {#B10.139} *(c).* G_i is the image of G under the continuous homomorphism Ad_i, so it is compact and connected. For Hermitian X, ([X, Y])* = [Y*, X], so tr Y*[X, Z] = tr([X, Y])*Z, and ad X is Hermitian on g_i ⊗ ℂ; ad_i is injective on g_i, as z(g_i) = 0, and vanishes on the other ideals. tr_i Ad_iU(∂p) is real (step 1 of Lemma 10.5), so ν_i(1 − tr_i Ad_iU(∂p)) = ν_i(1 − Re tr_i Ad_iU(∂p)). The identity for Ad_i is in the proof of Lemma 10.8(d). The quadratic part of ã_i(e^{iX}) is ½ν_i tr_i(ad_iX)², that of a(e^{iX}) is ½tr X², and they agree on g_i by the choice of ν_i; polarise. ∎

{#B10.140} **Lemma 10.10 (The Quadratic and Linear Terms per Factor).** Let U be in PBG's class (3.35)–(3.36) for G, or let U′U be in PBG's class (3.37), U′ PBG's complex factor, with O(1)Mα₀ and α₁ small depending on G. For the configuration e^{iηδ}U and the variable A := Σ_ih_i^{1/2}δ_i, the quadratic part of S(h; e^{iηδ}U) is ½⟨A, (D*D + Δ″)A⟩, with D = D_U of G and PBG's pairing (3.11), where Δ″ := ⊕_iΔ′_{(i)} + K_C, Δ′_{(i)} is PBG's Δ′ (3.10) for G_i at Ad_iU read through ad_i, and K_C is the operator of the form θd²C[h^{−1/2}A]. Then:
- {#B10.140-1} (a) D, the averaging operators Q_j(U) of PBG (3.15)–(3.16), the projection R(U) of PBG (3.21), and the gauge fixing operators of PBG pp.393–395 map g_i-valued fields to g_i-valued fields;
- {#B10.140-2} (b) Δ″ is local, with range the plaquettes containing a bond, analytic on PBG's class (3.37), and satisfies PBG (3.69): |(Δ″A)(b)| ≤ O(1)(Mα₀ + α₁)(L^jη)^{−2}|A| for b ∈ Ω_j, with the maximum of |A| over the bonds of the plaquettes containing b, and O(1) depending on G;
- {#B10.140-3} (c) |((Δ″(U′U) − Δ″(U))A)(b)| ≤ O(1)α₁(L^jη)^{−2}|A| for b ∈ Ω_j, the bound PBG states for Δ′ (p.404 l.15–16) and uses through V₃ of (3.82) in (3.85), p.407;
- {#B10.140-4} (d) S(h; ·) is gauge invariant; the term of S(h; e^{iηδ}U) linear in A is Σ_ih_i^{1/2}⟨A_i, J♮_i⟩, with J♮_i := J_(i) + (θ/h_i)J_{c,i}, where J_(i) is PBG's J (3.11) for G_i at Ad_iU read through ad_i and J_{c,i} is the g_i-component of J_c, the gradient of C; D*J♮ = 0; J♮ = D*F♮ for a plaquette function F♮; |J_{c}(b)| ≤ O(1)(Mα₀)³ξ³(L^jη)^{−3} on Ω_j for U in (3.35)–(3.36), and ≤ O(1)(Mα₀ + α₁)³ξ³(L^jη)^{−3} for U′U in (3.37); and PBG's identities (3.117) hold with D*D + Δ″ for Δ, J♮ for J, and the gauge parameter scaled as A.

{#B10.141} *Proof.*
1. {#B10.142} *The form.* By Lemma 10.9(a), the quadratic form is Σ_ih_id²Ã_i[δ_i] + θd²C[δ]. By Lemma 10.9(c), h_id²Ã_i[δ_i] = ν_ih_i times the Hessian of A^{(i)} at Ad_iU in ad_iδ_i, which is PBG (3.10) for G_i in tr_i; read through ad_i with ν_itr_i(ad_iX ad_iY) = tr XY, and with h_i^{1/2}δ_i = A_i, it is ⟨A_i, (D*D + Δ′_{(i)})A_i⟩, D acting on g_i-valued fields through Ad(U) as D for G_i acts through Ad_iU.
2. {#B10.143} *(a).* D and Q′_j are built from R(U(b)) = Ad(U(b)) and lattice differences or averages (PBG (3.8), (3.19)). Q_j(U) = Q(Ū^{j−1})⋯Q(U) (PBG (3.15), p.393 l.8–13), with Q(V) given by CMP98 (124), p.36, whose coefficients are R_{0,·} = Ad(·), g(−i ad_Y), g^{−1}(±i ad_{Y_x}) and e^{±i ad_Y} for g^c-valued Y, Y_x, all functions of ad. Each preserves every ideal.
   {#B10.143-1} R(U) is the orthogonal projection onto Δ_UN(Q′) (PBG (3.21)); N(Q′) is the direct sum of its g_i-valued parts and Δ_U preserves them, and the ideals are orthogonal for tr, so R(U) preserves them. The gauge fixing operators are built from these (pp.393–395).
3. {#B10.144} *(b) for Δ′_{(i)}.* PBG's proof of (3.69) uses only |Re(U′U)(∂p) − 1|, |Im(U′U)(∂p)| ≤ O(1)(Mα₀ + α₁)ξ², ξ = L^{−j} (p.404 l.11–14). Ad_i is holomorphic on G^c with Ad_i(1) = 1, so |Ad_i(u) − 1| ≤ C_Ad|u − 1| near 1, with C_Ad depending only on G, and the same bounds hold for Ad_i(U′U)(∂p) with O(1)C_Ad.
4. {#B10.145} *(b) for K_C.* With δ = h^{−1/2}A, X_p′ = η·(dlog at X_p)(Σ_{b⊂∂p} ±Ad(·)δ(b)) and X_p″ = O(η²|δ|²) on the bonds of p, so Lemma 10.9(b) gives, per plaquette, a form bounded by O(1)|X_p|²η²|δ|²_{∂p}, where |X_p| ≤ O(1)(|Re U(∂p) − 1| + |Im U(∂p)|) ≤ O(1)(Mα₀ + α₁)ξ². In the pairing (3.11) with d = 4, this is O(1)(Mα₀ + α₁)²ξ²(L^jη)^{−2}|δ|², as η^{−2}ξ⁴ = ξ²(L^jη)^{−2}; and θh_i^{−1/2}h_j^{−1/2} ≤ 1. c_⊗ is entire, so K_C is analytic.
5. {#B10.146} *(c).* Fix a small constant a with a ≥ Mα₀ and a ≥ 2α₁. On the class (3.37) with a in place of α₁, Δ″ is analytic and, by (b), |(Δ″A)(b)| ≤ O(1)(Mα₀ + a)(L^jη)^{−2}|A| ≤ O(1)a(L^jη)^{−2}|A|. Write U′ = e^{iηA′}; for |z| ≤ R := a/α₁ ≥ 2, e^{izηA′}U is in that class, and the Cauchy estimate in z on |z| ≤ R bounds the difference between z = 1 and z = 0 by O(1)a/R = O(1)α₁, times (L^jη)^{−2}|A|.
6. {#B10.146-1} *(d), invariance and gradient.* S(h; ·) is a sum of class functions of plaquette variables, so it is gauge invariant. Its gradient in δ is Σ_ih_iJ_(i) + θJ_c (Lemma 10.9(a), (c)). For a class function f of U(∂p), the left variation (e^{iηtδ}U)(∂p) = e^{itY_p + O(t²)}U(∂p) has Y_p = η²(Dδ)(p) (PBG (3.7), (3.9)), so the derivative is ⟨Dδ, F⟩ with F(p) := η^{−2}∇^Lf(U(∂p)), ∇^L the left gradient, and the gradient is D*F; for C, |∇^Lc_⊗| ≤ O(1)C_c″|X_p|³ by step 2 of Lemma 10.9, the O(1) bounding the derivative of the logarithm.
   {#B10.146-2} With δ_i = h_i^{−1/2}A_i the linear term is Σ_ih_i^{1/2}⟨A_i, J♮_i⟩. Gauge invariance gives ⟨Dλ, Σ_ih_iJ_(i) + θJ_c⟩ = 0 for every λ, and each component separately, as D preserves the ideals, so D*J♮ = 0.
   {#B10.146-2a} The bounds on J_c are Lemma 10.7 with |X_p| ≤ O(1)Mα₀ξ² on (3.35)–(3.36) and |X_p| ≤ O(1)(Mα₀ + α₁)ξ² on (3.37) (#B10.145), as η^{−3}ξ⁶ = ξ³(L^jη)^{−3}; on (3.37), U′ = e^{iηA′} with |A′| < α₁(L^jη)^{−1} (PBG p.396 l.42), so |ηA′| < α₁, and a transport, a product of at most four bond variables or their inverses (#B10.124-1), has ‖Ad(u)‖ ≤ e^{O(1)α₁} ≤ 2. Ad_iU satisfies (3.35)–(3.36) for G_i with O(1)C_Ad, since Ad_i(e^{iηA}) = e^{iη ad_iA} and ad_i is linear, so J_(i) is small as PBG states for J (p.419 l.11–12).
   {#B10.146-3} *(d), (3.117).* PBG derives (3.117) by expanding the gauge invariance of A to second order (p.419 l.2). The same expansion for S(h; ·), with δ = h^{−1/2}A and λ = h^{−1/2}μ, gives (3.117) for D*D + Δ″ in A and μ: a commutator [λ_i, δ_i] = h_i^{−1}[μ_i, A_i] is paired with h_iJ_(i) + θJ_{c,i}, which gives J♮_i. ∎

{#B10.147} *Use (open).* Lemma 10.10 gives, for S(h; ·), the analogues of the properties of Δ, Δ′ and J that PBG §3 states and uses: (3.69) and its difference bound (p.404), the form (3.82) (p.407), the smallness and locality that bound the commutator [Δ″, h_□] with PBG's localisation functions h_□ (p.414 l.2–3), gauge covariance and (3.117) (pp.395–396, 419). PBG's constructions from them, (3.118)–(3.138) (pp.419–423: Δ_π, Δ′_π, Δ^{(2)}, G, H, G₁, H₁) and Theorem 3.12, are Lemma 10.11.
   {#B10.147-1} RG1's Gaussian (2.6)–(2.8), p.266, is ½⟨H₁B′, Δ₁H₁B′⟩ with H_k, H₁ those of the action whose minimal configuration is the background. At RG1's background, A's, H₁ couples the factors through the Hessian of C (for SU(2) × SU(3) on ℂ² ⊗ ℂ³, a(e^{iX}) contains −¼tr X_1² tr X_2²), with a strength bounded only through the ratios h_i/h_j, and (2.7) does not combine A's H with the J of S(h; ·); at S(h^k; ·)'s own minimal configuration both are S(h^k; ·)'s, and Lemma 10.11 applies.
   {#B10.147-2} That background exists, with VAR's regularity, by Lemma 10.12, and Lemma 10.13 writes its change from step to step, as h^k changes, as the counterterm and C-term of Lemma 10.8(c) plus a second order term R_bg, and Lemma 10.14 localises R_bg into local terms analytic on 𝒰(Y). Lemma 10.15 localises the change of the other terms of RG1 (1.6) with the background, at the rate (1 − 2ϱ)κ. Open: what #B10.199-1, #B10.212-1 and #B10.221 state, and the rest of #B10.131-1. Awaiting review: (P-PBG) (#B9.29-3), and REG's results for the chain's dressed average (#BFP.160-2).

{#B10.148} **Lemma 10.11 (PBG's Theorem 3.12 for the Family).** Let U be in PBG's class (3.35)–(3.36) for G and a sequence {Ω_j} with Ω₀ = T (#B9.29-3), with M ≥ M₁, M ≥ M₃ for each G_i (#B9.29-3a), M large depending on d, L and G (#B10.148-0a), and Mα₀ small depending on d, L and G (PBG's Theorem 3.1, p.397 l.37–38, and Theorem 3.11, p.416 l.24), and let h^{±1/2} act on g-valued fields by multiplying the g_i-component by h_i^{±1/2}.
   {#B10.148-0} Let Q_j be PBG's averages (3.15)–(3.16) or the chain's dressed average of §7's Setting, built from RG1's (0.4) or (0.12) (#B9.40-3d); for the latter, the definitions below, (a) and (b) rest on (P-PBG) (#B9.29-3).
   {#B10.148-0a} M is large for the thresholds of BP_PBG_3130.md (#BG.12) and BP_PBG_3132.md (#BQ.13-1), for Lemma A (#BQ.5) in steps 5 and 6 of the proof, and for Lemma C and Schur's test at the rates ½δ₁′ and ¼δ₁′ in steps 5 and 8 (BP_PBG_COMPLEX.md #BX.11-0).
   {#B10.148-1} Define Ĝ, Ĥ, Ĝ₁, Ĥ₁ by PBG (3.118)–(3.129) with D*D + Δ″ (Lemma 10.10) in place of Δ, J♮ in place of J, and, in (3.127)–(3.128), ⟨A, Δ^{(2)}A⟩ := 2⟨h^{1/2}Ĥh^{−1/2}C^{(2)}(A), J♮⟩, C^{(2)} the second order term of Q_j (PBG p.421 l.12; RG1 p.266 l.33, l.39), and 𝔊̂ := Ĝ₁ − Ĝ₁DRD*Ĝ₁ − Ĥ₁QĜ₁, the formula of (3.153) (#B9.29-3a). Then:
- {#B10.149} (a) the term of PBG's (3.127) for S(h; ·), −⟨HC^{(2)}(δ), J⟩ with H and J those of S(h; ·) in the variable δ, equals −½⟨A, Δ^{(2)}A⟩ for A = h^{1/2}δ;
- {#B10.150} (b) PBG's Theorem 3.12 holds for these operators, and its bounds (Theorems 3.3 and 3.10 for Ĝ, Ĝ₁, with ⅜δ₀ for δ₀, without the covariant-Laplacian inequality of (3.42) and the fourth of (3.47), as there; (3.133) with ½δ₁′ for ½δ₁ and Theorem 3.10 for Ĥ, Ĥ₁; (3.132) with δ₁′ for δ₁ (#T10.50) and Theorem 3.10's expansion for (QĜQ*)^{−1} and (QĜ₁Q*)^{−1}; for 𝔊̂, Theorem 3.3 with ½δ₁′ for δ₀, without those two inequalities and the bounds of 𝔊̂∇*λ for λ only bounded, and an expansion) hold for their conjugates h^{s}Xh^{−s}, s = ±1/2, with constants depending on d, L and G, not on h.

{#B10.151} *Proof.* In balaban_proofs/BP_FAMILY_PBG_VAR.md (#BFP.152–#BFP.157-4), not yet through review.

{#B10.158} *Use.* In the variable A the factors couple only through K_C, and the weights θ/h_j enter only as factors ≤ 1, so the constants are independent of the couplings. With the chain's dressed average (#B9.40-3d) this is the input RG1 (2.6)–(2.8) needs at the minimal configuration of S(h^k; ·) (#B10.147-1); it gives nothing at RG1's background, A's, where H and H₁ are A's.

{#B10.159} **Lemma 10.12 (VAR's Theorem 1 for the Family).** VAR's Theorem 1 (p.279) holds with S(h; ·) in place of the action A of VAR (5), with constants a₀, a₁, B₃, B₄(β₀), M(ε₁) depending on d, L and G only (VAR's depend on d and L, #T3.32-2), not on h: for V satisfying VAR (7) on a sequence with Ω₀ = T_η, with ε₁ ≤ a₁, there is a minimal orbit of S(h; ·) in the space VAR (8); it is the unique critical orbit in VAR (6) if B₃ε₁ ≤ ε₀ ≤ a₀; and its configurations satisfy VAR (9)–(10). Its minimal configurations are analytic in V as in VAR §G.
   {#B10.159-1} The averages are VAR's, CMP98's through REG Sect. A (VAR p.278 l.2), or the chain's dressed average (#B9.40-3d), with Lemma 10.11's Q_j accordingly; for the latter, PBG's results hold by (P-PBG) (#B9.29-3–#B9.29-3a-2), and REG's results, which #BFP.160-1 lists, by BP_REG_DRESSED.md (#BFP.160-2).

{#B10.159-2} *Proof.* In balaban_proofs/BP_FAMILY_PBG_VAR.md (#BFP.160–#BFP.167-1), not yet through review.

{#B10.168} **Lemma 10.13 (Change of Background).** Let h, h′ be coupling vectors with h_i, h′_i ≥ 1, put β := h − h′ and b := max_i|β_i|, and let U_h and U_{h′} be the minimal configurations of S(h; ·) and S(h′; ·) for the same V (Lemma 10.12), with ε₁ ≤ a₁, B₃ε₁ ≤ ε₀ ≤ a₀, B₃ε₁ ≤ x_c′ (Lemma 10.7), and θ^{−1/2}b(B₃ε₁)³ ≤ c_bg, c_bg > 0 depending on d, L and G. With the chain's average the lemma rests on (P-PBG) (#B9.29-3–#B9.29-3a-2) and on Lemma 10.12 (#BFP.160-2). Then:
- {#B10.169} (a) S(h; U_h) − S(h′; U_{h′}) = Σ_iβ_iÃ_i(U_{h′}) + (θ − θ′)C(U_{h′}) + R_bg, with R_bg := S(h; U_h) − S(h; U_{h′});
- {#B10.170} (b) at U_{h′}, dS(h; ·)[δ] = Σ_iγ_i⟨δ_i, J_c⟩ for tangent δ = Σ_iδ_i split as in Lemma 10.6, with γ_i := θ − θ′ − β_iθ′/h′_i, so |γ_i| ≤ 2b;
- {#B10.171} (c) U_h = (e^{iηδ*}U_{h′})^u, u the G-valued gauge transformation restoring VAR's axial gauge (p.299 l.26–28), with δ* = δ′ − HD(δ′) (VAR (47)), and A* := h^{1/2}δ′ satisfies |A*|_{(−1)}, |∇A*|_{(−2)} ≤ O(1)θ^{−1/2}b(B₃ε₁)³ in VAR's norms, with the further factor η³ when all of VAR's domains Ω_n are T_η;
   {#B10.171-1} R_bg = −½⟨A*, Δ̂₁A*⟩ + R₃, Δ̂₁ that of S(h; ·) at U_{h′} (Lemma 10.11), where R₃ := V^A(A*) − ⟨A*, (δV^A/δA)(A*)⟩, V^A(A) := V(h^{−1/2}A) for VAR's V (80) of S(h; ·) in δ, and θ^{1/2}V^A has VAR's form (80) and Proposition 4, with constants depending on G (#BFP.175-3); and R_bg is analytic in V.

{#B10.172} *Proof.* In balaban_proofs/BP_FAMILY_PBG_VAR.md (#BFP.173–#BFP.175-3-1), not yet through review.

{#B10.176} *Use.* With h = h^k and h′ = h^{k+1}, Lemma 10.13 rewrites S(h^k; ·) at its own background, at scale k + 1, as S(h^{k+1}; ·) at its own, plus the counterterm and C-term of Lemma 10.8(c), plus R_bg. As b ≤ β_max (#B10.131) and θ_k ≥ 1, the hypothesis θ^{−1/2}b(B₃ε₁)³ ≤ c_bg holds once β_max(B₃ε₁)³ ≤ c_bg, and R_bg is of second order in b(B₃ε₁)³ and carries θ_k^{−1}, which is O(g_{k,i}²) for the largest g_{k,i}. It is analytic in V but not local; Lemma 10.14 localises it as an activity of RG1 §§3–5.

{#B10.177} **Lemma 10.14 (Localisation of R_bg).** In Lemma 10.13, with the chain's dressed average (#B9.40-3d), the lemma resting on (P-PBG) (#B9.29-3–#B9.29-3a-2) and on Lemma 10.12 (#BFP.160-2), let all of VAR's Ω_n be T_η (RG1's small-field case), j the scale of V, so η = L^{−j}, and put U := U_{h′} and J := RG1's J (1.8) at U, VAR's J (28) projected onto g.
   {#B10.177-0} For κ > 0 let κ₁ := max(16κ, 18) (local to Lemmas 10.14–10.15; §2's κ₁ is RG2's own, #T10.56-2), M satisfy the conditions of Lemma 10.11, also with ½δ₀ and ½δ_cx for δ₀ and δ_cx, and δ_σM ≥ κ₁ (δ_σ of #BFL.186-0a), and M′ := max(O(1)L, 20)M + R₁M₁, rounded up to a multiple of R₁M₁ as VAR's M is (p.279 l.3), satisfy M′ ≤ M(ε₁), O(1)LM being the cube size of RG1's (1.12) (p.262 l.21–23) and M(ε₁) = R₁M₁a₁/ε₁ VAR's (p.279 l.17, l.28), possible for ε₁ small depending on κ, and θ^{−1/2}b ≤ γ, with γ small depending on κ, M and G, which gives Lemma 10.13's θ^{−1/2}b(B₃ε₁)³ ≤ c_bg.
   {#B10.177-0a} Let 𝒰(Y) be the set of (𝐔, 𝐉) satisfying RG1's conditions (i)–(iii) (p.262) on Y with α₀ = γ₀ := 2B₃ε₁ and α₁ := B₃ε₁, and (1.12) at every scale n ≤ j for the cubes in Y of size O(1)LM or of side 20M in the units of scale n (#BFL.194-1, #BX.1-4); (1.11), (1.13) and (1.14) at scale n follow from scale j, being pointwise and their bounds weaker in coarser units, the current of scale n being L^{3(n−j)}𝐉 (RG1 (1.8) with L^{−n} for ξ, p.262 l.49–50).
   {#B10.177-0b} Let T^{(j)} have side at least 20M, and B₃ε₁ be small depending on d, L, G, M and κ, as #BFL.186-0b needs, and so that for (𝐔, 𝐉) ∈ 𝒰(Y) each (Ad_i𝐔, J_(i)) satisfies on Y the conditions of G_i's domain of (P-PBG) (#B9.29-3a-0), as in #BFR.210-0.
   {#B10.177-1} On 𝒰(Y) put J♮(𝐔, 𝐉) := (P_i𝐉 − (1 − θ/h_i)J_{c,i}(𝐔))_i, P_i the orthogonal projection of g onto g_i for tr XY (Lemma 10.1) and J_c(𝐔) the gradient of C at 𝐔. J♮(U, J) is J♮ of S(h; ·) at U (Lemma 10.10(d)), as P_iJ = J_(i) + J_{c,i}, J_(i) and J_c being the gradients of Ã_i and C for VAR's pairing (27) and A = Σ_iÃ_i + C (Lemma 10.5, #B10.121). Then R_bg = Σ_{Y∈D_j}R_bg(Y, U, J), where:
- {#B10.178} (a) R_bg(Y, ·, ·) depends on (𝐔, 𝐉) restricted to Y and is defined and analytic on 𝒰(Y), which contains (U, J) by VAR (9) and (28): a cube of size O(1)LM or of side 20M in the units of scale n ≤ j lies in a cube of VAR's class of size 2M′L^jη, all Ω_n being T_η, and (9) there with M′ ≤ M(ε₁) gives |a|, |∇^ηa| < B₃M′ε₁ ≤ O(1)LMBα₀, as M′ ≤ 2O(1)LMB for RG1's large B (p.262 l.26), the scale-n field L^{n−j}a and its derivative L^{2(n−j)}∇^ηa being smaller (#BFL.194-1);
- {#B10.179} (b) |R_bg(Y, 𝐔, 𝐉)| ≤ C(M, κ)θ^{−1}b²(B₃ε₁)⁶exp(−κd_j(Y)) on 𝒰(Y), with C(M, κ) = O(M^q)exp(O(1)κ), q and O(1) depending on d, L and G;
- {#B10.180} (c) R_bg(Y, ·, ·) is gauge invariant under the G^c-valued gauge transformations near the G-valued ones, as in RG2's Lemma 2 (p.011 l.27–28).

{#B10.180-1} *Proof.* In balaban_proofs/BP_FAMILY_LOCALISATION.md (#BFL.181–#BFL.187), not yet through review.

{#B10.188} *Use.* With h = h^k and h′ = h^{k+1}, R_bg(Y) carries θ_k^{−1} = O(g_{k,i}²) for the largest g_{k,i} and is of sixth order in B₃ε₁; it is local, gauge invariant and analytic on 𝒰(Y), which is smaller than RG2's domain (#B10.199-2). In the form RG1 (1.6) every other term, a counterterm or an E^{(n)}, changes as well when the background moves by e^{iηδ*} (Lemma 10.13(c)); Lemma 10.15 localises these changes.

{#B10.189} **Lemma 10.15 (The Other Terms under the Change of Background).** In Lemma 10.14 let B₃ε₁ be small depending on G and on RG1's absolute constants α₀′, α₁, γ₀ (#BFL.195-1), which in Lemmas 10.15–10.16 denote these and not 𝒰(Y)'s values (#B10.177-0a), and 0 < ϱ < ½ with ϱκ large (RG2's δ, p.009 l.16).
   {#B10.189-1} For (𝐔, 𝐉) ∈ 𝒰(Y) let δ*(𝐔, 𝐉) be Lemma 10.13(c)'s δ* computed at 𝐔 in place of U_{h′} with J♮(𝐔, 𝐉) for J♮ (steps 3–5 of Lemma 10.14), δ′ the corresponding δ′, 𝐔_t := e^{itηδ*}𝐔, and 𝐉_t := 𝐉 + J(𝐔_t) − J(𝐔), J(·) being RG1's (1.8), a sum over the plaquettes containing a bond of derivatives of plaquette functions.
   {#B10.189-2} E^{(n)} takes the current of scale n, 𝐉_{t,n} := L^{3(n−j)}𝐉_t, so 𝐉_{0,n} = L^{3(n−j)}𝐉 and 𝐉_{t,n} = 𝐉_{0,n} + J_n(𝐔_t) − J_n(𝐔) for J_n RG1's (1.8) with L^{−n} for ξ (p.262 l.49–50). At (𝐔, 𝐉) = (U, J), (𝐔₁, 𝐉₁) is (U_h, J(U_h)) up to the gauge transformation u of Lemma 10.13(c), under which E^{(n)}, Ã_i and C are invariant (RG1 (1.10), (1.19)).
- {#B10.190} (a) Let E^{(n)}, n ≤ j, be activities of RG1 (1.18)–(1.19) on U_n^c(X, α₀, α₁), with constants E₀^{(n)} ≤ E₀ and condition (iv) read with the minimal configurations of actions S(h″) as in Lemma 10.12. Then Σ_{n≤j}Σ_{X∈D_n}[E^{(n)}(X, 𝐔₁, 𝐉_{1,n}) − E^{(n)}(X, 𝐔, 𝐉_{0,n})] = Σ_{Y∈D_j}R_E(Y, 𝐔, 𝐉), with R_E(Y) as R_bg(Y) in Lemma 10.14(a), (c), and |R_E(Y)| ≤ C(M, κ, ϱ)θ^{−1}b(B₃ε₁)³E₀exp(−(1 − 2ϱ)κd_j(Y)), the rate of RG2's Lemma 1 for the same kind of term (p.009 (1.36));
- {#B10.191} (b) with h^0 the bare coupling vector and θ_0 := min_ih^0_i, the change of the counterterm sums, Δ_ct := Σ_i(h^0_i − h_i)(Ã_i(U_h) − Ã_i(U_{h′})) + (θ_0 − θ)(C(U_h) − C(U_{h′})), equals Σ_{Y∈D_j}R_ct(Y, U, J), with R_ct(Y) as R_bg(Y) in Lemma 10.14(a), (c), and |R_ct(Y)| ≤ C(M, κ)|h^0 − h|θ^{−1}b(1 + θ^{−1}b)(B₃ε₁)⁶η⁶exp(−κd_j(Y)), |h^0 − h| := max_i|h^0_i − h_i| + |θ_0 − θ|;
- {#B10.192} (c) R_E(Y) and R_ct(Y) vanish to fourth order at (𝐔, 𝐉) = (1, 0); in particular their second derivatives there are 0.

{#B10.193} *Proof.* In balaban_proofs/BP_FAMILY_LOCALISATION.md (#BFL.194–#BFL.198), not yet through review.

{#B10.199} *Use.* With h = h^k and h′ = h^{k+1}, b ≤ β_max and |h^0 − h^k| ≤ 2kβ_max (#B10.131), and kη⁶ ≤ 1, so R_bg, R_E and R_ct are local, gauge invariant and analytic on 𝒰(Y), bounded by C(M, κ, ϱ)θ_k^{−1}(1 + β_max)³(B₃ε₁)³(1 + E₀)exp(−(1 − 2ϱ)κd_j(Y)). By (c), and as R_bg is of sixth order at (1, 0) by the argument of #BFL.198, their second derivatives at 𝐔 = 1 vanish, so they do not change Π_{k+1} (RG1 (1.20)), the second derivative at B = 0 of E^{(k+1)}(U_{k+1}(exp iB)), U_{k+1}(1) = 1 with 𝐉 = 0 there, and so not β_{k+1} ((1.22)).
   {#B10.199-1} Writing the effective action of step k at S(h^{k+1})'s background is thus Lemma 10.13 plus these activities; this is the change of background in the induction of RG1 §§2–5. The rate (1 − 2ϱ)κ is that of RG2's V′_k, the same kind of term (Lemma 1, p.009 l.25–26, (1.36)), which RG2 §2 carries to (1 − 8δ_{RG2})½Lκd_{k+1} by 2d_k(Z) ≥ Ld_{k+1}(Z′) (p.019 l.35, p.020 l.33), at least κd_{k+1}, since (1 − 12δ_{RG2})½L = 1 (#B2.1.16) gives (1 − 8δ_{RG2})½L > 1; so with ϱ = δ_{RG2} the activities enter RG2 §2 with V′_k at its rate.
   {#B10.199-2} Putting them into E^{(k+1)} needs analyticity on RG2's domain U^c_{k+1}(Y, (1 + β)α₀, (1 + β)α₁, α₀) of Lemma 1 (p.009 l.17–18, l.40–41, (1.34); β of #T10.28-4-1-1), with RG1's absolute α₀, α₁ (p.263 l.24–25), larger than 𝒰(Y). This, RG1 §3 and RG2 for E^{(k+1)} (#B10.212-1), and running the induction are part of the open part of #B10.93; the rest is listed in #B10.131-1.

{#B10.200} **Lemma 10.16 (RG1 §2 and PBG §E for the Family).** Let h = h^k with θ := min_ih_i ≥ 1, W on T^{(k+1)} as on RG1 p.265 l.15–18, U_k(V) the minimal configuration of S(h; ·) for V on T^{(k)}, and U_{k+1} that for W, in the axial gauge (p.265 l.27–28), both given by Lemma 10.12.
   {#B10.200-0} Put 𝐆_h(V) := ½Σ_{y∈T^{(k+1)}}Σ_{x∈B(y), x≠y}|h^{1/2}(1/i)log V(y, x)|², with V(y, x) of RG1 (0.11) and the principal logarithm on χ_k's domain, B^♮ := h^{1/2}B, and write h_B, 𝒫 for RG1's operators h (p.267 l.18–23) and C (p.268 l.2–3), as in #B4.65–#B4.67. The lemma rests on (P-PBG) (#B9.29-3–#B9.29-4) and on Lemma 10.12 (#BFP.160-2).
   {#B10.200-1} For (c), let M be large depending on d, L and G, the side of T^{(k)} be at least 20M and that of the cubes of RG1's (1.12) (#B9.29-4), Mα₀ and RG1's α₀, α₁ be small depending on d, L and G, so that O(1)LMBα₀ + α₁ + α₀ ≤ a_R (#B9.29-4), and B₃ε₁ small depending on G and on α₀′ (#BFL.195-1), α₁ and γ₀ = α₀, and ε₁ small depending on M, so that M′ ≤ M(ε₁) (#B10.177-0), and let 𝒰_RG1 be the set of pairs (𝐔, 𝐉) satisfying RG1's (i)–(iii) (p.262) at scale k, with (1.12) also on the cubes of side 20M (#BX.1-4), and these α₀, α₁, γ₀.
- {#B10.201} (a) exp[−𝐆_h] is a gauge-fixing density for which RG1's derivation of (0.16) holds, so RG1 (2.1) with 𝐆_h(V) + S(h; U_k(V)) in place of g_k^{−2}(𝐆(V) + A(U_k(V))) represents the same transformation; the critical point (2.2) of 𝐆_h + S(h; U_k(·)) on {V̄ = W} is V^{(k)} = M^k(U_{k+1}) (2.3).
- {#B10.202} (b) In RG1 (2.4)–(2.12) for this integral, with B′ = B − h_BD̃(B) and B = h^{−1/2}B^♮, the linear term vanishes, the terms of order 0 are −½⟨B^♮, Δ̂^{(k)}B^♮⟩ with ⟨B^♮, Δ̂^{(k)}B^♮⟩ := ⟨Ĥ₁B^♮, Δ̂₁Ĥ₁B^♮⟩ − 2⟨h^{1/2}Ĥ₁h^{−1/2}h_BC̃^{(2)}(B^♮), J♮⟩ + 𝐆^{(2)}(B^♮), RG1's (1.5) with the operators of Lemma 10.11, and every other term of the exponent of (2.12) is RG1's with S(h; ·), 𝐆_h and S(h; ·)'s J, Δ₁, H₁, V for g_k^{−2}A, g_k^{−2}𝐆 and A's (step 3), and h^{−1/2}𝒫B^♮ in place of g_k𝒫B.
  {#B10.202-1} Those of 𝐏^{(k)} (p.268 l.19–20) have RG1's bounds with θ^{−1/2} in place of g_k; RG1 bounds the E_k-term in braces through (1.18) for the E^{(j)}, j ≤ k (p.272 l.2–3), which for S(h^j) is open (#B10.93, #B10.199-2).
- {#B10.203} (c) At U_{k+1}, 𝒫*Δ̂^{(k)}𝒫 ≥ c_{𝒞,h} with c_{𝒞,h} > 0 depending on d, L and G only; and Ĉ^{(k)} := (𝒫*Δ̂^{(k)}𝒫)^{−1}, as a function of (𝐔, 𝐉) on 𝒰_RG1 with J♮(𝐔, 𝐉) of #B10.177-1 for J♮, has the bound (3.187) with a rate δ₃ > 0 for δ₀ and a convergent expansion, taken at the G-valued factor U of RG1's (i), on which its terms depend as well (#BX.1-5b), and so do the resolvents (xI + 𝒫*Δ̂^{(k)}𝒫)^{−1}, 0 ≤ x ≤ γ₁, of RG2 (2.7) (p.013 l.19–35, RG2's γ₁, not PRT1's), with constants depending on d, L and G only, not on h.

{#B10.204} *Proof.* In balaban_proofs/BP_FAMILY_RG1.md (#BFR.205–#BFR.211-3), not yet through review.

{#B10.212} *Use.* So RG1 (2.12)–(2.14) hold for S(h^k) with dμ_{Ĉ^{(k)}}(B^♮) and the variables h^{−1/2}𝒫B^♮, defining E^{(k+1)} by (2.13); (2.15) becomes h^k = h^{k+1} + β_{k+1} with the C-term of Lemma 10.8(c), the background moving as in Lemmas 10.13–10.15.
{#B10.212-1} That E^{(k+1)} has the properties (1.18)–(1.19) (RG1 §3, RG2) and is Euclidean invariant as in (5.2), which RG1 assumes for the terms of (1.3) (p.263 l.42–45), is open (#B10.93); RG2 §2's localisation of it (p.013 l.30–34) needs expansions of Ĉ^{(k)} and the resolvents whose terms are functions of (𝐔, 𝐉), which #B10.203 does not give; Lemma 10.17 defines β_{k+1,i} and bounds it for an E with these properties, and its value is open (#B10.221).

{#B10.213} **Lemma 10.17 (RG1 §§4–5 for the Family).** Let E = E^{(j)} be a function of RG1 (1.6)–(1.7) on G's configurations, with the localised representation (1.7), the bounds (1.18) and the invariances (1.19), Euclidean invariant as in (5.2), and let Π^{ab}_{μν}(x, x′) be its second derivative at B = 0 as in (5.1) ((1.20) with j for j + 1), and P_i the projection of #B10.177-1. Then:
- {#B10.214} (a) Π^{ab}_{μν}(x, x′) = Σ_i(P_i)^{ab}Π_{i,μν}(x − x′), with Π_i real and Euclidean covariant as in (1.21), (5.4);
- {#B10.215} (b) Π_i satisfies RG1's (5.6)–(5.9), and (5.10) in the form |Π_i(x)| ≤ C(M, κ)E₀e^{−δ_Π|x|}, δ_Π := ½min(δ₁/2, κ(2M)^{−1}) with δ₁ of PBG (3.132) at U = 1; β_i := Σ_xΠ_{i,μν}(x)x_μx_ν, μ ≠ ν, is independent of μ ≠ ν, and |β_i| ≤ C(M, κ)E₀;
- {#B10.216} (c) the marginal terms (4.34) of E, and those of the counterterm Σ_iβ_iÃ_i in place of (4.38), split into sums over i of RG1's terms for G_i with Π_i and β_i, and (θ − θ′)C, C having no quadratic part at 1 (Lemma 10.5(b)), contributes only irrelevant terms; so RG1's cancellation of the marginal terms (§5, with (4.42)–(4.44)) holds for each i with β_i.

{#B10.217} *Proof.* In balaban_proofs/BP_FAMILY_RG1.md (#BFR.218–#BFR.220-2), not yet through review.

{#B10.221} *Use.* Lemma 10.17 applies to the E^{(k+1)} of Lemma 10.16 once E^{(k+1)} has (1.18)–(1.19) and the Euclidean invariance of (5.2), which is open (#B10.212-1). The activities of Lemmas 10.14–10.15 do not change Π (#B10.199), so they leave (a), (b) and β_{k+1,i} unchanged; including them in E for (c) needs their analyticity on RG2's domain, which is open (#B10.199-2).
   {#B10.221-1} Lemma 10.17 then defines β_{k+1,i} per factor with |β_{k+1,i}| ≤ C(M, κ)E₀, which bounds β_max ≥ b (#B10.131), so Lemma 10.14's θ^{−1/2}b ≤ γ holds once θ_k ≥ (C(M, κ)E₀/γ)². The value of β_{k+1,i}, which Theorem 0.1's rates need, is not given by RG1 (p.264 l.32–33) and is open.

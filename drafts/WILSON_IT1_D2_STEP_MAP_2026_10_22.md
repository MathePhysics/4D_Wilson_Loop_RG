# D2: the step map with the Wilson loop insertion

{#MP.1} Companion of WILSON_IT1_LINE_DEFECT_2026_10_21.md (the *IT-1 note*).
{#MP.1-1} Its §4 defines the step-1 class and the target D1.
{#MP.1-2} D2's first two items are in the IT-1 note: §3i (the thin form of E^∂) and §3j (the carrier dependence of the t > 0 species).
{#MP.1-3} This file holds the rest, from D2.0 on.

{#MP.2} *Base file.* The base is WILSON_FIRST_RG_STEP_V4.tex, cited by label, equation tag (e.g. (c4-6-5)) or section.

## WHAT THE CONSTRUCTION IS {#MSWTCI}

- {#MWTCI.1} **After one RG step the Wilson loop is no longer a Wilson loop.** As a function of the block field it is a dressed loop, a line defect: κ^{(k)}e^{𝓔_k}[f_k + Σ_𝔅Q_k(𝔅)·words].
  {#MWTCI.1-1} Here f_k is the holonomy of Bałaban's background U_k(V_k), not of V_k; the words carry gauge-covariant insertions Y_W along C; near large fields it depends on the pending (outer) variables.
  {#MWTCI.1-2} Already V4's leading term is W_χ(C_n;U₁) with U₁ the rebuilt fine field.
- {#MWTCI.2} **Consequences.**
  - {#MWTCI.3} V4's Theorem 1 cannot be iterated: its input is a Wilson loop and its output is not one.
    {#MWTCI.3-1} The induction runs on the class D(k), and everything rests on the step map D(k) → D(k+1) with constants uniform in k (D2.2–D2.4).
  - {#MWTCI.4} Bałaban's construction of the measure is reused unchanged, but none of his estimates control the dressed loop: every fluctuation integral with the loop needs its own cluster expansion (Bałaban/Dimock bound partition functions only).
  - {#MWTCI.5} The dressing has couplings: the perimeter part (grows like L^{K−k}) and the corner part must be absorbed exactly into δm_k and z_k at every step; the deviation insertions must contract (L^{−1}(1+β₀)⁸ per step) and are summed only at k = K.
  - {#MWTCI.6} The words are only gauge-covariant, so the representative of the gauge orbit matters (the representative gap); inside Bałaban's construction it never did.
  - {#MWTCI.7} The dependence on outer variables near large fields means the large-field terms cannot be counted; they are carried as local activities (D2.6).
  - {#MWTCI.8} The answer is E[W(C)] = κ^{(K)}·⟨𝒲_K⟩_final + errors. The continuum limit W^∞(C) exists along the full sequence of lattice spacings for every admissible loop (WILSON_IT1_CONTINUUM_LIMIT_CLOSURE_2026_10_26.md (8.4)), by the Cauchy property across K of the renormalised expectation (WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md #C7.1).
    {#MWTCI.8-1} W^∞(C) is a weak limit point of the stopping-scale effective measures tested against the fixed coarse loop plus a bounded remainder (the continuum note's (8.2), given D(K′) on every labelled term), whose large-field part is at most δ_LFB_LF (its (4.4) and (7), with the Cauchy note's §11).
- {#MWTCI.9} The target stays the bare Wilson loop; the dressing is how its renormalisation is computed, not a change of observable.
- {#MWTCI.10} The distance of the dressed object from the coarse Wilson loop after one step is V4's Proposition prop:coarse-loop-form and Remark rem:coarse-loop-form, after Corollary cor:main-leading-size.
  {#MWTCI.10-4} It uses V4's Lip_χ, giving |W_χ(C_n;V) − W_χ(C_n;U₁)| ≤ Lip_χ(e^{6c_hLn_Cε₁} − 1).
  {#MWTCI.10-5} At one step there is no fluctuation integral left over which the difference could average: both loops are functions of V, and any average is over the coarse ensemble E_h, i.e. the later steps.
- {#MWTCI.11} **That bound is the pointwise bound integrated; it uses no cancellation and is not an expectation-level comparison.** The expectation-level comparison, with the step-2 fluctuation average taken before any absolute value, is the section ONE MORE STEP below.
  {#MWTCI.11-1} There the first-order insertions are even in the coupling at step 2, so their first-order mean vanishes in the interior (away from S₂, the layer Ω₂∖Ω₂^{∼−1} and σ-dependent terms); a size bound is derived (#MOMGD.3): for activities without an old-factor link through the complex-coupling sup (the scaling identity), c_λρ₂·(decay), and for activities with a link through the 𝐄₁ link's absolute radius ε₁^{RG2}/g₁, the same bound.
  {#MWTCI.11-2} The perimeter and corner parts are multiplicative and are defined exactly via D2.3, given its input (S-w) (#MOMGD.5).
  {#MWTCI.11-3} An additive background term Δ_bg remains, of order B₃ε₂L^{−2} per scale-1 bond, and the exponent difference of the two dressings is bounded on the flat term ℓ₀ by (6) and is D2.6's on the other terms.

## ONE STEP: THE COARSE WILSON LOOP AGAINST V4'S LEADING TERM {#MSOSTC}

{#MOSTC.1} *Result.* On A_cov, if s := 2c_hA_Lε₁L^{−2} ≤ 1/10 and t := e^s − 1 ≤ r_G (both hold for g₁ small; V4 prop:coarse-loop-form assumes the same), then |W_χ(C_n;V) − W_χ(C_n;U₁)| ≤ e^{4nc_πξ} − 1 with ξ ≤ 2.12c_hA_Lε₁L^{−2}, A_L ≤ (d−1)(d+4)L²/8; for d = 4, ≤ e^{6.4c_πc_hn_Cε₁/L} − 1.

{#MOSTC.2} *Setting.* V4 Theorem 1, fine units, d = 4 where numbers are given.
{#MOSTC.2-1} C_n has 4n coarse bonds c_0, …, c_{4n−1}.
{#MOSTC.2-2} Each c_j is ±c for a positively oriented coarse bond c, the straight fine path of L bonds from c_− to c_+ = c_− + Le_μ (V4's opening conventions, before (wilson-definition)).
{#MOSTC.2-3} For c_j = −c, V(c_j) = V(c)^{−1} = e^{iX_{c_j}}U₁(c_j): RG1 (0.4) is inverse-consistent, since re-indexing x̃ = x′, Γ̃ = Γ′, Γ̃′ = Γ and the Ad-equivariance of the principal logarithm give X_{−c} = −Ad(U(−c))X_c.
{#MOSTC.2-4} U₁(c) is the product of U₁ along the fine bonds of c (RG1 p.252, "a contour which is obtained by a parallel transport of c"; as at #MOMST.74), so V4's leading word is W_χ(C_n;U₁) = d_π^{−1}tr π(U₁(c_0)⋯U₁(c_{4n−1})), and the coarse Wilson loop is W_χ(C_n;V) = d_π^{−1}tr π(V(c_0)⋯V(c_{4n−1})). ‖·‖ is the operator norm, and c_π := sup{‖π_*(Y)‖ : Y ∈ 𝔤, ‖Y‖ ≤ 1}, a constant of G ⊂ U(N) and π.

{#MOSTC.3} *Inputs.*
- {#MOSTC.4} (I1) CRE (1.12), p.248: U₁ is the critical point of A + 𝐆 on {U = V₀ on Ω₁ᶜ, Ū = V on Ω₁^{(1)}}.
  {#MOSTC.4-1} V4 (B1) determines U₁ by the conditions of CRE (1.12), the critical point of the constrained functional being its minimum (p.248), and V4 Theorem 1(i) fixes RG1 (0.4) as the average.
  {#MOSTC.4-2} So V(c) = Ū₁(c) for every coarse bond c of Ω₁^{(1)}.
- {#MOSTC.5} (I2) RG1 (0.4), p.253: Ū(c) = e^{iX_c}U(c) with X_c := Σ_{x∈B(c_−)}L^{−d}Σ_{Γ∈G(c_−,x)}|G(c_−,x)|^{−1}Σ_{Γ′∈G(c_+,x′)}|G(c_+,x′)|^{−1}(1/i)log U(ℓ), ℓ = ℓ(x,Γ,Γ′) := Γ∪[x,x′]∪(−Γ′)∪(−c), a closed fine loop at c_−, and [x,x′] the translate of c to x.
  {#MOSTC.5-1} The weights are nonnegative and sum to 1, so X_c is a convex combination of the (1/i)log U(ℓ).
- {#MOSTC.6} (I3) RG1 (0.3), p.252: B(y) is the set of fine points of the cube of side L (the coarse spacing) centred at y.
  {#MOSTC.6-1} By (0.3), B(y) = Δ(y) ∩ T^{(n−1)}_{L^{−1}δ} with Δ(y) the cube of side δ centred at y (p.252 l.23–26), so x = y + Σ_νn_νL^{−1}δe_ν with |n_ν|L^{−1}δ ≤ δ/2, i.e. |n_ν| ≤ (L−1)/2 for L odd, and B(y) has L^d points, as (0.4)'s weight L^{−d} requires. The contour construction of p.252 l.28–31 uses only that the n_μ are the coordinates of x − y, not the bound printed there.
  {#MOSTC.6-2} G(y,x) consists of the monotone staircase paths of displacement n, one for each order of the nonzero directions.
- {#MOSTC.7} (I4) V4 Lemma c2-plaquette-deviation: on every branch, ‖U₁(∂p) − 1‖ ≤ 2c_hε₁L^{−2}, with ε₁ = g₁p₀(g₁), for every fine plaquette p with a bond within distance 3R_c of I. On A_cov, Λ_b ⊆ I = Λ₁^* for every contour bond b (V4, *Location* in the proof of Proposition coarse-loop-form, by sec:c3-6; I is the set of free bonds with an endpoint in Λ₁, sec:c5-0), so each coarse bond c of C_n has a site in Λ₁.
  {#MOSTC.7-1} Every bond and plaquette used below lies in the two endpoint blocks of c and the paths between them, within ℓ^∞ distance 2L of that site.
  {#MOSTC.7-2} Lemma collar-coverage(i) puts all sites within ℓ^∞ distance LMR₁ − 1 > 2L of Λ₁ in Ω₁^{∼−1}, so c is a bond of Ω₁^{(1)} and (I1) applies; 3R_c ≥ 3(2R_loc + 1) = 12L + 15 > 8L + 1, so (I4) applies to all those plaquettes.

{#MOSTC.8} *(1) Area of ℓ.* Let Γ₊ be the translate of Γ by Le_μ; it lies in G(c_+,x′), since x′ − c_+ = x − c_−.
- {#MOSTC.9} (a) Γ′ and Γ₊ have the same displacement n.
  {#MOSTC.9-1} Going from the order of Γ′ to that of Γ₊ by adjacent transpositions inverts each pair of directions at most once, and swapping two consecutive straight segments of lengths |n_α|, |n_β| moves the path across |n_α||n_β| plaquettes.
- {#MOSTC.10} (b) Moving [x,x′] back along Γ one bond at a time crosses L plaquettes for a bond of direction ±ν, ν ≠ μ, and none for a bond of direction ±μ: there the two paths agree after cancelling backtracks.
- {#MOSTC.11} So ℓ is contracted to the trivial loop in at most A_L := Σ_{α<β}|n_α||n_β| + L(|n|₁ − |n_μ|) plaquette moves.
  {#MOSTC.11-1} With |n|₁ − |n_μ| ≤ (d−1)(L−1)/2, and Σ_{α<β}|n_α||n_β| ≤ (d−1)d(L−1)²/8 by Cauchy–Schwarz (Σ_{α<β}a_αa_β ≤ (d−1)(Σa)²/(2d), |n|₁ ≤ d(L−1)/2), A_L ≤ (d−1)(d+4)L²/8, i.e. A_L ≤ 3L² for d = 4.

{#MOSTC.12} *(2) Per coarse bond.* A move across a plaquette p multiplies the holonomy at the base point by gU₁(∂p)^{±1}g^{−1}, with g ∈ G the transport from the base point along the current loop.
{#MOSTC.12-1} So U₁(ℓ) is a product of at most A_L such conjugates.
{#MOSTC.12-2} For unitary W and g, ‖gWg^{−1} − 1‖ = ‖W − 1‖ = ‖W^{−1} − 1‖, and ‖∏(1 + a_m) − 1‖ ≤ ∏(1 + ‖a_m‖) − 1, so
  {#MOSTC.13} ‖U₁(ℓ) − 1‖ ≤ (1 + 2c_hε₁L^{−2})^{A_L} − 1 ≤ e^{s} − 1 =: t, s := 2c_hA_Lε₁L^{−2}.
{#MOSTC.14} For unitary W with ‖W − 1‖ ≤ t < 2, the principal logarithm satisfies ‖(1/i)log W‖ ≤ 2arcsin(t/2), since |e^{iφ} − 1| = 2|sin(φ/2)| for φ ∈ (−π, π].
{#MOSTC.14-1} It lies in 𝔤 once t ≤ r_G, the G-dependent radius of V4 prop:coarse-loop-form.
{#MOSTC.14-2} Under t ≤ r_G, X_c ∈ 𝔤 by (I2), ‖X_c‖ ≤ ξ := 2arcsin(t/2), and ‖V(c)U₁(c)^{−1} − 1‖ = ‖e^{iX_c} − 1‖ ≤ 2sin(ξ/2) = t.
{#MOSTC.14-3} For s ≤ 1/10, ξ ≤ 1.06s: t = e^s − 1 ≤ s(1 + s/2 + e^s s²/6) ≤ 1.052s ≤ 0.1052, and 2arcsin(t/2) ≤ t(1 − t²/4)^{−1/2} since arcsin′ is increasing on [0,1), with (1 − t²/4)^{1/2} ≥ 0.9986.
{#MOSTC.14-4} For d = 4: s ≤ 6c_hε₁, ‖V(c)U₁(c)^{−1} − 1‖ ≤ e^{6c_hε₁} − 1 and ‖X_c‖ ≤ 6.4c_hε₁.

{#MOSTC.15} *(3) The loop.* Put R_j := e^{iX_{c_j}}, H_j := U₁(c_0)⋯U₁(c_{j−1}) (H_0 := 1) and R̃_j := H_jR_jH_j^{−1}.
{#MOSTC.15-1} Then V(c_0)⋯V(c_{4n−1}) = R̃_0⋯R̃_{4n−1}·U₁(c_0)⋯U₁(c_{4n−1}).
{#MOSTC.15-2} Since ‖π(e^{iY}) − 1‖ ≤ ‖π_*(Y)‖ ≤ c_π‖Y‖ for Y ∈ 𝔤, and |d_π^{−1}tr((π(R) − 1)π(H))| ≤ ‖π(R) − 1‖ for unitary π(H),
  {#MOSTC.16} |W_χ(C_n;V) − W_χ(C_n;U₁)| ≤ (1 + c_πξ)^{4n} − 1 ≤ e^{4nc_πξ} − 1 ≤ e^{6.4c_πc_hn_Cε₁/L} − 1 on A_cov (d = 4, n_C = 4nL).
{#MOSTC.17} Expanded, the difference is a sum of words with insertions π(R̃_j) − 1 of norm ≤ c_πξ on nonempty sets of coarse bonds, the shape of V4's deviation words, with insertions bounded at first order in the curvature instead of at order ρε₁.

{#MOSTC.18} *(4) In V4's identity.* On A_cov, write W_χ(C_n;U₁) = W_χ(C_n;V) + [W_χ(C_n;U₁) − W_χ(C_n;V)].
{#MOSTC.18-1} Then
  {#MOSTC.19} E_ε[W_χ(C_n)] = κ_{C_n}E_h[1_{A_cov}e^{E°_ξ}W_χ(C_n;V)] + E_coarse + E_def + E_bdry,
  {#MOSTC.20} |E_coarse| ≤ |κ_{C_n}|(e^{6.4c_πc_hn_Cε₁/L} − 1)E_h[1_{A_cov}e^{|E°_ξ|}] ≤ |κ_{C_n}|(e^{6.4c_πc_hn_Cε₁/L} − 1)exp[Cτ²(2 + 1/c) + n_Cδ^I_q],
{#MOSTC.21} the last step by eq:thm-main-moment under the additional hypotheses of Theorem 1(iii), with the Result's conditions s ≤ 1/10 and t ≤ r_G for the pointwise bound on A_cov.

{#MOSTC.22} *(5) What this says.*
- {#MOSTC.23} Per fine contour bond the exponent of the upper bound is 6.4c_πc_hε₁/L = O(L^{−1}g polylog), against C_χρ(ε₁ + e^{−cb/(LM)}) = O(g³ polylog) in V4's bound on E_def (C_χ of (c4-6-8) depends on L, the group and χ, V4 sec:main-result *Notation*).
- {#MOSTC.24} For a loop of fixed physical side ℓ_C, n_C ≈ 4ℓ_C/ε, so the bound is e^{O(L^{−1}g₁p₀(g₁)ℓ_C/ε)} − 1, small for n_C ≪ L/ε₁.
- {#MOSTC.25} The factor L^{−2} of the plaquette bound is V4's lemma for the minimiser U₁ (the proof of V4 Lemma c2-plaquette-deviation; ONE MORE STEP (1)); a general regular field has only 2c_hε₁.
- {#MOSTC.26} The average is RG1's (0.4), which V4 fixes, not RG1's second average (0.12), p.254.

## ONE MORE STEP: THE DRESSED LOOP AGAINST THE COARSE LOOP IN EXPECTATION {#MSOMST}

{#MOMST.1} *What the objects are, and what that forces.*
- {#MOMST.2} D(V₁) := f₁(V₁) − g₁(V₁), with f₁(V₁) := W_χ(C;U₁(V₁)) (V4's leading word) and g₁(V₁) := χ(Hol^{(1)}_C V₁) (the coarse Wilson loop, V4's W_χ(C_n;V)), is a function of the coarse field.
  {#MOMST.2-1} At step 1 nothing averages it.
  {#MOMST.2-2} The first average that can cancel anything is the step-2 fluctuation integral.
  {#MOMST.2-3} Below, D is written exactly in the step-2 variables, and the average is taken before any absolute value.
- {#MOMST.3} **Result** ((5)–(7)).
  {#MOMST.3-1} After the step-2 integral, in the small-field interior, D splits into:
  - {#MOMST.4} (a) a perimeter and corner part.
    {#MOMST.4-1} It is not small: O(g₁²) per scale-1 bond at Gaussian level, so O(g²n_C/L) in total, unbounded as ε → 0 at fixed ℓ_C.
    {#MOMST.4-2} For both loops it is defined exactly as cluster sums (D2.3(5)) and absorbed, given D2.3's input (S-w) (derived, SW closure, its (6c) in the covariance note, #MOMGD.5; from which (T′), (Z) and the Kotecký–Preiss condition follow); for g₁ this is D2.2(5)–(6), D2.3 and D2.4 run on the coarse word, whose insertions have the same structural form as D2.1's (not a special case: M(𝐔)-transports, leading word outside D(2), slots on two blocks; (6), first bullet).
    {#MOMST.4-3} The values are not computed; their Gaussian (linear-insertion) parts are convergent self-energy sums ((6)).
  - {#MOMST.5} (b) an additive background part Δ_bg = f₂ − g̃₂, a function of V₂ and the pending variables.
    {#MOMST.5-1} Its pointwise bound is Lip_χ(e^{ax₁} − 1), where x₁ = 6c_hn_Cε₁/L is the step-1 exponent and a = B₃(ε₂/ε₁)L^{−2} ≤ (1+β₀)B₃L^{−2} ((4); the exponent, not the bound, scales by a).
    {#MOMST.5-2} By (7)(c), each step's background term is at every later step j the same comparison with U_j in place of U₂ plus insertion words, pointwise; the B′ = 0 end at the final scale is O(B₃ℓ_Cε_KL^{−(K−k)}) on the terms whose blocks lie in Ω_K, summing to O(B₃ℓ_Cε_K/L) uniformly in K ≤ N ((7)(d); for K > N the input at step K−1 is D2.7's).
    {#MOMST.5-3} The shed words carry the rest pointwise and are the differences of the two chains' insertion words, averaged at the next step as part of both chains' step maps; the coarse chain's absorption is its own D2.3 at every step, and the normalisation it induces is κ^{g_k,(j)}, with the ratio r_j to the fine chain's bounded ((7)(e), #MOMST.93-7–#MOMST.93-9).
  - {#MOMST.6} (c) averaged insertion activities.
    {#MOMST.6-1} They are even in the coupling at step 2 in the interior scope of (5), so their first-order mean vanishes there.
    {#MOMST.6-2} Class (i), without an old-factor link, and class (ii), with one, are each ≤ c_λρ₂·(decay) per activity, second order with the amplitude 𝔞₂ = max(τ₁², ρ₂·pl) that D2.3 and (S-w) assume (#MOMGD.3); on the real segment class (ii) also has the Lipschitz bound L_F = 2E_Y/ε₁^{RG2} = O(1)E_Y (#MOMST.49-14).
  - {#MOMST.7} The perimeter and corner factors enter multiplicatively, but an additive Δ_bg remains, and it dominates at scale 1.
    {#MOMST.7-1} Schematically (the error terms are (b), (c), and the large fields, bounded in (5)–(7)): E[f₁] ≈ e^{−(δm₂^f−δm₂^g)P₁(C)+4(ζ₂^f−ζ₂^g)}E[g₁] + (b) + (c) + large fields (corner factor (z₂^f/z₂^g)⁴ with z = e^ζ, D2.3(5), (8)).
- {#MOMST.8} **Consequence for the RG construction** ((7)).
  {#MOMST.8-1} Pointwise at step k+1 the background term is P_k(C)·O(ε_{k+1}L^{−2}) = O(ℓ_Cε_{k+1}L^{K−k−2}), small only on the last ≈ 2 + log(1/(ℓ_Cε_{k+1}))/log L steps.
  {#MOMST.8-2} By (7)(c), at each later step the term splits again, pointwise, into a background part and insertion words, and the background part at the final scale is W_χ(C;U_K) − W_χ(C^{(k)};M^kU_K) = O(B₃ℓ_Cε_KL^{−(K−k)}) by (7)(a)–(d), the iterated-average lemma, on the terms whose blocks lie in Ω_K; summed over the steps this is O(B₃ℓ_Cε_K/L), uniformly in the number of steps K ≤ N (for K > N the input at step K−1 is D2.7's).
  {#MOMST.8-3} What survives in expectation is E[W(C)] − N_k⟨g_k^{(k)}⟩_k = κ_f^{(K)}⟨e^{𝓔^f_K}β_k^{(K)}⟩_K^{good} + (the exponent difference) + (the insertion difference) + R_bad, with N_k and the ratios r_j of #MOMST.93-9 and #MOMST.93-12 and R_bad the whole-label term of #MOMST.93-10–#MOMST.93-11 ((7)(e)); at k = K the chain is trivial and only the fine chain is needed (#MOMST.93-14, #MOMGD.2). For k < K at K > N it also needs (iii-d) (#MOMST.73-1).

{#MOMST.9} *(0) Units.* Bałaban's step-1 units: block spacing 1, fine spacing η = L^{−1}.
{#MOMST.9-1} V4's C_n has P₁(C) = 4n scale-1 bonds c_j and n_C = 4nL fine bonds.
{#MOMST.9-2} Norms: ‖·‖ the operator norm, |·| CRE's matrix norm, ‖Y‖ ≤ c_h|Y| (the *Conventions* paragraph of V4 sec:sourced-effective-interaction; c_h compares h(Y) = (N^{−1}tr Y*Y)^{1/2} in a faithful N-dimensional unitary representation, for any compact G ⊂ U(N)).

{#MOMST.10} *(1) The step-1 plaquette bound loses L² (derived from the proof of V4 Lemma lem:c2-plaquette-deviation).*
- {#MOMST.11} The proof has sup_{p′⊂□′^∼}|U_{1,□′}(∂p′) − 1| < ε₁L^{−2} for the local minimum, and ‖U₁(e) − U_{1,□′}(e)‖ ≤ c_hO(1)B₃e^{−δ_cLM₂R₁}ε₁ on the bonds of □′^{∼2}.
  {#MOMST.11-1} The V4 proof bounds the second by c_hε₁L^{−2}/4.
- {#MOMST.12} Keep the exponential: ‖U₁(∂p) − 1‖ ≤ c_hε₁L^{−2} + 4c_hO(1)B₃e^{−δ_cLM₂R₁}ε₁ ≤ 2c_hε₁L^{−2} once 4O(1)B₃L²e^{−δ_cLM₂R₁} ≤ 1, a condition on g₀ (R₁ → ∞ as g₀ → 0, V4's own threshold argument).
- {#MOMST.13} In prop:coarse-loop-form this gives s = 6c_hε₁ in place of 6c_hL²ε₁, and (iii) becomes |f₁ − g₁| ≤ Lip_χ(e^{6c_hn_Cε₁/L} − 1): per scale-1 bond O(ε₁), the curvature of one coarse plaquette.
  {#MOMST.13-1} V4's Lemma lem:c2-plaquette-deviation proves the sharpened bound, and Proposition prop:coarse-loop-form carries s = 6c_hε₁.

{#MOMST.14} *(2) The step-2 variables (D2.1(1)).*
- {#MOMST.15} CRE (3.10)–(3.11), p.266: V^{(1)} = M(U₂) on Ω₂^{(1)}, and V₁ = e^{iB′}V^{(1)} on B(Γ₂).
  {#MOMST.15-1} RG1 pp.267–268: B′ = g₁CA − hD̃(g₁CA), with A the scaled fluctuation (B in RG1 (2.12)) and C the operator that eliminates the variables B′(b₀(c)) through the constraint on the corridor B(c).
- {#MOMST.16} RG1 (2.12)–(2.13), p.268: the step-2 integral is ∫dμ_{C^{(1)}}(A)χ₁exp[P^{(1)}(g₁,U₂,A) + {𝐄₁(U₁(e^{iB′}V^{(1)})) − 𝐄₁(U₁(V^{(1)}))}], with μ_{C^{(1)}} the centred Gaussian of covariance (C*Δ^{(1)}C)^{−1}.
  {#MOMST.16-1} RG1 p.267: the linear term vanishes, "−(1/g_k)⟨H₁B′,J⟩ = 0", since U₂ is the constrained critical point.
  {#MOMST.16-2} RG1 p.268: "the expression under the exponential above vanishes at g_k = 0".
- {#MOMST.17} CRE (3.16), p.268: the small-field cutoff is χ^{(1)}(R₂ᶜ) = ∏_{□′}χ({sup_{b∈(□′^{∼2})^{(1)*}}|A₁(b)| < δ₁}).
  {#MOMST.17-1} The R^c factor is a product (corrected p.268 l.18; the raw transcription has Σ): the second line of (3.16) writes it as the single function χ^{(k)}(R^c_{k+1}), and the first step's (1.18) prints ∏ on R₁^c (p.250 l.29).
  {#MOMST.17-2} A₁ in (3.16) is the variable after p.267 l.42's scaling A_k′ = g_kA_k, so the test is |A| < δ₁; since g₁ < 1 it gives g₁|A| < δ₁, i.e. |A| < δ₁/g₁ =: r₁, which is the form of the first step's printed test |A| < g₀^{−1}δ₀ ((1.18), p.250 l.29). (5) uses only this consequence, as an upper bound on the support.
- {#MOMST.18} χ′₁.
  {#MOMST.18-1} CRE p.268: "the characteristic functions χ_k′ depend now on the field V^{(k)} … We want to have characteristic functions depending on the fluctuation field only".
  {#MOMST.18-2} So χ′₁ is a function of A₁ and V^{(1)}.
  {#MOMST.18-3} On cubes of R₂ᶜ it is 1 on the support of χ^{(1)}(R₂ᶜ); on R₂ and on Ω₂∖Ω₂^{∼−1} it remains.
- {#MOMST.19} RG1 (2.12) is quoted for the single-domain case.
  {#MOMST.19-1} CRE's multi-domain (3.15), pp.267–268, has more in the curly bracket: the 𝐑₁, 𝐁₁ and A(1/g₁²(·) − 1/g₁², ·) differences, and the factor χ′₁(Ω₂).
  {#MOMST.19-2} They are functions of B′ with coefficients that are not substituted in (5), so (5)'s parity is unchanged in the interior.
- {#MOMST.20} Multi-domain operators through CRE p.267's transfer, accepted as Bałaban's statement, as in D2.1(1).

{#MOMST.21} *(3) The exact decomposition (D2.1(2), with CRE (3.6), #MD2.1.2.1).*
- {#MOMST.22} Dressed loop: D2.1(2), (4) give f₁(e^{iB′}V^{(1)}) = f₂ + Σ_{𝔊≠∅}d_π^{−1}tr(Y_{G₁}U_{(1)}⋯Y_{G_n}U_{(n)}), with f₂ := χ(Hol_CU₂) and every Y_G vanishing at B′ = 0.
- {#MOMST.23} Coarse loop: the transport identity of D2.1(3) on the scale-1 lattice gives Hol^{(1)}_C(e^{iB′}V^{(1)}) = ∏_jexp(iAd(Γ_j)B′(c_j))·Hol^{(1)}_C(V^{(1)}), Γ_j the V^{(1)}-transports.
  {#MOMST.23-1} Writing each factor as 1 + (e^{iX_j} − 1) gives g₁(e^{iB′}V^{(1)}) = g̃₂ + Σ_{S≠∅}(words with factors e^{iX_j} − 1 on the bonds j ∈ S), with g̃₂ := χ(Hol^{(1)}_CM(U₂)).
  {#MOMST.23-2} Each factor vanishes at B′ = 0, and e^{iB′(c_j)} − 1 depends on A near c_j (on a designated bond b₀(c′) ⊂ C, B′(b₀(c′)) depends on the corridor B(c′), still local; the transports Γ_j do not depend on A). g̃₂ is the value at B′ = 0 only where C ⊂ B(Γ₂); elsewhere V₁'s pending values appear in place of M(U₂).
- {#MOMST.24} So D = Δ_bg + [Σ f-words − Σ g-words], with Δ_bg := f₂ − g̃₂ = W_χ(C;U₂) − W_χ(C^{(1)};M(U₂)), a function of V₂ and the pending variables only.

{#MOMST.25} *(4) The background term.*
- {#MOMST.26} Δ_bg is prop:coarse-loop-form's comparison with (U₁, V) replaced by (U₂, M(U₂)).
  {#MOMST.26-1} Here V^{(1)}(c) = M(U₂,c) holds by definition, so the location step is not needed.
- {#MOMST.27} Plaquette input: CRE p.268, |∂U₂ − 1| < 2B₃ε₂(L^{−1}η)² on Ω₂, with η = L^{−1}.
  {#MOMST.27-1} So ‖U₂(∂p) − 1‖ ≤ 2c_hB₃ε₂L^{−4} for the fine plaquettes of Ω₂. The plaquettes of Ω₂ are those that intersect Ω₂ (CRE p.255 l.20–21 refers to Sect. 0 [I], which is RG I p.251 l.26–28), so they include every fine plaquette with all vertices in Ω₂.
- {#MOMST.28} If every scale-1 bond c_j of C has its two blocks in Ω₂: for each c_j the Area, One loop, One coarse bond and Loop steps of the proposition give the insertion bound t₂ = e^{s₂} − 1, with s₂ := 3L²·2c_hB₃ε₂L^{−4} = 6c_hB₃ε₂L^{−2}, under s₂ ≤ 1/10 and t₂ ≤ r_G.
  {#MOMST.28-1} Hence
  {#MOMST.29} |Δ_bg| ≤ Lip_χ(e^{4ns₂} − 1) = Lip_χ(e^{6c_hB₃n_Cε₂L^{−3}} − 1).
- {#MOMST.30} Against (1): the exponent changes by the factor B₃(ε₂/ε₁)L^{−2} ≤ (1+β₀)B₃L^{−2}, by CRE (2.8), p.256, first line at n − m = 1: ε_n ≤ (1+β₀)(n−m)^{1/2}ε_m.
  {#MOMST.30-1} The per-step factor is never iterated ((7)(c)–(d)), so no comparison of (1+β₀)B₃ with L² is used (B₃ depends on L, VAR Theorem 1, p.279). Per scale-1 bond the term is one scale-1 plaquette of U₂, O(ε₂L^{−2}), as in D2.0(2)'s coarse-plaquette bound.
- {#MOMST.31} Where a block of C meets Ω₂ᶜ, the term is D2.6's (step-2 large fields).
- {#MOMST.32} Δ_bg is not averaged at step 2; (7) carries it to the later steps and the final scale.

{#MOMST.33} *(5) Parity in the coupling: the first-order parts average out (RG1 (2.12), CRE (3.16)).*
- {#MOMST.34} Fix the background (V₂, the pending data, U₂) and the cutoffs.
  {#MOMST.34-1} For λ ∈ ℂ, replace g₁ by λ in every occurrence of g₁CA (and g₁A in 𝐆₃) and in every prefactor g₁^{−2} in RG1 (2.12), and in B′ = λCA − hD̃(λCA) inside the insertions.
  {#MOMST.34-2} Call the exponent W(λ,A).
- {#MOMST.35} Term by term, (2.12) consists of functions of λCA alone (Tr log(I − h(δD̃/δB)(λCA)), log σ, the 𝐄₁ difference) and of λ^{−2}F(λCA) with F analytic and starting at third order (𝐆₃, ⟨H₁hD̃₃,J⟩, the two D̃ cross terms, V).
  {#MOMST.35-1} Hence W(−λ,−A) = W(λ,A), W(0,A) = 0, and W is analytic at λ = 0.
  {#MOMST.35-2} The insertions Y_G and e^{iX_j} − 1 have the same symmetry and vanish at λ = 0.
  {#MOMST.35-3} Each localised potential V(Y,·) of RG2's expansion vanishes at λ = 0 too, since the localisation is linear in the function (closure a1), so a Mayer factor of a λ-dependent exponent vanishes at λ = 0.
- {#MOMST.36} μ_{C^{(1)}} is centred Gaussian.
  {#MOMST.36-1} RG2's s-interpolated "measures" are complex at complex s (RG2 p.15); they are symmetric under X → −X: the integrand couples B and X bilinearly through exp(−⟨B, Γ_kX⟩) (RG2 (2.6), (2.14)) with dμ₀ and dμ_C symmetric, so it is invariant under (B, X) → (−B, −X) (RG2 p.13's representation through [13] (3.185) is used as Bałaban's).
  {#MOMST.36-2} CRE (3.16)'s cutoff is invariant under A → −A, since it tests |A(b)| bond by bond.
- {#MOMST.37} *Scope.* The parity holds for the activities K(λ) of D2.2(5)–(6)'s joint cluster expansion that contain an insertion factor or a Mayer factor of a λ-dependent exponent (so that K(0) = 0) and are supported in Ω₂^{∼−1}∖R₂, away from S₂, with ω′ = 0 (σ-independent).
  {#MOMST.37-1} There χ′₁ = 1 on (3.16)'s support (p.268), and the substitution A → −A gives K(−λ) = K(λ), K(0) = 0.
  {#MOMST.37-2} It fails, and these activities are D2.6's, for:
  - {#MOMST.38} activities meeting the layer Ω₂∖Ω₂^{∼−1}, where the χ′₁ tests of V₁(V^{(1)}_{□′})^{−1} remain and are not invariant;
  - {#MOMST.39} activities meeting S₂, through ψ₂'s change of variables, its Jacobian and V^{(1)}(S₂, …);
  - {#MOMST.40} σ-dependent activities, through the cross term −⟨A, C*Δ^{(1)}Cσ⟩, which is linear in A (D2.2(5)(e), (6)(b6)).
- {#MOMST.41} *Checked separately:* the χᶜ pieces inside the small-field activities.
  {#MOMST.41-1} RG2 (2.14), p.15, has (−1)^{|P|}χ_{k,Y₀}(B)χ^c_{k,P}(B) inside the activities, and (2.26), p.17, shows these carry exp(−½γ₂ε₁²|P|/g_k²).
  {#MOMST.41-2} Their parity needs the χ^c test to be even in B. χ^c_{1,P} is even by RG2 (2.3), p.12, a product of single-bond tests (class closure b5(4); #MOMGD.3).
- {#MOMST.42} *Radius.* On the cutoff's support |A| < r₁ (#MOMST.17-2), so |λA| < |λ|r₁ (RG2 and closure a2 state their domains in g|B|, here |λA|; C enters only through C₁^{RG2}).
  {#MOMST.42-1} Two classes of interior activities:
  - {#MOMST.43} (i) *No old-factor link:* the activity contains only the leading-word and coarse insertions, the links of the λ^{−2}F terms of (2.12), the links of Tr log(I − h(δD̃/δB)(λCA)) and of log σ, and the Gaussian parts.
    {#MOMST.43-1} These are analytic for |λA| ≤ ε′, so for |λ| < λ_* (ε′, λ_* of #T3.37; class-activities closure a2), and g₁/λ_* = δ₁/ε′ → 0.
    {#MOMST.43-2} RG1 p.267's solution D̃ is analytic without a stated radius, but RG2 (1.19)–(1.20) contain hD̃(g₁CB) and hold for g₁|B| < ε₁^{RG2}, so D̃'s radius in the scaled variable is at least ε₁^{RG2}, fixed before the coupling (closure a2; the equation for D̃ on p.267 has no coupling in it).
  - {#MOMST.44} (ii) *At least one old-factor link:* the old factors of (2.12) and CRE (3.15) are evaluated at U₁(e^{iB′(λ)}V^{(1)}) = e^{iη𝐇}U₂.
    {#MOMST.44-1} The 𝐄₁ difference is an RG2 Lemma 1 term, analytic for |B| < ε₁^{RG2}g₁^{−1} (RG2 (1.34)) with ε₁^{RG2} absolute (the closure's Premise: the step-1 interior terms are analytic on RG1's absolute widths, from CRE (1.26) and RG2 p.10; RG2 p.7's 4B₀C₁e^{16κ₁}ε₁ ≤ ¼α₂ with RG1's absolute α₂), so it has class (i)'s radius (closure b1, b4; #MOMST.47).
    {#MOMST.44-2} The 𝐑₁ difference does not occur for k ≤ N_k (LFR I p.177 (ii); D2.7 item 1(a)–(b)).
    {#MOMST.44-3} The 𝐁₁ and A(·) differences and V^{(1)}(S₂), whose analyticity space is CRE (3.43), are analytic only while the deformation stays inside the α_{1,1}-margin (D2.2(4)(f): 1/T_Y ≥ 16B₀e^{16κ_s}|B′|_Y/(min(β,1)α_{1,k})).
    {#MOMST.44-4} With |B′| ≤ C₁^{RG2}|λCA| (‖C‖ = O(1) absorbed in C₁^{RG2}) this gives for them the radius λ_α := ρ_αg₁/δ₁, ρ_α := r_{α,1}/C₁^{RG2} (#T3.36), and g₁/λ_α = δ₁/ρ_α = O((log g₁^{−2})^{p₀−q₁}), which tends to 0 under q₀ = q₁ > p₀.
    {#MOMST.44-5} For these links (D2.6's, by b5) the radius ε′g₁/δ₁ of (i) is not an analyticity radius.
- {#MOMST.45} Even and vanishing at 0 means K(λ) = ψ(λ²) with ψ(0) = 0.
  {#MOMST.45-1} For any λ′ below the class's radius (the sup is taken on a circle inside the domain), the Schwarz lemma gives
  {#MOMST.46} |K(g₁)| ≤ (g₁/λ′)²·sup_{|λ|=λ′}|K(λ)|,
  {#MOMST.47} so for a fixed λ′ = θλ_*, θ < 1, the gain is (δ₁/(θε′))²·sup_{|λ|=λ′}|K(λ)| for class (i) (the sup ≤ (C₁^{RG2}θε′/ε_H)·(D2.4(10)'s factors) by closure a1's identity 𝐕₁^{[λ]}(Y,B) = ½⟨Q(Y,B̃)B,B⟩ + 𝐕₁″(Y,B̃), B̃ = (λ/g₁)B, for the potentials, class-activities closure a1–a4; the product is c_λρ₂·(decay), a6).
  {#MOMST.47-1} For a link with analyticity space CRE (3.43) (𝐁₁, A(·), V^{(1)}(S₂); D2.6's by b5) the same step with λ′ = θλ_α (it needs λ_α > g₁, i.e. ρ_α > δ₁, true for g small under q₁ > p₀) gives only (δ₁/(θρ_α))² = O(polylog), and the sup on |λ| = λ′ contains the insertion at |λA| ≈ ρ_α ∝ g₁, so this step gives O(g₁·polylog)·S_F for such a link.
  {#MOMST.47-2} Class (ii) takes λ′ = θλ_* as class (i) does, by #MOMST.44-1–#MOMST.44-2, and gets the same c_λρ₂ (closure b1, b4).
  {#MOMST.48} Pointwise, a single first-order insertion has size up to C₁^{RG2}δ₁/ε_H (D2.1(4) Claim, |B′|/ε_H), with δ₁ = A₁ĝ₁(log ĝ₁^{−2})^{p₀} ≤ g₁r₁ (#MD2.4.11.2-1, #MD2.4.11.2-3) on the support |A| < δ₁/g₁ ≤ r₁.
  {#MOMST.48-1} For class (i) the step-2 integral gains one more factor of order δ₁/ε′.
  {#MOMST.48-2} At the Gaussian level the first-order mean is 0 and the second-order mean is O(g₁²).
- {#MOMST.49} *Class (ii) is second order: the 𝐄₁ link's domain is RG2 Lemma 1's disc, radius ε₁^{RG2}/g₁, with ε₁^{RG2} absolute (class-activities closure b1–b4 and its Premise).* The Premise: the step-1 interior terms 𝐄^{(1)}(X, ·) are analytic on RG1's absolute-width space U₁^c(X, α₀, α₁), since they carry no earlier 𝐄 (CRE (1.26)), their background enters through the 𝐏-terms on absolute widths (RG2 p.10) and through C^{(0)}(Λ₁), a restricted covariance of RG2's kind (pp.12–13), and the cube tests act on the integration variable only, entering through (2.22) and Lemma 3 with r₀ = g₀^{−1}δ₀.
  {#MOMST.49-1} Bałaban's treatment of the exterior coupling is accepted (CRE pp.253–254, the k = 0 instance of RG2's numbering of [I]).
  {#MOMST.49-2} So RG1's shift width α₂ is absolute for the interior 𝐄^{(1)} (RG1 p.263, Theorem 3, p.264, (3.13)–(3.14)), and RG2 p.7's 4B₀C₁e^{16κ₁}ε₁ ≤ ¼α₂ fixes ε₁^{RG2} before the coupling. An old-factor link is a Mayer factor of the 𝐄₁ difference (or, in CRE (3.15), of the 𝐑₁, 𝐁₁, A(·) differences) localised to the polymer; call it F(B′) (an exponential factor equals 1 at B′ = 0 and is not a link).
  {#MOMST.49-3} It vanishes at B′ = 0 (RG1 (3.4), 𝐇₁(0) = 0 by RG2 (1.21)); the 𝐄₁ difference's terms are analytic on |B|_Y < ε₁^{RG2}/g₁ with |F| ≤ E_Y (Lemma 1, (1.33)–(1.36); the multi-domain case by CRE p.276's first clause, RG2's numbering of [I], #MD2.2.5.12; at a general step k this clause's interior width is compatible with (2.28)'s g-scaled widths by #MOMGD.49's inequality, under (q₀ = q₁ > p₀));
  {#MOMST.49-4} the 𝐑₁ difference is absent from the basic step of 𝐑 for k ≤ N by LFR I p.177 (ii), and no other part of 𝐑 acts either: D2.7 item 1(a)–(b) (derived) gives 𝐑′^{(k)} = 0 and Rρ_k = ρ_k term by term for k ≤ N_k, since the admissible domains of 𝐑′^{(k)} "contain at least one large field region connected with one of the 𝐓′_k-operations", LFR II p.390 l.10–11). The α_{1,1}-domain of D2.2(4)(f), |B′|_Y < r_α := r_{α,1} (#T3.36; in the units in which |B′| ≤ C₁^{RG2}g₁|A|, r_α ∝ g₁(log g₁^{−2})^{q₁}), is the complex domain of the touched old insertions (the α-disc).
  {#MOMST.49-14} Lemma 1's disc gives both bounds the activity needs (closure b3): Schwarz in the field gives |F(B)| ≤ E_Yg₁|B|_Y/ε₁^{RG2}, hence (α) S_F := sup|F| on the α-disc ≤ 2E_Yr_α/ε₁^{RG2} = O(g₁(log g₁^{−2})^{q₁})E_Y and (β) |F(B′)| ≤ L_F|B′|_Y on the real segment |B′|_Y ≤ C₁^{RG2}δ₁ with L_F = 2E_Y/ε₁^{RG2} = O(1)E_Y, using |B′|_Y ≥ g₁|B|_Y: B′ = g₁B on the non-designated bonds, since hB vanishes off {b₀(c)} (RG1 p.267) and B denotes the remaining variables after B′(b₀(c)) is eliminated (RG1 p.268); RG2 (1.20) is an upper bound only and is not used here.
  {#MOMST.49-17} The deviation part of such an activity is D2.4(4)'s.
  {#MOMST.49-18} The Schwarz step in λ applies to class (ii) with class (i)'s λ′ = θε′g₁/δ₁, since on |λ| ≤ λ′ the link is 𝐕₁′(Y,B̃) with g₁|B̃| ≤ θε′ < ε₁^{RG2} inside Lemma 1's disc, giving c_λρ₂·(decay) directly (closure b4); the real point lies at the fraction x_E := δ₁/ε₁^{RG2} = O(g₁(log g₁^{−2})^{p₀}) of the link's radius.
- {#MOMGD.3} *The class bound* (closure a5–a7). Ĥ^{[λ]}(M) is analytic on |λ| < λ_*, even (B̃ = (λ/g₁)B is invariant under (λ, B, X) ↦ (−λ, −B, −X)), and zero at λ = 0. On |λ| = λ′ each marked activity obeys its bound with (S-w)'s decay factors and D2.4(12)'s entropy count, with single-slot amplitude C₁^{RG2}θε′/ε_H (fine) or 2.12c_πc_hC₁^{RG2}θε′ (coarse) (#MOMST.50-1–#MOMST.50-2).
  {#MOMGD.3-1} So #MOMST.46 gives |Ĥ(M)| ≤ c_λρ₂·(D2.4(10)'s factors)·e^{−(κ_s−3)#(G)}, with c_λ of #T4.46 (δ₁² = g₁²r₁² ≤ ρ₁/C_ρ, A₁² inside r₁²), for the single-component single-slot polymers; the others are ρ₂-size by D2.4(11)(e). Count × size × weight per bond is O(ρ₂), and D2.3 absorbs the perimeter term into δm₂. So the second-order amplitude 𝔞₂ = max(τ₁², ρ₂·pl) that D2.3 and (S-w) assume holds for the coarse gas as for the fine one.
  {#MOMGD.3-2} Constant conditions: θ fixed, ε′ fixed before the coupling, δ₁ < θε′ and 8C₂O(1)²δ₁ ≤ 1 (smallness of g₁, uniform in the step through g₁ ≤ (1+β₀)g_K), RG2's conditions with RG2 Lemma 3's repair, D2.1(4) *Constants*, D2.4(11)(d), (12), and 2c_πc_hC₁^{RG2}ε′ ≤ 1/10 (implied by ε′'s definition).
- {#MOMST.50} Uses: the form of RG1 (2.12) (multi-domain through CRE p.267), the symmetry of μ and of (3.16).
  {#MOMST.50-1} The Kotecký–Preiss condition of the deformed vacuum gas and the marked-activity bounds at complex coupling on |λ| ≤ λ′ hold for both classes (class-activities closure a3–a4); a5–a6 use only these two statements.
  {#MOMST.50-2} D2.4's (S-w) (with its consequence (T′)) is stated at real coupling; its complex-coupling version is RG2 (2.19)–(2.26) and Lemma 3 verbatim at B̃ = (λ/g₁)B inside Lemma 2's disc, by closure a1's identity for the potentials (𝐕₁^{[λ]}(Y,B) = ½⟨Q(Y,B̃)B,B⟩ + 𝐕₁″(Y,B̃)), the Gaussian domination of the λ^{−2}F terms at complex λ being (2.19)–(2.25) at B̃.
  {#MOMST.50-3} Large-field terms at step 2 (R₂ ≠ ∅, χ^{(1)c}) and the excluded activities of *Scope* are D2.6's (closure b5), and so are: links to 𝐁₁, A(g₁^{−2}(·) − g₁^{−2}, ·), and V^{(1)}(S₂), analytic on O6's 𝒫_1^m (#MD2.2.6.170-3), so with radius λ_α in λ (#MOMST.44-4; (3.43)'s A-radius C₁p₁(g₁) is not used, O6 closure §7); domains meeting Z₁^∼, Z₁, or S₂, which are att(2, coll) by D2.6 closure §2.1 and §2.3; and touched old insertions, second order by sup norm (D2.4(11)(c)(β), (e)).

{#MOMST.51} *(6) The perimeter part and the comparison after step 2 ((5), with D2.2–D2.3 applied to g₁).*
- {#MOMST.52} *g₁'s step-2 expansion.* By (3), g₁(e^{iB′}V^{(1)}) = d_π^{−1}tr∏_j(1 + X_j)π(V^{(1)}(c_j)) in loop order, where C ⊂ B(Γ₂), X_j := π(e^{iB′(c_j)}) − 1 for a positively traversed c_j and X_j := π(V^{(1)}(c_j)e^{−iB′(−c_j)}V^{(1)}(c_j)^{−1}) − 1 for a negatively traversed one: a closed word X₁U₁X₂U₂⋯ of D2.2(5)(a)'s form, with the slots at the scale-1 bonds c_j and U_j = π(V^{(1)}(c_j)), V^{(1)} = M(U₂), a function of U₂ only.
  {#MOMST.52-1} D2.2(5) uses of the insertions only that each depends on A on a bounded domain D_j through B′ ((5)(a), (c): D_J^#, the (2.9)–(2.10) linking), and boundedness on the support ((5)(e)); D2.2(6) uses covariance and analyticity in the slot variables; D2.3 uses Schur at the flat reference and contour locality; D2.4 uses the per-slot size.
  {#MOMST.52-2} For X_j: it depends on A through B′(c_j) only, B′ being the local function of A of RG1 (3.2) (RG2 p.3; D2.1(4)(b)'s "locality of B′ in B"), so D_j is the π₁-hull of the bonds on which B′(c_j) depends (c_j, or the corridor of c_j if c_j is a designated bond b₀(c′), (3)); it carries no s-parameter and no propagator; ‖X_j‖ ≤ e^{c_πc_h|B′(c_j)|} − 1 ≤ 1.06c_πc_h|B′(c_j)| ≤ 1.06c_πc_hC₁^{RG2}g₁|A|_{D_j} on the support at real points (c_h from the norm convention of (0), V4 sec:sourced-effective-interaction *Conventions*; the 1.06 needs c_πc_hC₁^{RG2}ε′ ≤ 1/10, which closure a2's ε′ ≤ (20c_πc_hC₁^{RG2})^{−1} gives);
  {#MOMST.52-3} at complex points ‖X_j‖ ≤ 2.12c_πc_h|B′(c_j)| under 2c_πc_hC₁^{RG2}ε′ ≤ 1/10 (also given by closure a2's ε′), and X_j is entire in B′(c_j); it is covariant, X_j^u = π(u(c_{j−}))X_jπ(u(c_{j−}))^{−1}, by the formula RG1 (0.4) for M (log is Ad-covariant; (0.6) is the covariance of the set average) and the covariance of B′ (D2.2(6)(b)); at the flat reference U₂ = 1 the words are invariant under constant gauge transformations, so Schur applies as in D2.3(2); X_j depends on C only through c_j.
  {#MOMST.52-4} So D2.2(5)–(6), D2.3 and D2.4 run with the slot set {c_j} and the per-slot factor 2.12c_πc_hC₁^{RG2}|λA|_{D_j} at complex λ (1.06c_πc_hC₁^{RG2}g₁|A|_{D_j} at the real point) in place of D2.1(4)'s Claim, with three changes: the transports between slots are M(U₂)-transports, so D2.3(2)'s split uses T_{M(𝐔)}(I) in place of T_𝐔(I) ((6)(b)'s covariance covers it since M is covariant); the leading word is g̃₂, outside D(2) ((7)(e)(i)); and the coarse slots depend on U₂ through M(U₂) on the two blocks of c_j, which enlarges X(𝒢) and ℓ_X by those blocks in D2.4's (LPG′)/Cauchy step.
  {#MOMST.52-5} The output is the display below with δm₂^g, ζ₂^g, E°_2^g and g̃₂'s deviation words, given the same input (S-w) for the coarse gas (SW closure with the three changes of the first bullet, #MOMGD.5; (T′), (Z), and the Kotecký–Preiss condition follow from it), which has fewer and simpler slot factors than f₁'s.
- {#MOMST.53} The cluster series of D2.3(5) at the flat background is Π₂-periodic along a side, not translation invariant (D2.3(4), translation covariance (RTR)).
  {#MOMST.53-1} On sides whose length is commensurate with Π₂ its flat part equals P₁(C)μ^f + 4ζ^f + E°_2^f(C,T) for f₁ and P₁(C)μ^g + 4ζ^g + E°_2^g(C,T) for g₁ (D2.3(8): log S°(ℓ₀) = P₁(C)μ + 4ζ + E°₂(C,T)), with μ = (4Π₂)^{−1}Σ_{v∈𝒱_□}κ_v the average of the period sums κ_v over the orientations of C's sides (all four sides have the same length; μ = −δm₂, D2.3(5)), 4ζ the corner part, and E°₂ the corner and torus remainder, bounded by D2.3(6)(a) and not zero; what vanishes at the flat reference are the deviation words of the bracket, not part of the series.
  {#MOMST.53-2} D2.3 absorbs the flat parts exactly into δm₂, ζ₂, separately for the two loops, given its input (S-w) (SW closure, #MOMGD.5).
  {#MOMST.53-3} By (5), μ^f − μ^g is a sum of interior activities, each ≤ c_λρ₂·(decay) (#MOMGD.3).
- {#MOMST.54} Gaussian (linear-insertion) level, flat background (the colour covariance is δ^{ab} there): the second-order mean of d_π^{−1}tr π(∏_ie^{iX_i}) with the insertions replaced by their linear parts is −(C₂(π)/(2d_G))Σ_{i,i′}E⟨X_i,X_{i′}⟩, with C₂(π) the Casimir of π in the normalisation π_*(t^a)π_*(t^a) = C₂(π)·1 for an orthonormal basis t^a of 𝔤 in ⟨·,·⟩, and d_G = dim 𝔤.
  {#MOMST.54-1} The sum runs over the fine bonds with X_i = η(H_{1,1}B′)(b_i) for f₁, and over the scale-1 bonds with X_j = B′(c_j) for g₁.
  {#MOMST.54-2} RG1 (2.6) writes 𝐇 as H_{1,k}B′ + 𝐀_{1,k}, the representation of VAR (174), ℋ = 𝒜₁ + H₁B − HD(𝒜₁ + H₁B) (RG1 p.265 refers 𝐇_k's properties to "Sect. G [15]", which is VAR's; RG1 p.266 l.32 cites its (171) for ⟨𝐀₁, J⟩ = 0).
  {#MOMST.54-3} 𝐀_{1,1} has no part linear in B′: VAR p.306 l.2–4 prints that the expansion of 𝒜₁ "begins with a term of second order in H₁B", (176), and (177) gives ℋ = H₁B + (second order) + ⋯. So X_i = η(H_{1,1}B′)(b_i) is the whole linear part.
  {#MOMST.54-4} The bounds below use H_{1,1}'s own random-walk expansion (PBG p.427), not RG2's H₀.
  {#MOMST.54-5} So the Gaussian (linear-insertion) part of μ^f − μ^g, per scale-1 bond, is −(C₂(π)/(2d_G))[L·Σ_mE⟨X^f_0,X^f_m⟩ − Σ_mE⟨X^g_0,X^g_m⟩], the self-energy sums along a straight line; the covariances E⟨X,X⟩ below already contain g₁², so there is no further factor g₁².
  {#MOMST.54-6} At order g₁² the full mean also receives the second-order parts of the insertions (of 𝐇 and of B′), the cubic vertices of (2.12) paired with a first-order insertion, and the linear vertices paired with a first-order insertion: the Tr log term (linear in λCA at lowest order, D̃ starting quadratic) and the linear parts of the 𝐄₁ difference and of CRE (3.15)'s 𝐑, 𝐁 and A(·) differences.
  {#MOMST.54-7} These are the perturbative coefficients α_L.
  - {#MOMST.55} *Convergence of the self-energy sums.*
    {#MOMST.55-1} X_b is linear in A: by RG1 p.268 B′ = g₁CA − hD̃(g₁CA), and by RG1 p.267 D̃ "has an expansion beginning with quadratic terms", so the linear part of B′ is g₁CA, local (RG2 p.4: "the function B′ defined by (I.3.2) is a local function of B"), X_b = ηg₁(𝒦A)(b) with 𝒦 := H_{1,1}C for f₁, and X_j = g₁(CA)(c_j) for g₁ (RG2's D(H(s),A′) of (1.12)–(1.14) is the analogue of RG1's H_kD_k in (2.6), p.266, a different object from hD̃, the linearisation of the δ-function constraint).
    {#MOMST.55-2} So E⟨X_b, X_{b′}⟩ = η²g₁²(𝒦C^{(1)}𝒦*)(b,b′) (and without η², 𝒦 = C, for g₁).
    {#MOMST.55-3} Kernels: C^{(1)} = (C*Δ^{(1)}C)^{−1} (RG1, the text just before (2.12)); PBG Theorem 3.15, p.432, (3.187): |C^{(k)}(Λ;y,y′)| ≤ B₀e^{−δ₀|y−y′|} with B₀, δ₀ depending on d and L only; RG2 p.13 identifies C(xI + C*Δ_kC)^{−1}C* with the integral (3.185) [13] (= PBG (3.185)), with an extra term vanishing at x = 0, so (3.187) is the bound for CC^{(1)}C* (RG1 p.268's covariance, printed: RG1 p.268, "the covariance C^{(k)} = C^{(k)}(U_{k+1}) = (C*Δ^{(k)}C)^{−1}", and RG2 p.13, "(C^{(k)})^{1/2} = (C*Δ_kC)^{−1/2}", the same operator).
    {#MOMST.55-4} C is a local operator (its locality comes from RG1 p.267's corridor constraint; its left inverse is the restriction to the non-designated bonds), so C^{(1)} itself has the decay with a range-L loss.
    {#MOMST.55-5} H_{1,1} has a random-walk expansion of RG2 (1.6)–(1.7)'s type (printed: RG1 p.266 refers H₁ to PBG (3.127)–(3.129), and PBG p.427 l.14–21 gives "the random walk expansions for the operators G₁, H₁", with estimates "the same as in (3.108)"), each term bounded by O(1)O(M₁^{−1/2})^{|ω|}M₁^{−1/2|ω|}exp(−δ₀d(ω,y,y′)) as printed in (1.7), so its kernel decays exponentially.
    {#MOMST.55-6} A finite composition of kernels on T_η with |K_i(y,y′)| ≤ B_ie^{−δ_i|y−y′|} is bounded by Be^{−δ′|y−y′|} with δ′ < min δ_i (the sums over intermediate points converge, with a polynomial prefactor absorbed into δ′).
    {#MOMST.55-7} Hence |E⟨X_b, X_{b′}⟩| ≤ η²g₁²B′e^{−δ′|b−b′|}, and along a straight line Σ_m|E⟨X_0, X_m⟩| ≤ η²g₁²B′(1 + 2/(e^{δ′η} − 1)) = O(g₁²η/δ′) per fine bond for δ′η ≤ 1, O(g₁²/δ′) per scale-1 bond; for g₁, Σ_m ≤ g₁²B″(1 + 2/(e^{δ′} − 1)) = O(g₁²) per scale-1 bond.
    {#MOMST.55-8} Both self-energy sums converge absolutely, so the Gaussian (linear-insertion) part of μ^f − μ^g is a well-defined O(g₁²) number.
- {#MOMST.56} **The comparison after step 2.** With D2.2's output for each loop, writing 𝓔₂^f, 𝓔₂^g for the step-2 exponents and g̃₂ for g₁'s averaged word,
  {#MOMST.57} e^{δm₂^fP₁(C)−4ζ₂^f}E_h[1_{A_cov}e^{E°_ξ}f₁] − e^{δm₂^gP₁(C)−4ζ₂^g}E_h[1_{A_cov}e^{E°_ξ}g₁] = E^{(2)}[e^{𝓔₂^f}Δ_bg] + E^{(2)}[(e^{𝓔₂^f} − e^{𝓔₂^g})g̃₂] + (difference of the averaged deviation words) + (large-field terms),
  {#MOMST.58} where 1_{A_cov} is taken constant on each labelled term of ρ₂.
  {#MOMST.58-1} V4 Lemma covered calls a branch ξ covered when every contour bond is a bond of Ω₁ and every free-input stencil F_r of a contour bond lies in the region I of the branch; so 1_{A_cov} is a function of the branch data Ω₁ and I. I is determined by the step-1 history labels that ρ₂'s labelled terms keep: V4 sec:c5-0 gives I = Λ₁^*, CRE p.254 labels the terms of ρ_k by {Ω_j}, {Λ_j}, and D2.2(2)(a) keeps V4's Λ = Λ₁^fin.
  - {#MOMST.59} The first term is bounded by Lip_χ(e^{6c_hB₃n_Cε₂L^{−3}} − 1) times the step-2 moment of the fine chain's dressing e^{𝓔₂^f} (B₃ as in (4)).
  - {#MOMST.60} The second.
    {#MOMST.60-1} By D2.3(8), 𝓔₂ − 𝓔₁ = E^∂_2(ℓ) + E°_2(C,T) for each loop, with E^∂_2(ℓ) := log S°(ℓ) − log S°(ℓ₀) and E°_2 the corner and torus remainder of the flat reference gas.
    {#MOMST.60-2} On the flat term ℓ₀, E^∂_2 = 0, so the exponents are E°_2^f and E°_2^g, numbers, each at most C_Eτ₁²[(s₁+1)e^{−c_Es₁} + s₁e^{−cι_{T,2}}] by D2.3(6)(a), given (S-w) for the reference gas of the loop, from which (T′) and (Z) follow (SW closure, #MOMGD.5; for g₁ by the first bullet; amplitude 𝔞₂ = max(τ₁², ρ₂·pl)).
    {#MOMST.60-3} The second-order amplitude holds for the coarse gas since the class (ii) activities of (5) are second order (#MOMGD.3).
    {#MOMST.60-4} Hence |e^{𝓔₂^f} − e^{𝓔₂^g}| ≤ e^{Re 𝓔₂^g}·(e^{|E°_2^f| + |E°_2^g|} − 1) ≤ 4C_Eτ₁²[(s₁+1)e^{−c_Es₁} + s₁e^{−cι_{T,2}}]·e^{Re 𝓔₂^g} on ℓ₀, under 2C_Eτ₁²[(s₁+1)e^{−c_Es₁} + s₁e^{−cι_{T,2}}] ≤ 1, step 2 commensurate (D2.3(4)) and the torus condition (so that the bound is uniform in the size of C): the exponential of the exponent difference is 1 + O(τ₁²) and the corner term decays in s₁.
    {#MOMST.60-5} By D2.3(3) the non-flat parts are the deviation words Y^d_𝒢 of the bracket, the third term below, and the exponent on ℓ₀ is the flat cluster series, all of which but E°_2 is absorbed into δm₂ and ζ₂.
    {#MOMST.60-6} On labelled terms ℓ ≠ ℓ₀ the difference E^∂_2^f(ℓ) − E^∂_2^g(ℓ) remains, D2.6's with the large-field terms.
  - {#MOMST.61} The third: D2.4(4) gives e^θ‖Y^d_𝒢‖ ≤ b_𝒢Dev_X with b_𝒢 = (C_g/(c₀ᾱ₂))e^θS_𝒢, and Dev_X = O(ε₂ℓ_X) in step-2 normalisation (D2.0(3)(b)).
    {#MOMST.61-1} So the remainder is S_𝒢·(C_g/(c₀ᾱ₂))·Dev_X = O(ε₂ℓ_X/ᾱ₂)·S_𝒢, and ε₂/ᾱ₂ = O((log g₂^{−2})^{p₀−min(q₀,q₁)}) is a power of log, bounded under CRE p.277's margin and not small; smallness comes only from the later contraction (D2.4(6)).
    {#MOMST.61-2} S_𝒢 bounded as in (5).
    {#MOMST.61-3} It uses (LPG′) (SW closure §5, #MOMGD.5).
  - {#MOMST.62} The fourth is D2.6's, together with (5)'s excluded activities.
- {#MOMST.63} Sizes, per scale-1 bond of C:

  | {#MOMST.64} part | pointwise (before averaging) | after the step-2 average |
  {#MOMST.65} |---|---|---|
  | {#MOMST.66} first-order insertions (fluctuation), interior | O(δ₁/ε′) | 0 at first order; per activity c_λρ₂·(decay), classes (i) and (ii) (#MOMGD.3) |
  | {#MOMST.67} flat second-order (perimeter, corners) | — | absorbed exactly into δm₂, ζ₂ via D2.3, given its input (S-w) for the coarse gas (SW closure, #MOMGD.5; its second-order amplitude 𝔞₂ holds, class (ii) being second order), for both loops; Gaussian (linear-insertion) part −(C₂(π)/(2d_G))·Δ(self-energy), O(g₁²), the covariances carrying g₁², absolutely convergent (RG1 p.268's covariance, H_{1,1}'s walk expansion) |
  | {#MOMST.68} exponent difference (e^{𝓔₂^f} − e^{𝓔₂^g})g̃₂ | — | on ℓ₀: |e^{𝓔₂^f} − e^{𝓔₂^g}| ≤ 4C_Eτ₁²[(s₁+1)e^{−c_Es₁} + s₁e^{−cι_{T,2}}]e^{Re 𝓔₂^g}, under 2C_Eτ₁²[…] ≤ 1, step 2 commensurate, torus condition, given (S-w) for the coarse gas (D2.3(6)(a), amplitude 𝔞₂; the second-order amplitude holds since class (ii) is second order, #MOMGD.3); on ℓ ≠ ℓ₀: D2.6 |
  | {#MOMST.69} background Δ_bg (additive) | O(ε₁) (step 1, by (1); O(ε₁/L) per fine bond) | O(B₃ε₂L^{−2}) (function of V₂ and the pending variables); the B′ = 0 end at the final scale O(B₃ε_KL^{−2(K−1)}) per scale-1 bond, (7)(d), on terms with C's blocks in Ω_K; the shed words are the two chains' insertion-word differences, averaged by both step maps ((7)(e)) |
  | {#MOMST.70} deviation remainder | — | O(ε₂ℓ_X/ᾱ₂)·S_𝒢, bounded not small, given (LPG′), (S); smallness from D2.4(6)'s contraction |
  | {#MOMST.71} activities excluded in (5)'s *Scope*, large fields | — | D2.6 |

{#MOMST.73} *(7) The background terms, iterated to the final scale.* (a)–(d) are pointwise. (e) is WILSON_IT1_BACKGROUND_ITERATION_CLOSURE_2026_10_26.md given its interfaces: (iii-a), (iii-c) (WILSON_IT1_COARSE_CHAIN_INTERFACES_CLOSURE_2026_10_26.md, with #(X^g) ≤ 81#(X), ℓ_{X^g} ≤ 25921ℓ_X, and the touched domains X^g_W counted in σ with the share constant c_sh^g := c_sh + 10240ν_f/L at L₀ = 5000), (iii-d), and (iv-a)–(iv-c) (the closure's §5.3, at k = 1 on D2's fixed torus).
{#MOMST.73-1} **Open: (iii-d)** (closure §4.3), D2.7 15.4(ii)'s three bounds (on E°^R_j, μ^R_j, and ζ^R_j, amplitude e^{−p₀(g_j)/4}) for the coarse chain's 𝐑-gas, whose slots are 𝔖_k(j) with (D1)–(D5), with constants that may depend on k but not on j, K, or ℓ_C. It enters only for k < K at K > N; the construction's route uses k = K (#MOMGD.2), where the chain is trivial.
- {#MOMST.74} *Setting.* K the final step; the sides of C are multiples of L^K fine bonds, so C is a union of scale-k bonds for every k ≤ K, with P_k(C) = 4ℓ_CL^{K−k} scale-k bonds, ℓ_C the side in step-K bonds (as in D2.0(5) and D2.3(4)), n_C = 4ℓ_CL^K.
  {#MOMST.74-1} A corner of C lies on the scale-K lattice (D2.3(4), *Placement*) and L is odd (ONE STEP (I3)).
  {#MOMST.74-2} M^k := M∘⋯∘M is the k-fold iterate of RG1 (0.4), the average V4 fixes (#MOSTC.4-1, #MOSTC.26; CMP98 p.31). RG1 p.265 (2.3), "V^{(k)} = Ū^k_{k+1} = M^k(U_{k+1})", and CRE (3.4), (3.10) use the symbol M^k without defining it.
  {#MOMST.74-3} C^{(k)} is C regarded as a scale-k loop.
  {#MOMST.74-4} T_c(U) is the straight fine transport along a scale-k bond c (the contour variable U(c) of RG1 (0.4), as in ONE STEP (I2)). a_d := 0.3(d−1)(d+4), so a_d = 7.2 for d = 4.
- {#MOMST.75} *(a) Lemma (iterated average against the straight transport).* Let U be a fine field with ‖U(∂p) − 1‖ ≤ t on every fine plaquette of a region Ω, let L ≥ 3(d+3), and let k ≥ 1 with a_dL^{2k}t ≤ min(1/10, log(1 + r_G)) (the chart condition; r_G the group constant of V4 app:background-estimates, recalled in the *Conventions* of sec:sourced-effective-interaction, so that ‖W − 1‖ ≤ r_G puts W ∈ G in the chart domain, where (0.4)'s log is the principal logarithm with values in 𝔤).
  {#MOMST.75-1} Then for every j ≤ k and every scale-j bond c with B^j(c_−) ∪ B^j(c_+) ⊂ Ω,
  {#MOMST.76} (M^jU)(c) = e^{iE_c}T_c(U), ‖E_c‖ ≤ a_dL^{2j}t.
  {#MOMST.77} Proof by induction on j; j = 0 is E = 0.
  {#MOMST.77-1} Step j → j+1: by RG1 (0.4) applied to the scale-j field M^jU (the blocks of the scale-(j+1) lattice in the scale-j lattice), (M^{j+1}U)(c) = e^{iX_c}·(M^jU)(c), with X_c a convex combination of the (1/i)log(M^jU)(ℓ) over the loops ℓ = Γ∪[x,x′]∪(−Γ′)∪(−c) of (I2), now made of scale-j bonds, and (M^jU)(c) = ∏_{b⊂c}(M^jU)(b) the product over the L scale-j bonds of c.
  {#MOMST.77-2} Three facts:
  - {#MOMST.78} (M^jU)(c) = ∏_{b⊂c}e^{iE_b}T_b(U) = (∏_{b⊂c}g_be^{iE_b}g_b^{−1})·T_c(U), with g_b the partial transports (unitary), so (M^jU)(c) = e^{iF_c}T_c(U) with ‖F_c‖ ≤ 1.06a_dL^{2j+1}t (the product bound of ONE STEP (2), and ONE STEP (2)'s log bound, since a_dL^{2j+1}t ≤ a_dL^{2k}t/L ≤ 1/10 for j ≤ k−1).
  - {#MOMST.79} (M^jU)(ℓ) = (∏_{b∈ℓ}g_be^{iE_b}g_b^{−1})·U(ℓ), with U(ℓ) the fine holonomy around ℓ regarded as a fine loop. ℓ has at most (d+2)L scale-j bonds (Γ, Γ′ at most d(L−1)/2 each, [x,x′] and c L each), and ONE STEP (1)'s contraction of ℓ uses at most A_L ≤ (d−1)(d+4)L²/8 scale-j plaquette moves, each a conjugate of a scale-j plaquette holonomy of U, i.e. of a product of L^{2j} conjugated fine plaquette factors.
    {#MOMST.79-1} All paths of the contraction lie in B^{j+1}(c_−) ∪ B^{j+1}(c_+) ⊂ Ω (a box; staircases and translates of c between its points stay in it), and the fine blocks of the scale-j bonds of ℓ lie in the same box (blocks nest).
    {#MOMST.79-2} So ‖(M^jU)(ℓ) − 1‖ ≤ e^{s_ℓ} − 1 with s_ℓ := A_LL^{2j}t + (d+2)a_dL^{2j+1}t ≤ [(d−1)(d+4)/8 + (d+2)a_d/L]L^{2j+2}t ≤ a_dL^{2j+2}t ≤ min(1/10, log(1+r_G)); so (M^jU)(ℓ) ∈ G (by the induction hypothesis E_b ∈ 𝔤, so that M^jU is G-valued) lies in the chart domain, (0.4)'s log is the principal logarithm with value in 𝔤 (V4's chart step, prop:coarse-loop-form (i)), ‖(1/i)log(M^jU)(ℓ)‖ ≤ 1.06s_ℓ, and X_c ∈ 𝔤 with ‖X_c‖ ≤ 1.06s_ℓ by convexity.
  - {#MOMST.80} e^{iX_c}e^{iF_c} = e^{iE_c} with ‖E_c‖ ≤ 1.06(‖X_c‖ + ‖F_c‖) ≤ 1.124[A_LL^{2j}t + (d+3)a_dL^{2j+1}t] ≤ 1.124·a_d[1/2.4 + (d+3)/L]L^{2j+2}t ≤ a_dL^{2j+2}t for L ≥ 3(d+3) (the arcsin step needs 1.06(‖X_c‖ + ‖F_c‖) ≤ 1/10, which the same chain gives); and ‖e^{iX_c}e^{iF_c} − 1‖ ≤ e^{1.06(‖X_c‖+‖F_c‖)} − 1 ≤ r_G, so E_c ∈ 𝔤 by the chart step again, and M^{j+1}U is G-valued. ∎
  {#MOMST.81} The per-level loss is a factor (d+3)/L on the previous level's deviation, not a constant: that is why the constant a_d does not grow with j.
  {#MOMST.81-1} The contraction of ℓ at level j and (I2)'s convexity are scale-independent, so ONE STEP (1)–(2) are used verbatim at each level.
- {#MOMST.82} *(b) Comparison lemma.* Under (a), with k such that every scale-k bond c of C has B^k(c_−) ∪ B^k(c_+) ⊂ Ω: Hol_{C^{(k)}}(M^kU) = ∏_ie^{iE_{c_i}}T_{c_i}(U) (E conjugated for negatively traversed bonds, norm unchanged) and Hol_C(U) = ∏_iT_{c_i}(U), so by V4 prop:coarse-loop-form (iii)'s argument (the Lipschitz chain over the P_k(C) factors, ‖e^{iE} − 1‖ ≤ ‖E‖ ≤ κ_k)
  {#MOMST.83} |W_χ(C;U) − W_χ(C^{(k)};M^kU)| ≤ Lip_χ(e^{P_k(C)a_dL^{2k}t} − 1)
  {#MOMST.84} (ONE STEP (3)'s form e^{c_πP_kκ_k} − 1 without Lip_χ also holds, since (a) gives E_c ∈ 𝔤).
- {#MOMST.85} *(c) The background term of step k+1 at step j and at the final scale.* For j ≥ k+1 put β_k^{(j)}(V_j) := W_χ(C;U_j(V_j)) − W_χ(C^{(k)};M^kU_j(V_j)); then Δ_bg of (3)–(4) is β_1^{(2)}(V₂), and the step-(k+1) background term of the step-k comparison (the same decomposition one scale up) is β_k^{(k+1)}(V_{k+1}).
  {#MOMST.85-1} Under the step j → j+1 substitution V_j = e^{iB′_j}V^{(j)}, by D2.0(5)(c)(α) at step j (U_j(V^{(j)}) = U_j(M^jU_{j+1}) = U_{j+1}: CRE (3.10), p.266, V^{(j)} = M^j(U_{j+1}), and RG1 p.265;
  {#MOMST.85-2} U_k′(1) = 1 is not printed on p.265 but is D2.0(5)(c)(α)'s derivation from CRE p.256, and equality up to gauge suffices since β is gauge invariant), on the terms whose scale-k blocks of C lie in Ω_K (the premise of (d), stated here), where C ⊂ B(Γ_{j+1}) at every j by the nesting Ω_K ⊆ Ω_j (printed: CRE (2.1), p.254, "Ω₁ ⊃ Λ₁ ⊃ Ω₂ ⊃ … ⊃ Ω_k ⊃ Λ_k", and p.256, "Ω = Ω₀ ⊃ Ω₁ ⊃ … ⊃ Ω_j") (elsewhere the pending values replace M^jU_{j+1}; those terms are D2.6's),
  {#MOMST.86} β_k^{(j)}(e^{iB′_j}V^{(j)}) = β_k^{(j+1)}(V_{j+1}) + w_j, w_j := β_k^{(j)}(e^{iB′_j}V^{(j)}) − β_k^{(j+1)}(V_{j+1}), a word vanishing at B′_j = 0.
  {#MOMST.87} This is the pointwise split f(B′) = f(0) + [f(B′) − f(0)]; it is gauge-safe (β is a difference of traces of closed loops, M covariant), so the representative gap of D2.2(4)(d) does not touch it.
  {#MOMST.87-1} Iterated, β_k^{(k+1)}(V_{k+1}) = β_k^{(K)}(V_K) + Σ_{j=k+1}^{K−1}w_j with β_k^{(K)}(V_K) = W_χ(C;U_K) − W_χ(C^{(k)};M^kU_K), a function of V_K and the pending variables of the term (CRE p.266: U_{k+1} is determined by the sequence {V_{k+1}|Γ_{k+1}, V_k|Γ_k, …}).
  {#MOMST.87-2} The per-step factor (1+β₀)B₃L^{−2} of (4) is not iterated in this decomposition; but the words carry, pointwise, exactly what the B′ = 0 end sheds: Σ_jw_j = β_k^{(k+1)} − β_k^{(K)}.
  {#MOMST.87-3} (d) bounds the B′ = 0 end only.
- {#MOMST.88} *(d) Bound at the final scale (for K ≤ N; for K > N the inputs at step K−1 and D2.0(5)(c)(α) are D2.7's, as D2.0(3)(b) and D2.0(6) assign them: (5)(c)(α) and (3)(b) on the post-R term are WILSON_IT1_D27_CLOSURE_2026_10_26.md items 10 and 12, and the inputs at step K−1 its observable part, item 15, #MD2.0.4.12).*
  {#MOMST.88-1-1} CRE p.268 at step K−1: |∂U_K − 1| < 2B₃ε_K(L^{−1}η)² on Ω_K, i.e. t_K := 2c_hB₃ε_KL^{−2K} in the operator norm on the fine plaquettes of Ω_K (those that intersect Ω_K, RG I p.251 l.26–28, as in (4);
  {#MOMST.88-2} the conversion uses η = L^{−(K−1)} at step K−1, CRE p.276's convention).
  {#MOMST.88-3} If every scale-k bond of C, k ≤ K−1, has its two scale-k blocks in Ω_K, then (b) with U = U_K, t = t_K and j = k gives
  {#MOMST.89} |β_k^{(K)}(V_K)| ≤ Lip_χ(e^{8a_dc_hB₃ℓ_Cε_KL^{−(K−k)}} − 1), since P_k(C)L^{2k}t_K = 4ℓ_CL^{K−k}·2c_hB₃ε_KL^{2k−2K},
  {#MOMST.90} under a_dL^{2k}t_K = 2a_dc_hB₃ε_KL^{−2(K−k)} ≤ min(1/10, log(1+r_G)), which holds for all k ≤ K−1 once 2a_dc_hB₃ε_K ≤ L²min(1/10, log(1+r_G)) (a condition on g_K; the k = K form used at the stopping scale, (e) and closure §3.4, needs 2a_dc_hB₃ε_K ≤ min(1/10, log(1+r_G)), without the L²).
  {#MOMST.90-1} Summing over k = 1, …, K−1, with 8a_dc_hB₃ℓ_Cε_K ≤ L/10 so that e^x − 1 ≤ 1.06x on each term (≤ 1/10 for the k = K bound, background closure §3.4 with (C3)),
  {#MOMST.91} Σ_{k=1}^{K−1}|β_k^{(K)}(V_K)| ≤ Lip_χ·8.48a_dc_hB₃ℓ_Cε_K·Σ_{m=1}^{K−1}L^{−m} ≤ Lip_χ·8.48a_dc_hB₃ℓ_Cε_K/(L−1).
  {#MOMST.92} This is O(ℓ_Cε_K/L), uniformly in the number of steps K, for the background values β_k^{(K)} on the terms whose scale-k blocks of C lie in Ω_K: the term of step k+1 contributes L^{−(K−k)}, so the first steps contribute least at the final scale, although the exponent of their pointwise bound at step k+1, O(ℓ_Cε_{k+1}L^{K−k−2}) by (4) and (b) with U = U_{k+1}, is the largest.
  {#MOMST.92-1} B₃ enters once, as a constant independent of the step: VAR Thm 1, p.279, "a₀, a₁, B₃, depend on d and L only" (quoted in D2.0(5)(c)(β)), with CRE's reuse of the symbol at every step (V4's (B3)(iii) records only its independence of the coupling and of the branch, and uses it at step 1).
- {#MOMST.93} *(e) What the words of (c) are, and the expectation-level closure (WILSON_IT1_BACKGROUND_ITERATION_CLOSURE_2026_10_26.md, given the interfaces of (7)'s heading, the closure's constants (C1)–(C6), smallness conditions on g_K, and the chart conditions; the inputs (S-w) and (LPG′) are the SW closure's, #MOMGD.5).*
  {#MOMST.93-1} At each step j the words vanishing at B′_j = 0 are, for the fine loop, D2.1(2)'s slot-insertion words of C at step j, and, for the coarse loop, the expansion of the composed function V_j ↦ M^kU_j(V_j) along C^{(k)}: by (a)'s structure, (M^kU_j)(c) is a composition of (0.4)-averages (analytic near the identity because the chart logarithm is; RG1 p.252 introduces G^c for this;
  {#MOMST.93-2} (0.5)–(0.10) are the axioms of the set average, not of (0.4)) of transports of U_j(V_j) along contours in B^k(c_−) ∪ B^k(c_+), and each transport expands by D2.1(2) into the transport of U_{j+1} with slot insertions (U_j(e^{iB′}V^{(j)}) depends on B′ through the minimiser, so the slots are the local objects, not the dependence).
  {#MOMST.93-3} So the coarse words are analytic functions of D(j+1)-type slot insertions whose slots lie in the tubes of C's scale-k bonds, vanishing when the insertions vanish, with the symmetry of (5) (λ → −λ, A → −A) preserved by the composition since everything depends on (λ, A) through B′.
  {#MOMST.93-4} For k = 1 the composed words begin at the step 2 → 3 substitution; the step-2 g-words of (3) come from g₁ itself and coincide with words of MU₁(V₁) on Ω₁^{(1)} by (I1).
  {#MOMST.93-5} The first-order averages of those step-2 words of (3) vanish at step 2 in the interior by (5).
  {#MOMST.93-6} No w_j is averaged at step 2: w_j (j ≥ k+1 ≥ 2) arises at the step j → j+1 substitution and is first averaged at step j+1 ≥ 3.
  {#MOMST.93-7} The closure: w_j = Ξ^f_j − Ξ^{g_k}_j is the difference of the two chains' insertion words at the step j → j+1 (Ξ^f_j := f_j(e^{iB′_j}V^{(j)}) − f_{j+1}(V_{j+1}), Ξ^{g_k}_j likewise, from CRE (3.10)'s V^{(j)} = M^j(U_{j+1}) and U_j(M^jU_{j+1}) = U_{j+1}, D2.0(5)(c)(α)), and the step map is linear and observable-independent (D2.2(2)'s seven operations;
  {#MOMST.93-8} CRE (3.2), (3.3), (3.8)–(3.11), (3.16)–(3.19)), so each w_j is averaged at step j+1 as part of both chains' step maps and is never a separate object: (i) its first-order parts are the two chains' class (i) activities at step j+1, even in the coupling by (5) run at step j+1 (RG1 (2.12) at the general step with "the expression under the exponential above vanishes at g_k = 0", p.268; CRE (3.15) at the general step), bounded by #MOMGD.3's c_λρ_{j+1}·(decay) with the composed slot amplitude;
  {#MOMST.93-9} its flat second-order parts are the two chains' own δm_{j+1}, ζ_{j+1}, E°_{j+1}, absorbed by each chain's D2.3, with the ratio r_{j+1} := κ^f_{j+1}/κ^{g_k}_{j+1} of the two normalisations, |log r_{j+1}| ≤ 2C_S′𝔞^∨_{j+1}P_j(C) + 8C_ζ𝔞^∨_{j+1}; its deviation parts are the two chains' Y^d insertions;
  {#MOMST.93-10} (ii) the bonds whose scale-k blocks leave Ω_K are excluded at every step by the nesting Ω_K ⊆ Ω_j (CRE (2.1)), and the tubes meeting (5)'s excluded regions are D2.6's attached species with the carrier item ((iv-a)–(iv-c) of the closure: the whole-label remainder R_bad ≤ Cκ_f^{(K)}N_tube·w_K, N_tube = 4ℓ_C·3·2^{d−1}, w_K = O(g_K^{−2}(log g_K^{−2})^{1−p₀}e^{−2p₀(g_K)}) by the running lower bound of BETA_FUNCTION_WILSON_LOOPS.md Lemma 2.1(i), given the creation-position count under a scale-K cube (closure (iv-b)), needed only for this volume-uniform form,
  {#MOMST.93-11} on D2's fixed torus R_bad being bounded through the Cauchy note's (11.3) instead (closure (iv-e)), with LFR II (1.80)–(1.89), the D2.6 closure §7.2–7.3, (iv-a)'s carrier item, and the anchored E^∂ form);
  {#MOMST.93-12} (iii) the expectation-level statement is the identity E[W(C)] − N_k⟨g_k^{(k)}⟩_k = κ_f^{(K)}⟨e^{𝓔^f_K}β_k^{(K)}⟩_K^{good} + (the exponent difference) + (the insertion difference) + R_bad, N_k := κ_f^{(k)}e^{E^f_{const,k}}∏_{j>k}r_j (closure §3.1, the three terms over the labels where both chains have their D(K) forms), the first term bounded by (d), the second by the ratios r_j, the third by both chains' D(K)(ii) summed at K;
  {#MOMST.93-13} (iv) the β_k of different k enter one identity only through the telescoping of the coarse loops across scales under the single normalisation κ_f^{(K)} (closure §3.3), of which (d)'s sum is the pointwise bound.
  {#MOMST.93-14} At k = K the chain is trivial and E[W(C)] − κ_f^{(K)}⟨e^{𝓔^f_K}g_K^{(K)}⟩_K = κ_f^{(K)}⟨e^{𝓔^f_K}(β_K^{(K)} + I^f_K)⟩_K with |β_K^{(K)}| ≤ 8.48a_dc_hB₃ℓ_Cε_K·Lip_χ on the covered terms (closure §3.4): the form the construction uses at the stopping scale, needing neither (iii), the sum over k, nor any shed word.
  {#MOMGD.2} On the other labels ℒ_K it needs the fine chain's D(K) form (D2.7's beyond N), with which the ℒ_K term is at most 2|κ_f^{(K)}|exp(4Cℓ_C(ρ_Kε_K + τ_K²) + r^R_K)δ_LF, δ_LF → 0 as ḡ → 0 at a fixed loop and torus (closure §3.4 and (iv-e)); with ℓ_Cε_{K′} → 0 at the stopping scale (#MD2.3.4.16-8) this is WHAT THE CONSTRUCTION IS's form.
  {#MOMST.93-15} The coarse chain runs on the species "composed coarse word of level k" with the clauses (D1)–(D5) (locality in A through B′ on the tube, boundedness, the chart conditions b_d := (10d+29)/9, b_d^c := 1.2b_d) and the slot amplitude ε_H/(b_d^c)^k in place of ε_H, with the arc I^{(k)}(G); on these (S-w) runs as the SW closure's four inputs (observable-independent or following from (D1)) with the three changes of (6)'s first bullet, and the class (i) sup runs as the class closure's a1–a6 (every composed word depends on (λ, A) through B′, so the scaling identity holds verbatim) with that amplitude.

## D2.0 The inductive form at step k, and the count check {#MSD2.0}

### (1) Units {#MSD2.0.1}

- {#MD2.0.1.1} *Bałaban's units at step k.* The block lattice of step k has unit spacing, and the fine lattice is T_η with η = L^{−k}.
  {#MD2.0.1.1-1} The scale-j lattice is T_{L^{−(k−j)}} in these units.
  {#MD2.0.1.1-2} Checked against three prints:
  - {#MD2.0.1.2} CRE (2.17) tests the fine plaquettes of T_η at threshold ε_kη²;
  - {#MD2.0.1.3} CRE p.268 states the regularity of U_{k+1} at the threshold 2B₃ε_{k+1}(L^{−1}η)², with (L^{−1}η)² the squared fine spacing of step k+1;
  - {#MD2.0.1.4} LFR I p.178 reads the LM₂R_j-cubes of T_{L^{−j}} as the L^{−(k−j)}LM₂R_j-cubes of T_η.
- {#MD2.0.1.5} *V4's units at step 1* are fine units (the fine lattice has unit spacing, the block lattice spacing L).
  {#MD2.0.1.5-1} V4's ℓ = LMR₁ (V4 sec:c5-0) and the side L²M₂R₁ of the CRE (1.18) cubes are in fine units (IT-1 note §3f(2) R1).
- {#MD2.0.1.6} *The contour.* C is a closed contour of fine bonds that is a union of block bonds at every scale j ≤ K (V4's squares C_n; IT-1 note §4).
  {#MD2.0.1.6-1} V4's C_n is a coarse translate of a square of side nL in fine units (V4 sec:c5-5-0).
  {#MD2.0.1.6-2} It is a union of scale-j bonds for every j ≤ K when L^{K−1} divides n and the translate is by a scale-K lattice vector, with torus periods that are multiples of L^K.
  {#MD2.0.1.6-3} This restricts n and the periods to arithmetic progressions, which stay arbitrarily large.
  {#MD2.0.1.6-4} P_j(C) is the number of scale-j bonds of C, so P_j(C) = L^{−j}P_0(C).
  {#MD2.0.1.6-5} For a square loop of physical side ℓ_C at spacing L^{−K}, P_j(C) = 4ℓ_CL^{K−j}.
  {#MD2.0.1.6-6} (ℓ_C is not V4's collar width ℓ = LMR₁, sec:c5-0.)
- {#MD2.0.1.7} *Scales.* The parameters are those of the tube construction (#MD2.0.5.2): CRE's, LFR I's, and LFR II's, taken at ĝ_j (BETA_FUNCTION_WILSON_LOOPS.md #B2.2.171–#B2.2.180), so ε_j = ĝ_jp₀(ĝ_j) ≤ g_jp₀(g_j), and each threshold is within factors tending to 1 with γ of its value at g_j (Lemma 2.10(a), (e)). The couplings obey CRE (2.4) and (2.6)–(2.9), and R_j obeys (2.5) with 2L for L in its upper bound (Cauchy #CP.14–#CP.14-1).
  {#MD2.0.1.7-1} In particular ε_n ≤ (1+β₀)(n−m)^{1/2}ε_m, ε_m ≤ (1+β₀)²(n−m)^{β₀}ε_n and R_n ≤ LR_m for n > m (CRE (2.8)–(2.9)).

### (2) Regularity of the Background {#MSD2.0.2}

- {#MD2.0.2.1} *Quoted.*
  - {#MD2.0.2.2} CRE (2.17), p.257: on χ_k(Ω_k), sup_{p⊂□^∼}|U_{k,□}(V_k,∂p) − 1| < ε_kη² for every LM₂R_k-cube □ ⊂ Ω_k, the sup over the fine plaquettes p ⊂ □^∼.
  - {#MD2.0.2.3} CRE p.268: "The field U_{k+1} satisfies the regularity condition |∂U_{k+1} − 1| < 2B₃ε_{k+1}(L⁻¹η)² on Ω_{k+1}".
  - {#MD2.0.2.4} CRE (2.34)–(2.39), p.261: the analyticity spaces Ũ_j^c(X, α̃₀, α̃₁), X ∈ 𝐃_j, of configurations (𝐔, 𝐉) with 𝐔 = U′U.
    {#MD2.0.2.4-1} On X ∩ (Ω_n∖Ω_{n+1}) for n = 1, …, j−1, and on X ∩ Ω_j for n = j: |∂U − 1|, |∂𝐔 − 1| < (1 − β(1 − 2^{−(j−n)}))α_{0,n}ξ²(L^nξ)^{−2} (2.34), the analogous bounds (2.35)–(2.37) for the averaged configurations and for 𝐉, and U′ = exp iξA′ with L^nξ|A′|, (L^nξ)²|∇_U^ξA′| < (1 − β(1 − 2^{−(j−n)}))α_{1,n} (2.39).
    {#MD2.0.2.4-2} (2.38) asks for local gauges with U^u = exp iξA, L^nξ|A|, (L^nξ)²|∇^ξA| < BCMα_{0,n}, on cubes of size CML^nξ (CM for n = j). β is a small constant, e.g. 1/4.
    {#MD2.0.2.4-3} These conditions define the domain of analyticity; they are not bounds proved for U_k.
- {#MD2.0.2.5} *The deviation of coarser plaquettes.* Let P be a plaquette of the scale-j lattice, j ≤ k + 1, all of whose fine plaquettes lie in Ω_{k+1}, at a configuration in the support where p.268's bound holds.
  {#MD2.0.2.5-1} (CRE p.255 l.20–21 refers its set convention for plaquettes to "Sect. 0 [I]", RG I by CRE p.285: the plaquettes of a set are those that intersect it, RG I p.251 l.26–28. Every fine plaquette of P therefore counts as a plaquette of Ω_{k+1}.) In step-(k+1) units its side is L^{−(k+1−j)}, so it is a union of m² fine plaquettes with m = L^{−(k+1−j)}/(L^{−1}η) = L^{j}.
  - {#MD2.0.2.6} The lattice lasso identity writes the holonomy of ∂P from a corner as an ordered product ∏_p γ_p(∂p)γ_p⁻¹ over its fine plaquettes, with γ_p paths in P.
  - {#MD2.0.2.7} In a unitary representation, |∏_iA_i − 1| ≤ Σ_i|A_i − 1| (telescoping, since products of unitaries have norm 1), and |γ(∂p)γ⁻¹ − 1| = |∂p − 1|.
  - {#MD2.0.2.8} So |∂P(U_{k+1}) − 1| ≤ m²·2B₃ε_{k+1}(L^{−1}η)² = 2B₃ε_{k+1}L^{−2(k+1−j)}.
    {#MD2.0.2.8-1} No small-field expansion is used.
  - {#MD2.0.2.9} For j = k: a plaquette of the step-k lattice has deviation at most 2B₃ε_{k+1}L^{−2} under the step-(k+1) background.
- {#MD2.0.2.10} *Units.* η = L^{−k} is the fine spacing in step-k units (RG1 p.257 l.36; CRE p.276 l.7), so (L^{−1}η)² is the area of a fine plaquette in step-(k+1) units.
  {#MD2.0.2.10-1} So the step-k plaquettes of the step-(k+1) background deviate by at most 2B₃ε_{k+1}L^{−2}, the L^{−2} of the heuristic.
  {#MD2.0.2.10-2} This is a statement about the background only; the contraction of the insertions is D2.4's.

### (3) The Class at Step k {#MSD2.0.3}

{#MD2.0.3.1} This generalises the IT-1 note §4 from k = 1.
{#MD2.0.3.1-1} A *dressed loop of step k* on a labelled term of ρ_k (CRE (2.18), with the labels of D1.0(P) at every scale) is a function of V_k and of the outer variables that the term holds constant, of the form

{#MD2.0.3.2} 𝒲_k = κ^{(k)} e^{𝓔_k} [ f_k + Σ_{𝔅≠∅ compatible} Q_k(𝔅)·dim(π)⁻¹ tr(Y_{W₁}U_{(1)} ⋯ Y_{W_m}U_{(m)}) ].

- {#MD2.0.3.3} *Outer variables:* the pending variables of T_k: the V_j on Ω_{j+1}ᶜ and the fluctuation fields A_j on Z_{j+1} ∩ Ω_{j+1} (CRE (2.20)–(2.21)), the exterior and de-younged variables of the labels (IT-1 note §4, *Definition*).
- {#MD2.0.3.4} *κ^{(k)} := ∏_{j=1}^{k} κ_j* with κ_j := e^{−δm_jP_{j−1}(C)}z_j⁴, the exact step-j perimeter and corner coefficients.
  {#MD2.0.3.4-1} With δm_1 := δm^σP(C_n)/P_0(C_n) and z_1 := z_c^σ, κ_1 is V4's κ_{C_n} = e^{−δm^σP(C_n)}(z_c^σ)⁴ (eq:extracted-loop-scalar; D1(i)); this holds for any normalisation of P(C_n) proportional to n.
- {#MD2.0.3.5} *Leading word f_k := dim(π)⁻¹tr π(Hol_C(U_k)),* a scalar.
  {#MD2.0.3.5-1} At k = 1, D1's leading word is f_ξ(m̂) = W_χ(C;U_ξ(m̂)), V4's f_ξ at the real centre m̂, which contains the shift (IT-1 note §3j(4)); D(1) ⊇ D1 writes f_ξ(m̂) − f_1 as att(1, ·) insertions by the telescoping of *Species* below: by IT-1 note §3j(2) it depends on Λ only within R_N of C, and it is driven by the large-field and collar data through ℓ_Λ (its size and its place in the label sum are the D2.6 item of IT-1 note §3j(0)).
  {#MD2.0.3.5-2} The holonomy is written as a product, over the step-k bonds of C, of the transports of U_k along their fine bonds.
  {#MD2.0.3.5-3} Where C crosses a large-field region, outer variables enter as in D1.1 (IT-1 note §3d(1)).
- {#MD2.0.3.6} *Groups, families, insertions, words, interactions:* as in IT-1 note §4, with V4's groups replaced by the groups that the step-k map produces (D2.2).
  {#MD2.0.3.6-1} Their sizes are measured in step-k units.
  - {#MD2.0.3.7} *Interaction clause in cluster form (D2.3(3)).* At every step, Q_k(𝔅) = exp(−Σ_{Γ hits 𝔅}φ_k(Γ)), the sum over the clusters Γ of the step-k reference group gas (a pure hard-core gas) that are incompatible with some member of 𝔅, with φ_k(Γ) numbers given the labels that depend on C only through J_Γ, the traversals in the arcs of Γ's groups, and Σ_{Γ hits W}|φ_k(Γ)| ≤ θ(W).
    {#MD2.0.3.7-1} At k = 1 this is IT-1 note §4's form.
- {#MD2.0.3.8} *Scalar exponent* 𝓔_k = Σ_{j≤k}Σ_X e^{(j)}_X + E_const,k, a sum of local terms (the carrier parts and the thin E^∂ of IT-1 note §3i at every scale) plus a constant of the contour and the torus.
- {#MD2.0.3.9} *The deviation quantity.* Put η_k := L^{−k}.
  {#MD2.0.3.9-1} For a traversal n of a step-k bond of C,
  {#MD2.0.3.10} δ*_n^{(k)}(U) := η_k^{−2}Σ_{t≥1}w_tΔ_n^{(k)}(R_t^{(k)}), w_t := (t+1)³e^{−η_wt}, η_w := (5/16)η_V (D2.4(12)(b) *Base*, with ν_e := ν/(2C_box) and the complex factor e^{η𝔰/8} of D2.6 closure §6.5's budget; the step-1 proof of (ii-t) also carries the reserve and extent weights and §3j(6)'s share),
  {#MD2.0.3.11} Δ_n^{(k)}(R) := max{δ_p(U) : p a fine plaquette of Ω_k (of Λ₁ at k = 1) within step-k distance R of n}, with max ∅ := 0.
  {#MD2.0.3.11-1} The step-k distance is V4's d_T (sec:marginal-perimeter) times η_k.
  {#MD2.0.3.12} δ_p is V4's plaquette deviation, η_V is V4's exponent η (renamed, since η is the fine spacing here), and the radii R_t^{(k)} are fixed by D2.2's group scale, with R_t^{(1)} := C_boxM(t+1), V4's C_boxLM(t+1) in step-1 units.
  {#MD2.0.3.12-1} (Note from D2.4(6)(γ): R_t^{(k)} := C_boxM(t+1) in step-k units at every k.)
  - {#MD2.0.3.13} (a) At k = 1, δ*_n^{(1)}(U) ≥ L²δ*_{n_f}(U) for every fine traversal n_f ⊂ n, with δ*_{n_f} of IT-1 note §3a(6): η_1^{−2} = L², and the neighbourhoods of n contain those of n_f.
  - {#MD2.0.3.14} (b) For k ≥ 2, on the support of the step-k characteristic functions on which p.268 states the regularity (k ≤ N; for k > N, D2.7), δ*_n^{(k)}(U_k) ≤ 2c_σB₃ε_kΣ_tw_t, by p.268 at the step k−1 → k (|∂U_k − 1| < 2B₃ε_kη_k² on Ω_k), with c_σ converting CRE's matrix norm into V4's |·|_σ.
    {#MD2.0.3.14-1} At k = 1, δ_p(U₁) ≤ Cε₁ for p ⊂ Λ₁ (V4 Lemma c2-plaquette-deviation, applied in sec:c4-11-5), so δ*_n^{(1)}(U₁) ≤ CL²ε₁Σ_tw_t.
  - {#MD2.0.3.15} (c) For the same plaquettes and radii, η_{k+1}^{−2}max = L²·η_k^{−2}max for every U. This is the exact form of the L^{−2} of (5).
    {#MD2.0.3.15-1} The plaquette set changes from Ω_k to Ω_{k+1} (Λ₁ to Ω₂ at the first step), so the maximum in δ*^{(k)}_n(U_{k+1}) is split: the plaquettes of Ω_{k+1} give ≤ L^{−2}δ*^{(k+1)} after D2.4's matching; those of Ω_k∖Ω_{k+1} contribute at most η_k^{−2}·sup_{p⊂Ω_k∖Ω_{k+1}}δ_p(U_{k+1})·Σ_{t: R_t^{(k)} ≥ dist(n, Ω_k∖Ω_{k+1})}w_t, which by the membership condition (2.34) at j = k+1, n = k (|∂U − 1| < (1 − β/2)α_{0,k}η_k²) is ≤ c_σ(1 − β/2)α_{0,k}Σ_{t: …}w_t once U_{k+1} is shown to lie in the space.
    {#MD2.0.3.15-2} Here α_{0,k} = g_kC₀(log g_k⁻²)^{q₀} (CRE (2.28), p.259) is bounded uniformly in k, since x(log x⁻²)^{q₀} increases for log x⁻² > 2q₀ and g_k ≤ (1+β₀)g_K by the last inequality of CRE (2.6) (#MD2.0.5.2-2), under the condition (1+β₀)g_K < e^{−q₀}.
    {#MD2.0.3.15-4} RG1 Theorem 3 (p.264) is stated under "0<g_k≤γ for k=0,1,…,K", RG I's γ, written γ_B in D2 (Lipschitz note §5); the sequence of #MD2.0.5.2 has g_k ≤ (1+β₀)g_K (#MD2.0.5.2-2), so it stays in ]0, γ_B] at every step once sup_K g_K ≤ γ_B/(1+β₀).
    {#MD2.0.3.15-6} That part decays with the distance to Ω_{k+1}ᶜ and joins the scale-(k+1) attached part.
    {#MD2.0.3.15-7} Both the matching of the neighbourhoods and radii of an old traversal n with those of the new traversal n′ ⊇ n and this split are D2.4 items.
    {#MD2.0.3.15-8} The block-plaquette bound of (2) is a corollary (lasso step), not the class quantity.
- {#MD2.0.3.16} *Species.* Every insertion Y_W carries a species, fixed by the labels and the group geometry, at production and at each step's reclassification: *dev*; *att(j, Z)*, attached at step j to a large-field component Z by a non-good group; *att(j, coll)*, a collar part made at step j, with no component (one collar insertion is bounded by the marks of all of W's domains and inputs, which can be assigned to different components, so a species att(j, coll Z) is not defined for it; the bound is split by component instead of the insertion, (ii′-b));
  {#MD2.0.3.16-1} *lw(Z)*, the telescoped leading-word parts assigned to Z; *wrap(j)*.
  {#MD2.0.3.16-2} The words are expanded multilinearly in the species.
  {#MD2.0.3.16-3} The split is made in the formulas, not by the sizes of the bounds, so each part is analytic, as D(k)(iii) needs.
  - {#MD2.0.3.17} *Assignment rules.* Fix an order of the components of B_ξ at each step.
    {#MD2.0.3.17-1} A non-good group goes to the first component that its Q_W meets.
    {#MD2.0.3.17-2} Each bond mark, host mark and free input b of the collar data goes to the nearest component of the step-j large-field set Z_j, ties broken by the order.
    {#MD2.0.3.17-3} A telescoped bond i goes to the component nearest to i.
  - {#MD2.0.3.18} At step 1 the split exists: Υ¹_W = (Υ¹_W − Υ⁰_W) + Υ⁰_W (IT-1 note §3a(1)).
    {#MD2.0.3.18-1} Υ⁰_W is dev for good groups (§3a(3)); otherwise it is att(1, Z) in case (i) of §3a(4), with Z the component of B_ξ that Q_W meets first, and wrap(1) in case (ii), where Q_W does not lift, bounded by Cρe^{−c_att N_min/(LM)} and decaying from no component.
    {#MD2.0.3.18-2} Υ¹_W − Υ⁰_W is att(1, coll) (§3a(2), (7)).
  - {#MD2.0.3.19} *The leading word in slot form.* With T, T̂ the transports of U₁ and U_ξ(m̂) and Y_i := π(T̂_iT_i^{−1}) − 1 over the fine bonds i of C in order, Π_iπ(T̂_i) = Π_i(1 + Y_i)π(T_i) = Σ_{S⊆C}(the ordered product with Y_i at the positions of S and 1 elsewhere), so f_ξ(m̂) = Σ_Sf^{(S)} with f^{(∅)} = f_1, and likewise each word U_j (D2.6 closure §6.5).
    {#MD2.0.3.19-1} The identity is exact. Each S-term is a word with unitary transports and the |S| slots Y_i, i ∈ S, each of species lw(Z) for the Z that i is assigned to, θ := 0, with "i ∈ n" read for "W ∋ n" in ν_n; its Λ-dependence lies within R_dep of its slots, and lw slots have Q = 1 against each other and against every other insertion of the word.
    {#MD2.0.3.19-2} Σ_{i∈n}‖Y_i‖ is added to the displayed D(1)(ii).
    {#MD2.0.3.19-6} On every labelled term (closure §6.1–6.5, not only on V4's covered event A^fin_cov) T_i := U₁(r_i) and T̂_i := U_ξ(m̂)(r_i) = e^{iΦ_i}U₁(r_i) (V4 (c-reconstructed-field)), so Y_i = π(e^{iΦ_i}) − 1 with no background factor, Y_i = 0 off Ω₁.
    {#MD2.0.3.19-7} On rows within 2R_c + 2L of I (class (I)) Φ_i = q_U(Ψ_ξ(m̂ + a_old + A_e))(r_i) and ‖Y_i‖ ≤ C_I″g₀(r+1); on the far rows (class (III), within 2L of Λ₁ᶜ) Φ_i = q_U(Ψ_ξ(A_e))(r_i) is Λ-independent and ‖Y_i‖ ≤ C_III, a constant; complex data by D2.6 closure §6.1 with V4 §c4-10-1 *Contour Rows in the Joint Domain*. m̂ = λm̃ is the term's real centre of closure §6.4 *Shift* and *The centre*, so a complex background enters Y_i only through its stencil background.
    {#MD2.0.3.19-8} Every slot with Y_i ≠ 0 lies within R_lw′ := R_t + 2L + 1 ≤ ℓ of Z₁ = Λᶜ and is of species lw(X), X the component of Z₁ nearest to it (closure §6.2 *Support*).
    - {#MD2.0.3.20} *In the family sum.* An lw slot forms a one-element family with Q_k = 1.
      {#MD2.0.3.20-1} With the D2.6 closure §6.5's subset expansion several lw slots occur in one word, so lw slots are compatible with each other and with every other insertion of the word (Q = 1 for every such pair), and the family sum reproduces the subset expansion exactly.
      {#MD2.0.3.20-2} On a term with no large-field component the lw slots, if any, take lw(∅) and are bounded as a whole by (ii′-c) with the sum over all i; "the component nearest to i" is used only when a component exists.
  - {#MD2.0.3.21} At step k+1 the old dev insertions are reclassified: dev if their comparison box (the plaquettes their deviation bound uses) lies in Ω_{k+1}, att(k+1, Z) if it meets Ω_k∖Ω_{k+1}.
    {#MD2.0.3.21-1} Z is the component of Z_{k+1} = Λ_{k+1}ᶜ containing the first component, in the fixed order, of Ω_{k+1}ᶜ that the comparison box meets; one exists, since Ω_k∖Ω_{k+1} ⊆ Ω_{k+1}ᶜ ⊆ Λ_{k+1}ᶜ (CRE (3.20)).
    {#MD2.0.3.21-4} The charge of such a part to the data its component Z contains, of any step ≤ k+1, is D2.6's (D2.6 closure §3).
    {#MD2.0.3.21-5} This is the structural form of the split of the maximum in (3)(c).
  - {#MD2.0.3.22} *Insertions made at step k+1.* A group of D2.2(6)(d) made at step k+1 takes its species from the tests of the D2.6 closure 2.1, applied to the final merged group in the order: inherited species (#MD2.0.3.22-1), wrap(k+1) (#MD2.0.3.25), att(k+1, coll) (#MD2.0.3.24), att(k+1, Z) (#MD2.0.3.23), dev.
    - {#MD2.0.3.22-1} A group with an inherited attached member (att(j, ·), lw or wrap(j), j ≤ k) takes the first inherited species, step ascending, then att(j, Z) < att(j, coll) < lw < wrap.
    - {#MD2.0.3.23} A group passing the earlier tests whose comparison region meets Ω_{k+1}ᶜ is att(k+1, Z), Z the component of Λ_{k+1}ᶜ containing the first component, in the fixed order, of Ω_{k+1}ᶜ that the region meets.
    - {#MD2.0.3.24} A group passing the earlier tests is att(k+1, coll) if it meets the one-layer neighbourhood of Λ_{k+1}ᶜ, carries a boundary-type potential, or has a polymer component or an arc traversal leaving Ω_k; so are the parts of D2.2(6)(c)'s reference extraction whose clusters meet the collar.
    - {#MD2.0.3.25} A group with no inherited attached member whose set X(𝒢) does not lift at step k+1 is wrap(k+1).
    - {#MD2.0.3.25-1} The other groups are dev.
  - {#MD2.0.3.26} A fluctuation part Y(U_k) − Y(U_{k+1}) keeps its parent's species.
    {#MD2.0.3.26-1} An insertion made from several parents is dev only if all are dev.
    {#MD2.0.3.26-2} Otherwise it takes the first attached species of its parents in the total order: by step j ascending, then by kind att(j, Z) < att(j, coll) < lw < wrap, then by the fixed order of the components.
  - {#MD2.0.3.27} *Units of carried groups.* For att(j, ·) groups, θ(W) and σ(W) are those of step j, when the group was made; the bound θ(W) ≤ νσ(W)/16 is evaluated at that step.
- {#MD2.0.3.28} *D(k)(ii), per-traversal form.* For every traversal n of a step-k bond of C, with ν_n^{(k)} := Σ_{W∋n}e^{θ(W)}‖Y_W‖ over the insertions of species dev, att(k, ·) and wrap(·),
  {#MD2.0.3.29} ν_n^{(k)} ≤ C_χρ_kδ*_n^{(k)}(U_k) + Cρ̂_ke^{−c_att d_k(n)/M} + Cρ_{t,k}(Σ_Δ𝔪̂^{(k)}_Δe^{−c_*′dist(Δ,n)/M} + C′_χg_kΣ_bh(m^{(k)}_b)e^{−c_*′dist(b,n)/M}) + Σ_{j=1}^{k}CL^{k−j}ρ̂_je^{−c_att N^{(j)}_min/M}.
  {#MD2.0.3.29-1} The collar rate c_*′ = min(η_V/C_F, ν_e/8, κ/4) (#T12.19) is the rate at which the step-(k+1) collar groups are bounded (D2.6 closure 2.2 *The bound in (ii)'s form*); at k = 1, D1(ii)'s rate η_V/C_F implies it (#MD2.0.3.39-2).
  - {#MD2.0.3.30} *The first term (D2.4(5)).* For k ≥ 2 the first term is C_χρ̃_kδ*_n^{(k)}, ρ̃_k := ρ_k/ᾱ_k, ᾱ_k := min(α_{0,k}, α_{1,k}), and ρ̃_1 := ρ_1.
    {#MD2.0.3.30-1} The factor comes from D2.4(4)'s Cauchy step.
    {#MD2.0.3.30-2} On the support ρ̃_kδ*_n = O(ρ_k) under CRE p.277's margin's entailments, and at complex data the size gains 1 + (log g_k^{−2})^{(q₁−q₀)₊}; on 𝒟_k^{sub} the gain is 2 on every layer under q₀ = q₁ (SW closure §2–§3).
    {#MD2.0.3.30-3} Each dev insertion also carries its own bound e^{θ(W)}‖Y_W‖ ≤ b_WDev_{Q^#_W}, with Σ_{W∋n}b_WDev_{Q^#_W} ≤ C_χρ̃_kδ*_n (the per-insertion form, used by the reclassification).
    - {#MD2.0.3.31} *Tail clause (D2.4(5)).* Dev_{Q^#_W}, ℓ_W and b_W stay in the normalisation of the step at which W was made, and with β_W := b_Wℓ_Wη_{j(W)}^{−2}, (ii) also contains (ii-t) Σ_{W∋n, t^{(k)}(W)≥t}β_W ≤ C_χρ̃_kη_k^{−2}W_t for every t, W_t := Σ_{t′≥t}w_{t′}.
      {#MD2.0.3.31-1} The sum form above follows from it by Abel summation; at k = 1 it follows from IT-1 note §3a(6)'s proof.
    - {#MD2.0.3.32} *Reserve and extent weights (D2.4(12)(b)).* (ii) and (iii) carry the weight e^{ν_rσ_k(W) + ν_e·ext_k(W)} inside their per-position sums, ν_r := ν, ν_e := ν/(2C_box) (D2.6 closure §6.5's budget), ext_k(W) the extent of X(W) ∪ Q^#_W from every traversal of W in π_k-sides (production units for carried insertions; C_box ≥ 4A_E ≥ 4 so that ν_e ≤ ν/8): the form (ii-w) of D2.4(12)(b), per traversal only (cube positions by the box reduction of D2.4(12)(e)), for the dev species.
      {#MD2.0.3.32-1} At k = 1 it is V4 (c4-6-5) (Lemma c4-6-2), with V4 Lemma c5-5-8(a) (the e^{4νσ} pins and the ε̄_t displays) and (b); it carries k → k+1 as (ii-t) does, and D2.4(12)–(13) prove it for the new groups ((S-w)).
      {#MD2.0.3.32-2} It is what pays for merged old members in the step-(k+1) count.
  - {#MD2.0.3.33} *Per component.* The second term is stated per component: for each step-k large-field component Z, Σ_{W∋n, W∈att(k,Z)}e^{θ(W)}‖Y_W‖ ≤ Cρ̂_ke^{−c_att d_k^Z(n)/M}, with d_k^Z(n) the step-k distance from n to Z's data; Cρ̂_ke^{−c_att d_k(n)/M} in the display denotes this family of bounds.
    {#MD2.0.3.33-1} At k = 1 it follows from the argument of IT-1 note §3a(4)(i) with Q_W ∩ Z ≠ ∅, which gives d^Z(n) ≤ diam(Q_W) + 1.
    {#MD2.0.3.33-2} The collar term is the att(k, coll) part and keeps its form; its split by the assigned component of the marks is a split of the bound ((ii′-b)).
    {#MD2.0.3.33-3} At k = 1 the display also has the lw term Σ_{i∈n}‖Y_i‖.
  - {#MD2.0.3.34} Only the attached parts made at step k stay in (ii).
    {#MD2.0.3.34-1} Those made at earlier steps are bounded by (ii′) below, per large-field component.
    {#MD2.0.3.34-2} An object made at step j has decay length λ_{k,j} := ML^{−(k−j)} in step-k units (V4's LM, fine units at step 1, M in step-1 units; the scale-j lattice is T_{L^{−(k−j)}} in step-k units, (1)).
    {#MD2.0.3.34-4} The wrap terms stay in (ii) for every j: each grows by at most L per step, so the scale-j one is ≤ CL^{k−j}ρ̂_je^{−c_att N^{(j)}_min/M}, small under the torus condition of (5)(g); ρ̂_j here is max(C_S′ρ̂_j, C_S″b_j) (D2.6 closure 2.1; (5)(g) amended).
    {#MD2.0.3.34-5} Distances are step-k distances.
  - {#MD2.0.3.35} d_j(n) is the distance from n to the scale-j large-field data: E(B_ξ) of the step-j labels, together with the de-younged bonds of the step-j carrier on uncovered terms (d(n), d^Λ(n) of D1(ii) at j = 1).
    {#MD2.0.3.35-1} N^{(j)}_min is the smallest torus period in step-j units (V4's N_min/L at j = 1). 𝔪̂^{(j)}_Δ and m^{(j)}_b are the marks and shifts of the step-j labels (IT-1 note §3a(7), §3j). ρ̂_j = max(ρ_j, ρ_{ph,j}) and ρ_{t,j} are the step-j analogues of ρ̂ and ρ_t.
    {#MD2.0.3.35-2} *Fixed here:* r_k := A₁(log g_k⁻²)^{p₀}, ρ_k := C_ρg_k²(1+r_k)⁴ (the step-k analogue of V4's ρ = O(g₀²(1+r)⁴)), ρ_{t,k} := C′_χg_k(1+2r_k)/u_* and ρ_{ph,k} := C_phg_k²(1+2r_k)⁴, as at k = 1 below.
    {#MD2.0.3.35-3} D2.2 proves its bounds with these ρ's.
  - {#MD2.0.3.36} At k = 1 this is D1(ii), summed over the L fine traversals of each coarse bond, with C_χ ↦ L^{−1}C_χ by (a) (V4's traversals are fine, V4 sec:main-result *Notation*), and:
    - {#MD2.0.3.37} the attached constants C ↦ e^{2c_att/M}LC: L fine traversals, each with e^{−c_att(d(n_f)−1)/(LM)} ≤ e^{c_att/(LM)}e^{c_att/M}e^{−c_att d_1(n)/M};
    - {#MD2.0.3.38} D1(ii)'s collar term has g₀ and D(1)(ii) has g₁: C′_χ ↦ (1+β₀)C′_χ by g₀ ≤ (1+β₀)g₁ (the last inequality of CRE (2.6), p.255, n = 1, m = 0); likewise V4's ρ (at g₀) ≤ C(1+β₀)⁶ρ₁ with ρ₁ := C_ρg₁²(1+r₁)⁴ as in (5)(c).
    - {#MD2.0.3.39} The remaining conversions. ρ_t ≤ (1+β₀)²ρ_{t,1} with ρ_{t,1} := C′_χg₁(1+2r₁)/u_*: V4's ρ_t = u_t/u_* = C′_χg₀(1+2r)/u_* (V4 app:thresholds, item 4), g₀ ≤ (1+β₀)g₁ as above, and r ≤ (1+β₀)r₁ by the second inequality of CRE (2.7) (n = 1, m = 0); u_* is fixed before the coupling (V4 app:thresholds, opening list).
      {#MD2.0.3.39-1} In the same way ρ_ph ≤ C_phg₀²(1+2r)⁴ (V4 sec:c5-5R, under (c5-5R-T)(iii)) gives ρ_ph ≤ (1+β₀)⁶ρ_{ph,1} with ρ_{ph,1} := C_phg₁²(1+2r₁)⁴, so ρ̂ ≤ C(1+β₀)⁶ρ̂₁, with C absorbing V4's O(·) in ρ = O(g₀²(1+r)⁴).
      {#MD2.0.3.39-2} The collar term of D(1)(ii) is the sum of D1(ii)'s collar terms over the L fine traversals of n, so its constant is L times D1(ii)'s; the decay converts exactly, e^{−ηdist(Δ,n_f)/(C_FLM)} ≤ e^{−η_Vdist(Δ,n)/(C_FM)} ≤ e^{−c_*′dist(Δ,n)/M} (IT-1 note §3a(7): fine distances are L times step-1 distances, and dist(Δ,n_f) ≥ dist(Δ,n)).
  - {#MD2.0.3.40} The first term bounds the species dev; the others bound att(k, ·), att(k, coll), lw(·) (at k = 1) and wrap(·), which carry no deviation.
    {#MD2.0.3.40-1} The attached species made at step j leave (ii) at the end of step j + 1's map and are bounded from then on by (ii′).
- {#MD2.0.3.41} *D(k)(ii′), attached parts of earlier steps, species by species.* For every j < k and every step-j large-field component Z, with the outer sums over the step-k traversals n of C, the sums in N_j over the step-j traversals n_j of C, and d_j^Z(n_j) the step-j distance from n_j to Z's step-j data:
  - {#MD2.0.3.42} (ii′-a) att(j, Z): Σ_nΣ_{W∋n, W∈att(j,Z)}e^{θ(W)}‖Y_W‖ ≤ Cρ̂_jN_j(Z), N_j(Z) := Σ_{n_j}e^{−c_att d_j^Z(n_j)/M}.
    {#MD2.0.3.42-1} *At every later step n, in place of the display above (D2.6 closure §5.0, §5.2 (T0)):* each insertion is counted once, at the first of its traversals, with the carried weight w(W) := e^{ν_rσ_j(W)}e^{(3/8)ν_e·ext^{coll}_n(W)}e^{θ(W)}‖Y_W‖ (ext^{coll}_n in π_n-sides from Coll_j);
    {#MD2.0.3.42-2} the statement is the product form: the att(j, Z) products present at step n, summed over the terms of the multilinear expansion, are ≤ Π_{D∈𝔅_j}(1 + e^{c_W}w(D)Π_{m=j}^{n−1}(1+δ_m)) ≤ exp(2A_j(Z)), 𝔅_j the production set, A_j(Z) the production total of (5)(f) with its constant enlarged by e^{c_W}, so that Σe^{c_W}w ≤ A_j(Z) (closure §5.0, §7.1), δ_m as in the stability bullet below;
  - {#MD2.0.3.43} (ii′-b) att(j, coll), a total split by component: Σ_nΣ_{W∋n, W∈att(j,coll)}e^{θ(W)}‖Y_W‖ ≤ Σ_ZB_j(Z), B_j(Z) := Cρ_{t,j}[Σ_{Δ→Z}𝔪̂^{(j)}_ΔN_j(Δ) + C′_χg_jΣ_{b→Z}h(m^{(j)}_b)N_j(b)], N_j(x) := Σ_{n_j}e^{−c_*′dist(x,n_j)/M}, the inner sums over the marks Δ and inputs b assigned to Z. The right side is the sum over n_j of D(j)(ii)'s collar term, regrouped by the assignment of the marks.
    {#MD2.0.3.43-1} (5)(f) charges B_j(Z) to Z through ∏_W(1+‖Y_W‖) ≤ exp(Σ_W‖Y_W‖) ≤ ∏_Ze^{B_j(Z)}, so its A_j(Z) is unchanged.
    {#MD2.0.3.43-2} The split is of the bound, not of the insertion, so it does not depend on the field and analyticity is kept; the carry below applies to the total;
  - {#MD2.0.3.44} (ii′-c) lw(Z) (j = 1): Σ_nΣ_{i∈n, i→Z}‖Y_i‖ ≤ Σ_{i→Z}‖π(T̂_iT_i^{−1}) − 1‖.
    {#MD2.0.3.44-1} Its size is the D2.6 item named under *Species*: bounded in WILSON_IT1_D26_CLOSURE_2026_10_24.md §6.3 on every labelled term (classes (I)–(III), not only A^fin_cov; the slots Y_i of closure §6.1 in slot form), with the weighted production total lw_1(Z) ≤ (C_{lw}g₀(r+1) + C_{lw}^{III})M_VR₁(d₁′(Z)+1) of closure 6.3 (class-(I) slots bounded by C_I″g₀(r+1) on the polydisc; 7.1 doubles the class-(I) part for the label cost); the label sum of IT-1 §3j(0) is D2.7's (closure 6.5 *No merge within D2.6*, *Near slots*).
    {#MD2.0.3.44-2} Z₁ = Λᶜ (CRE (2.3) with IT-1 §3c(4⁗)(d); closure 6.2 *The components*), every free bond of J(Λ) lies in E(Z₁) (closure 6.2 *Where J(Λ) lies*), so every slot with Y_i ≠ 0 is an lw(X) insertion of the nearest component X of Z₁ within R_t + 2L + 1 ≤ ℓ, no merge of label polymers is made within D2.6, and the slots' Λ-dependence within 2ℓ of a second component is a link of D2.7's joint linking expansion;
    {#MD2.0.3.44-3} the lineage weights and reserve counts of the carried slots are in closure 6.4 *Reserve and extent*: the class-(I) slots are carried as the pieces Y_{i,X}, the lineage extent is measured from the 2ℓ-neighbourhood 𝒩₁′ of Λᶜ (closure 5.6: Ret(Λ) ∩ Ω₂ = ∅ by CRE (3.5), and the bridge at every step), and the carried total is ≤ 2·lw_1(X).
  - {#MD2.0.3.45} The constant of (ii′-a) does not fit the other two: ρ_{t,j} = C′_χg_j(1+2r_j)/u_* is of order g_j(log g_j^{−2})^{p₀}, ρ̂_j of order g_j²(log g_j^{−2})^{4p₀}, and a collar mark can be a fixed constant (IT-1 note §3a(8)), so the collar parts exceed Cρ̂_j by a factor of order 1/(g_j(log g_j^{−2})^{3p₀}).
    {#MD2.0.3.45-1} Each species therefore keeps the bound it has when it is made.
  - {#MD2.0.3.46} The carry from k to k+1 does not increase the left sides: a group that meets a new traversal n′ meets one of the L old traversals in n′, and distinct new traversals contain disjoint old ones.
    {#MD2.0.3.46-1} So no factor L per step appears, for each species line by line.
  - {#MD2.0.3.47} Only the per-component totals are controlled.
    {#MD2.0.3.47-1} At step n > j a step-n segment parallel to step-j data contains L^{n−j} step-j traversals, each carrying up to Cρ̂_j, so these species do not satisfy the per-segment cost e^{Cτ_n²} of (5)(f); (5)(f) pays them through (ii′), (ii′-b) at its own scale ρ_{t,j} times the marks, and (ii′-c) by D2.6 closure §6.3.
  - {#MD2.0.3.48} Stability of (ii′) under the evaluation at U_{k+1} and under the fluctuation parts of (5)(d) is WILSON_IT1_D26_CLOSURE_2026_10_24.md §5 (carry lemma): the att bounds are sup bounds on 𝒟^{sub} over D(j)(iii)'s ω-polydiscs, so the evaluation at U_{n+1} does not grow them (§5.1);
    {#MD2.0.3.48-1} a touched part must bridge from Coll_j to Ω_{n+1}, ≥ 5R_{n+1} π_n-sides, paid by the lineage weight e^{(3/8)ν_e·ext^{coll}} and the bridge's reserve, so the descendants made at step n+1 have weighted mass ≤ δ_n times the mass present, δ_n := C_δc̄e^{−(25/8)(ν_e/L)R_{n+1}} (L ≥ 16, closure §5.0), and Σ_nδ_n ≤ C_δc̄S_R ≤ log 2 by the running of the coupling (the window's pairwise form, #MD2.0.5.2-1).
    {#MD2.0.3.48-2} The statement is a product form: the att(j, Z) products at step n are bounded by Π_{D∈𝔅_j}(1 + e^{c_W}w(D)Π_m(1+δ_m)) ≤ exp(2A_j(Z)), A_j(Z) the production total normalised as Σe^{c_W}w ≤ A_j(Z) (c_W := c_sh, the share constant of (12)(d), taken once per insertion; closure §5.0, §5.5) (closure §5.0, §5.2 (T0) with the first-member injection, §5.3); multi-parent and merged insertions (§5.5); the older layers' transports (§5.4).
- {#MD2.0.3.49} *Norms, at every scale j ≤ k, in step-k units except where stated:*
  - {#MD2.0.3.50} |Q_k(𝔅)| ≤ ∏_{W∈𝔅}e^{θ(W)} with θ(W) ≤ νσ(W)/16; the insertions of species dev, att(k, ·), wrap(·) by (ii), those of species att(j, ·), j < k, by (ii′), as in IT-1 note §4.
    {#MD2.0.3.50-1} *At steps k ≥ 2 (D2.4(3)):* σ is σ_k = #_k + n_k/M, the π_k-cubes of the constituents' domains plus the step-k traversals of the arc in units of the π_k-side (D2.4(12)(a)), since the vacuum weight is proportional to volume; θ_k = θ_vac + θ_ref is the fresh weight of the step-k gas and does not carry θ_{k−1};
  - {#MD2.0.3.51} the step-j local terms e^{(j)}_X of 𝓔_k are indexed by ∗-connected unions X of boxes of the lattice integrated at step j, anchored at the step-j segments i, with Σ_{X∈𝒳^{(j)}_i}|e^{(j)}_{i,X}|e^{κ#boxes(X)} ≤ Cτ_j²e^{−c_thd^{(j)}_i}, and Σ_{X∩Q≠∅}|e^{(j)}_X|e^{κ_{a₂}#cubes(X)} ≤ (a₂/ℓ₀+2)⁴C_rτ_j² for every cube Q of side a₂ (IT-1 note §3i(7) at j = 1, where a₂ is written a), with e^{(j)}_X := Σ_ie^{(j)}_{i,X}.
    {#MD2.0.3.51-1} Here ℓ₀, a₂, κ_{a₂} and d^{(j)}_i (rate c_th) are in the units of the lattice integrated at step j, not in step-k units: a cube of side a₂ in step-k units meets up to (a₂L^{k−j+1}/ℓ₀ + 2)⁴ boxes of the lattice integrated at step j (the scale-(j−1) lattice), so a per-step-k-cube bound of the scale-j terms is not uniform in k − j.
    {#MD2.0.3.51-2} (5)(f) therefore pays the old terms in the anchored, per-component form (D2.6);
  - {#MD2.0.3.52} The constant E_const,k is bounded step by step (D2.3(7), (5)(g)):
    {#MD2.0.3.52-1} |E_const,k| ≤ Σ_{j≤k}C𝔞_j(n_je^{−c^Zι_{T,j}} + (n_j+1)e^{−c_En_j}), the remainder of step j carrying 𝔞_j = max(τ_{j−1}², ρ_j·pl), with n_j := s_{j−1} = ℓ_CL^{K−j+1}, the side of C in step-(j−1) bonds ((5)(g)'s n_k ≍ ℓ_CL^{K−k} is the same count with the index of the step's input lattice), and holds for the admissible sides of D2.3(4), where every step is commensurate.
    {#MD2.0.3.52-2} Without that restriction each of the at most a* other steps adds Cτ_{j−1}²(Π_j + 1 + 4s_{j−1}), Π_j the period of D2.3(4), and a* does not grow with K.
- {#MD2.0.3.53} *D(k)(iii):* for real U_k in the support of the term's indicators, which are kept as factors, the background-dependent factors extend analytically to 𝐔 = e^{iη_kA′}U_k, for complex parts satisfying the per-bond bounds of the complex part of (2.39) on each Ω_n∖Ω_{n+1} (the loop's factors are not localised in Bałaban's domains X ∈ 𝐃_k): |η_kA′| < (1 − β(1 − 2^{−(k−n)}))α_{1,n}L^{−n} per fine bond on Ω_n∖Ω_{n+1} (n < k) and on Ω_k (n = k), G-covariantly.
  {#MD2.0.3.53-1} For k = 1 this sup-only domain is the domain; it is larger than CRE's Ũ_k^c, which also asks (L^nξ)²|∇_U^ξA′| < (1−β(1−2^{−(k−n)}))α_{1,n}, and it is D1(iii)′'s form.
  {#MD2.0.3.53-3} (ii) holds there with δ*^{(k),c}_n(U_k) + a*^{(k)}_n(A′) in place of δ*^{(k)}_n(U_k), with ρ_{ph,k} replaced by ρ^c_{ph,k} := C^𝐔_phg_k²(1+2r_k)⁴(1 + (log g_k⁻²)^{(q₁−p₀)₊}), and with the tilt marks 𝔪^δ_Y included in 𝔪̂^{(k)}; at k = 1 this is IT-1 note D1(iii)′ (§3e(0); (3.12) *Order* and *Tilt marks*).
  {#MD2.0.3.53-4} The tolerance this needs is D2.4's. Here δ*^{(k),c}_n is δ*^{(k)}_n with the weights (t+1)³e^{−(61/16)η_Vt}, and a*^{(k)}_n(A′) := η_k^{−1}Σ_{t≥1}(t+1)e^{−(61/16)η_Vt}max{|η_kA′(b)| : b a fine bond within step-k distance R_t^{(k)} of n}: the step-k forms of IT-1 note §3e(0)'s δ*^c_n and a*_n(a′), at the complex rate 61/16 of D2.6 closure §6.5 *(iii)'s complex rate*.
  {#MD2.0.3.53-5} The normalisation η_k^{−1} makes a*^{(k)}_n a block-scale field: along a step-k bond the first-order change of the transport is Σ_bη_kA′(b) over its L^k fine bonds, of size |A′|.
  {#MD2.0.3.53-6} At k = 1, a*^{(1)}_n ≥ L·a*_{n_f} for every fine traversal n_f ⊂ n, as in (a).
  {#MD2.0.3.53-7} At k = 1 the radius is ϱ_{an,1} := α_{1,1}/L, IT-1 note §3e(0)'s ϱ₁ in D1(iii)′ (ρ₁ is the insertion scale of (5)(c)).
  - {#MD2.0.3.54} *The domain for k ≥ 2 (D2.2(6)(e)).* For k ≥ 2 the domain is CRE's: the full complex part of Ũ_k^c at 𝐔 = e^{iη_kA′}U_k, that is (2.34) for 𝐔 and (2.36) for 𝐉 per plaquette and bond, (2.38) per cube, and (2.39) per bond with both the sup and the gradient condition, (L^nξ)²|∇_U^ξA′| < (1−β(1−2^{−(k−n)}))α_{1,n}, posed on Ω_n∖Ω_{n+1} for n = 1, …, k−1 and on Ω_k.
    {#MD2.0.3.54-0} (2.35) and (2.37), which constrain the averaged configurations built on a domain X, are posed for each factor that uses them on that factor's own domain (Bałaban's X ∈ 𝐃_k, CRE p.261; the domain Z of RG2 p.15's covariance operators for the step's Ĥ(M), D2.2(6)(c), #MD2.2.6.131).
    {#MD2.0.3.54-1} The step-(k−1) → k integration produces factors with RG2's propagators, which are analytic only on a gradient-controlled domain (RG2 p.15).
    {#MD2.0.3.54-2} The sup-only form above stays at k = 1.
    {#MD2.0.3.54-3} The ω-clause below has radii r^{(k)}_{ω,j} per layer j (D2.2(6)(e)).
    {#MD2.0.3.54-4} *The ω-clause at complex configurations (D2.2(4)(d′), Step 8, and D2.2(6)(b7), *G^c-valued u*).* At a configuration 𝐔 of the polydisc that is not the step's output at its own data, the step's representative Ax_k at 𝐔 is Ax_k at the minimiser Ū at 𝐔's averages transformed by the B′-independent c₀(𝐔), so by Cov (D2.2(6)(b7)) a slot value σ at 𝐔 is the slot value R(c₀(𝐔))^{−1}σ in the frame of Ū, where the plain clause holds;
    {#MD2.0.3.54-5} here c₀(𝐔) := 𝐔(Γ^{(k)})^{−1}Ū(Γ^{(k)}) the mismatch of the hierarchical transports of 𝐔 and of the minimiser Ū at 𝐔's averages, G-valued at real 𝐔 and G^c-valued at complex 𝐔, analytic in 𝐔, and equal to 1 on the frame family (Step 8's family (I): the configurations U^{rep}_k(V) at real or complexified level-k data V, which contains the outputs and their continuations to complexified data).
    {#MD2.0.3.54-6} The step map invokes the clause on the frame family, except at (11)(c)(β)'s polydisc points with a″ ≠ 0, where the clause is used on 𝒟^{sub} with the rotation by the evaluation point's c₀ charged to (4)(c)'s per-step margin (#MD2.4.11.5).
    {#MD2.0.3.54-7} So the ω-clause at 𝐔 holds for the slot values σ with R(c₀(𝐔))^{−1}σ in the polydisc of radius r^{(k)}_{ω,j} around the real support.
    {#MD2.0.3.54-8} At real 𝐔 the rotation is real orthogonal and preserves the polydisc, so the clause is the one above; at complex 𝐔 this is its analytic continuation, with σ̂ := R(c₀(𝐔))^{−1}σ as the analytic coordinate in D2.1(2)'s identity theorem jointly with the configuration.
    {#MD2.0.3.54-9} The radii and their propagation (D2.2(6)(e), #MD2.2.6.175) are unchanged, as the propagation runs on the frame family.
    - {#MD2.0.3.55} *Conditions on the base point.* CRE's space also has two conditions on the real factor U, and its analyticity statements are made on that space: the real-U part of (2.34), |∂U − 1| < (1 − β(1 − 2^{−(j−n)}))α_{0,n}ξ²(L^nξ)^{−2}, and condition (ii), (2.38) (p.261): for each cube □ ⊂ Ω_n∖Ω_{n+2} with □ ∩ Ω_{n+1}ᶜ ≠ ∅ of size CML^nξ, or □ ⊂ Ω_j of size CM, a gauge transformation u on □ ∩ X with U^u = exp iξA, L^nξ|A|, (L^nξ)²|∇^ξA| < BCMα_{0,n}.
      {#MD2.0.3.55-1} Both are required of the base point U_k here.
  - {#MD2.0.3.56} *The variable 𝐉 for k ≥ 2 (D2.2(6)(b)).* For k ≥ 2 the factors are functions of (𝐔, 𝐉, ω), and the domain is posed on (𝐔, 𝐉): with the conditions above, CRE (2.36)–(2.37), p.261, |𝐉| < (1 − β(1 − 2^{−(k−n)}))α_{0,n}(L^nξ)^{−3} on each Ω_n∖Ω_{n+1} and on Ω_k (CRE's space Ũ_k^c is "the set of configurations (𝐔,𝐉)", p.261).
    {#MD2.0.3.56-1} Covariance is under (𝐔, 𝐉, ω) ↦ (𝐔^u, R(u)𝐉, R(u)ω) (CRE p.261: "(G-valued) gauge transformations of 𝐔, 𝐉, A (the variables 𝐉, A are transformed by the adjoint representation of the gauge transformations)").
    {#MD2.0.3.56-2} The factors are evaluated at 𝐉 = J_k.
    {#MD2.0.3.56-3} At k = 1 the factors are V4's, functions of 𝐔 and, on uncovered terms, of the exterior fields; there is no 𝐉.
    - {#MD2.0.3.57} *The 𝐉-term of (ii).* The dev parts are functions of 𝐉 that vanish at (1, 0, 0), so the bound of (ii) on this domain needs a deviation term in 𝐉 − J_k; without it, at flat U_k with A′ = 0 and 𝐉 ≠ J_k, the bound would force the dev parts to vanish.
      {#MD2.0.3.57-1} With r_J(b) := (1 − β(1 − 2^{−(k−n)}))α_{0,n}(L^nξ)^{−3}, the (2.36) radius at b, and ϱ(b) := (1 − β(1 − 2^{−(k−n)}))α_{1,n}L^{−n}, the A′-radius, put
      {#MD2.0.3.58} j*^{(k)}_n(𝐉) := η_k^{−1}Σ_{t≥1}(t+1)e^{−(61/16)η_Vt}max{ϱ(b)|𝐉(b) − J_k(b)|/r_J(b) : b within step-k distance R_t^{(k)} of n}, at the rate of δ*^{(k),c} and a*^{(k)}.
      {#MD2.0.3.59} For k ≥ 2, (ii) holds on the (𝐔, 𝐉) domain with δ*^{(k),c}_n(U_k) + a*^{(k)}_n(A′) + j*^{(k)}_n(𝐉).
      {#MD2.0.3.59-1} At the real point 𝐉 = J_k the new term vanishes, so (ii) at real data is unchanged, and D(1) has no 𝐉.
      {#MD2.0.3.59-2} *Sub-domain form (SW closure §3):* this dev-term bound at complex data is asserted on 𝒟_k^{sub} only (the top-layer radii α_{1,k}L^{−k}, α_{0,k}(L^kξ)^{−3} with the layer's factor on every layer); analyticity stays on the full domain; the per-insertion form likewise, with Dev_W over the per-traversal region of SW closure §5(e).
      {#MD2.0.3.59-3} The 𝐉-part of the dev bound is proved with the rest, by D2.4(4)'s Cauchy step, which runs in 𝐉 on the (2.36) polydisc as in A′ (SW closure (6b)).
  - {#MD2.0.3.60} The outer fields ω_j, j ≥ 1, are slot variables: the old A_j, which receive the values ψ_{j+1}(A_j^{new}; 𝐇^{(j)}) on S_{j+1}^{(j)*} and A_j elsewhere (D2.2(6)(b)).
    {#MD2.0.3.60-1} The ω-clause is analyticity in the slot variables.
    {#MD2.0.3.60-2} The same holds at j = 0, by #MD2.0.3.60-3–#MD2.0.3.60-4.
    {#MD2.0.3.60-3} On the bonds of (R₁^{∼2} ∩ S₁)^* V4's variable is A′, with A = Ψ_ξA′ through the C^∞ cutoff ω_b (V4 (native-source-exact-boundary-map)), and the slots are not analytic in A′ there.
    {#MD2.0.3.60-4} So at j = 0 the outer variable ω₀ is CRE (1.15)'s A = Ψ_ξA′, a slot variable; A′ and the cutoff values ω_b(A′(b)), frozen as real factors at the real configuration (as in D2.2(6)(e), *The radii*), only give its values, and the later rotations R(w) act on these values (#MOMGD.52).
    {#MD2.0.3.60-5} The lw slots' bounds on the r_{ω,0} = 1 polydisc are in the closure (§6.1 (a)–(b)).
  - {#MD2.0.3.61} *Outer fluctuation fields.* The ω-dependent factors (the insertions that consult outer fluctuation fields, on uncovered terms) extend analytically also in ω, jointly with 𝐔, to the ω within distance r_ω^{(k)} of a real point of the support, per bond (per layer j, r^{(k)}_{ω,j}: the polydiscs of D2.2(6)(e)), with the same bounds.
    {#MD2.0.3.61-1} The radii r^{(k)}_{ω,j} = r_{ω,j}(1/2 + 2^{−(k−j)}) are in the units of the slot variable σ_j (the old A_j, in step-j units), and r_{ω,j} is fixed at step j and does not change with k (D(k)(iv) concerns constants, and r_{ω,j} is a scale-j radius); the step-1 exterior fields have index j = 0, with r_{ω,0} = 1 in B-units.
    {#MD2.0.3.61-2} The original field V₀ on Ω₁ᶜ is part of 𝐔, not of ω.
    {#MD2.0.3.61-3} *At k = 1.* In V4's free variables B (phases A = g₀𝖢_UB, equal to g₀B on free bonds, V4 sec:source-phase-primitives), the exterior fields A_e and a_old enter the ω-dependent factors in three ways.
    {#MD2.0.3.61-4} They enter the cross term s⟨a, H_{ξ,IJ}A_e⟩ of (c4-11-1), which is linear, hence entire.
    {#MD2.0.3.61-5} They enter the near primitives 𝔭(a + sA_e) of (c4-11-1).
    {#MD2.0.3.61-6} They enter the row solutions and path products of the rows they feed.
    {#MD2.0.3.61-7} V4 Lemma charts makes the row solution and the functions it lists analytic in B|_{𝓔_c∩E_*} on 𝒰_c = {|B(b)| < 2 + 4r}, for every row within 2R_c + 2L of I, on every branch.
    {#MD2.0.3.61-8} On the support of the term's indicators the real inputs of these rows satisfy |B(b)| ≤ 2r on D(Λ) and |B(b)| < r on I∖D(Λ) and on J (IT-1 note §3d(2)(d), after S-A).
    {#MD2.0.3.61-9} So every ω-dependent factor is analytic, jointly with the background, for |Im B(b)| < 2 per bond, which gives r_ω^{(1)} := 1 in B-units with room to spare.
    {#MD2.0.3.61-10} The joint background radius is that of V4 Section c4-10-1.
    {#MD2.0.3.61-11} Its propagation to D(k+1)(iii) is D2.2(6)(e).
    {#MD2.0.3.61-12} *The bound clause (D2.6 closure §4.2(iii)).* At k = 1 the analyticity is shown above, and the bounds at complex ω₀ are closure §5.0's, for the t > 0 species on the sub-polydisc 𝒟^{sub}_{ω,0} of radius ρ_ω ≪ r_{ω,0} around the term's step-1 exterior data, which contains every point the consumers evaluate at (WILSON_IT1_O4_CLOSURE_2026_10_26.md §2(e); for the lw slots, closure §6.1 *The ω-polydisc*).
    {#MD2.0.3.61-13} For the ω-dependent members made at steps k ≥ 2 the bounds over the polydiscs rest on O6 (closure §2.2 (1′)), and the evaluation of every factor on Ω₁∖Ω₂ rests on the base points of D2.2(6)(e) *The inclusion*, at every k.
  - {#MD2.0.3.62} *Reference clause (D2.3(2)).* On every labelled term ℓ the background-dependent factors are defined and analytic also at 𝐔 = e^{iη_kA′}·1, A′ in the domain above, for k ≥ 2 with 𝐉 in the domain of (2.36)–(2.37) around 𝐉 = 0 = J(1), jointly with ω within its radii of ω = 0, although (1, 0) need not lie in the support of ℓ's indicators.
    {#MD2.0.3.62-1} At k = 1 this is V4 Section joint-extraction, the reference-data paragraph after (part1-grouped-source) (the step-1 lemmas "apply to U = id directly", on every branch); at step k+1 D2.3(2) derives it from D2.2(6)(e)'s argument at U_{k+1} = 1.
    {#MD2.0.3.62-2} The bounds at the reference point are D2.4's.
- {#MD2.0.3.63} *D(k)(iv):* all constants are independent of k, K, the contour size, the torus and the labelled term.
- {#MD2.0.3.64} *D(k)(v), scalar parts (added from D2.2(4)(a)).* On each labelled term, Q_k(𝔅) and 𝓔_k depend on the labels only, not on V_k and not on the outer variables: they are numbers given the labels, as at k = 1 (IT-1 note §4(iii): "φ and e_X are numbers on each labelled term"; q°, E° are built from the reference data U°₁ = id with the term's labels, V4 Lemma c5-5-3(b), (d) and IT-1 note §2(g), and E^∂_{D(Λ)} at flat reference data, IT-1 note §3b(5)).
  {#MD2.0.3.64-1} Field-dependent scalar parts are scalar insertions.
  {#MD2.0.3.64-2} At step k+1 it is proved in D2.2(6)(c).
- {#MD2.0.3.65} *D(k)(vi), torus consistency (D2.3(4), item (Z); for the insertions in local-agreement form and for the cluster weights φ_k(Γ), numbers given ℓ, D2.3(4) (Z-e); in summed form: on ℓ₀, for (𝐔, 𝐉) on T and (𝐔′, 𝐉′) on T′ ⊃ T that coincide under the covering on the ι_{T,k}/4-neighbourhood of a lift of the dependence set of each W that embeds in T, (I) Σ_{W∋n, embeds}e^{θ(W)}|ΔY_W| ≤ C_rel^{(k)}e^{−c_kι_{T,k}}·(D(k)(ii)'s right side, the larger of its T- and T′-values) and (O) sup_bΣ_{Γ∋b, embeds}|Δφ_k(Γ)|e^{a°(Γ)} ≤ C_rel^{(k)}e^{−c_kι_{T,k}}ρ_k·pl per position b (the form D2.4(13)(c) carries;
  {#MD2.0.3.65-1} the "hits W" form follows by the ≤ 81Mσ_k(W) positions of a group incompatible with W), φ_k being numbers given ℓ; the step-1 base is D2.3(4)(Z-h)).* For a cluster Γ of the reference group gas of the step-k output on the trivial-label term ℓ₀ (D2.3(3)) whose groups have short arcs on a straight line or on a bent path, the weight Φ°(Γ; T) is defined on every torus T of the sequence (H3) in which Γ embeds (dependence set of diameter < ι_T/4, D2.3(4) (Z)), and has a limit Φ°^∞(Γ) as the periods grow, with Σ_{Γ: b∈J_Γ}|Φ°(Γ;
  {#MD2.0.3.65-2} T) − Φ°^∞(Γ)| ≤ 3C_Z^{(k)}𝔞_ke^{−c^Zι_{T,k}} (#MD2.3.4.50) for every traversal b, 𝔞_k := max(τ_{k−1}², ρ_k·pl) (amplitude from D2.3(4)(Z-f)).
  {#MD2.0.3.65-3} At k = 1 this is D2.3(4)(Z-h) (V4's step-1 objects are exactly local: zero difference on embedding objects) with (Z-f)'s non-embedding clusters; V4's periodisation is not used.
  {#MD2.0.3.65-4} Its carrying to step k+1 is D2.3(4)(Z-f) with D2.4(12)(f), (13)(c), given D2.4's (S-w).
- {#MD2.0.3.66} *D(k), the identity.* The numerator density after k steps is N_k^C = Σχ_k(Ω_k)T_k[𝒲_k exp A_k], over the admissible sequences of ρ_k.
  {#MD2.0.3.66-1} For k ≤ N the basic step of the 𝐑-operation (LFR I Sect. 1) acts on no component (LFR I p.177 (ii)), R is the identity on every term for k ≤ N (WILSON_IT1_D27_CLOSURE_2026_10_26.md item 1), and so N_k^C is T applied k times to W(C;U)ρ₀ with CRE's expansions.
  {#MD2.0.3.66-2} From step N + 1 on, R acts on the numerator; D2.7.
  - {#MD2.0.3.67} *LFR I p.177 (ii) for the basic step.* LFR I p.177 applies the 𝐑-operation to components of Λ_k^c that satisfy (ii): "in the preceding N renormalization steps no new large field regions were created inside this component".
    {#MD2.0.3.67-1} Every component of Λ_k^c contains a region created at some step j ∈ [1, k], so for k ≤ N, (ii) fails if "the preceding N steps" includes all of the k steps that exist. p.178 (1.2) writes T_k(Z) through the last N one-step operations, from h = k − N, which needs h ≥ 0, i.e. k ≥ N; and (ii) excludes k = N. The print does not state the case k ≤ N. For the basic step it follows from (ii) as printed, since ρ₀ has no large-field region and every region inside a component was created at a step j ≤ k ≤ N, i.e. within the preceding N steps.
- {#MOMGD.47} *D(1).* D(1) is IT-1's D1 on V4 with the labels of D1.0(P) (D2.3(4), (Z-h)). The IT-1 note derives D1 and D1.0(P) under repairs K and K′ of V4's constant chain (IT-1 §3e(3.0), (3.6)), the g₀-thresholds of IT-1 §3c(2)(e), §3e(4) and §3f(2) (R1, R2 and Minor 4), and the enlarged retreat 𝒬⁺ (IT-1 §3c(4⁗)(c)), each a choice of a constant before the coupling or a smallness condition on g₀.
  {#MOMGD.47-1} The changes transfer to V4's uses: K by IT-1 §3e(3.0) and (3.11), 𝒬⁺ by IT-1 §3c(4⁗)(c), K′ by IT-1 §3e(3.6) *Repair K′*, and the new thresholds, each a condition on g₀ alone, by IT-1 §3e(4).
  {#MOMGD.47-2} D1.0(P)(ii)'s j = 1 factor at the steps k ≥ N + 1 rests on D2.7 (WILSON_IT1_D27_CLOSURE_2026_10_26.md) and on the acceptance item of WILSON_IT1_O2_CLOSURE_2026_10_26.md §4.2 (IT-1 §3f(2) R1 (ii) and Minor 4).

### (4) The Large-Field Parts: D2.6 and D2.7 {#MSD2.0.4}

- {#MD2.0.4.6} *D2.6, large fields* (WILSON_IT1_D26_CLOSURE_2026_10_24.md).
  {#MD2.0.4.6-1} Every evaluation point of the step lies in the analyticity domain of every factor by *The inclusion* (#MD2.2.6.189) and CRE p.277's margin (closure 2.2). At complex σ_k the terms of 𝐏^{(k)} keep the printed bound with the fluctuation factor doubled, and the bracket terms keep p.277's coefficient O(ε_k) times 2, with the decay rate reduced by ϑ_k → 0 (O6 §5, §5a; closure 2.2 *Complex σ_k*). The band-cube input of (T-dev) holds on every band cube, those with □′^{∼4} ⊄ Ω_{i+1} by route (a) (closure §8.3).
  {#MD2.0.4.6-3} The carried t > 0 species are bounded over complex backgrounds by WILSON_IT1_O4_CLOSURE_2026_10_26.md. At step n the term is expanded at the real centre tm̂, m̂ := m̂(𝐔(U_{n+1}), ω₀,₀), where 𝐔(U_{n+1}) is the step's real external background on the species' region, independent of the step's fluctuation, and ω₀,₀ is the term's real exterior data of step 1 (O4 §2(c); closure 6.4 *The centre*).
  {#MD2.0.4.6-4} For every real centre the expansion is exact at every real point and analytic in every field, so the carried species are IT-1 note §3j(4)'s representation at that centre, extended to the polydisc 𝒫(𝐔(U_{n+1})) by §3e(3.12). Every evaluation point of every step lies within 9ϱ₁/16 of 𝐔(U_{n+1}) per fine bond (O4 §2(b), under L ≥ 4(1+β₀)², closure 4.2's RM₁ ≥ 32log(4L·O(1))/δ₀, and CRE (2.9)).
  {#MD2.0.4.6-5} The carry lemma (closure §5) evaluates fixed members at every step, and the change of centre between steps is the change between two exact expansions of the same term. The bound over the ω₀-polydisc is stated on the sub-polydisc 𝒟^{sub}_{ω,0} of radius ρ_ω ≪ r_{ω,0}, which contains every point R(w_n(s,t))ω₀ the consumers evaluate at; the tilt constant carries the factor 1 + C_ω (closure 5.0 *The step-1 t > 0 species*, 7.1 *Step-1 marks*; O4 §2(e)).
  {#MD2.0.4.6-6} D2.2(3)(b)'s extra label for 2 ≤ k ≤ N is WILSON_IT1_O2_CLOSURE_2026_10_26.md: Λ₁ = Ω₁^{∼−2} ∩ (R₁′^∼)ᶜ with R₁ determined by S₁ (CRE (1.20) p.251, p.253, p.255), so the pair (Λ₁, Λ) carries no extra summation index: the sum over Λ₁ is CRE's own Σ_{S₁} inside 𝐓₁, (2.18) p.257.
  {#MD2.0.4.6-7} The step-1 term has CRE's inductive form with Λ in Λ₁'s role; 𝐓₁ is carried whole at the later steps ((3.1), (3.24)), and LFR II's induction takes only κ₁(X), j(X) = 1, and (1.76) per component of Λᶜ. Since Z₁ = Λᶜ contains the retreat region (closure 6.2 *The components*), the retreat slots are lw slots, carried by closure §5 with the bridge of closure 5.6 at every step, and no merge of label polymers is made within D2.6 (closure 6.5). So:
  {#MD2.0.4.6-8} Z₁ = Λᶜ, every free bond lies in E(Z₁), the slots are lw(X) insertions, Ret(Λ) ∩ Ω₂ = ∅ by CRE (3.5), the bridge holds at every step, and no merge is made within D2.6. The members and factors whose evaluation domain meets Ω₁∖Ω₂, the ω₀- and ω₁-dependent factors among them, are evaluated at every k at D2.2(6)(e)'s base points on that layer; the joint linking expansion at the 𝐑-operation is D2.7's. D2.6's items:
  - {#MD2.0.4.7} the attached terms of D(k)(ii);
  - {#MD2.0.4.8} the non-scalar large-field parts (at step 1 the att(1, Z) and wrap(1) parts of IT-1 note §3a(4), (8));
  - {#MD2.0.4.9} the exposed segments (IT-1 note §3d(3), (5));
  - {#MD2.0.4.10} the carrier at step k+1: p.256's "other conditions", domains made by a retreat, and the extra outer label (IT-1 note §3c(4′), (4⁗)).
    {#MD2.0.4.10-1} This item is an input of D2.2 and of (5)(c)'s evaluation at U_{k+1}, and is proved with D2.2 (D2.2(3));
  - {#MD2.0.4.11} the lifetime payment of (5)(f): Bałaban's induction pp.384–389 with the enlarged summand.
- {#MD2.0.4.12} *D2.7, the 𝐑-operation with a defect,* from step N + 1 on.
  {#MD2.0.4.12-1} It includes LFR I's construction of Z from Z_h after p.187 (IT-1 note §3f(3) S1).
  {#MD2.0.4.12-2} The construction part with Z₁ = Λᶜ (no observable) is RC_PAYMENT_PASS_2026_10_24.md Sect. 2, and the large-field acceptance in its Sect. 3; D2.7 keeps the observable part and the final-scale assembly at K > N ((5)(d)), for which RC_PAYMENT_PASS Sect. 4 supplies the step-1 factor.
  {#MD2.0.4.12-3} The observable part is WILSON_IT1_D27_CLOSURE_2026_10_26.md item 15, given LFR II Theorem 1, the inputs of D2.6 named there, D2.7 15.5(ii) (below), and the two-loop note's (TL #7), (TL #234), and (TL #274), with the note's 15.8 (the links in the gas, and O2 at k > N).
  {#MD2.0.4.12-6} The loop-linked part of (1.72)'s bracket is written exactly as the ratio of two polymer gases, Ξ^C/Ξ = Σ_𝔉e^{−Φ(𝔉)}A^C(𝔉) over compatible families 𝔉 of polymers meeting C, Ξ the whole bracket's gas and Ξ_{¬C}(𝔉) the gas of the polymers not meeting C and compatible with 𝔉, with the incompatibility factor Φ(𝔉) := log Ξ − log Ξ_{¬C}(𝔉) and the loop-linked activities A^C(𝔉) as traces of path-ordered tensors (15.3);
  {#MD2.0.4.12-7} at the flat reference each interleaving group of polymers contracts to a scalar by Schur (15.1, with the gauge covariance of the averaged arc, 15.2), so the flat part of the ratio is the cluster series of a one-dimensional gas along C, E_k^R(C) = P_{k−1}(C)μ_k^R + 4ζ_k^R + E°_k^R, and μ_k^R, ζ_k^R enlarge the step-k factor κ_k of κ^{(k)} (#MD2.0.3.4, #MD2.3.0.3, #MD2.3.5.5), E°_k^R staying in 𝓔_k (15.4);
  {#MD2.0.4.12-8} the remainder is a sum over marked sets S of groups, e^{E_k^R(C;V_k)}Σ_{S≠∅}e^{−Ψ(S)}tr[𝒲^{sf}(U^R) with the per-group deviations D_g at the spans of S], each D_g vanishing at pure-gauge data on hull(g)⁺, local there (hull(g)⁺ including the domains of the slots' localisation pieces, 15.5(ii)(β)), analytic on Bałaban's extension, and a dev insertion of D(k) with comparison box hull(g)⁺ and mass e^{|Ψ_g|}B(g)C·diam/r^{ext}_k (r^{ext}_k := min(r^{an}_k, c_{ext}α_{0,k}), D2.7 15.6(d)), e^{−Ψ(S)} the marked set's incompatibility factor against the group gas, with its Kotecký–Preiss bound (15.6),
  {#MD2.0.4.12-9} carried by (5)(c)'s recursion (#MD2.4.6.14) with the source C^R_k ≤ exp(−A₀(log g_k^{−2})^{p₀}/2 + log g_k^{−2} + O(log log g_k^{−2})) ≪ 1 added to C_new at the 𝐑-steps, its supremum over k bounded by its value at (1+β₀)g_K (15.7); every word of the loop is localised by Bałaban's expansion, on every bond i of C, Y_i^{𝒦} the sum of its pieces whose domains meet exactly the components of 𝒦 besides the bond's own, the far insertions joining the polymer structure as localisation domains and the attached species' supports joined to their components' polymers (15.5(i));
  {#MD2.0.4.12-10} the surviving sums are the geometric sum of the recursion and Σ_k|E°_k^R| ≤ CΣ_kMR_ke^{−p₀(g_k)/2}, finite by the window (#MD2.0.5.2-1; D2.7 15.7); the post-R dressed loop is of class D(k), with the term-dependent part E^{R,∂}_k(ℓ) of the flat cluster series attached per large-field component and charged to its reserve (15.4(iii)), and D2.6's step lemmas apply to it at every n ≤ K, with S_R and c̄ over m ≤ K, the second-class components re-entering D2.6 7.2's lifetime induction (15.8).
  {#MD2.0.4.12-11} *D2.7 15.5(ii), four clauses:* (α) the connected insertion Y_i^{𝒦} is bounded by τ_iO(1)^{|𝒦|}e^{−δℓ(i,𝒦)}, ℓ(i,𝒦) the scaled length of the shortest tree joining the bond's domain and the components of 𝒦;
  {#MD2.0.4.12-11-1} (β) every slot of the loop-linked activities is a sum of pieces, each depending on the renormalised configuration on a domain Y′ only, the piece on Y′ carrying e^{−δd(Y′∖Y′₀, Y′₀)}e^{−(κ₁−1)M^{−d}|Y′∖Y′₀|}, Y′₀ the cubes of the slot's bonds, of its components, and of (α)'s tree, the domains joining the polymer structure as localisation domains; (γ) every piece and every Y_i^{𝒦} is gauge covariant as its slot;
  {#MD2.0.4.12-12} these three follow from Bałaban's localisation expansion (LFR II p.372 l.12–28, p.373 l.13–p.376 l.13, (1.66)–(1.67)), which he makes for "any term in the sum" (p.373 l.14–15), applied to the loop's words, entire and bounded on its value space (1.65) (LFR I p.190–191), with (γ) from PBG (3.28)–(3.34), RG2 p.3 l.27–33 and (1.3)–(1.4).
  {#MD2.0.4.12-13} (α′) is the same bound for the carried insertions.
  {#MD2.0.4.12-14} The expansion's cubes are kept at distance Mt_k from Λ, t_k := ⌈(32/(δ₀M))(2log α_{1,k}^{−1} + log(L⁴R_k²))⌉, so that its s-points are perturbations of the two-loop note's (TL #7) points of at most C_Hα_{1,k}² per fine bond in L^{−k} units (CRE p.277's 𝐇-decay, #MD2.2.6.164, with VAR (190); the factor L^{k−j} on an older layer j is paid by the layers that the walks cross, CRE p.265, leaving L^{N₀+1} ≤ L⁴R_k², LFR I p.192), inside the family's slack there, with a factor e^{δt_k} per vertex of the tree.
  {#MD2.0.4.12-15} The commensurability of C's sides with the 𝐑-gas's period MR_k at every 𝐑-step follows from (Z-g)'s convention (#MD2.3.4.51) and R_j a power of L (BETA_FUNCTION_WILSON_LOOPS.md #B2.2.173; the note's 15.9(b)).
  {#MD2.0.4.12-16} That note also gives: N = N_k, the tube's depth, is step-dependent, with N_k ≤ log_L(16L⁴(L+1)²) + ν_L log_L log g_k^{−2} (D2.7 item 1(b); #MD2.3.4.16-1); the class and every exclusion are observable-independent; the density-changing operation is the integration of the term over V_k⌈_Λ, Λ ⊂ X, followed by the normalised fraction (1.100) (LFR I p.193 l.41–p.194 l.3), which preserves ∫f dV_k for every integrable f, and LFR II p.378's removal of the δ-functions on the first-class components, an equivalence that needs the integrand's invariance, so E[W(C)] = ∫RN_k^C/∫Rρ_k;
  {#MD2.0.4.12-17} the gauge invariance of the dressed loop enters the Faddeev–Popov and axial-gauge equalities of pp.195–197 and p.378 through Cov(k) ((4)(a)) and the covariance of the multi-scale minimiser (CRE (2.12)'s minimal orbit, the note's item 3); (3)(b) and (5)(c)(α) read on the post-R term; the form of 𝐑′^{(j)} for j > N; at a flat configuration the averaged block of an irreducible χ is a scalar per block shape (global gauge transformations fix the flat data and conjugate the averaged word; Schur).
  {#MD2.0.4.12-18} The 𝐑-produced terms in the small-field region are dev insertions and contract, so no carry of a constant-type species and no bridge of D2.6 §5 is needed for them (their flat part, whose per-block sum Σ_k|C|L^{K−k}e^{−p₀(g_k)/2} is unbounded in K, is in κ^{(K)}); those at second-class and unchanged components are att species at a region that stays large-field, D2.6 §5's case;
  {#MD2.0.4.12-19} (5)(d) and (5)(f) at K > N are the note's items 10–11 read with item 15's species.

### (5) The Count Check of D(k) → D(k+1) {#MSD2.0.5}

{#MD2.0.5.1} Regime: a loop of physical side ℓ_C, K steps, P_k(C) = 4ℓ_CL^{K−k}. τ_k and ρ_k are the step-k analogues of V4's τ = C[g(1+r)³ + e^{−cr²}] and ρ = O(g²(1+r)⁴) (V4 Remark main-regime (1)), r = A₁(log g⁻²)^{p₀}, so τ_k² and ρ_k are g_k² times a power of log g_k⁻².
- {#MD2.0.5.2} *The couplings.* G is compact, connected, and simple (V4 (H1)). The run is the tube construction for its target (K, g) (BETA_FUNCTION_WILSON_LOOPS.md #B2.2.171–#B2.2.180; Cauchy #CP.13). For ε = L^{−K} and every g ∈ ]0, γ′_T], γ′_T := (γ_T^{−2} + C_W)^{−1/2}, γ_T the class parameter γ of BFWL §2 (#B2.7-1, #B2.2.168; not D2.3(4)'s γ := sup_K g_K, which is taken ≤ γ′_T), it has a bare g₀ with g_K = g whose history lies in the tube H_K (Proposition 2.13, #B2.2.822–#B2.2.823).
  {#MD2.0.5.2-1} With x_k = g_k^{−2}, x_m − x_n = Σ_{j=m}^{n−1}β_{j+1}, and the window (W), which holds on the tube's histories (#B2.2.842; #B2.5), gives b(n−m) − C_W ≤ x_m − x_n ≤ b′(n−m) + C_W for all m ≤ n ≤ K, with the tube's b, b′, and C_W (#B2.2.165–#B2.2.167; Cauchy #C5.7-6).
  {#MD2.0.5.2-2} So CRE (2.6) holds with b′ + C_W for its β′, 1/g_k² ≤ 1/g_K² + (b′ + C_W)(K−k), and g_k ≤ (1+β₀)g_K uniformly in K − k for γ_T small (Lemma 2.10(b), #B2.2.268).
  {#MD2.0.5.2-3} The upper bound is g_k² ≤ C′/(K−k+1), C′ := 1/min(γ_T^{−2}, b): x_K = g^{−2} ≥ γ_T^{−2} + C_W, so x_k ≥ γ_T^{−2} + b(K−k).  {#MD2.0.5.2-4} The uniform form g_k ≤ (1+β₀)g_K is used by (3)(c)'s bound of α_{0,k}, (c)'s feedback factor (1+β₀)²g_K² and quadratic term, (d)'s factor (1+β₀)⁸L²g_K² ((1+β₀)^{10}L²g_K² against ρ̃_{k+1}, D2.4(6)), (f)'s τ̄², and D2.2(4)'s smallness conditions on g_K.
  {#MD2.0.5.2-5} The D2.6 carry lemma (D2.6 closure §5.0) uses the window bound: its sum S_R = Σ_me^{−(25/8)(ν_e/L)R_{m+1}} is bounded through x_m ≥ x_{m′} + b(m′ − m) − C, so that a window of length b in x holds at most 2 + C/b indices. (b) uses only the uniform form.

- {#MD2.0.5.3} *Convention for the deviation.* δ*_n^{(k)} is the quantity of (3): fine-plaquette deviations near n divided by the fine-plaquette area in step-k units, η_k² = L^{−2k}.
  {#MD2.0.5.3-1} The same fine plaquette has area L^{−2(k+1)} in step-(k+1) units, so the same maximum gives δ*^{(k+1)} = L²δ*^{(k)} for every U ((3)(c)).
  {#MD2.0.5.3-2} By (2), the fine plaquettes of Ω_{k+1} have |∂p − 1| < 2B₃ε_{k+1}η_{k+1}² under U_{k+1}, so δ*^{(k+1)}(U_{k+1}) ≤ 2c_σB₃ε_{k+1}Σ_tw_t there, with c_σ of (3)(b); by the lasso step a step-k plaquette of Ω_{k+1} deviates under U_{k+1} by at most 2B₃ε_{k+1}L^{−2}, a corollary only.
  - {#MD2.0.5.4} (3)(a) matches δ*^{(1)} with IT-1 note §3a(6) at k = 1.
    {#MD2.0.5.4-1} Matching the neighbourhoods of n with those of n′ is in D2.4.

- {#MD2.0.5.5} **(a) Perimeter scalar parts.** Size of order τ_k² per step-k bond (V4 Remark main-regime (1): |κ^σ_v| ≤ Cτ² (the sentence following eq:marginal-full-perimeter, by eq:marginal-cluster-tail, with eq:marginal-square-mass) gives |δm^σ|P(C_n) = n|Σ_vκ^σ_v| ≤ 4Cnτ²).
  {#MD2.0.5.5-2} Count P_k.
  {#MD2.0.5.5-3} P_kτ_k² → ∞: for k < K, CRE (2.6) (#MD2.0.5.2-2) gives g_k² ≥ g_K²/((1+β₀)²(K−k)) and CRE (2.7) (p = 6p₀) gives (log g_k⁻²)^{6p₀} ≥ (1+β₀)^{−1}(log g_K⁻²)^{6p₀}, so P_kτ_k² ≥ cℓ_CL^{K−k}(K−k)^{−1}g_K²(log g_K⁻²)^{6p₀}/(1+β₀)³.
  {#MD2.0.5.5-4} The flat-reference, period-invariant (Π_{k+1}-periodic) part is **absorbed exactly** into δm_{k+1}, with zero remainder (D2.3).
  {#MD2.0.5.5-5} Background-dependent scalar parts of deviation size stay as scalar insertions, since 𝓔_{k+1} holds numbers only (D(k+1)(v)), and history-dependent parts near large-field regions go to (f).
- {#MD2.0.5.6} **(b) Corner parts.** Four per step.
  {#MD2.0.5.6-4} D2.3 absorbs them exactly into z_{k+1} at every step (D2.3(6)–(7)); at a commensurate step the remainder is at most C_E𝔞_{k+1}(s_k+1)e^{−c_Es_k} + 12C̄_Z𝔞_{k+1}s_ke^{−c^Zι_{T,k+1}}, s_k = ℓ_CL^{K−k}, 𝔞_{k+1} = max(τ_k², ρ_{k+1}·pl) (D2.3(6)(a)), which decays in the contour size at that step.
  {#MD2.0.5.6-5} For the admissible sides of D2.3(4) every step is commensurate; without that restriction the at most a* other steps leave O(τ_k²(Π_{k+1}+1+s_k)).
  {#MD2.0.5.6-6} For the admissible sides the remainders of all steps sum to at most C_Σ𝔞̄ uniformly in K and ℓ_C, with g_k ≤ (1+β₀)g_K only (#MD2.0.5.2-2; #MD2.3.7.8), given (S-w) with constants independent of k (D2.4(12)(f), with its inputs (13)(d); (T′), (Z), and the Kotecký–Preiss condition follow from it).
- {#MD2.0.5.7} **(c) Deviation parts of the old insertions.** They are carried, never summed in absolute value.
  - {#MD2.0.5.8} Each new traversal n′ (a step-(k+1) bond of C) contains L old traversals.
  - {#MD2.0.5.9} Split an old insertion as Y(U_k) = Y(U_{k+1}) + [Y(U_k) − Y(U_{k+1})].
  - {#MD2.0.5.10} The first part is bounded by C_χρ_kδ*^{(k)}_n(U_{k+1}) ≤ C_χρ_k[L^{−2}δ*^{(k+1)}_{n′}(U_{k+1}) + B_n]: the first term after (γ)'s matching, and B_n the Ω_k∖Ω_{k+1} part of (3)(c), which joins the scale-(k+1) attached part (species att(k+1, ·), (3)).
    {#MD2.0.5.10-1} The equality of the convention above holds only for the same plaquettes and radii; here the plaquette set changes from Ω_k to Ω_{k+1}, and the traversal and radii from n to n′.
  - {#MD2.0.5.11} So, for the first term, the L old traversals of n′ contribute at most L^{−1}(ρ_k/ρ_{k+1})·C_χρ_{k+1}δ*_{n′}^{(k+1)}(U_{k+1}).
    {#MD2.0.5.11-1} Here ρ_k/ρ_{k+1} ≤ (1+β₀)⁶, with ρ_k := C_ρg_k²(1+r_k)⁴: g_k ≤ (1+β₀)g_{k+1} (CRE (2.6)) and (log g_k⁻²)^p ≤ (1+β₀)(log g_{k+1}⁻²)^p (the second inequality of CRE (2.7), with m = k, n = k+1).
  - {#MD2.0.5.12} With the feedback of (d) the constants obey C_χ^{(k+1)} ≤ C_new + (L^{−1} + C_dL²(1+β₀)²g_K²)(1+β₀)⁶C_χ^{(k)} + C_d′ρ_k(C_χ^{(k)})², which is bounded uniformly in k for L ≥ 2, β₀ small and g_K ≤ g(L).
    {#MD2.0.5.12-1} The factor (1+β₀)²g_K² and the quadratic term use g_k ≤ (1+β₀)g_K, the last inequality of CRE (2.6) at n − m = K − k, uniformly in K − k (#MD2.0.5.2-2).
  - {#MD2.0.5.13} *The ratio of the ρ̃ (D2.4(6)).* With D2.4(5)'s ρ̃_k the ratio is ρ̃_k/ρ̃_{k+1} ≤ (1+β₀)⁸, since α_{i,k+1} ≤ (1+β₀)²α_{i,k} by CRE (2.6)–(2.7) at n − m = 1.
    {#MD2.0.5.13-1} So the factor (1+β₀)⁶ above becomes (1+β₀)⁸, and "β₀ small" means (1+β₀)⁸ < L. CRE p.255 allows β₀ that small for small g.
    {#MD2.0.5.13-2} C_new = C_gC_S·pl/c₀ comes from D2.4(4), which rests on (LPG′) and (S-w) (SW closure §5–§6; for the carried insertions at complex data, #MOMGD.5).
  - {#MD2.0.5.14} *From D2.4(4):* the deviation part of an old insertion is bounded by the deviation of its argument, as D1(ii)'s first term states at step 1.
    {#MD2.0.5.14-1} Then the contraction L^{−1} per step follows from this count.
    {#MD2.0.5.14-2} The count also uses:
    - {#MD2.0.5.15} (α) the evaluation point: by RG I (2.3), p.265, V^{(k)} = M^k(U_{k+1}).
      {#MD2.0.5.15-1} By the unique minimal orbit (CRE p.256 l.44–51) and the gauge condition, U_k(M^k(U_{k+1})) = U_{k+1}, i.e. U_k′(1) = 1 in "U_k(V′V^{(k)}) = U_k′(V′)U_{k+1}" (RG I p.265);
    - {#MD2.0.5.16} (β) V^{(k)} in the support of the step-k indicators.
      {#MD2.0.5.16-1} CRE (2.17) tests U_{k,□}(V_k) on the cubes □ ⊂ Ω_k, and p.268 bounds U_{k+1} only on Ω_{k+1}.
      {#MD2.0.5.16-2} So the plaquette test at V_k = V^{(k)} needs the comparison of U_{k,□}(V^{(k)}) with U_{k+1} on □^∼.
      {#MD2.0.5.16-3} *From Bałaban's own steps.* Let □ ⊂ Ω_{k+1}^∼ with □ ⊂ □′ ⊂ R_{k+1}^c, □′ a cube of (3.16) (this holds on Λ_{k+1}^∼, CRE (3.20), p.269).
      {#MD2.0.5.16-4} By (3.19), p.268, |V^{(k)}(b)(V^{(k)}_{□′}(b))^{−1} − 1| < δ_k for b ∈ (□′^{∼2})^{(k)*}, so V_k = V^{(k)} passes (3.3)'s test (threshold 2δ_k).
      {#MD2.0.5.16-5} The argument of 𝐇_{k,□} in (3.6) is then bounded by 2δ_k ≤ 4δ_k off the boundary layer, since |(1/i)log x| ≤ 2|x − 1| for |x − 1| ≤ 1/2, as p.266 requires, and U_{k+1,□′} passes (3.2)'s test since □′ ⊂ P_{k+1}^c.
      {#MD2.0.5.16-6} So (3.7) and (3.8) hold at V_k = V^{(k)} as printed, and χ_k(□) = 1 there (p.266: "Thus χ_k(□) = 1 for □ ⊂ Ω_{k+1}^∼").
      {#MD2.0.5.16-7} (3.8) uses the test of (3.2) at threshold ε_{k+1}(L^{−1}η)², not p.268's regularity at 2B₃ε_{k+1}(L^{−1}η)², and needs only 2(1+β₀)L^{−2} + 4/10 < 1.
      {#MD2.0.5.16-8} *The cubes with □′ ⊂ R_{k+1} (p.268 and CMP98 pp.33, 42).* p.268 derives (3.19) from (3.17), the regularity of U_{k+1} on Ω_{k+1} (which bounds 𝐇_{k+1,□′} on □′^{∼2}), (3.18), and CMP98 (106)–(108), (159)–(163).
      {#MD2.0.5.16-9} (106)–(108) are identities for the gauge transformation u of CMP98 (p.33 does not name the gauge), and (159)–(163) bound Ū^k(Ū_0^k)^{−1} for U = U′U_0 from |(1/i)log \bar{\bar U}′^j| < 2α₁L^jη (the doubly barred Ū′ as printed in (161)) (CMP98 (161), from its Proposition 4); here U′ is the factor exp iL^{−1}η𝐇_{k+1,□′} of (3.17).
      {#MD2.0.5.16-10} (3.19) bounds V^{(k)}, a function not of the fluctuation A_k (p.268: "the characteristic functions χ_k′ depend now on the field V^{(k)}, hence on the new field variables V_{k+1}"), and no step of this derivation uses (3.16)'s test, which bears on the fluctuation A_k.
      {#MD2.0.5.16-11} So (3.19) holds for every cube □′ of (3.16), and the cubes □ ⊂ □′ ⊂ R_{k+1} are covered by the argument above.
      {#MD2.0.5.16-12} D2.6's carrier item: the cubes □ ⊂ Ω_{k+1}^∼ in the band Ω_{k+1}^∼∖Ω_{k+1}^{∼−1}, which lie in no cube □′ of (3.16), since (3.16) partitions only Ω_{k+1}^{∼−1} (p.268), and the cubes □ ⊂ Ω_k∖Ω_{k+1}^∼ whose localisation domain □^{∼4} (CRE (2.16)) meets Ω_{k+1}, which see V^{(k)} there too.
      {#MD2.0.5.16-13} Pages: (3.2), (3.3), P_{k+1} and δ_k on p.265 (printed "δ_k = g_kA_1/A_0p_0(g_k)"; (3.19) uses ε_k = (A₀/A₁)δ_k); (3.16)–(3.19) on p.268; (3.20) on p.269; B₃ in VAR Thm 1, p.279.
      {#MD2.0.5.16-14} The cubes of Ω_k∖Ω_{k+1}^∼ are WILSON_IT1_D26_CLOSURE_2026_10_24.md §8.2, for M ≥ 4LM₂ (□^{∼4} has width ≤ 4LM₂R_k ≤ 4L²M₂R_{k+1} ≤ LMR_{k+1}, R_k ≤ LR_{k+1} by Cauchy #CP.14-1, p.245's "M much larger than M₂"; with the closure's §8.1 gluing).
      {#MD2.0.5.16-15} The band cubes Ω_{k+1}^∼∖Ω_{k+1}^{∼−1} need a localisation identity for the mixed-constraint minimiser, since (3.17) with 𝔹_{k+1}(□′^{∼4}) is not an identity for U_{k+1} where □′^{∼4} meets Γ_k (scale-k constraints there).
      {#MD2.0.5.16-16} The identity is printed neither in CMP98 Sect. C (single domain) nor in CRE pp.266–269.
      {#MD2.0.5.16-17} CRE p.257 prints mixed-set localisation in a single-layer case (with a 2M₁ distance condition that fails where ∂□′^{∼4} crosses ∂Ω_{k+1}) and a several-layer sentence without conditions, and p.269 uses it on Λ_{k+1}ᶜ ∩ Λ_k, which is not a crossing instance.
      {#MD2.0.5.16-18} The identity for crossing domains is the D2.6 closure's §8.3 (1)–(2) (𝔹_mix is the intersection of two admissible nested sequences, VAR p.277 (1); gluing with D2.6 closure §8.1's gluing and VAR Theorem 1's uniqueness give (3.17) for it).
      {#MD2.0.5.16-19} The band cubes with □′^{∼4} ⊂ Ω_{k+1} follow from closure §8.3 (with the closure's §8.1 gluing, [15], [12], and [14] (1.65)'s reasoning); the others (□′^{∼4} ⊄ Ω_{k+1}) follow by route (a), with (3.7)'s requirement |𝐇_{k,□}| < (1/10)ε_k met by the bound B₃C_9δ_k + O(1)e^{−R_k}ε_k + (1/40)ε_k, C_9 = 4 + 4c₁₂B₃, for A₁/A₀ < 1/(20B₃C_9) and γ small; all sets on the one fine lattice of U_{k+1}; this uses CRE p.267's ζ resummation, D2.6 closure §8.3's layer bound, and LFR I p.177 (ii) (#MD2.0.4.6-1).
    - {#MD2.0.5.17} (γ) the step-k neighbourhoods of the L old traversals lie in the step-(k+1) neighbourhood of n′ (D2.4, with the radii of (3));
    - {#MD2.0.5.18} (δ) ρ_k := C_ρg_k²(1+r_k)⁴ with r_k := A₁(log g_k⁻²)^{p₀}, as fixed in (3);
    - {#MD2.0.5.19} (ε) the attached parts of the old insertions at U_{k+1}.
      {#MD2.0.5.19-1} Kept in D(k+1)(ii), the L old traversals of n′ would add them, a factor L per step (n′ parallel to the data), which is not controlled.
      {#MD2.0.5.19-2} So they leave (ii) at the end of step k+1's map and keep their species att(k, ·), bounded by (ii′) with j = k and paid per component in (f) (as att(k+1, Z) they would sit in D(k+1)(ii), the factor-L situation excluded here; they cannot be scalar local activities); D2.6.
      {#MD2.0.5.19-3} The wrap term stays: it grows by at most L per step and is bounded by CL^{K−j}ρ̂_je^{−c_att N^{(j)}_min/M} at step K. With N^{(j)}_min ≍ T_phL^{K−j} ((g)) and x := L^{K−j} ≥ 1 this is Cρ̂_jxe^{−c′T_phx/M}, and xe^{−ax} ≤ e^{−a} for x ≥ 1 once a ≥ 1; so each term is at most Cρ̂_je^{−c′T_ph/M}.
      {#MD2.0.5.19-4} That alone gives K terms of this size, which is not uniform in K. With a := c′T_ph/M ≥ 1 and L ≥ 2, L^ie^{−aL^i} = e^{−a}L^ie^{−a(L^i−1)} ≤ e^{−a}L^ie^{−(L^i−1)}, and Σ_{j≤K}L^{K−j}e^{−aL^{K−j}} ≤ e^{−a}Σ_{i≥0}L^ie^{−(L^i−1)} ≤ 2e^{−a}: the terms are 1, ≤ 0.74, ≤ 0.20, ≤ 0.01, …, their values at L = 2, since xe^{−(x−1)} decreases for x ≥ 1.
      {#MD2.0.5.19-5} So the sum over j is at most 2C(sup_jρ̂_j)e^{−c′T_ph/M}, small under the condition T_ph ≥ C·M of (g).
    - {#MD2.0.5.20} (ζ) the plaquettes of Ω_k∖Ω_{k+1}, where the maximum of δ*^{(k)} is not matched by δ*^{(k+1)}: the split of (3)(c) (D2.4).
- {#MD2.0.5.21} **(d) Fluctuation parts of the old insertions** (D2.1–D2.5).
  {#MD2.0.5.21-2} Y(U_k) − Y(U_{k+1}) is of order ρ_kg_k, with zero mean at first order in the step-(k+1) fluctuation.
  - {#MD2.0.5.22} Its second-order mean is O(ρ_kg_k²), and it is perimeter-proportional (P_kρ_kg_k² → ∞).
    {#MD2.0.5.22-1} At flat U_{k+1} the mean is scalar, by invariance under constant gauge transformations and Schur's lemma; that part goes to (a).
    {#MD2.0.5.22-2} The rest is O(ρ_kg_k²·curvature) and stays in the class, as for the pair contractions below.
  - {#MD2.0.5.23} Its pair contractions are of order ρ_k²g_k² per pair with another old insertion, and ρ_kg_k² per pair with the fluctuation of the leading word, which is O(g_k) per step-k bond.
    {#MD2.0.5.23-1} They decay over one new block, since the step-(k+1) covariance decays at the scale-(k+1) block scale (the analogue of μ_H = γ_L/(8Lm_L) in fine units; IT-1 note (D0)).
    {#MD2.0.5.23-2} So there are O(L²) pairs per new traversal, with a constant that depends on L through the decay rate μ_H.
  - {#MD2.0.5.24} Gauge covariance makes the leading part of each pair contraction scalar.
    {#MD2.0.5.24-1} Convention: t_a is an orthonormal basis of 𝔤 for the invariant metric, T^a := π_*(t_a), C₂(π) := Σ_aT^aT^a (positive for 𝔤 realised by Hermitian matrices, U = exp iA as in CRE), Ad(X)t_b = Σ_aAd(X)^{ab}t_a, and X is the transport between the two insertion points in the orientation of the word.
    {#MD2.0.5.24-2} If the covariance of the fluctuations at n and n″ is c(n,n″)·Ad(X_{n→n″}), then XT^bX^{−1} = Σ_cAd(X)^{cb}T^c gives Σ_{a,b}T^aXT^bAd(X)^{ab} = Σ_{a,c}T^aT^cX(Ad(X)Ad(X)ᵀ)^{ac} = (Σ_aT^aT^a)X = C₂(π)X, since Ad(X) is orthogonal and Σ_aT^aT^a is scalar by Schur.
    {#MD2.0.5.24-3} For covariant families M^a, N^a (π(g)M^aπ(g)^{−1} = Σ_cAd(g)^{ca}M^c and likewise for N^a, for all g ∈ G), the same computation gives Σ_{a,b}M^aXN^bAd(X)^{ab} = (Σ_aM^aN^a)X, and Σ_aM^aN^a commutes with π(G), hence is scalar; this covers the pairs of old insertions.
    {#MD2.0.5.24-4} The scalar part goes to (a).
    {#MD2.0.5.24-5} The non-scalar part is the deviation of the covariance from the transported form, which is of the order of the background curvature between n and n″.
  - {#MD2.0.5.25} Within one new block the curvature between n and n″ is summed over at most L² step-k plaquettes, so it is O(L²δ*^{(k)}) = O(δ*^{(k+1)}).
    {#MD2.0.5.25-1} So the non-scalar remainder per new traversal is O(L²ρ_kg_k²δ*^{(k+1)}).
    {#MD2.0.5.25-2} Against the class bound ρ_{k+1}δ*^{(k+1)} this is the factor L²g_k²ρ_k/ρ_{k+1} ≤ (1+β₀)⁸L²g_K², small for g_K ≤ g(L) (g_k ≤ (1+β₀)g_K, CRE (2.6)).
    {#MD2.0.5.25-3} With D2.4(5)'s ρ̃ the old dev bound is ρ̃_kδ*, and against ρ̃_{k+1}δ*^{(k+1)} the factor is L²g_k²ρ̃_k/ρ̃_{k+1} ≤ (1+β₀)^{10}L²g_K², which is D2.4(6)'s C_dL²(1+β₀)²g_K²·(1+β₀)⁸.
- {#MD2.0.5.26} **(e) Fresh insertions.** These come from integrating the step-(k+1) fluctuations of the leading word f_k.
  {#MD2.0.5.26-1} They are of order C_newρ_{k+1}δ*^{(k+1)} per new traversal: IT-1 note §3a(6)'s deviation form at step k+1, with D2.1's form of f_k (D2.1–D2.2).
- {#MD2.0.5.27} **(f) Large-field attached parts and exposed segments.**
  - {#MD2.0.5.28} Count: P_k·p_k, with p_k the probability that a step-k bond lies near a large-field region. p_k ≤ e^{−c(log g_k⁻²)^{2p₀}}.
    {#MD2.0.5.28-1} The bound P_kp_k = 4ℓ_CL^{K−k}e^{−c(log g_k⁻²)^{2p₀}} diverges as K − k → ∞, since (log(K−k))^{2p₀} = o(K−k), so these terms are carried as local activities attached to the large-field regions, as V4's E_bdry (Theorem 1, eq:thm-main-bounds) is (iteration audit §4(5)).
  - {#MD2.0.5.29} *Payment, per component and over its lifetime.* LFR II p.381 gives the fundamental factor exp(−½γ₀A₁²p₀²(g_j)(d_j′(Z_j^{(i)})+1) − 2p₀(g_j)) for each large-field region Z_j^{(i)} *created at step j* (IT-1 note RC payment's (d″)(ii) gives the step-1 form, with ½c₄ϑ²A₁²p₀²(g₁)).
    {#MD2.0.5.29-1} By p.384 the factor of a component Z of Z_j is exp(−κ_j(Z) − 2p₀(g_{j(Z)})), and it "controls K renormalization steps" through (1.80).
    {#MD2.0.5.29-2} The attached and exposed costs near Z recur at every one of these steps, so the payment must cover all of them.
  - {#MD2.0.5.30} *Per-step cost.* The contour has at most c_C·MR_n scale-n bonds per MR_n-cube, c_C depending only on the shape of C (c_C = 4 for a rectangle: each straight side meets a cube of side MR_n in at most MR_n bonds).
    {#MD2.0.5.30-1} The exposed segments cost Cτ̂_n² per traversal, τ̂_n² := max(τ_n², Cρ̂_n) with ρ̂_n D(n)(ii)'s attached amplitude (#MD2.0.3.29), so at step n they cost at most e^{Cc_CMR_nτ̂_n²} per MR_n-cube of the current region, S^{n−j}(Z) if no large fields are created near Z, with the collar factor 13^d inside C (D2.6 closure 7.4(a)).
    {#MD2.0.5.30-2} At n = 1 the per-cube cost is IT-1 note §3i(7)'s rooted form 205^d(ℓ/ℓ₀^{box}+2)⁴C_rτ₁² per ℓ-cube, ℓ = LMR₁ (closure 7.4(a)).
  - {#MD2.0.5.31} *Lifetime sum.* D_j(Z) := Σ_{n=j}^{j+K_Z}Cc_CMR_nτ̂_n²·#cubes_n(S^{n−j}(Z)), with K_Z the lifetime of Z (p.384's "K renormalization steps") and the summand at n = 1 in the form of #MD2.0.5.30-2.
    {#MD2.0.5.31-1} Bałaban's chain on p.384–385 bounds exactly this volume count: #cubes_n(S^{n−j}(Z)) = (MR_n)^{−d}|S^{n−j}(Z)| ≤ 63^d(MR_n)^{−d}|Z^{(n−j)}| ≤ 3(126)^d2^{−(n−j)}d_j′(Z) for n ≤ n₀, and S^{n−j}(Z) lies in a cube of size 64MR_n, so #cubes_n ≤ 64^d, for the at most R_j steps after n₀ (K_Z ≤ n₀ − j + R_j, p.385).
    {#MD2.0.5.31-2} With R_n ≤ LR_j (CRE (2.9)), τ̂_n² ≤ τ̂̄² := sup_{j≤n≤K}τ̂_n² ≤ Cg_K²(log g_K⁻²)^{6p₀} (τ = C[g(1+r)³ + e^{−cr²}] is increasing in g for small g, ρ̂_n is of order g_n²(log g_n^{−2})^{4p₀} (#MD2.0.5.35), and g_n ≤ (1+β₀)g_K by CRE (2.6)), and the step n = j itself (#cubes_j(Z) ≤ 3·2^{d−1}d_j′(Z) for d_j′(Z) > 0 by p.384's inequality at n = j, and ≤ 2^d otherwise), this is (1.81) with O(1)M^dR_n^{d+1} replaced by Cc_CMR_nτ̂_n², and d_n′(S^{n−j}(Z)) by #cubes_n, bounded by the same middle member:
    {#MD2.0.5.32} D_j(Z) ≤ C_dc_CMLR_j²τ̂̄²(d_j′(Z)+1), C_d := C(3(126)^d + 64^d + 3·2^{d−1}), plus, at j = 1, C_{εA}M^dL^{d+1}R₁^{d+2}τ̂̄²(d₁′(Z)+1) for the summand of #MD2.0.5.30-2 ((ℓ/ℓ₀^{box}+2)⁴ ≤ C(LMR₁)⁴ at d = 4; closure 7.2).
  - {#MD2.0.5.33} *The attached species.* D_j(Z) covers only the per-segment costs.
    {#MD2.0.5.33-1} The species att(j, Z), att(j, coll) (per component through B_j(Z)) and lw(Z) are carried without growth (D(k)(ii′): the carry does not increase the left sides; by the regrouping, while their stability under the evaluation at U_{k+1}, under the fluctuation parts and under the multi-parent insertions is the D2.6 item of D(k)(ii′)), so they are paid once, not at every step of Z's lifetime.
    {#MD2.0.5.33-2} Their totals, at the scales of D(k)(ii′), are
    {#MD2.0.5.34} A_j(Z) := Cρ̂_jN_j(Z) + Cρ_{t,j}[Σ_{Δ→Z}𝔪̂^{(j)}_ΔN_j(Δ) + [j = 1]C′_χg_jΣ_{b→Z}h(m^{(j)}_b)N_j(b)] + [j = 1]Σ_{i→Z}‖π(T̂_iT_i^{−1}) − 1‖ (the inputs term at j = 1 only: for j ≥ 2 the ω′-dependence is bounded pointwise without translation, D2.6 closure §2.2 with D2.6 closure §2.2's source bound, §7.1; every N_j(·) at the one rate c_att := min(c^{(1)}, c_*′) of closure 7.1, c_*′ = min(η_V/C_F, ν_e/8, κ/4) of closure §2.2 (ν_e/8, so that the att(j, Z) production at ν_e/8 is dominated);
    {#MD2.0.5.34-1} the lw term, unweighted here, is closure 7.1's weighted total [j = 1](2C_{lw}g₀(r+1) + C_{lw}^{III})M_VR₁(d₁′(Z)+1), with §6.5's label factor and class (III), and h(m^{(j)}_b) is h(m̂_b) at the complex sup of closure 6.3),
    {#MD2.0.5.35} with ρ̂_j of order g_j²(log g_j^{−2})^{4p₀} and ρ_{t,j} of order g_j(log g_j^{−2})^{p₀}.
    {#MD2.0.5.35-1} The cost to be paid by Z's fundamental factor is the lifetime total E_j(Z) of closure 7.2 (table #T12.19-9): the carried mass 2A_j(Z) (the carry's factor 2, closure §5, §6.4), the species att(n, Z_n) made at the later steps n of the lifetime, each of mass ≤ 2C̄_A(d_n′(Z_n)+1) (closure 7.1–7.2), and D_j(Z); closure 7.2 gives E_j(Z) ≤ ε_A(d_j′(Z)+1).
    {#MD2.0.5.35-2} The bound of A_j(Z) by a multiple of d_j′(Z) + 1 (counting the step-j traversals within distance O(M) of Z, the marks and the inputs assigned to Z) and the size of the lw term are D2.6 closure §7.1 and §6.3.
  - {#MD2.0.5.36} *The condition at j = 1 (closure 7.2 *Ledger at j = 1*).* Put K₁ := ¼c₄d^{−1}(434)^{−d}ϑ_V²A₁²(log g₁⁻²)^{2p₀} (ϑ_V of table #T12.19-4-1) and B₁ := O(1)(64)^dM^dL^{d+1}R₁^{d+2}. The cost is paid per label polymer X (a ∗-component of Λᶜ) if K₁ ≥ 8B₁ and ε_A(1) ≤ K₁/8: then κ₁(X) ≥ (K₁ − B₁)(d₁′(X)+1) covers the future sums B₁(d₁′(X)+1), the lifetime cost ε_A(1)(d₁′(X)+1), a reserve and a carried part.
    {#MD2.0.5.36-1} K₁ ≥ 8B₁ is p.385's j = 1 condition with ¼γ₀(14)^{−d} replaced by ¼c₄d^{−1}(434)^{−d}ϑ_V² (closure 7.2 *The fundamental factor at j = 1*) and 2(64)^d by 8(64)^d; ε_A(1) is a polylog of fixed degree (closure 7.2 *Sizes of ε_A*), so both hold for p₀ large and g small, as on p.385.
    {#MD2.0.5.36-2} The small domains of p.386 are paid in closure §7.3: their costs ε_A(100^d+1) + 2R_{j+1}C̄_A^{(j+1)}(100^d+1) are at most ¼p₀(g_j).
    {#MD2.0.5.36-3} The comparison at general j, with (1.85)'s "γ₀A₁²p₀²(g_{j+1})(d′+1)", is D2.6 closure §7.3.
  - {#MD2.0.5.38} *Bałaban's induction.* Bałaban's induction pp.384–389 runs with the summand of (1.80) enlarged by the per-step costs of E_j(Z) (closure 7.2 *The enlarged induction*).
    {#MD2.0.5.38-1} In the merging step (1.86) the exposed-segment summand is subadditive (#cubes_n(Z) ≤ #cubes_n(X) + #cubes_n(Y) for Z ⊂ X ∪ Y), and the species' d′+1 is subadditive up to p.386's slack 2d, whose extra cost 4dC̄_A^{(j+1)} the merging surplus pays (closure 7.2).
    {#MD2.0.5.38-2} The future sums of Z against those of X and Y are on p.387.
    {#MD2.0.5.38-3} This is WILSON_IT1_D26_CLOSURE_2026_10_24.md §7.1 (A_j(Z) ≤ C_A(d_j′(Z)+1)), §7.2 (the lifetime total ε_A(d_j′(Z)+1), the induction with (1.82)'s constant 8(64)^d at j = 1 and (1.88)'s constant doubled, future sums unchanged), §7.3 (the condition at general j with (1.85)), and §7.4 (exposed segments, per-cube comparisons, label weight).
  - {#MD2.0.5.39} *Localisation.* §3i(7) gives ∗-connected sets X meeting K_j and Dᶜ, which may meet several components.
    {#MD2.0.5.39-1} So the payment is per polymer, a union of components linked by such sets, with the weight e^{κ#boxes(X)}; the per-cube comparison of §3i(7) (*Against (0)*) is D2.6 closure §7.4.
- {#MD2.0.5.40} **(g) Torus and corner–corner parts of E°.** At step k these are Cτ_k²(n_k e^{−cι_{T,k}} + (n_k+1)e^{−cn_k}) (the torus part with the amplitude 𝔞_{k+1} = max(τ_k², ρ_{k+1}·pl) of D2.3(4)(Z-f), which changes nothing below) with n_k ≍ ℓ_CL^{K−k} and the step-k quantity ι_{T,k} := max(0, N_min^{(k)}/4 − ρ_dep L^{−k}), with ρ_dep the step-1 dependence halo in fine bonds (D2.3(4)(Z-g), #MD2.3.4.53), so that ι_{T,k} = Lι_{T,k+1} exactly (N_min^{(k)} = LN_min^{(k+1)}).
  {#MD2.0.5.40-1} Any other fixed subtraction R changes e^{−cι_{T,k}} by at most e^{c(R + ρ_dep)}, a constant at c = 1/(32M) for R = O(LM), since ρ_dep < M(1/2 + C_boxL).
  {#MD2.0.5.40-2} With a torus of physical side T_ph ≫ ℓ_C, N_min^{(k)} ≍ T_phL^{K−k}, and the terms are dominated by the last O(1) steps and **summable** (iteration audit §4(3)).
  {#MD2.0.5.40-4} The wrap terms of (c)(ε) need in addition T_ph ≥ C·M, with M the decay length of D(k)(ii).
  {#MD2.0.5.40-5} Both are lower bounds on the periods, which may be taken as large as needed.
  {#MD2.0.5.40-6} *Wrap amplitudes (D2.6 closure 2.1 *Precedence and units*).* A wrap(k+1) group failing (i) or (iii) has amplitude C_S″b_k, so D(k)(ii)'s wrap display carries max(C_S′ρ̂_j, C_S″b_j) at each j; the sum over j is ≤ 2max(C_S′, C_S″)sup_jmax(ρ̂_j, b_j) times the same torus factor, and the condition holds with b_j in place of ρ̂_j (b_j → 0 with g_j).
- {#MD2.0.5.41} **(h) The norm of the dressed loop.** |𝒲_k| ≤ |κ^{(k)}|e^{|𝓔_k|}∏_n(1+ν_n) is at most |κ^{(k)}|exp(CP_k(ρ_kε_k + τ_k²) + r^R_K), where r^R_K (table #T12.30-4) bounds the sum of the 𝐑-steps' constants E°^R_j in 𝓔_k (#MD2.3.5.5-2) over any set of steps; this bound is exponentially large in L^{K−k}.
  {#MD2.0.5.41-1} D(k) never uses it, and the step map may use only local bounds: Cauchy estimates on polydiscs in bounded sets of variables (IT-1 note §3e(6)(a)) and cluster expansions with local activities.
  {#MD2.0.5.41-2} At k = K, P_K = 4ℓ_C, so |𝒲_K| ≤ |κ^{(K)}|exp(4Cℓ_C(ρ_Kε_K + τ_K²) + r^R_K).

### (6) The Bałaban Inputs and Their Sources {#MSD2.0.6}

- {#MOMGD.17} The inputs, with their pages, the surrounding pages, and the cited papers, are READINGS_RECHECK_2026_10_23.md #RR.1–#RR.39.
  - {#MOMGD.18} *Printed:* VAR Prop. 9's extension, RG1 (1.8), (3.12) for the current, PBG p.394's locality, CMP98 p.31's M^k (CMP98 p.24, p.31; RG1 (0.21)), (2.7) at p = p₀ (CRE p.244 l.23, p.256 l.3), the nesting Ω_K ⊆ Ω_j (CRE (2.1), p.254), CRE (2.6)–(2.7) (CRE p.255; at simple G, (2.6) with b′ + C in place of β′ is #MD2.0.5.2-2;
    {#MOMGD.18-1} (2.7) follows from (2.6) once log g_n^{−2} ≥ p/β₀), REG p.81 (it names CMP98 (87), (99), (97), (105)), RG2 p.5's all-norms bound (PBG (3.42)), CRE (3.6), RG1 p.268's covariance (and RG2 p.13), H_{1,1}'s walk expansion (PBG p.427: "We have the same situation for the operators H₁"), the (k)* convention (CRE p.247 "More generally, for a set X"), the k-independent O(1) (Bałaban's "absolute constant O(1)", RG1 pp.255, 279; RG2 p.8).
  - {#MOMGD.19} *Consequences of the print:* (2.7) at p = r (r ≥ 2 is not stated to be an integer, CRE p.245; raise (2.7) at p = ⌈r⌉ to the power r/⌈r⌉ ≤ 1), RG1 (3.13)'s 𝐅₁ (RG1 p.272's identity with RD*𝐇_j = 0), CRE p.267's (g_k, δ_k) (index shift: A_k′ = g_kA_k, p.267; threshold δ_k, (3.16)), ε_D̃ independent of g₁ (RG1 p.267: D̃'s equation contains no coupling), the absence of an 𝐑-operation for k ≤ N (LFR I p.177 (ii): every component of Λ_k^c contains a region created at a step ≤ k ≤ N), 1_{A_cov} constancy (V4 sec:c5-0: I = Λ₁^*; CRE p.254 labels; D2.2(2)(a)).
  - {#MOMGD.20} *Bałaban's claims:* CRE p.267's ζ resummation, the analyticity in VAR Prop. 9's 𝐇^{(j)}, CRE p.251's 𝐇₀ (VAR Prop. 9 on PBG (3.35)–(3.38); CRE p.261, p.251; their bounds are D2.2(6)(e)'s), CRE p.277's margin (CRE p.277; p.259 leaves q₀, q₁, C₀, C₁ free above lower bounds; p.262; its constant comparison is D2.2(4)(f)'s, under q₀ = q₁ > p₀), CRE p.276's older-layer regularity (CRE p.276: the regularity of U_{k+1} "on a neighborhood of Ω_n∖Ω_{n+1}" is "the same as for U_n-configurations, i.e. they are characterized by the scale L^{−n}";
    {#MOMGD.20-1} p.277: "no regularity improvement" on Ω_{k+1}ᶜ, the powers of 1/2 in the conditions being the room for the step-by-step shifts, which the decay of 𝐇_k keeps "much greater than bounds on this function": so U_{k+1} on an older layer n satisfies the real parts of (2.34), (2.38) at the scale L^{−n} within the index factor; the quantitative form is D2.2(6)(e)'s, *The base point on Ω₁∖Ω₂*, *For k ≥ 2* and *Every older layer*, through the response chain from the root at k = 1 and from p.268's top-layer bounds),
    {#MOMGD.20-2} CRE p.279's same-way clause, (i′) (CRE p.276; p.279: "treated in exactly the same way … we proceed with the cluster expansions"), CRE p.277's 𝐇-decay (CRE p.267 l.42–44, p.277 l.6–8), CRE p.269's action change, p.269's bound on bonds leaving S_{k+1}, p.269's characteristic-function statements.
  - {#MOMGD.21} *Identified by content:* RG2's numbering of [I] (RG1 has only Sects. 0–5; RG2 p.15 prints "(7.14)" for its own (2.14); CRE's (I.6.9), (I.6.10), (I.6.34), (I.6.41), (I.7.1), (I.7.12), (I.7.13) match RG2 (1.9), (1.10), (1.34), (1.41), (2.1), (2.12), (2.13)). "Lemmas 5, 6 [I]" = RG2 Lemmas 1, 2 by content: CRE p.276 calls them the lemmas whose conditions the terms of (I.6.41) satisfy, "with analyticity space (I.6.34)"; RG2 (1.34) is in the statement of Lemma 1 (p.9) and (1.41) in that of Lemma 2 (p.11, analytic "on the space (1.34)"), the only two lemmas of RG2 Sect. 1.
    {#MOMGD.21-1} Only this content is used.
  - {#MOMGD.27} *PBG p.394's locality, VAR Prop. 9's 𝐇^{(j)}, CRE p.251's 𝐇₀.* PBG p.394's locality: only its single-torus part is printed (PBG p.394, Thm 3.10, RG2 pp.3, 14); the cross-torus identity follows from the local definitions, under translation covariance (RTR)'s convention that T′'s partitions and walk-domain families are the lifts of T's.
    {#MOMGD.27-1} VAR Prop. 9's 𝐇^{(j)}, CRE p.251's 𝐇₀: Bałaban's for the analyticity; their complex-space bounds are D2.2(6)(e)'s ( the argument bound at complex 𝐔 by REG Lemma 1 with CMP 98 Prop. 3 at complex data, S_H = C_H(α_{0,j+1} + α_{1,j+1})e^{−R_j}).
  - {#MOMGD.23} *Translation covariance* on ℓ₀ is RTR_PROOF_PASS_2026_10_23.md, definition by definition: printed for the totals (RG1 p.263, Thm 3, p.269), the z-localised terms (CRE (2.29)) and the ℓ₀ terms (CRE (3.39)); from the definitions for the localised activities (no fixed origin, no order of positions).
    {#MOMGD.23-1} Our convention for the choices the prints leave free: ζ̃_□, the walk-domain families, with RG2 p.13's X₀ the largest domain with X̃₀⁵ = Z̃₀, the union of the M₁-cubes Q with Q̃⁵ ⊆ Z̃₀ (RTR #TC.8-3), PBG p.394's locality's lifted partitions, and, for ties in PBG p.411's "closest" cube, the equal-weight average over the tied cubes (exact, same bounds; it keeps the free choices hypercubic symmetric), with the one-variable profiles of RG1 p.270 and PRT1 (1.118) taken even.
    {#MOMGD.23-2} D2 does not use covariance under the hypercubic group: the fluctuation fields 𝐇_k(B′), 𝐇_{k+1}(□₀,·) are written in a gauge generated from REG (1.19)'s axis-ordered axial gauge (RG1 p.265, p.276; REG pp.80–81; RTR_PROOF_PASS, *Hypercubic covariance*).
    {#MOMGD.23-3} So D2 keeps κ_v per orientation and ζ_{v,w} per corner pair, with δm_{k+1} and ζ_{k+1} their averages over C's orientations and corners (D2.3(5)).
    {#MOMGD.23-4} The bounds of D2.3(4)–(6) use only partition-preserving translations.
  - {#MOMGD.24} *RG2 Lemma 3's repair (D2.4(1)).* A repair of its proof, since RG2 (1.28) and (2.30), left inequality, are false at single cubes (RG1 p.257: d_j = 0 for one cube); it holds on every use in RG2 pp.7–21, and Lemma 3 holds as printed with enlarged absolute constants.
- {#MOMGD.22} *The step-1 domain Λ.* CRE pp.277–278 concern Bałaban's own Λ_{k+1}, and RG2 p.1 is programmatic, so the construction at Λ is not Bałaban's printed statement. Its construction part is RC_PROOF_PASS #RC.3–#RC.6, which writes out the step-1 construction at Λ with every cited hypothesis checked at Λ (PBG Thms 3.9, 3.10, 3.14, 3.15; RG2 Sects. 1–2 via the Bałaban project's GLT/GCT, RG2_NOTES.md; a margin of five block layers for the Λ-independence of interior terms, #RC.4–#RC.4-3; the 𝐁 format (2.41)–(2.42) and the count (2.47) at Λ, #RC.4-4–#RC.4-5).
  {#MOMGD.22-1} This includes the Mayer expansion of the shifted cutoffs on the collar 𝒦₃ of #RC.6-1-4 (collar tests #RC.5-9, penalty lemma #RC.5-8, cutoffs confined to P ∪ P″ #RC.6-3-7: V4's young carrier is D(Λ) = Λ* (V4 Section c5-0 and Section c5-2-3), and its collar J_col(Λ) contains every free bond with an endpoint within ρ_L − 1 of Λ, J₁(Λ) ⊂ J_col(Λ) by Lemma c5-1-2; the rounds are LINE_DEFECT's 𝒬⁺, for which Lemma c5-3-1(b) holds;
  {#MOMGD.22-2} by V4 (regular-covariance-hessian) and the paragraph after it the Hessian is CRE's C*Δ₁C, so m_t = t·m with V4's mean shift m, and V4 Remark c5-3-2 with (c5-4-1) gives t|m_b|_σ ≤ r/4 on every bond of D(Λ); no new tested bonds, nothing new to pay;
  {#MOMGD.22-3} the X-local pieces, at real and at complex backgrounds (Ũ^c₁(X), base (U, J_U)), by the local shift m^{loc}_t of #RC.6-1–#RC.6-1-4, the ρ₂-truncated walk sum of m_t with |m_t − m^{loc}_t| ≤ 1/(m_Lr²) (#RC.6-1-3), which keeps the cutoff pieces local in U and leaves the linear factor e^{−⟨A″,w⟩}, |w| ≤ 2/r², Mayer-interpolated as single-cube potentials W(Δ) (#RC.6-3-1–#RC.6-3-2; |W(Δ)| ≤ 4n_Δ/r, since |A″_b| ≤ 2r on the W-host bonds, each W-host paid by Cauchy at radius r^{1/2};
  {#MOMGD.22-4} the empty selection is RG2's 1), with the pointwise bound |m^{loc}_t| ≤ r/2 at the real base (#RC.6-2–#RC.6-2-5) from (c5-4-1)'s constant at Ũ′ = Ũ^{v^{−1}}, Ũ the global extension of the local gauge v on the U-range of each shifted bond (locality alone), the shifted sharp cutoffs confined to P ∪ P″ (#RC.6-3-7; χ = χ⁰ + Δ on the collar bonds of Y₀; the potentials' shift bounded in the fixed-field parts, #RC.5-6–#RC.5-6-3, and by Cauchy's estimate over P°, #RC.6-5-8–#RC.6-5-12-1) and the penalty at r/2 (#RC.6-5-6)); the coupling of the R₁ large field to ΛA vanishes (#RC.5-4).
  {#MOMGD.25-1} The collar step uses V4's collar tests at ϑr, not a bound on K: the printed bound (3.187) gives K = O(1), not K ≤ 1 − η.
  {#MOMGD.25-2} The uses of Λ₁ in CRE pp.243–285, RG1 Sect. 2, RG2 Sect. 2, PBG Sect. E, VAR's setting and LFR I/II are each one of (P1)–(P4), (α), (β), (δ) (RC_PROOF_PASS_2026_10_23.md #RC.1-1–#RC.1-3, checked at #RC.1-4–#RC.2-3).
  {#MOMGD.12} *The payment ((γ) with (β)).* CRE p.255's "If Ω_j∩Λ_jᶜ is nonempty, then S_j is nonempty too" fails for Λ when Ω₁ = T; its role, the payment of Ω₁∩Λᶜ by large-field factors, falls for Λ's new holes on the bad tests.
  {#MOMGD.12-2} The payment, (β)'s per-|Z₁∩Ω₁| cost and (γ)'s new holes, is RC_PAYMENT_PASS_2026_10_24.md: RC payment's (d″)(ii)'s dependencies (a) LFR I's construction after p.187 with Z₁ = Λᶜ and (b) the large-field acceptance are checked against LFR I pp.177–202, LFR II pp.384–389, and CRE pp.264–269; the payment runs through (1.79)–(1.82) with the modified (1.76); components the basic step never acts on use p.387's arbitrary-region (1.79)–(1.80), for j ≥ 2 only.
  {#MOMGD.12-2-1} The pass's Sect. 2 includes the omitted uses and p.197's gauge compensation through V4's Ad-invariant cutoff norms, and Sect. 7 the j = 1 factor lemma for every T-form.
  {#MOMGD.12-4} The observable part (D2.6(f), D(k)(ii′)) and D2.0(5)(d) at K > N are D2.7's (#MD2.0.4.12).

## D2.1 The Leading Word at Step k+1 {#MSD2.1}

{#MD2.1.0.1-1} D2.1 writes the leading word f_k(U_k) through the step-(k+1) background U_{k+1} and the fluctuation variable of CRE (3.15), in the class form: f_{k+1} plus insertions that are local along C, analytic, and small with the fluctuation. Every non-leading part is a local activity, since D2.2 integrates the fluctuation by a cluster expansion, and D2.0(5)(h) excludes any bound on the whole word.

### (1) Quoted {#MSD2.1.1}

{#MD2.1.1.1} *Notation.* RG2's constant κ₁ is written κ_s in this section, to keep it apart from D2.0(3)'s step-1 perimeter coefficient κ₁; the threshold of (4) is ε_H, to keep it apart from CRE's ε₀ = g₀p₀(g₀).
{#MD2.1.1.1-1} RG2's ε₂, ε₃ keep their names; RG2's ε₁ is written ε₁^{RG2} and VAR's ε₁ is written ε₁^{VAR}, to keep both apart from CRE's ε_k = g_kp₀(g_k) at k = 1.
{#MD2.1.1.1-2} CRE's "[I]" is RG I, CMP 109, 249–301 (CRE reference list, p.285).

- {#MD2.1.1.2} *The step-(k+1) variables.*
  - {#MD2.1.1.3} CRE (3.10)–(3.11), p.266: V^{(k)} = M^k(U_{k+1}) on Ω_{k+1}^{(k)}, and V_k′ = V_k(V^{(k)})^{−1} on B(Γ_{k+1}).
  - {#MD2.1.1.4} CRE (3.14), p.267: |V_k′ − 1| < O(1)ε_k on Ω_{k+1}, and A_k′ = (1/i)log V_k′.
  - {#MD2.1.1.5} CRE p.267, after (3.14): "The next steps are exactly the same as in Sect. C [16], and in fact the same as in Sect. 2 [I]. … only the symbols represent different operators, determined by the sequence {Ω_j}."
  - {#MD2.1.1.6} CRE uses the symbol A_k′ twice: first A_k′ = (1/i)log V_k′ ((3.14)), then the scaling A_k′ = g_kA_k (p.267), which defines the integration variable A_k.
    {#MD2.1.1.6-1} Below, A_k is always this scaled variable.
    {#MD2.1.1.6-2} After the scaling, the integrand of (3.15) contains U_k(exp i[g_kCA_k − hD̃(g_kCA_k)]V^{(k)}), and U_{k+1} where A_k = 0.
    {#MD2.1.1.6-3} So the step-k fine field is U_k(e^{iB′}V^{(k)}), with B′ := g_kCA_k − hD̃(g_kCA_k) on B(Γ_{k+1}) (RG2 (1.19), where A_k is called B).
    {#MD2.1.1.6-4} Off B(Γ_{k+1}), V_k is a pending variable and B′ := 0.
  - {#MD2.1.1.7} RG2 (1.20): |B′| ≤ O(1)g_k|A_k| + 4C₂(O(1)g_k|A_k|)² ≤ C₁g_k|A_k| < C₁ε₁^{RG2} for g_k|A_k| < ε₁^{RG2}.
    {#MD2.1.1.7-1} RG2 p.6, after (1.20): 𝐇_k is analytic in A_k for g_k|A_k| < ε₁^{RG2}, so this is a complex domain; C₁ε₁^{RG2} ≤ ε₃^{RG2} (RG2 p.7; C₁ = C₁^{RG2}) puts B′ in the domain of (1.18).
    {#MD2.1.1.7-2} RG1 p.267: D̃ is analytic and "has an expansion beginning with quadratic terms".
  - {#MD2.1.1.8} *The second-order bound.* Fix A_k with g_k|A_k| < ε₁^{RG2} and put f(t) := −hD̃(tg_kCA_k) = B′(tA_k) − tg_kCA_k for |t| < T := ε₁^{RG2}/(g_k|A_k|).
    {#MD2.1.1.8-1} The map t ↦ B′(tA_k) is analytic with B′(0) = 0 and derivative g_kCA_k at t = 0 (D̃ starts with quadratic terms), and |B′(tA_k)| < C₁ε₁^{RG2} by (1.20); Cauchy's estimate at t = 0 gives |g_kCA_k| ≤ C₁ε₁^{RG2}T^{−1} = C₁g_k|A_k|.
    {#MD2.1.1.8-2} So f is analytic with f(0) = f′(0) = 0 and |f(t)| ≤ 2C₁ε₁^{RG2}.
    {#MD2.1.1.8-3} The Schwarz lemma for a double zero gives |f(1)| ≤ 2C₁ε₁^{RG2}T^{−2}, so |B′ − g_kCA_k| ≤ 2C₁(ε₁^{RG2})^{−1}(g_k|A_k|)².
    {#MD2.1.1.8-4} No bound on C beyond (1.20) is used.
- {#MD2.1.1.9} *The composition.*
  - {#MD2.1.1.10} RG1 p.265 (RG1's [15] is VAR, RG1 reference list p.299): (2.3) "V^{(k)} = Ū^k_{k+1} = M^k(U_{k+1})"; "As in Sect. G [15] we write U_k(V′V^{(k)}) = U_k′(V′)U_{k+1}"; after a transformation to the axial gauge and the gauge transformation u_k to the Landau gauge, "U_k′^{u_k^{−1}} = exp iη𝐇_k(B′)".
  - {#MD2.1.1.11} RG1 (2.6), p.266: "Using the gauge invariance of the action … A(U_k(V′V^{(k)})) = A(exp iη𝐇_k(B′)U_{k+1})".
  - {#MD2.1.1.12} VAR p.305, Sect. G: with U₀ = U_k(V₀), "fix the Landau gauge for the configuration U_k(V′V₀)U₀^{−1} = U₁, and we have U₁ = exp iη𝓗(B)".
  - {#MD2.1.1.13} VAR p.307: 𝓗(B) "is an analytic function of 𝔤^c-valued configurations B defined on 𝔅_k and satisfying (172)".
    {#MD2.1.1.13-1} The transformation back to the axial gauge "is an analytic function of 𝓗, hence of B".
    {#MD2.1.1.13-2} (181) extends to G^c-valued gauge transformations.
- {#MD2.1.1.14} *The form of 𝐇_k.*
  - {#MD2.1.1.15} RG2 (1.2)–(1.4), p.2: 𝐇_k(B′) = H₀B′ + 𝐀₀ − HD(H₀B′ + 𝐀₀), with D(A′) = C(A′ − HD(A′)) and 𝐀₀ + G̃(δV/δA′)(H₀B′ + 𝐀₀) = 0.
  - {#MD2.1.1.16} RG2 (1.14), (1.16): |D(H(s),A′)| ≤ 4C₂|A′|² and |𝐀₀| ≤ 4C₄(B₀e^{16κ_s})³|B′|².
    {#MD2.1.1.16-1} So the first-order part of 𝐇_k is H₀B′.
- {#MD2.1.1.17} *The multi-domain form.*
  - {#MD2.1.1.18} CRE (3.6), p.266: U_{k,□} = (exp iη𝐇_{k,□}((1/i)log[M·(Q_k^{s*}V_k)(M·(U_{k+1,□′}))^{−1}])U_{k+1,□′})^{u_{k,□}^{−1}}; CRE (3.17), p.268, the same at step k+1.
    {#MD2.1.1.18-1} The gauge transformation acts on the product e^{iη𝐇}U_{k+1}.
  - {#MD2.1.1.19} CRE (3.7), p.266: |𝐇_{k,□}|, |∇^η_{U_{k+1,□′}}𝐇_{k,□}| < (1/10)ε_k on □^∼, for A₁/A₀ and γ small.
  - {#MD2.1.1.20} CRE p.267, continuing the quote above: "only the symbols represent different operators, determined by the sequence {Ω_j}.
    {#MD2.1.1.20-1} Their properties are essentially the same as before, because of the localization of the field A_k." On the pages read this is the only transfer to the multi-domain operators.
    {#MD2.1.1.20-2} It names RG1 Sect. 2 and Sect. C [16].
    {#MD2.1.1.20-3} RG2 Sect. 1's construction reaches CRE's operators through this sentence together with RG2 p.3, "we can replace the propagators by arbitrary operators having the same regularity properties and satisfying the same bounds", and (1.5).
    {#MD2.1.1.20-4} It is used as Bałaban's statement.
    {#MD2.1.1.20-5} It is used quantitatively in case (A) of (4), for RG2's constants on CRE's operators, which are k-independent, and qualitatively in case (B).
- {#MD2.1.1.21} *Decoupling, RG2 pp.3–6.*
  - {#MD2.1.1.22} (1.6) and p.3: the propagators are random-walk sums.
    {#MD2.1.1.22-1} Each walk term is localised in X̃₀⁵ ∪ ⋯ ∪ X̃_n⁵, and its kernel vanishes within ⅓M₁ of ∂X_j.
  - {#MD2.1.1.23} p.3: the cubes Δ of a partition σ_k carry parameters s(Δ) (the print's σ_k has cubes of side R₁M₁ ≤ M; its example, and (4) below, use cubes of side M).
    {#MD2.1.1.23-1} Each walk term is multiplied by ∏s(Δ) over the cubes meeting its localisation domain; this defines H(s), G̃(s), H₀(s), and "They coincide with the original ones for s = 1".
  - {#MD2.1.1.24} (1.5): D and 𝐀₀ are functionals of the operators.
  - {#MD2.1.1.25} p.4, at s(σ^c) = 0: the kernels "vanish, unless both arguments are in the interior of one component of Y(σ), in fact with distances to the boundary of this component bigger than M₁". 𝐀₀ "is equal to 0 on the neighborhood of Y(σ)^c", and on a component it depends on the propagators and B′ restricted to that component.
  - {#MD2.1.1.26} (1.11): for |s(Δ)| ≤ e^{κ_s} and δ₁M ≥ κ_s, H(s)X is analytic in s and bounded by B₀e^{16κ_s}|X|.
  - {#MD2.1.1.27} (1.17)–(1.18), p.6: 𝐇_k(s(Y₀),B′) is analytic in s(Y₀) and B′, with |𝐇_k(s(Y₀),B′)| ≤ 4B₀e^{16κ_s}|B′| "and the same bound for all admissible norms".
    {#MD2.1.1.27-1} This holds for |B′| < ε₃, with 4C₂B₀e^{16κ_s}ε₂ ≤ 1 (p.5), 4C₄B₀²e^{32κ_s}ε₃ ≤ 1 and 2B₀e^{16κ_s}ε₃ ≤ ε₂ (pp.5–6), uniformly for (𝐔,𝐉) in a complex domain given by I.(i)–(iii) (p.6, after (1.18)).
  - {#MD2.1.1.28} RG2's example decouples only the cubes disjoint from the interior of □̃⁴ (p.3).
    {#MD2.1.1.28-1} Below, all cubes carry parameters.

### (2) The Leading Word as a Function of the Fluctuation {#MSD2.1.2}

- {#MD2.1.2.1} *The gauge transformation (CRE (3.6), p.266, quoted at #MD2.1.1.18).* In RG1's "U_k′^{u_k^{−1}}", the gauge transformations act on U_k(V′V^{(k)}) with U_{k+1} fixed, as in VAR's "fix the Landau gauge for the configuration U_k(V′V₀)U₀^{−1}".
  {#MD2.1.2.1-1} CRE (3.6) and (3.17) print this form for the multi-domain functions: the gauge transformation acts on the product e^{iη𝐇}U_{k+1}.
  {#MD2.1.2.1-2} It is also the form under which RG1 (2.6) "Using the gauge invariance of the action" applies as written: if the transformation acted on the factor U_k′ alone, U_k′U_{k+1} and (U_k′)^{u}U_{k+1} would not be gauge equivalent in general.
  {#MD2.1.2.1-3} So: for real A_k on the support, there is a G-valued lattice gauge transformation u with U_k(e^{iB′}V^{(k)})^u = e^{iη𝐇_k(B′)}U_{k+1} bondwise.
- {#MD2.1.2.2} *The identity.* χ_π∘Hol_C is invariant under lattice gauge transformations, since Hol_C(U^u) = u(x₀)Hol_C(U)u(x₀)^{−1} for the base point x₀ of C. So for real A_k on the support,
  {#MD2.1.2.3} f_k(U_k(e^{iB′}V^{(k)})) = dim(π)^{−1}χ_π(Hol_C(e^{iη𝐇_k(B′)}U_{k+1})).
- {#MD2.1.2.4} *Complex A_k and complex backgrounds* (for D(k+1)(iii)).
  {#MD2.1.2.4-1} Run the identity theorem jointly in (A_k, a′), with 𝐔 = e^{iηa′}U_{k+1} as in (4) and a′ 𝔤^c-valued (CRE (2.39) complexifies the configuration, U′ = exp iξA′, not the variables that define U_{k+1}).
  {#MD2.1.2.4-2} Take a polydisc centred at a real point (real A_k, a′ = 0) that lies inside both the analyticity domain of the left side (VAR (172), VAR p.307 and (181), Prop. 9 [15] for the minimiser, D(k)(iii) for f_k) and RG2's domain I.(i)–(iii) (p.6), on which the right side is analytic by RG2 (1.18).
  {#MD2.1.2.4-3} The two sides agree at the real points of the polydisc, a uniqueness set for functions analytic on a polydisc centred at a real point, so they agree on the polydisc, and by the identity theorem on the connected component of the intersection of the two domains that contains it.
  {#MD2.1.2.4-4} The gauge transformation is not needed here.
- {#MD2.1.2.5} *At A_k = 0.* 𝐇_k(0) = 0 by (1.18), so f_k(U_k(V^{(k)})) = f_{k+1} := dim(π)^{−1}χ_π(Hol_C(U_{k+1})).
  {#MD2.1.2.5-1} This is the leading word of D2.0(3) at step k+1.
  - {#MD2.1.2.6} Where C runs outside Ω_{k+1}, U_{k+1} is a function of the pending variables.
    {#MD2.1.2.6-1} CRE p.266: U_{k+1} "is determined by the sequence of domains {Ω_{k+1},Ω_k,…}, and the corresponding sequence of fields {V_{k+1}|Γ_{k+1},V_k|Γ_k,…}".
    {#MD2.1.2.6-2} These variables enter f_{k+1} as outer variables, as in D(k).
  - {#MD2.1.2.7} The composition formulas on the pages read are RG1's single-domain (2.3)–(2.6) and CRE's cube-local (3.6) and (3.17).
    {#MD2.1.2.7-1} The identity above rests on CRE p.267's transfer of RG1 Sect. 2 to the multi-domain operators in every case, since 𝐇_k is non-local (#MD2.1.1.20).

### (3) The Transported Form and the First-Order Term {#MSD2.1.3}

- {#MD2.1.3.1} *Transport identity.* Let b_1, …, b_P be the fine bonds of C in order from x₀, U a configuration and X a 𝔤^c-valued function of the bonds.
  {#MD2.1.3.1-1} Then
  {#MD2.1.3.2} Hol_C(e^{iX}U) = (∏_{i=1}^{P} exp(i Ad(Γ_i)X(b_i)))·Hol_C(U), with Γ_i := U(b_1)⋯U(b_{i−1}) and the product ordered with i increasing to the right.
  - {#MD2.1.3.3} Proof: e^{iX₁}U₁e^{iX₂}U₂⋯ = e^{iX₁}(U₁e^{iX₂}U₁^{−1})U₁U₂⋯, and induction.
  - {#MD2.1.3.4} Orientation.
    {#MD2.1.3.4-1} The b_i are oriented along C. If C traverses a lattice bond b backwards, b_i = b̄ with U(b̄) = U(b)^{−1}, and (e^{iX}U)(b̄) = U(b)^{−1}e^{−iX(b)} = e^{iX(b̄)}U(b̄) with X(b̄) := −Ad(U(b)^{−1})X(b).
    {#MD2.1.3.4-2} With this convention the identity holds as stated.
- {#MD2.1.3.5} *The first-order term.* Take X = η𝐇_k(B′), with first-order part ηH₀B′ by (1), and B′ = g_kCA_k + O(C₁(ε₁^{RG2})^{−1}(g_k|A_k|)²) by (1).
  {#MD2.1.3.5-1} Then the part of f_k(U_k(e^{iB′}V^{(k)})) linear in A_k is
  {#MD2.1.3.6} iηg_k Σ_i dim(π)^{−1}tr[π_*(Ad(Γ_i)(H₀CA_k)(b_i))·π(Hol_C(U_{k+1}))], with Γ_i the U_{k+1}-transports.
  - {#MD2.1.3.7} It is odd in A_k.
    {#MD2.1.3.7-1} It is the leading word's first-order fluctuation of D2.0(5)(d).
  - {#MD2.1.3.8} Size.
    {#MD2.1.3.8-1} Cauchy's estimate in t for t ↦ 𝐇_k(tB′), |t| < ε₃/|B′|, and (1.18) give |H₀B′| ≤ 4B₀e^{16κ_s}|B′| in the sup norm.
    {#MD2.1.3.8-2} With |g_kCA_k| ≤ C₁g_k|A_k| (Cauchy, (1)) and L^kη = 1, the term is at most c_π′·4B₀e^{16κ_s}C₁g_k|A_k|_∞ per step-k bond of C (c_π′ of (4) *Constants*), where |A_k|_∞ is the sup norm.
    {#MD2.1.3.8-3} This uses (1.18) at s = 1 for CRE's operators (CRE p.267).
    {#MD2.1.3.8-4} With RG2's constants it holds at bonds of C in Ω_k, the scale-k set of VAR (190) ((4), *Two cases*), where (190) has j = k; at bonds in older regions (190) carries L^{k−j}, which (5) treats.
    {#MD2.1.3.8-5} CRE (3.7) prints a consistent sup bound < ε_k/10 for the cube-local functions 𝐇_{k,□} on □^∼.
  - {#MD2.1.3.9} Its locality in A_k is that of (4).
    {#MD2.1.3.9-1} In older large-field regions (y ∈ Λ_j, j < k), VAR (190) carries the prefactor (L^jη)^{−1} = L^{k−j}; that is case (B) of (4), whose size is (5)'s (the margin comparison is D2.2(4)(f), (6)(e), under CRE p.277's 𝐇-decay).

### (4) Localisation along C {#MSD2.1.4}

{#MD2.1.4.1} *Setting.* Let σ_k be a partition of the torus into cubes of side M, as in RG2's example.
{#MD2.1.4.1-1} Every cube Δ ∈ σ_k carries a parameter s(Δ).
{#MD2.1.4.1-2} H(s), G̃(s), H₀(s) are defined by RG2 p.3's rule, and 𝐇(s,B′) by (1.2)–(1.4) with these operators ((1.5)).
{#MD2.1.4.1-3} For σ ⊆ σ_k let Y(σ) := ∪_{Δ∈σ}Δ, with RG2's connectedness (p.4: a common (d−1)-dimensional wall).
{#MD2.1.4.1-4} Since no cube is exempt here, RG2's second case of connectedness, the one involving □̃⁴, does not occur.

- {#MD2.1.4.2} **(a)** 𝐇(1,B′) = 𝐇_k(B′) (p.3).
  {#MD2.1.4.2-1} Also 𝐇(0,B′) = 0: every walk term meets a cube, so H(0) = G̃(0) = H₀(0) = 0; then 𝐀₀ = 0 by (1.4), and 𝐇 = 0 by (1.2).
- {#MD2.1.4.3} **(b)** Let s(σ^c) = 0.
  {#MD2.1.4.3-1} The argument of RG2 p.4 uses the walk localisation and the multiplication rule of p.3, and the locality of C in (1.3) ("D(A′) = C(A′) on the neighborhood of Y(σ)^c"), of V₀, and of B′ in B. By it, 𝐇(s,B′) vanishes on a neighbourhood of Y(σ)^c, and on a component Y of Y(σ) it depends only on s|_Y, B′|_Y and (𝐔,𝐉)|_Y.
  {#MD2.1.4.3-2} Call it 𝐇_Y(s|_Y,B′|_Y).
- {#MD2.1.4.4} **(c)** The proofs of (1.11) and (1.18) use (1.7), |s(Δ)| ≤ e^{κ_s}, δ₁M ≥ κ_s, the count of at most 2⁴ cubes met by a short walk (p.5), the contraction bound (1.13), Prop. 4 [15] (p.5, with ε₂ for ε₃), and the conditions on ε₂, ε₃ quoted in (1).
  {#MD2.1.4.4-1} None of these uses the exempt cubes, so they hold with all cubes carrying parameters. 𝐇_Y is analytic for |s(Δ)| ≤ e^{κ_s} and |B′| < ε₃, and applying (1.18) to B′1_Y gives |𝐇_Y(s,B′)| ≤ 4B₀e^{16κ_s}|B′|_Y, where |B′|_Y is the supremum over Y. These are RG2's single-scale constants; where they apply is the case split of the bounds below.

{#MD2.1.4.5} *Expansion.* Let Φ(s) := Hol_C(e^{iη𝐇(s,B′)}U_{k+1}), as π-matrices at x₀.
{#MD2.1.4.5-1} The torus has finitely many cubes, so the fundamental theorem of calculus in each s(Δ) gives
{#MD2.1.4.6} Φ(1) = Σ_{σ⊆σ_k} ∏_{Δ∈σ}∫₀¹ds(Δ)∂_{s(Δ)}Φ(s)|_{s(σ^c)=0}.
- {#MD2.1.4.7} σ = ∅ gives Hol_C(U_{k+1}), by (a).
- {#MD2.1.4.8} At s(σ^c) = 0, by (b), the factor on a fine bond b of C is e^{iη𝐇_Y(b)}U_{k+1}(b) if b lies in a component Y, and U_{k+1}(b) otherwise.
  {#MD2.1.4.8-1} A component that contains no fine bond of C gives zero, since Φ does not depend on its parameters.
  {#MD2.1.4.8-2} So only the σ whose components all contain bonds of C remain.
- {#MD2.1.4.9} *Arcs and groups.*
  - {#MD2.1.4.10} For such a component Y, let S(Y) be the set of fine bonds of C in Y. Let I(Y) be the arc of C obtained by removing the longest maximal run of bonds not in S(Y); ties go to the run whose first bond comes first from x₀, and I(Y) = C if S(Y) = C.
  - {#MD2.1.4.11} Components whose arcs share a bond are joined into *groups* G: the connected components of the overlap graph.
    {#MD2.1.4.11-1} The arc of a group is I(G) := ∪_{Y∈G}I(Y), and distinct groups have disjoint arcs.
- {#MD2.1.4.12} *Insertions.* For a group G whose arc runs from x_G to x_G′, let
  {#MD2.1.4.13} Y_G := [∏_{Y∈G}∏_{Δ⊂Y}∫₀¹ds(Δ)∂_{s(Δ)}] Hol_{I(G)}(e^{iη𝐇(s,B′)}U_{k+1}) at s(Δ) = 0 for every cube Δ outside the components of G,
  {#MD2.1.4.14} a linear map from the fibre at x_G′ to the fibre at x_G, as a transport under 𝐔^u(b) = u(b_−)𝐔(b)u(b_+)^{−1} (orientation of D2.2(4)(a)).
  {#MD2.1.4.14-1} Write #(Y) for the number of cubes of Y and #(G) := Σ_{Y∈G}#(Y).
  - {#MD2.1.4.15} Inside a family, the other components' parameters do not change Y_G: a bond of C in a component Y′ of another group G′ lies in S(Y′) ⊆ I(G′), which is disjoint from I(G), and by (b) the factors on the bonds of I(G) depend only on the parameters of the components that contain them.
- {#MD2.1.4.16} **Result.** Put the groups in cyclic order along C, and let U_{(i)} be the U_{k+1}-transport along C from the end of I(G_i) to the start of I(G_{i+1}).
  {#MD2.1.4.16-1} Then
  {#MD2.1.4.17} f_k(U_k(e^{iB′}V^{(k)})) = f_{k+1} + Σ_{𝔊≠∅ compatible} dim(π)^{−1}tr(Y_{G_1}U_{(1)}⋯Y_{G_n}U_{(n)}).
  - {#MD2.1.4.18} A family 𝔊 is *compatible* if (0) each of its components is a connected union of cubes containing a fine bond of C, (i) its groups have disjoint arcs, (ii) its components are pairwise disjoint with no common wall, and (iii) each group is connected by arc overlaps.
  - {#MD2.1.4.19} The map σ ↦ (components of Y(σ)) ↦ 𝔊 is a bijection onto the compatible families.
    {#MD2.1.4.19-1} Given 𝔊, σ is the set of cubes of its components, and the components of Y(σ) are exactly these, since they are connected and pairwise wall-disjoint.
  - {#MD2.1.4.20} If one group has arc C, the family consists of that group alone and the term is dim(π)^{−1}tr Y_G.
  - {#MD2.1.4.21} This is the class form of D2.0(3) with Q ≡ 1 (hard-core interactions only).
- {#MD2.1.4.22} **Bounds** (case split).
  - {#MD2.1.4.23} *Two cases.* (A) every component of G lies in Ω_k, where (190) has j = j′ = k and RG2's constants of (c) apply; (B) some component of G meets Ω_kᶜ.
    {#MD2.1.4.23-1} A component can meet Ω_kᶜ while C lies in Ω_k, and large-field crossings are the main case of the IT-1 note's D1.1, so (B) is generic.
    - {#MD2.1.4.24} *Why Ω_k is the scale-k set of VAR (190).* (190) holds "for x ∈ Δ(y), … y ∈ Λ_j, y′ ∈ Λ_{j′}" (VAR p.308), with VAR's sets defined on p.277: "Λ_j = Ω_j^{(j)}∖Ω_{j+1}^{(j)}, Ω_{k+1} = ∅, or B^j(Λ_j) = Ω_j∖Ω_{j+1}", and 𝔅_k = ∪_{j≤k}Λ_j.
      {#MD2.1.4.24-1} So VAR's scale-k set is B^k(Λ_k) = Ω_k.
      {#MD2.1.4.24-2} RG1 p.265 applies VAR Sect. G at the step k → k+1, and CRE p.267 runs it on CRE's sequence {Ω_j} ((1)), so VAR's Ω_j are CRE's.
    - {#MD2.1.4.25} VAR's Λ_j are not CRE's small-field sets Λ_j of (3.20), which lie inside Ω_j; V4's "the large-fluctuation region R_1, which with Ω_1 determines the filled region Λ_1" (sec:main-result *Notation*) is about CRE's Λ_1.
      {#MD2.1.4.25-1} Below, VAR's sets are written Λ_j^{VAR} where they occur.
  - {#MD2.1.4.26} *Case (B).* The identity of (2) and the expansion above hold, since they need only the qualitative analyticity of 𝐇(s,B′) in (s,B′), which is CRE p.267 together with RG2 p.3: (1.5), the walk multiplication rule, and the walk expansion of the propagators ((3.107) [13] for RG1's operators; the multi-domain version through CRE p.267, not on the pages read otherwise).
    {#MD2.1.4.26-1} Its size is (5)'s: at points of a scale-j region, j < k, the kernels carry the prefactor (L^jη)^{−1} = L^{k−j} of VAR (190), and neither the per-bond bound of (c) nor (1.13)–(1.16) is on the pages read with k-independent constants there.
  - {#MD2.1.4.27} *Constants.* c_π′ := 2c_πmax(1, c_h) ≥ 2c_π, with c_π of #MOSTC.2-4 and c_h, |·| of #MOMST.9-2. For X ∈ 𝔤^c, ‖π(e^{iX})‖ = ‖e^{iπ_*(X)}‖ ≤ e^{‖π_*(X)‖} ≤ e^{c_π′|X|}: X = X₁ + iX₂ with X₁ := (X + X*)/2 and X₂ := (X − X*)/(2i) in 𝔤, |X₁|, |X₂| ≤ |X| since |X*| = |X| for the unitarily invariant |·| (#MD2.2.6.45-7), and ‖π_*(X)‖ ≤ c_π(‖X₁‖ + ‖X₂‖) ≤ c_πc_h(|X₁| + |X₂|). c_CM bounds the length of C in a cube of side M (D2.0(5)(f)).
    {#MD2.1.4.27-1} Fix ε_H < ε₃^{RG2} with c_π′c_CM·4B₀e^{16κ_s}ε_H ≤ 1 and ε_H ≤ 1 (the last for D2.6 closure §4.2). ε_H depends on π, M, κ_s, Bałaban's constants, and on C only through c_C.
    {#MD2.1.4.27-2} *Older-layer groups (D2.6 closure §4.2).* For the older-layer groups of case (B), ε_H is shrunk so that c_π′c_CM·O(1)·4B₀e^{16κ_s}ε_H ≤ 1, with RG2 p.6's B′-range's O(1) ≥ 1; this implies the condition above, and C₁^{RG2}δ_k ≤ ε_H/2 still holds for g_K small.
    {#MD2.1.4.27-3} *The VAR range (D2.6 closure §4.2).* Also ε_H ≤ C₁^{VAR}ε̄₁/(2c_V), c_V ≥ 1 the comparison constant |V − 1|_{VAR} ≤ c_V|V − 1| (G and π only) (VAR Prop. 9's B-range, (172), p.305: hypothesis |V′ − 1| < C₁^{VAR}ε₁, consequence |B′| < 2C₁^{VAR}ε₁, "for ε₁ sufficiently small"; ε̄₁ is VAR Sect. G's threshold, including (169)'s M′ε̄₁ ≤ a₁, and ε₁ := max(the data regularity, 2c_Vε_H/C₁^{VAR}) ≤ ε̄₁, so |V′ − 1|_{VAR} ≤ c_V(e^{|B′|} − 1) ≤ c_V(e^{ε_H} − 1) < 2c_Vε_H ≤ C₁^{VAR}ε₁ (B′ complex on the polydisc, submultiplicative norm, ε_H ≤ 1);
    {#MD2.1.4.27-4} (172)'s hypothesis, not its consequence, is the one checked, and a₁ is not a bound on ε₁), a constant condition fixed before the coupling.
    {#MD2.1.4.27-5} The shrunk ε_H replaces ε_H everywhere it occurs (T_Y = ε_H/|B′|_Y, the hypotheses O(1)ε_k ≤ ε_H and C₁^{RG2}δ_k ≤ ε_H/2, c_ev, c_M), not only for case (B).
  - {#MD2.1.4.28} *Conditions used:*
    - {#MD2.1.4.29} 4C₂B₀e^{16κ_s}ε₂ ≤ 1 (RG2 p.5), 4C₄^{RG2}B₀²e^{32κ_s}ε₃ ≤ 1 and 2B₀e^{16κ_s}ε₃ ≤ ε₂ (pp.5–6), C₁^{RG2}ε₁^{RG2} ≤ ε₃^{RG2} (RG2 p.7), ε_H < ε₃^{RG2}, δ₁M ≥ κ_s (in D2.1(4) the unmarked C₁ and ε₃ are RG2's (1.20) and p.7 constants, distinct from C₁^{VAR}; C₄ is marked RG2's, since VAR's C₄ (p.293) appears in the D2.6 closure §4.2; the unmarked C₂, ε₂ here are RG2's p.5 constants as well);
    - {#MD2.1.4.30} κ_s ≥ 1 (for the Cauchy radius e^{κ_s} − 1 ≥ e^{κ_s−1}), and κ_s > 3 for decay at complex backgrounds;
    - {#MD2.1.4.31} O(1)ε_k < ε₁^{RG2} (for (1.20)) and O(1)ε_k ≤ ε_H for every k ≤ K, with the O(1) of CRE (3.14) (times C₁^{RG2} of RG2 (1.20) in the second); these are smallness conditions on g_K through ε_k = ε(g_k) and g_k ≤ (1+β₀)g_K (for a fixed g₀ they restrict K; CRE (2.6) at simple G, #MD2.0.5.2-2);
    - {#MD2.1.4.32} g_k|A_k| ≤ ε_H/C₁^{RG2} on the complex A_k-domain ((4), *The hypothesis*), fixed with D2.2 and D2.4;
    - {#MD2.1.4.33} (𝐔,𝐉) in RG2's domain I.(i)–(iii) (p.6), including a bound on ∇a′ as in CRE (2.39);
    - {#MD2.1.4.34} VAR (172) for the configurations B at which 𝓗(B) is used;
    - {#MD2.1.4.35} 4c_π′M‖a′‖_∞ ≤ 1 at complex backgrounds: a condition on the radius of D(k+1)(iii), fixed with D2.4;
    - {#MD2.1.4.36} every torus period at least twice the side of C (for the arc-length step of the proof; at step 1 V4's (H3), "every coarse period K_μ … satisfies K_μ ≥ 3(n+2)" (sec:main-result *Hypotheses*), gives it for C_n of side nL);
    - {#MD2.1.4.37} |𝐇_k| < a₁ (RG1 p.266, for the analyticity of u_k in 𝐇_k), which follows from (1.18) if 4B₀e^{16κ_s}ε₃ ≤ a₁;
    - {#MD2.1.4.38} VAR (7), |(∂V)(p′) − 1| < ε₁^{VAR} on 𝔅_k, for V^{(k)}.
      {#MD2.1.4.38-1} This is part of Bałaban's construction as presented: RG1 p.265 applies VAR Sect. G with V₀ = V^{(k)} ("As in Sect. G [15] we write U_k(V′V^{(k)}) = U_k′(V′)U_{k+1}"), VAR Sect. G assumes "V₀ satisfies the condition (7)", and CRE p.267 transfers this to the multi-domain step.
  - {#MD2.1.4.39} *The hypothesis |B′|_Y ≤ ε_H.*
    - {#MD2.1.4.40} At real configurations.
      {#MD2.1.4.40-1} By CRE (3.11) and (3.15), V_k′ = e^{iB′} on B(Γ_{k+1}), so (3.14) gives |B′| < O(1)ε_k there directly; under O(1)ε_k ≤ ε_H this is the hypothesis.
      {#MD2.1.4.40-2} No (1.20) is needed.
    - {#MD2.1.4.41} The range of (1.20). g_k|A_k| < ε₁^{RG2} is part of what CRE p.267 transfers ("we perform the scaling transformation A_k′ = g_kA_k.
      {#MD2.1.4.41-1} All the applied formulas are the same as in Sect. 2 [I]"); RG2's domain for those formulas is g_k|B| < ε₁^{RG2}.
      {#MD2.1.4.41-2} The bound g_k|A_k| < O(1)ε_k for the scaled variable is not on the pages read: RG1 p.267 makes the change of variables B′ = B − hD̃(B) and then the scaling B = g_kB′ without stating it.
      {#MD2.1.4.41-3} It is used only in (1)'s *second-order bound* and in the complex A_k-domain of D2.2, where the radius g_k|A_k| ≤ min(ε₁^{RG2}, ε_H/C₁^{RG2}) is part of the domain's definition; the claim below uses |B′| directly.
    - {#MD2.1.4.42} At complex A_k.
      {#MD2.1.4.42-1} (1.20) on its complex domain gives |B′| ≤ C₁g_k|A_k|, so the hypothesis holds for g_k|A_k| ≤ ε_H/C₁^{RG2}.
      {#MD2.1.4.42-2} This is a radius condition of the complex A_k-domain, fixed with D2.2 and D2.4.
      {#MD2.1.4.42-3} The uniformity of (1.20) in (𝐔,𝐉) is printed: C₁ is "an absolute constant" (RG2 p.6 l.57), and p.6 l.44–45 states that "all the bounds above are uniform on the domain" given by I.(i)–(iii).
  - {#MD2.1.4.43} *Claim (case (A)).* Let G be a group of case (A), and suppose |B′|_Y ≤ ε_H for every Y ∈ G. Let the background be 𝐔 = e^{iηa′}U_{k+1} with a′ 𝔤^c-valued, as in CRE (2.39), and let C be a square or a′ = 0.
    {#MD2.1.4.43-1} Then
    {#MD2.1.4.44} ‖Y_G‖ ≤ ∏_{Y∈G}(|B′|_Y/ε_H)e^{−(κ_s−2−4c_π′M‖a′‖_∞)#(Y)}, where ‖a′‖_∞ is the sup over the bonds of I(G).
    - {#MD2.1.4.45} At real backgrounds, a′ = 0 and the exponent is −(κ_s−2)#(Y).
      {#MD2.1.4.45-1} For C a square (the target's C, D2.0(5)), the condition 4c_π′M‖a′‖_∞ ≤ 1 gives e^{−(κ_s−3)#(Y)}.
  - {#MD2.1.4.46} Proof.
    - {#MD2.1.4.47} Replace B′|_Y by t_YB′|_Y for each Y ∈ G. By (c), the integrand is analytic in the s(Δ) for |s(Δ)| ≤ e^{κ_s}, and in the t_Y for |t_Y| ≤ T_Y := ε_H/|B′|_Y, where T_Y ≥ 1.
    - {#MD2.1.4.48} At t_Y = 0, 𝐇_Y = 0 on S(Y) for every s.
      {#MD2.1.4.48-1} So the arc product does not depend on s|_Y, and the s|_Y-derivatives vanish.
      {#MD2.1.4.48-2} Since this holds for each Y separately, the Schwarz lemma in each t_Y gives the factor ∏_YT_Y^{−1}.
    - {#MD2.1.4.49} Cauchy's estimate on circles of radius e^{κ_s} − 1 ≥ e^{κ_s−1} (κ_s ≥ 1) around s(Δ) ∈ [0,1] gives e^{−(κ_s−1)} per cube.
    - {#MD2.1.4.50} The arc product over the polydisc.
      {#MD2.1.4.50-1} Write the factor on a bond b of I(G) as e^{iη𝐇_Y(b)}e^{iηa′(b)}U_{k+1}(b) (no 𝐇-factor on bonds in no component) with U_{k+1}(b) unitary.
      {#MD2.1.4.50-2} Its norm is at most exp(c_π′η(|𝐇_Y(b)| + |a′(b)|)), by *Constants*.
      {#MD2.1.4.50-3} Summing, the supremum is at most exp(c_π′ηΣ_{Y∈G}Σ_{b∈S(Y)}|𝐇_Y(s,t_YB′)(b)|)·exp(c_π′‖a′‖_∞·length(I(G))).
      {#MD2.1.4.50-4} The first factor is ≤ exp(c_π′c_CM·4B₀e^{16κ_s}ε_H·#(G)) ≤ e^{#(G)}, since η#S(Y) is the length of C in Y and is at most c_CM#(Y).
    - {#MD2.1.4.51} Arc length for a square C. I(Y) is the smallest arc of C containing S(Y), and Y is a connected union of #(Y) cubes of side M, so S(Y) has ℓ∞-diameter D ≤ M#(Y) (distances on the torus; every period is at least twice the side of C).
      {#MD2.1.4.51-1} If S(Y) lies on one side, it lies in a segment of length ≤ D, so length(I(Y)) ≤ D. If D is less than the side of C, S(Y) meets no two opposite sides, so at most two adjacent sides, and every point of it on one of them is within D of their common corner (the ℓ∞-distance of points on two perpendicular sides at distances a, b from the corner is max(a,b)); so length(I(Y)) ≤ 2D.
      {#MD2.1.4.51-2} Otherwise length(I(Y)) ≤ length(C) = 4·side ≤ 4D.
      {#MD2.1.4.51-3} Hence length(I(G)) ≤ Σ_{Y∈G}length(I(Y)) ≤ 4M#(G).
    - {#MD2.1.4.52} Multiplying the factors gives the claim.
  - {#MD2.1.4.53} Locality.
    {#MD2.1.4.53-1} Y_G depends on B′ and (𝐔,𝐉) on the components of G, and on U_{k+1} along I(G).
  - {#MD2.1.4.54} First order.
    {#MD2.1.4.54-1} A group with two or more components has no part linear in B′, since each component's factor vanishes at t_Y = 0.
    {#MD2.1.4.54-2} For G = {Y}, the linear part is the s|_Y-derivative of iηΣ_{b∈S(Y)}Hol_{I(Y),<b}(U_{k+1})·π_*((H₀(s)B′)(b))·Hol_{I(Y),≥b}(U_{k+1}), which is odd in B′.

### (5) Case (B) Components and the Transport Radius {#MSD2.1.5}

- {#MD2.1.5.11} *Case (B).* The size of the insertions of case (B), the groups with a component meeting Ω_kᶜ (the older scale sets B^j(Λ_j^{VAR}) = Ω_j∖Ω_{j+1}, j < k, whether or not C runs there), is D2.6's.
  {#MD2.1.5.11-2} At points of a scale-j region the kernels carry L^{k−j} (VAR (190)), which D2.6 bounds against the walk decay e^{−δ₀d(y,y′)/8} of the same bound, y′ in supp B′ ⊆ B(Γ_{k+1}).
  - {#MD2.1.5.12} *Decay distance.* A component Y with B′|_Y = 0 contributes zero: 𝐇_Y(s, 0) = 0 by (4)(c), so the arc product does not depend on s|_Y and the s|_Y-derivatives vanish.
    {#MD2.1.5.12-1} So every surviving case-(B) component meets both B(Γ_{k+1}) and Ω_kᶜ, and M#(Y) is at least the ℓ∞-distance between them.
    {#MD2.1.5.12-2} This is the decay distance D2.6 bounds L^{k−j} against.
    {#MD2.1.5.12-3} Where C runs outside Ω_{k+1}, the identity of (2) rests on CRE p.267's transfer of RG1 Sect. 2.
- {#MD2.1.5.13} *Transports.* The radius condition 4c_π′M‖a′‖_∞ ≤ 1 of (4), and the complex-background factor of the transports U_{(i)} between groups, the product form of D1(iii)′ (IT-1 note §3e: e^{C_Un_Cϱ₁}, with the number n_C of traversals), are D2.4's (D2.4(8), D2.2(6)(d) *Arcs*).

## D2.2 The Small-Field Map at Step k+1 {#MSD2.2}

{#MD2.2.0.1} D2.2 is D(k) → D(k+1) on the small-field side, for k ≤ N − 1, where no 𝐑-operation acts (D2.0(3), LFR I p.177 (ii)): given 𝒲_k on a labelled term of ρ_k, it gives the dressed loop of step k+1 on each term of ρ_{k+1}, in the class form of D2.0(3) at step k+1.

### (1) Quoted (CRE pp.267–271) {#MSD2.2.1}

- {#MD2.2.1.1} *The step-(k+1) integrand* at fixed Ω_{k+1}, pp.267–268: χ_{k+1}(Ω_{k+1})∫dV_k|_{Ω_{k+1}ᶜ}δ(V̄_kV_{k+1}^{−1})ζ(Ω_{k+1}ᶜ)·T_kexp[A_k(1/g_k², U_{k+1}) + log g_kd(𝔤)|B(Γ_{k+1})*| + log σ₀|B(Γ_{k+1})*| − log z(L⁴−1)|Γ_{k+1}|]·z^{(k)}∫dA_k|_{Ω_{k+1}}χ_k′(Ω_{k+1})exp[−½⟨A_k, C*Δ^{(k)}CA_k⟩ + 𝐏^{(k)}(g_k, U_{k+1}, A_k) + {(𝐄_k+𝐑_k+𝐁_k)(U_k(exp i[g_kCA_k − hD̃(g_kCA_k)]V^{(k)})) − (𝐄_k+𝐑_k+𝐁_k)(U_{k+1}) + A(1/g_k²(·) − 1/g_k², U_k(…)) − A(1/g_k²(·) − 1/g_k², U_{k+1})}] ((3.15)).
- {#MD2.2.1.2} *(3.16), p.268:* on Ω_{k+1}^{∼−1}, 1 = Σ_{R_{k+1}}χ^{(k)}(R_{k+1}ᶜ)χ^{(k)c}(R_{k+1}), with the tests sup_{b∈(□′^{∼2})^{(k)*}}|A_k(b)| < δ_k, resp. ≥ δ_k, on L²M₂R_{k+1}-cubes.
  {#MD2.2.1.2-1} On cubes of R_{k+1}ᶜ the small-field function of (3.3) "is equal to 1, because of the bound on A_k introduced by the second" ((3.17)–(3.19), pp.268–269).
- {#MD2.2.1.3} *(3.20)–(3.21), p.269:* Λ_{k+1} = Ω_{k+1}^{∼−2} ∩ (R′^∼_{k+1})ᶜ and S_{k+1} = (Ω_{k+1}∖Ω_{k+1}^{∼−1}) ∪ R_{k+1}; Λ_{k+1} is modified "in the same way as in Sect. 1" (components of Λ_{k+1}ᶜ inside a cube of size 100LMR_{k+1} are replaced by the smallest rectangular parallelepiped containing them); χ(Ω_{k+1}∩Λ_{k+1}ᶜ, S_{k+1}) = χ^{(k)}(R_{k+1}ᶜ∩Λ_{k+1}ᶜ)χ^{(k)c}(R_{k+1})χ_k′(S_{k+1}).
- {#MD2.2.1.4} *The change of variables, p.269:* on the bonds b ∈ S_{k+1}^{(k)*}, (1.22) with 𝐇^{(k)}(b) for 𝐇_{1,Ax}(b) on (R_{k+1}^{∼2}∩S_{k+1})^{(k)*}, the simpler change elsewhere.
  {#MD2.2.1.4-1} It turns χ_k′(S_{k+1}) into the same function with V^{(k)} replaced by V^{(k)}_{Λ_{k+1}ᶜ∩Λ_k}; "The other characteristic functions are unchanged"; the action gains V^{(k)}(S_{k+1}, A_k, 𝐇^{(k)}).
- {#MD2.2.1.5} *(3.23)–(3.25), p.270:* T^{(k+1)} := Σ_{S_{k+1}}∫dV_k|_{Ω_{k+1}ᶜ}δ(V̄_kV_{k+1}^{−1})ζ(Ω_{k+1}ᶜ)z^{(k)}∫dA_k|_{Ω_{k+1}∩Λ_{k+1}ᶜ}χ(Ω_{k+1}∩Λ_{k+1}ᶜ, S_{k+1})exp[−½⟨A_k, C*Δ^{(k)}CA_k⟩ + ½⟨A_k, C*Δ^{(k)}CC^{(k)}(Λ_{k+1})C*Δ^{(k)}CA_k⟩], T_{k+1} = T^{(k+1)}T_k, and
  {#MD2.2.1.6} C^{(k)}(Λ_{k+1}) is the inverse of the Λ_{k+1}-block of C*Δ^{(k)}C.
  {#MD2.2.1.6-1} This is the step-(k+1) form of CRE (1.26), p.253 (checked in the transcription, lines 6–11), where dμ_{C^{(0)}(Λ₁)} is the normalised Gaussian measure of ½⟨Λ₁A, C*Δ₁CΛ₁A⟩, as the completed square ½⟨Λ₁ᶜA, C*Δ₁CC^{(0)}(Λ₁)C*Δ₁CΛ₁ᶜA⟩ there shows.
  {#MD2.2.1.7} (Tρ_k)(V_{k+1}) = Σχ_{k+1}(Ω_{k+1})T_{k+1}exp[A_k(1/g_k², U_{k+1}) + E_0^{(k)}]·z^{(k)}∫dA|_{Λ_{k+1}}χ^{(k)}(Λ_{k+1})exp[−½⟨A, C*Δ^{(k)}CA⟩ − ⟨A, C*Δ^{(k)}CA_k⟩ − ½⟨A_k, C*Δ^{(k)}CC^{(k)}(Λ_{k+1})C*Δ^{(k)}CA_k⟩ + 𝐏^{(k)}(g_k, (A_k, A)) + {…} + V^{(k)}(S_{k+1}, (A_k, A))].
  {#MD2.2.1.8} "Here A_k denotes the fluctuation field on Ω_{k+1}∩Λ_{k+1}ᶜ, and A denotes this field on Λ_{k+1}."
- {#MD2.2.1.9} *(3.26)–(3.27), p.271:* the logarithm of the last integral is written by interpolation in s (multiplying 𝐑_k″) and t (multiplying 𝐁_k, the A(1/g_k²(·) − 1/g_k², ·) terms and V^{(k)}), with ⟨·⟩_{s,t} "the expectation value with respect to the probabilistic measure" Z_{s,t}^{−1}dμ_{C^{(k)}(Λ_{k+1})}(A)χ^{(k)}exp[−⟨A, C*Δ^{(k)}CA_k⟩ + 𝐏^{(k)} + {…}_{s,t} + tV^{(k)}(S_{k+1})].
  {#MD2.2.1.9-1} The print has χ_k and S_k in (3.27); they are χ^{(k)} and S_{k+1} (corrected p.271 l.22), since (3.27) is the measure of the expectations ⟨·⟩_{s,t} of (3.26) (p.271 l.20), whose integrand carries χ^{(k)} and V^{(k)}(S_{k+1}) (p.271 l.11–15); and the display called "(3.26)" on pp.275, 277, 279 carries no printed number (transcriber's notes, p.271).

### (2) The Numerator Identity at Step k+1, for k ≤ N − 1 {#MSD2.2.2}

- {#MD2.2.2.1} *Linearity.* From (3.1) to (3.25), every operation of CRE pp.264–270 acts on the integrand of a fixed term in one of seven ways (pp.264–267 read in full for this list):
  - {#MD2.2.2.2} (i) inserting a decomposition of unity: (3.2) for P_{k+1} and (3.3) for Q_{k+1}, p.265, and (3.16) for R_{k+1}, p.268;
  - {#MD2.2.2.3} (ii) a pointwise identity on the support of the characteristic functions: (3.8)–(3.9), p.266, "χ_k(□) = 1 for □ ⊂ Ω_{k+1}^∼" and "χ_Ax((Ω_{k+1}^∼)^{(k)}) = 1"; and (3.17)–(3.19), pp.268–269, the small-field function of (3.3) is 1 on the cubes of R_{k+1}ᶜ;
  - {#MD2.2.2.4} (iii) a change of integration variables on the bonds of S_{k+1} (p.269), a bijection ψ_{k+1} of the A_k-variables there;
  - {#MD2.2.2.5} (iv) regrouping the sums: at fixed Ω_{k+1} the resummation over P_{k+1}, Q_{k+1} into ζ(Ω_{k+1}ᶜ), p.267, which "applies only to the characteristic functions and the gauge fixing terms localized in Ω_k∖Ω_{k+1}"; then the reindexing R_{k+1} ↦ (Λ_{k+1}, S_{k+1}) of p.270, a bijection since R_{k+1} = S_{k+1}∖(Ω_{k+1}∖Ω_{k+1}^{∼−1}); also the filling of Λ_{k+1}, a function of (Ω_{k+1}, R_{k+1}), and the pointwise regroupings of factors on pp.267, 269, 270;
  - {#MD2.2.2.6} (v) splitting the A_k-integral into the conditional integral over A = A_k|_{Λ_{k+1}} and the outer integral in T^{(k+1)}, with the block form of the quadratic form ((3.23)–(3.25)): the exponent of (3.23) plus that of the last integral of (3.25) is −½⟨A_k + A, C*Δ^{(k)}C(A_k + A)⟩, the two terms with C^{(k)}(Λ_{k+1}) cancelling;
  - {#MD2.2.2.7} (vi) the change of variables of pp.266–267 on B(Γ_{k+1}): the fluctuation field V_k′ = V_k(V^{(k)})^{−1} ((3.11)), A_k′ = (1/i)log V_k′, the expansion "with respect to A_k′", the linearisation of the δ-functions, their removal "using the operator C", and the scaling A_k′ = g_kA_k.
    {#MD2.2.2.7-1} Together these give V_k = e^{iB′(A_k)}V^{(k)} with B′ = g_kCA_k − hD̃(g_kCA_k), and the Jacobian is part of the first exponential of (3.15) and of 𝐏^{(k)} (CRE p.269's action change, its 𝐏^{(k)} half, (iii)(b));
  - {#MD2.2.2.8} (vii) the axial gauge fixing of p.265, "as in (1.5), with V_k, ε_k, g_k instead of U, ε_0, g_0", in (P′^∼_{k+1} ∪ Z′^{∼5}_k)ᶜ, followed by the Faddeev–Popov procedure (p.265: "We get an expansion of the form (1.6)"; the procedure itself is on p.247).
- {#MD2.2.2.9} *Each commutes with the insertion.* Multiply the integrand by a bounded function F of the integration variables.
  - {#MD2.2.2.10} (i), (ii), (v): directly; (v) by Fubini on the finite torus.
  - {#MD2.2.2.11} (iv): F does not depend on P_{k+1}, Q_{k+1}, and the p.270 regrouping is a reindexing, so F stays inside each term.
  - {#MD2.2.2.12} (vi): F is defined as composed with it, F = 𝒲_k(U_k(e^{iB′}V^{(k)})).
  - {#MD2.2.2.13} (iii): with F composed with ψ_{k+1}.
    {#MD2.2.2.13-1} This rests on three inputs.
    {#MD2.2.2.13-2} (a) ψ_{k+1} is a bijection between the supports (below).
    {#MD2.2.2.13-3} (b) *CRE p.269's action change (exact changes).* p.269 prints: "The action is changed by terms corresponding to (1.24), and by terms obtained by the first order expansion of the action with respect to the perturbative parts of the changes of variables … We denote this new part of the action by V^{(k)}(S_{k+1},A_k,𝐇^{(k)})".
    {#MD2.2.2.13-4} So V^{(k)}(S_{k+1}, A_k, 𝐇^{(k)}) is the exact change of the action under ψ_{k+1}, with its Jacobian: the first-order Taylor formula with integral remainder is exact, and (3.25) is printed with "=" (Bałaban's). Likewise 𝐏^{(k)} is the exact remainder of the p.267 expansion in A_k′.
    {#MD2.2.2.13-5} The 𝐏^{(k)} half is also what (vi)'s "=" uses.
    {#MD2.2.2.13-7} (c) p.269's "The other characteristic functions are unchanged" and "These changes of variables transform the function χ_k′(S_{k+1}) into the same function, but with V^{(k)} replaced by V^{(k)}_{Λ_{k+1}ᶜ∩Λ_k}", Bałaban's statements.
    {#MD2.2.2.13-8} The identity itself does not depend on (c), since ∫G·F = ∫(G∘ψ)(F∘ψ)|det Dψ|; (c) only identifies the result with CRE's printed (3.25) and (3.27).
  - {#MD2.2.2.14} (vii): the Faddeev–Popov step needs the integrand to be invariant under the gauge transformations u of V_k used there, which are 1 at the centres of the scale-(k+1) blocks and act in (P′^∼_{k+1} ∪ Z′^{∼5}_k)ᶜ ⊂ Λ_k.
    {#MD2.2.2.14-1} Without F this is CRE p.250's "invariance of all the expressions determining the density with respect to the gauge transformations of the new field" (quote completed from the transcription).
    {#MD2.2.2.14-2} For F, put ũ(x) := u(y) for x ∈ B^k(y).
    {#MD2.2.2.14-3} The block averages are covariant (RG1 (0.6), "M({u𝐔_jv}) = uM({𝐔_j})v"; REG p.78, "(Ū^u)^j_b = u(b_−)(Ū^j)_bu^{−1}(b_+) for b ⊂ T^{(j)}") and the action is invariant, so U_k(V_k)^ũ minimises under the constraint of V_k^u, as U_k(V_k^u) does.
    {#MD2.2.2.14-4} By the uniqueness of the minimiser in its orbit (Bałaban's; RG1 p.265 states it for V^{(k)}: "there exists the exactly one critical point, which is obtained by taking the critical orbit … and choosing the element of the orbit satisfying the axial gauge conditions"), U_k(V_k^u) = (U_k(V_k)^ũ)^r, with r in REG's subgroup (1.14) (r(y) = 1 for y ∈ 𝔅_k) restoring the gauge condition.
    - {#MD2.2.2.15} *r = 1 where ũ = 1 (REG pp.78–79, RG1 pp.252–253).* REG (1.19), "∏_{b⊂Γ_{x_{n+1},x_n}}R(Ū_0^n(Γ_{x_{n+1},b_−}))Ũ′^n_b = 1" with Ũ′^n = (overline{U′U_0})^n(Ū_0^n)^{−1} (1.20), telescopes to Ū^n(Γ_{x_{n+1},x_n}) = Ū_0^n(Γ_{x_{n+1},x_n}) for U = U′U_0 (for two bonds b₁, b₂: Ū_{b₁}Ū_{0,b₁}^{−1}·Ū_{0,b₁}Ū_{b₂}Ū_{0,b₂}^{−1}Ū_{0,b₁}^{−1} = Ū_{b₁}Ū_{b₂}(Ū_{0,b₁}Ū_{0,b₂})^{−1}).
      {#MD2.2.2.15-1} The absolute form (1.15) is the case U_0 = 1.
      {#MD2.2.2.15-2} By the covariance, for U^r the condition reads r(x_{n+1})Ū^n(Γ)r(x_n)^{−1} = Ū_0^n(Γ), so r(x_n) = Ū_0^n(Γ)^{−1}r(x_{n+1})Ū^n(Γ): r is fixed down each chain x_j, x_{j−1}, …, x₀ from r(x_j) = 1.
      {#MD2.2.2.15-3} The path Γ_{x_{n+1},x_n} joins x_{n+1} to x_n ∈ B(x_{n+1}), and the averages on its bonds use the contours 𝐆(y,x), "shortest contours with the initial point at y, and the final point at x" for x ∈ B(y) (RG1 p.252), inside the two blocks of each bond (RG1 p.253's M(𝐔,c)).
      {#MD2.2.2.15-4} So the conditions on a block B^k(y) involve the configuration on B^k(y) only.
      {#MD2.2.2.15-5} On a block where ũ = 1, U_k(V_k)^ũ = U_k(V_k) there, which satisfies them, so r = 1 on that block.
      {#MD2.2.2.15-6} This holds for any background U_0 that the transformation u leaves unchanged; U_0 = U_{k+1}(V_{k+1}) is unchanged, since u = 1 at the centres of the scale-(k+1) blocks and the averages are covariant.
      {#MD2.2.2.15-7} Which gauge condition the step's representative uses is the representative item (D2.2(4)(d): the hierarchical mean axial gauge, RG1 (0.11)'s variables equal to 1 at every level); the argument covers (1.15), (1.19), and that mean condition alike, each being a covariant condition on the averages inside the block.
    - {#MD2.2.2.16} Hence ũr = 1 on every block outside the gauge-fixing region, and R(ũr)ω = ω below. ũ = 1 on every block outside the gauge-fixing region, in particular near Z_k = Λ_kᶜ, which carries the outer fluctuation fields ω: they live on Ω_{j+1}∩Λ_{j+1}ᶜ ⊆ Λ_kᶜ, j < k, since Λ_k ⊆ Ω_k ⊆ Λ_{k−1} (pp.264–265), and at k = 1 on the bonds I∖D(Λ) and J of V4's exterior (IT-1 note §3d(2)(d)).
      {#MD2.2.2.16-1} So R(ũr)ω = ω, and Cov(k) gives F(U_k^{ũr}, ω) = F(U_k, ω) for the closed words, that is F(V_k^u) = F(V_k).
      {#MD2.2.2.16-2} CRE p.250 prints the same block-constant extension at step 1, "u_0(x)=v(y) for x ∈ B(y), and the field U_0 constructed in (1.6) transforms by u_0".
- {#MD2.2.2.17} *The bijection ψ_{k+1}.* ψ_{k+1} is a bijection between the supports by (6)(a), the step-(k+1) form of V4 Lemma boundary-bijection.
  {#MD2.2.2.17-1} Its inputs are Inputs 1–4 of (6)(a), Input 3 being |Z_b − 1| < C_Zδ_k from (3.13).
  {#MD2.2.2.17-2} Its conditions are e^{R_k} ≥ 40·O(1)A₀/A₁ and δ_k ≤ δ_G(C_Z), both uniform in k for g_K small by g_k ≤ (1+β₀)g_K (#MD2.0.5.2-2).
  {#MD2.2.2.17-3} Its further inputs are those (6)(a) lists: the (k)* convention, CRE p.267's (g_k, δ_k), and Input 4's three (the k-independent O(1) of p.269, CRE (2.6)–(2.7), and the bound on S_{k+1} for bonds leaving S_{k+1}).
- {#MD2.2.2.18} The nonlinear step, the treatment of the logarithm of the A-integral from the unnumbered display of p.271 on, concerns the normalisation only.
- {#MD2.2.2.19} *The identity.* Apply (i)–(vii) to each term of (3.1) for the numerator N_k^C = Σχ_kT_k[𝒲_kexp A_k] (D2.0(3)) with F := 𝒲_k(U_k(e^{iB′}V^{(k)}))∘ψ_{k+1}, B′ = g_kCA_k − hD̃(g_kCA_k) (D2.1(1)).
  {#MD2.2.2.19-1} Then
  {#MD2.2.2.20} T N_k^C = Σχ_{k+1}(Ω_{k+1})T_{k+1}[𝒲_{k+1}exp A_{k+1}], with 𝒲_{k+1} := ⟨F⟩_{1,1},
  {#MD2.2.2.21} where exp A_{k+1} is CRE's integrand of (3.25) (A_{k+1} the logarithm, unchanged) and ⟨·⟩_{1,1} is the expectation of (3.27) at s = t = 1: at s = t = 1, (3.27) is the normalised integrand of the last integral of (3.25), with the constant −½⟨A_k, …A_k⟩ cancelled by the normalisation.
  - {#MD2.2.2.22} Z_{1,1} ≠ 0: the last integral of (3.25) equals z^{(k)}·(Gaussian normalisation)·e^{−½⟨A_k,…A_k⟩}·Z_{1,1}, and CRE takes its logarithm in the unnumbered display of p.271; p.279 states that the resulting terms "satisfy all the conditions of the inductive assumption".
  - {#MD2.2.2.23} F is finite on the support of the characteristic functions: |𝒲_k| ≤ |κ^{(k)}|e^{|𝓔_k|}∏_n(1+ν_n^{(k)}) < ∞ on the finite torus, from the class form of D2.0(3).
    {#MD2.2.2.23-1} The identity uses no other bound on F.
- {#MD2.2.2.24} *What 𝒲_{k+1} depends on.* V_{k+1} (through U_{k+1}); the outer variables of T_{k+1}, namely those of T_k, A_k on Ω_{k+1}∩Λ_{k+1}ᶜ and V_k on Ω_{k+1}ᶜ; and the labels.
  {#MD2.2.2.24-1} These are D2.0(3)'s outer variables at step k+1 (CRE (2.20)–(2.21)).
- {#MD2.2.2.25} So D2.2's task is to write ⟨F⟩_{1,1} in the class form of D2.0(3) at step k+1, with D(k+1)(ii)–(v).

### (3) The Carrier at Step k+1 {#MSD2.2.3}

- {#MD2.2.3.1} *(a) The carrier is CRE's Λ_{k+1}.* The observable F is integrated in A = A_k|_{Λ_{k+1}} under ⟨·⟩_{1,1}; A_k on Ω_{k+1}∩Λ_{k+1}ᶜ is outer.
  {#MD2.2.3.1-1} D2.2 adds no label at step k+1.
  {#MD2.2.3.1-2} At step 1, V4's labels Λ = Λ₁^fin refine CRE's Λ₁ (IT-1 note §3c(4), the choice (P)); the integration of (6) needs no refinement of Λ_{k+1} (#MD2.2.6.203-1).
  {#MD2.2.3.1-3} What (6) uses: on Λ_{k+1}^∼ the small-field tests of (3.16), and on all of Ω_{k+1} the bound |A_k′| < O(1)ε_k of CRE (3.14), which gives D2.1's condition |B′| ≤ ε_H under O(1)ε_k ≤ ε_H (D2.1(4)).
- {#MD2.2.3.2} *(b) The step-1 domain Λ = Λ₁^fin at the later steps (every line of CRE pp.255–284 containing Λ_j, Z_j or φ_j read in its context, pp.264–267 in full).*
  - {#MD2.2.3.3} *The data.* With (P), the step-1 data of a labelled term are (Ω₁, Λ₁, Λ, R₁, S₁).
    {#MD2.2.3.3-1} Ω₁, Λ₁, R₁, S₁ are CRE's, Λ₁ stays an outer label, and Λ = Λ₁^fin ⊆ Λ₁ is made by V4's retreat (sec:c5-3-1, with 𝒬⁺ of IT-1 note §3c(4⁗)(c)) and plays CRE's Λ₁ at the later steps, with Z₁ = Λᶜ (IT-1 note §3c(4⁗), §3f(2)).
  - {#MD2.2.3.4} *The printed conditions on the domains, at Λ.* p.255: "if a component of Z_j is contained in a cube of the size 100MR_j (in the L^{−j}-lattice), then it is a rectangular parallelepiped". p.256: Ω_j, Λ_j, "which are determined by he j-th renormalization transformation, but not by the 𝐑-operation, are unions of MR_j-cubes in the lattice T_{L^{−j}}.
    {#MD2.2.3.4-1} They satisfy also other conditions, e.g., the distance between their boundaries is at least equal to 2MR_j, which will be determined inductively by the operations in the k+1-st step" (two conditions printed, others announced without a list; print "he" for "the").
    {#MD2.2.3.4-2} At Λ: Λ is a union of ℓ-cubes, the MR₁-cubes of T_{L^{−1}} (ℓ = LMR₁ fine, D2.0(1)); Λ ⊆ Λ₁ ⊆ Ω₁^{∼−2}, so the distance condition holds (IT-1 note §3c(4′)); and Λ is filled, since the retreat ends with Fill, the iteration of CRE's p.251 modification until nothing changes (V4 Section c5-3-1, Lemma c5-3-1(c), Lemma c5-3-3(i)).
    {#MD2.2.3.4-3} P.251 (transcription): components of Λ₁ᶜ "which are contained in cubes of sizes smaller than 100LMR_1" are replaced "by the smallest rectangular parallelepipeds containing them".
    {#MD2.2.3.4-4} Filling can merge components; the label indicator still factorises over the ∗-components of Λᶜ (IT-1 note §3c(4⁗)(d), which treats Fill_1 explicitly).
  - {#MD2.2.3.5} *The uses of Λ_j, j ≤ k, on pp.262–284, each with the property it needs and how it holds at j = 1:*
    1. {#MD2.2.3.6} *𝐄^{(j)}(Λ_j, U_k, z)* with (2.26)–(2.27): z ∈ Λ_j⁰, the sum over X ∈ 𝐃_j with X ⊂ Λ_j, properties (i)–(iv) of p.259.
       {#MD2.2.3.6-1} Used in (2.43) (p.263, Ω ⊂ B^j(Λ_j⁰)), on p.276 ("For the term 𝐄^{(j)} it is in fact restricted to the domain Λ_j"), and in the proof of Theorem 2 and the renormalisation, pp.279–284 (cases (I.3.5) for X ⊂ Λ_j; comparison with "(2.26) for Λ_j = L^{−j}Z^d", p.282).
       {#MD2.2.3.6-2} Needs: the representation at Λ, and that the terms with X ⊂ Λ do not depend on Λ, the step-1 form of p.278's remark ("do not depend on Λ_{k+1}, and coincide with the corresponding terms arising from" the whole space).
       {#MD2.2.3.6-3} At Λ: built by CRE's step-1 construction at Λ (D1.0(P)(i), IT-1 note §3c(4″)), under the Λ construction (#MOMGD.22).
    2. {#MD2.2.3.7} *The coupling function.* (2.24), p.259: 1/g_{j−1}²(x) = 1/g_j²(x) + β_j(g_{j−1})φ_j(x), φ_j ∈ C_0^∞(Λ_j), φ_j = 1 on Λ_j^{∼−1}.
       {#MD2.2.3.7-1} Used on p.263 (Ω = B^j(Λ_j⁰), φ = φ_j), in the terms A(1/g_k²(·) − 1/g_k², ·) of (3.15) and the unnumbered display of p.271, in p.279's update by (2.24), and on p.283 ("For z ∈ Λ_j⁰ we have h_zφ_j = h_z").
       {#MD2.2.3.7-2} At Λ: φ₁ ∈ C_0^∞(Λ), φ₁ = 1 on Λ^{∼−1}, by CRE (1.27) at Λ (p.253, checked in the transcription: "We renormalize it in the region Λ₁ … φ₁ ∈ C_0^∞(Λ₁), φ₁ = 1 on Λ₁^{∼−1}"), which (P) applies with Λ (IT-1 note §3c(4), "A₁^Λ given by CRE's (1.26)–(1.30) with Λ₁ replaced by Λ"). h_zφ₁ = h_z for z ∈ Λ⁰ needs only that Λ is a union of MR₁-cubes.
       {#MD2.2.3.7-3} The j = 1 piece β₁(g₀)(1 − φ₁) of 1/g_k²(·) − 1/g_k² vanishes on Λ^{∼−1}, which contains every later Ω_{k+1} ⊆ Ω₂ ⊆ (Z₁′^{∼6})ᶜ (p.265, (3.5)), as for CRE's Λ₁.
    3. {#MD2.2.3.8} *E_k.* p.262: "The constant E_k (depending on {Ω_j}, {Λ_j} also) is obtained by subtracting one-step vacuum energy expressions, generated in small field regions, from the initial constant E".
       {#MD2.2.3.8-1} Λ enters through the step-1 subtraction only, the values at U₁ = 1 in Λ (p.253: "We renormalize it in the region Λ₁ subtracting the values at U₁=1", checked in the transcription).
       {#MD2.2.3.8-2} At Λ: by (1.26)–(1.30) at Λ, under (P).
       {#MD2.2.3.8-3} Its bound (p.264: "E_k, except the terms logarithmic in coupling constants, has the same bound as above, only with a different constant") holds at Λ: at k = 1, Λ^{(1)} ⊆ Ω₁^{(1)} = Γ₁; for k ≥ 2 the bound is CRE's for every Λ₁ satisfying the printed conditions, under the Λ construction (#MOMGD.22; D1.0(P)(i)), as in (b)'s conclusion, and Λ satisfies them (second bullet of (b)).
    4. {#MD2.2.3.9} *The 𝐁-bound (2.47)–(2.48), p.264.* Λ_k⁰ enters (2.47) in the terms j = n ("this inequality with |Γ_n∖Λ_k⁰| for j = n").
       {#MD2.2.3.9-1} Since Γ_n ∩ Λ_k = ∅ for n < k (Λ_k ⊆ Ω_k ⊆ Ω_{n+1}), (2.48) keeps it only for n = k.
       {#MD2.2.3.9-2} So Λ enters only at k = 1: |𝐁₁| ≤ 2B₁|Ω₁^{(1)}∖Λ⁰| (IT-1 note §3c(4⁗)(a), under the Λ construction, #MOMGD.22).
    5. {#MD2.2.3.10} *The label sums* over {Ω_j}, {Λ_j}, {S_j} in (3.1), (3.15) and on p.270.
       {#MD2.2.3.10-1} The operations act term by term ((2)).
       {#MD2.2.3.10-2} Each step-1 term has the form (2.18) at k = 1 with Λ (D1.0(P)), and the label sum is IT-1 note §3c(4⁗)(d)'s.
    6. {#MD2.2.3.11} *Z_k = Λ_kᶜ, pp.264–265.* It is the input of Z_k′, "the union of all LMR_{k+1}-cubes intersecting the region Z_k", and of the step-(k+1) restrictions built around Z_k′^{∼4}, …, Z_k′^{∼6}.
       {#MD2.2.3.11-1} The construction takes any union of cubes, so at k = 1 it applies to Z₁ = Λᶜ.
    7. {#MD2.2.3.12} *p.269, j = k.* The determining set 𝐁(Λ_{k+1}ᶜ∩Λ_k) ∪ 𝐁_{k+1} of (2.14), with 𝐁_k(Λ_k)|_{Ω_{k+1}ᶜ}, the minimiser U_{k+1,Λ_{k+1}ᶜ∩Λ_k}, V^{(k)}_{Λ_{k+1}ᶜ∩Λ_k}, 𝐇^{(k)}, and with them ψ_{k+1} and V^{(k)}(S_{k+1}).
       {#MD2.2.3.12-1} At k = 1 they use Λ through 𝐁₁(Λ)|_{Ω₂ᶜ}, which needs Λ to be a union of M₁-cubes (p.261's construction).
       {#MD2.2.3.12-2} This holds: CRE's cube partitions are nested, so each ℓ-cube is a union of M₁-cubes (CRE p.245 l.38–40: the partitions "have to be compatible, and compatible with the partition π₀ as well, and with other partitions introduced later"; V4 Section fixed-first-kernel).
    8. {#MD2.2.3.13} *(3.38)–(3.39), p.274:* Euclidean covariance of the whole-space construction (Ω_j = Λ_j = T_η); no Λ_j.
    9. {#MD2.2.3.14} *p.277.* The last expression in the curly bracket of (3.27), or (3.15), A(1/g_k²(·) − 1/g_k², U_k(…)) − A(1/g_k²(·) − 1/g_k², U_{k+1}), is localised by "supp(g_k^{−2}(·)−g_k^{−2}) ⊂ Z_k".
       {#MD2.2.3.14-1} By (2.24) and the constant recursion of (I.0.20), cited on p.259 ("Here the coupling constants g_{j−1} are defined as in (I.0.20)"; (I.0.20) is RG1's; (1.27) at j = 1), with 1/g_0²(·) = 1/g_0², g_k^{−2}(·) − g_k^{−2} = Σ_{j≤k}β_j(g_{j−1})(1 − φ_j); p.259 prints the case j = k as "Thus g_j²(x)=g_j² on the last domain".
       {#MD2.2.3.14-2} The j-th summand vanishes on Λ_j^{∼−1}.
       {#MD2.2.3.14-3} Λ_k ⊆ Ω_{j+1} ⊆ Λ_j^{∼−1} for j < k (item 2's inclusion, Ω_{j+1} ⊆ (Z_j′^{∼6})ᶜ, p.265).
       {#MD2.2.3.14-4} So the support lies in (Λ_k^{∼−1})ᶜ, which is what the localisation uses, since Ω_{k+1} ⊆ (Z_k′^{∼6})ᶜ ⊆ Λ_k^{∼−1} (item 2's inclusion at j = k), so (Λ_k^{∼−1})ᶜ ⊆ Ω_{k+1}ᶜ ⊆ Λ_{k+1}ᶜ, and the terms are localised away from Λ_{k+1}, as "contribute to the boundary terms only" requires; the print's "⊂ Z_k" is not needed.
       {#MD2.2.3.14-5} At j = 1 the inclusion is item 2's Ω₂ ⊆ Λ^{∼−1}.
       - {#MD2.2.3.15} *The inclusion (Z_j′^{∼6})ᶜ ⊆ Λ_j^{∼−1}.* By (2.9), second line at n − m = 1, R_j ≤ L(1+g_{j+1}²β′)^{β₀}R_{j+1} < L²R_{j+1} for g small, and the R's are powers of L, so R_j ≤ LR_{j+1}.
         {#MD2.2.3.15-1} So an LMR_{j+1}-cube of p.264's partition contains every MR_j-cube it meets (the partitions are compatible, p.264), and (Λ_j^{∼−1})ᶜ ⊆ Z_j′^{∼1}.
         {#MD2.2.3.15-2} The same holds in item 2.
    10. {#MD2.2.3.16} *The inductive form on pp.257–261 at j = 1.* Each use is at Λ by the inductive form at k = 1, through (P) (D1.0(P)(i), IT-1 note §3c(4)):
       - {#MD2.2.3.17} (2.19)–(2.22): T_k(Z_k)'s factorisation and C^{(0)}(Λ), with Z₁ = Λᶜ;
       - {#MD2.2.3.18} (2.25): the subtractions;
       - {#MD2.2.3.19} (2.41)–(2.42): the 𝐁^{(1)} localisation X∩Ω₁ ≠ ∅, X∩(Λᶜ)^∼ ≠ ∅, analyticity on Ũ₁ᶜ and the bound B₀e^{−κd₁(X)};
       - {#MD2.2.3.20} p.262's alternative with d_j(X∖Z_j), which is not used.
    - {#MD2.2.3.21} Pages 271–273, 275 and 278 use only Λ_{k+1}, the new step's own domain; p.274 is item 8 and p.277 item 9; pp.280–281 contain no Λ_j, Z_j or φ_j.
  - {#MD2.2.3.22} *𝐑^{(j)}* (p.260 (2.30)–(2.31): X ⊂ Λ_j^{∼−1}, unions of MR_j-cubes; (2.44), p.263) arise from the 𝐑-operations, so they go with D2.7.
  - {#MD2.2.3.23} *Conclusion (small-field objects).* Every use of Λ_j, j ≤ k, on CRE pp.262–284 needs either a geometric property that Λ has (unions of MR₁- and M₁-cubes, the 2MR₁ distance, filling) or a step-1 object that (P) builds at Λ by CRE's own formulas, under the Λ construction (#MOMGD.22).
    {#MD2.2.3.23-1} So the small-field part of CRE Sect. 3 accepts Λ at every later step.
    {#MD2.2.3.23-2} The large-field objects (D1.0(P)(ii), whose j = 1 factor is RC payment's (d″)(ii)) and the 𝐑-terms are (c)'s.
- {#MD2.2.3.24} *(c) The large-field parts and the 𝐑-operations.* The large-field parts of the later steps (LFR I, LFR II: the bounds of the T-operation and Bałaban's induction pp.384–389, with the geometry of (1.76)), the 𝐑-operations and 𝐑^{(j)}, and p.256's announced "other conditions", which are not listed.
  {#MD2.2.3.24-1} On pp.262–284 those conditions enter only through the properties listed in (b); their content stays with D2.6 (large fields) and D2.7 (the 𝐑-operation).
  {#MD2.2.3.24-2} D2.6's part: WILSON_IT1_D26_CLOSURE_2026_10_24.md §1 (G1)–(G3), §7.2 (the induction pp.384–389), §8.4 (the "other conditions").
  {#MD2.2.3.24-3} Since (6) needs no refinement of Λ_{k+1} (#MD2.2.6.203-1), no further retreat occurs, and the enlarged (1.84) of IT-1 note §3c(4⁗) is needed for the j = 1 factor only.

### (4) Composition of 𝒲_k with the Step-(k+1) Variables, with Gauge Covariance (D2.5) {#MSD2.2.4}

{#MD2.2.4.1} *(a) The covariance property Cov(k) (definition).*
- {#MD2.2.4.2} *Gauge transformations* are G-valued functions u on the sites of the fine lattice.
  {#MD2.2.4.2-1} They act on fine configurations by 𝐔^u(b) = u(b_−)𝐔(b)u(b_+)^{−1}, and on the outer fluctuation fields ω (the A_j among D2.0(3)'s outer variables) by R(u), (R(u)A)(b) = u(b_−)A(b)u(b_−)^{−1}, as in CRE (1.17), p.250, and (2.41)(iii), p.261 ("the variables 𝐉, A are transformed by the adjoint representation").
  {#MD2.2.4.2-2} The outer block variables V_j enter only through the background: CRE p.266, U_{k+1} "is determined by the sequence of domains {Ω_{k+1},Ω_k,…}, and the corresponding sequence of fields {V_{k+1}|Γ_{k+1},V_k|Γ_k,…}".
- {#MD2.2.4.3} *Cov(k).* Every insertion of 𝒲_k is the value at 𝐔 = U_k of a function Y_W(𝐔, ω) of a fine configuration 𝐔 and of ω, both restricted to a domain X_W containing the interval of W. For k ≥ 2 it is the value at (𝐔, 𝐉) = (U_k, J_k) of a function Y_W(𝐔, 𝐉, ω) (#MD2.0.3.56), and the law below reads Y_W(𝐔^u, R(u)𝐉, R(u)ω) = π(u(x_W))Y_W(𝐔, 𝐉, ω)π(u(x′_W))^{−1}; Cov(1) has no 𝐉.
  {#MD2.2.4.3-1} It is analytic on the domain of D(k)(iii), jointly in 𝐔 and ω (D(k)(iii), *Outer fluctuation fields*), and
  {#MD2.2.4.4} Y_W(𝐔^u, R(u)ω) = π(u(x_W)) Y_W(𝐔, ω) π(u(x′_W))^{−1} for every u,
  {#MD2.2.4.5} where x_W is the initial and x′_W the final endpoint of the interval in the orientation of C, as in V4 (c4-11-5).
  {#MD2.2.4.5-1} Under 𝐔^u(b) = u(b_−)𝐔(b)u(b_+)^{−1} a transport along an arc maps the fibre at its final point to the fibre at its initial point, and Y_W transforms the same way.
  {#MD2.2.4.5-2} This is the matrix analogue of CRE (2.27)(i)–(iii) and (2.41)(i)–(iii); for closed words it reduces to CRE's invariance.
- {#MD2.2.4.6} *Consequence.* Every closed word dim(π)^{−1}tr(Y_{W₁}U_{(1)}⋯Y_{W_m}U_{(m)}), with 𝐔-transports U_{(i)} and the leading word as the case m = 0, is invariant under (𝐔, ω) ↦ (𝐔^u, R(u)ω), and for k ≥ 2 under (𝐔, 𝐉, ω) ↦ (𝐔^u, R(u)𝐉, R(u)ω): the conjugations cancel at each endpoint, and tr is conjugation invariant.
- {#MD2.2.4.7} *The scalar parts.* At step 1 the interactions and the local terms are numbers on each labelled term (IT-1 note §4(iii): "φ and e_X are numbers on each labelled term").
  {#MD2.2.4.7-1} D(k) carries the same clause: Q_k(𝔅) and 𝓔_k do not depend on V_k, so they pass through the substitution unchanged.
  {#MD2.2.4.7-2} This is an output requirement on (6) at step k+1: the field-dependent parts go into the insertions, and the reference and Schur scalars go to D2.3.
  {#MD2.2.4.7-3} It is D2.0(3)'s D(k)(v).

{#MD2.2.4.8} *(b) Cov(1) (from V4 and the IT-1 note).*
- {#MD2.2.4.9} The step-1 insertions are Y_W = X_W·(transport of the interval), with X_W = Υ¹_W + a^Λ_W·id (IT-1 note §3a(5) *The matrix coefficient*).
  {#MD2.2.4.9-1} Their extension to 𝐔 = e^{ia′}U₁ is covariant, with a′ ↦ Ad_u a′, on every labelled term (IT-1 note §3e(2)(b): "The formula of each factor is covariant identically in 𝐔"; §3e(4)).
- {#MD2.2.4.10} The coefficient form is V4 (c4-11-5), c_W(U^g; g(o)hg(o)^{−1}) = c_W(U;h).
  {#MD2.2.4.10-1} Burnside (V4 Lemma c5-5-7(a)) turns it into the matrix form: for irreducible π the π(h), h ∈ G, span End(V_π), so tr(Xπ(h)) = 0 for all h forces X = 0.
  {#MD2.2.4.10-2} This holds for every compact G (Burnside, for the irreducible π).
- {#MD2.2.4.11} *The exterior inputs.* On uncovered terms the rows of a group that is not good consult V₀, A_e and a_old (IT-1 note §3d(4)).
  {#MD2.2.4.11-1} V₀ consists of fine links (the unintegrated original field on Ω₁ᶜ), and A_e, a_old are fluctuation fields.
  {#MD2.2.4.11-2} V4's formulas use them through the same operations as the free variables: plaquette actions, the block mean (covariant by RG1 (0.6), V4 sec:c4-11-5), the chart logarithm (conjugation covariant, V4 Lemma global-average(ii)), Haar measure, and the cross term s⟨a, H_{ξ,IJ}A_e⟩ of (c4-11-1).
  {#MD2.2.4.11-3} With U ↦ U^g on links and R_g on fluctuations, the intertwinings of §c4-11-2 (Q_{U^g}R_g = R^{(1)}_gQ_U, h_{U^g} = R_gh_U(R^{(1)}_g)^{−1}) apply term by term.
  {#MD2.2.4.11-4} So Cov(1) holds with ω = (A_e, a_old).
  {#MD2.2.4.11-5} V₀, the original field on Ω₁ᶜ, is the background there and is part of 𝐔.
- {#MD2.2.4.12} *From the IT-1 note.* The quoted sentence of IT-1 note §3e(2)(b), the exterior-input claim of §3d(4) and the printed formula Y_W = X_W·transport of §4 are used here as stated there.

{#MD2.2.4.13} *(c) The substitution identity (from Cov(k) and CRE (3.6)).* For real A_k on the support, let w be the gauge transformation of CRE (3.6), U_k(e^{iB′}V^{(k)})^w = e^{iη𝐇_k(B′)}U_{k+1}.
{#MD2.2.4.13-1} By Cov(k),
{#MD2.2.4.14} F = 𝒲_k(e^{iη𝐇_k(B′)}U_{k+1}, R(w)ω)∘ψ_{k+1}.
- {#MD2.2.4.15} *Factors without ω-dependence:* w drops out, as for the leading word (D2.1(2)).
  {#MD2.2.4.15-1} On covered terms this covers every factor.
- {#MD2.2.4.16} *Factors with ω-dependence:* w enters through R(w)ω.
  {#MD2.2.4.16-1} Its locality is (d).
- {#MD2.2.4.17} *ψ_{k+1}* changes only the A_k on S_{k+1} ⊆ Λ_{k+1}ᶜ (p.269).
  {#MD2.2.4.17-1} These are outer variables at step k+1, so ψ_{k+1} does not affect the dependence on the integrated field A = A_k|_{Λ_{k+1}}.
- {#MD2.2.4.18} *Complex A_k and complex backgrounds.* The identity theorem applies jointly, as in D2.1(2).
  {#MD2.2.4.18-1} The right side is analytic:
  - {#MD2.2.4.19} in the background by D(k)(iii), and in ω by D(k)(iii)'s *Outer fluctuation fields* clause;
  - {#MD2.2.4.20} in w, since w = u_k^{−1}v₁ ((d), #MD2.2.4.32) is analytic in 𝐇_k (RG1 p.266 for u_k, |𝐇_k| < a₁; (d′), Steps 7–8, for v₁, Step 8 for the complex backgrounds, where at a general configuration w_tot = c₀(𝐔)ŵ with the B′-dependent ŵ = û_k^{−1}v̂₁, û_k the u_k of the step at the minimiser at 𝐔's averages, and the B′-independent c₀(𝐔) going to (6)(b7)'s covariant form).
  - {#MD2.2.4.21} R(w)ω stays in the ω-domain.
    {#MD2.2.4.21-1} (R(w)ω)(b) = Ad_{w(b_−)}ω(b), so |R(w)ω − ω| ≤ (e^{2c_G|log w|} − 1)|ω| bond by bond, with c_G := sup_{X∈𝔤^c}‖ad_X‖/(2|X|), the operator norm on 𝔤^c of the Hermitian extension of the Ad-invariant norm; this holds for complex w and ω (for a product w = ∏_je^{Z_j}, Z_j ∈ 𝔤^c, with Σ_j|Z_j| for |log w|; for the conjugated factors e^{Z_j} = Ad_{P_j^{−1}}e^{Z_j′} of (d)'s v₁ this is at most Σ_j‖Ad_{P_j^{−1}}‖|Z_j′| with ‖Ad_P‖ ≤ e^{2c_G|Im Z(P)|}, P = e^{iZ}, equal to 1 at real backgrounds and 1 + o(1) at the complex backgrounds, (d′), Step 8;
    {#MD2.2.4.21-2} at a general complex configuration w is ŵ = û_k^{−1}v̂₁ with û_k the u_k of the step at the minimiser Ū at 𝐔's averages (w_tot = c₀(𝐔)ŵ, (d′), Step 8), the B′-independent outermost factor c₀(𝐔) being absorbed by the covariant form of the ω-clause, (6)(b7) *G^c-valued u*).
    {#MD2.2.4.21-3} So, on the layer of ω_j, dist(R(w)ω, real support) < r^{(k)}_{ω,j} per bond when dist(ω, real support) + (e^{2c_G|log w|} − 1)|ω| < r^{(k)}_{ω,j} (the neighbourhood form of D(k)(iii) with its per-layer radii).
  - {#MD2.2.4.22} At k = 1 the real inputs satisfy |ω| ≤ Cr, C absolute ((6)(e), j = 0), in B-units on the support and r_ω^{(1)} = 1 (D(k)(iii)), so this holds for real ω and |𝐇_1| = O(ε_1).
    {#MD2.2.4.22-1} For k ≥ 2 the bound on |ω| on the support, the radii r^{(k)}_{ω,j} per component and the form |log w_tot| ≤ (C_w + 3dL^{j−k})θ^{k−j−1}h_k of |log w_tot| on older layers are in (6)(e) (the u_k part, C_w) and in (d′), Steps 7–8 (the v₁ part, 3dL^{j−k}).

{#MD2.2.4.23} *(d) w is block-local in 𝐇_k.*
- {#MD2.2.4.24} RG1 p.265 builds w from two transformations.
  {#MD2.2.4.24-1} The first takes U_k′(V′) "into the axial gauge Ax_k(T^{(k)},U_{k+1})" and is "equal to 1 on T^{(k)}".
  {#MD2.2.4.24-2} The second, u_k, changes "the axial gauge into the Landau gauge" and "can be expressed in terms of the configuration 𝐇_k(B′) by the formula (106) in [12] with U_1 = exp iη𝐇_k".
  {#MD2.2.4.24-3} Here [12] is "Averaging operations for lattice gauge theories", CMP 98 (RG1 p.299).
- {#MD2.2.4.25} *The representative.*
  - {#MD2.2.4.26} VAR p.305: "U_0=U_k(V_0), and if we fix a gauge condition for U_k(V′V_0)U_0^{−1}, then it is an analytic function of B=1/i log V′".
    {#MD2.2.4.26-1} RG1 p.265 takes V_0 = V^{(k)}: (2.3) "V^{(k)}=Ū^k_{k+1}=M^k(U_{k+1})", and "U_k(V′V^{(k)})=U_k′(V′)U_{k+1}".
    {#MD2.2.4.26-2} So the reference is U_0 = U_k(V^{(k)}) = U_{k+1}.
  - {#MD2.2.4.27} It does not depend on B′: U_{k+1} is determined by {V_{k+1}|Γ_{k+1}, V_k|Γ_k, …} (CRE p.266), B′ lives on B(Γ_{k+1}) (CRE (3.11)), and Γ_k = Ω_k^{(k)}∖Ω_{k+1}^{(k)} (CRE (2.2) at step k+1) lies outside Ω_{k+1}.
    {#MD2.2.4.27-1} Replacing RG1's single-domain T^{(k)} by 𝔅_k is CRE p.267's transfer ("only the symbols represent different operators, determined by the sequence {Ω_j}").
  - {#MD2.2.4.28} *Which representative.* There are two representatives in play: U^{rep}_k(V_k), at which D(k)'s identity holds with the slot values of the step-k integration, and the step map's representative of U_k(e^{iB′}V^{(k)}) in Ax_k(𝔅_k, U_{k+1}).
    {#MD2.2.4.28-1} They are related by RG1 p.265's first transformation v₁, which depends on B′, because the configuration being gauge-fixed varies with B′.
    {#MD2.2.4.28-2} RG1's reason that v₁ is harmless, "This does not change the expressions in (2.1) because this gauge transformation is equal to 1 on T^{(k)}", covers Bałaban's expressions, not the ω-dependent factors, and (6)(b7)'s rotation covers only B′-independent changes.
    {#MD2.2.4.28-3} So the choice of representative is not free.
    - {#MD2.2.4.29} *The step map's representative.* VAR p.305 (Sect. G, "Analyticity and an Expansion of U_k"; [15] of RG1 is VAR): "We take U_0=U_k(V_0) and we consider the pair of configurations U_k(V′V_0), U_0.
      {#MD2.2.4.29-1} We repeat the whole procedure of Sects.
      {#MD2.2.4.29-2} A–E for this pair.
      {#MD2.2.4.29-3} At first we fix the Landau gauge for the configuration U_k(V′V_0)U_0^{−1}=U_1".
      {#MD2.2.4.29-4} VAR p.307: "We make the gauge transformation inverse to the one applied previously, i.e. we transform the configuration in the Landau gauge back to the axial gauge. … we obtain a gauge field configuration in the axial gauge, which we denote also by U_k(V′V_0).
      {#MD2.2.4.29-5} It is an analytic function of V′ … and for V′ with values in G it coincides with the minimal configuration constructed in the previous sections".
      {#MD2.2.4.29-6} VAR p.305 calls U_k(V) "a (multi-valued) function of the average variables V", so this fixes a branch.
    - {#MD2.2.4.30} Put U^{ax}_k(V_k) := this U_k(V′V₀), with V₀ = V^{(k)} = M^k(U_{k+1}) and U₀ = U_k(V₀) = U_{k+1} (RG1 (2.3)).
      {#MD2.2.4.30-1} Its axial gauge is that of the pair (U_k(V′V₀), U₀), i.e. Ax_k(𝔅_k, U_{k+1}) (REG (1.19) with reference U_{k+1}; multi-domain by CRE p.267's transfer, as above).
      {#MD2.2.4.30-2} REG p.79: "The conditions (1.19) determine uniquely an element in each orbit given by the subgroup (1.14)", so U^{ax}_k is the step map's representative, and nothing is left to choose within Ax_k(𝔅_k, U_{k+1}).
    - {#MD2.2.4.31} D(k)'s representative and the reference U_{k+1} are in the hierarchical mean axial gauge ((d′), Step 1; RG1 p.265 fixes V^{(k)} by "choosing the element of the orbit satisfying the axial gauge conditions 𝐆(V)=0"), and p.265 transforms U_k′(V′) into Ax_k(T^{(k)}, U_{k+1}) "at first", by v₁; at k = 1, V4's U₁ is "in its axial mean gauge" of CRE p.248 (V4 sec:branch-data).
    - {#MD2.2.4.32} *The composite w.* Put w := u_k^{−1}v₁ in (c). By (d′), v₁ is block-local and analytic (U^{rep}_k(V_k) is an explicit analytic gauge transform of e^{iη𝐇_k}U_{k+1}), v₁ = 1 at B′ = 0, and |log v₁(B′)| ≤ 2d(1 + o(1))sup_{B^k(y)}|𝐇_k| ≤ 3d sup_{B^k(y)}|𝐇_k| uniformly in k (d(1 + o(1))sup_{B(y)}|𝐇₁| at k = 1),
      {#MD2.2.4.32-1} with the older-layer form 3dL^{j−k}θ^{k−j−1}h_k and the multi-domain chains.
      {#MD2.2.4.32-2} (e)'s w(s) is built from both factors; (6)(b7)'s rotation absorbs only the B′-independent part.
      {#MD2.2.4.32-3} REG (1.19) with (1.20) telescoped gives v₁ = U_{k+1}(Γ^{(k)})^{−1}Ū^{rep}_k(V_k)(Γ^{(k)}) ((d′), *The gauge of REG (1.19)*).
    - {#MD2.2.4.33} So (c)–(e) hold at D(k)'s representative with w = w_tot = u_k^{−1}v₁ and C_w + 3d in place of C_w (C_w + 2d at k = 1); the frame of the slot values under w_tot is (6)(e)'s *The gauge frame of σ_j*.
  - {#MD2.2.4.34} No change of integration variables is made.
  - {#MD2.2.4.35} At the step map's representative U^{ax}_k, U_k′(V′) is already in Ax_k(T^{(k)}, U_{k+1}), which is REG (1.19) with reference U_{k+1}.
    {#MD2.2.4.35-1} So the first transformation is 1 there; at D(k)'s representative it is v₁, bounded in (d′).
    {#MD2.2.4.35-2} RG1 p.265 prints "U_k′^{u_k^{−1}} = exp iη𝐇_k(B′)", so in CRE (3.6)'s notation w = u_k^{−1}; locality, w₀ = 1, |log w| = |log u_k|, and analyticity are those of u_k.
- {#MD2.2.4.36} *u_k on a block B^k(y) ⊂ Ω_k.* CMP 98 (106), p.33, gives u(x) for x ∈ B^k(y), y ∈ Ω^{(k)}, along the chain x = x_0 ∈ B(x_1), …, x_k = y.
  {#MD2.2.4.36-1} It is a product over j = k−1, …, 0 of the inverse transports R(U_0(Γ^{(j+1)}_{x_{j+1},x}))^{−1} and of the brackets [(average)^{−1}(R̄^j_{0,x_{j+1}}Ū̄^j_1)(Γ_{x_{j+1},x_j})], with the averages (105) over the blocks B(x_{j+1}).
  - {#MD2.2.4.37} *Locality.* Every contour and every average (105) in this product lies in B^k(y), and "the definition of (Ū̄_1^k)_c, c ⊂ Ω^{(k)}, involves only the gauge fields U_{1,b}, U_{0,b} at bonds b ⊂ B^k(c_−) ∪ B^k(c_+)" (p.34).
    {#MD2.2.4.37-1} For an order-j average at a scale-j bond c ⊂ Γ_{x_{j+1},x_j}, j < k, p.31's general remark gives the fine bonds of B^j(c_±) ⊂ B^{j+1}(x_{j+1}) ⊂ B^k(y).
    {#MD2.2.4.37-2} So u_k on B^k(y) depends only on (𝐇_k, U_{k+1}) on the bonds inside B^k(y).
  - {#MD2.2.4.38} *u_k = 1 there when 𝐇_k vanishes on those bonds.* Then U_1 = 1 there and R(U_0)1 = 1.
    {#MD2.2.4.38-1} The one-step average (89), p.31, of V_1 = 1 is 1, since every logarithm in the point averages vanishes and (V̄₁V₀)_c(V̄₀)_c^{−1} = 1.
    {#MD2.2.4.38-2} So Ū̄_1^j = 1 by (90)–(91), every bracket of (106) is 1 by (105), and R(·)1 = 1.
  - {#MD2.2.4.39} *Size.* Proposition 4, p.38: Q_j(U_0, ηA) = (1/i)log Ū̄_1^j is analytic in A, and the display on p.38 gives |(L^jη)^{−1}Q_j(U_0, ηA)| ≤ 2α_1 for |A| < α_1 and small parameters.
    {#MD2.2.4.39-1} A contour Γ_{x_{j+1},x_j} in B(x_{j+1}) has O(L) scale-j bonds.
    {#MD2.2.4.39-2} So the j-th bracket has |log| ≤ O(L)L^jη sup|𝐇_k| = O(1)L^{j+1−k}sup|𝐇_k|, the real transports R(U_0(·))^{−1} preserve |·|, and the sum over j ≤ k−1 is geometric: |log w| = |log u_k| ≤ C_w sup|𝐇_k|, with C_w the constant of this geometric sum.
    {#MD2.2.4.39-3} The same holds at complex 𝐇 with |𝐇| < min(a₁, c₄), by the analyticity of Proposition 4, whose own range is c₄.
  - {#MD2.2.4.40} *Proposition 4's hypotheses.* It needs α₀, α₁ ≤ c₄ for U_0 = U_{k+1}: plaquette regularity of U_{k+1} on every block used, which CRE (3.12) gives on Ω_{k+1}; on Ω_j∖Ω_{j+1}, j ≤ k, U_{k+1} "coincides with a U_j-type configuration, it has the same regularity properties and bounds" (CRE p.275); and a size condition on 𝐇.
    {#MD2.2.4.40-1} At real B′, on Ω_k, |𝐇| ≤ 4B₀e^{16κ_s}|B′| = O(ε_k).
    {#MD2.2.4.40-2} On (f)'s polydisc the size is h_k = O(α_{1,k}) ((6)(e)), so the condition is h_k < min(a₁, c₄), which holds for small couplings.
- {#MD2.2.4.41} *Blocks of the older layers.* On a block B^j(y), y ∈ VAR's Λ_j, j < k (VAR p.277: B^j(Λ_j) = Ω_j∖Ω_{j+1}), the axial conditions are REG (1.15), (1.19) with the chain of j steps, and REG p.81 uses CMP 98's formulas on this multi-domain lattice: "In [3] we have determined the gauge transformation u in terms of the configuration U_1.
  {#MD2.2.4.41-1} We refer the reader especially to the formulas (87), (99), (97), and (105) of that paper" ([3] is CMP 98, REG p.102).
  {#MD2.2.4.41-2} For bonds with both endpoints in Λ_j the left side of REG (1.30) "is equal to (Ū̄_1^j)_b by (92) of [3]"; the bonds that cross ∂Λ_j are treated by (97), (99), (87) of [3].
  {#MD2.2.4.41-3} CMP 98 (97), p.32, is v_j(x) = (R_{0,x}U_1)‾(R̄_{0,x}Ū̄_1)‾⋯(R̄^{j−1}_{0,x}Ū̄_1^{j−1})‾, x ∈ Ω^{(j)}, the product of the averages of orders 0, …, j−1, and (99) is (R_{0,x}U_1)‾^{(j)} = v_j(x).
  {#MD2.2.4.41-4} REG states the multi-domain statement ("The rest of this paper is devoted to a proof of this statement", p.81) as Bałaban's result.
  - {#MD2.2.4.42} *u on B^j(y).* On B^j(y), y ∈ VAR's Λ_j, u is CMP 98's (106) with the chain of j steps, the product (97) truncated at order j.
    {#MD2.2.4.42-1} This gives the three properties of the k-blocks with k replaced by j: locality in B^j(y) (each factor of (97) is an average over blocks inside B^j(y)), u = 1 where 𝐇 vanishes on the block, and the size bound with L^{i+1−j} per order i < j.
    {#MD2.2.4.42-3} The formulas (87), (99), (97), and (105) of CMP 98 that REG p.81 cites (#MD2.2.4.41-1) give u = v_j^{−1} on Λ_j with v_j the j-fold product (97) of the averages (105), and (106) is CMP 98's rewriting of the same by (101)–(104).
    {#MD2.2.4.42-4} REG (1.29), "(R̄_0u)^j(y)=1 for y∈Λ_j", is the order-j analogue of CMP 98 (86).
    {#MD2.2.4.42-5} The bonds crossing ∂Λ_j are case (B) of D2.1(4) and go to D2.6 with it.
- {#MD2.2.4.43} *Result.* On each block B^j(y), j ≤ k, u_k^{−1} is a function of (𝐇_k, U_{k+1}) on the bonds inside the block, analytic in 𝐇_k for |𝐇_k| < a₁ (RG1 p.266), with |log u_k| ≤ C_w sup|𝐇_k| for |𝐇_k| < min(a₁, c₄), and equal to 1 when 𝐇_k vanishes on the block.
  {#MD2.2.4.43-1} By (d′), v₁ is block-local, analytic on (e)–(f)'s polydisc, and equal to 1 when 𝐇_k vanishes on the block (block locality and v₁(0) = 1), with |log v₁| ≤ 3d sup|𝐇_k|; so w_tot = u_k^{−1}v₁ is a function W_y of (𝐇_k, U_{k+1}) on the bonds inside the block, with |log W_y| ≤ (C_w + 3d)sup|𝐇_k| and W_y = 1 when 𝐇_k vanishes on the block (w₀ = 1).

{#MOMGD.31} *(d′) The bound on v₁.* D(k)'s identity holds at its representative U^{rep}_k(V_k), while the step map evaluates at Ax_k(𝔅_k, U_{k+1}); the two differ by RG1 p.265's first transformation v₁, which depends on B′ through U^{rep}_k and enters only the ω-dependent factors (uncovered terms).
{#MOMGD.31-1} *The output convention.* The step map hands D(k+1) the representative U^{rep}_{k+1}(W) := U^{rep}_k(V^{(k)}(W)), and U_{k+1} denotes this configuration: RG1 (2.3), U_k(V′V^{(k)}) = U_k′(V′)U_{k+1}, at V′ = 1 (#MD2.2.4.26-2).
- {#MOMGD.32} *At the next step.* At step k+2 the change recurs with B″: (6)(b7)'s pointwise rotation covers only changes independent of the integration variable, and by Cov(k+1) the insertions become functions of R(v₁(B″))^{−1}σ; (e)'s joint expansion and (6)(e)'s radius propagation interpolate R(w_tot(s))σ with the composite w_tot = u_k^{−1}v₁ (CRE (3.6)'s w), which needs v₁'s block locality, value at B′ = 0, analyticity, and size below.
- {#MOMGD.33} *The gauge of REG (1.19) ((2)(vii)).* The gauge transformation r into (1.19) relative to U₀ is fixed blockwise by the recursion r(x_n) = Ū_0^n(Γ)^{−1}r(x_{n+1})Ū^n(Γ) down each chain from r(x_k) = 1.
  {#MOMGD.33-2} *CMP 98's solution of the axial conditions.* CMP 98 poses the axial conditions (64), (66), (67) for U′ relative to a fixed U₀ (R₀, R̄₀^j the transports of U₀ and of its averages), with the relative averages Ũ′^j = (overline{U′U₀})^j(Ū₀^j)^{−1} ((65), (68), (69)), and solves them for U′ = U₁^u: (76) (R̄^j_{0,x_{j+1}}u)(x_j) = u(x_{j+1})(R̄^j_{0,x_{j+1}}Ũ₁^j)(Γ_{x_{j+1},x_j}) for x_j ∈ B(x_{j+1}), so down each chain x = x₀ ∈ B(x₁) ⊂ … ⊂ B^k(x_k) the value u(x) is u(x_k) times the ordered product, over the levels j = k−1, …, 0 from the left,
  {#MOMGD.33-3} of the level-j relative average Ũ₁^j transported along the block path Γ_{x_{j+1},x_j} (at most d(L−1) level-j block bonds) and conjugated by the real transports R̄₀ of U₀'s averages, with an overall R(U₀(Γ^{(k)}_{y,x}))^{−1} on the product ((77), (101)).
  {#MOMGD.33-4} Telescoped with (1.20), REG (1.19) says Ū^n(Γ_{x_{n+1},x_n}) = Ū₀^n(Γ_{x_{n+1},x_n}) at every level of every chain: the hierarchical transports agree.
  {#MOMGD.33-5} Hence, with U₀ = U_{k+1}, U′U₀ = U^{rep}_k(V_k) D(k)'s representative and u = v₁ with v₁ = 1 at the top centres (RG1 p.265), v₁(x) = U_{k+1}(Γ^{(k)}_{y,x})^{−1}Ū^{rep}_k(V_k)(Γ^{(k)}_{y,x}), the mismatch of the hierarchical transports of D(k)'s representative and of U_{k+1}.
- {#MOMGD.33-8} *Block locality.* v₁ on B^k(y) depends on the configuration on B^k(y) only: both hierarchical transports use the bonds of B^k(y), since the average at a level-j bond c uses B^j(c₋) ∪ B^j(c₊) (CMP 98 p.34 l.2, quoted at #MD2.2.4.37).
- {#MOMGD.33-9} *The value at B′ = 0.* v₁ = 1 at B′ = 0, since U^{rep}_k(V^{(k)}) = U_{k+1} by the output convention.
- {#MOMGD.33-10} *Analyticity.* v₁ is analytic in B′ where the averages Ū^n are: D(k)'s representative is an explicit analytic gauge transform of e^{iη𝐇_k}U_{k+1} (Step 7); VAR p.305 gives analyticity in a fixed gauge only.
- {#MOMGD.33-11} *Size at k = 1.* U^{rep}_1 = V4's U₁(e^{iB′}V^{(1)}) in CRE p.248's axial mean gauge (V4 sec:branch-data, (B1); CRE p.247: "U(y,x) are the variables introduced by (0.11) [I]"): M({U^{rep}_1(Γ)}_{Γ∈𝐆(y,x)}) = 1 for the mean contour variables of RG1 (0.10)–(0.11), while the step's Ax₁(𝔅₁, U₂) is REG's single-contour (1.19) (RG1 p.265 writes Ax_k(T^{(k)}, U_{k+1}) in REG p.79's notation; VAR p.280 cites "(1.19) in [6]"), so v₁(x) = U₂(Γ_{y,x})^{−1}U^{rep}_1(Γ_{y,x}) with Γ_{y,x} the canonical path inside B(y), and v₁(0) = 1 (U^{rep}_1 = U₂ at B′ = 0).
  {#MOMGD.33-12} Both identifications are printed: CRE p.247 l.8 for the mean variables, and RG1 p.265 l.37 with VAR p.280 l.44–45 ("see the definition (1.19) in [6]") for Ax_k.
  {#MOMGD.33-13} Exact form: with h_Γ := U^{rep}_1(Γ_{y,x})U^{rep}_1(Γ)^{−1} the holonomy of the closed contour Γ_{y,x} ∪ (−Γ) ⊂ B(y) based at y (at most d(L−1) fine bonds: RG1 p.252 defines 𝐆(y,x) as the shortest monotone contours, |n_μ| ≤ (L−1)/2), the mean condition M({h_Γ^{−1}U^{rep}_1(Γ_{y,x})}_Γ) = 1 and RG1 (0.5)–(0.6) give U^{rep}_1(Γ_{y,x}) = M({h_Γ}_{Γ∈𝐆(y,x)}) exactly (in logarithms: log U^{rep}_1(Γ_{y,x}) is the mean of the log h_Γ up to BCH corrections of relative size o(1), every U^{rep}_1(Γ) being O(L²ε₁) from 1 in the mean gauge).
  {#MOMGD.33-14} The holonomy is gauge-covariant: with g := v₁^{−1}u₁, so that U^{rep}_1 = (e^{iη𝐇₁}U₂)^{g} (Step 4 at k = 1) and g(y) = u₁(y) (v₁(y) = 1), h_Γ(U^{rep}_1) = Ad_{g(y)}h_Γ(e^{iη𝐇₁}U₂) and ‖Ad_{g(y)}‖ ≤ e^{2c_G|log u₁(y)|} = 1 + o(1); and h_Γ(e^{iη𝐇₁}U₂)h_Γ(U₂)^{−1} = ∏_b exp(i Ad_{T_b}η𝐇₁(b)) with T_b real partial transports of U₂, so |log(h_Γ(e^{iη𝐇₁}U₂)h_Γ(U₂)^{−1})| ≤ d(L−1)η sup_{B(y)}|𝐇₁|(1 + o(1)) < d sup_{B(y)}|𝐇₁|(1 + o(1)) (Lη = 1 at k = 1);
  {#MOMGD.33-14-1} the term (Ad_{g(y)} − 1)log h_Γ(U₂) is o(1)sup|𝐇₁|.
  {#MOMGD.33-15} So v₁(x) = U₂(Γ_{y,x})^{−1}M({Ad_{g(y)}h_Γ(e^{iη𝐇₁}U₂)}_{Γ∈𝐆(y,x)}), analytic in 𝐇₁ (M is analytic, RG1 p.253; u₁ is analytic for |𝐇₁| < a₁, RG1 p.266), depending on 𝐇₁ on B(y) only, hence evaluable at 𝐇(s,tB′) on (e)–(f)'s polydisc as u₁ is, with |log v₁(B′)| ≤ d(1 + o(1))sup_{B(y)}|𝐇₁(B′)| ≤ 2d sup_{B(y)}|𝐇₁(B′)|,
  {#MOMGD.33-15-1} with 𝐇₁'s localisation and decay, the inputs (c) and (6)(e) use for u₁ (sup_{B(y)}|𝐇₁| ≤ h₁, #MD2.2.6.156, #MD2.2.6.157); at k = 1, (c)–(e) hold with w_tot = u₁^{−1}v₁ and C_w + 2d in place of C_w.
- {#MOMGD.33-16} *Size at k ≥ 2.* Steps 1–7 are stated at G-valued U_{k+1}; Step 8 treats the complex backgrounds.
  {#MOMGD.33-17} Notation: a chain x = x₀ ∈ B(x₁) ⊂ … ⊂ B^k(x_k), x_k = y, x_n ∈ T^{(n)}, with Γ_n := Γ_{x_{n+1},x_n} ⊂ T^{(n)} REG's path, one of RG1 p.252's shortest monotone contours 𝐆(x_{n+1},x_n); for a configuration U on T, U^n := M^n(U) on T^{(n)}, and the hierarchical transport U(Γ^{(k)}_{y,x}) := U^{k−1}(Γ_{k−1})U^{k−2}(Γ_{k−2})⋯U^0(Γ_0); α₀ the curvature of U_{k+1} on T, |U_{k+1}(∂p) − 1| < α₀η², η = L^{−k} ((6)(e)'s α_{0,k+1}); α₁ := sup_{B^k(y)}|𝐇_k(B′)|.
  - {#MOMGD.33-18} *Step 1, D(k)'s frame.* With the output convention, M^k(U^{rep}_k(V)) = V (the δ-function, CRE (1.11) at k = 1; M(V^{(k)}(W)) = W).
    {#MOMGD.33-19} Claim: for every k and every V in U^{rep}_k's domain, M^n(U^{rep}_k(V))(x_{n+1}, x_n) = 1 for n = 0, …, k−1, x_{n+1} ∈ T^{(n+1)} (on Γ_{n+1} = Ω_{n+1}^{(n+1)} in the multi-domain construction, CRE (3.10) and p.248's "y ∈ Ω₁^{(1)}"; T^{(n+1)} in RG1's single-domain construction), x_n ∈ B(x_{n+1})∖{x_{n+1}}, in the mean variables of RG1 (0.11): the hierarchical mean axial gauge.
    {#MOMGD.33-20} By induction on k.
    {#MOMGD.33-21} At k = 1 it is CRE p.248's "axial gauge conditions U(y,x) = 1 for x ∈ B(y), x ≠ y" for V4's U₁.
    {#MOMGD.33-22} At k+1 the levels n ≤ k−1 are the claim for U^{rep}_k at V = V^{(k)}(W), and the level n = k is M^k(U^{rep}_k(V^{(k)})) = V^{(k)} with V^{(k)}(y,x) = 1 for y ∈ T^{(k+1)}, x ∈ B(y): RG1 p.265 takes V^{(k)} as "the element of the orbit satisfying the axial gauge conditions 𝐆(V) = 0", where 𝐆(V) = Σ_{y∈T^{(k+1)}}Σ_{x∈B(y),x≠y}[1 − Re tr V(y,x)] ((0.19), (2.1)), each term ≥ 0 for G-valued V with equality iff V(y,x) = 1;
    {#MOMGD.33-23} CRE (3.10) (p.266) prints the condition outright, V^{(k)} being the minimum over "V_k: V̄_k = V_{k+1} on Γ_{k+1} = Ω_{k+1}^{(k+1)}, V_k(y,x) = 1 for y ∈ Γ_{k+1}, x ∈ B(y)", "given by V^{(k)} = M^k(U_{k+1})".
    {#MOMGD.33-24} The frame is consistent and unique in each orbit of REG (1.14)'s subgroup (u = 1 on T^{(k)}): by RG1 (0.6), M^n(U^u)(x_{n+1}, x_n) = u(x_{n+1})M^n(U)(x_{n+1}, x_n)u(x_n)^{−1}, so the conditions are solved by u(x_n) = u(x_{n+1})M^n(U)(x_{n+1}, x_n) down each chain from u(x_k) = 1, and only so.
    {#MOMGD.33-25} In particular the reference U_{k+1} = U^{rep}_k(V^{(k)}) is in this frame, which fixes the gauge of the reference.
  - {#MOMGD.33-26} *Step 2, transports as means of holonomies.* For a T^{(n)}-configuration U^{rep,n} with U^{rep,n}(x_{n+1}, x_n) = 1 and h_Γ := U^{rep,n}(Γ_n)U^{rep,n}(Γ)^{−1}, Γ ∈ 𝐆(x_{n+1}, x_n) (the holonomy of the closed contour Γ_n ∪ (−Γ) ⊂ B(x_{n+1}) based at x_{n+1}, of at most d(L−1) level-n bonds), 1 = M({U^{rep,n}(Γ)}_Γ) = M({h_Γ^{−1}U^{rep,n}(Γ_n)}_Γ) = M({h_Γ^{−1}}_Γ)U^{rep,n}(Γ_n) by RG1 (0.6), so U^{rep,n}(Γ_n) = M({h_Γ}_Γ) by (0.5): the k = 1 identity at every level, for U^{rep,n} = M^n(U^{rep}_k(V_k)) and for U^n_{k+1} = M^n(U_{k+1}) alike (Step 1).
  - {#MOMGD.33-27} *Step 3, the level mismatches.* With Δ_n := U^n_{k+1}(Γ_n)^{−1}U^{rep,n}(Γ_n) and P_n := U^{n−1}_{k+1}(Γ_{n−1})⋯U^0_{k+1}(Γ_0) (P₀ = 1), v₁(x) = U_{k+1}(Γ^{(k)}_{y,x})^{−1}Ū^{rep}_k(V_k)(Γ^{(k)}_{y,x}) = ∏_{n=k−1}^{0}Ad_{P_n^{−1}}Δ_n (n = k−1 leftmost): a product of exponentials conjugated by the real partial transports of U_{k+1}, so in (c)'s convention (#MD2.2.4.21-1) |log v₁(x)| = Σ_{n<k}|log Δ_n|.
  - {#MOMGD.33-28} *Step 4, the Landau representation.* By (d)'s two transformations (#MD2.2.4.24, #MD2.2.4.35-2), U^{rep}_k(V_k)^{v₁} = (e^{iη𝐇_k}U_{k+1})^{u_k}, so U^{rep}_k(V_k) = Ṿ^{g} with Ṿ := e^{iη𝐇_k(B′)}U_{k+1} and g := v₁^{−1}u_k pointwise (the order is immaterial below).
    {#MOMGD.33-29} The averages are gauge-covariant (the loop in (0.12)'s exponent is based at c₋, so M(U^u) = M(U)^{u} with u restricted to T^{(1)}; CMP 98 (93) for the relative averages), hence h_Γ(U^{rep,n}) = Ad_{g(x_{n+1})}h_Γ(Ṿ^n) for loops based at x_{n+1}, and Δ_n = M({h_Γ(U^n_{k+1})}_Γ)^{−1}M({Ad_{g(x_{n+1})}h_Γ(Ṿ^n)}_Γ).
  - {#MOMGD.33-30} *Step 5, the bound on Δ_n.* The holonomies are near 1: a closed contour of ℓ ≤ d(L−1) level-n bonds bounds at most ℓ² level-n plaquettes, and |U^n_{k+1}(∂p) − 1| < 2α₀(L^nη)² (CMP 98 Proposition 2, (54), in the scaled form of p.37 l.7–8; RG1 p.254 l.7 transfers CMP 98's results to the average (0.12)), so |log h_Γ(U^n_{k+1})| ≤ 2d²L²α₀L^{2(n−k)}(1 + o(1)) =: q_n.
    {#MOMGD.33-31} M is analytic near 1 with M({e^{iZ_Γ}}_Γ) = exp(i·avg_ΓZ_Γ + O(sup_Γ|Z_Γ|²)) ((0.10) solved to second order), so |log Δ_n| ≤ (1 + o(1))sup_Γ|log(h_Γ(U^n_{k+1})^{−1}Ad_{g(x_{n+1})}h_Γ(Ṿ^n))| ≤ (1 + o(1))[A_n + (e^{2c_G|log g(x_{n+1})|} − 1)(q_n + A_n)], A_n := sup_Γ|log(h_Γ(U^n_{k+1})^{−1}h_Γ(Ṿ^n))| ((c)'s pattern |R(w)ω − ω| ≤ (e^{2c_G|log w|} − 1)|ω|, #MD2.2.4.21-1).
    {#MOMGD.33-32} (α) A_n. Ṿ^n = Ũ₁^nU^n_{k+1} with Ũ₁^n := Ṿ^n(U^n_{k+1})^{−1} the relative average of CMP 98 (68)–(69) at U₁ = e^{iη𝐇_k}, U₀ = U_{k+1}, and (97) gives Ũ₁^n = (Ū̄₁^n)^{v_n} in the relative action, i.e. Ṿ^n = (Ū̄₁^nU^n_{k+1})^{v_n} in the ordinary one, v_n(x) the product of the n means of transported Ū̄₁^j, j < n, each ≤ d(L−1)L^jηα₁(1 + o(1)) (a block path of at most d(L−1)/2 level-j bonds, each < 2α₁L^jη by (131)), so |log v_n(x)| ≤ d(L^n − 1)ηα₁(1 + o(1)) ≤ dL^{n−k}α₁(1 + o(1)).
    {#MOMGD.33-33} Then h_Γ(Ṿ^n)h_Γ(U^n_{k+1})^{−1} = Ad_{v_n(x_{n+1})}[h_Γ(Ū̄₁^nU^n_{k+1})h_Γ(U^n_{k+1})^{−1}]·[Ad_{v_n(x_{n+1})}h_Γ(U^n_{k+1})·h_Γ(U^n_{k+1})^{−1}].
    {#MOMGD.33-34} The first bracket is ∏_b exp(i Ad_{T_b}log(Ū̄₁^n)_b) over the bonds b of the loop, T_b the real partial transports of U^n_{k+1} from x_{n+1}, with |log(Ū̄₁^n)_b| = |Q_n(U₀, η𝐇_k, b)| < 2α₁L^nη for 1 ≤ n < k by CMP 98 (131) (p.38; Proposition 4's dependence set B^n(b₋) ∪ B^n(b₊) ⊂ B^k(y)) and = η|𝐇_k(b)| ≤ ηα₁ at n = 0; so its logarithm is ≤ 2d(L−1)L^nηα₁(1 + o(1)) for n ≥ 1 and ≤ d(L−1)ηα₁(1 + o(1)) for n = 0.
    {#MOMGD.33-35} The second bracket is ≤ (e^{2c_G|log v_n(x_{n+1})|} − 1)q_n = o(1)L^{n−k}α₁.
    {#MOMGD.33-36} Hence A_n ≤ 2d(L−1)L^nηα₁(1 + o(1)) + o(1)L^{n−k}α₁.
    {#MOMGD.33-37} (β) The conjugation by g(x_{n+1}) = v₁(x_{n+1})^{−1}u_k(x_{n+1}): |log g(x_{n+1})| ≤ |log u_k(x_{n+1})| + |log v₁(x_{n+1})| ≤ (C_w + 2d)(1 + o(1))α₁, by #MD2.2.4.39-2 for u_k and, for v₁ at the level-(n+1) point x_{n+1}, by this derivation applied to the levels m ≥ n+1 of the chain (downward from v₁(x_k) = 1, where g(x_k) = u_k(y) as at k = 1); so the second term of the bracket is ≤ 2c_G(C_w + 2d)α₁(1 + o(1))(q_n + A_n) = o(1)L^{n−k}α₁, as L²α₀, Lα₁, and (C_w + 2d)α₁ are small.
  - {#MOMGD.33-38} *Step 6, the sum.* |log v₁(x)| = Σ_{n<k}|log Δ_n| ≤ (1 + o(1))[d(L−1)η + Σ_{n=1}^{k−1}2d(L−1)L^nη]α₁ + o(1)α₁Σ_{n<k}L^{n−k} = (1 + o(1))[d(L−1)L^{−k} + 2d(1 − L^{1−k})]α₁ + o(1)α₁ ≤ 2d(1 + o(1))sup_{B^k(y)}|𝐇_k(B′)| ≤ 3d sup_{B^k(y)}|𝐇_k(B′)|, uniformly in k (at k = 1 the sum is the single term d(L−1)L^{−1}α₁, the bound of *Size at k = 1*);
    {#MOMGD.33-38-1} the o(1) are O(L²α₀ + c_G(C_w + 2d)(dLα₁ + d²L²α₀)) per level, none summed over k (in (c)'s convention |log v₁| is the sum Σ_n|log Δ_n| itself, Step 3; the principal logarithm, not used, differs from it by O((Σ_n|log Δ_n|)²)).
  - {#MOMGD.33-39} *Step 7, analyticity, the value at 0, the layers.* g is the hierarchical mean gauge fixing of Ṿ with the top values g(x_k) = u_k(x_k): g(x_n) = g(x_{n+1})Ṿ^n(x_{n+1}, x_n) down each chain (Step 1's recursion), an explicit composition of RG1's averages (0.12), means (0.10)–(0.11), and products applied to e^{iη𝐇_k}U_{k+1}, hence analytic in 𝐇_k where the averages are (CMP 98 Proposition 4, for |𝐇_k| below its c₄(d, L); M analytic on its domain near 1, RG1 p.253; u_k analytic for |𝐇_k| < a₁, p.266) and depending on 𝐇_k on B^k(y) only;
    {#MOMGD.33-40} the thresholds, these three and the smallness of L²α₀, dLα₁, and c_G(C_w + 2d)α₁ behind Steps 5–6's o(1), are met on (e)–(f)'s polydisc for g_K small, where α₁ ≤ h_k ((6)(e), #MD2.2.6.156, #MD2.2.6.157) and α₀ = α_{0,k+1} are small (#MD2.4.11.3: α_{1,k} → 0 with g_K); so U^{rep}_k(V_k) = Ṿ^g, its hierarchical transports, and v₁ are analytic in 𝐇_k, hence in B′ on (e)–(f)'s polydisc as u_k is. v₁(0) = 1 since U^{rep}_k(V^{(k)}) = U_{k+1} (#MOMGD.31-1).
    {#MOMGD.33-41} On a layer of 𝔅_k with top level j < k (CRE p.267's transfer, as for u_k in (d)): the chains have the levels n < j, each of whose mean conditions was imposed at step n on Γ_{n+1} = Ω_{n+1}^{(n+1)}, which contains the layer's (n+1)-block centres (CRE (3.10)), so Steps 1–6 run with j for k after the rescaling e^{iη𝐇_k} = e^{iη_j(L^{j−k}𝐇_k)}, η_j := L^{−j} (Propositions 2 and 4 at the scale L^{−j}, with L^{j−k}sup_{B^j(y)}|𝐇_k| for α₁), U_{k+1}'s regularity at the scale L^{−j} there (CRE p.276's older-layer regularity) in place of α₀η²,
    {#MOMGD.33-42} and give |log v₁| ≤ 2d(1 + o(1))L^{j−k}sup_{B^j(y)}|𝐇_k| ≤ 3dL^{j−k}sup_{B^j(y)}|𝐇_k|: the older-layer form of (6)(e) holds for v₁ with 3dL^{j−k} ≤ 3d in place of C_w, from the same bound on 𝐇_k over the layer-j blocks that (6)(e) uses for u_k.
  - {#MOMGD.33-44} *Step 8, complex backgrounds.* Notation: for P = e^{iZ}, Z = X + iY with X, Y ∈ 𝔤, Z is the phase and Y = Im Z its imaginary part.
    {#MOMGD.33-45} The complex backgrounds are 𝐔 = e^{iηa′}U_{k+1} with a′ 𝔤^c-valued (D2.1(4)'s parametrisation, #MD2.1.2.4), in D(k+1)(iii)'s domain (#MD2.0.3.53, #MD2.0.3.54 with k+1 for k): |ηA′| < α_{1,n}L^{−n} per fine bond on Ω_n∖Ω_{n+1}, real and imaginary parts alike, so |Im Z(𝐔(b))| ≤ ιη per fine bond with ι ≤ α_{1,n} on the layer n in units of the layer's scale L^{−n} (#MD2.4.11.3 states the same radius as Lα_{1,k} in η_{k+1}-units on Ω_k and as α_{1,n}L^{k−n} in η_k-units on the older layers);
    {#MOMGD.33-46} max_nα_{1,n} is small for g_K small, by g_n ≤ (1 + β₀)g_K (#MD2.1.4.31, #MD2.2.6.196-3) and the monotonicity of g ↦ gC₁(log g^{−2})^{q₁} for small g; #MD2.1.4.35's 4c_π′M‖a′‖_∞ ≤ 1 is a further condition on a′, not the radius.
    - {#MOMGD.33-47} *The two families.* (I) The frame family: the configurations U^{rep}_k(V) at complexified level-k data V, the continuation of D(k)'s representative in the data that define it.
      {#MOMGD.33-48} It contains the step-(k−1) map's outputs at complexified data, U_{k+1}(W_c) = U^{rep}_k(V^{(k)}(W_c)), which are the backgrounds the step map itself produces (at step k+1 with complex B″ the step-k reference is U^{rep}_k(V^{(k)}) at V^{(k)} = M^k(𝐔_{k+2}), complexified data; #MD2.2.6.186's reference minimiser at complex data is this object), and it contains the minimisers Ū below.
      {#MOMGD.33-49} On this family Step 1's mean conditions hold by the identity theorem (both sides analytic in V, equal at real V), M^k(U^{rep}_k(V)) = V, and Steps 2–7 run as below with v₁(0) = 1.
      {#MOMGD.33-50} (II) The general configurations of the domain, e^{iηa′}U_{k+1} with arbitrary a′: not in the frame and not minimisers in general (example: U_{k+1} = 1, a′ = iιH on the e₁-bonds with H in a Cartan subalgebra, flat; the hierarchical mean gauge fixing of 𝐔 is g₀(x) = e^{−ιη(x−y)₁H} ≠ 1).
      {#MOMGD.33-51} There v₁(𝐔, B′) = c₀(𝐔)v̂₁(𝐔, B′): with Ū := U^{rep}_k(M^k(𝐔)) the minimiser at 𝐔's own averages (in family (I), the data M^k(𝐔) being complex), v̂₁ := Ū(Γ^{(k)}_{y,x})^{−1}Ū^{rep}_k(V_k)(Γ^{(k)}_{y,x}) is family (I)'s v₁ at Ū (M^k(Ū) = M^k(𝐔) by Step 1's M^k(U^{rep}_k(V)) = V, so U^{rep}_k(V_k) at V_k = e^{iB′}M^k(𝐔) is the same object at 𝐔 and at Ū), and c₀(𝐔) := 𝐔(Γ^{(k)}_{y,x})^{−1}Ū(Γ^{(k)}_{y,x}) is the mismatch of the hierarchical transports of 𝐔 and of Ū: a gauge transformation with c₀ = 1 on T^{(k)} (it fixes the block variables, RG1 (0.6)), independent of B′,
      {#MOMGD.33-52} analytic in 𝐔 (𝐔 ↦ M^k(𝐔) by RG1's averages on G^c, or by CMP 98 Proposition 4 with (127)–(131) over the real base; the minimiser in its data by VAR p.307 on the domain (172), with ε₁ enlarged as at #MD2.2.6.186; the passage to the mean frame by Step 7; the transports are analytic), equal to 1 on family (I) (there Ū = U^{rep}_k(M^k(U^{rep}_k(V))) = U^{rep}_k(V) = 𝐔),
      {#MOMGD.33-52-1} G-valued at real 𝐔 (M^k(𝐔) is then G-valued, RG1 (0.10)–(0.12) at G-valued input, and Ū a real minimiser), and equal to h when 𝐔 = Ū^h with h = 1 on T^{(k)} (𝐔(Γ) = Ū(Γ)h(x)^{−1}), that is g₀(𝐔)^{−1} for the hierarchical mean gauge fixing g₀ of such a 𝐔.
      {#MOMGD.33-53} Its size: |log c₀| = O(dι), since c₀ = [𝐔(Γ^{(k)})^{−1}U_{k+1}(Γ^{(k)})]·v₁(U_{k+1}; B′₀) with B′₀ := (1/i)log(M^k(𝐔)M^k(U_{k+1})^{−1}) the complex datum of Ū over the real reference, the first factor ≤ 2dι(1 + o(1)) by (ii)'s telescoping below and the second ≤ 3d sup_{B^k(y)}|𝐇_k(B′₀)| = O(dι) by Steps 1–7 at the real reference with the complex datum B′₀ (|B′₀| = O(dι), *The reference Ū* below).
      {#MOMGD.33-54} The step at a general 𝐔 is the c₀-conjugate of the step at Ū: its words are evaluated at Ax_k(𝔅_k, 𝐔) = U^{rep}_k(V_k)^{v₁} = (U^{rep}_k(V_k)^{v̂₁})^{c₀} (gauge action U^u(b) = u(b₋)U(b)u(b₊)^{−1}, so (U^b)^a = U^{ab}), which depends on 𝐔 through its block data and its hierarchical transports only, both shared with Ū^{c₀} (c₀ = 1 on T^{(k)}; Ū^{c₀}(Γ^{(k)}) = Ū(Γ^{(k)})c₀(x)^{−1} = 𝐔(Γ^{(k)})).
      {#MOMGD.33-54-1} So the Landau gauge at 𝐔 is posed relative to the minimiser Ū^{c₀}: VAR's base is a minimiser, and the Landau condition is covariant under the simultaneous transformation of the configuration and of the base (REG (1.18), PBG (3.33)–(3.34) as used at #MD2.2.6.186, continued to G^c-valued transformations by analyticity).
      {#MOMGD.33-55} Hence 𝐇_k(𝐔, B′) = Ad_{c₀}𝐇̂_k(B′) and u_k(𝐔, B′) = c₀û_k(B′)c₀^{−1}, with 𝐇̂_k and û_k those of the step at Ū ((e^{iη𝐇̂_k}Ū)^{c₀} = e^{iηAd_{c₀}𝐇̂_k}Ū^{c₀} and (e^{iη𝐇̂_k}Ū)^{c₀û_k} = ((e^{iη𝐇̂_k}Ū)^{c₀})^{c₀û_kc₀^{−1}}), 𝐇̂_k(0) = 0, and the B′-independent factor stands outermost in the composite: w_tot = u_k^{−1}v₁ = c₀û_k^{−1}c₀^{−1}·c₀v̂₁ = c₀ŵ with ŵ := û_k^{−1}v̂₁, family (I)'s w_tot at Ū.
      {#MOMGD.33-56} So at a general 𝐔 the change of representative from D(k)'s U^{rep}_k(V_k) to the step's Ax_k(𝔅_k, 𝐔) is the B′-dependent v̂₁, bounded below, followed by the B′-independent c₀(𝐔).
    - {#MOMGD.33-57} *c₀ is absorbed by (6)(b7) in its covariant form.* (6)(b7) absorbs c₀ at the real points of the polydisc (there c₀ is G-valued and B′-independent, and the step's words at the two representatives differ by the rotation R(c₀)^{−1} of the slot values, which preserves the slot polydisc).
      {#MOMGD.33-58} At a complex 𝐔 the same covariance holds with the G^c-valued c₀ ((6)(b7), *G^c-valued u*: Cov(k) for G^c-valued u by analytic continuation, closed words being analytic in u and G a totally real uniqueness set in G^c), and the slot values are rotated by the G^c-valued R(c₀(𝐔))^{−1}, which does not preserve the polydisc around the real support (the continuation needs c₀ inside the connected domain of analyticity in u, which |log c₀| = O(dι) gives; the domain is rotated, not shrunk).
      {#MOMGD.33-59} So D(k+1)(iii)'s ω-clause at a complex configuration 𝐔 is stated in the frame of 𝐔's minimiser: Ax_k at 𝐔 is Ax_k at Ū transformed by c₀, so by Cov ((6)(b7)) word(Ū^{c₀}, R(c₀)𝐉, σ) = word(Ū, 𝐉, R(c₀)^{−1}σ), the plain clause holds at Ū (family (I)), and the clause at 𝐔 holds for the slot values σ with R(c₀(𝐔))^{−1}σ in the polydisc around the real support (D(k)(iii), *The ω-clause at complex configurations*).
      {#MOMGD.33-60} At real 𝐔 this is the plain clause (R(c₀) real orthogonal); on family (I) it is the plain clause (c₀ = 1); it is the analytic continuation of the real clause, with σ̂ := R(c₀(𝐔))^{−1}σ as the analytic coordinate in #MD2.1.2.4's identity theorem, jointly with a′ (the words at 𝐔 are the words at Ū in σ̂ composed with ŵ, analytic in (a′, σ̂); (a′, σ̂) ↦ (a′, R(c₀(a′))σ̂) is biholomorphic and maps real points to real points).
      {#MOMGD.33-61} The propagation (#MD2.2.6.175) and the frame bookkeeping (#MD2.2.6.196) concern the B′-dependent ŵ = û_k^{−1}v̂₁ only, where the backgrounds at which D(k) is invoked at step k (U^{rep}_k(V_k) at real or complexified data) lie in family (I), where c₀ = 1 and ŵ = w_tot; there they are unchanged, with Step 8's bound on v̂₁ below in place of v₁'s.
      {#MOMGD.33-62} The one further use of D(k)(iii) at general complex configurations, (11)(c)(β)'s polydisc points e^{iη(𝐇(s,tB′) + a″)}U_{k+1} (#MD2.4.11.5), does not lie in family (I) for a″ ≠ 0, and these points are not gauge transforms of frame points;
      {#MOMGD.33-63} there D(k)(iii)'s covariant clause involves the (s, t, B′)-dependent D(k)-level c₀^{(k)} of the evaluation point, whose rotation is charged to the per-step margin r_{ω,j}2^{−(k+1−j)}: on D(k+1)(iii)'s full domain it would cost dα_{1,j}, but every bound used there is on 𝒟^{sub}_{k+1}, where this Step's size bound decays as L^{j−k} on the layer j (#MD2.4.11.5).
    - {#MOMGD.33-64} *The bound at a field-small base, and at the reference Ū.* The bound is first derived at a G^c-valued base 𝐔 = e^{iηa′}U_{k+1} that is field-small per bond over the real reference (|Z(ηa′(b))| ≤ ιη per fine bond, as the configurations of the domain are).
      {#MOMGD.33-65} The minimisers Ū and the members of family (I) are not of this kind in the mean frame (the flat example of (II): Ū = 𝐔^{g₀} is 1 inside the top blocks and carries the phase ι on the bonds between them, ιL^k in units of η; #MD2.2.6.186: the complexified minimiser is field-small in the Landau frame and only phase-small in the axial-type frames); they are reached through their Landau representation over the real reference, *The reference Ū* below.
      {#MOMGD.33-66} RG1 defines the means and the averages on G^c-valued configurations (p.252 l.37–38 introduces G^c; p.253 l.15 and l.34 define M on G^c, for families of small diameter; (0.12) on p.254), so Step 1's frame, g, U^{rep}_k(V_k) = Ṿ^g, its hierarchical transports, and v₁ are the same compositions at 𝐔, jointly analytic in (𝐔, 𝐇_k) where the means (small diameter), Proposition 4 (phase below c₄(d, L)), and u_k (|𝐇_k| < a₁) are defined; the identity theorem of D2.1(2)'s bullet *Complex A_k and complex backgrounds* (#MD2.1.2.4) applies jointly, as for u_k.
      {#MOMGD.33-67} Size, at a field-small base 𝐔: Steps 2–6 run with 𝐔 for U_{k+1} with three changes.
      {#MOMGD.33-68} (i) CMP 98's Propositions 2 and 4 ((54), (131)) at the G^c-valued 𝐔: RG1 p.254 l.7–9 ("all results of the paper [12] are valid for it", the modifications being "connected … with the fact that we consider G^c-valued configurations"), Bałaban's, with α₀ the curvature constant of (2.34) for 𝐔 in the full domain (#MD2.0.3.53, #MD2.0.3.54; k ≥ 2) and α₁ as before; its quantitative modification, that R₀ is no longer an isometry in (126), is bounded in (ii) below by a factor 1 + o(1) per level.
      {#MOMGD.33-70} (ii) The conjugating transports are G^c-valued.
      {#MOMGD.33-71} Over the real base, (97) and (131) with A = a′ give 𝐔^m(b) = v_m(b₋)Ū̄₁^m(b)U^m_{k+1}(b)v_m(b₊)^{−1} with |Z(Ū̄₁^m(b))| < 2ιL^{m−k} and |Z(v_m)| ≤ dL^{m−k}ι(1 + o(1)) (the count of Step 5 (α)); telescoping the v_m along a path of at most d(L−1) level-m bonds and summing over the levels, |Im Z(P_n)| ≤ Σ_{m<n}2d(L−1)ιL^{m−k}(1 + o(1)) ≤ 2dιL^{n−k}(1 + o(1)) and |Im Z(T_b)| ≤ 2dιL^{n+1−k}(1 + o(1)), both ≤ 2dι(1 + o(1)).
      {#MOMGD.33-72} Ad_P = e^{i ad_X − ad_Y} with i ad_X skew-Hermitian and ad_Y Hermitian on 𝔤^c (the Hermitian extension of the Ad-invariant inner product), so by the log-norm bound ‖e^{S+H}‖ ≤ e^{λ_max(H)}, ‖Ad_P‖ ≤ e^{‖ad_Y‖} ≤ e^{2c_G|Im Z(P)|}, c_G as in (c); hence ‖Ad_{P_n^{−1}}‖, ‖Ad_{T_b}‖ ≤ e^{4c_Gdι(1 + o(1))} = 1 + o(1), as c_Gd max_nα_{1,n} is small.
      {#MOMGD.33-73} These enter Step 3's convention, |log v₁(x)| := Σ_{n<k}|Ad_{P_n^{−1}}log Δ_n| ≤ e^{4c_Gdι(1 + o(1))}Σ_{n<k}|log Δ_n| (the convention of (c)'s bullet *R(w)ω stays in the ω-domain*: w = ∏_je^{Z_j} with Σ_j|Z_j|), Step 5 (α)'s first bracket ∏_b exp(i Ad_{T_b}log(Ū̄₁^n)_b), whose logarithm is bounded by e^{4c_Gdι(1 + o(1))} times the real bound, and, in o(1) terms only, the transports R₀ and R̄₀^j inside (97)'s v_n and inside (126): a factor 1 + o(1) per level, not summed over k.
      {#MOMGD.33-74} (iii) M's Lipschitz bound in Step 5 holds on a complex neighbourhood of 1 (M analytic, p.253; Cauchy estimates) once the holonomies lie in it, |log h_Γ(𝐔^n)| ≤ q_n + 2dιL^{n+1−k}(1 + o(1)), small.
      {#MOMGD.33-75} (β)'s bound on u_k at complex 𝐔: (6)(e) (#MD2.2.6.155) bounds u_k's chain (106) with real transports; at complex 𝐔 the chain's conjugations are G^c-valued, each within (ii)'s bound, so |log u_k| ≤ C_we^{4c_Gdι(1 + o(1))}α₁ = C_w(1 + o(1))α₁.
    - {#MOMGD.33-76} *The reference Ū* (and any member of family (I), U^{rep}_k(V) at complex V, with a real datum V_r near V in place of V^{(k)}).
      {#MOMGD.33-77} With B′₀ := (1/i)log(M^k(𝐔)M^k(U_{k+1})^{−1}), |B′₀| = O(dι): by (97) and (131) over the real base, M^{k−1}(𝐔) = (Ū̄₁^{k−1}U^{k−1}_{k+1})^{v_{k−1}} with |Z(Ū̄₁^{k−1})| < 2ιL^{−1} and |Z(v_{k−1})| ≤ dL^{−1}ι(1 + o(1)), and (97) and (131) at j = k give the datum, |B′₀| ≤ 2ι + 2dι(1 + o(1)) = O(dι) ((0.12)'s averaging paths have L + 2Σ_ν|n_ν| bonds, RG1 p.254, so Step 5 (α)'s path count is not used here).
      {#MOMGD.33-78} Then Ū = U^{rep}_k(e^{iB′₀}V^{(k)}) = Y^{g} with Y := e^{iη𝐇_k(B′₀)}U_{k+1} the Landau configuration at the real reference and the complex datum B′₀ (Step 4 with B′₀ for B′) and g := g(B′₀) its hierarchical mean gauge fixing (Step 7), |log g| ≤ (C_w + 3d)sup_{B^k(y)}|𝐇_k(B′₀)| = O((C_w + 3d)dι) (|𝐇_k(B′₀)| = O(B₀e^{16κ_s}|B′₀|) by (6)(e)'s bound on 𝐇 by its datum, #MD2.2.6.156).
      {#MOMGD.33-79} Y is field-small over the real reference with ι₀ := sup|𝐇_k(B′₀)| = O(B₀e^{16κ_s}dι) for ι (here and in |log g| = O((C_w + 3d)B₀e^{16κ_s}dι) and the factors e^{O(c_G(C_w + 3d)dι)} below, the O contains the fixed factor B₀e^{16κ_s}, uniform in k and absorbed for g_K small), and its curvature is that of the Landau configurations e^{iη𝐇(s,tB′)}U_{k+1} with B′₀ for B′ ((6)(e) *The curvature conditions*, (f)'s chain condition;
      {#MOMGD.33-80} these are stated at |𝐇| ≤ h_k ≤ α_{1,k}/2, while here |𝐇_k(B′₀)| = O(B₀e^{16κ_s}dι)). The change formula of D2.2(6)(e)'s *The curvature conditions* does not use that radius: it is linear in the datum up to terms quadratic in it, giving at t = 1 the change 8B₀e^{16κ_s}C·O(1)ε_kξ²(L^nξ)^{−2} for |B′| < O(1)ε_k, so with B′₀ for B′ the change of curvature of Y against U_{k+1} is ≤ 8B₀e^{16κ_s}C·O(dι)ξ²(L^nξ)^{−2}.
      {#MOMGD.33-80-1} With CRE p.268 l.38's bound on U_{k+1}, Y's curvature constant is α₀ = O(ε_{k+1} + B₀e^{16κ_s}dι), which tends to 0 with g_K since ι ≤ α_{1,k}. So (i)–(iii) hold at the base Y for g_K small, with this α₀, which is Ū's (the plaquettes of Ū are the g-conjugates of Y's), not (2.34) for 𝐔.
      {#MOMGD.33-81} Steps 2–6 at the reference Ū: by the covariance of the averages (Step 4), Ū^n = (Y^n)^{g}, the hierarchical transports are Ū^n(Γ_n) = g(x_{n+1})Y^n(Γ_n)g(x_n)^{−1}, so P_n(Ū) = g(x_n)P_n(Y)g(x)^{−1} and ‖Ad_{P_n(Ū)^{−1}}‖ ≤ e^{2c_G(|log g(x_n)| + |log g(x)|)}‖Ad_{P_n(Y)^{−1}}‖; the holonomies are h_Γ(Ū^n) = Ad_{g(x_{n+1})}h_Γ(Y^n), so (iii) holds at Ū with the factor e^{2c_G|log g|};
      {#MOMGD.33-82} and U^{rep}_k(V_k) = (e^{iη𝐇̂_k(B′)}Ū)^{ĝ} = ((e^{iηX̂}Y)^{g})^{ĝ} with X̂ := Ad_{g^{−1}}𝐇̂_k(B′), |X̂| ≤ e^{2c_G|log g|}sup|𝐇̂_k(B′)|, ĝ := v̂₁^{−1}û_k, so the level-n mismatch is Δ_n = M({Ad_{g(x_{n+1})}h_Γ(Y^n)}_Γ)^{−1}M({Ad_{ĝ(x_{n+1})g(x_{n+1})}h_Γ((e^{iηX̂}Y)^n)}_Γ) ((U^g)^{ĝ} = U^{ĝg}), Step 5 at the field-small base Y with the fluctuation X̂ and the conjugation ĝ(x_{n+1})g(x_{n+1}) in place of g(x_{n+1}).
      {#MOMGD.33-83} Every g-conjugation costs a factor e^{2c_G|log g|} = e^{O(c_G(C_w + 3d)dι)} = 1 + o(1), none summed over k.
  - {#MOMGD.33-84} *Result.* Step 5's Δ_n bound holds at a field-small base, and the v₁ bound at a field-small base in the hierarchical mean frame (Step 1's mean conditions at the base): |log v₁(B′)| ≤ 2d(1 + o(1))e^{8c_Gdι(1 + o(1))}sup_{B^k(y)}|𝐇_k(B′)| (the factor e^{4c_Gdι(1 + o(1))} of Step 3's convention times that of Step 5 (α)'s first bracket); at the reference Ū, hence for v̂₁ at every 𝐔 of the domain, |log v̂₁(B′)| ≤ 2d(1 + o(1))e^{8c_Gdι₀(1 + o(1))}e^{O(c_G(C_w + 3d)dι)}sup_{B^k(y)}|𝐇̂_k(B′)|;
    {#MOMGD.33-85} both are ≤ 3d sup_{B^k(y)}|𝐇_k(B′)| (𝐇̂_k at Ū), uniformly in k, once c_G(C_w + 3d)d max_nα_{1,n} and Steps 5–6's o(1) are small (g_K small); on a layer of top level j the same with Step 7's rescaling and ι = α_{1,j}, giving 3dL^{j−k}sup_{B^j(y)}|𝐇_k|; v₁(0) = 1 on family (I), v̂₁(0) = 1 everywhere (𝐇̂_k(0) = 0).
    {#MOMGD.33-86} So (c)–(e) hold at D(k)'s representative at real backgrounds and on family (I) with w_tot = u_k^{−1}v₁ and C_w + 3d in place of C_w, and at the general complex configurations with ŵ = û_k^{−1}v̂₁ in place of w_tot and the B′-independent c₀(𝐔) absorbed by (6)(b7)'s covariant form.
    {#MOMGD.33-87} Inputs: RG1 (0.5)–(0.6), (0.10)–(0.12), (0.19), p.252 (l.37–38 for G^c), p.253 l.15 and l.34, p.254 l.7–9, p.265 with (2.1); CRE p.248 l.36, (3.10), p.267, p.268 l.38; REG (1.14), (1.19); CMP 98 Proposition 2 ((54)) with p.37 l.7–8, (68)–(69), (93), (97), (131), Proposition 4; (d)'s bound on u_k (#MD2.2.4.39); CRE p.276's older-layer regularity for the older layers only.
    {#MOMGD.33-88} v₁ is not block-constant on the top blocks (it is 1 at their centres only); (6)(e)'s *The gauge frame of σ_j* (#MD2.2.6.196) accounts for this.

{#MD2.2.4.44} *(e) The joint expansion (from (c), (d), and D2.1(4)).*
- {#MD2.2.4.45} *Interpolation.* With the parameters s and 𝐇(s,B′) of D2.1(4), put w(s) := (W_y(𝐇(s,B′), U_{k+1}))_y.
  {#MD2.2.4.45-1} For one old family 𝔅, let Φ_𝔅(s) be its closed word evaluated at (e^{iη𝐇(s,B′)}U_{k+1}, R(w(s))ω), and for k ≥ 2 at (e^{iη𝐇(s,B′)}U_{k+1}, 𝐉′(U_{k+1}, J_{k+1}, 𝐇(s,B′)), R(w(s))ω), with 𝐉′ of (6)(b4).
  {#MD2.2.4.45-2} Q_k(𝔅) is a constant by (a).
  - {#MD2.2.4.46} Φ_𝔅(1) is the word of (c), since 𝐇(1,B′) = 𝐇_k(B′) (D2.1(4)(a)).
  - {#MD2.2.4.47} Φ_𝔅(0) is the word at (U_{k+1}, ω), since 𝐇(0,B′) = 0 and w₀ = 1 ((d)).
  - {#MD2.2.4.48} W_y is given by (106) for every complex 𝐇 with |𝐇| < a₁ (RG1 p.266), and obeys (d)'s size bound for |𝐇| < min(a₁, c₄), so w(s) is defined for every s, also where 𝐇(s,B′) is not the 𝐇 of a configuration.
    {#MD2.2.4.48-1} The identity of (c) is used at s = 1 only.
- {#MD2.2.4.49} *Locality at s(σᶜ) = 0.* 𝐇(s,B′) vanishes on a neighbourhood of Y(σ)ᶜ (D2.1(4)(b)).
  {#MD2.2.4.49-1} So w(s) = 1 on every block all of whose bonds lie in that neighbourhood, in particular on every block disjoint from Y(σ).
  {#MD2.2.4.49-2} A factor then takes its s = 0 value unless its domain X_W, its interval or, for an ω-dependent factor, a block meeting X_W, meets a component of Y(σ).
  {#MD2.2.4.49-3} Blocks are the B^j(y), y ∈ VAR's Λ_j, j ≤ k, of (d).
- {#MD2.2.4.50} *Expansion.* The fundamental theorem of calculus in each s(Δ), as in D2.1(4), gives Φ_𝔅(1) = Σ_σ ∏_{Δ∈σ}∫₀¹ds(Δ)∂_{s(Δ)}Φ_𝔅(s)|_{s(σᶜ)=0}.
  {#MD2.2.4.50-1} A component on which Φ_𝔅 does not depend gives zero.
  - {#MD2.2.4.51} Call a component Y *active* for 𝔅 if it contains a fine bond of C, or meets X_W for some W ∈ 𝔅, or meets a block meeting X_W for an ω-dependent W ∈ 𝔅.
  - {#MD2.2.4.52} Only the σ whose components are all active remain.
- {#MD2.2.4.53} *Arcs and new groups.* For an active Y let S′(Y) be the fine bonds of C in Y together with the intervals of the W ∈ 𝔅 for which Y meets X_W (or, ω-dependent W, a block meeting X_W).
  {#MD2.2.4.53-1} Let I(Y) be the smallest arc containing S′(Y) by D2.1(4)'s rule, then enlarged at each end to the end of any old interval that it cuts.
  {#MD2.2.4.53-2} Old intervals are pairwise disjoint (old compatibility), so the enlargement stops after at most one interval at each end, and every old interval lies inside I(Y) or is disjoint from it.
  - {#MD2.2.4.54} The new groups G are the connected components of the overlap graph of the arcs I(Y), with I(G) := ∪_{Y∈G}I(Y).
  - {#MD2.2.4.55} The new insertion Y_G of G is #MD2.1.4.13's with Hol_{I(G)}(e^{iη𝐇(s,B′)}U_{k+1}) replaced by the ordered product along I(G) of the old insertions with intervals in I(G) and the transports of e^{iη𝐇(s,B′)}U_{k+1} along the pieces of C between them (the holonomy itself when no old interval lies in I(G)). Its endpoints are on C, at the ends of I(G).
  - {#MD2.2.4.56} An old insertion whose interval lies in no new arc stays, evaluated at (U_{k+1}, ω).
    {#MD2.2.4.56-1} Since w₀ = 1, it is an insertion of step k+1 with the same group, domain and interval.
- {#MD2.2.4.57} *Result.* For real A_k on the support,
  {#MD2.2.4.58} F = κ^{(k)}e^{𝓔_k}[f_{k+1} + Σ_{𝔊≠∅}dim(π)^{−1}tr(Y_{G₁}U_{(1)}⋯) + Σ_{𝔅≠∅}Q_k(𝔅)Σ_{𝔊 compatible with 𝔅}dim(π)^{−1}tr(word of (𝔅,𝔊))]∘ψ_{k+1}.
  - {#MD2.2.4.59} The first sum is D2.1(4)'s.
  - {#MD2.2.4.60} In the second, the word of (𝔅,𝔊) is the product along C, in cyclic order, of the new insertions Y_G, the untouched old insertions and the U_{k+1}-transports between them.
  - {#MD2.2.4.61} 𝔊 is *compatible with 𝔅* if each of its components is a connected union of cubes (D2.1(4)'s clause (0)), its components are active for 𝔅 and pairwise disjoint without a common wall, its arcs are disjoint, and each group is connected by arc overlaps.
  - {#MD2.2.4.62} The map σ ↦ 𝔊 is a bijection onto the families compatible with 𝔅, as in D2.1(4).
  - {#MD2.2.4.63} For complex A_k and backgrounds the same formula holds, by (c).
  {#MD2.2.4.93} So F is written exactly, on every labelled term, as f_{k+1} plus compatible families of local insertions at step k+1: new groups built from s-components and the old insertions they touch, and the untouched old insertions. The scalar parts are unchanged, and covered and uncovered terms are treated alike.
- {#MD2.2.4.64} *Locality.* Y_G depends on B′ and (𝐔,𝐉) on the components of G, on ω on the domains of its old insertions, on U_{k+1} along I(G), and on the blocks of (d) meeting these domains.
  {#MD2.2.4.64-1} This is the localisation of the observable, in the form (5) needs.
- {#MD2.2.4.65} *Gauge covariance of the new pieces ((6)(b)).* B′ transforms by R(v) for gauge transformations v of V_{k+1} (RG1 p.265: "A gauge transformation v of V induces the gauge transformation v of V^{(k)} and the transformation B′ → R(v)B′").
  {#MD2.2.4.65-1} Each factor of Y_G is then covariant in (U_{k+1}, ω) if 𝐇(s,·) is built from covariant operators.
  {#MD2.2.4.65-2} That RG2's walk expansion has this property is not printed on the pages read (RG2 pp.3–4).
  {#MD2.2.4.65-3} It is checked with Cov(k+1) in (6)(b).

{#MD2.2.4.66} *(f) The analyticity domain of the old factors (with CRE p.277's margin, and, for (2.35) and (2.37) at the evaluation points, #MD2.2.6.142's inputs: 𝐁_p(X)'s definition (CRE p.256 l.57–63), q₀ = q₁ > p₀ (SW closure §2), CRE (2.6)–(2.7) (p.255), RG2 p.5's all-norms bound, and the 𝐇-decay (CRE p.267 l.42–44, p.277 l.6–8); RMJ, #MOMGD.50).*
- {#MD2.2.4.67} The bounds of (e), by the Schwarz lemma and Cauchy's estimate as in D2.1(4), need every old factor to be analytic at e^{iη𝐇(s,tB′)}e^{iηa′}U_{k+1} for |s(Δ)| ≤ e^{κ_s}, |t_Y| ≤ T_Y and a′ in the radius of D(k+1)(iii), and, for ω-dependent factors, with ω replaced by R(w(s,t))ω.
  {#MD2.2.4.67-1} That stays in the ω-domain by (c) with sup|𝐇(s,tB′)| ≤ min(β,1)α_{1,k}/2 in place of sup|𝐇_k| on Ω_k, and on older layers with (6)(e)'s decaying bound; at k = 1 since α_{1,1}r → 0, and for k ≥ 2 by (6)(e)'s propagation; on Ω₁∖Ω₂ the propagation uses the base points of (6)(e) *The inclusion*, at every k.
  {#MD2.2.4.67-2} The leading word needs no condition, since a character of a holonomy is entire in the background.
- {#MD2.2.4.68} Write the point as e^{iηA″}X₁ with the real centre X₁ := e^{iη𝐇_k(B′)}U_{k+1} = U_k(e^{iB′}V^{(k)})^w, which lies in the support up to the gauge transformation w.
  {#MD2.2.4.68-1} By BCH and (1.18), |A″| ≤ 4B₀e^{16κ_s}(T_Y|B′|_Y + sup|B′|) + |a′| + O(·)², with sup|B′| for the term 𝐇_k(B′), since 𝐇_k is not local.
- {#MD2.2.4.69} D(k)(iii) asks |A″| below the step-k radius of CRE (2.39), and the step-(k+1) radius is smaller:
  - {#MD2.2.4.70} on Ω_n∖Ω_{n+1}, n < k, by β2^{−(k+1−n)}α_{1,n}L^{k−n} (in units of |A″|; the phase margin per fine bond is this times η = L^{−k});
  - {#MD2.2.4.71} on Ω_k∖Ω_{k+1} by (β/2)α_{1,k};
  - {#MD2.2.4.72} on Ω_{k+1} by α_{1,k} − α_{1,k+1}/L (the step-(k+1) radius there is that of n = k+1).
    {#MD2.2.4.72-1} This is ≥ α_{1,k}/2 when α_{1,k+1} ≤ (L/2)α_{1,k}, and that holds.
    {#MD2.2.4.72-2} CRE (2.6), first line, with n = k+1, m = k (CRE (2.6)–(2.7)), gives g_{k+1} ≤ (1+β₀)g_k.
    {#MD2.2.4.72-3} If g_{k+1} ≥ g_k, then α_{1,k+1}/α_{1,k} ≤ g_{k+1}/g_k ≤ 1+β₀ ≤ L/2 for L ≥ 2(1+β₀), since (log g^{−2})^{q₁} decreases as g grows.
    {#MD2.2.4.72-4} If g_{k+1} < g_k, then α_{1,k+1} < α_{1,k}, since g(log g^{−2})^{q₁} increases in g once log g^{−2} > 2q₁.
  {#MD2.2.4.73} So the condition is 4B₀e^{16κ_s}(T_Y|B′|_Y + sup|B′|) < margin, for a′ within the step-(k+1) radius: the margin is already the step-k radius minus the step-(k+1) radius, and |a′| is below the latter.
  {#MD2.2.4.73-1} B′ vanishes off B(Γ_{k+1}) and |B′| < O(1)ε_k there at real configurations (CRE (3.11), (3.14), (3.15); D2.1(4), *The hypothesis*).
  {#MD2.2.4.73-2} On Ω_k, with T_Y ≥ 1, it holds when 8B₀e^{16κ_s}T_YO(1)ε_k < min(β, 1)α_{1,k}/2.
- {#MD2.2.4.74} *CRE p.277's margin (Bałaban's).* CRE p.277 states the same requirement for the boundary terms 𝐁_k and asserts it: "we have to use a part of the analyticity domains of terms in 𝐁_k for the function 𝐇_k.
  {#MD2.2.4.74-1} This is the reason for putting the powers of 1/2 in the conditions (2.36)–(2.39).
  {#MD2.2.4.74-2} The analyticity domains become smaller after each step, but the difference is very small and exponentially decreasing in the number of steps.
  {#MD2.2.4.74-3} The localization of the fluctuation field, and the exponential decay of the minimizing function 𝐇_k imply that this difference is still much greater than bounds on this function" (the older layers use the decay, (*The older regions*) below).
  {#MD2.2.4.74-5} It applies to the old factors because D(k)(iii) is posed on the same domains (D2.0(3), complex part of (2.39)).
  - {#MD2.2.4.75} *What CRE p.277's margin entails.* On Ω_k∖Ω_{k+1} the margin (β/2)α_{1,k} is the power-of-1/2 difference, and there is no decay to use there.
    {#MD2.2.4.75-1} So CRE p.277's margin's "much greater than bounds on this function" is the inequality 8B₀e^{16κ_s}O(1)ε_k < (β/2)α_{1,k}.
  - {#MD2.2.4.76} On Ω_{k+1} CRE p.277's margin does not apply, since the margin α_{1,k} − α_{1,k+1}/L is not a power-of-1/2 difference.
    {#MD2.2.4.76-1} But that margin is ≥ α_{1,k}/2 ≥ (β/2)α_{1,k}, as β ≤ 1, so the same inequality closes it.
  - {#MOMGD.49} So the expansion of (e) needs, and CRE p.277's margin gives, 8B₀e^{16κ_s}O(1)ε_k < min(β,1)α_{1,k}/2.
    {#MOMGD.49-1} Without it already Φ_𝔅(0), and the Cauchy estimates in s(Δ) at t_Y = 1, would leave the domain.
  - {#MD2.2.4.78} With ε_k = ĝ_kA₀(log ĝ_k^{−2})^{p₀} (CRE (2.4), p.255) and α_{1,k} = ĝ_kC₁(log ĝ_k^{−2})^{q₁} ((2.28), p.259: "q_0, q_1 are integers greater than 1, C_0, C_1 are sufficiently large positive numbers"), at the tube's ĝ_k ≤ g_k (#MD2.0.1.7), so ε_k/α_{1,k} ≤ (A₀/C₁)(log g_k^{−2})^{p₀−q₁}, the inequality holds for g_K small under q₁ > p₀ (g_k ≤ (1+β₀)g_K for k ≤ K, CRE (2.6)–(2.7)).
    {#MD2.2.4.78-2} Related print: V4's "p_0 ≥ 5𝔯" (sec:sourced-effective-interaction *Conventions*, from CRE pp.245–246 and (2.5)).
    {#MOMGD.49-5} So CRE p.277's margin, which holds for every small g_K, entails q₁ ≥ p₀: for q₁ < p₀ the ratio ε_k/α_{1,k} = (A₀/C₁)(log ĝ_k^{−2})^{p₀−q₁} (#MD2.4.5.2-1) is unbounded as g_k → 0, since ĝ_k ≤ g_k.
  - {#MOMGD.49-4} No printed comparison of q₁ with p₀ was found: q₁ occurs only on CRE p.259 and LFR II p.368, and p₀ is not fixed on CRE p.255 (search of the CRE, RG1, RG2, LFR I, LFR II, and UV3 transcriptions).
    {#MOMGD.49-2} D2 uses the stronger q₀ = q₁ > p₀ (SW closure §2; #MD2.4.12.51).
    {#MOMGD.49-3} Under it ε_k/α_{1,k} → 0 as g_k → 0, so #MOMGD.49's inequality and (6)(e)'s complex-data form (#MD2.2.6.173-3) hold for g_K small, whatever the constants, and neither is taken from CRE p.277's margin.
  - {#MD2.2.4.80} *T_Y.* T_Y is taken as large as the margin allows.
    {#MD2.2.4.80-1} By the inequality T_Y ≥ 1, and 1/T_Y = max(|B′|_Y/ε_H, 16B₀e^{16κ_s}|B′|_Y/(min(β,1)α_{1,k}), C′B₀e^{16κ_s}|B′|_Y/(min(β,1)α_{0,k})) ≤ 1, the third entry for the pointwise conditions (2.34) and (2.36) (#MD2.2.6.142) and, with C′ enlarged by the factor C_{(2.35)}/C (#MD2.2.6.142-69) and C′ ≥ C_{(2.37)} (RMJ note #RMJ.6.5), for (2.35) and (2.37) at the evaluation points.
    {#MD2.2.4.80-2} This is the factor per component in D2.4's count.
- {#MD2.2.4.81} *The older regions.* On Ω_n∖Ω_{n+1}, n < k, the margin in the units of |A″| is β2^{−(k+1−n)}α_{1,n}L^{k−n} = (β/2)α_{1,n}(L/2)^{k−n}.
  {#MD2.2.4.81-1} CRE (2.6), first line, gives g_k ≤ (1+β₀)(k−n)^{1/2}g_n, and (2.7), first line (both with CRE (2.6)–(2.7)), (log g_k^{−2})^{q₁} ≤ (1+β₀)(log g_n^{−2})^{q₁}; so α_{1,n} ≥ α_{1,k}/((1+β₀)²(k−n)^{1/2}), and the margin is ≥ (β/2)α_{1,k}(L/2)^m/((1+β₀)²√m), m = k−n ≥ 1.
  - {#MD2.2.4.82} The deformation there is not bounded by the Ω_k inequality: the inequality of (f) bounds it on Ω_k only, as D2.1(3), D2.1(4) case (B) and (6)(e) say.
  - {#MD2.2.4.83} The decay closes it.
    {#MD2.2.4.83-1} On Ω_n∖Ω_{n+1}, sup|𝐇(s,tB′)| ≤ O(1)(Lθ)^{m}h_k with θ := e^{−δ₀RM₁/32}, by VAR (190), PRT2's weighted distance with VAR (1), and, on the polydisc, CRE p.277's 𝐇-decay (#MOMGD.55; RG2 p.5's all-norms bound has no decay form, RG2 (1.18) gives none), as derived in (6)(e) (*Older layers*: the layer of ω_j is Ω_{j+1}∖Ω_{j+2}, so k−j−1 = m).
    {#MD2.2.4.83-2} Against the margin it suffices that O(1)(1+β₀)²√m(2θ)^mh_k < (β/2)α_{1,k}.
    {#MD2.2.4.83-3} Since h_k ≤ min(β,1)α_{1,k}/2 by CRE p.277's margin's inequality in its complex-data form ((6)(e)), and √m x^m ≤ x for 0 < x ≤ 1/2, m ≥ 1, this holds for all m ≥ 1 once 2θ ≤ 1/2 and 2θ·O(1)(1+β₀)² < 1.
    {#MD2.2.4.83-4} That is so for g_K small, since R ~ R_j is large uniformly in j ((6)(e)).
  - {#MD2.2.4.84} So the older-layer margin rests on the decay, as CRE p.277 says (the sentence on the exponential decay of 𝐇_k in CRE p.277's margin's quote above), and on CRE p.277's 𝐇-decay.
    {#MD2.2.4.84-1} No condition L ≥ 3 or (1+β₀)² ≤ 3/2 is needed for it.
    {#MD2.2.4.84-2} The gradient part follows CRE p.277's 𝐇-decay and RG2 p.5's all-norms bound as in (6)(e); the curvature and 𝐉 parts on the older layers are in (6)(e), *The curvature conditions*, *Older layers*.
    {#MD2.2.4.84-3} The sizes of D2.1(4)'s case (B) insertions are D2.1(5)'s; this margin for them is (6)(e)'s.
  - {#MD2.2.4.85} The bounds sup|𝐇(s,tB′)| ≤ min(β,1)α_{1,k}/2 of (f) and |𝐇| ≤ 4B₀e^{16κ_s}|B′| of (d) are on Ω_k.
- {#MD2.2.4.86} *Carrying 𝐉 (k ≥ 2).* For k ≥ 2 the old factors are functions Y_W(𝐔, 𝐉, ω) (#MD2.0.3.56).
  {#MD2.2.4.86-1} At the deformed background the 𝐉-argument is carried as Bałaban carries it for 𝐄^{(j)}:
  - {#MD2.2.4.87} *Sources.* RG1 (3.10)–(3.13), p.272, RG1 p.273, RG2 p.2 and PBG (3.42), p.397, are quoted below.
  - {#MD2.2.4.88} RG1 (3.10)–(3.13), p.272. 𝐉′ = D^{ξ*}_{e^{iξ𝐀}𝐔}ξ^{−2}π Im∂e^{iξ𝐀}𝐔 is expanded by (3.11).
    {#MD2.2.4.88-1} RG1 p.272 replaces D*D by D*D + DRD*, equal to it on 𝐀 in the Landau gauge RD*𝐀 = 0 ("We use the fact that 𝐇_j satisfies the Landau gauge condition RD*𝐇_j=0"), and prints the operator identity D*D + DRD* = Δ_𝐔^ξ − P₁ + (lower order, local operator) (l.22), with P₁ defined in none of the papers (#MD2.2.6.71-3).
    {#MD2.2.4.88-2} The old term becomes the function (3.13) of (𝐔, 𝐉, 𝐀), with second argument (L^{j−1}η)³𝐉 + Δ_𝐔^ξ𝐀 − P₁𝐀 + 𝐅₁(𝐔,𝐀) = (L^{j−1}η)³𝐉 + (D*D + DRD*)𝐀 + 𝐅(𝐔, 𝐀) (#MD2.2.6.64).
    {#MD2.2.4.88-3} RG1 states its analyticity in 𝐀 under (3.14), |𝐀|, |P₁𝐀|, |∇_𝐔^ξ𝐀|, |Δ_𝐔^ξ𝐀| < α₂ on X. D2 uses (3.14′): |𝐀|, |∇_𝐔^ξ𝐀|, |(D*D + DRD*)𝐀| < α₂ on X. Under (3.14′), (3.13) is analytic in 𝐀 by p.272 l.36–38's argument: e^{iξ𝐀}𝐔 stays in the space for |𝐀| and |∇_𝐔^ξ𝐀| small, and the second argument differs from (L^{j−1}η)³𝐉 by (D*D + DRD*)𝐀 + 𝐅(𝐔, 𝐀), with 𝐅 local in 𝐔, ∂𝐔, 𝐀, ∇_𝐔^ξ𝐀 (p.272 l.19) and 𝐅(𝐔, 0) = 0 by (3.11).
  - {#MD2.2.4.89} RG2 p.2 states this structure for every old term: "there exists a function 𝐄(X,𝐔,𝐉,𝐀) analytic and localized to X in 𝐔, 𝐉, 𝐀, such that a given term is obtained substituting a proper nonlocal expression in the place of 𝐀".
    {#MD2.2.4.89-1} So Ỹ_W(𝐔, 𝐉, 𝐀, ω) := Y_W at the (3.13)-substituted arguments is local in 𝐀 on X_W's neighbourhood.
    {#MD2.2.4.89-2} At 𝐀 = 𝐇_k(B′), which is in the Landau gauge, it is the old factor at the true configuration ((3.11)–(3.12)).
    {#MD2.2.4.89-3} At 𝐀 = 0 it is Y_W(𝐔, 𝐉, ω).
  - {#MD2.2.4.90} The s-expansion of (e) substitutes 𝐀 = 𝐇(s, tB′), with (𝐔, 𝐉) in D(k+1)(iii)'s domain.
    {#MD2.2.4.90-1} At s ≠ 1, 𝐇(s, tB′) need not be in the Landau gauge, and nothing requires it: Φ_𝔅(s) is a value of the analytic function Ỹ_W, equal to the true word at s = 1 and to the word at (𝐔, 𝐉, ω) at s = 0.
  - {#MD2.2.4.91} The condition.
    {#MD2.2.4.91-1} (3.14′) for 𝐀 = 𝐇(s, tB′), with α₂ replaced by the 𝐉-margin β2^{−(k+1−n)}α_{0,n}(L^nξ)^{−3} between the step-k and step-(k+1) 𝐉-bounds of CRE (2.36), in the units of (3.13).
    {#MD2.2.4.91-2} At s = 1 RG1 p.273 asserts (3.14) with α₂/3: "We assume also that ε₁ is so small that 𝐇_j(B(t)) satisfies (3.14) with 1/3α₂ on the right-hand side", on every X. By the identity of #MD2.2.4.88-1, |(D*D + DRD*)𝐀| ≤ |Δ_𝐔^ξ𝐀| + |P₁𝐀| + |ℓ𝐀| on X, ℓ the lower-order local operator (table #T6.15), with |ℓ𝐀| on X at most O(1) times the sup of |𝐀| + |∇_𝐔^ξ𝐀| on X widened by ℓ's range, the O(1) bounding ℓ's coefficients on the space. So the (3.14) bounds give the (3.14′) bounds with O(1)α₂.
    {#MD2.2.4.91-3} For the s-localised 𝐇(s, ·) the |P₁𝐀| and |Δ_𝐔𝐀| bounds are RG2 (1.18)'s "same bound for all admissible norms" with RG2 p.5's all-norms bound: PBG Theorem 3.1, (3.42), p.397, lists |(Δ_UG′(U)λ)(x)| among its norms, with weight 1 against (L^jη)² for |G′λ|.
    {#MD2.2.4.91-4} RG1 p.272 promises such bounds: "for terms in this expansion we will have good bounds, including bounds for the covariant Laplace operator".
    {#MD2.2.4.91-5} So RG2 p.5's all-norms bound is extended to the Laplacian and P₁ norms (#MOMGD.57), and by #MD2.2.4.91-2 to the norm |(D*D + DRD*)𝐀| of (3.14′).
    {#MD2.2.4.91-6} The resulting smallness condition on ε_k is of the kind of (f)'s, and its sizes are D2.4's.

### (5) The Joint Cluster Expansion {#MSD2.2.5}

{#MD2.2.5.1} *(a) Reduction to tensor expectations.* By (4)(e), F is a finite sum (finite torus) of terms c·T, with c = κ^{(k)}e^{𝓔_k}Q_k(𝔅) a number (D(k)(v)) and T = dim(π)^{−1}tr(X₁U₁X₂U₂⋯X_mU_m) a closed word.
- {#MD2.2.5.2} The X_i are the new insertions Y_G and the untouched old insertions; the U_i are U_{k+1}-transports.
  {#MD2.2.5.2-1} Only the Y_G depend on the integrated field A = A_k|_{Λ_{k+1}}, through B′.
  {#MD2.2.5.2-2} Let J be the set of these slots.
  {#MD2.2.5.2-3} Y_{G_i} depends on A only on D_i := the union of the components of G_i (D2.1(4)(b), (4)(e) *Locality*).
- {#MD2.2.5.3} In matrix entries, T = dim(π)^{−1}Σ_{α,β}∏_i(X_i)_{α_iβ_i}(U_i)_{β_iα_{i+1}} (α_{m+1} := α₁) is multilinear in the X_i.
  {#MD2.2.5.3-1} So ⟨T⟩_{1,1} is the contraction, with the A-independent factors, of the tensor expectation ⟨𝒳⟩_{1,1}, 𝒳 := ⊗_{i∈J}X_i, a function of A with values in ⊗_{i∈J}End(V_π).
  {#MD2.2.5.3-2} If J = ∅ (the leading word f_{k+1} and the words of untouched old insertions only), ⟨T⟩ = T.
- {#MD2.2.5.4} ⟨𝒳⟩_{1,1} = I(𝒳)/I(1), with I(·) the last integral of CRE (3.25) with the observable inserted, at fixed outer variables ((2)).

{#MD2.2.5.5} *(b) Source of the expansion.* RG2 Sect. 2 (pp.11–14) expands the fluctuation integral of RG1 (2.13) ("Thus we have prepared the integral in (I.2.12), or (I.2.13), to the last step in our construction", p.11), with the action localised as Σ_{Y∈𝐃_k}𝐕_k(Y,B) (RG2 Lemma 2, (1.41)).
{#MD2.2.5.5-1} For the measure of CRE (3.27) Bałaban's own statement is CRE pp.275–279 (read in full in the transcription):
- {#MD2.2.5.6} p.275: "Let us consider now the expectation values in the formulas (3.26), (3.28), (3.37).
  {#MD2.2.5.6-1} To construct their cluster expansions we repeat all the considerations of Sect. 3.7 [I]" (so printed), with the multi-scale cover {□}, "which is a cover of Ω_1" (p.275), built from "cubes □, which are unions of 2^d neighboring cubes from π_j", and its partition of unity.
- {#MD2.2.5.7} p.276 localises "the actions defining the measures (3.27), (3.29)": "The action in (3.29) differs only by the additional dependence on the field tA_k, but this was already taken into acount [so printed] in the above considerations.
  {#MD2.2.5.7-1} The action in (3.27) contains more expressions": 𝐑_k as 𝐄_k; 𝐁_k by (I.3.6)–(3.7), localised over Y₀ ∈ 𝐃_k meeting Λ_{k+1}. p.277: these terms "can be estimated as in (2.42), but with the additional factor O(ε_k) arising from the bound of the fluctuation field"; the A(1/g_k²(·) − 1/g_k², ·) terms are localised in Z_k; V^{(k)}(S_{k+1}) likewise.
- {#MD2.2.5.8} p.277: the normaliser of the last expectation value in (3.37) "is expanded in exactly the same way as in Sect. 7 [I]" and "represented as exp Ẽ^{(k+1)}(Λ_{k+1})", given by (I.7.12) with terms (I.7.13).
  {#MD2.2.5.8-1} The numerator with an inserted localised term is (3.44), with one marked domain Z₀; "for n>0 the factors H(Z_i) are the same as in the expansion of the denominator". p.278: the sum over the polymers not meeting Z₀ along a cube or a wall "is exponentiated, and the exponent is represented by (I.7.12), with the additional restriction on the polymers Z_i" ((3.45)–(3.46)).
- {#MD2.2.5.9} p.279: "The other expectation values in (3.26), (3.28) are treated in exactly the same way.
  {#MD2.2.5.9-1} We have discussed already the localized expansions for the actions defining the corresponding measures, and for the integrated expressions.
  {#MD2.2.5.9-2} Having these expansions we proceed with the cluster expansions, and with the operations described above in (3.44)–(3.47)."
- {#MD2.2.5.10} The first expectation value of the display called (3.26) is ⟨·⟩_{s=1,t}, t ∈ [0,1], under (3.27), whose source term −⟨A, C*Δ^{(k)}CA_k⟩ carries no t ((1)).
  {#MD2.2.5.10-1} At t = 1 it is ⟨·⟩_{1,1}.
  {#MD2.2.5.10-2} So the localised action of (3.27) at s = t = 1, the exponentiation of Z_{1,1}, and the exponentiation of the restricted gases are Bałaban's construction as presented.
- {#MD2.2.5.11} *CRE p.279's vacuum statements (Bałaban's).* (i) "treated in exactly the same way" (p.279) includes the convergence of the cluster expansions of Z_{1,t} and of the gases restricted to polymers compatible with given domains, for every t ∈ [0,1] and with the source term at full strength.
  {#MD2.2.5.11-1} On pp.276–279 Bałaban's statements on that term are p.276's sentence "The action in (3.29) differs only by the additional dependence on the field tA_k, but this was already taken into acount [so printed] in the above considerations", with the analyticity space (3.43), and p.279's "Similarly, the first expectation value in (3.26) is included into this boundary term, too", which names ⟨·⟩_{s=1,t} under (3.27) directly.
  {#MD2.2.5.11-2} The field A_k there can be of size O(ε_k/g_k) (p.267: |A_k′| < O(1)ε_k, A_k′ = g_kA_k).
  {#MD2.2.5.11-3} No step uses a locality of the support of C*Δ^{(k)}CA_k.
  {#MD2.2.5.11-5} In (i), "convergence" means absolute convergence.
  {#MD2.2.5.11-6} (ii) Bałaban's "sufficiently small" (RG2 (2.12)) is used in the Kotecký–Preiss form Σ_{Z′≁Z}|H(Z′)|e^{a(Z′)+d(Z′)} ≤ a(Z) for every polymer Z and every single cube Z = {□}, with a(Z) = c|Z| and d(Z) = 9 log2·|Z|, |Z| the number of cubes; then Σ_{𝒞≁X}|φ^T(𝒞)|e^{d(𝒞)} ≤ c|X| for every union X of cubes, d(𝒞) := Σ_jd(Z_j) (a cluster ≁ X has a member ≁ {□} for a cube □ of X, since a wall in a union of closed cubes is a face of one of them).
  {#MD2.2.5.11-7} The weights d are needed for the bounds of (d) and in (6)(c).
  {#MD2.2.5.11-8} (ii) is D2.4(2), (e)–(g), with c = (9/64)e^{−4κ} for κ ≥ κ_vac.
  {#MD2.2.5.11-9} The derivation needs (i) in a bound form, CRE p.279's same-way clause in the form (i′) of D2.4(2) (Bałaban's): the activities of the gas of (3.27) with the source term satisfy (2.38) with Bałaban's constants; and RG2 Lemma 3's repair (D2.4(1)).
- {#MD2.2.5.12} *RG2's numbering of [I]: "Sect. 7 [I]" is RG2 Sect. 2.* CRE's [I] is RG1 (CMP 109) "and references therein" (CRE p.285); "references therein" concerns RG1's bibliography (CRE p.244: "The numbers here mean the numbers in the references to [I]"), not RG2.
  {#MD2.2.5.12-1} CRE p.285 lists RG2 separately ("[II] Bałaban, T.: Renormalization group approach to lattice gauge field theories. II. Cluster expansions. Commun. Math. Phys. 116, 1–22 (1988)") and still cites RG2's material under [I]; the identification below is by content.
  {#MD2.2.5.12-6} CRE's "Sect. 7 [I]" and "(I.7.1)"–"(I.7.13)" (CRE pp.277–278, the only pages of pp.243–285 with these citations) match RG2 Sect. 2 under (7.n) ↔ RG2 (2.n).
  {#MD2.2.5.12-7} For "Sect. 6 [I]": (I.6.41) ↔ RG2 (1.41), and (I.6.34) ↔ RG2 (1.34) by the form of the analyticity space (CRE (3.43) has the form of RG2 (1.34), U^c_{k+1}(Y,(1+β)α₀,(1+β)α₁,α₀)).
  {#MD2.2.5.12-8} The lemma numbers do not follow the equation rule: "Lemmas 5, 6 [I]" are identified with RG2's lemmas of Sect. 1; Lemma 1 (p.9) and Lemma 2 (p.11) are both read.
  {#MD2.2.5.12-9} Identified by content (the identity is not printed): Lemmas 5, 6 [I] are the two lemmas of RG2 Sect. 1, Lemmas 1 and 2 in order.
  {#MD2.2.5.12-10} CRE p.276 says the terms of (I.6.41) satisfy "exactly all the conditions of those lemmas", with the analyticity space (I.6.34) replaced by (3.43); RG2 (1.34) is in the statement of Lemma 1 (p.9), (1.41) in that of Lemma 2 (p.11, analytic "on the space (1.34)"), and RG2 Sect. 1 has no other lemma.
  {#MD2.2.5.12-11} Only this content is used, so the numbering is immaterial.
  {#MD2.2.5.12-13} Content: Lemma 1 localises the difference E_k(U_k(e^{iB′}V^{(k)})) − E_k(U_k(V^{(k)})) ((1.33)); Lemma 2 localises 𝐏^{(k)}(g_k, U_{k+1}, B) together with the bracketed terms of (1.41), as V_k = ½⟨Q(Y,B)B,B⟩ + V″_k ((1.42)).
  {#MD2.2.5.12-14} The evidence: RG2 (2.1) is the Mayer expansion, (2.11)–(2.13) the exponentiated expansion, (1.41) the localisation of Lemma 2, and RG2 p.15 prints "|(7.14)|" for the bound of (2.14) (transcriber's note there).
  {#MD2.2.5.12-15} RG2's introduction: "This expansion is described in Sect. 2".
- {#MD2.2.5.13} So (c)–(d) run RG2 (2.1)–(2.12) on the measure (3.27) at s = t = 1, with CRE's localised action (pp.276–277) for Σ𝐕_k(Y,B), CRE's cover (pp.275–276) and χ^{(k)} of CRE (3.16), p.268.

{#MD2.2.5.14} *(c) The expansion with marked supports.* Run RG2 (2.1)–(2.11) on I(𝒳):
- {#MD2.2.5.15} (2.1) Mayer expansion of exp Σ_Y𝐕_k(Y): unchanged, with 𝒳 multiplying the integrand.
- {#MD2.2.5.16} (2.2) Y₀ := ∪_{Y∈𝐃}Y ∪ D_J^#.
  {#MD2.2.5.16-1} Here D_J^# is the smallest union of cubes of the partition π_k (CRE p.278: "Z̄_0^c is the union of all cubes from π_k, such that they do not intersect Z_0, or intersect it along a two-dimensional edge at most") that contains in its interior every bond on which some Y_{G_i}, i ∈ J, depends.
  {#MD2.2.5.16-2} It is unique, being the intersection of all such unions (p.276's cover {□} overlaps and has several sizes, so a smallest union of its cubes need not be unique).
  {#MD2.2.5.16-3} This is the convention RG2 p.12 uses for P ("bonds of P have to be contained in the interior of Z_0").
  {#MD2.2.5.16-4} Z₀ is the smallest localisation domain containing Y₀ and P. D_J^# is a union of such cubes, so Z₀ is formed as in RG2.
  {#MD2.2.5.16-5} The enlargement from ∪D_i to D_J^# costs a bounded factor per cube in D2.4's count.
  - {#MD2.2.5.17} D2.4(2) counts "π_{k+1}-cubes" of RG2's 𝐃_{k+1}.
    {#MD2.2.5.17-1} *CRE p.278's π_k.* The families are different: π_j is the cubes "of a size M" in the scale of T_{L^{−j}} (RG1 p.257), of side ML^jη in CRE's η-scale (CRE p.275), and a π_{k+1}-cube is "of the size LM in the scale corresponding to the lattice T_η" (RG2 p.13), the union of L⁴ cubes of π_k (RG2 p.19 sums over "(L+2)^4 cubes □′ from π_k").
    {#MD2.2.5.17-2} P.278 uses π_k only to formulate the condition that "the domains Z_i do not intersect Z_0 along a cube, or a wall of a cube" as Z_i ⊂ Z̄_0^c.
    {#MD2.2.5.17-3} Z_0, …, Z_n "satisfy all the conditions described in Sect. 7 [I] in connection with the formula (7.11)" (p.277), so under RG2's numbering of [I] they are unions of π_{k+1}-cubes.
    {#MD2.2.5.17-4} For such unions the two formulations agree.
    {#MD2.2.5.17-5} The π_k-lattice refines the π_{k+1}-lattice (both have side a power of L and nested centres), so Z_i ⊂ Z̄_0^c if and only if every π_k-subcube q of every π_{k+1}-cube Q of Z_i meets Z_0 in a set of dimension ≤ 2.
    {#MD2.2.5.17-6} Q ∩ Z_0 is Q or a union of faces of Q, since Q and Z_0 are made of cubes of one lattice, and each face of Q of dimension ≥ 3 is a union of faces of subcubes of the same dimension.
    {#MD2.2.5.17-7} So this holds if and only if Q ∩ Z_0 has dimension ≤ 2, which is the condition stated with π_{k+1}-cubes.
    {#MD2.2.5.17-8} So the index does not change the condition, and D2.4(2)'s count in π_{k+1}-cubes is the count of RG2's polymers.
    {#MD2.2.5.17-9} D_J^#, a union of π_k-cubes, enters only through Z₀, its π_{k+1}-hull with P.
- {#MD2.2.5.18} (2.3) the decomposition of χ on Y₀^{c*}.
  {#MD2.2.5.18-1} CRE's χ^{(k)} is a product of sup-tests at δ_k over cubes (p.268, (3.16): χ({sup_{b∈(□′^{∼2})^{(k)*}}|A_k(b)| < δ_k})), and each test is on single-bond values |A_k(b)|, so it is a product of per-bond indicators.
  {#MD2.2.5.18-2} (2.3)'s decomposition then applies bond by bond, with CRE's thresholds in place of RG2's ε_1/g_k.
- {#MD2.2.5.19} (2.4)–(2.6) conditioning on Z₀ᶜ: the integrand F(Z₀,B)𝒳 is localised in Z₀ with respect to B, which is all that (2.5) uses. 𝒳 is a function of the conditioned Z₀-variable B, since D_J^# ⊂ Z₀, and the X-variables enter only through Γ_k.
  {#MD2.2.5.19-1} So (2.5)–(2.6) hold with 𝒳 inside G.
- {#MD2.2.5.20} (2.8) s-localisation of C^{(k)}(Z₀), (C^{(k)})^{1/2}, Δ_k: unchanged. 𝒳 carries no s-parameter, so H(Z,Z₀) now also contains 𝒳, and its external-field dependence is localised in Z together with the arcs and blocks on which the Y_{G_i} depend ((4)(e) *Locality*).
- {#MD2.2.5.21} (2.9)–(2.10) factorisation.
  {#MD2.2.5.21-1} RG2 states (2.10) for the components of Z ("From the definition of H(Z) it is also clear").
  {#MD2.2.5.21-2} With 𝒳 it holds over *linked components*: call two components of Z linked if some D_i meets both (a group with several components gives a disconnected D_i).
  {#MD2.2.5.21-3} The Mayer factors, the χ-factors, the conditioned Gaussian integrals at s(σᶜ) = 0 and the factors of 𝒳 all split over linked components, by the same argument.
  {#MD2.2.5.21-4} A linked component with no slot of J has the vacuum activity H(Z) of (2.11).
  {#MD2.2.5.21-5} One with slot set J(M) ≠ ∅ has a *marked activity* H̃(M) with values in ⊗_{i∈J(M)}End(V_π).
- {#MD2.2.5.22} (2.11) Hence I(𝒳) = Σ_𝔐 (⊗_{M∈𝔐}H̃(M))·Ξ(𝔐), where 𝔐 runs over the families of pairwise compatible (ζ = 1) marked linked polymers whose slot sets partition J, and Ξ(𝔐) := Σ ∏H(Z) over the families of vacuum polymers compatible with each other and with every M ∈ 𝔐.
  {#MD2.2.5.22-1} The tensor product is over slots, so the order of the factors does not matter.
  {#MD2.2.5.22-2} I(1) = Ξ := Ξ(∅).

{#MD2.2.5.23} *(d) The ratio (Bałaban's exponentiation formula, RG2 (2.12)).* Under CRE p.279's vacuum statements, which give the smallness that RG2 (2.12) uses ("If the activities H(Z) … are sufficiently small, then the polymer expansion can be exponentiated according to the well-known formula"),
{#MD2.2.5.24} Ξ(𝔐)/Ξ = exp(−Σ_{𝒞≁𝔐}φ^T(𝒞)), φ^T(Z₁,…,Z_n) := (1/n!)ρ^T(Z₁,…,Z_n)H(Z₁)⋯H(Z_n),
{#MD2.2.5.25} the sum over the ordered vacuum clusters 𝒞 = (Z₁,…,Z_n) of which some Z_j is incompatible with some M ∈ 𝔐.
{#MD2.2.5.25-1} This is the same formula, applied to Ξ and to the gas of vacuum polymers compatible with 𝔐, whose cluster sum is that of Ξ minus the clusters incompatible with 𝔐.
{#MD2.2.5.25-2} The restricted gas has the activities H(Z)·1[Z compatible with 𝔐], so D2.4(2)'s Kotecký–Preiss condition passes to it; for one marked domain this is CRE p.278's restricted exponentiation.
- {#MD2.2.5.26} *Per-polymer form (exact).* For a cluster 𝒞 let S_𝔐(𝒞) := {M ∈ 𝔐 : 𝒞 ≁ M} and s := |S_𝔐(𝒞)|.
  {#MD2.2.5.26-1} Put
  - {#MD2.2.5.27} Ψ(M) := Σ_{𝒞≁M}φ^T(𝒞), all clusters incompatible with M;
  - {#MD2.2.5.28} Ψ_≥(T) := Σ_{𝒞≁M for every M∈T}φ^T(𝒞), for T ⊆ 𝔐;
  - {#MD2.2.5.29} Q_{k+1}(𝔐) := exp(Σ_{T⊆𝔐,|T|≥2}(−1)^{|T|}Ψ_≥(T)).
  {#MD2.2.5.30} Then Ξ(𝔐)/Ξ = ∏_{M∈𝔐}e^{−Ψ(M)}·Q_{k+1}(𝔐).
  {#MD2.2.5.30-1} Proof: a cluster with s ≥ 1 appears s times in Σ_MΨ(M) and once in Σ_{𝒞≁𝔐}, and Σ_{T⊆S_𝔐(𝒞),|T|≥2}(−1)^{|T|} = (1−1)^s − 1 + s = s − 1.
  {#MD2.2.5.30-2} So both sides have the exponent −Σ_{𝒞≁𝔐}φ^T, and Q_{k+1}(𝔐) = exp(Σ_𝒞(s−1)_+φ^T(𝒞)).
  {#MD2.2.5.30-3} The rearrangement is absolutely convergent: a cluster lies in 2^s − 1 − s of the Ψ_≥(T) with |T| ≥ 2, and s ≤ 9|supp 𝒞| ≤ 9Σ_j|Z_j|, because the M are pairwise compatible and each M ∈ S_𝔐(𝒞) contains a cube of supp 𝒞 or one of its wall-neighbours, at most 9 per cube in d = 4 (ζ = 0 for a shared wall, RG2 p.14), the cubes and walls being those of π_k ((c)).
  {#MD2.2.5.30-4} On the finite torus s ≤ |𝔐| < ∞, so the rearrangement converges absolutely whenever Σ_{𝒞≁𝔐}|φ^T(𝒞)| < ∞, which CRE p.279's same-way clause gives.
  {#MD2.2.5.30-5} The Kotecký–Preiss form of D2.4(2), with 2^s ≤ e^{d(𝒞)}, gives the bounds uniform in 𝔐.
  - {#MD2.2.5.31} Ψ(M) depends on M alone, and Ψ_≥(T) on T alone (with the fields).
    {#MD2.2.5.31-1} So Q_{k+1} is a product of genuine |T|-body factors, which is the form (6)(c) needs.
- {#MD2.2.5.32} The self-energy e^{−Ψ(M)} is put into the marked activity: Ĥ(M) := e^{−Ψ(M)}H̃(M).

{#MD2.2.5.33} *(e) Result (k ≤ N, real outer variables independent of the integrated field A).*
{#MD2.2.5.34} ⟨𝒳⟩_{1,1} = Σ_𝔐 Q_{k+1}(𝔐)·⊗_{M∈𝔐}Ĥ(M), so ⟨T⟩_{1,1} = Σ_𝔐 Q_{k+1}(𝔐)·dim(π)^{−1}(contraction of ⊗_MĤ(M) with the A-independent factors of T).
- {#MD2.2.5.35} Each M is a new *group* at step k+1, possibly with several intervals of C (one per slot in J(M)); its insertion Ĥ(M) is a tensor over its slots and depends on M alone.
  {#MD2.2.5.35-1} The hard core is ζ, the soft interaction is Q_{k+1}.
  {#MD2.2.5.35-2} This is the class form of D2.0(3) with these changes, settled in (6):
  - {#MD2.2.5.36} insertions may be multi-interval tensors: (6)(d);
  - {#MD2.2.5.37} Q_{k+1}, the self-energies e^{−Ψ(M)} and the H̃(M) depend on U_{k+1} through the vacuum activities, and on the outer fluctuation field A_k on Ω_{k+1}∩Λ_{k+1}ᶜ, through −⟨A, C*Δ^{(k)}CA_k⟩, 𝐏^{(k)}(g_k, (A_k, A)) and V^{(k)}(S_{k+1}, (A_k, A)) in (3.27).
    {#MD2.2.5.37-1} In the slot variables this is the dependence on σ_k ((6)(b6)), and the reference extraction of (6)(c) is taken at ω′ = 0;
  - {#MD2.2.5.38} the marked polymers have no hard core with the supports of the untouched old insertions, which take no part in the expansion: (6)(d)'s second rule merges each untouched old insertion whose domain is incompatible with a constituent of a group into that group, an exact regrouping.
- {#MD2.2.5.39} |Q_{k+1}(𝔐)| ≤ exp(Σ_𝒞(s−1)_+|φ^T(𝒞)|) ≤ ∏_{M}exp(Σ_{𝒞≁M}|φ^T(𝒞)|) and |Ψ(M)| ≤ Σ_{𝒞≁M}|φ^T(𝒞)|.
  {#MD2.2.5.39-1} Under the Kotecký–Preiss form of D2.4(2) at the single-cube test sets the exponent is at most c|M| ((b); D2.4(2)(g); the weaker a(M⁺) ≤ 9c|M| also holds).
  {#MD2.2.5.39-2} The comparison c|M| ≤ νσ(M)/16 with the form of D2.0(3)'s norms is D2.4's count.
- {#MD2.2.5.40} *Exactness.* (c) is an identity on the finite torus.
  {#MD2.2.5.40-1} (d) uses the absolute convergence of the vacuum cluster expansion: Bałaban's construction as presented (CRE pp.275–279), under CRE p.279's same-way clause; the Kotecký–Preiss form of D2.4(2) is used for the bounds only.
  {#MD2.2.5.40-2} No bound on 𝒳 is used beyond boundedness on the support (as in (2)).
- {#MD2.2.5.44} *Polymers meeting Λ_{k+1}ᶜ.* Marked and vacuum polymers that meet Λ_{k+1}ᶜ or older regions, where the conditioning domain and the propagators are those of CRE's multi-domain construction, are treated in WILSON_IT1_D26_CLOSURE_2026_10_24.md §2.1–2.4 (the species rule; ω′-groups O(b_k) in the collar; CRE p.261's boundary potentials, from CRE p.261, Theorem 1, and RG2 pp.4–7; the vacuum gas by CRE p.277's Kotecký–Preiss statement, with its boundary-polymer bound p.277 l.19–23 for the polymers meeting Λ_{k+1}ᶜ) and §4 (kind (γ)).

### (6) The integration: output in class D(k+1) {#MSD2.2.6}

{#MD2.2.6.1} *(0) Input and output.* Input: the identity of (2), 𝒲_{k+1} = ⟨F⟩_{1,1} with F composed with ψ_{k+1}, and (5)(e), ⟨T⟩_{1,1} = Σ_𝔐Q_{k+1}(𝔐)·dim(π)^{−1}(contraction of ⊗_MĤ(M)).
{#MD2.2.6.1-1} Output: the class form of D2.0(3) at step k+1 on every labelled term of ρ_{k+1}.
{#MD2.2.6.1-3} The sizes, D(k+1)(ii), (ii′), and the norms, are D2.4's count and D2.6's.

{#MD2.2.6.2} *(a) The bijection ψ_{k+1} (the step-(k+1) form of V4 Lemma boundary-bijection).*
- {#MD2.2.6.3} *The map.* For b ∈ S_{k+1}^{(k)*}, ψ_b is p.269's change of variables: g_kA_k(b) = log(e^{ig_kA_k^{new}(b)}e^{−iω_b𝐇^{(k)}(b)}), with ω_b := g(A_k^{new}(b)) for b ∈ (R_{k+1}^{∼2}∩S_{k+1})^{(k)*} and ω_b := 1 on the other bonds of S_{k+1}^{(k)*} (p.269: "For bonds in (R_{k+1}^{∼2}∩S_{k+1})^{(k)*} we take the change of variables given by the formula (1.22), with 𝐇^{(k)}(b) instead of 𝐇_{1,Ax}(b).
  {#MD2.2.6.3-1} For the remaining bonds we take the simpler change of variables with the function g(A_k′(b)) replaced by 1"). log is the chart logarithm. g is CRE p.252's function at (g_k, δ_k): 0 ≤ g ≤ 1, g = 0 on |A| ≤ (4/3)g_k^{−1}δ_k, g = 1 where |e^{ig_kA} − 1| ≥ (5/3)δ_k.
  {#MD2.2.6.3-2} One such g with |Dg| ≤ 6g_k/δ_k is fixed by V4's construction (the paragraph after (native-source-exact-boundary-map)) with (g₀, δ₀) replaced by (g_k, δ_k).
  - {#MD2.2.6.4} *CRE p.267's (g_k, δ_k).* p.269 says only "(1.22), with 𝐇^{(k)}(b) instead of 𝐇_{1,Ax}(b)", and does not restate g's parameters.
    {#MD2.2.6.4-1} (g_k, δ_k) follows from the index shift: the variable is A_k′ = g_kA_k (p.267) and the threshold of the step-k tests is δ_k ((3.16)).
    {#MD2.2.6.4-2} It is used only through |Dg| ≤ 6g_k/δ_k and the two support conditions.
- {#MD2.2.6.5} *The star sets.* X^{(k)*} is CRE p.247's X* = X∖{b₀(c) : c ∈ X^{(1)}} at step k+1: the bonds of the scale-k lattice with at least one endpoint in X, minus the bonds b₀(c) for c with at least one endpoint in X^{(k+1)} (p.247: "with at least one end-point belonging to □′^{∼2}, except the bonds b₀(c) for c, such that at least one end-point belongs to (□′^{∼2})^{(1)}").
  {#MD2.2.6.5-1} CRE Sect. 3 writes (k)* in (3.3) and (3.16) without restating the definition.
  {#MD2.2.6.5-2} RG1 pp.267–268 print the elimination: "We perform the same operation as in the first step, namely using the δ-functions δ(Q̃B′) we eliminate the variables B′(b₀(c)), c ∈ T^{(k+1)}" (quoted as printed), so there is no variable A_k(b₀(c)) for p.269's "each bond variable A_k(b), b ∈ S_{k+1}^{(k)*}" to act on. p.269's statement that the changes "transform the function χ_k′(S_{k+1}) into the same function" presupposes it too: on a bond b₀(c) the test would involve B′(b₀(c)), a function of all the free variables of the corridor, and no bondwise change could act on it in this way.
  {#MD2.2.6.5-3} So the convention is forced by the print (CRE p.247: "More generally, for a set X").
- {#MD2.2.6.6} *Input 1, the bond form.* For b ∈ S_{k+1}^{(k)*}, V_k(b) = e^{ig_kA_k(b)}V^{(k)}(b).
  - {#MD2.2.6.7} The step-k field is e^{iB′}V^{(k)} on B(Γ_{k+1}), with B′ = g_kCA_k − hD̃(g_kCA_k) (D2.1(1)).
  - {#MD2.2.6.8} RG1 p.267: "The function hB is equal to 0 everywhere, except the set {b₀(c): c ∈ T^{(k+1)}}".
    {#MD2.2.6.8-1} RG1 pp.267–268: "namely using the δ-functions δ(Q̃B′) we eliminate the variables B′(b₀(c)), c ∈ T^{(k+1)}.
    {#MD2.2.6.8-2} Denoting the remaining variables by B we have B′ = CB".
    {#MD2.2.6.8-3} So (CA_k)(b) = A_k(b) and (hD̃)(b) = 0 off the bonds b₀(c).
    {#MD2.2.6.8-4} CRE p.267 transfers this to the multi-domain operators ("exactly the same as … Sect. 2 [I]", D2.1(1)).
  - {#MD2.2.6.9} A bond b of S_{k+1}^{(k)*} is not a b₀(c).
    {#MD2.2.6.9-1} If b = b₀(c), b lies in the corridor {b : b_− ∈ B(c_−), b_+ ∈ B(c_+)} (RG1 p.267), so its endpoint in S_{k+1} lies in the block of an endpoint of c.
    {#MD2.2.6.9-2} That block lies in S_{k+1}, since the cube partitions are nested (p.265: the "partition is compatible with all the other partitions"; at step 1, V4 sec:main-result *Hypotheses*, p.257's "compatible with all other partitions").
    {#MD2.2.6.9-3} So c has an endpoint in S_{k+1}^{(k+1)}, which b ∈ S_{k+1}^{(k)*} excludes.
  - {#MD2.2.6.10} *Which bonds carry A_k.* p.267 integrates dA_k|_{Ω_{k+1}} and dV_k|_{Ω_{k+1}ᶜ} separately.
    {#MD2.2.6.10-1} Input 1 and ψ_b are stated for the bonds of S_{k+1}^{(k)*} that carry an A_k variable; on the others the variable is V_k, which p.269's change ("each bond variable A_k(b)") does not touch.
- {#MD2.2.6.11} *Input 2, the tests.* For b ∈ S_{k+1}^{(k)*}, let □′(b) ⊂ S_{k+1} be an L²M₂R_{k+1}-cube containing an endpoint of b.
  {#MD2.2.6.11-1} It exists: S_{k+1} = (Ω_{k+1}∖Ω_{k+1}^{∼−1}) ∪ R_{k+1} is a union of such cubes, the layer by the nesting and R_{k+1} by (3.16).
  {#MD2.2.6.11-2} Then b ⊂ □′(b)^∼ ⊆ □′(b)^{∼2}.
  {#MD2.2.6.11-3} On the support, the factor χ_k′(□′(b)) of χ_k′(S_{k+1}) in (3.21) is 1.
  {#MD2.2.6.11-4} By (3.3), p.265, that is |V_k(b′)(V^{(k)}_{□′(b)}(b′))^{−1} − 1| < 2δ_k for b′ ∈ (□′(b)^{∼2})^{(k)*}.
  {#MD2.2.6.11-5} At b′ = b, with Input 1, this reads |e^{ig_kA_k(b)}Z_b − 1| < 2δ_k, where Z_b := V^{(k)}(b)(V^{(k)}_{□′(b)}(b))^{−1}.
- {#MD2.2.6.12} *Input 3, the size of Z_b.* (3.13), p.267, is stated for every cube □′ ⊂ Ω_{k+1}: |V^{(k)} − V^{(k)}_{□′}| < (4dL)²(1+β₀)B₃ε_k on □′^∼.
  {#MD2.2.6.12-1} Hence |Z_b − 1| < C_Zδ_k, with C_Z := (4dL)²(1+β₀)B₃A₀/A₁, since δ_k = (A₁/A₀)ε_k (p.265; confirmed by (3.19), p.268, "O(1)44d²B₃²(1+β₀)ε_k exp(−R_k) = O(1)44d²B₃²(1+β₀)(A₀/A₁)exp(−R_k)δ_k") and the factors are unitary.
  - {#MD2.2.6.13} At step 1, V4 has |Z_b − 1| < 2δ₀ from (B1) (proof of Lemma boundary-bijection).
    {#MD2.2.6.13-1} The input here is weaker.
    {#MD2.2.6.13-2} C_Z exceeds 2 when A₁/A₀ is small.
    {#MD2.2.6.13-3} C_Z depends on d, L, B₃, β₀, and A₀/A₁ only, so it is fixed before the coupling.
- {#MD2.2.6.14} *Input 4, the size of 𝐇^{(k)}.* p.269: 𝐇^{(k)} is "bounded on the set S_{k+1} by O(1)ε_k exp(−R_k)".
  {#MD2.2.6.14-1} So |𝐇^{(k)}(b)| ≤ O(1)(A₀/A₁)e^{−R_k}δ_k ≤ δ_k/40 once e^{R_k} ≥ 40·O(1)A₀/A₁.
  {#MD2.2.6.14-2} This holds for small g_k, uniformly in k by g_k ≤ (1+β₀)g_K (#MD2.0.5.2-2), with this O(1) independent of k.
  - {#MD2.2.6.15} Three inputs enter here.
    {#MD2.2.6.15-1} The k-independence of the O(1): Bałaban's "absolute constant O(1)" (RG1 pp.255, 279; RG2 p.8), with the explicit constant of (3.19) and p.269's "with similar bounds".
    {#MD2.2.6.15-2} g_k ≤ (1+β₀)g_K (#MD2.0.5.2-2).
    {#MD2.2.6.15-3} And "bounded on the set S_{k+1}" for the bonds of S_{k+1}^{(k)*} with an endpoint outside S_{k+1}: the bonds of a set are those that intersect it (RG I p.251 l.26–27, the convention CRE p.255 l.20–21 adopts), so these bonds are bonds of S_{k+1} and the printed bound covers them, as V4 uses p.251's bound at step 1 (Lemma boundary-bijection, *The inputs*; proved in Lemma axial-boundary-field).
- {#MD2.2.6.16} *The constants.* r_y := (π/2)(2 + C_Z), r_K := r_y + 1 and r_F := (π/2)(r_K + 1/40).
  {#MD2.2.6.16-1} The condition on the coupling is δ_k ≤ δ_G(C_Z) := min(log(3/2)/(√N r_F), r_G/(√N(r_K + 1/40))), with r_G and N as in V4's lemma.
  {#MD2.2.6.16-2} It holds for g_K small, since δ_k → 0 uniformly in k (#MD2.0.5.2-2).
- {#MD2.2.6.17} *The lemma.* Put 𝒯_b := {A ∈ 𝔤 : h(g_kA) < ϱ_G, |e^{ig_kA}Z_b − 1| < 2δ_k}.
  {#MD2.2.6.17-1} Under Inputs 1–4 and δ_k ≤ δ_G(C_Z), V4's statements (a)–(c) hold for every b ∈ S_{k+1}^{(k)*}.
  {#MD2.2.6.17-2} So Ψ_{k+1} maps the domain of the new variables bijectively onto that of the old ones, DΨ_{k+1} is invertible there, and the Jacobian is ∏_b|det Dψ_b|.
  {#MD2.2.6.17-3} The domain of the new variables is defined as in V4's proof (*The consequences*): the preimage of the old domain, with the new variables restricted to ∏_b𝒲_b ("the inclusion ⊆ being the definition").
- {#MD2.2.6.18} *The proof is V4's, with these changes.*
  - {#MD2.2.6.19} (a) Use Input 2 at the actual A_k, and the chart condition from (3.14), p.267: |V_k′ − 1| < 2δ_k + (4dL)²(1+β₀)B₃ε_k = (2 + C_Z)δ_k ≤ r_G/√N, so V_k′ lies in the chart domain and |A_k′(b)| ≤ r_yδ_k < ϱ_G, under δ_k ≤ δ_G(C_Z) (A_k′ = g_kA_k on free bonds, by Input 1).
    {#MD2.2.6.19-1} No further coupling condition enters.
  - {#MD2.2.6.20} (b) |e^{iy} − 1| < (2 + C_Z)δ_k, so |y| ≤ r_yδ_k.
    {#MD2.2.6.20-1} Take K := {|x| ≤ r_Kδ_k}.
    - {#MD2.2.6.21} K lies in the chart ball and e^{ix}W(x) in the chart domain, since (r_K + 1/40)δ_k ≤ r_G/√N.
    - {#MD2.2.6.22} |F(x)| ≤ r_Fδ_k, and ‖DR‖ ≤ ½ on {|X| ≤ r_Fδ_k}, since e^{√N r_Fδ_k} − 1 ≤ ½.
      {#MD2.2.6.22-1} So |F(x) − x| ≤ 2|𝐇^{(k)}(b)| ≤ δ_k/20.
    - {#MD2.2.6.23} Hence T(x) := x − F(x) + y maps K into itself, |T(x)| ≤ (r_y + 1/20)δ_k < r_Kδ_k.
      {#MD2.2.6.23-1} Brouwer's theorem gives a fixed point.
  - {#MD2.2.6.24} (c) |e^{ix} − 1| < (2 + C_Z + 1/40)δ_k, so |x| ≤ (π/2)(2 + C_Z + 1/40)δ_k ≤ r_Kδ_k, and both points lie in K.
    - {#MD2.2.6.25} The injectivity estimate |e^{ix} − e^{ix′}| ≤ (6/δ_k)|x − x′|·(δ_k/40) = (3/20)|x − x′| < ½|x − x′| does not involve C_Z.
    - {#MD2.2.6.26} The same holds for the differential.
  - {#MD2.2.6.27} V4's remark that the proof depends on the tolerance of Z_b only through these constants (*The inputs*) is what is used here.
- {#MD2.2.6.28} *Scope.* This is input (a) of (2)(iii).
  {#MD2.2.6.28-2} The bijection uses only r_G, ϱ_G = π/√N, and the √N comparisons of norms, so it holds for every compact simple G ⊂ U(N) (V4's *Norm facts* in the proof of Lemma boundary-bijection).

{#MD2.2.6.29} *(b) Cov(k+1).*
- {#MD2.2.6.30} *Slot variables.* The outer variables of step k+1 are ω′ := (ω, σ_k).
  {#MD2.2.6.30-1} Here σ_k is the old field A_k on the outer bonds of Ω_{k+1}∩Λ_{k+1}ᶜ, called the *slot variable* of ω_k.
  {#MD2.2.6.30-2} After (2)(iii) the integration variables on S_{k+1}^{(k)*} are the new variables A_k^{new}, and the slot variable receives σ_k(b) = ψ_b(A_k^{new}(b); 𝐇^{(k)}(b)), with ψ_b of (a).
  {#MD2.2.6.30-3} On the other outer bonds σ_k = A_k.
  {#MD2.2.6.30-4} Every insertion is a function of the slot variables; ψ_{k+1} only says which values they receive.
  {#MD2.2.6.30-5} So D(k+1)'s analyticity in the outer fields (D(k+1)(iii), *Outer fluctuation fields*) is analyticity in σ, and A_k^{new} is never complexified. g in ψ_b is not analytic in A_k^{new}, and this does not matter.
- {#MD2.2.6.31} *Statement.* Every insertion Ĥ(M) of (5)(e) is the value at (𝐔, 𝐉) = (U_{k+1}, J_{k+1}) of a function Ĥ(M)(𝐔, 𝐉, ω′), analytic jointly (by (e), not by (b)).
  {#MD2.2.6.31-1} It transforms slot by slot: Ĥ(M)(𝐔^u, R(u)𝐉, R(u)ω′) = (⊗_{i∈J(M)}π(u(x_i)))Ĥ(M)(𝐔, 𝐉, ω′)(⊗_{i∈J(M)}π(u(x′_i)))^{−1}, with x_i, x′_i the endpoints of the arc of slot i.
  {#MD2.2.6.31-2} Q_{k+1}(𝔐) and the self-energies e^{−Ψ(M)} are invariant.
  {#MD2.2.6.31-3} Here u is any G-valued gauge transformation of the fine lattice.
  {#MD2.2.6.31-4} It acts on a field on the scale-j lattice through its values at the sites of that lattice, (R(u)A)(x,x′) = R(u(x))A(x,x′) (PBG (3.28)).
  {#MD2.2.6.31-5} So R(u) acts pointwise and is orthogonal.
  - {#MD2.2.6.32} At real configurations 𝐉 = J_{k+1} = J(U_{k+1}), and J(U^u) = R(u)J(U) (PBG p.395, after (3.30)).
    {#MD2.2.6.32-1} So nothing changes there. 𝐉 is a variable for RG1 p.272's reason: bounds for D*D "do not hold", "and this is the reason why we do not formulate second order regularity conditions, as in (1.9) [14], (2) [15], but we replace the expression J_j by the new variable 𝐉".
    {#MD2.2.6.33-1} CRE p.250 keeps the invariance of the density under gauge transformations of the new field apart from the invariance of the effective action under (1.17), and CRE (3.17)–(3.18) show that the two minimisers differ by u_{k+1,□′} and a small field exp iL^{−1}η𝐇_{k+1,□′}, with 𝐇_{k+1,□′} "bounded by … ≤ 44d²B₃²(1+β₀)exp(−R_k)ε_k on □′^{∼2}" (CRE p.268).
- {#MD2.2.6.34} *The functions of (𝐔, 𝐉).* RG1 p.272, after (3.12): "we replace J_{k+1} by the variable 𝐉, and in the remaining expressions we replace U_{k+1} by the new variable 𝐔".
  {#MD2.2.6.34-1} RG1 p.273, for the operators: "we replace the configurations U_{k+1}, J_{k+1} occurring in operators there by the configurations 𝐔, 𝐉".
  {#MD2.2.6.34-2} So every operator of (4)–(5) that depends on (U_{k+1}, J_{k+1}) is taken at (𝐔, 𝐉).
  {#MD2.2.6.34-3} The covariance is checked on these operators in (b1)–(b4).
- {#MD2.2.6.35} *(b1) The operators, and RG2's s-localised operators.*
  - {#MD2.2.6.36} PBG (3.30)–(3.34), pp.395–396, for every gauge transformation u: Δ^η(U^u) = R(u)Δ^η(U)R(u^{−1}), the same for Δ_U^η, G′, R, Δ_a and G; and (Q_j′(U^u)R(u)λ)(y) = R(u(y))(Q_j′(U)λ)(y).
    {#MD2.2.6.36-1} For the gauge-field averaging operators Q_j(U): "inspecting the definitions … we can see that the equalities (3.32) hold again" (p.396).
  - {#MD2.2.6.37} Restriction to a set (X ↦ ΩXΩ) and multiplication by a scalar function commute with R(u), since R(u) acts pointwise.
    {#MD2.2.6.37-1} So local inverses of these operators on cubes and domains are covariant too.
  - {#MD2.2.6.38} The walk terms.
    {#MD2.2.6.38-1} PBG p.412: "Each term in this expansion is a product of factors".
    {#MD2.2.6.38-2} Its examples are K(h′_□)G′_□h′_□, h_□C_□h_□ and □̃Q′[G′_{□₀}, h′²_{□₀}]G′_{□₀}Q′*h_□C_□h_□ (pp.412–413), the last with a leading characteristic function.
    {#MD2.2.6.38-3} Each factor is built from these local operators, the scalar partitions of unity h_□, h′_□, and characteristic functions. On scalar fields K(h) = hΔ′_a − Δ′_ah ((3.88), p.409), with Δ′_a = (Δ_U^η + Q′*aQ′)↾_{Ω₀} = G′^{−1} (p.394 l.24, l.43); on gauge fields K(h) = hΔ_a − Δ_ah − P₁(∂h) ((3.104), p.414), with P₁(∂h) = DPD*h − hDPD* ((3.101)) and DPD* = DD* − DRD* (p.414 l.3); and C_□ = (Q′G′_□²Q′*)^{−1}, with G′_□ the operator G′ of the sequence {Ω_n(□)} (p.409 l.3).
    {#MD2.2.6.38-3-1} So K(h_□) and C_□ are covariant by (3.30)–(3.34) and, for D, the transport law of p.395 l.49, R(u) commuting with scalar multipliers.
    {#MD2.2.6.38-4} So every walk term T_ω satisfies T_ω(𝐔^u) = R(u)_{target}T_ω(𝐔)R(u)^{−1}_{source}, where target and source are the lattices on which T_ω takes and receives values ("act between different scales", p.413).
    {#MD2.2.6.38-5} So does every sum Σ_ωc_ωT_ω with scalar coefficients.
    - {#MD2.2.6.39} This is printed for PBG's expansion (3.98) (Theorem 3.9).
      {#MD2.2.6.39-1} G′ is (3.90) (Theorem 3.7, p.409), with the factors K(h_□)G′_□h_□ above.
      {#MD2.2.6.39-2} For the expansions of G, H, H₀, G̃, Δ_k, C^{(k)}(Z₀), and G̃₃(x) of RG2 p.13 the covariance is Bałaban's: RG2 p.11, "the operations in this section preserve the gauge invariance", and RG2 p.21, "By Lemma 2, and the transformation properties of the operators in (2.14) with respect to gauge transformations, e.g. see (3.28)–(3.34) [13], the expressions (2.14) are gauge invariant with respect to all G-valued transformations".
      {#MD2.2.6.39-3} PBG p.408's "all the results of these theorems are gauge invariant" concerns the bounds of PBG Theorems 3.1–3.3 and is not cited for this.
  - {#MD2.2.6.40} The s-parameters.
    {#MD2.2.6.40-1} RG2 p.3: "for a random walk ω localized in X̃_0^5∪X̃_1^5∪…∪X̃_n^5 we take the {Δ_1,…,Δ_m} of all cubes from σ_0 which intersect this localization domain, and we multiply the term in (1.6) corresponding to ω by s(Δ_1)⋯s(Δ_m)"; p.13: "The parameters s(Δ), Δ∈σ_0, are introduced into the operators as before".
    {#MD2.2.6.40-2} (C^{(k)})^{1/2} is the integral (2.7) of the resolvents (xI + C*Δ_kC)^{−1} and the powers (C*Δ_kC)^n.
    {#MD2.2.6.40-3} The resolvent is expanded by (3.185) of [13], with the added term −½x‖χ*(QA + D̄μ(QA))‖². χ* is "the characteristic function of the set of bonds T_1^{(k)}∖{b₀(c): c ∈ T^{(k+1)}}" (p.13), a scalar multiplier on bonds.
    {#MD2.2.6.40-4} Q, D̄, and μ are those of [13] (3.159)–(3.170), pp.428–430: Q is the gauge-field averaging operator, covariant by p.396 l.7 ("the equalities (3.32) hold again"); D̄ = D̄^k := D_{Ū^k}^{L^kη} (p.418 l.29–32), with (R_y(V)D̄μ)(Γ_{y,x}) = R(V(Γ_{y,x}))μ(x) − μ(y) at V = Ū^k (p.430 l.21); and μ(B) is the linear function (3.169), μ(y) = Σ_{x∈B(y)}L^{−d}(R_y(V)B)(Γ_{y,x}) and μ(x) = R(V(Γ_{x,y}))(μ(y) − (R_y(V)B)(Γ_{y,x})) for x ∈ B(y), x ≠ y.
    {#MD2.2.6.40-5} Ū^k is covariant (V4 sec:c4-11-5, RG1 (0.6)), so D̄ is covariant as D_𝐔 is ((b4), the transport law of PBG p.395); (R_y(V^u)R(u)B)(Γ_{y,x}) = R(u(y))(R_y(V)B)(Γ_{y,x}) by the same law, so (3.169) gives μ(R(u)B; V^u)(x) = R(u(x))μ(B; V)(x).
  - {#MD2.2.6.41} Hence, for every complex s, H(s), G̃(s), H₀(s), C^{(k)}(Z₀, s), (C^{(k)})^{1/2}(s) and Δ_k(s) are covariant, and Γ_k(Z₀, s), a scalar, is invariant.
    {#MD2.2.6.41-1} This is what RG2 p.21 calls "the transformation properties of the operators in (2.14) with respect to gauge transformations, e.g. see (3.28)–(3.34) [13]".
  - {#MD2.2.6.42} *The operator C and B′.* RG1 p.268: "C is the operator determined by the configuration V^{(k)}".
    {#MD2.2.6.42-1} V^{(k)} = M^k(𝐔) transforms by u at the scale-k sites: M({uU_jv}) = uM({U_j})v for unitary site gauges with no smallness restriction (V4 sec:c4-11-5; V4 Lemma global-average(ii)).
    {#MD2.2.6.42-2} Q̃ is the linear part of the block constraint at V^{(k)}, and h is "an inverse of a coefficient at the variable B′(b₀(c)) in (Q̃B′)(c)" (RG1 p.267).
    - {#MD2.2.6.43} Q̃ and h (one line each).
      {#MD2.2.6.43-1} Differentiating the covariance of M at e^{iB′}V gives Q̃(V^u)R(u) = Ad(u(c_−))Q̃(V), with Q̃ based at c_− as in the proof of V4 Lemma global-average(ii).
      {#MD2.2.6.43-2} Hence h_{V^u}(c) = Ad(u(b₀(c)_−))h_V(c)Ad(u(c_−))^{−1}.
    - {#MD2.2.6.44} C is fixed by Q̃CB = 0 with (CB)(b) = B(b) on the free bonds ((a), Input 1). b₀(c) enters only the constraint of c (V4 Lemma global-average(i)), and its coefficient there is invertible (RG1 p.267: "h is uniquely defined by these conditions").
      {#MD2.2.6.44-1} R(u) preserves the free bonds, so R(u)C(𝐔)R(u^{−1}) satisfies the same two conditions at 𝐔^u, and uniqueness gives C(𝐔^u) = R(u)C(𝐔)R(u^{−1}).
    - {#MD2.2.6.45} D̃.
      {#MD2.2.6.45-1} Its equation is LQ̃B′ + C̃(B′) = LQ̃B (RG1 p.267), with C̃ the nonlinear part of the block constraint.
      {#MD2.2.6.45-2} C̃ is covariant as Q̃ is, so R(u)D̃ solves the equation at (V^u, R(u)B).
      {#MD2.2.6.45-3} The set in which RG1 p.267's "exactly one solution" holds is a ball in the sup norm of the pointwise matrix norm.
      {#MD2.2.6.45-4} RG1 p.267 proves it "following the proofs in the above mentioned papers", which are "Sect.
      {#MD2.2.6.45-5} C [15], Sect. E [14]" (p.267; [15] is VAR, [14] is REG, RG1 p.299).
      {#MD2.2.6.45-6} In VAR, (51), p.285, poses the fixed-point problem on |A′| < ε₃(L^jη)^{−1} on Ω_j, X = 0 on Λ₀ and |X| < ε₃/B₀ on 𝔅_k, and p.286 finds "exactly one fixed point".
      {#MD2.2.6.45-7} Every unitarily invariant matrix norm (the operator norm, or the tr XY norm of PBG pp.391–392) has |uXu^{−1}| = |X| for u ∈ U(N), also for complex X. So the ball is invariant, the transformed fixed-point map is R(u)TR(u)^{−1}, and uniqueness gives D̃(V^u, R(u)B) = R(u)D̃(V, B).
      {#MD2.2.6.45-8} The same follows from the power-series recursion, whose terms (RG1 p.267: "D̃(B) has an expansion beginning with quadratic terms, and D̃^{(2)}(B)=C̃^{(2)}(B)") are covariant term by term.
      {#MD2.2.6.45-9} The data domain is invariant: RG1 p.263, "The spaces U_j^c(X,α_0,α_1) are, by the definition, gauge invariant also"; RG1 p.276's "so that the configurations after the transformations belong to proper spaces also" is a proviso on G^c-valued u and is not needed for G-valued u.
    - {#MD2.2.6.46} So B′(𝐔^u, R(u)A_k) = R(u)B′(𝐔, A_k).
    - {#MD2.2.6.47} Δ^{(k)}: RG1 (2.11) is ⟨H₁hC̃^{(2)}(B′), J⟩ − ½𝐆^{(2)}(B′) − ½⟨H₁B′, Δ₁H₁B′⟩ = −½⟨B′, Δ^{(k)}B′⟩, "see the definition (3.156) [13] with the δ-function gauge fixing term replaced by the exponential one".
      {#MD2.2.6.47-1} The first and third terms are invariant by PBG (3.30) (for J), by the average (for h and C̃^{(2)}), and by the walk terms above (for H₁ and Δ₁).
      {#MD2.2.6.47-2} The second is RG1 (2.5), p.266 l.9–13: 𝐆^{(2)}(B′) = Σ_{y∈T^{(k+1)}}Σ_{x∈B(y),x≠y}|B̃′(y,x)|², with B̃′(y,x) the linear part of Ṽ′(y,x) = (V′V^{(k)})(y,x)(V^{(k)}(y,x))^{−1}, B′ = (1/i)log V′ (p.265 l.34), and V(y,x) the averaged contour variable M({V(Γ)}_{Γ∈𝐆(y,x)}) of RG1 (0.11), p.253. Under (𝐔, B′) ↦ (𝐔^u, R(u)B′), V^{(k)} ↦ (V^{(k)})^u (#MD2.2.6.42-1) and the covariance of M give Ṽ′(y,x) ↦ u(y)Ṽ′(y,x)u(y)^{−1}, so B̃′(y,x) ↦ R(u(y))B̃′(y,x), and |B̃′(y,x)|² is unchanged, the form on 𝔤^c being Ad(G)-invariant.
      {#MD2.2.6.47-3} So ⟨R(u)B′, Δ^{(k)}(𝐔^u)R(u)B′⟩ = ⟨B′, Δ^{(k)}(𝐔)B′⟩, and Δ^{(k)} being symmetric, Δ^{(k)}(𝐔^u) = R(u)Δ^{(k)}(𝐔)R(u)^{−1}. Hence C^{(k)}(𝐔) = (C*Δ^{(k)}C)^{−1}, its restrictions, and C^{(k)}(Λ_{k+1}) are covariant.
- {#MD2.2.6.48} *(b2) 𝐇(s,·).*
  - {#MD2.2.6.49} RG2 (1.2)–(1.4): 𝐇_k(B′) = H₀B′ + 𝐀₀ − HD(H₀B′ + 𝐀₀), with D(A′) = C(A′ − HD(A′)) and 𝐀₀ + G̃(δV/δA′)(H₀B′ + 𝐀₀) = 0.
    {#MD2.2.6.49-1} These equations "are determined by local, analytic functions, and nonlocal propagators H, H₀, G̃" (RG2 p.2).
  - {#MD2.2.6.50} The local function C of (1.3) is the nonlinear part of the logarithmic average: VAR p.285, "Q_j(ηA) = L^jηQ_jA + C_j(L^jηA), |C_j(L^jηA)| ≤ C₂(L^jη)²|A|²", with C(A′) = C_j(L^jηA′) on Λ_j (VAR p.286).
    {#MD2.2.6.50-1} Q_j(U, ηA) = (1/i)log of the average (CMP98 Proposition 4, (4)(d)), and its linear part Q_j, are covariant by V4 sec:c4-11-5 and the conjugation equivariance of the chart logarithm (proof of V4 Lemma global-average(ii)).
    {#MD2.2.6.50-2} So C is covariant.
  - {#MD2.2.6.51} V is VAR (80), built from J, Δ_π, H, D and the higher-order part V₀ of the action.
    {#MD2.2.6.51-1} J is covariant by PBG (3.30).
    {#MD2.2.6.51-2} Δ_π is PBG (3.119), p.419: ⟨A, Δ_πA⟩ = ⟨A − DG′RD*A, Δ(A − DG′RD*A)⟩, covariant by PBG (3.30)–(3.34).
    {#MD2.2.6.51-3} The action is invariant by PBG (3.29).
    {#MD2.2.6.51-4} V₀ is the sum of the homogeneous orders ≥ 3 in A of the invariant action, and PBG p.395's expansion ("expanding both sides of the above equality in A we get a sequence of equalities between homogeneous polynomials of the same order") gives the invariance of each order, hence of V₀.
    {#MD2.2.6.51-5} So V(𝐔^u, R(u)𝐉; R(u)A′) = V(𝐔, 𝐉; A′), and δV/δA′ is covariant.
  - {#MD2.2.6.52} *Uniqueness on invariant balls.* RG2 (1.13)–(1.14) solve (1.3) by contraction on {X : |X| < 4C₂ε₂²} for |A′| < ε₂.
    {#MD2.2.6.52-1} RG2 (1.15)–(1.16) solve (1.4) on balls in max{|𝐀|, |∇𝐀|} for |B′| < ε₃.
    {#MD2.2.6.52-2} These are balls in sup norms of unitarily invariant pointwise norms, and |∇_{𝐔^u}R(u)𝐀| = |R(u)∇_𝐔𝐀| = |∇_𝐔𝐀| since ∇_{𝐔^u}R(u) = R(u)∇_𝐔.
    {#MD2.2.6.52-3} So the balls are invariant under R(u), also for complex 𝐀, and so is the data domain (RG1 p.263, the spaces U_j^c are "by the definition, gauge invariant").
  - {#MD2.2.6.53} With (b1) at the same s, R(u)D and R(u)𝐀₀ solve the equations at (𝐔^u, R(u)𝐉, R(u)B′), and they lie in the invariant balls.
    {#MD2.2.6.53-1} The transformed fixed-point maps are R(u)TR(u)^{−1}, so uniqueness gives 𝐇(s; 𝐔^u, R(u)𝐉, R(u)B′) = R(u)𝐇(s; 𝐔, 𝐉, B′) for every s in RG2's domain.
    {#MD2.2.6.53-2} At s = 1 this is the covariance that RG1 p.276 uses ("in the function 𝐇_k(B′) the variables 𝐉, B are replaced by R(u_{k+1}^{−1})R(v^{−1})𝐉, R(u_{k+1}^{−1})R(v^{−1})B"); p.276 asserts the invariance of (3.25)–(3.26), not this covariance by itself.
- {#MD2.2.6.54} *(b3) w(s), from CMP98 (85)–(106).* W_y(R(u)𝐇, 𝐔^u) = u·W_y(𝐇, 𝐔)·u^{−1} pointwise, for every complex 𝐇 with |𝐇| < a₁.
  - {#MD2.2.6.55} Here U₀ = 𝐔 and U₁ = e^{iη𝐇}, so U₁(b) ↦ u(b_−)U₁(b)u(b_−)^{−1}: U₁ is based at the initial point of each bond.
  - {#MD2.2.6.56} The one-step average (89), p.31, (R̄_{0,c_−}V₁)^{−1}(V̄₁V₀)_c(V̄₀)_c^{−1}R̄_{0,c}(R̄_{0,c_+}V₁), is based at c_−.
    {#MD2.2.6.56-1} Under (V₀, V₁) ↦ (V₀^u, u(·_−)V₁u(·_−)^{−1}), (V̄₁V₀)_c(V̄₀)_c^{−1} is conjugated by u(c_−), since both averages are covariant (V4 sec:c4-11-5; V4 Lemma global-average(ii)).
    {#MD2.2.6.56-2} The point averages R̄_{0,x}V₁, averages over a block of the quantities transported to x ((85); (105) for the logarithmic mean), are conjugated by u(x), since the chart logarithm and exp are conjugation equivariant.
    {#MD2.2.6.56-3} The middle transport R̄_{0,c} is the adjoint action of (V̄₀)_c, and (V̄₀)_c ↦ u(c_−)(V̄₀)_cu(c_+)^{−1}, so it carries conjugation by u(c_+) of R̄_{0,c_+}V₁ to conjugation by u(c_−).
    {#MD2.2.6.56-4} So all four factors of (89) are conjugated by u(c_−).
  - {#MD2.2.6.57} By induction through (90)–(91), with V₀ = Ū₀^j covariant, every Ū̄₁^j is based at its initial point in the same way.
  - {#MD2.2.6.58} In (106) each bracket [(…)^{−1}(R̄^j_{0,x_{j+1}}Ū̄^j_1)(Γ_{x_{j+1},x_j})] is conjugated by u(x_{j+1}).
    {#MD2.2.6.58-1} R(U₀^u(Γ_{x_{j+1},x}))^{−1} carries conjugation by u(x_{j+1}) to conjugation by u(x).
    {#MD2.2.6.58-2} CMP98 (56)–(57), p.27: R(X)Y = XYX^{−1}, R(X)R(Y) = R(XY), and R(X)^{−1} = R(X^{−1}); with U₀^u(Γ_{y,x}) = u(y)U₀(Γ_{y,x})u(x)^{−1} (p.27 l.2's bond law, multiplied along Γ_{y,x}) this gives R(U₀^u(Γ_{y,x})) = R(u(y))R(U₀(Γ_{y,x}))R(u(x)^{−1}), as PBG p.395 l.49 prints.
    {#MD2.2.6.58-3} So each factor of (106), and the product, is conjugated by u(x).
  - {#MD2.2.6.59} The same holds at the block centres, where CMP98 (87) gives the value w(y) = (R̄_{0,y}U₁)^{−1} (CMP98 writes u(y); renamed here to keep it apart from the gauge transformation u).
    {#MD2.2.6.59-1} It is a point average at y, so it is conjugated by u(y).
    {#MD2.2.6.59-2} So w need not be 1 there, and no such property is used.
  - {#MD2.2.6.60} *Scope.* (b3) covers the blocks on which (106), or its j-step form of (4)(d), gives w.
    {#MD2.2.6.60-1} The bonds crossing ∂Λ_j (VAR's Λ_j) are case (B) of D2.1(4); their covariance goes to D2.6 with them.
- {#MD2.2.6.61} *(b4) The new insertions before integration.* By (4)(e), Y_G is the ordered product along I(G) of old insertions at (e^{iη𝐇(s,B′)}𝐔, 𝐉′, R(w(s))ω) and of transports of e^{iη𝐇(s,B′)}𝐔, differentiated in s and taken at s = 0 off G. Here 𝐇(s, B′) = 𝐇(s; 𝐔, 𝐉, B′), and for k ≥ 2 𝐉′ = 𝐉′(𝐔, 𝐉, 𝐀) at 𝐀 = 𝐇(s, B′) is (4)(f)'s second argument of (3.13); at k = 1 there is no 𝐉′.
  - {#MD2.2.6.62} *The covariance of 𝐉′.*
    - {#MD2.2.6.63} RG1 p.272: (3.10) substitutes 𝐉′ = J̃(e^{iξ𝐀}U_{k+1}), with J̃(U) := D_U^{ξ*}ξ^{−2}π Im∂U; (3.11) is J̃(e^{iξ𝐀}U) = J̃(U) + D_U^{ξ*}D_U^ξ𝐀 + 𝐅(U, 𝐀) "for any regular configuration U", with 𝐅 "a local operator depending on U, ∂U, 𝐀, ∇_U^ξ𝐀 only"; then "we replace the operator D*D by D*D+DRD*=D*D+DD*−DPD*=Δ_U^ξ−P₁+(lower order, local operator)"; (3.12) is J̃(U_{k+1}) = (L^{j−1}η)³J_{k+1}; and J_{k+1} is replaced by 𝐉 and U_{k+1} by 𝐔.
    - {#MD2.2.6.64} So (3.13)'s second argument is (L^{j−1}η)³𝐉 + (D_𝐔^*D_𝐔 + D_𝐔R(𝐔)D_𝐔^*)𝐀 + 𝐅(𝐔, 𝐀), with 𝐅₁(𝐔, 𝐀) := 𝐅(𝐔, 𝐀) + (D*D + DRD* − Δ_𝐔^ξ + P₁)𝐀, the lower-order operator absorbed. 𝐅₁ is not defined in the print; with this 𝐅₁, (3.13) follows from (3.10)–(3.12) as printed.
      {#MD2.2.6.64-1} P₁ is not needed in this form.
    - {#MD2.2.6.65} The covariance of 𝐉′ does not depend on RG1 (3.13)'s 𝐅₁: with D*D not replaced, the second argument is (L^{j−1}η)³𝐉 + D*D𝐀 + 𝐅, which is covariant by the same bullets.
      {#MD2.2.6.65-1} So RG1 (3.13)'s 𝐅₁ only identifies (3.13)'s second argument.
    - {#MD2.2.6.66} J̃ is covariant ((3.12) is printed at U_{k+1} only).
      {#MD2.2.6.66-1} At G-valued U, ∂U^u(p) = u(x_p)∂U(p)u(x_p)^{−1}, with x_p the base point of p; Im and the projection onto 𝔤 commute with unitary conjugation; D_{U^u}R(u) = R(u)D_U and R(u) is orthogonal, so D_{U^u}^*R(u) = R(u)D_U^*.
      {#MD2.2.6.66-2} Hence J̃(U^u) = R(u)J̃(U).
      {#MD2.2.6.66-3} (The D of D*D maps bonds to plaquettes and the D of DRD* maps sites to bonds; both are covariant by the transport law below.) J̃ is a rational function of the entries of the U(b) and U(b)^{−1} (on G, X* = X^{−1}), and (3.10) uses it at the complex configuration e^{iξ𝐀}U_{k+1}, so it is taken in this rational form.
      {#MD2.2.6.66-4} The law is a rational identity in the entries that holds on G-valued configurations, which are Zariski dense in the G^c-valued ones (a compact real form is Zariski dense in its complexification).
      {#MD2.2.6.66-5} So it holds at every G^c-valued configuration where J̃ is defined.
      {#MD2.2.6.66-6} This rational form is Bałaban's continuation, by uniqueness of holomorphic continuation off the totally real G-valued configurations.
      {#MD2.2.6.66-7} Compactness and connectedness suffice; simplicity is not used.
    - {#MD2.2.6.67} D_𝐔 and R(𝐔) are covariant: R by PBG (3.33), "R(U^u)=R(u)R(U)R(u^{−1})"; D_𝐔 because it is built from the transports, R(U^u(Γ_{y,x})) = R(u(y))R(U(Γ_{y,x}))R(u^{−1}(x)) (PBG p.395), so D_{𝐔^u}R(u) = R(u)D_𝐔, and D_𝐔^* likewise.
      {#MD2.2.6.67-1} They extend to complex 𝐔 by the same Zariski-density argument, since each is a rational function of the entries (R through the finite-volume inverse G′, by Cramer's rule).
      {#MD2.2.6.67-2} For the other operators of (b1) at complex 𝐔: walk-series sums, (C^{(k)})^{1/2} and the fixed points D̃, D, 𝐀₀ are not rational.
      {#MD2.2.6.67-3} Zariski density is applied to each rational building block (finite-volume and local inverses, each walk factor, each resolvent of RG2 (2.7)), and the law passes to the convergent sums and integrals; for the fixed points, (b1)–(b2)'s uniqueness on invariant balls is used, which does not use real 𝐔.
    - {#MD2.2.6.68} e^{iξR(u)𝐀}𝐔^u = (e^{iξ𝐀}𝐔)^u (as in the next bullet).
      {#MD2.2.6.68-1} So 𝐅(𝐔^u, R(u)𝐀) = J̃((e^{iξ𝐀}𝐔)^u) − J̃(𝐔^u) − D_{𝐔^u}^*D_{𝐔^u}R(u)𝐀 = R(u)𝐅(𝐔, 𝐀), and hence 𝐉′(𝐔^u, R(u)𝐉, R(u)𝐀) = R(u)𝐉′(𝐔, 𝐉, 𝐀) for every G-valued u.
  - {#MD2.2.6.69} By (b2), e^{iη𝐇(s; 𝐔^u, R(u)𝐉, R(u)B′)}𝐔^u = (e^{iη𝐇(s; 𝐔, 𝐉, B′)}𝐔)^u.
    {#MD2.2.6.69-1} By the bullet above at 𝐀 = 𝐇(s; 𝐔, 𝐉, B′), the 𝐉-argument of the old insertions becomes R(u)𝐉′.
    {#MD2.2.6.69-2} By (b3), R(w′(s))R(u)ω = R(u)R(w(s))ω, with w′(s) the transform at the transformed data.
  - {#MD2.2.6.70} Cov(k) for the old insertions and the transport law then give Y_G(𝐔^u, R(u)𝐉, R(u)B′, R(u)ω) = π(u(x_G))Y_G(𝐔, 𝐉, B′, ω)π(u(x′_G))^{−1}, for every s, so also after the s-integrals.
    {#MD2.2.6.70-1} Derivatives and integrals in s commute with a fixed conjugation.
    {#MD2.2.6.70-2} The untouched old insertions are Cov(k)'s.
  - {#MD2.2.6.71} The transformed arguments stay in Cov(k)'s domain: R(u) is bondwise isometric and real, so it maps the polydisc of radius r around a real support point x onto the polydisc of radius r around R(u)x, which satisfies the same bondwise bounds (D(k)(iii)'s neighbourhood form), and the spaces of the background are gauge invariant, RG1 p.263: "The spaces U_j^c(X,α_0,α_1) are, by the definition, gauge invariant also" (unions of G^c-orbits, p.262;
    {#MD2.2.6.71-1} this replaces the appeal to RG1 p.276, whose "so that the configurations after the transformations belong to proper spaces also" is a proviso on G^c-valued u). |R(u)𝐉| = |𝐉| and |R(u)𝐉′| = |𝐉′|, since R(u) is orthogonal pointwise.
    {#MD2.2.6.71-2} For (3.14′) at the transformed data: |R(u)𝐀| = |𝐀|, |∇_{𝐔^u}R(u)𝐀| = |∇_𝐔𝐀| ((b2)), and (D*D + DRD*)(𝐔^u)R(u) = R(u)(D*D + DRD*)(𝐔), since D_{𝐔^u}R(u) = R(u)D_𝐔 and D*_{𝐔^u}R(u) = R(u)D*_𝐔 for both D's (#MD2.2.6.66-1–#MD2.2.6.66-5) and R(𝐔^u) = R(u)R(𝐔)R(u)^{−1} (PBG (3.33), at complex 𝐔 by #MD2.2.6.67-3).
    {#MD2.2.6.71-3} RG1's P₁ occurs on pp.272, 273, and 281 only and is defined neither there nor in REG, VAR, CMP 98, PBG, PRT1, PRT2, RG2, CRE, LFR I, or LFR II.
    {#MD2.2.6.71-4} RG1 p.272 l.22 prints D*D + DRD* = D*D + DD* − DPD* = Δ_U^ξ − P₁ + (lower order, local operator), with P = I − R (PBG p.399 l.4).
    {#MD2.2.6.71-5} (3.14′) uses the left side, which is covariant (#MD2.2.6.71-2). P₁ enters D2 only through Bałaban's bounds on |P₁𝐇| combined with this identity (#MD2.2.4.91-2), both being statements about the same operator.
    {#MD2.2.6.71-6} PBG's P₁(A) of (3.76), p.405, the A-expansion remainder of DRD*, the P₁(∂h) of PRT1 p.37 and PBG p.414, and the sets P₁ of CRE p.246, LFR I p.195, and LFR II p.381 are other objects.
- {#MD2.2.6.72} *(b5) The integration: the argument of RG2 p.21 with insertions.* A term of the marked activity H̃(M) is RG2's (2.14) with the factors of 𝒳 over J(M) inserted.
  {#MD2.2.6.72-1} In it make the changes of variables B ↦ R(u)B and X ↦ R(u)X in dμ_{C^{(k)}(Z₀,s)}(B) and dμ₀(X).
  {#MD2.2.6.72-2} Their Jacobian is 1, since R(u) is orthogonal.
  {#MD2.2.6.72-3} (Notation: RG2's localisation parameters are written s(Δ), t(Y) here, to keep them apart from the slot variable σ_k.
  {#MD2.2.6.72-4} At complex parameters dμ_{C^{(k)}(Z₀,s)} is not a measure; the parameters enter after B = (C^{(k)})^{1/2}(s)X (RG2 (2.6)–(2.8)), so the change X ↦ R(u)X in the Gaussian dμ₀ suffices, with (C^{(k)})^{1/2}(s) covariant by (b1).)
  - {#MD2.2.6.73} The Gaussian densities and Γ_k(Z₀, σ) are invariant by (b1); the pushforward of μ_{C(𝐔)} under R(u) is μ_{R(u)C(𝐔)R(u)^{−1}} = μ_{C(𝐔^u)}.
    {#MD2.2.6.73-1} The χ-factors are invariant, since they are bondwise functions of |B(b)| (RG2 p.12 l.18–19, RG1 (2.9)) and |R(u)B| = |B|.
    {#MD2.2.6.73-2} The localised terms 𝐑_k, 𝐁_k and A(1/g_k²(·) − 1/g_k², ·) of CRE pp.276–277 are invariant ((b6)).
    {#MD2.2.6.73-3} The 𝐕_k(Y) are invariant by RG2 Lemma 2's last statement (p.11: "The functions 𝐕_k(Y,𝐔,𝐉,B) … are gauge invariant with respect to the simultaneous gauge transformations (I.3.29)").
    {#MD2.2.6.73-4} (I.3.29) is 𝐔 → 𝐔^u, 𝐉 → R(u)𝐉, B → R(u)B (RG1 p.276), so 𝐉 is transformed with the rest. 𝒳 is covariant slot by slot by (b4).
  - {#MD2.2.6.74} The Cauchy integrals in s(Δ), t(Y) do not involve u.
    {#MD2.2.6.74-1} So H̃(M) is covariant slot by slot, and the vacuum activities H(Z) are invariant, which is RG2 p.21's statement.
  - {#MD2.2.6.75} Ψ(M), Ψ_≥(T) and Q_{k+1}(𝔐) are functions of the H(Z) and of supports fixed by the labels ((5)(d)), so they are invariant (the argument applies verbatim to Ψ(M) and Ψ_≥(T)). Ĥ(M) = e^{−Ψ(M)}H̃(M) is covariant.
- {#MD2.2.6.76} *(b6) The new outer field.* The record of (3.25)–(3.27) above and (5)(e) have σ_k entering also through 𝐏^{(k)}(g_k, (A_k, A)) and V^{(k)}(S_{k+1}, (A_k, A), 𝐇^{(k)}), and V^{(k)} depends on A and on the non-covariant 𝐇^{(k)}.
  {#MD2.2.6.76-1} In the slot variables these are handled by CRE p.269's action change ((2)(iii)(b)): the exponent of (3.25) satisfies
  {#MD2.2.6.77} [old exponent at (A_k^{new}, A)] + V^{(k)}(S_{k+1}, (A_k^{new}, A), 𝐇^{(k)}) = [old exponent at (σ_k, A)] + log|det Dψ_{k+1}(A_k^{new})|,
  {#MD2.2.6.78} with "old exponent" the exponent before p.269's change of variables.
  {#MD2.2.6.78-1} So V^{(k)} is not a channel of its own, and σ_k enters through the old exponent at (σ_k, A), in three channels, each covariant under (𝐔, 𝐉, A, σ_k) ↦ (𝐔^u, R(u)𝐉, R(u)A, R(u)σ_k):
  - {#MD2.2.6.79} (The channels are disjoint: the curly bracket of (3.25) is split into its 𝐄_k-part, which goes to the third channel with 𝐏^{(k)}, and its 𝐑_k, 𝐁_k and A(·) parts, which form the first channel.
    {#MD2.2.6.79-1} B′ in the observable is not part of the exponent.)
  - {#MD2.2.6.80} The 𝐑_k, 𝐁_k and A(1/g_k²(·) − 1/g_k², ·) parts of the bracket, at the configuration U_k(e^{iB′}V^{(k)}): gauge invariant (the Wilson action, PBG (3.29); for 𝐑^{(j)} property (iii) of CRE p.259 l.43, which p.260 l.21 extends to it, and for 𝐁^{(j)} property (iii) of p.261 l.60; CRE pp.276–277 localise them), with B′ covariant by (b1).
  - {#MD2.2.6.81} the cross term −⟨A, C*Δ^{(k)}Cσ_k⟩ of (3.27), invariant: ⟨R(u)A, R(u)C*Δ^{(k)}Cσ_k⟩ = ⟨A, C*Δ^{(k)}Cσ_k⟩ by (b1).
  - {#MD2.2.6.82} 𝐏^{(k)}(g_k, (σ_k, A)) + {𝐄_k-part} = Σ_{Y∈𝐃_k}𝐕_k(Y, U_{k+1}, (σ_k, A)), RG2 (1.41) (RG2's {⋯} is RG1's 𝐄_k-bracket; Lemma 2), with B = (σ_k, A) and CRE's localised action for Σ𝐕_k ((5)(b)).
    {#MD2.2.6.82-1} It is invariant by Lemma 2's last statement: "The functions 𝐕_k(Y,𝐔,𝐉,B), and both terms in (1.42), are gauge invariant with respect to the simultaneous gauge transformations (I.3.29)".
  - {#MD2.2.6.83} The Jacobian depends on A_k^{new} and 𝐇^{(k)} only, not on A (𝐇^{(k)} is built from the minimiser V^{(k)}_{Λ_{k+1}ᶜ∩Λ_k}).
    {#MD2.2.6.83-1} So it factors out of the A-integral, cancels in ⟨·⟩_{1,1}, and stays in Bałaban's density of the outer variables; it is part of no insertion.
    {#MD2.2.6.83-2} The same holds for the quadratic form in σ_k alone, which is A-independent.
  - {#MD2.2.6.84} ψ_{k+1} gives the values of σ_k and is not part of the function.
    {#MD2.2.6.84-1} So R(u) acts on ω′ = (ω, σ_k) jointly, as Cov(k+1) states.
    {#MD2.2.6.84-2} (6)(e)'s *V^{(j)}* bullet, which treats V^{(j)} as a σ_j-dependence at frozen θ, is the same exponent written in σ_j.
  - {#MD2.2.6.85} The slot values on the support. σ_k = A_k, the old variable, so its bound on the support is CRE (3.14) directly ((e)).
    {#MD2.2.6.85-1} At later steps the background on the layer of σ_j can be complex, and then σ_j(b) = ψ_b(A_j^{new}(b); 𝐇^{(j)}(b)) is complex through 𝐇^{(j)}, by at most 2|𝐇^{(j)}(b)|/g_j in the sense of (a)'s proof step (b).
    {#MD2.2.6.85-2} CRE p.269 bounds 𝐇^{(j)} by O(1)ε_je^{−R_j} on S_{j+1}, as an analytic function of the background.
    {#MD2.2.6.85-3} Its size and its change at the complex backgrounds of later steps are (e)'s, #MD2.2.6.185–#MD2.2.6.196.
- {#MD2.2.6.86} *(b7) Representatives.* (Within Ax_{k+1}(𝔅_{k+1}, U_{k+2}) the representative is unique, REG p.79; CRE p.250's invariance is not used.) Let u be a G-valued gauge transformation fixing every block variable and independent of the next step's integration variable.
  {#MD2.2.6.86-1} By Cov(k+1), each closed word satisfies word(𝐔^u, R(u)𝐉, σ) = word(𝐔, 𝐉, R(u)^{−1}σ).
  {#MD2.2.6.86-2} So passing from 𝐔 to 𝐔^u rotates the slot values by the real R(u)^{−1}.
  {#MD2.2.6.86-3} R(u) is real and orthogonal, so |Re σ| and |Im σ| are kept bond by bond, and the rotated values satisfy the same support bounds.
  {#MD2.2.6.86-4} D(k+1) states its clauses for slot values satisfying those bounds, so it holds at 𝐔^u.
  {#MD2.2.6.86-5} The change of representative that actually occurs, v₁, is not of this kind (*Scope* below).
  {#MD2.2.6.86-6} No integration variable is changed, so no Jacobian and no invariance of the rest of the integrand is used.
  {#MD2.2.6.86-7} The w of (4)(c) at the next step acts on the slot values in the same way, R(w)σ, with the radius bound of (4)(c) and (e) for complex w.
  {#MOMGD.52} So every change of representative at the later steps acts on the insertions through their slot values, by R(u)^{−1} for the u above and by R(w) for (4)(c)'s w (#MD2.2.4.21).
  {#MD2.2.6.86-8} *Scope.* This covers changes of representative by a u that does not depend on the next step's integration variable.
  {#MD2.2.6.86-9} RG1 p.265's first transformation v₁ = U_{k+1}(Γ^{(k)})^{−1}Ū^{rep}_k(V_k)(Γ^{(k)}) depends on B′ exactly when ρ_k's hierarchical transports do; D(k)'s representative is in the hierarchical mean axial gauge, not axial relative to a B′-independent reference ((4)(d′), Step 1), so v₁ depends on B′ and goes through (4)(c)–(e) with w_tot = u_k^{−1}v₁ (#MD2.2.4.43-1).
  {#MD2.2.6.86-10} At a configuration 𝐔 of D(k+1)(iii)'s polydisc that is not the step-k output at its own data (a real point other than the centre, or a general complex point), v₁ = c₀(𝐔)v̂₁ with c₀(𝐔) the B′-independent mismatch between 𝐔 and the minimiser at its averages ((4)(d′), Step 8): c₀ is of this bullet's kind for the output at 𝐔.
  {#MD2.2.6.86-11} One step later, at (11)(c)(β)'s polydisc points with a″ ≠ 0, the D(k)-level mismatch of the evaluation point depends on (s, t, B′) and is not of this kind; it is charged to (4)(c)'s per-step margin on 𝒟^{sub} (#MD2.4.11.5).
  {#MD2.2.6.86-12} *G^c-valued u.* For a G^c-valued u fixing the block variables and independent of the integration variable, Cov(k+1) holds by analytic continuation: each closed word is analytic in u, the identity holds on G, and G is a totally real uniqueness set in G^c (the real points of a polydisc).
  {#MD2.2.6.86-13} The rotation R(u)^{−1} is then complex and does not preserve the polydisc around the real support, so D(k+1)'s ω-clause at 𝐔^u is the clause at 𝐔 in the rotated slot values: it holds for σ with R(u)^{−1}σ in the polydisc (word(𝐔^u, R(u)𝐉, σ) = word(𝐔, 𝐉, R(u)^{−1}σ), and the clause at 𝐔 needs its slot value R(u)^{−1}σ in the polydisc); u must lie in the connected domain of analyticity of the words, which c₀'s size |log c₀| = O(dι) gives ((4)(d′), Step 8).
  {#MD2.2.6.86-14} This is the covariant form of the ω-clause at complex configurations (D(k)(iii), *The ω-clause at complex configurations*), which reduces to the plain polydisc at real u.
  {#MD2.2.6.86-15} At the next step the same holds with B″: the rotation R(v₁(B″))^{−1}σ depends on the integration variable and goes through (4)(e)'s interpolation of R(w_tot(s))σ, with the size of (4)(d′), *Result* (#MOMGD.33-84–#MOMGD.33-86).

{#MD2.2.6.98} *(c) The scalar parts, D(k+1)(v).*
- {#MD2.2.6.99} *Where field dependence enters.* κ^{(k)} (D(k)(i)), 𝓔_k, and Q_k(𝔅) (D(k)(v)) are numbers, and they pass through (2)–(5) unchanged. ⟨·⟩_{1,1} is normalised, and its normaliser is CRE's ((2)), so (2)–(5) create no new scalar exponent.
  {#MD2.2.6.99-1} The self-energies e^{−Ψ(M)} are inside Ĥ(M), and insertions may depend on the field.
  {#MD2.2.6.99-2} So the only field-dependent scalar is Q_{k+1}(𝔐) = exp(Σ_{T⊆𝔐,|T|≥2}(−1)^{|T|}Ψ_≥(T; 𝐔, 𝐉, ω′)) at (𝐔, 𝐉) = (U_{k+1}, J_{k+1}) (RG2's activities are functions of (𝐔, 𝐉), p.15).
  {#MD2.2.6.99-3} This is the per-polymer form of (5)(d).
- {#MD2.2.6.100} *The reference.* Scalars are extracted at the flat reference (𝐔, ω′) = (1, 0), with the labels of the term.
  {#MD2.2.6.100-1} This is V4's extraction at step 1 (q°, E° at U°₁ = id, the reference-data paragraph of V4 Section joint-extraction).
  {#MD2.2.6.100-2} D(k)(v) then stands as written, and (4)–(5) stay as they are.
- {#MD2.2.6.101} *The extraction (exact).* Put Ψ°_≥(T) := Ψ_≥(T; 𝐔 = 1, 𝐉 = 0, ω′ = 0) and δΨ_≥(T) := Ψ_≥(T; 𝐔, 𝐉, ω′) − Ψ°_≥(T), and likewise Ψ°(M), δΨ(M). 𝐉 = 0 is the current of the flat background, J(1) = 0.
  {#MD2.2.6.101-1} The vacuum expansion of (5)(d) converges at (1, 0, 0): (𝐔, 𝐉) = (1, 0) satisfies (2.34)–(2.39) trivially, Bałaban's bounds are uniform on the space (RG2 p.6: "all the bounds above are uniform on the domain"; p.15, the activity estimated as an analytic function on U^c_{k+1}(X, α₀, α₁)), and ω′ = 0 removes the coupling term of (3.27).
  {#MD2.2.6.101-2} The Kotecký–Preiss form of D2.4(2) is applied at the reference point (1, 0, 0); by RG2 p.6's uniformity this is the same count as at the true background.
  {#MD2.2.6.101-3} It is derived in D2.4(2)(f) on ℓ₀ and, on a labelled term, for the subgas Z ⊂ Λ_{k+1}; on a labelled term ℓ ≠ ℓ₀ the full gas contains the polymers meeting Λ_{k+1}ᶜ, and there the convergence at (1, 0, 0), hence the definition of Ψ°_≥, Q°, and δΨ and the sup bound used for the localisation below, rests on CRE p.277 l.19–23's boundary-polymer bound (Lemma 3's form for the boundary polymers), as D2.6 closure §2.4 applies it.
  {#MD2.2.6.101-4} So Ψ°_≥(T) is defined, and it is a number given the labels and the supports of the M ∈ T; it depends on T alone.
  - {#MD2.2.6.102} The self-energies are split the same way: e^{−Ψ(M)} = e^{−Ψ°(M)}e^{−δΨ(M)}, with e^{−Ψ°(M)} a number given the labels and the support of M. So Ĥ(M) = e^{−Ψ°(M)}Ĥ′(M), Ĥ′(M) := (1 + (e^{−δΨ(M)} − 1))H̃(M); e^{−Ψ°(M)} stays in Ĥ(M), a number given the labels with |e^{−Ψ°(M)}| ≤ e^{c#(M)}, so it enters c_𝒢 = Y_𝒢(1, 0) of D2.3(2), the activities of the gas from which D2.3 extracts δm_{k+1} and z_{k+1}; Ĥ′(M) carries e^{−δΨ(M)}.
    {#MD2.2.6.102-1} *Localisation (exact).* δΨ(M) and δΨ_≥(T) are field-dependent (they vanish at (1, 0, 0) and are not constant), and unexpanded they depend on the fields on every cluster incompatible with M. With y_𝒞 := φ^T(𝒞; 𝐔, 𝐉, ω′) − φ^T(𝒞; 1, 0, 0), δΨ(M) = Σ_{𝒞≁M}y_𝒞 and δΨ_≥(T) = Σ_{𝒞≁every M∈T}y_𝒞, so e^{−δΨ(M)} = Σ_𝒦∏_{𝒞∈𝒦}(e^{−y_𝒞} − 1) and e^{ε_TδΨ_≥(T)} − 1 = Σ_{𝒦≠∅}∏_{𝒞∈𝒦}(e^{ε_Ty_𝒞} − 1), over the finite sets 𝒦 of such clusters (the set of clusters is infinite, D2.3(3); the expansion is exact since Σ_{𝒞≁M}|e^{±y_𝒞} − 1| ≤ Σ_{𝒞≁M}u_𝒞 ≤ 3c#(M) by D2.4(2)(g) in its sup form, u_𝒞 as in D2.4(12)(c)).
    {#MD2.2.6.102-2} The expansion is done before grouping: for fixed 𝒮 and fixed chosen sets 𝒦, the groups of (d), Ĥ(G) and Y_𝒢 are defined term by term.
    {#MD2.2.6.102-3} For the clusters that D2.6 closure §2.4 treats (those meeting Λ_{k+1}ᶜ or depending on ω′) the expansion of their part δΨ^{coll}(M) is §2.4's power series Σ_n(−δΨ^{coll}(M))^n/n!, and the product expansion over 𝒦 is applied to the other clusters ≁ M; both are exact, and each term carries one of them. φ^T(𝒞) depends on the external fields only on supp 𝒞 (RG2 p.14: "The function H(Z) is localized in the interior of Z with respect to the external gauge fields"; 𝐉 is an independent variable of Cov(k), #MD2.2.4.3, on which H(Z) depends only on its dependence set, RG2 p.5, D2.3(4)(Z-c);
    {#MD2.2.6.102-4} its ω′-dependence is D2.6's, below), so each term is a function of the fields on M's domain and ∪_{𝒞∈𝒦}supp 𝒞, the locality Cov(k+1) asks of an insertion; y_𝒞 is invariant by (b5).
    {#MD2.2.6.102-5} The clusters of the chosen sets are the *vacuum links*, with domain supp 𝒞: those of e^{−δΨ(M)} at M (T = {M}), those of e^{ε_TδΨ_≥(T)} − 1 at the first M of T ((d)); a cluster chosen by several of these factors is one link domain, with factor ∏ over the choosing factors, carried at each M_T of a choosing factor (D2.4(12)(c)'s pairs (T, 𝒞)).
    {#MD2.2.6.102-6} They enter Y_𝒢 as field-dependent factors; the vacuum occurrences of Q° and the old occurrences of Q_k(𝔅) are numbers given the labels.
  - {#MD2.2.6.103} Then, with ε_T := (−1)^{|T|}, Q_{k+1}(𝔐) = exp(Σ_Tε_TΨ°_≥(T))·∏_{T}(1 + (e^{ε_TδΨ_≥(T)} − 1)) = exp(Σ_Tε_TΨ°_≥(T))·Σ_𝒮∏_{T∈𝒮}(e^{ε_TδΨ_≥(T)} − 1), over the sets 𝒮 of subsets T ⊆ 𝔐 with |T| ≥ 2.
    {#MD2.2.6.103-1} The product is finite on the finite torus.
  - {#MD2.2.6.104} For fixed 𝒮, call two M linked if some T ∈ 𝒮 contains both.
    {#MD2.2.6.104-1} The classes of the generated equivalence relation are the *scalar-linked groups* 𝔊(𝒮).
    {#MD2.2.6.104-2} The factor ∏_{T∈𝒮}(e^{ε_TδΨ_≥(T)} − 1) splits over them, each factor depending on its T alone.
  - {#MD2.2.6.105} Q° := exp(Σ_Tε_TΨ°_≥(T)) = exp(Σ_𝒞(s_𝔐(𝒞) − 1)_+φ^T(𝒞; 1, 0, 0)) is the whole flat factor, a number given the labels; it is D2.3(3)'s vacuum part, expanded there in vacuum occurrences, and it is not split over the groups.
  - {#MD2.2.6.106} So ⟨𝒳⟩_{1,1} = Σ_𝔐Σ_𝒮 Q°·⊗_{G∈𝔊(𝒮)}Ĥ(G), with Ĥ(G) := ∏_{T∈𝒮_G}(e^{ε_TδΨ_≥(T)} − 1)·⊗_{M∈G}Ĥ(M), 𝒮_G := {T ∈ 𝒮 : T ⊆ G}, a tensor over the slots of G that depends on (G, 𝒮_G); the group label in the gas includes 𝒮_G.
    {#MD2.2.6.106-1} This is the unexpanded form; the definition used is its expansion term by term over the chosen sets 𝒦 (*Localisation* above), and the display holds for the sums.
- {#MD2.2.6.107} *Properties.* Q° is a number given the labels, which is (6)(c)'s part of D(k+1)(v); the rest of D(k+1)(v), 𝓔_{k+1} and the cluster form, is D2.3's. δΨ_≥(T) and δΨ(M) are invariant by (b5), so Ĥ(G) is covariant slot by slot, and Cov(k+1) is kept. δΨ_≥(T) is analytic where the vacuum expansion converges locally uniformly (Weierstrass), and it vanishes at (1, 0, 0).
- {#MD2.2.6.108} *Bounds.* The clusters meeting Λ_{k+1}ᶜ or depending on ω′ (att(k+1, coll)) are treated in WILSON_IT1_D26_CLOSURE_2026_10_24.md §2.4.
  - {#MD2.2.6.109} The multiplicity: a cluster 𝒞 enters 2^s − 1 − s of the Ψ_≥(T), s = |S_𝔐(𝒞)| ≤ 9#(supp 𝒞), # the number of π_{k+1}-cubes (D2.4(2) #MD2.4.2.12: |Z⁺| ≤ 9#(Z) for any union of π_{k+1}-cubes; (5)(d) states the bound with |supp 𝒞|).
    {#MD2.2.6.109-1} So Σ_{|T|≥2}|Ψ°_≥(T)| and Σ_{|T|≥2}|δΨ_≥(T)| are bounded with the weight 2^s ≤ e^{d(𝒞)} of the Kotecký–Preiss form of D2.4(2).
  - {#MD2.2.6.110} The sizes: |e^{ε_TδΨ_≥(T)} − 1| through |δΨ_≥(T)| ≤ Σ_{𝒞≁every M∈T}|φ^T(𝒞; 𝐔, 𝐉, ω′) − φ^T(𝒞; 1, 0, 0)|, and |δΨ(M)| likewise over 𝒞 ≁ M.
    - {#MD2.2.6.111} The vacuum-link factors need only the sup bound |e^{±y_𝒞} − 1| ≤ u_𝒞 = |y_𝒞|_sup e^{|y_𝒞|_sup}, |y_𝒞|_sup ≤ 2|φ^T(𝒞)|_sup (D2.4(12)(c)).
    - {#MD2.2.6.112} No per-cluster deviation factor is needed: the deviation factor of the dev species is supplied for Y^d_𝒢 = Y_𝒢 − c_𝒢T_𝐔 as a whole by D2.4(4)'s Cauchy step at the group's support X(𝒢), which contains the link supports, every vacuum-link factor vanishing at the flat point.
    - {#MD2.2.6.113} The gauge that Cauchy step uses is (LPG′) (D2.4(4), from CRE (3.17) and VAR Theorem 1, #MD2.4.4.24).
  - {#MD2.2.6.114} The bound |Q°| ≤ ∏_Ge^{θ(G)}, θ(G) := Σ_{M∈G}Σ_{𝒞≁M}e^{d(𝒞)}|φ^T(𝒞; 1, 0, 0)|, from the multiplicity bound; under the Kotecký–Preiss form of D2.4(2) θ(G) ≤ c|G|, as in (5)(e), with |G| := Σ_{M∈G}|M|, the number of cubes.
  - {#MD2.2.6.115} The species: dev when the clusters lie in the small-field region and depend on 𝐔 only; att(k+1, ·) when they meet Λ_{k+1}ᶜ or depend on ω′ (D2.6: WILSON_IT1_D26_CLOSURE_2026_10_24.md §2.1–2.2).
  - {#MD2.2.6.116} D2.3 extracts δm_{k+1} and z_{k+1} from the reference gas, whose activities c_𝒢 contain the e^{−Ψ°(M)} and whose interaction contains Q°'s occurrences.

{#MD2.2.6.117} *(d) Multi-slot insertions: merging along C.*
- {#MD2.2.6.118} *The issue.* Ĥ(G) is a tensor over the slots of G, one per group of (4)(e) that G contains.
  {#MD2.2.6.118-1} D(k)'s words have one insertion in End(V_π) per group, on one interval (IT-1 note §4: "insertions Y_W ∈ End(V_π), one per group").
  {#MD2.2.6.118-2} The groups are merged along C, which keeps the class of D2.0(3).
- {#MD2.2.6.119} *The arc hull (the linked hull).* For a slot i, let I_i be the arc of its group in (4)(e), and for a marked polymer M let I(M) be the smallest arc of C containing ∪_{i∈J(M)}I_i, by D2.1(4)'s rule.
  {#MD2.2.6.119-1} The *pieces* of a group are the arcs I(M) of its marked polymers, the intervals of its untouched old insertions and the arcs J_{W′} of the members of its old occurrences.
  {#MD2.2.6.119-2} The piece of every constituent of a marked polymer's vertex (M itself, each touched W ∈ 𝔅(M), each cluster assigned to M) is I(M): a touched interval is not a separate piece, it lies in I(M) by (4)(e).
  {#MD2.2.6.119-3} Two pieces are *joined* when a rule merges their constituents directly: a scalar link T is assigned to its first M (in a fixed order), and a vacuum occurrence 𝒞 to the first M of S_𝔐(𝒞), so that the assignment depends on T, not on the unexpanded clusters of e^{x_T} − 1, and I(M) is joined to the piece of each other constituent that the link or occurrence contains; a constituent domain is incompatible with an old insertion's domain, touched or not (second rule; the pair is formed between the two constituents' pieces, I(M) for a touched W ∈ 𝔅(M));
  {#MD2.2.6.119-4} a vacuum link at M is incompatible with a marked polymer M′ ≠ M or a vacuum link at M′ ≠ M (vacuum-link rule; the pair is between I(M) and I(M′), fixed data independent of the merge order); a member of an old occurrence hits an insertion, or two members of one occurrence are incompatible (third rule).
  {#MD2.2.6.119-5} The *linked hull* of a class of pieces under the joined pairs is the union of its pieces and, for each joined pair of disjoint pieces, the shorter of the two arcs of C between them (when the two are equal, the one in C's orientation from the piece that comes first in a fixed order of the pieces, e.g. by their first bond along C from the base point), enlarged at each end to the end of any old interval that it cuts, as in (4)(e); it is an arc, or C (a group with arc C is alone in its family and its term is dim(π)^{−1}tr Y_G, #MD2.1.4.20).
  {#MD2.2.6.119-6} The arc I(G) of a group is the union of the linked hulls of its classes.
  {#MD2.2.6.119-7} It is connected: the groups of 𝔊(𝒮) are scalar-link components ((c)), whose marked polymers are joined through their links, and every other membership comes from a joined pair, an arc overlap, the hull rule below or a touched insertion inside I(M).
  {#MD2.2.6.119-8} Merge the groups of 𝔊(𝒮) whose arcs overlap, the merged arc being the union, and repeat until the arcs are pairwise disjoint.
  {#MD2.2.6.119-9} The untouched old insertions whose intervals lie inside an arc join the group of that arc.
  {#MD2.2.6.119-11} The linked hull lies in the union of D2.4(12)(c)'s windows, which is what the tree bound there needs; Y_𝒢, the class form, and Cov(k+1) below use only an arc containing the pieces, with the arcs of distinct groups disjoint.
  - {#MD2.2.6.120} *Second rule.* Also merge into a group every old insertion W, touched or not, whose domain X_W is incompatible with a constituent domain of the group; a touched W ∈ 𝔅(M) of another group carries that group with it.
    {#MD2.2.6.120-1} *Vacuum-link rule.* Merge two groups when a vacuum link of one ((c) *Localisation*, domain supp 𝒞) is incompatible with a marked polymer or a vacuum link of the other: the links are field-dependent factors of Y_𝒢, and the M are compatible with each other ((5)(c)) but not with the clusters of other M (a 𝒞 ≁ M′ with M′ ∈ S_𝔐(𝒞)∖T is allowed).
    {#MD2.2.6.120-2} Old insertions against vacuum links are the second rule's case (a vacuum link is a constituent of its M-vertex), and the members of old occurrences are treated as old insertions of their group for the second rule (third rule).
    {#MD2.2.6.120-3} A marked polymer's support contains Z₀ ⊇ Y₀ and Z ⊇ Z̃₀ ((5)), which are larger than the s-components, and (4)(e) only guarantees that no s-component meets X_W.
    {#MD2.2.6.120-4} Merging is a union of classes: a W already in a group by the arc rule carries its group with it, so the two groups merge.
    {#MD2.2.6.120-5} After each merge, recompute the arc as the union of the linked hulls, with the enlargement, and repeat both rules to a fixed point.
    {#MD2.2.6.120-6} The process is monotone and stops on the finite torus, and its result does not depend on the order of the merges: the pieces, the gap of each joined pair and its enlargement are fixed, and every rule only adds pieces, pairs or members, so the fixed point is the least structure closed under the rules.
    {#MD2.2.6.120-7} The words are unchanged, since it regroups an ordered product along C.
  - {#MD2.2.6.121} Call the results the *step-(k+1) groups* 𝒢.
- {#MD2.2.6.122} *The insertion.* For 𝒢 with arc I(𝒢) = [x, x′], let Y_𝒢 ∈ End(V_π) be the contraction along I(𝒢), in the order of C, of the tensors Ĥ(G), G ⊂ 𝒢, with the untouched old insertions in I(𝒢) and the U_{k+1}-transports between consecutive slots.
  {#MD2.2.6.122-1} By multilinearity, dim(π)^{−1}(contraction of ⊗Ĥ(M) with the A-independent factors of T) = dim(π)^{−1}tr(Y_{𝒢₁}U_{(1)}⋯Y_{𝒢_r}U_{(r)}), with the 𝒢's in cyclic order and U_{(i)} the transports between their arcs.
  {#MD2.2.6.122-2} This is exact.
- {#MD2.2.6.123} *Class form.* The families {𝒢} have disjoint intervals, and their constituent domains are pairwise compatible: the M are compatible by (5)(c), the old insertions by D(k), a new constituent with an old insertion, touched or not, by the second rule, and a vacuum link with a marked polymer or a vacuum link of another group by the vacuum-link rule.
  {#MD2.2.6.123-1} A touched old insertion W ∈ 𝔅(M) is not inside D_J^# (D_J^# is the B-dependence set of the slots, (2.2) above, and Y_G depends on B through B′ and 𝐇 on the components only, so X_W ⊂ D_J^# fails in general); its domain X_W is subject to the second rule like every old insertion's, and it is counted inside M's vertex in D2.4(12)(c).
  {#MD2.2.6.123-2} Inside one 𝒢 the constituents are linked by construction, so the condition of IT-1 note §4 is applied across distinct 𝒢's, with the union of its constituent domains as the domain of 𝒢: its marked polymers' domains, its vacuum links' supports and its old insertions' domains, touched or not, which with the bonds of I(𝒢) (the U_{k+1}-transports) is the set on which Y_𝒢 depends ((c) *Localisation*); the vacuum and old occurrences' factors are numbers given the labels and enter Y_𝒢 as scalars (D2.3(3)'s hard core still counts their members' domains).
  {#MD2.2.6.123-3} So they are compatible families in the sense of IT-1 note §4 (V4 Section joint-extraction: "all their constituent domains … mutually compatible and their intervals are disjoint").
  {#MD2.2.6.123-4} Cov(k+1) holds for Y_𝒢 with the endpoints x, x′, by (b) and the transport law.
  {#MD2.2.6.123-5} Distinct 𝒢's interact only by the hard core of D2.3(3) (third rule below); the parts of Q° and of Q_k(𝔅) inside one 𝒢 are numbers and go into Y_𝒢 (D2.3(3)).
  - {#MD2.2.6.124} *Third rule (from D2.3(3)).* Q° and the old interactions Q_k(𝔅) are expanded in cluster occurrences, the members hit by one occurrence join one group, and the arc hull is taken over the arcs J_Γ of the old occurrences as well.
    {#MD2.2.6.124-1} Then distinct step-(k+1) groups interact only by the hard core of D2.3(3).
- {#MD2.2.6.125} *Cost (D2.4).*
  - {#MD2.2.6.126} Norms.
    {#MD2.2.6.126-1} At real backgrounds, in the projective norm on ⊗End(V_π), contraction with unitary transports does not raise the norm.
    {#MD2.2.6.126-2} In the operator norm on V_π^{⊗m} a contraction can cost up to dim(π)^{m−1}: the swap Σ_{ij}E_{ij}⊗E_{ji} has norm 1 and contracts to dim(π)·1.
    {#MD2.2.6.126-3} So D2.4 uses the projective norm.
    {#MD2.2.6.126-4} At complex backgrounds the transports along I(𝒢) add exp(c_π′‖a′‖_∞·length(I(𝒢))), which D2.4(12)(d) pays from the vertices' shares (see *Arcs*).
  - {#MD2.2.6.127} Arcs.
    {#MD2.2.6.127-1} The merging enlarges arcs: the arc of 𝒢 can exceed the spatial diameter of its supports.
    {#MD2.2.6.127-2} For the squares C_n the shorter arc between two points of C is at most 2 times their distance in the maximum norm, with every period at least twice the side (D2.1(4)).
    {#MD2.2.6.127-3} For the hull of a set the constant is 4: length(I) ≤ 4·(ℓ∞-diameter of the supports), as in D2.1(4)'s proof, and the four midpoints of the sides attain 3.
    {#MD2.2.6.127-4} (A merged arc is not at most the sum of its constituents' arcs, since a second-rule merge also covers the gap between W's interval and I(𝒢).) The smallest-arc bound length ≤ 4·diam_ℓ∞ serves the arcs I(M) and those of (4)(e) (with 20c_π′M‖a′‖_∞ ≤ 1 for the latter, D2.4(11)(c)).
    {#MD2.2.6.127-5} For the linked hull, the shorter arc of a joined pair is at most twice the ℓ∞-distance of the pieces, so I(𝒢) lies in the union of D2.4(12)(c)'s windows and length(I(𝒢)) ≤ Σ_v|win(v)| over its vertices (D2.4(12)(c)'s covering lemma), which D2.4(12)(d) pays with the decay of the activities.
    {#MD2.2.6.127-6} For other contours this chord–arc constant enters.

{#MD2.2.6.129} *(e) D(k+1)(iii): the background domain and the ω-clause.*
- {#MD2.2.6.130} *The background domain must change at k + 1 ≥ 2.*
  - {#MD2.2.6.131} Ĥ(M) contains the covariances and propagators of (5) at the complex background 𝐔.
    {#MD2.2.6.131-1} RG2 p.15 gives their analyticity only "on the space of configurations (𝐔,𝐉) satisfying the conditions I.(i)–(iii) on the domain Z, with constants α₀′, α₁′ much bigger than α₀, α₁".
    {#MD2.2.6.131-2} Those conditions bound gradients as well.
  - {#MD2.2.6.132} D(k)(iii)'s sup-only domain does not control gradients.
    {#MD2.2.6.132-1} On Ω_n∖Ω_{n+1} it allows |A′| < αL^{k−n} in step-k field units, hence |∇^ξA′| ≤ 2ξ^{−1}|A′| < 2αL^{2k−n}, so (L^nξ)²|∇^ξA′| < 2L^nα.
    {#MD2.2.6.132-2} That exceeds CRE's bound α by the factor 2L^n, which is not bounded in n.
  - {#MD2.2.6.133} So D(k+1)(iii), k + 1 ≥ 2, is posed on CRE's domain at 𝐔 = e^{iηa′}U_{k+1}: the full complex part of Ũ^c_{k+1}, i.e. (2.34) for 𝐔 and (2.36) for 𝐉 per plaquette and bond, (2.38) per cube, and (2.39) with both the sup condition and the gradient condition (L^nξ)²|∇^ξ_UA′| < (1 − β(1 − 2^{−(k+1−n)}))α_{1,n}, posed on Ω_n∖Ω_{n+1} for n = 1, …, k and on Ω_{k+1} for n = k+1 (CRE poses none on Ω₀∖Ω₁);
    {#MD2.2.6.133-1} and (2.35), (2.37) for the averaged configurations built on a domain X, posed for each factor that uses them on that factor's own domain: Bałaban's X ∈ 𝐃_k (CRE p.261), and the domain Z of RG2 p.15's covariance operators for Ĥ(M) ((6)(c); #MD2.2.6.131).
    {#MD2.2.6.133-2} RG2 p.15's domain then contains it by definition.
    - {#MD2.2.6.135} The real background.
      {#MD2.2.6.135-1} U_{k+1} on the support lies in the real part of the space: on Ω_{k+1} by CRE p.268 ("The field U_{k+1} satisfies the regularity condition |∂U_{k+1} − 1| < 2B₃ε_{k+1}(L⁻¹η)² on Ω_{k+1}"), and on Ω_{k+1}ᶜ by (6)(e)'s *The base point on Ω₁∖Ω₂*, *For k ≥ 2*, and *Every older layer* (#MD2.2.6.190), which derive the curvature and gradient conditions there through CRE p.277's 𝐇-decay from the top-layer bounds.
      {#MD2.2.6.135-2} CRE p.276 l.10–12 and p.277 l.2–4 state this regularity qualitatively: on a neighbourhood of Ω_n∖Ω_{n+1} the regularity properties of U_{k+1} "are the same as for U_n-configurations", on Ω_{k+1}ᶜ "there is no regularity improvement of the configuration U_{k+1}", and the powers of 1/2 are the room for the shifts (#MOMGD.20).
      - {#MD2.2.6.136} *Membership.* On Ω_{k+1}, (2.34) at j = n = k+1 has the factor 1: |∂U − 1| < α_{0,k+1}ξ²(L^{k+1}ξ)^{−2} (p.261). p.268 gives |∂U_{k+1} − 1| < 2B₃ε_{k+1}(L^{−1}η)².
        {#MD2.2.6.136-1} Both weights are the scale-(k+1) plaquette weight.
        {#MD2.2.6.136-2} *Unit check.* CRE p.276: "In all bounds connected with such a cube we have to replace η=L^{−k} by L^{−n}", so η = L^{−k} and (L^{−1}η)² = L^{−2(k+1)}.
        {#MD2.2.6.136-3} (2.34) for X ∈ 𝐃_{k+1} is in the scale ξ = L^{−(k+1)} (p.256: "the lattice T_ξ, ξ=L^{−j}"), and at n = k+1, ξ²(L^{k+1}ξ)^{−2} = ξ² = L^{−2(k+1)}.
        {#MD2.2.6.136-4} The weights are equal, so membership needs 2B₃ε_{k+1} < α_{0,k+1}, i.e. (with ε_{k+1} = g_{k+1}A₀(log g_{k+1}^{−2})^{p₀}, α_{0,k+1} = g_{k+1}C₀(log g_{k+1}^{−2})^{q₀}) q₀ > p₀ for g_K small, or q₀ = p₀ with C₀/A₀ > 2B₃; this is the same kind of entailment as q₀ ≥ p₀ below, which it bases.
        {#MD2.2.6.136-5} Condition (2.38) for U_{k+1} on Ω_{k+1} (under q₀ > p₀, SW closure §6(6d)): VAR Thm 1 for U_{k+1} with the global ε₁ = O(L²)ε_{k+1} (VAR (7) is a sup over the whole determining set, whose older-layer data are O(L²)ε_j, CRE p.256 l.29–30) gives (2.38) on cubes of size CM, the cubes near ∂Ω_{k+1} through the scale-k class at a factor L, under B₃·O(L³)ε_{k+1} ≤ 2Bα_{0,k+1}, which holds for g_K small when q₀ > p₀ (the equality case q₀ = p₀ is not used),
        {#MD2.2.6.136-6} the membership entailment above in strengthened form (at the root k = 1 the (7)-constant of the U₂ problem is *The base point on Ω₁∖Ω₂*'s ε^V = 2(1+β₀)²ε₁ ≤ 2(1+β₀)⁴ε₂ by (2.8), so there the condition carries the factor 2(1+β₀)⁴); no (LPG′) needed.
        {#MD2.2.6.136-7} On Ω_{k+1}ᶜ the real parts of (2.34) and (2.38) for U_{k+1} are #MD2.2.6.190's: on the layer n = 1 at the root k = 1 from VAR Theorem 1 for U₂ (#MOMGD.11), and for k ≥ 2 and on every older layer from the response chain (#MD2.2.6.190-32, #MD2.2.6.190-50).
  - {#MD2.2.6.137} This is weaker than the sup-only form, which stays at k = 1 (IT-1 note D1(iii)′).
    {#MD2.2.6.137-1} D1(iii)′ implies the new form at k = 1, since its domain contains CRE's.
  - {#MD2.2.6.138} *The consumer still gets what it needs.* (4)(f) at the next step evaluates the old factors at A″ = 𝐇(s,tB″) + a″, with a″ in the new domain.
    {#MD2.2.6.138-1} So (4)(f)'s margin inequality is needed in the gradient norm too.
    - {#MD2.2.6.139} RG2 (1.18) bounds 𝐇_k(s(Y₀),B′) by 4B₀e^{16κ_s}|B′| "and the same bound for all admissible norms".
      {#MD2.2.6.139-1} RG2 p.5 bounds the operator H(s(Y₀)) of the same formula "in all norms of Theorems 3.1.-3.10 [13]" ([13] is PBG: RG2's reference list is RG I's, "and references therein", RG2 p.22 l.9–10, and RG I's entry 13 is PBG).
      {#MD2.2.6.139-2} PBG Theorem 3.1, (3.42), p.397, bounds |G′λ| and |∇_UG′λ| by B₀(L^jη)² and B₀L^jη on Δ(y), y ∈ Λ_j.
      {#MD2.2.6.139-3} That is the weighting of CRE (2.39), (L^nξ)² for the gradient against L^nξ for the field.
    - {#MD2.2.6.140} *RG2 p.5's all-norms bound.* The "admissible norms" of RG2 (1.18) are the norms of PBG Theorems 3.1–3.10: RG2 p.5 bounds H(s(Y₀))X "by B₀e^{16κ₁}|X| in all norms of Theorems 3.1.–3.10 [13]", and PBG (3.42), in Theorem 3.1, bounds |G′λ|, |∇_UG′λ|, |G′∇_U^*λ|, |Δ_UG′λ| by B₀[(L^jη)², L^jη, L^jη, 1]e^{−δ₀d(y,y′)}|λ|, i.e. the gradient with one extra factor (L^jη)^{−1}, the relative weighting of (2.39).
      {#MD2.2.6.140-1} (1.15) holds on the ball max{|𝐀|, |∇𝐀|} < 4C₄(B₀e^{16κ₁})³ε₃², and "holds for all admissible norms" keeps the map in that ball; its ∇ is unweighted (PBG (3.39)).
      {#MOMGD.54} So RG2 (1.18)'s "same bound for all admissible norms" includes the scale-weighted gradient norm of CRE (2.39) (#MD2.2.6.139-2–#MD2.2.6.139-3). Its bounds carry no decay factor; the decay is CRE p.277's 𝐇-decay (#MD2.2.6.164).
      {#MOMGD.57} The admissible norms also include |P₁𝐀| and |Δ_𝐔𝐀|, which give (3.14′) at 𝐀 = 𝐇(s, ·) through RG1 p.272's identity (#MD2.2.4.91-2): PBG (3.42) lists |(Δ_UG′(U)λ)(x)|, RG1 p.272 l.23 promises "bounds for the covariant Laplace operator", RG1 p.273 l.13 takes ε₁ so small that 𝐇_j(B(t)) satisfies (3.14) with α₂/3, and p.273 l.30–31 states that the "new localized functions will satisfy the bounds (3.14), (3.9)"; RG2 p.2 l.11–14 substitutes 𝐇_j(B(t)) + t_□δ𝐇_j for 𝐀 in (I.3.7) and (tζ̃_□ + t_□ζ_□)𝐇_k(B′) in (I.3.34).
    - {#MD2.2.6.141} With RG2 p.5's all-norms bound, the gradient part of A″ obeys the same bound as its sup part, up to the change of the covariant derivative between the centres U_{k+1} and X₁ of (4)(f).
      {#MD2.2.6.141-1} That change is (Ad(e^{iξ𝐇}) − 1)(·)/ξ, of size O(|𝐇||a″|), so (L^nξ)² times it is ≤ (L^nξ|𝐇|)(L^nξ|a″|), and it joins the O(·)² of (4)(f).
      {#MD2.2.6.141-2} So (4)(f)'s condition carries over unchanged to the gradient norm.
    - {#MD2.2.6.142} *The curvature conditions (2.34)–(2.35).* At the evaluation points e^{iηA″}X₁ the change of curvature against e^{iηa″}U_{k+1} is ≤ C(L^nξ)^{−2}ξ²[(L^nξ)²|∇𝐇| + (L^nξ|𝐇|)² + (L^nξ|𝐇|)(L^nξ|a″|)], with 𝐇 = 𝐇(s, tB′).
      {#MD2.2.6.142-1} It must stay below the curvature margin β2^{−(k+1−n)}α_{0,n}ξ²(L^nξ)^{−2}.
      {#MD2.2.6.142-2} At t = 1 this is an inequality of CRE p.277's margin's type with α_{0,n} in place of α_{1,n}: 8B₀e^{16κ_s}C·O(1)ε_k < (β/2)α_{0,k}, i.e. q₀ > p₀, or q₀ = p₀ with C₀/A₀ large.
      {#MD2.2.6.142-3} (2.35) for the averaged configurations is derived below, jointly with (2.37) (RMJ, WILSON_IT1_RMJ_CLOSURE_2026_10_30.md), from 𝐁_p(X)'s definition (CRE p.256 l.57–63), q₀ = q₁ and q₀ > p₀, CRE (2.6)–(2.7) (p.255), RG2 p.5's all-norms bound, and the 𝐇-decay (CRE p.267 l.42–44, p.277 l.6–8).      {#MD2.2.6.142-4} *The change of the averaged configuration.* It depends on 𝐔 only through the block variables, its change is exp(iηℋ(B)) with B the change of the block variables (VAR Proposition 9, p.309), and VAR (190) (p.308) bounds δℋ/δB and ∇δℋ/δB by O(1)(L^jη)^{−1}, O(1)(L^jη)^{−2} times (L^{j′}η)^{−d}e^{−δ₀d(y,y′)/8};
      {#MD2.2.6.142-5} against VAR's block weight (L^{j′}η)^d (VAR p.291) and with PRT2 (2.58)–(2.59) (Σ_{y′∈Λ_{j′}}e^{−αδ₀d(y,y′)} ≤ 6c₀^d(α/2)e^{−(αδ₀RM/4)max(|j−j′|−1,0)}, d of PRT2 (2.46)), this gives a curvature change ≤ C·η²(L^jη)^{−2}Σ_{j′}e^{−(δ₀RM/32)max(|j−j′|−1,0)}sup_{Λ_{j′}}|B| at a point of VAR layer j.
      {#MD2.2.6.142-7} *The averaged configurations U_{p,X}.* CRE (2.2), (2.11)–(2.14) (pp.255–257) define the determining set 𝐁 = ∪Γ_j, the averaging M_𝐁 = M^j on Γ_j, the minimal configuration U_𝐁(V) of A^η under M_𝐁(U) = V (from VAR), and 𝐁_j(Ω), the minimal determining set of Ω (Ω_n unions of L^nξM₁-cubes, ξ = L^{−j}); so U_{p,X} is the VAR minimiser for 𝐁_p(X) ∪ {Γ_i}_{i<p}, and (2.35)'s right side α_{0,n}L^{−2p}(L^nL^{−p})^{−2} is VAR's ε·η²(L^nη)^{−2} at η = L^{−p} for n ≤ p;
      {#MD2.2.6.142-8} which lattice and block scale U_{p,X} carries on the layers n > p is fixed by CRE's definition of 𝐁_j(Ω) at j = p (p.256 l.57–63): the minimal determining set with support in X, on X's maximal sequence X = Ω_0 ⊃ Ω_1 ⊃ … ⊃ Ω_p, Ω_n a union of L^nL^{−p}M₁-cubes at the distance ≥ L^nL^{−p}M₁ from Ω_{n−1}^c. CRE names RG1 (1.11)–(1.16) as the model of its spaces (p.261 l.1–2), and RG1 (iv) builds the U_n on the same sequence (p.262 l.41–43).
      {#MD2.2.6.142-9} CRE does not define p: in pp.250–270 the letter appears as an index only in (2.7) ("p is a positive integer") and in (2.35), (2.37).
      {#MD2.2.6.142-10} The condition's source is RG1's condition (iv) (p.262): X is taken as Ω_0, its maximal domains Ω_1, …, Ω_j satisfy REG (1.3)–(1.6) with j, ξ, and U_n is built on the subsequence {Ω_0, …, Ω_n}, n = 1, …, j, with the single bound (1.16) |∂U_n(M^·(𝐔)) − 1| < α₀ξ² on X̃^{−2}.
      {#MD2.2.6.142-11} So p ranges over 1, …, j, as RG1 (iv)'s n does, and U_{p,X} carries X's own layers up to p (CRE p.256 l.57–63); on X's layers n > p its finest data is the p-block average.
      {#MD2.2.6.142-12} CRE (2.37) carries for n > p the explicit relaxation L^{n−min{p,n}}, while (2.35) carries none.
      {#MD2.2.6.142-15} *The bound through curvature ((c0)–(c3) and *Assembly* below).* Curvature is gauge invariant, so the change is bounded through the deformation's own curvature.
      {#MD2.2.6.142-16} (c0) *Exact integration.* The path scales the field argument: 𝐔_t := e^{iη𝐇(s, (t·t_Y)B′)}e^{iηa′}U_{k+1}, t ∈ [0,1] (the path parameter t, distinct from the deformation parameters s, t_Y of (4)(f), which are held fixed), from the base point 𝐔_0 = e^{iηa′}U_{k+1} (𝐇(s, 0) = 0 by RG2 (1.18), |𝐇_k(s(Y_0), B′)| ≤ 4B₀e^{16κ₁}|B′|) to the evaluation point 𝐔_1 = e^{iηA″}X₁.
      {#MD2.2.6.142-17} Since |t·t_Y| ≤ T_Y, every 𝐔_t is itself an evaluation point of (4)(f). ∂_t𝐔_t = iηH_t𝐔_t, where H_t is the derivative of 𝐇(s, (t·t_Y)B′) in t through the differential of the exponential (H_t = ∂_t𝐇 + O(η|𝐇||∂_t𝐇|));
      {#MD2.2.6.142-18} 𝐇 is analytic in B′ for |B′| < ε₃ (RG2 p.6, with (1.18) "and the same bound for all admissible norms"), and the field (t·t_Y)B′ is ≤ 2(T_Y|B′|_Y + sup|B′|) for |t| ≤ 2, which the T_Y condition below (for T_Y|B′|_Y) and sup|B′| = O(1)ε_k with q₀ > p₀ (for sup|B′|) keep ≤ 2(1 + o(1))min(β,1)α_{0,k}/(C′B₀e^{16κ_s}) ≪ ε₃ for g_K small, so Cauchy's estimate on |t| ≤ 2 bounds ∂_t𝐇, in each admissible norm, by twice the bound (1.18) at the field t_YB′; so H_t obeys the deformation's bounds of the opening plaquette bound up to the factor 2;
      {#MD2.2.6.142-19} ȟ_n is defined by them: L^nη|H_t|, (L^nη)²|∇H_t| ≤ O(1)ȟ_n on layer n (η = L^{−p}, the units of U_t and 𝐔_t, as in the RMJ note §2), with ȟ_k := B₀e^{16κ_s}(T_Y|B′|_Y + sup|B′|) on Ω_k and ȟ_n := O(1)(2θ)^{k−n}h_k^{(0)} on an older layer n < k, the CRE p.277's 𝐇-decay majorant with #MD2.2.6.143's normalisation h_k^{(0)}.
      {#MD2.2.6.142-19-1} On Ω_k, ȟ_k ≤ (1 + o(1))min(β,1)α_{0,k}/C′ for g_K small by the T_Y condition below and sup|B′| = O(1)ε_k (q₀ > p₀), and on the older layers CRE p.277's 𝐇-decay gives the bounds with ȟ_n.
      {#MD2.2.6.142-20} U_t := U_{p,X}(M^·(𝐔_t)).
      {#MD2.2.6.142-21} Each 𝐔_t satisfies (2.34) by the opening bound, so its averaged data lie in the domain of VAR Theorem 1 and Proposition 9 (p.278 (7), p.309, ε₂ = B₅ε₁; the complex part |V′ − 1| < C₁^{VAR}ε₁ of VAR (172), p.305, C₁^{VAR} VAR's absolute constant, uses α_{1,n}/α_{0,n} = C₁/C₀ bounded, with CRE (2.28)'s C₁ and q₀ = q₁, #MD2.4.13.19): U_t exists (unique up to gauge at real data, the analytic extension at complex data), depends analytically on t, and is regular in PBG's sense ((3.35) with Mα₀ ≤ a₀; (3.37) with α₁ = B₅ε₁ for complex data).
      {#MD2.2.6.142-22} (c0′)'s Lagrange-multiplier term needs a per-layer bound on U_t's current 𝐉_{p,X}(M^·(𝐔_t)) (RG1 (1.15), p.262: J_n(M^·(𝐔)) "is defined by the formula (1.8) with U_n(M^·(𝐔)) instead of U_j, L^{−n} instead of ξ"), with any O(1) constant.
      {#MOMGD.50} *RMJ, the (2.37) part of CRE p.277's margin (WILSON_IT1_RMJ_CLOSURE_2026_10_30.md).* At every evaluation point of (4)(f), for every factor domain X (the non-𝐃_k domains Z included) and every p, 𝐉_{p,X}(M^·(𝐔)) satisfies CRE (2.37) with the step-k constant (1 − β(1 − 2^{−(k−n)})) on each layer n of X; in particular |J_t| ≤ α_{0,n}L^{n−min{p,n}}(L^nη)^{−3} at every path point (written in η-units; CRE (2.37) prints the scale as (L^nL^{−p})^{−3});
      {#MD2.2.6.142-24} (c0′) uses the path form supplied by the note's continuity set T (its doubled bounds, with ≤), constant 2.
      {#MD2.2.6.142-25} Every 𝐔_t is an evaluation point, and p.277's printed range "(2.36)–(2.39)" includes (2.37).
      {#MD2.2.6.142-26} But p.277 argues only that the shrinking of the domains "is still much greater than bounds on" 𝐇_k.
      {#MD2.2.6.142-27} At the T_Y-polydisc points the deformation is of size min(β,1)α_{0,k}/C′, not O(B₀ε_k), and on the non-𝐃_k domains Z of the map's own factors (#MD2.2.6.133) the statement is not printed.
      {#MD2.2.6.142-29} The RMJ note's exact identity: the linearised minimiser is H₁ = G₁Q*(QG₁Q*)^{−1} with G₁ = (Δ_a − Δ^{(2)})^{−1}, VAR p.294's operator with Δ in place of Δ_π (VAR p.297), and RD*G₁Q* = 0 follows from VAR's Landau-gauge variational problem (VAR (76), (127)–(128), (172)–(177); note §4(c)), so D*D𝒜_t = Q*(λ₁ − b_t) + Δ^{(2)}𝒜_t − Δ′𝒜_t with λ₁ = (QG₁Q*)^{−1}b_t, and λ₁ − b_t contains the deformation only through DH_t, H_t and (c3)'s δ_t;
      {#MD2.2.6.142-30} with (3.132) for G₁ the main term is O(1)B₀ȟ_n(L^pη)^{−1}(L^nη)^{−2}, (2.37)'s scale times O(1)B₀ȟ_n/α_{0,n}, with no loss, and the T_Y condition with C′ enlarged makes the change at most half the margin on every layer.
      {#MD2.2.6.142-31} On each p-block U_t is taken in the axial gauge Ax_k (REG p.79; u = 1 at the block points leaves M^· invariant).
      {#MD2.2.6.142-32} Then the curvature change is ∫_0^1 ∂_t(∂U_t) dt exactly, with no remainder in H, and ∂_tU_t = iη(𝒜_t + D_{U_t}ω_t)U_t, where 𝒜_t is the linearised minimiser ℋ_t at U_t (in Landau gauge relative to U_t, VAR Proposition 9) applied to the data derivative ∂_tM^·(𝐔_t) = Q_{𝐔_t}H_t (Q_Y the linearised averaging at Y), and ω_t, with |ω_t| ≤ O(1)L^pη|𝒜_t| ≤ O(1)ȟ_n, is the infinitesimal gauge keeping U_t in Ax_k; the plaquette rate is η²|D𝒜_t| plus the commutator terms O(|ω_t| + η|𝒜_t|)|∂U_t − 1| ≤ O(1)ȟ_n·α_{0,n}L^{−2n}, (2.35)'s scale times O(1)ȟ_n, absorbed in *Assembly*.
      {#MD2.2.6.142-33} Since M^·(U_t) = M^·(𝐔_t), Q_{𝐔_t}H_t = Q_{U_t}H_t + δ_t with δ_t := (Q_{𝐔_t} − Q_{U_t})H_t, (c3)'s mismatch.
      {#MD2.2.6.142-34} A continuity argument in t (the set T of t up to which U_s satisfies (2.35) and (2.37) with the margins doubled, i.e. with the step-(k+1) bounds plus 2β2^{−(k+1−n)}α_{0,n}L^{−2n} and 2β2^{−(k+1−n)}α_{0,n}L^{n−min{p,n}}(L^nη)^{−3} as right sides, contains 0, since a′ ranges over D(k+1)(iii)'s domain, which poses (2.35) and (2.37) for the averaged configurations, #MD2.2.6.133, is closed by continuity in t, and is open because the bounds below and the RMJ note's §4–§6 give (2.35) and (2.37) with the original margins on T, strictly inside the doubled ones,
      {#MD2.2.6.142-35} so T = [0,1]) supplies (2.35) and (2.37) for U_t along the path, which (c3) and (c0′) use; the current bound used along the path is T's, so nothing is assumed about the current at the evaluation points.
      {#MD2.2.6.142-36} (c0′) *The linearised minimiser.* VAR (182) and (188), pp.307–308, give δℋ/δB = H_0 + (I + G̃V″)^{−1}G̃(Δ^{(2)} − V″)H_0 − H⟨𝔇(𝒜_0 + H_0B), ·⟩, written with G := (Δ_a − Δ^{(2)})^{−1} (VAR p.306 l.37–38); at the minimiser U_t (expansion point A′ = 0) V″(0) = 0, V being of third and higher order (VAR p.282, (80) p.290), and 𝔇(0) = 0, D(A′) beginning at second order (VAR pp.289–290).
      {#MD2.2.6.142-37} With (c1)'s G = Δ_a^{−1} (VAR p.297) the same linearisation is ℋ_t = (I − G̃Δ^{(2)})^{−1}H_0 (VAR p.306 l.35), with H_0B = GQ*(QGQ*)^{−1}(L^{j(·)}η)^{−1}B.
      {#MD2.2.6.142-38} Δ^{(2)} is not a curvature term: PBG (3.134) (p.422) defines ⟨A, Δ^{(2)}A⟩ = 2⟨HC^{(2)}(A), J⟩, and (3.136) writes Δ^{(2)}A = Σ_jΣ_{b∈Λ_j}(L^jη)^{d+1}tr(δ/δA)C_j^{(2)}(A,b)(H*J)(b), linear in H*J_t, J_t U_t's current (the Lagrange multiplier, VAR p.305; P_0*J = 0 at the minimiser, VAR (178)); PBG's bound |(Δ^{(2)}A)(b)| ≤ O(1)Mα_0(L^jη)^{−2}|A| ((3.137), p.423) comes from |(H*J)(b)| ≤ O(1)Mα_0(L^jη)^{−3} through "the inequality (149) in [5]" (PBG p.422;
      {#MD2.2.6.142-39} PBG's [5] is CMP 98 "Averaging operations", whose (149), p.40, is |⟨(δ/δA)C_j(U_0,A), δA⟩| ≤ C_3|A|Q_j″|δA|, a local bound), i.e. |(Δ^{(2)}A)(b)| ≤ O(1)C_3L^jη·sup_{near b}|H*J|·|A|, the sup over several j-blocks surrounding b, with j = p, U_t's localisation index on X's layers n ≥ p. For data L^{j(·)}ηQH (VAR (126)) the identity H_0(L^{j(·)}ηQH) = H − G̃Δ_aH is exact (below H_0(QH) denotes this) (G̃Δ_a = I − GQ*(QGQ*)^{−1}Q by VAR (131), p.298, and G̃Q* = 0), with Δ_a = Δ + DRD* + Q*Q and Δ = D*D + Δ′, Δ′ linear in F_t.
      {#MD2.2.6.142-40} So DH_0(QH) = DH − DG̃D*(DH) − DG̃D(RD*H) − DG̃Δ′H, and the plaquette change rate is η²|D𝒜_t| (spacing squared times the curvature of 𝒜_t).
      {#MD2.2.6.142-41} The four terms: (1) η²|DH|, the deformation's own curvature; (2) DG̃D*(DH) by (3.44), below; (3) DG̃D(RD*H) by (3.44) with λ = RD*H, R = Δ𝒢Δ PBG's projection (p.426, 𝒢 = G′² − G′²Q′*(Q′G′²Q′*)^{−1}Q′G′²), bounded with its Hölder norms scale-free by (3.42), (3.46) and Theorem 3.2 (weights (L^jη)^{−2}·(L^jη)^4·(L^jη)^{−2}), so |RD*H| ≤ O(1)sup|∇H| on the localisation cube; (4) η²|DG̃Δ′H| ≤ B₀L^pη·O(1)η²|F_t||H| ≤ O(1)B₀·α_{0,n}L^{−2n}·L^pη|H| ≤ O(1)B₀·α_{0,n}L^{−2n}·L^{p−n}ȟ_n by (3.42) (|∇GJ| ≤ B₀L^jη), (2.35)'s scale times O(1)B₀ȟ_n.
      {#MD2.2.6.142-42} The correction ℋ_t − H_0 = Σ_{m≥1}(G̃Δ^{(2)})^mH_0(QH) is bounded through the current, not the curvature: |H_0(QH)| ≤ |H| + |G̃Δ_aH| ≤ O(1)(|H| + L^pη|∇H|) + O(1)α|H| ≤ O(1)ȟ_n(L^nη)^{−1} on layer n by (3.42), and, with T's current bound in η-units (the continuity argument above), |J_t| ≤ O(1)α_{0,n}L^{n−p}(L^nη)^{−3} on X's layer n ≥ p (CRE (2.37), α_{0,n}L^{n−min{p,n}}(L^nL^{−p})^{−3}, with the units of *(c2) units*;
      {#MD2.2.6.142-43} |H*J_t| ≤ O(1)sup|J_t| over the decay of PBG (3.133)'s kernel, the finer layers n′ entering with L^{3(n−n′)} against e^{−δ₂·(width)}, summed as below), |Δ^{(2)}A| ≤ O(1)C_3L^pη·α_{0,n}L^{n−p}(L^nη)^{−3}|A|.
      {#MD2.2.6.142-44} So η²|DG̃Δ^{(2)}H_0(QH)| ≤ η²·B₀L^pη·O(1)C_3L^pη·α_{0,n}L^{n−p}(L^nη)^{−3}·O(1)ȟ_n(L^nη)^{−1} = O(1)B₀C_3·α_{0,n}L^{−2n}·ȟ_nL^{p−n} by (3.42) (|∇GJ| ≤ B₀L^jη), (2.35)'s scale times O(1)B₀C_3ȟ_n with no loss; and |G̃Δ^{(2)}| ≤ O(1)B₀(L^pη)²·C_3L^pη·α_{0,n}L^{n−p}(L^nη)^{−3} ≤ O(1)B₀C_3α_{0,n}L^{2(p−n)} ≤ 1/2 for g_K small, so the terms m ≥ 2 add a geometric factor ≤ 2.
      {#MD2.2.6.142-46} PBG (3.44) (p.398), |∇_UG′∇_U^*λ(x)| ≤ B₀′(ε)e^{−δ₀d(y,y′)}(‖λ‖_ε^{ξ′} + |λ|), carries no factor L^jη, and DGD* is a finite combination of its ∇_UG∇_U^* components; PBG Theorem 3.3 (p.399) gives it for G, Theorem 3.4 extends it to complex U′U under (3.37), and the truncated sequence {Ω_0, …, Ω_p} on which U_{p,X} is built is covered by Theorems 3.1–3.4 themselves ("the constants … do not depend on the sequence {Ω_j} … if the conditions (2.1), (2.2) are satisfied", p.399), RG1 (iv) building it from REG (1.3)–(1.6);
      {#MD2.2.6.142-47} PBG's (2.1)–(2.2) are the conditions of PBG's [4] (p.393), and that REG (1.3)–(1.6) supply them is Bałaban's (REG p.77 l.2 places its sequences in the same setting, "see also [2.II, 4]").
      {#MD2.2.6.142-48} (3.44) is applied to μ = DH through a partition of unity subordinate to the cubes Δ̃(y′), with the product rule for ‖ζμ‖^{ξ′}.
      {#MD2.2.6.142-49} So at a point of X's layer n the change rate is ≤ η²[|DH| + B₀′(β_H)Σ_{y′}e^{−δ₀d(y,y′)}(‖DH‖_{β_H}^{ξ′} + |DH| + |∇H|)] + (2.35)'s scale × O(1)B₀ȟ_n, with no factor L^{n−p}.
      {#MD2.2.6.142-50} The finer layers n′ < n enter with L^{2(n−n′)}; for X's layers n, n′ ≥ p, U_t's localisation index is p for both, so the decay is spatial: REG (1.4) (p.77) gives (L^jη)^{−1}dist(Ω_j^c, Ω_{j+1}) > RM₁ with R = R₁ (RG1 (iv)), so a layer n″ > p of X is ≥ R₁M₁L^{n″−p} ≥ R₁M₁ wide in p-block units, giving e^{−δ₂R₁M₁(|n−n′|−1)}, summable against L^{3(n−n′)} (the current's (2.37) weight, a majorant of the true ratio L^{2(n−n′)}α_{0,n′}/α_{0,n} for n′ ≥ p, with α_{0,n′}/α_{0,n} ≤ (1+β₀)²(n−n′)^{β₀} ≤ (1+β₀)²√(n−n′) by the second lines of CRE (2.6)–(2.7) (n > m;
      {#MD2.2.6.142-51} β₀ ≤ 1/2, #MD2.4.13.19), CRE (2.6)–(2.7), absorbed by the "+1"; the curvature terms need only L^{2(n−n′)}; the sum is O(L³), so C_{(2.35)} depends on L) once δ₂R₁M₁ > 3log L + 1, which holds for g₀ small since R₁ ≥ (log g₁^{−2})^r → ∞ (CRE (2.5)); across localisation indices (n′ < p) PRT2 (2.58)–(2.59) gives the same.
      {#MD2.2.6.142-52} (c1) VAR p.297: Δ_a = Δ + DRD* + Q*aQ (a = 1), "For the operator Δ_a^{−1} = G we have proved Theorem 3.3 in [5]", i.e. VAR's G is PBG's G (PBG (p.395) G = (Δ_a↾Ω_0)^{−1}, same Δ_a); VAR p.300 (with the transcriber's note on the missing QG): G̃ = GP_0^* = G − GQ*(QGQ*)^{−1}QG, in Landau gauge.
      {#MD2.2.6.142-53} PBG p.422 states Theorem 3.3 for G "in all norms appearing on the left-hand sides of the inequalities (3.42)–(3.47), except the inequality involving the Laplace operator in (3.42)", so (3.44) holds for G. The second part of DG̃D* is (DH^{PBG})(QGD*) with H^{PBG} = GQ*(QGQ*)^{−1} of PBG (3.126): PBG (3.133) gives |∇H^{PBG}(x,y′)| ≤ O(1)(L^jη)^{−1}(L^{j′}η)^{−d}e^{−δ₁d(y,y′)/2}, and PBG (3.42) for G gives |QGD*μ(y′)| ≤ B₀L^{j′}ηΣ_{y″}e^{−δ₀d(y′,y″)}|μ|;
      {#MD2.2.6.142-54} against the block weight (L^{j′}η)^d the product is O(1)B₀L^{j′−j}e^{−(δ₁/2)d(y,y′)}Σ_{y″}e^{−δ₀d(y′,y″)}|μ|, scale-free on a layer and summable across layers by PRT2 (2.59) as above (j′ > j costs L^{j′−j}, absorbed by e^{−(δ₁RM/8)(|j−j′|−1)} for M large after L).
      {#MD2.2.6.142-55} So |DG̃D*μ(x)| ≤ O(1)B₀′(ε)Σ_{y′}e^{−δ₂d(y,y′)}(‖μ‖_ε^{ξ′} + |μ|), δ₂ := min(δ₀, δ₁)/4, with j the localisation index in U_{p,X}'s own determining set (j = p on X's layers n ≥ p): since min(δ₁/2, δ₀) ≥ 2δ₂, the triangle inequality for d gives (δ₁/2)d(y,y′) + δ₀d(y′,y″) ≥ δ₂d(y,y″) + δ₂d(y,y′), and the sum over the intermediate y′ of e^{−δ₂d(y,y′)} is bounded by PRT2 (2.58)–(2.59).
      {#MD2.2.6.142-56} (c2) the Hölder seminorm ‖DH_t‖_{β_H}^{ξ′} at the layer's scale, with the Hölder exponent β_H := 1/2 fixed (PBG's admissible range 0 ≤ β ≤ β₀^{PBG} < 1 with β₀^{PBG} ≥ 1/2).
      {#MD2.2.6.142-57} The input is printed: RG2 (1.18) (p.6) bounds 𝐇_k(s(Y₀), B′) "and the same bound for all admissible norms", with RG2 p.5's all-norms bound (#MD2.2.6.140: the admissible norms are those of PBG Theorems 3.1–3.10, RG2 p.5), and the direct Hölder input for an H-type operator is PBG (3.133)'s third entry, ‖ζ∇H(·,y′)‖_β ≤ O(1)(‖ζ‖_β^ξ + |ζ|)(L^jη)^{−1−β}(L^{j′}η)^{−d}e^{−(1/2)δ₁d(y,y′)}, the sup weight (L^jη)^{−1} times (L^jη)^{−β} (as in (3.43) for G′);
      {#MD2.2.6.142-58} so the Hölder seminorm of DH_t measured at the localisation scale is bounded by the same weight as |DH_t| itself, and ‖DH_t‖_{β_H}^{ξ′} + |DH_t| ≤ O(1)B₀^{PBG}(β_H)B₀e^{16κ_s}·(the sup bound of DH_t).
      {#MD2.2.6.142-59} The units of ‖·‖^{ξ′} are pinned under *(c2) units* below; (c3) the data mismatch.
      {#MD2.2.6.142-60} Since M^·(𝐔_t) = M^·(U_t), the data derivative differs from Q_{U_t}H_t by δ_t = (Q_{𝐔_t} − Q_{U_t})H_t.
      {#MD2.2.6.142-61} On a p-block b in X's layer n ≥ p, the linearised averaging is the average over the block's paths of Σ_l Ad(Y_{<l})H_t(l) (with the commutator terms of the ordered product) for Y = 𝐔_t, U_t, each taken in the block's axial gauge Ax_k (REG (1.19)–(1.22), p.79): 𝐔_t is axialised by a gauge transformation u with u = 1 at the block points, which leaves M^·(𝐔_t), hence U_t's orbit, unchanged, and carries H_t by Ad(u); U_t is its own axial representative in that orbit; the two frames agree at the block points.
      {#MD2.2.6.142-62} In the axial gauge the transport Y_{<l} along a path from the block root equals the holonomy of the loop formed by the path and the tree path back, a loop of area ≤ O(1)(L^pη/η)² plaquettes, so |Y_{<l} − 1| ≤ O(1)(L^pη/η)²·α_{0,n}η²(L^nη)^{−2} = O(1)α_{0,n}L^{2(p−n)} for both, by (2.34) for 𝐔_t and (2.35) for U_t (the continuity argument of (c0)).
      {#MD2.2.6.142-63} So |Ad(𝐔_{t,<l}) − Ad(U_{t,<l})| ≤ O(1)α_{0,n}L^{2(p−n)}, the commutator terms carry the same factor, and, ∂_tM^· being linear in H_t, |δ_t| ≤ O(1)α_{0,n}L^{2(p−n)}·L^pη|H_t| ≤ O(1)α_{0,n}L^{3(p−n)}ȟ_n with L^nη|H_t| ≤ O(1)ȟ_n (for complex 𝐔_t the non-abelian Stokes conjugation factors are 1 + O(L^{p−n}α_{1,n})).
      {#MD2.2.6.142-64} The (190) bound above at VAR layer p (η = L^{−p}) gives a curvature change ≤ C L^{−2p}·O(1)α_{0,n}L^{3(p−n)}ȟ_n = α_{0,n}L^{−2n}·O(1)C L^{−(n−p)}ȟ_n: (2.35)'s scale times O(1)Cȟ_n, with no loss.
      {#MD2.2.6.142-65} For n < p the same argument at the point's own layer gives the factor α_{0,n} without powers of L. *(c2) units (the distance part from print, the amplitude part by homogeneity).* PBG p.397: "‖·‖_α^ξ means that functions and distances are on the ξ-lattice"; PRT2 p.248: "the symbol ‖·‖_α^ξ indicates the scale ξ for which the Hölder norm is taken"; PRT2 p.223: the distance on ηZ^d "depends of course on the scale of the lattice";
      {#MD2.2.6.142-66} with η = L^{−k}, ξ = L^{−j}, the scaling by L^{k−j} takes T_η to T_ξ and the j-blocks (side L^jη) to unit side, so ‖f‖^ξ_β = (L^jη)^β·(the η-scale Hölder quotient over |x − x′| ≤ L^jη), the distances rescaled as printed; that the amplitude of f is not rescaled is not printed but is forced by the homogeneity of (3.44), whose left side and |λ| carry the same units.
      {#MD2.2.6.142-67} With (3.133)'s Hölder entry (η-scale Hölder weight (L^{j′}η)^{−β} times the sup weight), ‖DH_t‖^{ξ′}_{β_H} ≤ O(1)·(the sup bound of DH_t on Δ̃(y′)), since U_t's localisation index j′ = min(n, p) ≤ n.
      {#MD2.2.6.142-68} *Assembly.* At a point of X's layer n the rate of the curvature change of U_t is ≤ η²|DH_t| + O(1)B₀′(β_H)B₀^{PBG}(β_H)Σ_{y′}e^{−δ₂d(y,y′)}η²(|DH_t| + |∇H_t|)_{Δ̃(y′)} + α_{0,n}L^{−2n}·O(1)(B₀ + C)ȟ_n, and η²(|DH_t| + |∇H_t|) on layer n′ is ≤ C(L^{n′}ξ)^{−2}ξ²(L^{n′}ξ)²|∇H_t|, the gradient term already bounded for (2.34) above; the layer sum is controlled as in (c0′) under δ₂R₁M₁ > 3log L + 1; the Lagrange-multiplier term adds α_{0,n}L^{−2n}·O(1)B₀C_3ȟ_n.
      {#MD2.2.6.142-69} Integrated over t ∈ [0,1], (2.35) holds at the evaluation points with C replaced by C_{(2.35)} := C(1 + O(1)B₀′(β_H)B₀^{PBG}(β_H)c₀^d) + O(1)(B₀(1 + C_3) + C + 1), i.e. under the same T_Y condition with C′ enlarged by the factor C_{(2.35)}/C, which depends on d, L and the fixed β_H only; L is fixed before κ_s and M (#MD2.4.13.19), and the T_Y factor per component of D2.4's count (#MD2.2.4.80) stays ≤ 1 with this C′, its added part C′B₀e^{16κ_s}|B′|_Y/(min(β,1)α_{0,k}) being O((log g_k^{−2})^{p₀−q₀}) → 0 for q₀ > p₀.
      {#MD2.2.6.142-70} The uses of PBG (3.42)–(3.46) need U_t regular, which VAR Theorem 1 and Proposition 9 give (c0).
      {#MD2.2.6.142-72} CRE p.277's margin is printed for "(2.36)–(2.39)" only, so it is not used for (2.35).
      {#MD2.2.6.142-73} CRE's powers of 1/2 appear in (2.34)–(2.37) as in (2.39).
      {#MD2.2.6.142-74} On the polydisc T_Y is taken so small that the deformation respects the margins of the pointwise conditions (2.34) and (2.36): 1/T_Y ≥ C′B₀e^{16κ_s}|B′|_Y/(min(β,1)α_{0,k}) is added to the maximum of (4)(f).
      {#MD2.2.6.142-75} (2.37), a function of 𝐔 through the averaged minimiser, does not follow from this size condition alone; at the step-k margin at every evaluation point it is RMJ, derived in WILSON_IT1_RMJ_CLOSURE_2026_10_30.md under C′ ≥ C_{(2.37)} (#RMJ.6.5), a constant of d, L, β₀ ≤ 1/2 and the Ad-norm constants of G.
      - {#MD2.2.6.143} *Older layers.* The check above is at n = k.
        {#MD2.2.6.143-1} On Ω_n∖Ω_{n+1}, n < k, m := k−n ≥ 1, the bound on the deformation in the units of |A″| is O(1)L^mθ^m times its Ω_k-size, by CRE p.277's 𝐇-decay in the sup and the scale-weighted gradient norm.
        {#MD2.2.6.143-2} With h_k^{(0)} := 4min(β,1)α_{0,k}/C′ + 8C₁^{RG2}B₀e^{16κ_s}O(1)ε_k, the bound on the polydisc under the T_Y condition above, the curvature part needs O(1)(2θ)^m h_k^{(0)} < (β/2)α_{0,n}.
        {#MD2.2.6.143-3} CRE (2.6)–(2.7), first lines (for every p; CRE (2.6)–(2.7)), give α_{0,n} ≥ α_{0,k}/((1+β₀)²√m).
        {#MD2.2.6.143-4} The n = k inequality in its complex-data form gives h_k^{(0)} ≤ min(β,1)α_{0,k}/2 for C′ ≥ 16.
        {#MD2.2.6.143-5} With √m x^m ≤ x for x ≤ 1/2, the condition holds for all m ≥ 1 once 2θ ≤ 1/2 and 2θ·O(1)(1+β₀)² < 1, as for the sup part in (4)(f).
        {#MD2.2.6.143-6} The 𝐉-bound (2.36) is treated the same way at the 𝐉-margin of (4)(f), *Carrying 𝐉*, with CRE p.277's 𝐇-decay covering its Laplacian and P₁ parts (the extension of RG2 p.5's all-norms bound there is part of CRE p.277's 𝐇-decay); (2.37), for 𝐉_{p,X}(M^·(𝐔)), a function of 𝐔 not treated in *Carrying 𝐉*, is RMJ in its margin form (#MOMGD.50).
        {#MD2.2.6.143-7} The basis on the older layers is CRE p.277 (CRE p.277's margin) with CRE p.277's 𝐇-decay.
- {#MD2.2.6.144} *Analyticity of the new insertions, from (4)(f) and RG2 p.15.* For real U_{k+1} on the support and a′ in the new domain at step k+1:
  - {#MD2.2.6.145} the old factors are analytic at e^{iη(𝐇(s,tB′) + a′)}U_{k+1} by (4)(f), in the sup and the gradient norm;
  - {#MD2.2.6.146} the transports and the leading word are entire in the background;
  - {#MD2.2.6.147} the Gaussian parts and the 𝐕_k(Y) are analytic on Bałaban's domain by RG2 p.15, which contains the new one by the definition above;
  - {#MD2.2.6.148} the characteristic functions do not depend on a′.
    {#MD2.2.6.148-1} They depend on the fluctuation field (CRE p.268: "We want to have characteristic functions depending on the fluctuation field only", (3.16)) or on the real step-(k+1) configuration (the (3.3) factors that remain), and the latter are among the term's indicators, kept as factors.
  - {#MD2.2.6.149} Ĥ(M), and with it Y_𝒢 of (d), is then analytic in a′ by Morera's theorem in each variable under the integrals, and jointly by Hartogs' theorem.
    {#MD2.2.6.149-1} This needs: an integrable majorant for the parameter integrals, locally uniform in a′ (RG2 p.15's second measure is complex, and the large-field B is unbounded, so a uniform bound in B is not available); locally uniform convergence of the cluster series inside Ĥ(M), Ψ(M) and the vacuum sums, with Weierstrass' theorem.
    {#MD2.2.6.149-2} Both are part of D2.4's sizes at complex data (D(k+1)(ii) with δ*^{(k+1),c} + a*^{(k+1)}). Ĥ(M) is G-covariant by (b).
- {#MD2.2.6.150} *The ω-clause: where ω lives.* At step k the components of ω are ω₀, V4's exterior fields on the bonds I∖D(Λ) and J (IT-1 note §3d(2)(d) *The values*) of Ω₁∩Λᶜ, and the slot variables ω_j := σ_j, the old A_j on Ω_{j+1}∩Λ_{j+1}ᶜ ((b)), for 1 ≤ j ≤ k−1.
  {#MD2.2.6.150-1} Since Ω_{j+2} ⊆ Λ_{j+1} (CRE pp.264–265), ω_j lies in the layer Ω_{j+1}∖Ω_{j+2}.
  {#MD2.2.6.150-2} That layer is a union of scale-(j+1) blocks: VAR p.277, "B^j(Λ_j)=Ω_j∖Ω_{j+1}", with VAR's Λ_j := Ω_j^{(j)}∖Ω_{j+1}^{(j)}, not CRE's.
  {#MD2.2.6.150-3} The new component ω_k := A_k on Ω_{k+1}∩Λ_{k+1}ᶜ lies in the layer Ω_{k+1}∖Ω_{k+2}.
- {#MD2.2.6.151} *|ω| on the support.*
  - {#MD2.2.6.152} At step j+1, CRE (3.14), p.267, gives |A_j′| < O(1)ε_j on Ω_{j+1} on the support of the step-(j+1) characteristic functions of (3.3) ("|V_k′−1|<O(1)ε_k on Ω_{k+1}… |A_k′|<O(1)ε_k also").
    {#MD2.2.6.152-1} These are kept as factors in T_{j+1}.
    {#MD2.2.6.152-2} CRE p.268 removes a (3.3) factor only on cubes □′ ⊂ R_{j+1}ᶜ, where it "is equal to 1, because of the bound on A_k introduced by the second", the (3.16) factor.
    {#MD2.2.6.152-3} So the support is unchanged.
  - {#MD2.2.6.153} By (a), Input 1, A_j′ = g_jA_j on the free bonds, so |A_j| < O(1)ε_j/g_j = O(1)A₀(log g_j^{−2})^{p₀}.
    {#MD2.2.6.153-1} This bounds the slot variable σ_j = A_j of (b) directly, which is the bound the ω-clause uses.
    {#MD2.2.6.153-2} After ψ_{j+1} on S_{j+1}, |g_jA_j^{new} − g_jA_j| ≤ 2|𝐇^{(j)}| ≤ δ_j/20 by (a)'s proof step (b), and δ_j = (A₁/A₀)ε_j (Input 4).
    {#MD2.2.6.153-3} So also |A_j^{new}| ≤ O(1)ε_j/g_j on the support.
  - {#MD2.2.6.154} At j = 0.
    {#MD2.2.6.154-1} IT-1 note §3d(2)(d) gives |a_old| < r on I∖D(Λ) and |A_e(b)| < r on J for exterior data in the support of the collar indicators, with r = δ₀/g₀ = A₁(log g₀^{−2})^{p₀} (V4 Remark main-regime (1)). ω₀ is bounded on all of Ω₁∩Λᶜ by the step-1 small-field test on Ω₁: |e^{ig₀A(b)}Z_b − 1| < 2δ₀ with |Z_b − 1| < 2δ₀ from (B1) (proof of V4 Lemma boundary-bijection, (b)) gives |e^{ig₀A(b)} − 1| < 4δ₀, so |g₀A(b)| ≤ 2πδ₀.
    {#MD2.2.6.154-2} Since δ₀/g₀ = r, this is |B(b)| ≤ Cr with an absolute C, with the conversion between phases and B-units of IT-1 note §3d(2)(d).
    {#MD2.2.6.154-3} The j = 0 condition below holds with C in place of 2.
- {#MD2.2.6.155} *The size of w on the layer of ω_j.* On a block B^n(y), n ≤ k, the chain of (106) has n steps.
  {#MD2.2.6.155-1} By (4)(d), *Size*, the j′-th bracket has |log| ≤ O(L)L^{j′}η sup|𝐇| with η = L^{−k}, and the real transports preserve |·|.
  {#MD2.2.6.155-2} The sum over j′ < n gives |log W_y| ≤ O(1)L^nη·sup_{B^n(y)}|𝐇| = O(1)L^{n−k}sup_{B^n(y)}|𝐇|, with 𝐇 in fine units as in (4)(d).
  {#MD2.2.6.155-3} At complex backgrounds the chain's transports are G^c-valued and the conjugations cost the factor e^{4c_Gdι(1 + o(1))} = 1 + o(1) on the constant ((4)(d′), Step 8 (ii)–(iii)).
  - {#MD2.2.6.156} *The complex data.* The ω-dependent old factors are evaluated at R(w(s,t))ω on the whole polydisc of (4)(e)–(f), |s(Δ)| ≤ e^{κ_s}, |t_Y| ≤ T_Y, not only at t = 1.
    {#MD2.2.6.156-1} There sup|𝐇(s,tB′)| ≤ 4B₀e^{16κ_s}(max_YT_Y|B′|_Y + sup|B′|) ≤ min(β,1)α_{1,k}/4 + 8C₁^{RG2}B₀e^{16κ_s}O(1)ε_k =: h_k, by 1/T_Y ≥ 16B₀e^{16κ_s}|B′|_Y/(min(β,1)α_{1,k}) ((4)(f)).
    {#MD2.2.6.156-2} The second term is ≤ min(β,1)α_{1,k}/4, since ε_k/α_{1,k} ≤ (A₀/C₁)(log g_k^{−2})^{p₀−q₁} (#MD2.4.5.2-1) tends to 0 uniformly in k for q₁ > p₀ (g_k ≤ (1+β₀)g_K, g_K small); so h_k ≤ min(β,1)α_{1,k}/2 ≤ α_{1,k}/2, CRE p.277's margin's inequality in its complex-data form.
    {#MD2.2.6.156-3} So the size is O(α_{1,k}), not O(ε_k).
  - {#MD2.2.6.157} *The adjacent layer, j = k−1.* There n = k, the layer Ω_k∖Ω_{k+1} is in the scale-k region, and RG2 (1.18) bounds 𝐇 by h_k directly.
    {#MD2.2.6.157-1} So |log w| ≤ C_wh_k.
  - {#MD2.2.6.158} *Older layers, j ≤ k−2.* The sites lie in Ω_{j+1}∖Ω_{j+2} ⊆ Ω_kᶜ, where no k-independent sup bound of 𝐇 holds: VAR (190), p.308, bounds δ𝓗_μ(B,x)/δB_ν(y′) by O(1)(L^jη)^{−1}(L^{j′}η)^{−d}exp(−⅛δ₀d(y,y′)) for x ∈ Δ(y), y ∈ Λ_j, y′ ∈ Λ_{j′}, and the prefactor (L^{j+1}η)^{−1} = L^{k−j−1} cancels the chain's gain L^{j+1−k}.
    {#MD2.2.6.158-1} The decay replaces it:
    - {#MD2.2.6.159} d is PRT2's weighted distance (2.46), p.231.
      {#MD2.2.6.159-1} PBG p.397 l.29 cites it as "(2.36) in [4]", [4] = PRT2 (PBG p.433). PRT2's (2.36), p.229, is Σ_□h_□² = 1, and PRT2 defines one distance on 𝔅, (2.46) (p.230 l.52–p.231 l.14), its only other distance being the ℓ¹ norm |x − y| (p.223 l.15–16); VAR p.288 l.45 cites the same paper, its [3] (p.309), for "the distance d(y,y′), y,y′ ∈ 𝔅_k". So the equation number is misprinted and d is PRT2 (2.46) (READINGS_RECHECK #RR.39): d(y,y′) = inf_Γ Σ_m(L^mη)^{−1}|Γ∩B^m(Λ_m)|, each layer's length in its own block units.
    - {#MD2.2.6.160} VAR (1), p.277: (L^mη)^{−1}dist(Ω_mᶜ, Ω_{m+1}) > RM₁.
      {#MD2.2.6.160-1} A contour from B(Γ_{k+1}) ⊆ Ω_{k+1} to the layer Ω_{j+1}∖Ω_{j+2} crosses Ω_m∖Ω_{m+1} for m = j+2, …, k, each with weighted length > RM₁.
      {#MD2.2.6.160-2} So d > (k−j−1)RM₁.
    - {#MD2.2.6.161} Integrating the derivative along tB′ (𝓗(0) = 0) and keeping half the decay for the sum over y′ gives, at s = 1, sup_{B^{j+1}(y)}|𝐇| ≤ O(1)L^{k−j−1}e^{−δ₀(k−j−1)RM₁/16}h_k.
    - {#MD2.2.6.162} *At the complex data.* VAR (190) is printed for VAR's 𝓗 at s = 1.
      - {#MD2.2.6.163} *Single scale, from RG2 p.5.* RG2 bounds H(s(Y₀))X by (1.11), "B_0|X|sup_ω M_1^{−1/2|ω|}exp(−δ_0d(ω))e^{mκ_1}", and for m > 2⁴, "δ_0d(ω) ≥ δ_1mM".
        {#MD2.2.6.163-1} If δ₁M ≥ 2κ₁ (twice RG2's δ₁M ≥ κ₁; a condition on M, fixed before the coupling), then e^{−δ₀d(ω)}e^{mκ₁} ≤ e^{−δ₀d(ω)/2} for m > 2⁴, and for m ≤ 2⁴ the factor is at most e^{16κ₁}e^{−δ₀d(ω)}.
        {#MD2.2.6.163-2} So RG2's single-scale H(s) keeps half the decay of the walks at complex s.
        {#MD2.2.6.163-3} The walk bound behind (1.11) is RG2 (1.7), p.3, [13]'s (3.108): the term of ω is bounded by O(1)O(M₁^{−1/2})^{|ω|}M₁^{−1/2|ω|}exp(−δ₀d(ω,y,y′)), Δ(y), Δ(y′) its localisation cubes, and "This bound holds for all operator norms in formulations of theorems in [13], e.g. in Theorem 3.1".
        {#MD2.2.6.163-3-1} Since d(ω,y,y′) ≥ d(ω) (PBG (3.93), p.410, is the infimum of lengths of paths from y to y′ through all domains of ω, each a tree meeting them all; for generalized walks it is the shortest such tree, p.427 l.20), the factor e^{mκ₁} ≤ e^{16κ₁}e^{δ₀d(ω)/2} leaves e^{16κ₁}e^{−δ₀d(ω,y,y′)/2} per walk, a kernel decay in each of these norms.
      - {#MD2.2.6.164} *CRE p.277's 𝐇-decay.*
        {#MOMGD.55} On CRE's multi-domain lattice, 𝐇(s, tB′) on the polydisc obeys VAR (190)'s kernel bound with the rate halved, in the sup and in the scale-weighted gradient norm, and, for the 𝐉-conditions, in the Laplacian and P₁ norms (#MOMGD.57).
        {#MOMGD.55-1} Read per layer, each layer i crossed contributes θ_i := e^{−δ₀R_iM₁/32}, by VAR (1) in the layer's own units and the additivity across layers of (190)'s distance d(y, y′) (#MD2.2.6.159); the response chain uses this form (#MD2.2.6.190-39), and with the least R it is #MD2.2.6.165's θ.
        {#MD2.2.6.164-1} Bałaban states the multi-domain extension: CRE p.267 ("Their properties are essentially the same as before, because of the localization of the field A_k") and p.277, which asserts the comparison made here: "The localization of the fluctuation field, and the exponential decay of the minimizing function 𝐇_k imply that this difference is still much greater than bounds on this function".
        {#MD2.2.6.164-2} The rate is computed from VAR (190) (VAR Prop. 9) and RG2 p.5's argument above, which keeps half the walk decay at complex s, run on the multi-domain walks by CRE p.276 l.18–20 ("We repeat again the analysis of Sect. 6 [I], with the only change that the random walk expansions we use now are constructed for the sequence {Ω_j}").
        {#MOMGD.55-2} Its B′-range is that of its sources, RG2's |B′| < ε₃ (p.6 l.16) and VAR (172), both absolute, so it contains D2.1(4)'s |B′| ≤ ε_H (D2.6 closure §4.2).
        {#MD2.2.6.164-3} The gradient part uses RG2 p.5's all-norms bound (#MOMGD.54).
      - {#MD2.2.6.165} With CRE p.277's 𝐇-decay, sup_{B^{j+1}(y)}|𝐇(s,tB′)| ≤ O(1)L^{k−j−1}θ^{k−j−1}h_k on the polydisc, with θ := e^{−δ₀RM₁/32}.
        {#MD2.2.6.165-1} So |log w| ≤ C_wθ^{k−j−1}h_k on ω_j's layer.
    - {#MD2.2.6.166} CRE's domains satisfy VAR (1) with R of the size of R_{j}: the layers are built from a fixed number of layers of LMR_{j+1}-cubes around the large-field regions (CRE p.265: "four layers of the LMR_{k+1}-cubes, i.e., we take the domain Z_k′^{∼4}", then further single layers and "two layers of such cubes"), and R_j ≥ (log g_j^{−2})^r (CRE (2.5)) is large uniformly in j for g_K small.
  - {#MD2.2.6.167} So |log w| ≤ C_wθ^{k−j−1}h_k at the sites of ω_j, j ≤ k−1, with θ := e^{−δ₀RM₁/32} and C_w independent of j, k; for j ≤ k−2 this rests on CRE p.277's 𝐇-decay.
- {#MD2.2.6.168} *The radii.* Fix r_{ω,j} when ω_j is created: r_{ω,0} := 1 in V4's B-units (D(1)(iii)), and r_{ω,j} := g_j^{1/2} for j ≥ 1 (D2.6 closure §2.2 *Complex σ_k*).
  {#MD2.2.6.168-1} At g_j^{1/2} the per-cube Kotecký–Preiss sum of the localised source terms x_X (closure 2.2 (2), the random-walk expansion of K) is ≤ C_KB₀e^{16(3^d+1)a}A₁g_k^{1/2}(log g_k^{−2})^{p₀} → 0, under the condition δ₁M ≥ (3^d+1)a on M.
  {#MD2.2.6.168-2} The radius is used only as a domain (no Cauchy estimate in ω).
  {#MD2.2.6.168-3} The membership below holds since g_j|σ_j| ≤ O(1)ε_j + g_j^{3/2} ≤ 2O(1)ε_j for small g; *Propagation* is #MD2.2.6.175–#MD2.2.6.179-2, and the slot-value move #MD2.2.6.193.
  - {#MD2.2.6.169} In slot variables (b), the insertions depend on ω_j = σ_j, the old A_j, and not on A_j^{new}.
    {#MD2.2.6.169-1} So the cutoff g in ψ_{j+1} never enters their analyticity (in the slot form ψ only gives the values).
    {#MD2.2.6.169-2} At j = 0 the same convention holds with ω₀ = Ψ_ξA′ and the cutoff values ω_b frozen (D(k)(iii) above, D2.6 closure §6.1).
  - {#MD2.2.6.170} At step j+1, σ_j enters through the configuration U_j(exp i[g_jCσ_j − hD̃(g_jCσ_j)]V^{(j)}) of CRE (3.15) (the old factors and the terms 𝐄, 𝐑, 𝐁, A(1/g_j²(·) − 1/g_j², ·)), through the quadratic form ⟨A_j, C*Δ^{(j)}CA_j⟩ of (3.15), and through 𝐏^{(j)}(g_j, U_{j+1}, A_j) of (3.15) and (3.27).
    {#MD2.2.6.170-1} The cross terms of the quadratic form between A_j|_{Λ_{j+1}} and σ_j are linear in σ_j, hence entire.
    {#MD2.2.6.170-2} The analyticity of 𝐏^{(j)} in the outer field A_j = σ_j is printed nowhere (CRE (3.43) complexifies the integration field only); it is derived in WILSON_IT1_O6_CLOSURE_2026_10_26.md.
    {#MD2.2.6.170-3} Every σ_j-dependence of the actions of (3.27) and (3.29), apart from the entire quadratic forms, passes through the composite field B′ = g_jC(σ_j, A) − hD̃(g_jC(σ_j, A)), which RG2 §1 treats as a variable field (RG2 p.6: "in the preceding considerations B′ was a variable field").
    {#MD2.2.6.170-3-1} So the analyticity in (σ_j, A) jointly is composition with RG2 (1.19)–(1.20) on CRE p.277's margin's domain 𝒫_j^m = {g_j|B| < r_{α,j}/C₁^{RG2}}, r_{α,j} = min(β,1)α_{1,j}/(16B₀e^{16κ_s}) (the bracket terms 𝐄, 𝐑, 𝐁, A(·) are analytic in the shift only on CRE's g-scaled spaces (2.28), (2.34)–(2.39), CRE p.277's margin, p.277;
    {#MD2.2.6.170-4} 𝐏^{(j)}'s terms on the absolute domain e^{16κ₁}|B′| ≤ a₁), uniformly over the term's (𝐔, 𝐉)-space.
    {#MD2.2.6.170-5} The bound for 𝐏^{(j)}'s terms is the real-support bound with the fluctuation factor and the coefficients at most doubled and the quadratic forms' values by at most 8 (g_j sup|B| ≤ c₃ε_j + g_j^{3/2} + 6h_j ≤ 2c₃ε_j on the ω-polydiscs, h_j = max(c_He^{−R_j}ε_j, S_H)).
    {#MD2.2.6.170-6} The bracket terms are bounded by the Schwarz lemma on CRE p.277's margin's domain, with the margin-limited coefficient of order ε_j/α_{1,j} in place of p.277's O(ε_j) and their Y-localisation by one t_□-derivative and RG2's σ(Δ)-circles (O6 closure §5), the bound on 𝒫_j^{3/4} = {sup|B′| < 3r_{α,j}/4};
    {#MD2.2.6.170-7} at the consumers' points they carry p.277's coefficient O(ε_j) times 2 with the decay rate reduced by ϑ_j → 0 (O6 closure §5a, from p.277's bound on the size-set K′ (O6 §5a(i)) and CRE p.277's margin for the 𝐄- and 𝐑-brackets (CRE p.276 l.2–13, l.38–39), with p.277's A(·)-suppression (p.277's suppression of the A(·)-coefficients by 𝐇_j's decay) derived in §5a(ii) from p.277's printed support statement, CRE (2.24), (2.1) and CRE p.277's 𝐇-decay, condition (C7)), and V^{(j)}'s action part uses §5a at a Cauchy radius g_j^{3/2} ((C4′));
    {#MD2.2.6.170-8} only CRE (3.28)'s derivatives (O6 §9) use the margin-limited coefficient, at Cauchy radius r_{α,j}/(4C₁^{RG2}g_j) inside 𝒫_j^{3/4} under (C3), with no further condition.
    {#MOMGD.36} *The consumers.* The consumers' points of #MD2.2.6.170-7 are those of the att bounds at complex σ_k of D2.6 closure §2.2–§2.3, §4.3, and §5.0, which receive the bracket terms with p.277's coefficient O(ε_j) times 2 and the decay rate reduced by ϑ_j; these bounds are inputs of (S-w) (#MD2.4.12.52), on which (Z) rests (#MD2.3.4.58).
    {#MD2.2.6.170-9} The membership of the consumers' points in 𝒫_j^m is #MD2.2.6.173's computation, a smallness condition on g_K under q₀ = q₁ > p₀ (O6 closure §4); 𝒫_j^m contains the support, and (3.43)'s A-radius, defined nowhere, is not used (O6 closure §7; the bounds on the support are D2.6 closure 2.3 (c));
    {#MD2.2.6.170-10} V^{(j)}'s action part by a Cauchy estimate at half CRE p.277's margin's radius in the direction of the change of variables, and its Gaussian-form part −⟨K(σ_j, A) + ½Kδ, δ⟩, K = C*Δ^{(j)}C, bounded through K's random-walk expansion with S_{j+1} separated from Λ_{j+1} by (3.20)'s layer (O6 closure §6); conditions (C2), (C3), (C4′), (C5) and (C7) there, smallness conditions on g_K given (q₀ = q₁ > p₀).
    - {#MD2.2.6.171} *V^{(j)}.* p.269: the change of variables on S_{j+1} changes the action "by terms corresponding to (1.24), and by terms obtained by the first order expansion of the action with respect to the perturbative parts of the changes of variables.
      {#MD2.2.6.171-1} We denote this new part of the action by V^{(k)}(S_{k+1},A_k,𝐇^{(k)}).
      {#MD2.2.6.171-2} All terms of the previous action contribute to it", and p.271 puts V^{(k)}(S_{k+1}) inside ⟨·⟩_{s=1,t} and tV^{(k)}(S_k) into the measure (3.27).
      {#MD2.2.6.171-3} So V^{(j)} depends on the integrated field, and its dependence on σ_j (the S_{j+1}-bonds are bonds of σ_j) enters Ĥ(M) through the measure.
    - {#MD2.2.6.172} On (R_{j+1}^{∼2}∩S_{j+1})^{(j)*} the change of variables is (1.22), "A(b) = (1/ig_0)log exp ig_0A′(b)exp(−ig(A′(b))𝐇_{1,Ax}(b))" (p.251) with 𝐇^{(j)}(b) in place of 𝐇_{1,Ax}(b), and the Jacobian is (1.24) (p.252).
      {#MD2.2.6.172-1} Both carry the cutoff values g(A_j′(b)), and (1.24) also their derivatives.
      {#MD2.2.6.172-2} These are frozen as real factors θ_b := g(A_j′(b)), θ′_b := g′(A_j′(b)) at the real configuration and kept with the indicators, as for the cutoff in the slot form.
      {#MD2.2.6.172-3} At frozen θ, A_j′(b) = (1/ig_j)log(exp(ig_jσ_j(b))exp(−iθ_b𝐇^{(j)}(b))) (the sign of (1.22)) is analytic in σ_j for g_j|σ_j| small, and V^{(j)} is the first-order term of the action in the perturbation together with the (1.24) terms.
      {#MD2.2.6.172-4} The change of variables is analytic in σ_j at frozen θ, but V^{(j)} is the first-order term of the whole action, 𝐏^{(j)} included, so its analyticity in σ_j is derived with O6 (WILSON_IT1_O6_CLOSURE_2026_10_26.md §6: a directional derivative of the analytic action of #MD2.2.6.170 at points of CRE p.277's margin's domain 𝒫_j^m, bounded by a Cauchy estimate at radius r_{α,j}/(2C₁^{RG2}g_j), plus the entire Gaussian-form part bounded through K's random-walk expansion).
      {#MD2.2.6.172-5} Its size on S_{j+1} is O(|𝐇^{(j)}|) ≤ O(1)ε_je^{−R_j} at real backgrounds (p.269: 𝐇^{(k)} is "bounded on the set S_{k+1} by O(1)ε_kexp(−R_k)") and ≤ S_H (#MOMGD.58) at the complex backgrounds of D(j+1)(iii).
      {#MD2.2.6.172-6} V^{(j)} is in the list of the σ_j-dependences.
  - {#MD2.2.6.173} In the first, B′ = g_jCσ_j − hD̃(g_jCσ_j) is RG2 (1.19), with |B′| ≤ C₁^{RG2}g_j|B| for g_j|B| < ε₁^{RG2} (RG2 (1.20): "where C_1 is an absolute constant", written C₁^{RG2} here to keep it apart from CRE's C₁ in α_{1,k}).
    {#MD2.2.6.173-1} Fix c_ω ≤ O(1), the O(1) of CRE (3.14).
    {#MD2.2.6.173-2} For |σ_j − σ_{j,0}| < r_{ω,j} around a real σ_{j,0} in the support, g_j|B| < 2O(1)ε_j, so |B′| ≤ 2C₁^{RG2}O(1)ε_j.
    {#MD2.2.6.173-3} So D2.1(4)'s conditions, (4)(f)'s margin condition and CRE p.277's margin's entailment hold with O(1) replaced by 2C₁^{RG2}O(1).
    {#MD2.2.6.173-4} These are smallness conditions on g_K under q₁ > p₀; the O6 closure's Cauchy and localisation radii use its (C3), C₁^{RG2}ε_j^♯ < r_{α,j}/2.
  - {#MD2.2.6.174} D(m)(iii)'s ω-clause, m ≥ j+1 (polydiscs): joint analyticity in σ_j on the polydiscs |σ_j − σ_{j,0}| < r^{(m)}_{ω,j} := r_{ω,j}(1/2 + 2^{−(m−j)}) per bond, around real σ_{j,0} in the support.
    {#MD2.2.6.174-2} At k = 1 this matches the row domain, the polydisc 𝒰_c.
    {#MD2.2.6.174-3} So r^{(j+1)}_{ω,j} = r_{ω,j} at creation (r^{(1)}_{ω,0} = 1 = r_ω^{(1)}), decreasing to r_{ω,j}/2.
    {#MD2.2.6.174-4} These are the powers of 1/2 of CRE (2.36)–(2.39), used in the same way.
- {#MD2.2.6.175} *Propagation.* At the step k → k+1, k ≥ j+1, (4)(c) needs |σ_j − σ_{j,0}| + (e^{2c_G|log w|} − 1)(|σ_{j,0}| + |σ_j − σ_{j,0}|) < r^{(k)}_{ω,j} whenever |σ_j − σ_{j,0}| < r^{(k+1)}_{ω,j}.
  {#MD2.2.6.175-1} The two radii differ by r_{ω,j}2^{−(k+1−j)}.
  {#MD2.2.6.175-2} With e^{x} − 1 ≤ 2x for x ≤ 1 and |log w| ≤ C_w′θ^{k−j−1}h_k, C_w′ := C_w + 3d (C_w + 2d at k = 1; (4)(d), the representative's v₁), it suffices that 4c_GC_w′θ^{k−j−1}h_k(|σ_{j,0}|/r_{ω,j} + 1) ≤ 2^{−(k+1−j)}, that is
  {#MD2.2.6.176} 16c_GC_w′(2θ)^{k−j−1}h_k(|σ_{j,0}|/r_{ω,j} + 1) ≤ 1.
  {#MD2.2.6.177} *At r_{ω,j} = g_j^{1/2}:* |σ_{j,0}|/r_{ω,j} ≤ O(1)r_jg_j^{−1/2} and h_k ≤ α_{1,k} (#MD2.2.6.170-5), and CRE (2.6) gives g_j ≥ g_k(1 + β′(k−j))^{−1/2} for g_k ≤ 1, so h_kr_jg_j^{−1/2} ≤ Cg_k^{1/2}(log g_k^{−2})^{q₁+p₀}(1 + β′(k−j))^{1/4}(1 + log(1+β′(k−j)))^{p₀}, which (2θ)^{k−j−1} makes small uniformly in k, K for g_K small.
  {#MD2.2.6.178} (The slot values at complex backgrounds are bounded by a total move inside the smallest polydisc, the bullet below, so no per-step reservation is needed.
  {#MD2.2.6.178-1} The factor (|σ_{j,0}| + |σ_j − σ_{j,0}|) ≤ |σ_{j,0}| + r_{ω,j} covers any point of the polydisc, the slot values included.)
  - {#MD2.2.6.179} θ = e^{−δ₀RM₁/32} ≤ 1/4 once RM₁ ≥ 64 log 2/δ₀.
    {#MD2.2.6.179-1} This holds for g_K small, since the layer widths are of the size of R_j and R_j ≥ (log g_j^{−2})^r (above), uniformly by CRE (2.5) and g_j ≤ (1+β₀)g_K.
    {#MD2.2.6.179-2} Then (2θ)^{k−j−1} ≤ 2^{−(k−j−1)}.
  - {#MD2.2.6.180} *j ≥ 1:* the condition is the bullet *At r_{ω,j} = g_j^{1/2}* above.
  - {#MD2.2.6.181} *j = 0.* |σ_{0,0}|/r_{ω,0} ≤ Cr with r := r₀ = A₁(log g₀^{−2})^{p₀} ≤ A₁(log ĝ₀^{−2})^{p₀} (#MD2.0.3.35-2, #MD2.0.1.7), and r is not bounded by a power of log ĝ_k^{−2} alone.
    {#MD2.2.6.181-1} ĝ₀^{−2} = ĝ_k^{−2} + b′k (#MD2.0.1.7; BETA_FUNCTION_WILSON_LOOPS.md #B2.2.158), so log ĝ₀^{−2} ≤ log ĝ_k^{−2} + log(1 + b′k), as ĝ_k ≤ 1.
    {#MD2.2.6.181-2} Hence, with α_{1,k} = ĝ_kC₁(log ĝ_k^{−2})^{q₁} (#MD2.2.4.78) and (x + y)^{p₀} ≤ 2^{p₀}(x^{p₀} + y^{p₀}), α_{1,k}r2^{−(k−1)} ≤ 2^{p₀}C₁A₁ĝ_k(log ĝ_k^{−2})^{q₁}[(log ĝ_k^{−2})^{p₀} + sup_{k≥1}2^{−(k−1)}(log(1 + b′k))^{p₀}].
    {#MD2.2.6.181-3} The sup is finite, and the bracket times ĝ_k(log ĝ_k^{−2})^{q₁} is small for g_K small, uniformly in k and K, since ĝ_k ≤ g_k ≤ (1+β₀)g_K. So the j = 0 condition holds.
  - {#MD2.2.6.182} The layer decay θ^{k−j−1} carries the propagation; the chain's gain L^{j+1−k} is cancelled on older layers by VAR (190)'s prefactor.
  - {#MD2.2.6.183} *The complex A_k-domain with ω-dependent factors.* On D2.1(4)'s complex A_k-domain g_k|A_k| ≤ ε_H/C₁^{RG2}, sup|𝐇| reaches 4B₀e^{16κ_s}ε_H, a fixed constant, and the j = 0 condition fails (ε_H r → ∞ as g₀ → 0).
    {#MD2.2.6.183-1} So where ω-dependent factors are present the radius is cut to the α_{1,k} scale, g_k|A_k| ≤ cα_{1,k}/C₁^{RG2}; D2.4 does this by (4)(f)'s T_Y condition (#MD2.4.9.11-2).
  - {#MD2.2.6.184} *The slot values at complex backgrounds: a total-move bound.* At the complex backgrounds of later steps the slot values σ_j(b) = ψ_b(A_j^{new}(b);
    {#MD2.2.6.184-1} 𝐇^{(j)}(b)) move with 𝐇^{(j)}, which is "an analytic function of the background field U_{k+1} restricted to Λ_{k+1}^c∩Λ_k" (CRE p.269, (3.22), at k = j; p.269 states no domain of analyticity); A_j^{new} and the frozen cutoff values θ_b stay real (θ_b, not ω_b, to keep them apart from the outer fields ω).
    {#MD2.2.6.184-2} The move is bounded in total, not per step: the polydiscs r^{(m)}_{ω,j} = r_{ω,j}(1/2 + 2^{−(m−j)}) of D(m)(iii)'s ω-clause all contain the polydisc of radius r_{ω,j}/2 about the real slot value, and the rotations R(w) map r^{(k+1)} into r^{(k)} (*Propagation*), so it suffices that every slot value at every complex background reached lies within r_{ω,j}/4 of its real value.
    - {#MD2.2.6.185} *VAR Prop. 9's 𝐇^{(j)}: analyticity and bound from VAR Sect. G, Prop. 9, and CMP 98 Prop. 3.* Let Y_j be the support of p.269's determining set of 𝐇^{(j)} (𝔅_{j+1}(Λ_{j+1}^c)|_{Ω_{j+1}} ∪ 𝔅_j(Λ_j)|_{Ω_{j+1}^c}), that is Λ_{j+1}ᶜ∩Λ_j as on p.269, which meets the layers n = j+1 and n = j.
      {#MD2.2.6.185-1} Let 𝒰_j be the set of 𝐔 on Y_j satisfying (2.34), (2.38) and (2.39) of Ũ^c_{j+1}(Y_j, α̃₀, α̃₁) on Y_j.
      {#MD2.2.6.185-2} On 𝒰_j the analytic extension of 𝐇^{(j)} of (3.22) is bounded on S_{j+1} by S_H := C_H(α_{0,j+1} + α_{1,j+1})e^{−R_j} (= C_H(1 + C₁/C₀)α_{0,j+1}e^{−R_j} under q₀ = q₁, SW closure §2).
      {#MD2.2.6.185-3} The derivation below uses only α_{i,n} → 0 uniformly as g_K → 0, so a fixed factor on the α's of 𝒰_j would only enter C_H. 𝐇^{(j)} is a function of the background U_{k+1} only (p.269), so the 𝐉-conditions (2.36) are vacuous for it.
      {#MD2.2.6.185-4} (2.35) and (2.37) constrain configurations built on a domain X, U_{p,X}(M^·(𝐔)) and J_{p,X}(M^·(𝐔)), and are left out of 𝒰_j: the bound below does not use them (the argument bound runs on 𝐔 and its averages, REG (1.65)).
      - {#MD2.2.6.186} *What is printed, and what is not.* Printed (Bałaban's): 𝐇^{(j)} is "an analytic function of the background field U_{k+1} restricted to Λ_{k+1}^c∩Λ_k, bounded on the set S_{k+1} by O(1)ε_k exp(−R_k)" (p.269, at k = j; no domain is stated); it is obtained from (3.17) "with similar bounds";
        {#MD2.2.6.186-1} VAR Prop. 9 (p.309): 𝓗 "is an analytic function of B, and also of the external gauge field configuration U satisfying the regularity conditions (3.35)–(3.38) [5], or (1.7)–(1.9) [6]", and "its functional derivative (182) satisfies the inequalities (190)", and p.309: "These functions and operators can be extended to arbitrary, regular configurations U … They are analytic functions of these configurations, having the properties and bounds as described above"; PBG (3.37)–(3.38) is the complex class U′U, |A′| < α₁(L^jη)^{−1};
        {#MD2.2.6.186-2} CRE p.261 calls Ũ^c "a more detailed and precise form, suitable for our inductive constructions, of the regularity conditions for background fields, introduced in [13–15]".
        {#MD2.2.6.186-3} Derived from these: since 𝓗(0) = 0, 𝓗(B) = ∫₀¹Σ_{y′}(δ𝓗/δB(y′))(tB)·B(y′)dt, so by (190) |𝓗(x)| ≤ O(1)(L^jη)^{−1}e^{−δ₀D/16}sup|B|, D the distance from x to supp B (half the rate of (190)'s e^{−δ₀d(y,y′)/8} pays the sum over y′, which is ≤ O(1)(16/δ₀)^d; the factor (L^{j′}η)^{−d} of (190) is the density of a functional derivative with respect to the scalar product with volume element (L^{j′}η)^d, and with that element in the y′-sum it cancels; read so, as for the propagators whose bounds (190) is said to copy, p.307);
        {#MD2.2.6.186-4} this has the form of p.268's bound B₃exp(−δLM₂R_{k+1}) times the bound on the argument (a paraphrase, not a quotation), at complex regular U, with δ₀/16 in place of p.268's δ (*Constants* for the comparison with e^{−R_j}).
        {#MD2.2.6.186-5} *The argument bound at complex 𝐔.* p.268 bounds the argument (1/i)log[M^·(U_{k+1})(M^·(Q*_{k+1}V_{k+1}))^{−1}] of 𝐇_{k+1,□′} by 44d²B₃ε_{k+1} from the real regularity |∂U_{k+1} − 1| < 2B₃ε_{k+1}(L^{−1}η)².
        {#MD2.2.6.186-6} The computation behind this "hence" is REG Lemma 1 (pp.79–80), iterated over the scales as in REG (1.65) (p.87; CRE p.247 cites the same lemma for the analogous step-1 bound, "by the same reasoning as in the proof of Lemma 1 [14]").
        {#MD2.2.6.186-7} In the axial gauge, a link of the ratio is bounded by the plaquette deviations summed along block paths of at most (d−1)(L−1) bonds, plus the deviation of the block averages.
        {#MD2.2.6.186-8} *The gauge.* This is for 𝐔 = U′U whose real base U is in the axial gauge of CRE p.248 relative to the layer's blocks (p.247: U_{1,□′} is taken in the axial gauge; REG Lemma 1's hypothesis (1.24)); 𝒰_j carries no gauge condition and is G-invariant (its conditions are), and at a point not in that relation the argument is O(1).
        {#MD2.2.6.186-9} Reduction: for a G-valued v on Y_j the axial averages are covariant, M^·(𝐔^v) = M^·(𝐔)^{v̄} with v̄ the restriction of v to the block centres of the level in question (CMP 98 (93), "for an arbitrary gauge transformation v", one level; iterated over the levels; the transports obey R(U^u(Γ_{y,x})) = R(u(y))R(U(Γ_{y,x}))R(u^{−1}(x)), PBG p.395 before (3.32)), and the minimisers obey U_k(V^υ) = U_k(V)^{ῡ} with ῡ the block-constant extension of the data transformation υ, "constant on blocks B^j(y), y ∈ Λ_j, and equal to υ(y)" (VAR (181), p.307, extended to G^c-valued V and υ by analyticity);
        {#MD2.2.6.186-10} the reference data, a lift of the top data, transform by the lift of v̄_top, block-constant on the top blocks (Q^{s*}(V^t) = (Q^{s*}V)^{t̂} by (1.3)).
        {#MD2.2.6.186-11} So the j-th averages of both minimisers at a bond b ∈ S_{j+1}^{(j)*} transform by block-constant transformations, which at b₋, b₊, away from the lower-level collar strips, both equal v(y_top(b±)), the value at the centre y_top(b±) of the top-level block of the region of Y_j containing b± (the (j+1)-block on Ω_{j+1}; the j-block on Λ_j∩Ω_{j+1}ᶜ, which a bond of S_{j+1}^{(j)*} leaving Ω_{j+1} reaches, and where both data families have top level j);
        {#MD2.2.6.186-12} in e^{i𝐇^{(j)}(b)} = V^{(j)}(b)(V^{(j)}_{Y_j}(b))^{−1} the factors at b₊ cancel and 𝐇^{(j)}(𝐔^v)(b) = v(y_top(b₋))𝐇^{(j)}(𝐔)(b)v(y_top(b₋))^{−1}, of the same modulus, the norm on 𝔤^c being Ad(G)-invariant (with v = 1 at the top block centres of both regions, as the axial gauge allows, it is equality).
        {#MD2.2.6.186-13} Every real U has an axial representative U^v with v G-valued (REG p.79: "The conditions (1.19) determine uniquely an element in each orbit given by the subgroup (1.14)", and the orbit of U under all G-valued transformations meets that subgroup's orbits), and 𝐔^v = e^{iξvA′v^{−1}}U^v with |vA′v^{−1}| = |A′|; so 𝐔^v ∈ 𝒰_j is in the axial relation, and the bound at 𝐔^v is the bound at 𝐔.
        {#MD2.2.6.186-14} Its inputs at 𝐔 ∈ 𝒰_j: the curvature of 𝐔 and of its averages Ū^m at every level m, which is all REG (1.65) uses (p.87: CMP 98 Prop. 2 gives |∂Ū^m − 1| < 2α₀L^{2m}η² from |∂U − 1| < α₀η², and Lemma 1 is applied to these averages level by level; Lemma 1 is local, p.80, so it applies on the lower-level collar strips of CRE p.256 too, where the averages are smoother); for 𝐔 this is (2.34) with α_{0,n} at the weight where p.268 has 2B₃ε_{k+1} (*Unit check*), and p.268's own input is likewise the regularity of the background U_{k+1} alone;
        {#MD2.2.6.186-15} and the deviation of the averages, which CMP 98 bounds at complex data: Proposition 3 (p.36), posed for A ∈ 𝔤^c over a real V₀ with (109) (p.34), makes Q(V₀, A) = (1/i)log of the average analytic in A with Q = L(Q(V₀)A) + C(V₀,A), |(Q(V₀)A)_c| < e^{O(1)L²α₀}α₁ by (126) and |C| < C₁^{CMP}(Lα₁)² by (123), composed over the scales by CMP 98 (127)–(129) (each composition < 2α₁), so by (2.39) the deviation is O(α_{1,n}).
        {#MD2.2.6.186-16} REG's proof uses unitarity only in |XY − 1| ≤ |X − 1| + |Y − 1| and in the isometry of the conjugations R(·).
        {#MD2.2.6.186-17} For G^c-valued factors, |∏(1 + x_i) − 1| ≤ e^{Σ|x_i|} − 1, and over a block path of at most dL links each with phase below α_{1,n} by (2.39), ‖R(X)‖ ≤ ‖X‖‖X^{−1}‖ ≤ e^{2dLα_{1,n}} (R(X)Y = XYX^{−1}, CMP 98 (56), and submultiplicativity).
        {#MD2.2.6.186-18} So the bound holds with a factor 1 + O(d²α_{0,n} + dLα_{1,n}) ≤ 2, and the argument is O(α_{0,j+1} + α_{1,j+1}).
        {#MD2.2.6.186-19} *From the minimiser function to 𝐇^{(j)} at complex 𝐔.* The mean-value step bounds the minimiser function 𝓗 (p.268's 𝐇_{k+1,□′} of (3.17)); 𝐇^{(j)} of (3.22) is the logarithm of the ratio of j-th averages, reached on p.268 through (3.18) and CMP 98 (106)–(108), (159)–(163) at real data.
        {#MD2.2.6.186-20} At complex data: by (3.18), with p.269's replacement, e^{i𝐇^{(j)}(b)} = Φ_b(h) with h = L^{−1}η𝓗, Φ_b(h) = u(h)^{−1}(b₋)·exp iQ̃_j(h)·(R̄^ju(h))(b₊), as in (3.18).
        {#MD2.2.6.186-21} Here u = u_{j+1,□′} is the transformation from the Landau to the axial frame of the configuration e^{iη𝓗}U_{j+1,□′}, an analytic function of 𝓗 (VAR p.307: "This transformation is an analytic function of 𝓗"), with u(0) = 1, the reference being in the axial frame already; by CMP 98 (106) it is a product over the levels of conjugated ratios of the averages along the contours Γ_{x_{l+1},x_l}, so it depends on h only within the top-level blocks containing b₋, b₊.
        {#MD2.2.6.186-22} Q̃_j(h) depends on h only on the bonds of the blocks of b (CMP 98 p.34: the average at c involves only the bonds in B^k(c_−) ∪ B^k(c_+)).
        {#MD2.2.6.186-23} Let B_b be the bonds of these blocks; its diameter is O(L) in the units of (190).
        {#MD2.2.6.186-24} At X = 0 the data on the determining set agree, so the two minimisers agree ((3.17), first line), 𝓗 = 0 and the ratio is 1: (1/i)log Φ_b(0) = 0 at every background, real or complex.
        {#MD2.2.6.186-25} *Scale.* CMP 98 (127)–(129) are posed for U₁ = e^{iηA} with |A| < α₁, a field bound: after n averaging steps the phase is < 2α₁L^nη, so in phases a level-n average multiplies the input phase by up to 2L^n.
        {#MD2.2.6.186-26} With n_b the number of levels from 𝓗's lattice to b's lattice (n_b ≤ j: (3.18) takes the j-th average, and (106) uses the averages of the levels up to j along contours inside the (j+1)-blocks), (1/i)log Φ_b is a composition of CMP 98's averaged logarithms (Prop. 3 with (127)–(129), A ∈ 𝔤^c over the real base U of 𝐔 = e^{iξA′}U) and of the factors of u(h), each a near-unit analytic function of these averages (on the polydisc the phases of these averages are ≤ 2L^{n_b}ρ_b = c₃/2, so ‖R(u^{±1})‖ ≤ e^{O(dL)c₃} ≤ 2 once c₃ ≤ c/(dL);
        {#MD2.2.6.186-27} Prop. 3's composition condition 8C₁^{CMP}α₁ ≤ 1/3 ((129), (131)) is posed on the input field bound, which is c₃/4 in level-n_b units; with the safe upper bound c₃/2 it is c₃ ≤ 1/(12C₁^{CMP}); and the principal logarithm in (1/i)log Φ_b is defined while C_{d,L}c₃ < 1: three smallness conditions on c₃, met by taking c₃ smaller, which leaves the Schwarz factor M_b/ρ_b = C_{d,L}L^{n_b} unchanged and only tightens the g_K-threshold sup_{B_b}|h| < ρ_b).
        {#MD2.2.6.186-28} Hence (1/i)log Φ_b is analytic on the polydisc |h|_{B_b} < ρ_b := (c₃/4)L^{−n_b}, with modulus ≤ M_b := C_{d,L}ρ_bL^{n_b} (the averages' 2L^{n_b}ρ_b plus u's phases, O(dL) such terms per level).
        {#MD2.2.6.186-29} Schwarz's lemma (applied to λ ↦ (1/i)log Φ_b(λh/|h|_{B_b}), |λ| < ρ_b) gives |𝐇^{(j)}(b)| ≤ (M_b/ρ_b)|h|_{B_b} = C_{d,L}L^{n_b} sup_{b′∈B_b}|L^{−1}η𝓗(b′)|; sup_{B_b}|h| ≪ ρ_b by the mean-value step.
        {#MD2.2.6.186-30} The factor L^{n_b} is the ratio of b's length to the length of 𝓗's bonds, and it cancels against the field normalisation (L^{j_x}η)^{−1} of the mean-value step, j_x ∈ {j, j+1} the layer at the point, since n_b ≤ j ≤ j_x and L^{n_b}·L^{−1}η·(L^{j_x}η)^{−1} ≤ 1 in these units; so |𝐇^{(j)}(b)| ≤ C_{d,L}e^{O(L)δ₀}O(1)e^{−δ₀D/16}sup|B|, which is S_H on S_{j+1} (the e^{O(L)δ₀} from B_b's diameter).
        {#MD2.2.6.186-31} At real data this is p.268's form: (3.19) bounds the j-th average ratio by O(1) times the bound on 𝐇 itself.
        {#MD2.2.6.186-33} *Analyticity on 𝒰_j.* 𝐇^{(j)} depends on 𝐔 only through the data M^·(𝐔) on its determining set D_j (by (3.17), first line, with p.269's replacement: V^{(j)} and V^{(j)}_{Y_j} are the j-th averages of the minimisers with these data; off minimisers F∘M is the definition of the extension, the convention of *Which function is deformed*), so the evaluation point's own third-order behaviour never enters.
        {#MD2.2.6.186-34} At 𝐔 = e^{iξA′}U, M^·(𝐔) = V′V₀ with V₀ = M^·(U) real, satisfying VAR (7) by the real part of (2.34) and CMP 98's averages, and V′ analytic in A′ with |(1/i)log V′| < 2α_{1,n} at the scale weight (CMP 98 Prop. 3, (127)–(129)).
        {#MD2.2.6.186-35} So V′ satisfies VAR (172), |V′ − 1| < C₁^{VAR}ε₁, with ε₁ taken as the larger of V₀'s curvature bound in (7) and 3α_{1,n}/C₁^{VAR} (|V′ − 1| ≤ e^{|B′|} − 1 ≤ (3/2)|B′| for |B′| < 2α_{1,n} ≤ 1/2), which is ≤ a₁ for g_K small.
        {#MD2.2.6.186-36} VAR Sect. G (pp.305–307): U_k(V′V₀) is "an analytic function of V′, for V′ with values in a small neighborhood of the identity in G^c", and U_k(V′V₀)U_k(V₀)^{−1} in the Landau gauge is e^{iη𝓗(B)}, 𝓗 satisfying (19)–(21) at ε₂ = B₅ε₁ ((173)).
        {#MD2.2.6.186-37} The reference data are the lift of the top data: Q^{s*} acts bondwise (CRE (1.3): (Q^{s*}V)(b) is V(c) on the bonds b between B(c₋) and B(c₊) of the block bond c, and 1 inside the blocks), so Q^{s*}(V′V₀) = Q^{s*}(V′)Q^{s*}(V₀), and the averages of a lift are the lift, M^m(Q^{s*}V) = Q^{s*}_{top→m}V at every level m (the averaging loops of CMP 98 (110), (113), p.34, Γ_{c,x} ∪ (−c): the contours inside the blocks carry 1, the crossing between the blocks carries V(c) and −c carries V(c)^{−1}, so every loop is 1 and the average at c is V(c); by induction over the levels);
        {#MD2.2.6.186-38} hence the reference data at V′V₀ are V″D_ref(V₀) with V″ = Q^{s*}(V′) exactly, analytic in A′ with |(1/i)log V″| < 2α_{1,n}, and (127)–(129) are not needed for this concentrated input; the same applies to the reference minimiser.
        {#MD2.2.6.186-39} The j-th averages of both minimisers are analytic by CMP 98 Prop. 3 over the real bases U_k(V₀), applied in the Landau frame, where the ratio is e^{iη𝓗} with 𝓗 field-small by VAR (19) (in the axial frame it is only phase-small, REG p.80), and carried to the axial frame by u, analytic (above).
        {#MD2.2.6.186-40} The logarithm of their ratio is analytic.
        {#MD2.2.6.186-41} So 𝐇^{(j)} is analytic in A′ on 𝒰_j, in fact wherever the real part satisfies (2.34) and |A′| is below the fixed constants of CMP 98 Prop. 3 and VAR (172); no gradient or third-order condition on A′ is used.
        {#MD2.2.6.186-42} *Complex external fields in the mean-value step.* There the external configuration is the reference minimiser at complex data, U₀ := U_k(V″V₀′) = e^{iη𝓗}U_k(V₀′) (Landau frame of VAR Sect. G).
        {#MD2.2.6.186-43} Two links make the mean-value step's function the one bounded: (i) U_k(XV″V₀′)U₀^{−1} in the Landau gauge is e^{iη𝓗(X;U₀)} at complex V″ too, since both sides are analytic in V″ near the real slice (p.307; Prop. 9's analyticity in the external U composed with V″ ↦ U₀) and agree there (Prop. 9 at the real data V″V₀′), so they agree by the identity theorem; (ii) the axial→Landau passage for U₀ is a G^c-valued transformation u_L, under which the operators and 𝓗 conjugate by PBG (3.33)–(3.34) (G′, R, Δ_a, G at U^u are R(u)(·)R(u^{−1});
        {#MD2.2.6.186-44} extended to G^c-valued u by analyticity, as VAR p.307 does for (181)), covered by p.309's extension to arbitrary regular U ("All the above considerations and properties are valid for this function also", the considerations including p.307's transformation), with conjugation cost ‖R(u_L^{±1})‖ ≤ 2: u_L is the tree-gauge transformation to the axial representative, unique in the orbit of REG (1.14)'s subgroup (REG p.79, (1.19)), fixed level by level by CMP 98 (77), (87) from the block-path transports of the averages of U₀ relative to those of U_k(V₀′);
        {#MD2.2.6.186-45} at level n a path has ≤ d(L−1) block bonds, whose averaged phases are ≤ 2L^nη sup|𝓗| ≤ 2ε₂L^{n−j} by (127)–(131) and VAR (19), so the paths contribute ≤ Σ_{n<j}d(L−1)2ε₂L^{n−j} ≤ 2dε₂ to the phase of u_L, the inverse block averages (105) of each level's factor in (106) another ≤ 2dε₂(1 + 4dε₂) ((105) is the exponential of the average of log T_x, T_x a product of ≤ d(L−1) G^c-valued near-unit factors with summed phase s < 2dε₂, so |T_x − 1| ≤ e^s − 1 and |log T_x| ≤ −log(2 − e^s) ≤ s(1 + 2s) for s ≤ 1/4), total ≤ 4dε₂ + 8d²ε₂²,
        {#MD2.2.6.186-46} and ‖R(u_L^{±1})‖ ≤ e^{8dε₂ + 16d²ε₂²} ≤ 2 for ε₂ ≤ (log 2)/(10d) (ε₂ = B₅ε₁ → 0 with g_K; these constants take the 𝔤^c phase norm to dominate the operator norm, and for a general compact G the factor c_G enters as in #MD2.2.6.196, the condition becoming c_Gε₂ ≤ (log 2)/(10d), still a smallness condition on g_K); u_L is analytic in 𝓗 as a finite product of the averages (Prop. 3), which is p.307's statement.
        {#MD2.2.6.186-47} It is the construction of u(h) above, applied to U₀.
        {#MD2.2.6.186-48} Its real part satisfies PBG (3.35)–(3.36) with α₀ = B₃ε₁ by VAR Thm 1 (9)–(10) (|A|, |∇A|, |∂*∂A| < B₃Mε₁(L^jη)^{−1,−2,−3}), and its complex part 𝓗 satisfies PBG (3.37)–(3.38) with α₁ = B₅ε₁ by VAR (19) (|A|, |∇A|, |D*DA| < ε₂(L^jη)^{−1,−2,−3}).
        {#MD2.2.6.186-49} So it lies in PBG's complex class (3.35)–(3.38), where VAR p.309 and Prop. 9 print the analyticity of 𝓗 and the bounds (190).
      - {#MD2.2.6.187} *Constants.* C_H = C(d, L, G, δ₀, B₃, B₅, β₀, C₀^{CRE}, C₁^{CRE}, C₁^{CMP}, c₃) with (190)'s O(1): δ₀ through the y′-sum, CMP 98's C₁^{CMP} and c₃ through Prop. 3, B₅ through VAR (173), G through the norm on 𝔤^c, CRE's C₀ and C₁ (p.259) through the layer-n = j and α₁/α₀ comparisons, L also through the factor C_{d,L}L^{n_b} of the analytic bound before its cancellation. p.269's O(1) does not enter.
        {#MD2.2.6.187-1} The decay: the argument is supported in p.268's boundary layer of width 2LM₁ along ∂Λ_{j+1}, and S_{j+1} lies beyond p.269's layer of LMR_{j+1}-cubes, so the distance from S_{j+1} to that support is ≥ LMR_{j+1} − 2LM₁ ≥ ½LMR_{j+1} in p.268's units, in which the (j+1)-blocks have side L (CRE p.246: "cubes of the size LMR₁ … For the more natural scale L^{−1} these are … MR₁-cubes"; p.256: Ω_j are unions of MR_j-cubes of T_{L^{−j}}), since M ≥ 4M₁ and R_{j+1} ≥ 1 (CRE p.245: "M will be chosen much larger than M₂", M₂ > M₁).
        {#MD2.2.6.187-1-1} A bond of S_{j+1}^{(j)*} with an endpoint outside S_{j+1} is a bond of S_{j+1} (#MD2.2.6.15-3), at most one bond closer to the support, which changes the decay factor by at most e^{δ₀/16}, absorbed into C_H.
        {#MD2.2.6.187-2} Y_j's second boundary component, the collar strips along ∂Λ_j (layer n = j), carries argument too; it is farther from S_{j+1} ⊂ Ω_{j+1}: by CRE (3.5) with p.265's B^{j+1}(P¹_{j+1}) = (P′^∼_{j+1})ᶜ∩(Z_j′^{∼5})ᶜ, Z_j = Λ_jᶜ, Ω_{j+1} is separated from Λ_jᶜ by eight layers of LMR_{j+1}-cubes, so the first component's bound covers it.
        {#MD2.2.6.187-3} (190)'s distance is that of [3] = PRT2 (2.46) (p.231; in the local set), which counts the blocks of the layer's own lattice: on Ω_{j+1} these are (j+1)-blocks, so the separation is ≥ ½MR_{j+1} in its units (a path through the layer n = j counts j-blocks, L per (j+1)-block, so it is longer there), and at rate δ₀/16 the decay factor is e^{−(δ₀/32)MR_{j+1}} up to O(1).
        {#MD2.2.6.187-4} By CRE (2.9), R_j ≤ (L+1)R_{j+1}, so e^{−(δ₀/32)MR_{j+1}} ≤ e^{−R_j} once (δ₀/32)M ≥ L+1: a condition on M, which Bałaban chooses last, after δ₀, L and M₂ (at j = 0 the condition δM ≥ L+1 below).
        {#MD2.2.6.187-5} For comparison, p.268 prints B₃exp(−δLM₂R_{k+1})44d²B₃ε_{k+1} ≤ 44d²B₃²(1+β₀)exp(−R_k)ε_k with its own δ.
        {#MD2.2.6.187-6} On the layer n = j Ũ^c_{j+1}'s curvature bound is (1−β/2)α_{0,j} at the scale-j weight, and α_{0,j} ≤ (1+β₀)²α_{0,j+1} (CRE (2.6), (2.7), (2.28)), absorbed into C_H, as is the (1+β).
        {#MD2.2.6.187-7} The ratio α_{0,j+1}/ε_j ≤ (C₀/A₀)(1+β₀)²(log g_j^{−2})^{q₀−p₀} (CRE (2.4), (2.6), (2.7), (2.28), p.259).
    - {#MD2.2.6.188} *Which function is deformed.* As for all of Bałaban's old terms (RG1 (3.10): 𝐄^{(j)}(X, exp iξ𝐀U_{k+1})), the slot value at a step-k background 𝐔 is 𝐔 ↦ 𝐇^{(j)}(𝐔|_{D_j}), 𝐇^{(j)} evaluated at the restriction of the current fine background to its determining set D_j := 𝔅_{j+1}(Λ_{j+1}^c)|_{Ω_{j+1}} ∪ 𝔅_j(Λ_j)|_{Ω_{j+1}^c} (p.269; the convention of CRE (2.41)(i)–(ii)).
      {#MD2.2.6.188-1} D_j meets two layers: Λ_{j+1}ᶜ∩Ω_{j+1} ⊆ Ω_{j+1}∖Ω_{j+2} (by Ω_{j+2} ⊆ Λ_{j+1}), the layer n = j+1, and Λ_j∩Ω_{j+1}ᶜ ⊆ Ω_j∖Ω_{j+1}, the layer n = j.
      {#MD2.2.6.188-2} Here U is the real point of the step's real data, in the same frame as 𝐔 (the hierarchical mean axial gauge of #MD2.2.4.31).
      {#MD2.2.6.188-3} At the real configuration it is the real slot value, by D2.0(5)(c)(α) at the steps j+1, …, k (U_i(V^{(i)}) = U_{i+1}); this covers the slot values in insertions left untouched at every step, which (4)(e) evaluates at (U_{i+1}, ω).
      {#MD2.2.6.188-4} *Merged insertions.* Inside a group merged at a step i ∈ [j+1, k−1], 𝐇^{(j)} was evaluated at that step's evaluation point 𝐔_i = e^{iη(𝐇_i(s,tB′) + a″)}U_{i+1}, and at later steps it is evaluated at such composite points, not at 𝐔|_{D_j} of step k.
      {#MD2.2.6.188-5} Each is a step-i evaluation point whose base lies in D(i+1)(iii)'s domain, so (4)(f)'s chain condition at step i places it in Ũ^c_i, and *The inclusion* below with i in place of k places its restriction in VAR Prop. 9's 𝐇^{(j)}'s domain.
      {#MD2.2.6.188-6} So every point at which 𝐇^{(j)} is ever evaluated, at any step i ≥ j+1, is covered, and *The total move* stands unchanged.
      {#MD2.2.6.188-7} A slot value is a substituted value, not an insertion of D(k): its analyticity comes from VAR Prop. 9's 𝐇^{(j)} and the inclusion below, not from D(k)(iii).
      {#MD2.2.6.188-8} The slot value depends on 𝐔 on both layers n = j and n = j+1.
    - {#MD2.2.6.189} *The inclusion.* For k ≥ max(j+1, 2), D(k)(iii)'s domain is CRE's complex space Ũ^c_k (#MD2.0.3.54), and every evaluation point of the step k → k+1, 𝐔 = e^{iη(𝐇_k(s,tB′) + a″)}U_{k+1} with a″ in D(k+1)(iii)'s domain (the literal-base form, which #MD2.4.11.5 uses at a″ ≠ 0 as well), lies in it by (4)(f)'s chain condition, the same condition every old factor needs.
      {#MD2.2.6.189-1} Claim: every evaluation point 𝐔 satisfies 𝐔|_{Y_j} ∈ 𝒰_j, VAR Prop. 9's 𝐇^{(j)}'s domain.
      {#MD2.2.6.189-2} *No choice of X.* Y_j = Λ_{j+1}ᶜ∩Λ_j is the whole collar of every step-(j+1) large-field component, so it lies in no single old term's localisation domain.
      {#MD2.2.6.189-3} It need not: D(k)(iii)'s domain and (4)(f)'s margins are posed per bond and per cube on each Ω_n∖Ω_{n+1} (the loop's factors are not localised in Bałaban's X ∈ 𝐃_k, D(k)(iii)), so the pointwise conditions and (2.38) hold on every bond and cube and restrict to Y_j directly; (2.35) and (2.37) are not in 𝒰_j.
      {#MD2.2.6.189-4} Check, condition by condition of CRE p.261: on a layer n ≤ j+1, (2.34) (curvature, α_{0,n}) and (2.39) (A′ and its gradient, α_{1,n}) are pointwise and carry, for the space of index i, the factor (1 − β(1 − 2^{−(i−n)})), which is nonincreasing in i (read on p.261); so Ũ^c_k's conditions on the layers n = j+1 (factor (1 − β(1 − 2^{−(k−j−1)})) ≤ 1, Ũ^c_{j+1}'s top layer) and n = j (factor (1 − β(1 − 2^{−(k−j)})) ≤ 1 − β/2, Ũ^c_{j+1}'s) imply Ũ^c_{j+1}'s.
      {#MD2.2.6.189-5} (2.38) is the condition on the real configuration, BCMα_{0,n} with no index factor, on cubes of size CML^nξ, or CM inside the top domain, the same physical size in both spaces.
      {#MD2.2.6.189-6} The cube families match on Y_j: Ũ^c_{j+1}'s top domain uses all CM-cubes in Ω_{j+1}, Ũ^c_k's layer n = j+1 the cubes □ ⊂ Ω_{j+1}∖Ω_{j+3} with □∩Ω_{j+2}ᶜ ≠ ∅; on Y_j these agree, since a CM-cube meeting Ω_{j+2}ᶜ avoids Ω_{j+3} when its diameter √d·CM is below dist(Ω_{j+2}ᶜ, Ω_{j+3}).
      {#MD2.2.6.189-7} CRE p.256 gives the boundaries of consecutive Ω's at distance ≥ 2MR_i in the units of the layer's own lattice ("the distance between their boundaries is at least equal to 2MR_j"), so dist(Ω_{j+2}ᶜ, Ω_{j+3}) ≥ 2MR_{j+2}L in step-(j+1) units, and M cancels: the condition is √d·C < 2LR_{j+2}.
      {#MD2.2.6.189-8} (2.38)'s cube constant C is not fixed by p.261 (only B is called absolute); since R_{j+2} ≥ (log g_{j+2}^{−2})^r → ∞ as g_K → 0 (CRE (2.5), r ≥ 2 by p.245 l.34), √d·C < 2LR_{j+2} holds for every fixed C once g_K is small; the layer n = j and n = j−1 families (the latter reaches into Y_j∩Ω_j) coincide, with no index factor.
      {#MD2.2.6.189-9} So every evaluation point lies in 𝒰_j on Y_j, and |𝐇^{(j)}(𝐔|_{Y_j})| ≤ S_H there, by VAR Prop. 9's 𝐇^{(j)}.
      {#MD2.2.6.189-10} At k = 1 (only j = 0, below) D(1)(iii) is IT-1 note D1(iii)′'s sup-only domain, not contained in Ũ^c_1; there only the points reached at the step 1 → 2 count, and they lie in Ũ^c_1 on D₀ by (4)(f) at k = 1 (the evaluation points e^{iη(𝐇_1(s,tB′) + a″)}U_2), with the gradient condition from (6)(e)'s *The consumer still gets what it needs* via RG2 p.5's all-norms bound, the curvature condition (2.34) from its check, both written for general k and so at k = 1, and the base-point conditions for U₂ on D₀ from (6)(e)'s *The base point on Ω₁∖Ω₂* (on Ω₂ from *Derived instead of assumed*).
      - {#MD2.2.6.190} *The base point on Ω₁∖Ω₂.* The cited item covers U_{k+1} on Ω_{k+1} only.
        {#MOMGD.11} *Result.* At every k, on the terms of the form (2.21) with the printed characteristic functions (#MD2.2.6.190-12), U_{k+1} satisfies the real parts of (2.34) at n = 1 and of (2.38) on Ω₁∖Ω₂ ⊇ D₀: at k = 1 by VAR Theorem 1 applied to U₂ on the problem restricted to Ω₁^∼ (#MD2.2.6.190-13–#MD2.2.6.190-31), for k ≥ 2 by the response chain with this as its root (*For k ≥ 2*). VAR's R₁^V and M₁ are fixed constants, not CRE's scale R₁.
        {#MD2.2.6.190-1} D₀ := Ω₁∩Λ₁ᶜ, the set on which U₁(Ω₁∩Λ₁^c, V), and hence 𝐇_{1,Ax}'s background, depends (p.251 l.23 states this for U₁(Ω₁∩Λ₁^c, V), and (1.21), p.251 l.24–31, writes 𝐇_{1,Ax}(Ω₁∩Λ₁^c, ·) at this configuration, its argument restricted to a neighbourhood of ∂Λ₁, p.251 l.32–34), lies in Ω₁∖Ω₂, since Ω₂ ⊆ Λ₁.
        {#MD2.2.6.190-3} At the root k = 1 the real part of (2.34) at n = 1 and (2.38) for U₂ on all of Ω₁∖Ω₂, collar included, come from VAR Theorem 1 (p.279) for U₂ itself, as Bałaban obtains U₁'s existence ("By Theorem 1 [15]", p.248) and U_{k+1}'s regularity (p.267 (3.12): "The restrictions on the fields V_k, V_{k+1} on Ω_{k+1}^∼, and Theorem 1 from [15] imply, that U_{k+1} satisfies the following regularity condition"; "[15]" is the transcription's correction of the printed "[16]"; p.268).
        {#MD2.2.6.190-4} For k ≥ 2 the layer n = 1 is an older layer of the step k → k+1. CRE p.276 l.10–12 states U_{k+1}'s regularity there qualitatively ("on a neighborhood of Ω_n∖Ω_{n+1}" it is "the same as for U_n-configurations"; p.277 l.2: on Ω_{k+1}ᶜ "there is no regularity improvement of the configuration U_{k+1}", l.3–4: the powers of 1/2 as the room for the shifts; #MOMGD.20); *For k ≥ 2* below proves it, bounding the responses to the data changes on Ω_{m+1}, m = 2, …, k, on the layer n = 1 by CRE p.277's 𝐇-decay against the root's margin, the root being this item at k = 1.
        {#MD2.2.6.190-8} *The problem at k = 1.* U₂ is the critical point of the action with U = V₀ on Ω₁ᶜ and the determining conditions of 𝔅₂ on Ω₁ (the minimal-orbit map (2.12), p.256, with p.266 (3.10); (2.1)–(2.3) on p.255; CRE (1.12) is the step 0 → 1 problem for U₁).
        {#MD2.2.6.190-9} Only plaquettes meeting Ω₁ involve free variables, so it is VAR's problem (5)–(6) on Ω₀^{VAR} := Ω₁^∼ with Λ₀^{VAR} = Ω₁^∼∖Ω₁ carrying the fixed data V₀, Λ₁^{VAR} = Ω₁∖Ω₂ carrying V = V₁ and Λ₂^{VAR} = Ω₂ carrying V₂ (p.279: "B^j(Λ_j) ∪ B^{j+1}(Λ_{j+1}) = Ω_j∖Ω_{j+2}");
        {#MD2.2.6.190-9-1} VAR (1) holds (dist(Ω₁^{∼c}, Ω₁) is one layer of Ω₁'s cubes and dist(Ω₁ᶜ, Ω₂) ≥ 2LMR₁η by (1.20), both above R₁^VM₁ in the layer's units); VAR counts the plaquettes with at least one corner in Ω₀^{VAR}, and the fine plaquettes reaching one spacing beyond Ω₁^∼ are covered by p.248's χ₀ on the cubes □ ⊂ Ω₁^∼, which test p ⊂ □^∼;
        {#MD2.2.6.190-10} the omitted action terms are constants in the free variables, so the critical points are those of (2.12), and U₂ is the one in Theorem 1's class (6) by the regularity quote of #MD2.2.6.190-3 and V4 (H4) (next line), Theorem 1's uniqueness of the critical orbit in (6) for B₃ε^V ≤ ε₀ ≤ a₀ identifying the orbits, with the criticality-and-uniqueness argument of V4 sec:c3-9-1 (prop:c3-9-1, which treats U₁ at the step 0 → 1) as the template at the step 1 → 2; Bałaban identifies U_{k+1} with Theorem 1's minimal configuration on p.248 and p.267.
        {#MD2.2.6.190-11} "Regular" in (2.12) is printed: it is membership in VAR's 𝔘_k({Ω_j},ε₀). CRE refers (2.12) to [15] = VAR ("For precise definitions and the theory of this variational problem see [15]", p.256 l.49). VAR poses it as (5) on (6) = 𝔘_k({Ω_j},ε₀) ∩ 𝔙_k(𝔅_k,V), where 𝔙_k is the averaging constraint (3), CRE's M_𝐁(U) = V by (2.11), and 𝔘_k, defined by (2), is "a space of regular gauge field configurations" (VAR p.277 l.3, p.278 (2), (3), (6)).
          {#MD2.2.6.190-11-1} The radius ε₀ is immaterial: for B₃ε₁ ≤ ε₀ ≤ a₀ the orbit of (8) is "a unique critical orbit in the space (6)" (VAR Theorem 1, p.279 l.15), and a minimal orbit of (2.12) minimises A on an open subset of the constraint set, so it is critical and is that orbit.
        {#MD2.2.6.190-12} The 𝐑-operation changes the characteristic functions (p.258). For k ≤ N = N_k, the tube's depth (#MD2.3.4.16-1; D2.7 closure item 1(b)) no part of it acts on D(k) (#MD2.0.3.66): its basic step acts on no component of Λ_kᶜ by LFR I p.177 (ii) (#MD2.0.3.67), and 𝐑′^{(k)} = 0, Rρ_k = ρ_k term by term (D2.7 closure item 1(a)–(b); READINGS_RECHECK #RR.23–#RR.23-1). So on the terms of the form (2.21) the support carries the printed characteristic functions, and the 𝐑-modified terms, present only for k > N_k, are D2.7's (#MD2.3.4.16-2).
        {#MD2.2.6.190-13} *Hypothesis (7) on the support.* (7) asks |(∂V)(p′) − 1| < ε^V for every block plaquette of every layer, mixed plaquettes at a layer boundary taken with the averages V̄ (p.278).
        {#MD2.2.6.190-14} Layer n = 1: on the support χ₁(Ω₁) of (2.17) at k = 1 holds (V4 keeps it outside the A_e integral in eq:native-source-explicit-outer-operation and reads it in the measurability paragraph of sec:branch-data and in the proof of lem:c2-plaquette-deviation: χ₁(□′) = 1{V ∈ 𝒱_ax(□′)}·1{sup_{p⊂□′^∼}|U_{1,□′}(V)(∂p) − id| < ε₁L^{−2}} for every cube □′ of Ω₁'s decomposition).
        {#MD2.2.6.190-14-1} V = M(U_{1,□′}) on the block bonds of □′^∼ by 𝐁₁(□′^{∼4})'s conditions, so CMP 98 Prop. 2 (|∂Ū − 1| < 2α₀L²η² from |∂U − 1| < α₀η², read in #MD2.2.6.186) gives |∂V(p¹) − 1| < 2ε₁ for the block plaquettes p¹ of □′^∼, hence on Ω₁.
        {#MD2.2.6.190-15} The mixed plaquettes at ∂Ω₁ are block plaquettes whose fine-side bonds carry V̄₀; δ(V̄₀V^{−1}) ((1.11), (1.14)–(1.15), (2.21)) identifies V̄₀ with V on those block bonds, so they are block plaquettes of V near ∂Ω₁ inside Ω₁^∼, bounded by the same 2ε₁ (the cubes □′^∼ reach them); Prop. 2 on V₀, which gives only 2L²ε₀, is not needed.
        {#MD2.2.6.190-16} Layer n = 0 (Ω₁^∼∖Ω₁): "On the set Ω₁^∼ we have only the small field characteristic functions" and χ₀ "localized in Ω₁^∼ are equal to 1" (p.248; V4 (B1)(i), (B3)(i)), so |∂V₀ − 1| < ε₀ on the fine plaquettes there, with ε₀ ≤ (1+β₀)²ε₁ by (2.8) at (m, n) = (0, 1).
        {#MD2.2.6.190-17} Layer n = 2 (the top layer Ω₂ at k = 1): χ₂(Ω₂) of (2.17) and the determining conditions 𝐁₂ on Ω₂^∼ (p.267, "The restrictions on the fields V_k, V_{k+1} on Ω_{k+1}^∼"), so the block plaquettes of V₂ and the mixed plaquettes at ∂Ω₂ (block plaquettes of V̄₁ = V₂ by the δ at level 2) are bounded through Prop. 2 as on layer 1 by 2ε₂ ≤ 2(1+β₀)ε₁ ((2.8) at (1, 2)).
        {#MD2.2.6.190-18} So (7) holds with ε^V := 2(1+β₀)²ε₁, and ε^V ≤ a₁ for g_K small.
        {#MD2.2.6.190-19} *Conclusion (8): (2.34).* The minimal configuration lies in 𝔘₂({Ω_j}, B₃ε^V), that is (p.278 (2)) |∂U₂ − 1| < B₃ε^Vη²(L^nη)^{−2} on every layer n, in particular on Ω₁∖Ω₂ with the scale-1 weight η²(Lη)^{−2} = L^{−2} (η = ξ the fine spacing, as in *Unit check*).
        {#MD2.2.6.190-20} (2.34) at n = 1 for the space of index j ≥ 1 asks (1 − β(1 − 2^{−(j−1)}))α_{0,1}L^{−2} ≥ (1−β)α_{0,1}L^{−2}, so membership needs B₃ε^V < (1−β)α_{0,1}: as in *Derived instead of assumed*, q₀ > p₀ for g_K small, or q₀ = p₀ with C₀/A₀ > 2(1+β₀)²B₃/(1−β).
        {#MD2.2.6.190-21} B₃ depends on d and L only (p.279; V4 (H4)).
        {#MD2.2.6.190-22} *Conclusions (9)–(10): (2.38).* Write R₁^V for VAR's fixed constant R₁ of (1) (p.277), distinct from CRE's scale R₁.
        {#MD2.2.6.190-23} Theorem 1 gives, for every cube □ of its class of side 2M^VL^jη (M^V a multiple of R₁^VM₁, M^V ≤ M(ε^V) = R₁^VM₁a₁/ε^V, with □̃ of side (2M^V + 4R₁^VM₁)L^jη inside Ω_j∖Ω_{j+2} and not inside Ω_{j+1}∖Ω_{j+2}), a gauge u on a neighbourhood of □ with U^{u^{−1}} = e^{iηA}, |A| < B₃M^Vε^V(L^jη)^{−1}, |∇A| < B₃M^Vε^V(L^jη)^{−2}.
        {#MD2.2.6.190-24} (2.38) at n = 1 asks this on the cubes □ ⊂ Ω₁∖Ω₃, □∩Ω₂ᶜ ≠ ∅, of side CMLξ, with Lξ|A|, (Lξ)²|∇A| < BCMα_{0,1}; at k = 1, Ω₃ = ∅.
        {#MD2.2.6.190-25} Covering: take M^V₁ := the least multiple of R₁^VM₁ with 2M^V₁ ≥ CM + 2R₁^VM₁ (j = 1) and M^V₀ := L(M^V₁ + 2R₁^VM₁) (j = 0); both ≤ M(ε^V) for g_K small.
        {#MD2.2.6.190-26} A (2.38)-cube □ at distance d from Ω₁ᶜ lies in a j = 1 cube □¹ (side 2M^V₁Lη ≥ CMLη + 2R₁^VM₁Lη) with □̃¹ ⊂ Ω₁ whenever d ≥ 4R₁^VM₁Lη + (2M^V₁ − CM)Lη =: d₁ (place □¹ ⊇ □ away from Ω₁ᶜ, with the alignment slack of one block in the extra 2R₁^VM₁Lη); □̃¹ ⊂ Ω₁∖Ω₃ = Ω₁ and □̃¹ ⊄ Ω₂∖Ω₃ = Ω₂ since □ meets Ω₂ᶜ (for general k the disjointness from Ω₃ would come from Ω₃ ⊆ Λ₂ ⊆ Ω₂^{∼−2}, (3.5), (1.20)).
        {#MD2.2.6.190-27} For d < d₁, □ lies in a j = 0 cube □⁰ of side 2M^V₀η ≥ 2M^V₁Lη + 4R₁^VM₁Lη, placed towards Ω₁ᶜ so that dist(□⁰, Ω₁ᶜ) ≤ max(0, d − (2M^V₀ − CML)η) < 2R₁^VM₁η (d − (2M^V₀ − CML)η < 0 by d < d₁ = 2M^V₀η − CMLη, and the alignment costs at most M₁η), that is □̃⁰ meets Ω₁ᶜ, and □̃⁰ ⊂ Ω₁^∼∖Ω₂ since dist(Ω₂, Ω₁ᶜ) ≥ 2LMR₁η exceeds □̃⁰'s diameter (Ω₂ ⊆ Λ₁ ⊆ Ω₁^{∼−2} by (1.20), with Λ₁ = Ω₁^{∼−2}∩(R₁′^∼)ᶜ on p.251; the comparison is 2R₁ > √d(C + 9R₁^VM₁/M), true for g small since R₁ ≥ (log g₁^{−2})^r); so □⁰ is in the j = 0 class.
        {#MD2.2.6.190-28} On □ ⊆ □⁰ the j = 0 bound reads Lη|A| < B₃M^V₀Lε^V and (Lη)²|∇A| < B₃M^V₀L²ε^V, on □ ⊆ □¹ the j = 1 bound Lη|A| < B₃M^V₁ε^V, (Lη)²|∇A| < B₃M^V₁ε^V; both are ≤ BCMα_{0,1} for g_K small, since M^V₀, M^V₁, L, B₃ are fixed and ε^V/α_{0,1} → 0 when q₀ > p₀, while for q₀ = p₀ the binding case (j = 0, ∇A) needs C₀/A₀ > 2L³(1+β₀)²B₃(CM/2 + 4R₁^VM₁)/(BCM) (M^V₁ ≤ CM/2 + 2R₁^VM₁; B is (2.38)'s absolute constant: under q₀ > p₀ any B > 0 works, under q₀ = p₀ it enters this condition); the gauge u is defined on a neighbourhood of □ ⊇ □∩X.
        {#MD2.2.6.190-29} This covers the collar Ω₁∖Ω₁^{∼−1} (the j = 0 cubes) without a separate argument.
        {#MD2.2.6.190-31} The result: U₂|_{Ω₁∖Ω₂} satisfies the real parts of (2.34) and (2.38) at n = 1, so at k = 1 the j = 0 base point on D₀ and the j = 1 base points on the layer n = 1 lie in CRE p.251's 𝐇₀'s and VAR Prop. 9's 𝐇^{(j)}'s domains; for k ≥ 2 U_{k+1}'s membership on the layer n = 1 is *For k ≥ 2* below, with this item as its root, and the layer-2 part of 𝒰₁'s domain (Ω₂∖Ω₃ at k ≥ 2; at k = 1 #MD2.2.6.136's p.268 item) is *Every older layer* below.
        {#MD2.2.6.190-32} *For k ≥ 2: the response chain.* Notation: U_m := U_{𝔅_m}(V₀|Γ₀, …, V_{m−1}|Γ_{m−1}, V_m) is CRE's minimal configuration at the step m → m+1 before the fluctuation integral, a function of the step-m variables with V_m on all of Ω_m (p.256 (2.12); p.266 (3.10)); U₂ is the root's configuration above.
        {#MD2.2.6.190-33} At the step m → m+1, (3.10)–(3.11) give U_{m+1} = U_{𝔅_m}(V₀|Γ₀, …, V_{m−1}|Γ_{m−1}, V_m|Γ_m, V^{(m)}|Ω_{m+1}) with V^{(m)} = M^m(U_{m+1}) ("This minimum is given by V^{(k)} = M^k(U_{k+1}), where the minimal configuration U_{k+1} is determined by the sequence of domains {Ω_{k+1}, Ω_k, …}, and the corresponding sequence of fields {V_{k+1}|Γ_{k+1}, V_k|Γ_k, …}") and V_m = e^{iA′_m}V^{(m)} on Ω_{m+1}, |A′_m| < c_Aε_m on the support by (3.14) (c_A := the constant of |A′_m| < c_Aε_m,
        {#MD2.2.6.190-34} the supremum over m of (3.14)'s 2δ_m/ε_m + (4dL)²(1+β₀)B₃ times the logarithm's factor 1 + o(1) in A′_m = (1/i)log V′_m, finite since (3.14) reads "= O(1)ε_k").
        {#MD2.2.6.190-35} So U_m and U_{m+1} are the minimal configurations of one determining set 𝔅_m at level-m data differing by A′_m on Ω_{m+1} only, and VAR Prop. 9's response function (the map's 𝐇_m, (4)(d′), Step 4, with B′ = A′_m) gives U_m = (e^{iη𝐇_m(A′_m)}U_{m+1})^{g_m} for a gauge transformation g_m (the minimal orbit;
        {#MD2.2.6.190-36} p.309, 𝓗 at the base U_{m+1}, which obeys PBG (3.35)–(3.38) as at #MD2.2.6.186 and lies in VAR's class with the crude constant ε^V_m := max(2(1+β₀)max_{i≤m+1}O(L²)ε_i, (3/2)c_Aε_m/C₁^{VAR}) ≤ a₁ by the global Theorem 1 for U_{m+1} ((7) is monotone in its constant), its hypothesis (7) from p.256's regularity of V_i on Γ_i and (3.12) on Ω_{m+1}; the crude constant enters Prop. 9's hypotheses only, not (190)'s bound, whose constants are uniform).
        {#MD2.2.6.190-37} Prop. 9's domain is VAR (172), p.305, |V′ − 1| < C₁^{VAR}ε^V_m, and V′ = e^{iA′_m} lies in it by the choice of ε^V_m, as at #MD2.2.6.186, so the path t ↦ e^{itA′_m}V^{(m)} needs no splitting; Bałaban applies (190) to sources of size ε_m directly on p.266 ((3.6)–(3.7)).
        {#MD2.2.6.190-38} *The response on the layer n = 1.* The source A′_m is supported on Ω_{m+1} ⊆ Ω₃, and the walk from Ω_{m+1} to the layer n = 1 crosses the layers 2, …, m, of widths ≥ 2MR_i in level-i cubes (p.256; Ω_{i+1} ⊆ Λ_i by (2.1)).
        {#MD2.2.6.190-39} CRE p.277's 𝐇-decay (#MOMGD.55; at the real base with (190)'s full rate) gives on the blocks B¹(y) of the layer n = 1: sup|𝐇_m(A′_m)|, (Lη)|∇_{U_{m+1}}𝐇_m(A′_m)| ≤ c_RL^{m−1}∏_{i=2}^{m}θ_i·c_Aε_m, with θ_i := e^{−δ₀R_iM₁/32} the factor of the layer i (CRE p.277's 𝐇-decay per layer: each layer i crossed contributes e^{−δ₀R_iM₁/32}, by VAR (1) in the layer's own units (L^iη)^{−1} and the additivity across layers of (190)'s distance d(y, y′), whose definition VAR p.288 takes from PRT2 [3]; the layer widths are of the size of R_i, #MD2.2.6.179).
        {#MD2.2.6.190-40} c_R is the constant of CRE p.277's 𝐇-decay (the letter chosen apart from CMP 98's c₃, c₄ of #MD2.2.4.39, #MD2.2.4.40 and #MD2.2.6.186, #MD2.2.6.187).
        {#MD2.2.6.190-41} With η = L^{−m} at the step m, the bond change on the layer n = 1 is η|𝐇_m| ≤ c_Ac_RL^{−1}∏_{i=2}^{m}θ_i·ε_m, and the plaquette change is ≤ 2η²|∇𝐇_m| + O(η²|𝐇_m|² + η|𝐇_m||∂U − 1|) ≤ 2c_Ac_RL^{−2}∏_{i=2}^{m}θ_i·ε_m(1 + o(1)) (the plaquette identity: e^{iηX}U around p equals the product of the four transports of e^{iηX(b)} along p times U(∂p), the exponents summing to η² times the covariant curl of X up to the holonomy defects, which carry |∂U − 1|).
        {#MD2.2.6.190-42} *The chain.* For any choice of the fluctuation variables A′_m in the supports of the steps m = 2, …, k (such a choice exists wherever the step-(k+1) term is non-zero, and the root applies to U₂ at step-2 data with χ₂(Ω₂) = 1),
        {#MD2.2.6.190-43} U_{k+1} = (e^{iηX_{k+1}}U₂)^{g} with e^{iηX_{k+1}} the product of the conjugates of e^{−iη𝐇_m(A′_m)}, m = 2, …, k (each g_m conjugates the earlier exponents and preserves their sizes), so on the layer n = 1, in the sup and the scale-weighted covariant gradient, |X_{k+1}| ≤ (1 + o(1))Σ_{m=2}^{k}|𝐇_m| by BCH, giving η|X_{k+1}| ≤ L^{−1}Δ_{k+1}(1 + o(1)) and 2η²|∇X_{k+1}| ≤ 2L^{−2}Δ_{k+1}(1 + o(1)) with Δ_{k+1} := Σ_{m=2}^{k}c_Ac_Rε_m∏_{i=2}^{m}θ_i ≤ c_Ac_Rε_*θ₂Σ_{m≥2}∏_{i=3}^{m}θ_i ≤ 2c_Ac_Rε_*θ₂ =: Θ, where ε_* := max_{m≤K}ε_m (≤ (1+β₀)ε(g_K),
        {#MD2.2.6.190-44} since g_m ≤ (1+β₀)g_K by (2.6) and ε(g) increases for small g) and θ_i ≤ ½ (#MD2.2.6.179).
        {#MD2.2.6.190-45} *The size of Θ.* R₂ ≥ (log g₂^{−2})^r with r ≥ 2 printed (CRE p.245, "R₀ ≥ (log g₀^{−2})^r, r ≥ 2"; the same r on p.246 and in (2.5)), and (2.7)'s second line at p = 2, (n, m) = (2, 1), gives (log g₁^{−2})² ≤ (1+β₀)(log g₂^{−2})², so R₂ ≥ (1+β₀)^{−1}(log g₁^{−2})² and θ₂ ≤ exp(−δ₀M₁(log g₁^{−2})²/(32(1+β₀))) = o(g₁^N) for every N; so Θ ≤ 2c_Ac_Rε_*θ₂ and Θ/g₁ → 0 with no condition on δ₀M₁.
        {#MD2.2.6.190-46} *Conclusion.* (2.34) at n = 1 for every index j: |∂U_{k+1} − 1| < (B₃ε^V + 2Θ(1 + o(1)))L^{−2} < (1−β)α_{0,1}L^{−2} once 2Θ(1 + o(1)) < (1−β)α_{0,1} − B₃ε^V; the right side is ≥ ½(1−β)α_{0,1} for g_K small under q₀ > p₀, and ≥ ((1−β) − 2(1+β₀)²B₃A₀/C₀)α_{0,1} > 0 under q₀ = p₀ with the root's strict condition; Θ/α_{0,1} ≤ 2c_Ac_Rε_*θ₂/(C₀g₁) → 0, so the condition holds for g_K small.
        {#MD2.2.6.190-47} (2.38) at n = 1: the cubes □ ⊂ Ω₁∖Ω₃ meeting Ω₂ᶜ of side CMLξ are the root's cubes (Ω₃ ⊆ Λ₂ ⊆ Ω₂^{∼−2}, at distance ≥ 2MR₂L² > CML from Ω₂ᶜ; their parts inside Ω₂, at most √d·CMLξ deep, carry the decay θ₂^{1−O(C/(MR₂))} and the smaller field normalisation (L²η)^{−1}, so the bounds below hold there as well), the gauge is the root's u composed with the orbit's g, and in it Lξ|A| ≤ B₃M^V₀Lε^V + Θ(1 + o(1)) and (Lξ)²|∇^ξA| ≤ B₃M^V₀L²ε^V + Θ(1 + o(1)) (the j = 0 cubes, the binding case; the j = 1 cubes the same with M^V₁ and without the L-powers;
        {#MD2.2.6.190-48} the covariant gradient of Ad_uX_{k+1} in the gauge u is Ad_u of the covariant gradient of X_{k+1} up to the commutator with ξA_root, of size |ξA_root||X_{k+1}|), both < BCMα_{0,1} once Θ(1 + o(1)) < BCMα_{0,1} − B₃M^V₀L²ε^V, which holds for g_K small by the same comparison (under q₀ = p₀ the root's strict condition C₀/A₀ > 2L³(1+β₀)²B₃(CM/2 + 4R₁^VM₁)/(BCM) leaves the room).
        {#MD2.2.6.190-49} *Within D(k).* The quantity carried by the induction is Δ_k (Δ₂ = 0, Δ_{k+1} = Δ_k + c_Ac_Rε_k∏_{i=2}^{k}θ_i ≤ Θ): D(k)'s real base point U_k satisfies the layer-1 conditions in the root's gauge with the excess Δ_k, and the step adds the step-k term.
        {#MD2.2.6.190-50} *Every older layer: the same chain.* For the layer n ≥ 2 at the step k → k+1, k ≥ n, the root is U_n on Ω_n ⊇ Γ_n: p.268's |∂U_n − 1| < 2B₃ε_n(L^{−1}η)² (the top-layer bound at the step n−1 → n, #MD2.2.6.135; the weight is L^{−2n}) and the top-layer (2.38) of #MD2.2.6.136 (SW closure §6(6d));
        {#MD2.2.6.190-51} the steps m = n, …, k add the responses to A′_m on Ω_{m+1}, the step n with no decay (CRE p.277's 𝐇-decay at zero layers crossed: sup|𝐇_n|, (L^nη)|∇𝐇_n| ≤ c_Rc_Aε_n on the blocks B^n(y), consistent with (6)(e) #MD2.2.6.156), the later ones with ∏_{i=n+1}^{m}θ_i; so on the layer n the excess is Δ^{(n)}_{k+1} := Σ_{m=n}^{k}c_Ac_Rε_m∏_{i=n+1}^{m}θ_i ≤ c_Ac_Rε_n + 2c_Ac_Rε_*θ_{n+1}, with the weights L^{−n} (bond angles) and L^{−2n} (plaquettes and angle differences;
        {#MD2.2.6.190-52} the (2.38)-cubes' parts inside Ω_{n+1} as at #MD2.2.6.190-47), and θ_{n+1} ≤ exp(−δ₀M₁(log g_n^{−2})²/(32(1+β₀))) by (2.5) with r ≥ 2 and (2.7)'s second line at p = 2, as at #MD2.2.6.190-45.
        {#MD2.2.6.190-53} Conditions: 2B₃ε_n + 2c_Ac_Rε_n(1 + o(1)) + 4c_Ac_Rε_*θ_{n+1} < (1−β)α_{0,n} for (2.34), and #MD2.2.6.136's top-layer (2.38) constant plus Δ^{(n)}_{k+1}(1 + o(1)) < BCMα_{0,n}; under q₀ > p₀ both hold for g_K small (ε_n/α_{0,n} = (A₀/C₀)(log g_n^{−2})^{p₀−q₀}), under q₀ = p₀ they need C₀/A₀ > (2B₃ + 2c_Ac_R)/(1−β) for (2.34) and C₀/A₀ > (c_{SW} + c_Ac_R)/(BCM) for (2.38), c_{SW} the top-layer constant of #MD2.2.6.136 (SW closure §6(6d); the global (7)-constant of the U_n problem is ≤ O(L²)(1+β₀)ε_n, since ε(g) increases for small g and g_i ≤ (1+β₀)g_n for i < n by (2.6)).
        {#MD2.2.6.190-54} So the curvature and gradient conditions of the real base on every layer come from p.268's top-layer bound, #MD2.2.6.136's top-layer (2.38), and CRE p.277's 𝐇-decay.
    - {#MD2.2.6.191} *The total move.* Since both the complex and the real value of 𝐇^{(j)}(·|_{D_j}) are bounded by S_H, |Δ𝐇^{(j)}| := |𝐇^{(j)}(𝐔|_{Y_j}) − 𝐇^{(j)}(U|_{Y_j})| ≤ 2S_H (Y_j the support of D_j, as in VAR Prop. 9's 𝐇^{(j)} and the inclusion) at every evaluation point 𝐔 of every step k ≥ j+1, a″ included, in a fixed frame; across the step's gauge frames it is 3S_H (*The gauge frame of σ_j*, #MD2.2.6.196).
      {#MD2.2.6.191-1} No decay in k − j is needed, because the move is charged once against the fixed cushion r_{ω,j}/4, not per step.
    - {#MD2.2.6.192} *From 𝐇^{(j)} to σ_j.* g_jσ_j(b) = (1/i)log(e^{ig_jA_j^{new}(b)}e^{−iθ_b𝐇^{(j)}(b)}) ((a)), θ_b ∈ [0,1].
      {#MD2.2.6.192-1} By BCH, D_X(1/i)log(e^{iy}e^{−iX}) = −I + O(|y| + |X|), so its norm is ≤ 2 for |y| + |X| ≤ c₂, an absolute constant, at complex X as well (the chart logarithm is analytic).
      {#MD2.2.6.192-2} Here |y| = g_j|A_j^{new}(b)| ≤ r_Kδ_j on the support ((6)(a)(c)) and |X| ≤ S_H, both ≪ c₂ for g_K small; c₂ depends on the norm on 𝔤^c, that is on G and its embedding.
      {#MD2.2.6.192-3} The segment between the real and the complex X lies in that ball (convex), so |Δσ_j| ≤ (2/g_j)|Δ𝐇^{(j)}| ≤ 4S_H/g_j and |Im σ_j| ≤ |Δσ_j| (σ_j is real at the real background).
    - {#MD2.2.6.193} *The condition at r_{ω,j} = g_j^{1/2}.* Across the gauge frames the move is |Δσ_j| ≤ 10S_H/g_j (#MD2.2.6.196), and 10S_H/g_j ≤ r_{ω,j}/4 = g_j^{1/2}/4 holds if 40C_H(α_{0,j+1} + α_{1,j+1})g_j^{−3/2}e^{−R_j} ≤ 1, true for g_K small since α_{i,j+1} ≤ (1+β₀)O(1)g_j(log g_j^{−2})^{q_i}, i = 0, 1, and R_j ≥ (log g_j^{−2})^r with r > 1 (CRE (2.4)–(2.7), (2.28)), uniformly in j and k, by g_j ≤ (1+β₀)g_K.
    - {#MD2.2.6.194} *j = 0.* The same with 𝐇_{1,Ax} of CRE (1.21)–(1.22) in place of 𝐇^{(j)} and r_{ω,0} = 1 in V4's B-units. p.251 prints, at the real configuration, "The dependence is analytic, and the function 𝐇_{1,Ax} has the exponential decay property.
      {#MD2.2.6.194-1} It was formulated in (190) Sect. G of [15] for the Landau gauge, but on the unit lattice it holds for any gauge, for which propagators are exponentially decaying, hence for the axial gauge too" (p.251 l.34–36), with the bound O(1)B₃e^{−δMR₁}ε₁ on □′ ⊂ S₁.
      {#MD2.2.6.194-1-1} The domain 𝒰₀ is the set of 𝐔 on D₀ = Ω₁∩Λ₁ᶜ (#MD2.2.6.190-1), the set on which 𝐇_{1,Ax}'s background U₁(Ω₁∩Λ₁ᶜ, V) of (1.21) depends (p.251 l.23), satisfying (2.34), (2.38), and (2.39) of Ũ^c_1 on D₀, as 𝒰_j does on Y_j (#MD2.2.6.185-1); U_{k+1}|_{D₀} lies in its real part by #MOMGD.11.
      {#MD2.2.6.194-2} S_H's e^{−R₀} needs δMR₁ ≥ R₀ at real data, which holds by (2.9) once δM ≥ L+1 (δ is p.251's real-data rate), and (δ₀/16)MR₁ ≥ R₀ at complex data, where the rate is (190)'s δ₀/16, implied by #MD2.2.6.187-4's (δ₀/32)M ≥ L+1; both are conditions on M, chosen last.
      {#MD2.2.6.194-3} The bound S_H on 𝐇_{1,Ax} at complex backgrounds is CRE p.251's 𝐇₀: the same derivation as VAR Prop. 9's 𝐇^{(j)}'s (p.251 writes 𝐇_{1,Ax} with the argument (1/i)log[M^·(U₁)(M^·(Q₁^{s*}V))^{−1}], the structure of p.268), with the axial gauge in place of the Landau gauge: p.251 states that the dependence of 𝐇_{1,Ax} on its argument "is analytic, and the function 𝐇_{1,Ax} has the exponential decay property … (190) … for the axial gauge too" (at real external U);
      {#MD2.2.6.194-4} at complex external U it is derived as the j = 0 case of *From the minimiser function to 𝐇^{(j)}*: by (1.21), e^{iL^{−1}𝐇_{1,Ax}(b)} is the ratio of the two axial-gauge minimisers on the unit lattice, u(h)^{−1}(b₋)·e^{iη𝓗(b)}U^L(b)·u(h)(b₊)u(0)(b₊)^{−1}·U^L(b)^{−1}u(0)(b₋), with U^L the reference minimiser in the Landau frame, 𝓗 its Landau-frame deviation (analytic with (190) at complex regular U, VAR p.309 and Prop. 9) and u the Landau→axial transformation (REG (1.19), CMP 98 (106); analytic in 𝓗, VAR p.307; block-local, ‖R(u^{±1})‖ ≤ 2, as in #MD2.2.6.186);
      {#MD2.2.6.194-5} no average is taken (n_b = 0), so Schwarz's lemma gives |𝐇_{1,Ax}(b)| ≤ C_{d,L}sup_{B_b}|η𝓗| and (190)'s decay with the factor e^{O(L)δ₀}; (190) is posed on VAR (172)'s complex domain, the axial configuration is an analytic function of 𝓗, hence of B (VAR p.307), and the analyticity in the data follows as for VAR Prop. 9's 𝐇^{(j)} (#MD2.2.6.186-33–#MD2.2.6.186-41), at the points reached: for k ≥ 2 the points of Ũ^c_k, by the inclusion above; for k = 1 the points e^{iη(𝐇_1(s,tB′) + a″)}U_2 reached at the step 1 → 2, not all of D(1)(iii).
      {#MD2.2.6.194-6} Across the gauge frames of #MD2.2.6.196 the phase → B conversion is |ΔB| ≤ 10S_H/g₀, since on a free bond the phase is g₀B (V4 sec:source-phase-primitives: q_U(B)(r) = g₀B(r)), and the condition 10S_H/g₀ ≤ 1/4 is 40C_H(α_{0,1} + α_{1,1})e^{−R₀} ≤ g₀, true for g₀ small since α_{i,1}/g₀ = O((log g₀^{−2})^{q_i}·g₁/g₀) and e^{−R₀} decays faster than any power of log g₀^{−2}.
    - {#MD2.2.6.196} *The gauge frame of σ_j.* σ_j is defined in the frame of the configuration U_k(e^{iB′}V^{(k)}) before the step's gauge transformation w = u_k^{−1}v₁ ((4)(d), w_tot), and the real centre σ_{j,0} must be read in the same frame; the two frames differ by R(w).
      {#MD2.2.6.196-2} How 𝐇^{(j)} transforms is VAR Prop. 9's 𝐇^{(j)}'s law (#MD2.2.6.186, *The gauge*): 𝐇^{(j)}(𝐔^v)(b) = v(y_top(b₋))𝐇^{(j)}(𝐔)(b)v(y_top(b₋))^{−1} for G-valued v, y_top(b₋) the centre of the top-level block of the layer containing b₋, extended to G^c-valued v by VAR (181)'s analyticity; so under the frame change the value conjugates by an element g with |log g| ≤ |log w|, and ‖Ad_g‖ ≤ e^{2c_G|log w|}.
      {#MD2.2.6.196-3} The frames reached on a layer n = j compose over the steps m = j+1, …, k, so the relevant size is the cumulative Σ_m|log w_m| ≤ Σ_m C_wθ^{m−j−1}h_m ≤ C_wh̄/(1−θ) for u_m's shares ((4)(c), (6)(e)), with h̄ the value of #MD2.2.6.156's h_k at the coupling (1+β₀)g_K (h_k is increasing in g_k, and g_m ≤ (1+β₀)g_K for every m), plus v₁'s shares from (4)(d), each ≤ 3dL^{j−m}θ^{m−j−1}h_m on the layer n = j at the step m ((4)(d′), Step 7), so Σ_m|log w_m| ≤ (C_w + 3d)h̄/(1−θ);
      {#MD2.2.6.196-4} the condition used below is Σ_m|log w_m| ≤ (log 2)/(4c_G), so that e^{4c_G Σ|log w_m|} ≤ 2 and e^{2c_G Σ|log w_m|} ≤ √2; it holds for g_K small, since h̄ is the bound h_k ≤ α_{1,k}/2 of #MD2.2.6.156-2 taken at g_k = (1+β₀)g_K, which tends to 0 with g_K, and θ ≤ 1/4 (#MD2.2.6.179).
      {#MD2.2.6.196-5} Hence |𝐇^{(j)}| ≤ 2S_H in every frame reached, and *The total move* needs no frame: the move is bounded by the sizes, |Δ𝐇^{(j)}| ≤ |𝐇^{(j)}(𝐔)| + |𝐇^{(j)}(U)| ≤ 3S_H, |Δσ_j| ≤ 6S_H/g_j before the frame discrepancy.
      {#MD2.2.6.196-6} The slot's own rotation law in Cov(k) is Ad_{w(b₋)} at the level-j site b₋ (the law of the fields ω, (4)(c)), while 𝐇^{(j)} conjugates at y_top(b₋); for b on the layer n = j the two sites coincide, and for b inside a (j+1)-block of Ω_{j+1} (the bonds of S_{j+1}) they differ by Ad_{w(b₋)w(y_top(b₋))^{−1}}, a rotation with |log| ≤ 2|log w|(1 + O(c_G|log w|)) (BCH; the factor is absorbed by the margin below, 2√2 < 4).
      {#MD2.2.6.196-7} The discrepancy acts on the value 𝐇^{(j)}(b)/g_j that the slot is built from, not on σ_j (σ_j can vanish while 𝐇^{(j)}(b) does not), so the slot value read in either frame differs from the other by at most |σ_j′ − Ad_{w(b₋)}σ_j| ≤ 2θ_b e^{2c_G|log w|}(e^{4c_G|log w|} − 1)|𝐇^{(j)}(b)|/g_j, with 𝐇^{(j)}(b) in the frame before the rotation (|𝐇^{(j)}| ≤ S_H there), |log w| the cumulative Σ_m|log w_m|, the factor e^{2c_G|log w|} ≥ ‖Ad_{w(b₋)}‖ for G^c-valued w, θ_b the frozen cutoff value g(A_j′(b)) ∈ [0, 1] of (6)(a) (not the decay ratio θ of #MD2.2.6.157),
      {#MD2.2.6.196-8} and 2 the BCH derivative bound; under the condition above this is ≤ 2√2(e^{4c_GΣ|log w_m|} − 1)S_H/g_j ≤ 4S_H/g_j; charged to the total-move cushion, |Δσ_j| ≤ 10S_H/g_j, and *The condition* reads 40C_H(α_{0,j+1} + α_{1,j+1})g_j^{−3/2}e^{−R_j} ≤ 1, a smallness condition on g_K as before.
      {#MD2.2.6.196-9} For (6)(b7)'s u, G-valued and B′-independent (REG (1.14)'s residual gauge transformations are those equal to 1 on 𝔅_k, not block-constant ones), the discrepancy is a real rotation that carries the real centre with the value, at no cost.
      {#MD2.2.6.196-10} The real support set is Ad_G-invariant, so for G-valued rotations the real centre and the complex value rotate together and the polydisc condition is frame-independent; for G^c-valued w the centre's displacement is #MD2.2.6.175's term, which (4)(c) budgets.
      {#MD2.2.6.196-11} The G^c-valued B′-independent c₀ of (4)(d′), Step 8, does not reach this bound on family (I), where c₀ = 1; at (11)(c)(β)'s polydisc points with a″ ≠ 0 it does, and #MD2.4.11.5 charges it to half of the per-step margin on 𝒟^{sub}.
- {#MD2.2.6.197} *Bonds crossing the layer boundaries.* The bonds of (4)(d)'s blocks that cross ∂Λ_j (VAR's Λ_j) are case (B) of D2.1(4); they are treated in WILSON_IT1_D26_CLOSURE_2026_10_24.md §4.4 (covariance by the transport law, size by §5.4).
- {#MD2.2.6.198} *Result: the slot values at complex backgrounds.* Every evaluation point of every step k ≥ j+1, a″ and the composite points of merged insertions included, restricts to 𝒰_j on Y_j (#MD2.2.6.188, #MD2.2.6.189), the base points on Ω₁∖Ω₂ by #MOMGD.11 and on the older layers by #MD2.2.6.190-50.
  {#MOMGD.58} There |𝐇^{(j)}| ≤ S_H (#MD2.2.6.185-2), and at j = 0 𝐇_{1,Ax} obeys the same bound on 𝒰₀ (#MD2.2.6.194).
  {#MOMGD.58-1} The move is |Δσ_j| ≤ 4S_H/g_j in a fixed frame (#MD2.2.6.192-3) and ≤ 10S_H/g_j across the gauge frames (#MD2.2.6.196); under 40C_H(α_{0,j+1} + α_{1,j+1})g_j^{−3/2}e^{−R_j} ≤ 1 (#MD2.2.6.193), that is S_H ≤ g_j^{3/2}/40, both lie within r_{ω,j}/4 = g_j^{1/2}/4 of the real value, inside every polydisc of D(m)(iii)'s ω-clause (#MD2.2.6.184-2).

{#MD2.2.6.199} *(f) Λ_{k+1} and L.*
- {#MD2.2.6.203} *Λ_{k+1}.* (6) uses CRE's Λ_{k+1} (p.269) as printed, with ω_k on Ω_{k+1}∩Λ_{k+1}ᶜ.
  {#MD2.2.6.203-1} No refinement of Λ_{k+1} is needed for (a)–(e): (a) works bond by bond on S_{k+1} ⊆ Λ_{k+1}ᶜ, (b)–(d) are identities, and (e) uses only Ω_{j+2} ⊆ Λ_{j+1} (CRE pp.264–265) and VAR (1).
- {#MD2.2.6.204} *L.* L is odd with L > 11 (V4 app:thresholds, opening list), and D2 takes β₀ ≤ 1/2 and L ≥ L₀ = 5000 (#MOMGD.37).
  {#MD2.2.6.204-1} These give D2.2(4)(f)'s L ≥ 2(1+β₀) (#MD2.2.4.72-3), D2.4(6)'s (1+β₀)⁸ < L (1.5⁸ < 26), and D2.4(12)(f)'s 8(1+β₀)^{15} ≤ L (#MD2.4.12.23-3).

## D2.3 Exact Absorption of δm_{k+1} and z_{k+1} {#MSD2.3}

### (0) What is needed {#MSD2.3.0}

- {#MD2.3.0.1} *Input.* D2.2's output on a labelled term ℓ of ρ_{k+1}: ⟨𝒲_k⟩_{1,1} = κ^{(k)}e^{𝓔_k}·Σ_𝔉 Q(𝔉)·dim(π)^{−1}tr(Y_{𝒢₁}U_{(1)}⋯Y_{𝒢_r}U_{(r)}), the sum over the families 𝔉 of step-(k+1) groups of (6)(d), with f_{k+1} for 𝔉 = ∅.
  {#MD2.3.0.1-1} The insertions are Y_𝒢(𝐔, ω′) at 𝐔 = U_{k+1}, covariant by (6)(b), with flat scalars Ψ° by (6)(c).
- {#MD2.3.0.2} *Output.* The form of D(k+1):
  - {#MD2.3.0.3} (i) κ^{(k+1)} = κ^{(k)}κ_{k+1}, κ_{k+1} = e^{−δm_{k+1}P_k(C)}z_{k+1}⁴, with δm_{k+1} and z_{k+1} independent of the contour size, the torus and ℓ;
  - {#MD2.3.0.4} (v) the scalar parts are numbers given ℓ;
  - {#MD2.3.0.5} the insertions that remain vanish at the flat reference, or are attached to ℓ's data (D2.6).
- {#MD2.3.0.6} *Constraint (D2.0(5)(a), (b)).* No remainder proportional to P_k(C) may be left.
  {#MD2.3.0.6-1} The corner remainders must be summable over k uniformly in K.

### (1) Quoted {#MSD2.3.1}

- {#MD2.3.1.1} *Step 1 (V4).*
  - {#MD2.3.1.2} *Reference data,* L1130: the same regions, cubes and cutoffs, with U°₁ = id, V°₀ = id, A°_e = 0; "These data need not be a branch of the history sum." The lemmas used "apply to U = id directly".
  - {#MD2.3.1.3} *Schur,* Lemma schur, L1055–1064.
    {#MD2.3.1.3-1} At the identity background a constant gauge transformation fixes the data.
    {#MD2.3.1.3-2} So the group matrix Υ = w°(W)∫π(P°_W(a))d(⊗ν̂°)(a) satisfies Υ = π(u)Υπ(u)^{−1} for all u ∈ G, hence Υ = a_W·𝟙, and S°_{ξ,C} = Σ_{𝔅 compatible}∏_{W∈𝔅}a_W (eq:part1-reference-gas).
  - {#MD2.3.1.4} *Joint extraction,* Prop. joint-extraction, L1070–1075.
    {#MD2.3.1.4-1} With the joint defect R_ξ(𝔅) := Σ_{𝒮⊆𝔅}(−1)^{|𝔅∖𝒮|}(∏_{W∈𝔅∖𝒮}a_W)A_ξ(𝒮), F_ξ(0) = S°_{ξ,C}f_ξ(0) + Σ_{𝔅≠∅}S°^{[𝔅]}_{ξ,C}R_ξ(𝔅).
    {#MD2.3.1.4-2} At the reference data every nonempty defect vanishes: by Lemma schur A°(𝒮) = ∏_{W∈𝒮}a_W, so R°(𝔅) = ∏_{W∈𝔅}a_W·Σ_{𝒮⊆𝔅}(−1)^{|𝔅∖𝒮|} = 0 for 𝔅 ≠ ∅.
  - {#MD2.3.1.5} *Perimeter,* eq:marginal-full-perimeter (L1595): κ_v = Σ_{Γ: 0∈J_Γ}Φ_v(Γ)/|J_Γ| on the infinite straight line, δm_v = −κ_v/(Lε), with |κ_v| ≤ Cτ² from the rooted tail eq:marginal-cluster-tail (L1574). κ_v is kept per orientation v; D2 uses only the average δm^σ = −(4Lε)^{−1}Σ_{v∈𝒱_□}κ_v (eq:marginal-square-mass, L1649; so D2.0(3)'s δm_1 = εδm^σ = −(4L)^{−1}Σ_{v∈𝒱_□}κ_v per step-0 bond) over C's sides (D2.3(5) *Independence*;
    {#MD2.3.1.5-1} D2 does not use invariance of V4's Borel axial choice and chart choices under permutations of the axes; it uses translations only, RTR_PROOF_PASS, *Hypercubic covariance*). eq:marginal-line-endpoints (L1612) is the exact endpoint identity for a finite segment.
  - {#MD2.3.1.6} *Corners,* eq:corner-local-extraction (L1702): ζ_{v,w} = Σ_{j∈ℤ}(a_{v,w}(j) − k_{v,w}(j)) on the infinite bent path, with |a_{v,w}(j) − k_{v,w}(j)| ≤ Cτ²e^{−c|j|} (eq:corner-localisation-bound, L1710). eq:corner-mixed-cluster-formula (L1720) shows that ζ contains the straight-edge endpoint deficits.
  - {#MD2.3.1.7} *Square,* eq:corner-square-extraction-bound (L1763): |F_{□,∞}(n) − nΣ_vκ_v − Σ_{(v,w)∈𝒞_□}ζ_{v,w}| ≤ Cτ²(n+1)e^{−cn}, with z_c := exp(¼Σζ_{v,w}) (eq:corner-square-factor, L1772).
  - {#MD2.3.1.8} *Iteration,* Conjecture iteration, L3532, and Remark next-step (3)(e).
    {#MD2.3.1.8-1} There the torus and corner part E°_{T,n} "at most Cτ²(2+1/c)" is "one source of the term (k+2)τ²".
    {#MD2.3.1.8-2} Cτ²(2+1/c) bounds the torus part, by 4ne^{−cι_T} ≤ 1 from (H3), and the corner part, by (n+1)e^{−cn} ≤ 1+1/c (V4 Remark main-regime (1), by Corollary c5-7-2(c)); the decay in n is not used.
- {#MD2.3.1.9} *The partitions (Bałaban).*
  - {#MD2.3.1.10} RG2 p.3: "a regular partition σ_k of the space T, in the scale corresponding to the lattice T_η, into cubes Δ of the size R₁M₁.
    {#MD2.3.1.10-1} The number R₁ is a power of L".
  - {#MD2.3.1.11} RG2 p.13: "π_{k+1}, i.e. cubes of the size LM in the scale corresponding to the lattice T_η".
  - {#MD2.3.1.12} CRE p.245: "a partition into cubes of the size MR₀, where R₀ is the smallest power of L such that R₀ ≥ (log g₀^{−2})^r, r ≥ 2, and M = L^m is sufficiently large.
    {#MD2.3.1.12-1} The second is a partition into cubes of the size LM₂R₀, where M₂ = L^{m₂}".
  - {#MD2.3.1.13} PBG p.408: "We take these numbers as powers of L" (R, M).
  - {#MD2.3.1.14} CRE p.256: the domains Ω_j, Λ_j "which are determined by he j-th renormalization transformation, but not by the 𝐑-operation, are unions of MR_j-cubes in the lattice T_{L^{−j}}" (print "he" for "the").
    {#MD2.3.1.14-1} At step k+1 the small-field tests of CRE (3.16) are on L²M₂R_{k+1}-cubes (D2.2(1)).
  - {#MD2.3.1.15} *Translation covariance (RTR).* Every operation of Bałaban's step (averages, minimisers, propagators, cutoffs, s-localisation, activities) is defined from the lattice, the partitions and the fields alone, so a lattice translation that preserves all the partitions maps each object to the object of the translated data.
    {#MD2.3.1.15-1} The prints define the operations this way; no page states the covariance of the localised 𝐄-activities (CRE (2.29), p.260, is for the unrestricted sums 𝐄^{(j)}(U_j, z)). For the 𝐑-terms CRE (2.32), p.260 l.35–41, holds "for these Euclidean transformations r, which leave the partition of the lattice T_ξ in MR_j-cubes invariant", reflections included, and (2.33) for the totals; LFR II p.390 l.27 gives 𝐑′^{(k)}(X) the property (2.32).
    {#MD2.3.1.15-2} On ℓ₀ it is proved in RTR_PROOF_PASS_2026_10_23.md (printed covariance RG1 p.263/p.269, CRE (2.29), (3.39); the localised activities from the definitions); the free choices by our convention, with the PBG p.411 tie averaged with equal weights over the tied cubes (only translations are used below; the average keeps the free choices hypercubic symmetric, but the step itself is not shown hypercubic covariant, #MOMGD.23).
  - {#MD2.3.1.16} Nesting: each cube of a coarser partition is a union of cubes of each finer one, the L-blocks included (CRE p.245 l.38–40; V4 Section fixed-first-kernel; as used in D2.2(6)(a)).
  - {#MD2.3.1.17} CRE (2.9), p.256, for n > m: R_n ≤ LR_m and R_m ≤ L(1+g_n²β′(n−m))^{β₀}R_n ≤ (L+1)(n−m)^{β₀}R_n.

### (2) The Flat Value of a Group Is a Scalar {#MSD2.3.2}

- {#MD2.3.2.1} *The reference point.* On a labelled term ℓ it is (𝐔, 𝐉, ω′) = (1, 0, 0) with ℓ's regions, as in (6)(c) ("𝐔 = 1, 𝐉 = 0, ω′ = 0") and V4 Section joint-extraction.
  {#MD2.3.2.1-1} Below, (1, 0) abbreviates it.
  {#MD2.3.2.1-2} Write ℓ₀ for the trivial-label term: Ω_j = Λ_j = T for every j ≤ k+1, no large-field regions, hence no outer variables.
  {#MD2.3.2.1-3} On ℓ₀ the reference point is a real configuration in the support of every indicator, so D2.2's identities hold there.
  {#MD2.3.2.1-4} On other terms it need not lie in the support, and the insertions are taken there through the reference clause.
- {#MD2.3.2.2} *Reference clause (a clause of D(k)(iii)).* The background-dependent factors of D(k) on ℓ are defined and analytic also at 𝐔 = e^{iη_kA′}·1, A′ in D(k)(iii)'s domain, jointly with ω in its radii around ω = 0.
  - {#MD2.3.2.3} At k = 1 this is the reference-data paragraph of V4 Section joint-extraction: the step-1 lemmas "apply to U = id directly", on every branch.
  - {#MD2.3.2.4} At step k+1 it is (6)(e)'s analyticity argument with U_{k+1} = 1:
    - {#MD2.3.2.5} (4)(f) at U_{k+1} = 1 uses the clause at step k;
    - {#MD2.3.2.6} the transports and the leading word are entire;
    - {#MD2.3.2.7} the Gaussian parts and 𝐕_k(Y) are analytic on Bałaban's domain, given by the conditions I.(i)–(iii) (RG2 pp.6, 15; "I" is RG1).
      {#MD2.3.2.7-1} RG1 p.262 states them: (i) 𝐔 = U′U with |∂U − 1| < α₀ξ² (1.11) and, on cubes of size O(1)LM, a gauge with U^u = exp iξA, |A|, |∇^ξA| < O(1)LMBα₀ (1.12); (ii) U′ = exp iξA′, |A′|, |∇_U^ξA′| < α₁ (1.13); (iii) |∂𝐔 − 1| < α₀ξ², |𝐉| < γ₀ (1.14).
      {#MD2.3.2.7-2} At (𝐔, 𝐉) = (1, 0) take U = U′ = 1, u = 1, A = A′ = 0: every inequality holds strictly, and it holds for e^{iη_kA′}·1 with A′ in D(k)(iii)'s domain, whose bounds are those of (1.13) with smaller constants; (1.14)'s plaquette condition |∂𝐔 − 1| < α₀ξ² at 𝐔 = e^{iη_kA′}·1 is covered by RG2 p.15 l.5, analyticity on I.(i)–(iii) "with constants α₀′, α₁′ much bigger than α₀, α₁";
    - {#MD2.3.2.8} the large-field objects in the insertions on ℓ ≠ ℓ₀ are defined at the flat point: they are CRE (2.12)'s minimisers with determining set 𝔅 (CRE p.256, "A regular configuration V on 𝔅 determines the minimal orbit"; RG1 p.260's "exactly one regular, critical orbit … and it is a minimal orbit" is the small-field statement).
      {#MD2.3.2.8-1} At V = 1 the configuration 1 is a minimum (the action is ≥ 0 and vanishes there) and satisfies the constraint, so the orbit is that of 1.
      {#MD2.3.2.8-2} Hence the minimisers V^{(k)}_{Λᶜ∩Λ_k} are 1 in the axial gauge, 𝐇^{(k)} = 0, and the slot values ψ_{k+1}(A_j^{new}; 𝐇^{(j)}) are taken at 𝐇^{(j)} = 0 and ω′ = 0.
      {#MD2.3.2.8-3} That these are defined there is the statement; their sizes are D2.4's;
    - {#MD2.3.2.9} the characteristic functions do not depend on a′.
  - {#MD2.3.2.10} The bounds at the reference point are part of D2.4's sizes at complex data.
- {#MD2.3.2.11} *Schur.* Let 𝒢 be a step-(k+1) group with arc I(𝒢) from x to x′.
  {#MD2.3.2.11-1} Take u ≡ g constant in Cov(k+1) ((6)(b), (d)).
  {#MD2.3.2.11-2} Then 1^g = 1 and R(g)0 = 0, and the labels are gauge invariant.
  {#MD2.3.2.11-3} So Y_𝒢(1, 0) = π(g)Y_𝒢(1, 0)π(g)^{−1} for all g ∈ G.
  - {#MD2.3.2.12} π is irreducible (V4 (H1): χ = dim(π)^{−1}tr π).
    {#MD2.3.2.12-1} By Schur's lemma, Y_𝒢(1, 0) = c_𝒢𝟙 with c_𝒢 = c_𝒢(ℓ) ∈ ℂ, a number given ℓ.
  - {#MD2.3.2.13} This is V4's Lemma schur at step k+1.
    {#MD2.3.2.13-1} V4 applies Schur to the integrated reference group matrix; here the integral is already inside Y_𝒢 ((5)(c)).
  - {#MD2.3.2.14} Old groups that stand alone in 𝔉 (the untouched old insertions of (5)(a)) are covered by Cov(k) in the same way.
    {#MD2.3.2.14-1} For a whole-contour group, x = x′ is the base point and the argument is the same.
- {#MD2.3.2.15} *The split.* Let T_𝐔(I) := π of the ordered product of the 𝐔-transports along the arc I, in the orientation of C. Put
  {#MD2.3.2.16} Y^d_𝒢(𝐔, ω′) := Y_𝒢(𝐔, ω′) − c_𝒢T_𝐔(I(𝒢)).
  - {#MD2.3.2.17} T_𝐔(I(𝒢)) transforms as T ↦ π(u(x))·T·π(u(x′))^{−1}, so Y^d_𝒢 is covariant with the endpoints of Y_𝒢.
    {#MD2.3.2.17-1} T_𝐔 is entire, so Y^d_𝒢 is analytic on Y_𝒢's domain.
    {#MD2.3.2.17-2} T_1 = 𝟙, so Y^d_𝒢(1, 0) = 0.
  - {#MD2.3.2.18} The split is made in the formulas, as D2.0(3)'s *Species* requires, not by the sizes.
  - {#MD2.3.2.19} The flat parts of D2.0(5)(d) (the scalar parts of pair contractions of old insertions at flat U_{k+1}) are in c_𝒢.
    {#MD2.3.2.19-1} Their background-dependent remainder, of deviation size, is in Y^d_𝒢.
    {#MD2.3.2.19-2} This is the division that D2.0(5)(a) asks for.

### (3) The Exact Factorisation {#MSD2.3.3}

- {#MD2.3.3.1} *The interactions.* Both interactions are kept in cluster form and expanded into the groups, as V4 does with its vacuum clusters at step 1 (eq:c-cluster-expansion, eq:part1-group-weight, L1101–L1108).
  - {#MD2.3.3.2} *Old part.* By D(k)'s interaction clause in cluster form (note in D2.0(3)), Q_k(𝔅) = exp(−Σ_{Γ hits 𝔅}φ_k(Γ)), over the clusters Γ of the step-k reference group gas that are incompatible with some member of 𝔅.
    {#MD2.3.3.2-1} The φ_k(Γ) are numbers given ℓ, and they depend on C only through J_Γ, the traversals in the arcs of Γ's groups.
    {#MD2.3.3.2-2} At k = 1 this is IT-1 note §4's Q(𝔅) = exp(−Σ_{Γ hits 𝔅}φ(Γ)).
    {#MD2.3.3.2-3} At step k+1 it is the last bullet of this (3).
  - {#MD2.3.3.3} *Vacuum part.* Q° = Q_{k+1}(𝔐) of D2.2(5)(d) at the reference point, exp(Σ_𝒞(s_𝔐(𝒞) − 1)_+φ^T(𝒞)), over the vacuum clusters 𝒞 that are incompatible with at least two marked polymers.
    {#MD2.3.3.3-1} It does not involve C.
  - {#MD2.3.3.4} *Expansion in occurrences.* Expand the old part as the exponential series Σ_{m≥0}((−1)^m/m!)Σ_{Γ₁,…,Γ_m each hits 𝔅}∏_jφ_k(Γ_j), and the vacuum part as ∏_𝒞(1 + (e^{(s_𝔐(𝒞)−1)φ^T(𝒞)} − 1)), over the 𝒞 with s_𝔐(𝒞) ≥ 2.
    {#MD2.3.3.4-1} Both converge absolutely: Σ_{Γ hits W}|φ_k(Γ)| ≤ θ(W) by D(k)'s norms, Σ_{𝒞≁M}|φ^T(𝒞)| ≤ 9c#M by D2.4(2)(g), and |e^x − 1| ≤ |x|e^{|x|}.
    {#MD2.3.3.4-2} On the finite torus these are infinite sums, since clusters may repeat polymers, so the rearrangements below need this absolute convergence.
  - {#MD2.3.3.5} *Third merging rule (amends D2.2(6)(d)).* In each term, the old groups hit by one old occurrence, and the marked polymers hit by one vacuum occurrence with factor e^{(s−1)φ^T} − 1, join one group.
    {#MD2.3.3.5-1} The arc hull is taken over the arcs of the members and over J_Γ for every old occurrence Γ; vacuum occurrences add no arc.
    {#MD2.3.3.5-2} Then D2.2(6)(d)'s first two rules are repeated to a fixed point.
    {#MD2.3.3.5-3} Each occurrence lies in exactly one group 𝒢.
    {#MD2.3.3.5-4} Its factor goes into Y_𝒢 as a number, with (−1)^{m_𝒢}/m_𝒢! for the m_𝒢 old occurrences of 𝒢: the m! of the series splits into the m!/∏_𝒢m_𝒢! interleavings, as in eq:part1-group-weight.
  - {#MD2.3.3.6} *Hard core.* Two groups are compatible when their arcs are disjoint, their constituent domains are compatible, and no occurrence of one hits a member of the other.
    {#MD2.3.3.6-1} The terms of the expansion are then in bijection with the families of pairwise compatible groups with their occurrences.
    {#MD2.3.3.6-2} So the step-(k+1) reference group gas is a pure hard-core gas: Q(𝔉) = 1, and every interaction is inside a group.
- {#MD2.3.3.7} *Multilinear expansion.* Put Y_𝒢 = c_𝒢T_𝐔(I(𝒢)) + Y^d_𝒢 into each word and expand:
  {#MD2.3.3.8} dim(π)^{−1}tr(Y_{𝒢₁}U_{(1)}⋯Y_{𝒢_r}U_{(r)}) = Σ_{D⊆𝔉}(∏_{𝒢∈𝔉∖D}c_𝒢)·w^d(D).
  - {#MD2.3.3.9} w^d(D) is dim(π)^{−1}tr of the word with Y^d_𝒢 on the arcs of D and the 𝐔-transports elsewhere, and w^d(∅) = f_{k+1}.
    {#MD2.3.3.9-1} The transports of the scalar terms join the neighbouring U_{(i)}, so w^d(D) is the class word of the family D.
  - {#MD2.3.3.10} This is V4's joint defect (Proposition joint-extraction).
    {#MD2.3.3.10-1} Boolean inversion of A(𝔉) = Σ_{D⊆𝔉}(∏_{𝔉∖D}c_𝒢)R(D) has the unique solution R(D) = w^d(D).
    {#MD2.3.3.10-2} So at step k+1 the joint defect is the word of the deviation parts.
    {#MD2.3.3.10-3} As in V4, it vanishes at the reference point for D ≠ ∅.
- {#MD2.3.3.11} *Resummation.* Σ_𝔉Q(𝔉)Σ_{D⊆𝔉}(∏_{𝔉∖D}c_𝒢)w^d(D) = Σ_Dw^d(D)·S°^{[D]}(ℓ), where
  {#MD2.3.3.12} S°^{[D]}(ℓ) := Σ_𝔈 Q(D ∪ 𝔈)∏_{𝒢∈𝔈}c_𝒢 = Σ_𝔈∏_{𝒢∈𝔈}c_𝒢,
  {#MD2.3.3.13} the sum over the families 𝔈 disjoint from D for which D ∪ 𝔈 is a family (pairwise compatible groups), with Q = 1 by the hard core above.
  {#MD2.3.3.13-1} Put S°(ℓ) := S°^{[∅]}(ℓ).
  - {#MD2.3.3.14} The interchange needs Σ_𝔉∏_{𝒢∈𝔉}(|c_𝒢| + ‖Y^d_𝒢‖) < ∞ at the evaluation point, times the transport norms on the gaps of C (at complex 𝐔 at most e^{O(α)P_k(C)} in all, a finite factor on the finite torus), over the families with their occurrences.
    {#MD2.3.3.14-1} Without the occurrences the family sum is finite on the finite torus; with them it is an infinite sum, and the absolute convergence is D2.4's, as V4's proof of Prop. joint-extraction does with its β_W.
- {#MD2.3.3.15} *Result (exact).* Where S°(ℓ) ≠ 0,
  {#MD2.3.3.16} ⟨𝒲_k⟩_{1,1} = κ^{(k)}e^{𝓔_k}S°(ℓ)·[f_{k+1} + Σ_{D≠∅}Q^{out}_{k+1}(D)·w^d(D)], Q^{out}_{k+1}(D) := S°^{[D]}(ℓ)/S°(ℓ).
  - {#MD2.3.3.17} The name Q^{out} keeps it apart from D2.2(5)(d)'s vacuum interaction Q_{k+1}(𝔐).
    {#MD2.3.3.17-1} Q^{out}_{k+1} is D(k+1)'s Q_{k+1} in D2.0(3)'s display.
  - {#MD2.3.3.18} Q^{out}_{k+1}(D) is a number given ℓ, so D(k+1)(v) holds for it.
  - {#MD2.3.3.19} The insertions at step k+1 are the Y^d_𝒢.
    {#MD2.3.3.19-1} They vanish at the reference point.
- {#MD2.3.3.20} *S°(ℓ₀) is the flat reference integral.* At (1, 0) every Y^d_𝒢 vanishes and f_{k+1} = 1, so the bracket is 1 and ⟨𝒲_k⟩_{1,1}(1, 0) = κ^{(k)}e^{𝓔_k}S°(ℓ).
  {#MD2.3.3.20-1} On ℓ₀ the reference point is a configuration of the term.
  {#MD2.3.3.20-2} So
  {#MD2.3.3.21} 𝒲°_{k+1}(C; T) := S°(ℓ₀) = ⟨f_k + Σ_{𝔅≠∅}Q_k(𝔅)word_k(𝔅)⟩_{1,1} at U_{k+1} = 1,
  {#MD2.3.3.22} the expectation of D(k)'s bracket under the flat step-(k+1) fluctuation measure of CRE (3.25), with its small-field cutoffs.
  {#MD2.3.3.22-1} It is the step-(k+1) analogue of V4's 𝒲°_T(C) = N^σ_{C,T}/D^σ_T (eq:marginal-literal-ratio), the bare loop W_χ(C; ·) under the flat first-step measure.
- {#MD2.3.3.23} *The gas and its logarithm.* S°(ℓ) is the partition function of the *reference group gas*: polymers 𝒢 (with their occurrences) with activities c_𝒢 and the hard core of the *Hard core* bullet.
  {#MD2.3.3.23-1} There are no other interactions.
  - {#MD2.3.3.24} Under D2.4's Kotecký–Preiss condition its cluster series converges.
    {#MD2.3.3.24-1} Then S°(ℓ) = exp(Σ_ΓΦ°(Γ; ℓ)) ≠ 0, the sum over the clusters Γ of groups, Φ°(Γ) the Ursell function times ∏c_𝒢 (FV (5.11)). log S° denotes this series.
  - {#MD2.3.3.25} Every group has an arc on C (its slots, or the old group's arc), and the vacuum clusters were divided out in (5)(d).
    {#MD2.3.3.25-1} So every cluster Γ has a nonempty set J_Γ of traversals of C in the arcs of its groups.
- {#MD2.3.3.26} *The interactions at step k+1 have the cluster form.* S°^{[D]} is the partition function of the gas with the activities c_𝒢·1[𝒢 compatible with every member of D], so the Kotecký–Preiss condition passes to it (as in D2.2(5)(d)), and its cluster series is that of S° without the clusters incompatible with D. Hence
  {#MD2.3.3.27} Q^{out}_{k+1}(D) = exp(−Σ_{Γ hits D}Φ°(Γ; ℓ)),
  {#MD2.3.3.28} the sum over the clusters incompatible with some member of D. This is D(k+1)'s interaction clause in the cluster form of (3)'s *Old part*, with φ_{k+1} := Φ°, and the old occurrences of the next step are these clusters.
  {#MD2.3.3.28-1} The bound Σ_{Γ hits 𝒢}|Φ°(Γ)| ≤ θ_{k+1}(𝒢) is FV Lemma 5.6, (5.17) (p.226), under D2.4's condition (D2.4(3), θ_ref).

### (4) Periodicity, Contour Locality, and the Infinite Lattice {#MSD2.3.4}

- {#MD2.3.4.1} *The period.* Let Π_{k+1} be the largest cube side, in step-k bonds, of the partitions and cube families used at the steps 1, …, k+1: those of (1), the MR_j-cubes of which the step-j domains are unions (CRE p.256), and the L²M₂R_j-cubes of the tests (3.16).
  - {#MD2.3.4.2} The largest side is a power of L: every candidate is a power of L: the others by (1), and RG2's R₁M₁ since R₁ is one (CRE (2.5), p.255) and M₁ is one by V4 eq:c-standing-conditions (M₁, M₂, M powers of the odd L; also V4 sec:fixed-first-kernel), a choice of the project, as no transcribed text of Bałaban says M₁ is a power of L; R₁M₁ ≤ M. So every side divides the largest, and every one is invariant under the translations by Π_{k+1} step-k bonds along each axis.
    {#MD2.3.4.2-1} The torus periods are multiples of Π_{k+1}, since the partitions are regular partitions of T.
  - {#MD2.3.4.3} *Size.* At step j+1 the cubes are, in step-j units: R₁M₁ ≤ M (RG2 p.3); LM ≤ MR_j and LM₂R_j ≤ MR_j (M₂ < M, both powers of L, and R_j ≥ L for small g); the step-(j+1) domain cubes MR_{j+1} of scale j+1, which are LMR_{j+1} ≤ L²MR_j step-j bonds (R_{j+1} ≤ LR_j, CRE (2.9)); and L²M₂R_{j+1} ≤ LMR_{j+1} ≤ L²MR_j.
    {#MD2.3.4.3-1} In step-k units the largest is at most L^{j−k}L²MR_j.
    {#MD2.3.4.3-2} By CRE (2.9) with n = k, m = j, this is ≤ (L+1)(k−j)^{β₀}L^{j−k}L²MR_k ≤ L²MR_k for k > j, since (L+1)m^{β₀}L^{−m} ≤ 1 + 1/L for m ≥ 1, β₀ ≤ 1, and the side is a power of L; for j = k it is L²MR_k.
    {#MD2.3.4.3-3} So Π_{k+1} ≤ L²MR_k.
- {#MD2.3.4.4} *Invariance on ℓ₀ (from translation covariance (RTR) on ℓ₀, RTR_PROOF_PASS_2026_10_23.md, with our convention for the choices the prints leave free).* On ℓ₀ every object of the steps 1, …, k+1 is defined from the lattice, the partitions, the flat field and, for the insertions, their groups and occurrences, the arcs of C. A translation τ by a multiple of Π_{k+1} step-k bonds preserves the first three, and by translation covariance (RTR) ((1)) each object is carried to the object of the translated data.
  {#MD2.3.4.4-1} So c_{τ𝒢} = c_𝒢 and Φ°(τΓ) = Φ°(Γ) whenever τ maps the arcs of 𝒢 (of the groups of Γ) onto arcs of C of the same shape, by the next bullet.
- {#MD2.3.4.5} *Contour locality (from D2.1(4), D2.2(4)(e), (5)(c) and (3)).* For a group 𝒢 with a short arc (fewer than P_k(C)/2 step-k traversals), Y_𝒢 depends on C only through the bonds of C in I(𝒢).
  - {#MD2.3.4.6} Y_𝒢 is the contraction along I(𝒢) of the Ĥ(G), whose slots lie in I(𝒢), with the old insertions in I(𝒢) and the transports along I(𝒢) ((6)(d)), times the factors of its occurrences ((3)).
    {#MD2.3.4.6-1} The vacuum activities, the vacuum occurrences and Ψ° do not involve C. An old occurrence Γ has weight φ_k(Γ), which depends on C only through J_Γ ⊆ I(𝒢) (the third merging rule).
    {#MD2.3.4.6-2} The old insertions and the old cluster weights satisfy the same statement, by induction from step 1: there V4's group words are products along their intervals, the contour enters through the contact sets (eq:part1-contact-set), and V4's cluster weights φ(Γ) are Ursell functions times activities of groups with arcs in J_Γ.
    {#MD2.3.4.6-3} The hard core between groups depends on C only through their arcs.
  - {#MD2.3.4.8} The hull rule depends on the length of C, so whole-contour groups are excluded.
    {#MD2.3.4.8-1} They have spatial extent at least P_k(C)/2 step-k traversals in contour distance and are paid by the tail bound (T′) of (5) (from (S-w)): a whole-contour group has a network of diameter ≥ P_k(C)/4 in step-k bonds (its arc of ≥ P_k(C)/2 = 2s_k traversals along the square contains a whole side, whose endpoints are s_k = P_k(C)/4 apart, and the arc I(𝒢) lies in the support X(𝒢)), so the clusters containing one are ≤ C_S′𝔞_{k+1}e^{−c_dP_k(C)/4} per traversal.
- {#MD2.3.4.9} *Placement of C.* C is placed with a corner at the origin, taken at the centre of a cube of the coarsest partition.
  {#MD2.3.4.9-1} The partitions are grids with a common corner and sides powers of L (RG1 p.251, p.257, RG2 p.3), and L is odd, so this point is a site of every T^{(k)}, k ≤ K, and the centre of a cube of every partition; the period points (the origin plus multiples of Π_{k+1}) are cube centres of the partitions whose side divides Π_{k+1}, and every lattice and partition is invariant under the hypercubic group about the origin (the step's objects are not shown to be, D2.3(5) *Independence*).
  {#MD2.3.4.9-2} The bare expectation is translation invariant, so this is no restriction.
  {#MD2.3.4.9-3} C is a union of step-K bonds, with side s_k := ℓ_CL^{K−k} in step-k bonds.
  - {#MD2.3.4.10} Call step k+1 *commensurate* for C if Π_{k+1} divides s_k.
    {#MD2.3.4.10-1} Then the four corners lie on the period lattice and each side is a union of n_k := s_k/Π_{k+1} period cells.
  - {#MD2.3.4.11} Since Π_{k+1} is a power of L and s_k is ℓ_C times a power of L, step k+1 is commensurate whenever Π_{k+1} ≤ L^{K−k}.
    {#MD2.3.4.11-1} By Π_{k+1} ≤ L²MR_k and CRE (2.9) with n = K−1, m = k, R_k ≤ (L+1)(K−1−k)^{β₀}R_{K−1}.
    {#MD2.3.4.11-2} So a step that is not commensurate has L^{K−k} < L²(L+1)M(K−k)^{β₀}R_{K−1}, that is K − k ≤ a*, with a* depending on L, M, β₀ and R_{K−1} only.
    {#MD2.3.4.11-3} R_{K−1} is fixed by g_{K−1}, which CRE (2.6) compares with g_K.
    {#MD2.3.4.11-4} So at most a* steps are not commensurate, and a* does not grow with K at fixed g_K (void under the admissible sides).
  - {#MD2.3.4.12} *The admissible sides.* Let L^{q*} be the least power of L with L^{q*} ≥ sup_{k<K}Π_{k+1}L^{k−K}, the largest period in step-K units.
    {#MD2.3.4.12-1} By Π_{k+1} ≤ L²MR_k and CRE (2.9), Π_{k+1}L^{k−K} ≤ LMR_{K−1} at k = K−1 and ≤ (L+1)MR_{K−1} for k < K−1, so L^{q*} ≤ L²MR_{K−1}. ℓ_C is restricted to the multiples of L^{q*}.
    {#MD2.3.4.12-2} Then Π_{k+1} divides s_k = ℓ_CL^{K−k} at every step (Π_{k+1} is a power of L dividing L^{q*}L^{K−k}), every step is commensurate, and (6)(b) is void.
    - {#MD2.3.4.13} This is the kind of restriction D2.0(1) already makes (C a union of step-K bonds).
      {#MD2.3.4.13-1} It restricts no square when the scale at which the steps stop may depend on the loop (next bullet).
      {#MD2.3.4.13-2} A square on the L-adic lattices has side pL^{−q} in units of a scale u.
      {#MD2.3.4.13-3} Stopped at uL^{−j}, its side is pL^{j−q} step bonds (ℓ_C = pL^{j−q}, the side), a multiple of L^{q*} once j ≥ q + q*.
      {#MD2.3.4.13-4} Here q* is fixed by the coupling at the stopping scale through CRE (2.5), (2.7); it grows at most like β₀log_L j (next bullet), and j ≥ q + q*(j) has solutions.
      {#MD2.3.4.13-5} With the stopping scale held fixed, it does restrict the sides to multiples of L^{q*}.
      {#MD2.3.4.13-6} That D2's consumers allow a loop-dependent stopping scale is checked in the next bullet.
    - {#MD2.3.4.14} *The stopping scale per loop.* Let u be the unit scale, ε = uL^{−K} the fine spacing (K steps from ε to u), and C a square of physical side pL^{−q}u with integers p ≥ 1, q ≥ 0.
      {#MD2.3.4.14-1} For j ≥ q put K′ := K − j, the *stopping scale* uL^{−j}: the side of C is ℓ_C = pL^{j−q} step-K′ bonds, P_{K′}(C) = 4ℓ_C (ℓ_C is the side throughout D2.3), and C is a union of step-k bonds for every k ≤ K′.
      {#MD2.3.4.14-2} Four checks.
      - {#MD2.3.4.15} (i) *j(C) exists and does not depend on ε, given the coupling prescription.* Along the sequence ε = uL^{−K} → 0 the unit-scale couplings g_K are prescribed with g_min := inf_K g_K > 0 and γ := sup_K g_K small (for instance g_K = ḡ for all K).
        {#MD2.3.4.15-1} A bare-coupling sequence realises this by #MD2.0.5.2: for g small there is g₀(ε, g) with g_K = g whose history lies in the tube H_K (BETA_FUNCTION_WILSON_LOOPS.md Proposition 2.13, at simple G), with g_k ≤ (1+β₀)g_K (#MD2.0.5.2-2).
        {#MD2.3.4.15-2} (0.31) is not used here, and γ below is not RG I's γ, written γ_B.
        {#MD2.3.4.15-3} It is not D2's, and without it j(C) is not K-independent (as g_K → 0, j(C) → ∞: the forcing is the lower bound L^{q*(K′)} ≥ Π_{K′}L^{−1} ≥ LM₂R_{K′}, with R_{K′} ≥ (log g_{K′}^{−2})^r → ∞ since g_{K′} ≤ (1+β₀)g_K).
        {#MD2.3.4.15-4} The admissible-sides bullet at the final step K′ defines q*(K′) with L^{q*(K′)} ≤ L²MR_{K′−1}.
        {#MD2.3.4.15-5} Cauchy #CP.14 gives R_{K′−1} ≤ 2L(log g_{K′−1}^{−2})^r, and CRE (2.7) with n = K, m = K′−1 (n − m = j+1) gives (log g_{K′−1}^{−2})^r ≤ (1+g_K²β′(j+1))^{β₀}(log g_K^{−2})^r ((2.7) is printed for positive integers p (p.256, first line); p₀ is a positive integer (p.244); at p = r it follows from p = ⌈r⌉ by raising to r/⌈r⌉ ≤ 1; (2.6)–(2.7) at general G: CRE (2.6)–(2.7)).
        {#MD2.3.4.15-6} So q*(K′) ≤ q̄(j) := ⌈log_L(2L³M(1+γ²β′(j+1))^{β₀}(log g_min^{−2})^r)⌉, which grows like β₀log_L j, while j − q grows like j.
        {#MD2.3.4.15-7} Hence the least j ≥ q with j ≥ q + q̄(j) exists; call it j(C).
        {#MD2.3.4.15-8} It depends on q, L, M, β₀, β′, r, g_min and γ only: not on ε, K, p or the torus.
        {#MD2.3.4.15-9} For K′ = K − j(C) the side pL^{j(C)−q} is a multiple of L^{q*(K′)}, so every step k+1 ≤ K′ is commensurate and (6)(b) is void.
        {#MD2.3.4.15-10} The construction needs K′ ≥ 1, i.e. K > j(C), true for ε small.
        {#MD2.3.4.15-11} For two loops (V4's two-loop theorem) translation puts only one loop's corner at the origin; the other's corners must be period points too, so take the least j ≥ max(q₁, q₂, q₁₂) + q̄(j), with q₁₂ the least q such that the displacement between the two loops' corners lies in L^{−q}uℤ⁴.
      - {#MD2.3.4.16} (ii) *D2 stopped at K′.* The induction D(1) → ⋯ → D(K′) uses the step map only.
        {#MD2.3.4.16-1} D2 is written for k ≤ N, N the number of LFR I p.177's condition (ii); N = N_k is the tube's depth (Cauchy #CP.13–#CP.14; BP_TL_NSTEP_FRAME #3.2.1.1-1–#3.2.1.1-2), nonincreasing in k, with N_k ≤ log_L(16L⁴(L+1)²) + ν_L log_L log g_k^{−2}. Since g_k^{−2} ≤ g_min^{−2} + (b′ + C_W)(K−k) (#MD2.0.5.2-2), N_k = O(log log K) at fixed k, and the 𝐑-free initial segment {k : k ≤ N_k} has length O(log log K) (WILSON_IT1_D27_CLOSURE_2026_10_26.md item 1);
        {#MD2.3.4.16-2} for K′ > N_{K′}, which holds for all large K, D(K′) and the inputs at step K′−1 are D2.7's, that note's item 15 (#MD2.0.4.12).
        {#MD2.3.4.16-3} The final step enters at these places, each checked with K′ in place of K: D2.0(1) (C a union of step-K′ bonds, by the corner placement and pL^{j(C)−q} ∈ ℤ, which is not a unit-scale condition since C is not a union of step-K bonds unless L^q divides p; torus periods multiples of L^{K′}, implied by the unit-scale torus condition); this bullet's q* (at K′, by (i));
        {#MD2.3.4.16-4} (7)'s τ̄² := sup_{k<K′}τ_k² with g_k ≤ (1+β₀)g_K (#MD2.0.5.2-2), so C_Στ̄² ≤ Cg_K²(log g_K^{−2})^{6p₀} with (1+β₀)² absorbed into C;
        {#MD2.3.4.16-5} (7)'s torus sum with N^{(k)}_min ≍ (T_ph/u)L^{K′−k+j(C)} (N^{(k)}_min, s_k, and P_k are physical lengths in step-k units, the same in the stopped run as in the K-step run); D2.3(4)(Z-d)'s torus condition (TC), reduced there to the coarsest torus through R_K and ι_{T,K}: at K′ it reads ι_{T,K′} ≥ 32C_DL⁴M(L+1)(1+γ²β′j(C))^{β₀}(log g_min^{−2})^r by CRE (2.7), implied by the unit-scale condition since ι_{T,K′} = L^{j(C)}ι_{T,K} and L^{j(C)} ≥ L^{q̄(j(C))} ≥ (1+γ²β′j(C))^{β₀}, and (Z-g)'s lcm then runs over k ≤ K′;
        {#MD2.3.4.16-6} the deviation insertions summed at the stopping scale (D2.0(5)(c), checked with K′ in place of K: its per-step statements are the step map's and do not see K; its K-dependent constants are the coupling sup, g_k ≤ (1+β₀)g_K for k < K′ by CRE (2.6)'s last inequality as before, so the feedback recursion's condition g_K ≤ g(L) is unchanged, and the torus count in (ε)'s wrap term, N^{(j)}_min ≍ (T_ph/u)L^{K′−j+j(C)}, so the sum over j ≤ K′ is at most 2C(sup_jρ̂_j)e^{−c′(T_ph/u)L^{j(C)}/M} and the condition T_ph ≥ CM of (ε) reads (T_ph/u)L^{j(C)} ≥ CM, weaker than at K);
        {#MD2.3.4.16-7} ONE MORE STEP (7)(d), for K′ ≤ N only (its own scope; for K′ > N D2.7's), with CRE p.268 at step K′−1, where ε_{K′} ≤ (1+β₀)(1+g_K²β′j(C))^{β₀}ε_K, which is CRE (2.8)'s second line (p.256, printed; also from (2.4), (2.6), (2.7)), so its bound is O(pL^{j(C)−q}(1+g_K²β′j(C))^{β₀}ε_K/L), with constants independent of K, and its two smallness conditions are conditions on g_K for the given loop.
        {#MD2.3.4.16-8} They hold for small couplings: j(C) is least and q̄ is nondecreasing, so j(C) − q ≤ q̄(j(C)) and ℓ_C = pL^{j(C)−q} ≤ pL⁴M(1+γ²β′(j(C)+1))^{β₀}(log g_min^{−2})^r; with ε_{K′} ≤ (1+β₀)(1+γ²β′j(C))^{β₀}ε_K and ε_K = g_KA₀(log g_K^{−2})^{p₀}, ℓ_Cε_{K′} = O(p·γ(log g_min^{−2})^{r+p₀}(1+γ²β′(j(C)+1))^{2β₀}), and j(C) = O(log log g_min^{−2}) at fixed q, so ℓ_Cε_{K′} → 0 as γ → 0 with γ/g_min bounded (for instance g_K = ḡ → 0).
        {#MD2.3.4.16-9} D2.3(8)'s assembly and κ^{(K′)} (the perimeter coefficients of the steps 1, …, K′ and the corner factors) are the same formulas with K′.
        {#MD2.3.4.16-10} Every bound stated for k ≤ K in terms of g_K ((7)'s amplitude 𝔞̄ = max(τ̄², sup_kρ_k·pl) in its ρ part, (d)'s factor (1+β₀)⁸L²g_K², and the conditions "for every k ≤ K, g_K small" of D2.2 and D2.4) restricts to k ≤ K′ by the same g_k ≤ (1+β₀)g_K and the monotonicity of τ(g), ρ(g) for small g.
        {#MD2.3.4.16-12} D2.5–D2.7 at K′: D2.5 in D2.2(4); D2.6 for K′ ≤ N in the D2.6 closure, whose §7.2–7.3 reruns D2.0(5)(f)'s large-field induction (Bałaban pp.384–389); D2.7 for K′ > N in the D2.7 closure's item 15, with its 15.8 (the links in the gas, and O2 at k > N).
        {#MD2.3.4.16-13} The inputs of the error bounds of (iii) are checked there (*The error bounds' inputs*): none performs an integration of Bałaban's steps beyond K′, so nothing uses the last step to the unit scale.
      - {#MD2.3.4.17} (iii) *The final-scale expectation.* The identity E_ε[W(C)] = κ^{(K′)}⟨𝒲_{K′}⟩_{K′} + errors holds with ⟨·⟩_{K′} the expectation against Bałaban's step-K′ density, since D(K′) is the statement that the fine expectation equals the step-K′ integral of the dressed loop: stopping performs no further integral, and the identity does not use the remaining j(C) steps of Bałaban's construction.
        {#MD2.3.4.17-1} *The error bounds' inputs.* The errors are those of the background closure §3.4 at k = K′: (1) β_{K′}^{(K′)}, bounded by ONE MORE STEP (7)(b) at k = K′ through the iterated-average lemma (7)(a), RG1 (0.4) at the levels ≤ K′, and B₃ε_{K′} of VAR Theorem 1 at the scale K′ (for K′ > N, D2.7's); (2) the insertion word I^f_{K′}, bounded by D(K′)(ii), the output of the induction D(1) → ⋯ → D(K′), which uses the step map at the steps ≤ K′ only;
        {#MD2.3.4.17-2} (3) the labels ℒ_{K′}, bounded in the closure's (iv-e), under its condition (W), through the Cauchy note's §11 at the stopping scale, whose inputs are CRE (2.18)'s density at step K′, CRE Theorem 2's (2.45)–(2.48) at k = K′ (p.263, constants independent of the scale), VAR Theorem 1 for the minimiser on the stopping torus, LFR II (1.79)–(1.80) for the components of Z_{K′} and their histories at the steps ≤ K′, and the attached-species bounds of the D2.6 closure §7.2 (K′ ≤ N) or D2.7 (K′ > N), with the map's (h) at k = K′;
        {#MD2.3.4.17-3} (4) the factor ⟨|e^{𝓔^f_{K′}}|⟩^{good} of the good labels, bounded by (h) at k = K′.
        {#MD2.3.4.17-4} Bałaban's steps beyond K′ enter only as the numbers g_{K′+1}, R_{K′+1} of the coupling sequence (prescribed by (i)), in (1.80)'s first term c₀M^dR_{K′+1}^{d+1}d′_{K′+1}(S(X)), a lower bound on the exponent at step K′ that LFR II proves by induction over the steps ≤ K′ with the geometric map S (pp.384–387), and in the Cauchy note's (T2-i); no integration of a step beyond K′ is used.
        {#MD2.3.4.17-5} The identity holds on every labelled term on which D(K′) holds; for K′ ≤ N, on the large-field terms D(K′) is D2.6's (WILSON_IT1_D26_CLOSURE_2026_10_24.md); for K′ > N, on every labelled term, ℓ₀ included, D(K′) is D2.7's, WILSON_IT1_D27_CLOSURE_2026_10_26.md item 15.8, given D2.7 15.5(ii) and LFR II Theorem 1 (#MD2.0.4.12).
        {#MD2.3.4.17-6} CRE Thm 2's (2.43)–(2.46) hold at k = K′ with the same E₁, R₁ (p.263: "independent of j, k, Ω, {Ω_j}, {Λ_j}, T"), for regular U_{K′}, under Theorem 1's assumptions, with (2.46) for κ₀ ≥ 7 and g small (p.263).
        {#MD2.3.4.17-7} The torus condition is on the periods in step-K′ units.
      - {#MD2.3.4.18} (iv) *The K → ∞ statement.* The continuum limit is ε = uL^{−K} → 0 at fixed u, fixed C and fixed physical torus periods T_ph, with the prescription of (i), so j(C) is fixed and K′ = K − j(C) → ∞.
        {#MD2.3.4.18-1} Four parts.
        {#MD2.3.4.18-2} (a) On ℓ₀ the integration variable is V_{K′} on the lattice of spacing uL^{−j(C)}, independent of ε (ℓ₀ has no outer variables, D2.3(2)).
        {#MD2.3.4.18-3} (b) On ℓ₀ the needed statement is the convergence there of the dressed-loop expectation ⟨𝒲_{K−j(C)}⟩ on ℓ₀ with κ^{(K′)} divided out: along subsequences it converges to a weak limit point of the stopping-scale effective measures tested against the fixed coarse loop (the continuum note WILSON_IT1_CONTINUUM_LIMIT_CLOSURE_2026_10_26.md, items (3.4), (8.2)–(8.3), given D(K′) on every labelled term); along the full sequence it converges by the comparison of two runs of WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md (its #C7.1; the continuum note's (8.4)),
        {#MD2.3.4.18-4} with no uniformity in j(C) required. κ^{(K′)} is a K-dependent number (P_{k−1}(C) = 4ℓ_CL^{K′−k+1} and the couplings depend on ε), not an object on that lattice, divided out exactly (the continuum note's item (6)).
        {#MD2.3.4.18-5} (c) On labelled terms with large-field regions the step-K′ variables include V_j|Γ_j for j < K′ (CRE (2.2), p.255; ONE MORE STEP (7)(c)), on lattices of spacing uL^{j−K} that depend on ε; already at step 1 V4's E_h runs over the exterior fine field V₀.
        {#MD2.3.4.18-6} These terms are D2.6's and the final-scale step's; their total relative weight is 1 − w_{ℓ₀} ≤ δ_LF, bounded uniformly in K by the Cauchy note's (11.3) (its #C11c.5–#C11c.6; the continuum note's item (7)),
        {#MD2.3.4.18-7} and their contribution to the expectation is at most δ_LFB_LF (the continuum note's (4.4)). Their far part is cancelled by the 𝐑-operation given D2.7 (the continuum note's (4.1)–(4.2)).
        {#MD2.3.4.18-8} CRE p.244's first-step per-plaquette bound gives no positive power of ε, against ≍ ε^{−4} fine plaquettes of the fixed torus, so the large-field terms away from C are not small by counting; they are controlled by their relative weight, not by their number.
        {#MD2.3.4.18-9} (d) Relative to κ^{(K′)} the errors are bounded uniformly in K and converge along the subsequences of (b) (the continuum note's items (5), (6), (8)); along the full sequence the renormalised expectation converges as a whole, errors included (the Cauchy note's #C7.1, the continuum note's (8.4)), so the errors need no separate limit.
      - {#MD2.3.4.19} *Result.* Under the coupling prescription of (i), j(C) exists and does not depend on K, and D2 runs to K′ (for K′ ≤ N by (ii), for K′ > N by D2.7, #MD2.3.4.16-2), so the admissible sides restrict no square on the L-adic lattices.
        {#MOMGD.30} *The stopping scale.* K′ = K − j(C), with j(C) the least j ≥ q + q̄(j), q̄(j) := ⌈log_L(2L³M(1+γ²β′(j+1))^{β₀}(log g_min^{−2})^r)⌉, g_min := inf_K g_K > 0, and γ := sup_K g_K (#MD2.3.4.15–#MD2.3.4.15-8); the corners of C are period points of every step k+1 ≤ K′ (#MD2.3.4.15-9), also for two loops (#MD2.3.4.15-11); the final-scale expectation is (iii) and the limit K → ∞ is (iv).
        {#MD2.3.4.19-1} The coupling threshold of (ii) depends on the loop (on p and q).
        {#MD2.3.4.19-2} The statement is per loop: for each square C, all couplings below a threshold g(C).
        {#MD2.3.4.19-3} It is not a statement at one fixed coupling for all loops.
        {#MD2.3.4.19-4} The threshold falls with the side through ONE MORE STEP (7)'s stopping-scale error O(ℓ_Cε_{K′}) (the k = K bound of (7)(e), closure §3.4; (7)(d)'s sum over k < K is O(ℓ_Cε_{K′}/L)), which needs ℓ_Cε_{K′} small, so at a fixed coupling only loops up to some size p are covered.
        {#MD2.3.4.19-5} This dependence on p is present without the restriction of ℓ_C too (stopped at u, the same error appears).
        {#MD2.3.4.19-6} The per-loop stopping adds only a dependence on q through j(C), at most the factor (1+γ²β′(j(C)+1))^{2β₀} with j(C) = O(log log g_min^{−2}) at fixed q.
        {#MD2.3.4.19-9} The coupling prescription of (i) is #MD2.0.5.2.
        {#MD2.3.4.19-10} D2.7 at K′ > N: WILSON_IT1_D27_CLOSURE_2026_10_26.md item 15, given D2.7 15.5(ii) and LFR II Theorem 1 (#MD2.0.4.12).
        {#MD2.3.4.19-11} The continuum limit ((iv)(c)–(d)): WILSON_IT1_CONTINUUM_LIMIT_CLOSURE_2026_10_26.md fixes the stopping lattice K-independently and reduces the limit to the Cauchy property of the whole renormalised expectation W_ren = E_ε[W(C)]/κ^{(K′)} between the K-run and the (K+1)-run on the common stopping lattice;
        {#MD2.3.4.19-12} that property, the relative-weight inequality bounding the large-field terms against the small-field term (its costs (a)–(e) at the note's (4.3)), and the convergence of g_{K−i} are treated in WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md, from the input (LF) under the conditions (T1), (T2), (T-Λ), and (T-c) (its #C7.1), with §11 for the relative weight in place of (Q). κ^{(K′)} is divided out exactly (the continuum note's item (6)).
    - {#MD2.3.4.20} Without the restriction, the steps with Π_{k+1} ∤ s_k leave a remainder of order τ_k²s_k from the two sides off the origin ((6)(b)).
- {#MD2.3.4.21} *(Z) Torus consistency (D2.4 item; added to D(k) as clause (vi), at flat data on ℓ₀).* For a cluster Γ of the reference gas on ℓ₀ whose groups have short arcs on a straight line or on a bent path, the weight Φ°(Γ; T) is defined on every torus T of the sequence (H3) in which Γ embeds.
  {#MD2.3.4.21-1} *Embeds*: the dependence set of Γ (the union of its groups' X̃⁵-neighbourhoods, PBG Thm 3.10, with the π_{k+1}-cubes of RG2 p.13, the supports of its occurrences and its arcs, the dependence sets of the old insertions contracted into its groups, and the L²M₂R_{k+1}-cubes of the cutoffs of CRE (3.16) that enter its activities) has diameter < ι_T/4, in step-(k+1) block units.
  {#MD2.3.4.21-2} R_D is the radius of a neighbourhood of the network that contains the dependence set, in those units (computed in (Z-g): R_D^{(k)} ≤ 6L²MR_k step-k bonds, R_D = R_D^{(k)}/L step-(k+1) units).
  {#MD2.3.4.21-3} Its contributions: X̃⁵-layers of M₁-cubes, O(M/L); π_{k+1}-cubes, M; the old insertions' own margins, O(ML^{j−k−1}) for one made at step j; and the cutoff cubes, L²M₂R_{k+1} in the T_η scale, which contain R_{k+1} ≍ (log g_{k+1}^{−2})^r and so are not O(M) uniformly in the coupling.
  {#MD2.3.4.21-4} The item: these weights have limits Φ°^∞(Γ) as the periods grow, at the rate Σ_{Γ: b∈J_Γ}|Φ°(Γ; T) − Φ°^∞(Γ)| ≤ 3C_Z^{(k+1)}𝔞_{k+1}e^{−c^Zι_{T,k+1}} (#MD2.3.4.50), 𝔞_{k+1} := max(τ_k², ρ_{k+1}·pl) (constants of (Z-f)), the sum over the clusters rooted at a traversal b.
  {#MD2.3.4.21-5} In this sum a cluster that does not embed in T enters with |Φ°(Γ; T)| on T and with |Φ°^∞(Γ)| on ℤ⁴ (Φ°(Γ; T) := 0 for a ℤ⁴-cluster that does not embed in T); (Z-f) proves the bound in this form.
  - {#MD2.3.4.23} At step 1 the base is (Z-h): D(1) is IT-1's D1, built on V4 (#MOMGD.47), and D2's step-1 reference is V4's q°, E° (#MD2.2.6.100); V4's step-1 objects are exactly local, so no comparison bound enters.
    {#MD2.3.4.23-1} V4's flat regional representation, with its periodised free carrier K_T, the image bound eq:bulk-image-error and |F_{C,T} − F_{C,∞}(n)| ≤ Cτ²(4n)e^{−cι_T} (eq:regional-square-periodic-comparison), is not part of D(1) and is not used in (Z).
  - {#MD2.3.4.24} At step k+1 it needs the same for Bałaban's flat activities H(Z), which the s-parameters localise (RG2 p.13: σ₀ is the family of cubes of π_{k+1} "disjoint with the interior of Z̃₀, or with the interior of Z₀′"), and for the step-k objects by (vi) at step k.
  - {#MD2.3.4.25} *PBG p.394's locality (sibling of translation covariance (RTR)).* The walk pieces R_α(X) of PBG (3.107) and RG2 (1.6), and the local operators they are built from (G_□, G′_{□̃²} with the boundary conditions outside □̃⁵, Q_j, D, D*, and the pieces of C^{(k)} and (C^{(k)})^{1/2}, (3.183)–(3.186), PBG p.432, RG2 (2.7) with G̃₃(x)), are defined on an arbitrary torus of (H3) by the same local formulas: on T′ ⊃ T with the partitions and walk-domain families lifted from T, a piece whose dependence set embeds in T is the same function of the configuration on that set on T and on T′.
    {#MD2.3.4.25-1} The single-torus restriction is printed (PBG p.394, Thm 3.10, RG2 p.3, p.14); the cross-torus identity follows (each elementary operator restricted to its domain is a finite matrix with the local entries (3.23)–(3.24), (3.87), (3.90), (3.105); on an isometric non-wrapping copy of the domain it is the same matrix, and compositions and inverses, such as C_□ = (Q′G′_□²Q′*)^{−1}, inherit this); the lifted-partition and walk-domain convention is ours, a choice the prints leave free (RG2 p.13: "can be chosen to a large extent arbitrarily"; PBG p.415: "for an arbitrary partition");
    {#MD2.3.4.25-2} it is part of translation covariance (RTR)'s convention: every free choice (cube partitions, partitions of unity, walk-domain families, the Λ-modification, the PBG p.411 tie average) is made by a translation-covariant geometric rule, so on tori whose periods are multiples of the grid sides T′'s choices are the lifts of T's.
    {#MD2.3.4.25-3} Families defined relative to a polymer (σ₀ around Z̃₀ or Z₀′, RG2 p.13) are not free choices: they are determined by the polymer and the grid, so for an embedding polymer they agree locally, on Z̃, with the lifts of T's.
    {#MD2.3.4.25-4} The CRE (3.16) cutoff cubes, of side L²M₂R_{k+1}, are among the cubes whose sides divide Π_{k+1} (D2.3(1), *Size*: L²M₂R_{j+1} ≤ LMR_{j+1}, all powers of L), and the admissible tori have periods that are multiples of Π_{k+1}; so their partition on T′ is the lift of T's, with no separate lift rule.
    {#MD2.3.4.25-5} The activities and insertions are not part of PBG p.394's locality; their identity is derived from it in (Z-c).
    {#MD2.3.4.25-6} Evidence: PBG p.410 l.10–11 (the pieces of (3.90) are the localized propagators G′_□, which depend on U restricted to Ω₀(□) ⊂ □̃⁵, and the semi-local K(h)); PBG p.411 l.21 and p.415 l.3–5 (the expansions (3.90), (3.98) are built in the same way for any partition); PBG p.415 l.9 ("G′_{□̃₀²} with the boundary conditions outside □̃₀⁵"); and PBG (3.107), p.416 l.7–8 (a walk term "depends on configuration U restricted to X̃₀⁵ ∪ ⋯ ∪ X̃_n⁵").
    {#MD2.3.4.25-8} Non-local objects (the minimiser, whose restriction is local only up to e^{−cR}, (LPG′)) are not covered.
    {#MD2.3.4.25-9} Units: ι_T, |x − y| below are in step-(k+1) block units (RG2's unit lattice at step k+1).
    {#MD2.3.4.25-10} RG2 measures (1.7)'s δ₀ per unit of the T_η scale, in which π_{k+1}-cubes have side LM; a step-(k+1) block unit is at least one T_η unit, so using δ₀ per step-(k+1) unit gives a weaker decay and is safe.
    {#MD2.3.4.25-11} The cubes of (3.16) are the L²M₂R_{k+1}-cubes of D2.3(1).
    {#MD2.3.4.25-13} Two tori of (H3) need not be nested (each torus' periods multiples of the other's); for two tori that are not nested the comparison goes through their least-common-multiple torus, which must itself be admissible: its periods are multiples of Π_{k+1} (they are multiples of both tori's periods), and (S-w) must hold on it, which is part of its torus-uniform statement (settled in (Z-g); the tail (T′) follows from (S-w) on each torus).
  - {#MD2.3.4.31} *(Z-c) The activities are exactly local (from PBG p.394's locality).* For a polymer Z (or marked polymer M, or group 𝒢) whose X̃⁵-neighbourhood (PBG Thm 3.10's dependence set) embeds in T, H(Z) (RG2 (2.11)), H̃(M), Ψ(M), Ĥ(M) (D2.2(5)(c)–(d)) and the new c_𝒢 (D2.3(2)) are functions of: the s-localised propagators (RG2 (2.8)–(2.10)),
    {#MD2.3.4.31-1} taken at s with s(Y₀ᶜ) = 0 and |s(Δ)| ≤ e^{κ₁} on Y₀∖□̃⁴ (RG2 pp.4–5: (1.10) and its Cauchy estimates use only such s), at which the surviving walks lie in Y₀ and "this term depends on 𝐔, 𝐉 restricted to Y₀ ∪ □₀"; the cutoffs, Mayer factors and Gaussian integrals over its variables; the insertions Y_G, functions of H(s), G̃(s), H₀(s) restricted to their components and of B′ (RG2 p.4–5: "all propagators and the function B are restricted to Y₀"); and the carried old insertions and old cluster weights ((Z-e)).
    {#MD2.3.4.31-2} The dependence statements above are RG2 Sect. 1's (Y₀, □̃⁴, cubes of size M).
    {#MD2.3.4.31-3} For the Gaussian integrals of RG2 Sect. 2 the supplied evidence is p.13 ("We localize it again by the method used in Sect. 1, introducing the parameters s and differentiating", with π_{k+1}-cubes and σ₀ relative to Z̃₀, Z₀′) and p.14 after (2.9): "The function H(Z) is localized in the interior of Z with respect to the external gauge fields".
    {#MD2.3.4.31-4} By PBG p.394's locality the walk pieces and local operators entering them are the same functions on T and on T′ (with lifted partitions and walk-domain families), and the cutoffs, Mayer factors and Gaussian integrals are composed from them by the same formulas.
    {#MD2.3.4.31-5} Hence, for the lift Z̃ of Z to T′ and backgrounds (𝐔, 𝐉) on T, (𝐔′, 𝐉′) on T′ that coincide under the covering on Z's dependence set (𝐉 included: p.5 says "𝐔, 𝐉"),
    {#MD2.3.4.32} H_T(Z)(𝐔, 𝐉) = H_{T′}(Z̃)(𝐔′, 𝐉′) exactly for the vacuum activities, given (vac)_k below, and H̃(M), Ψ(M), Ĥ(M) and c_𝒢 at flat data on ℓ₀ are the same functionals of the configuration on the dependence set and of the carried old factors on both tori, except for the non-embedding vacuum clusters in e^{−Ψ°(M)}, δΨ(M) and the links' sums (Ψ(M) runs over all vacuum clusters incompatible with M, #MD2.2.5.27, including those of dependence diameter ≥ ι_T/4, whose sets differ between T and T′); their T–T′ difference is the tail C⁎ of (Z-e) and D2.4(13)(c)
    {#MD2.3.4.33} (the Mayer factors are geometric, defined by cubes and walls (RG2 p.14); the cutoffs are CRE (3.16)'s tests on L²M₂R_{k+1}-cubes, cube-local, and their cubes belong to the dependence set; flat data on ℓ₀ at every scale).
    - {#MD2.3.4.34} *The steps written out.* (i) The s-family: H_{T′}(Z̃) is built with T′'s own σ₀ around one lift (RG2 p.13); the cubes of T′'s σ₀ outside Z̃ carry s = 0 in the term, and those of Z̃∖Z̃₀′ are the lifts of those of Z∖Z₀′, so the surviving walks are the lifts of T's (the same holds for Sect. 1's σ₀ in (Z-e)(a)).
      {#MD2.3.4.34-1} (ii) The solutions D(H(s), A′) and 𝐀₀, restricted to the component, are the unique fixed points of the same restricted equations (pp.4–5: "all propagators and the function B are restricted to Y₀").
      {#MD2.3.4.34-2} (iii) The Gaussian integrals: in (2.5) the measures dμ_{C^{(k)}} and dμ_{C^{(k)}(Z₀)} are normalised, and after B′ = (C^{(k)})^{1/2}X, (2.6)'s dμ₀(X) is the product over bonds of normalised standard Gaussians (p.12); the integrand depends on X only on Z (p.17, "∫dμ₀(X)|_Z"), and C^{(k)}(Z₀), (C^{(k)})^{1/2} enter through their walk expansions (p.13: "For this class of localization domains we construct the generalized random walk expansions.
      {#MD2.3.4.34-3} This construction was discussed in [13] for all operators determining Δ_k, and for C^{(k)}(Z₀), but not for (C^{(k)})^{1/2}", so the expansion of (C^{(k)})^{1/2} is RG2's own, and (2.7)), whose pieces PBG p.394's locality covers.
      {#MD2.3.4.34-4} So no global normalisation constant enters H(Z).
      {#MD2.3.4.34-5} (iv) 𝐉: p.14 says "external gauge fields"; 𝐉 = J(𝐔) is local (RG1 (1.8), (3.12), RG1 (1.8), (3.12)).
      {#MD2.3.4.34-6} What is used: H(Z) depends on 𝐉 only through 𝐉 restricted to its dependence set, by RG2 p.5 ("this term depends on 𝐔, 𝐉 restricted to Y₀ ∪ □₀") for the Sect. 1 pieces and p.14 for H(Z).
    - {#MD2.3.4.35} *(vac)_j, the inherited vacuum objects.* H(Z) also contains the step-k vacuum activities: it is a sum "over Z₀, 𝐃, P" (RG2 p.14), its integrand is built from "the last term in (I.3.34), or an arbitrary expression obtained by the transformations of one of the terms" (p.3), p.17's bound carries "∏_{Y∈𝐃}2E₀ε₁…exp(−(1−3δ)κd_k(Y))", and (2.26) contains g_k.
      {#MD2.3.4.35-1} So exactness needs (vac)_j: for every X ∈ 𝐃_j that embeds in T, 𝐄^{(j)}_T(X) = 𝐄^{(j)}_{T′}(X̃) as analytic functions of the full argument (𝐔, 𝐉, 𝐀) restricted to X's dependence set (RG2 p.3 (1.8) evaluates 𝐄(□₀, 𝐔, 𝐀) at 𝐀 = (tζ̃ + t_□ζ)𝐇_k(…)), and g_j is the same on T and T′; the extracted constants agree per polymer, and the global ones cancel in the normalised state.
      {#MD2.3.4.35-2} *Embeds* for X ∈ 𝐃_j: the R_D^{(j−1)}-neighbourhood of X (R_D^{(j−1)} step-(j−1) bonds, i.e. radius R_D^{(j−1)}/L in step-j units) has diameter < ι_{T,j}/4 in step-j units (the margin (Z-g) assigns to a step-j object, #MD2.3.4.53; R_D^{(0)} = ρ_dep fine bonds for the step-1 objects), so the covering T′ → T is injective on it and X has lifts X̃, unique up to deck translations of T′ over T.
      - {#MD2.3.4.36} *Couplings (printed).* RG1 p.264: Π_{j+1} is taken in the "limit of these functions as T^{(j+1)} ↗ Z^d.
        {#MD2.3.4.36-1} This limit exists by the localized representation (1.7).
        {#MD2.3.4.36-2} The function β_{j+1}(g_j) is defined by" (1.22).
        {#MD2.3.4.36-3} So the β-functions are ℤ^d quantities, and with g_K prescribed (D2.3(4)(i)) the g_j of (0.20) are the same on every torus.
        {#MD2.3.4.36-4} The coupling-constant subtraction −β_{j+1}(g_j)A(U_k) (RG1 p.261) is a local term with a torus-independent coefficient.
      - {#MD2.3.4.37} *No finite-torus residual (from RG1 (0.19)–(0.20), (1.3), (1.6), (1.20), p.264).* The torus functions Π^T_{j+1} differ from their ℤ^d limit, so one might expect the torus action to keep (Π^T_{j+1} − Π_{j+1})·A(U).
        {#MD2.3.4.37-1} It does not.
        {#MD2.3.4.37-2} In (1.6), A_k = −(1/g_k²)A(U_k) + Σ_{j<k}{−β_{j+1}(g_j)A(U_k) + [𝐄^{(j+1)}(g_j,U_k) − 𝐄^{(j+1)}(g_j,1)]}, and (0.20), "1/g_k² = 1/g_{k+1}² + β_{k+1}(g_k)", gives Σ_{j<k}β_{j+1}(g_j) = 1/g_0² − 1/g_k².
        {#MD2.3.4.37-3} So the Wilson terms sum to −(1/g_0²)A(U_k): the β-terms rewrite the Wilson coefficient through the numbers g_j and are never subtracted from 𝐄^{(j+1)}.
        {#MD2.3.4.37-4} In (1.6), 𝐄^{(j+1)} is the full torus function of the step-j integration (p.261: "a result of an integration in the j-th step, after a subtraction of the previous action evaluated at U_j"), localised by (1.7).
        {#MD2.3.4.37-5} Π^T_{j+1} is only its second derivative at B = 0 ((1.20)), and it enters only through its ℤ^d limit, which defines β_{j+1} (p.264).
        {#MD2.3.4.37-8} The g_j enter the next step as numbers ((0.19): the block term −(1/g_k²)Σ[1 − Re tr U(y,x)], χ_k, the field scaling), the same on T and T′.
      - {#MD2.3.4.38} *Step.* Given (vac)_k, the new activities H(Z) for embedding Z are the same functionals on T and T′ by (i)–(iv) and PBG p.394's locality, with the inherited 𝐄^{(k)}(Y), Y ⊂ Z, equal by (vac)_k.
        {#MD2.3.4.38-1} Then 𝐄^{(k+1)}(X) of (2.13) is a sum over families Z₁, …, Z_n ⊂ X with ρ^T geometric (ζ is defined by cubes and walls, p.14), so it is the same on T and T′ for embedding X. Its constant part 𝐄^{(k+1)}(X, 1) is a local number of the same kind; the subtracted global constants (E_k, p.262 of CRE; RG1's log Z^{(j)}(1)) are field-independent and cancel in the normalised state.
      - {#MD2.3.4.39} *Base (exact).* (vac)_0 holds: the bare action is the Wilson action, the same local function on every torus, and 𝐄^{(0)} = 0.
        {#MD2.3.4.39-1} Bałaban's step-1 vacuum is RG1's 𝐄^{(1)}, described in V4 sec:extraction-procedure, "In the small-field construction of [RG1], with no large-field regions, … Write 𝐄^{(1)} for the first-step effective interaction, including the Gaussian normalisation", and in V4's introduction, "those factors remain inside the construction of N₁ and ρ₁".
        {#MD2.3.4.39-2} For Bałaban's 𝐄^{(1)}, his localised function, (vac)_1 is the *Step* above at k = 0 from the exact (vac)_0.
        {#MD2.3.4.39-3} **RW1: the T–T′ comparison of V4's step-1 branch weight 𝗐_ξ = e^{c_ξ}I_{ξ;1} on ℓ₀, in (vac)_1's localised form.** V4 does not identify 𝗐_ξ with RG1's e^{𝐄^{(1)}}: 𝐄^{(1)} occurs in V4 only in sec:extraction-procedure, and V4 sec:c5-2-1 says of the comparison with CRE's density "nothing below uses this correspondence".
        {#MD2.3.4.39-4} The comparison is made directly from V4's representation in WILSON_IT1_RW1_CLOSURE_2026_10_30.md.
        {#MD2.3.4.39-5} On ℓ₀, R₁ = S₁ = ∅ (CRE (1.20), p.251), Ψ_ξ = id, I_{ξ;1} = I_{ξ;0} = 𝔫_ξΞ^f_ξ and c_ξ = v(0), so log 𝗐_ξ = v(0) + (d_G|I|/2)log 2π − ½log det H + log Ξ^f_ξ (closure §1). −½log det H is a sum of closed-walk terms supported on balls of radius (m+2)R (V4 (fixed-kernel-inputs); §2), and log Ξ^f_ξ = Σ_𝔠Φ^v_ξ(𝔠) (V4 eq:part1-joint-vacuum-exponential with all domains; §3).
        {#MD2.3.4.39-6} Embedding terms are the same functions on T and T′ at real data, and, given RW1(c), as analytic functions on D(1)(iii)'s connected domain, for the determinant terms (polynomials in the entries of H) and the vacuum clusters (closure §4(a), §5(d)).
        {#MD2.3.4.39-7} At real data the non-embedding terms are at most C_we^{−cι_{T,1}} per step-1 position; their consumer is the *Step* at k = 1 (#MD2.3.4.38), where they are a further summand added to (Z-d)'s non-embedding bound at k+1 = 1 (#MD2.3.4.40), not clusters of φ₁, with C_Z^{(1)} := 4C_S′ (the T–T′ difference has non-embedding terms on both tori); (TC) puts them under it uniformly in K (ι_{T,1} = L^{K−1}ι_{T,K} with L^{K−1} ≥ max(1, (K−1)^{β₀}), and log g₁^{−2} ≤ (1+β₀)max(1, (K−1)^{β₀})log g_min^{−2} by CRE (2.7) (K ≥ 2;
        {#MD2.3.4.39-8} at K = 1, g₁ = g_K), with (TC)'s exponent r ≥ 2, so C_we^{−cι_{T,1}} ≤ C_S′ρ₁e^{−ι_{T,1}/(64M)} for g_min small, with 1/(64M) ≥ c^Z since ν ≤ 1/1000; closure §4).
        {#MD2.3.4.39-9} The outer prefactor's background factors z^{(0)}(U₁) and exp(−g₀^{−2}S(U₁)) (S the Wilson action of the fine background) are products of local factors, compared factor by factor (closure §4).
        {#MD2.3.4.39-10} Both rates are at least c = 1/(32M), by V4 (fixed-kernel-grouping), (fixed-kernel-collar-size) and θ ≥ (log 128)/8 (§4).
        {#MD2.3.4.39-11} **RW1(c):** the representation at complex data in D(1)(iii)'s domain (closure §5, the ℓ₀ case of the IT-1 note's §3e(3.7)): in V4's stencil frame every point is a background e^{iZ} with ‖Z − Z_re‖ ≤ 2α_{1,1}/L ≤ τ_w;
        {#MD2.3.4.39-12} the complex symmetric Hessian has γ/2 ≤ Re H ≤ 2h₊, so V4's Gaussian payment (Lemma gaussian-payment) holds with e^{(1+δ)N₁}, δ ≤ θ, its two real-data inputs redone at complex background (closure §5(b′): the walk-series tail with 3δ_M, M fixed first and τ_w after it, and the reserve identity with ‖T′‖ ≤ 1/3), and V4 Lemma activity-bounds runs at complex background (the positivity uses listed in IT-1 §3e(3.7), and V4 Lemma c2-selected-majorant with its proof read directly), giving the analytic extension of the k^f_ξ, the Kotecký–Preiss criterion at weight 1 + 5θ (convergence, nonvanishing and the branch of log Ξ^f_ξ),
        {#MD2.3.4.39-13} the determinant series with ‖𝖠_H‖ ≤ q_H^{1/2}, the tails at rates ≥ 1/(32M), and the outer prefactor (det_𝔤α_c > 0 at real data by V4 Lemma two-block); its consumer is the *Step* at k = 1 (#MD2.3.4.38).
        {#MD2.3.4.39-14} RW1 also conditions (vac)_j for j ≥ 2 of the project's chain, through the *Step*, whose step-2 input is V4's step-1 output.
        {#MD2.3.4.39-15} The vacuum clusters attached to V4's step-1 groups (V4 Definition groups) are counted in (vi)_1's base ((Z-h)); the unmarked vacuum gas Ξ^f_ξ lies in I_{ξ;0} = 𝔫_ξΞ^f_ξ (V4 (fixed-kernel-source-numerator)), hence in 𝗐_ξ, and falls under RW1; V4's flat regional representation with its periodised free carrier K_T (V4 app:flat-covariance, (bulk-periodisation)) is not part of D(1) (#MD2.3.4.23).
        {#MD2.3.4.39-16} So (vac)_j holds for Bałaban's 𝐄^{(j)} for every j on ℓ₀ (V4's step-1 weight: RW1 with RW1(c)), given PBG p.394's locality's convention, the *Step* ((i)–(iv), with (iii)'s normalisation from RG2 p.12, (2.5)–(2.6)) and the *No finite-torus residual* bullet.
        {#MD2.3.4.39-17} The T–T′ difference of H̃(M), Ψ(M), Ĥ(M) and c_𝒢 is the difference of the carried old factors plus the non-embedding vacuum clusters in e^{−Ψ°(M)}, δΨ(M) and the links' sums ((Z-c)), the first bounded by (Z-e)–(Z-f), the second the tail C⁎ of (Z-e) and D2.4(13)(c).
        {#MD2.3.4.39-18} No Schwarz step is needed for the new parts.
        {#MD2.3.4.39-19} (RG2 p.17's α₅ is Bałaban's remainder size, not an allowance for arbitrary perturbations of the quadratic form.)
  - {#MD2.3.4.40} *(Z-d) The cluster weights (the rooted sum is closed in (Z-f)).* Φ°(Γ) = (Ursell coefficient of Γ)·∏_{𝒢∈Γ}c_𝒢, and the Ursell coefficient depends only on the incompatibility graph, which is the same on T and T′ for clusters whose dependence sets embed in T (the hard core is geometric, D2.3(3)).
    {#MD2.3.4.40-1} A group's diameter, and the network of a cluster, include the supports of the vacuum occurrences merged into it (D2.3(3)).
    {#MD2.3.4.40-2} For such clusters, by (Z-c), Φ°_T(Γ) − Φ°_{T′}(Γ̃) comes from the old objects inside the groups ((Z-e)) and from the non-embedding vacuum clusters inside the groups' vacuum factors, the latter the tail C⁎ of (Z-e) (D2.4(13)(c)).
    {#MD2.3.4.40-3} Telescoping over them, one factor at a time replaced by its difference, the rooted sum of these differences is bounded by (vi)_k in the summed form of (Z-e), through D2.4(13)(c) (|c_𝒢| ≤ S_𝒢 on both tori is (S)).
    {#MD2.3.4.40-4} The count is a Kotecký–Preiss root sum in which the telescoping produces one term per old factor.
    {#MD2.3.4.40-5} For the old occurrences of a group, m_𝒢 telescoped terms carry 1/m_𝒢!, and m/m! = 1/(m−1)!, so the factorial absorbs them and no weight is needed.
    {#MD2.3.4.40-6} For the old insertions D2.4(13)(c) sums over marked trees, so no factor n_ins(𝒢) (the number of old insertions in 𝒢) is produced and no part of a° is reserved for one; the bound a(𝒢) ≥ a_min·n_ins(𝒢) is recorded with the root sum (D2.4(13)(b)).
    {#MD2.3.4.40-7} It follows from the size count: the old insertions of one step-(k+1) group lie on I(𝒢) (D2.3(4), *Y_𝒢*) and come from one compatible step-k family, whose arcs are disjoint (D2.3(3), *Hard core*), each of at least one step-k traversal; I(𝒢) has L·n_{k+1}(𝒢) step-k traversals, so n_ins(𝒢) ≤ L·n_{k+1}(𝒢) ≤ LMσ_{k+1}(𝒢) (σ_{k+1} = #_{k+1} + n_{k+1}/M, D2.4(12)(a)), and a° = (ν/32)σ_{k+1} gives a_min = ν/(32LM).
    {#MD2.3.4.40-8} (The unit of arc-disjointness in the step-k hard core is the step-k traversal, D2.3(3); that the carried groups and the step-1 base keep it is part of (S) and of (vi)_1's base, (Z-h).) The group-level constant is G = 2, the marked-vertex count of D2.4(13)(c), with C_KP = C_S′ and the amplitude ρ_{k+1}·pl.
    {#MD2.3.4.40-9} The clusters whose dependence sets do not embed in T have dependence diameter ≥ ι_T/4, so network extent ≥ ι_T/4 − 2R_D ≥ ι_T/8 once ι_T ≥ 16R_D (R_D is a neighbourhood radius, so the diameter loss is up to 2R_D), and are at most C_S′ρ_{k+1}·pl·e^{−c^Zι_{T,k+1}} on each torus (c^Z of (Z-f), #MD2.3.4.49), by the a°-weight of the reference gas ((Z-f)).
    {#MD2.3.4.40-10} Hence, once ι_T ≥ 16R_D,
    {#MD2.3.4.41} Σ_{Γ: b∈J_Γ}|Φ°(Γ; T) − Φ°(Γ̃; T′)| ≤ C_Z^{(k+1)}ρ_{k+1}·pl·e^{−c^Zι_{T,k+1}}, with C_Z^{(k+1)} and c^Z as in (Z-f),
    {#MD2.3.4.42} for T ⊂ T′, where the old-object term uses ι_{T,k} = Lι_{T,k+1} = (L−1)ι_{T,k+1} + ι_{T,k+1}.
    {#MD2.3.4.42-1} *The branch ι_T < 16R_D is excluded by a torus condition.* (TC): ι_{T,k} ≥ 16L·R_D^{(k)} at every step k ≤ K, both in step-k units (this implies ι_{T,k+1} ≥ 16R_D in step-(k+1) units, since ι_{T,k} = Lι_{T,k+1}).
    {#MD2.3.4.42-2} With R_D^{(k)} ≤ C_DL²MR_k, C_D = 6 ((Z-g)), (TC) at every k follows from the single condition on the coarsest torus
    {#MD2.3.4.43} ι_{T,K} ≥ 32C_DL⁴M(L+1)(log g_min^{−2})^r:
    {#MD2.3.4.44} by Cauchy #CP.14 R_K ≤ 2L(log g_K^{−2})^r ≤ 2L(log g_min^{−2})^r under the prescription g_K ≥ g_min (D2.3(4)(i)); by CRE (2.9) (#CP.14-1) R_k ≤ (L+1)(K−k)^{β₀}R_K for k < K, and R_K itself at k = K, so R_k ≤ (L+1)max(1, (K−k)^{β₀})R_K; and ι_{T,k} = L^{K−k}ι_{T,K} with L^{K−k} ≥ max(1, (K−k)^{β₀}) (β₀ ≤ 1).
    {#MD2.3.4.44-1} It bounds the unit-scale torus from below by a constant independent of K, ε and the step, compatible with the tori of (H3) (which grow) and with (5)(g)'s T_ph ≫ ℓ_C, of which it is a quantified part.
    {#MD2.3.4.44-2} Under (TC) the trivial branch never occurs, and C_Z^{(k+1)} carries no R_D-dependent factor.
    {#MD2.3.4.44-3} C_Z is the absolute constant of this rooted sum only; the per-object relative constant is C_rel of (Z-e).
    {#MD2.3.4.44-4} Uniformity in k: by D2.4(13)(c) the recursion has a tail term from the non-embedding vacuum clusters inside the marked polymers' vacuum factors, C_rel^{(j+1)} ≤ (L(1+β₀)⁷ + 1/8)e^{−c(L−1)ι_{T,j+1}}C_rel^{(j)} + C⁎ with the prefactor ≤ ½ under (TC) (#MD2.4.13.15), c := 1/(32M) (the step-1 rate is unrestricted, (Z-h)), so C_rel^{(k)} ≤ max(C_rel^{(1)}, 2C⁎) = 2C⁎ uniformly in k and in the torus, with C_rel^{(1)} = 0 ((Z-h)).
    {#MD2.3.4.44-5} The weights form a Cauchy sequence along the nested (H3), so the limits Φ°^∞(Γ) exist with the same rate, passed per root with Fatou ((Z-f), *Limits*).
  - {#MD2.3.4.45} *(Z-e) The old objects and the induction (the carry k → k+1 is D2.4(13)(c), the base is (Z-h); (O) is stated per position, as D2.4(13)(c) delivers it, see D(k)(vi) in D2.0(3)).* The new activities contain the carried old insertions Y_W(𝐔) as factors, evaluated at the step-(k+1) background 𝐔 = e^{iη𝐇_k(s)(B′)}·1 inside the fluctuation integral, not at 1, and the old occurrences as the numbers φ_k(Γ_old; T) (D2.3(3)'s merging rules; φ_k are numbers given ℓ, D(k)(v), not functions of (𝐔, 𝐉)).
    {#MD2.3.4.45-1} That background is not T-periodic on T′: 𝐀₀ "is equal to 0 on the neighborhood of Y(σ)ᶜ" (RG2 p.4), so the deformation lives on one lift of Y₀ only, and a clause at periodic lifts does not apply.
    {#MD2.3.4.45-2} The clause (vi)_k is therefore stated in local-agreement form, summed per traversal (a per-object clause carries the factor n_old(W), unbounded since occurrences are counted with multiplicity m_𝒢 and 1/m_𝒢!, so no W-independent constant follows).
    {#MD2.3.4.45-3} For a torus T′ ⊃ T of (H3) and a pair (𝐔, 𝐉) on T, (𝐔′, 𝐉′) on T′ in D(k)(iii)'s domains (𝐉 for k ≥ 2), ΔY_W := Y_W^T(𝐔,𝐉) − Y_W^{T′}(𝐔′,𝐉′) for an insertion W made at a step ≤ k that embeds in T, the configurations coinciding under the covering on the ι_{T,k}/4-neighbourhood of a lift of W's dependence set, and Δφ_k(Γ) := φ_k(Γ; T) − φ_k(Γ̃; T′).
    {#MD2.3.4.45-4} Then (vi)_k states, on ℓ₀ (no attached species, so D(k)(ii) is the right comparison), per position with the full (ii-w) weight, as D2.4(13)(c) uses and delivers it: (I) at every step-k traversal p, ε^{diff}_k(p) := Σ_{W at p, embeds}e^{θ_k(W) + ν_rσ_k(W) + ν_e·ext_k(W)}ℓ_{X_W}|ΔY_W| + Σ_{𝒢 at p, embeds}e^{(ν/16 + ν_r)σ_k(𝒢) + ν_e·ext_k(𝒢)}ℓ_{X(𝒢)}|Δc_𝒢| ≤ C_rel^{(k)}e^{−c_kι_{T,k}}·(D(k)(ii)'s right side in its (ii-w) form at p, the larger of its values on T and T′, since δ*_n's radii R_t^{(k)} = C_boxM(t+1) exceed the agreement radius for large t;
    {#MD2.3.4.45-5} ρ_k·pl_k at the reference point), the 𝒢 the groups made at step k; and (O) at every position p, Σ_{Γ at p, embeds}|Δφ_k(Γ)|e^{d(Γ)} ≤ 2e^{2c_sh+1}C_pc′C_rel^{(k)}e^{−c_kι_{T,k}}ρ_k·pl_k, with D2.4(13)(c)'s d(Γ) = Σ_{𝒢∈Γ}(ν_rσ_k(𝒢) + ν_e·ext_k(𝒢) + 2c_sh + 1 + log C_pc′) (the cluster level of D2.4(13)(c) at step k, from (I)'s group part).
    {#MD2.3.4.45-6} (I) is the inductive clause at traversals; at π_k-cubes the sums are derived at each step by D2.4(12)(e)'s box reduction (D2.4(13)(c)), since a per-cube clause carries a factor ~L².
    {#MD2.3.4.45-7} Carrying: the new parts of a step-(k+1) object are exact by (Z-c); its old factors (insertions inside the fluctuation integral, occurrences as numbers) are telescoped, one replaced by its difference, and the activity is multilinear in each factor inside the integral; the sums over the new objects containing n are then bounded by D2.4(13)(c)'s marked tree sums (D2.4(12)(f)'s rooted count with one vertex marked by its difference; a sum over marked trees, so no factor n_ins(W⁺) arises and no part of a° is reserved for it).
    {#MD2.3.4.45-8} This gives (I), (O) at k+1 with C_rel^{(k+1)} ≤ (L(1+β₀)⁷ + 1/8)e^{−c(L−1)ι_{T,k+1}}C_rel^{(k)} + C⁎, the prefactor ≤ ½ under (TC) (D2.4(13)(c), #MD2.4.13.15; C⁎ the tail term from the non-embedding vacuum clusters in the marked polymers' vacuum factors: e^{−Ψ°(M)}, δΨ(M) and the links' x_T sum over all vacuum clusters incompatible with M) and c_{k+1} ≤ c_k, using ι_{T,k} = Lι_{T,k+1}; the occurrences' telescoped terms are absorbed by 1/m_𝒢!.
    {#MD2.3.4.45-9} The deviation part: (I) at k+1 is relative to D(k+1)(ii)'s right side, whose dev term vanishes at (1, 0); ΔY^d_{W⁺} is the difference of two functions vanishing at (1, 0), analytic on the common domain, and is bounded relative to the deviation by the Cauchy step of D2.4(4) applied to it, as D2.4(13)(c) does at every step; the rooted cluster sum is then (Z-f)'s.
    {#MD2.3.4.45-10} The geometric part of the carry, for a new object W⁺ whose dependence set D⁺ has diameter < ι_{T,k+1}/4 and configurations coinciding on the ι_{T,k+1}/4-neighbourhood of a lift D̃⁺: (a) on the lift Ỹ₀ the deformations e^{iη𝐇_k(s)(B′)} on T and T′ agree, by RG2 pp.4–5 (the deformation is restricted to Y₀) and PBG p.394's locality, with the integration variables identified by the covering;
    {#MD2.3.4.45-11} (b) on T′ the deformation is 0 off Ỹ₀ (p.4), and a point whose projection lies in Y₀ but which is not in Ỹ₀ lies on another lift of Y₀, at distance ≥ ι_T − diam D⁺ > 3ι_T/4 from W̃, outside the neighbourhood N(W̃) of radius ι_{T,k}/4 step-k units = ι_{T,k+1}/4 step-(k+1) units; (c) N(W̃) ⊂ N(D̃⁺), since W ⊂ D⁺ and the radii are the same physical length.
    {#MD2.3.4.45-12} So (vi)_k's hypothesis holds at the inner backgrounds for the old insertions of W⁺, given that these backgrounds lie in D(k)(iii)'s domain (D2.2(4)(f), (6)(e)) and 𝐉-agreement, which needs J local (RG1 (1.8), (3.12)).
    {#MD2.3.4.45-13} The base, (vi)_1 for V4's step-1 groups as functions of U₁ and for their cluster weights, holds with zero difference on embedding objects, by the exact locality of V4's representation ((Z-h)).
  - {#MD2.3.4.46} *(Z-f) The non-embedding clusters from the Kotecký–Preiss weight, and the rooted sum of (Z-d) (from D2.4(12)(f), (13)(c)).* Let Γ be a cluster of the step-(k+1) reference gas on T (or on T′, or on ℤ⁴).
    {#MD2.3.4.46-1} Its groups are connected under incompatibility (D2.3(3) *Hard core*: arcs meeting, domains incompatible, an occurrence hitting a member), and two incompatible groups have supports at distance ≤ one π_{k+1}-cube side M (D2.4(12)(e): the incompatible positions lie in the 3⁴-neighbourhood).
    {#MD2.3.4.46-2} A group's support (its cubes, its arc hull I(𝒢), the domains of its merged occurrences' members, all counted in σ_{k+1}(𝒢) by D2.4(12)(c)) is connected with diameter ≤ M#_{k+1}(𝒢) + n_{k+1}(𝒢) = Mσ_{k+1}(𝒢) in step-(k+1) units.
    {#MD2.3.4.46-3} So the network of Γ (the union of its groups' supports) has diameter ≤ Σ_{𝒢∈Γ}(Mσ_{k+1}(𝒢) + M) ≤ 2MΣ_𝒢σ_{k+1}(𝒢), and the weight a°(Γ) = Σ_𝒢(ν/32)σ_{k+1}(𝒢) of D2.4(12)(f) satisfies a°(Γ) ≥ (ν/(64M))·diam(network of Γ) for k+1 ≥ 2 (at k+1 = 1 the count and the rate are D2.3(5)'s envelope count, #MD2.3.4.49, and the next display holds with c^Z in place of ν/(512M)).
    {#MD2.3.4.46-4} The dependence set of Γ (*Embeds*) lies in the R_D-neighbourhood of its network, R_D in step-(k+1) units ((Z-g)); if Γ does not embed in T, diam(dependence set) ≥ ι_T/4, so diam(network) ≥ ι_T/4 − 2R_D ≥ ι_T/8 under (TC).
    {#MD2.3.4.46-5} Hence, by FV Thm 5.4 (5.11) in the form of D2.4(12)(f) (Σ_{Γ∋b}|Φ°(Γ)|e^{a°(Γ)} ≤ Σ_{𝒢∋b}|c_𝒢|e^{2a°(𝒢)} ≤ C_S′ρ_{k+1}·pl, the Kotecký–Preiss condition at a°/2):
    {#MD2.3.4.47} Σ_{Γ∋b, not embedding in T}|Φ°(Γ)| ≤ e^{−νι_{T,k+1}/(512M)}·Σ_{Γ∋b}|Φ°(Γ)|e^{a°(Γ)} ≤ C_S′ρ_{k+1}·pl·e^{−νι_{T,k+1}/(512M)},
    {#MD2.3.4.48} on T, on T′ (where the clusters of T′ at a lift b̃ of b that are not lifts of embedding clusters of T are exactly those of dependence diameter ≥ ι_{T,k+1}/4, the covering being injective on the smaller ones), and on ℤ⁴ (the weights Φ°^∞ being the limits of (Z-d), with Fatou per root).
    {#MD2.3.4.48-2} So, with the embedding clusters by D2.4(13)(c) (Σ_{Γ∋b, embeds}|Φ°_T(Γ) − Φ°_{T′}(Γ̃)| ≤ 2C_rel^{(k+1)}e^{−cι_{T,k+1}}ρ_{k+1}·pl, c = 1/(32M)), for T ⊂ T′ of (H3) and every step-(k+1) traversal b:
    {#MD2.3.4.49} Σ_{Γ∋b}|Φ°(Γ; T) − Φ°(Γ̃; T′)| ≤ C_Z^{(k+1)}ρ_{k+1}·pl·e^{−c^Zι_{T,k+1}}, C_Z^{(k+1)} := 2C_S′ + 2C_rel^{(k+1)} for k+1 ≥ 2 and C_Z^{(1)} := 4C_S′ (C_rel^{(1)} = 0; the added summand is V4's branch weight 𝗐_ξ, #MD2.3.4.39), c^Z := ν/(256A_dM) (the rate of (Z), independent of k: ≤ ν/(512M), the general-k rate of the count above, since A_d ≥ 2, and at k+1 = 1 the rate of D2.3(5)'s envelope count, diam(network) ≤ A_dLMΣσ fine bonds with a° ≥ (ν/(32A_dM))·diam in step-1 units and diam ≥ ι_{T,1}/8 for non-embedding clusters; the relative clause's rate is c_k = c of D2.4(13)(c)) (≤ 1/(32M) for ν ≤ 16),
    {#MD2.3.4.50} with Φ°(Γ; T) := 0 for a cluster of T′ not embedding in T; C̄_Z := sup_kC_Z^{(k)} ≤ 4C_S′ + 4C⁎ < ∞ (C_Z^{(1)} = 4C_S′ at k+1 = 1, #MD2.3.4.39, and 2C_S′ + 2max(C_rel^{(1)}, 2C⁎) at the other steps) by D2.4(13)(c), uniformly in k, K and the torus, with no (TC)-unrolling needed.
    {#MD2.3.4.50-1} The amplitude is ρ_{k+1}·pl, not τ_k² ((7)(R), 𝔞_{k+1}), also at k = 1, where (Z-h) gives zero on embedding objects and the non-embedding clusters carry ρ₁·pl; the τ² entry below is an upper bound kept for D2.0's sums, not an input, so the (Z) statement of D(k)(vi) carries the amplitude 𝔞_k := max(τ_{k−1}², ρ_k·pl), and D2.3(6)(a)'s torus term reads 12C̄_Z𝔞_{k+1}s_ke^{−c^Zι_{T,k+1}}; since ρ_k·pl ≤ Cg_K²(log g_K^{−2})^{4p₀+(q₁−q₀)₊} ((3)'s ρ_k, g_k ≤ (1+β₀)g_K), the sums of D2.0(6)–(7) are unchanged with τ̄² replaced by 𝔞̄ := max(τ̄², sup_kρ_k·pl), still Cg_K² times a power of log g_K^{−2}.
    {#MD2.3.4.50-2} *Limits.* Along a nested sequence T₁ ⊂ T₂ ⊂ … of (H3) with ι_{T_{j+1}} ≥ 2ι_{T_j}, the weights Φ°(Γ; T_j) of a fixed embedding Γ are Cauchy with Σ_j e^{−c^Zι_{T_j}} ≤ 2e^{−c^Zι_{T_1}}, so Φ°^∞(Γ) := lim_jΦ°(Γ; T_j) exists, is independent of the sequence (two sequences are compared through their least-common-multiple tori, (Z-g)), and Σ_{Γ∋b}|Φ°(Γ;
    {#MD2.3.4.50-3} T) − Φ°^∞(Γ)| ≤ C_Z^{(k+1)}𝔞_{k+1}e^{−c^Zι_{T,k+1}}(1 − e^{−c^Zι_{T,k+1}})^{−1} + C_S′ρ_{k+1}·pl·e^{−c^Zι_{T,k+1}} ≤ 3C_Z^{(k+1)}𝔞_{k+1}e^{−c^Zι_{T,k+1}} for c^Zι_{T,k+1} ≥ 1 (true under D2.0(5)(g)'s T_ph ≫ ℓ_C at every step, since ι_{T,k+1} ≍ T_phL^{K−k−1}), by the telescoping sum over the embedding clusters (Σ_je^{−cι_{T_j}} ≤ Σ_je^{−c(j+1)ι_{T}}) and Fatou for the non-embedding part (whose bound on each T_j holds with ι_T in place of ι_{T_j}, the condition being on the dependence diameter).
    {#MD2.3.4.50-4} This is (Z) at step k+1 in the form of D(k+1)(vi), given (S-w) and (vi)_k.
  - {#MD2.3.4.51} *(Z-g) The tori (H3), the least-common-multiple tori and the margin R_D with C_D computed.* (H3) is V4's family (V4 (c-standing-conditions): every fine period a multiple of LMR₁ and at least 8M; V4 (c5-7-T)(iii): K_μ ≥ 3(n+2), 4ne^{−cι_T} ≤ 1) together with D2.3(1)'s admissibility: the periods are multiples of Π_{k+1} step-k bonds for every k ≤ K (lifted partitions, PBG p.394's locality).
    {#MD2.3.4.51-1} Π_{k+1} is a power of L in step-k bonds ((1), *The period*), i.e. L^kΠ_{k+1} fine bonds, a power of L, and LMR₁ is a power of L (M a power of L by V4 (c-standing-conditions), R₁ by CRE (2.5)); so the admissible fine periods are the multiples of one fixed number P := lcm(LMR₁, L^kΠ_{k+1} for k ≤ K) (a power of L), of size at least 8M; the least common multiple of two multiples of P is a multiple of P, so the least-common-multiple torus of two admissible tori is admissible (V4's (H3) family N_μ = 2L^m, sec:main-result *Hypotheses*, is the case P | 2L^m); nested means each period of T divides the corresponding one of T′.
    {#MD2.3.4.51-2} (S-w) holds on every admissible torus with torus-independent constants (D(k)(iv); D2.4(12)–(13)'s constants depend on L, M, κ, κ_s, C_box, ν, c_D and (11)'s constants only), so the comparison of two non-nested tori goes through their least common multiple with the bounds of (Z-f) for each pair, as PBG p.394's locality's last sentence needs.
    {#MD2.3.4.51-3} *R_D.* The dependence set of a step-(k+1) object is contained in the R_D^{(k)}-neighbourhood of its network (supports, arcs, the domains of merged occurrences, the supports of the old insertions contracted into it), with R_D^{(k)} in step-k bonds the sum of: PBG Thm 3.10's X̃⁵ (p.416, Thm 3.10's walk-term statement; p.413 l.10 says the same of a single operator R(X), "depends on U restricted to X̃⁵", with X a union of cubes of 𝒟, the M₁-cubes of RG2 p.13; five layers, ≤ 5R₁M₁ ≤ 5M step-k bonds by RG2 p.3's R₁M₁ ≤ M); RG2 p.13's σ₀ cubes of π_{k+1} around Z̃₀, side LM;
    {#MD2.3.4.51-4} the cutoff cubes of CRE (3.16), side L²M₂R_{k+1} ≤ LMR_{k+1} ≤ L²MR_k ((1), *Size*); and, for an old insertion made at step j+1 ≤ k, its own margin R_D^{(j)} in step-j bonds, i.e. R_D^{(j)}L^{j−k} step-k bonds, since the old insertion's support is part of the network and its dependence set is the R_D^{(j)}-neighbourhood of that support.
    {#MD2.3.4.51-5} So R_D^{(k)} ≤ 5M + LM + L²MR_k + max_{j<k}R_D^{(j)}L^{j−k} ≤ 2L²MR_k + max_{j<k}R_D^{(j)}L^{j−k} (R_k ≥ 1), and unrolling, with L^{j−k}R_j ≤ (L+1)(k−j)^{β₀}L^{j−k}R_k (CRE (2.9), n = k, m = j) and Σ_{m≥1}(L+1)mL^{−m} = (L+1)L/(L−1)² ≤ 2 for L ≥ 5:
    {#MD2.3.4.52} R_D^{(k)} ≤ 2L²M·Σ_{m≥0}L^{−m}R_{k−m} ≤ 2L²MR_k(1 + 2) = 6L²MR_k, i.e. C_D := 6 in the form R_D^{(k)} ≤ C_DL²MR_k that (TC) uses (no bound R_D^{(k)} ≤ C_DΠ_{k+1} is claimed: Π_{k+1} ≤ L²MR_k is an upper bound on the grid, not a lower one),
    {#MD2.3.4.53} in step-k bonds; in step-(k+1) units R_D = R_D^{(k)}/L ≤ 6LMR_k.
    {#MD2.3.4.53-1} The k-dependence is through R_k only, as (TC) assumes, and (TC) reads ι_{T,K} ≥ 192L⁴M(L+1)(log g_min^{−2})^r.
    {#MD2.3.4.53-2} At step 1 the margin is V4's step-1 dependence halo ρ_dep = R + ρ_w + h_box fine bonds (#MD2.3.4.54; R is V4's locality radius of H, not a term of CRE's scale sequence R_j), in the definition ι_{T,k} = max(0, N_min^{(k)}/4 − ρ_dep L^{−k}) of D2.0(3)(g) (#MD2.0.5.40; ι_{T,1} = max(0, N_min^{(1)}/4 − ρ_dep/L), and ι_{T,k} = Lι_{T,k+1} exactly);
    {#MD2.3.4.53-3} ρ_dep < M(1/2 + C_boxL) < LMR₁/4 fine bonds for g₀ small (#MD2.3.4.54), so the step-1 term of the unrolling is below the j = 0 term 2L²MR₁L^{−k} allowed above, and the bound R_D^{(k)} ≤ 6L²MR_k holds for every k ≥ 1.
  - {#MD2.3.4.54} *(Z-h) The step-1 base of (vi) (from V4's representation: the step-1 objects are exactly local, so (I)₁ and (O)₁ hold with zero left side, C_rel^{(1)} = 0, and the step-1 rate is unrestricted).* The step-1 objects on ℓ₀ are V4's groups W with the insertions Y_W(U₁) — the pairings w_ξ(W)𝔔_ξ(𝒜(W);
    {#MD2.3.4.54-1} f), with f running over the matrix entries of π(T_WP_W^{−1}) on 𝓗(W) at the root variables (V4 Lemma c4-6-1(a)), equivalently over its normalised characters against π(h), which are words of V4 Lemma c4-4-2 closed with the inverse background interval (not the whole-contour f_ξ of eq:part1-closed-family-pairing, also a word of that lemma, whose pairing is not local), and the closed source functional c_W(U₁;
    {#MD2.3.4.54-2} h), bounded by the positive majorant M(W) at physical and at reference data (V4 sec:c4-6-2: "M(W) … bounds |a_W|, the pairings …, and the undifferentiated closed source functional |c_W(U₁;h)|, the physical and reference data having the same numerical majorant") — and the reference-gas weights φ₁(Γ) at the carrier I (V4 Lemma c5-5-8).
    {#MD2.3.4.54-3} *Exact locality.* Each of these objects is a finite sum of absolutely convergent walk series (eq:c-weighted-walk-series) and parameter integrals in V4's local data, each term of which is the same expression on the lift (V4 sec:c4-10-2: "no surviving selected coefficient consults the background outside Q_W, and no field-dependent global spectral quantity appears among the recipe parameters"), and for an object embedding in T (*Embeds*, with the step-1 margin ρ_dep of (Z-g), #MD2.3.4.53: V4's step-1 dependence set lies in the neighbourhood of the network of radius ρ_dep := R + ρ_w + h_box fine bonds,
    {#MD2.3.4.54-4} the domains' 𝐑-neighbourhoods (V4 (fixed-kernel-inputs)), the radius ρ_w = R_* + R + 1 + 2M₁ of the domains D_b (V4, after (fixed-kernel-square-root-series); R_* = n_*R is V4's walk range), and Q_W's halo, "part of the fixed halo included in C_box" (V4 sec:c4-11-4, which lists the consulted objects whose endpoints it contains), h_box ≤ C_box·LM (V4 sec:c4-8-4, sec:c4-11-4); R, ρ_w < M/4 by V4 (fixed-kernel-collar-size) (M ≥ 4(ρ_w + R + R_* + 2)), so ρ_dep < M(1/2 + C_boxL) < LMR₁/4 for g₀ small (R₁ ≥ (log g₁^{−2})^r → ∞, CRE (2.5)), within (TC)) the expression on T′ at the lift is the same expression.
    {#MD2.3.4.54-5} (1) A group's weight w_ξ(W) = ((−1)^{k(W)}/k(W)!)∏_jΦ^v_ξ(𝔠_j) (V4 (part1-group-weight)), with Φ^v_ξ(𝔠) = (φ^T(𝔠)/m!)∏_jk^f_ξ(D_j) (eq:part1-vacuum-cluster), and its pairing 𝔔_ξ(𝒜(W); f) = ∫f(𝖾_𝒜a) d(⊗_{D∈𝒜}ν̂^f_{ξ,D})(a) (eq:fixed-probe-active-pairing): the vacuum clusters of q_ξ(𝒜) (eq:c-cluster-expansion) are members of the group (V4 Definition groups), so the group's dependence set contains their domains, and no factor of W refers to a domain outside it.
    {#MD2.3.4.54-6} (2) Each k^f_ξ(D) and ν^f_{ξ,D} is a finite sum of selected integrals with final domain D (eq:c-selected-integral, eq:probe-selection-measure): with σ_Δ = 0 off D every walk with w_ω ≠ 0 has D(ω) ⊂ int D (lem:component-blocks), so Γ_{E₀}(σ) is formed from H's entries on D's 𝐑-neighbourhood; C_{E₀} = ⊕_D(ι*_{E_D}Hι_{E_D})^{−1} is the inverse of a finite block (eq:fixed-kernel-exact-blocks); s_H = 2h₊, n_* and a_j are numbers (V4 sec:fixed-first-kernel); the X-integral reads X on J_D only and the rest of μ₀ integrates to one (proof of V4 Lemma polymer);
    {#MD2.3.4.54-7} the potentials 𝐕_ξ(Y, ·), the cutoffs χ_b and the probe labels 𝖫_D are local (V4 sec:selected-integrals, sec:probe-kernels); and H(b, c) is determined by the background, Ω₁ and membership in I within distance R of b (V4, with (fixed-kernel-inputs)).
    {#MD2.3.4.54-8} (3) The closed source functional c_W(U₁; h) consults only background bonds in Q_W (IT-1 note §3d(4)(b), V4 sec:c4-11-4), and the reference-gas weights φ₁(Γ) at the carrier I (V4 Lemma c5-5-8) are Ursell coefficients, the same for the lifted cluster (D2.3(3)), times such group factors.
    {#MD2.3.4.54-9} (4) The partitions π₀, π₁ and the M₁-partition are lifted (periods multiples of LMR₁, V4 sec:fixed-first-kernel; (Z-g)), the probe hosts are defined through a lift (V4 (c-probe-host)), and the hull rule (V4, the paragraph after (c-cluster-expansion)) depends on the contacts, n_C and the base point only, which are the same for the lifted contour; on ℓ₀, Ω₁ = Λ₁ = T, I = Λ₁* and J = Ω₁*∖I = ∅ (V4 sec:branch-data), so the branch data are trivially the lifted ones.
    {#MD2.3.4.54-10} Since J = ∅, A_e, j_ξ and the t-interpolation are absent, the exterior response ℬ_ξ of V4's numerator (c-physical-numerator), a covariance under the global ν_{ξ;t} (V4 (fixed-probe-boundary-functional)), vanishes.
    {#MD2.3.4.54-11} The branch weight 𝗐_ξ = e^{c_ξ}I_{ξ;1} (V4 (c-collar-identity)) is non-local (through 𝔫_ξ = (2π)^{d_G|I|/2}det(H)^{−1/2} on all of I, V4 Lemma polymer, and through c_ξ, V4 (native-collar-boundary-constant)) and does not cancel (V4 sec:c4-10-2: the conditional cancellation "does not cancel 𝗐_ξ = e^{c_ξ}I_{ξ;1} or the physical 𝒵₀"), but it is not a factor of Y_W, c_W or φ₁; its T–T′ comparison is RW1 with RW1(c) (#MD2.3.4.39).
    {#MD2.3.4.54-12} The IT-1 shift m vanishes on ℓ₀: Λ₁ = T gives Λ₁^{(0)} = Fill(T) = T, D(Λ₁^{(0)}) = I, J(Λ₁^{(0)}) = ∅, an empty collar and Λ₁^{fin} = T (V4 sec:c5-3-1, Lemma c5-3-3(i)), so J(Λ) = E_{Ω,*}∖D(Λ) = I∖I = ∅ (V4 sec:c5-2-3), ℓ_Λ = H_{D(Λ)J(Λ)}A^{Λ,Ψ} = 0 and m = −H^{−1}ℓ_Λ = 0 (V4 sec:c5-4; likewise m₀ and m̂), so the caller's Υ¹_W (#MD2.2.4.9) is V4's X_W − a_W·id.
    {#MD2.3.4.54-13} So for U₁ on T and U₁′ on T′ coinciding on the ι_{T,1}/4-neighbourhood N of a lift of W's dependence set, Y_W^T(U₁) = Y_W^{T′}(U₁′), c_W^T = c_W^{T′} and φ₁(Γ; T) = φ₁(Γ̃; T′): both sides are the same function of U₁|_N, at real U₁ term by term before any estimate, and at complex U₁ in D(1)(iii)'s domain (RW1(c), WILSON_IT1_RW1_CLOSURE_2026_10_30.md §5(a)–(e), supplies the Hessian, the Gaussian payment, the potentials and the activities there;
    {#MD2.3.4.54-14} the probe pairings and c_W are finite-dimensional integrals of these data against the same Gaussian, analytic by the dominated convergence of V4 sec:c4-11-3), the coefficients being the same finite-dimensional formulas there (V4 sec:c4-10; sec:c4-11-3 gives the dominated convergence for the derivatives, "a background-independent Gaussian majorant for that finite-dimensional integral"; equivalently, by the identity theorem, D(1)(iii)'s domain at k = 1 being a product of per-bond balls, #MD2.0.3.53).
    {#MD2.3.4.54-15} No covariance comparison, image bound or density derivative enters.
    {#MD2.3.4.54-16} Hence, for every step-1 position p (traversal or cube):
    {#MD2.3.4.55} (I)₁ Σ_{W at p, embeds}e^{θ(W) + ν_rσ₁(W) + ν_e·ext₁(W)}ℓ_{X_W}|Y_W^T(U₁) − Y_W^{T′}(U₁′)| + Σ_{W at p, embeds}e^{(ν/16 + ν_r)σ₁(W) + ν_e·ext₁(W)}ℓ_{X_W}|c_W^T(U₁; h) − c_W^{T′}(U₁′; h)| = 0 for every h, by exact locality.
      {#MD2.3.4.55-0} This is (I)₁ relative to D(1)(ii)'s base (ii-w) at k = 1, in the per-position form of (Z-e), with C_rel^{(1)} := 0 and any rate, at traversals and at cubes; groups of dependence diameter ≥ ι_{T,1}/4 do not embed and do not occur in the sum, and the restriction "embeds" is the one of *Embeds* with R_D^{(0)} = ρ_dep fine bonds, i.e. R_D = ρ_dep/L step-1 bonds ((Z-g), #MD2.3.4.53);
    {#MD2.3.4.56} (O)₁ sup_pΣ_{Γ at p, embeds}|φ₁(Γ; T) − φ₁(Γ̃; T′)|e^{d(Γ)} = 0, the sup over all step-1 positions, by exact locality (the Ursell coefficient is the same for the lifted cluster, and each group factor is equal).
    {#MD2.3.4.56-1} The Kotecký–Preiss check for the step-1 reference gas, which (Z-f) uses for the non-embedding step-1 clusters, is (c4-6-5)'s c-version: e^{2a°+d} ≤ e^{2c_sh+1}C_pc′·(the full weight), absorbed by e^{4η𝔰} (D2.4(12)(b) *Base*), with a° := (ν/32)σ₁ and ≤ (81A_F + M)σ₁(W) positions per group at step 1 (V4 Lemma c4-6-env(d)), which replaces D2.4(12)(e)'s 81Mσ₁(W) and changes only the constant of the absorption.
    {#MD2.3.4.57} So C_rel^{(1)} = 0, and no step-1 rate enters the recursion: (I)₁, (O)₁ hold at every rate, in particular at c₁ := c (#MD2.4.13.15's c_k := c for every k), so c = 1/(32M), c^Z = ν/(256A_dM), and the carry condition of D2.4(13)(c) is the c = 1/(32M) case (#MD2.4.13.15), with no lower bound on M from step 1.
    {#MD2.3.4.57-1} The dev clause of (I)₁ is void, since ΔY_W ≡ 0 on embedding groups.
    {#MD2.3.4.57-2} The non-embedding step-1 objects enter (Z) only as the non-embedding clusters of (Z-f), paid by the reference-gas weight a°, and, for V4's branch weight 𝗐_ξ, as the further summand of (Z-d)'s non-embedding bound at k+1 = 1 (#MD2.3.4.39, C_Z^{(1)} := 4C_S′).
    {#MD2.3.4.57-3} *What is used:* V4's representation (lem:polymer, lem:component-blocks, lem:probe-measures, prop:centred-expectation, eq:c-cluster-expansion, Definition groups), V4's locality of H (with (fixed-kernel-inputs)), IT-1 note §3d(4)(b)'s finite support of c_W, and (Z-g)'s lifted partitions.
    {#MD2.3.4.57-4} (vac)_1 for Bałaban's 𝐄^{(1)} is the *Step* at k = 0 ((Z-c), *Base*); the comparison of V4's branch weight 𝗐_ξ is RW1 with RW1(c) (#MD2.3.4.39), and does not enter (I)₁ or (O)₁.
  - {#MD2.3.4.58} *Result.* (Z) holds at every step in the form of D(k)(vi), with the amplitude 𝔞_k = max(τ_{k−1}², ρ_k·pl) (#MD2.3.4.50-1, #MD2.3.4.50-4), given (S-w) (D2.4(12)(f) with (13)(c) and the inputs of D2.4(13)(d)), (T-dev)'s inputs where the carried insertions' dev form is used (#MD2.4.5.13), O6 §5a for the bracket-term consumers at complex σ_k (#MD2.2.6.170), RW1 with RW1(c) (#MD2.3.4.39), and the step-1 base (Z-h) on IT-1's D1 (#MOMGD.47).
  - {#MD2.3.4.59} *Sources of (Z-c):* the base, couplings and absence of a finite-torus residual of (vac)_j are from RG1 pp.255–256, 260–261, 264 and RG2 p.12; the lift of the CRE (3.16) cutoff cubes is settled by the periods' divisibility by Π_{k+1} (PBG p.394's locality bullet); RG1 (1.8), (3.12) is printed.
    {#MD2.3.4.59-2} The old insertions' dependence sets are part of *Embeds*.
  - {#MD2.3.4.60} The coefficients below are defined on ℤ⁴ through these limits.
    {#MD2.3.4.60-1} V4 does the same at step 1 (V4 sec:extent-weights: "Use the infinite-lattice covariance constructed from the same periodic block grid").

### (5) The Coefficients {#MSD2.3.5}

- {#MD2.3.5.1} *The tail bound (T′).* For the reference gas on ℓ₀ of the square (on T, and on ℤ⁴ through (Z)), and for the straight-line and bent-path gases, defined as the clusters of the square gas whose dependence sets meet only one side, or only the two rays at one corner, of a square C′ on T (and on ℤ⁴ the limits of these as C′ and T grow, below), for every step-k traversal b and every R ≥ 0:
  {#MD2.3.5.2} Σ_{Γ: b∈J_Γ, diam(network of Γ) ≥ R}|Φ°(Γ)| ≤ C_S′𝔞_{k+1}e^{−c_dR}, c_d := ν/(32A_dML) per step-k bond, A_d := max(2, A_E + 1) (A_E V4's envelope constant, Lemma c4-6-env), 𝔞_{k+1} := max(τ_k², ρ_{k+1}·pl),
  {#MD2.3.5.3} uniformly in k.
  {#MD2.3.5.3-1} *Derivation (from D2.4(12)(f) by the argument of (4)(Z-f)):* the network of Γ (the supports, arc hulls and merged occurrences' domains of its groups, all counted in σ_{k+1}) is connected up to gaps of one cube side and has diameter ≤ 2MΣ_{𝒢∈Γ}σ_{k+1}(𝒢) step-(k+1) units = 2MLΣσ step-k bonds, so the weight a°(Γ) = (ν/32)Σσ_{k+1} is ≥ (ν/(64ML))·diam ≥ c_d·diam; and Σ_{Γ∋b}|Φ°(Γ)|e^{a°(Γ)} ≤ Σ_{𝒢∋b}|c_𝒢|e^{2a°(𝒢)} ≤ C_S′ρ_{k+1}·pl by FV Thm 5.4 (5.11) under the Kotecký–Preiss condition at a°/2 (D2.4(12)(f)).
  {#MD2.3.5.3-2} *On ℤ⁴.* Fix a line or bent-path cluster Γ on ℤ⁴ rooted at b, with dependence diameter D. For every admissible torus T with ι_T > 4D and every square C′ on T with sides longer than 2D, placed so that Γ's dependence set meets one side (or the two rays at one corner) of C′, contour locality ((4), *Contour locality*) makes Γ a cluster of C′'s square gas on T, with the same incompatibility graph.
  {#MD2.3.5.3-3} So every finite family of such clusters with dependence diameter ≤ D′ has root sum ≤ C_S′𝔞_{k+1}e^{−c_dR} on each torus T with ι_T > 4D′ carrying a square C′ with sides longer than 2D′, by the torus- and contour-uniform (12)(f) (the auxiliary contour C′ satisfies the induction's standing hypotheses on T: (12)(f) is proved for every square contour of the admissible sides on every admissible torus, with constants independent of both;
  {#MD2.3.5.3-4} at k+1 = 1 the tori are taken large enough that C′ also meets V4's standing conditions ((c-standing-conditions), and the coarse-square requirement K_μ ≥ 3(n+2) of sec:main-result *Hypotheses*, sec:extent-weights and sec:c5-5-0), V4's constants being "fixed before the coupling and independent of the loop length" (Lemma c4-6-2)).
  {#MD2.3.5.3-5} By (Z), Φ°(Γ; T) → Φ°^∞(Γ) for each cluster as T grows.
  {#MD2.3.5.3-6} So the truncated ℤ⁴ root sum obeys the same bound, and D′ → ∞ gives (T′) on ℤ⁴ by monotone convergence.
  {#MD2.3.5.3-7} For the step-1 gas (k+1 = 1), V4's reference gas φ₁ at the carrier I (V4 Lemma c5-5-8; D(1) is on V4, #MOMGD.47), the same derivation applies.
  {#MD2.3.5.3-8} The Kotecký–Preiss condition at a°/2, a° = (ν/32)σ₁, is #MD2.3.4.56's ((c4-6-5)'s c-version).
  {#MD2.3.5.3-9} *The step-1 group sum with the amplitude 𝔞₁.* φ₁'s activities are the reference activities a_W of V4 (part1-reference-group) at the carrier I (V4 Lemma c5-5-8: "the reference gas at the carrier I …, activities a_W"), and V4 sec:c4-6-2 bounds them by the positive majorant M(W) ("it bounds |a_W| …, the physical and reference data having the same numerical majorant", Lemma c4-4-2 applying at the reference data by Lemma c2-reference).
  {#MD2.3.5.3-10} V4 (c4-6-5) (Lemma c4-6-2) gives sup_nΣ_{W: n∈𝓗(W)}M(W)e^{4η𝔰(W)} + sup_ΔΣ_{W: Δ∈F(W)}M(W)e^{4η𝔰(W)} ≤ Cρ, rooted at the contour traversals and at the footprint cubes; (T′) roots at b ∈ J_Γ, the contour traversals (#MD2.0.3.7), so its root sum is (c4-6-5)'s first term, the sup over n ∈ 𝓗(W).
  {#MD2.3.5.3-11} V4's ν := η and σ(W) := 𝔰(W) = n(W) + |𝓗(W)|/(LM) (V4 Lemma c5-5-8, (c4-6-1)), the step-1 base of σ₁ (#MD2.4.12.1), so e^{4η𝔰} dominates e^{2a°} = e^{(ν/16)σ₁}.
  {#MD2.3.5.3-12} With ρ = (u/u_*)² + (u/u_*)v = O(g₀²(1+r)⁴) (V4 (c4-4-8): u = C_χg₀(1+r) by sec:c4-4-1, and v ≤ u + 4/R_Υ = u + 8C₀^∂g₀(1+r)³/ω_* by (c4-4-4), R_Υ ≥ 2) and ρ ≤ C(1+β₀)⁶ρ₁ (#MD2.0.3.39), the group sum is ≤ C(1+β₀)⁶ρ₁ ≤ C(1+β₀)⁶𝔞₁ (pl ≥ 1), and C_S′ of (S-w) is taken ≥ C(1+β₀)⁶ (both constants fixed before the coupling), so the step-1 group sum is ≤ C_S′𝔞₁ as #MD2.3.5.2 and #MD2.4.7.15 state.
  {#MD2.3.5.3-13} V4 Lemma c5-5-8(a)'s first-order amplitude ε̄_t = 2K_χC_pinρ_t comes from the t-family majorant M_Λ and is not needed on ℓ₀, where the t-interpolation is absent (#MD2.3.4.54).
  {#MD2.3.5.3-14} *The step-1 rate.* The envelope 𝔈(W) ⊇ F(W) ∪ π₁(𝓗(W)) is connected and has ℓ^∞ diameter ≤ A_ELMσ(W) fine bonds (V4 Lemma c4-6-env; c5-5-8(b)); two incompatible groups have touching footprints or overlapping intervals (V4 Lemma c4-6-env(d)), so the network of Γ has diameter ≤ Σ_{W∈Γ}(A_E + 1)LMσ(W) ≤ A_dLMΣσ fine bonds (σ(W) ≥ 1), and a°(Γ) = (ν/32)Σσ ≥ c_d·diam.
  {#MD2.3.5.3-15} So (T′) holds at k+1 = 1 with the amplitude 𝔞₁ and the rate c_d, uniformly with the general k.
  {#MD2.3.5.3-16} No network property is used.
  {#MD2.3.5.3-17} The old and vacuum occurrences merged into the groups ((3)) are inside σ_{k+1} (D2.4(12)(c)), so (T′) pays for them.
- {#MD2.3.5.4} *Perimeter.* For v ∈ 𝒱_□ let ℓ_v ⊂ ℤ⁴ be the straight line through the origin in orientation v, with its step-k traversals indexed by b ∈ ℤ.
  {#MD2.3.5.4-1} The reference gas on ℓ_v has the groups with short arcs on ℓ_v.
  {#MD2.3.5.4-2} By contour locality, their activities and interactions are the values on any contour that contains their arcs, taken on ℤ⁴ by (Z).
  {#MD2.3.5.4-3} With J_Γ the traversals in the arcs of Γ's groups, put
  {#MD2.3.5.5} a_v(b) := Σ_{Γ: b∈J_Γ}Φ°^∞_v(Γ)/|J_Γ|, κ^{(k+1)}_v := Σ_{b=0}^{Π_{k+1}−1}a_v(b), δm_{k+1} := −(4Π_{k+1})^{−1}Σ_{v∈𝒱_□}κ^{(k+1)}_v.
  {#MD2.3.5.5-1} At an 𝐑-step k+1 > N_{k+1} the flat part of the 𝐑-gas's cluster series along C enters here: δm_{k+1} is replaced by δm_{k+1} − μ^R_{k+1}, with μ^R_{k+1} := +(4LΠ^R_{k+1})^{−1}Σ_vκ^R_v, the per-length coefficient of the 𝐑-gas's flat series with the sign of μ = −δm (D2.7 note 15.4(ii)), and the corner coefficient ζ_{k+1} (z = e^ζ, #MOMST.7-1) by ζ_{k+1} + ζ^R_{k+1} (D2.7 note 15.4).
  {#MD2.3.5.5-2} (6)(a) holds at 𝐑-steps with E°_{k+1} + E°^R_{k+1} in place of E°_{k+1} and D2.7 15.4's bound on E°^R_{k+1}, and (8)'s identity with κ_{k+1}κ^R_{k+1}, κ^R_{k+1} := e^{P_k(C)μ^R_{k+1} + 4ζ^R_{k+1}} (D2.7 15.8's κ_k^R with k+1 in place of k).
  - {#MD2.3.5.6} a_v is Π_{k+1}-periodic by the invariance.
    {#MD2.3.5.6-1} By (T′) at R = 0, |a_v(b)| ≤ C_S′𝔞_{k+1}, so |δm_{k+1}| ≤ C_S′𝔞_{k+1}.
  - {#MD2.3.5.7} δm_{k+1} is per step-k bond, D2.0(3)'s convention (δm_1 := δm^σP(C_n)/P_0(C_n); V4's (marginal-full-perimeter) is per unit length, with the factor 1/(Lε)).
    {#MD2.3.5.7-1} At a commensurate step, δm_{k+1}P_k(C) = −n_kΣ_vκ^{(k+1)}_v, since P_k(C) = 4s_k = 4n_kΠ_{k+1}.
- {#MD2.3.5.8} *Corners.* For (v, w) ∈ 𝒞_□ (eq:corner-square-pairs), take the bent path of eq:corner-bent-path at the scale of the step-k traversals, with the bend at the origin, a period point.
  {#MD2.3.5.8-1} Let a_{v,w}(b) be its rooted density, and k_{v,w}(b) := a_v(b) for b < 0 and a_w(b) for b ≥ 0.
  {#MD2.3.5.8-2} Put
  {#MD2.3.5.9} ζ^{(k+1)}_{v,w} := Σ_{b∈ℤ}(a_{v,w}(b) − k_{v,w}(b)), ζ_{k+1} := ¼Σ_{(v,w)∈𝒞_□}ζ^{(k+1)}_{v,w}, z_{k+1} := e^{ζ_{k+1}}.
  - {#MD2.3.5.10} A cluster whose arcs all lie on one ray has the weight of the same cluster on that ray's line.
    {#MD2.3.5.10-1} Its groups see C only through their arcs (contour locality), the flat construction on ℤ⁴ does not involve C, and the bend is at a period point.
    {#MD2.3.5.10-2} This is V4's argument in the paragraph that leads to (corner-localisation-bound) (sec:marginal-corner), including "Vacuum carriers may cross the bend".
  - {#MD2.3.5.11} So only clusters with arcs on both rays, and the straddling straight-line clusters V4 names, survive in a_{v,w}(b) − k_{v,w}(b) (the factor 2 of the bound covers the latter).
    {#MD2.3.5.11-1} Their network contains the traversal b and a traversal of the other ray, so its diameter is ≥ |b|, and (T′) gives |a_{v,w}(b) − k_{v,w}(b)| ≤ 2C_S′𝔞_{k+1}e^{−c_d|b|} (no network range R_* is needed: by contour locality ((4)) a group sees C through its arcs only).
    {#MD2.3.5.11-2} Hence |ζ_{k+1}| ≤ C_ζ𝔞_{k+1}, with C_ζ := 2C_S′(1 + 2/(e^{c_d} − 1)).
- {#MD2.3.5.12} *Independence.* δm_{k+1} and ζ_{k+1} are ℤ⁴ quantities of a straight line and a bent path at flat trivial-label data.
  {#MD2.3.5.12-1} They do not depend on the size of C, the torus or ℓ.
  {#MD2.3.5.12-2} They depend on k through the couplings and the old objects, and on L, G, χ, σ and the prescriptions.
  {#MD2.3.5.12-3} They may depend on the coordinate plane of C: covariance of the step under the hypercubic group is not established (translation covariance (RTR), #MOMGD.23; RTR_PROOF_PASS, *Hypercubic covariance*), so κ^{(k+1)}_v and ζ^{(k+1)}_{v,w} are kept per orientation and corner pair.
  {#MD2.3.5.12-4} D2 uses only the averages δm_{k+1}, ζ_{k+1} over C's own orientations and corners: C is a square, its four sides have the same length s_k, so the perimeter part of a side of orientation v is (s_k/Π_{k+1})κ^{(k+1)}_v at commensurate s_k and the four sides sum to −P_k(C)δm_{k+1}; the four corners sum to 4ζ_{k+1}.
  {#MD2.3.5.12-5} No equality between orientations or planes is used, and the bounds of (4)–(6) do not use one.

### (6) The Square: The Remainder E°_{k+1} {#MSD2.3.6}

{#MD2.3.6.1} Put F°_{k+1}(C; T) := log 𝒲°_{k+1}(C; T) = Σ_ΓΦ°(Γ; T) and
{#MD2.3.6.2} E°_{k+1}(C, T) := F°_{k+1}(C; T) + δm_{k+1}P_k(C) − 4ζ_{k+1}.
{#MD2.3.6.3} The torus satisfies (5)(g)'s condition T_ph ≫ ℓ_C, so N^{(k)}_min ≫ s_k.

- {#MD2.3.6.4} *(a) Commensurate steps.* |E°_{k+1}| ≤ C_E𝔞_{k+1}(s_k+1)e^{−c_Es_k} + 12C̄_Z𝔞_{k+1}s_ke^{−c^Zι_{T,k+1}}, 𝔞_{k+1} := max(τ_k², ρ_{k+1}·pl) (corner constant and torus constant separate; amplitude 𝔞 from (4)(Z-f) and (5)(T′)).
  - {#MD2.3.6.5} Allocate by |J_Γ|^{−1}: F°_{k+1} = Σ_ba_□(b; T) over the 4s_k traversals of C, with a_□(b; T) := Σ_{Γ: b∈J_Γ}Φ°(Γ; T)/|J_Γ|.
  - {#MD2.3.6.6} Give each corner the last ⌊s_k/2⌋ traversals of its incoming side and the first s_k − ⌊s_k/2⌋ of its outgoing side (V4's half-sides, sec:marginal-corner).
    {#MD2.3.6.6-1} Translate the corner to the origin.
    {#MD2.3.6.6-2} It is a period point, since the step is commensurate.
    {#MD2.3.6.6-3} At the base corner, where the traversals are numbered from, V4 (sec:marginal-corner) first uses the cyclicity of the trace; here F° is a scalar cluster series and each Y_𝒢 is the product ordered along its own arc (D2.2(6)(d)), so a group across the base point is treated like any other and no cyclicity step is needed.
  - {#MD2.3.6.7} Let b lie in the half-sides of the corner (v, w), at distance ≤ s_k/2 from it, hence ≥ s_k/2 from the other corners.
    {#MD2.3.6.7-1} A cluster Γ ∋ b whose network has diameter < s_k/2 has all its arcs on the two sides of (v, w).
    {#MD2.3.6.7-2} It does not wrap the torus, since N^{(k)}_min ≫ s_k.
    {#MD2.3.6.7-3} Its groups have short arcs.
    {#MD2.3.6.7-4} By contour locality and the invariance, it is a cluster of the bent path, with the same weight on T. The other clusters at b cost at most C_S′𝔞_{k+1}e^{−c_ds_k/2}, by (T′).
  - {#MD2.3.6.8} By (Z), the bent-path weights on T differ from those on ℤ⁴ by at most 3C_Z^{(k+1)}𝔞_{k+1}e^{−c^Zι_{T,k+1}} per root ((4)'s (Z-f) *Limits*).
    {#MD2.3.6.8-1} So |a_□(b; T) − a_{v,w}(b)| ≤ 2C_S′𝔞_{k+1}e^{−c_ds_k/2} + 3C_Z^{(k+1)}𝔞_{k+1}e^{−c^Zι_{T,k+1}}, the factor 2 for the same truncation of a_{v,w}.
  - {#MD2.3.6.9} The sum of a_{v,w}(b) over the half-sides is the sum of k_{v,w}(b) over the half-sides, plus ζ^{(k+1)}_{v,w}, minus the part of ζ^{(k+1)}_{v,w} from |b| ≥ s_k/2.
    {#MD2.3.6.9-1} By (5) that part is at most C_ζ𝔞_{k+1}e^{−c_ds_k/2}.
  - {#MD2.3.6.10} Over the four corners, the half-sides make up the four sides.
    {#MD2.3.6.10-1} Each side is n_k whole period cells, starting at a period point, so its sum of a_v(b) is n_kκ^{(k+1)}_v exactly.
    {#MD2.3.6.10-2} The total is n_kΣ_vκ^{(k+1)}_v = −δm_{k+1}P_k(C).
  - {#MD2.3.6.11} Adding up: |E°_{k+1}| ≤ 4s_k·(2C_S′𝔞_{k+1}e^{−c_ds_k/2} + 3C_Z^{(k+1)}𝔞_{k+1}e^{−c^Zι_{T,k+1}}) + 4C_ζ𝔞_{k+1}e^{−c_ds_k/2}.
    {#MD2.3.6.11-1} This is the bound, with c_E := c_d/2 = ν/(64A_dML) and C_E := 8C_S′ + 4C_ζ for the corner terms (8C_S′𝔞_{k+1}s_ke^{−c_Es_k} and 4C_ζ𝔞_{k+1}e^{−c_Es_k}), and 12C̄_Z for the torus term only (C̄_Z = sup_kC_Z^{(k)} ≤ 4C_S′ + 4C⁎, #MD2.3.4.50, by D2.3(4)(Z-f) with D2.4(12)(f), (13)(c), given (S-w)).
- {#MD2.3.6.12} *(b) The other steps.* With the admissible sides of (4) there are none, and (b) is void.
  {#MD2.3.6.12-1} Without the restriction there are at most a* of them, and the bound is
  {#MD2.3.6.13} |E°_{k+1}| ≤ C_E′𝔞_{k+1}[Π_{k+1} + 1 + s_ke^{−cι_{T,k+1}}] + 4C_S′𝔞_{k+1}s_k (constants from (T′)).
  - {#MD2.3.6.14} Compare a_□(b; T) with the density of the line that carries b's side.
    {#MD2.3.6.14-1} For b at distance d from the nearest corner the comparison costs C_S′𝔞_{k+1}(2e^{−c_dd} + e^{−cι_{T,k+1}}), by the argument of (a) with the line in place of the bent path.
    {#MD2.3.6.14-2} Summed over b this is at most 8C_S′𝔞_{k+1}(1 + 2/(e^{c_d} − 1)) + 4s_kC_S′𝔞_{k+1}e^{−cι_{T,k+1}}.
  - {#MD2.3.6.15} The two sides through the origin lie on ℓ_{e₁}, ℓ_{e₂} (or their reverses).
    {#MD2.3.6.15-1} A side of s_k traversals need not be a union of cells; its sum of a_v(b) differs from (s_k/Π_{k+1})κ^{(k+1)}_v by at most 2Π_{k+1}C_S′𝔞_{k+1}.
  - {#MD2.3.6.16} The two far sides lie on x₁ = s_k and x₂ = s_k, the lines ℓ_v + t·e_⊥ with t = s_k mod Π_{k+1} ≠ 0, which are not period translates of ℓ_v.
    {#MD2.3.6.16-1} Their period sums κ_v^{[t]} have no relation to κ^{(k+1)}_v beyond |κ_v^{[t]}|, |κ^{(k+1)}_v| ≤ Π_{k+1}C_S′𝔞_{k+1}, so each far side leaves (s_k/Π_{k+1})|κ_v^{[t]} − κ^{(k+1)}_v| ≤ 2C_S′𝔞_{k+1}s_k.
  - {#MD2.3.6.17} With |4ζ_{k+1}| ≤ 4C_ζ𝔞_{k+1}, this gives the bound.

### (7) The Sum over the Steps {#MSD2.3.7}

- {#MD2.3.7.1} Put τ̄² := sup_{k<K}τ_k². τ = C[g(1+r)³ + e^{−cr²}] increases in g for small g, and g_k ≤ (1+β₀)g_K (the last inequality of CRE (2.6); CRE (2.6)–(2.7) at general G).
  {#MD2.3.7.1-1} So τ̄² ≤ Cg_K²(log g_K^{−2})^{6p₀}, as in D2.0(5)(f).
  {#MD2.3.7.1-2} Put 𝔞̄ := max(τ̄², sup_{k≤K}ρ_k·pl) ≤ Cg_K²(log g_K^{−2})^{max(6p₀, 4p₀+(q₁−q₀)₊)} ((3)'s ρ_k = C_ρg_k²(1+r_k)⁴ with CRE (2.6)–(2.7)); the amplitude of (5)–(6).
- {#MD2.3.7.2} With m := K − k ≥ 1 and s_k = ℓ_CL^m, (6) gives
  {#MD2.3.7.3} Σ_{k<K}|E°_{k+1}| ≤ C_E𝔞̄Σ_{m≥1}2ℓ_CL^me^{−c_Eℓ_CL^m} + 12C̄_Z𝔞̄Σ_{m≥1}ℓ_CL^me^{−c^Zι_{T,K−m+1}}
  {#MD2.3.7.4} for the admissible sides of (4), where every step is commensurate.
  - {#MD2.3.7.5} Without the restriction, the at most a* steps of (6)(b) add C_E′𝔞̄a*(Π* + 1) + 8C_S′𝔞̄ℓ_CL^{a*} + C_E′𝔞̄Σ_mℓ_CL^me^{−cι_{T,K−m+1}}, with Π* := L²M(L+1)(a*)^{β₀}R_{K−1} bounding Π_{k+1} there, by (4).
    {#MD2.3.7.5-1} The term 8C_S′𝔞̄ℓ_CL^{a*} is uniform in K but linear in ℓ_C.
  - {#MD2.3.7.6} The first sum is at most a constant C(c_E, L), for every ℓ_C ≥ 1 and every K: its terms are xe^{−c_Ex} at x = ℓ_CL^m, which grow at most geometrically up to x ≍ 1/c_E and then decay faster than geometrically.
  - {#MD2.3.7.7} The second is D2.0(5)(g)'s torus sum.
    {#MD2.3.7.7-1} With N^{(k)}_min ≍ T_phL^{K−k} it is at most Cℓ_Ce^{−c′T_ph}, small for T_ph large.
- {#MD2.3.7.8} So, for the admissible sides, the remainders of all steps sum to at most C_Σ𝔞̄, with C_Σ depending on L, c_E, C_E, C̄_Z and c^Z, i.e. on L, M, ν, C_S′, C_rel^{(1)}, C⁎ and A_d (through c^Z = ν/(256A_dM)) (no R_D-dependent factor under (TC)).
  {#MD2.3.7.8-1} It does not depend on K, nor on ℓ_C once T_ph ≫ log ℓ_C (the torus sum is at most Cℓ_Ce^{−c′T_ph}; (5)(g)'s T_ph ≫ ℓ_C gives it).
  {#MD2.3.7.8-2} C_Σ𝔞̄ ≤ Cg_K² times a power of log g_K^{−2}, small for g_K small.
  {#MD2.3.7.8-3} Without the restriction C_Σ also depends on M, β₀, C_E′ and, through a* and R_{K−1}, on g_K, and the bound gains the ℓ_C-linear term above.
- {#MD2.3.7.10} *Consequence for V4's Conjecture iteration.* V4 Remark next-step (3)(e) counts the torus and corner part as Cτ²(2+1/c) per step, one source of (k+2)τ².
  {#MD2.3.7.10-1} With the exact coefficients of every step kept in κ^{(K)}, this source contributes at most C_Σ𝔞̄ in total.
  {#MD2.3.7.10-2} The other source of (k+2)τ², replacing every z_j by 1 (Remark (2)), does not arise.
- {#MD2.3.7.11} *D(k)'s clause on E_const.* The remainder of step j is E°_j of the step j−1 → j, so it carries (6)(a)'s amplitude 𝔞_j = max(τ_{j−1}², ρ_j·pl) ((Z-f): the amplitude is ρ_j·pl, not τ_{j−1}² alone).
  {#MD2.3.7.11-1} So |E_const,k| ≤ Σ_{j≤k}C𝔞_j(n_je^{−c^Zι_{T,j}} + (n_j+1)e^{−c_En_j}), with n_j := s_{j−1}, at the admissible sides.
  {#MD2.3.7.11-3} Without the restriction, each of the at most a* other steps adds C𝔞_j(Π_j + 1 + 4s_{j−1}).
  {#MD2.3.7.11-4} The clause is amended so (note in D2.0(3)).

### (8) D(k+1)(i) and (v): The Assembly {#MSD2.3.8}

{#MD2.3.8.1} On every labelled term ℓ, (3) gives ⟨𝒲_k⟩_{1,1} = κ^{(k)}e^{𝓔_k}S°(ℓ)[f_{k+1} + Σ_{D≠∅}Q^{out}_{k+1}(D)w^d(D)].
{#MD2.3.8.1-1} Put
- {#MD2.3.8.2} κ^{(k+1)} := κ^{(k)}κ_{k+1}, κ_{k+1} := e^{−δm_{k+1}P_k(C)}z_{k+1}⁴, with δm_{k+1} and z_{k+1} of (5);
- {#MD2.3.8.3} E^∂_{k+1}(ℓ) := log S°(ℓ) − log S°(ℓ₀), the difference of the two cluster series;
- {#MD2.3.8.4} 𝓔_{k+1} := 𝓔_k + E^∂_{k+1}(ℓ) + E°_{k+1}(C, T), and E_const,k+1 := E_const,k + E°_{k+1}(C, T).

{#MD2.3.8.5} Since log S°(ℓ₀) = F°_{k+1} = −δm_{k+1}P_k(C) + 4ζ_{k+1} + E°_{k+1}, this gives κ^{(k)}e^{𝓔_k}S°(ℓ) = κ^{(k+1)}e^{𝓔_{k+1}} exactly.
- {#MD2.3.8.6} D(k+1)(i) holds, with coefficients independent of the size of C, the torus and ℓ ((5)).
- {#MD2.3.8.7} D(k+1)(v) holds: E^∂_{k+1}(ℓ), E°_{k+1}(C, T) and Q^{out}_{k+1}(D) are numbers given ℓ.
- {#MD2.3.8.8} E^∂_{k+1}(ℓ) is the step-(k+1) form of V4's E^∂_ξ, |E^∂_ξ| ≤ Cτ²Σ_je^{−cd_j} (V4 (regional-square-boundary-comparison)).
  {#MD2.3.8.8-1} It is the sum of the cluster terms that see ℓ's data: the clusters of ℓ₀ that ℓ does not have (they meet ℓ's large-field regions or their boundaries), the clusters that only ℓ has, and the changes of the activities near ℓ's data.
  {#MD2.3.8.8-2} Its form as a local sum Σ_Xe^{(k+1)}_X with D(k)(ii)'s anchored bound is D2.6's, as IT-1 note §3b and §3i do at step 1.
  {#MD2.3.8.8-3} It must not be bounded globally (D2.0(5)(f)).

### (9) What D2.3 leaves {#MSD2.3.9}

- {#MD2.3.9.1} *To D2.4:*
  - {#MD2.3.9.2} (S-w) with k-independent constants (D2.4(12)(f)), from which the tail (T′) of (5), (Z) and the Kotecký–Preiss condition follow;
  - {#MD2.3.9.3} (Z), at the rate e^{−c^Zι_{T,k+1}} (given (S-w), #MD2.3.4.58);
  - {#MD2.3.9.4} the Kotecký–Preiss condition that gives S°(ℓ) ≠ 0 and the cluster series of S°^{[D]}, on every ℓ;
  - {#MD2.3.9.5} the absolute convergence used in (3), now over the families with their occurrences;
  - {#MD2.3.9.6} Σ_{Γ hits 𝒢}|Φ°(Γ)| ≤ θ_{k+1}(𝒢) for the cluster form of Q^{out}_{k+1}, which gives |Q^{out}_{k+1}(D)| ≤ ∏e^{θ};
  - {#MD2.3.9.7} the payment, in D2.4's size statement (S) (and so in (T′)), for the occurrences merged into the groups by the third rule of (3): their arcs J_Γ, their supports and the entropy of the occurrence tuples;
  - {#MD2.3.9.8} the sizes of the Y^d_𝒢, D(k+1)(ii) for the deviation parts, including at the reference point (reference clause).
- {#MD2.3.9.9} *To D2.6:* E^∂_{k+1}(ℓ) as attached local terms; the species of the Y^d_𝒢 near ℓ's data; the reference clause's sizes on labelled terms.
  {#MD2.3.9.9-1} These are WILSON_IT1_D26_CLOSURE_2026_10_24.md §7.4(a) (E^∂_{k+1}(ℓ) = Σ_Xe^{(k+1)}_X over the loop-dependent clusters meeting Coll_{k+1} ∪ Z_{k+1}, anchored bound Cτ̂_{k+1}² per traversal with τ̂² := max(τ², Cρ̂), attached per component) and §2.5. The same-activity step is 7.4(a)'s: by RG2 (1.9)–(1.10) each activity is a function of the fields on its polymer, and the label enters only through Z_{k+1} and the cutoffs on Coll_{k+1}.
- {#MD2.3.9.10} *To the final-scale step:* the four parts of (4)(iv): on ℓ₀ the comparison of dressed loops on the fixed lattice of the stopping scale uL^{−j(C)}; the large-field terms on ε-dependent lattices with their normalisation; the errors as K → ∞; κ^{(K′)}.
  {#MD2.3.9.10-1} The continuum note WILSON_IT1_CONTINUUM_LIMIT_CLOSURE_2026_10_26.md derives the exact division by κ^{(K′)} (item (6)), the K-uniform bounds on the errors (item (5)), the relative weight 1 − w_{ℓ₀} ≤ δ_LF of the large-field terms (item (7), from WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md §11), and the limit along subsequences (item (8.2), given D(K′) on every labelled term, for K′ > N by the D2.7 closure's 15.8);
  {#MD2.3.9.10-2} the convergence along the full sequence is its item (8.4), the comparison of two runs of WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md, from the input (LF) under the conditions (T1), (T2), (T-Λ), and (T-c) (its #C7.1).
  {#MD2.3.9.10-3} The stopping scale may depend on the loop (#MOMGD.30).

## D2.4 The Contraction Count {#MSD2.4}

### (0) What is needed {#MSD2.4.0}

- {#MD2.4.0.1} *Input.* D2.3(9)'s items to D2.4 (#MD2.3.9.1), and from D2.2(5) the comparison c|M| ≤ νσ(M)/16 (#MD2.2.5.39-2), the sizes of Ĥ(M), and the cost of enlarging D_J to D_J^# (#MD2.2.5.16-5).
- {#MD2.4.0.8} *From D2.0(3)(c) and (5)(c):* the matching (γ) of old and new neighbourhoods and radii, the split (ζ) of the maximum, and the recursion for C_χ^{(k+1)}; the tolerance at complex data.
- {#MD2.4.0.9} *Output.* D(k+1)(ii) and the norms of D(k+1) for the insertions and interactions made at step k+1, with constants that satisfy D(k)(iv).

### (1) Quoted (Bałaban from the transcriptions Balaban\tex\<paper>\parts\pNNN.tex) {#MSD2.4.1}

- {#MD2.4.1.1} *RG1 p.257 (localization domains).* π_j is the family of closed cubes of size M. "Such a domain is a union of a connected, finite family of cubes from π_j.
  {#MD2.4.1.1-1} A connected family means that for every pair □, □′ of cubes from the family there exists a sequence … such that two consecutive cubes have a common wall, i.e. their intersection is a d−1-dimensional cube." The class is 𝐃_j. "Consider a class of tree graphs contained in X and intersecting all the cubes in X. A length of a shortest graph in this class, divided by M, is the linear size of X, and is denoted by d_j(X)."
- {#MD2.4.1.2} *RG2 p.14 (the vacuum gas).* (2.9) "(2.1) = Σ_ZH(Z)".
  {#MD2.4.1.2-1} (2.10): "if Z = Z₁ ∪ ⋯ ∪ Z_n, where Z_i is a connected component of Z, then H(Z) = H(Z₁)⋯H(Z_n)".
  {#MD2.4.1.2-2} (2.11) is the polymer expansion with ∏_{i<j}ζ(Z_i, Z_j), "where the function ζ(Z,Z′) is defined by the condition: ζ(Z,Z′) = 0 if Z∩Z′ contains a cube, or a wall of a cube, and ζ(Z,Z′) = 1 otherwise".
  {#MD2.4.1.2-3} (2.12)–(2.13) are the exponentiated series, with ρ^T(Z₁,…,Z_n) = Σ_{g∈C_n}∏_{{i,j}∈g}(ζ(Z_i,Z_j) − 1).
- {#MD2.4.1.3} *RG2 p.15 (domain).* "Thus the activities in (2.13), and the whole sum 𝐄^{(k+1)}(X), are analytic functions of (𝐔,𝐉), on the space 𝐔^c_{k+1}(X,α₀,α₁)." A term of H(Z) is (2.14), with contour integrals in complex σ(Δ), τ(Y) and real Gaussian integrals in X and B: "We consider it as an analytic function of (𝐔,𝐉) in the space 𝐔^c_{k+1}(X,α₀,α₁), and of the complex parameters σ(Z), τ.
  {#MD2.4.1.3-1} This complicates estimates of this expression, because the operators in it are not symmetric, and the second measure is complex." (2.15) bounds it.
- {#MD2.4.1.4} *RG2 pp.18–20 (the bound).*
  - {#MD2.4.1.5} (2.30), p.18: "(3·2³)^{−1}M^{−4}|Y| ≤ d_k(Y) ≤ M^{−4}|Y| − 1 holding for localization domains Y ∈ 𝐃_k".
  - {#MD2.4.1.6} p.19: "ε₂ = 2E₀ε₁C₁α₄^{−1}α₆^{−1}M^q exp C₂κ₁".
  - {#MD2.4.1.7} p.20: "Assuming that 2(L+2)⁴O(1)ε₂exp5κ ≤ 1, we obtain …"; "We define the constant C₃ = 2(L+2)⁴O(1)2E₀C₁α₄^{−1}α₆^{−1}M^q exp C₂κ₁."
  - {#MD2.4.1.8} Lemma 3, p.20: "Under all the above restrictions on the constants M, κ, κ₁, α₀, α₁, α₄, α₆, γ₂, γ, ε₁, the activity H(Z) for a localization domain Z ∈ 𝐃_{k+1} satisfies the inequality |H(Z)| ≤ C₃ε₁exp(−(1−8δ)½Lκd_{k+1}(Z))" (2.38).
  - {#MD2.4.1.9} p.21: (2.39)–(2.41) repeat "the considerations and bounds of the paper [26], for κ sufficiently large, and ε₁ sufficiently small", and give |𝐄^{(k+1)}(X)| ≤ O(1)C₃ε₁exp(−(1−10δ)½Lκd_{k+1}(X)). "At first we assume that (1−10δ)½L = 1, or δ = (1/10)(1−2L^{−1})." Also "we take M sufficiently large, so that δ₀M ≥ κ".
- {#MD2.4.1.10} *Check of (2.30), left side.* (2.30), p.18, reads "(3·2³)^{−1}M^{−4}|Y| ≤ d_k(Y) ≤ M^{−4}|Y| − 1".
  {#MD2.4.1.10-1} With RG1's d_j, a single cube has d = 0: one point of the cube is a tree graph that meets every cube of the domain.
  {#MD2.4.1.10-2} So the left inequality fails for one cube (1/24 ≤ 0), and also for the 16 cubes around a common vertex.
  {#MD2.4.1.10-3} (2)(a) gives #(Y) ≤ 162(d_k(Y) + 1) in its place (at scale k+1: #(Z) ≤ 162(d_{k+1}(Z) + 1)).
- {#MD2.4.1.11} *Its uses, and RG2 Lemma 3's repair (a repair of the proof).* Pages searched, every line, for uses of the left side of (2.30) or of its Section-1 form "M^{−4}|Y| ≤ 3·2³d_k(Y)", cited or not: RG2 pp.7–21 (pp.10–13 contain none: p.11's "M^{−4}|Y| ≤ exp M^{−4}|Y|" and (1.39), (1.40), (1.43) use no lower bound on d_k).
  {#MD2.4.1.11-1} Below, #(Y) := M^{−4}|Y| at scale k (so "#(Z_0)" on p.19 is M^{−4}|Z_0|) and (LM)^{−4}|Z| at scale k+1, and (2)(a) gives #(Y) ≤ 162(d_k(Y)+1), resp. #(Z) ≤ 162(d_{k+1}(Z)+1).
  {#MD2.4.1.11-2} The uses and their costs:
  - {#MD2.4.1.12} pp.8–9: (1.28) "M^{−4}|Y| ≤ 3·2³d_k(Y) ≤ exp(1/16)(κ₁−2)d_k(Y)" and p.9's "M^{−4}|Y| ≤ 3·2³d_k(Y) ≤ exp δκd_k(Y)" bound the sum over the cubes □₀ (resp. □) of Y. With (2)(a), M^{−4}|Y| ≤ 162(d_k(Y)+1) ≤ 162e^{d_k(Y)}, so each costs a factor ≤ 162 into (1.29)'s absolute O(1), once (κ₁−2)/16 ≥ 1, resp. δκ ≥ 1.
  - {#MD2.4.1.13} p.16, (2.20): "Using (1.28) we obtain" the bound Σ_{Y∈𝐃}α₄exp(−δκd_k(Y)) ≤ O(1)α₄M^{−4}|Y₀| (its second line).
    {#MD2.4.1.13-1} This needs no lower bound on d_k: each Y ∈ 𝐃 lies in Y₀ (2.2) and contains a cube of it, so the sum is ≤ Σ_{□⊂Y₀}Σ_{Y∋□}α₄e^{−δκd_k(Y)} ≤ O(1)α₄M^{−4}|Y₀| by (1.26) with δκ in place of κ.
    {#MD2.4.1.13-2} No cost.
    {#MD2.4.1.13-3} (The quadratic part uses (2.19)'s first exponential, as printed.) If "Using (1.28)" in (2.20) acts instead in passing from (1.43) to the middle line, it costs ≤ 162 per Y by (2)(a), an absolute factor absorbed in α₄'s O(1).
  - {#MD2.4.1.14} p.18, (2.29): "For κ sufficiently large and α₆ sufficiently small we have Σ_𝐃∏_{Y∈𝐃}α₆exp(−δκd_k(Y)) ≤ 1", the sum over the 𝐃 with ∪𝐃 = Y₀ (2.2).
    {#MD2.4.1.14-1} Bałaban refers its proof to [26] and adds "In connection with this notice … (2.30)".
    {#MD2.4.1.14-2} Derivation without (2.30)'s left side: put n := M^{−4}|Y₀|, w(Y) := α₆e^{−δκd_k(Y)} and t := 1/8.
    {#MD2.4.1.14-3} A covering family has Σ_{Y∈𝐃}#(Y) ≥ n, so the sum is ≤ e^{−tn}∏_{Y⊂Y₀}(1 + w(Y)e^{t#(Y)}) ≤ exp(−n(t − ε_t)), with ε_t := sup_□Σ_{Y∋□}w(Y)e^{t#(Y)}.
    {#MD2.4.1.14-4} By (2)(a), e^{t#(Y)} ≤ e^{20.25}e^{20.25d_k(Y)} ≤ e^{20.25}e^{δκd_k(Y)/2} once δκ ≥ 40.5, so ε_t ≤ α₆e^{20.25}Σ_{Y∋□}e^{−δκd_k(Y)/2} ≤ α₆e^{20.25}O(1) by (1.26) with δκ/2 in place of κ.
    {#MD2.4.1.14-5} Hence (2.29) holds once α₆e^{20.25}O(1) ≤ 1/8, an absolute factor in "α₆ sufficiently small".
    {#MD2.4.1.14-6} The single cubes (d_k = 0, and every domain with d_k = 0 has ≤ 2⁴ cubes) are paid by α₆ per member; Y₀ = □ admits only 𝐃 = {□}, with value α₆ ≤ 1.
  - {#MD2.4.1.15} p.19, after (2.34): "The exponential on the right-hand side multiplied by exp(−δκd_k(Z_0)) can be estimated by 1".
    {#MD2.4.1.15-1} The exponent is exp(−(1/20)γ₂ε₁²/γ²)#(Z_0).
    {#MD2.4.1.15-2} Per component Z′ of Z_0, with d := d_k(Z′), the cost is exp(162e^{−4κ}(d+1) − δκd) ≤ exp(162e^{−4κ}) ≤ 2, since 162e^{−4κ} ≤ min(δκ, log2) for κ ≥ κ_vac and L ≥ 3, using p.18's "(1/20)γ₂ε₁²/γ² ≥ 4κ".
  - {#MD2.4.1.16} pp.19–20: "The last sum is estimated using (1.28), with κ replaced by δκ, and with an additional sum over (L+2)⁴ cubes □′ from π_k, the cubes touching a fixed LM-cube in Z_i′".
    {#MD2.4.1.16-1} (1.28) contains no κ; the sum described (components through a fixed □′, weight e^{−δκd_k}) is the sum of (1.26), which uses no lower bound on d_k, so there is no cost.
    {#MD2.4.1.16-2} With (1.28) itself the cost is ≤ 162 per component (δκ ≥ 1), into "(L+2)⁴O(1)".
    {#MD2.4.1.16-3} In both cases the factor is absolute.
  - {#MD2.4.1.17} p.20 l.6: (2.29) applied at scale k+1. p.20 prints only the exponent replacement ("We have δ½Lκd_{k+1}(Z_i′) instead of δκd_k(Y), but the inequality (2.29) is valid for all k"); the prefactor is not printed, and the derivation below holds for both α₆ and 2(L+2)⁴O(1)ε₂.
    {#MD2.4.1.17-1} The derivation above covers any prefactor α with αe^{20.25}O_{(1.26)} ≤ 1/8, O_{(1.26)} the constant of (1.26) at rate δκ/2 (resp. δ½Lκ/2), so it covers both α₆ and 2(L+2)⁴O₃ε₂, given: (i) δκ/2 ≥ κ_{(1.26)}, the threshold of (1.26); (ii) 2(L+2)⁴O₃ε₂e^{20.25}O_{(1.26)} ≤ 1/8, which follows from p.20's assumption 2(L+2)⁴O₃ε₂e^{5κ} ≤ 1 once e^{5κ} ≥ 8e^{20.25}O_{(1.26)}; and δ½Lκ ≥ δκ.
  - {#MD2.4.1.18} p.20, in Lemma 3's proof: "We use the factor exp(−δ½Lκd_{k+1}(Z)), and the inequality (2.30), to bound the exponentials by 1".
    {#MD2.4.1.18-1} The exponentials are exp(A·#(Z)), A an absolute bound for O(1)(LM)⁴α₅ + exp(−½(κ₁−1)) (p.20: "We assume that (LM)⁴α₀, (LM)⁴α₁, (LM)⁴α₄, (LM)⁴γ₂ are bounded by a constant independent of M, for example by 1", with α₅ = O(1)e^{−δ₀M/3} + O(α₀+α₁) + O(1)α₄ + γ₂, so also (LM)⁴e^{−δ₀M/3} ≤ 1 for M ≥ M(L); A is fixed as an absolute number before κ).
    {#MD2.4.1.18-2} With (2)(a), exp(A#(Z) − δ½Lκd_{k+1}(Z)) ≤ e^{162A}e^{(162A − δ½Lκ)d_{k+1}(Z)} ≤ e^{162A} once δ½Lκ ≥ 162A, i.e. κ ≥ 3240A/(L−2) (p.21's δ).
  - {#MD2.4.1.19} p.21, after (2.40): an uncited use for 𝐄^{(k+1)}(X).
    {#MD2.4.1.19-1} (2) does not use the bound on 𝐄^{(k+1)}, so this use is not needed.
  - {#MD2.4.1.20} *RG2 Lemma 3's repair.* The proof of Lemma 3 goes through with (2)(a) in place of (2.30)'s left side.
    {#MD2.4.1.20-1} The cost is that Bałaban's absolute constants are enlarged by absolute factors: 162 in (1.29)'s O(1) (pp.8–9); e^{20.25} in "α₆ sufficiently small" (p.18); and 2 (p.19), ≤ 162 (pp.19–20, only if literal (1.28)) and e^{162A} (p.20) in the O(1) of "(L+2)⁴O(1)ε₂" on p.20.
    {#MD2.4.1.20-2} Call that enlarged O(1) O₃; it is the O(1) of p.20's assumption "2(L+2)⁴O(1)ε₂exp5κ ≤ 1" and of C₃.
    {#MD2.4.1.20-3} So Lemma 3 holds as printed, (2.38) with C₃′ := C₃ computed with O₃ (convention: C₃′ always means this).
    {#MD2.4.1.20-4} *Definition:* C₃′ := 2(L+2)⁴O₃·2E₀C₁^{L1}α₄^{−1}α₆′^{−1}M^q exp C₂κ₁, p.20's formula "C₃ = 2(L+2)⁴O(1)2E₀C₁α₄^{−1}α₆^{−1}M^q exp C₂κ₁" evaluated with O₃, with C₁^{L1} the constant C₁ of Lemma 1's (1.36) (p.9 l.48–50) enlarged by the pp.8–9 factor 162, and with α₆′ := e^{−20.25}α₆ (the e^{20.25} of p.18); ε₂ is evaluated with the same constants, so C₃′ε₁ = 2(L+2)⁴O₃ε₂ ≤ e^{−5κ}. p.16's assumption "C₃ ≤ E₀C₁" (p.16 l.20) concerns the absolute C₃ of (1.39) (p.10 l.25–28).
    {#MD2.4.1.20-5} Conditions: L ≥ 3 (δ = 0 at L = 2); κ ≥ max(κ_vac, 3240A/(L−2)), which gives δκ ≥ κ/30 ≥ 65 ≥ 40.5 and 162e^{−4κ} ≤ min(δκ, log2); δκ/2 ≥ κ_{(1.26)} and e^{5κ} ≥ 8e^{20.25}O_{(1.26)} (p.20 l.6 bullet); (κ₁−2)/16 ≥ 1, implied by p.20's "½(κ₁−1) ≥ 2Lκ".
    {#MD2.4.1.20-6} All fit Bałaban's order (κ, then κ₁ and M, then the α's, then ε₁; p.21).
    {#MD2.4.1.20-7} Basis: every line of RG2 pp.7–21; the per-component bookkeeping through pp.19–20 is Bałaban's and is not redone here; [26] is not used.
    {#MD2.4.1.20-9} *From (10)(d):* (2.32), p.18, is false as printed (eight rods on the walls of one cube of Z₀∖Y₀ give d_k(Z₀) = Σ_id_k(Y_i) + 10); it holds with 18 in place of 4, so p.18's "(1/20)γ₂ε₁²/γ² ≥ 4κ" becomes "≥ 18κ" (a condition on γ) and p.20's adapted use with "½(κ₁−1) ≥ 2Lκ" becomes ½(κ₁−1) ≥ 9Lκ (a condition on κ₁).
    {#MD2.4.1.20-10} And p.20's "2(L+2)⁴O(1)ε₂exp5κ ≤ 1" pays (2.27)'s joins at scale k+1, whose cost is e^{5(1−7δ)½Lκ} per domain Z_i′, not e^{5κ}; so the condition this needs is 2(L+2)⁴O₃ε₂e^{5(1−7δ)½Lκ} ≤ 1, a condition on ε₁, imposed here.
    {#MD2.4.1.20-11} Both are in Bałaban's order of choices (p.21) and change no statement.
- {#MD2.4.1.21} *C₃′ε₁ (from the print, with the O₃ of RG2 Lemma 3's repair).* C₃′ε₁ = 2(L+2)⁴O₃·ε₂ (C₃ is defined from that factor in p.20's paragraph).
  {#MD2.4.1.21-1} So p.20's assumption, with O₃, gives C₃′ε₁ ≤ e^{−5κ}.
- {#MD2.4.1.22} *FV Thm 5.4, p.224 (Friedli–Velenik).* Assume (5.2), |δ(γ,γ′)| ≤ 1, and that there is a: Γ → ℝ_{>0} with Σ_{γ′}|w(γ′)|e^{a(γ′)}|δ(γ,γ′)| ≤ a(γ) for each γ (5.10).
  {#MD2.4.1.22-1} Then for all γ₁, 1 + Σ_{k≥2}kΣ_{γ₂,…,γ_k}|φ(γ₁,…,γ_k)|∏_{j≥2}|w(γ_j)| ≤ e^{a(γ₁)} (5.11).
  {#MD2.4.1.22-2} Here φ(γ₁) = 1 and φ(γ₁,…,γ_m) = (1/m!)Σ_{G connected}∏_{{i,j}∈G}δ(γ_i,γ_j).
  {#MD2.4.1.22-3} For a hard-core gas 1 + δ is the compatibility indicator, so δ ∈ {−1, 0}, (5.2) holds, and (1/m!)ρ^T∏H is φ∏w.
  {#MD2.4.1.22-4} The polymer set is finite on the torus.
- {#MD2.4.1.23} *CRE (2.38), p.261.* For cubes □ of size CM in Ω_j there is a gauge transformation u on □∩X with "U^u = exp iξA, L^nξ|A|, (L^nξ)²|∇^ξA| < BCMα_{0,n}".
  {#MD2.4.1.23-1} This is condition (ii) of the definition of Ũ^c_j(X, α̃₀, α̃₁), p.261: a domain condition with α_{0,n}, not a bound proportional to the deviation.
- {#MD2.4.1.24} *CRE pp.277–278.* "The factor H′(Z₀) is different; it is given by an integral with the integrand including, as one of the factors, a localized term from the expansion of the integrated function in the expectation value in (3.37).
  {#MD2.4.1.24-1} Although different, it satisfies the same bound as the other factors." And: "the terms 𝐄₀^{(k+1)}(Λ_{k+1},X,z) of this representation, for X ⊂ Λ_{k+1}, do not depend on Λ_{k+1}, and coincide with the corresponding terms arising from the expressions defined on the whole lattice, i.e. in the framework of [I]."
- {#MD2.4.1.25} *VAR (7), p.278, and Theorem 1, p.279.* (7): "|(∂V)(p′) − 1| < ε₁ for p′ ∈ 𝔅_k".
  {#MD2.4.1.25-1} Theorem 1: "for an arbitrary cube □ in the class described above, of a size 2ML^jη, M ≤ M(ε₁), there exists a gauge transformation u defined on a neighborhood of □ and such that on □, U^{u^{−1}} = e^{iηA}, |A| < B₃Mε₁(L^jη)^{−1}, |∇^ηA| < B₃Mε₁(L^jη)^{−2}".
  {#MD2.4.1.25-2} The bound is in the global ε₁ of (7).
- {#MD2.4.1.26} *VAR Proposition 9, p.309.* "The minimal configuration U_k(V) = U_k(V′V₀) in the axial gauge has an extension to an analytic function of G^c-valued small configurations V′ on 𝔅_k." "The function U_k(V′V₀)U_k(V₀)^{−1} transformed to the Landau gauge is, by the definition, equal to exp iη𝓗(B), where B = 1/i log V′." 𝓗 "is an analytic function of B, and also of the external gauge field configuration U", satisfies (19)–(21) with ε₂ = B₅ε₁, and its functional derivative (182) satisfies (190).

### (2) The Kotecký–Preiss Condition for Bałaban's Vacuum Gas {#MSD2.4.2}

- {#MD2.4.2.1} *Setting.* The polymers are the Z ∈ 𝐃_{k+1} on T for ℓ₀, and the Z ∈ 𝐃_{k+1} with Z ⊂ Λ_{k+1} on a labelled term ℓ.
  {#MD2.4.2.1-1} On a labelled term these are wall-connected unions of π_{k+1}-cubes with RG2's ζ: CRE p.277 expands the normalisation factor "in exactly the same way as in Sect. 7 [I]", by "(I.7.12), with terms given by (I.7.13), but with the localization domains Z_i ∈ 𝐃_k, X ∈ 𝐃_{k+1} having nonempty intersections with Λ_{k+1}", so "the larger class of localization domains" is the 𝐃_{k+1}-domains meeting Λ_{k+1} (RG2's numbering of [I]: Sect. 7 [I] is RG2 Sect. 2).
  {#MD2.4.2.1-2} *Index:* the quoted Z_i ∈ 𝐃_k are RG2 p.19's scale-k components of Z₀, and the X ∈ 𝐃_{k+1} are the polymers of (2.11)–(2.13) and of Lemma 3 (p.14: "X ∈ 𝐃_{k+1}"); the labelled-term polymer class is the second, the 𝐃_{k+1}-domains meeting Λ_{k+1}.
  {#MD2.4.2.1-3} On ℓ₀ the activities are RG2's, and Lemma 3 applies to them with the constants of RG2 Lemma 3's repair ((1)).
  {#MD2.4.2.1-4} On a labelled term they are the activities of the gas of CRE (3.27), with the source term, and the bounds below use:
  - {#MD2.4.2.2} *CRE p.279's same-way clause in the form (i′) (Bałaban's).* For t ∈ [0,1] and with the source term at full strength, the activities H(Z), Z ∈ 𝐃_{k+1}, Z ⊂ Λ_{k+1}, of the gas of (3.27) satisfy (2.38) with C₃′.
    {#MD2.4.2.2-1} Basis: CRE p.276, "The action in (3.29) differs only by the additional dependence on the field tA_k, but this was already taken into acount in the above considerations", with the analyticity space (3.43); p.277, "The differences, like the restriction of the integration to Λ_{k+1}, or the larger class of localization domains, do not matter"; p.279, "The other expectation values in (3.26), (3.28) are treated in exactly the same way".
    {#MD2.4.2.2-3} p.277 and p.279 do not name the source term, whose coefficient can be of size O(ε_k/g_k) near ∂Λ_{k+1} (D2.2(5)(b)); p.276 is the sentence that covers tA_k.
    {#MD2.4.2.2-4} It is the bound form of CRE p.279's same-way clause (D2.2(5)(b)).
  - {#MD2.4.2.3} RG2's numbering of [I] (CRE's "Sect. 7 [I]" is RG2 Sect. 2).
  - {#MD2.4.2.4} The polymers that meet Λ_{k+1}ᶜ are D2.6's. #(Z) := (LM)^{−4}|Z| is the number of π_{k+1}-cubes of Z. Lemma 3 is a bound for the analytic continuation on 𝐔^c_{k+1}(X,α₀,α₁) (p.15); every polymer's domain contains the common domain 𝐔^c_{k+1}(T,α₀,α₁), so everything below holds uniformly on it.
- {#MD2.4.2.5} *The gas.* By (2.10), H of a domain is the product over its components, and distinct components share no cube and no wall (RG1's connectedness is through walls).
  {#MD2.4.2.5-1} So (2.11) is the hard-core gas of the connected Z ∈ 𝐃_{k+1}, with Z ≁ Z′ iff ζ(Z,Z′) = 0.
- {#MD2.4.2.6} *(a) Linear size.* d_{k+1}(Z) ≥ #(Z)/162 − 1.
  - {#MD2.4.2.7} Rescale so that the cubes of π_{k+1} are unit cubes.
    {#MD2.4.2.7-1} Let 𝒯 be a shortest tree graph of RG1's class, of length ℓ = d_{k+1}(Z).
    {#MD2.4.2.7-2} A closed walk around 𝒯 runs along each edge twice and has length 2ℓ.
    {#MD2.4.2.7-3} Choose points p₀, …, p_N on it, consecutive ones at arc length ≤ 1, with N := ⌈2ℓ⌉ (one point if ℓ = 0).
  - {#MD2.4.2.8} Every point of 𝒯 is within arc length 1/2, hence within ℓ^∞-distance 1/2, of some p_i.
    {#MD2.4.2.8-1} Each cube of Z meets 𝒯, so it meets the closed ℓ^∞-ball B_i of radius 1/2 about some p_i.
  - {#MD2.4.2.9} B_i is a cube of side 1.
    {#MD2.4.2.9-1} In each coordinate a closed interval of length 1 meets at most 3 closed unit intervals of the partition, so B_i meets at most 3⁴ = 81 cubes.
    {#MD2.4.2.9-2} Hence #(Z) ≤ 81(N+1) ≤ 81(2ℓ+2).
- {#MD2.4.2.10} *(b) Activities.* With p.21's δ, (1−8δ)½L = L/10 + 4/5 ≥ 1 for L ≥ 2, and d ≥ 0, C₃′ε₁ ≤ e^{−5κ} ((1), RG2 Lemma 3's repair).
  {#MD2.4.2.10-1} So (2.38) with C₃′ and (a) give |H(Z)| ≤ e^{−5κ}e^{−κd_{k+1}(Z)} ≤ e^{−4κ}e^{−λ#(Z)}, λ := κ/162.
- {#MD2.4.2.11} *(c) Entropy.* At most 64^{n−1} connected Z with #(Z) = n contain a given cube.
  {#MD2.4.2.11-1} A closed depth-first walk from that cube along a spanning tree of the wall-adjacency graph of Z has 2(n−1) steps, each to one of the 8 wall-neighbours, and it determines Z.
- {#MD2.4.2.12} *(d) Incompatibility.* A wall lies in exactly two cubes.
  {#MD2.4.2.12-1} So Z′ ≁ Z iff Z′ contains a cube of Z⁺, the cubes of Z and their wall-neighbours, and |Z⁺| ≤ 9#(Z).
  {#MD2.4.2.12-2} The same holds for any union M of π_{k+1}-cubes in place of Z, with ≁ meaning ζ = 0.
- {#MD2.4.2.13} *(e) The condition.* Let b ≥ 0, w̃(Z) := H(Z)e^{b#(Z)}, a(Z) := c#(Z).
  {#MD2.4.2.13-1} By (b)–(d),
  {#MD2.4.2.14} Σ_{Z′≁M}|w̃(Z′)|e^{a(Z′)} ≤ 9#(M)·e^{−4κ}Σ_{n≥1}64^{n−1}e^{−(λ−b−c)n}.
  {#MD2.4.2.15} If λ − b − c ≥ log 128, the series is at most 2e^{−(λ−b−c)} ≤ 1/64.
  {#MD2.4.2.15-1} So the left side is at most (9/64)e^{−4κ}#(M).
  {#MD2.4.2.15-2} With
  {#MD2.4.2.16} c := (9/64)e^{−4κ},
  {#MD2.4.2.17} this is (5.10) for w̃ and a, and the same bound holds for every union of cubes M. The requirement is κ/162 ≥ b + c + 7 log2.
- {#MD2.4.2.18} *(f) The Kotecký–Preiss form of D2.4(2) (from Lemma 3 and, on labelled terms, CRE p.279's same-way clause in the form (i′)).* Take b := 9 log2, the weight d(Z) = 9 log2·#(Z) of the Kotecký–Preiss form of D2.4(2) (D2.2(5)(b) writes |Z| for the cube count #(Z)).
  {#MD2.4.2.18-1} This KP weight d(Z) is not the linear size d_{k+1}(Z).
  {#MD2.4.2.18-2} Since c ≤ 1, the requirement holds for
  {#MD2.4.2.19} κ ≥ κ_vac := 162(1 + 16 log2).
  {#MD2.4.2.20} Then Σ_{Z′≁Z}|H(Z′)|e^{a(Z′)+d(Z′)} ≤ a(Z) with a(Z) = c#(Z).
  {#MD2.4.2.20-1} This is the Kotecký–Preiss form of D2.4(2) with c fixed.
  {#MD2.4.2.20-2} It follows from Lemma 3 on ℓ₀, and, on a labelled term ℓ, for the subgas of the Z ∈ 𝐃_{k+1}, Z ⊂ Λ_{k+1}, from CRE p.279's same-way clause in the form (i′).
  {#MD2.4.2.20-3} Lemma 3 is used as printed, with RG2 Lemma 3's repair's enlarged absolute constants.
  {#MD2.4.2.20-4} On ℓ ≠ ℓ₀ the full gas also contains the polymers meeting Λ_{k+1}ᶜ (CRE p.277's domains "having nonempty intersections with Λ_{k+1}"), and KP for it needs D2.6's bound on those boundary polymers (CRE p.277 l.19–23's boundary-polymer bound, Bałaban's, WILSON_IT1_D26_CLOSURE_2026_10_24.md §2.4).
  {#MD2.4.2.20-5} So (ii) rests on Bałaban's Lemma 3 and CRE p.279's same-way clause in the form (i′).
- {#MD2.4.2.21} *(g) Consequence (from (5.11)).* For every union of cubes M,
  {#MD2.4.2.22} Σ_{𝒞≁M}|φ^T(𝒞)|e^{d(𝒞)} ≤ c#(M),
  {#MD2.4.2.23} the sum over the ordered clusters with some member ≁ M. By the symmetry of φ, a cluster with a member ≁ M is counted by putting that member first, which costs the factor k of (5.11).
  {#MD2.4.2.23-1} So the sum is at most Σ_{Z₁≁M}|w̃(Z₁)|(1 + Σ_{k≥2}kΣ|φ(Z₁,…,Z_k)|∏_{j≥2}|w̃(Z_j)|) ≤ Σ_{Z₁≁M}|w̃(Z₁)|e^{a(Z₁)} ≤ c#(M), by (5.11) and (e).
  - {#MD2.4.2.24} This is sharper than a(M⁺) ≤ 9c|M|, which also holds; D2.2(5)(e) uses c|M|.
    {#MD2.4.2.24-1} The restricted gases (activities H(Z)·1[Z compatible with 𝔐]) satisfy (5.10) a fortiori, so D2.2(5)(d)'s ratio formula holds with these constants.
- {#MD2.4.2.25} *The condition on κ (κ_D′ below, #MOMGD.37).* κ ≥ κ_vac is a lower bound on Bałaban's κ, of the kind RG2 p.21 imposes ("for κ sufficiently large").
  {#MD2.4.2.25-1} RG2 fixes κ before M (δ₀M ≥ κ, p.21) and ε₁ (p.20's assumption, p.21's "ε₁ sufficiently small"), so the bound can be imposed in his order of choices.
  {#MD2.4.2.25-2} It is added to his list of restrictions, not read into his text.
  - {#MD2.4.2.26} κ_vac is the vacuum part of (9)'s κ_D := max{κ_vac, ¼log(9/(2ν)), 3240A/(L−2)}.
  - {#MD2.4.2.27} The other conditions on κ used here: κ ≥ 3240A/(L−2) of RG2 Lemma 3's repair; p.20's "½(κ₁−1) ≥ 2Lκ"; p.18's "(1/20)γ₂ε₁²/γ² ≥ 4κ".
    {#MD2.4.2.27-1} All of them fit the order κ → κ₁, M → ε₁ → γ: each bounds κ by a constant, or a later constant by κ.
- {#MOMGD.37} *The choices.* Bałaban's κ satisfies κ ≥ κ_D′ := max{κ_vac′, ¼log(9/(2ν)), 3240A/(L−2), κ_pc}, which is κ_D of #MD2.4.3.9-1 with κ_vac′ of #MD2.4.12.33 in place of κ_vac and with κ_pc of #MD2.4.12.33-1 added, as (12)(e)–(f) and (13)(d) use it. D2 takes β₀ ≤ 1/2 and L ≥ L₀ = 5000, under which D2.4(6)'s (1+β₀)⁸ < L holds (1.5⁸ < 26), and (q₀ = q₁ > p₀) of SW closure §2, which gives #MD2.4.6.9-1's q₀ ≤ q₁.

### (3) The Size Count σ_{k+1} and the Weights θ_{k+1} {#MSD2.4.3}

- {#MD2.4.3.1} *Definition (D2.4(12)(a)).* For a step-(k+1) group 𝒢 (D2.2(6)(d)) let n_{k+1}(𝒢) be the number of step-(k+1) traversals of C in I(𝒢), and #_{k+1}(𝒢) the number of π_{k+1}-cubes of the domains of 𝒢's constituents (marked vacuum domains, slot supports, the supports of the vacuum-link clusters, the domains of the old groups) and of the members of its merged old occurrences, counted with multiplicity.
  {#MD2.4.3.1-1} Put
  {#MD2.4.3.2} σ_{k+1}(𝒢) := #_{k+1}(𝒢) + n_{k+1}(𝒢)/M ((12)(a)).
  - {#MD2.4.3.3} V4's σ(W) = n(W) + |ℋ(W)|/(LM) ((c4-6-1)) has a cube count n(W) and the hull in units of the cube side LM; n(W) is a cube count, not a traversal count ((12)(a)).
    {#MD2.4.3.3-1} At step k+1 the vacuum weight of a group is proportional to the volume of its marked domains ((5)(d) of D2.2, (g) above), and these domains are 4-dimensional, so σ_{k+1} counts cubes, with the arc in cube sides as in V4.
  - {#MD2.4.3.4} The decay statements survive.
    {#MD2.4.3.4-1} Where the support of 𝒢 is wall-connected, two of its cubes are at step-(k+1) distance at most M·#_{k+1}(𝒢), so the envelope form σ ≥ dist/(C_FM) holds there.
    {#MD2.4.3.4-2} Where 𝒢 is linked along C, n_{k+1} gives it.
- {#MD2.4.3.5} *The weight.* θ_{k+1}(𝒢) := θ_vac(𝒢) + θ_ref(𝒢).
  - {#MD2.4.3.6} θ_vac(𝒢) := Σ_MΣ_{𝒞≁M}e^{d(𝒞)}|φ^T(𝒞)|, the sum over the marked domains M of 𝒢: the sup over the domain of the summand of D2.2(6)(c)'s θ(G), which (6)(c) evaluates at the reference point (1, 0, 0).
    {#MD2.4.3.6-1} By (2)(g), θ_vac(𝒢) ≤ c#_{k+1}(𝒢) ≤ cσ_{k+1}(𝒢).
  - {#MD2.4.3.7} θ_ref(𝒢) is the reference-gas weight of (7): what |Q_{k+1}(D)| = |S°^{[D]}(ℓ)/S°(ℓ)| costs per group of D.
- {#MD2.4.3.8} *The requirement θ_{k+1} ≤ νσ_{k+1}/16, split as ν/32 + ν/32.*
  - {#MD2.4.3.9} θ_vac: c ≤ ν/32, i.e. (9/64)e^{−4κ} ≤ ν/32, i.e. κ ≥ ¼log(9/(2ν)).
    {#MD2.4.3.9-1} With (1)–(2): κ ≥ κ_D := max{κ_vac, ¼log(9/(2ν)), 3240A/(L−2)}.
  - {#MD2.4.3.10} *Which constants ν depends on.* V4 sets ν := η, "the reserve constant of Section c4-6-2" (Lemma c5-5-8), with η chosen after the fixed constants so that 1000ηA_s < ϖ/8, A_s = 1 + A_h (Lemma c4-8-2(c)); ϖ is any number with 0 < ϖ ≤ min(1/16, λ_*/(64C_g)) ((c4-8-3)), λ_* the decay rate of the root weights, |k^f_ξ(Z)| ≤ ε_*e^{−λ_*ℓ₁(Z)} (Lemma activity-bounds).
    {#MD2.4.3.10-1} Bałaban's order fixes κ before M and ε₁; ν is an absolute number (#MOMGD.14-5), so it fits that order.
    - {#MD2.4.3.11} *Notation.* In this bullet C_g and δ are V4's (C_g = 162, δ = 1/40, app:mayer-constants), not (4)'s (LPG′) constant C_g or RG2's δ of (1).
    - {#MD2.4.3.12} *ϖ.* V4 app:mayer-constants: "Fix, in this order and depending on L and the group only: C_g=162 and δ=1/40; a decay rate κ≥3 with" δκ ≥ 2C_g log 128, λ′ = (1−5δ)Lκ/2049 and λ_* = λ′ − 2C_g ≥ 2C_g log 128 ((c2-kappa-choice)).
      {#MD2.4.3.12-1} So λ_* depends on L and κ only, and λ_*/(64C_g) ≥ (log 128)/32 > 1/16 for every admissible κ.
      {#MD2.4.3.12-2} Hence ϖ := 1/16 satisfies (c4-8-3) for every κ, and the condition on η is 1000ηA_s < 1/128.
      {#MOMGD.14} *A_h is absolute.* V4 Lemma c4-8-2(b) states |H_γ| ≤ A_hLMn_γ with A_h "fixed before the coupling", and its proof derives it "from the square geometry and the wall connectivity of a component's domains"; the contacts of γ lie within 2L of X_γ (V4 Lemma c4-6-env: the initial vertex of a traversal in contact with D is within 2L of D).
      {#MOMGD.14-1} So X_γ is a union of at most n_γ distinct LM-cubes, wall-connected (incompatible domains share a cube or a wall, V4 app:domain-geometry; corner contact is the footprint convention of sec:c4-12-4 and is not needed here), hence of maximum-norm diameter < n_γLM; the contact set 𝖳_γ lies within 2L ≤ LM/4 of it (M ≥ 8), so its diameter is D ≤ 2n_γLM; and the square geometry of sec:extent-weights (an arc of length ≤ 4D + 1 contains contacts of diameter D < s/2;
      {#MOMGD.14-2} otherwise the whole contour, of length 4s ≤ 8D) gives |H_γ| ≤ 8D + 1 ≤ 17n_γLM, and likewise the contour distance d_C(a, a′) from a ∈ H_γ to a contact a′, which lem:c4-8-2(b) also bounds by A_hLMn_γ: d_C ≤ |H_γ| for a short hull and ≤ n_C/2 = 2s ≤ 4D for the whole contour.
      {#MOMGD.14-3} So A_h := 17 serves, an absolute constant; A_x is bounded the same way (the distance from a contact to a cube of X_γ, halos included, is ≤ 2n_γLM + 2R_h with R_h the halo radius; M ≤ R_h < 4M, since the hosts are rectangles of at most 4 M-cubes per direction (V4 eq:part1-potential-host, eq:c-probe-host), so 2R_h < 8M < LM for L > 11 and A_x ≤ 3).
      {#MOMGD.14-4} The halo index bound R_e of lem:c4-6-env (R_e = ⌈2max(R_h, L)/(LM)⌉ = 1) enters the envelope constants A_E, A_F, A′_E (hence V4's C_F := A_E, Lemma c5-5-8), the footprint pin's constant C, and the threshold CρLM ≤ η/8 on g₀, not A_h or η.
      {#MOMGD.14-5} Hence, with A_h := 17, A_s = 18, and ϖ := 1/16 (#MD2.4.3.12-2), the only condition on the reserve η is 1000ηA_s < ϖ/8, met by η := 1/2 400 000 (V4 app:thresholds lets η depend on L, M, and κ; an absolute choice is within that clause); so ν = η and κ_D′'s term ¼log(9/(2ν)) are independent of κ, M, and ε₁, and the order of choice (κ before M and ε₁) holds.
  - {#MD2.4.3.13} θ_ref ≤ νσ_{k+1}/32: (7), with the sizes in D2.4(12)(f), by the Kotecký–Preiss condition for the reference gas with a° = (ν/32)σ_{k+1} and FV Lemma 5.6, (5.17) (p.226) (#MD2.4.12.51).
- {#MD2.4.3.14} *The old weights do not accumulate.* The bound ν_n^{(k)} = Σ_{W∋n}e^{θ_k(W)}‖Y_W‖ of D(k)(ii) already contains e^{θ_k(W)}.
  {#MD2.4.3.14-1} So when an old insertion enters a new group, its factor e^{θ_k(W)}|Q_k|-share is paid inside the group's size by ν_n^{(k)} ((4), (7)). θ_{k+1} is the fresh weight of the step-(k+1) gas.
  {#MD2.4.3.14-2} It is not θ_k converted to step-(k+1) units, which would grow by a factor L per step.
  - {#MD2.4.3.15} *Role of θ_vac in D2.3(3)'s cluster form.* The vacuum occurrences are merged into the groups, and Q^{out}_{k+1} carries only the reference-gas Φ°.
    {#MD2.4.3.15-1} So θ_vac does not bound an interaction between groups: it bounds the vacuum clusters merged into 𝒢 (the factor paid inside S_𝒢), and θ_ref bounds 𝒢's share of Q^{out}.

### (4) The Deviation Factor {#MSD2.4.4}

{#MD2.4.4.1} The object is Y^d_𝒢 = Y_𝒢 − c_𝒢T_𝐔(I(𝒢)) of D2.3(2), for a step-(k+1) group 𝒢 with support X(𝒢).
- {#MD2.4.4.2} *The support.* X(𝒢) is the union of the π_{k+1}-cubes that meet the constituents' domains (#MD2.4.3.1), the domains of the members of its merged old occurrences, the comparison boxes of its old insertions, its slots, or the bonds of its arc I(𝒢).
  {#MD2.4.4.2-1} The arc must be included: Y_𝒢 and T_𝐔(I(𝒢)) depend on 𝐔 along all of I(𝒢) (D2.1(4) *Locality*; D2.2(6)(d), the 𝐔-transports between consecutive slots), and I(𝒢) can leave every constituent domain (D2.2(6)(d): "a second-rule merge also covers the gap").
  {#MD2.4.4.2-2} The members' domains must be included too. Y_𝒢 depends on 𝐔 only on the constituents' domains and I(𝒢), the occurrences entering as scalars (#MD2.2.6.123-2), but 𝒢 and 𝒢′ are incompatible when an occurrence of one hits a member of the other (#MD2.3.3.6). So the positions of 𝒢 (#MD2.4.12.38-1, #MD2.4.12.51-4) and ext_{k+1}(𝒢) (#MD2.4.12.6), which the next step's Γ-vertices take over their members' supports (#MD2.4.12.17, #MD2.4.12.19-2), must cover them.
  {#MD2.4.4.2-3} (4) needs of X(𝒢) only that it contains the set on which Y_𝒢 depends (#MD2.4.4.15), that it is closed-connected (#MD2.4.4.3, #MD2.4.4.8-3), and the count #MD2.4.4.4-1, where #_{k+1}(𝒢) counts the members. (H) and its failure branch are stated through ℓ_{X(𝒢)} (#MD2.4.4.12, #MD2.4.4.12-2), and (S) is proved with the covering lemma's count, which includes the members (#MD2.4.12.19-2).
  - {#MD2.4.4.3} *X(𝒢) is connected as a closed set.* The cubes meeting I(𝒢) form a closed-connected chain, since I(𝒢) is a connected path.
    {#MD2.4.4.3-1} Each constituent meets I(𝒢): an s-component contains bonds of C or meets an old domain that contains its interval; a marked polymer contains its slot; a vacuum link's support meets its marked polymer's domain (#MD2.4.12.15); a comparison box contains its traversal. The domain X_W of an old group or of a member W of a merged occurrence contains W's interval (#MD2.2.4.3), which lies in I(𝒢) (#MD2.3.3.5-1, #MD2.0.3.7).
    {#MD2.4.4.3-1-1} Each X_W is closed-connected to I(𝒢) within X(𝒢). For k ≥ 2, X_W is a closed-connected union of π_k-cubes by (4) at step k, and the π_{k+1}-cubes meeting a closed-connected set form a closed-connected family. For k = 1, each component of W's root/cluster graph has a wall-connected union of domains, and its contacts lie on W's hull ℋ(W), W's interval, within 2L fine units of that union (#MD2.4.12.7-1-2, #MD2.4.12.7-1-3), less than the π₂-side. So the π₂-cubes meeting that union form a closed-connected family, one of which touches a π₂-cube meeting ℋ(W).
    {#MD2.4.4.3-2} So every cube of X(𝒢) is closed-connected to the chain.
  - {#MD2.4.4.4} *Count.* A closed step-(k+1) bond meets at most 2⁴ = 16 cubes of π_{k+1} (at most 2 intervals of the partition in each coordinate, the cubes having side M ≥ 1).
    {#MD2.4.4.4-1} So #(X(𝒢)) ≤ #_{k+1}(𝒢) + #(boxes) + 16n_{k+1}(𝒢), and ℓ_{X(𝒢)} ≤ 2#(X(𝒢)) by the bounds below.
    {#MD2.4.4.4-2} (S) pays for this through ℓ_{X(𝒢)}, as set up there.
- {#MD2.4.4.5} *Scope.* D(k+1)(ii) needs a bound by the deviation of U_{k+1} near X(𝒢) (D2.0(5)(c), "Needs D2.4").
  {#MD2.4.4.5-1} Here k+1 ≥ 2.
  {#MD2.4.4.5-2} A step-(k+1) group is dev iff it has no inherited attached member, its set lifts, and it passes the D2.6 closure 2.1's tests: no polymer component or member's domain meets the one-layer neighbourhood of Λ_{k+1}ᶜ, its polymers and arc lie in Ω_k, its polymers carry no boundary-type potential, and 𝒬_{n′}(𝒢)^{∼5} ⊂ Ω_{k+1} for every traversal n′ (𝒬 as below). Otherwise it takes its species from #MD2.0.3.22–#MD2.0.3.25-1, with D2.6's bound.
  {#MD2.4.4.5-3} A group passing the first test does not depend on ω′ (D2.6 closure 2.1), so ω′ = 0 below.

- {#MD2.4.4.6} *The local deviation (region per traversal, SW closure §5(e)).* For X a union of π_{k+1}-cubes put ℓ_X := d_{k+1}(X) + 1, with RG1's linear size d_{k+1} ((1)); diam_∞(X) ≤ M(d_{k+1}(X) + 2) ≤ 2Mℓ_X.
  {#MD2.4.4.6-1} For a group 𝒢 and a traversal n′ of its arc I(𝒢) ⊂ X(𝒢), let t = t_{n′}(𝒢) be the least t ≥ 1 with X(𝒢) ⊂ B_∞(n′, R_t^{(k+1)}), R_t^{(k+1)} = C_boxM(t+1) (#MD2.0.3.12-1), and 𝒬 = 𝒬_{n′}(𝒢) the smallest union of π_{k+1}-cubes containing B_∞(n′, R_t^{(k+1)}) (a cube of side ≤ 2R_t^{(k+1)} + 2M).
  {#MD2.4.4.6-2} Put Dev_{n′}(𝒢; U) := ℓ_{X(𝒢)}·E_𝒬(U), E_𝒬(U) := max{η_{k+1}^{−2}δ_p(U) : p a fine plaquette in 𝒬^{∼5}}, in the normalisation of δ*^{(k+1)} (D2.0(3)).
  {#MD2.4.4.6-3} The region must be contractible: for a ring X of cubes with flat plaquettes on X⁺ and curvature inside the ring, a bound by the deviation on X⁺ alone would force A = 0 while the holonomy around the ring is not 1 (SW closure §5(e)). 𝒬^{∼5} ⊂ B_∞(n′, R_{t+1}^{(k+1)}) for C_box ≥ 6.
  - {#MD2.4.4.7} With ℓ_X := d_{k+1}(X), Dev would vanish for one cube and for the 16 cubes at a vertex ((1)), and (LPG′) would force U_{k+1} to be pure gauge there.
    {#MD2.4.4.7-1} The +1 removes this.
  - {#MD2.4.4.8} *Bounds.* ℓ_X ≥ 1, and ℓ_X ≥ #(X)/162 by (2)(a).
    {#MD2.4.4.8-1} If X is wall-connected, ℓ_X ≤ #(X): order its cubes so that each meets an earlier one in a wall.
    {#MD2.4.4.8-2} A point of the tree in that earlier cube is within distance 1 of the wall, so one segment of length ≤ 1 inside the two cubes adds the new cube, and d_{k+1}(X) ≤ #(X) − 1, as in (2.30)'s right side.
    {#MD2.4.4.8-3} If X is only connected as a closed set, the same argument through a shared vertex, at distance ≤ √d = 2 from every point of the earlier cube (the tree's length is arc length, (2)(a)), gives d_{k+1}(X) ≤ 2(#(X) − 1), so ℓ_X ≤ 2#(X).
  - {#MD2.4.4.9} In (S) and (6), ℓ is this ℓ_X.
- {#MD2.4.4.10} *(LPG′), the local proportional gauge (WILSON_IT1_SW_CLOSURE_2026_10_24.md §5).* For every V_{k+1} in the support of the term's indicators, every dev group 𝒢 and every traversal n′ of I(𝒢), with 𝒬 = 𝒬_{n′}(𝒢), 𝒬^{∼5} ⊂ Ω_{k+1}, E := E_𝒬(U_{k+1}) and M_𝒬 := half the side of 𝒬^{∼2} rounded up to a multiple of R₁M₁ (M_𝒬 ≤ (2C_box + 6)Mℓ_{X(𝒢)}), under (H): 2E ≤ min(a₁, c₂), 2M_𝒬E ≤ R₁M₁a₁, there is a gauge transformation u on a neighbourhood of 𝒬^{∼2} with U_{k+1}^u = e^{iη_{k+1}A} on 𝒬^{∼2} ⊇ X(𝒢) and,
  {#MD2.4.4.10-1} in the units of CRE (2.38)–(2.39) at n = k+1,
  {#MD2.4.4.11} |A|, |∇^ξA|, |∂^{ξ*}∂^ξA|, |Δ^ξA| ≤ 3B₃M_𝒬E ≤ C_g·Dev_{n′}(𝒢; U_{k+1}), C_g := 3B₃(2C_box + 6)M, and |R(u)J_{k+1}| ≤ (4/3)C_gDev_{n′}(𝒢; U_{k+1}) in the units of (2.36) (RG1 (1.8), (3.12)),
  {#MD2.4.4.12} with C_g depending on B₃, C_box, M only. M_𝒬 ≤ R_t^{(k+1)} + 3M + R₁M₁ ≤ (2C_box + 6)Mℓ_{X(𝒢)} (SW closure §5): 𝒬^{∼2} has side ≤ 2R_t^{(k+1)} + 6M; R_t^{(k+1)} ≤ max(2C_boxM, 2Mℓ_{X(𝒢)} + C_boxM) ≤ 2C_boxMℓ_{X(𝒢)}, since t ≥ 1, diam_∞X(𝒢) ≤ 2Mℓ_{X(𝒢)} (#MD2.4.4.6) and ℓ_{X(𝒢)} ≥ 1; and R₁M₁ ≤ M by (C-M). At ℓ_{X(𝒢)} = 1, t = 1 and R_1^{(k+1)} = 2C_boxM, so the factor 2 is needed.
  {#MD2.4.4.12-1} Inputs: CRE (3.17) at 𝒬 (its first line at 𝒬 is SW §5(2); its second is VAR Prop. 9, p.309), the argument's bound 22d²E localised by CMP98 Prop. 2's locality (p.26), 𝐇_𝒬 ≤ C_H·22d²E ≤ E with its derivatives (VAR (190) at the distance 2M − 2LM₁ from 𝒬^{∼2} to the argument's support, SW §5(4); p.268's factor e^{−δLM₂R_{k+1}} belongs to the partition cubes and does not apply at 𝒬), VAR Thm 1 (p.279) for the local minimiser with ε₁ = 2E (SW §5(5); CMP98 Prop. 2; the lifting of VAR p.279; CRE p.267's "coefficient 1"), condition (C-M) on M, M₁, M₂, R₁^V, L, and (C-H) 22d²C_H ≤ 1, a condition on M.
  {#MD2.4.4.12-2} When (H) fails, C_gDev ≥ c₀ᾱ_{k+1} for g_K small and the Cauchy step below is in its trivial branch.
- {#MD2.4.4.13} *The Cauchy step (given (LPG′)).* Put ᾱ_{k+1} := min(α_{0,k+1}, α_{1,k+1}) and f(z) := Y_𝒢(e^{izη_{k+1}A}, zR(u)J_{k+1}, 0) − c_𝒢T_{e^{izη_{k+1}A}}(I(𝒢)).
  - {#MD2.4.4.14} f(0) = Y_𝒢(1, 0, 0) − c_𝒢𝟙 = 0, by Schur (D2.3(2)).
  - {#MD2.4.4.15} By covariance (D2.2(6)(b)) and since Y_𝒢 depends on 𝐔, 𝐉 only on X(𝒢), which contains the arc (D2.3(4), contour locality, and Bałaban's localisation), f(1) = π(u(x))Y^d_𝒢(U_{k+1}, J_{k+1}, 0)π(u(x′))^{−1}, with x, x′ the ends of I(𝒢). π(u) is unitary, so ‖f(1)‖ = ‖Y^d_𝒢(U_{k+1}, J_{k+1}, 0)‖.
  - {#MD2.4.4.16} For |z| < R_X := c₀ᾱ_{k+1}/(C_gDev_{n′}(𝒢; U_{k+1})), with c₀ a constant depending on d and L only (the domain also contains the curvature conditions (2.34)–(2.35) for e^{izηA} and its averages, |∂e^{iξA} − 1| ≤ C(ξ²|∇A| + ξ²|A|²), and (2.37) for the averaged 𝐉, which is a function of the configuration alone; the averages follow from the plaquette bound by RG1 p.263 (1.17) and (K3) (#MOMGD.5), with C_av = 2(B₃ + 2c_dB₅) in c₀; the 4/3 of the 𝐉 radius absorbed in c₀), (LPG′) puts (zA, zR(u)J_{k+1}) in D(k+1)(iii)'s domain at the reference background 1.
    {#MD2.4.4.16-1} So f is analytic there, by the reference clause (D2.3(2)).
  - {#MD2.4.4.17} Let S_𝒢 be the supremum of ‖Y_𝒢‖ + |c_𝒢|‖T_𝐔(I(𝒢))‖ over D(k+1)(iii)'s domain about the real points of the support, together with the reference-clause domain.
    {#MD2.4.4.17-1} If R_X > 1, Schwarz's lemma gives ‖f(1)‖ ≤ S_𝒢/R_X.
    {#MD2.4.4.17-2} If R_X ≤ 1, then ‖f(1)‖ ≤ S_𝒢 ≤ S_𝒢/R_X.
    {#MD2.4.4.17-3} In both cases
    {#MD2.4.4.18} e^{θ_{k+1}(𝒢)}‖Y^d_𝒢(U_{k+1})‖ ≤ b_𝒢Dev_{n′}(𝒢; U_{k+1}) for every traversal n′ of I(𝒢), b_𝒢 := (C_g/(c₀ᾱ_{k+1}))e^{θ_{k+1}(𝒢)}S_𝒢.
  - {#MD2.4.4.19} This is the per-insertion form of (5), at the real point U_{k+1}.
  - {#MD2.4.4.20} *Complex data (on 𝒟_{k+1}^{sub}; SW closure §6(6b)).* D(k+1)(iii)'s dev clause at 𝐔 = e^{iηa′}U_{k+1}, 𝐉, for a′ in the sub-domain of D2.0(3) (the 𝐉-term bullet): the same Cauchy step on z ↦ Y(e^{izηa″}e^{izηA}, z(R(u)J_{k+1} + (𝐉 − J_{k+1})), 0) − c_𝒢T with a″ := Ad(u)a′ (𝐔^u = e^{iηa″}e^{iηA}, so f(1) needs no BCH correction), radius c₀ᾱ_{k+1}/(C_gDev_{n′}(𝒢) + ‖a″‖_{sub} + ‖𝐉 − J‖_{sub}), gives e^{θ}‖Y^d_𝒢(𝐔, 𝐉)‖ ≤ b_𝒢(Dev_{n′}(𝒢) + a*_𝒢 + j*_𝒢) with a*_𝒢 ≤ α_{1,k+1}/C_g, j*_𝒢 ≤ 2α_{0,k+1}/C_g;
    {#MD2.4.4.20-1} summed by (S-w), Σ_{𝒢∋n′}e^θ‖Y^d_𝒢(𝐔,𝐉)‖ ≤ C_χρ̃_{k+1}δ*^{(k+1)}_{n′}(U_{k+1}) + 3C_χρ̃_{k+1}α_{1,k+1}Σ_tw_t, the second term O(ρ_{k+1}) under q₀ = q₁.
- {#MD2.4.4.21} *From the per-insertion form to D(k+1)(ii) (given (LPG′) and (7); SW closure §6(6a)).* With t(𝒢) = t_{n′}(𝒢) as above (containment), Dev_{n′}(𝒢) ≤ ℓ_{X(𝒢)}η_{k+1}^{−2}Δ^{(k+1)}_{n′}(R^{(k+1)}_{t(𝒢)+1}), for 𝒬_{n′}(𝒢)^{∼5} ⊂ Ω_{k+1} (C_box ≥ 6), since Δ^{(k+1)} takes only plaquettes of Ω_{k+1}.
  {#MD2.4.4.21-1} The dev species and (LPG′) are taken for such groups only; a group with 𝒬_{n′}(𝒢)^{∼5} meeting Ω_{k+1}ᶜ for some n′ is att(k+1, Z) (#MD2.0.3.23; D2.6 closure 2.1(a)), with D2.6's bound.
  {#MD2.4.4.21-2} If the sizes satisfy
  {#MD2.4.4.22} (S) Σ_{𝒢∋n′, t(𝒢)=t}e^{θ_{k+1}(𝒢)}S_𝒢ℓ_{X(𝒢)} ≤ C_Sρ_{k+1}w_t for every t,
  {#MD2.4.4.23} then Σ_{𝒢∋n′}e^{θ_{k+1}(𝒢)}‖Y^d_𝒢‖ ≤ (C_gC_S/c₀)e^{η_w}(ρ_{k+1}/ᾱ_{k+1})δ*^{(k+1)}_{n′}(U_{k+1}) (w_t ≤ e^{η_w}w_{t+1}, η_w = (5/16)η_V).
  {#MD2.4.4.23-1} (S) is the size statement of (7); it holds as (S-w), (13)(d), with the rate comparison of (13)(a).
- {#MD2.4.4.24} *The locality of (LPG′).* It is CRE (3.17): U_{k+1} = (e^{iξ𝐇_𝒬}U_{k+1,𝒬})^{u^{−1}} on 𝒬^{∼2}, with 𝐇_𝒬 exponentially small by (190) and the local minimiser bounded by VAR Theorem 1 in the local ε₁ (SW closure §5).
- {#MD2.4.4.25} *At k = 1 (step 1 → 2)* the old dev bound is IT-1's D1(ii), and the sup-only domain of D(1)(iii) needs no gradient bound.
  {#MD2.4.4.25-1} (LPG′) is needed for the groups made at steps k+1 ≥ 2.

### (5) The Amendment of D(k)(ii) {#MSD2.4.5}

- {#MD2.4.5.1} *The dev constant.* For k ≥ 2 the first term of D(k)(ii) becomes C_χρ̃_kδ*^{(k)}_n, with ρ̃_k := ρ_k/ᾱ_k, ᾱ_k := min(α_{0,k}, α_{1,k}), and ρ̃_1 := ρ_1.
  {#MD2.4.5.1-1} The factor 1/ᾱ_{k+1} of (4) is the Cauchy factor of the domain's radius, and S_𝒢 is of size ρ_{k+1} under (S) ((7); it holds as (S-w), (13)(d)).
  {#MD2.4.5.1-2} So the amendment is forced by the Cauchy route of (4), not by a choice.
- {#MD2.4.5.2} *Sizes on the support are unchanged in order.* On the support, δ*^{(k)}_n(U_k) ≤ 2c_σB₃ε_kΣ_tw_t (D2.0(3)(b)).
  {#MD2.4.5.2-1} So ρ̃_kδ*_n ≤ Cρ_kε_k/ᾱ_k, and ε_k/α_{i,k} = (A₀/C_i)(log ĝ_k^{−2})^{p₀−q_i} ≤ (A₀/C_i)(log g_k^{−2})^{p₀−q_i} ≤ A₀/C_i under (q₀ = q₁ > p₀) of (12)(f), for g_K small, since ĝ_k ≤ g_k (#MD2.0.1.7).
  {#MD2.4.5.2-2} Hence ν_n^{(k)} = O(ρ_k) on the support, as before.
- {#MD2.4.5.3} *At complex data* (D(k)(iii)) the dev term carries δ*^{(k),c}_n + a*^{(k)}_n(A′), and ρ̃_ka*_n(A′) ≤ Cρ_kα_{1,k}/ᾱ_k = Cρ_k·max(1, (C₁/C₀)(log ĝ_k^{−2})^{q₁−q₀}); the same bound holds for j*_n(𝐉), since |𝐉 − J_k|/r_J < 2.
  {#MD2.4.5.3-1} So the complex-data size gains the factor max(1, λ_R(log ĝ_k^{−2})^{q₁−q₀}) ≤ λ_R(1 + (log ĝ_k^{−2})^{(q₁−q₀)₊}), with λ_R = C₁/C₀ = K_RLM + 1 ≥ 1 fixed after L and M (the two-loop note's #14; table #T2.24), of the same kind as ρ^c_{ph,k}'s.
  {#MD2.4.5.3-2} This is the complex-data tolerance of (0) for the dev term only.
  {#MD2.4.5.3-3} This is the size of the right side away from older layers (next bullet); the clause itself holds on the sub-domain for new groups ((4) *Complex data*) and for carried insertions about U_{k+1} (SW closure §6(6c), given (T-dev)).
  {#MD2.4.5.3-4} It is λ_R times a power of log g_k^{−2}, of the kind D2.0(3)(iii) records for ρ^c_{ph,k}, and D(k)'s consumer tolerates that power (#MD2.4.9.10-2).
  - {#MD2.4.5.4} *Older layers (sub-domain form, SW closure §3).* On the full domain, D(k)(iii) allows |η_kA′| < α_{1,m}L^{−m} per fine bond on Ω_m∖Ω_{m+1}, m < k, so a* and j* would pick up L^{k−m}α_{1,m}, and CRE p.256 lets such a layer lie within about 2M₁ of n.
    {#MD2.4.5.4-1} The bound above is therefore asserted on the sub-domain 𝒟_k^{sub} of D2.0(3) (the top-layer radii on every layer), where a*, j* ≤ 3S₃₀α_{1,k} on every layer; the only consumer, (11)(c)(β)'s polydisc points, lies inside it by the chain condition with CRE p.277's 𝐇-decay (O(1)Lθ ≤ (1−β)/min(β,1)).
- {#MD2.4.5.5} *The per-insertion form.* Each dev insertion carries its own bound at the real evaluation points: e^{θ(W)}‖Y_W(U_k, J_k)‖ ≤ b_W·Dev_{Q^#_W}(U_k), with Q^#_W its comparison box.
  {#MD2.4.5.5-1} Dev_{Q^#_W} uses the plaquettes of (Q^#_W)⁺, and these are the comparison box of D2.0(3)'s reclassification rule.
  {#MD2.4.5.5-2} At step 1 (Q^#_W)⁺ := Q_W, so that its plaquettes lie in Λ₁; for a new group Q^#_𝒢 := X(𝒢) of (4).
  {#MD2.4.5.5-3} The reclassification of (6)(ζ) sorts insertions by where Q^#_W lies.
  {#MD2.4.5.5-4} That needs a bound per insertion.
  {#MD2.4.5.5-5} At step 1 the form holds by V4's group bounds (IT-1 note §3a); at step k+1 it is (4)'s, given (LPG′).
- {#MD2.4.5.6} *Normalisation.* Dev_{Q^#_W}, ℓ_W := ℓ_{Q^#_W} and b_W stay in the normalisation of the step j(W) at which W was made, as θ and σ do for carried att groups (D2.0(3), "Units of carried groups").
  {#MD2.4.5.6-1} Only δ* is converted from step to step ((6)(γ)).
- {#MD2.4.5.7} *The tail clause (ii-t) (part of D(k)(ii)).* Put β_W := b_Wℓ_Wη_{j(W)}^{−2}, so that b_WDev_{Q^#_W}(𝐔) = β_W·max{δ_p(𝐔) : p in (Q^#_W)⁺}.
  {#MD2.4.5.7-1} Let t^{(k)}(W) be the least t ≥ 1 with (Q^#_W)⁺ contained in the step-k R_t^{(k)}-neighbourhood of n (containment: the Abel step and (6)(ζ) use it), and W_t := Σ_{t′≥t}w_{t′}.
  {#MD2.4.5.7-2} The clause is
  {#MD2.4.5.8} (ii-t) Σ_{dev W∋n, t^{(k)}(W)≥t}β_W ≤ C_χρ̃_kη_k^{−2}W_t for every t ≥ 1 and every traversal n (the sum over dev W).
  - {#MD2.4.5.9} *It gives the sum form.* For dev W, (Q^#_W)⁺ ⊂ Ω_k, so b_WDev_{Q^#_W} ≤ β_WΔ_t with Δ_t := Δ^{(k)}_n(R_t^{(k)}) at t = t^{(k)}(W), and Δ_t is nondecreasing in t.
    {#MD2.4.5.9-1} With B_t := Σ_{W∋n, t^{(k)}(W)≥t}β_W, Abel summation gives Σ_{W∋n}b_WDev_{Q^#_W} ≤ Σ_tΔ_t(B_t − B_{t+1}) = Δ_1B_1 + Σ_{t≥2}(Δ_t − Δ_{t−1})B_t ≤ C_χρ̃_kη_k^{−2}Σ_tΔ_t(W_t − W_{t+1}) = C_χρ̃_kδ*^{(k)}_n.
    {#MD2.4.5.9-2} So (ii-t) is the class statement and the sum form is its consequence.
  - {#MD2.4.5.10} *At step 1 (from IT-1 note §3a(6)).* For a good group, ‖Υ⁰_W‖ ≤ K_χ𝔡⁰_W with 𝔡⁰_W ≤ C_χ𝔰(W)³δ_{Q_W}(U₁)M^{(ρ)}_Λ(W) (§3a(3)), and e^{θ°(W)} ≤ e^{η𝔰/8} (η = η_V, the IT-1 note's notation).
    {#MD2.4.5.10-1} So β_W ≤ K_χC_χe^{η𝔰/8}𝔰³M^{(ρ)}_Λ(W).
    {#MD2.4.5.10-2} Q_W lies within C_boxLM𝔰 of n_f, so t(W) ≤ max(1, ⌊𝔰⌋).
    {#MD2.4.5.10-3} §3a(6)'s split by ⌊𝔰⌋, with 𝔰³e^{η𝔰/8} ≤ (j+1)³e^{η/8}e^{−(31/8)ηj}e^{4η𝔰} at j = ⌊𝔰⌋ and the contour pin Σ_{W∋n_f}M^{(ρ)}_Λe^{4η𝔰} ≤ Cρ, gives Σ_{W∋n_f, t(W)≥t}β_W ≤ Cρ·sup_{j≥t}w_j ≤ CρW_t for t ≥ 2, and Cρ·max_{j≥0}w_j ≤ C_ηρW_1 for t = 1.
    {#MD2.4.5.10-4} Summing over the L fine traversals of a step-1 traversal, with the conversions of D2.0(3)(a), gives (ii-t) at k = 1.
    {#MD2.4.5.10-5} Step-1 conventions: t(W) above is relative to a fine traversal, t(W; n_f).
    {#MD2.4.5.10-6} Define t^{(1)}(W; n) as the least t with Q_W in the R_t^{(1)}-neighbourhood of n.
    {#MD2.4.5.10-7} Fine distance C_boxLM(t+1) is step-1 distance R_t^{(1)}, and n ⊇ n_f, so t^{(1)}(W; n) ≤ t(W; n_f) for every n_f ⊂ n with n_f ∈ W, hence {t^{(1)} ≥ t} ⊂ {t(W; n_f) ≥ t}; summing over the L fine traversals gives (ii-t) at k = 1, with C_χ absorbing L·C(1+β₀)⁶; η₁^{−2} = L² is the conversion factor from fine to step-1 plaquette deviations; ℓ_W := 1 and b_W := β_Wη₁² = β_W/L², so that β_W = b_Wℓ_Wη₁^{−2} holds at step 1 with Dev_{Q_W} the step-1 deviation.
    {#MD2.4.5.10-8} ℓ_W and b_W are defined here, from the IT-1 note's step-1 factors (§3a(3), §3a(6)), so the identity β_W = b_Wℓ_Wη₁^{−2} is exact; η₁^{−2} = L² is the ratio of the fine and step-1 plaquette scales, η₁ = L^{−1}.
  - {#MD2.4.5.11} *The transfer (given the inputs below).* (4) proves the per-insertion bound only at the background of the step j(W) at which W was made, U_{j(W)}, from (LPG′) for that step's minimiser.
    {#MD2.4.5.11-1} Carrying W to step k+1 needs it at U_{k+1}:
    {#MD2.4.5.12} (T-dev) e^{θ(W)}‖Y_W(U_{k+1}, J_{k+1})‖ ≤ b_W·Dev_{Q^#_W}(U_{k+1}) for every dev W made at a step j ≤ k with (Q^#_W)⁺ ⊂ Ω_k (scope Ω_k, so that (6)(ζ)'s reclassified insertions are covered).
    {#MD2.4.5.13} *Given (LPG′), D2.6's carrier item (both exclusions of (β), for every V_{i+1} in the support) at the steps j, …, k, the reference clause D(j)(iii) (D2.3(2)), which (1) uses through (4)'s Cauchy step, Bałaban's multi-scale constraint (CRE p.256 (2.10)–(2.12)), k ≤ N (LFR I p.177 (ii): no 𝐑-operation has acted, so the old cutoffs survive and p.268's regularity holds on their support, as in D2.0(3)(b)), CRE p.267's ζ resummation (region 3; Bałaban's), RG1 (1.8), (3.12) (printed), and the step-1 base;
    {#MD2.4.5.13-1} region 1 takes (β)'s input from the induction hypothesis, so D2.2(6)(e)'s membership and CRE p.277's margin are not used here.* (1) (4)'s Cauchy step holds at (U_j(V_j), J_j(V_j)) for every V_j in the support of χ_j(Ω_j): its inputs are f(0) = 0 (Schur, independent of V_j), the analyticity of Y_W on the reference domain, and (LPG′) at step j for U_j(V_j), which (LPG′) states for every V_j in the support and every X ⊂ Ω_j.
    {#MD2.4.5.13-2} So e^{θ(W)}‖Y_W(U_j(V_j), J_j(V_j))‖ ≤ b_WDev_{Q^#_W}(U_j(V_j)) for all such V_j, with b_W as in (4) (the evaluation points are the real ones).
    {#MD2.4.5.13-3} For j = 1 the same holds with V4's group bounds for every U₁ = U₁(V₁) with V₁ in V4's step-1 support (IT-1 note §3a), and V₁^* below lies in that support.
    {#MD2.4.5.13-4} V4's factors that depend on V₁ are χ_1(Ω₁), "the background test of [CRE, (2.16)–(2.17)] at k = 1" (V4 sec:branch-data; CRE p.253 writes ρ₁ in the general form, and (2.17) at k = 1, η = L^{−1}, is p.246's test (1.4)), and the axial factor χ_Ax(P₁¹) (pp.246–247).
    {#MD2.4.5.13-5} V4's other factors (the box factors, the collar tests, ι_ξ, and the label indicator χ_Λ) are functions of the fluctuation and exterior variables, and the far-row indicators are one on the support and omitted (IT-1 note §3c(2)(e)).
    {#MD2.4.5.13-6} (2) at i = 1 puts V₁^* in the support of χ_1(Ω₁) and χ_Ax, with U₁(V₁^*) = U_{k+1}.
    {#MD2.4.5.13-7} The group bound's inputs at U₁ are then V4's at that V₁: δ_{Q_W}(U₁) ≤ Cε₁ (V4 sec:c4-8-4 and sec:c4-11-5, by Lemma c2-plaquette-deviation, from the comparison (B3)(iii) after CRE (1.19)) and the Hessian bound (V4 Lemma c4-7-3).
    {#MD2.4.5.13-8} The branch data (Q_W ⊂ Λ₁, the injective lift) are labels of the term.
    {#MD2.4.5.13-9} (2) The global induction.
    {#MD2.4.5.13-10} For V_{k+1} in the step-(k+1) support put V_i^* := M^iU_{k+1}, j ≤ i ≤ k.
    {#MD2.4.5.13-11} Claim: V_i^* lies in the full step-i support of the term, and U_i(V_i^*) = U_{k+1}, for every i = j, …, k.
    {#MD2.4.5.13-12} Downward induction on i, three regions at each i, with the induction hypothesis at i+1 (at i = k the hypothesis is V_{k+1} itself in the step-(k+1) support):
    - {#MD2.4.5.14} on the cubes □ ⊂ Ω_{i+1}^∼ outside the band Ω_{i+1}^∼∖Ω_{i+1}^{∼−1}: V_i^* = M^iU_{k+1} = M^iU_{i+1}(V_{i+1}^*) = V^{(i)}(V_{i+1}^*) is in the step-i support by D2.0(5)(c)(β) at step i applied at V_{i+1} = V_{i+1}^*.
      {#MD2.4.5.14-1} (β)'s derivation uses the regularity of U_{i+1}(V_{i+1}^*) on Ω_{i+1} ((3.19) is derived from it).
      {#MD2.4.5.14-2} That input comes from the induction hypothesis: V_{i+1}^* lies in the full step-(i+1) support, so CRE p.268 at the step i → i+1, read on that support as in D2.0(3)(b), gives |∂U_{i+1}(V_{i+1}^*) − 1| < 2B₃ε_{i+1}η_{i+1}² on all of Ω_{i+1}, and U_{i+1}(V_{i+1}^*) = U_{k+1} by the hypothesis.
      {#MD2.4.5.14-3} That is (β)'s input, with no comparison of ε's.
    - {#MD2.4.5.15} on the band and on the boundary cubes: D2.6's carrier item, (β)'s both exclusions, proved for all V_{i+1} in the support.
      {#MD2.4.5.15-1} The boundary cubes are WILSON_IT1_D26_CLOSURE_2026_10_24.md §8.2 (M ≥ 4LM₂, with §8.1's gluing); the band cubes with □′^{∼4} ⊂ Ω_{i+1} are its §8.3 (with §8.1's gluing and [15], [12], [14] (1.65)'s reasoning at V^{(i)}), and those with □′^{∼4} ⊄ Ω_{i+1} its §8.3 (1)–(2), the mixed-set localisation across ∂Ω_{i+1}.
      {#MD2.4.5.15-2} Consumers of (T-dev): D2.4(5) *It carries*, D2.4(6), and SW §3(b4); D2.4(12)(f)'s c_{{W}} = 0 (the reference activity of the trivial group) at the reference point is by f(0) = 0 (D2.3(3)), not by (T-dev).
    - {#MD2.4.5.16} off Ω_{i+1}^∼, i.e. on Ω_i∖Ω_{i+1}^∼: the step-i field V_i is a pending variable of the term there, and U_{k+1} satisfies the constraint M^jU_{k+1} = V_j on Γ_j for every j ≤ k+1, by the definition of the multi-scale minimiser (CRE p.256: "V = V_j on Γ_j", (2.10); M_𝔹(U) = M^j(U) on Γ_j, (2.11); the minimal orbit of A^η on {U regular, M_𝔹(U) = V}, (2.12); p.266: U_{k+1} "is determined by the sequence" of fields).
      {#MD2.4.5.16-1} So V_i^* = V_i pointwise on all of Γ_i.
      {#MD2.4.5.16-2} The indicator claim: χ_i(□) depends on V_i through U_{i,□}(V_i) = U(𝔹_i(□^{∼4}), M·(Q_i^{s*}V_i)) (CRE p.257), so for the cubes □ ⊂ Ω_i∖Ω_{i+1}^∼ with □^{∼4} ∩ Ω_{i+1} = ∅ its argument is the same at V_i^* and at V_i; the remaining cubes of Ω_i∖Ω_{i+1}^∼ are boundary cubes, region 2's.
      {#MD2.4.5.16-3} At V_i the factors χ_i(□) and χ_{Ax} of those cubes hold on the term's support: CRE pp.265–266 show χ_{Ax} and χ_i equal to 1 on Ω_{i+1}^∼ only; p.267 resums "the characteristic functions and the gauge fixing terms localized in Ω_k∖Ω_{k+1}" into ζ(Ω_{k+1}^c) (at k = i); ζ(Ω_{i+1}^c) is a factor of 𝐓^{(i)} ((2.21), p.258) inside 𝐓_{k+1} ((2.18), (2.20)), and an operation 𝐓^{(j)} is changed only by an 𝐑-operation ("the characteristic functions are changed", p.258), so it survives for k ≤ N (LFR I p.177 (ii)).
      {#MOMGD.29-5} That the resummed ζ(Ω_{i+1}^c) contains the old χ_i(□) and χ_{Ax} of the cubes off Ω_{i+1}^∼ is CRE p.267's ζ resummation (p.267 does not list its factors; the resummation is Bałaban's).
    {#MD2.4.5.17} And U_i(V_i^*) = U_i(V^{(i)}(V_{i+1}^*)) = U_{i+1}(V_{i+1}^*) = U_{k+1} by (α) at step i, on the whole of Ω_i (U_i is the minimiser for the full sequence; same reference).
    {#MD2.4.5.17-1} No composition identity for the averages is needed: V_i^* is defined as M^iU_{k+1} and recognised as V^{(i)} at V_{i+1}^* through the induction hypothesis.
    {#MD2.4.5.17-2} (3) At i = j, (1) at V_j = V_j^* gives e^{θ(W)}‖Y_W(U_{k+1}, J_j(V_j^*))‖ ≤ b_WDev_{Q^#_W}(U_{k+1}), in the normalisation of step j, for every dev W of step j with (Q^#_W)⁺ ⊂ Ω_k (the full step-k support; this covers the reclassified insertions of (6)(ζ), whose boxes meet Ω_k∖Ω_{k+1}).
    {#MD2.4.5.17-3} The 𝐉-argument: J_j is the expression J(U_j) of RG1 p.272 ("we replace the expression J_j by the new variable 𝐉"; D2.2(6)(b): at real configurations 𝐉 = J_{k+1} = J(U_{k+1}), PBG p.395), the same current expression at every step evaluated at the fine field U_j (RG1 (1.8), (3.12), printed: RG1 (1.8), (3.12)).
    {#MD2.4.5.17-4} Normalisation: at the real step-(k+1) point the 𝐉-argument of a step-j insertion is J̃(U_{k+1}) = D^{ξ*}_{U_{k+1}}ξ^{−2}π Im∂U_{k+1} = (L^{j−1}η)³J_{k+1} (RG1 (3.10) at 𝐀 = 0, and (3.12), p.272).
    {#MD2.4.5.17-5} Under RG1 (1.8), (3.12) and U_j(V_j^*) = U_{k+1}, this is J_j(V_j^*) in step-j normalisation and units, so the bound is at D(k+1)'s evaluation point (U_{k+1}, J_{k+1}) up to that fixed factor and change of units.
    {#MD2.4.5.17-6} That is (T-dev), stated for (Q^#_W)⁺ ⊂ Ω_k.
    {#MD2.4.5.17-7} Its inputs: (LPG′), D2.6's carrier item at each step, the reference clause D(j)(iii), k ≤ N (LFR I p.177 (ii)), CRE p.267's ζ resummation, RG1 (1.8), (3.12), and the step-1 base.
  - {#MD2.4.5.18} *It carries from k to k+1 (given (T-dev)).* An old dev insertion with (Q^#_W)⁺ ⊂ Ω_{k+1} stays dev, with β_W unchanged, by (T-dev).
    {#MD2.4.5.18-1} (The β-inequality below is unconditional arithmetic on the β_W; (T-dev) is what gives it its meaning as a bound on the insertions at U_{k+1}.) If (Q^#_W)⁺ lies within step-k distance R_t^{(k)} of n ⊂ n′, it lies within step-(k+1) distance R_t^{(k)}/L ≤ R_t^{(k+1)} of n′, so t^{(k+1)}(W) ≤ t^{(k)}(W).
    {#MD2.4.5.18-2} Hence Σ_{W∋n′, t^{(k+1)}(W)≥t}β_W ≤ Σ_{n⊂n′}Σ_{W∋n, t^{(k)}(W)≥t}β_W ≤ L·C_χ^{(k)}ρ̃_kη_k^{−2}W_t = L^{−1}(ρ̃_k/ρ̃_{k+1})C_χ^{(k)}ρ̃_{k+1}η_{k+1}^{−2}W_t, the coefficient of (6)'s recursion.
  - {#MD2.4.5.19} *New groups (given (S)).* With Q^#_𝒢 := X(𝒢), β_𝒢 = (C_g/(c₀ᾱ_{k+1}))e^{θ_{k+1}(𝒢)}S_𝒢ℓ_{X(𝒢)}η_{k+1}^{−2}, so (S) summed over t′ ≥ t gives Σ_{𝒢∋n′, t(𝒢)≥t}β_𝒢 ≤ (C_gC_S/c₀)ρ̃_{k+1}η_{k+1}^{−2}W_t.
  - {#MD2.4.5.20} *The fluctuation parts and pair contractions of D2.0(5)(d).* In the exact construction they are not separate insertions.
    {#MD2.4.5.20-1} An old insertion touched by the step-(k+1) fluctuation is a W ∈ 𝔅(M) of a marked polymer M, evaluated at the shifted background inside Ĥ(M) (D2.2(6)(b4)), so it lies in a step-(k+1) group 𝒢 (D2.2(6)(d)).
    {#MD2.4.5.20-2} Its fluctuation part Y(U_k) − Y(U_{k+1}) and its contractions with other old insertions and with the leading word are parts of Y_𝒢: the flat scalar parts are in c_𝒢 and the rest is in Y^d_𝒢 (D2.3(2), *The split*).
    {#MD2.4.5.20-3} An untouched old insertion is taken at s = 0, that is at U_{k+1}, and is carried by (T-dev).
    {#MD2.4.5.20-4} So their tail form is (ii-t) for the new groups (*New groups* above, given (S)), with the first-order term of the leading word in (S)'s parity step (D2.4(11)(f)).
    {#MD2.4.5.20-5} The per-insertion form that (6)(ζ) needs for them is (4)'s for 𝒢 at its step k+1, which (T-dev) carries at the later steps.

### (6) Matching, Split, and Recursion {#MSD2.4.6}

- {#MD2.4.6.1} *(γ) The matching.* Take R_t^{(k)} := C_boxM(t+1) in step-k units at every k, which is D2.0(3)'s R_t^{(1)} at k = 1.
  {#MD2.4.6.1-1} Let n be one of the L step-k traversals in the new traversal n′.
  {#MD2.4.6.1-2} Step-(k+1) distances are step-k distances divided by L, so a plaquette within step-k distance R_t^{(k)} of n lies within step-(k+1) distance R_t^{(k)}/L ≤ R_t^{(k+1)} of n′.
  {#MD2.4.6.1-3} On a common plaquette set, Δ^{(k)}_n(R_t^{(k)}) ≤ Δ^{(k+1)}_{n′}(R_t^{(k+1)}) for every t.
  {#MD2.4.6.1-4} With η_k^{−2} = L^{−2}η_{k+1}^{−2},
  {#MD2.4.6.2} δ*^{(k)}_n(U) ≤ L^{−2}δ*^{(k+1)}_{n′}(U) for every U, on the plaquettes of Ω_{k+1}.
  {#MD2.4.6.3} Dev is not converted.
  {#MD2.4.6.3-1} Each insertion keeps Dev, ℓ_W and b_W in the normalisation of its step j(W) ((5), *Normalisation*), and the per-traversal bound carries through (ii-t) and the inclusion t^{(k+1)}(W) ≤ t^{(k)}(W) ((5)).
- {#MD2.4.6.4} *(ζ) The split (from (ii-t), given (T-dev) of (5)).* An old dev insertion W with (Q^#_W)⁺ ⊂ Ω_{k+1} stays dev ((5), carrying (ii-t), given (T-dev)).
  {#MD2.4.6.4-1} The bound below uses b_WDev_{Q^#_W}(U_{k+1}) for the reclassified insertions, whose boxes meet Ω_k∖Ω_{k+1}: that is (T-dev) in its scope (Q^#_W)⁺ ⊂ Ω_k ((5); through its global induction it needs D2.6's carrier item at every step j(W), …, k, on all band and boundary cubes).
  {#MD2.4.6.4-2} If (Q^#_W)⁺ meets Ω_k∖Ω_{k+1}, it becomes att(k+1, Z).
  {#MD2.4.6.4-3} By D2.0(3)'s reclassification rule, Z contains the first component of Ω_{k+1}ᶜ that the box meets, so the box meets Z, and R^{(k)}_{t^{(k)}(W)} ≥ dist(n, Z).
  - {#MD2.4.6.5} *Its plaquettes.* (Q^#_W)⁺ ⊂ Ω_k for a dev insertion at step k.
    {#MD2.4.6.5-1} By membership (2.34) at j = k+1, i.e. U_{k+1} in the step-(k+1) space on Ω_k∖Ω_{k+1}, which is D2.2(6)(e)'s (D2.0(3)(c) has it only "once U_{k+1} is shown to lie in the space") (CRE p.261: |∂U − 1| < (1−β(1−2^{−(j−n)}))α_{0,n}ξ²(L^nξ)^{−2}), the fine plaquettes of Ω_k∖Ω_{k+1} (n = k) give η_k^{−2}δ_p ≤ c_σ(1−β/2)α_{0,k}, as in D2.0(3)(c).
    {#MD2.4.6.5-2} Those of Ω_{k+1} (n = k+1) give η_k^{−2}δ_p ≤ c_σL^{−2}α_{0,k+1} ≤ c_σ(1+β₀)²L^{−2}α_{0,k} ≤ c_σα_{0,k}.
    {#MD2.4.6.5-3} So b_WDev_{Q^#_W} ≤ β_Wη_k²c_σα_{0,k}.
    {#MD2.4.6.5-4} Only the factor α_{0,k} is used below, so the margin (1 − β/2) is not needed.
  - {#MD2.4.6.6} *The bound.* Let t_Z be the least t with R_t^{(k)} ≥ dist(n, Z).
    {#MD2.4.6.6-1} By (ii-t),
    {#MD2.4.6.7} Σ_{W∋n, W ↦ att(k+1,Z)}b_WDev_{Q^#_W} ≤ c_σα_{0,k}η_k²Σ_{W∋n, t^{(k)}(W)≥t_Z}β_W ≤ C_χρ̃_kc_σα_{0,k}W_{t_Z} ≤ Cρ_k·max(1, α_{0,k}/α_{1,k})·e^{−cd_{k+1}^Z(n)/M},
    {#MD2.4.6.8} since ρ̃_kα_{0,k} = ρ_kα_{0,k}/ᾱ_k and W_t decays exponentially in t.
    {#MD2.4.6.8-1} This is per component, as D(k+1)(ii)'s att bound is (D2.0(3), "Per component").
  - {#MD2.4.6.9} D(k+1)(ii)'s att constant is Cρ̂_{k+1}, with ρ_k ≤ (1+β₀)⁶ρ_{k+1}.
    {#MD2.4.6.9-1} So the split needs α_{0,k}/α_{1,k} = (C₀/C₁)(log g_k^{−2})^{q₀−q₁} bounded, i.e. q₀ ≤ q₁, met by q₀ = q₁ of SW closure §2.
- {#MD2.4.6.10} *The recursion with ρ̃.* The old dev parts on Ω_{k+1} give, by (ii-t) carried ((5)) and its sum form, Σ_{n⊂n′}C_χ^{(k)}ρ̃_kδ*^{(k)}_n ≤ L^{−1}(ρ̃_k/ρ̃_{k+1})C_χ^{(k)}ρ̃_{k+1}δ*^{(k+1)}_{n′}.
  - {#MD2.4.6.11} By CRE (2.6), first and last lines with n − m = 1, g_{k+1} ≤ (1+β₀)g_k and g_k ≤ (1+β₀)g_{k+1}.
    {#MD2.4.6.11-1} By (2.7), first printed line and third (the continuation of the second, with (n−m)^{β₀} = 1 at n − m = 1), (log g_{k+1}^{−2})^p ≤ (1+β₀)(log g_k^{−2})^p and (log g_k^{−2})^p ≤ (1+β₀)(log g_{k+1}^{−2})^p.
  - {#MD2.4.6.12} So ρ_k/ρ_{k+1} ≤ (1+β₀)⁶ (D2.0(5)(c)) and α_{i,k+1}/α_{i,k} ≤ (1+β₀)², hence ᾱ_{k+1}/ᾱ_k ≤ (1+β₀)² and ρ̃_k/ρ̃_{k+1} ≤ (1+β₀)⁸.
  - {#MD2.4.6.13} The terms of D2.0(5)(c)–(d) that are linear in the old dev bound carry this ratio in place of (1+β₀)⁶.
    {#MD2.4.6.13-1} The quadratic term has two old dev bounds, and one of them is O(ρ_k) on the support by (5).
    {#MD2.4.6.13-2} So
    {#MD2.4.6.14} C_χ^{(k+1)} ≤ C_new + (L^{−1} + C_dL²(1+β₀)²g_K²)(1+β₀)⁸C_χ^{(k)} + C_d″ρ_k(C_χ^{(k)})²,
    {#MD2.4.6.15} with C_new := C_gC_S·pl/c₀ from (4) and D2.4(13)(a).
    {#MD2.4.6.15-1} It is bounded uniformly in k if L^{−1}(1+β₀)⁸ < 1 and g_K is small.
  - {#MD2.4.6.16} *The condition (1+β₀)⁸ < L (holds under β₀ ≤ 1/2 and L ≥ L₀ = 5000: 1.5⁸ < 26).* CRE p.255: "β₀ > 0 can be chosen arbitrarily small, if g is sufficiently small".
    {#MD2.4.6.16-1} So for every L ≥ 2 it holds once β₀ < L^{1/8} − 1.
    {#MD2.4.6.16-2} For L ≥ 13 (V4's L > 11 odd, (c-standing-conditions)) with β₀ ≤ 0.22 it holds: 1.22⁸ < 4.91.
    {#MD2.4.6.16-3} D2.0(5)(c)'s "L ≥ 2, β₀ small" is right only with "small" meaning this bound.
  - {#MD2.4.6.17} At the step 1 → 2 the ratio is ρ̃_1/ρ̃_2 = (ρ_1/ρ_2)ᾱ_2 ≤ (1+β₀)⁶ᾱ_2 < 1, so the first step costs nothing.

### (7) The Sizes of the Groups and the Reference Gas {#MSD2.4.7}

- {#MD2.4.7.1} *Where the slot factors are evaluated.* In D2.2(5)(c) the slot factor 𝒳 is a function of the conditioned Z₀-variable B alone ((2.4)–(2.6) there).
  {#MD2.4.7.1-1} It does not depend on X or on the s-, σ-, τ-parameters.
  {#MD2.4.7.1-2} In RG2 (2.14) B is a real integration variable, and the complex quantities are (𝐔, 𝐉) ∈ 𝐔^c_{k+1}(X,α₀,α₁), σ and τ.
  {#MD2.4.7.1-3} (2.15) bounds (2.14) by an integral of absolute values.
  {#MD2.4.7.1-4} So 𝒳 enters (2.15) through sup‖𝒳‖ over real B in the support of the indicators and complex (𝐔, 𝐉) in the domain.
  {#MD2.4.7.1-5} That is D(k)(iii)'s domain at U_k(𝐔, B), which D2.2(4)(f) and (6)(e) supply.
- {#MD2.4.7.8} *(S), the size statement (proved in the form (S-w) of (12)(b), (13)(d)).* Σ_{𝒢∋n′, t(𝒢)=t}e^{θ_{k+1}(𝒢)}S_𝒢ℓ_{X(𝒢)} ≤ C_Sρ_{k+1}w_t for every t ((4)), and the same with c_𝒢 in place of S_𝒢 for the reference gas, with ℓ_X = d_{k+1}(X) + 1 ((4); ℓ_{X(𝒢)} ≤ 2#(X(𝒢)) when X(𝒢) is connected).
  {#MD2.4.7.8-1} Summed over t′ ≥ t it gives (ii-t) for the new groups ((5)).
  {#MD2.4.7.8-2} (S-w) also gives the Kotecký–Preiss root sum of (Z) with insertion weights a(𝒢) ≥ a_min·n_ins(𝒢), a_min = ν/(32LM) (from a°; the occurrences are absorbed by 1/m_𝒢!), with constant C_KP = C_S′ ((13)(b)), and the same count with one old factor replaced by its T–T′ difference ((13)(c); D2.3(4)(Z-d)–(Z-f)).
- {#MD2.4.7.13} *(R), the reference gas.* By D2.3(3) it is a pure hard-core gas of groups that carry their old and vacuum occurrences, with no Mayer links.
  {#MD2.4.7.13-3} Given (S-w), its Kotecký–Preiss condition holds at a°/2, a°(𝒢) := (ν/32)σ_{k+1}(𝒢) ((12)(f), as in (2)(e)–(g)), and FV Thm 5.4 gives:
  - {#MD2.4.7.14} S°(ℓ) ≠ 0 and its cluster series, hence the absolute convergence used in D2.3(3);
  - {#MD2.4.7.15} the tail (T′) of D2.3(5) (#MD2.3.5.2), uniformly in k;
  - {#MD2.4.7.16} Σ_{Γ hits 𝒢}|Φ°(Γ)| ≤ a°(𝒢), FV Lemma 5.6, (5.17) (p.226), so Q^{out}_{k+1}(D) = exp(−Σ_{Γ hits D}Φ°(Γ)) satisfies |Q^{out}_{k+1}(D)| ≤ ∏_{𝒢∈D}e^{θ_ref(𝒢)} with θ_ref(𝒢) ≤ a°(𝒢) = (ν/32)σ_{k+1}(𝒢).
- {#MD2.4.7.18} *(Z).* Given (S-w), (Z) holds in the form of D(k)(vi) by D2.3(4)(Z-c)–(Z-h) with (12)(f) and (13)(b)–(c) (#MD2.3.4.58).

### (8) Complex Data {#MSD2.4.8}

- {#MD2.4.8.1} *Transports.* On Ω_{k+1}, |η_{k+1}A′| < α_{1,k+1}L^{−(k+1)} per fine bond, so ‖T_𝐔(I(𝒢))‖ ≤ e^{c_π′α_{1,k+1}n_{k+1}(𝒢)}, c_π′ of D2.1(4) *Constants*.
  {#MD2.4.8.1-1} It is at most e^{νσ_{k+1}(𝒢)/64} once c_π′α_{1,k+1}M ≤ ν/64 (n_{k+1}(𝒢) ≤ Mσ_{k+1}(𝒢), (12)(a)), which holds for g_{k+1} small, since α_{1,k} → 0 as g_k → 0.
  {#MD2.4.8.1-2} For an arc of at most 4M traversals the bound is e, under 4c_π′Mα_{1,k+1} ≤ 1.
  {#MD2.4.8.1-3} The older layers Ω_n∖Ω_{n+1}, n ≤ k, are att and D2.6's.
  {#MD2.4.8.1-4} Transports between groups are not needed: whole-word norms are never used (D2.0(5)(h)).
- {#MD2.4.8.2} *Analyticity of the sums (D2.2(6)(e)).* Bałaban's bounds (2.38) and (2.15) hold at every point of the domain with the same constants.
  {#MD2.4.8.2-1} So the absolute-value integrand of (2.15), with the sup of 𝒳 over the domain, is a majorant, locally uniform in the complex parameters.
  {#MD2.4.8.2-2} Morera's theorem under the integrals and Hartogs' theorem then apply.
  {#MD2.4.8.2-3} The cluster series converge uniformly on the domain by (2) and (R), so their sums are analytic by Weierstrass.
  {#MD2.4.8.2-4} For the reference gas this uses (R), hence (S).
- {#MD2.4.8.3} *The enlargement D_J^#.* D_J^# is determined by J. It is not summed over, so it adds no entropy.
  {#MD2.4.8.3-1} Its cubes are counted in #_{k+1}(𝒢) and in #(M), so their cost is inside θ_vac ≤ c#_{k+1} and inside (S).
- {#MD2.4.8.4} *Slot values at complex backgrounds.* The bounds of the loop slots and old insertions at complex (𝐔, 𝐉) are D(k)(iii)'s at step k.
  {#MD2.4.8.4-1} At step k+1 they are part of (S) (D2.2(6)(e), given VAR Prop. 9's 𝐇^{(j)}).

### (9) The Inputs and Outputs of D2.4 {#MSD2.4.9}

- {#MD2.4.9.1} *Inputs from outside D2.4,* besides (LPG′) ((4)), (T-dev) ((5)), and the vacuum gas's Kotecký–Preiss condition on the full gas off ℓ₀ ((2)(f)):
  - {#MD2.4.9.5} the slot values at complex backgrounds, D2.2(6)(e), given VAR Prop. 9's 𝐇^{(j)}, with the gauge frame of σ_j from the representative of D2.2(4)(d) (D(k)'s hierarchical mean axial gauge) and the base points on Ω₁∖Ω₂ (#MOMGD.11); inside (S) they enter through the sum over slots with the weights w_t;
  - {#MD2.4.9.6} the complex-data dev clause for the carried insertions about U_{k+1}, on 𝒟_{k+1}^{sub}, given (T-dev)'s other inputs (SW closure §6(6c)), SW §6(6d) under q₀ > p₀, (K3) of WILSON_IT1_COMPLEX_COVARIANCE_2026_10_29.md (C_av := 2(B₃ + 2c_dB₅), #MOMGD.5), and (4)(f)'s chain condition with CRE p.277's margin (#MD2.2.6.142, #MOMGD.50): (T-dev) for the real-point part and the complexified covariance for the excess, with no (LPG′) at step k+1 (WILSON_IT1_COMPLEX_COVARIANCE_2026_10_29.md §5);
  - {#MD2.4.9.7} the complex-data size of the dev term near older layers, by the sub-domain form ((5), SW closure §3);
  - {#MD2.4.9.8} for ν ((3)): λ_* and C_g checked against V4 (#MD2.4.3.12-1: λ_*/(64C_g) > 1/16 for every κ); the hull constant A_h (A_s = 1 + A_h) is absolute, A_h := 17, by #MOMGD.14, so ν can be fixed as an absolute number;
  - {#MD2.4.9.10} the complex-background polylog (the IT-1 note's §3j(6)): D(k)'s consumer n_C·ε̄_ph tolerates (log g_k^{−2})^{(q₁−p₀)₊}.
    {#MD2.4.9.10-1} D2.4(5) treats only the dev term's power of log, which q₀ = q₁ > p₀ removes (SW closure §2); ρ^c_{ph}'s power is treated here.
    {#MD2.4.9.10-2} V4's contour-wide factor e^{2n_Cε̄_t} ((c5-5-9)) has no counterpart in D(k): D(k)(ii) is per traversal, and the scalar parts go to D2.3's exact absorption, at real data. ρ^c_{ph,j} enters only through ρ̂^c_j := max(ρ_j, ρ^c_{ph,j}) ~ g_j²(log g_j^{−2})^{4p₀+(q₁−p₀)₊}, as the production amplitude of the att(j, ·) species, whose bounds are sup bounds over the complex domain (#MD2.0.3.48).
    {#MD2.4.9.10-3} Three uses remain.
    {#MD2.4.9.10-4} The carry lemma moves a member's mass multiplicatively, by ∏_n(1 + δ_n) ≤ 2 (D2.6 closure §5, (T0) and (T2)), so no ratio of logs at different scales arises.
    {#MD2.4.9.10-5} The payment by Z's fundamental factor needs only the per-cube smallness of Cρ̂^c_j, which holds since g_j² times a power of log g_j^{−2} tends to 0; D2.6 closure §7 already runs τ̂² ≤ Cg²(log g^{−2})^{max(6p₀, 4p₀+(q₁−p₀)₊)}.
    {#MD2.4.9.10-6} The wrap sum needs sup_j max(ρ̂^c_j, b_j)e^{−c′T_ph/M} small, which holds for the same reason;
  - {#MD2.4.9.11} the D2.1 radius g_k|A_k| ≤ ε_H/C₁ (D2.1(4)), fixed per slot kind in (11)(c).
    {#MD2.4.9.11-1} Pure loop slots ((α)) carry no ω-dependent factor and keep T_Y = ε_H/|B′|_Y.
    {#MD2.4.9.11-2} Slots with touched old insertions ((β)), the ω-dependent factors of D2.2(6)(e)'s constraint (#MD2.2.6.183), run at 1/T_Y ≥ 16B₀e^{16κ_s}|B′|_Y/(min(β,1)α_{1,k}), which is that constraint's cut to the α_{1,k} scale ((4)(f) *T_Y*).
    {#MD2.4.9.11-3} The ω′-dependent groups use the same per-slot factors pointwise in ω′ (D2.6 closure §2.2, its row R2), and the Cauchy step uses D(k+1)(iii)'s domain.
- {#MD2.4.9.13} *Outputs:*
  - {#MD2.4.9.14} the Kotecký–Preiss condition for Bałaban's vacuum gas, with κ ≥ κ_D: on ℓ₀ from Lemma 3, and on a labelled term for the subgas Z ∈ 𝐃_{k+1}, Z ⊂ Λ_{k+1}, from CRE p.279's same-way clause in the form (i′) ((2));
  - {#MD2.4.9.15} RG2 Lemma 3's repair ((1), on every use in RG2 pp.7–21): Lemma 3 holds with Bałaban's absolute constants enlarged by absolute factors (162, e^{20.25}, 2, ≤ 162, e^{162A}), since RG2 (2.30)'s left side fails for small domains; C₃′ := C₃ with the enlarged O(1) O₃;
  - {#MD2.4.9.16} θ_vac ≤ cσ_{k+1};
  - {#MD2.4.9.17} the Cauchy step and the per-insertion form at the real point, given (LPG′) and (S), with X(𝒢) containing the arc;
  - {#MD2.4.9.18} the tail clause (ii-t): at step 1 from IT-1 §3a(6), its sum form, for new groups given (S), and its carrying from k to k+1 given (T-dev);
  - {#MD2.4.9.19} the matching (γ) for δ* (Dev is not converted), and the split (ζ) from (ii-t), given (T-dev);
  - {#MD2.4.9.20} the recursion with (1+β₀)⁸;
  - {#MD2.4.9.21} given (S): KP for the reference gas, and |Q^{out}_{k+1}| ≤ ∏e^{a°} by FV Lemma 5.6, (5.17) (all of (R) given (S-w), (7));
  - {#MD2.4.9.22} the complex-data items of (8), the analyticity of the reference-gas sums given (S).
- {#MD2.4.9.31} *Amendments of D(k) (notes in D2.0(3) and (5)):* the dev constant ρ̃_k, the per-insertion form and the tail clause (ii-t) in (ii), with Dev, ℓ_W, b_W in the normalisation of the step of production; R_t^{(k)} := C_boxM(t+1) in step-k units at every k ((6)(γ)); σ_{k+1} in the norms; the exponent 8 in D2.0(5)(c)'s recursion and (1+β₀)^{10}L²g_K² in (5)(d); (vi) for the insertions and cluster weights ((7), (Z)).
- {#MD2.4.9.32} *To D2.6:* polymers meeting Λ_{k+1}ᶜ; groups depending on ω′; the factor (log g_k^{−2})^{(q₀−q₁)₊} in the att(k+1, ·) constant if q₀ > q₁; the older layers' transports.
  {#MD2.4.9.32-1} These are WILSON_IT1_D26_CLOSURE_2026_10_24.md §2.4 (polymers meeting Λ_{k+1}ᶜ), §2.2 (ω′-groups), §3 (q₀ = q₁ removes the factor), and §5.4 (transports on 𝒟^{sub}: phase ≤ α_{1,k+1} per step-(k+1) bond on every layer, no growth of a carried group's transport factor).

### (10) Step 1 of (S): The H′ Bound for Marked Polymers {#MSD2.4.10}

{#MD2.4.10.1} *(a) The object.* A marked polymer M (D2.2(5)(c)) is a linked union of connected Z ∈ 𝐃_{k+1} with slot set J(M) ≠ ∅.
{#MD2.4.10.1-1} D := D_J^#(M) ⊂ M is the union of π_k-cubes of D2.2(5)(c) for the slots of M, m(M) its number of wall-connected components; every connected component of M meets D (one disjoint from D would be a vacuum polymer of its own).
{#MD2.4.10.1-2} H̃(M) is the sum over (𝐃, P, Z₀) with Y₀ = ∪_{Y∈𝐃}Y ∪ D, P ⊂ Y₀^{c*}, Z₀ the smallest localisation domain containing Y₀ ∪ P (so D ⊂ Z₀), Z₀′ the π_{k+1}-hull of Z̃₀, Z₀′ ⊂ M with every component of M containing a component of Z₀′ (p.14), of the terms (2.14) with 𝒳_M in the B-integrand and Z = M. Notation:
- {#MD2.4.10.2} ‖𝒳_M‖_sup := sup of ‖𝒳_M(B; 𝐔, 𝐉)‖ over real B with |B(b)| < t_k := δ_k/g_k for every bond b ⊂ D (CRE (3.16)'s test in the variable B of (2.14), (11)(b); RG2 (2.3)'s threshold ε₁/g_k is replaced by t_k throughout (b) and (e): the P-factor is e^{−½γ₂t_k²|P|}, the conditions "(1/20)γ₂ε₁²/γ² ≥ 18κ", "e^{−γ₂ε₁²/(20γ²)} ≤ ε₂" and the term 4M⁴e^{−γ₂ε₁²/(10γ²)} of A read with t_k² in place of ε₁²/γ², and are smallness conditions on g_K, since t_k = A₁(log ĝ_k^{−2})^{p₀}ĝ_k/g_k ≥ ρ_γ^{−1/2}r_k (#MD2.4.11.2-1; ĝ_k ≤ g_k ≤ ρ_γ^{1/2}ĝ_k with ρ_γ → 1, Cauchy #CP.14) and r_k ≥ A₁(log((1+β₀)^{−2}g_K^{−2}))^{p₀} uniformly in k ≤ K;
  {#MD2.4.10.2-1} the support lies in (1.34)'s disc since δ_k < ε₁^{RG2} for g_K small) and over (𝐔, 𝐉) in the domain of (7)'s first bullet; ‖·‖ is the projective norm on ⊗_{i∈J(M)}End(V_π), a cross norm, the same on both sides ((12)(f)). 𝒳_M depends on B through the bonds inside D only, and not on X, s, σ, τ (D2.2(5)(c)).
- {#MD2.4.10.3} Contracted linear size.
  {#MD2.4.10.3-1} For a union X of cubes of one partition (side a) and a union D ⊂ X of its cubes, d(X; D) := a^{−1} inf |G ∖ D| over the finite unions G of segments and points with G ⊂ X, G meeting every cube of X and G ∪ D connected; |·| is the one-dimensional measure. d(X; ∅) is RG1 p.257's d(X).
  {#MD2.4.10.3-2} A cube of X that touches D costs nothing (a point of the cube in D); distinct components of D are joined through G, so their distance is charged.
  {#MD2.4.10.3-3} For M with components M^j, d_{k+1}(M; D′) := Σ_j d_{k+1}(M^j; D′ ∩ M^j). d_k is at scale k (a = M), d_{k+1} at scale k+1 (a = LM).
- {#MD2.4.10.4} D′ := the π_{k+1}-hull of D̃ (the smallest union of π_{k+1}-cubes containing D̃, D̃ := D with its touching π_k-cubes adjoined; p.13's convention for Z₀′).
  {#MD2.4.10.4-1} Z₀ ⊇ D gives Z₀′ ⊇ D′, and #_{k+1}(D′) ≤ #_k(D̃) ≤ 81#_k(D).

{#MD2.4.10.5} *(b) Result.* Let λ_L := L/max{2, 1 + 486/L} (= L/2 for L ≥ 486), r_κ := (1 − 5δ)λ_Lκ (= (L+2)κ/4 with RG2 p.21's δ = (1−2/L)/10 for L ≥ 486), and A := O(1)(LM)⁴α₅ + e^{−½(κ₁−1)} + L⁴(O_{(1.26)}α₆ + 4M⁴e^{−γ₂t_k²/10}), this (10)'s constant (RG2 Lemma 3's repair's A is p.20's), an absolute constant that Bałaban's choices make as small as wanted — an added restriction: p.20's "(LM)⁴α ≤ 1" is strengthened to "≤ a small number"; α₆ ≤ that number times L^{−4}; M, κ₁ large; g_K small for the last term.
{#MD2.4.10.5-1} Then, uniformly on the domain of (7)'s first bullet and in k,
  {#MD2.4.10.6} |H̃(M)| ≤ ‖𝒳_M‖_sup · e^{81A·#_{k+1}(D′)} · e^{(5 + 3λ_L)κ(m(M) − 1)} · exp(−r_κ·d_{k+1}(M; D′)),
{#MD2.4.10.7} under Lemma 3's restrictions with these constants made explicit: (1/20)γ₂t_k² ≥ 18κ (p.18 prints 4κ with ε₁²/γ²; (d)), ε₂e^{max(5, 3λ_L)κ} ≤ 1 (p.18's ε₂e^{5κ} ≤ 1; (e)), ½(κ₁−1) ≥ 2Lκ (p.20; this is what (10) itself uses, charging 3 per parent edge; Lemma 3 as printed needs ½(κ₁−1) ≥ 9Lκ by (d), a condition on κ₁ recorded in RG2 Lemma 3's repair), 324A ≤ δλ_Lκ (the absorption of (1)'s p.20 bullet in contracted form, with (d)'s counting constant 324), and RG2 Lemma 3's repair's conditions on κ.
{#MD2.4.10.7-1} No smallness factor: the term 𝐃 = ∅, P = ∅, Z₀ = D, M = Z₀′ = D′ is the conditioned Gaussian expectation of 𝒳_M and is bounded by ‖𝒳_M‖_sup·e^{A#_{k+1}(D′)} only.
{#MD2.4.10.7-2} Every other term of H̃(M) carries a factor ϑ := max{e^{−20δκ}, e^{−γ₂ε₁²/(20γ²)}, e^{−Lκ/2}} ≤ e^{−2κ/3} ((e)).
{#MD2.4.10.7-3} So H̃(D′) = (the plain expectation term) + O(ϑ), and H̃(M) = O(ϑ) for M ≠ D′, each with the bound above.
{#MD2.4.10.7-4} Analyticity in (𝐔, 𝐉): (8); the bound is a majorant.
{#MD2.4.10.7-6} The per-term bounds (2.15)–(2.26) are printed for RG2's measure; their use for the measure of CRE (3.27), with its source term and multi-domain cover (D2.2(5)(b)–(c)), rests on CRE pp.276–279 ("exactly the same way", "do not matter") and RG2's numbering of [I]: Bałaban's claim, read in the form (i′) of CRE p.279's same-way clause.

{#MD2.4.10.8} *(c) The per-term bound: (2.14)–(2.26) with 𝒳_M.*
- {#MD2.4.10.9} (2.14): the Cauchy representations in σ(Δ) and τ(Y) act on the operators and on exp Σ_Yτ(Y)𝐕_k(Y); 𝒳_M carries no s, σ, τ.
  {#MD2.4.10.9-1} So the term is (2.14) with 𝒳_M(B; 𝐔, 𝐉) multiplying the B-integrand, B the real variable of the complex Gaussian measure dμ_{C^{(k)}(Z₀,σ(Z))}.
- {#MD2.4.10.10} (2.15) is a pointwise bound in B. On the support of χ_{k,Y₀}χ^c_{k,P} every bond of D ⊂ Y₀ is small-field, so ‖𝒳_M(B; 𝐔, 𝐉)‖ ≤ ‖𝒳_M‖_sup there, and (2.15) holds with the factor ‖𝒳_M‖_sup in front (‖∫f‖ ≤ ∫‖f‖ for the tensor-valued integral).
- {#MD2.4.10.11} (2.16)–(2.25) concern the operators, the determinants, the potentials 𝐕_k(Y) and the indicators; none contains 𝒳_M.
  {#MD2.4.10.11-1} (2.20)'s second line is a sum over Y ∈ 𝐃 only, still ≤ O(1)α₄M^{−4}|Y₀| (RG2 Lemma 3's repair's p.16 bullet).
  {#MD2.4.10.11-2} So (2.26) holds with the factor ‖𝒳_M‖_sup, for every (𝐃, P, Z₀) with Y₀ ⊇ D, including 𝐃 = ∅ (empty product) and P = ∅:
  {#MD2.4.10.12} |term| ≤ ‖𝒳_M‖_sup · e^{−(κ₁−1)#_{k+1}(Z∖Z₀′)} · ∏_{Y∈𝐃}ε₂α₆e^{−(1−3δ)κd_k(Y)} · e^{−½γ₂(ε₁²/g_k²)|P|} · e^{O(1)α₅|Z|},
  {#MD2.4.10.13} with ε₂α₆ = 2E₀ε₁C₁α₄^{−1}M^q e^{C₂κ₁} (p.19) and #_{k+1}(Z∖Z₀′) = (LM)^{−4}|Z∖Z₀′|.

{#MD2.4.10.14} *(d) Geometry: (2.27), (2.32), (2.36) in contracted form.* Lengths in the cube side of the scale concerned.
{#MD2.4.10.14-1} A join between two pieces that share a cube or a wall, or between a piece and a cube it touches, costs at most √7 < 3 (the diameter of two wall-adjacent 4-cubes) from a point of one graph in the shared or adjacent cube to a point of the other.
- {#MD2.4.10.15} (2.27′) For Y_i a wall-connected component of Y₀, 𝐃_i := {Y ∈ 𝐃 : Y ⊂ Y_i}, D_i := D ∩ Y_i with m_i components: Σ_{Y∈𝐃_i}d_k(Y) ≥ d_k(Y_i; D_i) − 5(|𝐃_i| + m_i − 1).
  {#MD2.4.10.15-1} Proof: the pieces Y ∈ 𝐃_i and the components of D_i cover Y_i and their touching graph is connected (a wall-path of cubes passes from piece to piece through shared cubes or walls); a spanning tree has |𝐃_i| + m_i − 1 edges; G := ∪_YT_Y ∪ joins, T_Y a shortest tree of Y, meets every cube of Y_i, G ∪ D_i is connected, and |G∖D_i| ≤ Σ_YMd_k(Y) + 3M·(edges).
  {#MD2.4.10.15-2} For D_i = ∅ this is (2.27) (with 3 in place of 5).
- {#MD2.4.10.16} (2.32′) For a wall-connected component Z_i of Z₀ with Y-components Y_j ⊂ Z_i and D_i := D ∩ Z_i: Σ_jd_k(Y_j; D_j) + 18#_k(Z_i∖Y₀) ≥ d_k(Z_i; D_i).
  {#MD2.4.10.16-1} Proof: for each cube C ⊂ Z_i∖Y₀ take its main diagonal (length 2; its endpoints lie on all 8 walls); across each wall of C shared with a cube of Z_i join the diagonal's endpoint on that wall to the neighbour's graph (≤ 2 each; ≤ 8 walls).
  {#MD2.4.10.16-2} With the pieces' graphs G_j ∪ D_j this is a connected G meeting every cube of Z_i (distinct Y_j share no wall, so every wall-path between pieces passes through cubes of Z_i∖Y₀), and |G∖D_i| ≤ Σ_jMd_k(Y_j; D_j) + 18M#_k(Z_i∖Y₀).
  - {#MD2.4.10.17} *(2.32) as printed is false.* P.18: "By a simple geometric argument we have Σ_id_k(Y_i) + 4M^{−4}|Z₀∖Y₀| ≥ d_k(Z₀)".
    {#MD2.4.10.17-1} Counterexample (d = 4): one cube C ∈ Z₀∖Y₀ and eight rods Y₁, …, Y₈ of n ≥ 2 cubes each, one on each wall of C, pointing outward.
    {#MD2.4.10.17-2} The rods are distinct wall-components of Y₀ (two rods meet along a 2-face at most), d_k(rod) = n − 2, and d_k(Z₀) ≥ 8(n−1): the eight regions {x_μ > 1} ∩ Z₀ and {x_μ < 0} ∩ Z₀ are pairwise disjoint, and a connected graph meeting every cube of a rod has length ≥ n − 1 inside its region (the measure of its x_μ-projection).
    {#MD2.4.10.17-3} So d_k(Z₀) ≥ Σ_id_k(Y_i) + 8 > Σ_id_k(Y_i) + 4 (the main diagonal of C plus eight axis segments gives d_k(Z₀) ≤ 8(n−1) + 2; the exact value is not needed).
    {#MD2.4.10.17-4} The inequality holds with 18 (above; the sharp constant lies between 8 and 18).
    {#MD2.4.10.17-5} Its use, p.18's "(1/20)γ₂ε₁²/γ² ≥ 4κ", becomes "≥ 18κ", a condition on γ (on g_K with CRE's threshold, (a)); p.20's adaptation at scale k+1 ("(2.32), properly adapted") with "½(κ₁−1) ≥ 2Lκ" becomes ½(κ₁−1) ≥ 9Lκ, a condition on κ₁.
    {#MD2.4.10.17-6} Both are in the order of choices that (1)–(2) record (κ; κ₁ and M; the α's; ε₁; γ after ε₁, since γ is bounded by a function of ε₁, γ₂, κ — p.21 prints no order), so Lemma 3 holds as printed with these conditions.
    {#MD2.4.10.17-7} Added to RG2 Lemma 3's repair in (1).
- {#MD2.4.10.18} (2.36′) For Z_i, D_i as above, Z_i′ the π_{k+1}-hull of Z̃_i and D_i′ that of D̃_i: L·d_{k+1}(Z_i′; D_i′) ≤ (1 + 486/L)·d_k(Z_i; D_i) if D_i ≠ ∅.
  {#MD2.4.10.18-1} Proof: let G realise d_k(Z_i; D_i) (G ⊂ Z_i ⊂ Z_i′, G ∪ D_i connected, D_i ⊂ D_i′).
  {#MD2.4.10.18-2} A π_{k+1}-cube Q ⊂ Z_i′∖D_i′ that touches D_i′ is met at a point of Q ∩ D_i′, at no cost.
  {#MD2.4.10.18-3} One that does not touch D_i′ has dist_∞(Q, D_i′) ≥ LM, and D_i′ ⊇ D̃_i ⊇ {dist_∞(·, D_i) ≤ M}.
  {#MD2.4.10.18-4} Q contains a π_k-cube of Z̃_i (hull), which touches a π_k-cube □_Q ⊂ Z_i; so □_Q touches Q and dist_∞(□_Q, D_i) ≥ LM.
  {#MD2.4.10.18-5} G meets □_Q at a point x_Q ∉ D_i, and a segment from x_Q to Q inside □_Q costs ≤ 2M.
  {#MD2.4.10.18-6} The piece of G∖D_i containing x_Q has its closure on D_i (G ∪ D_i is connected), so its length ℓ is ≥ dist(x_Q, D_i) ≥ LM.
  {#MD2.4.10.18-7} Such a piece may branch (G is a Steiner-type minimiser), so it is covered by a closed walk around it, of length 2ℓ, cut into ⌈2ℓ/(LM)⌉ arcs of length ≤ LM; the M-neighbourhood of an arc has ∞-diameter ≤ LM + 2M < 2LM for L ≥ 3 and meets ≤ 3⁴ cubes; so the piece lies within ∞-distance M of at most 81(2ℓ/(LM) + 1) ≤ 243ℓ/(LM) cubes Q (ℓ ≥ LM).
  {#MD2.4.10.18-8} So the stubs cost ≤ 2M·243|G∖D_i|/(LM) = (486/L)|G∖D_i|, and G′ := G ∪ stubs ∪ touching points meets every cube of Z_i′∖D_i′ with G′ ∪ D_i′ connected.
  {#MD2.4.10.18-9} (For the vacuum components Bałaban's (2.36), 2d_k(Z_i) ≥ Ld_{k+1}(Z_i′), is used as printed; (2.36′) replaces it for the marked components only and agrees with it for L ≥ 486.)
- {#MD2.4.10.19} Coarse assembly (p.20's "(2.32), properly adapted", charged to parent edges).
  {#MD2.4.10.19-1} For Z = M connected, with the components Z_i of Z₀ (vacuum: D_i = ∅, n_v of them; marked: D_i ≠ ∅, m′ ≤ m of them), the pieces Π_i := G_i′ ∪ D_i′ (G_i′ realising d_{k+1}(Z_i′; D_i′); for vacuum pieces D_i′ = ∅) and the π_{k+1}-cubes of Z∖Z₀′: the touching graph is connected (Z is wall-connected and Z₀′ = ∪_iZ_i′).
  {#MD2.4.10.19-2} Root a spanning tree at a marked piece; each cube of Z∖Z₀′ pays its parent edge (≤ 3; its own point is the edge's endpoint), each vacuum piece its own (≤ 3), and the m′ − 1 other marked pieces' edges are unpaid: d_{k+1}(Z; D′) ≤ Σ_id_{k+1}(Z_i′; D_i′) + 3#_{k+1}(Z∖Z₀′) + 3(n_v + m′ − 1).
- {#MD2.4.10.20} Counting (replaces (2.30)/(2)(a) near D).
  {#MD2.4.10.20-1} For X wall-connected and ∅ ≠ D ⊂ X: #(X∖D) ≤ 80#(D) + 324·d(X; D), so #(X) ≤ 81#(D) + 324·d(X; D).
  {#MD2.4.10.20-2} Proof: a cube touching D is one of the ≤ 3⁴ − 1 = 80 neighbours of a cube of D; a cube not touching D is at ∞-distance ≥ a from D and is met by a piece of G∖D whose closure reaches D, so of length ℓ_p ≥ a; a piece may branch, so cover it by a closed walk of length 2ℓ_p cut into ⌈2ℓ_p/a⌉ arcs of length ≤ a, each of ∞-diameter ≤ a, meeting ≤ 3⁴ cubes: the piece meets ≤ 81(2ℓ_p/a + 2) ≤ 324ℓ_p/a cubes, and Σ_pℓ_p = a·d(X; D).

{#MD2.4.10.21} *(e) The resummation.* Bałaban's order (𝐃 with Y₀ fixed; Y₀, P with Z₀ fixed; Z₀ with Z₀′ fixed; Z₀′ ⊂ Z) pays the entropy of Z₀'s shape with the decay e^{−δκd_k(Z_i)} of each component.
{#MD2.4.10.21-1} Near D there is no decay, so the entropy is paid instead by the smallness of the Y's and P-bonds that build Z₀ ∖ D: the decay is taken as a sup over the data and the entropy as an unconstrained sum.
{#MD2.4.10.21-2} Fix M = Z connected (for several components the bound is the product of the components' bounds with ‖𝒳_M‖_sup once: the per-term bound (2.26) is a product over the components of M, each meeting D, and Σ_j(m_j − 1) ≤ m − 1).
{#MD2.4.10.21-3} Split each Y-factor of (c) as [α₆e^{−δκd_k(Y)}]·[ε₂e^{−(1−4δ)κd_k(Y)}], and each P-factor as on p.18: e^{−½γ₂(ε₁²/g_k²)|P|} ≤ e^{−(1/10)γ₂(ε₁²/γ²)|P|}·e^{−(1/5)γ₂(ε₁²/γ²)#_k(Z₀∖Y₀)} (|P| ≥ ½#_k(Z₀∖Y₀), p.18; g_k ≤ γ), the second factor being four twentieths: e^{−18κ#_k(Z₀∖Y₀)} (one twentieth, (1/20)γ₂ε₁²/γ² ≥ 18κ), and three spare twentieths e^{−(1/20)γ₂(ε₁²/γ²)#_k(Z₀∖Y₀)} each, each ≤ ε₂^{#_k(Z₀∖Y₀)} by p.19's e^{−γ₂ε₁²/(20γ²)} ≤ ε₂.
- {#MD2.4.10.22} *Decay part of a term:* ∏_{Y∈𝐃}ε₂e^{−(1−4δ)κd_k(Y)}·e^{−18κ#_k(Z₀∖Y₀)}·e^{−(κ₁−1)#_{k+1}(Z∖Z₀′)}·(one spare twentieth per cube of Z₀∖Y₀).
  - {#MD2.4.10.23} In each Y-component Y_i, by (2.27′): root the piece tree at a component of D_i if D_i ≠ ∅, else at a Y. Each non-root Y pays its parent edge, ε₂e^{5(1−4δ)κ} ≤ ε₂e^{5κ} ≤ 1, with e^{−20δκ} to spare.
    {#MD2.4.10.23-1} So a marked Y-component gives e^{5κ(m_i−1)}e^{−(1−4δ)κd_k(Y_i;D_i)} (all its Y's pay; the m_i − 1 edges of the other D-components are unpaid), and a vacuum one gives ε₂e^{−(1−4δ)κd_k(Y_i)} ((2.28), one ε₂ survives).
  - {#MD2.4.10.24} In each component Z_i of Z₀, by (2.32′): every cube of Z₀∖Y₀ pays its 18 at rate (1−4δ)κ ≤ 18κ.
    {#MD2.4.10.24-1} A vacuum Z_i keeps a factor ≤ ε₂ (from a vacuum Y-component, or one spare twentieth of a P-cube if it has no Y).
    {#MD2.4.10.24-2} So Z_i gives e^{5κ(m_i−1)}e^{−(1−4δ)κd_k(Z_i;D_i)} if marked, and ε₂e^{−(1−4δ)κd_k(Z_i)} if vacuum.
  - {#MD2.4.10.25} To scale k+1: by (2.36) for vacuum and (2.36′) for marked components, (1−4δ)κd_k(Z_i; D_i) ≥ (1−4δ)λ_Lκd_{k+1}(Z_i′; D_i′), since λ_L ≤ L/2 and λ_L ≤ L/(1 + 486/L).
  - {#MD2.4.10.26} Coarse assembly: each vacuum piece pays its parent edge with its ε₂, ε₂e^{3(1−4δ)λ_Lκ} ≤ 1; each cube of Z∖Z₀′ pays its edge, 3(1−4δ)λ_Lκ ≤ ½(κ₁−1), from half of its factor, with e^{−Lκ/2} to spare (½(κ₁−1) ≥ 2Lκ, λ_L ≤ L/2); the m′ − 1 unpaid marked edges cost e^{3(1−4δ)λ_Lκ} each.
    {#MD2.4.10.26-1} With Σ_i(m_i − 1) ≤ m − m′ over the marked Y-components (each marked Z_i has one at least):
  {#MD2.4.10.27} decay ≤ e^{(5+3λ_L)κ(m−1)}·e^{−(1−4δ)λ_Lκ·d_{k+1}(Z; D′)}·e^{−½(κ₁−1)#_{k+1}(Z∖Z₀′)}.
- {#MD2.4.10.28} *Entropy part of a term:* ∏_{Y∈𝐃}α₆e^{−δκd_k(Y)}·e^{−(1/10)γ₂(ε₁²/γ²)|P|} (the remaining spare twentieths ≤ 1).
  {#MD2.4.10.28-1} Summed over all subfamilies 𝐃 ⊂ 𝐃_k of domains Y ⊂ Z₀′ and all bond sets P in Z₀′, every constraint dropped ((𝐃, P) determines Z₀ and Z₀′, so the constrained sum is smaller): ≤ ∏_{Y⊂Z₀′}(1 + α₆e^{−δκd_k(Y)})·∏_{b⊂Z₀′}(1 + e^{−γ₂ε₁²/(10γ²)}) ≤ exp[(O_{(1.26)}α₆ + 4M⁴e^{−γ₂ε₁²/(10γ²)})#_k(Z₀′)] (each Y contains a cube of Z₀′ and (1.26) holds at rate δκ ≥ κ_{(1.26)}, RG2 Lemma 3's repair; 4M⁴ bonds of T^{(k)} per π_k-cube).
  {#MD2.4.10.28-2} This needs neither (2.29) nor (2.34), nor the sums of pp.19–20 over the components Z_i and the families Z_i′.
- {#MD2.4.10.29} *Fixed Z₀′ ⊂ Z:* Σ_{(𝐃,P): Z₀′(𝐃,P)=Z₀′}|term| ≤ ‖𝒳_M‖_sup·e^{O(1)α₅|Z|}·(entropy sum)·sup(decay) ≤ ‖𝒳_M‖_sup·e^{(O(1)(LM)⁴α₅ + L⁴B₂)#_{k+1}(Z)}·e^{(5+3λ_L)κ(m−1)}e^{−(1−4δ)λ_Lκd_{k+1}(Z;D′)}e^{−½(κ₁−1)#_{k+1}(Z∖Z₀′)}, B₂ := O_{(1.26)}α₆ + 4M⁴e^{−γ₂ε₁²/(10γ²)}, using #_k(Z₀′) ≤ L⁴#_{k+1}(Z).
- {#MD2.4.10.30} *Sum over Z₀′ ⊂ Z* (constraints dropped): Σ_{Z₀′}e^{−½(κ₁−1)#_{k+1}(Z∖Z₀′)} ≤ (1 + e^{−½(κ₁−1)})^{#_{k+1}(Z)} ≤ e^{e^{−½(κ₁−1)}#_{k+1}(Z)}.
  {#MD2.4.10.30-1} Total per π_{k+1}-cube of Z: e^{A}, A as in (b).
- {#MD2.4.10.31} *Absorption:* by the counting inequality at scale k+1 (D′ ≠ ∅), e^{A#_{k+1}(Z)} ≤ e^{81A#_{k+1}(D′)}e^{324A·d_{k+1}(Z;D′)} ≤ e^{81A#_{k+1}(D′)}e^{δλ_Lκ·d_{k+1}(Z;D′)} once 324A ≤ δλ_Lκ.
  {#MD2.4.10.31-1} This is (b), with the rate (1−5δ)λ_Lκ.
- {#MD2.4.10.32} *Smallness ϑ:* every Y of 𝐃 leaves e^{−20δκ} (a Y ⊂ D needs no join and leaves ε₂), every P-cube a spare twentieth e^{−γ₂ε₁²/(20γ²)}, every cube of Z∖Z₀′ e^{−Lκ/2}.
  {#MD2.4.10.32-1} The only term without a Y, a P-bond or a cube of Z∖Z₀′ is (𝐃, P, Z₀, Z) = (∅, ∅, D, D′), the conditioned expectation of 𝒳_M.
  {#MD2.4.10.32-2} With δκ ≥ κ/30 (RG2 Lemma 3's repair), e^{−γ₂ε₁²/(20γ²)} ≤ ε₂ ≤ e^{−5κ} and L ≥ 3, ϑ ≤ e^{−2κ/3}.

{#MD2.4.10.33} *(f) Scope.* The slot factor enters (b) through ‖𝒳_M‖_sup only, and (b) gives no decay inside or across D′: that decay comes from ‖𝒳_M‖_sup, that is, from the old norms and the slot sizes ((11)); CRE p.277 is not used.
  {#MD2.4.10.34-3} The cost of D′ is e^{81A} per π_{k+1}-cube, A small at will, and e^{(5+3λ_L)κ} per component of D beyond the first; both are paid by the slots' own sizes ((11)(d)).
  {#MD2.4.10.35} Since #_{k+1}(M) ≤ 81#_{k+1}(D′) + 324·d_{k+1}(M; D′) ((d) *Counting*), (b)'s decay is at least e^{−r_κ(#_{k+1}(M) − 81#_{k+1}(D′))/324}.
  {#MD2.4.10.35-2} Components of M meeting Λ_{k+1}ᶜ are D2.6's.
  {#MD2.4.10.35-3} The reference activities c_𝒢 ((7)(R)) obey the same bound at the reference point.

### (11) Step 2 of (S): The Slot Sizes ‖𝒳_M‖_sup and the Count Check {#MSD2.4.11}

{#MD2.4.11.1} *(a) The slots.* By D2.2(5)(a), 𝒳_M = ⊗_{i∈J(M)}Y_{G_i}, the new insertions of the groups G_i of D2.2(4)(e) whose slots M carries; the untouched old insertions are not in 𝒳 (they do not depend on A).
{#MD2.4.11.1-1} Each G_i is a set of s-components Y (connected unions of π_k-cubes, D2.1(4) *Setting*; the σ_k of RG2's example is π_k, D2.2(5)(c)) with the old insertions W whose intervals lie in I(G_i) or whose domains X_W (or blocks, for ω-dependent W) meet a component (D2.2(4)(e) *Arcs and new groups*).
{#MD2.4.11.1-2} Three kinds, by components: (α) *pure loop groups*, no old insertion, every component in Ω_k (case (A) of D2.1(4)); (β) *groups with old insertions*, every component in Ω_k; (γ) groups with a component meeting Ω_kᶜ (case (B)), whose sizes are D2.6's and are not bounded here.
{#MD2.4.11.1-3} Put n(G) := the number of components of G, #(G) := Σ_{Y∈G}#(Y) π_k-cubes, and D_i := the union of the π_k-cubes containing in their interior every bond on which Y_{G_i} depends, so that D = ∪_iD_i.
{#MD2.4.11.1-4} Y_{G_i} depends on B through B′ on the components of G_i (D2.1(4) *Locality*; D2.2(4)(e) *Locality*), and B′|_Y depends on B within the range of RG2 (1.19)'s operators C and hD̃ about Y (D2.1(4)(b)); so D_i ⊂ (∪_{Y∈G_i}Y)^{∼c_B}, c_B the number of π_k-cubes of that range, and #_k(D_i) ≤ (2c_B+1)⁴#(G_i) =: c_D#(G_i).
{#MD2.4.11.1-4-1} c_B must not depend on M, since κ_s is chosen before M ((d)); it does not: the range of (1.19)'s C and hD̃ is the range of RG1's step-k operators as localised by PBG p.394's locality (D2.1(4)(b)), fixed with L and PBG p.394's locality's convention before M, so c_B ≤ 1 and c_D ≤ 81 once M exceeds that range.
{#MD2.4.11.1-5} The wall-components of D number m(M) ≤ #_k(D) ≤ c_D#(G_M) (D need not have one component per s-component); n(M) := Σ_in(G_i).
{#MD2.4.11.1-6} The domains X_W of the touched old insertions are not part of D: Y_{G_i} depends on B through B′ on the components and through 𝐇(s, B′), which vanishes off the components (D2.2(4)(e)); D2.2(6)(d) states the same, and the touched W are counted inside the M-vertex in (12)(c).

{#MD2.4.11.2} *(b) The threshold on the support (units of CRE (3.16)).* ‖𝒳_M‖_sup is a sup over real B on the support of χ_{k,Y₀}, which is CRE (3.16)'s test on the bonds of D ((10)(a); D2.2(5)(c)).
{#MD2.4.11.2-1} In the variable B of RG2 (2.14), the Gaussian variable of CRE (3.27) after p.267's scaling A_k′ = g_kA_k (p.267 l.42; A_k′ = (1/i)log V_k′, p.267 l.28), p.268 l.18 prints the test sup|A_k(b)| < δ_k, i.e. |B(b)| < δ_k, with δ_k = (A₁/A₀)ε_k = A₁ĝ_k(log ĝ_k^{−2})^{p₀}, at ĝ_k in the tube (#MD2.0.1.7; p.265 l.39 prints "δ_k = g_kA₁/A₀p₀(g_k)"; (3.19) uses ε_k = (A₀/A₁)δ_k).
{#MD2.4.11.2-2} Since g_k < 1, the test gives g_k|B(b)| < δ_k, which is the form of the first step's printed test |A| < g₀^{−1}δ₀ on the scaled variable ((1.18), p.250 l.29).
{#MD2.4.11.2-3} Step 2 uses only g_k|B| < δ_k, i.e. |B| < δ_k/g_k ≤ r_k (#MD2.0.3.35-2), as an upper bound on the support: with ℓ := log g_k^{−2} and t := log(g_k²/ĝ_k²) ≥ 0, δ_k/g_k = A₁(ℓ + t)^{p₀}e^{−t/2} ≤ A₁ℓ^{p₀}e^{(p₀/ℓ − 1/2)t} ≤ r_k for ℓ ≥ 2p₀, that is for g_K small, so (b)–(f) hold.
{#MD2.4.11.2-4} No other property of the threshold is used: the large-field regions are paid by LFR II p.381's printed factor (D2.0(5)(f) *Payment*), not by a Gaussian tail computed here.
{#MD2.4.11.2-5} So on the support, for every component Y and its neighbourhood: g_k|B|_Y < δ_k, |B′|_Y ≤ C₁^{RG2}g_k|B|_Y < C₁^{RG2}δ_k =: b_k (RG2 (1.20), valid since δ_k < ε₁^{RG2} for g_K small), and x_k := δ_k/ε₁^{RG2} ≤ 1/2 bounds g_k|B|_Y/ε₁^{RG2}.
{#MD2.4.11.2-6} All three are O(g_k(log g_k^{−2})^{p₀}), uniformly in k ≤ K for g_K small (g_k ≤ (1+β₀)g_K, CRE (2.6)–(2.7)).
{#MD2.4.11.2-7} This agrees with D2.1(4)'s *The hypothesis* (|B′| < O(1)ε_k from (3.14)) and sharpens its constant.

{#MD2.4.11.3} *(c) The per-slot bounds (at the complex data of (7)'s domain).* Let the background be 𝐔 = e^{iηa′}U_{k+1} in D(k+1)(iii)'s domain, C a square (the target's C), and assume that the hull I(G) with its allowance lies in Ω_k, where D(k+1)(iii)'s radius is ≤ Lα_{1,k} ((4)(f); on Ω_n∖Ω_{n+1} with n < k it is α_{1,n}L^{k−n}, not small), and that 20c_π′M‖a′‖_∞ ≤ 1 there (D2.2(6)(d) *Arcs*; true for g_K small since α_{1,k} = g_kC₁(log g_k^{−2})^{q₁} → 0 with L, M fixed, and implied by (12)(d)'s c_π′α_{1,k+1}·41M/L ≤ ν_r/16);
{#MD2.4.11.3-1} groups whose hull leaves Ω_k are older-layer groups ((5) *Older layers*), left with the kind (γ).
- {#MD2.4.11.4} (α) Pure loop groups: D2.1(4)'s Claim with the merged-arc constant, ‖Y_G(B)‖ ≤ ∏_{Y∈G}(|B′|_Y/ε_H)e^{−(κ_s−3)#(Y)} pointwise in B, hence ≤ (b_k/ε_H)^{n(G)}e^{−(κ_s−3)#(G)} on the support.
  {#MD2.4.11.4-1} The factor per component is the Schwarz factor 1/T_Y with T_Y = ε_H/|B′|_Y; the decay per cube is Cauchy's e^{−(κ_s−1)} in s(Δ) less e^{1} for the 𝐇-transports (|B′|_Y ≤ ε_H, c_π′c_CM4B₀e^{16κ_s}ε_H ≤ 1) and e^{1} for the a′-transports (20c_π′M‖a′‖_∞·length ≤ #(G) + n(G) by D2.2(6)(d), absorbed as e^{−(κ_s−3)#(Y)}·e^{n(G)}, the e^{n(G)} going into the per-component constant below).
- {#MD2.4.11.5} (β) Groups with old insertions (D2.2(4)(e)–(f), (6)(d)–(e)): Y_G is the s-derivative of the ordered product along I(G) of the touched old insertions W ∈ 𝔅(G) and the transports, and the Schwarz lemma in t_Y on the polydisc |s(Δ)| ≤ e^{κ_s}, |t_Y| ≤ T_Y gives ‖Y_G‖ ≤ ∏_{Y∈G}(1/T_Y)e^{−(κ_s−3)#(Y)}·∏_{W∈𝔅(G)}sup_{polydisc}‖Y_W‖, with 1/T_Y = max(|B′|_Y/ε_H, 16B₀e^{16κ_s}|B′|_Y/(min(β,1)α_{1,k}), C′B₀e^{16κ_s}|B′|_Y/(min(β,1)α_{0,k})) ≤ C_Tb_k/ᾱ_k ((4)(f) *T_Y*; (6)(e) *The curvature conditions*;
  {#MD2.4.11.5-1} ᾱ_k = min(α_{0,k}, α_{1,k}), C_T := max(1/ε_H, 16B₀e^{16κ_s}/min(β,1), C′B₀e^{16κ_s}/min(β,1))), and the 𝐇-transports as in (α) (𝐇 vanishes off the components).
  {#MD2.4.11.5-2} The a′-transports differ from (α): I(G) is the smallest arc containing the components' bonds and the intervals of the touched W, so its gaps reach the touched intervals inside X_W and have length up to 2(diam Y + diam X_W); by D2.2(6)(d) *Arcs*, length(I(G)) ≤ 20Σ(diam + 1) over the components and the touched W, so under 20c_π′M‖a′‖_∞ ≤ 1 the a′-cost is ≤ exp(#(G) + n(G) + Σ_{W∈𝔅(G)}20c_π′M‖a′‖_∞(diam X_W + 1)) ≤ e^{#(G)+n(G)}·∏_{W∈𝔅(G)}e^{(ν_r/16)(σ_k(W)+1)} once c_π′α_{1,k+1}·20M/L ≤ ν_r/16 (diam X_W ≤ (M/L)σ_k(W), (12)(d)) and 20c_π′M‖a′‖_∞ ≤ ν_r/16 (the +1 terms);
  {#MD2.4.11.5-3} the factor e^{(ν_r/16)σ_k(W)} is paid from W's reserve weight ν_rσ_k(W) inside (ii-w) ((12)(b); the budget of (12)(e)), never from e^{θ_k(W)}, which D2.4(3) reserves for the Q_k-shares; the constant e^{ν_r/16} per touched W is inside the touched W's piece factor C_pc′ (#MD2.4.12.27-6, #MD2.4.12.28-0).
  {#MD2.4.11.5-4} The polydisc points e^{iη(𝐇(s,tB′) + a″)}U_{k+1} lie in D(k)(iii)'s domain by (4)(f)'s chain condition (with CRE p.277's margin, CRE p.277's 𝐇-decay, RG2 p.5's all-norms bound on the older layers, (6)(e));
  {#MD2.4.11.5-5} they are general complex configurations off the frame family (for a″ ≠ 0 they are, already at t = 0, not gauge transforms of any frame point, by a dimension count: frame points with their gauge orbits form an analytic image of dimension at most (#level-k bonds + #fine sites)·dim G), so D(k)(iii) applies there only in its covariant form (*The ω-clause at complex configurations*), with the D(k)-level mismatch c₀^{(k)}(𝐔_pd) of the evaluation point 𝐔_pd itself.
  {#MD2.4.11.5-6} That c₀^{(k)} depends on (s, t, B′), so D(k+1)(iii)'s covariant clause does not absorb it.
  {#MD2.4.11.5-7} Evaluating each touched W at the frame point U^{rep}_k(V_k) is valid at a″ = 0 only.
  {#MOMGD.1} *The points with a″ ≠ 0.* Every bound used at these points is a bound on 𝒟^{sub}_{k+1} (SW §3): the dev complex-data clause holds there (SW closure §6), and the att, lw and wrap bounds are stated there (D2.6 closure §5.0).
  {#MD2.4.11.5-9} So a″ ∈ 𝒟^{sub}_{k+1}, whose imaginary part is at most α_{1,k+1}L^{−(k+1)} per fine bond on every layer (D2.6 closure §5.4), and 𝐔_pd lies in 𝒟^{sub}_k by (4)(f)'s chain condition and SW §3(b3).
  {#MD2.4.11.5-10} *The ω-free members.* A group of the dev species contains only dev members (D2.6 closure 2.1 *Merged groups*: a group with an inherited att, lw or wrap member takes that species).
  {#MD2.4.11.5-11} These do not depend on ω: those made at steps ≥ 2 by D2.6 closure 4.2(iii) (a member that depends on ω is att, wrap or of an inherited species), and those made at step 1 by IT-1 note §3d(4) (c⁰_W depends only on U₁ inside Q_W).
  {#MD2.4.11.5-12} For them c₀^{(k)} rotates no slot value, and the plain D(k)(iii) bound at 𝐔_pd applies.
  {#MD2.4.11.5-13} *The ω-dependent members (att, lw, wrap): the size of c₀^{(k)} on 𝒟^{sub}.* Step 8's size bound is run at 𝐔_pd over its real reference: a first factor bounded by the telescoping over the hierarchical levels, and v₁ at the complex datum B′₀.
  {#MD2.4.11.5-14} On the layer j only the levels below j enter, as in Step 8's older-layer run (#MOMGD.33).
  {#MD2.4.11.5-15} The imaginary part of 𝐔_pd is at most α_{1,k}/2 + α_{1,k+1}/L ≤ α_{1,k} per fine bond in η_k-units: min(β,1)α_{1,k}/2 from 𝐇(s, tB′) by (4)(f), decaying off Ω_k, and α_{1,k+1}/L from a″.
  {#MD2.4.11.5-16} So the telescoping gives 2dα_{1,k}L^{j−k}(1 + o(1)) on the layer j.
  {#MD2.4.11.5-17} The older-layer form 3dL^{j−k}sup|𝐇_k(B′₀)|, with |𝐇_k(B′₀)| ≤ 4B₀e^{16κ_s}|B′₀| (#MD2.2.6.156) and |B′₀| ≤ 2(d+1)α_{1,k}(1 + o(1)) (Step 8 *The reference Ū*), gives the rest.
  {#MD2.4.11.5-18} Hence |log c₀^{(k)}| ≤ C_{c₀}α_{1,k}L^{j−k}(1 + o(1)) on the layer j, with C_{c₀} := 2d + 24d(d+1)B₀e^{16κ_s}.
  {#MD2.4.11.5-19} The step-level c₀^{(k+1)}(𝐔) at 𝐔 = e^{iηa″}U_{k+1} ∈ 𝒟^{sub}_{k+1} obeys the same bound.
  {#MD2.4.11.5-20} On D(k+1)(iii)'s full domain the imaginary part on the layer j is α_{1,j}L^{k−j} in η_k-units, and the same bound is O(dα_{1,j}), which the margin r_{ω,j}2^{−(k+1−j)} does not cover; so for the att, lw and wrap species the full domain carries no clause (D2.6 closure §5.0).
  {#MD2.4.11.5-21} *The charge.* The rotation between G's slot values in the frame of D(k+1)(iii)'s covariant clause and the slot values that W's covariant clause needs at 𝐔_pd is the product of c₀^{(k)}(𝐔_pd)^{−1}, c₀^{(k+1)}(𝐔) and ŵ (w_tot = c₀(𝐔)ŵ, #MD2.2.4.20).
  {#MD2.4.11.5-22} It is composed with #MD2.2.4.21's convention Σ|Z_j|, with conjugations 1 + o(1).
  {#MD2.4.11.5-23} Half of #MD2.2.6.175's margin r_{ω,j}2^{−(k+1−j)} goes to ŵ (#MD2.2.6.176 with 32 in place of 16), and half goes to the two c₀ factors.
  {#MD2.4.11.5-24} The latter needs 8c_GC_{c₀}α_{1,k}L^{j−k}(|σ_{j,0}|/r_{ω,j} + 1) ≤ 2^{−(k+1−j)}/2, that is 32c_GC_{c₀}(2/L)^{k−j}α_{1,k}(|σ_{j,0}|/r_{ω,j} + 1) ≤ 1.
  {#MD2.4.11.5-25} By #MD2.2.6.177's estimate with α_{1,k} in place of h_k, the left side is ≤ Cg_k^{1/2}(log g_k^{−2})^{q₁+p₀}(1 + β′(k−j))^{1/4}(1 + log(1+β′(k−j)))^{p₀}(2/L)^{k−j}, which is small uniformly in k, K and j for L ≥ 4 and g_K small.
  {#MD2.4.11.5-26} So W's slot values at 𝐔_pd lie in its radius-r^{(k)}_{ω,j} polydiscs whenever G's lie in the radius-r^{(k+1)}_{ω,j} polydiscs.
  {#MD2.4.11.5-27} At j = 0 (the step-1 species' ω₀), Σ_k2C_{c₀}α_{1,k}L^{−k} ≤ 2C_{c₀}(1+β₀)²α_{1,1}, by α_{1,k} ≤ (1+β₀)²k^{1/2}α_{1,1} (CRE (2.6)–(2.7)) and Σ_kk^{1/2}L^{−k} ≤ 1.
  {#MD2.4.11.5-28} So D2.6 closure §5.0's sub-polydisc 𝒟^{sub}_{ω,0} holds with C_w + 3d + 2C_{c₀} in place of C_w + 3d (an amendment of that section).
  {#MD2.4.11.5-29} This rests on Step 8's size bound in its per-layer form, #MD2.2.6.177, (4)(f)'s chain condition, SW §3(b3), the species rules of D2.6 closure 2.1 and 4.2(iii), and IT-1 note §3d(4).
  {#MD2.4.11.5-30} So each touched W is bounded by D(k)(iii)'s complex-data clause — the inductive input of (4) *Complex data*, (5) and (9), proved on the sub-domain (SW closure §6): for a dev W, e^{θ_k(W)}‖Y_W‖ ≤ b_W(Dev_{Q^#_W} + a*_W + j*_W) ≤ β_W(Δ^{(k)}_W + C_ah_kη_k^{−2}·… ) in the notation of (5), and by (5) *At complex data* its size is ρ̃_k·O(ᾱ_kλ_R(1 + (log g_k^{−2})^{(q₁−q₀)₊})) = O(ρ_kλ_R(1 + (log g_k^{−2})^{(q₁−q₀)₊})) per insertion (λ_R = C₁/C₀, #MD2.4.5.3), away from older layers ((5) *Older layers*); att/lw/wrap species are D2.6's.
  {#MD2.4.11.5-31} So a group of kind (β) is bounded by (C_Tb_k/ᾱ_k)^{n(G)}e^{−(κ_s−3)#(G)}·∏_{W∈𝔅(G)}e^{−θ_k(W)}·[e^{θ_k(W)}‖Y_W‖]_{polydisc}, and the old weights e^{θ_k(W)} are not consumed (D2.4(3)).
- {#MD2.4.11.6} The sup. ‖𝒳_M‖_sup ≤ ∏_{i∈J(M)}(bound of G_i).
  {#MD2.4.11.6-1} Every factor above is uniform in k and on the domain.

{#MD2.4.11.7} *(d) The count check for the exponential costs.* (10)(b) charges e^{81A} per π_{k+1}-cube of D′ and e^{(5+3λ_L)κ} per wall-component of D beyond the first, and nothing else inside D′.
{#MD2.4.11.7-1} By (a), #_{k+1}(D′) ≤ 81#_k(D) ≤ 81c_D#(G_M), #(G_M) := Σ_i#(G_i), and m(M) − 1 ≤ c_D#(G_M) ((a)).
{#MD2.4.11.7-2} The slots pay e^{−(κ_s−3)#(G_M)} and the e^{n(G)} of (c).
{#MD2.4.11.7-3} The 𝐃 ≠ ∅ odd terms of (f) cost e^{243A#_{k+1}(D′)} in place of e^{81A#_{k+1}(D′)} (3A in (10)'s counting), so
  {#MD2.4.11.8} e^{243A#_{k+1}(D′)}e^{(5+3λ_L)κ(m(M)−1)}·∏_ie^{n(G_i)}e^{−(κ_s−3)#(G_i)} ≤ e^{−κ_s′#(G_M)}, κ_s′ := κ_s − 4 − (5+3λ_L)c_Dκ − 19683c_DA,
{#MD2.4.11.9} and κ_s′ ≥ κ_s/2 once κ_s ≥ 8 + 2(5+3λ_L)c_Dκ + 39366c_DA.
{#MD2.4.11.9-1} With λ_L ≤ L/2, c_D ≤ 81 ((a)) and (10)(b)'s 324A ≤ δλ_Lκ (an a-priori bound on A, which is fixed after M) this is a condition κ_s ≥ 81(10 + 3L)κ + O(κ) on RG2's κ_s, which is chosen after κ and before M (δ₁M ≥ κ_s, D2.1(4) *Conditions used*), so it is in Bałaban's order of choices.
{#MD2.4.11.9-2} The remaining decay e^{−(κ_s/2)#(G_M)} is per π_k-cube of the components; per π_{k+1}-cube of D′ it is at least e^{−κ_s/(162c_D)}.
{#MD2.4.11.9-3} This is what Step 3 spends on the entropy of the components and Step 4 compares with w_t over the extent of D′.

{#MD2.4.11.10} *(e) The size check in powers of g (the count-check of the amplitudes).* (S) needs S_𝒢 of size ρ_{k+1} = C_ρg_{k+1}²(1+r_{k+1})⁴, and ρ_k ≤ (1+β₀)⁶ρ_{k+1} (D2.0(3)).
{#MD2.4.11.10-1} From (b)–(c), per component the sup factor is b_k/ε_H or C_Tb_k/ᾱ_k, both O(g_k(log g_k^{−2})^{p₀}) resp. O((log g_k^{−2})^{p₀−q}) with q = min(q₀,q₁); per touched old insertion it is O(ρ_k(log)^{(q₁−q₀)₊}).
{#MD2.4.11.10-2} So:
- {#MD2.4.11.11} a slot of kind (β) is O(ρ_k·(log g_k^{−2})^{p₀−q+(q₁−q₀)₊}) at least, which is ≤ Cρ_{k+1} when q ≥ p₀ + (q₁−q₀)₊, i.e. (with CRE p.277's margin's q₀, q₁ ≥ p₀) iff q₁ ≤ q₀ or 2q₀ ≥ p₀ + q₁; with (6)(ζ)'s entailment q₀ ≤ q₁ the condition is 2q₀ ≥ p₀ + q₁, and otherwise a power of log of the kind recorded in (5) *At complex data* and (9)'s polylog item remains.
  {#MD2.4.11.11-1} The amplitude of a (β) slot is the old insertions', not a new ρ_{k+1}: (12)(f) carries this as a recursion in k;
- {#MD2.4.11.12} a pure loop slot with n(G) ≥ 2 is O(b_k²) = O(g_k²(log g_k^{−2})^{2p₀}) ≤ (eC₁^{RG2}/ε_H)²ρ_k/C_ρ, since δ_k² ≤ g_k²r_k² ≤ ρ_k/C_ρ (#MD2.4.11.2-3);
- {#MD2.4.11.13} a marked polymer with two or more slots is a product of such factors, each O(b_k) or O(ρ_k·polylog) and ≤ 1, two of them O(b_k) at least;
- {#MD2.4.11.14} **the single-slot, single-component pure loop polymers** (|J(M)| = 1, G = {Y}, kind (α)) have ‖𝒳_M‖_sup = O(b_k) = O(g_k(log g_k^{−2})^{p₀}) only, which is not O(ρ_{k+1}): a factor 1/g_k short.
  {#MD2.4.11.14-1} These are the first-order fluctuations of the leading word (D2.1(3) *The first-order term*: linear in A_k, odd), which D2.0(5)(d) treats as zero-mean at first order and of size g_k² at second order.
  {#MD2.4.11.14-2} Within (10) the sup bound cannot see this.
  {#MD2.4.11.14-3} The parity argument that recovers it is (f).

{#MD2.4.11.15} *(f) Parity: the single-component slots.* *Scope.* ω′ = 0, which is D2.4(4)'s scope for the dev groups: at ω′ ≠ 0 the action of CRE (3.27) contains the source term −⟨A, C*Δ^{(k)}Cσ_k⟩ (D2.2(5)(b), (5)(e), (6)(b6)), linear hence odd in the integrated field, and the argument below fails; such polymers are att (D2.6).
{#MD2.4.11.15-1} And Y₀ away from older layers: there the potentials of (3.27)'s localised action are the terms of 𝐄_k and of 𝐑_k, which have Lemma 2's structure ((1.42), (1.43), (1.36), (2.18)) — for 𝐑_k by CRE p.276, "The expression determined by 𝐑_k is treated in exactly the same way as 𝐄_k, except the second renormalization connected with the coupling constant renormalization counterterm, which is not needed here", with the analyticity space (I.6.34) for Y ⊂ Λ_{k+1} (p.276): Bałaban's claim, read in the form (i′) of CRE p.279's same-way clause.
{#MD2.4.11.15-2} The boundary-type terms — 𝐁_k, A(g_k^{−2}(·) − g_k^{−2}, ·) and V^{(k)}(S_{k+1}) — are analytic jointly in (A_k, A) only on O6's 𝒫_k^m and bounded on its 𝒫_k^{3/4}, which g_k sup|B| < r^{an}_k gives (#MD2.2.6.170-3; r^{an}_k of #T4.50, g_k times a power of log g_k^{−2}, D2.7 15.6(d), 15.7; (3.43)'s A-radius C₁p₁(g_k) is not used, O6 closure §7; so no Cauchy gain), and carry p.277's factor O(ε_k) at the consumers' points (#MD2.2.6.170-7).
{#MD2.4.11.15-2-1} They are localised at Λ_{k+1}ᶜ, Z_k and S_{k+1} (p.277: "supp(g_k^{−2}(·) − g_k^{−2}) ⊂ Z_k", "at least one localization in S_{k+1}"), and belong to (5)'s older-layer item (CRE pp.276–277 read).
{#MD2.4.11.15-3} Fix M with J(M) = {i}, G_i = {Y}, Y ⊂ Ω_k, no old insertion.
{#MD2.4.11.15-4} Split Y_G(B) = Y_G^{ev}(B) + Y_G^{od}(B) into its even and odd parts under B ↦ −B on the support (the support is symmetric: sup-tests).
- {#MD2.4.11.16} *The even part is O(δ_k²).* In the Claim's proof, t ↦ Y_G(tB′) is analytic for |t| ≤ T_Y = ε_H/|B′|_Y ≥ 2 with sup ≤ S_Y := e^{−(κ_s−3)#(Y)} (the polydisc bound), and Y_G(0) = 0, so Y_G(B′) = L(B′) + R with L linear in B′ (the s|_Y-derivative of D2.1(4) *First order*), ‖L(B′)‖ ≤ S_Y|B′|_Y/ε_H, and ‖R‖ ≤ S_YΣ_{n≥2}T_Y^{−n} ≤ 2S_Y(|B′|_Y/ε_H)².
  {#MD2.4.11.16-1} In B, B′ = B′_od + B′_ev with B′_od the odd part: by RG2 (1.19), B′ = g_kCB − hD̃(g_kCB) with C the linear operator of RG1 ("B′ = CB", D2.2(6)(b) *The operator C and B′*), so g_kCB is odd and B′_ev = −[hD̃(g_kCB)]_ev; hD̃(·) is analytic for g_k|B| < ε₁^{RG2}, vanishes to second order at 0 (RG1 p.267: D̃ "has an expansion beginning with quadratic terms";
  {#MD2.4.11.16-2} only h is linear) and is bounded there by (C₁^{RG2} + O(1))ε₁^{RG2} ((1.20)), so Cauchy's remainder estimate gives |hD̃(g_kCB)|_Y ≤ 2(C₁^{RG2} + O(1))x_k²ε₁^{RG2} = C_evδ_k² for x_k ≤ 1/2, C_ev := 2(C₁^{RG2} + O(1))/ε₁^{RG2} (the C here is (1.19)'s linear operator, not (1.3)'s nonlinear C).
  {#MD2.4.11.16-3} Hence |B′_ev|_Y ≤ C_evδ_k².
  {#MD2.4.11.16-4} Hence ‖Y_G^{ev}‖ ≤ ‖L(B′_ev)‖ + ‖R‖ ≤ S_Y(C_ev/ε_H + 2(C₁^{RG2}/ε_H)²)δ_k² =: c_evδ_k²S_Y on the support, and ‖Y_G^{od}‖ ≤ (C₁^{RG2}δ_k/ε_H + c_evδ_k²)S_Y. δ_k² ≤ (A₁²/C_ρ)ρ_k ≤ (A₁²(1+β₀)⁶/C_ρ)ρ_{k+1}: the even part is ρ_{k+1}-size.
- {#MD2.4.11.17} *The odd part vanishes in the plain term.* The term (𝐃, P, Z₀, Z) = (∅, ∅, D, D′) of (10)(b) is (2.14) with 𝐃 = P = ∅: ∫dμ₀(X)|_Ze^{−½⟨Γ_kX, C^{(k)}Γ_kX⟩}∫dμ_{C^{(k)}(Z₀,σ(Z))}(B)e^{−⟨B,Γ_kX⟩}χ_{k,Y₀}(B)𝒳_M(B) (RG2 (2.14), p.15; here Z = Z₀′ so no s, σ).
  {#MD2.4.11.17-1} The joint density in (X, B) is exp of a quadratic form (two centred Gaussian densities and the bilinear coupling e^{−⟨B,Γ_kX⟩}; a quadratic form is even whether or not its operators are symmetric — RG2 p.15 says they are not), even under (X, B) ↦ (−X, −B); χ_{k,Y₀} is even; 𝒳_M = Y_G depends on B only.
  {#MD2.4.11.17-2} So the integral of Y_G^{od} vanishes, and the plain term is bounded by ‖Y_G^{ev}‖_sup·e^{A#_{k+1}(D′)} ≤ c_evδ_k²S_Ye^{A#_{k+1}(D′)}.
- {#MD2.4.11.18} *The odd part in the other terms.* For (𝐃, P, Z₀, Z) with 𝐃 = ∅ the same symmetry kills Y_G^{od}: χ^c_{k,P} is even, and the s, σ, τ-structure of (2.14) does not touch B's sign.
  {#MD2.4.11.18-1} For 𝐃 ≠ ∅ the only non-even factor is exp[Σ_{Y′∈𝐃}τ(Y′)𝐕_k(Y′,B)], and with y(B) := Σ_{Y′}τ(Y′)(𝐕_k(Y′,B) − 𝐕_k(Y′,−B)) its odd part is e^{ΣτV(B)}·½(1 − e^{−y}), |½(1 − e^{−y})| ≤ |y|e^{|y|}.
  {#MD2.4.11.18-2} By (1.42), 𝐕_k(Y′,B) = ½⟨Q(Y′,B)B,B⟩ + 𝐕″_k(Y′,B).
  - {#MD2.4.11.19} The 𝐕″_k-part. 𝐕″_k(Y′, ·) is analytic on (1.34)'s disc |B| < ε₁g_k^{−1} on Y′ with |𝐕″_k| ≤ E_{Y′} := E₀ε₁C₁M^qe^{C₂κ₁}e^{−(1−2δ)κd_k(Y′)} there (RG2 p.11: "satisfies the bound (1.36)").
    {#MD2.4.11.19-1} Cauchy's estimate on t ↦ 𝐕″_k(Y′, tB), |t| < ε₁/(g_k|B|_{Y′}), bounds its homogeneous part of degree n by E_{Y′}(g_k|B|_{Y′}/ε₁)^n, so |𝐕″_k(Y′,B) − 𝐕″_k(Y′,−B)| ≤ 2E_{Y′}Σ_{n odd}x_k^n ≤ 4E_{Y′}x_k on the support (x_k ≤ 1/2, (b)).
    {#MD2.4.11.19-2} With Bałaban's radius |τ(Y′)| = 2e^{(1−3δ)κd_k(Y′)}/(ε₂α₆) (read off (2.18), p.16, and (2.26), p.17: the factor 2/|τ(Y′)| of (2.15) becomes ε₂α₆e^{−(1−3δ)κd_k(Y′)}; ε₂ is defined on p.19), |τ(Y′)|E_{Y′} = α₄e^{−δκd_k(Y′)} (ε₂α₆ = 2E₀ε₁C₁α₄^{−1}M^qe^{C₂κ₁}, p.19).
    {#MD2.4.11.19-3} So the 𝐕″-part of |y| is ≤ 4x_kΣ_{Y′∈𝐃}α₄e^{−δκd_k(Y′)} ≤ 4x_k·O(1)α₄#_k(Y₀) by (2.20)'s second line with (1.26) (each Y′ contains a cube of Y₀; 𝐃 may overlap, so |𝐃| is not bounded by #_k(Y₀)).
    {#MD2.4.11.19-4} This part is of the same form as the quadratic-form part below and is carried with it (the constant y_k).
  - {#MD2.4.11.20} The quadratic-form part (RG2 pp.10–11 and 16–17).
    {#MD2.4.11.20-1} Q(Y′,B) depends on B: it is the Taylor-remainder coefficient (1.40), ∫₀¹dt(1−t)∂²_{B′_μ(x)B′_ν(y)}[(1.38) at tB′], composed with B′ = B′(B) of (1.19) (p.10: "we expand (1.38) with respect to B′ up to the second order.
    {#MD2.4.11.20-2} The terms of zeroth and first order vanish, and the second order term is written as a quadratic form with coefficients given by second order derivatives"; the same for all terms of 𝐏^{(k)}, p.11, "possibly with other absolute constants").
    {#MD2.4.11.20-3} So Q(Y′, ·) is analytic on (1.34)'s disc, as 𝐕_k is (Lemma 2; (1.38) is analytic in B′ for e^{16κ₁}|B′| ≤ a₁ on Y, p.10, and (1.19) is analytic in B), and its matrix elements obey (1.43) there.
    {#MD2.4.11.20-4} Bałaban's (2.18)–(2.19), p.16: "The quadratic form in (1.42), after multiplication by |τ(Y)|, can be bounded by ½Σ_{b,b′⊂Y}α₄M^{−4}exp(−¼(κ₁−1)M^{−4}|Y| − (1/16)(κ₁−1)M^{−1}|b_− − b_−′|)|B(b)||B(b′)|", i.e. |τ(Y′)||Q(Y′,B,b,b′)| ≤ α₄M^{−4}q̂_{Y′}(b,b′) with q̂ the printed exponential, uniformly in B on the disc (the bound comes from (1.43), which Lemma 2 states on (1.34)); and (2.20): the sum over Y ∈ 𝐃 of these forms is ≤ ½O(1)α₄Σ_{b⊂Y₀}|B(b)|², "In fact the constant is small for κ₁ large, hence we can bound it by 1".
    {#MD2.4.11.20-5} Cauchy's estimate on t ↦ Q(Y′,tB)_{bb′}, |t| ≤ ε₁/(2g_k|B|_{Y′}) (inside the disc), gives |τ(Y′)||Q(Y′,B) − Q(Y′,−B)|_{bb′} ≤ 2α₄M^{−4}q̂_{Y′}(b,b′)Σ_{n odd}(2x_k)^n ≤ 8x_kα₄M^{−4}q̂_{Y′}(b,b′) for x_k ≤ 1/4.
    {#MD2.4.11.20-6} The odd part of ½⟨Q(Y′,B)B,B⟩ under B ↦ −B is ½⟨(Q(B) − Q(−B))B,B⟩ (the form ⟨·B,B⟩ is even), so by (2.19)–(2.20) the quadratic-form part of |y| is ≤ 8x_k·½O(1)α₄Σ_{b⊂Y₀}|B(b)|² ≤ 8x_kα₄·4M⁴r_k²#_k(Y₀) on the support (|B(b)| < δ_k/g_k ≤ r_k, (b)).
    {#MD2.4.11.20-7} With the 𝐕″-part, |y| ≤ y_k#_k(Y₀), y_k := 4α₄x_k(8M⁴r_k² + O(1)) = O(g_k(log g_k^{−2})^{3p₀}), uniformly in k ≤ K for g_K small.
    {#MD2.4.11.20-8} So the factor |y|e^{|y|} of the odd part is ≤ y_k#_k(Y₀)e^{y_k#_k(Y₀)} ≤ y_k(L⁴/A)e^{2A#_{k+1}(Z)} once y_k ≤ A/L⁴ (g_K small), B-independent, and (2.15)–(2.26) go through for the odd part with this constant in front: every term with 𝐃 ≠ ∅ carries, besides (10)(c)'s bound with ‖Y_G^{od}‖_sup, the factor c_ody_ke^{2A#_{k+1}(Z)}, c_od := L⁴/A.
    {#MD2.4.11.20-9} Its absorption in (10)(e) is the counting inequality with 3A in place of A: condition 972A ≤ δλ_Lκ.
    {#MD2.4.11.20-10} The product ‖Y_G^{od}‖_sup·c_ody_k ≤ (C₁^{RG2}/ε_H + c_evδ_k)δ_k·(L⁴/A)4α₄(8M⁴r_k² + O(1))δ_k/ε₁^{RG2}·S_Y = O(g_k²r_k⁴)S_Y ≤ c_odd′ρ_kS_Y (g_k²r_k⁴ ≤ ρ_k/C_ρ, #MD2.0.3.35-2): ρ_{k+1}-size.
- {#MD2.4.11.21} *Consequence for (S).* Every marked polymer of kinds (α)–(β) has |H̃(M)| ≤ c_Mρ_{k+1}·(the polylog factor of (e)'s first bullet, absent iff 2q₀ ≥ p₀ + q₁; for kind (β) the amplitude is the touched insertions', (e), carried by (12)(f))·e^{−(κ_s/2)#(G_M)}·e^{−r_κ·d_{k+1}(M;D′)}·e^{(5+3λ_L)κ·0} with the costs of (d) already paid, c_M depending on A₁, C₁^{RG2}, ε_H, C_T, c_ev, c_od, α₄, M, L, A and Bałaban's constants only, uniformly in k ≤ K for g_K small;
  {#MD2.4.11.21-1} for the single-component slots this is the sum of the plain term (even part, c_evδ_k²S_Ye^{A#_{k+1}(D′)}) and of the O(ϑ) terms (even part with (10)(b)'s factors; odd part with the extra c_ody_k).
  {#MD2.4.11.21-2} The sum over polymers is Step 3's.

{#MD2.4.11.22} *(g) Inputs from outside (11).* D(k)(iii)'s complex-data dev clause for the touched insertions, on which (c)(β) rests: WILSON_IT1_SW_CLOSURE_2026_10_24.md (6b)–(6c), on its §3 sub-domain, with its §1 collar. The polylog factor of (e) is absent under q₀ = q₁ > p₀ (SW closure §2), since then 2q₀ − p₀ − q₁ = q₀ − p₀ > 0. D2.6's kinds (γ) and species (including the ω′ ≠ 0 polymers, where (f)'s parity fails), and (5)'s older-layer complex-data size, including the arcs that leave Ω_k ((c)) and CRE's boundary-type potentials ((f) *Scope*): WILSON_IT1_D26_CLOSURE_2026_10_24.md §2–§4.

### (12) Step 3 of (S): The Rooted Sums over the Linked Families {#MSD2.4.12}

{#MD2.4.12.1} *(a) The size σ_{k+1} (the definition (3) uses).* V4's σ(W) = n(W) + |ℋ(W)|/(LM): by V4 (c4-6-1) and the sentence before it, n(W) is the sum of N₁ over the roots and over every constituent domain of every occurrence in W's cluster list, with multiplicities, a *cube* count, and |ℋ(W)| is the number of fine traversals of the hull, so |ℋ(W)|/(LM) is the hull length in units of the π₁-cube side LM (the footprint F(W) of LM-cubes has |F(W)| ≤ C𝔰(W), V4 Lemma c4-6-env(a)).
{#MD2.4.12.1-1} The consistent step-(k+1) size is
  {#MD2.4.12.2} σ_{k+1}(𝒢) := #_{k+1}(𝒢) + n_{k+1}(𝒢)/M,
  {#MD2.4.12.3} #_{k+1}(𝒢) the number of π_{k+1}-cubes of the constituents' domains (as in (3): marked vacuum domains, slot supports, the supports of the vacuum-link clusters of (c), the domains of the old groups and of the members of the merged old occurrences, with multiplicity) and n_{k+1}(𝒢) the number of step-(k+1) traversals of C in I(𝒢); M is the π_{k+1}-cube side in step-(k+1) units, so the arc term is the hull length in cube sides, as V4's.
  {#MD2.4.12.3-1} With this σ: (3)'s *decay statements survive* bullet holds as written (its second sentence is the definition); the vacuum weight θ_vac ≤ c#_{k+1} ≤ cσ_{k+1} holds; (7)'s and D2.3(4)(Z-d)'s a_min is ν/(32LM), since n_ins(𝒢) ≤ L·n_{k+1}(𝒢) ≤ LMσ_{k+1}(𝒢); and the reference-gas requirement θ_ref ≤ (ν/32)σ_{k+1} is the one (f) delivers.
  {#MD2.4.12.3-2} An old group W and each member of a merged old occurrence contributes #_{k+1}(X_W), the number of π_{k+1}-cubes of its domain as a set.
  {#MD2.4.12.3-3} (8)'s transport condition is c_π′α_{1,k+1}M ≤ ν/64 (n_{k+1}(𝒢) ≤ Mσ_{k+1}(𝒢)).

{#MD2.4.12.4} *(b) The form of (S) that the induction needs: the reserve and extent weights of D(k)(ii)–(iii) and the tail weight w_t.* A merged old member W of a step-(k+1) group contributes its domain, its arc and the gap to its neighbours to σ_{k+1}(𝒢), and so to the fresh weight e^{θ_{k+1}(𝒢)} ≤ e^{νσ_{k+1}(𝒢)/16}, and its extent to X(𝒢) and t(𝒢).
{#MD2.4.12.4-1} The class norm ν_n^{(k)} = Σ_{W∋n}e^{θ(W)}‖Y_W‖ has no decay in σ_k(W) or in the extent of W, so these are paid by weights inside the per-traversal sums of D(k)(ii)–(iii).
{#MD2.4.12.4-2} V4 supplies both weights at step 1: Lemma c5-5-8(a) (pins for the t-family) gives sup_ΔΣ_{W: Δ∈F(W)}e^{2νσ(W)}K_χe^{θ°(W)}b̄_W ≤ ε̄_t and the same per fine traversal n ∈ ℋ(W), from its first display, which carries e^{4νσ(W)}M_Λ(W) with the first-order root weight ρ_t (M_Λ(W) = (1/k(W)!)∏_{Z∈𝒜(W)}ρ_tm(Z)∏_j|Φ|^+_Λ(𝔠_j), V4 Lemma c5-5-3, with m(Z) = ε_*e^{−λ_*ℓ₁(Z)} of Lemma c5-5-2, and |Φ|^+_Λ the incompatibility-tree sum of the m(D_i) (Lemma c5-5-6): a positive weight of the field-independent geometry, "defined without reference to the source data" (Lemma c5-5-3), so these pins hold at every background, real or complex;
{#MD2.4.12.4-3} at complex 𝐔 the group bounds (c5-5-8) by M_Λ(W) hold with the extra factor e^{4C_U|ℋ(W)|ϱ₁} ≤ e^{C′𝔰(W)ϱ₁}, C′ := 4C_ULM, IT-1 §3e(3.9)), and the ρ-size pins per traversal and per cube are V4 (c4-6-5) (Lemma c4-6-2): sup_{n∈I_C}Σ_{W: n∈ℋ(W)}M(W)e^{4η𝔰(W)} + sup_{Δ∈π₁}Σ_{W: Δ∈F(W)}M(W)e^{4η𝔰(W)} ≤ Cρ (this is the base of (ii-w) and of the reference gas's c-version at k = 1); and V4 Lemma c5-5-8(b) gives σ(W) ≥ dist(Δ, C)/(C_FLM) for Δ ∈ F(W), C_F := A_E the envelope constant.
{#MD2.4.12.4-4} D(k)(ii) and (iii) contain these two weights (#MD2.0.3.32): for every step-k traversal n of C (traversal positions only; the cube positions are recovered by the box reduction, (e)) and with the per-insertion sizes of (ii) (real points; the dev clause with b_WDev) and of (iii) (complex data),
  {#MD2.4.12.5} (ii-w) Σ_{W∋n}e^{θ(W)}e^{ν_rσ_k(W) + ν_e·ext_k(W)}·(size of W) ≤ C_χρ̃_k·(the right side of (ii)/(iii) at n),
  {#MD2.4.12.6} with the *reserve* ν_r := ν, the *extent weight* ν_e := ν/(2C_box) (D2.6 closure §6.5's budget), and ext_k(W) := the least R ≥ 0 such that X(W) ∪ Q^#_W lies in the ℓ∞-ball of radius R π_k-cube sides about every traversal n of W's interval (for carried insertions, in the units of the step of production, as σ and θ, D2.0(3) *Units of carried groups*; both weights are then in those units too, and a step-(k+1) unit is L step-k units, which only helps below;
  {#MD2.4.12.6-1} the extent is measured in the step's own metric, so that the rate comparison (13)(a) reads ext_{k+1} ≥ C_boxt − 2, and C_box ≥ 4A_E, so that ν_e ≤ ν/8; A_E = 9(2R_e+1)⁴ ≥ 729 since R_e = ⌈2max(R_h,L)/(LM)⌉ ≥ 1, V4 Lemma c4-6-env, so SW closure's C_box ≥ 6 holds too).
  {#MD2.4.12.6-2} The dev species of (ii) is the one with the weights: wrap boxes do not lift, so the clause is stated for the dev parts only.
  {#MD2.4.12.6-3} The size σ_k is (a)'s at every step k ≥ 2 and V4's 𝔰 at k = 1.
  {#MD2.4.12.6-4} Consequences and base:
  - {#MD2.4.12.7} *Base, k = 1 (from V4 Lemma c5-5-8 and (5) *At step 1*).* By (E₁): X(W) ∪ Q_W lies within C_box(𝔰(W)+1) π₁-sides of every fine traversal of W, since the envelope is connected with at most A_E𝔰(W) cubes and contains the cubes of the hull (V4 Lemma c4-6-env (a)–(b) and its proof: 𝔈(W) = 𝔑_{R_e}(X(W) ∪ π₁(ℋ(W))) is connected under maximum-norm adjacency with |𝔈(W)| ≤ A_E𝔰(W), so any two of its cubes are at index distance ≤ A_E𝔰(W) − 1, and it contains X(W) and the cube of every traversal of ℋ(W)).
    {#MD2.4.12.7-1} The comparison box lies within C_boxLM𝔰 of n_f ((5) *At step 1*). Both hold once C_box ≥ A_E; C_box ≥ 4A_E is chosen, and it meets V4's own requirements on C_box, which hold for every C_box ≥ 74:
      {#MD2.4.12.7-1-1} *V4's C_box.* V4 needs diam(Q_W) ≤ C_boxLMn(W), where Q_W is the coordinate rectangle enclosing the roots, the cluster domains, their halos, ℋ(W) with its closing transport (the inverse background transport along ℋ(W)) and the bonds the coefficient consults; and, when n(W) < b/(4C_boxLM), Q_W within b/2 of a source contact and injectively liftable (V4 sec:c4-8-4, sec:c4-11-3, sec:c4-11-4). Distances below are ℓ∞, in fine units, in the lift.
      {#MD2.4.12.7-1-2} *The hull.* A component κ of the root/cluster graph with n_κ cubes has a wall-connected union of domains, of diameter < n_κLM, with its contacts within 2L of it; its hull has at most 17n_κLM traversals if short, and if long then n_C = 4s ≤ 16n_κLM (#MOMGD.14-1 to #MOMGD.14-3). A short ℋ(W) is the union of its components' hulls (V4 sec:joint-extraction), so |ℋ(W)| ≤ 17LMn(W).
      {#MD2.4.12.7-1-3} A whole-contour group has a long member hull or a class whose hulls cover at least n_C/2 positions, so s ≤ 17LMn(W)/2. The contour does not wrap (proof of V4 Lemma c4-6-env (a)), so two vertices of ℋ(W) are within min(|ℋ(W)|, s) ≤ 17LMn(W). Two domain points of distinct components κ, κ′ are joined through their contacts and ℋ(W), so they are within (n_κ + n_κ′)LM + 4L + 17LMn(W) ≤ 18LMn(W) + 4L; within one component they are within n_κLM.
      {#MD2.4.12.7-1-4} *The consulted bonds.* A host is a rectangle of at most 4 M-cubes per direction containing its base and its primitive's stencil (V4 eq:part1-potential-host, eq:c-probe-host), so R_h ≤ 4M and a halo lies within 2R_h ≤ 8M of its domain (V4 Lemma c4-6-env). The row sets, block-mean paths and plaquettes that enlarge Q_W (sec:c4-11-4) lie in hosts or in contour stencils, a contour stencil lies within 2L of its traversal (Lemma c4-6-env), and a Hessian stencil lies within 3L of its free bond (V4 Lemma c2-entry-range), a bond of a domain, a halo or a contour stencil.
        {#MD2.4.12.7-1-4-1} The closing path is the inverse interval (V4 sec:c4-4-3, the sentence defining L_f), so it adds no bonds. So every point of Q_W's content lies within R_Q := 8M + 4L of a domain or of a vertex of ℋ(W), and diam_∞(Q_W) ≤ 18LMn(W) + 4L + 2R_Q ≤ 19LMn(W), since LM ≥ 12L + 16M for L ≥ 54 and M ≥ 18 (#T1.3; M ≥ 8LM₂, V4 eq:c-standing-conditions).
      {#MD2.4.12.7-1-5} *V4's lifting constant.* V4's network (sec:c4-11-4) consists of the trees of the domains' cubes (at most N₁(D) − 1 edges per domain, each joining the centres of two wall-adjacent cubes, LM bonds), the incompatibility joins (domains sharing a cube or a wall, at most LM bonds; #domains − 1 per component suffice, since a component's incompatibility graph is connected, proof of V4 Lemma c4-6-env (b)), one path per component from a cube centre of its marked root to a contact, and ℋ(W).
        {#MD2.4.12.7-1-5-1} A contact lies within 2L of its root (Lemma c4-6-env) and a site within LM/2 of its cube's centre, in ℓ∞, so a contact path has at most 4(LM/2 + 2L) = 2LM + 8L bonds. With m ≤ n(W) components the non-contour edges total at most (n(W) − m)LM + m(2LM + 8L) ≤ 3LMn(W) (8L ≤ LM, M ≥ 8), and a depth-first traversal of a spanning tree has length at most 6LMn(W) + 2|ℋ(W)| ≤ 74LMn(W), since |ℋ(W)| ≤ 34LMn(W) (#MD2.4.12.7-1-2–#MD2.4.12.7-1-3). So V4's constant C is at most 74, and the traversal has the form C_liftLMn(W) + 2|ℋ(W)| of #GL3.13-2-1 with C_lift = 6, the non-contour edges.
        {#MD2.4.12.7-1-5-2} Under (eq:c4-8-9) and C_box ≥ 74, 74LMn(W) < b/4 < N_min/4 (N_min > 32b, V4 sec:c4-8-4), so V4's lift applies, the distances of #MD2.4.12.7-1-2–#MD2.4.12.7-1-4-1 are those of the lift, and the Euclidean diam(Q_W) is at most 2·19LMn(W) = 38LMn(W) (d = 4). Hence V4's requirements, C ≤ C_box and diam(Q_W) ≤ C_boxLMn(W) (so that Q_W lies within C_boxLMn(W) < b/4 of the source contacts it contains), hold for every C_box ≥ 74, and #T4.44's C_box = 4A_E = 2916 meets them.
    {#MD2.4.12.7-2} With ν_e := ν/(2C_box) (D2.6 closure §6.5), ν_e·ext ≤ (ν/2)(σ+1).
    {#MD2.4.12.7-3} So e^{ν_rσ + ν_e·ext} ≤ e^{νσ}e^{(ν/2)(σ+1)} = e^{ν/2}e^{(3/2)νσ}, and V4's e^{4νσ} pins cover it together with §3j(6)'s 2νσ and e^{θ°(W)} ≤ e^{νσ/16} (proof of V4 Lemma c5-5-8) and, at complex backgrounds, IT-1 §3e(4)'s e^{C′𝔰ϱ₁} ≤ e^{η𝔰/8} (IT-1 §3e(3.8); the factor at 𝐔 is IT-1 §3e(3.9)), leaving (5/16)νσ for the tail (D2.6 closure §6.5 *Budget*).
    {#MD2.4.12.7-4} At complex backgrounds (iii)'s rate (D2.6 closure §6.5 *(iii)'s complex rate*) is 61/16 with V4's θ°-booking, and with the weights 3/2 and §3j(6)'s 2 inside the sum it is 5/16 = η_w/η_V, not below η_w.
    {#MD2.4.12.7-5} At k = 1 the tail clause (ii-t) follows from §3a(6)'s split 𝔰³e^{η𝔰/8} ≤ (j+1)³e^{η/8}e^{−(31/8)ηj}e^{4η𝔰} ((5) *At step 1*), which spends the whole e^{4η𝔰}; with the reserve and extent weights and §3j(6)'s share inside the sum the same split, with θ° at V4's 1/16 and the complex 1/8, gives 𝔰³e^{(1/16 + 1/8 + 2 + 1 + 1/2)η𝔰} ≤ C(j+1)³e^{−(5/16)ηj}e^{4η𝔰}.
    {#MD2.4.12.7-6} So the tail weight is
    {#MD2.4.12.8} w_t := (t+1)³e^{−η_wt}, η_w := (5/16)η_V, D2.0(3)'s (#MD2.0.3.10); w_t enters D2.0(3), (5) and (6) only through W_t = Σ_{t′≥t}w_{t′}, its monotonicity, Σ_tw_t < ∞ and "W_t decays exponentially" ((6)(ζ)).
  - {#MD2.4.12.9} *It carries (as (5) *It carries*; traversal positions only).* An old W keeps σ, ext, θ and β_W in its production units; t^{(k+1)}(W) ≤ t^{(k)}(W) as before.
    {#MD2.4.12.9-1} A step-(k+1) traversal n′ is met by L step-k traversals, so (ii-w) at step k+1 for the real-point dev part of the carried insertions follows from (ii-w) at step k with the factor L^{−1}(ρ̃_k/ρ̃_{k+1}) of (6), unchanged (its L^{−2} is δ*'s, #MD2.4.6.2); for the complex-data part (the a*, j* terms of D(k)(iii)) the same count gives ρ̃_k/ρ̃_{k+1} without L^{−1}, so that part is not carried but bounded from production by complexified covariance (#MOMGD.5; WILSON_IT1_COMPLEX_COVARIANCE_2026_10_29.md §4); the cube form would carry with a factor growing with L (~L²) and is not inductive.
  - {#MD2.4.12.10} *New groups.* (ii-w) at step k+1 for the groups made at step k+1 is the statement (S-w) below, proved in (e)–(f): for every position p at step k+1,
    {#MD2.4.12.11} (S-w) Σ_{𝒢: p ∈ X(𝒢) or p ∈ I(𝒢)}e^{θ_{k+1}(𝒢) + ν_rσ_{k+1}(𝒢) + ν_e·ext_{k+1}(𝒢)}S_𝒢ℓ_{X(𝒢)} ≤ C_S′ρ_{k+1}·(1 + (log g_k^{−2})^{(q₁−q₀)₊}),
    {#MD2.4.12.12} with ext_{k+1}(𝒢) defined as above with Q^#_𝒢 = X(𝒢) ((5)).
    {#MD2.4.12.12-1} (S) of (7) is (S-w) restricted to t(𝒢) = t and is (13).
    {#MD2.4.12.12-2} (S-w) also contains the c-version (|c_𝒢| ≤ S_𝒢) that the reference gas needs.
  - {#MD2.4.12.13} *Order of the proof (not circular).* (e)–(f) first bound the sums with the weight e^{(ν/16 + ν_r)σ_{k+1} + ν_e·ext_{k+1}}S_𝒢ℓ without θ_{k+1}; the c-version then gives the Kotecký–Preiss condition for the reference gas with a°(𝒢) = (ν/32)σ_{k+1}(𝒢), hence θ_ref ≤ a° by FV Lemma 5.6, (5.17) and θ_{k+1} = θ_vac + θ_ref ≤ νσ_{k+1}/16 for κ ≥ κ_D ((3)); so e^{θ_{k+1}} ≤ e^{νσ_{k+1}/16} and (S-w) follows.

{#MD2.4.12.14} *(c) The vertices and the links (from D2.2(6)(c)–(d) and D2.3(3)).* A step-(k+1) group 𝒢 is a set of *vertices* v of three kinds, with its arc I(𝒢) (D2.2(6)(d)'s union of linked hulls); the touched insertions and the vacuum links are part of the marked polymer's vertex:
- {#MD2.4.12.15} an *M-vertex* v = (M, 𝔅(M), 𝒱(M)): a marked polymer M of kinds (α)–(β) ((11)(a)), its touched old insertions 𝔅(M) := ∪_i𝔅(G_i) (the old insertions in the products of its slot groups, D2.2(4)(e)), and its *vacuum links* 𝒱(M): the pairs (T, 𝒞) of a vacuum cluster 𝒞 incompatible with M's domain and a factor that chose it in D2.2(6)(c) *Localisation* (a scalar link T ∈ 𝒮 with M ∈ T, or T = {M} for e^{−δΨ(M)}), or a vacuum occurrence merged at M (D2.2(6)(c), D2.3(3);
  {#MD2.4.12.15-1} as in D2.2(6)(d), a pair (T, 𝒞) lies in 𝒱(M_T), M_T the first M of T in one fixed order, and a vacuum occurrence 𝒞 at the first M of S_𝔐(𝒞); its multiplicity, at most 2^s, is counted by 2^s ≤ e^{d(𝒞)} below).
  {#MD2.4.12.15-2} Activity: |e^{−Ψ°(M)}H̃(M)|·∏_{(T,𝒞)∈𝒱(M)}(the weight of 𝒞 below), e^{−δΨ(M)} entering only through its links (D2.2(6)(c) *Localisation*), and H̃(M) containing ∏_{W∈𝔅(M)}Y_W ((11)(c)(β)); the touched insertions are counted once, inside the vertex.
  {#MD2.4.12.15-3} Support: M ∪ ∪_{W∈𝔅(M)}X_W ∪ ∪_{𝒱(M)}supp 𝒞; interval int(v) := I(M), the smallest arc of C containing the arcs I(G_i) of M's slot groups (D2.2(6)(d), D2.1(4)'s rule), which contains the touched intervals (D2.2(4)(e): I(G_i) contains the intervals of the insertions in G_i's product).
- {#MD2.4.12.16} a *W-vertex*: an untouched old insertion merged by the second rule, the third rule (hit by an old occurrence of 𝒢) or the hull rule; activity sup‖Y_W‖ at (U_{k+1}, ω), where D2.2(4)(e) evaluates an untouched insertion, in D(k)(iii)'s domain (D2.2(4)(f), (6)(e)); support X_W; interval its own.
- {#MD2.4.12.17} a *Γ-vertex*: an old occurrence of the step-k reference gas hitting a W of 𝒢 (a W-vertex or a touched W ∈ 𝔅(M)); activity |φ_k(Γ)| with D2.3(3)'s 1/m!; support the members' domains; its intervals are the members' arcs J_{W′}, and its window is the union of the members' windows, each with the member's own diam_{W′}.
{#MD2.4.12.18} *The vacuum factors.* For a scalar link T ∈ 𝒮, x_T := ε_TδΨ_≥(T) is a sum over the 𝒞 incompatible with every M ∈ T, |x_T| ≤ Σ_𝒞2|φ^T(𝒞)|_sup, so Σ_T|x_T| ≤ Σ_𝒞2^s·2|φ^T|_sup ≤ 2cΣ_M#(M) ((2)(g); s = |S_𝔐(𝒞)| ≤ 9#(𝒞), D2.2(6)(c) *Left to D2.4*); in the expanded form of D2.2(6)(c) *Localisation* a cluster 𝒞 is chosen by n_𝒞 ≤ 2^s factors (the T ⊆ S_𝔐(𝒞) with |T| ≥ 2 and the e^{−δΨ(M)}, M ∈ S_𝔐(𝒞)), each with |e^{±y_𝒞} − 1| ≤ u_𝒞 := |y_𝒞|_supe^{|y_𝒞|_sup}, |y_𝒞|_sup ≤ 2|φ^T(𝒞)|_sup, so the sum over the nonempty sets of factors choosing 𝒞 is (1 + u_𝒞)^{n_𝒞} − 1 ≤ n_𝒞u_𝒞e^{n_𝒞u_𝒞};
{#MD2.4.12.18-1} the factors e^{n_𝒞u_𝒞}e^{|y_𝒞|} are bounded over all 𝒞 ≁ M by exp(Σ_{𝒞≁M}(2^s + 1)u_𝒞) ≤ e^{5c#(M)} ((2)(g): (2^s + 1)u_𝒞 ≤ 4e^{2c}e^{d(𝒞)}|φ^T(𝒞)|_sup, and 4e^{2c} ≤ 5 since c = (9/64)e^{−4κ} ≤ 1/100) and absorbed into the flat factors: |e^{−Ψ°(M)}| ≤ e^{c#(M)}, so e^{6c#(M)} per M (e^{−δΨ(M)} enters only expanded), and each 𝒞 keeps the weight 2|φ^T(𝒞)|_sup with the choice of factors counted by 2^s ≤ e^{d(𝒞)} (no bound |x| ≤ 1 is needed).
{#MD2.4.12.18-2} A vacuum occurrence, with factor e^{(s_𝔐(𝒞)−1)φ^T(𝒞)} − 1 (D2.3(3)), has |factor| ≤ 2·2^s|φ^T(𝒞)|_sup ≤ 2e^{d(𝒞)}|φ^T(𝒞)|_sup, sup over the domain.
{#MD2.4.12.18-3} No deviation factor is needed in S_𝒢, since (4)'s Cauchy step supplies it for Y^d_𝒢 as a whole.
{#MD2.4.12.19} *Sizes.* #(v) is the sum of the cube counts #_{k+1} of the vertex's pieces (M, the X_W of the touched W and of the members, the supp 𝒞 of the vacuum links; an old group W contributes #_{k+1}(X_W), the union as a set); ext_v (π_{k+1}-sides, from the vertex's interval) is that of its support; and diam_v, in step-(k+1) bonds, is the largest ℓ∞-distance from a point of the support to int(v) (for a Γ-vertex, member by member).
{#MD2.4.12.19-1} The *window* win(v) is int(v) extended along C by 20(diam_v + 1) bonds at each end, |win(v)| = |int(v)| + 40(diam_v + 1) (the interval need not lie in the support: an arc around a corner, or D2.2(4)(e)'s arcs, which reach touched intervals).
{#MD2.4.12.19-2} With the arc covered by the windows (covering lemma below): σ_{k+1}(𝒢) ≤ Σ_v(#(v) + |win(v)|/M), ext_{k+1}(𝒢) ≤ Σ_v(ext_v + |win(v)|/M + 2), and #(X(𝒢)) ≤ Σ_v#(X_v) + 8n_{k+1}(𝒢)/M + 80 ≤ Σ_v(#(X_v) + 8|win(v)|/M + 80) (the gap cubes of I(𝒢) included; X_v the cubes meeting v's support, interval and box): from any n′ ∈ I(𝒢) every cube of X(𝒢) is reached along the arc and then within some vertex's extent.
{#MD2.4.12.19-3} *Arc cubes (sharpens (4)'s 16n_{k+1}).* An arc of n step-(k+1) bonds of a square C has at most 5 straight pieces, and a straight piece of n_i bonds meets at most 8(n_i/M + 2) cubes of π_{k+1} (≤ n_i/M + 2 partition intervals along it, ≤ 2 in each transverse coordinate), so the cubes meeting an arc number at most 8n/M + 80.

{#MD2.4.12.20} *Links: pair relations, and the covering lemma.* v ~ v′ when (ii) their supports are incompatible (D2.3(3)'s hard core); (iii) one is a Γ-vertex hitting a W of the other; (iv′) an interval of v′ meets win(v), or an interval of v meets win(v′).
{#MD2.4.12.20-1} The relation is defined on the vertices alone, as the tree bound needs.
{#MD2.4.12.20-2} *Lemma.* (1) On a square C the shorter arc between two points is at most twice their ℓ∞-distance (D2.2(6)(d) *Arcs*: on opposite sides the arc is ≤ 2·side ≤ 2·distance; on adjacent sides a + b ≤ 2max(a, b)).
{#MD2.4.12.20-3} (2) If the supports of v, v′ meet or touch (as for (ii), and for (iii) when the member hits by contact; a hit by arc overlap gives overlapping intervals and (iv′) directly, and a hit through the member's own occurrences reduces to contact or overlap of constituents contained in X_{W′} and J_{W′}), a traversal of int(v) and one of int(v′) are within ℓ∞-distance diam_v + diam_{v′} + 1 (each support point is within diam of its vertex's interval), so by (1) the shorter of the two arcs of C between the intervals has length ≤ 2(diam_v + diam_{v′} + 1) ≤ 20(max(diam_v,
{#MD2.4.12.20-4} diam_{v′}) + 1): it lies in the window of the one with the larger diam, whose window the other's interval meets, i.e. (ii), (iii) ⇒ (iv′).
{#MD2.4.12.20-5} (3) Let 𝒢₁, …, 𝒢_m be the classes of 𝒢 under D2.2(6)(d)'s joined pairs (these are (ii)–(iii) pairs here; the M–𝒞 rule and the touching of a touched W are internal to the M-vertex, whose constituents all have the piece I(M); the second-rule pair of a touched W₀ ∈ 𝔅(M) and a vacuum-link pair are (ii) pairs, X_{W₀} and supp 𝒞 lying in supp v_M; two incompatible members of one occurrence are internal to the Γ-vertex and covered by (2) member by member), with linked hulls H_j, so that I(𝒢) is the union of the H_j, connected by overlaps, the hull rule adding the classes with an interval inside it.
{#MD2.4.12.20-6} By (2) the shorter arc of each joined pair lies in a window of the pair; an enlargement at an end of H_j lies in the interval of the insertion that it reaches, which contains that end, a point of a window of 𝒢_j, so that insertion is (iv′)-linked to 𝒢_j; with these insertions added to 𝒢_j, H_j ⊂ ∪_{v∈𝒢_j}win(v).
{#MD2.4.12.20-7} At an overlap point x ∈ H_i ∩ H_j: if x lies in an interval of 𝒢_j, that interval meets the window of 𝒢_i covering x, (iv′); likewise if x lies in an interval of 𝒢_i; otherwise x lies in a gap g_i of H_i and a gap g_j of H_j (maximal subarcs without intervals of the class, bounded by intervals at both ends), two overlapping arcs, so one contains an end of the other or they share an end — the interval of 𝒢_j (say) adjacent to that end meets H_i ⊂ ∪_{𝒢_i}win, again (iv′).
{#MD2.4.12.20-8} So every group is (ii)–(iv′)-connected, I(𝒢) ⊂ ∪_v win(v), and length(I(𝒢)) ≤ Σ_v|win(v)|.
{#MD2.4.12.20-9} Distinct groups may be linked: the tree bound needs only that each group is a linked-connected family; the hard core across groups is the reference gas's (D2.3(3)).

{#MD2.4.12.21} *(d) Shares, charges and the budgets.* Put ν_f := ν/16 + ν_r = 17ν/16, and ν_e = ν/(2C_box) ≤ ν/8 (C_box ≥ 4A_E ≥ 4, (12)(b)).
{#MD2.4.12.21-1} Per vertex, the *share* sh(v) := ν_f(#(v) + |win(v)|/M) + ν_e(ext_v + |win(v)|/M + 2) + c_π′α_{1,k+1}|win(v)| + ℓ(v) (ℓ(v) the ℓ_X part below), so that (ν/16 + ν_r)σ_{k+1}(𝒢) + ν_e·ext_{k+1}(𝒢) ≤ Σ_v sh(v) by (c), and the transports ‖T_𝐔(I(𝒢))‖ ≤ e^{c_π′α_{1,k+1}n_{k+1}(𝒢)} ≤ ∏_ve^{c_π′α_{1,k+1}|win(v)|} ((8), (c)) are inside the shares.
{#MD2.4.12.21-2} The unit of #_k is the π_k-cube, nested in its π_{k+1}-cube (CRE p.265, "compatible with all the other partitions"), and M/L is the π_k-side in step-(k+1) units.
{#MD2.4.12.21-3} For an M-vertex, #(v) is the sum over its pieces, a point of M is within M#(M) + max_{W∈𝔅(M)}diam_W of I(M) (M is connected, (10); I(M) contains a fine bond of C in a component of M, or a touched interval whose X_W meets one), a point of a touched X_W within diam_W (its interval lies in I(M)), and a point of a 𝒞, which touches M, within M#(𝒞) + 1 more; so diam_v ≤ M#(M) + Σ_{W∈𝔅(M)}(diam_W + 1) + Σ_{𝒱(M)}(M#(𝒞) + 1), |win(v)| ≤ |win_M| + Σ_{W∈𝔅(M)}40(diam_W + 1) + Σ_{𝒱(M)}40(M#(𝒞) + 1) with |win_M| := n_{k+1}(M) + 40(M#(M) + 1), and sh(v) ≤ sh(M) + Σ_{W∈𝔅(M)}sh(W) + Σ_{𝒱(M)}sh(𝒞), with:
  - {#MD2.4.12.22} *M:* #(M) cubes (M ⊇ D′ ⊇ D ⊇ slots, (10)(a)); ext_M ≤ #(M) + 8n_{k+1}(M)/M + 81 + max_{W∈𝔅(M)}(ext_k(W)/L + 1) (M's cubes, the arc cubes, the boxes of its touched insertions, whose intervals lie in I(M)).
    {#MD2.4.12.22-1} *The arc of M.* I(M) is the smallest arc containing the I(G_i) = ∪_{Y∈G_i}I(Y), I(Y) the smallest arc containing S′(Y) (Y's fine bonds of C and the intervals of the touched W with X_W meeting Y), enlarged at each end by at most one old interval (D2.2(4)(e)).
    {#MD2.4.12.22-2} A smallest arc H of a set S has length ≤ 4·diam_ℓ∞(S) (D2.2(6)(d) *Arcs*), and each point of H is within ℓ∞-distance 2diam_ℓ∞(S) of S (half of a gap of H).
    {#MD2.4.12.22-3} With S_M := ∪_YS′(Y), diam_ℓ∞(S_M) ≤ M#(M) + 2max_{W∈𝔅(M)}(diam_W + |int(W)|) (a touched W's support reaches S_M through its interval), and diam_W + |int(W)| ≤ (M/L)σ_k(W) (below): every point of ∪_iI(G_i) is within 2diam(S_M) + max_W|int(W)| of S_M, so n_{k+1}(M) ≤ 4(5diam(S_M) + 2max_W|int(W)|) ≤ 20M#(M) + 48(M/L)Σ_{W∈𝔅(M)}σ_k(W).
    {#MD2.4.12.22-4} With ℓ(M) (below), for M ≥ 100, sh(M) ≤ ν_f(142#(M) + 11) + ν_e(221#(M) + 84) + (3ν_f + 9ν_e)(48/L)Σ_{W∈𝔅(M)}σ_k(W) + ν_eΣ_{W∈𝔅(M)}(ext_k(W)/L + 1) + c_π′α_{1,k+1}|win_M|.
  - {#MD2.4.12.23} *W* (old; and each member W′ of an old occurrence, in its Γ-vertex's share): its domain X_W is contained in the closed-connected set X_W ∪ (cubes meeting I(W)) of at most #_k(X_W) + 8n_k(W)/M + 80 ≤ 8σ_k(W) + 80 π_k-cubes (*Arc cubes* of (c) at step k), and a closed-connected union of N π_k-cubes meets at most 16 + 128N/L cubes of π_{k+1} (L ≥ 6): cut a closed spanning walk of 2(N−1) steps between vertex-adjacent cubes into ≤ 8N/L + 1 pieces of ≤ ⌊L/2⌋ − 1 steps; the cubes of one piece lie in an ℓ∞-ball of radius < ½ π_{k+1}-side, which meets at most 2⁴ cubes.
    {#MD2.4.12.23-1} So #_{k+1}(X_W) ≤ 16 + 10240/L + 1024σ_k(W)/L; |int(W)| = n_k(W)/L and diam_W ≤ (M/L)#_k(W) (the support, connected and of #_k(W) π_k-cubes of side M/L step-(k+1) bonds, meets W's interval), so diam_W + |int(W)| ≤ (M/L)σ_k(W) (at k ≥ 2 by (4): each constituent meets I(𝒢) and is counted in σ_k; at k = 1 V4's domains lie within 2L fine units of ℋ, a factor 1 + O(1/M) absorbed below), so |win(W)| ≤ 41(M/L)σ_k(W) + 40; and ext_W = ext_k(W)/L.
    {#MD2.4.12.23-2} With ℓ(W) (below), sh(W) ≤ ν_f(16 + 10240/L + 80/M) + (1106ν_f + 41ν_e)σ_k(W)/L + ν_e(1/8 + 1/L)ext_k(W) + ν_e(2 + 40/M) + c_π′α_{1,k+1}|win(W)|, hence sh(W) ≤ (ν_r/4)σ_k(W) + (ν_e/8 + ν_e/L)ext_k(W) + c_sh + c_π′α_{1,k+1}|win(W)|, c_sh := 2ν_f(16 + 10240/L + 41/M) + 2ν_e(2 + 41/M), for L ≥ L₀ := 5000 ((1106·17/16 + 41/8)/L₀ ≤ 1/4 with ν_e ≤ ν/8).
    {#MD2.4.12.23-3} A lower bound on L only; it is compatible with (6)'s (1+β₀)⁸ < L, (f)'s 8(1+β₀)^{15} ≤ L (8·1.5^{15} < 3504 for β₀ ≤ 1/2) and V4's L ≥ 3(d+3), and the rate of (10) is r_κ = (1 − 5δ)λ_Lκ = (L+2)κ/4 for L ≥ 486 ((10)(b): λ_L = L/2 there and δ = (1−2/L)/10).
    {#MD2.4.12.23-4} (c_sh, the share constant, is not the reference activity c_𝒢 of a group; that is written c_𝒢 below, also for the trivial group {W} and for the step-k groups W′.)
  - {#MD2.4.12.24} *Γ-vertex:* sh ≤ Σ_{W′∈Γ}((ν_r/4)σ_k(W′) + (ν_e/8 + ν_e/L)ext_k(W′) + c_sh + c_π′α_{1,k+1}|win(W′)|) (the members' domains, arcs and windows are the vertex's).
  - {#MD2.4.12.25} *𝒞:* #(𝒞) cubes, a point within M#(𝒞) + 1 of M, ext ≤ #(𝒞) + 1 beyond M's: with ℓ(𝒞), sh(𝒞) ≤ 2(83ν_f + 86ν_e)#(𝒞) ≤ #(𝒞)/4 for ν ≤ 1/1000.
  - {#MD2.4.12.26} *The polynomial ℓ_{X(𝒢)}.* ℓ_X ≤ 2#(X(𝒢)) ((4)) ≤ 1 + Σ_v(2#(X_v) + 16|win(v)|/M + 160) by (c) ≤ ∏_{pieces}(1 + 2#(X_piece) + 16|win_piece|/M + 160) (1 + Σa_i ≤ ∏(1 + a_i); the pieces of an M-vertex are M, its touched W and its 𝒞, with |win_W| := |win(W)| and |win_𝒞| := 40(M#(𝒞) + 1)), with #(X_M) ≤ #(M) + 8n_{k+1}(M)/M + 81, #(X_W) ≤ (2ext_k(W)/L + 3)⁴ (the box, which contains W's support and interval cubes; 4-dimensional, (5) *At step 1*), #(X_𝒞) ≤ #(𝒞).
    {#MD2.4.12.26-1} Then (2x/L + 3)⁴ ≤ C_ℓe^{(ν_e/8)x} for the boxes and 1 + y ≤ C_τe^{τy}, τ := ν_f/16, for the rest: ℓ_X ≤ ∏_{pieces}C_pce^{ℓ(piece)}, C_pc := 483C_τmax(C_τ, C_ℓ) (an M or 𝒞 piece takes C_τ² for its two terms, a W piece C_τ for its window and 1 + 2(2x/L + 3)⁴ ≤ 3C_ℓe^{(ν_e/8)x} for its box), ℓ(M) := (ν_f/8)(#(M) + 8n_{k+1}(M)/M + 81) + ν_f|win_M|/M, ℓ(W) := ν_f|win(W)|/M + (ν_e/8)ext_k(W), ℓ(𝒞) := (ν_f/8)#(𝒞) + ν_f|win_𝒞|/M, which the bounds above include.
    {#MD2.4.12.26-2} The constant C_pc per piece multiplies the activities in w̃ ((e)): for old pieces it is absorbed by the smallness of the old rooted sums (g_K small), for M in C_M ((f)).
  {#MD2.4.12.27} *Transports.* The transport part of the shares: c_π′α_{1,k+1}|win(W)| ≤ (ν_r/16)σ_k(W) + 40c_π′α_{1,k+1} once c_π′α_{1,k+1}·41M/L ≤ ν_r/16; c_π′α_{1,k+1}|win_M| ≤ ν_f#(M) + (ν_r/64)Σ_{W∈𝔅(M)}σ_k(W) + 40c_π′α_{1,k+1} once c_π′α_{1,k+1}·60M ≤ ν_f and c_π′α_{1,k+1}·48M/L ≤ ν_r/64; c_π′α_{1,k+1}|win_𝒞| ≤ ν_f#(𝒞) once c_π′α_{1,k+1}·80M ≤ ν_f.
  {#MD2.4.12.27-1} All hold under c_π′α_{1,k+1}·4096M ≤ ν (α_{1,k} = g_kC₁(log g_k^{−2})^{q₁} → 0, CRE p.277's margin, with L, M, ν fixed before g), and the per-piece constant e^{40c_π′α_{1,k+1}} ≤ e is absorbed in the activities.
  {#MD2.4.12.27-2} (11)(c)(β)'s a′-transports along the slot arcs are a separate factor ∏_{W∈𝔅(M)}e^{(ν_r/16)(σ_k(W)+1)} inside |H̃(M)| (under its c_π′α_{1,k+1}·20M/L ≤ ν_r/16 and 20c_π′M‖a′‖_∞ ≤ ν_r/16), the σ-part paid from the touched W's reserve below and the e^{ν_r/16} as in #MD2.4.12.27-6.
  {#MD2.4.12.27-3} *Charges.* b(W) := (ν_r/4)σ_k(W) + (ν_e/4)ext_k(W) + c_sh; b(Γ) := Σ_{W′∈Γ}b(W′); b(𝒞) := #(𝒞)/2; b(M-vertex) := (κ_s/4)#(G_M) + (r_κ/648)#(M∖D′) + 1 + Σ_{W∈𝔅(M)}b(W) + Σ_{𝒱(M)}b(𝒞) (with (10)'s counting constant 324: e^{−r_κd_{k+1}(M;D′)} ≤ e^{−(r_κ/324)#(M∖D′)}e^{20c_Dr_κ#(G_M)}, since #(M∖D′) ≤ 80#(D′) + 324d and #(D′) ≤ 81c_D#(G_M)).
  {#MD2.4.12.27-4} *The reserve budget of an old W:* of the weight ν_rσ_k(W) in (ii-w), sh(W) takes ν_r/4, its transports ν_r/16, b(W) ν_r/4, the window counts of (e) ν_r/8, the interaction weight of (e) (carried by every member of an occurrence) ν_r/16, (11)(c)(β)'s a′-transports of a touched W ν_r/16, and the share parts an M-vertex passes to its touched W ν_r/16: (3ν_f + 9ν_e)(48/L)σ_k(W) + (ν_r/64)σ_k(W) ≤ (ν_r/16)σ_k(W) for L ≥ L₀; in all 7/8, with ν_r/8 to spare.
  {#MD2.4.12.27-5} *The extent budget of an old W:* sh(W)'s ν_e/8 + ν_e/L, b(W)'s ν_e/4, the box reduction's ν_e/4 ((e)) and the M-vertex's ν_e/L (ext_M's touched boxes): ≤ (5/8 + 2/L)ν_e ≤ ν_e.
  {#MD2.4.12.27-6} The M-vertex's constant ν_e per touched W in the exponent, and (11)(c)(β)'s e^{ν_r/16} per touched W, give the factor e^{ν_e + ν_r/16} ≤ e per touched W, a piece of the M-vertex (#MD2.4.12.26); it is inside that piece's factor C_pc′ (#MD2.4.12.28-0).

{#MD2.4.12.28} *(e) The rooted sums and the Kotecký–Preiss condition.* Positions: a step-k traversal n or a π_k-cube (W- and Γ-vertices), a step-(k+1) traversal n′ or a π_{k+1}-cube (M-vertices, and every vertex at the step-(k+1) positions of (f)); "v at p" means p in an interval of v for a traversal, p ∈ X_v for a cube. w̃(v) := C_v·|activity|_sup·e^{sh(v)}, C_v the product over the pieces of one factor C_pc′ := e²C_pc (#MD2.4.12.28-0); the rooted sums ε_p := Σ_{v at p}w̃(v)e^{b(v)} include the window and box spares named below.
{#MD2.4.12.28-0} C_pc′ is a constant of ν_f and L, and at every k it bounds a piece's ℓ_X constant C_pc times its transports' e^{40c_π′α_{1,k+1}} ((d)) and, for a touched W, times the e^{ν_e + ν_r/16} of #MD2.4.12.27-6: 40c_π′α_{1,k+1} ≤ 40ν/(4096M) ≤ 1 by #MD2.4.12.27-1, and ν_e + ν_r/16 ≤ ν ≤ 1/1000 since ν_r = ν and ν_e = ν/(2C_box).
{#MD2.4.12.28-1} A step-(k+1) traversal contains L step-k traversals and a π_{k+1}-cube L⁴ π_k-cubes, so at step-(k+1) positions the old sums are ε̄^{old} := max(Lε^{old}_t, L⁴ε^{old}_c), and likewise ε̄^{ref,k}:
- {#MD2.4.12.29} *ε^{old}_t, ε^{ref,k}_t per step-k traversal*: from (ii-w) at step k and its c-version, since sh(W) + b(W) + (the transports, the interaction weight, the a′-transports and the M-vertex's share parts of (d), ν_r/16 each)σ_k(W) ≤ (3/4)ν_rσ_k(W) + (3/8 + 1/L)ν_e·ext_k(W) + 2c_sh: the activity's decay beyond this is e^{−(1/4)ν_rσ_k(W)}e^{−(5/8 − 1/L)ν_e·ext_k(W)}, of which ν_r/8 pays the window positions below and ν_e/4 the box reduction.
  {#MD2.4.12.29-1} At complex data the size is (5)'s, O(ρ_k·pl) away from older layers; at k = 1 the base is (c4-6-5), (12)(b), whose majorant M(W) bounds the reference activities a_W as well (V4 sec:c4-6-2: "the physical and reference data having the same numerical majorant"), so that (c4-6-5) is also the c-version at k = 1.
- {#MD2.4.12.30} *Cube positions follow from traversal positions.* A cube Δ ∈ X(W) ∪ Q^#_W lies within ext_k(W) of every traversal of W ((12)(b)'s definition of ext_k), so Σ_{W: Δ∈X(W)∪Q^#_W}w̃(W)e^{b(W)} ≤ Σ_{R≥0}#{n : dist(n, Δ) ≤ R+1}·sup_nΣ_{W∋n, ext_k(W)≥R}w̃(W)e^{b(W)} ≤ Σ_R8M(2R+3)e^{−(ν_e/4)R}ε^{old}_t ≤ C(M/ν_e²)ε^{old}_t =: ε^{old}_c (ε^{old}_t with the box spare e^{(ν_e/4)ext_k} inside), the *box reduction*, spending a quarter of the extent weight; the same for Γ-vertices (ε^{ref,k}_c);
  {#MD2.4.12.30-1} for M-vertices ε^{new}_c is counted directly in (f), the root in a cube.
  {#MD2.4.12.30-2} At k = 1 (c4-6-5)'s per-cube pin covers F(W) directly.
- {#MD2.4.12.31} *Window positions.* For a vertex kind with rooted sum ε per traversal and spare decay e^{−c_wdiam_v} beyond w̃e^{b}: Σ_{v: n∈win(v)}w̃(v)e^{b(v)} ≤ Σ_{d≥0}2·sup_{n_d}Σ_{v∋n_d, 20(diam_v+1)≥d}w̃(v)e^{b(v)} ≤ C_win·ε, C_win := 2Σ_{d≥0}e^{−c_w(d/20−1)₊} ≤ 82/c_w (c_w ≤ 1), d in the vertex's own traversals (at a step-(k+1) traversal the L step-k traversals give ε̄'s factor L).
  {#MD2.4.12.31-1} For old W the spare is (ν_r/8)σ_k(W) ≥ (ν_rL/(8M))diam_W (diam_W ≤ (M/L)σ_k(W), (d)); for Γ-vertices each member's own spare and window ((c)); for M-vertices, with diam_v ≤ M#(M) + Σ_{W∈𝔅(M)}(diam_W + 1) + Σ_{𝒱(M)}(M#(𝒞) + 1) ((d)), the spare is one unit of exponent per cube of M, reserved in (f)'s count, the touched W's window spare (ν_r/8)σ_k(W) (a touched W has no window of its own), and e^{#(𝒞)/4} of a vacuum link's weight (the vacuum sum below).
  {#MD2.4.12.31-2} So c_w := min(1, ν_rL)/(8M) serves every kind, and C_win ≤ 656M/min(1, ν_rL) depends on L, M, ν only.
- {#MD2.4.12.32} *ε^{new}_t per step-(k+1) traversal* (M-vertices): bounded in (f).
- {#MD2.4.12.33} *The vacuum sum.* For a union of cubes Y, Σ_{𝒞≁Y}w̃(𝒞)e^{b(𝒞)} ≤ 2C_pc′Σ_{𝒞≁Y}e^{d(𝒞) + (3/4)#(𝒞)}|φ^T(𝒞)| ≤ 2C_pc′c#(Y) by (2)(e)–(g) with b := 9log2 + 1 in (2)(e), i.e. under κ ≥ κ_vac′ := 162(1 + 17log2), which replaces κ_vac in κ_D (a larger lower bound on κ of the same kind); w̃(𝒞) carries the per-piece constant C_v = C_pc′ of ℓ_X, and in every later use of this sum (the e^{18c#(M)} of (f), the 24c of (f)'s per-cube cost, the smallness of c in the KP conditions, (13)(c)'s vacuum tail) c stands for C_pc′c.
  {#MD2.4.12.33-1} With c = (9/64)e^{−4κ} (D2.3(1)), C_pc′c ≤ min(1/100, 1/(2C_v′)) (C_v′ the absolute constant of (13)(c)'s vacuum Lipschitz bound) holds under κ ≥ κ_pc := ¼log((9/64)max(100, 2C_v′)C_pc′), a lower bound on κ after ν and L (C_pc′ depends on ν_f and L through C_τ, C_ℓ), included in κ_D′.
{#MD2.4.12.34} *The Kotecký–Preiss condition for the linking relation,* Σ_{v′~v}w̃(v′)e^{b(v′)} ≤ b(v)/2 for every vertex v (the factor ½ leaves room for the marked sums of (f) and (13)(c)), by counting the positions of a linked v′:
- {#MD2.4.12.35} for an M-vertex v: (ii) old W′ and Γ with support incompatible with v's: at the ≤ 81L⁴#(v) π_k-cubes of the support's 3⁴-neighbourhood, ≤ 81L⁴#(v)(ε^{old}_c + ε^{ref,k}_c); M′-vertices incompatible: ≤ 81#(v)ε^{new}_c; (iii) Γ hitting a touched W ∈ 𝔅(M): ≤ Σ_{W∈𝔅(M)}a(W) by the interaction clause below; (iv′) old v′ with an interval meeting win(v): ≤ L|win(v)|(ε^{old}_t + ε^{ref,k}_t) with |win(v)| ≤ n_{k+1}(M) + 40(diam_v + 1); old v′ whose window reaches int(v): ≤ L·n_{k+1}(M)·C_win(ε^{old}_t + ε^{ref,k}_t);
  {#MD2.4.12.35-1} M′-vertices with int(M′) meeting win(v) or whose window reaches int(v): ≤ (|win(v)| + n_{k+1}(M)C_win)ε^{new}_t (the M–M′ arc links).
  {#MD2.4.12.35-2} With n_{k+1}(M) ≤ 20M#(M) + 48(M/L)Σ_{W∈𝔅(M)}σ_k(W) ((d)) and diam_v ≤ M(#(M) + Σ_{W∈𝔅(M)}(σ_k(W)/L + 1) + 2Σ_{𝒱(M)}#(𝒞)), every term is ≤ (small)·(#(M∖D′) + #(G_M) + Σ_Wσ_k(W) + Σ_𝒞#(𝒞) + |𝔅(M)| + 1), small := O(L⁴(ε^{old}_c + ε^{ref,k}_c) + LMC_win(ε^{old}_t + ε^{ref,k}_t) + ε^{new}_c + MC_winε^{new}_t + c) (c = (9/64)e^{−4κ} from the vacuum links' positions, (2)(g)), which is ≤ b(v)/2 for g_K small and κ ≥ κ_D: the Σ_Wσ_k(W) and |𝔅(M)| parts are charged to the touched W's b(W)/2 ≥ (ν_r/8)σ_k(W) + c_sh/2, the Σ_𝒞#(𝒞) part to b(𝒞)/2 = #(𝒞)/4, the rest to (κ_s/8)#(G_M) + (r_κ/1296)#(M∖D′) + ½;
- {#MD2.4.12.36} for a W-vertex: (ii) ≤ 81#_k(X_W)(ε^{old}_c + ε^{ref,k}_c + ε^{new}_c); (iii) Γ hitting W: ≤ a(W) ≤ (ν_r/32)σ_k(W) (below); (iv′) ≤ (n_k(W) + 40L((M/L)σ_k(W) + 1) + L)(ε^{old}_t + ε^{ref,k}_t) + (n_k(W) + 2L)C_win(ε^{old}_t + ε^{ref,k}_t) + (the same with ε^{new}_t) (|win(W)| in step-k traversals, partial step-(k+1) bonds included): (ii) and (iv′) are ≤ (small)·(σ_k(W) + 1), and with (iii) the sum is ≤ (ν_r/32)σ_k(W) + (small)·(σ_k(W) + 1) ≤ b(W)/2 = (ν_r/8)σ_k(W) + (ν_e/8)ext_k(W) + c_sh/2 for g_K small;
- {#MD2.4.12.37} for a Γ-vertex: the sums over its members, as for W, each ≤ b(W′)/2.
{#MD2.4.12.38} *The weighted interaction clause (FV Thm 5.4 applied as it stands).* Apply (5.10)–(5.11) to the step-k reference gas with the activities |w(W′)| := |c_{W′}|e^{s(W′)}, s(W′) := sh(W′) + b(W′) + (ν_r/8 + ν_r/16)σ_k(W′) + log C_pc′ (the window spare and the transports, which every member of an occurrence carries, and the per-member factor of a Γ-vertex's C_v, as in (13)(c)'s d;
{#MD2.4.12.38-1} ε̂ small absorbs it), and the weight a(W′) := (positions of W′)·ε̂, positions of W′ := the ≤ 81#_k(X_{W′}) cubes incompatible with X_{W′} and the n_k(W′) traversals of its arc, ≤ 81Mσ_k(W′), and ε̂ := sup_pΣ_{W′ at p}|c_{W′}|e^{s(W′)+(ν_r/16)σ_k(W′)} (within (ii-w)'s c-version by (d)'s budget; c_{W′} the reference activity of the step-k group W′).
{#MD2.4.12.38-2} (5.10): Σ_{W″≁W′}|w(W″)|e^{a(W″)} ≤ (positions of W′)·sup_pΣ_{W″ at p}|c_{W″}|e^{s(W″)+a(W″)} ≤ (positions of W′)·ε̂ = a(W′), because a(W″) ≤ 81Mσ_k(W″)ε̂ ≤ (ν_r/16)σ_k(W″) once ε̂ ≤ ν_r/(1296M).
{#MD2.4.12.38-3} (5.11): Σ_{Γ hits W}|φ_k(Γ)|e^{Σ_{W′∈Γ}s(W′)} ≤ Σ_{W″≁W}|w(W″)|e^{a(W″)} ≤ a(W) ≤ 81Mσ_k(W)ε̂ ≤ (ν_r/32)σ_k(W) once ε̂ ≤ ν_r/(2592M) (g_K small).
{#MD2.4.12.38-4} (5.11) puts e^{a} on the first member only, and every member carries its s(W′), so the Γ-vertices' windows and transports are inside; the W budget closes at (ν_r/32)σ_k(W) ≤ b(W)/4, and ε^{ref,k}_t ≤ sup_pΣ_{W′ at p}|w(W′)|e^{a(W′)}.
{#MD2.4.12.38-5} At k = 1 the c-version is (c4-6-5) with V4 sec:c4-6-2 (first bullet).

{#MD2.4.12.39} *(f) The tree bound with the root at the position, ε^{new}, and the recursion in k.* T(v) := Σ over finite rooted trees at v in the linking graph of (c) of ∏_{v′≠v}w̃(v′); by the depth induction (FV Thm 5.4's mechanism, in the rooted-tree form; T_0 = 1, the depth-d sums increase to T), T(v) ≤ exp(Σ_{v′~v}w̃(v′)T(v′)) ≤ e^{b(v)/2} under (e).
{#MD2.4.12.39-1} Every linked family has a spanning tree rooted at any of its vertices, and the hard core only removes terms.
{#MD2.4.12.39-2} *Marked sums.* Let m be a weight on a class of vertices with sup_pΣ_{v′ at p}m(v′)e^{b(v′)} ≤ ε_m, and F(v) := the tree sum at v with exactly one marked non-root vertex, whose w̃ is replaced by m.
{#MD2.4.12.39-3} The mark is in exactly one child subtree, so F(v) ≤ T(v)·Σ_{v′~v}[m(v′)T(v′) + w̃(v′)F(v′)], and by induction on the depth F(v) ≤ λb(v)e^{b(v)/2}, λ := 2ε_m/ε_*, where ε_* is (e)'s threshold, (positions of v)·ε_* ≤ b(v)/2 for every v: Σ_{v′~v}m(v′)e^{b(v′)} ≤ (ε_m/ε_*)b(v)/2 and Σ_{v′~v}w̃(v′)b(v′)e^{b(v′)/2} ≤ Σ_{v′~v}w̃(v′)e^{b(v′)} ≤ b(v)/2 (xe^{x/2} ≤ e^x), so F(v) ≤ e^{b(v)/2}b(v)(ε_m/(2ε_*) + λ/2) ≤ λb(v)e^{b(v)/2}.
{#MD2.4.12.39-4} *The root.* Fix a position p at step k+1: a traversal n′ ∈ I(𝒢), which lies in win(v₀) for some vertex v₀ of 𝒢 by the covering lemma of (c), or a cube of X(𝒢), which lies in X_{v₀} for some v₀ or is a gap cube of I(𝒢), met by ≤ 4M + 4 traversals n′.
{#MD2.4.12.39-5} Root 𝒢 at v₀.
{#MD2.4.12.39-6} The root's position is paid by the window or cube sums of (e) with the root's own spare (only e^{b(v₀)/2} of e^{b(v₀)} is used by T), not by the shares, which already dominate e^{ν_fσ + ν_e·ext}.
{#MD2.4.12.39-7} *The amendments (T2) and (T0) of the D2.6 closure §5.2.* (T2) the slots' factor e^{−(κ_s−3)#(G_M)} of (11)(d) is split as e^{−ν_e#(G_M)}e^{−(κ_s−ν_e−3)#(G_M)} before (11)(d), which then runs with κ_s − ν_e in place of κ_s, under κ_s − ν_e ≥ κ_s^{(12)}, so that e^{−ν_e} per π_k-cube of the components is reserved, unspent by (c)–(e), for the carry lemma's bridges, which lie in the components (closure §5.2 (T1));
{#MD2.4.12.39-8} (T0) the rooted sums at an old vertex are run in the lineage form: the old att members of a term are its fixed data, and F(v₀) ≤ λb(v₀)e^{b(v₀)/2} bounds the sum over the new constituents rooted at v₀; (e)–(f) are re-run over the vertex set of the new constituents and the dev old members; a (β)-vertex touching only fixed att members adds at most K′b_n/ᾱ_n per position (n the step of the re-run, b_n/ᾱ_n as in (11)(c)(β), K′ closure §5.2's constant), so ε^{new}_{re-run} ≤ C_Mb_n·pl + K′b_n/ᾱ_n, which is first order in g and serves (e)'s smallness only, not an amplitude ρ_{n+1};
{#MD2.4.12.39-9} (e)'s condition needs K′b_n/ᾱ_n below its threshold, a smallness of g under (q₀ = q₁ > p₀); the merged untouched W of closure 5.5 are rooted here with b(W) = (ν_r/4)σ(W), the charge of a fixed member (no extent part, no constant; its positions are ≤ 81Mσ(W), so the KP condition at W needs no constant). Three classes:
- {#MD2.4.12.40} *groups with an M-vertex, rooted at an M-vertex:* Σ ≤ Σ_{v₀ M-vertex: p∈win(v₀) or p∈X_{v₀}}w̃(v₀)T(v₀) ≤ C_winε^{new}_t (or ε^{new}_c);
- {#MD2.4.12.41} *groups with an M-vertex, rooted at an old vertex:* by the marked sum with m := w̃ on the M-vertices (ε_m = ε^{new}, a group with an M-vertex has a tree with a marked M-vertex), Σ ≤ Σ_{v₀ old at p}w̃(v₀)F(v₀) ≤ (2ε^{new}/ε_*)Σ_{v₀ old: p∈win(v₀) or X_{v₀}}w̃(v₀)b(v₀)e^{b(v₀)/2} ≤ (2ε^{new}/ε_*)·C_win(ε̄^{old} + ε̄^{ref,k}) ≤ C_winε^{new} once ε̄^{old} + ε̄^{ref,k} ≤ ε_*/2;
- {#MD2.4.12.42} *M-free groups* (W- and Γ-vertices only; vacuum links belong to M-vertices), other than the trivial group {W}, which is the carried insertion of (6): Σ ≤ Σ_{v₀ at p}w̃(v₀)(T(v₀) − 1) ≤ Σ_{v₀ at p}w̃(v₀)x_{v₀}e^{x_{v₀}} with x_{v₀} := Σ_{v′~v₀}w̃(v′)e^{b(v′)} ≤ ((ε^{old} + ε^{ref,k})/ε_*)b(v₀)/2, so ≤ C_win(ε̄^{old} + ε̄^{ref,k})²/ε_*: quadratic in the old sums.
{#MD2.4.12.43} So, for every position p at step k+1, with ε^{new} := max(ε^{new}_t, ε^{new}_c) and ε̄^{old}, ε̄^{ref,k} of (e),
  {#MD2.4.12.44} Σ_{𝒢 at p}e^{(ν/16 + ν_r)σ_{k+1}(𝒢) + ν_e·ext_{k+1}(𝒢)}S_𝒢ℓ_{X(𝒢)} ≤ Σ_{𝒢 at p}∏_{v∈𝒢}w̃(v) ≤ 2C_winε^{new} + C_win(ε̄^{old} + ε̄^{ref,k})²/ε_*,
{#MD2.4.12.45} and the same with |c_𝒢| ≤ S_𝒢 (the c-version); at a gap-cube position of I(𝒢), met by ≤ 4M + 4 traversals n′, the right side carries the extra factor 4M + 4 (harmless for the KP conditions; (13)(b)'s factor 16 at off-C bonds); the group's weight is ≤ ∏_vw̃(v) by (c), (d), D2.2(6)(d) *Cost* and the projective norm ((10)(a)) (S_𝒢 ≤ ∏ vertex sups × transports; the 1/m_𝒢! of D2.3(3) is ≤ 1).
{#MD2.4.12.46} *ε^{new}, the marked-polymer sum, with the (α)/(β) split.* Fix a position: a π_{k+1}-cube Δ (ε^{new}_c) or a step-(k+1) traversal n′ (ε^{new}_t).
{#MD2.4.12.46-1} An M-vertex at Δ has Δ ∈ M, or Δ meeting I(M), or Δ in the box of a touched W ∈ 𝔅(M) (which contains X_W), or Δ ∈ supp 𝒞 of a vacuum link.
{#MD2.4.12.46-2} Its data: the domain M ∈ 𝐃_{k+1} (wall-connected); D′ ⊂ M; the π_k-cubes of D′ that are the components Y, grouped into the G_i; the touched insertions 𝔅(M); the arc I(M) (determined by the slots' arcs and the touched intervals, D2.2(4)(e)); the vacuum links 𝒱(M).
{#MD2.4.12.46-3} The count, from the root: the animal, one of ≤ 64^{#(M)−1} wall-connected animals through Δ ((2)(c)); a root in an arc cube or at n′ (≤ 4M + 4 traversals through Δ;
{#MD2.4.12.46-4} the arc is fixed by one of them and its two end offsets, ≤ n_{k+1}(M)² choices, and contains a slot traversal, ≤ n_{k+1}(M), in a cube of M, ≤ 16, then the animal) or in a box (the box reduction of (e)), or in a vacuum link (the 𝒞 ∋ Δ summed with their spare e^{#(𝒞)/4}, ≤ 2c, and M through one of the ≤ 81#(𝒞) cubes of 𝒞's 3⁴-neighbourhood, paid by the same spare), all polynomial in n_{k+1}(M) or #(𝒞) and absorbed by a constant in the weights below; D′ ⊂ M (2^{#(M)}); the components inside D′ (≤ 2^{L⁴#_{k+1}(D′)} ≤ 2^{81c_DL⁴#(G_M)}, (11)(a));
{#MD2.4.12.46-5} the grouping and which groups' slots M carries, ≤ 2^{2n(M)} ≤ 4^{#(G_M)} (D2.2(4)(e)'s groups are the connected components of the overlap graph of the arcs I(Y), a function of the components and the touched insertions, not a free partition); the touched insertions in two stages, with weights w̃(W)e^{b(W)}: first those whose domain meets a component, over the subsets of the ≤ 81#(G_M) cube positions, ≤ e^{81#(G_M)ε̄^{old}}, which fixes the slot arcs up to their enlargements;
{#MD2.4.12.46-6} then the ≤ 2 end insertions of D2.2(4)(e)'s enlargements, whose domains need not meet a component, at traversal positions next to the arcs, each ≤ ε^{old}_t and charged to its own b(W), which fixes I(M); then those with intervals in I(M), over the subsets of the ≤ L·n_{k+1}(M) traversal positions, ≤ e^{Ln_{k+1}(M)ε^{old}_t}, whose Σ_Wσ_k(W) part (n_{k+1}(M) ≤ 20M#(M) + 48(M/L)Σσ_k(W), (d)) is charged to the first-stage W's b(W)/2; together ≤ e^{(#(G_M) + #(M))/8} for g_K small;
{#MD2.4.12.46-7} the vacuum links, summed over the subsets of the 𝒞 incompatible with M's domain with weights w̃(𝒞)e^{b(𝒞)}, ≤ exp(Σ_{𝒞≁M}w̃(𝒞)e^{b(𝒞)}) ≤ e^{18c#(M)} by the vacuum sum of (e) (Y = M⁺, 9#(M) cubes), absorbed with the flat factors |e^{−Ψ°(M)}| and the expansion factors of (c), ≤ e^{6c#(M)} ((c)); the weight of (11)(f) *Consequence*, |H̃(M)| ≤ c_M·(amplitude)·pl·e^{−(κ_s/2)#(G_M)}e^{−(r_κ/324)#(M∖D′)}e^{20c_Dr_κ#(G_M)} with the amplitude of (11)(e)–(f).
{#MD2.4.12.46-8} With #(M) ≤ #(M∖D′) + 81c_D#(G_M) ((11)(d)), n(M) ≤ #(G_M), the charge b(v) and the share sh(M) of (d), and two units of exponent per cube of M reserved, one for (e)'s window decay and one for (13)(c)'s vacuum tail, a cube of M∖D′ costs log 64 + log 2 + 2 + 1/8 + 24c + 143ν_f + 221ν_e (≤ 8 for ν ≤ 1/1000) against r_κ/324 − r_κ/648 = r_κ/648, and a π_k-cube of the components costs 20c_Dr_κ + 81c_D(L⁴log2 + log 128 + 2 + 1/8 + 24c + 143ν_f + 221ν_e) + log 4 + 1 + 1/8 against κ_s/2 − κ_s/4 = κ_s/4; the sums over #(G_M) ≥ 1 and #(M∖D′) ≥ 0 then converge to a constant, and
  {#MD2.4.12.47} ε^{new} ≤ ε^{new,α} + ε^{new,β}, ε^{new,α} ≤ C_Mρ_{k+1}·pl, ε^{new,β} ≤ K_β·(b_k/ᾱ_k)·ε^{old},
  {#MD2.4.12.48} under r_κ/648 ≥ 8 (true: r_κ = (L+2)κ/4 ≥ 1250κ for L ≥ L₀, (10)(b), so r_κ/648 > 1.9κ, and κ ≥ κ_D′) and κ_s ≥ κ_s^{(12)} := 80c_Dr_κ + 324c_D(L⁴log2 + 9) + 16 (a condition on RG2's κ₁, written κ_s here, after κ, L and before M, δ₁M ≥ κ_s, D2.1(4); it contains (11)(d)'s, and c_D is M-independent by (11)(a)), ε^{new}_t being the same count with the root at n′.
  {#MD2.4.12.48-1} Kind (α) has amplitude O(b_k²) or O(δ_k²) ≤ Cρ_{k+1} ((11)(e)–(f)), kind (β) has amplitude (C_Tb_k/ᾱ_k)^{n(G)}·∏_{W∈𝔅(G)}[e^{θ_k(W)}‖Y_W‖] with at least one touched W ((11)(c)(β)), whose position sum is ε^{old} and whose further positions the charges absorb, so its amplitude is the old insertions', not a new ρ_{k+1}.
  {#MD2.4.12.48-2} C_M, K_β depend on L, M, κ, κ_s, C_box, ν, c_D and (11)'s constants, uniformly in k ≤ K (K_β includes ε̄^{old}'s L⁴).
  {#MD2.4.12.48-3} *c_{{W}} = 0 for the carried dev insertions* (the reference activity of the trivial group {W}) because their dev parts vanish at the reference point (D2.3(3); f(0) = 0 in (4)) — not by (T-dev), which is stated in the step-(k+1) support.

{#MD2.4.12.49} *Uniformity in k and (S-w).* Let ε^{(k)} be the (ii-w) sum at step k over all insertions present (carried and new) and write ε^{(k)}, ε^{ref,k} ≤ C^{(k)}ρ_k·pl_k, pl_k := 1 + (log g_k^{−2})^{(q₁−q₀)₊}.
{#MD2.4.12.49-1} At step k+1 the carried insertions contribute ≤ L^{−1}(ρ̃_k/ρ̃_{k+1})·ε^{(k)} per traversal for the real-point dev part ((6); (12)(b) *It carries*, traversal positions) and the new groups contribute the bound above;
{#MD2.4.12.49-2} ε^{(k)} is a size sum at complex data ((e)), and for its complex-data part the carry factor is ρ̃_k/ρ̃_{k+1} (a*^{(k)}_n ≤ L^{−1}a*^{(k+1)}_{n′} at the same datum, summed over the L step-k traversals), so a carried insertion made at step j contributes ≈ ρ̃_jα_{1,k+1} per step-(k+1) traversal at every later step, and the recursion below closes uniformly in k only for the real-point part.
{#MD2.4.12.49-3} The complex-data part is bounded instead from the production constants (WILSON_IT1_COMPLEX_COVARIANCE_2026_10_29.md §4; #MOMGD.5): Σ_j ≤ Ĉ·max_jN^{(j)}ρ_{k+1}pl.
{#MD2.4.12.49-4} With it the recursion reads C^{(k+1)} ≤ (1+Ĉ)max_{j≤k+1}N^{(j)} + L^{−1}(1+β₀)^{15}C^{(k)}, where N^{(j)} is the new groups' constant (2C_winC_M plus the (β) and quadratic terms of θ below), and C_S′ := max(2(1+Ĉ)C^{(1)}, 8(1+Ĉ)C_winC_M) in place of the value below.
{#MOMGD.5} *The complex-data part* (WILSON_IT1_COMPLEX_COVARIANCE_2026_10_29.md: the carried insertions at complex data, uniformly in k, and the region of SW §6(6c)). Its inputs are (T-dev)'s (#MD2.4.5.13), SW §6(6d), the note's (K3), CRE (2.6)–(2.7), the slot independence of D2.6 closure 4.2(iii) class (3), D2.2(4)(f)'s chain condition with CRE p.277's margin, and, for the trivial branch m < m₀ only, #MD2.2.6.142's inputs (𝐁_p(X)'s definition, CRE p.256 l.57–63; q₀ = q₁ > p₀; CRE p.277's 𝐇-decay; CRE (2.6)–(2.7); RG2 p.5's all-norms bound) with RMJ (#MD2.2.6.142, #MOMGD.50).
  {#MOMGD.5-1} (K3)'s averaging constant is C_av := 2(B₃ + 2c_dB₅), from RG1 p.263 (1.17) (the averaged bounds (1.16) from the curvature bound at complex 𝐔, "From Proposition 9 [15]") with VAR Theorem 1's multi-domain spaces (one ε₁ for all layers), read in the top-layer uniform form on X ⊂ Ω_j that the note uses. J_{p,X}(M^·(𝐔)) depends on 𝐔 alone (RG1 (1.15)).
  {#MOMGD.5-2} A carried dev insertion does not depend on the slot values (D2.6 closure 4.2(iii), class (3)), by induction on the production step. A dev group of step j ≥ 2 has no polymer component, no member's domain meeting the one-cube neighbourhood of Λ_jᶜ, and no slot in its Gaussian factor (D2.6 closure 2.1(i), with 2.2's localisation of the ω′-channels), and only dev members (*Merged groups*).
  {#MOMGD.5-3} At step 1 it is built from Υ⁰_W of a good group, a^Λ_W·id and the interval transport. Υ⁰_W is fixed by its traces c⁰_W − a^Λ_Wχ (IT-1 note §3a(1); Burnside for the irreducible π, any compact G), which consult no outer variable (IT-1 note §3d(4); D2.6 closure 4.2(iii), *Step 1*).
  {#MOMGD.5-7} *The covariance.* Lemma 1 complexifies Cov: if an insertion is analytic on a gauge-invariant domain and obeys Cov(j) there (#MD2.2.4.3–5), the law holds for every G^c-valued u joined to 1 by a path along which the transformed datum stays in the domain. This is the identity theorem on the totally real G^{sites}. Cov(j) holds on the production domain 𝒟_W, which is gauge invariant (#MD2.2.6.45-9), so the step owes no clause beyond Cov(k+1) and D(k+1)(iii).
  {#MOMGD.5-9} *The gain.* With the interval transport factored out and u(x_W) = 1, a complex gauge transformation, linear in a (2.38)-smooth gauge, reduces the complex part on X_W to K₁δ_Wa.
  {#MOMGD.5-10} Here δ_W := 4ML^{−m}σ_j(W), m := k+1−j, bounds X_W's path diameter in step-(k+1) units. The excess per insertion is ≤ 2(4/R)S_We^{νσ_j(W)/8192}, with 4/R ≤ (1+β₀)²m^{1/2}L^{−m}(8K₁δ_W/μ + 24L^{−2m}) (note §3).
  {#MOMGD.5-12} *The bound.* The generation sum is ≤ Ĉ·max_jN^{(j)}·ρ_{k+1}pl, with Ĉ depending on L, M, ν_r, β₀, (2.38)'s cube constant C, and C_avC₁/C₀ only (K₁ ≤ 3 and K₂ ≤ 2, note §2; the radius ratios are bounded below by functions of m, note §0). δ_W is paid from the free eighth of the reserve.
  {#MOMGD.5-15} The covariant regime is δ_W ≤ δ̄₀ := min(δ̄, μ), with δ̄ := min(1/2, CM/(2L)) (note §2–§3); it does not depend on m.
  {#MOMGD.5-16} Beyond it, Cauchy's estimate alone is used, on the disc R′ of note §3 with an L^{2m} cap, and the trivial bound 2S_W for the finitely many m < m₀ (by D2.2(4)(f)'s chain condition with CRE p.277's margin, with (2.37) and (2.35) from #MD2.2.6.142's joint derivation with RMJ). This gives the constant c_nc of note §3, which depends on L, C_avC₁/C₀ and β₀ only (m₀ is defined through k-independent lower bounds of R′'s entries), and the weight e^{−ν_rδ̄₀L^m/(64M)}.
  {#MOMGD.5-17} The covariant disc's inverse transport is ≤ e^{νσ_j(W)/8192} by #MD2.4.13.19's c_π′α·4096M ≤ ν, paid from the reserve, so the complex-data part has weight (15/16 − 1/8192)ν_r.
  {#MOMGD.5-18} *Checks.* (K1) is CRE p.261 (ii): every cube of the stated size. (K2) follows from CRE pp.254–256 and (3.5): partition cubes of side MR_{k+1}, and a collar ≥ 8MR_{k+1}.
  {#MOMGD.5-20} (K3) gives (2.35)/(2.37) at the path and disc points by RG1 (1.17), with VAR's multi-domain bounds up to ∂X, once the C_av-weighted curvature is ≤ (3/4)α_{0,j}L^{−2j}. For this the covariant disc is reduced by μ := min(1, MC₀/(2C_avC₁)) (no condition on M; C₁ = λ_RC₀, table #T2.24), and the base curvature 3B₃ε_{k+1}L^{−2(k+1)} (CRE p.268) and the quadratic term are absorbed for g_K small (ε_{k+1}L^{−2m}/α_{0,j} → 0 uniformly in m by q₀ > p₀; note §3(b)).
  {#MOMGD.5-22} *The region (note §5).* SW §6(6c)'s (LPG′) on 𝒬^{(j)} at step k+1 is not used. The real-point part is (T-dev), dev insertions carrying no slot (#MOMGD.5-2); its (LPG′) runs at step j for U_j(V_j^*) = U_{k+1}, on step-j cubes (#MD2.4.5.13 (1)–(2)). The excess uses only (2.38)'s gauge on a CM- or CM/L-cube, and no π_{k+1}-hull.
  {#MOMGD.5-27} Added constants: L ≥ 12(1+β₀)² and L > (1+β₀)⁹ (both implied by L ≥ L₀ = 5000 with β₀ ≤ 1/2), the disc factor μ, the regime δ̄₀, c_nc and m₀, the reserve weight (15/16 − 1/8192)ν_r, and B₃ ≥ 1 (note's constant list).
{#MD2.4.12.49-5} With ρ̃_k/ρ̃_{k+1} ≤ (1+β₀)⁸ ((6)), ρ_k ≤ (1+β₀)⁶ρ_{k+1}, pl_k ≤ (1+β₀)pl_{k+1} (CRE (2.7), p.255, as in (6)), ε̄^{old} + ε̄^{ref,k} ≤ 2L⁴C(M/ν_e²)C^{(k)}ρ_k·pl_k ((e)), and C_Tb_k/ᾱ_k ≤ C_TC₁^{RG2}A₁(log g_k^{−2})^{p₀−q}/min_iC_i (q := min(q₀, q₁); α_{i,k} = g_kC_i(log g_k^{−2})^{q_i}, CRE p.277's margin; (11)(b), (c)):
  {#MD2.4.12.50} C^{(k+1)} ≤ 2C_winC_M + θ_kC^{(k)}, θ_k := L^{−1}(1+β₀)^{15} + (1+β₀)⁷[2C_winK_βC_TC₁^{RG2}A₁(log g_k^{−2})^{p₀−q}/min_iC_i + 4L⁸C(M/ν_e²)²C_winC^{(k)}ρ_k·pl_k/ε_*].
  {#MD2.4.12.51} L^{−1}(1+β₀)^{15} ≤ 1/8 under 8(1+β₀)^{15} ≤ L, which holds for L ≥ L₀ and β₀ ≤ 1/2 (CRE (2.6) allows it, D2.2(6)(f) *L.*); the quadratic term is ≤ 1/8 for g_K small once C^{(k)} is bounded (below); the (β) term is ≤ 1/4 under *(q₀ = q₁ > p₀)*: q > p₀, when (log g_k^{−2})^{p₀−q} → 0 for g_K small (q₀ = q₁ > p₀ is SW closure §2's choice; it meets CRE p.277's margin's entailments q₀, q₁ ≥ p₀ and (6)(ζ)'s q₀ ≤ q₁, and is provisional against any printed upper bound on q in terms of p₀).
  {#MD2.4.12.51-2} Then θ_k ≤ 1/2 and C^{(k)} ≤ max(C^{(1)}, 4C_winC_M) for the real-point recursion above.
  {#MD2.4.12.51-3} The complex-data part replaces it by #MD2.4.12.49's recursion and C_S′ := max(2(1+Ĉ)C^{(1)}, 8(1+Ĉ)C_winC_M), for every k ≤ K, the induction closing with the g_K-smallness fixed from C_S′ (C^{(1)} is V4's, (c4-6-5) with V4 sec:c4-6-2 for the reference gas).
  {#MD2.4.12.51-4} The c-version gives the Kotecký–Preiss condition for the step-(k+1) reference gas with a°(𝒢) = (ν/32)σ_{k+1}(𝒢) at a°/2 (positions of 𝒢 ≤ 81Mσ_{k+1}(𝒢), times C_S′ρ_{k+1}pl ≤ ν/(64·81M)), hence θ_ref ≤ a° by FV Lemma 5.6, (5.17), θ_{k+1} = θ_vac + θ_ref ≤ νσ_{k+1}/16 ((3), (12)(b) *Order*), and
  {#MD2.4.12.52} (S-w) Σ_{𝒢 at p}e^{θ_{k+1}(𝒢) + ν_rσ_{k+1}(𝒢) + ν_e·ext_{k+1}(𝒢)}S_𝒢ℓ_{X(𝒢)} ≤ C_S′ρ_{k+1}·pl, pl = 1 + (log g_k^{−2})^{(q₁−q₀)₊},
{#MD2.4.12.53} with the c-version, uniformly in k ≤ K. The root sum Σ_{𝒢∋b}|c_𝒢|e^{2a°(𝒢)} ≤ C_S′ρ_{k+1}·pl at every step-(k+1) traversal b, i.e. (13)(b) with C_KP := C_S′ (at a bond of X(𝒢) off C, ≤ 16C_S′ρ_{k+1}·pl).

### (13) Step 4 of (S): The Rate Comparison, the Root Sum for (Z), and the Difference Count {#MSD2.4.13}

{#MD2.4.13.1} *(a) The rate comparison is one inequality.* With (12)(b)'s extent weight inside (S-w), no comparison of Bałaban's decay e^{−κd_{k+1}} with w_t is needed: the decay in t comes from e^{ν_e·ext_{k+1}(𝒢)} alone.
{#MD2.4.13.1-1} If t(𝒢) = t ≥ 2, then X(𝒢) ⊄ B_∞(n′, R_{t−1}^{(k+1)}) = B_∞(n′, C_boxMt) by (4)'s definition of t_{n′} (#MD2.4.4.7), so some cube of X(𝒢) lies at ℓ∞-distance > C_boxMt − M step-(k+1) units, at least C_boxt − 2 cube sides, from n′, and ext_{k+1}(𝒢) ≥ C_boxt − 2 (the extent is from every traversal of I(𝒢), n′ among them).
{#MD2.4.13.1-2} Hence
  {#MD2.4.13.2} Σ_{𝒢∋n′, t(𝒢)=t}e^{θ_{k+1}(𝒢)}S_𝒢ℓ_{X(𝒢)} ≤ e^{−ν_e(C_boxt−2)}·Σ_{𝒢∋n′}e^{θ_{k+1} + ν_e·ext_{k+1}}S_𝒢ℓ ≤ e^{2ν_e}C_S′ρ_{k+1}·pl·e^{−(η_V/2)t} ≤ C_Sρ_{k+1}·pl·w_t,
  {#MD2.4.13.3} since ν_eC_box = ν/2 = η_V/2 > η_w = (5/16)η_V and (t+1)³ ≥ 1; C_S := e^{2ν_e}C_S′ with (12)(f)'s C_S′, and t = 1 is the unrestricted sum.
  {#MD2.4.13.3-1} This is (S) of (7) (with (12)'s pl), and summed over t′ ≥ t it is (ii-t) for the new groups with W_t at the rate η_w ((5) *New groups*), with the constant C_new = C_gC_S·pl/c₀ in (5)'s (ii-t) (the pl is not absorbed into c₀).
  {#MD2.4.13.3-2} The rate per cube side is ν_e = η_V/(2C_box); the comparison holds for every C_box, and C_box ≥ 4A_E is (12)(b) *Base*'s constraint (the SW route needs also C_box ≥ 6, so C_box ≥ max(4A_E, 6) = 4A_E); R_t^{(k)} = C_boxM(t+1) with the same C_box at every step ((6)(γ)).
  {#MD2.4.13.3-3} Bałaban's rate r_κ and the slots' κ_s are spent entirely on the charges and the entropy ((12)(d), (f)), which is where the counting needs them: a cube of M∖D′ costs log 64 + O(1) against r_κ/648, and the unit of #(G_M), a π_k-cube of the components, costs 81c_DL⁴log2 + 20c_Dr_κ + O(1) against κ_s/4, both independent of t.

{#MD2.4.13.4} *(b) The Kotecký–Preiss root sum for (Z) (D2.3(4)(Z-d); given (S-w); on the trivial-label term ℓ₀, where (Z) lives, D2.0(3)(vi), (Z-e): off ℓ₀ the att and coll groups have amplitude b_k, D2.6 closure 2.2, *The rooted sum*).* The c-version of (S-w) ((12)(f)) gives, for the step-(k+1) reference gas, FV (5.10) for the tilted activities |c_𝒢|e^{a°(𝒢)} with a := a° = (ν/32)σ_{k+1}(𝒢) (Σ_{𝒢′≁𝒢}|c_𝒢′|e^{2a°(𝒢′)} ≤ a°(𝒢), (12)(f)'s Kotecký–Preiss condition at a°/2), so by FV (5.11), for every step-(k+1) traversal b,
  {#MD2.4.13.5} Σ_{Γ∋b}|Φ°(Γ)|e^{a°(Γ)} ≤ Σ_{𝒢∋b}|c_𝒢|e^{2a°(𝒢)} ≤ C_S′ρ_{k+1}·pl = C_KPρ_{k+1}·pl (#MD2.4.12.53),
  {#MD2.4.13.6} since 2a° = (ν/16)σ_{k+1} is inside (S-w)'s weight.
  {#MD2.4.13.6-1} The weight a°(𝒢) ≥ a_min·n_ins(𝒢) with a_min = ν/(32LM) ((12)(a)).
  {#MD2.4.13.6-2} The amplitude is ρ_{k+1}·pl, not τ_k² ((7)(R)).

{#MD2.4.13.7} *(c) The difference count for (Z-e) at the group and cluster levels, and the vacuum tail (in the form (Z-d) needs: one old factor replaced by its T–T′ difference).* For a torus pair T ⊂ T′ of (H3) write ι := ι_{T,k+1}, with "embeds" as in (Z-e).
{#MD2.4.13.7-1} A T–T′ difference of c_𝒢 or Y_𝒢 (embedding 𝒢) has three sources:
- {#MD2.4.13.8} *old vertices and touched insertions:* ΔY_W and Δφ_k(Γ), bounded by the step-k input, the per-position form of (vi)_k ((Z-e) (I), (O) as restated in D2.3(4)) with the full (ii-w) weight, ε^{diff}_k := sup_p[Σ_{W at p}e^{θ_k(W) + ν_rσ_k(W) + ν_e·ext_k(W)}ℓ_{X_W}·sup|ΔY_W| + Σ_{𝒢 at p}e^{(ν/16 + ν_r)σ_k(𝒢) + ν_e·ext_k(𝒢)}ℓ_{X(𝒢)}·sup|Δc_𝒢|] ≤ C_rel^{(k)}e^{−c_kι_{T,k}}ρ_k·pl_k, the sup over the step-k traversals p, which is the inductive clause (Δ := the T–T′ difference at the lifted data, (Z-e); the 𝒢 are the groups made at step k;
  {#MD2.4.13.8-1} sup|ΔY_W| is taken over the complex data as (12)(e) takes ε^{old}, (5)'s size O(ρ_k·pl) away from older layers with SW closure §3, the constant in C_rel).
  {#MD2.4.13.8-2} At a π_k-cube the sum is not carried, since a per-cube clause carries a factor ~L² ((12)(e)): it is obtained afresh at each step from the traversal clause by (12)(e)'s box reduction, with weight e^{θ + ν_rσ + (3/4)ν_e·ext} and constant C(M/ν_e²), which still contains sh + b (extent part (3/8 + 1/L)ν_e·ext; no window spare is needed at cubes), and the new objects at cubes come from (12)(f)'s cube-rooted count.
  {#MD2.4.13.8-3} At a traversal the weight contains e^{sh(v)+b(v)} and the window and box spares of (12)(e) up to e^{2c_sh}, and the Γ-vertices (clusters of the step-k reference gas) are bounded by the group part through the cluster level below at step k, whose d carries their per-member constants, so Σ_{v old at p}|Δw̃(v)|e^{b(v)} ≤ K₀ε^{diff}_k, K₀ := (1 + 2e)e^{2c_sh}C_pc′ (C_pc′ the per-piece constant of (12)(e)'s w̃), with Δw̃(v) := e^{sh(v)}·sup|act_T(v) − act_{T′}(ṽ)|, and (12)(e)'s window and box sums run with ε^{diff}_k in place of ε^{old}.
  {#MD2.4.13.8-4} A mark on a touched W ∈ 𝔅(M) sits inside the M-vertex: the first-order variation of the touched-insertion product, in (12)(f)'s two-stage count, is ≤ (81#(G_M) + Ln_{k+1}(M))·ε̄^{diff}_k·e^{(#(G_M)+#(M))/8} ≤ (ε̄^{diff}_k/ε_*)b(v)/2 times the vertex's weight (ε̄^{diff}_k := L⁴C(M/ν_e²)K₀ε^{diff}_k, which bounds the sum at a step-(k+1) traversal, LK₀ε^{diff}_k, and at a π_{k+1}-cube, L⁴ derived cube sums, as ε̄^{old} in (12)(e)) — the first term of (12)(f)'s F recursion;
- {#MD2.4.13.9} *the vacuum factors of an M-vertex:* e^{−Ψ°(M)}, δΨ(M) and the links' x_T are sums over all vacuum clusters incompatible with M, including those that do not embed in T. By (Z-c) and (vac)_{k+1} the embedding clusters of T (dependence diameter < ι/4, as in (vac)) and their lifts have the same values at the lifted data;
  {#MD2.4.13.9-1} every other cluster of T or T′ incompatible with M (or M̃) has dependence diameter ≥ ι/4, hence support diameter ≥ ι/4 − 2R_D ≥ ι/8 under (TC) (a vacuum cluster's dependence set lies in the R_D-neighbourhood of its support, (Z-g)'s margin, its activity being made of the same localised functions), and #(𝒞) ≥ ι/(8M).
  {#MD2.4.13.9-2} So |Δ(vacuum part)| ≤ C_ve^{C_v′c#(M)}·tail(M) (each of e^{−Ψ°(M)}, δΨ(M) and the x_T is an exponential or a sum of the cluster activities incompatible with M, bounded by e^{18C_pc′c#(M)} by (12)(e)'s vacuum sum, so its T–T′ difference is Lipschitz in the tail with such constants, C_v, C_v′ absolute), tail(M) := Σ_{𝒞≁M, #(𝒞)≥ι/(8M)}2·2^s|φ^T(𝒞)|_sup, on T and on T′, ≤ 36c#(M)e^{−ι/(32M)} by (12)(e)'s vacuum sum with its spare e^{#(𝒞)/4}.
  {#MD2.4.13.9-3} Put δ_vac := sup_pΣ_{v M-vertex at p}|Δ_vacw̃(v)|e^{b(v)} ≤ C_vacε^{new}e^{−ι/(32M)}, the #(M) and e^{C_v′c#(M)} absorbed by the second unit of exponent per cube of M reserved in (12)(f) (C_v′C_pc′c ≤ 1/2 under κ ≥ κ_pc, (12)(e) *The vacuum sum*) (the first pays (e)'s window decay).
  {#MD2.4.13.9-4} The new parts of H̃(M) are exactly local ((Z-c)) and have no difference of their own;
- {#MD2.4.13.10} *the Ursell coefficients* of the clusters: equal on T and T′ for embedding clusters (geometric, (Z-d)).
{#MD2.4.13.11} *Group level.* Telescoping c_𝒢 (or Y_𝒢) over the vertices, each term has one marked vertex: an old vertex, or an M-vertex marked by its vacuum tail or by a touched insertion.
{#MD2.4.13.11-1} Root at the vertex at p as in (12)(f) (the marked-vertex lemma uses its mark hypothesis only in the form Σm·e^{b/2} ≤ (ε_m/ε_*)b/2, which the touched-insertion mark m ∝ b(v)w̃(v) satisfies since be^{b/2} ≤ (2/e)e^{b}), with m := |Δw̃| on the old vertices (ε_m = K₀ε^{diff}_k at a traversal, ε̄^{diff}_k at a cube) and m := |Δ_vacw̃| (or the touched-insertion variation) on the M-vertices (ε_m = δ_vac + (ε̄^{diff}_k/ε_*)·ε^{new});
{#MD2.4.13.11-2} a group whose difference mark is on an old vertex and which has an M-vertex is counted with the M-mark of (12)(f) as well (two marks with ratios λ, λ′: F₂ ≤ 6λλ′b·e^{3b/4}, which closes the same induction with T ≤ e^{b/2}, F ≤ λbe^{b/2} and be^{−b/4} ≤ 4/e; a bound in b² would not dominate the terms linear in b when b < 1), and one without an M-vertex is M-free, hence quadratic as in (12)(f), the trivial group {W} being the carried insertion's own difference ((6)'s carry of (vi)_k;
{#MD2.4.13.11-3} the dev form at k+1 follows since (4)'s Cauchy step applies to ΔY_W, which vanishes at flat data as both terms do, with b_W^Δ in place of b_W, proportional to sup|ΔY_W|/ᾱ).
{#MD2.4.13.11-4} So, with the (S-w) weight at every step-(k+1) position, cubes included (the new groups at cubes from (12)(f)'s cube-rooted count, with the marks' cube sums ε̄^{diff}_k),
  {#MD2.4.13.12} δ_{k+1} := sup_pΣ_{𝒢 at p}e^{(ν/16 + ν_r)σ_{k+1}(𝒢) + ν_e·ext_{k+1}(𝒢)}ℓ_{X(𝒢)}|Δc_𝒢| ≤ K_Δ[(ε^{new} + ε̄^{old} + ε̄^{ref,k})/ε_*]·ε̄^{diff}_k + 2C_winδ_vac,
{#MD2.4.13.13} and the same for the new insertions' differences ΔY_W with (ii-w)'s weight; these two parts at the step-(k+1) traversals with the carried part (an old W keeps σ, ext and θ ((12)(b) *It carries*), and a carried W's sup|ΔY_W| at step k+1 is its step-k value, the agreement radius ι_{T,k+1}/4 step-(k+1) units being ι_{T,k}/4 step-k units, (Z-e)(c);
{#MD2.4.13.13-1} a step-(k+1) traversal is met by L step-k traversals, so the carried part is ≤ L·ε^{diff}_k per traversal: the sup form is not dev-normalised, and (6)'s L^{−1}(ρ̃_k/ρ̃_{k+1}) does not apply to it) make ε^{diff}_{k+1}, whose cube sums are derived as above and whose Γ-vertices at step k+2 are bounded through the cluster level below.
{#MD2.4.13.13-2} With ε^{new} + ε̄^{old} + ε̄^{ref,k} ≤ C″C_S′ρ_{k+1}·pl_{k+1} ((12)(e)–(f); C″ depends on L, M, ν_e, β₀ and C_win, C_M through the box factor L⁴C(M/ν_e²)) and ε^{new} ≤ C″C_S′ρ_{k+1}·pl_{k+1}:
  {#MD2.4.13.14} ε^{diff}_{k+1} ≤ [L + 2L⁴C(M/ν_e²)K₀K_ΔC″C_S′ρ_{k+1}pl_{k+1}/ε_*]·ε^{diff}_k + 4C_winC_vacC″C_S′ρ_{k+1}pl_{k+1}·e^{−ι/(32M)},
{#MD2.4.13.15} so with c_k := c := 1/(32M) for every k (the step-1 rate is unrestricted, D2.3(4)(Z-h)), ι_{T,k} = Lι_{T,k+1}, ρ_k·pl_k ≤ (1+β₀)⁷ρ_{k+1}·pl_{k+1} ((12)(f)) and the second term in the bracket ≤ (1+β₀)^{−7}/8 for g_K small, and with the inductive statement ε^{diff}_k ≤ C_rel^{(k)}e^{−cι_{T,k}}ρ_k·pl_k (the derived cube sums are then ≤ C(M/ν_e²) times this, and (O)_k ≤ 2e^{2c_sh+1}C_pc′ times this, (Z-e); the recursion uses them in this form, through ε̄^{diff}_k and K₀): put C_rel^{(k+1)} := (L(1+β₀)⁷ + 1/8)e^{−c(L−1)ι_{T,k+1}}C_rel^{(k)} + C⁎, C⁎ := 4C_winC_vacC″C_S′.
{#MD2.4.13.15-1} Then ε^{diff}_{k+1} ≤ C_rel^{(k+1)}e^{−cι_{T,k+1}}ρ_{k+1}·pl_{k+1}, and, since the bound on δ_{k+1} above does not depend on the position, δ_{k+1} ≤ C_rel^{(k+1)}e^{−cι_{T,k+1}}ρ_{k+1}·pl_{k+1} at every step-(k+1) position, cubes included.
{#MD2.4.13.15-2} The contraction is e^{−c(L−1)ι_{T,k+1}} (ρ_{k+1}·pl only makes the new-group term small): (TC) gives ι_{T,k+1} ≥ ι_{T,K} ≥ 96L⁴M(L+1) for k+1 ≤ K (D2.3(4)(Z-g), #MD2.3.4.53), so c(L−1)ι_{T,k+1} ≥ 96cML⁴(L²−1), and with β₀ ≤ 1/2, (L(1+β₀)⁷ + 1/8)e^{−c(L−1)ι_{T,k+1}} ≤ 1/2 once 96cML⁴(L²−1) ≥ log(35L): for c = 1/(32M) this is 3L⁴(L²−1) ≥ log(35L), true; no other value of c occurs, since D2.3(4)(Z-h) gives C_rel^{(1)} = 0 with no step-1 rate.
{#MD2.4.13.15-3} Hence C_rel^{(k)} ≤ max(C_rel^{(1)}, 2C⁎) uniformly in k and in the torus.
{#MD2.4.13.15-4} The sup form here is the inductive clause; it implies (Z-e)'s form relative to D(k)(ii)'s right side (the Cauchy step of (4) applied to ΔY_W, which vanishes at (1, 0) on both tori, with the extent weight's decay in t and the Abel summation of (5)), so (5)'s conversion constant is applied once, not iterated.
{#MD2.4.13.15-5} In the telescoped products each unmarked factor is bounded by |c^T| + |c^{T′}| (or the same for w̃), which doubles the rooted sums: (12)(e)'s condition and the KP check below hold with the factor 2 for g_K small.
{#MD2.4.13.16} *Cluster level.* For a cluster Γ of the step-(k+1) reference gas, Φ°(Γ) = (Ursell coefficient)·∏_{𝒢∈Γ}c_𝒢, the coefficient depending only on the incompatibility graph, the same on T and T′ for embedding Γ.
{#MD2.4.13.16-1} So ΔΦ°(Γ) telescopes over the groups of Γ, and the marked-vertex lemma of (12)(f) applies with vertices := groups, links := incompatibility, FV Thm 5.4's split a := a°, d(𝒢) := ν_rσ_{k+1}(𝒢) + ν_e·ext_{k+1}(𝒢) + 2c_sh + 1 + log C_pc′ (d := 0 for the unweighted form;
{#MD2.4.13.16-2} the log C_pc′ pays the per-member factor of a Γ-vertex's C_v at step k+2, (12)(e)), weights |c_𝒢|e^{a°(𝒢)+d(𝒢)}, charges a°(𝒢) = (ν/32)σ_{k+1}(𝒢), the threshold δ_* := ν/(64·81M) (positions of 𝒢 ≤ 81Mσ_{k+1}(𝒢)) and the Kotecký–Preiss check Σ_{𝒢′≁𝒢}|c_𝒢′|e^{2a°+d} ≤ 81Mσ_{k+1}(𝒢)·e^{2c_sh+1}C_pc′C_S′ρ_{k+1}pl ≤ a°(𝒢)/2 for g_K small, on T and on T′, which uses exactly (12)(f)'s weight e^{(ν/16 + ν_r)σ + ν_e·ext}ℓ_X with ℓ_X ≥ 1 ((4), #MD2.4.4.8) (zero margin in σ);
{#MD2.4.13.16-3} FV Thm 5.4's tree-graph bound on the Ursell coefficients is multilinear in the weights, so the marked version holds with δ^d_{k+1} := sup_pΣ_{𝒢 at p}|Δc_𝒢|e^{2a°+d} ≤ e^{2c_sh+1}C_pc′δ_{k+1} and F_g(𝒢) ≤ (2δ^d_{k+1}/δ_*)a°(𝒢)e^{a°(𝒢)/2}, and, with d(Γ) := Σ_{𝒢∈Γ}d(𝒢), at every position p,
  {#MD2.4.13.17} Σ_{Γ at p, embeds}|Φ°_T(Γ) − Φ°_{T′}(Γ̃)|e^{d(Γ)} ≤ Σ_{𝒢 at p}[|Δc_𝒢|e^{a°+d}T_g(𝒢) + |c_𝒢|e^{a°+d}F_g(𝒢)] ≤ δ^d_{k+1} + (2δ^d_{k+1}/δ_*)Σ_{𝒢 at p}|c_𝒢|e^{2a°+d} ≤ δ^d_{k+1}(1 + 2e^{2c_sh+1}C_pc′C_S′ρ_{k+1}pl/δ_*) ≤ 2δ^d_{k+1} ≤ 2e^{2c_sh+1}C_pc′δ_{k+1}
{#MD2.4.13.18} for g_K small; with d := 0 the same gives Σ_{Γ∋b, embeds}|ΔΦ°(Γ)| ≤ 2δ_{k+1} ≤ 2C_rel^{(k+1)}e^{−cι_{T,k+1}}ρ_{k+1}·pl (δ_{k+1}'s bound at every position, above).
{#MD2.4.13.18-1} The d-weighted form bounds the Γ-vertices of ε^{diff}_{k+1}, with their shares, charges and C_v, by 2e^{2c_sh+1}C_pc′ times its group part (the term 2e·e^{2c_sh}C_pc′ of K₀), which closes the recursion above; the unweighted form is the input of (Z-d), with G := 2 and the amplitude ρ_{k+1}·pl; with the non-embedding clusters bounded by the a°-weight (D2.3(4)(Z-f)), C_Z^{(k+1)} = 2C_S′ + 2C_rel^{(k+1)} (k+1 ≥ 2; C_Z^{(1)} = 4C_S′, #MD2.3.4.49) at the rate c^Z = min(c, ν/(256A_dM)) = ν/(256A_dM).
{#MD2.4.13.18-2} *Inputs from outside (c):* the step-1 base of ε^{diff} in the per-position weighted form (D2.3(4)(Z-h), from the exact locality of V4's representation: the left side is zero); (12)(b) *It carries* for the carried part; the sub-domain form of D(k)(iii)-dev (SW closure §3) for the old factors at complex backgrounds; (vac)_{k+1} and (Z-c) of D2.3(4); the margin of "embeds" (R_D ≤ 6L²MR_k, (Z-g)).

{#MD2.4.13.19} *(d) What (S) is.* Given the amendments (12)(a)–(b) and (q₀ = q₁ > p₀) of (12)(f), under κ ≥ κ_D′, L ≥ L₀ = 5000, 8(1+β₀)^{15} ≤ L (β₀ ≤ 1/2; CRE (2.6) allows it for g small, D2.2(6)(f) *L.*), C_box ≥ 4A_E, κ_s ≥ κ_s^{(12)} (after κ, L; before M; raised by ν_e by (12)(f)'s (T2)), M ≥ 100 (which also puts the composite range of C and D̃, three blocks, within one π_{k+1}-cube side; D2.6 closure 2.1),
{#MD2.4.13.19-1} c_π′α_{1,k+1}·4096M ≤ ν at every step k ≥ 0, that is, c_π′α_{1,j}·4096M ≤ ν for every j ≥ 1, the covariance note §3(b)'s condition at index j ((12)(d)'s transports and the covariant disc of #MOMGD.5;
{#MD2.4.13.19-2} with the reserve weight (15/16 − 1/8192)ν_rσ and the constants c_nc, m₀, μ of the covariance note §3) and c_π′α_{1,k+1}M ≤ ν/64 ((8), for σ = # + n/M);
{#MD2.4.13.19-2-1} δ₂R₁M₁ > 3log L + 1 with δ₂ of #MD2.2.6.142-55 (true for g₀ small) and the Hölder exponent β_H = 1/2 (#MD2.2.6.142's (2.35) and (2.37) at the evaluation points, proved jointly from 𝐁_p(X)'s definition (CRE p.256 l.57–63), q₀ = q₁ > p₀, and CRE (2.6)–(2.7) (printed, p.255), RG2 p.5's all-norms bound (printed) and the 𝐇-decay (Bałaban's, CRE p.267 l.42–44, p.277 l.6–8) (RMJ, CRE p.277's margin's (2.37) part, with the step-k constant at every evaluation point, wider than p.277's print;
{#MD2.4.13.19-3} WILSON_IT1_RMJ_CLOSURE_2026_10_30.md, #MOMGD.50), with C′ enlarged by the factor C_{(2.35)}/C of #MD2.2.6.142-69 and C′ ≥ C_{(2.37)} of #RMJ.6.5), r_κ/648 ≥ 8 ((12)(f)), the conditions of (10)–(11) (972A ≤ δλ_Lκ, RG2 Lemma 3's repair's list, 20c_π′M‖a′‖_∞ ≤ 1 on the arcs of (4)(e) and ≤ ν_r/16 on the slot arcs of (11)(c)(β)), ν ≤ 1/1000, CRE p.277's margin with (q₀ = q₁ > p₀), the torus condition (TC) of D2.3(4) for the vacuum tail, w_t at the rate η_w = (5/16)η_V (with ν_e := ν/(2C_box);
{#MD2.4.13.19-4} D2.6 closure §6.5), and g_K small, and given the inputs of (11)(g) (the polylog absorbed in pl = 1 + (log g_k^{−2})^{(q₁−q₀)₊}): (S) of (7) holds in the form (S-w) at each step k+1 given (ii-w) at step k with C^{(k)} bounded ((12)(f); uniformly in k ≤ K, with #MOMGD.5's complex-data part of the carried insertions), with (a)'s rate comparison (C_S := e^{2ν_e}C_S′;
{#MD2.4.13.19-5} the entropy per π_k-cube of the components, the unit of #(G_M), is 81c_DL⁴log2 + 20c_Dr_κ + O(1) against κ_s/4, and per cube of M∖D′ log 64 + O(1) against r_κ/648), and (ii-t) for the new groups with the constant C_new = C_gC_S·pl/c₀ in (5).
{#MD2.4.13.19-6} With it: the Kotecký–Preiss condition for the reference gas and θ_ref ≤ (ν/32)σ_{k+1}; the root sum for (Z) with a_min = ν/(32LM) and C_KP = C_S′ ((12)(f), (b)); the group- and cluster-level difference counts and the recursion of C_rel with the vacuum tail ((c)); for (Z) the reference-gas KP weight a° = (ν/32)σ_{k+1} itself bounds the extent of a cluster (a°(Γ) ≥ (ν/(64M))·diam for k+1 ≥ 2, and at k+1 = 1 the rate c^Z of D2.3(5)'s envelope count, D2.3(4)(Z-f), #MD2.3.4.49), and D2.3(5)–(7) use the tail (T′).
{#MD2.4.13.19-7} *Inputs from outside (S):* (T-dev)'s other inputs (#MD2.4.5.13), D2.3(3)'s hard-core reference gas (for (7)(R)), the k = 1 base point on Ω₁∖Ω₂, and D2.6's collar species; (LPG′) and the complex-data dev clauses (SW closure §5–§6); (Z)'s step-1 base, D2.3(4)(Z-h) (#MD2.3.4.54).
{#MD2.4.13.19-8} *The four inputs (WILSON_IT1_SW_CLOSURE_2026_10_24.md):* the kinds (γ)/species are a restriction of scope (the groups (i)–(iii) of §1(a1)), whose remainder is D2.6's bound (§1(a4); paid in the D2.6 closure §2.1–§2.2 at real σ_k, through O6 at complex σ_k); the older-layer size is removed by the sub-domain form of D(k)(iii)-dev (§3, a changed inductive hypothesis); the polylog by q₀ = q₁ > p₀ (§2; pl = 2);
{#MD2.4.13.19-9} the dev clause for the new groups by (LPG′) (§5, its (17) and (17b)), and for the carried insertions by §6(6c) and WILSON_IT1_COMPLEX_COVARIANCE_2026_10_29.md (#MOMGD.5), given (T-dev)'s inputs, SW §6(6d), that note's averaging bound (K3) (C_av := 2(B₃ + 2c_dB₅); #MOMGD.5), and D2.2(4)(f)'s chain condition with CRE p.277's margin, #MD2.2.6.142's inputs, and RMJ (#MD2.2.6.142, #MOMGD.50).
{#MD2.4.13.19-10} C_box ≥ max(4A_E, 6) there.
{#MD2.4.13.19-11} With them (S-w) holds at each step with pl = 2 and C_S = e^{2ν_e}C_S′.

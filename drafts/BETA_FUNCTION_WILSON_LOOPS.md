# The Beta Function for the Wilson-Loop Analysis

{#BP.1} This file contains the coupling-flow results that the Wilson-loop renormalisation-group analysis uses, with their
{#BP.2} proofs.
{#BP.2-1} It is extracted from `D:\University\Oxford PostDoc\Balaban\ONE_LOOP_PROOFS.md`.
{#BP.2-2} The proofs use Bałaban's papers,
{#BP.3} cited by printed page and equation and pinned in `D:\University\Oxford PostDoc\Balaban\sidecar\QUOTES.md` or in a sidecar
{#BP.4} contract (`D:\University\Oxford PostDoc\Balaban\sidecar\BalabanSidecar\`), and arguments given here.
{#BP.4-1} READINGS.md is
{#BP.5} `D:\University\Oxford PostDoc\Balaban\READINGS.md`.
- {#BP.6} RG1 = CMP 109; RG2 = CMP 116; CRE = CMP 119; LFR1 = CMP 122 175–202; LFR2 = CMP 122 355–392;
- {#BP.7} PRT1 = CMP 95; PRT2 = CMP 96 223–250; CMP98 (also AVG) = CMP 98 17–51; REG = CMP 99 75–102; PBG = CMP 99 389–434;
  {#BP.8} UV3 = CMP 102 255–275; VAR = CMP 102 277–309.

{#BP.9} G is a compact simple group, d = 4, and L is odd.
{#BP.9-1} §10 treats semisimple G: Proposition 10.2 reduces additive actions to
{#BP.10} the simple factors.

## 0. The Result {#BS0}

{#B0.1} The coupling flow is RG1 (2.15), p.268, as in RG1 (0.20):

  {#B0.2} 1/g_k² = 1/g_{k+1}² + β_{k+1}(g_0, …, g_k),

{#B0.3} where β_{k+1} is defined by RG1 (1.20)–(1.22), p.264, from the step term of RG1 (1.6), and b_{k+1} is its value at
{#B0.4} zero coupling (Remark 2.3).
{#B0.4-1} The step terms are those of RG1's construction run with CRE's fluctuation cutoff
{#B0.5} δ_k = g_k(A₁/A₀)p₀(g_k) (CRE p.265, (3.16) p.268) on RG1's fixed domains (§0, *Condition 3*).
{#B0.5-1} Let κ > 0 be defined by
{#B0.6} K = κ·tr (Lemma 1.1), and put c := (11/48π²)κ.
{#B0.6-1} Notation: the letters δ, K, and κ carry several meanings, each fixed
{#B0.7} by its context, as in the sources. δ without an index is the window constant of item 3 in §§0 and 2, and a decay or
{#B0.8} smallness constant of RG2, CRE, or UV3 where those are quoted (RG2 (1.36), Proposition 2.4, step 2, Lemma 2.8, CRE
{#B0.9} p.251); δ_k = g_k(A₁/A₀)p₀(g_k) is CRE's cutoff (δ_0 at step 0, δ^T_k in the tube construction), and δ₀ is the decay
{#B0.10} rate of VAR and of the random walks of RG2 (1.7).
{#B0.10-1} K is the Killing form in Lemma 1.1 and Lemma 6.5, ker Q or
{#B0.11} Hess A − h where §§3, 4, 6, and 7 say so, and otherwise the number of steps of a target (K, g); K_R (Proposition 2.11) is a
{#B0.12} constant. κ is the Killing ratio in c, in §6 from Lemma 6.5 on, and in §§7–8 (Theorem 8.1), and otherwise the decay
{#B0.13} constant of RG1, RG2, and CRE (as in exp(−κd_j(X))). p₀ is CRE's exponent in p₀(g) = A₀(log g^{−2})^{p₀}, except in §§7–8, where p₀ ≠ 0 is the external momentum. γ₀ and γ₁ are PRT1's bounds of (1.66)–(1.67) and p.28 in §§5 and 7–9; γ₀ is the coupling of "(0.33) [I]" in §0 and LFR2's constant of the large-field factor exp(−γ₀(1/g²)…) in §2.
{#B0.13-1} In §7, a is PBG's constant in aQ*Q (3.122), not a lattice spacing; R and N(Q′) are PBG's projection and kernel (3.21), N(p) is Lemma 5.2's normaliser, and 𝒩 := 𝐇D.
{#B0.13-2} The full list, with the clashes against the Wilson-loop notes, is §10 of CONSTANTS_AND_CONVENTIONS_WDELTA.md.

{#B0.14} **Theorem 0.1 (Coupling Flow).** There are constants γ > 0, C and δ ∈ (0, 2c ln L), independent of k, of the history
{#B0.15} and of the torus, with the following properties (RG1 (0.31), LFR2 (1.86), CRE (2.4); proofs below).
1. {#B0.16} *Window* (Theorem 8.1).
   {#B0.16-1} For all 0 ≤ m ≤ n, |Σ_{j=m+1}^{n} b_j − 2c(n − m) ln L| ≤ C.
2. {#B0.17} *Matching* (Corollary 8.2, RG1 Theorem 2 for simple G).
   {#B0.17-1} Put γ′ := (γ^{−2} + C)^{−1/2}.
   {#B0.17-2} For every K and every
   {#B0.18} renormalised coupling g ∈ (0, γ′] there is a bare coupling g_0(ε, g), ε = L^{−K}, independent of the torus, whose
   {#B0.19} flow has g_K = g and g_k ∈ (0, γ] for 0 ≤ k ≤ K.
3. {#B0.20} *Logarithmic window.* For 0 ≤ k ≤ K,
   {#B0.21} g^{−2} + (2c ln L − δ)(K − k) − C ≤ g_k^{−2} ≤ g^{−2} + (2c ln L + δ)(K − k) + C.
   {#B0.22} This is RG1 (0.31) with β = 2c − δ/ln L and β′ = 2c + δ/ln L, up to an additive constant.
4. {#B0.23} *Near-monotonicity.* g_k^{−2} ≥ g_l^{−2} − C for k ≤ l. This gives the comparison of thresholds in LFR2 (1.86)
   {#B0.24} (Remark 2.2).
5. {#B0.25} *Remainder.* With CRE's fluctuation cutoff δ_k = g_k(A₁/A₀)p₀(g_k) (CRE p.265, (3.16) p.268),
   {#B0.26} |β_{k+1}(h) − b_{k+1}| ≤ C_rem g_k² for every history h with entries in (0, γ] (Proposition 2.9). So 1/g_{k+1}² = 1/g_k² − b_{k+1} + O(g_k²).

{#B0.27} Proposition 2.4 gives δ = c ln L. Under the conditions of Proposition 2.9, δ = C_remγ² is also admissible, so the rate
{#B0.28} in item 3 tends to 2c ln L as γ → 0 (RG1 (0.31), CRE (2.4)).

{#B0.29} Theorem 0.1 holds under the following conditions.
{#B0.29-1} §9 lists them with the other inputs taken from Bałaban, and
{#B0.30} separately the arguments of this file that extend Bałaban's statements.

{#B0.31} Conditions:
1. {#B0.32} VAR (189), stated in VAR without proof, enters through Lemma 2.5 (sidecar node VAR_189).
2. {#B0.33} RG2's sketch on p.11 for the terms of P^{(k)} other than V enters item 5 (Lemma 2.7, step 2).
3. {#B0.34} The parts of RG1 Theorem 3 with RG2 that §§2.1–2.2 use (the bound RG1 (1.18), and the analyticity of the step terms
   {#B0.35} in (U, J) on RG1's fixed domains), run with CRE's fluctuation cutoffs δ_j = g_j(A₁/A₀)p₀(g_j), enter items 2–5:
   {#B0.36} through (P2) and (C) (the remark after Proposition 2.6) and through Proposition 2.9.
   {#B0.36-1} RG1 Theorem 3 is Bałaban's;
   {#B0.37} the transfer of these parts to the cutoffs δ_j is derived below (*Condition 3*).
4. {#B0.38} PBG's analyticity and decay away from U = 1, and for C^{(k)}(1), whose gauge-fixing term is exponential, for the
   {#B0.39} averaging of RG1 (0.4), enter Propositions 4.2 (and through it 5.3), 7.1, and 2.12 (step 5) as Bałaban applies them
   {#B0.40} to the chain of RG1, RG2, and CRE, whose averaging is RG1 (0.4) or (0.12) (CRE p.243); the passages are listed in
   {#B0.41} §9 (READINGS.md R50).
5. {#B0.42} VAR Theorem 1 rests on the sketched Theorem 8 of REG (p.101) and enters §§5 and 7 through the analyticity of U_k(V).
   {#B0.43} RG1 states VAR's results for its own chain; their use for the averaging RG1 (0.4) is listed in §9 (READINGS.md R47).

{#B0.44} *Scope.* CRE Theorem 1 (CRE p.262) takes the coupling inequalities "(I.0.33)" as its hypothesis: if the sequence {g_k}
{#B0.45} of the renormalisation group equations satisfies them, the densities ρ_k satisfy CRE's inductive assumptions.
{#B0.45-1} RG1 has
{#B0.46} no (0.33); its introduction ends at (0.32), and CRE p.246 cites "(0.33) [I]" for γ₀^{−2} = γ^{−2} + β log ε^{−1}, which
{#B0.47} is RG1's printed (0.31), p.259.
{#B0.47-1} Item 3 has the form of (0.31).
{#B0.47-2} Item 1 is the input from which Lemma 2.1 derives items 2,
{#B0.48} 3, and 4; item 2 provides the flow on which items 3 and 4 hold; and item 4 is the comparison of LFR2 (1.86).
{#B0.48-1} Theorem 0.1
{#B0.49} is stated for the coefficients β_j of the construction named before it.
{#B0.49-1} For semisimple G with an additive action,
{#B0.50} Proposition 10.2 gives the tube-construction form of it (the statements after Condition 5) for each simple factor of
{#B0.51} the product construction on ∏_iρ_i(G), with one bare coupling per factor; RG1's one-coupling construction on G is not covered (§10, *What is OPEN*).

{#B0.52} CRE's flow equation (2.24), p.259, uses its own coefficients β_j(g_{j−1}), which CRE (2.25), p.259, subtracts from its
{#B0.53} step terms (and p.279 for j = k+1).
{#B0.53-1} They differ from ours by the contribution of the R-terms (*Identification* and *The
{#B0.54} R-terms* below).
{#B0.54-1} CRE's coefficient β_{k+1}(g_k) is built from the whole-lattice term E^{(k+1)} (CRE (3.57), p.281;
{#B0.55} p.278), and g_{k+1} enters step k only through the localisation of the new density.
{#B0.55-1} CRE's printed construction is not a
{#B0.56} continuous function of the history because its parameters (the integers R_j, k₁, N₀, and the depth N, the thresholds,
{#B0.57} and the domain radii) jump or move with the couplings (*CRE's Construction as a Function of the History*, §2.2).
{#B0.57-1} The
{#B0.58} *tube construction* for a target (K, g) evaluates all of these parameters at couplings fixed by the target, and it
{#B0.59} places the threshold of the function χ′^{(j)} of LFR1 (1.55) on the unscaled field, |g_jB_j(b)| < δ′_j, where LFR1
{#B0.60} prints the scaled variable (*LFR1 (1.55)*, before Lemma 2.10; Lemma 2.10).
{#B0.60-1} For it:
- {#B0.61} the R-terms shift β_j by at most C_Rg_k^{κ₀−4} relative to RG1's construction run with the tube cutoffs δ_j^T
  {#B0.62} (Proposition 2.11), on the histories of the tube H_k; Propositions 2.4 and 2.9 hold for the latter on H_k
  {#B0.63} (Lemma 2.10, step 7).
  {#B0.63-1} So on H_k the per-step bounds of hypothesis (W) hold with δ′ = δ + C_Rγ^{κ₀−4} in place of
  {#B0.64} δ, and item 5 holds with C_rem + C_Rγ^{κ₀−6} in place of C_rem (*Consequence*, after Proposition 2.11);
- {#B0.65} its β_j is continuous on H_k (Proposition 2.12), and item 2 holds (Proposition 2.13), with γ′ as in item 2; item 3
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
{#B0.73} tube construction (CRE's inductive estimates, LFR1, LFR2, UV3, CMP98, REG, and VAR as CRE uses them), on Conditions
{#B0.74} 1–3 through Propositions 2.4 and 2.9 with δ_j^T, and on the arguments of this file that §9 lists separately: the
{#B0.75} identification of the regular part of β^T with RG1's construction run with δ_j^T, the tube construction with its
{#B0.76} convention for histories that are not flows, the decomposition χ′^{(j)} with the threshold on the unscaled field and
{#B0.77} the four steps that use it, the parameter choices p₀ > (d+5)r + ⌈r⌉ + 2 and q₀, q₁ > p₀,
{#B0.78} Lemma 2.10, Lemma 2.5 on the (2.28) domains, the step with complex multiples of the R-terms, Theorem 8.1 with
{#B0.79} Remark 2.3, and Propositions 2.12 and 2.13.

{#B0.80} *Condition 3 (derived).* The estimates of §§2.1–2.2 use RG1 Theorem 3 with CRE's fluctuation cutoff
{#B0.81} δ_k = g_k(A₁/A₀)p₀(g_k) (CRE p.265, (3.16) p.268) in place of the fixed cutoff ε₁ of RG1 (2.9), p.266, on RG1's fixed
{#B0.82} domains U^c_{k+1}(X, α₀, α₁).
{#B0.82-1} Here p₀(g) = A₀(log g^{−2})^{p₀} (CRE (2.4), p.255) and A₀ ≫ A₁ (CRE p.247).
{#B0.82-2} The cutoff
{#B0.83} applies to the field-scale fluctuation g_kA_k, so its unit-scale form is δ_k/g_k = A₁(log g_k^{−2})^{p₀}
{#B0.84} (`D:\University\Oxford PostDoc\Balaban\READINGS.md` R43, CRE p.267).
{#B0.84-1} CRE's ε_k = g_kp₀(g_k) is the plaquette threshold,
{#B0.85} the analogue of RG1's ε₀ (CRE (3.2), p.265), and it is not the fluctuation cutoff.
{#B0.85-1} The proof of RG1 Theorem 3
{#B0.86} (RG1 §§2–3, RG2 §§1–2) uses the cutoff in three ways only:
- {#B0.87} *Upper bounds on ε₁.* These are RG1 p.265 (the integration domain lies in U_k(ε₀)), p.269 (coefficients O(ε₁)), and
  {#B0.88} p.273 ("ε₁ is so small that"), pp.276 and 280 ("ε₁ sufficiently small"); and RG2 pp.6–9, p.11, p.16 (the radius 1/|τ(Y)| ∝ ε₁), p.18 (the
  {#B0.89} assumption 2E₀ε₁C₁α₄^{−1}α₆^{−1}M^q e^{C₂κ₁}e^{5κ} ≤ 1), p.20, and p.21 (O(1)C₃ε₁ ≤ ½E₀).
  {#B0.89-1} The auxiliary ε₃ = C₁ε₁ of
  {#B0.90} RG2 p.6 is of this kind.
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
- {#B0.101} *Comparisons within one step.* RG1 p.267 bounds B′(b₀(c)) by O(ε₁), with the cutoff of the same step.

{#B0.102} The inductive assumptions RG1 (1.1)–(1.22) do not contain ε₁, and no estimate compares the cutoffs of two steps.
{#B0.102-1} So the
{#B0.103} parts of RG1 Theorem 3 that §§2.1–2.2 use, the bound (1.18) and the analyticity of the step terms in (U, J) on the fixed
{#B0.104} domains, hold with the cutoffs δ_j for γ small.
{#B0.104-1} The gauge invariance and Euclidean covariance of the step terms, which
{#B0.105} the definition of β by RG1 (1.21)–(1.22) and the scalar Π of Lemma 2.5 use, hold for any cutoff that is invariant under
{#B0.106} Ad(G) and the lattice symmetries, as δ_j is.
{#B0.106-1} The clause of RG1 p.263 that E^{(j)} is a C^∞ (or analytic) function of
{#B0.107} g_{j−1} is not transferred to a coupling-dependent cutoff and is not used; continuity in the couplings is
{#B0.108} Proposition 2.6.

{#B0.109} *Identification with CRE's construction.* CRE builds its step terms with the formulas of RG1: "All the applied formulas
{#B0.110} are the same as in Sect. 2 [I], only the symbols represent different operators, determined by the sequence {Ω_j}" (CRE
{#B0.111} p.267).
{#B0.111-1} Of the result it states: "the terms E₀^{(k+1)}(Λ_{k+1}, X, z) of this representation, for X ⊂ Λ_{k+1}, do not
{#B0.112} depend on Λ_{k+1}, and coincide with the corresponding terms arising from the expressions defined on the whole lattice,
{#B0.113} i.e. in the framework of [I]" (CRE p.278). "The framework of [I]" means RG1's whole-lattice formulas, run with CRE's
{#B0.114} inputs (its cutoff δ_k and E_k with R′_k folded in), not RG1's construction itself.
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
{#B0.121} whole lattice", so the terms R″^{(k+1)} and B^{(k+1)} do not enter it.
{#B0.121-1} CRE (3.61), p.282, defines β′_j = Π^{(j)}_{22,11},
{#B0.122} and CRE proves that "it coincides with the definition (I.1.22)": (3.62) uses translation invariance and the identity
{#B0.123} (I.4.15), and (3.63) follows from (2.26) for Λ_j = L^{−j}ℤ^d and the definitions (I.1.20) and (I.5.1) (CRE p.282); CRE (3.64), p.283, gives β′_j = −½Σ_xΠ^{(j)}_{22}(x)x_1² = β_j.
{#B0.123-1} CRE (3.67), p.283, then asserts that
{#B0.124} E^{(j)}(U) − E^{(j)}(1) − β_jA(h_z, U) is irrelevant; since A(h_z, U) is marginal, CRE's β_j is the marginal coefficient
{#B0.125} of CRE's own E^{(j)}.
{#B0.125-1} CRE p.253 points to "(1.41)–(1.43)" of [I] for β₁; RG1 §1 ends at (1.22), and
{#B0.126} the pointer is not used.

{#B0.127} *The R-terms.* Before step k+1, CRE folds R′_k := Σ_{j=1}^{k₁}R^{(j)} into E_k: "It has the same covariance
{#B0.128} property as the expression determined by E_k, and we include it into E_k" (CRE p.271).
{#B0.128-1} So the bracket
{#B0.129} {E_k(U_k(…)) − E_k(U_{k+1})} whose fluctuation integral gives E^{(k+1)} contains R-terms.
{#B0.129-1} The R-terms do not vanish on
{#B0.130} the small-field density: the R-operation (LFR1 (0.3), p.176) integrates out the renormalised regions Z′ and leaves
{#B0.131} their quotients on the density of Z″ as exp Σ_X ℝ(X, V) (LFR1 (0.5)–(0.6), p.176), also for Z″ = ∅.
{#B0.131-1} Hence CRE's
{#B0.132} β_j = β_j^δ + β_j^R, where β_j^δ is the coefficient of RG1's construction run with δ_j (the β_j of §§2.1–2.2) and β_j^R
{#B0.133} is the change of the coefficient caused by the R′-terms.
{#B0.133-1} For the tube construction the same split holds with β_j^{δ,T},
{#B0.134} the coefficient of RG1's construction run with the tube cutoffs δ_j^T, in place of β_j^δ, and Proposition 2.11 bounds
{#B0.135} the R-part: |β^T_{k+1} − β^{δ,T}_{k+1}| ≤ C_R g_k^{κ₀−4} on the histories of the tube, with κ₀ ≥ 7 (CRE (2.31), p.260;
{#B0.136} (2.46), p.263).
{#B0.136-1} Propositions 2.4 and 2.9 hold for β^{δ,T} on the histories of the tube (Lemma 2.10, step 7).
{#B0.136-2} Item 5,
{#B0.137} with C_rem + C_Rγ^{κ₀−6}, and the per-step bounds of (W), with δ′ = δ + C_Rγ^{κ₀−4}, then hold on the histories of the
{#B0.138} tube (Proposition 2.11, *Consequence*); item 2, and items 3 (with δ′) and 4 along the matched flow, hold by
{#B0.139} Propositions 2.12 and 2.13.

{#B0.140} *CRE's Step Terms and β_j (checked against CRE pp.259, 267, 271, 272, 274, 278, 279, and 281–283, corrected transcriptions).*
- {#B0.141} The step is RG1's whole-lattice construction (RG1 §2): "All the applied formulas are the same as in Sect. 2 [I]"
  {#B0.142} (p.267), and the last logarithm of (3.28) "is formally given by the same formula as the term E^{(k+1)} in [I]" (p.272).
- {#B0.143} Its cutoff is CRE's δ_k: the characteristic function of (3.16), p.268, with δ_k = g_kA₁/A₀p₀(g_k) (p.265).
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

{#B0.151} CRE (2.28), p.259, states analyticity of CRE's step terms on smaller domains, α_{0,j} = g_jC_0(log g_j^{−2})^{q_0}, for its
{#B0.152} localised bounds.
{#B0.152-1} CRE's localised pieces (CRE (3.37), (3.41), (3.44)–(3.47)) are not RG2's (RG2 (2.1)–(2.13)).
{#B0.152-2} Without R-terms
{#B0.153} (s = 0 in Proposition 2.11) their sums coincide with RG2's whole-lattice terms up to an additive constant, and CRE's side
{#B0.154} contains the Gaussian term log Z^{(k)}, which RG2's step term excludes (CRE (3.42), p.275); the constant does
{#B0.155} not contribute to β, which is a second derivative in B, and log Z^{(k)} enters β on both sides through
{#B0.156} β_{k+1} = Λ(log Z^{(k)}) + Λ(E^{(k+1)}_fl) (Proposition 2.4, step 1; Remark 2.3, *What β is*). β^δ depends only on the second
{#B0.157} derivatives of the sum at B = 0 (RG1 (1.20)), and §§2.1–2.2 bound it through RG2's own pieces on the fixed domains.
{#B0.157-1} So
{#B0.158} (2.28) is not needed for β^δ.
{#B0.158-1} On the domains of (2.28) alone the Cauchy radius of Lemma 2.5 would be proportional to
{#B0.159} α_{0,j}, and Proposition 2.4 would not give a small bound (`WILSON_CAUCHY_LIPSCHITZ_2026_10_21.md`, *What changes on
{#B0.160} CRE's domains*).
{#B0.160-1} The R-part β^R is bounded on the domains of (2.28), with the tube radii; there only the size
{#B0.161} C_Rg_k^{κ₀−4} is needed, which the factor g_k^{κ₀} supplies (Proposition 2.11, steps 5–6).

{#B0.162} *Proof map.*
- {#B0.163} Theorem 8.1 (item 1) comes from the exact decomposition ℒ_k = F_k − F_0 + 𝒥_k of the k-step Gaussian (§3) and four
  {#B0.164} estimates of its polarisation at a fixed momentum:
  - {#B0.165} the total (Proposition 5.1);
  - {#B0.166} the top-level part (Proposition 7.1);
  - {#B0.167} the bare part (Proposition 6.4, with Proposition 6.3 and the value of c from Lemma 6.5);
  - {#B0.168} the J-terms (Proposition 5.3, with Proposition 4.2, Lemmas 4.1, 4.3, 5.2, and 7.2, and Bałaban's step form
    {#B0.169} RG1 (1.4)–(1.5), pp.266–268).
- {#B0.170} Propositions 2.4 and 2.6 give the history bound (P2) and the continuity (C) of β.
  {#B0.170-1} Remark 2.3 turns item 1 into
  {#B0.171} hypothesis (W) of the flow lemma, and Lemma 2.1 gives items 2–4 (Corollary 8.2).
- {#B0.172} Proposition 2.9 gives item 5.
- {#B0.173} Lemma 2.10 defines the tube construction, CRE's construction with its parameters fixed by the target (K, g) and the
  {#B0.174} threshold of χ′^{(j)} of LFR1 (1.55) placed on the unscaled field, and shows that the estimates of CRE, LFR1, and
  {#B0.175} LFR2 hold for it.
- {#B0.176} Proposition 2.11 bounds the R-part of the β_j of the tube construction; with Propositions 2.4 and 2.9 for the tube
  {#B0.177} cutoffs it gives item 5 and the per-step bounds of (W) on the histories of the tube.
- {#B0.178} Propositions 2.12 and 2.13 give its continuity, item 2, and items 3 and 4 along the matched flow.

## 1. One β for Simple G {#BS1}

{#B1.1} Let G ⊂ U(N) be compact simple, with Lie algebra g.

{#B1.2} **Lemma 1.1.** Every Ad(G)-invariant symmetric bilinear form on g is a multiple of the Killing form K. In particular the
{#B1.3} trace form tr(XY) of the defining representation (normalised trace, tr 1 = 1) is κ^{−1}K, with κ > 0 defined by
{#B1.4} K = κ·tr.

{#B1.5} *Proof.* Ad(G) acts irreducibly on g, over ℝ, and its complexification is irreducible because g is compact simple.
{#B1.5-1} By
{#B1.6} Schur's lemma an invariant form is a multiple of K. ∎
{#B1.7} References (page images read): B. Simon, *Representations of Finite and Compact Groups* (AMS GSM 10, 1996): invariance
{#B1.8} of K, Prop. VIII.2.1(b); K negative definite, Prop. VIII.2.2; uniqueness of the invariant inner product for irreducible
{#B1.9} orthogonal representations, with the Schur remark, Prop. VIII.2.3; Ad irreducible ⇔ g simple, and the definition of
{#B1.10} simple, Thm. VIII.2.4.

{#B1.11} Examples: κ = 2N² for SU(N) ⊂ U(N); κ = C₂(G)/λ in general, where tr = λ·⟨·,·⟩_std on g.

{#B1.12} **Consequences.**
1. {#B1.13} The vacuum polarisation Π^{ab}_{μν} of RG1 (1.20) is Ad-invariant in (a, b), so it is a multiple of the trace form.
   {#B1.14} This is the statement "proportional to δ^{ab}" of RG1 p.264.
2. {#B1.15} The marginal (dimension-4) gauge-invariant local terms are multiples of the Wilson action
   {#B1.16} A(U) = Σ_p [1 − Re tr U(∂p)].
   {#B1.16-1} So there is one coupling and one β, the effective action has the form RG1 (1.3) and
   {#B1.17} (1.6), and the flow is RG1 (0.20).

## 2. The Flow Lemma (Window Form) {#BS2}

{#B2.1} Work with x_k := g_k^{−2}.
{#B2.1-1} The flow RG1 (0.20) reads x_k = x_{k+1} + β_{k+1}(h_k), where h_k := (g_0, …, g_k) is the
{#B2.2} history.
{#B2.2-1} Fix γ > 0, and let 𝓗_γ be the set of histories with all entries in (0, γ].

{#B2.3} **Hypotheses.**
- {#B2.4} **(W)** There are constants 0 < b ≤ b′ and C such that for all 0 ≤ m ≤ n and all histories in 𝓗_γ:
  {#B2.5} b(n−m) − C ≤ Σ_{j=m}^{n−1} β_{j+1} ≤ b′(n−m) + C. This is the window of RG1 (0.31), stated for β.
- {#B2.6} **(C)** Each β_{j+1} is continuous on 𝓗_γ.

{#B2.7} **Lemma 2.1.** Assume (W) and (C).
{#B2.7-1} Let γ′ := (γ^{−2} + C)^{−1/2}.
{#B2.7-2} For every K and every g ∈ (0, γ′] there is a bare
{#B2.8} coupling g_0 whose flow stays in 𝓗_γ up to step K and has g_K = g.
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
   {#B2.16} F(x_0) := x_K.
2. {#B2.17} *The interval.* Let t := g^{−2}.
   {#B2.17-1} Clamped histories lie in 𝓗_γ, so (W) with m = 0, n = K gives
   {#B2.18} F(x_0) ∈ [x_0 − b′K − C, x_0 − bK + C].
   {#B2.18-1} At x_0 = t + bK − C this gives F(x_0) ≤ t, and at x_0 = t + b′K + C it
   {#B2.19} gives F(x_0) ≥ t.
3. {#B2.20} *Intermediate values.* F is continuous on [t + bK − C, t + b′K + C], so it takes the value t at some x_0 there.
4. {#B2.21} *The clamping is inactive.* For this solution, (W) on the window [k, K) gives
   {#B2.22} x_k = t + Σ_{j=k}^{K−1}β_{j+1} ≥ t + b(K−k) − C ≥ γ^{−2}, using t ≥ γ^{−2} + C. So c(x_k) = x_k^{−1/2} at every step,
   {#B2.23} and the clamped flow is the true flow, inside 𝓗_γ.
   {#B2.23-1} Then (i) is (W) on [k, K), and (ii) is (W) on [k, l). ∎

{#B2.24} **Remark 2.2 (What LFR2 (1.86) Needs).** Part (ii) and g_l^{−2} ≥ γ^{−2} give
{#B2.25} log g_k^{−2} ≥ log g_l^{−2} + log(1 − Cγ²) ≥ log g_l^{−2} − 2Cγ² for k ≤ l, once Cγ² ≤ ½.
{#B2.25-1} Hence
{#B2.26} p₀(g_k) ≥ (1+β₀)^{−1} p₀(g_l) once γ is small, which is the comparison used in LFR2 (1.86).

{#B2.27} **Remark 2.3 (From b to β).** Suppose that the zero-coupling coefficients satisfy (W) with constants 2c ln L, 2c ln L and
{#B2.28} C₀ (Theorem 8.1), and that (P2) holds: |β_{j+1}(h) − b_{j+1}| ≤ δ on 𝓗_γ.
{#B2.28-1} Then (W) holds for β with
{#B2.29} b = 2c ln L − δ, b′ = 2c ln L + δ and C = C₀, and b > 0 for δ < 2c ln L. So RG1 Theorem 2 (RG1 p.259) reduces to
{#B2.30} Theorem 8.1 together with (P2) and (C), which §2.1 derives.
{#B2.30-1} The type-checked Lean core is
{#B2.31} `BalabanFormal.coupling_flow_of_stepBound`.

{#B2.32} *What β is.*
- {#B2.33} RG1 defines β_{j+1} by (1.20)–(1.22), p.264, from the step term E^{(j+1)} of RG1 (1.6), which contains the Gaussian
  {#B2.34} term log Z^{(j)} (compare RG1 (1.3), p.260).
- {#B2.35} By RG1 (2.12)–(2.13), p.268, E^{(j+1)}(g_j, U) = log Z^{(j)}(U) + log ∫ χ_j exp[P^{(j)} + {…}] dμ_{C^{(j)}(U)}, and
  {#B2.36} the exponent vanishes at g_j = 0.
- {#B2.37} The earlier couplings enter only through {…}: the previous interaction at the fluctuating configuration, minus its
  {#B2.38} value at the background.
- {#B2.39} At g_j = 0 the exponent vanishes, and the cutoff χ_j = Π_b χ({|g_j(CB)(b)| < ε₁}) of RG1 (2.9) is identically 1.
  {#B2.40} Hence β_{j+1}(0; h) = b_{j+1} exactly.

{#B2.41} Neither (P2) nor (C) is stated in RG1 or RG2.
{#B2.41-1} The smoothness statement after RG1 (1.22) comes without proof.
{#B2.41-2} §2.1
{#B2.42} derives both from RG2's published bounds.

### 2.1 The History Dependence: (P2) and (C) {#BS2.1}

{#B2.1.1} Write E^{(k+1)}_fl for the fluctuation integral RG1 (2.13), so that the RG1 (1.6)-form step term is
{#B2.1.2} [log Z^{(k)}(U) − log Z^{(k)}(1)] + E^{(k+1)}_fl.
{#B2.1.2-1} RG2 represents E^{(k+1)}_fl = Σ_X E^{(k+1)}_fl(X) by an exponentiated
{#B2.1.3} cluster expansion.
{#B2.1.3-1} G is simple, so there is one coupling.

{#B2.1.4} **Proposition 2.4 (P2).** There are constants C_Λ and C₃, independent of k, of the history and of the cutoff ε₁, such
{#B2.1.5} that for every k and every history h ∈ 𝓗_γ (RG2 (2.41); proof below)
  {#B2.1.6} |β_{k+1}(h) − b_{k+1}| ≤ C_Λ C₃ ε₁.

{#B2.1.7} Every condition on ε₁ in RG1–RG2 is an upper bound (step 4, from RG2 pp.7, 18, 20 and 21).
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
   {#B2.1.16} (RG2 p.20), using (1−10δ)½L = 1.
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
4. {#B2.1.23} *Constants.* The conditions on ε₁ are all upper bounds, given κ, κ₁, M, the α's, E₀ and L:
   - {#B2.1.24} RG2 p.7: e^{32κ₁}ε₁ below an absolute constant, and 4B₀C₁e^{16κ₁}ε₁ ≤ ¼α₂;
   - {#B2.1.25} RG2 p.18: 2E₀ε₁C₁α₄^{−1}α₆^{−1}M^q e^{C₂κ₁}e^{5κ} ≤ 1;
   - {#B2.1.26} RG2 p.20: 2(L+2)⁴O(1)ε₂e^{5κ} ≤ 1;
   - {#B2.1.27} RG2 p.21: O(1)C₃ε₁ ≤ ½E₀;
   - {#B2.1.28} RG1 p.273, RG1 p.276 and RG1 p.280: "ε₁ is so small", "ε₁ sufficiently small".

   {#B2.1.29} γ enters only through exp(−γ₂ε₁²/(20γ²)) ≤ ε₂ and γ₂ε₁²/(20γ²) ≥ 4κ (RG2 pp.18–19), conditions on γ chosen last.
   {#B2.1.30} C_Λ depends on κ, δ₀, α₀, α₁, d, M and L, and C₃ on the constants listed.
   {#B2.1.30-1} Neither depends on ε₁. ∎

{#B2.1.31} **Lemma 2.5 (The Polarisation Is Bounded).** Let F = Σ_X F(X), with F(X) analytic on the space U^c_{k+1}(X, α₀, α₁) of
{#B2.1.32} RG1 (1.11)–(1.16) and depending on (U, J) restricted to X, and |F(X)| ≤ A e^{−κd_{k+1}(X)}, as in RG2 (2.41).
{#B2.1.32-1} Put
{#B2.1.33} Π(x) := ∂²F(U_{k+1}(e^{iB}))/∂B_μ(0)∂B_ν(x) at B = 0, and Λ(F) := Σ_x Π(x)x_μx_ν (μ ≠ ν).
{#B2.1.33-1} Then |Λ(F)| ≤ C_Λ A.

{#B2.1.34} *Proof.* Write u(B) for the configuration (U_{k+1}(e^{iB}), J_{k+1}) restricted to X, and ‖·‖ for the norms in which
{#B2.1.35} the conditions of U^c_{k+1}(X, α₀, α₁) are stated.
1. {#B2.1.36} *The background map.* B ↦ U_{k+1}(e^{iB}) is analytic for small complex B. Its functional derivative decays
   {#B2.1.37} exponentially, with rate δ₀ (VAR Prop. 9, p.309, and VAR (190); RG1 p.271).
   {#B2.1.37-1} So ‖∂u/∂B(y)‖ ≤ C e^{−δ₀ dist(y,X)}.
   {#B2.1.38} *Input status.* VAR p.308 derives VAR (190) from VAR (189), and VAR (189) is stated without proof ("We do not
   {#B2.1.39} perform these calculations here").
   {#B2.1.39-1} So this step rests on a published estimate stated without proof (sidecar node
   {#B2.1.40} VAR_189).
   {#B2.1.41} Apply Cauchy's estimate in the single variable B(y′), on a disc of fixed radius, to ∂u/∂B(y).
   {#B2.1.41-1} This gives
   {#B2.1.42} ‖∂²u/∂B(y)∂B(y′)‖ ≤ C e^{−δ₀ dist(y,X)}.
   {#B2.1.42-1} By symmetry the same holds with dist(y′, X), so the bound is
   {#B2.1.43} C e^{−δ₀(dist(y,X) + dist(y′,X))/2}.
2. {#B2.1.44} *Cauchy in the configuration.* Restrict F(X) to the lines u + t v and u + t v + s w.
   {#B2.1.44-1} This gives
   {#B2.1.45} |DF(X)[v]| ≤ A e^{−κd(X)}‖v‖/r and |D²F(X)[v, w]| ≤ 2A e^{−κd(X)}‖v‖‖w‖/r², with r > 0 depending on α₀, α₁ only.
3. {#B2.1.46} *Chain rule.* Π(x) = Σ_X (D²F(X)[∂_{B(0)}u, ∂_{B(x)}u] + DF(X)[∂²_{B(0)B(x)}u]).
   {#B2.1.46-1} By steps 1 and 2, the X-term is
   {#B2.1.47} at most C A r^{−2} e^{−κd(X)} e^{−δ₀(dist(0,X) + dist(x,X))/2}.
4. {#B2.1.48} *Sum.* Σ_x |x|² e^{−δ₀ dist(x,X)/2} ≤ C(1 + diam X + dist(0, X))^{d+2}.
   {#B2.1.48-1} The remaining sum over X of
   {#B2.1.49} e^{−κd(X) − δ₀dist(0,X)/2} times this polynomial converges for κ large, because d(X) ≥ cM^{−4}|X| (RG2 (2.30)). ∎

{#B2.1.50} This is the argument behind RG1 p.264 (existence of the limit RG1 (1.21) and boundedness of β).
{#B2.1.50-1} It is linear in A.

{#B2.1.51} **Proposition 2.6 (C).** For each k, h ↦ β_{k+1}(h) is continuous on (0, γ]^{k+1}.

{#B2.1.52} *Proof.* Induction on k.
{#B2.1.52-1} The claim S_k is: for every X, E^{(k+1)}_fl(X; h) is continuous in h, uniformly for
{#B2.1.53} (U, J) ∈ U^c_{k+1}(X, α₀, α₁).
1. {#B2.1.54} *Where the couplings enter.* In RG2's representation RG2 (2.1)–(2.14), the operators, covariances and measures
   {#B2.1.55} (C^{(k)}, Γ_k, dμ₀ and the s-dependent propagators) depend on (U, J) only.
   {#B2.1.55-1} The couplings enter in two ways:
   - {#B2.1.56} (a) the potentials V_k(Y, B) of RG2 Lemma 2 (p.11);
   - {#B2.1.57} (b) the indicators χ_{k,Y₀} and χ^c_{k,P}, whose threshold is ε₁/g_k (RG2 (2.3)).
2. {#B2.1.58} *(a) is continuous.*
   - {#B2.1.59} P^{(k)} is an explicit analytic function of g_k and g_kCB (RG1 (2.12)).
   - {#B2.1.60} {…} = E_k(U_k(exp i[g_kCB − hD̃(g_kCB)]V)) − E_k(U_k(V)).
     {#B2.1.60-1} E_k is continuous in its couplings by S_j for j < k,
     {#B2.1.61} together with the continuity of β_j.
   - {#B2.1.62} The localisation in RG2 (1.10), (1.23) and (1.38) uses s-integrals over [0, 1] and Cauchy integrals over fixed
     {#B2.1.63} circles.
     {#B2.1.63-1} Both preserve continuity, with bounds uniform in the history.
3. {#B2.1.64} *(b) is continuous almost everywhere.* Fix B with |B(b)| ≠ ε₁/g_k⁰ for all b.
   {#B2.1.64-1} Then the indicators are constant for
   {#B2.1.65} g_k near g_k⁰.
   {#B2.1.65-1} The exceptional set is a finite union of sets {|B(b)| = t}, which are null for the nondegenerate
   {#B2.1.66} Gaussian measures in RG2 (2.14).
4. {#B2.1.67} *Dominated convergence.* The integrand of RG2 (2.14) has the majorant RG2 (2.15)–(2.25).
   {#B2.1.67-1} It is integrable and uniform
   {#B2.1.68} in the history and in (U, J).
   {#B2.1.68-1} So each term RG2 (2.14) is continuous in h, uniformly in (U, J).
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

{#B2.1.77} *The cutoff of CRE.* CRE's fluctuation cutoff at step j is δ_j = g_j(A₁/A₀)p₀(g_j) (CRE p.265, (3.16) p.268), with
{#B2.1.78} p₀(g) = A₀(log g^{−2})^{p₀} (CRE (2.4), p.255) and A₀ ≫ A₁ (CRE p.247); its unit-scale form is
{#B2.1.79} δ_j/g_j = A₁(log g_j^{−2})^{p₀} (`D:\University\Oxford PostDoc\Balaban\READINGS.md` R43).
{#B2.1.79-1} With this cutoff, Proposition 2.4
{#B2.1.80} reads |β_{k+1}(h) − b_{k+1}| ≤ C_ΛC₃δ_k ≤ C_ΛC₃γp₀(γ), which tends to 0 with γ.
{#B2.1.80-1} So no change of the cutoff is needed,
{#B2.1.81} only γ small.
{#B2.1.81-1} The large-deviation condition of RG2 p.19, re-derived at g_k (§0, *Condition 3*), becomes
{#B2.1.82} exp(−γ₂A₁²(log g_k^{−2})^{2p₀}/20) ≤ c_εδ_k, with c_ε as in §0.
{#B2.1.82-1} Its left side is smaller than any power of g_k because
{#B2.1.83} 2p₀ > 1, so it holds for g_k ≤ γ small.
{#B2.1.83-1} This uses RG1's fixed domains with CRE's cutoff, which is condition 3 of §0
{#B2.1.84} (derived there, *Condition 3*).

{#B2.1.85} Proposition 2.6 holds with δ_j.
{#B2.1.85-1} In its step 3 the threshold ε₁/g_k becomes δ_k/g_k = A₁(log g_k^{−2})^{p₀}, which is
{#B2.1.86} continuous in g_k ∈ (0, γ].
{#B2.1.86-1} For B with |B(b)| ≠ δ_k/g_k at g_k = g_k⁰ for all b, the indicators are constant for g_k
{#B2.1.87} near g_k⁰, and the exceptional set is again a finite union of sets {|B(b)| = t}, null for the Gaussian measures of
{#B2.1.88} RG2 (2.14).
{#B2.1.88-1} Steps 1, 2, and 4–6 do not involve the threshold.

### 2.2 The Remainder at Order g_k² {#BS2.2}

{#B2.2.1} This section bounds the remainder R_{k+1}(h) := β_{k+1}(h) − b_{k+1} = Λ(E^{(k+1)}_fl(·; h)) (Proposition 2.4, step 1)
{#B2.2.2} by a multiple of g_k², for RG1's cutoff (2.9) with CRE's cutoff δ_k = g_k(A₁/A₀)p₀(g_k) (CRE p.265).
{#B2.2.2-1} Proposition 2.4
{#B2.2.3} gives O(δ_k) = O(g_kp₀(g_k)).
{#B2.2.3-1} Two facts give the extra power: the step integral is even in a complex coupling that
{#B2.2.4} replaces g_k in the exponent while the cutoff is held fixed, and the cutoff costs only a Gaussian tail.

{#B2.2.5} *Setting.*
- {#B2.2.6} Fix k and the history h, and put p := δ_k/g_k = A₁(log g_k^{−2})^{p₀}.
  {#B2.2.6-1} The cutoff of RG1 (2.9), p.266 runs over the bonds
  {#B2.2.7} b ∉ {b₀(c)}, where hD̃ = 0, and depends on the Gaussian variable only through |B(b)| < p (RG2 (2.3), p.12).
- {#B2.2.8} For a threshold q and complex z, χ_q := ∏_b χ({|B(b)| < q}) over the same bonds.
  {#B2.2.8-1} W(z, B) is the exponent
  {#B2.2.9} P^{(k)} + {…} of RG1 (2.12) with g_k replaced by z wherever it occurs in the exponent.
  {#B2.2.9-1} The cutoff is not changed.
- {#B2.2.10} E(z; q) := log ∫ χ_q exp W(z, B) dμ_{C^{(k)}}(B).
  {#B2.2.10-1} Then E^{(k+1)}_fl = E(g_k; p), by RG1 (2.13).
- {#B2.2.11} *Parity.* In RG1 (2.12), p.268, every term of the exponent is a function of g_k times a linear image of B (g_kCB,
  {#B2.2.12} or g_kB in G₃), or g_k^{−2} times such a function of order at least three (V and G₃ are of order at least three,
  {#B2.2.13} and D̃ starts at order two, RG1 p.267).
  {#B2.2.13-1} So W(−z, B) = W(z, −B).
  {#B2.2.13-2} The Gaussian measure is centred and χ_q is even,
  {#B2.2.14} so E(−z; q) = E(z; q) as functions of (U, J).

{#B2.2.15} **Lemma 2.7 (Complex Coupling).** Let ε* satisfy every condition on ε₁ listed in Proposition 2.4, step 4, and let
{#B2.2.16} P be the constant fixed in Lemma 2.8.
{#B2.2.16-1} Let q ≥ P and |z|q < ε*.
{#B2.2.16-2} Then RG2's expansion (2.1)–(2.13) applies to
{#B2.2.17} E(z; q) = Σ_X E(X; z, q).
{#B2.2.17-1} Each E(X; z, q) is analytic in z on |z| < ε*/q and in (U, J) on U^c_{k+1}(X, α₀, α₁).
{#B2.2.18} It satisfies RG2 (2.41) with ε* in place of ε₁: |E(X; z, q)| ≤ O(1)C₃ε* exp(−κd_{k+1}(X)).
{#B2.2.18-1} At z = g_k and q = p,
{#B2.2.19} E(X; z, q) is RG2's E^{(k+1)}(X).

{#B2.2.20} *Proof.*
1. {#B2.2.21} *The bracket.* {…} depends on (z, B) only through zCB (RG1 (2.12)).
   {#B2.2.21-1} With B̃ := (z/g_k)B it is the bracket at the
   {#B2.2.22} real coupling g_k and the complex field B̃.
   {#B2.2.22-1} RG2 Lemma 1 holds on the complex polydisc |B̃| < ε*/g_k (READINGS R40,
   {#B2.2.23} with ε* for ε₁).
   {#B2.2.23-1} So V′_k(Y, (z/g_k)B) localises the bracket.
   {#B2.2.23-2} It is analytic in z and satisfies RG2 (1.36) with ε*,
   {#B2.2.24} for |z||B| < ε* on Y.
2. {#B2.2.25} *The action terms.*
   - {#B2.2.26} RG2 builds the localisation of P^{(k)} from the pieces (1.38).
     {#B2.2.26-1} These are functions of the unscaled fluctuation B′
     {#B2.2.27} alone, analytic for e^{16κ₁}|B′| ≤ a₁ and bounded by RG2 (1.39), p.10. "It can be done in the same way for all
     {#B2.2.28} terms in P^{(k)}" (RG2 p.11).
   - {#B2.2.29} The factor g_k^{−2} is removed by the second-order expansion RG2 (1.40) in B′, whose coefficients are bounded
     {#B2.2.30} by a multiple of |B′|.
   - {#B2.2.31} The coupling enters only through B′ = g_kCB − hD̃(g_kCB) (RG2 (1.19), p.6).
     {#B2.2.31-1} The bound (1.20) and the circle
     {#B2.2.32} (1.22) are stated through g_k|B| (RG2 pp.6–7).
   - {#B2.2.33} With z in place of g_k, the pieces are the same analytic functions at B′ = zCB − hD̃(zCB).
     {#B2.2.33-1} The prefactor
     {#B2.2.34} cancels by z^{−2}⟨Q̂B′, B′⟩ = ⟨Q̂B′/z, B′/z⟩.
     {#B2.2.34-1} The map B′/z = CB − z^{−1}hD̃(zCB) is analytic in z, also at z = 0.
   - {#B2.2.35} RG2 (1.20), with |z| in place of g_k, gives |B′| ≤ C₁|z||B| < C₁ε* and |B′/z| ≤ C₁|B|.
     {#B2.2.35-1} So RG2 (1.43) and (1.36)
     {#B2.2.36} hold with ε* in place of ε₁ on |z||B| < ε*, and each V_k(Y; z, B) is analytic in z there.

   {#B2.2.37} This step is our transfer of RG2's construction to complex coupling.
   {#B2.2.37-1} RG2 states Lemmas 1–2 for real g_k only.
   {#B2.2.38} For the terms of P^{(k)} other than V, the transfer rests on RG2's sketch "It can be done in the same way for all
   {#B2.2.39} terms in P^{(k)}" (RG2 p.11), used as Bałaban states it.
3. {#B2.2.40} *The expansion.* RG2 section 2 (pp.12–21) uses the potentials only in two ways:
   - {#B2.2.41} through RG2 (1.42), (1.43), (1.36) and the inequality (1.28), in (2.18)–(2.20) on p.16;
   - {#B2.2.42} through the analyticity of V_k in (U, J) on U^c_{k+1}(Y, (1 + β)α₀, (1 + β)α₁, α₀) (RG2 (1.34)), used on p.15.
     {#B2.2.43} z does not enter the (U, J)-dependence, so this holds at every z.

   {#B2.2.44} It uses the cutoff only through the factor χ_{k,Y₀}χ^c_{k,P}, with values in [0, 1], and the tail bound RG2 (2.22).
   - {#B2.2.45} The potentials are evaluated only on the support of χ_{k,Y₀} (RG2 (2.3)).
     {#B2.2.45-1} There |z||B| < |z|q < ε*.
   - {#B2.2.46} The threshold enters RG2's conditions only as ε₁/g_k in (2.22), (2.31), (2.33) and (2.34).
     {#B2.2.46-1} With q in its place,
     {#B2.2.47} these are lower bounds on q, and they hold for q ≥ P.

   {#B2.2.48} So RG2 (2.1)–(2.41) hold with ε* in place of ε₁ and q in place of ε₁/g_k.
4. {#B2.2.49} *Analyticity.* Each term RG2 (2.14) is an integral of a function analytic in z.
   {#B2.2.49-1} It is dominated by RG2 (2.26),
   {#B2.2.50} uniformly on compact subsets of |z| < ε*/q, so it is analytic in z.
   {#B2.2.50-1} The sums (2.35)–(2.41) converge uniformly
   {#B2.2.51} there. ∎

{#B2.2.52} **Lemma 2.8 (Threshold Differences).** There is a constant P, depending on ε*, κ, M, γ₂ and the constants of RG2,
{#B2.2.53} with the following property. ε* is fixed first: the condition exp(−γ₂q²/20) ≤ ε₂ of RG2 (2.33) involves ε₂, which is
{#B2.2.54} proportional to ε* here.
{#B2.2.54-1} Let P ≤ q′ < q″ ≤ 2q′ and |z|q″ < ε*.
{#B2.2.54-2} Then E(z; q″) − E(z; q′) = Σ_X Δ(X; z), where each
{#B2.2.55} Δ(X; z) is analytic in z and in (U, J) on U^c_{k+1}(X, α₀, α₁).
{#B2.2.55-1} With constants C₄ and C₅ that do not depend on k,
{#B2.2.56} the history, q′, q″ or z, the following bounds hold.
- {#B2.2.57} RG2 (2.41) has the analogue |Δ(X; z)| ≤ C₄ exp(−γ₂q′²/4) exp(−κd_{k+1}(X)).
- {#B2.2.58} At z = 0, |E(X; 0, q)| ≤ C₅ exp(−γ₂q²/20) exp(−κd_{k+1}(X)) for q ≥ P.

{#B2.2.59} *Proof.*
1. {#B2.2.60} *Same index sets.* The families D, the sets P ⊂ Y₀^{c*}, and the domains Z₀ and Z of RG2 (2.1)–(2.13) do not depend
   {#B2.2.61} on the threshold (RG2 (2.1)–(2.3)).
   {#B2.2.61-1} So, term by term in (2.14), the activities at q″ and q′ differ only in the
   {#B2.2.62} factor χ_{k,Y₀}χ^c_{k,P}.
   {#B2.2.62-1} Write χ″ and χ′ for this factor at the two thresholds.
2. {#B2.2.63} *The difference of the cutoffs.* χ″ − χ′ = (χ″_{Y₀} − χ′_{Y₀})χ″^c_P + χ′_{Y₀}(χ″^c_P − χ′^c_P).
   - {#B2.2.64} The first term is nonzero only if some b ∈ Y₀ has |B(b)| ≥ q′.
   - {#B2.2.65} The second term is nonzero only if P ≠ ∅ and every b ∈ P has |B(b)| ≥ q′.
   - {#B2.2.66} Bounding each indicator as in RG2 (2.22), and using that Y₀ and P are disjoint bonds of Z₀, gives
     {#B2.2.67} |χ″ − χ′| ≤ (|Y₀| + 1) exp(−γ₂q′²/4) exp(−¼γ₂q′²|P| + ½γ₂‖Z₀B‖²).
3. {#B2.2.68} *RG2's chain.*
   - {#B2.2.69} The factor exp(½γ₂‖Z₀B‖²) is absorbed into the Gaussian as in RG2 (2.23), whose room α₅ contains γ₂ and
     {#B2.2.70} multiplies ‖Z₀B‖².
   - {#B2.2.71} The factor exp(−¼γ₂q′²|P|) runs the sums RG2 (2.31)–(2.34) with γ₂/2 in place of γ₂.
     {#B2.2.71-1} P is taken so large that
     {#B2.2.72} they hold.
   - {#B2.2.73} Over the components Y_i of Y₀, RG2 (2.30) gives |Y₀| + 1 ≤ (1 + 24M⁴/(δκ)) exp(δκ Σ_i d_k(Y_i)), and the
     {#B2.2.74} exponential is absorbed by the decay in (2.28).
   - {#B2.2.75} The rest of the chain RG2 (2.26)–(2.38) is unchanged.
     {#B2.2.75-1} It bounds H″(Z) − H′(Z) by RG2 (2.38) times C exp(−γ₂q′²/4).
4. {#B2.2.76} *The polymer series.* In RG2 (2.13), ∏H″(Z_i) − ∏H′(Z_i) is a sum of n products, each with one factor H″ − H′.
   - {#B2.2.77} The bound RG2 (2.39)–(2.41) gives the claim, with one more δ in the exponent.
   - {#B2.2.78} Taking δ = (1 − 2L^{−1})/12 in place of RG2's (1 − 2L^{−1})/10 makes (1 − 12δ)½L = 1.
   - {#B2.2.79} In RG2 section 2, δ enters only the estimates (for instance, the radii (2.18) of Cauchy formulas).
     {#B2.2.79-1} So no activity
     {#B2.2.80} changes.
5. {#B2.2.81} *z = 0.* Every localized potential vanishes at z = 0.
   {#B2.2.81-1} In Lemma 1, H_k(s, 0) = 0 (RG2 (1.18), p.6), so the
   {#B2.2.82} integrand of RG2 (1.23) does not depend on t_□, and the Cauchy integral in t_□ is 0.
   {#B2.2.82-1} In the action terms the
   {#B2.2.83} coefficients of RG2 (1.40) are O(|B′|), and B′ = 0 at z = 0.
   {#B2.2.83-1} So V_k(Y; 0, B) = 0 for every Y, and only D = ∅
   {#B2.2.84} contributes to RG2 (2.1).
   {#B2.2.84-1} Then Y₀ = ∅, and every nonzero term has P ≠ ∅.
   {#B2.2.85} RG2 (2.33) gives the factor exp(−(1/20)γ₂q²) per component in place of max{ε₂, …}, and RG2 (2.37)–(2.41) give
   {#B2.2.86} the bound with C₅. ∎

{#B2.2.87} **Proposition 2.9 (The Remainder at Order g_k²).** Take RG1's cutoff (2.9) with CRE's cutoff δ_k = g_k(A₁/A₀)p₀(g_k)
{#B2.2.88} (CRE p.265, (3.16) p.268).
{#B2.2.88-1} There are constants C_rem and γ > 0, independent of k and of the history, such that for every k
{#B2.2.89} and every history h ∈ 𝓗_γ

  {#B2.2.90} |β_{k+1}(h) − b_{k+1}| ≤ C_rem g_k²  (RG1 (2.13), CRE p.265; proof below).

{#B2.2.91} *Proof.*
1. {#B2.2.92} *The function.* Put R(z; q) := Λ(E(·; z, q)) for |z|q < ε*.
   - {#B2.2.93} Λ is a Cauchy integral followed by a sum dominated as in Lemma 2.5.
     {#B2.2.93-1} So, by Lemma 2.7, R(·; q) is analytic on
     {#B2.2.94} this disc, and |R(z; q)| ≤ C_Λ O(1)C₃ε* =: M₀ (RG2 (2.41)).
   - {#B2.2.95} R(·; q) is even, because each activity E(X; z, q) is even in z and Λ is linear.
     - {#B2.2.96} Each piece of V_k(Y; z, B) sees z only through zCB and z^{−2} (Lemma 2.7, steps 1–2).
       {#B2.2.96-1} Hence
       {#B2.2.97} V_k(Y; −z, −B) = V_k(Y; z, B).
     - {#B2.2.98} In RG2 (2.14), the change of variables (B, X) ↦ (−B, −X) leaves the centred measures, the coupling
       {#B2.2.99} exp(−⟨B, Γ_kX⟩), and χ_{k,Y₀}χ^c_{k,P} invariant.
     - {#B2.2.100} So each H(Z) is even in z, and by RG2 (2.13) so is each E(X; z, q).
   - {#B2.2.101} Proposition 2.4, step 1, gives β_{k+1}(h) − b_{k+1} = R(g_k; p).
2. {#B2.2.102} *Even functions.* Let f be even and analytic on |z| < r, with |f| ≤ M there.
   {#B2.2.102-1} Then φ(z) := (f(z) − f(0))/z² is
   {#B2.2.103} analytic.
   {#B2.2.103-1} By the maximum principle on the circles |z| = ρ < r, |f(g) − f(0)| ≤ 2Mg²/r² for 0 ≤ g < r.
   {#B2.2.103-2} Here f is
   {#B2.2.104} R(·; q), and M is M₀ from RG2 (2.41) (step 4), or a bound from Lemma 2.8 (step 5).
3. {#B2.2.105} *Telescoping.* Let J be the least integer with 2^JP ≥ p. Put p_j := 2^jP for 0 ≤ j < J and p_J := p, and
   {#B2.2.106} D_j(z) := R(z; p_{j+1}) − R(z; p_j).
   {#B2.2.106-1} Then
   {#B2.2.107} R(g_k; p) = R(0; p) + [R(g_k; P) − R(0; P)] + Σ_{j<J} [D_j(g_k) − D_j(0)].
4. {#B2.2.108} *The main term.* R(·; P) is even and analytic on |z| < ε*/P, and bounded by M₀ there (Lemma 2.7, RG2 (2.41)).
   {#B2.2.109} Step 2 gives |R(g_k; P) − R(0; P)| ≤ 2M₀P²g_k²/ε*².
5. {#B2.2.110} *The threshold terms.*
   - {#B2.2.111} D_j is even and analytic on |z| < ε*/p_{j+1}, and |D_j| ≤ C_ΛC₄ exp(−γ₂p_j²/4) there (Lemmas 2.5 and 2.8, from
     {#B2.2.112} RG2 (2.26)–(2.41)).
   - {#B2.2.113} g_k lies in this disc, because g_kp_{j+1} ≤ g_kp = δ_k < ε*.
   - {#B2.2.114} Step 2 and p_{j+1} ≤ 2p_j give |D_j(g_k) − D_j(0)| ≤ 8C_ΛC₄ p_j² exp(−γ₂p_j²/4) g_k²/ε*².
   - {#B2.2.115} Summed over j, the bound is 8C_ΛC₄Sg_k²/ε*², with S := Σ_{j≥0} 4^jP² exp(−γ₂4^jP²/4), which is finite.
6. {#B2.2.116} *The cutoff term.*
   - {#B2.2.117} R(0; p) = Λ(log μ_{C^{(k)}}(χ_p)).
     {#B2.2.117-1} Lemmas 2.5 and 2.8 (z = 0) give |R(0; p)| ≤ C_ΛC₅ exp(−γ₂p²/20).
   - {#B2.2.118} p = A₁(log g_k^{−2})^{p₀} (CRE p.265), with p₀ a positive integer (CRE p.244).
     {#B2.2.118-1} So (γ₂/20)p² ≥ log g_k^{−2} once
     {#B2.2.119} (γ₂/20)A₁²(log g_k^{−2})^{2p₀−1} ≥ 1, which holds for g_k ≤ γ small.
   - {#B2.2.120} Then |R(0; p)| ≤ C_ΛC₅g_k².
7. {#B2.2.121} *Constants.*
   - {#B2.2.122} C_rem := 2M₀P²/ε*² + 8C_ΛC₄S/ε*² + C_ΛC₅.
   - {#B2.2.123} The constants are fixed in this order: ε*, then P, then γ. γ is taken so small that, for g ≤ γ,
     {#B2.2.124} A₁(log g^{−2})^{p₀} ≥ P, gA₁(log g^{−2})^{p₀} < ε*, and step 6 holds (CRE pp.244, 246, 265).
   - {#B2.2.125} None of these depends on k or on the history. ∎

{#B2.2.126} In the coupling flow RG1 (2.15) this reads 1/g_{k+1}² = 1/g_k² − b_{k+1} + O(g_k²), uniformly in the history.

{#B2.2.127} *Inputs.*
- {#B2.2.128} Lemma 2.5 rests on VAR (189), as in Proposition 2.4 (sidecar node VAR_189).
- {#B2.2.129} RG2 Lemmas 1–2 and section 2, RG1 (2.12), and CRE pp.244–246 and (2.4), as cited.
- {#B2.2.130} Bałaban does not print the parity, the complex-coupling transfer (Lemma 2.7), the threshold differences
  {#B2.2.131} (Lemma 2.8), or the telescoping.
  {#B2.2.131-1} Their proofs are in this section, and they hold under the following conditions.

  {#B2.2.132} Conditions:
  1. {#B2.2.133} VAR (189), through Lemma 2.5 (sidecar node VAR_189).
  2. {#B2.2.134} RG2's sketch on p.11 for the terms of P^{(k)} other than V (Lemma 2.7, step 2).
  3. {#B2.2.135} The bound RG1 (1.18) and the analyticity of the step terms in (U, J) on RG1's fixed domains, from RG1 Theorem 3
     {#B2.2.136} run with CRE's cutoffs δ_j = g_j(A₁/A₀)p₀(g_j) (the remark after Proposition 2.6; the transfer is derived in §0,
     {#B2.2.137} *Condition 3*).

{#B2.2.138} *CRE's Construction as a Function of the History.* CRE's coefficient β_{k+1}(g_k) (CRE p.279) is built from the
{#B2.2.139} whole-lattice term E^{(k+1)} ((3.57), p.281; p.278: the localised terms "do not depend on Λ_{k+1}"), which uses the
{#B2.2.140} cutoff δ_k and the input R′_k.
{#B2.2.140-1} The next coupling g_{k+1} enters step k only through the localisation and the
{#B2.2.141} analyticity statements of the new density (the threshold ε_{k+1} of CRE (3.2), p.265, (3.8), p.266, and p.268; the
{#B2.2.142} scale R_{k+1} of p.264; and the domains (2.28) at scale k+1).
{#B2.2.142-1} What breaks the continuity in the history is that the
{#B2.2.143} parameters jump or move with the couplings:
- {#B2.2.144} R_j (CRE (2.5)), k₁ (CRE p.270), N₀ (LFR1 p.179), and the depth N of the R-operation are integers that jump with the
  {#B2.2.145} couplings.
  {#B2.2.145-1} N is "to the positive power of log g_k^{−2}" (LFR1 p.198), N ≥ (ν/log L) log log g_k^{−2} (LFR2 p.363),
  {#B2.2.146} and LFR2 p.384 takes N = R_j (`D:\University\Oxford PostDoc\Balaban\READINGS.md` R4).
  {#B2.2.146-1} Since R′_k = Σ_{j≤k₁}R^{(j)}
  {#B2.2.147} (CRE p.271), a jump of k₁ moves a whole R-term between R′ and R″, and β_{k+1} jumps with it.
- {#B2.2.148} The thresholds ε_j, δ_j, and δ′_j, the threshold 2ε_kη² of LFR1 (1.75), and the supports of the bump functions of the
  {#B2.2.149} changes of variables CRE (1.22) (pp.252, 269) move with the couplings, so the characteristic functions under the
  {#B2.2.150} integrals depend on the history.

{#B2.2.151} The construction below evaluates every such parameter at a value fixed by the target (K, g).
{#B2.2.151-1} Then no characteristic
{#B2.2.152} function depends on the history, and the couplings enter only through the densities.

{#B2.2.153} *The Class of Tubes.* A tube is given by constants 0 < b ≤ b′ and C ≥ 0 and a target (K, g), with
  {#B2.2.154} c ln L ≤ b ≤ b′ ≤ min((3/2)b, 3c ln L),  C ≤ C₀,  t := g^{−2} ≥ max(γ^{−2} + C, 8C),
{#B2.2.155} with C₀ the constant of Theorem 8.1.
{#B2.2.155-1} Put ρ_γ := max(b′/b, (t + C)/(t − 2C)); on the class ρ_γ ≤ 3/2.
{#B2.2.155-2} Put ρ̄ := 15/8,
{#B2.2.156} the factor of the action comparison on the class (*Histories that are not flows*).
{#B2.2.157} For 0 ≤ k ≤ K put
  {#B2.2.158} ℓ_k := t + b(K−k) − C,  u_k := t + b′(K−k) + C,  T_k := [ℓ_k, u_k],  ĝ_k := u_k^{−1/2},
{#B2.2.159} and let H_k be the set of (x_0, …, x_k) with x_j ∈ T_j for j ≤ k and b(n−m) − C ≤ x_m − x_n ≤ b′(n−m) + C for
{#B2.2.160} 0 ≤ m < n ≤ k.
{#B2.2.160-1} H_k is closed and convex.
{#B2.2.160-2} It contains x_j := t + ½(b + b′)(K−j), and the sequence (u_j) lies in H_K.
{#B2.2.161} The constants of Lemma 2.10 and of Propositions 2.4, 2.9, and 2.11 below (C_Λ, C₃, C_rem, C′, C_Σ, K_R, and C_R) are uniform
{#B2.2.162} over the class, and so is the smallness of γ required in Lemma 2.10, because they depend on the tube only through
{#B2.2.163} the bounds c ln L ≤ b ≤ b′ ≤ 3c ln L, C ≤ C₀, ρ_γ ≤ 3/2, and the action comparison with ρ̄ (for instance, Lemma 2.10, step 2, needs
{#B2.2.164} γ²(b′ + C) ≤ (1+β₀)² − 1, and step 3 needs (1 + log(1 + b′)/log γ^{−2})^r ≤ 1 + 1/L).

{#B2.2.165} *The Tube of a Target.* Put δ′ := δ + C_Rγ^{κ₀−4}, with δ = C_ΛC₃γp₀(γ) the bound of Proposition 2.4 and C_R that of
{#B2.2.166} Proposition 2.11, both with the constants of the class.
{#B2.2.166-1} For γ small, δ′ ≤ (2/5)c ln L. Put b := 2c ln L − δ′,
{#B2.2.167} b′ := 2c ln L + δ′, and C := C₀ (Theorem 8.1).
{#B2.2.167-1} Then c ln L ≤ b ≤ b′ ≤ 3c ln L and b′/b ≤ 3/2, and
{#B2.2.168} t ≥ γ′^{−2} = γ^{−2} + C ≥ 8C for γ small, so the tube of the target (K, g) lies in the class.
{#B2.2.168-1} For it ρ_γ → 1 as
{#B2.2.169} γ → 0.
{#B2.2.169-1} These constants do not depend on K or g, and the
{#B2.2.170} definition is not circular, because C_R and δ are fixed on the class before b and b′ are.

{#B2.2.171} The tube construction for (K, g) is CRE's construction in which every parameter that CRE, LFR1, and LFR2 define from
{#B2.2.172} a coupling g_j is defined from ĝ_j instead:
- {#B2.2.173} R_j^T is the smallest power of L with R_j^T ≥ (log ĝ_j^{−2})^r, the depth is N_k^T := R_k^T, and k₁ and N₀ are
  {#B2.2.174} defined from R^T by the formulas of CRE p.270 and LFR1 p.179;
- {#B2.2.175} ε_j^T := ĝ_jp₀(ĝ_j), δ_j^T := (A₁/A₀)ε_j^T, the threshold of LFR1 (1.75) is 2ε_k^Tη², and the domains of
  {#B2.2.176} CRE (2.28) are α^T_{0,j} := ĝ_jC^α_0(log ĝ_j^{−2})^{q₀} and α^T_{1,j} := ĝ_jC^α_1(log ĝ_j^{−2})^{q₁}, where C^α_0
  {#B2.2.177} and C^α_1 are the constants that CRE (2.28) prints as C₀ and C₁ (renamed here, since C₀ is the constant of
  {#B2.2.178} Theorem 8.1 and C₁ the constant of RG2 Lemma 1);
- {#B2.2.179} every other threshold, every factor p₀, p₁, q₀, or q₁ in a threshold, a scale, or a domain, and the supports of the
  {#B2.2.180} bump functions of CRE (1.22) are taken at ĝ_j.

{#B2.2.181} The factors g_j^{±1} that convert between scaled and unscaled fields stay the couplings of the history.
{#B2.2.181-1} So the
{#B2.2.182} thresholds act on unscaled fields (the plaquette variables U(∂p) and the fluctuation fields g_kA_k) with values fixed
{#B2.2.183} by the target.
- {#B2.2.184} *LFR1 (1.55).* LFR1 (1.55), p.188, prints χ′^{(j)} = χ({|B_j(b)| < δ′_j}) for the scaled variable B_j, with
  {#B2.2.185} δ′_j = g_jA₁p₁(g_j) (LFR1 p.183).
  {#B2.2.185-1} LFR2 prints no large-field factor for the components that LFR1 p.188 excludes
  {#B2.2.186} from Z with 1 − χ′^{(j)}: the factors of the preparatory steps on LFR2 pp.380–383 are those of 1 − χ_j^{(n)}, of
  {#B2.2.187} 1 − χ′_m of LFR1 (1.27), of the second function of the decomposition LFR1 (1.28) ("yields the same final factor",
  {#B2.2.188} p.381), of 1 − χ_{j,Λ}, and of 1 − χ′ of LFR1 (1.82).
  {#B2.2.188-1} The construction here takes
  {#B2.2.189} χ′^{(j)} := χ({|g_jB_j(b)| < δ′_j}), with the threshold on the unscaled field; the identity
  {#B2.2.190} 1 = χ′^{(j)} + (1 − χ′^{(j)}) holds for every threshold.
  {#B2.2.190-1} The same choice is made for CRE's fluctuation threshold:
  {#B2.2.191} CRE (3.16), p.268, prints χ({sup|A_k(b)| < δ_k}) after the scaling A′_k = g_kA_k (CRE p.267), and its threshold is
  {#B2.2.192} read at field scale (READINGS.md R43), the value that LFR2 p.380's factor exp(−γ₀(1/g_j²)δ_j²(LM₂R_j)^{−d}|R_j|)
  {#B2.2.193} for it carries.
  {#B2.2.193-1} LFR1 (1.9), p.178, prints the fluctuation threshold as |A_j(b)| < g_j^{−1}δ_j, and LFR1 (1.82),
  {#B2.2.194} p.196, prints δ′_k on the unscaled field B′, V′ = exp iB′.
  {#B2.2.194-1} Four steps use the threshold.
  - {#B2.2.195} *The expansion.* Since δ_j = g_j(A₁/A₀)p₀(g_j) (CRE p.265), δ′_j/δ_j = A₀p₁(g_j)/p₀(g_j) < 1 for g small, as
    {#B2.2.196} p₁ < p₀.
    {#B2.2.196-1} The bound |B′_j| < 6δ′_j, B′_j = g_jB_j, holds on the whole integration domain by (1.54), p.187, and LFR1
    {#B2.2.197} p.187 expands the action on it, so the expansion holds on both kinds of components.
    {#B2.2.197-1} The small-field components,
    {#B2.2.198} |g_jB_j| < δ′_j, lie in the small-field domain |g_jA| < δ_j of CRE (3.25), p.270, read as in R43.
  - {#B2.2.199} *The removal of χ′_j.* The small-field integral of LFR1 p.188 carries χ′^{(j)} but not χ′_j of (1.27),
    {#B2.2.200} |V_j(V^{(j)}_Z)^{−1} − 1| < 2δ′_j. On the small-field components χ′_j = 1: V_j(V^{(j)}_Z)^{−1} =
    {#B2.2.201} V′_jV^{(j)}(V^{(j)}_Z)^{−1} with V′_j = exp ig_jB_j by (1.53), and V^{(j)}(V^{(j)}_Z)^{−1} = exp i𝐇^{(j)}_Z by (1.58),
    {#B2.2.202} with 𝐇^{(j)}_Z bounded by O(1)exp(−R_j)ε_j, "smaller than any positive power of g_j" (p.188).
    {#B2.2.202-1} So
    {#B2.2.203} |V_j(V^{(j)}_Z)^{−1} − 1| ≤ |g_jB_j| + O(1)exp(−R_j)ε_j < δ′_j + O(1)exp(−R_j)ε_j < 2δ′_j for g small.
  - {#B2.2.204} *The Gaussian tails.* LFR1 p.189 treats the small-field integral (1.60) as "of the same type as the integral
    {#B2.2.205} studied in Sect. 3 [III]", and that analysis needs the lower bounds on the unit-scale cutoff of §0, *Condition 3*.
    {#B2.2.206} Here the unit-scale cutoff is δ′_j/g_j = A₁(log g_j^{−2})^{p₁}.
    {#B2.2.206-1} The condition of RG2 p.19 becomes
    {#B2.2.207} exp(−γ₂A₁²(log g_j^{−2})^{2p₁}/20) ≤ c_εδ′_j, which holds for g_j ≤ γ small because 2p₁ > 1: LFR2 p.383 assumes
    {#B2.2.208} 2p₁ − (d+5)r₀ > p₀, and p₀ > 2 (Lemma 2.10, step 4), so 2p₁ > p₀ > 2.
    {#B2.2.208-1} The condition of RG2 p.18 holds once
    {#B2.2.209} γ₂A₁²(log γ^{−2})^{2p₁} ≥ 80κ, and the other lower bounds of *Condition 3* hold because δ′_j/g_j ≥ A₁(log γ^{−2})^{p₁}
    {#B2.2.210} tends to ∞ as γ → 0.
  - {#B2.2.211} *The large-field factor.* On the large-field components some bond b has |g_jB_j(b)| ≥ δ′_j, that is
    {#B2.2.212} |B_j(b)| ≥ g_j^{−1}δ′_j = A₁p₁(g_j). The B_j-integral of LFR1 p.188 has the quadratic form ⟨B_j, C^*Δ^{(j)}CB_j⟩ of
    {#B2.2.213} CRE's fluctuation integrals.
    {#B2.2.213-1} For the threshold of CRE (3.16), LFR2 p.380 obtains the factor above "by the same
    {#B2.2.214} positivity bound for the quadratic form", a lower bound of the kind of PRT2 (2.157), p.250,
    {#B2.2.215} ⟨B′, C^*Δ_kCB′⟩ ≥ γ′₀‖B′‖² with γ′₀ = (γ₀/12d²)L^{−d−1}.
    {#B2.2.215-1} The same bound, with δ′_j in place of δ_j and the single
    {#B2.2.216} bond b in place of the cubes of R_j, gives the factor exp(−c(1/g_j²)δ′_j²) = exp(−cA₁²p₁²(g_j)) for each such
    {#B2.2.217} component, with c > 0 depending on d and L only.
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
  {#B2.2.227} 1/g²_{j−1}(x) = 1/g_j²(x) + β_j(g_{j−1})φ_j(x), with g_j²(x) = g_j² on the last domain; this holds along a flow.
  {#B2.2.227-1} For an
  {#B2.2.228} arbitrary history h = (g_0, …, g_k) the tube construction uses the same relation counted from the top:
    {#B2.2.229} 1/g_k²(x) := 1/g_k² + Σ_{j=1}^{k} β^T_j(h_{j−1})(1 − φ_j(x)),
  {#B2.2.230} which agrees with (2.24) along a flow (put d_j(x) := 1/g_j²(x) − 1/g_j²; (2.24) and the flow give
  {#B2.2.231} d_{j−1} = d_j − β_j(1 − φ_j) with d_0 = 0).
  {#B2.2.231-1} The density of step k is CRE's (2.18) with A_k(1/g_k²(·), U_k) and the
  {#B2.2.232} terms E_k, R_k, and B_k produced by the steps 0, …, k−1 of the history; this is RG1's convention, in which the
  {#B2.2.233} Wilson term carries the current coupling and the earlier steps enter through the effective action (Remark 2.3,
  {#B2.2.234} *What β is*).
  {#B2.2.234-1} The formula involves the history only through the β^T_j, and on H_j each β^T_j satisfies the same
  {#B2.2.235} per-step bounds as along a flow (Proposition 2.11, *Consequence*).
  {#B2.2.235-1} So every bound that CRE, LFR1, and LFR2 derive
  {#B2.2.236} for g_k(x) from bounds on the β_j, such as 1/(g″_k(·))² − 1/g_k² = O(N) (LFR2 p.366), holds.
  {#B2.2.236-1} Where they use the
  {#B2.2.237} flow identity 1/g_k²(x) = 1/g_m² for x ∈ Λ_m^{∼−1} outside Λ_{m+1}, the top-down value is
  {#B2.2.238} 1/g_k² + Σ_{j=m+1}^{k}β^T_j: the domains are nested (CRE (2.1), p.254), so x ∉ Λ_j and φ_j(x) = 0 for j > m, and
  {#B2.2.239} x ∈ Λ_m^{∼−1} ⊂ Λ_j^{∼−1} (Λ_m ⊂ Λ_j, and the operation ∼ removes cubes of size L^jMR^T_j at scale j, CRE
  {#B2.2.240} pp.245, 256, which are no larger than those of scale m, since L^jR^T_j ≤ L^mR^T_m for j ≤ m by (c)) and
  {#B2.2.241} φ_j(x) = 1 for j ≤ m (φ_j ∈ C_0^∞(Λ_j), φ_j = 1 on Λ_j^{∼−1}, CRE p.259).
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
  {#B2.2.247-1} With x_k ≥ t + b(K−k) − C₀,
    {#B2.2.248} y ≥ t − 2C₀ + b(K−k) + (8/5)c ln L(k−m),  u_m ≤ t + C₀ + b′(K−k) + b′(k−m),
  {#B2.2.249} and b′ ≤ (3/2)b, b′ ≤ 3c ln L, and t ≥ γ^{−2} give, by the mediant inequality,
    {#B2.2.250} u_m/y ≤ max(3/2, 15/8, (t + C₀)/(t − 2C₀)) = ρ̄ for γ small.
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
   {#B2.2.278} (1 + g_n²β′(n−m))^{1/2} ≤ (1 + β₀)(n−m)^{1/2} once γ²β′ ≤ (1+β₀)² − 1.
   {#B2.2.278-1} And x_n ≤ x_m + C ≤ (1+β₀)²x_m for γ
   {#B2.2.279} small, so g_m ≤ (1 + β₀)g_n.
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
   {#B2.2.291} N ≥ (ν/log L) log log g_k^{−2}, with a different exponent ν (READINGS R4).
   {#B2.2.291-1} With N = R_j both hold for g small (R4),
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
   {#B2.2.298-1} N₀ satisfies L^{N₀−1} = R^T_{k−N₀+1} ≤ (L+1)(N₀+1)^{β₀}R^T_k (LFR1 p.192,
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
     {#B2.2.312} place of 1/g_j² and the tube threshold ĝ_jp(ĝ_j) it gives ½ρ̄^{−1}p²(ĝ_j) − O(1)g_jp³ ≥ ¼ρ̄^{−1}p²(ĝ_j).
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
     {#B2.2.327} kinds below, read on CRE's and LFR2's pages; RG1's fixed domains are covered by step 7 and by §0, *Condition 3*.
   {#B2.2.328} Every occurrence is of one of four kinds.
   - {#B2.2.329} *Relations among the parameters alone*, of one index or of several.
     {#B2.2.329-1} Examples: the cube sizes and the
     {#B2.2.330} compatibility of the partitions (CRE pp.245–270, LFR1 p.177, LFR2 pp.384–387); the definitions of k₁ (CRE
     {#B2.2.331} p.270) and N₀ (LFR1 p.179), and the bounds L^{N₀−1} ≤ (L+1)(N₀+1)^{β₀}R_k and R_k^{−α₀} (LFR1 pp.192, 200);
     {#B2.2.332} (2.7) (CRE p.255) and (2.9) (CRE p.256); δ′_j ≤ (1+β₀)²(k−j)^{β₀}δ′_k (LFR1 p.192);
     {#B2.2.333} δ′_j/δ_j = A₀p₁(g_j)/p₀(g_j) (with the definitions of LFR1 p.183); the comparisons of ε_{k+1} with ε_k
     {#B2.2.334} (CRE pp.266–268, LFR1 pp.184–200); N^{1/2}p₁(g_h)/p₀(g_h) small (LFR1 pp.198–199); the margins
     {#B2.2.335} 2p₁ − (d+5)r₀ > p₀ (LFR2 p.383), 2(1+β₀)^{−1}p₀ against O(1)3(100M)^dR^{d+2} (LFR2 (1.88), p.387), and
     {#B2.2.336} −2(1+β₀)^{−1}p₀ + 1 + 2κ(100R_k)^d ≤ −(3/2)p₀ (LFR2 p.389); and bounds through p₀(γ), p₁(γ) (LFR1 p.186).
     {#B2.2.336-1} In the
     {#B2.2.337} tube construction all of these are evaluated on the sequence (ĝ_j).
     {#B2.2.337-1} That sequence satisfies the hypotheses CRE
     {#B2.2.338} places on coupling sequences: its entries lie in (0, γ], it satisfies (2.6) because (u_j) ∈ H_K (step 2), and its
     {#B2.2.339} R^T satisfies (2.9) by (c).
     {#B2.2.339-1} So these relations hold as printed.
   - {#B2.2.340} *Lower bounds from the action.* A threshold τ_j forces a suppression exp(−c yτ_j²), with y the coefficient of the
     {#B2.2.341} action at scale j: 1/g_j², or the top-down value of *Histories that are not flows*, which satisfies
     {#B2.2.342} y ≥ u_j/ρ̄ = ĝ_j^{−2}/ρ̄ there on every tube of the class.
     {#B2.2.342-1} Examples: exp[−(1/g_0²)[1 − Re tr U(∂p)]] ≤ exp(−p₀(g_0)) (LFR1 p.175) and ≤ exp(−½p₀²(g_0))
     {#B2.2.343} (CRE p.244), for |U(∂p) − 1| ≥ g_0p₀(g_0); the large-field factors of
     {#B2.2.344} LFR2 pp.380–383, including exp(−γ₀(1/g_m²)(2δ′_m)²) ≤ exp(−γ₀A₁²p₁²) (p.381) and the factor
     {#B2.2.345} exp(−¼g_j^{−2}(24R_j⁴)^{−2}δ′_j²) (p.382); the factor exp(−c(1/g_j²)δ′_j²) of the components excluded by
     {#B2.2.346} 1 − χ′^{(j)} (*LFR1 (1.55)*); and the Gaussian tails of RG2 (§0, *Condition 3*).
     {#B2.2.346-1} Since
     {#B2.2.347} y ≥ ĝ_j^{−2}/ρ̄ (by (a) when y = 1/g_j², as ρ_γ ≤ ρ̄), yτ_j(ĝ_j)² ≥ ρ̄^{−1}τ_j(ĝ_j)²/ĝ_j², so each such factor
     {#B2.2.348} holds with c replaced by c/ρ̄ = 8c/15, that is, with γ₀ replaced by 8γ₀/15.
     {#B2.2.348-1} The conditions on the constants that
     {#B2.2.349} compare such factors at the same order are then imposed with the factor ρ̄ on the side of the action:
     - {#B2.2.350} the creation factor exp(−γ₀min{½B₃^{−2}A₀², 2A₁², A₁²}p₀²(d′ + 1)) ≤ exp(−½γ₀A₁²p₀²(d′ + 1) − 2p₀) (LFR2
       {#B2.2.351} p.381), whose margin is a factor 2 in the leading term: with ρ̄ = 15/8 the left side is at most
       {#B2.2.352} exp(−(8/15)γ₀A₁²p₀²(d′ + 1)), and (1/30)γ₀A₁²p₀² ≥ 2p₀ for g small;
     - {#B2.2.353} A₀ ≫ A₁ in exp(−⅛B₃^{−2}(1+β₀)^{−2}A₀²p₀²) ≤ exp(−A₁²p₀²) (LFR2 p.381, CRE p.247);
     - {#B2.2.354} 4(1+β₀)^{−2} ≥ ρ̄ in exp(−γ₀(1/g_m²)(2δ′_m)²) ≤ exp(−γ₀4(1+β₀)^{−2}A₁²p₁²) ≤ exp(−γ₀A₁²p₁²) (LFR2 p.381),
       {#B2.2.355} which holds for β₀ ≤ √2 − 1, since then 4(1+β₀)^{−2} ≥ 2;
     - {#B2.2.356} A₀² ≥ 4ρ̄O(1)B₃M²A₁² in exp(−¼(1/g_j²)(O(1)B₃M²)^{−1}ε_j²) ≤ exp(−A₁²p₀²) (LFR2 p.381);
     - {#B2.2.357} A₁ ≥ 48√ρ̄ in exp(−¼(1/g_j²)(24R_j⁴)^{−2}δ′_j²) = exp(−A₁²48^{−2}R_j^{−8}p₁²) ≤ exp(−R_j^{−8}p₁²)
       {#B2.2.358} (LFR2 p.382);
     - {#B2.2.359} ¼γ₀14^{−d}A₁²p₀²(g₁) ≥ O(1)2·64^dM^dL^{d+1}R₁^{d+2} (LFR2 p.385), which has in addition the margin
       {#B2.2.360} p₀² ≫ R₁^{d+2} of a power of log g_1^{−2}.
     {#B2.2.361} Every other such comparison has a margin of a positive power of log g_j^{−2}.
   - {#B2.2.362} *Upper bounds relative to the action.* Fluctuations bounded by a threshold enter the expansion of the action in
     {#B2.2.363} g_jB, giving terms such as (1/g_k²)O(1)|𝐁₀|δ′_k³ ≤ g_kO(1)M^dR_k^{d+2}A₁³p₁³(g_k) (LFR2 p.361), (1/g_k²)(α_{0,k} + α_{1,k})ε_k
     {#B2.2.364} (LFR2 p.368), and p₁²(g_k)(α_{0,k} + α_{1,k}) (LFR2 p.379).
     {#B2.2.364-1} By (e) these ratios change by at most the factor
     {#B2.2.365} 1 + o(1), and ε^T_j ≤ ε_j.
   - {#B2.2.366} *Conversions between scaled and unscaled fields*, such as |A(b)| < g_0^{−1}δ_0 (CRE p.250), |A_j(b)| < g_j^{−1}δ_j
     {#B2.2.367} (LFR1 (1.9), p.178), |B′| < M₀g_k^{−1}ε_k (LFR2 p.356), and |B(b)| ≥ g_j^{−1}δ′_j (LFR2 p.383).
     {#B2.2.367-1} The factor g_j^{±1}
     {#B2.2.368} is the coupling of the history, and the threshold is the tube parameter, so in the unscaled field the threshold
     {#B2.2.369} is δ^T_0, δ^T_j, M₀ε^T_k, or δ′^T_j.
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
   {#B2.2.381} The lower bounds on R_j, such as exp(−R_k) and exp(−δMR_k) small (CRE pp.250–251, 266, 268–269) and
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
   {#B2.2.390} exp(−p₀(ĝ_k)) = ĝ_k^{2A₀(log ĝ_k^{−2})^{p₀−1}} ≤ ĝ_k^{κ₀} ≤ g_k^{κ₀} for γ small, so CRE (2.31) holds with the
   {#B2.2.391} couplings of the history for the new R-terms.
   {#B2.2.391-1} The R-terms of earlier steps, in R′_k and in R″_k alike, keep their
   {#B2.2.392} bounds by CRE's induction ("These terms satisfy all the conditions of the inductive assumption", CRE p.279), which
   {#B2.2.393} in the tube construction runs over the histories of H_k with the tube domains α^T_{i,j}: the R-operation of LFR1
   {#B2.2.394} (1.100), p.201, acts on the step's analyticity domain, which is the tube domain, so its output is analytic and
   {#B2.2.395} bounded there.
7. {#B2.2.396} *RG1 with δ_j^T.* Propositions 2.4, 2.6, and 2.9 use the cutoff only through δ_j ≤ γp₀(γ), through
   {#B2.2.397} δ_j/g_j = A₁(log g_j^{−2})^{p₀} in the Gaussian tails (Proposition 2.9, steps 4–7, and §0, *Condition 3*), and
   {#B2.2.398} through the continuity of δ_j/g_j in g_j.
   {#B2.2.398-1} On the histories of H_k, by (e), δ_j^T/g_j lies between ρ_γ^{−1/2} and
   {#B2.2.399} 1 + o(1) times A₁(log g_j^{−2})^{p₀}, and it is continuous in g_j.
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
3. {#B2.2.420} *The size of the R-part.* By the windows of H_k, x_j ≥ x_k + b(k−j) − C ≥ ½x_k + c ln L·(k−j) for j ≤ k and γ
   {#B2.2.421} small, since b ≥ c ln L on the class of tubes.
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
   {#B2.2.429} controlled by g_j^{κ₀}" (CRE p.260), and (2.44) and (2.46), p.263, bound the R-terms by
   {#B2.2.430} R₁g_j^{κ₀}Σ_{n=j}^{k}|Γ_n ∩ Ω|.
   {#B2.2.430-1} The potential V′ of RG2 Lemma 1, through which the R′-part enters the step, is linear in the constant
   {#B2.2.431} of (2.31): V′ is built linearly from the bracket of E_k (RG2 (1.33)), and the sums over X and j are controlled as
   {#B2.2.432} quoted.
   {#B2.2.432-1} The later expansions of the step, such as the products of RG2 (2.26), p.17, are not linear in it; they use
   {#B2.2.433} only the resulting bound (1.36) with 2E₀ and the smallness condition of RG2 p.18, and the R′-part enters them
   {#B2.2.434} through the modulus of the interaction (*The Step with Complex Multiples of the R-Terms*, below).
   {#B2.2.434-1} Let K_R be the
   {#B2.2.435} constant such that an R′-input of step j whose terms satisfy (2.31) with g_i^{κ₀} replaced by a_ig_i^{κ₀} enters
   {#B2.2.436} the potential V′ of RG2 Lemma 1 with K_RΣ_{i≤j}a_ig_i^{κ₀} in the place of E₀ in (1.36), p.9: its part of V′ is
   {#B2.2.437} at most K_RΣ_{i≤j}a_ig_i^{κ₀}ε₁C₁M^q exp C₂κ₁ exp(−(1−2δ)κd_j(Y)).
   {#B2.2.437-1} So the input side of the step, regular part and
   {#B2.2.438} R′-part together, is bounded as in (1.36) with E₀ + K_RΣ_{i≤j}a_ig_i^{κ₀} in place of E₀.
   {#B2.2.438-1} K_R depends only on the
   {#B2.2.439} constants of CRE's step and on κ, so it is uniform over the class of tubes.
   {#B2.2.440} Every R′-term that has entered E up to step k, at any earlier step, carries the factor s, so a_i = |s|.
   {#B2.2.440-1} Put
   {#B2.2.441} θ := E₀/(K_RC_Σ) and ρ := θg_k^{2−κ₀}.
   {#B2.2.441-1} For j ≤ k, Σ_{i≤j}g_i^{κ₀} ≤ Σ_{i≤k}g_i^{κ₀} ≤ C_Σg_k^{κ₀−2} by the first
   {#B2.2.442} display, so for |s| ≤ ρ
     {#B2.2.443} K_R|s|Σ_{i≤j}g_i^{κ₀} ≤ K_RρC_Σg_k^{κ₀−2} = K_RθC_Σ = E₀
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
   {#B2.2.454} ε₁/g_k (§0, *Condition 3*), and C₃ ≤ E₀C₁ of RG2 p.16.
   {#B2.2.454-1} On CRE's domains the cutoff enters relative to α_{0,j},
   {#B2.2.455} through δ_j/α_{0,j} = (A₁/C^α_0)(log g_j^{−2})^{p₀−q₀}, and CRE takes C^α_0 and C^α_1 "sufficiently large"
   {#B2.2.456} (p.259).
   {#B2.2.456-1} This ratio is small for g_j small when q₀ > p₀, and likewise
   {#B2.2.457} δ_j/α_{1,j} when q₁ > p₀.
   {#B2.2.457-1} CRE (2.28), p.259, prints q₀ and q₁ as "integers greater than 1", and says on p.262
   {#B2.2.458} that "some of the restrictions on constants, e.g. on constants κ, M, ε_j, α_{0,j}, α_{1,j}, come from the paper
   {#B2.2.459} [I]".
   {#B2.2.459-1} RG1 and RG2 bound the domain radii from
   {#B2.2.460} below relative to the cutoff (RG2 p.18) and print no upper restriction on q₀, q₁; nor do LFR2 pp.358, 368, and 379,
   {#B2.2.461} where α_{0,k} + α_{1,k} enters multiplied by small factors (Lemma 2.10, step 6, *upper bounds relative to the
   {#B2.2.462} action*).
   {#B2.2.462-1} So q₀ and q₁ are taken greater than p₀; this choice is listed in §9.
   {#B2.2.462-2} These conditions are imposed for 2E₀ when C^α_0, C^α_1, and the cutoff are chosen.
   {#B2.2.462-3} The step
   {#B2.2.463} output is given by convergent expansions whose terms are analytic in the exponent, uniformly for |s| ≤ ρ, so
   {#B2.2.464} E^{(j+1)}(X; s) is analytic in s.
   {#B2.2.464-1} The parameter s is not CRE's parameter s of (3.26)–(3.27), p.271, which
   {#B2.2.465} multiplies R″_k; that one stays as in CRE.
5. {#B2.2.466} *Polarisation on the tube domains.* E^{(k+1)}_fl(X; s) is analytic on U^c_{k+1}(X, α^T_{0,k+1}, α^T_{1,k+1}) and
   {#B2.2.467} bounded by E₀e^{−κd_{k+1}(X)}.
   {#B2.2.467-1} In the proof of Lemma 2.5 the domain enters only through the Cauchy radius r of step 2,
   {#B2.2.468} and here r ≥ c·min(α^T_{0,k+1}, α^T_{1,k+1}) (`WILSON_CAUCHY_LIPSCHITZ_2026_10_21.md`, *What changes on CRE's
   {#B2.2.469} domains*).
   {#B2.2.469-1} With q_* := min(q₀, q₁) ≥ 2 and x̂ := ĝ_{k+1}^{−2} = u_{k+1} ≤ u_k ≤ ρ_γx_k ≤ 2x_k (Lemma 2.10(a)),
     {#B2.2.470} |β_{k+1}(s) − b_{k+1}| = |Λ(E^{(k+1)}_fl(·; s))| ≤ C′E₀x̂(log x̂)^{−2q_*} ≤ 2C′E₀g_k^{−2}.
   {#B2.2.471} The domain is fixed by the target, so no bound on the next coupling is needed.
   {#B2.2.471-1} The infinite-volume limit of Λ is
   {#B2.2.472} uniform in s by the domination of Lemma 2.5, so s ↦ β_{k+1}(s) is analytic on |s| < ρ.
6. {#B2.2.473} *Cauchy in s.* For γ small, ρ = θg_k^{2−κ₀} > 2 because κ₀ ≥ 7.
   {#B2.2.473-1} For σ ∈ [0, 1] the closed disc of radius ρ/2
   {#B2.2.474} about σ lies in |s| < ρ, since 1 + ρ/2 < ρ, so |β′_{k+1}(σ)| ≤ 4C′E₀g_k^{−2}/ρ, and
   {#B2.2.475} |β_{k+1}(1) − β_{k+1}(0)| ≤ 4C′E₀g_k^{−2}/ρ = 4C′K_RC_Σg_k^{κ₀−4} =: C_Rg_k^{κ₀−4}. ∎

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
  {#B2.2.525} P_i(B⁰) := {|B − B⁰| < r_i}, r_i := c·min(α^T_{0,i+1}, α^T_{1,i+1}), with c so small that u_i maps every P_i(B⁰) into
  {#B2.2.526} D_F.
  {#B2.2.526-1} Such a c exists by RG1 (1.15) and Lemma 2.5, step 1, whose derivative bound comes from VAR Prop. 9 and VAR (190),
  {#B2.2.527} stated for every external configuration satisfying "the regularity conditions (3.35)–(3.38) [5], or (1.7)–(1.9) [6]"
  {#B2.2.528} (VAR p.309 l.8–13).
  {#B2.2.528-1} Then F(X, u_i(B); h) → F(X, u_i(B); h⁰) uniformly on compact subsets of P_i(B⁰), for every
  {#B2.2.529} admissible B⁰.

{#B2.2.530} Lemma 2.5, and so Λ, uses (b) for the regular terms of step k at B⁰ = 0; the localisations of the later steps use (a).
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
   {#B2.2.552} read, in unscaled fields, exp(iB) = exp(iB′)exp(−iφ(B′)H), where φ is the C^∞ bump of CRE p.252 with supports fixed
   {#B2.2.553} by δ^T_0 at step 0, by δ^T_k at the step k, and by δ′^T_j in the change of variables of LFR1 p.188, and H is an
   {#B2.2.554} analytic function of the background fields (H_{1,Ax} of CRE (1.21), 𝐇^{(k)} of CRE (3.22), p.269, and ℍ_Z^{(j)} of
   {#B2.2.555} LFR1 (1.58)).
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
   {#B2.2.615} r max{|δ𝐇_j|_X, …} = ⅓α₂ in RG1 (3.15), p.273, t_□ with |t_□|4B₀C₁e^{16κ₁}g_k|B| = ½α₂ in RG2 (1.22)–(1.23),
   {#B2.2.616} p.7, and σ(Δ) with |σ(Δ)| = e^{κ₁} (RG2 p.7, and RG2 p.8 for (3.15)).
   {#B2.2.616-1} These integrals are the derivatives at
   {#B2.2.617} t_□ = 0 and at s ∈ [0, 1]^{Y₀} of φ_h(t_□, s), the integrand read as a function of (t_□, s) (RG2 (1.9)–(1.10), p.4;
   {#B2.2.618} "We differentiate it with respect to t_□, at t_□ = 0, and we represent all derivatives by the Cauchy formula",
   {#B2.2.619} p.7).
   {#B2.2.619-1} Let D be the open polydisc |t_□|4B₀C₁e^{16κ₁}g_k|B| < ½α₂ (|t_□|max{|δ𝐇_j|_X, …} < ⅓α₂ for (3.15)),
   {#B2.2.620} |s(Δ)| < e^{κ₁}. On D the field 𝐀 stays in the class (3.31) strictly below α₂ (½α₂ from tζ̃_□ and less than ½α₂
   {#B2.2.621} from t_□ζ_□, RG2 p.7), or in (3.14) (⅓α₂ from 𝐇_j(B(t)) and less than ⅓α₂ from t_□δ𝐇_j, bounds that the localised
   {#B2.2.622} functions keep, RG1 p.273), so φ_h is analytic on D and bounded there by RG1 (3.54) and (3.17), with constants
   {#B2.2.623} independent of the history (Lemma 2.10).
   {#B2.2.623-1} In case (ii), φ_h is the last term of RG1
   {#B2.2.624} (3.34), an integral over
   {#B2.2.625} τ ∈ [0, 1] of fifth B-derivatives, or a term obtained from the Taylor terms of (3.34).
   {#B2.2.625-1} The function
   {#B2.2.626} w ↦ 𝐄^{(j)}(X, U_j(□₀, exp iw)) is analytic on the connected open set N of the w above, bounded by E₀exp(−κd_j(X))
   {#B2.2.627} (RG1 (3.53)–(3.54)), and converges at the real points of N by the paragraph above.
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
     {#B2.2.658} functions come from the results of Sects.
     {#B2.2.658-1} D, E of VAR with operators of PBG (LFR2 (1.51),
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
   - {#B2.2.687} *Small-field terms.* E^{(j+1)}(X) is the exponentiated cluster expansion RG2 (2.13), p.14, in the activities H(Z)
     {#B2.2.688} of RG2 (2.14), p.15: integrals over s(Δ), t(Y) ∈ [0, 1] of Cauchy integrals over circles in σ(Δ) and τ(Y), of
     {#B2.2.689} Gaussian integrals over X and B in which "the operators in it are not symmetric, and the second measure is
     {#B2.2.690} complex" (RG2 p.15).
     {#B2.2.690-1} In unscaled fields, at a real point (𝐔, 𝐉) and fixed (σ, τ) on the circles, h enters the
     {#B2.2.691} integrand only through the coupling g_k in the Gaussian densities exp(−Q_σ/(2g_k²)) and their normalisations,
     {#B2.2.692} where the quadratic form Q_σ of (X, B) does not depend on h (step 1), and through the potentials 𝐕_k(Y, B), read
     {#B2.2.693} at real B and continuous in h by step 2 and S_{j−1}; the characteristic functions χ_{k,Y₀} and χ^c_{k,P} are
     {#B2.2.694} fixed.
     {#B2.2.694-1} So the integrand converges pointwise.
     {#B2.2.694-2} RG2 (2.15)–(2.23), pp.15–17, bound its modulus pointwise by e^C
     {#B2.2.695} times the integrand of (2.23): the forms are compared with those at σ(Z) = 0, 𝐔 = U, 𝐉 = 0, and the differences
     {#B2.2.696} and the potentials are bounded by α₅(‖ZX‖² + ‖Z₀B‖²) plus constants ((2.16)–(2.21)), with α₅ so small that the
     {#B2.2.697} form of (2.23) stays positive (RG2 p.17, (2.24)–(2.25)).
     {#B2.2.697-1} In unscaled fields this majorant is a positive Gaussian
     {#B2.2.698} density in which the coupling enters as g_k^{−2} in front of a nonnegative form, so for ½g⁰_k ≤ g_k ≤ 2g⁰_k it is
     {#B2.2.699} at most 4^n times its value at 2g⁰_k, n the number of integration variables.
     {#B2.2.699-1} Dominated convergence over (X, B),
     {#B2.2.700} (σ, τ), and (s, t) gives the continuity of H(Z).
     {#B2.2.700-1} By RG2 Lemma 3, (2.38), p.20,
     {#B2.2.701} |H(Z)| ≤ C₃ε₁exp(−(1 − 8δ)½Lκd_{k+1}(Z)), uniformly in h, and the series (2.13) is "estimated in the standard
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
     {#B2.2.712} σ(g_kB)δ_{rT}(B)χ′(X), and over the gauge field V_h with χ_{h,1/2}, of T_h(Z_h ∩ X) applied to the exponential of
     {#B2.2.713} −½⟨DH″_{1,k,X}B, ζDH″_{1,k,X}B⟩ − A((g″_k(·))^{−2}ζ₁⌈_X, U″_{h+2}(exp ig_kB, V″)) + V(X^∼, U_k) + E_k(X) and the
     {#B2.2.714} normalisation constants.
     {#B2.2.714-1} T_h(Z_h ∩ X) is the ordered product CRE (2.20) of the operations (2.21) of the earlier
     {#B2.2.715} steps, integrals over gauge fields V_j with the Haar measure and over fluctuation fields A_j with Gaussian
     {#B2.2.716} densities.
     {#B2.2.716-1} Of these expressions only the quadratic form in B and V(X^∼) depend on (𝐔, 𝐉) ("only the quadratic
     {#B2.2.717} form in B and the term V(X^∼) depend on (𝐔,𝐉)", LFR2 p.379).
     {#B2.2.717-1} At a real point the integration variables are real,
     {#B2.2.718} and the modulus of the integrand is the exponential of the real part of its exponent.
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
   {#B2.2.763} real space ℝ^N of B, and P is connected; an analytic function on a connected open set of ℂ^N that vanishes on a
   {#B2.2.764} nonempty open subset of its real points vanishes identically.
   {#B2.2.764-1} So every limit is f_{h⁰}, and f_h → f_{h⁰} locally
   {#B2.2.765} uniformly on P. This is (b).
5. {#B2.2.766} *The coefficient.* β^T_{k+1} is computed by CRE (3.57) and (3.61), pp.281–282, from the whole-lattice E^{(k+1)},
   {#B2.2.767} through the infinite-volume limit of Λ, as the torus T^{(k+1)} ↗ ℤ^d ("This limit exists by the localized
   {#B2.2.768} representation (1.7)", RG1 (1.21), p.264).
   {#B2.2.768-1} The limit is taken of Π_{k+1}(x, x′) at fixed x, x′, and β is
   {#B2.2.769} Σ_x Π_{k+1}(x)x_μx_ν (RG1 (1.22)).
   {#B2.2.769-1} Bałaban states the existence of the limit for each history and prints no rate.
   {#B2.2.770} A rate uniform in h comes from the mechanism the sentence names.
   {#B2.2.770-1} RG2 localises the fluctuation-field effective
   {#B2.2.771} action "using the generalized random walk expansions for propagators" (p.1): each propagator is the sum (1.6) over
   {#B2.2.772} walks ω = ((0, X_0), (α_1, X_1), …, (α_n, X_n)) of products R_0(X_0)R_{α_1}(X_1)⋯R_{α_n}(X_n) of local operators on
   {#B2.2.773} simple localisation domains, the term of a walk is bounded by O(1)O(M₁^{−1/2})^{|ω|}M₁^{−|ω|/2}exp(−δ₀d(ω, y, y′))
   {#B2.2.774} (RG2 (1.7), p.3, from PBG (3.107)–(3.108)), the term of ω is multiplied by the decoupling variables s(Δ) of the cubes
   {#B2.2.775} it meets (RG2 p.3), and the localised terms are the s-derivatives and the exponentiated cluster expansion of RG2 §2
   {#B2.2.776} built from these (RG2 pp.13, 21).
   {#B2.2.776-1} Each factor depends on the external configurations restricted to its domain X̃^5_m
   {#B2.2.777} and is built from local inverses: G = G₀(I − R)^{−1} = Σ_n G₀R^n (PBG (3.106), p.414), with R of PBG (3.105) a sum
   {#B2.2.778} over cubes □ of operators formed from the cube-local inverses G_□, the cutoffs h_□ and ζ_□̃, and the projection P,
   {#B2.2.779} which PBG p.415 replaces by its own random walk expansion with local inverses G′ on enlarged cubes and boundary
   {#B2.2.780} conditions outside them (RG2's application of PBG's construction to the chain's propagators, READINGS.md R50).
   {#B2.2.781} Each such factor does not depend on the torus once its side exceeds diam X̃^5_m.
   {#B2.2.781-1} So
   {#B2.2.782} within one step, for a fixed polymer X, the torus enters only through walks of total length at least a fixed
   {#B2.2.783} multiple of the side, and these are bounded by the same bounds times e^{−c·side}.
   {#B2.2.784} The inputs of the step also come from the torus: the effective action of the earlier steps, with the R-terms
   {#B2.2.785} R^{(i)} summed over X "in T_ξ" (CRE (2.33), p.260), which the R-operation of LFR1 (0.3)–(0.6) produced.
   {#B2.2.785-1} This is
   {#B2.2.786} handled by induction over the steps, with the claim W_j: every localised regular term and R-term F(X) produced by
   {#B2.2.787} the steps 0, …, j with diam X at most a third of the side differs from the term of the same construction
   {#B2.2.788} on L^{−j}ℤ^d, to which CRE extends the sums ("to all domains X ∈ D_j for the space L^{−j}Z^d", CRE p.281), by at
   {#B2.2.789} most C_We^{−c·side} times its bound, uniformly in h on H_j.
   {#B2.2.789-1} W_{−1} is empty.
   {#B2.2.789-2} In step j+1 the new terms are
   {#B2.2.790} analytic functions of the inputs on the domains of CRE p.259, bounded by the inductive bounds, so by Cauchy
   {#B2.2.791} estimates a change of the inputs by e^{−c·side} times their bounds changes the outputs by C e^{−c·side} times
   {#B2.2.792} theirs; the step's own expansions, including the polymer expansions (0.5) of the R-operation, whose activities
   {#B2.2.793} decay as exp(−κd(X)) (LFR2 pp.388–389), add the winding contributions bounded as above; and terms that wrap the
   {#B2.2.794} torus are bounded by exp(−κd_j(X)) with d_j(X) at least a fixed multiple of the side.
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
   {#B2.2.801-1} On the torus of side s, x is
   {#B2.2.802} represented in the fundamental domain (−s/2, s/2]^d, which defines x_μx_ν.
   {#B2.2.802-1} For ε > 0 let F be a finite set of pairs
   {#B2.2.803} (X, x) of ℤ^d, all within distance R of 0, with Σ_{(X,x)∉F}m(X, x) < ε on ℤ^d.
   {#B2.2.803-1} For s > 8R the pairs of F are
   {#B2.2.804} identified with torus pairs, and their X have diam X ≤ 2R < s/3, as W_k requires.
   {#B2.2.804-1} Take the torus pairs with
   {#B2.2.805} diam X, dist(0, X), and |x| all at most s/8.
   {#B2.2.805-1} Lift x into the fundamental domain, and X along its paths from a lift of a
   {#B2.2.806} point nearest to 0, at distance ≤ s/8 from 0; then the lifts of x and X lie in the ball of radius s/4 about 0.
   {#B2.2.806-1} So any
   {#B2.2.807} two of their points differ by at most s/2 in each coordinate, and then no translate by sℤ^d brings them closer in
   {#B2.2.808} any coordinate.
   {#B2.2.808-1} Hence the torus distances dist(0, X), dist(x, X), and diam X equal the ℤ^d distances of the lifts, and so
   {#B2.2.809} does d_{k+1}(X) when its tree graphs have length below s/4 in lattice units (the other pairs go to the remainder
   {#B2.2.810} below): a tree graph is simply connected, so it lifts to ℤ^d with the same length from a point of the lift of X;
   {#B2.2.811} the lifted tree stays within distance s/4 + s/4 = s/2 of 0, while the other translates of X lie beyond s − s/4, so
   {#B2.2.812} it meets the cubes of the lift of X, and the ℤ^d value is at most the torus value; the converse inequality is the
   {#B2.2.813} projection.
   {#B2.2.813-1} The lift
   {#B2.2.814} is injective with the same x_μx_ν, so these pairs not in F contribute less than ε.
   {#B2.2.814-1} Every other torus pair has
   {#B2.2.815} diam X, dist(0, X), or |x| greater than s/8, or only tree graphs of length at least s/4; since d_{k+1}(X) is at
   {#B2.2.816} least c times the diameter and the tree length at fixed k, its majorant carries a factor e^{−cs}, and the
   {#B2.2.817} sum of the majorants over them is at most C·poly(s)e^{−cs}, with the polymer count absorbed by part of the factor
   {#B2.2.818} e^{−κd_{k+1}(X)} as in Lemma 2.5.
   {#B2.2.818-1} On F the torus terms converge to the ℤ^d terms uniformly in h by W_k (the B-terms
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
   {#B2.2.827-1} Then x_K =: F(x_0) is continuous in x_0 by
   {#B2.2.828} Proposition 2.12.
2. {#B2.2.829} *The interval.* By the *Consequence* above, |β^T_{j+1} − b_{j+1}| ≤ δ′ at every history of H_j, so
   {#B2.2.830} Σ_{j=m}^{n−1}β^T_{j+1} ∈ [b(n−m) − C, b′(n−m) + C] for the projected flow, by Theorem 8.1 (Remark 2.3).
   {#B2.2.830-1} This uses
   {#B2.2.831} only that the arguments of β^T lie in H_j, not that the flow itself does.
   {#B2.2.831-1} With m = 0 and n = K,
   {#B2.2.832} F(x_0) ∈ [x_0 − b′K − C, x_0 − bK + C].
   {#B2.2.832-1} So F(ℓ_0) ≤ t ≤ F(u_0), and F takes the value t at some x_0 ∈ T_0.
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
- {#B2.2.842} at every depth k < K, its β^T_{k+1} satisfies the per-step bounds of (W) with δ′ and item 5 with
  {#B2.2.843} C_rem + C_Rγ^{κ₀−6} on the histories of H_k (*Consequence*);
- {#B2.2.844} at every depth k < K, β^T_{k+1} is continuous on H_k (Proposition 2.12); the tube is not defined at K + 1, and no
  {#B2.2.845} β^T_{K+1} is used;
- {#B2.2.846} item 2 holds: a bare coupling g_0 gives the flow with g_K = g inside H_K (Proposition 2.13);
- {#B2.2.847} items 3 (with δ′ in place of δ) and 4 hold along that matched flow.
{#B2.2.848} This is not a statement about CRE's printed construction, whose parameters jump or move with the couplings, so that
{#B2.2.849} its β_{k+1} is not a continuous function of the history (*CRE's Construction as a Function of the History*).
{#B2.2.849-1} The construction depends on the target (K, g): the parameters, the
{#B2.2.850} densities ρ_k, the effective actions, the coefficients β^T, the couplings g_k, and the bare coupling g_0 are those of
{#B2.2.851} the tube of (K, g), and objects of different targets are not identified with each other.
{#B2.2.851-1} The constants in the bounds (C_Λ, C₃, C_rem, C′, C_Σ, K_R,
{#B2.2.852} C_R, δ′, and C₀) are independent of K and g.
{#B2.2.852-1} Statements that combine several targets, such as a limit K → ∞ at fixed
{#B2.2.853} physical scale, use only these uniform bounds and the properties of each target's own construction.

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
- {#B3.1.7} P: Y → Ȳ, restriction to level-k sites (L odd, so these are fine sites).
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

  {#B3.1.16} Z_k[h] = c · det(QQᵀ)^{−1/2} · det(h|_W)^{−1/2} · det(D_0ᵀD_0)^{1/2},  W := ker Q ⊖ D(Y_0).

{#B3.1.17} Here c does not depend on the background.
{#B3.1.17-1} *Reason.* The axial slice meets each residual orbit once, and the map
{#B3.1.18} (slice, ω) ↦ A_s + Dω has block-triangular Jacobian with determinant det D_tree = 1.
{#B3.1.18-1} So the slice integral equals
{#B3.1.19} ∫ e^{−½⟨A,hA⟩} δ(QA) dA divided by ∫_{Y_0} dω.
{#B3.1.19-1} The δ-integral equals det(QQᵀ)^{−1/2} ∫_{ker Q}.
{#B3.1.19-2} Splitting
{#B3.1.20} ker Q = W ⊕ D(Y_0) with the induced orbit measure det(D_0ᵀD_0)^{1/2} dω gives the formula.

{#B3.1.21} **Definitions.** For each level j:
- {#B3.1.22} Δ_j is the quadratic form on Z_j ⊖ ran D̄_j given by ⟨z, Δ_j z⟩ := min{⟨A, hA⟩ : Q_j A ∈ z + ran D̄_j}.
  {#B3.1.22-1} It is the
  {#B3.1.23} gauge-invariant coarse action of level j.
  {#B3.1.23-1} At U = 1 it is Bałaban's ⟨B, Δ_j B⟩ = ⟨dH_jB, dH_jB⟩ (PRT1 (1.65)).
- {#B3.1.24} F_j := ½ log det_⊥(Δ_j) − ½ log det(D̄_jᵀD̄_j).
- {#B3.1.25} At level 0 (Q_0 = 1, D̄_0 = D): Δ_0 = h|_{(ran D)^⊥}, so F_0 = ½ log det_⊥(h) − ½ log det(DᵀD).

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
   - {#B3.2.12} the matrix determinant lemma: det h_F = det(Π_KΔ_FΠ_K) · det_Ȳ(1 − N), with N := PDᵀ C DPᵀ and
     {#B3.2.13} C := Δ_F^{−1} − Δ_F^{−1}QᵀS^{−1}QΔ_F^{−1} (the inverse of Π_KΔ_FΠ_K on K, extended by 0).

   {#B3.2.14} Using Δ_F^{−1}D = D(DᵀD)^{−1} and QΔ_F^{−1}D = D̄P(DᵀD)^{−1}:
   - {#B3.2.15} DᵀCD = 1 − (DᵀD)^{−1}PᵀD̄ᵀS^{−1}D̄P(DᵀD)^{−1};
   - {#B3.2.16} hence 1 − N = R D̄ᵀ S^{−1} D̄ R, and det_Ȳ(1 − N) = (det R)² det(D̄ᵀS^{−1}D̄).
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

{#B3.2.28} **Corollary 3.2 (Steps).** The one-loop factors of RG steps 1, …, k compose: the δ-constraints compose exactly, and
{#B3.2.29} nested Gaussian integrations multiply by the Schur-complement identity.
{#B3.2.29-1} So Σ_{j<k} log Z^{(j)}[h] = log Z_k[h], and the
{#B3.2.30} step-(k+1) one-loop term is

  {#B3.2.31} **log Z^{(k)}[h] = F_{k+1} − F_k + const.**

{#B3.2.32} **Lemma 3.3 (Full-Space Form).** Δ_k vanishes on ran D̄ and is positive on (ran D̄)^⊥.
{#B3.2.32-1} Hence
{#B3.2.33} log det_⊥ Δ_k = log det(Δ_k + D̄D̄ᵀ) − log det(D̄ᵀD̄), and

  {#B3.2.34} **F_k = ½ log det(𝒟_k) − log det(D̄ᵀD̄),  𝒟_k := Δ_k + D̄D̄ᵀ.**

{#B3.2.35} **Remark 3.4 (Finite Tori and Infinite Volume).** The symbols of §§4–8 are infinite-volume momentum integrals.
{#B3.2.35-1} A
{#B3.2.36} finite torus serves only to prove identities between them, and it is used one momentum coset at a time.
- {#B3.2.37} *The defect at U = 1.* Let T be the coarsest lattice of the quantity at hand (T^{(k+1)} in §4, the top lattice in
  {#B3.2.38} §§5–8), a torus of side N. Let B = t(a e^{ip·y} + c.c.) be a plane wave with p ∈ (2π/N)ℤ⁴, p ≢ 0 mod 2π, and
  {#B3.2.39} a ∈ g_ℂ ⊗ ℂ⁴.
  {#B3.2.39-1} At U = 1, ker D consists of the constant 0-forms, and the constant 1-forms lie in (ran D)^⊥ ∩ ker h.
  {#B3.2.40} For t ≠ 0, ker D_U consists of the parallel sections.
  {#B3.2.40-1} For a = e₁w with w ∈ g and p₂ ≢ 0, some plaquette holonomies
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
  {#B3.2.59} Σ_{p′∈𝒪∪(−𝒪)} M(p′, p).
  {#B3.2.59-1} Here M is the one-loop integrand of its Bloch form, with internal lines at p′ and p′ + p:
  {#B3.2.60} Proposition 4.2(d) for J^{(k)}, Proposition 7.1(f) for F_k with k ≥ 1, and, for F_0, the form below.
  {#B3.2.60-1} For N larger than the ranges of the local operators, the fibre of each operator at
  {#B3.2.61} U = 1 is its infinite-volume symbol, since inverses, projections, and Schur complements are taken fibrewise.
  {#B3.2.61-1} Put
  {#B3.2.62} Π^N(p) := N^{−4} Σ_{p′∉ℤp} M(p′, p).
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
  - {#B3.2.71} The second-order part of log det_{T₀}(P_TΠ_UP_T) is −tr(P_TD₁(DᵀD)^{−1}D₁ᵀP_T), as in Proposition 7.1(e), and
    {#B3.2.72} log det(D_UᵀD_U) has propagators (DᵀD)^{−1} with vertices (DᵀD)₁ and (DᵀD)₂.
  - {#B3.2.73} So in this form every factor of degree 2 sits on one internal line, and the integrand has degree at most 2 at
    {#B3.2.74} each of p′ = 0 and p′ = −p.
- {#B3.2.75} *Infinite volume.* M(·, p) is continuous away from p′ ∈ {0, ∓p} mod 2π, and has singularities of degree at most 2
  {#B3.2.76} there (Proposition 4.2(d), degree count; Proposition 7.1(f); for F_0, the form above).
  - {#B3.2.77} Since d = 4, the grid points within distance r of a singular point contribute at most Cr² to Π^N, uniformly in N.
  - {#B3.2.78} p is fixed along the sequence of N, so p ∈ 2πℚ⁴ has a fixed order m₀ in ℝ⁴/2πℤ⁴, and ℤp consists of m₀ points
    {#B3.2.79} independent of N. Apart from 0 and ∓p they are not singular, so |M| ≤ C_p there, and ℤp would contribute at most
    {#B3.2.80} C_pm₀N^{−4}.
  - {#B3.2.81} Hence Π^N(p) → ∫_{[−π,π]⁴} M(p′, p) d⁴p′/(2π)⁴ as N → ∞ through the N with p ∈ (2π/N)ℤ⁴.
    {#B3.2.81-1} These integrals are the
    {#B3.2.82} symbols of §§4–8.
    {#B3.2.82-1} In §7 the external momentum is p₀ and the internal one p.
  - {#B3.2.83} The integrals are continuous in p ≢ 0: for p in a compact set avoiding 2πℤ⁴, the integrals of the bounds over
    {#B3.2.84} r-neighbourhoods of the singular points are O(r²) uniformly in p. So the identities extend from the dense set
    {#B3.2.85} ⋃_N (2π/N)ℤ⁴ to every p ≢ 0.
    {#B3.2.85-1} The symbol of J^{(k)} (Proposition 4.2) extends continuously to p = 0 (Lemma 4.3).

### 3.3 Which h Is Meant: J-Terms {#BS3.3}

{#B3.3.1} Bałaban's step Gaussian is taken at the constrained minimiser U* = U_{k+1}(e^{iB}), where ∇A(U*) = Q_{k+1}ᵀλ ≠ 0.
{#B3.3.1-1} Its
{#B3.3.2} quadratic form is the Lagrangian Hessian h_L = Hess A − ⟨λ, Hess φ_{k+1}⟩ on the constraint tangent space, modulo the
{#B3.3.3} residual gauge directions.
{#B3.3.3-1} RG1 (1.5) writes this out: the J-term is −2⟨H hC̃^{(2)}, J⟩, with J the gradient
{#B3.3.4} (RG1 (1.8)).

{#B3.3.5} Throughout, h := Π_⊥ Hess A(U) Π_⊥ (Π_⊥ onto (ran D_U)^⊥).
{#B3.3.5-1} This form is gauge-invariant (hD = 0), the same for all
{#B3.3.6} levels, and involves no λ.
{#B3.3.6-1} The Hessian of a gauge-invariant function transforms covariantly even off-shell, because
{#B3.3.7} the coordinates X ↦ U e^{iX} transform linearly.
{#B3.3.7-1} Differentiating ⟨∇A, Dω⟩ ≡ 0 shows that
{#B3.3.8} h_L − h = (terms linear in ∇A(U) or λ), and λ = (QQᵀ)^{−1}Q∇A.
{#B3.3.8-1} Define the **step J-term**

  {#B3.3.9} J^{(k)}(U) := log Z^{(k)}_{Bałaban}(U) − (F_{k+1} − F_k)(U).

## 4. The J-Terms Do Not Contribute to the Marginal Coefficient {#BS4}

{#B4.1} **Notation.** "Symbol" means the Fourier multiplier on the coarse lattice (unit spacing, momentum p ∈ [−π, π]⁴) of a
{#B4.2} translation-covariant linear map, or of a quadratic form's kernel.
{#B4.2-1} The second-order Taylor coefficient in B of a
{#B4.3} function of the coarse field B has the symbol Π(p) (the polarisation).
{#B4.3-1} The marginal coefficient is read off from the
{#B4.4} O(|p|²) part of Π(p) (RG1 (1.22)).
{#B4.4-1} Write v_ν(p) := e^{ip_ν} − 1, so that pure-gauge coarse fields are
{#B4.5} B = v(p)ω̂ e^{ipy}.

{#B4.6} **Lemma 4.1 (Second-Order Vanishing).** Let T(p) (4×4 in the vector index, ⊗ 1 on g) satisfy T(p)v(p) = 0 for all p.
- {#B4.7} (a) If T is C² on a ball around p = 0, with the derivatives of order at most 2 bounded by C there, and T is covariant
  {#B4.8} under the hyperoctahedral group (signed permutations R), T(Rp) = ρ(R, p)T(p)ρ(R, p)^{−1}, with ρ(R, ·) unitary and
  {#B4.9} differentiable and ρ(R, 0) the signed permutation matrix of R, then ‖T(p)‖ ≤ (C/2)|p|² on that ball.
  {#B4.9-1} (For bond variables at the
  {#B4.10} initial site, ρ(R, p) carries phases e^{±ip_λ}; with pure signs ρ(R, p) = ρ(R, 0) for all p, covariance and
  {#B4.11} T(p)v(p) = 0 together force T ≡ 0.)
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
{#B4.34-1} The same holds for finite sums of such f, with the pairs (a, b) varying from term to term.

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
{#B4.49} ‖Π_J^{(k)}(p)‖ ≤ C for all p, with C independent of k.
{#B4.49-1} Hence, for every α ∈ (0, ½), ‖Π_J^{(k)}(p)‖ ≤ C_α|p|^{2+2α} on
{#B4.50} [−π, π]⁴ with C_α := C max(π^{1−2α}, π^{−2−2α}), and J^{(k)} contributes nothing to b_{k+1}.

{#B4.51} **Setting.** Units are those of T^{(k+1)}, so p ∈ [−π, π]⁴ is the coarse momentum of §4's Notation.
{#B4.51-1} The fine objects
{#B4.52} 𝐇, J, h, K, φ_A, Π_D, D, Q, Q′, R, G′, Δ′_π, G, and H are those of §7's Setting at the chain level k, and C_G denotes
{#B4.53} §7's C := G − GQ*(QGQ*)^{−1}QG.
{#B4.53-1} The step variable B′ is a g-valued function on the bonds of T^{(k)}, h_B is RG1's
{#B4.54} operator h of p.267 l.18–23 (written h_B to distinguish it from §3's h), C̃^{(2)} is the second-order part of the
{#B4.55} nonlinear Q̃(B′) of RG1 (2.4), whose linear part is LQ̃ (RG1 p.261 l.10–11; p.267 l.26 and, D̃^{(2)} = C̃^{(2)}, l.29;
{#B4.56} (d), *The step objects*), C^{(2)} is the second-order part of the dressed average Q
{#B4.57} (Lemma 7.3), which enters Δ^{(2)}_π through PBG (3.134), 𝐆^{(2)} is twice the quadratic part of the axial gauge-fixing
{#B4.58} term, 𝐆 = ½𝐆^{(2)} + 𝐆₃ (RG1 (2.5), p.266), and 𝒫 is Bałaban's parametrisation of {Q̃B′ = 0} (p.268 l.2–3; RG1
{#B4.59} writes it C).
{#B4.59-1} By constant-gauge covariance at U = 1 (step (b)), every symbol at U = 1 below commutes with Ad(G) on
{#B4.60} g_ℂ ⊗ ℂ⁴.
{#B4.60-1} Since g is simple, Ad is irreducible on g_ℂ, so by Schur's lemma these symbols have the form T₀(p) ⊗ 1, as
{#B4.61} Lemma 4.1 takes them.

{#B4.62} *Proof.*

{#B4.63} *(a) Bałaban's step form.* By RG1 (1.4)–(1.5) with j = k, and (2.11) with p.267 l.38–39,
{#B4.64} Z^{(k)}(U) = ∫dB′ δ(Q̃B′) exp[−½⟨B′, Δ^{(k)}(U)B′⟩] with

  {#B4.65} ⟨B′, Δ^{(k)}B′⟩ = ⟨H₁B′, Δ₁H₁B′⟩ − 2⟨H₁h_BC̃^{(2)}(B′), J⟩ + 𝐆^{(2)}(B′),

{#B4.66} where 𝐆^{(2)} replaces the δ-function gauge fixing of PBG (3.156).
{#B4.66-1} Eliminating the variables B′(b₀(c)) by δ(Q̃B′) gives
{#B4.67} B′ = 𝒫B″, Z^{(k)}(U) = c(U)·det(𝒫*Δ^{(k)}(U)𝒫)^{−1/2}, and C^{(k)} = (𝒫*Δ^{(k)}𝒫)^{−1} (p.268 l.2–3).
{#B4.67-1} Here c(U) is
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
{#B4.82} log Z^{(k)}(U) = F(U, J(U)) + log c(U) − ½ log det(𝒫*Δ^{(k)}(U, 0)𝒫) + const.
- {#B4.83} At j = 0, X = 0 and Y = 0, and the argument of Proposition 7.1(b) gives ⟨B′, Δ^{(k)}(U, 0)B′⟩ = ⟨B′, Δ_kB′⟩ +
  {#B4.84} 𝐆^{(2)}(B′), with §3's Δ_k on the level-k field B′.
- {#B4.85} On {Q̃B′ = 0}, the gauge directions of Δ_k are the ω vanishing at the sites of T^{(k+1)} (QD = D̄P, §3.1).
  {#B4.85-1} They shift
  {#B4.86} B̃′(y, x) by −Ad(V(y, x))ω(x), which is orthogonal at real V. So the Gaussian integral over these directions against
  {#B4.87} e^{−½𝐆^{(2)}} is a constant, and the axial slice has Faddeev–Popov determinant 1 (§3.1).
  {#B4.87-1} The integral
  {#B4.88} ∫dB′ δ(Q̃B′) exp[−½⟨B′, Δ^{(k)}(U, 0)B′⟩] carries the same Jacobian c(U), so
  {#B4.89} log c(U) − ½ log det(𝒫*Δ^{(k)}(U, 0)𝒫) = log Z^{(k)}[h] + const = (F_{k+1} − F_k)(U) + const on each coset
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
  {#B4.118} Q_{k+1}A = B (Proposition 5.3, step 1, third fact), ∂ᵀ∂H_{k+1}B = Q_{k+1}ᵀλ_B.
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
  {#B4.128} ⟨j, Θ(U)⟩ = −½tr(𝒞(U)𝒫*V(U, j)𝒫).
  {#B4.128-1} In the direction A₁, the U-derivative falls on 𝒞, 𝒫, H_h, X, h_B, or C̃^{(2)}.
  {#B4.129} By §3.3, h(U) = 𝐇(U) − K(U, J(U)) with ∂J(1)[A₁] = 𝐇(1)A₁, so ∂_Uh(1)[A₁] = ∂𝐇(1)[A₁] − K(1, 𝐇(1)A₁).
  {#B4.129-1} In K, the
  {#B4.130} derivative of φ_A at fixed A is (∂ᵀ∂)^{−1}[D₁ᵀΠ_⊥A − ∂ᵀD₁φ_A], as in Proposition 7.1(d), T4.
- {#B4.131} *F_jj.* ½F_jj[j, j] = −½tr(𝒞𝒫*V₂(j)𝒫) + ¼tr(𝒞𝒫*V(1, j)𝒫𝒞𝒫*V(1, j)𝒫) at U = 1, with V₂(j) the j-quadratic part
  {#B4.132} of Δ^{(k)}(1, j).
  {#B4.132-1} The constrained Gaussian gives the j-quadratic part of the minimum as
  {#B4.133} −⟨H(1)B′, X(1, j)C_GX(1, j)H(1)B′⟩ (as in Proposition 7.1(b)).
  {#B4.133-1} The j-quadratic part of Y is
  {#B4.134} −2⟨∂_jH₁[j]h_BC̃^{(2)}(B′), j⟩, with ∂_jH₁[j] = −C_GX(1, j)H(1) by differentiating H₁ = G₁Q*(QG₁Q*)^{−1}.
- {#B4.135} *Bloch form.* At U = 1 every operator commutes with the translations of T^{(k+1)}.
  {#B4.135-1} For B of momentum p, each trace
  {#B4.136} is ∫_{[−π,π]⁴} tr_q M(q, p) d⁴q/(2π)⁴, the limit of the coset sums (Remark 3.4), with q the quasi-momentum of the internal line on which no external leg has
  {#B4.137} acted, and q + p that of the other line. tr_q runs over the step variables of one cell of T^{(k+1)}, which number
  {#B4.138} dL^d dim g, so |tr_q M| ≤ dL^d dim g ‖M(q, p)‖, and ‖M‖ is at most the product of the fibre norms of its factors
  {#B4.139} (§7's Bloch norms).
  {#B4.139-1} The integrands are 2πℤ⁴-periodic in q.
- {#B4.140} *Regular factors (L).* Their Bloch symbols are bounded with bounded q-derivative, uniformly in k, by exponential
  {#B4.141} decay of their kernels and the Schur test: 𝒞(1) = C^{(k)}(1), 𝒫, H, G, G′, C_G, R, Q, Qᵀ, A₁, D₁, Δ′_π (through
  {#B4.142} λ_A = G′RD*A), Δ^{(2)}_π, h_B, C̃^{(2)}, 𝐆^{(2)}, ∂𝐇(1)[A₁], the local factors of T in (7.1), and the U-derivatives
  {#B4.143} at 1 in the direction A₁ of 𝒫, R, Q, Qᵀ, D, the transports R(U_b), h_B, C̃^{(2)}, C^{(2)}, and 𝐆^{(2)}.
  {#B4.143-1} Sources: PBG Thms 3.1, 3.2
  {#B4.144} (for R, p.399 l.4), 3.3, 3.12, and 3.15 and (3.131)–(3.133) at U = 1, where H, G, G′, C_G, R, Q, and (QGQ*)^{−1} are PBG's own operators by
  {#B4.145} §7's Setting.
  {#B4.145-1} For Δ^{(2)}_π, PBG (3.134)–(3.135) with Lemma 7.3: |⟨A′, Δ^{(2)}(1, j)A⟩| ≤
  {#B4.146} 2‖C^{(2)}(1; A′, A)‖_1‖H(1)*j‖_∞ ≤ C‖j‖_∞‖A‖_2‖A′‖_2 by (3.133), and its finite range bounds the q-derivative.
  {#B4.147} Lemma 7.3 also gives the U-derivatives at 1 of Q, Qᵀ, and C^{(2)}.
  - {#B4.148} *Explicit local factors.* With D_Uλ(b) = η^{−1}(R(U_b)λ(b₊) − λ(b₋)) (PBG (3.50), p.400, and p.418) and
    {#B4.149} U(t) = exp(itηA₁ + O(t²)), the U-derivative of D is D₁λ(b) = i[A₁(b), λ(b₊)], of range 1, with sup norm
    {#B4.150} ≤ 2‖A₁‖_∞‖λ‖_∞ and ℓ² norm ≤ 2√d‖A₁‖_∞‖λ‖_2 (each site is b₊ of d positively oriented bonds).
    {#B4.150-1} The transports
    {#B4.151} R(U_b) in T of (7.1) and in PBG (3.120) have U-derivative iη ad_{A₁(b)}, of range 0 and norm ≤ 2η‖A₁‖_∞.
    {#B4.152} 𝐇(U) is the Hessian of the Wilson action W in the chart A ↦ e^{iηA}U.
    {#B4.152-1} Since e^{isηA}e^{itηA₁} =
    {#B4.153} exp iη(sA + tA₁ + (i/2)ηst[A, A₁] + …) and 1 is a critical point of W,
    {#B4.154} ⟨A, ∂𝐇(1)[A₁]A⟩ = W‴(1)[A₁, A, A] + iη⟨[A, A₁], 𝐇(1)A⟩, with W‴ the third derivative of X ↦ W(e^{iηX}) at 0.
    - {#B4.155} With U = e^{iηX} the plaquette logarithm is iη²(d_ηX + q(X)) + O(η³), q(X) a sum of commutators [X(b), X(b′)]
      {#B4.156} of bonds of the plaquette, and 1 − Re tr e^{iY} has no cubic term (tr Y³ is real).
      {#B4.156-1} So the cubic part of the
      {#B4.157} action is, up to constants and orientation signs, η^d Σ_p tr(d_ηX·q(X)): each term of W‴(1)[A₁, ·, ·] has one
      {#B4.158} fine difference quotient d_η, on A₁ or on one of the two other arguments, and a commutator with the remaining
      {#B4.159} two, and it has finite range.
    - {#B4.160} The chart term.
      {#B4.160-1} As an operator, the chart part of ∂𝐇(1)[A₁] is the symmetric (iη/2)[ad_{A₁}, 𝐇(1)], with
      {#B4.161} polarised form (iη/2)(⟨[A′, A₁], 𝐇(1)A⟩ + ⟨[A, A₁], 𝐇(1)A′⟩) (the srt coefficient of
      {#B4.162} W(e^{iη(sA+rA′)}e^{itηA₁})).
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
    {#B4.174-1} RG1 p.267 l.26 writes it as LQ̃B′ + C̃(B′), so the linear operator Q̃ is L^{−1} times the linear part of f,
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
    {#B4.187} For RG1 (0.12), whose linear part at 1 is the same (READINGS.md R47, run 105), the coefficient is the same.
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
    {#B4.194-1} None of this uses R50.
  - {#B4.195} The U-derivative of X(U, j) also needs those of H and G′: Δ′_π contains λ_A = G′RD*A, and Δ^{(2)}_π contains H
    {#B4.196} through (3.134) and G′ through (3.135).
    {#B4.196-1} R50 covers 𝒞(1) = C^{(k)}(1), whose gauge-fixing term is exponential,
    {#B4.197} and the U-derivatives at 1 of PBG's operators H, G′, and R (the projection onto ΔN(Q′), not the transports).
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
  {#B4.211-1} Put M := h + DRD* + aQ*Q, G_M := M^{−1} = G₁(U, 0), and S := QG_MQ* at j = 0, so the minimum in
  {#B4.212} (b) is ⟨B′, S^{−1}B′⟩ and H_h = G_MQ*S^{−1}.
  {#B4.212-1} G_M is not §7's G away from U = 1, but G_M(1) = G(1), since K and Δ′_π
  {#B4.213} are linear in J and J(1) = 0.
  {#B4.213-1} Since Q = Q(U), the constraint QA = B′ moves with U. All derivatives below are at
  {#B4.214} U = 1 in the direction A₁, ∂G_M = −G_M∂M G_M, and ∂M contains a(∂Q*Q + Q*∂Q).
  - {#B4.215} ∂𝒞 = −𝒞(∂(𝒫*Δ^{(k)}(·, 0)𝒫))𝒞.
  - {#B4.216} ∂⟨B′, Δ^{(k)}(·, 0)B′⟩ = ⟨H(1)B′, ∂M H(1)B′⟩ − 2⟨S^{−1}B′, ∂Q H(1)B′⟩ + ∂𝐆^{(2)}(B′), from
    {#B4.217} ∂S^{−1} = −S^{−1}(∂Q G_MQ* + QG_M∂Q* − QG_M∂MG_MQ*)S^{−1}.
  - {#B4.218} ∂H_h = −C_G∂M H(1) + C_G∂Q*S^{−1} − H(1)∂Q H(1), using C_G = G_M − G_MQ*S^{−1}QG_M at U = 1.
  - {#B4.219} Here ∂_Uh(1)[A₁] = ∂𝐇(1)[A₁] − K(1, 𝐇(1)A₁), whose K-part has singular degree ≤ 1 and is counted below.
    {#B4.219-1} The other
    {#B4.220} parts, including the ∂Q terms (S^{−1} = (QGQ*)^{−1} decays exponentially, PBG (3.132)), are regular.
- {#B4.221} *Singular factors (N).* These are diagonal in the aliases: Π_D of degree 0, φ = (∂ᵀ∂)^{−1}∂ᵀ and ∂(∂ᵀ∂)^{−1} of
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
- {#B4.230} By Lemma 4.3, with M depending only on d, L, and PBG's constants: ‖τ(p) − τ(0)‖ ≤ C|p| for |p| ≤ π, and
  {#B4.231} ‖τ(p)‖, ‖R̃(p)‖ ≤ C for all p.

{#B4.232} *(e) Pure gauge.* For B = D̄ω, the minimum of ‖∂A‖² on {Q̃_{k+1}A = D̄ω} is 0, attained at a gradient (QD = D̄P,
{#B4.233} §3.1).
{#B4.233-1} So A₁ has zero curvature, hence is a gradient for p ≠ 0, Θ₁B = 0 by (c), and τ(p)v(p) = 0 for p ≠ 0; at p = 0,
{#B4.234} v(0) = 0.

{#B4.235} *(f) Conclusion.* τ is 2πℤ⁴-periodic and bounded, so ‖τ(p) − τ(0)‖ ≤ C|p| holds for all p. By (e) and Lemma 4.1(b)
{#B4.236} with γ = 1, ‖τ(p)‖ ≤ C|p|.
{#B4.236-1} By (c), ‖Π_J^{(k)}(p)‖ ≤ C|p|·C|p|² + C|p|⁴ ≤ C|p|³ for |p| ≤ π, and
{#B4.237} ‖Π_J^{(k)}(p)‖ ≤ C for all p. Since |p|³ ≤ π^{1−2α}|p|^{2+2α} for |p| ≤ π and 1 ≤ π^{−2−2α}|p|^{2+2α} for |p| ≥ π, the
{#B4.238} bound by C_α|p|^{2+2α} follows.
{#B4.238-1} The Lean core is `BalabanFormal.jterm_holder` with γ = 2α.
{#B4.238-2} Its hypothesis
{#B4.239} ‖Δ(p)‖ ≤ MΔ|p|² is the bound of (c), its hypothesis ‖τ(p) − τ(0)‖ ≤ Mτ|p|^{2α} follows from the Lipschitz bound and
{#B4.240} the boundedness of τ, and its hypothesis on Π_J is the last bullet of (c).
{#B4.240-1} The marginal coefficient is
{#B4.241} determined by the O(|p|²) part (RG1 (1.22)). ∎

## 5. The k-Step Total, and the J-Terms Seen from the Top {#BS5}

{#B5.1} **Conventions.**
- {#B5.2} Top units: T^{(k)} is the unit lattice, and the bare spacing is η_k = L^{−k}.
- {#B5.3} For a functional 𝔉 of the top field B, write 𝔉(e^{iB}) = 𝔉(1) + ½⟨B, Π_𝔉 B⟩ + O(B³), and call Π_𝔉(p) its
  {#B5.4} polarisation symbol.
- {#B5.5} A(U_k(e^{iB})) = ½⟨B, Δ_k B⟩ + O(B³).
  {#B5.5-1} Here Δ_k is Bałaban's coarse operator (PRT1 (1.65)–(1.67)): its symbol is
  {#B5.6} analytic, it annihilates pure gauge, and γ_0|∂̂B|² ≤ ⟨B, Δ_k B⟩ ≤ γ_1|∂̂B|² with γ_0, γ_1 depending only on d.
- {#B5.7} **𝔅_r**: the complex ball of top fields with sup|B| ≤ r and sup|∂̄B| ≤ r (top units).
- {#B5.8} **Analyticity of the background.** For r small, U_k(e^{iB}) with B ∈ 𝔅_r lies in the complex regularity spaces
  {#B5.9} U_j^c(X, α_0, α_1) of RG1 (1.11)–(1.16), for every j ≤ k (VAR Thm 1, §G and (181); RG1 p.263).
  {#B5.9-1} So every functional
  {#B5.10} below that Bałaban proves analytic on those spaces is analytic in B ∈ 𝔅_r.
- {#B5.11} **Cauchy estimate.** Let 𝔉(B) be analytic on 𝔅_r, translation-covariant, and bounded by M per top unit cube.
  {#B5.11-1} Then its
  {#B5.12} polarisation symbol satisfies ‖Π_𝔉(p)‖ ≤ 2(1+π)²M/r² for all p. (A plane wave of momentum p and unit amplitude has
  {#B5.13} 𝔅-norm at most 1+π.) It is applied to the localized terms of RG1 (0.29).

{#B5.14} **Proposition 5.1 (Total).** Let ℒ_k(B) := Σ_{j=1}^{k} E^{(j)}(0, U_k(e^{iB})), the zero-coupling step terms of
{#B5.15} RG1 (1.6) evaluated at the top background, i.e. the k-step Gaussian.
{#B5.15-1} Then (RG1 (0.28)–(0.30); proof below)
  {#B5.16} Π_{ℒ_k}(p) = Φ_k Δ_k(p) + E_k(p),  Φ_k := Σ_{j=1}^{k} b_j,  sup_p ‖E_k(p)‖ ≤ C,
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
  {#B5.26} Σ_{l} |(dH_k)^∧(p + l)| · |p + l|^α ≤ C,
{#B5.27} where the sum runs over the aliases p + l of p in the fine Brillouin zone, (dH_k)^∧ is the symbol of B ↦ d(H_kB), α ∈
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
     {#B5.54} Σ_λ ∂̄¹_λ(p)(Δ₀(p)φ_λ(p))^{−1}B̂_λ(p).
     {#B5.54-1} The first sum of the bracket, extended to all l′, is Δ₀(p)²φ_μ(p)Δ(q)^{−1} ≤
     {#B5.55} c₁Δ₀(p)Δ(q)^{−1}; the second, extended to all l′, is |v_μ(q)|²N(p).
     {#B5.55-1} Since Σ_ν|∂¹_ν(p)|²/(Δ₀(p)²φ_ν(p)) ≥
     {#B5.56} Δ₀(p)/(c₁Δ₀(p)) = 1/c₁ and Σ_λ|∂¹_λ(p)|(Δ₀(p)φ_λ(p))^{−1} ≤ √d|∂¹(p)|/c₀, |b(p)| ≤ (c₁√d/c₀)|∂¹(p)||B̂(p)|.
     {#B5.56-1} So
       {#B5.57} |T₂| ≤ (c₁√d/c₀²)|∂_μ(q)||u(q)|Δ(q)^{−1}[c₁Δ₀(p)/(c_NΔ(q)) + |v_μ(q)|²]|∂¹(p)||B̂(p)|.
3. {#B5.58} *The term l = 0.* Here q = p, and by step 1 the factors Δ₀(p)/Δ(p), |∂_μ(p)||∂¹(p)|/Δ(p), and |v_μ(p)| are bounded
   {#B5.59} by constants depending on d.
   {#B5.59-1} So |(H_kB)^∧(p)| ≤ C₁|B̂(p)|, and |(dH_k)^∧(p)||p|^α ≤ 2|∂(p)|C₁|p|^α ≤ C₂, with
   {#B5.60} |p| ≤ π√d.
4. {#B5.61} *The terms l ≠ 0.* Here |q| ≥ π.
   {#B5.61-1} By step 1, |T₁| ≤ C|u(q)||q|^{−2}; in T₂, |∂_μ(q)|Δ(q)^{−2} ≤ C|q|^{−3} and
   {#B5.62} |∂_μ(q)||v_μ(q)|² ≤ π, so |T₂| ≤ C|u(q)||q|^{−2}, all times |B̂(p)|. The curvature (d_ηA)_{μν} has the symbol
   {#B5.63} ∂_μ(q)Â_ν(q) − ∂_ν(q)Â_μ(q), so |(dH_k)^∧(q)| ≤ 2|q|max_μ|(H_kB)^∧_μ(q)|/|B̂(p)| ≤ C|u(q)||q|^{−1}, and
     {#B5.64} Σ_{l≠0}|(dH_k)^∧(q)||q|^α ≤ C Σ_{l≠0}|q|^{α−1}|u(q)| ≤ C′ Σ_{l≠0}|l|^{α−1}∏_μ(1 + |l_μ|)^{−1}.
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
   {#B5.78} part of V*(B) is Q_mH_kB up to a level-m field of zero curvature (*Zero-curvature terms* below).
   {#B5.78-1} J^{(j)} ∘ U_m has
   {#B5.79} zero first-order coefficient at the trivial background (Proposition 4.2(c)).
   {#B5.79-1} So the top polarisation of
   {#B5.80} J^{(j)}(U_k(e^{iB})) is ⟨V_1, Π_J^{(j)} V_1⟩ with V_1 := Q_m H_k B. Here Π_J^{(j)} is the level-m symbol of
   {#B5.81} Proposition 4.2, for the step J-term J^{(j)} of §3.3: for a fixed
   {#B5.82} α ∈ (0, ½), ‖Π_J^{(j)}(p′)‖ ≤ C_α|p′|^{2+2α} on the whole level-m zone, and it is transverse
   {#B5.83} (Π_J^{(j)}(p′)v(p′) = 0, since Δ_{m}(p′)v(p′) = 0 and τ(p′)v(p′) = 0 in Proposition 4.2(c), (e)).

   {#B5.84} *Zero-curvature terms.* In step 4's normalisation the level-m bond logarithm carries the factor Mη = L^{m−k}, which
   {#B5.85} step 2 accounts for, so the first-order part of V*(B) reads i(Mη)Q_mH_kB.
   {#B5.85-1} It equals this only up to a level-m field
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
     {#B5.99} of the Wilson action (RG1 p.252) is a positive multiple c of ‖d_ηX‖², with U = e^{iηX}.
     {#B5.99-1} Minimality gives
     {#B5.100} ct²‖d_ηA_1‖² + O(t³) ≤ ct²‖d_ηA‖² + O(t³); divide by t² and let t → 0.
   - {#B5.101} The sets {d_ηA : Q̃_kA = B} and {d_ηA : Q_kA = B} coincide.
     {#B5.101-1} A gauge transformation A ↦ A − ∂^ηλ changes Q_kA by
     {#B5.102} −∂Q′_kλ (PRT1 (1.20), p.20).
     {#B5.102-1} By the gauge covariance of RG1 (0.4), it changes Q̃_kA by the gradient of −λ on
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
3. {#B5.118} *Transversality.* On transverse modes |q|²|V̂_1|² ≤ C|(d̄V_1)^∧|², and only transverse modes contribute (step 1).
   {#B5.118-1} So
     {#B5.119} |⟨V_1, Π_J^{(j)} V_1⟩| ≤ C L^{−2α(k−m)} Σ_q |q|^{2α} |(d̄V_1)^∧(q)|²
   {#B5.120} (hypothesis `hunits` of `BalabanFormal.jterm_assembly`).
4. {#B5.121} *Alias summability.* Set M := L^m = 2h + 1 and η := L^{−k}.
   {#B5.121-1} In top units the fine lattice has spacing η and the
   {#B5.122} level-m lattice has spacing Mη = L^{m−k}.
   {#B5.122-1} Fields are in physical normalisation: a bond of length ε carries the
   {#B5.123} logarithm εA_μ.
   {#B5.123-1} The lattice curl at spacing ε is (d_εA)_{μν}(x) := ε^{−1}(A_ν(x + εe_μ) − A_ν(x) − A_μ(x + εe_ν) +
   {#B5.124} A_μ(x)), and d̄V_1 means d_{Mη}V_1.

   {#B5.125} *The first-order level-m average.* The chain averages with RG1 (0.4), p.253 (READINGS.md R47).
   {#B5.125-1} Its m-th order average
   {#B5.126} is the m-fold iterate of the one-step average by construction: each step's kernel is the one-step
   {#B5.127} δ(Ū(c)V^{−1}(c)) (RG1 (0.17), (0.19), p.255).
   {#B5.127-1} At U = 1, on a coarse bond c with c₊ = c₋ + Le_μ, the first-order part
   {#B5.128} of the logarithm in RG1 (0.4) is

     {#B5.129} Σ_{x∈B(c₋)} L^{−d} A([x, x′]) + ω(c₋) − ω(c₊),  ω(y) := Σ_{x∈B(y)} L^{−d} |G(y, x)|^{−1} Σ_{Γ∈G(y,x)} A(Γ),

   {#B5.130} with A(Γ) the sum of the bond logarithms along Γ.
   {#B5.130-1} Indeed, the loop logarithm is A(Γ) + A([x, x′]) − A(Γ′) − A(c) to
   {#B5.131} first order, the term −A(c) cancels against the factor U(c), and the contour families at c₊ are the translates by c of
   {#B5.132} those at c₋.
   {#B5.132-1} This is L times PRT1 (1.8), p.19 (PRT1 normalises per unit coarse length), with the single contour
   {#B5.133} replaced by the average over G(y, x).
   {#B5.133-1} Its first term is L times PRT1's straight average PRT1 (1.11), and its endpoint
   {#B5.134} terms form a coarse gradient.

   {#B5.135} A straight average of a gradient is the gradient of the block means, so later averaging steps carry gradients to
   {#B5.136} gradients.
   {#B5.136-1} The composition of m straight averages over centred blocks is the straight average over the centred block
   {#B5.137} of side M. PRT1 (1.16)–(1.18), p.20, states this for corner blocks ("It is easily seen").
   {#B5.137-1} For corner and centred
   {#B5.138} blocks alike the path offsets sL + t run once over {0, …, L² − 1}, and for centred blocks the offsets Lr + o,
   {#B5.139} with r and o in the centred block of side L, run once over the centred block of side L².
   {#B5.139-1} So the first-order level-m
   {#B5.140} bond logarithm is (Mη)Q_mA plus a level-m gradient, where

     {#B5.141} (Q_mA)_μ(Y) := |B_m|^{−1} Σ_{r∈B_m} M^{−1} Σ_{t=0}^{M−1} A_μ(η(MY + r + te_μ)),  B_m := {−h, …, h}⁴.

   {#B5.142} The gradient has zero curl, and Π_J^{(j)} is transverse (step 1), so the gradient drops out of ⟨V_1, Π_J^{(j)}V_1⟩.
   {#B5.143} RG1's blocks are centred at the coarse points (RG1 p.252), and PRT1's blocks need not be.
   {#B5.143-1} A translation of the blocks
   {#B5.144} multiplies every Fourier coefficient by a unit phase, so none of the absolute values below changes.

   {#B5.145} *The curvature identity.* The curl of a straight-path average is the sum of the fine plaquettes in the M × M square
   {#B5.146} that the path sweeps out (discrete Stokes).
   {#B5.146-1} Hence d_{Mη}Q_mA = P_m d_ηA, where

     {#B5.147} (P_mF)_{μν}(Y) := |B_m|^{−1} M^{−2} Σ_{r∈B_m} Σ_{a,b=0}^{M−1} F_{μν}(η(MY + r + ae_μ + be_ν)).

   {#B5.148} The weights of P_m are nonnegative and sum to one, as the weights η^{d+1} of PRT1 (1.18), p.20, do for Q_k.
   {#B5.148-1} On a fine
   {#B5.149} plane wave of momentum p, P_m therefore acts as a symbol σ_m(p) with |σ_m(p)| ≤ 1, times the level-m character of p.

   {#B5.150} *Folding.* At U = 1, for the top input B̂(p)e^{ip·Y}, the fine field H_kB is a finite sum of plane waves with momenta
   {#B5.151} p_a = p + 2πl_a in the fine zone (PRT1 (1.63)).
   {#B5.151-1} Write ĉ_{μν}(a) for the coefficient of (d_ηH_kB)_{μν} at p_a.
   {#B5.151-2} Subtract
   {#B5.152} from each component of p_a a multiple of 2π/(Mη) to land in (−π/(Mη), π/(Mη)]; call the result q(a).
   {#B5.152-1} On the level-m
   {#B5.153} lattice p_a and q(a) have the same character, and |q(a)| ≤ |p_a| in the Euclidean norm.
   {#B5.153-1} Distinct representatives give
   {#B5.154} distinct characters, so the Fourier coefficient of (d̄V_1)_{μν} at q is Σ_{a: q(a)=q} σ_m(p_a)ĉ_{μν}(a).
   {#B5.154-1} Hence, with
   {#B5.155} the last step from Lemma 5.2,
     {#B5.156} Σ_q |q|^{2α}‖(d̄V_1)^∧_{μν}(q)‖² ≤ Σ_q (Σ_{a: q(a)=q} |p_a|^α‖ĉ_{μν}(a)‖)² ≤ (Σ_a |p_a|^α‖ĉ_{μν}(a)‖)² ≤ C_H²‖B̂(p)‖².

   {#B5.157} Here C_H ≤ C, with C = C(d, α) from Lemma 5.2, which bounds the curvature symbol (dH_k)^∧ itself.
   {#B5.157-1} The
   {#B5.158} norms are the invariant norms on the Lie algebra: at U = 1, H_k acts on every Lie-algebra component in the same way.

   {#B5.159} Summing over the six planes μ < ν gives, by Lemma 5.2,
     {#B5.160} Σ_q |q|^{2α}‖(d̄V_1)^∧(q)‖² ≤ 6C_H²‖B̂(p)‖²,
   {#B5.161} uniformly in k and m, which is the bound step 3 needs.
5. {#B5.162} *Sum.* Σ_{m≤k} L^{−2α(k−m)} ≤ (1 − L^{−2α})^{−1} (`BalabanFormal.jterm_assembly`). ∎

## 6. The Bare-Lattice One-Loop Polarisation {#BS6}

{#B6.1} **Notation.** Lattice units (bare spacing 1), momenta ξ, k ∈ T⁴ = [−π, π]⁴, s(k) := Σ_μ 4 sin²(k_μ/2) = |k|² + O(|k|⁴).

### 6.1 The Infrared Lemma {#BS6.1}

{#B6.1.1} **Lemma 6.1.** Let N(k, ξ) be a matrix-valued trigonometric polynomial with N(−k, −ξ) = N(k, ξ).
{#B6.1.1-1} Write N = N_2 + N_r,
{#B6.1.2} where N_2 is a homogeneous polynomial of degree 2 in (k, ξ) and |N_r| ≤ C(|k| + |ξ|)³ near 0 (`SmoothNum.lemma61`).
{#B6.1.2-1} Set
  {#B6.1.3} I(ξ) := ∫_{T⁴} N(k, ξ) / (s(k) s(k+ξ)) d⁴k/(2π)⁴.
{#B6.1.4} Then, as ξ → 0,
  {#B6.1.5} I(ξ) = a_0 + a_1·ξ + Σ(ξ) ln(1/|ξ|) + O(|ξ|²),  Σ(ξ) := (2π)^{−4} ∫_{S³} f_2(ω, ξ) dσ(ω),
{#B6.1.6} where f_2(u, ξ) is the part quadratic in ξ of the Taylor expansion of f(u, ξ) := N_2(u, ξ)/(|u|²|u+ξ|²) at ξ = 0.
{#B6.1.7} Single-propagator integrals ∫ M(k, ξ)/s(k) with M trigonometric are C^∞ in ξ.
{#B6.1.7-1} In fact a_0 = I(0) and a_1 = 0.

{#B6.1.8} The type-checked Lean core `SmoothNum.lemma61` covers steps 0–4 below, for scalar N that is C³, even and zero at 0,
{#B6.1.9} with the bounds of step 0 derived rather than assumed.
{#B6.1.9-1} The hypotheses hold for N(k, ξ) = Σ_μ sin k_μ sin(k_μ + ξ_μ).

{#B6.1.10} *Proof.* Let G(k, ξ) := N(k, ξ)/(s(k)s(k+ξ)) and Δ²G(k) := G(k, ξ) + G(k, −ξ) − 2G(k, 0).
{#B6.1.10-1} The substitution k ↦ −k,
{#B6.1.11} with the parity of N and of s, gives I(−ξ) = I(ξ).
{#B6.1.11-1} Hence a_1 = 0 and
  {#B6.1.12} I(ξ) − I(0) = ½ ∫_{T⁴} Δ²G(k) d⁴k/(2π)⁴.

{#B6.1.13} No integral is Taylor-expanded: the order-0 and order-1 parts of the integrand cancel in Δ² identically.
{#B6.1.13-1} Take
{#B6.1.14} 0 < |ξ| ≤ π/16.
{#B6.1.14-1} Work entrywise, so N is scalar, and use the norm |(k, ξ)| := max(|k|, |ξ|) on ℝ⁴ × ℝ⁴
{#B6.1.15} (`SmoothNum.lemma61`).
0. {#B6.1.16} *Bounds on N.* Only three properties of N are used: N is C³, N is even, and N(0, 0) = 0.
   - {#B6.1.17} Evenness gives DN(0) = 0, so the Taylor polynomial forces N_2 = ½D²N(0).
   - {#B6.1.18} Let M bound |D²N| and |D³N| on the ball |q| ≤ 2π + 1.
     {#B6.1.18-1} This ball contains every (k, ξ) with k ∈ [−π, π]⁴ and
     {#B6.1.19} |ξ| ≤ π/8.
   - {#B6.1.20} The mean-value theorem on the ball of radius |q|, applied in turn to DN, N, D²N_r, DN_r and N_r (each vanishes
     {#B6.1.21} at 0), gives |DN(q)| ≤ M|q|, |N(q)| ≤ M|q|², and |DᵗN_r(q)| ≤ M|q|^{3−t} for t = 0, 1, 2.
   - {#B6.1.22} For F ∈ {N, N_r}, the mean-value theorem along v ↦ (k, v), |v| ≤ |ξ|, gives
     {#B6.1.23} |F(k, ξ) − F(k, 0)| ≤ |ξ| sup|DF|. Applied to v ↦ F(k, v) − DF(k, 0)(0, v), it gives
     {#B6.1.24} |Δ²F| ≤ 2|ξ|² sup|D²F|; the linear terms cancel in Δ².
   - {#B6.1.25} If |ξ| ≤ |k|/2, every point of the segment has norm |k|.
     {#B6.1.25-1} Hence N ∈ DC(2) and N_r ∈ DC(3) on
     {#B6.1.26} {0 < |k| ≤ π/2, |ξ| ≤ |k|/2}, with constant 2M.
   - {#B6.1.27} On the outer region (k ∈ [−π, π]⁴, |k| ≥ π/2, |ξ| ≤ π/8), the same estimates with |k| ≤ 2π + 1 give N ∈ DC(0),
     {#B6.1.28} with constant 2M(2π + 1)².
     {#B6.1.28-1} Also |N(k, ξ)| ≤ M|(k, ξ)|² ≤ M(|k| + |ξ|)².
1. {#B6.1.29} *Second-difference calculus.* On {0 < |k| ≤ R, |ξ| ≤ |k|/2}, say F ∈ DC(m) if
   - {#B6.1.30} |F| ≤ C|k|^m,
   - {#B6.1.31} |F(k, ξ) − F(k, 0)| ≤ C|ξ||k|^{m−1},
   - {#B6.1.32} |Δ²F| ≤ C|ξ|²|k|^{m−2}.

   {#B6.1.33} The class DC is stable under the following operations (`SmoothNum.lemma61`):
   - {#B6.1.34} sums;
   - {#B6.1.35} products, by Δ²(FG) = Δ²F·G₀ + F₀·Δ²G + Δ⁺FΔ⁺G + Δ⁻FΔ⁻G;
   - {#B6.1.36} reciprocals of functions with |F| ≥ c|k|^m, by 1/a + 1/b − 2/z = (−z(a+b−2z) − 2(a−z)(b−z))/(abz).

   {#B6.1.37} On bounded regions DC(m) ⊂ DC(m′) for m′ ≤ m.
   {#B6.1.37-1} Elementary trigonometry gives |k+ξ|² ∈ DC(2), s(k+ξ) ∈ DC(2) and
   {#B6.1.38} q(k+ξ) := |k+ξ|² − s(k+ξ) ∈ DC(4) (`SmoothNum.lemma61`).
   {#B6.1.38-1} The ingredients are:
   - {#B6.1.39} cos(k ± ξ) = cos k cos ξ ∓ sin k sin ξ;
   - {#B6.1.40} |x − sin x| ≤ 2|x|³;
   - {#B6.1.41} |2 − 2cos y − y²| ≤ 5y⁴.

   {#B6.1.42} Also s(p) ≥ (36/25π²)|p|² when all |p_μ| ≤ 5π/4.
   {#B6.1.42-1} So h(p) := 1/s(p) − 1/|p|² = q/(s|p|²) satisfies h(k+ξ) ∈ DC(0)
   {#B6.1.43} (`SmoothNum.lemma61`).
2. {#B6.1.44} *Outer region* |k| ≥ π/2.
   {#B6.1.44-1} Here G = N·s(k)^{−1}·s(k+ξ)^{−1} ∈ DC(−4), so |Δ²G| ≤ C|ξ|².
   {#B6.1.44-2} The region contributes
   {#B6.1.45} O(|ξ|²) (`SmoothNum.lemma61`).
3. {#B6.1.46} *Inner ball* |k| < 2|ξ|.
   {#B6.1.46-1} From |N| ≤ C(|k|+|ξ|)² and s ≥ c|·|²,
   {#B6.1.47} |G(k, η)| ≤ C(|k|^{−2} + |k+η|^{−2}) for η ∈ {ξ, −ξ, 0}. Since ∫_{|k|<r}|k|^{−2} d⁴k = 2|B₁|r², the region
   {#B6.1.48} contributes O(|ξ|²) (`SmoothNum.lemma61`).
4. {#B6.1.49} *Annulus* 2|ξ| < |k| < π/2.
   {#B6.1.49-1} Exactly,
     {#B6.1.50} G = f + F_r,  F_r = N_r/(|k|²|k+ξ|²) + N[h(k)/|k+ξ|² + h(k+ξ)/|k|² + h(k)h(k+ξ)].
   - {#B6.1.51} By step 1, F_r ∈ DC(−1), so |Δ²F_r| ≤ C|ξ|²|k|^{−3}.
     {#B6.1.51-1} Also ∫_{2|ξ|<|k|<π/2}|k|^{−3} d⁴k ≤ 2π|B₁|
     {#B6.1.52} (`SmoothNum.lemma61`).
   - {#B6.1.53} For the homogeneous part write a = |k|², u = ⟨k, ξ⟩, c = |ξ|² and N_2 = p₀ + p₁ + p₂, with p₀ = A(k, k),
     {#B6.1.54} p₁ = B(k, ξ), p₂ = Γ(ξ, ξ) bilinear in their arguments.
     {#B6.1.54-1} Then
       {#B6.1.55} f_2 = p₂/a² − 2p₁u/a³ − p₀c/a³ + 4p₀u²/a⁴,
     {#B6.1.56} and the exact identity
       {#B6.1.57} Δ²f − 2f_2 = 2[p₀(a²c² + ac³ − 12acu² − 4c²u² + 16u⁴) + 2p₁ua(2ac + c² − 4u²) + p₂(−a³c − a²c² + 4a²u²)]
                    {#B6.1.58} / (a⁴|k+ξ|²|k−ξ|²)
     {#B6.1.59} gives |Δ²f − 2f_2| ≤ C|ξ|⁴|k|^{−6} (`SmoothNum.lemma61`).
     {#B6.1.59-1} Its integral over the annulus is O(|ξ|²).
   - {#B6.1.60} f_2(·, ξ) is homogeneous of degree −4.
     {#B6.1.60-1} In polar coordinates,
     {#B6.1.61} ∫_{2|ξ|<|k|<π/2} f_2 = ln(π/(4|ξ|)) ∫_{S³} f_2(ω, ξ) dσ(ω), and Σ(ξ) = O(|ξ|²).

   {#B6.1.62} Adding the three regions gives I(ξ) − I(0) = Σ(ξ) ln(1/|ξ|) + O(|ξ|²).
5. {#B6.1.63} *Single-propagator integrals.* 1/s is integrable and M is smooth in ξ. ∎

### 6.2 Application to the Bare Lattice Functional {#BS6.2}

{#B6.2.1} Let B_tb(U) := −½ log det(Hess A(U) + D_UD_Uᵀ) + log det(D_UᵀD_U).
{#B6.2.1-1} This is the lattice background-field one-loop
{#B6.2.2} functional in Feynman gauge, with the Wilson action and normalised trace.
{#B6.2.2-1} It is gauge-invariant, because the
{#B6.2.3} coordinates X ↦ Ue^{iX} transform linearly under gauge transformations, so the Hessian is covariant even off-shell.
{#B6.2.4} Its polarisation symbol Ψ_tb(ξ) in the direction of a fine background b is a finite sum of:
- {#B6.2.5} bubbles ∫ tr[V^{(1)} G V^{(1)} G], whose numerators are of the type in Lemma 6.1;
- {#B6.2.6} tadpoles ∫ tr[V^{(2)} G].

{#B6.2.7} Here G = s(k)^{−1}·1, because Hess A(1) + ddᵀ = −Δ_lat componentwise.
{#B6.2.7-1} V^{(1)} and V^{(2)} are the first- and
{#B6.2.8} second-order background vertices of Hess A + DDᵀ and of the ghost operator DᵀD.

{#B6.2.9} **Lemma 6.2 (Naive Continuum Limit).** The vertices are trigonometric polynomials in (k, ξ), odd and even respectively
{#B6.2.10} under (k, ξ, b) ↦ (−k, −ξ, b).
{#B6.2.10-1} The lowest-order Taylor parts of V^{(1)} are linear in (k, ξ), and they are the
{#B6.2.11} continuum background-field vertices of −D_b²·1 − 2 ad F_b (vector) and −D_b² (ghost).

{#B6.2.12} *Proof.* Taylor expansion of 1 − Re tr e^{iX_p}: it equals ½ tr X_p² + O(X_p⁴).
{#B6.2.12-1} For U = e^{i(b + X)}, the plaquette
{#B6.2.13} variable is X_p = (lattice curl of b + X) + ½[·,·] + (terms of higher order in the lattice spacing).
{#B6.2.13-1} At quadratic order
{#B6.2.14} in X and to the lowest order in momenta, this reproduces the continuum form ½⟨X, (−D_b² − 2 ad F_b)X⟩ after adding the
{#B6.2.15} Feynman term |D_bᵀX|².
{#B6.2.15-1} D_UᵀD_U is the lattice covariant Laplacian, whose lowest-order part is −D_b².

{#B6.2.16} B_tb uses the coordinates X ↦ U_be^{iX} rather than e^{i(b+X)}.
{#B6.2.16-1} The two differ by X′ = X + ½[b, X] + O(b²X, bX²).
- {#B6.2.17} The linear change S = 1 + ½ ad b turns Hess A into SᵀHess A S. At first order in b this adds ½(M(k+ξ) − M(k)) ad b̂,
  {#B6.2.18} where M is the symbol of Hess A(1); it vanishes to second order at 0, so the added term has degree at least two in
  {#B6.2.19} (k, ξ).
- {#B6.2.20} The term ⟨∇A(b), ∂²X′(X, X)⟩ is of second order in b and contains no differences of X, so it is a tadpole.

{#B6.2.21} Neither changes the linear parts of V^{(1)}. ∎

{#B6.2.22} Hence each bubble numerator N = tr[V^{(1)} V^{(1)}] satisfies the hypotheses of Lemma 6.1: it is a trigonometric
{#B6.2.23} polynomial, even, and zero at 0.
{#B6.2.23-1} Its N_2 is the product of the linear parts of the two vertices, which is the numerator
{#B6.2.24} of the continuum Feynman-gauge background-field bubble.
{#B6.2.24-1} The tadpoles have one propagator, so by the last part of
{#B6.2.25} Lemma 6.1 they are C^∞ in ξ and carry no logarithm.
{#B6.2.25-1} The logarithm in Ψ_tb is therefore fixed by the continuum vertices.

{#B6.2.26} **Lemma 6.5 (Angular Coefficient).** Fix a background mode b̂_μ(ξ) ∈ g ⊗ ℂ.
{#B6.2.26-1} Put ⟨X, Y⟩ := −tr(XY), which is positive
{#B6.2.27} definite on g, and B_μν(ξ) := ⟨conj b̂_μ(ξ), b̂_ν(ξ)⟩.
{#B6.2.27-1} The second-order term of B_tb in this mode has logarithmic part

  {#B6.2.28} c ln(1/|ξ|²) · ½(|ξ|²δ_μν − ξ_μξ_ν) B_μν(ξ),  **c = (11/48π²) κ,**

{#B6.2.29} up to the factor |Λ|^{−1} common to all modes.
{#B6.2.29-1} The same mode of the quadratic part of the Wilson action A is
{#B6.2.30} ½(|ξ̂|²δ − ξ̂ξ̂)B.
{#B6.2.30-1} Hence Σ_tot(ξ) ln(1/|ξ|) = c ln(1/|ξ|²)(|ξ|²δ − ξξ), and c > 0.

{#B6.2.31} *Proof.* By Lemma 1.1, tr_g(ad X ad Y) = K(X, Y) = −κ⟨X, Y⟩ on g, extended bilinearly to g ⊗ ℂ.
{#B6.2.31-1} Since b is real,
{#B6.2.32} b̂(−ξ) = conj b̂(ξ).
{#B6.2.32-1} Multiplication by b has plane-wave matrix elements |Λ|^{−1}b̂(k′ − k).
1. {#B6.2.33} *Expansion.* If Δ = Δ⁰ + V¹ + V² + O(b³) and G = (Δ⁰)^{−1}, then
   {#B6.2.34} log det Δ = log det Δ⁰ + Tr GV¹ + Tr GV² − ½Tr(GV¹GV¹) + O(b³).
   {#B6.2.35} Tr GV² is a tadpole.
   {#B6.2.35-1} So the logarithmic part of the second-order term of B_tb = −½ log det Δ₁ + log det Δ₀ is that of
   {#B6.2.36} ¼Tr(GV₁¹GV₁¹) − ½Tr(GV₀¹GV₀¹).
2. {#B6.2.37} *Continuum vertices.* At A = b + X, the part of ¼∫|F_μν|² quadratic in X, plus the Feynman term ½∫|D_μX_μ|², is
   {#B6.2.38} ½⟨X, Δ₁X⟩ with Δ₁ = −D² − 2 ad F and (ad F X)_ν := [F_νμ, X_μ].
   {#B6.2.38-1} This follows by integration by parts from
   {#B6.2.39} [D_μ, D_ν] = ad F_μν and ⟨F, [X_μ, X_ν]⟩ = ⟨[F, X_μ], X_ν⟩.
   {#B6.2.39-1} The ghost operator is Δ₀ = −D².
   {#B6.2.39-2} The parts linear in b
   {#B6.2.40} have matrix elements, with ξ = k′ − k and b̂ = b̂(ξ):
   - {#B6.2.41} convective, −i(k + k′)_μ ad b̂_μ/|Λ|, on each of the four components for Δ₁;
   - {#B6.2.42} magnetic (Δ₁ only), W_νμ = −2i ad(ξ_νb̂_μ − ξ_μb̂_ν)/|Λ|.
3. {#B6.2.43} *Traces.* Put k′ = k + ξ.
   {#B6.2.43-1} Each trace below is κ|Λ|^{−1}Σ_ξ times a lattice bubble ∫N/(s(k)s(k+ξ)) d⁴k/(2π)⁴, whose
   {#B6.2.44} N_2 is the continuum numerator listed.
   - {#B6.2.45} Ghost: N_2 = (2k+ξ)_μ(2k+ξ)_ν B_μν.
     {#B6.2.45-1} The sign: (−i)²K(b̂_μ(−ξ), b̂_ν(ξ)) = κB_μν.
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

   {#B6.2.55} With u = ⟨ω, ξ⟩ and c₀ = |ξ|²:
   - {#B6.2.56} convective: f_2 = ξ_μξ_ν − 4u(ω_μξ_ν + ξ_μω_ν) − 4c₀ω_μω_ν + 16u²ω_μω_ν, so
     {#B6.2.57} ⟨f_2⟩ = ξξ − 2ξξ − c₀δ + ⅔(c₀δ + 2ξξ) = −⅓(|ξ|²δ − ξξ);
   - {#B6.2.58} magnetic: N_2 is already quadratic in ξ, so f_2 = N_2/|ω|⁴ and ⟨f_2⟩ = 8(|ξ|²δ − ξξ)B.
5. {#B6.2.59} *Sum.* In units of κ|Λ|^{−1}(1/16π²) ln(1/|ξ|²)(|ξ|²δ − ξξ)B, the logarithmic part is
   {#B6.2.60} ¼[4·(−⅓) + 8] − ½·(−⅓) = 5/3 + 1/6 = 11/6.
   {#B6.2.60-1} This is (11κ/96π²) ln(1/|ξ|²)(|ξ|²δ − ξξ)B, which is
   {#B6.2.61} c ln(1/|ξ|²)·½(|ξ|²δ − ξξ)B. ∎

{#B6.2.62} The type-checked Lean core `BalabanFormal.angular_coefficient` covers steps 4–5: the invariance of the S³ integral under
{#B6.2.63} isometries, the moments, both averages and the constant 11/(48π²).

{#B6.2.64} So the k-step rate 2c ln L per step is (11/24π²)κ ln L, the universal one-loop running.
- {#B6.2.65} *Sign.* c > 0 is asymptotic freedom; it matches RG1 (0.20), because log Z ≈ +b·A.
- {#B6.2.66} *Affine part.* Ψ_tb is transverse (Ψ_tb v = 0) and hypercubic-covariant.
  {#B6.2.66-1} The argument of Lemma 4.1 applied to the
  {#B6.2.67} affine part a_0 + a_1ξ (the logarithmic part is O(|ξ|² ln) and transverse up to O(|ξ|³ ln)) forces a_0 = 0 and
  {#B6.2.68} a_1 = 0.

{#B6.2.69} **Proposition 6.3 (Bare Polarisation).** Let −F_0 be the exact bare functional of §3 (built from h = Π_⊥ Hess A Π_⊥).
{#B6.2.70} Its polarisation symbol is Ψ_0 = d̂*Ψ̃_0 d̂, with d̂ the lattice curl and Ψ̃_0 acting on ran d̂.
{#B6.2.70-1} Let c = (11/48π²)κ
{#B6.2.71} (Lemma 6.5).
{#B6.2.71-1} Then

  {#B6.2.72} Ψ̃_0(ξ) = c ln(1/|ξ|²)·1 + R_0(ξ),  sup_{ξ ∈ T⁴∖0} ‖R_0(ξ)‖ < ∞.

{#B6.2.73} *Proof.*
{#B6.2.74} Write H := Hess A(U), D := D_U, Π_D := D(DᵀD)^{−1}Dᵀ, Π := 1 − Π_D, h_⊥ for h on (ran D)^⊥, S := (DᵀD)^{−2}, and
{#B6.2.75} J := ∇A(U).
{#B6.2.75-1} Differentiating ⟨∇A(U), D_Uω⟩ ≡ 0 along U ↦ Ue^{iX} gives HD = 𝒩_U(J).
{#B6.2.75-2} Here 𝒩_U(j) is linear in j, local,
{#B6.2.76} contains no lattice difference, depends on U only through the bond transports, and is gauge-covariant; in PBG's
{#B6.2.77} coordinates it is the T of §7.
{#B6.2.77-1} All operators are restricted to a coset 𝒪 ≠ ℤξ (Remark 3.4).
{#B6.2.77-2} The loop momentum k is that
{#B6.2.78} of the 0-form line, a := |k|, and a′ := |k + ξ|, both taken mod 2π.
{#B6.2.78-1} Factors |b̂| are not written.

1. {#B6.2.79} *One log-determinant.* −F_0 − B_tb = −½[log det(h + DDᵀ) − log det(H + DDᵀ)].
   - {#B6.2.80} In (ran D)^⊥ ⊕ ran D, h + DDᵀ = h_⊥ ⊕ DDᵀ, and H + DDᵀ has the diagonal blocks h_⊥ and Π_DHΠ_D + DDᵀ.
     {#B6.2.80-1} The Schur
     {#B6.2.81} complement of h_⊥ is DDᵀ + Π_DH_SΠ_D, with H_S := H − HΠh_⊥^{−1}ΠH.
   - {#B6.2.82} On ran D, (DDᵀ)^{−1} = DSDᵀ.
     {#B6.2.82-1} By Sylvester's identity det(1 + AB) = det(1 + BA),

       {#B6.2.83} −F_0 − B_tb = ½ log det_Y(1 + S𝒲),  𝒲 := DᵀH_SD = Dᵀ𝒩_U(J) − 𝒩_U(J)ᵀΠh_⊥^{−1}Π𝒩_U(J).

     {#B6.2.84} The second form follows from HD = 𝒩_U(J).
     {#B6.2.84-1} The two forms are one expression, so they have the same integrand.
2. {#B6.2.85} *The integrand.* 𝒲₀ = 0, so the second-order term is ½tr(S𝒲₂) + ½tr(S₁𝒲₁) − ¼tr(S𝒲₁S𝒲₁), with integrand I(k, ξ).
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
   - {#B6.2.95} *J-form.* With J₀ = 0, I = ½tr(SD₀ᵀ𝒩₀(J₂)) + I_lin + I_quad, where
     - {#B6.2.96} I_lin := θ₁(k, ξ)[b̂, Ĵ₁], θ₁ being the first-order part in b at fixed j of the integrand of ½tr(SD_Uᵀ𝒩_U(j));
     - {#B6.2.97} I_quad := −½tr(S𝒩₀(J₁)ᵀΠh_⊥^{−1}Π𝒩₀(J₁)) − ¼tr(SD₀ᵀ𝒩₀(J₁)SD₀ᵀ𝒩₀(J₁)).

     {#B6.2.98} Only the zero-momentum part of J₂ reaches the trace.
     {#B6.2.98-1} For constant j, 𝒩₀(j) = Σ_ν A_ν(j) ⊗ n_ν(k), with A_ν(j) a
     {#B6.2.99} multiple of ad j_ν, and every other factor is scalar on g.
     {#B6.2.99-1} Since tr_g ad = 0, the J₂ term vanishes for every k.
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
     - {#B6.2.116} After tr_g the second kind vanish.
       {#B6.2.116-1} By Leibniz, the first give θ₁(k, 0)[β, j] = Σ_{μν} C_{μν}∂_{k_μ}Φ_ν(k),
       {#B6.2.117} with C_{μν} a fixed multiple of tr_g(ad β_μ A_ν(j)) and Φ_ν(k) := tr[S(k)D₀(k)*n_ν(k)].
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
   {#B6.2.126} ⟨∇F_0(U), D_Uλ⟩ ≡ 0 at U = 1 therefore gives Ψ_0(ξ)v = 0 for every pure-gauge mode v = d̂λ, on each coset and hence
   {#B6.2.127} in the limit.
   {#B6.2.127-1} So Ψ_0 = d̂*Ψ̃_0d̂.
5. {#B6.2.128} *Conclusion.* By §6.2, Ψ_tb(ξ) = c ln(1/|ξ|²)(|ξ|²δ − ξξ) + O(|ξ|²) near 0.
   {#B6.2.128-1} Also d̂*d̂(ξ) = |ξ|²δ − ξξ + O(|ξ|³) (O(|ξ|⁴) for 1-forms at bond midpoints), and c ln(1/|ξ|²)·O(|ξ|³) = O(|ξ|²),
   {#B6.2.129} and on coexact forms d̂*d̂ is bounded below by a positive multiple of |ξ|², since 4 sin²(ξ_μ/2) is at least 4ξ_μ²/π²
   {#B6.2.130} for |ξ_μ| up to π.
   {#B6.2.130-1} Away from 0, Ψ_0 is continuous and bounded. ∎

### 6.3 The Bare Functional Seen from the Top {#BS6.3}

{#B6.3.1} **Proposition 6.4.** For fixed p_0 ≠ 0 (top units), Π_{−F_0}^{top}(p_0) = c ln(1/η_k²) Δ_k(p_0) + O_{p_0}(1), uniformly
{#B6.3.2} in k, where η_k = L^{−k}.
{#B6.3.2-1} The type-checked Lean core of the summation is `BalabanFormal.bare_assembly`.

{#B6.3.3} *Proof.*
1. {#B6.3.4} *Composition.* The top polarisation is ⟨H_kB, Ψ_0 H_kB⟩ = Σ_l ⟨(dH_kB)^∧(q), Ψ̃_0(η_k q)(dH_kB)^∧(q)⟩, summed over
   {#B6.3.5} the aliases q = p_0 + l (top units).
2. {#B6.3.6} *Insert Proposition 6.3.* This gives c ln(1/η_k²)Σ_l|(dH_kB)^∧(q)|² + cΣ_l ln(1/|q|²)|(dH_kB)^∧(q)|² + R-terms.
3. {#B6.3.7} *First term.* Σ_l |(dH_kB)^∧(q)|² = ‖dH_kB‖² = ⟨B, Δ_k B⟩ by PRT1 (1.65).
4. {#B6.3.8} *Second term.* For l ≠ 0, |q| ≥ π.
   {#B6.3.8-1} Hence |ln(1/|q|²)| ≤ ln(1/|p_0|²) + C_α|q|^{2α}, and the term is at most
   {#B6.3.9} C(p_0)(Σ_l|q|^α|(dH_k)^∧(q)|)²|B̂|², which is O_{p_0}(1)|B̂|² by Lemma 5.2.
5. {#B6.3.10} *R-terms.* They are at most sup‖R_0‖·‖dH_kB‖², which is bounded by PRT1 (1.67). ∎

## 7. The Top-Level Part Is Bounded at a Fixed Momentum {#BS7}

{#B7.1} **Proposition 7.1.** For fixed p_0 ≠ 0, sup_k ‖Π_{F_k}(p_0)‖ < ∞.

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
  {#B7.8-2} N(Q′) = {λ : Q′λ = 0}, R (the orthogonal projection onto ΔN(Q′)), and G′ are as in PBG
  {#B7.9} (3.21)–(3.24), with Q and Q′ as follows.
- {#B7.10} *The average.* Write Q̃ for §3.1's Q, the linearised k-fold average of the chain (RG1 (0.4) or (0.12)), with
  {#B7.11} Q̃D = D̄P.
  {#B7.11-1} PBG works with a dressed average instead (PBG p.392 l.45–46: CMP98 (89)–(92)), and §7 does the same for the
  {#B7.12} chain.
  {#B7.12-1} Q := Q(U) is the linear part of PBG's one-step formula (3.113), with Ū the chain's average and the contour
  {#B7.13} variables U(y, x) of RG1 (0.11) in place of U(Γ_{y,x}), composed over the k steps as in PBG (3.15).
  {#B7.13-1} Q′ is PBG (3.19)
  {#B7.14} with the same replacement: Q′λ(y) = Σ_{x∈B(y)}L^{−d}R(U(y, x))λ(x), composed over the k steps.
  - {#B7.15} *QD = D̄Q′.* PBG's derivation (3.113)–(3.115), p.418, uses only the point covariance of Ū (§3.1) and the
    {#B7.16} covariance U(y, x) ↦ u(y)U(y, x)u(x)^{−1} of the contour variables (RG1 (0.6) for (0.11)).
  - {#B7.17} *Q − Q̃ ∈ ran D̄.* The dressing factors (R̄_{c₋}U′)^{−1} and R̄_{c₊}U′ of (3.113) equal 1 at U′ = 1.
    {#B7.17-1} So the
    {#B7.18} one-step linear part is Q̃^{(1)}A + D̄ω_d(A), with ω_d(A)(y) the linear part of (1/i)log R̄_yU′.
    {#B7.18-1} Over the steps,
    {#B7.19} Q_j − Q̃_j = Q^{(j)}(Q_{j−1} − Q̃_{j−1}) + (Q^{(j)} − Q̃^{(j)})Q̃_{j−1}, and Q^{(j)}D̄ = D̄Q′^{(j)}, so the difference
    {#B7.20} stays in ran D̄ at every level.
    {#B7.20-1} Hence {QA ∈ z + ran D̄} = {Q̃A ∈ z + ran D̄}, and §3's Δ_k and F_k are the same
    {#B7.21} for Q and Q̃.
  - {#B7.22} *At U = 1, Q = Q_k,* the composite of the straight one-step averages (PRT1 (1.16)–(1.18)), with centred blocks.
    {#B7.23} Indeed, at U = 1 let A(Γ) and A(y, x) be the linear parts in A of (1/i)log U′(Γ) and (1/i)log U′(y, x); by RG1
    {#B7.24} (0.8), A(y, x) is the mean of A(Γ) over Γ ∈ 𝐆(y, x).
    {#B7.24-1} Then ω_d(A)(y) = Σ_{x∈B(y)}L^{−d}A(y, x), since R_y is the
    {#B7.25} identity at U = 1.
    {#B7.25-1} The contour factors contribute +ω_d(A)(c₋) − ω_d(A)(c₊) to Q̃^{(1)}A(c): in (0.4) directly, and
    {#B7.26} in (0.12) because reversing the contours of 𝐆(c₊, x′) gives 𝐆(x′, c₊) (RG1 p.252), so A(x′, c₊) = −A(c₊, x′).
    {#B7.26-1} The
    {#B7.27} dressing contributes −ω_d(A)(c₋) + ω_d(A)(c₊).
    {#B7.27-1} Also Q′(1) is the centred block average Q′_k (PRT1 (1.20)).
  - {#B7.28} So at U = 1, G, G′, R, H, C, and (QGQ*)^{−1} below are PBG's own operators at U = 1, conjugated by the fixed fine
    {#B7.29} translation from CMP98's corner blocks (CMP98 (2)) to RG1's centred ones: PBG's average also has Q(1) = Q_k
    {#B7.30} (CMP98 (124)) and the block average as Q′(1) (PBG (3.19)).
    {#B7.30-1} PBG's bounds at U = 1 apply without R50.
- {#B7.31} *The defect of the Hessian.* 𝒩 := 𝐇D.
  {#B7.31-1} Comparing first-order terms in λ in PBG (3.117) gives
  {#B7.32} ⟨A, 𝒩λ⟩ = ½⟨i[λ(b₋), A(b)] − i[A(b), R_bλ(b₊)], J⟩ =: T(J, λ, A).
  {#B7.32-1} This is linear in J, local, and contains no
  {#B7.33} derivative: |T(J, λ, A)| ≤ c Σ_b η⁴|J(b)||A(b)|(|λ(b₋)| + |λ(b₊)|), with c absolute.
- {#B7.34} *K.* K := 𝐇 − h = Π_D𝐇 + 𝐇Π_D − Π_D𝐇Π_D, with Π_D := D(DᵀD)^{−1}Dᵀ.
  {#B7.34-1} Put φ_A := (DᵀD)^{−1}DᵀA.
  {#B7.34-2} Since 𝐇D = 𝒩,

    {#B7.35} ⟨A′, KA⟩ = T(J, φ_{A′}, A) + T(J, φ_A, A′) − T(J, φ_A, Dφ_{A′}).  (7.1)

  {#B7.36} So K is linear in J, and it is nonlocal through φ.
- {#B7.37} *PBG's propagators.* Δ_π is PBG's gauge-invariant extension (3.119), and Δ′_π := 𝐇 − Δ_π is given by PBG (3.120).
  {#B7.38} Δ_π is invariant only under λ ∈ N(Q′).
  {#B7.38-1} Every term of (3.120) contains λ_A := G′RD*A.
  {#B7.38-2} G := (Δ_π + DRD* + aQ*Q)^{−1}
  {#B7.39} (PBG (3.122)), H := GQ*(QGQ*)^{−1} (PBG (3.126)), and C := G − GQ*(QGQ*)^{−1}QG.
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

  {#B7.56} The last two terms depend on B and not on k (step (e)).
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
{#B7.68-1} The constrained Gaussian (Schur complement) gives the t^n term of m_t as −t^n H*K′(CK′)^{n−1}H for
{#B7.69} n ≥ 1, with t⁰ term (QGQ*)^{−1} − a.
{#B7.69-1} On the fields of a coset 𝒪 ≠ ℤp₀ (step (a)), K′ = O(B), so for small B the map t ↦ m_t is analytic on |t| ≤ 2,
{#B7.70} and the t^n term is of order n in B. Moreover H*Δ′_πH = 0: polarising (3.120), every term contains λ_{Hz} = 0 or
{#B7.71} λ_{Hz′} = 0.
{#B7.71-1} So, up to terms of order three in B,

    {#B7.72} Δ_k = [(QGQ*)^{−1} − a] − H*KH − H*K′CK′H.  (7.2)

{#B7.73} *(c) Inputs on 𝔅_r.*
- {#B7.74} (QGQ*)^{−1}(U) has kernel ≤ Ce^{−δ₁|y−y′|} (PBG (3.132) with Theorem 3.12), and H(U) has the bounds (3.133).
  {#B7.74-1} These
  {#B7.75} hold for complex B ∈ 𝔅_r by Condition 4 and READINGS.md R50, through the conventions of §5.
  {#B7.75-1} So sup|H(U)z| ≤ C|ẑ| for
  {#B7.76} a coarse plane wave z.
- {#B7.77} U_k(e^{iB}) lies in U_k^c (conventions of §5), so |J| < α₀ on 𝔅_r, with RG1's α₀ (RG1 (1.16), p.262, with n = k and L^kξ = 1; RG1's γ₀, which is not PRT1's γ₀ of (d) and (f), equals α₀ by p.263 l.3).
- {#B7.78} (7.2) is invariant under fine gauge transformations that leave V fixed.
  {#B7.78-1} We take VAR's Landau gauge, in which
  {#B7.79} U = exp(iη𝓗(B)) with |𝓗| < B₅ε₁, VAR's ε₂ (VAR Proposition 9 with (19) and (173), pp.281, 305, 309).
- {#B7.80} Cauchy estimates in the plane-wave directions b, b̄ (𝔅-norm ≤ (1 + π)|b|) bound the first- and second-order parts.
  - {#B7.81} j₁ and j₂ of J have ‖j₁‖_∞ ≤ C|b| and ‖j₂‖_∞ ≤ C|b|².
  - {#B7.82} H₁z, the first-order part of H(U)z, has ‖H₁z‖_∞ ≤ C|b||ẑ|.
  - {#B7.83} A₁, the first-order part of 𝓗, has ‖A₁‖_∞ ≤ C|b|.
  - {#B7.84} The first- and second-order parts of (QGQ*)^{−1}(U) have kernels ≤ C|b|e^{−δ₁|y−y′|} and ≤ C|b|²e^{−δ₁|y−y′|}.
- {#B7.85} At U = 1, ‖G‖ ≤ C and ‖G′‖ ≤ C. These are PBG's operators at U = 1 (Setting), so the kernel bounds of PBG Theorems
  {#B7.86} 3.1 and 3.3 (B₀e^{−δ₀d(y,y′)} in top units) and the Schur test apply.

{#B7.87} All these C depend on d, L, r, RG1's α₀, and PBG's constants, and not on k.

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
  {#B7.95-1} By (7.1) it is at most
  {#B7.96} c‖j₁‖_∞(‖φ_{Hz′}‖_∞‖Hz‖_2 + ‖φ_{Hz}‖_∞‖Hz′‖_2 + ‖φ_{Hz}‖_∞‖Dφ_{Hz′}‖_2) ≤ C|b||ẑ||ẑ′|.
- {#B7.97} *T2, the second-order part of J.* −⟨Hz′, K(1, j₂)Hz⟩ ≤ C|b|²|ẑ||ẑ′| in the same way.
- {#B7.98} *T3, the term H*K′CK′H at U = 1.*
  - {#B7.99} Let X := K′(1, j)Hz with j ∈ {j₁[b], j₁[b̄]}; its quasi-momentum is p′ = p ± p₀.
  - {#B7.100} C ≥ 0, and on ker Q it is the inverse of G^{−1}.
    {#B7.100-1} So ⟨X, CX⟩ = sup{2Re⟨X, Y⟩ − ⟨Y, G^{−1}Y⟩ : Y ∈ ker Q},
    {#B7.101} with Y a Bloch wave of quasi-momentum p′.
  - {#B7.102} ⟨X, Y⟩ = ⟨Hz, KY⟩ − ⟨Hz, Δ′_πY⟩.
    {#B7.102-1} By (7.1), |⟨Hz, KY⟩| ≤ c‖j‖_∞(‖φ_{Hz}‖_∞‖Y‖_2 + (‖Hz‖_∞ +
    {#B7.103} ‖Dφ_{Hz}‖_∞)‖φ_Y‖_2) ≤ C(1 + |p̂′|^{−1})|b||ẑ|‖Y‖_2.
  - {#B7.104} Polarising (3.120) with λ_{Hz} = 0 gives ⟨Hz, Δ′_πY⟩ = ½⟨i[λ_Y(b₋), Hz(b)] − i[Hz(b), R_bλ_Y(b₊)], j⟩.
    {#B7.104-1} So
    {#B7.105} |⟨Hz, Δ′_πY⟩| ≤ c‖j‖_∞‖Hz‖_∞‖λ_Y‖_2.
  - {#B7.106} At U = 1, Δ_π = ∂*∂ ≥ 0, so ⟨Y, G^{−1}Y⟩ ≥ ‖RD*Y‖² and ⟨Y, G^{−1}Y⟩ ≥ ‖G‖^{−1}‖Y‖².
    {#B7.106-1} Also
    {#B7.107} ‖λ_Y‖ ≤ ‖G′‖‖RD*Y‖.
  - {#B7.108} Hence ⟨X, CX⟩ ≤ C(1 + |p̂′|^{−1})²|b|²|ẑ|², and by Cauchy–Schwarz for C ≥ 0 the T3 terms are at most
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

{#B7.121} *(e) The top-level terms.* They are explicit functions of B on the unit lattice.
- {#B7.122} P_TD̄_V = P_TD̄_1[B] + O(B²), where D̄_1[B]ω(c) = −i[B(c), ω(c₊)] has no derivative.
  {#B7.122-1} So
  {#B7.123} log det_{T₀}(P_TΠ_VP_T) = −tr(P_TD̄_1(D̄_0ᵀD̄_0)^{−1}D̄_1ᵀP_T) + O(B³), and its symbol at p₀ is at most
  {#B7.124} C∫|p̂|^{−2}d⁴p.
- {#B7.125} For log det(D̄_VᵀD̄_V), the first- and second-order vertices of D̄_VᵀD̄_V are at most C(|p̂| + |(p + p₀)^|) and
  {#B7.126} C(1 + |p̂|).
  {#B7.126-1} So its symbol at p₀ is at most C∫(|p̂|^{−2} + |p̂|^{−2}|(p + p₀)^|^{−2}(|p̂| + |(p + p₀)^|)²)d⁴p.

{#B7.127} *(f) Integration.* The second-order coefficient of ½ log det_{T₀}(Δ⁰ + V¹ + V²) is
{#B7.128} ½tr(Δ⁰^{−1}V²) − ¼tr(Δ⁰^{−1}V¹Δ⁰^{−1}V¹).
{#B7.128-1} By (d) and γ₀|p̂|² ≤ Δ⁰,

    {#B7.129} ‖Π_{F_k}(p₀)‖ ≤ C ∫_{[−π,π]⁴} [|p̂|^{−2}(1 + |(p + p₀)^|^{−2} + |(p − p₀)^|^{−2}) + |p̂|^{−2}|(p + p₀)^|^{−2}] d⁴p
      {#B7.130} + (the terms of (e)) < ∞.

{#B7.131} The integrals converge because d = 4 and p₀ ≠ 0, which separates the singular points 0 and ∓p₀.
{#B7.131-1} C does not depend on
{#B7.132} k. ∎

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
2. {#B7.144} *PRT1's gauge parameter.* Put S(p) := Σ_ν|∂¹_ν(p)|²/(Δ₀(p)²φ_ν(p)), N(p) := Σ_{l″}|u(p + l″)|²Δ₀(p)²/Δ(p + l″)², and
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
{#B7.161} one-step formulas (3.113) composed as in CMP98 (91).
{#B7.161-1} Let U(t) = exp(itηA₁ + O(t²)) bondwise, for a fine 1-form A₁.
{#B7.162} For a field X at spacing s put ‖X‖_p^p := Σ_b s^d|X(b)|^p over the bonds of one top cell.
{#B7.162-1} Then for Bloch waves A, A′
  {#B7.163} ‖C^{(2)}(1; A, A′)‖_1 ≤ C‖A‖_2‖A′‖_2,  ‖∂_tC^{(2)}(U(t); A, A′)|_{t=0}‖_1 ≤ C‖A₁‖_∞‖A‖_2‖A′‖_2,
{#B7.164} and ‖∂_tQ(U(t))|_{t=0}A‖_p ≤ C‖A₁‖_∞‖A‖_p for p = 1, 2.
{#B7.164-1} Here C depends only on d, L, and G. At a top bond c these
{#B7.165} depend only on the fields on B^k(c₋) ∪ B^k(c₊).

{#B7.166} *Proof.* Step j (1 ≤ j ≤ k) maps level-(j − 1) fields, of spacing s_j := L^{j−1−k}, to level-j fields, of spacing
{#B7.167} ε_j := Ls_j.
{#B7.167-1} The computation is in `work_K2_second_order_average.md`.
1. {#B7.168} *One step.* Ū̄′_c is built from the level-(j − 1) bond variables of the fluctuation and of the background on the
   {#B7.169} bonds R_c of B(c₋) ∪ B(c₊) and of the lines [x, x′], by products, inverses, conjugations, the group average M of
   {#B7.170} RG1 (0.10), and averages exp(iΣ w log).
   {#B7.170-1} These are defined and analytic near 1 on the complexified group G^c (RG1
   {#B7.171} p.252 l.37, p.253 l.16), and no length enters them.
   {#B7.171-1} So there is one analytic Ψ: g_ℂ^n × g_ℂ^n → g_ℂ on a complex
   {#B7.172} polydisc of radius r₀(d, L, G), with n = |R_c| depending on d and L, such
   {#B7.173} that (1/i)log Ū̄′_c = Ψ(s_ja, s_jB) for every j, k, and c, where a and B are the background and fluctuation
   {#B7.174} logarithms on R_c.
   {#B7.174-1} Ψ(a, 0) = 0, since every factor of (3.113) is 1 at U′ = 1.
   {#B7.174-2} The normalised step is
   {#B7.175} ε_j^{−1}Ψ(s_ja, s_jB).
2. {#B7.176} *Kernels.* By Cauchy estimates, the Taylor coefficients of Ψ of order N are at most K_N := sup|Ψ|r₀^{−N}, with
   {#B7.177} the sup over the complex polydisc.
   {#B7.177-1} So, at
   {#B7.178} a = ta₁ + O(t²), the second-order part c_j^{(2)} of the normalised step has kernel entries at most K₂s_j²/ε_j =
   {#B7.179} K₂s_j/L on R_c × R_c.
   {#B7.179-1} Its t-derivative has entries at most K₃ns_j³ε_j^{−1}‖a₁‖_∞, and the t-derivative of the
   {#B7.180} linear part has entries at most K₂ns_j‖a₁‖_∞/L on R_c.
3. {#B7.181} *Norms.* Let each bond lie in at most m(d, L) of the sets R_c.
   {#B7.181-1} For a bilinear kernel with entries at most K on
   {#B7.182} R_c × R_c, 2|X||Y| ≤ τ|X|² + τ^{−1}|Y|² and the count give an L¹-norm at most L^dKnm(τ‖B‖_2² + τ^{−1}‖B′‖_2²), so
   {#B7.183} at most 2L^dKnm‖B‖_2‖B′‖_2.
   {#B7.183-1} A linear kernel with entries at most K has L²-norm at most L^{d/2}K(nm)^{1/2} and
   {#B7.184} L¹-norm at most L^dKm.
4. {#B7.185} *Composition at U = 1.* At U = 1 every background is 1, and the linear part of each step is the straight average
   {#B7.186} Q^{(j)} (§7's Setting).
   {#B7.186-1} It is an L¹-, L²-, and L^∞-contraction: each level-(j − 1) bond lies on exactly L lines
   {#B7.187} [x, x′], each with weight s_j^dL^{−1}, and (Q^{(j)}B)(c) is a mean of L^{d+1} values.
   {#B7.187-1} Expanding the composite to
   {#B7.188} second order gives
     {#B7.189} C^{(2)}(1; A, A′) = Σ_{j=1}^k Q^{(k)}⋯Q^{(j+1)} c_j^{(2)}(Q_{j−1}A, Q_{j−1}A′).
   {#B7.190} By steps 2–3, the j-th term is at most 2L^{d−1}K₂nm s_j‖A‖_2‖A′‖_2.
   {#B7.190-1} Also Σ_{j=1}^k s_j ≤ 1/(L − 1).
5. {#B7.191} *The background of step j* is the raw average Ū^{j−1}(U(t)) (PBG (3.15)), with logarithms tQ̃_{j−1}(1)A₁ + O(t²).
   - {#B7.192} At U = 1, Q̃^{(i)}B = Q^{(i)}B − D̄ω^{(i)}(B), with ω^{(i)}(B) the contour mean ω_d of §7's Setting for the
     {#B7.193} field B, and
     {#B7.194} the contours of 𝐆(y, x) have at most d(L − 1)/2 bonds.
     {#B7.194-1} (B(y) consists of the points of spacing s_i in the cube of
     {#B7.195} side ε_i centred at y (RG1 (0.3)), so with L odd x − y = Σ_μ s_in_μe_μ has |n_μ| ≤ (L − 1)/2; RG1 p.252 l.29
     {#B7.196} prints "L − 1/2".) So |ω^{(i)}(B)| ≤ s_id(L − 1)sup|B|/2.
   - {#B7.197} By Q̃^{(i)}D̄ = D̄P, Q̃_iA = Q_iA − D̄ω_i(A) with ω_i := Pω_{i−1} + ω^{(i)}(Q_{i−1}A).
     {#B7.197-1} Since
     {#B7.198} Σ_{i<j}s_i ≤ ε_{j−1}/(L − 1), we get sup|ω_{j−1}| ≤ (d/2)ε_{j−1}sup|A|.
     {#B7.198-1} So the normalised level-(j − 1) gradient is
     {#B7.199} at most d·sup|A|, and ‖Q̃_{j−1}(1)A₁‖_∞ ≤ (1 + d)‖A₁‖_∞.
6. {#B7.200} *The derivative.* The t-derivative of the composite falls on one Q^{(i)}, on c_j^{(2)}, or on Q_{j−1}.
   {#B7.200-1} By steps 2,
   {#B7.201} 3, and 5 these contribute at most C‖A₁‖_∞ times Σ_j s_jΣ_i s_i, Σ_j s_j², and Σ_j s_jΣ_{i<j}s_i respectively.
   {#B7.201-1} Each
   {#B7.202} of these is bounded independently of k.
   {#B7.202-1} The derivative of Q(U(t)) is the sum over i of the middle factors, with
   {#B7.203} the same bound.
7. {#B7.204} *Locality.* The contours of 𝐆(y, x) lie in B(y), and the lines [x, x′] join B(c₋) to B(c₊), so each step at c
   {#B7.205} uses only the fields on B^k(c₋) ∪ B^k(c₊). ∎

## 8. The Window Theorem {#BS8}

{#B8.1} **Theorem 8.1.** There is a C such that for all k (from PRT1 (1.67) and Propositions 5.1, 5.3, 6.4 and 7.1)
  {#B8.2} |Φ_k − (11/24π²) κ k ln L| ≤ C,
{#B8.3} and therefore, for all 0 ≤ m ≤ n,
  {#B8.4} **| Σ_{j=m+1}^{n} b_j − (11/24π²) κ (n−m) ln L | ≤ 2C.**

{#B8.5} *Proof.*
1. {#B8.6} *Identity.* By Corollary 3.2 on each coset 𝒪 ≠ ℤp₀ (Remark 3.4), summed over the steps, ℒ_k = F_k − F_0 + 𝒥_k
   {#B8.7} holds for the restrictions to the fields on 𝒪 ∪ (−𝒪), hence for the coset sums and their limits.
   {#B8.7-1} So at p_0 ≠ 0:
   {#B8.8} Π_{ℒ_k}(p_0) = Π_{F_k}(p_0) + Π_{−F_0}^{top}(p_0) + Π_{𝒥_k}(p_0).
   {#B8.9} These limits are the symbols that step 2 inserts, for the following reasons.
   - {#B8.10} Π_{F_k} is computed on the same cosets (Proposition 7.1(a)).
   - {#B8.11} Π_{ℒ_k} (Proposition 5.1) is the polarisation of Bałaban's step factors on the whole torus.
     {#B8.11-1} Their quadratic forms
     {#B8.12} are built from PBG's G₁, H₁, Δ₁, G′, R, h_B, C̃^{(2)}, and 𝐆^{(2)} (PBG (3.128)–(3.129); Proposition 4.2(a)), and
     {#B8.13} contain no (DᵀD)^{−1}; C^{(j)}(1), j < k, is invertible on the whole torus, and the Jacobian c(U) is site-local.
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
     {#B8.25} N. The level-m integrands are bounded there, since their singular points 0 and −q lie in ℤq.
     {#B8.25-1} So, at fixed k, the
     {#B8.26} limits are the alias sums of the level-m symbols of Propositions 4.2 and 6.3, of which there are L^{4(k−m)}.
2. {#B8.27} *Insert the estimates.* Take p_0 = (π/2, 0, 0, 0) and a unit vector e ⊥ v(p_0).
   {#B8.27-1} Propositions 5.1, 7.1, 6.4 and 5.3
   {#B8.28} give Φ_k⟨e, Δ_k(p_0)e⟩ = c ln(1/η_k²)⟨e, Δ_k(p_0)e⟩ + O(1).
3. {#B8.29} *Divide.* By PRT1 (1.67), ⟨e, Δ_k(p_0)e⟩ ∈ [γ_0|p̂_0|², γ_1|p̂_0|²], with γ_0 > 0 independent of k.
   {#B8.29-1} Since
   {#B8.30} ln(1/η_k²) = 2k ln L and 2c = (11/24π²)κ, the claim follows. ∎

{#B8.31} **Corollary 8.2 (RG1 Theorem 2 for Simple G).** Take ε₁ as in Proposition 2.4.
{#B8.31-1} Theorem 8.1 is hypothesis (W) of §2 at
{#B8.32} zero coupling, and Propositions 2.4 and 2.6 give (P2) with δ = c ln L and (C).
{#B8.32-1} By Remark 2.3, Lemma 2.1 gives, for
{#B8.33} every small renormalised coupling g and every ε = L^{−K}:
- {#B8.34} a bare g_0(ε, g), independent of the torus;
- {#B8.35} g_K = g, and all g_k in ]0, γ];
- {#B8.36} RG1 (0.31) with β = 2c − δ/ln L ≥ c and β′ = 2c + δ/ln L, up to an additive constant;
- {#B8.37} the near-monotonicity that LFR2 (1.86) uses (Remark 2.2).

{#B8.38} With CRE's cutoff δ_k, Proposition 2.9 also gives (P2) with δ = C_remγ² (RG1 (0.31), CRE p.265).

## 9. Inputs {#BS9}

{#B9.1} **Inputs taken from Bałaban without re-proof, with their caveats.**
- {#B9.2} PRT1 (1.31), (1.61)–(1.63), and the alias decomposition of PRT1 p.23 (for Lemma 5.2, whose bounds (1.36) and
  {#B9.3} γ₀ ≤ Δ₀φ_μ ≤ γ₁ of PRT1 p.28 are derived there with constants depending only on d), and PRT1 (1.65)–(1.67); PBG Thms
  {#B9.4} 3.1, 3.3, 3.4, 3.12, 3.15; PBG (3.117)–(3.137) and (3.156), of which (3.132) PBG p.422 gives without proof ("We will
  {#B9.5} not repeat these considerations here, let us write only bounds"); RG1 (0.28)–(0.30), RG1 (1.8)–(1.9), RG1 p.263
  {#B9.6} (analyticity domains); VAR Thm 1 and §G.
- {#B9.7} For Proposition 4.2: Bałaban's step form RG1 (1.4)–(1.5), with (2.5), p.266, (2.10)–(2.11), p.267, the replacement
  {#B9.8} of the δ-function gauge fixing of PBG (3.156) by the exponential term 𝐆^{(2)} (p.267 l.38–39), and the elimination
  {#B9.9} B′ = 𝒫B″ with C^{(k)} = (𝒫*Δ^{(k)}𝒫)^{−1} (p.268 l.2–3).
- {#B9.10} For Proposition 5.3, steps 1 and 4, and Proposition 7.1(a): PRT1's corner blocks (p.18), its averages (1.8) and
  {#B9.11} (1.11), p.19, and (1.16)–(1.18), p.20; the gauge covariance (1.20), p.20; the projection R onto ΔN(Q′_k) (pp.24–25);
  {#B9.12} the properties of H_kB on p.29 (Q_kH_kB = B, R∂*H_kB = 0, and H_kB a minimum of ½⟨∂A, ∂A⟩ on
  {#B9.13} {A : Q_kA = B, R∂*A = 0}); the gauge term of PRT1 (1.68)–(1.70); the Wilson action RG1 (0.2) and the centred blocks
  {#B9.14} RG1 (0.3), p.252; RG1 (0.17) and (0.19), p.255; and RG1 (0.21)–(0.22), p.256 (the unique critical orbit of minima,
  {#B9.15} proved in VAR).
- {#B9.16} PBG was written for the averaging of AVG (CMP 98), and PRT1 for the Abelian straight averages PRT1 (1.8) and (1.11),
  {#B9.17} p.19, which are the main term of AVG's linear form at V₀ = 1 (CMP98 (124)–(125), p.36: it "resembles the definition
  {#B9.18} of the averaging operation Q in [2]", [2] = PRT1).
  {#B9.18-1} RG1 uses the Euclidean-symmetric average RG1 (0.4).
  {#B9.18-2} At U = 1 the
  {#B9.19} first-order part of RG1 (0.4) is PRT1's straight average up to a gradient and a fine translation (Proposition 5.3,
  {#B9.20} steps 1 and 4), so Lemma 5.2 and PRT1 (1.65)–(1.67) apply to the chain at U = 1.
  {#B9.20-1} This argument uses R47 for the
  {#B9.21} statement that the chain averages with RG1 (0.4), and, through Proposition 5.3, step 1, for the unique minimal orbit
  {#B9.22} and the analyticity in t (the bullet on VAR below); the sentence on RG1 p.253 that the earlier results hold for any
  {#B9.23} average with the listed properties concerns group averages M (R47, scope) and is not used.
- {#B9.24} At U = 1, the linear parts of the dressed average of the chain and of PBG's dressed average agree up to a fine
  {#B9.25} translation, and both are Q_k (§7's Setting; CMP98 (124)); their second-order parts differ.
  {#B9.25-1} So PBG's bounds at
  {#B9.26} U = 1 on G, G′, H, C_G, R, and (QGQ*)^{−1} (Propositions 4.2(d) and 7.1(c)) hold for the chain as printed.
  {#B9.26-1} The
  {#B9.27} second-order part of the chain's dressed average at U = 1 and its U-derivative, and the U-derivative at 1 of its linear
  {#B9.28} part Q, are bounded directly (Lemma 7.3), and so are the U-derivatives at 1 of D and of RG1's step objects h_B,
  {#B9.29} C̃^{(2)}, 𝒫, and 𝐆^{(2)} (Proposition 4.2(d)).
  {#B9.29-1} PBG's results for the operators of the chain away from U = 1
  {#B9.30} (Propositions 4.2, 5.3, 7.1, and 2.12, step 5; Condition 4), and for C^{(k)}(1), whose gauge-fixing term is
  {#B9.31} exponential (Proposition 4.2(d)), are not covered by these arguments.
  {#B9.31-1} They enter as
  {#B9.32} Bałaban applies them to the chain of RG1, RG2, and CRE, whose averaging CRE p.243 states as RG1 (0.4) or (0.12):
  {#B9.33} RG1 p.261 (the operators H_{1,j}, Δ₁ of PBG Sect. D, and the analyticity "from results of that paper" under PBG
  {#B9.34} (3.35)–(3.38)); RG1 pp.266–267 (PBG (3.127)–(3.128) and (3.156)); RG2 p.3 (the expansion PBG (3.107)–(3.108),
  {#B9.35} whose bound "holds for all operator norms in formulations of theorems in [13]"); RG2 p.5 ("in all norms of Theorems
  {#B9.36} 3.1.-3.10 [13]"); RG2 p.13 (random walk expansions "discussed in [13] for all operators determining Δ_k, and for
  {#B9.37} C^{(k)}(Z_0)", with PBG (3.185)); and CRE p.276 ("we apply Theorems 3.7–3.10 [13] in their full generality").
  {#B9.38} Reading these applications as Bałaban's statement that PBG's results hold for the operators of that chain, with
  {#B9.39} those operators built from the dressed average of §7's Setting (Bałaban prints no dressing for his chain), is
  {#B9.40} READINGS.md R50.
- {#B9.41} VAR Thm 1 inherits the sketched Theorem 8 of REG (p.101: "Inspecting the proofs … almost without any changes")
  {#B9.42} (`D:\University\Oxford PostDoc\Balaban\BALABAN_DEPENDENCE_TREE.md`, D3).
  {#B9.42-1} It enters §§5 and 7
  {#B9.43} through the analyticity of U_k(V).
- {#B9.44} VAR was written for the averaging of CMP98.
  {#B9.44-1} RG1 states VAR Thm 1's unique regular minimal orbit for its own M^k
  {#B9.45} (RG1 (1.1), p.260, "see Theorem 1 there"; RG1 (0.21), p.256), and it applies VAR Prop. 9 (p.309: U_k(V) analytic
  {#B9.46} in B = (1/i)log V′) to U_n(M^·(𝐔)) on complex configurations (RG1 (1.17), p.263), and VAR Prop. 9 with (190) to
  {#B9.47} the derivative δ𝐇_j/δB (RG1 p.271 l.33).
  {#B9.47-1} Apart from LFR2's functions built from VAR's results, which enter with
  {#B9.48} LFR2 (the tube-construction bullet below), the file uses VAR for the chain averaging with RG1 (0.4) only through
  {#B9.49} these statements: Proposition 5.3, step 1 (the orbit and analyticity in t), the analyticity of the background in
  {#B9.50} §5, Proposition 7.1(c) (the Landau gauge of VAR Prop. 9), Lemma 2.5, step 1 (VAR (190)), and Proposition 2.12(b)
  {#B9.51} (VAR Prop. 9 and (190) at every admissible real B⁰).
  {#B9.51-1} That they hold for this chain is READINGS.md R47.
- {#B9.52} VAR (189), stated without proof, enters Lemma 2.5 through VAR (190) (sidecar node VAR_189).
- {#B9.53} From RG1 Theorem 3 with RG2 Lemmas 1–3 and RG2 (2.41): the bound RG1 (1.18) and the analyticity of the step terms in
  {#B9.54} (U, J) on RG1's fixed domains, for §§2.1–2.2, as printed for RG1's cutoff.
- {#B9.55} For the tube construction: CRE's inductive estimates as printed, in particular CRE (2.30)–(2.31), p.260, (2.44) and
  {#B9.56} (2.46), p.263, and the statement that the step output satisfies the inductive assumption (CRE p.279), and the
  {#B9.57} estimates of LFR1 and LFR2, including LFR2 (1.79)–(1.80), pp.383–384, and of UV3, CMP98, REG, and VAR as CRE uses
  {#B9.58} them.
- {#B9.59} Readings of these inputs, as READINGS.md records them, each checked against the print:
  - {#B9.60} R40: the B-set of RG2 (1.34) is a complex polydisc, and RG2 Lemmas 1–2 hold on it, as "defined and analytic on
    {#B9.61} the space (1.34)" states (RG2 pp.9–11; Lemma 2.7, step 1);
  - {#B9.62} R43: CRE (3.16)'s threshold applies to the field-scale fluctuation g_kA_k (CRE pp.267–268; §0, *Condition 3*);
  - {#B9.63} R4: LFR1 p.198 and LFR2 p.363 use two different exponents ν, and with N = R_j both conditions hold for small g
    {#B9.64} (*CRE's Construction as a Function of the History*; Lemma 2.10, step 4);
  - {#B9.65} R47: the RG1 and CRE results used here hold for the chain built with the averaging RG1 (0.4), which CRE p.243
    {#B9.66} names as its averaging (Proposition 5.3, steps 1 and 4, the analyticity of the background in §5, Proposition
    {#B9.67} 7.1(c), Lemma 2.5, Proposition 2.12(b), and the bullets above on the averaging and on VAR);
  - {#B9.68} R50: PBG's results hold for the operators of the chain of RG1, RG2, and CRE, as Bałaban applies them there
    {#B9.69} (Propositions 4.2, 5.3, 7.1, and 2.12, step 5, away from U = 1, and C^{(k)}(1) in Proposition 4.2(d); Condition
    {#B9.70} 4), with the chain's operators read as built from the dressed average of §7's Setting; PBG states Thms 3.12, 3.15, and (3.132) for real U, and their
    {#B9.71} complex form rests on RG1 p.261 and RG2 pp.3, 5 (R50).
- {#B9.72} RG2's sketch on p.11 for the terms of P^{(k)} other than V, for Lemma 2.7 and so for Proposition 2.9.

{#B9.73} **Arguments of This File That Extend Bałaban's Statements.** These are not printed by Bałaban; their proofs are in §§0
{#B9.74} and 2, and, for Theorem 8.1 and Corollary 8.2, in §§3–8.
- {#B9.75} The identification of CRE's step terms with those of RG1's construction run with δ_j, up to the R′-terms (CRE
  {#B9.76} pp.267, 271, 272, 274, 278–283; §0, *CRE's Step Terms and β_j*).
  {#B9.76-1} It identifies the regular part of the tube
  {#B9.77} construction's β^T with RG1's construction run with the tube cutoffs δ_j^T, whose bounds come from Propositions 2.4
  {#B9.78} and 2.9 (Lemma 2.10, step 7).
- {#B9.79} The alias summability (Lemma 5.2) for every α ∈ (0, 1), derived from PRT1 (1.63) with the bounds (1.36) and
  {#B9.80} γ₀ ≤ Δ₀φ_μ ≤ γ₁ proved there with constants depending only on d; PRT1 pp.28–29 states a bound of this kind without
  {#B9.81} defining its exponent.
- {#B9.82} The dressed average of the chain: PBG (3.113) applied to RG1 (0.4) or (0.12), with the contour variables of RG1
  {#B9.83} (0.11).
  {#B9.83-1} It differs from the chain's average by a coarse gauge direction, so Δ_k and F_k are unchanged, and its
  {#B9.84} linear part at U = 1 is Q_k (§7's Setting).
  {#B9.84-1} Lemma 7.3 bounds its second-order part at U = 1, and the U-derivatives at 1 of
  {#B9.85} that part and of its linear part, uniformly in k.
- {#B9.86} The window theorem for the zero-coupling coefficients (Theorem 8.1, from §§3–7), the flow lemma (Lemma 2.1),
  {#B9.87} Remark 2.3, and the matching for simple G (Corollary 8.2).
  {#B9.87-1} RG1 Theorem 2 (RG1 p.259) is stated for SU(2), and its
  {#B9.88} proof is deferred to "a separate paper"; Corollary 8.2 proves it for simple G.
- {#B9.89} The parameter choices p₀ > (d+5)r + ⌈r⌉ + 2 (Lemma 2.10, step 4) and q₀, q₁ > p₀ (Proposition 2.11, step 4), which CRE's
  {#B9.90} printed conditions ("p₀ ≥ 5r", CRE p.246; q₀, q₁ "integers greater than 1", CRE p.259) allow.
- {#B9.91} The transfer of RG1 Theorem 3 from RG1's cutoff to CRE's cutoff δ_j = g_j(A₁/A₀)p₀(g_j) (CRE p.265) and to δ_j^T
  {#B9.92} (§0, *Condition 3*; the remark after Proposition 2.6; Lemma 2.10, step 7).
- {#B9.93} The bound (P2) and the continuity (C) of β (Propositions 2.4 and 2.6), with the polarisation bound of Lemma 2.5.
- {#B9.94} The transfer to complex coupling (Lemma 2.7), the parity, the threshold differences (Lemma 2.8), and the
  {#B9.95} telescoping (Proposition 2.9).
- {#B9.96} CRE's inductive step run with complex multiples of the R′-part, with that part controlled through CRE's own bound
  {#B9.97} (2.31) by a constant K_R, and the regular inputs bounded with 2E₀; CRE states the step at s = 1 only
  {#B9.98} (Proposition 2.11, steps 3–4, and *The Step with Complex Multiples of the R-Terms*).
- {#B9.99} Lemma 2.5 on the (2.28) domains with the tube radii, with Cauchy radius r ≥ c·min(α^T_{0,k+1}, α^T_{1,k+1})
  {#B9.100} (Proposition 2.11, step 5).
- {#B9.101} The decomposition χ′^{(j)} = χ({|g_jB_j(b)| < δ′_j}) with the threshold on the unscaled field, in place of LFR1
  {#B9.102} (1.55), whose print has the scaled variable, with the four steps that use it, among them the large-field factor
  {#B9.103} exp(−cA₁²p₁²(g_j)) of the components it
  {#B9.104} excludes, which LFR2 does not print (*LFR1 (1.55)*, before Lemma 2.10).
- {#B9.105} The tube construction, its convention for histories that are not flows, and its admissibility (Lemma 2.10).
  {#B9.105-1} Step 6
  {#B9.106} of its proof rests on a reading of every line of CRE, LFR1, LFR2, and UV3 that contains one of the parameters,
  {#B9.107} sorted into four kinds and two further uses.
- {#B9.108} The continuity of the tube construction in the history (Proposition 2.12) and the matching (Proposition 2.13).

{#B9.109} **Lean cores.** The type-checked Lean cores named above (`BalabanFormal.flow_lemma`,
{#B9.110} `BalabanFormal.coupling_flow_of_stepBound`, `BalabanFormal.symbol_holder_bound`,
{#B9.111} `BalabanFormal.jterm_holder`, `BalabanFormal.jterm_assembly`, `BalabanFormal.bare_assembly`, `SmoothNum.lemma61`, and
{#B9.112} `BalabanFormal.angular_coefficient`) are abstract statements.
{#B9.112-1} The hypotheses of `jterm_holder` and `jterm_assembly` are
{#B9.113} those stated in Propositions 4.2 and 5.3; those of the others are listed in
{#B9.114} `D:\University\Oxford PostDoc\Balaban\sidecar\BalabanSidecar\Instantiation.lean`.
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
{#B9.121} names in `C:\Users\marti\Documents\Scientia\Mathematics\Lean\Projects\balaban`, which the Bałaban sidecar's gates check.

## 10. Semisimple G {#BS10}

{#B10.1} Let G ⊂ U(N) be compact, connected, and semisimple, with Lie algebra g = g_1 ⊕ ⋯ ⊕ g_r (simple ideals).
{#B10.1-1} RG1 states its
{#B10.2} construction and Theorem 1 for this case (p.251 l.30–p.252 l.2, p.259 l.23–24), with one coupling; a step that needs
{#B10.3} r = 1 is the statement "proportional to δ^{ab}" on p.264 l.11–12 (Lemma 10.1).

{#B10.4} **Lemma 10.1.** Every Ad(G)-invariant symmetric bilinear form on g has the form Σ_i ϑ_i K_i (ϑ_i real), where K_i is the Killing form
{#B10.5} of g_i.
{#B10.5-1} In particular the trace form of G ⊂ U(N) is Σ_i (κ_i^N)^{−1} K_i, with κ_i^N > 0 defined by K_i = κ_i^N·tr on
{#B10.6} g_i.

{#B10.7} *Proof.* Let β be invariant and i ≠ j, and let G_i be the connected subgroup of G with Lie algebra g_i.
{#B10.7-1} For fixed
{#B10.8} Y ∈ g_j, the functional X ↦ β(X, Y) on g_i is invariant under Ad(G_i) (G_i acts trivially on g_j), hence zero, since a simple g_i has no nonzero invariant vectors.
{#B10.8-1} On each g_i, Lemma 1.1
{#B10.9} gives β|_{g_i} = ϑ_i K_i. ∎

{#B10.10} **Proposition 10.2 (Additive Actions Reduce to Simple Factors).** Let ρ_i: G → U(N_i), i = 1, …, r, be unitary
{#B10.11} representations with dρ_i injective on g_i and zero on g_j for j ≠ i, and let the bare action be
{#B10.12} S(U) = Σ_i g_{0,i}^{−2}A_i(ρ_i(U)), where A_i is the Wilson action RG1 (0.2) of U(N_i).
{#B10.12-1} Put H_i := ρ_i(G),
{#B10.13} H := H_1 × ⋯ × H_r, and Φ := (ρ_1, …, ρ_r): G → H. Then:
- {#B10.14} (a) Φ is onto, with finite central kernel Z, each H_i ⊂ U(N_i) is compact with simple Lie algebra dρ_i(g_i), and
  {#B10.15} Φ_*μ_G = ⊗_iμ_{H_i} (μ the normalised Haar measures).
- {#B10.16} (b) For bounded measurable F on H^E (E the bonds of the torus), ∫ F(Φ(U))e^{−S(U)}dμ_G^E(U) = ∫ F(V)∏_ie^{−g_{0,i}^{−2}A_i(V_i)}dμ_H^E(V), and for F = ∏_iF_i(V_i)
  {#B10.17} the right side is the product of the factors' integrals.
  {#B10.17-1} For bounded measurable F on G^E, let PF(U) be the average
  {#B10.18} of F(zU) over z ∈ Z^E ((zU)_b := z_bU_b), with the uniform measure.
  {#B10.18-1} Then PF = F̃∘Φ^E for a bounded measurable F̃ on
  {#B10.19} H^E, and ⟨F⟩_G = ⟨F̃⟩_H, the expectation of the product theory on H.
- {#B10.20} (c) Let σ be an irreducible representation of G and C a loop.
  {#B10.20-1} If σ is trivial on Z, then σ = (σ_1 ⊗ ⋯ ⊗ σ_r)∘Φ with
  {#B10.21} σ_i irreducible on H_i, and ⟨tr σ(U(C))⟩_G = ∏_i⟨tr σ_i(V_i(C))⟩_{H_i}.
  {#B10.21-1} If σ(z) ≠ 1 for some z ∈ Z and C traverses
  {#B10.22} some bond exactly once, then ⟨tr σ(U(C))⟩_G = 0.
- {#B10.23} (d) For a target (K, g^{(1)}, …, g^{(r)}) with g^{(i)} ∈ (0, γ_i′], run on each H_i ⊂ U(N_i) the tube construction of
  {#B10.24} §0 for the target (K, g^{(i)}), and take the product.
  {#B10.24-1} Then for each i there is a bare coupling g_{0,i}(ε, g^{(i)}),
  {#B10.25} independent of the torus and of the other targets, with g_{K,i} = g^{(i)} and g_{k,i} ∈ (0, γ_i] for 0 ≤ k ≤ K, whose
  {#B10.26} flow satisfies what §0 (after Condition 5) states for the tube construction of H_i: item 1, items 3 and 4 along the
  {#B10.27} matched flow with δ′_i = δ_i + C_Rγ_i^{κ₀−4} in place of δ_i, and item 5 with C_rem,i + C_Rγ_i^{κ₀−6} in place of
  {#B10.28} C_rem,i.
  {#B10.28-1} Here γ_i, γ_i′, C_i, δ_i, C_rem,i, and c_i = (11/48π²)κ_i are the constants of Theorem 0.1 for H_i, with
  {#B10.29} K_i = κ_i·tr on dρ_i(g_i) ⊂ u(N_i) (tr the normalised trace of U(N_i)); for the Wilson action of a defining representation (*Which actions are
  {#B10.30} additive*), κ_i^N = (N/N_i)κ_i.

{#B10.31} *Proof.*
1. {#B10.32} *Covering.* dΦ = ⊕_idρ_i is injective, because on g_j only the component dρ_j is nonzero and it is injective there;
   {#B10.33} and Lie(H_i) = dρ_i(g) = dρ_i(g_i), so dΦ is onto ⊕_iLie(H_i).
   {#B10.33-1} Hence Φ(G) contains a neighbourhood of 1 in H, so it
   {#B10.34} is an open, hence closed, subgroup of the connected group H, and equals H. Z = ker Φ is closed with Lie algebra
   {#B10.35} ker dΦ = 0, so discrete and, being compact, finite; it is central, because for z ∈ Z the map g ↦ gzg^{−1} is a
   {#B10.36} continuous map from the connected G into the discrete Z.
2. {#B10.37} *Haar measure.* Φ_*μ_G is a probability measure on H, invariant under left translation by every Φ(g), that is, by
   {#B10.38} every element of H; by uniqueness, Φ_*μ_G = μ_H = ⊗_iμ_{H_i}.
3. {#B10.39} *Action.* Φ is a homomorphism, so ρ_i(U)(∂p) = ρ_i(U(∂p)) and S(U) = Σ_ig_{0,i}^{−2}A_i(Φ(U)_i).
   {#B10.39-1} This and 2 give the
   {#B10.40} integral identity of (b); the product form is Fubini.
   {#B10.40-1} For the average: Φ is a surjective homomorphism of Lie groups
   {#B10.41} with finite kernel, so Φ^E: G^E → H^E is a finite covering map, whose fibres are the cosets Z^EU (Φ(U′_b) = Φ(U_b)
   {#B10.42} if and only if U′_bU_b^{−1} ∈ Z).
   {#B10.42-1} PF is constant on them, so PF = F̃∘Φ^E, with F̃ Borel because Φ^E has local
   {#B10.43} continuous sections.
   {#B10.43-1} For each z ∈ Z^E the substitution U ↦ zU preserves μ_G^E (a translation) and S (Φ(zU) = Φ(U)),
   {#B10.44} so ⟨F⟩_G = ⟨F(z·)⟩_G; averaging over z gives ⟨F⟩_G = ⟨PF⟩_G, and the integral identity, with F̃ and with 1, gives
   {#B10.45} ⟨PF⟩_G = ⟨F̃⟩_H.
4. {#B10.46} *Representations.* σ(z) is a scalar ω(z) for z ∈ Z (Schur).
   {#B10.46-1} If ω ≡ 1, σ factors through G/Z ≅ H. An irreducible
   {#B10.47} representation of H_1 × H′ is τ_1 ⊗ M: H′ commutes with H_1, so it preserves the H_1-isotypic components, and
   {#B10.48} irreducibility leaves one, τ_1 ⊗ M with M = Hom_{H_1}(τ_1, σ), on which H′ acts irreducibly (an invariant M′ ⊂ M
   {#B10.49} gives the invariant τ_1 ⊗ M′).
   {#B10.49-1} By induction σ ≅ σ_1 ⊗ ⋯ ⊗ σ_r, normalised traces multiply, and (b) gives the
   {#B10.50} product of expectations, since numerator and normaliser both factor.
   {#B10.50-1} If ω(z) ≠ 1 and C traverses b exactly once,
   {#B10.51} the substitution U_b ↦ zU_b preserves μ_G and S (Φ(z) = 1) and multiplies tr σ(U(C)) by ω(z)^{±1}, the sign being
   {#B10.52} the direction in which C traverses b, z being central; since ω(z)^{±1} ≠ 1, the expectation vanishes.
5. {#B10.53} *Flow.* By (b) with F = 1, the partition function of G is that of H, whose action is a sum over factors with
   {#B10.54} independent integration variables.
   {#B10.54-1} The product construction is therefore the tube construction of §0 run
   {#B10.55} separately on each H_i: the RG kernels multiply, the effective action at each step is the sum of the factors'
   {#B10.56} effective actions, and the flow of factor i involves only factor i's couplings and target.
   {#B10.56-1} Each H_i ⊂ U(N_i) is
   {#B10.57} a closed subgroup of U(N_i) (the setting of RG1 p.252 l.2), compact and connected (the image of G), with a simple Lie algebra and the Wilson action of its defining representation, so Theorem 0.1 applies to
   {#B10.58} it, in the form §0 gives for the tube construction. ∎

{#B10.59} The construction in (d) is defined on H. It is not RG1's construction on G with one coupling.
{#B10.59-1} The effective couplings
{#B10.60} are not observables, and by (b) every expectation of the G theory is an expectation of the product theory on H.

{#B10.61} *Which actions are additive.* Let G ⊂ U(N) carry the Wilson action of its defining representation ρ.
{#B10.61-1} If every
{#B10.62} irreducible summand of ρ is nontrivial on at most one factor, the action is additive with ρ_i the sum of the summands
{#B10.63} nontrivial on factor i, and g_{0,i}^{−2} = (N_i/N)g_0^{−2}: with N_0 the dimension of the trivial summands,
{#B10.64} 1 − Re tr ρ(V) = Σ_i(N_i/N)[1 − Re tr ρ_i(V)], because Σ_iN_i + N_0 = N. dρ_i is injective on g_i, because
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
{#B10.73} factor.

{#B10.74} The rest of this section concerns RG1's construction run directly on G, as needed for non-additive actions.

{#B10.75} **What carries over.**
- {#B10.76} The vacuum polarisation of RG1 (1.20) is block-diagonal: on g_i ⊗ g_i it is a multiple of the trace form, and the
  {#B10.77} blocks g_i ⊗ g_j (i ≠ j) vanish.
  {#B10.77-1} The statement "proportional to δ^{ab}" of RG1 p.264 holds only for r = 1.
- {#B10.78} The marginal terms are Σ_i ϑ_i A_i(U), with A_i a Wilson action of factor i, and there is no invariant marginal cross
  {#B10.79} term.
  {#B10.79-1} So there is one coupling and one β per simple factor, and the flow RG1 (0.20) becomes
  {#B10.80} 1/g_{k,i}² = 1/g_{k+1,i}² + β_{k+1,i}(g_0, …, g_k), i = 1, …, r, where g_j = (g_{j,1}, …, g_{j,r}) and the β's depend
  {#B10.81} on the whole vector history.
  {#B10.81-1} The bare action gives g_{0,i}^{−2} = λ_i′/g², with weights λ_i′ fixed by the embedding.
- {#B10.82} §§3–8 hold per factor, with c_i^N = (11/48π²)κ_i^N (Lemma 10.1's normalisation), because every polarisation is
  {#B10.83} block-diagonal.
- {#B10.84} The flow lemma holds for the coupling vector (RG1 (0.31) per factor; `BalabanFormal.flow_lemma`).
  {#B10.84-1} Clamp each component
  {#B10.85} as in Lemma 2.1, and take the box Π_i [t_i + b_iK − C, t_i + b_i′K + C].
  {#B10.85-1} (W) gives F_i ≤ t_i on the face
  {#B10.86} x_{0,i} = t_i + b_iK − C and F_i ≥ t_i on the face x_{0,i} = t_i + b_i′K + C, whatever the other components are.
  {#B10.86-1} The
  {#B10.87} Poincaré–Miranda theorem then gives a solution in the box, and step 4 of Lemma 2.1 applies componentwise.

{#B10.88} **What is OPEN.** For additive actions, Proposition 10.2 gives the tube-construction form of Theorem 0.1 for each factor
{#B10.89} of the product construction on H, with r bare couplings tuned independently.
{#B10.89-1} Not covered:
- {#B10.90} RG1's one-coupling construction on G, the model for which RG1 states Theorem 1 (p.259 l.23–24), even for additive
  {#B10.91} actions: its step terms have a marginal part Σ_iϑ_iA_i (Lemma 10.1), which one coupling does not absorb unless the
  {#B10.92} ϑ_i are in the ratio of the bare weights; at zero coupling this needs the c_i^N to be equal.
- {#B10.93} RG1's construction on G for non-additive actions, such as SO(4) ⊂ U(4), with a coupling vector.

{#B10.94} In both, the coupling-dependent thresholds of CRE and LFR2, which the construction of Theorem 0.1 uses in place of
{#B10.95} RG1's fixed ε₀ and ε₁ (§0, *Condition 3*), use a single coupling g_k: ε_k = g_kp₀(g_k) in CRE (2.4), δ_k on CRE p.265,
{#B10.96} and p₀(g_k) in LFR2 (1.86); for several factors they would be read with g_k := max_i g_{k,i}.
{#B10.96-1} RG1, RG2, CRE, and LFR1–LFR2 have not
{#B10.97} been re-verified with this substitution.
{#B10.97-1} For a non-additive action more than notation changes: A differs from every sum Σ_iϑ_iA_i of
{#B10.98} per-factor Wilson actions (for SO(4) by 2 at the plaquette value −1 ∈ SO(4), where every per-factor action vanishes), so RG1's form g_k^{−2}A(U_k) of the effective action,
{#B10.99} the background field as the minimiser of one action, and the large-field bounds would have to be restated.
{#B10.99-1} A unitary W with WGW* = G that permutes the factors transitively
{#B10.100} (for SO(4), W = diag(−1, 1, 1, 1)) would make one coupling suffice, if the construction were equivariant under
{#B10.101} U ↦ WUW*; that equivariance has not been checked against the sources.
{#B10.101-1} Until then, Theorem 0.1 is stated for simple G;
{#B10.102} for semisimple G with an additive action, Proposition 10.2 gives its tube-construction form per factor for the product
{#B10.103} construction on H.

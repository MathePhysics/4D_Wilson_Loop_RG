# The Beta Function for the Wilson-Loop Analysis

This file contains the coupling-flow results that the Wilson-loop renormalisation-group analysis uses, with their
proofs. It is extracted from `D:\University\Oxford PostDoc\Balaban\ONE_LOOP_PROOFS.md`. The proofs use Bałaban's papers,
cited by printed page and equation and pinned in `D:\University\Oxford PostDoc\Balaban\sidecar\QUOTES.md` or in a sidecar
contract (`D:\University\Oxford PostDoc\Balaban\sidecar\BalabanSidecar\`), and arguments given here. READINGS.md is
`D:\University\Oxford PostDoc\Balaban\READINGS.md`.
- RG1 = CMP 109; RG2 = CMP 116; CRE = CMP 119; LFR2 = CMP 122 355–392;
- PRT1 = CMP 95; PBG = CMP 99 389–434; VAR = CMP 102 277–309.

G is a compact simple group, d = 4, and L is odd. The semisimple case is the open future direction of §10.

## 0. The Result

The coupling flow is RG1 (2.15), p.268, as in RG1 (0.20):

  1/g_k² = 1/g_{k+1}² + β_{k+1}(g_0, …, g_k),

where β_{k+1} is defined by RG1 (1.20)–(1.22), p.264, from the step term of RG1 (1.6), and b_{k+1} is its value at
zero coupling (Remark 2.3). The step terms are those of RG1's construction run with CRE's fluctuation cutoff
δ_k = g_k(A₁/A₀)p₀(g_k) (CRE p.265, (3.16) p.268) on RG1's fixed domains (§0, *Condition 3*). Let κ > 0 be defined by
K = κ·tr (Lemma 1.1), and put c := (11/48π²)κ. Notation: the letters δ, K, and κ carry several meanings, each fixed
by its context, as in the sources. δ without an index is the window constant of item 3 in §§0 and 2, and a decay or
smallness constant of RG2, CRE, or UV3 where those are quoted (RG2 (1.36), Proposition 2.4, step 2, Lemma 2.8, CRE
p.251); δ_k = g_k(A₁/A₀)p₀(g_k) is CRE's cutoff (δ_0 at step 0, δ^T_k in the tube construction), and δ₀ is the decay
rate of VAR and UV3. K is the Killing form in Lemma 1.1 and Lemma 6.5, ker Q or Hess A − h where §§3 and 6 say so,
and otherwise the number of steps of a target (K, g); K_R (Proposition 2.11) is a constant. κ is the Killing ratio in
c and in Lemma 6.5, and otherwise the decay constant of RG2 and CRE (as in exp(−κd_j(X))).

**Theorem 0.1 (Coupling Flow).** There are constants γ > 0, C and δ ∈ (0, 2c ln L), independent of k, of the history
and of the torus, with the following properties (RG1 (0.31), LFR2 (1.86), CRE (2.4); proofs below).
1. *Window* (Theorem 8.1). For all 0 ≤ m ≤ n, |Σ_{j=m+1}^{n} b_j − 2c(n − m) ln L| ≤ C.
2. *Matching* (Corollary 8.2, RG1 Theorem 2 for simple G). Put γ′ := (γ^{−2} + C)^{−1/2}. For every K and every
   renormalised coupling g ∈ (0, γ′] there is a bare coupling g_0(ε, g), ε = L^{−K}, independent of the torus, whose
   flow has g_K = g and g_k ∈ (0, γ] for 0 ≤ k ≤ K.
3. *Logarithmic window.* For 0 ≤ k ≤ K,
   g^{−2} + (2c ln L − δ)(K − k) − C ≤ g_k^{−2} ≤ g^{−2} + (2c ln L + δ)(K − k) + C.
   This is RG1 (0.31) with β = 2c − δ/ln L and β′ = 2c + δ/ln L, up to an additive constant.
4. *Near-monotonicity.* g_k^{−2} ≥ g_l^{−2} − C for k ≤ l. This gives the comparison of thresholds in LFR2 (1.86)
   (Remark 2.2).
5. *Remainder.* With CRE's fluctuation cutoff δ_k = g_k(A₁/A₀)p₀(g_k) (CRE p.265, (3.16) p.268),
   |β_{k+1}(h) − b_{k+1}| ≤ C_rem g_k² for every history h with entries in (0, γ] (Proposition 2.9). So 1/g_{k+1}² = 1/g_k² − b_{k+1} + O(g_k²).

Proposition 2.4 gives δ = c ln L. Under the conditions of Proposition 2.9, δ = C_remγ² is also admissible, so the rate
in item 3 tends to 2c ln L as γ → 0 (RG1 (0.31), CRE (2.4)).

Theorem 0.1 holds under the following conditions. §9 lists them with the other inputs taken from Bałaban, and
separately the arguments of this file that extend Bałaban's statements.

Conditions:
1. VAR (189), stated in VAR without proof, enters through Lemma 2.5 (sidecar node VAR_189).
2. RG2's sketch on p.11 for the terms of P^{(k)} other than V enters item 5 (Lemma 2.7, step 2).
3. The parts of RG1 Theorem 3 with RG2 that §§2.1–2.2 use (the bound RG1 (1.18), and the analyticity of the step terms
   in (U, J) on RG1's fixed domains), run with CRE's fluctuation cutoffs δ_j = g_j(A₁/A₀)p₀(g_j), enter items 2–5:
   through (P2) and (C) (the remark after Proposition 2.6) and through Proposition 2.9. RG1 Theorem 3 is Bałaban's;
   the transfer of these parts to the cutoffs δ_j is derived below (*Condition 3*).
4. PBG's analyticity and decay away from U = 1, for the averaging of RG1 (0.4), enter Proposition 7.1 as Bałaban states
   them.
5. VAR Theorem 1 rests on the sketched Theorem 8 of CMP 99 389–434 and enters §§5 and 7 through the analyticity of U_k(V).

*Scope.* CRE Theorem 1 (CRE p.262) takes the coupling inequalities "(I.0.33)" as its hypothesis: if the sequence {g_k}
of the renormalisation group equations satisfies them, the densities ρ_k satisfy CRE's inductive assumptions. RG1 has
no (0.33); its introduction ends at (0.32), and CRE p.246 cites "(0.33) [I]" for γ₀^{−2} = γ^{−2} + β log ε^{−1}, which
is RG1's printed (0.31), p.259. Item 3 has the form of (0.31). Item 1 is the input from which Lemma 2.1 derives items 2,
3, and 4; item 2 provides the flow on which items 3 and 4 hold; and item 4 is the comparison of LFR2 (1.86). Theorem 0.1
is stated for the coefficients β_j of the construction named before it.

CRE's flow equation (2.24), p.259, uses its own coefficients β_j(g_{j−1}), which CRE (2.25), p.259, subtracts from its
step terms (and p.279 for j = k+1). They differ from ours by the contribution of the R-terms (*Identification* and *The
R-terms* below). CRE's coefficient β_{k+1}(g_k) is built from the whole-lattice term E^{(k+1)} (CRE (3.57), p.281;
p.278), and g_{k+1} enters step k only through the localisation of the new density. CRE's printed construction is not a
continuous function of the history because its parameters (the integers R_j, k₁, N₀, and the depth N, the thresholds,
and the domain radii) jump or move with the couplings (*CRE's Construction as a Function of the History*, §2.2). The
*tube construction* for a target (K, g) evaluates all of these parameters at couplings fixed by the target
(Lemma 2.10). For it:
- the R-terms shift β_j by at most C_Rg_k^{κ₀−4} relative to RG1's construction run with the tube cutoffs δ_j^T
  (Proposition 2.11), on the histories of the tube H_k; Propositions 2.4 and 2.9 hold for the latter on H_k
  (Lemma 2.10, step 7). So on H_k the per-step bounds of hypothesis (W) hold with δ′ = δ + C_Rγ^{κ₀−4} in place of
  δ, and item 5 holds with C_rem + C_Rγ^{κ₀−6} in place of C_rem (*Consequence*, after Proposition 2.11);
- its β_j is continuous on H_k (Proposition 2.12), and item 2 holds (Proposition 2.13), with γ′ as in item 2; item 3
  holds along the matched flow of Proposition 2.13 with δ′ in place of δ, and item 4 holds along it;
- the bare coupling of item 2 is independent of the torus, because β_j^T, like CRE's β_j, is defined by RG1's
  definition (I.1.22) (CRE p.282), that is, by the limit of the polarisation as T^{(j)} ↗ ℤ^d (RG1 (1.21), p.264),
  computed from (2.26) for Λ_j = L^{−j}ℤ^d (CRE (3.63), p.282). The limit exists, and is approached uniformly in the
  history, by the localisation through the random-walk expansions (Proposition 2.12, step 5).
These statements are for the tube construction, at every depth k ≤ K of each target. They are not statements about CRE's
printed construction (*What Is Proved for β_j*, after Proposition 2.13). They rest on the inputs that §9 lists for the
tube construction (CRE's inductive estimates, LFR1, LFR2, UV3, CMP98, REG, and VAR as CRE uses them), on Conditions
1–3 through Propositions 2.4 and 2.9 with δ_j^T, and on the arguments of this file that §9 lists separately: the
identification of the regular part of β^T with RG1's construction run with δ_j^T, the tube construction with its
convention for histories that are not flows, the parameter choices p₀ > (d+5)r + ⌈r⌉ + 2 and q₀, q₁ > p₀,
Lemma 2.10, Lemma 2.5 on the (2.28) domains, the step with complex multiples of the R-terms, Theorem 8.1 with
Remark 2.3, and Propositions 2.12 and 2.13.

*Condition 3 (derived).* The estimates of §§2.1–2.2 use RG1 Theorem 3 with CRE's fluctuation cutoff
δ_k = g_k(A₁/A₀)p₀(g_k) (CRE p.265, (3.16) p.268) in place of the fixed cutoff ε₁ of RG1 (2.9), p.266, on RG1's fixed
domains U^c_{k+1}(X, α₀, α₁). Here p₀(g) = A₀(log g^{−2})^{p₀} (CRE (2.4), p.255) and A₀ ≫ A₁ (CRE p.247). The cutoff
applies to the field-scale fluctuation g_kA_k, so its unit-scale form is δ_k/g_k = A₁(log g_k^{−2})^{p₀}
(`D:\University\Oxford PostDoc\Balaban\READINGS.md` R43, CRE p.267). CRE's ε_k = g_kp₀(g_k) is the plaquette threshold,
the analogue of RG1's ε₀ (CRE (3.2), p.265), and it is not the fluctuation cutoff. The proof of RG1 Theorem 3
(RG1 §§2–3, RG2 §§1–2) uses the cutoff in three ways only:
- *Upper bounds on ε₁.* These are RG1 p.265 (the integration domain lies in U_k(ε₀)), p.269 (coefficients O(ε₁)), and
  p.273 ("ε₁ is so small that"), pp.276 and 280 ("ε₁ sufficiently small"); and RG2 pp.6–9, p.11, p.16 (the radius 1/|τ(Y)| ∝ ε₁), p.18 (the
  assumption 2E₀ε₁C₁α₄^{−1}α₆^{−1}M^q e^{C₂κ₁}e^{5κ} ≤ 1), p.20, and p.21 (O(1)C₃ε₁ ≤ ½E₀). The auxiliary ε₃ = C₁ε₁ of
  RG2 p.6 is of this kind. They hold with δ_k for γ small, because δ_k ≤ ε_k ≤ γp₀(γ) → 0 as γ → 0.
- *Lower bounds on ε₁/g_k (the Gaussian tail).* These are RG2 p.12 (χ^c_{k,P}), (2.22), (2.26), (2.31), p.16 (the tail
  bound), p.17, p.18 (the bracket and γ₂ε₁²/(20γ²) ≥ 4κ), (2.33) and (2.34), p.19. With δ_k the ratio is
  δ_k/g_k = A₁(log g_k^{−2})^{p₀} ≥ A₁(log γ^{−2})^{p₀}, which tends to ∞ as γ → 0. RG2 prints the conditions of
  pp.18–19 with γ in place of g_k: it passes from exp(−γ₂ε₁²/(20g_k²)) to exp(−γ₂ε₁²/(20γ²)) through g_k ≤ γ
  (RG2 p.18, "(1/20)γ₂ε₁²/g_k² ≥ (1/20)γ₂ε₁²/γ² ≥ 4κ", and (2.33)–(2.34), pp.18–19). With a cutoff that tends to 0 with g_k, the γ-form fails for g_k ≪ γ, so the conditions are re-derived at g_k
  from the same estimates. RG2 p.19 prints "ε₂ = 2E₀ε₁C₁α₄^{−1}α₆^{−1}M^q exp C₂κ₁", so ε₂ is proportional to the
  cutoff, and the condition of p.19 becomes exp(−γ₂A₁²(log g_k^{−2})^{2p₀}/20) ≤ c_εδ_k with
  c_ε := 2E₀C₁α₄^{−1}α₆^{−1}M^q e^{C₂κ₁}. Since 2p₀ > 1, the left side is smaller than any power of g_k for g_k small, so it holds for
  g_k ≤ γ small, as in Proposition 2.9, step 6. The condition of p.18, γ₂δ_k²/(20g_k²) ≥ 4κ, holds once
  γ₂A₁²(log γ^{−2})^{2p₀} ≥ 80κ.
- *Comparisons within one step.* RG1 p.267 bounds B′(b₀(c)) by O(ε₁), with the cutoff of the same step.

The inductive assumptions RG1 (1.1)–(1.22) do not contain ε₁, and no estimate compares the cutoffs of two steps. So the
parts of RG1 Theorem 3 that §§2.1–2.2 use, the bound (1.18) and the analyticity of the step terms in (U, J) on the fixed
domains, hold with the cutoffs δ_j for γ small. The gauge invariance and Euclidean covariance of the step terms, which
the definition of β by RG1 (1.21)–(1.22) and the scalar Π of Lemma 2.5 use, hold for any cutoff that is invariant under
Ad(G) and the lattice symmetries, as δ_j is. The clause of RG1 p.263 that E^{(j)} is a C^∞ (or analytic) function of
g_{j−1} is not transferred to a coupling-dependent cutoff and is not used; continuity in the couplings is
Proposition 2.6.

*Identification with CRE's construction.* CRE builds its step terms with the formulas of RG1: "All the applied formulas
are the same as in Sect. 2 [I], only the symbols represent different operators, determined by the sequence {Ω_j}" (CRE
p.267). Of the result it states: "the terms E₀^{(k+1)}(Λ_{k+1}, X, z) of this representation, for X ⊂ Λ_{k+1}, do not
depend on Λ_{k+1}, and coincide with the corresponding terms arising from the expressions defined on the whole lattice,
i.e. in the framework of [I]" (CRE p.278). "The framework of [I]" means RG1's whole-lattice formulas, run with CRE's
inputs (its cutoff δ_k and E_k with R′_k folded in), not RG1's construction itself. The last logarithm of CRE (3.28) "is formally given by the same formula as
the term E^{(k+1)} in [I] [see (2.12), (2.13)], but the integral is restricted to Λ_{k+1}, and operators are determined
by the sequence {Ω_j}" (CRE p.272), and for Ω_j = Λ_j = T_η "the expressions (3.37) coincide with the expressions in the
inductive assumption" (CRE p.274). Those expressions include R′_k (p.271), and their Euclidean covariance (3.39)
follows from (2.29) and from (2.32), p.260, the covariance of the R-terms (p.274). CRE (2.24) defines the couplings
g_{j−1} "as in (I.0.20)" (p.259), with CRE's own β_j. CRE's coefficient is built from the whole-lattice step term alone: Π^{(j)} in CRE
(3.57), p.281, is "given by the formula (3.50), but with E^{(j)}(X, U_j, z) replaced by E^{(j)}(U_j, z) defined on the
whole lattice", so the terms R″^{(k+1)} and B^{(k+1)} do not enter it. CRE (3.61), p.282, defines β′_j = Π^{(j)}_{22,11},
and CRE proves that "it coincides with the definition (I.1.22)": (3.62) uses translation invariance and the identity
(I.4.15), and (3.63) follows from (2.26) for Λ_j = L^{−j}ℤ^d and the definitions (I.1.20) and (I.5.1) (CRE p.282); CRE (3.64), p.283, gives β′_j = −½Σ_xΠ^{(j)}_{22}(x)x_1² = β_j. CRE (3.67), p.283, then asserts that
E^{(j)}(U) − E^{(j)}(1) − β_jA(h_z, U) is irrelevant; since A(h_z, U) is marginal, CRE's β_j is the marginal coefficient
of CRE's own E^{(j)}. CRE p.253 points to "(1.41)–(1.43)" of [I] for β₁; RG1 §1 ends at (1.22), and
the pointer is not used.

*The R-terms.* Before step k+1, CRE folds R′_k := Σ_{j=1}^{k₁}R^{(j)} into E_k: "It has the same covariance
property as the expression determined by E_k, and we include it into E_k" (CRE p.271). So the bracket
{E_k(U_k(…)) − E_k(U_{k+1})} whose fluctuation integral gives E^{(k+1)} contains R-terms. The R-terms do not vanish on
the small-field density: the R-operation (LFR1 (0.3), p.176) integrates out the renormalised regions Z′ and leaves
their quotients on the density of Z″ as exp Σ_X ℝ(X, V) (LFR1 (0.5)–(0.6), p.176), also for Z″ = ∅. Hence CRE's
β_j = β_j^δ + β_j^R, where β_j^δ is the coefficient of RG1's construction run with δ_j (the β_j of §§2.1–2.2) and β_j^R
is the change of the coefficient caused by the R′-terms. For the tube construction the same split holds with β_j^{δ,T},
the coefficient of RG1's construction run with the tube cutoffs δ_j^T, in place of β_j^δ, and Proposition 2.11 bounds
the R-part: |β^T_{k+1} − β^{δ,T}_{k+1}| ≤ C_R g_k^{κ₀−4} on the histories of the tube, with κ₀ ≥ 7 (CRE (2.31), p.260;
(2.46), p.263). Propositions 2.4 and 2.9 hold for β^{δ,T} on the histories of the tube (Lemma 2.10, step 7). Item 5,
with C_rem + C_Rγ^{κ₀−6}, and the per-step bounds of (W), with δ′ = δ + C_Rγ^{κ₀−4}, then hold on the histories of the
tube (Proposition 2.11, *Consequence*); item 2, and items 3 (with δ′) and 4 along the matched flow, hold by
Propositions 2.12 and 2.13.

*CRE's Step Terms and β_j (checked against CRE pp.259, 267, 271, 272, 274, 278, 279, and 281–283, corrected transcriptions).*
- The step is RG1's whole-lattice construction (RG1 §2): "All the applied formulas are the same as in Sect. 2 [I]"
  (p.267), and the last logarithm of (3.28) "is formally given by the same formula as the term E^{(k+1)} in [I]" (p.272).
- Its cutoff is CRE's δ_k: the characteristic function of (3.16), p.268, with δ_k = g_kA₁/A₀p₀(g_k) (p.265).
- The only additional input is R′_k, which "we include … into E_k" (p.271). The R-terms otherwise get "the vacuum
  energy renormalization only" (p.259). Once R′_k is inside E_k, its contribution to the fluctuation integral of the
  next step enters E^{(k+1)} and is coupling-renormalised with it ((3.57), p.281).
- β_j is built from the whole-lattice E^{(j)} ((3.57), p.281), so R″^{(j)} and B^{(j)} do not enter it, while the R′-part
  does. It is the second moment of the polarisation of that E^{(j)} ((3.61)–(3.64), pp.282–283).
- CRE (3.67), p.283, leaves only an irrelevant remainder after β_jA(h_z, U) is subtracted, which holds only for the
  coefficient of CRE's own E^{(j)}.

CRE (2.28), p.259, states analyticity of CRE's step terms on smaller domains, α_{0,j} = g_jC_0(log g_j^{−2})^{q_0}, for its
localised bounds. CRE's localised pieces (CRE (3.37), (3.41), (3.44)–(3.47)) are not RG2's (RG2 (2.1)–(2.13)). Without R-terms
(s = 0 in Proposition 2.11) their sums coincide with RG2's whole-lattice terms up to an additive constant, and CRE's side
contains the Gaussian term log Z^{(k)}, which RG2's step term excludes (CRE (3.42), p.275); the constant does
not contribute to β, which is a second derivative in B, and log Z^{(k)} enters β on both sides through
β_{k+1} = Λ(log Z^{(k)}) + Λ(E^{(k+1)}_fl) (Proposition 2.4, step 1; Remark 2.3, *What β is*). β^δ depends only on the second
derivatives of the sum at B = 0 (RG1 (1.20)), and §§2.1–2.2 bound it through RG2's own pieces on the fixed domains. So
(2.28) is not needed for β^δ. On the domains of (2.28) alone the Cauchy radius of Lemma 2.5 would be proportional to
α_{0,j}, and Proposition 2.4 would not give a small bound (`WILSON_CAUCHY_LIPSCHITZ_2026_10_21.md`, *What changes on
CRE's domains*). The R-part β^R is bounded on the domains of (2.28), with the tube radii; there only the size
C_Rg_k^{κ₀−4} is needed, which the factor g_k^{κ₀} supplies (Proposition 2.11, steps 5–6).

*Proof map.*
- Theorem 8.1 (item 1) comes from the exact decomposition ℒ_k = F_k − F_0 + 𝒥_k of the k-step Gaussian (§3) and four
  estimates of its polarisation at a fixed momentum:
  - the total (Proposition 5.1);
  - the top-level part (Proposition 7.1);
  - the bare part (Proposition 6.4, with Proposition 6.3 and the value of c from Lemma 6.5);
  - the J-terms (Proposition 5.3, with Proposition 4.2 and Lemma 5.2).
- Propositions 2.4 and 2.6 give the history bound (P2) and the continuity (C) of β. Remark 2.3 turns item 1 into
  hypothesis (W) of the flow lemma, and Lemma 2.1 gives items 2–4 (Corollary 8.2).
- Proposition 2.9 gives item 5.
- Lemma 2.10 defines the tube construction, CRE's construction with its parameters fixed by the target (K, g), and
  shows that the estimates of CRE, LFR1, and LFR2 hold for it.
- Proposition 2.11 bounds the R-part of the β_j of the tube construction; with Propositions 2.4 and 2.9 for the tube
  cutoffs it gives item 5 and the per-step bounds of (W) on the histories of the tube.
- Propositions 2.12 and 2.13 give its continuity, item 2, and items 3 and 4 along the matched flow.

## 1. One β for Simple G

Let G ⊂ U(N) be compact simple, with Lie algebra g.

**Lemma 1.1.** Every Ad(G)-invariant symmetric bilinear form on g is a multiple of the Killing form K. In particular the
trace form tr(XY) of the defining representation (normalised trace, tr 1 = 1) is κ^{−1}K, with κ > 0 defined by
K = κ·tr.

*Proof.* Ad(G) acts irreducibly on g, over ℝ, and its complexification is irreducible because g is compact simple. By
Schur's lemma an invariant form is a multiple of K. ∎
References (page images read): B. Simon, *Representations of Finite and Compact Groups* (AMS GSM 10, 1996): invariance
of K, Prop. VIII.2.1(b); K negative definite, Prop. VIII.2.2; uniqueness of the invariant inner product for irreducible
orthogonal representations, with the Schur remark, Prop. VIII.2.3; Ad irreducible ⇔ g simple, and the definition of
simple, Thm. VIII.2.4.

Examples: κ = 2N² for SU(N) ⊂ U(N); κ = C₂(G)/λ in general, where tr = λ·⟨·,·⟩_std on g.

**Consequences.**
1. The vacuum polarisation Π^{ab}_{μν} of RG1 (1.20) is Ad-invariant in (a, b), so it is a multiple of the trace form.
   This is the statement "proportional to δ^{ab}" of RG1 p.264.
2. The marginal (dimension-4) gauge-invariant local terms are multiples of the Wilson action
   A(U) = Σ_p [1 − Re tr U(∂p)]. So there is one coupling and one β, the effective action has the form RG1 (1.3) and
   (1.6), and the flow is RG1 (0.20).

## 2. The Flow Lemma (Window Form)

Work with x_k := g_k^{−2}. The flow RG1 (0.20) reads x_k = x_{k+1} + β_{k+1}(h_k), where h_k := (g_0, …, g_k) is the
history. Fix γ > 0, and let 𝓗_γ be the set of histories with all entries in (0, γ].

**Hypotheses.**
- **(W)** There are constants 0 < b ≤ b′ and C such that for all 0 ≤ m ≤ n and all histories in 𝓗_γ:
  b(n−m) − C ≤ Σ_{j=m}^{n−1} β_{j+1} ≤ b′(n−m) + C. This is the window of RG1 (0.31), stated for β.
- **(C)** Each β_{j+1} is continuous on 𝓗_γ.

**Lemma 2.1.** Assume (W) and (C). Let γ′ := (γ^{−2} + C)^{−1/2}. For every K and every g ∈ (0, γ′] there is a bare
coupling g_0 whose flow stays in 𝓗_γ up to step K and has g_K = g. Moreover, for all 0 ≤ k ≤ K (RG1 (0.31)):
- (i) g^{−2} + b(K−k) − C ≤ g_k^{−2} ≤ g^{−2} + b′(K−k) + C, i.e. RG1 (0.31) with β = b/ln L, β′ = b′/ln L, up to an
  additive constant;
- (ii) g_k^{−2} ≥ g_l^{−2} − C for k ≤ l (near-monotonicity).

*Proof.* The type-checked Lean core is `BalabanFormal.flow_lemma`. It is stated for a vector of couplings, with the
Poincaré–Miranda theorem as a hypothesis; for one coupling that hypothesis is the intermediate value theorem.
1. *Clamping.* Let c(x) := max(x, γ^{−2})^{−1/2} ∈ (0, γ]. Define the clamped flow by
   x_{k+1} := x_k − β_{k+1}(c(x_0), …, c(x_k)). It is defined for all x_0 ∈ ℝ and is continuous in x_0 by (C). Let
   F(x_0) := x_K.
2. *The interval.* Let t := g^{−2}. Clamped histories lie in 𝓗_γ, so (W) with m = 0, n = K gives
   F(x_0) ∈ [x_0 − b′K − C, x_0 − bK + C]. At x_0 = t + bK − C this gives F(x_0) ≤ t, and at x_0 = t + b′K + C it
   gives F(x_0) ≥ t.
3. *Intermediate values.* F is continuous on [t + bK − C, t + b′K + C], so it takes the value t at some x_0 there.
4. *The clamping is inactive.* For this solution, (W) on the window [k, K) gives
   x_k = t + Σ_{j=k}^{K−1}β_{j+1} ≥ t + b(K−k) − C ≥ γ^{−2}, using t ≥ γ^{−2} + C. So c(x_k) = x_k^{−1/2} at every step,
   and the clamped flow is the true flow, inside 𝓗_γ. Then (i) is (W) on [k, K), and (ii) is (W) on [k, l). ∎

**Remark 2.2 (What LFR2 (1.86) Needs).** Part (ii) and g_l^{−2} ≥ γ^{−2} give
log g_k^{−2} ≥ log g_l^{−2} + log(1 − Cγ²) ≥ log g_l^{−2} − 2Cγ² for k ≤ l, once Cγ² ≤ ½. Hence
p₀(g_k) ≥ (1+β₀)^{−1} p₀(g_l) once γ is small, which is the comparison used in LFR2 (1.86).

**Remark 2.3 (From b to β).** Suppose that the zero-coupling coefficients satisfy (W) with constants 2c ln L, 2c ln L and
C₀ (Theorem 8.1), and that (P2) holds: |β_{j+1}(h) − b_{j+1}| ≤ δ on 𝓗_γ. Then (W) holds for β with
b = 2c ln L − δ, b′ = 2c ln L + δ and C = C₀, and b > 0 for δ < 2c ln L. So RG1 Theorem 2 (RG1 p.259) reduces to
Theorem 8.1 together with (P2) and (C), which §2.1 derives. The type-checked Lean core is
`BalabanFormal.coupling_flow_of_stepBound`.

*What β is.*
- RG1 defines β_{j+1} by (1.20)–(1.22), p.264, from the step term E^{(j+1)} of RG1 (1.6), which contains the Gaussian
  term log Z^{(j)} (compare RG1 (1.3), p.260).
- By RG1 (2.12)–(2.13), p.268, E^{(j+1)}(g_j, U) = log Z^{(j)}(U) + log ∫ χ_j exp[P^{(j)} + {…}] dμ_{C^{(j)}(U)}, and
  the exponent vanishes at g_j = 0.
- The earlier couplings enter only through {…}: the previous interaction at the fluctuating configuration, minus its
  value at the background.
- At g_j = 0 the exponent vanishes, and the cutoff χ_j = Π_b χ({|g_j(CB)(b)| < ε₁}) of RG1 (2.9) is identically 1.
  Hence β_{j+1}(0; h) = b_{j+1} exactly.

Neither (P2) nor (C) is stated in RG1 or RG2. The smoothness statement after RG1 (1.22) comes without proof. §2.1
derives both from RG2's published bounds.

### 2.1 The History Dependence: (P2) and (C)

Write E^{(k+1)}_fl for the fluctuation integral RG1 (2.13), so that the RG1 (1.6)-form step term is
[log Z^{(k)}(U) − log Z^{(k)}(1)] + E^{(k+1)}_fl. RG2 represents E^{(k+1)}_fl = Σ_X E^{(k+1)}_fl(X) by an exponentiated
cluster expansion. G is simple, so there is one coupling.

**Proposition 2.4 (P2).** There are constants C_Λ and C₃, independent of k, of the history and of the cutoff ε₁, such
that for every k and every history h ∈ 𝓗_γ (RG2 (2.41); proof below)
  |β_{k+1}(h) − b_{k+1}| ≤ C_Λ C₃ ε₁.

Every condition on ε₁ in RG1–RG2 is an upper bound (step 4, from RG2 pp.7, 18, 20 and 21). So ε₁ can be chosen with
C_Λ C₃ ε₁ ≤ c ln L, and γ is then chosen small. This gives (P2) with δ = c ln L.

*Proof.*
1. *Split.* β is linear in the step term (RG1 (1.20)–(1.22)). Write Λ for this linear map, so that
   β_{k+1}(h) = Λ(log Z^{(k)}) + Λ(E^{(k+1)}_fl(·; h)). At g_k = 0 the exponent in RG1 (2.13) vanishes and χ_k ≡ 1, so
   E^{(k+1)}_fl = 0. Hence b_{k+1} = Λ(log Z^{(k)}), the zero-coupling coefficient of Theorem 8.1, and
   β_{k+1}(h) − b_{k+1} = Λ(E^{(k+1)}_fl(·; h)).
2. *The step bound.* RG2 (2.41), p.21, gives on U^c_{k+1}(X, α₀, α₁):
     |E^{(k+1)}_fl(X)| ≤ O(1) C₃ ε₁ exp(−κ d_{k+1}(X)),  C₃ = 2(L+2)⁴O(1)·2E₀C₁α₄^{−1}α₆^{−1}M^q e^{C₂κ₁}
   (RG2 p.20), using (1−10δ)½L = 1. The factor ε₁ comes from Lemmas 1–3 of RG2. On the cutoff region the unscaled
   fluctuation is |g_kCB| < ε₁, so the interaction V_k is O(ε₁): RG2 (1.36), (1.43); RG1 p.269 ("coefficients of the
   order O(ε₁)"). The cutoff complement contributes exp(−γ₂ε₁²/(20γ²)) ≤ ε₂ (RG2 (2.22), (2.33)). The earlier
   couplings enter only through E_k. RG1 Theorem 3 gives E_k the inductive bounds RG1 (1.18) for every sequence in
   (0, γ], so RG2 (2.41) is uniform in the history.
3. *Polarisation.* Lemma 2.5 gives |Λ(F)| ≤ C_Λ A for localised F with |F(X)| ≤ A e^{−κd_{k+1}(X)}. Take
   A = O(1)C₃ε₁ (RG2 (2.41)).
4. *Constants.* The conditions on ε₁ are all upper bounds, given κ, κ₁, M, the α's, E₀ and L:
   - RG2 p.7: e^{32κ₁}ε₁ below an absolute constant, and 4B₀C₁e^{16κ₁}ε₁ ≤ ¼α₂;
   - RG2 p.18: 2E₀ε₁C₁α₄^{−1}α₆^{−1}M^q e^{C₂κ₁}e^{5κ} ≤ 1;
   - RG2 p.20: 2(L+2)⁴O(1)ε₂e^{5κ} ≤ 1;
   - RG2 p.21: O(1)C₃ε₁ ≤ ½E₀;
   - RG1 p.273, RG1 p.276 and RG1 p.280: "ε₁ is so small", "ε₁ sufficiently small".

   γ enters only through exp(−γ₂ε₁²/(20γ²)) ≤ ε₂ and γ₂ε₁²/(20γ²) ≥ 4κ (RG2 pp.18–19), conditions on γ chosen last.
   C_Λ depends on κ, δ₀, α₀, α₁, d, M and L, and C₃ on the constants listed. Neither depends on ε₁. ∎

**Lemma 2.5 (The Polarisation Is Bounded).** Let F = Σ_X F(X), with F(X) analytic on the space U^c_{k+1}(X, α₀, α₁) of
RG1 (1.11)–(1.16) and depending on (U, J) restricted to X, and |F(X)| ≤ A e^{−κd_{k+1}(X)}, as in RG2 (2.41). Put
Π(x) := ∂²F(U_{k+1}(e^{iB}))/∂B_μ(0)∂B_ν(x) at B = 0, and Λ(F) := Σ_x Π(x)x_μx_ν (μ ≠ ν). Then |Λ(F)| ≤ C_Λ A.

*Proof.* Write u(B) for the configuration (U_{k+1}(e^{iB}), J_{k+1}) restricted to X, and ‖·‖ for the norms in which
the conditions of U^c_{k+1}(X, α₀, α₁) are stated.
1. *The background map.* B ↦ U_{k+1}(e^{iB}) is analytic for small complex B. Its functional derivative decays
   exponentially, with rate δ₀ (VAR Prop. 9, p.309, and VAR (190); RG1 p.271). So ‖∂u/∂B(y)‖ ≤ C e^{−δ₀ dist(y,X)}.
   *Input status.* VAR p.308 derives VAR (190) from VAR (189), and VAR (189) is stated without proof ("We do not
   perform these calculations here"). So this step rests on a published estimate stated without proof (sidecar node
   VAR_189).
   Apply Cauchy's estimate in the single variable B(y′), on a disc of fixed radius, to ∂u/∂B(y). This gives
   ‖∂²u/∂B(y)∂B(y′)‖ ≤ C e^{−δ₀ dist(y,X)}. By symmetry the same holds with dist(y′, X), so the bound is
   C e^{−δ₀(dist(y,X) + dist(y′,X))/2}.
2. *Cauchy in the configuration.* Restrict F(X) to the lines u + t v and u + t v + s w. This gives
   |DF(X)[v]| ≤ A e^{−κd(X)}‖v‖/r and |D²F(X)[v, w]| ≤ 2A e^{−κd(X)}‖v‖‖w‖/r², with r > 0 depending on α₀, α₁ only.
3. *Chain rule.* Π(x) = Σ_X (D²F(X)[∂_{B(0)}u, ∂_{B(x)}u] + DF(X)[∂²_{B(0)B(x)}u]). By steps 1 and 2, the X-term is
   at most C A r^{−2} e^{−κd(X)} e^{−δ₀(dist(0,X) + dist(x,X))/2}.
4. *Sum.* Σ_x |x|² e^{−δ₀ dist(x,X)/2} ≤ C(1 + diam X + dist(0, X))^{d+2}. The remaining sum over X of
   e^{−κd(X) − δ₀dist(0,X)/2} times this polynomial converges for κ large, because d(X) ≥ cM^{−4}|X| (RG2 (2.30)). ∎

This is the argument behind RG1 p.264 (existence of the limit RG1 (1.21) and boundedness of β). It is linear in A.

**Proposition 2.6 (C).** For each k, h ↦ β_{k+1}(h) is continuous on (0, γ]^{k+1}.

*Proof.* Induction on k. The claim S_k is: for every X, E^{(k+1)}_fl(X; h) is continuous in h, uniformly for
(U, J) ∈ U^c_{k+1}(X, α₀, α₁).
1. *Where the couplings enter.* In RG2's representation RG2 (2.1)–(2.14), the operators, covariances and measures
   (C^{(k)}, Γ_k, dμ₀ and the s-dependent propagators) depend on (U, J) only. The couplings enter in two ways:
   - (a) the potentials V_k(Y, B) of RG2 Lemma 2 (p.11);
   - (b) the indicators χ_{k,Y₀} and χ^c_{k,P}, whose threshold is ε₁/g_k (RG2 (2.3)).
2. *(a) is continuous.*
   - P^{(k)} is an explicit analytic function of g_k and g_kCB (RG1 (2.12)).
   - {…} = E_k(U_k(exp i[g_kCB − hD̃(g_kCB)]V)) − E_k(U_k(V)). E_k is continuous in its couplings by S_j for j < k,
     together with the continuity of β_j.
   - The localisation in RG2 (1.10), (1.23) and (1.38) uses s-integrals over [0, 1] and Cauchy integrals over fixed
     circles. Both preserve continuity, with bounds uniform in the history.
3. *(b) is continuous almost everywhere.* Fix B with |B(b)| ≠ ε₁/g_k⁰ for all b. Then the indicators are constant for
   g_k near g_k⁰. The exceptional set is a finite union of sets {|B(b)| = t}, which are null for the nondegenerate
   Gaussian measures in RG2 (2.14).
4. *Dominated convergence.* The integrand of RG2 (2.14) has the majorant RG2 (2.15)–(2.25). It is integrable and uniform
   in the history and in (U, J). So each term RG2 (2.14) is continuous in h, uniformly in (U, J).
5. *Uniform convergence.* The sums over D, P and Z₀, and the polymer series RG2 (2.12)–(2.13), are dominated by
   RG2 (2.26)–(2.41) uniformly in the history. So E^{(k+1)}_fl(X; ·) is continuous: this is S_k. The base case S_0 has
   {…} = 0.
6. *β.* β_{k+1}(h) − b_{k+1} = Λ(E^{(k+1)}_fl(·; h)). Λ is a Cauchy integral over fixed circles followed by a sum over
   X dominated as in Lemma 2.5, uniformly in h. So β_{k+1} is continuous. The infinite-volume limit RG1 (1.21) is
   uniform by the same domination. ∎

RG1 p.266 mentions a second cutoff, g_k/γ_k·ε₁ in place of ε₁, which makes E^{(j)} and β_j analytic in the couplings.
Propositions 2.4 and 2.6 use the cutoff RG1 (2.9) as published and do not need it.

*The cutoff of CRE.* CRE's fluctuation cutoff at step j is δ_j = g_j(A₁/A₀)p₀(g_j) (CRE p.265, (3.16) p.268), with
p₀(g) = A₀(log g^{−2})^{p₀} (CRE (2.4), p.255) and A₀ ≫ A₁ (CRE p.247); its unit-scale form is
δ_j/g_j = A₁(log g_j^{−2})^{p₀} (`D:\University\Oxford PostDoc\Balaban\READINGS.md` R43). With this cutoff, Proposition 2.4
reads |β_{k+1}(h) − b_{k+1}| ≤ C_ΛC₃δ_k ≤ C_ΛC₃γp₀(γ), which tends to 0 with γ. So no change of the cutoff is needed,
only γ small. The large-deviation condition of RG2 p.19, re-derived at g_k (§0, *Condition 3*), becomes
exp(−γ₂A₁²(log g_k^{−2})^{2p₀}/20) ≤ c_εδ_k, with c_ε as in §0. Its left side is smaller than any power of g_k because
2p₀ > 1, so it holds for g_k ≤ γ small. This uses RG1's fixed domains with CRE's cutoff, which is condition 3 of §0
(derived there, *Condition 3*).

Proposition 2.6 holds with δ_j. In its step 3 the threshold ε₁/g_k becomes δ_k/g_k = A₁(log g_k^{−2})^{p₀}, which is
continuous in g_k ∈ (0, γ]. For B with |B(b)| ≠ δ_k/g_k at g_k = g_k⁰ for all b, the indicators are constant for g_k
near g_k⁰, and the exceptional set is again a finite union of sets {|B(b)| = t}, null for the Gaussian measures of
RG2 (2.14). Steps 1, 2, and 4–6 do not involve the threshold.

### 2.2 The Remainder at Order g_k²

This section bounds the remainder R_{k+1}(h) := β_{k+1}(h) − b_{k+1} = Λ(E^{(k+1)}_fl(·; h)) (Proposition 2.4, step 1)
by a multiple of g_k², for RG1's cutoff (2.9) with CRE's cutoff δ_k = g_k(A₁/A₀)p₀(g_k) (CRE p.265). Proposition 2.4
gives O(δ_k) = O(g_kp₀(g_k)). Two facts give the extra power: the step integral is even in a complex coupling that
replaces g_k in the exponent while the cutoff is held fixed, and the cutoff costs only a Gaussian tail.

*Setting.*
- Fix k and the history h, and put p := δ_k/g_k = A₁(log g_k^{−2})^{p₀}. The cutoff of RG1 (2.9), p.266 runs over the bonds
  b ∉ {b₀(c)}, where hD̃ = 0, and depends on the Gaussian variable only through |B(b)| < p (RG2 (2.3), p.12).
- For a threshold q and complex z, χ_q := ∏_b χ({|B(b)| < q}) over the same bonds. W(z, B) is the exponent
  P^{(k)} + {…} of RG1 (2.12) with g_k replaced by z wherever it occurs in the exponent. The cutoff is not changed.
- E(z; q) := log ∫ χ_q exp W(z, B) dμ_{C^{(k)}}(B). Then E^{(k+1)}_fl = E(g_k; p), by RG1 (2.13).
- *Parity.* In RG1 (2.12), p.268, every term of the exponent is a function of g_k times a linear image of B (g_kCB,
  or g_kB in G₃), or g_k^{−2} times such a function of order at least three (V and G₃ are of order at least three,
  and D̃ starts at order two, RG1 p.267). So W(−z, B) = W(z, −B). The Gaussian measure is centred and χ_q is even,
  so E(−z; q) = E(z; q) as functions of (U, J).

**Lemma 2.7 (Complex Coupling).** Let ε* satisfy every condition on ε₁ listed in Proposition 2.4, step 4, and let
P be the constant fixed in Lemma 2.8. Let q ≥ P and |z|q < ε*. Then RG2's expansion (2.1)–(2.13) applies to
E(z; q) = Σ_X E(X; z, q). Each E(X; z, q) is analytic in z on |z| < ε*/q and in (U, J) on U^c_{k+1}(X, α₀, α₁).
It satisfies RG2 (2.41) with ε* in place of ε₁: |E(X; z, q)| ≤ O(1)C₃ε* exp(−κd_{k+1}(X)). At z = g_k and q = p,
E(X; z, q) is RG2's E^{(k+1)}(X).

*Proof.*
1. *The bracket.* {…} depends on (z, B) only through zCB (RG1 (2.12)). With B̃ := (z/g_k)B it is the bracket at the
   real coupling g_k and the complex field B̃. RG2 Lemma 1 holds on the complex polydisc |B̃| < ε*/g_k (READINGS R40,
   with ε* for ε₁). So V′_k(Y, (z/g_k)B) localises the bracket. It is analytic in z and satisfies RG2 (1.36) with ε*,
   for |z||B| < ε* on Y.
2. *The action terms.*
   - RG2 builds the localisation of P^{(k)} from the pieces (1.38). These are functions of the unscaled fluctuation B′
     alone, analytic for e^{16κ₁}|B′| ≤ a₁ and bounded by RG2 (1.39), p.10. "It can be done in the same way for all
     terms in P^{(k)}" (RG2 p.11).
   - The factor g_k^{−2} is removed by the second-order expansion RG2 (1.40) in B′, whose coefficients are bounded
     by a multiple of |B′|.
   - The coupling enters only through B′ = g_kCB − hD̃(g_kCB) (RG2 (1.19), p.6). The bound (1.20) and the circle
     (1.22) are stated through g_k|B| (RG2 pp.6–7).
   - With z in place of g_k, the pieces are the same analytic functions at B′ = zCB − hD̃(zCB). The prefactor
     cancels by z^{−2}⟨Q̂B′, B′⟩ = ⟨Q̂B′/z, B′/z⟩. The map B′/z = CB − z^{−1}hD̃(zCB) is analytic in z, also at z = 0.
   - RG2 (1.20), with |z| in place of g_k, gives |B′| ≤ C₁|z||B| < C₁ε* and |B′/z| ≤ C₁|B|. So RG2 (1.43) and (1.36)
     hold with ε* in place of ε₁ on |z||B| < ε*, and each V_k(Y; z, B) is analytic in z there.

   This step is our transfer of RG2's construction to complex coupling. RG2 states Lemmas 1–2 for real g_k only.
   For the terms of P^{(k)} other than V, the transfer rests on RG2's sketch "It can be done in the same way for all
   terms in P^{(k)}" (RG2 p.11), used as Bałaban states it.
3. *The expansion.* RG2 section 2 (pp.12–21) uses the potentials only in two ways:
   - through RG2 (1.42), (1.43), (1.36) and the inequality (1.28), in (2.18)–(2.20) on p.16;
   - through the analyticity of V_k in (U, J) on U^c_{k+1}(Y, (1 + β)α₀, (1 + β)α₁, α₀) (RG2 (1.34)), used on p.15.
     z does not enter the (U, J)-dependence, so this holds at every z.

   It uses the cutoff only through the factor χ_{k,Y₀}χ^c_{k,P}, with values in [0, 1], and the tail bound RG2 (2.22).
   - The potentials are evaluated only on the support of χ_{k,Y₀} (RG2 (2.3)). There |z||B| < |z|q < ε*.
   - The threshold enters RG2's conditions only as ε₁/g_k in (2.22), (2.31), (2.33) and (2.34). With q in its place,
     these are lower bounds on q, and they hold for q ≥ P.

   So RG2 (2.1)–(2.41) hold with ε* in place of ε₁ and q in place of ε₁/g_k.
4. *Analyticity.* Each term RG2 (2.14) is an integral of a function analytic in z. It is dominated by RG2 (2.26),
   uniformly on compact subsets of |z| < ε*/q, so it is analytic in z. The sums (2.35)–(2.41) converge uniformly
   there. ∎

**Lemma 2.8 (Threshold Differences).** There is a constant P, depending on ε*, κ, M, γ₂ and the constants of RG2,
with the following property. ε* is fixed first: the condition exp(−γ₂q²/20) ≤ ε₂ of RG2 (2.33) involves ε₂, which is
proportional to ε* here. Let P ≤ q′ < q″ ≤ 2q′ and |z|q″ < ε*. Then E(z; q″) − E(z; q′) = Σ_X Δ(X; z), where each
Δ(X; z) is analytic in z and in (U, J) on U^c_{k+1}(X, α₀, α₁). With constants C₄ and C₅ that do not depend on k,
the history, q′, q″ or z, the following bounds hold.
- RG2 (2.41) has the analogue |Δ(X; z)| ≤ C₄ exp(−γ₂q′²/4) exp(−κd_{k+1}(X)).
- At z = 0, |E(X; 0, q)| ≤ C₅ exp(−γ₂q²/20) exp(−κd_{k+1}(X)) for q ≥ P.

*Proof.*
1. *Same index sets.* The families D, the sets P ⊂ Y₀^{c*}, and the domains Z₀ and Z of RG2 (2.1)–(2.13) do not depend
   on the threshold (RG2 (2.1)–(2.3)). So, term by term in (2.14), the activities at q″ and q′ differ only in the
   factor χ_{k,Y₀}χ^c_{k,P}. Write χ″ and χ′ for this factor at the two thresholds.
2. *The difference of the cutoffs.* χ″ − χ′ = (χ″_{Y₀} − χ′_{Y₀})χ″^c_P + χ′_{Y₀}(χ″^c_P − χ′^c_P).
   - The first term is nonzero only if some b ∈ Y₀ has |B(b)| ≥ q′.
   - The second term is nonzero only if P ≠ ∅ and every b ∈ P has |B(b)| ≥ q′.
   - Bounding each indicator as in RG2 (2.22), and using that Y₀ and P are disjoint bonds of Z₀, gives
     |χ″ − χ′| ≤ (|Y₀| + 1) exp(−γ₂q′²/4) exp(−¼γ₂q′²|P| + ½γ₂‖Z₀B‖²).
3. *RG2's chain.*
   - The factor exp(½γ₂‖Z₀B‖²) is absorbed into the Gaussian as in RG2 (2.23), whose room α₅ contains γ₂ and
     multiplies ‖Z₀B‖².
   - The factor exp(−¼γ₂q′²|P|) runs the sums RG2 (2.31)–(2.34) with γ₂/2 in place of γ₂. P is taken so large that
     they hold.
   - Over the components Y_i of Y₀, RG2 (2.30) gives |Y₀| + 1 ≤ (1 + 24M⁴/(δκ)) exp(δκ Σ_i d_k(Y_i)), and the
     exponential is absorbed by the decay in (2.28).
   - The rest of the chain RG2 (2.26)–(2.38) is unchanged. It bounds H″(Z) − H′(Z) by RG2 (2.38) times C exp(−γ₂q′²/4).
4. *The polymer series.* In RG2 (2.13), ∏H″(Z_i) − ∏H′(Z_i) is a sum of n products, each with one factor H″ − H′.
   - The bound RG2 (2.39)–(2.41) gives the claim, with one more δ in the exponent.
   - Taking δ = (1 − 2L^{−1})/12 in place of RG2's (1 − 2L^{−1})/10 makes (1 − 12δ)½L = 1.
   - In RG2 section 2, δ enters only the estimates (for instance, the radii (2.18) of Cauchy formulas). So no activity
     changes.
5. *z = 0.* Every localized potential vanishes at z = 0. In Lemma 1, H_k(s, 0) = 0 (RG2 (1.18), p.6), so the
   integrand of RG2 (1.23) does not depend on t_□, and the Cauchy integral in t_□ is 0. In the action terms the
   coefficients of RG2 (1.40) are O(|B′|), and B′ = 0 at z = 0. So V_k(Y; 0, B) = 0 for every Y, and only D = ∅
   contributes to RG2 (2.1). Then Y₀ = ∅, and every nonzero term has P ≠ ∅.
   RG2 (2.33) gives the factor exp(−(1/20)γ₂q²) per component in place of max{ε₂, …}, and RG2 (2.37)–(2.41) give
   the bound with C₅. ∎

**Proposition 2.9 (The Remainder at Order g_k²).** Take RG1's cutoff (2.9) with CRE's cutoff δ_k = g_k(A₁/A₀)p₀(g_k)
(CRE p.265, (3.16) p.268). There are constants C_rem and γ > 0, independent of k and of the history, such that for every k
and every history h ∈ 𝓗_γ

  |β_{k+1}(h) − b_{k+1}| ≤ C_rem g_k²  (RG1 (2.13), CRE p.265; proof below).

*Proof.*
1. *The function.* Put R(z; q) := Λ(E(·; z, q)) for |z|q < ε*.
   - Λ is a Cauchy integral followed by a sum dominated as in Lemma 2.5. So, by Lemma 2.7, R(·; q) is analytic on
     this disc, and |R(z; q)| ≤ C_Λ O(1)C₃ε* =: M₀ (RG2 (2.41)).
   - R(·; q) is even, because each activity E(X; z, q) is even in z and Λ is linear.
     - Each piece of V_k(Y; z, B) sees z only through zCB and z^{−2} (Lemma 2.7, steps 1–2). Hence
       V_k(Y; −z, −B) = V_k(Y; z, B).
     - In RG2 (2.14), the change of variables (B, X) ↦ (−B, −X) leaves the centred measures, the coupling
       exp(−⟨B, Γ_kX⟩), and χ_{k,Y₀}χ^c_{k,P} invariant.
     - So each H(Z) is even in z, and by RG2 (2.13) so is each E(X; z, q).
   - Proposition 2.4, step 1, gives β_{k+1}(h) − b_{k+1} = R(g_k; p).
2. *Even functions.* Let f be even and analytic on |z| < r, with |f| ≤ M there. Then φ(z) := (f(z) − f(0))/z² is
   analytic. By the maximum principle on the circles |z| = ρ < r, |f(g) − f(0)| ≤ 2Mg²/r² for 0 ≤ g < r. Here f is
   R(·; q), and M is M₀ from RG2 (2.41) (step 4), or a bound from Lemma 2.8 (step 5).
3. *Telescoping.* Let J be the least integer with 2^JP ≥ p. Put p_j := 2^jP for 0 ≤ j < J and p_J := p, and
   D_j(z) := R(z; p_{j+1}) − R(z; p_j). Then
   R(g_k; p) = R(0; p) + [R(g_k; P) − R(0; P)] + Σ_{j<J} [D_j(g_k) − D_j(0)].
4. *The main term.* R(·; P) is even and analytic on |z| < ε*/P, and bounded by M₀ there (Lemma 2.7, RG2 (2.41)).
   Step 2 gives |R(g_k; P) − R(0; P)| ≤ 2M₀P²g_k²/ε*².
5. *The threshold terms.*
   - D_j is even and analytic on |z| < ε*/p_{j+1}, and |D_j| ≤ C_ΛC₄ exp(−γ₂p_j²/4) there (Lemmas 2.5 and 2.8, from
     RG2 (2.26)–(2.41)).
   - g_k lies in this disc, because g_kp_{j+1} ≤ g_kp = δ_k < ε*.
   - Step 2 and p_{j+1} ≤ 2p_j give |D_j(g_k) − D_j(0)| ≤ 8C_ΛC₄ p_j² exp(−γ₂p_j²/4) g_k²/ε*².
   - Summed over j, the bound is 8C_ΛC₄Sg_k²/ε*², with S := Σ_{j≥0} 4^jP² exp(−γ₂4^jP²/4), which is finite.
6. *The cutoff term.*
   - R(0; p) = Λ(log μ_{C^{(k)}}(χ_p)). Lemmas 2.5 and 2.8 (z = 0) give |R(0; p)| ≤ C_ΛC₅ exp(−γ₂p²/20).
   - p = A₁(log g_k^{−2})^{p₀} (CRE p.265), with p₀ a positive integer (CRE p.244). So (γ₂/20)p² ≥ log g_k^{−2} once
     (γ₂/20)A₁²(log g_k^{−2})^{2p₀−1} ≥ 1, which holds for g_k ≤ γ small.
   - Then |R(0; p)| ≤ C_ΛC₅g_k².
7. *Constants.*
   - C_rem := 2M₀P²/ε*² + 8C_ΛC₄S/ε*² + C_ΛC₅.
   - The constants are fixed in this order: ε*, then P, then γ. γ is taken so small that, for g ≤ γ,
     A₁(log g^{−2})^{p₀} ≥ P, gA₁(log g^{−2})^{p₀} < ε*, and step 6 holds (CRE pp.244, 246, 265).
   - None of these depends on k or on the history. ∎

In the coupling flow RG1 (2.15) this reads 1/g_{k+1}² = 1/g_k² − b_{k+1} + O(g_k²), uniformly in the history.

*Inputs.*
- Lemma 2.5 rests on VAR (189), as in Proposition 2.4 (sidecar node VAR_189).
- RG2 Lemmas 1–2 and section 2, RG1 (2.12), and CRE pp.244–246 and (2.4), as cited.
- Bałaban does not print the parity, the complex-coupling transfer (Lemma 2.7), the threshold differences
  (Lemma 2.8), or the telescoping. Their proofs are in this section, and they hold under the following conditions.

  Conditions:
  1. VAR (189), through Lemma 2.5 (sidecar node VAR_189).
  2. RG2's sketch on p.11 for the terms of P^{(k)} other than V (Lemma 2.7, step 2).
  3. The bound RG1 (1.18) and the analyticity of the step terms in (U, J) on RG1's fixed domains, from RG1 Theorem 3
     run with CRE's cutoffs δ_j = g_j(A₁/A₀)p₀(g_j) (the remark after Proposition 2.6; the transfer is derived in §0,
     *Condition 3*).

*CRE's Construction as a Function of the History.* CRE's coefficient β_{k+1}(g_k) (CRE p.279) is built from the
whole-lattice term E^{(k+1)} ((3.57), p.281; p.278: the localised terms "do not depend on Λ_{k+1}"), which uses the
cutoff δ_k and the input R′_k. The next coupling g_{k+1} enters step k only through the localisation and the
analyticity statements of the new density (the threshold ε_{k+1} of CRE (3.2), p.265, (3.8), p.266, and p.268; the
scale R_{k+1} of p.264; and the domains (2.28) at scale k+1). What breaks the continuity in the history is that the
parameters jump or move with the couplings:
- R_j (CRE (2.5)), k₁ (CRE p.270), N₀ (LFR1 p.179), and the depth N of the R-operation are integers that jump with the
  couplings. N is "to the positive power of log g_k^{−2}" (LFR1 p.198), N ≥ (ν/log L) log log g_k^{−2} (LFR2 p.363),
  and LFR2 p.384 takes N = R_j (`D:\University\Oxford PostDoc\Balaban\READINGS.md` R4). Since R′_k = Σ_{j≤k₁}R^{(j)}
  (CRE p.271), a jump of k₁ moves a whole R-term between R′ and R″, and β_{k+1} jumps with it.
- The thresholds ε_j, δ_j, and δ′_j, the threshold 2ε_kη² of LFR1 (1.75), and the supports of the bump functions of the
  changes of variables CRE (1.22) (pp.252, 269) move with the couplings, so the characteristic functions under the
  integrals depend on the history.

The construction below evaluates every such parameter at a value fixed by the target (K, g). Then no characteristic
function depends on the history, and the couplings enter only through the densities.

*The Class of Tubes.* A tube is given by constants 0 < b ≤ b′ and C ≥ 0 and a target (K, g), with
  c ln L ≤ b ≤ b′ ≤ min((3/2)b, 3c ln L),  C ≤ C₀,  t := g^{−2} ≥ max(γ^{−2} + C, 8C),
with C₀ the constant of Theorem 8.1. Put ρ_γ := max(b′/b, (t + C)/(t − 2C)); on the class ρ_γ ≤ 3/2.
For 0 ≤ k ≤ K put
  ℓ_k := t + b(K−k) − C,  u_k := t + b′(K−k) + C,  T_k := [ℓ_k, u_k],  ĝ_k := u_k^{−1/2},
and let H_k be the set of (x_0, …, x_k) with x_j ∈ T_j for j ≤ k and b(n−m) − C ≤ x_m − x_n ≤ b′(n−m) + C for
0 ≤ m < n ≤ k. H_k is closed and convex. It contains x_j := t + ½(b + b′)(K−j), and the sequence (u_j) lies in H_K.
The constants of Lemma 2.10 and of Propositions 2.4, 2.9, and 2.11 below (C_Λ, C₃, C_rem, C′, C_Σ, K_R, and C_R) are uniform
over the class, and so is the smallness of γ required in Lemma 2.10, because they depend on the tube only through
the bounds c ln L ≤ b ≤ b′ ≤ 3c ln L, C ≤ C₀, and ρ_γ ≤ 3/2 (for instance, Lemma 2.10, step 2, needs
γ²(b′ + C) ≤ (1+β₀)² − 1, and step 3 needs (1 + log(1 + b′)/log γ^{−2})^r ≤ 1 + 1/L).

*The Tube of a Target.* Put δ′ := δ + C_Rγ^{κ₀−4}, with δ = C_ΛC₃γp₀(γ) the bound of Proposition 2.4 and C_R that of
Proposition 2.11, both with the constants of the class. For γ small, δ′ ≤ (2/5)c ln L. Put b := 2c ln L − δ′,
b′ := 2c ln L + δ′, and C := C₀ (Theorem 8.1). Then c ln L ≤ b ≤ b′ ≤ 3c ln L and b′/b ≤ 3/2, and
t ≥ γ′^{−2} = γ^{−2} + C ≥ 8C for γ small, so the tube of the target (K, g) lies in the class. For it ρ_γ → 1 as
γ → 0. These constants do not depend on K or g, and the
definition is not circular, because C_R and δ are fixed on the class before b and b′ are.

The tube construction for (K, g) is CRE's construction in which every parameter that CRE, LFR1, and LFR2 define from
a coupling g_j is defined from ĝ_j instead:
- R_j^T is the smallest power of L with R_j^T ≥ (log ĝ_j^{−2})^r, the depth is N_k^T := R_k^T, and k₁ and N₀ are
  defined from R^T by the formulas of CRE p.270 and LFR1 p.179;
- ε_j^T := ĝ_jp₀(ĝ_j), δ_j^T := (A₁/A₀)ε_j^T, the threshold of LFR1 (1.75) is 2ε_k^Tη², and the domains of
  CRE (2.28) are α^T_{0,j} := ĝ_jC^α_0(log ĝ_j^{−2})^{q₀} and α^T_{1,j} := ĝ_jC^α_1(log ĝ_j^{−2})^{q₁}, where C^α_0
  and C^α_1 are the constants that CRE (2.28) prints as C₀ and C₁ (renamed here, since C₀ is the constant of
  Theorem 8.1 and C₁ the constant of RG2 Lemma 1);
- every other threshold, every factor p₀, p₁, q₀, or q₁ in a threshold, a scale, or a domain, and the supports of the
  bump functions of CRE (1.22) are taken at ĝ_j.

The factors g_j^{±1} that convert between scaled and unscaled fields stay the couplings of the history. So the
thresholds act on unscaled fields (the plaquette variables U(∂p) and the fluctuation fields g_kA_k) with values fixed
by the target.
- *LFR1 (1.55).* LFR1 (1.55), p.188, prints χ′^{(j)} = χ({|B_j(b)| < δ′_j}) for the scaled variable B_j. The threshold
  acts on the unscaled field g_jB_j. LFR1 p.187 establishes |B′_j| < 6δ′_j and then scales B′_j = g_jB_j. The
  complementary function (1.59), p.188, is χ({|exp ig_jB_j(b) − 1| < 2δ′_j})(1 − χ′^{(j)}). LFR2 p.381 uses
  "|B′(b)| ≥ δ′_j", and LFR2 p.383 takes "|B(b)| ≥ g_j^{−1}δ′_j = A₁p₁(g_j)". The print of (1.55) itself has the
  scaled variable; reading the threshold on g_jB_j is what these four passages require, and it is the reading used
  here. In the tube construction χ′^{(j)} is χ({|g_jB_j(b)| < δ′^T_j}).
- *Histories that are not flows.* CRE (2.24), p.259, defines the position-dependent couplings by
  1/g²_{j−1}(x) = 1/g_j²(x) + β_j(g_{j−1})φ_j(x), with g_j²(x) = g_j² on the last domain; this holds along a flow. For an
  arbitrary history h = (g_0, …, g_k) the tube construction uses the same relation counted from the top:
    1/g_k²(x) := 1/g_k² + Σ_{j=1}^{k} β^T_j(h_{j−1})(1 − φ_j(x)),
  which agrees with (2.24) along a flow (put d_j(x) := 1/g_j²(x) − 1/g_j²; (2.24) and the flow give
  d_{j−1} = d_j − β_j(1 − φ_j) with d_0 = 0). The density of step k is CRE's (2.18) with A_k(1/g_k²(·), U_k) and the
  terms E_k, R_k, and B_k produced by the steps 0, …, k−1 of the history; this is RG1's convention, in which the
  Wilson term carries the current coupling and the earlier steps enter through the effective action (Remark 2.3,
  *What β is*). The formula involves the history only through the β^T_j, and on H_j each β^T_j satisfies the same
  per-step bounds as along a flow (Proposition 2.11, *Consequence*). So every bound that CRE, LFR1, and LFR2 derive
  for g_k(x) from bounds on the β_j, such as 1/(g″_k(·))² − 1/g_k² = O(N) (LFR2 p.366), holds. Where they use the
  flow identity 1/g_k²(x) = 1/g_m² for x ∈ Λ_m^{∼−1} outside Λ_{m+1}, the top-down value is
  1/g_k² + Σ_{j=m+1}^{k}β^T_j: the domains are nested (CRE (2.1), p.254), so x ∉ Λ_j and φ_j(x) = 0 for j > m, and
  x ∈ Λ_m^{∼−1} ⊂ Λ_j^{∼−1} (Λ_m ⊂ Λ_j, and the operation ∼ removes cubes of size L^jMR^T_j at scale j, CRE
  pp.245, 256, which are no larger than those of scale m, since L^jR^T_j ≤ L^mR^T_m for j ≤ m by (c)) and
  φ_j(x) = 1 for j ≤ m (φ_j ∈ C_0^∞(Λ_j), φ_j = 1 on Λ_j^{∼−1}, CRE p.259). On the
  boundary layers the formula is CRE's own expression Σ_jβ_j(1 − φ_j(x)) with β^T_j in place of the flow's β_j, so
  CRE's treatment of the layers applies with the same bounds. The top-down value and x_m = 1/g_m² both lie in
  [x_k + b(k−m) − C, x_k + b′(k−m) + C], by the windows of H_k and by Remark 2.3 for the β^T_j. Since x_k ≥ t − C, they
  agree within the factor max(b′/b, t/(t − 2C)) ≤ ρ_γ. The coefficient y of the Wilson action at such x, whether
  1/g_m² or the top-down value, is compared with the tube coupling of scale m by
    u_m/y ≤ (t + b′(K−m) + C)/(t + b(K−m) − 2C) ≤ ρ_γ,
  since y ≥ x_k + b(k−m) − C ≥ t + b(K−m) − 2C. This is the comparison that the lower bounds from the action use
  (Lemma 2.10, step 6). The same coefficient enters the Gaussian densities of the fluctuation fields at scale m.
  The order of the argument is a joint induction on k: the convention at depth k uses the bounds on β^T_j for j ≤ k
  (Proposition 2.11, *Consequence*, at depths below k), and those use Lemma 2.10 at depths below k.
- *Where the history enters.* The couplings g_j of the history enter only through the densities: the Wilson action
  with the couplings g_k(x); the counterterms β^T_j; the Gaussian densities of the unscaled fluctuation fields, with
  covariance proportional to g_j²; the axial gauge-fixing weight exp[−(1/g_k²)G] and its normaliser z(g_k, ε^T_k)
  (CRE (1.5)–(1.7), p.247, used at scale k "as in (1.5), with V_k, ε_k, g_k instead of U, ε₀, g₀", p.265;
  LFR1 (1.5)–(1.6)); the scaling Jacobians d(𝔤) log g_k|·| (CRE p.267; LFR2 (1.10); UV3
  p.261); the R-operation densities and normalisers of LFR1 (1.100), p.201; and the terms of the effective action of
  the earlier steps.

**Lemma 2.10 (The Tube Construction Is Admissible).** Let γ be small, take a tube of the class, and let
ρ_γ = max(b′/b, (t+C)/(t−2C)) ≤ 3/2 be as in *The Class of Tubes* (ρ_γ → 1 as γ → 0 for the tube of a target). For
every (x_0, …, x_k) ∈ H_k, with g_j := x_j^{−1/2}:
- (a) ρ_γ^{−1/2} ≤ ĝ_j/g_j ≤ 1 and log g_j^{−2} ≤ log ĝ_j^{−2} ≤ log g_j^{−2} + log ρ_γ;
- (b) CRE (2.6) holds, with β′ := b′ + C;
- (c) (log g_j^{−2})^r ≤ R_j^T ≤ 2L(log g_j^{−2})^r, R^T_{j+1} ∈ {R^T_j, L^{−1}R^T_j}, and CRE (2.9) holds for R^T;
- (d) N_k^T satisfies the conditions of LFR1 p.198 and LFR2 p.363, and N_k^T > N₀;
- (e) ε_j^T ≤ ε_j, and ε_j^T/g_j, δ_j^T/g_j, and α^T_{i,j}/g_j lie between ρ_γ^{−1/2} and (1 + log ρ_γ/log γ^{−2})^{p}
  times CRE's values at g_j, with p the exponent of the logarithm in each.

The estimates of CRE, LFR1, and LFR2 hold for the tube construction on the histories of H_k, with changed constants,
and Propositions 2.4, 2.6, and 2.9 hold for RG1's construction run with the cutoffs δ_j^T.

*Proof.*
1. *(a).* x_j ≤ u_j, so ĝ_j ≤ g_j. By the mediant inequality u_j/ℓ_j ≤ ρ_γ, so u_j ≤ ρ_γx_j.
2. *(b).* For m < n, x_m ≤ x_n + b′(n−m) + C ≤ x_n + β′(n−m), which is the first inequality of (2.6), and
   (1 + g_n²β′(n−m))^{1/2} ≤ (1 + β₀)(n−m)^{1/2} once γ²β′ ≤ (1+β₀)² − 1. And x_n ≤ x_m + C ≤ (1+β₀)²x_m for γ
   small, so g_m ≤ (1 + β₀)g_n.
3. *(c).* R_j^T ≥ (log ĝ_j^{−2})^r ≥ (log g_j^{−2})^r, and R_j^T < L(log ĝ_j^{−2})^r ≤ 2L(log g_j^{−2})^r by (a). The
   sequence u_j decreases, so R^T_{j+1} ≤ R^T_j, and u_j = u_{j+1} + b′ ≤ (1 + b′γ²)u_{j+1} gives
   R^T_j/R^T_{j+1} < L(1 + b′γ²/log γ^{−2})^r < L², so the ratio, a power of L, is 1 or L. For the second inequality
   of (2.9) let s := n − m and λ := log γ^{−2}. Then R^T_m/R^T_n < L(log u_m/log u_n)^r and
   u_m ≤ (1 + b′sγ²)u_n, so R^T_m/R^T_n < L(1 + log(1 + b′sγ²)/λ)^r.
   - For s ≤ γ^{−2} the bracket is at most (1 + log(1 + b′)/λ)^r ≤ 1 + 1/L for γ small.
   - For s > γ^{−2} put y := log s > λ. Then 1 + b′sγ² ≤ (1 + b′)sγ², and the bracket is at most
     ((y + log(1 + b′))/λ)^r. This is at most 1 + 1/L at y = λ, and its logarithmic derivative in y is at most
     r/λ ≤ β₀ for γ small, so it is at most (1 + 1/L)s^{β₀}.
   In both cases R^T_m ≤ (L+1)s^{β₀}R^T_n.
4. *(d).* LFR1 p.198 requires "N ≤ O(1)(log g_k^{−2})^ν" and N sufficiently large; LFR2 p.363 requires
   N ≥ (ν/log L) log log g_k^{−2}, with a different exponent ν (READINGS R4). With N = R_j both hold for g small (R4),
   and by (c) they hold for N_k^T = R_k^T, whose upper bound 2L(log g_k^{−2})^r has the form O(1)(log g_k^{−2})^ν once
   r ≤ ν. The exponents admit this: LFR1 p.198 takes ½ν ≤ p₀ − p₁ − 1 and LFR2 p.383 takes 2p₁ − (d+5)r₀ > p₀, with
   r₀ = r the exponent of R_j (UV3 p.257 writes R = R₁(1 + log g_0^{−1})^{r₀}). LFR1 p.198 takes ν a positive
   integer, so put ν := ⌈r⌉; then r ≤ ν, and ν ≤ 2(p₀ − p₁ − 1) together with 2p₁ > p₀ + (d+5)r needs
   p₁ ∈ ((p₀ + (d+5)r)/2, p₀ − 1 − ⌈r⌉/2), which is nonempty when p₀ > (d+5)r + ⌈r⌉ + 2. CRE bounds p₀ only from below
   ("p₀ ≥ 5r", CRE p.246), so p₀ is taken above (d+5)r + ⌈r⌉ + 2 and p₁ in that interval. The ν of LFR2 p.363 is a different exponent, with ν ≥ 2p₀ + dr₀; there N ≥ (ν/log L)
   log log g_k^{−2} holds for N = R^T_k ≥ (log g_k^{−2})^r and g small. N₀ satisfies L^{N₀−1} = R^T_{k−N₀+1} ≤ (L+1)(N₀+1)^{β₀}R^T_k (LFR1 p.192,
   with (c)), so N₀ = O(log R^T_k) < N_k^T for γ small.
5. *(e).* ε(g) = gA₀(log g^{−2})^{p₀} increases on (0, γ] for γ small, since its logarithmic derivative is
   g^{−1}(1 − 2p₀/log g^{−2}) > 0, so ε_j^T ≤ ε_j by (a). The ratios follow from (a), since each parameter is ĝ_j or
   1 times a power of log ĝ_j^{−2}.
6. *Where the parameters enter.* Every line of the corrected transcriptions of CRE (pp.244–284), LFR1 (pp.175–201),
   and LFR2 (pp.356–391) that contains R_j, k₁, N₀, N, ε_j, δ_j, δ′_j, α_{0,j}, α_{1,j}, p₀(·), p₁(·), q₀(·), or q₁(·)
   was read; LFR2's references [III] and [IV] are CRE and LFR1 (LFR2 p.392). The three papers import further results,
   and those were read too:
   - UV3 ([16], CMP 102, pp.255–275), every line with one of its parameters (ε₁, p(g), R, r(g), and log g). They are of the same kinds: the definitions
     ε₁ = g_0p(g_0) and R = R₁r(g_0) (p.257) and their scale-k versions (pp.266–267), the distance conditions (p.266),
     the factors exp(−R₁r(g_0)) (p.264), the normalisations d(𝔤) log g_k|·| (pp.261, 265, 269, 271), and the
     chain ≥ (1/(2g_j²))|V_j(∂p′) − 1|² − O(1)g_jp³(g_j) ≥ ½p²(g_j) − O(1)g_jp³(g_j) ≥ ¼p²(g_j) of p.273, for
     |V_j(∂p′) − 1| ≥ g_jp(g_j). This is a lower bound from the action; with the tube threshold ĝ_jp(ĝ_j) it gives
     ½ρ_γ^{−1}p²(ĝ_j) − O(1)g_jp³ ≥ ¼ρ_γ^{−1}p²(ĝ_j).
   - CMP98 ([12]), REG ([14]), and VAR ([15]) are statements about lattice gauge fields, averaging operators, and
     variational problems under a smallness condition on the field (a threshold ε with ε small). They contain no
     coupling, so they apply to the tube thresholds, which are smaller than CRE's (by (e)).
   - RG1 §§3–4 are run by CRE on its own cover, with the (2.28) domains and the regularity thresholds ε_n (CRE
     p.276). Their parameters enter there as smallness conditions on the thresholds, as the cutoff δ_j relative to
     the radii α_{0,j}, α_{1,j}, or as relations among the parameters, so they fall under the kinds below, read on
     CRE's pages; RG1's fixed domains are covered by step 7 and by §0, *Condition 3*.
   Every occurrence is of one of four kinds.
   - *Relations among the parameters alone*, of one index or of several. Examples: the cube sizes and the
     compatibility of the partitions (CRE pp.245–270, LFR1 p.177, LFR2 pp.384–387); the definitions of k₁ (CRE
     p.270) and N₀ (LFR1 p.179), and the bounds L^{N₀−1} ≤ (L+1)(N₀+1)^{β₀}R_k and R_k^{−α₀} (LFR1 pp.192, 200);
     (2.7) (CRE p.255) and (2.9) (CRE p.256); δ′_j ≤ (1+β₀)²(k−j)^{β₀}δ′_k (LFR1 p.192);
     δ′_j/δ_j = A₀p₁(g_j)/p₀(g_j) (with the definitions of LFR1 p.183); the comparisons of ε_{k+1} with ε_k
     (CRE pp.266–268, LFR1 pp.184–200); N^{1/2}p₁(g_h)/p₀(g_h) small (LFR1 pp.198–199); the margins
     2p₁ − (d+5)r₀ > p₀ (LFR2 p.383), 2(1+β₀)^{−1}p₀ against O(1)3(100M)^dR^{d+2} (LFR2 (1.88), p.387), and
     −2(1+β₀)^{−1}p₀ + 1 + 2κ(100R_k)^d ≤ −(3/2)p₀ (LFR2 p.389); and bounds through p₀(γ), p₁(γ) (LFR1 p.186). In the
     tube construction all of these are evaluated on the sequence (ĝ_j). That sequence satisfies the hypotheses CRE
     places on coupling sequences: its entries lie in (0, γ], it satisfies (2.6) because (u_j) ∈ H_K (step 2), and its
     R^T satisfies (2.9) by (c). So these relations hold as printed.
   - *Lower bounds from the action.* A threshold τ_j forces a suppression exp(−c yτ_j²), with y the coefficient of the
     action at scale j: 1/g_j², or the top-down value of *Histories that are not flows*, which satisfies
     y ≥ u_j/ρ_γ = ĝ_j^{−2}/ρ_γ there. Examples: exp[−(1/g_0²)[1 − Re tr U(∂p)]] ≤ exp(−p₀(g_0)) (LFR1 p.175) and ≤ exp(−½p₀²(g_0))
     (CRE p.244), for |U(∂p) − 1| ≥ g_0p₀(g_0); the large-field factors of
     LFR2 pp.380–383, including exp(−γ₀(1/g_m²)(2δ′_m)²) ≤ exp(−γ₀A₁²p₁²) (p.381) and the factor
     exp(−¼g_j^{−2}(24R_j⁴)^{−2}δ′_j²) (p.382); and the Gaussian tails of RG2 (§0, *Condition 3*). Since
     y ≥ ĝ_j^{−2}/ρ_γ (by (a) when y = 1/g_j²), yτ_j(ĝ_j)² ≥ ρ_γ^{−1}τ_j(ĝ_j)²/ĝ_j², so each such factor holds with c
     replaced by c/ρ_γ ≥ 2c/3, that is, with γ₀ replaced by 2γ₀/3. The conditions on the constants that compare such
     factors at the same order are then imposed with a factor 2 ≥ ρ_γ on the side of the action:
     - the creation factor exp(−γ₀min{½B₃^{−2}A₀², 2A₁², A₁²}p₀²(d′ + 1)) ≤ exp(−½γ₀A₁²p₀²(d′ + 1) − 2p₀) (LFR2
       p.381), whose margin is a factor 2 in the leading term: with ρ_γ ≤ 3/2 the left side is at most
       exp(−⅔γ₀A₁²p₀²(d′ + 1)), and ⅙γ₀A₁²p₀² ≥ 2p₀ for g small;
     - A₀ ≫ A₁ in exp(−⅛B₃^{−2}(1+β₀)^{−2}A₀²p₀²) ≤ exp(−A₁²p₀²) (LFR2 p.381, CRE p.247);
     - 4(1+β₀)^{−2} ≥ ρ_γ in exp(−γ₀(1/g_m²)(2δ′_m)²) ≤ exp(−γ₀4(1+β₀)^{−2}A₁²p₁²) ≤ exp(−γ₀A₁²p₁²) (LFR2 p.381),
       which holds for β₀ ≤ √2 − 1;
     - A₀² ≥ 4ρ_γO(1)B₃M²A₁² in exp(−¼(1/g_j²)(O(1)B₃M²)^{−1}ε_j²) ≤ exp(−A₁²p₀²) (LFR2 p.381);
     - A₁ ≥ 48√ρ_γ in exp(−¼(1/g_j²)(24R_j⁴)^{−2}δ′_j²) = exp(−A₁²48^{−2}R_j^{−8}p₁²) ≤ exp(−R_j^{−8}p₁²)
       (LFR2 p.382);
     - ¼γ₀14^{−d}A₁²p₀²(g₁) ≥ O(1)2·64^dM^dL^{d+1}R₁^{d+2} (LFR2 p.385), which has in addition the margin
       p₀² ≫ R₁^{d+2} of a power of log g_1^{−2}.
     Every other such comparison has a margin of a positive power of log g_j^{−2}.
   - *Upper bounds relative to the action.* Fluctuations bounded by a threshold enter the expansion of the action in
     g_jB, giving terms such as (1/g_k²)δ′_k³ ≤ g_kO(1)A₁³p₁³(g_k) (LFR2 p.361), (1/g_k²)(α_{0,k} + α_{1,k})ε_k
     (LFR2 p.368), and p₁²(g_k)(α_{0,k} + α_{1,k}) (LFR2 p.379). By (e) these ratios change by at most the factor
     1 + o(1), and ε^T_j ≤ ε_j.
   - *Conversions between scaled and unscaled fields*, such as |A(b)| < g_0^{−1}δ_0 (CRE p.250), |A_j(b)| < g_j^{−1}δ_j
     (LFR1 (1.9), p.178), |B′| < M₀g_k^{−1}ε_k (LFR2 p.356), and |B(b)| ≥ g_j^{−1}δ′_j (LFR2 p.383). The factor g_j^{±1}
     is the coupling of the history, and the threshold is the tube parameter, so in the unscaled field the threshold
     is δ^T_0, δ^T_j, M₀ε^T_k, or δ′^T_j. The analyticity domain (3.43) of CRE p.276 bounds the scaled fluctuation
     field by C₁p₁(ĝ_k); it is a domain on which analyticity and bounds are asserted, not a threshold under an
     integral, and it enters as the other domains of analyticity do (Proposition 2.12, step 4).
   Two further uses are not comparisons of a threshold with the action, and they hold for the same reasons.
   - Quantities of the history bounded by a parameter, such as the bound on 1/(g″_k(·))² − 1/g_k² by O(N) (LFR2
     p.366), the bounds on the background fields by thresholds (LFR2 pp.357, 378), and the terms "bounded by any
     positive power of g" (CRE pp.252, 269; LFR1 p.188). The history side is bounded by the β^T_j and by the couplings
     g_j ≥ ĝ_j, and the parameter side is a tube parameter, which differs from CRE's by the factors of (e).
   - The geometry: the domains Λ_j, Ω_j, the partitions, and the scales R^T_j are fixed by the target and the
     configuration, so the combinatorial bounds (numbers of polymers, of cubes, and of partitions) hold as printed
     with R^T in place of R.
   The lower bounds on R_j, such as exp(−R_k) and exp(−δMR_k) small (CRE pp.250–251, 266, 268–269) and
   log g_j^{−2} ≤ R_j (LFR2 p.380), hold by (c). The threshold 2ε_kη² of (1.75) enters LFR1 p.193 (the definition
   and the large-field side), pp.195 and 200 (the bounds |U_0(∂p) − 1|, |U″_{k,Z}(∂p) − 1| < (2ε_kη² + …)), and
   p.199 (the comparison ε_kη² ≤ (1+β₀)(k−j)^{1/2}L^{−2(k−j)}ε_j(L^{k−j}η)², a relation among parameters), and
   LFR2 p.359 (extensions satisfying (1.75)), p.363, p.378 ("This is clear for χ_{k,Λ}", from |∂V_k − 1| < 2ε_k), and
   p.381. The function χ_{k,Λ} itself enters further LFR1 pp.194, 196, 198, 200, and 201 and the densities of LFR2
   pp.356, 369, 377, and 390. All of these are statements about unscaled plaquette variables, with ε_k^T in each,
   so they hold as printed. The R-terms come out of LFR2 with |R′^{(k)}(X)| ≤ exp(−p₀(ĝ_k))exp(−κd_k(X)) (LFR2 p.390), and
   exp(−p₀(ĝ_k)) = ĝ_k^{2A₀(log ĝ_k^{−2})^{p₀−1}} ≤ ĝ_k^{κ₀} ≤ g_k^{κ₀} for γ small, so CRE (2.31) holds with the
   couplings of the history for the new R-terms. The R-terms of earlier steps, in R′_k and in R″_k alike, keep their
   bounds by CRE's induction ("These terms satisfy all the conditions of the inductive assumption", CRE p.279), which
   in the tube construction runs over the histories of H_k with the tube domains α^T_{i,j}: the R-operation of LFR1
   (1.100), p.201, acts on the step's analyticity domain, which is the tube domain, so its output is analytic and
   bounded there.
7. *RG1 with δ_j^T.* Propositions 2.4, 2.6, and 2.9 use the cutoff only through δ_j ≤ γp₀(γ), through
   δ_j/g_j = A₁(log g_j^{−2})^{p₀} in the Gaussian tails (Proposition 2.9, steps 4–7, and §0, *Condition 3*), and
   through the continuity of δ_j/g_j in g_j. On the histories of H_k, by (e), δ_j^T/g_j lies between ρ_γ^{−1/2} and
   1 + o(1) times A₁(log g_j^{−2})^{p₀}, and it is continuous in g_j. So Propositions 2.4, 2.6, and 2.9 hold for
   RG1's construction run with δ_j^T on the histories of H_k; off H_k the tube parameters are not compared with the
   couplings, and no claim is made there. ∎

**Proposition 2.11 (The R-Terms Shift β by O(g_k^{κ₀−4})).** Let γ be small, k < K, (x_0, …, x_k) ∈ H_k, and
h = (g_0, …, g_k) with g_j = x_j^{−1/2}. Let β^T_{k+1}(h) be the coefficient of the tube construction (CRE (3.61)–(3.64),
pp.282–283) and β^{δ,T}_{k+1}(h) the coefficient of RG1's construction run with the cutoffs δ_j^T on the same history.
Then
  |β^T_{k+1}(h) − β^{δ,T}_{k+1}(h)| ≤ C_R g_k^{κ₀−4},
with C_R independent of k, K, g, and the history, and κ₀ ≥ 7 the exponent of CRE (2.31).

*Proof.*
1. *The R-terms.* CRE (2.30)–(2.31), p.260: R_k = Σ_j[R^{(j)}(Λ_j, U_k) − R^{(j)}(Λ_j, 1)], with the properties
   (i)–(iii) of CRE p.259 (property (ii) is analyticity on U^c_j(X, α_{0,j}, α_{1,j})) and
   |R^{(j)}(X, (U, J))| ≤ g_j^{κ₀}exp(−κd_j(X)). (2.31) is an inductive assumption; "κ₀ can be chosen arbitrarily
   large, similarly as κ, if the other parameters are fixed properly, as in [I]" (CRE p.260), and CRE (2.46), p.263, uses κ₀ ≥ 7. The
   histories of H_k satisfy CRE (2.6) (Lemma 2.10(b)).
2. *The family.* Take the whole-lattice R-terms R^{(j)}(U_j) = Σ_X R^{(j)}(X, U_j) of CRE (2.33), p.260, of the tube
   construction for the history h. For s ∈ ℂ, run the whole-lattice regular recursion of the tube construction (RG1's
   formulas with δ_j^T, CRE pp.267, 272, 274) with sR^{(j)} in place of R^{(j)} wherever CRE includes R′ into E
   (CRE p.271), and with the counterterms β_j(s) computed from its own step terms by CRE (3.61). Write E^{(j)}(s) and
   β_j(s). At s = 1 this is the regular part of the tube construction, so β_{k+1}(1) = β^T_{k+1}(h); at s = 0 no R-term
   enters, so β_{k+1}(0) = β^{δ,T}_{k+1}(h).
3. *The size of the R-part.* By the windows of H_k, x_j ≥ x_k + b(k−j) − C ≥ ½x_k + c ln L·(k−j) for j ≤ k and γ
   small, since b ≥ c ln L on the class of tubes. So
     Σ_{j≤k} g_j^{κ₀} ≤ Σ_{m≥0}(½x_k + mc ln L)^{−κ₀/2} ≤ C_Σ g_k^{κ₀−2},  C_Σ := 2^{κ₀/2}(1 + 2/((κ₀−2)c ln L)).
   C_Σ, and hence C_R below, is uniform over the class of tubes, so δ′ = δ + C_Rγ^{κ₀−4} ≤ (2/5)c ln L for γ small
   is not circular (*The Tube of a Target*).
   Each R′-term satisfies a bound of the form (1.18), since |s|g_j^{κ₀} ≪ E₀, but the R′-part lacks the factor
   (L^jη)⁵ of the irrelevant terms (RG2 (1.24), p.7) that RG2 uses to sum over j (RG2 p.8) before Lemma 1, (1.36),
   p.9: after the vacuum-energy renormalisation it consists of marginal terms, with bounds
   O(1)(L^jη)⁴g_j^{κ₀}exp(−κd_j(X)). CRE controls it by its own bound instead: "The sum over X is controlled by the exponential factor, and by the factor (L^jη)⁴. The sum over j is
   controlled by g_j^{κ₀}" (CRE p.260), and (2.44) and (2.46), p.263, bound the R-terms by
   R₁g_j^{κ₀}Σ_{n=j}^{k}|Γ_n ∩ Ω|. The potential V′ of RG2 Lemma 1, through which the R′-part enters the step, is linear in the constant
   of (2.31): V′ is built linearly from the bracket of E_k (RG2 (1.33)), and the sums over X and j are controlled as
   quoted. The later expansions of the step, such as the products of RG2 (2.26), p.17, are not linear in it; they use
   only the resulting bound (1.36) with 2E₀ and the smallness condition of RG2 p.18, and the R′-part enters them
   through the modulus of the interaction (*The Step with Complex Multiples of the R-Terms*, below). Let K_R be the
   constant such that an R′-input of step j whose terms satisfy (2.31) with g_i^{κ₀} replaced by a_ig_i^{κ₀} enters
   the potential V′ of RG2 Lemma 1 with K_RΣ_{i≤j}a_ig_i^{κ₀} in the place of E₀ in (1.36), p.9: its part of V′ is
   at most K_RΣ_{i≤j}a_ig_i^{κ₀}ε₁C₁M^q exp C₂κ₁ exp(−(1−2δ)κd_j(Y)). So the input side of the step, regular part and
   R′-part together, is bounded as in (1.36) with E₀ + K_RΣ_{i≤j}a_ig_i^{κ₀} in place of E₀. K_R depends only on the
   constants of CRE's step and on κ, so it is uniform over the class of tubes.
   Every R′-term that has entered E up to step k, at any earlier step, carries the factor s, so a_i = |s|. Put
   θ := E₀/(K_RC_Σ) and ρ := θg_k^{2−κ₀}. For j ≤ k, Σ_{i≤j}g_i^{κ₀} ≤ Σ_{i≤k}g_i^{κ₀} ≤ C_Σg_k^{κ₀−2} by the first
   display, so for |s| ≤ ρ
     K_R|s|Σ_{i≤j}g_i^{κ₀} ≤ K_RρC_Σg_k^{κ₀−2} = K_RθC_Σ = E₀
   at every step j ≤ k, and the input side is bounded with 2E₀ in place of E₀. The argument is an induction over j = 0, …, k at the fixed radius ρ = ρ_k: if the regular
   part of the input of step j satisfies (1.18) with E₀ and is analytic in s on |s| < ρ, then the input side is
   bounded with 2E₀, and by step 4 the output E^{(j+1)}(s) satisfies (1.18) with E₀ (the fluctuation part at most
   ½E₀ by RG2 pp.20–21, the part from log Z^{(j)} at most ½E₀) and is analytic in s; β_{j+1}(s) is analytic on
   |s| < ρ by step 5 at scale j+1. At j = 0 there is no R-term and no s.
4. *The step with 2E₀ and complex s.* CRE's step accepts these inputs (*The Step with Complex Multiples of the
   R-Terms*, below). The conditions that involve E₀ are upper bounds on the cutoff relative to the domain radii: RG2 p.18,
   2E₀ε₁C₁α₄^{−1}α₆^{−1}M^q e^{C₂κ₁}e^{5κ} ≤ 1; RG2 p.20; and RG2 p.21, O(1)C₃ε₁ ≤ ½E₀ with C₃ linear in E₀
   (Proposition 2.4, step 2). Two further conditions involve E₀ and only get weaker when E₀ is doubled: the tail
   condition exp(−γ₂ε₁²/(20γ²)) ≤ ε₂ of RG2 p.19, with ε₂ = 2E₀ε₁C₁α₄^{−1}α₆^{−1}M^q exp C₂κ₁, a lower bound on
   ε₁/g_k (§0, *Condition 3*), and C₃ ≤ E₀C₁ of RG2 p.16. On CRE's domains the cutoff enters relative to α_{0,j},
   through δ_j/α_{0,j} = (A₁/C^α_0)(log g_j^{−2})^{p₀−q₀}, and CRE takes C^α_0 and C^α_1 "sufficiently large"
   (p.259). This ratio is small for g_j small when q₀ > p₀, and likewise
   δ_j/α_{1,j} when q₁ > p₀. CRE (2.28), p.259, prints q₀ and q₁ as "integers greater than 1", and says on p.262
   that "some of the restrictions on constants, e.g. on constants κ, M, ε_j, α_{0,j}, α_{1,j}, come from the paper
   [I]". RG1 and RG2 bound the domain radii from
   below relative to the cutoff (RG2 p.18) and print no upper restriction on q₀, q₁; nor do LFR2 pp.358, 368, and 379,
   where α_{0,k} + α_{1,k} enters multiplied by small factors (Lemma 2.10, step 6, *upper bounds relative to the
   action*). So q₀ and q₁ are taken greater than p₀; this choice is listed in §9. These conditions are imposed for 2E₀ when C^α_0, C^α_1, and the cutoff are chosen. The step
   output is given by convergent expansions whose terms are analytic in the exponent, uniformly for |s| ≤ ρ, so
   E^{(j+1)}(X; s) is analytic in s. The parameter s is not CRE's parameter s of (3.26)–(3.27), p.271, which
   multiplies R″_k; that one stays as in CRE.
5. *Polarisation on the tube domains.* E^{(k+1)}_fl(X; s) is analytic on U^c_{k+1}(X, α^T_{0,k+1}, α^T_{1,k+1}) and
   bounded by E₀e^{−κd_{k+1}(X)}. In the proof of Lemma 2.5 the domain enters only through the Cauchy radius r of step 2,
   and here r ≥ c·min(α^T_{0,k+1}, α^T_{1,k+1}) (`WILSON_CAUCHY_LIPSCHITZ_2026_10_21.md`, *What changes on CRE's
   domains*). With q_* := min(q₀, q₁) ≥ 2 and x̂ := ĝ_{k+1}^{−2} = u_{k+1} ≤ u_k ≤ ρ_γx_k ≤ 2x_k (Lemma 2.10(a)),
     |β_{k+1}(s) − b_{k+1}| = |Λ(E^{(k+1)}_fl(·; s))| ≤ C′E₀x̂(log x̂)^{−2q_*} ≤ 2C′E₀g_k^{−2}.
   The domain is fixed by the target, so no bound on the next coupling is needed. The infinite-volume limit of Λ is
   uniform in s by the domination of Lemma 2.5, so s ↦ β_{k+1}(s) is analytic on |s| < ρ.
6. *Cauchy in s.* For γ small, ρ = θg_k^{2−κ₀} > 2 because κ₀ ≥ 7. For σ ∈ [0, 1] the closed disc of radius ρ/2
   about σ lies in |s| < ρ, since 1 + ρ/2 < ρ, so |β′_{k+1}(σ)| ≤ 4C′E₀g_k^{−2}/ρ, and
   |β_{k+1}(1) − β_{k+1}(0)| ≤ 4C′E₀g_k^{−2}/ρ = 4C′K_RC_Σg_k^{κ₀−4} =: C_Rg_k^{κ₀−4}. ∎

*The Step with Complex Multiples of the R-Terms (checked against CRE pp.260, 264, 271, 276–279, and RG2 pp.15–18).*
- CRE's step uses the inductive assumption on E_k: "Using the inductive assumption we write" (CRE p.264), and it
  takes R′_k in as part of E_k (p.271). Its output satisfies the inductive bounds: "These terms satisfy all the
  conditions of the inductive assumption" (p.279).
- R′_k itself, carried in E_k, gets no counterterm. Its contribution to the fluctuation integral of step k enters the
  whole-lattice E^{(k+1)}, from which the counterterm of step k+1 is computed (CRE (3.57), p.281; p.279), so only
  that contribution is coupling-renormalised; this is the part that the family of step 2 multiplies by s inside the
  step terms. The R-terms that stay R (R″_k) get no coupling
  counterterm: R_k "is treated in exactly the same way as E_k, except the second renormalization connected with the
  coupling constant renormalization counterterm, which is not needed here" (p.276). This sentence concerns R″_k in the
  measure (3.27), which CRE multiplies by its own real parameter s ∈ [0, 1] (p.271), and it rests on the factor g_j^{κ₀}
  ("The sum over j is controlled by g_j^{κ₀}", p.260). The family of Proposition 2.11 multiplies only the R′-part, and
  step 3 keeps the R′-parts, summed over all earlier steps, at most E₀.
- "The final step in constructing localized expansions of the expectation values is the exponentiated cluster
  expansion of Sect. 7 [I], or rather its appropriate generalization", and the normalization factor of (3.28) "is
  expanded in exactly the same way as in Sect. 7 [I]" (p.277). CRE's [I] is RG1 (CRE
  p.285), whose sections are 0–5. RG2 numbers its own sections 1 and 2, but the equations that CRE cites with
  sections 6 and 7 of [I] are RG2's equations of sections 1 and 2: (I.7.12)–(I.7.13) are RG2 (2.12)–(2.13), and
  (I.6.34) is RG2 (1.34). So "Sect. 7 [I]" is RG2 §2. That expansion is already analytic in complex multipliers of the interaction.
  RG2 (2.14) carries exp[Σ_Y τ(Y)V_k(Y, B)] with complex τ(Y), and RG2 (2.15) bounds it through
  exp[Σ_Y |τ(Y)||V_k(Y, B)|]. The only positivity used is that of the Gaussian measure at (U, 0): "For the pair (U, 0)
  the operators are symmetric, and the measure is positive … The general case is handled by a perturbative argument"
  (RG2 p.15). The interaction, which contains the bracket of E_k, enters only through its modulus. So a complex scalar s
  on the R′-part of E_k enters the same way as τ, and it preserves the properties (i)–(iii) of CRE p.259 and the
  covariance (2.29).

*Consequence (the Bounds of (W) and Item 5 for the Tube Construction).* For every history of H_k, Proposition 2.11 with
Propositions 2.4 and 2.9 for the cutoffs δ_j^T (Lemma 2.10, step 7) gives
  |β^T_{k+1} − b_{k+1}| ≤ δ + C_Rγ^{κ₀−4} = δ′  and  |β^T_{k+1} − b_{k+1}| ≤ (C_rem + C_Rγ^{κ₀−6})g_k².
So (W) holds for β^T on the histories of H_K, with b = 2c ln L − δ′, b′ = 2c ln L + δ′, and C = C₀ (Remark 2.3), and
δ′ < 2c ln L for γ small. Item 1 concerns b_j only. Item 5 holds on H_k with C_rem + C_Rγ^{κ₀−6}. Items 3 and 4 hold
along the matched flow of Proposition 2.13, which lies in H_K.

**Proposition 2.12 (Continuity of the Tube Construction).** Let γ be small. For each k < K, the coefficient
β^T_{k+1}(h) of the tube construction for (K, g) is continuous on the histories h = (x_0^{−1/2}, …, x_k^{−1/2}) with
(x_0, …, x_k) ∈ H_k.

*Proof.* Induction on j. The claim S_j is: the coefficients β_i for i ≤ j+1, and every term of the density ρ_{j+1}
produced by the steps 0, …, j (the regular part E_{j+1} with the R′-part, the R-terms R^{(i)}, the terms B_{j+1}, and
the operations T_{j+1} of CRE (2.18)–(2.23)), are continuous in h at every h⁰ of H_j. For the terms this means: on
real unscaled fields, and, for each term F(X) and each real field B⁰, as the analytic function B ↦ F(X, u(B)) on the
polydisc |B − B⁰| < r about B⁰, with r ≥ c·min(α^T_{0,j+1}, α^T_{1,j+1}) the radius of Lemma 2.5 and
u(B) = U_{j+1}(e^{iB}), uniformly on compact subsets of the polydisc. This is the form in which Lemma 2.5, and so Λ,
uses the terms (Lemma 2.5, steps 1–2; RG1 (1.15)). Within the stage j, steps 1–4 below give the continuity of the step
terms E^{(j+1)}, R, and B produced by step j, step 5 gives that of β_{j+1}, and then E_{j+1}, which contains
−β_{j+1}A(φ_{j+1}, ·) (CRE (2.25)), is continuous too.
0. *Base case.* The density ρ_0 is the Wilson density exp(−(1/g_0²)A(U)) with no earlier terms and no β; it is
   continuous in g_0 at fixed U, so S_{−1} holds.
1. *What depends on h.* In the tube construction every threshold, scale, depth, and partition, and every domain
   radius α^T_{i,j}, is fixed by (K, g) (Lemma 2.10); the one radius that moves with h is that of the domain (3.43) in
   the unscaled field (step 4). In unscaled fields the characteristic functions do not depend on h:
   - the background-field functions χ_k(Ω_k) of CRE (2.17), with threshold ε^T_kη² on the plaquettes of the background
     fields U_{k,□}(V_k) of CRE (2.16), which are defined from the fields alone;
   - the inf–sup function χ_{k,Λ} of LFR1 (1.75), with threshold 2ε^T_kη²;
   - the fluctuation-field functions, whose thresholds act on g_jA_j and on exp(ig_jB_j(b)) (for example
     |exp ig_jB_j(b) − 1| < 2δ′_j in LFR1 (1.59), p.188), with δ^T_j and δ′^T_j.
   The changes of variables of CRE (1.22)–(1.23), pp.251–252, and of LFR1 p.188 read, in unscaled fields,
   exp(iB) = exp(iB′)exp(−iφ(B′)H), where φ is the C^∞ bump of CRE p.252 with supports fixed by δ^T_0 at step 0, and by δ′^T_j in the change of
   variables of LFR1 p.188, and H is an
   analytic function of the background fields (H_{1,Ax} of CRE (1.21), and ℍ_Z^{(j)} of LFR1 (1.58)). These maps and
   their Jacobians (CRE (1.24)) do not depend on h. The block-averaging constraints and the Haar measures do not depend
   on h either. The couplings of the history therefore enter only through the densities: the Wilson action with the
   couplings g_j(x) (the top-down formula), the Gaussian densities of the unscaled fluctuation fields with covariance
   ∝ g_j², the axial gauge-fixing weight exp[−(1/g_k²)G] and its normaliser z(g_k, ε^T_k), the scaling Jacobians,
   the R-operation densities and normalisers of LFR1 (1.100), the counterterms β_i, and the terms of the effective
   action of the earlier steps (the list of *Where the history enters*).
2. *Pointwise continuity.* At fixed unscaled fields these densities are continuous in h, by S_{j−1}, by the continuity
   of β_i (i ≤ j), and because g_j(x) depends continuously on g_j and the β_i through the top-down formula (the bullet
   *Histories that are not flows* above). The characteristic
   functions are fixed. The integrands are bounded uniformly for h near h⁰ in H_k: the estimates of CRE, LFR1, and LFR2
   hold on H_k with constants independent of the history (Lemma 2.10). Dominated convergence gives continuity of each
   integral at fixed external fields.
3. *Quotients and sums.* The R-operation produces the quotients of LFR1 (0.3) and (0.5), p.176, with the densities
   and normalisers of LFR1 (1.100), p.201. At real configurations the denominators are integrals of positive
   densities over nonempty domains ("the densities are positive, and the integration domains … are nonempty, hence
   the denominators are positive", LFR1 p.176), and they are continuous in h by step 2. So at real fields each
   quotient, and each term R(X, V) of its exponentiated polymer expansion (0.5), is continuous at h⁰. The complex
   values are used only through f_h(B) := R(X, u(B); h) on a polydisc P = {|B − B⁰| < r} about a real field B⁰
   (the form of S_j). For real B ∈ P, u(B) is a real configuration, so f_h(B) is the value of the quotient there,
   continuous in h. On P, f_h is analytic and bounded uniformly for h near h⁰: u(P) lies in the analyticity domain of
   the R-terms (Lemma 2.5, step 1, with RG1 (1.15)), where they satisfy CRE (2.31), p.260, and the bounds of LFR2
   (1.99)–(1.100), p.390, with constants independent of the history (Lemma 2.10). By Montel's theorem every sequence
   h_n → h⁰ has a subsequence along which f_{h_n} converges locally uniformly on P. Every limit agrees with f_{h⁰} on
   the real points of P, which form an open subset of the real space ℝ^N of B, and P is connected. An analytic
   function on a connected open set of ℂ^N that vanishes on a nonempty open subset of its real points vanishes
   identically, so every limit is f_{h⁰}, and f_h → f_{h⁰} locally uniformly on P. The polymer expansions and the
   sums over large-field regions converge uniformly for h near h⁰, with the activity bounds of LFR2 pp.388–389 on
   real fields and the bounds (1.99)–(1.100) and CRE (2.31) on P as majorants.
4. *Uniformity in the external fields.* The domains of analyticity have the radii α^T_{i,j}, which do not depend on h.
   The domain (3.43) of CRE p.276 bounds the scaled fluctuation field A by C₁p₁(ĝ_k); in the unscaled field its radius
   g_kC₁p₁(ĝ_k) is continuous in h, so a compact subset of it at h⁰ lies inside it for h near h⁰, and S_j is stated
   there as joint continuity in h and the fields.
   On a compact subset 𝒦 of a domain 𝒟, the Cauchy estimates on polydiscs of radius ½dist(𝒦, ∂𝒟) > 0 about the
   points of 𝒦 bound the derivatives in the external fields uniformly in h near h⁰. So the functions are equicontinuous there, and pointwise continuity in h
   is uniform on the compact subset. This is S_j.
5. *The coefficient.* β^T_{k+1} is computed by CRE (3.57) and (3.61), pp.281–282, from the whole-lattice E^{(k+1)},
   through the infinite-volume limit of Λ, as the torus T^{(k+1)} ↗ ℤ^d ("This limit exists by the localized
   representation (1.7)", RG1 (1.21), p.264). The limit is taken of Π_{k+1}(x, x′) at fixed x, x′, and β is
   Σ_x Π_{k+1}(x)x_μx_ν (RG1 (1.22)). Bałaban states the existence of the limit for each history and prints no rate.
   A rate uniform in h comes from the mechanism the sentence names. The localised terms are built from the
   generalized random-walk expansions of the propagators and of the background maps: each term is a sum over graphs
   with vertices localised in cubes and lines replaced by walks ω = ((α_0, X_0), …, (α_n, X_n)) of connected unions of
   big blocks, and the term of a walk is bounded by O(1)O(M₁^{−1/2})^{|ω|}M₁^{−|ω|/2}exp(−½δ₀d(ω, □_i, □_j)) (UV3
   (23), p.262; RG2 localises "using the generalized random walk expansions for propagators", p.1, and pp.13, 21).
   The operators attached to a single X_m are local inverses on X_m, which do not depend on the torus once its side
   exceeds diam X_m. So within one step, for a fixed polymer X ∋ 0, the torus enters only through graphs whose walks
   have total length at least a fixed multiple of the side, and these are bounded by the same bounds times e^{−c·side}.
   The inputs of the step also come from the torus: the effective action of the earlier steps, with the R-terms
   R^{(i)} summed over X "in T_ξ" (CRE (2.33), p.260), which the R-operation of LFR1 (0.3)–(0.6) produced. This is
   handled by induction over the steps, with the claim W_j: every localised term F(X) produced by the steps 0, …, j
   (regular, R-, and B-terms) with diam X at most a third of the side differs from the term of the same construction
   on L^{−j}ℤ^d, to which CRE extends the sums ("to all domains X ∈ D_j for the space L^{−j}Z^d", CRE p.281), by at
   most C_We^{−c·side} times its bound, uniformly in h on H_j. W_{−1} is empty. In step j+1 the new terms are
   analytic functions of the inputs on the domains of CRE p.259, bounded by the inductive bounds, so by Cauchy
   estimates a change of the inputs by e^{−c·side} times their bounds changes the outputs by C e^{−c·side} times
   theirs; the step's own expansions, including the polymer expansions (0.5) of the R-operation, whose activities
   decay as exp(−κd(X)) (LFR2 pp.388–389), add the winding contributions bounded as above; and terms that wrap the
   torus are bounded by exp(−κd_j(X)) with d_j(X) at least a fixed multiple of the side. The constants are those of
   the steps, uniform in h on H_k (Lemma 2.10). C_W may grow with j, but only k + 1 steps enter at depth k, and only
   uniformity in h at fixed k is needed here.
   So Π_{k+1}(x; h) on the torus converges to its limit at fixed x uniformly in h, and with the domination
   Σ_x|Π_{k+1}(x; h)||x|² ≤ C_ΛE₀, uniform in h and in the torus (Lemma 2.5 on the tube domains, Proposition 2.11,
   step 5), the finite-volume values of β converge uniformly in h near h⁰. Each is continuous in h by steps 1–4. So
   β^T_{k+1} is
   continuous. ∎

**Proposition 2.13 (Matching for the Tube Construction).** Let γ be small, and γ′ := (γ^{−2} + C)^{−1/2}. For every K
and every g ∈ (0, γ′] there is a bare coupling g_0 such that the flow of the tube construction for (K, g) has g_K = g
and (x_0, …, x_k) ∈ H_k for all k ≤ K. Along this flow (i) and (ii) of Lemma 2.1 hold.

*Proof.*
1. *Projecting onto the tube.* Let P_k be the Euclidean projection of ℝ^{k+1} onto the closed convex set H_k. It is
   nonexpansive, hence continuous. Define the projected flow by x_{k+1} := x_k − β^T_{k+1}(P_k(x_0, …, x_k)), with
   β^T_{k+1} evaluated at the history of the projected point. Then x_K =: F(x_0) is continuous in x_0 by
   Proposition 2.12.
2. *The interval.* By the *Consequence* above, |β^T_{j+1} − b_{j+1}| ≤ δ′ at every history of H_j, so
   Σ_{j=m}^{n−1}β^T_{j+1} ∈ [b(n−m) − C, b′(n−m) + C] for the projected flow, by Theorem 8.1 (Remark 2.3). This uses
   only that the arguments of β^T lie in H_j, not that the flow itself does. With m = 0 and n = K,
   F(x_0) ∈ [x_0 − b′K − C, x_0 − bK + C]. So F(ℓ_0) ≤ t ≤ F(u_0), and F takes the value t at some x_0 ∈ T_0.
3. *The projection is inactive.* For this solution, step 2 on [m, n) gives b(n−m) − C ≤ x_m − x_n ≤ b′(n−m) + C for
   0 ≤ m < n ≤ K, and with n = K, x_m ∈ [t + b(K−m) − C, t + b′(K−m) + C] = T_m. So (x_0, …, x_k) ∈ H_k, P_k is the
   identity at every step, and the projected flow is the flow of the tube construction. Since ℓ_k ≥ t − C ≥ γ^{−2},
   its couplings lie in (0, γ]. Then (i) is the bound x_k ∈ T_k, and (ii) is the window bound on [k, l). ∎

*What Is Proved for β_j.* For every target (K, g) with g ≤ γ′, the tube construction for (K, g) is CRE's construction
with its parameters evaluated at the couplings ĝ_j of the tube (Lemma 2.10), and at every depth k ≤ K:
- item 1 concerns the zero-coupling coefficients b_j only, and holds as stated (Theorem 8.1);
- its β^T_j satisfies the per-step bounds of (W) with δ′ and item 5 with C_rem + C_Rγ^{κ₀−6} on the histories of H_k
  (*Consequence*);
- β^T_{k+1} is continuous on H_k (Proposition 2.12);
- item 2 holds: a bare coupling g_0 gives the flow with g_K = g inside H_K (Proposition 2.13);
- items 3 (with δ′ in place of δ) and 4 hold along that matched flow.
This is not a statement about CRE's printed construction, whose parameters jump or move with the couplings, so that
its β_{k+1} is not a continuous function of the history (*CRE's Construction as a Function of the History*). The construction depends on the target (K, g): the parameters, the
densities ρ_k, the effective actions, the coefficients β^T, the couplings g_k, and the bare coupling g_0 are those of
the tube of (K, g), and objects of different targets are not identified with each other. The constants in the bounds (C_Λ, C₃, C_rem, C′, C_Σ, K_R,
C_R, δ′, and C₀) are independent of K and g. Statements that combine several targets, such as a limit K → ∞ at fixed
physical scale, use only these uniform bounds and the properties of each target's own construction.

## 3. Exact One-Loop Decomposition

### 3.1 Linear-Algebra Setting

All spaces are finite-dimensional real inner-product spaces (a finite torus); infinite volume is handled in
Remark 3.4.
- X: fine Lie-algebra-valued 1-forms. Y: fine 0-forms, taken orthogonal to ker D.
- D: Y → X, injective; this is D_U, the linearised gauge action at the background U.
- h: X → X symmetric, with h ≥ 0, hD = 0, and h positive definite on (ran D)^⊥.
- Q: X → Z onto, the linearised k-fold average (Z: level-k coarse 1-forms).
- P: Y → Ȳ, restriction to level-k sites (L odd, so these are fine sites). PPᵀ = 1.
- D̄: Ȳ → Z, injective (orthogonal to coarse constants).
- **Covariance:** QD = D̄P. (This is the linearisation of M(uUv) = uM(U)v, RG1 (0.6).)
- Y_0 := ker P, the residual gauge algebra (gauge transformations trivial at level-k sites); D_0 := D|_{Y_0}.

**One-loop factor.** In Bałaban's normalisation (axial gauge in blocks, Faddeev–Popov determinant 1, group δ-function
linearised to δ(QA)), the one-loop factor of the k-step constrained integral is

  Z_k[h] = c · det(QQᵀ)^{−1/2} · det(h|_W)^{−1/2} · det(D_0ᵀD_0)^{1/2},  W := ker Q ⊖ D(Y_0).

Here c does not depend on the background. *Reason.* The axial slice meets each residual orbit once, and the map
(slice, ω) ↦ A_s + Dω has block-triangular Jacobian with determinant det D_tree = 1. So the slice integral equals
∫ e^{−½⟨A,hA⟩} δ(QA) dA divided by ∫_{Y_0} dω. The δ-integral equals det(QQᵀ)^{−1/2} ∫_{ker Q}. Splitting
ker Q = W ⊕ D(Y_0) with the induced orbit measure det(D_0ᵀD_0)^{1/2} dω gives the formula.

**Definitions.** For each level j:
- Δ_j is the quadratic form on Z_j ⊖ ran D̄_j given by ⟨z, Δ_j z⟩ := min{⟨A, hA⟩ : Q_j A ∈ z + ran D̄_j}. It is the
  gauge-invariant coarse action of level j. At U = 1 it is Bałaban's ⟨B, Δ_j B⟩ = ⟨dH_jB, dH_jB⟩ (PRT1 (1.65)).
- F_j := ½ log det_⊥(Δ_j) − ½ log det(D̄_jᵀD̄_j).
- At level 0 (Q_0 = 1, D̄_0 = D): Δ_0 = h|_{(ran D)^⊥}, so F_0 = ½ log det_⊥(h) − ½ log det(DᵀD).

### 3.2 The Identity

**Proposition 3.1.** log Z_k[h] = F_k − F_0 + const.

*Proof.* Let K := ker Q and Δ_F := h + DDᵀ, which is invertible. Then Δ_F D = D(DᵀD), hence
Δ_F^{−1}D = D(DᵀD)^{−1}. Write S := QΔ_F^{−1}Qᵀ and R := P(DᵀD)^{−1}Pᵀ.

1. *Feynman form.* Define h_F := Π_K(h + D_0D_0ᵀ)Π_K on K, where D_0D_0ᵀ = D(1−PᵀP)Dᵀ. Decompose
   K = W ⊕ D(Y_0). Then h(D Y_0) = 0, ⟨Dω, hw⟩ = 0, and D_0ᵀw = 0 for w ∈ W. So h_F = h|_W ⊕ (D_0D_0ᵀ)|_{D(Y_0)} and
   det h_F = det(h|_W)·det(D_0ᵀD_0). Therefore

     log Z_k = −½ log det(QQᵀ) − ½ log det h_F + log det(D_0ᵀD_0) + const.

2. *Ghost (Schur).* On Y = Y_0 ⊕ ran Pᵀ: det(DᵀD) = det(D_0ᵀD_0) · det((P(DᵀD)^{−1}Pᵀ)^{−1}). Hence

     det(D_0ᵀD_0) = det(DᵀD) · det R.

3. *Constraint.* h_F = Π_K(Δ_F − DPᵀPDᵀ)Π_K. Two standard identities:
   - det(Π_KΔ_FΠ_K) = det Δ_F · det S / det(QQᵀ) (constrained Gaussian);
   - the matrix determinant lemma: det h_F = det(Π_KΔ_FΠ_K) · det_Ȳ(1 − N), with N := PDᵀ C DPᵀ and
     C := Δ_F^{−1} − Δ_F^{−1}QᵀS^{−1}QΔ_F^{−1} (the inverse of Π_KΔ_FΠ_K on K, extended by 0).

   Using Δ_F^{−1}D = D(DᵀD)^{−1} and QΔ_F^{−1}D = D̄P(DᵀD)^{−1}:
   - DᵀCD = 1 − (DᵀD)^{−1}PᵀD̄ᵀS^{−1}D̄P(DᵀD)^{−1};
   - hence 1 − N = R D̄ᵀ S^{−1} D̄ R, and det_Ȳ(1 − N) = (det R)² det(D̄ᵀS^{−1}D̄).
4. *Collecting.* The factors det(QQᵀ) cancel, and so do the factors det R (−½·2 log det R + log det R = 0):

     log Z_k = [−½ log det Δ_F + log det(DᵀD)] + [−½ log det S − ½ log det(D̄ᵀS^{−1}D̄)] + const.

5. *First bracket.* On X = ran D ⊕ (ran D)^⊥, Δ_F = (DDᵀ)|_{ran D} ⊕ h|_⊥. So the first bracket equals
   −½ log det_⊥ h + ½ log det(DᵀD) = −F_0.
6. *Second bracket.* Let M := S^{−1}, so ⟨z, Mz⟩ = min{⟨A, Δ_F A⟩ : QA = z}. Decompose Z = ran D̄ ⊕ (ran D̄)^⊥:
   - det M = det(M_∥) · det(M/M_∥), with det(M_∥) = det(D̄ᵀMD̄)/det(D̄ᵀD̄).
   - So the second bracket equals ½ log det(M/M_∥) − ½ log det(D̄ᵀD̄).
   - The Schur complement is (M/M_∥)(z) = min over A with QA ∈ z + ran D̄ of ⟨A, (h + DDᵀ)A⟩. That set is invariant under
     A ↦ A + Dω (QDω = D̄Pω ∈ ran D̄). Since h is gauge-invariant, choose ω = −(DᵀD)^{−1}DᵀA to make DᵀA = 0. So
     M/M_∥ = Δ_k, and the second bracket equals F_k.

Check: k = 0 gives log Z_0 = 0 (the constraint fixes everything). ∎

**Corollary 3.2 (Steps).** The one-loop factors of RG steps 1, …, k compose: the δ-constraints compose exactly, and
nested Gaussian integrations multiply by the Schur-complement identity. So Σ_{j<k} log Z^{(j)}[h] = log Z_k[h], and the
step-(k+1) one-loop term is

  **log Z^{(k)}[h] = F_{k+1} − F_k + const.**

**Lemma 3.3 (Full-Space Form).** Δ_k vanishes on ran D̄ and is positive on (ran D̄)^⊥. Hence
log det_⊥ Δ_k = log det(Δ_k + D̄D̄ᵀ) − log det(D̄ᵀD̄), and

  **F_k = ½ log det(𝒟_k) − log det(D̄ᵀD̄),  𝒟_k := Δ_k + D̄D̄ᵀ.**

**Remark 3.4 (Regulator and Infinite Volume).** Replace h by h_m := h + m²Π_⊥, where Π_⊥ is the orthogonal projection
onto (ran D_U)^⊥. This is gauge-covariant, h_mD = 0, and h_m is positive on (ran D)^⊥ with no harmonic zero modes, so
Proposition 3.1 holds exactly on every finite torus for every m > 0.
- The true one-loop factors Z^{(k)} are already massive: fluctuations with vanishing block averages satisfy a Poincaré
  inequality (PRT2 Lemma 2.4). So they are continuous at m = 0.
- All second-order Taylor coefficients used below are taken at a fixed external momentum p ≠ 0, where they are
  absolutely convergent momentum integrals, and they converge as the torus grows and then m → 0.
- So Corollary 3.2 holds for the infinite-volume polarisation symbols at every p ≠ 0, and, by continuity of the massive
  step symbols, at p = 0.

### 3.3 Which h Is Meant: J-Terms

Bałaban's step Gaussian is taken at the constrained minimiser U* = U_{k+1}(e^{iB}), where ∇A(U*) = Q_{k+1}ᵀλ ≠ 0. Its
quadratic form is the Lagrangian Hessian h_L = Hess A − ⟨λ, Hess φ_{k+1}⟩ on the constraint tangent space, modulo the
residual gauge directions. RG1 (1.5) writes this out: the J-term is −2⟨H hC̃^{(2)}, J⟩, with J the gradient
(RG1 (1.8)).

Throughout, h := Π_⊥ Hess A(U) Π_⊥ (Π_⊥ onto (ran D_U)^⊥). This form is gauge-invariant (hD = 0), the same for all
levels, and involves no λ. The Hessian of a gauge-invariant function transforms covariantly even off-shell, because
the coordinates X ↦ U e^{iX} transform linearly. Differentiating ⟨∇A, Dω⟩ ≡ 0 shows that
h_L − h = (terms linear in ∇A(U) or λ), and λ = (QQᵀ)^{−1}Q∇A. Define the **step J-term**

  J^{(k)}(U) := log Z^{(k)}_{Bałaban}(U) − (F_{k+1} − F_k)(U).

## 4. The J-Terms Do Not Contribute to the Marginal Coefficient

**Notation.** "Symbol" means the Fourier multiplier on the coarse lattice (unit spacing, momentum p ∈ [−π, π]⁴) of a
translation-covariant linear map, or of a quadratic form's kernel. The second-order Taylor coefficient in B of a
function of the coarse field B has the symbol Π(p) (the polarisation). The marginal coefficient is read off from the
O(|p|²) part of Π(p) (RG1 (1.22)). Write v_ν(p) := e^{ip_ν} − 1, so that pure-gauge coarse fields are
B = v(p)ω̂ e^{ipy}.

**Lemma 4.1 (Second-Order Vanishing).** Let T(p) (4×4 in the vector index, ⊗ 1 on g) be C² near p = 0 with
‖∂^αT‖ ≤ C for |α| ≤ 2. Suppose:
- (i) T(p)v(p) = 0;
- (ii) T is covariant under the hyperoctahedral group (signed permutations R): T(Rp) = ρ(R)T(p)ρ(R)^{−1}.
Then ‖T(p)‖ ≤ (C/2)|p|². It is applied to the symbol of PRT1 (1.65) and to the J-coefficient of Proposition 4.2. The
type-checked Lean core is `symbol_quadratic_bound`, used in `BalabanFormal.jterm_quartic`.

*Proof.* (Lean core `BalabanFormal.jterm_quartic`, through `symbol_quadratic_bound`.)
1. At p = 0, (ii) says T(0) commutes with every signed permutation matrix. Commuting with the sign changes forces
   T(0) to be diagonal, and commuting with the permutations forces T(0) = t·1.
2. Differentiate (i) at 0 in the direction e_μ. Since v(0) = 0 and ∂_μv(0) = i e_μ, this gives i t e_μ = 0, so t = 0.
3. Let a_ρ := ∂_ρT(0). Covariance under the reflection R_λ (p_λ ↦ −p_λ) gives
   (a_ρ)_{μν} = (−1)^{[ρ=λ]+[μ=λ]+[ν=λ]} (a_ρ)_{μν} for every λ.
4. Sum the exponents over λ = 1, …, 4: the total is 3, which is odd. So for at least one λ the exponent is odd, and that
   entry vanishes. Hence ∇T(0) = 0.
5. Taylor's theorem then gives ‖T(p)‖ ≤ (C/2)|p|². ∎

**Proposition 4.2 (J-Terms).** Let J^{(k)} be the step J-term of §3.3, evaluated on the background U_{k+1}(e^{iB}), that
is, the contribution of the term −2⟨H hC̃^{(2)}, J⟩ of RG1 (1.5). The symbol Π_J^{(k)}(p) of its second-order Taylor
coefficient in B satisfies ‖Π_J^{(k)}(p)‖ ≤ C|p|⁴ for |p| ≤ π, with C independent of k. In particular J^{(k)}
contributes nothing to b_{k+1}.

*Proof.*

*(a) The J-coefficient Θ.* Let Ĵ(U, j) be the step Gaussian built from h + δh(U, j), minus (F_{k+1} − F_k)(U). Here j is
an independent fine adjoint 1-form, δh is the part of h_L − h that is linear in (∇A, λ), and ∇A is replaced by j and λ
by (QQᵀ)^{−1}Qj. These are the independent variables (U, J) of RG1 (1.8)–(1.9). Then J^{(k)}(U) = Ĵ(U, ∇A(U)) and
Ĵ(U, 0) = 0.
- The step Gaussian is massive: its covariance C^{(k+1)}(U) decays exponentially and is analytic in U, uniformly in k
  (PBG Thm 3.15 with Thm 3.4). The operator δh(U, j) is local and linear in j.
- Hence log det(1 + C δh) is analytic in (U, j) near (1, 0), with exponentially decaying derivative kernels and
  uniform constants.
- So Ĵ(U, j) = ⟨j, Θ(U)⟩ + 𝓡(U, j), where |𝓡| is quadratic in j, and Θ(U) is a fine adjoint 1-form depending
  analytically on U.
- Θ(1) = 0: at U = 1 the construction is invariant under constant gauge transformations, so each Θ(1)(b) is an
  Ad-invariant vector of g, hence zero.

*(b) Second order in B.* Write U = U_{k+1}(e^{iB}) and expand ∇A(U) = j_1(B) + j_2(B) + …. The second-order part of
J^{(k)} is ⟨j_1(B), Θ_1(B)⟩ + ⟨j_2(B), Θ(1)⟩ + 𝓡_2(j_1(B)), where Θ_1 is the linearisation of B ↦ Θ(U_{k+1}(e^{iB})).
The middle term is 0.

*(c) The gradient term.* j_1 = Hess A(1)·H_{k+1}B = dᵀdH_{k+1}B. Since H_{k+1}B minimises ‖dA‖² subject to
Q_{k+1}A = B (PRT1 (1.60)–(1.65)), dᵀdH_{k+1}B = Q_{k+1}ᵀλ_B. Then ⟨B, Δ_{k+1}B⟩ = ‖dH_{k+1}B‖² = ⟨B, λ_B⟩, so
λ_B = Δ_{k+1}B. Hence j_1 = Q_{k+1}ᵀΔ_{k+1}B.
- The symbol Δ_{k+1}(p) is analytic and bounded with its derivatives, uniformly in k (PRT1 (1.63)–(1.67)).
- It annihilates pure gauge fields: a pure-gauge B has a pure-gauge minimiser, with zero energy.
- It is hypercubic-covariant.
- By Lemma 4.1, ‖Δ_{k+1}(p)‖ ≤ C|p|² (PRT1 (1.65)). Therefore 𝓡_2(j_1) = O(|p|⁴).

*(d) The Θ term.* ⟨j_1, Θ_1(B)⟩ = ⟨Δ_{k+1}B, τB⟩ with τ := Q_{k+1}Θ_1, a coarse translation-covariant map.
- *Regularity.* τ is C² with uniform bounds: Θ_1 is the derivative at 0 of an analytic, exponentially decaying family
  (Cauchy estimates); B ↦ U_{k+1}(e^{iB}) is analytic (VAR §G, Prop. 9); Q_{k+1} is local.
- *Pure gauge.* For B = ∂̄ω, the minimiser U_{k+1}(e^{i∂̄ω}) is 1^u with u constant on the blocks, at linear order. It is
  in axial gauge in the blocks, has action 0, and has the right averages by the covariance RG1 (0.6). By uniqueness of
  the minimal orbit (VAR Thm 1) it is the minimiser. Gauge transformations constant on the blocks preserve the axial
  gauge and commute with the averaging, so Θ(1^u) = Ad(u)Θ(1) = 0. Hence τ(p)v(p) = 0.
- *Covariance.* τ is hypercubic-covariant. Bałaban's averaging RG1 (0.4), p.253, with contour families generated by all
  permutations, and his axial gauge, defined through the averaged contour variables RG1 (0.11), are lattice-Euclidean
  covariant (RG1 pp.252–253).
- So by Lemma 4.1, ‖τ(p)‖ ≤ C|p|².

*(e) Conclusion.* Π_J^{(k)}(p) = Δ_{k+1}(p)*τ(p) + τ(p)*Δ_{k+1}(p) + O(|p|⁴) = O(|p|⁴), with uniform constants
(`BalabanFormal.jterm_quartic`). The marginal coefficient is determined by the O(|p|²) part (RG1 (1.22)). ∎

## 5. The k-Step Total, and the J-Terms Seen from the Top

**Conventions.**
- Top units: T^{(k)} is the unit lattice, and the bare spacing is η_k = L^{−k}.
- For a functional 𝔉 of the top field B, write 𝔉(e^{iB}) = 𝔉(1) + ½⟨B, Π_𝔉 B⟩ + O(B³), and call Π_𝔉(p) its
  polarisation symbol.
- A(U_k(e^{iB})) = ½⟨B, Δ_k B⟩ + O(B³). Here Δ_k is Bałaban's coarse operator (PRT1 (1.65)–(1.67)): its symbol is
  analytic, it annihilates pure gauge, and γ_0|∂̂B|² ≤ ⟨B, Δ_k B⟩ ≤ γ_1|∂̂B|² with γ_0, γ_1 depending only on d.
- **𝔅_r**: the complex ball of top fields with sup|B| ≤ r and sup|∂̄B| ≤ r (top units).
- **Analyticity of the background.** For r small, U_k(e^{iB}) with B ∈ 𝔅_r lies in the complex regularity spaces
  U_j^c(X, α_0, α_1) of RG1 (1.11)–(1.16), for every j ≤ k (VAR Thm 1, §G and (181); RG1 p.263). So every functional
  below that Bałaban proves analytic on those spaces is analytic in B ∈ 𝔅_r.
- **Cauchy estimate.** Let 𝔉(B) be analytic on 𝔅_r, translation-covariant, and bounded by M per top unit cube. Then its
  polarisation symbol satisfies ‖Π_𝔉(p)‖ ≤ 2(1+π)²M/r² for all p. (A plane wave of momentum p and unit amplitude has
  𝔅-norm at most 1+π.) It is applied to the localized terms of RG1 (0.29).

**Proposition 5.1 (Total).** Let ℒ_k(B) := Σ_{j=1}^{k} E^{(j)}(0, U_k(e^{iB})), the zero-coupling step terms of
RG1 (1.6) evaluated at the top background, i.e. the k-step Gaussian. Then (RG1 (0.28)–(0.30); proof below)
  Π_{ℒ_k}(p) = Φ_k Δ_k(p) + E_k(p),  Φ_k := Σ_{j=1}^{k} b_j,  sup_p ‖E_k(p)‖ ≤ C,
with C independent of k.

*Proof.*
1. By RG1 (0.28), E^{(j)}(U_k) = β_jA(U_k) + Σ_{X∈D_j} V^{(j)}(X, U_k).
2. Each V^{(j)}(X, ·) is analytic on U_j^c, with |V^{(j)}(X, U)| ≤ O(1)(L^jη)^{4+α} e^{−κ d_j(X)} (RG1 (0.29), α > 0).
   As in RG1 (0.30), the sum over X meeting a fixed top unit cube is at most C(L^jη)^α.
3. By the Cauchy estimate, the polarisation of Σ_X V^{(j)} is bounded by C(L^{j−k})^α. Summing over j ≤ k gives at
   most C(1 − L^{−α})^{−1}.
4. At zero coupling β_j = b_j, and the polarisation of A(U_k(e^{iB})) is Δ_k. ∎

**Lemma 5.2 (Alias Summability; Bałaban).** At U = 1, for every k and every coarse momentum p (top units),
  Σ_{l} |(dH_k)^∧(p + l)| · |p + l|^α ≤ C,
where the sum runs over the aliases p + l of p in the fine Brillouin zone, (dH_k)^∧ is the symbol of B ↦ d(H_kB), α ∈
(0,1) is fixed once, and C depends only on d and α. This is the statement in PRT1 p.28–29 following PRT1 (1.63).

*Source of the range of α.* PRT1 p.29 states the bound for each pair μ, ν, for the expression PRT1 (1.63) multiplied by
|∂_ν(p + l)||p + l|^α, as the input of the Hölder bounds on ∂_ν(H_kB)_μ; the curvature component is a difference of two
such terms. PRT1's Hölder exponents range over 0 ≤ α < 1, with constants depending on d and α that blow up as α → 1
(PRT1 (1.109)–(1.112), pp.35–36). The proof that PRT1 p.29 points to is that of Lemma 2.4 in Bałaban, Commun. Math. Phys.
89 (1983). On its pp.585–586 it bounds the same alias sum for the scalar kernel ∂G_jQ_j^* through the factors
|u_j(p + l)| ≤ O(1)∏_μ(1 + |l_μ|)^{−1} and |∂(p + l)|/|p + l|² ≤ O(1)|p + l|^{−1}. These leave
Σ_{l≠0}|p + l|^{α−1}∏_μ(1 + |l_μ|)^{−1}, which is finite for α < 1, and the page says "the constant depends on α<1".

**Proposition 5.3 (J-Terms, Total).** Let 𝒥_k(B) := Σ_{j=0}^{k−1} J^{(j)}(U_k(e^{iB})), with J^{(j)} as in §3.3. Then
sup_p ‖Π_{𝒥_k}(p)‖ ≤ C, uniformly in k (from PRT1 (1.63) and Lemma 5.2; proof below). The summation of steps 2–5 is the
type-checked Lean core `BalabanFormal.jterm_assembly`.

*Proof.* Fix j and set m := j+1 ≤ k.
1. *Reduction to level m.* U_k(e^{iB}) = U_m(V*(B)) by nesting, where V*(B) = (U_k(e^{iB}))^{(m)} =
   exp(iQ_mH_kB + O(B²)). Indeed, M^k is M^{k−m} after M^m, so a minimiser on {U : M^k(U) = e^{iB}} also minimises on
   the subset {U : M^m(U) = V*(B)}, and the minimal orbit is unique (RG1 (0.21)–(0.22), p.256). J^{(j)} ∘ U_m has zero first-order coefficient at the trivial
   background (§4(a)–(b)). So the top polarisation of J^{(j)}(U_k(e^{iB})) is ⟨V_1, Π_J^{(j)} V_1⟩ with
   V_1 := Q_m H_k B. Here Π_J^{(j)} is the level-m symbol of Proposition 4.2, for the J-term of RG1 (1.5):
   ‖Π_J^{(j)}(p′)‖ ≤ C|p′|⁴ on the whole level-m zone, and it is transverse.

   *Zero-curvature terms.* In step 4's normalisation the level-m bond logarithm carries the factor Mη = L^{m−k}, which
   step 2 accounts for, so the first-order part of V*(B) reads i(Mη)Q_mH_kB. It equals this only up to a level-m field
   of zero curvature (next paragraph and step 4). Such a field is a gradient plus a constant. Π_J^{(j)} annihilates it:
   transversality kills the gradient, and the factor |p′|⁴ of Proposition 4.2 kills the constant. So it does not change
   ⟨V_1, Π_J^{(j)} V_1⟩.

   *The first-order background.* By RG1 (0.21)–(0.22), p.256 (contract RG1_021_orbit), U_k(V) lies in the unique regular
   orbit of minimisers of the Wilson action on {U : M^k(U) = V}, under the gauge transformations equal to 1 on T^{(k)},
   which leave M^k unchanged. At V = 1 the configuration 1 is such a minimiser (its action is zero), so the representative
   can be chosen with U_k(1) = 1. Then U(t) := U_k(e^{itB}) = exp(itA_1 + O(t²)) bondwise, analytic in t (VAR §G). Let Q̃_k
   be the first-order part of M^k at U = 1, in the normalisation of step 4. Step 4's computation with m = k gives
   Q̃_kA = Q_kA + ∂ω_k(A), with ω_k linear and ∂ the gradient on T^{(k)}. The constraint gives Q̃_kA_1 = B, so Q̃_k is
   onto.

   Three facts give d_ηA_1 = d_ηH_kB.
   - A_1 minimises ‖d_ηA‖² over {A : Q̃_kA = B}. Since Q̃_k is onto and M^k is analytic near 1, the implicit function
     theorem gives, for each such A, regular U_t = exp(itA + O(t²)) with M^k(U_t) = e^{itB}. At U = 1 the quadratic part
     of the Wilson action (RG1 p.252) is a positive multiple c of ‖d_ηX‖², with U = e^{iX}. Minimality gives
     ct²‖d_ηA_1‖² + O(t³) ≤ ct²‖d_ηA‖² + O(t³); divide by t² and let t → 0.
   - The sets {d_ηA : Q̃_kA = B} and {d_ηA : Q_kA = B} coincide. A gauge transformation A ↦ A − ∂^ηλ changes Q_kA by
     −∂Q′_kλ (PRT1 (1.20), p.20). By the gauge covariance of RG1 (0.4), it changes Q̃_kA by the gradient of −λ on
     T^{(k)}. Either change can be chosen to cancel ∂ω_k(A), and neither changes d_ηA. The common set is affine, so
     ‖·‖² has exactly one minimiser on it.
   - H_kB attains that minimum. PRT1 p.29 gives H_kB as a minimiser of ½⟨∂A, ∂A⟩ on {Q_kA = B, R∂*A = 0}. That slice
     meets every orbit of the gauge transformations λ with Q′_kλ = 0. R is the orthogonal projection onto ΔN(Q′_k)
     (PRT1 p.25), so λ ∈ N(Q′_k) with Δλ = R∂*A gives R∂*(A − ∂λ) = 0. PRT1's blocks are corner blocks (PRT1 p.18),
     RG1's are centred: the centred Q_k is PRT1's Q_k composed with a fixed fine translation T, so the centred H_k is
     T^{−1} composed with PRT1's H_k, and R transforms in the same way. Minimality and curvature norms are
     translation invariant, so the fact holds for the centred blocks.

   So A_1 − H_kB has zero curvature, and its level-m average plus the gradient of step 4 has zero curvature too. The same
   three facts give the expansion A(U_k(e^{iB})) = ½⟨B, Δ_kB⟩ + O(B³) of the conventions, since PRT1 p.29 defines
   ⟨B, Δ_kB⟩ as ⟨∂H_kB, ∂H_kB⟩.
2. *Change of units.* Write V_1 in top units: modes q with |q_μ| ≤ π L^{k−m}, and level-m momentum p′ = L^{−(k−m)}q.
   A level-m bond carries L^{−(k−m)} times the top amplitude, and there are L^{4(k−m)} level-m sites per top site. So
     |⟨V_1, Π_J^{(j)} V_1⟩| ≤ C L^{−2(k−m)} Σ_q |q|² |(d̄V_1)^∧(q)|²
   (hypothesis `hunits` of `BalabanFormal.jterm_assembly`). Transversality is used here: on transverse modes
   |q|²|V̂_1|² ≤ C|(d̄V_1)^∧|².
3. *Fractional power.* On the level-m zone |q| ≤ 2π L^{k−m}, so |q|² ≤ (2πL^{k−m})^{2−2α}|q|^{2α}. Therefore the bound
   is at most C L^{−2α(k−m)} Σ_q |q|^{2α} |(d̄V_1)^∧(q)|² (`BalabanFormal.jterm_assembly`).
4. *Alias summability.* Set M := L^m = 2h + 1 and η := L^{−k}. In top units the fine lattice has spacing η and the
   level-m lattice has spacing Mη = L^{m−k}. Fields are in physical normalisation: a bond of length ε carries the
   logarithm εA_μ. The lattice curl at spacing ε is (d_εA)_{μν}(x) := ε^{−1}(A_ν(x + εe_μ) − A_ν(x) − A_μ(x + εe_ν) +
   A_μ(x)), and d̄V_1 means d_{Mη}V_1.

   *The first-order level-m average.* The chain averages with RG1 (0.4), p.253 (READINGS.md R47). Its m-th order average
   is the m-fold iterate of the one-step average by construction: each step's kernel is the one-step
   δ(Ū(c)V^{−1}(c)) (RG1 (0.17), (0.19), p.255). At U = 1, on a coarse bond c with c₊ = c₋ + Le_μ, the first-order part
   of the logarithm in RG1 (0.4) is

     Σ_{x∈B(c₋)} L^{−d} A([x, x′]) + ω(c₋) − ω(c₊),  ω(y) := Σ_{x∈B(y)} L^{−d} |G(y, x)|^{−1} Σ_{Γ∈G(y,x)} A(Γ),

   with A(Γ) the sum of the bond logarithms along Γ. Indeed, the loop logarithm is A(Γ) + A([x, x′]) − A(Γ′) − A(c) to
   first order, the term −A(c) cancels against the factor U(c), and the contour families at c₊ are the translates by c of
   those at c₋. This is L times PRT1 (1.8), p.19 (PRT1 normalises per unit coarse length), with the single contour
   replaced by the average over G(y, x). Its first term is L times PRT1's straight average PRT1 (1.11), and its endpoint
   terms form a coarse gradient.

   A straight average of a gradient is the gradient of the block means, so later averaging steps carry gradients to
   gradients. The composition of m straight averages over centred blocks is the straight average over the centred block
   of side M. PRT1 (1.16)–(1.18), p.20, states this for corner blocks ("It is easily seen"). For corner and centred
   blocks alike the path offsets sL + t run once over {0, …, L² − 1}, and for centred blocks the offsets Lr + o,
   with r and o in the centred block of side L, run once over the centred block of side L². So the first-order level-m
   bond logarithm is (Mη)Q_mA plus a level-m gradient, where

     (Q_mA)_μ(Y) := |B_m|^{−1} Σ_{r∈B_m} M^{−1} Σ_{t=0}^{M−1} A_μ(η(MY + r + te_μ)),  B_m := {−h, …, h}⁴.

   The gradient has zero curl, and Π_J^{(j)} is transverse (step 1), so the gradient drops out of ⟨V_1, Π_J^{(j)}V_1⟩.
   RG1's blocks are centred at the coarse points (RG1 p.252), and PRT1's blocks need not be. A translation of the blocks
   multiplies every Fourier coefficient by a unit phase, so none of the absolute values below changes.

   *The curvature identity.* The curl of a straight-path average is the sum of the fine plaquettes in the M × M square
   that the path sweeps out (discrete Stokes). Hence d_{Mη}Q_mA = P_m d_ηA, where

     (P_mF)_{μν}(Y) := |B_m|^{−1} M^{−2} Σ_{r∈B_m} Σ_{a,b=0}^{M−1} F_{μν}(η(MY + r + ae_μ + be_ν)).

   The weights of P_m are nonnegative and sum to one, as the weights η^{d+1} of PRT1 (1.18), p.20, do for Q_k. On a fine
   plane wave of momentum p, P_m therefore acts as a symbol σ_m(p) with |σ_m(p)| ≤ 1, times the level-m character of p.

   *Folding.* At U = 1, for the top input B̂(p)e^{ip·Y}, the fine field H_kB is a finite sum of plane waves with momenta
   p_a = p + 2πl_a in the fine zone (PRT1 (1.63)). Write ĉ_{μν}(a) for the coefficient of (d_ηH_kB)_{μν} at p_a. Subtract
   from each component of p_a a multiple of 2π/(Mη) to land in (−π/(Mη), π/(Mη)]; call the result q(a). On the level-m
   lattice p_a and q(a) have the same character, and |q(a)| ≤ |p_a| in the Euclidean norm. Distinct representatives give
   distinct characters, so the Fourier coefficient of (d̄V_1)_{μν} at q is Σ_{a: q(a)=q} σ_m(p_a)ĉ_{μν}(a). Hence, with
   the last step from Lemma 5.2 (PRT1 p.29),
     Σ_q |q|^{2α}‖(d̄V_1)^∧_{μν}(q)‖² ≤ Σ_q (Σ_{a: q(a)=q} |p_a|^α‖ĉ_{μν}(a)‖)² ≤ (Σ_a |p_a|^α‖ĉ_{μν}(a)‖)² ≤ C_H²‖B̂(p)‖².

   Here C_H ≤ C, with C from Lemma 5.2. PRT1 p.29 bounds Σ_l |∂_ν(p + l)||(H_kB)^∧_μ(p + l)||p + l|^α for each pair μ, ν
   by a constant depending on d and on the fixed α (Lemma 5.2), so in that form C_H is at most twice PRT1's constant. The
   norms are the invariant norms on the Lie algebra: at U = 1, H_k acts on every Lie-algebra component in the same way.

   Summing over the six planes μ < ν gives, by Lemma 5.2 (PRT1 p.29),
     Σ_q |q|^{2α}‖(d̄V_1)^∧(q)‖² ≤ 6C_H²‖B̂(p)‖²,
   uniformly in k and m, which is the bound step 3 needs.
5. *Sum.* Σ_{m≤k} L^{−2α(k−m)} ≤ (1 − L^{−2α})^{−1} (`BalabanFormal.jterm_assembly`). ∎

## 6. The Bare-Lattice One-Loop Polarisation

**Notation.** Lattice units (bare spacing 1), momenta ξ, k ∈ T⁴ = [−π, π]⁴, s(k) := Σ_μ 4 sin²(k_μ/2) = |k|² + O(|k|⁴).

### 6.1 The Infrared Lemma

**Lemma 6.1.** Let N(k, ξ) be a matrix-valued trigonometric polynomial with N(−k, −ξ) = N(k, ξ). Write N = N_2 + N_r,
where N_2 is a homogeneous polynomial of degree 2 in (k, ξ) and |N_r| ≤ C(|k| + |ξ|)³ near 0 (`SmoothNum.lemma61`). Set
  I(ξ) := ∫_{T⁴} N(k, ξ) / (s(k) s(k+ξ)) d⁴k/(2π)⁴.
Then, as ξ → 0,
  I(ξ) = a_0 + a_1·ξ + Σ(ξ) ln(1/|ξ|) + O(|ξ|²),  Σ(ξ) := (2π)^{−4} ∫_{S³} f_2(ω, ξ) dσ(ω),
where f_2(u, ξ) is the part quadratic in ξ of the Taylor expansion of f(u, ξ) := N_2(u, ξ)/(|u|²|u+ξ|²) at ξ = 0.
Single-propagator integrals ∫ M(k, ξ)/s(k) with M trigonometric are C^∞ in ξ. In fact a_0 = I(0) and a_1 = 0.

The type-checked Lean core `SmoothNum.lemma61` covers steps 0–4 below, for scalar N that is C³, even and zero at 0,
with the bounds of step 0 derived rather than assumed. The hypotheses hold for N(k, ξ) = Σ_μ sin k_μ sin(k_μ + ξ_μ).

*Proof.* Let G(k, ξ) := N(k, ξ)/(s(k)s(k+ξ)) and Δ²G(k) := G(k, ξ) + G(k, −ξ) − 2G(k, 0). The substitution k ↦ −k,
with the parity of N and of s, gives I(−ξ) = I(ξ). Hence a_1 = 0 and
  I(ξ) − I(0) = ½ ∫_{T⁴} Δ²G(k) d⁴k/(2π)⁴.

No integral is Taylor-expanded: the order-0 and order-1 parts of the integrand cancel in Δ² identically. Take
0 < |ξ| ≤ π/16. Work entrywise, so N is scalar, and use the norm |(k, ξ)| := max(|k|, |ξ|) on ℝ⁴ × ℝ⁴
(`SmoothNum.lemma61`).
0. *Bounds on N.* Only three properties of N are used: N is C³, N is even, and N(0, 0) = 0.
   - Evenness gives DN(0) = 0, so the Taylor polynomial forces N_2 = ½D²N(0).
   - Let M bound |D²N| and |D³N| on the ball |q| ≤ 2π + 1. This ball contains every (k, ξ) with k ∈ [−π, π]⁴ and
     |ξ| ≤ π/8.
   - The mean-value theorem on the ball of radius |q|, applied in turn to DN, N, D²N_r, DN_r and N_r (each vanishes
     at 0), gives |DN(q)| ≤ M|q|, |N(q)| ≤ M|q|², and |DᵗN_r(q)| ≤ M|q|^{3−t} for t = 0, 1, 2.
   - For F ∈ {N, N_r}, the mean-value theorem along v ↦ (k, v), |v| ≤ |ξ|, gives
     |F(k, ξ) − F(k, 0)| ≤ |ξ| sup|DF|. Applied to v ↦ F(k, v) − DF(k, 0)(0, v), it gives
     |Δ²F| ≤ 2|ξ|² sup|D²F|; the linear terms cancel in Δ².
   - If |ξ| ≤ |k|/2, every point of the segment has norm |k|. Hence N ∈ DC(2) and N_r ∈ DC(3) on
     {0 < |k| ≤ π/2, |ξ| ≤ |k|/2}, with constant 2M.
   - On the outer region (k ∈ [−π, π]⁴, |k| ≥ π/2, |ξ| ≤ π/8), the same estimates with |k| ≤ 2π + 1 give N ∈ DC(0),
     with constant 2M(2π + 1)². Also |N(k, ξ)| ≤ M|(k, ξ)|² ≤ M(|k| + |ξ|)².
1. *Second-difference calculus.* On {0 < |k| ≤ R, |ξ| ≤ |k|/2}, say F ∈ DC(m) if
   - |F| ≤ C|k|^m,
   - |F(k, ξ) − F(k, 0)| ≤ C|ξ||k|^{m−1},
   - |Δ²F| ≤ C|ξ|²|k|^{m−2}.

   The class DC is stable under the following operations (`SmoothNum.lemma61`):
   - sums;
   - products, by Δ²(FG) = Δ²F·G₀ + F₀·Δ²G + Δ⁺FΔ⁺G + Δ⁻FΔ⁻G;
   - reciprocals of functions with |F| ≥ c|k|^m, by 1/a + 1/b − 2/z = (−z(a+b−2z) − 2(a−z)(b−z))/(abz).

   On bounded regions DC(m) ⊂ DC(m′) for m′ ≤ m. Elementary trigonometry gives |k+ξ|² ∈ DC(2), s(k+ξ) ∈ DC(2) and
   q(k+ξ) := |k+ξ|² − s(k+ξ) ∈ DC(4) (`SmoothNum.lemma61`). The ingredients are:
   - cos(k ± ξ) = cos k cos ξ ∓ sin k sin ξ;
   - |x − sin x| ≤ 2|x|³;
   - |2 − 2cos y − y²| ≤ 5y⁴.

   Also s(p) ≥ (36/25π²)|p|² when all |p_μ| ≤ 5π/4. So h(p) := 1/s(p) − 1/|p|² = q/(s|p|²) satisfies h(k+ξ) ∈ DC(0)
   (`SmoothNum.lemma61`).
2. *Outer region* |k| ≥ π/2. Here G = N·s(k)^{−1}·s(k+ξ)^{−1} ∈ DC(−4), so |Δ²G| ≤ C|ξ|². The region contributes
   O(|ξ|²) (`SmoothNum.lemma61`).
3. *Inner ball* |k| < 2|ξ|. From |N| ≤ C(|k|+|ξ|)² and s ≥ c|·|²,
   |G(k, η)| ≤ C(|k|^{−2} + |k+η|^{−2}) for η ∈ {ξ, −ξ, 0}. Since ∫_{|k|<r}|k|^{−2} d⁴k = 2|B₁|r², the region
   contributes O(|ξ|²) (`SmoothNum.lemma61`).
4. *Annulus* 2|ξ| < |k| < π/2. Exactly,
     G = f + F_r,  F_r = N_r/(|k|²|k+ξ|²) + N[h(k)/|k+ξ|² + h(k+ξ)/|k|² + h(k)h(k+ξ)].
   - By step 1, F_r ∈ DC(−1), so |Δ²F_r| ≤ C|ξ|²|k|^{−3}. Also ∫_{2|ξ|<|k|<π/2}|k|^{−3} d⁴k ≤ 2π|B₁|
     (`SmoothNum.lemma61`).
   - For the homogeneous part write a = |k|², u = ⟨k, ξ⟩, c = |ξ|² and N_2 = p₀ + p₁ + p₂, with p₀ = A(k, k),
     p₁ = B(k, ξ), p₂ = Γ(ξ, ξ) bilinear in their arguments. Then
       f_2 = p₂/a² − 2p₁u/a³ − p₀c/a³ + 4p₀u²/a⁴,
     and the exact identity
       Δ²f − 2f_2 = 2[p₀(a²c² + ac³ − 12acu² − 4c²u² + 16u⁴) + 2p₁ua(2ac + c² − 4u²) + p₂(−a³c − a²c² + 4a²u²)]
                    / (a⁴|k+ξ|²|k−ξ|²)
     gives |Δ²f − 2f_2| ≤ C|ξ|⁴|k|^{−6} (`SmoothNum.lemma61`). Its integral over the annulus is O(|ξ|²).
   - f_2(·, ξ) is homogeneous of degree −4. In polar coordinates,
     ∫_{2|ξ|<|k|<π/2} f_2 = ln(π/(4|ξ|)) ∫_{S³} f_2(ω, ξ) dσ(ω), and Σ(ξ) = O(|ξ|²).

   Adding the three regions gives I(ξ) − I(0) = Σ(ξ) ln(1/|ξ|) + O(|ξ|²).
5. *Single-propagator integrals.* 1/s is integrable and M is smooth in ξ. ∎

### 6.2 Application to the Bare Lattice Functional

Let B_tb(U) := −½ log det(Hess A(U) + D_UD_Uᵀ) + log det(D_UᵀD_U). This is the lattice background-field one-loop
functional in Feynman gauge, with the Wilson action and normalised trace. It is gauge-invariant, because the
coordinates X ↦ Ue^{iX} transform linearly under gauge transformations, so the Hessian is covariant even off-shell.
Its polarisation symbol Ψ_tb(ξ) in the direction of a fine background b is a finite sum of:
- bubbles ∫ tr[V^{(1)} G V^{(1)} G], whose numerators are of the type in Lemma 6.1;
- tadpoles ∫ tr[V^{(2)} G].

Here G = s(k)^{−1}·1, because Hess A(1) + ddᵀ = −Δ_lat componentwise. V^{(1)} and V^{(2)} are the first- and
second-order background vertices of Hess A + DDᵀ and of the ghost operator DᵀD.

**Lemma 6.2 (Naive Continuum Limit).** The vertices are trigonometric polynomials in (k, ξ), odd and even respectively
under (k, ξ, b) ↦ (−k, −ξ, b). The lowest-order Taylor parts of V^{(1)} are linear in (k, ξ), and they are the
continuum background-field vertices of −D_b²·1 − 2 ad F_b (vector) and −D_b² (ghost).

*Proof.* Taylor expansion of 1 − Re tr e^{iX_p}: it equals ½ tr X_p² + O(X_p⁴). For U = e^{i(b + X)}, the plaquette
variable is X_p = (lattice curl of b + X) + ½[·,·] + (terms of higher order in the lattice spacing). At quadratic order
in X and to the lowest order in momenta, this reproduces the continuum form ½⟨X, (−D_b² − 2 ad F_b)X⟩ after adding the
Feynman term |D_bᵀX|². D_UᵀD_U is the lattice covariant Laplacian, whose lowest-order part is −D_b².

B_tb uses the coordinates X ↦ U_be^{iX} rather than e^{i(b+X)}. The two differ by X′ = X + ½[b, X] + O(b²X, bX²).
- The linear change S = 1 + ½ ad b turns Hess A into SᵀHess A S. At first order in b this adds ½(M(k+ξ) − M(k)) ad b̂,
  where M is the symbol of Hess A(1); it vanishes to second order at 0, so the added term has degree at least two in
  (k, ξ).
- The term ⟨∇A(b), ∂²X′(X, X)⟩ is of second order in b and contains no differences of X, so it is a tadpole.

Neither changes the linear parts of V^{(1)}. ∎

Hence each bubble numerator N = tr[V^{(1)} V^{(1)}] satisfies the hypotheses of Lemma 6.1: it is a trigonometric
polynomial, even, and zero at 0. Its N_2 is the product of the linear parts of the two vertices, which is the numerator
of the continuum Feynman-gauge background-field bubble. The tadpoles have one propagator, so by the last part of
Lemma 6.1 they are C^∞ in ξ and carry no logarithm. The logarithm in Ψ_tb is therefore fixed by the continuum vertices.

**Lemma 6.5 (Angular Coefficient).** Fix a background mode b̂_μ(ξ) ∈ g ⊗ ℂ. Put ⟨X, Y⟩ := −tr(XY), which is positive
definite on g, and B_μν(ξ) := ⟨conj b̂_μ(ξ), b̂_ν(ξ)⟩. The second-order term of B_tb in this mode has logarithmic part

  c ln(1/|ξ|²) · ½(|ξ|²δ_μν − ξ_μξ_ν) B_μν(ξ),  **c = (11/48π²) κ,**

up to the factor |Λ|^{−1} common to all modes. The same mode of the quadratic part of the Wilson action A is
½(|ξ̂|²δ − ξ̂ξ̂)B. Hence Σ_tot(ξ) ln(1/|ξ|) = c ln(1/|ξ|²)(|ξ|²δ − ξξ), and c > 0.

*Proof.* By Lemma 1.1, tr_g(ad X ad Y) = K(X, Y) = −κ⟨X, Y⟩ on g, extended bilinearly to g ⊗ ℂ. Since b is real,
b̂(−ξ) = conj b̂(ξ). Multiplication by b has plane-wave matrix elements |Λ|^{−1}b̂(k′ − k).
1. *Expansion.* If Δ = Δ⁰ + V¹ + V² + O(b³) and G = (Δ⁰)^{−1}, then
   log det Δ = log det Δ⁰ + Tr GV¹ + Tr GV² − ½Tr(GV¹GV¹) + O(b³).
   Tr GV² is a tadpole. So the logarithmic part of the second-order term of B_tb = −½ log det Δ₁ + log det Δ₀ is that of
   ¼Tr(GV₁¹GV₁¹) − ½Tr(GV₀¹GV₀¹).
2. *Continuum vertices.* At A = b + X, the part of ¼∫|F_μν|² quadratic in X, plus the Feynman term ½∫|D_μX_μ|², is
   ½⟨X, Δ₁X⟩ with Δ₁ = −D² − 2 ad F and (ad F X)_ν := [F_νμ, X_μ]. This follows by integration by parts from
   [D_μ, D_ν] = ad F_μν and ⟨F, [X_μ, X_ν]⟩ = ⟨[F, X_μ], X_ν⟩. The ghost operator is Δ₀ = −D². The parts linear in b
   have matrix elements, with ξ = k′ − k and b̂ = b̂(ξ):
   - convective, −i(k + k′)_μ ad b̂_μ/|Λ|, on each of the four components for Δ₁;
   - magnetic (Δ₁ only), W_νμ = −2i ad(ξ_νb̂_μ − ξ_μb̂_ν)/|Λ|.
3. *Traces.* Put k′ = k + ξ. Each trace below is κ|Λ|^{−1}Σ_ξ times a lattice bubble ∫N/(s(k)s(k+ξ)) d⁴k/(2π)⁴, whose
   N_2 is the continuum numerator listed.
   - Ghost: N_2 = (2k+ξ)_μ(2k+ξ)_ν B_μν. The sign: (−i)²K(b̂_μ(−ξ), b̂_ν(ξ)) = κB_μν.
   - Vector, convective: four times the ghost trace (four components).
   - Vector, mixed: zero, since the vector-index trace of W is Σ_ν W_νν = 0.
   - Vector, magnetic: N_2 = 4Σ_μν|ξ_μb̂_ν − ξ_νb̂_μ|² = 8(|ξ|²δ − ξξ)_μν B_μν.
4. *Angular averages.* By Lemma 6.1 each bubble has logarithmic part Σ(ξ) ln(1/|ξ|) = (1/16π²)⟨f_2(·, ξ)⟩ ln(1/|ξ|²),
   where ⟨·⟩ is the average over S³ and (2π)^{−4}|S³| = 1/8π². The moments are ⟨ω_μω_ν⟩ = δ_μν/4 and
   ⟨ω_μω_νω_ρω_σ⟩ = (δ_μνδ_ρσ + δ_μρδ_νσ + δ_μσδ_νρ)/24:
   - permutations and sign changes of the coordinates leave only ⟨ω_1²⟩, ⟨ω_1⁴⟩ and ⟨ω_1²ω_2²⟩;
   - Σ_μ ω_μ² = 1 gives ⟨ω_1²⟩ = 1/4, and Σ_μν ω_μ²ω_ν² = 1 gives 4⟨ω_1⁴⟩ + 12⟨ω_1²ω_2²⟩ = 1;
   - rotation by π/4 in the (1, 2)-plane gives ⟨ω_1⁴⟩ = 3⟨ω_1²ω_2²⟩.

   With u = ⟨ω, ξ⟩ and c₀ = |ξ|²:
   - convective: f_2 = ξ_μξ_ν − 4u(ω_μξ_ν + ξ_μω_ν) − 4c₀ω_μω_ν + 16u²ω_μω_ν, so
     ⟨f_2⟩ = ξξ − 2ξξ − c₀δ + ⅔(c₀δ + 2ξξ) = −⅓(|ξ|²δ − ξξ);
   - magnetic: N_2 is already quadratic in ξ, so f_2 = N_2/|ω|⁴ and ⟨f_2⟩ = 8(|ξ|²δ − ξξ)B.
5. *Sum.* In units of κ|Λ|^{−1}(1/16π²) ln(1/|ξ|²)(|ξ|²δ − ξξ)B, the logarithmic part is
   ¼[4·(−⅓) + 8] − ½·(−⅓) = 5/3 + 1/6 = 11/6. This is (11κ/96π²) ln(1/|ξ|²)(|ξ|²δ − ξξ)B, which is
   c ln(1/|ξ|²)·½(|ξ|²δ − ξξ)B. ∎

The type-checked Lean core `BalabanFormal.angular_coefficient` covers steps 4–5: the invariance of the S³ integral under
isometries, the moments, both averages and the constant 11/(48π²).

So the k-step rate 2c ln L per step is (11/24π²)κ ln L, the universal one-loop running.
- *Sign.* c > 0 is asymptotic freedom; it matches RG1 (0.20), because log Z ≈ +b·A.
- *Affine part.* Ψ_tb is transverse (Ψ_tb v = 0) and hypercubic-covariant. The argument of Lemma 4.1 applied to the
  affine part a_0 + a_1ξ (the logarithmic part is O(|ξ|² ln) and transverse up to O(|ξ|³ ln)) forces a_0 = 0 and
  a_1 = 0.

**Proposition 6.3 (Bare Polarisation).** Let −F_0 be the exact bare functional of §3 (built from h = Π_⊥ Hess A Π_⊥).
Its polarisation symbol is Ψ_0 = d̂*Ψ̃_0 d̂, with d̂ the lattice curl and Ψ̃_0 acting on ran d̂. Let c = (11/48π²)κ
(Lemma 6.5). Then

  Ψ̃_0(ξ) = c ln(1/|ξ|²)·1 + R_0(ξ),  sup_{ξ ∈ T⁴∖0} ‖R_0(ξ)‖ < ∞.

*Proof.*
1. *From −F_0 to B_tb.* −F_0 − B_tb = −½[log det(h + DDᵀ) − log det(Hess A + DDᵀ)]. The difference
   K := Hess A − h = Π_D Hess A + Hess A Π_D − Π_D Hess A Π_D, with Π_D := D(DᵀD)^{−1}Dᵀ, is linear in ∇A(U): by
   ⟨∇A, Dω⟩ ≡ 0, Hess A(X, Dω) = −⟨∇A, [X, ω]⟩.
2. *Size of the difference.* At second order in b the difference has three kinds of term:
   - ⟨∇A_1, θ_1(b)⟩, with ∇A_1 = dᵀdb = O(|ξ|²)b and θ_1 a one-loop integral with two massless propagators, one vertex
     of degree 1 and the degree-0 symbols of Π_D. Its integrand has degree −3, so θ_1 is bounded and continuous.
   - ⟨∇A_2, θ_0⟩ = 0, since θ_0 is Ad-invariant.
   - O(|∇A_1|²·∫1/(s(k)s(k+ξ))) = O(|ξ|⁴ ln(1/|ξ|)).

   So Ψ_0 − Ψ_tb = O(|ξ|²) with a bounded coefficient.
3. *Conclusion.* By §6.2, Ψ_tb(ξ) = c ln(1/|ξ|²)(|ξ|²δ − ξξ) + O(|ξ|²) near 0. Also d̂*d̂(ξ) = |ξ|²δ − ξξ + O(|ξ|⁴),
   and on coexact forms d̂*d̂ is bounded below by a positive multiple of |ξ|², since 4 sin²(ξ_μ/2) is at least 4ξ_μ²/π²
   for |ξ_μ| up to π. Away from 0, Ψ_0 is continuous and bounded. ∎

### 6.3 The Bare Functional Seen from the Top

**Proposition 6.4.** For fixed p_0 ≠ 0 (top units), Π_{−F_0}^{top}(p_0) = c ln(1/η_k²) Δ_k(p_0) + O_{p_0}(1), uniformly
in k, where η_k = L^{−k}. The type-checked Lean core of the summation is `BalabanFormal.bare_assembly`.

*Proof.*
1. *Composition.* The top polarisation is ⟨H_kB, Ψ_0 H_kB⟩ = Σ_l ⟨(dH_kB)^∧(q), Ψ̃_0(η_k q)(dH_kB)^∧(q)⟩, summed over
   the aliases q = p_0 + l (top units).
2. *Insert Proposition 6.3.* This gives c ln(1/η_k²)Σ_l|(dH_kB)^∧(q)|² + cΣ_l ln(1/|q|²)|(dH_kB)^∧(q)|² + R-terms.
3. *First term.* Σ_l |(dH_kB)^∧(q)|² = ‖dH_kB‖² = ⟨B, Δ_k B⟩ by PRT1 (1.65).
4. *Second term.* For l ≠ 0, |q| ≥ π. Hence |ln(1/|q|²)| ≤ ln(1/|p_0|²) + C_α|q|^{2α}, and the term is at most
   C(p_0)(Σ_l|q|^α|(dH_k)^∧(q)|)²|B̂|², which is O_{p_0}(1)|B̂|² by Lemma 5.2 (PRT1 p.29).
5. *R-terms.* They are at most sup‖R_0‖·‖dH_kB‖², which is bounded by PRT1 (1.67). ∎

## 7. The Top-Level Part Is Bounded at a Fixed Momentum

**Proposition 7.1.** For fixed p_0 ≠ 0, sup_k ‖Π_{F_k}(p_0)‖ < ∞.

*Proof.* By Lemma 3.3, F_k = ½ log det 𝒟_k − log det(D̄_VᵀD̄_V), with 𝒟_k(U) = Δ_k(U) + D̄_VD̄_Vᵀ and
⟨z, Δ_k(U)z⟩ = min{h_U(A) : Q_k(U)A = z}. (This minimum is already gauge-invariant: z ↦ z + D̄ω̄ corresponds to
A ↦ A + Dω, and hD = 0.)

*(a) Representation.* Let G_a(U) := (h_U + D_URD_Uᵀ + aQᵀQ)^{−1}, with Bałaban's gauge term R as in PRT1 (1.68)–(1.70).
Set H_k(U) := G_aQᵀ(QG_aQᵀ)^{−1}, the minimiser of h_U + (gauge term) on {QA = z}. Its minimum equals the minimum of h_U,
because the minimiser lies on the slice RD*A = 0 (PRT1 p.29). So Δ_k(U) = H_k(U)* h_U H_k(U).

*(b) Analyticity and decay, uniform in k.*
- PBG Thms 3.3–3.4 give analyticity in complex backgrounds U′U, under PBG (3.37), with exponential decay uniform in the
  sequence {Ω_j} and in k, for G(U) = (D_U*D_U + D_URD_U* + aQ*Q)^{−1}.
- The Wilson Hessian is h_U = D_U*D_U + K_U, where K_U is local, analytic, and O(r) for U = U_k(e^{iB}), B ∈ 𝔅_r (its
  curvature terms). The Neumann series G_a = (1 + GK_U)^{−1}G converges for r small and keeps the exponential decay.
- QG_aQᵀ lies between (C + a)^{−1} and a^{−1}, because its inverse is (min of h + gauge term on QA = z) + a. So its
  inverse is analytic and exponentially decaying (PBG (3.132)).
- H_k(U) is exponentially decaying (PBG Thm 3.12).
- Hence B ↦ 𝒟_k(U_k(e^{iB})) is analytic on 𝔅_r, with kernel bounded by Ce^{−δ|y−y′|}, and C, δ, r independent of k.

*(c) At U = 1.* 𝒟_k(1) acts by multiplication with c|p̂|²·1 ≤ 𝒟_k(1)(p) ≤ C|p̂|²·1. On transverse modes this is
PRT1 (1.67) for Δ_k; on longitudinal modes Δ_k(1) = 0 and D̄D̄ᵀ = |p̂|². Also D̄ᵀD̄(1) = |p̂|².

*(d) Second-order coefficient.* Expand 𝒟 = 𝒟_0 + 𝒟^{(1)}[B] + 𝒟^{(2)}[B, B] + …. The second-order coefficient of
log det 𝒟 is tr(𝒟_0^{−1}𝒟^{(2)}) − ½ tr(𝒟_0^{−1}𝒟^{(1)}𝒟_0^{−1}𝒟^{(1)}). By (b) and the Cauchy estimate, the vertex
symbols 𝒟^{(1)}(k, k+p_0) and 𝒟^{(2)} are bounded uniformly. With (c), which rests on PRT1 (1.67),
  ‖Π_{log det 𝒟_k}(p_0)‖ ≤ C ∫_{T⁴} (|k̂|^{−2} + |k̂|^{−2}|(k+p_0)^|^{−2}) d⁴k < ∞  (d = 4, p_0 ≠ 0).
The ghost term log det(D̄_VᵀD̄_V) is explicit and bounded in the same way. ∎

## 8. The Window Theorem

**Theorem 8.1.** There is a C such that for all k (from PRT1 (1.67) and Propositions 5.1, 5.3, 6.4 and 7.1)
  |Φ_k − (11/24π²) κ k ln L| ≤ C,
and therefore, for all 0 ≤ m ≤ n,
  **| Σ_{j=m+1}^{n} b_j − (11/24π²) κ (n−m) ln L | ≤ 2C.**

*Proof.*
1. *Identity.* By Corollary 3.2 and Remark 3.4, ℒ_k = F_k − F_0 + 𝒥_k as functionals of B. So at p_0 ≠ 0:
   Π_{ℒ_k}(p_0) = Π_{F_k}(p_0) + Π_{−F_0}^{top}(p_0) + Π_{𝒥_k}(p_0).
2. *Insert the estimates.* Take p_0 = (π/2, 0, 0, 0) and a unit vector e ⊥ v(p_0). Propositions 5.1, 7.1, 6.4 and 5.3
   give Φ_k⟨e, Δ_k(p_0)e⟩ = c ln(1/η_k²)⟨e, Δ_k(p_0)e⟩ + O(1).
3. *Divide.* By PRT1 (1.67), ⟨e, Δ_k(p_0)e⟩ ∈ [γ_0|p̂_0|², γ_1|p̂_0|²], with γ_0 > 0 independent of k. Since
   ln(1/η_k²) = 2k ln L and 2c = (11/24π²)κ, the claim follows. ∎

**Corollary 8.2 (RG1 Theorem 2 for Simple G).** Take ε₁ as in Proposition 2.4. Theorem 8.1 is hypothesis (W) of §2 at
zero coupling, and Propositions 2.4 and 2.6 give (P2) with δ = c ln L and (C). By Remark 2.3, Lemma 2.1 gives, for
every small renormalised coupling g and every ε = L^{−K}:
- a bare g_0(ε, g), independent of the torus;
- g_K = g, and all g_k in ]0, γ];
- RG1 (0.31) with β = 2c − δ/ln L ≥ c and β′ = 2c + δ/ln L, up to an additive constant;
- the near-monotonicity that LFR2 (1.86) uses (Remark 2.2).

With CRE's cutoff δ_k, Proposition 2.9 also gives (P2) with δ = C_remγ² (RG1 (0.31), CRE p.265).

## 9. Inputs

**Inputs taken from Bałaban without re-proof, with their caveats.**
- PRT1 (1.63), (1.65)–(1.67) and the alias-summability statement on PRT1 p.29; PBG Thms 3.3, 3.4, 3.12, 3.15 and
  PBG (3.132); RG1 (0.28)–(0.30), RG1 (1.8)–(1.9), RG1 p.263 (analyticity domains); VAR Thm 1 and §G.
- PRT1 and PBG were written for the averaging of AVG (CMP 98); RG1 uses the Euclidean-symmetric average RG1 (0.4). At
  U = 1 the first-order part of RG1 (0.4) is PRT1's straight average up to a gradient and a fine translation
  (Proposition 5.3, steps 1 and 4), so Lemma 5.2 and PRT1 (1.65)–(1.67) apply to the chain at U = 1. The sentence on
  RG1 p.253 that the earlier results hold for any average with the listed properties concerns group averages M
  (READINGS.md R47, scope) and is not used. PBG's results away from U = 1 (§7) are not covered by this argument; their
  use for RG1 (0.4) is an input taken as Bałaban states it.
- VAR Thm 1 inherits the sketched Theorem 8 of CMP 99 389–434
  (`D:\University\Oxford PostDoc\Balaban\BALABAN_DEPENDENCE_TREE.md`, D3). It enters §§5 and 7
  through the analyticity of U_k(V).
- VAR (189), stated without proof, enters Lemma 2.5 through VAR (190) (sidecar node VAR_189).
- From RG1 Theorem 3 with RG2 Lemmas 1–3 and RG2 (2.41): the bound RG1 (1.18) and the analyticity of the step terms in
  (U, J) on RG1's fixed domains, for §§2.1–2.2, as printed for RG1's cutoff.
- For the tube construction: CRE's inductive estimates as printed, in particular CRE (2.30)–(2.31), p.260, (2.44) and
  (2.46), p.263, and the statement that the step output satisfies the inductive assumption (CRE p.279), and the
  estimates of LFR1 and LFR2, including LFR2 (1.79)–(1.80), pp.383–384, and of UV3, CMP98, REG, and VAR as CRE uses
  them.
- RG2's sketch on p.11 for the terms of P^{(k)} other than V, for Lemma 2.7 and so for Proposition 2.9.

**Arguments of This File That Extend Bałaban's Statements.** These are not printed by Bałaban; their proofs are in §§0
and 2, and, for Theorem 8.1 and Corollary 8.2, in §§3–8.
- The identification of CRE's step terms with those of RG1's construction run with δ_j, up to the R′-terms (CRE
  pp.267, 271, 272, 274, 278–283; §0, *CRE's Step Terms and β_j*). It identifies the regular part of the tube
  construction's β^T with RG1's construction run with the tube cutoffs δ_j^T, whose bounds come from Propositions 2.4
  and 2.9 (Lemma 2.10, step 7).
- The window theorem for the zero-coupling coefficients (Theorem 8.1, from §§3–7), the flow lemma (Lemma 2.1),
  Remark 2.3, and the matching for simple G (Corollary 8.2). RG1 Theorem 2 (RG1 p.259) is stated for SU(2), and its
  proof is deferred to "a separate paper"; Corollary 8.2 proves it for simple G.
- The parameter choices p₀ > (d+5)r + ⌈r⌉ + 2 (Lemma 2.10, step 4) and q₀, q₁ > p₀ (Proposition 2.11, step 4), which CRE's
  printed conditions ("p₀ ≥ 5r", CRE p.246; q₀, q₁ "integers greater than 1", CRE p.259) allow.
- The transfer of RG1 Theorem 3 from RG1's cutoff to CRE's cutoff δ_j = g_j(A₁/A₀)p₀(g_j) (CRE p.265) and to δ_j^T
  (§0, *Condition 3*; the remark after Proposition 2.6; Lemma 2.10, step 7).
- The bound (P2) and the continuity (C) of β (Propositions 2.4 and 2.6), with the polarisation bound of Lemma 2.5.
- The transfer to complex coupling (Lemma 2.7), the parity, the threshold differences (Lemma 2.8), and the
  telescoping (Proposition 2.9).
- CRE's inductive step run with complex multiples of the R′-part, with that part controlled through CRE's own bound
  (2.31) by a constant K_R, and the regular inputs bounded with 2E₀; CRE states the step at s = 1 only
  (Proposition 2.11, steps 3–4, and *The Step with Complex Multiples of the R-Terms*).
- Lemma 2.5 on the (2.28) domains with the tube radii, with Cauchy radius r ≥ c·min(α^T_{0,k+1}, α^T_{1,k+1})
  (Proposition 2.11, step 5).
- The tube construction, its convention for histories that are not flows, and its admissibility (Lemma 2.10). Step 6
  of its proof rests on a reading of every line of CRE, LFR1, LFR2, and UV3 that contains one of the parameters,
  sorted into four kinds and two further uses.
- The continuity of the tube construction in the history (Proposition 2.12) and the matching (Proposition 2.13).

**Lean cores.** The type-checked Lean cores named above (`BalabanFormal.flow_lemma`,
`BalabanFormal.coupling_flow_of_stepBound`, `BalabanFormal.jterm_quartic`, `BalabanFormal.jterm_assembly`,
`BalabanFormal.bare_assembly`, `SmoothNum.lemma61` and `BalabanFormal.angular_coefficient`) are abstract statements
whose hypotheses are listed in `D:\University\Oxford PostDoc\Balaban\sidecar\BalabanSidecar\Instantiation.lean`. They check the finite algebra and analysis of
the steps that cite them. Each of those steps also has its proof written out here.

The Lean modules of these cores are in the standalone project
`C:\Users\marti\Documents\Scientia\Mathematics\Lean\Projects\ym_beta_function` (28 modules of namespace `BalabanFormal`,
importing only each other and Mathlib; `lake build` there, and `#print axioms` of each name above gives propext,
Classical.choice and Quot.sound only). They are verbatim copies of the modules of the same names in
`C:\Users\marti\Documents\Scientia\Mathematics\Lean\Projects\balaban`, which the Bałaban sidecar's gates check.

## 10. Semisimple G: Open Future Direction

Let G ⊂ U(N) be compact semisimple, with Lie algebra g = g_1 ⊕ ⋯ ⊕ g_r (simple ideals).

**Lemma 10.1.** Every Ad(G)-invariant symmetric bilinear form on g has the form Σ_i c_i K_i, where K_i is the Killing form
of g_i. In particular the trace form is Σ_i κ_i^{−1} K_i, with κ_i > 0 defined by K_i = κ_i·tr on g_i.

*Proof.* Let β be invariant and i ≠ j. For fixed Y ∈ g_j, the functional X ↦ β(X, Y) on g_i is invariant under Ad(G_i)
(G_i acts trivially on g_j), hence zero, since a simple g_i has no nonzero invariant vectors. On each g_i, Lemma 1.1
gives β|_{g_i} = c_i K_i. ∎

**What carries over.**
- The vacuum polarisation of RG1 (1.20) is block-diagonal: on g_i ⊗ g_i it is a multiple of the trace form, and the
  blocks g_i ⊗ g_j (i ≠ j) vanish. The statement "proportional to δ^{ab}" of RG1 p.264 holds only for r = 1.
- The marginal terms are Σ_i c_i A_i(U), with A_i a Wilson action of factor i, and there is no invariant marginal cross
  term. So there is one coupling and one β per simple factor, and the flow RG1 (0.20) becomes
  1/g_{k,i}² = 1/g_{k+1,i}² + β_{k+1,i}(g_0, …, g_k), i = 1, …, r, where g_j = (g_{j,1}, …, g_{j,r}) and the β's depend
  on the whole vector history. The bare action gives g_{0,i}^{−2} = λ_i′/g², with weights λ_i′ fixed by the embedding.
- §§3–8 hold per factor, with c_i = (11/48π²)κ_i, because every polarisation is block-diagonal.
- The flow lemma holds for the coupling vector (RG1 (0.31) per factor; `BalabanFormal.flow_lemma`). Clamp each component
  as in Lemma 2.1, and take the box Π_i [t_i + b_iK − C, t_i + b_i′K + C]. (W) gives F_i ≤ t_i on the face
  x_{0,i} = t_i + b_iK − C and F_i ≥ t_i on the face x_{0,i} = t_i + b_i′K + C, whatever the other components are. The
  Poincaré–Miranda theorem then gives a solution in the box, and step 4 of Lemma 2.1 applies componentwise.

**What is OPEN.** Bałaban's thresholds use a single coupling g_k: ε_k = g_kp₀(g_k) in CRE (2.4), δ_k on CRE p.265, and p₀(g_k) in
LFR2 (1.86). For several factors they are to be read with g_k := max_i g_{k,i}. RG1, RG2, CRE and LFR1–LFR2 have not
been re-verified with this substitution. The changes are notational, but they run through all the papers. Until that
check is done, Theorem 0.1 is stated for simple G only.

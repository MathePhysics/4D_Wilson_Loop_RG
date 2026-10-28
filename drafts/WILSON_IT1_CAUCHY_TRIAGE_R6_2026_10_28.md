# Triage of the Cauchy Reviews, Round 6 (28 Oct 2026)

Four packets were launched about 00:31 on the Cauchy note a66428c8de7f: cauchy-pi-20261028-r2, cauchy-align-20261028-r2, cauchy-act-20261028-r1, and cauchy-lift-20261028-r1. The dispositions below are entered as the reviews land.

## Dispositions, Review cauchy-pi-20261028-r2 (§10.4, the π-Part, Polarisation, and Interpolation)

Verdict: β_π ≡ 0, the J-term, (A1), r_β, the kernel bound, and (A2) are correct. Nothing is fatal. Accepted:

- (S1, serious) Line 478 identifies E with 𝔊_Aℒ*β(·, 𝒜^B), 𝔊 the operator of PBG (3.153). That operator rests on the Faddeev–Popov identities (3.151)–(3.152), which need the N(Q′)-invariance that fails at the pair, and R_AD_A*E = 0 is not shown. The characterisation on line 478 itself, ⟨Q₁ℱ, G_A^{−1}E⟩ = β(ℱ, 𝒜^B) for ℱ ∈ ker Q^B_j with E ∈ ker Q^A_{j−1}, needs no Landau input and identifies E with the Green operator on ker Q^A_{j−1}, G₁^Q := G₁ − G₁Q*(QG₁Q*)^{−1}QG₁ = (I − H₁Q)G₁ at run A's pair. Repair (the integrator's): line 478 and the LF note's §4(d) *The terms in E.* (l.241) use G₁^Q, whose bounds follow from (3.132) for G₁ and (3.133) for H₁ at the pair (§10.3), with Q local.
- Minor, accepted: (M1) the two operators written Q′ in the π-paragraph are renamed apart; (M2) "writing 𝐉 for J in (3.128)" names line 1 of (3.128), Δ_π := Δ − Δ′_π[𝐉]; (M3) "not invariant" reads "invariant only if ⟨δJ, c_A(λ, Y)⟩ vanishes identically, which is not given"; (M4) B₀(2γ_H) + B₀ in place of B₀(2γ_H).

## Dispositions, Review cauchy-align-20261028-r2 (§10.3, the Pair Class and the Multipliers)

Verdict: every identity and constant of *The Pair Class.* and *The Multipliers.* checks. Nothing is fatal or serious inside the paragraphs. Accepted:

- (Observation, load-bearing for (f) and (h)) VAR p.281 l.2–4 reaches the Landau representative by a gauge transformation u with the averaged transformation trivial, not u| = 1, so M^j(e^{iεA′*}Ũ) = V^w with w := u^{−1}| in general. Repair (the integrator's): the multiplier at that representative is Ad(w)λ^A, and w = 1 + O(ρ_j), since u carries U^A from the axial gauge of Ũ's data to the Landau gauge relative to Ũ at distance ≤ ρ_j. So |Ad(w) − 1||λ^A| ≤ Cρ_j(B_λ + x_λ)ε₁a_j^{−3} is absorbed into x_λ with a changed constant, and the same holds for δ𝐉 in the caller. The size of u is checked against VAR p.281 before the edit.
- Minor, accepted: (1) "RG I takes the same pairs" reads "RG I p.261–262 treats 𝐉 as a variable independent of 𝐔 on an analogous class U^c_j, with |𝐉| < γ₀ in (1.14); 𝒟_j is not the same class"; (2) the complex extension of (3.132)–(3.133) for G₁ and H₁ cites Theorem 3.4, pp.403–407, uniform convergence, and RG I p.261; (3) Theorem 3.11 only at real pairs; (4) the omission of (3.36) is stated; (5) the plain-lift smallness conditions C_ax·d(R_Q + 3)C₀ε₁ ≤ m_Q^{pl}/4 and δ₁ ≤ δ_Q^{pl} are listed, and C_ℒ's dependence on B₀(γ)/B₀ and δ₁ is stated; (6) the bond sum for r₀ is bounded by the plaquette sum in d = 4; (7) a reads a_j in c_e; (8) 𝒟_j states the scale a_j and PBG's α₀ for (3.35); (9) the BCH line for the (3/2) margin.

## Dispositions, Review cauchy-lift-20261028-r1 (§9.4–§9.5 and §10.4 *Regularity of the Lifts.*)

Verdict: the nodes, the tents, m_Q = 1/3, the localisation, the Neumann decay, C_I, and C_ℒ′ at every exponent γ < 1 are verified. Nothing is fatal. Accepted:

- (S1, serious) §9.4's bound on (Q₁^{pl}Q₁^{pl}*)^{−1} at U = 1 by a constant of L and d is argued only by surjectivity, which gives positivity in each finite volume and no volume-uniform constant. It feeds C_𝒦, C_ℒ, the decay of the inverse, (9.8), and §10.3's artifact term. Repair: a right inverse bounded uniformly in the volume. X₀ := Q^{str}*T(1)^{−1}ν has Q^{str}X₀ = ν, with ‖T(1)^{−1}‖ ≤ 3 from §10.4's tents. X := X₀ + Dω̃, with ω̃ the block-constant extension of Θ₁X₀, has Q₁^{pl}X = ν by (B1)–(B2), and ‖X‖ ≤ C(L, d)‖ν‖. Then ‖ν‖² = ⟨X, Q₁^{pl}*ν⟩ ≤ C(L, d)‖ν‖‖Q₁^{pl}*ν‖, so Q₁^{pl}Q₁^{pl}* ≥ C(L, d)^{−2} in every volume. The exponential decay of the inverse follows from this lower bound, the upper bound, and the finite range of Q₁^{pl}Q₁^{pl}*, by the Neumann series of (Q₁^{pl}Q₁^{pl}*)^{−1} = c(I − (I − cQ₁^{pl}Q₁^{pl}*))^{−1} with c the inverse upper bound, whose terms have growing finite range.
- Minor, accepted: (1) the condition c₁₂₄C₀ε₁ ≤ ½ is added to the list after (10.6), since CMP 98 p.036 prints only O(L²α₀); (2) the Hölder distance is fixed as the ℓ^∞ distance, or the factor 2 of C_ℒ′ reads 4; (3) the count 2dν_F𝔰′ omits the transport mismatch, and 2C_trν_F𝔰′ is used; (4) the curl and divergence oscillations carry the factors 2 and d; (5) the third term of (124) joins the column sums; (6) I_{pl} is defined as the multilinear interpolation of coarse plaquette fields to fine plaquettes, and D(Ig) = I_{pl}D̄g + O(ε|∇∇g| + (ε₁/a)|g|); (7) "supported on the averaging paths" and "translation-invariant local" read "exponentially localised"; (8) (1 + C_𝒦) multiplies B₀′(ε₀) as well; (9) "∓" in the quotation of (124) is removed; (10) the gauge covariance of T = Q̄₁Q̄₁* is derived from CMP 98 (11).

## Dispositions, Review cauchy-act-20261028-r1 (§10.4, the Action Part and (10.6a))

Verdict: (10.6a) holds in form and rates, uniformly in j, k, K, ε, and the volume. Nothing is fatal or serious. Accepted, all constants:

- (1) the curl and divergence oscillations are 2ω and dω, and osc_p(Tf) carries them; (2) the second variation of T gains the i ad a″ term, |a″| ≤ ½c_br(4dε)²|𝒜′||𝒜|, and |a| the dlog factor, with c_br² in |d²F^w_p|, X_tr, k_Φ″, and k_ν raised; (3) the 4-cell oscillation is in the ℓ^∞ distance; (4) at j = 1 the localised (3.133) is chained over the oscillation box, which changes only B₀(γ_H); (5) the face count is 32d³, the garbled clause is rewritten, and C_tr is derived; (6) "∓" is removed and c₁₂₄ depends on G; (7) the t-radius r_G/(2η|Z|) is stated; (8) dF_{p′}(1)[Z_c] = 0 is stated for the cross terms; (9) "the same holds for Q₁𝒜 on T_ε" is removed, since (10.6a) does not use it.

## Assignment of the Repairs

- Agent C (Cauchy note §9.4, §9.5, §10.3, and §10.4 only): pi S1 at l.478, the align observation, lift S1, and every minor of the four reviews.
- The integrator: the LF note's §4(d) *The terms in E.* (l.241 at 86547ec89d91) with G₁^Q, inside the interface-multiplier repair.

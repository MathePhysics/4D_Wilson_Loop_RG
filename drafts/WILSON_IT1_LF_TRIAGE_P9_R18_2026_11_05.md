# Triage of LF Packet 9, Eighteenth Review (lf-p9-20261105-r18)

The review is verification\isolated_reviewer\reviews\lf-p9-20261105-r18\review.md. It finds no fatal and no serious issue, three minor issues, and five trivial ones. This is packet 9's first clean pass.

The review confirms the seventeenth review's repairs:
- the gauge-orbit identity 𝒬̃(D_Uλ, t) = 0;
- the absorption in a_L alone, giving e_a ≤ C(L, M′)ε₁θ_{B₁} and e_a = 0 at U = 1;
- N(a) ≤ C(L)θ_{B′_U} through VAR (190), Bałaban's, accepted;
- the ν_a bound through the printed (3.42)–(3.44);
- the non-circular one-sided bound;
- the conversion per level with the factor 1 + C(L)α₀.

The repairs below change #A.11.1.4.3.4, #A.11.1.4.3.4.1, #A.11.1.4.3.4.2, #A.11.1.4.3's first sentence, the right inverse and t′ in #A.11.1.4.4.4.1, #A.11.1.4.4.4.2.2.1, #A.11.1.4.4.4.2.3's first clause, #A.11.1.5.3.1, #A.11.1.6, and #A.11.1.6.1. They go to r19.

The LF is now 2b482b58579b, with labels 828ff3bc285b (102 multiply defined, CR 0). The table is dc709ff60261, after the fork's bookkeeping hash update in {#T4.32} (two-loops 28374a2bc8dc).

| Finding | Verdict | Disposition |
|---|---|---|
| M1: the crossing shift was restricted to b₋ ∈ Λ₀, but REG p.81 l.36–44 puts the crossing factor at every interface | Accepted | #A.11.1.4.3.4 defines {#D.S_b} S_bU′_ax, the first-order part of the crossing factor on every bond from Λ_{j−1} to Λ_j. At j = 1 it is #0.1.4's KU′_ax(b₋). ξ_ω(b₋) does not contain it. B′_U = B + S_bU′_ax + E(U)U′_ax on the crossing bonds. #A.11.1.4.3.4.1 bounds S_b through the data of the layer j − 1 on bonds that do not cross, ≤ C(d)L(θ_B + C(L)α₀θ_{B′_U}), so the one-sided bound keeps its form. #A.11.1.4.3 and #A.11.1.4.3.4.2 name the shift at every interface. |
| M2: the right inverse of Q̃(U) misses the crossing term | Accepted | λ_X vanishes on Λ₀, and Q̃(U)(H₁X + D_Uλ_X) = (I + S + E′)X = (I + S)(I + E″)X, with S² = 0 and E″ := (I − S)E′. H̃ := (H₁ + D_Uλ_·)(I + E″)^{−1}(I − S). H̃^*J carries (I − S)^*, with abs(S^*) ≤ C(d)L, so its bound is unchanged. t′ is unaffected, since Q(U)t = 0 on the bonds S reads. |
| M3: the gauge commutator in #A.11.1.4.3.4.1 | Accepted | The plaquette variables of U′_ax are those of u_R, ≤ C(L)N(a), plus the commutator of ζ^R with the base's plaquettes, ≤ C(L)B₃ε₁abs(ηζ^R). abs(ηζ^R) ≤ C(L)(N(a) + sup abs(U′_ax)) by #A.9's scalar problem. This is absorbed for C(L)B₃ε₁ ≤ ½, which #A.11.1.6.1 lists. |
| Trivial: #A.11.1.5.3 does not list the conversion term; (δ₀/8)RM is absent from #A.11.1.6; δB versus B′_U; "every λ" | Accepted | #A.11.1.5.3.1 lists C_HC(L)α₀. #A.11.1.6 lists (δ₀/8)RM ≥ 8 log L. #A.11.1.4.4.4.2.2.1 states B′_U = φ(ad i Re B)δB with θ_{δB} ≤ 2θ_{B′_U} for C(d)C₁ε₁ ≤ ½, which #A.11.1.6.1 lists. #A.11.1.4.4.4.2.3 reads "every real λ vanishing on Ω₁^c, as ν_a does". |
| (190) rests on (189), stated without computation (disclosure) | Noted | (190) is Bałaban's stated result, accepted as his printed claim (VAR p.308 l.30–47, p.307 l.17–18). |
| t1–t4 | Noted | Deferred until after the second clean pass. |

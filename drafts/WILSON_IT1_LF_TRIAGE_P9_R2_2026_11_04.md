# Triage of LF Packet 9, Second Review (lf-p9-20261104-r2)

The review is verification\isolated_reviewer\reviews\lf-p9-20261104-r2\review.md. It finds no fatal issue, one serious issue, and seven minor ones, and it resolves every finding of r1. Each finding is accepted. The repairs are in the LF, now 208471f1b3e3 (labels 644ae0320a5a, 102 multiply defined), and in the table, now 6c8c973e67d1.

| Finding | Verdict | Repair |
|---|---|---|
| S1: the width hypothesis of #A.11.1.2 fails at the joins (LM₁) and at the top layers of 𝐁″_k (M), since M_□ was chosen after the large-field M | Accepted. The M of #A.9–#A.11.1 is PBG's block size, which the chain runs at M′ (#4.26–#4.27; table #T2.10). | #A.11.1.1 states the reading M = R₁M₁ = M′. #A.11.1.3 gives K = C(L)e^{¼δ₀C(d)M′}. #A.11.1.2 takes RM to be the chain's least width R′M′ ≥ ½LM₁. #A.11.1.6 orders the constants as L, then M₁/M′ ≥ C(L), then M′, then M_□ ≥ C(L)(M′ + 1), then the large-field M, then ε₁. New #4.22.3 adds K ≥ C(L) for CRE's K, and table #T2.10, #T2.12, and #T2.15 record this. |
| m1: C_H against C_H + δ_U in #0.1.12.1, #0.1.13, and #0.1.40 | Accepted | Each clause now carries C_H + δ_U. In #0.1.40, C(d) is doubled to cover C_H + δ_U ≤ 2C_H. |
| m2: #A.11.1.4 (P2) needs δ ≤ c(d)δ₀ | Accepted | δ := c(d)min(1, δ₀), and δRM ≥ (d + 2)log L by #A.11.1.6 |
| m3: the identification of A_N(U) with #A.9's A_N at a non-flat base (UNCLEAR) | Accepted. The identification does not hold exactly: the gauge with Q′ω ≠ 0 does not preserve PBG's form at curvature ≠ 0. | New #A.11.1.4.1–#A.11.1.4.2. By VAR Proposition 2, (44), (47)–(49), (79), and (99)–(102) (table #T11.25), a = H₁(U)Q(U)a, so #A.9's A_N = A_N(U)B + 𝒫_Uξ_ω. 𝒫_U is a covariant member with 𝒫_1 = 0, and #A.11.1.2 with K_♭ = 0 bounds it by C(L)δθ_B, inside δ_U. |
| m4: real regular in PBG's form with an explicit α₀ | Accepted | #A.11.1.1 requires M′α₀ ≤ a₀ on PBG's class cubes, and #A.11.1.2 gives U_□ α₀ = α_□/M′. |
| m5: "unions of G^c-orbits" in #0.1.10 | Accepted | The clause now applies only to RG I's spaces. The boundary terms' spaces are G-invariant (CRE p.261 l.42–43), and those terms are handled as covariant members (#0.1.13). |
| m6: #0.1.42's T_□ clause omits the order of #A.11.1.6 | Accepted | Added |
| m7: the margin in #A.11.1.5's m_y step | Accepted | supp ψ_α ⊂ □_{α,1/5}, and a block meeting it lies in □_{α,1/4} for M_□ ≥ 40L. |

Cross-packet effect: #4.22.3 is a new block of packet 11 (open). The statements of #0.1.9–#0.1.13 keep the same factor per level, so packets 1–8 are not re-opened. #A.9.6 (packets 1 and 6–8) now reads the extra term of #A.11.1.4.2, which δ_U covers.

# Triage of LF Packet 9, Eighth Review (lf-p9-20261104-r8)

The review is verification\isolated_reviewer\reviews\lf-p9-20261104-r8\review.md. Its verdict is that the claim is established as stated, with one minor UNCLEAR point and seven trivial items. It finds no fatal or serious issue. Since the minor point is a finding, r8 is not clean, and the count of clean passes restarts. Each item is accepted. The repairs are in the LF, now 076a09424918 (labels 6fb341d306c7, CR 0, 102 multiply defined), and in the table, now 185590aaefb5. The next round, r9, reviews the repaired blocks and their callers only; the other blocks of packet 9 were clean in r7 and r8.

| Finding | Verdict | Repair |
|---|---|---|
| Minor: B₁ = B inside the layers together with B₁ − B = D̄ξ_ω needs a stated justification | Accepted | New block #A.11.1.4.4: REG (1.19) (p.79) fixes, at every level and every site of each block, the averaged contour variables that RG I's averages (0.12) are built from (RG I p.253 l.12–13, p.254 l.7 and l.26), so at first order ξ_ω = KU′_ax = 0 at every block point of the layers ≥ 1, and ξ_ω = 0 on Λ₀. Hence D̄ξ_ω = 0, 𝒫_Uξ_ω = 0, and B₁ = B on every data bond; the crossing contour mean is the datum shift of #0.1.4, contained in both. #A.11.1.4.3 now derives θ_{B₁} = θ_B from it, with no bound running through B₁; #A.11.1.4 and #A.11.1.5 note the vanishing. |
| t(a): #A.11.1.1, p.305 l.44 is an assumption | Accepted | "VAR assumes C₁ to be an absolute constant (p.305 l.44)", also in #0.1.10. |
| t(b): #A.11.1.1, Theorem 3.12's α₀ threshold | Accepted | Added to #A.11.1.1 (p.423 l.34) and to the ε₁-list of #A.11.1.6. |
| t: #A.11.1.4.2, the second term is identically 0 | Accepted | The step says so: Q′(U)λ^U_ξ = ξ for every U, so Q(U)D_Uλ^U_ξ = D̄ξ by PBG (3.115). |
| t: #A.11.1.4.2, ξ on the layers ≥ 1 | Accepted | Stated, with the reason (ξ_ω vanishes on Λ₀). |
| t: #A.11.1.4.3, the base's plaquette commutators | Accepted, the review's wording | The terms ≤ C(L, M′)B₃ε₁θ_B are stated (VAR p.304 l.52), and the factor is (1 + C(L) + C(L, M′)ε₁)δ, in #A.11.1.5 too. |
| t: #A.11.1.5, Σψ_α < 1 | Accepted | One sentence: there y lies in Λ₀ away from Ω₁, the ω_α vanish, and the identity is not needed. |
| t: #A.11.1.6, the conditions on K | Accepted | δ₁RM ≥ 8 log L and PRT2's (2.59) at the rates of #A.11.1.3 and #A.11.1.4.2 are listed, both for M₁/M′ ≥ C(L). |

Further repairs found in the self-check before r9: #0.1.14's clause on the G^c transformations cites the two-loops note's section *The G^c transformations* by title (it was a bare "#6", which the relabel check rejects), and the table's #T4.30 states T₂^{old} on Λ∖Ω″^{∼2}_{h+1} as derived and reviewed (the two-loops note's (R-eval-old), packets PV, PL, and CT), in place of the stale "open".

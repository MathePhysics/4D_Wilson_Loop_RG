# Packet 13a r2 Result and r3 Repairs (7 Nov 2026)

lf-p13a-20261106-r2 reported no fatal and no serious findings, two minor ones (m1, m2), and four trivial ones (m3–m6). All are repaired in place, and the subject check below replaced every reading in 13a by a derivation, at LF 3befa8a18385 (labels 27e76972eb6f), table c94afde7eca1 (unchanged). r3 is a full round of 13a, #4.43–#4.55-1, with r2's review as its prior. 13b's r2 result (S1, m1–m6) is handled after 13a is done.

## Open

None.

## Repairs (in place)

| Item | Line | Repair |
|---|---|---|
| m1 | #4.43-1, #4.51-1, #4.55-0.1 | R_k and ε_k are each the larger of the two runs' values, stated at ε₁'s definition for every bound of (c) by them, so ε₁ bounds both runs' C(M)R_kε_k; removed from #4.51-1. #4.55-0.1 writes ε_k = g_kp₀(g_k) (#3.29) with g_k the coupling of the run attaining the larger ε_k, g_j that run's, R_k the larger value, and a factor 2 for the other run's g_j^{−2}, since the runs' g_j^{−2} differ by a factor ≤ 2 (the Cauchy note's #C5.7-3–#C5.7-8). |
| m2 | #4.45, new #4.45-1, new #4.48-3, #4.48-3.0.1, #4.48-3.0.2, #4.48-3.1, #4.48-4, #4.50-1.1 | The action is linear in its weight, so the ζ₀ ≡ 1 form is the ζ₀ form plus the 1 − ζ₀ form. (1.7)–(1.8) (p.358 l.3–13) bound the first by (2κ_Λ − O(1)(M⁶R_kε_k + e^{−R_k}))‖Y‖₂². The second is bounded on P. The support of 1 − ζ₀ is at the sup-distance ≥ 6MR_k from Λ, derived in the subject check below, and PRT2's d(y, Λ) ≥ 4MR_k there ((2.46), p.231 l.11). Its function changes by ≤ 2C(1 + 2C_ℋ)C_ℋC₁²ε₁²e^{−(δ₀/8)MR_k}N_Λc_tot(1/128), and Cauchy's estimate gives its form ≤ C_{1−ζ₀}(M)e^{−(δ₀/8)MR_k}‖Y‖₂². (T-Λ)'s first threshold adds this term. |
| m3 | #4.50-1.1 | 2ε₁ ≤ a₁ in VAR Theorem 1, with PBG Theorem 3.12 also at 2ε₁, for the segment of *The comparison.* Split at a sentence into new #4.50-1.1.1 for length. |
| m4 | #4.51-1 | σ̄ holds at V′^A₀ and V′^B₀ (regular with ε₁); the segment, regular with 2ε₁, is used only for the derivative bound of #4.51-2. |
| m5 | #4.54, new #4.54-0.1 | |w| is read at the point: |w(x)| ≤ g_{j(x)}^{−2} ≤ (1 + β₀)²(|j(x) − j| + 1)g_j^{−2} by CRE (2.6) (p.255 l.44–46, both inequalities), and d ≥ RM(|j(x) − j| − 1) (#4.31), so half the decay absorbs the factor. |
| m6 | #4.55 | C_A(M) := Cc_K(C′_Δ(M) + C′_Δ(M)²) + C(M)C_Δ(M). The rest of #4.55 moves to new #4.55-0.1. |

## Subject check (in place)

For each Bałaban input of 13a: do the cited lines name the object the note applies them to? Where they did not, the step is now derived from printed definitions.

| Line | Was | Now |
|---|---|---|
| #4.43-1, new #4.43-1.1, #4.43-1.2 | The data's regularity was taken from p.357 l.46–48, which bounds U_0 only. | The data of U_0 are LFR I's V_Λ. Off Λ they are V_k, with the bound 2L(L + 1)R_kε_k from χ_k and χ″_k on Ω″_k ⊃ Z ∩ Λ^c (LFR I p.193 l.21–23, (1.12), (1.73)). On Λ, (1.78) gives B₅M⁵ times that, on the plaquettes meeting Λ (RG I p.251 l.26–28). C(M) ≥ 2L(L + 1)max(1, B₅M⁵) is added. |
| #4.45 | RG I (2.8) was cited for the Λ-problem via p.356 l.31–33, which concerns the ζ₀-action. | Bałaban applies (2.8) to Φ itself "with ζ₀ = 1" (LFR II p.359 l.5–8). |
| #4.48-3, new #4.48-3.0, #4.48-3.0.0, #4.48-3.0.1 | The support of 1 − ζ₀ was located from (1.6)'s bound and from p.363's statement on the support of B. | Derived from definitions. ζ₀ ∈ C₀^∞(Z) changes from 0 to 1 near ∂Z^{∼−2} (LFR I p.201 l.28–29); the note takes ζ₀ = 1 on Z^{∼−2}, which meets that definition, so the support of 1 − ζ₀ is within the sup-distance 2MR_k of Z^c. Λ ⊂ Ω^c_{k₀+1} ⊂ Z_{k₀+1} ⊂ Z_{k−1} (LFR I (1.73), CRE (2.1), (2.3); N₀ ≥ 2 as R_k ≥ 2, #CP.13). CRE (3.5) and p.265 l.19 give Ω_k ⊂ (Z′^{∼8}_{k−1})^c, so Z ⊃ Λ's sup-neighbourhood of radius 8MR_k. Hence the sup-distance is ≥ 6MR_k, and contour lengths bound it. |
| #4.48.1 | "𝐁_k(Z) consists of the layers of CRE's domains in Z" had no citation. | CRE's determining set (2.2) (p.255 l.12–18), restricted to Z (LFR I (1.74)). |
| #4.52 | "B shared by the runs" read like a statement of Bałaban's. | B is the integration variable; the note compares the two runs' integrands at its equal values (a definition of the comparison). |
| #4.54, new #4.54-0 | The data derivative of U″_k was named by (1.54), which concerns U_k^0's data 𝐀₀ only. | U″_k = U_{𝐁″_k}(D″) by (1.50); VAR (172)–(174) for 𝐁″_k give ℋ = 𝒜₁ + H″_{1,k}δD − HD(𝒜₁ + H″_{1,k}δD), so the first-order change is ⟨J_w, (1 − HD)H″_{1,k}δD⟩, with the factor 1 + C_{HD}c_tot(1/128)ε₃ ≤ 3/2 of #4.47-2. |
| §4(d) #4.159 | The same reading of the support of 1 − ζ₀. | Cites #4.48-3–#4.48-3.0.0. |

Checked and matching: LFR II p.358 l.7–9, (1.7)–(1.8), (1.4), (1.25), (1.50), p.361 l.36–38; LFR I Proposition 1, (1.79), (1.83), p.197 l.39–42; VAR (172)–(175), Theorem 1 (p.279 l.9); PBG Theorems 3.12, 3.13, (3.133), p.422 l.32–33, p.423 l.39–40.

## Checked, unchanged

- LFR II p.357 l.1–56 ((1.2)–(1.6), l.33–38, l.51–53), p.358 l.1–24 ((1.7)–(1.9)), p.360 l.21–43, p.363 l.41–46. LFR I p.195 l.27–36 ((1.81), 𝐁₀), p.201 l.28–29. PRT2 (2.46), p.231 l.11. LF #3.29 (ε_k = g_kp₀(g_k)).
- CRE p.255 (2.4)–(2.6), l.30–48. The Cauchy note #C5.7–#C5.7-8.
- Cauchy note #C9.6.1-3–#C9.6.1-5 (local Hessian bound), LF #4.31 (PRT2 (2.60)), #4.41-3-1, #4.47-2, #4.48, #4.48.1.

## Files

- **Pins.** LF edbeac67699f, table cd814aac5ad0 (labels 328e517d7d93). The LF changed since 3befa8a18385 only outside 13a (#0.1.26.1's σ_u), and the rebuilt argument is byte-identical to the 3befa8a18385 build. 13a cites no table row, and none of the symbols renamed or entered on 7 Nov (ȟ_k, σ_u, r₁, C_KP, C^R, #T4.43, #T4.44, #T11.27-1, #T12.22) occurs in it.
- **Packet.** spec_p13a_r3.json, built at these pins, 0 definition conflicts (7 allowed), 19,166 argument characters, every packet line ≤ 611 (longest 609). The Cauchy note's #CP.13 and #C5.7–#C5.7-8, CRE (2.1)–(2.3), (3.5), pp.254–265 and p.269, LFR I pp.177–179 and pp.192–193, RG I p.251, and LFR II pp.359–360 and p.370 are added to the permitted background.
- **Pre-check, lf-p13a-20261107-r3.**
  - Changed lines re-derived: m1–m6 against the pages under *Checked, unchanged*.
  - Arithmetic re-checked: (1.8) gives γ₀‖∂Y‖² ≥ 2κ_Λ‖Y‖² at d = 4. The 1 − ζ₀ change is 2C_ℋ(1 + 2C_ℋC₁)C₁ε₁²e^{−(δ₀/16)d} ≤ 2(1 + 2C_ℋ)C_ℋC₁²ε₁²e^{−(δ₀/16)d} for C₁ ≥ 1, and e^{−(δ₀/16)d} = e^{−(δ₀/32)d}e^{−(δ₀/32)d} ≤ e^{−(δ₀/8)MR_k}e^{−(δ₀/32)d} for d ≥ 4MR_k. Contour lengths bound any of the usual lattice distances, so the step from 8MR_k − 1 to d(y, Λ) does not depend on which one p.363 uses. Cauchy: form = 2c₂‖Y‖_∞², |c₂| ≤ change/(2C₁ε₁)². C_A(M) sums the first- and second-order terms of #4.54-0.1 and #4.54-1 with ε/a_n ≤ 1. The runs' ratio is ≤ 2 from |δ_j| ≤ ½(g^A_j)^{−2}.
  - New symbols checked against the labels file: N_Λ, C_{1−ζ₀}(M) (C_ζ is taken, #4.109), C_A(M); 0 definition conflicts.
  - Wider implications: the only outside citations are table l.94 (κ_Λ, "#4.45", now defined in its sub-tag #4.45-1) and #4.568 ("k + 1 ≤ 8n + j(C) (#4.55)", now in #4.55-0.1 and #4.55-1); both resolve to the tag with its sub-tags, so neither changes. No caller cites #4.45's old wording.
  - Linear order kept: #4.45-1 points to *The bound on P.* by name; #4.48-4 cites #4.45-1; #4.48-4 points to (T-Λ) by name.
- **Status.** Launched on 7 Nov 2026 on the user's "Continue with 13a r3", headless, after the table fork's #T4.43 and #T4.44 edits. 13b's r2 findings wait until 13a is done.

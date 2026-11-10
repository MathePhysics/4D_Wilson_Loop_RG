# Triage: the 𝐑-step chain inputs #86, #88.1, #157 re-derived; D2.7 and inventory updated (7 Nov 2026, 18:10–18:22)

No referee round. #86, #88.1 and #157 of the two-loops note (two-loops-owned) were re-derived from the transcripts before they left D2.7's *Open* list and the inventory's Open table. All three hold. Two defects in the two-loops note and one in D2.7's #7 block (both two-loops-owned) were sent to two-loops. D2.7's own lines were repaired where they used the rejected n = 0 reading.

## Re-derivations

| Item | Checked against | Verdict |
|---|---|---|
| #157, #157-1–#157-3 | LFR I p.179 l.10, l.27, l.36; p.181 l.40; p.190 l.18–37; p.191 l.3–34; CRE p.261 l.15–40. At n = 0, j = h = k − N < k₀ = k − N₀, so (i) has no L₀ powers and (ii) is empty; Ω″_m = Ω_m for m ≤ h; Σ_{q=m+1}^k2^{−(q−m)} = 1 − 2^{−(k−m)} gives f_m, and (1.68) gives 3 on Ω_k; the cube families of (1.65) and (1.69) contain CRE (2.38)'s (Ω_{h+1}^c ⊂ Ω_{k₀+1}^c); so Ũ^{(0)c}(X) ⊂ 𝒟^3_k | holds |
| #86, #86-0, #86-0-1 | LFR II p.369 l.14, p.370 l.11, p.372 l.2–35, p.375 l.20–35; RG1 p.262 l.13; CRE p.259 l.41–44, p.261 l.60–62 | holds |
| #86.1, #86.1-1 | LFR I p.177 l.27–28, p.183 l.2, p.195 l.27–36, p.196 l.40; LFR II p.360 l.41–43; CRE (2.1), (2.3), p.264 l.52–53, (3.2)–(3.5) | holds, except the upper bound j′ ≤ k₀ (below) |
| #86.2–#86.3-2 | #44's layer crossing; (1.94) (p.198 l.54–56), whose α is a fixed constant, so ν_L does not depend on q₀ and q₀ > p₁ + θ_Lν_L is a consistent order; CRE (2.28) for δ′_k/α_{0,k} | holds |
| #88.1, #88.1-1–#88.1-4 | p.186 l.2–5 ((1.44)); p.191 l.37–43; covariance induction w̄_n = w̄_{n+1}u_n from (U^a)^b = U^{ba}; abs(σ_n) ≤ 12c_{nm}c_χδ′_k; BCH; (1 + x/16)² ≤ 1 + 9x/64 for x ≤ 1 | holds |

## Findings sent to two-loops (its files)

| Where | Finding | Consumers |
|---|---|---|
| two-loops #86.1-1 | "h ≤ j′ ≤ k₀" is false at the top: Λ = Z″_k plus one layer of M-cubes (LFR I (1.73), p.192 l.43–46), and in Z, Ω″_{k₀+1} = Ω^{∼7}_{k₀+1}, Ω″_k = Ω^{∼5}_{k₀+1} ((1.10)), so Λ₀ holds 𝔹_k″'s layers k₀+1, …, k−1 and part of layer k; the range is h ≤ j′ ≤ k | none uses the upper bound (#86.2 through #44; #86.2-0 and #86.3 use j′ ≥ h) |
| two-loops #87 | "For n = 0 the space is Ũ_k^c(X, α̃₀, α̃₁)" contradicts #157-3 (c = 3 on Ω_k) | #88, through #6.13 |
| D2.7 #7 block | three "OPEN (*Open* at the top)" marks; "lies in D(k)(iii)'s 𝒟_k" and "𝒟♮_k" where #6.13 and #88 give the reduced representative in 𝒟^{λ,3}_k | status marks and the set name |

## Repairs (own files)

| File | Where | Change | Kind |
|---|---|---|---|
| D2.7 | *Open* block | removed; the three inputs are derived, not reviewed, in the two-loops note | status |
| D2.7 | *Status*, item 5 status, item 15 status, 15.8 status, 15.9 | "OPEN through #86, #88.1, #157" replaced by "derived, not reviewed" | status |
| D2.7 | item 5(b) | "that configuration lies in D(k)(iii)'s domain 𝒟_k" replaced by "its reduced representative lies in 𝒟^{λ,3}_k (table #T4.49), where the insertions are analytic (two-loops #6.12–#6.13, #88)" | derivation |
| D2.7 | 15.5(ii)(α′)(3) | "D(k)(iii) on 𝒟_k, which contains the space (1.65): … coincide with Ũ_k^c at n = 0 (p.191 l.33–36)" replaced by the class's analyticity on 𝒟^{λ,3}_k (two-loops #6.12–#6.13, #6.13-2); "𝒟♮_k as at s = 1" corrected to 𝒟^{♮,3}_k | derivation |
| inventory | Open, Awaiting review, Closed | rows #157, #86, #88.1 moved to Awaiting review as one row; 15.5(ii)(α′)'s row and #220's and #160's rows updated | status |
| table | #T12.22 | BETA's BQ δ₀ and B₀ entered (the first bound of PBG (3.42) common to G_C, G and G₁, #BQ.3), distinct from p.423 l.39–40's common δ₀ (#T4.30's), which is fixed after (3.132); re-derived from PBG p.422 l.12–13, l.50, p.423 l.4–5, l.29–40 | index |
| table | new #T11.27-1, #T11.27-2 | two-loops' proposed fact, re-derived: lengths in T_{L^{−j}} are in j-block units (RG I p.257 l.2–4, l.11–12; LFR I p.178 l.51–52 at η = L^{−k}, p.179 l.7–8), so (2.14)'s M₁ and 2M₁ are M₁L^jη and 2M₁L^jη, and 𝐁_j(Ω)'s Ω_n are M₁L^nη-cubes (CRE p.256 l.60–61) | index |

## Pre-check

Every changed line was re-read. Every "OPEN" and "*Open*" in D2.7 was grepped: the remaining ones are in the two-loops-owned #7 block (sent). "coincides", "p.191 l.33", "𝒟♮_k" and "⊇ (1.65)" were grepped in D2.7, the inventory and the table.

## SHAs

- D2.7 d0664862e3cf → 11d562a80409
- inventory DDC08A77100E → 36ca9dc55b60
- table 80bb9f361a9e → 794024f152f0 → cb04a87d3ce5
- LABELS_LF_AND_TABLE 451d9b947474 → adf4d335ae96 → 73ef5a2bf7fc
- BETA's BD 2c7ec9df22dc, BQ 0e44fea98dd2 (received)

## Two-loops' repairs (verified)

TL 9499176112b5: #86.1-1 now reads h ≤ j′ ≤ k with (1.10) and (1.73), and #87 places the n = 0 space in 𝒟^3_k. D2.7 5e2af8c989e8: the #7 block has no OPEN and names 𝒟^{λ,3}_k. One leftover was sent back: #87's last sentence, "it lies in 𝒟_k", had an ambiguous subject. It now reads "the chain's end point, in its reduced form, lies in 𝒟^{λ,3}_k (#6.13, #88; …)" (TL eab31ddb367c, verified).

## Messages

- Two-loops: the re-derivation, #86.1-1, #87, and the #7 block marks; SHAs.
- BETA: #T12.22 entered, with the re-derivation; table SHA.

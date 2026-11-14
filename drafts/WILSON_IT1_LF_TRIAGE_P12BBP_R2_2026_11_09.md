# Packet 12b-bp (BP_LFR2_CHI_K_LAMBDA.md), round 2, 9 Nov 2026

## Pre-check of bp-p12bbp-20261109-r2 (full)

- **Whole packet read** (#3.84–#3.90), with LF #3.76 and #3.83, table rows #T1.9, #T2.23, #T10.1-1, and #T12.12, LFR II p.378 l.1–20, CRE p.257 l.24–46 ((2.16)–(2.17)) and p.266 l.8–24 ((3.6)–(3.7)), VAR p.308 l.36–48 ((190)), p.288 l.45, and PRT2 (2.46) on p.231.
- **Repairs made in this pre-check:**
  - #3.84-0 stated the soft test for the cube of p only, while #3.86.1-1 bounds every k-plaquette of the enlarged cube around □^{∼4}. p.378 l.6 applies the decomposition in the components of Z, and LFR I (1.71) tests every cube of Ω_k^{∼4}, so every LM₂R_k-cube □ ⊂ X_i passes, with sup_{p′⊂□^∼} (CRE (2.17)). #3.84-0 now says so, and draws the bound at p as the case of p's cube.
  - #3.86.1-1 now places each k-plaquette of the enlarged cube in a cube □′ ⊂ X_i. The points of □′ differ from p by less than MR_k + LM₂R_k < 2MR_k in every coordinate (M ≥ (dL + 4)M₂, #3.76), so they lie outside Λ_k, at distance ≥ 2MR_k from p (#3.84), and are joined to p in Λ_k^c.
  - "γ small" is cited to #T1.9 at its first use (#3.84-1.1-1). #3.87 now cites R_k ≥ (log g_k^{−2})^r with g_k ≤ (1 + β₀)γ (#T2.23, #T1.9) for R_k → ∞.
  - #3.87 names its rate as CRE's δ of (3.7), p.266 l.18 (#T10.1-1). (190) bounds the kernel pointwise at the rate ⅛δ₀ in PRT2 (2.46)'s distance, which counts a bond of Λ_j as one unit of L^jη. Summing it over the layer costs a polynomial factor, and CRE's printed rate absorbs that, so replacing it by ⅛δ₀ would be unsupported.
  - #3.90's closing aside about "the room" of (1.75) is deleted.
- **Re-derived:**
  - #3.86.1: the complete axial tree inside a cube of side s joins b₋ and b₊ by paths that agree up to the direction μ of b. The loop then encloses, for each ν > μ, a ladder of width 1 and length ≤ s, so ≤ (d − 1)s plaquettes, with s ≤ MR_k.
  - #3.86-1.1: 2α₀ ≤ 11d²α₀ and 2(1 + κ_s)ε_k ≤ 2α₁ (2(d − 1)MR_k ≥ 1), so (7) holds at ε₁′ for both data.
  - #3.87: (π/2)(11d²α₀ + 2α₁) = (π/2)(22d²B₃ + 4(d − 1)MR_k)(1 + κ_s)ε_k.
  - #3.88–#3.90: (1 + 1/4 + 0.2·1.4)/(1 − 4/20) = 1.53/0.8 < 2.
- **Definition check:** 0 conflicts (9 allowed, as in r1).
- **Consumers:** LF #3.83 cites #3.84–#3.90 for the bound only, which is unchanged. Table #T12.12's τ is unchanged.
- **Size:** 9.50k before and 9.98k after. CR is 0, and there are no trailing spaces, duplicate tags, or lines over 600.
- **Spec:** specs\spec_p12bbp_r2.json (BP 03a2452da83d, Cauchy a0b36ebcf1d0, LF 56d172c27cf2). Its claim (a) now reads "every LM₂R_k-cube in X_i, p's cube □ included". The table record adds γ (#T1.9), and the background adds VAR (190) on p.308, LFR II p.378 l.6, and CRE (2.17).
- **Order:** after 14b r2's triage. Nothing is running.
- **Built** at 07:25: 0 conflicts (9 allowed); reviewed block 9.3k. Launched at 07:26.

Written 2026-11-09 07:25.

## Verdict of bp-p12bbp-20261109-r2

No fatal or serious finding. There are four minor findings, m1–m4, and all four are correct, so the round is not clean. The referee confirms the claim: #3.84–#3.90 prove |U_{k,Z}(∂p) − 1| < 2ε_kη² on Ω_k^c ∩ X_i, uniformly in the volume, k, K, ε, and the number of layers. The review is reviews\bp-p12bbp-20261109-r2\review.md (20.4k), read in full.

## Repairs

| Finding | Repair |
|---|---|
| m1, #3.84-1.1-1: the constant of CMP98 (54) is called C₁ | Checked: CMP98 (54) (p.026 l.46–52) prints α₀ + 2C₀α₀² < 2α₀, and REG p.87 l.36 writes 2C₁. The line now reads "a + 2C₀a² < 2a … C₀ the constant of CMP98 (54), p.026 l.46–52, written C₁ at REG p.87 l.36". 2C₀a < 1 follows from a ≤ c₂ ≤ 1/(3C₀), which γ small gives |
| m2, #3.85.1-2: VAR p.301 l.44–45 cited for openness | That passage is the neighbourhood argument for (150). The line now draws openness from VAR (2) (p.278 l.5–6) itself: its bounds are strict inequalities between continuous functions of the bond variables |
| m3, #3.87: the step from the derivative bound (190) to the bound on 𝐇 inherited from (3.7) | The step is now written out. At B = 0 the minimiser is U_{k,Z}^w, so 𝐇(0) = 0 and 𝐇(B) = ∫₀¹(δ𝐇/δB)(tB)B dt, each tB within (172). B vanishes off the layer, and (190) (p.308 l.37–47) bounds the kernel and its gradient on □^∼ (L^kη = 1) by O(1)(L^{j′}η)^{−d}exp(−⅛δ₀d(y, y′)). The sum over the layer is (3.7)'s (p.266 l.14–22), with CRE's δ and B₃ (#T10.1-1). The line, at 817 characters, is split into #3.87 and #3.87-1 |
| m4, #3.88-1: E₂ bounded by reading (3.8)'s second term, which omits the cubic terms | Replaced by a direct bound. By REG (1.22) (p.079), E₂ + 1 is the product of four factors e^{iA_i}, two of them conjugated by U₀, with abs(A_i) ≤ s := τε_kη. The linear part iΣ±A_i is iη times two U₀-covariant differences of 𝐇, of norm ≤ 2τε_kη². The remainders of e^{iA} − 1 − iA give 4·s²/2, and the products of two, three, and four factors e^{iA_i} − 1 give 6s² + 4s³ + s⁴. So abs(E₂) ≤ 2τε_kη² + 8s² + 4s³ + s⁴ ≤ (2τ + 9τ²)ε_kη², since 8 + 4s + s² ≤ 9 at s ≤ 1/20. #3.89 now reads (1 − 4τε_kη)^{−1}(1 + κ_s + 2τ + 9τ²)ε_kη², and #3.90's middle term is (1.25 + 0.1 + 0.0225)/0.8 = 1.3725/0.8 < 2. CRE (3.8) is no longer used |

- **Split:** #3.84-1.1-1 (631 characters after m1) is split at its second sentence into #3.84-1.1-1 and #3.84-1.1-1-1. Neither new tag occurs in the LF note, the table, or balaban_proofs/.
- **Consumers:** LF #3.83-1 cites #3.84–#3.90 for the bound < 2ε_kη², which is unchanged. Table #T12.12's τ is unchanged. No other file cites #3.87, #3.88-1, or (3.8)'s second term from this file.
- **Repaired SHA:** BP ffa8a38e3e22. CR is 0, and there are no trailing spaces, duplicate tags, or lines over 600.
- **Next:** r3, narrow, on #3.84-1.1-1–#3.84-1.1-1-1, #3.85.1-2, and #3.87–#3.90, the rest as context. It runs after 14bp r3.

Written 2026-11-09 07:46.

- **Update (07:56):** the REG pins are now print lines, file line − 1 (table #T6.6). The table fork passed on BETA's finding of off-by-one REG pins in another file, and I checked this file against REG/parts. The Proposition 2 sentence is file line 36 of p087.tex, so REG p.87 l.36 → l.35 (×3, in #3.84-1.1-1 and #3.85-1). The iteration is p.87 l.36–41 → l.35–40 (#3.86-1). Locality is p.80 l.5–6 → l.4–5 (#3.86-1). REG p.81 l.24–25 → l.23–24 (#3.86-1-1). The repaired rows above keep the old pins as written. BP is now df3dad742c4d. r3 also covers #3.85-1, #3.86-1, and #3.86-1-1 for these pins.

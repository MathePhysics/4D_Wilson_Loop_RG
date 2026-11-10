# Packet 12b-bp (balaban_proofs/BP_LFR2_CHI_K_LAMBDA.md), round 3, 9 Nov 2026

## Pre-check of bp-p12bbp-20261109-r3 (narrow)

- **Lines under review:** #3.84-1.1-1–#3.84-1.1-1-1, #3.85.1-2–#3.85-1, #3.86-1–#3.86-1-1, and #3.87–#3.90. These are r2's repaired lines (m1–m4), the split, and the lines whose REG pins were corrected (WILSON_IT1_LF_TRIAGE_P12BBP_R2_2026_11_09.md, update 07:56), with their consumers. The rest of the file, reviewed CORRECT in r2, is context.
- **Every line of the file re-read** on 9 Nov 2026 (BP df3dad742c4d).
- **Re-derived:**
  - #3.84-1.1-1: a + 2C₀a² < 2a iff 2C₀a < 1, which a ≤ c₂ ≤ 1/(3C₀) gives for γ small.
  - #3.87-1: sup abs(B) ≤ (π/2)(11d²α₀ + 2α₁), with α₀ = 2B₃(1 + κ_s)ε_k and α₁ = 2(d − 1)MR_k(1 + κ_s)ε_k. That is (π/2)(22d²B₃ + 4(d − 1)MR_k)(1 + κ_s)ε_k, and the factor B₃e^{−δ2M₂R_k} turns it into τε_k.
  - #3.88: the product of two factors U₁(b), each within τε_kη of 1, is within 2τε_kη of 1. So abs(P)abs(Q) + abs(S) ≤ 4τε_kη.
  - #3.88-1: Π(1 + x_i) − 1 with x_i := e^{iA_i} − 1 is Σx_i + Σ_{i<j}x_ix_j + Σ_{i<j<l}x_ix_jx_l + x₁x₂x₃x₄.
    - The linear part iΣ±A_i is iη²(the U₀-covariant curl of 𝐇), of norm ≤ 2τε_kη².
    - Σ(e^{iA_i} − 1 − iA_i) ≤ 4·s²/2 = 2s², and the products of two, three, and four factors give 6s² + 4s³ + s⁴.
    - With ε_k, η ≤ 1, 8s² ≤ 8τ²ε_kη², and 4s³ + s⁴ ≤ (4/20 + 1/400)s² ≤ τ²ε_kη².
  - #3.89–#3.90: abs(X)(1 − 4τε_kη) ≤ abs(W − 1) + abs(E₂), with abs(W − 1) < (1 + κ_s)ε_kη² (#3.84-0). And (1 + 1/4 + 1/10 + 9/400)/(1 − 1/5) = 1.3725/0.8 = 1.7156 < 2.
- **Pins:** REG p.87 l.35 (Proposition 2), p.87 l.35–40 (the iteration), p.80 l.4–5 (locality), and p.81 l.23–24 (the Landau representative) are print lines, file line − 1 (table #T6.6), as checked at 07:56. CMP98 (54) is p.026 l.46–52, and VAR (190) is p.308 l.37–47.
- **Grep of touched claims:**
  - LF #3.83–#3.83-1 cite #3.84–#3.90 for the bound < 2ε_kη², which is unchanged.
  - Table #T12.12 records B, W, X, α₁, and τ, which are unchanged.
  - The new local letters s and e^{iA_i} of #3.88-1 occur nowhere else in the file.
- **No known weak point** remains in the lines under review.
- **Definition check:** 0 conflicts (11 allowed). These are r2's nine, plus s and e^{iA_i} of #3.88-1, both local to that line.
- **Size:** the reviewed lines are 5.02k characters (25k cap). The file is 9.98k. CR is 0, and there are no trailing spaces, duplicate tags, or lines over 600.
- **Spec:** specs\spec_p12bbp_r3.json (BP df3dad742c4d, Cauchy d901e7a1b941, LF 6ac728004094). The background now cites REG (1.22), CRE (3.7) on p.266 l.14–22, CMP98 (54), and VAR (2) on p.278 l.5–6 for the openness. It drops VAR p.301 l.44–45.
- **Order:** after 14a r4. Rebuild at launch.

Written 2026-11-09 08:19.

- **Built** at 08:31 (BP df3dad742c4d, Cauchy d226af81ac1b after 14a r4's repairs, which touch none of this packet's Cauchy context, LF 6ac728004094, table a9ff90c0cf7f, LABELS 40cd822d99e0). The argument field, context included, is 15.8k characters. Launched at 08:31, after 14a r4's triage.

## Verdict of bp-p12bbp-20261109-r3

No fatal or serious finding. Three minor findings (m1–m3) and one remark, all correct, all repaired. Not clean: next r4 narrow, then r5 full.

## Repairs

| Item | Finding | Repair |
|---|---|---|
| m1 | #3.86-1 cites #3.84-1.2, stated on □^{∼4} only, for Lemma 1's (1.7) on the k-blocks around it too | #3.86-1 now cites the bounds of #3.84-1.2 on □^{∼4} and of #3.84-1.1-1-1 on the k-blocks around it |
| m2 | #3.85-1 points to #3.86-1 for VAR (172) | pointer is #3.86-1.1 |
| m3 | #3.88-1 does not state its reading of REG (1.22) | #3.88-1 states the reading U₁(y, z) as the third factor, as in (1.21), labelled inferred, not printed, with the print U′(z, y) and the identity (1.43) |
| remark | the factor (1 − 4τε_kη)^{−1} in #3.89 is unnecessary | #3.88 now writes W − 1 = (1 + P)XQ + E₂ with unitary 1 + P and Q, so abs(X) ≤ abs(W − 1) + abs(E₂); #3.89 has no factor, and #3.90 drops ε_k ≤ 1 and 0.8 |

- **Re-derived:**
  - (1.43) with S = Q − 1: PXQ + X(Q − 1) + X = (1 + P)XQ. Here 1 + P = U₁(x,y)R(U₀(x,y))U₁(y,z) and Q = R(U₀(x,w))U₁(z,w)U₁(w,x) are products of unitary factors, so abs((1 + P)XQ) = abs(X).
  - #3.89: abs(X) ≤ (1 + κ_s)ε_kη² + (2τ + 9τ²)ε_kη², and 1 + 1/4 + 1/10 + 9/400 = 1.3725 < 2.
  - #3.88-1's E₂ bound still uses ε_k, η ≤ 1 and s ≤ 1/20, as stated there.
- **Consumers:** LF #3.83-1 uses the bound < 2ε_kη² (#3.89), unchanged. Table #T12.12's B, W, X, α₁, and τ are unchanged.
- **Hygiene:** line 29 reached 717 characters after m3 and was split at "The rest is" into #3.88-1-1 (the tag is unused in the LF and in this file). CR 0, no trailing spaces, duplicates, or long lines.
- **Repaired SHA:** BP 8f87e8c3ee33.

Written 2026-11-09 08:47.

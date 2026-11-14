# Packet 14bp (balaban_proofs/BP_CMP98_ADJOINT_AVERAGING.md), round 5, 9 Nov 2026

## Pre-check of bp-p14bp-20261109-r5 (narrow)

- **Lines under review:** #C10.3.21-2–#C10.3.21-3 and #C10.3.23-3–#C10.3.23-4. These are r4's reworded lines, #C10.3.21-2, #C10.3.21-3, and #C10.3.23-3 (WILSON_IT1_LF_TRIAGE_P14BP_R4_2026_11_09.md), with their consumer #C10.3.23-4. The rest of the file, reviewed CORRECT in r3 and r4, is context.
- **Every changed line re-read** on 9 Nov 2026 (BP 0c5dc5ff8bfd).
- **Re-derived:**
  - P_{b,Γ} := Ad(W(Γ from c₋ to b₋)) is the operator that #C10.3.21-2's ±Ad(W(γ from c₋ to b₋)) becomes for b on Γ, Γ being the initial segment of γ. #C10.3.23-3 takes its adjoint P_{b,Γ}* = Ad(W(Γ from c₋ to b₋)^{−1}), an isometry.
  - Per occurrence: γ may visit b₋ twice (#C10.3.21). For the occurrence of b on −Γ′, the rest of γ after that visit runs along −Γ′ to c₊. So W(γ) = W(γ from c₋ to b₋)·W(Γ′ from c₊ to b₋)^{−1}, which gives #C10.3.21-3's factorisation, with W(γ) = hW(c) (#C10.1.4-0-2).
  - Sign: if b has sign s on Γ′, then −Γ′ traverses it with sign −s. With P_{b,Γ′} = P_{b,Γ} for the same contour of 𝐆(y, x̂), the leaving terms give +s·P_{b,Γ}*ν(c) and the entering ones −s·P_{b,Γ}*Ad(W(c))^{−1}ν(c). The bracket Σ_{c₋=y}ν(c) − Σ_{c₊=y}Ad(W̄(c))^{−1}ν(c) is −LηD*_{W̄}ν(y) for the site pairing (Lη)^dΣ_y, as in #C10.3.23-4.
- **Grep:** P_{b,Γ} and P_{b,Γ′} occur in this file and in Cauchy #C10.3.31-2, which counts Ad(W(c))P_{b,Γ′} as one transport of norm 1, consistent with the Ad definition.
- **No known weak point** remains in the lines under review.
- **Definition check:** 0 conflicts (8 allowed, as in r4).
- **Size:** the reviewed lines are 1.32k characters (25k cap). Lines 7, 8, 23, and 24 are 371, 259, 248, and 442 characters. CR is 0, and there are no trailing spaces or duplicate tags.
- **Spec:** specs\spec_p14bp_r5.json (BP 0c5dc5ff8bfd, Cauchy 14ee33c357e1, LF 6ac728004094). #C10.3.23-5 moves to context, its bound being unchanged since r4.
- **Order:** after 14b2 r3. Rebuild at launch.

Written 2026-11-09 08:57.

## Build and Verdict

- **Build (10:13):** BP 0c5dc5ff8bfd, Cauchy 4c3614eed5e5, LF 029a1d03a304, table 611d15a06e81, LABELS 8c04ad0e29d7.
- **Verdict: clean.** There is no fatal, serious, or minor finding, and all four named lines are CORRECT. This is the first clean round of 14bp; r6 is full. The referee checked:
  - the signs and transports per occurrence;
  - the factorisation of #C10.3.21-3 in both orientation cases, including the endpoint checks b₋ = c₊ and b₋ = x′ and a flat pure-gauge check;
  - the shared P_{b,Γ}* and the opposite sign of the entering terms;
  - −LηD*_{W̄}ν(y) against both pairings and PBG (3.114)–(3.116), p.418.
- **Remark below the minor threshold, applied:** #C10.3.21-2 now reads "Each occurrence in γ of a bond b = ⟨b₋, b₊⟩ contributes ±Ad(W(γ from c₋ to b₋))iηA(b) to dW(γ)W(γ)^{−1}". This rewords the existing sentence; no mathematics changed.

## Pre-Check of r6 (Full)

- **Whole file read** (lines 1–30) for gaps; re-derived:
  - #C10.3.21: the weight L^{−1}|𝐆(c₋, x)|^{−2} from the pairings η^dΣ_b and (Lη)^dΣ_c.
  - #C10.3.21-6: Σ_{α<β}|n_α||n_β| ≤ (d − 1)|n|₁²/(2d) with |n|₁ ≤ dL/2. And (d − 1)(d + 4)L²/8 ≤ dL² iff d² − 5d − 4 ≤ 0, which holds for d ≤ 5.
  - #C10.3.21-7: c_{av} ≥ 4d gives dL²κ_W ≤ 1/32. Then κ_W ≤ ρ_𝔤/L² < ρ_𝔤 and 2κ_W ≤ 1/(16dL²), so the path stays within 1/16 of 1.
  - #C10.3.21-7-2: the logarithms on the path are ≤ 1/8, and |ad X| ≤ 1/4 < 2π.
  - #C10.3.21-8: (e^a − 1 − a)/a² = 0.5215 at a = 1/8, so the bound is ≤ 0.53a. Also 0.53·4/(1 − 0.066) ≤ 2.4.
  - #C10.3.22: each fine bond lies on [x, x′] for L points x, each of weight L^{−1}.
  - #C10.3.23-2: each of the 2d bonds has weight L^{−1}|𝐆(y, x̂)|^{−1}.
  - #C10.3.24-1: (1 + x)⁴ − 1 = 0.6018 ≤ 5x at x = 1/8, with total weight 1 + 2dL^{d−1}.
  - #C10.3.24-2: (1 + x)³ − 1 = 0.4238 ≤ 4x, and each fine bond lies in at most one coarse bond.
  - #C10.3.24-3: 5x(1 + (2d + 1)L^{d−1}) ≤ 10(d + 1)xL^{d−1} = c_QL^{d+1}κ_W.
  - #C10.3.24-4: x = 4c_{av}C₀ε₁L^{2(i+1−n)} ≤ 4c_{av}C₀ε₁.
- **No weak point found.** Hygiene: CR 0, no trailing spaces, no duplicate tags, no line over 600 characters.
- **SHAs:** BP 7e76b7fcdacf, Cauchy 1f73875e3b26, LF 029a1d03a304, table 40e20f5e4530, LABELS 3a2b74eff243.
- **Spec:** specs\spec_p14bp_r6.json, all of #C10.3.21–#C10.3.24-4 under review.

Written 2026-11-09 10:19.

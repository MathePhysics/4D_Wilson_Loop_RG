# Packet 12b-bp (BP_LFR2_CHI_K_LAMBDA.md), round 1, 9 Nov 2026

## Pre-check of bp-p12bbp-20261109-r1 (full)

- **Whole packet read** (#3.84–#3.90) on 9 Nov 2026, with its context: LF #3.76–#3.76-1 and #3.83–#3.83-1, and table rows #T12.8 and #T12.12.
- **Citations checked against the corrected transcriptions** (REG has no corrected file, so its pins are to the transcription):
  - LFR II p.378: l.6 (the decomposition 1 = χ_k((Ω_k^{∼4})^c) + χ_k^c), l.10 ("This is clear for χ_{k,Λ}"), and l.10–11 (|∂V_k − 1| < 2ε_k on the first class).
  - CRE:
    - (1.3) on p.246 (Q^{s*}V is 1 inside blocks and V(c) on the bonds joining B(c₋) and B(c₊));
    - p.245 l.34–38 (M ≫ M₂ > M₁) and l.38–40 (compatible partitions);
    - (2.2) on p.255 (display l.13–18);
    - p.256 l.43–53 (the unique minimal orbit, (2.12)) and l.57–63 (the domains of 𝔹_j(Ω): Ω_n a union of L^nξM₁-cubes, l.60; dist(Ω_n, Ω_{n−1}^c) ≥ L^nξM₁, l.61; Ω^{∼−2} ⊂ Ω_j, l.62);
    - (2.16)–(2.17) on p.257;
    - p.264 l.52 (Z_k = Λ_k^c);
    - (3.6)–(3.8) on p.266, with l.11–14 (B = (1/i)log[…] off the layer of width 2M₁, the bound 30d²L²B₃(1 + β₀)ε_k on the layer, and (190));
    - (3.20) on p.269 (Λ_{k+1} ⊂ Ω_{k+1}^{∼−2});
    - p.251 l.34–36 ((190) for the Landau gauge).
  - RG I: (0.4) on p.253; (0.12) on p.254 l.1–6; p.252 l.34 ("the definition introduced in [12]").
  - CMP 98: (11) on p.19 l.13 and (15) on l.46 (display lines; the tags are on l.14 and l.47).
  - REG: (1.7) on p.77; (1.14) and (1.15) on p.78; (1.19) on p.79; p.80 l.5–6 (locality of Lemma 1); p.81 l.24–25 (Σ_k ⊄ 𝔙_k); (1.35)–(1.38) on p.82; (1.43) on p.83; p.87 l.36–41 (Proposition 2 of CMP 98 and the iteration of Lemma 1 to 11d²α₀ + α₁).
  - VAR: (2), (6), and (7) on p.278; (8) and Theorem 1 on p.279, with uniqueness at l.15 under B₃ε₁ ≤ ε₀ ≤ a₀; p.301 l.44–45 (the minimum in the smaller space); (190) on p.308.
- **Arithmetic re-derived:**
  - #3.84-1.1, the averages. Level-j blocks nest in k-blocks. So every contour of CMP 98 (15) inside a level-j block is 1, and each straight segment of a bond joining two k-blocks crosses the boundary once, carrying V_k(c). The loop U(Γ_{c,x})U(c)^{−1} is then 1, and the average is U(c), which is 1 or V_k(c).
  - #3.85-1, Theorem 1's uniqueness. With ε₁ = 2α₀ and ε₀ = (1 + 2B₃)α₀: B₃ε₁ = 2B₃α₀ ≤ ε₀ ≤ a₀ for γ small.
  - #3.86.1. □^{∼4} has side LM₂R_k + 8M₂R_k = (L + 8)M₂R_k. |V_k^w − 1| < (d − 1)MR_k·2(1 + κ_s)ε_k = α₁.
  - #3.86-1. |a − b| ≤ |a − 1| + |b − 1| < α₁ + 11d²α₀ + α₁, so |B| ≤ (π/2)(11d²α₀ + 2α₁).
  - #3.87.
    - dist(□^∼, layer) ≥ 3M₂R_k − 2M₁ ≥ 2M₂R_k, since M₁ < M₂.
    - B₃e^{−δ2M₂R_k}(π/2)(22d²B₃ + 4(d − 1)MR_k)(1 + κ_s)ε_k = τε_k, using 11d²α₀ = 22d²B₃(1 + κ_s)ε_k and 2α₁ = 4(d − 1)MR_k(1 + κ_s)ε_k.
  - #3.88–#3.89.
    - (1.43) reads W − 1 = PXQ + XS + X + E₂, with P, S each two factors U₁(b) (conjugated by R(U₀)) minus 1, and Q unitary. So |P||Q| + |S| ≤ 4τε_kη.
    - |E₂| ≤ 2τε_kη²(1 + 4τε_k) is (3.8)'s second term with 1/10 → τ.
    - Then |X|(1 − 4τε_kη) ≤ (1 + κ_s)ε_kη² + |E₂|, and (1 + 1/4 + (1/10)(1 + 1/5))/(1 − 1/5) < 2 for ε_kη ≤ 1.
- **Repairs made in this pre-check:**
  - The header line (622 characters) is split at its third sentence into two paragraphs.
  - #3.86-1.1 is deleted. It compared #3.86-1's bound with CRE p.266 l.12–13's and anticipated #3.87, which makes the absorption itself. No line cites it.
- **Definition check:** 6 conflicts, all allowed in the spec. They are the file's local letters B, W, X, and τ, REG's α₁ (local to #3.84-1.2–#3.87, as #3.84-1.2 states), and the convention Ω_{k+1} := ∅. Table rows #T12.8 and #T12.12 record each as this file's.
- **Size:** 7.70k before and 7.50k after. The largest line is 592 characters. CR is 0, and there are no trailing spaces.
- **Spec:** specs\spec_p12bbp_r1.json (BP a9d749094150, LF d72f4de24c38 after the bookkeeping edits of 04:07). Its check gives 0 conflicts (6 allowed).
- **Order:** launch after 14bp r1 (one referee at a time: 12b r12, then 14 r1, then 14bp r1).
- **Messages:** the table fork is sent the deleted tag #3.86-1.1 and the new SHA.

Written 2026-11-09 04:02.

## Pre-check of bp-p12bbp-20261109-r1 (full), redone after the RG I (0.4) conversion

The pre-check above is superseded: packet 14 r1's M8 put the chain's average at RG I (0.4) (Cauchy #C10.1.4–#C10.1.4-0-3), and #3.84-1.1 and #3.85.1 were converted.
- **Changed lines re-read,** with the whole file:
  - #3.84-1.1 now cites CRE (1.3) and Cauchy #C11b.2-4.
  - #3.85.1 cites RG I (0.4) and #BC.3-2.
  - #3.86-1 uses Proposition 2 of CMP 98 for (0.4).
- **#C11b.2-4 re-derived.** This is the induction on j, for a level-(j + 1) bond b′ with j + 1 ≤ k.
  - The contours of 𝐆(b′₋, x) are coordinate-monotone, so they stay in the cube B(b′₋) ⊂ one k-block (#BC.3-2-1), and the same holds for 𝐆(b′₊, x′). They carry 1.
  - [x, x′] and the straight path of b′ each cross the face between B(b′₋) and B(b′₊) once. That face lies on a k-face exactly when the two blocks lie in different k-blocks, and then the crossing bond carries V(c).
  - So W(γ) = W(b′) ∈ {1, V(c)}, h = 1, Y_{b′} = 0, and M(b′) = W(b′).
  - The data plaquettes are then 1 or k-level plaquettes of V_k. At a corner of four k-blocks the four crossing bonds give V(c₁)V(c₄)V(c₂)^{−1}V(c₃)^{−1}, a plaquette of V_k.
- **Repairs in this pre-check:**
  - #3.85.1 cited "RG I (0.4) and (0.12), p.253 and p.254 l.2–6", and it read Ū^{n−1} "only on Δ(c₋) ∪ Δ(c₊)". (0.12) is RG I's alternative average through the group-averaged contour variables (0.11) (p.253, last lines, and p.254 l.2–6). The chain's average is (0.4) (Cauchy #C10.1.4), so the chain does not use (0.12). Δ is not defined in this file. The line now reads "only on the bonds with both end-points in the blocks of c₋ and c₊ (RG I (0.4), p.253; #BC.3-2)".
  - #3.86-1 used "Proposition 2 of CMP98", which is proved for CMP 98's own average. It now adds "valid for (0.4) (Cauchy #C10.1.4-0-3)". That line records RG I p.254 l.7–10 and RG I's own applications of CMP 98 to its averages.
- **Consumers:** LF #3.83–#3.83-1 cite #3.84–#3.90 for the bound only, which is unchanged. BP_LFR2_REPLACEMENT #160.5-1 is the two-loops session's; it now cites RG I (0.4) (BP #3.84-1.1).
- **Definition check:** 0 conflicts (6 allowed, as above).
- **Size:** 7.50k before and 7.41k after. The largest line is 592 characters. CR is 0, and there are no trailing spaces.
- **Spec:** specs\spec_p12bbp_r1.json (BP 86914d878565, Cauchy 1b66a27cdc01, LF 31538d03f6ab). The Cauchy note's #C10.1.4–#C10.1.4-0-3 and #C11b.2-2–#C11b.2-4 are added as context. The permitted background cites RG I (0.3), (0.4), and p.254 l.7–10 in place of CMP 98 (15) and (0.12).
- **Order:** launch after 14bp r1 reports.

Pre-check redone 2026-11-09 05:07.

## Verdict of bp-p12bbp-20261109-r1 (full)

- No fatal or serious finding. There are nine minor findings, m1–m9, all correct, so the round is not clean. Every step was rated CORRECT, and the one-line verdict confirms the bound.
- The referee reports that the harness context included AGENTS.md project-status text (context-exposed), none of it about this packet.

## Repairs (BP_LFR2_CHI_K_LAMBDA.md)

| Finding | Repair |
|---|---|
| m1, #3.84-1.1: soft ε₁ stated, not derived | New #3.84-1.1-1 derives it. On the k-plaquettes of □, V_k = M^k(U_{k,□}), the constraint on the deepest domain ⊃ (□^{∼4})^{∼−2} ⊃ □^∼ (CRE p.256 l.62–63). The soft test bounds U_{k,□}'s plaquettes in □^∼ by aη², a = (1 + κ_s)ε_k. CMP98 Proposition 2, as at REG p.87 l.36 with L^kη = 1, then gives a + 2C₁a² < 2a |
| m2, #3.85-1, #3.86-1, #3.87: VAR (172) unchecked | New #3.86-1.1. V′ = e^{iB} has |V′ − 1| < ε₁′ := 11d²α₀ + 2α₁, which is (172) with constant 1 at VAR's ε₁ raised to ε₁′. (7) holds at ε₁′ for both data (2α₀, 2(1 + κ_s)ε_k ≤ 2α₁ ≤ ε₁′), ε₁′ ≤ a₁ and B₃ε₁′ ≤ a₀ for γ small, and the minimal orbit is the same by uniqueness (VAR p.279 l.15). So Proposition 9 and (190) apply. #3.85-1 points there |
| m3, #3.87–#3.88: U_{k,Z} for U_{k,Z}^w | #3.87 now reads ∇^η_{U_{k,Z}^w}. #3.88 takes U₀ = U_{k,Z}^w and X := U_{k,Z}^w(∂p) − 1, of the norm of U_{k,Z}(∂p) − 1 |
| m4, #3.84, #3.84-1: Z componentwise | The intro states that U_{k,Z} is defined in each component separately (LFR I p.192 l.55), so Z, Z^c, 𝔹_k(Z), and the Z-problem are those of one component X_i. #3.84 uses X_i^c |
| m5, #3.86, #3.86.1: w off □^{∼4}, bonds at ∂□^{∼4} | w is the complete axial gauge on the k-blocks of □^{∼4} and of the layer around it (in the deepest domain, #3.84-1), and 1 elsewhere. #3.86.1 gives the enlarged cube's side as (L + 8)M₂R_k + 2 ≤ (dL + 4)M₂R_k ≤ MR_k (d = 4, L ≥ 2), with the data bonds at ∂□^{∼4} included |
| m6, #3.85.1-1: lower-level data | #3.85.1-1 now adds that the data of levels j < k lie in the layers within 2M₁ of Z^c (p.256 l.61–62), at distance ≥ MR_k − 2M₁ from □^{∼4}. The rest of the line moved to #3.85.1-2 |
| m7, #3.88: E₂ by homogeneity | #3.88-1. Since τ ≤ 1/20 < 1/10, (3.7)'s bound holds, and (3.8)'s printed second term (2/10)ε_kη²(1 + (4/10)ε_k) is used. #3.89 now carries this term |
| m8, #3.90: ε_k < 1.5 implicit | #3.90 adds ε_k ≤ 1 (#T3.27, small coupling). The middle term is then ≤ (1.53/0.8)ε_kη² < 2ε_kη², since η ≤ 1 |
| m9, #3.84: p.255 l.2–3 | #3.84 states that (3.20) (p.269 l.9) builds Λ_k at the step to the scale k, that p.269 l.14–16 only enlarges Λ_k^c, and that the 𝐑-operation with χ_{k,Λ} follows, so the case Λ_j = Ω_j of p.255 l.2–3 does not occur for j = k |

- Tags: #3.84's second half is now #3.84-0, #3.86's second half #3.86-0, and #3.86.1's last sentences #3.86.1-1, each split at a sentence. LF consumers cite #3.84-1 (#4.44-0.1) and #3.85–#3.85-1 (#0.1.41), whose content is unchanged.
- Re-derived: 1.25 + 0.2·1.4 = 1.53 and 1 − 4·(1/20) = 0.8, so 1.53/0.8 < 2. Also (L + 10) ≤ 4L + 4 for L ≥ 2, and 2α₁ = 4(d − 1)MR_k(1 + κ_s)ε_k ≥ 2(1 + κ_s)ε_k.
- Size: 7.41k to 9.50k characters, for the new derivations m1, m2, m5, m6, and m9. CR is 0, there are no trailing spaces or duplicate tags, and no line exceeds 600 characters. BP SHA is a2ed044a6797.
- Next: r2 (full).

Written 2026-11-09 05:36.

# Packet 12b-bp (balaban_proofs/BP_LFR2_CHI_K_LAMBDA.md), round 4, 9 Nov 2026

## Pre-check of bp-p12bbp-20261109-r4 (narrow)

- **Lines under review:** #3.85-1, #3.86-1, and #3.88–#3.90 (#3.88-1-1 included). These are r3's repaired lines (WILSON_IT1_LF_TRIAGE_P12BBP_R3_2026_11_09.md), with the consumer #3.89–#3.90 of the new form of #3.88. The rest of the file, reviewed CORRECT in r2 and r3, is context.
- **Every changed line re-read** on 9 Nov 2026 (BP 8f87e8c3ee33).
- **Re-derived:**
  - #3.86-1: the iteration runs on the k-blocks of □^{∼4} and of the layer around it (#3.86). #3.84-1.2 bounds U_{k,Z} on □^{∼4}. #3.84-1.1-1-1 gives U_{k,Z} the bounds of VAR (2) on Z's deepest domain, which contains the layer (#3.84-1, #3.86). Proposition 2 of CMP98 turns both into (1.7).
  - #3.88: with a := U₁(x,y)R(U₀(x,y))U₁(y,z), Y := U₀(∂p), and q := R(U₀(x,w))U₁(z,w)U₁(w,x), (a − 1)(Y − 1)q + (Y − 1)(q − 1) + (Y − 1) + (aq − 1) = aYq − 1. So P = a − 1, Q = q, and S = q − 1, and PXQ + XS + X = (1 + P)XQ, with 1 + P = a and Q = q products of unitary factors. Hence abs(X) = abs(W − 1 − E₂) ≤ abs(W − 1) + abs(E₂).
  - #3.88-1: (1.43) needs ∂_{U₀}U₁ = aq, which is (1.22) with U₁(y, z) as its third factor, the factor of (1.21); the print has U′(z, y) (transcription tnote at p.079). The line labels the reading inferred, not printed.
  - #3.88-1-1: the four linear remainders ≤ s²/2 each, six pairs ≤ s², four triples ≤ s³, and one quadruple ≤ s⁴ give 8s² + 4s³ + s⁴ ≤ 9τ²ε_kη² for s ≤ 1/20 and ε_k, η ≤ 1.
  - #3.89–#3.90: abs(W − 1) < (1 + κ_s)ε_kη² (#3.84-0), and 1 + 1/4 + 1/10 + 9/400 = 1.3725 < 2.
- **Grep of touched claims:** LF #3.83-1 uses only the bound < 2ε_kη² of #3.89. Table #T12.12 records B, W, X, α₁, and τ, unchanged. #3.88-1-1 is a new tag, unused elsewhere.
- **No known weak point** remains in the lines under review.
- **Definition check:** 0 conflicts (11 allowed). W, e^{iA_i}, and s now name #3.88-1-1 in their ranges, and W's entry names the table's #T12.22 weight as another object.
- **Size:** the reviewed lines are 2.32k characters (25k cap). The file is 10.95k. CR is 0, and there are no trailing spaces, duplicate tags, or lines over 600.
- **Spec:** specs\spec_p12bbp_r4.json (BP 8f87e8c3ee33, Cauchy 14ee33c357e1, LF 6ac728004094). The background adds REG (1.21).
- **Order:** after M8b r1. Rebuild at launch.

Written 2026-11-09 08:58.

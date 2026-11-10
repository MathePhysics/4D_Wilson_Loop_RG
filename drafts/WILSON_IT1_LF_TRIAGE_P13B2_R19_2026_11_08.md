# Triage of lf-p13b2-20261108-r19

## Verdict

- r19 was a full round of 13b2 at LF d8bf3d14487a, table 6d09b1b5054d, and labels 971e7d7d5325.
- **Fatal:** none. **Serious:** none.
- **Minor:** m1, the weight factor of the real-point density bound behind C_dc(M). It is repaired below.
- **Trivial:** t1–t5, exposition only, repaired below by rewording.
- r18's t1–t5 were confirmed repaired.
- The round is **not clean**, so 13b2's count returns to 0. The next round, r20, is narrow (count 1 if clean), then a full round (count 2).

## Repairs

| Finding | Line | Issue | Repair |
|---|---|---|---|
| m1 | #4.565, #4.565-0, #4.565-1 | (c)'s d_y is unweighted (Φ = A(U), #4.44; #4.51-0), so #4.565-0's ingredients give C_y(M)(ε/a_n)^{(1−ε₀)/3}ε₁′² with no g^{−2}; the disc bound (#4.563-3-1) and #4.568 use the weighted density | #4.565: the densities "weighted, as on the disc, by (g″)^{−2} ≤ 2g_{j(x)}^{−2} (#4.41-1-1), are ≤ 2C_y(M)g_{j(x)}^{−2}(…)ε₁′² (#4.565-0)"; #4.565-0: "this is the unweighted bound C_y(M)(…)ε₁′², …, and, both bounds being sums over the plaquettes of y, the weighted one is abs(w)_y times it (#4.48.0-3)"; #4.565-1: "the weighted abs(d_y) ≤ …", C_dc(M) := 2max(C_y(M), C_act) |
| t1 | #4.561.1-0, #4.561.1-1.3-1.1 | C_{V′} and ε₂ used before their defining lines, their tags not cited there | #4.561.1-0: "C_{V′}ε₁′ being ≥ 4c_avε′_k ≥ 4c_avC_cα̂₁ = 240c_avα̂₁ by C_{V′}'s first entry (#4.561.1-2) and ε₁′ ≥ ε′_k (#4.560.1-1)"; #4.561.1-1.3-1.1: "ε₂^{AL} ≤ ε₂/4, ε₂ of #4.561-1 (#4.561-1-2)" |
| t2 | #4.561.1-1 | B^e(z) ∈ 𝔤^c, needed by LFR II (1.40)–(1.41), unstated; for general compact G it does not follow from abs(W − 1) ≤ ½ alone | "and B^e(z) is 𝔤^c-valued, by continuity along the segment from 0, where it vanishes, since on abs(W − 1) ≤ ½ the principal logarithm inverts exp, which maps a neighbourhood of 0 in 𝔤^c onto one of 1 in G^c"; the bound now cites #4.561.1-0 |
| t3 | #4.517-1 | REG's threshold of (1.71) also constrains the base regularity α₀ | "That threshold is a smallness of α₀ + α₁, α₀ the base's regularity, here VAR's ε₀ ≤ ε₂/B₁ by (113) (p.294 l.44) and 0 at the base 1; its inputs CMP98 (130)–(131) hold …" |
| t4 | #4.563-2.1 | "plaquette variables" read on η-plaquettes, then used on a_j-plaquettes in #4.563-3-0 | "move by ≤ (2 + 8C₀^{ms}ε₁′ + 16ε₂)ε₂L^{−2j} ≤ 3ε₂L^{−2j} at the spacing η and, by the same computation with a_j abs(𝐇) < ε₂ and abs(U^r(∂p) − 1) ≤ 2C₀^{ms}ε₁′, by ≤ 3ε₂ at the spacing a_j = L^jη" |
| t5 | #4.517, #4.517-0, #4.517-1-1, #4.517-2 | u, R, and s overloaded | u: "not #4.536's gauge factors u"; R: "each conjugated, Y ↦ XYX^{−1}, by a transport X of the real base U₀" (the letter R dropped); s renamed s_u in #4.517-1-1 and #4.517-2 (the generic s of the monotonicity clause kept as a dummy variable) |

## Checks

- **m1.** #4.48.0-3 multiplies a sum over the plaquettes of y by abs(w)_y; b_y (#4.51-1.0) is likewise a sum of remainders over the coarse plaquettes with the initial point in y. The weight of the actions of U″_k is ≤ (g″)^{−2} ≤ (1 + 2b₂ḡ²)g_{j(y)}^{−2} ≤ 2g_{j(x)}^{−2} (#4.41-1-1, #4.54-0.1). The Lemma at z = i with M₁ = 2C_y(M)g^{−2}(ε/a_n)^{(1−ε₀)/3}ε₁′² and M₂ = 2C_actg^{−2}ε₁′² gives M₁^{15/16}M₂^{1/16} ≤ 2max(C_y(M), C_act)g^{−2}(ε/a_n)^{5(1−ε₀)/16}ε₁′². #4.568 uses C_dc(M) by name, unchanged.
- **t2.** The set of t ∈ [0, 1] with log W(tz) ∈ 𝔤^c is closed by continuity and open since exp restricted to 𝔤^c is a local diffeomorphism near its points of norm < log 2 onto a neighbourhood in G^c and the principal logarithm is injective on abs(W − 1) ≤ ½. It contains 0. abs(W − 1) ≤ c_avε′_k ≤ ⅛ on the whole disc (#4.561.1-0), which is star-shaped.
- **t3.** VAR p.294 l.44, (113): B₃ε₁ ≤ ε₀, B₁(ε₀ + C₁ε₁) ≤ ε₂, ε₂ ≤ ¼ε₃; so ε₀ ≤ ε₂/B₁.
- **t4.** On the layer j, a_j abs(𝐇) < ε₂ and a_j² abs(∇𝐇) < ε₂ (VAR (19) in VAR's units), and U^r's a_j-plaquettes have abs(U^r(∂p) − 1) ≤ 2C₀^{ms}ε₁′ (#4.48.0-0). The four-factor computation gives 2ε₂ + 4·2C₀^{ms}ε₁′ε₂ + 16ε₂² ≤ 3ε₂ under 8C₀^{ms}ε₁′ + 16ε₂ ≤ 1.
- **Symbols.** s_u is unused elsewhere in the LF, the table, and the Cauchy note. C_dc and C_y(M) occur in the LF only at #4.565–#4.565-1 and #4.568. Table row 466 states C_dc(M) := max(C_y(M), 2C_act) and is stale; the change is sent to the table's owner.
- **Line lengths.** #4.517 238, #4.517-0 584, #4.517-1 565, #4.517-1-1 178, #4.517-2 370, #4.561.1-0 333, #4.561.1-1 581, #4.561.1-1.3-1.1 222, #4.563-2.1 610, #4.565 554, #4.565-0 394, #4.565-1 271 characters. CR count 0.
- **Packet note.** r19's spec placed Lemma (Two Constants) in the Cauchy note's §8.6; it is LF #4.557–#4.558-1.1 (13b1, done). r20's spec says so.

## Pre-check of lf-p13b2-20261108-r20 (narrow)

- **Spec.** specs\spec_p13b2_r20.json, prior r19. Extracts as in r19. Named steps: the changed lines #4.517, #4.517-0, #4.517-1, #4.517-1-1, #4.517-2, #4.561.1-0, #4.561.1-1, #4.561.1-1.3-1.1, #4.563-2.1, #4.565, #4.565-0, #4.565-1, with their consumers #4.561.1-1.1 (B^e ∈ 𝔤^c), #4.563-3-0 (abs(Y − 1) ≤ 3ε₂ at a_j), #4.563-3-1, and #4.568 (C_dc(M)).
- **Changed since r19:** the twelve named lines above. Every one re-read in place after the edit.
- **Cited displays.** VAR (113) (p.294 l.44), #4.48.0-3, #4.41-1-1, #4.54-0.1 re-read; #4.561.1-0's bound on D(z)D(0)^{−1} re-read for t2.
- **Size.** Built at LF 179f5fa14433: argument 24,554 characters (r19: 23,622; growth from the t2–t4 rewordings and the m1 weight clause), 28 files. The gate's 12 changed tags are the 12 named lines above.
- **Relabel.** Pending with the table fork, as for r17–r19; the spec tells the referee to locate tags by searching the LF.
- No known weak point and no OPEN is in the part.

## SHAs

LF d8bf3d14487a (r19's snapshot) → 179f5fa14433 (m1, t1–t5). Table 6d09b1b5054d and labels 971e7d7d5325 (unchanged; relabel and rows 326, 464, 466, #T12.9-1, #T11.33 pending with the table fork).

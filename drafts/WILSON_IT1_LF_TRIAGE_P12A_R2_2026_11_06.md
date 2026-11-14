# Packet 12a r2 Triage (LF #1.2, #3.16–#3.62-1)

## The Report of r2

r2 (lf-p12a-20261106-r2, launched 16:15 under .claude-Main) found no fatal finding, no serious finding, and six minor ones. The first round's S1 is repaired. So r2 is not clean, and r3 is a full round. Each finding was re-derived against the print and repaired in place.

| Finding | Item | Repair |
|---|---|---|
| n1 | #3.26-2 | The plaquette difference is written as the ordered product of e^{iεAd(P_{<b})A′*_b} with the partial transports of MU^B. VAR's ∇ is covariant at U₀ = MU^B (VAR p.281 l.7, #5.18), and the transports differ from its own by the closing plaquette, ≤ B₃ε₁ (VAR (8)). The bound is now a_i²∣∇A′*∣ + C(a_i∣A′*∣)² + C(a_i∣A′*∣)B₃ε₁ ≤ 3ρ̄(x), split into #3.26-2-1. |
| n2 | #3.26-5 | The data bound now comes from the plaquettes of U^A_{k,Z} below (1 + 2κ_s)t(η^A)², through CMP 98 Proposition 2 (p.26, (54)), as in #1.4; the converse citation p.193 l.20 is gone. #3.26-4 chooses σ with f^A + σt < (1 + 2κ_s)t. The exchange step reads f^A ≤ f^B + δ^f_kt^B ≤ f^B + (3/2)δ^f_kt, with the 3/2 absorbed in C. |
| n3 | #3.19.1, #3.26-2 | For j ≤ k₀ the thresholds are "inferred, not printed, from (1.22), (1.23), and the remark for j ≤ k₀ at p.191 l.30–31"; #3.26-2 sets l = 0 there. |
| n4 | #1.2-1 | "There" is replaced: the A_j on Z_{j+1} ∩ Ω_{j+1} ∩ X lie in Ω_{j+1} ⊂ Ω_{j₀}. |
| n5 | #3.38–#3.39 | At the scale j a cube carries the tests of the CRE step j and of the 𝐑-operations of the steps k′ ≥ j with k′ − N̄(K − k′) ≤ j, on disjoint components (LFR I (1.1)), so of at most s_T(j) := 2 + N̄(K − j) steps (#3.38-1). The common depth N := N̄(K − j), N̄(n) := ⌈(log(ḡ^{−2} + bn))^ν⌉, is fixed in the Cauchy note's #CP.13–#CP.14 like R̄, so matched 𝐑-operations have the same N and κ_c (#3.39). The contribution to C_h is (2Cn_T + 32C(1 + j(C)))θ̃^{−1}c_{hs}/κ_s with c_{hs} := sup_j(j + 1)s_T(j)L^{−(3−7ε₀)j/4}, finite since s_T(j) is polylogarithmic in j (#3.39-1). #4.249 cites the common N. |
| n6 | #3.19.1 | Each tested plaquette is assigned to the LM₂R_i-cube containing it, i the scale of its threshold; any assignment gives the same sharp test (#3.19.1-1). |

## Pre-check for r3

I read every line of #1.2–#1.2-1 and #3.16–#3.62-1 as they now stand.

- The count of #3.38-1: N̄ is nondecreasing, so for k′ ≥ j, k′ ≤ j + N̄(K − k′) ≤ j + N̄(K − j). That gives at most N̄(K − j) + 1 𝐑-operations plus the CRE step.
- The bound s_T(j) ≤ 3 + (2log(ḡ^{−2} + C + 8b′(1 + j(C))(j + 1)))^ν follows from #CP.14 and #3.30.
- The exponent split: (1 − ε₀)/4 + (3 − 7ε₀)/4 = 1 − 2ε₀.
- The per-step factor: n_T + 2·8(1 + j(C))(j + 1) ≤ (n_T + 16(1 + j(C)))(j + 1).
- One repair: #3.39-1 named c_{hs}'s dependence as "L, ε₀, ḡ, ν, and j(C) only". It also depends on Lemma 2.1(i)'s b′ = 2c ln L + δ′ and C = C₀, which are now named.

The lines #3.19.1, #3.26-2, #3.38, and #3.39 exceeded ~600 characters. They were split at sentence boundaries into #3.19.1-1, #3.26-2-1, #3.38-1, and #3.39-1, with no change of wording. The citations "#3.26-2 applies" (#3.26-5) and "the s_T(j) steps of #3.38" (#3.39-1) now name the sub-lines.

The definition check passed for spec_p12a_r3.json: 0 conflicts, 1 allowed (N). s_T(j), n_T, and c_hs are each defined once.

## Files

r2: LF 98afdbda7e48, labels 5b9158c1de9a, table 88a6dcbd277a. r3: LF ad44c62ee742, labels 2bcd7b0b486a, table 88a6dcbd277a; Cauchy note 9250f39dd504.

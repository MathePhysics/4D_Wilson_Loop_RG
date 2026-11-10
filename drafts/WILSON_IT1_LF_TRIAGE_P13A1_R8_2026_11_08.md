# Triage of lf-p13a1-20261108-r8 (focused round of part 13a1)

## Verdict

- r8 was a focused round of 13a1 at LF c47aebb08b0d, table 6d09b1b5054d, and LABELS 971e7d7d5325. The LABELS file was stale (the fork had not relabelled); the spec said so, and the referee located tags in the LF text.
- **Fatal:** none. **Serious:** none.
- **Minor:** one, m1: the norms of ‖Y‖_∞ and ‖Y‖₂.
- **Trivial:** four, t1–t4.
- The round is not clean.
- The referee confirmed round 7's r1 and r2 repaired. r3 needs no change in this part.

## Repairs

| Finding | Line | Issue | Repair |
|---|---|---|---|
| m1 | #4.44-2, #4.46-0 and consumers | #4.44-2 defined ‖Y‖_∞ and ‖Y‖₂ in the normalised-trace norm, but ‖·‖_y and Bałaban's bounds ((3.133), VAR (103), (172)) are in the operator norm abs(·) of #T6.23, so #4.46-0's bound lacked √N | ‖Y‖_∞ := max_b abs(Y(b)) is now in the operator norm, and ‖Y‖₂ := (Σ_b‖Y(b)‖²)^{1/2} in the normalised-trace norm, the L² norm of LFR II (1.7)–(1.9) (both #T6.23), so ‖Y‖_∞ ≤ √N‖Y‖₂. #4.46-0, #4.46-1, #4.47-1, #4.47-2, #4.50, #4.51-1.1, #4.51-2, #4.53-1.1, #4.162, and #4.560-1.1.2 are then correct as written. N enters where the two norms meet: #4.48-2 (NC_Φ(M)), #4.48-3.1 (C_{1−ζ₀}(M) gains N), #4.49 (the range 2C₁κ_Λε₁/(NC_Φ(M))), #4.50-0 (C₁ := max(1, NC_𝔛(M)C_Φ(M)/κ_Λ)), #4.51-2.1 (C_{dΛ} := 8√NC_bdB₀, by ‖𝔛‖_∞ ≤ √NΔ), and #4.51-3 (C_Δ(M) gains √N and now bounds both Δ and ‖𝔛‖_∞). The uses of "‖𝔛‖_∞ ≤ Δ" in #4.53, #4.53-1.2, #4.54-1, #4.55, #4.154, and #4.179 now cite #4.51-3's bound on ‖𝔛‖_∞ directly, so C′_Δ(M), C_A(M), and C_E(M) keep their formulas |
| t1 | #4.44-1 | V′ meant LFR II's fluctuation and the note's data | LFR II's fluctuation is written W′ in this line: "its fluctuation V′ written W′ here, is U_{k,Z}(W′V′₀V_{Λ^c}), the note's V′ being W′V′₀" |
| t2 | #4.48.0-2.1 | §9.6's coefficients also contain the plaquette variables | The sentence now names both: "coefficients polynomial in the transports and in the plaquette variables U(∂p) − 1 … #4.41-3-1 bounds the transports as unitary, and at U_t the plaquette variables are bounded by #4.48.0-2's curvature condition" |
| t3 | #4.50-1.0, #4.50-1.1.0 | #4.50-1.0 restated #4.48.0's conditions; "2ε₁ ≤ a₁ in VAR Theorem 1" read as printed; the conditions were not assigned to their uses | #4.50-1.0 now cites "#4.48.0's three conditions at ε_r = ε₁ and abs(ℋ)_y < 2C_ℋC₁ε₁". #4.50-1.1.0 reads "VAR Theorem 1's ε₁ ≤ a₁ … at the regularity 2ε₁, for #4.46-2 at the configurations of *The comparison.*'s segment (#4.51-2); #4.48.0's conditions at ε_r = 2ε₁ and at the field A′*, for that section (#4.51-1, #4.51-2.1)" |
| t4 | #4.50-1.1.0-0, #4.53-1, #4.50-2 | α₁ named CMP 98 (158)'s constant and PBG's; "2C_U(M)ε₁ ≤ α₁ of its (I)" read as stated in (I) | CMP 98's is now {#D.α₁^CMP} α₁^{CMP} (not PBG's α₁), also in #4.53-1. #4.50-2 now says "2C_U(M)ε₁ ≤ α₁, which its (I) needs to use *The multipliers.* at every t ∈ [0, 1]" |

## Re-derivation of m1

- **Norms.**
  - CMP 98 (18) defines ‖X‖² = tr X*X with the normalised trace, and (19) the operator norm abs(X).
  - (20) gives ‖X‖ ≤ abs(X) ≤ √N‖X‖.
  - LFR II (1.7) and (1.9) are written with ‖B′‖² and ‖∂B′‖², the L² norm of (18) (p.358 l.3–22). So κ_Λ of #4.45-1 is a bound in ‖Y‖₂, which stays in the trace norm.
- **Operator-norm side.**
  - (3.133), VAR (103), (172), and #T11.26's (24)–(25) are bounds in abs(·), as are ‖·‖_y (#4.30-1) and |ℋ|_y.
  - With ‖Y‖_∞ in abs(·), #4.46-0 holds as written: a_j abs(H₁Y) ≤ B₀Σ_be^{−δ₀d(y,b)}abs(Y(b)) ≤ B₀K_Λ(y)‖Y‖_∞.
  - #4.46-1's abs(e^{iY(b)} − 1) ≤ abs(Y(b)) < 2C₁ε₁ also holds as written.
- **Where the two meet.**
  - Schwarz (#4.48-2): (‖Y‖_∞/(2C₁ε₁))³C_ΦC₁²ε₁² = (C_Φ/(8C₁ε₁))‖Y‖_∞·‖Y‖_∞² ≤ (NC_Φ/(8C₁ε₁))‖Y‖_∞‖Y‖₂².
  - #4.48-3.1: ‖Y‖_∞² ≤ N‖Y‖₂².
  - The growth (#4.49) is ≥ (κ_Λ/4)‖Y‖₂² once (NC_Φ/(8C₁ε₁))‖Y‖_∞ ≤ κ_Λ/4, that is ‖Y‖_∞ ≤ 2C₁κ_Λε₁/(NC_Φ).
  - At Y = ±𝔛 this needs C₁ ≥ NC_𝔛C_Φ/κ_Λ, since ‖𝔛‖_∞ ≤ C_𝔛ε_k ≤ C_𝔛ε₁ (#4.50, operator norm).
  - C₁ is defined after C_Φ and C_{1−ζ₀}, which do not involve C₁ (C_ℋ is independent of C₁, #4.47-2). So nothing is circular.
- **The comparison.**
  - #4.51-2.1: the t-derivative of each term is ≤ 2C_bdε₁·2B₀K̃_Λ(y)‖𝔛‖_∞. With ‖𝔛‖_∞ ≤ √NΔ, the two terms give 8√NC_bdB₀ε₁K̃_Λ(y)Δ.
  - #4.51-3's algebra is unchanged and gives Δ ≤ C°(ε/a_n)^{(1−ε₀)/3}ε₁, with C° := (2N_blc′_Λ/κ_Λ)^{2/3}(2C_σC_{dΛ})^{1/3}.
  - So Δ and ‖𝔛‖_∞ ≤ √NΔ are both ≤ √NC° = C_Δ(M).
- **Consumers.** #4.53-1.2, #4.54-1, #4.55, #4.154, #4.162 (s_n), #4.179, and #4.189 use C_Δ(M) as a bound on the operator-norm data difference ‖𝔛‖_∞, which it now is. Their formulas are unchanged.
- **Uniformity.** N is fixed by the faithful representation G ⊂ U(N) (#T10.18), so every uniformity and threshold claim stands. C₁′ still depends only on d, L, G, M, and C₀^{ms} (#4.50-1).

## Rounds

The user asked for one focused check each on 13a. So 13a1's repaired lines go under review in 13a2's focused round r10, as #4.50-1.1.0 went into 13a2 r9. They are #4.44-1, #4.44-2, #4.48.0-2.1, #4.48-2, #4.48-3.1, #4.49, #4.50-0, #4.50-1.0, #4.50-1.1.0, #4.50-1.1.0-0, and #4.50-2. 13a2 r10's spec adds them, and adds #4.53, #4.53-1.2, and #4.55, which the repair changed in 13a2. #4.154 and #4.179 are §4(d) and wait for their own packet.

## Checks

- No duplicate tags. No CRLF.
- Edited lines ≤ 600 characters, except #4.179 (1,123). It was over-long before this repair, which shortened it. It is §4(d)'s, left for its packet.
- New D-tag {#D.α₁^CMP}. Table rows requested from the fork: ‖Y‖_∞ and ‖Y‖₂ (#T12.9 restates them in the old norm), C_{1−ζ₀}(M), C₁, C_{dΛ}, C_Δ(M), α₁^{CMP}.

## Pre-check of lf-p13a2-20261108-r10 (updated for these repairs)

- The gate's changed tags for r10 (27, since 13a2 r9's snapshot) are all in extracts under review. This was checked by script: no tag is left out, and no line appears twice.
- They are 13a1's #4.44-1, #4.44-2, #4.48.0-2.1, #4.48-2, #4.48-3.1, #4.49, #4.50-0, #4.50-1.0, #4.50-1.1.0, #4.50-1.1.0-0, and #4.50-2, and 13a2's #4.51-2–#4.51-3, #4.52-1, #4.53–#4.53-1.2, #4.54-0.0, #4.54-0.0-1, and #4.54-1–#4.55-1-1.
- Each changed line was re-read after the edit:
  - the norms against CMP 98 (18)–(20) and LFR II p.358;
  - the N and √N factors as re-derived above;
  - #4.53-1.2's C′_Δ(M) = (1 + (π/2)c_vdB₀c_tot(1/128))C_Δ(M) + c_vc_{A′}, which bounds the first sentence's ‖𝔛‖_∞, the first bracket, and the second bracket;
  - #4.55's C_A(M) = C_prc_K((π/2)C′_Δ(M) + C_Δ(M)), with #4.54-1's ‖𝔛‖_∞ ≤ C_Δ(M)(ε/a_n)^{(1−ε₀)/3}ε₁.
- --check gives 0 conflicts (7 allowed). Earlier pre-check items stand (WILSON_IT1_LF_TRIAGE_P13B_R8_2026_11_08.md).
- The labels file is still stale, because the fork has not relabelled. The spec says so.

## SHAs

LF c47aebb08b0d → 3b7b6d176dd2.

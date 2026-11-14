# Triage of lf-p13b-20261108-r8, and the consolidation of packet 13

## Verdict

- r8 was a full round of 13b at LF 07065b0520af, table e5a1131811bf, and LABELS 6a37a08d8be1.
- **Fatal:** none. **Serious:** none.
- **Minor:** one, m1: run B's U″_k data under run A's ū₀.
- **Observations:** five, o1–o5.
- The round is not clean, so 13b's clean count stays 0.
- Round 5's m1–m3 and o2, o5, o6, and o7 were confirmed repaired.

## Repairs

| Finding | Line | Issue | Repair |
|---|---|---|---|
| m1 | #4.561.1-1.3-0, #4.52-1 | Run B's datum carries run A's ū₀ (#4.52-1), so the bound needs a common gauge of U_0 in which (1.84) holds for both runs; #4.52-1 named the gauge only as "that of the comparison of the Cauchy note's §9.8", which names none | #4.52-1 now names the gauge: LFR I's axial gauge in k-blocks inside Λ (#T11.29-2), each run's own gauge of U_0, in which (1.84) holds (#4.561.1-1.2-1). #4.561.1-1.3-0 states that run B's datum (M^·U^B_0(z))^{ū₀^A(z)} obeys #4.561.1-1.3-2's bound with the same constants, abs(log ū₀^A) being bounded by #4.561.1-1.3-1.1. I checked #C9.8.14's block-axial gauge first: it belongs to the one-step lift ι, not to U_0, so it is not cited |
| o1 | #4.561 | (T-Λ) at 26ε₁′ is stronger than needed | No change. (T-c) is used on the disc at abs(z) < 25 with 26 for 25 (#4.505), and a stronger valid condition costs nothing |
| o2 | #4.561-1-2 | "monotone in ε₂" did not cover the base-1 thresholds written through C₁ε₁ | Rewritten in place: the thresholds through VAR's ε₀ and C₁ε₁, Proposition 2's ε₀ + C₁ε₁ ≤ c₁ (#T11.25) and (172)'s smallness, hold at the base 1, since ε₀ = 0 and C_{AL}ε′_k ≤ ¼C_{V′}ε₁′ |
| o3 | #4.561.1-1.3-0 | "the choice does not matter" at complex points needs an analytic alternative | The sentence now takes the alternative ū₀ as a function of V_k analytic on the line, so the identity theorem carries the invariance to the disc |
| o4 | #4.561.1-1.3-1 | VAR assumes C₁ absolute (p.305 l.44), while C_{AL} depends on M | The line now says C_{AL} depends on M as C₁′ does in #4.46-1.1, where the deviation is handled |
| o5 | #4.565, #4.565-0 | d̄^c and d̄_c(x) look alike | d̄^c is renamed d_{al} ({#D.d_al}); table row requested |

## The consolidation of packet 13

The user asked for packet 13 as a whole (13a1, 13a2, 13b) to be consolidated in its text, not its bookkeeping. Each fact argued in more than one place is now stated once and cited.

**The two runs' couplings (13a1, 13a2).**
- #4.50-1.1.1-1 now holds the run convention: g_k and g_j are those of the run with the larger ε_k, the runs' g_j^{−2} differ by a factor ≤ 2 at every j, and both couplings are ≤ (1 + β₀)γ.
- #4.50-1.1.0-1 and #4.55-0.1.1 restated these facts. They now cite #4.50-1.1.1-1.

**Uniformity of (T-Λ) (13a1).**
- The uniformity in k and K was argued three times, in #4.50-1.0, #4.50-1.1.1, and #4.50-1.2.
- It is now one argument, in #4.50-1.2. Every condition but the two exceptions is cε₁ ≤ c′, and ε₁ is g_k times a power of log g_k^{−2}.
- 13b's #4.562-1.1 restated the same argument for (T-c). It now cites #4.50-1.2 and adds only c_{rp}M⁶R_kε′_k ≤ M⁶ε₁′.

**H₁Y and K_Λ (13a1, 13a2).**
- The (3.133) bound on H₁Y with its count was derived in both #4.46-0 and #4.47-1.
- K_Λ(y) was defined only in #4.51-2, after its first use.
- #4.46-0 now defines K_Λ(y) and states ‖H₁Y‖_y ≤ 2B₀K_Λ(y)‖Y‖_∞ and K_Λ(y) ≤ dc_tot(1/128). #4.47-1, #4.51-2, and #4.53-1.1 cite it.

**N_Λ (13a1).**
- 2d(100M + 1)^d, the bound on the bonds that meet Λ, was written out in both #4.48.1 and #4.48-3.0.3.
- N_Λ is now defined once, in #4.48.1, and c′_Λ := N_Λc_tot(1/16).

**Φ (13a1).** Both #4.44 and #4.44-1 said that V′₀ minimises Φ. Φ is now defined in #4.44, and #4.44-1 keeps only the identifications with LFR I and LFR II.

**Absorption (13a2, 13b).**
- #4.55-1 and #4.568 each did the absorption into θ̃^n.
- The new #4.55-1-1 does it once, for any exponent s > ¼: L^{−s(1−ε₀)n} ≤ θ̃^nL^{−(s−¼)(1−ε₀)n}. It is used at s = ⅓ in (c) and cited at s = 5/16 by #4.568.

**The real points (13b).**
- "the O(1) of #4.560-1" appeared six times. It is now the constant c_{rp}, defined once at #4.560.1, and #4.43-1.2 lists the lower bounds on C(M) through it.
- ε′_k ≤ ε₁′ was argued in four places. The new #4.560.1-1 states ε₁′ ≥ 4ε′_k and ε₁′ ≥ c_{rp}ε′_k once, and #4.561-1-2, #4.563-1.1, and #4.567-1 cite it.
- #4.560-1 no longer restates #4.559-1 (U_0 as the minimiser of (1.3)), and #4.560-1.1 no longer restates #4.559-1.1 (#T6.11's replacement).
- #4.560-1 and #4.560-1.1.1 called U_0's field "A₀", which clashes with the constant A₀ of p₀(g). It is now 𝔸_Z, as in #4.43-1.
- #4.556-1's pointer to "The room at complex points" is deleted, since #4.559-2 says the same.

**Sizes** (characters of the tagged lines):
- 13a1: 20,710 → 20,530.
- 13a2: 12,489 → 12,353.
- 13b: 22,360 → 22,240.

The savings are small. Most of 13 consists of distinct derivations, and the m1, o2, and o4 repairs added text.

**Checks.**
- No duplicate tags and no duplicate D-tags.
- No CRLF.
- Every new or edited line is ≤ 600 characters.
- #4.55-1 (635) was split at a sentence into #4.55-1-1.
- The over-long lines left are #4.560 (608), #4.43-1.1 (604), and #4.54-0.1.2 (617). I did not edit them this round.

## Rounds

The consolidation changes text in all three parts. The user asked for one focused round each of 13a1 and 13a2 (lf-p13a1-20261108-r8, lf-p13a2-20261108-r10), then 13b r9, a full round. They run one at a time.

## Pre-check of lf-p13a1-20261108-r8 and lf-p13a2-20261108-r10

**Scope.** Each spec puts under review every tag that changed since its part's last snapshot (the gate's list), with their consumers in the part. The rest of the part is context. A script confirmed that the extracts cover each part contiguously, with no line twice and no changed tag left out.
- 13a1 (since r7): #4.43-1.2, #4.44, #4.44-1, #4.44-2, #4.46-0, #4.47-1, #4.48.0, #4.48.0-2.1, #4.48.1, #4.48-3.0.3, #4.50-1.0, #4.50-1.1.0, #4.50-1.1.0-0, #4.50-1.1.0-1, #4.50-1.1.1, #4.50-1.1.1-1, #4.50-1.2, #4.50-2. Consumers under review: #4.47-0, #4.48.0-0–#4.48.0-3, #4.48.1-1, #4.48-1, #4.48-3.1.
- 13a2 (since r9): #4.51-2, #4.52-1, #4.53-1, #4.53-1.1, #4.53-1.1-1, #4.54-0.0, #4.54-0.0-1, #4.55-0.1.1, #4.55-1, #4.55-1-1. Consumers under review: #4.51-2.1, #4.51-3, #4.52-1.1, #4.53-1.0, #4.54-1.
- Besides the consolidation, these lists contain the earlier trivial repairs, which no round has seen yet. They are 13a1 r7's r1–r2 (#4.44-2, #4.48.0, #4.48.0-2.1), 13a2 r9's t1–t3 (#4.53-1, #4.54-0.0-1, #4.50-1.1.0-0), and #4.50-2's C₀^{ms}.

**Repairs found in the pre-check.**
- #4.51-2 cited #4.46-0 for ‖H₁𝔛‖_{y′} ≤ 2B₀K_Λ(y′)‖𝔛‖_∞. But #4.46-0's H₁ is the one at U_0, while #4.51-2's is at the segment's configurations, which are regular with 2ε₁. It now reads "by (3.133) at that configuration, as in #4.46-0". PBG's hypotheses at regularity 2ε₁ are in (T-Λ) (#4.50-1.1.0).
- #4.53-1.1 needs the single-term bound a_k|H₁𝔛| ≤ B₀K_Λ‖𝔛‖_∞. #4.51-2's ‖·‖_y bound would give a factor 2 more. So it now cites "(3.133) at the configurations of the segment, as in #4.46-0".
- #4.53-1.1 had grown to 721 characters. It is split at "In the second," into #4.53-1.1-1, one sentence per bracket. Nothing cites #4.53-1.1.
- #4.55-1-1 required C_h to dominate the sup only at s = ⅓, but #4.568 uses it at s = 5/16, where the sup is larger. C_h is a single constant chosen last (#4.622). The line now says "at each s used (s = ⅓ here, s = 5/16 in #4.568)". Found while reading 13b in full for r9.

**Re-derivations** (each changed line re-read against its source):
- #4.46-0. (3.133) bounds a_j|H₁Y| and a_j²|∇H₁Y| by B₀K_Λ(y)‖Y‖_∞. So ‖H₁Y‖_y ≤ 2B₀K_Λ(y)‖Y‖_∞. On P, |H₁Y|_{(−1)} ≤ B₀dc_tot(1/128)·2C₁ε₁ ≤ 2dLB₀C₁′ε₁, since C₁′ = 4c_tot(1/128)C₁.
- #4.47-1. For b ∈ Λ, w_Λ(y) ≤ e^{(δ₀/16)d(y,b)}, so the sum runs at the rate (15/16)δ₀ ≥ δ₀/128. This gives 2dB₀c_tot(1/128).
- #4.48.1. Σ_ye^{−(δ₀/16)d(y,Λ)} ≤ Σ_{b∈Λ}Σ_ye^{−(δ₀/16)d(y,b)} ≤ N_Λc_tot(1/16).
- #4.51-3. c′_Λ ≥ Σ_bΣ_{y′}e^{−(δ₀/2)d(y′,b)} ≥ Σ_{y′}K_Λ(y′)^{1/2}, since (Σ_bx_b)^{1/2} ≤ Σ_bx_b^{1/2}.
- #4.48-3.0.3. Each y′ is counted for at most N_bl blocks y, and ‖Y‖_∞ < 2C₁ε₁. The count at δ₀/32 gives c_tot(1/32) ≤ c_tot(1/128), since c_tot decreases in α. Hence the factor 2C_bd(1 + 2C_ℋ)C_ℋN_blN_Λc_tot(1/128)C₁²ε₁².
- #4.48-3.1. Cauchy's estimate at radius 2C₁ε₁/‖Y‖_∞ gives twice the coefficient ≤ 2·change·‖Y‖_∞²/(2C₁ε₁)² = C_{1−ζ₀}(M)e^{−(δ₀/8)MR_k}‖Y‖_∞².
- #4.48.0-2.1. In the operator norm of #T6.23, abs(e^{itηℋ(b)}) ≤ e^{η·abs(ℋ(b))} ≤ e^{abs(ℋ)_y} ≤ 2^{1/8}, using a_j ≥ η (#4.48.0-1's (a_j/η)⁴ plaquettes) and abs(ℋ)_y ≤ (log 2)/8. A monomial with at most n_tr factors is then at most 2^{n_tr/8} times its unitary bound.
- #4.50-1.1.0-1. g_k ≤ (1 + β₀)γ (#C5.7-5), so (1 + β₀)g_k ≤ (1 + β₀)²γ < e^{−p₀}.
- #4.50-1.1.1-1. The other run's g^{−2} is ≤ 2g_k^{−2}, so with log 2 ≤ log g_k^{−2} its log is ≤ 2log g_k^{−2}. The larger R_k is then ≤ 2^{r+1}L·2^r(log g_k^{−2})^r. With ε_k = A₀g_k(log g_k^{−2})^{p₀}, this gives M⁶R_kε_k ≤ 2^{2r+1}LA₀M⁶g_k(log g_k^{−2})^{p₀+r}. For f(g) = g(log g^{−2})^s, f′ = (log g^{−2})^{s−1}(log g^{−2} − 2s) > 0 for g < e^{−s}.
- #4.50-1.2. ε₁ = C(M)R_kε_k obeys the same bound without M⁶. Every condition but the two named exceptions is cε₁ ≤ c′, so it holds for γ small, uniformly in k and K.
- #4.52-1. #T11.29-2 (LFR I p.197 l.9–14) takes U_0 in the axial gauge in k-blocks inside Λ, where (1.84) holds for M^j(U_0) at every scale j. This is the gauge at the shared centres.
- #4.55-1-1. L^{−s(1−ε₀)n} = L^{−¼(1−ε₀)n}L^{−(s−¼)(1−ε₀)n} ≤ θ̃^nL^{−(s−¼)(1−ε₀)n}. The polylogarithmic-times-linear factor times L^{−(s−¼)(1−ε₀)n} is bounded in n for s > ¼. At s = ⅓, (ε/a_n)^{(1−ε₀)/3} = L^{−(1−ε₀)n/3}.
- #4.53-1, #4.54-0.0-1. Re-read against 13a2 r9's re-derivations (t1, t2). Neither content nor constants changed.

**Other checks.**
- Symbols: no new symbol. c_{rp}, N_Λ, K_Λ, and Φ are in the rows requested from the table fork. --check gives 0 conflicts (7 allowed) for both specs.
- Sizes (tagged lines): 13a1 20,322 and 13a2 12,379 characters, both under 25k.
- No CRLF and no duplicate tags.
- No known weak point and no OPEN is in these lines.

**SHAs.** LF 7823314fe441 → 9f58d594709d (the two citations and the split of #4.53-1.1) → c47aebb08b0d (#4.55-1-1's C_h). The build waits for the fork's relabel at c47aebb08b0d and the rows requested above.

## Pre-check of lf-p13b-20261108-r9 (a full round)

- I read the whole of 13b (#4.556–#4.565-1, #4.567, #4.568) for gaps. Re-derived:
  - the Lemma: Re 𝔥 on D₊, the factor ((𝔳² − z²)/(4𝔳²))^η, and (4/π)arcsin(1/24) ≈ 0.0531 < 1/16;
  - the real points at 25 and 26 times the class bounds, with abs(A′_R) ≤ abs(A′) because A′_R = (A′ + A′*)/2 in the operator norm;
  - #4.561.1-0's e^{27c_avα̂₁} − 1 ≤ 54c_avα̂₁ ≤ c_avε′_k, with C_c = 60;
  - C_{V′}'s three entries;
  - #4.561.1-1.2-1's C_{AL}, with M^j(U_0(0)) unitary and c₈₄ = c_{rp} times (1.84)'s O(1);
  - #4.561.1-1.3-2's bound 2(1 + 48c_GdB₁B₃)C_{AL}ε′_k, using e^t − 1 ≤ 2t for t ≤ ½;
  - #4.561-1-2's base-1 thresholds through ε₂^{AL} ≤ ε₂/4 and C_{AL}ε′_k ≤ ¼C_{V′}ε₁′;
  - #4.563-1.1's 20C_{V′}ε₁′;
  - c_pl and C_act;
  - #4.565-1's exponent (15/16)(1/3) = 5/16;
  - #4.567-1's radius, (9/16 + ¼)C_{V′}ε₁′ < C_{V′}ε₁′.
- ε₁″ of #4.560.1 is used in #4.290-1.
- The only weak point found was C_h at s = 5/16, repaired in #4.55-1-1 above. The changed tags of 13b are all in the full round.
- spec_p13b_r9.json: --check gives 0 conflicts (6 allowed). 13b is 22,240 characters, under 25k.

## SHAs

- LF 07065b0520af → c6924224635c (the tags restored in place of "below", logged in the r5 triage file) → 7823314fe441.
- Table 6d09b1b5054d (the fork's forward-tag restorations). The rows requested above are pending.

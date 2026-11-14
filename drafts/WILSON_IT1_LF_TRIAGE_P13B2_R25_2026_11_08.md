# Triage of lf-p13b2-20261108-r25

## Verdict

- r25 was the full round of 13b2, at LF a8968717c318, table 6d09b1b5054d, and labels 971e7d7d5325.
- **Fatal:** none. **Serious:** none.
- **Minor:** m1, in #4.567–#4.567-1. The real *The couplings.* (#4.168) lists four routes of the coupling differences. The class treatment stated bounds for the weights and the data exp(ig_kB) only. The form ½⟨DH″B, ζDH″B⟩ depends on the couplings through its background U^0_{k,Z}, and that route had no class bound.
- **Trivial:** t1–t6.
- r24's t1–t5 were confirmed repaired. Every other named step was re-derived CORRECT, including the C_{V′} accounting, the u bound, the density bounds, the Lemma, and both stated coupling routes.
- The round is **not clean**, so the count returns to 0. The next round, r26, is narrow.

## Repairs

| Finding | Line | Issue | Repair |
|---|---|---|---|
| m1 | new #4.567-2, #4.567-2-1 | No class bound for the form's background route | #4.567-2: a data derivative times abs(g^A_k − g^B_k)abs(B) ≤ g_k²abs(δ_k)δ′_k; Cauchy with #4.567-1's radius and the forms ≤ c_4N_k per point of 𝐁₀ (#4.563-2.2 on the whole domain by #4.567-0) gives 4e^{1/4}c_4N_kg_k²δ′_k abs(δ_k)/(C_{V′}ε₁′). #4.567-2-1: N_kg_k² = 2d²(2B₀c_K(1 + 2dL))²(g_kb_k)² (#4.110) and 25g_kb_k ≤ ε′_k ≤ ε₁′/4 (#4.560-0, #4.560.1-1) give ≤ (2dB₀c_K(1 + 2dL))²c_4ε₁′δ′_k abs(δ_k), the data route's form |
| t1 | #4.563-3 | Whose g_{j(x)} in the weighted clause, for run B | "g″ and g_{j(x)} run A's in both runs (#4.41-0, #4.41-1-1)" |
| t2 | #4.564, #4.568 | "#4.568 absorbs them" included #4.567's bounds, which carry no (ε/a_n)^s | #4.564: "Cauchy's estimate those of #4.567–#4.567-2-1; #4.568 absorbs the first two, and the last keep the real form and are absorbed as the real coupling terms are"; #4.568: "the changes of #4.565-1 and #4.566" |
| t3 | #4.567-1 | The set of points of the per-point Cauchy bound unnamed | "Both bounds are per point of the support of the action's weight, which lies in Z (#4.160)" |
| t4 | #4.561.1-1.1 | γ₀ unqualified | "γ₀ LFR II's positivity constant (p.358 l.4), not RG I's (#T3.14)"; the other reused names (VAR's ε₀, LFR I Proposition 1's ε, the pair class's α₁) are already qualified where used |
| t5 | #4.561.1-1-0 | V^e(tz) ∈ G^c unstated | "V^e(tz) being in G^c as the averages V_k(tz) of the G^c-valued 𝐔(tz) are" |
| t6 | #4.563-2.1 | "the same computation … at the spacing a_j" presupposed links at a_j, whereas VAR's plaquettes are at η | "≤ 3ε₂L^{−2j} at the spacing η, in each run's own layers, so the field strength moves by ≤ 3ε₂/a_j², which is ≤ 3ε₂ in the units of a_j = L^jη in which (b)'s plaquette bounds are read" |

## Checks

- **m1, re-derived.**
  - The move in the exponent is X = (g^A_k − g^B_k)B, with abs(X) ≤ g_k²abs(δ_k)δ′_k on the support of χ′ (#4.168).
  - The derivative along X is ≤ sup/r times abs(X), with r ≥ e^{−1/4}½C_{V′}ε₁′ (#4.567-1), so it is ≤ 2e^{1/4}c_4N_k abs(X)/(C_{V′}ε₁′) per point. The line's 4e^{1/4} covers a finite difference as well: abs(f(1) − f(0)) ≤ 2S abs(X)/r for abs(X) ≤ r/2, and abs(X) ≤ ½g_kb_k ≤ ε₁′/200.
  - #4.110: σ_k := 2B₀c_K(1 + 2dL)b_k and N_k := 2d²σ_k².
  - #4.560-0: ε′_k := ε_k + C_c(α̂₀ + α̂₁) + 25g_kb_k, so g_kb_k ≤ ε′_k/25 ≤ ε₁′/100 by #4.560.1-1.
  - Then 4e^{1/4}·2d²(2B₀c_K(1 + 2dL))²(ε₁′/100)²c_4δ′_k/(C_{V′}ε₁′) = (32e^{1/4}/10⁴)(dB₀c_K(1 + 2dL))²c_4ε₁′δ′_k/C_{V′} ≤ (2dB₀c_K(1 + 2dL))²c_4ε₁′δ′_k, using C_{V′} ≥ 1.
  - The real data route is C(1 + β₀)²(k − j + 1)ε₁δ′_k abs(δ_k), and (k − j + 1) ≥ 1.
- **Consistency with the real route.** #4.168 calls the form route "a data derivative of the same kind as the second". The class bound is now of the second's form, with ε₁′ for ε₁.
- **t1.** #4.41-0: "g″ is run A's coupling function in both runs". #4.41-1-1 bounds (g″)^{−2} by run A's g_{j(x)}.
- **t6.** The downstream uses are unchanged.
  - #4.563-2.1-1 has |Y − 1| ≤ 3ε₂ and |Y| ≤ 2, both of which hold at η with room to spare.
  - #4.563-3-0's |X − 1| ≤ ½ holds at η.
  - #4.563-3-1 reads the field strength at a_j.
- **Citations of the new lines.** No live note cites #4.567–#4.567-1 as a closed range that should now include #4.567-2. The table's row 466 cites #4.567-1 for the radius, which is unchanged.
- **New tags.** #4.567-2 and #4.567-2-1 were unused before (Grep over the YM4 .md files).
- **Line lengths.** #4.561.1-1-0 571, #4.561.1-1.1 389, #4.563-2.1 590, #4.563-3 260, #4.564 290, #4.567 506, #4.567-1 571, #4.567-2 418, #4.567-2-1 280, #4.568 564 characters. CR count 0.

## Pre-check of lf-p13b2-20261108-r26 (narrow)

- **Spec.** specs\spec_p13b2_r26.json, prior r25.
- **Named steps.** The changed lines #4.561.1-1-0, #4.561.1-1.1, #4.563-2.1, #4.563-3, #4.564, #4.567-1, #4.567-2, #4.567-2-1, and #4.568, with their consumers #4.563-2.1-1, #4.563-2.2, #4.563-3-0, #4.563-3-1, #4.567, and #4.567-0.
- **Changed since r25.** These lines, each re-read in place.
- **Cited lines re-read.** #4.41-0, #4.57 (b_k, δ′_k), #4.110 (σ_k, N_k), #4.160, #4.168, #4.560-0, #4.560.1-1; table #T3.14; LFR II p.358 l.4.
- **Size.**
  - First build: 25,673 characters, over 25k. #4.517–#4.517-2 were context only in this narrow round, so that extract left the packet and is cited by tag.
  - Rebuilt at LF 2fb3f5358bf1: argument 23,329 characters, 28 files.
  - For the full round, the extracts measure: #4.517–#4.517-2 2,298; #4.561–#4.565-1 17,044; #4.567–#4.568 2,549 (21.9k under review); context #4.198-1 634 and #4.559–#4.560-0 2,908. The context will be trimmed there.
- **Symbols.** No new symbol. The definition check passed in the build.
- No known weak point and no OPEN is in the part.

## SHAs

LF a8968717c318 (r25's snapshot) → 2fb3f5358bf1 (m1, t1–t6). Table 6d09b1b5054d and labels 971e7d7d5325 (unchanged; relabel and rows pending with the table fork).

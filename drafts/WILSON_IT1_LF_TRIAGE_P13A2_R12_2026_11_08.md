# Triage of lf-p13a2-20261108-r12

## Verdict

- r12 was a focused round of 13a2 at LF 185f6a82754a, table 6d09b1b5054d, and labels 971e7d7d5325.
- **Fatal:** none. **Serious:** none. **Minor:** none.
- **Trivial:** four, t1–t4, all presentational.
- The round is **clean**. It is focused, so 13a2's clean count is 1; the next round of 13a2 must be full (r13).
- Round 11's m1 and t1–t5, and 13b r11's m1, o1, and o2, were confirmed repaired.

## Repairs

| Finding | Line | Issue | Repair |
|---|---|---|---|
| t1 | #4.50-1.1.0-0 | α₁^{CMP} would be crisper as a formula | "α₁^{CMP} := 2ε₁max((π/8)dB₀c_tot(1/128), c_{A′}) (not PBG's α₁), twice the larger of that section's two bounds on a_ksup abs(A) by #4.51-1.1's ...". The two bounds are (π/2)dB₀c_tot(1/128)‖𝔛‖_∞ ≤ (π/8)dB₀c_tot(1/128)ε₁ (#4.53-1.1, ‖𝔛‖_∞ ≤ ε₁/4) and c_{A′}(ε/a_n)^{1−ε₀}ε₁ ≤ c_{A′}ε₁ (#4.53-1.1-1) |
| t2 | #4.52-1-1.1 | REG prints the identification of (1.15) with Ax_k(𝔅_k, 1) at p.097 l.44 | "(1.19) at the base 1 is REG's axial gauge (1.15) (p.078 l.29–38), its Ax_k(𝔅_k, 1) (p.097 l.44)". Checked: p.097 l.44 reads "a configuration satisfying the axial gauge conditions (1.15), i.e. we get a configuration belonging to Ax_k(𝔅_k,1)". The table's #T11.33 should say that "not the absolute axial gauge (1.15)" is for a base U₀ ≠ 1; sent to the table fork |
| t3 | #4.52-1-1.1 | The match of l.10's Q^{s*}_{k−j}V_Λ with REG's Ū_0^j was unstated | "at the base Q^{s*}_kV_Λ, with Ū_0^j = M^j(Q^{s*}_kV_Λ) = Q^{s*}_{k−j}V_Λ". Re-derived from CRE (1.3) (p.246 l.39–44): the base is 1 on the bonds inside the k-blocks and V(c) on B(c) = {b : b₋ ∈ B(c₋), b₊ ∈ B(c₊)}. A scale-j average of a bond inside a k-block uses only bonds of that k-block, so it is 1. Each averaging path of a scale-j bond in B(c) crosses B(c) once and is 1 elsewhere, so the average is V(c) |
| t4 | #4.51-2-1 | The tangency is exact, so "modulo REG (1.14)" and "through a gauge lift" are not needed | "So H₁𝔛 is tangent to the critical set (VAR (98), (101)), and by ODE uniqueness and the unique critical orbit of VAR Theorem 1 ...". The gauge freedom stays in "up to a gauge transformation of (1.14)" |

## Checks

- No CRLF. Line lengths: #4.50-1.1.0-0 421, #4.51-2-1 499, and #4.52-1-1.1 592 characters.
- "gauge lift" and "modulo REG (1.14)" have no other uses. α₁^{CMP}'s one consumer, #4.53-1, cites #4.50-1.1.0-0 by tag and is unchanged.

## Rounds

- 13b r12 (narrow) is next; its extract #4.52-1–#4.52-1-2 contains t2 and t3. Then 12a r15 (full), then 13a2 r13 (full).

## Pre-check of lf-p13b-20261108-r12 (narrow)

- **Spec.** specs\spec_p13b_r12.json at LF 8e49f0e24a20, prior r11. --check gives 0 conflicts (2 allowed). Claim (i) now names p.097 l.44 and Ū_0^j = Q^{s*}_{k−j}V_Λ; the permitted background names REG p.097 l.44. Built: 5,026 bytes of argument.
- **Changed tags since r11 (4), all under review:**
  - **#4.52-1-1.1:** 13b r11's m1 and o1, and 13a2 r12's t2 and t3 above. CRE (1.3) and p.257 l.34, REG (1.15) at p.078 l.29–38 and p.097 l.44, and REG (1.65) at p.087 l.36–44 are checked against the transcriptions. 13a2 r12 found these quotations and the bridge correct.
  - **#4.52-1-2:** 13b r11's o2. Ω^B_{m+1} = Ω^A_m (#4.5-2), and Λ lies in the top layer (#4.44-0.2). 13a2 r12 found it correct.
  - **#4.567-1:** 13b r11's o3, the citation (#4.561.1-2, #4.560.1-1). Re-derived: abs(V′) ≤ 1 + ¼C_{V′}ε₁′ ≤ 9/8, since ρ_V ≤ ¼. So abs(W_dV′ − 1) ≤ (9/16 + ¼)C_{V′}ε₁′. And abs(X) ≤ e^{−1/4}ρ_V gives abs(X)e^{abs(X)} ≤ ρ_V, as ρ_Ve^{−1/4} ≤ ¼.
  - **#4.568:** 13b r11's o4, the list of ε′_k's constants.
- No new symbol. No known weak point and no OPEN is in these lines.

## The split of 12a, and tag pointers in §3(d)

- 12a's own blocks measure 32.5k (#1.1–#1.2-1 1.2k, #3.16–#3.36 19.4k, #3.37–#3.62-1 8.4k, #5.6 0.4k, #5.66–#5.66-2 1.5k), over 25k. So it is split at the sub-headings, in the packet plan:
  - **12a1:** #1.1–#1.2-1, #3.16–#3.36, and #5.6, about 21k. r14 (focused, clean) is its first clean round.
  - **12a2:** #3.37–#3.62-1 and #5.66–#5.66-2, about 10k. Its lines were clean in r12 and in r13, the full round. Since then they changed only by the name (RS) for (R-s) and by tag pointers. They cite #3.26-1 and #3.30, which are unchanged, and use δ^f_j and δ^s_j only through their definitions. So 12a2 is done.
- **Tag pointers** (bookkeeping): ten vague "below" and "above" pointers in §3(d) now cite tags:
  - #3.19.1-0 → (#3.68–#3.68-1); #3.20 → #3.34; #3.22 → (#3.80); #3.24 → #3.48–#3.99-1;
  - #3.24-1 drops "below", since it already cites #3.48–#3.99-1;
  - #3.26 → #3.26-1–#3.31; #3.26-4 → "in #3.26-4–#3.26-5"; #3.28-2-2 → (#3.28-2-3); #3.28-6 → #3.28-3-1;
  - #3.48 → #3.49–#3.99-1; #3.53 → (#3.61).
- **Split line:** #3.24-1 (616 characters) is split at a sentence boundary, giving the new #3.24-1-1.

## Pre-check of lf-p12a1-20261108-r15 (full)

- **Spec.** specs\spec_p12a1_r15.json at LF 4cf4519bb09d (refreshed after 13b r12's repairs, which lie outside its extracts), prior lf-p12a-20261108-r14. Built: 23,140 characters of argument, about 1.6k of them context.
  - Under review: #1.1–#1.2-1, #3.16–#3.36, and #5.6.
  - Context: #4.53-1–#4.53-1.0-2 (13a2's), for its use in #3.27-1-2.
  - --check gives 0 conflicts (1 allowed).
  - It launches after 13b r12 reports.
- **Read in full myself** (the full-round rule): #1.1–#1.2-1, #3.16–#3.36, and #5.6.
  - **#3.19.1–#3.19.1-0** changed after r13 and were not in r14's focus. Checked against LFR I p.181 (corrected file):
    - l.39–42 name the generalisations of (1.22)–(1.23) for j ≤ k₀ but do not print them; l.41 says the regions are disjoint; l.42–44 give the L₀ powers for the overlapping regions.
    - The coefficients 1 − β(1 − 2^{−(j−i+1)}) at the layers i < j and 1 − β/2 at the layer j match (1.22) (n = 0), (1.23) (n = 1: 1 − β(½ + ¼) = 1 − β(1 − 2^{−2})), and l.48–49.
    - #3.68-1's ℓ = L₀^{2max(0, i−k₀−1)} is 1 at i ≤ k₀ + 1, so it covers the case j ≤ k₀.
  - **#3.24-1:** β/10 − β/45 = 7β/90 at L = 3, and (1 + β/15)(1 − 7β/90) < 1, with 2κ_s = β/15.
  - **#3.29-1:** log g_k^{−2} ≤ log g_j^{−2} + 2log(1 + β₀) ≤ 2log g_j^{−2}, from g_j ≤ (1 + β₀)g_k. The factor 2^{p₀+2r+1} = 2^{p₀}·2^{r+1}·2^r.
  - **#3.30-1:** C_{1.27} carries (ε/a_j)^{1−ε₀} = (ε/a_j)^{1−2ε₀}L^{−ε₀j}, with the sup over j.
- **Changed tags since r14 (18):**
  - #3.19.1-0, #3.20, #3.22, #3.24, #3.24-1, #3.26, #3.26-4, #3.28-2-2, and #3.28-6: the tag pointers above;
  - #3.24-1-1: the split above;
  - #3.27-1, #3.27-1.0, #3.27-1-1, #3.27-1-2, and #3.28-1: r14's c1–c5 (WILSON_IT1_LF_TRIAGE_P12A_R14_2026_11_08.md);
  - #4.53-1, #4.53-1.0, and #4.53-1.0-1 (context): 13a2's repairs, reviewed clean in 13a2 r12.
- Every line of the extracts under review is under review in a full round. No new symbol. No known weak point and no OPEN is in these lines.
- Lines over 600 characters in 12a1: none after the split. No CRLF.

## SHAs

LF 185f6a82754a → 8e49f0e24a20 (t1–t4) → cf78c695fc4c (tag pointers) → 29d718346d09 (#3.24-1 split). Table 6d09b1b5054d (unchanged).

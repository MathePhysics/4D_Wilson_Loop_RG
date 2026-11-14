# Triage of lf-p12a1-20261108-r15

## Verdict

- r15 was the full round of 12a1 at LF 4cf4519bb09d, table 6d09b1b5054d, and labels 971e7d7d5325.
  - Under review: #1.1–#1.2-1, #3.16–#3.36, and #5.6.
  - Context: #4.53-1–#4.53-1.0-2.
- **Fatal:** none. **Serious:** none. **Minor:** none.
- **Cosmetic:** five, c1–c5.
- The round is **clean**. r14 (focused) was clean, so this is the second consecutive clean round and the full one. **12a1 is done.**
- 12a2 is done (WILSON_IT1_LF_TRIAGE_P13A2_R12_2026_11_08.md, the split), so **12a is done**.
- Round 14's c1–c4 were confirmed repaired.

## Repairs

| Finding | Line | Issue | Repair |
|---|---|---|---|
| c1 | LABELS, the table's LF symbol list | Stale lines; #3.27-1.0, #3.27-1-1, #3.27-1-2, and #D.c_ax are missing; c_{ax} is missing from the table's list | These are the table fork's. It has been sent every SHA since 185f6a82754a and is now sent this one, with c_{ax} for the symbol list |
| c2 | #3.19.1 | For j ≤ k₀ the test regions were not named, and f^{(n)}_□ used the assignment of the next line | "over the tested plaquettes p assigned to □ (#3.19.1-1), on the layers of (1.16) (#3.26-1)" |
| c3 | #3.29 | Two definitions of ε₁ exist (§1 and §4(c)); #3.29 did not say which enters ρ̄_j | "ε₁ = C(M)R_kε_k of §4(c) (#4.43-1; §1's ε₁ is covered in #3.30-2)" |
| c4 | #3.28-2-1–#3.28-2-2 | The route to abs(g_jB_j) < 7δ′_j through (1.54) and BCH is longer than needed | No change. The shorter route is valid: where g_c = 1, the (1.59) argument is abs(e^{ig_jB_j} − 1), so abs(g_jB_j) ≤ (π/2)(1 + 2κ_s)2δ′_j < 3.2δ′_j (#T11.26). The printed route is also correct, and its constant 7δ′_j feeds #3.28-2-3's (7/2) and §4(e)'s #4.634, which are reviewed in their packets. Replacing it would change those reviewed lines without changing any result |
| c5 | #3.28-2-3, #3.31 | The coupling part needs the fine ratio t^A/t^B ≤ 1 + 2Cg_j²abs(δ_j), not the crude bound 2 | #3.28-2-3 now reads "up to #3.28-1's factor 1 + Cg_j²abs(δ_j) between the runs". #3.31 now reads "which covers the ratio t^A/t^B ≤ 1 + 2Cg_j²abs(δ_j) ≤ 2 of #3.26". Re-derived: abs(t^A − t^B) ≤ Ct^Ag_j²abs(δ_j) ≤ ½t^A gives t^A/t^B ≤ 1/(1 − x) ≤ 1 + 2x, with x := Cg_j²abs(δ_j) ≤ ½. The total is (7/2)C(1 + x) + (1 + 2κ_s)C(1 + 2x) = (4.5 + 2κ_s)C(1 + O(x)) ≤ 4(2 + κ_s)C |

## Checks

- No CRLF. Line lengths: #3.19.1 406, #3.28-2-3 547, #3.29 376, and #3.31 341 characters.
- c2, c3, and c5 are rewordings that change no bound: two pointers, a reading of the existing ε₁, and the ratio that the line already used. So 12a1 stays done.

## Rounds

- 13a2 r13 (full) is next, then 13b r13 (narrow), then 13a1 r9 (focused).

## Pre-check of lf-p13a2-20261108-r13 (full)

- **Spec.** specs\spec_p13a2_r13.json at LF a6bf083f0336, prior r12.
  - One extract, #4.51–#4.55-1-1, all under review.
  - --check gives 0 conflicts (6 allowed).
  - Built: 16,299 characters of argument.
- **Read in full myself** (the full-round rule): #4.51–#4.55-1-1, while 13b r12 ran. Re-derived:
  - C_Δ(M), through min(u, v) ≤ (uv)^{1/2}, Σ_yK̃_Λ(y)^{1/2} ≤ N_blΣ_{y′}K_Λ(y′)^{1/2}, and √N from ‖𝔛‖_∞ ≤ √NΔ;
  - C_{dΛ} = 8√NC_bdB₀ (two terms, each 2C_bdε₁·2B₀);
  - #4.53-1.0-1–#4.53-1.0-2's telescoping, with Σ_{n<k}(L − 1)a_n = a_k − ε;
  - both brackets below α₁^{CMP} = 2ε₁max((π/8)dB₀c_tot(1/128), c_{A′}): the first is ≤ (π/8)dB₀c_tot(1/128)ε₁, and the second is ≤ c_{A′}ε₁;
  - C′_Δ(M) and c_{δD};
  - ε_{D″} = (2 + 2πLc_{δD})ε₁ (four sides, each with at most L bonds moved by ≤ (π/2)c_{δD}ε₁);
  - C_pr's 6 = 2B₀'s 2 × the 3 of #4.54-0.1.1;
  - C_A(M), and #4.55-0.1's g_k²/g_j² ≤ (1 + β₀)²(k − j + 1).
- **Changed tags since r12 (4):**
  - **#4.51-2-1:** r12's t4, the exact tangency.
  - **#4.52-1-1.1:** r12's t2 and t3, and 13b r12's m1 and o2 (WILSON_IT1_LF_TRIAGE_P13B_R12_2026_11_08.md).
  - **#4.52-1-1.1-1:** new, 13b r12's o1. The identity is checked against CMP 98 (15) at p.019 l.41–47 and CRE (1.3).
  - **#4.52-1-2:** 13b r12's o3.
- r12's t1 is in #4.50-1.1.0-0 (13a1, permitted background here), and the claim states it.
- No new symbol. No known weak point and no OPEN is in these lines.

## SHAs

LF 4cf4519bb09d → a6bf083f0336. Table 6d09b1b5054d (unchanged).

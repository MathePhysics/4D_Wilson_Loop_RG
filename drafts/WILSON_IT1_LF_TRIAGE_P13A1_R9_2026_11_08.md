# Triage of lf-p13a1-20261108-r9

## Verdict

- r9 was a focused round of 13a1 at LF 1b87b5ea51bf, table 6d09b1b5054d, and labels 971e7d7d5325, on the eleven tags changed since r8.
- **Fatal:** none. **Serious:** none.
- **Minor:** one, m1. The letter N (in √N, NC_Φ(M), C_{1−ζ₀}(M), and C₁) is not defined in these lines; it was reached only through "(both #T6.23)". It also clashes with the LF's {#D.N} N := k − h (#3.19), read as which the constants would depend on k.
- **Trivial:** t-a (#4.46-0, the norm of PBG (3.133)'s kernel), t-b (#4.50-2 restates #4.92's conditions), and t-c (#4.50-2 names the κ_W condition without writing it). For information: #4.51's Δ := ‖𝔛‖₂ shares its letter with Δ(y), Δ₁, and Δ(U_t).
- The round is not clean, so 13a1's clean count stays 0. Round 8's m1 and t1–t4 were confirmed repaired.

## Repairs

| Finding | Line | Issue | Repair |
|---|---|---|---|
| m1 | #4.44-2, #4.44-2-1 | N undefined locally; clash with #3.19's N := k − h | The new #4.44-2-1 says "So ‖Y‖_∞ ≤ √N‖Y‖₂, N being the dimension of #T6.23's representation G ⊂ U(N), as in #4.48-2–#4.51-3, not #3.19's N := k − h." The definition of 𝔛 moves with it into #4.44-2-1, since #4.44-2 would otherwise be 663 characters. #4.51-2.1's citation of the √N bound becomes #4.44-2-1 |
| t-a | #4.46-0 | (3.133) names no norm for H_{μν}(x, y′) | "its kernel bounds read in the operator norm on 𝔤^c induced by abs(·) (inferred, not printed: (3.133) names no norm, and another changes B₀ by a factor of G)". The K_Λ count moves into the new #4.46-0-1 to keep the line under 600 characters. #4.47-0 now cites #4.46-0-1 and #4.53-1.1 cites #4.46-0–#4.46-0-1 |
| t-b, t-c | #4.50-2 | #4.92's conditions are restated, and the κ_W condition is not written | "…at PBG's α₁ lowered to 16dLα₁ ≤ 1, among them #4.92's 4C_U(M)ε₁ ≤ α₁ and 4C₀^{ms}ε₁ ≤ α₁, which give what (I) of *The Current at the Multiscale Chain.* in (ii) needs to use *The multipliers.* at every t ∈ [0, 1]; and that section's (T-E) and c_QL^{d+1}κ_W ≤ 1 of its ΔJ_c (#4.359)." |
| info | #4.51, #4.51-2.1, #4.51-3 | Δ shares its letter with Δ(y), Δ₁, and Δ(U_t) | Renamed to {#D.Δ_𝔛} Δ_𝔛 := ‖𝔛‖₂ in its three lines. These are the only uses; C_Δ(M) and C′_Δ(M) are unchanged names. No other file cites LF #D.Δ. This is bookkeeping in 13a2's lines |

## Checks

- **m1, re-derived.** Every N in #4.44-2-1 through #4.51-3 is from abs(X) ≤ √N‖X‖ (#T6.23, CMP98 (20)). These are #4.48-2 (Schwarz), #4.48-3.1 (Cauchy), #4.49, #4.50-0 (C₁), #4.51-2.1 (C_{dΛ}), and #4.51-3 (C_Δ(M)). A scan of §4(c) for a bare N finds no other meaning.
- **t-a.** PBG p.422 l.23–30 prints abs(H_{μν}(x, y′)) with no norm named, as the referee says. Any two norms on End(𝔤^c) are equivalent with constants of G.
- **t-b.** #4.92 reads "4C_U(M)ε₁ ≤ α₁ and 4C₀^{ms}ε₁ ≤ α₁", and 4C_U(M)ε₁ ≤ α₁ implies the 2C_U(M)ε₁ ≤ α₁ that (I) needs (#4.349, #4.71). #4.359 has c_QL^{d+1}κ_W ≤ 1.
- **Line lengths:** #4.44-2 516, #4.44-2-1 296, #4.46-0 491, #4.46-0-1 248, #4.47-0 290, #4.50-2 470, #4.51 498, #4.51-2.1 481, and #4.51-3 568 characters. #4.53-1.1 is 640, 6 more than before; it is in done part 13a2 and its edit is a re-point.
- No CRLF. Δ_𝔛 is new and clashes with nothing in the LF, the table, or the Cauchy note.

## Rounds

- 13b r14 (narrow) is next, then a full 13a1 round r10 on the repaired lines, then 13b's full round. 13a1 r10 is full, but its clean count is 0, so it can be only its first clean round; a further full round follows it.

## Pre-check of lf-p13b-20261108-r14 (narrow)

- **Spec.** specs\spec_p13b_r14.json at LF 0dfaf73c3db4, prior r13. --check gives 0 conflicts (2 allowed). Built: 5,840 characters of argument.
- **Changed tags since r13 (4), all under review:**
  - **#4.52-1-1.1-1:** r13's m1. b′ names the averaged bond, the induction on j is stated, and (15)'s factor U(b′) does not matter. If every U(Γ_{b′,x}) equals W, then (15) gives exp[i(1/i)log(WU(b′)^{−1})]U(b′) = W, since exp∘log = id near 1 and the average of equal terms is the term.
  - **#4.52-1-1.1-2:** the conditions (1.19) at U_{REG} are those at the base 1, since its averages are 1 on the contours.
  - **#4.52-1-2:** the averages are written M^n(MU^B_0), as in #4.53.
  - **#4.561.1-1.3-1.0:** "at their data V_k(z) (#4.559-1)". #4.559-1 defines V_k(z) := M^k(𝐔(z)) and says that at a real point U_0 is the minimiser of LFR I (1.79).
- r9's edits are outside 13b's lines.
- No new symbol. No known weak point and no OPEN is in these lines.

## Reading of 13a1 before its full round

- I read #4.43–#4.50-2 (LF lines 524–580) in full while 13b r14 ran, re-deriving each bound:
  - #4.48-1 (½C_Φ(M)C₁²ε₁², using C₁ ≥ 1);
  - #4.48-1.1 and #4.48-2 (Cauchy, then Schwarz with ‖Y‖_∞³ ≤ N‖Y‖_∞‖Y‖₂²);
  - #4.48-3.1 (C_{1−ζ₀}(M));
  - #4.50 (abs(UV^{−1} − 1) = abs(U − V), and abs(log U) ≤ (π/2)abs(U − 1));
  - #4.50-0 (C₁, no circularity);
  - #4.50-1.1.1-1 (the runs' log g_k^{−2} within a factor 2; g(log g^{−2})^a increasing on (0, e^{−a})).
- No gap was found.
- **Forward pointers.** Eleven vague forward pointers ("below") are replaced by tags: #4.43-1.2 (#4.50), #4.44-2 (#4.45–#4.50-0, #4.44-2-1), #4.45-1 (#4.48-3–#4.48-3.1), #4.46 (#4.50-0), #4.46-1.1 (#4.50-1), #4.48.0 and #4.48.0-2 (#4.48.0-2.1), #4.48-4 (#4.50-1.1), #4.50-1.1.0-0 (#4.53–#4.53-1.2), and #4.50-1.2 (#4.51, #4.53, #4.54). These are bookkeeping.
- **Line lengths.** Every line of the part is ≤ 600 characters except #4.43-1.1 (608, unchanged).
- **Spec.** specs\spec_p13a1_r10.json (full, one extract #4.43–#4.50-2) at LF 5c005225d6a9. --check gives 0 conflicts (7 allowed). It is built at launch, after 13b r14 reports.

## SHAs

LF 1b87b5ea51bf → 0dfaf73c3db4 → 5c005225d6a9 (the pointers). Table 6d09b1b5054d (unchanged). Labels 971e7d7d5325 (stale: new tags #4.44-2-1, #4.46-0-1, and #D.Δ_𝔛; the table's owner is told).

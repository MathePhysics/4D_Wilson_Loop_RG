# Background-Iteration Closure, Third Session Self-Review (10 Nov 2026): Triage

Review: the session's own third full read of WILSON_IT1_BACKGROUND_ITERATION_CLOSURE_2026_10_26.md at e076734eead9, every line from the opening to the closing lists, with each computation redone (the identity of §3.1, the bounds of §3.2 with the 𝐑-parts and the sum lemma, the telescoping of §3.3, the chart and Lipschitz constants of §4.1–4.2, the arc and per-cube exponents of (iii-a), (iii-d) and §5.3, and the step sum of (iv-b)).

## Verdict

Not clean. There is no fatal and no serious finding, and there are five minor findings (H1–H5). Every computation checked agrees with the note.

## Repairs

- **H1** (§3.1 *The complement*): two remarks claimed more than is shown. The crude bound was "never of the right order", and the coarse normalisation's perimeter factor was "exponentially large in P_k(C)"; both are lower bounds, and no sign of δm is derived.
  - Repair: 1/|κ_f^{(K)}| = ∏_j|e^{δm^f_jP_{j−1}(C)}z_j^{−4}| is bounded only through the fine chain's perimeter self-energy, whose bound is unbounded as ε → 0 at fixed ℓ_C. For k < K, N_k/κ_f^{(K)} = e^{E^f_{const,k}}/κ^{g_k,(K)} (§3.1's proof), and 1/|κ^{g_k,(K)}| is bounded only through the coarse chain's perimeter self-energy, a bound exponential in P_k(C).
  - The conclusion is unchanged: ℒ_k is taken with the two chains' D(K) forms.
- **H2** (§2.3, §3.2, (iii-a)): the coarse amplitude bound was stated as an expectation. §2.3 wrote "§4.2 expects 𝔞^g_{j+1} ≤ (b_d^c)^{2k}𝔞_{j+1}", which is the wrong pointer (§4.2 is the Lipschitz recursion), with a heuristic reason; §3.2 wrote "expected"; (iii-a) wrote "the expectation from (D4)". But the coarse-chain note's §4.4 derives 𝔞^g_{j+1} ≤ c_X(b_d^c)^{2k}𝔞_{j+1} and 𝔞̄^g ≤ c_X(b_d^c)^{2k}𝔞̄.
  - Repair: (iii-a) states the form 𝔞^g_{j+1} ≤ (b_d^c)^{2k}·C·𝔞_{j+1} (the wording the coarse-chain note quotes) and that the coarse-chain note's §4.4 gives it with C = c_X of §5.3. §2.3 and §3.2 cite (iii-a), and the heuristic is deleted.
- **H3** (§1.5): the enlargement of the coarse chain's σ by the blocks was cited to 4.1(4), the sizes. It is 4.1(1), the dependence domain. The line is split at a sentence boundary (it had 1,042 characters).
- **H4** ((D3) in §4.3): "under (C2′), (C4), (D4) per-slot size" read as a list of three conditions. It now reads "under (C2′) and (C4), (D4) per-slot size".
- **H5** (*Sources Read*, *What Is Bałaban's*): RG1 p.265 (2.3) and CRE p.267's multi-domain transfer were listed, but the body cites neither. Both are deleted.

## Pre-Check

- Every changed line re-read. Every use of 𝔞^g, 𝔞̄^g, c_X, (iii-a), 4.1(1) and the remarks on κ_f^{(K)} grepped; §3.4's "not of the right order for the fine part" agrees with the repaired §3.1.
- The coarse-chain note's quote of (iii-a)'s form, "𝔞^g_{j+1} ≤ (b_d^c)^{2k}·C·𝔞_{j+1} with C from D2.4(12)'s constants", is kept word for word, so its citation still holds.
- Definitions (bgdefs): every symbol is defined once. Pointers (bgptr): only the known non-tags #cubes, #X and #NV.3-4-2 are reported.
- Lines over 600 characters: none among the edited lines.
- Size: from 334 lines and 100,678 characters (e076734eead9) to 335 lines and 100,678 characters (b273ec3fa013).
- No other session's file quotes the changed text, so no message is needed. The ℒ_K bound and e^{c_C} are unchanged.

## SHAs

Background note: e076734eead9 → b273ec3fa013.

## Status

This round has minor findings, all repaired. The next full self-review is the candidate for clean round 1.

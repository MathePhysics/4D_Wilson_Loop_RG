# Background-Iteration Closure, Second Session Self-Review (10 Nov 2026): Triage

Review: the session's own second full read of WILSON_IT1_BACKGROUND_ITERATION_CLOSURE_2026_10_26.md at 521bd90aaecd, every line from the opening to the closing lists.

## Verdict

Not clean. There is no fatal and no serious finding, and there are five minor findings (G1–G5). Every tag resolved.

## Repairs

- **G1** (§3.1): 𝔏_good was introduced as "the set of labelled terms on which both chains have their D(K) forms", but *The complement* then fixes it as ℒ_kᶜ, a subset of that set. It now reads "a set of labelled terms at step K on which both chains have their D(K) forms (fixed in *The complement* below)".
- **G2** (§3.4): the I-term at the stopping scale was written over all labels, while ℒ_{K′} is covered whole (β and I^f together) by the bound 2|κ_f^{(K′)}|e^{c_C}δ_LF of (iv-e). The term is now |⟨e^{𝓔^f_{K′}}I^f_{K′}⟩^{good}|, matching the β-term's ⟨·⟩^{good}.
- **G3** (4.1(4), §4.2, (D5) in §4.3): the transports' norm bound was stated with c_π^ℂ, which is weaker than what the coarse-chain note's §2.2 uses (c_π).
  - Re-derivation: with log V = A + iB, A and B in 𝔤 (Hermitian convention of table #T12.13-1), the Hermitian part of π_*(log V) is π_*(A). Its norm is at most c_π‖A‖ ≤ c_π‖log V‖. And ‖e^M‖ ≤ e^{λ_max((M+M*)/2)} for every matrix M, since (d/dt)‖e^{tM}x‖² = 2Re⟨Me^{tM}x, e^{tM}x⟩ ≤ 2λ_max((M+M*)/2)‖e^{tM}x‖².
  - So ‖π(V)‖ ≤ exp(c_π‖log V‖), and ‖π((M^k𝐔)(c))‖ = ‖π(V)‖ as π((M^kU_{j+1})(c)) is unitary. With ‖log V‖ ≤ −log(1 − ‖V − 1‖) ≤ 1.04Δ_k (‖V − 1‖ ≤ 0.075), this gives ‖π((M^k𝐔)(c))‖ ≤ exp(1.04c_π(b_d^cL)^kθ_j). The slot bound 1 + ‖X_c‖ ≤ exp(1.04c_π^ℂ(b_d^cL)^kθ_j) keeps c_π^ℂ.
  - 4.1(4) states both bounds; §4.2 proves the norm bound in a sub-line; (D5) quotes ‖π(·)‖ ≤ exp(1.04c_π(b_d^cL)^kθ_j). The (D5) item is split onto its own line (the old line had 950 characters).
  - The other uses of c_π^ℂ for norms ((iii-a), τ_c, (iii-d), §5.3 (4)) remain true, as c_π ≤ c_π^ℂ.
- **G4** (*Constant Conditions*): the constants line restated the definition sites of the note's own symbols, which the table now indexes (#T12.30–#T12.30-10), and omitted m, 𝔞̄^g and x_k. It now keeps the identifications of the map's constants (C_S′, C_ζ, c^T_E, C^T_E, C̄_Z, C^E_Σ; C^R_E, c^R_E) and cites table #T12.30–#T12.30-10 for the rest.
- **G5** (*Sources Read*): the newly cited table row #T12.19-12 and map line #MD2.1.1.23-1 were missing; both are added.

## Pre-Check

- Every changed line re-read; every use of c_π^ℂ, (D5), 4.1(4), 𝔏_good and the ℒ_K bound grepped. The consumers of (D5) are (iii-a)–(iii-d) and the coarse-chain note §2.2; c_π in the norm bound serves both.
- Definitions (bgdefs): every symbol is defined once. Pointers (bgptr): every tag resolves; the remaining hits are the known non-tags #cubes, #X and #NV.3-4-2 (a file-qualified tag). Every tag cited in the body is in *Sources Read*, directly or inside a listed range.
- Lines over 600 characters: none among the lines edited in this round.
- Size: from 332 lines and 100,439 characters (521bd90aaecd) to 334 lines and 100,678 characters (e076734eead9). The growth comes from G3's proof of the norm bound; G4 removed text.

## Defects in Other Sessions' Files

- Coarse-chain note (owner (4)): the earlier report (WILSON_IT1_LF_TRIAGE_BG_SELF_2026_11_10.md) said that c_π should be c_π^ℂ there. By G3's re-derivation c_π is right for norms of π-images, and only the factor 1.04 (from ‖log V‖ ≤ 1.04Δ_k) is missing. So its §2.2 exponent should be exp(1.04c_π(b_d^cL)^kΔ_0), (C7)'s 1.08 should be 1.12 (1.04·1.06·1.01 = 1.1134), and (C9)'s 1.06 should be 1.11. (Cε) still implies the corrected (C7). The correction was sent to (4).

## SHAs

Background note: 521bd90aaecd → e076734eead9.

## Status

This round has minor findings, all repaired. The next full self-review of the note is the candidate for clean round 1, and a second clean full round must follow.

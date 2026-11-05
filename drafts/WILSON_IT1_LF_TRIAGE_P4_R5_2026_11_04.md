# LF Packet 4, Review 5: Triage

Review: verification\isolated_reviewer\reviews\lf-p4-20261104-r5\review.md (LF 5b5acbec3af8). Verdict: (K1)–(K6), #A.10, and #0.1.27 hold as stated, and #0.1.28 holds, conditional on the labelled dependencies, except for the unit convention of ‖·‖_{W_ms}. There is no fatal item, one serious item, and four minors. The pass is not clean, so the count of clean passes restarts. All items are accepted. LF after the repairs: fa0767743ba9 (labels b387f9c4c001).

## Serious

1. **#0.1.28, "the field in the units of the layer of the bond's site (#A.11.49)".** Accepted. On the strip of Λ_{j+1} next to Λ_j/Λ_{j+1}, where χ_j = 1, #A.11.42 and #A.11.49 bound the field in units of L^j.
   - Repair: the norm is now taken "with the field in the units of L^{j(b)}, j(b) the least j with χ_j(b) ≠ 0 (#A.11.49)".
   - The readings are covered: R_j consists of points of Λ_j and Λ_{j+1} (#A.11.48), so χ_j ≠ 0 at a bond of Λ^B_n only for j ∈ {n − 1, n}, and j(b) ≥ n − 1. A reading there at blocks finer than c's has a scale ≤ n − 1 ≤ j(b). The text now states this.

## Minor

1. **Conditional dependencies.** Labelled. No change.
2. **The claim's T_□ factor.** The next claim states M ≥ M₀(L) and ε₁ ≤ ε₁(L, M) with L ≥ L₀(d).
3. **#0.1.28, the block averages.** Now ≤ C(d)(1 + log L)^p‖c‖_W.
4. **Lattice slack.** Acknowledged in the text. No change.

## Next

p4 r6 on LF fa0767743ba9 (labels b387f9c4c001).

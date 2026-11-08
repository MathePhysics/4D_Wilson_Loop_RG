# LF Packet 4, Review 6: Triage

Review: verification\isolated_reviewer\reviews\lf-p4-20261104-r6\review.md (LF fa0767743ba9). Verdict: (K1)–(K6), #A.10, and #0.1.27 hold as stated, and #0.1.28 holds, conditional on the labelled dependencies, with the units-of-L^{j(b)} convention verified. There is no fatal or serious item, and there are seven minors. This is a clean pass, the first after r5. All items are accepted. LF after the repairs: 450c0eb52df4 (labels 11f6a5462a6b).

## Minor

1. **Conditional dependencies.** Labelled. No change.
2. **#A.11.42, the closing words.** Now "with the field at a fine bond b in the units of L^{j(b)}, j(b) the least j with χ_j(b) ≠ 0 ((6)(vi))".
3. **#0.1.28, the case i_prev − i ≥ 2.** Now "pays W ≤ (1 + log L)^pL/ρ₀, leaving (1 + log L)^p/(Lρ₀) within the factor per level".
4. **"Only inside T_□" citations.** #0.1.28 cites #4.445.2 and #4.445.1, and #0.1.42 identifies the other history (#4.245). No change.
5. **Wording.**
   - #0.1.28 now reads "every value of Im c".
   - It now states that run B's scale indices count from its finest spacing ε/L and that the two runs' scales are compared as block sizes.
   - (K5) now reads "the local component K′ of z in Q_{2Kr}(z)".
6. **#0.1.27, the mass-bond increments.** Now "carries the weight …, times ρ₀ for t(b) < 4√dρ₀, which p absorbs (K2, #A.17)".
7. **Lattice slack and the sign.** #0.1.24 now reads "Δλ = −σ at the free sites (K2)". The slack is acknowledged in the text.

## Next

p4 r7 on LF 450c0eb52df4 (labels 11f6a5462a6b). A clean r7 closes packet 4.

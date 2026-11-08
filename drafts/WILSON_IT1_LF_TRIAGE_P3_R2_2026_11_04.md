# LF Packet 3, Review 2: Triage

Review: verification\isolated_reviewer\reviews\lf-p3-20261104-r2\review.md (LF 1f397a562fda). Verdict: no fatal or serious item. r1's serious item is resolved. This is the first of the two consecutive clean passes. All seven minors are accepted and applied.

## Minor

1. **m1 (#0.1.14, (2.147)).** The sentence is now restricted: the (KW) chain and C_H do not use (2.147) (#0.1.13), and §4 (#4.36) uses (QGQ*)^{−1} at the bounds PBG (3.132)–(3.133) as printed.
2. **m2 (#0.1.18, the local sup bound).** The Caccioppoli step is replaced by a Hadamard division:
   - k·block is the cube of side kL concentric with the block. χ = 1 on the 3/2·block and 0 off the 2·block.
   - For Δ_j, χ(b′) − χ(b) is expanded to second order. The first-order part is (∇χ)·Nu, where N has symbol i∂Δ̂_j, analytic in a strip and vanishing at p = 0. The vanishing follows because Δ̂_j ≥ 0 and Δ̂_j(0) = 0: ⟨B, Δ_jB⟩ is the minimum of ‖∂A‖² + ‖R∂*A‖² on {Q_jA = B} (#0.1.17), and constant B has the constant lift. The premise was checked in the LF.
   - Division by e^{ip_k} − 1 gives N = Σ_k∂_kM_k, so [T, χ]u is a sum of derivatives of (∇χ)Mu and of terms (∇²χ)Mu on the annulus at distance ≥ L/4 from the block.
   - The Q₁ coefficients reach the 5·block. The ∂₁ω term is stated for d = 4, as (1 + log L)^{1/2}‖∂₁ω_{g′}‖_{5·block}, by Cauchy–Schwarz against the kernel of T^{−1}.
3. **m3.** The weighted bound on Π_m∂₁*u is the same test-function argument with the conjugated form, whose coercivity #0.1.17 gives.
4. **m4.** p.291 (86) is added to the B₀ page list.
5. **m5.** "At best with const ≈ 3/(2L)".
6. **m6 (#0.1.18).** After "t ≤ t₃ ≤ L" the argument is added: the 2^k cells around a codimension-k grid face are joined pairwise through face-sharing chains, so a contact between distinct local components has a cell of Λ around it and lies in ∂Λ. The caps are monotone.
7. **m7 (#0.1.19).** Both occurrences of "≥ L/2" now read "≥ L/2 − ½". The local-component sentence reads "at a point z of the contact … with closures containing z".

## Bookkeeping

The tag check found two older duplicate tags in §4: {#D.h} (#4.276) and {#D.φ_B} (#4.284). No line cites either tag. They are renamed {#D.h.3} and {#D.φ_B.2}, since {#D.h.2} is in use at #A.11.40.

## Next

p3 r3 on LF 7dee8e4eafc7 (labels 0a2576566f8e), as the potential second consecutive clean pass.

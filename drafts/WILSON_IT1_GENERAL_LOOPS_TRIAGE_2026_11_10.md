# General-Loops Note: Self-Check and Messages, 10 November 2026

Note: `WILSON_IT1_GENERAL_LOOPS_2026_11_10.md`, owned by the BETA session. SHA 1d61bc4589e2 after this pass (246 lines, 182 tags). Status: derived, not reviewed. No referee round has been run.

## Open
- (O1) Reflection positivity for general loops (#GL.3). Not treated. Closing it means reading the RP note with corner sums Σ_{c∈𝒦(C)}ζ_c under the reflection.
- (O2) The pair factorisation bound (two-loops #941) is not read with general loops (#GL.3). Nothing in the note uses it.

## Full read (every line, between 21:14 and 21:34)
- #GL2.2-6 repaired. In case (a), V4's hull can be the whole contour when the smallest arc has ℓ_a = P_k/2 − 1 bonds, and diam_k(C) ≤ P_k/2 then exceeds 2Λ(C)D by up to 1. Closed by diam_k(C) ≤ P_k(C)/2 − s_k(C) ≤ ℓ_a: some segment runs along a coordinate other than the one of largest range, and that coordinate varies by at least 2s_k(C). Split as #GL2.2-6-1.
- #GL2.7-5 repaired. "A subarc of fewer than 4r(b) positions" fails by one when r(b) = P_k/8 ≡ ¼ mod 1. Replaced by "length less than 4r(b)": ℓ^∞-distances are integers, so the length is at most 4(⌈r(b)⌉ − 1) < 4r(b). This is what #GL2.2-1 needs.
- #GL1.4-2. s_0(C) ≥ LMR_1 ≥ L²M, using R_1 ≥ L. #GL2.4-2 uses L²M, and the line had printed 2LM.
- #GL5.2-8-2 sharpened. A π_k-cube has side M < LMR_{k+1} ≤ δ_k(C_i), so the segments meeting it are pairwise adjacent, hence at most two. The arc term is at most 2N_C(M + 1)/M ≤ (5/2)N_C, c_off := (1 + (5/2)N_C)ν_r + (3/8)ν_e ≤ 4N_Cν, and Λ̄ drops out.
- Symbol clashes fixed. C_E (general) renamed C^𝒦_E, distinct from the map's C_E = #T4.37's C^T_E. c_h(C) is marked as V4's hull constant, distinct from the map's c_h of #MOMST.9-2. #GL3.12-2's constant is written c_{\mathrm h} = √N, as V4 prints it (G ⊂ U(N)). #GL5.5's x_k names the map's c_h. #GL5.5-4 cites #T12.30-8 for e^{c_C}, e^{c_C^g} instead of redefining them.
- #GL.1-1. Per-loop factor 2Λ̄(C_i) (#GL6.1-2), replacing Λ̄(𝒞).
- Checked unchanged: §§3–7 otherwise, including every inequality of #GL4.10-2 against map #MD2.4.12.22-3 (diam(S_M) ≤ M#(M) + 2(M/L)Σσ_k(W)).

## NL 204c1c20c891 (two-loops session's pass, received between 21:14 and 21:34)
- The separation of #NL1.3-1–#NL1.3-3 carries over to general loops (#GL6.1-4, #GL6.1-4-1). Its proof uses only vertex-disjoint unions of edges of hℤ⁴, h = L^{j−Q}, and #GL1.1-2 and #GL1.3–#GL1.3-1 give that for general loops.
- #GL6.3-1. t_γ ≤ n_γ, so at most n(W) intervals, abs(X ∪ π₁ℋ) ≤ 9𝔰(W), and A′_E is #NL1.5's. #NL6A.4's u₁ holds. The footprint count is Λ̄(𝒞)CLM.
- #GL6.3-2. φ_c(b) ≤ Λ̄(𝒞)Φ_c for all large K, so the factor 2 becomes Λ̄(𝒞), in place of N_CΛ̄(𝒞)/2.
- #GL6.4-3-1. The contour-density constant is max_ic_C(C_i) = 2Λ̄(𝒞).
- Unchanged, since separation does not reach lengths along loops (#NL1.3-4, #NL.1.2): the side count (#GL6.4-1-1), window ends and hulls (#GL6.2), u_𝔏(𝒞), and L₀(𝒞).

## Messages sent
- Between 21:14 and 21:34 to the two-loops session ("yang mills 4 handover ⑂"). NL #NL6A.6/#NL6B.1 with two-loops #715-1/#716: N_C squares have 4N_C sides, so #716's D_P coefficient is 2^{d+1} + ½ + 8N_C. It needs to be at most 2^{d+2}u_𝔏 (σ_g's π(P) carries 2^{d+2}D_P, #691), which fails for N_C ≥ 368 636; the printed check (≤ 2^{d+2}) already fails at N_C = 4. Options given: restrict N_C, or u_𝔏^{(N)} := (N_C/2)u_𝔏. Adopted by them as option (b) in NL 204c1c20c891 (#NL6B.1-1, #NL6B.1-2, #NL6A.9).
- 21:34 to the table session ("yang mills 4 handover (2) ⑂"). Rows A–E announced (general-loop symbols), table 05cbd40be4db re-grepped, no clashes. Awaiting their tags and SHA.
- 21:35 to the two-loops session. Note SHA 1d61bc4589e2. Separation carries over to general loops, with what it changes in the note. A wording remark on #NL1.3-1.1 for any future widening; no change is needed for squares.
- 21:35 to the step-map session ("yang mills 4 handover (4)"). FYI: the note reads the map with general loops; no defect found.

## Withdrawn before sending
- D2.7 closure 15.8-1(4), "arc term ≤ 4(M + 1)/M ≤ 5" for C₁ ⊔ C₂. It is correct for the pair: a π_k-cube has side M < s_k, so it meets at most two sides of each square, at most four in all. The earlier slip claim (8 sides, c_off ≤ 11ν) is wrong and was not sent. The closure leaves this reason unstated, and the LF session that owns the closure is not live; to be mentioned to it as a remark when it is.

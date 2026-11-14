# Packet 14bp (balaban_proofs/BP_CMP98_ADJOINT_AVERAGING.md), Round 7, 9 Nov 2026

## Pre-Check of r7 (Narrow)

- **Spec:** specs/spec_p14bp_r7.json, rev bp-p14bp-20261109-r7. BP 422cd8d6d59f, Cauchy 648f51a2e090, LF b510202f38c5. Definition check: 0 conflicts (9 allowed, T′_b added as local to BP). Reviewed blocks 2.41k; the longest line is 571 characters.
- **Under review:** BP #C10.3.21-4–#C10.3.21-5, #C10.3.21-7-1, #C10.3.22, #C10.3.23-1, #C10.3.24-2, and #C10.3.24-4, the lines repaired after r6. Context: the rest of #C10.3.21–#C10.3.24-4, Cauchy #C10.1.4–#C10.1.4-0-3, #C10.3.17–#C10.3.20, #C10.3.25–#C10.3.28, and #C10.3.31-2.
- **Each line re-read and re-derived:**
  - #C10.3.21-4: L^{−d}Σ_{x∈B(c₋)}abs(𝐆(c₋, x))^{−2}Σ_{Γ,Γ′}1 = L^{−d}abs(B(c₋)) = 1, with abs(B(c₋)) = L^d by #C10.1.4-0-1.
  - #C10.3.21-5: W(c) = W(b_1)⋯W(b_L), so dW(c)W(c)^{−1} = Σ_{b⊂c}Ad(W(c from c₋ to b₋))dW(b)W(b)^{−1}, and dW(b)W(b)^{−1} = iηA(b) under 𝐔 = e^{iεA}U₀. Ad of a group element is an isometry for Re tr X*Y.
  - #C10.3.21-7-1: c_{av}L²κ_W ≤ 1/8 and c_{av} ≥ 1/(8ρ_𝔤) give κ_W ≤ ρ_𝔤/L². qW(∂p)^{±1}q^{−1} = e^{±iAd(q)P}, so Q := ±Ad(q)P and abs(Q) = abs(P) ≤ 2κ_W.
  - #C10.3.22: b = ⟨z, z + e_μ⟩ lies on [x, x + Le_μ] exactly for x = z − se_μ, s = 0, …, L − 1. Since the blocks partition the fine lattice (#C10.1.4-0-1), each x lies in one block B(y), which determines c = ⟨y, y + Le_μ⟩.
  - #C10.3.23-1: N_b ≤ Σ_{x̂∈B(y)}1 = L^d.
  - #C10.3.24-2: the column is (T′_b)* applied to the adjoint of #C10.3.21-4's operator. T′_b* is an isometry, so the bound 5x is unchanged.
  - #C10.3.24-4: W_0 = U is real, and W_i = e^{iY_c}W_{i−1}(c) with Y_c ∈ 𝔤 by #C10.3.21-7-2, under the condition at W_{i−1}. The condition then holds at W_i, by the same bound with i < n.
- **Uses grepped:** T′_b occurs only in BP. #C10.1.4-0-1's consumers are Cauchy §9.8, §10.1, and §10.3, and BP. Cauchy #C10.3.31-2 describes the L^{d−1} term as a transport along c, consistent with T′_b.
- **Size:** BP is unchanged since r6's repairs, 422cd8d6d59f. No queued repair applies to packet 14bp.
- **Launch:** held. The user asked to pause before launching (10:27).

Written 2026-11-09 12:17.

## Round 7, Reviewed by Me in Place of the Referee

- **How:** at the user's request, no referee was launched. I read every line under review and its context in BP and the Cauchy note.
- **Verdict:** clean; no finding.
- **Checked and correct:** the weights (#C10.3.21-4), the adjoint and its column (#C10.3.21-5, #C10.3.24-2), the bond count (#C10.3.22–#C10.3.23-1), and the condition at the W_i (#C10.3.21-7-1, #C10.3.24-4).
- **Next round:** a full round, at BP 422cd8d6d59f.

Written 2026-11-09 16:41.

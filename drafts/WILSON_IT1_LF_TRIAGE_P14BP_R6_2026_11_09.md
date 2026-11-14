# Packet 14bp (balaban_proofs/BP_CMP98_ADJOINT_AVERAGING.md), Round 6, 9 Nov 2026

## Build

Full round of #C10.3.21–#C10.3.24-4, built at 10:20: BP 7e76b7fcdacf, Cauchy 1f73875e3b26, LF 029a1d03a304, table 40e20f5e4530, LABELS 3a2b74eff243. Definition check: 0 conflicts (8 allowed); reviewed block 7.45k. Pre-check: WILSON_IT1_LF_TRIAGE_P14BP_R5_2026_11_09.md, *Pre-Check of r6 (Full)*.

## Verdict

There is no fatal or serious finding, and there are two minor findings, m1 and m2, so the round is not clean. The clean count restarts: r5's clean round was narrow, and r6 is not clean. Both minors are correct; I re-derived each one. The review was read in full. The referee verified every other line, including:
- the move count against D2 #MOSTC.5 and #MOSTC.11, with hand checks at d = 2, L = 3;
- the logarithm bound 1.02|h − 1|;
- dexp at a = 1/8 (0.522a);
- the adjoints dexp_Z* = dexp_{−Z} and dlog_h* = dlog_{h^{−1}};
- the weights, D*_{W̄} against PBG (3.114)–(3.116), and (AQ).

## Repairs

| Finding | Re-derivation | Repair | Lines |
|---|---|---|---|
| m1: the term of weight L^{d−1} omits the isometric transport along c | W(c) is the product of the L fine bonds of c, all traversed along their orientation. So dW(c)W(c)^{−1} = Σ_{b⊂c}Ad(W(c from c₋ to b₋))iηA(b), and the column entry is L^{d−1}T′_b*K*ν(c). T′_b* is an isometry, so the bound 5x is unchanged. | #C10.3.21-5 now reads "It acts on each fine bond b of c through dW(c)W(c)^{−1} = Σ_{b⊂c}T′_b iηA(b), with the isometry T′_b := Ad(W(c from c₋ to b₋)), and with weight L^{d−1}". #C10.3.24-2 now reads "The column carries, followed by the isometry T′_b* (#C10.3.21-5), the adjoint of …". T′_b occurs in no other note. | BP #C10.3.21-5, #C10.3.24-2 |
| m2: L odd is used and not cited ("the weights summing to 1", "determines its coarse bond", disjoint blocks) | RG I p.251 l.14 prints "L is an odd, positive integer". So the centred cube of side L has L^d fine points, and the cubes centred at the coarse points partition the fine lattice, with abs(n_ν) ≤ (L − 1)/2. | The fact is stated once, at its definition: Cauchy #C10.1.4-0-1 now reads "and L is odd (RG I p.251 l.14, table #T10.43), so the blocks have L^d points each and partition the fine lattice, x − y = Σ_νn_νe_ν with abs(n_ν) ≤ (L − 1)/2". BP cites it in #C10.3.21-4 ("(abs(B(c₋)) = L^d, #C10.1.4-0-1)"), #C10.3.22 ("the blocks partitioning the fine lattice (#C10.1.4-0-1)"), and #C10.3.23-1 ("≤ abs(B(y)) = L^d (#C10.1.4-0-1)"). #C10.3.21-6's abs(n_ν) ≤ L/2 stays true. | Cauchy #C10.1.4-0-1; BP #C10.3.21-4, #C10.3.22, #C10.3.23-1 |
| Remark: "κ_W < ρ_𝔤" uses L > 1 | κ_W ≤ 1/(8c_{av}L²) ≤ ρ_𝔤/L². | #C10.3.21-7-1 now reads "κ_W ≤ ρ_𝔤/L² < ρ_𝔤". | BP #C10.3.21-7-1 |
| Remark: "Q := Ad(q)P" for the factor W(∂p)^{−1} | qW(∂p)^{±1}q^{−1} = e^{±iAd(q)P}. | Now "Q := ±Ad(q)P"; the bound abs(Q) ≤ 2κ_W is unchanged. | BP #C10.3.21-7-1 |
| Remark: W_i real is implicit in #C10.3.24-4 | W_0 = U is real, and W_i = e^{iY_c}W_{i−1}(c) with Y_c ∈ 𝔤 by #C10.3.21-7-2 under the condition at W_{i−1}, which this line establishes. | #C10.3.24-4 now reads "The condition holds at the averages W_i of (a) (#C10.3.25), each real by induction on i, Y_c ∈ 𝔤 at W_{i−1} by #C10.3.21-7-2:". | BP #C10.3.24-4 |

- **Consumers:**
  - #C10.1.4-0-1 is cited by the Cauchy note's §9.8, §10.1, and §10.3 and by BP, for the blocks, the contours, and abs(n_ν). The sharper bound (L − 1)/2 and the partition only strengthen these.
  - Cauchy #C10.3.31-2 already describes BP #C10.3.21-4's term as "a transport along c times Ad(e^{iY_c}) minus …", which is consistent with T′_b.
- **Hygiene:** CR 0, no trailing spaces, no duplicate tags. BP's longest line is 571 characters and Cauchy #C10.1.4-0-1 is 542.
- **SHAs after repair:** BP 422cd8d6d59f, Cauchy cae2edf1313c, LF 029a1d03a304, table 1e252f854c47, LABELS 7de12f87e5de.
- **Table:** the fork added "L odd also Cauchy #C10.1.4-0-1" to #T10.43's usage column, re-checked against RG I p.251 l.14, and gave T′_b no row (local to BP). This gives table 0fc5618dd0d4 and LABELS b5585ab6e0f2, and the definition check is 0.
- **Next:** r7, narrow, on #C10.3.21-4–#C10.3.21-5, #C10.3.21-7-1, #C10.3.22, #C10.3.23-1, #C10.3.24-2, and #C10.3.24-4, with Cauchy #C10.3.31-2 and #C10.1.4-0-1 as context. Then r8, full. Launches are held at the user's request (10:27).

Written 2026-11-09 10:32.

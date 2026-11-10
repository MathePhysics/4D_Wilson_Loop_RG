# Triage of lf-p13b1-20261108-r15

## Verdict

- r15 was a full round of 13b1 (#4.52-1–#4.52-1-2, #4.556–#4.560-2, with #4.561 as context) at LF a100b37e1628, table 6d09b1b5054d, and labels 971e7d7d5325.
- **Fatal:** none. **Serious:** none. **Minor:** none. **Trivial:** o1–o3. **Housekeeping:** o4, carried from r14's o2.
- The round is clean. It follows the clean r14 of packet 13b (narrow, covering 13b1's changed lines), and it is a full round of the part, so **13b1 is done**.
- r14's o1 (#4.52-1-1.1-1) was confirmed repaired, with both cases of the induction checked by hand.

## Repairs

| Finding | Line | Issue | Repair |
|---|---|---|---|
| o1 | #4.559, new #4.559-0 | "Since ∇_U is a real operator" was attached to the bounds on A′_R and A′_I, which come from 𝔤 being hermitian | Reworded: "Since 𝔤 consists of hermitian matrices (CMP98 p.20 l.17), A′_R = (A′ + A′*)/2 and A′_I = (A′ − A′*)/(2i), and likewise for 𝐉, so abs(A′_R) and abs(A′_I) are ≤ abs(A′), and abs(𝐉_R) and abs(𝐉_I) are ≤ abs(𝐉), the operator norm being *-invariant; since ∇_U is a real operator, …". The line reached 724 characters, so this sentence is split into #4.559-0 |
| o2 | #4.559-0 | #4.560's current bound 25α_{0,m} uses abs(𝐉_R), abs(𝐉_I) ≤ abs(𝐉), which was stated only for A′ | Covered by o1's "and likewise for 𝐉" |
| o3 | #4.560-1.1 | "its data passing the characteristic functions at O(ε_k) at the scale k on Z (LFR I (1.75), #3.71, #4.523)": #3.71 records the passed side of χ_k at O(1)M²L²R_kε_k, which is not O(ε_k), and #4.523 is about the data of the class | Reworded: "At the real step U_0's parameter is O(ε_k): its plaquettes are < (2(1 + κ_s) + O(1)B₃B₅M⁵)ε_kη² on Ω_k by LFR I (1.80), from the threshold of (1.75) (#3.71), not from the data of Z ∩ Λ^c, which pass χ_k only at O(1)M²L²R_kε_k (p.193 l.22–24)." |
| o4 | table #T11.33, LABELS | Stale labels; #T11.33 lacks "for a general base U₀" | With the table's owner (sent with LF a100b37e1628 at 07:36, and with db3245af7967 after this triage) |

## Checks

- **o3, re-derived.**
  - LFR I p.195 l.15–17 prints (1.80): abs(U_0(∂p) − 1) < 2ε_kη² + O(1)B₃B₅M⁵exp(−δ dist(p, Λ))ε_kη² for p ∈ Ω_k. #3.71 reads the first term with the note's κ_s, as 2(1 + κ_s)ε_kη².
  - p.193 l.22–24 prints that χ_k, χ″_k restrict the data at 2L₀^{2N₀}ε_k < 2L(L + 1)N₀^{−1}R_kε_k, which is R_k-sized.
  - So the O(ε_k) parameter comes from (1.80), as the referee says. Theorem 1 is not needed at the real step.
  - Consumer: #4.560-1.1.1 replaces ε_k by c_{rp}ε′_k at the real points through Proposition 1 and Theorem 1. That chain is unchanged and does not use the deleted words.
- **o1, re-checked.** CMP98 p.20 l.17 prints "Its Lie algebra 𝔤 is a subalgebra of the algebra of hermitian matrices". For X, Y ∈ 𝔤, (X + iY)* = X − iY, which gives the formulas. The operator norm satisfies abs(T*) = abs(T), so abs(A′_R) ≤ ½(abs(A′) + abs(A′*)) = abs(A′).
- **Line lengths.** #4.559 373, #4.559-0 361, and #4.560-1.1 594 characters.
- No CRLF. The only new tag is #4.559-0, which was unused in the LF note and the table.

## Pre-check of lf-p13b2-20261108-r15 (full)

- **Spec.** specs\spec_p13b2_r15.json at LF db3245af7967, prior lf-p13b-20261108-r14. --check gives 0 conflicts (5 allowed). Built: argument 18,048 characters, of which the context #4.559–#4.560-0 is about 3.3k and the reviewed lines about 14.8k.
- **Reading.** I read the whole part before 13b's full round, as recorded in WILSON_IT1_LF_TRIAGE_P13B_R14_2026_11_08.md (*Reading of 13b before its full round, and the split*). Since then only #4.564 has changed in 13b2.
- **Changed lines.** #4.564 now reads "the Lemma gives the bounds of #4.565–#4.568 per point of the history". #4.566 is in that range and is permitted background (§4(d)). In the context lines, #4.559 is split, and its new #4.559-0 is o1's repair.
- **Consumers of r10's and r15's repairs.** 13b2 cites #4.44-0.2, #4.46-1.1, #4.48.0, #4.48.0-0, #4.50-1.1, #4.50-1.1.1, #4.50-1.2, #4.559-1, #4.559-1.1, and #4.560-1.1.2. None of them was changed by 13a1 r10 (#4.44, #4.44-2-1, #4.46-0, #4.47, #4.47-0, #4.48-3, #4.48-3.0.0, #4.50, #4.50-1.1.1-1) or by o3 (#4.560-1.1).
- **New tags.** 13b2 is a new part name, so the gate finds no prior round of it. Its changed tag is computed by hand: #4.564.
- No known weak point and no OPEN is in these lines.

## Rounds

- 13b1: done (13b r14 narrow clean, 13b1 r15 full clean).
- Next: 13b2 r15 (full). Its count is 1 from 13b r14, so a clean r15 finishes it.
- Then 13a1 r11 (narrow), then a full r12.

## SHAs

LF a100b37e1628 (r15's snapshot) → db3245af7967 (o1–o3). Table 6d09b1b5054d (unchanged).

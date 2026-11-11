# Two-Loops Note: BETA Session's Triage, 11 November 2026

Note: `WILSON_IT1_TWO_LOOPS_UNIFORM_BOUND_2026_10_27.md` (TL), with `LABELS_TWO_LOOPS.md`. Owned by the BETA session since 01:48 on 11 November. SHA b734cba1137b after the repairs of 01:55 (824 lines, 774 tags in the note, 1446 with the BP_TL_* files, 221708 characters by wc -m); LABELS_TWO_LOOPS 07b7d5f8e1a3. Taken over at TL b94da3099515, LABELS_TWO_LOOPS e9023cc9fb4c.

## Open
- Nothing open in TL's text.
- Not reviewed since the October rounds: the 9 November tl-6ba to tl-6cb round was held and never launched, and the D_P block (#626–#647, #699-2–#699-4, #703, #714–#720, #728–#728.3, #255, #519, #287) was rewritten on 10 November. Rounds wait for the user's go.

## Awaiting
- Nothing.

## Transfer (01:48)
- User: "I transfer TL to you since the other session isn't working on it". The two-loops session confirmed at 01:5x: it no longer edits TL or LABELS_TWO_LOOPS.md. PC, NL, RP, NV, PF, the decay plan and the BP_TL_* files stay with it.
- Its queue for TL: (1) V4 line pins to replace by labels; (2) the held round, with no report pending and no unapplied repairs or unanswered findings; (3) its notes cite #290 (PF #PF4.4-4), #290 and #290-1 (PC #PC2.3, #PC7.2; NL #NL10.2, #NL10.7, #NL12.1; RP #RP.6, #RP.6-3, #RP.10-2; NV #NV.5-2, #NV.9), and #941. These tags do not move.
- Its logs, read as handover: WILSON_IT1_TWO_LOOPS_TRIAGE_TORUS_2026_11_11.md (current), WILSON_IT1_TWO_LOOPS_SELF_REVIEW_2026_11_09.md (closed), WILSON_IT1_TWO_LOOPS_CAUCHY_TRIAGE_PCRSTEP_R29_2026_11_07.md (the 10 November D_P entry), WILSON_IT1_TWO_LOOPS_TRIAGE_R1_2026_10_27.md (historical). All snapshotted.

## The torus hypothesis (01:50 to 01:55)
- Finding: #290 described V4's torus hypothesis for each loop as the square/torus condition K_μ ≥ 3(n_i + 2) alone, and #917 assumes "V4's torus hypothesis for each loop (#290)". V4's (H3) (sec:main-result *Hypotheses*, V4 64c07217fa40) also requires N_μ a multiple of LMR₁ exceeding 200LMR₁, K_μ > max(2, 2R_p + 8), and for (iii) N_min ≥ 4R_0 + (4/c)log(4n); thm:two-loop-theorem (iii) takes "the condition of (H3) for (iii) for each square". sec:two-loops-setting adds no condition relating the squares.
  - Nothing showed these on the fixed torus. Continuum #NWTOA.1-6–#NWTOA.1-7 (d598e46ff20a) now show them for one square for K ≥ K_tor(C); GL #GL1.5-3 did the same for general loops.
  - #290-1 also paraphrased #NWTOA.1 as "T_ph is a fixed multiple of u", which is now T_ph = 2L^{m_T}u, and gave "L ≥ 6 (#288)" where V4's standing L > 11 applies.
- Repairs in place:
  - #290: V4's torus hypothesis is (H3) of sec:main-result for each loop; the span bound uses its square/torus condition. "ℓ_i^{ph} = p_iL^{−q_i}u" is now the table's ℓ_i^{ph} (#T12.4-1), and the closing clause is shorter (626 → under 600 characters).
  - #290-1: T_ph = 2L^{m_T}u, m_T ≥ 0 (#NWTOA.1); "the condition" for "the hypothesis"; L > 11 (V4 eq:c-standing-conditions). The arithmetic is unchanged: T_ph − 3ℓ_i^{ph} ∈ uL^{−q_i}ℤ, positive, so ≥ uL^{−q_i} ≥ 6uL^{1−K}, as L^{K−1−q_i} ≥ L² > 6 for K ≥ q_i + 3.
  - New #290-2: (H3)'s other conditions (table #T12.31-1-2, table ae5e18927daf) hold on the fixed torus for K ≥ max_iK_tor(C_i) (#NWTOA.1-6–#NWTOA.1-7), so #917's hypothesis holds there for those K when 3ℓ_i^{ph} < T_ph.
- Consumers in TL: #596 (span bound, uses N_s ≥ 2max ℓ_i) and #917 (cites #290); both read correctly. #T12.31-1-2 was read before citing.

## V4 line pins (bookkeeping, 01:52 to 01:55)
- Each pinned line of V4 64c07217fa40 was read, with its section, last label and environment (scratchpad pin_labels.py), and the cited fact found on it.
  - L3590 (a_W = a^{(i)}_W; a_W := 0 for cross groups) → sec:two-loops-extraction, at #316 and #420. L3556 (χ̄_i), L3566 (domains free of the observable), L3560 (periodic δ_a; base points) → sec:two-loops-setting. L3727 → sec:two-loops-retreated. L1565 → sec:extent-weights.
  - L3571, L3574 → sec:two-loops-groups and rule (A2) of def:two-loop-groups. L3614 → lem:two-loop-source. L5249 → lem:c4-6-3. L5197 → eq:c4-6-1 (n(W) is defined in its lead-in). L5229 (2L halos) → proof of lem:c4-6-env.
  - L3658 ("Put c_× = 2η/A′_E") → sec:two-loops-cross. L3677 → "its proof of (a)". L3696 ("within 2L of D") → proof of lem:two-loop-cross. L3711 ("C_× is the largest of those above") → the last sentence of V4's proof of lem:two-loop-cross. L3644, L3709, L3737 dropped where the lemma or proof part was already named.
  - V3 L2806 (proof of lem:c5-5-8(a)) → V3 lem:c5-5-3(d), which states θ°(W) ≤ νσ(W)/16 (V3 a520a59f363d).
- No "L####" pin remains in TL.

## Pre-check
- Changed lines re-read: #290, #290-1, #290-2, and the 22 pin sites. labels_two_loops.py passes (1446 tags, every cross-reference resolves).
- Lines over 600 characters: #286 (625) and #654 (621), both unchanged and under the 630 the previous owner split at, and five at 602–607. None was touched.

## Messages sent
- 01:48 to the two-loops session: the transfer, the state taken over, and the request for its queue. 01:49 to the table session: the transfer.
- 01:56 to the two-loops session and the table session: TL b734cba1137b, LABELS_TWO_LOOPS 07b7d5f8e1a3, with #290-2.

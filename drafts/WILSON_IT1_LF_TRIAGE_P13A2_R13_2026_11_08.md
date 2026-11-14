# Triage of lf-p13a2-20261108-r13

## Verdict

- r13 was the full round of 13a2 at LF a6bf083f0336, table 6d09b1b5054d, and labels 971e7d7d5325.
  - Under review: #4.51–#4.55-1-1.
- **Fatal:** none. **Serious:** none. **Minor:** none.
- **Trivial:** five, t1′–t5′.
- The round is **clean**. r12 (focused) was clean, so this is the second consecutive clean round and the full one. **13a2 is done.**
- Round 12's t1–t4 were confirmed repaired.

## Repairs

| Finding | Line | Issue | Repair |
|---|---|---|---|
| t1′ | table #T11.33; LABELS | "It is not the absolute axial gauge (1.15)" needs "for U₀ ≠ 1"; LABELS is stale (#4.51-2-1, #4.52-1-1.1-1 missing) | Both belong to the table fork, which was asked at 05:50 and with every SHA since. No reply yet |
| t2′ | #4.52-1-1.1 | REG's base U₀ and LFR I's U_0 differ only by glyph | "at REG's base U₀, written U_{REG} := Q^{s*}_kV_Λ here, REG's U′U₀ being LFR I's U_0". U_{REG} occurs nowhere else in the LF, the table, or the Cauchy note |
| t3′ | #4.54-0.1.1 | "#4.20" is a tag of balaban_proofs/BP_JOINS_BLOCK_SIZE.md, cited without the file | "the rate of balaban_proofs/BP_JOINS_BLOCK_SIZE.md #4.20". The same pointer is fixed at its three other uses (two §0 status lines and one line of §4(d)), as bookkeeping |
| t4′ | #4.52-1 | The extension of run A's u₀ to run B's finer lattice was unstated | "... use run A's ū₀, extended to run B's lattice in any way, since the shared-scale data see it only at the block points and the compensations act on the coarse variables" |
| t5′ | #4.54-0-1 | ε_{D″} could be (1 + 2πLc_{δD})ε₁ | No change: the stated (2 + 2πLc_{δD})ε₁ is valid, and it enters C_pr and the regularity of #4.54-1 (2ε₁ ≤ ε_{D″}), so tightening it would change reviewed constants without changing any result |

## Checks

- No CRLF. Line lengths: #4.52-1 472, #4.52-1-1.1 489, and #4.54-0.1.1 525 characters.
- t2′, t3′, and t4′ are rewordings and pointers that change no bound. So 13a2 stays done. #4.52-1 and #4.52-1-1.1 are also lines of 13b, which reviews them in r13.

## Rounds

- 13b r13 (narrow) is next, then 13a1 r9 (focused). 13b then needs a full round, and 13a1 a full r10.

## Pre-check of lf-p13b-20261108-r13 (narrow)

- **Spec.** specs\spec_p13b_r13.json at LF a0e16b2810b8, prior r12. --check gives 0 conflicts (2 allowed). Built: 5,619 characters of argument.
- **Changed tags since r12 (7), all under review:**
  - **#4.52-1:** 13a2 r13's t4′, the extension of ū₀. The compensating transformations of LFR I p.197 l.39–42 act on V_h and V′, coarse variables, and the shared-scale data are averages that see a gauge transformation only at the block points (CMP 98 (15) is covariant under u at c₋ and c₊).
  - **#4.52-1-1.1:** 13b r12's m1 and o2, and 13a2 r13's t2′.
  - **#4.52-1-1.1-1:** 13b r12's o1. The identity is checked against CMP 98 (15), p.019 l.41–47, and CRE (1.3), p.246 l.39–44.
  - **#4.52-1-2:** 13b r12's o3.
  - **#4.561.1-1.3-1.0** and **#4.561.1-1.3-1.0-1:** 13b r12's o4, the identity theorem, with LFR I (1.79), p.195 l.7, checked.
  - **#4.567-1:** 13b r12's o5. #4.561-1.2 states C_{V′}ε₁′ ≤ ½.
- 13a2 r13 found #4.52-1-1.1, #4.52-1-1.1-1, and #4.52-1-2 correct in their r12 wording, before t2′.
- No new symbol except U_{REG}, which clashes with nothing. No known weak point and no OPEN is in these lines.

## SHAs

LF a6bf083f0336 → a0e16b2810b8. Table 6d09b1b5054d (unchanged).

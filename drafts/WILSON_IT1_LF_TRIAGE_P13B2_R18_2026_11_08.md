# Triage of lf-p13b2-20261108-r18

## Verdict

- r18 was a narrow round of 13b2 on r17's repairs and their consumers, at LF 179b7dab2854, table 6d09b1b5054d, and labels 971e7d7d5325.
- **Fatal:** none. **Serious:** none. **Minor:** none.
- **Trivial:** t1–t5, exposition only, repaired below by rewording.
- r17's m1 was confirmed repaired. The referee re-derived from the transcriptions:
  - CMP98 (105)–(106) with R(X)Y = XYX^{−1} (p.27);
  - REG (1.70)–(1.72);
  - CMP98 §D at 𝔤^c-valued fields;
  - |u − 1| ≤ e^s − 1 without unitarity;
  - −log(2 − e^s)/s increasing;
  - the arithmetic of #4.561.1-1.3-2 and C_{V′};
  - #4.563-3-0's |X − 1| ≤ ¼.
- The round is **clean**, so 13b2's count is 1. The next round, r19, is full.

## Repairs

| Finding | Line | Issue | Repair |
|---|---|---|---|
| t1 | #4.517-0 | "the real U₀" overloads LFR I's U_0, complex at z | "a transport of the real base U₀ of VAR's axial gauge (not LFR I's U_0)" |
| t2 | #4.517-0 | REG p.88 l.37–38 states (106) for the inductive u₁ | "(REG p.88 l.37–38, stated there for the inductive u₁, and so at each k)" |
| t3 | #4.517-1 | L^{n+1−j} reads REG's printed L^{n+l−j} | "(REG prints L^{n+l−j}; n + 1 − j is a reading, inferred, not printed, which (1.72)'s factor 1/(1 − L^{−1}) requires)" |
| t4 | #4.561-1-2 | The transfer of REG (1.71)'s smallness to ε₂^{AL} is unwritten | "and 256dε₂ ≤ 1 and the smallness of ε₂ in REG (1.71) give its 256dε₂^{AL} ≤ 1, 128dε₂^{AL} ≤ 1, and that smallness at ε₂^{AL}" (the line's first sentence states the monotonicity) |
| t5 | #4.563-2.2 | c_4 needs 2ε₁′ ≤ 1 | "by ε₂ < α₁, and 2ε₁′ ≤ 1 by (T-c)'s 16C₀^{ms}ε₁′ ≤ 1" |

- **Split.** #4.517-1 became 612 characters with t3, so its second sentence ("So the exponents of u's factors sum …") is now #4.517-1-1. Citations of the range #4.517-1–#4.517-2 still cover it.

## Checks

- **t5.** (T-c) has 16C₀^{ms}ε₁′ + 16ε₂ ≤ 1 and C₀^{ms} ≥ 2 (#4.48.0-0), so ε₁′ ≤ 1/32 and 2ε₁′ ≤ 1/16.
- **t4.** REG's smallness of α₀ + α₁ in (1.71) is an upper bound on ε₂, so it is monotone. At the base 1, ε₀ = 0 and ε₂^{AL} ≤ ε₂/4.
- **t1.** VAR Proposition 2's base is the U₀ of Ax_k(𝔅_k, U₀) (VAR p.281 l.28), real. LFR I's U_0 is written with a subscript zero in the note and is complex at z. The rewording separates them.
- **Line lengths.** #4.517-0 586, #4.517-1 448, #4.517-1-1 192, #4.561-1-2 554, #4.563-2.2 564 characters. No CRLF.

## Pre-check of lf-p13b2-20261108-r19 (full)

- **Spec.** specs\spec_p13b2_r19.json, prior r18. Under review: the whole part, #4.561–#4.565-1 and #4.567–#4.568, plus #4.517–#4.517-2 with #4.517-1-1, which 13b2 uses. Context: #4.198-1, #4.517-3–#4.517-5, and #4.559–#4.560-0.
- **Reading of the whole part.** I read all of 13b2 (LF #4.561–#4.568) before r18, at LF 14a59772400b. The two points that reading found (#4.563-3's |X − 1| ≤ ½ and #4.563-2.2's own layers) were repaired in r17's triage and confirmed in r18. Every line changed since then was re-read in place: r17's m1 repairs and r18's t1–t5. No other gap was found. Checks:
  - (T-c)'s list against its uses: 256dε₂ ≤ 1, REG (1.71)'s smallness, C_{V′}ε₁′ ≤ ½, 16C₀^{ms}ε₁′ + 16ε₂ ≤ 1, ε₂ < α₁, C^c_Jε₁′ < α_J, and LFR I Proposition 1 at 20C_{V′}ε₁′;
  - #4.561.1-0's 54 ≤ C_c = 60 and 27c_avα̂₁ ≤ 1;
  - #4.561.1-2's max over the data moves;
  - #4.563-1.1's 16c_avε′_k;
  - #4.563-2.1's (2 + 8C₀^{ms}ε₁′ + 16ε₂)ε₂;
  - #4.563-2.1-1's c_pl;
  - #4.563-3-1's count;
  - #4.565-1's exponent (1 − ε₀)/3 · 15/16 = 5(1 − ε₀)/16;
  - #4.567-1's 13/16.
- **Changed since r18:** #4.517-0, #4.517-1, #4.517-1-1 (split), #4.561-1-2, #4.563-2.2.
- **Symbols.** Grep found no stale c_Gd or r_G in the LF. t_n is local and does not clash. Table rows #T12.9-1, 464 and 466 are stale and with the table's owner; the spec says so.
- **Size.** Built at LF d8bf3d14487a: argument 23,622 characters, 28 files, definition check 0 conflicts (7 allowed).
- No known weak point and no OPEN is in the part. #4.536-2's open item (packet 42, complex base) is outside 13b2, and 13b2 does not cite it.
- **Rounds.** 13b2: count 1. r19 (full) would make it 2, and 13b2 done.

## SHAs

LF 179b7dab2854 (r18's snapshot) → d8bf3d14487a (t1–t5, split). Table 6d09b1b5054d and labels 971e7d7d5325 (unchanged; relabel and rows pending with the table fork).

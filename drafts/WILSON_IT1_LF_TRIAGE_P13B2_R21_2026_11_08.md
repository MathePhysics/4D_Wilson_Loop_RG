# Triage of lf-p13b2-20261108-r21

## Verdict

- r21 was a narrow round of 13b2 on r20's repairs, at LF 6ce650aff3e6, table 6d09b1b5054d, and labels 971e7d7d5325.
- **Fatal:** none. **Serious:** none.
- **Minor:** m1, in the consumer #4.567. Its weight route multiplied the absolute weight difference by "the disc bound of a density". The only disc bound stated for the unweighted density carried g_{j(x)}^{−2}, which is not slack against the real form Cε₁′²(abs(δ_{j(x)}) + abs(δ_k)) of #4.168 and #4.191.
- **Trivial:** t1–t3.
- r20's m1′ and t-a–t-c were confirmed repaired. The referee re-derived d_y unweighted from #4.44, #4.48 and #4.51-0, the Lemma's C_dc(M) = max(C_y(M), 2C_act), and #4.561.1-1-0's openness step.
- The round is **not clean**, so the count stays 0. The next round, r22, is narrow.

## Repairs

| Finding | Line | Issue | Repair |
|---|---|---|---|
| m1 | #4.567, with #4.563-3, #4.563-3-1, #4.565-1 | The g-free disc bound of the unweighted density was not stated, so #4.567's product carried g_{j(x)}^{−2} | The bound is stated once, in #4.563-3: "≤ C_actε₁′² there unweighted, and ≤ C_actg_{j(x)}^{−2}ε₁′² with the weight (g″)^{−2}"; #4.563-3-1 applies the weight "in the weighted density"; #4.567: "times the disc bound C_actε₁′² of an unweighted density (#4.563-3)" |
| t1 | #4.561.1-1, #4.561.1-1-0 | W(·) undefined, and W has ten note-wide definitions | V^e(z) := V_k(z)V_k(0)^{−1} defined in #4.561.1-1 ({#D.V^e(z)}, unused before); B^e(z) := (1/i)log V^e(z); #4.561.1-1-0 written with V^e |
| t2 | #4.565 | "regular with ε₁′ (#4.51-1.1)", where #4.51-1.1 states ε₁ | "(#4.51-1.1 with ε₁′ for ε₁, #4.560-0)" |
| t3 | #4.565-1 | The weighted-to-unweighted inference needed "termwise" | No longer an inference: #4.565-1 cites #4.563-3's unweighted bound, "≤ 2C_actε₁′² ≤ 2C_actg_{j(x)}^{−2}ε₁′², each run's unweighted density being ≤ C_actε₁′²" |

## Checks

- **m1.**
  - #4.563-3-1's count without the weight gives ½d(d − 1)(c_plC₀^{ms}ε₁′)² ≤ C_actε₁′² per point, each term ≤ (c_plC₀^{ms}ε₁′)² by #4.563-3-0 and #4.563-2.1-1.
  - With the weight, the factor is ≤ 2g_{j(x)}^{−2}, which gives C_actg_{j(x)}^{−2}ε₁′².
  - #4.565-1's disc input to the Lemma is 2C_actε₁′² ≤ 2C_actg^{−2}ε₁′², by g_{j(x)} ≤ 1 (#4.565-0), so C_dc(M) is unchanged.
  - #4.567 now has the weight difference times C_actε₁′², the real form.
- **Consumers.** #4.567-0 cites the range #4.563-2–#4.563-3-1, which still holds. #4.198-1 does not use C_act. Table row 466's C_act := d²(c_plC₀^{ms})² is unchanged.
- **Symbols.** V^e is new; Grep found no other V^e in the LF or the table. It goes to the fork for the relabel.
- **Line lengths.** #4.561.1-1 411, #4.561.1-1-0 486, #4.563-3 197, #4.563-3-1 524, #4.565 581, #4.565-1 269, #4.567 502 characters. CR count 0.

## Pre-check of lf-p13b2-20261108-r22 (narrow)

- **Spec.** specs\spec_p13b2_r22.json, prior r21, extracts as in r21.
- **Named steps.** The changed lines #4.561.1-1, #4.561.1-1-0, #4.563-3, #4.563-3-1, #4.565, #4.565-1 and #4.567, with their consumers #4.567-0, #4.567-1 and #4.568.
- **Changed since r21.** The seven lines above, each re-read in place.
- **Cited lines re-read:** #4.560-0 (the real points regular with ε₁′); #4.168 and #4.191 (the real coupling form), through the referee's quotation and the note's tags.
- **Size.** Built at LF 81ef3601b01c: argument 24,959 characters, context extracts included (r21: 24,909), 28 files. The spec now marks #4.517–#4.517-5 as context only, as no line of it changed.
- No known weak point and no OPEN is in the part.

## SHAs

LF 6ce650aff3e6 (r21's snapshot) → 81ef3601b01c (m1, t1–t3). Table 6d09b1b5054d and labels 971e7d7d5325 (unchanged; relabel and rows pending with the table fork).

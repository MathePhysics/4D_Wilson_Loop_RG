# Triage of p12b r9 (lf-p12b-20261106-r9, 7 Nov 2026)

**Verdict.** Clean: no fatal, serious, or minor findings, and three trivia. It was a full round, and the referee opened every cited page in the print, including the steps r8 had checked only against quotations. r8 and r9 are two consecutive clean full rounds, so **part 12b (#3.63–#3.100-1) is done**. I read the whole part myself before r7.

## Repairs (wording and citations, in place)

| Trivium | Words at stake | Repair |
|---|---|---|
| t1, #3.97 and #3.100-1 | pp.382–383 named only through #3.100-1's general sentence | New #3.97-1 names the passed regularity there: abs(V₀(b) − 1) < O(1)B₃²B₅M⁶L^{−N}ε_j (p.382 l.10–16), used against L^{−N} (l.23), and the first-order term ‖B‖²O(1)B₃⁴B₅M⁶R_jε_j (l.39–40), used for γ small. Both absorb 1 + 2κ_s. Checked against the corrected file. |
| t2, #3.97 against #3.92 | "so they hold at t" | Now "at the soft test's threshold t of #3.17". #3.92's t := M₀p₀(g_k) is already in allow_defs. |
| t3, #3.76 | "LR_{h+1} ≥ R_h (CRE (2.5)–(2.6))" | Now cites CRE (2.9) (p.256 l.15): R_h < L²R_{h+1} for γ small, and the R_j are powers of L by (2.5). Checked against the corrected file l.13–15. |

**Non-findings, unchanged.**
- #3.94-1's abs(Λ^{(k)}) is the union bound over the shell's bonds.
- The referee notes that Bałaban's p.378 l.14 "χ is also equal to 1" needs a factor π/2, which #3.96's factor 2 in M₀ supplies.

**Round needed?** No. These are a citation, a disambiguation, and one coverage line that restates bounds the referee checked in the print (bookkeeping, §6). They will be seen by the next content round of any packet that reads part 12b.

**Pins.** LF c80c74a09439 (labels 8cb018ead815), table 1e392e405632. Every line of the part is ≤ 610 characters.

## Re-opened (8 Nov 2026) and pre-check of lf-p12b-20261108-r10 (narrow)

- **Changed since r9's snapshot** (diffed tag by tag):
  - #3.76, #3.97 and #3.97-1: r9's trivia, above.
  - #3.96-1-1: 13a r5. V′ is the deviation from V′^X₀.
  - #3.85.1 and the new #3.85.1-1: 13b r3. The locality citation is re-pointed to RG I (0.4) and (0.12), and the line is split.
  - #3.99-1: the name (RS) only.
  - #3.70-5 and the new #3.70-5-1, repaired here.
- **#3.70-5, a weak point found in the diff.** After r9 the line had become "So the spaces contain the real configurations of the soft supports, each of their conditions checked at these constants in #3.70-1–#3.70-4". But #3.70-4 shows only that, on the domains outside (1.24), the soft supports are Bałaban's supports at (1 + 2κ_s)A₀ and (1 + 2κ_s)A₁. It does not check the space conditions there. Repaired in place:
  - #3.70-5 keeps the constants and the descent;
  - the new #3.70-5-1 reads: (1.24)'s domains by #3.70-1–#3.70-3; the others because the configurations are Bałaban's supports at these constants, which his spaces contain, as his bounds on the terms of (1.63) on them require (p.191 l.49–51; inferred, not printed).
  - This is r8 and r9's reading, now labelled again. #3.70-5-1 was checked unused before creation.
- **Re-derived.**
  - #3.96-1-1: ε₁ = C(M)R_kε_k ≥ 8(1 + κ_s)M₀ε_k (#4.152), and #4.50-0's polydisc has radius 2C₁ε₁ in Y with C₁ ≥ 1.
  - #3.85.1: checked in 13b r3 against RG I p.253 and p.254 l.2–6.
  - LFR I pp.190–191 re-read for #3.70-5-1. CRE p.259 l.40–50 re-read for C₀ and C₁.
- **Whole part read** (#3.63–#3.100-1) on 8 Nov 2026 at LF 87e0431cfd68. No other gap was found.
- **Spec.** specs\spec_p12b_r10.json, prior r9. Named steps are the changed lines with their consumers #3.70-4, #3.85-1, #3.86-1-1, #3.91 and #3.100-1. The definition check gives 0 conflicts (4 allowed).
- **Order.** It launches after 13b2 is done (r20 narrow, then a full round). Rebuild at the then-current LF; re-diff if the part changed.
- **Lines.** #3.70-5 323, #3.70-5-1 366 characters. CR 0.

## Pre-check of lf-p12b-20261109-r10 (narrow; 9 Nov 2026 03:03)

The 8 Nov build was not launched, because the consolidation came first. It was rebuilt at LF c3321e0e4802 (labels 3851174fe014, table 72a5f3ad7918).
- **Re-diffed against r9's snapshot.** No change to the named steps' text since the 8 Nov pre-check. The consolidation re-pointed section pointers to tags in #3.69 ("above" dropped), #3.82 (#3.74–#3.79), #3.83 (#3.89), #3.94 (#4.45-1), #3.94-1 (#4.43-1.2), #3.95 and #3.96-1 (#C8.6.5–#C8.6.8-1), and #3.100 and #3.100.1 (#3.45, #3.100.1). These are now named steps (claim (vii)).
- **Pointers checked.** Each resolves to the text it names:
  - Cauchy #CP.13: the R_j are powers of L.
  - BP_DERIVED_CONFIGS #BC.3-2: locality of Ū^n.
  - #4.45-1: κ_Λ.
  - #4.43-1.2: C(M).
  - #C8.6.5–#C8.6.8-1: the denominator.
  - #4.50-0: C₁ ≥ 1.
  - #3.17: the soft test's t.
- **One pointer repaired.** #3.96-1-1 said "the polydisc of #4.152", but the polydisc P := {‖Y‖_∞ < 2C₁ε₁} is defined at #4.46. It now reads "the polydisc P = {‖Y‖_∞ < 2C₁ε₁} of #4.46". #4.152 is still cited for C(M) ≥ 8(1 + κ_s)M₀ and its use.
- **CRE (2.9) re-read** in the corrected p.256, l.14–15. R_m ≤ L(1 + g_n²β′(n − m))^{β₀}R_n at m = h, n = h + 1 gives R_h < L²R_{h+1} for γ small, and R_h ≤ LR_{h+1} since the ratio is a power of L. This matches #3.76.
- **Whole part re-read** (#3.63–#3.100-1) on 9 Nov. No other gap was found.
- **Size.** The part is 25.9k characters (r9: 25.1k), so the full round needs it ≤ 25k first. This narrow round reviews only the named steps. No line of the part is over 600 characters, and CR is 0.
- **Spec.** specs\spec_p12b_r10.json, rev lf-p12b-20261109-r10. Definition check: 0 conflicts (4 allowed).

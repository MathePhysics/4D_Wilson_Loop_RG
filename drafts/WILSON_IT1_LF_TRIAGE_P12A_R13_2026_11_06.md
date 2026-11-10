# LF packet 12a, round 13 (full): triage

Review: verification/isolated_reviewer/reviews/lf-p12a-20261106-r13/review.md. Under review: LF 91951cbcc102 (labels 946fae7624bf).

## Verdict

Clean: no fatal, serious, or minor finding. r12 (focused) was clean, so this is the second consecutive clean round and the full one. **12a is done.**

## Cosmetic findings, all repaired

- **r13-c1 (LF #3.28-2-1).** "on the support of the soft (1.27), where abs(B′_j) < 6δ′_j at the soft threshold" was loose. It now reads "where the (1.27) argument is < (1 + 2κ_s)2δ′_j, abs(B′_j) < 6δ′_j (#3.28-1)", the set #3.28-1 actually bounds.
- **r13-c2 (LF #3.28-2-2).** "the small solution of (1.22)" had no pointer. It now names it as the solution on which (1.22)'s printed expansion holds, with 𝐅 the Baker–Campbell–Hausdorff terms of order above 1 (CRE p.251 l.45–46, p.252 l.6–8). To keep the line under 600 characters, the bound on ℍ_Z^{(j)} moved into #3.28-2-3, which now opens with it. No bound changed.
- **r13-c3 (Cauchy #C6.2.1-7-1).** The renaming of Z_k∖Z as Z_k now cites LFR I p.201 l.11 ("We denote Z_k∖Z by Z_k"). The LFR I p.179 l.40 pointer, which did not print the renaming, is dropped.
- **r13-c4 (table #T11.26).** The row now quotes CMP98 (21)–(25) (p.21 l.26–50), including (24)–(25): abs(U − 1) ≤ abs(log U) ≤ (π/2)abs(U − 1) for every unitary U.

## Correction to r12's triage

r12's triage said #3.86-1 and #3.96 needed abs(v − 1) < 1. CMP98 (25) prints the (π/2) bound for every unitary, so that condition was unnecessary. It is removed from both lines, which again read "for unitary v (#T11.26)", and the r12 triage is corrected in place.

## Pre-check of the repairs

- #3.28-2-1 to #3.28-2-3 re-read in full: 584, 403, and 532 characters. #4.634 still cites #3.28-2–#3.28-2-3, which covers the moved sentence.
- CRE p.251 l.44–46 and p.252 l.2–10 and LFR I p.201 l.11 re-read in the parts files.
- The changes are outside the 12b packet's reviewed blocks except through #T11.26, which the next 12b round will see.

## Hashes after repair

- LF ccbb6b4a5962 (labels e4a1a9927b1f).
- Table 1e392e405632.
- Cauchy 4138f0908f6d.
- D2.7 22e10e0cd238 (unchanged since the c_ext integration).

## Message to the two-loops session (21:19)

Sent: the four SHAs; the #T11.26 row's new quote of CMP98 (21)–(25); and the correction that the (π/2) bound holds for every unitary, not only for abs(v − 1) < 1, as I had said earlier. I also noted that its specs, pinned to LF 91951cbcc102, need re-pinning.

# LF review, part 12a, round 12: triage and repairs (6 Nov 2026)

Review: `verification/isolated_reviewer/reviews/lf-p12a-20261106-r12/review.md`, LF 036c68e6658f, a focused round on the r11 repairs. Result: 0 fatal, 0 serious, 0 minor, and 2 cosmetic (k12-1 and k12-2). All of r11's findings (m11-1, c11-1 to c11-4) were confirmed repaired. **Clean**: the first clean round. r13 must be a clean full round of the part.

## Repairs

- **k12-1 (LF #3.28-2): the bound of g_jB_j by π had no source.**
  - The bound was cut from #3.28-2. The (1.59) coupling part is now derived in three new sub-lines, #3.28-2-1 to #3.28-2-3.
  - #3.28-2-1 gives CRE (1.22) as printed (p.251 l.44–46): the old variable is (1/(ig))log of exp(ig·new)·exp(−ig_cℍ), the new variable being A′, renamed A (p.252 l.19–20: "the new variables A′ by A"), with ℍ_Z^{(j)} in place of 𝐇_{1,Ax} by p.188 l.35. The change acts on χ′_j(1 − χ′^{(j)}) (p.188 l.37), so on the support of the soft (1.27). There B′_j is below 6δ′_j by #3.28-1, which rests on (1.54) and p.187 l.52.
  - #3.28-2-2 takes the new variable as the small solution of (1.22).
    - Where g_c = 1, g_jB_j is (1/i)log(e^{iB′_j}e^{iℍ}), with the power series of CMP98 (21). The Baker–Campbell–Hausdorff formula and the size of ℍ (p.188 l.33–34, smaller than any power of g_j, against δ′_j ≥ A₁g_j) then give a bound below 7δ′_j.
    - Where g_c < 1, the tested quantity is below 2δ′_j (#3.69, CRE p.252 l.2–3), and the (π/2) bound of #T11.26 gives πδ′_j.
  - #3.28-2-3 concludes: the (1.59) part is at most (7/2)C_{2.10}g_j² times the size of δ_j, up to #3.28-1's factor between the runs.
- **k12-2 (LF #3.28-2-1): the range.** The bound is stated wherever min(x^A, x^B) < 1 + 2κ_s, the range of #3.32, in the run attaining the minimum. That run's point lies on the support of the soft (1.27) at the threshold (1 + 2κ_s)2δ′_j (#3.69), where #3.28-1 gives the bound on B′_j. Constant check: about 3.5C_{2.10}, plus the threshold's part (1 + 2κ_s)C_{2.10}, is about 4.5C_{2.10}. That is below #3.31's 4C ≥ 4(2 + κ_s)C_{2.10} ≈ 8.0C_{2.10}.

## Errors in the first versions of the repair, caught before any launch

- **A reading presented as an inference.** The first version said "the branch is the principal one, as p.187 l.52 infers …". That reads a convention into Bałaban from a downstream inequality. The user objected, and the version was removed.
- **The direction of (1.22) reversed.** The second version wrote the new variable as a function of the old. The print gives the old as a function of the new (p.252 l.20). The check against the transcript found this.
- **A false bijection.** The third version took the new variable with eigenvalues in ]−π, π] and claimed that (1.22) maps that domain one-to-one onto the old one. That is false for a general compact G: under the charge-(1, 2) embedding of U(1), the principal log of an element of G can leave 𝔤. Removed. The final version needs no global branch, since the change acts only where the old variable is small.

## Bałaban's logarithm (new table row, announced to the fork before the edit)

- **The row.** #T11.26 quotes CMP98 (21)–(25) (p.21 l.26–50). (21) is the power series for abs(X − 1) < 1, "an inverse to the exponential function". (22)–(23) are spectral, with eigenvalue angles in ]−π, π], for unitaries. (24)–(25) print abs(U − 1) ≤ abs(log U) ≤ (π/2)abs(U − 1) for every unitary U. A grep of the parts files for "logarithm" and "principal" finds no other definition.
- **The uses.** Every (π/2) bound on a logarithm in the live notes now cites the row: LF #3.86-1, #3.91, #3.96, #3.96-1-1, and #4.7-1-4-1-1, and Cauchy #C9.7.1-6 and #C9.7.1-8.
- **#3.86-1 and #3.96** state the bound "for unitary v". CMP98 (25) prints it for every unitary, so they need no condition on abs(v − 1).
- These are citation repairs in lines outside 12a: 12b is to be reviewed, §4(a) is done, and Cauchy §9 is to be reviewed. They are logged here and in the handover, and the next content rounds will see them.

## Wider implications

- #4.634 cited #3.28-2 for the coupling part; it now cites #3.28-2–#3.28-2-3. This is re-pointing only.
- No other line cites #3.28-2's sub-lines (grep of LF, Cauchy, and the table).
- #3.28-1's bound on B′_j for (1.27) uses the soft threshold (1 + 2κ_s)2δ′_j, the same range as #3.28-2-1.
- D2.7 has no (π/2) bound on a logarithm (grep).

Line lengths: #3.28-2 is 474 characters, #3.28-2-1 598, #3.28-2-2 499, and #3.28-2-3 285.

Hashes: LF 91951cbcc102, labels 946fae7624bf, table 25bbcd6bd3f0, Cauchy e77bf64f6f2f. D2.7 05b327829cca is unchanged.

## Peer message (two-loops session, 20:54): D2.7's c_ext

- **The request.** TL (99397a886835) changed c_ext to (1+β₀)/(2LKC_mJ) at #167-1, with C_mJ := max(1, C_{(2.35)}, C_{(2.37)}) at #167-1-1. Both lines were read in TL.
- **Re-derived.** r^{ext}_k ≤ c_extα_{0,k} gives C_mJ·2Kr^{ext}_k ≤ ((1+β₀)/L)α_{0,k}. That is TL #6.16.4-2-1's condition for the derived configurations' change, which stays within #6.16.4-1's fractions of the rooms. D2.7 15.6(d) needs the points within 2r^{ext}_k to satisfy TL's (R-eval)(iv), so it needs TL's c_ext.
- **The edit.** D2.7 15.6(d) now reads c_{ext} := (1+β₀)/(2LKC_mJ), with VAR Proposition 9's K and C_mJ of two-loops #167-1-1, fixed after L and M (two-loops #167-1).
- **The consumer 15.7.** C_mJ depends on d, L, β₀, β_H, and G only, so 1/c_ext is still fixed after L and M. r^{ext}_k is still g_k times a polylog, and C^R_k's form is unchanged.
- **Clashes.** C_mJ does not occur in LF, the table, or Cauchy.
- D2.7 is now 22e10e0cd238.

## Pre-check for lf-p12a-20261106-r13 (built, not launched)

Spec `specs/spec_p12a_r13.json`, lf_sha 91951cbcc102. This is the full round of the part, with r11's extracts: #1.1–#1.2-1, #3.16–#3.62-1, #5.6, and #5.66–#5.66-2. #T11.26 and CMP98 (21)–(22) are added to the sources and the permitted background. Definition check: 0 conflicts (1 allowed). Packet: 29,603 argument characters. r11 had 27.8k, which the user accepted. The growth since then is the derivations added in the r11 and r12 repairs.

Changed LF tags (the gate's list, 4): #3.28-2, #3.28-2-1, #3.28-2-2, and #3.28-2-3.

Checks:
- **Whole part read.** I read the part's extracts in full before the build. No new gap was found. Its cited supports outside the part were re-derived in r11's *Recheck*, apart from those of the new lines.
- **Citations of the new lines,** re-read in the transcripts: CRE p.251 l.44–46 and p.252 l.2–3, l.19–20; LFR I p.187 l.43–54 and p.188 l.33–37; CMP98 p.21 l.26–39.
- **No reading presented as derived:** the new variable as the small solution is a construction stated as such.
- **New symbols:** g_c, CRE's cutoff, which occurs nowhere else in LF or the table.
- **Wider implications:** done (above).
- **Lines ≤ 600:** yes.
- **Linear order:** 12a r13, then 12b r3.

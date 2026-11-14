# Background-Iteration Closure, Round r4 (it1-bg-20261109-r4): Pre-Check

Packet: reviews\it1-bg-20261109-r4. It is hand-built in the format of it1-bg r2/r3, because build_packet extracts only tagged lines and this note has none. The YM4 files the referee reads are frozen copies in the snapshot folder:
- note 3d283bfdbfdd (176 lines);
- D2.7 e88981b21801;
- map 7e6f1e0e4136;
- Cauchy 648f51a2e090;
- table ef7efc104801;
- LABELS b0b6c48b2471.

The argument is 13.8k characters in total, under the 25k limit. Under review: snapshot l.63–72, l.74–76, l.143 and l.153–156. Context: l.51–59, l.61–62 and l.102–103.

## Pre-check

- **Changed lines re-read, every step re-derived (9 Nov 2026, 12:3x):**
  - the bracket bound, using ι_{T,j} ≥ s_j/2 − ρ_dep and MR_j ≥ 1;
  - 2s+1 ≤ MR(8/c+1)(2y+1), since the right side is ≥ 4s + 1;
  - (1+x)e^{−x} ≤ 2e^{−1/2}e^{−x/2};
  - CRE (2.5), read as R_j < L(log g_j^{−2})^r because R_j is the least power of L above (log g_j^{−2})^r, with (log g_j^{−2})^r ≥ 1;
  - CRE (2.7), both lines, with n = K and m = j, for general p (p.255);
  - (MR_j)² ≤ R̂_K²m̂^{1/2} ≤ R̂_K²L^{m/2};
  - the exponent bound ≥ aL^{m/2};
  - the sum lemma's proof at a real base ≥ 2, including its m = 1 case for a ∈ (½, 1), where 2ae^{−a} ≤ 2/e;
  - the factor bound, with (e^{0.1} − 1)/0.1 = 1.0517;
  - the log r_j 𝐑-part, ≤ 2C^{R∨}_E e^{−p₀/4}(P + 4);
  - the perimeter sum, with P_{j−1}(C) = 4ℓ_CL^{K−j+1}.
- **Weak point repaired before launch:** the reading of "c in MR_k-cube units". The line now states the reading and shows the other reading gives larger exponents.
- **Every use of the touched bounds grepped:**
  - C_Σ𝔞̄ appears at l.63–64, l.71, l.75 and l.143, plus (C5);
  - E^f_{const} appears at l.51, 59, 85, 87, 121, 136 and 143;
  - l.85/87/136 keep Re E^f_{const,K} unbounded, so they need no change;
  - l.143 is updated.
- **Symbols checked against the table and the note:**
  - 𝔯 (#D.𝔯), 𝔢(z), ρ_K^ℓ and C₁ (note l.146) were taken;
  - the new names r^R_K, r^{R,g}_K, r^{R∨}_K, ê^R_K, R̂_K and C^R_1 are unused.
- **Quotations checked against the snapshot:**
  - 15.4(ii)'s bound and its "c in MR_k-cube units" (D2.7 l.136);
  - N_min ≥ 2s_k (l.132);
  - μ_k^R and ζ_k^R (l.136);
  - map #MD2.0.5.40 (l.1234), #MD2.3.5.5-2 (l.3333) and #MD2.3.6.3 (l.3359);
  - Cauchy #C7.6-7-1 (l.993);
  - CRE (2.4)–(2.7) (p255_corrected l.31–60).
- **Size of §3.2:** the second term and *Size of N_k* grew from about 1.7k to 4.6k characters. All of the growth is the new derivation of r^R_K and the κ^R part of r_j; no text was restated.
- **Lines:** all lines in the repaired block are ≤ 600 characters. l.65 was split.
- **Known open items, outside this packet's claim:**
  - r^{R,g}_K rests on (C6)'s "D2.7's inputs for the coarse chain", a stated condition;
  - Cauchy #C7.6-3 and two-loops #884 misquote 15.4(ii); both are reported to their owners.

## Triage (report read in full, 12:44)

**Verdict.** Not clean. There is no fatal finding. The referee found one serious finding, an open premise moved into a hypothesis, and eight minor ones. It checked every step of the fine chain's r^R_K and the *Size of N_k* sums and found them correct.

**Repairs.** Line numbers are the snapshot's. The repaired note is a860547b5933.
- **S1** (l.70 and l.155): the coarse chain's 15.4(ii) was assumed inside (C6).
  - Checked: no note delivers it. The coarse-chain closure treats only the general T-step j → j+1. D2.7 15.5(ii) uses an entire word on (1.65), and the composed transports are not entire ((D5)).
  - Repair: it is now the explicit open interface (iii-d) in §4.3. That entry states the bounds and constants and says what a closure must re-run: 15.5's localisation on the chart domain of §4.1(3).
  - It is listed in the header's open interfaces. §3.2's coarse statements, (C5) and (C6) now cite (iii-d).
- **m1** (l.155): the independence of j, K and ℓ_C is now stated in (iii-d), and (C6) cites (iii-d).
- **m2** (l.153): (C5) now says "r^{R∨}_K ≤ g_K² at fixed k (r^{R,g}_K given (iii-d))". The conclusion at l.72 now says "at fixed k", given (iii-a) and (iii-d).
- **m3** (l.63): the clause "same s_j" is replaced. D2.3(7)'s sum runs over every step j ≥ 1, the step-j term carrying n_j = s_{j−1} (map #MD2.0.3.52-1, #MD2.3.7.3).
- **m4** (l.63, step 1): #MD2.0.3.52-1's sum Σ_{j≤k} includes j = 1, with 𝔞_1 = max(τ_0², ρ_1·pl). So E°^f_1 is covered, and l.63 now says so.
- **m5** (l.68):
  - CRE's indices are now written "its n := K and its m := j".
  - The p₀ normalisation is now addressed: LFR II's p₀(g) without A₀ (#T10.2-1) changes nothing, because only (2.7)'s ratio and p₀ > 1 are used.
  - The line is split at "So MR_j".
- **m6** (l.71): 𝔞̄^∨ := max(𝔞̄, 𝔞̄^g) is now defined at its first use, and the later definition at l.75 is deleted.
- **m7** (l.154, l.156):
  - ℓ_C ≥ 1 is now in (C6), derived: C is a union of scale-K block bonds (map #MD2.0.1.6), so ℓ_C is a positive integer.
  - "L ≥ 4" is dropped from (C6), since (C1) gives L ≥ 3(d+3). l.69 now says "L ≥ 4 by (C1)".
  - The constants list now adds r^{R∨}_K and 𝔞̄^∨, with m̂, a and y marked local.
- **m8** (background): #T4.37 already reads "the C and c of D2.7 15.4(ii)" (table 3f044f23ff9e). Cauchy #C7.6-3 now carries MR_j under the MR-cube reading (Cauchy 785c3a36fed5, repaired by (4)).
- **Queued item:** the sum lemma's parenthetical now reads "(Cauchy #C7.6-7-1, for a real base ≥ 2)".

**Pre-check for r5:**
- Every changed line was re-read: l.3, 63, 68–69, 70–73, 76, 107–108, 156–159.
- Every use of (iii-d), r^{R,g}_K, r^{R∨}_K and 𝔞̄^∨ was grepped. C^{R,g}_E and c^{R,g}_E are unused in the table.
- (iii-d)'s claims about D2.7 were checked against the text:
  - 15.1 uses covariance under constant conjugation;
  - 15.3 uses abs(T_P) ≤ F̄(P)Π sup‖w‖;
  - 15.5(ii): "π is a finite-dimensional representation, entire on G^c, and on the space (1.65) …".
- (D2), (D4) and (D5) were checked against §4.3.
- All repaired lines are ≤ 600 characters. Two touched lines were over that limit and are now split at sentence boundaries, with no change of content:
  - the header (old l.3, 2,093 characters) is now l.3–10, with the open interfaces as a list;
  - §5.3 (iv-b) at k = 1 (old l.143, 1,169 characters) is now l.153–156.
- My full read before the full round found one weak point, now repaired. l.77 said r^R_K is "uniformly in K", but r^R_K is a function of g_K. It now reads "depends on K only through g_K and not on ℓ_C or on the set".
- Every step of l.70–84 was re-derived again, including the m = 0 case of CRE (2.7) and of m̂^{β₀} ≤ L^{m/2}, and the sum lemma for every a > 0 (#C7.6-7-1).
- Cross-file pointer: the continuum note cites this note as "l.1–71 (header, §1–§3)". That pointer was already stale and is now stale by a further 10 lines. The continuum note's owner, (4), is told.
- Packet r5 (reviews\it1-bg-20261109-r5): a full round of the repaired part.
  - Snapshot: note 96f8f4c2ab91 (189 lines), D2.7 55d8246f93a0, map 7e6f1e0e4136, Cauchy 785c3a36fed5, table 3f044f23ff9e, LABELS 65f0b227aea3. prior_review.md is r4's report.
  - Peer, 12:5x (two-loops): TL #885–#889 stand on note 96f8f4c2ab91, and #885 uses only the fine chain, so (iii-d) does not enter. TL #887 now reads p₀ as "a positive constant times (log g^{−2})^{p₀}" (TL 4c2d342a9417).
    - Re-derived for table #T4.52 under both normalisations, p₀(g) = A(log g^{−2})^{p₀} with A = A₀ or A = 1. Since g_{K′} ≤ (1+β₀)g_K (CRE (2.6) in either order of K′ and K; BETA #B8.38–#B8.38-1 at simple G), p₀(g_{K′}) ≥ p₀((1+β₀)g_K). The prefactor 2C^R_1R̂_{K′}²(2 + 24R̂_{K′}/c^R_E) is a power of log g_{K′}^{−2}, so it is at most e^{p₀(g_{K′})/30} for g_{K′} small, the threshold depending on A. Hence #T4.52's bound ≤ 2e^{−p₀((1+β₀)g_K)/6} holds either way, and the row needs no change.
  - Under review: l.3–6, 70–80, 82–84, 114–115, 153–156 and 166–169, 8.6k characters in total. Context: l.8–10, 58–66, 68–69 and 110–113. The argument is 18.8k characters.

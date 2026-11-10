# Triage of pc-soft r4 (6 Nov 2026)

Review: verification\isolated_reviewer\reviews\pc-soft-20261106-r4\review.md, read in full. Packet: TL 47f7bfe1199d, PC 04cd2db746a7, LF de345faea9a2.

## Verdict

No fatal or serious finding. Two minor findings (m-a, m-b) and seven trivial points (t1–t5 and two unnamed ones). r3's S1 and m1–m5 are resolved. The round is not clean, so the clean count for pc-soft is 0. Every finding is repaired in place below.

## Repairs

| Finding | Where | Repair |
| --- | --- | --- |
| m-a, minor | #6.16.5, #167-8 | Both now carry the qualifier: (2.37) in each factor domain's collar is read at the own index (#6.16.3-2-1-1; inferred, not printed). |
| m-b, minor | #6.16.3-3-2-1 | The ≥2M₁ sentence now cites p.257 l.9–11 alone. A new sentence states that where a CRE-layer cut crosses the collar's set layers, or cuts meet each other or ∂X, the set is p.257 l.22–26's, built on each layer and summed. This is as for CRE's own X, whose boundaries cross CRE's layers in the same way (Bałaban's construction, accepted). |
| t1 | #6.16.3-2 | The collar index is labelled a reading: p.261 l.10's 𝐁_p(X) read by (2.14)'s ∂Ω ⊂ Ω_j∖Ω_{j+1} (p.257 l.9) and l.22–26, inferred, not printed. |
| t2 | #6.16.3-3 | ε_0 is cited as the first of CRE's two choices, which CRE takes (p.246 l.20–21, checked in the transcript). |
| t3 | #6.16.3-3-3 | Layer 0 is at least LM₁ finest spacings wide, more than an index-0 localisation's 2M₁ in the same units. |
| t4 | #6.16.3-5-0 | Now reads "by (181)'s covariance (p.307 l.7) the gauge at the collars' added block points is ours to choose and changes neither curvature nor current". The line went over 600 characters and was split at a sentence boundary; its last sentence is now #6.16.3-5-0-1. |
| t5 | #6.16.3-5-1-1, #6.16.3-6 | #6.16.3-5-1-1 now derives e^{−δ₀LM₁/16} ≤ L^{−32} from δ₀M₁ ≥ 64 log L (table #T2.5, #T2.9). It states that each finer layer of a cut collar has L^d times the blocks but lies across a further LM₁-wide layer, at L^{−32} < L^{−d}. #6.16.3-6 cites this bound instead of restating it. |
| trivial, slack | #6.16.1-1-1, #6.16.1-2 | 2M^V ≥ CM + R₁M₁: VAR's cubes are unions of M₁L^kη big blocks (p.279 l.2, p.277 l.12), so a CM-cube lies in one of side 2M^V once 2M^V ≥ CM + M₁, and M₁ ≤ R₁M₁. Then M^V ≤ CM/2 + (3/2)R₁M₁, and s^U_n's factor is (1 + 3R₁M₁/(CM)) ≥ 2M^V/(CM). The line was trimmed to stay at 583 characters. |
| trivial, running configuration | #6.16.3-5-2 | (190)'s D*D, at the segment's running configuration, differs from U^d_x's by O(abs 𝓗), second order in D*D𝓗. |
| queued, LF #3.99 | #910 | It now quotes CRE p.268 l.38's regularity abs(∂U − 1) < 2B₃ε_{K′}(L^{−1}η)² on the soft tests' support, with ε_{K′} enlarged by 1 + 2κ_s^{LF}. This matches LF #3.99 at c461a649ab2c; the bound is unchanged. |

## Consumers

- **m-a.** #158 cites "where V̂ ∈ 𝒟_k (above)", so it inherits the qualifier from #6.14 and #6.16.5. #6.14's V̂ ∈ 𝒟_k rests on R-mJ for (2.37), whose §7 reads X's layers at their own index ("On layers n < p, j_n = n"). So #6.14 carries the same qualifier, as bookkeeping (a status mark that changes no bound; #6.14 is outside this packet). The line was 1,121 characters, so it was split at sentence boundaries into #6.14, #6.14-1 and #6.14-1-1 (499, 479 and 274 characters), with no other change.
- **Slack.** M^V's only other use is #6.16.2-1's B₃LM^Vε^V_n, which needs only M^V ≤ M(ε^V_n) and still holds. The factor appears only in TL #6.16.1-2.
- **t5.** No other line restated the bound δ₀LM₁/16 ≥ 32 log L.
- **#910.** No line consumes its wording. #918 and #920 use the bound, which is unchanged.

## Pre-check for r5: the itemised pass

The first pre-check (23:44) re-read the repairs for correctness, but did not run the checklist line by line. At the user's request the pass below was run on every line of the part. It found six further defects, all repaired in place before any launch.

### Defects found by the pass

| Defect | Where | Check that found it | Repair |
| --- | --- | --- | --- |
| The triage claimed #6.14 was unaffected by m-a | #6.14 | consumers | #6.14-1 carries the qualifier (above, Consumers). |
| The own-index (2.37) was posed on the collar's layer 0, where CRE poses none (p.261 l.24) and R-mJ §7 says so | #6.16.3-2-1-1 | readings, against CRE p.261 l.24 | It is now posed at the own index for j ≥ 1 and not on the collar's layer 0. |
| The units of the cuts' M₁-cubes, of LM₁/2 and of 3M₁ were unstated | #6.16.3-3-2, #6.16.3-3-2-1 | units | X_x is a union of M₁-cubes at the set's index along each part of its boundary. The depth is counted in the set's index units, at most the layers' own (j′ ≤ m′), and meets (2.14)'s 2M₁ (p.257 l.9–11, with p.256 l.58–63's units). The line went over 600 characters, so #6.16.3-3-2-1-1 holds the crossing sentence. |
| A collar datum joining neighbouring blocks in adjacent CRE layers was measured at "y" with τ^d treated as constant; τ^d jumps by about L² there | #6.16.3-5-1 | consumers (r4's l.227 reading) | y is the point of the datum's one or two blocks (each in one CRE layer) where τ^d is larger. Both lie in the cut's collar, over which q^d's maximum runs. |
| r^{an}_k rested on an unlabelled reading of (3.43)'s scaling | #167-1 | readings, against CRE p.276 l.30 | r^{an}_k = g_kC₁p₁(g_k) lies within (3.43)'s abs A < C₁p₁(g_k) under either scaling, as g_k ≤ 1, so no reading is needed. D2.7 15.6(d), 15.7 and l.189 need only r^{ext}_k ≤ r^{an}_k. |
| TL cited LF #4.21, #4.22–#4.24 and #4.22.1, tags that are no longer in the LF; the LF's #4.10-2 moved #4.19–#4.29 to balaban_proofs/BP_JOINS_BLOCK_SIZE.md, keeping the numbers | #5.8, #5.10.5 (outside the packet) | citations resolve (a script over all external citations) | They are re-pointed to BP-joins #4.21–#4.24 and #4.22.1 (the same text), with BP-joins defined at its first use; "not reviewed in LF" now reads "not reviewed" (LF #4.10-2). labels_two_loops.py treats "BP-joins #…" as external, as it treats "LF #…". Bookkeeping. |

### The pass, line by line

- **Consumers of each changed conclusion.**
  - V̂ ∈ 𝒟_k: #158 (inherits it), #167-8, #6.14-1, #113 (conditional on #6.14 and #6.16), and D2.7 l.7, which cites #6.14 and #6.16 and is told by message.
  - M^V: #6.16.1-2 and #6.16.2-1.
  - The band's set: #6.16.3-3-3, #6.16.3-3-4, #6.16.3-4, #6.16.3-5-0 and #6.16.3-5-1. Each holds at the crossings, because (2.14) summed over the domains changes the set only within 2M₁ of ∂X_x, and every block of index j′ ≤ m′ lies in one CRE layer.
  - The e^{−δ₀LM₁/16} ≤ L^{−32} bound: #6.16.3-6.
  - #910: #918 and #920, whose bound is unchanged.
  - r^{an}_k: D2.7 l.187 and l.189.
- **Readings.** Every reading in the part is now labelled or removed:
  - the collar index (#6.16.3-2);
  - the own-index (2.37) (#6.16.3-2-1-1, #6.14-1, #6.16.5, #167-8);
  - Bałaban's l.22–26 at the crossings (accepted, as for CRE's own X);
  - (3.43)'s scaling (removed);
  - ε_0 (CRE's own choice, p.246 l.20–21).
  - Others already labelled: #6.16.2-1 (D2.7 15.8, derived, not reviewed), #6.16.3-0 (derived from (3.11)'s expansion), #6.16.3-0-1 (R-dec, Bałaban's), and #6.16.4-2 (R-mJ, derived, not reviewed).
- **Cited lines, with their context, in the corrected transcripts.**
  - VAR p.278 l.5–6 and l.34–46.
  - VAR p.279 l.2–4, 9–28, and p.277 l.12. The cube class is unions of M₁L^jη big blocks (the repairs table's slack row).
  - VAR p.307 l.4–9 (181).
  - CRE p.246 l.10–21; p.256 l.55–63; p.257 l.7–26; p.261 l.5–40; p.268 l.38; p.276 l.18–32.
  - CRE p.261's rooms were recomputed: (2.35) in the weights at j is fτ^d at every j; (2.37) at j = min(m, p) is fτ^d; and the own-index room f_jα_{0,j} ≥ (1+β₀)^{−2}f_jτ^d.
- **Units.** Every length in #6.16.3-2-2–#6.16.3-6 now names its units: own layer units, set-index units, index-0 units, or (190)'s.
- **Prior reviews' requests.**
  - r4: m-a, m-b, t1–t5 and the two unnamed points are done (repairs table).
  - r3: m1, m2 (alignment, the lattice sum with its L^d growth, and the passage from 𝓗), m3 (X_x defined, the ∂X convention), m4, and m5's three wordings (#6.16.3 u_m, #6.16.4's (2.36), M^V a multiple of R₁M₁) are all in the text.
- **Citations resolve.**
  - Every table and map tag cited by TL and PC exists.
  - Every bare tag in PC is a TL, PC or LF tag.
  - Every LF tag cited by TL and PC exists, except the moved #4.2x ones above.
- **LF update.** LF moved to 4d4eef81e63c. A diff of every tag against r5's snapshot (c461a649ab2c) shows exactly the changed tags #0.1.9, #0.1.41, #3.70-4, #3.84-1, #3.85, #3.85.1, #3.85-1, #3.86, #3.86.1, #3.86-1 and #3.94. TL and PC cite none of them, so the specs are re-pinned to 4d4eef81e63c.
- **Linear order.** Inside #6.16 the only forward citations are declarative: #6.16's summary of its own sub-lines, #6.16.1's pointer to #6.16.1-0, and "N^b ≥ 2, chosen at #6.16.3-6". The other forward citations go to later sections (#47–#75, #113, #125, #130.12, #167-x, #173.x, #191, #212), and none of those uses #6.16's conclusion:
  - #173.3 cites #6.16.1 only for the notation κ_s^{LF};
  - #113, #167-8 and #212-1 only state what rests on #6.16.
  - So there is no circularity. My first pre-check's "no line cites a later one" was not checked and was literally false.
- **Lengths.** Every line of the part is at most 600 characters. #6.14.1 (1,776) and #6.14.2 (1,445) are long lines that predate this work, lie outside the packet, and are not touched.
- **Definition check.** 0 conflicts for every spec.
- **Size.** r4's reviewed blocks were 19,204 characters. r5's are 21,037, the growth being the m-b sentence, the t5 derivation, #910's extract, and the pass's repairs.
- **Expectation.** There is no known weak point and no open item in the part, so a clean round is expected.

## The weak points named afterwards, and the adversarial read

The user asked whether r5 would be clean. I named four weak points. Two were defects and are repaired. A referee-style read of every new or rewritten sentence then found four more precision points, also repaired.

| Point | Where | Repair |
| --- | --- | --- |
| A collar datum near the edge of a cut's collar could have a block just outside it, so its y fell outside q^d's maximum | #6.16.3-3-3-1 (new), #6.16.3-3-2-1 | The cuts' collars are now the points of X_x within 3M₁ of the cuts, which hold both blocks of every datum within 2M₁ of them (a block has side 1 ≤ M₁). The cuts lie at least LM₁/2 − M₁ ≥ 4M₁ inside their layers (L ≥ 12d + 6, table #T1.3), so the collars lie in the cut layers, and #6.16.3-5-1-1's distance and #6.16.3-3-4's τ^d bound hold on them. |
| The letter d stood for both the dimension and (190)'s distance in the same lines | #6.16.3-5-1–#6.16.3-6 | The distance is written d_{PRT} there, defined as (190)'s d. The note's other uses of (190)'s d keep VAR's letter. |
| "every datum there" was ambiguous | #6.16.3-3-3-1 | It now reads "every datum within 2M₁ of the cuts". |
| L^{−32} < L^{−d} needs d < 32 | #6.16.3-5-1-1 | "(d = 4)" is added. |
| "L ≥ 10" did not cite what the table gives | #6.16.3-3-2-1 | It cites L ≥ 12d + 6 (table #T1.3). |
| #6.14-1's qualifier omitted layer 0 | #6.14-1 | It reads "posed at its own index j ≥ 1 and not on the collar's layer 0", as #6.16.3-2-1-1 does. |

The first and fifth rows are superseded by the next section, which replaces the band's construction.

## The crossings: not an import (7 Nov 2026)

The user asked whether the band's set was just an imported construction. It was not. #6.16.3-3-2-1-1 called the set at the cuts' crossings "Bałaban's construction, accepted". But X_x is our band, and VAR Theorem 1, its uniqueness clause, Proposition 9 and (190) are applied to X_x's problem. That needs X_x's own sequence to meet VAR (1) (p.277 l.11–14), which was never checked, and CRE p.257 l.22–26 does not say what happens where ∂Ω passes between layers. Re-deriving it found a real defect, which is now repaired.

| Defect | Where | Repair |
| --- | --- | --- |
| A cut in CRE's finer layer m − N^b needs a new ladder from index 0, with layers wider than R′M′ = LM₁ − M′. Such a ladder needs depth about Σ_{i≤n}L^iM₁η to reach index n, more than the depth at which U^d's minimal-width layers m − N^b + 1, …, m begin. So X_x's set would differ from U^d's at the start of every layer up to x, and q^d would not be small | #6.16.3-3-2 (old) | The CRE cut is made only when min(j + N^b, p) ≤ m − N^b. Then every index of X_x is at most the cut layer's, and the ladder catches up inside that layer. Otherwise m − j < 2N^b, and no cut is needed for the τ^d bound. The coarser-side CRE cut is dropped, since τ^d only decreases inwards (#6.16.3-3-4). X_x := (X ∩ Ω_{m−N^b})∖Ω^d_{j+N^b+1}, and its slabs are the whole cut layers. |
| The set at the crossings was imported, not constructed | #6.16.3-3-2-1-1 (deleted), #6.16.3-3-3 | X_x's set is given explicitly by the domains Ω^d_n ∩ E_n. Here E is X_x's sequence of L^nηM′-cubes at the spacing L^nηM₁ (#6.16.3-3-3-00). Its layers are at least LM₁ wide, so it meets VAR (1) at M′ with R′ (#6.16.3-3-3-0; BP-joins #4.23–#4.24, derived, not reviewed). |
| U^d's domains were taken to be unions of M₁-cubes | #6.16.3-3-3 | They are unions of L^nηM′-cubes: CRE's and the R-operations' domains are unions of MR_n-cubes (CRE p.256 l.21–22; BP-widths #4.18-2-1-2), the collar's of M₁-cubes, and all of these are powers of L. So E uses M′-cubes, and the agreement is proved directly on U^d's sequence, not through a maximal sequence. |
| The agreement off the cuts' collars was asserted from (2.14)'s 2M₁ | #6.16.3-3-3-1–#6.16.3-3-3-1-1 | This is now an induction: Ω^d_n ∩ {dist(·, Y^x) ≥ D_n} ⊂ E_n, with D_n = (d + 1)M₁ηΣ_{i≤n}L^i ≤ (d + 2)M₁L^nη. It holds in any lattice distance, since a cube of side s lies within ds of each of its points. |
| The collars were "points within 3M₁ of the cuts" | #6.16.3-3-3-2–#6.16.3-3-3-2-1 | K is now the blocks of X_x's set finer than U^d's, together with their neighbours. K lies within (3d + 3)M₁L^{j′}η of Y^x, so it lies in CRE's layer m − N^b and the set's layer j + N^b (L ≥ 12d + 6). |
| τ^d bound | #6.16.3-3-4 | τ^d ≤ (1+β₀)²L^{4N^b}τ^d(x) on X_x, case by case: m′ < m by #130.12, and m′ ≥ m by #53. The √N^b factor is no longer needed, so C^d (#6.16.3-4) and q^d (#6.16.3-6) drop it. |
| The top domains were also described as unions of MR_n-cubes, which the LF session pointed out is wrong (re-derived from LFR I p.179 l.19–24) | #6.16.3-3-3 | For k − N₀ + 2 ≤ n ≤ k, Bałaban's completed Z″_n are unions of M-cubes of the scale n, with no factor R_n. The line now says so. The conclusion does not change, since M is a power of L and M ≥ 2(d + 1)L²M₁ ≥ M′ (table #T2.9), and those layers, one M-cube of the scale wide, are wider than LM₁. LFR I p.179 is added to r5's sources. |
| "Finer averages fix coarser ones" was uncited | #6.16.3-4-1 | It cites RG1 pp.255–256: M^n = Ū^n is built by iterating the one-step average, one RG step at a time. The uniqueness sentence is split off to #6.16.3-4-1-1, for line length. |
| The cube structure of U^d's domains inside X was not derived | #6.16.3-3-3–#6.16.3-3-3-01 | On X^{∼−2} the domains are CRE's Ω_n, and off it they are the collar's. X^{∼−2} is a union of M₁-cubes of the scale p, the units of p.256 l.62's 2M₁ (inferred, not printed), so both pieces are unions of L^nηM′-cubes for n ≤ p. |
| Name clashes found by the build's definition check | #6.16.3-3-3-0, #6.16.3-3-3-1 | R′ is cited from table #T2.21, not defined. C is renamed Y^x. |

Consumers re-read:
- #6.16.3-3-1 now cites #6.16.3-3-3-0 for U^d's own sequence.
- #6.16.3-4 cites it for X_x's, and its C^d drops √N^b.
- #6.16.3-4-1's "nowhere coarser" cites #6.16.3-3-3-00. The nesting argument (finer averages fix coarser ones) and the free bonds hold, since Ω^x_n ⊂ Ω^d_n and X_x's layer 0 carries bonds.
- #6.16.3-5-0's gauge clause names the block points of X_x's set that are not U^d's.
- #6.16.3-5-1-1 cites #6.16.3-3-3-2-1. Its sum over finer layers is over E's layers, which are at least LM₁ wide.
- #6.16.3-6's bound drops √N^b.
- The labels script treats "BP-widths #" as external.
- Every line of #6.16.3 is at most 600 characters, and the part's argument grew from 21,281 to 22,569 characters, all of it the new construction.

## The collar datum against Bałaban's averages (7 Nov 2026)

On the user's "Rewrite!", the collar-datum bound (#6.16.3-5-0–#6.16.3-5-1-0) was re-derived from the printed averages. The old text compared U's and U^d's data through "(181)'s covariance" alone, which fixes no gauge in which data that are averages of different fine fields are close. A first rewrite used CMP98 Proposition 4 (p.038 l.48–p.039 l.6, (131)) and was withdrawn before any edit stood. That proposition's composite averages are relative to U₀ in its u-gauge ((87), (92), (97)), not the averages M^l of RG1, so at U₀ = 1 it gives M^n only up to a block-point gauge, and its L^{−1}-smallness is not what REG Lemma 1 gives (REG p.080 l.8–9).

| Defect | Where | Repair |
| --- | --- | --- |
| No gauge was fixed in which a collar datum of U is close to U^d's; "(181)'s covariance" only permits one | #6.16.3-5-0 | t_x is fixed down the levels l = p − 1, …, 0 by REG's relative axial condition (1.19) at k = 1 (p.079 l.8), unique given t_x at the block point (p.078 l.38), with t_x = 1 at U^d's block points. Averages are covariant (p.078 l.15) and M^{l+1} = M ∘ M^l (RG1 p.255 l.21–42), so M^{l+1}(U)^{t_x} is the average of M^l(U)^{t_x}. |
| The datum's difference was not bounded from printed results | #6.16.3-5-0-1–#6.16.3-5-0-3 | V^x_l := M^l(U)^{t_x}M^l(U^d)^{−1} is 1 off the level-(l+1) blocks in Ω^d_{l+1}. On them REG Lemma 1 (p.079 l.39–p.080 l.6, local by p.080 l.5–6) gives |V^x_l − 1| < 4d²θ^x_l + |V^x_{l+1} − 1|. Here θ^x_lL^{−2} bounds the level-l plaquettes as (1.7) poses them on Ω_1 (p.077 l.35; the proof's (1.26) uses 2α₀L^{−2}). By CMP98 (53), θ^x_l = 2ρ_xL^{2(l+1)}. Summed over c's ancestors up to j^x, where V^x = 1, this is < 8d²ρ_xΣL^{2l} ≤ 9d²κ_x, as L² ≥ 9. |
| The room at a collar datum was taken at one point although τ^d jumps by about L² between layers | #6.16.3-5-1–#6.16.3-5-1-0 | τ^x(c) is the largest α_{0,m′}L^{−2(m′−j^x)} over the CRE layers meeting c's two level-j^x blocks. Those blocks lie within 2√dL^{j^x}η of a point y of X_x of index j^x, with indices at least j^x − 1 (M₁ ≥ L, table #T2.9; layers LM₁ wide, #6.16.3-2-2). So m′ ∈ {m_y − 1, m_y, m_y + 1}, and τ^x(c) ≤ (1+β₀)²L²τ^d(y) by #130.12 and #53. |
| Constants downstream | #6.16.3-5-2, #6.16.3-6, #6.16.3-6-1 | (190)'s bound carries 9d²(a* + s^X)τ^x(c). q^d ≤ O(d²δ₀^{−d})(1+β₀)⁴L^{34−28N^b}, since 4N^b + 2 − 32(N^b − 1) = 34 − 28N^b. a* ≤ (2B₃C^d + 1)s^X, in place of (2B₃C^d + L²)s^X, since the L² now sits in q^d. |
| Lines over 600 characters, and symbol clashes | #6.16.3-5-0-1, #6.16.3-5-1-01 | The kernel sentence moved to #6.16.3-5-1-01. G, P, j″, τ̂, V′ and α_l were renamed t_x, ρ_x, j^x, τ^x, V^x_l and θ^x_l, after grepping TL, PC, the table and the LF. |

Consumers re-read:
- No line of TL, PC or D2.7 outside #6.16.3 cites q^d's power of L or a*'s constant. #6.16.3-6-1's conclusion (a share → 0 uniformly in X, p and k) is unchanged.
- Line 122 above ("names the block points of X_x's set that are not U^d's") is superseded: t_x = 1 at U^d's block points, and the axial gauge fixes it at the others.
- spec_pc_soft_r5.json was updated as follows:
  - the claim names the gauge t_x, REG Lemma 1, CMP98 (53) and τ^x(c);
  - Q2's t4 and Q3 name the new gauge, τ^x's locality and (2B₃C^d + 1)s^X;
  - the provenance describes the rewrite;
  - the sources add REG pp.77–80 ((1.7), (1.14)–(1.19), covariance, Lemma 1) and CMP98 p.26 (Propositions 1–2, (51)–(54)).

Pre-check:
- Every changed line was re-read against REG p.077 l.32–44, p.078, p.079 l.36–60, p.080 l.1–9, CMP98 p.026, and VAR p.307.
  - These lines were each re-derived: #6.16.3-5-0, #6.16.3-5-0-1, #6.16.3-5-0-1-1, #6.16.3-5-0-2, #6.16.3-5-0-3, #6.16.3-5-1, #6.16.3-5-1-0, #6.16.3-5-1-01, #6.16.3-5-2, #6.16.3-6 and #6.16.3-6-1.
  - #6.16.3-5-0-2's points:
    - θ^x_l = 2ρ_xL^{2(l+1)} follows from CMP98 Proposition 2 at its k = l, local in the level-l blocks at the corners.
    - j^x is at most one more than the other end's index (#6.16.3-2-2).
    - c's ancestors run over n < l ≤ j^x, and V^x_{j^x} = 1, as the level-j^x blocks are not in Ω^d_{j^x+1}.
- Both lemmas' smallness holds at θ^x_l ≤ 2κ_x and α₁ ≤ 9d²κ_x, which are small for g small by #6.16.3-5-1's 9d²L²(B₃ε^D + s^X).
- The part's argument went from 22,958 to 24,846 characters (≤ 25k), all of it the new derivation.

Adversarial pass (on the user's "Do you really think it'll be clean?"):

| Point | Where | Repair |
| --- | --- | --- |
| "V^x_l = 1 off Ω^d_{l+1}" named only bonds between index-l blocks and between finer cubes. VAR (3) poses data only on Λ_l = Ω_l^{(l)}∖Ω_{l+1}^{(l)} (VAR p.277 l.21), so a referee could ask about the mixed bond and about the averages inside an index-l block, which are not data | #6.16.3-5-0-1 | The line now argues by induction up from l = 0. A bond with an end in Ω^d_l lies in Λ_l, where both averages are X's datum, and t_x = 1 at its ends. A bond without is an average of such level-(l − 1) bonds. |
| The uniqueness pin p.078 l.38 is (1.15)'s, for the absolute gauge | #6.16.3-5-0 | It is now p.079 l.16, the uniqueness of the relative condition (1.19). |
| Lemma 1's gauge hypothesis and (1.7)'s normalisation were not tied to the print | #6.16.3-5-0-1-1 (split from #6.16.3-5-0-1 for length) | The line says that its (1.24) is t_x's gauge, which is (1.19) at k = 1 with n = 0, and that θ^x_lL^{−2} is (1.7) on Ω_1 (p.077 l.35). |
| Packet over 25k after the repairs (25,003) | #6.16.3-5-1-0 | The width sentence uses absolute lengths (2√dL^{j^x}η against LM₁L^{j^x−1}η), with the same content: 24,988. |

These were checked and stand:
- (1.7) is the plaquette condition alone; (1.9), the current, is not a hypothesis of Lemma 1.
- CMP98 Proposition 2's locality (the level-l blocks at the plaquette's corners, p.026 after (54)) keeps ρ_x within the two level-(l+1) blocks. Its smallness at its k = l is ρ_xL^{2l} ≤ κ_x.
- The datum's level-j^x blocks are not in Ω^d_{j^x+1}, Ω^d_{j^x+1} being a union of level-(j^x+1) cubes, so V^x_{j^x} = 1.
- The ancestor bonds' level-(l+1) blocks lie in the level-j^x blocks.
- The two blocks lie within √(d+3)L^{j^x}η ≤ 2√dL^{j^x}η of y.

## SHAs

TL 267ff572b1d3 (labels 98d03f67db5b, 1099 tags); PC 04cd2db746a7; LF c80c74a09439 (labels 8cb018ead815). Its changes since 5608f787e2f2 are #3.64, #3.76–#3.76.1, #3.93 and #3.94 (cdf81e25ac5a), then wording in #3.76 and #3.97 and a new #3.97-1, inside r5's permitted §3(d). None of them is cited by TL or PC, which cite LF #3.90, #3.96, #3.96-1-1, #3.99 and #3.99-1 in that range. Table 1e392e405632.

pc-rstep r29, pc-links-a r1 and pc-links-b r1 are re-pinned to TL 267ff572b1d3 and LF c80c74a09439, with 0 conflicts each. spec_pc_soft_r5.json (a full round, prior r4) is rebuilt at reviews\pc-soft-20261106-r5: 24,988 characters, 36,945 bytes, 0 conflicts. It is not launched and waits for the user's go. The LF session was told on 7 Nov 2026 at 01:26: the three LF SHAs are verified, TL is 4ca4959f5c9d, and the new q^d and a* are cited nowhere outside #6.16.3.

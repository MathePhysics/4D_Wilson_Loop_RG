# Triage: LF part 13a1, round 6 (lf-p13a1-20261107-r6), 7 Nov 2026

## Verdict

Clean: no fatal, serious, or minor finding; five trivial remarks (t1–t5). This round was a full round of 13a1, so the clean count of 13a1 is 1. The next round of 13a1 must be clean and full for 13a1 to be done.

LF reviewed at 3bc0f6261a26 (table 7a009cefc43a, LABELS 69fc7acb91d1). Repaired LF 11ce11342b9a; relabel requested from the table fork.

The referee confirmed the round-5 repairs (S1, the layers of 𝐁_k(Z) near Λ, against CRE p.256–257, (3.5), p.264–265, and LFR I (1.73)–(1.74); m1, the operator norms), and found no misquotation, no volume or scale dependence, no circularity, and no SU(N)-specific fact.

## Repairs

| Finding | Where | Repair |
|---|---|---|
| t1: Z^{∼−2} means M₁-cubes in #4.44-0.1–#4.44-0.2 and MR_k-cubes in #4.48-3 | #4.44-0.2 | "Z^{∼−2} for M₁-cubes contains every point …" |
| t2: the claim's growth statement omits ‖Y‖_∞ < 2C₁ε₁, which #4.49 keeps (implied, since κ_Λ ≤ C_Φ/4) | spec of the next 13a1 round | The claim states both conditions, as #4.49 does |
| t3: "LFR II p.357 l.27" for VAR's H₁ = H_{1,k} | #4.46 | "as RG I (2.6) uses VAR (174) (p.266 l.18)"; RG I's [15] is VAR (p.258 l.18, p.265 l.37) |
| t4: C₁′ depends also on d, L, G and C₀^{ms} | #4.50-1 | "depends only on d, L, G, M, C₀^{ms} (#T4.4) and Bałaban's constants" |
| t5: at complex ℋ the plaquette bound at U_t was cited through the real case only | #4.48.0-2, #4.48.0-2.1 (new) | "(#4.41-3-2, by the same expansion at complex ℋ, the operator-norm factors below entering the O(·))"; the line (636 characters) is split at "At complex ℋ" into #4.48.0-2.1 |

## Consumers

- The table's #T12.9 cites #4.48.0-2 for the local path U_t, which stays in #4.48.0-2.
- No live note cites #4.48.0-2 for the complex case.
- 13a2 r6 and 13b r3 are built at LF ff32ad403ddb, so these background lines are not in their snapshots. Their extracts do not use the reworded words, and the snapshots stand.

## Pre-check for the next 13a1 round (r7, full)

- Changed lines re-read: #4.44-0.2, #4.46, #4.48.0-2, #4.48.0-2.1, #4.50-1, with no forward tag citation ("below" names the next sub-line).
- Sources: RG I p.266 l.18 ("formulas (41), (174) [15]"); [15] is VAR (RG I p.258 l.18, p.265 l.37, "Sect. G [15]"); #T4.4.
- Lines: 395, 393, 319, 338, 477 characters.
- Built: reviews\lf-p13a1-20261107-r7 at LF 11ce11342b9a, table d8006ecd710f, LABELS a44bb969f4f4 (the fork's relabel, verified), prior = the r6 review. 20,422 characters of reviewed blocks (20,252 at r6, ≤ 25k); the growth is the t3 and t5 wording. 0 definition conflicts (7 allowed). Not launched.

# Rewrite of the Inductive Class and the Inductive Step

**Instruction of the user, 12 Nov 2026, 20:07 (verbatim):** "Rewrite everything necessary! Get rid of
old/deprecated constructions & proofs in the paper while doing it!"

**Instruction of the user, 12 Nov 2026, after 20:17 (verbatim): "Do not stop until the repairs are finished!"**
Do not end a turn to report. Give short status lines in passing and keep working: read the next block, digest it
here, write, compile, record, go on. After a context break: read this file from the top, then continue at "State".

This file is the plan and the state of that rewrite. Read it first after any break. It replaces the roadmap part
of `F26_SECTION_PLAN.md` (which keeps the digests of the notes read on 12 November and the state of F26).

## Why (the Record)

- `FINDINGS.md` F26, items 7–9: the paper's Definition "Dressed Loops" is weaker than the class D(k) of the step
  map (no extent weight, no tail clause, no comparison boxes, no rules for the species, (ii′) not species by
  species, no size for the insertions which the 𝐑-operation makes), and Section 6 asserts the counting of the step
  (`eq:size-bound`, the carry of sizes and weights) in a few sentences.
- `PROGRESS.md`, entry of 11 Nov 20:59: Section 6 was written in about an hour as "a structured argument in five
  parts", "condensed relative to the notes (to raise with the user)"; the Phase 1 map had read the step map's
  D2.1–D2.4 "by the first statements of each numbered part". The status later read "every section is written, with
  proofs".
- Six condensation notes in `PROGRESS.md` (lines 138, 171, 229, 291, 618, 681): Section 6; Section 7, Proposition
  "Torus Consistency"; Section 8, Lemma "Terms", large-field part; Section 11 with S.13–S.17; S.9 (the bookkeeping
  of the map's (12)(c)–(f) cited to the paper, which only asserts it: circular); Part II of the supplement.

## Rules of the Rewrite

1. **Read the argument in full before writing it.** For each block: the note's block at its current hash, every
   tag, not the openers; the cited lines of Bałaban in the `_corrected` transcription. Record the hash and the
   line range here.
2. **Only what is truly necessary** (the user, 12 Nov 2026, 20:16, verbatim: "Only add those parts of the map
   that are truly necessary!"). A clause, an object, or an estimate of the map enters the paper only if a proof in
   the paper uses it, and the use is named here (which step of which proof). "Necessary" is decided by reading the
   argument that would use it, never by the fact that the map has it. Variants, alternative routes, history,
   conversions between the notes' own normalisations, and bookkeeping that serves only the notes' organisation
   stay out. Where the paper's simpler object suffices, the paper's is kept and the reason is recorded. Conversely
   a clause the induction uses is not dropped as detail. Verdicts in the table of Step 0: **N** (needed, with the
   place of use), **no** (not needed, with the reason), **?** (undecided until the named argument is read).
3. **No condensation.** One display per transformation, every inequality with its reason, every count with its
   derivation. A passage of the form "the counts are those of ..." or "as in the notes" is not a proof.
4. **A block is "written" only when its proof is in the manuscript and compiles.** `PROGRESS.md` and the reports
   say "asserted", "outlined", or "proved", never "written" for an outline.
5. **Remove what is superseded, in the same edit.** When a rewritten definition, lemma, or proof replaces an old
   one, the old one is deleted from the paper (and from the supplement where it lives there), not kept beside the
   new one; every label that other text cites is either kept on the new statement or its citations are changed in
   the same pass. Each removal is listed in `PROGRESS.md` (what, where, replaced by what). After each block:
   grep for the removed labels and for the old names.
6. **Placement** (`STRUCTURE.md`, proposal of 20:05): definitions in Section 5 before the class; the counting in
   the body, as a section after the construction of the step; statements about Bałaban's bounds with the loops
   present in the supplement (S.8–S.10). No appendix for proofs.
7. Compile after each block (scratchpad), record pages and hashes; one dated line in `..\SESSION_HANDOVER.md`.
8. Open items at the top of every report; what is derived here and not reviewed is said as such.

## Sources (Hashes on 12 Nov 2026)

- The step map `WILSON_IT1_D2_STEP_MAP_2026_10_22.md`, 9f0d33e406e6, 3815 lines. D2.0(3), the definition of D(k):
  lines 382–560 (#MD2.0.3.1–#MD2.0.3.65). D2.2(6) the groups: find. D2.3(3) the reference gas and the interaction
  clause: find. D2.4(5) the contraction, D2.4(12) the counting: #MD2.4.3.1 at line 3051; (12)(a)–(f) at lines
  3563–3700 ((a) size 3563; (b) reserve and extent 3577; vertices 3613–3618; (c) links and covering 3623; (d)
  shares 3634–3650; (e) rooted sums and Kotecký–Preiss 3661–3673; weighted interaction clause 3681). Cov(k):
  #MD2.2.4.3 at line 1149.
- The closures (hashes in `MAP.md` §3; re-hash before use): D2.6 (large fields: species tests 2.1, the carry lemma
  5.0–5.6 with (T0)–(T3), 6.4–6.5, 7.1–7.4), D2.7 (the 𝐑-operation with the loop: items 1–7, 15.0–15.8), O2, O4,
  O6, SW, class activities, background, RMJ, RW1.
- Several loops: the two-loops note `WILSON_IT1_TWO_LOOPS_UNIFORM_BOUND_2026_10_27.md`, ac5f11dda03c: (6) lines
  250–294, (6A) 295–403, (6B) 404–635, (6C) 636–756, (7) 757–790; the N-loops note; the general-loops note §§3–6
  (the paper is for general loop ensembles, so the general-loops note decides where it differs).
- The first step: V4 (0f859f2d3652) and IT-1, for the base k = 1 of every clause.
- The paper at 19d7c448179d (161 pp.): Definition "Dressed Loops" lines 1123–1163; Section 6 lines 1208–1335
  (`sec:inductive-class`, `sec:small-field-map` 1238, `sec:contraction` 1250, `sec:large-field-step` 1293,
  `sec:assembly` 1309); `sec:flat-part` 1335; `sec:reference-gas` 1339. The supplement at 170045337da2 (156 pp.):
  S.8 line 1419, S.9 line 1494, S.10 line 1558, Section 18 at the end.

**Table of contents of the step map (line numbers at 9f0d33e406e6):** WHAT THE CONSTRUCTION IS 10; ONE STEP 33;
ONE MORE STEP 91; **D2.0** the inductive form at the step k and the count check 338: (1) units 340, (2) regularity
of the background 360, (3) the class at the step k 380–583, (4) the large-field parts 584, (5) the count check of
D(k) → D(k+1) 620–750, (6) the Bałaban inputs 751; **D2.1** the leading word at the step k + 1, 782: (1) quoted
786, (2) as a function of the fluctuation 843, (3) the transported form and the first-order term 864, (4)
localisation along C 887, (5) case (B) components and the transport radius 995; **D2.2** the small-field map
1005: (1) quoted 1009, (2) the numerator identity 1025, (3) the carrier 1080, (4) composition of 𝒲_k with the
variables of the step, with gauge covariance 1143–1460, (5) the joint cluster expansion 1461, (6) the integration:
output in the class 1580–2342; **D2.3** exact absorption of δm_{k+1} and z_{k+1}, 2343: (2) the flat value of a
group is a scalar 2388, (3) the exact factorisation 2429, (4) periodicity, contour locality, the infinite lattice
2487, (5) the coefficients 2755, (6) the square: the remainder 2805, (7) the sum over the steps 2843, (8) the
assembly 2868; **D2.4** the contraction count 2901: (1) quoted 2909, (2) Kotecký–Preiss for Bałaban's vacuum gas
2985, (3) the size count and the weights 3049, (4) the deviation factor 3085, (5) the amendment of D(k)(ii) 3145,
(6) matching, split, and recursion 3231, (7) the sizes of the groups and the reference gas 3273, (8) complex data
3291, (9) inputs and outputs 3308, (10) step 1 of (S): the H′ bound for marked polymers 3340, (11) step 2: the
slot sizes and the count check 3441, (12) step 3: the rooted sums over the linked families 3561, (13) step 4: the
rate comparison, the root sum for (Z), and the difference count 3748–3815.

## Order of Work

0. **Comparison.** The map's D2.0(3) in full against the paper's Definition "Dressed Loops": a table here, one row
   per clause of the map (tag, what it says, where the paper has it or that it does not, whether the induction
   uses it and where). Also the paper's objects which the map does not have (candidates for removal).
1. **Section 5, the objects and the class.** Species and their rules; the domain X_W, the dependence domain, the
   intervals, the comparison box Q^#_W; the sizes σ, n, #; the extent; the deviation quantity δ*; units of carried
   groups; the class with (i), (ii) incl. (ii-w) and (ii-t), (ii′-a), (ii′-b), (ii′-c), (iii)–(vi). The base k = 1
   from V4 and IT-1 for every clause.
2. **The step map, construction** (D2.1, D2.2, D2.3): evaluation point, slots, groups, the reference gas, the
   interaction clause in cluster form.
3. **The step map, counting** (D2.4): the contraction (5); (12)(a)–(f) in full; the weighted interaction clause;
   the tail clause; the proof of the size bound; the carry of sizes, weights, and units.
4. **Large fields** (D2.6 closure): reclassification, species tests, the carry lemma, exposed segments, payment;
   S.9 rewritten on it (no citation back to an assertion).
5. **The 𝐑-steps** (D2.7 closure; two-loops note (6B), (6C)): polymers' data, the free factors of LFR II (1.89),
   (1.93)–(1.97) (supplement), sizes and weights of the insertions which the operation makes, members, attached
   members; S.10 rewritten on it.
6. **Several loops** (two-loops note (6), (6A); N-loops; general loops): multi-interval arc sets, the unit factor,
   cross groups: production, carry, the cross exponent.
7. **Then F26 proper:** the masses of a young pair, Proposition S.19, the corrected S.14(f).
8. **Audit of the other condensation sites:** Section 7 "Torus Consistency"; Section 8 Lemma "Terms"; Section 11
   with S.13–S.17; Part II of the supplement. Same rules.

## What Counts as Deprecated (to Be Removed When Its Replacement Is in Place)

- Definition "Dressed Loops" in its present form (replaced by the class of step 1).
- In Section 6: the paragraph ending in `eq:size-bound` which asserts the counts ("The construction of the groups,
  the counting of the families ... are the counts of the step k + 1 per traversal and per cube ... so these counts
  are those of a square up to the factor Λ(C)/2"); the sentence "a carried insertion keeps the size and the weight
  of the step at which it was made" as a proof; the five-part outline wherever a full proof replaces it.
- S.9, proof of (ii), "merged parts": the citation of "the bound for a sum rooted at an old vertex of Paper,
  Section ..." (circular).
- S.10(v): the unweighted bounds of the insertions which the 𝐑-operation makes, once the weighted ones exist.
- S.14(f): the rates `eq:dressing-rates`, `eq:dressing-rates-cross` with the undefined C^W_Q, ε̄_A, C″_Ψ (step 7).
- Anything the comparison of step 0 shows to be an object of the paper with no counterpart in the notes.
- Not deprecated without a check: the statements of the main theorems; Sections 1–4; the flat part (Section 7) as
  far as it concerns the trivial term; these are audited, not presumed wrong.

## State

- **13 Nov 2026, 09:46 (from `date`). RESUME HERE.** Paper 236 pp. `adcb89b98fbf`, supplement 188 pp.
  `bf198958e69c`. Since 09:45: the paragraph "The polymer expansion at the local shift" (V4 Lemmata 9.14,
  9.15, Cor. 9.16 at (χ̂, W̃_t) under `eq:tilted-threshold` ω̂_t ≤ ω_*/2; the three properties used were read in
  V4's proofs, ll. 2754, 2772–2783, 2795). Still to do of "the consequences": V4 §9.6–§9.7 (Lemmata 9.20,
  9.22–9.27, 9.31–9.34, E.13), then (B)–(G). Added at 09:45, after `lem:local-shift`: the recall of V4's objects of its §9.5 and
  `lem:tilted-potentials` (χ̂^t_b, Θ̂^t_E, W̃_t; the identity `eq:tilted-measure`; the bound `eq:tilted-bound`
  with ω̂_t := (C₀ + C_τ)g₀(1 + 2r)³, C_τ := 5120M⁴m_Lϑ_Ve^{255κ}; locality within R_t). Verified in V4 for
  it: §9.5 opening and Lemma 9.13 (ll. 2693–2710), §9.5.1, §9.6.3 opening (the probe term L_Y(λ, ·) has the
  properties (i)–(iii) of the proof of Lemma 9.14), Lemma B.1(1) and §B.1 (a cube meets at most 8M⁴ bonds).
  **Next: the consequences**, as a lemma or a paragraph: V4's Lemmata 9.14, 9.15, Cor. 9.16, 9.20, 9.22–9.27,
  9.31–9.34, E.13 with (m̂, W̃_t, ω̂_t) in the places of (m, 𝐖_t, ω_t); the note (§3j(4)(a)–(e), (5)) lists the
  five uses of the host potentials and the three kinds of uses of the shift; read V4 Lemma 9.15 (ll. 2757–
  2797), 9.20 (2864–2896), 9.24 (2945–2977), 9.32 (3178–3197) for the exact hypotheses before writing; then
  (B)–(G). The entry below continues to hold as the record of block (a′) up to 09:42.
- 13 Nov 2026, 09:42 (from `date`). Paper 235 pp. `f682d4abd876`, supplement 188 pp.
  `bf198958e69c`. Block (a′) (F40) begun: `sec:first-step-regions` with `lem:local-shift` is in the paper
  (labels: `eq:hessian-decay`, `eq:linear-term-bound`, `eq:mean-shift-decay`, `eq:shift-range`,
  `eq:local-shift-sizes`, `eq:local-shift-identity`, `eq:parametrix`, `eq:parametrix-identity`,
  `eq:parametrix-rows`, `eq:truncation-error`, `eq:local-shift`, `eq:tilt-size`, `eq:bump-bound`; notation:
  r := t₀, ϑ_V, A^Λ, ℓ_Λ, J_1(Λ), m, m̂, δ̂, boxes Δ, Δ̃, Δ̂, N_nb = 7⁴, q_s, ℓ_s, N₀, N, R_t, μ_x = μ_H/20,
  C_m, C_δ). Next: part (A′) of the list in `PROGRESS.md` (entry of 09:42): read V4 Lemma 9.15 (ll. 2757–
  2797), Lemma 9.17 (2798–2814), §9.6 (2815–3130) at the places which note §3j(4), (5) names, and write the
  statement "V4's Sections 9.5–9.7 hold at m̂" as a lemma with the changes of constants; then (B)–(G). The
  entry below is the reading record for all of this.
- 13 Nov 2026, 09:34 (from `date`). Paper 232 pp. `0cea572ef7a7`, supplement 188 pp.
  `bf198958e69c`. Done since 09:30: S.9(iv) against LFR II pp. 384–387 with the 𝐑-step costs, S.9(v), the
  six-layer condition in the paper's definition of interior groups. Next: the first step's atoms. Read, in
  this order: `WILSON_FIRST_RG_STEP_V4.tex` Section 9.4 (labelled terms; Lemmata 9.21, 9.24; what is bounded
  on which terms), D2.6 closure (325ff1872afc) §5.6, §6.1–§6.5, §7.1; compare with the paper's
  `sec:first-step-proof` (Assembly), `sec:old-regions` (outer field of the first step, r^{(n)}_0), Supplement
  `sec:retreated-region` and S.9(i), "(ii), the first step". Missing in the paper as far as seen: the
  transports of the words near the region of integration as attached insertions (the closure's three classes
  of contour bonds), their pieces with sizes and weights (closure 6.4(b)), and the bound of the weighted masses
  per component (closure 6.3, 7.1) on the polydisc of the outer field. Then (e), (f).
  **Scope found at 09:36 (block (a′), the first step on the labelled terms with large-field regions;
  FINDINGS F40 lists its parts (A)–(G); `date` at the end of the reading: 09:37).** Also read: note §3j complete (ll. 1316–1400): the local shift m̂ := λm̃ with the
  parametrix P, K = Σ_ΔK_Δ, HP = 1 − K, boxes of sides in [ℓ_s, 2ℓ_s), m̃ := −PΣ_{n≤N}Kⁿℓ_Λ, the tilt
  δ̂ = Hm̂ + ℓ_Λ, R_N = 5ℓ_s(N + 2) + 2ρ_L, N(g₀) least N ≥ N₀ with e^{−μ_Hℓ_sN/4} ≤ g₀, the tilt in the host
  potentials W̃_t, C₀ → C₀ + C_τ, μ′ → μ̂′ = min(μ_x/4, ν/(2C_FLM)), μ_x = μ_H/20. Note §3i(4) read (box
  walk expansion of the inverse of a principal restriction: G_Δ, χ_Δ, 𝒢, K_Δ, H𝒢 = 1 − K, range 5ℓ₀(n + 1)).
  V4 §9.5.1 read (ll. 2713–2756: B = a − tm, χ^t_b, 𝐖_t, (c5-4-2), Lemma c5-4-1). More numbers: (c5-4-1) =
  (9.11), (c5-4-4) = (9.12), (c5-4-2) = (9.13), (c5-4-3) = (9.14), (c5-4-T) = (9.15), (c5-5-1) = (9.18);
  Lemma c5-1-1 = 9.1, c5-1-2 = 9.2, Remark c5-1-3 = 9.3, c5-4-1 = L. 9.14, c5-5-4 = L. 9.22, c4-7-1 = L. E.13,
  c2-domain-geometry = L. B.1; (part1-potential-host) = (3.36), (c-probe-host) = (3.75); sections: c5-0 =
  §9.1, c5-1 = §9.2, c5-3 = §9.4, c5-4 = §9.5, c5-4-2 = §9.5.1, c5-5 = §9.6, c5-5R = §9.7, c5-7 = §9.9,
  probe-kernels = §3.7, thresholds = §B.8. Decided: the new text goes into the paper as a subsection
  `sec:first-step-regions` after `sec:first-step-complex`, written lemma by lemma (first the local shift),
  and the paragraph "Assembly" of the proof of `thm:first-step` is changed when all parts are in.
  V4 (0f859f2d3652) §9.4 "The Labelled History Sum" proves the first step in averaged form: the expansion
  (c5-6-2) of F^Λ(1) holds on the covered event A^fin_cov only, the boundary term 𝓑^Λ and the uncovered
  terms are bounded inside the history average (Proposition c5-6-4), and nothing is of the form of the class
  there. `thm:first-step` asserts "dressed at the step 1" on every labelled term and its proof cites V4 "and
  its form on the labelled terms" for clause (ii); FINDINGS F32 lists this as not covered. The derivation is
  in the line-defect note (1bc8334cfad9): §3c (assembly at the step 1, choice (P), ll. 301–605), §3d (uncovered
  labelled terms and the closed contour, ll. 606–716), §3g, §3i (thin form of E^∂), §3j (carrier dependence of
  the t > 0 species), with §3e (analyticity) and §3f (bad-cube factor; in the supplement as S.7), and in the
  D2.6 closure §5.6, §6, §7.1 and the O4 closure (the centre of the expansion). To write: in the paper, a
  subsection after `sec:first-step-complex` "The First Step on a Term with Large-Field Regions" (the exact
  identity on a labelled term with the shift, the three classes of contour bonds and the transports as
  attached insertions, the t-family and the marks, E^∂ at the step 1, clauses (i)–(iv), (vii) of the class and
  the weighted masses A_1(Z) on the attached space of the step 1); in the supplement, what concerns the
  conditional Gaussian at the retreated carrier (shift, tilt, parametrix) next to S.7. Read §3c first.
  Read so far: §3c ll. 301–360 (identification with CRE label by label; placements of constants),
  §3d complete (ll. 606–716): the identity F^Λ(1) = κ_Ce^{E^∂ + E°}[f_ξ(m) + Σ q°(𝔅)tr(…)] on every labelled
  term; where V4 uses the covered event and why it is not needed, item by item ((2)(a)–(i)); D1(ii) on every
  term with the distance d^Λ(n) to E(B_ξ) ∪ (I∖D(Λ)) and ρ̂ = max(ρ, ρ_ph) ((4)); the count of the exposed
  segments ((5)). D2.6 closure §5.6, §6.1–6.5 read (the three classes of contour bonds, Y_i, the pieces
  Y_{i,X}, W_I, W_III, lw_1(Z)). V4 labels → printed numbers (from its aux): c5-3-0 = L. 9.9, c5-3-1 = 9.10,
  sec c5-3-4 = §9.4.2, c5-4-0 = 9.13, c5-4-2 = 9.15, c5-4-3 = Cor. 9.16, c5-4-4 = 9.17, sec c5-5-0 = §9.6.1,
  c5-5-1 = 9.19, c5-5-2 = 9.20, c5-5-3 = 9.21, c5-5-5 = 9.23, c5-5-6 = 9.24, c5-5-7z = 9.25, c5-5-7 = 9.26,
  c5-5-8 = 9.27, c5-5-9 = Prop. 9.28, c5-5-10 = Cor. 9.29, c5-5R-1 = 9.31, c5-5R-2 = 9.32, c5-5R-3 = 9.33,
  c5-5R-4 = Prop. 9.34, c5-6-1 = 9.36, c5-6-2 = 9.37, c5-6-3 = 9.38, c5-6-4 = Prop. 9.39, c5-6-def =
  Prop. 9.40, c5-7-1 = 9.42, c5-7-2 = Cor. 9.43, charts = L. 3.6, collar-coverage = L. 3.11,
  centred-expectation = Prop. 3.23, grouped-source = L. 3.25, covered = L. 3.28,
  regional-square-extraction = Prop. 7.3; row-locality = L. 3.5; (convex-response-operands) = (3.46);
  (c5-5-2) = (9.19); (c5-5-T) = (9.20); (c5-5-8) = (9.26); (c5-5-9) = (9.27); (c5-5R-T) = (9.29);
  Rem. c5-5-11 = 9.30; (c5-6-1) = (9.31); (c5-6-2) = (9.32); (c5-7-T) = (9.39); Rem. c5-6-5 = 9.41;
  Rem. c5-7-5 = 9.48; §c4-10-4 = §E.9.4; §c4-11-4 = §E.10.4; (c4-11-6) = (E.71); §regional-square-scalar
  = §7.4. Verified in V4's text: §9.6.1 places the whole of Section 9.6 on the covered event; the
  preamble of Lemma 9.25 uses it as §3d(2)(d) says; Lemma 3.6 is stated "on every branch" for the rows
  within 2R_c + 2L of I, with the inclusion of a + tΨ_ξ(A_e) in the row polydiscs; Lemma 9.33 is stated on
  the covered event; the paragraph after (3.46) has "it is not interpolated" and "is constant in a
  otherwise"; Lemmata 9.21 and 9.26 have "links off Ω₁ equal to their background value". The paper's Def.
  `def:dressed-loop`(c) lets the transports "contain outer variables" on a large-field region crossed by a
  loop; but the contour links of the first step differ from U₁ also on bonds of Ω₁ within R_t + 2L + 1 of
  the complement of the region of integration (the shift m̂ and the exterior inputs; closure 6.1, class
  (I)), so the paper needs the closure's attached insertions Y_i = π(T̂_i)π(T_i)^{−1} − 1 with their pieces,
  sizes, and weights (closure 6.1–6.5) as atoms of the first step, and §3d for the groups.
  Next: read the paper's `sec:first-step-proof` (ll. 1264–1332) and
  `sec:first-step-complex`, then V4 Lemma 9.25 (preamble), Lemma 3.6, §9.6.1, Lemma 9.33, Lemma 9.42 at the
  places §3d names, then write the paragraph "The labelled terms with large-field regions" of the proof of
  `thm:first-step` and the supplement part.
- 13 Nov 2026, 09:30 (from `date`). Paper 231 pp. `1a65e546e23e`, supplement 188 pp.
  `eead3a2062f8`. (d) is written: S.10 with links, sizes, (viii), (ix), (x), the cluster terms split at the
  flat reference for interior objects only, bound pieces, one block per class of second-class components
  (FINDINGS F38, F39; `PROGRESS.md`, entries of 13 Nov 09:02 and 09:30). Next, in order: leftovers of (c)
  (first step's atoms; S.9(iv) against LFR II pp. 384–389, now also with the costs log b_k and
  C^𝐑_Ae^{−p₀/4}R_k^d(d′+1) of the 𝐑-steps; S.9(v)); (e) F26; (f).
- 13 Nov 2026, 09:02 (from `date`). Paper 231 pp. `809f141acc7d`, supplement 184 pp.
  `f4a7afbe0c66`. (d) written for the free groups (links, sizes, (viii), (ix), cluster terms split at the
  flat reference).
- 13 Nov 2026, 01:40 (from `date`). Paper 230 pp. `5b2d0b3b481a` (at 01:45, after two
  entries in "Notes on the Papers" and the appendix line on the new constants: `eeb9bbb6c7dc`), supplement
  173 pp. `bf05c5ecee8a`. (c) large fields is written: `sec:regions`, `sec:new-region`, `sec:collar-groups`,
  `sec:old-regions` (`prop:old-regions`), payment paragraph and `lem:term-bound` on `eq:carry-product`;
  Supplement S.9 redone ((ii) in the paper's count; (vi) gauge transformation; (vii) complex outer field).
  Left over from (c), to do with the audits: the first step's atoms in detail (closure §6, IT-1 §3a, §3e),
  S.9(iv) against LFR II pp. 384–389, S.9(v) (cross species; only S.10 and the Cauchy part still cite it).
  **Next: (d)** 𝐑-steps (S.10 from the D2.7 closure; F30's L-condition), **(e)** F26, **(f)** appendix,
  "Status", "What Is Not Proved", "Notes on the Papers", audits, lint. FINDINGS F36.
  *(d), what is to do (13 Nov, 01:45 from `date`; paper `eeb9bbb6c7dc`):* S.10 (`prop:r-operation`, supplement ll. 1595–1683) has (i)–(vii) with proofs;
  its (v) gives the 𝐑-made deviation insertions only in the old form (sum per traversal ≤ C^𝐑ρ̃δ*). Needed for
  the class as rewritten: for an 𝐑-made group its domain, size, extent, the geometry (vii) with the unit
  constant, `eq:per-insertion` with b_W, `eq:tail-clause`, `eq:sup-clause`, `eq:production-clause`, clause
  (iii) on the space of the step; members (regular, attached) inside 𝐑-groups. Sources: D2.7 closure
  (ab6c80ebce1b) 15.6 (ll. 463–552), 15.7, 15.8 (594–696), 15.8-1 (697–794: counted domain hull_c(g), size
  σ̃(D̂_g) = Σ_P(#π_k(B_P) + 2^{d+2}D_P + λ_𝔏ℓ_P) + ⅓Σσ(D), unit u_𝔏 = 640(2^{d+2} + 8), L ≥ 4·10⁴u); the
  two-loops note (6A)–(6C) (#518–#524, #561–#569, #629, #698–#751, #803–#832). The paper's `u_\star` and the
  conditions `eq:count-conditions` on L change with u_𝔏 (F30 item 2): record in FINDINGS.
  *(d), read so far:* D2.7 15.6 (ll. 463–552) and the two-loops note (ac5f11dda03c) (6B) #690–#747,
  #761–#778, (6C) #826–#844. Findings: (1) the paper has `u_\star := 11` (l. 1306) and S.10 says nothing of
  the geometry clause (vii) for the groups which the 𝐑-operation makes; the notes give them the unit
  u_𝔏 = 640(2^{d+2} + 8) = 46080 (#829), so `u_\star := u_𝔏` is needed, and `eq:blocking-factor-condition`
  already covers L ≥ 6·10⁶Λ̄u_𝔏 (2^{52} for Λ̄ ≤ 1.6·10⁴, 4Λ̄²L₀^× beyond). (2) The size is not the volume of
  the hull: σ_g = Σ_{cross members}σ + ½Σ_{single-loop members}σ + Σ_Pπ(P), π(P) = #π_k(B_P) + 2^{d+2}D_P +
  λ_𝔏ℓ_P (#691), domain = the counted cubes hull_c(g) (#714), dependence in the 8M-neighbourhood of hull_c(g)
  and of the cubes meeting span(g) (D2.7 15.8-1(1-2)); B_P, D_P, ℓ_P are defined in (6B) *Lengths*, *Cubes*,
  *A link's data* (#626–#629-5), not yet read. (3) Per-insertion bound: b_g = e^{|Ψ_g|}B(g)·C·diam(hull⁺)/r^ext
  (D2.7 15.6(d)); extent #834; rooted sum Σ_{g ∋ □} ≤ C_gr e^{−p₀(g_k)/2} with the weights (#742-2); payment
  (5/2)ν per unit of Σ_P(#π_k(B_P) + 2^{d+2}D_P) (#723). **To write:** S.10 new item with these definitions and
  the clauses (vii) (geometry, `eq:production-clause`), `eq:per-insertion`, `eq:tail-clause`, `eq:sup-clause`
  for the 𝐑-made groups; set `u_\star := u_𝔏` in the paper and re-check where 11 is used (`eq:first-step-units`
  stays, as 11 ≤ u_𝔏).
  *(d), definitions read (two-loops (6B) #626–#653; LFR II p. 389 (1.94)–(1.97) re-read in the corrected
  transcription):* a polymer P of the 𝐑-gas has Bałaban's
  localisation domains X′_1..X′_s (unions of cubes of π_k; LFR II (1.90)), pieces P′ of the letters, home
  tensors, and carried insertions with domains Y_{P′}, bases Y′₀, excess ex = |Y_{P′}∖Y′₀|, and links (clusters
  of earlier reference gases, numbers e^{e_X} − 1) with count ℓ_P = Σσ_{n(X)}(X).
  D_P := Σ_r(d_k(X′_r) + 4R_k + 2λ̂ + 498) + 4Σ_{P′}ex(Y_{P′}) (d_k in M-units, RG I p. 257);
  B_P := ∪_rX′_r ∪ ∪_{X first-class in P}X^{(λ̂+248)}; π(P) := #π_k(B_P) + 2^{d+2}D_P + λ_𝔏ℓ_P, λ_𝔏 = 1/640.
  What pays: e^{−βκd_k} of (1.95) leaves c_F^× = ½ per unit of D_P (#636–#647); the volume factor of (1.95)
  leaves a_V ≥ ½ per cube of X′_r (#648); the factor of (1.89) of a first-class component leaves
  e^{−p₀/2 + polylog} (the margin, #652), which pays e^{5p₀/64} for X^{(λ̂+248)} and the constants; links pay
  from a°(X) = (ν/32)σ (#629-4). Rooted sum: Σ_{g: polymer ∋ □}(weights) ≤ C_gr e^{−p₀(g_k)/2} (#742-2).
  Supplement S.10 setup (ll. 1597–1605) and `lem:loop-localisation` (l. 2689) read: the supplement measures a
  polymer by |P| (cubes of side MR_k) and its localisation lemma has pieces with cores but states neither the
  domain of a piece, nor its base, nor the weight e^{3κ·ex} (D2.7 15.5(ii)(α), (β): base
  Y′₀ ⊂ X(F)^{[3]} ∪ ⋃_{K ∈ h(F) ∪ 𝒦}(K⁺)^{[λ̂]}, λ̂ = 4⌈R_k/(1024√d)⌉ + 9, ex ≤ 3^dΣ_c|c|).
  **(d-2), first part DONE, 13 Nov 01:52 (from `date`), supplement `db9ed8ccc3e6`, 175 pp., clean:** S.10
  setup: paragraph "The local terms of the exponent" (links: definition, set X̂ = union of the domains of the
  groups of the cluster, #_n(X) cubes, reads labels within M, meets X_c^∼; weight from the second bound of
  `eq:exposed-bound`); polymers and |P| include the links; proof paragraph "(iii), the links" (per first-class
  component the links cost ≤ e^{2 mass(X_c)} ≤ e^{Res(X_c)/2}, paid from the reserve). **Still to write in
  (d-2):** the sums over the polymers with links through a cube in (iv), (v) (D2.7 15.8 "The sum over P through
  a traversal": attachment cubes, polynomial factors), and the new item on sizes and weights.
  **(d-1) DONE, 13 Nov 01:47 (from `date`), supplement `4bfdbffbcc83`, 173 pp., clean:**
  `lem:loop-localisation`(vi) (λ̂ := ⌈R_k/(128√d)⌉ + 31, base, cores, excess ≤ 3^dΣ|c|, weight e^{3κ·ex} from
  the unused half of e^{−(κ₁−1)|c|}; new condition L ≥ (3/2)3^d, covered). **Now (d-2):** read the two-loops
  note #698–#721 (big and small members, T_D, the cube and span counts #714, #715, #748–#760) and D2.7 15.4(i)
  (spans, ℓ_D, s_D), then write the definitions and S.10(viii).
  *(d-2), read (two-loops #698–#721):* a member D of a polymer is *big* if σ(D) ≥ 240 (made at k) or ≥ 32
  (made before), else small; big: #_k(X_D) + n_k(D)/M ≤ (21/20)σ(D), diam of its set T⁺_D ≤ (43/20)Mσ(D);
  small members in the slots of a component X lie with their 5M-neighbourhoods in X^{(247)} ⊂ B_P; a far letter
  or far small member has a piece with ex ≥ R_k (#699-2, #699-3), a quarter of 4ex covers it (#699-4). Counted
  domain X_g := the cubes of π_k of ∪_P dom_c P (dom_c P: cubes meeting dom P, #629-1), σ(D_g) :=
  #_k(X_g) + |span(g)|/M. Bounds: #_k(hull_c g) ≤ Σ_{big}#_k(X_D) + Σ_P(#_k(B_P) + (2^{d+1} + ½)D_P +
  2^{d+2}ℓ_P) (#714); |ℐ(g)| ≤ Σ_{big}n_k(D) + 16MΣ_PD_P (#715-1); sum ≤ u_𝔏σ_g (#716); diam(S_g) ≤
  2MΣ_P(D_P + 2ℓ_P) + (43/10)MΣ_{big}σ(D) ≤ u_𝔏Mσ_g (#720); extent #834. Not yet read: #748–#760 (spans,
  joins), D2.7 15.4(i) (ℓ_D, s_D, why a span lies within |P| layers), D2.7 15.7 (the surviving sums).
  **Checked (01:48 from `date`):** the supplement's S.10 has no "links" (the local terms e_X of E^∂ as
  constituents of the polymers); D2.7 15.8 "The links in the gas" (ll. 676–695) has them and their payment:
  expand e^{e_X} = 1 + (e^{e_X} − 1); a term reading the labels of a first-class X_c meets X_c^∼ ⊂ the
  localisation domain of X_c; polymer = connected union of Bałaban's X′_a and link sets X̂; a°(X) = (ν/32)σ
  split ½ (root sum), ⅛ (attachment cubes), ¼ (weights, 15.8-1(6)), ⅛ (polynomial factors); links at a
  second-class Y_i paid by Res(Y_i). To be added to S.10(iii). FINDINGS F37. LFR II p. 377 (localisation
  domains contain the components of Z^∼ which they meet), p. 378 (𝐓′_k(X) sums the labels {Ω_j^c ∩ X, Z_j ∩ X}),
  p. 379 (1.72) (𝐓′_k(Y_i) outside the bracket) re-read in the corrected transcription. **Subtlety for the
  paper's definitions:** in `sec:old-regions` a cluster is in the reference gas of a term iff its groups are
  interior, and interior/regular read the labels also through the comparison regions of the members
  (Ω_m ⊃ comparison region), not only within one cube of the domains; so the set of a link, where it reads
  labels, must contain these comparison regions (diameter bounded by size plus extent, paid by e^{ν_e·ext}),
  or the reference gas must be defined by the domains alone (then a group with a reclassified member stays in
  the gas; check `prop:old-regions`(ii) and S.9(iii)). Decide when writing the links paragraph of S.10.
  **Order of work for (d):** (d-1) add to `lem:loop-localisation` a part on the domain, the base, and the
  excess of a piece, with the weighted bound, from its own proof (cores, factor e^{−(κ₁−1)|c|}); (d-2) S.10:
  definitions D_P, B_P, π(P), σ(g), counted domain, and a new item (viii) with the units (u_𝔏), the payment,
  the rooted sum, and the clauses of the class for the groups which the operation makes; (d-3) paper:
  `u_\star := u_𝔏` at l. 1306 (now "u_⋆ := 11"), the paragraph "The 𝐑-operation" of `sec:large-field-step`,
  appendix; FINDINGS entry.

- **12 Nov 2026, 23:53 (from `date`). (c) begun; superseded by the entry above.** Paper 216 pp. `0c2b21f592e9`, supplement `d3c297f5d58e`.
  Done of "NEXT, IN ORDER" (entry of 23:03): (a) the base k = 1 and (b) the wrapping and the cross species, both
  on the term without large-field regions (PROGRESS 23:17, 23:26, 23:51; FINDINGS F32–F34). **Now: (c) large
  fields.** Supplement S.9 (`prop:attached`, ll. 1478–1544) and the paper's `sec:large-field-step` are the old
  text: S.9's proof speaks of "touched parts", "merged parts", a "bridge", and cites a bound of the paper which
  no longer exists. To do: read the D2.6 closure (325ff1872afc) in full, §1–§8; extend Sections 6.2–6.8 of the
  paper (identity, expansion, marked polymers, groups, count) from the term without large-field regions to all
  terms, or state exactly which of their statements hold verbatim there; rewrite S.9 on it; the attached parts
  and marks at k = 1 (IT-1 §3a(7), §3e (3.9), (3.12)). Then (d), (e), (f). The user (23:40): prose pass by
  `proof-exposition` only, not `math-prose` or `deslop-maths`; keep the status updates coming.

  **(c), reading record and design (13 Nov 2026, 00:00 from `date`).** D2.6 closure read in full: §1–§5
  (ll. 1–270) and §7 (payment, ll. 353–447). Not read: §6 (lw slots, ll. 272–352), §8 (band, 448–522).
  CRE pp. 264–265, 269–272, 276–278 (corrected) re-read. Map D2.2(4) read to l. 1212 only. **In the paper
  (217 pp., `c0230008055f`):** new subsection `sec:regions` with Lemma `lem:regions` (Λ_{j+1} ⊂ Ω_{j+1} ⊂ Λ_j;
  8 layers from CRE (3.5); the collar Coll_j and its distance ≥ 7LMR_{n+1} from Ω_{n+1}), before the old
  text of `sec:large-field-step`, which is unchanged. Also found: `prop:marked-polymers` is already stated
  for the measure CRE (3.27) with arbitrary Ω_{k+1}, Λ_{k+1}, S_{k+1}; `prop:marked-size` and everything from
  `sec:groups-of-step` on is for the term of ϱ_{k+1} without large-field regions. Bałaban's own treatment of
  the general term (CRE pp. 276–278) is a sketch ("or rather its appropriate generalization", "treated as
  above"); it is accepted as his and goes into "Notes on the Papers". In the paper's terms the tests for a
  group made at k + 1 reduce to two: (S1) the bodies of its constituents do not meet the one-layer
  neighbourhood of Λ_{k+1}^c (this implies the closure's (ii) for polymers and (iii)); (S2) its comparison
  regions lie in Ω_{k+1}; and a group with an attached member is attached. What the closure does, in the
  paper's terms:
  - *What the main theorems need of a term with large-field regions:* the exact form (dressed loop with the
    same normalisation κ) and a bound which may lose e^{C·#cubes} per large-field component
    (`lem:term-bound`, `eq:attached-condition` allows L⁴(MR_n)⁴ per cube). No smallness per group near large
    fields, only summability.
  - *Scope notes in the paper:* `sec:localisation-expansion` (l. ~1538) takes the term of ϱ_k without
    large-field regions and arbitrary Ω_{k+1}, Λ_{k+1}, S_{k+1}; `sec:groups-of-step` onwards takes the term of
    ϱ_{k+1} without large-field regions. So two extensions: (A) new regions at the step k + 1 (outer variable
    σ_k = A_k on Ω_{k+1} ∩ Λ_{k+1}^c, boundary potentials, the measure CRE (3.27) at σ_k ≠ 0, CRE pp. 270–277);
    (B) old regions (propagators of a sequence of domains, CRE p. 267, p. 276; 𝐇 decays into the old layers,
    CRE p. 277; members which depend on outer variables).
  - *Species tests* (closure 2.1): a group made at k + 1 is of a small-field species iff (i) no polymer
    component and no member's domain meets the one-layer neighbourhood of Λ_{k+1}^c, (ii) its components and
    arc lie in Ω_k, (iii) no boundary-type potential, (iv) its comparison region lies in Ω_{k+1}. Otherwise
    attached: to the component Z of Λ_{k+1}^c ((iv) fails alone; amplitude ρ, decay in d^Z from the extent
    weight) or to the collar Coll_{k+1} (the cubes of π_{k+1} within 6 layers of Λ_{k+1}^c; amplitude
    b_k = O(δ_k), no parity gain). A group with an attached member takes that member's species. Old deviation
    groups whose comparison region meets Ω_k∖Ω_{k+1} are reclassified (closure §3).
  - *The count with attached members* (closure §5): attached members are not summed in the
    Kotecký–Preiss condition (a traversal of the step n holds L^{n−j} of them); they are fixed roots, each roots
    at most one group per term, the group's mass is ≤ δ_n times the member's, δ_n = 2c̄e^{−(25/8)(ν_e/L)R_{n+1}},
    because a polymer which touches the member must reach supp B′ ⊂ Ω_{n+1}, at distance ≥ 5R_{n+1} sides of π_n
    from Coll_j (CRE (3.5), (3.20)); Σ_nδ_n ≤ log 2 by the coupling flow. In the paper's count this means: the
    tree bound `lem:tree-bound` rooted at an attached member, attached members excluded from 𝖤_k and from
    E_o; product form ∏_D(1 + w(D)∏(1 + δ_m)).
  - *Complex outer variables* arise only from complex localisation parameters s (the gauge transformation
    w(s) rotates the outer fields); the interpolation in s is ours to choose, real for real s. The attached
    clause needs analyticity and a supremum bound on a domain in (𝐔, 𝐉, ω) which contains the later evaluation
    points (SW closure §3's 𝒟^sub; map D2.2(4)(c)–(f), (6)(e); O6 closure for σ_k complex). **Still to read:**
    these, and the closure §6–§8.
  - *Read after 00:00 (13 Nov), for the next window:* (1) O6 closure to §2: the outer field σ_k is the
    restriction of the one fluctuation field A_k of CRE (3.15) to Ω_{k+1} ∩ Λ_{k+1}^c; every term of the
    actions of CRE (3.27), (3.29) depends on it through the composite field B′ (RG II (1.19)) and through entire
    quadratic forms, so the localised terms are analytic jointly in (σ_k, A) where RG II §1 has them analytic
    in B′. (2) Map D2.2(4)(c)–(d′): at the shifted block field the old insertions are evaluated at
    (e^{iη𝐇_k(B′)}U_{k+1}, R(w)ω), w = u_k^{−1}v₁ block-local and analytic in 𝐇_k, |log w| ≤ (C_w + 3d)sup|𝐇_k|;
    the rotation cannot be moved to the configuration (w jumps between blocks, the change per fine bond would
    be O(h_k), not O(L^{−k}h_k)), so members which depend on outer fields need analyticity in those fields on
    a polydisc of relative radius O(h_k). Without it only real localisation parameters are available, and the
    bound of a component by Cauchy's estimate in s is lost. (3) Closure §8 is Supplement S.8's content.
    (4) `r` of `sec:count` renamed `r_κ` (clash with the exponent of R_j). Paper `8c53e0a1f174`.
  - **Written, 00:22 (13 Nov, from `date`), paper `48c02591bfac`, 222 pp.:** `sec:new-region` (case (A):
    the earlier steps have no large-field region): interior groups = groups of ℓ₀ (`lem:interior-constituents`,
    `prop:interior-groups`), collar occurrences `eq:collar-occurrences`, `prop:region-attached`. **Next block,
    the collar (still case (A)):** (1) sizes: `prop:marked-size` for marked polymers with a cube in 𝒩_{k+1}:
    amplitude b_k/ε_H per component, no parity (Supplement Lemma 17.28 fails with an outer field); the bound of
    Lemma 17.27 on such polymers rests on Bałaban's generalisation (boundary potentials O(ε_k) by CRE p. 277,
    the conditional Gaussian with the outer field); |B′| ≤ b_k holds on every bond of Ω_{k+1} (the form of CRE
    (3.14) with r_y). (2) Count: polymer vertices with a cube in 𝒩 get 𝔞_v = b_k/ε_H and one more factor for
    the collar occurrences (sets of clusters ≁ M, factor |z_𝒞| ≤ 2φ̄e^{2φ̄}, sum ≤ exp(4e·c#(M)); the margin
    "7c + 1/800 ≤ 1" of `prop:rooted-sums` becomes (6e + 1)c + 1/800 ≤ 1); `thm:size-bound` with
    E_α + E′_α, E′_α ∝ b_k; this proves the convergence for `prop:regrouping` on the present term. (3) Groups
    at the collar: every one has a cube of 𝒩 in X_𝒢, so ext ≥ dist(𝔫, 𝒩)/M: the collar term of
    `eq:insertion-bound` with amplitude b_k ≤ Cρ_{t,k+1}. (4) Analyticity in σ_k (O6 closure §3–§9, unread
    from §3) for the later steps. **Then case (B), old regions:** the expansion with members which depend on
    outer fields (map D2.2(4)(c)–(f) read; (6)(b3), (b6), (b7), (e) from l. 1990 unread), the count with fixed
    roots (closure §5 read), the payment (closure §7 read), the first step (closure §6 unread; IT-1 §3a(4)–(8),
    §3d, §3i, §3j unread).
  - *Plan of the text:* a new subsection of Section 6 "The Step on a Term with Large-Field Regions" with
    (1) the setting and the collar, (2) which statements of Sections 6.3–6.8 hold as they stand for the groups
    passing the tests (locality), (3) the attached groups: production, (4) the carry, (5) the payment; S.9
    rewritten as the supplement's statements on Bałaban's text which (1)–(5) use (CRE pp. 270–277 at σ_k ≠ 0,
    the 𝐇-decay, LFR II pp. 384–389 with the enlarged summand).

- **12 Nov 2026, 23:08 (from `date` 23:07:23). ONE SESSION FOR THE MANUSCRIPT FROM NOW ON.** The user, 23:06
  (verbatim): "Transcription ⑂ Solely works on the rotation, you solely work the manuscript. The third station
  won't do anything anymore". The session which wrote the entries below (20:45–23:03) has stopped; the session
  which wrote `COMPLEX_COVARIANCE_*` and `FIRST_STEP_BASE_STATE.md` (the "third session" of the entries below)
  now owns the paper, the supplement, `PROGRESS.md`, `FINDINGS.md`, and this file, and continues at "NEXT, IN
  ORDER" of the entry of 23:03, item (a). `ListAgents` at 23:07: no other session busy on the folder. Builds:
  the session's scratchpad was withdrawn; compile in a directory made by `mktemp -d` outside the project.
  `COMPLEX_COVARIANCE_DRAFT.tex` is the source of `sec:carried-complex` and is no longer maintained; the
  three-lines lemma (O1 of `COMPLEX_COVARIANCE_STATE.md`) is a candidate replacement for the citation of RG I
  (1.17) (F31) and goes to the supplement when written.

- **12 Nov 2026, 23:03 (from `date` 23:00:46 at the last compile). LATEST STATE; RESUME HERE.** Paper 204 pp.
  `fa0bfccd5d4f`, supplement 170 pp. `d3c297f5d58e`, both clean. Items (4) and (5) of the entry of 22:58 below
  are done: `lem:new-insertions` (in `sec:small-field-map`, before "The flat parts"); the paragraph "Assembly"
  of `sec:assembly` (clause by clause, θ := νσ/16, order of the constants C_α, C_{S′}, C_c, C_new, C_χ).
  `FINDINGS.md` F30 (count) and F31 (space of a step, constants, what is not covered) are written.
  **Section 6 now, in order:** `sec:evaluation-point`, `sec:step-identity`, `sec:localisation-expansion`,
  `sec:marked-polymers` (with `prop:marked-size`), `sec:groups-of-step`, `sec:count`, `sec:small-field-map`
  (`lem:new-insertions`, flat parts, `cor:production-bound`), `sec:new-deviation`, `sec:contraction`
  (`prop:carried-real`, recursion), `sec:carried-complex`, `sec:large-field-step` (OLD TEXT),
  `sec:assembly` (cross species, torus: OLD TEXT; "Assembly": new).
  **NEXT, IN ORDER:** (a) the base k = 1 of the new clauses: `eq:per-insertion`, `eq:tail-clause`, clause (iii)
  in the form of `eq:space-of-step`/`eq:production-space`/`eq:covariance-law` at j = 1, clause (vii) (X_W
  connected, u_⋆ = 11, incompatible ⇒ common point, `eq:sup-clause`, `eq:production-clause` with ρ₁), θ := νσ/16;
  the third session's `FIRST_STEP_BASE_STATE.md` has the readings of V4 (Lemma E.8 with its proof, (3.36),
  (3.75), Section E.10.4) and IT-1 §3a; it is paused; if it does not continue, read that state file and write
  the base into the proof of Theorem `thm:first-step` (which also has to be rewritten from IT-1: the seventh
  condensation site). (b) The wrapping species on the term without large-field regions (a group with one
  interval whose cube 𝒬^{∼5} does not embed: ext ≥ N_min/(2M) − 6; from `eq:size-bound` with the extent weight;
  table constant c_att) and the cross species in the supremum form with the extent weight (new cross groups:
  `thm:size-bound` holds for them in the projective norm, and a cross group contains a chain of cubes between
  two loops, so σ ≥ a_{k+1}/M; carried cross groups: the complex block for tensors with several intervals, or a
  bound by the production suprema with the growth 2^{k−j}): rewrite the first paragraphs of `sec:assembly` and
  the cross clause `eq:cross-bound` accordingly (two-loops note (6), lines 250–294, and N-loops note §6 to read).
  (c) Large fields (S.9, D2.6 closure; the split of an old insertion; map D2.2(6)(b3), (b6)–(b7), (e)).
  (d) 𝐑-steps (S.10, D2.7 closure; L-condition of F30). (e) F26 proper. (f) Appendix A and C (constants and
  conditions of F27–F31; η_w; c_F clash with Supplement Lemma 17.22), "Status", "Notes on the Papers" (RG I
  (1.17); RG II (2.32)), audits (F30 "to audit"; other condensation sites), prose passes (`math-prose`,
  `deslop-maths`) on Sections 5–6 new text, final lint.

- **12 Nov 2026, 22:58 (from `date` 22:56:43 at the last compile). SUPERSEDED BY THE ENTRY ABOVE.** Paper 202 pp.
  `689634a8c24f`, supplement 170 pp. `d3c297f5d58e`, both clean. Done since the entry of 22:46 below (its
  items (1)–(3)): `sec:carried-complex` moved in (decision (A) taken, reported to the user, not yet answered);
  `sec:new-deviation` (`prop:new-deviation`: `eq:new-per-insertion`, `eq:new-tail`, constants C_g :=
  3B₃(2C_box + 5)M, c_an := min(3/4, c_F/(2c_G)); deviation species at k + 1 := one interval and the cubes
  𝒬_𝔫(𝒢)^{∼5} embedded in the torus; the others are the wrapping species, old text in `sec:assembly`);
  `sec:contraction` rewritten (`prop:carried-real`, `eq:contraction-first`, `eq:rho-ratio`,
  `eq:deviation-recursion` with C_new := 4C_gC_{S′}/c_an and a := L^{−1}(1+β₀)⁸, `eq:recursion-fixed-point` with
  C_χ := max(C^{(1)}_χ, 2C_new)); `cor:production-bound` has the spare factor e^{(7/16)νσ}. θ(W): to be taken
  as νσ(W)/16 for every group (then it is fixed at production, and for a carried group
  Σ_{Γ≁{W}}|φ_{k+1}(Γ)| ≤ 81·625(1 + 81u_⋆σ(W)/L)C_{S′}𝔞_{k+1} ≤ νσ(W)/16 for γ_q small): **not yet written into
  the paper; goes into the assembly.** Third session ("Transcription"): base k = 1 in
  `FIRST_STEP_BASE_STATE.md` (decided: the paper's X_W, σ := 𝔰, u_⋆ := 11, R_h ≤ 4M from V4 (3.36), (3.75),
  Lemma E.8; dependence within 8M settled except the Hessian stencils of the root measures); it paused at
  22:5x for the user's word.
  **NEXT, IN ORDER:** (4) the analyticity and covariance of the insertions of the groups made at k + 1 on the
  space of the step k + 1 (hypothesis of `prop:new-deviation`; clause (iii) at k + 1): map D2.2(6)(b) lines
  1653–1841 ((b4) 1756–1789 the new insertions before integration, (b5) 1790–1802 the integration; (b1)–(b3)
  the operators, 𝐇(s,·), w(s); (b6)–(b7) outer field and representatives: large-field block) and (e) lines
  1931–2336 (the background domain; about 100 KB, mostly the terms with large-field regions and the evaluation
  points — on the term without large-field regions what is needed is: the interpolated configurations lie in
  the space of the step k (`eq:expansion-condition`, already in the paper), Bałaban's operators and activities
  are analytic and gauge covariant on his spaces (RG II pp. 3–7, 14–15; RG I (1.19)), the fluctuation measure
  is invariant under the adjoint action of the gauge transformations of the background, and RG I (1.17) for
  the inclusion of the pointwise space). (5) The assembly: rewrite `sec:assembly` for the terms without
  large-field regions: the dressed loop at k + 1 (split, reference gas, Q_{k+1}, 𝓔_{k+1}), clauses (i)–(vii) at
  k + 1 with θ := νσ/16, citing `cor:production-bound`, `prop:new-deviation`, `prop:carried-real`,
  `prop:carried-sup`, `lem:group-covering`; the wrapping species (groups whose cube 𝒬^{∼5} does not embed:
  ext ≥ N_min/(2M) − 6, so e^{−ν_e ext} gives the last term of `eq:insertion-bound` if c_att ≤ ν_e/2: check the
  table's c_att = #T12.19's c); the cross species in the supremum form with the extent weight (𝖤_k contains
  them). (6) The base k = 1 (move in the third session's draft when it exists). (7) Large fields (S.9; the
  split of an old insertion whose comparison region leaves Ω_{k+1}), 𝐑-steps (S.10; the L-condition of F30
  item 2; `eq:deviation-recursion` is cited there), F26 proper, audits (F30 "to audit"; the paper's c_F vs the
  supplement's c_F of Lemma 17.22), appendix of constants and conditions (F27–F30 and the constants of
  `sec:carried-complex`: c_F, ρ₀, c_G, ϰ_m, λ_r, μ_c, c_pl, Ĉ, C_c; L ≥ 20(1+β₀)², L > (1+β₀)⁶; η_w = (5/16)ν),
  FINDINGS entry F31 for the blocks of 22:46–22:57 (decision (A), the constants, the deleted text), prose
  passes on all new text, final lint.

- **12 Nov 2026, 22:46 (from `date` 22:42:55 at the last compile). SUPERSEDED BY THE ENTRY ABOVE.** Paper 192 pp.
  `06117d994581`, supplement 170 pp. `e205777bd372`, both clean. **In the paper, with proofs, on the terms
  without large-field regions:** the count (`sec:count`: `lem:coarse-cubes`, `lem:group-covering`,
  `lem:cube-set-sizes`, `lem:tree-bound`, `lem:group-weight`, `prop:rooted-sums`, `thm:size-bound`, with the
  weight e^{(5/2)νσ + ν_e ext}); `prop:marked-size`; in `sec:small-field-map` the split Y = c·(transport) + Y^d and
  Corollary `cor:production-bound` with `eq:size-bound` (now this corollary's display; the old display in
  `sec:contraction` is deleted) and C_{S′} := (3e^{2ν}/ν)(1+β₀)⁶C_α (`eq:size-constant`), then θ ≤ νσ/16 through
  Lemma `lem:root-bound` (its proof adjusted: positions are the 81σ cubes touching X_𝒢). Conditions and what is
  derived here: `FINDINGS.md` F30. **The design entry of 22:06 below is carried out, except that the arcs of
  the components are not filled at all** (groups of components = classes of "touch a common member"; a
  memberless group is one component), and the tree lemma is applied twice (groups; inside a polymer vertex).
  **A third session ("Transcription", the branch stopped at 20:45) works in its own files:**
  `COMPLEX_COVARIANCE_DRAFT.tex` + `COMPLEX_COVARIANCE_STATE.md` (the complex covariance block, drafted, 10 pp.;
  its state file read in full at 22:44, the draft's lines 49–99 read: the space 𝒮_n(U) of `eq:space-of-step` in
  fine units — |α| < α_{1,n}L^{−n}, |δ_eα| < α_{1,n}L^{−2n}, |∂(e^{iα}U) − 1| < c_Fα_{0,n}L^{−2n}, |𝐉| < α_{0,n}L^{−3n} —
  Lemma "space inclusion", constants c_F, ρ₀, c_G with (N1)–(N3), ϰ_m, μ, c_pl, Λ_𝔞, Ĉ, C_c := 1 + (1 + Ĉ)C_{S′},
  conditions L ≥ 20(1+β₀)², L > (1+β₀)^{10}); and next `FIRST_STEP_BASE_DRAFT.tex` + `FIRST_STEP_BASE_STATE.md`
  (the base k = 1 of the new clauses). **Its open point O1:** the complex covariance note's averaging bound (K3)
  is not proved (VAR (172) unchecked for the complex part). Its options: (A) the space of the step is defined
  by the pointwise conditions (which is what the paper's clause (iii) says already), RG I (1.17) cited as
  Bałaban's at the production of a new insertion; (B) (2.35), (2.37) in the space, block open. A candidate proof
  (three-lines theorem between real configurations and VAR Proposition 9) is in its state file. **I proceed
  with (A) (it follows the rule on Bałaban's claims and leaves nothing open) and report it to the user at the
  top of the next report.**
  **NEXT, IN ORDER:** (1) read `COMPLEX_COVARIANCE_DRAFT.tex` in full (376 lines) and move it into the paper as
  a subsection of Section 6 after `sec:small-field-map` (its hypotheses (a)–(d) against the class; clause (iii)
  restated with 𝒮_n(U), c_F; O2: θ, σ, ext of a carried group are fixed at production; O3: the current in fine
  units); FINDINGS entry for its constants. (2) The Cauchy step for the groups made at k + 1 (map D2.4(4), lines
  3085–3144, re-read in full at 22:43; Supplement Lemma 17.22: 𝒬 a cube of cubes with 𝒬^{∼5} ⊂ Ω_{k+1}, E the
  largest fine curvature in 𝒬^{∼5}, M_𝒬 half the side of 𝒬^{∼2}, gauge with |A|, |∇A|, |∂*∂A|, |ΔA| ≤ 3B₃M_𝒬E,
  |R(u)J| ≤ 4B₃M_𝒬E under 2E ≤ min(a₁, c₂), 2M_𝒬E ≤ R₁M₁a₁): f(z) := Y_𝒢(e^{izηA}, zR(u)J) − c_𝒢T, f(0) = 0 by
  Schur, analytic for |z| < R_X := c₀ᾱ_{k+1}/(3B₃M_𝒬E) with c₀ from the pointwise conditions (c_F, c_G), Schwarz ⇒
  e^{θ}‖Y^d_𝒢(U_{k+1})‖ ≤ b_𝒢 Dev, b_𝒢 := (C_g/(c₀ᾱ_{k+1}))e^{θ}S_𝒢 with M_𝒬 ≤ C·M·ℓ_𝒢 (ℓ_𝒢 = #(X_𝒢): X_𝒢 ⊂
  B(𝔫, M#(X_𝒢) + 1), so R_{t_𝔫} ≤ 2C_boxMℓ_𝒢); tail clause from `eq:size-bound` and ext ≥ C_box t for t ≥ 2
  (ν_eC_box = ν/2 > η_w = (5/16)ν). (3) The carrying of the old insertions ((T-dev), Supplement S.8; map D2.4(5),
  (6), lines 3145–3272, to re-read) and the recursion of C_χ; delete the old text of `sec:contraction`. (4) The
  base k = 1 (third session's draft). (5) Large fields (S.9), 𝐑-steps (S.10; the L-condition of F30 item 2),
  several loops (the cross species in the sup form with the extent weight), F26 proper, audits (F30 "to
  audit"), appendix of constants and conditions (F27–F30), prose passes on all new text.

- **12 Nov 2026, 22:06 (from `date`). DESIGN OF THE COUNT FOR AN ENSEMBLE, FIXED AFTER READING (all in full):
  the general-loops note §6 (d401d13826f7, lines 227–267), the map's (11)(a)–(f), (12)(a)–(f), (13)(a)
  (9f0d33e406e6, lines 3441–3760), the two-loops note §(2) (lines 147–174), the N-loops note §1 and §6A
  (2f8558cd2e50, lines 10–34, 75–111). NOTHING WRITTEN INTO THE MANUSCRIPTS SINCE 21:50; WRITE NOW, BLOCK BY
  BLOCK, IN THIS ORDER.**
  *A defect of the definitions written at 21:18–21:50, for three or more loops:* the arc `I_i(Y)` of a component
  (filled on every loop) and the arc set of Definition `def:groups-of-step` (an arc between every tied pair on
  every common loop) can be longer than a constant times the sizes of the constituents when a constituent has
  pieces on many loops (the N-loops note avoids this: #NL6A.5, "a cross vertex is joined only into cross groups,
  which have no joining arcs", and tube hulls). **Corrections (D1)–(D4), block 1:** (D1) the arc of an active
  component Y is filled only if S′(Y) lies on one loop; otherwise I(Y) := S′(Y) (the dichotomy for intervals
  holds trivially; then |I(G)| ≤ 4Λ̄M#(G) for every G without members). (D2) A marked polymer all of whose arcs
  lie on one loop has the one piece I_i(M); otherwise its pieces are the maximal arcs of the union of the arcs
  of its groups. (D3) Ties star-shaped, so that tied constituents have domains in contact: (ii) a marked
  polymer of the set T of a link is tied to the carrier of the link; a marked polymer incompatible with a
  vacuum occurrence is tied to the marked polymer to which the occurrence is *assigned* (the first one
  incompatible with it); (v) two *incompatible* groups of one old occurrence. (D4) Joining arcs only between two
  tied constituents each of which has all its pieces on the same single loop. A group with all intervals on
  one loop still has one interval.
  *The class (Section 5), block 1:* compatibility of groups is a relation given with the groups, with the
  property that incompatible groups have domains X_W which share a point; X_W := domains ∪ cubes of π_j which
  *meet* a fine bond of the intervals; X_W is connected (cubes sharing points) and #_j(X_W) + n_j(W)/M ≤ u_⋆σ(W);
  ℓ_W := #_j(X_W) (replaces d_j(X_W) + 1: X_W need not be wall-connected); every group has σ(W) ≥ 1. New
  clauses: (S_k) the production bound of the groups made at the step k (sup norm S_W over the space of the
  step, weight e^{θ + νσ + ν_e ext}, factor ℓ_W, right side C′_S𝔞_k, per traversal and per cube of π_k), and the
  sup form for all groups present, per traversal, with the weight λ_cν, λ_c := 15/16 − 1/8192 (its proof for
  carried groups is the complex covariance block).
  *The count, blocks 2–5 (my own bookkeeping, simpler than the map's; to be recorded in FINDINGS F30 with its
  conditions):* cube positions only. For a constituent c let K(c) be the set of the cubes of π_{k+1} which meet
  its domain (group: X^+_W; marked polymer: M, the supports of its links and assigned vacuum occurrences, its
  pieces) and, if c has all its pieces on one loop, its window (the piece extended at each end by
  Λ̄(2 diam + 2)). Facts: tied ⇒ K's share a cube; X_𝒢 ⊂ ∪K(c), X_𝒢 connected; σ_{k+1}(𝒢) := #(X_𝒢) + n/M ≤
  (1 + 4Λ̄)Σ_c|K(c)| (a cube meets ≤ 4Λ̄M traversals); ext_{k+1}(𝒢) ≤ #(X_𝒢) + 3C_box; ℓ_𝒢 = #(X_𝒢); a connected
  union of n cubes of π_j meets ≤ 81 + 625n/L cubes of π_{k+1}; so |K(W)| ≤ 146 + (50625 + 108Λ̄)u_⋆σ(W)/L.
  Vertices: polymer vertex (M with 𝔊(M), touched members, links carried, vacuum occurrences assigned), member
  vertex (untouched member), occurrence vertex (Γ with multiplicity n, weight |φ_k(Γ)|ⁿ/n!). Linking: K(v) and
  K(v′) contain equal or touching cubes. Tree lemma: Σ_{v′~v}w(v′)e^{b(v′)} ≤ ηb(v), η ≤ 1 ⇒ the sum over the
  connected sets S ∋ v₀ of Π_{v≠v₀}w(v) is ≤ e^{ηb(v₀)}, and over those with |S| ≥ 2 it is ≤ ηb(v₀)e^{b(v₀)}.
  Old cube sums from the traversal sums by the extent weight (box reduction, constant K_box); occurrence
  vertices by Kotecký–Preiss for the gas of the step k with the activities multiplied by a constant;
  ε^new ≤ C_M𝔞_{k+1} + K_β(b_k/r_α)E^old. Result: Σ_{𝒢 at Δ}e^{(17/16)νσ + ν_e ext}S_𝒢ℓ_𝒢 ≤ C_new𝔞_{k+1} + ηK·E^old.
  Then θ ≤ νσ/16 by Kotecký–Preiss for the gas of the step k + 1, the tail clause by ext ≥ C_box t − 2, and
  the absolute convergence for `prop:regrouping`.
  *For the 𝐑-steps block:* with these constants the share of an 𝐑-made insertion (u_⋆ = 2Λ̄u_𝔏) needs
  L ≥ CΛ̄³u_𝔏 with a larger C than `eq:blocking-factor-condition` provides; sharpen the constants there or
  record the changed condition.

- **12 Nov 2026, 21:51 (from `date` 21:50:28). LATEST STATE OF THE MANUSCRIPTS: paper 177 pp. `d2646ba2e1e8`,
  supplement 170 pp. `3b566797fddb`, both clean.** Since the entry "21:55" below (typed; actual about 21:49):
  the dependence set X^+_W (8M fine units around X_W) is defined in Section 5 and used in (iii), in
  `sec:localisation-expansion` (touching), and in `sec:groups-of-step` (the domain of a group as a
  constituent); the comparison region contains it. (H1), (H2) are still to be added to the class with the
  count. **RESUME HERE: (1) general-loops note §6 (lines 227–267); (2) write the count for an ensemble (outline
  of "22:04" below, items 2–6), re-reading (12)(e)–(f), (13) (lines 3661–3760) in full; (3) items 7; (4) the
  complex covariance block and the complex clause of (iii); (5) the base k = 1 / the first-step proof from
  IT-1; (6) large fields, 𝐑-steps, F26 proper, audits, appendix of conditions (F27–F29), prose passes.** Clock
  rule: the entries below headed 21:44–22:04 and "21:50", "21:52", "21:55" carry typed times; only times marked
  "from `date`" are measured.

- **12 Nov 2026, 21:55 (two reads after `date` 21:47:24). Two-loops note (6A)(i) IS NOW READ IN FULL (lines
  295–372). The resolution of the point about windows on several loops (entry of 21:50), all N for the count
  written for an ensemble:**
  *Base at the step 1* (#526–#532): X(W) ∪ π₁(ℋ(W)) is connected (V4 lem:two-loop-pins(a)); Y_W depends on the
  configuration on X(W), on the halos within 2R_h < 8M fine units, on the stencils within 2L of the traversals,
  and on the transports of ℐ(W); S_W := the closed 8M-neighbourhood (fine units) of X(W) ∪ ℐ(W) contains the
  dependence set, is closed-connected, and diam_∞(S_W) ≤ (1 + 4/M + 48/L)M𝔰(W); #₁(X_W) + n₁(W)/M ≤ (1 + 4/M)𝔰(W);
  so the step-1 insertions have "units with a factor" u ≤ u₁ := 1 + 4/M + 48/L.
  *Vertices on several loops* (#533–#543): diam_v := max over the loops on which v has an interval of the
  largest distance from a point of supp v to the intervals of v on that loop. For a polymer vertex put
  Q_v := M ∪ ∪_{W∈𝔅(M)}S_W ∪ ∪supp 𝒞: it is closed-connected (M connected; each touched W has its dependence set
  meeting M and inside the connected S_W; each link cluster touches M), each int_i(v) contains a point of Q_v,
  and supp v ⊂ Q_v, so diam_v ≤ diam_∞(Q_v) ≤ M#(M) + Σ_{W∈𝔅(M)}(diam_∞(S_W) + 1) + Σ(M#(𝒞) + 1), with
  diam_∞(S_W) ≤ u_W(M/L)σ_k(W). The window extends each int_i(v): |win(v)| ≤ Σ_i|int_i(v)| + 80(diam_v + 1) (four
  ends for two loops; for N loops the number of ends is twice the number of intervals).
  *Filled hulls* (#544–#548): for an old insertion D with several intervals, H_i(D) := the smallest arc of C_i
  containing ℐ_i(D); win(D) := ∪_iH_i(D) extended by 20(diam_D + 1) at each end; |H_i(D)| ≤ 4diam(S_D) ≤ 4uMσ(D),
  diam_D ≤ uMσ(D) in production units. *Covering* (#549–#554): piece by piece and loop by loop; a pair without a
  common loop has no arc to cover. *Units with a factor* (#566): an insertion D with n(D) ≤ uMσ(D),
  diam(S_D) ≤ uMσ(D), #(X_D) + n(D)/M ≤ uσ(D) in production units and (H0)–(H2); u = 1 for the groups made by a
  step after the first, u ≤ u₁ at the step 1, u ≤ u_𝔏 for the 𝐑-made ones; *the share of D* (#555–#572, read
  earlier): 170uMσ(D) positions, C^×_win ≤ 196u/c_w, #_{k+1}(X_D) ≤ 16 + 20480/L + 8320uσ_k(D)/L,
  |win(D)| ≤ 88u(M/L)σ_k(D) + 84, the share conditions u(8496ν_f + 88ν_e)/L ≤ ν_r/4 (L ≥ 4·10⁴u) and
  u·c′_πα_{1,k+1}·88M/L ≤ ν_r/16.
  **THEREFORE the class needs, for every group W (to add to Definition `def:dressed-loop`, with the base from
  V4 and the step from the construction): (H0) Y_W depends on the configuration only within 8M fine units of
  X_W ∪ (the cubes meeting its intervals); (H1) a closed-connected set S_W containing X_W, the dependence set,
  and the intervals, with diam_∞(S_W) ≤ uMσ(W) in production units; (H2) the set E_W := X_W ∪ (the cubes meeting
  the filled hulls) is closed-connected; with u = 1 for the groups made by a step k ≥ 2 on the trivial term,
  u₁ at the step 1 (and u_𝔏 at the 𝐑-steps).** The clause "Y_W depends on the background only through X_W"
  written at 21:40 is to be replaced by (H0) (the halos of the step 1 reach 8M fine units beyond the domains).
  **NEXT: the general-loops note §6 (lines 227–267) for N loops and general loops; then write items 3–6 of the
  outline for an ensemble with these definitions; (H0)–(H2) into the class in the same edit.**

- **12 Nov 2026, 21:52 (after `date` 21:47:24; two reads since). Two-loops note (ac5f11dda03c) (6A), lines
  295–322, read in full (#503–#524); lines 323–351 not yet (then #555–#576, read earlier).** Content: (i)
  *multi-interval arc sets*: the arc set of a group on C_i is the union of the linked hulls of its classes of
  joined pairs on C_i; a class can have several intervals on one loop (two pieces on C₁ joined only through a
  piece on C₂ get no joining arc). *Connectedness*, by induction on the step with three hypotheses for every
  old insertion D: (H0) the set X^{Cov}_D on which D depends lies within 8M fine units of X_D ∪ (the π_k-cubes
  meeting ℐ(D)); (H1) a closed-connected set S_D ⊃ X_D ∪ X^{Cov}_D with diam_∞(S_D) ≤ u_DMσ(D) in production units
  (the factor u_D of "Units with a factor"); (H2) E_D := X_D ∪ (the π_k-cubes meeting the arcs H₁(D) ∪ H₂(D) of
  "Filled hulls") is closed-connected. D's domain one step later := the π_{k+1}-cubes meeting the
  8M-neighbourhood of E_D. For a new group: X(𝒢) := its constituents' domains and those of the members of its
  merged occurrences (old ones taken one step later), S_𝒢 := X(𝒢) ∪ ℐ(𝒢) closed-connected with
  diam_∞(S_𝒢) ≤ Mσ_{k+1}(𝒢), so (H0)–(H2) hold for it with u = 1. The rest of #518–#524 concerns the insertions
  made by the 𝐑-operation (u = u_𝔏 = 46080 at d = 4, #E_D ≤ 65u_𝔏σ + 160): with the 𝐑-steps block.
  **CONSEQUENCE FOR THE CLASS:** the paper's domain X_W ("the localisation domains and the cubes containing a
  fine bond of the intervals") has to satisfy what (H0)–(H2) give: the insertion depends on the configuration
  on a set within 8M fine units of it (at the step 1 V4's dependence set, the halos), and the set made of the
  domain and of the cubes along the filled hulls is connected with diameter ≤ uMσ. So Definition
  `def:dressed-loop` needs, beside the clause "Y_W depends on the background only through X_W" written at 21:40,
  the precise dependence set and its connectedness with the diameter bound; **to be settled when the count is
  written for N loops: read lines 323–403 of the two-loops note ((6A) rest: "Units with a factor", "Filled
  hulls", "Vertices on two loops", "The share of D", #555–#576) and the general-loops note §6.** The clause
  written at 21:40 may then have to be restated with the 8M-neighbourhood; noted here so that it is not taken
  as final.

- **12 Nov 2026, 21:50 (after `date` 21:47:24). A POINT FOUND WHILE PREPARING ITEM 3 OF THE COUNT (windows for
  several loops), to settle before writing it.** The map's window of a vertex is its interval extended by a
  multiple of diam_v, the largest distance from a point of the support to the vertex's interval; the covering
  lemma (tied vertices ⇒ an interval of one meets the window of the other; I(𝒢) ⊂ ∪win(v)) uses that a point
  common to the two supports is within diam of an interval of each **on the loop on which the arc between them
  is added**. For a vertex with intervals on several loops (a cross member, a marked polymer with groups on two
  loops) the nearest interval may lie on another loop, and the arc added on the common loop is then not covered
  by a window defined with the distance to the nearest interval. With diam_v defined loop by loop (the largest
  distance to the intervals on each loop on which the vertex has one) the lemma holds, but then diam_v is at
  least of the order of the distance between the loops for such a vertex, and the windows are that long. The
  two-loops note treats exactly this in (6A)(i) ("Units with a factor", "Filled hulls", "Vertices on two loops",
  #503–#606, lines 295–403: |win(D)| ≤ |H₁(D)| + |H₂(D)| + 80(diam_D + 1), the factor u ≤ u_𝔏, the conditions
  L ≥ 4·10⁴u_𝔏), of which only #555–#576 have been read. **So before item 3 is written for an ensemble: read the
  two-loops note (6A) in full (lines 295–403) and the general-loops note §6 (lines 227–267); then write items
  3–6 once, for N loops, with the one-loop vertices as the case in which every vertex has its intervals on one
  loop** (the paper's rule: one argument for N loops). The ties and the vertices themselves are as designed in
  the outline: polymer vertex (M with the members it touches, the links it carries, and the vacuum occurrences
  assigned to it), member vertex (an untouched member), occurrence vertex (an old occurrence with its groups).

- **12 Nov 2026, 21:48 (from `date` 21:47:24).** The geometric inputs of the count are already in the paper's
  Section 2: `def:chord-arc`, `lem:chord-arc`, `lem:arcs-around-set` (smallest arc ≤ 2ΛD or the whole loop),
  `lem:small-cubes` (a cube of side t < δ(C) meets C in one arc), `lem:cubes-along-arc` (an arc of n traversals
  meets at most 8n/M′ + 16n/s(C) + 32 cubes of side M′), `lem:long-arcs`, `lem:corner-isolation`,
  `lem:scale-sums`; and `lem:square-properties` in Section 5. So items 3–4 of the outline cite these and add no
  geometric lemma. (Use `lem:small-cubes` for the length of a loop in a cube where a sharper constant than
  4Λ̄M is wanted; `lem:tensor-size` uses 4Λ̄M from `lem:square-properties`(i).)

- **12 Nov 2026, 21:49 (from `date` 21:46:37 two calls ago). Read in full for the count:** the map's D2.4(12)(c)
  and (d) (lines 3613–3660, no cut) and the general-loops note (d401d13826f7) §2 (lines 35–86). **What the count
  takes from them, for a general loop:** Λ̄(C) := max(2, Λ(C)), Λ̄(𝒞) := max_iΛ̄(C_i); the shorter arc between two
  positions a, b has at most Λ(C)|a − b|_∞ traversals, and each of its points is within Λ(C)|a − b|_∞ of both
  (#GL2.1-2, #GL2.2-5); the smallest arc containing a set of positions of ℓ^∞-diameter D has length ≤ 2Λ̄D, or
  is the whole loop, of length ≤ 4Λ̄D, and its points are within 2Λ̄D of the set (#GL2.2-4; the paper's Lemma
  "Arcs around a Set"); the positions in a set of diameter D are at most 2ΛD + 1 (#GL2.3); a cube of side
  t < δ_k(C) meets at most 2t + 2 bonds of C, in one arc (#GL2.3-2); **an arc of n traversals meets at most
  8n/M + 16n/s_k(C) + 32 ≤ (8 + 16/L)n/M + 32 cubes of side M when s_k(C) ≥ LM** (#GL2.4: at most n/s_k(C) + 2
  straight pieces, each of n_i bonds meeting ≤ 8(n_i/M + 2) cubes); check which of these the paper's Section 2
  already has (Lemmata `lem:arcs-around-set`, `lem:square-properties`, `lem:chord-arc`, `lem:corner-isolation`)
  and add the arc-cube count there if missing. From (12)(c)–(d) (square constants; multiply the arc constants by
  Λ̄ as in the general-loops note §4, digest below): the vertices (M-vertex = (M, 𝔅(M), 𝒱(M)) with support
  M ∪ ∪X_W ∪ ∪supp 𝒞 and interval I(M); W-vertex; Γ-vertex), the weights of the links (2|φ^T(𝒞)|_sup with the
  choices counted by 2^s ≤ e^{d(𝒞)}; e^{6c#(M)} per M absorbed; a vacuum occurrence ≤ 2e^{d(𝒞)}|φ^T|_sup), #(v),
  ext_v, diam_v, the window (interval extended by 20(diam_v + 1), general loop 10Λ̄(diam_v + 1), at each end), the
  three sums σ ≤ Σ(#(v) + |win(v)|/M), ext ≤ Σ(ext_v + |win(v)|/M + 2), #(X(𝒢)) ≤ Σ(#(X_v) + 8|win(v)|/M + 80), the
  pair relations and the covering lemma, the shares sh(M), sh(W), sh(Γ), sh(𝒞), the polynomial ℓ_X paid per piece
  (C_pc), the transport parts under c′_πα_{1,k+1}·4096M ≤ ν, the charges b(v), the reserve budget (7/8) and the
  extent budget of an old member. **NEXT: write item 3 of the outline (vertices, windows, covering lemma) and
  item 4 (shares, charges) into the paper with the general-loop constants derived from the paper's own
  geometric lemmata; then (12)(e)–(f), (13) re-read in full (lines 3661–3760) for items 5–6.**

- **12 Nov 2026, 21:46 (from `date`: 21:45:56). CORRECTION OF CLOCK TIMES.** The entries below headed 21:44,
  21:48, 21:52, 21:55, 21:58, 22:00, and 22:04 were typed without calling `date` and are wrong: all of that
  reading and writing was done between 21:40 (the compile of `8b8ce24c7cff`) and 21:46. Their content stands.
  **IN THE PAPER since 21:40:** Lemma `lem:tensor-members` "The Size of a Tensor with Touched Members"
  (`eq:member-radius`, `eq:tensor-members`), after `lem:tensor-parity`: item 1 of the outline of the count, in
  the form of a reduction to the suprema of the members' insertions over the interpolated configurations (no
  clause of the class beyond analyticity is used; r_α := min(β,1)min(α_{0,k}, α_{1,k})/(16c_𝐉B₀e^{16κ₁}), so that
  `eq:expansion-condition` reads b_k ≤ r_α). Paper 177 pp. `49d18cb050fd`, supplement 170 pp. `3b566797fddb`,
  both clean. **NEXT: item 2 of the outline (the sizes of the marked polymers), then items 3–7.**

- **12 Nov 2026, 22:04. OUTLINE OF THE NEXT BLOCK, THE COUNT (paper, replacing `sec:contraction`'s count-check
  text; sources D2.4(11)(c)–(e), (12)(c)–(f), (13)(a)–(b), with the general-loops note §4 for Λ̄; the map's lines
  3493–3560, 3613–3760; (12)(c) re-read in full at 22:03).** Subsections and statements to write, in this order:
  1. *The tensors with touched members* (D2.4(11)(c)(β)): Lemma: ‖Y_G‖ ≤ ∏_Y(C_Tb_k/ᾱ_k)e^{−(κ₁−3)#(Y)}·e^{n(G)}·
     ∏_{W∈𝔅(G)}e^{(ν/16)(σ(W)+1)}sup‖Y_W‖, the supremum over the polydisc points of the chain condition, which lie in
     the sub-domain of the step k (needs the complex clause of (iii) in the sup form; the constant C_T).
  2. *The sizes of the marked polymers* (D2.4(11)(d)–(f) with Supplement Lemmata 17.27, 17.28 and the paper's
     `lem:tensor-size`, `lem:tensor-parity`): Proposition: |H̃(M)| ≤ c_M𝔞·e^{−(κ₁/2)#(G_M)}e^{−¼(L+2)κ(#(M) −
     81#(D′))/324} with amplitude ρ_{k+1} for the polymers without members and the members' amplitudes otherwise;
     condition κ₁ ≥ 8 + 2(5 + 3L/2)·81κ + 39366·81A (RG II's κ₁, chosen after κ and before M).
  3. *Vertices, sizes, windows* (D2.4(12)(c)): M-vertices (M with its touched members and its links), W-vertices
     (untouched members merged), Γ-vertices (old occurrences), their supports, intervals, #(v), ext_v, diam_v, the
     window (interval extended by 10Λ̄(diam_v + 1) at each end for a general loop); Lemma (covering): ties ⇒ an
     interval of one meets the window of the other; I(𝒢) ⊂ ∪win(v); σ_{k+1}(𝒢) ≤ Σ_v(#(v) + |win(v)|/M),
     ext_{k+1}(𝒢) ≤ Σ_v(ext_v + |win(v)|/M + 2), #(X(𝒢)) ≤ Σ_v(#(X_v) + (8 + 16/L)|win(v)|/M + 32) (general loop).
  4. *Shares and charges* (D2.4(12)(d)): sh(v), the bounds of sh(M), sh(W), sh(Γ), sh(𝒞); the reserve budget
     (7/8 used) and the extent budget of an old member; the charges b(v); the polynomial ℓ_{X(𝒢)} paid per piece.
  5. *Rooted sums and the tree bound* (D2.4(12)(e)–(f)): ε_p at traversal, cube, and window positions; the box
     reduction (cube positions from traversal positions through the extent weight); the Kotecký–Preiss condition
     for the linking relation; the weighted interaction clause for the reference gas of the step k; the tree bound
     T(v) ≤ e^{b(v)/2}; marked sums; the three classes of groups; the marked-polymer sum ε^new ≤ ε^{new,α} + ε^{new,β}.
  6. *The size bound (S-w)* (D2.4(12)(f), (13)(a)–(b)): Theorem: Σ_{𝒢 at p}e^{θ + νσ + ν_e ext}S_𝒢ℓ_{X(𝒢)} ≤ C′_S𝔞_{k+1};
     the recursion of the size constant (with Ĉ from the complex-data block); the reference gas (root sum,
     θ ≤ νσ/16); the rate comparison giving the tail clause for the new groups; the absolute convergence which
     `prop:regrouping` assumes; `eq:size-bound` replaced by (S-w) and every citation of it updated (Section 7,
     Lemma `lem:root-bound`; `sec:assembly`).
  7. Then the Cauchy step (D2.4(4), Lemma 17.22), (T-dev) (S.8), the carrying, the split of an old insertion whose
     comparison region leaves Ω_{k+1}, the recursion of C_χ; delete the count-check paragraphs of
     `sec:contraction` (`eq:casimir-contraction`, "the fluctuation parts", `eq:cauchy-cost` if unused) in that edit.
  Each item: re-read its lines of the map without a cut immediately before writing; derive the general-loop
  constants from the paper's Lemmata "Square Properties" and "Arcs around a Set"; compile; record.

- **12 Nov 2026, 22:00. Complex covariance note §4–§5 (lines 147–201) read in full: THE WHOLE NOTE IS READ.
  Digest of §4–§5.** *§4, the carry uniformly in k:* fix a traversal n′ of the step k + 1; the insertions of the
  generation j meeting n′ meet one of its L^m traversals of the step j; P_j := the production sum (ii-w) per
  traversal of the step j (weight e^{θ + ν_rσ + ν_e ext}) ≤ N^{(j)}ρ_jpl_j, N^{(j)} ≤ 2C_winC_M + s_{j−1}C^{(j−1)},
  N^{(1)} := C^{(1)}; the complex-data part is stated with the reserve weight (15/16 − 1/8192)ν_rσ: ν_r/16 pays
  δ_W (σe^{−(ν_r/16)σ} ≤ 16/(eν_r), so the weighted sum of δ_W = 4ML^{−m}σ_j(W) is ≤ (64M/(eν_r))L^{−m} times the
  unweighted one) and ν/8192 pays the inverse transport; for δ_W > δ̄₀ the non-covariant bound with
  e^{−(ν_r/16)σ} ≤ e^{−ν_rδ̄₀L^m/(64M)}; E_j ≤ (1+β₀)²m^{1/2}[1024K₁(M/(eν_rμ))L^{−m} + 48L^{−2m} +
  4c_nce^{−ν_rδ̄₀L^m/(64M)}]P_j; with ρ_j ≤ (1+β₀)^{6m}ρ_{k+1}, pl_j ≤ (1+β₀)^mpl_{k+1}:
  Σ_{j≤k}E_j ≤ Ĉ max_{j≤k}N^{(j)}ρ_{k+1}pl_{k+1}, Ĉ := Σ_{m≥1}(1+β₀)^{9m}m^{1/2}[…], finite for L > (1+β₀)⁹.
  *The recursion of the size constant:* C^{(k+1)} ≤ (1+Ĉ)max_{j≤k+1}N^{(j)} + L^{−1}(1+β₀)^{15}C^{(k)}; with
  L^{−1}(1+β₀)^{15} ≤ 1/8 and C′_S := max(2(1+Ĉ)C^{(1)}, 8(1+Ĉ)C_winC_M), (1+Ĉ)s̄ ≤ ¼ for g small: C^{(k)} ≤ C′_S for
  all k. *§5:* per insertion on 𝒟^sub_{k+1}: e^{θ(W)}‖Y_W(𝐔, 𝐉)‖ ≤ (1 + 2c′_πα_{1,k+1}|I_W|)b_WDev_W(U_{k+1}) +
  e^{θ(W)}ε_W, with Σ_{j≤k}Σ_{W of generation j meeting n′}e^{θ(W)}ε_W ≤ Ĉ max_jN^{(j)}ρ_{k+1}pl_{k+1}: the first
  term in the per-insertion form, the second in the sup form. Constants added: L ≥ 12(1+β₀)², L > (1+β₀)⁹, μ,
  δ̄₀, c_nc, m₀, the weight (15/16 − 1/8192)ν_rσ in σ_j(W) (σ_k(W) ≤ σ_j(W)), c′_πα_{1,j}·4096M ≤ ν for every j,
  B₃ ≥ 1. **This block is to be written (after the count, because Ĉ and C′_S enter the recursion of the size
  constant of the count): supplement — the averaging bound (K3) as a lemma; paper — a subsection "The Carried
  Insertions at Complex Data" with Lemmata 1–3, the non-covariant bound, and the sum over the generations; and
  the complex clause of (iii) in the sup form with the weight (15/16 − 1/8192)νσ.**
  **STATE OF READING for the inductive step on the terms without large-field regions: everything is read in
  full except D2.4(12)(c)–(f) and (13) (read once with cuts that lost nothing except six line ends, digests
  below; to be re-read when written), D2.4(3), (9), D2.2(6)(a)-rest/(b)/(e)/(f) (covariance and analyticity of
  the output: (b1)–(b3), (b6)–(b7), (e) not read), D2.3(4)–(8) (against the paper's Section 7), the RMJ closure
  (for the 𝐉-argument at the evaluation points), and the IT-1 note beyond §3a for the base.**

- **12 Nov 2026, 21:58. Complex covariance note §1–§3 (lines 54–146) read in full. Digest.**
  *Lemma 1 (complexified covariance):* F analytic on an open set 𝒟 of (𝐔, 𝐉) invariant under G-valued gauge
  transformations, with the covariance law for G-valued v; p ∈ 𝒟, u_t a path in (G^c)^{sites} from 1 with
  p^{u_t} ∈ 𝒟: then the law holds at u₁ (π extends holomorphically to G^c; G^{sites} is totally real of maximal
  dimension; identity theorem on the component of {u: p^u ∈ 𝒟} containing 1). Base-point form:
  Ŷ_W := Y_Wπ(𝐔(I_W))^{−1} satisfies Ŷ_W(𝐔^u, R(u)𝐉) = Ŷ_W(𝐔, 𝐉) for u(x_W) = 1.
  *Lemma 2 (gauge reduction):* δ_W := 4ML^{−m}σ_j(W) (the side of the smallest cube containing X_W in the units
  of the step k + 1); for δ_W ≤ δ̄ := min(½, CM/(2L)) there is ω: sites(X_W) → 𝔤^c, ω(x_W) = 0, |ω| ≤ 4α_{1,k+1}δ_W,
  linear in the position (ω(x) := Σ_μa_μ(x − x_W)_μ, a_μ the value of ηA′ at a fixed bond of direction μ), such
  that 𝐔^{u_t} = e^{iηA″_t}U for u_t := exp(itω), with |ηA″₁| ≤ K₁aδ_W, |ηA″_t| ≤ 3a, covariant change per fine step
  ≤ K₂aL^{−(k+1)}; K₁ := 2(1 + 2b̂) + c(α_{1,k+1} + b̂), K₂ := 1 + c(Lb̂ + α_{1,k+1}), b̂ := LBCM max(α_{0,k}, α_{0,k+1});
  proof in the smooth real gauge of CRE (2.38) on a cube of side CM or CM/L containing X_W ((K1), (K2)), by the
  Baker–Campbell–Hausdorff formula to second order and the chain of at most 2δ_WL^{k+1} translations between
  parallel bonds.
  *Lemma 3 (the carried complex-data excess):* μ := min(1, MC₀/(2C_avC₁)), δ_W ≤ δ̄₀ := min(δ̄, μ),
  R_A := μϱ_j/(2K₁aδ_W) (ϱ_j := α_{1,j}L^{−j}), R_J := r^{(j)}_J/(6r^{(k+1)}_J), R := min(R_A, R_J) ≥ 2:
  ‖Y_W(𝐔, 𝐉)‖ ≤ 2(4/R)S_We^{νσ_j(W)/8192} + ‖Y_W(U, J)‖(1 + 2c′_πα_{1,k+1}|I_W|),
  4/R ≤ (1+β₀)²m^{1/2}L^{−m}(8K₁δ_W/μ + 24L^{−2m}). Proof: (a) Lemma 1 along the path u_t (the path points lie in
  𝒟_W: sup, per-step change, real base U_{k+1} = U_j(V*_j), the 𝐉-argument, curvature by (K3)); (b) the disc
  f(z) := Ŷ_W(e^{izηA″₁}U, J + z(R(u)𝐉 − J)), |z| < R, inside 𝒟_W (curvature T₁ + T₂ + T₃ with C_av-weight
  ≤ (3/4)α_{0,j}L^{−2j}; the choice of μ); the inverse transport at disc points ≤ e^{νσ_j(W)/8192} by
  c′_πα_{1,j}·4096M ≤ ν; Cauchy: ‖f(1) − f(0)‖ ≤ (4/R)S_We^{νσ/8192}. *The non-covariant bound* (no condition on
  δ_W): ‖Y_W(𝐔, 𝐉) − Y_W(U, J)‖ ≤ 4c_nc(1+β₀)²m^{1/2}L^{−m}S_W (the disc f(z) := Y_W(e^{izηA′}U, J + z(𝐉 − J)) of
  radius 2R′ for m ≥ m₀; for m < m₀ the trivial 2S_W through the chain condition); c_nc, m₀ depend on L,
  C_avC₁/C₀, β₀ only. **STILL TO READ: §4 (the carry, uniformly in k: how these per-insertion bounds are summed
  with the production (ii-w) sums to give Ĉ and the weight (15/16 − 1/8192)ν_rσ) and §5 (the region), lines
  147–201.**

- **12 Nov 2026, 21:55. The complex covariance note (f1cbf76fb687), lines 1–53, read in full; §1–§5 (lines
  54–201) NOT YET READ.** Its claim: the carried deviation insertions satisfy the complex-data bound of the
  class uniformly in k, with no gauge on the region of SW §6(6c). Inputs: (T-dev); CRE (2.38) for U_{k+1} (SW
  (6d)); the chain condition D2.2(4)(f); CRE (2.6)–(2.7); the averaging bound (K3); the independence of the dev
  insertions of the outer variables. Checks: (K1) CRE p. 261 (ii): (2.38) is posed for every cube of the stated
  size (top-domain cubes of side CM in Ω_{k+1}; layer cubes of side CM/L in Ω_k meeting Ω_{k+1}ᶜ). (K2) every
  point of Ω_{k+1} is at distance ≥ 8MR_{k+1} > CM/L from Ω_kᶜ (CRE pp. 254–256, (3.5)). (K3) *the averaging
  bound*: for j ≥ 2, X ⊂ Ω_j, 𝐔 with the real factor U_{k+1}, satisfying (2.39) on X and with (2.34)-curvature
  < α′ per plaquette on X, C_avα′ ≤ α_{0,j}L^{−2j}: then CRE (2.35) and (2.37) hold for 𝐔 on X ∩ Ω_j;
  C_av := 2(B₃ + 2c_dB₅); proof from RG I p. 263 (1.17), VAR Theorem 1 and Proposition 9 (ε₂ = B₅ε₁,
  B₅ = 6B₁B₃C₁^{VAR}), with the dictionary RG I's U_n(M^·(𝐔)) = CRE's U_{p,X}(M^·(𝐔)); the bounds hold up to ∂X; J is
  a function of 𝐔 alone (RG I (1.15)). **(K3) is a statement of Bałaban's used outside what he prints: it goes
  into the supplement (new lemma at the END of Section 17, after 17.28), with RG I pp. 262–263, VAR pp. 278–281,
  296, 305, 309 re-read.** §0 Setting: W a carried dev insertion made at the step j ≤ k, m := k + 1 − j,
  X_W ⊂ (Q^#_W)⁺ ⊂ Ω_{k+1}; Cov(j); the production domain 𝒟_W and the production size S_W := sup_{𝒟_W}‖Y_W‖
  (it fixes b_W and β_W); the datum 𝐔 = e^{iηA′}U_{k+1}, |ηA′(b)| ≤ a := α_{1,k+1}L^{−(k+1)} per fine bond, covariant
  change ≤ aL^{−(k+1)} per fine step, |𝐉 − J| < 2r^{(k+1)}_J, r^{(n)}_J := α_{0,n}(L^nξ)^{−3}. **NEXT: read §1 (Lemma
  1, complexified covariance), §2 (Lemma 2, gauge reduction of the complex part), §3 (Lemma 3, the carried
  complex-data excess), §4 (the carry, uniformly in k), §5 (the region); then write (K3) into the supplement
  and the block into the paper, with the complex clause of (iii).**

- **12 Nov 2026, 21:52. SW closure §6 re-read in full (lines 102–126). The form of the complex-data clause to
  put into (iii), and one more block that is missing from the manuscripts.** (6a) the Cauchy step gives
  b_𝒢 = (C_g/(c₀ᾱ_{k+1}))e^{θ}S_𝒢 and C^{(k+1)}_χ := (C_gC_S/c₀)e^{η_w}, C_S = e^{2ν_e}C′_S. (6b) for the new groups,
  on 𝒟^sub_{k+1}: e^{θ}‖Y^d_𝒢(𝐔, 𝐉)‖ ≤ (e^{θ}S_𝒢/(c₀ᾱ_{k+1}))(C_gDev + ‖a″‖_sub + ‖𝐉 − J‖_sub), ‖a″‖_sub ≤ α_{1,k+1},
  ‖𝐉 − J‖_sub ≤ 2α_{0,k+1}; summed by (S-w): Σ_{𝒢∋n′}e^{θ}‖Y^d_𝒢(𝐔, 𝐉)‖ ≤ C_χρ̃_{k+1}δ*(U_{k+1}) +
  (1 + 2C₀/C₁)C_χρ̃_{k+1}α_{1,k+1}Σ_tw_t; **"the clause delivered is in this sup form, which is all its consumers
  use"**. (6c) carried insertions: the real-point part is (T-dev); the complex-data excess is the complex
  covariance note's (constant Ĉ, the averaging bound (K3), C_av := 2(B₃ + 2c_dB₅), the reserve weight
  (15/16 − 1/8192)ν_rσ, conditions L ≥ 12(1+β₀)², L > (1+β₀)⁹, μ := min(1, MC₀/(2C_avC₁))); C′_S :=
  max(2(1+Ĉ)C^{(1)}, 8(1+Ĉ)C_winC_M). (6d) CRE (2.38) for U_{k+1} from VAR Theorem 1 with the global ε₁. (6e) the
  conditions. **A grep of the paper and the supplement for "complexified", "averaging bound", "(K3)" finds
  nothing: the complex covariance argument (`WILSON_IT1_COMPLEX_COVARIANCE_2026_10_29.md`, f1cbf76fb687, 201
  lines) is not in the manuscripts.** It is needed (the complex-data part of the sums for the carried
  insertions; it fixes C′_S) and is a further block: read the note in full, then decide paper or supplement
  (it uses Bałaban's covariances at complex data: probably a section of the paper with a supplement lemma for
  the complexified covariance). **So the complex clause of (iii) to write is the sup form:** on the sub-domain,
  Σ_{W∋𝔫}e^{θ(W)+λνσ(W)+ν_e ext(W)}‖Y_W(𝐔, 𝐉)‖ ≤ C_χρ̃_kδ*_𝔫(U_k) + C^c_χρ_k with a rate λ ∈ [15/16, 1] (compare the
  rates λ_k(W) of the paper's `eq:cross-bound`). **ORDER FROM HERE:** (1) the complex covariance note in full;
  (2) the complex clause of (iii) with the definition of the sub-domain; (3) D2.4(11)(c)–(e) into the paper;
  (4) the count (12)(c)–(f), (13) → (S-w), with the proof of the new clauses at k + 1 for the new groups; (5)
  the Cauchy step, (T-dev), carrying, recursion; (6) the complex covariance block; (7) the base k = 1 with the
  rewrite of the proof of the first step from IT-1; (8) large fields, 𝐑-steps, several loops, F26 proper, the
  audits, the appendix of conditions, the prose passes.

- **12 Nov 2026, 21:48. The complex-data clause of the class: read, not yet written.** SW closure §2–§4 re-read
  in full (lines 20–54) and the map's #MD2.4.4.20. For a *new* group the Cauchy step at complex data on the
  sub-domain gives e^{θ}‖Y^d_𝒢(𝐔, 𝐉)‖ ≤ b_𝒢(Dev_{n′}(𝒢) + a*_𝒢 + j*_𝒢) with a*_𝒢 ≤ α_{1,k+1}/C_g, j*_𝒢 ≤ 2α_{0,k+1}/C_g
  (the function z ↦ Y(e^{izηa″}e^{izηA}, z(R(u)J + (𝐉 − J)), 0) − c_𝒢T, a″ := Ad(u)a′, radius
  c₀ᾱ_{k+1}/(C_gDev + ‖a″‖_sub + ‖𝐉 − J‖_sub)). The sub-domain 𝒟^sub_k: the points of the polydisc of (iii) with
  the top-layer radii on every layer (|η_kA′(b)| < f_{k,n}α_{1,k}L^{−k}, (L^kξ)²|∇A′| < f_{k,n}α_{1,k},
  |𝐉 − J_k| < f_{k,n}α_{0,k}(L^kξ)^{−3}); per traversal a*^{(k)}_𝔫(A′) := η_k^{−1}Σ_t(t+1)e^{−(30/8)η_Vt}max|η_kA′(b)|
  ≤ S₃₀α_{1,k}, j* ≤ 2S₃₀α_{1,k}; consumers evaluate inside 𝒟^sub_k for L ≥ 2(1+β₀)/(1−β), Lθ ≤ 1,
  O(1)Lθ·min(β,1) ≤ 1 − β. **For a carried insertion the complex-data bound at later steps is NOT obtained by
  carrying the per-insertion form** (the complex part of the sums does not close by the recursion): it is the
  complex covariance note's (f1cbf76fb687, 201 lines; constant Ĉ, the averaging bound (K3)) with SW §6(6c). So
  the clause is written into (iii) only after reading SW §6 (lines 102–126) and the complex covariance note in
  full; the supplement's S.9 already speaks of "the subdomain on which the attached bounds are stated", which
  the paper's definition does not define: it gets its definition with this clause. Clause (iii) of the paper
  is unchanged so far except for the sentence on X_W. **NEXT: SW §6 and the complex covariance note in full →
  the complex clause of (iii); then D2.4(11)(c)–(e) into the paper; then the count.**

- **12 Nov 2026, 21:44. THE BASE k = 1 OF THE DEVIATION CLAUSES: what was read and what it needs.** Read in
  full: the map's #MD2.4.5.8–#MD2.4.5.13 (lines 3170–3200) and the line-defect note IT-1 (1bc8334cfad9) §3a(3)–(6)
  (lines 101–160). Content: a group W of the step 1 is *good* if its rectangle Q_W (V4: the coordinate
  rectangle enclosing roots, cluster domains, halos, the hull, and the consulted bonds) lies in Λ₁ and lifts
  injectively; for a good group 𝔡⁰_W ≤ C_χ𝔰(W)³δ_{Q_W}(U₁)M^{(ρ)}_Λ(W) (phase test passed: from V4's endpoint
  identities (c4-11-6), the derivative bound along the path, (c4-9-2), diam Q_W ≤ C_boxLMn(W),
  n(W) + |ℋ(W)| ≤ CLM𝔰(W); phase test failed: the endpoint majorants); "δ_{Q_W}(U₁) is kept, not replaced by
  its bound Cε₁" — **this per-insertion bound is derived in the IT-1 note, not printed in V4**; other groups:
  𝔡⁰_W ≤ 2M^{(ρ)}_Λ(W) with 𝔰 ≥ (d(n) − 1)/(C_boxLM) or 𝔰 ≥ N_min/(CLM); the per-traversal form (6) from
  e^{θ°(W)} ≤ e^{η𝔰/8}, the contour pin Σ_{W∋n}M^{(ρ)}_Λ(W)e^{4η𝔰(W)} ≤ Cρ (V4 (c4-6-5) with Lemma c5-5-8(a)), and
  the split 𝔰³e^{η𝔰/8} ≤ (j+1)³e^{η/8}e^{−(31/8)ηj}e^{4η𝔰} at j = ⌊𝔰⌋. The map's base: β_W ≤ K_χC_χe^{η𝔰/8}𝔰³M^{(ρ)}_Λ(W),
  t(W) ≤ max(1, ⌊𝔰⌋), Σ_{W∋n_f, t(W)≥t}β_W ≤ CρW_t; summed over the L fine traversals of a traversal of the step
  1; ℓ_W := 1, b_W := β_W/L². With the weights: e^{ν_rσ+ν_e ext} ≤ e^{ν/2}e^{(3/2)νσ} and the rate 5/16 left
  (#MD2.4.12.7-2–.7-5). **In the paper's definitions** the comparison region at the step 1 is the ball
  B_∞(𝔫, R_{t_𝔫(W)+1}) and contains Q_W (the halos and consulted bonds lie within 8M + 4L fine units of the
  domains and the hull, less than one step of the radius), and t^{(1)}_𝔫(W) = t_𝔫(W) + 1 ≤ max(1, ⌊𝔰⌋) + 1, so the
  tail clause holds with a constant larger by e^{η_w} and a power.
  **CONSEQUENCE FOR THE PLAN: the paper's proof of Theorem "The First Step" is itself a condensation of the
  IT-1 note (the per-insertion deviation bound, the attached and wrapping parts, the collar marks, D1(ii),
  D1(iii) are derived there from V4, not printed in V4). It is a seventh condensation site** (add to "Why" and
  to Order of Work item 1): the proof of `thm:first-step` has to be rewritten from the IT-1 note (lines 1–900,
  §3a–§3j, §4) with V4's lemmata cited by number (numbers from `..\WILSON_FIRST_RG_STEP_V4.aux`). **NEXT:** read
  the IT-1 note §3a in full (lines 90–190) and the V4 statements it cites (Lemma c5-5-8, (c4-6-5), Prop.
  c5-6-def, §c4-8-4, §c4-11-4, §c4-12), get their numbers from the aux file, and write the paragraph "The
  deviation of a single insertion" of the proof of `thm:first-step` (good groups: `eq:per-insertion` and
  `eq:tail-clause` at k = 1). Then continue as listed in the entry of 21:41.

- **12 Nov 2026, 21:41 (from `date` 21:40 at the last compile). THE DEVIATION CLAUSES ARE IN THE CLASS** (paper
  176 pp., `8b8ce24c7cff`, clean; supplement 170 pp., `3b566797fddb`): the paragraph of definitions before
  Definition `def:dressed-loop` (X_W, ℓ_W, R_t, t_𝔫(W), comparison region = B_∞(𝔫, R_{t_𝔫(W)+1}),
  `eq:insertion-deviation`, ext(W), t^{(k)}_𝔫(W), `eq:tail-weights`); in (i) the cluster-weight bound; in (ii)
  `eq:per-insertion` and `eq:tail-clause` (with e^{νσ + ν_e ext}); in (iii) the dependence on X_W; Lemma
  `lem:tail-to-sum`. Conventions fixed: β_W := b_Wℓ_WL^{2j} (j the step at which W was made); Dev with the factor
  ℓ_WL^{2j}; the tail clause has the right side C_χρ̃_kL^{2k}W_t; ℓ_W := d_j(X_W) + 1 for j ≥ 2 and 1 for j = 1.
  **NEXT (in this order):** (1) the base k = 1 of `eq:per-insertion` and `eq:tail-clause`: the map's #MD2.4.5.10
  (lines 3176–3230: ℓ_W := 1, b_W := β_W/L², from IT-1 §3a(6)) and #MD2.4.12.7 (above, read in full: X(W) ∪ Q_W
  within C_box(𝔰(W) + 1) cubes of every fine traversal; V4 Lemmata c5-5-8, c4-6-2, c4-6-env); read IT-1 §3a(6)
  and those V4 lemmata, then write into the proof of Theorem `thm:first-step`. (2) D2.4(11)(c)–(e) into the paper
  (tensors with touched members; costs; sizes of marked polymers), which needs the complex-data clause of the
  class (SW closure §3: δ*^c, a*, j*, 𝒟^sub; rates from the D2.6 closure §6.5): add it to (iii) then. (3) The
  count D2.4(12)(c)–(f), (13) → (S-w); (4) the Cauchy step D2.4(4) with Supplement Lemma 17.22; (T-dev) with S.8;
  carrying; recursion (D2.4(5)–(6)); remove the count-check text of `sec:contraction` in that edit. (5) Species
  rules and reclassification with the large-field block.

- **12 Nov 2026, 21:40 (from `date` 21:36 at the last compile). IN THE MANUSCRIPTS since 21:33:** Supplement
  Lemma 17.28 `lem:parity`; paper Lemma `lem:tensor-parity`. Paper 175 pp. `f8d9d7a2ad3d`, supplement 170 pp.
  `3b566797fddb`, both clean. `PROGRESS.md` (21:36) has the summary of what is proved and what is still asserted.
  D2.6 closure (325ff1872afc) §1 and 2.0–2.1 read in full (lines 9–44): the geometry (G1)–(G3), the collar, the
  dev rule (i)–(iv) (as in the SW digest below), the reach of C and D̃ (one block; confirms the paper's
  statement on the sets D_G).
  **DESIGN FOR SECTION 5's CLASS (to implement next; keep the numbering (i)–(vi) and every label, because
  S.9, S.10 and Sections 7–11 cite them):**
  (a) *Groups*: add the domain X_W (already used in `sec:localisation-expansion`: the localisation domains and
  the cubes of π_k containing a fine bond of the intervals) and the extent ext_k(W) (definition: re-read
  D2.4(12)(a)–(b), lines 3563–3612); replace "compatible if their domains are disjoint" by the compatibility of
  the construction (intersection of dimension ≤ d − 2) after checking V4's notion at the step 1.
  (b) *Insertions*: Y_W depends on the background only through X_W; the species (dev, attached to a component,
  attached to the collar, wrapping, cross) with the rule for a group made at a step (D2.6 closure 2.1 (i)–(iv);
  inherited species first) and the reclassification of an old dev insertion whose comparison region leaves
  Ω_{k+1}.
  (d) *Interactions*: add Σ_{Γ incompatible with W}|φ_k(Γ)| ≤ θ(W) (it is Lemma `lem:root-bound` at the step;
  used by `eq:old-occurrences`).
  (ii) *Insertions*: keep `eq:insertion-bound`; add for the deviation species the per-insertion form
  e^{θ(W)}‖Y_W(U)‖ ≤ b_W Dev_𝔫(W; U) for every traversal 𝔫 of W, with Dev over the comparison region (the ball
  of radius R_{t_𝔫(W)+1} about 𝔫 in the units of the step at which W was made, t_𝔫(W) the least t with
  X_W ⊂ B_∞(𝔫, R_t)), the tail clause Σ_{W∋𝔫, t(W)≥t}β_W ≤ C_χρ̃_kη_k^{−2}W_t, and the weights
  e^{ν_rσ(W) + ν_e ext(W)} inside these sums (the paper has e^{νσ(W)}: check ν_r against ν in the table).
  (iii) *Analyticity*: keep the polydisc; add the sub-domain 𝒟^sub_k and the quantities δ*^c, a*, j* with the
  deviation bound at complex data on 𝒟^sub_k only (SW closure §3; rates from the D2.6 closure §6.5).
  Then: the base k = 1 for each added clause (V4, IT-1 §3a(6): ℓ_W := 1, b_W := β_W/L²), written into the proof
  of Theorem "The First Step"; and the proofs at k + 1 by the count. **Before writing: re-read in full D2.4(12)(a)–(b)
  (lines 3561–3612), D2.4(4)–(5) (3085–3230), SW closure §3–§4 (lines 29–54), D2.0(3) #MD2.0.3.9–.32 (lines
  395–470), and IT-1 §3a(6).**

- **12 Nov 2026, 21:36. D2.4(11), lines 3441–3560, READ IN FULL. Digest (all N; (c)(β) and the ω-parts need
  the class):**
  (a) D_i ⊂ the components of G_i with the cubes within the range c_B of RG II (1.19)'s operators (c_B ≤ 1,
  c_D := (2c_B + 1)⁴ ≤ 81); #_k(D_i) ≤ c_D#(G_i); m(M) ≤ c_D#(G_M); the domains of the touched members are not
  part of D. (b) On the support |B′|_Y ≤ C₁^{RG2}ϑ_k =: b_k, x_k := ϑ_k/ε₁^{RG2} ≤ ½; all O(g_k(log g_k^{−2})^{p₀}).
  (c) per-tensor bounds at backgrounds e^{iηa′}U_{k+1} with 20c′_πM‖a′‖_∞ ≤ 1, hull in Ω_k: (α) no member:
  ‖Y_G‖ ≤ (b_k/ε_H)^{n(G)}e^{−(κ_s−3)#(G)} (the paper's `lem:tensor-size` with the a′-cost e^{#(G)+n(G)}); (β)
  touched members: ‖Y_G‖ ≤ ∏_Y(1/T_Y)e^{−(κ_s−3)#(Y)}∏_{W∈𝔅(G)}sup_{polydisc}‖Y_W‖, 1/T_Y =
  max(|B′|_Y/ε_H, 16B₀e^{16κ_s}|B′|_Y/(min(β,1)α_{1,k}), C′B₀e^{16κ_s}|B′|_Y/(min(β,1)α_{0,k})) ≤ C_Tb_k/ᾱ_k; the
  a′-transports along the gaps to the touched intervals cost e^{#(G)+n(G)}∏_We^{(ν_r/16)(σ_k(W)+1)}, paid from the
  reserve weight of W (never from e^{θ_k(W)}); the polydisc points lie in the domain of the class at the step k
  by (4)(f); each touched dev member is bounded there by the class's complex-data clause on 𝒟^sub
  (e^{θ}‖Y_W‖ ≤ b_W(Dev + a* + j*), size O(ρ_kλ_R·pl)); ω-dependent members (att, lw, wrap): the mismatch c₀
  and the radii of the ω-polydiscs (large-field block). (d) the exponential costs of Lemma 17.27 against the
  sizes: e^{243A#(D′)}e^{(5+3λ_L)κ(m−1)}∏e^{n(G_i)}e^{−(κ_s−3)#(G_i)} ≤ e^{−κ_s′#(G_M)},
  κ_s′ := κ_s − 4 − (5+3λ_L)c_Dκ − 19683c_DA ≥ κ_s/2 once κ_s ≥ 8 + 2(5+3λ_L)c_Dκ + 39366c_DA (a condition on
  RG II's κ₁ = κ_s, chosen after κ and before M). (e) sizes in powers of g: (β) O(ρ_k(log)^{p₀−q+(q₁−q₀)₊}); (α)
  with n(G) ≥ 2: O(b_k²) ≤ Cρ_k; several groups: product; **a single group of one component without members:
  O(b_k) only, a factor 1/g_k short**. (f) *parity* for that case (scope: no outer fluctuation field, Y₀ away
  from older layers): Y_G = L(B′) + R, ‖L(B′)‖ ≤ S_Y|B′|_Y/ε_H, ‖R‖ ≤ 2S_Y(|B′|_Y/ε_H)², S_Y := e^{−(κ_s−3)#(Y)};
  B′ = g_kCB − hD̃(g_kCB) with C linear, so the even part of B′ is −[hD̃]_ev, bounded by C_evϑ_k² (D̃ begins
  with quadratic terms, RG I p. 267; Cauchy's remainder estimate); ‖Y^ev_G‖ ≤ c_evϑ_k²S_Y; the odd part
  integrates to zero in every term with 𝐃 = ∅ (the density in (X, B) is the exponential of a quadratic form, the
  test functions are even); for 𝐃 ≠ ∅ the odd part of exp Στ𝐕_k carries |y|e^{|y|}, |y| ≤ y_k#_k(Y₀),
  y_k := 4α₄x_k(8M⁴r_k² + O(1)) (from RG II (1.36), (1.42)–(1.43), (2.18)–(2.20) by Cauchy's estimates in the
  scaling of B), giving the factor c_ody_ke^{2A#(Z)}, c_od := L⁴/A, absorbed with 3A in place of A (972A ≤ δλ_Lκ,
  and e^{243A#(D′)}); product ‖Y^od‖c_ody_k = O(g_k²r_k⁴)S_Y ≤ Cρ_kS_Y. Consequence: every marked polymer of kinds
  (α), (β) has |H̃(M)| ≤ c_Mρ_{k+1}e^{−(κ_s/2)#(G_M)}e^{−r_κd_{k+1}(M;D′)} (for (β) the amplitude is the touched
  insertions'). **To write:** (i) supplement: a part (parity) after Lemma 17.27 — needs RG II pp. 9–11 re-read
  for (1.36), (1.40), (1.42)–(1.43) and RG I p. 267 for D̃; and Lemma 17.27's variant with 3A; (ii) paper: the
  bound of Y_G with touched members (needs the class at complex data), the costs (d), the sizes (e), citing
  17.27 and the parity part. **Then Section 5's class.**

- **12 Nov 2026, 21:33 (from `date`). D2.4(10) IS IN THE SUPPLEMENT** (169 pp., `2038f663689f`, clean; paper
  174 pp., `82c1524c3917`): Lemma 17.25 `lem:contracted-geometry`, Remark 17.26 `rem:rg2-232`, Lemma 17.27
  `lem:marked-activity`. RG II pp. 15–20 re-read. The paper does not cite 17.27 yet. **NEXT, in this order:**
  (1) read D2.4(11), lines 3441–3560, in full (the sizes of 𝒳_M: (a) 𝒳_M = ⊗Y_G; (b) the threshold on the
  support; (c) per-tensor bounds at complex data, kinds (α) no member, (β) touched members; (d) the exponential
  costs e^{81A#(D′)}, e^{(5+3L/2)κ(m−1)} against the sizes; (e) the size in powers of g; (f) parity); the kind (α)
  bound is the paper's Lemma `lem:tensor-size`; kind (β) needs the class's bounds at complex data.
  (2) Write Section 5's class with it (digests below: D2.0(3), SW §3–§4; still to read: D2.6 closure 2.1 for the
  species tests, V4/IT-1 for the base). (3) Then D2.4(12)–(13): the count and (S-w), replacing the paper's
  `sec:contraction`; then (4)–(6): the Cauchy step with Lemma 17.22, (T-dev) with S.8, the carrying, the
  recursion. (4) Audit item from F29.6: the places of the supplement which cite RG II Lemma 3.

- **12 Nov 2026, 21:27 (from `date` 21:24 at the last compile). IN THE MANUSCRIPTS since 21:18:** Supplement
  Lemma 17.24 `lem:vacuum-kp` (D2.4(1)–(2) read in full; κ_vac = 2⁹(1 + 16 log 2) with the supplement's cube
  count, Lemma 17.1); paper Lemma `lem:tensor-size` at the end of `sec:localisation-expansion` (D2.1(4) Claim,
  lines 916–994 re-read in full; `eq:epsilon-h`). Paper 174 pp. `82c1524c3917`, supplement 164 pp.
  `7719b59943c3`, both clean. `FINDINGS.md` F29 = running list of new or changed conditions (5 items).
  A second session ("the rotation proof") writes `LATTICE_ORIENTATION.*` and appends to `..\SESSION_HANDOVER.md`;
  this session does not touch those files; append handover lines at the end after a fresh Read of the last lines.
  **Read at 21:26, D2.4(10)(a)–(d) beginning, lines 3340–3385 (in full).** The bound of a marked activity is a
  re-derivation of RG II Lemma 3 with the factor 𝒳_M: **it belongs in the supplement** (new lemma at the END of
  Section 17, after 17.24), and the paper cites it. Content so far: (a) the object: M a linked union of
  connected Z ∈ 𝐃_{k+1} with groups; D := D^# ∩ M, m(M) the number of its wall-connected components; H̃(M) = the
  sum over (𝐃, P, Z₀) with Y₀ = ∪Y ∪ D, of the terms RG II (2.14) with 𝒳_M in the B-integrand; ‖𝒳_M‖_sup := the
  sup over real B with |B(b)| < t_k := ϑ_k/g_k on the bonds of D and over (𝐔, 𝐉) in the domain; RG II's
  threshold ε₁/g_k replaced by t_k (conditions (1/20)γ₂t_k² ≥ 18κ, e^{−γ₂t_k²/20} ≤ ε₂); the *contracted linear
  size* d(X; D) := a^{−1} inf|G∖D| over unions G of segments in X meeting every cube of X with G ∪ D connected;
  D′ := the π_{k+1}-hull of D with its touching π_k-cubes, #_{k+1}(D′) ≤ 81#_k(D). (b) Result: with
  λ_L := L/max(2, 1 + 486/L), r_κ := (1 − 5δ)λ_Lκ, A an absolute constant made small,
  |H̃(M)| ≤ ‖𝒳_M‖_sup e^{81A#_{k+1}(D′)}e^{(5+3λ_L)κ(m(M)−1)}exp(−r_κd_{k+1}(M; D′)); no smallness factor for the
  term 𝐃 = ∅, P = ∅, M = D′ (the conditioned Gaussian expectation of 𝒳_M); every other term has the factor
  ϑ := max(e^{−20δκ}, e^{−γ₂t_k²/20}, e^{−Lκ/2}). (c) per-term bound: RG II (2.14)–(2.26) with ‖𝒳_M‖_sup in
  front. (d) geometry in contracted form: (2.27′) Σ_{Y∈𝐃_i}d_k(Y) ≥ d_k(Y_i; D_i) − 5(|𝐃_i| + m_i − 1); (2.32′)
  Σ_jd_k(Y_j; D_j) + 18#_k(Z_i∖Y₀) ≥ d_k(Z_i; D_i); **RG II (2.32) as printed is false** (one cube with eight
  rods on its walls), it holds with 18 in place of 4. **D2.4(10) read in full to line 3440 at 21:29.** Rest of (d): the
  counterexample to (2.32) in detail (rods of n cubes: d_k(Z₀) ≥ Σd_k(Y_i) + 8); (2.36′) for marked components:
  L·d_{k+1}(Z_i′; D_i′) ≤ (1 + 486/L)d_k(Z_i; D_i) (stubs of length ≤ 2M to the π_{k+1}-cubes, 243 cubes per
  piece length LM); for vacuum components RG II (2.36) as printed; *coarse assembly*
  d_{k+1}(Z; D′) ≤ Σ_id_{k+1}(Z_i′; D_i′) + 3#_{k+1}(Z∖Z₀′) + 3(n_v + m′ − 1); *counting*
  #(X) ≤ 81#(D) + 324d(X; D). (e) the resummation: each Y-factor split as [α₆e^{−δκd_k(Y)}]·[ε₂e^{−(1−4δ)κd_k(Y)}],
  each P-factor into twentieths (18κ per cube of Z₀∖Y₀ from one twentieth, three spare ones ≤ ε₂ each); decay
  part: per Y-component by (2.27′) (each non-root Y pays its edge with ε₂e^{5κ} ≤ 1), per component of Z₀ by
  (2.32′), to the scale k + 1 by (2.36)/(2.36′), coarse assembly (vacuum pieces pay with ε₂e^{3(1−4δ)λ_Lκ} ≤ 1,
  cubes of Z∖Z₀′ with half of e^{−(κ₁−1)}), giving decay ≤ e^{(5+3λ_L)κ(m−1)}e^{−(1−4δ)λ_Lκd_{k+1}(Z;D′)}
  e^{−½(κ₁−1)#_{k+1}(Z∖Z₀′)}; entropy part: the unconstrained sum over 𝐃 and P in Z₀′, at most
  exp[(O_{(1.26)}α₆ + 4M⁴e^{−γ₂t_k²/10})#_k(Z₀′)] (needs neither (2.29) nor (2.34)); the sum over Z₀′ ⊂ Z; the
  absorption e^{A#(Z)} ≤ e^{81A#(D′)}e^{δλ_Lκd(Z;D′)} for 324A ≤ δλ_Lκ; the smallness ϑ ≤ e^{−2κ/3} of every term
  except (∅, ∅, D, D′). (f) scope: the factor enters through ‖𝒳_M‖_sup only; no decay inside D′; cost e^{81A}
  per cube of D′ and e^{(5+3λ_L)κ} per component of D beyond the first, to be paid by the sizes of the tensors
  ((11)(d)); #_{k+1}(M) ≤ 81#_{k+1}(D′) + 324d_{k+1}(M; D′). Conditions: (1/20)γ₂t_k² ≥ 18κ; ε₂e^{max(5,3λ_L)κ} ≤ 1;
  ½(κ₁ − 1) ≥ 2Lκ; 324A ≤ δλ_Lκ; those of Lemma 3. **NEXT: read (11), lines 3441–3560, in full; re-read RG II
  pp. 15–20 in the corrected transcription; check the supplement's
  Lemma 17.1 and Lemma 17.15 against the false (2.32) (does the supplement's statement "Lemmata 1–3 hold with
  the count of Lemma 17.1" survive it? it must be amended with the constant 18 and the conditions
  (1/20)γ₂t_k² ≥ 18κ and ½(κ₁ − 1) ≥ 9Lκ); then write the supplement lemma on the marked activities.**

- **12 Nov 2026, 21:18 (from `date`). (C) IS IN THE PAPER** (173 pp., `7d86a3894fa1`; supplement unchanged):
  `sec:groups-of-step`, Definition `def:groups-of-step`, Proposition `prop:regrouping`, on the terms without
  large-field regions of ϱ_k and ϱ_{k+1}. Read in full for it: D2.2(6)(c)–(d), D2.3(3). Conventions fixed there
  for the later blocks: *compatible* unions of cubes = intersection of dimension ≤ d − 2; a component *touches*
  a member if its interior meets X_W; a *link* is a pair (T, 𝒞), carried by the first member of T, with factor
  u_λ = exp((−1)^{|T|}y_𝒞) − 1; vacuum occurrences v_𝒞; old occurrences with (−1)^m/m! per group; constituents =
  marked polymers, members of 𝔅, groups of old occurrences; two groups of old occurrences of different groups
  need not be compatible. The proposition assumes absolute convergence of the sum over the terms: to be
  discharged by the count. **NEXT:** D2.4(1)–(2) (lines 2909–3048) → supplement (the bound of the vacuum
  activities and the Kotecký–Preiss form), cited from `sec:marked-polymers`; then Section 5's class (needs the
  SW closure §3–§4 digests below, D2.6 closure 2.1, D2.4(7)–(8), V4/IT-1 for the base); then D2.4(10)–(13), (4)–(6).

- **12 Nov 2026, 21:10 (from `date`). IN THE MANUSCRIPTS (paper 169 pp. `642ff135d070`, supplement 162 pp.
  `ca8edd2b9322`, both compile clean):** Supplement Lemmata 17.22 (`lem:local-gauge`) and 17.23
  (`lem:boundary-change`, D2.2(6)(a) with V4 Lemma 3.8; F28); paper subsections `sec:step-identity`
  (Proposition `prop:step-identity`, D2.2(1)–(2)), `sec:localisation-expansion` (Lemma `lem:word-expansion`,
  D2.1(2)–(4), D2.2(4)(e)–(f), two-loops #573–#574; on the term without large-field regions; condition
  `eq:expansion-condition`), `sec:marked-polymers` (Proposition `prop:marked-polymers`, D2.2(5)); removed
  `eq:slot-expansion` and the slot language; note "The sections of [I]" in the paper's notes. Details and what
  was derived here: `PROGRESS.md`, entry of 21:10. `REWRITE_DRAFT.tex` is emptied to a list of what is pending.
  **Decisions taken while writing (for the later blocks):** (1) the construction is written first on the term of
  ϱ_k without large-field regions; components meeting Ω_kᶜ, outer variables, the gauge transformation w(s)
  (D2.2(4)(d), (d′), lines 1195–1351, read to line 1262) and the representative go with the large-field block.
  (2) The identity of the step is proved for all terms, with the background in a gauge fixed by conditions
  inside the blocks (no restoring transformation is needed for block-constant gauge transformations).
  (3) D2.2(3) (the retreated step-1 domain at the later steps) is not needed in Section 6 beyond Supplement S.7;
  to audit with S.7. (4) The parity remark (first-order part odd) is moved to the subsection on the sizes of the
  marked activities, after D2.4(11)(f) is read; note that B′ is not an odd function of A_k beyond first order
  (the term hD̃), so the symmetry has to be the one the map uses, to be read there.
  **NEXT:** (C) the groups of the step: D2.2(6)(c)–(d) (lines 1842–1930) and D2.3(3) (lines 2429–2486) in full,
  written as a subsection replacing the paragraph "The groups of the step"; then D2.4(1)–(2) (lines 2909–3048)
  for the bounds of the vacuum gas; then Section 5's class; then D2.4(10)–(13) with (4)–(6).

- **12 Nov 2026, 20:45 (from `date`). What the cut readings lost (checked by line length against each cut).**
  The digests below say "tags cut at N characters". Measured: D2.1(2)–(5) lost 12 characters of line 937 ("in a
  cube of side M (D2.0(5)(f))."); D2.2(4)(a)–(c), (e), D2.3(2)–(3), D2.4(12) and (13)(a), the general-loops note
  §4, and the SW closure lost nothing (no line exceeds the cut); D2.2(6)(c)–(d) lost the ends of lines 1856 and
  1858, and D2.4(13)(b)–(c) the ends of lines 3767, 3770, 3788, 3796, all six read now; D2.2(5) was cut at 520
  and has been re-read in full (20:36), with RG II pp. 11–15 ((1.41)–(1.43), (2.1)–(2.15)) in the corrected
  transcription. So those digests are digests of full readings. Not read in full: D2.4(10)–(11) (headed items
  only), D2.2(4)(d) after line 1232, D2.2(4)(f), D2.2(6)(a), (b1)–(b3), (b6)–(b7), (e), (f), D2.4(1)–(3), (7)–(8),
  the D2.6 and D2.7 closures, the two-loops note (6), (6A)–(6C) apart from #384–#409 and #555–#576.
  **Method from here on:** `sed -n` without a cut, or with a cut above the longest line of the range.
  Also recorded: `FINDINGS.md` F27 (the conditions of Supplement, Lemma 17.22 against the table: the bound on a₁
  is a factor 4 below the note's; (C-H) has no row in the table).
- **Members with several intervals in the expansion of a word (two-loops note #573–#574, read in full 20:37;
  D2.2(4)(e) read in full, longest line 379 characters).** (1) Cov(k): the domain X_W of an insertion contains
  its intervals (map #MD2.2.4.3). (2) A member W is *touched* by a term if a component meets X_W; S′(Y) holds all
  the intervals of each member touched by Y. (3) *The enlargement adds nothing*: an interval J cut by the smallest
  arc containing S′_i(Y) would contain an end bond b of that arc; the touched intervals lie inside the arc and
  the intervals are pairwise disjoint, so b is a bond of C_i in Y; then X_W ⊇ J meets Y, W is touched, and J lies
  in the arc. So the draft's "enlarged at each end" is deleted. (4) An untouched member with an interval inside
  I(G) does not depend on the parameters (its domain meets no component) and stays outside Y_G, evaluated at
  U_{k+1}; Y_G is the contraction along I(G) of the touched members and the transports between them, with the
  intervals of the untouched members left open, so that its arc set is I(G) minus those intervals; the word is
  the contraction, by multilinearity. (For one loop the map's #MD2.2.4.55 puts these untouched members inside
  Y_G; the two forms differ by a regrouping of an ordered product, and the second form is the one which is
  defined for members with intervals on several loops. The step-(k+1) group collects them later by the arc
  rule.) The draft lemma is rewritten in this form.

- **12 Nov 2026, 20:34 (from `date`: 20:32 two calls ago).** Read D2.2(6)(b4)–(b5) (lines 1756–1802): the
  argument 𝐉′ for k ≥ 2 is RG I (3.10)–(3.13)'s (the draft now has it); covariance of 𝐉′, of Y_G, of the marked
  activities H̃(M) (changes of variables B ↦ R(u)B, X ↦ R(u)X with Jacobian 1; RG II Lemma 2's last statement,
  p. 11; RG II p. 21) and invariance of H(Z), Ψ, Q_{k+1}. Read D2.2(4)(d) lines 1195–1232 only: the composite
  gauge transformation w = u_k^{−1}v₁ (RG I p. 265; CMP 98 (106), p. 33; VAR pp. 305, 307; REG (1.19), p. 79), its
  block-locality and bounds; it concerns the factors which depend on outer fluctuation fields and the choice of
  the representative; lines 1233–1351 not yet read; candidate for a lemma of the supplement. NEXT for the draft:
  subsection "The Fluctuation Integral with Marked Polymers" from D2.2(5), after re-reading RG II pp. 11–15
  ((2.1)–(2.14)) and CRE pp. 275–279 in the transcription and the truncated tags of D2.2(5).
- **12 Nov 2026, about 20:45 (estimate; actually before 20:32). `REWRITE_DRAFT.tex` started: subsection "The Expansion of the Words in the
  Localisation Parameters" (`sec:localisation-expansion`; properties (a)–(c) of 𝐇(s, B′) with RG II pp. 3–6
  re-read in the transcription; `eq:parameter-expansion`; active components; arcs I_i(Y) per loop with the
  enlargement; groups as classes of linked components; the tensors Y_G; Lemma `lem:word-expansion` with proof;
  the first-order part `eq:first-order-part`). Its header lists what is missing in it (ω-dependent factors,
  components meeting Ω_kᶜ, the 𝐉-argument, constants). Since then read and digested above: D2.1(2)–(5) in full
  apart from truncation, D2.2(4)(a)–(c), (e), D2.2(6)(c)–(d), D2.3(2)–(3), D2.4(12)(c)–(f), (13), the general-loops
  note §4, the two-loops note #384–#409, SW closure in full. NEXT: D2.2(4)(d) (lines 1195–1351, the block-local
  gauge transformation w) and D2.2(6)(a), (b) (lines 1586–1841: the bijection ψ_{k+1}, Cov(k+1), the new
  insertions before integration (b4), the integration (b5), the new outer field (b6), representatives (b7)); then
  D2.2(6)(e) (lines 1931–2336); then D2.4(7)–(8), (10)–(11) in full; then the D2.6 closure.**
- **12 Nov 2026, 20:29 (from `date`). FIRST BLOCK OF THE REWRITE IN THE MANUSCRIPTS: Supplement, Lemma 17.22
  "A Gauge Bounded by the Local Curvature" (`lem:local-gauge`, at the end of Section 17; equations
  `eq:kernel-layer-constant`, `eq:local-curvature`, `eq:local-gauge-hypothesis`, `eq:local-gauge`,
  `eq:local-representation`, `eq:local-argument`, `eq:local-correction`, `eq:local-minimiser`), with its proof in
  six steps from the SW closure §5 (2be3106d4b2f). Every cited line re-read in the corrected transcriptions: CRE
  pp. 250 (1.17), 266 (3.6)–(3.7), 267 (ll. 11–13), 268 (3.17), ll. 38–42; VAR pp. 278 (5)–(7), 279 (Theorem 1,
  the class of cubes), 281 (22)–(23), 308 (190), 309 (Proposition 9); CMP 98 p. 26 ((52), Proposition 2, (54));
  REG pp. 79 (Lemma 1, (1.24)–(1.25)), 87 (1.65); RG I pp. 261 (1.8), 272 (3.11), (3.12) and the sentence on 𝐅.
  Derived here beyond the note: the constants c_F ≥ 1 (the quadratic remainder of the current) and c_B ≥ 1 (the
  Baker–Campbell–Hausdorff and covariant-operator corrections) in place of the note's O(1); the current bound with
  (6B₃M_𝒬E)² and the condition a₁ ≤ min(1/(2c_B), 1/(18c_FB₃R₁M₁)) (the note has a₁ ≤ 2/(9O(1)B₃R₁M₁) from
  (3B₃M_𝒬E)², which bounds |A| + |∇A| by 3B₃M_𝒬E instead of 6B₃M_𝒬E). Conditions of the lemma to be entered in the
  paper's appendix when the paper cites it: M a multiple of R₁M₁, M ≥ 2LM₁ + 2R₁M₁, 22d²C_H ≤ 1, the bound on a₁.
  Compile: supplement 159 pp. (`cca6cc620992`), paper 161 pp. (`19d7c448179d`), no errors, no undefined
  references, 9 overfull boxes each (old). Lemmata 18.1–18.3 keep their numbers.**
- **12 Nov 2026, 20:15 (from `date`). Correction of the clock times in this file: every time written beside a
  digest below ("20:10" to "20:34", "20:14", "20:20", "20:24", "20:28") was typed from memory and is wrong; all of
  that reading was done between 20:08 and 20:15. Read so far, with digests and verdicts below: D2.0(3) (lines
  378–582, in full); D2.4(4), (5), (6) (lines 3085–3272, in full); D2.2(5) (lines 1461–1579, tags cut at 520
  characters); D2.4(12)(a)–(b) (in full) and (d)–(e) (lines 3634–3672, tags cut at 900 characters). Decided:
  tail clause N, extent weight N. Still undecided: the ω-clause; lw, collar, ρ_ph at the first step. Not yet
  read: D2.2(6) (lines 1580–2342, 179 000 characters: the integration and the output in the class), D2.4(10),
  (11), (12)(c), (12)(f), (13) (the size statement (S-w)), D2.3 against the paper's Section 7, the closures.
  Nothing of the rewrite is in the manuscripts.**
- 12 Nov 2026, 20:16 (estimate, superseded by the line above): Step 0 done for D2.0(3) (lines 378–582 read in full) and D2.4(5)–(6) (lines
  3145–3272 read in full); verdicts in the table below. Confirmed at the map's lines 620–695: its section (5) is a
  *count check* with items (c) "old insertions" and (d) "fluctuation parts of the old insertions" (second-order
  mean O(ρ_kg_k²), pair contractions ρ_k²g_k² per pair); the paper's `sec:contraction` is written on (c)–(d), not on
  the exact construction D2.2(5)–(6) with D2.4(4)–(6), (10)–(13). Nothing of the rewrite is in the manuscripts
  yet. Next: D2.4(4) (lines 3085–3144, the deviation factor), then D2.2(5)–(6) (lines 1461–2342, the joint
  expansion, the marked polymers M with their old members 𝔅(M), Ĥ(M), the groups, the output in the class), read
  for what the paper's proof needs; D2.4(12)(c)–(e) for the extent weight; then write Section 5's definitions.**
- 12 Nov 2026, 20:08 (from `date`): plan written. Nothing of the rewrite is written. In the manuscripts from this evening: the
  activity-0 convention for attached groups (paper `sec:reference-gas`, "The flat parts"), Supplement Section 18
  (Lemmata 18.1–18.3). Next: step 0, reading the map's lines 382–560 in full.

## Step 0: The Comparison (Filled in While Reading)

Paper lines are those of 19d7c448179d. "Read in full" means every tag of the range, at 9f0d33e406e6.

**Map lines 378–415, read in full at 20:10.**

| Map tag | Clause of D(k) | In the paper? | Used by the induction (where) |
|---|---|---|---|
| #MD2.0.3.2 | the form 𝒲_k = κ^{(k)}e^{𝓔_k}[f_k + Σ_{𝔅≠∅}Q_k(𝔅) dim(π)⁻¹tr(Y_{W₁}U_{(1)}⋯Y_{W_m}U_{(m)})] | yes, `eq:dressed-loop` (line 1125), for an ensemble (product of leading words, words w_k(𝔅)) | everywhere |
| #MD2.0.3.3 | outer variables: V_j on Ω_{j+1}ᶜ, A_j on Z_{j+1} ∩ Ω_{j+1} (CRE (2.20)–(2.21)), the exterior and "de-younged" variables of the labels | "the outer variables of the term" (line 1124), defined before the definition: check lines 1060–1100 | large fields (D2.6) |
| #MD2.0.3.4 | κ^{(k)} = Πκ_j, κ_j = e^{−δm_jP_{j−1}(C)}z_j⁴, exact perimeter and corner coefficients; κ_1 is V4's | yes, `def:step-factor` (general loops: per orientation and corner) | flat part |
| #MD2.0.3.5 | leading word; at k = 1, f_ξ(m̂) − f_1 written as att(1, ·) insertions by the telescoping of *Species* (lw slots) | leading words yes; **the lw species: to check** | first step, D2.6 |
| #MD2.0.3.6–.7 | groups of the step-k map; sizes in step-k units; **interaction clause in cluster form**: Q_k(𝔅) = exp(−Σ_{Γ hits 𝔅}φ_k(Γ)), Γ the clusters of the step-k reference gas incompatible with a member of 𝔅, φ_k(Γ) numbers given the labels depending on C only through J_Γ, Σ_{Γ hits W}\|φ_k(Γ)\| ≤ θ(W) | the paper's (i) has only \|Q_k(𝔅)\| ≤ Πe^{θ(W)}, θ(W) ≤ νσ(W)/16; **the cluster form is not in the definition** (it appears in `sec:reference-gas` as construction) | the occurrences of the next step; locality; the comparison of two runs |
| #MD2.0.3.8 | 𝓔_k = Σ_{j≤k}Σ_Xe^{(j)}_X + E_const,k, local terms plus a constant of the contour and the torus | yes, (iv) with `eq:scalar-bounds` | flat part, large fields |
| #MD2.0.3.9–.12-1 | δ*^{(k)}_n(U) := η_k^{−2}Σ_{t≥1}w_tΔ^{(k)}_n(R^{(k)}_t), w_t := (t+1)³e^{−η_wt}, η_w := (5/16)η_V, R^{(k)}_t := C_boxM(t+1), Δ the maximum of V4's plaquette deviation over the fine plaquettes of Ω_k (of Λ₁ at k = 1) | yes, `eq:deviation-quantity` (line 1118), with \|U(∂p) − 1\|; **Λ₁ at k = 1 and V4's norm \|·\|_σ: to check** | contraction |
| #MD2.0.3.16–.16-3 (lines 416–419, read in full 20:14) | **species**, fixed by the labels and the geometry at production and at each reclassification: dev; att(j, Z) (attached at the step j to a component Z by a non-good group); att(j, coll) (a collar part, bounded by the marks of all the domains and inputs of W, no component: its *bound* is split by component, (ii′-b)); lw(Z) (telescoped leading-word parts); wrap(j). The words are expanded multilinearly in the species; the split is made in the formulas, so each part is analytic | the paper names deviation, attached (region and boundary layer through the marks), wrapping, cross; **no lw species, no att(j, coll) as a species of its own, no statement that the split is in the formulas** | (iii) analyticity of each part; (ii′) |
| #MD2.0.3.17 | assignment rules: a fixed order of the components at each step; a non-good group goes to the first component its Q_W meets; each bond mark, host mark, and free input goes to the nearest component of Z_j (ties by the order); a telescoped bond to the nearest component | the paper assigns marks to cubes Δ (line 1137) and "the first component whose boundary layer it meets" in S.9(iii); **no assignment rule for groups** | (ii′) per component; the payment |
| #MD2.0.3.18 | at the step 1: Υ¹_W = (Υ¹_W − Υ⁰_W) + Υ⁰_W; Υ⁰_W dev for good groups, att(1, Z) or wrap(1) otherwise; Υ¹_W − Υ⁰_W is att(1, coll) | first step, Section 5: to compare | base |
| #MD2.0.3.19–.20-2 | the leading word in slot form at the step 1: Y_i := π(T̂_iT_i⁻¹) − 1, f_ξ(m̂) = Σ_Sf^{(S)}, exact; each slot of species lw(Z), θ := 0, Q = 1 against everything; Σ_{i∈n}‖Y_i‖ added to D(1)(ii); Y_i = 0 off Ω₁; bounds ‖Y_i‖ ≤ C″_Ig₀(r + 1) near I, ≤ C_III far; nonzero only within R′_lw ≤ ℓ of Λᶜ; lw(∅) on a term without component | the paper has the slot expansion `eq:slot-expansion` at every step; **the lw species of the first step: to compare with Section 5's first step** | first step; (ii′-c) |
| #MD2.0.3.21 | **reclassification**: at the step k + 1 an old dev insertion stays dev if its comparison box (the plaquettes its deviation bound uses) lies in Ω_{k+1}, and becomes att(k + 1, Z) if the box meets Ω_k∖Ω_{k+1}, Z the component of Λ_{k+1}ᶜ containing the first component of Ω_{k+1}ᶜ which the box meets | **not in the paper** (it has "+ (attached)" in `eq:contraction-first`) | contraction (the split of the maximum); D2.6 |
| #MD2.0.3.22–.25-1 | **species of a group made at the step k + 1**, tests applied to the final merged group in the order: inherited species (first inherited attached member: att(j, ·), lw, wrap(j), by step ascending, then att(j, Z) < att(j, coll) < lw < wrap); wrap(k + 1) (X(𝒢) does not lift); att(k + 1, coll) (meets the one-layer neighbourhood of Λ_{k+1}ᶜ, carries a boundary-type potential, or has a polymer component or an arc traversal leaving Ω_k; also the parts of the reference extraction whose clusters meet the collar); att(k + 1, Z) (comparison region meets Ω_{k+1}ᶜ); else dev | **not in the paper**; my definition of an "attached group" of 12 Nov 19:56 (attached to a large-field region of its step, or contains a part of an attached insertion) must be restated with these tests; note that in the map a group with a wrap parent and a later attached parent is *wrap* (step order), so "activity 0 for every group containing attached content" is a statement about content, not about the species | everywhere after the step 1 |
| #MD2.0.3.26 | a fluctuation part Y(U_k) − Y(U_{k+1}) keeps its parent's species; an insertion made from several parents is dev only if all are dev, else the first attached species of its parents in the total order (step, kind, component) | **not in the paper** | contraction; carry |
| #MD2.0.3.27 | units of carried groups: for att(j, ·), θ(W) and σ(W) are those of the step j; θ(W) ≤ νσ(W)/16 is evaluated at that step | the paper: "σ(W) the size of W at the step at which it was made" (lines 1132, 1143) | carry |
| #MD2.0.3.28–.29-1 (lines 450–502 read in full, 20:18) | (ii), per traversal: ν^{(k)}_n := Σ_{W∋n}e^{θ(W)}‖Y_W‖ over dev, att(k, ·), wrap(·) ≤ C_χρ_kδ*_n + Cρ̂_ke^{−c_att d_k(n)/M} + Cρ_{t,k}(Σ_Δ𝔪̂_Δe^{−c′_*dist(Δ,n)/M} + C′_χg_kΣ_bh(m_b)e^{−c′_*dist(b,n)/M}) + Σ_{j≤k}CL^{k−j}ρ̂_je^{−c_att N^{(j)}_min/M}; c′_* = min(η_V/C_F, ν_e/8, κ/4) | yes, `eq:insertion-bound`; the collar term is Cρ_{t,k}𝔪_k(𝔫) with the marks of bonds and hosts; **the term of the free inputs b with the shifts h(m_b): compare with the paper's marks** | **N** (it is the class) |
| #MD2.0.3.30–.30-3 | the first term is C_χρ̃_kδ*, ρ̃_k = ρ_k/min(α_{0,k}, α_{1,k}) for k ≥ 2 (the Cauchy step of D2.4(4)); **per-insertion form**: each dev insertion has e^{θ(W)}‖Y_W‖ ≤ b_WDev_{Q^#_W} with Σ_{W∋n}b_WDev_{Q^#_W} ≤ C_χρ̃_kδ*_n | ρ̃_k yes; **the per-insertion form with the comparison box Q^#_W: no** | **N**: an old deviation insertion whose plaquettes leave Ω_{k+1} is not bounded by the first term at k + 1 and does not contract, so it has to be told apart *as an insertion* (the reclassification #MD2.0.3.21); a bound on the sum cannot do that |
| #MD2.0.3.31 | tail clause (ii-t): with β_W := b_Wℓ_Wη_{j(W)}^{−2} in the normalisation of the step at which W was made, Σ_{W∋n, t^{(k)}(W)≥t}β_W ≤ C_χρ̃_kη_k^{−2}W_t for every t, W_t := Σ_{t′≥t}w_{t′}; the sum form follows by Abel summation | **no** | **?** decide on reading D2.4(5), (6)(γ) (the matching of the neighbourhoods and radii of an old traversal with those of the new one) |
| #MD2.0.3.32–.32-2 | reserve and extent weights (ii-w): e^{ν_rσ_k(W) + ν_e ext_k(W)} inside the per-position sums of (ii), (iii), per traversal only, for the dev species; "it is what pays for merged old members in the step-(k+1) count" | reserve yes (lines 1143, 1287); **extent weight no** | reserve **N** (merged members; S.9); extent **?** decide on reading (12)(d)–(e): the paper states `eq:size-bound` per traversal *and per cube*, and the map gets the cube positions from ext_k by the box reduction |
| #MD2.0.3.33–.35-3 | per component: Σ_{W∋n, W∈att(k,Z)}e^{θ}‖Y_W‖ ≤ Cρ̂_ke^{−c_att d^Z_k(n)/M}; only the attached parts made at the step k stay in (ii); the wraps stay in (ii) for every j with the growth L per step; d_j(n) the distance to the large-field data of the scale j; ρ̂_j = max(ρ_j, ρ_{ph,j}) | per component: in words (line 1143, 1295); wraps: the last term of `eq:insertion-bound`; ρ̂_k := Cρ_k in the paper (line 1137), **ρ_ph not in the paper** | **N** per component (the payment); ρ_ph **?** (first step) |
| #MD2.0.3.36–.39-2 | the conversions of D1(ii) into D(1)(ii) (fine traversals to step-1 traversals, g₀ to g₁, V4's ρ to ρ₁) | first step, Section 5 | **no** as text of the class; the base case states its bounds in the paper's units directly |
| #MD2.0.3.41–.42-2 | (ii′-a) att(j, Z), j < k: Σ_nΣ_{W∋n}e^{θ}‖Y_W‖ ≤ Cρ̂_jN_j(Z); at later steps each insertion counted once, at its first traversal, with w(W) := e^{ν_rσ_j(W)}e^{(3/8)ν_e ext^{coll}_n(W)}e^{θ(W)}‖Y_W‖, and the product form Π_D(1 + e^{c_W}w(D)Π_m(1 + δ_m)) ≤ exp(2A_j(Z)) | the paper: one sentence (line 1143) and `eq:attached-total`; the supplement: S.9(ii), `eq:weighted-mass`, `eq:carry-bound` | **N**; already in the supplement; the paper's definition should state (ii′) as the product form |
| #MD2.0.3.43 | (ii′-b) att(j, coll): the total split by component through the assignment of the marks, B_j(Z) := Cρ_{t,j}[Σ_{Δ→Z}𝔪̂_ΔN_j(Δ) + C′_χg_jΣ_{b→Z}h(m_b)N_j(b)]; a split of the bound, not of the insertion | the paper: `eq:attached-total` has Cρ_{t,j}𝔪_j(Z), "the sum of the marks of the data assigned to Z" | **N** in the paper's form (marks assigned to Z); the free-input term **?** |
| #MD2.0.3.44 | (ii′-c) lw(Z) at j = 1 | to compare with the paper's first step | **?** (depends on how the paper's first step treats the shift of the leading word) |
| #MD2.0.3.45–.48-2 | each species keeps the bound it has when made; the carry does not increase the left sides (no factor L per step); only the totals per component are controlled; stability under evaluation and fluctuation parts = the carry lemma | S.9(ii) | **N**, in the supplement |
| #MD2.0.3.49–.50-1 (lines 503–545 read in full, 20:24) | norms: \|Q_k(𝔅)\| ≤ Πe^{θ(W)}, θ(W) ≤ νσ(W)/16; for k ≥ 2, σ_k = #_k + n_k/M and θ_k = θ_vac + θ_ref is the fresh weight of the gas of the step k and does not carry θ_{k−1} | yes, (i) | **N** |
| #MD2.0.3.51–.51-2 | the local terms e^{(j)}_X: indexed by ∗-connected unions of boxes of the lattice integrated at the step j, anchored at the segments of that step; two bounds, per anchor (Cτ_j²e^{−c_thd^{(j)}_i}) and per cube of side a₂ **in the units of the lattice integrated at the step j** (a bound per cube of the step k is not uniform in k − j, so the old terms are paid in the anchored, per-component form) | (iv), `eq:scalar-bounds`: the first bound; **the remark on the units and the second bound: check** | **N** (flat part; the payment) |
| #MD2.0.3.52 | \|E_const,k\| ≤ Σ_{j≤k}C𝔞_j(n_je^{−c^Zι_{T,j}} + (n_j + 1)e^{−c_En_j}) for the commensurate sides | (iv): \|E_const,k\| ≤ Σ_{j≤k}ε_j(𝒞, T), `eq:step-remainder` (general loops) | **N**, in the paper's general-loops form |
| #MD2.0.3.53–.53-7 | (iii) for k = 1: the sup-only domain \|η_kA′\| < (1 − β(1 − 2^{−(k−n)}))α_{1,n}L^{−n} per fine bond; (ii) holds there with δ*^{c}_n(U_k) + a*_n(A′) in place of δ*_n, δ*^c with the weights (t+1)³e^{−(61/16)η_Vt}, a*^{(k)}_n(A′) := η_k^{−1}Σ_t(t+1)e^{−(61/16)η_Vt}max\|η_kA′(b)\|; ρ^c_{ph,k}; the tilt marks included in the marks | (iii): the polydisc yes; "`eq:insertion-bound` holds there with the deviation of 𝐔 from U_k added to δ*" — **the complex deviation quantities are not defined in the paper** | **N**: the Cauchy step of the contraction and every evaluation at a complex background use (ii) at complex data; the quantities have to be defined |
| #MD2.0.3.54–.55-1 | (iii) for k ≥ 2: CRE's domain (2.34), (2.36), (2.38), (2.39) with the gradient condition, on Ω_n∖Ω_{n+1} and Ω_k; (2.35), (2.37) on each factor's own domain; the ω-clause at complex configurations through the frame rotation c₀(𝐔); the two conditions on the real base point | (iii): "for k ≥ 2 with the gradient condition of CRE (2.39) and in the variable 𝐉 of CRE (2.36)" | the domain **N**; the ω-clause at complex 𝐔 with c₀ **?** (D2.2(4)(d′), (6)(b7)); base-point conditions **?** |
| #MD2.0.3.56–.59-3 | the variable 𝐉 for k ≥ 2: factors are functions of (𝐔, 𝐉, ω), evaluated at 𝐉 = J_k; the 𝐉-term j*^{(k)}_n(𝐉) of (ii), needed because the dev parts vanish at (1, 0, 0) and not at flat 𝐔 with 𝐉 ≠ J_k; **sub-domain form**: the dev bound at complex data is asserted on 𝒟^sub_k only, analyticity on the full domain | 𝐉 mentioned in (iii); the reference data have 𝐉 = 0; **j* and the sub-domain not in the paper** (the supplement's S.9 speaks of "the subdomain on which the attached bounds are stated") | **N** (the Cauchy step runs in 𝐉 as in A′; S.9 uses the subdomain); to be stated |
| #MD2.0.3.60 | the outer fields ω_j are slot variables; the ω-clause is analyticity in them | "outer variables" | **?** (D2.2(6)(b)) |
| #MD2.0.3.60-3–.61-13 (lines 546–582 read in full, 20:28) | the outer fluctuation fields: the ω-dependent factors extend analytically in ω jointly with 𝐔, per layer j with radii r^{(k)}_{ω,j} = r_{ω,j}(½ + 2^{−(k−j)}); at j = 0 the slot variable is CRE (1.15)'s A = Ψ_ξA′, r_{ω,0} = 1; the bound clause on the sub-polydisc 𝒟^sub_{ω,0} | the paper's (iii) does not state analyticity in the outer variables or radii for them | **?** (D2.2(6)(e); needed if an insertion on a term with large fields is evaluated at changed outer variables: the 𝐑-operation integrates them, and S.10's bounds are on "the polydiscs of the class") |
| #MD2.0.3.62 | reference clause: the factors are defined and analytic at 𝐔 = e^{iη_kA′}·1, 𝐉 near 0, ω near 0, although (1, 0) need not lie in the support of the indicators | yes, (iii), last sentence | **N** (the scalars c_𝒢) |
| #MD2.0.3.63 | (iv) constants independent of k, K, the contour size, the torus, the labelled term | yes, (v) | **N** |
| #MD2.0.3.64 | (v) scalar parts: Q_k(𝔅) and 𝓔_k are numbers given the labels; field-dependent scalar parts are scalar insertions | yes, (iv) | **N** |
| #MD2.0.3.65 | (vi) torus consistency, in summed form (I) for the insertions and (O) for the cluster weights | yes, (vi) | **N** (flat part) |
| #MD2.0.3.66–.67-1 | the identity N_k = Σχ_k(Ω_k)T_k[𝒲_k exp A_k]; the 𝐑-operation is the identity for k ≤ N | yes (line 1162; S.10(i)) | **N** |

**Result of Step 0 for D2.0(3) (20:30).** The paper's definition has the form, (i), the display of (ii), the
reference clause, the scalar parts, uniformity, torus consistency, and the identity. It lacks, or has only in
words: (1) the species with their rules (#16–#27), **N**; (2) the per-insertion form of the deviation bound with the
comparison box, and the reclassification (#21, #30-3), **N**; (3) the complex deviation quantities δ*^c, a*, j* and
the sub-domain on which the deviation bound holds at complex data (#53-3–#59-3), **N**; (4) (ii′) as a product
form, species by species (#41–#44), **N** (exists in S.9); (5) the cluster form of the interactions as a clause
(#7), **N**; (6) the extent weight (#32) and the tail clause (#31), **?**; (7) the ω-clause with its radii
(#54-4–#61), **?**; (8) lw(Z), att(j, coll) as its own species, ρ_ph, the free-input term of the collar bound,
**?** (first step). **To decide the "?": read D2.4(5)–(6) (lines 3145–3272) for the tail clause; D2.4(12)(c)–(e)
(lines 3613–3680) for the extent weight; D2.2(6)(b), (e) for the ω-clause; the paper's Section 5 (first step) for
lw, coll, ρ_ph.**

**Verdict on the tail clause, after reading D2.4(5) lines 3145–3175 in full (20:34): N.** The map's reasons
(#MD2.4.5.5–#MD2.4.5.9-2): (a) each dev insertion carries its own bound e^{θ(W)}‖Y_W(𝐔, 𝐉)‖ ≤ b_W Dev_{Q^#_W}(𝐔),
Dev over the plaquettes of the comparison box (Q^#_W)⁺ ((Q^#_W)⁺ := Q_W at the step 1; Q^#_𝒢 := X(𝒢) for a new
group); b_W, ℓ_W, Dev stay in the normalisation of the step at which W was made, only δ* is converted from step to
step; (b) with β_W := b_Wℓ_Wη_{j(W)}^{−2}, b_W Dev_{Q^#_W}(𝐔) = β_W max{δ_p(𝐔) : p in (Q^#_W)⁺}, and t^{(k)}(W) := the
least t with (Q^#_W)⁺ in the R^{(k)}_t-neighbourhood of n; (ii-t): Σ_{dev W∋n, t^{(k)}(W)≥t}β_W ≤ C_χρ̃_kη_k^{−2}W_t for
every t and n; (c) Abel summation gives Σ_{W∋n}b_W Dev_{Q^#_W} ≤ C_χρ̃_kδ*_n, **for every configuration**, because
Δ_t is nondecreasing in t: "(ii-t) is the class statement and the sum form is its consequence". Why the paper
needs it: the contraction evaluates an old insertion at the new background U_{k+1} and re-sums in the units of
the step k + 1; a bound of the sum at U_k (the paper's (ii)), or at a complex 𝐔 in terms of δ*(U_k) plus the
deviation of 𝐔 from U_k (the paper's (iii)), does not give Σ_{W∋n}e^{θ}‖Y_W(U_{k+1})‖ ≤ C_χρ̃_kδ*^{(k)}_n(U_{k+1}), which
the paper's `eq:contraction-first` uses on its left side; the per-insertion form at 𝐔 = U_{k+1} with the
distribution of the boxes in t does. Also: on the support ρ̃_kδ*_n ≤ Cρ_kε_k/ᾱ_k = O(ρ_k) under q₀ = q₁ > p₀
(#MD2.4.5.2); at complex data the dev term carries δ*^c + a* + j*, bounded on the sub-domain 𝒟^sub_k only
(#MD2.4.5.3–.4-1), its only consumer being the polydisc points of (11)(c)(β).

**(All clock times written in this table before this line are estimates and too late by about twenty minutes;
`date` gives 20:11 now. From here on times are taken from `date` only.)**

**D2.4(6), lines 3231–3272, read in full (20:11). What the paper's contraction needs from it, all N:**
- *The matching* (#MD2.4.6.1–.3-1): R^{(k)}_t := C_boxM(t+1) at every k; a plaquette within the step-k distance
  R^{(k)}_t of n lies within the step-(k+1) distance R^{(k)}_t/L ≤ R^{(k+1)}_t of n′ ⊃ n; so
  δ*^{(k)}_n(U) ≤ L^{−2}δ*^{(k+1)}_{n′}(U) for every U on the plaquettes of Ω_{k+1} (the paper has this as
  `eq:deviation-scaling`); Dev is not converted: each insertion keeps Dev, ℓ_W, b_W in the normalisation of its
  step, and the per-traversal bound carries through (ii-t) and t^{(k+1)}(W) ≤ t^{(k)}(W).
- *The split* (#MD2.4.6.4–.9-1): an old dev insertion with (Q^#_W)⁺ ⊂ Ω_{k+1} stays dev; if the box meets
  Ω_k∖Ω_{k+1} it becomes att(k+1, Z), the box meets Z, and R^{(k)}_{t^{(k)}(W)} ≥ dist(n, Z). Its plaquettes:
  by CRE (2.34) at j = k + 1 (U_{k+1} in the space of the step k + 1, which is D2.2(6)(e)'s), the fine plaquettes of
  Ω_k∖Ω_{k+1} give η_k^{−2}δ_p ≤ c_σ(1 − β/2)α_{0,k}, those of Ω_{k+1} give η_k^{−2}δ_p ≤ c_σL^{−2}α_{0,k+1} ≤
  c_σα_{0,k}; so b_W Dev_{Q^#_W} ≤ β_Wη_k²c_σα_{0,k}, and by (ii-t), with t_Z the least t with R^{(k)}_t ≥ dist(n, Z),
  Σ_{W∋n, W↦att(k+1,Z)}b_W Dev_{Q^#_W} ≤ C_χρ̃_kc_σα_{0,k}W_{t_Z} ≤ Cρ_k max(1, α_{0,k}/α_{1,k})e^{−cd^Z_{k+1}(n)/M},
  per component; needs α_{0,k}/α_{1,k} bounded, i.e. q₀ ≤ q₁ (q₀ = q₁ in the construction). **This is the
  proof of the paper's "+ (attached)" in `eq:contraction-first`, which the paper does not give.**
- *The recursion* (#MD2.4.6.10–.17): Σ_{n⊂n′}C^{(k)}_χρ̃_kδ*^{(k)}_n ≤ L^{−1}(ρ̃_k/ρ̃_{k+1})C^{(k)}_χρ̃_{k+1}δ*^{(k+1)}_{n′};
  ρ_k/ρ_{k+1} ≤ (1+β₀)⁶, ᾱ_{k+1}/ᾱ_k ≤ (1+β₀)², ρ̃_k/ρ̃_{k+1} ≤ (1+β₀)⁸ (CRE (2.6), (2.7));
  C^{(k+1)}_χ ≤ C_new + (L^{−1} + C_dL²(1+β₀)²g_K²)(1+β₀)⁸C^{(k)}_χ + C″_dρ_k(C^{(k)}_χ)², C_new := C_gC_S·pl/c₀;
  the condition (1+β₀)⁸ < L; at the step 1 → 2 the ratio is ρ̃₁/ρ̃₂ ≤ (1+β₀)⁶ᾱ₂ < 1. The paper has this recursion
  (`eq:deviation-recursion`, `eq:recursion-fixed-point`); keep.
- **Still to read for the contraction:** the rest of D2.4(5), lines 3176–3230 (the step-1 base of (ii-t), its
  carrying, and the condition (T-dev) on the deviation bound of a carried insertion at the new background, which
  "through its global induction needs D2.6's carrier item at every step"); D2.4(4), lines 3085–3144 (the
  deviation factor: the Cauchy step which gives a new group its bound b Dev); D2.0(5)(c)–(d) (the linear and the
  quadratic term of the recursion).

**D2.4(5), lines 3176–3230, read in full (20:14). Two results for the rewrite.**

1. *(T-dev), N, and it is where S.8 is used.* The per-insertion bound is proved by the Cauchy step only at the
   background of the step j at which W was made, for every V_j in the support (inputs: f(0) = 0 by Schur, the
   analyticity on the reference domain, the regularity of U_j(V_j)). Carrying W needs it at U_{k+1}:
   (T-dev) e^{θ(W)}‖Y_W(U_{k+1}, J_{k+1})‖ ≤ b_W Dev_{Q^#_W}(U_{k+1}) for every dev W made at a step j ≤ k with
   (Q^#_W)⁺ ⊂ Ω_k. Proof: with V*_i := M^iU_{k+1}, j ≤ i ≤ k, a downward induction in three regions (the cubes of
   Ω^∼_{i+1} outside the band; the band and boundary cubes, by the D2.6 closure's carrier item §8.1–§8.3; off
   Ω^∼_{i+1}, where V_i is a pending variable and the multiscale constraint gives V*_i = V_i) shows that V*_i lies
   in the support of the step i and U_i(V*_i) = U_{k+1}; then the bound at V_j = V*_j is the bound at U_{k+1}; the
   𝐉-argument by J_j = J(U_j) (RG I (1.8), (3.12)). **The supplement's S.8 (`prop:band`) is this induction** (its
   proof ends "by a downward induction"); the paper must state (T-dev) as a lemma of the contraction and cite
   S.8 for it. Then *it carries*: t^{(k+1)}(W) ≤ t^{(k)}(W) and
   Σ_{W∋n′, t^{(k+1)}(W)≥t}β_W ≤ L·C^{(k)}_χρ̃_kη_k^{−2}W_t = L^{−1}(ρ̃_k/ρ̃_{k+1})C^{(k)}_χρ̃_{k+1}η_{k+1}^{−2}W_t; *new groups*:
   with Q^#_𝒢 := X(𝒢), β_𝒢 = (C_g/(c₀ᾱ_{k+1}))e^{θ_{k+1}(𝒢)}S_𝒢ℓ_{X(𝒢)}η_{k+1}^{−2}, and (S) summed over t′ ≥ t gives the
   tail clause for them. Base at k = 1 from IT-1 §3a(6) (#MD2.4.5.10): ℓ_W := 1, b_W := β_W/L².
2. **A deprecated construction in the paper, to be removed (#MD2.4.5.20).** The map: "The fluctuation parts and
   pair contractions of D2.0(5)(d). In the exact construction they are not separate insertions. An old insertion
   touched by the step-(k+1) fluctuation is a W ∈ 𝔅(M) of a marked polymer M, evaluated at the shifted background
   inside Ĥ(M), so it lies in a step-(k+1) group 𝒢. Its fluctuation part Y(U_k) − Y(U_{k+1}) and its contractions
   with other old insertions and with the leading word are parts of Y_𝒢: the flat scalar parts are in c_𝒢 and the
   rest is in Y^d_𝒢. An untouched old insertion is taken at s = 0, that is at U_{k+1}, and is carried by (T-dev)."
   The paper's `sec:contraction` (lines 1250–1291) is written on the *count check* D2.0(5)(c)–(d) (the section of
   the map is headed "(5) The Count Check of D(k) → D(k+1)", line 620): it splits an old insertion as
   Y(U_k) = Y(U_{k+1}) + [Y(U_k) − Y(U_{k+1})], takes the mean of the fluctuation part at second order and the pair
   contractions "of the order (g_k/α_k)² per pair", makes their leading part scalar by the Casimir identity
   `eq:casimir-contraction`, and counts "O(L²) pairs per traversal". In the exact construction none of these is a
   separate object. **Remove from the paper: the splitting of an old insertion into value and fluctuation part as
   a step of the proof, the second-order means and pair contractions as separate terms, `eq:casimir-contraction`
   and the count of pairs, the quadratic term of the recursion as derived from them (check what D2.4(6)'s
   C″_dρ_k(C_χ)² rests on in the exact construction before removing the term itself).** Replace by: the groups of
   the joint expansion (D2.2(5)–(6)) with their old members 𝔅(M); the split Y_𝒢 = Y^d_𝒢 + c_𝒢 id; the size bound
   (S) for new groups (D2.4(10)–(13)); (T-dev) and the tail clause for untouched old insertions; the recursion.
   The paragraph on Schur's lemma for a flat value stays (it is D2.3(2)).

**D2.4(4), lines 3085–3144, read in full (20:20). All N: it is the mechanism of the deviation bound of a new
group, of which the paper has one sentence ("the factor ρ̃_k is the price of the Cauchy estimate").**
- *The support* X(𝒢): the cubes of π_{k+1} which meet the constituents' domains, the domains of the members of the
  merged old occurrences, the comparison boxes of its old insertions, its slots, or the bonds of its arc I(𝒢); the
  arc must be included (Y_𝒢 depends on 𝐔 along all of I(𝒢), and the arc can leave every domain); the members' domains
  too (incompatibility through occurrences). X(𝒢) is connected as a closed set (#MD2.4.4.3), and
  #(X(𝒢)) ≤ #_{k+1}(𝒢) + #(boxes) + 16n_{k+1}(𝒢), ℓ_{X(𝒢)} ≤ 2#(X(𝒢)).
- *Which groups are dev* (#MD2.4.4.5-2): no inherited attached member, the set lifts, no polymer component or
  member's domain meets the one-layer neighbourhood of Λ_{k+1}ᶜ, polymers and arc in Ω_k, no boundary-type
  potential, and 𝒬_{n′}(𝒢)^{∼5} ⊂ Ω_{k+1} for every traversal n′; such a group does not depend on ω′.
- *The local deviation*: ℓ_X := d_{k+1}(X) + 1 (RG I's linear size; the + 1 so that it does not vanish for one
  cube); t_{n′}(𝒢) the least t with X(𝒢) ⊂ B_∞(n′, R^{(k+1)}_t); 𝒬_{n′}(𝒢) the smallest union of cubes containing that
  ball; Dev_{n′}(𝒢; U) := ℓ_{X(𝒢)}E_𝒬(U), E_𝒬(U) := max{η_{k+1}^{−2}δ_p(U) : p in 𝒬^{∼5}}; the region has to be
  contractible (a ring with flat plaquettes and curvature inside); ℓ_X ≥ #(X)/162, ℓ_X ≤ 2#(X).
- *(LPG′), the local proportional gauge* (SW closure §5): under (H) there is a gauge transformation u near 𝒬^{∼2}
  with U^u_{k+1} = e^{iη_{k+1}A} there and |A|, |∇A|, … ≤ 3B₃M_𝒬E ≤ C_g Dev, C_g := 3B₃(2C_box + 6)M,
  |R(u)J_{k+1}| ≤ (4/3)C_g Dev; inputs CRE (3.17) at 𝒬, VAR Prop. 9 p. 309, CMP98 Prop. 2 p. 26, VAR (190), VAR
  Thm 1 p. 279, conditions (C-M), (C-H). **In the manuscripts: a grep for "proportional gauge" finds nothing;
  "local gauge" occurs in the supplement only at lines 2434, 2480, 2484 (Section 17; check whether that lemma is
  this statement or the complex base gauge of CMP 98). If it is not there, (LPG′) is a missing re-derivation of
  Bałaban's (CRE (3.17) used at a cube 𝒬 of the paper's choice) and belongs in the supplement; source SW closure
  §5.**
- *The Cauchy step*: f(z) := Y_𝒢(e^{izη_{k+1}A}, zR(u)J_{k+1}, 0) − c_𝒢T(I(𝒢)); f(0) = 0 by Schur; f(1) is conjugate to
  Y^d_𝒢(U_{k+1}, J_{k+1}, 0); f analytic for |z| < R_X := c₀ᾱ_{k+1}/(C_g Dev) by the reference clause; with S_𝒢 the
  supremum of ‖Y_𝒢‖ + |c_𝒢|‖T‖ over the domain, Schwarz's lemma (or the trivial bound if R_X ≤ 1) gives
  e^{θ_{k+1}(𝒢)}‖Y^d_𝒢(U_{k+1})‖ ≤ b_𝒢 Dev_{n′}(𝒢; U_{k+1}), b_𝒢 := (C_g/(c₀ᾱ_{k+1}))e^{θ_{k+1}(𝒢)}S_𝒢, for every traversal
  n′ of I(𝒢); at complex data on 𝒟^sub_{k+1} the same with Dev + a*_𝒢 + j*_𝒢.
- *From the per-insertion form to (ii)*: Dev_{n′}(𝒢) ≤ ℓ_{X(𝒢)}η_{k+1}^{−2}Δ^{(k+1)}_{n′}(R^{(k+1)}_{t(𝒢)+1}); if
  **(S)** Σ_{𝒢∋n′, t(𝒢)=t}e^{θ_{k+1}(𝒢)}S_𝒢ℓ_{X(𝒢)} ≤ C_Sρ_{k+1}w_t for every t, then
  Σ_{𝒢∋n′}e^{θ}‖Y^d_𝒢‖ ≤ (C_gC_S/c₀)e^{η_w}(ρ_{k+1}/ᾱ_{k+1})δ*^{(k+1)}_{n′}(U_{k+1}). **(S) is the size statement; the
  paper's `eq:size-bound` is a weaker relative of it (no ℓ_X, no distribution in t); (S) is proved in D2.4(10)–(13)
  as (S-w).**

**D2.2(5), lines 1461–1579, read at 20:24 with each tag cut at 520 characters (re-read the long tags
#MD2.2.5.5–.13, .16–.17, .30, .37, .44 in full before writing). The construction; all N; the paper's
`sec:small-field-map` has it in one paragraph.**
- *(a) Reduction to tensor expectations.* The integrand is a finite sum of terms c·T, c = κ^{(k)}e^{𝓔_k}Q_k(𝔅) a
  number, T a closed word in the new insertions Y_G, the untouched old insertions, and transports of U_{k+1}; only
  the Y_G depend on the integrated field, on D_i := the union of the components of G_i; T is multilinear, so
  ⟨T⟩ is the contraction of ⟨𝒳⟩, 𝒳 := ⊗_{i∈J}X_i, and ⟨𝒳⟩ = I(𝒳)/I(1) with I the last integral of CRE (3.25).
- *(b) Source.* RG II Sect. 2 run on the measure CRE (3.27) at s = t = 1, with CRE's localised action (pp.
  276–277), cover (pp. 275–276), and χ^{(k)} of (3.16); "Sect. 7 [I]" of CRE is RG II Sect. 2 (identified by
  content); CRE p. 279's "treated in exactly the same way" is used as (i) absolute convergence of the vacuum
  expansions and (ii) in the Kotecký–Preiss form Σ_{Z′≁Z}|H(Z′)|e^{a(Z′)+d(Z′)} ≤ a(Z), a(Z) = c|Z|,
  d(Z) = 9 log 2·|Z| (D2.4(2), c = (9/64)e^{−4κ} for κ ≥ κ_vac).
- *(c) The expansion with marked supports.* RG II (2.1)–(2.11) with 𝒳 in the integrand: Y₀ := ∪Y ∪ D^#_J (the
  smallest union of cubes of π_k containing in its interior every bond on which a Y_{G_i} depends); (2.3) bond by
  bond with CRE's thresholds; (2.4)–(2.6) with 𝒳 inside; (2.8) unchanged; (2.9)–(2.10) factorisation over *linked
  components* (two components of Z are linked if some D_i meets both); a linked component without a slot has the
  vacuum activity H(Z), one with the slot set J(M) ≠ ∅ a *marked activity* H̃(M) with values in ⊗_{i∈J(M)}End(V_π);
  (2.11): I(𝒳) = Σ_𝔐(⊗_{M∈𝔐}H̃(M))Ξ(𝔐), 𝔐 the families of pairwise compatible marked linked polymers whose slot
  sets partition J, Ξ(𝔐) the gas of the vacuum polymers compatible with 𝔐; I(1) = Ξ.
- *(d) The ratio.* Ξ(𝔐)/Ξ = exp(−Σ_{𝒞≁𝔐}φ^T(𝒞)) (RG II (2.12)); per polymer: Ψ(M) := Σ_{𝒞≁M}φ^T(𝒞),
  Ψ_≥(T) := Σ_{𝒞≁M ∀M∈T}φ^T(𝒞), Q_{k+1}(𝔐) := exp(Σ_{T⊆𝔐, |T|≥2}(−1)^{|T|}Ψ_≥(T)); then
  Ξ(𝔐)/Ξ = Π_Me^{−Ψ(M)}·Q_{k+1}(𝔐) (a cluster incompatible with s members is counted s − 1 times in the exponent
  of Q); Ĥ(M) := e^{−Ψ(M)}H̃(M).
- *(e) Result.* ⟨𝒳⟩ = Σ_𝔐Q_{k+1}(𝔐)⊗_MĤ(M); each M is a new group, possibly with several intervals; hard core ζ,
  soft interaction Q_{k+1}; |Q_{k+1}(𝔐)| ≤ Π_M exp(Σ_{𝒞≁M}|φ^T(𝒞)|), exponent ≤ c|M|; the marked polymers have no
  hard core with the untouched old insertions, which D2.2(6)(d)'s second rule merges into the groups whose
  constituents their domains are incompatible with (an exact regrouping); polymers meeting Λ_{k+1}ᶜ: D2.6 closure
  §2.1–2.4. This vacuum part of the interaction is θ_vac; the reference gas of the groups (D2.3(3)) gives θ_ref.

**Verdict on the extent weight, after reading D2.4(12)(d)–(e), lines 3634–3672 (20:28; tags cut at 900
characters, re-read in full before writing): N.** It is used in three places of the count. (1) *Cube positions
follow from traversal positions* (#MD2.4.12.30, the box reduction): a cube Δ of X(W) ∪ Q^#_W lies within ext_k(W)
of every traversal of W, so Σ_{W: Δ∈X(W)∪Q^#_W}w̃(W)e^{b(W)} ≤ Σ_{R≥0}8M(2R + 3)e^{−(ν_e/4)R}ε^{old}_t ≤
C(M/ν_e²)ε^{old}_t, spending a quarter of the extent weight. The class is stated per traversal only; the paper's
`eq:size-bound` and Lemma "Root Bound and Tail" assume the bound per cube, which is exactly what this derives.
(2) The polynomial ℓ_{X(𝒢)} of the Cauchy step is paid per piece, the box of an old W by (2x/L + 3)⁴ ≤
C_ℓe^{(ν_e/8)x}, x = ext_k(W) (#MD2.4.12.26). (3) The extent of a new group contains ext_k(W)/L + 1 of its touched
insertions (#MD2.4.12.22). *The extent budget of an old W* (#MD2.4.12.27-5): share ν_e/8 + ν_e/L, charge ν_e/4, box
reduction ν_e/4, the M-vertex ν_e/L; in all ≤ (5/8 + 2/L)ν_e ≤ ν_e. *The reserve budget of an old W*
(#MD2.4.12.27-4): of ν_rσ_k(W): share ν_r/4, transports ν_r/16, charge ν_r/4, window counts ν_r/8, interaction
weight ν_r/16, a′-transports ν_r/16, share parts passed by an M-vertex ν_r/16; in all 7/8, ν_r/8 to spare.
**The objects of the count (all N; this is "the counting of the step" which the paper asserts):** vertices of a
group: an M-vertex (a marked polymer M with its touched old insertions 𝔅(M) and its vacuum links 𝒱(M)), W-vertices
(old insertions merged), Γ-vertices (old occurrences of the reference gas of the step k hitting a W of 𝒢), vacuum
links 𝒞; sizes #(v), ext_v, diam_v, the window win(v); the pair relations and the covering lemma ((12)(c), lines
3623–3633, not yet read); the share sh(v) := ν_f(#(v) + |win(v)|/M) + ν_e(ext_v + |win(v)|/M + 2) +
c′_πα_{1,k+1}|win(v)| + ℓ(v), ν_f := 17ν/16, with (ν/16 + ν_r)σ_{k+1}(𝒢) + ν_e ext_{k+1}(𝒢) ≤ Σ_v sh(v); the bounds
sh(M), sh(W) ≤ (ν_r/4)σ_k(W) + (ν_e/8 + ν_e/L)ext_k(W) + c_sh + c′_πα_{1,k+1}|win(W)| for L ≥ L₀ := 5000 (through
#_{k+1}(X_W) ≤ 16 + 10240/L + 1024σ_k(W)/L), sh(Γ), sh(𝒞) ≤ #(𝒞)/4; the charges b(W), b(Γ), b(𝒞), b(M); the rooted
sums ε_p := Σ_{v at p}w̃(v)e^{b(v)}, w̃(v) := C_v|activity|_sup e^{sh(v)}, at traversal, cube, and window positions
(C_win ≤ 656M/min(1, ν_rL)); then (f) and (13) (lines 3673–3815, not yet read): the new rooted sum, the
Kotecký–Preiss condition, the weighted interaction clause, the rate comparison, (S-w).

**D2.4(12): vertices, sizes, pair relations, covering lemma, lines 3613–3633, read at 20:17 (tags cut at 900
characters). N.** A *Γ-vertex*: an old occurrence of the reference gas of the step k hitting a W of 𝒢, activity
|φ_k(Γ)| with the 1/m!, support the members' domains, intervals the members' arcs, window the union of the
members' windows. *Vacuum factors*: a cluster 𝒞 is chosen by at most 2^s factors, weight 2|φ^T(𝒞)|_sup with
2^s ≤ e^{d(𝒞)}; e^{6c#(M)} per M absorbed; no deviation factor is needed in S_𝒢 (the Cauchy step supplies it for
Y^d_𝒢 as a whole). *Sizes*: #(v) the cube counts of the pieces; ext_v; diam_v the largest ℓ^∞-distance from a
point of the support to int(v); the *window* win(v) := int(v) extended by 20(diam_v + 1) bonds at each end;
σ_{k+1}(𝒢) ≤ Σ_v(#(v) + |win(v)|/M), ext_{k+1}(𝒢) ≤ Σ_v(ext_v + |win(v)|/M + 2),
#(X(𝒢)) ≤ Σ_v(#(X_v) + 8|win(v)|/M + 80). *Arc cubes*: an arc of n bonds meets at most 8n/M + 80 cubes of π_{k+1}
(**the map's count is for a square: five straight pieces; shorter arc ≤ twice the ℓ^∞-distance. For a general
loop the paper has Λ(C) (Lemma "Square Properties"); take the constants from the general-loops note §§4–6.**)
*Pair relations*: v ~ v′ if (ii) supports incompatible, (iii) one is a Γ-vertex hitting a W of the other, (iv′) an
interval of one meets the window of the other; *covering lemma*: (ii), (iii) ⇒ (iv′) (the shorter arc between the
intervals has length ≤ 2(diam_v + diam_{v′} + 1) ≤ 20(max + 1)); every group is (ii)–(iv′)-connected,
I(𝒢) ⊂ ∪_v win(v), length(I(𝒢)) ≤ Σ_v|win(v)|.

**D2.4(12)(e) end and (f) beginning, lines 3673–3712, read (tags cut at 1000 characters). N: this is the count.**
- *The vacuum sum* (#33): Σ_{𝒞≁Y}w̃(𝒞)e^{b(𝒞)} ≤ 2C′_pc c#(Y) under κ ≥ κ′_vac := 162(1 + 17 log 2); C′_pc c ≤
  min(1/100, 1/(2C′_v)) under κ ≥ κ_pc.
- *Kotecký–Preiss for the linking relation* (#34–#37): Σ_{v′~v}w̃(v′)e^{b(v′)} ≤ b(v)/2 for every vertex, by
  counting the positions of a linked v′: for an M-vertex, the ≤ 81L⁴#(v) cubes of π_k near its support, its
  window positions, the Γ hitting its touched W; each term ≤ (small)·(#(M∖D′) + #(G_M) + Σσ_k(W) + Σ#(𝒞) +
  |𝔅(M)| + 1), small := O(L⁴(ε^old_c + ε^{ref,k}_c) + LMC_win(ε^old_t + ε^{ref,k}_t) + ε^new_c + MC_winε^new_t + c);
  charged to b(W)/2, b(𝒞)/2, and (κ_s/8)#(G_M) + (r_κ/1296)#(M∖D′) + ½; for a W-vertex ≤ (ν_r/32)σ_k(W) +
  (small)(σ_k(W) + 1) ≤ b(W)/2.
- *The weighted interaction clause* (#38): FV Theorem 5.4 (5.10)–(5.11) for the reference gas of the step k with
  |w(W′)| := |c_{W′}|e^{s(W′)}, s(W′) := sh(W′) + b(W′) + (ν_r/8 + ν_r/16)σ_k(W′) + log C′_pc, a(W′) := (positions
  of W′)·ε̂ ≤ 81Mσ_k(W′)ε̂, ε̂ := sup_pΣ_{W′ at p}|c_{W′}|e^{s(W′)+(ν_r/16)σ_k(W′)}; (5.10) holds once
  ε̂ ≤ ν_r/(1296M); (5.11): Σ_{Γ hits W}|φ_k(Γ)|e^{Σ_{W′∈Γ}s(W′)} ≤ a(W) ≤ (ν_r/32)σ_k(W) once ε̂ ≤ ν_r/(2592M).
  **This is the origin of the paper's `eq:kp-condition` (2592MC_{S′}𝔞 ≤ ν) and of θ(W) ≤ νσ(W)/16; the paper's
  version has the weight e^{2a°} in place of e^{s + (ν_r/16)σ}, i.e. without the shares and charges.**
- *The tree bound* (#39): T(v) := the sum over the rooted trees at v of Π_{v′≠v}w̃(v′) ≤ e^{b(v)/2}; *marked sums*:
  with one marked vertex of weight m, sup_pΣ m e^{b} ≤ ε_m, F(v) ≤ λb(v)e^{b(v)/2}, λ := 2ε_m/ε_* (this is the
  "bound for a sum rooted at an old vertex" which S.9 cites); *the root*: a position p at the step k + 1 lies in
  win(v₀) or X_{v₀} of a vertex of 𝒢, or is a gap cube of I(𝒢), met by ≤ 4M + 4 traversals; the amendments (T2)
  (e^{−ν_e} per cube of the components reserved for the bridges of the carry lemma) and (T0) (the old attached
  members of a term are fixed data; the rooted sums are re-run over the new constituents and the dev old
  members; ε^new_{re-run} ≤ C_Mb_n·pl + K′b_n/ᾱ_n) of the D2.6 closure §5.2.
- *Three classes* (#40–#42): groups with an M-vertex rooted at an M-vertex ≤ C_winε^new; rooted at an old vertex
  ≤ C_winε^new by the marked sum (once ε̄^old + ε̄^{ref,k} ≤ ε_*/2); M-free groups other than the trivial group
  {W} ≤ C_win(ε̄^old + ε̄^{ref,k})²/ε_*, **quadratic in the old sums: this is the exact origin of the quadratic
  term of the recursion, so that term stays when the count-check derivation is removed.**
- *The result* (#43–#45): for every position p at the step k + 1,
  Σ_{𝒢 at p}e^{(ν/16 + ν_r)σ_{k+1}(𝒢) + ν_e ext_{k+1}(𝒢)}S_𝒢ℓ_{X(𝒢)} ≤ Σ_{𝒢 at p}Π_{v∈𝒢}w̃(v) ≤ 2C_winε^new +
  C_win(ε̄^old + ε̄^{ref,k})²/ε_*, and the same with |c_𝒢| ≤ S_𝒢 (the c-version); factor 4M + 4 at a gap cube.
- *ε^new, the marked-polymer sum* (#46): the data of an M-vertex (the animal M ∈ 𝐃_{k+1}, D′ ⊂ M, the components
  grouped into the G_i, 𝔅(M), I(M), 𝒱(M)) and their entropy: 64^{#(M)−1} animals, 2^{#(M)}, 2^{81c_DL⁴#(G_M)},
  4^{#(G_M)}, the touched insertions in two stages (e^{(#(G_M)+#(M))/8}), the vacuum links e^{18c#(M)}; against
  |H̃(M)| ≤ c_M(amplitude)·pl·e^{−(κ_s/2)#(G_M)}e^{−(r_κ/324)#(M∖D′)}e^{20c_Dr_κ#(G_M)} of (11)(f): a cube of M∖D′
  costs ≤ 8 against r_κ/648, a cube of the components a constant against κ_s/4.

**D2.4(12)(f) end and (13)(a), lines 3713–3760, read (tags cut at 850 characters). N.**
- ε^new ≤ ε^{new,α} + ε^{new,β}, ε^{new,α} ≤ C_Mρ_{k+1}·pl, ε^{new,β} ≤ K_β(b_k/ᾱ_k)ε^old (#47), under r_κ/648 ≥ 8 and
  κ_s ≥ κ^{(12)}_s := 80c_Dr_κ + 324c_D(L⁴log 2 + 9) + 16; kind (α) has amplitude O(b_k²) or O(δ_k²) ≤ Cρ_{k+1}, kind
  (β) (at least one touched W) the amplitude (C_Tb_k/ᾱ_k)^{n(G)}Π_{W∈𝔅(G)}[e^{θ_k(W)}‖Y_W‖]; c_{{W}} = 0 for a carried
  dev insertion because its dev part vanishes at the reference point.
- *Uniformity in k and (S-w)* (#49–#53): ε^{(k)}, ε^{ref,k} ≤ C^{(k)}ρ_k·pl_k; the carried insertions contribute
  L^{−1}(ρ̃_k/ρ̃_{k+1})ε^{(k)} per traversal at real points; C^{(k+1)} ≤ 2C_winC_M + θ_kC^{(k)},
  θ_k := L^{−1}(1+β₀)^{15} + (1+β₀)⁷[2C_winK_βC_TC₁^{RG2}A₁(log g_k^{−2})^{p₀−q}/min C_i +
  4L⁸C(M/ν_e²)²C_winC^{(k)}ρ_k·pl_k/ε_*] ≤ ½ under 8(1+β₀)^{15} ≤ L, q₀ = q₁ > p₀, g_K small; so
  C^{(k)} ≤ max(C^{(1)}, 4C_winC_M). **The complex-data part of the size sums does not close by this recursion**
  (a carried insertion made at the step j contributes ≈ ρ̃_jα_{1,k+1} per traversal at every later step); it is
  bounded from the production constants by the complex covariance note (#MOMGD.5: complexified covariance, the
  gain δ_W := 4ML^{−m}σ_j(W), the averaging bound (K3), constants Ĉ, c_nc, m₀, μ, δ̄₀, the weight
  (15/16 − 1/8192)ν_r), giving C′_S := max(2(1+Ĉ)C^{(1)}, 8(1+Ĉ)C_winC_M). The c-version gives the
  Kotecký–Preiss condition of the reference gas of the step k + 1 with a°(𝒢) = (ν/32)σ_{k+1}(𝒢) at a°/2, hence
  θ_ref ≤ a° (FV Lemma 5.6, (5.17)), θ_{k+1} = θ_vac + θ_ref ≤ νσ_{k+1}/16, and
  **(S-w)** Σ_{𝒢 at p}e^{θ_{k+1}(𝒢) + ν_rσ_{k+1}(𝒢) + ν_e ext_{k+1}(𝒢)}S_𝒢ℓ_{X(𝒢)} ≤ C′_Sρ_{k+1}·pl, with the c-version,
  uniformly in k ≤ K; the root sum Σ_{𝒢∋b}|c_𝒢|e^{2a°(𝒢)} ≤ C′_Sρ_{k+1}·pl (×16 at a bond off C).
  **(S-w) is the statement which replaces the paper's `eq:size-bound`** (it has in addition ℓ_{X(𝒢)}, the extent
  weight, and the supremum S_𝒢 of ‖Y_𝒢‖ + |c_𝒢|‖T‖ over the domain).
- *(13)(a), the rate comparison*: if t(𝒢) = t ≥ 2 then ext_{k+1}(𝒢) ≥ C_boxt − 2, so
  Σ_{𝒢∋n′, t(𝒢)=t}e^{θ}S_𝒢ℓ ≤ e^{−ν_e(C_boxt−2)}Σe^{θ+ν_e ext}S_𝒢ℓ ≤ C_Sρ_{k+1}·pl·w_t, since ν_eC_box = ν/2 = η_V/2 >
  η_w = (5/16)η_V; C_S := e^{2ν_e}C′_S. **A fourth use of the extent weight: the distribution in t of the new
  groups, i.e. the tail clause for them, comes from it alone.** Bałaban's rate r_κ and the slots' κ_s are spent
  entirely on the charges and the entropy. Note η_V = ν here (the rate of V4 named η there).
- The paper's constants to align: C_{S′} (paper) ↔ C′_S; C_new := C_gC_S·pl/c₀; pl := 1 + (log g^{−2})^{(q₁−q₀)₊} = 2
  at q₁ = q₀ (the paper's "factor 2", line 1375); 𝔞_k := max(τ²_{k−1}, ρ_k·pl).

**D2.4(13)(b)–(d), lines 3761–3815, read (tags cut at 560 characters; (c) is long and must be re-read in full
before Section 7's "Torus Consistency" is rewritten). N.**
- *(b) The root sum*: the c-version of (S-w) gives FV (5.10) for |c_𝒢|e^{a°(𝒢)} with a = a°, so
  Σ_{Γ∋b}|Φ°(Γ)|e^{a°(Γ)} ≤ Σ_{𝒢∋b}|c_𝒢|e^{2a°(𝒢)} ≤ C′_Sρ_{k+1}·pl; a°(𝒢) ≥ a_min n_ins(𝒢), a_min = ν/(32LM); the
  amplitude is ρ_{k+1}·pl. (This is the paper's Lemma "Root Bound and Tail", which is then a consequence of (S-w).)
- *(c) The difference count for torus consistency*: a T–T′ difference of c_𝒢 or Y_𝒢 has three sources: old
  vertices and touched insertions (the inductive clause ε^diff_k ≤ C^{(k)}_rel e^{−c_kι_{T,k}}ρ_k·pl_k, a sup over the
  traversals with the full (ii-w) weight and ℓ_X; cube sums re-derived at each step by the box reduction); the
  vacuum factors of an M-vertex (clusters which do not embed have #(𝒞) ≥ ι/(8M); tail(M) ≤ 36c#(M)e^{−ι/(32M)};
  δ_vac ≤ C_vacε^new e^{−ι/(32M)}); the Ursell coefficients (equal). Group level by telescoping and the
  marked-vertex lemma (two marks: F₂ ≤ 6λλ′b e^{3b/4}); δ_{k+1} ≤ K_Δ[(ε^new + ε̄^old + ε̄^{ref,k})/ε_*]ε̄^diff_k +
  2C_winδ_vac; the carried part is ≤ L·ε^diff_k per traversal (the sup form is not dev-normalised);
  ε^diff_{k+1} ≤ [L + small]ε^diff_k + 4C_winC_vacC″C′_Sρ_{k+1}pl_{k+1}e^{−ι/(32M)}; with c := 1/(32M),
  ι_{T,k} = Lι_{T,k+1}, the contraction is e^{−c(L−1)ι_{T,k+1}}, and (TC) ι_{T,K} ≥ 96L⁴M(L + 1) gives
  C^{(k)}_rel ≤ max(C^{(1)}_rel, 2C⁎), C^{(1)}_rel = 0. Cluster level: the marked-vertex lemma with vertices := groups,
  d(𝒢) := ν_rσ_{k+1}(𝒢) + ν_e ext_{k+1}(𝒢) + 2c_sh + 1 + log C′_pc; Σ_{Γ at p, embeds}|ΔΦ°(Γ)|e^{d(Γ)} ≤ 2δ^d_{k+1};
  C^{(k+1)}_Z = 2C′_S + 2C^{(k+1)}_rel, rate c^Z = ν/(256A_dM).
- *(d) What (S) is, and its conditions*: κ ≥ κ′_D, L ≥ L₀ = 5000, 8(1+β₀)^{15} ≤ L, C_box ≥ 4A_E (and ≥ 6),
  κ_s ≥ κ^{(12)}_s, M ≥ 100, c′_πα_{1,j}·4096M ≤ ν for every j ≥ 1, c′_πα_{1,k+1}M ≤ ν/64, δ₂R₁M₁ > 3 log L + 1,
  β_H = ½, r_κ/648 ≥ 8, the conditions of (10)–(11), ν ≤ 1/1000, q₀ = q₁ > p₀, (TC), η_w = (5/16)η_V, g_K small.
  Inputs from outside: (T-dev)'s inputs; the hard-core reference gas (D2.3(3)); the collar species (D2.6);
  (LPG′) and the complex-data dev clauses (SW closure §5–§6); the complex covariance note; RMJ; (Z)'s base.
  **Each of these conditions has to be found in the paper's appendix of conditions or added to it.**

**D2.4(10)–(11), lines 3340–3560: only the headed items read (20:22). N, to be read in full when the count is
written.** (10) the bound of a marked activity: (a) the object, a marked polymer M, a linked union of connected
Z ∈ 𝐃_{k+1} with slot set J(M) ≠ ∅; (b) the result with λ_L := L/2 (L ≥ 486), r_κ := (1 − 5δ)λ_Lκ = (L + 2)κ/4,
A := O(1)(LM)⁴α₅ + e^{−½(κ₁−1)} + …; (c) the per-term bound, RG II (2.14)–(2.26) with 𝒳_M; (d) the geometry, RG II
(2.27), (2.32), (2.36); (e) the resummation (decay part, entropy part, fixed Z′₀ ⊂ Z, the sum over Z′₀, the
absorption e^{A#(Z)} ≤ e^{81A#(D′)}e^{δλ_Lκd(Z;D′)} once 324A ≤ δλ_Lκ, the smallness ϑ); (f) scope: the slot factor
enters through ‖𝒳_M‖_sup only. (11) the slot sizes: (a) 𝒳_M = ⊗_{i∈J(M)}Y_{G_i}; (b) the threshold on the support
(CRE (3.16)); (c) the per-slot bounds at complex data, kinds (α) and (β) (a touched old insertion); (d) the count
check for the exponential costs; (e) the size in powers of g: the single-slot, single-component pure loop
polymers have ‖𝒳_M‖_sup = O(b_k) = O(g_k(log g_k^{−2})^{p₀}), a factor 1/g_k short of ρ_{k+1}; (f) **parity**: the
even part of such a slot is O(δ_k²), the odd part vanishes in the plain term and in the terms with 𝐃 = ∅ by the
symmetry B → −B; consequence |H̃(M)| ≤ c_Mρ_{k+1}·pl·(decay); (g) inputs from outside. **The paper's sentence "each
slot ... produces a fresh insertion of deviation size" (line 1244) rests on this parity argument and does not
give it.**

**Writing order decided at 20:23.** The manuscripts are changed block by block, and a block is moved in only when
it is closed (no reference to a statement not yet in the manuscripts), so that the paper never contains a
statement without its proof; until then the text is drafted in `REWRITE_DRAFT.tex`. Block A = the new Section 5
objects and the class + the rewritten Section 6 (construction, deviation bound of a new group, the count with
(S-w), (T-dev), carrying, split, recursion). Its inputs still to read: D2.2(6) (the integration), D2.4(10)–(11),
D2.4(7)–(8), SW closure §5–§6 for (LPG′) (supplement), the complex covariance note for the complex-data part
(the paper's Section on the averaging bound (K3) may already hold part of it: check), D2.3(2)–(3) against the
paper's Section 7, the general-loops note §§4–6 for the constants with Λ(C). Drafting starts with what is fully
read: the objects (sizes, extent, comparison box, deviation quantities), the species and their rules, the class.

**The general-loops note `WILSON_IT1_GENERAL_LOOPS_2026_11_10.md` (d401d13826f7, 346 lines; sections: 1 setting
13, 2 geometric lemmata 35, 3 the first step 87, 4 the step map 146, 5 the single-loop closures 183, 6 the
multi-loop notes 227, 7 conditions 268). §4, lines 146–182, read (tags cut at 900 characters). It gives the
count for a general loop as changes of constants in the map's count; the paper's rewrite uses these directly:**
- P_j(C) = P_{K′}(C)L^{K′−j} for 4ℓ_CL^{K−j}; the step factor of #GL2.9-3; the contour constant c_C(C) := 2Λ̄(C) (a
  half-open cube of side MR_n holds the initial sites of at most 2Λ̄(C)MR_n bonds of C).
- Arcs: the chord–arc constant 2 becomes Λ(C); a smallest arc has length ≤ 4Λ̄(C)diam + 2, its points within
  2Λ̄(C)diam of the set; length(I(G)) ≤ 4Λ̄(C)M#(G); every arc constant of the map is multiplied by at most Λ̄(C);
  the conditions 20Λ̄(C)c′_πM‖a′‖_∞ ≤ 1, c′_πα_{1,k+1}·20Λ̄(C)M/L ≤ ν_r/16.
- (12)(c): the window extends int(v) by 10Λ̄(C)(diam_v + 1) at each end; arc cubes (8 + 16/L)n/M + 32; covering
  lemma with Λ(C): the shorter arc between the intervals ≤ Λ(C)(diam_v + diam_{v′} + 1) ≤ 2Λ̄(C)(max + 1).
- (12)(d): |win_M| := n_{k+1}(M) + 20Λ̄(C)(M#(M) + 1); ext_M ≤ #(M) + (8 + 16/L)n_{k+1}(M)/M + 33 +
  max_W(ext_k(W)/L + 1); n_{k+1}(M) ≤ Λ̄(C)(5M#(M) + 9(M/L)Σσ_k(W)); X_W with its arc cubes ≤ (8 + 16/L)σ_k(W) + 32
  cubes of π_k; |win(W)| ≤ (20Λ̄(C) + 1)(M/L)σ_k(W) + 20Λ̄(C); every count in the shares and in ℓ_X at most
  Λ̄(C)(1 + 2/L) times the map's; **conditions L ≥ 5000Λ̄(C) and ν ≤ 1/(1000Λ̄(C)), with ν = η(C)** (#GL4.8:
  A_h(C), A_s(C), η(C) of #GL3.11-2–.11-4; for a family η(𝒞) of #GL6.3-0); C_win(C) ≤ 41Λ̄(C)/c_w.
- (12)(e)–(f), (13): the ν-parts of the per-cube costs multiplied by at most Λ̄(C)(1 + 2/L); the transport
  condition c′_πα_{1,k+1}·4096Λ̄(C)M ≤ ν; (S) holds with L ≥ L₀(𝒞) (#GL7.1-1) and (TC) with the stopping index of
  #GL1.3; the entropy counts per cube are unchanged.
- Still to read there: §2 (the geometric lemmata, against the paper's Section 2), §3 (the first step), §5 (the
  closures: D2.6, D2.7 for a general loop), §6 (several loops), §7 (conditions).

**D2.2(4)(a)–(c), lines 1143–1194, read (tags cut at 640 characters). Verdict on the ω-clause: N on the terms
with large fields.**
- *Cov(k)* (#MD2.2.4.1–.7): gauge transformations u act by 𝐔^u(b) = u(b_−)𝐔(b)u(b_+)^{−1} and on the outer
  fluctuation fields ω by R(u) (adjoint at b_−; CRE (1.17), (2.41)(iii)); every insertion is the value at
  (𝐔, 𝐉) = (U_k, J_k) of a function Y_W(𝐔, 𝐉, ω) restricted to a domain X_W containing the interval of W, analytic
  on the domain of (iii) jointly in 𝐔 and ω, with Y_W(𝐔^u, R(u)𝐉, R(u)ω) = π(u(x_W))Y_W(𝐔, 𝐉, ω)π(u(x′_W))^{−1}, x_W
  and x′_W the ends of the interval; closed words are invariant. The paper has covariance in (iii) in half a
  sentence, without the outer fields. N.
- *The substitution identity* (#MD2.2.4.13–.22): with w the gauge transformation of CRE (3.6),
  U_k(e^{iB′}V^{(k)})^w = e^{iη𝐇_k(B′)}U_{k+1}, Cov(k) gives F = 𝒲_k(e^{iη𝐇_k(B′)}U_{k+1}, R(w)ω)∘ψ_{k+1}. For the
  factors without ω-dependence w drops out (on the terms without exterior variables this is every factor); for
  the factors which consult outer fluctuation fields w enters through R(w)ω, which must stay in the domain of
  analyticity in ω: |R(w)ω − ω| ≤ (e^{2c_G|log w|} − 1)|ω| per bond, radii r^{(k)}_{ω,j} per layer. **So the
  ω-clause (#MD2.0.3.54-4–.61) is used by the step itself whenever an insertion depends on an outer fluctuation
  field, which happens on the terms with large fields (the groups which are not good, the lw slots). N there; on
  the trivial term it is void.** ψ_{k+1} changes only the A_k on S_{k+1} ⊂ Λ_{k+1}ᶜ (CRE p. 269), outer variables
  of the step k + 1.

**D2.2(4)(e), lines 1352–1389, read (tags cut at 760 characters). N: the construction of the new insertions
before integration.** With the localisation parameters s of the step (D2.1(4)) and 𝐇(s, B′), w(s): for an old
family 𝔅 its closed word Φ_𝔅(s) at (e^{iη𝐇(s,B′)}U_{k+1}, 𝐉′, R(w(s))ω); Φ_𝔅(1) is the word of the substitution
identity, Φ_𝔅(0) the word at (U_{k+1}, ω); at s(σᶜ) = 0, 𝐇(s, B′) vanishes near Y(σ)ᶜ, so a factor takes its value
at s = 0 unless its domain X_W, its interval, or (for an ω-dependent factor) a block meeting X_W meets a component
of Y(σ); the fundamental theorem of calculus in each s(Δ) gives Φ_𝔅(1) = Σ_σΠ_{Δ∈σ}∫₀¹ds(Δ)∂_{s(Δ)}Φ_𝔅(s)|_{s(σᶜ)=0};
a component is *active* for 𝔅 if it contains a fine bond of C, meets X_W for a W ∈ 𝔅, or meets a block meeting
X_W for an ω-dependent W; for an active Y, S′(Y) := the fine bonds of C in Y with the intervals of the W for which
Y meets X_W, and I(Y) := the smallest arc containing S′(Y), enlarged at each end to the end of any old interval
that it cuts (old intervals are pairwise disjoint, so at most one at each end); **the new groups G are the
connected components of the overlap graph of the arcs I(Y), I(G) := ∪_{Y∈G}I(Y); the new insertion Y_G is the
derivative term with the ordered product along I(G) of the old insertions with intervals in I(G) and the
transports of e^{iη𝐇(s,B′)}U_{k+1} between them; an old insertion whose interval lies in no new arc stays,
evaluated at (U_{k+1}, ω), with the same group, domain, and interval.** Result:
F = κ^{(k)}e^{𝓔_k}[f_{k+1} + Σ_{𝔊≠∅}tr(Y_{G₁}U_{(1)}⋯) + Σ_{𝔅≠∅}Q_k(𝔅)Σ_{𝔊 compatible with 𝔅}tr(word of (𝔅, 𝔊))]∘ψ_{k+1},
exactly, on every labelled term; σ ↦ 𝔊 is a bijection onto the families compatible with 𝔅. Locality: Y_G depends
on B′ and (𝐔, 𝐉) on the components of G, on ω on the domains of its old insertions, on U_{k+1} along I(G).
Covariance of the new pieces: (6)(b). *(f)*: the bounds need every old factor analytic at
e^{iη𝐇(s,tB′)}e^{iηa′}U_{k+1} for |s(Δ)| ≤ e^{κ_s}, |t_Y| ≤ T_Y, a′ in the radius of (iii) at k + 1 (the chain
condition with CRE p. 277's margin; (2.35), (2.37) at the evaluation points by RMJ).
**The stages of the construction, for the paper's Section 6:** (1) the s-expansion of the old words into
components and groups G with insertions Y_G (D2.1(4), D2.2(4)(e)); (2) the fluctuation integral with marked
supports: marked polymers M, activities H̃(M), Ĥ(M) := e^{−Ψ(M)}H̃(M), vacuum interaction (D2.2(5)); (3) merging
along the loop into the groups 𝒢 of the step k + 1, with their vertices (D2.2(6)(d), D2.4(12)); (4) the species
(D2.0(3), D2.6 2.1), the split Y_𝒢 = Y^d_𝒢 + c_𝒢T, the reference gas, the interactions (D2.3(2)–(3)); (5) the
bounds: the marked activities (D2.4(10)–(11)), the count (12)–(13) giving (S-w), the Cauchy step (4), (T-dev) and
the carrying (5), the split and the recursion (6).

**D2.2(6)(c)–(d), lines 1842–1930, read (tags cut at 600 characters; re-read #102-1–#102-6, #119-3–#119-9,
#120–#120-7, #123–#123-5 in full before writing). N: the scalar parts and the definition of the groups of the
step k + 1.**
- *(c) Scalar parts.* The only field-dependent scalar after the integration is the vacuum interaction
  Q_{k+1}(𝔐) = exp(Σ_{T⊆𝔐,|T|≥2}(−1)^{|T|}Ψ_≥(T; 𝐔, 𝐉, ω′)). Extraction at the flat reference (1, 0, 0) with the labels
  of the term: Ψ°_≥(T), δΨ_≥(T) := Ψ_≥ − Ψ°_≥, likewise Ψ°(M), δΨ(M); the vacuum expansion converges at (1, 0, 0)
  (on a term with large fields through CRE p. 277's bound for the boundary polymers, D2.6 closure §2.4);
  Ĥ(M) = e^{−Ψ°(M)}Ĥ′(M), Ĥ′(M) := (1 + (e^{−δΨ(M)} − 1))H̃(M), |e^{−Ψ°(M)}| ≤ e^{c#(M)}; *localisation (exact)*: with
  y_𝒞 := φ^T(𝒞; 𝐔, 𝐉, ω′) − φ^T(𝒞; 1, 0, 0), e^{−δΨ(M)} = Σ_𝒦Π_{𝒞∈𝒦}(e^{−y_𝒞} − 1) and e^{ε_TδΨ_≥(T)} − 1 =
  Σ_{𝒦≠∅}Π_{𝒞∈𝒦}(e^{ε_Ty_𝒞} − 1): the chosen clusters are the *vacuum links*, field-dependent factors of the
  insertion, with domain supp 𝒞, at M or at the first M of T; Q° := exp(Σ_Tε_TΨ°_≥(T)) is the whole flat factor,
  a number given the labels (the vacuum part of the reference gas, expanded there in vacuum occurrences); the
  *scalar-linked groups* 𝔊(𝒮): two M linked if some T ∈ 𝒮 contains both; ⟨𝒳⟩ = Σ_𝔐Σ_𝒮Q°·⊗_{G∈𝔊(𝒮)}Ĥ(G),
  Ĥ(G) := Π_{T∈𝒮_G}(e^{ε_TδΨ_≥(T)} − 1)·⊗_{M∈G}Ĥ(M); no deviation factor per cluster is needed (the Cauchy step
  supplies it for Y^d_𝒢 as a whole, every vacuum-link factor vanishing at the flat point); |Q°| ≤ Π_Ge^{θ(G)},
  θ(G) ≤ c|G|.
- *(d) Merging along the loop.* Pieces of a group: the arcs I(M) of its marked polymers (the smallest arc
  containing the arcs of the slots of M), the intervals of its untouched old insertions, the arcs of the members
  of its old occurrences. Joined pairs: a scalar link or vacuum occurrence joins I(M) of its first M to the pieces
  of its other constituents; **second rule**: a constituent domain incompatible with the domain of an old
  insertion, touched or not, merges that insertion (a marked polymer's support Z ⊇ Z₀ ⊇ Y₀ is larger than the
  s-components, and the first stage only guarantees that no s-component meets X_W); **vacuum-link rule**: a vacuum
  link of one group incompatible with a marked polymer or a vacuum link of another; **third rule**: the flat factor
  Q° and the old interactions Q_k(𝔅) are expanded in cluster occurrences, and the members hit by one occurrence
  join one group. The *linked hull* of a class of pieces: the union of the pieces and, for each joined pair of
  disjoint pieces, the shorter arc between them, enlarged at each end to the end of any old interval it cuts; the
  arc I(𝒢) is the union of the linked hulls; groups whose arcs overlap are merged; the untouched old insertions
  with intervals inside an arc join its group; repeat to the fixed point (monotone, finite, independent of the
  order: the least structure closed under the rules). The results are the **groups 𝒢 of the step k + 1**; Y_𝒢 is
  the contraction along I(𝒢) of the tensors Ĥ(G), G ⊂ 𝒢, with the untouched old insertions and the transports of
  U_{k+1} between consecutive slots; the words are unchanged (a regrouping of an ordered product). Families {𝒢}
  have disjoint intervals and pairwise compatible constituent domains; distinct groups interact only by the hard
  core of the reference gas. Cost: the projective norm on ⊗End(V_π) (a contraction can cost dim(π)^{m−1} in the
  operator norm); at complex backgrounds the transports add exp(c′_π‖a′‖_∞ length(I(𝒢))), paid by the shares.
  **The paper's Section 6 has the projective norm (lines 1100–1107) and one paragraph for all of this.**

**D2.3(2)–(3), lines 2388–2486, read (tags cut at 520 characters). N; the paper has most of it in
`sec:small-field-map` ("The flat parts") and `sec:reference-gas`.**
- *(2)*: the reference point (1, 0, 0) with the regions of ℓ; the reference clause at the step k + 1 from the
  analyticity argument of D2.2(6)(e) at U_{k+1} = 1 (RG I p. 262 (1.11)–(1.14) hold strictly at (1, 0); RG II p. 15
  l. 5; the large-field objects at the flat point: the minimal orbit of CRE (2.12) at V = 1 is that of 1, so the
  minimisers are 1, 𝐇^{(k)} = 0); Schur: Y_𝒢(1, 0) = c_𝒢𝟙; the split Y^d_𝒢 := Y_𝒢 − c_𝒢T_𝐔(I(𝒢)), covariant, analytic,
  zero at (1, 0), "made in the formulas".
- *(3)*: both interactions in cluster form, expanded in occurrences: the old part as
  Σ_m((−1)^m/m!)Σ_{Γ₁,…,Γ_m each hits 𝔅}Πφ_k(Γ_j), the vacuum part as Π_𝒞(1 + (e^{(s_𝔐(𝒞)−1)φ^T(𝒞)} − 1)); absolute
  convergence; the third merging rule; each occurrence lies in exactly one group and its factor goes into Y_𝒢 with
  (−1)^{m_𝒢}/m_𝒢!; hard core: arcs disjoint, constituent domains compatible, no occurrence of one hits a member of
  the other; the reference gas is a pure hard-core gas; multilinear expansion
  tr(Y_{𝒢₁}U⋯) = Σ_{D⊆𝔉}(Π_{𝔉∖D}c_𝒢)w^d(D); resummation Σ_Dw^d(D)S°^{[D]}(ℓ);
  ⟨𝒲_k⟩ = κ^{(k)}e^{𝓔_k}S°(ℓ)[f_{k+1} + Σ_{D≠∅}Q^out_{k+1}(D)w^d(D)], Q^out_{k+1}(D) := S°^{[D]}(ℓ)/S°(ℓ) =
  exp(−Σ_{Γ hits D}Φ°(Γ; ℓ)); S°(ℓ₀) is the flat reference integral; Σ_{Γ hits 𝒢}|Φ°(Γ)| ≤ θ_{k+1}(𝒢) by FV Lemma 5.6,
  (5.17).
- **Point to settle when the large-field part is rewritten.** The map gives every group, attached ones included,
  the activity c_𝒢 = Y_𝒢(1, 0), and says that every Y^d_𝒢 vanishes at the reference point. Since 19:56 the paper
  gives the attached groups the activity 0 (needed for the comparison of two runs, and by the proof of S.9(iii)
  as written). With it: for an attached group Y^d = Y does not vanish at the reference point; the identity
  "S°(ℓ) is the flat reference integral" is used on ℓ₀ only, where there is no attached group; the D2.6 closure's
  statements on the local terms E^∂ (its 7.4(a)) and on the masses are written for the map's convention and have
  to be re-derived for the paper's (the pair's Cauchy note compares the two conventions: #PC4.14.4-4). Check
  every place where the D2.6 and D2.7 closures use c_𝒢 of an attached group.

**The closures (hash, lines, characters; 12 Nov 2026, 20:30):** background iteration 3ae13498b90a, 360, 108 000;
class activities f71859d97de4, 100, 42 000; coarse-chain interfaces d02ba134814f, 241, 54 000; complex covariance
f1cbf76fb687, 201, 28 500; D2.6 325ff1872afc, 522, 201 000; D2.7 ab6c80ebce1b, 850, 141 000; D2 open items
078f0d1a0640, 76, 28 000; O2 1c529b0ff9ad, 193, 41 000; O4 952a1687d5c4, 111, 30 000; O6 0c216608bc3e, 230,
44 000; RMJ 16b633f9adc6, 147, 22 000; RW1 4fa123269841, 102, 34 000; SW 2be3106d4b2f, 126, 33 000 (§1 the scope
11, §2 the prescription q₀ = q₁ 20, §3 the dev clause on the sub-domain 29, §4 the inductive statement that (S-w)
uses and delivers 49, §5 the local proportional gauge (LPG′) 55, §6 consequences 102). **Needed before the class
can be written exactly: SW §3 and §5 (the sub-domain; the region of the deviation per traversal, i.e. what
(Q^#_W)⁺ is for a new group), D2.6 closure 2.1 (the species tests), D2.4(7)–(8).**

**SW closure §1–§4, lines 11–54, read (tags cut at 820 characters). N: these fix the exact form of the class.**
- *The scope tests for a group 𝒢 of the step k + 1* (D2.6 closure 2.1): (i) no polymer component and no member's
  domain meets the one-layer neighbourhood of Λ_{k+1}ᶜ; (ii) every component of its polymers and every traversal
  of its arc, length allowance included, lies in Ω_k; (iii) none of its polymers carries a boundary-type
  potential; (iv) the comparison region lies in Ω_{k+1}. (S-w) is proved for every group passing (i)–(iii) (the
  count uses no comparison region; such a group does not depend on ω′, so the parity argument holds); (iv) is
  used only by the dev bound. Species, in the order inherited, wrap(k+1), att(k+1, coll), att(k+1, Z), dev: a
  set which does not lift → wrap(k+1); a failure of (i) or (iii) → att(k+1, coll), of size O(b_k), carried by the
  collar term of (ii); a failure of (ii) → att(k+1, coll); a failure of (iv) alone → att(k+1, Z), with ω′ = 0 and
  O(ρ_{k+1}) per group. *The collar* Coll_{k+1} := the cubes of π_{k+1} within d₀ := 6 layers of Λ_{k+1}ᶜ (those of
  Λ_{k+1}ᶜ included); it contains S_{k+1} and Ω_{k+1}ᶜ; Coll_{k+1} ∩ Ω_{k+2} = ∅.
- *The prescription* q₀ = q₁ =: q, an integer > p₀; C₁ = λ_RC₀; then pl = 2, ᾱ_k = g_k min(C₀, C₁)(log g_k^{−2})^q,
  𝔞_{k+1} = max(τ_k², 2ρ_{k+1}), ε_k/α_{i,k} = (A₀/C_i)(log g_k^{−2})^{p₀−q} small. (The paper has q₁ = q₀ in its
  appendix and q₀ > 25r + 5/2; check that q₀ > p₀ is among its conditions.)
- *The sub-domain*: 𝒟_k := the domain of (iii) (CRE's complex part about U_k, radii f_{k,n}α_{1,n}L^{−n} on
  Ω_n∖Ω_{n+1}, α_{1,k}L^{−k} on Ω_k, f_{k,n} := 1 − β(1 − 2^{−(k−n)})); 𝒟^sub_k := the (A′, 𝐉) ∈ 𝒟_k with, on every
  layer, |η_kA′(b)| < f_{k,n}α_{1,k}L^{−k}, (L^kξ)²|∇A′(b)| < f_{k,n}α_{1,k}, |𝐉(b) − J_k(b)| < f_{k,n}α_{0,k}(L^kξ)^{−3}
  (the top-layer radii on every layer). **Clause (iii)-dev**: analyticity on 𝒟_k; the dev bound at complex data,
  (ii) with δ*^{c}_n(U_k) + a*_n(A′) + j*_n(𝐉), and its per-insertion form
  e^{θ(W)}‖Y_W(𝐔, 𝐉)‖ ≤ b_W(Dev_W(𝐔) + a*_W + j*_W), on 𝒟^sub_k; there a* ≤ S₃₀α_{1,k}, j* ≤ 2S₃₀α_{1,k},
  S₃₀ := Σ_{t≥1}(t+1)e^{−(30/8)η_Vt}, so ρ̃_k(a* + j*) ≤ 3S₃₀(C₁/min(C₀, C₁))ρ_k. (The complex rate is 30/8 here and
  61/16 in D2.0(3): take the value from the D2.6 closure §6.5 when writing.) The consumers evaluate inside
  𝒟^sub_k: needs L ≥ 2(1+β₀)/(1−β), Lθ ≤ 1, O(1)Lθ·min(β, 1) ≤ 1 − β with θ = e^{−δ₀RM₁/32}.
- *§4, the inductive statement in one place.* Uses at the step k: (ii) with (ii-t) and (ii-w); (iii) analyticity
  on 𝒟_k; (iii)-dev on 𝒟^sub_k in the per-insertion form, **with Dev_W over the per-traversal comparison region:
  for W made at the step j, in the units of the step j, the ball of radius R^{(j)}_{t_n(W)+1} about each traversal
  n of W, t_n(W) the least t with X(W) ⊂ B_∞(n, R^{(j)}_t); the bound holds for every traversal**; the reference
  clause; (v)–(vi). Delivers the same at k + 1. With Q^#_W := that ball, ext_k(W) changes by at most 3C_box + 1.

**SW closure §5–§6, lines 55–126, read (tags cut at 760 characters). (LPG′) is NOT in the supplement (its
lemmata are listed at 20:36: none on a local gauge with the local curvature). It is a statement of Bałaban's
(CRE (3.17), VAR Theorem 1) used at a cube of the paper's choice with a local ε₁: it belongs in the supplement,
as a new lemma at the END of Section 17 (no number shifts). First closed block to write.**
- *(e) The comparison region*: for a traversal n′ of I(𝒢): t = t_{n′}(𝒢), R_t = C_boxM(t + 1), 𝒬 = 𝒬_{n′}(𝒢) the
  smallest union of cubes containing B_∞(n′, R_t), 𝒬^{∼5} ⊂ B_∞(n′, R_{t+1}) for C_box ≥ 6; R_t ≤ 2C_boxMℓ_X.
- *(LPG′)*: V_{k+1} in the support, 𝒬^{∼5} ⊂ Ω_{k+1}, E := E_𝒬(U_{k+1}), M_𝒬 := half the side of 𝒬^{∼2} rounded up to
  a multiple of R₁M₁ (R_t ≤ M_𝒬 ≤ R_t + 3M + R₁M₁); (H): 2E ≤ min(a₁, c₂), 2M_𝒬E ≤ R₁M₁a₁. Then a gauge
  transformation u near 𝒬^{∼2} with U^u_{k+1} = e^{iξA} on 𝒬^{∼2} (ξ = L^{−1}η = η_{k+1}), and
  |A|, |∇^ξA|, |∂^{ξ*}∂^ξA|, |Δ^ξA| ≤ 3B₃M_𝒬E, |R(u)J_{k+1}| ≤ 4B₃M_𝒬E, in the units of CRE (2.38)–(2.39), (2.36) at
  n = k + 1. If (H) fails, Dev is bounded below independently of g and the Cauchy step is trivial.
- *Proof in six steps*: (1) the local problem at 𝒬: the domain 𝐁_{k+1}(𝒬^{∼4}) with data Q^{s*}_{k+1}V_{k+1}, of VAR's
  kind (p. 278); condition (C-M): M ≥ 2LM₁ + 2R₁M₁, M ∈ R₁M₁ℕ. (2) CRE (3.17) at 𝒬: first line by the mixed-set
  localisation (D2.6 closure 8.3(2)(i)–(iii) = the supplement's S.8) and VAR Theorem 1's uniqueness (p. 279);
  second line VAR Proposition 9 (p. 309): U_{k+1} = (e^{iξ𝐇_𝒬}U_{k+1,𝒬})^{u_𝒬^{−1}} on 𝒬^{∼2},
  𝐇_𝒬 := 𝐇_{k+1,𝒬}(B_𝒬), B_𝒬 := (1/i)log[M^·(U_{k+1})(M^·(Q^{s*}_{k+1}V_{k+1}))^{−1}]. (3) B_𝒬 is supported in the
  boundary layer of width 2LM₁ of 𝒬^{∼4} and |B_𝒬(b)| ≤ 22d²E (CRE p. 268 l. 38–40; CMP98 Proposition 2, p. 26,
  locality; REG Lemma 1, p. 79, (1.65), p. 87). (4) |𝐇_𝒬| and its derivatives ≤ C_H·22d²E ≤ E on 𝒬^{∼2} by VAR
  (190), the distance from 𝒬^{∼2} to the support being 2M − 2LM₁; condition (C-H): 22d²C_H ≤ 1, on M. (5) VAR
  Theorem 1 for U_{k+1,𝒬} with ε₁ := 2E (block plaquettes of V_{k+1} on 𝒬^{∼4} deviate by < 2E, CMP98 Proposition
  2 with (52); CRE p. 267 l. 11–13 "only with the coefficient 1"): a gauge v with U^{v^{−1}}_{k+1,𝒬} = e^{iξA′},
  |A′| and derivatives < B₃M_𝒬·2E, the cube 𝒬^{∼2} in the class by (C-M) and M_𝒬 ≤ R₁M₁a₁/(2E). (6) composition:
  u := v^{−1}u_𝒬, A := A′ + Ad(v^{−1})𝐇_𝒬 + ξr, bounds 2B₃M_𝒬E + E + O(1)ξB₃M_𝒬E² ≤ 3B₃M_𝒬E; the current by RG I
  (1.8), (3.11)–(3.12) and VAR (22)–(23): |R(u)J_{k+1}| ≤ 4B₃M_𝒬E once a₁ ≤ 2/(9O(1)B₃R₁M₁).
- *§6*: (6a) the Cauchy step gives C^{(k+1)}_χ := (C_gC_S/c₀)e^{η_w}, C_new = C_gC_S·pl·e^{η_w}/c₀; (6b) the
  complex-data clause for new groups in the sup form: second term (1 + 2C₀/C₁)C_χρ̃_{k+1}α_{1,k+1}Σ_tw_t; (6c) the
  carried insertions: the Cauchy step cannot be run at U_{k+1} on the comparison region of an older step (it is
  smaller than one cube of π_{k+1}); real-point part = (T-dev) (its gauge at the step j for U_j(V*_j) = U_{k+1});
  complex-data excess = the complex covariance note (constant Ĉ, averaging bound (K3), C_av := 2(B₃ + 2c_dB₅));
  (6d) CRE (2.38) for U_{k+1} on Ω_{k+1} from VAR Theorem 1 with the global ε₁ = O(L²)(1+β₀)ε_{k+1}; (6e) the
  conditions: C_box ≥ 4A_E; (C-M); (C-H); a₁ ≤ 2/(9O(1)B₃R₁M₁), O(1)ξa₁ ≤ 1; L ≥ 2(1+β₀)/(1−β), Lθ ≤ 1,
  O(1)Lθ·min(β, 1) ≤ 1 − β; q₀ = q₁ > p₀; L ≥ 12(1+β₀)², L > (1+β₀)⁹; μ := min(1, MC₀/(2C_avC₁)); B₃ ≥ 1.

**D2.1(2)–(4) beginning, lines 843–900, read (tags cut at 620 characters; D2.1 is 31 000 characters).**
- *(2)*: for real A_k on the support there is a gauge transformation u with U_k(e^{iB′}V^{(k)})^u =
  e^{iη𝐇_k(B′)}U_{k+1} (CRE (3.6)), so f_k(U_k(e^{iB′}V^{(k)})) = dim(π)^{−1}χ_π(Hol_C(e^{iη𝐇_k(B′)}U_{k+1})); complex data by
  the identity theorem on a polydisc centred at a real point; at A_k = 0, 𝐇_k(0) = 0 and the value is f_{k+1}.
- *(3)*: the transport identity Hol_C(e^{iX}U) = (Π_i exp(i Ad(Γ_i)X(b_i)))Hol_C(U), Γ_i := U(b₁)⋯U(b_{i−1}); the
  first-order term in A_k, odd, of size c′_π4B₀e^{16κ_s}C₁g_k|A_k|_∞ per bond of C.
- *(4)*: the partition σ_k of the torus into cubes Δ of side M, each with a parameter s(Δ); H(s), G̃(s), H₀(s) by
  RG II p. 3's rule, 𝐇(s, B′) by RG II (1.2)–(1.5); (a) 𝐇(1, B′) = 𝐇_k(B′), 𝐇(0, B′) = 0; (b) at s(σᶜ) = 0, 𝐇(s, B′)
  vanishes near Y(σ)ᶜ and on a component Y of Y(σ) depends only on s|_Y, B′|_Y, (𝐔, 𝐉)|_Y (RG II p. 4); (c) the
  bounds RG II (1.11), (1.18) for |s(Δ)| ≤ e^{κ_s}, δ₁M ≥ κ_s.
- **A second deprecated construction in the paper.** `sec:small-field-map` (lines 1240–1246) writes
  π(T̂_m) = (1 + Y_m)π(T_m) for each traversal, expands the product over the subsets S of the traversals
  (`eq:slot-expansion`), calls the Y_m "slots", and then merges "the polymers of the expansion which meet the
  support of an insertion or the arc of a slot". The identity is exact, but a slot Y_m is a function of
  𝐇_k(B′) along its traversal, and 𝐇_k depends on the fluctuation field everywhere (with exponential decay): a
  slot has no support in the integrated field, so the merging rule is not defined. The map localises this
  dependence first, by the parameters s(Δ) of RG II (1.9)–(1.10) (D2.1(4), D2.2(4)(e)): the words are expanded
  into terms indexed by sets of cubes, whose components Y carry the dependence on B′, and the groups are built
  from these components. The subset expansion in slots is the map's device for the leading word of the *first*
  step only (lw slots, #MD2.0.3.19). **Remove `eq:slot-expansion` and the slot language from the step for
  k + 1 ≥ 2; replace by the s-expansion.**

**D2.1(4) rest and (5), lines 900–1004, read (tags cut at 520 characters). N: the expansion of a word in the
localisation parameters, for the leading word; D2.2(4)(e) extends it to words with old insertions.**
- *Expansion*: Φ(s) := Hol_C(e^{iη𝐇(s,B′)}U_{k+1}); Φ(1) = Σ_{σ⊆σ_k}Π_{Δ∈σ}∫₀¹ds(Δ)∂_{s(Δ)}Φ(s)|_{s(σᶜ)=0}; σ = ∅ gives
  Hol_C(U_{k+1}); at s(σᶜ) = 0 the factor on a fine bond b of C is e^{iη𝐇_Y(b)}U_{k+1}(b) if b lies in a component
  Y, U_{k+1}(b) otherwise; a component without a bond of C gives zero.
- *Arcs and groups*: S(Y) := the fine bonds of C in Y; I(Y) := C minus the longest maximal run of bonds not in S(Y)
  (ties to the run whose first bond comes first from the base point); groups G := the connected components of the
  overlap graph of the arcs; I(G) := ∪I(Y); Y_G := [Π_{Y∈G}Π_{Δ⊂Y}∫₀¹ds(Δ)∂_{s(Δ)}]Hol_{I(G)}(e^{iη𝐇(s,B′)}U_{k+1}) at
  s = 0 outside the components of G; result f_k(U_k(e^{iB′}V^{(k)})) = f_{k+1} + Σ_{𝔊≠∅ compatible}tr(Y_{G₁}U_{(1)}⋯);
  compatible: components connected unions of cubes containing a bond of C, arcs of the groups disjoint,
  components pairwise disjoint without a common wall, each group connected by arc overlaps; σ ↦ 𝔊 a bijection.
- *Bounds*: case (A) every component in Ω_k (RG II's constants apply; Ω_k is the scale-k set of VAR (190)); case
  (B) some component meets Ω_kᶜ (size by the D2.6 closure: the kernels carry L^{k−j}, bounded against the walk
  decay; a surviving component meets both B(Γ_{k+1}) and Ω_kᶜ). Claim for (A): if |B′|_Y ≤ ε_H for every Y ∈ G,
  ‖Y_G‖ ≤ Π_{Y∈G}(|B′|_Y/ε_H)e^{−(κ_s−2−4c′_πM‖a′‖_∞)#(Y)}: Schwarz's lemma in t_Y (B′|_Y → t_YB′|_Y, |t_Y| ≤ T_Y :=
  ε_H/|B′|_Y; at t_Y = 0 the arc product does not depend on s|_Y), Cauchy's estimate on circles of radius
  e^{κ_s} − 1 ≥ e^{κ_s−1} about s(Δ) ∈ [0, 1], the arc product ≤ e^{#(G)} (from |𝐇_Y(s, B′)| ≤ 4B₀e^{16κ_s}|B′|_Y and
  c′_πc_CM·4B₀e^{16κ_s}ε_H ≤ 1) times exp(c′_π‖a′‖_∞ length(I(G))), length(I(G)) ≤ 4M#(G) for a square (general
  loop: 4Λ̄(C)M#(G), #GL4.2). c′_π := 2c_π max(1, c_h): ‖π(e^{iX})‖ ≤ e^{c′_π|X|} for X ∈ 𝔤ᶜ. *First order*: a group
  with two or more components has no part linear in B′; for G = {Y} the linear part is odd in B′.
- *Conditions* (#28–#38): 4C₂B₀e^{16κ_s}ε₂ ≤ 1, 4C₄B₀²e^{32κ_s}ε₃ ≤ 1, 2B₀e^{16κ_s}ε₃ ≤ ε₂, C₁ε₁ ≤ ε₃ (RG II pp. 5–7),
  ε_H < ε₃, δ₁M ≥ κ_s, κ_s > 3, O(1)ε_k < ε₁^{RG2} and O(1)ε_k ≤ ε_H for every k, g_k|A_k| ≤ ε_H/C₁ on the complex
  domain, (𝐔, 𝐉) in RG II's domain I.(i)–(iii), 4c′_πM‖a′‖_∞ ≤ 1 (general loop: 4Λ̄(C)c′_πM‖a′‖_∞ ≤ 1), every
  period of the torus at least twice the side of C, |𝐇_k| < a₁, VAR (7) for V^{(k)}; ε_H also shrunk for the
  older layers and for VAR's range (D2.6 closure §4.2).
- **To re-read in the transcription before writing this subsection: RG II pp. 3–7 ((1.2)–(1.5), the rule of p. 3,
  the locality of p. 4, (1.7), (1.9)–(1.11), (1.13), (1.18), (1.20), the uniformity on p. 6), RG I pp. 265–266,
  CRE p. 267 (the transfer to the multi-domain operators).**

**Sizes of what is still unread in the map (characters):** D2.2(6) 179 000; D2.4(10)–(11) 47 000; D2.4(12)(e)
rest and (f) 24 000; D2.4(13) 20 000. With the closures and the notes for several loops this is several context
windows of reading; each block is digested here before the next is read.

| #MD2.0.3.13–.15-8 | (a) δ*^{(1)}_n ≥ L²δ*_{n_f}; (b) δ*^{(k)}_n(U_k) ≤ 2c_σB₃ε_kΣ_tw_t on the support (CRE p. 268); (c) η_{k+1}^{−2}max = L²η_k^{−2}max, and the split of the plaquette set Ω_k → Ω_{k+1}: the plaquettes of Ω_k∖Ω_{k+1} give a part which decays with the distance to Ω_{k+1}ᶜ and joins the attached part of the scale k + 1 | the paper has `eq:deviation-scaling` and `eq:contraction-first` with "+ (attached)" in `sec:contraction`; **(a), (b) and the bound of the split part: to check** | contraction, reclassification |


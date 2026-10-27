# Streamlining Plan for WILSON_FIRST_RG_STEP_V4.tex

Scope: the full manuscript (5849 lines, about 278 pages). This is a plan; the TeX file is unchanged. Dependencies were decided by reading the proofs; label searches served only to locate text. Line numbers (L…) refer to the current file.

## Summary

- **Both headline theorems are proved at the original carrier I.** The retreated-carrier route of Section 9 (L2450–3550, 344 KB, about 67 pages, 24% of the paper, 36% of the main text) feeds no theorem. Its only consumers are rem:main-regime item (2) and Section 10.7, which states itself that it is not used. Removing it, apart from the few carrier-I statements that Theorem (iii) and the factorisation corollary cite, is the largest single cut.
- **Main-chain material sits in appendices**:
  - E_h and P_h (App D, eq:c3-6-1) appear in the statement of the main theorem;
  - App D.7 (the one-point witnesses) feeds the boundary term, the defect term, and the exponential moment;
  - App C (local interaction at the identity) is used by Sections 5–7;
  - App F (the regional scalar) is the identification used in the main proof.
- **The same material is written out several times**:
  - Bałaban readings, in about ten places;
  - the flat objects, in Sections 3 and 4;
  - the conditional kernel, in Sections 3.1 and 8.1;
  - the flux identity, in Section 8.2 and prop:coarse-loop-form;
  - the Neumann-series decay argument, four times;
  - the periodic comparison, three times;
  - threshold lists, in about eight places.
- **Appendix E runs backwards**: its statements come first and their proofs sit in later subsections.
- Expected size after the plan: about 185–200 pages (Section "Size Estimate").

## Decisions Needed

1. **Remove the retreated-carrier route** (Section 9, apart from its carrier-I parts, plus Section 10.7). Recommended: remove. This saves about 63 pages and changes no headline statement.
2. **Section 8** gives the conditional form W_1(C;V) = 𝒪_V[𝒥_ξ(ℒ^(0) + ℋ_ξ)] of the outgoing observable. Nothing uses it: the proof of Theorem 1 cites it only for κ_C ≠ 0, which follows directly from eq:marginal-square-mass and eq:corner-square-factor.
   - (a) Recommended: delete Sections 8.1–8.3 (about 8 pages).
   - (b) Keep 8.3 in Section 3 notation as a subsection of "Towards the Next Step" (about 2 pages).
3. **prop:coarse-loop-form** is cited by no other result. Its parts (i)–(ii) are the flux identity of Section 8.2.
   - (a) Recommended: keep it as a corollary (statement in Section 1, proof in "Proofs of the Main Results"); delete Section 8.2 as a duplicate; cut rem:coarse-loop-form to one sentence (its item (2)).
   - (b) Delete it together with its remark (about 2.5 pages).
4. **Two rates for the leading-error moment.**
   - Theorem (iii) uses δ^I_q = Cτ²N'_lat e^{Cτ²Φ_c} q^{1/C_K}. It bounds E_h[1_{A_cov} e^{|E°_ξ|}] via the joint witness bound lem:c5-7-joint and lem:c5-7-expmoment.
   - cor:main-factorisation uses δ^♯_q = Cτ²N'_lat e^{Cτ²L⁴C_KΦ_c} q^{1/16}. It bounds E_h[1_{A_cov}|e^{E^∂_ξ} − 1|] via a 16-colour chessboard argument written inside its proof (L214–221).
   - (a) Recommended: keep both statements unchanged and place the two arguments side by side in the new moment section.
   - (b) Derive both from the chessboard argument and drop the joint-witness route. This changes δ^I_q in Theorem (iii), a headline constant, so it needs your approval.
5. **The finite-torus limit characterisations**: the second equality of eq:marginal-square-mass, eq:corner-ratio-limit, and eq:corner-fixed-square-limit. None is used in a proof.
   - (a) Recommended: keep them as two-line corollaries of the quantitative periodic comparison, moved into Section 6; delete their separate qualitative proofs (L1682–1704 and L1780–1801).
   - (b) Delete them.
6. **Main text versus appendices for Appendices D and E.**
   - Recommended:
     - the history measure, the one-point witnesses, and the exponential moment go into the main text;
     - the boundary-term estimate (App D.1–D.5 with prop:c3-7-5) stays an appendix;
     - the defect-term estimate (App E) stays an appendix, in linear order.
   - Alternative: both estimates in the main text, as Sections 8–9.

## Structural Findings

### What the Headline Proofs Use

- **thm:main-theorem** (proof at L188–190) uses:
  - (i)–(ii):
    - cor:c4c-5-2 and prop:c4c-5-1 (App F);
    - prop:regional-square-extraction (Section 7.4);
    - prop:c4-12-3, eq:c4-12-8 (defect term, App E);
    - prop:c3-7-5, eq:c3-7-14 (boundary term, App D).
  - (iii):
    - eq:c5-7-expbound-I (cor:c5-7-4(c) at I);
    - the refined split cor:c5-7-2(c) applied at D = I;
    - eq:c5-7-expmoment-I and eq:c5-7-joint-I.

    These four rest only on App D.7: lem:c3-7-2, lem:c3-7-3, lem:c3-7-4, and eq:c3-7-chessboard.
- **cor:main-factorisation** uses prop:c4c-5-1, together with N'_lat(c), Φ_c, and C_K from lem:c5-7-expmoment and lem:c5-7-joint (carrier-I parts) and the one-point rate of App D.7.
- **cor:main-leading-size** uses cor:main-factorisation, eq:c3-7-3, and Section D.7.
- **thm:two-loop-theorem** uses Section 10.1–10.6 with the group sums of App E (lem:c4-6-1, lem:c4-6-env, lem:c4-6-3, lem:c4-8-2, lem:c4-9-2, sec:c4-9-4), at carrier I (L3740).

### Citations of Section 9 from Outside It

- L189 lists the hypotheses of the preamble of cor:c5-7-4 (prop:c5-5R-4, prop:c5-5-9, eq:c5-5R-T, lem:c5-7-3, prop:c5-6-4) and checks that (H2)–(H3) imply them. This bookkeeping disappears once the carrier-I statement carries its own hypotheses.
- App D L4634, L4653, L4671, and L4704 cite "(I1), (I2) of Section 9.0". These are the range and row-sum statements of lem:hessian-gauge-locality and lem:regular-bounds, plus the norm comparison |·|_σ ≤ √N h. The citations repoint to Section 3.
- c_q of eq:c5-2-3 is the ϑ = 1 case of prop:c5-2-6 and equals c_* (L157). The symbol appears in the statements at L182, L345, and L352, so it stays and is defined in the witness section.
- eq:c5-3-1 (ℓ = LMR_1 ≤ L²M(2 log g_0^{-2})^𝔯), with the comparison paragraph L2679–2688, is a genuine input of L193, App D L4941, and App E L5080. It moves to the thresholds appendix.
- L1565, L3781, and L5733 cite eq:c5-7-T for conditions of (H3) type. These repoint to (H3) or the thresholds appendix.
- Pointer sentences elsewhere: L405, L818, L1225, L3553, L4542, L4547, L4553, L4604, L4739, L4885 (in part), L4945, L5053, L5289, L5722, and L5775.

### Material Written Out More Than Once

1. **Bałaban readings** appear in:
   - (H4) L159;
   - the Section 3 conventions L407;
   - Section 3.1: (B1)–(B4) L470–474, the step list L468, and lem:borel-minimiser;
   - the (1.22) discussion L708–719 and "The inputs" L743;
   - Section 4 L1319–1336;
   - App B.8 L4551;
   - App D.9 (prop:c3-9-1, lem:axial-boundary-field);
   - App E sec:c4-11-5.
2. **Flat objects.** Section 4 defines at U = id the average, Q, N, h, C, D̃, the gauge mean, the Hessian, and the Haar density. These are the U = id case of Sections 3.2–3.3; lem:identity-primitives(i) proves the agreement.
3. **The conditional kernel.** Section 8.1 redefines the kernel of the measurability paragraph of Section 3.1 (L2330 says so) and restates lem:covered (L2357).
4. **The flux identity.** Section 8.2's Y_c = e^{−iβ_c}, P_c = Y_c V(c) is prop:coarse-loop-form(i)–(ii).
5. **Neumann-series decay** appears as:
   - App A eq:bulk-neumann-inverse;
   - Section 7 (decay of C_D);
   - lem:c3-4-1;
   - lem:c5-1-1.
6. **The periodic comparison** is proved quantitatively in the proof of prop:regional-square-extraction (L2245–2253), and qualitatively in Section 5 L1682–1704 and Section 6 L1780–1801.
7. **The density-derivative method** is written out in Section 7.2 (L1945–1975) and again in the proof of prop:regional-square-extraction (L2217–2237).
8. **Threshold lists** appear in:
   - (H2);
   - eq:c-standing-conditions with L420;
   - App B.8;
   - eq:c3-1-2;
   - sec:c4-9-2;
   - every eq:c5-*-T;
   - "threshold of Lemma X" items.
9. **Inside App E:**
   - lem:c4-7-2 (eq:c4-7-6) is the first bound of lem:c4-4-2 (eq:c4-4-9);
   - ω(g_0) and R_Υ are defined in sec:c4-4-1 and again in eq:c4-7-1;
   - u is defined in sec:c4-4-1 and again in eq:c4-10-9;
   - eq:c4-12-1–eq:c4-12-2 restate lem:c4-4-3 and the bound of lem:c4-9-1;
   - sec:c4-11-1 restates the collar and boundary-response identities of Section 3.4.

### Order Inside Appendix E

- sec:c4-7 opens with "supplies the quantitative steps used in Section c4-4".
- lem:c4-6-2 is proved by "the combinatorial payment of Sections c4-8-2 and c4-8-3".
- lem:c4-6-4 is stated in sec:c4-6-3 and proved in sec:c4-12-2.
- There is no subsection c4-5: rem:c4-5-1 sits in sec:c4-6.

### Section 1

Section 1 contains:
- a notation paragraph of about one page;
- (H4), which is about three pages of readings;
- rem:main-regime (8 KB);
- four long proofs (L213–313, 27 KB, about 5 pages).

## Target Structure

### Main Text

| New | Title | Content | From |
|---|---|---|---|
| 1 | Introduction and Main Results | Setting, first step, (H1)–(H4) with (H4) a pointer, statements of thm:main-theorem, cor:main-factorisation, cor:main-leading-size, prop:coarse-loop-form (Decision 3), and thm:two-loop-theorem, a one-paragraph remark on the regime, and the roadmap | Section 1 (statements only); Section 2 as one paragraph (g_1 via [CRE, (1.27)]; δm and z_c as the quantities to extract) |
| 2 | The Sourced Effective Interaction | Branch data, Hessian, primitives, collar, walks, polymers, joint extraction; definitions of E_h, P_h, and E_bdry; the expectation identity | Section 3 without the readings; App D eq:c3-6-1–eq:c3-6-2; App E L5383–5387 (eq:c4-8-1, positivity of 𝒪, 0 < 𝒵_0 < ∞, the empty far uncovered event) |
| 3 | The Flat Reference Integral | Flat objects as the U = id case; the subsection "Locality of the Interaction at the Identity" | Section 4; App C (label sec:perimeter-attempt becomes sec:identity-locality) |
| 4 | The Straight Edge | Unchanged apart from trims | Section 5 without L1682–1704 |
| 5 | The Corner | Corner expansion; the periodic comparison lemma; limit formulas as corollaries (Decision 5) | Section 6 without L1780–1801; L2245–2253 from the proof of prop:regional-square-extraction |
| 6 | The Regional Square Scalar | Traversal polynomial; lemma "The Conditional Reference Kernel at Identity Data" (facts (1)–(5) of L2106–2123 with eq:regional-collar-sizes); lem:identity-primitives; prop:regional-square-extraction; then the identification with S° and the extraction at I | Section 7.1 (eq:regional-wilson-polynomial only); 7.2 (definitions eq:regional-precision–eq:regional-distance; the density-derivative identity moves into the square proof, which repeats it at L2217–2237); 7.3 without the periodic straight segment; 7.4; App F |
| 7 | The History Measure and the Leading-Error Moment | One-point witnesses, reflection positivity, chessboard, the one-point rate c_q; joint witness bound, exponential moment, and moment corollary at I; the chessboard rate δ^♯_q | App D.7 without prop:c3-7-5's proof; carrier-I parts of Section 9.7; L214–221 |
| 8 | Proofs of the Main Results | Proofs of thm:main-theorem, cor:main-factorisation, cor:main-leading-size, and prop:coarse-loop-form | L188–190, L213–222, L235–241, and L282–313 |
| 9 | Two Disjoint Squares | Section 10.1–10.6 and its proof | Section 10 without 10.7 |
| 10 | Towards the Next Step | conj:iteration with a short introduction and a short remark | Section 11, trimmed |

### Appendices

| New | Title | Content | From |
|---|---|---|---|
| A | Bałaban's First Step as Used Here | Fibre measures of submersions; the step list (1.11)–(1.15); (B1)–(B4) with justifications and readings; measurability and lem:borel-minimiser; the (1.22) change of variables, its readings, and lem:boundary-bijection; prop:c3-9-1 and lem:axial-boundary-field; the [RG1, (0.6), (0.10)] readings | (H4) L159; L407 (readings part); L427, L461, and L468–493; L708–721 and L743; L1319–1336; App D.9; sec:c4-11-5 (readings part); L4551 (readings part) |
| B | The Flat Covariance | Lemmas "Uniform Flat Gap" and "The Infinite-Lattice Covariance"; one general Neumann-decay lemma, cited by Section 6, lem:c3-4-1, and App A itself | App A, currently paragraphs only |
| C | Background Estimates | Domain geometry, regular bounds, charts, Gaussian payment, Mayer constants, vacuum clusters, reference data | App B.1–B.7 |
| D | The Exterior Response and the Boundary Term | Response lemmas, cor:c3-6-1, prop:c3-7-5 with its proof | App D.1–D.5, D.6 (corollary), and D.7 (prop:c3-7-5) |
| E | The Defect Term | Linear order (Section "Appendix E in Linear Order") | App E |
| F | Constants and Thresholds | The order of choice of constants; every threshold of the paper in one list | App B.8 without item 4; L420; eq:c3-1-2; sec:c4-9-2 (eq:c4-9-3); eq:c5-3-1 with L2679–2688; sec:c4-12-4; sec:c4-7-1 (order of choice); the two-square thresholds |

The headline statements (thm:main-theorem, thm:two-loop-theorem, cor:main-factorisation, cor:main-leading-size, and conj:iteration) keep their wording, apart from reference targets and Decision 4(b).

## Removals

| # | Item | Lines | Reason |
|---|---|---|---|
| R1 | The retreated-carrier route: Sections 9.0–9.7 apart from the carrier-I parts listed under M7 | L2450–3550 | Used by no theorem (Section "What the Headline Proofs Use") |
| R2 | Section 10.7 "The Retreated Carrier" and the last sentence of L3553 | L3726–3741 | States itself that it is not used |
| R3 | Section 8 (Decisions 2 and 3) | L2266–2449 | 8.1 restates Section 3.1 and lem:covered; 8.2 is prop:coarse-loop-form(i)–(ii); 8.3 has no consumer |
| R4 | The straight-segment results of Section 7: the source framing of 7.1 (K_ξ(t), K_ξ,vac, the flat projection), prop:regional-coefficient, the periodic straight segment, the kernel and mass identifications | L1857–1881 (in part), L1930–2020 (in part), L2067–2105, L2124–2140 | Not used by the square proof; App F uses only the identity-data facts, which become a lemma |
| R5 | Section 2 apart from one paragraph: Π_1, the β_1 sum, eq:balaban-regular-subtraction, and S_φ1 | L363–400 | Unused; only g_1 = g_1(g_0) of [CRE, (1.27)] enters, and Section 3.1 defines it |
| R6 | The qualitative torus limits (Decision 5) | L1682–1704, L1780–1801 | Superseded by the quantitative periodic comparison |
| R7 | App B.8 item 4 (collar thresholds) and the second-order-rate sentences of L4551 | L4539–4554 (in part) | Exist only for Section 9 |
| R8 | sec:c4-11-1 "Which Exterior Dependence Is Removed" | L5605–5618 | Restates the collar and boundary-response identities of Section 3.4 |
| R9 | Remarks: rem:main-regime item (2); rem:c3-5-1; rem:c3-8-1; rem:c4-5-1; rem:c4c-8-1; rem:coarse-loop-form apart from one sentence | — | Scope and defensive remarks; item (2) restates Section 9 |
| R10 | The notation-clash paragraph L422 and the disclaimers at L890, after the renames of Section "Notation" | L422, L890 | Each letter gets one meaning |
| R11 | The version-history comment | L2–19 | History |
| R12 | Pointer sentences into Section 9 | L189 (preamble bookkeeping), L405, L818, L1225, L1565, L3553, L4542, L4547, L4553, L4604, L4739, L4885 (the prop:c5-2-6 mention), L4945, L5053, L5289, L5722, L5733, L5775, and the last sentence of lem:c3-7-seed | Their target goes |

### Labels Removed

- **R1, Section 9** (118 labels; the ones under M7 survive under new labels):
  - 9.0–9.1: sec:one-step-insertion, sec:c5-0, eq:c5-0-1, sec:c5-1, lem:c5-1-1, lem:c5-1-2, eq:c5-1-1, rem:c5-1-3, and eq:c5-1-2.
  - 9.2: sec:c5-2, sec:c5-2-1, eq:c5-2-1, rem:c5-2-2, sec:c5-2-3, lem:c5-2-3, lem:c5-2-4, lem:c5-2-5, prop:c5-2-6, eq:c5-2-2, and eq:c5-2-3 (c_q moves).
  - 9.3: sec:c5-3, sec:c5-3-1, lem:c5-3-0, lem:c5-3-1, rem:c5-3-2, lem:c5-3-3, sec:c5-3-4, eq:c5-3-mark-inequality, eq:c5-3-coverage-average, eq:c5-3-1 (moves), and eq:c5-3-2.
  - 9.4: sec:c5-4, eq:c5-4-1, lem:c5-4-0, eq:c5-4-4, sec:c5-4-2, eq:c5-4-2, eq:c5-4-3, lem:c5-4-1, lem:c5-4-2, eq:c5-4-T, eq:c5-4-Tp, eq:c5-4-5, cor:c5-4-3, lem:c5-4-4, and rem:c5-4-5.
  - 9.5: sec:c5-5, sec:c5-5-0, lem:c5-5-1, eq:c5-5-1, eq:c5-5-2, sec:c5-5-2, eq:c5-5-T, lem:c5-5-2, eq:c5-5-3, eq:c5-5-4, lem:c5-5-3, eq:c5-5-5, lem:c5-5-4, lem:c5-5-5, eq:c5-5-6, lem:c5-5-6, lem:c5-5-7z, lem:c5-5-7, eq:c5-5-7, eq:c5-5-8, lem:c5-5-8, prop:c5-5-9, eq:c5-5-9, cor:c5-5-10, eq:c5-5-10, and rem:c5-5-11.
  - 9.5R: sec:c5-5R, eq:c5-5R-T, lem:c5-5R-1, lem:c5-5R-2, lem:c5-5R-3, prop:c5-5R-4, eq:c5-5-9R, and rem:c5-5R-5.
  - 9.6: sec:c5-6, lem:c5-6-1, eq:c5-6-1, eq:c5-6-2, lem:c5-6-2, lem:c5-6-3, prop:c5-6-4, eq:c5-6-3, eq:c5-6-4, prop:c5-6-def, eq:c5-6-def-1, eq:c5-6-def-2, eq:c5-6-def-3, and rem:c5-6-5.
  - 9.7: sec:c5-7, eq:c5-7-1, eq:c5-7-T, lem:c5-7-1, cor:c5-7-2 (its part (c) at I survives, M7), eq:c5-7-2 (the form of eq:regional-square-error, which is cited instead), eq:c5-7-3, lem:c5-7-3, eq:c5-7-4, eq:c5-7-joint, eq:c5-7-expmoment, cor:c5-7-4, eq:c5-7-delta, eq:c5-7-expbound, eq:c5-7-leading-modulus, eq:c5-7-delta-small, and rem:c5-7-5.
- **R2**: sec:two-loops-retreated and lem:two-loop-retreated.
- **R3**:
  - sec:remaining-physical-comparison;
  - eq:extracted-loop-scalar (App F L5722 repoints to the definition of κ_{C_n} in Section 1);
  - eq:retained-reconstruction, eq:retained-source-domain, eq:retained-change-domain, eq:retained-prechange-density, eq:retained-positive-kernel, eq:retained-outer-measure-identities, and eq:retained-outer-kernel;
  - eq:retained-flux, eq:retained-flux-reversal, and eq:retained-loop-insertion;
  - eq:retained-conditional-law, eq:retained-disintegration, eq:retained-leading-source, eq:retained-source-correction, eq:retained-first-step-numerator, and eq:retained-outgoing-observable.
- **R4**: prop:regional-coefficient, eq:regional-coefficient-bound, eq:regional-summed-bound, eq:regional-periodic-line-tail, eq:regional-torus-bound, eq:regional-kernel-identification, and eq:regional-mass-identification. eq:regional-resolvent, eq:regional-covariance-difference, and eq:regional-density-derivative move into the proof of prop:regional-square-extraction.
- **R5**: sec:extraction-procedure (L405 repoints to Section 1) and eq:balaban-regular-subtraction.
- **R6**: eq:corner-fixed-square-limit becomes a corollary label under Decision 5(a), or is removed under 5(b).
- **R8, R9, and App E merges**:
  - sec:c4-11-1, rem:c4-5-1, rem:c3-5-1, rem:c3-8-1, rem:c4c-8-1, rem:coarse-loop-form, lem:c4-7-2 (merged into lem:c4-4-2), sec:c4-12-1 (folded into lem:c4-9-1), and sec:c4-7-1 (merged into one parameter subsection);
  - lem:c4c-2-1 keeps its label as the single identification lemma.

The labels part1-, c2-, c3-, c4-, c4c-, and c5- do not appear in the PDF, so renaming them is optional and not part of this plan. Two exceptions get renamed because their names describe a removed route:
- sec:perimeter-attempt becomes sec:identity-locality;
- sec:one-step-insertion goes with R1.

## Moves and Merges

| # | What | From | To |
|---|---|---|---|
| M1 | E_h and P_h (eq:c3-6-1), E_bdry (eq:c3-6-2), and the expectation identity eq:c4-8-1 with positivity of 𝒪, 0 < 𝒵_0 < ∞, and the empty far uncovered event | App D.6; App E L5383–5387 | Section 2 (old 3), after eq:c-one-step-branch-identity |
| M2 | The local interaction at the identity (eq:perimeter-literal-local-sum, eq:perimeter-literal-local-bound, eq:perimeter-literal-total-reserve) as a lemma | App C | Section 3 (old 4) |
| M3 | The regional-scalar identification: lem:c4c-2-1, prop:c4c-5-1 with the refined split of cor:c5-7-2(c) as its part (b), and cor:c4c-5-2 | App F, Section 9.7 | End of Section 6 (old 7) |
| M4 | The flat objects stated as the U = id case of Sections 3.2–3.3 (lem:identity-primitives(i) becomes a remark) | Section 4 | Section 3 (old 4), one sentence each |
| M5 | Facts (1)–(5) of L2106–2123 with eq:regional-collar-sizes, as the lemma "The Conditional Reference Kernel at Identity Data", stated at the carrier I | Section 7.3 | Section 6 (old 7) |
| M6 | The periodic comparison eq:regional-square-periodic-comparison as a lemma, with the limit formulas as corollaries | Proof of prop:regional-square-extraction, L2245–2253 | Section 5 (old 6) |
| M7 | The carrier-I moment results: joint witness bound (eq:c5-7-joint-I, with C_K), exponential moment (eq:c5-7-expmoment-I with φ_c, Φ_c, N'_lat, R_0', and ϱ_K ≤ 2L + 1 of eq:c5-7-boundary-marks), moment corollary eq:c5-7-expbound-I with δ^I_q and its smallness, the one-point rate c_q (eq:c5-2-3 at ϑ = 1), and the chessboard rate δ^♯_q | Section 9.7 (I-parts), L2600, L214–221 | Section 7 (new), after the witness lemmas |
| M8 | One-point witnesses: lem:c3-7-1, lem:c3-7-block, lem:c3-7-seed, lem:c3-7-2, lem:c3-7-3, lem:c3-7-4, eq:c3-7-rp, and eq:c3-7-chessboard | App D.7 | Section 7 (new) |
| M9 | Proofs of cor:main-factorisation, cor:main-leading-size, prop:coarse-loop-form, and thm:main-theorem | Section 1 | Section 8 (new) |
| M10 | Bałaban readings (list in "Target Structure", Appendix A) | Ten places | Appendix A (new); (H4) becomes three or four lines |
| M11 | Thresholds and the order of choice (list in "Target Structure", Appendix F) | Eight places | Appendix F (new); each lemma names its threshold by number there |
| M12 | One Neumann-decay lemma: a finite-range bounded positive operator with a gap has an entrywise exponentially decaying inverse, uniformly under principal restriction | App A eq:bulk-neumann-inverse, Section 7 (C_D), lem:c3-4-1 | Appendix B (new) |
| M13 | lem:two-loop-inputs(d)–(e) as instances of the moment lemma of M7, stated for a finite set of contours; the Section 10 proof of (iii) cites prop:c4c-5-1(b) in place of cor:c5-7-2(c) | Section 10 | Section 9 (new) |
| M14 | rem:main-regime item (3) ("not proved here") as two sentences | Section 1 | Section 10 (new) |
| M15 | The norm comparison |·|_σ ≤ √N h and the range and row-sum facts cited as "(I1), (I2) of Section 9.0" | Section 9.0 | Section 3 conventions; App D citations repoint to lem:hessian-gauge-locality and lem:regular-bounds |

## Appendix E in Linear Order

| New | Content | From |
|---|---|---|
| E.1 Operand and Near Histories | ℛ_ξ and E_def; near histories (lem:c4-2-1); the interior operand | sec:c4-1, sec:c4-2, sec:c4-3 (without rem:c4-5-1) |
| E.2 Analytic Inputs | Joint background/phase analyticity, differentiated walks, the complex-Gaussian moment, source remainders, tree gauge (lem:c4-10-5), Hessian bounds along the path (lem:c4-7-3), covariance of the selected coefficient, the curvature input | sec:c4-10; sec:c4-7-3; sec:c4-11-2; sec:c4-11-5 (curvature part) |
| E.3 Signed Selected Integrals | One parameter subsection (u, v, ω(g_0), R_Υ, u_*, defined once); dummy comparison (lem:c4-4-1); positive host comparison (lem:c4-7-1); lem:c4-4-2 with the commuting-projection proof of lem:c4-7-2; one background derivative (lem:c4-4-3); derivative of the cluster sum (lem:c4-7-4); the joint ratio (lem:c4-4-4) | sec:c4-4, sec:c4-7 |
| E.4 The Group Coefficient | c_W, d_W, and lem:c4-6-1; interior boxes and endpoints; the coefficient path (lem:c4-9-1, absorbing eq:c4-12-1–eq:c4-12-2); endpoint conventions and the lifting claim | sec:c4-6-1, sec:c4-8-4, sec:c4-9-1, sec:c4-11-3, sec:c4-11-4, sec:c4-12-1 |
| E.5 Group Sums | Component pins (lem:c4-8-2, with the reserve convention of sec:c4-12-4 in its proof); class pins (lem:c4-8-3); footprints (lem:c4-6-env); positive group sums (lem:c4-6-2); reference group gas (lem:c4-6-3); countable species (lem:c4-9-2) | sec:c4-8-2, sec:c4-8-3, sec:c4-6-2, sec:c4-9-3, sec:c4-12-4 |
| E.6 Assembly | Group pin sum (lem:c4-6-4 with its proof from sec:c4-12-2); family sum (lem:c4-6-5); integrability; prop:c4-12-3 | sec:c4-6-3, sec:c4-6-4, sec:c4-12-2, sec:c4-9-4, sec:c4-12-3 |

The expectation identity of sec:c4-8-1 moves to Section 2 (M1). The other paragraphs of sec:c4-8-1 (carrier, source, and physical weights; covariance) join E.1. sec:c4-9-2 moves to Appendix F, and sec:c4-11-1 is removed (R8).

## Sentence-Level Trims

### Defensive and Negative Sentences

These are sentences that say what is *not* done or assumed. Each one is deleted, or shortened to its positive content:

- **Section 3**: last sentence of L1215.
- **Section 4**: L1362.
- **Section 5**: L1378, L1405, L1477, L1479, L1489, L1525, L1617, L1657, and L1705.
- **Section 6**: L1825 and L1836.
- **Section 7**: second half of the last sentence of L2151; the remark paragraph L2264.
- **Section 10**: second sentence of L3608.
- **App A**: L3825, L3865, and the last sentence of L4073.
- **App C**:
  - the parenthesis at L4559 (the constant is renamed instead);
  - L4560;
  - the last two sentences of L4601.
- **App D**:
  - L4867;
  - L4925, which shortens to "adapted from [FV, Thm 10.11]";
  - the last sentence of the proof of cor:c3-6-1.
- **App E**:
  - L5110 (first sentence and the closing parenthesis);
  - L5150 (second half);
  - L5188;
  - the last sentence of L5275;
  - L5292 ("adds no assumption");
  - L5459 (second clause);
  - the last sentence of L5526;
  - L5561 ("not a new exponential reserve");
  - the last sentences of L5633 and L5644;
  - L5651 (second sentence);
  - the last sentence of L5697;
  - L5716 (whole paragraph).
- **App F**:
  - the last sentence of the proof of lem:c4c-2-1;
  - the two "not …" clauses of L5741.

### Internal Jargon

"Young" (young variable, young label, young fibre, young integration carrier, young field) occurs about 32 times outside Sections 8 and 9. The lines are L320, L405, L427, L438, L641, L749, L750, L848, L890, L1005, L1137, L1142, L1176, L2151, L4326, L4607, L4639, L4653, L4674, L4690, L4769, L4790, L4794, L5087, L5091, L5204, L5222, L5526, and L5725.

The proposed replacements describe the variable plainly: "the integration variable a" (the free field on the carrier I), "integration label", and "the fibre of integration variables". The letter A_e keeps the name "exterior fluctuation".

### Notation

After R1–R4, these clashes from L422 remain. Proposed renames, final names subject to your approval:

| Letter | Meanings | Proposal |
|---|---|---|
| R_0 | Bałaban's scale (quotes, lem:c3-7-seed); this paper's range 4(1 + R_* + R_H + L) | the paper's range becomes R_rng |
| R_* | walk range n_*R; the label-support range from Section 5 on | the latter becomes R_lab |
| R_1 | scale integer; Bałaban's large-fluctuation region | the region becomes 𝓡_1 in quotations |
| ℓ | macro side LMR_1 (App D.7, the moment section); selection labels | the macro side becomes ℓ_M |
| θ | Mayer constant; witness threshold (App D.7) | the witness threshold becomes θ_w |
| C_L | coercivity constant (App A, γ_L = C_L^{-1}); contour constant |Γ_C| ≤ C_L n_C | the contour constant becomes C_Γ (and C'_L becomes C'_Γ) |
| K | the integer 256 of σ_K and C_K; the exponent of [RG1] in ε = L^{-K}; the row input count of sec:c4-10-4 | 256 becomes K_c; the row count becomes K_row |
| ω | background direction; the number ω(g_0); the host budget ω_* | ω(g_0) becomes ω_g |

The M(W) clash disappears with R3 (Section 8 meaning), and the m clash with R4 (segment length). After the renames, L422 shrinks to one sentence on the fonts of B and F, and the disclaimers at L890 go.

### Long Paragraphs

- **Section 1**:
  - (H4) at L159 becomes three or four lines pointing to Appendix A;
  - the constant bookkeeping in the notation paragraph (L157) and at L352 moves to Appendix F;
  - L126 shrinks to the definition of the first step and the measures;
  - rem:main-regime becomes one paragraph: the scales tend to zero, and the bounds are absolute with the stated relative size.
- **Section 3**:
  - L407 keeps the chart and norm conventions only;
  - L427 keeps the definitions (the fibre-measure discussion goes to Appendix A);
  - L743 "The inputs" becomes two sentences;
  - L1225 is rewritten for the new order, which also fixes the raw "eq:c-one-step-branch-identity" written there without \eqref.
- **App D.1**: the restatements of r (eq:c3-1-1), of the conditional law ν_{ξ;t}, and of the score are replaced by references; eq:c3-1-2 moves to Appendix F.
- **Section 11**: the introduction L3785 shrinks to the statement of what is iterated; rem:next-step gives one sentence per item, with item (b) as one sentence and its citation.
- **App B.8 L4553** "Further conditions" becomes the list of Appendix F.

## Size Estimate

The estimate uses 5.1 KB of TeX per page, the current average. Equation-dense parts overstate it slightly.

| Item | Pages |
|---|---|
| R1 Section 9, less about 4 pages kept under M7 | −63 |
| R3 Section 8 (Decision 2(a)) | −8 |
| R4 straight-segment results | −4 |
| Duplicates: Bałaban readings consolidated, flat objects, App D.1, App E internal, threshold lists | −9 |
| Defensive sentences and long paragraphs | −5 |
| R2, R5–R7, R9–R11 | −5 |
| **Total** | **about −85 to −95** |

Result: about 185–200 pages, down from 278. Without Decision 1, the saving is about 25 pages.

## Order of Work after Approval

1. Write Section 7 (new) from M7 and M8 at the carrier I. Repoint the proofs of thm:main-theorem, cor:main-factorisation, and Section 10 to it. Then delete Section 9, Section 10.7, and the pointer sentences R12.
2. Section 8 and prop:coarse-loop-form, per Decisions 2 and 3.
3. M1–M6 and M9: E_h, E_bdry, and the expectation identity into Section 2; App C into Section 3; App F into Section 6; proofs out of Section 1; the periodic comparison into Section 5; R4 and R6.
4. M10 and M11: Appendices A and F; (H4) and the notation paragraph shortened; R5 and R7.
5. App E in linear order, with its internal merges; M12–M15.
6. Sweeps: defensive sentences, jargon, notation, long paragraphs, Oxford commas, and headline capitalisation of every new title.
7. Check: compile a copy in the scratchpad twice. Require zero undefined references, zero multiply defined labels, and zero overfull boxes; CRLF line endings preserved. Append the final removed-label list to this file.

All edits use the Edit tool on the TeX, keep CRLF line endings, and leave line wrapping as it is.

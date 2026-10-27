# D2.6 closure: triage of round 28 (it1-d26-s{4,7}-20261025-r9; both reports read in full; repairs 12:05–12:1x, 25 Oct, date)

Round 28 re-reviewed §4 (s4) and §7 (s7) after the round-27 repairs (WILSON_IT1_D26_TRIAGE_R27_2026_10_25.md). Both ran on claude-opus-5-5 through the CLI route. No fatal item. Serious: s4 S-B, a labelling error, repaired below. No new OPEN item.

## s4 (§4, kind (γ))

Verdict: "not yet correct as labelled". No fatal; serious S-B; minors m-D′, m-C residue, m-E residue, m-F; nits N-1 to N-5.

- S-B (round 27's S-A covered only att members): ω-dependent wrap(j) members exist (2.1(e) makes wrap groups that fail (i)), and touched ones are evaluated at R(w(s,t))ω. The lw slots also depend on ω, through ω₀ (a_old, A_e and m̂; §6.1 *The ω-polydisc*, map D2.0(3) *The telescoped leading word*). Repaired by splitting the members into three classes in 4.2(iii), and relabelling 4.2, 4.3 and 4.5 to match:
  - (1) members made at a step ≥ 2 that depend on ω (att or wrap(j)). These rest on O6 at every point of the ω-polydiscs, R(w(s,t))ω included, in both the (T2) and the wrap(j) cases.
  - (2) step-1 members (att(1, ·), wrap(1), lw, step-1 dev). These depend on ω only through ω₀. Their bounds over the r_{ω,0}-polydisc are D(1)(iii)'s and, for lw, §6.1's (R-st). Evaluating them at R(w)ω₀ rests on O3.
  - (3) ω-free members. This includes every dev member of step ≥ 2, by 2.1(i) read structurally.
  - **Departure from the suggested wording.** The reviewer proposed putting "every touched inherited member (att, lw or wrap(j)) that depends on ω" on O6. I did not do that for lw and the other step-1 members. Their ω-dependence is through ω₀ only, and O6 concerns the localised terms at complex σ_k, which they do not contain. Their open point is O3.
  - Also: §8's O6 consumer list now names 2.1(e)'s wrap groups and the (T2)/wrap(j) cases, and 5.1's propagation clause now names all ω-dependent members.
- m-D′ (repair (a) taken): an att(k+1, coll) group failing only (ii) is ω′-free in 2.1(i)'s structural sense. By 2.1(d), the reference clusters meeting Coll_{k+1} go to att parts. By 2.2, ω′ enters only through terms localised at the σ_k-bonds and through the old members' own domains. So the activity of such a group, and the set of such groups, do not depend on ω′. Their bound and rooted sum therefore equal the real-σ_k values, where the re-run is derived. The round-27 qualifier is withdrawn in 4.3's label, and §8's O6 entry now says "ω′-dependent" groups. 2.1(a) and the dev totals need no qualifier.
- m-C residue, all done against the VAR transcription:
  - 4.2's label now reads: threshold accepted from Bałaban, R-uniformity printed for a₁ (p.279, p.304), derived for Sect. G.
  - (187)'s O(1) is added to the constant list. VAR states its usage at p.291, after (86): "We have gathered together all the constants into an absolute constant O(1)".
  - "(77) (p.290), re-imposed at p.307 for A′ satisfying (77) with ε₃ sufficiently small".
  - "M′ε₁ ≤ a₁" is the condition ε₁ ≤ R₁M₁a₁/M. Here M′ = (R₁M₁)^{−1}M in p.304's second case and M′ = 1 in the first. The condition depends on M but not on R.
  - "M′ may be up to 2M" is deleted.
- m-E residue: by 2.1(i), dev members of step ≥ 2 are ω-free, so only step-1 dev insertions can depend on ω (through ω₀). Their bound over the polydisc is D(1)(iii)'s. It is not settled here whether a good group's Υ⁰_W consults ω₀: its free inputs lie in D(Λ), but its rows may be fed by A_e. If it does, its bound is D(1)(iii)'s, not O6.
- m-F: O3 is the map's (6)(e) base-point item. 4.5's label now reads "not closed, at every k, for the factors depending on ω₀ or ω₁ and for every factor whose evaluation domain meets Ω₁∖Ω₂ (O3: the j = 0, 1 base points on Ω₁∖Ω₂)". §8's O3 entry lists §4.2(iii) and §4.5 as users.
- Nits:
  - N-1: "at every point of D(k)(iii)'s ω-polydiscs, R(w(s,t))ω included" is now in the 4.2(iii) and 4.5 bodies.
  - N-2: "touched" is in 4.3's label; untouched members are evaluated at (U_{k+1}, ω) (D2.2(4)(e)).
  - N-3: 4.1's body now uses (2.7)'s second line with m = k, n = k+1. This gives R_k < L(1+β₀)R_{k+1}, so 6LMR_{k+1} > 6MR_k/(1+β₀) ≥ M₁R_k for β₀ ≤ 5 and M ≥ M₁ (read in CRE p.255).
  - N-4: "R-ζ(a) beyond Ω_{i+1}^∼" is in 4.5's label.
  - N-5: in map D2.1(4) *Conditions used*, C₄ is now C₄^{RG2}, with a note that the unmarked C₂ and ε₂ are RG2's.
- Not supplied to the reviewer: the lift-freeness of (T2)/(T3) (§5.2–5.3). Unchanged.

## s7 (§7)

Verdict: "correct and sufficient for its stated purpose", with O2, O2′, O3, O4 and O6 open; M1, M3 and M4 correctly repaired. No fatal or serious item; minors m1 and m2; nits n1 to n5. All repaired.
- m1: the complex δℓ tilt mark is now stated as 𝔪^δ_Y ≤ C^δ_bdρ₁ϑr²Σ_{b:Y_b=Y}Σ_{e∈J_col(Λ)}e^{−μ_xd(b,e)}, with C^δ_bd built from C_δ at (2C_m, μ_x). The source is IT-1 §3j(6) *Thresholds*, l.1757, read. The round-27 citation of l.1125 was the pre-m̂ form, at rate μ_H over J₁(Λ). The text also records that this is the frozen-centre mark: if O4 closes by a host tilt, this term of C_h and K₁'s condition are to be re-checked.
- m2: bond marks, and with them the host-cutoff pieces, are now anchored at the nearest point of J_col(Λ). J₁(Λ) ⊆ J_col(Λ), so the bound holds at real data, and C_{μ/2}, C_{μ/4} are sups over all bonds. The complex-data bond-mark bound in the J_col form is recorded under O4.
- n1: the N′ part of each piece uses the first assertion of Lemma c5-5-7z(b), with the fixed insertion N′_{s,b}, whose norm (a) bounds by N_trC_linkg₀.
- n2: the pieces are one per pair (W, b), all anchored at b.
- n3: the b_W decay is stated as the weighted sum Σ_{W∋n}K_χe^{θ°}𝔡⁰_We^{c(d(n,b_W)−1)/(LM)} ≤ Cρ̂, restricted to b_W ∈ 𝔅_Z.
- n4: in the inputs bullet, the support is within R_t of J₁(Λ) at real data and of J_col(Λ) at complex data, with the same conclusion.
- n5: §8's *For the user's review* item now names the J_col anchors, the b_W rule and the per-(W, b) split. The *Reviewed* line adds rounds 27 and 28.

## Status after round 28

Open, unchanged:
- O6: the localised terms with Y ⊄ Λ_{k+1} at complex σ_k. Its consumers now explicitly include the ω-dependent wrap(j) members of step ≥ 2.
- O2, O2′, O3 and O4. O3 now explicitly covers the ω₀- and ω₁-factors of §4.5 at every k.
- D2.7.

O1 is derived given R-ζ(b), R-h and R-ζ(a) beyond Ω_{i+1}^∼, for re-review.

## Class sweep (after the repairs, 25 Oct, at the user's request)

Each round-28 finding was treated as a class. I grepped the closure and the map for every other place where the same object or label occurs.
- **O3 scope.** O3 is used at every k by the factors meeting Ω₁∖Ω₂, not only at k = 1. Widened in:
  - §0 *Not D2.6's*: §3 at k = 1; §4.2(iii), §4.5, §5.1, §5.3 and §6.4 at every step;
  - §6.4 *Carrying*: "at n = 1, and at every later n where Y_i's evaluation domain meets Ω₁∖Ω₂";
  - §8 *Derived*, the §6.4 entry;
  - the map's D2.6 status paragraph and D2.2(4)(f)'s propagation sentence.
  §3's k = 1-only statement is correct as it stands: its comparison layer is Ω_k∖Ω_{k+1}.
- **ω-dependent members and O6.**
  - Register rows R4 and R7 had no qualifier. They now name O6 (members of step ≥ 2) and O3.
  - R1 now says that O6 concerns the ω′-dependent groups only.
  - §8 *Derived* now lists §4's exceptions.
  - §4.2(iii) class (2) is made exact: D(1)(iii)'s analyticity is derived at k = 1, and its bound clause at complex ω₀ is 5.0's for-review amendment. Only the lw bound is derived (§6.1).
  - The map's D(k)(iii) *Outer fluctuation fields* now carries a status note with the same split.
  §2.1(e), §2.4, §5.3 and the 7.1 label were checked and are correct. 7.1's O6 for att(j, Z) at j ≥ 2 stands, because later descendants of att(j, Z) can sit in groups with ω′ ≠ 0.
- **ω′-free groups.** §2.2's *rooted sum* heading put every group of the re-run on O6. It now says that the qualifier concerns the ω′-dependent groups, not 4.3's (ii)-only groups. No other place applied the "whole gas" reason.
- **J₁ anchors and stale citations.**
  - 5.6's anchor list now names J_col(Λ).
  - O4's "what closes it" now localises the constant near J_col(Λ), where the δ-term decays (6.3(d)).
  - The other J₁(Λ) uses are real-data statements and are correct: 6.1's support, 6.4's real tilt, 7.1's V3 forms.
  - l.1125 now appears only in the round-28 note.
  - The other (2.9) uses are legitimate (R_m ≤ (L+1)(n−m)^{β₀}R_n).
- **Constants.** 4.2's VAR paragraph now writes "VAR's C₁ (= C₁^{VAR})" and "VAR's C₁, C₄, …". The map's RG2 marks were done under N-5.

S-B was a relabel, and m-D′ withdrew an over-conservative qualifier. A round-29 s4 packet would check the three-class split of 4.2(iii) and the m-D′ argument. Not launched: only if the user asks.

## History strip of the closure and the map (25 Oct, finished 13:58 GMT)

User: "Strip the repair history from the D2.6 closure and the step map, keeping only current content and status labels; the triage files keep the record." Times, dates, review IDs, round numbers, packet logistics and "withdrawn/former/superseded/retired" prose are removed from both files; status labels (derived, OPEN, reading, for review, amendment, reviewed / not reviewed), citations and l./L pointers are kept. Superseded paragraphs are restated in their current form; dead routes get one "doesn't work" line; base text corrected later reads "(14)(x) corrects it". The map keeps exactly 1670 lines (LF), so every l.NNN pointer still lands on the same item. Backups of the pre-strip files: PRE_STRIP_BACKUP_2026_10_25\.

Content changes (beyond deleting history):
- Closure: 5.5 c_W → c_W^{chg} for fixed members; §3's c′ note dropped; present-tense reasons in 2.3, 5.2, (T3), 6.1, 6.2, 6.4, 6.5; §8 *Reviewed* is one pointer line to R20–R28; §9.3 "OPEN cubes" → "crossing cubes"; R-reg2/R-run notes dropped; route (b) "(not needed; route (a) is derived)"; O5 "derived in §6.4 (for review)"; O6 paragraph says the map's D2.2(6)(e) (l.958) puts the σ_j-analyticity of 𝐏^{(j)}, V^{(j)} under O6.
- Map: (Z-d) carries the cluster weights and G = 2, its rooted sum closed in (Z-f); the (TC) route has one "doesn't work" line; C_rel ≤ max(C_rel^{(1)}, 2C⁎); (T) is "not used" throughout, (T′) in its place; stale rate values updated to η_w = (5/16)η_V, ν_e = η_V/(2C_box), C_box ≥ 4A_E, L₀ = 5000; D2.4(7)(R) restated in the cluster form; D2.4(8)'s transport condition c_πα_{1,k+1}M ≤ ν/64; D2.4(9) and (12)(f) *Uniformity in k* given their current status; (12)(c)–(f), (13)(b)–(c) headed "(14)(x) corrects it"; (13)(d) is the pointer "(14)(h)" (its stale list had L₀ = 4600, (7/8)η_V); (13)(c)'s step-1 base points to (Z-h) (derived), not "OPEN as before"; status line l.199 now says V^{(j)}'s σ_j-analyticity is part of O6 (it said "analytic", which l.958 and closure §2.2 (1′) contradict); the "not in the review packets" remarks became "not checked here".

Hashes 13:58 GMT: closure c0beb784145d → be0fcee52e9c (177 lines), map 7095c7cd7194 → 9a6f1a5bc40d (1670 lines).

## Merge of D2.4(14) into D2.4(12)–(13) (finished 14:22 GMT, 25 Oct, date; user: "rewrite D2.4(12)(c)–(f) and (13)(b)–(d) in their corrected form from (14) … drop the 'corrects it' headers, and reduce (14) to what is new")

Backup before the merge: PRE_MERGE_BACKUP_2026_10_25/ (map, closure, SW closure). (14) had nothing that was not a correction of (12)–(13), so it is gone entirely; (12)(c)–(g) and (13)(c)–(d) are written in (14)'s corrected form, (12)(a)–(b) and (13)(a)–(b) keep their text with refs renamed.

Label map: (14)(a), (b) → (12)(c) (*Links* as an inline paragraph); (14)(c) → (12)(d); (14)(d) → (12)(e) (with the vacuum sum and the box reduction); (14)(e), (f) → (12)(f) (*Uniformity in k and (S-w)* inline); (14)(g) → (13)(c); (14)(h) → (13)(d); κ_s^{(14)} → κ_s^{(12)}. Old (12)(g) rewritten as *What Step 3 gives and leaves*; the (13) heading now says (c)–(d) not reviewed.

Content changes found while merging:
- sh(M): (14)(c) printed 21ν_f#(M) while using the 41 windows; corrected to 42ν_f#(M) + ν_e(42#(M) + 83) + ….
- c_W := 2ν_f(16 + 10240/L + 41/M) + 2ν_e(2 + 41/M): doubled to include the ℓ_X factor.
- L₀ = 5000 checked: the bound needs L ≥ 4608.
- (13)(a), (13)(d): the entropy is paid against r/648 and κ_s/4 (the other halves are the charges of (12)(d)), not r/324 and κ_s/2 as the old (13) text said.
- (T-dev)'s consumer list: merged (12)(f) gets c_W = 0 at the reference point from f(0) = 0 (D2.3(3)), not from (T-dev); map l.1355 and closure §9.4 corrected (the CMP98 (42)–(43) pin there dropped with the claim).
- Map l.1496: the transport condition is (12)(d)'s c_πα_{1,k+1}·41M/L ≤ ν_r/16 (was 20M/L).

Line numbers: map lines 1–1522 keep their numbers (39 of them carry renamed refs only); the region from l.1523 is shorter (map 1670 → 1614 lines). Closure pointers repointed: l.1625 → l.1547 (window), l.1638 → l.1571 (rooted at an old vertex), l.1603 → l.1593 ((13)(a)), l.1669 → l.1614 ((13)(d)), l.1556 → l.1531, l.1551 (ν_e ≤ ν/8), l.1589, l.1630 → l.1559, l.1576 (box reductions). SW closure: refs renamed, (10)–(14) → (10)–(13); no line pointers. RC_PAYMENT_PASS and LINE_DEFECT had no D2.4(14) refs. Citation tokens checked against the backup: none lost, only duplicate counts down.

Hashes 14:22 GMT: map 9a6f1a5bc40d → 323bc8f940b4 (1614 lines), closure be0fcee52e9c → ab8599f86f84 (177 lines), SW closure a1991529cbc8 → 04a41c349c24 (106 lines). All LF.

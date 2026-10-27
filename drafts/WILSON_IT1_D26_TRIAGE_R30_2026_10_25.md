# D2 map: triage of round 30 (it1-d2-4s12s1-20261025-r2, it1-d2-4s13sa-20261025-r2; both reports read in full; repairs finished 22:0x, 25 Oct, date)

Round 30 re-reviewed the two serious round-29 repairs (WILSON_IT1_D26_TRIAGE_R29_2026_10_25.md):
- S1, the linked hull, in packet 4s12s1;
- S-A, the weighted difference count, in packet 4s13sa.

Both ran on claude-opus-5-5 through the CLI route, 18:35–18:48. No fatal item. One serious item, S-1 in 4s12s1, is repaired below.

## 4s12s1 (D2.2(6)(d), D2.4(12)(c)–(d))

Verdict: "not yet correct and sufficient as written". The arithmetic of (12)(d) was verified throughout: n_{k+1}(M), sh(M), sh(W), c_sh, L₀ = 5000, the 4096 condition, and both budgets. The design repairs the round-29 defect, but one reading of "pieces" breaks the covering lemma.

- **S-1** (the piece of a touched insertion). If I_{W₀} is the piece of X_{W₀}, the hull adds a gap that Lemma (2) does not control. The reviewer's counterexample has I(M) longer than |C|/2.
  - Repaired as proposed: in D2.2(6)(d), the piece of every constituent of a marked polymer's vertex (M, each touched W ∈ 𝔅(M), each assigned cluster) is I(M). A touched interval is not a separate piece; it lies in I(M) by (4)(e).
  - The pieces now list *untouched* old insertions. The second rule's pair is with an untouched insertion.
  - Lemma (3)'s pair note says the M-vertex's constituents all have the piece I(M).
- m-1: tie-break for equal arcs (C's orientation from the earlier piece).
- m-2: a scalar link T is assigned to its first M, and a vacuum occurrence to the first M of S_𝔐(𝒞). So the assignment depends on T, not on the unexpanded clusters of e^{x_T} − 1.
- m-3: "connected by overlaps" is now derived. The groups of 𝔊(𝒮) are scalar-link components (D2.2(6)(c), l.888, checked). Every other membership comes from a joined pair, an arc overlap, the hull rule or a touched insertion inside I(M).
- Q1 (order independence): one sentence added to *Second rule* (the least structure closed under the rules).
- m-4: Lemma (3) now covers incompatible members of one occurrence. They are internal to the Γ-vertex and covered by (2) member by member.
- m-5: Lemma (2) now names the other two kinds of hit: by arc overlap ((iv′) directly), and through the member's own occurrences (reduced to contact or overlap).
- m-6: diam(S_M) ≤ M#(M) + 2max_W(diam_W + |int(W)|). Also stated: diam_W ≤ (M/L)#_k(W) (connected support of #_k cubes meeting the interval) and |int(W)| = n_k/L, so diam_W + |int(W)| ≤ (M/L)σ_k(W). The 48, and hence the reserve budget, stand.
- m-7: (12)(a)'s #_{k+1} list includes the supports of the vacuum-link clusters. Their share ν_f#(𝒞) is already paid.
- m-8: the per-piece constant is C_pc := 483C_τmax(C_τ, C_ℓ). An M or 𝒞 piece takes C_τ², and a W piece C_τ·3C_ℓ. (12)(e) uses C_pc′ := C_pce^{40c_πα} per piece.
- m-9: the L₀ remark cites 8(1+β₀)^{15} ≤ L (8·1.5^{15} < 3504).
- m-10: "linked by construction".
- m-11: arc C is handled by l.488: such a group is alone in its family, with term dim(π)^{−1}tr Y_G. This is cited at the hull definition.

## 4s13sa (D2.4(13)(c), D2.3(4)(Z-e), (Z-h))

Verdict: correct in substance, and S-A repaired. Input and output match at traversals, the Γ part is produced, and the recursion closes. Not yet sufficient in one respect (m-A). No fatal, no serious.

- m-A (cube clause of the carried insertions):
  - The inductive clause ε^{diff}_k is now taken over traversals only, in (13)(c) and in (Z-e)(I).
  - At π_k-cubes the sums are derived afresh at each step by (12)(e)'s box reduction, with weight e^{θ+ν_rσ+(3/4)ν_e·ext} and constant C(M/ν_e²). This still contains sh + b, whose extent part is (3/8 + 1/L)ν_e·ext.
  - The new objects at cubes come from (12)(f)'s cube-rooted count.
  - ε̄^{diff}_k := L⁴C(M/ν_e²)K₀ε^{diff}_k. The bracket term of the recursion gains C(M/ν_e²) and is still ρpl-small, so the contraction ¼ is unchanged.
  - At step 1, (c4-6-5) holds per cube, so (Z-h) is direct at cubes.
- m-B: (Z-h)(I)₁ now states the group part (c_W with (c4-6-5)'s c-version). (O)₁ fixes a° := (ν/32)σ₁ and ≤ 81Mσ₁ positions.
- m-C:
  - d(𝒢) gains log C_pc′, the per-member factor of a Γ-vertex's C_v.
  - The KP check and the chain carry C_pc′.
  - K₀ := (1 + 2e)e^{2c_sh}C_pc′ (n-5's redundant factor is removed).
  - ℓ_X ≥ 1 is cited ((4), l.1320).
  - (Z-e)(O) is updated to match.
- m-D: (Z-e)'s *Carrying* paragraph now cites D2.4(13)(c)'s marked tree sums, with no n_ins factor and no reserve in a°, and the recursion ¼e^{−c(L−1)ι}C_rel + C⁎. (Z-d)'s matching sentence on n_ins was changed the same way; a_min stays recorded with the root sum (13)(b).
- m-E: (Z-h) is relabelled "derived … given one structural input, for the user's confirmation against V3 Sect. c4-4". Item (i) of the gaps block closes with that confirmation.
- The (I)₁ absorption, flagged UNSUPPORTED:
  - The text now shows the margin. (12)(b) *Base* bounds the full weight with complex data by e^{(59/16)η𝔰} (its split 1/16 + 1/8 + 2 + 1 + 1/2), leaving e^{(5/16)η𝔰}.
  - The polynomial (k+|F|+1)² is ≤ (C_M𝔰 + 1)² ≤ C′e^{(5/16)η𝔰}. Here k is the carrier size and |F| ≤ k the forest edge count; V4 L2176–2186 was read for these, and V4 is unchanged.
  - The tail clause (ii-t), which spends that margin, is not used here. C_rel^{(1)} now depends on M.
- m-F: (13)(c) says that sup|ΔY_W| is taken over the complex data as (12)(e) takes ε^{old}: (5)'s size O(ρ_k·pl) away from older layers, with SW closure §3, and the constant in C_rel.
- m-G: (13)(c) records two facts:
  - (12)(b) *It carries* (l.1534, read) uses only weights, positions and normalisations, and an old W keeps σ, ext and θ;
  - a carried W's sup|ΔY_W| at step k+1 equals its step-k value, since the agreement radius ι_{T,k+1}/4 step-(k+1) units is ι_{T,k}/4 step-k units ((Z-e)(c)).
- n-1: the mark hypothesis form (Σm·e^{b/2} ≤ (ε_m/ε_*)b/2; be^{b/2} ≤ (2/e)e^{b}) is stated.
- n-2: "at p".
- n-3: a vacuum cluster's dependence set lies within R_D of its support ((Z-g)'s margin).
- n-4: "clusters of dependence diameter ≥ ι_{T,1}/4 do not embed".
- n-5: see m-C.
- n-6: no change. ε̄ is conservative, as noted.

## Next

Round 31 re-reviews both packets as r3 (S-1 was serious; the S-A residues added new constants), using build_round30 with r3 revisions.

Hashes:
- map 1614 lines, hash after the last edit recorded in SESSION_HANDOVER.md;
- V4 b35c60e537b8, unchanged.

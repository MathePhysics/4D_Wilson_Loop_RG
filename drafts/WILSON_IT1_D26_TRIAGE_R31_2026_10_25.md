# D2 map: triage of round 31

Reviews read in full:
- it1-d2-4s12s1-20261025-r3 (S1: D2.2(6)(d), D2.4(12)(c)–(d));
- it1-d2-4s13sa-20261025-r3 (S-A: D2.4(13)(c) with D2.3(4)(Z-e), (Z-h)).

S-A verdict: correct and sufficient, with one minor item (r-1) and nits n-a to n-e. S1 verdict: with N-1's one-sentence repair, correct and sufficient.

All edits were made in WILSON_IT1_D2_STEP_MAP_2026_10_22.md with Edit. The map still has 1614 lines. The closure is unchanged (177 lines). V4 b35c60e537b8 is unchanged.

## S1 (it1-d2-4s12s1-20261025-r3)

- **N-1 (serious; regression from the round-30 S-1 fix).** The round-30 fix restricted the second rule to untouched old insertions. A constituent domain incompatible with a touched W ∈ 𝔅(M′) of another group was then left unmerged. The rule is restored for every old insertion, touched or not:
  - joined pairs: "a constituent domain is incompatible with an old insertion's domain, touched or not (second rule; the pair is formed between the two constituents' pieces, I(M) for a touched W ∈ 𝔅(M))";
  - *Second rule*: "every old insertion W, touched or not, … a touched W ∈ 𝔅(M) of another group carries that group with it";
  - *Class form*: "a new constituent with an old insertion, touched or not, by the second rule".
  - The reviewer's covering check (§2) applies: the pair is one more (ii) pair, since X_{W₀} ⊂ supp v_M.
- **m-a.** (12)(c)'s assignment is aligned with D2.2(6)(d). A pair (T, 𝒞) lies in 𝒱(M_T), where M_T is the first M of T in one fixed order. A vacuum occurrence 𝒞 lies at the first M of S_𝔐(𝒞).
- **m-b.** "Earlier" is defined: the piece that comes first in a fixed order of the pieces, e.g. by its first bond along C from the base point.
- Uniqueness of 𝔅(M) is D2.2(4)(e)'s structure (not supplied to the reviewer). The reviewer notes that either choice satisfies Lemma (2). No change.

## S-A (it1-d2-4s13sa-20261025-r3)

- **r-1.** (13)(c) now states the inductive statement explicitly: ε^{diff}_k, the derived cube sums and (O)_k at every position are bounded by C_rel^{(k)}e^{−cι_{T,k}}ρ_k·pl_k.
  - It defines C_rel^{(k+1)} := ¼e^{−c(L−1)ι_{T,k+1}}C_rel^{(k)} + C⁎.
  - It concludes ε^{diff}_{k+1} ≤ C_rel^{(k+1)}e^{−cι_{T,k+1}}ρ_{k+1}·pl_{k+1}. It also concludes δ_{k+1} ≤ the same at every step-(k+1) position, cubes included, because δ_{k+1}'s bound does not depend on the position.
  - The cluster-level line cites this bound.
  - No constant changes.
- **n-a.** The rate of (Z) is renamed c^Z := min(c₁, ν/(512M)), independent of k. The occurrences changed are:
  - D(k)(vi)'s (Z) clause;
  - (Z-d) and its torus remark;
  - (Z-f)'s display and limits;
  - D2.0(6)(a) and its sum;
  - the D2.3(5) bent-path line;
  - (13)(c).

  The rate of the relative clause is c_k = c of (13)(c). (Z-e)'s "c_{k+1} ≤ c_k" now refers to that rate only.
- **n-b.** (13)(c) adds that each unmarked factor in the telescoped products is bounded by |c^T| + |c^{T′}|. This doubles the rooted sums, so (12)(e)'s condition and the KP check hold with the factor 2 for g_K small.
- **n-c.** In (Z-h), the polynomial (k_W+|F_W|+1)² now sits inside the sum over W. The absorbed polynomial is 𝔰³(C_M𝔰+1)² ≤ C′e^{(5/16)η𝔰}. C′, hence C_rel^{(1)}, depends on η and C_M.
- **n-d.** Two additions to (13)(c):
  - The "*Used, not derived here*" list now names (12)(b) *It carries* and SW closure §3 (for review).
  - (13)(c) states that its sup form is the inductive clause and implies (Z-e)'s relative form, so (5)'s conversion constant is applied once and not iterated.
- **n-e.** The packet's claim field described the round-29 forms. This is a packet artefact, so no text change.

## Next

Round 32 re-reviews S1 only, as r4, because N-1 was serious. S-A was found correct and sufficient, and its round-31 edits are the reviewer's own wording.

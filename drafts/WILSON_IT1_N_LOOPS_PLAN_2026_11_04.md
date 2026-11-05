# Extension of the Two-Loop Bound to n Loops: Plan (4 November 2026)

Status: step 1 (the adversarial pass) done, with no real entry; step 2 (the n-loop note) done: WILSON_IT1_N_LOOPS_UNIFORM_BOUND_2026_11_05.md, derived, not reviewed; its review packets come after the two-loop queue. Nothing below
is derived. The source is the two-loops note
WILSON_IT1_TWO_LOOPS_UNIFORM_BOUND_2026_10_27.md (cited by section and tag), and the target is the n-loop analogue
of its K-uniform bound (8.2) for n disjoint loops C_1, ..., C_n.

## Assessment

The extension is moderate: mostly bookkeeping, with no new analytic input identified. The number two enters through
the class (2), the cross groups (6), the two-component reading (6A), the merge rule (R-member), and the count (7).
The analytic inputs act on one insertion, word, or chain at a time and do not see the number of loops.

## What Carries Over Unchanged

- The R-step inputs: (R-eval) with (R-eval-old) and the G^c transformations, (R-eval-cr) {#220}, (R-round) {#234},
  and (R-att-ext) {#274}.
- The large-field note and its response bounds (peer-owned, read only).
- The doubly exponential decay of cross groups. A group touching r >= 2 loops spans at least D L^{K'-k}, with D the
  smallest pairwise distance; a group touching more loops spans more.
- The common stopping step and the normalisation. K' uses the largest of the q_i and the pairwise q_ij, and
  kappa^{(K')} factorises because perimeters add.
- The pair identity (8.1), which becomes a product of n factors with |beta| <= Sum_i |beta^{(i)}|.

## Work Items

1. **Setting and class, (1)-(2) ({#330}, {#356}).** D becomes the smallest pairwise distance. Each of the 28
   occurrences of "both loops" and the 10 of "3−i" becomes a statement about all loops or the other loops. Each
   occurrence is checked, not substituted.
2. **Cross groups, (6) ({#459}).** Label cross groups by the subset S of loops they touch, |S| >= 2. A cross group's
   flat value lies in a tensor product of |S| End factors. The note sets cross flat values to 0 and never contracts
   them, so no new algebra is expected; confirm that no step uses |S| = 2.
3. **Two-component reading, (6A) ({#503}).** Replace "the complement of one loop is the other loop" by the
   n-component decomposition. This is the main risk: a line-by-line pass lists every use of two components.
4. **(R-member) ({#241}).** The merge rule already handles insertions with several intervals. Recheck u = 19, C_y,
   and L_0^× = 10^6 with n loops. If u grows with n, L_0 depends on n, which is allowed (large L).
5. **Count check, (7) ({#874}).** The real work. Recount A^×, E*, and w-bar as count × size × weight per scale, with
   a choice of the subset S for each cross group. Expect n-dependent constants and Sum_i l_i in place of l_1 + l_2.
6. **The bound, (8.2) ({#907}).** Restate with Sum_i l_i, the largest C_chi over the characters, and the new A^×.
7. **First step, V4 Section 10.** Generalise thm:two-loop-theorem and lem:two-loop-retreated in the same way.
8. **Limitations, (9) ({#938}).** Factorisation for large D and convergence along the full sequence stay open, as for
   two loops; (9) carries over with n in place of 2.

## Order of Work

1. Adversarial pass over (6A), (7), and (R-member): list each place where n enters and each step that uses "two".
   Output: a short list in this file, each entry marked harmless, bookkeeping, or real.
2. If the pass finds no real entry: write the n-loop note as a new file with its own tags, items 1-6 in order,
   then item 7 in V4 Section 10, then item 8.
3. If the pass finds a real entry: repair it first, by a better choice of decomposition or gauge before any new
   estimate.

## Adversarial Pass (Step 1): Entries

Each entry names where N_C (the number of loops) or "two" enters, with its mark. No entry is real.

- (6A) u_1 = 1 + 4/M + 48/L (#530-#532): at most |W| intervals per loop met, two partial bonds each. Becomes
  1 + 2N_C/M + 16(N_C + 1)/L. Bookkeeping; L_0 = L_0(N_C).
- (6A) C_win^x and the window ends (#557, #558, #568): 2N_C ends in place of 4, so C_win^x ≤ 98N_C u/c_w.
  Bookkeeping, absorbed by g small.
- (6A) shares (#571, #572): per-loop sums of pieces; the factors 16 and 6 are per group (below). Bookkeeping.
- (6A) arc choices: n^{2r} choices of 2r arc ends become (N_C)-fold per end. Bookkeeping, a constant per unit.
- (6A) c_C and a_k: at most N_C-fold sums of the single-loop terms. Bookkeeping.
- (6A) base points: ordered C_1, ..., C_{N_C} in place of C_1, C_2. Harmless.
- (6A) D2.5 covariance: ⊗_i V_{π_i} over the loops. Harmless.
- (6A) #598's 5diam(S): independent of N_C. Harmless.
- (6A) #575-#578 M-vertices: n_{k+1}(M) ≤ 20N_C M#(M) + 48N_C(M/L)Σu_Wσ_k(W), and the coefficients 282, 441, 22,
  164 of #578 become about 141N_C, 221N_C, 11N_C, 82N_C. The cube cost of #580 is paid against r/648 > 182, so it
  is harmless. Keeping #580's 7.6, and so the bracket within κ_s^{(12)}'s constant 9, needs
  (N_C/2)(283ν_f + 441ν_e) ≤ 0.383, with ν_f = 17ν/16 (map l.4257) and ν_e ≤ ν/8. Constant level: holds for
  ν ≤ 1/(500N_C) (left side ≤ 0.356), the map's ν ≤ 1/1000 at N_C = 2; #581's 0.045 then holds too (≤ 0.044). The map's other conditions on ν (#MD2.4.13.19 to
  #MD2.4.13.19-6) are upper bounds or smallness of g after ν (c_πα_{1,j}·4096M ≤ ν), so a smaller ν is free.
- Notation: N_C, not n_C, since the map's M ≥ n_C + 2 (#MD2.4.13.19) uses n_C for C's range of blocks.
- (6A) #524 connectedness: E_D is the cubes meeting the dom P of g's polymers, which form a connected union since g is
  linked, plus the arcs H_i(g) for each loop with ℐ_i(g) ≠ ∅, each meeting some dom P through ℐ_i(g). Harmless;
  "both loops" becomes "each loop the group meets".
- (R-member) u = 19: 18.05σ per cross insertion, 16 per single-loop group, 6 per cross group. Each is per insertion
  or per polymer, not per loop. Harmless.
- (6B) *The count* u = 6 (#716, #720): sums over the polymers of g and their members. Harmless.
- (6C) u = 16 (#830): per group. Harmless.
- (5) E^x: log S° − Σ_i log S°_{C_i}, with δ_b the distance from b ∈ C_i to the union of the other loops. The
  allocation, cancellation, and bound go through per traversal. Bookkeeping: ℓ_1 + ℓ_2 becomes Σ_i ℓ_i.
- (6) cross species: cross(j) labelled by the set S of loops met, |S| ≥ 2. Production is pinned at a traversal
  with δ_b ≥ D, so no subset factor enters. Flat values are set to 0 and never contracted. Harmless.
- (7) A^x, E*, w-bar: per traversal or per loop, summed. ℓ_1 + ℓ_2 becomes Σ_i ℓ_i; C_Σ(χ_1) + C_Σ(χ_2) becomes
  Σ_i C_Σ(χ_i). Bookkeeping.
- E^{R x} (6B): inclusion-exclusion, log Ξ^c_{[n]} − Σ_i log Ξ^c_i + (N_C − 1)log Ξ, leaving the clusters that
  meet at least two loops; each such cluster is a cross cluster and has the pair bound. Bookkeeping.
- V4 Section 10, lem:two-loop-pins(b): 𝔰(γ) sums the hulls over the squares, so 𝔰(γ) ≤ (1 + N_C A_h)n_γ, and the
  condition on η becomes 1000ηA_s < ϖ/(4N_C) (#NL9.6-4a). A constant fixed before the coupling. Harmless.
- The n-loop note's packets, with scopes in reviews\work: scope_nloops_NL1.md (§§1–4), NL2 (§§5–6B), NL3 (§§7–8),
  NL4 (§9, V4 Section 10), NL5 (§§10–12).

## Review Plan

- New packets, two clean rounds each: (2); (5)-(6); (6A); (R-member); (7); (8); V4 Section 10.
- No new rounds for the R-eval packets, (R-eval-cr), (R-round), or (R-att-ext); the n-loop note cites them.
- Referees run one at a time after the two-loop queue (C1, C2a4, C2b8, A9, B2, E1e, P2, P1, 2b, 2), so they do not
  compete with it.

## Main Risks

- (6A) uses "two components" in a way that does not generalise.
- (7) acquires a combinatorial factor in n that is not absorbed by the doubly exponential decay at the given L_0.
- (R-member)'s u grows with n faster than the large-L freedom absorbs.

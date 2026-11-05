# Extension of the Two-Loop Bound to n Loops: Plan (4 November 2026)

Status: proposed, not started. Nothing below is derived. The source is the two-loops note
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

## Review Plan

- New packets, two clean rounds each: (2); (5)-(6); (6A); (R-member); (7); (8); V4 Section 10.
- No new rounds for the R-eval packets, (R-eval-cr), (R-round), or (R-att-ext); the n-loop note cites them.
- Referees run one at a time after the two-loop queue (C1, C2a4, C2b8, A9, B2, E1e, P2, P1, 2b, 2), so they do not
  compete with it.

## Main Risks

- (6A) uses "two components" in a way that does not generalise.
- (7) acquires a combinatorial factor in n that is not absorbed by the doubly exponential decay at the given L_0.
- (R-member)'s u grows with n faster than the large-L freedom absorbs.

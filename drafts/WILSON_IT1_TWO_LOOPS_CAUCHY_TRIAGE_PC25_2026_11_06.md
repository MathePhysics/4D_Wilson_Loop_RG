# Pair note triage: PC25 (R-step booking and totals, full round)

Note: WILSON_IT1_TWO_LOOPS_CAUCHY_2026_11_05.md, owned by the two-loops session.
Reviewed SHA: dfc8ee5b72bc, with the two-loops note at 4b0b4faae66c (both frozen during the round). Repaired SHAs: pair note 1a74f6e56213 (83,566 bytes; was 83,226), two-loops note 6b3d1f0d7c47.
Referee: referee_cli_20261106-152111_scope_pairCauchy_PC25.json (opus-5-5, $4.76), section in reviews\REVIEW_LOG.md. The referee ran no shell command.
LF pin: 640c0fddd9ad at review, now 462dc146eba3 (checked by hash; the changes are in LF #4.43 and #4.45, not cited). Table 88a6dcbd277a. D2.7 55e50090afd6.

## Verdict

No ERROR, three MINOR findings, and the numbers stand in all three, so the round is not clean. PC24-1 and PC24-2 are resolved.

## Repairs

| Finding | Severity | Repair (in place) | Lines |
|---|---|---|---|
| PC25-1: "costs log 2" is right for the block but not for the word pieces, which are many insertions; doubling each turns their cost e^S into at most e^{2S} | MINOR | -4.5.4-3-1: the block's doubling costs log 2; each word piece is doubled, so the cost e^S (S the sum of their masses) becomes at most e^{2S}, again of 15.8(c)'s form (d'-part paid by kappa_k(Y_i)'s p0^2(g_k)(d'+1) term, constant part a polylog of order at most r(d+1) < p0), which 15.8(c)'s margins absorb for small g_k | #PC4.14.4-4.5.4-3-1 |
| PC25-2: 15.4(iii)'s terms of E^{R,∂}_k(ℓ) are numbers of the labelled term, as D26 7.4(a)'s E^∂ are, yet PC24's own repair had made them productions (carriers) without weights, end or payment | MINOR | the PC24 own repair is reverted in -4.5.4-7, -4.5.4-8, -4.5.4-9 and -4.10.1; the new -4.5.4-7-1 states that they are numbers attached to one component as D26 7.4(a) attaches E^∂ (7.4(b)(ii): "the e_X are numbers"), so they enter no activity, no c^a and no N, as E^∂ at the T-steps (#PC4.14.4-4), D2.7 paying them within Res (15.8) | #PC4.14.4-4.5.4-7, -4.5.4-7-1, -4.5.4-8, -4.5.4-9, -4.10.1 |
| PC25-3: two-loops #815's "mass at most 4C_Psi''" bounds the exponent 2 Sigma abs(d_c), not the D26 5.0 mass of the insertions e^{-d_c} - 1 | MINOR | #815: insertions e^{-d_c} - 1 with Sigma_c abs(d_c) at most 2C_Psi'' (15.6(d)); carried with the factor 2 their mass is at most m_Psi := 2(e^{2C_Psi''} - 1), and they cost at most e^{2 m_Psi} at every later step, a slot's e^{2 Sigma A} included; #817's E(Y_i) uses C_Psi'' + 2m_Psi, and its margin p0(g_k)/32 holds for small g_k, both being constants | two-loops #815, #817 |
| LF pin | bookkeeping | 640c0fddd9ad replaced by 462dc146eba3 | #PC.1-1.2 |

## Pre-check

- D26 7.4(b)(ii) re-read (D26 l.150: "On a labelled term ℓ the e_X are numbers (D2.3(8), D(k+1)(v)), each attached to one component (7.4(a))", paid with 13^d m_n per cube). D2.7 15.4(iii) (l.173) attaches its cluster terms "as D26 7.4(a) attaches E^∂_{k+1}(ℓ)", and 15.8 (l.191) pays them "within Res". So they are numbers of the term and enter no activity; LF counts them in Y-bar^R_X for #5.42's local terms, which is LF's and consistent.
- D2.7 15.8(c) re-read (l.191): the constant parts 4C_alpha(MR_k + 2M delta^{-1}) delta^{-1} and the weights are "polylogs of order at most r(d+1) < p0", joining "the left side of the last inequality, which still holds for small g_k"; the d'-parts are paid by kappa_k(Y_i)'s p0^2(d'+1) term with a larger O(1). Doubling S keeps both forms.
- #815 arithmetic: abs(e^{-d} - 1) at most e^{abs(d)} - 1 for complex d; Sigma_c(e^{x_c} - 1) at most e^{Sigma x_c} - 1; so the mass is at most e^{2C_Psi''} - 1, carried at most m_Psi; the product Pi(1 + 2 abs(p_c)) is at most e^{2 Sigma abs(p_c)}, at most e^{m_Psi}, and a slot's e^{2 Sigma A} at most e^{2m_Psi}. E(Y_i) pays once, as before (flat part C_Psi'' plus the dev part's 2m_Psi).
- Grep: no 4C_Psi'', 8C_Psi'' or 9C_Psi'' left in the two-loops note; the pair note does not use C_Psi''. D2.7 cites #815 and #817 by tag.
- labels_pair_cauchy.py: 322 tags, all checks pass; labels_two_loops.py: 1005 tags. Changed lines at most 553 characters (-4.5.4-3-1), #815 at 558. LF line endings in both.
- Sent to the LF session at 15:43 GMT: LF #5.39-3-1's "the q = 0 dev parts are at most 4C_Psi'' per Y_i" becomes m_Psi, with 4C_Psi'' in eps^R_A replaced by m_Psi; eps^R_A keeps its form.

## Handover

- 2026-11-06 15:43 GMT: PC25 triaged and repaired; pair note 1a74f6e56213, two-loops 6b3d1f0d7c47. PC26 (full round) next; scope_pairCauchy_PC26.md written.
- 2026-11-06 (later): the LF session re-derived and agreed to m_Psi and to PC25-1 and PC25-2. Its LF #5.39-3-1 and #5.39-3-3 edits (4C_Psi'' becoming m_Psi) are queued until its 12a r1b round reports; LF stays at 462dc146eba3 meanwhile. D2.7 needs no change. PC26 waits for those edits, since #PC4.14.4-4.12.1 reads LF's eps^R_A and launching against the old value would put a known mismatch into the round.
- 2026-11-06 16:16 GMT: LF now 98afdbda7e48 (checked by hash; D2.7 unchanged at 55e50090afd6). #5.39-3-1 carries the q = 0 dev parts at m_Psi per Y_i, and #5.39-3-3's eps^R_A ends with + 1 + m_Psi; re-read, it matches #815. The other LF changes (12a r1b in §§1-3, #3.26-1 to #3.26-5, #3.86, #3.94-1 to #3.95, #4.559) are not cited by either note (case-sensitive grep). #PC.1-1.2 re-pinned (bookkeeping); pair note 5ee561774ff5, two-loops 6b3d1f0d7c47; labels pass. Pre-check: every repaired line re-read (-4.5.4-3-1, -4.5.4-7, -4.5.4-7-1, -4.5.4-8, -4.5.4-9, -4.10.1; two-loops #815, #817), packet about 10k characters of reviewed lines, no OPEN item and no known weak point. PC26 launched (full round) under the user's standing "Continue until everything has been closed and reviewed".
- 2026-11-06 (during PC26): LF now fc510e5cad00 (checked by hash): #5.39-3-1's duplicated heading reference removed, nothing else in §5 changed. Queued bookkeeping for after PC26: re-pin #PC.1-1.2 to fc510e5cad00.
- 2026-11-06 (during PC26): LF now d50e92b09804 (checked by hash): §4(c)-(d) only (#4.43 split, pins in #4.45 and #4.559, sub-tag splits in #4.44-#4.565, no bound changed); §5 unchanged. Neither note cites LF #4.4x or #4.5xx (case-sensitive grep). The queued re-pin is now to d50e92b09804.

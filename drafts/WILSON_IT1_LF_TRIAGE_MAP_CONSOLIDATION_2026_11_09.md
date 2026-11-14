# Consolidation of the D2 Step Map, 9 Nov 2026

## Rules

- Read every line. Remove status remarks, history, roadmaps, hedging, and dead routes.
- Cite by tag. Verify each citation. Keep lines at ~600 characters or less.
- Move the gaps block's items (#MOMGD) into their sections, with their tags, and delete the gaps block.
- Check consumers with cons.py before deleting any tag.

## Progress

- **Done:** the whole map. The gaps block (#MSOMGD) is deleted; each of its items is in its section, or was deleted as a status line or a duplicate of a section's text.
- **Next:** the D27 closure (status remarks; lines over 600 characters, line 7 at 6220).

## Edits

- **#MP.2-5, #MP.2-7:** dates and script names removed.
- **#MWTCI.8, #MWTCI.8-1:** stale "(Q), (Q″) neither derived" removed; they now point to continuum #NP.1-1 and #NP.1-2.
- **#MWTCI.10:** merged with #MWTCI.10-2. #MWTCI.10-1 (draft pointer) deleted.
- **#MWTCI.11-1, #MWTCI.11-2:** now point to #MOMGD.3 (the class (i)/(ii) entry) and #MOMGD.5 ((S-w)).
- **ONE STEP:**
  - Heading status removed.
  - Hedges deleted: #MOSTC.1-1–#MOSTC.1-4 (1-2 and 1-3 restated #MOSTC.23–#MOSTC.24), #MOSTC.23-1, and #MOSTC.24-1.
  - Roadmap and dead-route lines deleted: #MOSTC.25-1, #MOSTC.25-2, and #MOSTC.26-1.
  - #MOSTC.26 reduced to the convention ((0.4), which V4 fixes). The table cites it.
  - #MOSTC.14-1: the SU(3) example is removed. Its determinant is e^{6.28i} ≠ 1, so it is not an SU(3) element.
  - #MOSTC.14-3: the numerical ratio is replaced by a symbolic bound:
    - t ≤ s(1 + s/2 + e^s s²/6) ≤ 1.052s;
    - 2arcsin(t/2) ≤ t(1 − t²/4)^{−1/2};
    - hence ξ ≤ 1.0535s ≤ 1.06s.
- **ONE MORE STEP:**
  - Heading status removed.
  - #MOMST.6-2 now carries class (i) and class (ii) by pointer (#MOMGD.3, #MOMGD.3-13). #MOMST.6-3–#MOMST.6-5 deleted.
  - #MOMST.5-3 and #MOMST.8-3 now point to #MOMGD.2-6, #MOMGD.2-7, #MOMGD.2-10, and #MOMGD.2-12. #MOMST.8-4 deleted.
  - "with its OPEN items" removed.
- **Coupling item:** reported by the table fork, re-derived from BETA #B2.4–#B2.11 and #B8.31–#B8.38-3.
  - RG1 Thm 2 is on p.259 l.28–38, not p.260. p.260 has only the "superficial" sentence.
  - The exact lower bound of (0.31) is not available at simple G (#B8.38-2). The map now uses g_k² ≤ C′/(K−k+1), C′ := 1/min(γ^{−2}, b) (#B8.38-3), and (W) on windows (#B2.5) for the carry lemma's S_R.
  - New #MD2.0.5.2–#MD2.0.5.2-5. (b) is rewritten as #MD2.0.5.6-4–#MD2.0.5.6-6, with D2.3(6)(a)'s 𝔞_{k+1} remainder and C_Σ𝔞̄.
  - Deleted, each cited only in the map: #MOMGD.26, #MOMGD.38–#MOMGD.44, #MD2.0.5.2-6, #MD2.0.5.2-7, #MD2.0.5.6-1, #MD2.0.5.6-2, #MD2.0.5.6-3, #MD2.0.5.6-7, #MD2.0.5.6-8, and #MD2.3.7.9 with its sub-lines.
  - "Coupling item" pointers repointed at #MOMGD.18, #MOMGD.20-2, #MOMGD.30-1, #MD2.0.3.15-2, #MD2.0.3.15-4, #MD2.1.4.31, #MD2.2.2.17-2, #MD2.2.6.14-2, #MD2.2.6.15-2, #MD2.2.6.16-2, #MD2.3.4.16-4, #MD2.3.4.19-9, #MD2.0.5.44, and #MD2.3.9.13-1.
  - #MD2.0.5.5-3: the SU(2) clause is removed; the lower bound on P_kτ_k² now comes from CRE (2.6) via #MD2.0.5.2-2.
- **Gaps block:**
  - Moved with their tags: #MOMGD.37 (D2.4(2)), #MOMGD.47–47-2 (end of D2.0(3)), #MOMGD.55–55-2 (#MD2.2.6.164), #MOMGD.58–58-1 (#MD2.2.6.198), #MOMGD.36 (after #MD2.2.6.170-8: the consumers, (S-w), and through it (Z), #MD2.3.4.58), #MOMGD.52 (after #MD2.2.6.86-7), #MOMGD.54 and #MOMGD.57 (after #MD2.2.6.140-1).
  - #MOMGD.57: RG1 p.273 l.13 assumes (3.14) for 𝐇_j(B(t)) at small ε₁, and l.30–31 states that the localised functions satisfy it; the unprinted "at s = 1" is removed; RG2 p.2 l.11–14 quoted for the substituted functions.
  - #MOMGD.49–49-5 are on D2.2(4)(f)'s margin lines (former #MD2.2.4.77, 77-1, 77-2, 79, 79-1). 49-5 is now derived: the margin, holding for every small g_K, entails q₁ ≥ p₀, since ε_k/α_{1,k} = (A₀/C₁)(log g_k^{−2})^{p₀−q₁}.
  - #MOMGD.50 is on the RMJ line (former #MD2.2.6.142-23).
  - Deleted (statuses or duplicates of section text, each checked against the section): #MOMGD.34, 35, 36-1–36-3, 45–45-3, 46–46-2, old 47–47-6, 48–48-4, old 49–50-3, 51, old 52–52-4, 53–53-2, old 54–57-1, 59–61, 62–62-12, 63–66, and #MSOMGD.
- **D2.3(9), D2.4(0):** amendment notes and the RTR duplicate deleted (#MD2.3.9.11–#MD2.3.9.13-1); D2.4(0)'s copy of D2.3(9)'s list replaced by one input line; the pointer "D2.2(5)(f)" (no such item) removed.
- **Bare d:** fixed at #MD2.1.5.11-2, #MD2.0.4.12-11-1 (now e^{−δd(Y′∖Y′₀, Y′₀)}e^{−(κ₁−1)M^{−d}|Y′∖Y′₀|}, as D27 15.5(ii)), #MD2.2.6.142-54, #MD2.2.6.142-57, (6)(e)'s (190) line, #MD2.4.1.14-6, and #MD2.4.1.15-2.
- **Repair, #MD2.2.6.142-55:** δ₂ := min(δ₀, δ₁)/4, was /2. Composing e^{−(δ₁/2)d(y,y′)} with e^{−δ₀d(y′,y″)} and summing over y′ needs a rate below min(δ₁/2, δ₀); /2 equals it when δ₀ ≥ δ₁. #MD2.4.13.19-2 now cites #MD2.2.6.142-55.
- **#MOMGD.29-5:** restored on the former #MD2.4.5.16-4 (CRE p.267's ζ resummation); the D26 closure cites it three times.
- **Splits (lines over 620 characters):** new #MD2.0.3.54-0, #MD2.0.4.12-11-1, #MOMGD.12-2-1, #MD2.2.6.38-3-1, #MD2.2.6.142-19-1, #MD2.2.6.163-3-1, #MD2.2.6.170-3-1, #MD2.2.6.190-9-1, #MD2.2.6.190-14-1, #MD2.3.4.55-0, #MD2.4.11.1-4-1, and #MD2.4.13.19-2-1.
- **Continuum note:**
  - Old-version map line cites → tags: l.1093 → #MD2.3.4.15, l.1094 → #MD2.3.4.16, l.1096 → #MD2.3.4.18.
  - Self cites l.3 → #NP.1-2 and l.84 → #NP.1-3.
  - The bg note is cited by section (#NR.2), at the table fork's request.
- **D27 closure:** item 13's heading (stale "D2.0(6) orders the work" sentence and status removed); register: #MOMGD.25 → #MOMGD.25-2, #MOMGD.62 → #MD2.2.6.98–#MD2.2.6.116.
- **READINGS_INVENTORY:** #MOMGD.11-1 → #MD2.2.6.190-11. **Packet plan:** #MOMGD.11–#MOMGD.11-9 → #MOMGD.11.

## SHAs

- Map: 9d16ba768748 → 2b6ef4264a32 → 75fc93c17638.
- Continuum: 3ded0274387d → f53427d9fb47.
- D27 closure: 8ac6c8411363 → 4bd083b24532.
- READINGS_INVENTORY: 7e3131d7736f. Packet plan: dd136224741f.

## Messages

- 13:01, to the table fork: the repair, the deleted tags, and the SHAs.
- 15:33–15:35, to the table fork: dangling rows (#MOMGD.50-2 → #MOMGD.50; the object of #MOMGD.33-69 is no longer defined), δ₂, σ_{k+1} → #MD2.4.3.2, S_H at #MD2.2.6.185-2, #MOMGD.49's content, c_π uses, moved, new, and deleted tags, and the SHAs.
- 15:33–15:35, to the two-loops session: TWO_LOOPS #MOMGD.7-10 → #MD2.4.12.48, PAIR #MOMGD.9-1 → #MD2.3.5.2, #MOMGD.30 valid, c_π, and the D27 fix with its SHA.

## Outside This Session's Files

- Table rows above: the table fork.
- TWO_LOOPS #MOMGD.7-10 and PAIR #MOMGD.9-1: the two-loops session.
- Bare c_π: D27 line 8 (D2.7's #7 block), the COMPLEX_COVARIANCE note, and D26 §4.4 line 81.
- O4's status (NOT CLOSED in rounds 50 and 52; the S1′ repair unreviewed) is in the O4 closure's *Status* (line 5); the map's copy, #MOMGD.62-7, is deleted.

Written 2026-11-09 15:35.

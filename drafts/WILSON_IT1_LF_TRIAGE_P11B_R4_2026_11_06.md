# Packet 11b r4 Triage (LF #4.30–#4.42-2)

Review: verification/isolated_reviewer/reviews/lf-p11b-20261106-r4/review.md (full round of part 11b, with r3's review as its prior), on LF 82fcc5b842a5, labels 9dbc3256f7db, and table 697a56eb4c81. The run used the config directory .claude-IF.

## Verdict

r4 has no fatal or serious finding. It has two minor findings (m1, m2) and one trivial point (t1), so it is **not clean**. r3's m1 and m2 are confirmed fixed. #4.41-2-2 is INCORRECT as a reading of the source (m1). #4.42-1 is CORRECT in its estimate, with a notation finding (m2). Every other named step is CORRECT.

## Repairs

| Finding | Lines | Repair |
|---|---|---|
| m1 | #4.41-2-2 | The claim that (1.70) does not fix the evaluation point is removed. The line now reads "(1.70) writes the weighted action in CRE's notation A(f, U), which weights a plaquette's term by f(x(p)), x(p) the initial point of ∂p, p = p_{μν}(x(p)) (CRE p.253 l.28–30; LFR II p.361 l.25, p.364 l.22), so w(p) := w(x(p))". w(b) is taken at the initial point of b, and the bonds of p_{μν}(x) have initial points at distance 0 or ε from x(p). |
| m1 | #4.41-2-3 | The fine plaquettes of cell(p), L in each direction of the 4-cell of side ε, have initial points that differ from x(p) by at most (1 − 1/L)ε in each coordinate, so they lie within 2ε of x(p). The bounds ε\|∇w\| and 2ε\|∇w\| are unchanged. |
| m2 | #4.42-1, #4.42-1-1 | The {#D.C_h} tag and the ":=" are deleted. The line now reads "with C_w(ε₀)C²ḡ²p₀(ḡ)²(g_a^{−2} + 8b₂/(eε₀ ln L)) added to C_h, a constant of ε₀, ḡ, g_a, L, C_T, and Bałaban's constants", and #4.42-1-1 reads "This contribution is uniform in K". |
| m2 | table #T4.35 | The row now reads "LF #4.42-1 adds C_w(ε₀)C²ḡ²p₀(ḡ)²(g_a^{−2} + 8b₂/(eε₀ ln L)) to the cumulative C_h", and its dependence cell reads "that contribution on ḡ, g_a, and C_T (LF #4.42-1)". The row was announced to the fork before the edit. |
| t1 | #4.30 | The line adds "In #4.30–#4.42-2, VAR's lattice spacing η is ε, so a_j = L^jη". #4.30-1 is at 588 characters, so the identification goes into #4.30. |

## Pre-check

- **m1.** CRE p253_corrected.tex l.28–30 prints that A(φ₁, U₁) multiplies a plaquette's term by φ₁(x(p)), "x(p) is the initial point of ∂p". LFR II p361_corrected.tex l.25 and p364_corrected.tex l.22 print ζ(x(p)) and A(ζ₁, U″_{k,Z}) in this notation.
  - The bonds of p_{μν}(x) as positively oriented bonds are (x, μ), (x + εe_μ, ν), (x + εe_ν, μ), and (x, ν). Their initial points are x, x + εe_μ, x + εe_ν, and x, at distance 0 or ε from x(p).
  - cell(p) has L⁴ fine plaquettes parallel to p, one per point of a grid of step ε/L in the 4-cell of p, and each fine plaquette lies in exactly one cell (#C9.3.3-6). So in each coordinate their initial points take L values, which differ from x(p) by at most (L − 1)ε/L. The distance is then ≤ 2(1 − 1/L)ε < 2ε, whichever 4-cell containing p is meant.
  - The decomposition J_w = wJ + J_∇ is ours, so w(b) is a free choice; only w(p) is fixed by (1.70). No other line of the LF, the Cauchy note, the table, or the BP files uses the centre convention.
- **m2.** C_h is cumulative across the LF: it is added to at #3.38, #3.39, and later lines ("absorbed in C_h", "C_h enlarged by …"), and table rows cite "Cauchy §8.6's C_h". No file cites #D.C_h, and the deletion changes no mathematics. C_T enters through C_w(ε₀) (#4.42).
- **t1.** a_j = εL^j (#4.42-0), and the blocks of the layer j have side L^jη in VAR. So η = ε throughout this part. The LF's other uses of η = ε/L (outside the part) are unaffected. η_π of #4.31 is a separate symbol.
- **Lines.** #4.30 has 538 characters. CR 0 in the LF and the table. The labels index is rebuilt (37c88ea8a521).

## Outside the part (recorded, not repaired here)

- #C6.2.18-5 describes #4.41's weight as CRE (2.24)'s 1/g_k²(x), omitting ζ₁. This goes to the Cauchy caller's packet.
- #T3.23's ε₃ record omits VAR (77) and Proposition 4. This goes to the table's record.

## Repaired files

LF 9eaf5c814323 (was 82fcc5b842a5), labels 37c88ea8a521 (was 9dbc3256f7db), table f0a0118791cf (was 697a56eb4c81).

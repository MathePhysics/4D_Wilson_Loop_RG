# Triage of lf-p13b-20261108-r12

## Verdict

- r12 was a narrow round of 13b at LF 8e49f0e24a20, table 6d09b1b5054d, and labels 971e7d7d5325.
  - Under review: #4.52-1–#4.52-1-2, #4.561.1-1.3-1.0, and #4.567–#4.568.
- **Fatal:** none. **Serious:** none.
- **Minor:** one, m1: a name clash in #4.52-1-1.1. "Ū_0^j" was REG's average of REG's base U₀ := Q^{s*}_kV_Λ, while the note's U_0 is LFR I's configuration, REG's U′U₀.
- **Observations:** six, o1–o6.
- The round is not clean, so 13b's clean count stays 0.
- Round 11's m1 and o1–o4 were confirmed repaired.

## Repairs

| Finding | Line | Issue | Repair |
|---|---|---|---|
| m1 | #4.52-1-1.1 | Ū_0^j named REG's base with the note's letter U_0 | The line now reads "... has the form of REG (1.65) ..., at REG's base U₀ := Q^{s*}_kV_Λ, REG's U′U₀ being LFR I's U_0, whose top-level difference abs(M^k(U_0) − V_Λ), bounded by REG's α₁, is 0 (p.197 l.3)". The base's averages are written M^j(Q^{s*}_kV_Λ), and the symbol Ū_0^j is gone from the note |
| o1 | #4.52-1-1.1-1 (new, split from #4.52-1-1.1) | M^j(Q^{s*}_kV_Λ) = Q^{s*}_{k−j}V_Λ was stated without proof | "(derived: each contour Γ_{c,x} of CMP 98 (15) of a bond c crossing a k-face meets it in one bond of B(c), its other bonds being 1)". Checked against CMP 98 p.019 l.41–47: Ū_c = exp[iΣ_xL^{−d}(1/i)log U(Γ_{c,x})U(c)^{−1}]U(c), with Γ_{c,x} = Γ_{c₋,x} ∪ [x, x(c)] ∪ Γ_{x(c),c₊}. At the base, every U(Γ_{c,x}) and U(c) is V_Λ(c), so Ū_c = V_Λ(c). Bonds inside a k-block average to 1. The step iterates, since the result has the same form at the k − 1 scale. Checked against CRE (1.3): B(c) = {b : b₋ ∈ B(c₋), b₊ ∈ B(c₊)} |
| o2 | #4.52-1-1.1 | Q^{s*}_kV_Λ is not in REG's 𝔘_k(α₀) of (1.33), since its edge plaquettes carry V_Λ's curvature; (1.65)'s proof uses only plaquettes on which this base is flat | "is REG (1.65)" now reads "has the form of REG (1.65)". This identifies the form and the mechanism, as support for a reading labelled inferred. It is Bałaban's step, used only as evidence |
| o3 | #4.52-1-2 | #4.5-2 is a statement about domain layers; inside Λ the lattice scales and the common top scale are what is used | "(#4.5-2, the two runs having the top scale a_k on Λ, #4.53)" |
| o4 | #4.561.1-1.3-1.0 | (1.43) prints only "in the axial gauge"; that U_0(z) satisfies the k-block conditions was not derived | "So is U_0(z) of (1.43) (#T11.30-2) (derived): at the real points of the line it is LFR I's U_0 (1.79), and the conditions are analytic equations in its averages M^n(U_0(z)), so they hold on the disc by the identity theorem." Checked LFR I (1.79), p.195 l.7: U_0 = U_{k,Z}(V_Λ). The line is split at "These conditions" into the new #4.561.1-1.3-1.0-1 |
| o5 | #4.567-1 | ρ_V ≤ ¼ and abs(V′) ≤ 9/8 use (T-c)'s C_{V′}ε₁′ ≤ ½, which was uncited | "ρ_V := ½C_{V′}ε₁′ ≤ ¼ ((T-c), #4.561-1.2)". #4.561-1.2 states C_{V′}ε₁′ ≤ ½ |
| o6 | the table, LABELS | #T11.33's "not the absolute axial gauge (1.15)" needs "for a general base"; LABELS is stale | Both belong to the table fork. It was asked for #T11.33 at 05:50 and is now sent this SHA and the new tags |

## Checks

- No CRLF. Line lengths:
  - #4.52-1-1.1 467, #4.52-1-1.1-1 452, and #4.52-1-2 278;
  - #4.561.1-1.3-1.0 363 and #4.561.1-1.3-1.0-1 271;
  - #4.567-1 482 characters.
- "Ū_0" no longer occurs in the LF.
- #4.52-1-1 cites #4.52-1-1.1 for the evidence, which now continues in its sub-line #4.52-1-1.1-1.
- #4.561.1-1.3-1.0 has no consumer outside 13b; #4.561.1-1.3-0 cites the gauge through #4.52-1-1.
- **Identity theorem:**
  - The conditions are ordered products of M^n(U_0(z)) along the contours, equal to 1.
  - M^n is analytic near 1 (CMP 98 (15), through log and exp), and U_0(z) is analytic on the disc (#T11.30-2).
  - The real points of the line form a segment in the connected disc, so a condition that holds there holds on the whole disc.

## Rounds

- 12a1 r15 (full) is next. Then 13a2 r13 (full; its extract contains these repairs of #4.52-1-1.1, #4.52-1-1.1-1, and #4.52-1-2), then 13b r13 (narrow), then 13a1 r9 (focused).
- The pre-check of 12a1 r15 is in WILSON_IT1_LF_TRIAGE_P13A2_R12_2026_11_08.md. Since then the LF changed only in §4(c)–(d), outside 12a1's extracts and its context #4.53-1–#4.53-1.0-2. The spec is refreshed to this LF.

## SHAs

LF 29d718346d09 → 4cf4519bb09d. Table 6d09b1b5054d (unchanged).

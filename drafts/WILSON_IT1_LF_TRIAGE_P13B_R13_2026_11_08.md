# Triage of lf-p13b-20261108-r13

## Verdict

- r13 was a narrow round of 13b at LF a0e16b2810b8, table 6d09b1b5054d, and labels 971e7d7d5325.
  - Under review: #4.52-1–#4.52-1-2, #4.561.1-1.3-1.0–#4.561.1-1.3-1.0-1, and #4.567–#4.568.
- **Fatal:** none. **Serious:** none.
- **Minor:** one, m1. In #4.52-1-1.1-1 the letter c meant a k-bond in "V_Λ(c) on B(c)" but the averaged bond of a level n + 1 ≤ k in the parenthesis; the induction on j and the factor U(c) of (15) were left implicit.
- **Observations:** four, o1–o4.
- The round is not clean, so 13b's clean count stays 0.
- Round 12's m1 and o1–o5 were confirmed repaired.

## Repairs

| Finding | Line | Issue | Repair |
|---|---|---|---|
| m1 | #4.52-1-1.1-1 | The letter c served for the k-bond and for the averaged bond; the induction and U(c) were implicit | "U_{REG} is 1 on the bonds inside the k-blocks and V_Λ(c) on B(c), c a bond of Λ^{(k)} (...). So M^j(U_{REG}) = Q^{s*}_{k−j}V_Λ, l.10's reference term (derived, by induction on j: at a level-(n+1) bond b′, every contour Γ_{b′,x} of CMP 98 (15) has the value 1 if b′ lies in a k-block, and V_Λ(c) if b′ crosses the face of the k-blocks joined by c, its one crossing bond lying in B(c); so (15) gives Ū_{b′} = 1 or V_Λ(c), whatever its factor U(b′))." The last sentence is split into the new #4.52-1-1.1-2 |
| m1, the factor U(b′) | #4.52-1-1.1-1 | CMP 98 does not define the factor U(c) of (15) at p.019 (l.25–56 checked) | The derivation does not need it. If every U(Γ_{b′,x}) equals W, then (15) gives exp[i(1/i)log(WU(b′)^{−1})]U(b′) = WU(b′)^{−1}U(b′) = W, since the average of equal terms is the term and exp∘log = id near 1. The line says "whatever its factor U(b′)" |
| o1 | #4.52-1-1.1-1, #4.52-1-1.1-2 | U_{REG} was defined but unused | Both lines now write U_{REG} |
| o2 | #4.52-1-2 | M^n(MU^B) and MU^B_0 were mixed | "M^n(MU^B_0)". The consumer #4.53-1.1-1 writes MU^B in #4.53's convention, MU^B at V′^B₀, which the referee found clear; it is left as it is |
| o3 | #4.561.1-1.3-1.0 | "it is LFR I's U_0 (1.79)" means LFR I's U_0 at the real point's data | "it is LFR I's U_0 (1.79) at their data V_k(z) (#4.559-1)" |
| o4 | the table, LABELS | #T11.33's qualifier; stale LABELS | The table fork's. It has been asked for both since 05:50 and has not replied |

## Checks

- No CRLF. Line lengths: #4.52-1-1.1-1 524, #4.52-1-1.1-2 114, #4.52-1-2 280, and #4.561.1-1.3-1.0 395 characters.
- b′ is a local dummy: no {#D.b′} exists in the LF or the table.
- **The induction, re-derived.**
  - At level n, assume the configuration is Q^{s*}_{k−n}V_Λ.
  - A level-(n+1) bond b′ inside a k-block has its contours Γ_{b′,x} = Γ_{b′₋,x} ∪ [x, x(b′)] ∪ Γ_{x(b′),b′₊} inside the k-block (nesting, #T11.33-2), so each has the value 1.
  - For b′ crossing a k-face, the segment [x, x + Le_μ] crosses the face in one level-n bond, joining the two k-blocks, of value V_Λ(c). Its other bonds and the two contours lie in the two k-blocks, where the value is 1.
- The edits of #4.52-1, #4.52-1-1.1, and #4.52-1-2 are in 13a2's lines too, which are done. These are a renaming, a subscript, and a written-out derivation that changes no bound.

## Rounds

- 13a1 r9 (focused) is next. Then 13b r14 (narrow: #4.52-1-1.1-1, #4.52-1-1.1-2, #4.52-1-2, and #4.561.1-1.3-1.0), then the full rounds of 13b and 13a1.

## Pre-check of lf-p13a1-20261108-r9 (focused)

- **Spec.** specs\spec_p13a1_r9.json at LF 1b87b5ea51bf, prior r8. --check gives 0 conflicts (7 allowed). Built: 22,883 characters of argument, the whole part with its unchanged lines as context.
- **Changed tags since r8 (11), all under review:**
  - **#4.44-1:** consolidation; LFR II's fluctuation is written W′ and the note's V′ is W′V′₀.
  - **#4.44-2:** r8's m1. ‖Y‖_∞ is in the operator norm and ‖Y‖₂ in the normalised trace, so ‖Y‖_∞ ≤ √N‖Y‖₂ (operator norm ≤ HS norm = √N times the normalised-trace norm).
  - **#4.48.0-2.1:** the operator norms of the transports; 2^{1/8} = e^{(log 2)/8}.
  - **#4.48-2:** Schwarz: C_ΦC₁²ε₁²(‖Y‖_∞/(2C₁ε₁))³ = C_Φ‖Y‖_∞³/(8C₁ε₁) ≤ NC_Φ‖Y‖_∞‖Y‖₂²/(8C₁ε₁).
  - **#4.48-3.1:** Cauchy's estimate with ‖Y‖_∞² ≤ N‖Y‖₂², giving the factor N in C_{1−ζ₀}(M).
  - **#4.49:** κ_Λ/2 − NC_Φ‖Y‖_∞/(8C₁ε₁) ≥ κ_Λ/4 if and only if ‖Y‖_∞ ≤ 2C₁κ_Λε₁/(NC_Φ).
  - **#4.50-0:** C₁ ≥ NC_𝔛C_Φ/κ_Λ gives 2C₁κ_Λε₁/(NC_Φ) ≥ 2C_𝔛ε₁ ≥ ‖𝔛‖_∞, and C_𝔛ε_k ≤ ε₁ < 2C₁ε₁.
  - **#4.50-1.0, #4.50-1.1.0, and #4.50-2:** consolidation. Each cites #4.48.0's conditions and the uses in *The comparison.* by tag instead of restating them.
  - **#4.50-1.1.0-0:** 13a2 r12's t1, α₁^{CMP} := 2ε₁max((π/8)dB₀c_tot(1/128), c_{A′}).
- 13a2 rounds 10–13 read several of these lines among their extracts and found no fault in them.
- No new symbol. No known weak point and no OPEN is in these lines.

## SHAs

LF a0e16b2810b8 → 1b87b5ea51bf. Table 6d09b1b5054d (unchanged).

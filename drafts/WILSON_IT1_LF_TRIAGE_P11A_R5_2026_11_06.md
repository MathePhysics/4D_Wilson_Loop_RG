# Packet 11a r5 Triage (LF #0.17 and #4.1–#4.9-3)

Review: verification/isolated_reviewer/reviews/lf-p11a-20261106-r5/review.md (full round of part 11a), on LF a4bf700750d6, labels 9d999873d0aa, and table e02c753f1f9d.

## Verdict

r5 has no fatal or serious finding, two minor findings, m-1 and m-2, and five trivial points, t-1 to t-5. So it is **not clean**. r4's m-A and t-A are resolved; t-B became m-2. The earlier findings remain resolved.

## Repairs

| Finding | Lines | Repair |
|---|---|---|
| m-1 | #4.7-1-4-1-2, #4.7-1-4-1-3, #4.43 | U_{k,Λ} is used only in (d) (#4.546), whose ε₁ is the larger of §1's and C(M)R_kε_k (#4.59, ε₁^{LF} of #T4.35). Its data are V″ off Λ and V_Λ^{(A)} on Λ, within O(1)B₃B₅M⁶ε_k ≤ C(M)R_kε_k of 1 in the axial gauge ((1.84) [IV], LFR II p.371 l.32–33). #4.43 adds C(M) ≥ O(1)B₃B₅M⁶ to its lower bounds on C(M). The bounds on 𝐁₁'s bottom strip hold with (d)'s ε₁. |
| m-2 | #4.7-2, new #4.7-2-0 | C₀^{ms} := 2L⁴C₀ is unchanged. #4.7-2 now excepts the composites ∂*∂A and ΔA on T_{1.70}, which are within 2dC₀^{ms} (#4.7-1-4-2-1). #4.7-2-0 records that §9 uses only (9.2) on F, ∇F, A (#C9.3.1) and that PBG (3.36) for Ũ comes from REG Proposition 6 (#C9.8.4-2). At the a_0 bottom strips the composites are within C₀^{ms} already. |
| t-1 | #4.5-2 | "as #4.445.1's count gives at ∂□₀" now reads "by the maximal domains of CRE p.256 l.59–61, as at ∂□₀ (#4.445.1)". |
| t-2 | #4.5 | "≤ g_k²abs(δ_k)" cites #4.168. |
| t-3 | #4.5-2-2 | "in #4.32" now reads "in #4.32-1". |
| t-4 | #4.7-1-4-1-2 | The 2M′a_0-cube is taken on the a_0-grid inside U_{k,Λ}'s class cube of side ≥ 2M′a_j containing x. |
| t-5 | #0.17 | "The others" now reads "The bounds for all layers". |

## Pre-check

- **m-1 source.** LFR I p.197: "(1.84) abs(M^j(U_0) − 1) < O(1)B₃B₅M⁶ε_k inside Λ". LFR II p.371: "The field V_Λ^{(A)} is in the axial gauge in Λ … More precisely the condition (1.84) [IV] is satisfied for it." Plaquettes are gauge invariant and within 4 times a link bound; R_k ≥ 1 (#T2.23).
- **m-1 home and consumers.** The regularity of U_0's data already lives in (c) and (d): #4.43 (ε₁ := C(M)R_kε_k) and #4.59 ("Throughout (d), ε₁ is the larger of the ε₁ of §1 and the C(M)R_kε_k of (c)"); #4.546 lies in (d). #1.3's C is untouched. Every use of C(M) in the LF, the table, and the Cauchy note is a lower bound or a constant factor in a ratio made small by γ, so the added lower bound changes no other line. No line cites #4.7-1-4-1-1–#4.7-1-4-1-3.
- **Withdrawn first repair.** A first repair (a new #4.7-0 raising #1.3's C to O(1)B₃B₅M⁶) was withdrawn before review: it changed §1's ε₁ from outside its definition, restated #4.43's fact, and claimed (1.84) for data it does not cover (the factor exp ig_kB in U″_k's data, the complex data of (1.53)). The r6 run launched on it was stopped by the user.
- **m-2 consumers.** #C9.3.1 assumes (9.2) only; #C9.8.4–#C9.8.4-2 obtain (3.35)–(3.36) of Ũ from VAR (2) through REG Proposition 6. #4.315 uses VAR (9)–(10) on VAR's own cubes with B₃M, not C₀^{ms}. C_hes (#4.40.1-3) bounds ⟨A, ΔA⟩ through a abs(A) and its differences, not through the background's composites.
- **Lines.** #4.7-1-4-1-1 and #4.7-2 split at sentence boundaries (new #4.7-1-4-1-2, #4.7-1-4-1-3, #4.7-2-0). Longest lines of the part: 615 (#4.9-0), 613 (#4.7-1-0), 601 (#4.5-2-2). CR 0; no duplicate line tags; every citation resolves.
- **Size.** Part 19.2k characters; argument of the r6 packet 21.0k (≤ 25k). Definition check: 0 conflicts.

## Repaired files

LF 27b8858fc692, table e02c753f1f9d, labels f37e89c7f85d.

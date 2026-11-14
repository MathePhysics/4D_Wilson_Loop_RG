# Packet 14b1 (Cauchy #C10.3.1–#C10.3.16), round 4, 9 Nov 2026

## Pre-check of cauchy-p14b1-20261109-r4 (narrow)

- **Under review:** the lines repaired after round 3 (m1–m7, WILSON_IT1_LF_TRIAGE_P14B1_R3_2026_11_09.md): #C10.3.3–#C10.3.3-1, #C10.3.3-6–#C10.3.3-10-1, #C10.3.3-11-6–#C10.3.3-11-7-0, #C10.3.4–#C10.3.4-0-1, #C10.3.10-2, and #C10.3.14–#C10.3.14-2. #C10.3.3-11-6-1 is included as the consumer of #C10.3.3-11-6-0. The rest of 14b1 and the consumers #C10.3.3-11-7-1–#C10.3.3-11-8-1, #C10.3.14-3–#C10.3.16, and #C10.3.51 are context.
- **Changed lines re-read** at Cauchy e269a956602b. The re-pointing of #C10.3.10-2 below changes only a tag.
- **Re-derived:**
  - **#C10.3.3-1.** At the scale ℓ = a_j/L: |A| < α₁/a_j = (α₁/L)ℓ^{−1}; |∇A| < α₁a_j^{−2} = (α₁/L²)ℓ^{−2} ≤ (α₁/L)ℓ^{−2}; and |𝐉| < α_Ja_j^{−3} = α_JL^{−3}ℓ^{−3}. (3.35) passes from a_j to ℓ by #C10.2.1-0-1.
  - **#C10.3.3-10-1.** In ℓ-units, (3.35) at a_j puts U₀'s plaquettes within Mα₀η²/a_j² = (Mα₀/L²)(η/ℓ)², which is (52) with O(1)Mα₀/L². Also |A| < α₁/a_j becomes α₁/L.
  - **#C10.3.3-11-6-0.** W₀'s plaquettes at spacing ℓ are within O(1)Mα₀/L² of 1 (#C10.3.3-11-1). With Lℓ as the unit the spacing is 1/L, so (52) holds with O(1)Mα₀. Since |W′ − 1| < O(1)α₁ and W′ = e^{iA′/L}, |A′| ≤ O(1)Lα₁.
  - **#C10.3.3-11-6-1.** For |s|, |s′| ≤ r_P/(3Lℓ), Lℓ sup|B| ≤ 2r_P/3 < r_P, so |f| ≤ C₂^{(135)}(2r_P/3)². The ss′ coefficient is at most C₂^{(135)}(2r_P/3)²(3Lℓ/r_P)² = 4C₂^{(135)}(Lℓ)², and half of it times (Lℓ)^{−1} gives 2C₂^{(135)}Lℓ. Higher-order terms contribute no ss′ monomial.
  - **#C10.3.3-11-7.** (B1) at n = 1 adds D̄Θ₁ to the plain part. Θ₁B(y) reads B only on the contours inside B(y) (CMP 98 (97)), and b₀(c) joins B(c₋) to B(c₊), so it lies on no contour inside one block. Hence the coefficient of B(b₀(c)) is the same for both averagings.
  - **#C10.3.4.** t = 1 lies in #C10.3.14's disc |t| ≤ α₁/(8ρ_j) when 8ρ_j ≤ α₁, which 16ρ_j ≤ α₁ (#C10.3.51) gives.
  - **#C10.3.4-0-1.** 𝒬(U^B) = d(M^{j+1})(U^B) = d(M^j)(Ũ)·dM(U^B) by the chain rule (#C10.3.1-6). A composition of onto maps is onto.
  - **#C10.3.14–#C10.3.14-2.** The ∇_Ũ wording changes no bound. #C10.3.14-2's arithmetic: 4C₀ε₁·2α₁(ε/a_j) ≤ (1/15)α₁ when 40C₀ε₁ ≤ 1 and ε/a_j ≤ 1/3.
  - **#C10.3.3-6, #C10.3.3-10, and #C10.3.10-2.** The pins p.419 l.11–12, p.422 l.15–21 and l.50, and p.423 l.33–36 were re-read in round 3's triage. Nothing changed since.
- **Consumers grep** (tag-exact, over the Cauchy note, the LF, the W-δ note, the table, balaban_proofs/, and the two-loops notes):
  - #C10.3.3 is cited by #C10.1.6-1 and #C10.2.1-0. #C10.3.3-1 is cited by #C10.2.1.
  - #C10.3.3-6 is cited by #C10.2.1, #C10.3.3-9, #C10.3.3-10, and #C10.3.10-2.
  - #C10.3.3-10 is cited by #C10.1.3-3, #C10.1.6-1, #C10.2.1, #C10.2.1-0, #C10.2.3, #C10.3.3-11, #C10.3.3-11-5, #C10.3.10-2, #C10.3.42-3, #C10.3.51-0-1, and table #T12.7-24-2 (for B₀^{cx}, correct).
  - #C10.3.3-10-1 is cited by #C10.3.3-11, #C10.3.3-11-6-0, and #C10.3.51-0-1. #C10.3.3-11-6 is cited by #C10.3.3-10-1 and #C10.3.51-0-1. #C10.3.3-11-7 is cited by #C10.3.3-10-1.
  - #C10.3.10-2 is cited by #C10.3.14-5. #C10.3.14 is cited by #C10.3.4, #C10.3.4-0-1, #C10.3.42-2, #C10.3.51, and #C10.4.1-1.
- **Stale pointers from round 3's re-cut of #C10.3.3-8–#C10.3.3-10** (bookkeeping; re-pointed to the same text, no round needed):
  - #C10.1.6-1 cited #C10.3.3-10 for BX's conditions M ≥ M₃ and Mα₀ + α₁ + α_JL^{−3} ≤ a_cx, now at #C10.3.3-9. Re-pointed.
  - #C10.3.10-2 had "under the conditions of #C10.3.3-10". Re-pointed to #C10.3.3-9.
  - #C10.2.1-0 cited #C10.3.3-8 for the convergent series (3.138), now at #C10.3.3-9. Re-pointed.
  - #C10.3.51-0-1 cites #C10.3.3-9 for PBG's Theorem 3.4 (now #C10.3.3-8), #C10.3.3-10 for BX's conditions (now #C10.3.3-9), and #C10.3.3-11-6 for Proposition 7's threshold (now #C10.3.3-11-6-0). It is under review in cauchy-p14b2-20261109-r3, so it waits for that report and is re-pointed in its triage.
  - The other consumers read content still at the cited tag.
- **Other files:** the table is db331ee55977 (LABELS 54e113fa9642) after the fork's #T12.7-27, #T12.28-3-1, and #T11.20-2 changes, none cited by these lines. The LF is 73435a4a8e2a after #4.101–#4.101-1, which these lines do not cite.
- **Definition check:** 0 conflicts (9 allowed, as in round 3).
- **Size:** the reviewed block is 6.70k characters (25k cap). Every line is ≤ 581 characters, with no duplicate tags.
- **Spec:** specs\spec_p14b1_r4.json (Cauchy 21a4ba1b0dd3 after the re-pointings, LF 73435a4a8e2a). The table is now 0e8cb42f87e0 (LABELS 22c9a3403920) after the fork's #T10.1-3-0 split, which none of these lines cites.
- **Order:** next after 14b2 r3's triage.
- **Update at 09:48:** 14b2 r3's repairs (WILSON_IT1_LF_TRIAGE_P14B2_R3_2026_11_09.md) touch only 14b2 lines and the context line #C10.3.51 (§E's α₀ condition added). They change none of these lines. The spec is updated to Cauchy 5e2918ba9bcf and LF 8d84c228e098 (#4.53-1 cites c_v).
- **Built** at 09:48 (Cauchy 5e2918ba9bcf, LF 8d84c228e098, table 48ed6504f348, LABELS f16b9103c444, BP_PBG_COMPLEX 98a9c04ec3a7). Definition check: 0 conflicts (9 allowed). The argument field, context included, is 37.9k characters, of which the reviewed block is 6.70k. Launched at 09:48.

Written 2026-11-09 09:35.

## Verdict of cauchy-p14b1-20261109-r4

Not clean: one serious finding (S1) and three minor ones (m1–m3). There is no fatal finding. All other named steps are CORRECT, including the unit conversions of #C10.3.3-1 and #C10.3.3-10-1, the bilinear Cauchy bound, h, (124)'s coefficient, the multipliers, and the path U(t).

## Repairs

| Finding | Line | Repair |
|---|---|---|
| S1: C̃^{(2)} was read as the double-bar quadratic part (CMP 98 (134)), against RG I (2.4), which prints Q̃ with the plain M | #C10.3.3-11-6–#C10.3.3-11-6-1, #C10.3.3-10-1, #C10.3.3-11-8–#C10.3.3-11-8-1 | C̃^{(2)} is now RG I's plain quadratic part: F_c(B) := (1/i)log[M(e^{iℓB}W)(c)M(W)(c)^{−1}] = Q̃(ℓB)(c), with C̃^{(2)} the quadratic part of (Lℓ)^{−1}F_c. The support follows from (0.4). The bound comes from CMP 98 Proposition 6 ((164)) and Cauchy's estimate: abs(C̃^{(2)}(X1_b, Y1_{b′})) ≤ 4Lℓ/r_P², and C_𝐉 := (512/3)Ndr_P^{−2}c_eB₀^{cx}α_JL^{d−2}e^{δ₁′(2d+1)L}. C₂^{(135)} is gone, also from #CK. |
| m1: the real-pair use of Theorem 3.12 omitted that 𝐔 = e^{iεA}U₀ satisfies (3.35) | #C10.3.3-10, new #C10.3.3-10-0–#C10.3.3-10-0-1 | (3.35) at scale ℓ with 2(α₀ + α₁/(ML)) for α₀, derived in U₀'s cube gauge through the BCH remainder Φ. The conditions are added at #C10.3.51-0-2. |
| m2: the complex analyticity of (3.130) named only G₀ | #C10.3.3-8 | It names G′ and R (through Δ′_π) with G₀, all extended by Theorem 3.4 (p.400 l.7–10). |
| m3: the pointer for (3.133) for H at complex pairs | #C10.3.3-9 | #BX.1-3 and #BX.8-1 replace #C10.3.3-6. |
| Remark under #C10.3.3-11-7: Q̄₁h = I needs no off-diagonal entries | #C10.3.3-11-7 | It now states that b₀(c′), c′ ≠ c, is no bond of B(c₋) ∪ B(c₊). |
| Qualification under #C10.3.3-6: "(3.36) on U₀" | #C10.3.3-6 | (3.36) is asked of U₀ in (3.38) and of the external field in Theorem 3.12. |

## Re-derivations

- **S1, source check.** RG I p.266 l.6 prints (2.4), M(V′V^{(k)})M(V^{(k)})^{−1} = exp iQ̃(B′), with RG I's M of (0.4), the note's plain average (#C10.1.4). p.267 l.26 defines C̃ by LQ̃(B′) = LQ̃B′ + C̃(B′), and l.29 gives D̃^{(2)} = C̃^{(2)}. The referee's reading is correct, and the table already calls C̃^{(2)} the quadratic part "of the undressed Q̃".
- **S1, the bound.** CMP 98 (159) (p.042) is the plain relative average written as v_k(b₋)·(double bar)·R̄·v_k^{−1}(b₊). Proposition 6 (p.043) states that the plain Ū^k(Ū₀^k)^{−1} is analytic in complex A′, |A′| < α₁, within O(1)α₁ of 1. With Lℓ as the unit, e^{iℓB}W = U″W₀, and U″ = e^{iℓB}e^{iA′/L} = e^{iA″/L}. The BCH bound gives |A″| ≤ L(|ℓB| + |A′|/L + c_B|ℓB||A′|/L) ≤ r_P/2 + r_P/3 + r_P/18 < r_P. Both factors are within 1/8 of 1. Then |g₂^{−1} − 1| ≤ 1/7 and |g − 1| ≤ (1/8)(8/7) + 1/7 = 2/7, so |F_c| ≤ log(7/5) < 1/2. Cauchy's estimate in (s, s′) on |s|, |s′| ≤ r_P/(4Lℓ) bounds the ss′ coefficient by ½(4Lℓ/r_P)², so after the factor (Lℓ)^{−1}, |C̃^{(2)}| ≤ 4Lℓ/r_P². Constant, linear, and cubic terms contribute no ss′ monomial.
- **S1, consumers.** #C10.3.3-11-8: 2·2d·(8/3)·(4Lℓ/r_P²)·4N gives 512/3; L^{−3}·L^d·L = L^{d−2}; and ℓ^{−d}ℓ^{−3}ℓ = ℓ^{−d−2}. #C10.4.1-4 needs hC̃^{(2)} to depend on the background only through the block field, and F_c depends on W = M^mU only. #C10.1.3-0 already reads C̃^{(2)} as the quadratic term of Q̃ at the block field. The identification of Δ_{(𝐔,𝐉)} with RG I (2.11) now holds as printed.
- **m1.** In U₀'s gauge u, 𝐔^u = e^{iεA^u}e^{iεA₀}. Transports over at most two bonds give |∇A^u − (∇_{U₀}A)^u| ≤ 4|A₀||A|. Cauchy's estimate on Φ over a ball of radius r_B/2 gives |∂_XΦ| ≤ (2/r_B)c_Br_B|Y| = 2c_B|Y|. The lattice difference of ε^{−1}Φ(εA^u, εA₀) is then ≤ 2c_Bε|A₀||∇A^u| + 2c_Bε|A^u||∇A₀|. So |A_tot| ≤ O(1)M((5/4)α₀ + α₁/(10ML))ℓ^{−1} and |∇A_tot| ≤ O(1)M(3/2)(α₀ + α₁/(5ML))ℓ^{−2}, both ≤ O(1)M·2(α₀ + α₁/(ML)) times ℓ^{−1} and ℓ^{−2}. Theorem 3.12 (p.423 l.33–36) asks "α₀ sufficiently small", so the condition is 2(α₀ + α₁/(ML)) below that threshold.
- **m2.** Theorem 3.4 (p.400 l.7–10): "the operators G′(U), (Q′(U)G′²(U)Q′*(U))^{−1}, R(U), G(U) extend … as analytic functions of A … satisfy all the inequalities of Theorems 3.1–3.3".
- **m3.** #BX.8-1 gives |(H*𝐉)(b)| ≤ O(1)γ(L^jη)^{−3} from (3.133) at complex pairs.

## SHAs and messages

- Cauchy 4c3614eed5e5 after the repairs; LF 029a1d03a304.
- The table fork was asked to update #T12.7-24-2 (delete C₂^{(135)}; r_P as Proposition 6's α₁ with its conditions; the new C_𝐉) and to relabel for #C10.3.3-10-0, #C10.3.3-10-0-1, #C10.3.3-11-6-0-1, and #C10.3.51-0-2.
- Lines are ≤ 581 characters, CR is 0, and there are no trailing spaces or duplicate tags.
- Bookkeeping (10:15): the fork found r_B used for both the BCH radius and the field r_B := R_Bf_B (#C10.4.64–#C10.4.65). The BCH radius is renamed r_{BCH} at all 19 occurrences (#C10.3.3-10-0-1, #C10.3.3-11-2-1, #C10.3.3-11-6-0, #C10.3.14-3, #C10.3.34-7, #C10.3.36, #C10.3.51-0-1, #C10.3.51-0-2, #C10.4.9-1-1-1, #C10.4.124, and #CK); Cauchy 1f73875e3b26, max line 585. The fork applied it to #T12.7-24-2 and #T12.7-24-4: table 40e20f5e4530, LABELS 3a2b74eff243, definition check 0.

## Next

r5, narrow, on #C10.3.3-6, #C10.3.3-8–#C10.3.3-10-1, and #C10.3.3-11-6–#C10.3.3-11-8-1, with their consumers (#C10.3.51-0-1–#C10.3.51-0-2 are in 14b2 r4). Then r6, full.

Written 2026-11-09 10:11.

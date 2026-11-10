# Packet 14a (Cauchy §10.1–§10.2), round 3, 9 Nov 2026

## Pre-check of cauchy-p14a-20261109-r3 (full)

- **Whole part re-read** (#C10.1.1–#C10.2.3) on 9 Nov 2026, after 14a r2's repairs (WILSON_IT1_LF_TRIAGE_P14A_R2_2026_11_09.md), with its context: Cauchy #C9.8.1–#C9.8.1-2, #C10.3.4–#C10.3.4-1, #C10.3.25–#C10.3.25-1, #C10.3.39, and #C10.4.9-1-1–#C10.4.9-1-1-1. The last of these is new context, because #C10.1.4-1-1-1-1 cites its weights.
- **Citations re-read in the corrected transcriptions:**
  - PBG (3.16) on p.393 l.22–23: ⟨A, Q*aQA⟩ = Σ_j aΣ_{b∈Λ_j}(L^jη)^{d−2}|(Q_j(U)A)(b)|².
  - RG I p.253 l.42–43: "The considerations and results of this, and previous papers, do not depend on any particular averaging operation used; they are valid universally for all averages satisfying the above properties."
  - RG I p.254 l.7–10: (0.12) "has properties similar to the properties of the average introduced in (0.4), especially all results of the paper [12] are valid for it"; "both definitions are equally good for our purposes".
- **Re-derived:**
  - #C10.1.2-1: at the single scale ℓ, aℓ^{d−2}Σ_b|(Q_mA)(b)|² = aℓ^{−2}·ℓ^dΣ_b|(Q_mA)(b)|² = aℓ^{−2}⟨Q_mA, Q_mA⟩. So Q*aQ = aℓ^{−2}Q_m*Q_m for the adjoint of η^dΣ_b and ℓ^dΣ_b, and the a-term of (3.156) is aℓ^{−2}⟨B, B⟩.
  - #C10.2.1-1–#C10.2.3: on {Q_mA = B}, ⟨A, aℓ^{−2}Q_m*Q_mA⟩ = aℓ^{−2}⟨B, B⟩. Also (Δ₁ + DRD*)H₁B = G₁^{−1}H₁B − aℓ^{−2}Q_m*Q_mH₁B = G₁^{−1}H₁B − aℓ^{−2}Q_m*B, which lies in ran Q_m* = (ker Q_m)^⊥.
  - #C10.1.8-3–#C10.1.8-3-1:
    - By (0.8) the linear part at U = 1 of the contour variable U(y, x) is X(Γ̄_{y, x}), so the gauge average at y has linear part λ_y = L^{−(d+1)}Σ_{x∈B(y)}X(Γ̄_{y,x}) in the units of T_{Lη}.
    - (89) composes −λ_{c₋} + (L^{−(d+1)}Σ_x(X(Γ̄_{c₋,x}) + X([x, x′]) − X(Γ̄_{c₊,x′}))) + λ_{c₊}. Since x ↦ x′ is a bijection from B(c₋) onto B(c₊), this leaves L^{−(d+1)}Σ_xX([x, x′]), CMP 98 (125) in the normalisation of #C10.1.8-2.
    - The signs agree with (B1): Q^{pl} − Q̄₁ = λ_{c₋} − λ_{c₊}, a coarse difference of λ, and with #C10.4.69-1's θ_𝒜, which is −λ up to its units.
  - #C10.1.9-2 and -4: w_u^{(n)} composes the one-step w_u at the backgrounds M^iU along (B4), and its logarithm has linear part Q′_nλ, consistent with PBG (3.114)–(3.115).
- **Grep of touched symbols:**
  - a-term: Q*aQ in #C5.69–#C5.70 is PBG's notation at U = 1, and aQ*Q in #C9.4.1-2 is VAR's form (p.293). Neither uses the note's inner products, so neither changes. §10.4's consumers #C10.4.1-5 and #C10.4.5-2 now have aℓ^{−2}.
  - (124): it now remains only in §10.4 (packet 15), for the non-main terms, which #C10.1.4-1-1-1-1 covers.
  - (89)–(91): no remaining occurrence in §10.1.
- **Table:**
  - #T12.7-23 and its new continuation #T12.7-23-1 (table fork, after my message) carry P_U with aℓ^{−2}⟨B, B⟩, w_u, and w_u^{(n)}.
  - #T6.5-2 points to #C10.1.4-1-1-1 for the dressed average.
  - The part restates no row.
- **No known weak point** remains in the part. r2's m1, m2, and six cosmetic findings are repaired.
- **Definition check:** 0 conflicts (4 allowed: Y_c, U₁, X, and ℓ, as in r2).
- **Size:** the reviewed block (#C10.1.1–#C10.2.3, blank lines included) is 11.58k characters (25k cap). The growth over r2 is new mathematics: the a-term normalisation (#C10.1.2-1), the sources for CMP 98's results beyond (60)–(108) (#C10.1.4-1-1-1, -1-1-1-1, and #C10.1.4-0-3), and the U = 1 derivation for the contour-variable gauge averages (#C10.1.8-3, -3-1). The longest line is 579 characters. CR is 0, and there are no trailing spaces or duplicate tags.
- **Spec:** specs\spec_p14a_r3.json (Cauchy 00e33ad08351, LF b142ee965e51; table e87be282550b and LABELS 77da8ca31175 at this pre-check).
- **Order:** after 14bp r2, 14b r2, and 12b-bp r2, one referee at a time. Rebuild at launch.

Written 2026-11-09 06:20.

## Pre-check update after 14b r2's repairs

- **Changed lines in the part** (diff against the 14b r2 snapshot, Cauchy 3802c8fb4ced):
  - #C10.1.3-3: δ₂ := δ₁′, the rate of (3.132) at complex data (table #T10.50; #C10.3.3-10). r_j is the least number with the bound at that rate, so the line only fixes a definition. The bound by PBG's B₀ and δ₁ in its first clause is for real pairs. The consumer #C10.4.122 runs at δ₂ = δ₁′, and #C10.5.1-1, #CK.1-24, and #T3.27 now read δ₁′.
  - #C10.1.4-1-1-1: the results of CMP 98 taken on RG I p.254 l.7–8 and p.253 l.42–43 now include (124), Proposition 4 with (134)–(135), and Propositions 6 and 7, which #C10.3.3-10-1 and #C10.3.3-11-6–#C10.3.3-11-7-1 use. #C10.1.4-1-1-1-1 keeps (124)'s explicit form as CMP 98's own, with its contour terms over 𝐆(y, x). For x on the line of c, 𝐆(c₋, x) is the single straight segment, as a coordinate-monotone contour changes only the μ-coordinate. So #C10.3.3-11-7's reduction to T_c holds for the families.
- **Repair to the context** #C10.4.9-1-1-1: it still used the old angle bound abs(Ā) ≤ 2δ′ + c_{GM}δ′², which 14b r2's M2 replaced. The line now reads abs(Ā) ≤ (8/3)dε²abs(F) ≤ 3dε²abs(F) (#C10.3.3-11-2-1 at the spread dε²abs(F)). Its conditions now add 24c_BdC₀ε₁ ≤ 1 and 12dC₀ε₁ ≤ r_B, which are 8c_Bδ′ ≤ 1 and 4δ′ ≤ r_B at δ′ ≤ 3dC₀ε₁, beside 198c_{GM}dC₀ε₁ ≤ 1 (= 66·3). #C10.4.124 now lists the three. #C10.3.51-0-1 cites #C10.3.3-11-1–#C10.3.3-11-2-1 (601 characters).
- **Grep:** no other line uses 2δ′ + c_{GM}δ′² or cites #C10.3.3-11-2 for the angle bound. Table #T12.7-24 was updated by the fork (table 75715b244ad6, then 2396f07aafeb after BETA's BH10b-7, which touches no row this part uses).
- **Spec:** Cauchy 7a007794e060. Claim (a) gives δ₂ := δ₁′, and claim (b) and the background list (124), Propositions 4, 6, and 7, and (134)–(135). Definition check: 0 conflicts (4 allowed).
- **Size:** the reviewed block is 11.75k characters (25k cap). CR is 0, and there are no trailing spaces or duplicate tags.
- **Order:** after 12b-bp r2 reports.

Written 2026-11-09 07:29.

- **Update (07:36):** 14b1's pre-check rewrote #C10.3.3-11-7-1 and cited #T1.3 at #C10.3.14-2, outside this part and its context. The spec carries Cauchy ab50fa4809fd. Definition check: 0 conflicts (4 allowed).
- **Built** at 07:47 (Cauchy ab50fa4809fd, LF 56d172c27cf2, table 2396f07aafeb, LABELS 62079add07c0); the argument field, context included, is 15.4k. Launched at 07:47, after 12b-bp r2's triage.

## Verdict of cauchy-p14a-20261109-r3 (full)

- No fatal and no serious finding. One minor (M1) and three cosmetic findings (C1–C3), all valid. The round is not clean.
- Every other step is CORRECT: (B1)–(B5), the linear part at U = 1, onto-ness, (10.2), and the Galerkin identity.

## Repairs (Cauchy c495b103652a → 03f0376a8c65)

| Finding | Lines | Repair |
| --- | --- | --- |
| M1: the hypotheses of PBG Theorem 3.12 and the real-U restriction of the minimum are unstated | #C10.2.1, #C10.2.3, #C10.1.6-1 | #C10.2.1 now takes U real, satisfying Theorem 3.12's hypotheses (p.423 l.33–36) at the scale ℓ, (3.35) with α₀ small and the current bound in the place of (3.36) (#C10.3.3-6), or U the real configuration of a pair of 𝒟_j, where PBG's bounds at the scale ℓ hold (#C10.3.3-1, #C10.3.3-10). #C10.2.3: the identity uses only Q_mH₁B = B and the two inverses, so it holds on 𝒟_j with the bilinear extension; the minimum is for real U only. #C10.1.6-1: Q_n is onto wherever (Q_nG₁Q_n*)^{−1} exists, at real U under #C10.2.1 and on 𝒟_j by #C10.3.3-10. |
| C1: #C10.1.4-1-1-1 names CMP 98's results only | #C10.1.4-1-1-1 | Adds PBG's results used for Q_m (PBG is RG I's [13]), and is split at its sentence boundary: RG I's statements now form #C10.1.4-1-1-1-0 (new tag, unused before). The consumers #C10.1.3, #C10.3.34-5, and #T6.5-2 still find their claims in #C10.1.4-1-1-1. |
| C2: D̃^{(2)} = hC̃^{(2)} was worded as printed | #C10.1.3-0 | Now reads PBG (3.155)'s D̃^{(2)}, a quadratic polynomial restricted to unit blocks (p.427 l.37–38), as hC̃^{(2)}, inferred, not printed, from RG I p.267 l.29 (D̃^{(2)}(B) = C̃^{(2)}(B) for its coarse D̃) and l.38–39 (the form equals (3.156)). |
| C3: which normalisation of p.421 l.12–14 | #C10.1.8-2 | Names the second, C^{(2)}(A) = L^jηC_j^{(2)}(A) on Λ_j, which goes with H of (3.126). |

- **Re-derived:** the Galerkin identity is algebraic: with Q_mH₁B = B, (Δ₁ + DRD*)H₁B = G₁^{−1}H₁B − aℓ^{−2}Q_m*B, and ⟨A′, Q_m*ν⟩ = ⟨Q_mA′, ν⟩ for the bilinear form. So ⟨A′, (Δ₁ + DRD*)H₁B⟩ = ⟨B′, ((Q_mG₁Q_m*)^{−1} − aℓ^{−2})B⟩ needs no positivity. The minimum needs G₁^{−1} > 0, which holds at real U only.
- **Checked against the source:** #C9.8.4–#C9.8.4-3 prove (3.35)–(3.36) for Ũ on T_ε at the scale a, not for U^A_j and U^B at the scale ℓ. So #C10.2.1 cites the pair class for the backgrounds §10 uses, not #C9.8.4.
- **Hygiene:** CR 0, no trailing spaces, no duplicate tags; the longest line of §10.1–§10.2 has 599 characters.

## Next

- r4, narrow (#C10.1.3-0, #C10.1.4-1-1-1–#C10.1.4-1-1-1-0, #C10.1.6-1, #C10.1.8-2, #C10.2.1, and #C10.2.3, the rest of the part as context), as the first clean round, after 14bp r3. Then r5, full.

Written 2026-11-09 08:05.

- **Update (08:12), consumer check of M1:** #C10.3.4 uses #C10.1.6-1 with n = j at U^A, at the scale a_j, not ℓ, and "likewise" at U^B on T_{ε/L}, where neither #C10.2.1's hypotheses at ℓ nor #C10.3.3-10 apply.
  - #C10.1.6-1 now covers three cases. The first is real U under Theorem 3.12's hypotheses at the scale L^nη. The second is 𝒟_j at ℓ (#C10.3.3-10). The third is a configuration satisfying 𝒟_j's condition on 𝐔 at its scale a_j, with the current 0, so that G₁ = G₀, by BP_PBG_COMPLEX #BX.1-3 under Mα₀ + α₁ ≤ a_cx, which #C10.3.3-10's condition implies. Onto-ness follows because the range of Q_nG₁Q_n* lies in that of Q_n. The construction of X moves, unchanged, to the new tag #C10.1.6-1-1.
  - #C10.3.4 (packet 14b1): U^A satisfies 𝒟_j's condition on 𝐔 by #C10.3.14 at t = 1. That line uses no multiplier, so citing it avoids #C10.3.42, whose current bound uses B_λ. The U^B case is now #C10.3.4-0-1: by the chain rule, 𝒬(U^B) = d(M^j)(Ũ)dM(U^B) up to positive unit factors. Q₁^{pl}(U^B) is onto since T^{pl}(U^B) ≥ m_Q^{pl}/2 (#C9.4.3-4, #C9.4.5-2), and d(M^j)(Ũ) is onto by the third case, with Ũ covered by #C10.3.14 at t = 0.
  - Cauchy d901e7a1b941. r4 also covers #C10.1.6-1-1, and #C10.3.4–#C10.3.4-0-1 as a consumer.

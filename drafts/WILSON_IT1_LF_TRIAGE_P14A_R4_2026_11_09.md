# Packet 14a (Cauchy §10.1–§10.2), round 4, 9 Nov 2026

## Pre-check of cauchy-p14a-20261109-r4 (narrow)

- **Lines under review:**
  - 14a r3's repaired lines: #C10.1.3-0, #C10.1.4-1-1-1–#C10.1.4-1-1-1-0, #C10.1.6-1–#C10.1.6-1-1, #C10.1.8-2, and #C10.2.1–#C10.2.3.
  - Their consumer #C10.3.4–#C10.3.4-0-1, from packet 14b1.
  - The rest of 14a is context, with #C10.3.1-4, #C10.3.3–#C10.3.3-1, #C10.3.3-6, #C10.3.3-10, #C10.3.14, #C9.4.3-4, and #C9.4.5–#C9.4.5-2.
- **Every changed line re-read** on 9 Nov 2026 (WILSON_IT1_LF_TRIAGE_P14A_R3_2026_11_09.md, repairs and the 08:12 update).
- **Citations quoted and checked in the corrected transcriptions:**
  - PBG p.421 l.12–14: "or we take H given by (3.126), and C^{(2)}(A) equals to L^jηC_j^{(2)}(A) on Λ_j".
  - PBG p.427 l.37–38: "the function D̃^{(2)}(B) is a quadratic polynomial in B with properties similar to C^{(2)}(A), only restricted to unit blocks".
  - RG I p.267 l.29: "D̃^{(2)}(B) = C̃^{(2)}(B)". RG I p.267 l.38–39: "The quadratic form in B′ above is equal to −1/2⟨B′, Δ^{(k)}B′⟩, see the definition (3.156) [13]".
  - RG I p.299 l.13: [13] is "Propagators for lattice gauge theories in a background field. Commun. Math. Phys. 99".
  - PBG p.423 l.33–36, Theorem 3.12: "If an external gauge field configuration U satisfies both regularity conditions (3.35), (3.36) for α₀ sufficiently small, then Theorems 3.3, 3.10, 3.11 hold for the propagators G, G₁, …".
  - PBG p.396 l.19–43: (3.35) bounds |A| and |∇A| in a cube gauge, and (3.37) is the class U′U, U′ = e^{iηA′}.
  - BP_PBG_COMPLEX #BX.1–#BX.1-3 is stated for U of class (3.35), A′ in (3.37), and |𝐉| < γ(L^jη)^{−3}, under Mα₀ + α₁ + γ ≤ a_cx. At γ = 0 this is Mα₀ + α₁ ≤ a_cx.
- **Re-derived:**
  - Range: ran(Q_nG₁Q_n*) ⊂ ran Q_n, so invertibility of Q_nG₁Q_n* forces Q_n to be onto.
  - Galerkin identity: ⟨A′, Q_m*ν⟩ = ⟨Q_mA′, ν⟩ for the bilinear form, so ⟨A′, (Δ₁ + DRD*)H₁B⟩ = ⟨B′, ((Q_mG₁Q_m*)^{−1} − aℓ^{−2})B⟩ without positivity.
  - Chain rule: 𝒬(U^B) = d(M^{j+1})(U^B) = d(M^j)(MU^B)dM(U^B), with the positive scalar unit factors of #C10.3.1-4.
  - Circularity: #C10.3.14 at t = 1 needs 1 ≤ α₁/(8ρ_j), which #C10.3.14-8's 16ρ_j ≤ α₁ gives. It uses no multiplier.
- **Grep of touched claims:**
  - #C10.1.6-1's consumers are #C10.3.4 and #C10.3.4-0-1. The 14a r1 triage pointer is history only.
  - #C10.1.4-1-1-1's consumers (#C10.1.3, #C10.3.34-5, and #T6.5-2) still find their claims in it.
  - #C10.2.3's consumers in §10.4 use it on 𝒟_j, which the identity now covers explicitly.
- **No known weak point** remains in the lines under review.
- **Definition check:** 0 conflicts (4 allowed: Y_c, U₁, X, and ℓ, with X now at #C10.1.6-1-1).
- **Size:** the reviewed blocks are 4.31k characters (25k cap), and the longest line has 599 characters. The part #C10.1.1–#C10.2.3 measures 12.66k. CR is 0, and there are no trailing spaces or duplicate tags.
- **Spec:** specs\spec_p14a_r4.json (Cauchy d901e7a1b941, LF 6ac728004094).
- **Order:** after 14bp r3's triage. Rebuild at launch.

Written 2026-11-09 08:15.

- **Built** at 08:16 (Cauchy d901e7a1b941, LF 6ac728004094, table 0b9312c28f58, LABELS 0d0957612a48). The argument field, context included, is 18.3k characters. Definition check: 0 conflicts (4 allowed). Launched at 08:16, after 14bp r3's triage.

## Verdict of cauchy-p14a-20261109-r4

No fatal or serious finding. Two minor findings and four cosmetic ones, all repaired in place. Not clean.

## Repairs

| Finding | Line | Repair |
|---|---|---|
| M1: positivity of G₁^{−1} at a real pair of 𝒟_j cited to PBG Theorem 3.11, but (3.35) for e^{iεA}U₀ is not shown, and the current must be real | #C10.2.1, #C10.3.3-12 | #C10.2.1 now takes (U, J) a real pair. New #C10.2.1-0: along (e^{itεA}U₀, J), t ∈ [0, 1], all real pairs of 𝒟_j, G₁(t)^{−1} is symmetric, invertible by the series (3.138), and continuous; positive at t = 0 by the first case, so positive at t = 1. New #C10.2.1-0-1: U₀ satisfies (3.35) at the scale ℓ (cube containment, κ′ ≤ max(10M, κ/L + 2M) ≤ Lκ), and the current bound α_Ja_j^{−3} ≤ α_Jℓ^{−3}. #C10.3.3-12, which claimed the positivity from p.416's smallness, is deleted. |
| M2: RG I p.254 l.7–8 is for (0.12), the bridge l.9–10 is not cited, and PBG's transfer rests on an assertion printed without proof | #C10.1.4-1-1-1, #C10.1.4-1-1-1-0 | The CMP 98 results are taken by p.254 l.7–10 (#C10.1.4-0-3, which already quotes l.9–10). PBG's results are taken by p.253 l.42–43, now called an assertion printed without proof. #C10.1.4-1-1-1-0 merged into #C10.1.4-1-1-1 (it restated #C10.1.4-0-3). |
| C1: RG I (2.11) not cited | #C10.1.3-0 | Cites (2.11), p.267 l.35, with the term ⟨H₁hC̃^{(2)}(B′), J⟩, in the place of l.29. |
| C2: case (c) omits M ≥ M₃ and the strict inequality | #C10.1.6-1 | Under M ≥ M₃ and Mα₀ + α₁ + α_JL^{−3} ≤ a_cx, the current 0 lying strictly inside its bound. |
| C3: hypotheses are a variant of Theorem 3.12's; M large implicit | #C10.2.1 | "the variant of the hypotheses … with the current bound in the place of (3.36)", and "(3.35) with M large and α₀ small". |
| C4: "orthogonal" on 𝒟_j | #C10.2.3 | "orthogonal" read as annihilated in the bilinear pairing. |

## Re-derived

- M1: G₁(t) is the Neumann series (3.138) inverting the form operator at (e^{itεA}U₀, J), which lies in 𝒟_j since |tA| < α₁/a_j and |t∇A| < α₁/a_j². At a real pair the form operator is real and symmetric, and analytic in t (#C10.3.3-10). On a finite torus its eigenvalues are continuous and never 0, and all are positive at t = 0.
- Cube containment: a cube of side κℓ (κ ≥ 10M) lies in a union of big blocks of side Ma_j of side at most κℓ + 2Ma_j, enlarged to at least 10Ma_j. So κ′ ≤ max(10M, κ/L + 2M), and 10M ≤ Lκ and κ/L + 2M ≤ κ/L + κ/5 ≤ Lκ for L ≥ 2. The bounds then need κ′/a_j ≤ κ/ℓ and κ′/a_j² ≤ κ/ℓ², that is κ′ ≤ Lκ and κ′ ≤ L²κ.
- C2: BX with current bound γ = α_JL^{−3} > 0 contains the current 0 strictly, and Mα₀ + α₁ + γ ≤ a_cx is #C10.3.3-10's condition.
- Grep: #C10.3.3-12 and #C10.1.4-1-1-1-0 are cited only in review snapshots and in this round's spec. Packet 14b1's range loses #C10.3.3-12.

## Repaired SHAs

Cauchy d226af81ac1b (also carries the packet-15 deletions #C10.4.7-1, #C10.4.7-2, #C10.4.7-6, #C10.4.40, and #C10.4.62-2, and the trimmed #C10.4.7-7).

## Next

- r5, narrow: #C10.1.3-0, #C10.1.4-1-1-1, #C10.1.6-1, #C10.2.1–#C10.2.1-0-1, and #C10.2.3, the rest of 14a as context, with #C10.3.3–#C10.3.3-11-8-1.
- r6, full.

Written 2026-11-09 08:30.

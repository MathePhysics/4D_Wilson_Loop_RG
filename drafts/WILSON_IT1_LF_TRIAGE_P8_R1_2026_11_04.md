# LF Packet 8, Review 1: Triage

Review: verification\isolated_reviewer\reviews\lf-p8-20261104-r1\review.md (LF 1ce1241e341b, table 3d5b823a0a37, labels 8a9b2c7efa17). Verdict: "NOT ESTABLISHED AS STATED". There is no fatal item, two serious items, and seven minors. All items are repaired. LF after the repairs: f06d4cbef4a8 (labels 27c896f0548e).

## Serious

1. **F1, #0.1.26 with #0.1.29 and (K2)–(K6): the modified v_{x̄} = χ̃E − ∂₁*Δ^{−1}r_χ + ∂₁*Δ^{−1}(χda) has ∂₁*v_{x̄} = ∂₁*(χ̃E) ≠ 0, which the λ-equation Δλ = −σ omits.** It is of size up to θ_B next to Λ₀.
   - v_{x̄} = ∂₁*Δ^{−1}(χF) is now kept in VAR's problem, so ∂₁*v_{x̄} = 0 and σ = ∂₁*u − ∂₁*w_{x̄}, as in the N_b problem.
   - Its E-part is bounded pointwise: ∂₁*Δ^{−1}(χdE) = χ̃E − ∂₁Δ^{−1}∂₁*(χ̃E) − ∂₁*Δ^{−1}r_χ.
   - The kernel of ∂₁Δ^{−1}∂₁* consists of second differences of the Green's function, O(max(abs(x − y), 1)^{−d}), on a support of diameter O(L). So the E-part is ≤ C(d)(1 + log L)²θ_B.
   - #A.15 (K4) now uses this bound, with the split applied to ∂₁*Δ^{−1}(χda).
2. **F2, #0.1.26 and #A.11.42: no interior bound at the scales ≤ R/2 in VAR's problem or for V_L.** The new paragraph *VAR's interior bound.* in #0.1.26 supplies it:
   - On the bonds of Q_{2R}(y), ∂₁*∂₁A_N = h_Q := Q*μ, by ⟨∂A_N, ∂t⟩ = ⟨μ, Qt⟩ (#A.8), and ∂₁*A_N is block-constant (#0.1.29).
   - The N_b interior bound then runs with ∂₁*∂₁ for Δ_j, T the Laplacian, h_Q for h₀ and h₁, and ω_{g′} = ψ₃ = 0. It gives sup_{Q_{R/2}(y)}abs(F) ≤ C(d)(R^{−d/2}‖F‖_{Q_{2R}(y)} + R sup abs(h_Q)).
   - The bumps β_c of #A.8 give μ(c) = ℓ_E(β_c) + ⟨da, dβ_c⟩ ≤ C(d)(1 + log L)^pL^{d−3}θ, by (b) and (f).
   - Q's weight on a bond is ≤ C(d)L^{1−d}, so abs(h_Q) ≤ C(d)(1 + log L)^pθ/L² and R²sup abs(h_Q) ≤ C(d)(1 + log L)^pθ.
   - With abs(dE) ≤ C(d)(1 + log L)θ_B/t on Q_{2R}(y), the scales ≤ R/2 of the dyadic sum of da add at most the term of the scale 2R plus a source term of the bulk size.
   - V_L at Λ_j/Λ_{j+1} is treated in the same way, with Δ_j, T = Δ_j + ∂₁∂₁*, the equation of 𝒫₁ and its source from c_D, ℓ_E of (g)(4), and (f) for V_L.

## Minor

- F3a: #0.1.25 now defines Δ := ∂₁∂₁* + ∂₁*∂₁ ≥ 0 for #0.1.25–#0.1.26, minus the scalar Δ of #A.10.
- F3b: the vacuous t(y) ≤ 31L step is removed. The weight is ≥ 1, since t and t₃ are capped at L (#0.1.18).
- F3c: #A.10 now states the regions where (K0) bounds ‖A‖_{Q_{2L}(x₀)}. It also says the curvature enters through F₁, the E-part of v_{x̄}, and VAR's interior bound.
- F3d: #A.11.50 now reads λ̂_j and ηω^f_j as gauge parameters in the units of the layer j (#A.9).
- F3e: #0.1.30 now states B₀'s role in VAR p.285 l.27 (checked against the corrected transcription, l.27), and cites the list at #0.1.14.
- F3f: #0.1.29's "not merged" sentence now reads "t₃ is, as in the N_b problem, …".
- F3g: in #A.11.42, t₃ for W_j counts only the contacts in ∂Λ_{j+1}; the pinches of Ω_j next to Λ_{j−1}, outside R_j, are not counted.

## Review 2

Review: verification\isolated_reviewer\reviews\lf-p8-20261104-r2\review.md (LF f06d4cbef4a8, table 3d5b823a0a37, labels 27c896f0548e). Verdict: "ESTABLISHED with minor gaps". There is no fatal or serious item, so this is the first clean pass. All five minors are repaired. LF after the repairs: d9e10bc45f12 (labels 26486d87f712); table c64debe8ab80.

- m1: *VAR's interior bound.* now states that for a site y of Λ₀ with t(y) ≥ 4√dρ₀, Q_{2R}(y) contains only data bonds, and that *The massive case.* concerns the N_b problem only.
- m2: the V_L paragraph now states the equation, the multipliers, and the tails, in-line in the same paragraph.
- m3: #0.1.26 and #A.10 now list where dE enters: the E-part of v_{x̄}, the pointwise bound on the free plaquettes, *VAR's interior bound.*, and the source ℓ_E of the hole-filling (#0.1.30).
- m4: #A.11.50 now says that λ̂_j and ω^f_j are potentials for the plain difference ∂, and states their bounds for ηλ̂_j and ηω^f_j in the units of the layer j (#A.9).
- m5: in table row #T11.17, t₃ now uses the contacts of codimension ≥ 2 in both problems, and B₀'s role is given by the full list of #0.1.14 and #0.1.30.

## Review 3

Review: verification\isolated_reviewer\reviews\lf-p8-20261104-r3\review.md (LF d9e10bc45f12, table c64debe8ab80, labels 26486d87f712). Verdict: "ESTABLISHED with minor gaps". There is no fatal or serious item, so this is the second consecutive clean pass, and packet 8 is DONE. All five minors are repaired. LF after the repairs: c5e4d4d49619 (labels f9bcc174bdc1); table 171f3732420b.

- n1: #0.1.26's list of where dE enters now includes H_E in F₁ (#0.1.25), bounded through sup abs(E).
- n2: in the V_L paragraph of *VAR's interior bound.*, μ now carries the linearised constraints Q̃^{(1)} = Q^{(1)} − D̄K (#A.8). The tails are split: from Ω_j, where (1)–(6) bound V_L polynomially in L, they are ≤ L^{−10} times the bulk size; from Ω_j^c, at distance ≥ RM/4 from R_j and bounded with Bałaban's C(L) of (s3), they are ≤ C(L)e^{−c(d)RM/4}θ_B, which RM chosen after L absorbs.
- n3: #A.9 now has *At the interfaces.*, with g_♮ := ge^{−iηω_♮^{im}}, ω_♮^{im} the ω_♮ for the data i Im B.
  - g_♮ = 1 on Λ₀, and ‖Ad(g_♮)‖ ≤ 1 + C(L, M)ε₁.
  - g_♮^{−1}∂_sg_♮ = iη(ω′_0 − ω_♮^{im}) at s = 0, so the first-order part of u_R^{g_♮^{−1}} is A_♮.
  - The second-order terms are ≤ C(L, M)ε₁², by Cauchy's bound in s.
  - #0.1.30 cites it.
- n4: #A.11.50's quotation of (iii) now has the factor L^{d/2} per layer of (f), a C(L) on Λ_j ∪ Λ_{j+1}.
- n5: table #T11.17 now has "the faces, edges, and vertices of Λ" for "the strata of Λ".

## Review 4

Review: verification\isolated_reviewer\reviews\lf-p8-20261104-r4\review.md (LF c5e4d4d49619, table 171f3732420b, labels f9bcc174bdc1). Verdict: "ESTABLISHED with minor gaps". There is no fatal or serious item. n1–n5 are resolved, and n3's #A.9 *At the interfaces.* is checked. All five minors (wording) are repaired. LF after the repairs and the split below: fb9b8af212b4 (labels 7b85d19c9162); table unchanged.

- p1: #0.1.26.3's list of where dE enters now separates H_E in F₁ (bounded through sup abs(E)) from the pointwise bound on the free plaquettes and ℓ_E(β_c) in the multipliers (#0.1.26.4, #0.1.26.5).
- p2: #0.1.30 and #A.9.6 now say that the chain uses A_♮ for the complex part of the data (#0.1.11). At s = 0 the representative is u_R(Re B)^{g₀^{−1}}.
- p3: #A.9.6 now reads abs(ηω_♮^{im}) = abs(ηω_♮(Im B)) ≤ C(L, M)ε₁, by the sup-to-sup bounds of #A.11.50 at the real background.
- p4: #A.11.50 now gives the reason the factor L^{d/2} is a C(L): the cubes Q_{4+5k}(x) of (iii)(δ) have radius < RM/5, and supp χ_j lies ≥ 3RM/8 from Λ_{j−1} and ≥ r₂ + RML/8 from Λ_{j+2}.
- p5: #A.11.42 now has L/2 − ½ for the centre planes of the blocks of Λ_{j+1} (as in #0.1.19). The blocks of the scales ≥ j + 2 lie in Ω_{j+2}, ≥ RML from the interface, where W_j = (1 + log L)^p.

## Layout

The packet-8 repairs had been appended to existing paragraph lines. #0.1.26 (14.1k chars) and #A.9 (13.7k chars) are now split into tagged blocks, with the wording unchanged except for p1–p3:
- #0.1.26 into #0.1.26 and #0.1.26.1–#0.1.26.6: the v_{x̄} bound, *The interior bound.* (two blocks), VAR's E-part, *VAR's interior bound.*, V_L, and *The massive case.*;
- #A.9 into #A.9 and #A.9.1–#A.9.7: the first-order ω, its weighted bound, its pointwise bound, *The exact transformation.*, *At the complex backgrounds.*, the ODE bound, *At the interfaces.*, and the maximum-principle remark.

The blocks are 0.2k–3.3k chars. Internal citations are retargeted (#0.1.21 → #0.1.26.1, #0.1.25 → #0.1.25–#0.1.26.6, #A.13 (K2) → #0.1.26.6, #A.15 (K4) → #0.1.26.3, #0.1.30 → #A.9.6). The citations of #A.9 as a whole in the table and the two-loops note still hold.

## Status

Packet 8 is DONE: r2, r3, and r4 are clean in a row.

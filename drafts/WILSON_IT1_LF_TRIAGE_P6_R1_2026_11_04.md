# LF Packet 6, Review 1: Triage

Review: verification\isolated_reviewer\reviews\lf-p6-20261104-r1\review.md (LF 3a128b6a24e7, table 3d5b823a0a37). Verdict: "Not established as stated". There is no fatal item, two serious items, and twelve minors. All are repaired. LF after the repairs: bbab4389fda1 (labels 7ad560e0567f).

## Serious

1. **S1, #A.11.29: w_G was undefined and its decay underived.** w_G is removed. (1) now defines Z := A_N − H_jV_N ∈ ker Q_j and derives two identities.
   - ⟨dZ, dφ⟩ = 0 for every φ ∈ ker Q_j supported at distance ≥ 2√d from Ω_j^c. The reason is that A_N + tφ satisfies all the constraints of A_N and Q_j(H_jV_N + tφ) = V_N.
   - ⟨dZ, dH_jD⟩ = 0 for every scale-j field D.

   (1) also constructs a local right inverse b_c of Q_j from PRT1's path average (p.20). It is supported within 1/4 of the face of c, and abs(b_c), abs(∂b_c) ≤ C(d).

   #A.11.30 now gives the exact source of the V-problem, ⟨V_N, Δ_jD⟩ = ⟨dA_N, dc_D⟩. Here c_D := (1 − χ)H_jD + Σ_c(Q_j(χH_jD)(c) − D(c))b_c, and c_D is exponentially small from supp D. The phrase "up to the finer constraints" in #A.11.23 and #A.11.30 is replaced by dZ_j of (6)(iii). #A.11.32 now reads the Ω_j^c fields through the kernels of H_j and c_D.
2. **S2, #A.11.46: the Combes–Thomas argument of (i) needed a globally least ν.** (iii) is rewritten. Z_j := A_N − H^Λ_jV_N lies in ker Q_j, dZ_j = dZ, and ∂*Z_j = q_y is constant on the scale-j blocks of Ω_j. The new argument has four steps.
   - (α) For finitely supported u ∈ ker Q_j, ‖u‖ ≤ γ₀^{−1/2}‖du‖ + C(d)‖(1 − P_𝔫)∂*u‖. The proof gauges u into R∂*u″ = 0 on a torus T_η by λ = Δ^{−1}R∂*u ∈ N(Q′) (PRT1 p.33), uses PRT1 (1.90), and adds the per-block Poincaré bound.
   - (β) Hole-filling with the test η_r²Z_j − Σ_cQ_j(η_r²Z_j)(c)b_c gives E(Q_r) ≤ θE(Q_{r+5}) with θ = θ(d) < 1.
   - (γ) The strong form is ΔZ_j = Q_j*ω + ∂q, with abs(ω(c)) ≤ C(d)‖dZ_j‖ and abs(q_y) ≤ C(d)‖Z_j‖_y. The Green's function of the fine lattice (Lawler–Limic Theorem 4.3.1, p.81, and Corollary 4.3.3, p.84) then gives abs(Z_j(b)) ≤ C(d)E(Q_4(b))^{1/2}.
   - (δ) Iterating over ⌊RM/(25√d)⌋ − 1 steps gives E(y)^{1/2} and sup_y abs(Z_j) ≤ C(L)e^{−c(d)RM}(ℳ + 1)θ at distance ≥ RM/4 from Ω_j^c, with the factor L^{d/2} per layer beyond Λ_j.

   The bound no longer depends on w_G, so the strip RM/8–RM/4 no longer enters. (v) carries ‖Z_j‖_{Q_{2L}(x)}, and #A.11.50 now bounds Z_j on supp χ_j for (5).

## Minor

1. **m1, the rates.** (1) now defines δ_H = c(d) as the Combes–Thomas rate of H_j, dH_j, and Δ_j. The downstream rates are δ_H/2 for M̃, δ_H/4 for σ̃, δ_H/8 for h and the commutators of (4), δ_H in (2), (3)(ii)–(iii), and (4), and e^{−δ_H(RM − 3√d)} for the V-problem sources.
2. **m2, (3)(iii)(A).** The odd representative now comes from the axial potential ū′ of ∂₁ū, which has zero normal components and zero tangential components on the plane. Uniqueness makes it odd, and ‖ū′‖ ≤ C(d)R‖∂₁ū‖. Then ū − ū′ = ∂g with g odd, ũ := ū′ − ∂μ, and λ := g + μ on H₊.
3. **m3, the limit N → ∞.** #A.11.35 now passes the equation to the limit. Pointwise convergence covers the plaquettes within N^{1/2}, and the tail of σ̃ (e^{−c(d)N^{1/2}}) covers the rest, against ‖F^N‖² ≤ γ₀^{−1}γ₁‖∂₁V_f‖², which is uniform in N.
4. **m4, the crossing bonds in (2).** They now have the ρ_j-length 1 of their finer endpoint (#A.9). The near-pair distance is ≤ C(d)(r + 1)/L + 2.
5. **m5, the normalisation.** (s2) now states that local ℓ² norms in the units of L^j use the measure L^{−dj} of a fine bond, as for ℳ. (iii) states the same.
6. **m6, #0.1.21 in (3)(ii).** (3)(ii) now says that only the symmetric-kernel identity and the kernel decay are used.
7. **m7, the distance.** (s1) now notes that PBG p.397 l.29 cites PRT2 (2.46) as "(2.36) in [4]".
8. **m8, (3.133).** (s1) now cites (3.35) and (3.36) (p.396), both trivial at A = 0, and (3.132) (p.422).
9. **m9, 𝒫_d.** (i) and (iii) now cite Lawler–Limic p.10 for simple random walk ∈ 𝒫_d.
10. **m10, "Q′_jζ = 0".** The sentence is removed with w_G.
11. **m11, (iv).** The source is now explicit: ⟨V_N, ∂₁λ′⟩_♯ = ⟨g_Z, ∂₁λ′⟩ + ⟨f_Z, λ′⟩. Here g_Z := −(H^Λ_j)*Z_j, and f_Z comes from the correction λ̃ of the lift on Ω_j^c, which lies in N(Q′): block-mean bumps on the layers Λ_{j′}, 1 ≤ j′ < j, and 1_{Λ₀}λ̂ on Λ₀, where N(Q′) vanishes. Both are ≤ C(L)e^{−c(d)RM}(ℳ + 1)θ on Ω_{j+1}. The weighted bound on λ″_j carries these terms, and (v) absorbs them.
12. **m12, (2).** "Δ_j∂ = 0" now reads Δ_j∂₁ = 0.

## Packet 8 pre-check repairs, applied with these

- #0.1.29: "the mass term of E(Q_r) (#0.1.20)".
- #0.1.30: "the free bonds of supp χ_f ((K0)(b))", and A_♮ = A_N at the points of R₀ outside the blocks of Λ₁ that meet R₁.
- #A.11.42: t and t₃ for W_j; the averages of W_ms per block of Λ_i, with the exception near Λ_{i+1} read in supremum (#A.11.43); the set where (KW) holds (Q_{48L}(x̄) ⊂ R_j); and the reading of V_L by H^Λ_j off that set.

## Next

lf-p6-20261104-r2 on LF bbab4389fda1 (labels 7ad560e0567f).

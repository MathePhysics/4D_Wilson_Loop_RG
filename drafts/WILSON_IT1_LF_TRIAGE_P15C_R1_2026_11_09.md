# Packet 15c (Cauchy #C10.4.108–#C10.4.124-1), round 1, 9 Nov 2026

## Pre-check of cauchy-p15c-20261109-r1 (full)

- **Under review:** every line of #C10.4.108–#C10.4.124-1. The context is §10.4's first and second parts (#C10.4.1–#C10.4.14-2, #C10.4.46–#C10.4.62-1, #C10.4.66–#C10.4.66-5, #C10.4.87–#C10.4.92, #C10.4.106–#C10.4.107), plus #C10.3.40–#C10.3.51-1, #C10.3.36, #C10.3.3-10–#C10.3.3-11-8-1, #C10.1.3-3, #C10.1.4-0-1, #C10.1.4-3, #C9.5.4, and #C9.7.1-16.
- **Read in full:** every line of the part.
- **Re-derived:**
  - **#C10.4.111-3.** Tent overlaps along a column: the diagonal is (2L³ + L)/(3L³) and the off-diagonal sum is (L³ − L)/(3L³). Their difference, (L³ + 2L)/(3L³), is ≥ 1/3, so m_Q = 1/3.
  - **#C10.4.112-2.** The IMS identity Σ_iχ_iT_Qχ_i + ½Σ_i(χ_i(c) − χ_i(c′))²T_Q(c, c′) = T_Q follows from Σ_iχ_i² = 1. Since T_Q(c, c′) = 0 for d_ε(c, c′) > r_T and each point lies in at most 2^d boxes, Schur's test bounds the remainder by ½·2^dC_χ²r_T²R_Q^{−2}sup_cΣ_{c′}|T_Q(c, c′)|. This is C_E/R_Q², with C_E a constant of L and d.
  - **#C10.4.113-1.** Neumann series: the spectrum lies in [m_Q/2, M̃_Q], so ‖1 − T_Q/M̃_Q‖ ≤ q_T. The n-th term has range nr_T, which gives the decay rate δ_Q = r_T^{−1}log(1/q_T) and the prefactor M̃_Q^{−1}(1 − q_T)^{−1} = 2/m_Q.
  - **#C10.4.113-3–#C10.4.113-7.** The column total is 1 + ½(1 + 3dL^{d−1} + L^{d−1}) ≤ 2(1 + 2dL^{d−1}). CMP 98 (109)'s α₀ is the plaquette bound itself (p.034), so L²α₀ = ε²|F| with α₀ = (ε/L)²|F|.
  - **#C10.4.114–#C10.4.114-2.** Under δ₁ ≤ 1/(10d), e^{½δ₁·5d} = e^{1/4} < 4/3, and 3^γ·4/3 < 4 for γ < 1.
  - **#C10.4.116-1.** 4^{2γ_H} = 16^{γ_H}. Dividing ℒH₁^Ae_y by C_ℒ′(2γ_H) leaves the sup and gradient bounds with B₀ and the oscillation bound with B₀(2γ_H) + B₀, which are the inputs of C_β^ℒ and C_gf^ℒ (#C10.4.117-3). The fields H₁^Be_y satisfy the same bounds because B₀(2γ_H) ≤ B₀(2γ_H) + B₀ and C_β and C_gf are increasing.
  - **(A1), #C10.4.117–#C10.4.118.** (10.5′) (#C10.4.107) gives |⟨B, (P_B − P_A)B⟩| ≤ max(|β(𝒜^B, 𝒜^B)|, |β(ℒ𝒜^A, ℒ𝒜^A)|). Expanding over y, the brackets of (10.6a) (#C10.4.60) and (10.6b) (#C10.4.90) at exponent 2γ_H are each ≤ 2(ε/ℓ)^{2γ_H}, by ε/ℓ ≤ (ε/ℓ)^{2γ_H}, ε₁ ≤ 1, C₀ε₁ ≤ 1, and L^{−2}, L^{−3} ≤ 1. Normalising ℒ𝒜^A gives the factor C_ℒ′(2γ_H)² ≥ 1. Hence r_β = 2C_ℒ′(2γ_H)²[C_β^ℒ(2γ_H) + C_gf^ℒ(2γ_H)](ε/ℓ)^{2γ_H}.
  - **#C10.4.119-1.** For symmetric T, ⟨u + v, T(u + v)⟩ − ⟨u − v, T(u − v)⟩ = 4⟨u, Tv⟩. With B = u ± v, (A1) has Σ_{z,z′}|B(z)||B(z′)|e^{−¼δ₁d(z,z′)} ≤ 4, so each form is ≤ 4r_βB₀ℓ^{−2}ℓ^d. Then |⟨u, Tv⟩| ≤ 2r_βB₀ℓ^{−2}ℓ^d, and ⟨e_y, Ke_{y′}⟩ = ℓ^{2d}K(y, y′) (#C10.4.62-1) gives the kernel bound 2r_βB₀ℓ^{−2}ℓ^{−d}.
  - **#C10.4.120.** Both pairs are real (#C10.4.1-1), so (3.132) holds with B₀ and δ₁ (#C10.3.3-10, #C10.1.3-3). The difference of the two runs' kernels is therefore ≤ 2B₀ℓ^{−2}ℓ^{−d}e^{−δ₁d}.
  - **(A2), #C10.4.121.** min(u, v) ≤ (uv)^{1/2} gives 2r_β^{1/2}B₀ℓ^{−2}ℓ^{−d}e^{−½δ₁d}. Then 2r_β^{1/2} = 2√2C_ℒ′(2γ_H)[…]^{1/2}(ε/ℓ)^{γ_H}, with 2√2 < 3 and (ε/ℓ)^{γ_H} = L^{−γ_H(j−1)} (#C10.4.62-1).
  - **#C10.4.122.** (10.3) (#C10.3.43) divided by B₀ℓ^{−2}ℓ^{−d}, with ρ_j = C_G(ε₀)L^{−(1−ε₀)j}ε₁ (#C9.7.1-16), ε/a_j = L^{−j} ≤ L^{−(1−ε₀)j}, and 1/α₁, 1/α_J ≤ 1/α_*, gives [16C_G(ε₀) + 8x_J(C_G(ε₀) + 1)]((B₀^{cx} + a + C_𝐉 + C_𝐆)/B₀)ε₁L^{−(1−ε₀)j}/α_*. Its rate is δ₁′ = δ₂ ≤ δ₁/8 < ½δ₁ (table #T10.50), so (A2)'s decay dominates e^{−δ₂d}.
  - **#C10.4.123.** r_j is the sum of the two coefficients, which gives C(ε₀, γ_H) as stated.
  - **#C10.4.124.** #C10.3.51 lists #C10.3.36, so 14b2's repaired conditions (c₁₂₄C₀ε₁ ≤ 1/16, §E's α₀, C₁^{(123)}ρ_j ≤ 1/64, and c_wρ_j < π) reach (10.6) through §10.3. The ½-condition of #C10.4.113-6 follows from 16c₁₂₄C₀ε₁ ≤ 1.
- **Repairs in this pre-check:**
  - **#C10.4.123.** C(ε₀, γ_H) had a trailing "+ 1" that no step produces and no consumer needs (#C6.2.7, #CK.1-18). Deleted.
  - **#C10.4.124.** "ε₁ small enough for the conditions listed after (10.3)" omitted that #C10.3.51-0-1's conditions are on M_P, α₀, and α₁. It now reads "under the conditions of #C10.3.51–#C10.3.51-0-1 (those on ε₁ for all j, by ρ_j ≤ C_G(ε₀)ε₁)".
  - **The Gram operator.** #C10.4.43 already uses T for Ad(U^B(γ_{p′})) in §10.4, so the Gram operator Q₁Q₁* is renamed T_Q in #C10.4.110-1, #C10.4.111, #C10.4.111-3, #C10.4.112-2–#C10.4.112-5, #C10.4.112-7, #C10.4.113-1, #C10.4.113-2, and #CK.1-27. #C10.4.119-1 now binds its T ("for a symmetric T, at T = P_B − P_A").
  - **LF #4.244-2** carried "{#D.C_Q} C_{Q*} := 2(1 + (2d + 1)L^{d−1})", a misnamed tag restating Cauchy #C5.6-5, which clashed with #C10.4.113-2's C_Q. It now cites C_{Q*} from #C5.6-5. The line, about 1,300 characters, is split at sentence boundaries into #4.244-2–#4.244-2-3. The consumers are re-pointed: the LF line citing "added in #4.244-2" now cites #4.244-2-1, and the C_mem line's "C_{Q*} (#4.244-2)" now cites #C5.6-5.
  - **W-δ #W8.15-3** now cites C_{Q*} (#C5.6-5) and C_φ (LF #4.284.2-1) without restating their values.
- **Messages to the table fork:**
  - #T12.7-31's C(ε₀, γ_H) lacked the factor (B₀^{cx} + a + C_𝐉 + C_𝐆)/B₀. The fork fixed it at table 862a80d8ea69.
  - The LF relabel removed {#D.C_Q}. #T3.13 now carries C_{Q*} from #C5.6-5. #T4.14 now distinguishes W-δ's C_ℒ′ (table eb8a5723c2b2, LABELS a913f25dfc3f).
  - #T12.7-28 now reads "T_Q := Q₁Q₁* on the coarse bond fields (#C10.4.110-1)" (table 1e464ebebe51, LABELS 3076a41eaa7c).
- **Definition check:** 0 conflicts (2 allowed: C_ℒ′ versus #T4.14, and the local letter g).
- **Size:** 9.81k before and after (25k cap). Every line is ≤ 578 characters, with no duplicate tags.
- **Spec:** specs\spec_p15c_r1.json (Cauchy b3ae2ca96d3a, LF 029a1d03a304). Update it to the current SHAs at launch.
- **Order:** queued after the rounds listed in the packet plan.

Written 2026-11-09 09:59.

## Round 1, Reviewed by Me in Place of the Referee

- **How:** at the user's request, no referee was launched. I read every line of #C10.4.108–#C10.4.124-1 and its context, with CMP 98 (121)–(126) and Proposition 3 (p.036).
- **Verdict:** not clean; four minors and three cosmetics, all repaired.
- **m1, #C10.4.109-5.** The oscillation bullet compared values carried by the interpolation's transports with oscillations of the Hölder quotients (#C10.4.14-3). Added: the passage, along a fine contour within δ_T of 1 and a coarse one of at most 6d links each within δ_T of 1 (#C10.4.9-2-1), costs at most (6d + 3)δ_T sup|∇g| ≤ 288d³ν_F𝔰′, with 4d + 256d² + 288d³ ≤ 4C_tr.
- **m2, #C10.4.110.** The Taylor bound carried the second differences' transport term without their total weight C, and it omitted the non-main terms of CMP 98 (124). Now |g − Q₁Ig| ≤ max(C, 1)(ε²|∇∇g| + C_trε²|F||g|), with 4Cδ_T + 2δ_T + c₁₂₄ε²|F| ≤ max(C, 1)C_trε²|F| (#C10.4.110-0, split at 692 characters). C_I already carries max(C, 1).
- **m3, #C10.4.112-5 and #C10.4.112-7.** The axial-gauge bound on T_Q(U^B) − T_Q(1) holds only on the fields supported in the box. It is now stated there, for the forms ⟨χ_iν, ·χ_iν⟩. C_ax depends on G through c₁₂₄.
- **m4, #C10.4.122.** (A2)'s rate ½δ₁ was not shown to be ≥ δ₂ = δ₁′, since δ₁ is reduced after δ₁′ is fixed (#C10.4.124). Now δ₂ := min(δ₁′, ½δ₁) (#C10.1.3-3), and #C10.4.122, #C10.5.1-1, and #CK.1-24 are changed to match. A smaller δ₂ only enlarges c_{δ₂}, a constant of d and the rates.
- **Cosmetics:**
  - #C10.4.122 now cites #C10.4.105 for the J-terms.
  - #C10.4.124 now asks B₀(2γ_H) ≥ 9B₀ as well, for #C10.4.8-2-1 at the exponent 2γ_H (#C10.4.116-1).
  - #C10.4.124-1's list now includes G and CMP 98.
- **Re-derived:** (6d + 3)·32d² ≤ 288d³ for d ≥ 1. And (4C + 2)·32d² + c₁₂₄ ≤ 192max(C, 1)d² + c₁₂₄ ≤ max(C, 1)(1000d⁴ + 2dc₁₂₄).
- **Consumers in W-δ** (7278da3ec2e3):
  - #W10.1.17-1 and #W10.5.17: max(C₁, 1) on the transport term, with C₁ defined at #W10.1.17-1;
  - #W10.5.27 and #W12.76-1: the transport term (6d + 3)·32d²ε²|F|sup|∇_Au| ≤ 576d³ε|F||u| by |∇_Au| ≤ 2|u|/ε, with 4d + 256d² + 576d³ ≤ 4C_tr;
  - #W10.5.28, #W10.5.28-1, #W11.18, and #W12.72: max(C, 1) on the transport term.
- **Table (fork):** #T3.27 and #T12.7-23 say δ₂ = δ₁′, and #T12.15 says "not #T3.27's δ₂ = δ₁′".
- **Next round:** r2, full, at Cauchy 282155b15f71.

Written 2026-11-09 16:41.

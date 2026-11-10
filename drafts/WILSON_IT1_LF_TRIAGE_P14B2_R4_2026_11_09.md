# Packet 14b2 (Cauchy #C10.3.17–#C10.3.51-1), Round 4, 9 Nov 2026

## Pre-Check of cauchy-p14b2-20261109-r4 (Narrow)

- **Under review:** #C10.3.29-2; #C10.3.31-1–#C10.3.32; #C10.3.34-3–#C10.3.36-1; #C10.3.39–#C10.3.40; #C10.3.51–#C10.3.51-0-2. These are the lines repaired after round 3 (M1–M5 and the nit, WILSON_IT1_LF_TRIAGE_P14B2_R3_2026_11_09.md) and their consumers in the packet. The rest of 14b2 is context.
- **Every line under review re-read** at Cauchy a0464784c8bc (lines 1918–1980). Since round 3, the only changes in these lines are bookkeeping:
  - the BCH radius is renamed r_{BCH} in #C10.3.34-7, #C10.3.36, #C10.3.51-0-1, and #C10.3.51-0-2;
  - #C10.3.51-0-2's range is re-pointed to #C10.3.3-10-0–#C10.3.3-10-0-2.
- **Re-derived:**
  - **#C10.3.31.** The adjoint of the difference of the covariant differences over the 2d bonds at a site gives 2d·(L^{i+1}η)^{−1}·2c_vL^{i+1}η sup|A| = 4dc_v sup|A|.
  - **#C10.3.31-1.** (ii) with ν = μ′_{i+1} − μ_{i+1} gives the defect L^{d−1}L^{i+1}η·4dc_v sup|A| sup|μ_{i+1}|.
  - **#C10.3.31-2.** The weights total 1 + 2dL^{d−1} + L^{d−1} ≤ (2d + 2)L^{d−1}. The bracket of BP #C10.3.21-4 has norm ≤ x + (1 + x)³ − 1 = 0.549 ≤ 5/8.
  - **#C10.3.31-3.** A transport along ≤ (2d + 1)L bonds changes by ≤ (2d + 1)Lv, and its Ad by twice that. The loop h has ≤ (d + 2)L ≤ (2d + 1)L bonds.
  - **#C10.3.31-3-1.** 4(9/8)³k_G² + 2(9/8)⁴ ≤ 5(9/8)⁴k_G² by k_G ≥ 2, and 5(9/8)⁴ = 8.01 ≤ 9 gives c_D.
  - **#C10.3.32.** Unrolling with the products ≤ 2, sup|μ_{i+1}| ≤ 2 sup|μ|, and Σ_{i<n}L^{i+1}η ≤ 2a_j gives 8(c_D + 4d)c_vL^{d−1} = C′_Q.
  - **#C10.3.34-3.** For normal u the numerical range is the convex hull of the eigenvalues, which gives the eigenvalue-angle characterisation. Re⟨g*v, hv⟩ = Re⟨v, ghv⟩.
  - **#C10.3.34-4–#C10.3.34-6.** θ_0 ≤ 4L^{−j}ρ_j from a_j sup|A′*| ≤ 4ρ_j. Σ_{i<j}L²α₀^{(i)} = 4C₀ε₁Σ_kL^{−2k} ≤ (16/3)C₀ε₁. The induction θ_{i+1} ≤ 2L^{i+1}θ_0 ≤ 8L^{i+1−j}ρ_j uses Σ Lθ_i ≤ 16ρ_j.
  - **#C10.3.34-7.** By (0.10), |Z| ≤ a_i/(1 − c_Ba_i) ≤ (4/3)a_i under 32c_Bdρ_j ≤ 1, and (4/3)·8dρ_j ≤ (2/3)r_{BCH} under 16dρ_j ≤ r_{BCH}.
  - **#C10.3.34-7-1–#C10.3.35.** Σ_{i<j}L^{i−j+1} ≤ 3/2 for L ≥ 3. So |(1/i)log w| ≤ 16dρ_j, and the brackets give (8/3)·12dρ_j = 32dρ_j = c_wρ_j < π.
  - **#C10.3.36-1.** |Ad(w) − 1| ≤ c_br|Y| ≤ c_brc_wρ_j.
  - **#C10.3.39–#C10.3.40.**
    - Ad(w)λ^B is divergence-free at V^w by covariance.
    - 2(x_λ + c_brc_wB_λ)(…) + (4C′_Qρ_j + 2c_brc_wρ_j)B_λε₁ ≤ [2x_λ + (4C′_Q + 4c_brc_w)B_λ](ρ_j + (ε/a_j)ε₁) by ε₁ ≤ 1.
    - a_j³|J′| ≤ 2B_λε₁ by (a).
  - **#C10.3.51–#C10.3.51-0-2.** The list contains #C10.3.36 and §E's α₀ threshold. It also contains every condition of #C10.3.3-10-0–#C10.3.3-10-0-2: 4c_Bα₁ ≤ 1 follows from 64c_Bα₁ ≤ 1, and ε|A^u| ≤ α₁ ≤ r_{BCH}/4 from 4α₁ ≤ r_{BCH}. It contains the conditions of #C10.3.3-11-6-0–#C10.3.3-11-6-0-1 (O(1)Lα₁ ≤ r_P/3).
- **Spec repair:** claim (c) said Σ_{i<j}Lθ_i ≤ 12ρ_j, while #C10.3.34-6 uses 16ρ_j inductively and the 12ρ_j comes from #C10.3.34-7-1 by L ≥ 3. The claim now states both. Claim (e) is re-pointed to #C10.3.3-10-0–#C10.3.3-10-0-2.
- **Context:** #C10.3.3-8–#C10.3.3-10-1 and #C10.3.3-11-6–#C10.3.3-11-8-1 changed in 14b1 r4's repairs and are under review in cauchy-p14b1-20261109-r5. This packet uses them only for B₀^{cx}, δ₁′, C_𝐉, C_𝐆, and their conditions, which #C10.3.51-0-2 lists. The table fork's δ₁′ := min(δ_cx, ½δ₀)/8 (table 1e252f854c47) restates no formula used here.
- **Definition check:** 0 conflicts (9 allowed). **Size:** reviewed blocks 7.56k (25k cap), max line 597.
- **Spec:** specs\spec_p14b2_r4.json (Cauchy a0464784c8bc, LF 029a1d03a304).
- **Launch:** held. The user asked to pause before launching (10:27).

Written 2026-11-09 10:27.

## Round 4, Reviewed by Me in Place of the Referee

- **How:** at the user's request, no referee was launched. I read every line under review and its context, with #C10.3.29-2 against CMP 98 §E (p.042) and #C10.3.34-5 against (126) and Proposition 3 (p.036).
- **Verdict:** clean; no finding.
- **Checked and correct:** every re-derivation above, line by line.
- **Next round:** a full round, at Cauchy 282155b15f71.

Written 2026-11-09 16:41.

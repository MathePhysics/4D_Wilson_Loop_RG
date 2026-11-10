# Packet 15b (Cauchy #C10.4.46–#C10.4.107), round 1, 9 Nov 2026

## Pre-check of cauchy-p15b-20261109-r1 (full)

- **Split:** see WILSON_IT1_LF_TRIAGE_P15A_R1_2026_11_09.md. 15b is #C10.4.46–#C10.4.107: the bounds of β_act + β_con, the multiscale defect, the weighted defect, the π-part, the J-term, and the assembly.
- **Whole part re-read** (#C10.4.46–#C10.4.107), with the context extracts of the spec (#C10.4.1–#C10.4.45-1, #C10.1.7–#C10.1.11, #C10.2.1–#C10.2.3, and #C10.3.4–#C10.3.7), PBG p.394 l.29 and (3.24)–(3.25), and LF #4.101–#4.101-1.
- **Repairs made in this pass** (in place):
  - #C10.4.59 and #C10.4.59-1: the bond and plaquette weights are ε^d.
  - #C10.4.65-2: a_X is PBG's number a_m at a = 1. The line says this a_m is not table #T2.3's spacing and names the run indices j − 1 and j in words. The choice a = 1 is cited to LF #4.101-1: R_X is defined by (3.22), which does not involve a, and PBG states Theorems 3.1 and 3.2 at a = 1 (p.397 l.38, p.399 l.18). The recursion holds for m ≥ 1, with a₀ = a₁ = 1 (PBG p.394 l.29 at a = 1; "for m ≥ 1" is inferred, not printed, since at m = 0 the recursion would give a₁ ≠ a₀). The bound 0 ≤ a_m − (1 − L^{−2}) ≤ L^{−2m} cites LF #4.101-1, which was split from #4.101 with the same reading. So |a_A − a_B| ≤ L^{−2(j−1)} ≤ 2L^{−j} for j ≥ 2, and a_A = a_B at j = 1. The table fork pointed out that a = 1 was unstated and added #T11.20-2.
  - #C10.4.66: both runs' configurations satisfy (3.35) at the scale ℓ (#C10.4.1-1), so PBG Theorems 3.1 and 3.2 hold on both lattices, at a = 1 and with the run's single layer in (3.24), uniformly in PBG's spacing η.
  - #C10.4.87 no longer restates δr. It cites *The Defects.* (#C10.4.85), where δr is defined, and the table's #T12.7 keeps the definition at #C10.4.85 (table fork, b5ec74b360de).
  - #C10.4.95-1 and #C10.4.95-2: the tent derivation of the weight per fine bond.
- **Re-derived:**
  - **#C10.4.65-2.** With a_* = 1 − L^{−2}, L^{−2} + a_* = 1 gives a_{m+1} − a_* = L^{−2}(a_m − a_*)/(L^{−2} + a_m). By induction from a₁ − a_* = L^{−2}, the denominator is ≥ 1 and 0 ≤ a_m − a_* ≤ L^{−2m}. Both a_{j−1} and a_j lie in [a_*, a_* + L^{−2(j−1)}], and L^{−2(j−1)} ≤ 2L^{−j} is L^{2−j} ≤ 2, true for j ≥ 2.
  - **#C10.4.95-1.** The 2L − 1 slices carry the weights min(i + 1, 2L − 1 − i)/L², which sum to 1. Subtracting the face slice S_{L−1} and summing by parts gives the coefficient of S_{i+1} − S_i as minus the partial sum of the weights up to i (for i ≤ L − 2), and symmetrically above. The largest is Σ_{i≤L−2}(i + 1)/L² = (L − 1)/(2L) < ½.
  - **#C10.4.95-2.** A fine bond lies in at most two tubes, so its total weight is ≤ 2·½·ε = ε ≤ C_ldε.
  - **#C10.4.58.** ε⁴ is the factor c_κη⁴ of κ's derivative bounds (#C10.4.41), not a volume weight. ε⁴|F|² ≤ ν_F² holds by ε ≤ ℓ, and ε⁴|F|³ℓ² ≤ ν_F² by ε²|F| ≤ C₀ε₁ ≤ 1.
  - **#C10.4.101-1–#C10.4.101-3.** c(λ, D_Xλ) = i[λ(b₋), D_Xλ], and the bracket of (3.117) is 2c(λ, Y) − c(λ, D_Xλ). At 𝐉 = Q_X*ν_λ the two terms cancel, so each quadratic form vanishes. Then each symmetric form is 0 by polarisation, and both runs' currents are of this form (#C10.4.101-2).
- **Definition check:** 0 conflicts (6 allowed: B_G, G′_X, r_B, s₂, δr, and ψ), each allowance checked against the other source's tag. G′_X's allowance cites LF #4.101, where {#D.G′_X} still stands.
- **Size:** reviewed block 18.34k characters (25k cap); it was 18.24k before the a_m repair. CR is 0, there are no trailing spaces or duplicate tags, and every line is ≤ 544 characters.
- **Spec:** specs\spec_p15b_r1.json. Updated to the current Cauchy and LF SHAs (e269a956602b and 73435a4a8e2a after the a = 1 repair) at launch, and rebuilt then.
- **Order:** after 15a r1.

Written 2026-11-09 09:30.

## Round 1, Reviewed by Me in Place of the Referee

- **How:** at the user's request, no referee was launched. I read every line of #C10.4.46–#C10.4.107 and its context, with PBG p.394 l.29, (3.24)–(3.25), and (3.113)–(3.121) (p.418–419), and CMP 98 (121)–(126) (p.036).
- **Verdict:** not clean; one minor and four cosmetics, all repaired.
- **Minor: the transports of the Hölder quotients, and the face term.**
  - *Regularity of H₁.* and #C10.4.66-1 bound the oscillations of Hölder quotients, whose transports run along shortest contours (#C10.4.8-3). #C10.4.74-1, #C10.4.79, #C10.4.82-3, and #C10.4.97-1 applied them to values carried by other transports without a bound on the change.
  - #C10.4.95-1's tent sum treated Q̂_fℱ(c) as the face slice's value, but Q^{str} carries the face values with its own transports.
  - Repairs:
    - new #C10.4.14-3: on a cell of side ≤ 4ε, the passage costs at most 5δ_T sup|g|;
    - #C10.4.74-1: 5δ_T(|f_B| + |φ_B(μ_B)|) ≤ C_trc_{g2}ν_F𝔰;
    - #C10.4.77, #C10.4.79, and #C10.4.81: X counted at 300d⁴ + 2dc₁₂₄, plus 5δ_T = 160d²ε²|F|, within C_tr;
    - #C10.4.82-2–#C10.4.82-4: d𝔬 + 288d³ν_F𝔰, with 2(300d⁴ + 2dc₁₂₄) + 288d³ ≤ 2C_tr;
    - #C10.4.95–#C10.4.95-2 with the new #C10.4.95-1-1: (Q^{str} − Q̂_f)ℱ(c) = (ε/L)Σ_iW_i𝔡_i(c) + 𝔣(ℱ)(c), with |W_i| < ½, (1/L)Σ_i|W_i| = (L² − 1)/(3L²), and |𝔣| ≤ 2δ_T sup|ℱ|;
    - #C10.4.96–#C10.4.96-1: D_A*𝔣(ℱ) adds 4dδ_T/ε = 128d³ε|F| to the row sums;
    - #C10.4.97-1: 4(300d⁴ + 2dc₁₂₄) + 160d³ ≤ 4C_tr.
- **Re-derived:** the per-path weights −(m + 1)/L and (L − 1 − m)/L, which are the summation by parts of the average minus the face value. Σ_{i≤L−2}(i + 1)(i + 2)/2 = (L − 1)L(L + 1)/6, so with the symmetric half Σ_i|W_i| = (L² − 1)/(3L). And (6d + 3)·32d² ≤ 288d³, 5·32d² = 160d², and 4d·32d² = 128d³.
- **Cosmetics:**
  - #C10.4.98-1–#C10.4.101-1 used μ_A, already defined at #C10.4.65-3 as K_X^{−1}Q′_XG′_Xf_X. Renamed σ_A.
  - #C10.4.48-1 restated c_{br}; it now cites #C10.3.36-1.
  - #C10.4.62 restated h_H; it now cites #C10.4.8-5.
  - #C10.4.81 now states the main term of #C10.4.79, dB_GB_G(γ_H)(ε/ℓ)^{γ_H}ℓ²|ρ|.
- **Consumers:** LF #4.284.4 and table #T12.7 stay valid.
- **Next round:** r2, narrow, on the repaired lines, at Cauchy 557b0ab39354.
- **After the entry:** the table fork found that W_i clashes with #C10.1.4-0-2's W_i := M^iU. The tent weights are renamed W^{tent}_i in #C10.4.82-3, #C10.4.95-1-1, and #C10.4.95-2. Their definition is split off as #C10.4.95-1-2, since the line had grown to 643 characters, and #C10.4.82-3 now cites #C10.4.95-1–#C10.4.95-1-2.

Written 2026-11-09 16:41.

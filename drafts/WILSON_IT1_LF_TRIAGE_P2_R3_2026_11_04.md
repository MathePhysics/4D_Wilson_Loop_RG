# LF Packet 2, Review 3: Triage

Review: verification\isolated_reviewer\reviews\lf-p2-20261104-r3\review.md (LF 12d07fa2eacc). Verdict: established except S1. There is no fatal item and one serious item. The revised Q₁ normalisation was checked against PRT2 pp.243–245. All items are accepted and repaired. Since r3 found a serious item that r2 missed, the two clean passes are counted again from r4.

## Serious

- **S1 (#0.1.26): the sites deep in Λ^c.** Accepted. The interior bound was written only for Q_{2R}(y) ⊂ Λ, and (K2) needs v_{x̄} at the mass bonds. #0.1.26 now has *The massive case.* for y in a cell of Λ^c with t(y) ≥ 4√dρ₀:
  - On the bonds of Q_{2R}(y), ∂₁ω_{g′} = 0, because ω_{g′} ∈ N_b vanishes on Λ^c. P_N = 1 − Π_m − 1_{Λ^c} annihilates the functions supported in Λ^c. So Ku = h₁ with {#D.K.5} K := Δ_j + a, a = 1.
  - K ≥ 1, and its kernel decays at the unit scale (#0.1.17). So Combes–Thomas gives abs(K^{−1}(b, b′)) ≤ 2e^{−μabs(b − b′)}, uniformly in the volume.
  - Splitting Ku inside and outside Q_{2R}(y) gives sup_{Q_R(y)}abs(u) ≤ C(d)(S + (1 + log L)^pL^{−2}θ) + L^{−10}θ.
  - So the scales below R/2 add ≤ C(d)(θ_B + (1 + log L)^pθ)/L + L^{−9}θ, far below the weight.

  The old last sentence ("On the mass bonds abs(u(b)) ≤ (E(Q_1)/a)^{1/2}, with the same weight") is replaced by the bound on u(b) from this case. The opening of the interior bound now states that Q_{2R}(y) lies in Λ or in one cell of Λ^c.

## Minor

- **M1.** Accepted: "one of whose two blocks meets Q_s".
- **M2.** Accepted. #A.16 now uses {#D.K₁} K₁ := the exit factor K of the hitting argument, and K := K₁ + 1. K₀ stays the distance factor of #0.1.24. #0.1.24's ν sentence now reads osc_{Q_{(K+1)r}(x)} and ν := log(1/(1 − c(d)))/log(K + 1), with K + 1 the K of (K5).
- **C3.** Accepted. The ball of radius N/4 about y is read in ℤ^d, as for v_{x̄}. φ and ψ₃ are cut off outside it, at a cost ≤ e^{−c(d)N}L^{C(d)} times the bulk size, which is part of the tails.
- **C4.** Accepted. The bound u″ ≤ L^{C(d)} times the bulk size is now derived from #A.10, from the kernel O(abs(x)^{1−d}) of ∂₁(∂₁*∂₁)^{−1} with abs(σ) ≤ C(d)L^{−d/2}‖∂₁*u‖_{Q_{2L}}, and from max abs(∂₁ψ) ≤ ‖u′‖ + 2‖a₀‖.
- **C5.** Accepted:
  - the split in #0.1.21 is now at abs(b − b′) ≤ s/64 − 2;
  - the bound on v_{x̄} carries C(d);
  - #0.1.25 reads "≥ 6L − 2";
  - the hitting sentence reads Q_{(K+1)r}(x) in ℤ^d with 2(K + 1)r ≤ L/C(d).

## Next

p2 r4 on LF 60293c0941af (labels 44c71438d0b0).

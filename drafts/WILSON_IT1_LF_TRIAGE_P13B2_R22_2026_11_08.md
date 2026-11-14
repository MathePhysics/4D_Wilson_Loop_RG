# Triage of lf-p13b2-20261108-r22

## Verdict

- r22 was a narrow round of 13b2 on r21's repairs, at LF 81ef3601b01c, table 6d09b1b5054d, and labels 971e7d7d5325.
- **Fatal:** none. **Serious:** none. **Minor:** none.
- **Trivial:** t1, in #4.565-1. The disc bound ≤ 2C_actε₁′² from "each run's unweighted density" used the cancellation d_y = a_y(U^A) − a_y^B(U^B) without stating it.
- r21's m1 and t1–t2 were confirmed repaired, and t3 moot. The referee re-derived the two disc bounds of #4.563-3 from #4.563-3-1's count, the Lemma's C_dc(M) = max(C_y(M), 2C_act), #4.567's weight route in the real form of #4.168, and #4.561.1-1-0's openness step.
- The round is **clean**, so the count is 1. The next round, r23, is full.

## Repairs

| Finding | Line | Issue | Repair |
|---|---|---|---|
| t1 | #4.565-1 | The cancellation behind the disc bound was unstated | Reworded: "since d_y = a_y(U^A) − a_y^B(U^B), the terms a_y(Ũ) cancelling (#4.51-0, Ũ = MU^B), and each run's unweighted density is ≤ C_actε₁′² in run A's blocks (#4.563-3)" |
| own | #4.517-2 | ε₂ = B₅^cε₁′ cited by the heading *The members.* | Cited by the tag of its definition, (#4.561-1) |

## Checks

- **t1.** #4.51-0 defines d_y := [a_y(U^A) − a_y(MU^B)] + b_y(U^B) and b_y(W) := a_y(MW) − a_y^B(W), so d_y = a_y(U^A) − a_y^B(U^B) exactly. #4.565 writes the same density with Ũ, which #4.5-2-1 defines as MU^B; #4.565-1 now uses Ũ too.
- **Line lengths.** #4.517-2 378 and #4.565-1 360 characters. CR count 0.

## Pre-check of lf-p13b2-20261108-r23 (full)

- **Spec.** specs\spec_p13b2_r23.json, prior r22. The extract #4.517 is now #4.517–#4.517-2, the part's own lines. #4.517-3–#4.517-5 left the packet and are cited as permitted background (only #4.563-2.2-1 cites #4.517-5, by tag).
- **Named steps.** Every tagged line of #4.517–#4.517-2, #4.561–#4.565-1, and #4.567–#4.568.
- **Changed since r22.** #4.565-1 and #4.517-2, re-read in place.
- **Whole part read** (8 Nov 2026, 10:36–10:38), every line re-derived:
  - #4.517-1-1–#4.517-2: Σ_{n<j}L^{n+1−j} ≤ 1/(1 − L^{−1}), so s_u ≤ 8dε₂/(1 − L^{−1}) ≤ 16dε₂ for L ≥ 2. Then 256dε₂ ≤ 1 gives s_u ≤ 1/16, and −log(2 − e^{1/4})·4 ≈ 1.34 < 2.
  - #4.561.1-0: e^x − 1 ≤ 2x for x ≤ 1 gives 54c_avα̂₁, which is ≤ c_avε′_k since C_c = 60 > 54. Also 240c_avα̂₁ ≤ ½ gives 27c_avα̂₁ ≤ 1.
  - #4.561.1-2's first entry covers three bounds:
    - on Λ, 2·4d(100M)⁵γ₀^{−1}B₃²·2c_avε′_k = 4c_av·4d·100⁵γ₀^{−1}B₃²M⁵ε′_k;
    - on Z ∩ Λ^c, c_avε′_k;
    - on the j-th domains, c_ṼB₃B₅M⁵·2c_avε′_k.
  - The second entry is #4.561.1-1.3-2's computation, e^{64dε₂^{AL}} ≤ 2 and e^{64dε₂^{AL}} − 1 ≤ 128dε₂^{AL} = 768dB₁B₃C_{AL}ε′_k, with D^{AL}(0) unitary.
  - #4.561-1-1's 2B₀C_{V′}B₃ε₁′ ≤ 64ε₂ = 384B₁B₃C_{V′}ε₁′. #4.561-1-2's ε₂^{AL} ≤ ε₂/4 holds by C_{V′} ≥ 4C_{AL}.
  - #4.562-1: g(log g^{−2})^{q} increases for small g, and log((1 + β₀)g_k)^{−2} ≤ log g_k^{−2}, so α̂_i ≤ (1 + β₀)α_{i,k}.
  - #4.563-1.1: 4abs(B^e) ≤ 8c_avε′_k ≤ 1 gives 16c_avε′_k. With c_{rp}ε′_k ≤ ε₁′ and C_{V′} ≥ 4c_av, the total is ≤ 2C_{V′}ε₁′ < 20C_{V′}ε₁′.
  - #4.563-2.1: the terms are 2ε₂L^{−2j}, 8C₀^{ms}ε₁′ε₂L^{−2j} and 16ε₂²L^{−2j}, and 8C₀^{ms}ε₁′ + 16ε₂ ≤ 1. #4.563-2.1-1 gives 4C₀^{ms}ε₁′ + 3L²ε₂ = c_plC₀^{ms}ε₁′.
  - #4.563-3-0: −½tr((X − 1)²X^{−1}) = 1 − ½tr(X + X^{−1}) with tr 1 = 1, and abs(X^{−1}) ≤ 2 for abs(X − 1) ≤ ½. Also 4C₀^{ms}ε₁′ + 3ε₂ ≤ ¼.
  - #4.565-0: (ε/a_n) ≤ (ε/a_n)^{(1−ε₀)/3}.
  - #4.567-1: (9/16 + ¼) = 13/16 < 1, and abs(X)e^{abs(X)} ≤ ρ_V for abs(X) ≤ e^{−1/4}ρ_V ≤ ¼.
  - No gap was found beyond the two rewordings above.
- **Symbols.** Ũ is #4.5-2-1's. No new symbol. The definition check passed in the build.
- **Size.** Built at LF 292b6345f662: argument 23,895 characters (r22 24,959; the drop is #4.517-3–#4.517-5 leaving the packet), 28 files.
- No known weak point and no OPEN is in the part.

## SHAs

LF 81ef3601b01c (r22's snapshot) → 292b6345f662 (t1 and the #4.517-2 citation). Table 6d09b1b5054d and labels 971e7d7d5325 (unchanged; relabel and rows pending with the table fork).

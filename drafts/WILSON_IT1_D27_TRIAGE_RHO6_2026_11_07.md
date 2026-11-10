# D2.7 Per-Cube Entropy Repair (7 Nov 2026)

pc-rinputs r4's remark ρ6: D2.7 counted the groups and polymers through an MR_k-cube by their MR_k-level positions only. It omitted the root among the cube's R_k^d π_k-cubes (or next to a first-class component) and the M-level shapes. Repaired in place at D2.7 5124e5410d92, citing TL abbdda1d8519 (labels a53ca44c4ea3).

## Open

None.

## Re-derived

- **Roots.** Off ∪Y, a polymer through an MR_k-cube is rooted at one of its R_k^d π_k-cubes. Next to a first-class component X_j, M^{−d}|X_j| ≤ 2(100R_k)^d (p.389 l.13–14), so at most 3^{d+1}(100R_k)^d roots. By p.389 l.18, ¼p₀(g_k) ≥ 1 + 2κ(100R_k)^d gives (100R_k)^d ≤ p₀(g_k)/(8κ), so the root count is ≤ p₀(g_k)/8 for κ ≥ 3^{d+1}. N(Y_i) = 3^d(101R_k)^d + 1 < p₀(g_k) for κ ≥ 4^d.
- **Shapes.** The tree of (1.67) (p.376 l.26–32), of length Md_k, meets at most 2^d(2d_k + 1) M-cubes. These and the fixed domains with a face on them fix P∖fixed, so there are at most e^{c(d)(d_k+1)} shapes. They are paid by (β/8)κd_k out of item 6(b)'s e^{−(1+β/4)κd_k}, for κ ≥ 8c(d)/β. The other (β/8)κ ≥ 3·2^{d−2} ≥ 1, from βκ ≥ 6·2^d (p.389 l.12). This is TL #637-1.
- **Sums.** Per MR_k-cube, the polymers with a slot sum to at most (R_k^d + 6^d)C_Ψ″ĉ₁ ≤ e^{−p₀(g_k)/4}. The groups sum to at most p₀(g_k)O(1)ĉ₁ ≤ e^{−p₀(g_k)/4} (TL #814-4-2-3–#814-4-2-5). The per-polymer amplitude ĉ₁ ≤ e^{−p₀(g_k)/2} is unchanged.
- **Exponent.** e^{−p₀(g_k)/4} ≤ (g_K^{−2} + b(K−k) − C)^{−2} once A₀(log(·))^{p₀−1} ≥ 8.

## Repairs (in place)

| Item | Repair |
|---|---|
| 15.3, Φ(∅) | The sum through an MR_k-cube is the polymers with a slot, rooted as above, so Φ(∅) is at most e^{−p₀(g_k)/4}#cubes_k(C) in modulus. |
| 15.3, Φ(𝔉) − Φ(∅) | At most B_Q#cubes_k(∪𝔉) in modulus, B_Q the Bałaban polymers' per-cube sum of TL #814-4-2–#814-4-2-2 (the q = 0 polymers at Y carry α^{1/3}). |
| 15.3, c^R_n | The charge per MR_n-cube is ≤ 2p₀(g_n)e^{O(1)}e^{−p₀(g_n)/2} ≤ ½e^{−p₀(g_n)/4}; c^R_n := O(1)e^{−p₀(g_n)/4} stands. |
| 15.4(i) | The entropy sentence adds the root (≤ p₀(g_k)/8) and the M-level shapes. The groups through an MR_k-cube sum to ≤ e^{−p₀(g_k)/4}. |
| 15.4(ii) | μ_k^R, ζ_k^R, and E°_k^R carry e^{−p₀(g_k)/4}. |
| 15.4(iii) | m_k^R := O(1)e^{−p₀(g_k)/4}, with the per-part sums of 15.3 and (i). |
| 15.6 | Ψ_g(S) is at most 2e^{−p₀(g_k)/4}#cubes_k(hull g) in modulus (TL #849-0). |
| 15.6(e) | The att charge is ≤ ½e^{−p₀(g_k)/4} per MR_k-cube. |
| 15.7 | C^R_k, the members' coefficient, λ_R, and the sum of the remainders E°_k^R carry e^{−p₀(g_k)/4}; e to the modulus of Ψ_g is ≤ exp(30e^{−p₀(g_k)/4}n_g), with hull(g) meeting ≤ 15n_g cubes. |
| 15.8 | A Bałaban polymer rooted at a π_k-cube is summed by O(1)c₁ ((1.97) with #637-1), not by 15.3. |
| Item 6, l.100 | Per π_k-cube O(1)c₁; per MR_k-cube O(1)p₀(g_k)c₁. |
| Summary, l.3, l.155; constants, l.250, l.261 | The new rates and the root-count conditions. |

## Not changed

- l.102's per-block bound (rooted at the block b) and the failed accounting of items 4–9, which item 15 replaces.
- TL #637 cites "D2.7 15.3(b)" for the activity bound, which is D2.7 item 6(b). Reported to the two-loops session.

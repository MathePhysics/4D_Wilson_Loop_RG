# Packet 13 r1 Result and r2 Repairs (7 Nov 2026)

lf-p13-20261106-r1 reported no fatal and no serious findings, and twelve minor ones (m1–m12). All are repaired in place at LF e873ea0df345 (labels 93851bc1cc55), table 8e227609f36c. The repaired part is over the 25k limit, so r2 is split into 13a, (A-ii) #4.43–#4.55-1 (14,216 characters), and 13b, the complex class #4.556–#4.568 (14,857 characters). Each takes r1's review as its prior.

## Open

None.

## Repairs (in place)

| Item | Line | Repair |
|---|---|---|
| m1 | #4.51 | D = Σ_yd_y runs over the blocks of all layers of 𝐁_k(Z) (#4.48.1), each in its own units, not the scale-k blocks of Z. |
| m2 | #4.53 | The ratio V′^B₀(V′^A₀)^{−1} is e^{iX}; the difference (e^{iX} − 1)V′^A₀ is ≤ C‖X‖_∞. |
| m3 | #4.52 | The shared scales are m, h ≤ m ≤ k. (1.25)'s pin is p.362 l.22–29, to include ū₀'s definition. |
| m4 | #4.559-1, new #4.559-1.1, #4.560-1, #4.560-1.1.1, #4.560-0 | U_0 at z is U_0 at the data V_k(z) := M^k(𝐔(z)): the minimiser of (1.3) with data M_{𝐁_k(Z)}(Q^{s*}_kV_k(z)) on Z ∖ Λ (p.357 l.11–17), that is U_{k,Z}(V_Λ) with V_Λ the minimum of LFR I (1.77) (1.79). V″ is replaced by the averages of 𝐔(z) (p.374 l.38–39) and is not fixed; only V′ on Λ, B, and the couplings are. #4.560-1 now reads U_0's data regularity, the scale-k part of (7) for D(z), instead of applying Theorem 1 to D(z). #4.560-1.1.1 replaces ε_k by O(1)ε′_k, the data parameter, with C(M) ≥ O(1)M⁶ times that O(1) from p.357 l.47–48. |
| m5 | #4.563, new #4.563-2, #4.563-2.1, #4.563-3 | The disc plaquettes are derived from Proposition 9: each minimiser is e^{iη𝐇}U^r up to gauge, U^r the real minimiser at z = 0 (plaquettes ≤ 2C₀ε₁′/a_j²), 𝐇 with (19) at ε₂ = B₅ε₁′. Moving the four factors to the left gives η²·curl 𝐇 up to 4|U^r(∂p) − 1|η|𝐇| and higher terms ≤ (4η|𝐇|)², a move ≤ 3ε₂L^{−2j}. So plaquettes ≤ c_plC₀ε₁′/a_j², c_pl := 2 + 3B₅/C₀, and C_act := d²(c_plC₀)². With the normalised trace (#T10.18), 1 − ½tr(X + X^{−1}) = −½tr((X − 1)²X^{−1}) ≤ abs(X − 1)², so no dimension factor. VAR's ∇_{U^r} in (19) is the norm of the covariant differences: REG states the same bounds with ∇^η_{U₀} (p.82 l.48), its D^η_{U,μ} are (1.1) (p.76 l.32–41), and PBG (3.39) (p.397 l.4–7) defines the norm with them; the curl is iη²(D_μ𝐇_ν − D_ν𝐇_μ), as in REG (1.47) (p.84 l.37–44). |
| m5 (consumer) | #4.198, new #4.198-1, #4.199, #4.200 (§4(d)) | #4.198's "≤ 52C₀ε₁′/a_j²" had the same gap; it now uses c_pl: each link ≤ 26C_L(c_pl + 26C_𝐇)C_𝐇w̄ε̂′²e^{…}, 𝔐 := 8·26C_L(c_pl + 26C_𝐇)C_𝐇c_tot(1/24)w̄ε̂′², and #4.200's disc factor is 26(c_pl + 26C_𝐇)(2 + C_𝐇)^{−1}C_wc. Split at a sentence for length. For §4(d)'s own packet. |
| m6 | new #4.50-1.1, #4.561, new #4.561-1.2, #4.562-1, new #4.562-1.1 | (T-Λ) lists Bałaban's thresholds: O(1)(M⁶R_kε_k + exp(−R_k)) ≤ κ_Λ for (1.9) (p.358 l.2–22), Proposition 1's smallness at ε_k (p.194 l.38–39), and ε₁ ≤ a₁ (p.279 l.9). (T-c) adds them with O(1)ε′_k for ε_k, C_c(α̂₀ + α̂₁) ≤ c₂ (CMP98 p.26 l.47), Proposition 1's smallness at 20C_{V′}ε₁′, and (8C₀ + 16B₅)ε₁′ ≤ 1. #4.562-1.1: the (1.9) threshold is a bound on g_k alone and holds for g_k small. |
| m7 | new #4.560-1.1.2 | LFR I Proposition 1 applies to V_k(z) at ε = O(1)ε′_k, so (1.78) and (1.83) (p.197 l.3–6) give #4.50's a priori location at a real point, with C_X(M)'s C at least that O(1). |
| m8 | new #4.563-1, #4.563-1.1 | V_k(z) = e^{iB′(z)}V_k(0), abs(B′) ≤ 52ε₁′ ≤ C_{V′}ε₁′, abs(∂V_k(z) − 1) < 20C_{V′}ε₁′; Proposition 1's analytic extension (p.194 l.46–48) makes V′^X₀(z) analytic, and U_0(z) = U_{k,Z}(V′^X₀(z)) by Proposition 9. |
| m9 | #4.567, #4.200 | Cauchy's estimate is on the data domain of U″_k = U_{𝐁″_k}(·) in VAR Sect. G (abs(V′ − 1) < C_{V′}ε₁′), not on (c)'s P. |
| m10 | #4.48.1 | c′_Λ := d(100M + 1)^dc_tot(1/16), the bonds of a box of size 100M (p.358 l.8). |
| m11 | #4.561.1 | The labels C₁.2, C₁.3 are removed: VAR's C₁ is C₁′ in (c) and C_{V′} at the disc (C_{V′} + 2C_U(M) + 5C_p for ι), and (T-Λ)'s C₁ and C₁′ are those of (c). |
| m12 | #4.51-2, #4.51-3, #4.55 | #4.51-2's C_L is renamed C_{dΛ} := 3CB₀ (the letter C_L has other uses); C_A(M) is a constant of C_Δ(M), C′_Δ(M), c_K, and the constants of #4.54 and #4.54-1. |
| r1 notes | #4.50, #4.197 | #4.50 states ‖X‖_∞ < 2C₁ε₁ and the chain to 2C₁κ_Λε₁/C_Φ(M). #4.197 (§4(d)) said V″ and V_k are fixed on the line; they are averages of the line. |
| m-c (peer) | table #T4.43, LF #5.49-1 | #T4.43 drops "times e³" (announced to the two-loops session); #5.49-1 cites #T4.43 for C_Ψ″. |

## Checked, unchanged

- LFR I Proposition 1 (p.194 l.37–48), (1.77) (p.194 l.28–30), (1.79) (p.195 l.6–8), (1.83) (p.197 l.3–7).
- LFR II p.357 l.11–17 ((1.3)), l.45–48; p.358 l.2–22 ((1.7)–(1.9)), l.27–30; p.361 l.36–37; p.362 l.22–29; p.370 l.2–5; p.374 l.37–40.
- VAR (2), (5), (7) (p.278), Theorem 1 (p.279 l.8–15), (19)–(21) (p.281 l.5–17), Proposition 9 (p.309 l.8–14); CMP98 Proposition 2 (p.26 l.46–52); CRE (2.4), (2.5) (p.255 l.32–40).

## Files

- **Pins.** LF 724946123ea0 (labels c0928da8b396; #5.39-3-1-2 cites 15.8-1(6-0) and #5.49-1 roots at two-loops #814-1's r^Y_i, both outside 13a and 13b), table c94afde7eca1 (#T4.43's C_Ψ″ at the root r^Y_i, uniform in k and R_k; new row #T4.44, C_box := 4A_E = 2916 and ν_e = ν/5832; #T4.42's D^∪_P has the q = 0 constant 4; #T4.43's E(Y_i) has two-loops #806-1's 4R_k + 92 + 2^{d+1}κ), D2.7 2b2692792582 (pc-links_a r2's N2: u := 640(2^{d+2} + 8), X̂ meets ≤ 2^{d+2}σ π_k-cubes; r7's m1: X̂ cites two-loops #629-2–#629-2-5, step 1 included). All three are frozen while the two-loops session's pc-links_a r2 and pc-links_b r2 run.
- **Packets.** spec_p13a_r2.json and spec_p13b_r2.json are built at these pins, 0 definition conflicts (7 allowed). 13b's permitted background adds REG (1.1), (1.47), p.82, and PBG (3.39). Every packet line is ≤ 611 characters.
- **D2.7 15.8 (done, 87d77709acc7; accepted by the two-loops session).** e_X is a number given the term's labels (map #MD2.0.3.64, #MD2.3.8.7), with its set X̂ (two-loops #629-2). A link reading X_c's labels meets X_c^∼ (#629-0-2), which lies in the X′ holding a first-class X_c (LFR II p.377 l.5–6, p.389 l.10). 𝐓′_k(Y_i) sums Y_i's labels from outside the bracket ((1.72), p.379 l.17–18). The factorisation is over the X′ and the X̂, with #π_n(X̂) in the cube count. The links reading a second-class Y_i's labels meet Y_i^∼. 15.8-1(2-5) cites two-loops #288.
- **Pre-check, lf-p13a-20261106-r2 and lf-p13b-20261106-r2.**
  - Changed lines re-derived: m1–m12, #4.563-2–#4.563-2.1 (REG (1.1), (1.47), PBG (3.39)), against the pages listed under *Checked, unchanged*.
  - Arithmetic and citations re-checked: c_pl, C_act, 52ε₁′ ≤ C_{V′}ε₁′, 20C_{V′}ε₁′, c′_Λ, and each new pin re-opened.
  - New symbols checked against the labels file: c_pl, C_act, C_{dΛ}, c′_Λ, V_k(z); 0 definition conflicts.
  - Wider implications: §4(d)'s #4.197–#4.200 carry c_pl for their own packet. The later table, D2.7 and LF #5.39-3-1-2 and #5.49-1 edits lie outside 13a and 13b, so their argument text is unchanged.
  - Linear order kept: #4.561-1.2 follows C_{V′}'s definition.
  - Relabelled, specs at LF 724946123ea0 and table c94afde7eca1 (labels c0928da8b396), packets built at 14,216 and 14,857 characters, every line ≤ 611.
- **Status.** 13a launched 7 Nov 2026 on the user's go; 13b follows when 13a reports.

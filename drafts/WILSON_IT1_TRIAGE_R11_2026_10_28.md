# Triage R11 (2026-10-28, from 14:40)

Reviews launched about 14:40: cauchy-moment-20261028-r1 (Cauchy §3/§5 plane-resolved moment and the pair-r1 minors), lf-rate-20261028-r1 (θ̃ and the rate of (iv) and (α)), var-20261028-r6 (LF §4(d), the var-r5 repairs). Packet hashes: Cauchy 952 lines 80709efc7f3e; LF 624 lines 4aaa11bc70db.

## Edits while the reviews run

- LF Open Gaps (3), first sub-bullet (in the var-r6 and lf-rate ranges): the closure of PRT2 (2.1)–(2.2) for the joins 𝐁₁ and 𝐁₂ is made specific. [III] of LFR II is CRE (p.392 l.18); the join is CRE (2.14) (p.257 l.7–16), with ≥ 2M₁ from ∂Ω to the inner layer boundaries, against VAR's (1) > RM₁ (p.277 l.11–17). What closes it: the layer separations from LFR I's domains (Ω″_{h+1} = Ω_{h+1}^{∼5}, p.195 l.28; Z″_j, LFR I (1.10)–(1.12), p.179), or a proof that the collar is never an intermediate layer of (2.58). Read for it: CRE p.256 l.21–24 (2MR_j between the boundaries of the RG domains), CRE p.245 l.35–37 (M₁ < M₂ = L²M₁ < M), LFR I p.179 (the Z″_j at the top N₀ scales one layer of M-cubes apart; {Ω″_j} admissible, l.40). Admissibility alone does not settle the joins' margin, so the item stays open.

## Closed in this round (unreviewed)

- **LF §3(d), the shell of (1.27).** Derived: |W_B − W_A| bounds the change of |V_jW^{−1} − 1| for G-valued W; ρ̄_j = 2C_G(ε₀)c″_K(ε/a_j)^{1−ε₀}ε₁ (§4(b)); δ′_j = g_jA₁p₁(g_j) (LFR I p.183 l.2, read); ε₁/δ′_j ≤ C(M)(A₀/A₁)(1 + β₀)2^{p₀+r}L(k − j + 1)^{1/2}(log g_j^{−2})^{p₀+r} by CRE (2.4)–(2.6); on the young pairs' histories j ≥ n, k < 8n + j(C), so the factors are absorbed by L^{ε₀j}, with C_{1.27} polynomial in j(C). The test's description is corrected to the print, |V_j(b)(V^{(j)}_Z(b))^{−1} − 1| < 2δ′_j (LFR I p.182 l.53, both transcriptions); the note had a (1/i)log form.
- The premise that the cascade sets are VAR determining sets rests on LFR I p.179 l.19–22 and l.40 ({Ω″_j} is an admissible sequence; the Z″ complements are admissible sequences of M-cubes), read.

## The three reviews (written 14:50–14:52), triaged 14:52–15:09

All three reports were read in full. None has a fatal finding. Each review was context-exposed through AGENTS.md (disclosed); after completion a stop hook showed excerpts of other verdicts to lf-rate and cauchy-moment, and neither used them. cauchy-moment saw the LF note at 952e58bd4284 (628 lines, after the joins edit) and did not open it.

### lf-rate-20261028-r1 (θ̃ and the rate of (iv) and (α))

- (A) θ̃: correct in substance. A5, (4/3 + L^{−β′})/2 < 1, needs L ≥ 3. **Repaired**: (1+θ)/2 ≤ (3 + L^{−β′})/4 once ε^* ≤ (1 − L^{−β′})/2, a γ-small condition like (T1); θ̃ ≥ (1 + L^{−β′})/2 keeps a fixed margin above L^{−β′} and L^{−1/3}. A4, the incomplete list: **repaired** (C_∗, C″_μ, C_m, C′_m, C_S″, and the K-threshold of s′_K ≤ 1 added).
- B12 (serious), the status omits the age factor at the near domains crossing ∂□₀ and ∂Y_i. **Repaired** in the rate bullet's input list, in the status of (iv), and in Open Gaps (3), (iv)/(α) sub-bullet.
- B4 (serious), the tail at σ_c's size for every generation, which its single-scale form Cε₁e^{−δ₀M₁L^j/2} does not meet. **Repaired**: the requirement is restated as σ_c's size plus C_tε₁e^{−cδ₀M₁L^j} (rate bullet and Open Gaps (3), tail sub-bullet), and the new sub-bullet *The tail part.* routes the second part through the moment split: (C_tε₁/ε_m)^{θ_V}[L^{−β′m/4}(1 − L^{−β′/2})^{−1} + e^{−cθ_Vδ₀M₁L^{m/2}}(1 − e^{−cθ_Vδ₀M₁})^{−1}], absorbed by the moment part's slack.
- B10, C_iv's j(C)-dependence is exponential through L^{θ_Vε₀j(C)}. **Repaired** in the rate bullet. It propagates to C_h through the threshold n₀ as well, so the Cauchy note's l.390, l.412, and both Constants entries (C_ν, C_a) now read "at most L^{Cε₀j(C)} times a polynomial"; the callers use them at fixed j(C).
- B11, the history's finest layer n − 1 (Cauchy §8.6, checked). **Repaired**: the same bound with C_iv·L^{β′/4}.
- B6, b for b′ in the upper bound of Lemma 2.1(i). **Repaired** at all nine occurrences in the LF note (seven of b(K − k) + C, two in C_{1.27}); the Cauchy note had none.
- B7: the Constants list now has q₁ ≥ q₀ > p₀ + r; the moment part covers the case of §1's ε₁. B1: the rate bullet states that j is the generation and m the layer (n in the bullet above).

### var-20261028-r6 (LF §4(d), the var-r5 repairs)

- S1 (serious), the telescoping order is wrong for the brackets of (1.60). **Repaired**: (iii) and (β) first for (1.59); for (1.60), (i) first at e^{iη𝐇^A(s)}c^A, then (iii) and (δ); the pieces are the same in both orders.
- S2 (serious), the U_{1,2} closure covers only (5.1c). **Repaired**: a sub-bullet *Where U_2 and the cut are read* from LFR II p.371 l.25–27 ("This configuration restricted to Z^c is equal to U_1", read), (1.54) with J_{1,2} = J_1 on Ω″^∼_{h+1} (p.370 l.39–50, read), and (1.55) with θ (p.371 l.2–5, l.19–24, read); the closure lists, in order, the half-domain lift with run B's boundary condition, r_z at U_{1,2} by (a) or (b), the lift–patch commutator, and (5.1c) at the patch. Open Gaps (3) matches. The item stays open.
- M1, closure (a) also needs (5.1c) for G at c^A: **repaired** (body and Open Gaps). The remark on (b) (collars at the layer's scale) added. Item 1's qualification added (per-z against per-X; r_z = ℓ_X for the 𝐑-terms).
- M2, ∂Y_2 and ∂Y_3: **added** (body and Open Gaps).
- M3, O(k)E₀ε₁² to O(k)E₀: **repaired**.
- M4, the header now excludes (3), (6), and (7). The Open Gaps (6) piece on (b̄) was stale: the body derives (b̄) by its own recursion (l.266–267, read in full). It is removed, and the (6) intro says (b̄) is derived, unreviewed.
- M5, the field A: Bałaban does not define it on pp.355–377; the candidates are V_Λ^{(A)} of (1.56) (p.371 l.29–32, p.374 l.39–40) and 𝐀₀, both functions of the background. The body no longer calls A shared; **new open sub-bullet** in Open Gaps (3) (what closes it: the definition of A in LFR II or LFR I; grep of LFR I found none).
- M6, G̃ maps fine sources: **repaired**. M7, δ_w now has one meaning, δ_w(ω) := N_cmax_cδ_c, and C_H no longer contains N_c.
- M8, the t_□ room. RG II p.7 l.8–11 (read) gives ½α₂ for the tζ̃_□ part and ½α₂ for the t_□ζ_□ part on Bałaban's circle, so the room is zero there. **Repaired** by taking the circle at half his radius (radius-independence of the derivative at t_□ = 0, factor 2 in (1.24)): room ¼α₂, move ¾α₂C_Hδ_w, constant 12C_H (also in the (iii) bound, 12C_HC_w).
- M9, the background of run B's walk terms: **repaired**, they are taken at ι_Yc^A; the move from c^B is in (ii) and carried through r(Y), as the walk-factor note's §5 l.124 states; then γ_w = β.
- M10, the Status duplicate is merged, and the Open Gaps (7) intro carries the qualification of the room at real points.

### cauchy-moment-20261028-r1 (Cauchy §3/§5, the plane-resolved moment)

- Serious 1, l.212 and l.214 define irr^G and (5.1c) for G without −N_j. **Repaired** (both).
- 2, Π^G is per z: (3.57)'s z-independence uses translation invariance (CRE p.281 l.59, read), as do (3.62)–(3.63) (p.282 l.44, read). **Repaired** in the header, the definition of N_j, and *Evidence.*.
- 3, (3.49) without Euclidean symmetry. RG I removes the first-moment terms of (I.4.34) by the Euclidean symmetries (p.290 l.13–15, read, with (4.34) on p.289). In CRE's version all factors are B moved to z (p.280 l.22–25, read), so each first-moment term has a constant slot B(z). The Ward identity at λ = cx_κ, with the first variation at 1 zero, gives Σ_x𝐄^{(2)}_{κν}(X, x, y, z) = 0. **Derived** and written into *Evidence.*.
- 4, Re tr changed to tr (holomorphic; real at real configurations). 5, the first variation vanishes by Ad-invariance (RG I p.264 l.9–10), not by the reflections. **Repaired**.
- 6, affine reproduction. **Derived**: φ := ℓ(MA_aff) − A_aff with its multiplier solves the homogeneous constrained system, and the exponentially decaying inverse (VAR (190), PBG (3.42)) gives 𝒢𝒜 = I on pairs of polynomial growth, so φ = 0 in the lift's gauge. The composition wording and the block-translation covariance of the Fourier form are stated.
- 7, C_α counts the 36 plane pairs (n = j and n > j). 8, the (W) citation goes through ONE_LOOP_PROOFS Remark 2.3, Theorem 8.1, and Proposition 2.4 (read). 9, λ_Q needs B₃ ≥ ½ (stated); C₀, C_r, and Δβ disambiguated in the Constants and at (5.1); the "4-cell" of §5 is now the ε-cube. The loose factor 16 and the redundant C_X are left (both harmless).

Hashes after the repairs: LF note 638 lines, 15ce72b29005; Cauchy note 952 lines, 8b42e1e7397a.

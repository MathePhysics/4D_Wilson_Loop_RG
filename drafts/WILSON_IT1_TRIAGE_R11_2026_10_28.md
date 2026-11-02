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

## Gap closures after the triage (15:20–15:36)

- **The field A of LFR II p.377 l.7 (LF Open Gaps (3)).** Closed, unreviewed. A is 𝐀₀ := 𝐇_{k,Λ}((1/i)log M^·(U_0(𝐔))), the analytic extension of p.367 l.46–49 (read) of LFR I's 𝔸₀ of (1.86)–(1.87) (p.197 l.25–38, read), U_0^{(AL)} = exp iη𝔸₀ in Λ. p.368 l.4–7 (read) names B, 𝐀₀, and V″ as the fields of U″_{k,Z″_{h+2}}, the three fields of p.377 l.7. On pp.355–377, 𝐀₀ occurs only at p.367 l.48, p.368 l.5–11, and p.370 l.16, l.41, l.45 (grep of the transcriptions), always as Q̃_·(η𝐀₀) with exp iQ̃_·(η𝐀₀) = M^·(U_0^{(AL)}) (p.370 l.15–16, read): the data of U^0_k, the configuration (1.50) at B = 0 (p.370 l.14). The open item had wrongly listed it as undefined on these pages and as a fixed point; RG II's 𝐀₀ (p.2 l.36–38, read) is a different object. Written as *The field A* in §4(d)(ii): A is the link image M^·(c_{U^0_k}) on Λ ∩ Ω″^{∼2}_{h+1}, equal to each run's A at its chain in the common gauge of §4(c), with the run difference of §4(c)'s *The data difference.*, contained in d̄ (l.430, "(c) through U_0"). The Open Gaps sub-bullet is removed; (ii)'s *The entries.* now stands as its own sub-bullet.
- **The exceptional constituents of a deep V(Y) (LF Open Gaps (10)).** Closed, unreviewed. p.373 l.13–14 (read): every term of the second-stage sum "has a localization domain X intersecting Z"; the first-stage terms have domains Y₀ containing a component of Λ^∼ (p.372 l.17–18, read). *The Constituents.* had described the re-summed terms as the old terms disjoint from Z; corrected. For the constituents with all Y′_i empty (p.376 l.43–46, read), X is connected and joins a point near the deep point y to Z, so it crosses the N layers inside W; half of exp(−βκd_i(X)), which remains after Bałaban's extraction through d_k(Y₀) ≥ d_{k,Z}(Y), gives e^{−σ_V} per layer, and the other half controls the resummation of p.376 l.45–46. New constant C_E and r_E := 2e²C_E2^{−k_s/16}; the §8.6 bracket is 2(r_D + r_E) and ν_j's deep-V(Y) term carries C_V + C_E. Open Gaps (10), the §4(e) status line, the §8.6 change list, and the Status paragraph updated.

Hash after these closures: LF note 643 lines, 31eb6613edf4.

## Reviews launched about 15:45, and the next gap

- Launched in the background: lf-tail-20261028-r1, var-20261028-r7, cauchy-evidence-20261028-r1, lf-deep-20261028-r1 (packets at LF 31eb6613edf4, Cauchy 8b42e1e7397a).
- LF Open Gaps (3), the conditions of LFR I (1.64)–(1.69) at the other members: narrowed, still open. Read LFR II p.373–375 and LFR I p.198: U_1 and U_{k,Λ} are the representation configurations (1.62) and (1.63), so the item's old wording ("other than U^0_k and the representation configurations") was confused; U_k is 𝐔; the second-stage terms read U^0_k only (p.375 l.29–35), covered by (1.65); the proof of (1.89) is a real-configuration argument. What remains: a quantitative form of Bałaban's two "almost the same" statements (p.375 l.1–10) at the halved thresholds, and the conditions at U_{1,2} for the first-stage expressions (p.373 l.1–6). This edit was made after the packets' hash.

## The four reviews (written 15:47–15:52), triaged until 16:14

Every report was read in full. All findings were repaired in the notes except the ones named below.

### lf-tail-20261028-r1 (LF §4(d), (iv) and the rate in the layer)

- Serious, B9(a): the current along the pair line was missing from the inputs of (iv) and (α). Repaired: the (iv) status names it, with the reason (the Cauchy note derives it only at the global single-scale real minimisers, through §10.3's multipliers; with the lifted current's size alone, (5.1v) is only polylogarithmically small), and Open Gaps (3) and the input list of the result carry it.
- Minor, repaired: the ε^* condition against (T1) (Cauchy §8.7, l.400); the units of the tail (the layer m of z); ι_X against ι_Y for the moment defect's decay; (1 − L^{−θ_Vδ₀M₁})^{−1} and (1 − L^{−cθ_Vδ₀M₁})^{−1} in place of the e-based factors; the dependence of C_iv on C_t and c; "n > k_s/8, i.e. k < 8n + j(C)"; the cost θ̃^{−1} at the layer n − 1; the missing inputs LFR I (1.64)–(1.69) and the reduced-threshold reading; (5.1v) unreviewed.
- B8 is conditional on l.437; no action.

### lf-deep-20261028-r1 (LF §4(e), the deep V(Y))

- Serious: the completions of LFR II p.377 l.22–26 were missing. Repaired: new sub-bullet *The Completions*, derived under the reading (R-C) that a completion is re-summed as an exceptional constituent, with r_C := 2e²C_C2^{−k_s/16}; totals now r_D + r_E + r_C.
- Minor, repaired: the condition (κ-½) (κ ≥ 2κ_B and ½βκ ≥ 1; CRE p.260 l.27–28, LFR II p.389 l.12); the CRE p.263 citation and the matching of step-i and step-j layers; the status labels of §4(e) and of the deep V(Y).
- Not repaired, out of the packet's scope: the §8.6 factor.

### cauchy-evidence-20261028-r1 (Cauchy §5, the moment of the lifted term)

- No fatal or serious findings.
- Minor, repaired: 2c, the constrained inverse was mis-cited, now through PBG (3.126), (3.128), (3.148), and (3.153), with 𝔊G^{−1} = I − GDRD* − ℓ₁Q; 2b, the affine step, now RD*A_aff = 0 since R annihilates constants at U = 1 (PBG (3.25)); 1b, the citations ((I.4.14) p.284 l.19–25, RG I p.290 l.25–26, (4.23)–(4.25)); item 3, Π^G(z) and the per-z form of (2.43); 1e, the dependence of (3.66) on the affine reproduction of run A's lift.

### var-20261028-r7 (LF §4(d), the field A, U_{1,2}, the telescoping, and (iii))

- Fatal, F1: the A of LFR II p.377 l.7 is Bałaban's system of fluctuation fields {A_{j−1}} (CRE (2.23), p.258 l.47–48), the argument of 𝐁_k(U″_k, A) + 𝐁″_k(U″_k, A) of (1.49) (p.369 l.14), not 𝐀₀. Checked against CRE p.258, p.261 l.47–66, p.267 l.40–44, and LFR II p.369. Repaired by splitting the item. *The fluctuation fields A* (derived, unreviewed): the variables of the postponed 𝐓^{(j)} on Z_{j+1} ∩ Ω_{j+1}, on the scale-j lattice, with the operator C determined by {Ω_j}; a matched pair has the same domains and, by (M), no postponed variable at run B's extra step; so the matching is the identity, as in the Cauchy note's §6.2, and V^B(Y)[c] takes A as a shared real argument; the gauge is consistent since ṽ = v on T_ε. *The field 𝐀₀* (derived, unreviewed): a function of 𝐔, so not a separate variable.
- Serious, S1: in the (1.60) brackets the renormalised 𝐄-combinations leave a remainder at the decoupled configuration. Repaired as the new piece r^s_z, the first three parts of r_z with ι_X; open, with no age partner, closed by (b) of the r_z item. Added to the piece list, the telescoping, l.442, and Open Gaps (3).
- Minor, repaired: M1, the 𝐀₀ citations ((1.61) p.373 l.21, (1.62) p.373 l.40, p.375 l.9; p.368 l.4–7 dropped); M2, the reading of 𝐀₀ through U^0_k is a choice that the bound of f on the disc must cover, the gauge through run A's ū₀ (§4(c)), and C_U(M) ≥ C′_Δ(M); M3, (1.54) expands U^0_k around U_{1,2} and (1.51) U″_k around U^0_k, and U_{1,2} enters p.373 l.2–3 and l.34–35; M4, the size and the current of the half-domain lift in the closure list; M5, "each bracket's difference is a sum of pieces from the list"; M6, C_H := 3B₀′e^{16κ₁}S_H/ρ_H, the linear move on the disc |u| ≤ R = 1/(3C_Hδ_w), and C_Hδ_w ≤ 1/6; M7, the sum into (1.68) derived for the 𝐑- and 𝐁-terms and open for the renormalised 𝐄-combinations (added to Open Gaps (7)); M8, the walk-factor pointer (its §5, not l.124) and γ_w = β conditional on the exponents of (Wδ-2) and (Wδ-3); M9, the two sets called 𝐁₁; M10, the mixed-term factor (1 + max_cδ_c)^{N_c(|ω|+1)−1}, whose product with |ω| + 1 is at most 3·2^{|ω|} for N_cmax_cδ_c ≤ log(3/2), and the bound (1.11) with 3δ_w(Y).

Hashes after the repairs: LF note 659 lines, 53e0c3351f7f; Cauchy note 956 lines, 072a416bac60.

## The joins 𝐁₁ and 𝐁₂, 16:14–16:26

- New bullet LF §4(b), *The joins (derived under the reading (R-J), unreviewed).*
- The collar layers of CRE's 𝐁_h(Ω) are ≥ LM₁ wide in their own units (CRE p.256 l.57–60). (2.14) alone gives the joined layer no width (p.257 l.7–11, p.256 l.61). On 𝐁₂'s side, CRE's 2MR_h does not fix the distance from ∂Ω″^∼_{h+1} to ∂Ω_h (LFR I (1.11)–(1.12)).
- The count: PRT2 (2.58)–(2.61) use (2.2) only through (2.57), so they hold with RM replaced by any common lower bound W of the layer widths.
- Reading (R-J): Bałaban's use of VAR's minimisers U_{𝐁₁}, U_{𝐁₂} (LFR II p.370 l.22–23) and of VAR Sects. D–E for (1.54) (l.38–43) is read as VAR's (1) for the joins with R ≥ R₁. So W = R₁M₁ and R₁ < L. The top N₀ layers of 𝐁″_k are M > L²M₁ wide and need no reading.
- Condition (J-W): (2.59) at α = 1/128 and ⅛δ₀R₁M₁ ≥ 4 log L + 1. PRT1 Proposition 1.2's δ₀ depends on d only. PRT2's δ₀ in (2.43) comes from its reference [3] (CMP 89), whose M₁-dependence is not checked.
- Open Gaps (3), first sub-bullet: the joins part is replaced by this; the fine side σ_c stays open. Status and l.192 and the open item of (ii) updated.
- Hash at 16:26: LF note 666 lines, 7021db178666.

## Readings Replaced by Source Checks, 16:31–16:52

The user asked why the note kept readings when the sources could be checked. They should not have been there. (R-J) and the δ₀ question were both settled by papers the text cites, and stopping at LFR II's wording put an unchecked step in the place of a derivation.

- (R-J) is removed. CRE (2.14) and p.256 l.57–62, LFR I p.179 l.6–7 and (1.11)–(1.12), and PRT2 (2.47) give the widths directly. In 𝐁₁ every layer is ≥ LM₁ wide in its own units: the collar is ≥ LM₁, and the joined layer h is ≥ LMR_{h+1} − 2M₁. In 𝐁₂ every layer below the top is ≥ LM₁ wide, by four junction cases that use dist(Ω_h, Ω_{h−1}^c) ≥ M₁ and Ω^{∼−2} ⊂ Ω_h. The top layer of 𝐁₂ can be thin, but PRT2's crossings join Σ_j and Σ_{j+1} and lie in the lower layer, so it is never crossed. So W = LM₁ is derived.
- The δ₀ question is answered from RDG, PRT2's reference [3]: RDG's constants depend on d and the big-block size M (p.573 l.19, p.574 l.4), and its printed rates are M^{−1} ((2.22), p.579 l.11–22) and ½δ₂M^{−1} with δ₂ = ¼δ₀ ((5.21), p.596 l.18–29). The earlier claim that (J-W) holds for M₁ large at fixed L was wrong. M₁ cancels from ⅛δ₀LM₁, and (J-W) is a condition on L at the constant δ₀M₁, whose L-dependence RDG does not print. M is fixed through L-dependent constants ((5.3), p.593 l.46–47). (J-W) is now an Open Gaps (3) item.
- (R-C) is removed. LFR II p.377 l.24–25 says the completions "may be resummed in domains Y described above", so the assignment is a construction choice. The rule of the exceptional constituents, X ↦ Y₁(X) of p.373 l.15–16, is that choice, and Y₀ ∖ Z = Y₁ ∖ Z (p.376 l.44) depends only on X and Z.
- (R-Z) is relabelled as Bałaban's convention (LFR I p.177 l.33–35), which three printed statements force. The tree-length scale convention (l.532) is relabelled as forced by CRE p.264 l.1–3. Its citation is corrected to CRE p.263 l.6–8 and l.21–22. The 𝐀₀ entry is relabelled as a choice of the construction.
- What remains: *Bałaban's Statements at the Reduced Thresholds* is a reading, already open, and its closure is the check of every use of C₀ and C₁.
- Hash at 16:52: LF note 669 lines, 5f25f115853e.

## The Reduced Thresholds Checked, 16:53–17:23

The user asked for a check of *Bałaban's Statements at the Reduced Thresholds*. Every use of C₀, C₁, and the thresholds in CRE, LFR I, LFR II, RG I, and RG II was read, and the section is now derived (unreviewed).

- *The construction.* No cutoff and no construction parameter involves C₀ or C₁: ε_j (CRE (2.4)), δ_k (CRE p.265 l.39), ϑ_k, and the number of usual steps N = R_j (LFR II p.384 l.17). C₀ and C₁ enter only spaces, extensions, and bounds. The C₀ of LFR I (1.70) is a bound constant, and the α₀ of LFR I p.200 l.35 is an exponent.
- *The three kinds.* Every restriction is of one of three kinds.
  - Upper bounds, met for γ small at fixed C (RG I Theorem 3: γ depends on all other constants). In LFR II (1.47) L^{−R_j} beats every power of log g^{−2}.
  - Homogeneous relations (RG I pp.277–285, RG II p.7).
  - Lower bounds against C-free sizes (LFR I (1.44)–(1.52) behind the step statement, LFR II (1.65), RG I p.273 and p.280, RG II p.7 and p.20). These are what "sufficiently large" provides.
- *The order of the constants.* B₃ depends on d and L only (VAR p.279 l.28), and C_{Q*} = 2(1 + (2d + 1)L^{d−1}). So λ_Q comes before C₀ and C₁, and C_i/μ ≥ K_i for the five μ.
- *A correction.* The old text said the lower bounds hold "since α_{i,j}/ε_j grows as a power of log g_j^{−2}". That needs q > p₀, which the print does not give. The derivation now uses C_i/μ ≥ K_i instead.
- *(R-m′).* No printed upper bound on q₀ or q₁ was found. They occur only in (2.28) and in the factors q₀(g_k) and q₁(g_k) of LFR II (1.47) and p.379 l.31, both upper bounds met for γ small.
- *Edits.* The LF note's Open Gaps item is removed, and so is item (3) of *The room at complex points.* The status mentions are relabelled at l.24, l.456, l.474, l.479, and l.480. The Cauchy note's l.12 and l.122 now cite the derived item.
- Hash at 17:23: LF note 693 lines, 4e83b87b6740; Cauchy note 956 lines, 9bbaae7f37cc.

## (J-W) Closed for M₁ Large, 17:23–17:41

The user asked to close Open Gaps (3). The first item taken was (J-W), and the conclusion of 16:31–16:52 that M₁ cancels is wrong.

- *The error.* RDG's rates ∝ M^{−1} are in RDG's own big blocks, whose size is "a large positive integer defined later in this paper" (RDG p.572 l.11–13), fixed by 3^dc₂O(1)M^{−1} ≤ e^{−1}. That size is a constant of RDG's proof, not the domain's M₁-cubes, so δ₀ does not scale with M₁.
- *The rate.* PBG Theorem 3.1 prints M₁, δ₀, a₀, and B₀ "dependent on d and L only", valid "for M ≥ M₁", M the big-block size (PBG p.397 l.37–38). The distance is PRT2 (2.46), in the block units of each layer (p.231 l.9–13).
- *The choice of M₁.* With c₀(1/256) < 1024/δ₀, (J-W) holds once M₁ ≥ M_J(d, L) := max{8(4 log L + 1), 512(2d log(1024/δ₀) + 1)}/(δ₀L). CRE's M₁ is the size of large cubes for which the earlier theorems hold (CRE p.245 l.35–37), and those hold at every larger size, so M₁ is a power of L at least M_J(d, L), chosen before M₂ = L²M₁ and M.
- *Edits.* LF note §4(b) *The joins.* is derived (unreviewed), and the (J-W) bullet is replaced by the three points above. l.9, l.34, l.192, and l.453 are updated, and the separate (J-W) Open Gaps sub-bullet is removed. The memory check-sources-before-readings is corrected.
- Hash at 17:41: LF note 695 lines, bddff9c0b1aa.

## The Fine Side at the Chain and the Lift ι_Y, 17:41–18:13

The next two sub-items of Open Gaps (3), the fine side at the multiscale chain and the tail of ι_Y, are derived (unreviewed) in two new blocks of LF §4(d)(ii), placed before *The bounds of V(Y) (quoted).*

- *The Fine Side at the Multiscale Chain.* It covers c ∈ {U″_k, U^0_k, U_{k,Λ}, U_k} at real data.
  - The one-step problem of ι has a single layer, so the chain's layers enter only through the sizes of the sources, which VAR (9)–(10) bound layer by layer (p.279 l.19–26).
  - Every kernel is ≤ Ce^{−δ_f|x−y|/ε}, δ_f := min(δ₀, δ_Q^{pl}), by PBG (3.42), (3.44), and Theorem 3.13. The Hölder factor at one step is 2L^{ε₀} (ξ′ = 1/L, PBG p.397 l.17–18).
  - The smeared weight Ŵ(x) := sup_y e^{−½δ_f|x−y|/ε}(a_{j(x)}/a_{j(y)})²d̄(y) satisfies d̄ ≤ Ŵ ≤ L^{7/3}d̄ under (F-W): ½δ_fW ≥ (7/3)log L for W = RM and LM₁. The layer widths are from PRT2 (2.2) (p.224 l.8–13) and the joins.
  - The bound is linear. The derivative of ι along V_t := e^{itεA_c}Mc^B is integrated in t, as §9.8 integrates δℋ/δB, so no weighted-norm contraction is needed. The result is σ_c ≤ C(ε₀)d̄ ≤ C(ε₀)(a_k/ε)^{ε₀}d̄, with the ι_Y tail ≤ C′d̄ absorbed.
  - The lift condition of (i) holds at these members, for ι_X and ι_Y. The current is from RG I (1.8) with VAR (10).
- *The Lift ι_Y.* The collar of Y^∼ is formed from the scale-k M₁-cubes (CRE p.256 l.57–63, LFR II p.376 l.25–31).
  - The tail is ≤ C_tε₁e^{−½δ₀M₁L^k} in the units of every layer. It uses the crude bound |F(ιc^A)| ≤ C_Fε₁/ε², with C_t := 2C_ιe^{δ₀(R/L+2)M₁}(4/(eδ₀M₁))².
  - The moment defect is ≤ C_Π(j)E₀e^{−δ₀M₁L^k}, by §9.8's linearisation at 1 with the scale-k collar.
- *Not covered.* The composites U_j(𝐁_j(□₀), ·) of (1.59) (LFR II p.372 l.7–8) are not covered, since no identity ι(Mc^B) = c^B is derived for them. Neither are U_1 and U_2, which belong to the U_{1,2} item, nor complex points. The composites' fine side and tail stay among the inputs of (iv).
- *Edits.* l.395, l.405, *The joint line.*, the rate of (iv) (configuration part, moment part, and result), *The room at real points.*, the complex-class bullet, and the (iv) status were updated. "Four inputs" became "Three inputs", and the fine-side input was removed. Open Gaps (3) sub-items 1–2 were folded into its lead paragraph, and the Status lines were updated.
- *A lead from the user's file.* The user asked for a check against `WILSON_IT1_LF_GAMMA_REPAIR_ATTEMPTS_2026_10_28.md`. Its §2 pays the shrinking margin β2^{−(i−m)} of the old 𝐁-terms at complex backgrounds (LF §4(e), *Complex Backgrounds*) with one unit of the boundary decay, e^{−d_i(X)} ≤ 2^{1−r} (CRE p.264). That contradicts the LF note's "a room of that size doesn't work". This is the next item to check.
- Hash at 18:13: LF note 713 lines, d4af4a2a4682.

## (10) at Complex Backgrounds, 18:13–18:29

The first sub-item of Open Gaps (10), the variation of the old 𝐁-terms at complex backgrounds, is derived (unreviewed) in LF §4(e), *Complex Backgrounds.* The LF note's "a room of that size doesn't work" was wrong.

- *The room.* CRE (2.34)–(2.39) print the prefactor 1 − β(1 − 2^{−(j−n)}) (p.261 l.14–40). With the shift using at most half of a step's shrinkage (p.277 l.1–7, read as at real backgrounds), the room at a layer m < i is ≥ ¼β2^{−(i−m)}α_m. The room at m ≥ i is ≥ ¼βα_m, for L > 11 (RG I p.251 l.14). (2.38) conditions only the G-valued factor U, which the path keeps fixed. This is the repair note's (G.2).
- *The moves.* There is one joint line through the background and the complex fluctuation. Its real points use *The Room at Real Backgrounds.*, and the Lemma (Two Constants) gives the power 15/16, as in LF (d)(ii) at complex points. The path is on run A's lattice, so no lift is needed.
- *The factor 2^{(i−m)}.* It is paid by the ratio's slack, not by decay. Since θ̃ ≥ (1 + θ)/2 ≥ ½ (Cauchy note §8.7) and i − m < 7k_s/8 + j(C), the condition (L-V) L^{5(1−ε₀)/128} ≥ 4 suffices. (L-V) is a lower bound on L; RG I p.251 l.14 prints L only as "an odd, positive integer > 11".
- *The repair note's route.* Its §2 pays 2^r with e^{−d_i(X)} ≤ 2^{1−r} (CRE p.264 l.2–3). That leaves the decay κ − 1, which, as its (G.4) states, does not enter the κ-norm b_i without a loss. The CRE p.260 l.27–28 freedom in κ would then be needed at κ − 1 in Bałaban's step derivations, which is not checked. The L-route avoids this, and Bałaban's κ is unchanged.
- *Edits.* The §4(e) heading, *The Variation at the Fluctuation Step.*, (ii) of "The step map", "The recursion", the Cauchy note's §8.6 bullet, Open Gaps (10), and Status were updated.
- Hash at 18:29: LF note 734 lines, 286879c8a150.

## The Current at the Multiscale Chain, 18:32–18:54

The (3) sub-item on the current part of the joint line is closed at the real members U″_k, U^0_k, U_{k,Λ}, and U_k: a_{j(x)}³|ΔJ_c(x)| ≤ Ĉ_Jd̄(x) (LF §4(d)(ii), *The Current at the Multiscale Chain.*, derived, unreviewed). At complex points it remains open, together with the complex lift (*The Fine Side at Complex Points.*).
- *The representation.* Each member is a VAR minimiser under multiscale constraints, in each run at its own data. So the multiplier representation of (d) holds at it, J = Q_db*ν = 𝐐*λ. Run B's set factors through M (*The joint line.*), which gives J(c^B) = Q₁^{pl}(c^B)*J′_c and the split of the Cauchy note's *The current along the pair line.*
- *A weak point of (d) found and repaired.* (d)'s *The multipliers.* bounds f_y(U^A) − f_y(Ũ) with a single Cauchy disc of radius α₁/(2d̄). That radius uses the supremum of d̄ over the whole volume, which is set by the finest layer of the volume, older histories included, so the bound is not local. The repair takes the difference at the fixed right inverse R₀ = H₀(Ũ_c):
  - R^A := R₀(1 + E)^{−1}, with E := (Q_db(c^A) − Q_db(Ũ_c))R₀. E's kernel is bounded by a local Cauchy estimate, since Q_db is local in U, and the Neumann series converges under (T-E).
  - The difference then splits into three parts: (I), the weak form of the action's derivative at a fixed field, through the second variation; (II), the Neumann correction, which is relatively ε₁ smaller; (III), the blocking artifact.
  - The weight facts (LW₀) and (LW) turn the pointwise d̄(p) into d̄(y), using the layer widths in the multiscale distance. They need ¼δ₀W ≥ log L, which (b)'s ⅛δ₀RM ≥ 4 log L + 1 and M₁ ≥ M_J(d, L) give.
  - A sentence in (d)'s *The multipliers.* now points to the pointwise form.
- *The current part.* r_J(Y) ≤ 4(1 + β₀)Ĉ_J max d̄/α_m, which *At real points the ratio is small.* bounds, so the current part is ≤ C_hθ̃^n per point. The room at members other than U^0_k rests on their (1.64)–(1.69) conditions, which are already an open item.
- *Self-check repairs.* Two points were repaired before logging. The transport moves of the multistep averaging are counted over all levels (4dL, not 4d). The current room's dependence on (1.64)–(1.69) at the other members is now stated.
- *Edits.* The new block; *The current of the line at complex points.* in **Open: the variation of the chain.**; the room bullet and its heading; Open Gaps (3), its lead and sub-item; the two "only at the global single-scale real minimisers" passages; and Status.
- Hash at 18:54: LF note 772 lines, 8dd8b32d07bd.

## The Fine Side and the Current at Complex Points, 18:57–19:24

The open complex-point items of (3) are closed: the fine side, the lift condition at the members, and the current of the line. All three are derived and unreviewed. They are in LF §4(d), *The Fine Side at Complex Points.* and the current block's *At complex points*.

- *Sources read.* VAR pp.308–309, which gives (185)–(190) and Proposition 9, and VAR (19)–(21) at p.281 l.5–19. PBG pp.396–407: the complex class (3.37)–(3.38), Theorem 3.4 at p.400 l.7–10, (3.86), and Theorems 3.10–3.13. RG I p.273 l.1–3, and RG I (1.17) at p.263 l.10–18.
- *Analyticity.* The real construction (*The bound.*) is a flow in t. Its right-hand side is Φ(W)A_c, the derivative of the solution map ℋ at the external configuration W.
  - Φ is analytic on PBG's complex class by Proposition 9. The operators there keep their bounds by PBG Theorem 3.4 and by VAR p.309 l.1–4, which covers 𝔊 and H₁.
  - The Picard iterates are analytic in z and converge uniformly, so 𝐒^ι(1, z) is analytic on the disc by Weierstrass. At real z it is the real solution, by uniqueness, so no gauge comparison is needed.
- *Class membership.* ι's problem is single-layer, so its class (3.37)–(3.38) is in ε-units. The lattice bound on differences (2L/ε each) gives the ∇ and D*D parts from the sup part. This gives the condition (T-ι) on ε₁′, with a₁^{PBG} named apart from VAR's a₁.
- *The crude bound.* 𝔐_S = 8C_δ(ε₀)L^{7/3}M_c + 4C^c_tε₁′ ≤ 1. It comes from the flow with the alignment field's disc bound M_c, layer-adapted through (F-W). The tail is bounded at complex points through (190) and |F(ιc^A(z))| ≤ C^c_Fε₁′ε^{−2}. Then the Lemma (Two Constants) gives 𝔰 = 8σ′^{15/16}, unchanged.
- *The current.* 𝔣_J := ℓ(a³ΔJ_c(z)(x)) is analytic, and 𝔪_J = 2Ĉ_Jd̄′ at the real points.
  - 𝔐_J = (2C_{Q*} + 1)C^c_Jε₁′ ≤ 1. It comes from RG I (1.8) with VAR (9)–(10) at the base and (19) for the move.
  - The result is a³|ΔJ_c| ≤ 2Ĉ_J^{15/16}d̄′^{15/16}, with T^c_J; the ratio is bounded through *The Ratio.*
- *Self-check repair.* A first draft of the lift condition at complex points used "ε₁′/α_m → 0". This is false: ε₁′ contains C_c(α̂₀ + α̂₁). The members' own quantities now come only from *The Room.* (Bałaban's (1.65)), and the 𝔰-moves come from r(Y) ≤ ½ (*The Ratio.*).
- *Rejected route.* Proposition 9 alone gives a crude bound in ε-units, whose gradient part costs L^{2j} at the layer j. That bound doesn't work, since 𝔐^{1/16} would cost L^{n/2} against L^{−5n/16}.
- *Still open in (3).* f on the disc, r_z, r^s_z, (iv)/(α), (β)/(δ), U_{1,2}, the near domains, and (1.64)–(1.69) at the other members. The current part at complex points and the lift condition there rest on (1.64)–(1.69) at the members other than U^0_k and U_k, as at real points.
- *Edits.* The new fine-side block replaces the open one. The current block's complex bullet is replaced, and *The current part at complex points* is added. The open bullet *The current of the line at complex points.* is removed ("Three" → "Two inputs"). Also edited: the Open Gaps (3) lead and its current sub-item, the room-at-complex-points bullet, and Status (the derived list and the review list).
- *Repair-note comparison* (WILSON_IT1_LF_GAMMA_REPAIR_ATTEMPTS_2026_10_28.md, read only):
  - §15, the envelope route to the multiplier difference, is consistent with the fixed-right-inverse repair, and it refuses unlocalised bounds as the repair does.
  - §4 (G.14)–(G.16) is consistent with the open (β), (Wδ-3), and (δ).
  - §17 consumes |ΔV(Y)| ≤ u·a_Y, the form (3) gives.
  - §10.6 points to Proposition 9 for the analytic extension, which this closure uses.
- Hash at 19:24: LF note 781 lines, ec9e21ce08d1.

## The Single-Background Shortcut for f, 19:30–19:35

The user asked whether the shortcut works: write the joint line as run B's member maps applied to one complex background 𝐔(z), so that Bałaban's (1.68)–(1.69) bounds f directly. It doesn't work.

- For c ∈ {U″_k, U^0_k, U_{k,Λ}}, run B's constraints factor through M (LF *The joint line.*), and Mι_YU = U on Y^∼. So ι_Yc^A_c has run A's data.
- Run B's member at given data is unique up to gauge (VAR Theorem 1). So the member equals ι_Yc^A_c only if 𝐒_c = 0, which is false at nonzero depth at equal data.
- No line through run B's chains at single backgrounds reaches the endpoint, and l.447 already noted the companion failure of V^B∘ι_Y. The bound of f on the disc stays a multi-variable statement.
- One "doesn't work" line was added after l.447.
- Hash at 19:34: LF note 782 lines, d41a56ff483c.

## The Bound of f Reduced, 19:36–19:45

The user asked for the multi-variable (1.68). It is reduced to two inputs (LF §4(d), *The bound of f on the disc*, unreviewed).

- *Read.* LFR II pp.376–377; CRE pp.279–280 (the proof of Theorem 2); RG I pp.275–277, (3.26)–(3.36), and p.285, (4.16)–(4.18); VAR (9) at p.279; PBG (3.43)–(3.45) at p.398.
- *The reduction.*
  - (1.68) is a sum of term bounds (p.376 l.1–42).
  - The old terms are analytic on spaces of configurations (RG I p.277 l.41–43).
  - The renormalisation is set up for a minimiser times an arbitrary regular field 𝐀 of RG I (3.31) (p.276 l.27–41). The entries e^{it(ε/L)𝐒_c}c^B have this form, so the minimiser property is used only at c^B.
  - The note's earlier claims are replaced: that a replay of Bałaban's proof does not give f, and that the renormalisation is the hard step.
- *Still open.*
  - (F-H): the Hölder part ‖𝐀‖_{1,β} of (3.31) at the Cauchy note's index β_H ≥ 19/20. The trivial lattice bound costs (a_n/ε)^{19/20} against d̄'s (ε/a_n)^{(1−ε₀)/3}. That doesn't work.
  - The possible route: the terms read only block averages Q(η𝐀) at their own scale (RG I (3.33)), and (4.18) is a bound on those. Not derived.
  - Also open: the conditions at the link images, which is the existing item (1.64)–(1.69) at the other configurations.
- *Self-check.* The first draft used β_H ≤ ε₀ and "any β_H > 0". This was false against the Cauchy note's β_H ≥ 19/20 and was corrected before logging. The name β_H matches the Cauchy note's Hölder index, kept apart from the thresholds' β₀.
- Hash at 19:45: LF note 789 lines, 1e2ca89477f2.

## (F-H) Closed, 19:46–19:49

(F-H) is derived, unreviewed (LF, *(F-H) The Hölder part of (3.31) at the entries*).

- *Read.* RG I p.279 (3.48)–(3.49), p.285 (4.17)–(4.18), p.288 l.28–40, and p.298 l.1–8.
- *Where the Hölder norm enters.* It is used only through (4.18), to make the second-order Taylor remainder of B irrelevant (power 4 + β; p.288) and the third-order terms of (5.43) irrelevant (p.298). The analyticity (3.36) does not use it.
- *The split.* B = Q(minimiser) + Q′, with |Q′| ≤ O(1)L^jη|𝐀|. The minimiser part keeps (4.18) by VAR (9). Q′ gets the lattice bound |∂∂Q′| ≤ 2max|∂Q′|, which leaves a marginal excess O(1)E₀sup|∇𝐀| per layer cube and per generation.
- *The bound.* There are at most k ≤ 2(n + 1) generations, so sup|f| ≤ (α + C_Fkc_ρ max α_m)e^{−(1+2β)κd_{k,Z}(Y)}. The factor k is absorbed as C_hkθ̃^n ≤ C_h′θ̃^{n/2}. Only lower bounds on θ̃ are used downstream.
- *Self-check.* The first draft had n generations; it is now m ≤ k at the layer m.
- *What remains for f.* Only the conditions at the link images: the existing (3) item, LFR I (1.64)–(1.69) at the other configurations.
- Hash at 19:49: LF note 794 lines, 591103b5ffc6.

## The Conditions at the Other Members, 19:50–19:58

These are derived, unreviewed (LF §4(d), *The conditions at the other configurations*).

- *Read.* LFR II p.375; LFR I pp.190–191 ((1.64)–(1.69)), p.192 ((1.70)), p.193 l.18–30, p.195 l.18–26, and p.198 ((1.89)).
- *U^0_k.* The second-stage terms read U^0_k only, and Ũ″^c_k(Y_1) lies in all terms' analyticity domains (p.375 l.29–35). This is (1.65), as before.
- *U_k.* Covered by §3(d).
- *U″_k.* The 𝐁-terms' domain is the space of LFR I (1.70). At real points U″_k lies in it (LFR I p.195 l.20–24, through (1.80) at the size of ε_j), which is a C-free lower bound. So it holds at α̃′/2.
- *The determining-set configurations.* LFR I's space at 𝕌 also bounds U_{p,X}(M^·(𝕌)) and J_{p,X} (p.190 l.17–18). So the representation configurations of an entry's data have their conditions in that entry's space.
- *Still open.* U_1 and U_2 fall in the U_{1,2} item. U_{k,Λ} and the extended (1.62)–(1.63), where they are not U_{p,X}(M^·(·)) of a single entry, are read only as the backgrounds and arguments of 𝐇_{𝐁₁} and 𝐇_k (p.375 l.4–13), so they belong to (β).
- *Effect on f.* f no longer has an input of its own. Its remaining dependencies are the existing items U_{1,2} and (β).
- Hash at 19:58: LF note 800 lines, 7505cdddd650.

## Triage of lf-cxbg-20261028-r1, 20:13–20:29

The review covers §4(e) at complex backgrounds, the deep V(Y), and the completions. It found nothing fatal. Every finding is repaired in the LF note.

- *DV-5 (minor to serious): the crossing cost for completions of generation i < k.* *The Crossing.* had used "a term whose domain meets a renormalised component is integrated with it", which does not apply to completions. Replaced by monotonicity of the layer indices. A fluctuation step adds Ω_{k+1} and keeps Ω_1, …, Ω_k (CRE (3.5), p.265 l.42–44). An R-operation replaces Ω_l by Ω″_l ⊇ Ω_l inside Z, since Z″_l ⊂ Z_l, and keeps Ω_l outside Z (LFR I (1.10)–(1.12), p.179). LFR II uses the same Ω″_l (p.362 l.10). So step-i units are no coarser than step-j units, for integrated terms and completions alike. *The Completions.* now cites this.
- *DV-2.* The phrase "in the finest layer" is gone; the new text says "inside the current top layer Ω_k".
- *DV-3 and CB-10: the order of constants.* κ is fixed before R. κ_B does not involve R, since Bałaban's resummations hold at every k with one κ while the widths MR_k grow (CRE (2.5)). In §4(e) the order is ε₀, then L under (L-V), then the L-dependent constants with κ before R, then n₀ and C_h.
- *CB-6: the citation slip.* The text now reads "the profile of (b) at equal data bounds the alignment field".
- *CB-6: the current-move input (UNCLEAR, inherited).* Now derived. The configuration of the t-integrand is the minimiser U_k at its data, U_k(exp iB′V^{(k)}) = exp(iη𝐇_k(B′))U_{k+1} (RG I (3.3), p.270 l.24–28). So it has the multiplier representation of *The Current at the Multiscale Chain.* This is added to *The Room at Real Backgrounds.* and to the real segment of the line.
- *CB-8.* P(k), C_c′, and C_r now carry their ḡ-, b′-, and (K − k)-dependence.
- *CB-12 (INCORRECT, minor).* Replaced by the reviewer's corrected statement: n₀ is the larger threshold, and C_h ≥ max(2C_r, 2θ̃^{−n₀/8}).
- *l.680 and l.665.* The references to the repair-attempts note are removed.
- *CB-5a.* Added a sub-item, *The quantities.* U_{p,X} and 𝐉_{p,X} are built from Ω_1, …, Ω_p of the current sequence (p.261 l.5–10). Both classes use that sequence, and the fluctuation step keeps it.
- *CB-5b.* Added a sub-item, *The class.* b_{k+1} and the room are on Ũ^c_{k+1}, not on (3.43). The 𝐁_k-expression's terms go to 𝐁^{(k+1)} (p.276 l.33–35), whose class in (2.41)–(2.42) is the unenlarged one. Boundary terms are not renormalised (p.276 l.40–41), so no derivative estimate uses the enlargement. The Cauchy note's §8.5 is applied on Ũ^c_{k+1} for these insertions. The Cauchy note's §8.5 *Statement.* now says this for boundary-term insertions.
- Hash at 20:29: LF note 802 lines, 0936d5f6d287.

## Triage of var-20261028-r8, 20:29–20:31

The review covers the fluctuation fields A, the field 𝐀₀, r^s_z, and the inputs of (iv)/(α). It found nothing fatal and two serious points. All of them are repaired.

- *1g (serious): an open premise inside a part labelled derived.* The run difference of 𝐁″_k, and of the preliminary integrations that consume the A_j on Z, had been attributed to b_i and the Cauchy note's §6.2/§10. They are now named as the open creation difference of Open Gaps (10).
- *1c.* The A of V(Y) is now stated to be the remaining system. The A_j with h ≤ j ≤ k − 1 on Z are integrated by LFR I's preliminary integrations, (1.25), (1.60)–(1.62), and (1.71). The remaining system is shared because N₀, h, Z″_j, and Ω″_j agree under R_j = R̄(K − j).
- *1e.* Two points are added. The matched variable is the scaled A_j (CRE p.267 l.42): the g_j sit in the integrands as coupling ingredients, and the Jacobian cancels in the ratio. A is read in the intersection of the two runs' supports of |A_j| < g_j^{−1}δ_j, with the rest a χ-difference.
- *2b.* The occurrence list of 𝐀₀ is corrected. p.368 and (1.46) concern U″_{h+2}, outside V(Y). (1.50), (1.52), and the 𝐇″_k/u^0_k route are added.
- *3b and 3d.* r^s_z now names ι_X at the complex W as its presupposition, which is the open lift condition. (δ) now includes the current difference in its bracket.
- *3e.* The closing sentence of the telescoping now says the pieces are exact, except at U_{1,2} near the cut and for the entries of U_1 and U_2, which are undefined. The bounds are open as listed.
- *4a and 4b (serious): the inputs of (iv)/(α).* Open Gaps (3) now lists all of them. The complex-point extension for the current is added. The tail of ι_Y is added to the result bullet, removing the l.549/l.554 inconsistency. The (1.64)–(1.69) sub-item now includes U(𝐁″_k(Y_1), D(s)).
- Hash at 20:31: LF note 804 lines, ce4212d86478.

## Triage of lf-fineside-20261028-r1, 20:31–20:35

The review covers *The Fine Side at the Multiscale Chain.*, the lift condition of (i), and *The Lift ι_Y.* It found nothing fatal and two serious points. All of them are repaired.

- *1(i) (serious): the lift condition.* The tail had picked up a spurious factor L^{j−m}. The text now uses the reviewer's repair (a). A generation-j term reads every layer m ≥ j at the scale-j thresholds, since Ũ^c_j conditions Ω_j as one layer (CRE (2.34)–(2.39) at n = j). So its radius in the units a_j is r_{0,j}, independent of m. The move is L^{j−m}σ_c + C_tε₁e^{−½δ₀M₁L^j}. The tail part is ≤ C_te^{−½δ₀M₁L^j}ε₁/α_j, which is small for γ small. The polynomial factors in k − j are absorbed, since k < 8j + j(C) for non-deep terms.
- *2(c) (serious): the moment defect of ι_Y.* The bound rested on §5, which the reviewer could not read. The note now spells out §5's three inputs: the linearisation bound, the Hessian at the term's own scale (RG I (4.5)), and the affine test. The collar enters only through the distance in C″_Π = C_ιe^{δ₀(R/L+2)M₁}, so L^k for L^j is valid. The E₀ and ε₁² bookkeeping is made explicit through §5's per-point bound.
- *1(g).* The stated result is now σ_c ≤ C(ε₀)d̄. The callers' weaker form is valid at the non-deep layers, where they absorb (a_k/ε)^{ε₀} explicitly. The γ-smallness after R, M, and M₁ that C′ needs is stated. Open Gaps (3) is updated.
- *1(h).* (F-W) is now stated as an additional bound, RM, LM₁ ≥ 14 log L/(3δ_f).
- *1(a).* The joint line now uses the uniqueness of ι's one-step problem, by containment of the constraint sets. The σ̂_{k,j} wording is fixed.
- *1(b).* "Where the profile applies" is now "at every point of the member's determining set (PRT2 (2.1)–(2.2))". (A-iii) is carried with the coupling terms of (α): both members are taken at run B's coupling in exp ig_kB.
- *1(f).* Three fixes: the BCH step is now a continuity argument; b_t is removed, since W_t is critical; and the gauge along the path is named.
- *δ₀ overload.* The moment-defect bullet now says that δ₀ there is §9.8's rate. The CRE p.256 and LFR II p.376 citations are left as they are (minor).
- Hash at 20:35: LF note 806 lines, ee0a9aea1fce.

## Triage of lf-current-20261028-r1, 20:35–20:38

The review covers *The Current at the Multiscale Chain.*, the repaired *The multipliers.*, and the current part. It found nothing fatal and two serious points. All of them are repaired.

- *Serious 1: the current part.* It bounded V^B(Y) at the lifted entries with moved currents, which is not Bałaban's (1.68). The current is an independent coordinate of the terms' spaces (CRE p.261 l.5–10). So the term-by-term bound of *The bound of f on the disc* applies at c(1) with the currents J(c^B) + uΔJ_c, with f's inputs. Both the real and the complex current part now cite that bound.
- *Serious 2: the global d̄ downstream in (d).* The pointwise λ and δ𝐉 of the chain item now replace the global displays where finer layers occur. A new sub-item, *The pointwise disc.*, aligns the localised walk terms of PBG Theorem 3.10 ((3.107)–(3.108), pp.415–416; [13] = PBG checked in CRE's reference list). Each walk term depends on U only on X_ω and decays as e^{−½δ₀d(ω)}. Each is aligned on its own disc R̄(x)L^{−(1−ε₀)m/3}, and the layer crossings pay L^{1/3}. So the change is ≤ 2c_wL^{1/3}/R̄(x) pointwise.
- *Minor.* Five fixes:
  - The interface locality r_Q = d(L − 1) + 2 is added. (LW₀) still holds by the layer index.
  - c_E carries e^{½δ₀r_Q}. At S_j, c_δQ carries the factor L, and q_Q is taken at Ad ≤ e^{c₃/2}.
  - The bond-count factor 2d is added to c_tot.
  - (T-E), (I)'s conditions, and κ_W are added to the definition of (T-Λ).
  - "¾ of their thresholds" is replaced by ½ϖθ + ¼θ ≤ ϖθ, with T_J strict. The transfer of C_ℒ′ to R₀e_y now names its inputs (PBG (3.133), Theorem 3.12).
- Hash at 20:38: LF note 807 lines, 0f75ba998d92.

## Triage of lf-cxpoint-20261028-r1, 20:41–20:44

The review checks the opening, the members, the complex class, the lifted backgrounds with (T-ι), the tail, *The Room.*, *The Ratio.*, the Lemma (Two Constants), and the current at complex points as correct. It finds five serious and five minor points. All five serious points are accepted. None of them is repaired by a derivation in this pass. Each is now stated as open in the block, in Open Gaps (3), and in the Status line.

- *S1: the bound on the ball.* Accepted, open. *The flow.* now says that the decomposition is derived only at the critical W_t, that the Picard iterates pass through non-critical W(𝐒, z), and that (190) loses a factor a_j/ε. The bound of Φ(W)A_c from the structure H₀ + G̃ of VAR (182)–(183), on PBG's class, is listed as open.
- *S2: agreement with the real lift.* Accepted, open. "By uniqueness" is removed. The identity Φ(W_t)A_c = δ_t in the gauge of the real construction (Landau (21) against the axial minimal configuration) is listed as open. So is the alternative, a direct real layered bound for the flow.
- *S3: the representative.* Accepted, open. The lift condition now has the sub-item *The representative.*, which states c^B(i) = U^0_k(𝐔)^u with |log u| and a_j|∇ log u| of order ε₁′, together with the transport by u^{−1}, as open. The same holds for J.
- *S4: small n.* Accepted, open. The sub-item *Small n.* states that the real fallback needs the lift condition. Open Gaps (3) and the Status now carry n ≥ n₀′.
- *S5: overstated status.* Accepted. Open Gaps (3) now says that the bound of 𝐒_c and the current come from the Lemma, and that the lift condition comes from *The Room.* and r(Y), at U^0_k and U_k, for ι_Y, and for n ≥ n₀′. ι_X and the other members are listed as open at complex points. The block's label is now *Partly Open, Unreviewed*.
- *Minor.* Four points are fixed and one is not:
  - m1: "VAR Prop. 6" is replaced at both places by PBG (3.133) and Cauchy's estimate on the multipliers.
  - m2: the reference now reads (179)–(180).
  - m3: (T-ι), VAR's regularity threshold of p.309 l.1–4, and Proposition 9's thresholds are now all taken with (T-c).
  - m5: the real points of the disc are now s, and x denotes lattice points only.
  - m4 is not applied. 𝔐 = 1 is valid. 𝔐 = 𝔐_S would only remove ε₁′^{−1/16}.
- Hash at 20:44: LF note 815 lines, d216167b974f.

## Triage of lf-fbound-20261028-r1, 20:44–20:46

The review finds nothing fatal, four serious points, and seven minor ones. All are accepted. The serious points are recorded as open, and the minor ones are fixed.

- *Serious 1 (1c): the renormalisation at the entries.* Accepted, open. The claim that RG I's set-up covers "a minimiser times an arbitrary regular field" is withdrawn. In RG I, 𝐀 sits in the data of a local minimisation, and the terms are evaluated at its minimiser. The new sub-item *The renormalised terms at the entries (open).* states the non-minimiser defect and the counterterm defect for the terms that read an entry as such, the completions at U_k among them. It also records why the alternative reading through M^·(·) does not avoid a mismatch. Open Gaps (3) is rewritten to match.
- *Serious 2 (2e/2f): the sums.* Accepted, open. The sum of the excess over the positions is now stated as open. It is open because of the factor exp(−⅓κd_j(X)) of (4.22) and the age decay of CRE (2.45). The result is labelled "given the open inputs above".
- *Serious 3 (3d): (1.61) and the determining-set configurations.* Accepted, open. The derived claim is reduced to the plaquettes and currents of LFR I p.190 l.18–22. The remaining analyticity conditions, and the mixed-data configuration U(𝐁″_k(Y_1), ·) of (1.61), are listed as open.
- *Serious 4 (3e): U_{k,Λ}, (1.62), and (1.63).* Accepted. These are now a separate open condition, not part of (β), and their reading as data of a representation configuration is stated.
- *Minor.* Seven fixes:
  - 1d: c_ρ is taken with c_ρα_m < min(α₂, α₃) (new sub-item *The class at the entries.*).
  - 1e: the localisation of the 𝐇-arguments at the entries is stated as open.
  - 2b/2d: the counterterm excess of CRE (3.66) is now counted.
  - 2c: Q′ carries |𝐀||∇A₀|, and the layer scale is now cited as CRE p.280 l.20–23.
  - 2g: θ̃′ is removed. The factor k < 8n + j(C) is absorbed by the slack of the ratio.
  - 3c: the U″_k citation is now the support of χ_k^{(N)} with LFR I p.190 l.9–11, in place of p.195.
  - The pinpoints are corrected: (1.68) is at p.377 l.10–13, and the sums are at p.376 l.39–46.
- Hash at 20:46: LF note 816 lines, c42c87a089a3.

## Triage of lf-redthr-20261028-r1, 20:46–20:48

The review finds nothing fatal, one serious point, and six minor ones. It checks the reduced thresholds as correct in substance. (J-W) is closed for M₁ ≥ M_J(d, L).

- *Serious (2c′/2d/Q5(i)): the width of the middle layers of 𝐁″_k.* Accepted, open. CRE p.256 l.21–23 excludes the R-operation domains. *The join.* now cites it only for j ≤ h, where Ω″_j = Ω_j (LFR I (1.12)). The top N₀ layers are M wide. The middle layers h + 1 ≤ j ≤ k − N₀ are stated as open in *The join.*, in *The layers of 𝐁₁.*, in *At the joins W = LM₁.*, and in the residual's parenthesis of §9. Bałaban applies VAR's Sects. D–E to these sets at LFR II p.370 l.39 without stating their widths (checked in p370_corrected.tex). The new item Open Gaps (11) names what closes it.
- *Minor 1 (1c′).* Accepted and checked. RG I p.277 l.54 (B₃²O(1)Mα₀ < ½α₁) and (4.17) at p.285 l.17 force q₁ ≥ q₀. Both places now say q₁ ≥ q₀ > p₀.
- *Minors 2–6.* Not yet repaired. They are, in order: PBG Theorem 3.1 at R < L, which needs the remark that the proofs use R only through RM, together with δ₀^{PBG} ≤ δ₀^{(2.43)}; the 𝐉-dependence through the explicit formulas; the Q2 classification (α₄ and α₆ of RG II, and the homogeneity of α₂(α₀)); λ_Q as the largest of the five μ; and the open premises in parts labelled derived.
- Hash at 20:48: LF note 817 lines, 85af56c23e6f.

## Repair of lf-redthr-20261028-r1 Minors 2–6, 29 Oct 00:38–00:45

User: "Tackle lf-redthr's minors 2–6". Each source was read on its page before the edit.

- *Minor 2.* PBG p.399 proves Theorems 3.1–3.3 by reduction to PRT2, with constants independent of {Ω_j} under (2.1)–(2.2). In PRT2, (2.2) enters only through the crossing length > RM of (2.57) (p.233), then Lemma 2.1 (p.234) and the factors e^{−cδ₀RM·max(|j−j′|−1,0)} (pp.235, 237). The RM choices of Ω₀ (PRT2 p.228, PBG pp.394, 396) are "e.g." examples. New sub-bullet *Theorem 3.1 at the joins.* Rate δ_* := min(δ₀^{PBG}, δ₀^{(2.43)}) in *The rate.*, (J-W), and M_J. (J-W) is extended to every crossed layer narrower than RM: the joins and the top N₀ layers of 𝐁″_k (Q5(i)). The LFR II p.370 reading is corrected: Bałaban takes U_{𝐁₁} and U_{𝐁₂} after (1.52) and expands U^0_k around U_{1,2} by VAR Sects. D–E at (1.54). The middle-layer width stays open (Open Gaps (11)).
- *Minor 3.* "Uniqueness of analytic continuation" is replaced by the explicit substitution formulas: RG I (3.13) p.272, (3.15) p.273, and LFR II pp.358, 366, 367. Also noted: real configurations fix an extension only on 𝐉 = J(𝐔).
- *Minor 4.* New *Mixed statements.* sub-bullet. On LFR I pp.198–200 with ε → α₀, the step statement of p.191 and (1.65) split three ways: e^{−R}ε < αε is homogeneous, B₃δ′_k < αε is lower, and the α²ε terms are upper.
  - RG II's α₄^{−1}α₆^{−1} is removed: these are RG II's own constants (pp.16, 18).
  - α₂ := c₂min(α₀, α₁) is homogeneous.
  - Added uses:
    - RG I p.263, (3.17) p.273, and (4.5)/(4.21) pp.282, 286;
    - RG II pp.6, 8, 10, 15, 16, 17;
    - CRE (3.43) p.276;
    - LFR I p.192.
  - "Apart from the order relation below" is added to the q-bound sentence.
- *Minor 5.* λ_Q := max{1, 4B₃, 8B₃, 16B₃², 8B₃C_{Q*}}, so the B₃ ≥ ½ assumption is dropped. Changed in the LF note (room at real points, reduced thresholds, order of constants) and the Cauchy note (§5 l.122, glossary l.952).
- *Minor 6.* *The room at real points.* is now labelled "derived except the current". It names its three premises: §3(d)'s item on (1.64)–(1.69), *The multipliers.*, and the reduced thresholds. The current is moved by *The Current at the Multiscale Chain.* The lower-bounds item names §3(d) as well.
- Hashes at 00:45: LF note 824 lines, e28a93e03438; Cauchy note 956 lines, 3b1febe345a1. The round-53 packets for both notes were rebuilt with these hashes. lf-redthr-20261029-r2 now asks whether each repair closes its minor.

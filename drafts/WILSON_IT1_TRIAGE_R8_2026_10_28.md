# Triage R8: Second Referee Round of 28 October 2026

Reviews of the Cauchy note (`WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md`, SHA256 920f06b19bf4… at review) and the LF note (`WILSON_IT1_LARGE_FIELD_DEPTH_2026_10_27.md`, SHA256 e64619bd303a… at review, 565 lines), launched by `run_app_review_cli.ps1` on claude-opus-5-5. All three reviews of the round have landed, and every report was read in full. All dispositions below are applied. After the repairs the Cauchy note has SHA256 8f7a3e6cc5c7… (905 lines) and the LF note 3b38676698e0… (582 lines).

## cauchy-lift-20261028-r3 (Cauchy §5, the Lift, the Pair Line, and the Moment)

Verdict: one fatal point (step 25), two serious points, and minor ones. The reviewer reports the hash 920f06b19bf4… (match).

- Step 25 (fatal), the current along the pair line: accepted. A bound at the lift's current alone leaves the current part at 16C(ε₁/r_{0,k})L^{2(j−k)}E₀, and (5.1v) is then not summable. Repair: the frozen-current split of *The pair line.*, with F(s, u) := 𝐄^B(W(s), J(U^B) + uΔJ; z), a configuration part ≤ C_σ(σ̂_{k,j}/r_{0,k})E₀ (C_σ = 64), and a current part ≤ 16(sup|ΔJ|/r_{0,j})E₀. The new input (J-δ), sup|ΔJ| ≤ C_Jσ̂_{k,j}L^{j−k}, is derived at the ages k − j ≥ k/2 by the lattice inequality and open at k − j < k/2. It implies the lift's current. A new Open line in the header names it. Applied.
- Step 18, the coefficient of the localised lift: accepted. Both pieces are renormalised with Π^G, with |Π^G_{22,11} − β^B_{j+1}| ≤ C_ΠE₀e^{−δ₀M₁L^j}, and the defect enters only the second bound of (5.1v). Applied in §3 and §5.
- Step 13, the closure of the lift's current: replaced by (J-δ). Applied.
- Steps 21 and 35, status labels: accepted. Applied.
- R1, the localisation tail: accepted. σ̂_{k,j} := σ_k + C(ε₀)(ρ_k + ε₁e^{−δ₀M₁L^j}), since ι_X has no exterior constraint. Applied in §5, §9.8, §10.5, and the notation.
- R2, the covariance of ι_X: accepted. ι_X is CRE's minimal configuration of the determining set 𝐁_1(X^∼) (CRE p.256 l.36–p.257 l.6), which is covariant; the former "fixed exterior field" wording is withdrawn. Applied in §9.8. This also answers the question of 28 October on gauge invariance: every term is gauge invariant, and the moment defect concerns only the quadratic coefficient.
- Minors: Jensen replaced by the Euler–Lagrange argument; d̂ℓ_0; the domain of 𝐄^B (2B₃·½r_{0,j} < α^B_{0,j+1}); the BCH term; E₁(α); q₀ > p₀ as a choice (CRE p.259 l.50); k_V removed; M′ a multiple of R₁M₁ (VAR p.279 l.3). Applied.
- Also applied in this round, from the reading of RG I Lemma 4: its proof does not use (I.1.12) or CRE (2.38). (N) becomes □₀ ⊂ Ω_n, the layers n + p close by (1+β₀)²p^{1/2}L^{−p}/(1 − β_C) ≤ 1, and (R-Δ^c-T) keeps only the near domains that meet a finer layer.

## lf-shell-beta-20261028-r1 (LF §3(d), the Soft χ̄ Shell, and the Choice β = 1/8)

Verdict: no fatal point; one serious point and thirteen minor ones. The reviewer reports the hash e64619bd303a… (match).

- S1, the cutoff χ(Λ) of LFR I (1.101): accepted. It was soft at l.148, l.152, and l.307 and listed as sharp at l.95 and l.63. Repair: §3(d) lists χ(Λ) as soft, the same function in LFR II (1.1), (1.2), and (1.70) (p.356 l.19–37, p.378 l.13–14); χ′ of (1.70) stays sharp as LFR I's (1.82); §2(b) says the denominator's shell is the Lipschitz shell and the numerators' χ′ the density bound, as in the Cauchy note's §8.6. Applied in both notes.
- m1, the coupling part of the χ̄(Λ) shell: accepted. Per bond δ^χ_c ≤ 4Cg_k²|δ_k|/κ_s. The shell now runs through the split of §2(b), (Π_A − Π_B)₊ ≤ 1{Π_A > 0}|Π_A − Π_B|, so both parts share run A's own sharp tests at (1 + κ_s)t, and the condition s_n ≤ κ_st is no longer needed. Applied.
- m2, the denominator sandwich: accepted. It holds at real backgrounds only. Repair: d̄ = E_s[d(s)] over bond thresholds, |d(s)/d(1) − 1| ≤ τ := |Λ^{(k)}|e^{C(M)}e^{−κ_Λt²/8} at complex backgrounds by (1.7)–(1.9) on the class, (1.6), p.357 l.9–10, (1.10)–(1.11), and |Λ| ≤ O(M⁴) (p.358 l.26), so |log d̄ − log d(1)| ≤ 2τ. Applied.
- m3, the constant: accepted. C_Δ(M) for C_X(M). C_{ε₁} = C(M)R_k is absorbed by R_k ≤ L(log g_k^{−2})^r, K − k < 8n + j(C), and the slack L^{−(1−ε₀)n/12}. Applied.
- m4, θ̃: accepted. θ̃ ≥ L^{−(1−ε₀)/4} of §4(c) is cited. Applied.
- m5, notation: accepted. δ^f_n renamed δ^χ_n. Applied.
- m6, p.193 l.7: accepted. Attached to χ_{k,Λ_i}; (1.102), which Bałaban states without proof (p.201 l.40–44), holds with χ̄ by the Haar translation V_k⌈_Λ ↦ V′_k, since V_Λ depends only on V_k⌈_{Z∩Λ^c} (Proposition 1, p.194 l.38–41). Applied.
- m7, "½ of the threshold" at p.378 l.10: accepted. Labelled as this note's inference from the threshold 2ε_kη² of LFR I (1.75). Applied.
- m8: accepted. "8α ≤ 1" (p.187 l.13), with the factors αβ of p.186 l.42. Applied.
- m9, the count: accepted. A recount of the bare β gives 119 on 28 pages (29 on 10 pages of CRE, 59 on 11 of LFR I, and 31 on 7 of LFR II), and every page lies in a cited page or range. Applied.
- m10: accepted. LFR I p.182 l.17 (0 < β ≤ ½) added; p.186 l.42 added. Applied.
- m11, RG I: accepted. A bullet for RG I's class parameter β_I (≤ 1/4, as in the Cauchy note): (1 + 7β_I)L^{−2} ≤ 1 (p.279 l.28) and (1 + 8β_I)L^{−2} ≤ 1 (p.280 l.18) hold at L ≥ 2; its other restrictions are choices of α₀ and α₁ made after β_I. The one undefined β_I of §4(d) is now defined, and the condition on α₃ written with β_I. Applied.
- m12, δ^s of §3(b): accepted. δ^s := 2δ^f + 4Cg_a²|δ_k|, which is δ^s_k of §3(d). Applied.
- m13, the packet's "Section 3(b)": to read §3(d) in later packets.

## var-20261028-r3 (LF §4(d), the Functions of the Configurations, (i)–(iii) and the Room)

Verdict: no fatal point; four serious points and seven minor ones. The reviewer reports the hashes e64619bd303a… and 920f06b19bf4… (match).

- S1, the decomposition: accepted. Repair: the re-summation is written per term, V^B(Y)[(c_X)_X], with the composites of (1.59) computed by run B's local minimisation at the data of c_X and the links taken as run B's maps at c_X; the joint line has one parameter for all terms; (iii) is taken at fixed configurations, run B's propagators at ι_Xc^A against run A's at c^A, so it no longer overlaps with (ii); a new item (iv), the variation group at the composites, is bounded as the Cauchy note's §5 variation group with the status there, with the lift condition at the composites; (i) lists its evaluation points, U^0_k with its expansion points (p.374 l.31–34), the two composites (p.372 l.5–11), and U_k for the completions (p.377 l.22–26). Applied.
- S2, the lift condition at the multiscale chain: accepted. (i) is derived at the single-scale real minimisers except the current; at the multiscale members of 𝒞 and the composites it rests on the multiscale fine side, which is open. σ̂_{k,j} at U_k likewise. Applied.
- S3, the room at real points: accepted. Relabelled "derived at U^0_k given the reading *Bałaban's Statements at the Reduced Thresholds*, except the current". (1.65) concerns U^0_k (p.375 l.17–21); the conditions at the other members of 𝒞, whose regularity Bałaban calls "almost the same" (p.375 l.1–13), are a new open input of (ii). *The Room.* at complex points is corrected the same way. Applied.
- S4, the closure of the bound of f: accepted. The closure now names the statement: a multi-variable form of (1.68)–(1.69) in the per-term configurations, with the links and the composites as above. Bałaban's analyticity is in one background, so this is a new statement; its renormalisation step is evaluated at configurations that are not local minimisers. Applied.
- m5, the weighted blocking artifact: accepted. With G renormalised by Π^G, G − 𝐓^A = irr(Δ_j), and run B's term at the lift differs by r_z := (Π^G − β^B_{j+1})A_ε(h_z, c^A) + β^B_{j+1}b_{h_z}(ι_Xc^A). This is the moment defect and the action part of the Cauchy note's variation group at the pair (c^A, ι_Xc^A), bounded as there. Applied.
- m6, the first "doesn't work" line: accepted. Restated as "V^B∘ι_Y … alone does not give (i) + (iii); it leaves an equal-data variation of the type of (ii)". Applied.
- m7, the layer of x in (1.66): accepted. The identification is stated: on (Ω_l ∖ Ω_{l+1}) ∩ X, l = k₀ + 1, …, j, (1.66) carries the scale-j factors with L_0^{2(j−l)} (p.190 l.38–48), and (1.24) has the thresholds ε_j there (pp.181–182), so the data there is at the scale j. Applied.
- m8, CRE p.262 l.45–46: accepted. The clause "and we will introduce some new restrictions also" is quoted; the restrictions read are sorted into three kinds, and the new restrictions of CRE, LFR I, and LFR II are listed as unchecked under the reading in Open Gaps (3). Applied.
- m9, the §1 alternative for ε₁: accepted. The factor C(1 + β₀)(k_s − k + 1)^{1/2}(1 + A₁/A₀) is polynomial in n and absorbed. Applied.
- m10, notation: accepted. C_tr replaced by the constants C_r and C_ℒ′ of *The multipliers.*; the room renamed ϱ(x) and ϱ^F(x), apart from the residual ρ(x) of §4(b); "ρ(x) ≤ 1" dropped; λ ≥ μ stated with B₃ ≥ ½; (1.69) called a cube-gauge regularity condition; σ_{c,X} uses the covariant gradient at c^B. Applied.
- m11, the (5.1v) clause: outside the packet's ranges; no change.
- Q3, further points: the localised lift and c = U_k are added to the first open input of (ii); the coarse side is labelled derived where the profile of §4(b) applies, which needs the joins 𝐁₁ and 𝐁₂ to satisfy PRT2 (2.1)–(2.2), not checked. The current of the line now points to the frozen-current split and (J-δ) of the Cauchy note. Applied.

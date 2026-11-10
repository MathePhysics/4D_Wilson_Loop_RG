# Packet 12a r1 Triage (LF #1.2, #3.16–#3.62-1)

## Pre-check

Before the first round, I read every line of #1.2 and #3.16–#3.62-1 and checked each cited page of CRE against the corrected transcriptions (Balaban\tex\CRE\parts\pNNN_corrected.tex): p.246 l.14–15; p.247 l.34–48 ((1.8)); p.248 l.10–12 and l.36–38; p.250 l.39–49 ((1.19)); p.251 l.37–48 ((1.22)); p.252 l.2–5; p.254 l.47; p.258 l.14–31 ((2.20)–(2.21)); p.259 l.47–50 ((2.28)); p.264 l.50–51; p.265 ((3.3)); p.266 l.12–42 ((3.7)–(3.9)); p.267 l.5–28 ((3.12)–(3.14)); p.268 l.18–54 ((3.16)–(3.19)); p.269 l.45–50; p.270 l.8–24 ((3.23)–(3.25)); p.276 l.30 ((3.43)); p.284 l.2–8 ((3.68)). The arithmetic was re-derived: (1 + κ_s)(2(1 + β₀)L^{−2} + 4/10) ≤ 0.657 at L = 3 and β₀ = 1/7 (#3.56); (1 + β/15)(1 − 7β/90) = 0.9985 at β = 1/8 (#3.24-1); (1 + κ_c)^{N+1} ≤ e^{κ_s} (#3.19-1); and (1 + κ_s)(11d² + dM(n − j + 2)) ≤ 3dM(1 + (n − j)log L) for M ≥ 12d (#3.62-1).

Repairs before r1, each by rewording the existing sentence:

- **#1.2.** "The part of X that is large-field from the scale j₀ on" is now the part in Ω^c_{j₀}, which lies in every Ω^c_{j+1} with j ≥ j₀ − 1 by Ω₁ ⊃ Ω₂ ⊃ … ⊃ Ω_k (CRE p.254 l.47).
- **#3.62-1.** "α_{0,k} exceeds ε_k by a power of log g_k^{−2}" now gives the reason: α_{0,n} = g_nC₀(log g_n^{−2})^{q₀} (CRE (2.28)), and q₀ > p₀ + 3r (#4.480). CRE (2.28) itself requires only q₀ > 1.
- **#3.62-1.** (3.68)'s range is p.284 l.3–8, which includes its tag line.

The lines #3.19, #3.24, #3.27, #3.30, and #3.62 exceeded ~600 characters. Each was split at a sentence boundary into the sub-items #3.19-1, #3.24-1, #3.27-1, #3.30-1–#3.30-2, and #3.62-1, with no change of wording.

The definition check found κ_s, δ^s_j, and δ^f_j defined both in the part and in the status line #0.20.1, and δ^f_j also at #2.17. #0.20.1 now cites them (κ_s of #3.24, δ^s_j of #3.32, δ^f_j of #2.17), and #3.26 cites #2.17's δ^f_j instead of defining it again. N (#3.19, the number of cascade integrations) and N (#4.582, a count of crossed layers) are unrelated local uses of one letter, recorded in the spec's allow_defs.

## The Run

The first launch, lf-p12a-20261106-r1, ended at 14:47 on the .claude-IF session limit with only a draft disclosure, so it is no round. Outside the part, LF §5 (#5.39-3–#5.39-3-3), 12b's lines, and #4.43–#4.45 were then repaired, and r1 was rebuilt as lf-p12a-20261106-r1b with the same argument (14,884 characters). Its launch under .claude-IF at 15:40 stopped at once on the same limit; at the user's direction r1b runs under .claude-Main from 15:41 (session 0fc6f2f6).

## The Report of r1b

r1b (16:01) found no fatal finding, one serious finding, and seventeen minor ones. Each was re-derived against the print and repaired.

- **S1 (#3.26).** §2(c)'s two-run bound covers only local minimisers; the cascade tests (1.22)–(1.24) and (1.75) test multiscale minimisers. Repaired by the derivations #3.26-1–#3.26-5. By LFR I (1.16), the layer of 𝐁^{(n)}_k(Z) at each tested plaquette is the scale of T_n(p), so (P′) (#5.19) bounds the plaquette difference by 3ρ̄_i in the layer's normalisation, against a threshold ≥ (1 − β)ε_i, giving 4ρ̄_i/ε_i ≤ (4/c_v)C_{1.27}(ε/a_i)^{1−2ε₀} since ε_i ≥ δ′_i. For (1.75), the tested plaquettes lie at depth ≥ 2MR_k in Z, where 𝐁_k(Z) has k-blocks, and a near-minimiser of the smaller run gives |f^A − f^B| ≤ δ^f_kt.
- **m12, m8, m11 (#3.30, #3.38, #3.39).** Test scales are j ≥ n − 1; k + 1 ≤ 8(1 + j(C))(j + 1). After the removals of (R-s)(a), at most two cascade tests per cube remain (χ̄^{(n)} = 1 on the support of χ̄^{(n+1)}); the contributions to C_h are now 2Cn_T/κ_s, n_T := 14, and 32C(1 + j(C))c_{hs}/κ_s with c_{hs} := sup_{j≥0}(j + 1)L^{−(3−7ε₀)j/4}.
- **m5 (#3.24-1).** The cascade removals use Bałaban's coefficient bound ≤ αβ (p.186 l.36–43), into which the soft (1.27)'s 1 + κ_s enters, and no other margin.
- **m14 (#3.47).** 1 + 2κ_s; convergence rests on (b).
- **m4 (#3.20).** CRE (3.20) does not give the disjointness; the soft product now keeps χ̄² on any overlap, and no χ̄² = χ̄ is used.
- **m9 (#3.30-2).** C_{1.27}'s dependence on ḡ, L, ε₀, M, A₀/A₁ is stated; max(1, k_s − k + 1)^{1/2}.
- **m7 (#3.29).** CRE's p₀(g) contains A₀; LFR I's p₁(g) does not; "of (c)" is §4(c), #4.43-1.
- **m16 (#3.61).** The half {g < 1}: there the argument is < (5/3)ϑ_k + o(ϑ_k) < 2ϑ_k (CRE p.252 l.2–5).
- **m17 (#3.62).** χ(Ω_{k+1} ∩ Λ^c_{k+1}, S_{k+1}) is CRE (3.21)'s product, with the soft χ′_k(S_{k+1}).
- **m2 (#3.18).** p.380 l.31–42.
- **m3 (#3.19.1).** The cubes are the LM₂R_i-cubes of the threshold's scale; for j ≤ k₀ the thresholds are p.181 l.40–42's generalisations.
- **m1 (#1.2–#1.2-1).** The blocks that meet Ω_{j₀}, the factors ζ and χ of (2.21), and the 𝐑-operation clause (p.258 l.22–23, l.34–36).
- **m6, m10, m13, m15.** #3.26's C is taken for data regular at the support thresholds; #3.32 states the bound on either run's support; #3.40 uses the threshold's scale; the unused m_B is deleted.

Outside the part, at the same time: 12b's pre-check repairs (#3.86's α₀ is REG (1.65)'s parameter; #3.94-1–#3.95 write out the second τ and give the factor e^{1/2}); the fork's PC25 (m_Ψ := 2(e^{2C_Ψ″} − 1) in #5.39-3-1 and ε^R_A, re-derived: Σ|e^{−d_c} − 1| ≤ e^{Σ|d_c|} − 1); packet 13's #4.559 pins (CRE p.261 l.5–6 and l.5–40).

From r2 on, the referee reads frozen copies of LF, the table, and the labels in the review folder (build_packet.py and brief_template.md, at the user's direction), so LF outside the part can change during a round.

## Files

r1b: LF 462dc146eba3, labels 33d27e62cbdc, table 88a6dcbd277a. r2 (launched 16:15 under .claude-Main): LF 98afdbda7e48, labels 5b9158c1de9a, table 88a6dcbd277a.

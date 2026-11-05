# Packet 10, Round r2: Triage

Review: verification\isolated_reviewer\reviews\lf-p10-20261105-r2\review.md (Cauchy note aa200ada31ee, a confirming round on the r1 repairs). Verdict: no fatal or serious finding, every r1 finding resolved, and eleven minor findings (§3 items 1–11). All eleven are accepted and repaired within existing lines. The repaired Cauchy note is a573eeed7edb (970 lines), and the table is 6ce52c2a8851 ({#T4.33} wording, its new C_{U′}, and the source SHAs of {#T4.4} and {#T4.33}; no existing constant changed).

| Finding | Verdict | Repair |
|---|---|---|
| 1, the cube-gauge regularity of U₀′ | accepted | §9.7 l.516: §9.8's REG argument at the one-step scale gives U₀′ (3.35)–(3.36), as PBG Theorem 3.13 needs for 𝔊_B (and VAR p.280 l.52). |
| 2, the current part of U₀′ in VAR (14) | accepted | l.516: plaquettes within (C₀ε₁ + 16C_ℒρ)(ε/a)² and current within (C₀ε₁ + C_{U′}ρ)(ε/a)² in one-step units, C_{U′} := (32(d − 1)L + 4C)C_ℒ, by sup-norm D*f ≤ 2(d − 1)(L/ε)sup f on T_{ε/L} and the transport part s; both ≤ 2C₀ε₁(ε/a)² once C_{U′}ρ ≤ C₀ε₁. |
| 3, §9.7's k-conditions and the source from H₁B | accepted | l.508: k₀(ε₀) includes 8ρ ≤ C₀ε₁, C_{U′}ρ ≤ C₀ε₁, 16C₂C_ℒ²ρ² < 6dLC₁C₀ε₁, and 3C₀L^{−2k} ≤ 1. l.516: −𝔊_B(δV/δA′)(H₁B) ≤ B₀C₄(B₀B)² by VAR (117), of order ρ⁴. |
| 4, the factor e^{5δ} | accepted | l.281: z's cutoff moves by ≤ ½ of the coupling difference (the factor Cp₀^{d_G}e^{−cp₀²}g_i² ≤ ½ for γ small); the ratio of (1.6) is written out, inside e^{±5δ} for coupling differences ≤ 1/20, which s′_K ≤ ½ gives. |
| 5, N_s and M_P | accepted | l.434: N_s > 24M_P with M_P dividing N_s and M_P a power of L (PBG p.408 l.26), a restriction on the torus side, which can still be taken arbitrarily large; l.526: strict inequality. |
| 6, Δ_π | accepted | l.504: Δ_π = Δ − Δ′_π (VAR p.284 l.37–38, p.299 l.2); (138) uses of HB only RD*(HB) = 0, so ⟨A₁*, Δ′_πA₁*⟩ = 0 for the Landau-gauge A₁*, and the form is that of the second variation Δ. |
| 7, the citation for ε_V | accepted | l.434: the restrictions on V_k, V_{k+1} on Ω̃_{k+1} from which CRE derives (3.12) (p.267 l.5). |
| 8, the hypothesis of §9.3 and the transport factor | accepted | l.458: (9.2) with C₀^{VAR}, as U^B satisfies; l.462: the factor 2 covers the holonomy corrections O(εF²), smaller than ∇F's bound by (ε/a)C₀^{VAR}ε₁ ≤ 1. |
| 9, the descriptions in (9.0) | accepted | l.440: a₁′ is VAR's §§A–E threshold at the given C₁ (p.281 l.2 and the ε₃ restrictions at (113)–(121), ε₃ of (114)); a₀ is PBG's, not VAR Theorem 1's. |
| 10, ρ^B at l.307 | accepted | ρ^{B′}. |
| 11, the perimeter at l.49 | accepted | P_{j−1}(C) is the perimeter in bonds of its scale, 4ℓ_CL^{k−j+1} for a square loop. |

New symbol: C_{U′}, recorded in {#T4.33}.

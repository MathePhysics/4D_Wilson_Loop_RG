# Packet 10, Round r1: Triage

Review: verification\isolated_reviewer\reviews\lf-p10-20261105-r1\review.md (Cauchy note a8808e2d5f5d, §1, §6.2, §9; table rows {#T4.4}, {#T4.33}). Verdict: no fatal finding, one serious finding (S1), and fifteen minor findings (m1–m15). All sixteen are accepted and repaired. The repaired Cauchy note is aa200ada31ee, the LF is 88aebf74c8c0, and the table is d90a35e9e1c9.

| Finding | Verdict | Repair |
|---|---|---|
| S1, run B's own-support shells measured against M^B | accepted | §6.2 l.297–l.305: the three-piece split is written out. Run B's piece Π_B(1 − Π_A)ρ_B is bounded against M^B_{τ⁺} and removed first, at a cost of 2B_Ws_Kδ_LF (Z^B − m_B ≥ Z^B_{ℓ₀}). The rest, ρ^{B′} against ρ^A, is measured against M^A_τ. b^{(M)}_K := 3e^{−C_P⌊k/2⌋} + 4s_K + s^{W,tot}_K, also changed at l.966 and in LF #5.3 and #5.63. (LF-1) at l.5 and l.297 names the majorant run by run. |
| m1, C₁ too small for VAR (2) | accepted | (9.2): C₀ := c₁₁C₀^{VAR}, c₁₁ := 3(1 + 4c_9). l.462 derives VAR (2) for MW at 2C₀ε₁, so C₁ = 2C₀/B₃ stands (§9.4 l.474). |
| m2, (9.0) incomplete | accepted | (9.0) adds 2C₀ε₁ ≤ min(c₂, c₃), 14dL²B₁^{REG}M_PC₀ε₁ ≤ a₀, and 280dL²M_PC₀ε₁ ≤ c₁^{REG}; l.440 explains each condition. |
| m3, the bound of J | accepted | §9.6: J is ε^{−2}D*∂Ũ up to higher order, and \|D*∂Ũ\| ≤ 2C₀ε₁ε²/a³ by §9.3. |
| m4, the sign in §9.1 and (9.9) | accepted | §9.1, (9.9), and §1's (3.2) (l.82–l.86) now use the identity (9.1) and absolute values. |
| m5, k₀ conditions | accepted | §9.6: ρ ≤ 1, 54C₂B₀ρ ≤ 1 (VAR p.286 l.20 at ε₃ := 3ρ), 6ρ ≤ c₄ (p.287 l.7), 4ρ ≤ a₃ (p.292 l.50); l.508: C_gap(ε₀)L^{−(1−2ε₀)k} ≤ C_b. |
| m6, Δ₁ is non-local | accepted | §9.6: ½⟨A₁*, Δ₁A₁*⟩ = ½⟨A₁*, Δ_πA₁*⟩ − ⟨HC^{(2)}(A₁*), J⟩ by VAR (79); the second term is bounded by the ⟨HD, J⟩ bound through VAR (44). |
| m7, the citation for ∇HD | accepted | VAR (57) p.286 l.42 and (58) p.287 l.4. |
| m8, the cutoff of z | accepted | §6.2 l.281 and l.289: z's cutoff moves by a relative amount ≤ \|δ_i\| (LF #2.10–#2.11), so (1.6) differs by e^{5\|δ_i\|} − 1 ≤ 10\|δ_i\|, still one ingredient inside 10sup\|δ_i\|. |
| m9, "k large" depends on j(C) | accepted | l.293: k ≥ k_*(j(C)), through C_a, C_h, and (K + 1)θ̃^{k_s/8}. |
| m10, \|F̃ − F\| | accepted | l.466: 6ε\|∇F\| (ℓ¹ distance 6ε); l.470: \|r₁\| ≤ 8c_9C₀εε₁a^{−3} ≤ C_r. |
| m11, §9.7's fine side and the data at scale j | accepted | l.516: the one-step problem at its own scale ε, with data parameter ε₁^{(1)} := 3C₀ε₁(ε/a)², the H₁B term, the current split D*f + s, and the bounds of 𝔊_B at scale ε, giving ‖A″‖ ≤ C(ε₀)ρ. The data at scale j are averages of a stopping-scale minimiser and satisfy VAR (7) at ε₁ by CMP 98 Proposition 2, since ε₁ := 2C₀ε_V (l.434). The forward use of §10.3 is noted as non-circular. |
| m12, cube-gauge regularity | accepted | l.526 rewritten on REG Proposition 6 (p.099 l.42–58) from REG's class (1.8)–(1.9) at α₀^R := 2C₀ε₁. It gives (3.35)–(3.36), bounds proportional to the cube size, at PBG's block size M_P for cubes up to 20M_P (LF #4.25), so no cube matching is needed. N_s ≥ 24M_P (l.434). C_L is now defined at l.540. |
| m13, two uses of C_G, and ε₀ | accepted | The covariance bound is renamed C_cov (l.290, l.293, l.327, l.347, l.966). VAR's ε₀ is distinguished at l.462. |
| m14, transverse extent of the weights | accepted | l.524. |
| m15, the size claim in §1 | accepted | l.49: the size claim is dropped. |

New symbols, all recorded in {#T4.33}: c₁₁, C₀^{VAR}, ε_V, C_{(3.12)}, C_{ε₁}, M_P, α₀^R, α₀^P, c₁^{REG}, B₁^{REG}, C_cov, and ε₁^{(1)} (local to l.516). The constants C_gap, C_b, and C_r are unchanged.

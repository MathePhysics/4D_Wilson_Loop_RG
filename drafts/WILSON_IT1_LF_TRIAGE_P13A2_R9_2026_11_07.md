# Triage: LF part 13a2, round 9 (lf-p13a2-20261107-r9), 7–8 Nov 2026

## Verdict

Clean, a full round: no fatal, serious, or minor finding, and three trivial findings (t1–t3). r8 was clean too, so **part 13a2 is done** (two consecutive clean rounds, the second a full round).

LF reviewed at 9186fbbbf1be (table b9386336d887, LABELS 857f1538fd28, Cauchy e0c534fa3017). The referee confirmed the round-8 repairs. It checked:
- CMP 98 (52), (158)–(164) and Proposition 6;
- PBG (3.133) and p.422 l.32–33;
- LFR I and II (1.25), (1.50), p.195 and p.197;
- CRE (2.6), BETA Lemma 2.1(i), and BP_LAYER_WIDTHS #4.16–#4.18-2-2.

It found no misquotation, no circularity, no volume or scale dependence, and no SU(N)-specific fact.

## Repairs

| Finding | Where | Repair |
|---|---|---|
| t1: η means the fine spacing in "e^{iηA}W" and CMP 98's dimensionless η = ε/a_m in the next line | #4.53-1, #4.53-1.1 | Both configurations are now e^{iεA}W, in #4.53-1 (twice) and in #4.53-1.1's U^A(V′^B₀) = e^{iεA}U^A(V′^A₀). η now means only CMP 98's η = ε/a_m, in #4.53-1.0 |
| t2: "p.422's factor (L^{j}η)^{−1}" uses j before #4.54-0.1.1 defines it | #4.54-0.0 | The sentence now reads "the worse of p.422 l.33's additional factors, the source's inverse spacing a_{j(x′)}^{−1} (Bałaban's (L^{j′}η)^{−1}, his y′ being the source), against the weight a_{j(y′)} of ‖·‖_{y′} gives the spacing ratio …". The line reached 640 characters, so this sentence becomes the new sub-tag #4.54-0.0-1 |
| t3: (T-Λ)'s clause names α₀^{CMP} as a fixed multiple of ε₁ but not α₁ | #4.50-1.1.0 | The CMP clause is now its own sub-tag #4.50-1.1.0-0: "its α₀ of (52), that section's α₀^{CMP} (not PBG's α₀), and its α₁ of (158), taken as twice that section's bound on a_k·sup abs(A), both fixed multiples of ε₁, sufficiently small". #4.50-1.1.0 ends at the data path's regularity |

## Re-derivation

- **t1.** For a fine-lattice field A and fine spacing ε, U′ = e^{iεA}W. In CMP 98's units the field is A′ = a_mA and the fine spacing is η = ε/a_m, so ηA′ = εA. Proposition 6's condition |A′| < α₁ is a_m sup|A| < α₁, which follows from a_k sup|A| < α₁ because a_m ≤ a_k. #4.53-1.1's second bracket already used e^{iεA′*}.
- **t2.** PBG (3.133) (p.422 l.25–27) bounds H(x, y′) with x ∈ Δ(y), y ∈ Λ_j the evaluated block, and y′ ∈ Λ_{j′} the source. Line 33 adds "(L^jη)^{−1}, or (L^{j′}η)^{−1}".
  - In the LF's labels, y′ is the evaluated block and x′ the source.
  - For y′ coarser than x′, the worse factor is the source's a_{j(x′)}^{−1}.
  - Against the weight a_{j(y′)}, it gives a_{j(y′)}/a_{j(x′)} = L^{j(y′)−j(x′)} ≤ L^{3(j(y′)−j(x′))}, K_ρ's factor (#4.9-2-1).
- **t3.** #4.53-1.1 bounds both perturbations on the layer k:
  - a_k|A| ≤ (π/2)dB₀c_tot(1/128)‖𝔛‖_∞ ≤ (π/8)dB₀c_tot(1/128)ε₁, by ‖𝔛‖_∞ ≤ ε₁/4 (#4.51-1.1);
  - a_k|A′*| ≤ c_{A′}(ε/a_n)^{1−ε₀}ε₁ ≤ c_{A′}ε₁.

  Twice the larger bound is a fixed multiple of ε₁, and (158)'s strict inequality holds at it. Through (161)–(163), the O(1) c_v is uniform in α₁ below a fixed α₁*. So the smallness is a condition cε₁ ≤ c′, covered by #4.50-1.2.

## Consumers

- Nothing else cites #4.50-1.1.0 (grep of the LF), so the split changes no citation.
- #4.53-1's statement is unchanged in content, and #4.53-1.2's constants are unchanged.
- #4.54-0.0-1's conclusion (the factor of K_ρ) is unchanged, and so are #4.54-0.1.2 and C_pr.

## Repaired SHAs

LF 9186fbbbf1be → 6cb9d70ab5fa. Relabel requested from the table fork. New tags: #4.50-1.1.0-0 and #4.54-0.0-1. There are no new {#D.…} symbols.

## Next

Packet 13b r3. The build lf-p13b-20261107-r3 (LF ff32ad403ddb) was never launched. Its snapshot predates the 13a2 r7–r9 repairs and the table's later rows: 13a's old #4.54-0.1.1, with RM, would sit in the referee's permitted background. So 13b r3 is rebuilt as lf-p13b-20261108-r3 at the current LF after the relabel. Its extracts #4.556–#4.565-1 and #4.567–#4.568 are unchanged since ff32ad403ddb, apart from the bookkeeping repoint in #4.561.1-2.

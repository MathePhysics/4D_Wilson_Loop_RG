# Triage: LF part 13a2, round 7 (lf-p13a2-20261107-r7), 7 Nov 2026

## Verdict

Not clean: one minor finding (m1) and two trivial ones (t1, t2). 13a2's clean count returns to 0. r6 was clean, so the next two rounds must both be clean, the second a full round.

LF reviewed at d7604c80f69f (table 29f7da24a7d9, LABELS 83db907f3cf4). The referee confirmed the round-6 repairs. It found no misquotation, no circularity, no volume or scale dependence, and no SU(N)-specific fact.

## Repairs

| Finding | Where | Repair |
|---|---|---|
| m1: d(y′, x′) ≥ RM(i − 1)_+ by PRT2 (2.60) is applied on 𝐁″_k, whose top N₀ layers are only LM wide, outside (2.60)'s printed scope | #4.54-0.1.1 | The bound is now d(y′, x′) ≥ LM₁(i − 1)_+, by (2.60) with RM replaced by LM₁, the common lower bound of the layer widths of 𝐁″_k under (J-W) (#4.9-1; BP_LAYER_WIDTHS #4.16–#4.18-2). It holds with ⅛δ₀LM₁ ≥ ⅛δ_*LM₁ ≥ 1 by (J-W), where δ_* ≤ δ₀ is the rate of #4.20 (#T12.21-1). The ≤ 3 and C_pr are unchanged |
| t1: R_k ≤ 2^{r+1}L(log g_k^{−2})^r is stated at one run's g_k, while R_k is the larger of the two runs' values | #4.55-1 | Now "each run's R_k ≤ 2^{r+1}L(log g_k^{−2})^r at its own g_k (#3.29-1) and #4.55-0.1's bound on either run's log g_k^{−2}" |
| t2: CMP 98 Proposition 6 also needs (52) for the base, but the text and (T-Λ) name only (158) | #4.53-1, #4.50-1.1.0 | #4.53-1: "and W satisfies (52) with α₀ = 2C₀^{ms}ε₁ (Proposition 6, p.043), as both bases below do (W = U^A(V′^A₀), a minimiser of (b), and W = MU^B = Ũ, #4.48.0-0, with abs(W(∂p) − 1) ≤ ε²abs(F))". The sentence "These blocks lie …" moves to #4.53-1.0. (T-Λ) (#4.50-1.1.0) now lists "the conditions of CMP 98 Proposition 6 (p.043), α₁ of (158) and α₀ = 2C₀^{ms}ε₁ of (52) sufficiently small" |
| Observation: the leading 2 in ε_{D″} is slack | none | No change, as in r6 |

## Re-derivation

- m1:
  - BP_LAYER_WIDTHS #4.16: (2.57)–(2.61) rest on the crossing length of each layer, so they hold with RM replaced by any common lower bound of the widths.
  - #4.17 and #4.18-2-2: on 𝐁″_k that bound is LM₁. The top N₀ layers are LM wide and the others are ≥ M > LM₁ wide.
  - (J-W) (#4.18-2) gives ⅛δ_*LM₁ ≥ 4 log L + 1, with δ_* := min(δ₀^{PBG}, δ₀^{(2.43)}) ≤ δ₀.
  - So (3/8)δ₀d(y′, x′) ≥ 3(i − 1)_+, and (|j(y) − j| + 1)e^{−(3/8)δ₀d} ≤ (i + 2)e^{−3(i−1)_+} ≤ 3 as before.
  - The column count c_K in #4.54-0.1.2 was already taken on 𝐁″_k with LM₁ (#4.9-1), as the referee confirmed.
- t2:
  - CMP 98 (52) is |U(∂p) − 1| < α₀η² (p.026), and Proposition 6 (p.043) holds for U_0 satisfying (52), with α₀ and α₁ sufficiently small.
  - Both bases satisfy a_j²|F| ≤ 2C₀^{ms}ε₁ (#4.48.0-0). With |W(∂p) − 1| ≤ ε²|F| and η = ε/a_j, this is (52) at α₀ = 2C₀^{ms}ε₁.
  - The smallness is a condition cε₁ ≤ c′, so it holds for γ small, by #4.50-1.2.
- t1: #4.55-0.1 applies Lemma 2.1(i) at the pinned ḡ to both runs (#C5.7-7), so each run's R_k is bounded by the same polylogarithm.

## Consumers

- #4.54-0.1.1's ≤ 3 feeds #4.54-0.1.2, C_pr, and C_A(M). None changes.
- #4.50-1.1.0 is in 13a1, which is done. Its change adds one smallness condition to (T-Λ), consumed by #4.53-1. It is put under review in 13a2 r8, as a separate extract.
- (T-Λ)'s callers (§4(d), 13b) use it only as "for γ small".

## Pre-check for r8 (lf-p13a2-20261107-r8)

Gate answers, all yes:
- The changed lines are re-derived (see above), and their arithmetic and citations are re-checked: PRT2 (2.60) with LM₁ via BP_LAYER_WIDTHS #4.16–#4.18-2; CMP 98 (52) on p.026 and Proposition 6 on p.043, both read in the transcription.
- New symbols are checked: δ_* against #T12.21-1, and α₀ is a local constant of (52).
- Wider implications are checked: (T-Λ)'s callers see one more smallness condition, and #4.50-1.1.0 is under review in r8.
- Linear order is kept: 13a2 runs to done, then 13b.
- Relabelled at LF b4f32ca7849c (table 30aec4a3446b, LABELS 59a564066c7f, verified). The spec is current, and the packet is built (argument 13,079 characters).

- The changed lines are re-read: #4.50-1.1.0 (527 characters), #4.53-1 (542), #4.53-1.0 (112), #4.54-0.1.1 (492), and #4.55-1 (600).
- δ_* is checked against the table: #T12.21-1, JOINS #4.20. It is not #T12.17's δ_*; the LF's δ_* at #0.1.12 is the same rate.
- The Cauchy note's naming clashes, reported by the table fork (#T12.7-x indexing), are repaired before the launch:
  - (6.2)'s weight is now ω^s, and §10.4's oscillation bound is 𝔬; exp(C_PP) stays ω, as in #T12.10.
  - The near part is F^{nr}_j, and F_j := F^{nr}_j + the far sum.
  - §11b's ε₁ is now ε_a.
  - §10.4's q is now q_T, and §11c's q is marked as the continuum note's loop parameter.
  - §10.3's δ_i is now δ^μ_i.
  - ν := 𝒬′*λ^B is now ν_λ; LF #4.131's #D.ν.3 points to it.
  - #CP.22-3 cites LF #4.656's W instead of restating it.
  - The local letters T, R, ρ, and M′ are unchanged: each is defined at its use inside one section, and the table states the clash.
- The Cauchy note's §8.7, §9.3, §10.3, #C1.1-2, and #C5.7 are background for 13a2. Of the renamed symbols, only δ_i (#C10.3.29-3, §10.3) lies in sections near those cited (#C10.3.29-2), and #C10.3.29-2 is unchanged.

## Repaired SHAs

LF d7604c80f69f → 5a0cdf89528a → b4f32ca7849c (with LF #4.131's ν alias). Cauchy e35edf723b18 → e0c534fa3017. Relabel requested from the table fork.

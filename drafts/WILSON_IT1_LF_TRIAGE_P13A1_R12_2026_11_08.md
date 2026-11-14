# Triage of lf-p13a1-20261108-r12

## Verdict

- r12 was a full round of 13a1 (#4.43–#4.50-2) at LF be1108eaf60a, table 6d09b1b5054d, and labels 971e7d7d5325.
- **Fatal:** none. **Serious:** none. **Minor:** none.
- **Trivial:** t1–t4, wording only, repaired below by rewording.
- r11's t-i–t-v were confirmed repaired.
- The round is clean. With r11 (narrow, clean) this is two consecutive clean rounds, the second full, so **13a1 is done**.

## Repairs

| Finding | Line | Issue | Repair |
|---|---|---|---|
| t1 | #4.50-0.0, #4.50-1 | 2C₁′ε₁ < π and the G-dependent radius under which G's elements near 1 are e^{iX}, X ∈ 𝔤, were covered only by "the smallness that VAR Sect. G needs" | #4.50-0.0: "…(p.305 l.11–12; inferred, not printed in (172)), which holds when C₁′ε₁ is below a radius depending on G under which the elements of G are e^{iX}, X ∈ 𝔤, abs(X) < π (G being a closed subgroup of U(N)). Bałaban's logarithm returns B′ there, since abs(B′) < 2C₁′ε₁ < π". #4.50-1: "…for this C₁′, with 2C₁′ε₁ < π and the radius of #4.50-0.0 among it, …" |
| t2 | #4.46-0-1, #4.48.1-1 | (b)'s count is used on 𝐁_k(Z) before #4.48.1-1 records the transfer; #4.48-3.0.3 uses α = 1/32 | #4.46-0-1: "by the count of (b), which holds on 𝐁_k(Z) (#4.48.1-1)". #4.48.1-1: "(2.59) at α = 1/16 and α = 1/32 (#4.48-3.0.3) follows from (2.59) at α = 1/128" |
| t3 | #4.50-1.2 | (T-π) carries (b)'s VAR C₁, while (c) uses C₁′ and its own C₁ | "the condition (T-π) of (b) (#4.38-1), with (b)'s VAR C₁ = 2C₀/B₃ at C₀^{ms} (#4.7-2-1), not C₁′," |
| t4 | #4.43-1.1 | ε_P drops the printed factor N₀^{−1} | "abs(∂V_k − 1) < 2L(L + 1)N₀^{−1}R_kε_k ≤ ε_P := 2L(L + 1)R_kε_k (N₀ ≥ 1)" |

- **Splits.**
  - #4.43-1.1 became 648 characters with t4, so its second sentence ("So LFR I Proposition 1, …") is now #4.43-1.1-1. V_{Λ^c} and ε_P keep their definitions in #4.43-1.1, so #T12.9's pointer is unchanged.
  - #4.50-1.2 became 627 characters with t3, so its second sentence ("Every condition of (T-Λ) but …") is now #4.50-1.2-1.
- **Re-point (bookkeeping).** #4.562-1.1 cites the uniformity sentence and its "two exceptions named there", so its "(#4.50-1.2)" now reads "(#4.50-1.2-1)".

## Checks

- **t1, re-derived.** G is a closed subgroup of U(N), so it is an embedded Lie subgroup. exp maps a small ball of i𝔤 homeomorphically onto an open neighbourhood of 1 in G, in the subspace topology. That neighbourhood contains G ∩ {abs(U − 1) < r} for some r depending on G, and the ball can be taken inside abs(X) < π.
  - For Hermitian X with spectrum in ]−π, π[, the principal logarithm of e^{iX} is iX.
  - So, for abs(V − 1) < C₁′ε₁ ≤ r, VAR's B′ (Hermitian, abs(B′) < 2C₁′ε₁ < π) equals that X ∈ 𝔤, by the injectivity of exp on such matrices.
  - Both conditions are cε₁ ≤ c′, with c, c′ depending on G, C₁′, and so on M, as #4.50-1 states. No SU(N) fact is used.
- **t3.** #4.7-2-1 gives VAR's C₁ = 2C₀/B₃ taken at C₀^{ms}, with ε₄ = 3B₀C₁B₃ε₁ = 6B₀C₀ε₁ (#4.37). This matches #4.38-1's "VAR's ε₄ = 3B₀C₁B₃ε₁".
- **t4.** N₀ ≥ 2 (#4.44-0), so the weakening is valid. p.193 l.23 prints "< 2L(L+1)N₀^{−1}R_kε_k".
- **Line lengths.** #4.43-1.1 322, #4.43-1.1-1 339, #4.46-0-1 250, #4.48.1-1 349, #4.50-0.0 574, #4.50-1 531, #4.50-1.2 320, #4.50-1.2-1 326, #4.562-1.1 342 characters. No CRLF.

## Pre-check of lf-p13b2-20261108-r17 (narrow)

- **Spec.** specs\spec_p13b2_r17.json, prior lf-p13b2-20261108-r16, narrow. Its LF SHA is updated to 14a59772400b.
- **Changed since r16 (LF 59a9b7a0e6ac).**
  - r16's triage (m-a, o-b, o-c): #4.517, #4.561.1, #4.561-1.2, #4.561-1-2, #4.561.1-1.3-1.1, #4.563-3-1.
  - This triage (13a1, not under review in r17): #4.43-1.1, #4.43-1.1-1, #4.46-0-1, #4.48.1-1, #4.50-0.0, #4.50-1, #4.50-1.2, #4.50-1.2-1.
  - In 13b2: #4.562-1.1, the re-point only.
- **Re-read.**
  - **#4.517's sentence.** abs(log u) ≤ −log(2 − e^s) ≤ 2s ≤ 4dε₂ ≤ 4c_Gdε₂ for s ≤ 2dε₂ ≤ ¼ and c_G ≥ 1. The BCH sum converges in 𝔤^c for s < r_G and is the principal logarithm there (re-derived in r16's triage).
  - **#4.561-1-2 and #4.561.1-1.3-1.1.** The condition holds at ε₂^{AL} ≤ ε₂/4.
  - **#4.561.1-1.3-2.** It still uses 4c_Gdε₂ ≤ 1 to get 8c_Gdε₂^{AL} ≤ ½.
  - **#4.561.1.** It names V′ apart from the integration variables of #4.559-1.1 and from V′^X₀. V′V₀ is a pointwise product.
  - **#4.563-3-1.** The count (a_j/a)^d cancels (a/a_j)^d for every finer spacing a, including run B's fine plaquettes on T_{1.70}.
  - **#4.562-1.1.** Its "two exceptions named there" are #4.50-1.2-1's "the first of #4.50-1.1 and (1 + β₀)²γ < e^{−p₀}". The new conditions in #4.50-0.0 and #4.50-1 are cε₁ ≤ c′, so its argument is unchanged.
- **Symbols.** c_G and r_G are #T4.10 (table l.121, "the radius of the BCH and logarithm series"). The radius in #4.50-0.0 is described, not named, so no new symbol enters. The requirement c_G ≥ 1 is still pending in #T4.10 with the table's owner.
- No known weak point and no OPEN is in r17's named steps.
- **Rounds.** 13a1 is done. 13b2: count 0; r17 (narrow), then r18 (full).

## SHAs

LF be1108eaf60a (r12's snapshot) → 14a59772400b (t1–t4, splits, re-point). Table 6d09b1b5054d and labels 971e7d7d5325 (unchanged; relabel pending with the table fork for #4.43-1.1-1 and #4.50-1.2-1).

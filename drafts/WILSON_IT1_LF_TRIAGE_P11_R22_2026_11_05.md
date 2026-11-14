# Packet 11 r22 Triage (LF §4(a)–(b) and #0.17)

Review: verification/isolated_reviewer/reviews/lf-p11-20261105-r22/review.md (full round), on LF d1de5b46e7af, labels d77b22572463, and table b562b85c8322.

## Verdict

r22 has one serious finding, S-1, and four trivial findings, t-1 to t-4. So it is **not clean**. r23 reviews the changed lines; a full round follows if r23 is clean.

## Repairs

| Finding | Lines | Repair |
|---|---|---|
| S-1 | #4.1, new #4.5-1 to #4.5-2-2, new #4.7-1-4-3 to #4.7-1-4-3-2, #4.7-1-5-1, #4.9-1-1, #4.17, #4.22.3-0, #4.40.2-2, #4.41, new #4.41-0-1, #4.42; table #T4.35 | (1.70)'s configuration U″_{h+2} = U″_{k,Z″_{h+2}} is identified as the minimiser for 𝐁_{1.70} := 𝐁″_k ∪ 𝐁_{h+1}(Z″_{h+2}) of CRE (2.14)–(2.15) (inferred, labelled). j = h + 1 is forced, and (2.14)'s hypotheses are checked. Its layers are ≥ LM₁ wide in the four cases of #4.14 one index up, and its top layer is not crossed. supp w lies in Ω^{∼−2}, where the set is 𝐁″_k. The collar data are read as M^·(Q^{s*}_{h+1}W) (inferred, labelled) and satisfy (7). The layer 0 is pinned (VAR (3) at j = 0), so the bottom strip has explicit bounds within C₀. The runs' collars differ on the strip T_{1.70}. There run B is at least as fine as run A, so the data ratio vanishes and only the strip current of #4.445.2 enters. #4.445.3 bounds it by C_Tπ(x)ε₁, and C_w(ε₀) gains C_T beside C_G(ε₀)c″_K. |
| t-1 | #4.7-1 | The Hölder bound B₄(β₀)Mε₁a_j^{−2−β} (VAR p.279 l.22) is named. |
| t-2 | #4.9-1 | "2R_j > R for γ small" is replaced by "> LM₁ by M > L²M₁, the common width of #4.16–#4.17". |
| t-3 | #4.454.18 | "L ≥ 1 M₁-cubes" is replaced by "LM₁ ≥ 1 units of d". |
| t-4 | #4.26 | The text now says "VAR's regularity parameter ε₀, not the Hölder exponent ε₀ of π", and the upper bounds are on VAR's ε₀. |

## Pre-check

- **Sources read.**
  - LFR II p.367 (end) and p.368 l.2–7: "we localize it again in the domain Z″_{h+2} instead of Z"; "Denote for simplicity the above configuration by U″_{h+2}". The configuration depends on exp ig_kB exp iQ̃(η𝐀₀) on Ω″^{∼2}_{h+1} ∩ Z″_{h+2} and on V″ elsewhere.
  - LFR II (1.16), p.360: U″_k = U″_{k,Z}(M^·(U″_k)), with the argument (M^·(Q_k^{s*}V_k))^{−1}; its support is "a layer of width 2M₁ at the boundary ∂Z".
  - CRE p.257, (2.14)–(2.15):
    - "Assume that ∂Ω ⊂ Ω_j ∖ Ω_{j+1}, that Ω is a union of M₁-cubes in the lattice T_ξ, and that the distance between ∂Ω and this boundary of Ω_j, Ω_{j+1}, which is contained in Ω, is greater than, or equal to 2M₁".
    - (2.16) uses M^·(Q_k^{s*}V_k).
  - CRE p.256 l.56–63: the maximal domains with dist(Ω_n, Ω_{n−1}^c) ≥ L^nξM₁, and "dist(Ω_j, Ω^c) ≤ 2M₁, or Ω^{∼−2} ⊂ Ω_j".
  - CRE (1.12): "U = V_0 on Ω_1^c".
  - VAR (3): Ū^j = V on Λ_j, j = 0, 1, …, k.
  - RG I (0.4): the averaging, with its contours Γ ∪ [x, x′] ∪ (−Γ′) ∪ (−c).
  - LF #4.445.2–#4.445.3 (the strip sources and their size, C_s and C_T) and #4.449 (the class (8) up to the boundary, VAR p.278 l.5–6, p.279 l.12).
  - Cauchy #C9.2.2 (C₀ := c₁₁·4R₁M₁(B₃ + B₄(1))) and the line stating c₁₁ ≥ 15.
- **Run dependence.** The collar is built down to each run's fine lattice.
  - Run A's domains: Ω^A_1 = M₁a_1 and Ω^A_m = 2M₁a_m for m ≥ 2.
  - Run B's domains: Ω^B_1 = M₁a_0, Ω^B_2 = 2M₁a_1, and Ω^B_{m+1} = Ω^A_m for m ≥ 2.
  - These follow by rounding M₁a_{m−1} + M₁a_m (or 2M₁a_{m−1} + M₁a_m) up to the grid of side M₁a_m, which is ≤ 2M₁a_m at L ≥ 2.
  - On T_{1.70}, run B's layers 0 and 1 are at ε/L and a_0. Run A's are a_0 to the distance M₁a_1 and a_1 beyond.
  - So MU″^B is the datum Q^{s*}_{h+1}W of run A there, and B = 0.
  - A first draft compared U″^B with an auxiliary run-A set pinned on T_{1.70}. It was dropped because the lift ℒ is nonlocal: ℒδA has tails on run B's pinned bonds. #4.445.2's strip current already accounts for run B's rows on the strip.
- **Arithmetic.**
  - Plaquette angle: |θ| ≤ (π/2)|e^{iθ} − 1| for |θ| ≤ π.
  - Axial gauge: (d − 1)·2M′·(π/2)ε₁ = π(d − 1)M′ε₁.
  - Differences: 4π(d − 1)M′ = 12πM′ < 38M′ at d = 4, and 38M′ ≤ 60M′ ≤ C₀.
  - In run A's units at a_1: 2^mπ(d − 1)L^{2+m}M′ ≤ 4π(d − 1)L⁴M′ < 38L⁴M′ ≤ 2L⁴C₀ = C₀^{ms}.
  - Widths: LM − 2dM₁ > (L³ − 2d)M₁ ≥ M₁. The distance 5MR_{k−N₀+1}a_{k−N₀+1} ≥ 5LMa_{h+1}, since a_{k−N₀+1} ≥ a_{h+2}.
  - #4.42: 48·2(C_G(ε₀)c″_K + C_T) = 96(…) and ρ̄² ≤ 4(…)²π(x)ε₁².
- **Every use.**
  - C_w(ε₀) is defined at #4.42 and #T4.35 and used at #4.42-1 (C_h). C_h's form is unchanged; only its value grows.
  - U″_{h+2} appears in the LF at #0, #4.1, #4.41, #4.160, and #4.174. #4.160 states the data only, and U_{k,Z}'s collar there is a later packet's item (handover).
  - Other notes (Cauchy, continuum, β-function) cite (1.70)'s configuration by name only.
  - "2R_j > R" and "L ≥ 1 M₁-cubes" have no other occurrence in the live notes.
  - The width lists #4.17, #4.22.3-0, #4.9-1-1, #4.40.2-2, and #4.7-1-5-1 now name 𝐁_{1.70}.
- **Lines.**
  - The new lines are under 600 characters, the longest 599.
  - #4.41 is 526 characters. #4.17 and #4.22.3-0 grew slightly. #4.9-1 and #4.26 are long lines with edits of about the same length.
  - CR 0 in both files, and there are no duplicate tags.
- **Table.** The #T4.35 edit was announced to the fork before it was made, and the SHAs were sent after.

## Repaired files

LF 07ab528b6dc2, table 44a3db409d3a, labels 2048f9d9fcd3 (multiply defined 101).

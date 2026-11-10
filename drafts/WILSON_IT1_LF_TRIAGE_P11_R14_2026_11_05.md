# Packet 11 r14 Triage (LF §4(a)–(b) and #0.17)

Review: verification/isolated_reviewer/reviews/lf-p11-20261105-r14/review.md (full round), on LF 517f95e16693, labels 4891cd09b8c8, and table ede3cd24c7da.

## Verdict

r14 has no fatal or serious finding and one minor finding, m-1, so it is **not clean**. The trivials T-1 to T-4 are repaired as well. r15 reviews the changed lines; a full round follows if r15 is clean.

## Repairs

| Finding | Lines | Repair |
|---|---|---|
| m-1 | #4.7-1, new #4.7-1-1 to #4.7-1-3-1, #4.7-2, new #4.7-2-1, new #4.7-3-1; table #T4.35 | VAR's class (p.279 l.1–4) is restated with its margin 2R₁M₁ = 2M′. Points with δ(x) ≥ 4M′ from Ω_j^c lie in index-j cubes at M = M′. Points with δ(x) < 4M′ lie in index-(j − 1) cubes at M = 2LM′, placed on the big-block grid with x in the last block away from the nearest y ∈ Ω_j^c. Their □̃ reaches 4M′ > δ(x) and stays in Ω_{j−1} ∖ Ω_{j+1} by the widths of #4.22.3-0. The thin top layer of 𝐁₂ needs no width. The bounds are linear in M, so C₀^{ms} := 2L⁴C₀. M ≤ M(ε₁) at 2LM′ gives ε₁ ≤ a₁/(2L). |
| T-1 | #4.11 | CRE p.256 l.61. |
| T-2 | #4.12-2-3 | M = L^m (CRE p.245 l.33); M₁ is a power of L by its choice (#4.22, #4.29); compatibility at p.245 l.39. |
| T-3 | #4.13-3, new #4.13-3-1, #4.13-3-2 | The ℓ∞ distance from Z″_{h+1} to Z^c by a monotone path in the box spanned by its ends. The pair Ω″_{j+1} ∩ Z^c against Ω^c ∩ Z is named. |
| T-4 | #4.17-1 | T_η is the fine lattice; its cubes are measured in the units of the scale k (LFR I p.179 l.7–8). |

## Pre-check

- **Sources read.**
  - VAR p.279, rendered: □ of size 2ML^jη, M a multiple of R₁M₁, a union of big blocks; □̃ of size (2M + 4R₁M₁)L^jη in B^j(Λ_j) ∪ B^{j+1}(Λ_{j+1}) = Ω_j ∖ Ω_{j+2} and not in B^{j+1}(Λ_{j+1}); (9)–(10) are B₃Mε₁ times powers of (L^jη)^{−1}, for M ≤ M(ε₁) = R₁M₁(a₁/ε₁).
  - CRE p.256, rendered: the condition dist(Ω_n, Ω_{n−1}^c) ≥ L^nξM₁ is on the line before "It is easy to see that dist(Ω_j, Ω^c) ≤ 2M₁" (l.62), so l.61.
  - CRE p.245 (text layer): M = L^m on l.33, "The above partitions have to be compatible" on l.39.
  - LFR I p.179, rendered: "unions of L^{−(k−j)}MR_j-cubes of the lattice T_η" on l.7–8.
- **Arithmetic.**
  - Index j: faces within 2M′ of x, so dist(□, Ω_j^c) ≥ δ − 2M′ ≥ 2M′; □̃ within 4M′ of x; Ω_{j+2} at ≥ LR′M′ > 4M′.
  - Index j − 1: reach 4LM′ − 2M′ + 2M′ = 4LM′ in the units a_{j−1}, that is 4M′ in the units a_j; □̃ within (4L + 4)M′ of x; ½LK_{M′}M′ ≥ 6.5LM′ > (4L + 4)M′ for L ≥ 2; R′M′ − 4M′ > (4 + 4/L)M′ since R′ ≥ 12dL; the layer j − 1 is R′M′/L > 4M′ wide in the units a_j.
  - Factors: 2L·L, 2L·L², 2L·L³ for A, F, ∇F; the Hölder term 2L·L^{2+β} ≤ 2L⁴.
- **Every use.** C₀^{ms} enters #4.40.1-3, #4.41-2–#4.41-3-3, #4.42 and table #T4.35 symbolically; only #T4.35 recorded the value, now 2L⁴C₀. The W-δ note's #W11.121 uses its own cubes at 3LR₁M₁, unchanged. No other note cites the value.
- **Lines.** The new and changed lines are under 600 characters; #4.7-2 was split at its list of constants (#4.7-2-1). CR 0, no duplicate tags.

## Repaired files

LF 02bb1b22b20e, table dc5e8a710045, labels 02dad79f36c7 (multiply defined 101).

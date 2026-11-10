# Packet 11 r23 Triage (LF §4(a)–(b) and #0.17)

Review: verification/isolated_reviewer/reviews/lf-p11-20261105-r23/review.md (changed lines of r22's repairs), on LF 07ab528b6dc2, labels 2048f9d9fcd3, and table 44a3db409d3a.

## Verdict

r23 has no fatal or serious finding, one minor finding, m-1, and five trivial findings, t-a to t-e. So it is **not clean**. Packet 11 is now split (packet plan, parts 11a–11e); the repaired lines lie in 11a (#4.5-1-1, #4.5-2 to #4.5-2-1, #4.7-1-4-3-1 to #4.7-1-4-3-2) and 11e (#4.41-0-1 to #4.42), and each part has its own rounds.

## Repairs

| Finding | Lines | Repair |
|---|---|---|
| m-1 | #4.5-2, new #4.5-2-0 | The box property is cited: all components of the domains Z″_j, h ≤ j ≤ k, are rectangular parallelepipeds (LFR I p.179 l.50–51). So CRE's lattice ℓ¹ distance to Ω^c is the distance to the nearest face, as for □₀ in #4.445.1, and Ω lies on the grid of the M₁a_m-cubes, m ≤ h + 1. #4.5-2 now cites #4.445.1's count with #4.5-2-0. |
| t-a | #4.5-2-1, #4.7-1-4-3-2 | Ũ = MU″^B is the a_0-lift Q^{s*}_{h+1}W on T_{1.70}, by run B's pin and the averaging of lifts on its layer 0 and by its constraint on its layer 1; this is run A's pinned datum only on run A's layer 0. |
| t-b | #4.7-1-4-3-1, new #4.7-1-4-3-1-1 | Run B's bottom strip in run A's units at a_0: factors L² for F, L³ for ∇F, and 2^mπ(d − 1)L^{2+m}M′ε₁ for the differences of order m ≤ 2 of A, all ≤ C₀^{ms}ε₁. |
| t-c | table #T4.35 | The dependence column adds ḡ for C_w(ε₀) through C_∇, and ḡ and g_a for C_h. |
| t-d | #4.41-0-1, #4.41-2-1, #4.41-3, #4.41-3-2, #4.41-3-3, #4.42 | The bound of (1.70)'s configuration is renamed ρ̄_{1.70}(x), defined at #4.41-0-1 (#D.ρ̄_1.70); #4.38's ρ̄(x) keeps its meaning. |
| t-e | #4.5-1-1 | "LM in the top N₀ layers" is replaced by "a layer below the top N₀ since h + 1 ≤ k − N₀". |

## Pre-check

- **Sources read.** LFR I p.179 (corrected file l.50–51): "By the definition all components of the domains Z_j″ are also rectangular parallelepipeds for j = h, h + 1, …, k." LF #4.13-2: the middle layers h + 1 ≤ j ≤ k − N₀ are at least LMR_{j+1} wide.
- **Box distance.** For a point of a box component, the nearest point of the complement is across the nearest face, so the ℓ¹ and ℓ∞ distances to Ω^c agree. The grid of M₁a_{h+1}-cubes contains that of M₁a_m, m ≤ h + 1, so the maximal domains are boxes on aligned grids, as the r23 reviewer checked by hand.
- **The lift on T_{1.70}.** On run B's layer 0 (depth M₁a_0) U″^B is the ε/L-lift (#4.5-1-4-1), and its average is the a_0-lift (#4.5-1-4). On run B's layer 1 on T_{1.70} (depth M₁a_0 to 2M₁a_1) run B's constraint fixes the average at a_0 to the layer-1 datum, the a_0-lift. So Ũ is the a_0-lift on all of T_{1.70}.
- **Arithmetic of t-b.** A cube of side 2M′a_0 has 2LM′ bonds of ε/L per side, so an axial bond angle is ≤ (d − 1)2LM′(π/2)ε₁ = π(d − 1)LM′ε₁, and a_0|A| = L times that. (ε/L)^{1+m}|∇^mA| ≤ 2^m(ε/L)|A| gives a_0^{1+m}|∇^mA| ≤ 2^mπ(d − 1)L^{2+m}M′ε₁. At m = 2 this is 4π(d − 1)L⁴M′ε₁ = 12πL⁴M′ε₁ < 38L⁴M′ε₁ ≤ 2L⁴C₀ε₁. A point within 4M′a_0 of ∂Ω and its cube lie within 6M′a_0 < M₁a_0 of ∂Ω (K_{M′} ≥ 12d + 1).
- **Every use.** ρ̄(x) in #4.41–#4.42 occurred at #4.41-0-1, #4.41-2-1, #4.41-3, #4.41-3-2, #4.41-3-3, and #4.42; none remains. #4.38–#4.40 and §5 (#5.19, #D.ρ̄(x).2) keep ρ̄(x). #4.9-3's pointer "#4.40–#4.42 use the profile ρ̄(x)" now names ρ̄_{1.70}(x) for #4.41–#4.42.
- **Pre-launch self-pass of 11a.** #0.17-1 listed the derived widths without 𝐁_{1.70}'s layers; it now adds them (#4.5-1-2). No other gap was found in #0.17–#0.17-2 and #4.1–#4.9-3. The table's ρ̄ entries (#T3.13, #T4.34) are other quantities or #4.38's profile, and C_ℒ^π's bound is homogeneous in the profile.
- **Lines.** The longest changed line is 586 characters; CR 0 in both files; no duplicate tags.
- **Table.** The #T4.35 edit was announced to the fork before it was made, and the SHAs were sent after.

## Repaired files

LF ec27d1b32902, table 5c3dda77979a, labels cf626884b711 (multiply defined 101).

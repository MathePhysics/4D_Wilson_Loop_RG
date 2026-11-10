# Packet 15a (Cauchy #C10.4.1–#C10.4.45-1), round 1, 9 Nov 2026

## Pre-check of cauchy-p15a-20261109-r1 (full)

- **Split:** §10.4 is cut at its sub-headings into 15a (#C10.4.1–#C10.4.45-1: the setting, (10.4)–(10.5), the regularity of H₁, the transports, and the parts of β), 15b (#C10.4.46–#C10.4.107: the bounds), and 15c (#C10.4.108–#C10.4.124-1).
- **Whole part re-read** (#C10.4.1–#C10.4.45-1), with the context extracts of the spec (#C10.1.2–#C10.1.8-2, #C10.2.1–#C10.2.3, #C10.3.3–#C10.3.3-1, #C10.3.3-11–#C10.3.3-11-3, #C10.3.40–#C10.3.42-3, #C10.4.46–#C10.4.46-3, and #C10.4.98–#C10.4.101-3).
- **Repairs made in this pass** (in place):
  - #C10.4.1-1 places run B's pair (U^B, J^B(U^B)) in the first case of #C10.2.1 at the same ℓ: U^B satisfies VAR (2) on T_{ε/L} at 2C₀ε₁ by (9.2); #C9.8.4–#C9.8.4-4 at the scale a_j and #C10.2.1-0-1 give (3.35) at the scale ℓ; and |J^B(U^B)| ≤ 2B_λε₁a_j^{−3} < α_Jℓ^{−3} (#C10.3.40, #C10.3.42-2).
  - New #C10.4.1-1-1: §10.2 holds in both runs, with G₁ and H₁ built as on PBG p.421 l.12–17 from (3.127) through (3.128)–(3.129), with the run's current written for J.
  - #C10.4.7-7: on the diagonal, the second term of (10.5) is ⟨E, G₁^{−1}E⟩ ≥ 0, G₁^{−1} being positive definite at the pair (#C10.2.1).
  - #C10.4.8 names the Hölder exponent γ_H and separates it from table #T3.33's γ.
- **Re-derived:**
  - #C10.4.1-1: Σ_{i<j}L^{i+1}η ≤ (3/2)a_j turns the per-level bound into (3.35) at the scale a_j (#C9.8.4-4); the cube argument of #C10.2.1-0-1 passes from a_j to ℓ = La_j with M multiplied by a constant of d and L; 2B_λε₁a_j^{−3} = 2B_λε₁L³ℓ^{−3} < α_Jℓ^{−3} under #C10.3.42-2's condition.
  - #C10.4.8: (3.133) with Theorem 3.10 for H₁ (p.423 l.33–36) gives the Hölder bound. A fine 4-cell of side 4ε has ℓ^∞ diameter 4ε, so the oscillation of ∇𝒜 is ≤ (4ε)^{γ_H}B₀(γ_H)ℓ^{−1−γ_H}e^{−½δ₁d(x,y′)} = 𝔬(x). The curl and the divergence are sums of 2 and of d differences, giving 2𝔬 and d𝔬.
  - #C10.4.45: |Cov_p(X, Y)| ≤ osc_pX·osc_pY. Subtracting constants leaves Cov unchanged, and for a probability measure |E[XY] − E[X]E[Y]| ≤ ‖X − c‖_∞‖Y − c′‖_∞ with c and c′ the midpoints, which is ≤ ¼osc·osc ≤ osc·osc. #C10.4.45-1: the box of sides 2ε, 2ε, ε, …, ε has diameter ε(4 + 4 + (d − 2))^{1/2} = ε(d + 6)^{1/2}.
- **Definition check:** 0 conflicts (17 allowed), each allowance checked against the other source's tag.
- **Size:** reviewed block 20.43k characters (25k cap). CR is 0, there are no trailing spaces or duplicate tags, and every line is ≤ 581 characters.
- **Spec:** specs\spec_p15a_r1.json (Cauchy f92f946e4b55, LF 6ac728004094). Rebuilt at launch.
- **Order:** after 14b1 r5 (full) and the queue in the packet plan.

Written 2026-11-09 09:28.

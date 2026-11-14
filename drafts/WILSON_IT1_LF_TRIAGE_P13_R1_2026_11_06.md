# Packet 13 r1 Pre-Check (LF #4.43–#4.55-1, #4.556–#4.565-1, #4.567–#4.568)

## The Pre-Check

Before the first round I re-read every line of the packet and re-derived each step. Four repairs were made.

| Item | Line | Repair |
|---|---|---|
| p1 | #4.53-1 | C′_Δ(M) was used without a definition. It is now defined as C′_Δ(M) := (C + B₀c_K)C_Δ(M) + 4CC_G(ε₀)c_K, since ‖X‖_∞ ≤ Δ ≤ C_Δ(M)(ε/a_n)^{(1−ε₀)/3}ε₁ (#4.51-3) and ε/a_n ≤ 1. |
| p2 | #4.55, #4.55-1 | "k < 8n" was inaccurate. In a young history k ≤ K < 8n + j(C) (#3.30). So log g_k^{−2} ≤ log(ḡ^{−2} + 8b′n + b′j(C) + C) by Lemma 2.1(i), and the prefactor is a power of that logarithm times k + 1 ≤ 8n + j(C). This is polylogarithmic times linear in n and independent of K. #4.55's last sentence moved into #4.55-1. |
| p3 | #4.568 | "K − j ≤ 7k/8 + j(C)" was inaccurate. It now reads "k + 1 ≤ 8n + j(C) (#4.55)". |
| p4 | #4.561-1, #4.561-2 | VAR prints two values of ε₂. One is ε₂ = 8B₅ε₁ for the regularity of the representation (p.305 l.54); the thresholds of Propositions 4 and 6 use this value, with ε₃ = 4ε₂ = 32B₅ε₁′ (113). The other is ε₂ = B₅ε₁ in Proposition 9 (p.309 l.13), the value of (173). #4.561-2 states which value enters where. #4.561-1 exceeded ~600 characters and was split. |

## The Steps Re-derived

- **Lemma (Two Constants) (#4.557–#4.558).**
  - 𝔴 = (𝔯 + z)/(𝔯 − z) maps the disc of radius 𝔯 onto the right half-plane and the upper half-disc onto the first quadrant. So Re 𝔥 = 1 − (2/π)arg 𝔴 is 1 on the segment and 0 on the semicircle.
  - 𝔉 is bounded on D₊, since 𝔢 ∈ [0, 1]. The factor ((𝔯² − z²)/(4𝔯²))^η has modulus ≤ ½ on D₊ and tends to 0 at ±𝔯. So the maximum modulus principle applies to 𝔉_η.
  - For |z| ≤ 1, |arg((𝔯 + z)/(𝔯 − z))| ≤ 2arcsin(1/𝔯). Since arcsin(1/24) < 0.04168, (4/π)arcsin(1/24) < 0.0531 < 1/16. So 𝔢 ≥ 15/16.
  - The real decay (ε/a_n)^{(1−ε₀)/3} becomes (ε/a_n)^{5(1−ε₀)/16} at z = i.
- **The real points (#4.560).** At real z with |z| < 24, the line's fields are ≤ 25 times the class bounds of (2.39). The bound C_c = 60 covers the linear terms, 2·25, and the quadratic ones, ≤ 10 for γ small.
- **(A-ii) (#4.43–#4.55-1).**
  - I re-derived the expansion at a minimum with κ_Λ, the polydisc P with C₁ := max(1, C_X(M)C_Φ(M)/κ_Λ), Schwarz's growth (κ_Λ/4)‖Y‖₂², and the comparison Δ ≤ C_Δ(M)(ε/a_n)^{(1−ε₀)/3}ε₁.
  - The common gauge gives the data difference ≤ C′_Δ(M)(ε/a_n)^{(1−ε₀)/3}ε₁ per point (p1), and the propagation gives C_A(M)g_j^{−2}(ε/a_n)^{(1−ε₀)/3}ε₁² per point.
  - The bound is uniform in K through p2.
- **The class (#4.561–#4.565-1, #4.567).** (T-c) is (T-Λ) with 26ε₁′ in place of ε₁. Its conditions are lower bounds on M and smallness conditions on γ, uniform in K. VAR's thresholds are those of p4.

The constants table gained row {#T3.34-1} (κ_s, κ_c of the LF, apart from the map's κ_s = RG II's κ₁). No line of this packet uses it.

## Files

LF f1f82651705d, labels c82f001241c5, table a8041051efc3. r1 launches after 12b r2 has been triaged and 12a r4 has reported.

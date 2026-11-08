# Triage of lf-k0-20261103-r40 (LF a71e8411bfd0 → 25d702f41997), 3 Nov 2026

Review: verification\isolated_reviewer\reviews\lf-k0-20261103-r40\review.md. Verdict: not established as written; no fatal; one serious (d6′), six minor. r39's b5 and all r39 minors closed. Each finding was checked before repair. All repairs are derived, not reviewed.

## Serious

- **d6′, the scale-j version of (K0)(d).** Confirmed: ‖ℓ^{−1}H_jB‖ ≤ C(d)‖ℓ^{−1}B‖ fails by the factor L across Λ_j/Λ_{j+1}, and a vortex count near a codimension-2 contact of two components of Λ_j indicates a unit-level gap growing like ((j + 1)log L)^{1/2}. So the global Combes–Thomas argument of (e), the localisation of (f), and the decay from the coarser interfaces in (g)(1) lost their j-uniform input.
- **Repair: freezing and a bootstrap.**
  - (c) The two-layer problem 𝒫₁: 𝒞₁ ⊂ 𝒞 is cut out by Q₁A = Q₁A_N on the scale-1 bonds of Ω₂ = ∪_{j≥2}B^j(Λ_j). A_N ∈ 𝒞₁ is least there. The deeper constraints are redundant on 𝒞₁. 𝒫₁'s gauge group lies in the full one. 𝒫₁ has the single interface Λ₀/Ω₁, so (c)–(d) hold as written. The frozen data is extended by Ã′ := 1_UA_N plus bumps. E vanishes beyond L/16 of Λ₀, so Q₁E = 0 on Ω₂.
  - (d) The unit-level scale-j paragraph and the H_j lift are removed. (d) is used for 𝒫₁, and through (g)(2) for V on the scale-j lattice.
  - (e) The weight is e^{±δρ} in the metric ds = dx/ℓ_ms of the full problem. ℓ ≤ ℓ_ms, so it is admissible for 𝒫₁'s Combes–Thomas argument, with δ = c(d)(1 + log L)^{−2} uniform in j.
  - (f) ℳ is the least bound on ‖A_N‖_{Q_{2L}} and ‖dA_N‖_{Q_{2L}} on the regions of (g), which cover Ω₂ and its 2L-neighbourhood. The frozen sources of a block of Λ_j are ≤ C(d)L^{d+3}ℳθ/θ_B times a first-layer block's, plus L^{d/2} per further layer. They are paid by e^{−δρ} for δr₂/L ≥ (d + 4)log L + C(d)(1 + log(1 + log L)), a choice of C(d) in r₂, and δRM ≥ (d/2)log L + C(d), RM chosen after L. This gives ℳ ≤ C(d)(1 + log L)^p + ℳ/2. The da bound is now stated in θ ≥ θ_B; all outside uses already read it in θ (l.6 F₁, l.1008 Ē, (K1), (K4)).
  - (g)(1) The coarser constraints act through the same freezing for V, with the frozen source ⟨σ̃∂₁V_N, ∂₁D⟩ = ⟨dH_jV_N, dH_jD⟩ and dH_jV_N = dA_N up to the finer constraints. The ds = dx/ℓ_ms metric is used in (g)(2).
  - The scalar argument of (f) needs only the per-block Poincaré bound, so its use on the full N(Q′) at l.1007 stands.

## Minor (repaired)

- m1: T̂_f's blocks are joined through data bonds of the same local component; the intermediate vertices are averaged over balls of radius ≍ m_f; Y(x) is a block of Z_f.
- m2: B_Y(x) ⊂ Y for d ≤ 4 (distance m(x)/(4√d)).
- m3: the hole-filling source uses Q_{C(d)r}, since T̂_f reads dT within C(d)m_f.
- m4: void, since the H_j lift is removed.
- m5: (g)(3)(iii) has the exponentially weighted sum Σ_{s″}e^{−c(d)abs(s − s″)}N₁(s″).
- m6: table line 232, exponent a → κ as in l.6 (table f43d6febb394 → 931fade2c56c; fork notified before and after).

## Next

Self-check done. Then the re-review of (K0) (r41, prior review r40), then (K1)–(K6).

# LF Packet 2, Review 1: Triage

Review: verification\isolated_reviewer\reviews\lf-p2-20261104-r1\review.md (LF 109ca4674cac). Verdict: not established as written. No fatal item; three serious items and several minors. All are accepted and repaired in the LF.

## Serious

1. **#0.1.23 / #A.7: θ < 1 not established.** Accepted. The Caccioppoli cutoff η now has its gradient in Q_{7s/8} ∖ Q_{3s/4}, and the near part of the non-local error reads w only on R_η = Q_{57s/64} ∖ Q_{47s/64}. The blend χ changes in Q_{5s/8} ∖ Q_{9s/16}. So w = u − ∂φ_A on R_η, and Lemma P on A′_s = Q_s ∖ Q_{9s/16} bounds that term by C(d)E(A_s). The Q_s gauge enters only the sources and the tails. This gives E(Q_{s/2}) ≤ C₁E(A_s) + ¼E(Q_s) + (sources) and θ_h = (C₁ + ¼)/(C₁ + 1) ∈ [5/8, 1). The capacity forms (old #A.6) are removed: below s₃ the sites of Λ^c in Q_s and in A′_s are connected (#A.1), so both gauges equal one constant on Λ^c. The hole-filling ratio is renamed θ_h.
2. **#0.1.24: the distant-pole source bound.** Accepted, and repaired by a cruder route that needs no Green's-function second differences. The non-local part −⟨g′, ∂₁ω_w⟩, with ∂₁ω_w = (1 − P_𝒮)(η²w), is bounded through the weighted bound of #0.1.17: Σ_b abs(∂₁ω_w(b)) ≤ C(d)L^{d/2}‖w‖_{Q_s}. With S = sup abs(g′) ≤ L^{−2}θ_B, this is a source of exponent 2. Since θ_h ≥ 5/8, α ≤ log(8/5)/log 6 < 1 < 2. The sources (data, coarse terms, tails) now have explicit exponents d + 2, 2, d + 2, and 10, and the Morrey bound is stated without a source remainder.
3. **#A.5: Lemma P's gluing.** Accepted. Lemma P is re-derived in four steps, replacing the old #A.2–#A.5:
   - #A.2: the averaged axial primitive on boxes, and on A′_s through the 2d slabs of A_s, with the slab constants fixed by the triangle relations (d ≥ 3);
   - #A.3: Poincaré on the sites of Λ^c in D, a connected union of fat boxes;
   - #A.4: an extension of a function on Λ^c ∩ D to D by reflections across the hyperplanes, weighted by distances, with ‖∂f̃‖² ≤ C(d)(‖∂f‖²_Z + ρ^{−2}‖f‖²_Z). Local joinedness enters here only;
   - #A.5: the assembly φ = ψ − f̃.

   No partition over boxes and no Dirichlet-face potentials remain. So items (a)–(c) of the review (the P ∪ P′ potential, the common constant, the corner overlaps) and the minor on #A.4's three-face case no longer apply.

## Minor

- **#0.1.22, fat pieces of A_s.** Accepted in modified form. Goodness now asks that the faces of Q_s and of Q_{9s/16} lie at distance ≥ ρ/(40d) from the hyperplanes. The excluded s have measure ≤ 5ρ/36. A′_s is the annulus whose pieces must be fat; the slabs of A_s carry no Λ^c condition.
- **#A.4, three or more faces and the rectangular cross-section.** Superseded by the reflection extension (#A.4 new).
- **#0.1.21, unstated conditions.** Accepted. The text now states:
  - the support of ∇η and the near band R_η;
  - the extension φ∘π of φ, with π the coordinatewise projection onto Q_s, and its weighted bound;
  - Ē as the bulk bound C(d)(1 + log L)^{2p}L^{d−2}θ² on every E(Q_L(x)) (#A.10).
- **#0.1.26, interior bound.** Accepted.
  - (i) g = P_𝒮g′ = g′ − ∂₁ω_{g′}. The gradient part is removed by ∂₁ψ₃, with ψ₃ = (∂₁*∂₁)^{−1}(1_{Q_R}(ω_{g′} − c₃)), which leaves F unchanged. It costs R^{1−d/2}L^{d/2}S in sup abs(F), which is ≤ C(d)θ_B after the dyadic factor R for d = 4.
  - (ii) ψ is extended by ψ∘π, giving polynomial tails.
  - (iii) R := t(y)/(4√d), with t Euclidean. The C(d) scales between R/2 and t(y)/8 are bounded by monotonicity.
  - The dependence on #0.1.18's kernel bounds is unchanged and is stated there as derived, not reviewed.
- **#0.1.24, hitting.** Accepted. A is placed in the cell of Λ^c inside Q_{2r}(x), at distance ≥ (K₀ + 2)n from Q_r(x), with C(d) ≥ 4(K₀ + 2). The order is now "hits A, hence the cell". Γ = d^{−1}I and 𝒥 = abs(·) are cited at p.82; checked on the page image.
- **#A.6 vacuous in the N_b problem.** Accepted. The capacity forms are removed; see serious 1.
- **θ for two objects.** Accepted. The hole-filling ratio is now θ_h.
- **C(d) in F₁ ≤ L^{1−d/2}Ē^{1/2}.** Accepted.
- **Q₁ size L^{1−3d/2}.** Valid as written; kept.

## Next

Self-check of the repaired #0.1.20–#0.1.26 and #A.1–#A.7, then p2 r2.

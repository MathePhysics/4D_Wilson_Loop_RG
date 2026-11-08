# Triage of lf-k0-20261103-r39 (LF 9b80fce2014e → a71e8411bfd0), 3 Nov 2026

Review: verification\isolated_reviewer\reviews\lf-k0-20261103-r39\review.md. Verdict: not established as written; no fatal; two serious, thirteen minor. Each finding was checked before repair. All repairs are derived, not reviewed.

## Serious

- **S1 (b5), the Hardy step of (K0)(b).** Confirmed: where the foot of the normal line lies off f, the in-plane part of the axial potential φ_f is used by a wedge of sites, not a disc; the referee's T_y ≍ ε(−1)^{z₁} on {x = 0, y ∈ [r/8, r/4]} gives ratio ≍ r^{1/2}. The referee's single potential with Ĝ = 0 on all of Λ₀ fails between distinct local components (T = ∂χ with χ = 1 on one component has dT = 0). Repair: per-face cone potential T̂_f = T − ∂Ĝ_f from the blocks of side L of Λ₀ with a face in f, patched by φ^f_Y as in (d); T̂_f = 0 on Z_f ⊃ f; the patching terms G^Y_T − G^{Y₀}_T close through Z_f (T = 0) and obey the cone bound of J; ‖T̂_f/m_f‖ ≤ C(1 + log L)^{1/2}‖dT‖. Faces are taken per local component.
- **S2 (d6), the scale-j version of (d).** Confirmed: inside Λ_j, j ≥ 1, only Q_jD vanishes, and a bump lift loses L. Repair: run (d) for V = Q_jD on the scale-j lattice, γ₀‖∂₁V‖² ≤ ⟨V, Δ_jV⟩ ≤ ‖dD‖²; lift by H_j with ‖dH_jB‖² ≤ γ₁‖∂₁B‖² and ‖ℓ^{−1}H_jB‖ ≤ C(d)‖ℓ^{−1}B‖ (PRT1 (1.103), (1.101), (1.110); constants of d only, checked on pp.34–35); tails in other layers corrected at C(L)e^{−δ₀RM/8}.

## Minor (all repaired)

- d2: Schur sum ≤ C(1 + log L); ‖m^{−1}D̃^Y‖² and ‖de‖² carry (1 + log L); final (1 + log L)² unchanged.
- a1: K at b₋ on coarse crossing bonds: B denotes the datum shifted by −KU′_ax(b₋) (l.6).
- b1: mixed second differences via (6.17) on ∇_{e′}P, (6.19), and Harnack (checked on LL p.131).
- b3, g4: χ_f conditions rewritten (faces, not planes: the plane version fails at the 90° ray of a convex edge); (g)(4) uses T̂_f.
- e1: Ω_c at coarse crossing bonds; only the variation of f within one scale-j block enters.
- e2: δ ≤ c(d)(1 + log L)^{−2} in (e)(i).
- f2: localisation conditions raised to (d/2)log L for the plain-ℓ² bound on A_N.
- g1: finer constraints only change A_N − H_jV; coarser act on V and decay at rate δ; minimum cited as PRT1 p.29 l.4–5.
- g3(iii): slice choice s₀ ≤ R/16 with the smeared N₁; truncation values bounded by (ii).
- g3(iv): the case s < C(d) through the z′-sum.
- g5: the chain's "fine data not read in the weighted region" at j ≥ 1 (cases (i)–(ii) of l.6, Q_ic = Q^{(i−j)}Q_jc).
- l.6: "1/a" → "1/κ"; step (1) cites the Δ_j form bound (1.66)–(1.67) without σ_k's locality.

## (K1)–(K6) self-check repairs (same revision)

- (K1): source of ‖A‖_y ≤ C(1 + log L)^pL^{d/2}θ (l.6 C̃ bound; (K0)(f)–(g)).
- (K3): "thin slab" replaced by the exact set.
- (K4): kernel cut 3L; the max-principle line with abs(M − m).
- (K5): K := K₀ + 1, stopping at the exit from Q_{K₀r}; hitting argument stated for the box used.
- (K6): reason that Q_{Kr₀}(z) meets one local component.

## Next

Re-review of (K0) (r40, same scope, prior review r39), then (K1)–(K6) (LL pp.81, 130, 131 images from the r38 folder).

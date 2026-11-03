# Triage of lf-iv-20261103-r38 (3 November 2026, from 16:53)

Packet: LF 0bf759f90f53, table eecb4705d23a. Verdict: NOT ESTABLISHED. The report was read in full; every item is accepted unless marked otherwise below.

## Serious

- **S1 (item 8): face-layer energy.** Fine data bounded only in supremum can have dB ~ θ_B on the face plaquettes of Λ₀. By closedness on the unit cubes that straddle the face, every admissible a has energy ≳ Σ_face abs(dB)² ~ L^{d−1}θ_B² per block face. This breaks Ē ≤ C L^{d−2}θ², the per-block bound of (K0)(b), and "sources of bulk size". The pointwise size near the face is θ_B/t. Accepted. Repair below.
- **S2 (items 9 and 10): gauge group of ker Q versus the N_b slice.** VAR's constraints at an interface are coarse crossing bonds (REG p.81). The scale-j bonds into the coarser layer carry no constraint. So the gauge group of {Qa = δ, a = B on the data bonds} is N(Q′) ∩ {λ = 0 on Λ₀}, and the P_b-slice leaves zero modes. Accepted. Repair below: the N(Q′)-slice, with the Landau bound re-derived for VAR's crossing structure.
- **S3 (item 21): volume dependence of v and of the far part of (K4).** The global Hodge part has log(S/L) at the edges for data spread over a cube of side S. Accepted. Repair below: localise at scale L.
- **S4 (item 12): layers j ≥ 2 in (K0)(c)–(d).** Accepted. Repair below: the multiscale metric.

## Minor (all accepted)

- Item 2: Q̃A_N = B + D̄P(λ^N − λ^{ax}), not B. Use a′ := U′_ax + ∂ζ′ with Q′ζ′ = −KU′_ax and ζ′ = 0 on Λ₀.
- Item 3: PBG (3.114)–(3.115) use scaled derivatives, which is CMP98's normalisation. In RG I's normalisation the identity comes from (0.4) directly.
- Item 5: table line 239 mixes the normalisations, so Q′μ = −L·K(a) should be −K(a). Table edit with the fork protocol.
- Item 7: QÃ = B fails at the coarse crossing bonds. The bump amplitude there is B(c) minus the fine-data contribution.
- Item 11: [P_b, f] is O(δ) as an operator; O(δ/L) holds on block-constant ∂*D. State this.
- Item 16: the χ_y wording is self-contradictory (in (K1) and in l.6).
- Item 18: the symbol a is used for both the mass and the exponent of W.
- Item 20: (K3) needs the thin-slab case. Use one deep site per cell in (K4).
- Item 21 (minor part): the l.6 summary disagrees with (K4).
- Item 22: Lawler–Limic 6.5.2 misprint; ball versus box. Already repaired after the launch (LF e24e9e4f9712).
- Item 23: r₀'s property is used only for r₀ ≥ 2t; (K4) needs chaining for t comparable to L.
- Item 25: the units of W at the scale k − 1.

## Repairs

(written in LF as they are made; listed here with their status)

Plan, in order:
- **Minor items.**
- **S3.** The local Hodge part v_x := ∂*Δ^{−1}(χ_xF), where χ_x is a cutoff equal to 1 on Q_{4L}(x₀) and supported in Q_{8L}(x₀). On Q_{2L}(x₀) the curvature left over is H := δΔ^{−1}(dχ∧F), of size ≤ C L^{−d/2}‖F‖_{Q_{8L}} and smooth at the scale L. Its Poincaré potential w_x has abs(w_x) ≤ C L sup abs(H). Only local energies at scales ≤ 8L enter.
- **S4.** (K0) is run for the two-scale problem Λ₀ ∪ Λ₁, localised to within half the width of Λ₁. The coarser layers and the Λ₁/Λ₂ interface enter through VAR (190) with C(L)e^{−δ₀·width/8}, which M₁ ≥ M₀(L) absorbs.
- **S1.** Split the response into a fine-data part and a coarse-data part. The fine-data part is E + a, with E the patched exact half-space minimisers in axial gauge. By the Gauss law the exact part of the tangential field is constant in depth, and the coexact part is the discrete harmonic extension P_sC₀. So abs(F_E) ≤ Cθ_B log L/max(s, 1), by Lawler–Limic Thm 6.3.8(a). The residual a has no fine data, coarse data ≤ C Lθ_B log L, and codimension-2 patching sources of bulk Morrey size.
- **S2.** VAR's gauge group N(Q′) for the two-scale problem. The partial axial condition D(b(p)) = 0 at one crossing bond per layer site reduces it to N_b. Then comes the N_b Landau slice of l.6. Finally, a gap bound for the jumps at the codimension-2 contacts between distinct Λ₀ components; a test mode gives the ratio L^{−2}/log L.

Status (LF c9a2c52655df):
- **Item 2, S3, the minor part of item 21, item 22's M, item 23.** Written (l.6 heading, *The gauge-invariant part.*, (K2), (K4)–(K6), l.1007). A_N is now v-free: Q′ζ^N = −KU′_ax, ζ^N = 0 on Λ₀, least norm.
- **Item 3.** Written in (K0)(a).
- **S1.** Written in (K0)(b): half-space axial minimisers E_f (Lawler–Limic 6.3.8(b), 6.3.9), angular sectors vanishing within a fixed angle of the edge of f's half-space, and the residual a = A_N − E with source ℓ_E of Morrey exponent d − 2. In l.6 the curvature enters H and w through F₁ (L¹ per L-cube, (K0)(f)), v splits into v(χdE) + v(χda) with abs(v(χdE)) ≤ C(1 + log L)³θ_B, and the hole-filling is run for a. The same changes are in (KW)'s heading, (K2), and (K4).
- **S2.** Written in (K0)(c)–(d), revised after a self-check. The first version (an 𝒳-slice with the gauge term ‖R_b∂*D‖² + Σ_𝒳w_b abs(Q_jD(b))²) was wrong in two places. Its step (i) treated the jumps at codimension-2 contacts between distinct components of Λ₀ as local. And its Combes–Thomas commutator needed ‖∂*D‖ ≤ C(1 + log L)‖dD‖ on the slice, which the contact jumps break. Now there is no gauge-fixing term; the problem is solved modulo ∂N(Q′). The gap holds for the weighted-Landau representative, ‖ℓ^{−1}D₁‖ ≤ C(1 + log L)²‖dD‖, by comparison with e + e_α + D′_L: D′_L is PBG's R_b-Landau representative (l.6 steps (2)–(5)), and e is the angular field carrying the contact jumps J. J is bounded through the two coarse crossing constraints at the contact, paired by translation: abs(J(x′)) ≤ C(1 + log L)^{1/2}‖dD‖_{Q_{CL}(x′)} in d = 4.
- **S4 (item 12 as stated).** Written in (K0)(e): Combes–Thomas in ds = dx/ℓ with the f-Landau representative, whose gap follows from (d) up to O(δ). Item 7 is covered by (K0)(c): the coarse data of the residual are B′ = B − QE, put on the bumps. Item 11 is moot, since there is no projection in q.
- **(K0)(b) also changed:** per-face representatives T̃_f (axial from f's plane), with the Hardy constant C(1 + log L).
- **Item 16.** χ_y is now supported at distance ≥ L/8 (l.6 and (K1)).
- **l.1007.** The complex part of ω is now bounded by a direct scalar problem (ω minimises ‖u_R − ∂ω‖ under Q′ω = KU′_ax), without local bounds on A_N in the deep layers.
- **NEW, OPEN (S5): the interfaces Λ_j/Λ_{j+1} with j ≥ 1, other than the part of Λ₁ at distance ≥ r₂ = C L(1 + log L)³ from Λ₂.** Found while writing S4. A coarser block at multiscale distance O(1) carries L^{d/2−1} times the local-unit sources, and no weighted L² bound localises this. So (K0)(f), and hence (KW), gives (1 + log L)^p only near Λ₀. What closes it is (KW) at each interface at the scale L^j, with a weight W_j, and the chain's norm carrying the product of the weights.
- **S5 plan (not started in LF).**
  1. Reduction. At the flat base Q_{j+1} = Q^{(1)}Q_j (PBG (3.15)), so the constraints on Λ_{≥j} are constraints on V := Q_jA. Minimising first over A with Q_jA = V and the finer constraints gives S_eff(V). Near Λ_j/Λ_{j+1}, at distance ≥ RM/2 from Λ_{j−1} in local units, this is ⟨V, Δ_jV⟩ (PRT1 (1.66)–(1.67), γ₀ ≤ σ_k ≤ γ₁, exponential decay) up to C(L)e^{−cδ₀RM}, and A = H_jV with H_j L-uniform (PRT1 (1.63)). So the interface Λ_j/Λ_{j+1} is VAR's Λ₀/Λ₁ problem on the scale-j lattice, with Δ_j in place of d*d: V = B on Λ_j (data), Q^{(1)}V = B on Λ_{j+1}, and no constraint on the scale-j crossing bonds.
  2. (KW) for Δ_j. The gauge part (K1)–(K6) is operator-independent (λ solves Δλ = σ with block-constant σ), and the hole-filling is already written for Δ_j (l.6 step (1)). (K0)(c)–(f) transfer with γ₀, γ₁ and [σ_k, f] = O(δ).
  3. The fine data for Δ_j. The d*d-extension E_f leaves a residual source of order θ per bond in the face layer, since σ_k is nonlocal. What is needed is a half-space extension for Δ_j with abs(∂E^σ) ≤ Cθ/max(s, 1). Route: tangential Fourier transform plus the exponential decay of σ_k; or a corrector supported within C log L of the face, with energy L^{d−1}θ², whose outer source is e^{−δ₀C log L}-small. This is the hard step.
  4. The weight. W_ms := Π_jW_j, with W_j of the form of W in the units of L^j about Λ_j/Λ_{j+1}. Check that its block averages at every scale stay ≤ C(1 + log L)^p, and that the chain (l.6, *the factor per level*) accepts it.
- **(K0)(d), the field e (LF 7583289ea6f4).** Rewritten after a self-check. The angular field χ_dJ̃∂φ had a spanning-tree mismatch at all scales about strata where several contacts meet. Its zone gradient bound was also unsupported. The new field is built on the blocks of Λ₀:
  - G^Y is the average of D along segments from a ball of radius m/8 in Y, m := max(dist(·, Λ₀), 1), and φ_Y is a partition by distance ratios.
  - de₀ = Σ D̃^Y ∧ ∂φ_Y, with ‖m^{−1}D̃^Y‖ ≤ C‖dD‖.
  - F_{YY′} is bounded pointwise: by loop averages for blocks joined through faces, and by (β) with the apex at x and k coarse constraints at contacts of codimension k ≥ 2.
  - The count gives ‖ℓ^{−1}e‖² + ‖de‖² ≤ C(1 + log L)²‖dD‖² for d = 4.
  - The corner-site count and the J(x′ + e) − J(x′) sentence of (β) are removed, since they are no longer used.
- **S5 (LF 36e3acd5b3bb).** Written as l.1009 (K0)(g), derived, not reviewed:
  - (1) The reduction to V = Q_jA, with ⟨V, Δ_jV⟩ the effective action (PBG (3.15); PRT1 (1.64)–(1.67), (1.103), Prop. 1.2 (1.110), (1.112)).
  - (2) The transfer of (a)–(f).
  - (3) The half-space Δ_j extension, through:
    - a local flux σ̃ := M̃*M̃ with M̃F = dH_jK_{x̄}F. The PRT1 (1.66) multiplier need not be analytic at p′ = 0 (φ = QΔ^{−1}Q*), so it is not used.
    - interior regularity, with Bochner's ‖∇v‖² = ‖dv‖² + ‖d*v‖² on Z^d;
    - large-scale Lipschitz decay at the wall: odd reflection for the gauge, then the co-closedness of σ̃F and the half-line Toeplitz bound ≥ γ₀;
    - the exterior decay r^{−d} and the wall flux, so abs(F) ≤ Cθ_B/max(s, 1). The boxes Q_N have N → ∞.
  - (4) The patching with [σ̃, χ_f].
  - (5) W_ms := max_jW_j: each layer is ≥ RM ≥ 2L wide, so at most one W_j is nontrivial at any site.
  - In l.6 the chain's norm is now ‖·‖_{W_ms}. The fork was told.
  - Step 4 of the plan used a product of weights; the max replaces it.
- **Items 18, 20, 25, and 5.** Done (LF ad21ea2d88c4, table f43d6febb394, with fork messages before and after the table edit):
  - item 18: W's exponent is now κ;
  - item 20: (K3) is restricted to joins through cells meeting Q_r(z), and (K4) runs cell by cell;
  - item 25: W is read in the units of the scale k − 1;
  - item 5: row 239 has Q′μ = −K(a).

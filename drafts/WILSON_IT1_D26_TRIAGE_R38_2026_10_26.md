# Round 38 triage (12:21, 26 Oct 2026, date)

Launcher: `verification\isolated_reviewer\run_app_review_cli.ps1 -Rev <folder>` (claude -p, claude-opus-5-5, effort high). The user: "Yes, run round 38 in the CLI on the repaired Pass 6 (f) (S-1, S-2) and the map l.972 m1–m4 edits." Packets built by `verification\isolated_reviewer\build_round38_review_packets_20261026.py` (two packets, each with the round-37 reviews as priors).

Reports (verification/isolated_reviewer/reviews/):
- `it1-rh-20261026-r5/review.md` — R-𝐇, map l.972 (re-review of m1–m4). Verdict: correct and sufficient; no fatal, no serious finding; m1–m5 closed; minors n1, n2; one cosmetic point.
- `it1-rc-p6f-20261026-r5/review.md` — RC_PROOF_PASS Pass 6 (f). Verdict: no fatal finding; S-1 closed, S-2 closed in substance; new serious N-1 (routine repair); minors m-1′–m-9′. Closure table: m-a, m-b mostly closed; m-c, m-d, m-e, m-h, m-i, m-j, m-k closed; m-f, m-g partly closed (now covered by N-1 and m-3′).

Every report was read in full; every finding was checked against the sources before the repair: PBG Theorem 3.4 (p.400: the operators "extend to configurations U′U for α₁ ≤ a₁ as analytic functions of A" with the inequalities of Theorems 3.1–3.3), p.406, Corollary 3.6 (p.408), Theorems 3.9–3.10 (pp.413, 415); RG1 p.257 (d_j as a shortest-tree length divided by M); CRE (2.34), p.261; V4 Lemma c2-plaquette-deviation, Lemma c2-local-gauge and the remark after it (any ε in place of ε₁).

V4 changed during the round (the user's edits; not touched here): the packet's provenance hash differed when the reviewer checked it, and the file is now 069a89058fd0. Pass 6 (f) now cites V4 by label only.

## Open after this round

- OPEN: the base points on Ω₁∖Ω₂ (rooted at k = 1, every k) — unchanged, D2.4(LPG′).
- OPEN: the gauge frame of σ_j (D2.2(4)(d)) — unchanged.
- Not re-reviewed: RC_PROOF_PASS Pass 6 (f) after N-1 and m-1′–m-9′, Pass 6 (d)'s cost sentence, Pass 5 (a), (d) wording; the map l.972 after n1, n2.

## it1-rc-p6f-20261026-r5 (Pass 6 (f))

**N-1 (confirmed).** "The term with 𝐃 = ∅, P = P″ = ∅ integrates to a second A″-free constant …, which also cancels in ⟨·⟩_t" is false: with e^{−⟨A″,w⟩} kept in the density, only the empty selection takes the value e^{½⟨w,Cw⟩}; the s-decoupled nonempty selections do not carry it, so Σ_ZH(Z) = Ξ + (e^{½⟨w,Cw⟩} − 1), an additive nonlocal correction that breaks RG2 (2.11)–(2.13).
*Repair (the reviewer's option (a); *The pieces (real base)* (i) rewritten).* e^{−⟨A″,w⟩} = Π_Δe^{W(Δ)}, W(Δ) := −Σ_{b∈Δ}⟨A″_b, w_b⟩ over the cubes of π₁, Mayer-interpolated in (2.1) with the potentials V(Y) as single-cube potentials; a W-host belongs to 𝐃, hence to Y₀. The empty selection is RG2's 1 and (2.5)–(2.13) are RG2's own. On a W-host every bond carries a cutoff, so |A″_b| ≤ (K+2)r (also in the variable y_b at complex points), and with |w| ≤ 2/r², |W(Δ)| ≤ 2(K+2)n_Δ/r. The W-host's Mayer factor ∫₀¹dτ ∂_τe^{τW(Δ)} is bounded by Cauchy on circles of radius r^{1/2} (e^{|τ′||W|} ≤ 2) by 2r^{−1/2}, and 3r^{−1/2} ≤ α₆e^{−(1+C_d)κ} pays the cube's entropy (2.29) and the unit of d₁ it adds (RG1 p.257), as single cubes are paid under R-L3. w's walks are s-decoupled with RG2's operators (Pass 4 (3)(e)'s localisation at s = 0 outside Z); W(Δ, σ) is bounded on the σ-polydisc by the tail bound with δ_*″. The factors e^{|⟨x,Re w⟩|}, e^{|⟨m_I,Im w⟩_P|} are gone from *The bound* (P ⊂ Y₀^{c*} carries no W); in the P″ estimate the W-factor's increment is ≤ 2ϵ_mr^{−1/2}. Option (b) (s-decoupling the empty selection) was not used: it depends on RG2 Sect. 1's convention at s ≡ 0.

**Minors applied.**
- m-1′: w = +tH_{DD}Σ_{|ω|>ρ₂}C_ωℓ; the modulus identity e^{½⟨μ,H_Rμ⟩}e^{−⟨x,H_Iμ⟩}, μ = m_I1_P, the second sum over the bonds within ρ_L of P; the Ad-direction point is moot (m-3′ drops the covariance identity).
- m-2′: (2.34) at n = 1 gives |∂U − 1| < α_{0,1}L^{−2}, so ‖U(∂p) − id‖_op ≤ c_hα_{0,1}L^{−2} (Lemma c2-plaquette-deviation's norm comparison): Lemma c2-local-gauge with ε := α_{0,1}L^{−2}/2 (the remark after it allows any ε), condition 3c_hL^{−2}s_bα_{0,1} ≤ r_G, μ̂_b = 3c_Gc_hL^{−2}s_bα_{0,1}. Ũ := e^{iA} on 𝔓_b and id elsewhere. Lemma regular-bounds' condition max(1, c_L)μ̂ < γ_L/4 cited; 𝖬 defined on 𝒪_c by (eq:nonlinear-average); α_c's invertibility by Lemma two-block and the Remark in (B2). The stencil rectangle in *The base and δH* has side 6L + 1, phases ≤ 3c_Gc_hL^{−2}(6L + 1)α_{0,1}.
- m-3′: the termwise covariance of the walk terms is not used. Ũ′ := Ũ^{v^{−1}} (v extended by the identity) equals U on 𝔓_b, so m^{loc}(U)(b) = m^{loc}(Ũ′)(b) by locality alone; (I1)–(I3) at Ũ′ by Lemma hessian-gauge-locality (conjugation by R_{v^{−1}} keeps spectra and entrywise row sums of the Ad-invariant norms); Lemma c2-uniform-chart at Ũ′ with the gauge v; Lemma c5-1-2 at Ũ′ with the unchanged A_e. The *Gauge covariance* sentence of *The local shift* is dropped.
- m-4′: δ_*″ := δ_*′/2 by per-cube accounting (RG2 p.16): a walk of |ω| steps meets ≤ 2⁴(C_L|ω|M₁/(LM) + 1) cubes of π₁, so the σ-factors cost ≤ e^{16κ₁}e^{δ_*′|ω|/4} under LM ≥ 64C_Lκ₁M₁/δ_*′ (e^{16κ₁} into K′), and the complex background (1 + O(ϵ_H))^{|ω|} ≤ e^{δ_*′|ω|/4}. |w| ≤ (1 + n_ρϵ_H/m_L)/r² ≤ 2/r² at complex points and on the σ-circle. U-range R_U := C_Lρ₂M₁ + ρ_L (step range C_LM₁); 𝒦₃, s_b = 2R_U + 1, w′ = ⌈R_U/(LM)⌉ updated.
- m-b (residual): the walk factors are PBG's local operators, extended analytically by PBG Theorem 3.4 and p.406 on the local sequences of Corollary 3.6; the 𝐉-part of δH enters as Neumann steps of size ≤ ϵ_H; the relative O(ϵ_H) per factor by Cauchy.
- m-5′: d₁(X′) ≤ d₁(Z) + N_e(2w′+1)⁴ by RG1 p.257's tree length. The count for fixed X′ runs over S = X′ ∖ Z ⊂ N(E): with ε := g₀^{1/(16(2w′+1)⁴)} and (ε/4)^{(2w′+1)⁴} reserved per enlarged cube, 1{S ⊂ N(E)}Π(ε/4)^{(2w′+1)⁴} ≤ (ε/4)^{|S|} and Σ_S(ε/4)^{|S|} ≤ e^{6ε(d₁(X′)+1)}, an o(1) change of κ. The per-cube cost is e^{O(κ)(2w′+1)⁴}g₀^{−1/16} ≤ g₀^{−1/8}; the P-share e^{−γ₂r²/48} ≤ g₀; on P″, 2βg₀^{−1/8} ≤ 2g₀^{3/8}; the P″-sum ≤ e^{3g₀^{3/8}|Y₀∩𝒦₃|}. Cluster products have domain ∪X′_i and the costs multiply.
- m-6′: e^θ − 1 ≤ 2βexp[(ϵ_mm_L′ + (4n_ρr²)^{−1})Σ_{b′∼b}|x_{b′}|²] (q ≤ βe^{q/β}), m_L′ := m_L + n_ρϵ_H + O(α₄); the potentials' increment in RG2's τ-form, Σ_{Y∋b}|τ(Y)||ΔV| = O(α₄g₀ϵ_mr/ε₁) + O(α₄ϵ_mr)Σ|x| ((2.18), (2.20), (1.43)); the O(g₀²r³) claim dropped; several P″-bonds by telescoping, cross terms O(ϵ_m²r²).
- Potentials bullet: the parenthetical "with |m^{loc}_b|_σ ≤ r/2" on Y₀ ∩ 𝒦₃ ∖ P″ dropped (not available at complex points; the majorant |m^{loc}(s)| ≤ O(K)r is what is used).
- m-7′: Pass 6 (d) now lists the absorbed small factors (W-hosts' 2r^{−1/2}, the determinant ratio, the Im-parts at P, the P″-sum) and says κ changes by o(1).
- m-8′: V4 cited by label in (f) (the Inputs list too).
- m-9′: "These are what remains of RG2's R₁–R₃" replaced: the δH factors are handled without (2.16); RG2's R₁–R₃ for the σ-dependence of the decoupled operators are still used, as in Pass 4 (3)(g).
- Inputs: RG1 p.257, PBG Theorem 3.4, p.406, Corollary 3.6, RG2 (1.43), (2.11)–(2.13), (2.18), p.16, R-L3 added.

## it1-rh-20261026-r5 (R-𝐇, map l.972)

Verdict correct and sufficient; m1–m5 closed. Minors verified and applied at map l.972:
- n1: for bonds of S_{j+1}^{(j)*} leaving Ω_{j+1} the conjugator is v(y_top(b₋)), the value at the centre of the top-level block of the region containing b± (the (j+1)-block on Ω_{j+1}; the j-block on Λ_j∩Ω_{j+1}ᶜ, where both data families have top level j).
- n2: at complex data |T_x − 1| ≤ e^s − 1 and |log T_x| ≤ −log(2 − e^s) ≤ s(1 + 2s) for s ≤ 1/4, so each level's inverse block averages contribute ≤ 2dε₂(1 + 4dε₂), the total phase is ≤ 4dε₂ + 8d²ε₂², and ‖R(u_L^{±1})‖ ≤ e^{8dε₂+16d²ε₂²} ≤ 2 for ε₂ ≤ (log 2)/(10d) (hand check at equality: e^{0.554+0.077} ≈ 1.88; −log(2 − e^{1/4}) ≈ 0.334 ≤ 0.375).
- Cosmetic (l.973 lists c₃ among C_H's arguments): left as is.

## Files changed

- RC_PROOF_PASS_2026_10_23.md: Pass 6 (f) (*The local shift*, *The pointwise bound at the real base*, *The pieces (real base)* (i), *The base and δH*, *The bound*, *The enlargement paid*, Inputs); Pass 5 (a) tail; Pass 5 (d) Localisation bullet; Pass 6 (d), (e).
- WILSON_IT1_D2_STEP_MAP_2026_10_22.md: l.972 (n1, n2), l.185 and l.188 (R-c status).
- READINGS_RECHECK_2026_10_23.md: row 28 (Round 38 entry); summary.
- SESSION_HANDOVER.md: round-38 entry.

Hashes after the repairs: Map 421d19c6b5fe, RC ef6bdfc94944, READINGS 3337c710fab4, V4 069a89058fd0 (the user's edits).

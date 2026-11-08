# LF Packet 1, Review 2: Triage

Review: verification\isolated_reviewer\reviews\lf-p1-20261104-r2\review.md (LF 2e90657e5938). LF after the repairs: bcd45850b90e, labels 5bb845acb6bc.

## Fatal

1. **Crossing bonds of PRT2 (2.122) read as constrained.** Accepted. The print was checked: PRT2 Lemma 2.4 (p.245, transcription p245_corrected.tex l.76) reads "We denote by Λ also a set of bonds b such that at least one of the end-points b₋, b₊ belongs to Λ … We put B = 0 outside Λ". (2.103)–(2.104) (p.241) are then exact as printed. Repair:
   - #0.1.15: the group is Bałaban's N_b := {ω : ω = 0 on Λ^c, Q′₁ω = 0 on Λ′} of (2.104). The tag name is kept for the downstream references. P_N = 1 − Π_m − 1_{Λ^c}, with Π_m the projection onto the block constants. Π_∂ and ∂_y are gone, and so is the false sentence about the narrower bond set.
   - #0.1.16–#0.1.17: the free branch of the gap. B↾_Λ is the restriction to the bonds with an endpoint in Λ, and B↾_{Λ^c} the restriction to those with both endpoints in Λ^c. The test functions t and t′ need only vanish on Λ^c: ⟨t, Δω⟩ = ⟨P_Nt, P_NΔω⟩ + ⟨t, v⟩. "Π_∂ commutes" becomes "1_{Λ^c} commutes", and u = P_Nu + c1_y on y.
   - #0.1.32: the constrained branch is removed. The claim is stated for N_F := {λ = 0 on F, Q′λ = 0 on C}, with the reduction to D vanishing on 𝒳 (#A.11.9), and the consequence on 𝒮 is drawn with ℓ = L on the crossing bonds.
   - #0.1.33: Ã := B only on the bonds with both endpoints in Λ^c. The bumps avoid the crossing bonds, so D = B there.
   - #0.1.37 and #0.1.37.1: the constrained alternatives and the joined-site step are removed.
   - #0.1.31 and #A.11.9: the crossing bonds are free in every use.
   - Downstream definitions now follow PRT2 Lemma 2.4:
     - the mass graph and 1_m use the bonds with both endpoints in Λ^c (#0.1.18, #0.1.20, #A.1);
     - t₃ is measured to the contacts of codimension ≥ 2 (#0.1.10, #0.1.18, #0.1.19, #0.1.27 summary, #A.10, (K6));
     - in (K1), ∂*A is constant on whole blocks.
   - **Open for packet 2:** #0.1.22 and #A.2–#A.5 still treat the crossing bonds as mass and the codimension-2 contacts as joined. They must be rewritten before p2 r1.

## Minor

2. **#A.9, complex backgrounds.** Accepted and repaired with a new paragraph, *At the complex backgrounds.*:
   - u_R(B_t) = e^{iηA′}U_re, with abs(ηA′) ≤ αℓ^{−1} and abs(η∇A′) ≤ αℓ^{−2} by VAR (190) (PBG's (3.37) form);
   - the per-block Poincaré bound, the conjugate test field ω̄₀ in the weighted bound, and the Green's-function step, where the remainder is put in divergence form plus an ℓ^{−2} potential;
   - covariance, ω′_t = Ad(g_t^{−1})ω̃′_t (PBG (3.33), Theorem 3.4), so the bootstrap needs only abs(ηω_t) ≤ ½, and it is written with a maximal T;
   - the second-order remainder of the representative, ≤ C(L, M)ε₁², by Cauchy's bound on abs(s) ≤ c/ε₁, which goes to #0.1.11.
3. **#A.11.9, "larger".** Moot: the sentence is removed.
4. **#A.11.10, exponent.** Accepted: the claim is now (1 + log L).
5. **#A.11.17, D off Ω_j.** Accepted. Q_jA is fixed off Ω_j through Q_i = Q^{(1)}Q_{i−1} (PBG (3.15)), by induction on i.
6. **Path family at m = 1.** Accepted for #A.11.14, with a sentence on loops of length ≤ C(d). Moot for #0.1.37.1, whose joined-site step is removed.
7. **#A.11.12, J.** Accepted: J(x′) := D(b₂) − D(b₁).
8. **#0.1.31 citations.** Accepted:
   - (2.123) (p.244) is cited for the bonds inside the blocks;
   - (2.125)–(2.127) (p.245) are cited for the bonds between blocks;
   - Q₁ = L^{−1}Q is cited to (2.125);
   - CMP98 (125) carries L^{−(d+1)}, checked on p.36.
9. **#A.9, ρ-length.** Accepted. An interlayer bond has length ℓ^{−1} of its finer endpoint, and the product rule puts ω₀ at the finer endpoint.

## Next

p1 r3 with #0.1.15–#0.1.17 added to the extracts, prior = the r2 review.
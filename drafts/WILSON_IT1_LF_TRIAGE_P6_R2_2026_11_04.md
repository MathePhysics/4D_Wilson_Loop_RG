# LF Packet 6, Review 2: Triage

Review: verification\isolated_reviewer\reviews\lf-p6-20261104-r2\review.md (LF bbab4389fda1, table 3d5b823a0a37). Verdict: "Not yet established as stated". There is no fatal item, one serious item, and six minors. r1's S1 and S2 are resolved. All r2 items are repaired. LF after the repairs: d3f763467c43 (labels d18d943c3b7d).

## Serious

1. **S1, #A.11.47 (6)(iv) with #A.11.28: the bounds of g_Z and f_Z read A_N^{(j)} on Ω_j^c, and (s1)–(s3) bound only the supremum of ω_H(B^{(j)}) there.** (s2) now bounds ∂ω_H(B^{(j)}) per block Y of each finer layer Λ_{j′}, j′ ≤ j − 1, in the units of Λ_{j′}.
   - The weighted bound of #A.9 with the weight e^{−δρ(Y, ·)} gives ‖∂ω_H(B^{(j)})‖²_Y ≤ C(d)Σ_{y‴}e^{−2δρ(Y, y‴)}‖H₀B^{(j)}‖²_{y‴}.
   - A block y‴ of Λ_i enters ‖·‖_{Y,j′} with dL^{(d−2)(i−j′)}s(y‴)², s(y‴) from (s1), and ρ(Y, y‴) ≥ (abs(i − j′) − 1)RM (PRT2 (2.2)).
   - Hence ‖∂ω_H(B^{(j)})‖_{Y,j′} ≤ C(L)δ^{−d/2}e^{−δ_ω max(j − 3 − j′, 0)RM}θ_B, with δ_ω := min(δ, δ₁)/4, and the same for A_N^{(j)}.

   (iv) now writes ⟨f_Z, λ′⟩ = ⟨A_N, ∂(λ̂ − λ̃)⟩ and bounds abs(∂(λ̂ − λ̃)) ≤ C(d)L^{j−j′}Σe^{−c(d)abs(· − y′)}abs(λ′(y′)) on Λ_{j′}. Cauchy–Schwarz per block gives C(d)L^{(2−d)(j−j′)}, and the L^{d(j−j′)} blocks per cube of side 1 give L^{2(j−j′)}. The sum over j′ is ≤ C(L) for δ_ωRM ≥ 2 log L + 1. (s3)'s last sentence cites the new bound.

## Minor

1. **n1.** (6)(iii)(α) now uses γ_P, the γ₀ of PRT1 Proposition 1.1, distinct from (1.67)'s γ₀.
2. **n2.** #A.11.30 now writes the check that H_jD − c_D vanishes within √d of Ω_j^c: 2√d − √((9d + 16)/16) ≥ √d for d ≥ 3.
3. **n3.** (3) now states the ℤ^d window, with V_f of finite support. Q_N has side 2N, and N is not the torus side.
4. **n4.** (iv) now cites the Combes–Thomas argument of (f) on N_V for ‖e^{−δρ_j}V_L‖ ≤ C(d)‖e^{−δρ_j}V_N‖.
5. **n5.** (6)(iii)(δ) now says that e^{−c(d)RM} absorbs the count C(d)RM^{d/2}, and that RM, chosen after L, absorbs C(L) where (v) uses the bound.
6. **n6.** (1) now says "no constraint on the scale-j bonds crossing into Λ_{j+1}". The crossing bonds at Λ_{j−1}/Λ_j carry REG p.81's constraints, which are among the finer ones.

## Packet 7 pre-check repair, applied with these

- #A.11.48: "There the bound" now reads "In the part beyond r₂/(2L), the bound", since the g_Z, f_Z clause now precedes it.

## Review 3

lf-p6-20261104-r3 on LF d3f763467c43 is clean: "Established as stated", with no fatal or serious item. It found three minors, all applied (LF e4e1964fcc07, labels 9b0ebfcd874b):
- m1: ‖·‖_{Y,j′} now runs over the bonds of Y, its crossing bonds, and the bonds at Λ₀.
- m2: c_D is supported within 4√d of Ω_j^c, and the kernel distance is RM − 4√d (#A.11.30, #A.11.32).
- m3: the Ω_j^c part of g_Z, with the test field ∂λ̂, is now written out.

## Review 4

lf-p6-20261104-r4 on LF e4e1964fcc07 is clean: "Established as stated", with no fatal or serious item. Packet 6 now has two consecutive clean passes (r3 and r4). Its two minors are applied (LF d298d5285ba5, labels 94b650007ab7):
- r4-m1, the count. Block by block, the count of ρ of #A.9 carries L^{d−1}: a face of a coarser block meets L^{d−1} blocks of the next finer layer at distance O(1). (s2) now reads Σ_{y″}e^{−δρ(y, y″)/4} ≤ C(d)L^{d−1}δ^{−d}, with the further passages to finer layers paid for δRM ≥ 8(d − 1)log L. The same point affects packets 5 and 7:
  - (e), #A.11.20: the blocks at the face of a coarser block are now counted by the cubes of side L, with their sources bounded per cube (the Morrey bounds of (b), ℳ).
  - (f), #A.11.22: the block-by-block factor L^{d−1} is paid beyond the crossing of a layer, for δRM ≥ 4(d − 1)log L. The condition on r₂ is now δr₂/L ≥ 4(d + 2)log L + C(d)(1 + log(1 + log L)).
  - (v), #A.11.48: the factor L^{d−1} enters at m ≥ r₂/(2L), and e^{−δr₂/(2L)} pays L^{2d+2}(1 + log L)^q.

  These are under review in lf-p7-20261104-r1.
- r4-m2, the commutators of (2), #A.11.32: they are now taken as in (e). The product rule reads f at the coarser endpoint, and [σ̃, f] acts on the curvatures. They are not taken as a kernel estimate of Δ_j.

## Next

lf-p7-20261104-r1 on LF d298d5285ba5 (labels 94b650007ab7).

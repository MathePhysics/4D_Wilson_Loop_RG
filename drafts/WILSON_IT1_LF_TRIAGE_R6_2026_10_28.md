# Large-Field and Cauchy Notes: Triage of the Sixth Review Round, LF Part and R-Δ^c (28 October 2026)

Four reviews of this round are triaged here: lf-profile-20261028-r2, lf-remainder-20261028-r1, lf-kernel-20261028-r1, and cauchy-rdc-20261028-r1. The Cauchy-note reviews of the same round assigned to the repair agent C are in `WILSON_IT1_CAUCHY_TRIAGE_R6_2026_10_28.md`. All repairs below were made by the integrator through Read and Edit; no review of them has been launched, by the instruction to start no new agents.

## Dispositions, Review lf-profile-20261028-r2 (§4(b), *The Profile.*)

Verdict: the profile is correct; nothing is fatal or serious. The six minor points, all applied:

- (1) (T-π) lacks ε₄ ≤ ¼a₃ for the kernel form at ε₃ := ε₄, and VAR's own ε₄ = 3B₀C₁B₃ε₁ ≤ a₄. Both are added to (T-π).
- (2) *The ratio.*: a_{j′}/a_j ≤ L·e^{(log L/RM)d}, with the prefactor L.
- (3) *The propagator.*: the π-weighted entries equal the propagator's on the finer side and are ≤ 1 on the coarser side; the phrase about the factor L^{3n} is replaced.
- (4) The bond and block convention at the layer interfaces is fixed, at the cost of a uniform factor L^{3−ε₀}.
- (5) The coarse-side restriction is stated in the Status clause and in the bullet's first sentence, and "older layers" is replaced.
- (6) The note's A′* is VAR's A′ − HD(A′), stated where N := δV/δA′ is used.

## Dispositions, Review lf-remainder-20261028-r1 (§4(c), *The Remainder.*)

Verdict: the head, the weighted bound, the bound on P, and the growth are correct; nothing is fatal or serious. The minor points, all applied:

- (1) (T-Λ) lists 4B₀c_KC_Nc_tot(1/128)ε₃ ≤ 1, C_Hc_tot(1/128)ε₃ ≤ ½, ε₃ ≤ ¼a₃, and the smallness of η‖ℋ‖.
- (2) The analyticity on complex P comes from the complex clause of VAR's Proposition 6 (p.295 l.49–p.296 l.2) with (103) at C₁′ = 4C₁.
- (3) C_ℋ := 6dB₀c_tot(1/128), with the factor 2 of the H₁ bound.
- (4) 𝔊's decay is PBG Theorem 3.13 (p.426), and the extra variational factor of (3.133) is stated.
- (5) The quadratic-form bound on P cites Cauchy's estimate.
- (6) (2.59) at α = 1/16 follows from α = 1/128, and 𝐁_k(Z) satisfies PRT2 (2.1)–(2.2) as in (b).
- (7) ε₃ := CC₁ε₁ is stated as an upper bound, ≥ ε₁, so the J-terms of the kernel form are covered.
- (8) The packet's notation C_H for C_ℋ: no change to the note.

## Dispositions, Review lf-kernel-20261028-r1 (§4(b), *The Kernel Form of VAR Proposition 4.*)

Verdict: the vertices, D, HD, 𝔇₂, and the chains are correct except for the decay budget. One serious point, accepted and repaired:

- (iii-h) The budget "at most 6δ₀/128 + 6δ₀/32 < ⅜δ₀ is spent" from the rate ½δ₀ does not account for the links whose rate is ¼δ₀, the bounds of (ii). Repair: each link has its own rate r_i (δ₀ for H, H*, (QGQ*)^{−1}, and ℜ after PBG p.423 l.39; ½δ₀ for (71) and (73); ¼δ₀ for (ii)); a ratio costs δ₀/32 of its own link's rate, so ρ := min_i(r_i − δ₀/32) ≥ 7δ₀/32; the intermediate sums, taken one at a time, cost δ₀/128 in all through the factor Π_ie^{−(δ₀/128)d_i} and give c_tot(1/128)⁵. So the chain decays at the rate ≥ 27δ₀/128 > ⅛δ₀. The reviewer's version with 5δ₀/128 in total, which gives 23δ₀/128, holds as well.

The minor points, all applied:

- (2) The source of ε₃ is stated per term: the local-size link itself in the first line of (88), the first part of (90), and the direct terms of (91)–(96), another link in the other terms, and also ε₁ through J in (85).
- (3) The local size is ≤ L² times the layer norms for the gradient vertices of (91)–(96).
- (4) 𝔇^{(1)} = 𝒱^{(1)}(A).
- (5) H is bounded by (3.133), not (3.132), with the rates δ₁ and ½δ₁ renamed δ₀ on PBG p.423 l.39.
- (6) m = 1 for δC_j/δA by (44) and (56).
- (7) r_v and M_v come from (44), (52)–(54), (72), the range argument of (59)–(62) (p.287), and locality. The side condition s ≤ ½r_v is dropped: for s ≥ ½r_v the direct bound (72) gives |f| ≤ M_v ≤ M_v(2s/r_v)^m, and the factor 2^m enters C_v.
- (8) Q and Q* are at the bound of a local average, and Δ_πH enters only through (89).
- (9) "and in (90)" is removed from the list of the local-size links D(A).
- (10) The variants of (91)–(96) that VAR sketches are chains of the same kinds.
- (11) A″ is renamed A^♯, which is not VAR's A″ of p.292.

## Dispositions, Review cauchy-rdc-20261028-r1 (Cauchy Note §5, R-Δ^c and Its Derivative Version)

Verdict: no fatal point. The uniform class bound with an E₀-proportional constant is Bałaban's in substance (RG I Lemma 4, p.280 l.24–32; RG I p.281 l.3–4; CRE p.279 l.43–44). Four serious points, all accepted. The reviewer's readings were checked on the transcriptions: CRE p.255 (2.6)–(2.7), p.261, p.263, p.280, p.283; RG I pp.276, 277, 280, 281, 284, 285, 286.

- (S1) The homogeneous form |irr(Δ)(U)| ≤ d·E₁^{true}·s(U)^{5−β} is false: irr(Δ) vanishes only to second order at U = 1, and the terms n = 2–4 of (I.3.34) are small through derivatives of B ((I.4.17)–(I.4.18)), not through powers of its amplitude. Repair: (5.1c), |irr(Δ)(U)| ≤ d·E₁(α)(L^{j−n})^{5−β}, uniform on the class, with the remark that Schwarz's lemma improves it at most quadratically in the background's size.
- (S2) The derivative version rests on (S1), counts L^{j−n} twice, needs a family holomorphic on the complex disc, and needs a₀ ≤ ½α. Repair: for a family holomorphic on |t| < R in the class, a₀ ≤ ½α_n, and R := (α_n − a₀)/s₁, the derivative is ≤ (2s₁/α_n)·d·E₁(α)(L^{j−n})^{5−β}. This is Bałaban's t_□ mechanism (CRE p.283 l.23–25, RG I p.280 l.47–49). The callers §10.5 and LF §4(d) (ii) already used this form; §5's *What it gives.* now uses it too.
- (S3) E₁′(α) = E₀·O((α_{1,n}/α_{3,j})^5) has the wrong numerator and grows like (n−j)^{5/2}; "E₁′(α) = E₁′·O(α^5/ε_n^5)" is false. Repair, in *The constant.*: the numerator is the background bound B₃O(1)Mα_{0,n} (RG I p.276 l.42–43); α_{3,j} := β_IL^{−2}α_{0,j}/(2B₃) (RG I p.280 l.6, l.16, p.277 l.54); α_{i,n}/α_{i,j} ≤ (1+β₀)²(n−j)^{1/2} by CRE (2.6)–(2.7); the growth is absorbed by L^{−β(n−j)} with C_β := (5/(2eβ log L))^{5/2}. The constants of the terms of orders 2–4 ((4.22)) and of the far domains ((3.48)) are included: C_α := C_β[C_r⁵ + (1+β₀)⁸C₄ + O(1)]. The Constants line is updated; §8.2's copy of the old C_α was sent to agent V.
- (S4) The class U^c_n(X, α₀, α₁) is undefined, and the transfer to RG I's single-scale space is asserted. Repair: the class is Bałaban's Ũ^c_k of CRE (2.34)–(2.39). The transfer is derived under the condition (N), that the near domain lies in one cube of the condition (ii) of CRE p.261, using (2.38)–(2.39) and (2.6)–(2.7) at n − m = 1. At the other near domains it is OPEN as (R-Δ^c-T), now on the Cauchy note's Open list.

The minor points, all applied:

- (5) 𝐀 is not the background; in Theorem 2's proof 𝐀 = 0 (CRE p.280 l.17–19).
- (6) The quotation from p.280 l.9–11 concerns the far domains of the complete analysis; it is no longer used as evidence.
- (7) The misquotes are corrected: |B| < O(1)L^jη, "e.g. |B|<α₁L^jη"; the circle variable σ and the Cauchy integral of 𝐄; the four-argument space of RG I p.277 l.34; α₃ a fraction of α₀. The (3.29) quotation is no longer used: the Ward–Takahashi identities are multilinear identities at B = 0 (RG I p.284 l.37).
- (8) The remainder carries E₀α₃^{−5}, and the □̃⁴ localisation (RG I p.280 l.44–47) is stated as Bałaban's.
- (9) The t_□ derivative is a derivative along a holomorphic family of complex configurations.
- (10) E₁^{true} is removed; the class constant is E₁(α) := C_αE₀, the name §8.2 and the LF note use.

The LF note's *The functions of the configurations.* (ii) quoted the misreading "the background enters only through its size in scale-j units". It now cites RG I Lemma 4, p.281 l.3–4, and (5.1c) with (R-Δ^c-T).

## Dispositions by the Repair Agents V and I

Agent V repaired four reviews of the round:

- lf-vfun-20261028-r1 (*The functions of the configurations.*).
  - S1, the current bound, which is false pointwise: repaired by the path in pairs (𝐔(s), 𝐉(s)) := (e^{−isεA}U^A, J(U^A) − sδ𝐉), ending at (Ũ, J′). The path that ends at (Ũ, J(Ũ)) doesn't work.
  - S2, the per-Y reduction: partly repaired. The walk telescoping and the analyticity in the operators are derived, and (W-δ) is open.
  - S3, the class bound for 𝐑: stated as the reading R-Δ^c with exponent 4 and R₁(α), open as a reading.
  - Minors 4–7, 9, and 10 are applied. Minor 8, β ≤ 1/8 against CRE p.261 l.42, is stated as open.
- lf-cweights-20261027-r1 (*The complementary-weight parts.*).
  - S1: *The Localised Pieces of 𝐂_k (open).*
  - S2: Bałaban's representation of d, in the Cauchy note's §8.6.
  - Minors 4–6 and 10 are applied. Minor 7, the χ(Λ)(V′_k) shell, is stated as open. Minor 3 was applied by the integrator through (W-θ).
- cauchy-s86-20261028-r2 (Cauchy §8.6).
  - S1, the deep V(Y): agent B's input, still open in ν_j.
  - S2: *The Own Differences of the V(Y).*
  - S3: C_ν = C_ν(j(C)), absorbed through j < 8n + j(C).
  - Minors 4–7 are applied. Minor 8, the deep threshold k_s/8, was applied by the integrator.
- cauchy-s87-20261028-r2 (Cauchy §8.4 and §8.7): all minors applied, with D^♭ carried through 𝒯, C_τ, C_S″, and (8.6).

Agent I repaired the accepted serious points forms S1 and align S1 of the earlier round, through VAR's twisted averaging Q_db of VAR (154)–(156), with Ξ² = 0, J = Q_db*ν, and E = E₀ + E_Ξ. Three pieces stay open as (6) of the LF note's (LF-A):
- the multiscale π-part of β;
- the twist term 2⟨B̃₂, ν_0⟩ where Λ meets an interface;
- the multiscale alignment (b̄).

Agent W's note `WILSON_IT1_WALK_FACTOR_DIFFERENCE_2026_10_28.md` shows that (W-δ) as printed is not well posed. It restates (W-δ) per walk term and reduces it to the open inequalities (Wδ-1)–(Wδ-3).

The LF note's Open Gaps keep their numbers. Items (8) and (9) are removed: (8) per agent R's report (its point P3), and (9) by agent C's volume-uniform right inverse in the Cauchy note's §9.4.

## Packets Prepared and Not Launched

By the instruction to start no new agents, the repair agents' review packets were written and not launched (all dated 20261028):

- lf-rs-r2, lf-wext-r2, lf-complex-r2, and lf-gen5d-r1 (agent R);
- cauchy-lift-r2, cauchy-pi-r3, cauchy-align-r3, and cauchy-act-r2 (agent C);
- lf-cre-room-r1, lf-deep-vy-r1, and lf-boundary-r3 (agent B);
- lf-vfun-r2, lf-roomc-r1, lf-cweights-r2, cauchy-s86-r3, cauchy-s87-r3, and cauchy-s82-r1 (agent V);
- lf-walk-r1 (agent W);
- lf-align-r2, lf-forms-r3, and lf-terms-e-r1 (agent I).

Several packets cite hashes from before the integrator's last edits, and their briefs tell the reviewer to report the hashes seen. The repairs of this file (the kernel-form budget and R-Δ^c) have no packets yet.

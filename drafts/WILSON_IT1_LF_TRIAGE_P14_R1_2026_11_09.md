# Packet 14 (Cauchy §10.1–§10.3), round 1, 9 Nov 2026

## Pre-check of cauchy-p14-20261109-r1 (full)

- **Whole packet read** (#C10.1.1–#C10.3.51-1) on 9 Nov 2026.
- **Citations checked against the corrected transcriptions:**
  - PBG: p.394 l.2 (Q′, from CMP 98 (78)–(80)) and l.9–11 ((3.21), R); p.396 ((3.35)–(3.37)); p.399 (Theorem 3.3); p.400 (Theorem 3.4), proved on pp.400–407 (G′ pp.400–402, the inverse p.403, R and P pp.403–404, Q_j p.406, G p.407 l.33–40); p.402 l.56 and p.407 l.36 (uniform limits of analytic terms); p.416 (Theorem 3.11's proof, G = G₀(I − R)^{−1} with R small); p.418 ((3.113)–(3.116)); p.421 ((3.127)–(3.130)); p.422 ((3.131)–(3.137), with l.40 on Δ_π^{(2)}); p.423 (Theorem 3.12); pp.425–426 ((3.148), (3.153)); p.428 ((3.156)).
  - CMP 98: p.019 ((11), (14), (15)); p.026 ((52)–(54), Proposition 2); pp.030–031 ((78)–(92)); p.032 ((97), (99)); pp.033–034 ((105), (106), (109)); p.036 (Proposition 3, (122)–(126)); (158)–(163).
  - VAR: p.281 l.2–4 and (21); p.290 (79); p.294 l.18.
  - RG I: p.261 ((1.5)); p.267 l.28–29 and l.38–39.
- **Repairs made in this pre-check** (Cauchy note):
  - #C10.1.3 pinned G₁ to PBG (3.148), (3.153). G₁ is defined by (3.128). It is now "PBG's G₁ of (3.128)", with Δ₁ = Δ_π − Δ_π^{(2)} (VAR (79), table #T11.25) the operator of the first two terms of (3.128) (PBG (3.134) and p.422 l.40), and ‖RD*A‖² = ⟨A, DRD*A⟩. The line was split: #C10.1.3-0 now holds J, R, Q′_m, and D̃^{(2)}. The Q′ pin is now p.394 l.2.
  - #C10.1.4-3 said that the regularity of CMP 98 (109) holds "at U^B and at Ũ_j by §9.2 and §10.3". Run A's background U^A_j (#C10.1.3-1) and the intermediate averages also need it. It now holds under 2C₀ε₁ ≤ c₃ at U^A_j, U^B, and Ũ_j, whose plaquettes are within 2C₀ε₁η²/a_j² (#C10.3.39). It also holds at their averages M^iU, i < n. There the plaquettes are within 4C₀ε₁L^{2i}η²/a_j² ≤ 4C₀ε₁L^{−2} ≤ C₀ε₁ (#C10.3.25-1, from Proposition 2 rescaled with η := L^{−i} and α₀′ := 2C₀ε₁L^{2i}η²/a_j² ≤ c₂).
  - #C10.3.3-9 pinned Theorem 3.4 to "pp.403–407". It is now "p.400, proved on pp.400–407". The analyticity of uniform limits was attributed to RG I p.261, which introduces the (𝐔, 𝐉) extension but does not argue it. It is now PBG p.402 l.56 and p.407 l.36.
  - The radius R := min(…) of #C10.3.42-1 clashed with PBG's projection R of #C10.1.3-0. It is renamed R_𝒟 at #C10.3.42-1, #C10.3.42-2, #C10.3.42-4, and #C10.3.51.
  - (B5)'s local gauge transformation was w, also the name of §10.3's w. It is renamed w_u (#C10.1.9-2, #C10.1.9-4).
  - Section pointers became tags: #C10.1.3 (#C10.1.4-1), #C10.1.6-1 (#C10.3.4-1), #C10.3.1 ((9.8) at scale j, #C9.7.1 and #C9.7.1-15), #C10.3.1-3 (#C10.3.35), #C10.3.1-6 (#C9.4.3, #C10.1.4-2), #C10.3.3-3 (#C10.4.98), #C10.3.4 (#C10.1.6-1, #C9.4.3-4), #C10.3.7-1 (#C10.1.6), #C10.3.8 and #C10.3.15 (#C9.4.3), #C10.3.10 (#C10.1.4-1), #C10.3.10-4 (#C10.1.5-1), #C10.3.14-1 and #C10.3.39 (#C9.3.3-1, #C9.7.1-15), and #C10.3.42-2 (#C10.3.14).
  - Restatements removed. #C10.3.1-1's abbreviations now read "stand for", and V = M^jŨ is stated as an equality. #C10.3.1-6 cites Q₁^{pl} = dM(U^B) of #C9.4.3. #C10.3.3 cites α_J = Mα₀ to table #T3.15. #C10.3.17 cites Q₁^{pl}(W) = dM(W) to #C3.2-1. #C10.1.3 writes Q_m = Q_m(U), PBG's object. #CK.1-25, #CK.1-27, and #CK.1-28 now list δ₂, Q₁^{pl}, Θ_n, c_w, α_J, c_Q, x_J, and α_* by name without ":=", add R_𝒟, and place α_* in §10.4. The header of BP_CMP98_ADJOINT_AVERAGING.md cites κ_W, W̄, and Q₁^{pl}(W) to #C10.3.17.
  - #CR.1-4 now lists PBG p.394 l.2, pp.400–407, and p.418.
- **Arithmetic re-derived:**
  - (B4) is the unrolled (91): Ū̄^n_U = D_{M^{n−1}U}∘⋯∘D_U = Ū̄^{n−1}_{MU}∘D_U.
  - In #C10.3.25-4, Σ_{i<n}L^{2(i−n)} ≤ L^{−2}/(1 − L^{−2}) ≤ (4/3)L^{−2}, and e^{2/3} < 2 under (AQ).
  - The BP deviations total 4x + 8dxL^{d−1} + 5xL^{d−1} ≤ (8d + 9)c_{av}L^{d+1}κ_W ≤ c_QL^{d+1}κ_W.
  - At (a), x ≤ 4c_{av}C₀ε₁ ≤ 1/(18(d + 1)L^{d−1}) ≤ 1/8.
- **Definition check:** 24 conflicts at first. The restatements above removed 14. The remaining 10 are allowed in the spec, each with its scope: local symbols (X, Y, U₁, U(t), ℓ), the note's single c_w against other notes' c_w, §10.3's w against #C6.2.18-5's weight, and the LF's multiscale analogues (H₀(U), f_y(U), δ𝐉).
- **Size:** 24.0k before and 24.5k after (≤ 25k). The growth is the Δ₁ definition and #C10.1.4-3's regularity list. No line is over 600 characters (the largest is 520). CR is 0, and there are no trailing spaces.
- **Spec:** specs\spec_p14_r1.json (Cauchy note e5112202b24f, LF d598eaace460). Its check gives 0 conflicts (10 allowed).
- **Order:** launch after 12b r12 completes, which is one referee at a time. BP_CMP98_ADJOINT_AVERAGING.md (3e32e122df37) is packet 14bp (WILSON_IT1_LF_TRIAGE_P14BP_R1_2026_11_09.md).
- **Messages:** the table fork was sent rows 594 and 596 (w_u, R_𝒟) and the new sub-tag #C10.1.3-0, and has applied them (table f571631e3200). It pointed out that Δ₁ is #T11.25, which #C10.1.3 now cites.

Written 2026-11-09 03:51.

## Verdict of cauchy-p14-20261109-r1 (full)

Not clean: one serious finding (S1) and eight minor ones (M1–M8). No fatal finding. The referee found (B1)–(B5), (10.2), the multiplier and current bounds, and the alignment (10.3) correct for the form as defined.

## Repairs

| Finding | Repair | Where |
|---|---|---|
| S1: the Gaussian form omits RG I's exponential gauge-fixing term 𝐆^{(2)} (RG I (1.5), (2.5)) | Re-derived from RG I (1.4)–(1.5) on {Q̃B = 0}: (10.1) now carries 𝐆^{(2)}_{M^mU}(B), the quadratic part of the exponential axial gauge fixing, which depends on the background only through the block field. #C10.1.3-0-1 gives the unit conversion B′ = ℓB to table #T10.14's definition. The pair form at #C10.3.3-2 has 𝐆^{(2)} at M^m𝐔. Its analyticity is at #C10.3.3-10, and its bound C_𝐆 := 4L^de^{δ₁dL} (the kernel is a sum of at most L^d terms of norm at most 4ℓ^{−2}ℓ^{−d}, with transports at most 2 under 2O(1)dLα₁ ≤ log 2) is at #C10.3.3-11. (10.3), #C10.3.42-3, #C10.4.122, and (10.6) carry the factor (1 + C_𝐆/B₀). The run difference vanishes, since both runs have the same blocks and contours on T_ℓ (#C10.4.1-4). | #C10.1.1, (10.1), #C10.1.3-0-1, #C10.3.3-2, #C10.3.3-10, #C10.3.3-11, #C10.3.42-3, (10.3), #C10.4.1-4, #C10.4.122, (10.6) |
| M1: the operator h of hC̃^{(2)} is dropped | (10.1) writes −2⟨H₁hC̃^{(2)}(B), J⟩, with h the operator of RG I p.267 l.18–23 and PBG's D̃^{(2)} = hC̃^{(2)} (RG I p.267 l.28–29) | #C10.1.3-0 |
| M2: (3.35) for Ũ_j uncited; ε₁ ≤ 1 and PBG's α₀, M conditions not listed | #C10.3.14 cites (3.35) for Ũ via #C9.8.4–#C9.8.4-4 at the scale a_j, under α₀^P ≤ α₀. #C10.3.51 lists #C10.3.39-1 (ε₁ ≤ 1) and α₀^P ≤ α₀, and the new #C10.3.51-0 lists the ε₁ statement and PBG's fixed α₀, α₁ conditions: O(1)M_Pα₀ small (p.396 l.32), 64c_Bα₁ ≤ 1, 8α₁ ≤ 1, 4α₁ ≤ r_B, and 2O(1)dLα₁ ≤ log 2 | #C10.3.14, #C10.3.51, #C10.3.51-0 |
| M3: complex extension of (QG₁Q*)^{−1} inferred, not printed; analyticity of D̃^{(2)} not mentioned | #C10.3.3-10 says that PBG prints the extensions for G′ and G only, and derives them for G₁ in the same way. It adds M^m𝐔 analytic with abs(M^m𝐔(M^mU₀)^{−1} − 1) < O(1)α₁ (CMP 98 Proposition 6, (164), p.043), and C̃^{(2)} (Proposition 7), h, and 𝐆^{(2)} analytic | #C10.3.3-10 |
| M4: the norm of the unit vector e not stated | e is a unit element of the Lie algebra. #C10.3.15-4 uses abs(X) ≤ N sup over abs(e) ≤ 1 of abs(⟨e, X⟩) for the normalised trace pairing, N the dimension of #T6.23's G ⊂ U(N). x_λ and B_λ carry the factor N | #C10.3.10-3, #C10.3.15-4, #C10.3.16 |
| M5: loose bond and plaquette count in #C10.3.14-7 | #C10.3.14-7 deleted. c_e := sup_y a_j^{−d}max(Σ_pη^de^{−½δ₁d(p,y)}, Σ_bη^de^{−½δ₁d(b,y)}) at #C10.3.14-6 absorbs both counts and the decay shift | #C10.3.14-6 |
| M6: "units of (3.14)" ambiguous for C_n^{(2)} | Checked against PBG (3.14): the note's normalisation was right; only the wording changed. C_n^{(2)}(U)[X, X] is the quadratic part of (1/(L^nη))C_n(U, L^nηX), that is, L^nη times PBG's C^{(2)} of p.421 l.12–14. #C10.1.4-1 now cites #C10.1.8-2 for it. The referee's suggested direction was incorrect | #C10.1.8-2, #C10.1.4-1 |
| M7: "i ≥ 1" | Now reads 1 ≤ i ≤ n − 1 | #C10.1.5 |
| M8a: the note's C₀ collides with CMP 98's C₀ | #C10.1.4-3: C₀ is the note's constant of (9.2), not CMP 98's C₀ of Proposition 1 | #C10.1.4-3 |
| M8b: RG I's (0.4) is not CMP 98 (15); the convention should be stated once | #C10.1.4–#C10.1.4-0-3 fix M = RG I (0.4), as CRE p.243 l.23–25 and RG I p.252 l.34–36 require (CMP 98 (15) lacks the lattice Euclidean symmetry). They also define 𝐆(y, x), the paths γ_{c,x}^{Γ,Γ′}, the holonomies h_{c,x}^{Γ,Γ′}, and Y_c, and cite CMP 98's results for (0.4) as RG I does (p.254 l.7–10; Proposition 2 at p.260 l.36 and p.265 l.17; (97) at p.270 l.32). #C10.1.4-1 defines Γ_{y,x}, the PRT1 (1.7) contour of the double bar | #C10.1.4–#C10.1.4-1 |

## Carrying M8b through

Every formula-level use of CMP 98 (14)–(15) was converted, each step re-derived:

- **Cauchy §9.** #C9.3.1-1 now uses convex combinations of the h_{c,x}^{Γ,Γ′}. #C9.3.1-3 pairs translates by #C10.1.4-0-1. #C9.3.5-2 cites dM(W) at #C9.8.1, and its parenthetical restating #C9.8.1–#C9.8.3 is deleted (the line was 612 characters). #C9.4.3-2 and #C9.4.5 use the paths. #C9.8.1–#C9.8.1-2 use the family-mean chains; their Γ̄-pieces cancel because Γ̄_{y+z,x+z} = Γ̄_{y,x} + z, so the weights w_{p,p′} of (9.11) are unchanged. #C9.8.7-1 cites #C11b.2-4. #C9.8.14-2 counts at most (d + 1)L bonds per path. #C9.8.18-7 uses the h_{c,x}^{Γ,Γ′}.
- **Cauchy §5, §7, §10, and §11b.** #C5.6-6, #C7.5-2, and #C10.3.20 are converted. #C10.4.9-2 has paths of at most (d + 1)L ≤ 3dL bonds. #C10.4.35-3–#C10.4.35-4 use the translation-covariant families. #C10.4.69-1 has θ_𝒜 with Γ̄. #C11b.2-3–#C11b.2-4 hold the multilevel fact M^j(Q_k^{s*}V) = Q^{s*}_{k−j}V, derived once by induction for (0.4) and cited from Cauchy #C9.8.7-1, LF #4.52-1-1.1-1, and BP_LFR2 #3.84-1.1.
- **BP adjoint file (BP_CMP98_ADJOINT_AVERAGING.md).** Re-derived for (0.4):
  - For fixed (x̂, Γ), the 2d bonds at y share the transport P_{b,Γ}, with N_b := Σ_{x̂}#{Γ ∋ b}/abs(𝐆(y, x̂)) ≤ L^d.
  - The entering-contour terms carry Ad(h)Ad(W(c))P_{b,Γ′}, since W(γ up to b) = hW(c)W(Γ′ up to b). So Ad(h) is a fourth replaced operator there, and each term changes by at most (1 + x)³ − 1 + x ≤ 5x.
  - The path weights total at most 1 + 2dL^{d−1}, and the outer term is at most 5x with weight L^{d−1}. In all, 10(d + 1)xL^{d−1}, so c_Q := 10(d + 1)c_{av} (was 9(d + 1)).
  - Loop area: A_L ≤ (d − 1)(d + 4)L²/8 ≤ dL² for d ≤ 5, from the step map's move count (#MOSTC.8–#MOSTC.11) with abs(n_ν) ≤ L/2. So c_{av} ≥ 4d and every dL² consumer stand.
  - (AQ) is stated through c_Q and is unchanged; #C10.3.24-4 now reads x ≤ 1/(20(d + 1)L^{d−1}).
- **LF.** #4.51, #4.52-1-1.1-1, #4.174, #4.454.4-2, #4.561.1 (split into #4.561.1-00 to stay under 600 characters), #4.597-1, and #5.21–#5.21-0.1 (the loop of h_{c,x}^{Γ,Γ′} has at most (d + 2)L ≤ (3d + 1)L bonds) are converted. #A.11.2 already used (0.4).
- **W-δ note.** #W10.5.45-16–#W10.5.45-18 and #W11.161-4.
- **Other BP files.** BP_LFR2_CHI_K_LAMBDA #3.84-1.1 now cites Cauchy #C11b.2-4. #3.85.1's sentence on CMP 98 (15)'s locality is deleted, now moot. BP_VAR_PROP4_KERNEL #4.36-0-3 is converted.
- **Not edited.** BP_LFR2_REPLACEMENT.md l.21 still says "CMP98 (15) (BP #3.84-1.1)"; this session may not edit that file. Its claim holds with #3.84-1.1 as re-pointed.

## Messages

- **Table fork** (04:56): the SHAs, the new tags (Cauchy #C10.1.4-0-1–#C10.1.4-0-3, #C10.1.3-0-1, #C10.3.51-0, #D.C_𝐆; LF #4.561.1-00), the deleted #C10.3.14-7, the stale rows (#T10.23, l.169, l.576, l.583, #T12.7-25 with c_Q, c_e, and h, l.628, x_λ and B_λ with N), and the #T11.24 normalisation note.

## SHAs after the repairs

Cauchy 646ef7ef1bb6, LF 31538d03f6ab, W-δ 07f9b653bf2f, BP_CMP98_ADJOINT_AVERAGING 9cf308a7efe7, BP_LFR2_CHI_K_LAMBDA 9f72d21b1c21, BP_VAR_PROP4_KERNEL cc86940158a1. CR 0, no trailing spaces, tags unique, and no touched line is over 600 characters.

## Next

- Packet 14 needs r2 (full) after its pre-check.
- 14bp r1 and 12b-bp r1 must be re-pre-checked, because the BP adjoint file is rewritten and BP_LFR2 is edited.

Repairs written 2026-11-09 04:56.

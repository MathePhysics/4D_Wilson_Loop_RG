# Non-Gaussianity Note: Triage and Pre-Check

Owner: BETA session. Note: `WILSON_IT1_NON_GAUSSIANITY_2026_11_11.md`.

## Status (2026-11-11 04:14)

- Note SHA 0487ff54209e, 40,437 characters, 7 sections, tags #NG.0–#NG7.7-2.
- No referee round yet; none launched (needs the user's go). A full round needs the 25k split: part a = header, §§1–4 (15.2k); part b1 = §§5–6 (13.9k); part b2 = §7 (11.3k), each with the rest as context.
- Open: (O1b), #NG.2-1. (O1a) is Proposition A (#NG7.1).

## Pre-check (03:11)

- Every line of the note re-read after the rewrite.
- Every cited tag resolves (129 tags) against: GL b55baaef58e9 (live, own), NV a23c5c204987, PF 3137f5cade3e, continuum note e11a4286a383, Cauchy b90f03322044, map ea2d3fdca669, table c571f2502afe, V4 0f859f2d3652 (snapshots in the scratchpad's snap folder).
- Table and map changed since the earlier snapshots (3e9dd1981ea0, 5c5203be2b03): diffs read; no cited row changed (#T1.2, #T3.27-0, #T3.33, #T4.52, #T10.2, #T12.14, #T12.16, #MOMST.76, #MOMST.82, #MD2.0.5.40).
- V4 changed (64c07217fa40 to 0f859f2d3652): V4 (H1) still reads "compact connected simple", and cor:main-leading-size still defines Lip_χ by ‖π_χ(g) − π_χ(h)‖_op ≤ Lip_χ‖g − h‖_op.
- No line over 600 characters.
- Each cited line read against the claim it supports:
  - #GL2.6, #GL2.7-2, #GL2.8-2, #GL4.6, #GL5.2-6, #GL5.5-1, #GL5.5-2, #MD2.0.5.40 (ι_{T,k} = Lι_{T,k+1}), #CP.13, #NK.4, #ND.2.3, #ND.5.3-0: Lemma E♯ and its size.
  - #NV.1–#NV.1-2.1, #NV.3, #NV.4-2–#NV.4-4, #NV.5-2–#NV.5-2.1, #NV.9, #GL9.8–#GL9.8-4, #ND.7.1: the stopping-scale form and λ^ng.
  - #PF4.2-0–#PF4.4-4, #PF4.5-2, #MOMST.74–#MOMST.84: the enlarged typical event. #MOMST.82 has Hol_{C^{(k)}}(M^kU) = Π_ie^{iE_{c_i}}T_{c_i}(U) with E_c ∈ 𝔤, so the telescoping bound needs no exponential (GL's 1.06 is not needed here).
  - #PF3.2-3–#PF3.2-9b, #T4.52, #GL6.5–#GL6.5-2: the near part on ℓ₀.
  - #GL9.1–#GL9.7-2, #GL7.1: levels, normalisations, families, §7's conditions.
  - #ND.5.4–#ND.5.4-2, #T12.14: ι^{ℓ₀} and ρ_k.

## Repairs made during the pre-check

- Symbol clashes with table rows, renamed:
  - R_n (#T12.7-29 and others: radii R_n) to 𝖱_n.
  - P_k (tube projection, bond counts P_k(C)) to 𝖯_k.
  - a_R (#T12.24-1-4) to 𝖺_𝖱.
  - n_R (#T4.29-6) to n(𝖱).
  - r_S (#T4.47, #T12.5) to 𝗋_S.
  - h_m (#T12.7) to 𝗁_𝗆.
  - ι in Lemma E♯ (#T12.35's RW1 ι := ι_{T,1}) to ι_{T,K′} written out.
  - ι_C to the existing ι^{ℓ₀}_C (#PF4.2-0-1, #GL8.6).
  - I_a to 𝖨_a.
  - Gaussian vector Φ (table Φ_ℓ(X), Φ^⋆) to 𝖷.
  - 1-form A (Wilson action A) to 𝖡.
  - F (NV's F_𝔇) to 𝖥.
  - Charge e (Euler's e in the same lines) to 𝗀.
  - Lattice Λ_a, side T, spacing a in §4 to 𝕋_ε, 𝖳, ε, as Λ_a clashed with Λ_{𝖨_a} and a with the index a.
  - M_C to 𝖬_C.
  - Directions ρ, σ in §4 (σ_C, σ_ng) to α ∉ {μ, ν}.
- New symbols, all free in table c571f2502afe: 𝔜, 𝔶_S, 𝔶_k, 𝔶^{ℓ₀}_S, c^G_k, c^F_k, D^F, B^♯_E, B^♯, B^♯_S, T_ng, ε_ng, 𝒱_ng, h^ng_C, σ_C, σ_ng, λ^ng, 𝖺_𝖱, 𝗋_S, 𝗋′_S, 𝖬_C, and the sans-serif diagram names.
- Proposition K(ii), Theorem P and Proposition R gained "Under #GL7.1's conditions for the five diagrams": #GL9.8 holds under §7's conditions, which include constants fixed after the family (L ≥ L₀(𝒞), #GL6.6).
- Theorem P: σ_ng := 3ḡ⁴ + limsup_Kσ_{𝖨₀}, with the order bound uniform in K, so that "let K → ∞" is valid.
- Near part (#NG5.5-3–#NG5.5-6) re-derived on ℓ₀ from #PF3.2-4–#PF3.2-6 with ℓ₀'s majorants 𝖬_a = Π_n(1 + ν_n) and N^{nr} of #PF3.2-9. On ℓ₀ there are no large-field components, and the local terms are constants, so N^{LF} and the δ̄_D terms are absent. GL's rate e^{−c_dP_{K′}/(2Λ̄)} is now cited, with its bound e^{−c_dr_{K′}}.
- ι^{ℓ₀}_C order (#NG5.5-10): the wrap term of #ND.5.4-2 is stated and bounded, with j(C) = j_q by #GL9.1-1.
- Lemma F: hypothesis 4t ≤ 𝖳 added for k = 3.
- #NG2.1-1 examples: "generalised free fields" dropped; the continuum case is stated with L² limits of Riemann sums.
- #NG.1-1: the conditional sentence replaced by "is open: it follows from (O1) by #NG6.3".

## Messages

- To the two-loops session, the PF and NV owner: sent 2026-11-11 (see below).
- To the table session: announced the new rows (list above), to be entered after their reply; no table edit by this session.
- From the two-loops session (03:2x), against PF 3137f5cade3e and NV a23c5c204987, each re-derived there:
  - #PF4.3-1 holds for every T, so ḡ⁸ at T_ng.
  - #BPA.6 is general in T, so #PF4.3-3 and #PF4.3-5 run with ε_ng.
  - T_ng ≤ (C_fsC_q + C_ℰC_q + 4)(log ḡ^{−2})^{4r+1}, and 18NT_ng ≤ p₀(g_{K′}) by 2p₀ > 8r + 1.
  - (2)(a): the majorant reading of #ND.5.4-2, with Q(∅) = 1, disjoint arcs, m_× ≤ 𝖬₀𝖬_ke^{N^×}.
  - (2)(b): on ℓ₀, N^×, N^{(0)} + N^{(k)} ≤ N^{nr}, with no N^{LF} and no δ̄_D.
  - Lemma E♯'s sums are confirmed; it is not taken into NV. The telescoping without 1.06 is agreed.
  - Each point matches #NG5.4–#NG5.5-11 as written. No change.
- Table session rows #T12.36–#T12.36-7 (table e92eb9c3e3c9) read against note 9464f27abd5c: they match.
- 04:15, to the table session: the §7 symbols announced (list under Proposition A), SHA requested after entry.
- 04:15, to session (4): #MD2.4.4.2's X(𝒢) omits the merged occurrences' members' domains that #MD2.3.4.46-2 and #MD2.4.12.19-2 include. The KP position count (#MD2.4.12.38-1, #MD2.4.12.51-4) needs the larger support. The hits-form pin is FV (5.17), not (5.11).

## Work on (O1), 2026-11-11 03:48 (note 124102a7911b → 9464f27abd5c)

- Gap found in the description of (O1b): 𝐏_{ℓ₀} is gauge invariant and restricts the plaquettes only, so it does not confine the holonomies around the torus cycles. At second order the fluctuations around a flat connection are twisted free fields, not the untwisted field of the old Lemma F.
- §4 was rewritten in place for a twist θ ∈ [0,1)⁴. Lemma F(a) is the old bound at θ = 0. Lemma F(b): Re Cov ≤ −(st)²/(1200𝖳⁴) for every θ, if d + t ≤ 𝖳/3, s ≤ 𝖳/2 and ε ≤ 𝖳/4. The proof uses the image sum of the twisted 1-D Green's function, whose real part is positive for |z| < 𝖳/2, and keeps one mode. Hence D^θ ≥ (st)²/(400𝖳⁴), and the witness's 3max(4t, s) < T_ph meets the hypotheses.
- #NG6.2-1–#NG6.2-3 and #NG.2-1 now state (O1b) with the twists.
- (O1a) routes:
  - Size: the insertion bound is linear Cauchy, ρ̃ = ρ/ᾱ (#MD2.0.3.30). A second-order Cauchy, with the linear term killed by global gauge invariance, would need q₀ > 2p₀ + 4r roughly. That is a new lower bound on q₀; not adopted.
  - Locality: translation covariance on ℓ₀ (RTR, #MD2.3.1.15, #MD2.3.4.4) and torus locality (#MD2.3.4.25) are in the map. Missing: a loop-locality (agreement) statement for the V-dependent insertions.
- (O1b) inputs still open: second-moment comparison of 𝐏_{ℓ₀} with the Gaussian around flat connections, and the flux covariance of the scale-K′ quadratic form against the fine twisted free field. A route for the action part: CRE Theorem 2 (2.43) on real fields along V₀e^{iλX}, plus per-polymer analyticity (2.27)(ii),(iv) for the cubic remainder (summable over scales by L^{−2(k−j)}), plus the gauge-invariant vanishing of the linear term (RG1 p.264 l.12–14). Not yet written.

## Proposition A, 2026-11-11 04:14 (note 9464f27abd5c → 0487ff54209e)

- New §7 (#NG7.1–#NG7.7-2): |Σ_𝖱n(𝖱)𝐄_{ℓ₀}[I_{K′}(𝖱; ℓ₀)]| = O(ḡ³(log ḡ^{−2})^{5r+1/2+4p₀}) uniformly in K, which gives (O1a).
- Route:
  - families of ≥ 2 members: elementary symmetric sums over distinct first traversals, 𝗇_C²e^{𝗇_C}/2;
  - one member: the gap transport is 𝗍_W^{−1} times the holonomy, error ‖Y_W‖h_C, so O(ḡ³ polylog) on 𝒱_ng plus ḡ⁸ off it;
  - large insertions (Mσ + 1 > 𝖣/4) cut by the reserve weight e^{νσ} of (ii-w);
  - Q({W}) localised to clusters with network within 𝖣/4 of supp W, using the reference gas's KP condition at a°/2 (FV Lemma 5.6 (5.17) with tilted activities) and the network bound a°(Γ) ≥ (ν/(64M))diam (#MD2.3.4.46-3);
  - agreement (#NG7.5) from contour locality, translation covariance and the τ-invariance of 𝐏_{ℓ₀};
  - corner and middle-cell totals common to 𝖱₁, 𝖱₂, 𝖱₄ (cells of the period Π, 𝖣 a multiple of Π), cancelled by the weights 1, 2, −3 (#NG1.3-1).
- Other lines changed: #NG.0-1 (FV added), #NG.1-1, #NG.2, #NG.2-1, #NG.2-2, the last sentence of #NG6.2, and #NG6.3. #NG6.3 now derives (O1) from (O1b) with Proposition A.
- Pre-check (04:14):
  - every new and changed line re-read;
  - 195 tags resolve against GL (live), NV a23c5c204987, PF 3137f5cade3e, continuum note e11a4286a383 (now also #NP.2), Cauchy b90f03322044, map ea2d3fdca669 and table e92eb9c3e3c9; no line over 600 characters;
  - the cited lines were read against each claim: #MD2.0.3.2, #MD2.0.3.5-2, #MD2.0.3.30-3, #MD2.0.3.32, #MD2.3.1.15, #MD2.3.3.19, #MD2.3.3.27–#MD2.3.3.28, #MD2.3.4.1–#MD2.3.4.6-3, #MD2.3.4.40-8, #MD2.3.4.46-1–#MD2.3.4.46-3, #MD2.3.4.49, #MD2.4.7.16, #MD2.4.12.5–#MD2.4.12.6, #MD2.4.12.51-4, #MD2.4.12.53, #MD2.4.13.4, #GL5.2-6, #ND.5.4–#ND.5.4-2, #NP.2 (with D2.7 closure 515f6d31c942's 15.8: the post-R term is of class D(k)), #PF4.2-0;
  - FV pp.224–226 read: Theorem 5.4 with (5.10)–(5.11), Remark 5.5, and Lemma 5.6 (5.17). The map's "FV (5.11)" for the hits-form bound is really (5.17); the note cites (5.17).
- Symbol checks:
  - new symbols, free in table e92eb9c3e3c9 and in the note: 𝖣, 𝗇_C, ν^w_n, ν^w, w_wr, 𝗍_W, 𝖧_W, 𝗓⁰_W, 𝗓_W, supp W, Q^𝖣(W), Σ′, 𝗒_C(p), 𝖽(p), p_v(r), 𝖹_c, 𝖲_v, 𝖾_C, and Proposition A;
  - rejected because of clashes: T_W (V4's transport, #T12.2-13), τ_c (a table row), 𝖠 (#T12.35's 𝖠_H), and m for the distance along a side (§7's member count m);
  - in §7 the product is written ∏, as Π is the period Π_{K′+1}.
- Map point, not a defect of this note: #MD2.4.4.2's X(𝒢) does not list the domains of merged occurrences' members, while #MD2.3.4.46-2's support includes them and #MD2.4.12.19-2 counts them in σ. §7 uses the latter support and σ only.

## For the user

- Route: the witness compares with abelian Gaussian charge models and their limits (#NG2.3). A 𝔤-valued Gaussian field with path-ordered holonomies is not covered.
- Referee rounds for GL, TL and NG need the user's go.
- (O1a) is proved (Proposition A). (O1b) is open, so (O1) is open.

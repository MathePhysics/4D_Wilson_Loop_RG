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
- (O1a) route: locality (translation covariance on ℓ₀, RTR, #MD2.3.1.15, #MD2.3.4.4, and torus locality #MD2.3.4.25), closed by Proposition A below. A size route is not needed.
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

## Table entry and symbol clashes, 2026-11-11 05:17 (note 0487ff54209e → 75f8dadd7bae)

- The table session entered the note (table f1dee8f86a8d, LABELS 51d297b89db1, rows #T12.36–#T12.36-8-4) after a clean narrow round and a clean full round, and listed letters reused within the note. Bookkeeping renames, no bound changed:
  - Lemma F's shift d → 𝗐; #NG4.2-3's local a, N, q, φ → η, 𝖭_ϑ, 𝗊, ψ; Lemma C's θ_j → ω_j; #NG5.2-2's m → i; #NG5.4-2's local t removed (the map's radius written out);
  - #NG5.5-5's 𝖬 → 𝖬_k, 𝖬₀; the weights 1, 2, −3 are n_S(𝖱) throughout (n(𝖱₁) = 8 stays for the five diagrams);
  - (O1)'s constant c → c_O; #NG3.3's factor c^{|𝔇|} → "a constant factor per loop"; products in §§1–6 written ∏ (Π is §7's period);
  - §7: ν_n → ν̄_n (with #ND.5.4's bound of ν_n bounding it), the traversal p → 𝗉, p_v(r) → 𝗉_v(ϱ), the ball B → 𝔹, the corner c → 𝔠, "a := a°" removed, #NG7.4-2's x → y with the complex sum z written out.
- Not renamed: τ (only §7), and the exponent constants "a c > 0 fixed before the coupling" of #NG5.5-6 and #NG7.7-1, which are local.
- #NG2.3 now states that 𝔜 does not exclude 𝔤-valued Gaussian fields, pointing to the NA note's #NA1.5.
- Pre-check: 196 tags resolve against GL, NV, PF, the continuum note, the Cauchy note, map 2e35d8c5c925 and table f1dee8f86a8d; no line over 600 characters.

## Non-abelian witness, 2026-11-11 05:15 (new note `WILSON_IT1_NONABELIAN_WITNESS_2026_11_11.md`, 0cd8e85b8756)

- §1 records the 𝔤-valued Gaussian computation (Lemmas NA1, NA2, Proposition NA3): 𝔜 = 𝗀²C₂D_G + O(𝗀⁴).
- §3 Lemma S, proved: for abelian Källén–Lehmann models the shape-term coupling is non-increasing in the scale (φ(x) = x³K₁ + 2x²K₂, φ′ = −x³K₀).
- §4: path ordering gives the 𝔤-valued covariant models the rate (C_A/4π²)(3/2 − b/(2a)) ≤ 3/2 against Yang–Mills's 11/6; the log coefficient is derived, the remainder (G1) open. §5 lists (G1)–(G3) and (Y1)–(Y4).

## Holonomy part and (O1c), 2026-11-11 06:42 (note 102563ef3e27 → bca2ecaab99d; NA 0cd8e85b8756 → 93118b233ccf; new work file `WILSON_IT1_NG_O1C_WORK_2026_11_11.md`, 13e424868b0c)

- Witness weights n_S = (1, −3, 3, −1) on 𝖱₁, …, 𝖱₄ and −1, +1 on the pairs (05:41); Lemma F bounds c^θ(3t) − c^θ(2t) ≥ s²t³/(112𝖳⁵) uniformly in θ.
- New NG §8: Lemma H (#NG8.2), proved, reduces (O1b) to (O1c) (#NG8.3) with |r_H| ≤ 512𝗅³ + 16ḡ⁸. #NG.1-1, #NG.2, #NG6.2 restated to point there; #NG6.2-1–#NG6.2-3 deleted; #NG4.2-4 split (#NG4.2-4.1).
- NA note: D^𝔤 := c₃ − c₂, d → d_𝔤, C₂(π); Proposition NA3 for the six diagrams; Lemma S re-proved for I₂ − I₃ (#NA3.3-3); #NA2.1 split (#NA2.1-1).
- Work file: Lemma FS (flux splitting), proved; §3 now proves, from PBG's cited bounds, D𝔊D^* = Π_{D ker Q} at flat backgrounds (#O1C.3-5.2) and |𝔣_r| ≤ C₇(s/t)²e^{−δ₂t/2} uniformly in the fine spacing (#O1C.3-9.1), via Lemma LR (Lawler–Limic Theorem 4.3.1, p.81; Corollary 4.3.3, p.84). One reading is inferred, not printed: the curl as a combination of PBG's ∇_U (#O1C.3-8.1). §4 Lemma IBP proved; §5 a map, not proved.
- Renames: transport 𝗀 → 𝗍_{[o,o_a]}, F_a → 𝖪_{a,b}, φ → Ψ_k, C_A(π) → C₂(π), the work file's Lemma S → Lemma FS, D_G → D^𝔤, PBG's 0-form derivative → ∂_U, PBG's current J → J_U.
- Pre-check: all #NG, #NA, #O1C, #MD, #B, #C, #T tags resolve against Cauchy 03ca5efd7b86, map 7e2a5cdf96e6, table bcc27399a0f8; no line over 600 characters.

## Soft sector, 2026-11-11 06:50 (note bca2ecaab99d → f0312af7f14b; work file 13e424868b0c → 49377b20fa4d)

- Work file §5: the Gaussian-level moduli density is ∝ ∏_{α>0}|α(θ)|^{−4} near central 4-tuples (#O1C.5-4–#O1C.5-4.2), so the soft core carries the mass (log-uniformly for SU(2), with a power if |Φ⁺| > rank). The old Łojasiewicz route (#O1C.5-5) is superseded.
- Lemma CC (#O1C.5-5), proved: for constant connections, X_{0,k} = Ad(e^{iktb_μ})X₀ and |𝖪_{0,3} − 𝖪_{0,2}| ≤ (13/2)t²‖[π_*(b_μ), π_*(X₀)]‖²_HS. The hard–soft cross term vanishes at order g² by cyclicity (#O1C.5-5.3). Open inputs (S1)–(S3) (#O1C.5-6).
- NG #NG.2-1 and #NG.2-2 updated in place to say this; tags resolve, no line over 600 characters.
- 06:54 (work file → 27c0445d5b46): #O1C.4-2.1, analyticity of 𝒜_{ℓ₀} on the interior of {χ_{K′}(T) = 1}, now cited: VAR Proposition 9 (p.309), CRE (2.25)–(2.31) (p.259–260), RG1 (1.11)–(1.18) (p.262–263). Still open in §4: the sizes in #O1C.4-5, including the 𝐄 + 𝐑 gradient term.

## Table fork's points, 2026-11-11 07:05 (note f0312af7f14b → 138f3a20b26c; NA 93118b233ccf → e32a4a271f9b; work file 27c0445d5b46 → ade8e144a827)

- Received from the table fork (information, re-derived here): NG and NA entered at table 0b81f0e4e31c, LABELS ab37b3c4f243.
- (1) #NA1.1-1, sign slips: re-derived. Σ_aT_aT_cT_a = C₂T_c + if_{ace}T_eT_a = C₂T_c − (i/2)f_{ace}[T_a, T_e] = C₂T_c + (1/2)f_{ace}f_{aeg}T_g, and f_{ace}f_{aeg} = −f_{cea}f_{gea} = −C_Aδ_{cg}. Repaired in place; the result C₂ − C_A/2 is unchanged.
- (2) NA letter clashes, bookkeeping: Π → ∏ (#NA1.2); path field b(s) → 𝔟(s) (#NA1.2-2, #NA1.3-2); a_C → ω_C (#NA1.4-1, #NA1.4-2); B(k²) → ϖ(k²) (#NA3.2, #NA3.2-1); c_k → c^ν_k in §3 (#NA3.3-1–#NA3.3-2); F_r → 𝖿_r (#NA3.3-2, #NA3.3-3); amplitudes a, b → 𝖺, 𝖻 (#NA.1(iii), #NA4.1, #NA4.2-1, #NA4.3, #NA5.1); order-𝗀⁴ term F → 𝒦₄ (#NA4.2-1, (G1)). F := dB and c_k of §1 are kept.
- (3) #NG.2-2: g_a → g_{K′}, the coupling of the density of 𝐏_{ℓ₀} (Cauchy's g_a, #CP.21; #NG5.4); λ > 0 named as the regulariser. Split into #NG.2-2 and #NG.2-2.1 (684 characters). Work file: g_a defined at its first use (#O1C.1-4), λ > 0 at #O1C.4-3, chosen in #O1C.5-2.
- (4) The work file is not tabled: it is a derivation in progress; it goes to the table only with a review round, which needs the user's go.
- Tags resolve, no line over 600 characters.
- 07:12 (note → bb33c4d3a62a; NA → 8018cad134b2; work file → d6494ab75055), after the fork's table b9d4d8aa47f9 marks. ϖ (clash with #NG5.1's ϖ) → ϱ_L; 𝖺, 𝖻 (clash with #NG5.3's 𝖺_𝖱) → 𝖼_T, 𝖼_L; α_0, β_0 of #NA4.1 (clash with RG I's α₀ and #T1.2's β₀) → 𝖼_δ, 𝖼_x. 𝔟 is kept (local by #NA.0; the BLL bond is elsewhere). g_a in #NG.2-2 and #O1C.1-4 now cites #T3.33. Bookkeeping, no mathematics changed.

## Lemma EG and the deterministic route, 2026-11-11 07:36 (work file d6494ab75055 → 9e9522910433; NG bb33c4d3a62a → 9836936f0811)

- Work file §4–§5 restructured: #O1C.4-4 is exact, so no conditional law of the fluctuations enters; (S1)–(S3) are replaced by (M) (deterministic on supp ζ), (★) and div v (#O1C.4-5). ζ := ϑ(A(U_{K′}(V))/(T_ngg_a²)) keeps V in the interior of {χ_{K′}(T) = 1} (#O1C.4-2). λ := N_s^{−2}ℓ^{−p_λ}, 0 < p_λ ≤ 2r + 1 (#O1C.5-2.1, split from #O1C.5-2 at 640 characters).
- New §6, proved from cited bounds: Lemma EG (#O1C.6–#O1C.6-4), the gradient of 𝐄_{K′} + 𝐑_{K′} along any w, by (5.1c) and the 𝐑 bound on the complex family e^{itw}V and Cauchy's estimate in t; the resolvent bound Δ(V) ≥ −C_HN_s⁴ε_ng/r_{0,K′} (#O1C.6-5–#O1C.6-5.3); the 𝐄 + 𝐑 term O(g_a²ℓ^{11r+p_λ+1/2−q₀}) = o(ḡ²) with no new condition, as q₀ > 13r + 2 (#O1C.6-6–#O1C.6-6.4); the ∇ζ term O(g_a²ℓ^cḡ⁸) (#O1C.6-7).
- Recheck of §6 before logging (every line re-derived): #O1C.6-3's 𝐑 sum Σ_jg_j^{κ₀} was asserted bounded without proof; now derived from Lemma 2.1(i) via #C4.2.1 (κ₀ ≥ 7 gives O(ḡ^{κ₀−2})). #O1C.6-7's support needed A > T_ngg_a² (𝒱_ng is A ≤ T_ngg_a², #NG5.4; ϑ′ = 0 on (−∞, 1]). Pointers #O1C.6-6.3 → #O1C.6-6.4 in #O1C.6-5, #O1C.6-6.2 → #O1C.6-6.4 in #O1C.0-2 and #O1C.5-2.1. Checked: D²a's integral form (cyclicity of tr on D²exp), the constants 192√2·72 < 2·10⁴ and 48√2, the exponents 11r + p_λ + 1/2 and 8r + p_λ + 1/2.
- NG #NG.2-2.1 now records that the 𝐄 + 𝐑 and cut-off terms are o(ḡ²).
- Tags resolve (O1C, NG, NA); no line over 600 characters.

## (M) and div v, 2026-11-11 08:14 (work file 9e9522910433 → 21f4c76ac38a; NG 9836936f0811 → c57c20c7e232)

- New work-file §7, proved from cited bounds: Lemma ML (#O1C.7–#O1C.7-2.2), c_λ at every flat background equals Σ_r(D^{θ_r} − 𝔣_r − 𝔩_r) exactly, with |𝔩_r| ≤ 10π²C_Vt_b²(s_b + 2)(t_b + 2)λ by the spectral measure of the block translation; Lemma CO (#O1C.7-3), coercivity ‖∇_μu‖ ≤ 4‖DHu‖ on ker d_c^*, by PRT1 (1.18)–(1.20) and lattice Stokes; Lemma VB (#O1C.7-4), by PBG (3.133) and Lemma LR.
- Lemma FA (#O1C.7-5), a flat W within 50N_s²ε + C_G(8N_s²ε)^{α_G} of V, by a tree gauge, plaquette moves and Łojasiewicz on G⁴ (Bierstone–Milman, IHÉS 67 (1988), Thm 6.4: to read). Lemma LV (#O1C.7-6), Lipschitz bound on c_λ from VAR Prop. 9 and (172)–(173). Together, (M) on all of supp ζ (#O1C.7-7). Lemma DV (#O1C.7-8): the div v term is O(g_a²ℓ^{17r+2p_λ+1/2}ḡ).
- Lemma LT (#O1C.7-9): the λ-term of (★) at flat backgrounds, with order O(g_a²ℓ^{7r+1−p_λ/2}), o(ḡ²) only for p_λ > 14r + 2, hence q₀ > 25r + 5/2 (#O1C.7-9.2).
- Repairs: #O1C.4-5 had (M) against the value of #O1C.1-4 (weights w_r) and (★) with |𝔢_α|; now the Schur normalisation (#O1C.4-5, G simple by V4 (H1)), (M) with d_𝔤 and (★) signed (#O1C.4-5.1–#O1C.4-5.2). #O1C.5-2, #O1C.5-2.1, #O1C.5-5.3, #O1C.5-6, #O1C.5-6.1, #O1C.0-2 rewritten; #O1C.0-3 new; #O1C.6-6.4 gives the general condition p_λ < q₀ − 11r − 1/2.
- Recheck before logging (every line of §7 re-derived): the block count (s_b + 1)(t_b + 1) → (s_b + 2)(t_b + 2), constant 40π² → 90π²; Lemma LV lacked VAR (7)'s regularity, now 4δ < ε₁; #O1C.7-8.1 used ‖e_{bγ}‖_∞ where ‖e_{bγ}‖_{ℓ²} = 1 is needed; tree origin placed off the six diagrams (#O1C.7-5.1); the plaquette-move step written out (#O1C.7-5.2–#O1C.7-5.2.1).
- NG #NG.2-1 now names (★) as the missing step (#NG.2-1.1 split off); #NG.2-2.2 records (M) and Lemma DV.
- Tags resolve (O1C, NG, NA); no line over 600 characters.

## For the user

- Route: Theorem N (#NG.1) is the result. 𝔜^sym compares with the Gaussian charge models of any covariance and their limits (#NG2.2), which contain the Wilson-loop functions of real Gaussian 1-forms; it does not test 𝔤-valued Gaussian fields with path-ordered holonomies (#NG2.3-1). The NA and NAG notes are abandoned (user, 12 Nov 2026).
- Referee rounds for GL, TL and NG need the user's go.
- (O1a) is proved (Proposition A). (O1b) reduces to (O1c) by Lemma H, and (O1c) is proved from cited bounds (work file Theorem E, #O1C.8, and #O1C.8-11.1). So (O1) holds and 𝔜(W) ≥ c_Oḡ²/2 > 0 (#NG6.3); the complex-data readings are printed or re-derived (#O1C.0-4).
- Approved by the user: (★) needs q₀ > 25r + 5/2 (#O1C.7-9.2), a lower bound beyond #T1.2's; sent to the table fork.

## Łojasiewicz citation read, 2026-11-11 11:04 (work file 21f4c76ac38a → ff5b5d2f82bb; NG c57c20c7e232 → 5463397a3ab5)

- The user supplied Bierstone–Milman, Publ. Math. IHÉS 67 (1988); project copy `Balaban\Balaban\Bierstone_Milman_1988_Semianalytic_and_subanalytic_sets_IHES67.pdf`. Theorem 6.4 (p.34): f, g: K → ℝ subanalytic with compact graphs, K in a real analytic manifold, f⁻¹(0) ⊂ g⁻¹(0) ⇒ |f| ≥ c|g|^r.
- #O1C.7-5.3 now cites it with f = Φ, g = d_Z; hypotheses checked in #O1C.7-5.3.1–#O1C.7-5.3.2 (G⁴ and Z semianalytic; Φ, d_Z extrema over compact sets, subanalytic by Remark 3.11(2), p.19, whose "as in (1)" argument was re-derived via Theorem 3.10, p.19). "To read" removed from #O1C.7-5, #O1C.7-7, #O1C.0-2 and NG #NG.2-2.2.

## (★) closed: Theorem E, 2026-11-11 12:05 (work file ff5b5d2f82bb → d150f8b5f371; NG 5463397a3ab5 → 1e2d96ec3bf8)

- Work file §8 (#O1C.8–#O1C.8-11.1) proves (★): sup_{supp ζ}|Σ_αF_α𝔢_α| ≤ C_E(ḡ²ℓ^{7r+1−p_λ/2} + ḡ^{2+β_*/2}ℓ^{c_E}) for 14r + 2 < p_λ < q₀ − 11r − 1/2. Route: strata of the commuting locus Z with Łojasiewicz on each stratum, power-scale pigeonhole (β_k = α_G(4ρ)^{−k}/2), slice lemma, coercivity, symmetry of B = e^{ic}W′ under twisted translations, translation identity for X_{0,k}, path identity for φ′, Lemma LT with T′_α.
- Representative repair in §6–§7: U_{K′}(e^{iB}V₁) = (e^{iη𝓗(B)}U_{K′}(V₁))^{w_B}, w_B = u₁ (VAR (124) p.296, p.297 l.1–2; REG (1.72) p.88); new #O1C.6-6.1.1, #O1C.7-6.1.1, #O1C.7-6.1.2, #O1C.7-6.2.0; L_Ξ, #O1C.6-6.2, C_Ξ and C_Δ adjusted; T′_α := Ad(S(o₀))^{−1}T_α in #O1C.7-1. Coarse-gauge invariance now cited from VAR (181) with Theorem 1 for group (4), replacing a wrong pointer to #C5.26-13.
- Status lines: #O1C.0-3 (proved), new #O1C.0-4 (inferred readings), #O1C.4-5.1, #O1C.5 (only #O1C.5-2.1 and Lemma CC are used or proved, the rest heuristic), #O1C.5-2, #O1C.5-2.1, #O1C.5-4, #O1C.5-5.3, #O1C.5-6, #O1C.5-6.1; #O1C.7-9.2 now takes ‖F‖ from #O1C.8-9.1 instead of the heuristic #O1C.5-3. #O1C.8-10 split into #O1C.8-10.1 (length); #O1C.8-11.1 re-pointed.
- NG: #NG.1-1 split, new #NG.1-2 (𝔜(W) > 0 follows), #NG.2 proved from cited bounds, #NG.2-1 rewritten (c_O, q₀ condition, inferred readings), #NG.2-2 and #NG.2-2.2 updated, new #NG.2-2.3 (the error term, Theorem E). NA unchanged: its "expected" concerns equality of the second moments to order ḡ², which is not claimed.
- Inferred, not printed: VAR Proposition 9 and REG (1.72) for complex data (#O1C.0-4).
- For approval: q₀ > 25r + 5/2 (#O1C.7-9.2), a lower bound beyond #T1.2's; #T1.2 is the table fork's row.
- Checks: no line over 600 characters, no duplicate tags, every #O1C, #NG, #C, #T, #MD, #NA and #PF reference resolves, in both files. No referee round run; NG rounds need the user's go.

## Readings checked, 2026-11-11 12:13 (work file d150f8b5f371 → c2b61e20b5b7; NG 1e2d96ec3bf8 → 62e7d9afff26)

- The user approved q₀ > 25r + 5/2. Sent to the table fork (yang mills 4 handover (2) ⑂ (2)) for #T1.2 or #T6.17, with the derivation pointers; their SHA awaited.
- VAR Proposition 9 for complex B: printed, not inferred. Domain: 𝓗 analytic on 𝔤^c-valued B satisfying (172) (VAR p.306 l.47–p.307 l.2); Proposition 6 for complex data (p.295 l.49–p.296 l.2); Proposition 4 for 𝔤^c-valued A′ (p.292 l.49); p.309 l.2–4 carries all bounds to the analytic 𝓗. Written in new #O1C.7-6.1.0 (split from #O1C.7-6.1 for length).
- REG (1.72) for complex data: not printed (REG is for G-valued data); re-derived in new #O1C.7-6.1.3–#O1C.7-6.1.4 from AVG (105)–(106) p.33, AVG's complex bounds (109) p.34, Proposition 4 p.38, (31) p.22. The real-only steps of REG (1.70) (unitarity of the factors, |e^{iY} − 1| ≤ |Y|) are replaced by e^{|Y|} − 1 and a Neumann series; the result |u₁ − 1| ≤ 12dε₂(1 + O(ε₂)) < 16dε₂ uses L ≥ 3 (#T1.3). #O1C.7-6.1.2 now identifies the complex w_B with (106) by the identity theorem (VAR p.307 l.2–5).
- A third inferred reading on the route, #O1C.3-8.1 (∇_U in PBG (3.42), (3.46)), is printed: PBG (3.39), p.397 l.4–7, and the curl p.391 l.14; |DA| ≤ 2|∇_UA|.
- #O1C.0-4 and NG #NG.2-1 updated. No line in the work file or NG note is now marked inferred, not printed. Checks rerun: lengths, tags, references clean.

## Nontrivial π, 2026-11-11 12:15 (work file c2b61e20b5b7 → ac60247ad186; NG 62e7d9afff26 → 7edc6c33d88c)

- Gap reported by the table fork, re-derived: #NG1.1 allowed the trivial π, for which every Wilson loop is 1, 𝔜 ≡ 0 and C₂(π) = 0, so c_O = 0. Repair: #NG1.1 takes π nontrivial; new #O1C.1-0 proves C₂(π) > 0 (π_*(T_α) Hermitian, #NG8.2-2, so n_πC₂(π) = Σ_α‖π_*(T_α)‖²_HS, zero iff π_* = 0 iff π trivial, G connected by V4 (H1), #NG5.1-2); #NG.2-1 states c_O > 0 with that pointer. NA uses the π of #NG1.1, so it inherits the repair.
- Peer note (yang mills 4 handover (4)): BP files consolidated; #BR.14-1 (VAR's "(106) [5]" is CMP98 (106)) agrees with #O1C.7-6.1.2. Their remarks on BETA's "not yet through review" lines and "is open" lines (#B10.93, #B10.202-1, #B10.212-1, #B10.221, #B10.221-1) are passed to the user.

## Table entries in, 2026-11-11 12:18 (work file ac60247ad186 → b00c3900a476; NG 7edc6c33d88c → bd5992f9feb6)

- Table 4fc638b90c78 (LABELS 695e1eeb30b2), checked by grep: #T1.2-0-1 lists q₀ > 25r + 5/2 for NG's (O1c); #T12.36-9-1 gives c_O and "c_O > 0 as π is nontrivial (#O1C.1-0)"; #T12.36 has π nontrivial. Bookkeeping: #O1C.0-3, #O1C.7-9.2 and #NG.2-1 now cite #T1.2-0-1 instead of calling the bound "beyond #T1.2". Checks clean.

## Self-review by the owner, 2026-11-11 12:41 to 14:06 (NG bd5992f9feb6 → d79a4c1b5fed; work file b00c3900a476 → 2d7f3fab6e26; GL b55baaef58e9 → e796a0245ace; BP_RG2_COMPLEX_B 58a21586e0df → 87218282e6a1)

- User: "Review it yourself don't launch independent reviewers, no packet splitting". Every line of NG and of the work file read and checked; every printed citation read in its source (PBG, PRT1, PRT2, RG1, CRE, REG, AVG, VAR, Lawler–Limic, Bierstone–Milman, FV). No referee round.
- Snapshots: none was taken before the first edits, against the standing rule. The exact pre-edit files were reconstructed from the session transcript and SHA-verified (NG bd5992f9feb6, work file b00c3900a476); they and the post-edit copies are in the session scratchpad's snap folder, with GL b55baaef58e9 and BP_RG2_COMPLEX_B 58a21586e0df.
- NG repairs:
  - #NG2.1: κ-form corners defined (𝒦(C), orientations (v_c, w_c), #GL1.1–#GL1.1-1); #NG2.1-1 split, new #NG2.1-2 (U(1) free fields; gauge independence by discrete Stokes).
  - #NG3.3: the normalisation changes named. #NG4.2-1, #NG4.2-4.1: lift offset t ≤ 𝗐 ≤ 𝖳 − t, so 0 < y_μ − x_μ < 𝖳, with 2t, 3t in range as 12t ≤ 𝖳.
  - #NG5.1: Lemma C for compact, connected, semisimple G; #NG5.1-1: det∘ϖ = 1 via e^{i𝔤} ⊃ a neighbourhood of 1 (#NG8.1) and connectedness.
  - #NG5.2-3: r_{K′}(C) = min(N_μ(C), s)/2 from GL's geometry; c^Z from #T12.16-0-3. Row pointers: #NG5.2-4 and #NG5.5-6 → #T4.52-0-2, #NG5.5-5 → #T4.52-0-1–#T4.52-0-2, #NG5.5-10 → #T12.14-0-3. #NG5.3-1: w₀ ≥ (1 + δ_LF)^{−1} ≥ 2/3.
  - #NG5.5-11: #PF4.3-2a's conditions with ε_ng derived (ε_ng ≤ ε_{K′} reads 18NT_ng ≤ p₀(g_{K′})², 2p₀ > 4r + 1).
  - #NG7.4-1 split into #NG7.4-1, #NG7.4-1.0, #NG7.4-1.1: tilted activities, FV (5.2), (5.10), (5.12), Lemma 5.6 (5.17) at γ = W, Ursell coefficients. #NG7.5-4: invariance under τ^{±1} written out. #NG7.7-1: the exponentials bounded explicitly.
  - #NG8.1: 𝔤 the Hermitian X with e^{isX} ∈ G for all s; δ_G's existence proved in new #NG8.1-0–#NG8.1-0.1 (𝔤^⊥, renamed from 𝔥 for #T4.29-0-9's 𝔥_A); ‖log g‖ ≤ 2‖g − 1‖. #NG8.1-3: Hermitian convention for π_* and its equivariance. #NG8.2-1.1: conjugation by 𝗍 ∈ G. #NG8.2-2: ‖π_*(X)‖ ≤ Lip_χ‖X‖ derived. #NG8.2-4: τ as in #NG7.5-3, #NG7.5-4 applied a times.
- Work-file repairs:
  - Title "(O1c): Derivation in Progress" → "(O1c): The Proof"; #O1C.0 rewritten, citations moved to new #O1C.0-0 (REG and AVG added).
  - #O1C.1-0: pointers #NG8.1-3 (Hermitian π_*), #NG8.1 and #NG5.1-1 (generation). #O1C.1-4: the conditional "value to expect" deleted, with its only input #O1C.1-2.
  - #O1C.2-3: gauge directions lie in ker D at flat U only (D∂_U = 0, #O1C.3-5). #O1C.2-4: the 2-form is F, not B.
  - #O1C.3, #O1C.3-1: t_b, s_b defined as the sides in step-K′ blocks, R_{K′} CRE's radius (#T2.23); t → t_b in §3, #O1C.4-5.1–#O1C.4-5.2, #O1C.6-6.1, #O1C.7, #O1C.7-7.1; (log ḡ^{−2})^r for (log ḡ^{−2})² in #O1C.3-9.1 and #O1C.4-5.2.
  - PBG readings corrected: #O1C.3-3 ((3.36); H's decay), #O1C.3-4 (the Gaussian measure and its generating source), #O1C.3-4.1 (Q at a flat U = 1^u), #O1C.3-5 (the current of (3.11)).
  - #O1C.3-6: the c_κ are constants. #O1C.3-6.1: Lawler–Limic read (∇_j p.17; the generator −2dε^{−2}L).
  - Factor √6 for the six components: #O1C.3-7.1, #O1C.3-9.1, #O1C.7-4.1, #O1C.7-4.3; C₇ := 2C₆e^{5δ₂}(8/(eδ₂))⁴ stated. #O1C.3-8, #O1C.3-8.2: |Q^*e_b| ≤ 1 and |QA(b)| ≤ √2‖A‖_{Δ̃(b)} replace c_Q.
  - §6: the data-move radius R_mv := r_{0,K′}/(8C_mvC_{Q*}) replaces R_{K′}, which is CRE's radius. #O1C.6-1 and #O1C.6-3: VAR citation and the identity at p.280. #O1C.6-5.2: the logarithm bound ‖log(1 + X)‖ ≤ 2‖X‖ and ‖u‖_∞. #O1C.6-5.3: 4r⁺_{0,K′}η² ≤ 1 (2 was not enough for #O1C.6-5.2). #O1C.6-6.4 → #T1.2-0-1.
  - #O1C.7-5.3–#O1C.7-5.3.2, new #O1C.7-5.3.3: Bierstone–Milman Theorem 6.4 read in the print (manifold ℝ^N; E₊ as the image of a subanalytic set); #O1C.7-5.3.0 cites through #O1C.7-5.3.3.
  - #O1C.7-5.5: the coarse gauge transformation from AVG (11) p.19 and p.24 l.9–12; VAR Theorem 1 replaces (181).
  - #O1C.7-6.1.2 split: new #O1C.7-6.1.2-1 (VAR's "(106) [5]" is AVG's (106); inferred, not printed) and #O1C.7-6.1.2-2. #O1C.7-6.1.4: the middle step bounded (e^y − 1 ≤ y + (4/7)y² for 0 ≤ y ≤ 1/8); new #O1C.7-6.1.5 (|u₁ − 1| < 16dε₂).
  - Clashes: δ₁ → δ_fl (#O1C.7-7, #O1C.7-7.1); the stratum index k → j and d_k → δ^Z_j in §8 and #O1C.5-6.1; ρ₁, ρ₂ → R_ω, R_u with C_sl := 6C_N′c′_G (#O1C.8-4.2, #O1C.8-4.3); the path γ → 𝓅 (#O1C.8-7.2–#O1C.8-7.3.1).
  - #O1C.8-5.1, #O1C.8-7.7: ∇A(B) ∈ C cited from #O1C.8-6.2. #O1C.8-7.1: the crossing range corrected (−4 − kt_b ≤ x_μ − o_μ ≤ −4). #O1C.8-7.5: |⟨T_α, Y⟩_A| ≤ 2c′_G‖Y‖ for complex Y, so C_Ξ̂ := 128c′_GC_ΓC_X (was 64).
- Status lines removed (user, 14:00: "Why does NG have status lines???"):
  - NG: the status in #NG.0 and the section #NG.2–#NG.2-3 deleted. Its facts stand once: c_O, its positivity and q₀ > 25r + 5/2 in #NG8.3; the proof in the work file. #NG.0-1 lists the work file (#O1C…), #NG.1-2 cites #O1C.8-11.1, #NG6.2 cites c_O of #NG8.3.
  - Work file: the section #O1C.0-1–#O1C.0-4 deleted; its facts stand at #O1C.3-9.1, #O1C.4-4, #O1C.7-6.1.0–#O1C.7-6.1.5, #O1C.7-9.2 and #O1C.8-11.1. §1 retitled "The Setting", as its expected value left with #O1C.1-4's heuristic. #O1C.4-3 cites #O1C.5-2.1 for λ.
  - GL #GL.0 and BP_RG2_COMPLEX_B's opening line: the status sentences deleted.
  - NA untouched (user: "If NA is not live ignore it!"). Its #NA2.1 still cites #O1C.1-4 for the removed heuristic.
- Bounds: none changed. c_O, the q₀ condition and every exponent stand; C_Ξ̂'s factor 2 enters later lines only through the symbol. No approval needed.
- Message sent at 14:03 to the table session (yang mills 4 handover (2) ⑂ (2)). It asks to re-point #T1.2-0-1 and #T12.36-9-1 from #NG.2-1 to #NG8.3, to re-point #T12.36-9-1's #NG.2 to #NG6.3, and to cite #T12.36-9-1-0-1's Δ(V), λ and g_{K′} from #O1C.4-3, #O1C.5-2.1 and #O1C.1-4. It also repeats that #T12.36-9 still restates the old §8 (e^{iX} ∈ G, a neighbourhood O). Reply awaited; at table eeadea088f70, #T12.36-9 was unchanged.
- Checks: o1c_check on NG and the work file finds no line over 600 characters, no duplicate tags and no missing references. CRLF line endings are preserved in the four edited notes.

## NA live: the Gaussian side, 2026-11-11 14:10 to 14:57 (owner, BETA session)

User, after NG: "Continue work on NA!!!! That is the only meaningful answer to what it means to be non-Gaussian!!!". SHAs are sha256sum prefixes (o1c_check hashes LF-normalised text).
- NG daa815feb399 → 450a7eb54bed (snapshot NG_daa815feb399.md):
  - #NG2.3-1 and #NG2.3-2 (the 𝔤-valued model; 𝔜 = 𝗀²C₂(c^G_3 − c^G_2) + O(𝗀⁴)) and the CRLF restore were logged by the table session's re-pointing (table 6115bfa3aeee).
  - #NG6.1-1: "W_ren_S(𝖱)" → "W_ren(𝖱; ε)". Reported by the table session in its message with table 6115bfa3aeee; checked against #NG5.3, where W_ren(𝖱; ε) = w₀e^{E^𝖱}𝖺_𝖱 + Λ_𝖱 for the single loop and E^𝖱 is a constant. Typo only.
- NA 2bbb27531cf9 → 51caf92af8fd (snapshot NA_2bbb27531cf9.md):
  - #NA.0 cites the work file; #NA.1 (iii) states the proved range; #NA.2 lists (G2), (G3).
  - #NA4.2 and #NA4.2-1: the chord heuristic is replaced by Lemmas M, NAG1–NAG3. The table's σ (#NA4.2) no longer occurs; new are 𝔞_× and K₄ (#NA4.2), and 𝒦₄ := −C₂C_AK₄/2 (#NA4.2-1).
  - #NA4.3: the rate with Theorem NAG4's error. #NA4.3-1 (the Feynman-gauge 5/6 aside, not derived) is deleted.
  - §5: the (G1) bullet is deleted; (G2) points at (R1), #NAG5.4.
- The work file WILSON_IT1_NA_GAUSSIAN_RG_WORK_2026_11_11.md was created and rewritten, 03ae741fd8c0 → be9cf86ba2fc (snapshot NAG_03ae741fd8c0.md). It moves to ℝ⁴, which removes the torus corrections. Proved:
  - Lemma M: 𝔞_× = ∫σġ = (3𝖼_T − 𝖼_L)/(8π²), by scaling.
  - Lemma NAG1: the 𝗀-expansion with |R| ≤ c(𝗀P/ε)⁶.
  - Lemma NAG2: Σn_SQ = −2𝖼_TD^F_∞ + O(η^N).
  - #NAG2.3: the crossing identity J(a, b) + J(b, a) = ∫𝔴_ab̄ − 2𝒩.
  - Lemma NAG3: Σn_SJ_× = −2𝔞_×𝖼_TD^F_∞ln(1/η) + K₄ + O(η), via the exact log-derivative in η, with corners and nested chords removed by n_S.
  - Theorem NAG4: 𝔄_Δ = C_A𝔞_×/𝖼_T + O(L^Δη + 𝗀^{−2}(L^Δη)^N + 𝗀²η^{−6}).
  - §§3–5: the heat flow, Duhamel and the charge flow. The normalisation and the final stage are now proved from Lemmas NAG1 and NAG2 (#NAG5.2–#NAG5.3-1), and (R1) is stated precisely (#NAG5.4).
  - Repaired while rewriting: (R1)'s old form "o(𝗀⁴) per unit t" would fail if the Gaussian charge has a two-loop term. It now asks for E = O(𝗀_{t_λ}⁴) with E/𝗀⁴ slowly varying.
- Open: (R1) = (G2), the leading-log regime; (R2) = (G3). Symbols local to the work file; 𝔞_× is distinct from the table's 𝔞̄.
- Checks: no line over 600 characters, no duplicate tags and no missing references in NG, NA and the work file; CRLF in all three. No bounds outside NA/NAG changed. No approval needed.

## NA live: the polymer gas of chords, 2026-11-11 15:00 to 15:41 (owner, BETA session)

- NAG be9cf86ba2fc → 010635e4b87e (snapshots NAG_65b837a36044.md, the first draft of §6, and the pre-§6 state = its first 79 lines). New §6:
  - #NAG6.1–#NAG6.1-2: grid with corners in hℤ (s, t ∈ uL^{−q}ℕ), grid chord sets, W_k → W.
  - #NAG6.2: the colour factor factorises over crossing components (gap words are invariant, hence scalars by Schur).
  - #NAG6.3: W_k is a hard-core polymer gas (FV Def. 5.2, p.221).
  - #NAG6.4: crossing sums ≤ C_×𝔏, 𝔏 = 1 + ln(P/η).
  - Lemma NAG5: KP via FV Thms 5.4 (p.224) and 5.8 (p.228), for 𝗀²𝔏 < δ₀; limit by Montel.
  - Lemma NAG6: |Σn_Slog W| ≤ C_G𝗀², the side and corner clusters cancelling under n_S.
  - Lemma NAG7: 𝔶_S = 𝗀²G₁ + 𝗀⁴G₂ + O(𝗀⁶𝔏²), by Cauchy.
  - Theorem NAG8: the rate with error O(L^Δη + 𝗀^{−2}(L^Δη)^N + 𝗀²𝔏²).
- Repairs before the final text, made in the first draft:
  - the endpoint-meeting term was 2c_CPh/η², not 2c_Ch/η;
  - the factor e³ in the (C)-bound is e⁴;
  - the log was named Λ, which clashed with #NAG2.4-4's wedge, and is now 𝔏;
  - the continuum limit was done term by term without a dominating bound, and is replaced by the grid estimates with Montel;
  - the crossing count is 2ℓ/h, not 4min(ℓ, ℓ₀)/h.
- NA 51caf92af8fd → 661d26fe6630 (snapshot NA_51caf92af8fd.md): #NA.1 (iii), #NA4.3 and (G2) cite Theorem NAG8; new #NA4.3-1 states the method.
- Open: (R1) = (G2), now only the regime where 𝗀²ln²(λ/ε) does not tend to 0 (#NAG.0-2). (R2) = (G3) unchanged.
- Checks: o1c_check on NAG and NA (no long lines, no duplicate or missing tags), CRLF kept. No approval needed.

## NA live: the scale derivative, 2026-11-11 15:45 to 16:33 (owner, BETA session)

- NAG 010635e4b87e → e24b3a8b5b6d (LF-normalised SHA of the o1c check; snapshot NAG_010635e4b87e.md). Theorem NAG8 (#NAG6.9–#NAG6.9-2) is deleted and superseded by the new §7:
  - Lemma NAG8 (#NAG7.1): the Penrose tree-graph bound |φ| ≤ t(g)/m!, proved inline via the least-weight spanning tree (Kruskal), whose fibres are Boolean intervals [𝒯, 𝒯 ∪ R(𝒯)].
  - Lemma NAG9 (#NAG7.2): the rooted-tree identity 𝔗 = exp(ΣAu𝔗) and the bounds 𝔗 ≤ e^a, 𝔗^♮ ≤ e^ab, with a marked vertex.
  - #NAG7.3: a two-cutoff gas with activities z on 𝒢_{η′} and z_δ on 𝒢_η − 𝒢_{η′}; its limit k → ∞ is taken by the segment formula for log, without Montel.
  - Lemma NAG10 (#NAG7.4): step bounds with the moment ratio max(1, ℓ/ℓ₀), at most C_s𝔏, and a far step at most C_sℓ₀/r₀ with no logarithm.
  - Lemma NAG11 (#NAG7.5): |∂_{z_δ}G| ≤ C_∂(ϑΔ ln L + (η′/r₀)^N) on the polydisc ϑ < δ₂/𝔏. The proof carries the moment along the tree path from the marked cutoff chord to the long chord, so the last step costs no logarithm.
  - Theorem NAG12 (#NAG7.6): the rate with error O(L^Δη + 𝗀^{−2}(L^Δη)^N + 𝗀²𝔏).
- NAG #NAG.0-1 and #NAG.0-2 updated: the proved regime is 𝗀²ln(1/η) → 0, and the open part of (R1) is 𝗀²ln(λ/ε) not tending to 0.
- NA 661d26fe6630 → f0e3e8e5353e (snapshot NA_661d26fe6630.md): (iii), #NA4.3, #NA4.3-1 and (G2) now cite Theorem NAG12 and its range.
- Open: (R1) = (G2) in the leading-logarithm regime 𝗀²ln(λ/ε) ≍ 1. (R2) = (G3) unchanged.
- Checks: o1c_check on NAG and NA, CRLF kept (NAG 136 lines, NA 68 lines). No approval needed.

## NA live: the Callan–Symanzik reduction, 2026-11-11 16:55 to 17:45 (owner, BETA session)

- NAG e8fff838b5c9 → d4a6e3c13078 (snapshot NAG_e8fff838b5c9.md). New §8:
  - Lemma NAG13 (#NAG8.1–#NAG8.1-4): the exact equation η∂_η𝔶 + (κ/2)𝗀³∂_𝗀𝔶 = r, κ = C_A𝔞_×, where r = Σn_S𝔫 − Re Σn_S𝔼𝓡/W and Σn_S𝔫 = O_N(𝗀²η^N). The proof is §3's heat-flow expansion applied to W, plus the splitting of #NAG4.3.
  - Lemma NAG14 (#NAG8.2–#NAG8.2-3): along characteristics, |𝔄_Δ − (F̂(τ_*, v + κΔ′) − F̂(τ_*, v))/Δ′| ≤ sup|ρ| on [τ, τ′] + κ∫sup_θ|∂_uρ|, with ρ = −C₂Dr/𝔶² and v = 𝗀_{t_λ}^{−2}.
  - #NAG8.2-4–#NAG8.2-5: the coarse end, at cutoff 1/M by Lemma NAG7, is κ/𝖼_T + O_N(M^{−N}) + O(𝔏_M²𝗀_{t_λ}²).
- #NAG.0-2 now states (R1) as that bound on ρ; (R2) moved to #NAG.0-3 (line length). #NAG5.4 no longer states an open bound of its own; it points to the same normalised remainder. #NAG5.4-1 is deleted: it was a consequence of the deleted formulation.
- NA f0e3e8e5353e → 424d3115a705 (snapshot NA_f0e3e8e5353e.md): (G2) cites Lemmas NAG13 and NAG14 instead of #NAG5.4.
- Open: (R1) needs a bound on r with no leading logarithm on 𝒮, where 𝗀²𝔏 is not small; Lemmas NAG5 and NAG11 do not reach it. (R2) = (G3) unchanged.
- Checks: o1c_check on NAG and NA, CRLF kept (NAG 150 lines, NA 68 lines). No approval needed.

## 2026-11-11 19:50 GMT: NAG §9, multiscale expansion (first part)
- NAG d4a6e3c13078 → 6d1e68c8f49c (snapshots NAG_d4a6e3c13078.md, NAG_7f734def9a8b.md, NAG_a021de2b7ea0.md).
- New §9. Lemma NAG15 (#NAG9.1–#NAG9.1-5): exact chord form of 𝔼𝓡^{(η)}, from Σ_eT^eXT^e = (C₂ − kC_A/2)X − Σ_pairs X_{c₁c₂}; contained chords cancel because ad_e is a derivation and Σ_bT^b ⊗ T^b is invariant. This removes the large-field split of §4.
- Lemma NAG16 and #NAG9.2-1–#NAG9.2-6: peeling in order of increasing length (root C₂, child −C_A/2, and for n ≥ 2 crossing chords kept 1 or removed −(C₂ − nC_A/2)), and W_k as an FV polymer gas whose polymers are link-connected histories. Compatibility means distinct endpoints, and no chord of one polymer crosses an R-chord of the other while in its current set. Kept chords of distinct polymers do not cross, so #NAG6.2 factorises c.
- Dead route: expanding the pair part into its 2n(n − 1) virtual-line terms (first draft of #NAG9.2) is not absolutely summable when 𝗀²𝔏 ≍ 1. With k chords whose letters lie near one point, chords crossing all of them carry ~2k² options each, giving e^{2k²𝗀²t} against e^{−kt}. Replaced in place by the R-chord form, whose weights are linear in n.
- Open (#NAG.0-2a): convergence of the #NAG9.2 gas for 𝗀²𝔏 not small, with per-chord charge ≤ C·running charge, then r without a leading logarithm. Needs approval (#NAG.0-2b): the bound needs ln(𝗀^{−2}𝗀_{t_λ}²) ≤ c𝗀_{t_λ}^{−2} besides 𝗀_{t_λ} → 0 (inferred from the two-loop drift, not proved necessary).
- BFWL 0f0d3401bffd → ba8a3b36f418 (snapshot BFWL_0f0d3401bffd.md): #B2.2.274-1 cites LF #3.17–#3.18 and (RS) #3.43–#3.99-1 instead of #3.17–#3.35, on the 4th handover session's report, checked against LF 697c65ec6aa9 (#3.35 ends the device; (RS) is #3.43; #3.53-1 covers V4's step-1 uses). Re-pointing only.
- Checks: o1c_check on NAG (168 lines, CRLF 168), no line > 600, no duplicate tags or missing refs; BFWL LF kept.

## 2026-11-11 20:46 GMT: NAG, (H_c) withdrawn; Lemma NAG14 with an autonomous speed
- NAG 947824f65884 → d16d43ed381b (snapshot NAG_pre14gen.md).
- (H_c) is withdrawn; there is no approval request. At fixed λ and M, 𝗀^{−2} − 𝗀_{t_λ}^{−2} = κt_λ → ∞ as ε → 0. So ln(u/v) ≤ cv along a sequence forces v → ∞: if v ≤ V on a subsequence, then u ≤ Ve^{cV}. A result under (H_c) therefore misses exactly the (G2) sequences, those with a non-vanishing charge at a fixed scale. #NAG.0-2b now states this proof; the "inferred" sentence is deleted.
- Dead route: a global KP majorant whose running charge Z′ = κZ²(1 + c_ZZ) uses a crude two-loop constant. Its charge diverges once (c_Z/κ)ln(u/v) is of order v, which is the (H_c) regime.
- Lemma NAG14 is repaired in place (#NAG8.2-1–#NAG8.2-3). It now takes an arbitrary continuous β with |β| ≤ κ/2 and the autonomous characteristics U′ = −(κ + β(U)). The two curves are time translates of each other, so no ∂_u-derivative appears. The bound is ∫|E| along the two curves, with E := ρ − β∂_uF̂. #NAG8.2-4–#NAG8.2-5 now work on [V₀, V₁] and add the error O(sup|β|).
- #NAG.0-2 now states (R1) in this form, in the regime η → 0 with g_W(λ) → 0, uniformly in 𝗀. #NAG.0-2a gives E = −(C₂D/𝔶̂²)(r̂ − β∂_u𝔶̂), with ∂_u𝔶̂ = −z Re Σn_S⟪|p|⟫/W and the insertion Σ_c((C_A/2)a(c) − β) + Π (Lemma NAG15).
- Checks: o1c_check on NAG (168 lines, CRLF 168), no line > 600, no duplicate tags or missing refs.

## 2026-11-12 02:05 GMT: NAG §10 completed (Lemmas NAG26–NAG31, Theorem NAG32); NA (G2) updated
- NAG c298c5ef5f2e (snapshot NAG_pre_NAG26.md) → 224097e22919 → a76bee1186eb (snapshot NAG_pre_split0.md). New #NAG10.14 (Lemma NAG26, Lipschitz bounds by the Cauchy formula on a V-leg and a K-leg, seminorms through Tonelli), #NAG10.15 (congruence; Lemma NAG27: S, V′ common to all loops, s and ω congruence-invariant), #NAG10.16 (Lemma NAG28: straight and one-corner arcs cancel under Σn_S = Σn_S·n = 0, tail αe^{−b(𝗆+1)}Σ|n_S|N), #NAG10.17 (runs, ε_v, multiplicity-one 𝒱 = ℝπ_*; Lemma NAG29), #NAG10.18 (Lemma NAG30, comparison runs and shooting by the intermediate value theorem), #NAG10.19 (Lemma NAG31, final scale, N ≤ 16L), #NAG10.20 (Theorem NAG32).
- Edits in existing lines: #NAG10.1 general loops c𝖱_n with cm ∈ ℕ (blocks sentence split into #NAG10.1a), #NAG10.1-2 W(γ), #NAG10.8 P(γ), #NAG10.13-1 (iv) includes ω(Y).
- Self-review (every line): the K-leg uses Theorem NAG25 at (4v, ε_b) for the ω̂ majorant; the θ^*g extension fills gaps (an arc may meet a side twice); m = L_𝔄^Δ ∈ ℕ is required; v in Theorem NAG32 is the maximum over the loops; the IVT is named; g_W > 0 justified by 𝔶̃ > 0 and |𝔶 − 𝔶̃| ≤ 𝔶̃/2. Symbol choices: second loop γ̌ (γ′ is the tangent), coupling ϰ (A clashes with arcs and C_A).
- Header: #NAG.0-1a (Theorem NAG32 result, split from #NAG.0-1 at 608 characters), #NAG.0-2 cites the band regime, new #NAG.0-2c states what is open (the flow of ϰ_j; Theorem NAG25 gives only C_L(v² + ε_v)/c_π per step).
- NA 424d3115a705 (snapshot NA_pre_NAG32.md) → 6c0d6965f94c: (G2) at #NA5.1 cites Theorem NAG32 and #NAG.0-2c.
- Approvals requested: (G2) restricted to π with 𝒱 = ℝπ_* (G stays general); the band-regime statement of (R1); L_𝔄^Δ ∈ ℕ; the profile (ii); κ > 0 not used.
- Checks: NAG 326 lines, CRLF 326, longest 602, no duplicate tags or dangling references; NA 69 lines, CRLF 69, none > 600.

## 2026-11-12 02:14 GMT: parity, cubic flow, Theorem NAG36; the weak side
- NAG a76bee1186eb (snapshot NAG_pre_NAG33.md) → a56409c95934; NA 6c0d6965f94c → 7409369150dd.
- #NAG10.21 (K^∨, K^±) and Lemma NAG33 (#NAG10.21-1–3): (V, K) ↦ (−V, K^∨) commutes with the step, with S, s, ω, E unchanged, V′ ↦ −V′ and K_{j+1} ↦ K_{j+1}^∨. Proof: T_A(−V; g) = T_A(V; −g), and ζ̃_j has the law of −ζ̃_j.
- Lemma NAG34 (#NAG10.22–#NAG10.22-6): on the state (zV, wK^+ + zK^−), V′ − zV is odd in z. The proof uses separate analyticity (Theorem NAG25(iv)), continuity from Cauchy's estimate, a(w) = ∂_zF(0, w) analytic by Fubini and Morera, and the kernels (z²(z² − 1))^{−1} and (w(w − 1))^{−1}. It gives ‖V′ − V‖ ≤ C_Lε_− + u_♭ε_+/(2ε_L) + u_♭³/6, and the same for the odd part of K_{j+1}, with leading term 28ε_−/L.
- Lemma NAG35 (#NAG10.23–-4): the induction ‖K_j^+‖ ≤ C_+v_j², ‖K_j^−‖ ≤ C_−v_j³ gives |v_{j+1} − v_j| ≤ C_♭v_j³, so v_j^{−2} moves by at most 3C_♭ per step. Constants: C_+ = 10C_L and C_− = 80C_+/(v_Lε_L) + 320/(3v_L³), chosen so that 0.7 + 0.1 ≤ 0.8 ≤ 0.93³ and 8.6C_L = 10C_L·0.86. Inequalities used: (1 + x)^{−2} ≥ 1 − 2x, and (1 − x)^{−2} ≤ 1 + 3x on [0, 0.07].
- Theorem NAG36 (#NAG10.24–-2): the band regime contains every sequence with 𝗀 ≥ 2η^{θ_L} and 𝗀^{−2} − C_♯ln(1/η) → ∞, C_♯ = 2C_♭c_π²/ln L, e.g. 𝗀²ln(1/η) = c ∈ (0, 1/C_♯).
- New #NAG.0-2d: a perimeter or area law gives 𝔶_S → 0 (P(𝖱_n) and the area nts are affine in n, Σn_S = Σn_Sn = 0). So g_W(λ) → 0 alone does not force weak coupling, and the band regime is the weak-coupling part of (R1). #NAG.0-1a, #NAG.0-2 (split into #NAG.0-2-1 at 663 characters), #NAG.0-2c and NA (G2) were reworded accordingly.
- Self-review fixes before the checks: K^∨(X; 0) = K(X; 0) stated; G(0, 0) = 0 by continuity; j₀ ≤ j_* added to Lemma NAG35; θ_L pointer.
- Approval requested: state (R1)/(G2) on the band regime (weak side), as #NAG.0-2d shows that g_W(λ) → 0 does not exclude perimeter- or area-law sequences.
- Checks: NAG 347 lines, CRLF 347, longest 602, no duplicate tags or dangling references; NA 69 lines, CRLF 69, none > 600.

## 2026-11-12 02:55 GMT: NG finished as Theorem N; NA and NAG abandoned
- User, 12 Nov 2026: finish NG, abandon NA. No further work on NA (7409369150dd) or NAG (a56409c95934); both files are left in place, unedited.
- NG 670a717698fe (snapshot NG_pre_finish_670a717698fe.md) → ef223510a700; work file cff5e5fb5eff (snapshot O1C_pre_finish_cff5e5fb5eff.md) → acc21c562b85.
- Foreign edit found: the two-loops session's change to R_j := R^T_j (handover, 11 Nov 2026 17:45) rewrote #NG5.2-3–#NG5.2-4 to R_{K′} ≥ (log ḡ^{−2})^r and left four consumers at the old 2(log ḡ^{−2})^r. Repaired: #NG7.1-2 (𝖣 ≥ (2/9)L³M(log ḡ^{−2})^r), #NG7.7-1 (exponents /18 and /1152), #O1C.3-9.1 and #O1C.4-5.2 (t_b ≥ L³M(log ḡ^{−2})^r). Only constants change. #NG5.2-3 now cites LF #4.50-1.1.1 with its prefix, declared in #NG.0-1 with #NP…; #NG5.2-4 cites #T4.52-0-2 for R̂ in place of the undeclared #886; #O1C.3 cites #T2.23's R_{K′} without "CRE's radius".
- Stationarity removed from the Gaussian class. New #NG1.4–#NG1.4-3: the translates 𝖨₁, 𝖨₂, 𝖨₃, 𝖱₂^{(1)}, 𝖱₃^{(1)} (eleven diagrams), ind(𝔇), the weights n^sym, 𝔜^sym, and the ten index sums 𝗌(a, b) = 0. #NG2.1: a Gaussian charge model has any covariance, and is stationary if Cov(𝖷_a, 𝖷_b) = c^G_{abs(a−b)}; new #NG2.1-0 holds 𝖷(𝔇), κ(𝔇), W(𝔇), moved from #NG2.1 and #NG2.2-1.
- Proposition G (#NG2.2–#NG2.2-2): 𝔜^sym = 0 on every Gaussian charge model and limit, 𝔜 = 𝔜^sym = 0 on the stationary ones. #NG2.3 keeps the stationary formulas; #NG2.3-2 re-pointed to them. New #NG3.4: W_ren(τ𝔇; ε) = W_ren(𝔇; ε), so 𝔜^sym(W) = 𝔜(W) for Yang–Mills with no new hypothesis; #NG5.5-1 cites it; #NG4.3 says stationary.
- #NG.1–#NG.1-2 are now Theorem N, with hypotheses #GL7.1's conditions for the six diagrams and q₀ > 25r + 5/2, and #NG6.3–#NG6.3-1 its proof (the former target line, with (O1b) by Lemma H and (O1c)).
- Work file: the unused §5 lines (#O1C.5–#O1C.5-2, #O1C.5-3–#O1C.5-6.1) deleted, §5 retitled "The Parameter λ" and keeping #O1C.5-2.1; #O1C.0 and #O1C.4-4 no longer mention them; #O1C.7-9's last sentence gives the reason for DHλ(K + λ)^{−1}u = P_rDHu.
- Re-derived before writing: the ten index sums; the class sums 1, −3, 3; 𝔶_S = 𝗀²(c^G_3 − c^G_2) and 𝔶_k = −𝗀²c^G_k in a stationary model; c_dx ≥ νL³(log ḡ^{−2})^r/(64A_d); the two exponents of #NG7.7-1. The 143 external lines cited by NG and the work file outside PF were re-read against their uses.
- Checks: NG 161 lines, CRLF 161, none over 600 characters, no duplicate tags, every tag resolves; work file 178 lines, LF, none over 600, no duplicate tags, every tag resolves (#BPA.5 and #BPA.6 in balaban_proofs/BP_PF_ACTION_LOWER_BOUND.md).
- Messages sent at 02:58: table session (yang mills 4 handover (2) ⑂ (2); rows #T12.36-1, #T12.36-2, #T12.36-2-1, #T12.36-10-0-1, #T12.37–#T12.37-4), two-loops session (yang mills 4 handover ⑂ (3); the four consumers), and yang mills 4 handover (4) (NA and NAG abandoned).
- Peer note (two-loops session, after 02:58): it re-checked the four repaired consumers and the two re-pointed citations and agrees; it will message before editing NG or the work file again.

# Triage: LF packet 13b, round 5 (lf-p13b-20261108-r5), 8 Nov 2026

## Verdict

Not clean: three minor findings (m1–m3) and seven observations (o1–o7). There is no fatal or serious finding. 13b's clean count stays 0.

LF reviewed at 9862073671bf (table 738ed458c86b, LABELS 49097cb3bd46, Cauchy 2acf54aae054). The referee confirmed:
- every round-4 repair (m1, o3, o5–o9);
- the Lemma, the lines, the real points, (T-c), the non-circular data bound C_{V′}, Proposition 9's ε₂, U_0(z) through (1.43), the disc bounds at base ε₁′, the 5/16 result, the couplings, and the absorption.

## Origin of the findings

- m1 came from my r4 o3 repair. That repair added the segment problems' base 2ε₁′ to #4.561-1 but did not carry it into U^r's plaquette constant (#4.563-2) and c_pl.
- m2 (#4.565's block-density constants) and m3 (the D-tags c₂ and α₁) were in the text since 13b r1.
- o6 was also in the text since the disc's data list (#4.561.1–#4.561.1-2) was written. The list treated the averages of U_0 in the axial gauge only. U″_k's data are in the axial–Landau gauge, whose gauge ū₀(z) moves at complex z. The repair below enlarges C_{V′}, so o6 is treated as a gap, not as wording.

## Repairs

| Finding | Where | Repair |
|---|---|---|
| m1: U^r's plaquette constant is taken at base ε₁′; the segment problems have base 2ε₁′ | #4.563-2, #4.563-2.1, #4.563-2.2 (split; new #4.563-2.2-1), #4.561-1.2 | U^r's plaquettes ≤ 4C₀^{ms}ε₁′/a_j², (b)'s bound at ε_r = 2ε₁′ (#4.48.0-0, #4.560-2), covering both bases. Then (2 + 16C₀^{ms}ε₁′ + 16ε₂)ε₂L^{−2j} ≤ 3ε₂L^{−2j} and c_pl := 4 + 3B₅^c/C₀^{ms} (the referee's second option). c_4's hypothesis is taken with 2ε₁′ for ε₁, with plaquettes ≤ (2C₀^{ms}·2ε₁′ + 4α₁)/a_j². The threshold is now 16C₀^{ms}ε₁′ + 16ε₂ ≤ 1 |
| m2: #4.565's first- and second-order constants are asserted | #4.565, new #4.565-0 | #4.48.0 at ε_r = ε₁′ with abs(ℋ)_y ≤ d̄^c gives abs(a_y(U^A) − a_y(Ũ)) ≤ C_bd(ε₁′ + d̄^c)d̄^c. With b_y as in #4.51-1.0, this gives C_y(M) := C_bd(1 + C_U(M))C_U(M) + C_b. d̄^c := C_U(M)(ε/a_n)^{(1−ε₀)/3}ε₁′ (#4.59 with ε₁′). It was first named d̄′ and is renamed here, since #4.504's pointwise d̄′(x) is a different bound |
| m3: c₂ and α₁ each have a clashing D-tag | #4.115, #4.117, #4.118 (§4(d)); #4.508-0 (§4(d)) | {#D.c₂} := 648d²L² → {#D.c_B̃₂} c_{B̃₂}, with all its uses (abs(B̃₂) ≤ c_{B̃₂}b_k², the β-derivative, C_tw(M)). {#D.α₁} := 8dL²α′ → {#D.α₁^ι} α₁^ι. (T-c)'s c₂ (CMP98's) and the pair class's α₁ (PBG's) are unchanged |
| o2: 27c_avα̂₁ ≤ 1 and c_avε′_k ≤ ½ are not listed | #4.561.1-0 | It now states that both follow from (T-c)'s C_{V′}ε₁′ ≤ ½, since C_{V′}ε₁′ ≥ 4c_avC_cα̂₁ = 240c_avα̂₁; the second gives c_avε′_k ≤ ⅛ |
| o3: 3ε₂ ≤ 4α₁ is implied by ε₂ < α₁ | #4.561-1.2 | The redundant condition is removed (in the m1 pass) |
| o5: the Cauchy radius in the multiplicative metric | #4.567-1 | abs(V′ − 1) ≤ C_{V′}ε′_k ≤ ¼C_{V′}ε₁′ by C(M) ≥ 2 and R_k ≥ L ≥ 2. A move W with abs(W − 1) ≤ r := ½C_{V′}ε₁′ ≤ ¼ gives abs(WV′ − 1) ≤ (9/16 + ¼)C_{V′}ε₁′ < C_{V′}ε₁′ |
| o6: U″_k's data exp(ig_kB)(M^·U_0)^{ū₀} at complex z | new #4.561.1-1.2 (#4.561.1-2's representation and c_Ṽ moved here), #4.561.1-1.2-1, #4.561.1-1.3, #4.561.1-1.3-1, #4.561.1-1.3-2; #4.561.1-2; new #4.561-1-2; #4.561-1.2 | Derived below. C_{V′} := max(4c_av(1 + 4d·100⁵γ₀^{−1}B₃² + c_ṼB₃B₅)M⁵, 4(1 + 48c_GdB₁B₃)C_{AL}). (T-c) adds 4c_Gdε₂ ≤ 1 |
| o7: "(2.39) for its radius r_{1,q}" conflates α̂₁ and r | #4.561.1 | Now 26c_avr_{1,q} ≤ 26c_avα̂₁, since r_{1,q} = α_{1,q}/(8B₃) ≤ α̂₁ |
| o1 (26ε₁′ stronger than needed), o4 (a₄ "absolute") | none | A stronger valid condition, and a correct reading; no change |

## Re-derivation

- **m1, #4.563-2.1.** U^r's plaquettes satisfy abs(U^r(∂p) − 1) ≤ η²abs(F) ≤ 4C₀^{ms}ε₁′L^{−2j}. The move of a plaquette variable by the four factors e^{iη𝐇} is then:
  - first order: < 2ε₂L^{−2j};
  - transport: 4·4C₀^{ms}ε₁′·ε₂L^{−2j};
  - second order: < 16ε₂²L^{−2j}.
  - Under 16C₀^{ms}ε₁′ + 16ε₂ ≤ 1 the sum is ≤ 3ε₂L^{−2j}.
  - The representative then has abs(F) ≤ (4C₀^{ms}ε₁′ + 3B₅^cε₁′)/a_j² = c_plC₀^{ms}ε₁′/a_j² with c_pl = 4 + 3B₅^c/C₀^{ms}.
  - #4.563-3's C_act = d²(c_plC₀^{ms})² keeps its form and needs c_plC₀^{ms}ε₁′ ≤ ¼, a smallness condition of the same kind.
  - The caller #4.198-1 reads c_plC₀^{ms}ε₁′ at the regularity 2ε₁ with c_plε₁′ for 2ε₁, so ε_r = c_plε₁′/2 ≤ c_plε₁′. It stays consistent.
- **m2, #4.565-0.** #4.48.0's conditions hold at ε_r = ε₁′ and abs(ℋ)_y ≤ d̄^c ≤ C_U(M)ε₁′ (#4.561-1.2), and Ũ obeys a_j²abs(F) ≤ 2C₀^{ms}ε₁′ (#4.48.0-0).
  - C_bd(ε₁′ + d̄^c)d̄^c ≤ C_bd(1 + C_U(M))C_U(M)(ε/a_n)^{(1−ε₀)/3}ε₁′².
  - b_y ≤ C_b(ε/a_n)ε₁′² ≤ C_b(ε/a_n)^{(1−ε₀)/3}ε₁′², since ε/a_n ≤ 1.
  - The sum gives C_y(M).
- **o6, the gauge of U″_k's data.**
  - **The data.** U″_k's data on Λ ∩ Ω″^{∼2}_{h+1} are exp(ig_kB)D^{AL}(z), D^{AL}(z) = (M^·U_0(z))^{ū₀(z)} (#4.52). u₀(z) is LFR I (1.86)'s transformation at U_0(z).
  - **Its problem.** (1.86) expands U_0 = U(𝔹_k(Λ), M^·(U_0)) around the configuration 1 and takes its Landau gauge (LFR I p.197 l.16–23). That is VAR Proposition 2's transformation (p.281 l.1–3) at the base 1. LFR II continues it, with 𝐇_{k,Λ}, by VAR Sect. G (p.367 l.47–48).
  - **The data of that problem.** M^j(U_0(z)) = Ṽ_{j,Z}M^j(U_0(0)) with abs(Ṽ_{j,Z} − 1) ≤ c_ṼB₃B₅M⁵abs(B^e) ≤ 2c_avc_ṼB₃B₅M⁵ε′_k ((1.44)–(1.45), on Λ).
    - LFR I (1.84) at the real point, with O(1)ε′_k for ε_k as for (1.83), gives abs(M^j(U_0(0)) − 1) ≤ c₈₄B₃B₅M⁶ε′_k.
    - M^j(U_0(0)) is unitary, so abs(ṼW − 1) ≤ abs(Ṽ − 1) + abs(W − 1).
    - So abs(M^j(U_0(z)) − 1) ≤ C_{AL}ε′_k, with C_{AL} := 1 + c₈₄B₃B₅M⁶ + 2c_avc_ṼB₃B₅M⁵ ≥ 1.
  - **Proposition 9 at the base 1.** V₀ = 1 is regular with any ε₁, so take VAR's C₁ = C_{AL} and ε₁ = ε′_k.
    - (173): ε₂^{AL} = B₁(B₃(1 + 4C_{AL})ε′_k + C_{AL}ε′_k) ≤ 6B₁B₃C_{AL}ε′_k.
    - Its thresholds are monotone in ε₂, and ε₂^{AL} ≤ ε₂/4, since C_{V′} ≥ 4C_{AL} and ε₁′ ≥ ε′_k (#4.561-1-2).
    - Proposition 6's inequality reads 2B₀C_{AL}B₃ε′_k ≤ 64ε₂^{AL} = 384B₁B₃C_{AL}ε′_k, which is true.
  - **The gauge.** U_0(z) is in the axial gauge in k-blocks (p.197 l.9; (1.43) "in the axial gauge", p.367 l.27–30), and so is 1. #4.517's argument applies verbatim: u is fixed by the transports of e^{iη𝐇_c} along axial contours of ≤ dL^j bonds and by R̄₀u^j = 1, with η|𝐇_c| ≤ ε₂^{AL}L^{−j} by (19). So abs(log u₀) ≤ 4c_Gdε₂^{AL} =: λ at z and at 0, and the same holds for ū₀, which takes u₀'s values at the centres.
  - **The bound.** A datum is ū₀(x)W(b)ū₀(y)^{−1}, with W := M^·(U_0(z)).
    - abs(ū₀(x)Wū₀(y)^{−1} − 1) ≤ e^{2λ}abs(W − 1) + (e^{2λ} − 1).
    - With 16c_Gdε₂^{AL} ≤ 1: 2λ ≤ ½, so e^{2λ} ≤ 2 and e^{2λ} − 1 ≤ 4λ = 16c_Gdε₂^{AL} = 96c_GdB₁B₃C_{AL}ε′_k.
    - So abs(D^{AL}(z) − 1) ≤ 2(1 + 48c_GdB₁B₃)C_{AL}ε′_k, and the same at z = 0.
  - **The deviation.** V₀ := exp(ig_kB)D^{AL}(0) is real, and V′ := exp(ig_kB)D^{AL}(z)D^{AL}(0)^{−1}exp(−ig_kB).
    - Then abs(V′ − 1) = abs(D^{AL}(z) − D^{AL}(0)) ≤ 4(1 + 48c_GdB₁B₃)C_{AL}ε′_k, the second entry of C_{V′}.
    - 16c_Gdε₂^{AL} ≤ 4c_Gdε₂ ≤ 1 by the new (T-c) condition.
  - **The consumers of C_{V′}.**
    - #4.561-1 uses C_{V′} ≥ 4. It holds, since 4C_{AL} ≥ 4.
    - o2 uses C_{V′} ≥ 4c_avM⁵ (the first entry).
    - B₅^c, ε₂, ε₂^ι, c_pl, C_act and C^c_J are defined from C_{V′} and keep their forms. Their numerical values grow, and they enter only smallness conditions (for γ small, M fixed first).
    - §4(d)'s line "below C_{V′}ε₁′" (*The route.*) only gains.
    - The referee suggested gauge invariance; the direct bound above avoids reading G^c-invariance into the conjugated exp(ig_kB).
- **o5.** abs(V′) ≤ 1 + ¼C_{V′}ε₁′ ≤ 9/8, so r·9/8 = (9/16)C_{V′}ε₁′.

## Pre-check, lf-p13b-20261108-r6 (full round)

**Changed lines in the extracts.** Each is re-read and re-derived above:
- #4.561.1 (o7), #4.561.1-0 (o2);
- the new #4.561.1-1.2, #4.561.1-1.2-1, #4.561.1-1.3, #4.561.1-1.3-1, #4.561.1-1.3-2, and #4.561.1-2 (o6);
- #4.561-1.2 (m1, o3, o6) and the new #4.561-1-2 (o6);
- #4.563-2, #4.563-2.1, #4.563-2.2, and the new #4.563-2.2-1 (m1);
- #4.565 and the new #4.565-0 (m2);
- #4.567-1 (o5).

**Changed lines outside the extracts.** Both are permitted background, reviewed in their own packets:
- #4.115, #4.117, #4.118 (m3, c_{B̃₂});
- #4.508-0 (m3, α₁^ι).

**Symbols.**
- New: C_{AL}, c₈₄, D^{AL}(z), ε₂^{AL}, d̄^c, c_{B̃₂}, α₁^ι. Each was grepped in the LF, the table, the Cauchy and W-δ notes, and balaban_proofs/, and is free.
- d̄′ is renamed d̄^c, since #4.504's d̄′(x) is another bound.
- c_Ṽ's definition moved into #4.561.1-1.2 and is not restated.
- The table rows (#T12.9-1: C_{V′}, the new constants, c_pl, d̄^c, C_y(M); #T12.9: c_{B̃₂}; #T12.12: α₁^ι) were sent to the table fork at 01:39, with the new tags.

**Every use of C_{V′}** (16 in the LF) was grepped: none uses an upper bound on C_{V′}.

**Other checks.**
- No known weak point is left.
- Every new and changed line in the extracts is ≤ 600 characters. The longest are #4.563-2.1 at 566 and #4.561-1.2 at 526.
- The cited pins were re-read:
  - LFR I p197_corrected l.1–41;
  - LFR II p367_corrected l.24–49, p370_corrected l.1–20, p362_corrected l.18–31;
  - VAR p281_corrected l.1–30;
  - REG p.88–89 (for the two-loops note's reading, not cited).

## Repaired SHAs

- LF 9862073671bf → 1c87cfb8768b.
- Cauchy 2acf54aae054, unchanged this round (#C7.5-2 was changed in r4).
- Table 565d0ca22a72 → 7d7f4da8fb3d, LABELS d4fe87df6146 → 1353bdf7f256. The fork entered the rows listed above and relabelled at LF 1c87cfb8768b and Cauchy 2acf54aae054; all four SHAs were verified here. The fork also entered V₀ := exp(ig_kB)D^{AL}(0) and r := ½C_{V′}ε₁′ as local definitions in #T12.9-1, and re-derived #4.561.1-1.3-2 independently.
- The spec is specs\spec_p13b_r6.json: lf_sha 1c87cfb8768b, prior r5. It adds VAR Proposition 2 (p.281), LFR II p.370, and #T4.10 to the background, and a question on U″_k's data. The definition check gives 0 conflicts (6 allowed).
- The r6 packet is 21,752 characters of reviewed blocks (r5: 19,049). The growth is new mathematics: the derived bound on U″_k's axial–Landau data (o6) and #4.565-0's derivation (m2).

## r6 stopped; two recheck passes before r7

The user stopped lf-p13b-20261108-r6 before its report and asked for every repair to be rechecked twice. r6 has no review, so r7's prior is the r5 review.

**First pass: weak points found in my r5 repairs, all repaired in place.**

| Point | Line | Weak point | Repair |
|---|---|---|---|
| a | #4.561.1-1.3, new #4.561.1-1.3-0 | u₀ was presented as VAR Proposition 2's transformation, but LFR I prints no normalisation | 𝔹_k(Λ) cited as #T11.27's minimal determining set, (1.86) as Proposition 2 at the base 1 (#T11.25); the normalisation R̄₀u₀^j = 1 labelled inferred, not printed; the integral is unchanged by #4.52-1's argument, u₀ being a function of V_k |
| b | #4.561.1-1.2-1 | (1.84) was used at O(1)ε′_k with only (1.83) cited | (1.84) comes from (1.80), (1.83) and (1.65) [14] (p.197 l.9–11), and (1.80) and (1.83) from (1.78) (p.195 l.19–20, p.197 l.3–6), so #4.560-1.1.2 covers it |
| c | #4.561.1-1.3-1, new #4.561.1-1.3-1.0 | "axial conditions in k-blocks" did not show that U_0(z) is in the axial gauge of the problem (1.85), whose set 𝔹_k(Λ) has finer layers near ∂Λ (CRE p.256 l.56–62) | derived: at the base 1 the conditions (1.19) of a block of the layer j (#T11.33) are those of the levels n < j along its sub-blocks, which the k-block containing it imposes; U_0(z) is in the k-block gauge by (1.43), Λ lying in 𝐁_k(Z)'s top layer (#4.44-0.2) |
| d | new #4.561.1-1.3-1.1 | #4.517 needs "ε₂ small"; whether this holds at ε₂^{AL} was not stated | stated: its argument runs per block of each layer, and its smallness holds at ε₂^{AL} ≤ ε₂/4 (#4.561-1-2) |
| e | #4.565 | "at each configuration of (b)–(d)" did not say which regularity, while the segment points have 2ε₁′ | the densities are at V′^A₀ and V′^B₀, regular with ε₁′ (#4.51-1.1); the segment enters only the t-derivative at 2ε₁′ (#4.51-2.1), so ε_r = ε₁′ is right |

**The table.** The user asked why these readings were not in the table. They should have been: the pre-check rule asks for every reading to be entered and cited by row. The packet's Bałaban pins were swept one by one against the table:
- Cited from existing rows in place of restated pins: #T11.10 (CRE's class), #T11.30 (LFR II's U_0), #T6.11 (p.374), #T11.18 (VAR (152)), #T3.19 (VAR (7) and Theorem 1), #T11.19 (VAR (2)), #T11.19-1 (REG (1.1)), #T3.13 (CRE (2.28)), #T3.32 (a₃), #T3.14 (LFR II's γ₀, in place of #T4.30, a two-loops constant).
- New rows requested and entered by the table fork, all pins re-checked by both sessions:
  - #T11.29-1 to #T11.29-3: LFR I (1.80), (1.83)–(1.86), and the u₀ reading.
  - #T11.30-0 to #T11.30-3: LFR II p.358 l.26–30 and (1.38)–(1.45).
  - #T3.32-1 and #T3.32-2: VAR's a₄, Sect. E, and (113), and the dependence of Bałaban's constants.
  - Row C: CMP98 Proposition 2, VAR Sect. F, LFR I Proposition 1, LFR II (1.7)–(1.9) and (1.35), VAR (172)–(175) with Proposition 9, VAR Proposition 3, REG p.82 and (1.47), and PBG (3.39).
- #4.561-1-1's "ε₄ = 64ε₂ (p.296 l.9)" now reads "ε₄ = 8·8ε₂ = 64ε₂": the print's ε₄ = 8ε₂ is Sect. E's value at its own ε₂, here the regularity 8ε₂.
- #4.561.1-1.3-0 now holds only the normalisation and why it does not matter; the reading itself is #T11.29-3.
- Before launch, two points flagged as the likeliest minors were strengthened. #4.561.1-1.3-1.0 now says why a j-block's chains are among its k-block's: the blocks of CMP98 (2) refine one another (a new row was requested). #4.561.1-1.3-0 now states #4.52-1's invariance directly.

**Second pass.** Every line from #4.561.1 to #4.567-1 was re-read and its arithmetic redone:
- #4.561.1-0: e^{27c_avα̂₁} − 1 ≤ 54c_avα̂₁ ≤ c_avε′_k by C_c = 60.
- #4.561.1-1.2-1: C_{AL} = 1 + c₈₄B₃B₅M⁶ + 2c_avc_ṼB₃B₅M⁵ covers abs(Ṽ − 1) + abs(M^j(U_0(0)) − 1).
- #4.561.1-1.3-2: e^{8c_Gdε₂^{AL}} ≤ 2 and e^t − 1 ≤ 2t for t ≤ ½ give 2C_{AL}ε′_k + 96c_GdB₁B₃C_{AL}ε′_k.
- #4.561.1-2: the three branches of C_{V′} (𝐔's averages c_avε′_k; V′^X₀ ≤ 16c_avd·100⁵γ₀^{−1}B₃²M⁵ε′_k; Ṽ ≤ 2c_avc_ṼB₃B₅M⁵ε′_k), and C_{V′} ≥ 4 for C₁ = C_{V′}/2 ≥ 2 in #4.561-1.
- #4.561-1-2: ε₂^{AL} = 6B₁B₃C_{AL}ε′_k ≤ ε₂/4, Proposition 6 at the base 1, and 16c_Gdε₂^{AL} ≤ 4c_Gdε₂ ≤ 1.
- #4.563-2.1: the c_pl arithmetic, and #4.563-2.2's ≤ (4C₀^{ms}ε₁′ + 4α₁)/a_j².
- #4.565-0: C_y(M) arithmetic.
- #4.567-1: radius (9/16 + ¼) = 13/16 < 1.
- The lines outside the extracts (#4.115, #4.117, #4.118, #4.508-0) were re-read: c_{B̃₂} = K/r² = 648d²L² and α₁^ι are used consistently, and both are in the table (#T12.9, #T12.9-1).
- Citations to later lines are by tag. I had misread the user's "keep things linear" (work through the files one step at a time) as a ban on forward citations. On that reading I had replaced six tags with a vague "below", in #4.559-1.1, #4.560-0, #4.561.1-0, #4.561.1-1.3-1, #4.561.1-1.3-1.1, and #4.561.1-3. These were rewritten to cite the tags: #4.567, #4.560.1–#4.560-1.1.2, #4.561-1.2, #4.561-1-1 and #4.561-1-2, and #4.561-1 and #4.509. This is bookkeeping (re-pointing to the same text) after r8's build, so r9 sees it.
- Every line is ≤ 600 characters except #4.560 (608, unchanged since r5). The over-long #4.561.1-1.3-1 (635) was split at a sentence into #4.561.1-1.3-1.0.

## Pre-check, lf-p13b-20261108-r8 (full round)

r7 (LF 90648860989c) was built but not launched, because the forward-citation check before its launch found #4.560-0's range citation. r8 replaces it. Its prior is still the r5 review.

**Tags under the pre-check.** The r8 gate lists #4.560-0 (changed since the r7 build). The r7 gate listed, since r5's build:
- #4.559, #4.559-1, #4.559-1.1, #4.559-2;
- #4.560.1, #4.560-1, #4.560-1.1, #4.560-1.1.1, #4.560-1.1.2;
- #4.561, #4.561.1-1.1, #4.561.1-1.2, #4.561.1-1.2-1, #4.561.1-1.3, #4.561.1-1.3-0, #4.561.1-1.3-1, #4.561.1-1.3-1.0, #4.561.1-1.3-1.1;
- #4.561-1, #4.561-1-1, #4.561-1.1, #4.561-1.2, #4.561-2;
- #4.562-1;
- #4.563-1, #4.563-1.1, #4.563-1.2, #4.563-2-1, #4.563-2.1;
- #4.565.
Every one was re-read in both passes above. Apart from points (a)–(e) and the ε₄ wording, each change replaces a restated page pin with the row citing the same text; each row was checked against its pin.

**The gate's questions.**
- Changed lines re-derived: yes. #4.560-0's ε₁′ := C(M)R_kε′_k is derived in #4.560.1–#4.560-1.1.2, which follow it, and "shown below" now says so in words.
- Arithmetic and citations re-checked: yes, the second-pass list above. All 38 cited table tags exist in the frozen LABELS, and the script check finds no missing tag.
- New symbols and claims checked: no new symbol since r7. #T11.33-1 and #T11.33-2 are rows, not restated in the note.
- Wider implications checked: the change is wording only, with no bound changed.
- Linear order kept: yes. The script check over #4.559–#4.568 finds no forward tag citation.
- Relabelled, spec current, packet built: yes. The fork relabelled at LF 07065b0520af. The spec is specs\spec_p13b_r8.json (lf_sha 07065b0520af, prior r5). The definition check gives 0 conflicts (6 allowed).
- Pre-check in the triage file: this section.

**SHAs and size.**
- LF 90648860989c → 07065b0520af (no CRLF).
- Table e5a1131811bf (unchanged). LABELS 169e2f787a15 → 6a37a08d8be1. Cauchy 2acf54aae054. All four were verified here, and the fork reports citations going 1849 → 1847, which matches the removed range.
- The r8 argument is 22,202 characters (r7 22,212; r6 21,752).

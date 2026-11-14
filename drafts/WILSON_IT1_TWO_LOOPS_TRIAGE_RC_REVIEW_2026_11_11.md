# Triage: Review of RC's New Repairs (11 November 2026)

Two-loops session. The user's instruction: "Review and consolidate the new repairs". Scope: the unreviewed lines of RC_PROOF_PASS_2026_10_23.md listed at #RC.0-4 (#RC.3–#RC.4's repairs, #RC.5 except #RC.5-2, #RC.5-2-1 and #RC.5-9, the local shift and 𝒦₃, the step-1 τ, the penalty lemma, and #RC.6-5-8–#RC.6-5-13). Packets: rc_a (§§3–5 under review, 22.5k characters) and rc_b (§6, 23.6k characters).

## Pre-check before rc_a r1

- RC read in full (40BA9FDBEBB1). Every line of §§3–6 re-derived against the cited displays:
  - CRE p.278 l.32–35: "The terms of the sum above satisfy the bounds (2.42), with the constant B₀ replaced by O(p₀³(g_k)) … the multiplication by g_k yields small bounds" (#RC.3-14-1).
  - RG II (1.20): |B′| ≤ C₁g_k|B| < C₁ε₁; (1.40): the second derivative bounded by ½C₃3³e^{56κ₁}|B′|·exp(…); (1.43): |Q(Y, B, b, b′)| ≤ C₃ε₁M⁴e^{C₂κ₁}exp(…); (1.36): |𝐕′| ≤ E₀ε₁C₁M^qe^{C₂κ₁}e^{−(1−2δ)κd_k(Y)}; (2.18): 1/|τ(Y)| = E₀ε₁C₁α₄^{−1}M^qe^{C₂κ₁}e^{−(1−3δ)κd_k(Y)}; (2.19). With |B′| ≤ C₁g₀O(K_m)r = C₁O(K_m)δ₀ and the circle shrunk by (O(K_m)r)^{−2}, the per-polymer factor is C₃O(K_m³)δ₀r² ≤ C₃ε₁ (#RC.5-6–#RC.5-6-3, #RC.6-5-12-1).
  - RG II (2.22) (penalty ½γ₂ε₁²g_k^{−2}|P|), p.18 l.31 (five equal factors), p.18 l.48 and p.19 l.12 (the 1/20 conditions) (#RC.5-8–#RC.5-8-1, #RC.6-6-3).
  - V4 sec:c5-1: "Put m = −H_{DD}^{−1}H_{DJ}A′_e" (#RC.5-2-1).
- Repairs made before launch:
  - #RC.4-4-2's rate. "κ ≤ min(κ_{CRE}, (1−10δ)½Lκ_{RG2}) − 1" used an undefined κ_{CRE}. RG II's κ is (I.1.18)'s (RG II p.21 l.29), which CRE (2.27)(iv) and (2.42) take over, so with RG II p.21's normalisation the rate is exactly κ and the factor |X| of the z-sum is not absorbed. Repair: RG II's δ is the table's δ_{RG2} = (1 − 2L^{−1})/12 (#T10.28-3-1-1), so (1 − 10δ)½L = (L + 10)/12 ≥ 3 for L ≥ 26. With |X| ≤ 24M⁴(d₁(X) + 1) and κ ≥ 1, |X|e^{−((L+10)/12)κd₁(X) + ϵd₁(X)} ≤ 48M⁴e^{−(κ+1)d₁(X)} for 0 ≤ ϵ ≤ 1/12 (the rates differ by at least 2κ − 1 − ϵ ≥ ½, and (d + 1)e^{−d/2} ≤ 2). New #RC.4-4-2-1, #RC.4-4-3 rewritten, notation in #RC.3, pointer in #RC.0-2.
  - #RC.6-6–#RC.6-6-2: the enlargement cost is now stated against (2.38)'s rate a_H := (1−8δ)½Lκ; #RC.6-6-1 and #RC.6-6-4 refer to #RC.4-4-2-1's margin.
  - #RC.5-8-1 notes RG2_NOTES.md's 18κ for p.18's 4κ.
  - #RC.5-6's "gains at most" now reads "grows by at most the factor".
  - #RC.5-2-1's "m :=" is now "m = … (defined in sec:c5-1, sec:c5-4)", since the symbol is V4's (the packet's definition check flagged m).
  - #RC.3's 678-character line is split, with the new #RC.3-0.
- Symbols: build_packet's definition check passes (0 conflicts). a_H, ϵ (a local bound variable), C_{P″}, C_𝔙, Ω_V, β_{P″}, ϵ_e, ϵ_m, ϵ_H, m^{loc}, 𝒦₀, 𝒦₃, R_U, w′, ρ₂, K_tl, δ_tl and ν_p are not table rows. δ_{RG2} and L ≥ L₀ are the table's (#T10.28-3-1-1, #T1.3).
- RC is now 66FF18F11B86 (153 lines, longest line 628 characters, LF endings).
- rc_a r1 built and launched at 11:21 (packet: reviewed blocks 22,471 characters; snapshot RC 66FF18F11B86, LF 696B636C3A57, table E876B76FB244, labels 0F27D75CD241).

## Pre-check of §6 for rc_b (during rc_a r1; §6 is context there)

- Every line of §6 re-derived: the truncation and w's bound (#RC.6-1-3), the shifted integrand (H_{DD}m^{loc} + tℓ_Λ = H_{DD}(m^{loc} − tm)), the W-host's Cauchy bound, the cutoff split on Y₀ ∩ 𝒦₃, the modulus identity of #RC.6-5 (expanded with A″ = x − im_I^P), the determinant ratio, the centres, the polydisc radii and the bound |z_bm_I(b)| ≤ (C_{P″}r)^{−1}, the Gaussian, W- and potential increments, β_{P″}, the remaining factors, and the enlargement's count and payment against RG II p.18's five-way split.
- Repairs:
  - #RC.6-3-3 put (2.26)'s prefactor 2E₀ε₁C₁α₄^{−1}M^qe^{C₂κ₁} on the wrong side of the W-host condition. RG II (2.28) needs from each member of 𝐃 only (2.26)'s factor, so the condition is 2r^{−1/2} ≤ 2E₀ε₁C₁α₄^{−1}M^qe^{C₂κ₁}e^{−(1−3δ)κd₀(Δ)}, with d₀(Δ) ≤ L⁴ − 1; it holds for small g₀, as before. The new #RC.6-3-3-1 notes that a cube may carry a V- and a W-member, which multiplies a domain's weight in (2.29) by at most 3 (α₆ smaller, then ε₁ smaller, RG II p.21 l.11).
  - rc_b's definition check: w clashed with the table's #T4.47 and is now w_tl (in #RC.5-7, #RC.6-1-3, #RC.6-3, #RC.6-3-1, #RC.6-3-2, #RC.6-3-4, #RC.6-3-8 and #RC.6-5-10). #RC.5-7 is under review in rc_a r1; its change is the rename only, and r2 reads it. #RC.6-5-7's second "x :=" is now "x = … (#RC.6-5)". X′, x and Γ are local and carry allow_defs entries in spec_rc_b_r1.json.
- RC is now 15C7A6ECD316 (155 lines, longest line 628 characters). rc_b's check passes (0 conflicts, 3 allowed). rc_b waits for rc_a's report.

## rc_a r1: report and repairs

- Verdict (reviews\rc_a-20261111-r1\review.md, read in full): fatal none; serious S1; minor M1–M9. "The claim holds after S1 is repaired." Not clean.
- Repairs (each re-derived against the transcriptions before writing):

| Finding | Repair | Tags |
|---|---|---|
| S1: the per-term bound omits the log-det and χ-ratio terms; B₀ threshold wrong | The bond terms of (3.37) split into three kinds: (A) the log-det part (−½log λ₀ plus the λ-integral, constant c_det, rate δ_detM by RG II p.21 l.34–36), (B) the χ-ratio (constant B′_χ), (C) the g₀-expectation (B′_V = O(p₀³)). The rates of (B) and (C) come from the new BP_CRE_PINNED_RATE.md #PE.1 (rate 𝔞_P = (1 − 10δ)½Lκ − η₀ ≥ 2κ + 1 for L ≥ 26, κ ≥ η₀ + 1). z-terms are formed with the box 𝔔_z (constant C_z). New threshold B₀ > 2¹⁰M⁴C_z + C_wpK_tl + 4O(1)C₃ε₁ + 1, independent of Λ and g₀ | #RC.3-14-1–#RC.3-14-4-1, #RC.4-4-2–#RC.4-4-3-1, BP #PE.1–#PE.4 |
| M1: "expectation values of (3.37)" plural; Glimm–Jaffe | Covered by the three kinds; the p.278 l.32–35 citation is attached to (C) only; the Glimm–Jaffe remark is deleted | #RC.3-14-1, #RC.3-14-3 |
| M2: the single condition O(K_m³)C₃δ₀r² ≤ ½E₀ | The factor of (2.26) for polymers meeting 𝒦₃ is 2E₀O(K_m³)δ₀r²C₁… and is below RG II's, so RG II's ε₂ bounds it and every condition (2.28), ε₂ ≤ 1, the penalty condition, p.20's, p.21's holds as printed | #RC.5-6-1–#RC.5-6-3 |
| M3: Theorem 3.14 needs one configuration on both sequences; pin l.10; admissibility | The lemma compares two admissible regions Λ′, Λ″ in Ω₁ (sequences B⁰(Λ′), B⁰(Λ″) with the one U₁); quote pinned at p.427 l.10; admissibility against Theorem 3.15's hypotheses | #RC.4-1–#RC.4-2-1 |
| M4: whole-lattice term must use CRE's threshold r | Stated: built with CRE's threshold r on every bond | #RC.4-1-1 |
| M5: ΛᶜA in the conditioning and in (iii) | (b) refers to the last logarithm, where A_e = 0; in 𝐁_out the outer field enters through the shift; (iii) is A_e = 0 | #RC.3-9, #RC.4-2-2 |
| M6: 𝐁-terms tied to the integration-by-parts form | 𝐁_out := log Ĩ₁ − log Ĩ₀ − ½⟨ℓ_Λ, C^{(0)}(Λ)ℓ_Λ⟩, rewritten through #RC.6-3's shift; walk pairs and cluster differences bounded separately | #RC.5-1-1–#RC.5-1-3 |
| M7: A_e = 0 parts stay in the last logarithm; V^{(0)}(S₁) sees the field on S₁ | Both reworded; V^{(0)}(S₁) does not depend on ΛA and is CRE's own | #RC.3-6, #RC.5-4 |
| M8: threshold r stated only in #RC.5-8-1 | Stated in (f) | #RC.3-13-1 |
| M9: κ quote | Quoted exactly: "Here κ₀ can be chosen arbitrarily large, similarly as κ, if the other parameters are fixed properly" | #RC.4-4-2 |

- Further repairs found in the pre-check (no finding):
  - The sign of the potential is e^{+𝐏^{(0)}} ((1.26), (3.30)), as in Ĩ₁, 𝔑_t, Î₁.
  - 𝔑_t is the normaliser of the measure of (3.30)'s expectation ⟨·⟩_t (p.272 l.43–44), and 𝔑₁ = Ĩ₀.
  - The (A) kind omitted (3.37)'s constant −½log λ₀ (p.274 l.17); now a single-cube term, with c_det ≥ ½|log λ₀|.
  - Rate. Bałaban's β is the table's 1/8 (#T3.34-0-1), not CRE's example 1/4 (the LF session's message, re-derived from #T3.34-0-3 and CRE p.261 l.42, p.262 l.24–29). V^{(0)}(S₁)'s terms carry CRE's improved rate (1 + 4β)κ = 3κ/2, so 𝐁^{(1)}'s bound is stated at (1 + 4β)κ; RC's own terms decay at 2κ + 1 ≥ (1 + 4β)κ. #RC.0-2, #RC.3-14-0, #RC.4-4-2-3, #RC.4-4-3, #RC.4-4-3-1.
  - #RC.4-4-2-1: 2L < LM (was L < LM); 0 ≤ h_z ≤ 1 cited (p.275); 𝔔_z is a wall-connected box, so X′ = X ∪ 𝔔_z ∈ 𝐃₁; d₁ is Euclidean (RG I p.257).
  - #RC.4-4-2-2: the bound on 𝐄(X′, z) through Λ^∼ uses that #RC.3–#RC.4-4-2-1 use of Λ only that it is a union of ℓ-cubes at distance > RM₁ from Ω₁ᶜ.
  - #RC.3-14-1 defines 𝐄₀(Λ, z) := Σ_μΣ_xh_z(x)𝐄₀(Λ, ⟨x, x + e_μ⟩), (3.41) without its log z^{(0)} terms (p.275 l.10), which LINE_DEFECT §3c(2)(a) places.
  - Symbol clashes resolved: c_A → c_det (table #T12.15-0-10), δ_A → δ_det, C_b → C_bond (table #T4.33), C_M → C_wp (table rows), Q_z → 𝔔_z (table l.741's local Q_z), 𝒦 := 𝒦₀ ∪ 𝒦₃ dropped (table #MOMST.55's 𝒦); in BP: w(Y) → u_Y (#T4.47), N(Z₀) → #cubes(Z₀) (N of U(N)), d → d_{k+1} (d the dimension, #T2.1), c₃ → c_cl (#T4.46), c_ε → c_Σ (#T4.34). N(X) → #cubes(X) in RC.
  - Lines over ~600 characters split at sentence boundaries: new #RC.0-4-1, #RC.3-13-1, #RC.3-14-2-0, #RC.3-14-2-1, #RC.3-14-4-1, #RC.4-1-1, #RC.4-4-2-1-1, #RC.4-4-2-3, #RC.4-4-3-1, #RC.6-5-15-1; #RC.6-5-15's heading is now *The potentials' arguments.* (#RC.6-5-12 is *Potentials.*).
  - Removed tags #RC.5-7, #RC.5-7-1 (merged into #RC.5-1-1–#RC.5-1-3); no live note cites them (grep of the YM4 root and balaban_proofs/).

## Peer messages

- From the LF session ("yang mills 4 handover (4)"), on BP_TL_MIXED_TERM #5.4-2's citation of #T11.17: repaired to cite LF #0.1.12-1 directly; p′ (C_H^{reg}'s exponent, LF #0.1.27-1) ≤ p_θ by LF #A.10-1's definition. BP_TL_MIXED_TERM is now 0359A6ECA029. Replied.
- To the LF session: LINE_DEFECT §3c(2)(a)(iv) needs the improved rate, the new threshold pointer (#RC.4-4-3) and the deletion of the false O(g₀p₀³(g₀)) sentence; placement agrees with #RC.3-14-1. The LF session applied all three (LINE_DEFECT 5872E2194395) and raised β = 1/8, repaired above.
- From the LF session (13:16): LINE_DEFECT (iv) re-read against RC 0784E4D957E6 (#RC.0-2, #RC.4-4-2-3–#RC.4-4-3-1); its citation now reads "(1 + 4β)κ = 3κ/2 ≤ 2κ (CRE p.262 l.24–29; β = 1/8, #T3.34-0-1)", no bound changed; LINE_DEFECT is 548540E95F8B. Checked: the same pins as RC #RC.0-2 and #RC.4-4-2-3; each row term ≤ 2C + 1 with d₁(X_c) ≤ 2^d gives (2.42) at rate 3κ/2 for B₀ ≥ e^{2κ2^d}N_{d,M}(2C + 1), and the two thresholds add for the sum over X. Nothing changes in RC.
- From the LF session (14:41): D2.7 closure 52A69CF538EE, line 812 only (CRE δ_k pinned at p.265 l.39, the threshold of (3.3) at 2δ_k and of (3.16)), no bound changed, (R-eval) untouched. Checked: CRE p265_corrected.tex l.39 defines δ_k = g_kA₁/A₀p₀(g_k). The two-loops note, the pair note, RC and RP cite D2.7 by item, not line 812, and none cites CRE p.265 l.40 for δ_k (the Cauchy note's p.265 l.40–45 is the layers of (3.5), correct). Nothing changes in this session's files.

## Pre-check before rc_a1 r2

- Split: §§3–5 with BP come to 31.3k characters (§3 11.9k, §4 7.2k, §5 9.5k, BP 2.7k), so part a is split: a1 = §§3–4 + BP #PE.1–#PE.4 (21.8k), a2 = §5 (9.5k). One referee at a time: a1, then a2, then b.
- Every changed line of §§3–4 and BP re-read; BP #PE.2–#PE.4 re-derived (the box diameter 5M in ℓ₁, the tree inequality, abs(e^{−u} − 1) ≤ 2abs(u), the Mayer sum, 9 = 1 + 2d, 2⁴e ≤ 2⁶); #RC.4-4-2's rate arithmetic ((L − 14)κ/12 ≥ κ for L ≥ 26), #RC.4-4-2-1's count (4(2L − 1)⁴ bonds, 2^{2⁴} sets X per X′, C_z = 2⁶L⁴·2^{16}e^{2(2κ+1)}C_bond), #RC.4-4-3's sum, #RC.5-1-2's n_X and C_wp (δ_tl n_X/8 ≥ (2κ + 2)(d₁ − 404)) checked.
- Cited displays re-read: CRE p.261 (2.41)–(2.42) and l.42, p.262 l.24–29, p.272 l.35–44 ((3.30)), p.273 ((3.31)–(3.35)), p.274 ((3.36)–(3.38)), p.275 ((3.40)–(3.42)), p.253 ((1.26)); RG I p.257; RG II p.21 l.25–37; #T3.34–#T3.34-0-3; #BK.1-1, #BK.5-1.
- build_packet's definition check: 0 conflicts (8 allowed, BP's own symbols).
- RC is now B7BFBD0DBDE2 (171 lines, longest line 602 characters, LF endings); BP_CRE_PINNED_RATE.md 2845980FD958.
- rc_a1 r2 built and launched at 13:12 (snapshot RC B7BFBD0DBDE2, BP 2845980FD958, LF 696B636C3A57, table D77FC861E0D1, labels 695E1EEB30B2). Stopped at 13:13 on the user's instruction ("Stop running review sessions"), before any report; reviews\rc_a1-20261111-r2\ holds the packet and snapshot only. No round counts.

## After the stop (not reviewed)

- §5 pre-check for rc_a2: #RC.5-9 and #RC.6-2-5 now state V4's definition ϑ = 1/(4c_hC_H^near) (rem:c5-1-3) instead of "c_hC_H^near ϑ ≤ 1/4". RC is now 0784E4D957E6.
- specs\spec_rc_a2_r2.json written (§5 under review, 9.6k). spec_rc_b_r1.json brought up to date (§6 under review, 23.9k): the claim now states m^{loc} := −Σ…, abs(m − m^{loc}), w_tl and #RC.6-3's exact shift identity with e^{𝐏^{(0)}(A_e, ·)}, and (e) gives #RC.5-1-3's bound; the callers are the current ones (#RC.1-5, #RC.1-14, #RC.3-9, #RC.4-4-1, #RC.5-1-1–#RC.5-1-3, #RC.5-5, #RC.5-6, #RC.5-6-2); the context ranges end at #RC.0-4-1 and #RC.3-14-4-1, with BP #PE.1–#PE.4 (𝔞_H, #RC.6-6) and #BK added. All three specs carry RC 0784E4D957E6; build_packet --check: 0 conflicts each (a1 8 allowed, a2 0, b 3), LF 696B636C3A57 matches.
- No referee is running for this session; none is launched until the user says so.

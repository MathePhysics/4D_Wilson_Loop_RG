# Triage of lf-p13a2-20261108-r10 (focused round of part 13a2, with part 13a1's lines repaired after its round 8)

## Verdict

- r10 ran at LF 3b7b6d176dd2, table 6d09b1b5054d, and LABELS 971e7d7d5325. LABELS was stale, and the spec said so.
- **Fatal:** none. **Serious:** one, S1. **Minor:** one, m1. **Trivial:** five, t1–t5.
- The round is not clean.
- Q0 (13a1's round-8 repairs) is answered yes: the norms, the factors N and √N, and t1–t4 of 13a1 r8 are correct.
- Round 9's t1–t3 are confirmed repaired.

## Repairs

| Finding | Line | Issue | Repair |
|---|---|---|---|
| S1 | #4.52-1, #4.53, #4.53-1.1, #4.53-1.1-1 | The two brackets bounded scale-m averages of two different representatives of U^A(V′^B₀): the endpoint of the Landau-gauge H₁𝔛 flow, and #4.38's representative in VAR's gauge relative to MU^B. "One gauge of U_0 at the shared centres" was not defined for two lattices | #4.52-1 keeps only run A's ū₀. The new #4.52-1-1 states that each run's U_0 is in LFR I's own axial gauge in k-blocks (#T11.29-2), with the conditions REG (1.14) and (1.19) at the base 1 along PRT1 (1.7)'s contours, which depend only on the blocks, so MU^B_0 satisfies run A's conditions at the shared levels. #4.53 names U^A(V′^B₀) as the element in that gauge of run A's critical orbit at V′^B₀. The new #4.53-1.0-1 and #4.53-1.0-2 bound the change to that gauge: abs(M^m(V^u) − M^m(W)) ≤ (d + 1)c_va_ksup abs(A). #4.53-1.1 and #4.53-1.1-1 apply this at W = U^A(V′^A₀) and W = MU^B. C′_Δ(M) and c_{δD} gain the factor d + 1 on their c_v terms (#4.53-1.2) |
| m1 | #4.55-1-1 | C_h's list of dependencies left out d, L, and G (through √N), and the prefactors | C_h is the sup over n of the factors with their prefactors (C_A(M) and 2C(M)²(1 + β₀)²) times L^{−(s−¼)(1−ε₀)n}, a constant of d, L, G, M, ε₀, ḡ, j(C), r, b′, C_W, the note's constants in these prefactors, and Bałaban's constants |
| t1 | #4.50-1.1.0-0 | "Fixed multiples of ε₁" needs ‖𝔛‖_∞ ≤ ε₁/4 and ε/a_n ≤ 1 | The clause now reads "both fixed multiples of ε₁ by #4.51-1.1's ‖𝔛‖_∞ ≤ ε₁/4 and ε/a_n ≤ 1" |
| t2 | #4.51-2, #4.54-0.0 | "∂_tU^X is the field H₁𝔛" holds only up to a gauge transformation | #4.51-2 defines {#D.U^X_t} U^X_t as the curve that starts at U^X(V′^A₀) and moves by H₁𝔛, H₁ being VAR's data derivative in the Landau gauge relative to U^X_t (VAR (100)–(102)). #4.51-2-1 (split off at a sentence boundary) states that it is the run's critical configuration at V′_t up to a gauge transformation of REG (1.14), by VAR Theorem 1's unique critical orbit (p.279 l.8–15); a_y and a_y^B are gauge invariant. #4.54-0.0 takes U_t the same way |
| t3 | #4.53-1.1 | The bound on H₁𝔛 was re-derived, not cited | It now cites #4.46-0 at U^A_t: "a_k abs(H₁𝔛) ≤ dB₀c_tot(1/128)‖𝔛‖_∞ by #4.46-0 at U^A_t". This is #4.46-0's bound on a_j abs(H₁Y), not #4.51-2's ‖·‖_{y′} bound, which is twice as large |
| t4 | #4.44-2 | LFR II (1.8) is printed with abs(·) | The parenthesis now reads "(both #T6.23; (1.8), printed with abs(·) at p.358 l.10–12, holds at B′ = fX, abs(X) = 1, for real f, and so in ‖·‖ by summing over a ‖·‖-orthonormal basis of 𝔤)" |
| t5 | provenance | "2016 lines", while wc -l gives 2015 (the LF has no final newline) | build_packet.py's single-note branch now counts newlines (lfb.count(b"\n")), as its multi-note branch does |

## Re-derivation of S1

- **The gauge freedom.**
  - Minimisers at given data form one orbit of the gauge transformations REG (1.14), u = 1 on the data centres (VAR Theorem 1, p.279 l.8–15).
  - The averages are covariant at the scale-m centres: (Ū^u)^m_b = u(b₋)Ū^m_bu(b₊)^{−1} (REG p.078).
  - So the data of U″_k at scales m < k depend on the representative.
- **The common gauge.**
  - LFR I takes U_0 "in the axial gauge in k-blocks" (p.197 l.9). Its conditions contain Ax_k(𝔹_k(Λ), 1) (#4.561.1-1.3-1.0).
  - At the base 1, REG (1.19)–(1.20) read: the ordered product of the scale-n averages Ū^n along Γ_{x_{n+1},x_n} is 1, since Ũ′^n = Ū^n and R(1) = 1.
  - The contours are PRT1 (1.7) (p.018 l.44–50): coordinate segments in B(x_{n+1}), whose point x_{n+1} is a corner (CMP98 (2), PRT1 (1.6)), so at most d(L − 1) bonds of the level n. They depend only on the block.
  - Run B's level n + 1 is run A's level n, with the same blocks, and its averages there are M^n(MU^B) (composition of the averagings). So MU^B_0 satisfies run A's conditions at the shared levels.
  - Each run's U_0 is in this gauge already, so no change of gauge is needed. (1.84) and #4.561's use of it stand.
- **The lemma (#4.53-1.0-1).**
  - Setting: W is in the gauge, satisfies (52), and V = e^{iεA}W has W's data, with a_ksup abs(A) < α₁^{CMP}.
  - Let V^u be V's element in the gauge. Then u = 1 at the block points of the scale k.
  - (1.19) for V^u along Γ_{x_{n+1},x_n} is u(x_{n+1})P_Vu(x_n)^{−1} = 1, so u(x_n) = u(x_{n+1})P_V.
  - P_W = 1, so by unitarity and #4.53-1, abs(P_V − 1) = abs(P_V − P_W) ≤ Σ_{b⊂Γ} abs(M^n(V)_b M^n(W)_b^{−1} − 1) ≤ d(L − 1)c_va_nsup abs(A).
  - Summing over the levels n < k, with Σ_{n<k}a_n ≤ a_k/(L − 1), gives abs(u − 1) ≤ dc_va_ksup abs(A) at the block points below k.
  - u₋Xu₊^{−1} − Y = (u₋ − 1)Xu₊^{−1} + X(u₊^{−1} − 1) + (X − Y), so abs(M^m(V^u)_b − M^m(W)_b) ≤ 2dc_va_ksup abs(A) + c_va_msup abs(A) ≤ (2d + 1)c_va_ksup abs(A).
- **The brackets.**
  - U^A_1 (the flow's endpoint) and e^{iεA′*}MU^B (#4.38) are both in run A's critical orbit at V′^B₀, so both have the same element U^A(V′^B₀) in the gauge.
  - First bracket: the lemma at W = U^A(V′^A₀), with a_ksup abs(A) ≤ (π/2)dB₀c_tot(1/128)‖𝔛‖_∞.
  - Second bracket: the lemma at W = MU^B, with a_ksup abs(A′*) ≤ c_{A′}(ε/a_n)^{1−ε₀}ε₁.
  - At m = k the second bracket vanishes, since both elements have the data V′^B₀, and the first is the difference of #4.53's first sentence.
- **Consumers.**
  - C′_Δ(M) = (1 + (π/2)(2d + 1)c_vdB₀c_tot(1/128))C_Δ(M) + (2d + 1)c_vc_{A′} bounds max(‖𝔛‖_∞, the sum of the brackets).
  - c_{δD} = ¼(1 + (π/2)(2d + 1)c_vdB₀c_tot(1/128)) + (2d + 1)c_vc_{A′} at ‖𝔛‖_∞ ≤ ε₁/4 and π_n ≤ 1.
  - ε_{D″}, C_pr, C_A(M), and C_h cite these by name, so their formulas are unchanged. α₁^{CMP} is twice the bounds on a_ksup abs(A) and a_ksup abs(A′*), which are unchanged.
  - #4.561.1-1.3-0 now cites #4.52-1 for ū₀ and #4.52-1-1 for LFR I's gauge.
  - A grep for "#4.52-1's gauge", "one gauge", the old C′_Δ and c_{δD} formulas, and "∂_tU" found no other use.

## The same point in §3 (#3.27-1), repaired

- **The point.** The referee noted that #3.27-1 uses CMP 98 (159)–(163) with VAR minimisers for M^j differences in the same way.
  - LFR I (1.27) tests V_j against M^j of a cascade minimiser at bonds of the scale j.
  - These averages depend on the representative. (P′) (#5.19) bounds only the representative e^{iεA′*}MU^B.
- **The gauge.** LFR I p.187 l.36–37 performs "all the operations discussed in Sect. 3 [III]", [III] being CRE (LFR I p.202). CRE takes the background in the axial gauge U(y, x) = 1, x ∈ B(y) (p.248 l.35–36, and p.266 l.34 for V^{(k)}_{□′}). For LFR I's cascade this is inferred, not printed, and the line says so.
- **The levels.** By LFR I (1.16) at j + 1, 𝐁^{(j+1−h)}_k contains (Ω_{j+2}^c ∖ Z″_{j+1})^{(j+1)}. So at the tested bonds (Ω_{j+1}^c ∖ Z″_{j+1})^{(j)*} the data are at the scale j + 1, one level above the bonds.
- **The bound.**
  - The contour Γ_{y,x}, y ∈ T^{(j+1)}, has at most d(L − 1) bonds of the level j (y a corner of B(y)), each with the note's per-bond bound 2c_vρ̄_j.
  - With u = 1 on T^{(j+1)}, this gives abs(u − 1) ≤ 2d(L − 1)c_vρ̄_j at the scale-j points.
  - The difference is then ≤ 4d(L − 1)c_vρ̄_j + 2c_vρ̄_j = 2c_{ax}c_vρ̄_j, with {#D.c_ax} c_{ax} := 2d(L − 1) + 1.
  - Run B's scale-j averages are M^j(MU^B), on the same contours, so MU^B satisfies run A's conditions.
- **Repair.**
  - #3.27-1 now states the (P′) bound for (P′)'s representative.
  - The new #3.27-1-1 states the gauge and the conversion, citing #4.53-1.0-1's argument.
  - #3.28-1 carries c_{ax} (4c_{ax}c_vρ̄_j, and 2c_{ax}c_vρ̄_j/δ′_j relative to the threshold).
  - #3.31 takes the C of δ^f_j at least 2c_{ax}C_{1.27}.
  - #3.26-3 and #3.30-1 bound c_vρ̄/δ′ and are unchanged. #3.28-2-1's abs(B′_j) < 6δ′_j is within one run and is unchanged.
- **Rounds.** This reopens packet 12a (#3.25–#3.36). Its changed lines (#3.27-1, #3.27-1-1, #3.28-1, #3.31) need a 12a round, queued after 13b r9.
- **Checks.** Line lengths are 519, 605, 491, and 327. No duplicate tags. LF ebbb8dc3b2e2 → 4edad5d591ef.

## Pre-check of lf-p12a-20261108-r14 (focused)

- **Spec.** specs\spec_p12a_r14.json at LF 315b050eea14 (after the corner correction of WILSON_IT1_LF_TRIAGE_P13B_R9_2026_11_08.md, re-derived there), prior r13. Under review: #3.25–#3.36 and #4.53-1–#4.53-1.0-2. --check gives 0 conflicts (1 allowed). Built: 16,013 argument characters, table 6d09b1b5054d, labels 971e7d7d5325 (possibly stale, as the spec says).
- **The gate's changed tags since r13 (13), all in extracts under review:**
  - #3.27-1, #3.27-1-1, #3.28-1, and #3.31: the repair above, re-derived there.
  - #4.53-1, #4.53-1.0, #4.53-1.0-1, and #4.53-1.0-2: the CMP 98 bound and the lemma, re-derived in S1's re-derivation.
  - #3.26-4: adds the citation #3.84-1 for "𝐁_k(Z) consists of k-blocks"; #3.84-1 states it (CRE's top domain of k-blocks).
  - #3.28-2-1: now reads "where the (1.27) argument is < (1 + 2κ_s)2δ′_j, abs(B′_j) < 6δ′_j (#3.28-1)". There abs(V′_j − 1) ≤ (1 + 2κ_s)2δ′_j plus a term much smaller than δ′_j, which is < 3δ′_j at κ_s = 1/240, so abs(B′_j) < 6δ′_j by (1.54).
  - #3.28-2-2: the small solution of CRE (1.22), with 𝐅 the BCH terms of order above 1 (p.251 l.45–46, p.252 l.6–8). abs(g_jB_j) ≤ abs(B′_j) + abs(ℍ) + C abs(B′_j)abs(ℍ) < 6δ′_j + δ′_j/2 + o(δ′_j) < 7δ′_j.
  - #3.28-2-3: the bound abs(ℍ_Z^{(j)}) < δ′_j/2 and the g_c < 1 case, moved from #3.28-2-2 unchanged.
  - #3.35: the rename (R-s) → (RS), which the note uses throughout (8 uses, none of (R-s) left).
- **Consumers checked.**
  - #3.26-3 and #3.30-1 bound c_vρ̄/δ′, with no gauge conversion. #3.26-3's tests are plaquette tests, which are gauge invariant.
  - #3.30-2's dependence list is unaffected: c_{ax} enters through #3.31's C, a constant of d and L.
- **Size.** Part 12a's #3.25–#3.36 grew by #3.27-1-1 (605 characters) and the longer #3.27-1, for the new mathematics. The packet is built at launch time.
- **Labels.** The labels may be stale; the spec says so.

## Rounds

- The user asked for one focused check each on 13a. 13a1 had r8 and 13a2 had r10, so these repairs wait for 13a's next round.
- The exception is #4.52-1 and #4.52-1-1, which 13b's #4.561.1-1.3-0 cites. They go under review in 13b r9, with a question (Q7).

## Checks

- No duplicate tags. No CRLF.
- Edited lines are ≤ 600 characters. The longest are #4.44-2 (568), #4.53-1.1 (553), #4.55-1-1 (552), and #4.561.1-1.3-0 (558).
- New tags:
  - {#4.51-2-1}, {#4.52-1-1}, {#4.53-1.0-1}, and {#4.53-1.0-2};
  - the D-tag {#D.U^X_t}.
- Part 13a2 (#4.51–#4.55-1-1) went from 12,585 to 14,614 characters: +2,029 for the new mathematics (the common gauge, the lemma, and the flow).
- Table rows to request from the fork:
  - C′_Δ(M) and c_{δD} (the factor 2d + 1, corrected in WILSON_IT1_LF_TRIAGE_P13B_R9_2026_11_08.md);
  - U^X_t;
  - the reading of LFR I's gauge (#T11.29-2: REG (1.19) at the base 1 along PRT1 (1.7)).

## SHAs

LF 3b7b6d176dd2 → ebbb8dc3b2e2.

## Pre-check of lf-p13b-20261108-r9 (updated)

- **This update's changes.**
  - The 13b spec's lf_sha is now ebbb8dc3b2e2.
  - #4.52-1–#4.52-1-1 go under review, with Q7.
  - The claim's gauge clause now cites #4.52-1 and #4.52-1-1.
  - C₁'s allow_defs entry now carries the factor N.
  - The provenance states the r10 repair and that the labels may be stale.
  - PRT1 (1.7) and REG (1.14) are added to the permitted background.
- **Changed 13b lines.**
  - The only one is #4.561.1-1.3-0, whose citation was re-pointed. It was re-read: (1.84) holds for each run's U_0 in LFR I's gauge (#4.561.1-1.2-1), as before.
  - --check gives 0 conflicts (6 allowed).
  - The gate's changed tags are all in extracts under review.
- **Consolidation lines the gate lists, re-read now** (they were changed in the consolidation of packet 13, and were not named in the earlier pre-check):
  - #4.560-0: ε₁′ := C(M)R_kε′_k, with ε′_k's term 25g_kb_k covering exp(ig_kB) on the line.
  - #4.560-1.1.2: ‖𝔛‖_∞ ≤ c_{rp}C_𝔛(M)ε′_k ≤ ε₁′/4 needs C(M)R_k ≥ 4c_{rp}C_𝔛(M), which holds by C(M) ≥ 4c_{rp}C_𝔛(M) (#4.43-1.2) and R_k ≥ 1. The bound is in the operator norm, as #4.50's is after 13a1 r8's m1.
  - #4.561.1-3: VAR's C₁ is C_{V′} + 2C_U(M) + 5C_p, and ε₂^ι = 6B₁B₃C₁ε₁′, as (173) gives at that C₁ (the pattern of ε₂^{AL}).
  - #4.562-1: α_{i,m} = const·g_m(log g_m^{−2})^{q_i} with q_i ≥ 0, and g_m ≤ (1 + β₀)g_k. Monotonicity gives α_{i,m} ≤ const·(1 + β₀)g_k(log((1 + β₀)^{−2}g_k^{−2}))^{q_i} ≤ (1 + β₀)α_{i,k}.
  - #4.563-1: V_k(z) = e^{iB^e(z)}V_k(0) with abs(B^e(z)) ≤ 2c_avε′_k, which is #4.561.1-1's bound.
- **Earlier items.** The pre-check items in WILSON_IT1_LF_TRIAGE_P13B_R8_2026_11_08.md stand.

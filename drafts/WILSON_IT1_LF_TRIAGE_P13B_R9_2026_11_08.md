# Triage of lf-p13b-20261108-r9

## Verdict

- r9 was a full round of 13b (#4.556–#4.565-1, #4.567–#4.568), with #4.52-1 and #4.52-1-1 under review (Q7), at LF ebbb8dc3b2e2.
- **Fatal:** none. **Serious:** none.
- **Minor:** two. m1 is the segment problems on the disc. m2 is the name clash on r.
- **Observations:** six, o1–o6.
- The round is not clean, so 13b's clean count stays 0.
- Round 8's m1 and o2–o5 were confirmed repaired, and #4.52-1 and #4.52-1-1 were found correct against LFR I p.197, REG (1.14)–(1.19), and PRT1 (1.7).

## Repairs

| Finding | Line | Issue | Repair |
|---|---|---|---|
| m1 | #4.561-1 | Proposition 9 was claimed for the segment problems whose base is regular with 2ε₁′, at complex z. But the segment datum's continuation to the disc was not defined, and its deviation was not among #4.561.1-2's bounded data | The claim is deleted. #4.565 uses only the endpoints V′^A₀ and V′^B₀, whose data are regular with ε₁′, and no other line of 13b continues the segment. #4.561-1 now reads "At base data regular with ε₁′, C₁ = C_{V′}." The next 13b spec drops "segment problems" from its claim |
| m2 | #4.567-1 | r := ½C_{V′}ε₁′ reused r ({#D.r}, 1/(36dL)), and R_k's exponent r, which C_h depends on (#4.55-1-1) | Renamed ρ_V. The move is now W_d, not W (o2) |
| o1 | #4.561 | 26ε₁′ in (T-c) is stronger than needed | No change, as in round 8: (T-c) is used at abs(z) < 25 with 26 for 25 (#4.505) |
| o2 | #4.558-1, #4.567-1 | η (the damping exponent) clashes with the lattice spacing η, and W with {#D.W} (#3.88) | The exponent is 𝔭, with {#D.𝔉_𝔭} 𝔉_𝔭. The move is W_d |
| o3 | #4.556-1 | Ũ(z) has no pointer | "the averaged run-B configuration on the line (#4.504)" |
| o4 | #4.560.1 | c_rp is well defined | No action: CMP98 Proposition 2 fixes it as VAR uses it |
| o5 | #4.568 | Only the s = ⅓ prefactors are named in #4.55-1-1 | #4.568 now names its prefactors: C_dc(M), max(C_F(M), 2c_4), and #4.55-0.1's 2C(M)²(1 + β₀)². #4.55-1-1's C_h is the sup over n at each s used, with these prefactors |
| o6 | #4.52-1-1 | "k-centres" and "centres" are the block points y, which are corners (PRT1 (1.6), CMP98 (2)) | Renamed "the block points of the scale k ..., the corners y of the blocks B(y)". This corrects the contour length in #4.53-1.0-1 and #3.27-1-1 (below) |

## The corner correction

r10 of 13a2 and the §3 repair assumed centred blocks, so they gave at most d(L − 1)/2 bonds per contour. With y at the corner, y_μ ≤ x_μ < y_μ + L (CMP98 (2), PRT1 (1.6)), the contour Γ_{x_{n+1},x_n} of PRT1 (1.7) has at most d(L − 1) bonds.

**Re-derivation of #4.53-1.0-1 and #4.53-1.0-2.**
- (1.19) for V^u along Γ_{x_{n+1},x_n} is u(x_{n+1})P_Vu(x_n)^{−1} = 1, so u(x_n) = u(x_{n+1})P_V.
- P_W = 1, so by unitarity and #4.53-1, abs(P_V − 1) ≤ d(L − 1)c_va_nsup abs(A).
- So abs(u(x_n) − 1) ≤ abs(u(x_{n+1}) − 1) + abs(P_V − 1). With u = 1 at the scale-k block points and Σ_{n<k}a_n ≤ a_k/(L − 1), this gives abs(u − 1) ≤ dc_va_ksup abs(A) at the block points below k.
- u₋Xu₊^{−1} − Y = (u₋ − 1)Xu₊^{−1} + X(u₊^{−1} − 1) + (X − Y). So abs(M^m(V^u)_b − M^m(W)_b) ≤ 2dc_va_ksup abs(A) + c_va_msup abs(A) ≤ (2d + 1)c_va_ksup abs(A), since a_m ≤ a_k.

**Consumers.**
- #4.53-1.1: (π/2)(2d + 1)c_vdB₀c_tot(1/128)‖𝔛‖_∞.
- #4.53-1.1-1: (2d + 1)c_vc_{A′}(ε/a_n)^{1−ε₀}ε₁.
- #4.53-1.2: C′_Δ(M) := (1 + (π/2)(2d + 1)c_vdB₀c_tot(1/128))C_Δ(M) + (2d + 1)c_vc_{A′} and c_{δD} := ¼(1 + (π/2)(2d + 1)c_vdB₀c_tot(1/128)) + (2d + 1)c_vc_{A′}.
- ε_{D″}, C_pr, C_A(M), and C_h cite these by name, so their formulas are unchanged. α₁^{CMP} bounds a_ksup abs(A), which is unchanged.

**§3 (#3.27-1-1).**
- At the one level j, with 2c_vρ̄_j per bond and u = 1 on T^{(j+1)}, abs(u − 1) ≤ d(L − 1)·2c_vρ̄_j = 2d(L − 1)c_vρ̄_j.
- The difference is ≤ 2·2d(L − 1)c_vρ̄_j + 2c_vρ̄_j = 2c_{ax}c_vρ̄_j, with c_{ax} := 2d(L − 1) + 1.
- #3.28-1 and #3.31 cite c_{ax} by name, so they are unchanged. c_{ax} is still a constant of d and L.

**Records corrected.** WILSON_IT1_LF_TRIAGE_P13A2_R10_2026_11_08.md (its re-derivations and the §3 section) and specs\spec_p12a_r14.json (claim, Q3, background with CMP98 (2) and PRT1 (1.6)) now carry the corrected constants. The handover entries of 04:16 and 04:20 are superseded by the entry recording this triage.

## Checks

- A grep of the LF finds no "(d + 1)c_v", no "d(L − 1)/2", no "k-centres", no 𝔉_η, and no segment claim in 13b.
- No duplicate tags. No CRLF.
- Edited lines: #4.52-1-1 597, #4.53-1.0-1 571, #4.53-1.0-2 215, #4.561-1 214, #4.563-2 433, #4.567-1 360, #4.558-1 387, #4.556-1 321, #4.568 444, and #3.27-1-1 607 characters.
- Re-derived #4.567-1 with ρ_V: ρ_V ≤ ¼ gives C_{V′}ε₁′ ≤ ½, so abs(V′ − 1) ≤ ⅛ and abs(V′) ≤ 9/8. So ρ_V abs(V′) ≤ (9/16)C_{V′}ε₁′, and the sum is ≤ (9/16 + ¼)C_{V′}ε₁′.
- Table rows to request from the fork: #T12.9-1's 𝔉_η → 𝔉_𝔭 and r → ρ_V; C′_Δ(M), c_{δD}, and c_{ax} with the corrected constants; and the corner reading of the block points.

## Rounds

- 12a r14 (focused) is next. 13b then needs r10, a narrow round on #4.561-1, #4.563-2, #4.567-1, #4.558-1, #4.556-1, #4.568, and #4.52-1-1.
- 13a's next rounds must cover the S1 repairs and the corner correction.
- **Queued (found while re-reading 13a2 for its next round).** #4.53-1.0-1 calls V := e^{iεA}W the configuration "which has W's data". In #4.53-1.1's application, W = U^A(V′^A₀) and V = U^A_1, whose data are V′^B₀, so the clause is false there. The lemma does not use it: u is fixed by u = 1 at the scale-k block points and by the contours, and at m = k, #4.53-1 bounds M^k(V) − M^k(W) directly. The repair deletes "which has W's data,". The line is under review in 12a r14, so this waits for that report.

## Pre-check of lf-p13b-20261108-r10 (narrow)

- **Spec.** specs\spec_p13b_r10.json at LF d9e8d74b97a1 (12a r14's cosmetic repairs, in §3 and #4.53-1–#4.53-1.0-1, outside these extracts), prior r9. --check gives 0 conflicts (6 allowed).
  - Under review: #4.52-1–#4.52-1-1, #4.556–#4.558-1.1, #4.561-1–#4.561-2, #4.563–#4.565-1, and #4.567–#4.568.
  - Context: #4.559–#4.561.1-3 and #4.562-1–#4.562-1.1, unchanged since r9.
  - It launches after 12a r14 reports.
- **Changed tags since r9, all under review:**
  - #4.52-1-1: the block points are corners. Re-derived above.
  - #4.556-1: Ũ(z) is #4.504's "Ũ(z)", against which A(z) is the alignment field of run A's configuration. #4.504 shows it is analytic for abs(z) < 25.
  - #4.558-1: 𝔉_𝔭 replaces 𝔉_η, with η → 𝔭 throughout the line; the argument is unchanged. 𝔭 is not D-tagged elsewhere.
  - #4.561-1: the segment clause is deleted (m1). Its consumers #4.561-1-1–#4.561-2 use only ε₂ = B₅^cε₁′. #4.563 and #4.565 use only the endpoints, whose data are regular with ε₁′ (#4.51-1.1). #4.504's real points regular with 2ε₁′ are those of the line, not the segment, and are covered by (T-c) through #4.505.
  - #4.563-2: U^r's plaquettes ≤ 2C₀^{ms}ε₁′/a_j² by #4.48.0-0 at ε_r = ε₁′. The weaker 4C₀^{ms}ε₁′ feeds c_pl in #4.563-2.1. #4.563-2.2's c_4 hypothesis (2C₀^{ms}·2ε₁′ + 4α₁)/a_j² is implied.
  - #4.567-1: ρ_V and W_d (m2, o2), re-derived under Checks. #4.567's domain abs(V′ − 1) < C_{V′}ε₁′ is the one the radius keeps.
  - #4.568: the prefactors are named (o5). #4.55-1-1 takes C_h as the sup at each s used, with the prefactors, so s = 5/16 is covered.
- **Claim wording.** The r9 claim's "also for the segment problems of (c) whose base is regular with 2ε₁′" and "at both bases by (b)'s multiscale bound at ε_r = 2ε₁′" are gone from the r10 claim.
- **Symbols.** ρ_V, W_d, and 𝔉_𝔭 occur nowhere else in the LF or the table. #T12.9-1's old 𝔉_η and r are in the rows requested from the fork.
- No known weak point and no OPEN is in these lines.

## SHAs

LF ebbb8dc3b2e2 (r9's snapshot) → 4edad5d591ef (the §3 repair) → 315b050eea14 (the corner correction and these repairs). Table 6d09b1b5054d.

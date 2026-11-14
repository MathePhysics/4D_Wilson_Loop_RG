# Triage: LF packet 13b, round 2 (lf-p13b-20261106-r2), 7 Nov 2026

## Verdict

Not clean: one serious finding (S1) and six minor ones (m1–m6). No fatal finding. The clean count of 13b stays 0.

LF reviewed at 724946123ea0; repaired LF b94d3e5f0d86, then 400c5fa76246 after the fork's cosmetic note. The fork entered the rows #T3.33, #T12.9, #T12.9-1 and #T12.12, which I re-checked against the LF: table d3fd1c0fcdf7, LABELS a02a0e60471e at LF b94d3e5f0d86. It relabels again at 400c5fa76246.

## Repairs

| Finding | Where | Repair |
|---|---|---|
| S1 (serious): C_{V′} covered the Λ part of the disc data only through §4(d)'s "chain's arguments ≤ 26C_Ψε̂′", which presupposes *The disc.* (circular) | #4.561.1 (rewritten), #4.561.1-1, #4.561.1-1.1, #4.561.1-2, #4.561.1-3 (new), #4.563, #4.563-1, #4.563-1.1 | The data of the disc are bounded without the chain. Averages of 𝐔(z): #4.523's path bound with (2.39), 26c_avα̂₁ at z and c_avα̂₁ at 0, so the move is ≤ e^{27c_avα̂₁} − 1 ≤ 54c_avα̂₁ ≤ c_avε′_k (ε′_k ≥ 60α̂₁). Fixed unitaries (the integration variables on Λ, exp(ig_kB)) move nothing and leave products' moves unchanged. Data built from U_0: B^e(z) := (1/i)log(V_k(z)V_k(0)^{−1}), abs(B^e) ≤ 2c_avε′_k; LFR II (1.38)–(1.42) with the replacement of p.366 l.36–37 give V′^X₀(z) = exp(iB^Λ)V′^X₀(0) in the axial gauge, abs(B^Λ) ≤ 4d(100M)⁵γ₀^{−1}B₃²abs(B^e) (1.41); (1.43)–(1.45) give M^j(U_0(z)) = Ṽ_{j,Z}M^j(U_0(0)), abs(Ṽ − 1) ≤ c_ṼB₃B₅M⁵abs(B^e), on every domain of 𝐁_k(Z) and on Λ. So abs(V′ − 1) ≤ C_{V′}ε′_k with C_{V′} := 4c_av(1 + 4d·100⁵γ₀^{−1}B₃² + c_ṼB₃B₅)M⁵, M-dependent (M is fixed before γ). The plaquette move of V_k(z) is ≤ 16c_avε′_k, so abs(∂V_k(z) − 1) < 20C_{V′}ε₁′ still holds |
| S1, consumer | #4.198, #4.198-0, #4.198-0.1 (new), #4.198-1, #4.199, #4.200, #4.522 (§4(d)) | #4.198's arguments are now derived from *The disc.*: (1.51) and (1.58) are fixed; the averages of (1.57) and the current J_{1,2} of U_{1,2} belong to minimisers at the disc data, which Proposition 9 gives with (19) at ε₂, up to the u of *The transformation.*; 𝐆″_k keeps its kernel bounds within a factor 2 on 𝒟̄. The factor 26 becomes ϰ_c := 2 + c_ϰB₅^c/C_Ψ throughout #4.198-1–#4.200 and in #4.522; 𝔐 := 8ϰ_cC_L(c_pl + ϰ_cC_𝐇)C_𝐇c_tot(1/24)w̄ε̂′². §4(d) is reviewed in its own packet |
| m1: ε₂ tagged 8B₅ε₁′ but used as B₅ε₁′ | #4.561-1, #4.561-2, #4.563-2, #4.563-2.1 | ε₂ := B₅^cε₁′, Proposition 9's value; the representation's regularity is 8ε₂ (p.305 l.54), so ε₃ = 32ε₂; the field-strength move reads 3ε₂/a_j² |
| m2: the 26ε₁′ data move not derived | #4.561.1 | Derived from #4.523's path bound (see S1); c_av := the O(1) ≥ 1 of #4.523 |
| m3: Sect. E's uniqueness condition missing | #4.561-1 | ε₄ = 64ε₂ ≤ a₄ (p.296 l.9), which also gives Proposition 6's 2B₀C_{V′}B₃ε₁′ ≤ ε₄, since B₁ = 5dLB₀ |
| m4: c_4's hypotheses at the disc minimisers | #4.563 (last sentence moved), #4.563-2.2 (new), #4.561-1.2 | The Landau representative e^{iη𝐇}U^r lies in 𝒟̄ (U^r by VAR (9)–(10) as in #4.336, 𝐇 by (19) with ε₂ < α₁); its plaquettes are ≤ (2C₀ε₁′ + 4α₁)/a_j² by 3ε₂ ≤ 4α₁; its current is ≤ C^c_Jε₁′a_j^{−3} < α_Ja_j^{−3} as in #4.364; its lifts obey (3.133) on 𝒟̄. The forms' continuation in z is their value there by the identity theorem, as in #4.517. The three conditions are added to (T-c) |
| m5: the Landau transformation is G^c-valued | #4.563-2, #4.563-3 | Stated; the plaquette term 1 − ½tr(X + X^{−1}) is invariant under G^c conjugation, so it is evaluated at the Landau representative |
| m6: overloaded symbols | #4.557–#4.558-1.1; #4.562-1; #4.561-1, #4.563-2.1, #4.364, #4.506, #4.517 | The Lemma's 𝔯, 𝔯₁, 𝔪, 𝔐 are now 𝔳, 𝔳₁, 𝔨, 𝔎 (no clash: 𝔳, 𝔨, 𝔎 unused before); #4.562-1 writes α̂_i ≤ (1 + β₀)α_{i,k} without CRE's C_i; the disc's B₅ is B₅^c, also in C^c_J (#4.364) and in #4.506 and #4.517, where "ε₂ ≤ 8B₅^cε₁′" now reads "ε₂ = B₅^cε₁′" (the table fork's cosmetic note, 7 Nov) |

## Pre-check, lf-p13b-20261107-r3

- Changed lines re-read in full: #4.557–#4.558-1.1, #4.561.1–#4.561-2, #4.562-1, #4.563–#4.563-3; in §4(d) #4.198–#4.200, #4.364, #4.506, #4.517, #4.522.
- Cited displays re-read in the transcriptions:
  - LFR II p.366 (1.38)–(1.39) and l.36–42, p.367 (1.40)–(1.45) and l.30–32, l.45–46;
  - VAR p.305 (173)–(175) and l.44, l.54; p.309 Proposition 9; p.296 l.9, l.19–21; p.281 (19)–(21);
  - LFR II p.370 (1.53)–(1.54) and l.45–50, p.371 l.5, l.21 (J_{1,2});
  - LF #4.523, #4.60, #4.201, #4.336, #4.364, #4.517, table #T4.30.
- Quantifiers and directions: |e^Xe^{−Y} − 1| ≤ e^{|X|+|Y|} − 1; e^t − 1 ≤ 2t for t ≤ 1 (at 27c_avα̂₁ and at 4abs(B^e) ≤ 8c_avε′_k); |log W| ≤ 2|W − 1| for |W − 1| ≤ ½; abs(B^Λ) ≤ 1. All follow from C_{V′}ε₁′ ≤ ½ in (T-c), since C_{V′} ≥ 4c_av and C_{V′} ≥ 16c_avd·100⁵γ₀^{−1}B₃²M⁵.
- Grepped: C_{V′}, B₅, ε₂, 26ε₁′, 52ε₁′, B′(z), 26C_Ψ, 26C_𝐇, 𝔯, 𝔪, 𝔐, c_pl in the LF, the table, the Cauchy note and balaban_proofs. The consumers #4.506, #4.511 and #4.550 (C_{V′}ε₁′), #4.567 (cites #4.561.1) and #4.566 (2c_4) need no change. 𝔪, 𝔐 at #4.197–#4.199 are the global ones.
- New symbols clash-checked: c_av (the table's C_av is capital; allow_defs entry), c_Ṽ, B^e(z), B^Λ(z), B₅^c, ϰ_c, c_ϰ, 𝔳, 𝔳₁, 𝔨, 𝔎.
- D-tags all carry ":=" (the fork's relabel caught c_av; fixed, with c_Ṽ).
- No forward tag citations: #4.198-0 and #4.198-0.1 name *The disc.*, *The transformation.*, "The room at complex points" and *At complex points.* by section.
- Lines: the new and changed 13b lines are ≤ ~620 characters (#4.561.1-1 and #4.198-0 were split). The long #4.364 and #4.517 are pre-existing and changed by one symbol only.
- Part size: 17,887 characters of reviewed blocks at r3 (≤ 25k). The growth is S1's new derivation (the data of the disc) and m4's c_4 hypotheses.
- Spec: the stale D entry (#4.51's D is now δΦ) was removed, and the C₁ and V′_t entries were re-pointed to #4.50-0 and #4.51-1.1.
- Built: reviews\lf-p13b-20261107-r3 at LF ff32ad403ddb, table d3fd1c0fcdf7, LABELS 3371dd395591, with 0 definition conflicts (6 allowed); a build at 400c5fa76246 was never launched and was removed (the LF change in between is 13a2's #4.54-0 split, outside 13b).

## Pre-check, lf-p13b-20261108-r3 (replaces the unlaunched lf-p13b-20261107-r3), 8 Nov 2026

The build lf-p13b-20261107-r3 was never launched. Its snapshot predates 13a2's r7–r9 repairs, so it would have put 13a's old #4.54-0.1.1 (RM on 𝐁″_k, r7 m1) into the referee's permitted background. It also predates the table's later rows. So r3 is rebuilt at the current LF; the old folder is not used.

Gate answers, all yes:
- **Whole part read for gaps** before this full round: every line of #4.556–#4.565-1, #4.567 and #4.568. One defect was found and repaired in place, in #4.568:
  - Its citation "k + 1 ≤ 8n + j(C) (#4.55)" pointed to a line that does not state it. It now cites #4.55-0.1, which gives k ≤ K < 8n + j(C), so k + 1 ≤ 8n + j(C) for integers, together with the log g_k^{−2} bound.
  - The line now names #4.562-1 for ε₁′ being g_k times a power of log g_k^{−2}.
  - It also states, as #4.55-1 does, that C_h is at least the sup over n of the class factors times L^{−(1−ε₀)n/16}.
- **The changed line is re-derived.**
  - 5(1−ε₀)/16 = (1−ε₀)/4 + (1−ε₀)/16, and θ̃ ≥ L^{−(1−ε₀)/4}, so L^{−5(1−ε₀)n/16} ≤ θ̃^nL^{−(1−ε₀)n/16}.
  - The factors are polylogarithmic in 8n + j(C) times linear in it, so their sup against L^{−(1−ε₀)n/16} is finite and independent of K.
- **Other lines checked against current text.**
  - #4.565-1's exponent: (1/3)(15/16) = 5/16.
  - #4.566's r̄_n = C_F(M)(ε/a_n)^{(1−ε₀)/3} (#4.201), with ε₁′ ≤ 1 for c_4c_alε₁.
  - #4.560-1.1.2's ε₁′/4 is as #4.51-1.1 uses it.
  - (T-c)'s "(T-Λ) with 26ε₁′" now includes #4.50-1.1.0-0's CMP 98 conditions, which are fixed multiples of ε₁, at 26ε₁′.
- **Changed since r2, each re-read and re-checked.**
  - Lemma and proof: #4.557, #4.558, #4.558-1 and #4.558-1.1.
    - 𝔴 maps D₊ onto the first quadrant.
    - Re 𝔥 = 1 − (2/π)arg 𝔴.
    - Re(𝔳² − z²) ≥ 𝔳² − |z|² > 0 and |(𝔳² − z²)/(4𝔳²)| ≤ ½, so |𝔉_η| ≤ |𝔉| and 𝔉_η → 0 at ±𝔳.
    - 𝔢(z̄) = 𝔢(z).
    - (4/π)arcsin(1/24) < 0.054 < 1/16.
  - The a priori location: #4.560-1.1.2.
  - The data of the disc: #4.561.1, #4.561.1-1, #4.561.1-1.1, #4.561.1-2 and #4.561.1-3.
  - VAR's constants and thresholds: #4.561-1, #4.561-1.1, #4.561-1.2 and #4.561-2. #4.561-1.1's pins were re-read:
    - VAR p.293 l.6 (a₃ depends on d and L only) and p.279 l.28 (B₃ likewise);
    - p.295 l.48 (a₄ "absolute") and p.296 l.11 (B₁ = 5dLB₀);
    - CMP98 p.39 l.2 (C₂ depends on d, c₄ on d and L, both independent of k);
    - PRT2 p.234 l.3 (c₁(α) = 12c₀^d(½α)).
  - (T-c) holds for γ small: #4.562-1 and #4.562-1.1. #4.562-1.1's R_k ≤ 2^{2r+1}L(log g_k^{−2})^r is #4.50-1.1.1-1's, at the run with the larger ε_k, and its exponentials are #4.50-1.1.1's.
  - The disc: #4.563, #4.563-1, #4.563-1.1, #4.563-2, #4.563-2.1, #4.563-2.2 and #4.563-3.
  - The absorption: #4.568.
- **Changes since ff32ad403ddb in the extracts.** Only the bookkeeping repoint in #4.561.1-2 and #4.568 (snapshot diff of #4.556–#4.565-1 and #4.567–#4.568).
- **Lines.** All are ≤ 621 characters (#4.560, #4.560.1, #4.561.1, #4.561-1 and #4.563-2 are 604–621).
- **Size.** About 17,970 characters of reviewed blocks (≤ 25k).
- **Linear order is kept.** 13a2 is done (r8 and r9 clean, r9 full), and 13b follows.
- **Spec and relabel.** The spec is specs\spec_p13b_r3_20261108.json, with lf_sha d9048cd9bbe1 and Q3 naming C_h. The definition check gives 0 conflicts (6 allowed). Relabelled at LF d9048cd9bbe1, table dbcd2978e308 and LABELS 650ad1cc1a89, all verified. The Cauchy note is e0c534fa3017.

# Triage: LF packet 13b, round 3 (lf-p13b-20261108-r3), 8 Nov 2026

## Verdict

Not clean: four minor findings (m1–m4) and three observations (o1–o3). There is no fatal or serious finding. 13b's clean count stays 0.

LF reviewed at d9048cd9bbe1 (table dbcd2978e308, LABELS 650ad1cc1a89, Cauchy e0c534fa3017). The referee confirmed:
- every round-2 repair, including S1: the disc data are bounded without §4(d)'s chain, and the dependence runs one way only;
- the Lemma's arithmetic, LFR II (1.38)–(1.45) quoted verbatim and used within scope, and the hand checks of C_{V′}, c_pl, C_act, C_dc(M) and #4.568's absorption.

## Repairs

| Finding | Where | Repair |
|---|---|---|
| m1: "the B₅ and ε₂ of (T-ι)" are not defined; (T-ι) writes a bare B₅, and the only tagged ε₂ is the members' B₅^cε₁′ | #4.508 (split; new #4.508-0), #4.509, #4.510, #4.561.1-3 | ι's parameter is defined where it is first used, in #4.508. Its data deviate by ≤ C_{V′}ε₁′ + M_c (*The flow.* below), so VAR's C₁ there is C_{V′} + M_c/ε₁′, and Proposition 9 (p.309 l.13–14) with (173) gives (19) at {#D.ε₂^ι} ε₂^ι := 6B₁B₃(C_{V′}ε₁′ + M_c), not the members' ε₂. #4.508-0 now has (19) as ε·abs(𝐇_{c^B}) ≤ Lε₂^ι and α′ := 2(2𝔯 + Lε₂^ι). (T-ι) is now 16dL²(16C_δ(ε₀)L^{7/3}M_c + Lε₂^ι) ≤ a₁^{PBG}, and #4.510 uses 2L²ε₂^ι. #4.561.1-3 states ε₂^ι = 6B₁B₃(C_{V′} + 2C_U(M) + 5C_p)ε₁′ (#4.508) and lists it among the M-dependent constants |
| m2: #4.504 and #4.513 (§4(d)) apply the Lemma "with 𝔪 = … and 𝔐 = 1"; the Lemma's names are now 𝔨, 𝔎, and 𝔪, 𝔐 are global | #4.504, #4.513 | Now "with 𝔨 = 2d̄′(x) and 𝔎 = 1" and "with 𝔨 = 2σ_c′(x) and 𝔎 = 1" |
| m3: #4.563-1.1 gets U_0(z)'s analyticity from Proposition 9 with #4.561.1-2's data bound, which rests on (1.44)–(1.45), which presuppose the extension (1.43) | #4.563-1.1 (split; new #4.563-1.2) | #4.563-1.2: U_0(z) = U_{k,Z}(V′^X₀(z)V_{Λ^c}(z)) is LFR II's extension (1.43), which exists by VAR Sect. G (p.367 l.26–31). Its data on the layers of 𝐁_k(Z) are M^j(U_0(z)) by the constraint (1.3), so by (1.44)–(1.45) they are within C_{V′}ε₁′ of the real ones (#4.561.1-2), and Proposition 9 applies to U_0(z) at them |
| m4: two citations. #4.567 cites #4.561.1 for abs(V′ − 1) < C_{V′}ε₁′; #4.561-1.2 cites p.366 l.42 for B̃′, but that line concerns B′ | #4.567, #4.561-1.2 | #4.567 now cites #4.561.1-2. #4.561-1.2 reads "the smallness of LFR II's B̃′ in (1.40)–(1.45) (p.367 l.13–14) …, and with it, by (1.41), that of the solution B′ (p.366 l.42)" |
| o3: two definitions of M_c in §4(d), {#D.M_c} (#4.282, a current bound) and {#D.M_c.2} (#4.504) | #4.282, #4.286.2-1, #4.286.2-2 | #4.282's bound is renamed {#D.M_{ιJ}} M_{ιJ}, and so are its uses in #4.286.2-1 (twice) and #4.286.2-2. M_c now has the single definition #4.504. M_{ιJ} is free in the LF, the table, the Cauchy note and the labels |
| o1: (T-c)'s "26ε₁′" is stronger than any step needs | none | No change: it is a valid, stronger condition that holds for γ small |
| o2: 27c_avα̂₁ ≤ 1 is not listed in (T-c), but it follows from C_{V′}ε₁′ ≤ ½ | none | No change: the referee derived it, C_{V′}ε₁′ ≥ 240c_avα̂₁ |

## Re-derivation

- **m1.**
  - VAR (173) sets B₅ = 6B₁B₃C₁ for data deviating by ≤ C₁ε₁ (p.305 l.41), and Proposition 9 gives (19) at ε₂ = B₅ε₁ (p.309 l.13).
  - #4.511 bounds ι's data deviation along the whole flow by C_{V′}ε₁′ + M_c, at t = 0 as well. So C₁ε₁′ = C_{V′}ε₁′ + M_c and ε₂^ι = 6B₁B₃(C_{V′}ε₁′ + M_c). With M_c = (2C_U(M) + 5C_p)ε₁′ (#4.504), this is #4.561.1-3's form.
  - On the finest layer, of spacing ε/L, (19) gives ε\|𝐇\| ≤ Lε₂^ι and ε²\|∇𝐇\| ≤ L²ε₂^ι. Then α₁ = 8dL²α′ = 16dL²(16C_δL^{7/3}M_c + Lε₂^ι), which is (T-ι).
  - The old "8LB₅ε₁′" took ε₂ = 8B₅ε₁′ (round 2's m1) with an unspecified B₅.
  - #4.240 (l.840) uses (T-ι) "with M_c + M_H for M_c". Since ε₂^ι is written through M_c, the substitution carries over.
  - (T-ι) is still a smallness condition on ε₁′ (#4.552).
- **m3.**
  - LFR II p.367 l.26–31 prints (1.43) "in the axial gauge. Existence of the analytic extension follows from the results of Sect. G [15], and from the results and bounds formulated above".
  - l.31–46 gives (1.44)–(1.45) on every domain of 𝐁_k(Z) and on Λ.
  - (1.3) (p.357 l.11–17) makes U_0's averages on Z ∖ Λ its data.
- **m4.** p.366 l.42 reads "where V′ = exp iB′, and B′ is sufficiently small". p.367 l.13–14 reads "exactly one solution B′_Λ(B̃′) … of the 𝐠^c-valued small field B̃′".

## Norm convention (raised by the table fork, 8 Nov)

- CMP98 (19) (p.21 l.8–16) defines \|X\| as the operator norm on ℂ^N. (20) gives \|tr X\| ≤ \|X\| and ‖X‖ ≤ \|X\| ≤ √N‖X‖, with ‖X‖² = tr X*X (l.7–8).
- The LF and the Cauchy note use \|·\| in this sense (#4.62, #4.115, #4.561.1-1, #4.563-3, #T11.35).
- LF #4.48.0-2.1 claimed "‖X‖_op ≤ √N\|X\| for the normalised trace norm", which is wrong for this \|·\|. It now reads "e^{η\|ℋ(b)\|} ≤ e^{\|ℋ\|_y} ≤ 2^{1/8}, \|·\| being the operator norm of CMP98 (19)". Here η\|ℋ(b)\| ≤ ‖ℋ‖_{y′} ≤ \|ℋ\|_y, since η ≤ a_j (#4.48).
- The needless √N is removed from the thresholds of #4.48.0 and #4.50-1.0, which become \|ℋ\|_y ≤ (log 2)/8. This weakens a smallness condition of 13a1 (done) to what the proof uses; no bound changes.
- So TL's c_π equals the LF's ‖dπ‖ exactly. A convention row was requested from the table fork, to be cited in LF #5.1, #4.48.0-2.1 and Cauchy #C10.3.34-3.

## Pre-check, lf-p13b-20261108-r4 (full round)

Gate answers, all yes.

**Changed lines in the extracts.** Each is re-read and re-derived above.
- #4.561.1-3: ι's C₁ and ε₂^ι.
- #4.561-1.2: the pins p.367 l.13–14 for B̃′ and p.366 l.42 for B′, re-read in the transcription.
- #4.563-1.1, cut at V′^X₀'s extension.
- #4.563-1.2 (new): (1.43) at p.367 l.26–31 and (1.3) at p.357 l.11–17. V_{Λ^c}(z) is now named as #4.43-1.1's V_{Λ^c} at V_k(z), without a second :=, as the table fork suggested.
- #4.567: cites #4.561.1-2.
- The gate also lists #4.561.1-2 and #4.568. Both are verbatim the same as in the r3 snapshot (LF d9048cd9bbe1; snapshot diff empty). The r3 referee confirmed both: #4.561.1-2's C_{V′} hand check, and #4.568's #4.55-0.1 citation and C_h. Both were re-derived in r3's pre-check.

**Changed lines outside the extracts.** They are permitted background, and their consumers were checked.
- In §4(d):
  - #4.282, #4.286.2-1 and #4.286.2-2: M_{ιJ};
  - #4.504 and #4.513: 𝔨, 𝔎;
  - #4.508 and the new #4.508-0, #4.509 and #4.510: ε₂^ι. #4.240's "M_c + M_H for M_c" carries over, since ε₂^ι is written through M_c.
- In 13a1, #4.48.0, #4.48.0-2.1 and #4.50-1.0: the operator norm (#T6.23), with the √N removed.
- LF #5.1 and Cauchy #C10.3.34-3 cite #T6.23.

**Symbols.**
- ε₂^ι and M_{ιJ} are free in the LF, the table and the Cauchy note.
- The table fork entered both in #T12.9, with α′ in #T12.9-1, and removed #T12.12's duplicate M_c.
- #T6.23 was checked against CMP98 (17) (p.020 l.34) and (19)–(20) (p.021 l.8–24).

**Other checks.**
- No known weak point is left.
- The observations o1 and o2 are valid stronger conditions, as the referee said.
- All new and changed lines are ≤ 568 characters.
- The reviewed blocks grew by about 200 characters, through m3's citation of (1.43) and (1.3).
- The spec is specs\spec_p13b_r4.json: lf_sha 0f55157a095f, prior r3, with #T6.23 and CMP98 (17), (19), (20) added to the background. The definition check gives 0 conflicts (6 allowed).
- Relabelled at LF 0f55157a095f and Cauchy c297b0730322: table 31436db32f84, LABELS c4013f2c7f07, both verified. The fork's definition check gives 0 on the LF and on the Cauchy note.

## Bookkeeping during r4 (two-loops' message, 8 Nov)

- **The weak pin.** LF #3.85.1 (§3, done) cited REG p.75 l.9 for the locality of the composed averages. That line (l.8–10) only mentions [3]'s compositions.
- **Re-derived.** RG I (0.4) (p.253 l.2–8) and (0.12) (p.254 l.2–6) read 𝐔 only along c and along the contours of 𝐆(c₋, x), [x, x′] and 𝐆(c₊, x′), x ∈ B(c₋). So Ū^n(c) reads Ū^{n−1} only on Δ(c₋) ∪ Δ(c₊) (BP_DERIVED_CONFIGS #BC.3-2).
- **Repaired.** The citation is re-pointed to these. The fact and the bound are unchanged, so it is bookkeeping. The line is split at its second sentence into the new #3.85.1-1. LF 0f55157a095f → 6e38d5fd2a97.

## Repaired SHAs

LF d9048cd9bbe1 → 9f2b6c71dbfb → 0f55157a095f (#T6.23 cited). Cauchy e0c534fa3017 → c297b0730322. Relabel requested from the table fork. New tags: #4.508-0 and #4.563-1.2. New symbols: ε₂^ι and M_{ιJ}.

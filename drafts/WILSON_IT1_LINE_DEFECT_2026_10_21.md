# IT-1: the loop as a line defect, first-step draft (21 Oct 2026)

- **Parent:** WILSON_V3_ITERATION_AUDIT_2026_10_21.md, gap IT-1.
- **Not edited:** WILSON_FIRST_RG_STEP_V3.tex (5206 lines, SHA-256 A520A59F…).
- **Status (21:20):** draft of the architecture.
  - One reframing (§0, a design choice) and one derived consequence (§2).
  - One lemma, derived up to a definitional check S1 (§3).
  - D1.1–D1.3 and D2 open.
  - Not reviewed.
- **Status (21:36):**
  - S1 is closed (§3).
  - D1.2a, the deviation bound on covered branches, is derived from V3 Appendix c4 and Lemma c5-5-7, with V3's inputs taken at their stated status (§3a).
  - S3 is closed for the groups that carry a deviation (§3a(5)).
  - D1.2b (analyticity), D1.1, D1.3 and D2 are open.
- **Status (21:50):**
  - D1.3 is derived in §3b. It was written after the 21:45 review packets were built, so it is not reviewed.
  - Six reviews are running.
- **Review (21 Oct, reports written 21:54–22:00):** §3 and §3a in packet it1-a-dev-20261021-r1; the header, gaps block and §§0–2, 4–7 in packet it1-b-frame-20261021-r1. Neither found anything fatal. Repairs:
  - it1-a-dev S-1: "outside S₁" was omitted. It now follows from Q_W ⊂ Λ₁ by CRE p.251, (1.20) and the filling (§3a(3)).
  - it1-a-dev S-2 and it1-b-frame S3: D1(ii) was vacuous as written. It is now the per-traversal form of §4, with a deviation part and attached parts.
  - it1-b-frame S1: D1 is now per labelled term, with the new gap D1.0 (assembly and CRE (1.26)–(1.28)).
  - it1-b-frame S2: D1 is now for C_n under (c5-7-T); rectangles are open.
  - it1-b-frame S4: the class is indexed by V3's groups and quantified.
  - it1-b-frame S5: D1.1's checklist now includes c5-6-1, c5-7 (I1), (I4) and the pending A, S₁ mode.
  - it1-b-frame S6: D1 is relabelled a candidate target.
  - The minor findings of both reports were repaired.
  - §3b is still not reviewed.
- **Status (22:25):** D1.0 worked in §3c, not reviewed.
  - At step 1, n₁ = Σχ₁T₁[F_ξ(1)·exp A₁] is derived, under readings R-a and R-b of CRE.
  - The label sum is V3 Lemma c5-6-1. The de-younged variables are internal.
  - Proposed: option (P), V3's labels as refined CRE labels. Its domain and T-form conditions pass (§3c(4′)).
  - 22:39: item (i), the Gaussian at the retreated regions, is derived in §3c(4″), under R-a and a new reading R-c.
  - 22:58: item (ii), the large-fluctuation factor at ϑr, is derived in §3c(4‴) from LFR II pp.380–385, under a new reading R-d. R-c is checked against CRE p.269. So D1.0 holds at step 1 with (P).
  - Reviews it1-c-d10 (§3c up to (4″)) and it1-d-d13 (§3b) were launched at 22:47. §3c(4‴) was written after that and is not in the packet.
- **Status (23:31):** both reviews read and repaired; neither found anything fatal.
  - §3b (it1-d-d13): the bound is now stated for the anchored decomposition, with a derived bound near each segment (S1). The pointer for D(Λ) is now the retreat of §c5-3 (S3). The fat shape of the sets X (S2) is a new open item under D2.
  - §3c (it1-c-d10): R-b is a fact, and R-a is replaced by a definition of V^{(0)} (S2). The cross-component blocks cost O(1) per boundary bond (S1). The bad collar tests refine the small-field set and use an enlarged retreat 𝒬⁺ (S3). Four bookkeeping placements and the label-sum factorisation are open.
- **Status (23:48):** the D1.0 leftovers are closed (§3c(2), (4⁗)(d)).
  - The four placements are fixed. z^{(0)}(U₁) is a product of row factors, placed in A₁; its Λ₁ rows are inside E^{(1)} under a new reading R-f. ζ(Ω₁ᶜ) and the J-tests are single factors of T₁. (B1)–(B4) are inputs of CRE's own derivation.
  - The label sum factorises over the ∗-components of Λᶜ: the retreat never crosses between them (derived).
  - So D1.0 holds at step 1 with (P). Only p.256's "other conditions" remain, and they belong to D2. Not reviewed.
- **Status (00:15, 22 Oct):** D1.1 is derived in §3d by the closed-contour route. Not reviewed.
  - The identity of §2 holds on every labelled term. Exposed links are constants inside the words, and S°_Λ = κ_Ce^{E°_Λ} holds at uncovered carriers.
  - V3's coverage hypotheses were checked at each use; each one either is not needed or is replaced by V3's own chart inclusion at carrier I (cited as L607; the correct line is L475, fixed 22 Oct in §3f(4)).
  - D1(ii) holds on every term with d^Λ(n), the distance to D(Λ)ᶜ (redefined in the round-3 repair as the distance to E(B_ξ) ∪ (I∖D(Λ)), §3d(4)).
- **Status (00:57, 22 Oct):** D1.2b is derived in §3e. Not reviewed.
  - The target is stated in Bałaban's form, as D1(iii)′: analyticity in the complex background direction a′ with ‖a′‖_∞ < ρ₁ = α_{1,1}/L (CRE (2.39) at j = 1).
  - It needs one repair of V3's constants, K: V3's Gaussian payment has no margin (L3831). K re-runs the chain before the coupling, with γ/2 and tighter n_* and M.
  - The words and f_ξ grow like e^{P(C)ρ₁} on the polydisc. This is intrinsic, and it is recorded as a constraint on D2.
  - Review round 3 (four packets: §3c(2), §3c(4‴), §3c(4⁗), §3d) was launched at 00:24:46. §3e is not in it.
- **Review round 3 (reports written 00:37–00:40, read 00:58–01:01).** None found anything fatal. Serious findings, with their repair status in §3f:
  - it1-c2-place (§3c(2)): S1 ι_ξ is not placed; S2 "p₀ ≥ 5𝔯 (CRE (2.5))" is misattributed; S3 the per-test large-field factor and the 𝐁₁ criterion for the z^{(0)} rows are unsupported.
  - it1-c4t-ii (§3c(4‴)): R1 reading R-d is broader than what was read (replace it by a weakest form R-d′ and prove that); R2 the label entropy spends the bad-test factor a second time.
  - it1-c4q-rep (§3c(4⁗)): S1 the extension of R-c ("CRE uses (α) only through |A| < r on Λ^∼") is not checked against CRE's uses of (α); S2 V3's downstream uses of the retreat constants are not reread under 𝒬⁺; S3 the bad-bond cubes are not placed in LFR II's set structure, and the lower bound of the T₁^Λ form is not derived.
  - it1-d11 (§3d): S-A the chart-inclusion quote "(L607)" is not in V3's L593–607; S-B the endpoint majorants (L3080) off coverage; S-C V3's "use its covered stencils" (L1977) and a link-change gap in §3b's telescoping at uncovered carriers; S-D the list of coverage uses is not complete.
  - Recommended statuses: D1.0(P) "derived at step 1 modulo R-c (extended), R-d and the 𝒬⁺ reread"; D1.1 "identity derived; bounds open pending S-A to S-D". Adopted until §3f closes them.
- **Status (02:05, 22 Oct): every round-3 finding is repaired (§3f). The repairs are not reviewed.**
  - it1-c2-place: ι_ξ is placed (§3c(2)(e)). The p₀ condition is CRE p.246 l.15 with LFR II p.387. The z^{(0)} rows off Λ₁ are factors of the T₁-integrand; there is no 𝐁₁ placement.
  - it1-c4t-ii: R-d is replaced by the weaker reading R-d″ (p.380 at threshold ϑδ₀, one factor per bad cube). The bad cubes are a fourth generator W₁ of LFR II's cover. The label entropy is paid inside (1.79)'s first exponential.
  - it1-c4q-rep: R-c is restated in sublevel form and checked against every transcribed use of (α). V3's uses of the retreat constants are reread under 𝒬⁺. R-e is dropped.
  - it1-d11: the chart citation is Lemma charts, L475. The endpoint majorants off coverage are Lemma c5-5R-3. V3's extraction proof uses contour coverage only locally. §3b's supp Γ now includes the marked stencils. Every coverage use under L2594 is listed.
  - So D1.0(P) is derived at step 1 under R-c (sublevel form) and R-d″, and D1.1 is derived on every labelled term.
- **Agreed for the V3 overhaul (user, 22 Oct, 05:02):** the enlarged retreat 𝒬⁺ (§3c(4⁗)(c); needed for D1.0(P)) and repair K of the constant chain (§3e(3.0); needed for D1.2b). Neither is needed for V3's one-step results, and neither is made in V3 yet.
- **Review round 4 and the reading review (launched 05:18:41, 22 Oct; user: "Run a review on the reading of R-d'' and R4").** Nine packets, built by verification/isolated_reviewer/build_round4_review_packets_20261022.py: it1-rd2-reading (R-d″ against LFR II p.380, with [16] = UV3), it1-e-red (§3e(0)–(2)), it1-e-gauss (§3e(3.0)–(3.5)), it1-e-rest (§3e(3.8)–(5)), it1-c2-place-r2 (§3c(2)+§3f(1)), it1-c4t-ii-r2 (§3c(4‴)+§3f(2)), it1-c4q-rep-r2 (§3c(4⁗)+§3f(3)), it1-d11-r2 (§3d+§3f(4), with the 21 Oct arc plan for m12), it1-d-d13-r2 (§3b).
  - Correction made before the launch: [16] of LFR II is UV3 (transcribed). It has only the curvature factor (71); the R_j factor is p.380's own (§3f(2) R1).
- **Status (07:28, 22 Oct): round 4 read and repaired (§3h); the D1.3 leftovers are in §3g.** No report found anything fatal.
  - R-d″ is not printed (rd2 S1). So D1.0(P)(ii) is OPEN; the rest of D1.0(P) is derived.
  - §3e is repaired. The complex factor e^{C′𝔰ρ₁} is paid by lowering the rate to 30η/8. The exterior shift is the real m₀ = m(U₁), with the tilt paid in the host potentials ((3.12)). The identity theorem is applied on 𝒩.
  - One more V3 constant change, K′ (§3e(3.6)), was proposed. Agreed by the user for the V3 overhaul (22 Oct, 08:57: "1.(a)"); not made in V3.
  - Λ₁ stays an outer label and M10 is withdrawn (c4q-r2c S-1). d11-r2 S-1 and d-d13-r2 S1 are repaired.
  - The repairs are not reviewed.
- **Status (09:39, 22 Oct): R-d″ derived under a narrower reading R-s (§3f(2) R1, (D0)–(D2); user: "2(a)").** The insertion below is superseded at 11:02 (Hölder route).
  - The pointwise bound is derived: on the support of the bad tests, each component form of T₁^Λ is ≥ 2c_bϑ²r²|𝒲_X|. It uses CRE p.248's positivity (H ≥ 0, no constant), V3's local gap extended to within ℓ/2 of I, and a localisation lemma. No lower bound of the T₁ form on 𝔤^J is used.
  - The insertion into (1.79) halves the T-form and pays 2^{n/2} as a volume cost. That (1.79) holds for the halved form is reading R-s, not printed.
- **Status (10:18, 22 Oct): R-s accepted by the user as a logged Bałaban reading ("(a)").** Superseded at 11:02: R-s is withdrawn.
- **Status (11:02, 22 Oct): review round 5 read (it1-rd3-pw-20261022-r1 and it1-rd3-rs-20261022-r1, finished 10:39 and 10:43); no fatal finding.**
  - The pointwise part (D0)–(D1) is correct (rd3-pw); its minors are repaired in §3f(2) R1.
  - R-s is withdrawn. R-d″(ii) is now derived from the printed (1.79) by Hölder's inequality, and the bad-cube factor is merged with (1.79)'s per-component factors by the subadditivity of the linear size (rd3-rs S1; §3f(2) R1 (D2)). R-d″ is restated in two parts (rd3-pw S1).
  - The comparison of the T₁^Λ forms with those at Λ₁ is withdrawn (rd3-rs S2); (1.79) is applied at Λ under R-c, as throughout D1.0(P).
  - So D1.0(P) is derived at step 1 under reading R-c only. The repairs are not reviewed.
  - D2's first item, the thin form of E^∂, is derived in §3i (10:33–10:50). Not reviewed.
- **Status (12:24, 22 Oct, date): review round 6 read (it1-rd4-d2, it1-rd4-thin1, it1-rd4-thin2, launched 11:12:37); no fatal finding; every finding repaired; the repairs are not reviewed.**
  - d2 S1: the Hölder route and the use of (1.79) at Λ are withdrawn. R-d″(ii) is derived factor by factor at the labelled configuration, by a check of LFR II pp.379–383 at Λ (§3f(2) R1 (D2)).
    - It uses reading R-c only. R-p (p.380's P₁- and Q₁-factors come from the action and backgrounds on plaquettes in Ω₁ᶜ) and R-q (CRE p.250's comparison of U₁ and U_{1,□′} on every cube with □′^{∼4} ⊂ Ω₁) were listed as new readings at 12:24. They were then checked against UV3 (70)–(71) and CRE pp.245–250 (§3f(2) R1, after the user's question, 22 Oct). R-p: location checked, rates quoted from p.380 (rd5-d2 M1). R-q is quoted on Ω₁^{∼−1} only (R-q₀). Its clause for Ω₁∖Ω₁^{∼−1} was a reading and is withdrawn; (B-q), from V3's logged (B1)(iii), replaces it (rd5-dbq S1).
    - R₁ is paid together with the bad cubes, through (D-b⁺) and (D1⁺).
    - One citation check was open: LFR II's construction of T′ before p.379, against R-c. Closed after 13:17 ((D2) (l)).
  - thin1 S1: §3i(2)'s claim that complex s needs no positivity is withdrawn. Complex s is admissible within λ/16 of the real blocks, which §3i(4) proves.
  - thin2 S1: X(Γ,Y) now contains V3's support network, contour intervals included, and is ∗-connected.
  - The minors are repaired as marked in §3f(2) and §3i.
  - D2's second item, the carrier dependence of the t > 0 species, is derived in §3j (12:13–12:24). Its open items (O1)–(O3) were closed after 12:44, by 12:53. No V3 η change is needed: a pointwise decay form at rate μ_H/20 serves every consumer for every η (§3j(5)).

## OPEN MATHEMATICAL GAPS

- **Open now (after 15:25, 22 Oct, date):**
  - **R-d″(ii) depends on D2.7 and the acceptance item (new status after rd5-d2-r2 S1; title after rd5-d2-r4 m-1(b)).** R-d″(ii) is now the j = 1 factor of (1.79) at step k ≥ N + 1 (§3f(2) R1 (D2), repair (i)): P₁/Q₁ come from p.380 in its printed scope, and R₁ and the bad cubes from (D1)/(D1⁺) inside T_h(Z_h ∩ X_k). Missing: that LFR I's construction after p.187 of Z and of Ω_hᶜ, Ω″_{h+1}, Z″_{h+2} and the preliminary-integration data from Z_h goes through with Z₁ = Λᶜ among the step-1 data. Closes in D2.7 (R-operation with a defect). Also missing (rd5-d2-r3 S1): the acceptance item, that CRE's steps 2, …, h and the R-operations before step k accept the retreat-made step-1 data (Ω₁, Λ₁, Λ), including p.256's "other conditions", so that T_h(Z_h ∩ X_k) contains T₁^{Λ₁,Λ}. Its small-field part is derived in the D2 file, D2.2(3)(b) (reviewed in rounds d2-2a r1–r3; r3 found it correct once its minors were repaired, done 22 Oct 23:48, date); the large-field objects and the 𝐑-terms close with D2.7. Until both close, D1.0(P)(ii) is not derived.
  - **Contour-wide factors in the label sum (§3j(0), after tj1-r2 m3).** f_ξ(m̂) and the words U_j depend on Λ only within R_N of C. Missing: how a factor with this fixed support enters the label sum over Λ near C, with the per-cube label weight. Closes in D2.6, with the per-cube weights below.
  - **D2, all items except the first two.** The first two are derived: the thin form of E^∂ (§3i; repairs reviewed in round 7 with no fatal or serious finding, round-7 minors applied, not reviewed) and the t > 0 species (§3j; round-7 repairs re-reviewed in round 8 with no fatal or serious finding; round-8 minors applied, not reviewed). The others are in WILSON_IT1_D2_STEP_MAP_2026_10_22.md: R-operation with a defect, IT-3 rates, contraction count, gauge covariance, non-scalar parts, attached terms, exposed segments.
  - **Complex-background polylog factor (§3j(6), new after rd5-tj2).** At complex backgrounds ρ_ph ≤ Cg₀²(1+2r)⁴(1 + (log g₀⁻²)^{(q₁−p₀)₊}). Missing: whether D(k)'s consumer n_C·ε̄_ph tolerates the power of log g₀⁻². Closes in D2.4 (contraction count).
  - **Per-cube weights for D2.6.** The label weight a_lab·n_t of §3j(6) and the comparisons of §3i(7) *Against (0)* ((a₂/ℓ₀+2)⁴C_rτ² with κ_{a₂}, κ_{a₂} with the step-2 large-field mass per cube; a₂ the step-2 cube side, thin1-r2 m4) are D2.6 count checks.
  - **LFR II's T′ before p.379 (§3f(2) R1 (D2) (l)): closed after 13:17 (22 Oct, date); reviewed in round 8 (rd5-d2-r2: R5 answered correctly; the list of uses corrected, m1).** On pp.356–379 the step-1 Λ-data enter only through R-c and (1.76). At k ≤ N, T′_k acts on no component (LFR I p.177 (ii); the definition itself states no range of k). So the step-1 large-field functions are integrated inside T′_k at k ≥ N + 1, and (D2) bounds their j = 1 factor there (repair (i) of rd5-d2-r2 S1). What is left are the two items of the first open item above, D2.7 (LFR I's construction of Z from Z_h after p.187; §3f(3) S1) and the acceptance item (rd5-d2-r4 m-1(b)).
  - **Round 10 read (three IT-1 sessions: it1-rd5-d2-20261022-r4, it1-rd5-thin1-20261022-r3, it1-rd5-thin2-20261022-r3; read and applied after 20:16, by 20:44, 22 Oct, date).** No fatal or serious finding. rd5-d2-r4: m-1 (every status line names both D2 items; withdrawn log claims marked), m-2 (the R₁ witnesses are split among the components G, so c₄ := ½min{γ₀m_A, c_b/(4·10^d)}; the threshold ½c₄ϑ²A₁²(log g₁⁻²)^{p₀} ≥ 2 still holds for small g), m-3 (p.384 l.33 replaced by a derived bound; the supply list corrected), m-4 (RG1's "equivalent definition" holds up to constants), m-5 (the step-k component is X_k), m-6 (normalised trace). thin1-r3 m-a to m-e and thin2-r3 m-a, m-b applied in §3i. Not re-reviewed.
  - **Round 8 read (four IT-1 sessions; read 15:21–15:25, 22 Oct, date; repairs applied after 15:25).** No fatal finding. Serious: rd5-d2-r2 S1 (repair (i), above). Minors: dbq-r2 m-a to m-g; rd5-d2-r2 m1–m16 (m7 lapsed); tj1-r2 m1–m6 (m1: C_bd with C₀ + C_τ); tj2-r2 A–E. All applied in §3e(4)–(5), §3f(2) R1, §3j and §3c(4‴); not re-reviewed.
  - **Round 7 read (six app sessions on claude-opus-5-5, started 13:06; triaged 14:11–14:24, 22 Oct, date).** No fatal finding. Serious: rd5-dbq S1 (R-q's layer clause; withdrawn, replaced by (B-q) from V3's logged (B1)(iii)), rd5-d2 S1 (answered by the (D2) (l) check of 13:17), rd5-tj1 S1 (finite check of V3 §c5-5 at W̃_t, ω̂_t, added to §3j(4)), rd5-tj2 S1 (Repair A, N(g₀) tied to g₀) and S2 (per-cube count, §3j(6)). thin1 and thin2: no serious finding. All repairs and minors applied in §3f(2) R1, §3i and §3j; not reviewed. The round-6 §3c lines stay not reviewed.
  - **Round 8 launched 14:52:48 (22 Oct, session timestamps):** re-reviews of the round-7 serious repairs, it1-rd5-dbq-20261022-r2 (local_8ffd6b06), it1-rd5-d2-20261022-r2 with the (l) check of T′ (local_1f85bb2c), it1-rd5-tj1-20261022-r2 (local_54f3c72e), it1-rd5-tj2-20261022-r2 (local_b538bd17), claude-opus-5-5, with the D2 file's three packets. §3i's round-7 findings were minors only; its re-review waits for the next batch.
  - Repair K′ of §3e(3.6) is agreed for the V3 overhaul (user, 22 Oct, 08:57) and not made in V3 (§3h(7)).
- **D1.0 (assembly; worked in §3c; reviewed up to §3c(4″) in it1-c-d10-20261021-r1, §3c(2), (4‴), (4⁗) in round 3 and their repairs in round 4; no fatal finding in any; round-4 repairs §3h(1)–(4), not reviewed).**
  - *Derived (§3c(1)–(3)):*
    - at step 1 no R-operation is applied (a fact: CRE (1.6), p.247; p.244). With V^{(0)}(S₁) defined as the exact change under (1.22), as V3 does (L2132), CRE's ρ₁ of (1.28) equals Tρ₀ as measures. CRE's stated properties of V^{(0)} hold for the exact change by the first-order Taylor formula with integral remainder (§3c(1));
    - V3's 𝒪 and CRE's Σχ₁T₁ have the same integrands label by label, so N₁ = Σχ₁T₁[F_ξ(1)·exp A₁] as measures;
    - the label sum is V3 Lemma c5-6-1: F_ξ(1) is the π_ξ-average of the labelled F^Λ(1).
  - *Bookkeeping of the identification (§3c(2)): closed 23:45, not reviewed.*
    - (a) z^{(0)}(U₁) = c·Π_c|det α_c(U₁)|⁻¹ is placed in A₁. Its Λ₁ rows are the δ-part of RG1's log Z^{(0)} (RG1 (1.3)–(1.4)), inside CRE's E^{(1)} by p.254 (reading R-f). The other rows are factors of the T₁-integrand, of total size ≤ exp(2Cd|Z₁∩Ω₁|), the kind of factor LFR II p.383 has (§3f(1), S3). There is no 𝐁₁ placement.
    - (b) ζ(Ω₁ᶜ) and (c) the J-tests of χ^{(0)}(Λ₁) are factors of the T₁-integrand. They do not depend on a. A sup-test is a product of single-bond tests, so the J-part splits off exactly.
    - (d) (B1)–(B4) are V3's record of CRE's own derivation, so the identification adds no input. (P) changes none of them.
  - *The choice:* (P), refining CRE's labels by V3's labels Λ = Λ₁^fin, with the de-younged bonds and the collar tests moved into T₁^lab. Option (A) would need a cluster expansion of the label law under ρ_ξ.
  - *D1.0(P) at step 1:*
    - (i) the Gaussian at the retreated regions: derived (§3c(4″), (4⁗)(a)). The split is CRE (1.26) at Λ. C^{(0)}(Λ) exists by interlacing and decays by V3 Lemma c5-1-1. Cross-component blocks, with components taken at range ℓ/2, cost O(1) per boundary bond. This uses reading R-c in sublevel form: CRE's construction uses only the listed properties (α)–(δ) of Λ₁, with (α) as a sublevel-set statement; checked against every use in the CRE transcription pp.243–285 and in LFR I (§3c(4″), §3f(3)). R-e is dropped: p.258 is read directly (§3c(4⁗)(a)).
    - (ii) the large-fluctuation factor: OPEN (R-d″(ii), pending D2.7 and the acceptance item of its status; rd5-d2-r3 m8); its parts are derived in §3c(4‴), (4⁗)(b), §3f(2), §3h(1). The bad collar tests refine the small-field set (ϑr ≤ |A| < r). They are paid by a factor for all bad cubes jointly: R-d″. Round 4 found its earlier form not printed (rd2 S1). Its pointwise part is derived (§3f(2) R1): from H ≥ 0 and the local gap ((D1), reviewed correct in round 5; (D1⁺) for R₁). Its per-component part R-d″(ii) is the j = 1 factor of (1.79) at step k ≥ N + 1, bounded factor by factor under reading R-c, with R-p (location checked; rates quoted from p.380 (step k ≥ N + 1)) and R-q₀ recorded, not used ((D2), restated after rd5-d2-r2 S1; the Hölder route and R-s are withdrawn). OPEN: R-d″(ii) depends on two D2 items, D2.7 (LFR I's construction of Z, Ω_hᶜ, Ω″_{h+1}, Z″_{h+2} from Z_h after p.187, with Z₁ = Λᶜ) and the acceptance item of its status (§3f(2) R1; rd5-d2-r4 m-1(a)). Everything else in (ii) is derived. The bad cubes are a fourth generator W₁ of the cover; (1.76) becomes Z₁ ⊂ ⋃_G G^{∼107}, and the j = 1 condition with (434)^{−d} holds since 2p₀ ≥ 10𝔯 > 6𝔯 (CRE p.246 l.15; LFR II p.387). LFR II pp.386–389 put no further condition on A₁. Cor. 3 is asserted on p.387 and accepted as Bałaban's result.
    - Both need the *enlarged retreat* 𝒬⁺(e), the ℓ-cubes within ℓ + ρ_L + 1 of x_e (§3c(4⁗)(c)). It puts every bad bond outside Λ^∼, as (α) requires, and changes V3's constants to 103ℓ and N⁺_ret = 4(209ℓ)⁴. V3's downstream uses of these constants were reread under 𝒬⁺ (§3f(3), S2). Agreed by the user for the V3 overhaul (22 Oct, 05:02); not made in V3.
  - *The label sum (§3c(4⁗)(d)): derived 23:48.* χ_Λ := Σ_{lab: Λ^fin = Λ} 1_lab = 1{Λ^fin = Λ} is the product over the ∗-components X of Λᶜ of local indicators χ_{Λ,X}. Each depends on X, on 𝔅₀∩X and on the tests in X. The proof is an induction over the rounds: every change the retreat makes is face-connected and stays in one X. This is the form (2.19) asks for at Z₁ = Λᶜ.
  - *Left for D2:* p.256's "other conditions … determined inductively", and whether the later steps accept domains made by a retreat.
  - §3c(2)'s placements, §3c(4‴) and §3c(4⁗) were reviewed in round 3, and their repairs (§3f(1)–(3)) in round 4. The round-4 repairs (§3h(1)–(4)) are not reviewed. Λ₁ stays an outer label; M10 is withdrawn (c4q-r2c S-1).
- **Geometry (only for the Creutz route).** D1 is for the squares C_n under (c5-7-T). Rectangles need V3's square/torus constants (Remark c5-5-11(6)) to be re-derived. Open, and needed only if the Creutz route of the iteration audit §6 is used.
- **D1.1 (uncovered branches): derived 00:15 in §3d; reviewed in it1-d11 (round 3) and it1-d11-r2 (round 4), no fatal finding in either; round-4 repairs §3h(5), not reviewed.**
  - *Result.* The identity of §2 holds on every labelled term, with the contour kept closed. Contour links in Ω₁ᶜ (V₀) and links with free inputs in J(Λ) (the exterior variable at its actual value; V3's Wilson factor is "not interpolated", L607) are constants inside f_ξ(m), U_j and T_W.
  - *Inputs.* Lemma c5-5-3(a)–(d), c5-5-7(b),(d),(e), c5-5-7z, c5-5-8, c5-5R-3, c5-7-1 and Prop. regional-square-extraction hold at uncovered carriers. V3's coverage hypotheses were checked at each use (§3d(2)(i) lists them). The substantive steps are three. The row phase with exterior inputs lies in V3's chart domain, by Lemma charts (L475) at carrier I (§3d(2)(d)). The endpoint majorants off coverage come from Lemma c5-5R-3, whose proof uses no coverage. Prop. regional-square-extraction holds at uncovered carriers, since its proof uses contour coverage only locally, through d_j (§3d(2)(g)).
  - *Cost.* Cτ² per exposed coarse segment inside E^∂, as local terms attached to D(Λ)ᶜ; no arc-end factors. In D1(ii), d(n) becomes d^Λ(n) := dist(Γ_n, E(B_ξ) ∪ (I∖D(Λ))) on uncovered terms, with root weight max(ρ, ρ_ph) (§3d(4)). Any later bound of e^{E^∂} costs e^{Cτ²Σ_j e^{−c″d_j}}, e^{Cτ²} per exposed segment (D2; §3d(5)).
  - *Background (V3):* the exact identity of §2 is stated only on the covered event: every contour bond in Ω₁, and every free input of the contour in the carrier (V3 L2594). V3 handles the uncovered branches by bounding F_ξ(1) by 1 times their probability ((c3-6-2), L4196; Prop. c3-7-5).
  - *Why it is the main case (count).*
    - The expected number of contour bonds near the bad region is about n_C b⁴ p_z.
    - V3 proves only the upper bound p_z ≤ q_pt ≤ e^{−c_*π_*²}.
    - A lower bound of the same Gaussian-tail order, p_z ≥ e^{−C π_*²}, is expected: a plaquette fluctuation exceeds a threshold of p₀(g₀) standard deviations. It is not proved here.
    - With it, n_C p_z ≍ L^K e^{−C(log K)^{2p₀}} → ∞ at a loop of fixed physical size. So covered branches would have vanishing probability, and the generic branch would have of order n_C p_z crossings of large-field regions.
  - The earlier arc plan (1)–(8) is replaced by the closed-contour route; §3d(6) says where each item went.
  - (I4), A^fin_cov as used with Lemma c5-6-1 (L3101), only names the event on which V3 splits the label sum (L2986, L2990). Lemma c5-6-1 itself holds "On every history and every labelled term" (L2982). With §3d the split is not needed.
- **D1.2b (analyticity in the background; D1(iii)): derived 00:57 in §3e; reviewed in round 4 (it1-e-red, -e-gauss, -e-rest), no fatal finding; repairs §3h(7), not reviewed.**
  - *Result (§3e(4)).* The target is D1(iii)′, in Bałaban's form: analyticity in a complex background direction a′ with ‖a′‖_∞ < ρ₁ = α_{1,1}/L, which is CRE (2.39) at j = n = 1 in V3's fine units. The indicators stay outside as factors. On every labelled term, covered or not, Υ¹_W, the words and f_ξ(m) are analytic and G-covariant there. D1(ii) holds with δ*^{30}_n(U₁) + a*_n(a′), the rate 30η/8 in place of 31η/8, and the exterior marks including the tilt marks 𝔪^δ_Y of §3e(3.12).
  - *Conditions.* Repairs K and K′ ((3.0), (3.6)), and the new g₀-thresholds listed in §3h(7).
  - *Method.* A complex symmetric matrix lemma (§3e(1)) replaces V3's real spectral steps. Every V3 argument by moduli runs on Re H with V3's real lemmas, plus a determinant ratio and the form T^c. The path argument uses the real rooted tree gauge (§3e(2)(d)). The path endpoint is identified at complex 𝐔 by G-covariance and coefficient locality of the formula (§3e(3.10)).
  - *Repair K (constants; agreed by the user for the V3 overhaul, 22 Oct, 05:02; not made in V3).* V3's Gaussian payment has no margin (L3831). K re-runs V3's chain before the coupling with γ/2, h_+ + γ/2, a_*β ≤ 1/8 and a tighter M and α_G (§3e(3.0)). No later choice of the chain conflicts with it (§3e(3.11)).
  - *Repair K′ (proposed after round 4, e-rest S2; agreed by the user for the V3 overhaul, 22 Oct, 08:57; not made in V3).* After τ_L, choose ρ₀, then take H_*, K_*, C_C, C^D_k, C^a_k, Q_*, C_Π, C_p and C^∂_p as sups over the complex neighbourhood 𝒱_{ρ₀}, and choose ϑ_* and the rest as V3 does (§3e(3.6)). Without it the earlier "constants at most doubled" breaks 4K_*H_*ϑ_* < 1.
  - *Constraint on D2.* The words and f_ξ grow like e^{P(C)ρ₁} on the polydisc. This is intrinsic to the bare loop, so D2 may not use a uniform sup of the words over the polydisc (§6(f)).
  - *Kept for D2:* the analyticity of the step-2 minimiser U₁ = U(V) in the coarse field (VAR Prop. 9, item (2) below). D1(iii)′ is stated in the fine background 𝐔, which is where Bałaban's U_j^c puts it.
  - *Earlier analysis (21:53), kept as the record of what V3 has:*
  - *What was missing:* D2 integrates the step-2 fluctuations, so it needs the dressed loop as an analytic function of the coarse field V on a complex neighbourhood of the step-2 small-field region, with the bounds of §3a there.
    - q° and E° are reference quantities: U°₁ = id, with "the same Ω₁, Λ₁, I, J, cubes, hosts, constants and cutoffs" (L986). So on a fixed labelled term they do not depend on V, and their analyticity is trivial.
    - The V-dependence is in Υ¹_W, the words U_j and f_ξ(m), and in the region and label indicators ("the support of the term's collar indicators and exterior cutoffs", L2594).
    - The indicators are not analytic. D1(iii) is therefore asked on the support of the indicators, with the indicators kept as factors, as Bałaban keeps his characteristic functions. That this form is what D2 can use is part of D2.
  - *What V3 has (checked 21:53).*
    - The entries are complex-analytic in the background.
      - §c4-10-1 (L4880): the path products and means are "jointly analytic" in the background phase Z and the fluctuating phase A on ‖Z‖ < 2τ_b, ‖A‖ < 2θ₀.
      - The row maps of Lemma c2-uniform-chart(i) are analytic on a complex ball (L3689).
    - The integral estimates are proved only at real backgrounds.
      - V3 applies the chart lemma "at each real Z" (L4880).
      - The coefficient path e^{itB_W} is real.
      - The Hessian bounds (c4-7-7), the selected-integral majorants and the pins are all stated at real data.
  - *What closes it (as planned at 21:53; (1) and (3) are now §3e, (2) is kept for D2).*
    - (1) Extend the Hessian two-sided bound and the majorants of §c4-12-1 to complex backgrounds e^{i(Z+iY)} with ‖Y‖ small. Done in §3e(3); it needed repair K.
    - (2) Analyticity of U₁ = U(V) in V: quoted and checked. VAR Proposition 9 (p.309): "The minimal configuration U_k(V)=U_k(V′V₀) in the axial gauge has an extension to an analytic function of G^c-valued small configurations V′ on 𝔅_k". In the Landau gauge, U_k(V′V₀)U_k(V₀)⁻¹ = exp iη𝓗(B), with 𝓗 analytic in B = (1/i)log V′.
      - The complex domain: V′ = e^{iB′} with |V′ − 1| < C₁ε₁, |B′| < 2C₁ε₁ (VAR (172), p.305), "for ε₁ sufficiently small", with C₁ and B₅ absolute constants (p.305). VAR has no coupling, so the radius is coupling-free. The external field must satisfy the regularity conditions (3.35)–(3.38) of [5] or (1.7)–(1.9) of [6], which are not transcribed here.
      - The passage from VAR's axial and Landau gauges to V3's gauge conventions is part of (3).
    - (3) Rerun §3a on that complex domain. Done in §3e(2)(d), (4). §3b needs no rerun: E^∂_{D(Λ)} is taken at flat reference data, so it is a number on each labelled term (§3b(5)).
- **D1.2a (per-traversal bound on covered branches): derived in §3a, reviewed (it1-a-dev-20261021-r1; repaired).**
  - It takes V3's Appendix c4 inputs at their stated status, as V3's Prop. c5-6-def does (Remark c5-6-5(2),(4)).
  - It gives D1(ii) in the per-traversal form of §4. Only the curvature term is a deviation.
  - The exterior-mark part 𝔡^diff and the groups that are not good carry attached terms. These do not vanish at the reference point and carry no deviation; they are attached to B_ξ, to the wrap and to the collar data, with explicit decay. They are routed to D2(d).
- **D1.3 (the carrier part as a local sum): derived in §3b, reviewed (it1-d-d13-20261021-r1 and, in round 4, it1-d-d13-20261022-r2; no fatal finding in either); round-4 repairs §3h(6), not reviewed.**
  - E^∂_D = Σ_j Σ_{X∈𝒳_j} e_{j,X}, with each X ∈ 𝒳_j containing a bond of Dᶜ and lying within R_0 of K_j, and e_{j,X} depending on D only through D ∩ X. The anchored bound is Cτ²e^{−c''d_j}, and near each segment the bound is Cτ²e^{−c'd_j}.
  - It comes from V3's carrier comparison (L1992–2043), with the covariance comparison extended to pairs of carriers and a telescoping in the carrier.
  - E°_{T,n} depends only on n and the torus (L161). It is a constant of the contour and needs no localisation.
  - *The two leftovers: derived 05:19–05:29, 22 Oct, in §3g; not reviewed.*
    - Carrier dependence of the reference species (§3g(1)). For any two carriers D, D′ and a union Z of LM-cubes with E_D(Z) = E_{D′}(Z), the t = 0 selected integrals at final domain Z coincide (V3's proof of Lemma c5-6-2, which uses its hypothesis only in this form). So a^D_W, w°_D(W) and Φ°_D(Γ) depend on D only through D near the footprint, and log q°_D(𝔅) − log q°_{D′}(𝔅) is a sum over the marked clusters. The cluster weight e^{3νσ(Γ)/2} of V3's Kotecký–Preiss step is kept, and with Lemma c4-6-env it gives decay at rate 3ν/(2A_E LM) in the diameter of the cluster's envelope.
    - D(Λ) ∩ Y (§3g(2)). It is a function of Λ near Y. At fixed outer (Ω₁, Λ₁) the label indicator factorises over the ∗-components of Λᶜ (§3c(4⁗)(d), M4; M10 withdrawn, c4q-r2c S-1), so the label sum has the polymer form of CRE's sum over Λ₁. The pointwise statement (the history near Y determines D(Λ) ∩ Y) is not needed.
    - Not covered, and moved to D2: the carrier dependence of the t > 0 species (Υ¹_W, 𝓑^Λ), which contain the shift m and so C^{(0)}(D).
- **D2 (the step map; started 10:33, 22 Oct, with the thin form of E^∂).**
  - *Thin form of E^∂ (review it1-d-d13 S2, 23:25): derived in §3i (10:33–10:50, 22 Oct); reviewed in round 6 (it1-rd4-thin1, -thin2; no fatal finding); thin1 S1, thin2 S1 and the minors repaired 12:04–12:13; the repairs reviewed in round 7 (it1-rd5-thin1, -thin2; no fatal or serious finding); round-7 minors applied by 14:24, not reviewed.*
    - *What was missing:* the sets X of §3b are balls B_{m+1} around supp Γ, with |X| ≍ m⁴ bonds, while the terms that produce them decay only like e^{−a₀m}. If D2 puts E^∂ into its large-field polymers, whose bound is e^{−κd_j(X)} (CRE (2.42)), it needs a decomposition into thin sets.
    - *Result (§3i(7)):* E^∂_D = Σ_jΣ_{X∈𝒳_j^{thin}}e^{thin}_{j,X} over ∗-connected unions X of boxes of side in [ℓ₀, 2ℓ₀) meeting K_j and Dᶜ, with Σ|e^{thin}_{j,X}|e^{κ#boxes(X)} ≤ Cτ²e^{−c_th d_j}, the rooted form Σ_{X⊇Δ}|e_X|e^{κ#boxes(X)} ≤ C_rτ² per box, and Σ_{X∩Q≠∅}|e_X|e^{κ_{a₂}#cubes(X)} ≤ (a₂/ℓ₀+2)⁴C_rτ² per step-2 cube Q of side a₂ (thin1-r2 m4). It holds at every carrier D ⊆ D₊ = Λ₁^*, covered or not (thin2-r3 m-b). It uses a box walk expansion of the principal-restriction inverses, V3's cluster bounds at the complex s-expanded blocks, and RG2's localisation in the box parameters. No new hypothesis.
  - The R-operation with a defect.
  - The exact per-bond rates δm_2 and z_2 (IT-3).
  - The contraction count (§6).
  - The step-2 gauge covariance of the dressed loop, for all groups (§5 S3).
  - The non-scalar large-field parts (§6(d)).
  - The attached terms of D1(ii) (D2(d)).
  - The exposed segments: if D2 bounds e^{E^∂} rather than expanding it, the cost is e^{Cτ²Σ_j e^{−c″d_j}}, a factor e^{Cτ²} per exposed segment, with 𝔼[N_exp] ≤ 4(2c_st+1)⁴C_Ln_C(q + N_ret q_ϑ) from V3's coverage average (L2451–2457) (§3d(5), reviews it1-d11 S7, d11-r2 m-b, m-i). D2 must pay this against the large-field factors.
  - *The carrier dependence of the t > 0 species (Υ¹_W, the terms of 𝓑^Λ, f_ξ(m); §3g(1)(f)): derived in §3j (12:13–12:24, 22 Oct; (5)–(7) revised and (O1)–(O3) closed after 12:44, by 12:53); not reviewed.* The labelled terms contain them, so D2's label sum needs them local in Λ (§3j(0)). Translating by a local, clipped parametrix shift m̂ instead of m = −H⁻¹ℓ_Λ, with the remainder as a tilt in the host potentials (the device of §3e(3.12)), makes them exactly local within R_t ≤ (10/μ_H)log g₀⁻² + 5ℓ_s(N₀+3) + 2ρ_L (after rd5-tj2 S1, Repair A: the clipping depth N(g₀) is the least N ≥ N₀ with e^{−μ_Hℓ_sN/4} ≤ g₀; the earlier log log range is withdrawn). The label weight this costs is a per-cube count check left to D2.6 (§3j(6), after rd5-tj2 S2). All V3 uses of (c5-4-1) and the pointwise uses of m hold verbatim. The pointwise decay form (c5-5-1) holds at m̂ at the rate μ_H/20, so Prop. c5-5-9 and its consumers hold at the rates μ_H/40 and min(μ_H/80, η/(2A_ELM)), for V3's η unchanged. The pass over V3 L2479–3120 found no other use of m.

## 0. What changed relative to the audit

This section is a design choice, not a derivation.
- **Carry, don't bound.** The audit's terms §4(4)–(7) are not errors of a representation. They are bounds on pieces that a defect representation should carry.
- **The target is an identity.** At step 1 the target is an exact identity with local activities, not a bound. The consumer, D2, is expected to need the activities themselves, not their sums along the contour. D2 is not started.
- **V3 already has the identity on covered labelled terms (§2):** per labelled term, on A^fin_cov, under (c5-5-T)(iv) and (c5-7-T). So the new work at step 1 is D1.0–D1.3, not a new expansion.
- **The difficulty moves to D2 (§6).**

## 1. Framing: a partition function with a defect

- **Two integrals.** E_ε[W_χ(C)] = Z₀(C)/Z₀, with Z₀(C) := ∫W_χ(C;U)ρ₀(U)dU.
  - The RG is applied to numerator and denominator separately, each time preserving the integral.
  - No law of the block variables enters. That matters, because Bałaban's densities preserve integrals only: the operation R is defined so that "integrals of the densities are unchanged" (LFR I p.176, (0.3)–(0.4)), and the density obtained "may not be equal to ρ_k, but is equivalent to it, in the sense that they have equal integrals" (LFR I p.200).
  - V3's branch identity is the first step of this: E[W] = E_h[F_ξ(1)], with E_h positive and normalised. E_h is defined at (eq:c3-6-1), L4191. The identity itself is (c-one-step-branch-identity) with (native-source-physical-ratio).
- **Bałaban's first step.** ρ₁(V) = Σ_{Ω₁,Λ₁} χ₁(Ω₁) T₁({Ω₁,Λ₁}) exp A₁(1/g₁², U₁) (CRE (1.28), p. 253).
  - CRE (1.29), p.254: T₁ = Σ_{S₁} ∫dV₀|_{Ω₁ᶜ} δ(V̄₀V⁻¹)ζ(Ω₁ᶜ) ∫dA|_{Ω₁∩Λ₁ᶜ} χ(Ω₁∩Λ₁ᶜ,S₁) exp[−½⟨A,C*Δ₁CA⟩ + ½⟨A,C*Δ₁CC^{(0)}(Λ₁)C*Δ₁CA⟩]. "Gaussian" is my gloss; the positivity of the quadratic form is not on that page.
  - The integrand exp A₁ depends on the pending A and S₁ through 𝐁^{(1)}(U₁,A,S₁) in (1.30).
  - These integrals stay pending inside ρ₁: T₁ is "the integral operation" (p.254), and the step-k operations "are left undefined, only their basic general properties are formulated" (p.254).
  - So contour links in Ω₁ᶜ can remain functions of the pending V₀. Their unitary words need no bound beyond norm 1, but D1's bounds must hold on these branches (D1.1).
  - Links whose free inputs lie in Ω₁∩Λ₁ᶜ depend on the pending A and S₁. This second mode is part of D1.1.
- **Target form.** Z₀(C) = ∫dV Σ_{Ω₁,Λ₁} χ₁ T₁[𝒲₁·exp A₁], with 𝒲₁ a dressed loop (§4). This form is to be established by D1.0–D1.3.
  - V3 works at the stage of CRE (1.15) with the cutoff (1.25). CRE's (1.26), its cluster expansion and the renormalisation (1.27)–(1.28) "are replaced by the construction of this section and are not used" (V3 L300–314).
  - So the identification of V3's 𝒪[𝗐_ξ·] with Σχ₁T₁[· exp A₁] has to be derived, with the loop carried through (1.26)–(1.28). This is gap D1.0, derived at step 1 in §3c up to the form of the label average.

## 2. What V3 already gives on covered branches

All of the following is quoted from V3, for a labelled term with final region Λ and carrier D(Λ):

- **(a) Groups and families.** Lemma c5-5-3(a) (L2665): F^Λ(t) = Σ_{𝔅 compatible} A^t_Λ(𝔅), absolutely convergent. Compatible groups have disjoint intervals ℋ(W) in cyclic order, and a whole-contour group occurs only as a singleton (L2756).
- **(b) Reference data.** Lemma c5-5-3(b): U°₁ = id, V°₀ = id, A° = 0, Ψ° = id, exterior variable zero on J(Λ), so m° = 0.
  - The reference activities are a^Λ_W.
  - The Schur identity holds: the reference group matrix is a^Λ_W·id (Lemma schur, L991, via the constant gauge R_u).
  - S°_Λ = Σ_{𝔅 compatible} ∏_{W∈𝔅} a^Λ_W.
- **(c) Exact identity.** Lemma c5-5-3(c): F^Λ(t) = S°_Λ f_ξ(tm) + Σ_{𝔅≠∅ compatible} S°^{[𝔅]}_Λ R^t_Λ(𝔅).
- **(d) Resummation against the reference exclusions.** Lemma c5-5-3(d), via Kotecký–Preiss:
  - q°_Λ(𝔅) := S°^{[𝔅]}_Λ/S°_Λ = exp(−Σ_{Γ hits 𝔅} Φ°_Λ(Γ));
  - |q°_Λ(𝔅)| ≤ ∏_{W∈𝔅} e^{θ°(W)}, with θ°(W) ≤ νσ(W)/16.
- **(e) Ordered-product form.** Lemma c5-5-7(b):
  - R^t_Λ(𝔅) = dim(π)⁻¹ tr(Υ^t_{W₁}U^t₁ ⋯ Υ^t_{Wₙ}U^t_n);
  - Υ^t_W := w^t_Λ(W)∫π(T^t_W(B)(P^t_W)⁻¹) d⊗ν̂^{f,t} − a^Λ_W·id, an element of End(V_π);
  - the U^t_j are unitary background words.
- **(f) Bounds.**
  - ‖Υ‖_op ≤ K_χ·sup_h |dim(π)⁻¹ tr(Υπ(h))| (Burnside, Lemma c5-5-7(a));
  - ‖Υ^t_W‖ ≤ K_χ(M_Λ(W) + |a^Λ_W|) (Lemma c5-5-7(e));
  - |a^Λ_W| ≤ M_Λ(W) (Lemma c5-5-3(d));
  - the root weight: Lemma c5-5-7 takes only the first-order gain ρ_t = Cg₀(1+2r) per root. "Section c5-5R recovers the second order for the undifferenced slots at t∈{0,1} and for the activities a^Λ_W (Lemma c5-5R-3); the differenced slots and the marked part are unchanged" (L2786). So ρ = O(g₀²(1+r)⁴) holds for those two parts only. L2966 states the second-order rate ε̄_ph of the family-sum factor.
- **(g) Identification of S°.** S° = κ_C e^{E°}, with E° = E^∂ + E°_{T,n}. This is Lemma c5-7-1 and Cor. c5-7-2 at the retreated carrier (L2849, item (1); L2594, "by Corollary c5-7-2, under (c5-7-T)"), and Prop. c4c-5-1 with Cor. main-factorisation (L161) at I. It holds under (c5-7-T) (L3102):
  - (i) the collar conditions, and the contour a coarse translate of the counterclockwise (e₁,e₂) square of side nL;
  - (ii) the common small-coupling thresholds;
  - (iii) K_μ ≥ 3(n+2) for every coarse period, and 4ne^{−cι_T} ≤ 1 for the n-uniform form of Cor. c5-7-2(c).

  The split E° = E^∂ + E°_{T,n} is displayed at I (L161); at D(Λ) it is Cor. c5-7-2.

**Consequence (derived).** Exact per labelled term, on A^fin_cov, on the support of the term's indicators, under (c5-5-T)(iv) and (c5-7-T). Divide (c) by S°_Λ (S°_Λ ≠ 0 by the Kotecký–Preiss part of (d)) and use (d), (e), (g) at t = 1:

F^Λ(1) = κ_C e^{E°_Λ}·[ f_ξ(m) + Σ_{𝔅≠∅ compatible} q°_Λ(𝔅)·dim(π)⁻¹ tr(Υ^1_{W₁}U^1₁ ⋯ Υ^1_{Wₙ}U^1_n) ].

- **The bracket is a dressed loop.** Its parts are:
  - the leading word f_ξ(m) = W_χ(C;U_ξ(m)), where the shift m is the harmonic extension of the exterior data and decays away from the exterior (Lemma c5-5-1, L2607);
  - insertions Υ^1_W at pairwise disjoint intervals;
  - scalar interactions q°(𝔅), the exponential of a sum of local cluster coefficients.
- **Where n_C enters V3.** V3 does not keep the bracket. It bounds it in two pieces: the difference between t = 1 and t = 0, the exterior response B^Λ_ξ (Lemma c5-5-3(c), second form), and the t = 0 bracket through 𝔡⁰_W (proof of Prop. c5-6-def, L3066; §3a).
  - Each family of the response is bounded by one differenced or marked slot times the undifferenced slots b̄_W := M_Λ(W) + |a^Λ_W| (Lemma c5-5-7(c),(e)).
  - Summing the undifferenced slots over compatible families gives at most ∏_W(1 + K_χ b̄_W e^{θ°(W)}) ≤ exp(Σ_W K_χ b̄_W e^{θ°(W)}).
  - This is the family-sum factor e^{2n_C ε̄_t}, or e^{n_C ε̄_ph} after the repair, of (c5-5-10) (L2842, L2966).
  - In the response bound (c5-5-10)/(c5-5-9R), the only factor exponential in n_C is this family-sum factor, and Remark c5-5-11 attributes V3's restriction on n_C to it. Outside the response bound, n_C also enters V3 through n_C N_lat(μ'/2)e^{−μ'(b−1)/2} (Cor. c5-5-10), |R_n| ≤ e^{n_Cδ^♯_q} − 1 (L161), (c5-6-def-3), C_L S_c n_C(q + N_ret q_ϑ) (c5-3-coverage-average), and the torus conditions (c5-7-T)(iii).

## 3. The reference point: Υ vanishes at flat data (derived)

**Claim.** Suppose the actual data of a labelled term are the reference data of Lemma c5-5-3(b): U₁ = id, V₀ = id, A = 0, Ψ = id, and exterior variable 0 on J(Λ). Then Υ^t_W = 0 for every group W and every t ∈ [0,1].

For t ∈ (0,1), Υ^t_W is read with the t-objects of Lemma c5-5-3(a), which are defined for all t ∈ [0,1]. Lemma c5-5-7 states it for t ∈ {0,1} (L2756).

**Proof.**
- **The objects are the reference ones.** The weights w^t_Λ, the root measures ν̂^{f,t}_{Λ,Z} and the words T^t_W, P^t_W are then the reference ones. Lemma c5-5-3(b) defines the reference data as "the same Ω₁, cubes, hosts, constants and cutoffs" at these values. The reference row solutions are those of Lemma charts in its reference form (L986); they equal the selected solutions by the uniqueness of the small row solution (§c4-11-2).
- **The shift vanishes, and nothing depends on t.** m = 0 at these data: Lemma c5-5-3(b), "exterior variable zero on J(Λ) (so m°=0, ℓ°=0, …)" (L2665–2680). The linear term ℓ and any exterior inputs of primitives also vanish there. Lemma c5-5-3(b) states that "the reference objects are independent of t", and by the previous bullet this applies to the actual objects.
- **Schur.** Hence w^t_Λ(W)∫π(T^t_W(B)(P^t_W)⁻¹) d⊗ν̂ = w°_Λ(W)∫π(P°_W(a)) d⊗ν̂°. This commutes with π(G) by the constant-gauge argument in the proof of Lemma c5-5-3(b), so by Schur's lemma for the irreducible π it is a scalar.
- **The scalar is a^Λ_W.** Its normalised trace against π(h) is a^Λ_W χ(h) by Lemma schur, so the scalar is a^Λ_W, and Υ^t_W = 0. ∎

**S1 (closed).** The step "the objects are the reference ones" requires that each actual object, evaluated at these data, literally equals its reference counterpart. Examples:
- the Hessian at U₁ = id equals H° = (𝖧^{Ω₁}_{id})_{D(Λ)D(Λ)};
- f_ξ(a) = W_χ(C; e^{iq_{id}(a)}) at U₁ = id and Ψ = id.

Checked against the definition of the reference data (V3 L986): the same regions, the same cutoffs, and a group index set that does not depend on the field. V3 also uses this identity itself, at the carrier D(Λ), in the proof of Prop. c5-6-def (L3082): "c_W(U_{W,0};h) = a^Λ_W χ(h), the t = 0 recipe being the reference data of Lemma c5-5-3(b) (the same D(Λ), Ω₁, 𝐃₀(Λ) and cutoffs) with its Schur identity".

**Consequence.** Υ^1_W is a deviation: a function of the data that vanishes at the reference point. D1.2 is the quantitative form of this.

## 3a. D1.2a: the deviation bound on covered branches (derived from V3)

**Setting.**
- A labelled term with final region Λ and carrier D(Λ), on A^fin_cov, at t = 1.
- Any history: the far-history event 𝖭_b of (c4-2-1) is not assumed.
- V3's standing hypotheses of Prop. c5-6-def and §c4-12 are in force: the g₀ thresholds, (c5-5-T), ρ ≤ ρ_pin, and the radii τ_b and θ₀.
- Notation:
  - 𝔰(W), the size (c4-6-1); n(W), the cube count; ℋ(W), the interval;
  - Q_W, the enclosing comparison rectangle with its halos (§c4-8-4, §c4-11-4);
  - δ_Q(U) := max over plaquettes p ⊂ Q of |U(∂p) − id| (Lemma c4-10-5);
  - M_Λ(W), the majorant of Lemma c5-5-7(d) with root weight ρ_t; M^{(ρ)}_Λ(W), the same with root weight ρ (L3080).

**(1) Splitting.** Υ^1_W = (Υ^1_W − Υ^0_W) + Υ^0_W.
- The normalised traces against π(h) are c^1_W − c^0_W and c^0_W − a^Λ_W χ (definition before Lemma c5-5-7(a)).
- By Burnside (Lemma c5-5-7(a)): ‖Υ^1_W − Υ^0_W‖ ≤ K_χ 𝔡^diff_W and ‖Υ^0_W‖ ≤ K_χ 𝔡^0_W.
- Here 𝔡^0_W := sup_h |c^0_W(h) − a^Λ_W χ(h)| (proof of Prop. c5-6-def, L3066).

**(2) Exterior part (quoted).** (c5-5-8), L2774:

𝔡^diff_W ≤ M_Λ(W)·[Σ_{Z∈𝒜(W)} 𝔐_Λ(Z) + Σ_j Σ_{D∈𝔠_j} 𝔐_Λ(D) + C'_χ g₀ Σ_{b∈I_{ℋ(W)}} h(m_b)],

with 𝔐_Λ(Z) = Σ_{b∈E(Z)} 𝔪_b + Σ_{Y∈𝐃₀(Λ), Y⊆Z} 𝔪_Y (L2720). Every mark sits on a bond or host of W's domains, or on a free input of a traversal of ℋ(W).

**(3) Background part, good groups.** Call W *good* if Q_W ⊂ Λ₁ and Q_W lifts injectively. Then

𝔡^0_W ≤ C_χ 𝔰(W)³ δ_{Q_W}(U₁) M^{(ρ)}_Λ(W).

*Derivation.*
- **What V3's proof uses.** V3 proves (c4-12-3) for its small interior class (c4-8-9), n(W) < b/(4C_box LM), on far histories. In the proof, the size condition and the far history serve only to give four facts:
  - Q_W ⊂ Λ₁ and Q_W outside S₁: "On a far history this box lies in Λ₁, hence in Ω₁, and outside S₁" (L4824). §c4-8-1 (L4757–4758) states "outside S₁" as a requirement of the local-data comparison;
  - the injective lift (L5028);
  - δ_{Q_W}(U₁) ≤ Cε₁, which V3 derives from Q_W ⊂ Λ₁ alone (L5033).
- **"Outside S₁" follows from Q_W ⊂ Λ₁ (quoted and checked).** CRE p.251 line 5: Λ₁ = Ω₁^{∼−2} ∩ (R₁′^∼)ᶜ and S₁ = (Ω₁∖Ω₁^{∼−1}) ∪ R₁, with R₁′ "the union of LMR₁-cubes intersecting the set R₁" (line 3).
  - R₁ ⊆ R₁′ ⊆ R₁′^∼, so Λ₁ ∩ R₁ = ∅.
  - Ω₁^{∼−2} ⊆ Ω₁^{∼−1}, since shrinking is monotone, so Λ₁ ∩ (Ω₁∖Ω₁^{∼−1}) = ∅.
  - V3's Λ₁ is the filled region. The filling (CRE p.251 lines 9–13) replaces small components of Λ₁ᶜ "by the smallest rectangular parallelepipeds containing them". So it only shrinks Λ₁, and the two points above still apply.
  - Hence Λ₁ ∩ S₁ = ∅ on every branch, and Q_W ⊂ Λ₁ places Q_W outside S₁.
- **Where V3 imposes these facts.** §c4-8-4 (L4819–4824), §c4-8-1, §c4-6-3, §c4-9-2 (the lift), §c4-11-3, §c4-11-4 (L5024–5028; its only consumer is the lifting argument), §c4-11-5 (L5033) and §c4-12-2 (L5053–5057). At D(Λ), V3 says these facts "concern the group's domains, the contour and Λ₁, not the carrier" (L3082), listing "on N_b^c, the inclusion of Q_W in Λ₁ outside S₁".
- **What does not use size or history.** The Hessian bound (c4-7-7) needs only ‖B‖_∞ ≤ τ_b (Lemma c4-7-3; at D(Λ) by min–max, L3076). The chart condition along the path follows from the phase test alone (L3078).
- **Not re-read here.** §c4-9-1 (the definition (c4-9-1) of ω_W), §c4-10-1 to §c4-10-4, §c4-11-1 and Lemma c4-9-2 were not re-read for further uses of size or history. V3 makes the step ‖ω_W‖_∞ ≤ C_tg diam²δ itself in §c4-6-3 and §c4-12-2.
- **Phase test passed** (C_tg diam(Q_W)² δ_{Q_W}(U₁) ≤ τ_b/2).
  - The path is U_{W,t} = e^{itB_W} in the rooted tree gauge on Q_W, with ‖B_W‖_∞ ≤ C_tg diam(Q_W)² δ_{Q_W}(U₁) ((c4-10-17)).
  - V3 supplies, at D(Λ): the endpoint identities (c4-11-6) (L3082) and the derivative bound along the path (L3080, the D(Λ) form of (c4-12-2)).
  - Together: 𝔡^0_W ≤ C_χ‖B_W‖_∞(n(W) + |ℋ(W)|)M^{(ρ)}_Λ(W).
  - With diam(Q_W) ≤ C_box LM𝔰(W) and n(W) + |ℋ(W)| ≤ CLM𝔰(W) (L5053), and LM fixed, this is ≤ C_χ𝔰³δ_{Q_W}M^{(ρ)}_Λ.
- **Phase test failed.**
  - Then 1 < (2C_tg/τ_b)diam(Q_W)²δ_{Q_W}(U₁).
  - The endpoint majorants (L3080) give 𝔡^0_W ≤ 2M^{(ρ)}_Λ(W) ≤ (4C_tg/τ_b)(C_box LM)²𝔰²δ_{Q_W}M^{(ρ)}_Λ, which is ≤ C𝔰³δ_{Q_W}M^{(ρ)}_Λ since 𝔰 ≥ 1.
- **Difference from V3.** There are two changes from V3's (c4-12-3). δ_{Q_W}(U₁) is kept, not replaced by its bound Cε₁. And the class changes from "small interior groups on far histories" to "good groups, of any size, on any history". The kept form dev(W) = 𝔰(W)³δ_{Q_W}(U₁) is the one D2 is expected to use. D2 is not started, so this is not checked.

**(4) Background part, other groups.** If W is not good, then 𝔡^0_W ≤ 2M^{(ρ)}_Λ(W), by the endpoint majorants (L3080; (c4-12-4)), which hold on A^fin_cov on every history. Moreover one of the following holds.
- **(i) Q_W lifts injectively and Q_W ⊄ Λ₁.** The diameter bound below is for a liftable rectangle (§c4-8-4).
  - Write B_ξ = Λ₁ᶜ. For a traversal n put d(n) := dist_{d_T}(Γ_n, E(B_ξ)), with Γ_n the bonds and input templates of n (as in Γ_C, L4446).
  - Q_W contains the bonds and stencils of every n ∈ ℋ(W) (enlargement, L5024), and it contains a vertex of B_ξ.
  - So d(n) ≤ diam(Q_W) + 1 ≤ C_box LM𝔰(W) + 1, i.e. 𝔰(W) ≥ (d(n) − 1)/(C_box LM) for every n ∈ ℋ(W).
- **(ii) Q_W does not lift.** Then n(W) ≥ N_min/(C LM), so 𝔰(W) ≥ N_min/(C LM). This is the contrapositive of the two lifting conditions of L5028, CLMn(W) < N_min/4 and 2C_box LMn(W) < N_min, so C = max(4C_lift, 2C_box); "C_box is chosen to include these constants" (L5028).

On 𝖭_b^c this recovers V3's class (c4-12-4): (i) gives 𝔰 ≥ (b − 1)/(C_box LM) ≥ T_b, and (ii) gives the same because N_min > 32b (c4-9-3).

**(5) Gauge (S3).**
- δ_Q(U) is invariant under site gauges, since each U(∂p) is conjugated.
- V3 compares with the reference in the rooted tree gauge on Q_W, using the covariance of the coefficient (§c4-8-1, §c4-11; at D(Λ), L3082). The data are not gauge-fixed.
- So the deviation of a good group is gauge-invariant. For a group that is not good, no deviation is claimed.

**(6) Per-traversal form (derived).** For every traversal n ∈ ℐ_C:

Σ_{W: n∈ℋ(W)} K_χ e^{θ°(W)} 𝔡^0_W ≤ C_χ ρ [δ*_n(U₁) + e^{−c(d(n)−1)/(LM)} + e^{−cN_min/(LM)}],

where:
- δ*_n(U) := Σ_{k≥1} (k+1)³ e^{−(31/8)ηk} Δ_n(C_box LM(k+1));
- Δ_n(R) := max{δ_p(U) : p ⊂ Λ₁ a plaquette within distance R of n};
- c := 31η/(8 max(C_box, C)).

*Proof.*
- **Weights.** e^{θ°(W)} ≤ e^{η𝔰(W)/8} (L3066). The contour pin (c4-6-5), at D(Λ) by Lemma c5-5-8(a), gives Σ_{W∋n} M^{(ρ)}_Λ(W)e^{4η𝔰(W)} ≤ Cρ.
- **Good groups.**
  - Q_W lies in Λ₁ within diam(Q_W) ≤ C_box LM𝔰 of n, so δ_{Q_W} ≤ Δ_n(C_box LM(⌊𝔰⌋+1)).
  - Split by k = ⌊𝔰⌋ and use 𝔰³e^{η𝔰/8} ≤ (k+1)³e^{η/8}e^{−(31/8)ηk}e^{4η𝔰}.
- **Other groups.**
  - 𝔰 ≥ s_n := min((d(n) − 1)/(C_box LM), N_min/(C LM)).
  - So e^{η𝔰/8} ≤ e^{−(31/8)ηs_n}e^{4η𝔰}.
- **Constants.** These are V3's constants of §c4-12, which depend "not on the coupling, the square length, the compatible torus size or the history" (L5038).

*Count check.*
- δ_p(U₁) ≤ Cε₁ for p ⊂ Λ₁ (L5033), so δ*_n ≤ C_ηε₁.
- On 𝖭_b^c, d(n) > b for every n. Summing over the n_C traversals overcounts each group |ℋ(W)| ≥ 1 times, which is allowed in an upper bound.
- The sum is at most C_χ n_C ρ(ε₁ + e^{−c'b/(LM)}). This is V3's (c5-6-def-3) up to the value of the constant c' (V3 has c = η/(2C_box)).
- Per traversal, the rate is ρ·(local curvature) ≤ Cρε₁ inside Λ₁.
- The whole-contour groups sit inside every pin. Their total is at most Cρn_C e^{−25ηn_C/(LM)} ((c4-8-8), taken at D(Λ) as in L3084).

**(7) Exterior marks per traversal (derived).**
- **Envelope decay.** A group with n ∈ ℋ(W) and a cube Δ ∈ F(W) has σ(W) ≥ dist(Δ, n)/(C_F LM). This is the envelope argument of Lemma c5-5-8(b) (L2797): the envelope contains Δ and π₁(ℋ(W)) ∋ n, and has ℓ^∞ diameter ≤ A_E LM σ(W).
- **Marks per cube.** Fix an assignment of each bond mark and each host mark to one cube of the domain containing it (for a host Y ⊆ Z, a cube containing a chosen site of Y). Write 𝔪̂_Δ for the sum of the marks assigned to Δ. Domain multiplicities are at most n(W) ≤ σ(W), so the first two mark sums of (2) are at most σ(W)Σ_{Δ∈F(W)}𝔪̂_Δ.
- **Result.** With σ e^{η𝔰/8} ≤ C e^{4ησ − ησ} and the pins of Lemma c5-5-8(a):

  Σ_{W∋n} K_χ e^{θ°(W)} 𝔡^diff_W ≤ Cρ_t [Σ_Δ 𝔪̂_Δ e^{−η dist(Δ,n)/(C_F LM)} + C'_χ g₀ Σ_b h(m_b) e^{−η dist(b,n)/(C_F LM)}].

  The last sum runs over the free inputs b of the traversals. Every input of ℋ(W) lies in the envelope.

**(8) What D1(ii) now has.** On covered branches, for every traversal n, Σ_{W∋n} e^{θ°(W)}‖Υ^1_W‖ is at most the sum of (6) and (7):
- a gauge-invariant local curvature term C_χρδ*_n(U₁), which is ≤ Cρε₁ inside Λ₁;
- a term attached to the large-field region B_ξ, of size Cρ, decaying from B_ξ at rate c/(LM);
- a wrapping term e^{−cN_min/(LM)}, which is already ≤ e^{−2cR₁} by N_min ≥ 2LMR₁ (c4-9-3), on any compatible torus;
- exterior marks attached to the collar data, decaying from them. A mark 𝔪_Y is a fixed constant when a primitive has an input in J(Λ) (L2710ff.), so this term does not vanish at the reference point.

The second and fourth terms are not small, and they carry no deviation. They are attached to large-field regions and collars, which is the D2(d) case (§6(d)). So §3a gives the deviation form of D1(ii) only for the curvature term; D1(ii) is stated in §4 in this per-traversal form.

## 3b. D1.3: the carrier part as a local sum (derived from V3's proof of (regional-square-boundary-comparison))

Repaired at 23:10–23:25 after review it1-d-d13-20261021-r1 (S1, S3 and m1–m10; S2 is moved to the gaps block under D2).

**What is to be shown.** Let D be a covered carrier: I, or D(Λ) on a labelled term. (Uncovered carriers: §3d(2)(h).) Write E^∂_D := F_{D,C,T} − F_{C,T}.
- At I this is the split of Cor. main-factorisation (L161–165).
- At D(Λ), Cor. c5-7-2 sets E°_Λ := E°_{D(Λ),C,T}. V3 defines E°_{D,C_n,T} := (F_{D,C,T} − F_{C,T}) + (F_{C,T} − F_{C,∞}(n)) + E^σ_n for every carrier D (L2060–2061). The last two terms are E°_{T,n} (L164). So E°_Λ = E^∂_{D(Λ)} + E°_{T,n} by these definitions alone (round 4, d-d13-r2 m4: the earlier route through log κ_C and the bulk extraction is not needed).

The claim:
- E^∂_D = Σ_j Σ_{X∈𝒳_j} e_{j,X}. Here j runs over the 4n coarse segments and 𝒳_j is a family of finite bond sets;
- each X ∈ 𝒳_j contains a bond of Dᶜ and meets the free-input stencil K_j (d-d13-r2 m2: X ∩ K_j ≠ ∅ is what (4) proves);
- e_{j,X} depends on D only through D ∩ X;
- *(anchored bound)* for every j, Σ_{X∈𝒳_j} |e_{j,X}| e^{2a·diam X} ≤ Cτ² e^{−c''d_j};
- *(bound near a segment)* with e_X := Σ_j e_{j,X}, for every j, Σ_{X within R_0 of K_j} |e_X| e^{a·diam X} ≤ Cτ² e^{−c'd_j}.

Here a, c'', c' > 0 and C are fixed before the coupling, and d_j is as in (regional-square-distances), L1957.

V3 proves only |E^∂_D| ≤ Cτ²Σ_j e^{−cd_j} ((regional-square-boundary-comparison), L2043). That bound does not say how E^∂ depends on D. D2 needs that dependence to be local: at step 2, e^{E^∂} has to be expanded into polymers attached to the large-field region and merged with Bałaban's large-field polymers (IT-2(b) of the audit). Whether the sets X below are thin enough for that is open (gaps block, D2).

**V3's structure (quoted).**
- *(Q1) The expansion at a covered carrier.* "Apply the protected-label expansion with supports intersected with D, keeping every original label" (L1992). The estimates "use its covered stencils, spectral bounds and small-coupling conditions" (L1977), and the bounds "hold uniformly for these restricted labels" (L1994). So F_{D,C,T} = Σ_{Γ∈𝒞_D} φ_D(Γ), over the source clusters 𝒞_D of carrier D, absolutely convergent by the rooted majorant (regional-square-rooted-majorant), L2015: Σ_{Γ: j∈J_Γ} U(Γ)e^{η'ℓ(Γ)} ≤ Cτ².
- *(Q2) The flat data.* The scalar is taken at the conditional reference data: background identity and flat torus entries (L1983). (regional-square-scalar) (L1946) and (regional-periodic-weight) (L1834) define S°_{D,C_n,T} by a formula in D, C_n, T, g₀ and σ. So F_{D,C,T} is a function of the set D alone, and no physical field enters.
  - At a carrier D' ⊇ D other than D(Λ) or I, §3b uses only this formula, the per-cluster bound |φ_{D'}(Γ)| ≤ U(Γ) and (1) below. These rest on L1994 and L2034–2039, which are generic in the carrier. When D is covered, every free-input stencil lies in D'. At an uncovered D this is not used (§3d(2)(g), (h)).
  - *At D = T*, the torus free carrier E_{*,T}: i_{T,T} is the identity, so C_{T,T} = H_T⁻¹. P_{T,T} is the sum of all periodic primitives, and Θ_T^σ is the full bond product: (regional-weight) (L1701–1702) defines Θ_D^σ(B) = ∏_{b∈D}1{|B_b|_σ < r}. V3 defines F_{C,T} := log(N^σ_{C_n,T}/D^σ_T) (L1981; d-d13-r2 m4). By Lemma identity-primitives (L1983: the primitives agree with the local terms "label by label", and "the cutoff is the same product of bond tests"), the ratio (L1946) at D = T is N^σ_{C_n,T}/D^σ_T of (L1218–1224). So F_{C,T} = F_{T,C,T} = Σ_{Γ∈𝒞_T} φ_T(Γ), by (Q1) at D = T.
- *(Q3) Interpolation.* "On D, interpolate between (C_∞)_{D,D} and C_D" (L1771).
  - Spectrum: a principal block of H_T has spectrum in [γ_L, h_L] by the Rayleigh quotient, so its inverse has spectrum in [h_L⁻¹, γ_L⁻¹]. Principal blocks of these inverses and their convex combinations stay in that interval.
  - Decay: "Principal restriction and inversion preserve the spectral bounds, and the finite-range Neumann series gives uniform exponential covariance decay in the periodic metric" (L1994).
  - The derivative: h_A := e^{−a₀ d_T(A,Dᶜ)} on a carrier A of size k (L2034). The differentiated object bound is C(k+|F|+1)²h_A, and "the product rule over repeated object occurrences" gives the cluster bound (L2039).
  - A cluster activity depends on the carrier only through its restricted labels and the covariance restricted to its carrier. V3 uses this for its own D-versus-T comparison (L2041: "identical labels and cyclic intervals in both expansions … Their covariance derivative is bounded by the preceding estimate").
- *(Q4) The covariance comparison.* The resolvent identity C_{D,T} − (C_T)_{D,D} = C_{D,T}(H_T)_{D,Dᶜ}(C_T)_{Dᶜ,D} (L2020–2022) gives ‖C_{D,T}(b,c) − C_T(b,c)‖ ≤ Ce^{−a₀(d_T(b,Dᶜ)+d_T(c,Dᶜ)+d_T(b,c))} (L2024–2031).
- *Notation.* a₀ is V3's exponent a of L2031 and L2034; the letter a is the new weight of (4). R_* bounds "the label diameters and source-to-stencil distances" (L1729), and R_0 ≥ R_* "includes the label, reconstruction and precision ranges" (L1960). The metric d(b,c) = ‖x−y‖_∞ + 𝟏{i≠k} (L1729) is integer-valued, with d(b,c) ≥ 1 for b ≠ c.

**(1) Pairs of carriers (derived).** Let D₂ ⊆ D₁ be carriers and E := D₁ ∖ D₂. The covariance statements below need no coverage. The cluster comparison at the end of (1) is made for clusters Γ with E ∩ supp Γ = ∅, supp Γ as in (2); this holds for every use in (3). (Repaired 22 Oct after review it1-d11, S-C(ii) and m11. The earlier hypothesis "carriers containing every free-input stencil" is dropped.)
- The block identity H₁H₁⁻¹ = id on D₂ × D₂, with H₁ := (H_T)_{D₁D₁}, gives (H_T)_{D₂D₂}(C_{D₁})_{D₂D₂} + (H_T)_{D₂E}(C_{D₁})_{ED₂} = I_{D₂}. Multiplying on the left by C_{D₂} gives C_{D₂} − (C_{D₁})_{D₂D₂} = C_{D₂}(H_T)_{D₂E}(C_{D₁})_{ED₂}.
- This is (Q4) with T replaced by D₁ and Dᶜ by E. Both inverses are principal-restriction inverses, so they have the spectrum and the uniform decay of (Q3). Neither needs coverage.
- The convolution argument of L2024–2028 gives ‖C_{D₂}(b,c) − C_{D₁}(b,c)‖ ≤ Ce^{−a₀(d_T(b,E)+d_T(c,E)+d_T(b,c))} for b, c ∈ D₂.
  - Take u ∈ D₂ and w ∈ E with d_T(u,w) ≤ R_H, and s := d_T(b,u) + d_T(w,c).
  - Then d_T(b,E) ≤ d_T(b,u) + R_H, d_T(c,E) ≤ d_T(c,w) and d_T(b,c) ≤ s + R_H. The sum is at most 2s + 2R_H.
  - Only w ∈ E is used. The shell count is carrier-independent (L2028).
- *Same index (S-C(ii)).* If E ∩ supp Γ = ∅, then every label support and every marked stencil of Γ meets D₁ and D₂ in the same set. So the restricted labels coincide, and so do the link functions of the marked traversals: the link of r at i_{D,T}B depends on B through the stencil of r intersected with D only. Hence Γ ∈ 𝒞_{D₂} iff Γ ∈ 𝒞_{D₁}, with the same index, and only the covariance changes.
- Interpolating on D₂ between (C_{D₁})_{D₂D₂} and C_{D₂}, as in (Q3), gives for such a cluster Γ ∈ 𝒞_{D₂} ∩ 𝒞_{D₁}:

  |φ_{D₁}(Γ) − φ_{D₂}(Γ)| ≤ C(|Γ| + 1)² e^{−a₀·d_T(A_Γ, E)} U(Γ).

  *One U(Γ) for all carriers (d-d13-r2 m1).* U(Γ) is the pinned-tree majorant of (regional-square-rooted-majorant) (L2013–2015). It is built from the web-tree majorants u_p of L2006–2010, which are functions of the restricted labels and of constants common to all carriers: s_*, q_*, R_* ("Restriction preserves the support-size, overlap and range bounds", L2000), K_2, and the edge majorant B_{bc} = A_0e^{−μ_0d_T(b,c)} (L2034). So U(Γ) is a function of the index of Γ, which is common to every carrier used in (1) and (3).

  Here A_Γ is the carrier of Γ, and |Γ| := Σ_γ (k_γ + |F_γ| + 1), summed over the component occurrences γ of Γ with multiplicity, with k_γ = |A_γ|. Each occurrence costs C(k_γ+|F_γ|+1)²h_{A_γ} (L2039 with E in place of Dᶜ). The product rule (L2039) sums these, and Σ_γ(k_γ+|F_γ|+1)² ≤ (|Γ|+1)².
- *|Γ| against ℓ(Γ).* ℓ(γ) = |A_γ| + Σ_{F_γ} d_T(b,c) ≥ k_γ + |F_γ| (L1368, d ≥ 1), and ℓ(γ) ≥ 1. So k_γ + |F_γ| + 1 ≤ 2ℓ(γ) and |Γ| ≤ 2ℓ(Γ).

**(2) Three classes of clusters.** Write supp Γ for the union of the *original* supports of the labels of Γ and of the free-input stencils of the traversals marked by Γ (enlarged for S-C(ii), 22 Oct). Each label support has diameter at most R_*, and each stencil lies within R_* of its source label (L1729: "R_* bound[s] the label diameters and source-to-stencil distances"). *Stencil reach (round 4, d-d13-r2 S1; derived 22 Oct from V3 L2598).* Each free-input bond of a traversal r lies within ℓ^∞ distance 2L+1 of r: the forward influence set ℛ_b lies within 2L+1 of b (L2598). So it lies within c_st := 2L+2 of r in the metric d of L1729, and a traversal stencil has diameter at most 2c_st. c_st depends on L only. Put R_K := R_* + 2c_st. Then every point of a marked stencil is within R_K of its source label, whether L1729's "source-to-stencil distance" is read to the traversal bond or to the nearest stencil bond (d-d13-r2 m3). With label diameters ≤ R_*, every point of supp Γ lies within c_supp := R_* + R_K of the carrier A_Γ, which the network joins (L2041). (The C_K of §3f(3) S2 is a different, ℓ-dependent bond count and is not used here.) Only marked traversals enter a cluster: in (regional-wilson-polynomial), L1670–1677, 𝒢_S varies only the links of S and uses U₁ = id elsewhere at the reference data. A cluster of 𝒞_{D'} has only labels whose original support meets D', since primitives whose support misses D' are not in P_{D',T} (L1838). Call Γ *D-interior* if supp Γ ⊆ D.
- A D-interior cluster has the same index (labels, forest, web interval) in 𝒞_D and in 𝒞_T. Its restricted labels are the original ones, its marked links are the torus links (their stencils lie in D), and the grouping of L1992 ("shortest cyclic intervals, with its fixed tie-breaking base") is geometric.
- With F_{C,T} = Σ_{𝒞_T} φ_T(Γ) from (Q2), and absolute convergence from (Q1), this gives the exact identity

  E^∂_D = Σ_{Γ D-interior} [φ_D(Γ) − φ_T(Γ)] + Σ_{Γ∈𝒞_D, not D-interior} φ_D(Γ) − Σ_{Γ∈𝒞_T, not D-interior} φ_T(Γ).
- In the last two sums supp Γ contains a bond of Dᶜ.

**(3) Localising the dependence on D (derived).** Fix Γ. Put B_m := {bonds b with d_T(b, supp Γ) < m}, so B_1 = supp Γ, and D^{(m)} := (D ∩ B_m) ∪ (T ∖ B_m).
- D^{(m+1)} ⊆ D^{(m)}, and D^{(m)} ⊇ D. (The earlier "contains every free-input stencil" holds only for covered D and is not used; d-d13-r2 m5.)
- Γ is D^{(m)}-interior whenever it is D-interior.
- φ_{D^{(m)}}(Γ) depends on D only through D ∩ B_m.
- D^{(m)} = T for m ≤ m₀ := d_T(supp Γ, Dᶜ), and D^{(m)} = D once B_m covers the torus.
- D^{(m)} ∖ D^{(m+1)} = Dᶜ ∩ (B_{m+1} ∖ B_m), the bonds of Dᶜ at distance exactly m from supp Γ.

*Interior clusters.* Telescoping,

φ_D(Γ) − φ_T(Γ) = Σ_{m≥m₀} [φ_{D^{(m+1)}}(Γ) − φ_{D^{(m)}}(Γ)].
- The m-th term depends on D only through D ∩ B_{m+1}.
- It vanishes unless Dᶜ meets B_{m+1} ∖ B_m: otherwise the two carriers coincide.
- Apply (1) with D₁ = D^{(m)}, D₂ = D^{(m+1)} and E = Dᶜ ∩ (B_{m+1} ∖ B_m). Here m ≥ m₀ ≥ 1, so E ∩ supp Γ = ∅, as (1) requires. Since A_Γ ⊆ supp Γ, d_T(A_Γ, E) ≥ m, so the term is at most C(|Γ|+1)²e^{−a₀m}U(Γ).
- Put X := B_{m+1}, which contains supp Γ and a bond of Dᶜ.

*Other clusters.*
- Γ ∈ 𝒞_T, not D-interior: φ_T(Γ) does not depend on D. Only the indicator "Γ is not D-interior" does, and it is a function of D ∩ supp Γ. Put X := supp Γ.
- Γ ∈ 𝒞_D, not D-interior. Its index, restricted labels and marked links depend on D ∩ supp Γ only. For m ≥ 1, D^{(m)} ∩ supp Γ = D ∩ supp Γ, so Γ ∈ 𝒞_{D^{(m)}} with the same index. Telescope from m = 1:

  φ_D(Γ) = φ_{D^{(1)}}(Γ) + Σ_{m≥1}[φ_{D^{(m+1)}}(Γ) − φ_{D^{(m)}}(Γ)].
  - The first term depends on D ∩ supp Γ, with X := supp Γ, and is at most U(Γ).
  - The m-th term obeys the bound of the interior case, with X := B_{m+1}.

**(4) Summation (derived).**
- *Anchoring.* As in L2041, allocate each source cluster Γ to its marked segments j ∈ J_Γ with weight |J_Γ|⁻¹. Index the terms of (3) by (Γ, type, m) (d-d13-r2 m6): type "supp" (X = supp Γ, no m, for the clusters that are not D-interior) or type "shell" (X = B_{m+1}, kept only when Dᶜ meets B_{m+1} ∖ B_m). 𝒳_j is the set of X produced from the clusters with j ∈ J_Γ, and e_{j,X} := Σ |J_Γ|⁻¹ t_{Γ,type,m}, over the indices with j ∈ J_Γ that produce X. Here t is the term of (3), with a sign. Every source cluster has J_Γ ≠ ∅, so E^∂_D = Σ_j Σ_{X∈𝒳_j} e_{j,X}. Each kept X contains a bond of Dᶜ, so e_{j,X} = 0 whenever X ⊆ D.
- *Position.* supp Γ contains the stencil of the marked traversal in segment j, which lies in K_j. So each X ⊇ supp Γ meets K_j.
- *Diameters.* Every label of Γ meets the carrier, and the network joins the carrier, stencil edges and contour intervals with length at most C_net ℓ(Γ) + R_0 (L2041). Every point of supp Γ is within c_supp = R_* + R_K of the carrier ((2)). So diam(supp Γ) ≤ C_net ℓ(Γ) + R_0 + 2R_* + 2R_K, and diam X ≤ C_net ℓ(Γ) + R_0 + 2R_* + 2R_K + 2m for X = B_{m+1}. R_K = R_* + 2(2L+2) is fixed before the coupling ((2); d-d13-r2 S1).
- *Weights.* Take a ≤ min(a₀/8, η'/(8C_net)). Then e^{2a·diam X} ≤ Ce^{(η'/4)ℓ(Γ)}e^{a₀m/2}. By |Γ| ≤ 2ℓ(Γ) (from (1)), (|Γ|+1)² ≤ (2ℓ(Γ)+1)² ≤ C_{η'}e^{(η'/4)ℓ(Γ)}. So

  Σ_{X∈𝒳_j} |e_{j,X}| e^{2a·diam X} ≤ C Σ_{Γ: j∈J_Γ} U(Γ) e^{(η'/2)ℓ(Γ)} [e^{−(a₀/2)m₀(Γ)} + 𝟏{Γ not D-interior}].

  The bracket comes from the geometric sum over m ≥ m₀ (interior clusters) or m ≥ 1 (the others), plus the terms with X = supp Γ.
- *Decay in d_j (V3's split, L2041).* Put c'' := min(a₀/4, η'/(4C_net)).
  - From the position, d_T(K_j, Dᶜ) ≤ diam(supp Γ) + m₀(Γ). With d_j = d_T(K_j, Dᶜ) − R_0, this gives m₀(Γ) ≥ d_j − C_net ℓ(Γ) − 2R_* − 2R_K.
  - Short clusters, ℓ(Γ) < d_j/(2C_net), with d_j > 4(R_* + R_K): m₀ ≥ d_j/2 − 2(R_* + R_K) > 0. So Γ is D-interior, and its term is at most CU(Γ)e^{(η'/2)ℓ(Γ)}e^{−a₀d_j/4}.
  - Long clusters, ℓ(Γ) ≥ d_j/(2C_net): e^{(η'/2)ℓ(Γ)} ≤ e^{η'ℓ(Γ)}e^{−η'd_j/(4C_net)}.
  - Non-interior clusters have m₀ = 0, so they are long when d_j > 4(R_* + R_K).
  - Summing with the rooted majorant (L2015) at D and at T, Σ_{Γ: j∈J_Γ} U(Γ)e^{η'ℓ(Γ)} ≤ Cτ², gives the anchored bound Cτ²e^{−c''d_j}. Bounded d_j ≤ 4(R_* + R_K) are covered by enlarging C. At an uncovered D the rooted majorant at D holds by §3d(2)(g).
- *Near a segment (review S1).* Read "X within R_0 of K_j" as d_T(X, K_j) ≤ R_0 (d-d13-r2 m2). An X ∈ 𝒳_{j'} meets K_{j'} (*Position*). So if d_T(X, K_j) ≤ R_0, then diam X ≥ dist(K_j, K_{j'}) − R_0 ≥ dist(K_j, K_{j'}) − 2R_0, and e^{a·diam X} ≤ e^{2aR_0}e^{2a·diam X}e^{−a·dist(K_j,K_{j'})}.
  - d_j ≤ d_{j'} + dist(K_j, K_{j'}) + diam K_{j'}. K_{j'} is the union of the free-input stencils of the contour bonds of the coarse segment j′, which has length L, so diam K_{j'} ≤ L + 2c_st is fixed (d-d13-r2 S1).
  - Put c' := min(c'', a/2). Then Σ_{X within R_0 of K_j} |e_X|e^{a·diam X} ≤ Cτ² Σ_{j'} e^{−c''d_{j'}}e^{−a·dist(K_j,K_{j'})} ≤ Cτ²e^{−c'd_j} Σ_{j'} e^{−(a/2)dist(K_j,K_{j'})}.
  - Each point of K_{j'} lies within c_st of a bond of segment j′, and distinct segments contain distinct contour bonds. Fix a bond b_j of segment j; every point of K_j lies within L + c_st of b_j. So if dist(K_j, K_{j'}) < r, some bond of segment j′ lies within r + L + 2c_st of b_j, and the number of such j′ is at most the number of bonds within r + L + 2c_st of b_j. Periodic shells are at most the infinite-lattice shells (L2028), so that number is at most C(1+r)⁴. The last sum is therefore bounded uniformly in n and the torus.

**(5) What this gives, and what it does not.**
- E^∂_D is an exact sum of activities attached to Dᶜ. Each depends on D only inside its own set X, and each decays from the contour at the rate c' = min(c'', a/2) of (4), not V3's rate c. This meets the diameter-weighted clause of the class 𝔇₁ (§4) for the carrier part of E.
- *Shape (review S2).* The sets X = B_{m+1} are balls around supp Γ: |X| ≍ m⁴ bonds, while the terms that produce them decay only like e^{−a₀m}. So a bound weighted by |X|, or by tree length, does not follow from these estimates (d-d13-r2 m7). Whether D2 can use a diameter weight is open (gaps block, D2).
- *Check.* Summing the anchored bound over j gives |E^∂_D| ≤ Cτ²Σ_j e^{−c''d_j}. This is V3's bound (regional-square-boundary-comparison), with c'' in place of c.
- *Scope.* The carrier at a labelled term is D(Λ), which depends on the history and the labels.
  - The decomposition is local in D(Λ).
  - D(Λ) is built by the retreat of §c5-3 (L2400–2431), not by Lemma c5-6-2. Lemma c5-6-2 compares activities at D(Λ) and at I for domains with no cube of 𝒩_lab. It belongs to the item on a^Λ_W below, in its "marked" form (Remark c5-6-5: "what is local is the marking, not the domain").
  - What §c5-3 gives about position: every site of (Λ₁^{(0)})ᶜ is within 100ℓ of CRE's unfilled bad region (Lemma c5-3-0(b)). Every site of Λ₁^{(0)} ∖ Λ₁^fin is within 102ℓ of x_e for a bond e found bad (Lemma c5-3-1(c)). At most N_ret = 4(207ℓ)⁴ bonds are removed on account of one bad bond (Lemma c5-3-1(d)).
  - What §c5-3 does not state: that D(Λ) ∩ Y is determined by the history and labels near Y. Fill acts on components inside cubes of side 100ℓ, but its fixed point and the rounds are defined globally. This is needed only if D2 expands e^{E^∂} into polymers (gaps block, D2, with S2). §3g(2) shows that D2 needs only the polymer form of the label sum, which is derived.
- *What §3b does not cover.*
  - E°_{T,n}, which depends only on n and the torus (L161) and is a constant of the contour.
  - The carrier dependence of the group activities a^Λ_W and q°, through H°, 𝖫_Z, 𝐃₀(Λ), E₀ and C_{E₀} (Remark c5-5-11(1)). Derived in §3g(1) for the reference species; the t > 0 species are a D2 item.
- *V-independence.* By (Q2), E^∂_{D(Λ)} is a number on each labelled term. It needs no analytic continuation in V (D1.2b).
- *Reviewed* in it1-d-d13-20261021-r1 (report 22:59): no fatal finding. S1, S3 and m1–m10 are repaired here; S2 is in the gaps block under D2.
- *Round 4* (it1-d-d13-20261022-r2): no fatal finding, and every inequality was hand-checked. S1 (C_K undefined and clashing with §3f(3)'s ℓ-dependent C_K) is repaired by the fixed stencil reach c_st = 2L+2 of (2). m1–m7 are repaired in place. The repairs are not reviewed.

## 3c. D1.0: the assembly (step 1, with the choice (P); reviewed up to (4″) and repaired)

*Setting.* The first step. V3's branch data are ξ = (Ω₁, R₁, V, V₀, A_e) (L2082, L2978). The outer operation is 𝒪 (L280). The branch weight is 𝗐_ξ = ∫_{𝔤^I} ρ_ξ da_old, and the conditional loop is F_ξ(1) = 𝒥^a_ξ[f_ξ]/𝒥^a_ξ[1] with f_ξ = W_χ(C;U_ξ(a)) (L2978).

Repaired at 23:25–23:31 after review it1-c-d10-20261021-r1 (S1–S3, M1–M13). The repairs of S1 and S3 are in (4⁗).

**(1) At step 1, CRE's ρ₁ is Tρ₀ by equalities.**
- CRE (0.1), p.243: (Tρ)(V) = ∫dU δ(ŪV⁻¹)ρ(U).
- The first-step section rewrites Tρ₀ by equalities:
  - (1.11), p.248: "This yields the equality";
  - (1.15), p.249, and (1.17)–(1.19), p.250 (not reread here);
  - the change of variables (1.22), p.251, and its Jacobian (1.24), p.252: "After the change of variables we obtain an expansion of the form (1.15)";
  - (1.26), p.253: "The above equalities define the functions V^{(0)} and E^{(1)}";
  - the renormalisation (1.27), p.253, and the collection of all constants into E₁, which "depends on Ω₁, Λ₁" (p.254).
  - Two steps are Bałaban's presented-as-true statements, accepted: dropping χ₀, χ_Ax on p.248 "if A₀ is sufficiently larger than A₁", and separating 𝐁^{(1)} on p.253.
- *No R at step 1 (fact).* CRE (1.6), p.247, writes ρ₁(V) as T applied to ρ₀, with partitions of unity. Of the R-operation p.244 says "We will not describe it here", and its terms enter only in the generalisation of (1.28)–(1.30) (p.254). So ρ₁ of (1.28) is Tρ₀. This was reading R-b; it is now a fact.
- *V^{(0)} (definition; was reading R-a).*
  - p.252: "Expanding the terms of the effective action … with respect to the last two perturbative terms in (1.22) up to the first order, we obtain a new expression V^{(0)}(S₁,A,𝐇_{1,Ax})".
  - Here V^{(0)}(S₁) is defined as the exact change of that exponent under (1.22). V3 does the same: "The definition retains p_ξ∘Ψ_ξ without a truncation of the boundary terms described after CRE (1.24)" (L2132).
  - The first-order Taylor formula with integral remainder, f(A′+h) − f(A′) = ∫₀¹ ∂f(A′+th)·h dt, with h = −g₀⁻¹(g𝐇_{1,Ax} + 𝐅), writes this exact change in first-order form.
  - So CRE's stated properties hold for it, for CRE's reasons: a sum over b ∈ S₁* (h is supported there); almost local, by "the almost local character of the action in (1.15)"; analytic in 𝐇_{1,Ax}; and small, since |𝐇_{1,Ax}| < O(1)B₃e^{−δMR₁}ε₁ (p.251). The intermediate points A′+th stay in the analyticity domain, since |h| ≪ g₀⁻¹δ₀.
  - The Jacobian (1.24) is exponentiated exactly ("can be exponentiated", p.252).
  - (1.22) is taken on V3's set (L2108: the second form "on the other bonds of S₁*, a set differing from the one printed at p.252", as recorded in V3 Section boundary-law-collar). The identifications of A₁, V^{(0)} and the Jacobian are with V3's version. F_ξ(1) is unaffected on covered branches, since it uses A_e only where Ψ_ξ = id.
- So ρ₁ of (1.28) and V3's ρ₁ = M_*(ρ₀dU) (L91) are equal as measures, for the averaging choice V3 takes after (0.1) (L2082). The inner fibre integrals agree at every admissible (V, V₀) (L269). No density is asserted: "No absolute continuity is asserted or needed" (L91).
- LFR I p.200: after R-operations the density "may not be equal to ρ_k, but is equivalent to it, in the sense that they have equal integrals". This matters from step 2 on (D2), not at step 1.

**(2) The integrands agree label by label.**
- V3 (L280): 𝒪[𝔐](V) = Σ_{Ω₁,R₁} χ₁ ∫δ(V̄₀V⁻¹)[∫ι_ξζ_ξχ_{ξ,e}κ_ξ𝔐_ξ dA_e|_J] dV₀|_{Ω₁ᶜ}, with κ_ξ the prefactor of (1.15).
- CRE (1.28)–(1.29): Σ_{Ω₁,Λ₁} χ₁ Σ_{S₁} ∫dV₀|_{Ω₁ᶜ} δ(V̄₀V⁻¹)ζ(Ω₁ᶜ) ∫dA|_{Ω₁∩Λ₁ᶜ} χ(Ω₁∩Λ₁ᶜ,S₁)·G_{Λ₁}(A)·exp A₁. Here G_{Λ₁} is the exponential of the two quadratic forms in (1.29).
- *Labels.* (Ω₁,R₁) determines (Λ₁,S₁) by (1.20) and the filling (p.251), and "the set S₁ determines the set R₁" (p.253), since R₁ = S₁ ∩ Ω₁^{∼−1} (R₁ ⊂ Ω₁^{∼−1}, p.250). So the label sums agree: the Σ_{Λ₁}Σ_{S₁} of (1.28)–(1.29) is the regrouping Σ_{R₁} = Σ_{Λ₁}Σ_{S₁: Λ₁(Ω₁, S₁∩Ω₁^{∼−1}) = Λ₁} of the R₁-sum of (1.25), an identity (review it1-c2-place m8).
- *Variables.* V3's J is the set of free bonds of Ω₁ outside I = Λ₁* (L2082: "J = E_{Ω,*}∖D" with D = I). CRE integrates A|_{Ω₁∩Λ₁ᶜ}. Both use the variables of V3's version of (1.22) ((1)). CRE's (1.26)–(1.30) are taken at V3's split, I = Λ₁* and J = E_{Ω,*}∖I. That is exact, since the split (1.26) holds whichever free bonds are called interior (§3c(4″)). Agreement with [I] Sect. 0's bond convention matters only where CRE's statements about 𝐄^{(1)} and 𝐁^{(1)} are used; there it is a logged reading, in the list of (d) (review it1-c2-place m1).
- *Integrands (corrected after c2-r2 minor "integrands").* At each label and outer datum, ι_ξζ_ξχ_{ξ,e}κ_ξ𝗐_ξ and ζ(Ω₁ᶜ)χ(Ω₁∩Λ₁ᶜ,S₁)·ι_ξ·Π_{off-Λ₁ rows}(z_c(U₁)/z_c(1))·G_{Λ₁}·exp A₁, with A₁ as modified in (a) and ι_ξ one on the support by (e), are the integrand of (1.15) with the cutoff (1.25), in the variables of (1.22), integrated over the fluctuation field on Λ₁. V3 integrates a ∈ 𝔤^I over the box, which is the fibre of the domain on a branch (L2112, L2121; Lemma c5-3-3(iv) at the retreated carrier). CRE integrates A|_{Λ₁} with χ^{(0)}(Λ₁) in (1.26).
- *Bookkeeping of the identification (review it1-c-d10 G1; closed 23:35–23:45).* Some placements are not displayed in CRE (1.26)–(1.30). They are fixed in items (a), (b), (c) and (e) below; item (d) lists the inputs (c2-r2 minor "counting"). Each placement is made in an exact identity, not an estimate.
  - (a) *z^{(0)}(U₁) (repaired after review it1-c2-place S3, m2–m4, m10; §3f).* By V3 L298, z^{(0)}(U₁) = c_{Ω₁}·Π_{c∈Ω₁^{[1]}} |det_𝔤 α_c(U₁)|⁻¹, with a constant c_{Ω₁}. Each factor depends on U₁ on the two blocks of c only (V3 L311).
    - It is gauge invariant: "Under a site gauge transformation u, α_c(U^u) = Ad_{u(c_−)}α_c(U)Ad^{−1}_{u(b₀(c)_−)}" (Lemma two-block, L352), and Ad maps are orthogonal for the Ad-invariant inner product, so |det| is unchanged.
    - Two-sided bound. At every row there is a gauge with U₁ = e^{iφ}, ‖φ‖_∞ ≤ τ_L/2 on 𝓔_c (L311). For ‖A‖_∞ ≤ τ_L, α_c is "analytic in A with smallest singular value at least L^{−4}/2" (L352), so |det α_c| ≥ (L^{−4}/2)^{d_G}; the upper bound is continuity on the compact set. So z_c := |det α_c|⁻¹ has |log(z_c(U₁)/z_c(1))| ≤ 2C, with C depending on L and G. det α_c is real, nonzero on the connected set ‖A‖_∞ ≤ τ_L and equal to L^{−4d_G} at A = 0, so it is positive and |det α_c| = det α_c is analytic there.
    - z^{(0)} sits in κ_ξ, outside 𝒥 (L298), so it never enters F_ξ(1), F^Λ(1) or any ratio of D1.
    - *Placement.* The constant c_{Ω₁}Π_c z_c(1) goes into E₁ (p.254: "E₁ is obtained from E by subtraction of all the constants which have appeared in the procedure"). p.254's "i.e." lists only the constants in the first exponential of (1.15) and 𝐄^{(1)}(Λ₁,g₀,1), and z^{(0)} stands outside that exponential. So this placement is *reading R-i*: "all the constants which have appeared" includes c_{Ω₁}Π_c z_c(1) (c2-r2 minor "E₁"; logged in (d)). The rest is Σ_c log(z_c(U₁)/z_c(1)):
      - *Rows of Λ (Λ₁ for CRE's labels), into A₁ as part of E^{(1)}(Λ).* As an identity no reading is needed: A₁ is defined to contain these terms. What is used later is that 𝐄^{(1)}(Λ) + Σ_{Λ-rows} log(z_c(U₁)/z_c(1)) has the properties CRE states for 𝐄^{(1)}(Λ). This follows from Bałaban's own statements. CRE's 𝐄^{(1)} "coincides with the corresponding function constructed in [I], if the last is suitably restricted to the domain Λ₁" (p.254). p.254 combines log Z^{(0)}(Λ₁) with the old 𝐄^{(1)}, and the result "coincides with the corresponding function constructed in [I]". In RG1 (1.3)–(1.4) (p.260) the zeroth-order term paired with −β₁A is [log Z^{(0)}(U) − log Z^{(0)}(1)], with Z^{(0)}(U) = ∫dB δ(Q̃B) exp[−½⟨B,Δ^{(0)}(U)B⟩]; p.260 displays it separately from [𝐄^{(1)} − …], and [I] writes its action "not … separat[ing] the terms of zeroth order" (RG1 (1.6), p.261). (Corrected after c2-r2 minor "R-f": the earlier sentence "[I]'s 𝐄^{(1)} contains [log Z^{(0)}(U) − log Z^{(0)}(1)]" is withdrawn.) And "the expansion of the log Z^{(j−1)}(U_j) constructed in [16], implies, that we can represent this term in the form (1.7)" (p.261), the local form. *Reading R-f (weakest form):* integrating the δ-function of RG1 (1.4) over the designated variables gives the factor c·Π_c|det α_c(U)|⁻¹ times the free-variable normaliser, which needs RG1's Q̃ to be V3's Q_U (V3's own recorded reading, in the step list L269–314: "RG1's Q̃ … is Q_U", taken at its stated status) and the designated bonds b₀(c) (V3: "b₀(c) is the only designated bond in 𝓔_c", L348).
      - *All other rows (those with a block in Λᶜ), into the T₁-integrand.* Π_{c ∉ Λ-rows} z_c(U₁)/z_c(1) is a positive factor of the T₁-integrand: an analytic, positive, gauge-invariant, row-local function of U₁(V,V₀) (corrected after c2-r2 M-B). U₁ depends on V throughout Ω₁, so the factor does not have the localisation of χ(Ω₁∩Λ₁ᶜ,S₁) (pp.251–252); its status is that of the U₁-dependent coefficients of the quadratic forms in (1.29) ("all the above expressions depend on the configuration U₁", p.253). A row has diameter < 2L < ℓ, so it meets at most one ∗-component X of Λᶜ (distinct ones are ≥ ℓ+1 apart), and the factor groups over the X of (4⁗)(d). It lies in [e^{−2C}, e^{2C}] per row, so its total is at most exp(2Cd|Z₁∩Ω₁|) with Z₁ = Λᶜ, the row count being at most d times the volume. Its sup bound is of the same type as p.383's "The integrals with respect to the fields A_j … we get the factors exp O(1)|Z_j∩Ω_j|" (p.383 produces upper bounds, not integrand factors), and (1.79) absorbs it into its first exponential. So it changes only that O(1), for (1.79). Its compatibility with the uses of (2.21) other than (1.79) (the R-operation, step 2) is a D2 item (c2-r2 M-B). No per-test large-field factor and no 𝐁₁ criterion is used. This replaces the 𝐁₁ placement and its count check, whose per-test factor was not established (review S3).
    - The Λ-rows term is a function of U₁ = U₁(V,V₀), like −A(1/g₁²,U₁), and enters through exp A₁, which depends on all variables. CRE's T-operations factorise as operations (p.258: "involves integrations and variables restricted to this region"), so neither placement touches (2.19).
  - (b) *ζ(Ω₁ᶜ).* It depends on V, V₀ and on A_e at the bonds of Ω₁ within 2L²M₂R₁+1 of Ω₁ᶜ (V3 L294). These bonds lie in Ω₁∖Ω₁^{∼−1} ⊂ S₁. It does not depend on a (V3 (c-large-field-factor), L298).
    - It is a nonnegative factor of the T₁-integrand. It depends on A on S₁-bonds, so it stands inside ∫dA|_{Ω₁∩Λ₁ᶜ}; (1.29)'s print is read with that scope. Inside the joint integral its position is then free: by Tonelli for the nonnegative denominator integrand, and by Fubini for the F-weighted numerator (|f_ξ| ≤ 1, integrability from V3) (review it1-c2-place m6; c2-r2 minor "Fubini").
    - Under (P) it groups over the regions X of (4⁗)(d). This follows from CRE (2.19) for CRE's T₁ at Λ₁ (accepted), since every component of Λ₁ᶜ lies in one ∗-component of Λᶜ ⊇ Λ₁ᶜ (for CRE's adjacency, which is no coarser than ∗: review it1-c4q-rep M9). A product over components, grouped by a coarser partition, is again a product. Two readings are used here (review it1-c2-place m7), logged in (d): *R-g*, (2.21)'s unrestricted "ζ(Ω_{j+1}ᶜ)" inside T^{(j)}(Z∩X) is ζ restricted to X; *R-h*, (2.19) holds for V3's version of (1.22), which differs from the printed one only on bonds of S₁* (L2108) and acts bond by bond (L458).
  - (c) *The J-bond parts of χ^{(0)}(Λ₁).*
    - A sup-test is a product of single-bond tests: χ({sup_{b∈X}|A(b)| < r}) = Π_{b∈X} 1{|A(b)| < r}. Indicators are idempotent, so the product over the cubes of R₁ᶜ in (1.18) equals Π_{b∈𝔅} 1{|A(b)| < r} over the union 𝔅 of the bond sets (□′^{∼2})*.
    - So χ^{(0)} splits exactly into the tests at I-bonds and at J-bonds. In the variables of (1.22) the J-part is a function of A_e and the branch data (V3 Lemma collar-coverage(ii), with the exact composition (retained-cutoff-composition); (ii) is applied off branches too, as in (e), since its proof uses only (i), the standing conditions and (c-bondwise-shift), c2-r2 minor "collar-coverage(ii)"). The I-part is the box {Θ_ξ = 1} (Lemma collar-coverage(iv)).
    - The cubes of R₁ᶜ∩Λ₁ᶜ next to Λ₁ also test I-bonds, through (□′^{∼2})*; these factors sit in CRE's χ(Ω₁∩Λ₁ᶜ,S₁). At an I-bond each is 1{|a_b| < r}, a factor of the box, so by idempotence the box times them is the box. So the I-part of the whole product of good-cube tests, over all cubes, is the box, and χ(Ω₁∩Λ₁ᶜ,S₁) is read as its J-part. T₁'s cutoff then does not depend on A|_{Λ₁} (review it1-c2-place m5).
    - The large-fluctuation tests of the cubes of R₁ read no I-bond. Their bonds lie within 2L²M₂R₁ < ℓ of R₁, while Λ₁ ⊂ (R₁′^∼)ᶜ.
    - Placement: the J-part goes into χ(Ω₁∩Λ₁ᶜ,S₁) of T₁. CRE's χ^{(0)}(Λ₁) in (1.26) is read as the I-part. Both groupings give the same function, so (1.28) is unchanged.
    - Under (P) the box factors at I∖D(Λ) are single-bond tests. Such a bond has no endpoint in Λ, so both endpoints lie in one region X of (4⁗)(d).
  - (d) *V3's (B1)–(B4), and the inputs of the identification (corrected after review it1-c2-place m9).*
    - (B1)–(B4) record what V3 takes from CRE's own derivation of (1.11)–(1.25) (V3 L307: "taken from CRE as stated there, except where an item records a reading, a derivation or a proof").
    - The identification with (1.28) uses, beyond them: CRE (1.26)–(1.30), taken at V3's split as in *Variables* (V3 does not use them: "CRE's (1.26)–(1.29) are not used", L2082); the definition of V^{(0)} in (1); the separation of 𝐁^{(1)} (p.253, accepted); readings R-f, R-g, R-h, R-i above; and four readings named in round 4 (c2-r2 minor "unlisted readings"):
      - the constraint Λ₁(Ω₁, S₁∩Ω₁^{∼−1}) = Λ₁ in (1.29)'s Σ_{S₁} (*Labels*);
      - the scope of ζ(Ω₁ᶜ) in (1.29), inside ∫dA|_{Ω₁∩Λ₁ᶜ} ((b));
      - χ(Ω₁∩Λ₁ᶜ,S₁) read as the J-part of the good-cube tests, and χ^{(0)}(Λ₁) as their I-part ((c)).
    - (P) changes none of (B1)–(B4), since V3 keeps U₁(Ω₁∩Λ₁ᶜ,V), S₁, R₁ and Ψ_ξ of the original Λ₁ (L2423).
    - Status: CRE's statements are accepted (Bałaban's presented-as-true results). V3's readings inside them are the ones V3 names in (H4): the representative of the local minima, the O(L²) and (B3)(iii) constants independent of the coupling, U₁(Ω₁∩Λ₁ᶜ,V) as a minimal configuration, the rows with one block off Ω₁, D̃ = φ, CRE's "in the domain of integration in (1.11)" read as the support of every characteristic factor of (1.11) ((B1)(iii)), and CRE's compatible partitions read as nested ((B4)(i)). They are carried as logged readings, not as new conditions. The bond convention of [I] Sect. 0 (see *Variables*) is one more.
  - (e) *The branch indicator ι_ξ (review it1-c2-place S1; derived).* ι_ξ(A_e) = 1 exactly when (A_e, 0) ∈ 𝒟_ξ, "a Borel condition" (V3 L277). It is a factor of V3's integrand and has no displayed counterpart in CRE.
    - *Its content.* The proof of Lemma collar-coverage(iv) (V3 L673ff.) lists what membership B ∈ 𝒜_ξ means: (1.25) at B is nonzero; every row equation has a solution at g₀𝖢_UB; and the tests of (1.11) at U(B). At a = 0, B = Ψ_ξ(A_e). There:
      - (1.25) at B equals Θ_ξ(0)χ_{ξ,e}(A_e) = χ_{ξ,e}(A_e) (Lemma collar-coverage(ii); its proof uses only (i), the standing conditions and the bondwise shift (c-bondwise-shift)).
      - The near rows, within 2R_c + 2L of I, are solvable by Lemma charts once |B| < 2+4r on their two-block sets. On J-bonds within 3R_c of I this is |A_e(b)| < r, "a factor of χ_{ξ,e}(A_e)" (proof of (iii)). So on the support of χ_{ξ,e} the near rows impose nothing.
      - Each far row is solvable or not according to B|_{𝓔_c∩E_*} alone (Lemma row-locality), and Ψ_ξ "acts bond by bond and is the identity off S₁*" (L458). So its condition is a function ι_c of A_e on 𝓔_c and the branch data.
      - The constraint on the rows and the restriction V₀ off Ω₁ follow from the row equations, and the rows of Ω₁ᶜ from admissibility (same proof). χ₁(Ω₁) and ζ(Ω₁ᶜ) are factors of the integrand already. The other cube factors χ'₀(□′) are one by (B3)(ii).
    - *The far rows are solvable on the support (round 4, it1-c2-place-20261022-r2 S-A; derived 22 Oct).* The earlier placement of the far-row indicators ι_c in χ(Ω₁∩Λ₁ᶜ,S₁) is withdrawn: ι_c depends on V through U₁|_{𝓔_c}, against CRE's localisation (p.252: after the change of variables "the characteristic functions depend on the new variables V restricted to the large field domain Λ₁ᶜ. It is the desired localization property"). Instead, ι_c = 1 on the support of the other factors:
      - Let B = Ψ_ξ(A_e) on J and B = 0 on I. Take a free bond b of a far row; it lies in J (far rows miss I). Let □′ ⊂ Ω₁ be the L²M₂R₁-cube containing an endpoint of b in Ω₁, chosen in S₁ when b ∈ S₁*. Then b is a bond of □′^{∼2}.
      - If □′ ⊂ S₁: the factor χ′₀(□′) of (1.25), in the variable of (1.15) (V3 composes the cutoff there, L542), gives |e^{ig₀B(b)}U₁(b)U_{1,□′}⁻¹(b) − 1| < 2δ₀ ((1.19), second factor; it stays for □′ ⊂ S₁, p.250). V3 (B1)(ii)–(iii) gives |U₁U_{1,□′}⁻¹ − 1| < O(L²)ε₀ on □′^{∼2} (CRE p.247; L309), boundary cubes of Ω₁ included. So |e^{ig₀B(b)} − 1| < 2δ₀ + O(L²)ε₀, the same combination V3 makes in the proof of Lemma c2-fibre-smallness(ii) (L3742). g₀B(b) lies in the chart ball, since A_e(b) ∈ 𝒲_b is a factor of χ_{ξ,e} (L542).
      - If □′ ⊂ R₁ᶜ: then b ∉ S₁*, Ψ_ξ = id at b, and the good test of □′ gives |B(b)| < g₀⁻¹δ₀.
      - Hence h(g₀B(b)) ≤ c_Gc_h(2δ₀ + O(L²)ε₀) on every free bond of the row (V3's norm comparisons). A|_{𝓔_c} = g₀𝖢_{U₁}B|_{𝓔_c} has these entries on the free bonds and, at b₀(c), the linear elimination (regular-stencil-elimination), bounded by a constant C_𝖢(L,G) through |α_c(U₁)⁻¹| ≤ 2L⁴ (L352). So ‖A|_{𝓔_c}‖ ≤ n_𝓔^{1/2}(1 + C_𝖢)c_Gc_h(2δ₀ + O(L²)ε₀). This is < ϑ_*/2 once g₀ is below a threshold depending on L and G only (δ₀, ε₀ → 0 with g₀). That is one more smallness condition on g₀, of the kind of V3's threshold item 6 (not in V3).
      - Then A ∈ 𝒩_Θ, and Lemma c2-fibre-smallness(iv) gives the small chart-class solution φ_c at every row, with Θ chart-valued. So the reconstructed field U(B) = e^{iΘ}U₁ is defined. Its (1.11) tests are (1.25) at B for the χ′₀ part, and χ₀, χ_Ax are one on the support of the rest (p.248, accepted; (B3)(i)).
      - So, at an admissible pair, χ₁ζχ_{ξ,e}·ι_ξ = χ₁ζχ_{ξ,e}: ι_ξ is one on the support and is omitted from T₁. The membership list of the proof of Lemma collar-coverage(iv) is covered item by item: (1.25) at B is χ_{ξ,e}(A_e) (collar-coverage(ii), applied off branches too, since its proof uses only (i), the standing conditions and (c-bondwise-shift)); the Ψ-domain is the factor 𝒲_b of χ_{ξ,e}; the chart class of the free bonds and the solvability of every row are the items above; the averages are defined on D^{(11)}.
      - *1_adm.* Admissibility of (V, V₀) is CRE's own implicit domain of U₁, a function of (V, V₀) present in CRE's T₁ through the V₀-integral. Its placement is CRE's; it is covered by accepting (2.19) for CRE's T₁, as reading R-g does for ζ (c2-r2 S-A(2)).
    - Off the branches CRE's conditional integral over A|_{Λ₁} is over an empty fibre and vanishes. With the item above, the branches contain the support of χ₁ζχ_{ξ,e} at admissible pairs, so the identity below holds with ι_ξ omitted.
- *Consequence.* Let N₁ = M_*(W_χρ₀dU). As measures, using 𝗐_ξF_ξ(1) = 𝒥^a_ξ[f_ξ] (L609) and V3's (native-source-physical-ratio):
  - N₁ = 𝒪[𝗐_ξF_ξ(1)] = Σ_{Ω₁,Λ₁} χ₁ T₁[F_ξ(1)·exp A₁], with the placements (a)–(e) above (A₁ includes the Λ-rows of log z^{(0)}(U₁); T₁'s integrand includes the other rows; ι_ξ is one on the support of χ₁ζχ_{ξ,e}, (e)). F_ξ(1) is defined on branches, which contain that support.
  - On the right, F_ξ(1) is a function of (Ω₁,Λ₁,S₁,V,V₀|_{Ω₁ᶜ},A|_{Ω₁∩Λ₁ᶜ}). T₁ integrates V₀|_{Ω₁ᶜ} and A|_{Ω₁∩Λ₁ᶜ} and sums S₁; V and the outer labels are parameters (c2-r2 minor "V a parameter").
  - So F_ξ(1) is the loop factor in the form (1.28). It is a π_ξ-average of terms of §4's form (see (3)), not itself of that form.

**(3) The label sum and the de-younged bonds (V3 Lemma c5-6-1, L2982).**
- 𝒥^a_ξ[f] = Σ_lab 𝒥^{a,lab}_ξ[f], with Σ_lab 1_lab = 1 pointwise (L2978).
- (c5-6-1): 𝒥^{a,lab}_ξ[f_ξ] = ∫_{𝔤^{I∖D(Λ)}} 1_lab e^{c^Λ_ξ}I^Λ_1F^Λ(1) da_old|_{I∖D(Λ)}. 𝗐^lab_ξ is the same integral without F^Λ(1).
- Hence F_ξ(1) = Σ_lab ∫π_ξ(lab, da_old|_{I∖D(Λ)}) F^Λ(1), with π_ξ := 1_lab e^{c^Λ_ξ}I^Λ_1 da_old/𝗐_ξ.
  - π_ξ ≥ 0, since ρ_ξ ≥ 0 ((retained-positive-kernel)), and it has total mass 1.
  - π_ξ is the law of (lab, a_old|_{I∖D(Λ)}) under the normalised conditional measure ρ_ξda_old/𝗐_ξ on 𝔤^I.
- *Where the de-younged variables sit depends on the choice in (4).* With CRE's labels, a_old|_{I∖D(Λ)} are integration variables of the step-1 conditional integral over 𝔤^I, inside CRE's integral over A|_{Λ₁}. Under (P) they are variables of T₁^lab, and §4's "outer variables … the de-younged bonds" is the (P) reading.
- The round-0 collar tests read A_e on J (L2417), which is an outer variable. So 1_lab is partly a function of ξ.

**(4) What is left: the form of the label average. Two options.**
- *(A) Average over the labels.* Keep CRE's labels. On covered labels (§2, §3b):
  - 𝒲₁ = κ_C e^{E°_{T,n}} Σ_lab ∫π_ξ e^{E^∂_{D(Λ)}}[f_ξ(m) + Σ_𝔅 q°(𝔅)·tr(…)/dim π].
  - D1's relative form needs the logarithm of this average to be a local sum along the contour. That needs a polymer representation of π_ξ, with retreats as polymers and distant retreats decoupled under ρ_ξ.
  - (A) needs a cluster expansion of the label law under ρ_ξ at fixed ξ. V3's label bounds in the lines read (L2455–2457, Prop. c5-2-6, Lemma c5-3-0(b)) are after the history average, and V3's group expansion (Lemma c5-5-3) is at a fixed label.
- *(P) Make the labels part of ρ₁'s domain structure.* Refine CRE's labels by V3's.
  - The step-1 output becomes Σ_{Ω₁,Λ₁,lab} χ₁T₁^lab[F^Λ(1)·exp A₁^Λ], with:
    - Λ = Λ₁^fin(lab) as the domain of the conditional integral;
    - the de-younged bonds, their box factors and the collar tests moved into T₁^lab;
    - A₁^Λ given by CRE's (1.26)–(1.30) with Λ₁ replaced by Λ.
  - Since Σ_lab 1_lab = 1, the same refinement applied to the denominator is again an equality for Tρ₀. Then 𝒲₁ = F^Λ(1) on each refined term, and the per-term identity of §2 is used without averaging.
  - *The refined data have the form of (2.1) at k = 1.*
    - Λ is a filled union of ℓ-cubes with Λ ⊂ Λ₁^{(0)} ⊂ Λ₁ ⊂ Ω₁ (Lemma c5-3-0(a), Lemma c5-3-1(c)), so it satisfies (2.3).
    - S₁ ⊂ Ω₁∩Λ₁ᶜ ⊂ Ω₁∩Λᶜ, because V3 keeps the S₁ and R₁ of the original Λ₁ (L2423).
    - The new characteristic functions on Ω₁∩Λᶜ are the box factors on I∖D(Λ) and the collar tests: good, |A_e(e)|_σ < ϑr, or bad, ≥ ϑr.
  - *What (P) needs.* CRE's inductive description (Sect. 2) and Theorem 1 must accept the refined labels.
    - CRE's large-fluctuation threshold is sup|A′(b)| ≥ g₀⁻¹δ₀ ((1.23), p.252). With δ₀ = g₀A₁(log g₀⁻²)^{p₀} (p.247, corrected transcription), this is V3's r (L122).
    - A bad collar test is at ϑr, with ϑ ≤ 1/16 (L2403), on a bond where |A_e(e)|_σ < r also holds (Lemma collar-coverage(iii) at the round of testing, or the box factor; (4⁗)(b); Lemma c5-3-3(iii) is stated relative to the final carrier and is not the source, c4q-r2c m-5). It is therefore *not* a CRE large-fluctuation function. It refines the small-field set, and its suppression has to come from the Gaussian weight in T₁. This is the route (P) takes ((4⁗)(b)).
- *Proposed choice: (P).* It moves V3's labels into ρ₁'s domain structure, which D2 must handle anyway (iteration audit IT-2(b)). (A) needs a cluster expansion that does not exist yet. With (P), what remains of D1.0 is D1.0(P), the check against CRE Sects. 2–3.

**(4′) D1.0(P) against CRE pp. 256–259 and Sect. 3 (read 22:23–22:25).**
- *Domains (p.256).*
  - The domains Ω_j, Λ_j "determined by the j-th renormalization transformation" are unions of MR_j-cubes in T_{L^{−j}}. For j = 1 these are ℓ-cubes, and Λ = Λ₁^fin is one.
  - They satisfy "the distance between their boundaries is at least equal to 2MR_j". Λ ⊂ Λ₁ ⊂ Ω₁^{∼−2}, so dist(Λ, Ω₁ᶜ) ≥ 2ℓ.
  - (2.3) holds because Λ is filled.
  - Open: p.256 adds "They satisfy also other conditions, e.g., …, which will be determined inductively"; only the example was checked. Also, p.256 covers domains "determined by the j-th renormalization transformation", and p.255 covers domains modified by R. Λ₁^fin is made by V3's retreat, a third kind. At step 1 the construction at Λ is CRE's construction at an admissible domain ((4⁗)(c)). Whether the later steps accept the third kind is part of D2.
- *The T-operation (pp.257–258, (2.19)–(2.22)).*
  - T_k is supported in the large-field region Z_k and factorises over its components and over the scales.
  - The one-step factor (2.21) integrates V_j on Ω_{j+1}ᶜ and A_j on Z_{j+1}∩Ω_{j+1}, with a characteristic function χ(Z_{j+1}∩Ω_{j+1}∩X) and the quadratic form with C^{(j)}(Λ_{j+1}).
  - The refined T₁^lab has this form at j = 0, with Z₁ = Λᶜ. Its characteristic function is χ(Ω₁∩Λ₁ᶜ,S₁) times the box factors on I∖D(Λ) times the collar tests.
  - The quadratic form "couples only the fields A_j in the same component of Z_{j+1}∩Ω_{j+1}"; the other terms go into 𝐁 (p.258). A retreated region joins the component that contains its bad bond, so its couplings to that component stay in T₁^lab. Only cross-component blocks go to 𝐁₁. Their size is bounded in (4⁗)(a).
- *Thresholds.*
  - CRE's own thresholds are unchanged under (P): its characteristic functions keep A₁. ϑA₁ enters only where the bad-test factor is spent ((4‴), (4⁗)(b)).
  - The conditions on A₁ in the pages read (pp.247, 248, 251, 266, 268), for completeness:
    - upper bounds relative to A₀: A₀ "much larger than A₁" (p.247), "sufficiently larger" (p.248), "A₁/A₀ … sufficiently small" (p.266, twice);
    - lower bounds of the form A₁/A₀ ≫ O(1)e^{−cR}: (3.19), O(1)44d²B₃²(1+β₀)(A₀/A₁)e^{−R_k} < 1 (p.268);
    - p.251: |𝐇_{1,Ax}| < O(1)B₃e^{−δMR₁}ε₁ is "much smaller than δ₀, for MR₁ large enough".
    - Each holds with ϑA₁ in place of A₁ for small g, since R_k → ∞.
- *What remains of D1.0(P):*
  - (i) the Gaussian cross terms at the retreated regions, routed to 𝐁₁;
  - (ii) the uses of the large-fluctuation factor in CRE Sect. 3 and in the R-operation papers, checked for slack in the constant of the exponent.
  - Count check for (ii): a retreat region has at most N⁺_ret = 4(209ℓ)⁴ bonds ((4⁗)(c)), with ℓ = LMR₁ ≍ (log g₀⁻²)^𝔯. A boundary cost of O(1) per bond ((4⁗)(a)) is at most e^{CN⁺_ret}. The bad-test factor would be the integrand factor e^{−cϑ²A₁²(log g₀⁻²)^{2p₀}} at threshold ϑδ₀ (R-d″, §3f(2) R1: the j = 1 factor of (1.79) at step k ≥ N + 1, bounded factor by factor in (D2); OPEN pending D2.7 and the acceptance item; rd5-d2-r3 m8), not the history bound q_ϑ. Given it, since p₀ > 6𝔯 (LFR II p.387, §3f(0)) gives 2p₀ > 4𝔯 + 1, it pays for its region for small g₀, with room; the bookkeeping inside (1.79) is §3f(2) Minor 4.

**(4″) D1.0(P)(i): the Gaussian at the retreated regions (worked 22:34–22:39).**
- *V3's split at Λ is CRE (1.26) with Λ₁ replaced by Λ.*
  - V3 Lemma c5-2-5 (L2366) splits the exponent at Λ = Λ₁^fin. c^Λ_ξ holds the J(Λ)J(Λ) block of H_ξ and the far primitives. K^Λ_{ξ;1} holds the D(Λ)D(Λ) block, the cross term −⟨a, H_{D(Λ)J(Λ)}A^{Λ,Ψ}⟩ and the near primitives. The proof is an exact rewriting of the CRE (1.15) density, whichever free bonds are called interior.
  - H_ξ = 𝖧^{Ω₁}_{U₁} is CRE's C*Δ₁C of (1.15), with Δ₁ as in (1.16) (V3 L382–389). In both, V collects the terms of order higher than two (V3 Lemma primitive-sum, L509).
  - So K^Λ is the integrand of CRE (1.26) with Λ in place of Λ₁, in V3's variables, up to the a-independent factor exp Σ_far 𝔭, which sits in c^Λ. The cross term is −⟨ΛᶜA, C*Δ₁CΛA⟩, and 1_{𝒟^Λ} is the box on D(Λ) wherever the fibre is nonempty (Lemma c5-3-3(iv)).
- *Completing the square.*
  - In (1.26), C^{(0)}(Λ₁) is the inverse of the Λ₁-block of the form and the covariance of a Gaussian measure. So H_II is positive definite. (p.248 also has "a minimum of (1.12), with a strictly positive second order differential".)
  - H_DD, with D = D(Λ) ⊂ I, is a principal block of H_II. By Cauchy interlacing its smallest eigenvalue is at least that of H_II. So C^{(0)}(Λ) := H_DD⁻¹ exists, and ‖C^{(0)}(Λ)‖ ≤ ‖C^{(0)}(Λ₁)‖.
  - Decay: V3 (I3) gives (γ_L/2)id ≤ H_{ξ,DD} ≤ m_L id for every principal restriction (L2270), and it passes to D^fin (Remark c5-3-2). V3 Lemma c5-1-1 (L2280) then gives ‖C^{(0)}(Λ)(b,b′)‖ ≤ γ⁻¹e^{−μ_H d(b,b′)}, with μ_H = γ_L/(8Lm_L).
  - The two equalities of (1.26) then hold with Λ in place of Λ₁; the logarithm is finite because the fibre is nonempty on the support. They define Z^{(0)}(Λ), 𝐕^{(0)} and 𝐄^{(1)}(Λ, g₀, ΛᶜA), as in CRE: "The above equalities define".
  - The quadratic form left in T₁^lab is that of (1.29) at Λ: −½⟨A, H_JJA⟩ + ½⟨A, H_JD C^{(0)}(Λ) H_DJ A⟩ on J = J(Λ).
  - Ψ_ξ differs from the identity only on S₁*. d(I, S₁*) ≥ LMR₁ − 2 (L660 proof) exceeds the range 4L of H_ξ (L609 proof). So the D(Λ) blocks are the same in the old and the new variables. The change on S₁* goes into V^{(0)}(S₁) by its definition in (1), as for Λ₁.
- *Routing to 𝐁₁.*
  - (2.21) keeps in T only the blocks within one component of Z₁∩Ω₁ = Ω₁∩Λᶜ. The cross-component blocks are moved into 𝐁₁ by an equality: at k = 1, (1.29) displays the full form, and the component split is the general statement of p.258.
  - These blocks are of two kinds:
    - blocks of H_JJ between components within its range (H_ξ is a stencil sum, (regular-stencil-quadratic-decomposition));
    - the Schur term H_JD C^{(0)}(Λ) H_DJ, which couples components through Λ.
- *What is new relative to CRE's Λ₁.*
  - The new T-variables are the de-younged bonds I∖D(Λ). The collar bonds of J are already T₁-variables; the collar tests are new functions of them.
  - Collar bonds are within ρ_L = 4L < R_c of D(Λ) ⊂ I (R_c ≥ 2R_loc + 1 = 4L + 5). For e ∈ J_col(Λ), d(e,I) ≤ d(e,D(Λ)) ≤ ρ_L, so by collar coverage (i) every one of these bonds lies in 𝒢_ξ∖S₁* (Lemma c5-2-3(a)), away from R₁ and S₁*.
  - The fields are bounded by r on all of them: on I∖D(Λ) by the retained box factor (Lemma c5-2-5), and on the J bonds by Lemma collar-coverage(iii), since d(e,I) ≤ d(e,D(Λ)) ≤ ρ_L ≤ 3R_c (also Lemma c5-2-3(b)).
  - So the boundary data of the conditional integral on Λ are small fields, as for Λ₁: on Ω₁∩Λ₁ᶜ by CRE's χ^{(0)}(R₁ᶜ∩Λ₁ᶜ), and on Λ₁∖Λ by the box factors.
  - The new characteristic functions split [0, r) at ϑr on the tested collar bonds. No field above r is introduced. For a bond tested at an earlier round k, the same bound holds with D^{(k)} in place of D(Λ): d(e,I) ≤ d(e,D^{(k)}) ≤ ρ_L (proof of Lemma c5-3-1(a)), and e ∈ I∖D^{(k)} ⊂ I∖D(Λ) in the box case (c4q-r2c m-1).
  - The cost of the new 𝐁-terms and its payment are in (4⁗)(a), (b).
- *Reading R-c (extended after review it1-c-d10 G6).* CRE's k = 1 construction for Λ₁ (the cluster expansion of 𝐄^{(1)}, the 𝐁 representation; accepted) uses these properties of Λ₁:
  - Λ₁ is a filled union of ℓ-cubes, inside Ω₁ at the required distance;
  - its boundary data are bounded by r;
  - (α) "On the set Λ₁^∼ we have only the small fluctuation field characteristic functions from (1.18)" (p.251; p.269 at the general step);
  - (β) its boundary lies near R₁ or Ω₁ᶜ, so that 𝐁^{(1)} "is controlled by the large field estimates" (p.253);
  - (γ) the large-fluctuation functions in χ(Ω₁∩Λ₁ᶜ,S₁) are "associated with the set R_j" (p.255), with the (1.21)–(1.22) localisation around them;
  - (δ) the 𝐇_{1,Ax} bound uses the distance > MR₁ between □′ ⊂ S₁ and ∂Λ₁ (p.251).
  - (4⁗)(c) checks each of these for Λ = Λ₁^fin with the enlarged retreat. R-c then says that CRE's construction uses no other property of Λ₁. It is checked against pp.247–258 and 269. (α) is stated in sublevel-set form, and it is checked against every use of Λ^∼ in CRE pp.243–285 (grep: p.251 l.8, l.23–24; p.269 l.18) and of LFR I (1.9) (pp.179, 183, 187) in §3f(3) S1. The second use on p.251, the background U₁(Ω₁∩Λ₁ᶜ,V), is item (δ).
- *Status.* (i) is derived at step 1, using reading R-c and the repairs of (4⁗).

**(4‴) D1.0(P)(ii) and the check of R-c (read 22:48–22:58: CRE pp.259–264, 269–270; LFR II pp.380–385).**
- *Where the factor is spent.*
  - The inductive assumption (CRE Sect. 2, pp.255–262) states domains, the T-form, the localised 𝐄, 𝐑, 𝐁 with (2.26)–(2.28), (2.31) and (2.41)–(2.42), and E_k. It contains no large-field estimate. So at k = 1, (P) has to meet only these, which (4′) and (4″) check, except p.256's "They satisfy also other conditions … determined inductively", of which (4′) checked only the example; that item is open and deferred to D2 (c4t-r2 m6).
  - The small factors are used in two places:
    - In Corollary 3, through (2.49): "The first term on the right-hand side yields the small factors for large field characteristic functions", with the combinatorics "as in [6]", Sect. 3, (3.42) (p.264). [6] is Higgs_{2,3} II, CMP 86 (1982), which is not transcribed.
    - In the R-operation: LFR II Sect. 1, pp.380–389, the "fundamental large field factors".
- *LFR II's mechanism (pp.380–383, read).*
  - χ^{(j−1)c}(R_j) yields exp(−γ₀g_j⁻²δ_j²(LM₂R_j)^{−d}|R_j|) "by the same positivity bound for the quadratic form" (p.380). This is one factor per cube of the large-fluctuation set.
  - The MR_j-cube cover of P_j∪Q_j∪R_j has components Z_j^{(i)}. Each yields exp(−γ₀min{½B₃⁻²A₀², 2A₁², A₁²}p₀²(d_j′+1)) ≤ exp(−½γ₀A₁²p₀²(d_j′+1) − 2p₀) (p.381). Here d_j′ is the linear size in MR_j-cubes.
  - The costs are O(1)M^dR_j^{d+1}d_j′(Z_j) per large-field domain (p.380) and exp O(1)(MR_j)^{−d}|Z_j| for the sums over admissible sequences (p.383). They are summarised in (1.79).
  - The geometry is (1.76): Z_j ⊂ Z′_{j−1}^{∼10} ∪ ⋃_i(Z_j^{(i)})^{∼2}.
- *(P) in this mechanism.*
  - A bad collar bond (|A_e(e)|_σ ≥ ϑr) yields its factor from the T₁^Λ form, jointly for all bad cubes (R-d″, §3f(2) R1: derived pointwise in (D1), with the R₁ cubes in (D1⁺); the j = 1 factor of (1.79) at step k ≥ N + 1 is bounded factor by factor in (D2) under reading R-c, with R-p (location checked; rates quoted from p.380 (step k ≥ N + 1)) and R-q₀ quoted and checked, recorded, not used, and V3's logged (B1)(iii), (H4) (R-q's layer clause withdrawn, rd5-dbq S1); OPEN pending D2.7 and the acceptance item (§3f(2) R1 status; rd5-d2-r4 m-1(b)); dbq-r2 m-g, rd5-d2-r2 S1). With it, its cube enters as a fourth generator of the cover, and each component G of the cover carries the factor exp(−½c₄ϑ²A₁²(log g₁⁻²)^{2p₀}(d₁′(G)+1) − 2(log g₁⁻²)^{p₀}) (§3f(2) Minor 4).
  - The step to exp(−½γ₀ϑ²A₁²p₀²(d′+1) − 2p₀) needs ½γ₀ϑ²A₁²p₀²(g) ≥ 2p₀(g), which holds for small g because p₀(g) → ∞.
  - Geometry: every cube of the enlarged 𝒬⁺(e) of (4⁗)(c) meets the ball of radius ℓ + ρ_L + 1 < 2ℓ around x_e. With the Fill, every removed point is within 103ℓ of a bad x_e (Lemma c5-3-1(c) with 𝒬⁺), so ∼2 is not enough: (1.76) is modified to Z₁ ⊂ ⋃_G G^{∼107} (§3f(2) Minor 4).
  - V3's Fill is an iterated side-100ℓ variant of CRE's (p.251; p.269 at the general step). By V3 Lemma c5-3-1(d), with the constants of (4⁗)(c), a retreat removes at most N⁺_ret = 4(209ℓ)⁴ bonds. With the modified (1.76), p.385's constant (14)^{−d} becomes (434)^{−d} (§3f(2) Minor 4).
  - Label entropy (repaired, §3f(2) R2): a label is determined by its bad set U ⊂ S, so the labelled terms with Λ^fin = Λ number at most 2^{|S|} ≤ Π_Z exp(O(1)M^dR₁^{d+1}d₁′(Z)), a term of the first exponential of (1.79). The bad-cube factor is spent once, in p.381.
- *The conditions on A₁ in the pages read.*
  - Upper bounds relative to A₀: p.381 l.24, and CRE pp.247, 248, 266 ((4′)). They hold with ϑA₁. CRE (3.19), p.268, is a lower bound on A₁/A₀ and also holds with ϑA₁ for small g. All of these concern CRE's own thresholds, which keep A₁ under (P).
  - The j = 1 condition ¼γ₀(14)^{−d}A₁²p₀²(g₁) ≥ O(1)2(64)^dM^dL^{d+1}R₁^{d+2} (p.385) is "satisfied for p₀ large, and g₁ sufficiently small". It holds in the form ¼c₄(434)^{−d}ϑ²A₁²(log g₁⁻²)^{2p₀} ≥ O(1)2(64)^dM^dL^{d+1}R₁^{d+2} (§3f(2) Minor 4: c₄ of R-d″(ii) takes γ₀'s place; γ₀ was written here before 22 Oct, 15:25), since 2p₀ ≥ 10𝔯 > 6𝔯 (CRE p.246 l.15; LFR II p.387 forces p₀ > 6𝔯 as well, §3f(0)).
  - p.382 l.28 (A₁²48⁻²R_j^{−8}p₁² ≥ R_j^{−8}p₁²) and p.383 l.25–29 concern LFR II's own threshold δ_j′ = g_jA₁p₁(g_j), which (P) does not change.
- *R-c checked against CRE p.269.*
  - At the general step, Λ_{k+1} is built from Ω_{k+1} and R_{k+1} by (3.20) and then filled. CRE uses that "On the domain Λ_{k+1}, in fact on Λ_{k+1}^∼ also, there are only the small field characteristic functions … their product is χ^{(k)}(Λ_{k+1})".
  - For Λ = Λ₁^fin: every field on Λ^∼ is below r. On Λ₁^∼ this is CRE's; on Λ₁∖Λ it holds by the box factors ((4″)).
  - With V3's retreat 𝒬(e), a bad bond can lie within ρ_L + 2 ≪ ℓ of Λ, so inside Λ^∼ (review it1-c-d10 G6(α)). The enlarged retreat 𝒬⁺(e) of (4⁗)(c) puts every bad bond outside Λ^∼. Then Λ^∼∖Λ carries only small-field functions: CRE's, the box factors, and the good collar tests at ϑr. These are functions of T-variables only. They do not enter the conditional integral, whose cutoff is the box on D(Λ).
  - By idempotence of single-bond indicators, box(D(Λ))·box(I∖D(Λ))·(J-tests) = box(D(Λ))·χ^{(0)}(R₁ᶜ∩Λᶜ), the step-1 form of (3.21)'s first factor (§3f(2) Minor 5). Only the good collar tests, at the threshold ϑr, are of a new kind on Λ^∼.
- *Reading R-d (superseded by R-d″, §3f(2) R1).* The earlier form, "LFR II's estimates use a large-field characteristic function only through the factor that the positivity bound gives it (pp.380–383)", was broader than what was read. R-d″ reads p.380 for the bad cubes jointly at threshold ϑδ₀, on cubes whose □′^{∼2} lies in the T-region (joint form after round 4; not printed).
- *LFR II pp.386–389 (read 22:58–22:59; the induction j → j+1 for κ_j and the polymer bound).*
  - A₁ enters only through the new-region terms γ₀A₁²p₀²(g_{j+1})(d′+1) of (1.85). For a single new region the condition is the j = 1 one.
  - The induction (1.86)–(1.88) needs 2(1+β₀)^{−1}p₀ ≥ O(1)3(100M)^dR_{j+1}^{d+2} "for p₀ large and γ small enough".
  - (1.92)–(1.97) need only conditions on p₀(g_k), κ, R_k and α (p.389 l.17–19, l.40).
  - So the collar tests can recur at every step of D2 without a new condition on A₁, as far as this mechanism goes.
- *[6] is not needed.* LFR II p.387 l.37–39: (1.80) and the improved (1.89) "implies the inequality (2.50) [III], hence Corollary 3". LFR II asserts this implication; it is accepted as Bałaban's result.
- *Status.* D1.0(P)(ii) is OPEN at step 1. Everything except the bad-cube factor is derived: the enlarged retreat of (4⁗)(c), the label entropy, the generator W₁, the modified (1.76) and the j = 1 condition (§3f(2), checked in round 4, it1-c4t-ii-20261022-r2). The factor is R-d″: (i) is derived; (ii) is OPEN pending D2.7 and the acceptance item (§3f(2) R1; rd5-d2-r3 m8). R-c is checked against p.269 and, in sublevel form, against every transcribed use (§3f(3) S1).

**(4⁗) Repairs after review it1-c-d10 (23:25–23:31).**
- *(a) Size of the cross-component blocks (S1).*
  - p.253's bound is for 𝐁^{(1)}: the clusters within MR₁ of Λ₁ᶜ and the expanded V^{(0)}(S₁). It is printed "O(1)|Λ₁∩Λ₁ᶜ|" (so printed). It is not stated for the quadratic cross-component blocks of (2.21), and nothing below uses a per-bond reading of it (reading R-e dropped, §3f(3) M7).
  - *Components.* In (2.21), take the components of Ω₁∩Λᶜ for the adjacency "bonds at distance < ℓ/2". CRE leaves the adjacency unspecified; the component split is read on p.258 directly. A coarser adjacency only merges components, so (2.19) still holds over them, and more of the form stays in T. At the level of the ℓ-cube cover this is ∗-adjacency (adjacency per use: §3f(3) M9).
  - H_JJ then has no cross-component block, since its range is 4L < ℓ/2.
  - The Schur term couples bonds x ∈ 𝒦 and y ∈ 𝒦′ of distinct components only through H_JD C^{(0)}(Λ) H_DJ, with x, y within 4L of D(Λ). By the choice of adjacency, d(x,y) ≥ ℓ/2. By the decay of C^{(0)}(Λ) ((4″), V3 Lemma c5-1-1) the entry is at most Ce^{−μ_H(d(x,y)−8L)}. C contains (164L⁴m_L)², since the entries of H_{JD} have norm ≤ m_L and each row has at most 164L⁴ of them ((I1)–(I2); §3f(3) M8).
  - The fields on these bonds are below r ((4″)). So the cross-component part at a boundary bond x is at most Cr² Σ_{y: d(x,y) ≥ ℓ/2} e^{−μ_H(d(x,y)−8L)} ≤ Cr²e^{−μ_Hℓ/4}.
  - Here μ_Hℓ = γ_LMR₁/(8m_L) and r² = A₁²(log g₀⁻²)^{2p₀}. Since R₁ grows like (log g₀⁻²)^𝔯, the bound is at most 1 for small g₀. So the cross-component blocks cost O(1) per boundary bond. Their localisation, a sum of terms each localised in a ball with exponential decay in its diameter, is the Neumann series of §3f(3) M8.
  - *Their 𝐁-format (c4q-r2b m6).* The format of 𝐁-terms is (2.41)–(2.42) (p.261): dependence on U, A restricted to X, an analytic extension to Ũ^c_j(X), gauge invariance, and |𝐁^{(j)}(X)| < B₀e^{−κd_j(X)}. p.258 moves the cross-component blocks into 𝐁 in CRE's own construction, and at Λ that construction is CRE's at an admissible domain (R-c). So CRE supplies the format; the computation above gives the size and the locality only.
  - *The total 𝐁 cost at Λ (round 4, c4q-r2c S-3 and r2b m2; derived 22 Oct from CRE p.264).* Under (P), 𝐁^{(1)} is formed at Λ: its clusters are those within MR₁ of Λᶜ, and its expanded V^{(0)}(S₁) is CRE's at Λ₁ (§3c(4)). CRE bounds all boundary terms of the k-th density by (2.48), derived from (2.42): "Bounds for the boundary terms (2.40) are even more elementary" (p.263).
    - At k = 1, (2.47) with j = n = 1 and (2.48) give |𝐁₁| ≤ 2B₁|Γ₁∖Λ₁⁰|. Here Γ₁ = Ω₁^{(1)} (p.255: Γ_k = Ω_k^{(k)}), Λ₁⁰ is Λ₁^{(1)} with one layer of MR₁-cubes removed (p.259), and volumes are numbers of points of T^{(1)} (p.263).
    - At Λ (R-c) the same bound reads |𝐁₁| ≤ 2B₁|Ω₁^{(1)}∖Λ⁰|. The MR₁-cubes of T^{(1)} are the ℓ-cubes, since ℓ = LMR₁.
    - Every ℓ-cube of Λ∖Λ⁰ is ∗-adjacent to an ℓ-cube meeting Λᶜ. That cube lies in Ω₁, since Λ ⊂ Λ₁ ⊂ Ω₁^{∼−2}. So |Ω₁^{(1)}∖Λ⁰| ≤ 3^d|Z₁∩Ω₁| with Z₁ = Λᶜ.
    - This is a volume cost of the kind LFR II p.380 l.27–29 places in the first exponential of (1.79): "every large field domain Z_j contributes the constant O(1) log g_j⁻²|Z_j| ≤ O(1) log g_j⁻²(MR_j)^d d_j′(Z_j) ≤ O(1)M^dR_j^{d+1}d_j′(Z_j)". Here it holds with Z₁ = Λᶜ, and it is paid by (1.82) with the modified (1.76) (§3f(2) Minor 4).
    - Relative to CRE's Λ₁, the volume added by the retreats and the round-0 fill lies within 103ℓ+1 of a bad bond or within 100ℓ of CRE's unfilled bad region ((c)(β)). That is at most C·N⁺_ret points of T^{(1)} per bad bond, which is the input of the count check in (4′). No per-bond reading of p.253 is used.
    - The change from C^{(0)}(Λ₁) to C^{(0)}(Λ) changes the 𝐁 values but not (2.48), which CRE states for every term of the expansion.
- *(b) The bad collar tests (S3): route.* They are refinements of the small-field set, not CRE large-fluctuation functions; in LFR's accounting only, their cubes are a fourth generator of the cover (§3f(2) Minor 4). On a bad bond, ϑr ≤ |A_e(e)|_σ < r, by Lemma collar-coverage(iii) for e ∈ J, or by the retained box factor for e ∈ I∖D(Λ). The distance is taken at the round k in which e was tested, e ∈ J_col(Λ₁^{(k)}): d(e,I) ≤ d(e,D^{(k)}) ≤ ρ_L ≤ 3R_c (proof of Lemma c5-3-1(a), "A bad e ∈ J_col(Λ₁^{(k)}) has dist(e,D^{(k)}) ≤ ρ_L"), and in the box case e ∈ I∖D^{(k)} ⊂ I∖D(Λ). The distance to the final D(Λ) exceeds ρ_L by (c)(α) (c4q-r2b m1, r2c m-1).
  - No (1.21)–(1.22) localisation is needed around them. V3 keeps U₁(Ω₁∩Λ₁ᶜ,V), S₁ and Ψ_ξ of the original Λ₁ (L2423), so the background and the change of variables are CRE's at Λ₁. The tests read T-variables only.
  - Their suppression is the factor exp(−½c_bϑ²A₁²p₀²(g₁)|𝒲|) of R-d″ (§3f(2) R1 (D2)). It is an integrand factor, derived pointwise in (D1) from H ≥ 0 (CRE p.248) and V3's local gap near I. Since round 6 the labelled integral is bounded factor by factor ((D2), with the R₁ cubes in (D1⁺); R-s and the Hölder route withdrawn; not reviewed). It needs no lower bound of S on 𝔤^J.
- *(c) Enlarged retreat and the properties (α)–(δ) of R-c (S3, G6).*
  - *Definition.* 𝒬⁺(e) := the union of the ℓ-cubes meeting the closed ℓ^∞-ball of radius ℓ + ρ_L + 1 around x_e, and Λ^{(k+1)} := Fill(Λ^{(k)} ∖ ⋃_{e∈B^{(k)}} 𝒬⁺(e)). It has at most 4⁴ = 256 cubes, and every point of 𝒬⁺(e) is within 2ℓ + ρ_L + 1 ≤ 3ℓ of x_e. This is a change to V3's retreat, agreed by the user for the V3 overhaul (22 Oct, 05:02) and not made in V3.
  - *V3 Lemma c5-3-1 with 𝒬⁺.*
    - (a) is unchanged: the removed cube lies in 𝒬⁺(e), since ρ_L + 1 ≤ ℓ + ρ_L + 1.
    - (b) is unchanged, since the ball is larger.
    - (c) holds with 103ℓ in place of 102ℓ.
    - (d) holds with N⁺_ret := 4(209ℓ)⁴, since 4(206ℓ+3)⁴ ≤ 4(209ℓ)⁴ and 4(206ℓ+4)(206ℓ+3)³ ≤ 4(209ℓ)⁴ for ℓ ≥ 2.
    - Lemma c5-3-3 is unchanged.
    - V3 uses N_ret and 102ℓ at L2426–2474, 2845–2849, 3029–3043, 3090, 3155–3227 and 4365. All were reread at 01:33 and transfer with (103ℓ, N⁺_ret); the count "2⁴ = 16 cubes" (L2423) becomes 256 and is not used elsewhere (§3f(3) S2).
  - *(α).* Every bad bond e lies outside Λ^{fin,∼}.
    - Λ^fin ⊂ Λ^{(j)} ∖ 𝒬⁺(e) for the round j in which e was found bad.
    - A cube ∗-adjacent to a cube that contains an endpoint of e has a point within ℓ + 1 of x_e, so it meets the ball and is not in Λ^fin. Hence e ∉ Λ^{fin,∼}, where ∼ is one layer of ℓ-cubes (p.251, as in R₁′^∼).
    - *Localisation convention (c4q-r2a m-6).* A cube test of (1.18) is located by its index cube □′, as on p.251 ("On the set Λ₁^∼ we have only the small fluctuation field characteristic functions from (1.18)"), although it reads the bonds of (□′^{∼2})*. A single-bond test (box factor, collar test) is located by its bond. With this convention (α) holds for CRE's own Λ₁ as printed: a large-fluctuation cube of R₁ can read bonds inside Λ₁^∼, but its index cube lies in R₁ ⊂ R₁′, outside Λ₁^∼.
    - On Λ^{fin,∼} ⊂ Λ₁^∼ the characteristic functions are then CRE's (1.18) small-field functions, the box factors on I∖D(Λ), and the good collar tests at ϑr. All are sublevel indicators {|A(b)| < t} with t ≤ r, which is (α) in the sublevel-set form of R-c; every use of (α) is checked in §3f(3) S1. The far-row indicators ι_c are not factors of T₁: they are one on the support (§3c(2)(e), c2-r2 S-A), which settles c4q-r2b m3 and r2a m-2. The z^{(0)} rows off Λ are positive factors, not indicators ((2)(a)).
  - *(β).* The new boundary of Λ^fin lies within 103ℓ+1 of a bad bond ((c) above; +1 for boundary bonds, c4q-r2b m8) or within 100ℓ of CRE's unfilled bad region (Lemma c5-3-0(b)). Both cases are in the modified (1.76), Z₁ ⊂ ⋃_G G^{∼107}, and their 𝐁-terms are volume costs inside the first exponential of (1.79), paid by (1.82) (§3f(2) Minor 4, which also covers V3's iterated Fill).
  - *(γ).* The bad tests are not CRE large-fluctuation functions ((b)): they need no (1.21)–(1.22) layer, and CRE's R₁, S₁ and their layers are unchanged. In LFR II's accounting their cubes are the fourth generator W₁ of the cover (§3f(2) Minor 4); that is bookkeeping of the bound, not a change of R₁.
  - *(δ).* Λ^fin ⊂ Λ₁. So □′ ⊂ S₁ is at least as far from ∂Λ^fin as the relevant distance for Λ₁, and V3 keeps U₁(Ω₁∩Λ₁ᶜ,V). The 𝐇_{1,Ax} bound is CRE's.
- *(d) The label sum factorises (M11; derived 23:45–23:48).*
  - *Λ₁ stays an outer label (round 4, c4q-r2c S-1; replaces §3f(3) M10).* CRE's outer labels are (Ω₁, Λ₁), and its S₁-sum is inside T₁: ρ₁ = Σ_{Ω₁,Λ₁} χ₁(Ω₁)T₁({Ω₁,Λ₁}) exp A₁ with T₁({Ω₁,Λ₁}) = Σ_{S₁}∫… ((1.28)–(1.29), pp.253–254). The kernel of T₁ depends on Λ₁ through χ(Ω₁∩Λ₁ᶜ,S₁), U₁(Ω₁∩Λ₁ᶜ,V), Ψ_ξ and 𝐇_{1,Ax}. 𝐇_{1,Ax} has only "the exponential decay property" (p.251), so moving Λ₁ inside T₁ would break the factorisation (2.19). Λ₁ therefore stays outer, and Λ₁^{(0)} = Fill(Λ₁) and 𝔅₀ = (Λ₁^{(0)})ᶜ are functions of the outer label Λ₁.
  - *Index by Λ.* Given the field and (Ω₁, Λ₁), exactly one label has 1_lab = 1, namely the actual run of the retreat. So χ_Λ := Σ_{lab: Λ^fin(lab) = Λ} 1_lab = 1{Λ^fin = Λ}. At fixed Λ₁ the new outer label Λ ranges over Λ ⊂ Λ₁^{(0)} (χ_Λ = 0 otherwise; §3f(3) M3); this is a range of the outer sum, since both Λ₁ and Λ are outer. F^Λ(1) and A₁^Λ depend on the label only through Λ (and on Ω₁, and on S₁ inside T₁ as in CRE). So the refined output is Σ_{Ω₁,Λ₁,Λ} χ₁ T₁^{Λ₁,Λ}[F^Λ(1)·exp A₁^Λ]. T₁^{Λ₁,Λ} is CRE's T₁({Ω₁,Λ₁}) with the conditional integration at Λ ((4″)), the de-younged variables and their box factors, the collar tests and χ_Λ.
  - *The extra label.* Λ plays the role of CRE's Λ₁ for the next step (Z₁ = Λᶜ). The original Λ₁ is a parameter of T₁^{Λ₁,Λ}, as Ω₁ and Λ₁ are of CRE's T₁ and E₁ (p.254). So the step-1 sequence of domains is (Ω₁, Λ₁, Λ), one more than CRE's (2.1). Whether the later steps accept the extra label is part of the D2 item on domains made by a retreat ((4′), p.256). The sum over Λ₁ is CRE's own, and the sum over Λ at fixed Λ₁ is the label entropy of §3f(2) R2.
  - *Regions.* (2.19) is the factorisation over a decomposition of Z₁ = Λᶜ into disjoint unions of components ("e.g. as a union of connected components", p.258). Take for the regions X the ∗-components of Λᶜ (ℓ-cubes sharing a point). Distinct regions are at ℓ^∞-distance ≥ ℓ. Each ∗-component of Ω₁∩Λᶜ (the components of (a)) lies in one X, and so does each component of Ω₁ᶜ and of 𝔅₀ = (Λ₁^{(0)})ᶜ.
  - *Claim.* On the range Λ ⊂ Λ₁^{(0)}, χ_Λ = Π_X χ_{Λ,X}. Here χ_{Λ,X} is the indicator that the retreat run started from the full 𝔅₀, with every test at a bond without both endpoints in X declared good, ends with complement X ∪ (𝔅₀∖X) (one definition, §3f(3) M4). So χ_{Λ,X} depends only on X, on 𝔅₀ (a function of the outer label Λ₁) and on the test variables in X.
  - *Locality in 𝔅₀ (c4q-r2b m4, r2c S-2).* At fixed outer Λ₁ the dependence on all of 𝔅₀ is a dependence on an outer parameter, which (2.19) allows. In fact χ_{Λ,X} depends on 𝔅₀ only through 𝔅₀ ∩ X; §3g(2) uses this.
    - On the range, 𝔅₀∖X lies in the other regions, at distance ≥ ℓ+1 > 2ρ_L + 2 from X.
    - While the local complement stays inside X ∪ (𝔅₀∖X), its X-part and the rest are not ∗-adjacent. So the collar near X, the removals 𝒬⁺(e) for bonds in X and the Fill hulls of the components in X are computed from the X-part alone.
    - The first change that adds a cube outside X ∪ (𝔅₀∖X) is made from X-part data: a hull, or a box 𝒬⁺(e), that meets X and contains a cube outside X. A ∗-path inside it from X to that cube leaves X through a cube ∗-adjacent to X and not in X, which lies in Λ. So the final complement contains a cube of Λ, and χ_{Λ,X} = 0, whatever 𝔅₀∖X is.
  - *Proof.* Let C^{(k)} be the complement at round k, increasing in k. Say that C^{(k)} *splits* if C^{(k)} ⊂ ∪_X X and its part in each X is the part in X of the complement at round k of the local run for X (frozen once that run stops).
    - Collar bonds are exterior, so both endpoints lie in C^{(k)}, in one X. A collar bond has dist ≤ ρ_L to D^{(k)}. Parts of C^{(k)} in different X are ≥ ℓ > 2ρ_L + 2 apart. So the collar near X, and its tests, are those of the local run.
    - A bad bond e is assigned to the X containing x_e. 𝒬⁺(e) is face-connected and contains the cube of x_e. Fill_1 acts on each face-component of the complement, each inside one X, and a hull is face-connected and contains its component. So every change made near X is a face-connected set meeting X.
    - (⇒) If Λ^fin = Λ, every C^{(k)} ⊂ Λᶜ = ∪_X X. A face-connected set inside ∪_X X lies in one X. By induction over the rounds and the Fill passes, C^{(k)} splits, and the local run for X ends with complement X ∪ (𝔅₀∖X). The local run agrees with the global run near X, and it leaves 𝔅₀∖X unchanged, since 𝔅₀ is filled (Lemma c5-3-0(a)) and its tests outside X are declared good. The two agree near X by the ℓ-separation of the regions.
    - (⇐) If every local run ends with complement X ∪ (𝔅₀∖X), the same induction shows that C^{(k)} splits at every round; its base case 𝔅₀ ⊂ ∪_X X is the range Λ ⊂ Λ₁^{(0)} (§3f(3) M3; c4q-r2b m8). Each change near X lies in the final local complement, and so in X. The global run stops at the last local stop, so Λ^fin = Λ.
  - *The whole cutoff (c4q-r2b m5).*
    - The box factors at I∖D(Λ) and the J-tests of (2)(c) are single-bond tests, each in one X.
    - CRE's χ(Ω₁∩Λ₁ᶜ,S₁) (including χ′₀(S₁) and χ^{(0)c}(R₁), which are not single-bond tests) and ζ(Ω₁ᶜ) factorise over the components of Λ₁ᶜ by CRE's (2.19) for CRE's T₁ at the outer Λ₁ (accepted). Each component of Λ₁ᶜ lies in one X ((2)(b), M9), so they group over the X.
    - The z^{(0)} rows off Λ are row-local, each in one X ((2)(a)). ι_ξ is one on the support ((2)(e)).
    - So the whole cutoff of T₁^{Λ₁,Λ} factorises over the regions X, as (2.19) requires. With the quadratic-form blocks of (a) above, this places T₁^{Λ₁,Λ} in the form (2.19)–(2.21) at j = 0, with Λ₁ as an extra outer parameter, and with one new integrand factor: the off-Λ rows of z^{(0)} ((2)(a)). That factor is analytic, positive, gauge-invariant and row-local in U₁, like the coefficients of (1.29). Whether the uses of (2.21) beyond (1.79) (the R-operation, step 2) accept it is a D2 item (c2-r2 M-B).
  - The argument uses only that 𝒬⁺(e) is face-connected and contains the cube of x_e, so it also holds for V3's 𝒬(e).

**(5) Status.**
- *Identification at step 1 ((1)–(2)).* No R at step 1 is a fact (CRE (1.6), p.244), and V^{(0)} is defined as the exact change, with CRE's stated properties ((1)). The equality n₁ = Σχ₁T₁[F_ξ(1)·exp A₁] holds as measures, with the placements (a)–(d) of (2), using reading R-f for (a).
- The label sum is V3 Lemma c5-6-1. Where the de-younged variables sit depends on the choice: under (P) they are T₁^lab-variables.
- D1.0(P)(i) is derived in (4″) and (4⁗)(a), using reading R-c (sublevel-set form, checked against the transcribed identities, §3f(3) S1 as corrected in round 4). R-e is dropped (§3f(3) M7); the 𝐁 cost at Λ is CRE's (2.48) at Λ ((4⁗)(a)).
- D1.0(P)(ii) is derived under reading R-c, with R-p (location checked; rates quoted from p.380 (step k ≥ N + 1)) and V3's logged (B1)(iii), (H4) (R-q₀ quoted and checked, recorded, not used; dbq-r2 m-b), except one item: (4‴) and (4⁗)(b) derive everything except the bad-cube factor R-d″ (§3f(2) R1). Round 4 found its earlier form not printed. It is now derived pointwise ((D1), reviewed correct in round 5; R₁ cubes in (D1⁺)), and its per-component part is the j = 1 factor of (1.79) at step k ≥ N + 1, bounded factor by factor ((D2), restated after rd5-d2-r2 S1). OPEN: that factor depends on D2.7 (LFR I's construction of Z and of Ω_hᶜ, Ω″_{h+1}, Z″_{h+2} from Z_h after p.187, with Z₁ = Λᶜ) and on the acceptance item (rd5-d2-r4 m-1(b)). R-s and the Hölder route are withdrawn. The check of LFR II's construction of T′ before p.379 against R-c ((D2) *Check* (l)) was reviewed in it1-rd5-d2-20261022-r2 and corrected (m1). The bad cubes are a fourth generator, with the modified (1.76) (§3f(2) Minor 4). Both use the enlarged retreat 𝒬⁺ of (4⁗)(c), whose effect on V3 is reread (§3f(3) S2).
- The label sum factorises over the ∗-components of Λᶜ at fixed outer (Ω₁, Λ₁) ((4⁗)(d), derived). Λ₁ stays an outer label (c4q-r2c S-1), so the step-1 output has the domains (Ω₁, Λ₁, Λ); M10's inner R₁-sum is withdrawn. So D1.0 holds at step 1 with (P) except R-d″(ii), the per-component factor of P₁, Q₁, R₁ and the bad cubes, which is OPEN pending D2.7 and the acceptance item (rd5-d2-r3 S1, m8).
- Left for D2: the p.256 "other conditions" for the later steps, the extra outer label Λ₁, and the enlarged (1.84) if retreats recur.
- LFR II pp.386–389 (the induction for κ_j), read at 22:59, put no further condition on A₁. Collar tests at every step of D2 fit this mechanism.
- The uncovered labels are D1.1, not D1.0.
- Reviewed up to (4″) in it1-c-d10-20261021-r1 (report 23:02, no fatal finding); (2), (4‴) and (4⁗) in round 3 (it1-c2-place, it1-c4t-ii, it1-c4q-rep, 22 Oct, no fatal finding). All repaired in §3c and §3f; the repairs are not reviewed.

## 3d. D1.1: uncovered labelled terms, the closed-contour route (worked 23:50–00:15; reviewed in it1-d11, round 3; repaired 01:48–02:05, 22 Oct; repairs reviewed in it1-d11-r2, round 4; S-1 and m-a to m-j repaired 22 Oct, not reviewed; summaries in §3f(4), §3h)

**The route.** A labelled term is uncovered when a contour bond lies in Ω₁ᶜ, or a free input of a contour link lies in J(Λ) = J ∪ (I∖D(Λ)) (L2835). The contour is kept closed and is not split into arcs. The exposed links are constants of the young integral, and they sit inside the words. This replaces the arc plan (1)–(8) of the gaps block; see (6).

**(1) Claim (derived).** On every labelled term, covered or not, for exterior data in the support of the term's collar indicators and exterior cutoffs. Hypotheses (m9): those of Lemmas c5-4-0 and c5-4-2 (L2541), the thresholds of Lemma c5-4-4 (L2573), threshold item 3 of Appendix thresholds (4C_𝖢g₀(1+2r) ≤ ϑ_*/2, used in Lemma c5-5-7z), (c5-5-T), (c5-5R-T) and (c5-7-T), and the period condition of §c5-3-1; for D1(ii) in (4), also those of Prop. c5-5-9 and the hypotheses of §3a and §c4-12. The domain includes the box factor |a_{old,b}|_σ < r on I∖D(Λ) (L2982) (d11-r2 m-c). Then:

F^Λ(1) = κ_C e^{E^∂_{D(Λ)} + E°_{T,n}}·[ f_ξ(m) + Σ_{𝔅≠∅ compatible} q°_Λ(𝔅)·dim(π)⁻¹ tr(Υ^1_{W₁}U^1₁ ⋯ Υ^1_{Wₙ}U^1_n) ],

the formula of §2. In it:
- a contour link in Ω₁ᶜ is V₀(r), a constant of the term (L2757: "links off Ω₁ equal to their background value");
- a contour link with a free input in J(Λ) is the reconstructed link at the young variable on 𝓕_r ∩ D(Λ) and at the actual exterior variable on 𝓕_r ∩ J(Λ). V3's Wilson factor is "the reconstructed fine field … at the actual retained data, including the change of variables; it is not interpolated" (L607). So the exterior inputs of links do not depend on t;
- these constants enter f_ξ(m), the words U_j and the words T_W inside Υ_W. At t = 0 the source still carries them: f_ξ(0) ≠ W_χ(C;U₁) in general, and c^0_W carries them too. "Exterior parameter zero" (L3080) refers to the kernel only (review it1-d11, S1). On the T₁ side they are the pending V₀ on Ω₁ᶜ and the pending A on Ω₁ ∩ Λ₁ᶜ (§1), and under (P) also the de-younged bonds of T₁^lab.

**(2) The inputs (derived).** For each one: where V3 uses coverage, and why the use is not needed.
- **(a) Groups, Lemma c5-5-3(a).** V3 assumes A^fin_cov for the whole subsection (L2594). There it serves to say that f_ξ depends on a only through a|_{I_C}. The lemma needs less:
  - every contour link depends on a only through a|_{𝓕_r ∩ D(Λ)}, and is constant in a otherwise. At carrier I this is L607: "each contour link U_ξ(a)(r) depends on a only through a|_{𝓕_r∩I}, through a row within 2R_c of I when 𝓕_r meets I, and is constant in a otherwise";
  - links off Ω₁ have 𝓕_r = ∅, by the convention of the contact set (L2667).
  - The unmarked-domain argument (L956) and the grouped source (L975, "On every branch") use only this. The t-family objects of §c5-4 come from statements without coverage (m5): Lemma c5-4-2 is stated "on every labelled term" (L2541); Cor. c5-4-3 holds "Under the hypotheses of Lemma c5-4-2" (L2561); Lemma c5-4-4 is stated "on every labelled term … and on the covered event A^fin_cov" (L2573; corrected after d11-r2 m-a, the earlier quote stopped before the coverage clause). Only its definitions and thresholds are used here; its proof uses coverage to note that D^Λ_ξ then sums over all of I_C: "the intersection in its definition records this" (L2582). If its bound is ever needed off coverage, its source-gradient input extends by the S-A argument of (d), with derivatives in the D(Λ) directions and inputs in 𝒰_c.
- **(b) Reference data and Schur, Lemma c5-5-3(b).** The reference data are defined on every term: the exterior variable is zero on J(Λ), and links off Ω₁ equal id (L2668). Constant conjugation fixes both, so the Schur identity holds. The proof of Lemma c5-5-3(b) (L2679) uses the constant gauge R_u acting bondwise, with "the reconstruction covariance q_id(R_uB) = R_uq_id(B)", field-independent hosts and partitions, and "Schur's lemma and the Fubini evaluation of the group product are verbatim". Each of these holds at the reference data on every term: a link with inputs in J(Λ) is evaluated at zero exterior variable, and a link off Ω₁ is id. (m5: the earlier citation of L1992 was tangential.)
- **(c) The exact identity (Lemma c5-5-3(c)) and the ordered product (Lemma c5-5-7(b)).** Both are algebra from (a) and (b). The factorisation over groups needs only that a traversal outside every ℋ(W) depends on no root variable. That is the definition of the contact sets.
- **(d) The link bounds, Lemma c5-5-7z.**
  - *The two uses of coverage (m1).* The preamble (L2738): "on A^fin_cov the row c of every traversal n of C has its free-input set 𝓕_{r_n} ⊆ D(Λ) ⊆ I", so "the exterior variable A^{Λ,Ψ} … does not enter a traversal link at all", and every input bond has |a_b|_σ ≤ 2r < 2+4r, so the input lies in the row polydisc 𝒰_c and ‖A‖ ≤ 2C_𝖢g₀(1+2r) ≤ ϑ_*/4. The proof of (a) then writes the row phase without exterior input: "(on A^fin_cov, where no exterior input enters the row, as in the preamble)". With an exterior input, the row phase is g₀𝖢_UΨ_ξ(a + A_e)|_{𝓔_c}.
  - *Why neither is needed (S-A, repaired).* The citation is Lemma charts, L475, not L607. Its statement holds "On every branch … for every row c ∈ Ω₁^{[1]} within 2R_c+2L of I", and it says: "Every a+tΨ_ξ(A_e) with a in the enlarged box and t∈[0,1] lies in 𝒰_c and 𝒰_y for every such row and centre (Lemma collar-coverage(i),(iii): Ψ_ξ(A_e)=A_e and |A_e(b)|<r on the bonds of 𝓔_c, 𝓔_y, which are within 2R_c+4L−1 ≤ 3R_c of I …)".
    - *The rows.* Take a traversal n whose link has 𝓕_{r_n} ∩ D(Λ) ≠ ∅. Then 𝓕_{r_n} meets I, so the link depends on a "through a row within 2R_c of I" (L607). That row is a row of Ω₁^{[1]} within 2R_c+2L of I, so it is one of L475's rows. L475 defines its rows by distance, so no bridge through a near primitive is needed (review item 6).
    - *The values.* On D(Λ): |a_b|_σ ≤ 2r (enlarged box). On I∖D(Λ): |a_old|_σ < r (the box factor of the a_old-integral, L2982). On J: |A_e(b)| < r and Ψ_ξ(A_e) = A_e, by the parenthesis of L475 (collar-coverage(i),(iii)), for exterior data in the support of the collar indicators. So a′ := (a, a_old) lies in the carrier-I enlarged box, and the row input at the term is the carrier-I input a′ + Ψ_ξ(A_e) of L475 at t = 1. L475's inclusion then covers every bond of 𝓔_c at once (the earlier split of the input bonds into D(Λ), I∖D(Λ) and J is dropped, d11-r2 m-f).
    - *Conclusion.* The input lies in 𝒰_c. Every input bond has |·|_σ ≤ 2r, so the preamble's bound ‖A‖ ≤ 2C_𝖢g₀(1+2r) ≤ ϑ_*/4 holds as written. The Cauchy estimates of the proof hold with the same constants, the derivatives being taken in the D(Λ) directions only; the inputs on I∖D(Λ) and J are constants of the term, independent of t ((1)). A row that misses D(Λ) gives a fixed unitary factor, which (b) of the lemma allows with ‖N‖ = 1.
  - *Consequences.* Lemma c5-5-7(d),(e), (c5-5-8) and Lemma c5-5R-3 hold on every term with V3's constants. The proof of c5-5R-3 (L2924–2957) was read: its parity step uses only that the term linear in B_{b_i} is odd and that the t = 0 measures are even. Constants inside the links do not affect either.
  - *The endpoint majorants (S-B, repaired).* L3080 is not used off coverage. Its last clause, "on A^fin_cov the source is the carrier-I source with zero on I∖D(Λ)", fails there, since a_old ≠ 0. In its place, Lemma c5-5R-3 (L2915) gives, for every group W, h ∈ G and t ∈ {0,1}, |c^t_W(h)| ≤ M^ph_Λ(W) and |a^Λ_W| ≤ M^ph_Λ(W). With |χ| ≤ 1 (normalised character) this gives 𝔡^0_W ≤ 2M^ph_Λ(W). Lemma c5-5-8 holds with (M^ph_Λ, ρ_ph, ε̄_ph) (L2916). Here ρ_ph ≤ ρ_t ≤ ρ_pin and M^ph_Λ ≤ M_Λ (L2870).
    - The proof of c5-5R-3 (L2924–2957) uses no coverage. Its inputs are Lemmas c5-5-2(a),(d), c5-5-3(a), Cor. c5-4-3, c5-5-6(b), c5-5R-1(b), c5-5R-2, and the g_t bound sup|g^{(p)}| ≤ 2^{−p}u_t^{|J′|+2p} from Lemma c5-5R-1(b) (corrected after d11-r2 m-d). Lemmas c5-5-2(a),(d), c5-5-6(b), c5-5R-2 and Cor. c5-4-3 are kernel statements at D(Λ) ((2)(i); c5-5R-2, L2899–2914, is the parity of the split measures on 𝔤^{E₀}). Lemma c5-5-3(a) is (2)(a). Lemma c5-5R-1 (L2879–2898) extends the link bounds of Lemma c5-5-7z(a),(b), and with the g_t bound it holds on every term by the S-A argument above. c5-5R-1 and c5-5R-2 inherit Lemma c5-5-2's hypotheses, which are kernel statements ((2)(i)) (corrected after d11-r2 m-j).
    - The path bound for good groups is in (4).
  - *The pins (Lemma c5-5-8).* They use (c5-5-T)(iv), a condition on g₀ alone, and "the field-independent domain/cluster/interval geometry" (L2788). There is no coverage input.
- **(e) Kotecký–Preiss, Lemma c5-5-3(d).** It uses the reference majorants, (b) and (d), only.
- **(f) S°_Λ = S°_{D(Λ),C,T} (Lemma c5-7-1).** The proof (L3126) uses coverage at two places.
  - *Qualification step.* "D(Λ) is covered on A^fin_cov …; what (I2) needs is Λ_r ⊆ D(Λ) (Remark c5-7-5(2))". Here (I2) is Prop. regional-square-extraction, whose hypothesis is "every free-input stencil of the contour lies in D" (L1945). This use is discharged by (g): the proposition holds at every carrier D ⊆ D₊ with the collar. The other parts of the qualification step (D(Λ) ⊆ I, stencils meeting D(Λ) in the regular region, de-younged bonds as exterior variables) do not use coverage.
  - *(F4).* Coverage is used to say that "the exterior variable (zero) does not enter". (F1)–(F3) concern D(Λ) and the reference data. At the reference data the exterior variable is zero on every term. A contour link r off Ω₁ is id on both sides:
    - on V3's side by L2668;
    - on the torus side by distance (m4, the repair of review S4; corrected after d11-r2 m-e). The torus-side free-input stencil of a traversal link r is the coverage stencil Λ_r (L3101). Λ_r = {r} for a free bond, and Λ_{b₀(c)} = 𝒮_c ∩ E_* lies in the two endpoint blocks of the row (Remark c5-7-5(2)), so Λ_r lies within 2L of r. (L2598's 2L+1 is a statement about V3's 𝓕_r, not about the torus link.) D(Λ) consists of bonds with an endpoint in Λ₁ ⊆ Ω₁^{∼−2}, so dist(D(Λ), Ω₁ᶜ) ≥ 2ℓ − 1 > 2L, and Λ_r misses D(Λ). So the torus phase of r at i_{D,T}B is q_id(0)(r) = 0, and the link is id.
    - A partly exposed link (inputs in J(Λ) and in D(Λ)) is evaluated at zero exterior variable on both sides, and (I3) fact 2 gives agreement.
    - A link r ∈ Ω₁ with all free inputs in J(Λ) (the sub-case not written before, d11-r2 m-e): Λ_r ⊆ 𝓕_r (Remark c5-7-5(2)) and 𝓕_r ∩ D(Λ) = ∅, so the torus link at i_{D,T}B is id. On V3's side the link is evaluated at zero exterior variable and zero young input, so it is id too.
  - So the lemma holds on every term.
- **(g) Prop. regional-square-extraction at an uncovered carrier.**
  - *Where the hypothesis enters (S-C(i)).* The hypothesis is "every free-input stencil of the contour lies in D" (L1945). The proposition says that "The estimates for the defined flat integral use its covered stencils, spectral bounds and small-coupling conditions; the collar enters at the identification" (L1977). The proof (L1980–2045) was read line by line for that use:
    - L1983 (identification): "The collar contains every stencil touching D". This is the collar, not contour coverage.
    - L1985–1990 (common chart domain): small-coupling conditions on the box ‖B‖_∞ ≤ r; no stencil condition.
    - L1992 (expansion): "supports intersected with D, keeping every original label". Valid for any D. A traversal link at i_{D,T}B is a function of B on its stencil ∩ D, so it is a restricted label of the same kind.
    - L1994–2017 (bounds): "Restriction preserves the support-size, overlap and range bounds" (L2000); the loads (L2009–2010) are per-bond and per-site suprema; the pinned-tree proof (L1420–1427) is tree combinatorics plus "Equation (marginal-KP-payment) implies inductively T_p^{(k)} ≤ |z̃_p|e^{a(p)}". None uses coverage.
    - L2019–2039 (covariance comparison and derivatives): generic in D; "Constant-conjugation invariance survives differentiation" (L2039).
    - L2041 (short clusters): "Short clusters have their original stencils inside D". For d_j > 2R_* + 2R_0 this follows from d_j alone: a short cluster's network has length ≤ d_j/2 + R_0 and is anchored within R_0 of K_j, while d_T(K_j, Dᶜ) = d_j + R_0. So it is local, not global coverage (review S5).
    - So the global hypothesis is used nowhere else in the text of L1980–2045. The words "its covered stencils" refer to the stencils of the short clusters at large d_j. The residuals of d11-r2 m-h, checked 22 Oct:
      - The protected-label expansion is applied "with supports intersected with D, keeping every original label" (L1992), "replacing every free-input support Λ by Λ ∩ D" (L1721). So its inputs lie in D by construction, and no stencil-inclusion assumption can enter through it.
      - §c4-10-1 to §c4-10-3 (L4880–4937), used for the path bound, contain no coverage condition (search for "cover", "A^fin", "inside D", "lies in D", "stencil"). Their stencil statements are the finitely many local stencil types (L4881) and the walk domains given by the construction of D_b (L4917). The one coverage clause nearby, "On covered far histories" (L4877), is in §c4-9-4, on history sums, and is not used here.
  - *The exposed segments.* At a segment whose stencils meet Dᶜ, d_j = 0, and "Bounded d_j are covered by the same rooted bound after enlarging C" (L2041) applies. The rooted bound is per segment (Σ_{Γ: j∈J_Γ}), so the enlargement factor is fixed per segment and uniform in N_exp.
  - *The rooted majorant (L2015)* holds at any carrier, by the list above. Constant-conjugation invariance survives restriction and differentiation (L1992, L2039), so a single marked component keeps its quadratic gain.
  - *Constant links.* A traversal whose stencil misses D has a constant link, id at i_{D,T}B. Every 𝒢_S with that traversal in S vanishes (L1673: a Boolean difference of equal terms), so it contributes no source variable.
  - *The corner extraction* compares F_{C,T} with F_{C,∞} and does not involve D.
  - So (regional-square-extraction)–(regional-square-error) hold at every D ⊆ D₊ with the collar, with d_j = 0 at the exposed segments. "No side-endpoint terms occur because both contours are the same closed square" (L2043) stays true.
- **(h) §3b at an uncovered D (S-C(ii) and m11, repaired).**
  - *The gap.* §3b(1) compared only the covariances. At an uncovered intermediate carrier D^{(m)}, the set E = Dᶜ ∩ (B_{m+1}∖B_m) could meet a marked traversal's stencil outside the old supp Γ. Then the link function itself changes between D^{(m)} and D^{(m+1)}, and §3b(1) did not control that. (The old §3b(1) also stated coverage as a hypothesis, m11.)
  - *The repair.* supp Γ now includes the free-input stencils of Γ's marked traversals (§3b(2)). Then E ∩ supp Γ = ∅ for every m ≥ 1, the link functions at D^{(m)} and D^{(m+1)} coincide, and §3b(1) applies as written ("Same index"). The diameter of supp Γ grows by at most 2R_K, which the position and diameter constants absorb (§3b(4), short-cluster threshold 4(R_* + R_K)).
  - (Q1) at the carriers D^{(m)}, which may be uncovered, holds by (g): the rooted majorant and the per-cluster bound hold there. So the anchored decomposition holds, with d_j = 0 at the exposed segments, where the anchored bound is Cτ².
- **(i) The remaining statements under V3's standing coverage hypothesis (S-D, checked by 01:57).** L2594 places §c5-5 on A^fin_cov. Each statement used here was checked for what the coverage does:
  - *Lemma c5-5-7z, preamble and (a):* (d) above (S-A).
  - *L3080, last clause:* not used ((d), S-B).
  - *Lemma c5-7-1, qualification step:* (f), discharged by (g).
  - *Cor. c5-7-2.* Its proof of (a) is "Lemma c5-7-1 and (I2) at D = D(Λ), whose hypotheses are (c5-7-T) and coverage" (L3147). With (f) and (g), (a) holds on every term, with the same formula: d_j(Λ) = max(0, d_T(K_j, D(Λ)ᶜ) − R_0) is already V3's definition (L3130), and d_j(Λ) = 0 at exposed segments. (b) concerns the covered leading term only. Its uncovered analogue is (1) with (4).
  - *Lemma c5-4-4:* the intersection I_C ∩ D(Λ) is in the definition of D^Λ_ξ (L2582). No change.
  - *Lemma c5-5-1:* the display Σ_{b∈I_C} h(m_b) ≤ C_mϑrN_lat(μ_H/2)Σ_{e∈J₁(Λ)} e^{−μ_H dist(e,I_C)/2} is (c5-5-2) "restricted to b ∈ I_C ⊆ D(Λ)" (display L2616, proof L2620). The shift m lives on D(Λ) (L2620). On every term the display holds with I_C ∩ D(Λ) on the left, and with dist(e, I_C ∩ D(Λ)) ≥ dist(e, I_C) the right side may keep I_C. This is the sum used in (c5-5-8) and §3a(7).
  - *Cor. c5-4-3 (L2561), Lemmas c5-5-2 (L2639), c5-5-5 (L2696) and c5-5-6 (L2711):* stated under the hypotheses of Lemma c5-4-2, or for bonds of D(Λ) and hosts of 𝐃₀(Λ). They concern kernel objects at D(Λ): selected integrals, the Gaussian disintegration along a coordinate, mark weights. No contour object enters, except through the constant C′_χ of Lemma c5-5-7z. A grep of L2541–2736 for coverage finds only L2582 (Lemma c5-4-4), L2594 (the standing hypothesis) and L2598 (the reference S°_Λ, which is (f)); the other hits are "covariance" and "cover sum".
  - *Lemmas c5-5R-1, c5-5R-2:* (d), endpoint majorants.

**(3) What the exposed segments cost.**
- *In the scalar:* Cτ² per coarse segment whose stencils meet D(Λ)ᶜ. This sits inside E^∂_{D(Λ)} as local terms e_X, with X within R_0 of K_j and containing a bond of D(Λ)ᶜ: activities attached to D(Λ)ᶜ, the form the class needs (§4).
- *No arc-end factors.* The contour stays closed. At the reference data a fully exposed link (off Ω₁, or with all its inputs in J(Λ)) is id. A partly exposed link is e^{iq_id(a|_{D(Λ)}, 0)}, a link of the reference integral like the covered ones, not id (m8).
- *In the words:* unitary constants, of norm 1.

**(4) D1(ii) on every labelled term (derived).** §3a goes through with two changes.
- **Good groups.** To "Q_W ⊂ Λ₁ and Q_W lifts injectively", add: every free input of every traversal of ℋ(W) lies in D(Λ). On covered terms this holds automatically.
  - For a good group the exterior variable enters no link of ℋ(W), and at exterior parameter zero it enters no kernel (L3080). So c^0_W carries no exterior constant and depends only on U₁ inside Q_W (L5024).
  - *Phase test passed: the path bound (S-B, checked).* §3a(3) uses L3080's |𝒟_ω c_W(U_{W,t};h)| ≤ C_χ‖ω‖_∞(n(W)+|ℋ(W)|)M^{(ρ)}_Λ(W). L3080 rests it on "the source remainder bounds of Section c4-10-4 hold on A^fin_cov, where every contour row has its free inputs in D(Λ) and the exterior variable does not enter a link". §c4-10-4 uses "Only the source f_W(a;h)=χ(T_W(a)P_W⁻¹h) … untouched factors are unitary in its representation" (L4943): only the rows of the group's own traversals, with the row constants (c4-10-4), which need only the protected-input condition g₀‖𝖢_Za‖ < θ₀/2 (L4897–4901). For a good group the added condition puts every input of those rows in D(Λ), so the remainders are those of the covered case. The kernel side along the path (Cor. c5-4-3, Lemma c5-5-2(b),(c) at U_{W,t}, (c4-7-9), Lemma c4-7-1(c)) concerns D(Λ) at exterior parameter zero ((2)(i)). So the path bound holds.
  - *Phase test failed:* 𝔡^0_W ≤ 2M^ph_Λ(W) by Lemma c5-5R-3 ((2)(d)), in place of L3080's endpoint majorant. The rest of §3a(3) is unchanged, with M^ph_Λ in place of M^{(ρ)}_Λ.
  - *Endpoint identities (c4-11-6) off coverage (round 4, it1-d11-20261022-r2 S-1; checked 22 Oct against V3 §c4-11-1 to §c4-11-4, L4978–5028).* The path bound needs both endpoints, c_W(U_{W,0};h) = a^Λ_Wχ(h) and c_W(U_{W,1};h) = c⁰_W(h). V3 restricts (c4-11-6) "to covered far histories and the small interior groups" (L5024). Its proof uses three things:
    - (a) covariance (c4-11-5), under the simultaneous transformation of the background and the free variables (§c4-11-2, L4996–5007);
    - (b) finite support: every background bond the coefficient consults has both endpoints in Q_W, by the enlargement of the rectangle to every Hessian stencil, row set, block-mean path, plaquette and interval or closing-path bond (L5024);
    - (c) the t = 0 recipe is the regional reference recipe with the same carrier, Ω₁, cutoffs and constants (L5015; at D(Λ), Lemma c5-5-3(b), L3082).
    - Coverage enters only in §c4-11-1 (L4989): it makes every contour link of the source the reconstruction from a alone at U₁. For c_W the source is f_W, whose links are those of ℋ(W) (L4943). For a good group their free inputs lie in D(Λ) by the added condition, so f_W consults no outer variable (V₀, A_e, a_old).
    - Every selected measure and vacuum occurrence in c_W is built from the kernel at exterior parameter zero: near primitives at a, Hessian H_{DD}, cutoff on D(Λ) (L4989 at D(Λ), L3080). None consults an outer variable.
    - Hence (a) applies with R_g acting on U₁ and a only, (b) is a property of Q_W, and (c) uses Lemma c5-5-3(b)'s reference data, which are the same on every term.
    - The far-history facts are replaced by Q_W ⊂ Λ₁. Q_W then misses S₁ (Λ₁ ∩ S₁ = ∅, CRE p.251) and lies in Ω₁^{∼−2}, the regular region; and δ_{Q_W}(U₁) ≤ Cε₁ is a statement about U₁ on Λ₁ (L3082).
    - So (c4-11-6) holds at D(Λ) for good groups on every labelled term, and the passed-test path bound above has both endpoints. The earlier interpretation of L5024 (m10) is no longer needed.
  - A link off Ω₁ cannot occur in ℋ(W), since Q_W contains the bonds of every n ∈ ℋ(W) (L5024) and Q_W ⊂ Λ₁ ⊂ Ω₁.
- **Other groups.** 𝔡^0_W ≤ 2M^ph_Λ(W) by Lemma c5-5R-3 ((2)(d), S-B). Put d^Λ(n) := dist_{d_T}(Γ_n, E(B_ξ) ∪ (I∖D(Λ))) (m2; the complement is taken inside the bonds, so the non-free bonds of Λ₁ are not in the target set and the decay is not vacuous).
  - d^Λ(n) ≤ d(n), since E(B_ξ) is part of the target set.
  - If Q_W ⊄ Λ₁ and Q_W lifts, §3a(4)(i) gives d^Λ(n) ≤ d(n) ≤ diam Q_W + 1.
  - If some n₀ ∈ ℋ(W) has a free input b ∉ D(Λ), and Q_W lifts (m7: the diameter bound is for liftable rectangles, §3a(4)(i)), then b ∈ Q_W (L5024, the row-set enlargement). Also b ∈ J(Λ) = J ∪ (I∖D(Λ)), and J ⊆ E(Λ₁ᶜ) = E(B_ξ) (L2835), so b is in the target set. So d^Λ(n) ≤ diam Q_W + 1 for every n ∈ ℋ(W).
  - Either way 𝔰(W) ≥ (d^Λ(n) − 1)/(C_box LM). The non-lifting case is unchanged.
- **Result.** The per-traversal bound of §3a(6) holds on every labelled term, with d^Λ(n) in place of d(n) and ρ̂ := max(ρ, ρ_ph) ≤ ρ_pin in place of ρ: the pins are Lemma c5-5-8(a) with M^{(ρ)}_Λ for the passed-test good groups, and with M^ph_Λ (Lemma c5-5R-3) for the rest. §3a(7) is unchanged: (c5-5-8) holds by (2)(d), and the shift m lives on D(Λ), so the h(m_b)-sum runs over free inputs in D(Λ) (Lemma c5-5-1 with I_C ∩ D(Λ), (2)(i)). On covered terms the sharper d(n) of §3a stays.
- **No new exterior term.** The exterior inputs of links do not depend on t ((1)). So Υ^1_W − Υ^0_W carries the marks of §3a(2) only, and the exposed links enter only through the groups that are not good.
- **What the attached term covers.** The target set of d^Λ is E(B_ξ) ∪ (I∖D(Λ)). (The earlier "rest of J" is empty, since J ⊆ E(B_ξ), L2835.) The de-younged bonds I∖D(Λ) are of two kinds (m3):
  - collar-retreat bonds, within 102ℓ of x_e for a bond e found bad (Lemma c5-3-1(c)), 103ℓ with 𝒬⁺ (§3c(4⁗)(c));
  - round-0 bonds, within 100ℓ of CRE's unfilled bad region (Lemma c5-3-0(b)).
  So Cρ̂e^{−c(d^Λ(n)−1)/(LM)} is attached to the large-field region, to the bad collar tests and to CRE's bad region. That is the case D2(d).

**(5) Count check.** Let N_exp be the number of coarse segments whose stencils meet D(Λ)ᶜ. Upper bound only (m6), in the normalised history average 𝔼 := 𝒵₀^{−1}∫𝒪[Σ_lab 𝗐^lab_ξ ·]dV (corrected after d11-r2 m-i):
  - A stencil bond z of segment j with z ∉ D(Λ) = D^fin has no endpoint in Λ₁^fin, so z ∈ E(B^fin_ξ) (L2451). It lies within c_st = 2L+2 of a contour bond b of the segment (§3b(2)). So N_exp ≤ Σ_{b∈Γ_C}Σ_{z: d(b,z)≤c_st}1{z ∈ E(B^fin_ξ)}.
  - By the mark inequality (c5-3-mark-inequality) and the averages p^{(0)}_z ≤ q and Σ_{e near z}p^ϑ_e ≤ N_ret q_ϑ (L2455), as in (c5-3-coverage-average) (L2457): 𝔼[N_exp] ≤ 4(2c_st+1)⁴C_Ln_C(q + N_ret q_ϑ), with V3's C_L, q, N_ret, q_ϑ.
  - No lower bound on p_z is used or claimed.
- E^∂_{D(Λ)}: at most Cτ²N_exp + Cτ²Σ_{other j} e^{−c''d_j}. It is carried as local terms, not bounded. Per exposed segment it is O(τ²), one term of (regional-square-error) at d_j = 0. Any later bound of e^{E^∂} costs e^{Cτ²Σ_j e^{−c''d_j}}, with e^{−c''d_j} = 1 at the N_exp exposed segments, which D2 must pay (review S7; d11-r2 m-b; gaps block, D2).
- ν_n: Cρ̂ for the traversals within O(LM) of E(B_ξ) ∪ (I∖D(Λ)), decaying away from them (d11-r2 m-g). These are carried and never exponentiated (§5 S4).
- No factor exponential in n_C enters (1): the identity is exact, and q° is bounded by Kotecký–Preiss.

**(6) What this replaces in the plan (1)–(8) of the gaps block.**
- (1) Splitting into arcs: not needed.
- (2) Schur with open arcs: (2)(b).
- (3) Arc-end factors: there are none ((3)).
- (4) Regional extraction for open arcs: (2)(g).
- (5) Partly exposed links: they are already V3's source links, with exterior constants ((1), (2)(a)).
- (6) The uses of coverage were checked at L2594, L1945/L1977, the whole proof L1980–2045 with the pinned-tree proof L1420–1427, L3080, L3101 with L3126 (qualification step and (F4)), L3130/L3147, L5024, L475, L2738, L2582, L2616–2620, L4943, and in the proofs of Lemmas c5-5-7z(a), c5-5-8 and c5-5R-3 and the statements of c5-5R-1, c5-5R-2 ((2)(i)).
- (7) Both failure modes are in (1).
- (8) The extraction of κ_C: (2)(f), (g).
- (m12) The plan (1)–(8) is the arc plan of the gaps block. It was not in packet it1-d11; the next packet must include it.

**(7) Status.** D1.1 is derived in the form (1) with D1(ii) as in (4). Reviewed in it1-d11 (no fatal finding); S-A to S-D and m1–m12 repaired at 01:48–02:05 (§3f(4)); the repairs are not reviewed. Not touched here:
- D1.2b (analyticity), on uncovered terms as on covered ones; now §3e, which covers both (§3e(4));
- the uses of the exposed constants by the later steps (D2).

## 3e. D1.2b: analyticity in the background (worked 00:30–00:57, 22 Oct; reviewed in round 4 (e-red, e-gauss, e-rest); repairs written 07:03–07:23, 22 Oct (session log), not reviewed; summary in §3h)

**(0) Target, in Bałaban's form (quoted and checked; round-4 repairs e-red S1, m2, m3, m5, m8).**
- Every localised term of 𝐁_k has "an extension to an analytic function on the space Ũ_j^c(X, α̃₀, α̃₁)" (CRE p.261, after (2.41)); the regular terms are analytic on U_j^c(X, α_{0,j}, α_{1,j}) (p.259). The pending variable A is not complexified ((2.41)–(2.42)).
- The complex direction is 𝐔 = U′U, with U G-valued and regular ((2.34), (2.38)), and U′ = exp iξA′, A′ 𝔤^c-valued: "L^nξ|A′|, (L^nξ)²|∇_U^ξA′| < (1−β(1−2^{−(j−n)}))α_{1,n}" ((2.39), p.261), with α_{1,j} = g_jC₁(log g_j^{−2})^{q₁} ((2.28), p.259).
- Units: ξ = L^{−j} is the spacing of the fine lattice T_ξ (p.256 l.59). At j = n = 1 the factor in (2.39) is 1. In V3's dimensionless fine-lattice units the complex phase per fine bond is a′ := ξA′, and (2.39) reads ‖a′‖_∞ < α_{1,1}/L, with fine differences < α_{1,1}/L².
- So a sufficient candidate target for D1(iii), in the form of the input that Bałaban's step-2 machinery takes. In some respects it asks more than CRE's set. Whether its base points (real U₁ in the support of a term's indicators) cover CRE's (2.34)/(2.38), and whether D2 needs more, are D2 items (e-red m2).
  - **D1(iii)′.** Fix a labelled term, a real U₁ in the support of its indicators, and a 𝔤^c-valued a′ on the fine bonds of Ω₁ with ‖a′‖_∞ < ρ₁, where ρ₁ := α_{1,1}/L.
    - *Where a′ acts (e-red m5).* 𝐔 := e^{ia′}U₁ on every fine bond of Ω₁, including the bonds of J(Λ) and the de-younged bonds. The variables on these bonds stay real: the young variable on D(Λ), the exterior variable on J(Λ) and the pending A on Ω₁ ∩ Λ₁ᶜ. V₀ on Ω₁ᶜ is unchanged.
    - Then the term's background-dependent factors (Υ¹_W, the words U_j, f_ξ(m)) extend to analytic functions of a′ at 𝐔, equal to the real ones at a′ = 0. At 𝐔 the shift is the real m₀ := m(U₁), and the background dependence of m is carried by the tilt of (3.12). So f_ξ(m) at 𝐔 means f_ξ(m₀) at the background 𝐔.
    - They are covariant under G-valued gauge transformations, with a′ transformed by the adjoint.
    - D1(ii) holds there in the per-traversal form of §3a(8), with three changes (e-red S1, e-rest M1):
      - δ*_n(U₁) is replaced by δ*^{30}_n(U₁) + a*_n(a′);
      - the rate 31η/8 of §3a(6) becomes 30η/8, in δ*_n, in the large-field and wrapping terms and in c := 30η/(8 max(C_box, C));
      - each group's majorant carries e^{C′𝔰(W)ρ₁}, absorbed by the freed η/8 of the pin weight once C′ρ₁ ≤ η/8 ((3.8)).
    - Here δ*^{30}_n is δ*_n of §3a(6) with (31/8)ηk replaced by (30/8)ηk, a*_n(a′) := Σ_{k≥1}(k+1)e^{−(30/8)ηk}A_n(C_box LM(k+1)) and A_n(R) := max{‖a′(b)‖ : b within distance R of n}. The exterior marks of §3a(7) keep their rate η/(C_F LM) and gain the tilt marks 𝔪^δ_Y of (3.12).
  - The indicators are functions of the real data and stay outside, as factors (§OPEN, D1.2b).
  - q°, E^∂_{D(Λ)}, φ and e_X are numbers on each labelled term (§3b(5), L986), so nothing is asked of them.
- The replacement of δ*_n by δ*^{30}_n + a*_n is admissible. At U₁ = id and a′ ≠ 0 the background is not flat, and a*_n is of order ‖a′‖_∞. For D2's Cauchy estimates this is the expected size: the bound on the ρ₁-polydisc, divided by ρ₁, bounds the first derivative in the fluctuation direction.

**(1) Complex symmetric matrices (derived).** Let H = R + iS be a complex symmetric n×n matrix, with R, S real symmetric (the entrywise real and imaginary parts), R ≥ γ′ > 0 as a quadratic form, and ‖H‖ ≤ m. Write ⟨·,·⟩ for the Hermitian product on ℂⁿ.
- (a) *Numerical range.* For x ∈ ℂⁿ, ⟨x,Rx⟩ and ⟨x,Sx⟩ are real, so Re⟨x,Hx⟩ = ⟨x,Rx⟩ ≥ γ′‖x‖². This passes to every principal restriction H_E = ι_E^*Hι_E, with the same γ′ and m: Re⟨x,H_Ex⟩ = Re⟨ι_Ex,Hι_Ex⟩. This replaces min–max and interlacing.
- (b) *Inverse.* γ′‖x‖² ≤ Re⟨x,Hx⟩ ≤ ‖x‖‖Hx‖, so H is invertible with ‖H^{−1}‖ ≤ 1/γ′, and γ′ ≤ m.
- (c) *Neumann series.* With m′ := m²/γ′,

  ‖(1−H/m′)x‖² = ‖x‖² − (2/m′)Re⟨x,Hx⟩ + ‖Hx‖²/m′² ≤ (1 − 2γ′²/m² + γ′²/m²)‖x‖²,

  so ‖1−H/m′‖ ≤ q := (1−γ′²/m²)^{1/2} < 1 and H^{−1} = m′^{−1}Σ_{k≥0}(1−H/m′)^k. If H has range R_H, the k-th term vanishes at (b,c) for k < d(b,c)/R_H, so ‖H^{−1}(b,c)‖ ≤ (γ′/m²)q^{d(b,c)/R_H}/(1−q). This is the real argument with constants depending on γ′ and m only.
- (d) *Determinant.* det H = det R·det(1+iK), with K := R^{−1/2}SR^{−1/2} real symmetric and ‖K‖ ≤ ‖S‖/γ′. With eigenvalues λ_k of K, |det(1+iK)| = Π_k(1+λ_k²)^{1/2}, so

  1 ≤ |det H|/det R ≤ exp(n‖S‖²/(2γ′²)).

- (e) *Gaussian integrals.* For real x, |e^{−⟨x,Hx⟩/2}| = e^{−⟨x,Rx⟩/2}. The set {R > 0} is convex and det H ≠ 0 on it by (b), so det(H)^{1/2} has a continuous branch there, positive at S = 0. Both sides of ∫_{ℝⁿ}e^{−⟨x,Hx⟩/2}dx = (2π)^{n/2}det(H)^{−1/2} are analytic in the entries and agree at S = 0, so they agree. For the normalised expectation E_H[F] := (2π)^{−n/2}det(H)^{1/2}∫F e^{−⟨x,Hx⟩/2}dx,

  |E_H[F]| ≤ (|det H|/det R)^{1/2}E_R[|F|] ≤ e^{n‖S‖²/(4γ′²)}E_R[|F|].

  The exponent of the cost is linear in the dimension n. So it is harmless only on local carriers, never on I (see (2)(e)).
- (f) *Perturbation from a real background.* Let H_𝐔 have entries analytic in the background on a polydisc, with finite range, and H_U real with γ ≤ H_U ≤ m at a real U. If ‖H_𝐔 − H_U‖ ≤ s, then ‖R − H_U‖ ≤ s and ‖S‖ ≤ s, since entrywise real and imaginary parts do not increase the operator norm (Re M = (M + M̄)/2 and ‖M̄‖ = ‖M‖). So (a)–(e) hold with γ′ = γ − s and m + s in place of m.
  - *Symmetry (e-red m7).* H_𝐔 is complex symmetric. In the chart of (2)(c), H_𝐔ᵀ − H_𝐔 is analytic in the complex chart phases on a connected polydisc. It vanishes at the real phases, where H is a real symmetric compression, and a power series that vanishes at the real points of a polydisc vanishes identically.
  - *Notation.* In §3e, R := Re H. V3's Hessian range (the R of Lemma hessian-gauge-locality) is written R_V.

**(2) Reduction.**
- (a) *Analyticity follows from the bounds.* On a fixed labelled term the factors are built from four things:
  - entries analytic in the background (§c4-10-1, L4880, on ‖Z‖ < 2τ_b, Z complex);
  - integrals over real fluctuation variables, with cutoff domains in the fluctuation variables only ("The protected cutoff domain is fixed throughout", L4937; to be checked for every cutoff in (3));
  - finite or convergent cluster sums;
  - logarithms defined as convergent cluster series or on matrix balls (L4907).
  An integral of an analytic integrand that is locally uniformly dominated is analytic (differentiation under the integral). A locally uniformly convergent series of analytic functions is analytic (Weierstrass). So analyticity on the ρ₁-polydisc follows from the majorants of (3), taken uniformly on it.
  - *Along the path (e-red m6).* The same argument gives analyticity on a complex neighbourhood of each path background of (2)(d). Those backgrounds lie within C‖a′‖ of V3's real path, and (3.1)–(3.6) hold at every background within Cρ₁ of a real one in V3's domain.
- (b) *Covariance.* For G-valued u, (e^{ia′}U₁)^u = e^{i Ad_{u}a′}U₁^u at the initial site of each bond. The formula of each factor is covariant identically in 𝐔, so the extension is covariant with a′ ↦ Ad_u a′, and ‖Ad_u a′‖ = ‖a′‖.
- (c) *Local charts (repaired, e-red m1).* At U₁, V3 evaluates the entries in the U₁ charts of Lemma c5-4-0(c) (L2491): Lemma c2-uniform-chart, phases ‖φ‖_∞ ≤ τ_L/2 in a site gauge. The bound ‖Z‖ < 2τ_b of §c4-10-1 (L4880) is established only along the path, by the phase test (L3080).
  - In the same gauge 𝐔 = e^{ia′_φ}e^{iφ}, with a′_φ the gauge transform of a′. So 𝐔 = e^{iφ^c} with φ^c := (1/i)log(e^{ia′_φ}e^{iφ}) and ‖φ^c − φ‖ ≤ C‖a′‖ (BCH).
  - So every entry at 𝐔 is evaluated in the complex neighbourhood {‖Re φ‖ ≤ τ_L/2 + ρ₀, ‖Im φ‖ ≤ ρ₀} of (3.6), once Cρ₁ ≤ ρ₀. Along the path ((2)(d)) the margin below 2τ_b is the phase test's.
  - By the Cauchy estimates on the polydisc and the finite range, ‖H_𝐔 − H_{U₁}‖ ≤ C_Hρ₁ (Schur test), and (1)(f) applies with s = C_Hρ₁.
- (d) *The path argument (derived, modulo (3)).* Let W be a good group passing V3's real phase test, and let g_W be the real rooted tree gauge of U₁ on Q_W (Lemma c4-10-5). Then on Q_W, 𝐔^{g_W} = e^{i Ad a′}e^{iB_W}.
  - Put B^c_W(b) := (1/i)log(e^{i Ad a′(b)}e^{iB_W(b)}) on Q_W and B^c_W = 0 on the other bonds. Then ‖B^c_W − B_W‖_∞ ≤ C‖a′‖_{Q_W}, so ‖ω^c_W‖_∞ ≤ C_tg diam(Q_W)²δ_{Q_W}(U₁) + C‖a′‖_{Q_W}.
  - The path is U^c_{W,t} := e^{itB^c_W}, 0 ≤ t ≤ 1. At t = 1 the coefficient is the extended one at 𝐔, by coefficient locality on Q_W and (2)(b). At t = 0 it is the flat reference, as in V3.
  - t ↦ c_W(U^c_{W,t}; h) is C¹ with derivative 𝒟_{ω^c}c_W, because c_W is analytic along the path, by (a).
  - The real gauge is used on purpose. A complex tree gauge would multiply complex links along tree paths of length up to diam(Q_W) ≤ C_box LM𝔰(W), with growth e^{C diam·ρ₁}. That is not bounded uniformly in 𝔰. The real gauge preserves ‖a′‖.
  - So the good-group bound of §3a(3) holds at 𝐔 once Lemma c4-9-1's derivative bound holds along complex paths with ‖Im‖ ≤ Cρ₁ ((3)), in the form |𝒟_ω c_W(U_t)| ≤ 2C e^{C′𝔰(W)ρ₁}‖ω‖(L_f + n(W))M(W) ((3.11)). The extra term C‖a′‖_{Q_W}(L_f+n)M ≤ C𝔰‖a′‖_{Q_W}M gives Cρ a*_n, by the summation of §3a(6) at the rate 30η/8 ((0), (3.8)).
- (e) *What is left.* By (a)–(d), D1(iii)′ follows from one statement:
  - (★) (restated, e-red S1, e-rest M1). Under repairs K and K′ ((3.0), (3.6)), V3's majorants for the coefficient and its directional derivatives hold at complex backgrounds e^{iZ^c}, with Re Z^c in V3's real domain and ‖Im Z^c‖ ≤ Cρ₁, with the real shift m₀ and the tilt of (3.12), and with three kinds of extra factor:
    - per group, e^{C′𝔰(W)ρ₁} from the words and closed contractions ((3.8)), and a factor 2 on the derivative bounds from the complex direction ((3.7));
    - per Gaussian component, e^{C₄s|J_Z|} with |J_Z| ≤ 4(LM+1)⁴N₁(Z), from the determinant ratio of (1)(d) and the complex T^c ((3.4));
    - per host, the tilt part of (3.12), which keeps the host bound ω̃_t ≤ ω_* and adds the marks 𝔪^δ_Y.
  - The majorants in question are M(W) and (c4-12-4), Lemma c4-9-1, their D(Λ) forms (L3080), and the exterior bound (c5-5-8).
  - The factors are not of the form 1 + O(ρ₁) uniformly in the group, since 𝔰(W) is unbounded. Since ρ₁ ≍ g₁(log g₁^{−2})^{q₁} → 0, they are absorbed by three g₀-thresholds: C′ρ₁ ≤ η/8 (the pin weight, at the lowered rate 30η/8); s ≤ (16C₄(LM+1)⁴)^{−1} (the Gaussian budget under K, (3.4)); and the tilt threshold of (3.12).

**(3) V3's inputs at complex backgrounds (checked 00:46–00:57).** Throughout, H is the I-compression (or the D(Λ)-compression, L3076) at 𝐔, H_U the same at the real U₁ (or along V3's real path), and s := ‖H − H_U‖ ≤ C_Hρ₁. Write R := Re H and S := Im H (entrywise). γ = γ_L/2, h_+ = m_L, as in (fixed-kernel-inputs) (L713).

- **(3.0) Margins: the constant chain is re-run (repair K; round-4 repairs e-gauss m1–m4, m10).** The payment has no margin as V3 states it: with V3's choices, C_d(α_G + δ_M²)|J_Z| ≤ C_d(α_G + δ_M²)·4(LM+1)⁴N₁(Z) ≤ N₁(Z) can hold with equality in the last step (L3831). Repair K: run V3's chain, in V3's order (γ, h_+, R_V; κ₁; n_*, R_*, C_w; M₁, ρ_w, M; α_G; then g₀; L715), with these changes:
  - γ_c := γ/2 in place of γ, and h_c := h_+ + γ/2 in place of h_+, throughout the chain. In particular q_H and s_H of Lemma walk-series are computed from (γ_c, h_c) (e-gauss m4).
  - a_*β ≤ 1/8 in place of 1/4 in (fixed-kernel-grouping) (L719).
  - C_w := (4/3)s_H^{−1/2}n_*V_*a_* and δ_M := 2C_w4^{−N_M} (e-gauss m1). The factor 4/3 bounds 1/(1 − a_*β^c) for a_*β^c ≤ 1/4. So the tail constants of (3.2) are bounded by the same C_w in the real and the complex case, and the margins below hold as stated.
  - In the choice of M: 4C_d^Kδ_M²(LM+1)⁴ ≤ 1/4 in place of 1/2, and h_c²δ_M²/γ_c ≤ 1/16 in place of 1/8. The second follows from the first, since C_d^K ≥ 2d_Gh_c²/γ_c gives h_c²δ_M²/γ_c ≤ 1/(32d_G) (e-gauss m10). It is kept for reference.
  - α_G ≤ min(γ_c/2, γ_c²/(16A_*²), (8C_d^K(LM+1)⁴)^{−1}).
  - Here A_* := h_c(γ_c^{−1/2}+1), and C_d^K := d_G max(1/γ_c + 2A_*²/γ_c², 2h_c²/γ_c). This is (fixed-kernel-trace-payment)'s constant (L3829) at (γ_c, h_c, A_*), with its 2/3 replaced by 1 and its δ-coefficient doubled ((3.4); e-gauss m5).

  Every change is a choice made before the coupling, so the order and the coupling-independence of V3's constants are kept. Every later choice of V3's chain is re-made from the changed earlier ones. V3's choices after α_G put no lower bound on α_G and no upper bound on M (checked in (3.11); e-gauss m2). CRE's conditions on M are lower bounds or arithmetic: "M be large" (p.245), M ≥ 8LM₂, odd powers of L, M/M₁ integral (L3968). So K's smaller α_G and larger M violate none of them (e-rest M7). Then g₀ is reduced so that s ≤ s_*, with s_* fixed by the chain (collected at the end of (3.4)). V3's real statements hold a fortiori under K, since every condition changed is monotone in the direction used. Repair K′ of (3.6) is a further change; it needs the user's agreement.
- **(3.1) Hessian bounds.** By (1)(f), γ − s ≤ R ≤ h_+ + s and ‖S‖ ≤ s, with V3's range R_V. The bound s ≤ C_Hρ₁ comes from the Schur bound c_H on the entry derivatives (L3076). Those derivatives come from Cauchy estimates on the joint polydisc of §c4-10-1, so they hold in complex directions at complex points of a smaller polydisc.
  - *Evidence (e-gauss m7).* The entries are bounded on §c4-10-1's joint complex polydisc "uniformly in Z" (L4880ff.), which gives the Cauchy estimates. At U₁ the real chart has the margin ρ₀ of (3.6) (e-red m1, (2)(c)), and along the path the phase test's margin.
  - For s ≤ γ/4, R ≥ γ − s ≥ γ_c and R ≤ h_+ + s ≤ h_c (e-gauss m6: s < γ/2 strictly is needed below, and s ≤ γ/4 is put into s_*). The min–max step at D(Λ) (L3076) is replaced by (1)(a).
- **(3.2) Walk series (L717–755) and tail (L3804–3809).**
  - *Real-only step:* "has operator norm at most q_H^n" (L717) is spectral.
  - *Complex (e-gauss m4).* 𝖠_H = (1 − R/s_H) − iS/s_H, with q_H, s_H computed from (γ_c, h_c) under K. For s ≤ γ/4, 0 ≤ 1 − R/s_H ≤ 1 − (γ − s)/s_H, so
    - ‖𝖠_H‖ ≤ 1 − (γ − 2s)/s_H, used for the square root below;
    - ‖𝖠_H‖ ≤ q_H + s/s_H, used for the walk constants, since γ − s ≥ γ_c.
    Block supports and stencils do not change.
  - With n_* chosen under K, (1 + s/(s_Hq_H))^{n_*} ≤ 2 for s ≤ s_Hq_H log 2/n_*. Then β^c := V_*(q_H + s/s_H)^{n_*} ≤ 2β and a_*β^c ≤ 2a_*β ≤ 1/4 (e-gauss m5). With C_w and δ_M as fixed in K (e-gauss m1), Lemma walk-series (bound, holomorphy in σ on the larger polydisc, gauge law) and (fixed-kernel-rooted-tail) hold with V3's constants.
  - The binomial series still sums to a square root of 𝖦 = H^{−1}, since (Σ_j a_jx^j)² = (1−x)^{−1} as power series and ‖𝖠_H‖ < 1. It is symmetric, and ‖𝖦^{1/2}‖ ≤ s_H^{−1/2}(1 − ‖𝖠_H‖)^{−1/2} ≤ (γ − 2s)^{−1/2}.
- **(3.3) Conditioning (Lemma conditioning, L763–772).**
  - *Real-only step:* the proof is probabilistic ("conditional law").
  - *Complex (repaired, e-gauss S1).* The convex set {R > 0, ‖𝖠_H‖ < 1} used before is too large: (3.4) covers only s ≤ s_*. Put
    - 𝒦 := {H real symmetric : γ ≤ H ≤ h_+};
    - 𝒩 := {H complex symmetric : dist_op(H, 𝒦) < s_*}.
  - 𝒩 is convex (the Minkowski sum of the convex 𝒦 and an open ball), hence connected, and open. It contains the nonempty set of real symmetric H with dist(H, 𝒦) < s_*, which is open in the real symmetric matrices. It contains H_𝐔, since H_{U₁} ∈ 𝒦 and ‖H_𝐔 − H_{U₁}‖ ≤ s < s_*. Every H ∈ 𝒩 lies within s < s_* of some H′ ∈ 𝒦, so (1)(f), (3.2) and (3.4) apply to it.
  - Both sides of (c-conditioning) are analytic in H on 𝒩. The left side is a normalised complex Gaussian ((1)(e)); the right side converges locally uniformly by (3.4).
  - They agree on the real points of 𝒩. An analytic function on a connected open set that vanishes on a nonempty open set of real points vanishes identically (its power series vanishes there). So they agree on 𝒩.
  - L778, "C_{E₀} is real, positive and independent of σ; its determinant is one fixed positive number": at 𝐔, C_{E₀} is complex symmetric with Re C_{E₀}^{−1} ≥ γ − s, and det C_{E₀} is one fixed nonzero number, independent of σ.
  - *Uses (e-gauss m8).* The sentence is not cited elsewhere in V3. det C_{E₀} recurs at L4917, as the local normalisation. So only its σ-independence and its nonvanishing are used.
- **(3.4) Gaussian payment (Lemma gaussian-payment, L794–803; proof L3803–3833), recomputed.** Write H_E = R_E + iS_E for ι_{E₀}^*Hι_{E₀}, C := H_E^{−1} = C′ + iC″, and γ′ := γ − s.
  - *(i).* The tail bound of (3.2) and ‖H‖ ≤ h_+ + s ≤ h_c give ‖Γ(σ) − Γ(1)‖ ≤ h_cδ_M. With the binomial square root of C (the series of (3.2) for H_E, a principal restriction, so (1)(a) applies), ‖C^{1/2}‖ ≤ (γ−2s)^{−1/2} and ‖C^{1/2}(Γ(σ)−Γ(1))‖ ≤ h_c(γ−2s)^{−1/2}δ_M.
  - *Consumers of (i) (e-gauss m9).* V3 uses only the first bound of (i): L3819 takes it for ‖Γ₁‖ and ‖Γ₂‖. The second bound occurs only in the statement (L797) and its derivation (L3809). So no consumer receives the non-Hermitian binomial square root.
  - *Real-only step:* "Γ_{E₀}(1) is real, so Γ₂ = Im(Γ_{E₀}(σ) − Γ_{E₀}(1))" (L3811). At 𝐔, Γ(1) = ι^*HΠ𝖦^{1/2} is complex. Differentiating the series along the segment from H_U to H (inside 𝒩) gives ‖Γ(1) − Γ(1)|_{H_U}‖ ≤ C_Γ s, with C_Γ := γ_c^{−1/2} + h_cγ_c^{−3/2}/2, since γ − 2s ≥ γ_c for s ≤ γ/4. So ‖Γ₂‖ ≤ h_cδ_M + C_Γs and ‖Γ₁‖ ≤ A_c := h_c((γ−2s)^{−1/2} + 1) + C_Γs. At s = 0, A_c = h_c(γ^{−1/2}+1) < A_* (since γ > γ_c), so A_c ≤ A_* for s below a fixed s_A.
  - *The B-integral.* |dμ_C(B)| = (2π)^{−n/2}|det H_E|^{1/2}e^{−⟨B,R_EB⟩/2}dB. Against e^{α_G‖B‖²/2} and |e^{−⟨B,ΓX⟩}| = e^{−⟨B,Γ₁X⟩}, the B-integral is

    (|det H_E|/det R_E)^{1/2}·det(1 − α_GR_E^{−1})^{−1/2}·e^{⟨Γ₁X,(R_E−α_G)^{−1}Γ₁X⟩/2}.

  - *The X-form.* With Re⟨ΓX,CΓX⟩ = ⟨Γ₁X,C′Γ₁X⟩ − ⟨Γ₂X,C′Γ₂X⟩ − 2⟨Γ₁X,C″Γ₂X⟩ (bilinear pairings, C′ and C″ real symmetric), the X-exponent is ⟨X,T^cX⟩/2 with

    T^c := Γ₁ᵀ[(R_E−α_G)^{−1} − C′]Γ₁ + Γ₂ᵀC′Γ₂ + Γ₁ᵀC″Γ₂ + Γ₂ᵀC″Γ₁,

    real symmetric and supported on J_Z (Lemma component-blocks is a support statement). At S = 0 this is V3's T_{α_G}. T^c need not be positive semidefinite, and nothing below uses that it is.
  - *Norm.* C − R_E^{−1} = −iCS_ER_E^{−1}, so ‖C′ − R_E^{−1}‖, ‖C″‖ ≤ s/γ′², and ‖C′‖ ≤ 1/γ′. Hence

    ‖T^c‖ ≤ A_c²[α_G/(γ′(γ′−α_G)) + s/γ′²] + ‖Γ₂‖²/γ′ + 2A_c‖Γ₂‖s/γ′² ≤ 2α_GA_c²/γ′² + 2h_c²δ_M²/γ′ + C₃s.

    Under K, the first two terms are at most 1/8 + 1/8, so ‖T^c‖ ≤ 1/3 for s ≤ 1/(12C₃).
  - *The constant C₃ (e-gauss m5).* Put s₀ := γ/4. For s ≤ s₀ use γ′ ≥ γ_c, A_c ≤ A_*, δ_M ≤ 1, γ′ − α_G ≥ γ′/2, and ‖Γ₂‖² ≤ 2h_c²δ_M² + 2C_Γ²s². The terms of ‖T^c‖ that carry a factor s then sum to at most C₃s, with

    C₃ := A_*²/γ_c² + 2A_*(h_c + C_Γs₀)/γ_c² + 2C_Γ²s₀/γ_c.
  - *Determinants.* (1)(d) gives ½log(|det H_E|/det R_E) ≤ d_G|E₀|s²/(4γ′²). The eigenvalues of α_GR_E^{−1} lie in [0, 1/2], as in V3. For |t| ≤ 1/3, −½log(1−t) ≤ |t|, so log det_{J_Z}(1−T^c)^{−1/2} ≤ d_G|J_Z|‖T^c‖. With E₀ ⊆ J_Z the total is at most (C_d^c(α_G + δ_M²) + C₄s)|J_Z|, where C_d^c is (fixed-kernel-trace-payment)'s C_d at (γ′, h_c, A_c) with 2/3 replaced by 1 and the δ-term doubled.
  - *Constants (e-gauss m5).* C₄ := d_G(C₃ + s₀/(4γ_c²)): the determinant ratio contributes d_G|E₀|s²/(4γ′²) ≤ d_G|J_Z|s·s₀/(4γ_c²), and the s-part of ‖T^c‖ contributes d_G|J_Z|C₃s.
    - V3's constant is C_d = d_G max(1/γ + 4A_*²/(3γ²), 2h_+²/(3γ)) (L3829), from the factor 2/3 and ‖T_α‖ ≤ 2α_GA_*²/γ² + h_+²δ_M²/γ.
    - Here the factor is 1 (|t| ≤ 1/3, eigenvalues of either sign) and the δ-term is 2h_c²δ_M²/γ′. So C_d^c = d_G max(1/γ′ + 2A_c²/γ′², 2h_c²/γ′), and C_d^K := d_G max(1/γ_c + 2A_*²/γ_c², 2h_c²/γ_c).
    - C_d^c ≤ C_d^K, since γ′ ≥ γ_c and A_c ≤ A_*. C_d^K is the constant with which K chooses α_G and M.
  - *Result.* With |J_Z| ≤ 4(LM+1)⁴N₁(Z) (L3831) and K, the total is at most (1/2 + 1/4)N₁(Z) + 4C₄s(LM+1)⁴N₁(Z) ≤ N₁(Z) for s ≤ (16C₄(LM+1)⁴)^{−1}. So (ii) holds at 𝐔 with the same e^{N₁(Z)}, and it factors over the components as in V3, since T^c, C and Γ are block diagonal. (iii) is pointwise in B and unchanged. The tilt of (3.12) is paid in the host potentials, not in this budget.
  - *The threshold s_*.* s_* := min(γ/4, s_Hq_H log 2/n_*, s_A, 1/(12C₃), (16C₄(LM+1)⁴)^{−1}). It is fixed by the chain under K, before the coupling. Then g₀ is reduced so that C_Hρ₁ ≤ s_*.
- **(3.5) The complex-Gaussian moment payment (§c4-10-3, L4919–4937), recomputed.**
  - The same computation per component gives |G_σ|e^{α_G‖B‖²/2} = (prefactor)·exp(−⟨y,(R_E−α_G)y⟩/2 − ⟨X,(1−T^c)X⟩/2), with y = B + (R_E−α_G)^{−1}Γ₁X.
  - With R_E − α_G ≥ γ′/2, ‖T^c‖ ≤ 1/3 and ‖Γ₁‖ ≤ A_c, the real form is at least c_G^c(‖B‖² + ‖X‖²), where c_G^c := min(γ′/2, 2/3)/(2(1+2A_c/γ′)²), V3's (c4-10-13) with 3/4 → 2/3. It is at least c_G^K := min(γ_c/2, 2/3)/(2(1+2A_*/γ_c)²), which replaces V3's c_G (L4930) at its two uses, (c4-10-14) and L5021 (e-gauss m5).
  - The mass is ≤ e^{N₁(Z)} by (3.4), and (c4-10-14) holds with c_G^c.
  - The derivative terms Tr(C_E𝒟_ωH_E)/2, ⟨B,(𝒟_ωH_E)B⟩/2, ⟨B,(𝒟_ωΓ)X⟩ and 𝒟_ω⟨ΓX,C_EΓX⟩/2 are bounded as in V3, using |Tr(AB)| ≤ (dim)‖A‖‖B‖, ‖C_E‖ ≤ 1/γ′ and 𝒟_ωC_E = −C_E(𝒟_ωH_E)C_E.
- **(3.8) Words and characters (derived).**
  - *Real-only step:* "|f_ξ| ≤ 1" (L3064) and ‖U_j‖ = 1 hold at unitary data.
  - *Complex (repaired, e-rest M3).*
    - For X ∈ 𝔤_ℂ and unitary U, ‖π(e^{iX}U)‖_op ≤ e^{‖π(Im X)‖_op}. This is the logarithmic-norm bound: iπ(Re X) is skew-Hermitian, so the Hermitian part of iπ(X) is −π(Im X). Also ‖π(x+iy)‖_op ≤ √2C_π h_ℂ(x+iy) (Lemma c5-5-7z, L2738).
    - A traversal link is L_n = e^{iq(Ψ_ξ(a+A_e))(r_n)}𝐔(r_n) (L2740), with the reconstruction phase q evaluated at the background 𝐔. The phase is real at real data, and ‖D_Zq_Z(a)‖ ≤ Cg₀(1+r) ((c4-10-4)). So at real a in the enlarged box, ‖Im q(r_n)‖ ≤ C_qg₀(1+r)‖a′‖_{N(r_n)}, with N(b) the stencil of b.
    - So ‖π(L_n)‖ ≤ exp(√2C_π(1 + C_qg₀(1+r))‖a′‖_{N(r_n)}) ≤ exp(C_U‖a′‖_{N(r_n)}), with C_U := 2√2C_π once C_qg₀(1+r) ≤ 1. The same bound holds for π(L_n)^{−1} = e^{−iπ(q)}π(𝐔(r_n))^{−1}.
    - Hence ‖U_j(𝐔)‖ ≤ exp(C_UΣ_{n∈U_j}‖a′‖_{N(r_n)}), and |f_ξ(m₀)(𝐔)| ≤ exp(C_UΣ_{n∈C}‖a′‖_{N(r_n)}) ≤ e^{C_UP(C)ρ₁}, at the real shift m₀ of (3.12).
    - Inside c_W, |χ(T_WP_W^{−1}h)| ≤ ‖π(T_WP_W^{−1}h)‖ ≤ e^{C_UL_fρ₁}. χ is normalised, so there is no factor dim π, and the bound reduces to V3's "≤ 1" at a′ = 0.
  - The words' factor is not uniformly bounded on the polydisc: it grows like e^{P(C)ρ₁} with the perimeter. So D1(iii)′ states it in this product form, and D2 may not use a uniform sup of f_ξ over the polydisc.
  - *Absorption (repaired, e-red S1, e-rest M1).*
    - L_f ≤ C_L𝔰(W) with C_L = O(LM). L4848 gives L_f ≤ 2|ℋ(W)| times the row-overlap constant; Lemma c5-5-3's proof gives |ℋ(W)| ≤ LMσ(W); and σ = 𝔰 (Lemma c5-5-8, L3066).
    - Put C′ := C_UC_L + C_c, with C_c the constant of the closed contractions in (3.7) and (3.9). So each group's factor is at most e^{C′𝔰(W)ρ₁}.
    - §3a(6) spends the whole pin weight e^{4η𝔰}: η/8 on e^{θ°} and 31η/8 on the decay. So the factor is absorbed by lowering the decay rate to 30η/8, under the g₀-threshold C′ρ₁ ≤ η/8. The split of §3a(6) becomes 𝔰³e^{η𝔰/4} ≤ (k+1)³e^{η/4}e^{−(30/8)ηk}e^{4η𝔰}, and likewise e^{η𝔰/4} ≤ e^{−(30/8)ηs_n}e^{4η𝔰}.
    - §3a(7) keeps its rate: there σe^{η𝔰/8} ≤ Ce^{4ησ−ησ} leaves more than η𝔰/8 spare.
  - *Own words only (e-rest M5).* The factor e^{C_UL_fρ₁} bounds the group's own words. In Lemma c5-5-7(c) the word U¹_j − U⁰_j includes the gap G_j, and its factor is e^{C_Un_jρ₁}, with its own length n_j. That step feeds (c5-5-7), not the group majorants.
- **(3.6) Charts and primitives (Lemma c2-uniform-chart, L3689–3711; §c4-10-1, L4880–4907; Lemma c5-4-0(c), L2491).**
  - Lemma c2-uniform-chart is stated for real backgrounds U with ‖φ‖_∞ ≤ τ_L/2 in a site gauge. Its proof (L3704) gets uniform constants from two facts: the maps are "analytic for phases ‖φ‖_∞ ≤ τ_L and A near zero", and the set of real phase configurations with ‖φ‖_∞ ≤ τ_L/2 is compact.
  - The same compactness gives a fixed width ρ₀ > 0, depending on L and G only, such that every map in (i)–(iv) is analytic on the complex neighbourhood 𝒱_{ρ₀} := {‖Re φ‖ ≤ τ_L/2 + ρ₀, ‖Im φ‖ ≤ ρ₀}. The contraction of (ii) and the implicit function theorem of (iv) are complex arguments already.
  - *"At most doubled" withdrawn (e-rest S2).* The lemma needs 4K_*H_*ϑ_* < 1: (ii) needs ‖DΦ‖ ≤ 2K_*H_*ϑ < 1/2, and (iii) needs the determinant within 2K_*H_*ϑ_* < 1/2 of id. With H_*, K_* doubled the same computation gives only 8K_*H_*ϑ_* < 2. The host budget of (3.7) has the same problem with a doubled C_p.
  - **Repair K′ (a V3 change beyond K; agreed by the user for the V3 overhaul, 22 Oct, 08:57; not made in V3).** After τ_L, choose ρ₀ as above. Define H_*, K_*, C_C, C^D_k, C^a_k, Q_*, C_Π, C_p and C^∂_p as the sups of the corresponding quantities over 𝒱_{ρ₀} instead of over the real phases. Then choose ϑ_* and every later constant as V3 does, from these.
    - Each sup over 𝒱_{ρ₀} dominates the real one, and every later choice is made from the dominating constants. So V3's real statements hold a fortiori, and the order and coupling-independence of the chain are kept.
    - At 𝐔 the lemma then holds with these constants and no doubling. The potential bound (c5-4-4) holds at 𝐔 with V3's formula ω_t = C₀g₀(1+2r)³, C₀ built from K′'s C_p, and the host norms with K′'s C^∂_p.
  - In the real gauge of U₁ on a stencil, 𝐔 has phases φ^c with ‖φ^c − φ‖ ≤ Cρ₁ ((2)(c)). So the lemma applies at 𝐔 once Cρ₁ ≤ ρ₀.
  - *Real-only steps of the lemma, not used at 𝐔:*
    - "real on real A";
    - the positivity of the determinant in (iii);
    - the real logarithms;
    - "for unitaries ‖U₁⋯U_n − id‖_op ≤ Σ_j‖U_j − id‖_op" in (iv);
    - in (iv), "for real q, M_x(q) is unitary" and "D𝒢_{y,U}(0) = 0 because each summand is nonnegative on real q" (e-rest M4).
    At 𝐔 the logarithms are the analytic ones on matrix balls of radius < 1/2 (as V3 already uses at L4907). The product bound becomes ‖Π(1+X_j) − 1‖ ≤ e^{Σ‖X_j‖} − 1. This changes the constant in the choice of τ_L, before the coupling; it is part of K′. The conclusion D𝒢_{y,𝐔}(0) = 0 holds at 𝐔 by the identity theorem in the background: D𝒢_{y,·}(0) is analytic in the chart phases and vanishes at the real ones.
  - §c4-10-1's bounds (c4-10-3), (c4-10-4) and the primitive bounds |p^E| + ‖D_Zp^E‖ ≤ Cg₀(1+r)³ come from Cauchy estimates and uniform contraction on the joint complex polydisc, so they hold at complex Z in the smaller polydisc, with the complex sups as constants (K′). The potential bound (c5-4-4) is a bound on |𝐕|; it holds at 𝐔 with ω_t under K′, and with ω̃_t once the tilt of (3.12) is added.
  - The sentence "K^Λ_{ξ;t} > 0 there, I^Λ_t > 0" of Lemma c5-4-0(c) is a normaliser statement. It is not used along the path (L3078) and not used here.
- **(3.7) Selected integrals, majorants and vacuum clusters (Lemmas c5-4-1, c5-4-2, Corollary c5-4-3, Lemma c5-5-2(a)–(c); §c4-4, §c4-7).** V3 states that their proofs use the background only through Lemma c5-4-0(a), (c) and (d) (L3078); V3's sentence concerns exterior parameter zero along the path. (a) is (3.1)–(3.5) and (c) is (3.6). In (d) (hosts) the geometry is field-independent, but the bound (c5-4-4) depends on (c) (e-rest M6); it holds at 𝐔 under K′, with the tilt of (3.12). A scan of L2515–2665, L4468–4580, L4618–4760 and L4864–4976 for positivity, reality and unitarity found these uses:
  - *Normalisers:* Ξ^{f,t}_Λ > 0, I^Λ_t > 0 (L2515ff.). They are not used along the path, and the extension (3.10) never divides by them.
  - *Cutoffs (repaired, e-red S2, e-rest S1):* "χ^t_b ≤ 1", "for b ∈ 𝖯 and real B" (Lemma c5-4-2). With V3's shift m = −H⁻¹ℓ at the background 𝐔, the cutoffs χ^t_b(B) = 1{|B_b + tm_b|_σ < r} would be complex for t > 0. With the real shift m₀ of (3.12) they are V3's real cutoffs at U₁, for every t, and so are the boxes, reserves and shells.
  - *Parity:* "the determinant, the quadratic cross term, the compensator, the real cutoffs χ_b, 1−χ_b and the spatial Cauchy integrations are even" (§c4-4-1, L4484). The evenness under (B,X) ↦ (−B,−X) is algebraic and holds at complex H.
  - *Positive host comparison* (Lemma c4-7-1, L4684–4710): "After taking absolute values inside the real Mayer t-integral … a positive numerical comparison". It is a comparison of absolute bounds A_Y + B_Y ≤ (5/8)ω_*e^{−κd₀(Y)}. For real t_Y and complex 𝐕, |∫₀¹ζ𝐕e^{tζ𝐕}dt| ≤ e^{|ζ𝐕|} − 1, so it needs |𝐕_𝐔| ≤ C^∂₀g₀(1+r)³e^{−κd₀} with V3's formula. That holds at 𝐔 under K′ ((3.6)), and with ω̃_t ≤ ω_* after the tilt ((3.12)). The Mayer parameter t_Y ∈ [0,1] stays real.
  - *Positive sums* (Lemma c4-6-2, the pins of Lemma c5-5-8(a)): field-independent geometry with positive majorants. Unchanged.
  - *Unitarity in words:* "All untouched transports are unitary matrices inside the same closed contraction" (L4480), and the unitary factors of Lemma c5-5-7z (L2737–2755). At 𝐔 these factors have norm ≤ e^{C_U‖a′‖_{N(b)}} per link ((3.8)), so each closed contraction gains a factor ≤ e^{C_cL_fρ₁}, absorbed as in (3.8).
  - *Omitted before (e-rest M4).*
    - Lemma c5-5-7z(b): "at real points its real-direction derivatives are the adjoints of those of π(L_{n_i})" uses π(L)^{−1} = π(L)^*. At 𝐔, π(L)^{−1} = π(𝐔(r_n))^{−1}e^{−iπ(q)} is bounded directly: its norm by (3.8), and its derivatives by the same Cauchy estimate as for π(L) in (a).
    - Lemma c5-5-7(d): "‖N′_s‖ ≤ ‖∂_sπ(P^s_W)‖" and the "product rule for the word of unitaries". At 𝐔 each word factor has norm ≤ e^{C_U‖a′‖_N}, and the two steps gain per-group factors ≤ e^{C_UL_fρ₁}.
  - *Real directions:* "take a real background direction ω" (Lemma c4-4-3, L4535). For a complex direction ω^c, 𝒟_{ω^c} = 𝒟_{Re ω^c} + i𝒟_{Im ω^c} (complex-linear derivative of an analytic function), so the bound holds with a factor 2. The base point is complex, which (3.1)–(3.6) supply.
  - Kotecký–Preiss for the vacuum clusters uses the activity bound |k| ≤ m in absolute value, so the Φ^{v,t} are convergent cluster series at 𝐔, analytic by (2)(a).
- **(3.9) The exterior part (Lemmas c5-5-3, c5-5-7z, c5-5-7; (c5-5-8)).**
  - c^t_W = w^t_Λ(W)∫χ(T_WP_W^{−1}h) d⊗ν̂^{f,t}_{Λ,Z}, defined in the statement of Lemma c5-5-7; w^t is defined in Lemma c5-5-3(a) (L2667), from the vacuum cluster weights of Corollary c5-4-3 (e-rest M6). No physical normaliser enters.
  - Lemma c5-5-7 uses no parity (L2786). Its unitarity steps are "the links are unitary and the word is their ordered product, so the difference is at most the sum of the link differences" and ‖N_t‖ = 1. At 𝐔, ‖ΠX_i − ΠY_i‖ ≤ (max_i max(‖X_i‖,‖Y_i‖))^{n−1}Σ_i‖X_i − Y_i‖, with n the word length. For the group's own words n ≤ L_f, so the factor is ≤ e^{C_UL_fρ₁}, and ‖N_t‖ ≤ e^{C_UL_fρ₁}. For the gap words of (c5-5-7) n is their own length (e-rest M5, (3.8)).
  - So (c5-5-8) and §3a(7) hold at 𝐔 with the extra factor e^{C_UL_fρ₁} ≤ e^{C′𝔰ρ₁}, absorbed by the pin weight as in (3.8).
  - *Marks (repaired, e-red S2, e-rest S1).* V3's marks are built from the shift: 𝔪_b = 2ϖ_b with ϖ_b ≤ C_Vr^{d_G−1}|m_b|_σ (Lemma c5-5-5), and 𝔪_Y ∝ Σ_{b∈E(Y)}h(m_b) (Lemma c5-5-6). At 𝐔 they are taken at the real shift m₀ of (3.12), so they are V3's real marks at U₁. The thin-shell lemma holds for any real tilt (L2696), and the density at 𝐔 is centred, so it applies to the modulus as in (3.11). The tilt adds the host marks 𝔪^δ_Y of (3.12).
- **(3.10) The extension and its identification (derived).**
  - *Definition (repaired, e-red m4, e-rest H5).* For every group, c_W(𝐔; h) is V3's coefficient formula at the background 𝐔 in the analytic form of L4842. For a generic noncritical background V3 defines the energy primitive by subtracting its constant, linear and quadratic Taylor terms, and the Haar and constraint-Jacobian primitives by their analytic row formulas; "These definitions specify an analytic coefficient extension" (L4842). The other ingredients are the selected integrals with H_𝐔, the real shift m₀ and the tilt of (3.12), the charts of (3.6), and the vacuum cluster series. The regional data I, Ω₁, D(Λ), the cutoffs (real, at m₀) and the labels are held fixed (L4838). This removes the earlier mismatch between "selected integrals with H_𝐔" and "cutoffs held fixed" at t = 1.
    - Υ_W(𝐔) is obtained from it by Burnside (Lemma c5-5-7(a)), uniformly in h ∈ G. By (2)(a) and (3.1)–(3.9), (3.12) it is analytic on the ρ₁-polydisc.
    - At a′ = 0 it is V3's c_W(U₁; h): at the physical endpoint each compensated primitive agrees with its Taylor-subtracted formula by locality, criticality being used only in the primitive-sum identity (L4842). At 𝐔 only the analytic form is used, so no criticality is needed off the real critical backgrounds. Covariance at noncritical backgrounds is L4998.
  - *Path endpoint.* For a good group passing the phase test, the formula at 𝐔 equals the formula at e^{iB^c_W} (the path endpoint of (2)(d)). The proof is V3's for t = 1 (L4853, L3082):
    - by G-covariance with the real g_W, the formula at 𝐔 equals the formula at 𝐔^{g_W};
    - by coefficient locality on Q_W (the support statements of §c4-10-2: seed inverse on E₀, walks inside their domains, stencils in Q_W), it equals the formula at the background that is 𝐔^{g_W} on Q_W and id elsewhere, which is e^{iB^c_W}.
    Both properties are properties of the formula, true at every background, so the identity holds at complex 𝐔. It is not an identity-theorem argument: the physical (critical) backgrounds U₁(V) form a lower-dimensional submanifold, on which agreement would not determine the extension.
  - *Other groups.* For groups that are not good, or that fail the phase test, only the direct formula is used, with the endpoint majorant |c_W(𝐔; h)| ≤ e^{C′𝔰(W)ρ₁}M^{(ρ)}_Λ(W) from (3.7), (3.8).
- **(3.11) The remaining uses (checked 00:53–00:57).**
  - *α_G and M after K.* α_G enters later only through a_bad = c_nα_Gr²/4, in conditions on g₀ alone: (9/16)a_bad ≥ max(160(κ + log(8M⁴+8) + 1), 64 log(1/η_*)) (L2538), (9c_nα_G/64)A₁²log g₀^{−2} ≥ 1 (L2862, L3973), with r = A₁(log g₀^{−2})^{p₀} → ∞. α_G is fixed after M (L3857, L3968). No later choice bounds α_G from below or M from above, so K is consistent with V3's order.
  - *The thin-shell lemma (Lemma c5-5-5, L2695–2706).* It is applied to the modulus of the density (L2708: the tilt is "e^{−⟨B, Re Γ_{E₀}(σ)X⟩} after moduli are taken"). At 𝐔 the modulus of dμ_{C_{E₀}} is (|det H_E|/det R_E)^{1/2} times the real Gaussian with precision R_E. So the lemma applies verbatim to R_E, with γ − s and h_+ + s, and ϖ_b computed with h_+ + s at the real shift m₀ ((3.12)). No complex conditional mean occurs.
  - *The general pattern.* Every V3 argument that takes moduli runs on R_E with V3's own real lemmas, plus two perturbation terms: the determinant ratio of (1)(d) and T^c in place of T_α.
  - *§c4-12-1 (L5040–5049), read.* It uses Lemmas c4-7-1 and c4-7-2, (c4-7-8), (c4-8-10), (c4-10-6), (c4-10-9), (c4-10-14) and the parity of the root Gaussian, all covered by (3.2), (3.5), (3.7) and (3.8) (e-rest M6 added (c4-7-8) and (c4-8-10). (c4-7-8), L4741, is the derivative bound |𝒟_ωΦ^v_ξ(𝔠)| ≤ C_M‖ω‖n(𝔠)M_v(𝔠) of the vacuum cluster functions: at 𝐔 it follows from the Kotecký–Preiss and complex-direction items of (3.7), with the factor 2. (c4-8-10), L4828, is the product rule for 𝒟_ωw_ξ(W), an identity). So (c4-12-1) holds at 𝐔 with C_χ replaced by C_χe^{C′𝔰ρ₁}, and the derivative bound (c4-12-2) with 2C_χe^{C′𝔰ρ₁}. The 2 is the complex direction of (3.7) and belongs to the derivative bound only.
  - *§c4-12-2 (L5051–5060), read.* It uses δ_{Q_W}(U₁) ≤ Cε₁ and the real phase test, both at the real U₁; the path, replaced by (2)(d); the endpoint identities (c4-11-6), replaced at 𝐔 by (3.10); and the pins.
  - *Lemma c4-9-2 (L4864–4874), read.* It uses positive majorants, Kotecký–Preiss on |a_W| ≤ M(W), the walk-derivative series of §c4-10-2, which is (3.2), and the "uniform Gaussian coercivity (Section c4-10-3)", which is (3.5).
  - *§c4-10-2 (L4909–4917), read.* "Of the background these constructions use only the input bounds … γ ≤ H ≤ h_+, and the R-locality of the entries". The block bound V_j jq_H^{j−1} becomes V_j j(q_H^c)^{j−1}, and "the denominators positive because a_*β ≤ 1/4" holds under K. The locality paragraph (L4917) is the structural fact used in (3.10); it also says the Gaussian determinant is the local det C_{E₀}, never one on all of I.
  - *§c4-10-4 (L4938–4955), read.* "a normalised character, so |f| ≤ 1; untouched factors are unitary". At 𝐔, (c4-10-8)–(c4-10-10) hold for the source f_W with the factor e^{C_UL_fρ₁} of (3.8). For the full closed Wilson character the factor is e^{C_UP(C)ρ₁} (e-rest M6).
  - *Missing evidence (e-rest M7).* The scan covers the ranges listed in (3.7); outside them it is a summary, not a certificate. The uncovered-term claim of (4) rests on §3d(2), and on where a′ acts ((0), e-red m5): links in Ω₁ᶜ carry the unchanged V₀, and exterior-input links carry 𝐔 times the real exterior reconstruction. On uncovered terms, Lemma c5-5-7z's preamble (stated on A^fin_cov, L2738) is replaced by §3d(1)(d): the row input lies in 𝒰_c, with the preamble's bound ‖A‖ ≤ ϑ_*/4. a′ does not change the row input, since it acts on the background only. So at 𝐔 the link bounds follow from the chart at 𝐔 ((3.6), Cρ₁ ≤ ρ₀) and (3.8).

- **(3.12) The exterior shift at complex backgrounds (new; round-4 repair of e-red S2 and e-rest S1; written 07:08–07:16, 22 Oct (session log), not reviewed).**
  - *The problem.* V3 centres the young variable at m = −H_DD^{−1}H_DJA^{Λ,Ψ} (L2298, L2620), a = B + tm (L2501). At 𝐔, H is H_𝐔 and m(𝐔) is complex. The cutoffs χ^t_b(B) = 1{|B_b + tm_b|_σ < r} (L2503), the boxes, the reserves (1 − t|m_b|_σ/r)²a_bad (L2557), the shells ϖ_b ≤ C_Vr^{d_G−1}|m_b|_σ (Lemma c5-5-5) and the marks (Lemma c5-5-6) would all depend on 𝐔 for t > 0. The real integration variable cannot be translated by a complex vector without moving these.
  - *Translation by the real shift.* Put m₀ := m(U₁), real, and at 𝐔 set a = B + tm₀. (c5-4-2) is the completion of the square in −½⟨a,H_DDa⟩ − t⟨a,ℓ⟩, with ℓ := H_DJA^{Λ,Ψ}; at real U₁ this gives V3's constant e^{½t²⟨m,Hm⟩} (L2507). At 𝐔, with the bilinear pairing and H_𝐔 symmetric ((1)(f)),

    −½⟨a,H_{𝐔,DD}a⟩ − t⟨a,ℓ_𝐔⟩ = −½⟨B,H_{𝐔,DD}B⟩ − t⟨B,δℓ⟩ − t²(½⟨m₀,H_{𝐔,DD}m₀⟩ + ⟨m₀,ℓ_𝐔⟩),

    δℓ := H_{𝐔,DD}m₀ + ℓ_𝐔 = (H_𝐔 − H_{U₁})_{DD}m₀ + (H_𝐔 − H_{U₁})_{DJ}A^{Λ,Ψ},

    since H_{U₁,DD}m₀ + ℓ_{U₁} = 0. At a′ = 0, δℓ = 0, and the constant is V3's.
  - *The constant.* e^{−t²(½⟨m₀,H_𝐔m₀⟩ + ⟨m₀,ℓ_𝐔⟩)} is a nonzero complex number, the same in the numerator and the denominator of every ratio (c5-4-3) and in Ξ^{f,t}. V3 never estimates its counterpart (L2513), and the formula of (3.10) uses normalised quantities only through cluster series ((3.7)). So it cancels.
  - *Size of δℓ.* The entries of H_𝐔 − H_{U₁} vanish out of V3's range, since the real entries vanish identically there: (H_𝐔 − H_{U₁})(b,b′) ≠ 0 forces d(b,b′) ≤ ρ_L (I1). They have norm ≤ C_eρ₁, with C_e the entrywise Cauchy constant behind C_H ((3.1)). Use h(m₀(b′)) ≤ C_mϑrΣ_{e∈J₁(Λ)}e^{−μ_Hd(b′,e)} ((c5-5-1)), h(A^{Λ,Ψ}_e) < ϑr on J₁(Λ) (Lemma c5-3-1(b), as at L2620), d(b′,e) ≥ d(b,e) − ρ_L, and the count 4(2ρ_L+1)⁴ of the b′ with d(b,b′) ≤ ρ_L (L2620). Then

    h_ℂ(δℓ(b)) ≤ C_δρ₁ϑr Σ_{e∈J₁(Λ)} e^{−μ_Hd(b,e)},   C_δ := C_ee^{μ_Hρ_L}(4(2ρ_L+1)⁴C_m + 1).

    So δℓ has (c5-5-1)'s form, with C_m replaced by C_δρ₁: it is small in the coupling and decays from J₁(Λ).
  - *The tilt in the host potentials.* Assign each b ∈ D(Λ) to its probe host Y_b ∈ 𝐃₀(Λ) (Lemma c5-4-0(d), L2491; b ∈ Y_b by (c-probe-host), L873). For Y ∈ 𝐃₀(Λ) put

    W̃_t(Y,B) := 𝐖_t(Y,B) − t·Π_{b′∈E(Y)}χ^t_{b′}(B)·Σ_{b: Y_b=Y}⟨B_b, δℓ(b)⟩.

    The integrand carries Θ^t (L2507), on whose support every box factor is 1. So Σ_Y W̃_t = Σ_Y 𝐖_t − t⟨B,δℓ⟩ there, and the identity is exact. The Gaussian stays centred, with the complex H_𝐔, as in (3.4).
  - *The polymer-lemma inputs are kept (L2531).* (i) The cutoffs are V3's real single-bond cutoffs at m₀, with values in {0,1}. (ii) W̃_t(Y,·) depends on B|_{E(Y)} only and vanishes off the translated local box. On the box, |B_b|_σ < r + |m₀_b|_σ ≤ 5r/4 (|m₀_b|_σ ≤ r/4 by (c5-4-1)). With |⟨x,y⟩| ≤ C_σ|x|_σh_ℂ(y) (C_σ a norm-comparison constant of 𝔤), sup_bΣ_{e∈J₁}e^{−μ_Hd(b,e)} ≤ N_lat(μ_H), and |E(Y)| ≤ 4(4M+2)⁴ (Y is a rectangle of at most 4⁴ M-cubes), the tilt part is at most

    τ̄ := (5/4)C_σC_δN_lat(μ_H)·4(4M+2)⁴·ρ₁ϑr².

    So |W̃_t(Y,B)| ≤ ω̃_te^{−κd₀(Y)} with ω̃_t := ω_t + e^{κ(B_h+4)}τ̄, since d₀(Y) ≤ B_h + 4 (L3788).
  - *Tilt threshold (new g₀-threshold).* V3's threshold items 4(ii) and 4(iii) (L3973) hold with ω_t and ω̄ replaced by ω̃_t and ω̄̃ := ω̄ + e^{κ(B_h+4)}τ̄. Every term on their left sides tends to 0 with g₀, and so does τ̄, since ρ₁r² ≍ g₁(log g₁^{−2})^{q₁}(log g₀^{−2})^{2p₀} → 0. Then ω̃_t ≤ ω_*/2 ((c5-4-T)), and Lemmas c5-4-2 and c4-7-1 apply at 𝐔 with W̃_t.
  - *New host marks.* On Θ^t's support the t-derivative of the tilt part of W̃_t(Y,·) is −Σ_{b:Y_b=Y}⟨B_b,δℓ(b)⟩, of modulus ≤ (5/4)C_σrΣ_{b:Y_b=Y}h_ℂ(δℓ(b)). Its box factor is handled by V3's bond marks, as for 𝐖_t (L2732). In the telescoping of Lemma c5-5-6 this gives, as for V3's second form of 𝔪_Y (L2718),

    𝔪^δ_Y := (5/4)C_σr(1+ω̄̃)e^{ω̄̃}·e^{κ(B_h+4)}/ω_*·e^{1/8}·Σ_{b:Y_b=Y}h_ℂ(δℓ(b)) ≤ C^δ_bdρ₁ϑr²Σ_{b:Y_b=Y}Σ_{e∈J₁(Λ)}e^{−μ_Hd(b,e)},

    with C^δ_bd := (5/4)C_σC_δ·2e·e^{κ(B_h+4)}e^{1/8}/ω_* (ω̄̃ ≤ 1 by the tilt threshold). V3's own marks 𝔪_Y (L2716–2718) are taken with ω̄̃ in place of ω̄. The tilt marks have the decay of V3's host marks from J₁(Λ), and they are small in the coupling (ρ₁r² → 0). They enter §3a(7) through 𝔪̂_Δ. They vanish at a′ = 0.
  - *What else uses m.* The leading word is f_ξ(m₀) at 𝐔 ((0)). The response bound, Lemma c5-5-4 (L2687), holds at 𝐔 with C_resp,χ replaced by C_resp,χe^{C_UP(C)ρ₁} ((3.8)) and h(m₀_b). The shells, reserves and bond marks are V3's real ones at m₀ ((3.7), (3.9)).
  - *Rejected alternatives (one line each).* Putting the tilt into the Gaussian (a complex linear term in X) breaks the centring that (3.4) uses. Translating by the complex m(𝐔) makes the cutoffs complex.

**(4) Result (derived; restated after round 4, not reviewed).** Under repairs K and K′ ((3.0), (3.6); both agreed for the overhaul, not made in V3), and for g₀ so small that s = C_Hρ₁ ≤ s_*, Cρ₁ ≤ ρ₀, C′ρ₁ ≤ η/8, C_qg₀(1+r) ≤ 1 and the tilt threshold of (3.12) hold:
- D1(iii)′ holds on every labelled term, covered or not. §3d's uncovered carriers use the same objects at D(Λ) (§3d(2)), with Lemma c5-5-7z's preamble replaced by §3d(1)(d) ((3.11)).
- Concretely, for real U₁ in the support of the term's indicators and ‖a′‖_∞ < ρ₁:
  - Υ¹_W, the words U_j and f_ξ(m₀) are analytic in a′ and G-covariant;
  - D1(ii) holds in the per-traversal form of §3a(8) with the curvature term C_χρ[δ*^{30}_n(U₁) + a*_n(a′)], the large-field and wrapping terms at the rate 30η/8, and the exterior marks of §3a(7) at their rate, now including 𝔪^δ_Y; wherever the second-order root weight ρ_ph enters (the root weight max(ρ, ρ_ph)), at complex backgrounds ρ_ph ≤ Cg₀²(1+2r)⁴(1 + (log g₀⁻²)^{(q₁−p₀)₊}) (§3j(6) *Order*; the D2.4 item; tj2-r2 E);
  - ‖U_j(𝐔)‖ ≤ exp(C_UΣ_{n∈U_j}‖a′‖_{N(r_n)}) and |f_ξ(m₀)(𝐔)| ≤ exp(C_UΣ_{n∈C}‖a′‖_{N(r_n)}) ((3.8));
  - |c_W(𝐔;h)| ≤ e^{C′𝔰(W)ρ₁}M^{(ρ)}_Λ(W), and |𝒟_ωc_W| ≤ 2C e^{C′𝔰(W)ρ₁}‖ω‖_∞(L_f + n(W))M^{(ρ)}_Λ(W) at every point of the polydisc, in complex directions (e-rest (4)).
- The constants are V3's constants under K and K′, plus C_U, C′, C_δ and C^δ_bd, independent of n, the torus and the labelled term.

**(5) Count check.**
- a*_n(a′) ≤ C_ηρ₁, since Σ_k(k+1)e^{−(30/8)ηk} < ∞. So on the polydisc ν_n ≤ C_χρ(C_ηε₁ + C_ηρ₁) + attached parts, with ρ_ph ≤ Cg₀²(1+2r)⁴(1 + (log g₀⁻²)^{(q₁−p₀)₊}) wherever it enters ρ at complex backgrounds (§3j(6); D2.4; tj2-r2 E). Both ε₁ and ρ₁ are g₁·polylog.
- The extra costs are e^{C′𝔰(W)ρ₁} ≤ e^{η𝔰(W)/8} per group, e^{C₄s|J_Z|} ≤ e^{N₁(Z)/4} per component, and the tilt τ̄e^{κ(B_h+4)} ≤ ω_*/2 per host with marks 𝔪^δ_Y. All are per group, per component or per host, never per volume.
- Tilt marks per traversal. Each bond is assigned to one host, so the tilt marks sum to C^δ_bdρ₁ϑr²Σ_{b∈D(Λ)}Σ_{e∈J₁(Λ)}e^{−μ_Hd(b,e)} against the weights e^{−ηdist(Δ,n)/(C_FLM)} of §3a(7). Up to the bounded factor for moving from a bond to its assigned cube, the summation of (c5-5-2) (X = {n}, μ = η/(C_FLM)) bounds this by Cρ₁ϑr²N_lat(μ_H/2)Σ_{e∈J₁(Λ)}e^{−min(μ_H/2, η/(C_FLM))dist(e,n)}. This is ρ₁r² times V3's collar decay, never a volume sum. The only volume-sized object is the global Hessian, and its determinant cancels: c_W is a selected-integral formula with local normalisations ((3.3), (3.4)).
- Not uniform: f_ξ(m) and the words grow like e^{P(C)ρ₁} on the polydisc. This is intrinsic to the bare loop: it is a product of P(C) links, each of norm e^{‖a′‖}. At real fluctuations they are unitary, so D2 meets this growth only if it takes sup norms of the words over the polydisc. That is a constraint on D2, recorded in §6(f).

## 3f. Round-3 repairs (worked 01:05–02:05, 22 Oct; not reviewed)

The four reports are verification/isolated_reviewer/reviews/it1-{c2-place, c4t-ii, c4q-rep, d11}-20261022-r1. This section gives the repair of each serious item and of the minors; §3c is corrected in place where a line was wrong.

**(0) Source facts used below (quoted and checked in the transcriptions).**
- *p₀.* CRE p.246 l.15: "ε₀ = g₀p₀(g₀), p₀(g₀) = A₀(log g₀⁻²)^{p₀}, p₀ ≥ 5r and A₀ is a sufficiently large constant". Here r = 𝔯 is the exponent of R_j ≥ (log g_j⁻²)^𝔯, and R₁ is the smallest power of L above (log g₁⁻²)^𝔯 (V3 L2465, from p.246). So 2p₀ ≥ 10𝔯.
  - LFR II p.387 (1.88) imposes 2(1+β₀)⁻¹p₀(g_{j+1}) ≥ O(1)3(100M)^dR_{j+1}^{d+2} "for p₀ large". This forces p₀ > (d+2)𝔯 = 6𝔯, which is the binding condition: it is stronger than p.246's p₀ ≥ 5𝔯 (round 4, rd2 m9).
  - LFR II's displays on pp.381–383 (A₀², A₁² written separately; g_j⁻¹δ_j′ = A₁p₁(g_j)) are consistent with p₀(g) = (log g⁻²)^{p₀}; this is inferred, not printed as a definition (rd2 m13). CRE (2.4) puts A₀ in front. The two conventions differ by a constant factor and do not affect any exponent comparison below.
  - In this section r = 𝔯 is the exponent; "ϑr" in R-d″ below is V3's cutoff radius r = A₁(log g₀⁻²)^{p₀} (rd2 m9).
- *The large-field factors.* LFR II p.380 l.38–48:
  - χ_j′^c(Q_j) yields its factor "by expanding the Wilson action locally in the approximate fluctuation field, and using the positivity bound for the resulting quadratic form";
  - χ^{(j−1)c}(R_j) yields exp(−γ₀g_j⁻²δ_j²(LM₂R_j)^{−d}|R_j|) "by the same positivity bound for the quadratic form".
- *Volume and linear size.* p.380 l.29 gives O(1)log g_j⁻²|Z_j| ≤ O(1)log g_j⁻²(MR_j)^d d_j′(Z_j). Since d′ can be 0 (p.384), the note uses |Z_j| ≤ (MR_j)^d(d_j′(Z_j)+1) (rd2 m10).
- *(1.79).* p.383 l.47: (1.79) "holds for all large field regions", "not only for the regions satisfying the conditions (i), (ii)". It says nothing about covers with an added generator such as W₁ (rd2 m11); the generator W₁ is treated in (2) Minor 4.
- *[15].* LFR II p.392 (the corrected copy's list): [15] is Bałaban, "The variational problem and background fields in renormalization group method for lattice gauge theories", CMP 102 (1985) 277–309. p.380 cites "Theorem 1 [15]" only for the factor of χ_j^c(P_j), together with (71) [16].
- *Citations of (1.76).* In the LFR II transcription, (1.76) is cited on pp.383, 385 and 386 only. p.383 is the domain class of the sup; p.385 is the step j = 1; p.386, (1.84), is the later steps.
- *Citations of LFR I (1.9).* LFR I (1.9) (p.178) is cited by number on pp.179, 183 and 187 only. p.185 uses these functions through (1.29), without the number ((3) S1; rd2 m8).

**(1) it1-c2-place (§3c(2)).**
- *S1 (ι_ξ):* derived in §3c(2)(e). As corrected in round 4 (c2-r2 S-A): on the support of χ₁ζχ_{ξ,e} at admissible pairs, ι_ξ = 1, so it is omitted from T₁. The earlier placement as a product of far-row indicators in χ(Ω₁∩Λ₁ᶜ,S₁) is withdrawn, since those indicators depend on V through U₁.
- *S2 (p₀):* the source is CRE p.246 l.15, together with LFR II p.387 ((0)). §3c(4′) and (4‴) are corrected. V3 L2470 uses the same p.246 condition.
- *S3:* repaired in §3c(2)(a). The rows of z^{(0)} off Λ₁ are factors of the T₁-integrand, of total size ≤ exp(2Cd|Z₁∩Ω₁|). That is the kind of factor LFR II p.383 has, exp O(1)|Z_j∩Ω_j|. There is no 𝐁₁ placement.
- *Minors:* repaired in §3c(2).

**(2) it1-c4t-ii (§3c(4‴)).**
- *R1: reading R-d is replaced by R-d″, a bound derived at the labelled configuration (round 6: the Hölder route and the use of (1.79) at Λ are withdrawn, d2 S1, m10).*
  > **R-d″ (restated after review round 6, d2 S1 and m1–m12; derived under reading R-c, with R-p (location checked; rates quoted from p.380 (step k ≥ N + 1); rd5-d2-r3 m3) and V3's logged readings (B1)(iii) and (H4) (R-q₀ quoted and checked, recorded, not used); the layer clause of R-q withdrawn after rd5-dbq S1; dbq-r2 m-b).** Let 𝒲 be the set of cubes of the partition of CRE (1.18) (side L²M₂R₁ in fine units, i.e. LM₂R₁-cubes of T_{L⁻¹}) that contain the initial site of a bad bond of the label, and ℛ the set of cubes of R₁ (CRE (1.18)). Λ = Λ^fin, with the enlarged retreat 𝒬⁺. Let g₀ be small enough for the thresholds of (D-b), (D-b⁺) and (D1⁺) (ℓ > (8/3)(s_𝔓 + 4), R_ϑ + 2ρ ≤ ℓ/2, R_ϑ + ρ + s_𝔓 + 5 ≤ L²M₂R₁, 4c_hθ₁ ≤ 1 (so |Ψ_ξ − id|_σ ≤ r/2 on S₁*, (D1⁺) *Variables*), μ̂′ < τ_L/2 and max(1,c_L)μ̂′ < γ_L/4 ((D-b⁺); rd5-dbq S1, m6), δ₀ ≤ δ_G (V3 boundary-bijection lemma, L549; δ₀ = (A₁/A₀)ε₀ → 0; dbq-r2 m-d)), for β₀ ≤ 1 in CRE (2.7), and for ½c₄ϑ²A₁²(log g₁⁻²)^{p₀} ≥ 2 (d2 m8; to be added to V3's list, L3973, in the overhaul).
  > - (i) *Pointwise.* On the support of the bad tests, of χ^{(0)c}(R₁) and of the cutoffs (1.19) and box factors on the bonds ∂P_X, every component form satisfies Q_X(x) ≥ 2c_bϑ²r²|W_X|, with c_b := γ_L/(16c_σ²). W_X holds one witness bond for each bad cube and each R₁ cube of X, and |W_X| ≥ |𝒲_X| + |ℛ_X|/(2·5^d) ((D1), (D1⁺)).
  > - (ii) *Per component, as the j = 1 factor of (1.79) (restated after rd5-d2-r2 S1, repair (i)).* Let k ≥ N + 1 be a step at which T′_k acts on a component X_k of the step-k region Z (LFR I p.177 (ii): no component qualifies at k ≤ N), and let 𝒳 be a component of Z₁ = Λᶜ in X_k. T₁′(𝒳) denotes the j = 1 part of T′_k(X_k) on 𝒳 ((D2) *Setting*). Then T₁′(𝒳,(U,0))(label tests) ≤ exp{O(1)M^dR₁^{d+1}(d₁′(𝒳)+1)} · sup Π_G exp(−½c₄ϑ²a(d₁′(G)+1) − 2p₀(g₁)). Here G runs over the components in 𝒳 of the MR₁-cube cover of P₁ ∪ Q₁ ∪ R₁ ∪ W₁ (Minor 4), a := A₁²p₀²(g₁), c₄ := ½min{γ₀m_A, c_b/(4·10^d)} (rd5-d2-r4 m-2) and m_A := ¼min{½B₃⁻²A₀²A₁⁻², 2} ((D2); the ¼ absorbs the index change of rd5-d2 M2). The sup runs over the domain data P₁, Q₁, R₁, S₁ in 𝒳, as in (1.79); the count of these data is in the first factor ((j)), and the p.385 step removes the dependence (rd5-d2 M-sup). This is the j = 1 factor of (1.79) for T′_k(X_k), with the cover of P₁ ∪ Q₁ ∪ R₁ ∪ W₁ in place of p.380's cover of P₁ ∪ Q₁ ∪ R₁; its consumers are (1.82) and the κ induction of pp.384–386.
  > - *Status of (ii) (after rd5-d2-r3 S1).* OPEN: it depends on two D2 items. (a) D2.7: LFR I's construction of Z and of the domains Ω_hᶜ, Ω″_{h+1}, Z″_{h+2} and the preliminary-integration data from Z_h, after LFR I p.187, with Z₁ = Λᶜ among the step-1 data. (b) The acceptance item: the acceptance by CRE's steps 2, …, h, and by the R-operations acting before step k, of the step-1 data (Ω₁, Λ₁, Λ) made by the retreat, including p.256's "other conditions" (§3c(4′), (4⁗)); through it T_h(Z_h ∩ X_k) contains T₁^{Λ₁,Λ}. For the small-field objects of CRE Sect. 3, (b) is derived in D2 file D2.2(3)(b) (not reviewed); the large-field objects and the 𝐑-terms remain (D2 file D2.2(3)(c), D2.7). Everything else in (ii) is derived in (D2) under reading R-c, with R-p (location checked; rates quoted from p.380 (step k ≥ N + 1)). (i) is derived.
  > - Notation. c_σ := sup_{X≠0}|X|_σ/h(X) ≤ √N (V3 L2272). p₀(g) := (log g⁻²)^{p₀}, as p.381's display requires: its ½B₃⁻²A₀² is (B₃⁻¹ε_j/g_j)²/2 with ε_j = g_jA₀(log g_j⁻²)^{p₀} (CRE (2.4), which writes p₀(g) for A₀(log g⁻²)^{p₀}; the factor A₀ changes no conclusion, d2 m6). So a = A₁²(log g₁⁻²)^{2p₀}. 𝒳 is the argument of T₁′, and X ranges over the components of Ω₁∩Λᶜ in 𝒳, the blocks of (2.21) (d2 m9). The component of the step-k region Z on which T′_k acts, X in LFR's notation, is written X_k (rd5-d2-r4 m-5). Bad bonds in one cube count once.
  - *Status (round 6 read 22 Oct by 11:36, date; repairs 11:36–12:04; R-p/R-q source check after 12:26, by 12:43; round-7 repairs (rd5-dbq S1, m1–m10) 14:11–14:24; reviewed in it1-rd5-dbq-20261022-r2, no fatal or serious finding, its minors m-a to m-g and note n-3 applied after 15:25; dbq-r2 m-c).*
    - Round 6 (it1-rd4-d2-20261022-r1) found nothing fatal. Its S1: the first Hölder factor applied the printed (1.79) at Λ outside its printed scope. Three things were used beyond R-c: p.383 l.46 restricts the sup to domains satisfying (1.76), which Λᶜ violates; (1.71) was taken at the labelled configuration; and the positivity steps of pp.380 and 383 were applied to the (2.21) forms at Λ.
    - Repair: (D2) below uses neither (1.79) nor Hölder's inequality. It checks pp.379–383 step by step at Λ ((D2) *Check*) and bounds the labelled integral factor by factor. The R₁-factor is derived at Λ together with the bad-cube factor ((D-b⁺), (D1⁺)).
    - (i) for the bad cubes was reviewed in it1-rd3-pw-20261022-r1: correct, every inequality hand-checked. It uses CRE p.248's positivity, qualitatively only, and V3's local gap extended to the neighbourhoods of the bad bonds ((D-b)). No lower bound of the T₁ form on 𝔤^J is used, so V3 Remark c5-2-2 still stands. Its extension to the R₁ cubes ((D-b⁺), (D1⁺)) was reviewed in it1-rd5-dbq-20261022-r1 (S1, m1–m10); the repairs are reviewed in r2 (dbq-r2 m-c).
    - Round 8 for (D2) (it1-rd5-d2-20261022-r2, session local_1f85bb2c, claude-opus-5-5; read 22 Oct after 15:21, date): nothing fatal. S1: after the T′ correction (T′_k acts on no component at k ≤ N, which (l) settles), p.380's P₁/Q₁ rates are printed for the j = 1 factor inside T′_k, k ≥ N + 1, and (D2) had applied them to CRE's step-1 integral; the link to (1.79) was not drawn. Repaired after 15:25 by its repair (i): R-d″(ii) and (D2) are restated as the j = 1 factor of (1.79) at step k ≥ N + 1 (P₁/Q₁ from p.380 in its printed scope, source (1.48) on pp.366–368; R₁ and the bad cubes from (D1)/(D1⁺) inside T_h(Z_h ∩ X_k)); R-d″(ii)'s status names the open D2.7 item (now two items, with the acceptance item; rd5-d2-r3 S1). Minors m1–m6, m8–m16 applied (m7 lapses under repair (i); m14 settled by reading [III] = CRE (2.47)–(2.48), p.264, instead of a reading label). Not re-reviewed.
    - Round 9 for (D2) (it1-rd5-d2-20261022-r3; read 22 Oct by 16:55, date): nothing fatal. S1: R-d″(ii)'s status omitted the acceptance item, and "carried unchanged (p.356 l.16–18)" overread p.356, which covers LFR II §1 only. Repaired 17:38–17:43 (date): the status names both D2 items; the two citations read "left unchanged by LFR II §1 (p.356 l.16–18) and a factor of (1.71) (pp.378–379)"; the consumers and the gaps block name both items. m1–m6, m8 applied; m4 with the full p.264 quotation; m5 against LFR II p.368 l.37–39; m7 lapses (RG1 p.257 l.15–19: the linear size uses Euclidean tree length). m9: CRE p.246, pp.256–259, p.264; LFR II pp.383–386; RG1 p.257; V3 L549 go into the next packet. Round 10's packet supplied only p.264, RG1 p.257 and V3's radius lines (rd5-d2-r4 m-3); CRE p.246 and pp.256–259, LFR II pp.383–386 and V3 L549 go into the round-11 packet, and p.384 l.33 is no longer used. Not re-reviewed.
    - Reading now used: R-c only (CRE's step-1 construction at Λ, §3c(4″)). V3's logged readings used at their status (rd5-dbq S1, m9): (B1)(iii) (U₁ lies in the support of every characteristic factor of (1.11), and p.247's bound applies to U₁; used in (B-q)) and (H4) with (B3)(iii) (the constants B₃, δ and the O(1), O(L²) of pp.247–251 do not depend on g₀; used in (B-q), (D-b⁺), (D1⁺)). Also used: CRE (2.8), first line with n = 1, m = 0, ε₁ ≤ (1+β₀)ε₀. R-p: location checked; rates quoted from p.380 (step k ≥ N + 1) (p.380's P₁- and Q₁-factors come from the action and backgrounds on plaquettes in Ω₁ᶜ; UV3 (70)–(71), CRE pp.245–248; (D2) *Check* (c); rd5-d2-r2 m2). Quoted and checked: R-q₀ (CRE p.250's comparison of U₁ and U_{1,□′} on every cube of Ω₁^{∼−1}; not used after the repair). Both were listed as readings at 12:24, before the sources were checked; their status lines were written after 12:24, after the repairs of 11:36–12:04 (rd5-dbq m8). R-q's clause for the cubes of Ω₁∖Ω₁^{∼−1} was a reading presented as quoted and is withdrawn (rd5-dbq S1, read 22 Oct after 14:03); (B-q) replaces it. R-s stays withdrawn (rd3-rs S1), and the comparison with Λ₁ stays withdrawn (rd3-rs S2).
    - Citation check (l), closed after 13:17 (22 Oct, date; not reviewed): on pp.356–379 the step-1 Λ-data, the only step-1 data that (P) changes, enter only through T_h(Z_h ∩ X_k) (R-c) and through the domain-data sums whose geometry is (1.76) ((l), corrected after rd5-d2-r2 m1; rd5-d2-r3 m1). At k = 1, T′_k acts on no component: LFR I p.177 (ii) admits only components in which no region was created in the preceding N steps, and T′_k contains T_h, h = k − N (p.178 l.11). The 13:17 wording "no k = 1 T′ is printed" was wrong (corrected 13:26). The object (D2) bounds is the j = 1 part of T′_k(X_k) on 𝒳 at the labelled configuration; the step-k B-integral of (1.71) is part of T′_k(X_k) and is bounded as printed ((h); rd5-d2-r3 m1). Left: D2.7 and the acceptance item (R-d″(ii)'s status; rd5-d2-r4 m-1(b)).
    - Round 4 (rd2 S1) found the earlier, undecomposed form of R-d″ not printed: p.380 states the factor only for CRE's own R_j-cubes at threshold δ_j, and no transcribed page of LFR I, LFR II, CRE or UV3 gives that bound or its proof (searched 22 Oct; LFR I again at 09:35). The derivation below replaces that form. The sentences "the threshold enters only through |A(b)| ≥ t" and "p.380 l.43–48 is their only source" stay withdrawn.
  - *Derivation (22 Oct, after the user's "2(a)" at 08:57; written by 09:39).*
    - (D0) *Setting.* x denotes the T₁^Λ variables on J(Λ) = Ω₁*∖D(Λ), in the variables of (1.15); Ψ_ξ is the identity off S₁*. (D1) uses only bonds far from S₁*; (D1⁺) treats the bonds of S₁* near R₁. H := H_ξ on 𝔤^{Ω₁*}, and Q_Λ(x) := min_y⟨(y,x),H(y,x)⟩. (2.21) keeps the component blocks ((4″)): the form of a component X is Q_X(x) := Q_Λ(x⁰), with x⁰ = x on X and 0 elsewhere. γ := γ_L/2, ρ := ρ_L = 4L, μ := μ_H = γ_L/(8Lm_L).
    - (D-a) *H ≥ 0 on 𝔤^{Ω₁*} (quoted, with a derived chart step).* The critical point of (1.12) "is a minimum of (1.12), with a strictly positive second order differential" (CRE p.248, Theorem 1 [15]). VAR p.299's "positive definite" is for VAR's functional on its own gauge slice and supports Theorem 1 [15] only (rd3-pw m6). V3 (regular-covariance-hessian) gives ⟨B,HB⟩ = D²(S+𝒢)(0)[a,a] − DS(0)[h_UD²𝒩_U(0)[a,a]], the second derivative along V3's chart B ↦ exp(iq_{U₁}(B))U₁ of the constraint set of (1.12). The chart step: with a = g₀𝖢_UB, D̃(0) = 0 and DD̃(0) = 0 (Lemma row-locality), so D²q_U(0)[B,B] = −g₀²h_UD²𝒩_U(0)[a,a]; and D𝒢(0) = 0, since 𝒢 ≥ 0 and 𝒢(0) = 0 (rd3-pw m10). At a constrained critical point the second derivative along a parametrisation is the intrinsic second differential, so H ≥ 0 (indeed > 0). V3 L388 identifies H with CRE's C*Δ₁C of (1.15). Only H ≥ 0 is used; no constant. V3 inputs at their stated status: (B1)(iii) (U₁ is the critical point of (1.12) in the domain of (1.11)) and (H4) (rows with one block off Ω₁) (rd3-pw m12).
    - (D-b) *Local gap near I.* Let P ⊂ Ω₁* have all its bonds within ℓ/2 of I. Then (γ_L/2)id ≤ H_PP ≤ m_L id, every row b within ℓ/2 of I has Σ_{b′∈Ω₁*}‖H_{bb′}‖ ≤ m_L, and ‖H_PP⁻¹(b,b′)‖ ≤ γ⁻¹e^{−μd(b,b′)}.
      - The proof is V3's proof of Lemma regular-bounds (L3650–3677) with I replaced by P. It uses supp B ⊂ I in three places, and each transfers (rd3-pw m5): to place each patch 𝔓_w within s_𝔓 + 1 of supp B, where Lemma c2-plaquette-deviation applies; for the entry stencils, which lie within 3L of b and so in Ω₁, as dist(Λ₁, Ω₁ᶜ) ≥ 2ℓ; and for the rectangle 𝔓_{z(b)} of each row b, within s_𝔓 + 1 of b.
      - That lemma's proof needs only that the cube of the initial site of each bond lies within LMR₁ − 1 of Λ₁ (its use of collar coverage (i), L674). This holds within ℓ/2 + s_𝔓 + 2 of I once 5ℓ/8 + s_𝔓 + 3 < ℓ − 1, i.e. ℓ > (8/3)(s_𝔓 + 4), since L²M₂R₁ ≤ ℓ/8 (Lemma c5-2-4); a g₀ threshold (rd3-pw m3).
      - The flat gap (covariance-uniform-gap) holds on the whole free space, and Lemma c2-regional-entry holds on all of Ω₁*.
      - The decay is V3 Lemma c5-1-1, whose proof uses only the two-sided bound and the range ρ.
    - (D-c) *Localisation lemma.* Let W ⊂ P ⊂ Ω₁* with every bond of Ω₁*∖P at distance > R from W, and ∂P := {b ∉ P : d(b,P) ≤ ρ}. Suppose H ≥ 0 ((D-a)), H has entry range ρ ((I1)), γ ≤ H_PP ≤ m_L, with row sums ≤ m_L on the rows of P ∪ ∂P, and ‖H_PP⁻¹(b,b′)‖ ≤ γ⁻¹e^{−μd(b,b′)} (Lemma c5-1-1, from the two-sided bound and the range) (rd3-pw m4). Then, for every z ∈ 𝔤^{Ω₁*},
      ⟨z,Hz⟩ ≥ (γ/2)|z_W|² − γσ(R−ρ)²m_L²|z_{∂P}|², with σ(T) := γ⁻¹Σ_{t≥T}32(2t+1)³e^{−μt}.
      - Put u := −H_PP⁻¹H_{P,Pᶜ}z_{Pᶜ} and w := z_P − u. Completing the square, ⟨z,Hz⟩ = ⟨w,H_PPw⟩ + ⟨z_{Pᶜ},Sz_{Pᶜ}⟩ with S := H_{PᶜPᶜ} − H_{PᶜP}H_PP⁻¹H_{PPᶜ}.
      - S ≥ 0: ⟨v,Sv⟩ is ⟨·,H·⟩ at (−H_PP⁻¹H_{PPᶜ}v, v), which is ≥ 0 by (D-a). So ⟨z,Hz⟩ ≥ γ|w_W|² ≥ γ(½|z_W|² − |u_W|²).
      - f := H_{P,Pᶜ}z_{Pᶜ} depends on z_{∂P} only, and Schur's test gives |f| ≤ m_L|z_{∂P}|. It is supported on bonds of P within ρ of Pᶜ, at distance ≥ R − ρ from W.
      - At most 32(2t+1)³ bonds have initial site at ℓ^∞ distance t from a given one. So the block (H_PP⁻¹)_{W,supp f} has row and column sums ≤ σ(R−ρ), and |u_W| ≤ σ(R−ρ)m_L|z_{∂P}|. ∎
    - (D-d) *Choice of R.* Let c_□ := sup_{X≠0}h(X)/|X|, for the norm |·| of the box of (1.25). That box is V3's Θ^σ (L2260, L676; rd5-dbq m3), so |·| = |·|_σ ≥ h and c_□ ≤ 1 (the name c_h is V3's for the reciprocal ratio, rd3-pw m2). Let N(R) := 4(2R+2ρ+1)⁴, which bounds the number of bonds within R + ρ of a bond, and R_ϑ the least integer R > ρ with σ(R−ρ)²m_L²c_□²(4C_n+1)²N(R) ≤ ϑ²/(4c_σ²), with C_n of (D1⁺). The factor (4C_n+1)² (it was (3C_n+1)² before rd5-dbq S1) covers the boundary data near R₁; near I they are below r (round 6). R_ϑ depends on ϑ, L and the group only, since σ decays exponentially.
    - (D1) *The pointwise bound.* Fix a labelled term with Λ = Λ^fin. For each □′ ∈ 𝒲 choose one bad bond e(□′) with initial site in □′. Distinct cubes give distinct bonds. For a component X, let W_X be the chosen bonds in X, 𝒲_X their cubes, and P_X the bonds of Ω₁* within R_ϑ of W_X.
      - Geometry: a bad bond e is a collar bond of some Λ^{(k)}, so d(e,I) ≤ d(e,D(Λ^{(k)})) ≤ ρ, since D(Λ^{(k)}) ⊂ I. With 𝒬⁺, d(e,Λ) ≥ ℓ ((4⁗)(c)(α)). So P_X ∪ ∂P_X lies within R_ϑ + 2ρ of I, at distance ≥ ℓ − 1 − R_ϑ − ρ from D(Λ) and ≥ ℓ − 2 − R_ϑ − 2ρ from S₁*. For small g₀ (ℓ → ∞), (D-b) applies, and P_X ∪ ∂P_X ⊂ J(Λ) avoids S₁*.
      - Boxes: every b ∈ ∂P_X has |x(b)| < r. For b ∈ J, b lies in 𝒢_ξ (the argument of collar coverage (i), L674, at distance ≤ R_ϑ + 2ρ < ℓ/2 from I), where (1.25) contains 1{|A(b)| < r} (L676). For b ∈ I∖D(Λ) it is the retained box (Lemma c5-2-5).
      - Apply (D-c) to z* := (y*(x⁰), x⁰), the minimiser of Q_X(x). Since (P_X ∪ ∂P_X) ∩ D(Λ) = ∅, z*_{W_X} = x_{W_X}, and z*_{∂P_X} is x on ∂P_X ∩ X and 0 elsewhere.
      - On the support of the bad tests and of the T₁^Λ cutoffs on ∂P_X (rd3-pw m7), h(x(e)) ≥ |x(e)|_σ/c_σ ≥ ϑr/c_σ for e ∈ W_X, and |z*_{∂P_X}|² ≤ c_□²r²N(R_ϑ)|W_X|. By (D-d), Q_X(x) ≥ (γ/4)|x_{W_X}|² ≥ 2c_bϑ²r²|𝒲_X|, with c_b := γ_L/(16c_σ²).
    - (D-b⁺) *Local gap near R₁ (added after round 6, for the R₁ witnesses of (D1⁺)).*
      - *R-q₀ (quoted and checked, 22 Oct; restricted to Ω₁^{∼−1} after rd5-dbq S1).* R-q₀ is the bound |U₁U_{1,□′}⁻¹ − 1| < O(1)B₃exp(−δLM₂R₁)ε₁ on the bonds of □′^{∼2}, for every L²M₂R₁-cube □′ ⊂ Ω₁^{∼−1}.
        - Printed: CRE p.250, the sentences after (1.18)–(1.19). The sum (1.18) is over R₁ ⊂ Ω₁^{∼−1}, and R₁ᶜ is the complement in Ω₁^{∼−1}. For each cube □′ ⊂ R₁ᶜ the page states the bound, for two reasons: □′^{∼4} ⊂ Ω₁, and U₁ and U_{1,□′} are determined by the same V on □′^{∼3}. U_{1,□′} depends on V on □′^{∼4} only (p.246), and U₁ = U₁(Ω₁, V, V₀) ((1.12)); neither depends on A or R₁ (rd5-dbq m1). The term R₁ = ∅ of (1.18) therefore gives the bound for every cube of Ω₁^{∼−1}. V3's (B3)(iii) (L3597) is the same printed bound on the good cubes.
        - Withdrawn (rd5-dbq S1): the clause for the cubes □′ ⊂ Ω₁∖Ω₁^{∼−1} with □′^{∼4} ⊂ Ω₁, argued by "the printed step applies to it unchanged". p.250 prints the bound for cubes of Ω₁^{∼−1} only, and the derivation behind it is not on the page, so that sentence asserted the scope of an unseen derivation. V3 Remark c5-2-2's conclusion stands (no lower bound for S on 𝔤^J is used). Its (ii) holds for the p.250-size comparison only (size e^{−δLM₂R₁}ε₁, not printed on the layer); at size O(L²)ε₀, (B1)(ii)–(iii) supply the comparison on every cube of Ω₁, and (D-b⁺) supplies the near-flat gauge on cubes with □′^{∼4} ⊂ Ω₁. The parenthesis (□′^{∼4}⊄Ω₁) holds only for the outer layer cubes. To be reconciled in V3 at the overhaul (dbq-r2 m-e).
      - *(B-q) The comparison on every cube of Ω₁ (from V3's logged reading (B1)(iii); no new reading; rd5-dbq S1(b)).* Let □′ ⊂ Ω₁ be an L²M₂R₁-cube.
        - (a) |U₁(b)U_{1,□′}(b)⁻¹ − 1| < 2δ₀ for every b ∈ (□′^{∼2})*. By (B1)(iii), U₁ lies in the support of every characteristic factor of (1.11). Among them is χ₀′(Ω₁) = Π_{□′⊂Ω₁}1{sup_{b∈(□′^{∼2})*}|UU_{1,□′}⁻¹(b) − 1| < 2δ₀} ((1.8), p.247; (1.11), p.248). V3 derives the same inequality at b ∈ S₁* in the proof of its boundary-bijection lemma (L557).
        - (b) |U₁(e)U_{1,□′}(e)⁻¹ − 1| < O(L²)ε₀ on every bond e of □′^{∼2}, the designated bonds included: p.247 applied to U₁, as (B1)(ii)–(iii) record. The O(L²) does not depend on g₀ ((H4)).
        - (a) is sharper but excludes the designated bonds b₀(c), which plaquettes may contain; so (D-b⁺) uses (b) and *Boundary data* uses (a).
      - *Statement.* Let P ⊂ Ω₁* be such that the initial site of every bond within s_𝔓 + 2 of P lies in a cube □′ with □′^{∼4} ⊂ Ω₁. Then, for g₀ below the thresholds on μ̂′ in the proof, (γ_L/2)id ≤ H_PP ≤ m_L id, every row b ∈ P has Σ_{b′∈Ω₁*}‖H_{bb′}‖ ≤ m_L, and ‖H_PP⁻¹(b,b′)‖ ≤ γ⁻¹e^{−μd(b,b′)}; the same holds for every P′ ⊂ P (dbq-r2 m-f: (D-b) states its row sums only for rows within ℓ/2 of I, and the proof below gives them for every row of P).
      - *Proof.* V3's proof of Lemma regular-bounds (L3650–3681) with I replaced by P, as in (D-b). It uses the cubes only through Lemma c2-plaquette-deviation, on the patches 𝔓_w (L3666) and on the rectangles 𝔓_{z(b)} of the rows (L3681).
        - That lemma is redone for a cube □′ with □′^{∼4} ⊂ Ω₁, in the steps of its proof (L3604). □′ ⊂ Ω₁, so the test χ₁(Ω₁) gives |U_{1,□′}(∂p′) − 1| < ε₁L⁻² for p′ ⊂ □′^∼ (rd5-dbq m10). By (B-q)(b), ‖U₁(e) − U_{1,□′}(e)‖_op ≤ c_hO(L²)ε₀ on the bonds of □′^{∼2}. Telescoping over the four bonds of p ⊂ □′^∼, ‖U₁(∂p) − 1‖_op ≤ c_hε₁L⁻² + 4c_hO(L²)ε₀ =: 2c_hε′.
        - Lemma c2-local-gauge in its general-ε form (L3618) then gives phases ≤ μ̂′ := 6c_Gc_hs_𝔓ε′. The proof of Lemma regular-bounds uses μ̂ only through μ̂ < τ_L/2 (analyticity, L3672, L3681) and through c_Lμ̂ in the gap (L3674, L3678), i.e. through the two conditions of (convex-background-thresholds) (L3633–3634; dbq-r2 m-a). With μ̂′ in place of μ̂ both are g₀-thresholds, since ε′ → 0 as g₀ → 0 (the O(L²) does not depend on g₀, (H4)).
        - The entries are local on all of Ω₁* (Lemma c2-regional-entry, stencils within 3L of b), and the flat gap holds on the whole free space.
    - (D1⁺) *R₁ witnesses (added after round 6).*
      - *Choice.* For each cube □′ of R₁, χ^{(0)c}(R₁) gives a bond of (□′^{∼2})* with |A(b)|_σ ≥ r (CRE (1.18)); choose one, e(□′), and add it to W_X for the component X of Ω₁∩Λᶜ that contains it. A bond lies in (□′^{∼2})* for at most 2·5^d cubes □′, so the R₁ cubes of X give at least |ℛ_X|/(2·5^d) distinct bonds.
      - *Placement.* R₁′ ⊃ R₁ is at distance ≥ LMR₁ = ℓ from Λ₁ ⊃ Λ (V3 Lemma collar-coverage (i)). So e(□′) is at distance ≥ ℓ − 2L²M₂R₁ − 1 ≥ (3/4)ℓ − 1 from D(Λ), and it differs from the bad witnesses, which lie within ρ of I. For small g₀, (P_X ∪ ∂P_X) ∩ D(Λ) = ∅.
      - *(D-b⁺) applies.* A bond within s_𝔓 + 2 of P_X ∪ ∂P_X near e(□′) lies within 2L²M₂R₁ + R_ϑ + ρ + s_𝔓 + 3 of □′ ⊂ Ω₁^{∼−1}. Its cube □″ then has □″^{∼4} within 7L²M₂R₁ + R_ϑ + ρ + s_𝔓 + 3 ≤ LMR₁ − 2 of Ω₁^{∼−1}, by the threshold R_ϑ + ρ + s_𝔓 + 5 ≤ L²M₂R₁ and LMR₁ ≥ 8L²M₂R₁ (M ≥ 8LM₂). Points within LMR₁ − 2 of Ω₁^{∼−1} = ((Ω₁ᶜ)^∼)ᶜ lie in Ω₁. So □″^{∼4} ⊂ Ω₁. Near I the cubes are good, so □′^{∼4} ⊂ Ω₁ there as well. Hence the hypothesis of (D-b⁺) holds on all of P_X ∪ ∂P_X, and (D-b⁺) is applied to that set; (D-b) is its special case (rd5-dbq m4).
      - *Variables.* Ψ_ξ differs from the identity only on S₁* (CRE (1.21)–(1.22); V3 L678); elsewhere A = A′ (rd5-dbq m5). On S₁* the T-variable is A′ of CRE (1.22), and A = Ψ_ξ(A′).
        - V3's boundary-bijection lemma (L549–557) writes, for b ∈ S₁*, e^{ig₀A(b)} = e^{ig₀A′(b)}W_b with W_b = e^{−iω̃𝐇_{1,Ax}(b)} and |W_b − 1| ≤ |𝐇_{1,Ax}(b)|. Its (a) and the bound |Z_b − 1| < 2δ₀ in its proof give |e^{ig₀A(b)} − 1| < 4δ₀ on the support.
        - CRE p.251 gives |𝐇_{1,Ax}| < O(1)B₃exp(−δMR₁)ε₁ ≤ θ₁δ₀, with θ₁ := O(1)B₃e^{−δMR₁}(1+β₀)A₀/A₁, by CRE (2.8) (first line, n = 1, m = 0: ε₁ ≤ (1+β₀)ε₀) and δ₀ = (A₁/A₀)ε₀ (p.247). θ₁ → 0 as g₀ → 0, since the constants do not depend on g₀ ((H4)) and R₁ → ∞ (rd5-dbq m6, m9). So |e^{ig₀A′(b)} − 1| < 5δ₀ once θ₁ ≤ 1.
        - Both g₀A(b) and g₀A′(b) lie in the chart ball h < ϱ_G (V3 L557(a) and the domain 𝒲_b), where ‖X‖_op < π (V3 L252). So |X| ≤ (π/2)|e^{iX} − 1| < 8δ₀ for both, in the cutoff norm (V3 L557, norm facts). On {|X| ≤ 12δ₀}, |X − X′| ≤ 2|e^{iX} − e^{iX′}| (same place), and |e^{ig₀A} − e^{ig₀A′}| = |W_b − 1| ≤ θ₁δ₀. Hence |A − A′| ≤ 2θ₁r. Since |·|_σ ≤ c_hh and h is at most the cutoff norm, |A − A′|_σ ≤ 2c_hθ₁r ≤ r/2 once 4c_hθ₁ ≤ 1, a g₀-threshold.
        - Whether the form is written at Ψ_ξ(A′) or at A′ with the difference in V^{(0)}(S₁) ((4″)), the witness and boundary bounds below hold for its argument.
      - *Boundary data near R₁.* Let b ∈ ∂P_X near e(□′), and let □″ be the cube of b₋ (□″^{∼4} ⊂ Ω₁ by the above).
        - If □″ ⊂ Ω₁^{∼−1}∖R₁, the first factor of (1.19) gives |A(b)|_σ < r.
        - Otherwise □″ ⊂ R₁ or □″ ⊂ Ω₁∖Ω₁^{∼−1}, and the second factor of (1.19) is retained (p.250, the sentence after (1.19)): |e^{ig₀A(b)}W − 1| < 2δ₀ with W := U₁(b)U_{1,□″}⁻¹(b). b ∈ Ω₁* has its initial site in □″ and is not designated, so b ∈ (□″^{∼2})*, and |W − 1| < 2δ₀ by (B-q)(a) (rd5-dbq S1(b); R-q is no longer used). For a unitarily invariant norm, |e^{ig₀A} − 1| ≤ |e^{ig₀A}W − 1| + |W − 1| < 4δ₀.
        - g₀A(b) lies in the chart ball h < ϱ_G: A is the scaled chart logarithm of U′ (CRE (1.13), p.248; the scaling A = g₀A′ is (1.15), p.249; V3 L557(a); dbq-r2 n-3). There ‖X‖_op < π (V3 L252), so |g₀A(b)| ≤ (π/2)|e^{ig₀A(b)} − 1| (V3 L557, norm facts) and |g₀A(b)|_σ ≤ 4C_nδ₀ with C_n := (π/2)c_h, a group constant (rd5-dbq m7). So |A(b)|_σ ≤ 4C_nr.
        - With |Ψ_ξ − id|_σ ≤ r/2, the form's argument is at most r_∂ := (4C_n + 1)r on ∂P_X. On the witnesses it is at least r/2 ≥ ϑr.
      - *Conclusion.* Apply (D-c) as in (D1), with W_X now holding the bad and the R₁ witnesses and P_X the bonds of Ω₁* within R_ϑ of W_X. Then z*_{W_X} = x_{W_X}, |z*_{∂P_X}|² ≤ c_□²r_∂²N(R_ϑ)|W_X|, and by (D-d), Q_X(x) ≥ (γ/4)|x_{W_X}|² ≥ 2c_bϑ²r²|W_X|. Its support conditions are the bad tests, χ^{(0)c}(R₁) and the cutoffs (1.19) and box factors on ∂P_X, all factors of the integrand. (D1) is the case ℛ_X = ∅.
    - (D2) *The labelled integral, factor by factor (rewritten after round 6, d2 S1; the Hölder route and the use of (1.79) at Λ are withdrawn; restated after rd5-d2-r2 S1 as the j = 1 factor of (1.79) at step k ≥ N + 1, repair (i); the revision times are in the status line of R1).*
      - *Setting (restated after rd5-d2-r2 S1, repair (i)).* Fix a labelled term with Λ = Λ^fin. The step-1 large-field functions are integrated only inside an R-operation: T′_k acts on a component X_k of the step-k region Z only at steps k ≥ N + 1 ((l)), and the step-1 functions reach it inside T_h(Z_h ∩ X_k), h = k − N, left unchanged by LFR II §1 (p.356 l.16–18) and a factor of (1.71) (pp.378–379); that it contains T₁^{Λ₁,Λ} at Λ is the acceptance item of R-d″(ii)'s status (rd5-d2-r3 S1). Fix such k and X, and a component 𝒳 of Z₁ = Λᶜ in X_k. T₁′(𝒳) denotes the j = 1 part of T′_k(X_k) on 𝒳: the integral over the step-1 variables in 𝒳 at fixed values of all other variables of (1.71). The bound below is uniform in them, and since the integrand is ≥ 0 (below) it enters the bound of T′_k(X_k) as a factor, as p.380 extracts its factors per configuration. This decomposition is the note's own; (1.79), p.383, is not in the packets so far (rd5-d2-r3 m6). Its measure μ: the A-integrals over the step-1 T-variables on J(Λ) ∩ 𝒳, the V₀-integrals with δ(V̄₀V⁻¹), and the sums over the step-1 domain data in 𝒳, Σ_{S₁} included (§3c(4⁗)(d); d2 m4). Its integrand (rd5-d2-r2 m6) is the label tests times the j = 1 factors that p.380 l.32–48 extracts:
        - the step-1 forms at Λ, e^{−½Σ_XQ_X}, with the step-1 tests χ^{(0)c}(R₁), the cutoffs (1.19) and the box factors on ∂P_X, carried in T_h(Z_h ∩ X_k);
        - the step-k Wilson term (1.48) (pp.366, 368) on the plaquettes near P₁ ∪ Q₁, with the step-1 tests χ₁^c(P₁), χ₀′^c(Q₁) of ζ(Ω₁ᶜ) (1.11) and their gauge-fixing factors;
        - the step-1 parts of V(X^∼), of the vacuum counterterms and of the normalisation constants ((b)), and the z^{(0)} rows off Λ ((k)).
        By (1.73), |T′_k(X_k,(U,J))F| ≤ sup e^{|σ|}·T′_k(X_k,(U,0))|F|, and the density is positive at J = 0 (p.379 l.38; rd3-rs m9). So it suffices to bound T₁′(𝒳,(U,0)) applied to the label tests; the integrand is ≥ 0. The B-integral of (1.71), over the step-k field V′ = exp ig_kB (p.360 l.42–44), is part of T′_k(X_k) and is bounded as printed ((h)); it is not a j = 1 factor.
      - *Check of pp.379–383 at Λ (d2 S1, repair items 1–2).* The steps of the proof of (1.79), for the factors j = 1 inside T′_k(X_k), k ≥ N + 1 (rd5-d2-r3 m2), and what each uses of the configuration:
        - (a) p.379 l.28–p.380 l.24, (1.73)–(1.75): reduction to J = 0, by positivity of the density at the real configuration. Per configuration.
        - (b) p.380 l.26–29: V(X^∼) by (1.69), the vacuum counterterms and the normalisation constants, in modulus; each large-field domain Z_j contributes O(1)log g_j⁻²|Z_j| ≤ O(1)M^dR_j^{d+1}d_j′(Z_j). Their step-1 parts are CRE's step-1 terms at Λ (𝐄^{(1)}(Λ), V^{(0)}, the 𝐁-terms; rd5-d2-r2 m5), made by CRE's construction at Λ (R-c). p.377 l.3–4 bounds the corresponding sum "similar to the bound (2.48) [III] for the sum of the boundary terms"; [III] is CRE (LFR II p.392), and CRE (2.47)–(2.48), p.264, print |𝐁^{(j,n)}| ≤ B₁2^{−(j−n)}|Γ_n| for j > n, the same with |Γ_n∖Λ_k⁰| for j = n, and |(2.40)| ≤ 2B₁(Σ_{n=1}^{k−1}|Γ_n| + |Γ_k∖Λ_k⁰|) ≤ 2B₁Σ_{n=1}^k|Γ_n|, with Γ_n = Ω_n^{(n)}∖Ω_{n+1}^{(n)} for 1 ≤ n ≤ k−1 and Γ_k = Ω_k^{(k)} (p.255, (2.2)) (rd5-d2-r2 m14; quotation corrected after rd5-d2-r3 m4, now the same as §3c(4⁗)(a)). At step 1 the cost is (4⁗)(a)'s |𝐁₁| ≤ 2B₁|Ω₁^{(1)}∖Λ⁰| at Λ (R-c), in points of T^{(1)} (p.263). Since Λ ⊂ Ω₁^{∼−2}, each MR₁-cube of the layer removed from Λ to form Λ⁰ is adjacent to a cube of Z₁ ∩ Ω₁, and each cube has at most 3^d − 1 neighbours; so on 𝒳 the cost is at most 2B₁·3^d|Z₁ ∩ Ω₁ ∩ 𝒳|, absorbed in this item's factor exp(O(1)log g₁⁻²|Z₁ ∩ 𝒳|).
        - (c) p.380 l.32–43: the P₁-factor, "using Theorem 1 [15] and (71) [16]", and the Q₁-factor, "by expanding the Wilson action locally in the approximate fluctuation field, and using the positivity bound for the resulting quadratic form". These are printed for the large-field functions "introduced in the j-th step" inside T′_k, k ≥ N + 1, and are used here in that printed scope at j = 1 (rd5-d2-r2 S1, repair (i)); their source term is the step-k Wilson term (1.48), pp.366, 368. P₁ and Q₁ lie in Ω₁ᶜ, at distance ≥ 2LMR₁ from Ω₁ (CRE p.248 l.9–10), and their characteristic functions sit in ζ(Ω₁ᶜ) of (1.11) (p.248 l.24–25).
          - *R-p (location checked; rates quoted from p.380 (step k ≥ N + 1); it was listed as a reading before UV3 and CRE pp.245–248 were checked; rd5-d2-r2 m2).* R-p says both factors come from the Wilson action and the background fields on plaquettes in Ω₁ᶜ, on the support of χ₁^c(P₁)χ₀′^c(Q₁). The sources fix where each factor lives. Status: location checked; the rates are p.380's printed displays, quoted, not traced through VAR (7)/(9) and UV3 (67)–(68) (rd5-d2 M1).
            - P₁-factor: [16] = UV3 (70)–(71), p.273 l.36–56. For a large plaquette p′, the action on the four j-blocks Δ′ = B^j(x₀) ∪ … ∪ B^j(w₀) at the corners of p′ is ≥ ½g_j⁻²|V_j(∂p′) − 1|² − O(1)g_jp³(g_j) ≥ ¼p²(g_j), pointwise, for g_j small. Theorem 1 [15] (VAR p.279) gives the minimal configurations, their uniqueness and their regularity (9), for the backgrounds U_{1,□′}. At step 1 the test χ₁^c(P₁) of (1.4) (p.246) is on U_{1,□′}(V,∂p) for p ⊂ □′^∼, □′ ⊂ P₁, and U_{1,□′} depends on V on □′^{∼4} only (p.246 l.46).
            - Q₁-factor: the expansion is in the approximate fluctuation field UU_{1,□′}⁻¹, which p.247 l.34–37 defines on □′^{∼2}. The test χ₀′^c(Q₁) of (1.8) is on (□′^{∼2})*, □′ ⊂ Q₁, and U_{1,□′} again depends on V on □′^{∼4}.
            - Locality: □′^{∼4} lies within 4L²M₂R₁ of □′, and 4L²M₂R₁ < LMR₁ since M is chosen much larger than M₂ (p.245 l.37; M ≥ 8LM₂, V3 L3968; rd5-d2 M7). So all plaquettes and fields used lie within 4L²M₂R₁ of P₁ ∪ Q₁. P₁ ∪ Q₁ is at distance ≥ 2LMR₁ from Ω₁ (p.248 l.9–10), so □′^{∼4} for □′ ⊂ P₁ ∪ Q₁ is at distance ≥ LMR₁ from Ω₁ and lies in Ω₁ᶜ (rd5-d2 M3; rd5-d2-r2 m9).
            - Not used: p.380's R₁-factor; (D1⁺) derives that factor at Λ.
          - The step-1 tests χ₁^c(P₁), χ₀′^c(Q₁) and their variables (V₀ and V) are the same at Λ as at Λ₁: (P) changes only the conditional domain inside Λ₁ ⊂ Ω₁^{∼−2}, and through it the forms and 𝐄 on Ω₁. The step-k term (1.48) on these plaquettes does not involve Λ except through its domains Ω_hᶜ, Ω″_{h+1} and Z″_{h+2} (pp.364–368). p.380's displays are bounds per configuration on the support of the tests (pointwise, as in UV3 (70)–(71)), so they hold at the labelled configuration once (1.48) is formed on these domains. Their construction from Z_h, with Z₁ = Λᶜ among the step-1 data, is D2.7, the first D2 item of (l) (rd5-d2-r2 S1, repair (i); rd5-d2-r4 m-1(b)).
        - (d) p.380 l.44–48: the R₁-factor, "by the same positivity bound for the quadratic form". R₁ ⊂ Ω₁^{∼−1} lies in the T-region, so at Λ this step concerns the (2.21) forms at Λ (d2 Q4(c)). They are in T_h(Z_h ∩ X_k), which is left unchanged by LFR II §1 (p.356 l.16–18) and is a factor of (1.71) (pp.378–379); that it contains T₁^{Λ₁,Λ} at Λ is the acceptance item of R-d″(ii)'s status (rd5-d2-r3 S1). It is derived at Λ in (D1⁺), jointly with the bad cubes; this is p.380 l.44–48's location.
        - (e) p.380 l.48–p.381 l.9: the combination per component. Arithmetic; redone below for the cover with W₁.
        - (f) p.381 l.10–15, (1.76): a property of LFR II's domains. It is cited on p.383 (the domain class of the sup of (1.79)), p.385 and p.386; only the last two use it in a bound (p.385 l.17, p.386 l.7; grep of the transcription, 22 Oct; rd5-d2-r2 m10). So p.383 l.46 restricts the sup to the domains that occur and is not an input of the bounds. At Λ the modified (1.76) of Minor 4 enters on p.385 (d2 Q4(a)).
        - (g) p.381 l.16–p.383 l.29: the preparatory factors Π′, from characteristic functions ≤ 1. Not used.
        - (h) p.383 l.31–32: the group integrals ≤ 1 (normalised Haar measure under δ(V̄₀V⁻¹)). Per configuration. The line's second half, the B-form bounded below by 0 with the logarithmic constants put into the measure, concerns the step-k B-integral of T′_k(X_k), which is bounded as printed and is not a j = 1 factor (*Setting*).
        - (i) p.383 l.33–34: the A-integrals, "using the positivity properties of the quadratic forms". At Λ this is derived directly below, together with the (1.15) Jacobian (d2 m2).
        - (j) p.383 l.34–35: the sums over admissible sequences, exp O(1)(MR₁)^{−d}|Z₁|. Counting, per configuration. The label sum is counted separately (R2).
        - (k) The z^{(0)} rows off Λ (§3c(2)(a)) are a factor of the labelled integrand that CRE's does not have. They are bounded by exp(2Cd|Z₁∩Ω₁∩𝒳|) (d2 m5).
        - (l) *(1.71) and T′ (d2 Q4(b); checked against LFR II pp.356–380 and LFR I pp.177–178).*
          - Printed: T′_k(X_k) is defined at step k "for a component of Z", as the composition of the integration of (1.70) and the T_h-operation of (1.100) [IV], both localised in X (p.378 l.26–29; (1.71), p.378 l.30–p.379 l.8). Here h = k − N, and by LFR I's condition (ii) the last N one-step operations contain no large-field functions (LFR I p.178 l.11–14), with N ≥ (ν/log L)log log g_k⁻² (p.363 l.40–42). The B-integral of (1.71) is over the step-k field V′ = exp ig_kB on 𝐁₀ (p.360 l.42–44; (1.81)–(1.82) [IV]).
          - (1.71) states no range of k. The range comes from the class of components the R-operation acts on, which LFR I p.177 (i)–(ii) fixes: by (ii), "in the preceding N renormalization steps no new large field regions were created inside this component". The large-field regions of the k-th density are created in steps 1, …, k (at step 1: P₀, P₁, Q₁, R₁ of CRE §1; rd5-d2-r2 m12). Every component of Z₁ = Λᶜ contains a step-1 large-field region, so (ii) does not hold vacuously on it: each retreat cube set 𝒬(e) is connected and contains x_e, which lies outside the current region; Fill only merges or enlarges components (V3 L2414, L2430, Lemmas c5-3-0 and c5-3-1(c)); so every component of Λᶜ contains a component of 𝔅₀ = (Λ₁^{(0)})ᶜ, and each component of 𝔅₀ contains an original bad point of CRE's unfilled region Q₁′^{∼4} ∪ (B(P₁¹)ᶜ)^{∼5} ∪ R₁′^{∼1} (proof of Lemma c5-3-0(b)), which the step-1 regions generate (CRE (1.10), (1.20)). So at k = 1, and at every k ≤ N, no component satisfies (ii), and h = k − N ≤ 0 is not a step. Nothing in the definition of T′ excludes k = 1; the exclusion comes from (ii) (an earlier wording, "no k = 1 operation is printed", is withdrawn; rd5-d2-r2 m15).
          - For this reason the earlier sentence "T₁′(𝒳) at Λ is LFR's k = 1 operation at the domain Λᶜ" is withdrawn. The step-1 large-field functions reach T′_k only inside T_h(Z_h ∩ X_k), at steps k ≥ 1 + N, and p.380 l.32–48 extracts their factors for each step j. The object (D2) bounds is the j = 1 part of T′_k(X_k) on 𝒳 at the labelled configuration (*Setting*, restated after rd5-d2-r2 S1); (a)–(k) check pp.379–383's steps for j = 1 on it.
          - Uses of the step-1 data in pp.356–379: T_h(Z_h ∩ X_k), left unchanged by LFR II §1 (p.356 l.16–18) and a factor of (1.71) (pp.378–379; its content at Λ is the acceptance item, rd5-d2-r3 S1); the volume bound (1.69); the sums over the domain data in (1.71), whose geometry enters on p.385 through (1.76); the size bounds over Γ″_j in (1.47); and Ω_h in χ_{h,1/2}. Every other domain on these pages is the step-k region Z or LFR's own Λ ⊂ Z, the domain of the preliminary integrations in axial gauge, "a rectangular parallelepiped contained in a cube of the size 100M" (p.357 l.44, p.358 l.9). It is not the note's Λ.
          - So (corrected after rd5-d2-r2 m1): on pp.356–379 the step-1 Λ-data, the only step-1 data that (P) changes, enter only through T_h(Z_h ∩ X_k) (R-c) and through the domain-data sums whose geometry is (1.76). The step-1 Ω-data also enter through (1.47), (1.69), χ_{h,1/2} and the Wilson term (1.37)/(1.48) (pp.366, 368), all unchanged by (P). Ω″_j, Z″_{h+1}, Z″_{h+2}, Ω_k and 𝐁₀ are data of steps h+1, …, k. This check is closed. It leaves two D2 items on which R-d″(ii) depends (rd5-d2-r3 S1): LFR I's construction of Z and of the preliminary-integration data from Z_h, the operations after LFR I p.187 (§3f(3) S1; D2.7); and the acceptance of the retreat-made step-1 data (Ω₁, Λ₁, Λ) by CRE's steps 2, …, h and by the R-operations before step k (R-d″(ii)'s status).
      - *The bound.* On the support of the integrand:
        - χ_lab·χ^{(0)c}(R₁)·(the cutoffs (1.19) and box factors on the bonds ∂P_X, which are factors of the integrand; d2 m12)·e^{−½Σ_XQ_X} ≤ e^{−c_bϑ²r²|W|}, with W := ⋃_XW_X, by (D1) and (D1⁺). This is the only use of the forms; the remaining integrand is ≤ 1 and is integrated over |A| ≤ C_𝐠/g₀ below (rd5-d2 M6);
        - for each term of ζ(Ω₁ᶜ), the step-k Wilson term (1.48) on the plaquettes near P₁ ∪ Q₁ gives, by R-p and p.380 l.32–43 at j = 1 in its printed scope, the factor exp(−γ₀(2g₁²)⁻¹(B₃⁻¹ε₁)²(LM₂R₁)^{−d}|P₁|) = e^{−½γ₀B₃⁻²A₀²𝔭²} per cube of P₁ and exp(−½γ₀g₁⁻²(2δ₁)²(LM₂R₁)^{−2}|Q₁|) ≤ e^{−2γ₀A₁²𝔭²} per cube of Q₁, with 𝔭 := (log g₁⁻²)^{p₀} (ε₁/g₁ = A₀𝔭, δ₁/g₁ = A₁𝔭; (LM₂R₁)^{−d}|P₁| is the number of cubes, and (LM₂R₁)^{−2}|Q₁| is at least that number). These are p.380's j = 1 displays at their own indices, so no index change is needed. Both are ≥ γ₀m_Aa per cube: ½B₃⁻²A₀²𝔭² = (½B₃⁻²A₀²A₁⁻²)a ≥ m_Aa and 2a ≥ m_Aa. The ¼ in m_A, introduced for the withdrawn index change (rd5-d2 M2), is kept and is slack (rd5-d2-r2 S1, repair (i); m7 lapses with it). The P₀, P₁, Q₁ and S₁ sums are decompositions of unity, with one nonzero term at each point; their terms are bounded one at a time and counted in (j) (rd5-d2 M5). The gauge-fixing exponentials of ζ(Ω₁ᶜ) are ≤ 1 (d2 m5). Their normalisations 1/z of (1.5), σ₀ and the (1.24) Jacobian contribute at most O(log g₀⁻²) per site to the exponent. For 1/z (rd5-d2-r2 m8): by Haar invariance z = ∫dv χ(|v − 1| < ε₀)exp[−g₀⁻²(1 − Re tr v)] ((1.5), p.247; tr normalised, tr 1 = 1, so Re tr v ≤ 1; with the unnormalised trace write N − Re tr v, and nothing below changes; rd5-d2-r4 m-6), so z ≤ 1; restricting to v = e^{iX}, |X| < g₀ ≤ ε₀ (|e^{iX} − 1| ≤ |X|), where 1 − Re tr v ≤ c_tr|X|², gives z ≥ e^{−c_tr}·Haar{|X| < g₀} ≥ c g₀^{d(𝐠)} with c, c_tr depending on G only. So log(1/z) = O(log g₀⁻²). They go into (b)'s factor exp(O(1)log g₁⁻²|Z₁∩𝒳|), by the second line of CRE (2.7) (rd5-d2 M4);
        - the rest of (1.48): its Wilson action has a G-valued field, "hence the action is positive" (p.368 l.37–39), so its exponential is ≤ 1, and its O(1) terms are small (p.368 l.32, l.37), a factor ≤ e absorbed in the first factor of the bound; the remaining characteristic functions are ≤ 1 (rd5-d2-r3 m5: e^{−g₀⁻²S(U₁)} belongs to CRE's step-1 integrand (1.15), not to the *Setting* integrand, and is withdrawn here);
        - (b): exp(O(1)log g₁⁻²|Z₁∩𝒳|); (k): exp(2Cd|Z₁∩Ω₁∩𝒳|); Σ_{S₁}: at most 2^{#(L²M₂R₁-cubes of Ω₁∩Λ₁ᶜ∩𝒳)} terms (d2 m4);
        - the A-integral: each T-variable is A(b) = g₀⁻¹A′(b) with A′ = (1/i)log U′ in the principal chart (CRE (1.13), p.248), so |A(b)| ≤ C_𝐠/g₀. With the (1.15) Jacobian g₀^{d(𝐠)} per T-bond (p.249's scaling, old variable = g₀ × new variable; rd5-d2-r2 m13), the A-integral is ≤ C_𝐠^{d(𝐠)·#(T-bonds)}, and #(T-bonds) ≤ O(1)|Z₁∩Ω₁∩𝒳| (the O(1) depends on d, d(𝐠) and L, rd3-rs m10).
      - *Together.* T₁′(𝒳,(U,0))(label tests) ≤ exp{O(1)log g₁⁻²|𝒳|}·sup_{P₁,Q₁,R₁,S₁ in 𝒳}Π_{cubes of P₁∪Q₁ in 𝒳}e^{−γ₀m_Aa}·e^{−c_bϑ²r²|W|}, the sup over the domain data as in (1.79) (rd5-d2-r2 m4). By p.380 l.29, with d₁′ + 1 in place of d₁′ (#cubes ≤ 2·3^d(d₁′ + 1), below; d2 m1; rd5-d2-r4 m-3), exp{O(1)log g₁⁻²|𝒳|} ≤ exp{O(1)M^dR₁^{d+1}(d₁′(𝒳)+1)}: |𝒳| = #cubes·(MR₁)^d in points of T^{(1)}, and log g₁⁻² ≤ R₁.
      - *The bad-cube and R₁ constants.* r = δ₀/g₀ = A₁(log g₀⁻²)^{p₀} (§3c(4); V3 L122). CRE (2.7), first line with n = 1, m = 0, gives (log g₁⁻²)^{2p₀} ≤ (1+β₀)(log g₀⁻²)^{2p₀}, and β₀ ≤ 1 for small g (p.255 l.51; d2 Q6). So r² ≥ ½a, and with |W| ≥ |𝒲| + |ℛ|/(2·5^d), c_bϑ²r²|W| ≥ ½c_bϑ²a|𝒲| + (c_bϑ²a/(4·5^d))|ℛ|. *Splitting the R₁ witnesses among the G below (rd5-d2-r4 m-2, repair (2)).* Two closed MR₁-cubes at distance < LMR₁ may meet only in an edge or a corner, so R₁ cubes with a common witness need not lie in one wall-component G. Each R₁ witness is within 2L²M₂R₁ of the R₁ cubes it serves, so these cubes lie in a set of diameter ≤ 4L²M₂R₁ ≤ ½LMR₁ (M ≥ 8LM₂, V3 L3968), which meets at most 2^d MR₁-cubes, hence at most 2^d components G. Each such G receives the share 2^{−d}c_bϑ²r² of the witness's exponent c_bϑ²r²; the shares of one witness add up to at most its exponent. A bad-cube witness is a bad bond with initial site in its own cube, so it stays in its own G. With r² ≥ ½a and at least |ℛ_G|/(2·5^d) witnesses serving the R₁ cubes of G, each G receives at least ½c_bϑ²a|𝒲_G| + (c_bϑ²a/(4·10^d))|ℛ_G|. This holds for wall-components and for ∗-components alike.
      - *Per component.* Let G run over the components in 𝒳 of the MR₁-cube cover of P₁ ∪ Q₁ ∪ R₁ ∪ W₁ (Minor 4). The four generating sets are unions of LM₂R₁-cubes, and the three kinds are disjoint: P₁ ∪ Q₁ ⊂ Ω₁ᶜ, R₁ ⊂ Ω₁^{∼−1}, and the bad cubes lie in Ω₁^{∼−1}∖R₁′ (V3 Lemma c5-2-3(c)). Each LM₂R₁-cube lies in exactly one MR₁-cube, since LM₂ divides M (odd powers of L, M ≥ 8LM₂; V3 L3968). So #MR₁-cubes(G) ≤ #gen(G), the number of generating cubes in G.
        - *Linear size.* d₁′ is the length of a shortest tree graph contained in the set and meeting all of its MR₁-cubes, in units of the cube side (RG1 p.257, with MR₁-cubes as on LFR II p.380 l.29).
        - For a connected union of n cubes, join the centres of intersecting cubes through a common point, along a spanning tree of the intersection graph. The union of these paths is connected and meets every cube; a spanning subtree of it has length ≤ √d(n−1) (d2 m11). So d₁′(G) + 1 ≤ 2·#MR₁-cubes(G) (d = 4). The length is Euclidean: RG1 p.257 l.15–19 defines the linear size by the shortest tree graphs "in the continuous space", meeting all the cubes, divided by the cube side, and adds that shortest trees formed by cube edges also exist, calling this an equivalent definition. It is equivalent up to constants only (rd5-d2-r4 m-4): in d = 4 the unit cubes [0,1]⁴, [1,2]×[0,1]³, [1,2]²×[0,1]², [1,2]³×[0,1], [1,2]⁴, [2,3]×[1,2]³, [2,3]²×[1,2]², [2,3]³×[1,2], [2,3]⁴ are consecutively wall-adjacent; the segment from (1,1,1,1) to (2,2,2,2) meets all nine, so the continuous linear size is 2, while any edge tree joining the first to the last has length ≥ their ℓ¹ distance 4. An edge tree through a wall-connected union of n cubes has length ≤ 2d(n − 1), so the two differ by constants; if p.385 uses the edge form, the constants of rd5-d2-r3 m7 apply there. The note uses the continuous form. So the bound holds as written, and the lattice-graph alternative of rd5-d2-r3 m7 lapses (checked 22 Oct, after 17:38, date).
        - Conversely (derived, replacing the citation of p.384 l.33, which no packet has supplied; rd5-d2-r4 m-3 and its §3(f)): let T be a tree of Euclidean length t = d₁′, in units of the cube side, meeting all the cubes. A closed traversal of T has length 2t, and points on it at spacing 1, at most 2t + 1 of them, put every point of T within ½ of one of them. A closed ℓ∞-box of side 1 meets at most 3^d closed unit grid cubes. So #cubes ≤ 3^d(2t + 1) ≤ 2·3^d(d₁′ + 1); this is used in *Together*.
        - Exponent available for G: γ₀m_Aa·#(cubes of P₁∪Q₁ in G) + ½c_bϑ²a|𝒲_G| + (c_bϑ²a/(4·10^d))|ℛ_G| ≥ 2c₄ϑ²a·#gen(G) ≥ c₄ϑ²a(d₁′(G) + 1), with c₄ := ½min{γ₀m_A, c_b/(4·10^d)} (the 10^d after rd5-d2-r4 m-2) and ϑ ≤ 1/16: 2c₄ ≤ γ₀m_A, and 2c₄ ≤ c_b/(4·10^d) ≤ ½c_b.
        - By the threshold ½c₄ϑ²A₁²(log g₁⁻²)^{p₀} ≥ 2, ½c₄ϑ²a ≥ 2(log g₁⁻²)^{p₀} (d2 m8). So the factor of G is at most exp(−½c₄ϑ²a(d₁′(G) + 1) − 2(log g₁⁻²)^{p₀}), i.e. −2p₀(g₁) in the box's notation (rd5-d2-r2 m16). This is R-d″(ii).
      - *What is used.* (D1) and (D1⁺), with (D-a), (D-b), (D-b⁺), (D-c); R-c for (b) and (l); R-p for the P₁- and Q₁-factors, with p.380's P/Q displays at step k ≥ N + 1 and their source (1.48), pp.364, 366, 368; LFR I pp.177–178; LFR II pp.356, 360, 363, 378; CRE (2.47)–(2.48), p.264, and Γ_n of p.255; CRE (1.5), p.247, for z; V3 Lemma c5-2-3(c), V3 L3968, V3 L122; CRE (1.4), (1.8) and pp.246–247 (rd5-d2-r2 m11); (B-q) (V3's (B1)(iii)) in (D-b⁺) and for the boundary data; (H4) for the g₀-independence of the constants of pp.247–251; the positivity of (1.73) at J = 0; p.248 l.9–10 for the distance of P₁ ∪ Q₁ from Ω₁; CRE (1.13), (1.15), (1.18)–(1.22), (2.6)–(2.8), and the β₀ of p.255; p.380 l.29, p.383 l.31–35; the linear size of RG1 p.257 (rd5-d2 M9; p.384 l.33 is replaced by the derived bound of *Linear size*, rd5-d2-r4 m-3). Not used: Hölder's inequality, the printed (1.79) applied at Λ as a whole (its j = 1 factor is re-derived here), any lower bound of the (2.21) forms beyond (D-a) and the local gaps, and any estimate comparing the Λ- and Λ₁-integrands (R-p's "the same at Λ as at Λ₁" is an identity of factors, not an estimate). Thresholds: those listed in R-d″.
    - *Reading R-s: withdrawn (rd3-rs S1).* It is not printed, and by A = √2y it is p.380's R₁ mechanism at threshold δ₀/√2, a case of the withdrawn threshold reading. (D2) does not use it.
  - *[16] = UV3, on the pages read (p.258, 260, 261, 268, 273; rd2 m12).* [16] is Bałaban, CMP 102 (1985) 255–275 (LFR II p.392), transcribed as Balaban\tex\UV3. On those pages:
    - its large-field sets are the curvature sets P of ζ_{Λ_j} (p.273 l.19–20), and (71) (p.273) gets their factor exp(−¼p²(g_j)) from a lower bound of the action on the four j-blocks Δ′ around a large plaquette. That is the factor p.380 l.37 uses for χ_j^c(P_j);
    - its fluctuation-field restrictions (p.260 l.37, p.268 l.26–27 and l.44) produce no small factor. p.268 enlarges the integration region explicitly; on p.260 and in (51) the restriction stands inside a "≤".
  - *Geometry of the bad bonds (round-4 form; (D1) uses the first item, and the box in its own form):*
    - With 𝒬⁺, e lies in an ℓ-cube none of whose ∗-neighbours is in Λ = Λ^fin ((4⁗)(c)(α)). So d(e,Λ) ≥ ℓ.
    - The cube □′ of e has side L²M₂R₁ ≤ ℓ/8 (V3 Lemma c5-2-4: M ≥ 8LM₂). So □′^{∼2} lies within 3ℓ/8 of e, at distance ≥ 5ℓ/8 from Λ.
    - □′ ⊂ Ω₁^{∼−1}∖R₁′ and e ∈ (□′^{∼2})* (V3 Lemma c5-2-3(c)).
    - Every bond of (□′^{∼2})* is a T₁^Λ variable: none lies in D(Λ).
    - Near □′^{∼2} the T₁^Λ quadratic form has the entries of H (the Schur term, range 4L around D(Λ), does not reach it). The Wilson action is expanded, so it is not literally a factor of the integrand (rd2 m4). The sentence on CRE's 𝐁^{(1)} clusters is dropped (rd2 m5, c4t-r2 m5): p.380 bounds "all the expressions in the exponential, except the Wilson action and the quadratic forms" first.
    - On the support, ϑr ≤ sup_{(□′^{∼2})*}|A|_σ < r, since □′ ⊂ R₁ᶜ. p.380's R_j-cubes have some |A| ≥ r and an upper bound from the second factor of (1.19) (CRE p.250, rd3-pw m11).
  - *How R-d″ is used:*
    - (D1) tests the bad bonds themselves, in V3's norm |·|_σ (L122); the cube-sup indicator of the round-4 form is not needed.
    - LFR's bound is a bound of 𝐓′(X,(U,0)) with a nonnegative integrand ((1.73)), so a larger indicator may replace a smaller one.
    - Bad bonds sharing a cube give one factor: (D1) chooses one bond per cube, and distinct cubes give distinct bonds. The overlap 6·5^{d−1} of the round-4 form (rd2 m6, c4t-r2 m1) does not enter. Minor 4 below uses the factor for all bad cubes of a component at once, which is why the joint form is needed.
  - *Positivity used (rd2 S2; revised after rd3-rs S2 and round 6).* R-d″ uses the positivity of the T-form only through (D1) and (D1⁺): H ≥ 0 ((D-a)), hence Q_X ≥ 0, and the local gaps (D-b), (D-b⁺) (d2 m3). The printed (1.79) is no longer applied at Λ.
    - The earlier reduction of the T₁^Λ forms to the forms at Λ₁ stays withdrawn (rd3-rs S2): it compared unsplit forms, while both integrands carry component-split forms over different partitions.
    - The A-integral at Λ: Q_X ≥ 0, |A(b)| ≤ C_𝐠/g₀ (CRE (1.13)), and g₀^{d(𝐠)#}∫e^{−½ΣQ_X}dA ≤ C_𝐠^{d(𝐠)#}, with # the number of T-bonds. The bound holds after pairing with the (1.15) Jacobian, which p.380 books among the normalisation constants (d2 m2).
    - The global form R-d′ would need S ≥ γ on 𝔤^J, which the sources do not give (V3 Remark c5-2-2). (D-a)–(D1⁺) avoid it: they use H ≥ 0 and the local gaps only.
- *R2: label entropy, option (b) of the report.*
  - *Injectivity.* Each collar bond is tested once. B^{(k)} is the set of bad bonds among those first tested at round k (V3 §c5-3-1). So, given 𝔅₀, a label is determined by U := ⋃_kB^{(k)}.
  - *Where U lies.* Given Λ, U lies in S := the bonds of Λᶜ within ρ_L + 1 of Λ₁^{(0)}. Then |S∩Z| ≤ dℓ^d·#(ℓ-cubes of Z) ≤ dL^dM^dR₁^d(d₁′(Z)+1) for each component Z of Z₁ = Λᶜ (p.380 l.29 with d′+1, (0); an ℓ-cube is an MR₁-cube at scale L⁻¹).
  - *The bound.* The labelled terms with Λ^fin = Λ number at most 2^{|S|} ≤ Π_Z exp(O(1)M^dR₁^{d+1}(d₁′(Z)+1)) once R₁ ≥ dL^d. This is a term of the first exponential of (1.79). The bad-cube factor is spent once, in p.381's fundamental factor.
- *Minor 3 (p₀):* see (0).
- *Minor 4 / c4q-rep S3: the bad cubes as a fourth generating set, and (1.76) modified.*
  - *Generators.* Let W₁ be the union of the bad LM₂R₁-cubes. Take the MR₁-cube cover of P₁∪Q₁∪R₁∪W₁, with components G = Z₁^{(i)}.
  - *Factor per component (R-d″(ii), bounded in (2) R1 (D2); OPEN pending D2.7 and the acceptance item; rd5-d2-r3 m8).* Each component G yields exp(−½c₄ϑ²A₁²(log g₁⁻²)^{2p₀}(d₁′(G)+1) − 2(log g₁⁻²)^{p₀}) (rd5-d2-r2 m16), with c₄ = ½min{γ₀m_A, c_b/(4·10^d)} (rd5-d2-r4 m-2). Since round 6, (D2) obtains it from per-cube factors: those of P₁ and Q₁ by R-p, and those of R₁ and the bad cubes by (D1⁺). It then uses the linear-size bound, so p.381's min is not reopened (rd3-rs m3; m4 is then moot). It needs the factors of all cubes of G at once: R-d″'s joint form (c4t-r2 S1).
  - *Geometry.*
    - Every point of 𝔅₀ = (Λ₁^{(0)})ᶜ is within 100ℓ of CRE's unfilled bad region Q₁′^{∼4} ∪ (B(P₁¹)ᶜ)^{∼5} ∪ R₁′^{∼1} (V3 Lemma c5-3-0(b)). That region is within 6ℓ of P₁∪Q₁∪R₁.
    - Every point of Λ₁^{(0)}∖Λ is within 103ℓ of x_e for a bad e (Lemma c5-3-1(c) with 𝒬⁺).
    - Hence the modified (1.76): Z₁ = Λᶜ ⊂ ⋃_G G^{∼107}.
    - *Per component (c4t-r2 m3).* (1.82) is per component Z of Z₁, so the form needed is Z ⊂ ⋃_{G⊂Z} G^{∼107}. It holds: each removed point is joined inside Λᶜ to x_e, since 𝒬⁺(e) is face-connected and the fill hulls contain their component (V3 Lemma c5-3-1(c), proof); each point of 𝔅₀ is joined inside 𝔅₀ to an original bad point (Lemma c5-3-0(b), proof); and each G lies in Λᶜ and is connected. So the G used for a point lie in its component.
    - *The P-part (c4t-r2 m2).* "within 6ℓ of P₁∪Q₁∪R₁" is checked for Q₁′^{∼4} (5ℓ) and R₁′^{∼1} (2ℓ). For (B(P₁¹)ᶜ)^{∼5} it needs CRE's definition of P₁¹ and its relation to LFR's P₁, not yet read. Any O(ℓ) distance changes only 107 and 434, and the exponent count below is unaffected. Open as a citation, not as a bound.
  - *p.385's step with ∼108 in place of ∼3.* d₁′(G^{∼108}) ≤ 217^d(3·2^{d−1}d₁′(G) + 2^d) ≤ 2(434)^d(d₁′(G) + ½). So d₁′(Z)+1 ≤ 2(434)^d Σ_G(d₁′(G)+1), and (1.82) holds with ¼c₄(434)^{−d}ϑ² in place of ¼γ₀(14)^{−d}.
  - *The j = 1 condition.* It becomes ¼c₄(434)^{−d}ϑ²A₁²(log g₁⁻²)^{2p₀} ≥ O(1)2(64)^dM^dL^{d+1}R₁^{d+2}, with the O(1) enlarged by R2 and by the costs of (D2). The +1 of d2 m1 costs O(1)M^dR₁^{d+1} per component, which the same condition dominates. The left side is of order (log g₁⁻²)^{2p₀} and the right of order (log g₁⁻²)^{6𝔯}. Since p₀ ≥ 5𝔯 (V3 L3968, from CRE p.246; d2 m7; rd5-d2-r2 m3), 2p₀ ≥ 10𝔯 > 6𝔯, and it holds for small g₁ for any fixed c₄ > 0.
  - *Where (1.76) enters (p.385, at step k ≥ N + 1; rd5-d2-r3 m2).* The sup of R-d″(ii) runs over the domain data occurring at the labelled configuration; the modified (1.76) enters only on p.385 (and p.386) ((0); c4t-r2 m4; rd5-d2-r2 m5). The enlarged domain class is harmless: pp.380–383 do not use (1.76) ((D2) *Check* (f)), and (D2) bounds each labelled configuration directly. p.386's (1.84) belongs to D2, where recurring retreats need the same enlargement.
  - *M5.* This also covers V3's iterated side-100ℓ Fill (c4q-rep M5). The extra region Λ₁∖Λ₁^{(0)} is part of Z₁, so its volume costs are in (1.79)'s first exponential, and the factor that pays them is (1.82) with the modified (1.76).
- *Minor 5:* the box factors on I∖D(Λ) are the part, at those bonds, of χ^{(0)}(R₁ᶜ∩Λᶜ). The rest of that factor is J-tests already in χ(Ω₁∩Λ₁ᶜ,S₁), and tests on D(Λ) that duplicate the conditional box. By idempotence of single-bond indicators, box(D(Λ))·box(I∖D(Λ))·(J-tests) = box(D(Λ))·χ^{(0)}(R₁ᶜ∩Λᶜ) as functions. §3c(4‴) is corrected.
- *Minor 6:* CRE (3.19), p.268, is a lower bound on A₁/A₀. It holds with ϑA₁ for small g, and the check is moot, since CRE keeps A₁ under (P).
- *Minor 7:* LFR II p.387 asserts that (1.89) implies (2.50) [III], hence Corollary 3. This is accepted as Bałaban's result.
- *Minor 8 (where the factor is used):*
  - A bad test's factor enters only (1.79), through R-d″.
  - Corollary 3 consumes (1.79) through (1.80) and (1.89) (p.387).
  - p.264's route takes its factors from −A(1/g², U_k), a function of the background, and cannot see a fluctuation test.
  - CRE p.253's "controlled by the large field estimates" for 𝐁^{(1)} is a volume cost inside (1.79)'s first exponential. For retreats it is (4⁗)(a)'s O(1) per changed boundary bond.
- *Minor 9:* R-c is restated in sublevel-set form in (3) S1 below. p.251's second use of Λ₁^∼ (the background) is named there. "cutoff χ^{(0)}(Λ)" means the box on D(Λ). The Fill is V3's iterated side-100ℓ variant, covered by the modified (1.76).

**(3) it1-c4q-rep (§3c(4⁗)).**
- *S1: R-c (α), in sublevel-set form (corrected in round 4, it1-c4q-rep-20261022-r2a).* On Λ^∼∖Λ, the characteristic functions of the T-integrand are sublevel indicators {|A(b)| < t} with t ≤ r. Tests are located as in (4⁗)(c)(α): a cube test by its index cube, a single-bond test by its bond (r2a m-6).
  - *Why 𝒬⁺ (r2a m-8).* A bad test is a superlevel indicator. None of the occurrences below is sensitive to the sign of an extra factor, so they do not force 𝒬⁺. The need is R-d″'s geometry ((2) R1): its cubes must lie at distance ≥ ℓ/2 from Λ, and 𝒬⁺ gives d(e,Λ) ≥ ℓ for every bad bond e.
  - *The other factors (r2a m-2, m-3).* ι_ξ = 1 on the support ((1) S1), so it is not a factor. Terminal-round good tests lie in Λ^∼∖Λ (Lemma c5-3-1(b)). Earlier-round good tests and the box factors on I∖D(Λ) lie in Λᶜ, possibly outside Λ^∼ (up to about 103ℓ from Λ on retreated terms). On terms with no bad test, all good tests are terminal-round tests. All of these factors take values in [0,1].
  - *The monotonicity principle (r2a S-1; derived 22 Oct).* The occurrences listed below are a list, not a proof that every consumer accepts the extra factors. The argument at step 1 is this. Every step-1 consumer of T₁'s characteristic functions is an identity of functions, an upper bound of an integral with a nonnegative integrand, or a supremum over the support:
    - T₁ is pending (p.254): no step-1 operation integrates it.
    - At k = 0 the kernel of (1.29) (p.254) is a nonnegative measure. δ, ζ and the characteristic functions are nonnegative. The fields are real, so the quadratic forms in the exponent are real.
    - The conditional cutoff is box(D(Λ)), unchanged (Lemma c5-3-3(iv)).
    - (4⁗)(a), R-d″ and (1.79) are upper bounds of such integrals. R-d″ is OPEN as a statement, and is used only in this form.
    - A pointwise identity survives multiplication by any factor. An upper bound of a nonnegative integrand, or a sup over the support, survives multiplication by a factor in [0,1].
    - So the collar tests and box factors cannot break a step-1 use.
  - *The LFR I part (D2).* The integration that consumes p.187's list ("all the operations discussed in Sect. 3 [III]") is not read. Until it is, the LFR I claims are restricted to the identities listed below.
  - *Occurrences in the transcriptions (citations corrected, r2a m-1, m-4).*
    - *CRE p.253 (1.26) (k = 0) and p.269 l.17–19 (general k):* "their product is χ^{(k)}(Λ_{k+1})", with (3.21) for Ω∩Λᶜ. p.251 has only "On the set Λ₁^∼ we have only the small fluctuation field characteristic functions from (1.18)".
      - This is an identity of functions. It splits the characteristic functions into the cutoff of the conditional integral on Λ and the T-part.
      - Under (P), the cutoff is box(D(Λ)) ((4″); Lemma c5-3-3(iv)). The T-part is (3.21)'s product times the collar tests of the term, by the idempotence statement of (2) Minor 5.
      - No estimate is drawn from it at step 1.
    - *CRE p.251 l.22–24:* the background U₁(Ω₁∩Λ₁ᶜ,V) is defined using Λ₁^∼∖Λ₁. This is a definition at the original Λ₁, which V3 keeps (L2423) and (P) does not change.
      - Since Λ ⊂ Λ₁, a function of V on Ω₁∩Λ₁ᶜ is a function of V on Ω₁∩Λᶜ. This is the locality in V that p.251 asks for. Whether step 2's determining set, which p.269 builds from 𝐁_k(Λ_k), is needed at Λ or at Λ₁ is a D2 item (r2a m-7).
      - This is item (δ).
    - *LFR I p.178:* the defining occurrence. (1.8) sits on (Ω_{j+1}∖Λ_{j+1}^∼)∩Z and (1.9) on (Λ_{j+1}^∼∖Λ_{j+1})∩Z. p.178 also says that ζχ "is equal to the product of the following seven groups", under its condition (ii). Under (P) the product has an eighth group, the collar tests. Whether terms with collar tests satisfy LFR I's conditions (i) and (ii) is a D2 item.
    - *LFR I (the R-operation, used from D2 on).* The (1.9) functions {sup_{(□′^{∼2})*}|A_j(b)| < g_j⁻¹δ_j} on (Λ_{j+1}^∼∖Λ_{j+1})∩Z are cited by number:
      - on p.179: they are not gauge invariant, which motivates the gauge fixing;
      - on p.183: (1.28), their completion to Z∩Ω by a decomposition of unity;
      - on p.187 l.36–39: the list of the remaining functions.
    - *LFR I (1.29).* It is stated on p.183, and its proof runs pp.183–187. p.185 proves the (1.8) and (1.7) parts, with (1.38) on □′^{∼2} for □′ ⊂ Ω_{j+1}^∼∖Λ_{j+1}^∼. Under (P) those cubes are S₁-cubes of the original Λ₁, outside Λ₁^∼ ⊃ Λ^∼. The proof uses the restrictions only as upper bounds on |A_j| (r2a m-5).
    - *The good collar tests in LFR I.* They are sublevel indicators of the same variables A_j(b), at threshold ϑg_j⁻¹δ_j, located as in the bullet on the other factors.
      - They are functions of the same variables A_j(b) as (1.9). How p.179's gauge fixing acts on them is not read (r2a m-9).
      - (1.28) and (1.29) are identities, and they hold with the extra factor on both sides.
      - p.187's list gains them.
    - *(2.41)* uses Z_j^∼ for the 𝐁-localisation (p.261). Z₁ = Λᶜ there, as read from (2.21) at j = 0 against (1.29); the definition of Z_j on pp.255–256 is not read (r2a m-10). So this is a definition from Λ, not a use of (α).
  - *Status:* at step 1, (α) in sublevel-set form holds by the monotonicity principle. R-c is otherwise as in §3c(4″). The LFR I part waits for the operations after p.187 (D2).
- *S2: the 𝒬⁺ reread of V3 (done 01:33).* Every line of V3 containing N_ret or 102ℓ was read.
  - *Search record (round 4, c4q-r2b m7; literal-string searches of V3, 22 Oct).*
    - N_{\mathrm{ret}}: L2426, 2455, 2457, 2459, 2461, 2467, 2474, 2845, 2849, 3029, 3032, 3033, 3037, 3039, 3043, 3090, 3155, 3158, 3162, 3186, 3194, 3204, 3210, 3211, 3214, 3223, 3227, 4365. All are in the ranges below.
    - 102\ell: L2426, 2430, 2453, 2455, 2461, 2845, 3043, 3162, 3186, 3204. 204\ell and 207\ell: L2426, 2430, 3204. 2\ell+: the 102ℓ lines. All are in the ranges below.
    - \rho_L+1: L2420, 2423, 2430, and L2610, 2620 (the count 4(2ρ_L+1)⁴ for the shift m), L4060, 4079 (the collar and Hessian range). The last four are not retreat geometry.
    - \mathcal Q: L2419, 2420, 2423, 2430 are the retreat set. The other hits (L269–680, 1062–1066, 1846–1919, 3986, 4887) are the constraint primitive 𝒬 and its rows.
    - =16: L729 (2⁴ = 16, the cubes met by D_b), L2423, and L1732, 3545, 3839 (c_reg, C_g = 162), which are unrelated. 2^4: L729, 2423.
    - So the count 16 of L2423 is used nowhere else, and no other line restates the retreat geometry under these patterns.
  - *L2423.* 𝒬⁺(e) has at most 4⁴ = 256 cubes, and its points are within 2ℓ+ρ_L+1 ≤ 3ℓ of x_e. The count 16 is not used anywhere else in V3. (L729's "2⁴ = 16" counts the cubes met by D_b and is unrelated.)
  - *L2426–2430, Lemma c5-3-1.* (a) and (b) are unchanged. (c) holds with 103ℓ, and (d) with N⁺_ret = 4(209ℓ)⁴ ((4⁗)(c)).
  - *L2453–2474.*
    - The radius 102ℓ+1 becomes 103ℓ+1, and N_ret becomes N⁺_ret.
    - (c5-3-1) holds in the same form: log N⁺_ret ≤ C′ + 4𝔯 log(2 log g₀⁻²).
    - (c5-3-2) and its comparison are unchanged, since 2p₀ ≥ 10𝔯 > 4𝔯.
  - *L3204.* The bonds with an endpoint within 103ℓ+1 of x_e number at most 4(206ℓ+5)⁴ ≤ 4(209ℓ)⁴ = N⁺_ret, for ℓ ≥ 2.
  - *L2461, L2845, L2849, L3029–3043, L3090, L3155–3194, L3210–3227, L4365.*
    - N_ret enters as a prefactor, through log N_ret = O(log log g₀⁻²) or τ²N_ret → 0, or as the count of L3204.
    - The radius enters only in the attributions "x_e within 102ℓ+1".
    - All of these transfer with (103ℓ, N⁺_ret).
    - C_K = 4(4Kℓ+9)⁴ comes from the witness radius Kℓ of the marks, fixed by Lemma c5-2-4 for M_e and by Lemma c5-3-0(b) for a_b (K = 256; r2b m8). Neither depends on the shape of the retreat, so C_K does not change.
  - *Status:* the 𝒬⁺ change is consistent with all of V3's uses. The status "modulo the 𝒬⁺ reread" is dropped.
- *S3:* (2) R1 and (2) Minor 4. No lower bound of the T₁^Λ form is used.
- *M1:* in (4⁗)(b) and (4″), "< r (Lemma c5-3-3(iii))" is replaced by "< r, by Lemma collar-coverage(iii) for e ∈ J, or by the retained box factor for e ∈ I∖D(Λ)". Corrected in round 4 (c4q-r2c m-1, r2b m1): the distance is taken at the round k in which e was tested, d(e,I) ≤ d(e,D^{(k)}) ≤ ρ_L ≤ 3R_c (proof of Lemma c5-3-1(a)), since a bad bond has d(e,D(Λ^fin)) > ρ_L. The box case is e ∈ I∖D^{(k)} ⊂ I∖D(Λ). §3c(4) and (4″) are corrected.
- *M2:* in (4⁗)(d), (2.19) is the factorisation over a decomposition of Z₁ into disjoint unions of components ("e.g. as a union of connected components", p.258). Here the components are the ∗-components.
- *M3:* the Λ-sum runs over Λ ⊂ Λ₁^{(0)}. χ_Λ = 0 otherwise, and the (⇐) identity is exact for these Λ. The restriction is necessary (c4q-r2c): if Λᶜ ⊊ 𝔅₀ and no test is bad, every local run ends with complement 𝔅₀, so Π_Xχ_{Λ,X} = 1 while χ_Λ = 0. Since Λ₁ is an outer label ((4⁗)(d)), Λ ⊂ Λ₁^{(0)} is a range of the outer sum, not an indicator inside T₁.
- *M4: one definition of the local run.*
  - χ_{Λ,X} := the indicator that the run started from the full 𝔅₀ ends with complement X ∪ (𝔅₀∖X). In this run, every test at a bond without both endpoints in X is declared good.
  - χ_{Λ,X} depends on the tests in X and on 𝔅₀, a function of the outer label Λ₁ (Lemma c5-3-0(a)). On the range Λ ⊂ Λ₁^{(0)} it depends on 𝔅₀ only through 𝔅₀ ∩ X ((4⁗)(d), *Locality in 𝔅₀*; r2c S-2).
  - The proof of (4⁗)(d) is unchanged (checked by r2c against this definition). The (⇒) step's "other regions frozen" is now the definition.
- *M6:* "on at most N⁺_ret bonds" becomes "on at most C·N⁺_ret bonds", counting the MR₁ layer and ρ_L. The count check is unchanged.
- *M7:* R-e is dropped. The cross-component cost is bounded per boundary bond by (4⁗)(a)'s own computation, and a retreat costs at most C·N⁺_ret times that. Corrected in round 4 (c4q-r2c S-3): under (P), 𝐁^{(1)} is formed at Λ, so "CRE's 𝐁^{(1)} at Λ₁ is unchanged" is withdrawn. Its total cost is CRE's (2.48) at Λ, a volume cost 2B₁|Ω₁^{(1)}∖Λ⁰| paid as on LFR II p.380 l.27–29 ((4⁗)(a), *The total 𝐁 cost at Λ*). No per-bond reading of p.253 is used.
- *M8: the format of 𝐁, by the Neumann series.*
  - (I3) gives γ ≤ H_DD ≤ h_+ on D = D(Λ). So C^{(0)}(Λ) = h_+⁻¹Σ_{n≥0}K^n, with K := 1 − H_DD/h_+ and 0 ≤ K ≤ 1 − γ/h_+.
  - By (I1), (K^n)_{bb′} = 0 unless d(b,b′) ≤ nρ_L. It depends on D(Λ) only within nρ_L of b, and on U₁ only within (n+1)ρ_L of b, since each entry depends on U₁ through a stencil of diameter ≤ ρ_L (V3 L660; c4q-r2c m-2).
  - *The off-diagonal blocks (r2c m-2; derived 22 Oct from V3 (I1)–(I2), L2268–2269).* For a row b ∈ D, (I2) gives Σ_e‖H(b,e)‖ ≤ m_L, so every entry has norm ≤ m_L. By (I1), H(b,e) ≠ 0 only if |z(b)−z(e)|₁ ≤ 2, so a column e meets at most 164L⁴ rows b ∈ D. Schur's test gives ‖H_{DJ}‖ ≤ (m_L·164L⁴m_L)^{1/2} ≤ 13L²m_L =: C_{DJ} (r2c's C_H; renamed, since §3e(3) uses C_H for another constant). H is the symmetric matrix of a quadratic form, so ‖H_{JD}‖ ≤ C_{DJ} too. For x ∈ I∖D(Λ), (I2) with D = I gives the same bound.
  - So the Schur cross term is Σ_n h_+⁻¹⟨x, H_{xD}K^nH_{Dy}y⟩. Its n-th term is a function of the fields in the (n+2)ρ_L-ball around x, has norm ≤ C_{DJ}²h_+⁻¹(1−γ/h_+)^n|x||y|, and vanishes unless (n+2)ρ_L ≥ d(x,y) ≥ ℓ/2.
  - This is a localised representation with exponential decay in the diameter. The format of 𝐁-terms is (2.41)–(2.42), p.261 (not p.258); CRE supplies it at Λ ((4⁗)(a), *Their 𝐁-format*). U₁'s own dependence on V is localised as in CRE: p.251 determines U₁(Ω₁∩Λ₁ᶜ,V) on Λ₁^∼∖Λ₁ "by the set 𝐁₁(Λ₁ᶜ)", and p.252 l.22–23 calls the result "the desired localization property".
- *M9: adjacency, recorded per use.*
  - Fill (V3): face adjacency of ℓ-cubes.
  - The components of (2.19) and (2.21): ∗-adjacency. This is the ℓ/2 rule of (4⁗)(a) at the cube level, in the direction used: every ℓ/2-component of Ω₁∩Λᶜ lies in one ∗-component of Λᶜ. That the two coincide is not needed.
  - *The weakest form (round 4, c4q-r2c m-3).* p.258 leaves the adjacency of its components unspecified ("in the same component"). What §3c(2)(b) uses is that CRE's (2.19) components at Λ₁ (p.258) are no coarser than ∗-components, so each lies in one ∗-component of Λᶜ. This is part of reading R-g.
  - *One p.251 sentence, two readings (logged).* p.251's filling of Λ₁ᶜ states no adjacency either. V3 implements it with face adjacency (L2401: "CRE p.251 does not specify its adjacency"). Both readings are no coarser than ∗, which is all that is used.
- *M10: withdrawn in round 4 (c4q-r2c S-1).* M10 wrote the output as Σ_{Ω₁,Λ}χ₁T₁^Λ[…], with the original Λ₁ a function of an inner label R₁. That doesn't work: the S₁ kernel depends on Λ₁ nonlocally, through U₁(Ω₁∩Λ₁ᶜ,V), Ψ_ξ and 𝐇_{1,Ax}. It is replaced by keeping Λ₁ an outer label: the output is Σ_{Ω₁,Λ₁,Λ}χ₁T₁^{Λ₁,Λ}[F^Λ(1)·exp A₁^Λ] ((4⁗)(d), *Λ₁ stays an outer label*). The R₁-part is then CRE's own sum at fixed Λ₁, grouped into the X by M9, and the cost is the extra label (Ω₁, Λ₁, Λ), a D2 item.
- *M11:* the fact used in (4⁗)(a) is read on p.258 directly. The pointer "V3 §c5-3-1 on p.251" is dropped.

**(4) it1-d11 (§3d; repaired 01:48–02:05, in place in §3d and §3b).** No fatal finding. Each item, and where it is now:
- **S-A (chart inclusion).** The citation was wrong: the sentence is Lemma charts, L475, not L607. §3d(2)(d) now quotes it and checks its six parts. The rows with 𝓕_r ∩ D(Λ) ≠ ∅ are L475's rows by distance. Their input bonds lie in D(Λ), I∖D(Λ) or J, with values ≤ 2r, < r and < r respectively; Ψ_ξ = id there by L475's own parenthesis. So the input is L475's carrier-I input at t = 1, and ‖A‖ ≤ ϑ_*/4 as in the covered case.
- **S-B (endpoint majorants).** L3080 is no longer used off coverage. Lemma c5-5R-3 gives 𝔡^0_W ≤ 2M^ph_Λ(W) with ρ_ph ≤ ρ_t ≤ ρ_pin, and its proof uses no coverage (§3d(2)(d)). The passed-test path bound for good groups was checked against §c4-10-4: it uses only the group's own word f_W, whose rows the added condition places in D(Λ) (§3d(4)).
- **S-C(i) (extraction at uncovered carriers).** The proof of Prop. regional-square-extraction (L1980–2045) and the pinned-tree proof (L1420–1427) were read in full. Contour coverage enters only at the short-cluster step L2041, and there it follows from d_j > 2R_* + 2R_0 alone (§3d(2)(g)). This also discharges the qualification step of Lemma c5-7-1 and Cor. c5-7-2(a) (§3d(2)(f), (i)).
- **S-C(ii) (link change in the §3b telescoping).** supp Γ now includes the free-input stencils of Γ's marked traversals (§3b(2)). Then E ∩ supp Γ = ∅ at every step, the link functions coincide, and §3b(1) applies. The diameter grows by ≤ 2R_K, and the short-cluster threshold becomes 4(R_* + R_K) (§3b(4), §3d(2)(h)).
- **S-D (the universal claim).** Every statement under L2594 used here is listed with what its coverage does (§3d(2)(i)). Two need a restriction, and both are recorded: Lemma c5-5-1's display holds with I_C ∩ D(Λ), and Lemma c5-4-4's definition already has it (L2582).
- **Minors.** m1: §3d(2)(d), both uses. m2: d^Λ(n) := dist(Γ_n, E(B_ξ) ∪ (I∖D(Λ))). m3: two kinds of de-younged bonds, 102ℓ/103ℓ and 100ℓ. m4: torus side by distance, 2ℓ − 1 > 2L+1 (§3d(2)(f)). m5: Schur via L2679, and each §c5-4 statement cited separately. m6: N_exp ≲ n_C b⁴ q_pt, an upper bound. m7: "and Q_W lifts". m8: partly exposed links are not id. m9: full hypothesis list in §3d(1). m10: L5024 marked as an interpretation and no longer relied on. m11: §3b(1) no longer assumes coverage. m12: the next packet must include the gaps-block plan.
- **S1 and S7 consequences, now stated.** At t = 0 the source carries the exterior constants (§3d(1)). A later bound of e^{E^∂} costs e^{Cτ²} per exposed segment, which is a D2 obligation (§3d(5)).

**(5) Statuses after (1)–(4), as corrected after round 4 (§3h).**
- D1.0(P) at step 1: everything is derived except R-d″(ii), the per-component factor of P₁, Q₁, R₁ and the bad cubes. Round 4 found its earlier form not printed (§3h). (i) is derived pointwise; (ii) is the j = 1 factor of (1.79) at step k ≥ N + 1 and is OPEN pending D2.7 and the acceptance item; the Hölder route is withdrawn ((2) R1, (D0)–(D2); rd5-d2-r3 m8). R-c (sublevel form) holds at step 1 by the monotonicity principle ((3) S1). 𝒬⁺'s effect on V3 is reread, with the search record. Λ₁ stays an outer label ((3) M10, withdrawn), and 𝐁 at Λ is paid by CRE's (2.48) ((3) M7).
- R-d″ replaces R-d, and R-e is dropped.
- D1.1: the identity §3d(1) is derived on every labelled term. D1(ii) as in §3d(4) is derived on every labelled term, including good groups that pass the phase test on uncovered terms: the endpoint identities (c4-11-6) hold off coverage (§3d(4), round-4 repair of it1-d11-20261022-r2 S-1).
- ι_ξ = 1 on the support of χ₁ζχ_{ξ,e}, at a new small-g₀ threshold (§3c(2)(e), round-4 repair of c2-r2 S-A).
- (1)–(4) were reviewed in round 4 and repaired (§3h). The round-4 repairs are not reviewed.

## 3g. D1.3 leftovers: carrier dependence of the reference species, and the locality of D(Λ) (worked 05:19–05:29, 22 Oct; not reviewed)

**(1) Carrier locality of the reference species (derived from V3's proof of Lemma c5-6-2, L3005).**
- *Setting.* The carriers are I and D(Λ) := {b ∈ I : b has an endpoint in Λ} for regions Λ ⊂ Λ₁^{(0)} (V3 §c5-2-3). For a carrier D and a union Z of LM-cubes put E_D(Z) := {b ∈ D : b has an endpoint in Z}. The Hessians at all carriers are principal restrictions of the one H_ξ, and the reference ones of the one H° (L3005, last sentences; Remark c5-5-11(1)).
- *(a) Selected integrals.* Let D, D′ be carriers with E_D(Z) = E_{D′}(Z). Then the selections and split selections with final domain Z are the same at D and D′, and at t = 0 the selected integrals coincide, for the actual and the reference data: k^{f,0}_D(Z) = k^{f,0}_{D′}(Z), ν^{f,0}_{D,Z} = ν^{f,0}_{D′,Z}, k^{f,∘}_D(Z) = k^{f,∘}_{D′}(Z), ν̂^{f,∘}_{D,Z} = ν̂^{f,∘}_{D′,Z}.
  - *Proof.* V3 proves this for (D, D′) = (D(Λ), I) under "every bond of I with an endpoint in Z lies in D(Λ)", which is E_{D(Λ)}(Z) = E_I(Z). The proof uses its hypothesis only in that form. The uses, in order:
    - the young part of a primitive's free-input set lies in E_D(Y) = E_D(Z) ∩ E(Y) for its host Y ⊆ Z ("the same set for both carriers by hypothesis");
    - probe hosts Y_b ⊆ Z have b ∈ E_D(Y_b), so the 𝐃₀-hosts inside Z are the same;
    - the bad bonds 𝖯 meet Z, so 𝖯 ⊆ E_D(Z), and "𝖯 ⊆ D ∖ E(Y₀)" is the same condition at both carriers;
    - E₀ = E_D(Z₀) = E_D(Z) ∩ E(Z₀), so C_{E₀} has the same entries;
    - every bond entering S_{Z₀}(σ) and Γ_{E₀}(σ) is a carrier bond in Z: walks have D(ω) ⊂ Z, the walk blocks are entries of powers of id − H/s_H over carrier bonds in D(ω), and the rows e ∈ E₀ use b′ ⊂ int D ⊂ Z;
    - the X-integral (Γ_{E₀}(σ)X involves X on bonds of Z only) and the Dirac tensors.
  - Where V3 writes "in D(Λ) by hypothesis", the general case reads "in E_D(Z) = E_{D′}(Z)". No step uses D(Λ) ⊆ I.
- *(b) Groups.* For a group W let F(W) be its footprint (L4583) and Ẑ(W) the union of the cubes of F(W). If E_D(Ẑ(W)) = E_{D′}(Ẑ(W)), then W is a group at both carriers, w°_D(W) = w°_{D′}(W), and a^D_W = a^{D′}_W.
  - Each root and constituent domain lies in Ẑ(W), so (a) applies to each.
  - The probe label sets 𝖫_Z are carrier bonds b with Y_b ⊆ Z, so b ∈ E_D(Z). The contact sets and hulls are then determined by the domains and the contour (L3001).
  - The Ursell coefficients and 1/k(W)! depend on the incompatibility graph only.
  - a_W = w°(W)∫χ(P°_W(a)) d⊗ν̂^{f,∘}(a) (L2674) integrates the reference word, whose links depend on the root variables only, against the same measures.
- *(c) Clusters and q°.* Incompatibility is footprint contact or a shared traversal (L4642). It does not involve the carrier. For a cluster Γ put Ẑ(Γ) := ⋃_{W∈Γ}Ẑ(W). If E_D(Ẑ(Γ)) = E_{D′}(Ẑ(Γ)), then Φ°_D(Γ) = Φ°_{D′}(Γ), by (b).
  - Call Γ *marked* (by D, D′) if Ẑ(Γ) contains an endpoint of a bond of D △ D′. A cluster present at one carrier only contains a group present at one carrier only, so it is marked, by (b). Put Φ° := 0 at a carrier where Γ is not a cluster.
  - With q°_D(𝔅) = exp(−Σ_{Γ hits 𝔅}Φ°_D(Γ)) (L2674), for every compatible family 𝔅 of groups present at both carriers:

    log q°_D(𝔅) − log q°_{D′}(𝔅) = −Σ_{Γ hits 𝔅, Γ marked} [Φ°_D(Γ) − Φ°_{D′}(Γ)].

  - The same holds for log S° = Σ_Γ Φ°(Γ), with the sum over all marked Γ. For (D(Λ), I) this is the first line of Lemma c5-6-3's proof.
- *(d) Bounds, with the cluster weight kept.* At D(Λ) (and at I, by the closing remark of Lemma c5-5-3(d)), V3 applies Kotecký–Preiss to the gas with activities |a_W|e^{3νσ(W)/2} and node cost νσ(W)/8 (proof of Lemma c5-5-3(d), L2679). The cluster coefficient of that gas has modulus |φ^T(Γ)|∏_{W′∈Γ}|a_{W′}|e^{3νσ(W′)/2} = |Φ°(Γ)|e^{3νσ(Γ)/2}, with σ(Γ) := Σ_{W′∈Γ}σ(W′). So the rooted conclusion, before V3 drops the weight, is

  Σ_{Γ∋W} m_W(Γ)|Φ°(Γ)|e^{3νσ(Γ)/2} ≤ |a_W|e^{13νσ(W)/8}.

  - With |a_W| ≤ M_Λ(W) and the pin sum Σ_{W: Δ∈F(W)}e^{4νσ(W)}M_Λ(W) ≤ C_pinρ_t (Lemma c5-5-8(a), first display, as used in Lemma c5-6-3), for every cube Δ:

    Σ_{Γ hits Δ}|Φ°(Γ)|e^{3νσ(Γ)/2} ≤ C_pinρ_t.

  - Hence, with 𝒩(D, D′) the cubes containing an endpoint of a bond of D △ D′, the difference in (c) is at most Σ_{Δ∈𝒩(D,D′)} Σ_{Γ hits Δ and 𝔅}(|Φ°_D(Γ)| + |Φ°_{D′}(Γ)|), and each Δ contributes ≤ 2C_pinρ_t e^{−3νσ_*(Δ,𝔅)/2}, where σ_*(Δ,𝔅) is the least σ(Γ) of a cluster hitting both. For (D(Λ), I) this is Lemma c5-6-3 with the weight kept.
- *(d′) Diameter (derived).* σ(W) := s(W) = n(W) + |ℋ(W)|/(LM) (Lemma c5-5-8, L2788), the size of Lemma c4-6-env (L4610–4616). That lemma gives F(W) ⊆ 𝔈(W), with the envelope 𝔈(W) connected under max-norm adjacency of cubes and |𝔈(W)| ≤ A_Eσ(W) ((a), (b)). Incompatible groups have footprints in contact or share a traversal n ∈ ℋ(W) ∩ ℋ(W′) ((d)), and π₁(ℋ(W)) ⊆ 𝔈(W).
  - So for a cluster Γ (connected in the incompatibility graph) the envelope union 𝔈(Γ) := ⋃_{W∈Γ}𝔈(W) is connected, with at most A_Eσ(Γ) cubes. A connected set of k cubes has fine ℓ^∞ diameter < kLM (proof of (c)). Hence Ẑ(Γ) ⊆ 𝔈(Γ) and diam 𝔈(Γ) ≤ A_E·LM·σ(Γ).
  - With (d): for every cube Δ and R ≥ 0, Σ_{Γ hits Δ, diam 𝔈(Γ) ≥ R}|Φ°(Γ)| ≤ C_pinρ_t·e^{−3νR/(2A_E LM)}.
  - In (c), a marked cluster hitting 𝔅 has 𝔈(Γ) containing a cube of 𝒩(D, D′) and a cube within index distance one of 𝔈(W) for some W ∈ 𝔅. So with d := dist(𝒩(D, D′), ⋃_{W∈𝔅}𝔈(W)) − LM, the difference in (c) is at most 2C_pinρ_t|𝒩(D, D′)|e^{−3νd/(2A_E LM)}.
- *(e) What (1) gives.* E_{D(Λ)}(Z) is a function of the ℓ-cubes of Λ that contain a site within distance 1 of Z. So every reference species of a labelled term (a^Λ_W, w°_Λ(W), Φ°_Λ(Γ), hence q°_Λ and S°_Λ) depends on the label only through Λ near its footprint. This is Remark c5-6-5's "what is local is the marking, not the domain", now for any two labels, which is the comparison D2 makes.
- *(f) Not covered by (1).*
  - *The t > 0 species* (Υ¹_W and the terms of 𝓑^Λ). Their selected integrals contain the shift m, which depends on the carrier through C^{(0)}(D) = H_DD⁻¹ (§3f(3) M8 gives its Neumann series: exponential decay, not exact locality). So (a) does not apply to them as it stands. Their carrier dependence is derived in §3j, with the local shift m̂, except (O1)–(O3) there.

**(2) Locality of D(Λ) ∩ Y (reduced to §3c(4⁗)(d)).**
- D(Λ) ∩ Y = {b ∈ I ∩ Y : b has an endpoint in Λ} is a function of the ℓ-cubes of Λ containing an endpoint of a bond of Y. So the question is about Λ = Λ₁^fin.
- On a single history, Λ₁^fin near Y is not a function of the tests near Y, since the rounds of L2417–2423 can carry a retreat from round to round.
- D2 does not need that pointwise statement. It needs the label sum in polymer form, and that is derived:
  - Σ_lab 1_lab(…) = Σ_Λ χ_Λ(…), χ_Λ = 1{Λ₁^fin = Λ} (§3c(4⁗)(d));
  - at fixed outer labels (Ω₁, Λ₁) and on the range Λ ⊂ Λ₁^{(0)}, χ_Λ = ∏_X χ_{Λ,X} over the ∗-components X of Λᶜ, with χ_{Λ,X} the indicator of the local run (§3f(3) M4). It is a function of the tests at bonds with both endpoints in X and of 𝔅₀ ∩ X ((4⁗)(d), *Locality in 𝔅₀*). 𝔅₀ is a function of the outer label Λ₁ (Lemma c5-3-0(a)). The earlier reduction of 𝔅₀ ∩ X to R₁ ∩ X (§3f(3) M10) is withdrawn with M10;
  - on the term labelled Λ, every carrier-dependent quantity is a function of Λ near its own support: E^∂_{D(Λ)} through D(Λ) ∩ X for each of its sets X (§3b), and the reference species through Λ near their footprints ((1)(e)).
- So at fixed (Ω₁, Λ₁) the sum over Λ has the form of CRE's sum over Λ₁. The components of Λᶜ are the polymers, each with its own indicator, and every other factor depends on Λ locally. The sum over Λ₁ is CRE's own; whether the later steps accept the pair (Λ₁, Λ) is the D2 item of (4⁗)(d), *The extra label*.
- *Size of the polymers.* Every point of a component X lies within 103ℓ of x_e for a bad bond e (Lemma c5-3-1(c) with 𝒬⁺) or within 100ℓ of CRE's unfilled bad region (Lemma c5-3-0(b)). So Λᶜ ⊂ ⋃_G G^{∼107}, as in §3f(2) Minor 4, and each component carries the factor of its generators ((1.79) for P₁ ∪ Q₁ ∪ R₁; for the bad cubes, R-d″'s joint factor, merged with (1.79)'s per component of the cover, §3f(2) R1 (D2); not reviewed).

**(3) Status.**
- (1) is derived for the reference species (t = 0): exact locality in the carrier, the per-cube bound with the weight e^{3νσ(Γ)/2}, and its diameter form ((d′), decay rate 3ν/(2A_E LM) per fine unit).
- (2) is derived as a reduction: D(Λ) ∩ Y is local in Λ, and at fixed outer (Ω₁, Λ₁) the label indicator χ_Λ factorises over the components of Λᶜ. This rests on §3c(4⁗)(d) and M4, as repaired after the round-4 reports it1-c4q-rep-20261022-r2a, -r2b, -r2c (§3h). M10 is withdrawn.
- Left for D2, recorded there: the carrier dependence of the t > 0 species.
- Not reviewed.

## 3h. Round-4 review results and repairs (reports read 22 Oct; triage in verification/isolated_reviewer/reviews/ROUND4_TRIAGE_20261022.md; repairs written 07:03–07:28, 22 Oct, session log; not reviewed)

No report found anything fatal. Every serious and minor finding below is repaired in the section named, except where a line says OPEN or names a decision for the user.

**(1) it1-rd2-reading-20261022-r1 (reading R-d″ against LFR II p.380, with [16] = UV3).**
- *S1.* R-d″ is a claim about an unprinted proof. p.380 states the factor only for CRE's own R_j-cubes at threshold δ_j. No transcribed page of LFR I, LFR II, CRE or UV3 gives the bound or its proof. The sentences "the threshold enters only through |A(b)| ≥ t" and "p.380 l.43–48 is their only source" are withdrawn (§3f(2) R1).
- **R-d″ derived at 09:39 (§3f(2) R1, (D0)–(D2), at the user's "2(a)"), under reading R-s (accepted by the user at 10:18, "(a)").**
  - The derivation splits off half of each component form. On the support of the bad tests, that half is ≥ c_bϑ²r²|𝒲_X| ((D1)): a localisation lemma ((D-c)) gives it from H ≥ 0 (CRE p.248) and V3's local gap near I ((D-b)).
  - The change of the Gaussian normalisation, 2^{n/2}, is a volume cost in the first exponential of (1.79).
  - R-s, (1.79) for the halved form, is not printed. It was accepted as a logged Bałaban reading at 10:18 and withdrawn at 11:02 after round 5: the insertion is now Hölder's inequality with the printed (1.79) (§3f(2) R1 (D2), rd3-rs S1).
- *S2.* "R-d″ needs none" is withdrawn. The comparison Q_Λ(x′,x) ≥ Q_{Λ₁}(x) written here was withdrawn after round 5 (rd3-rs S2: it compared unsplit forms); R-d″ now uses positivity only through the printed (1.79) (§3f(2), *Positivity used*).
- *Minors m1–m13.* They are applied in §3f(2):
  - g₁ and δ₁ indices (m1);
  - a fixed c > 0 in place of γ₀ (m2);
  - cube side L²M₂R₁ in fine units (m3);
  - the Wilson action is expanded, not a factor (m4);
  - the 𝐁^{(1)} sentence dropped (m5);
  - the overlap 6·5^{d−1} (m6);
  - small g₀|A| on both kinds of cube (m7);
  - p.185 (m8);
  - p₀ > 6𝔯 from (1.88) and the meaning of r (m9);
  - d′+1 (m10);
  - (1.79) says nothing about added generators (m11);
  - the UV3 pages read (m12);
  - p₀(g) inferred, not printed (m13).

**(2) it1-c4t-ii-20261022-r2 (§3c(4‴) + §3f(2)).**
- *S1.* R-d″ was logged for one cube, but (1.82) needs all the bad-cube factors of a component at once, jointly with P, Q, R. R-d″ is restated in joint form (§3f(2) R1). Its status is that of (1).
- *Minors.* Applied:
  - the overlap constant (m1);
  - the P-part of the 6ℓ inclusion: open as a citation (CRE's P₁¹ not read), not as a bound (m2);
  - (1.76) per component (m3);
  - p.383's domain class (m4);
  - the 𝐁^{(1)} sentence dropped (m5);
  - p.256's "other conditions" named as open and deferred to D2 (m6);
  - m7.

**(3) it1-c2-place-20261022-r2 (§3c(2) + §3f(1)).**
- *S-A.* ι_ξ's row indicators depend on V through U₁. Placing them in χ(Ω₁∩Λ₁ᶜ, S₁) would break CRE's V-localisation. Repaired: ι_ξ = 1 on the support of χ₁ζχ_{ξ,e} at admissible pairs, at a new small-g₀ threshold, so it is omitted (§3c(2)(e)). 1_adm is CRE's own implicit domain, covered with reading R-g.
- *M-B.* The off-Λ z-factor is now worded as an analytic, positive, gauge-invariant, row-local function of U₁(V,V₀), with a sup bound of the type on p.383. Its compatibility with the uses of (2.21) beyond (1.79) is a D2 item (gaps block, D2).
- *Minors.* Applied in §3c(2):
  - the integrand bullet;
  - the five placements;
  - reading R-i for E₁;
  - the R-f citation;
  - the unlisted readings, now logged in (d);
  - collar-coverage(ii) off branches;
  - Tonelli/Fubini;
  - V a parameter.

**(4) it1-c4q-rep-20261022-r2a, -r2b, -r2c (§3c(4⁗) + §3f(3)).**
- *r2a S-1.* "Every use" was a list of occurrences. Repaired with the monotonicity principle: every step-1 consumer of T₁'s characteristic functions is an identity, an upper bound of a nonnegative integrand, or a supremum over the support (§3f(3) S1). The LFR I part is restricted to the listed identities.
- *r2b.* No serious finding. Minors m1–m8 are applied in §3c(4⁗) and §3f(3):
  - the round of testing (m1);
  - the total 𝐁 cost (m2);
  - ι_c far rows (m3);
  - 𝔅₀∩X-locality (m4);
  - the whole cutoff (m5);
  - the 𝐁-format from p.258 (m6);
  - the search record (m7);
  - 103ℓ+1 and C_K (m8).
- *r2c S-1.* M10 made Λ₁ an inner label, but the S₁ kernel depends on Λ₁ nonlocally. Repaired: Λ₁ stays an outer label and M10 is withdrawn ((4⁗)(d), §3g(2)).
- *r2c S-2.* χ_Λ factorises on the range Λ ⊂ Λ₁^{(0)}, with 𝔅₀∩X-locality (§3f(3) M3, M4).
- *r2c S-3.* After R-e was dropped, the per-bond cost of 𝐁^{(1)} at retreat boundaries had no support. Repaired: 𝐁^{(1)} is formed at Λ, and its total cost is CRE's (2.48) at Λ, a volume cost paid as on p.380 (§3f(3) M7; (4⁗)(a)).
- *Minors.* r2a m-1 to m-10 and r2c m-1 to m-6 are applied where they are cited in §3c(4⁗) and §3f(3).

**(5) it1-d11-r2 (§3d + §3f(4)).**
- *S-1.* Passed-test good groups on uncovered terms need the endpoint identities (c4-11-6), which L5024 restricts to covered far histories. Repaired in §3d(2): the objects read only bonds inside Q_W ⊂ Λ₁ and no outer variable.
- *Minors m-a to m-j.* Applied:
  - Lemma c5-4-4 is stated on A^fin_cov (m-a, §3d(2)(a));
  - the cost is e^{Cτ²Σ_j e^{−c″d_j}} (m-b, §3d(5));
  - the hypotheses (m-c, §3d(1));
  - g_t from Lemma c5-5R-1(b) (m-d);
  - the torus side via Λ_r, and the all-J sub-case (m-e, §3d(2)(f));
  - the trichotomy dropped (m-f);
  - the stale definitions of d^Λ(n), f and ν_n (m-g: §3d(5), §4);
  - the residuals checked (m-h, §3d(2)(g));
  - N_exp from V3's coverage average, 𝔼[N_exp] ≤ 4(2c_st+1)⁴C_Ln_C(q + N_ret q_ϑ) (m-i, §3d(5));
  - c5-5-2's hypotheses inherited (m-j).

**(6) it1-d-d13-20261022-r2 (§3b).**
- *S1.* C_K was undefined in §3b and clashed with §3f(3)'s C_K. Repaired with the fixed stencil reach c_st = 2L+2, R_K := R_* + 2c_st, and diam K_j ≤ L + 2c_st (§3b(2), (4)).
- *Minors m1–m7.* Applied in §3b:
  - U(Γ) is carrier-independent (m1);
  - X ∩ K_j ≠ ∅ (m2);
  - c_supp (m3);
  - E°_Λ from V3's definitions, without the F_{C,T} branch route (m4);
  - D^{(m)} ⊇ D only (m5);
  - m6;
  - no |X|-weighted bound (m7).

**(7) it1-e-red, it1-e-gauss, it1-e-rest (§3e).**
- *e-red S1, e-rest M1/M2.* At complex backgrounds the per-group factor is e^{C′𝔰ρ₁}, not 1 + O(ρ₁). Repaired: C′ρ₁ ≤ η/8, and the rate 31η/8 becomes 30η/8 in δ*_n, a*_n and in the large-field and wrapping terms ((0), (2)(e), (4), (5)).
- *e-red S2, e-rest S1.* The shift m = −H⁻¹ℓ depends on 𝐔. Repaired in (3.12): translate by the real shift m₀ = m(U₁), so the cutoffs, boxes, reserves, shells and marks are V3's real ones at U₁. The residual tilt −t⟨B,δℓ⟩ is paid in the probe-host potentials, with the threshold ω̃_t, ω̄̃ and the tilt marks 𝔪^δ_Y.
- *e-rest S2.* "Constants at most doubled" breaks 4K_*H_*ϑ_* < 1 and the host budget. Withdrawn. The replacement is repair K′, which takes the constants as sups over the complex ρ₀-neighbourhood 𝒱_{ρ₀} before ϑ_* is chosen ((3.6)). K′ is a V3 change beyond K; the user agreed it for the overhaul (22 Oct, 08:57). It is not made in V3.
- *e-gauss S1.* The identity theorem is now applied on 𝒩 = {dist_op(H, 𝒦) < s_*}, with 𝒦 = real γ ≤ H ≤ h_+ ((3.3)).
- *Minors.* Applied in §3e:
  - e-red m1–m8;
  - e-gauss m1–m10: C_w, the α_G conditions, the scope of γ_c and h_c, the constants C₃, C₄, β^c, C_d^K, c_G^K, s ≤ γ/4 in s_*, the consumers of (i);
  - e-rest M3–M7: the word bounds at the young variable with √2C_π and no dim π, the omissions in the scan, the citations, and M7, which is covered by §3d(1)(d).
- *New g₀-thresholds introduced by these repairs.* Each is a smallness condition on g₀ after V3's constants are fixed, as V3's own thresholds are:
  - ι_ξ ((3) above);
  - C′ρ₁ ≤ η/8;
  - Cρ₁ ≤ ρ₀;
  - C_qg₀(1+r) ≤ 1;
  - s = C_Hρ₁ ≤ s_*;
  - the tilt threshold of (3.12).
  V3's threshold list (L3973) does not contain them yet.

**(8) What round 4 leaves.**
- D1.0(P)(ii) ((1) above): R-d″(i) is derived, and R-d″(ii), the j = 1 factor of (1.79) at step k ≥ N + 1, is derived except for two open D2 items, D2.7 (LFR I's construction of Z from Z_h) and the acceptance item (§3f(2) R1 status; rd5-d2-r4 m-1); both under reading R-c, with R-p (location checked; rates quoted from p.380 (step k ≥ N + 1)) and V3's logged (B1)(iii), (H4) (R-q₀ quoted and checked, recorded, not used; §3f(2) R1; the R-q layer clause withdrawn after rd5-dbq S1; round 5 found the pointwise part correct; since round 6 the labelled integral is bounded factor by factor, without Hölder's inequality or the printed (1.79) at Λ; restated after rd5-d2-r2 S1, not re-reviewed). Its g₀-thresholds: ℓ = LMR₁ large enough that R_ϑ + 2ρ_L + s_𝔓 + 3 + L²M₂R₁ < LMR₁ − 1 (strict, as in collar coverage (i), rd3-pw m3) and R_ϑ + 2ρ_L < ℓ − 2 ((D-b), (D1)); R_ϑ + ρ_L + s_𝔓 + 5 ≤ L²M₂R₁ and 4c_hθ₁ ≤ 1 ((D1⁺)); μ̂′ < τ_L/2 and max(1,c_L)μ̂′ < γ_L/4 ((D-b⁺)); β₀ ≤ 1; ½c₄ϑ²A₁²(log g₁⁻²)^{p₀} ≥ 2 (d2 m8). V3's list (L3973) does not contain them yet.
- Repair K′ ((7)): agreed by the user for the overhaul (22 Oct, 08:57).
- Not reviewed: every repair in this section, and §3g.
- D2 items added: M-B's off-Λ z-factor ((3)); the base points of D1(iii)′ against CRE (2.34)/(2.38) (§3e(0)); the e^{Cτ²} cost per exposed segment ((5)).

## 3i. D2, first item: the thin form of E^∂ (derived 10:33–10:50, 22 Oct, date; reviewed in round 6, it1-rd4-thin1 and it1-rd4-thin2; repairs 12:04–12:13, date; repairs reviewed in round 7, it1-rd5-thin1 and it1-rd5-thin2, no fatal or serious finding; round-7 minors applied by 14:24, date, not reviewed)

**(0) Why it is needed (count check).** At step 2, e^{E^∂_{D(Λ)}} has to enter Bałaban's large-field polymer gas. A Kotecký–Preiss weight a(X) for a defect polymer X must be at least the mass of the large-field polymers that meet X, about ε·#(cubes of X), and at most what its activity pays. §3b's sets X = B_{m+1} have #(cubes) ≍ (m/a₂)⁴ for step-2 cubes of side a₂ (renamed from a, the diameter weight of §3b; thin1-r2 m4) and activity e^{−a₀m}. So ε(m/a₂)⁴ ≤ a₀m fails for large m, whatever ε is, and the available bounds cannot certify the ball decomposition. A bound only of E^∂ would lose the identity of §0. What the KP route needs from a decomposition of E^∂ into thin sets is a rooted bound per step-2 cube. (7) gives one: for a step-2 cube Q of side a₂, Σ_{X∩Q≠∅}|e_X|e^{κ_{a₂}#cubes(X)} ≤ (a₂/ℓ₀+2)⁴C_rτ² ((7), *Rooted form*; round 7, thin1 M-a, thin2 m7). Two comparisons are left to D2.6: of (a₂/ℓ₀+2)⁴C_rτ² with κ_{a₂} (a small-coupling condition when τ² beats a₂⁴), and of κ_{a₂} with the step-2 large-field mass per cube.

**(1) The source of the non-locality.** The regional integrals are Gaussian integrals with covariance C_{D,T} = (i_{D,T}^*H_Ti_{D,T})⁻¹ (V3 (regional-periodic-weight), L1833–1839, the torus analogue of (regional-precision), (regional-integrals), L1696–1718). The cutoff Θ_D^σ and the interaction P_{D,T} are local in D. The precision i_{D,T}^*H_Ti_{D,T} is local in D too. So are the source factor and the restricted free-input supports Λ∩D of L1721 (Λ is V3's free-input support there, not the region Λ of this note; thin1 M-h); the Gaussian normalisation cancels in the normalised ratios (thin1 M5). The non-locality is only in the inverse.

**(2) Bałaban's method for this (RG2 pp.12–14; CRE pp.276–278 describe the same scheme, citing "Sect. 6 [I]" and "(I.7.3)–(I.7.13)"; CRE's [I] is RG I, CMP 109 (CRE reference list, p.285), which has Sects. 0–5 only, so these citations have no target in RG I, and this subsection rests on RG2 directly; thin1 M2).**
- RG2 (2.1)–(2.4): a Mayer expansion of the action density and an expansion of the characteristic functions off the localisation domain, χ_k = Σ_P(−1)^{|P|}χ_{k,Y₀}χ^c_{k,P} (2.3). Each term is localised in a domain Z₀.
- RG2 (2.5)–(2.6): conditioning on Z₀ᶜ, and the change of variables B′ = (C^{(k)})^{1/2}X. The X-measure is the fixed standard Gaussian dμ₀; all dependence on the operators moves into the integrand G.
- RG2 (2.7)–(2.8): generalized random walk expansions of C^{(k)}(Z₀), (C^{(k)})^{1/2} and Δ_k, with parameters s(Δ) per cube, and the localisation Σ_Z Π_{Δ⊂Z∖Z₀′}∫₀¹ds(Δ)∂/∂s(Δ). The activities H(Z) are localised in Z and factorise over components ((2.10)); RG2 (2.12)–(2.13) exponentiate.
- Complex s is admissible on a polydisc on which (i) every complex covariance block is within λ/16 of the real one in operator norm, so that, with V3's forest Cauchy radius halved (L1307), every density argument M has ‖M − M_real‖ ≤ λ/8 and Re M ≥ 7λ/8; and (ii) the complex entries decay exponentially, uniformly on the polydisc (round 7, thin1 M-b). (4) proves (i) for the full matrix, and (ii), for |s_Δ| ≤ R once ℓ₀ ≥ ℓ₀(R, L, G); (5) passes (i) to the interpolated blocks. RG2 pp.12–14 state nothing about complex s. (Round 6, thin1 S1: the earlier bullet "because the X-measure is fixed, … no positivity of an interpolated covariance is needed" was wrong; RG2's G contains dμ_{C^{(k)}(Z₀,s(Z))} and an s-dependent X-form.)

**(3) Plan (carried out in (4)–(7); thin1-r2 m6).**
- (W1) A box walk expansion of every principal-restriction inverse C_{D′}: C_{D′} = Σ_ω c_{D′}(ω), with c_{D′}(ω) := G_{Δ₀}χ_{Δ₀}K_{Δ₁}⋯K_{Δ_n} for ω = (Δ₀, …, Δ_n), each term depending on D′ only near the boxes of its walk ω, with ‖c_{D′}(ω)‖ ≤ γ_L⁻¹ε_w^{|ω|} at s = 1 (names as in (4); thin1-r3 m-b), ε_w small for large boxes (ε_w is the walk constant of (4), renamed from ε₀, which is CRE's g₀p₀(g₀) elsewhere in this note; thin1-r2 m1). It uses only V3's two-sided bound on principal restrictions of H, its finite range and the proof of Lemma c5-1-1.
- (W2) V3's source clusters with every covariance block replaced by its (W1) expansion at complex s(Δ), within λ/16 of the real block (thin1 S1).
- (W3) The localisation of RG2 (2.8): E^∂_D = Σ_jΣ_{X∈𝒳_j^{thin}}e^{thin}_{j,X} over ∗-connected unions X of boxes, e^{thin}_{j,X} depending on D only through D ∩ X, with summed bounds: anchored, Σ_{X∈𝒳_j^{thin}}|e^{thin}_{j,X}|e^{κ#boxes(X)} ≤ Cτ²e^{−c_thd_j} (the names of (6)–(7); 𝒳_j and e_{j,X} are §3b's ball decomposition, for which this bound is not available; thin1-r3 m-b), and rooted, Σ_{X⊇Δ}|e_X|e^{κ#boxes(X)} ≤ C_rτ², by Cauchy estimates in s and the sum over Y ((6), (7)). A pointwise bound per set would carry no entropy control (round 7, thin1 M-f).
- What (W2) needs: V3's cluster bounds with the operators replaced by their s-expanded forms for complex s. Read in V3 L1228–1362, see (5). Bałaban's conditioning step RG2 (2.5)–(2.6) is not needed: V3's clusters are already Gaussian principal marginals on their carriers, with fixed bounded integrands (L1259, L1287).

**(4) (W1): box walk expansion of principal-restriction inverses.**
- *Setting.* H = H_T is the flat torus operator of §3b. It has finite range: "Each map has finite range" (V3 L3477, not in the packets so far). For the compatible tori, L1196 says: "The free-inverse Neumann series \eqref{eq:bulk-neumann-inverse} applies on the compatible tori as well, with the same gap and row-sum bound." (4) needs only H_T(b,c) = 0 for d_T(b,c) > R_H, with R_H independent of the torus (thin1-r3 m-e). R_H denotes this range in V3's metric d_T (L1196): H_T(b,c) = 0 for d_T(b,c) > R_H; R_H depends on L, G and the fixed reconstruction, not on the torus (round 7, thin1 M-c; V3 L1196, last sentence: "All constants below may depend on this metric, G, L, the fixed local reconstruction and χ, but not on the square size or torus volume"; thin1-r2 m5). Every principal restriction H_{AA} has γ_L ≤ H_{AA} ≤ h_L (§3b (Q3), Rayleigh quotient; V3 L1196). By the proof of V3 Lemma c5-1-1 (L2287, Neumann series; it uses only the two-sided bound and the range), ‖(H_{AA})⁻¹(b,c)‖ ≤ γ_L⁻¹e^{−μ_Td_T(b,c)} with μ_T := γ_L/(h_LR_H), for every bond set A (μ_T, not V3's covariance exponent μ, introduced at L1191 and displayed at L1194; thin1 M7, M-c). Put σ(T) := γ_L⁻¹Σ_{t≥T}32(2t+1)³e^{−μ_Tt}; at most 32(2t+1)³ bonds lie at distance t from a bond (as in §3f(2) (D-c)).
- *Boxes.* Fix an integer ℓ₀ ≥ max(R_H + 1, c_supp + 2) (thin1-r3 m-d), chosen after R (see *Constants*; thin1 M-d), with c_supp = R_* + R_K of §3b(2) (the second bound is used only for connectivity in (6), thin2 S1), and partition each coordinate circle into intervals with lengths in [ℓ₀, 2ℓ₀) (the whole circle if its period is < ℓ₀; thin1 M3), and let the boxes Δ be the products of these intervals (thin1-r2 m2). Such interval partitions exist for every period p ≥ ℓ₀: with n := ⌊p/ℓ₀⌋ parts, nℓ₀ ≤ p ≤ n(2ℓ₀ − 1), since (n+1)ℓ₀ − 1 ≤ n(2ℓ₀ − 1) for n, ℓ₀ ≥ 1; the parts get lengths ℓ₀ + r_i with 0 ≤ r_i ≤ ℓ₀ − 1 and Σr_i = p − nℓ₀ ≤ n(ℓ₀ − 1) (thin1-r3 m-d); so this adds no condition. A bond belongs to the box of its initial site. Δ̃ := bonds within ℓ₀ of Δ, Δ̂ := bonds within R_H of Δ̃. Any bond lies in Δ̂ for at most N_nb := 7⁴ boxes (in fact ≤ 5⁴), and a box has at most N_nb boxes within ℓ₀ + R_H of it. N_nb does not depend on ℓ₀. Full-circle intervals only lower these counts; Δ ⊆ Δ̃ and the distance bound below hold by the definition of Δ̃, and the step bound below uses only the upper side bound 2ℓ₀. So no condition on the periods is needed beyond V3's compatible torus (L1191, L1196; thin1 M-g).
- *Parametrix (renamed 𝒢, since P_{D,T} is the interaction of (1); thin1-r2 m3. In (4) 𝒢 is the parametrix, not V3's gauge-fixing term 𝒢 of §3f(2) (D-a); thin1-r3 m-a).* Fix a bond set D′. For each box, G_Δ := (H_{Δ̃∩D′,Δ̃∩D′})⁻¹ extended by zero, χ_Δ := the projection onto 𝔤^{Δ∩D′}, 𝒢 := Σ_ΔG_Δχ_Δ, K_Δ := −1_{D′∖Δ̃}HG_Δχ_Δ.
  - For u supported in Δ̃∩D′, H_{D′D′}u equals H_{Δ̃∩D′}u on Δ̃∩D′, and 1_{D′∖Δ̃}Hu off it. Since Σ_Δχ_Δ = 1_{D′}, this gives H_{D′D′}𝒢 = 1_{D′} − K with K := Σ_ΔK_Δ.
  - K_Δ uses only entries G_Δ(y,z) with z ∈ Δ and y ∈ Δ̃ within R_H of D′∖Δ̃, so d_T(y,z) ≥ ℓ₀ − R_H. By the Schur test, ‖K_Δ‖ ≤ h_Lσ(ℓ₀ − R_H) =: ε_w.
- *Walks.* Fix R ≥ 1 (thin1 M4; (6) takes R ≥ 2). For s = (s_Δ) ∈ ℂ^{boxes} with |s_Δ| ≤ R, put K(s) := Σ_Δ s_ΔK_Δ.
  - The pieces χ_Δf are orthogonal, and K_Δχ_Δf is supported in Δ̂∖Δ̃, which meets each bond for at most N_nb boxes. So ‖K(s)‖ ≤ q := N_nb^{1/2}Rε_w. In the same way ‖𝒢‖ ≤ N_nb^{1/2}γ_L⁻¹.
  - For q < 1 put C_{D′}(s) := 𝒢(1 − K(s))⁻¹ = Σ_{n≥0}𝒢K(s)ⁿ. Expanding K(s)ⁿ gives the walks ω = (Δ₀,…,Δ_n): the term s_{Δ₁}⋯s_{Δ_n}G_{Δ₀}χ_{Δ₀}K_{Δ₁}⋯K_{Δ_n} is nonzero only if consecutive boxes lie within ℓ₀ + R_H. Its (b,c) entry needs b ∈ Δ̃₀ and c ∈ Δ_n.
  - At s = 1, C_{D′}(1) = (H_{D′D′})⁻¹ = C_{D′}, since H_{D′D′}𝒢(1−K)⁻¹ = 1.
  - *Symmetric form.* C^{sym}_{D′}(s) := ½(C_{D′}(s) + C_{D′}(s)ᵀ), with ᵀ the transpose for the real bondwise inner product. It is complex symmetric, and C^{sym}_{D′}(1) = C_{D′}.
- *Locality.* The walk term of ω depends on D′ only through D′ ∩ (Δ̂₀ ∪ … ∪ Δ̂_n), and so does its transpose.
- *Bounds.*
  - ‖C^{sym}_{D′}(s) − C_{D′}‖ ≤ ‖𝒢‖‖(1−K(s))⁻¹ − (1−K)⁻¹‖ ≤ N_nbγ_L⁻¹ε_w(R+1)(1−q)⁻² (resolvent identity).
  - *Range of a walk (chained, after thin1-r3 m-c).* Between arbitrary bonds of consecutive boxes the displacement can reach 6ℓ₀ − 3, so the bound is chained through the intermediate bonds. For n ≥ 1, b ∈ Δ̃₀ lies within ℓ₀ + (2ℓ₀ − 1) = 3ℓ₀ − 1 of a bond x₀ ∈ Δ₀ ∩ Δ̂₁. For 1 ≤ i ≤ n, x_{i−1} ∈ Δ̂_i lies within (ℓ₀ + R_H) + (2ℓ₀ − 1) ≤ 4ℓ₀ − 2 of the next bond x_i ∈ Δ_i ∩ Δ̂_{i+1}, with x_n := c (R_H ≤ ℓ₀ − 1). So d_T(b,c) ≤ 3ℓ₀ − 1 + n(4ℓ₀ − 2) ≤ 5ℓ₀(n+1), which also holds for n = 0, and the (b,c) entry of 𝒢K(s)ⁿ vanishes unless n ≥ d_T(b,c)/(5ℓ₀) − 1. Bounding each entry by the norm of 𝒢K(s)ⁿ, ‖C^{sym}_{D′}(s)(b,c)‖ ≤ N_nb^{1/2}γ_L⁻¹(1−q)⁻¹q^{d_T(b,c)/(5ℓ₀)−1}.
- *Constants.* ε_w ≤ C(ℓ₀)³e^{−μ_Tℓ₀}. For ℓ₀ ≥ ℓ₀(R, L, G), q ≤ e^{−μ_Tℓ₀/2}, ‖C^{sym}_{D′}(s) − C_{D′}‖ ≤ λ/16 with λ = h_L⁻¹, and the entry decay rate log(1/q)/(5ℓ₀) is ≥ μ′ := μ_T/10, independent of R and ℓ₀. All of this holds for every |s_Δ| ≤ R, in particular with s_Δ = 0 off any set of boxes.
- *Alternative prefactor (thin1 M6, not needed below).* The n = 0 terms of C_{D′}(s) and C_{D′} cancel, and the entries of 𝒢K(s)ⁿ, 𝒢Kⁿ vanish for n < d_T(b,c)/(5ℓ₀) − 1. With q ≤ e^{−μ_Tℓ₀/2} this gives ‖C^{sym}_{D′}(s)(b,c)‖ ≤ γ_L⁻¹(1 + 2N_nb^{1/2}(1−q)⁻¹)e^{−μ_Td_T(b,c)/20}, at rate μ_T/20. For q ≤ 1/2 the prefactor is at most γ_L⁻¹(1 + 4N_nb^{1/2}), independent of ℓ₀ and R (thin1 M-e).

**(5) (W2): V3's cluster bounds at C^{sym}_{D′}(s).**
- *How V3's clusters see the covariance.* A label selection J has the carrier A_J (L1253), and its term is ∫F_JG_S dμ_{(C)_{A_J}}, a principal marginal with a fixed bounded integrand (L1259). The forest formula (L1262) differentiates the density p_{C_A(x)} (L1271) in the pair variables x_{bc} at w^F ∈ 𝒦_A. No cutoff or Wilson function is differentiated (L1276). The regional expansion is the same with C_D and restricted supports (L1721). So a cluster weight φ_{D′}(Γ) is a function of the blocks (C_{D′})_{A_γ} of its components, through the densities p_M and the edge entries.
- *Replacement.* Define φ_{D′}(Γ;s) by replacing every block (C_{D′})_{A_γ} with (C^{sym}_{D′}(s))_{A_γ}. Then φ_{D′}(Γ;1) = φ_{D′}(Γ).
- *Conjugation equivariance (thin2 m1).* H_T, principal restriction, inversion, χ_Δ, the indicators 1_{set} and the scalars s_Δ commute with constant Ad_u, and transposition preserves this since Ad_u is orthogonal. So C^{sym}_{D′}(s) commutes with constant Ad, and the τ^{𝟏{|S|=1}} gain (L1327, L1335) and the τ² source loads (L1360) hold at complex s.
- *V3's estimate at the replaced blocks.*
  - Base point: (C_{D′})_{A}(w^F) is real, with λ ≤ · ≤ Λ (L1274). Since w^F is a convex combination of partition matrices, (δ)_A(w^F) is a convex combination of block-diagonal pinchings of δ_A. So with δ := C^{sym}_{D′}(s) − C_{D′}, ‖(δ)_A(w^F)‖ ≤ ‖δ‖ ≤ λ/16 ((4)).
  - Take V3's Cauchy radius (L1307) with 16 in place of 8 and ‖C^{sym}_{D′}(s)(b,c)‖ in place of ‖C_T(b,c)‖. The forest perturbation then has norm ≤ λ/16 (L1309), and the total distance from the real base point is ≤ λ/8.
  - So every M on the Cauchy circles satisfies (marginal-complex-density) (L1311–1315) verbatim, and (marginal-density-majorant) (L1319–1321) holds. The determinant branch is continued from the real base point inside the convex set {M complex symmetric : Re M ≥ 7λ/8} (L1317).
  - (marginal-fixed-forest-bound) (L1327) holds with 16 for 8 and the edge factors ‖C^{sym}_{D′}(s)(b,c)‖ ≤ A′e^{−μ′d_T(b,c)}, A′ := N_nb^{1/2}γ_L⁻¹(1−q)⁻¹q⁻¹.
  - The degree payment (L1339–1342), the counting (L1344–1356), the load series (L1358–1361), the extent weights of §extent-weights and the rooted majorant (L2013–2015) use the edge majorants, the carrier counts, the τ-factors, s_*, q_*, R_*, c_h and the one-mark gain (thin2 m4). Only the edge majorants change. So these steps hold with μ′, A′ in place of V3's covariance exponent μ and prefactor A, and with constants fixed before the coupling. Write Ū(Γ) and η̄ for the resulting pinned-tree majorant and extent rate: Σ_{Γ: j∈J_Γ}Ū(Γ)e^{η̄ℓ(Γ)} ≤ Cτ².
- *Analyticity.* Each component functional is an integral of a fixed bounded function against ∂_Fp_M, with M analytic in s and the uniform majorant above. So φ_{D′}(Γ;s) is analytic on |s_Δ| < R, with |φ_{D′}(Γ;s)| ≤ Ū(Γ) there (the Ursell coefficients do not depend on the covariance).
- *Order of constants.* μ′ = μ_T/10 is fixed by L and the group. V3 fixes its extent rates from the decay exponents alone: the rooted majorant (L2013–2015) is at η′ = μ₁/1024, with μ₁ the edge exponent left after the degree payment and μ₁ ≤ one eighth of the covariance and comparison exponents (L1994–1999). Here η̄ := μ₁′/1024 with μ₁′ ≤ μ′/8 the corresponding exponent (thin2 m3), and it does not depend on A′. Then κ and R ((6)), then ℓ₀ = ℓ₀(R, L, G), then A′, K₁ and the coupling. R and ℓ₀ do not enter μ′ or η̄, so the order is not circular.
- *New coupling threshold (thin2 m2; round 7, thin2 m4).* V3's α′ = μ₁/(1024(1+c_h)) (L1996) is taken at V3's μ₁. Put ᾱ := μ₁′/(1024(1+c_h)), and let K̄₂, C̄′_* be V3's K₂, C′_* re-run at μ′, A′ and the factor 16. g₀ is chosen last so that K̄₂^{s_*}τ ≤ 1/2, C̄′_*τ ≤ 1/4 and C̄′_*τ² ≤ ᾱ/4 (the conditions of V3 L2013 at the new constants); V3's own thresholds stay in force separately. A′ depends on ℓ₀, which is fixed before the coupling. This is a checkable condition on g₀, listed in (7).

**(6) (W3): localisation in the box parameters.**
- *The identity.* Fix a source cluster Γ of 𝒞_{D′}, D′ ∈ {D, T}. On the finite torus, s ↦ φ_{D′}(Γ;s) is analytic on |s_Δ| < R ((5)). The identity behind RG2 (2.8), F(s_Δ=1) = F(s_Δ=0) + ∫₀¹∂_{s_Δ}F ds_Δ in each box parameter, multiplied out over the boxes, gives
  φ_{D′}(Γ) = Σ_Y f_{Γ,D′}(Y), f_{Γ,D′}(Y) := ∫_{[0,1]^Y}∂^Yφ_{D′}(Γ; s_Y, 0_{Yᶜ}) ds_Y,
  over the sets Y of boxes.
- *Which Y occur (admissible Y).* At (s_Y, 0) only walks with Δ₁,…,Δ_n ∈ Y contribute, and an entry (b,c) of a block of Γ needs b ∈ Δ̃₀ and c ∈ Δ_n with b, c ∈ A_Γ. So ∂_{s_Δ} vanishes unless Δ lies on such a walk. Hence f_{Γ,D′}(Y) = 0 unless every box of Y lies on a walk Δ₀, Δ₁, …, Δ_n with Δ̃₀ ∩ A_Γ ≠ ∅ (Δ₀ need not lie in Y), Δ₁, …, Δ_n ∈ Y, consecutive boxes within ℓ₀ + R_H, and Δ_n meeting A_Γ (thin2 m6). Y is *admissible* (for Γ) when every box of Y lies on such a walk; only admissible Y occur (round 7, thin2 m6).
- *The set (rewritten after round 6, thin2 S1 and m11).* Let B₀(Γ) be the boxes Δ₀ with Δ̃₀ ∩ A_Γ ≠ ∅. Let 𝒩(Γ) be V3's support network of Γ (L1437): the carrier A_Γ, lattice paths for the edges of a spanning tree of F_γ ∪ Q_{J_γ} for each component γ, the attachment paths (length ≤ R_*) of the source contacts, and the fine contour bonds of the intervals h_W of the webs of Γ. The choices are fixed by a rule that depends only on the index of Γ: the lexicographically first spanning tree in a fixed order of the bonds, and, for each tree edge and for each contact to the nearest bond of its restricted stencil, the lexicographically first shortest lattice path. The counts in *Size* and the connectivity below hold for every such choice (round 7, thin2 m2). X(Γ,Y) = X_{D′}(Γ,Y) is the union of the boxes that contain a bond of supp Γ (§3b(2)), of 𝒩(Γ), or of Δ̂ for some Δ ∈ Y ∪ B₀(Γ). Here A_Γ, B₀(Γ) and 𝒩(Γ) are those of Γ as a cluster at the carrier D′ of the term: the D′-restricted carrier and stencils (L1721, L1992; "the restricted support network", L2006). So X_{D′}(Γ,Y) depends on D′ only through D′ ∩ supp Γ (the web intervals are geometric, L1992). For a D-interior Γ (supp Γ ⊆ D, §3b(2)) the restricted objects at D are the original ones, which are those at T, so X_D(Γ,Y) = X_T(Γ,Y) (thin2-r2 m-1; the earlier "defined from Γ and Y alone" is withdrawn).
  - *Locality.* By (4) (Locality) and §3b(2), f_{Γ,D′}(Y) and the indicator Γ ∈ 𝒞_{D′} depend on D′ only through D′ ∩ (supp Γ ∪ ⋃_{Δ∈Y∪B₀(Γ)}Δ̂) ⊆ D′ ∩ X(Γ,Y).
  - *Connectivity.* Connected means ∗-connected: two boxes are ∗-adjacent when they contain sites at ℓ∞ distance ≤ 1. The boxes containing the bonds of a lattice-connected bond set form a ∗-connected family, since consecutive bonds of a lattice path have initial sites at ℓ∞ distance ≤ 1.
    - 𝒩(Γ) is lattice-connected: "in a cluster, incompatible objects meet through carriers or contour intervals, so these networks form a connected union" (V3 L1437).
    - Each Δ̂ (the bonds within ℓ₀ + R_H of a box) is lattice-connected. For Δ₀ ∈ B₀(Γ), Δ̂₀ ⊇ Δ̃₀ meets A_Γ ⊆ 𝒩(Γ).
    - Each Δ ∈ Y lies on a walk Δ₀ ∈ B₀(Γ), Δ₁, …, Δ_m = Δ with Δ₁, …, Δ_m ∈ Y and nonzero term (*Which Y occur*). The output of K_{Δ_{i+1}} lies in Δ̂_{i+1} and meets the input box Δ_i, so Δ̂_i ∩ Δ̂_{i+1} ⊇ Δ_i ∩ Δ̂_{i+1} ≠ ∅.
    - Every label of a nonzero cluster at D′ has nonempty restricted support inside A_Γ, the D′-restricted carrier of *The set* (thin2-r3 m-a): primitives in 𝒱_{D′} meet D′ (V3 L1700), cutoff labels lie in D′ (Θ_{D′} is a product over b ∈ D′, L1701), and "A source mark with empty restricted stencil is zero" (L1721). With original label diameters ≤ R_* and stencil diameters ≤ 2c_st, every bond of supp Γ therefore lies within c_supp of A_Γ (§3b(2)). Since ℓ₀ ≥ c_supp + 2, its initial site is within ℓ∞ distance < ℓ₀ of the initial site of a carrier bond. Boxes have sides ≥ ℓ₀ or are full circles, so the two boxes are equal or ∗-adjacent.
    So X(Γ,Y) is ∗-connected. (The earlier X, without 𝒩(Γ), need not be: components inside a web have disjoint carriers, V3 L1294 (round 7, thin2 m1), and meet only through contour intervals, L1437.)
  - *Unchanged consequences.* Enlarging X keeps the locality, the cancellation below (X ⊆ D still forces supp Γ ⊆ D and every Δ̂ used ⊆ D), and "nonzero ⇒ X ∩ Dᶜ ≠ ∅".
- *Size (thin2 S1, m7).* A bond lies in one box.
  - supp Γ: Γ has at most q_*|A_Γ| labels, A_Γ the D′-restricted carrier (at most q_* labels meet a bond, L1259, and every label meets A_Γ by *Connectivity*; thin2-r3 m-a), each with at most s_* bonds and at most one marked stencil (of its source traversal), of at most C(c_st) bonds (diameter ≤ 2c_st, §3b(2)). With |A_Γ| ≤ Σ_γ|A_γ| ≤ ℓ(Γ) (ℓ(γ) = |A_γ| + Σ_{F_γ}d_T(b,c), L1368, §3b(1)), the boxes meeting supp Γ number at most C_sℓ(Γ), C_s = C(s_*, q_*, c_st).
  - 𝒩(Γ): at most C_netℓ(Γ) bonds, C_net = 8(1+R_*)(1+q_*+c_h) (L1437; the web intervals cost Σ_W(H_W+1) ≤ (c_h+1)ℓ(Γ) by L1378–1382).
  - |B₀(Γ)| ≤ N_nb|A_Γ| ≤ 2N_nbℓ(Γ), and each Δ̂ meets at most N_nb boxes.
  - So #boxes(X(Γ,Y)) ≤ N_nb|Y| + C₀ℓ(Γ), with C₀ := C_s + C_net + 2N_nb². C₀ depends on L, G and V3's fixed constants and not on ℓ₀.
- *Bound.* For s ∈ [0,1]^Y and 0 < ρ < R − 1 the closed polydisc of radius ρ around s lies in |s_Δ| < R. By Cauchy's estimate and (5), |∂^Yφ_{D′}(Γ; s_Y, 0)| ≤ ρ^{−|Y|}Ū(Γ); letting ρ ↑ R − 1 (thin2 m5), |∂^Yφ_{D′}(Γ; s_Y, 0)| ≤ (R−1)^{−|Y|}Ū(Γ). So |f_{Γ,D′}(Y)| ≤ (R−1)^{−|Y|}Ū(Γ).
- *The decomposition of E^∂ (pairing restated after thin2-r2 m-1).* By §3b (Q1), (Q2), E^∂_D = Σ_{Γ∈𝒞_D}φ_D(Γ) − Σ_{Γ∈𝒞_T}φ_T(Γ) = Σ_Y[Σ_{Γ∈𝒞_D}f_{Γ,D}(Y) − Σ_{Γ∈𝒞_T}f_{Γ,T}(Y)].
  - *Paired terms.* A D-interior Γ lies in both families with the same index (§3b(2)), and X_D(Γ,Y) = X_T(Γ,Y) =: X(Γ,Y). Put t_{Γ,Y} := f_{Γ,D}(Y) − f_{Γ,T}(Y), with the set X(Γ,Y). If X(Γ,Y) ⊆ D, every walk term used and every G_{Δ₀} is the same at D and at T, since D ∩ Δ̂ = Δ̂ = T ∩ Δ̂ for the boxes involved. So t_{Γ,Y} = 0, and every nonzero paired term has X(Γ,Y) ∩ Dᶜ ≠ ∅.
  - *Unpaired terms.* For Γ not D-interior, t_{Γ,Y,D} := 1{Γ∈𝒞_D}f_{Γ,D}(Y) with the set X_D(Γ,Y), and t_{Γ,Y,T} := −1{Γ∈𝒞_T}f_{Γ,T}(Y) with the set X_T(Γ,Y). Each set contains the boxes of supp Γ, and supp Γ ⊄ D, so it meets Dᶜ.
  - Each term depends on D only through D ∩ (its set): f_{Γ,D}(Y) by *Locality*; the indicator 1{Γ∈𝒞_D} (§3b(2): the labels whose original support meets D), the set X_D(Γ,Y) and whether Γ is D-interior through D ∩ supp Γ; and the boxes of supp Γ lie in the set.
  - Each term is bounded by |f_{Γ,D}(Y)| + |f_{Γ,T}(Y)| or by one of them, and its set obeys *Size* at its own carrier, so the summation below is unchanged.
- *Anchoring and summation.* Allocate (Γ,Y) to j ∈ J_Γ with weight |J_Γ|⁻¹, as in §3b(4); the set of each term meets K_j, since supp Γ does. Let 𝒳_j^{thin} be the sets so produced from the nonzero terms (paired and unpaired, thin2-r2 m-1), so that every member meets Dᶜ, and e^{thin}_{j,X} the allocated sums (round 7, thin2 m6).
  - *Box graph.* Boxes Δ, Δ′ are adjacent when Δ′ meets Δ̂; this is symmetric, and each box has at most N_nb neighbours. A connected set of k boxes containing a given box has a spanning tree whose depth-first closed walk has 2(k−1) steps, so there are at most N_nb^{2(k−1)} such sets (the count V3 uses for its cubes, L3550).
  - *Admissible Y.* Split Y = (Y ∩ B₀) ⊔ (Y ∖ B₀). For Δ ∈ Y ∖ B₀ on a walk Δ₀ ∈ B₀, Δ₁, …, Δ_m = Δ, let i < m be the last index with Δ_i ∈ B₀; then Δ_{i+1}, …, Δ_m is a path in Y ∖ B₀ and Δ_{i+1} is adjacent to B₀. So each component of Y ∖ B₀ contains a box u of ∂B₀ := {boxes outside B₀ adjacent to B₀}, with |∂B₀| ≤ N_nb|B₀| (∂B₀ was N(B₀) before round 7, thin2 m6). Assigning to each component its first such u (in a fixed order of the boxes) is injective, so for 0 < w ≤ 1/(2N_nb²)
    Σ_{Y admissible} w^{|Y|} ≤ (1+w)^{|B₀|}·Π_{u∈∂B₀}(1 + Σ_{k≥1}N_nb^{2(k−1)}w^k) ≤ (1+w)^{|B₀|}(1+2w)^{N_nb|B₀|} ≤ e^{3wN_nb|B₀|} ≤ e^{6wN_nb²ℓ(Γ)}.
  - *Choice of κ and R.* κ := η̄/(4C₀ + 4), so 2κC₀ ≤ η̄/2. Then R ≥ 2 with w := (R−1)^{−1}e^{2κN_nb} ≤ η̄/(24N_nb²) (≤ 1/(2N_nb²), as η̄ < 1). With #boxes(X(Γ,Y)) ≤ N_nb|Y| + C₀ℓ(Γ),
    Σ_{Y admissible}(R−1)^{−|Y|}e^{2κ#boxes(X(Γ,Y))} ≤ e^{2κC₀ℓ(Γ)}Σ_{Y admissible}w^{|Y|} ≤ e^{(η̄/2 + η̄/4)ℓ(Γ)} ≤ e^{η̄ℓ(Γ)}.
  - So Σ_{X∈𝒳_j^{thin}}|e^{thin}_{j,X}|e^{2κ#boxes(X)} ≤ Σ_{Γ∈𝒞_D, j∈J_Γ}Ū(Γ)e^{η̄ℓ(Γ)} + Σ_{Γ∈𝒞_T, j∈J_Γ}Ū(Γ)e^{η̄ℓ(Γ)} ≤ 2Cτ², by |t_{Γ,Y}| ≤ |f_{Γ,D}(Y)| + |f_{Γ,T}(Y)| (thin2 m8) and V3's pinned-tree summation at the extent rate η̄ ((5)), once at D and once at T (round 7, thin2 m5). C absorbs the 2 below.
  - *Decay in d_j.* A ∗-connected X meeting K_j and Dᶜ has #boxes(X) ≥ d_T(K_j,Dᶜ)/(2ℓ₀) ≥ d_T(K_j,Dᶜ)/(4ℓ₀) − 1, since a ∗-chain of n boxes of side < 2ℓ₀ spans ℓ∞-distance at most 2nℓ₀. Spending half of the weight, Σ_{X∈𝒳_j^{thin}}|e^{thin}_{j,X}|e^{κ#boxes(X)} ≤ e^{−κ min#boxes}·Cτ² ≤ e^{κ}Cτ²e^{−κd_j/(4ℓ₀)}, with d_j = d_T(K_j,Dᶜ) − R_0 ≤ d_T(K_j,Dᶜ).
  - *Near a segment (thin2 m10; the analogue of §3b(4)).* Put c_th := κ/(4ℓ₀). Let X ∈ 𝒳_{j′}^{thin} with d_T(X, K_j) ≤ R_0. X is ∗-connected and meets K_{j′} and Dᶜ, so with d_{j′}^+ := max(d_{j′},0), #boxes(X) ≥ d_T(K_{j′},Dᶜ)/(2ℓ₀) ≥ d_{j′}^+/(2ℓ₀) and #boxes(X) ≥ (dist(K_j,K_{j′}) − R_0)/(2ℓ₀). Splitting e^{−κ#boxes(X)} into two halves, e^{κ#boxes(X)} ≤ e^{2κ#boxes(X)}e^{c_thR_0}e^{−c_th(d_{j′}^+ + dist(K_j,K_{j′}))} (round 7, thin2 m3: d_{j′} can be negative).
    - d_j ≤ d_{j′}^+ + dist(K_j,K_{j′}) + diam K_{j′} and diam K_{j′} ≤ L + 2c_st (§3b(4)). Using d_{j′}^+ ≥ 0 in the second half, e^{−c_th(d_{j′}^+ + dist(K_j,K_{j′}))} ≤ e^{(c_th/2)(L+2c_st)}e^{−(c_th/2)d_j}e^{−(c_th/2)dist(K_j,K_{j′})}.
    - With the bound Σ_{X∈𝒳_{j′}^{thin}}|e^{thin}_{j′,X}|e^{2κ#boxes(X)} ≤ Cτ² above,
      Σ_{j′}Σ_{X∈𝒳_{j′}^{thin}, d_T(X,K_j)≤R_0}|e^{thin}_{j′,X}|e^{κ#boxes(X)} ≤ Cτ²e^{c_thR_0 + (c_th/2)(L+2c_st)}e^{−(c_th/2)d_j}Σ_{j′}e^{−(c_th/2)dist(K_j,K_{j′})}.
    - The number of j′ with dist(K_j,K_{j′}) < r is at most C(1+r)⁴ (§3b(4), the shell count of L2028), so the last sum is bounded uniformly in n and the torus. The near-segment bound holds with rate c_th/2.

**(7) Result (not reviewed).** E^∂_D = Σ_jΣ_{X∈𝒳_j^{thin}}e^{thin}_{j,X}, where each X is a ∗-connected union of boxes of side in [ℓ₀, 2ℓ₀) (or full circles in a direction of period < ℓ₀), meets K_j and Dᶜ, and e^{thin}_{j,X} depends on D only through D ∩ X, with
- Σ_{X∈𝒳_j^{thin}}|e^{thin}_{j,X}|e^{2κ#boxes(X)} ≤ Cτ² ((6), *Anchoring and summation*);
- Σ_{X∈𝒳_j^{thin}}|e^{thin}_{j,X}|e^{κ#boxes(X)} ≤ Cτ²e^{−c_thd_j}, c_th := κ/(4ℓ₀).
- *Range of D (round 7, thin2 m8; thin2-r2 m-2).* D is any carrier D ⊆ D₊, covered or not, with D₊ of V3 L1908 (the bonds of the free carrier E_{Ω,*} with at least one endpoint in Λ₁). So D₊ = I = Λ₁^* of V3 L2260 ("the free bonds with an endpoint in Λ₁"), and the range contains I and every retreated D(Λ) ⊆ I. The earlier qualifier "with the collar" is dropped: (5)–(6) do not use it (thin2-r3 m-b). (Q1), (Q2) and the rooted majorant hold at covered carriers by §3b, and at uncovered ones by §3d(2)(g), (h), at their stated status. The bounds of (6) hold for every j, whatever the sign of d_j (thin2-r3 m-b). For instance, if d_T(K_j, Dᶜ) = 0 (a segment j meeting Dᶜ), then d_j = −R_0 ≤ 0 under (6)'s definition, and the anchored bound is at most e^{c_thR_0}Cτ², absorbed in C; "Same index" of §3b(1) needs no coverage.
- *Rooted form (round 7, thin1 M-a, thin2 m7).* Put e_X := Σ_je^{thin}_{j,X}. Let Δ be a box and X ∈ 𝒳_j^{thin} with Δ ⊆ X. X is ∗-connected and meets K_j, so #boxes(X) ≥ dist(Δ,K_j)/(2ℓ₀), by the span bound of (6) (*Decay in d_j*). Spending half of the weight of the first bound,
  Σ_{X⊇Δ}|e_X|e^{κ#boxes(X)} ≤ Cτ²Σ_je^{−κ·dist(Δ,K_j)/(2ℓ₀)} ≤ C_rτ².
  - The last sum: fix a bond b_Δ with initial site in Δ. If dist(Δ,K_j) < r, some bond of segment j lies within r + 2ℓ₀ + c_st of b_Δ (diam Δ < 2ℓ₀; every point of K_j is within c_st of a bond of segment j, §3b(4)). Distinct segments contain distinct contour bonds, and periodic shells are at most the infinite-lattice shells (L2028), so the number of such j is at most C(1 + r + 2ℓ₀ + c_st)⁴. Hence Σ_je^{−κ·dist(Δ,K_j)/(2ℓ₀)} ≤ Σ_{r≥0}C(2 + r + 2ℓ₀ + c_st)⁴e^{−κr/(2ℓ₀)}, and C_r depends on κ, ℓ₀, L, c_st only, uniformly in n and the torus.
  - Per step-2 cube: an interval of length a₂ meets at most a₂/ℓ₀ + 2 box intervals (sides ≥ ℓ₀, or one full circle), so at most (a₂/ℓ₀ + 2)⁴ boxes meet a cube Q of side a₂ (the boxes are products of intervals, (4)). With κ_{a₂}#(cubes of X) ≤ κ#boxes(X) (*Against (0)*), Σ_{X∩Q≠∅}|e_X|e^{κ_{a₂}#(cubes of X)} ≤ (a₂/ℓ₀ + 2)⁴C_rτ².
- κ, ℓ₀, C, C_r, c_th depend on L, G and V3's fixed constants only, and are fixed before the coupling. Uniform in n and the torus.
- *Against (0):* a box of side < 2ℓ₀ meets at most (2ℓ₀/a₂ + 2)⁴ cubes of side a₂, so for Bałaban's step-2 cubes, of side a₂, #(cubes of X) ≤ (2ℓ₀/a₂ + 2)⁴#boxes(X) and e^{−κ#boxes(X)} ≤ e^{−κ_{a₂}#(cubes of X)}, κ_{a₂} := κ(2ℓ₀/a₂ + 2)^{−4}. This needs no order between M and ℓ₀, and κ_{a₂} ≥ κ(2ℓ₀ + 2)^{−4} for a₂ ≥ 1, fixed before the coupling even if a₂ depends on g. With the *Rooted form*, the defect polymers have the per-cube rooted bound of (0). What D2.6 still has to check is the comparison of (a₂/ℓ₀ + 2)⁴C_rτ² with κ_{a₂}, and of κ_{a₂} with the step-2 large-field mass per cube.
- *Inputs used (at their stated status; round 7, thin2 m8):* the two-sided bound and range of H_T on every principal restriction (§3b (Q3); V3 L1196, L3477); Lemma c5-1-1's proof; V3's integrated density estimate, support network (L1437) and pinned-tree summation (L1303–1438, L2013–2015) at the replaced blocks ((5)); §3b (Q1), (Q2); §3b(1)–(2): index locality, supp Γ within c_supp of A_Γ, the same index for D-interior clusters; V3 L1721 (restricted free-input supports) and L1992 (geometric web intervals); the segment count of §3b(4) and the shell count L2028; §3d(2)(g), (h) for uncovered D; (4) itself in (5) and (6); RG2's localisation identity. No new hypothesis; no condition on the torus periods beyond V3's compatible torus ((4) Boxes, thin1 M3, M-g).
- *New conditions (thin2 m2, m4), all checkable and fixed before or with the coupling:* R ≥ 2 with (R−1)^{−1}e^{2κN_nb} ≤ η̄/(24N_nb²) ((6)); then ℓ₀ ≥ max(R_H + 1, c_supp + 2) and ℓ₀ ≥ ℓ₀(R, L, G) ((4)); g₀ chosen last with K̄₂^{s_*}τ ≤ 1/2, C̄′_*τ ≤ 1/4, C̄′_*τ² ≤ ᾱ/4 ((5)), V3's own thresholds in force separately.
- *Relation to §3b.* §3b's ball decomposition stays correct; for D2 the thin form replaces it. The near-segment bound of §3b(4) holds for the thin form with rate c_th/2 ((6), *Near a segment*).
- *Check.* Summing over j gives |E^∂_D| ≤ Cτ²Σ_je^{−c_thd_j}, V3's bound with a smaller rate.
- *Open in this item:* none found. Reviewed in round 6 (it1-rd4-thin1, it1-rd4-thin2, 22 Oct): no fatal finding; thin1 S1 ((2), complex s) and thin2 S1 (connectivity of X) and all minors repaired as marked. The repairs were reviewed in round 7 (it1-rd5-thin1, it1-rd5-thin2, 22 Oct): no fatal and no serious finding; the minors (thin1 M-a to M-h, thin2 m1 to m8) are applied as marked. The round-7 edits were reviewed in round 9 (it1-rd5-thin1-20261022-r2, it1-rd5-thin2-20261022-r2): correct and sufficient, no fatal or serious finding. Applied 17:43–17:49, 22 Oct (date), not reviewed: thin1-r2 m1 (walk constant ε_w), m2 (boxes as products of interval partitions), m3 (parametrix 𝒢), m4 (step-2 cube side a₂), m5 (V3 L1196 for R_H), m6 (wording); thin2-r2 m-1 by the reviewer's alternative (only D-interior clusters paired; the others keep their own sets X_D, X_T; no constant changes), m-2 (D₊ of V3 L1908; d_j = −R_0 at exposed segments). The comparisons named in *Against (0)* belong to D2.6.

## 3j. D2, second item: carrier dependence of the t > 0 species (derived 22 Oct, 12:13–12:24, between the date readings 12:12:44 and 12:24:31; (5)–(7) revised after 12:44, by the date reading 12:53:25; round-7 repairs (tj1, tj2) after 14:11; repairs not reviewed)

**(0) What is needed.** By §3g(2), on the term labelled Λ every carrier-dependent factor must depend on Λ only near its own support; then the label sum is CRE's polymer sum. The reference species are exactly local (§3g(1)). The t > 0 species (Υ¹_W, the terms of 𝓑^Λ) and the leading word f_ξ(m) = W_χ(C;U_ξ(m)) (§2) read the carrier through the mean shift m = −H⁻¹ℓ_Λ, with H := H_{D(Λ)D(Λ)} and ℓ_Λ := H_{D(Λ)J(Λ)}A^{Λ,Ψ} (V3 L2479, L2484). m depends on all of D(Λ). Every other carrier dependence of the t-family is local: C_{E₀}, Γ_{E₀}(σ), hosts, probe hosts (§3g(1)(a) at t = 0; Lemma c5-4-0(d), L2491), and at t > 0 the near primitives, which are evaluated at a = B + tm̂ and read A^{Λ,Ψ} only on their own inputs (rd5-tj1 M1). The reference species are exactly local per group or cluster (a^D_W, w°_D(W), Φ°_D(Γ)); q°_Λ and S°_Λ are cluster sums, local in the cluster form of §3g(1)(d′). For the contour-wide factors (f_ξ(m̂) and the words U_j) the support is the contour: by (2) they depend on Λ only through D(Λ) and A^{Λ,Ψ}|_{J₁(Λ)} within R_N of C. How such a factor with fixed support enters the label sum (the sum over Λ near C, with the per-cube label weight) is not derived. It is an open D2 item, listed in the gaps block and routed to D2.6 (rd5-tj1 M1; tj1-r2 m3, which found that the earlier pointer to §3c(4⁗)(d) does not say this).
- *Weakest form.* Exact locality within a finite range R_t(g₀) that is small against the polymer weights of the label sum ((6)). §3g(2)'s factorisation is an identity that uses exact locality; a decaying dependence would need an extra decoupling expansion. The cutoffs χ^t_b, which are indicators in B + tm, rule out Cauchy-estimate localisation in V3's translated representation. (1)–(4) give exact locality with an exact tilt instead (rd5-tj1 M1; the earlier reason, "the label indicators … are not analytic in m", is withdrawn).
- *Method.* Translate by a local real shift m̂ instead of m, and put the remaining linear term into the host potentials as a tilt. This is §3e(3.12)'s device at the real background.

**(1) The local shift.**
- *Parametrix.* §3i(4) uses only a two-sided bound and a finite range on every principal restriction. H has γ ≤ H ≤ h_+ with γ = γ_L/2, h_+ = m_L, and entry range ρ_L, on every principal restriction (Lemma c5-4-0(a), L2491; (I1)–(I3)). So §3i(4) applies at D′ = D(Λ), with (γ, h_+, ρ_L, μ_H) in place of (γ_L, h_L, R_H, μ_T), at s = 1 (R = 1). Fix once a partition of the torus sites into boxes with sides in [ℓ_s, 2ℓ_s), ℓ_s ≥ ρ_L + 1, independent of Λ (rd5-tj1 M2). It gives P and K = Σ_ΔK_Δ with HP = 1 − K.
- *Row sums.* Each K_Δ has row sums ≤ ε_s := m_Lσ_H(ℓ_s − ρ_L), with σ_H(T) := γ⁻¹Σ_{t≥T}32(2t+1)³e^{−μ_Ht}: (I2) bounds the row sums of H by m_L, and the proof of Lemma c5-1-1, which uses only (I3) for the block and (I1), bounds the entries of G_Δ (rd5-tj1 M2). A bond lies in Δ̂ for at most N_nb boxes, so ‖K‖_{∞→∞} ≤ q_s := N_nbε_s. Fix ℓ_s = ℓ_s(L, G) with q_s ≤ e^{−μ_Hℓ_s/2}.
- *Truncation.* For N ≥ 0 put m̃ := −PΣ_{n=0}^{N}Kⁿℓ_Λ. Then Hm̃ + ℓ_Λ = K^{N+1}ℓ_Λ =: δ_N. Since P = H⁻¹(1 − K), m̃ = −H⁻¹(1 − K^{N+1})ℓ_Λ = m + H⁻¹δ_N.
- *Clipping.* m̂_b := m̃_b·min{1, r/(4|m̃_b|_σ)} for b ∈ D(Λ). Then |m̂_b|_σ ≤ r/4. Since |m_b|_σ ≤ r/4 ((c5-4-1)), |m̂_b − m̃_b|_σ ≤ (|m̃_b|_σ − r/4)₊ ≤ |m̃_b − m_b|_σ.

**(2) Locality.** A walk term of PKⁿ moves at most 5ℓ_s per step and depends on D(Λ) only near its boxes (§3i(4) *Locality*). ℓ_Λ(c) depends on D(Λ) and on A^{Λ,Ψ} within ρ_L of c, and on A^{Λ,Ψ}|_{J₁(Λ)} only (Lemma c5-1-2). Put R_N := 5ℓ_s(N+2) + 2ρ_L: 5ℓ_s(n+1) ≤ 5ℓ_s(N+1) for a walk entry of PKⁿ, n ≤ N; ℓ_s + ρ_L for the box enlargement Δ̂; ρ_L for ℓ_Λ; in total ≤ 5ℓ_s(N+2) + 2ρ_L (rd5-tj1 M2). Then m̃_b, m̂_b and δ_N(b) depend on Λ only through D(Λ) and A^{Λ,Ψ}|_{J₁(Λ)} within distance R_N of b. They vanish unless d(b, J₁(Λ)) ≤ R_N, since ℓ_Λ is supported within ρ_L of J₁(Λ). The clipping is bondwise and keeps this.

**(3) Sizes.** sup_c h(ℓ_Λ(c)) ≤ c_ℓϑr with c_ℓ := 4(2ρ_L+1)⁴m_L, from the entry and count bounds in the proof of Lemma c5-5-1 (L2620). Hence:
- sup_b h(δ_N(b)) ≤ q_s^{N+1}c_ℓϑr;
- sup_b h(m̃_b − m_b) = sup_b h((H⁻¹δ_N)(b)) ≤ γ⁻¹N_lat(μ_H)q_s^{N+1}c_ℓϑr (Lemma c5-1-1; the lattice count of Lemma c5-1-2);
- so |m̂_b − m_b|_σ ≤ 2c_hγ⁻¹N_lat(μ_H)c_ℓϑr·q_s^{N+1} =: ε_N for every b (c_h of Remark c5-1-3);
- since m̂_b = 0 when d(b,J₁(Λ)) > R_N: h(m̂_b) ≤ h(m_b) + ε_N𝟏{d(b,J₁(Λ)) ≤ R_N};
- δ̂ := Hm̂ + ℓ_Λ = δ_N + H(m̂ − m̃). With (I2), sup_b h(δ̂(b)) ≤ q_s^{N+1}c_ℓϑr + m_Lε_N ≤ C_shϑr·q_s^{N+1}, C_sh := c_ℓ(1 + 2c_hm_Lγ⁻¹N_lat(μ_H)). δ̂ vanishes unless d(b,J₁(Λ)) ≤ R_N + ρ_L.

**(4) The t-family at m̂.**
- *Identity.* Put a = B + tm̂ in (c5-4-2) (L2507). Then
  −½⟨a,Ha⟩ − t⟨a,ℓ_Λ⟩ = −½⟨B,HB⟩ − t⟨B,δ̂⟩ − t²(½⟨m̂,Hm̂⟩ + ⟨m̂,ℓ_Λ⟩).
  The constant is the same in the numerator and the denominator of every ratio (c5-4-3) and is never estimated (L2513), so it cancels. The values of all normalised quantities are unchanged. Their expansion changes, and the species become new functions: Υ¹_W, the terms of 𝓑^Λ, and the leading word f_ξ(m̂) in place of f_ξ(m). From here on §2's bracket and D1 are read at m̂ (rd5-tj1 M4). m̂ is real and does not depend on t.
- *Cutoffs and pointwise uses.* χ̂^t_b(B) := 𝟏{|B_b + tm̂_b|_σ < r} and 𝐖̂_t(Y,B) := 𝐕^Λ_{ξ,t}(Y, B + tm̂). (c5-4-1) holds for m̂ by (1). V3's pointwise uses of m therefore hold verbatim with m̂: the boxes, the reserves (1 − t|m_b|_σ/r)²a_bad (L2557), the shells ϖ_b ≤ C_Vr^{d_G−1}|m_b|_σ (Lemma c5-5-5, which holds for any real tilt, L2696) and the bond marks. They use only |m_b|_σ ≤ r/4 and the value at b.
- *The tilt.* As in §3e(3.12): W̃_t(Y,B) := 𝐖̂_t(Y,B) − t·Π_{b′∈E(Y)}χ̂^t_{b′}(B)·Σ_{b:Y_b=Y}⟨B_b, δ̂(b)⟩. On Θ̂^t's support, Σ_YW̃_t = Σ_Y𝐖̂_t − t⟨B,δ̂⟩, so the identity is exact. Every b with δ̂(b) ≠ 0 lies in D(Λ), so its probe host Y_b ∈ 𝐃₀(Λ) exists (L2636). The tilt part of W̃_t(Y,·) depends on B|_{E(Y)} (b ∈ E(Y_b)), so the polymer-lemma inputs (i), (ii) of L2531 hold. On the translated box |B_b|_σ < 5r/4, so the tilt part is at most τ̂_N := 5C_σ(4M+2)⁴C_shϑr²·q_s^{N+1}, and |W̃_t(Y,B)| ≤ ω̂_te^{−κd₀(Y)} with ω̂_t := ω_t + e^{κ(B_h+4)}τ̂_N. ω̂_t ≤ ω_*/2 is a g₀-threshold once N = N(g₀) of (6) is fixed (rd5-tj1 M4).
- *Tilt marks.* 𝔪^{δ̂}_Y ≤ Ĉ^δ_bd r Σ_{b:Y_b=Y}h(δ̂(b)) with Ĉ^δ_bd := (5/4)C_σ·2e·e^{κ(B_h+4)}e^{1/8}/ω_*, nonzero only for hosts within R_N + ρ_L of J₁(Λ). (3.12)'s C^δ_bd contains C_δ and is not this constant (rd5-tj1 M3, rd5-tj2 m10).
- *The source-insertion expansion (V3 §c5-5 and Lemma c4-7-1) with W̃_t (finite check after rd5-tj1 S1; V3 L2624–2735, L2853–2950, L4684–4706 read 22 Oct after 14:11, date; L2736–2852 and L2951–2971 added after tj1-r2 m6: Lemmas c5-5-7z, c5-5-7, c5-5-8, Prop. c5-5-9, Cor. c5-5-10 and Remark c5-5-11 use the host potentials only through the mark constants C_bd, C′_bd and the tilt-mark constant, treated in (c)).* V3 uses the host potentials there in five ways, and each holds with W̃_t:
  - (a) the host bound |𝐖_t| ≤ ω_te^{−κd₀(Y)} ≤ A_Y := (ω_*/2)e^{−κd₀(Y)} on the host's box: in Lemma c5-5-2(b) (the Mayer factor ω_*e^{1/2}e^{−κd₀}), Lemma c5-5-2(c) (the dummy comparison, stated there "for any potentials 𝐖′ with |𝐖′| ≤ A_Y", L2647), Lemma c4-7-1(a) (only |ordinary| ≤ e^{A_Y} − 1 is used, L4691, L4705), the undifferenced factors of Lemma c5-5-6, and Lemma c5-5R-2(c),(d). With ω̂_t ≤ ω_*/2 these hold verbatim. In Lemma c5-5R-2(c), R_Υ := ω_*/(2ω̂_t), and the class-(β) factor of Lemma c5-5R-3 Step 3 becomes 2ω̂_t/ω_*.
  - (b) locality on E(Y) and boundedness on the translated box (properties (i)–(iii) of the proof of Lemma c5-4-1; Lemma c5-5-2(a),(d), L2636, L2662): shown above.
  - (c) the host form 𝐖_t = Θ^t_{E(Y)}𝐏_t in Lemma c5-5-6 (L2728–2732). With the tilt, W̃_t = Θ̂^t_{E(Y)}P̃_t, P̃_t := 𝐏̂_t − tL_Y(δ̂,·), 𝐏̂_t := Σ𝔭(B + tm̂ + tA^{Λ,Ψ}), L_Y(δ̂,B) := Σ_{b:Y_b=Y}⟨B_b,δ̂(b)⟩ (tj1-r2 m4). So |P̃_t| ≤ ω̄̂ := ω̄ + e^{κ(B_h+4)}(τ̄ + τ̂_N) (τ̄ = 0 at real backgrounds; rd5-tj1 M3, rd5-tj2 m2). The smooth part of a host mark is ≤ 2ω̄̂e^{ω̄̂}. Without exterior input, ∂_tP̃_t = ΣD𝔭(B + tm̂)[m̂|_{E(Y)}] − L_Y(δ̂,B), and the second term adds the tilt mark above. ω̄̂ ≤ 1 is required; since ω̄̂ − ω̄ → 0 with g₀ ((6)), it is a g₀-threshold. The second branch of (c5-5-T)(iii) enters only the cutoff part and the dummy comparison at t = 0, where P̃₀ = 𝐏₀, so it is used only with ω̄ and is unchanged (tj1-r2 m5). The mark constants: C′_bd needs only (1 + ω̄̂)e^{ω̄̂} ≤ 2e, which holds with ω̄̂ ≤ 1, and its Σh(m_b) becomes Σh(m̂_b) ((5)); C_bd := 2e·e^{κ(B_h+4)}e^{1/8}C₀/ω_* bounds the marks by C₀g₀(1+3r)³ ≥ ω̄ and is raised to C_bd := 2e·e^{κ(B_h+4)}e^{1/8}(C₀ + C_τ)/ω_*, valid at real backgrounds because ω̄̂ ≤ ω̄ + C_τg₀²r² ≤ (C₀ + C_τ)g₀(1+3r)³ for g₀ ≤ 1 (tj1-r2 m1). At complex backgrounds ω̄̂ also contains e^{κ(B_h+4)}τ̄, and C_bd carries τ̄'s factor (1 + (log g₀⁻²)^{(q₁−p₀)₊}) of (6) (the D2.4 item).
  - (d) the cutoffs and the bond marks at m̂: pointwise uses, above.
  - (e) the evenness of Lemma c5-5R-2(a) at t = 0, where the tilt vanishes. At t = 1 a class-(γ) root has 𝒟 = ∅, so no ordinary Mayer factor is selected, the tilt does not appear, and its measure is the t = 0 measure plus marked cutoff differences, as in V3 (Lemma c5-5R-2(b)).
  - In Lemma c5-5R-2(c), ζ multiplies the whole W̃_t, tilt included ("every near primitive assigned to a host of 𝒟 multiplied by ζ", with the tilt part assigned to the probe host Y_b); so R_Υ := ω_*/(2ω̂_t) is the right radius (tj1-r2 m4).
  - So V3 §c5-5, §c5-5R and Lemma c4-7-1 hold with W̃_t, ω̂_t and ω̄̂, with C₀ replaced by C₀ + C_τ in C_bd (hence in C₂ of Prop. c5-5-9, the term 64C_bd, and in Cor. c5-5-10, Prop. c5-6-4 and Cor. c5-7-4(a)) and in the constants of §c5-5R, under the choice of (6). The quantitative uses of h(m̂_b) and the tilt marks enter through (5) (tj1-r2 m1, m2).

**(5) The decay form of the shift at m̂ (rewritten 22 Oct, after 12:44, finished by the date reading 12:53:25; the sum form with the rate condition η/(A_ELM) ≤ μ_H/20 is withdrawn).** V3 uses the decay of m through the pointwise (c5-5-1) and the sum form (c5-5-2) with its I_C clause (L2609–2616). Put μ_x := μ_H/20.
- *A finite-range bump costs a fixed rate.* For R ≥ 0 and every bond b, 𝟏{d(b,J₁(Λ)) ≤ R} ≤ Σ_{e∈J₁(Λ)}𝟏{d(b,e) ≤ R} ≤ e^{μ_xR}Σ_{e∈J₁(Λ)}e^{−μ_xd(b,e)}. And q_s^{N+1}e^{μ_xR_N} ≤ e^{−μ_Hℓ_s(N+1)/2 + μ_Hℓ_s(N+2)/4 + μ_Hρ_L/10} = e^{−μ_Hℓ_sN/4 + μ_Hρ_L/10}, by q_s ≤ e^{−μ_Hℓ_s/2} and R_N = 5ℓ_s(N+2) + 2ρ_L.
- *Pointwise form (c5-5-1) at m̂.* By (3), h(m̂_b) ≤ h(m_b) + ε_N𝟏{d(b,J₁(Λ)) ≤ R_N}. With the bump bound and e^{−μ_Hd} ≤ e^{−μ_xd},
  h(m̂_b) ≤ [C_m + 2c_hγ⁻¹N_lat(μ_H)c_ℓe^{μ_Hρ_L/10}e^{−μ_Hℓ_sN/4}]ϑrΣ_{e∈J₁(Λ)}e^{−μ_xd(b,e)} ≤ 2C_mϑrΣ_{e∈J₁(Λ)}e^{−μ_xd(b,e)}
  for N ≥ N₀, the least N with 2c_hγ⁻¹N_lat(μ_H)c_ℓe^{μ_Hρ_L/10}e^{−μ_Hℓ_sN/4} ≤ C_m, a constant of L and the group (rd5-tj2 m1). This is (c5-5-1) with (2C_m, μ_x) in place of (C_m, μ_H), with no counting factor and no condition on the rate of any consumer.
- *Sum form (c5-5-2) at m̂.* V3's proof of (c5-5-2) from (c5-5-1) (L2620: the splitting e^{−μ_xd(b,e)}e^{−μdist(b,X)} ≤ e^{−μ_xd(b,e)/2}e^{−min(μ_x/2,μ)dist(e,X)} and the lattice count) gives, for every μ ≥ 0 and every set X,
  Σ_{b∈D(Λ)}h(m̂_b)e^{−μdist(b,X)} ≤ 2C_mϑrN_lat(μ_x/2)Σ_{e∈J₁(Λ)}e^{−min(μ_x/2,μ)dist(e,X)},
  and its I_C clause becomes Σ_{b∈I_C}h(m̂_b) ≤ 2C_mϑrN_lat(μ_x/2)Σ_{e∈J₁(Λ)}e^{−μ_xdist(e,I_C)/2}.
- *The real tilt δ̂.* By (3), h(δ̂(b)) ≤ C_shϑr·q_s^{N+1}𝟏{d(b,J₁(Λ)) ≤ R_N + ρ_L} ≤ C_she^{3μ_Hρ_L/20}e^{−μ_Hℓ_sN/4}ϑrΣ_{e∈J₁(Λ)}e^{−μ_xd(b,e)}. With the choice of N in (6) (e^{−μ_Hℓ_sN/4} ≤ g₀) this is ≤ C_she^{3μ_Hρ_L/20}ϑrg₀Σ_ee^{−μ_xd(b,e)}: (c5-5-1)'s form at rate μ_x, small in the coupling.
- *Consumers (V3 read after 12:44, by 12:53, date: Prop. c5-5-9 L2810–2833, Cor. c5-5-10 L2834–2846, Remark c5-5-11 L2849, Prop. c5-5R-4 L2961–2966, Prop. c5-6-4 L3029–3043, §c5-7 L3210, L2461).*
  - Lemma c5-5-4 (L2687) and the source-shift marks of Prop. c5-5-9 (ii) use the I_C clause: they hold with 𝔖̂₁(Λ) := Σ_{e∈J₁(Λ)}e^{−μ_xdist(e,I_C)/2} and N_lat(μ_x/2), 2C_m in C₁.
  - Lemma c5-5-5's consequence and the bond marks (L2701, L2713) hold at rate μ_x with 2C_m in C_ϖ. Prop. c5-5-9's splitting then gives the bond and host marks at the rate min(μ_x/2, ν/(C_FLM)), for every ν. So μ′ becomes μ̂′ := min(μ_x/4, ν/(2C_FLM)), and V3's condition μ′ ≤ min(μ_H/2, ν/(C_FLM))/2 holds with μ_x in place of μ_H.
  - The tilt marks 𝔪^{δ̂}_Y ≤ Ĉ^δ_bd rΣ_{b:Y_b=Y}h(δ̂(b)) ((4)) have the form of V3's host marks without exterior input, with the prefactor Ĉ^δ_bdC_she^{3μ_Hρ_L/20}ϑg₀r² in place of C′_bd g₀(1+3r)²·2C_mϑr (both of order g₀ times a power of r). They enter C₂ε̄_tr^{d_G}𝔖̂₂(Λ) with an added constant. This was the one place where the withdrawn sum form needed η/(A_ELM) ≤ μ_H/20: there e^{μR_N} appeared at μ = ν/(C_FLM). The bump bound at the fixed rate μ_x avoids it.
  - Prop. c5-5-9 at m̂: (c5-5-9) with 𝔖̂₁, 𝔖̂₂(Λ) := Σ_{e∈J(Λ)}e^{−μ̂′dist(e,C)}, and C₁, C₂ with 2C_m, N_lat(μ_x/2), the tilt-mark constants and the raised C_bd of (4)(c) (tj1-r2 m1); C₂ is doubled for the label share of (6) (tj2-r2 D). Its constants still depend on L, the group, M, κ, ω_*, ν, ϑ, the character and the stencil ranges only.
  - Cor. c5-5-10: 𝔖̂₁ ≤ e^{μ_x(2L+1)/2}𝔖̂₂, since μ_x/2 ≥ μ̂′. The far-event bound n_CN_lat(μ̂′/2)e^{−μ̂′(b−1)/2} and r^{d_G}e^{−μ̂′(b−1)/2} ≤ e^{−μ̂′(b−1)/4} once b − 1 ≥ (4d_G/μ̂′)log r: a g₀-threshold, as b − 1 grows as a power of log g₀⁻². 𝔇_Λ ≤ |I∖D(Λ)| does not involve the rate.
  - Remark c5-5-11's fixed-loop restriction on n_C keeps its form, with μ̂′ for μ′. Prop. c5-5R-4 takes the constants of Prop. c5-5-9, with C_ph multiplied by 1 + C_τ/C₀ under the choice of N in (6) (rd5-tj2 S1).
  - Prop. c5-6-4 (L3032–3043) and §c5-7 (L3210) use μ′ only through N_lat(μ′) and the factor e^{μ_H(2L+1)/2} of Cor. c5-5-10. With μ̂′, N_lat(μ̂′) is a larger constant, and e^{μ_x(2L+1)/2} ≤ e^{μ_H(2L+1)/2}.
  - L2461 needs bounds Ce^{−cd(b,Γ_C)} with C, c independent of the labels, the fields and r. c = μ̂′ (and μ_x/2) qualifies.
- *V3's η.* V3 fixes η only by upper bounds from the forest sums: 1000ηA_s < ϖ/8 with ϖ ≤ min(1/16, λ_*/(64C_g)) and A_s = 1 + A_h (L4619, L4775, L4790). They do not involve μ_H or A_E, so they do not imply η/(A_ELM) ≤ μ_H/20. That condition is not needed: the consumers above hold for every ν = η. The rates of Prop. c5-5-9 change from μ_H to μ_x as part of the m → m̂ repair (rd5-tj2 m4).
- *Constants fixed before the coupling (after tj2-r2 A; V3 L3968 read 22 Oct after 15:25, date).* V3's order, with C₀′ := C₀ + C_τ placed at C₀'s place (after N_h and C₀ of (part1-host-multiplicity)), in the role of C₀ wherever the host bound enters: thresholds 4(ii)–(iii), §c5-5R, and C_bd ((4)(c)). This placement is not circular: C_τ = 5C_σ(4M+2)⁴C_shϑe^{κ(B_h+4)} is built from the norm constant C_σ of 𝔤, M, ϑ ≤ ϑ_*, κ, the host constant B_h (V3 L3788, fixed with N_h) and C_sh, which depends on L and the group only ((3)); none of them depends on C₀. Every constant after C₀ in V3's order (C′_χ, K_χ, u_*, η, C_pin, ρ_pin, N_host, C_M; L3968: "depending on L, M, κ, ω_*, the group, the character and the constants earlier in this order only") is read from C₀′; so is a constant that uses C₀'s value still fixed before the coupling. Added constants: ℓ_s, N₀, C_sh, C_τ, Ĉ^δ_bd. Derived quantities that change: μ′, C_ϖ, C₁, C₂, 𝔖₁, 𝔖₂, ω_t, ω̄, C_bd, C_ph (× (1 + C_τ/C₀)), and V3's g₀-threshold (L3967), which now also depends on the added constants.

**(6) Choice of N, range, count check.**
- *Choice (changed after rd5-tj2 S1, 22 Oct after 14:11; the 12:53 choice e^{−μ_Hℓ_sN/4} ≤ r^{−3} is withdrawn: it gave τ̂_N ≍ r⁻⁴ at best, not of the order of ω_t, and so lost §c5-5R's second-order rate at t = 1).* Take N = N(g₀) the least N ≥ N₀ with e^{−μ_Hℓ_sN/4} ≤ g₀. Then q_s^{N+1} ≤ e^{−μ_Hℓ_sN/2} ≤ g₀², so τ̂_N ≤ 5C_σ(4M+2)⁴C_shϑ·r²g₀² and ε_N ≤ 2c_hγ⁻¹N_lat(μ_H)c_ℓϑ·rg₀². Since r²g₀² ≤ g₀(1+2r)³ for g₀ ≤ 1, ω̂_t ≤ (C₀ + C_τ)g₀(1+2r)³ with C_τ := 5C_σ(4M+2)⁴C_shϑe^{κ(B_h+4)}, a constant fixed before the coupling. So ω̂_t has ω_t's form with C₀ + C_τ in place of C₀. Likewise ω̄̂ ≤ ω̄ + C_τg₀²r² at real backgrounds. The tilt bound of (5) is ≤ C_she^{3μ_Hρ_L/20}ϑrg₀Σ_ee^{−μ_xd(b,e)}.
- *Thresholds.* (c5-5-T)(ii) holds with ω̂_t, (c5-5-T)(iii) and Lemma c5-5-6 with ω̄̂ ((4)), and (c5-5R-T)(ii) with ω̂_t: all for small g₀, since ω̂_t and ω̄̂ have the forms of ω_t and ω̄ up to constants at real backgrounds, and up to the factor (1 + (log g₀⁻²)^{(q₁−p₀)₊}) at complex backgrounds; the thresholds still hold for small g₀ because τ̄ ≤ Cg₁(log g₁⁻²)^{q₁}ϑr² → 0 (rd5-tj2 m2; tj2-r2 E). Class (β), and so ρ_ph ≤ C_phg₀²(1+2r)⁴ and the explicit second-order rate of Prop. c5-5R-4, hold with C_ph multiplied by 1 + C_τ/C₀ (rd5-tj2 S1, Repair A). At complex backgrounds (3.12)'s real shift becomes m̂₀ := m̂(U₁), and the two tilts add: ω_t + e^{κ(B_h+4)}(τ̄ + τ̂_N). (3.12)'s δℓ becomes H_{𝐔,DD}m̂₀ + ℓ_𝐔 = (H_𝐔 − H_{U₁})_{DD}m̂₀ + (H_𝐔 − H_{U₁})_{DJ}A^{Λ,Ψ} + δ̂(U₁). By the pointwise form of (5), each of the two difference terms has (c5-5-1)'s form at rate μ_x and carries ρ₁; C_δ is taken with (2C_m, μ_x) for them. The term δ̂(U₁) is the real tilt, bounded by (5)'s tilt bound and counted in τ̂_N, not in C_δ (rd5-tj2 m3). So τ̄ holds with N_lat(μ_x), and its tilt marks enter Prop. c5-5-9 like V3's host marks, for every ν.
- *Order at complex backgrounds (rd5-tj2, remark on τ̄).* τ̄ ∝ ρ₁ϑr² with ρ₁ = α_{1,1}/L, α_{1,1} = g₁C₁(log g₁⁻²)^{q₁} (CRE (2.28), p.259: q₁ an integer > 1, C₁ large; CRE and LFR print no relation between q₁ and p₀). So τ̄/ω_t ≍ (log g₀⁻²)^{q₁−p₀}, and at complex backgrounds class (β) gives ρ_ph ≤ Cg₀²(1+2r)⁴(1 + (log g₀⁻²)^{(q₁−p₀)₊}): second order in g₀, with at most a power of log g₀⁻² more. Whether D(k)'s consumer tolerates that power is checked in D2.4 (contraction count), where n_C·ε̄_ph is used.
- *Range.* N(g₀) ≤ N₀ + 1 + 2log g₀⁻²/(μ_Hℓ_s), so R_t := R_{N(g₀)} ≤ (10/μ_H)log g₀⁻² + 5ℓ_s(N₀+3) + 2ρ_L. The tilt δ̂ reaches R_t + ρ_L (rd5-tj2 m5, m6).
- *Count check, per cube (rewritten after rd5-tj2 S2; the earlier per-group comparison of ρ_t with e^{CR_t⁴} is withdrawn: a group's smallness is per root, and its per-size decay is only the fixed reserve e^{2νσ(W)}).* On the term labelled Λ, the t > 0 factors of a group W depend on Λ only within R_t + ρ_L of its envelope 𝔈(W) (with §3g(1)(d′)). The envelope has at most A_Eσ(W) cubes of side LM. Its enlargement by R_t + ρ_L has at most n_t := (2(R_t+ρ_L)/(LM) + 3)⁴A_Eσ(W) cubes. The label polymers are the components of Λᶜ (§3g(2)). Let a_lab bound the summed weight of the label polymers that contain a given cube. Then the label configurations meeting the enlarged envelope cost at most exp(a_lab·n_t). The share e^{ησ(W)/2} is freed inside V3's reserve e^{2νσ(W)} (ν = η) of Lemma c5-5-8: there e^{νσ(W)} becomes decay, e^{2νσ(W)} ≥ e^{νσ(W)}e^{νdist(Δ,C)/(C_FLM)}, and the other e^{νσ(W)} pays σ(W) ≤ ν⁻¹e^{νσ(W)} in the differenced slot. Pay it instead with σ(W) ≤ (2/ν)e^{νσ(W)/2} (from x ≤ eˣ); C₂ doubles and e^{νσ(W)/2} is free. The rates of D1(ii) (δ*^{30}_n and §3a(6)'s 30η/8) do not change (tj2-r2 D, its second option). This share absorbs the label cost iff a_lab(2(R_t+ρ_L)/(LM)+3)⁴A_E ≤ η/2. D2.6 inherits this share. Each component carries LFR II's factor e^{−κ₁(Z)−2p₀(g₁)} (p.384, the factors exp(−κ_j(Z) − 2p₀(g_{j(Z)})); R-d″(ii) for the bad cubes, which joins (1.79)'s form). With the modified (1.76) of §3c(4‴) (§3f(2) Minor 4), p.385's constant ¼γ₀(14)^{−d} becomes ¼c₄(434)^{−d}ϑ² (§3f(2) Minor 4, *p.385's step*): κ₁(Z) ≥ ¼c₄(434)^{−d}ϑ²A₁²(log g₁⁻²)^{2p₀}(d₁′(Z)+1) − O(1)M^dR₁^{d+1}d₁′(Z) (p.385, the display for κ₁, modified), under the modified condition ¼c₄(434)^{−d}ϑ²A₁²(log g₁⁻²)^{2p₀} ≥ O(1)2(64)^dM^dL^{d+1}R₁^{d+2}, which holds for small g₁ (tj2-r2 B; with c₄ for γ₀ as Minor 4 derives). LFR's p₀(g) is (log g⁻²)^{p₀} (R-d″ *Notation*). So a_lab ≤ Ce^{−2(log g₁⁻²)^{p₀}} (the tree count through a cube is paid by κ₁). With R_t ≍ log g₀⁻² and CRE (2.6), p.255, g₁ ≤ (1+β₀)g₀, so ½log g₀⁻² ≤ log g₁⁻² for small g₀ (V3 L2455), hence (log g₁⁻²)^{p₀} ≥ 2^{−p₀}(log g₀⁻²)^{p₀} and a_lab·R_t⁴ ≤ C(log g₀⁻²)⁴e^{−2^{1−p₀}(log g₀⁻²)^{p₀}} → 0, a g₀-threshold (tj2-r2 C; the earlier citation of CRE (2.7) is withdrawn). Count check, not a proof: how the label sum consumes the dependence is D2.6 (§3c(4⁗)(d), *The extra label*), and this is the per-cube weight it must use.

**(7) Status.**
- Round 7 (it1-rd5-tj1, it1-rd5-tj2, read 22 Oct after 14:03): nothing fatal. tj1 S1 (W̃_t checked only against the vacuum expansion) is repaired by the finite check in (4). tj2 S1 (the 12:53 choice of N lost the second-order rate at t = 1) is repaired by Repair A in (6). tj2 S2 (a mis-normalised count) is repaired by the per-cube count in (6). The minors tj1 M1–M4 and tj2 m1–m7, m9, m10 are applied; m8 lapsed with the old choice of N.
- Round 8 (it1-rd5-tj1-20261022-r2, it1-rd5-tj2-20261022-r2, sessions local_54f3c72e and local_b538bd17, claude-opus-5-5; read 22 Oct after 15:21, date): no fatal or serious finding; the repairs of round 7 are confirmed. Minors applied after 15:25: tj1-r2 m1 (C_bd with C₀ + C_τ, carried into C₂), m2, m4, m5, m6 (finite check extended to L2736–2852, L2951–2971); m3 (the pointer for the contour-wide factors did not support its sentence: now an open D2 item, (0)); tj2-r2 A (C₀′ in V3's order, (5)), B (modified κ₁ display), C (CRE (2.6) via V3 L2455), D (the freed share inside Lemma c5-5-8's reserve), E (the polylog factor in §3e(4)–(5) and (6) *Thresholds*). Not re-reviewed.
- Derived: (1)–(5), (6) except the count check, which stays a count check until D2.6 uses its per-cube weight (rd5-tj2 m7). The t > 0 species, the words and f_ξ(m̂) depend on Λ only within R_t + ρ_L of their footprints. No new hypothesis. The new conditions are N ≥ N₀, ℓ_s(L, G) and the g₀-thresholds of (4)–(6). Open for D2.4: whether the polylog factor (log g₀⁻²)^{(q₁−p₀)₊} at complex backgrounds ((6)) is affordable in n_C·ε̄_ph. The rates of Prop. c5-5-9 and its consumers become μ_x/2 and μ̂′ = min(μ_x/4, η/(2A_ELM)), as part of the m → m̂ repair for the overhaul.
- *Former open items, closed after 12:44, by 12:53 (date), after the user's "Check whether V3's current η already satisfies η/(A_ELM) ≤ μ_H/20 before any V3 change, then continue with (O2), (O3)":*
  - (O1) closed. V3's η does not imply the condition (its bounds are forest-sum bounds, (5) *V3's η*), but the condition is not needed: the pointwise form of (5) gives every consumer for every η. The constants fixed before the coupling are V3's with C₀′ := C₀ + C_τ at C₀'s place, plus the added ones ((5) *Constants fixed before the coupling*; rd5-tj2 m4; tj2-r2 A).
  - (O2) closed. The I_C clause holds at rate μ_x/2. Its consumers (Lemma c5-5-4, Prop. c5-5-9 (ii), Cor. c5-5-10, Prop. c5-6-4, §c5-7 L3210, L2461) use the rates only as fixed positive constants: through N_lat(·), e^{rate·(2L+1)/2} (rd5-tj2 m9), and the g₀-threshold b − 1 ≥ (4d_G/μ̂′)log r ((5) *Consumers*).
  - (O3) closed. Every occurrence of the shift in V3 L2479–3120 was extracted with its context (standalone m, tm and sm tokens, m_L, m_A, m_* and the majorants m(Z), m(D) excluded; 74 contexts outside the ranges read before, L2636–3096) and classified:
    - pointwise uses (|m_b|_σ ≤ r/4, values at b, segments a + sm in the enlarged box; L2636–2662, L2692–2708, L2728–2751, L2910, L2925–2929): verbatim at m̂;
    - the expansion at the young variable B + tm (L2654–2672, L2757–2764): the identity of (4);
    - finite sums Σh(m_b) over E(Y), I_C, I_{𝓗(W)} (L2687, L2718, L2732–2735, L2769–2774): bounded by (5);
    - the parity of §c5-5R (L2910, L2929): at t = 0 only, where the tilt vanishes and 𝒟 = ∅;
    - the reference data m° = 0 (L2668, L2679, L2910, L3096), remarks (L2849, L3090), and false hits (m_*, δm, m_W(Γ), ρ_tm(Z)).
- Not reviewed.

## 4. The class 𝔇₁ and the target D1 (draft)

Repaired after reviews it1-b-frame-20261021-r1 (S1–S4, S6) and it1-a-dev-20261021-r1 (S-2). The earlier draft indexed insertions by intervals. That cannot contain V3's bracket: several groups can have the same interval, and q° and Υ depend on the groups themselves. Its norms were also unquantified, and its clause (ii) was vacuous (dev := ‖Y‖/(2K_χM) satisfies it by §3 and §2(f)).

**Definition (draft).** A *dressed loop of step 1* for C_n on a labelled term (final region Λ, carrier D(Λ)) is a function of V and of the outer variables that the term holds constant, of the form

𝒲 = κ_C e^{E} [ f + Σ_{𝔅≠∅ compatible} Q(𝔅)·dim(π)⁻¹ tr(Y_{W₁}U₁ ⋯ Y_{Wₙ}U_n) ].

The outer variables are V₀ on Ω₁ᶜ, the exterior variable on J, and the de-younged bonds I∖D(Λ) (L2594). On uncovered terms they also enter the contour links (§3d(1)). The ingredients:
- **groups** W of V3 (Lemma c5-5-3(a)), with size |W| := σ(W), and **families** 𝔅 compatible in V3's sense: "all their constituent domains … mutually compatible and their intervals are disjoint" (L967);
- **insertions** Y_W ∈ End(V_π), one per group;
- **leading word** f, a unitary word of the background (V3: f_ξ(m)); on uncovered terms it also contains outer variables (§3d(1); d11-r2 m-g);
- **words** U_j, unitary words of the background and the outer variables;
- **interactions** Q(𝔅) = exp(−Σ_{Γ hits 𝔅} φ(Γ)), over the clusters Γ of the reference group gas, with "hits" as in Lemma c5-5-3(d);
- **scalar exponent** E = Σ_X e_X + E_const, a sum of local terms plus a constant of the contour and the torus.

The norms, quantified as V3 and §3 to §3b supply them. Here a > 0, and the bounds hold for every traversal n and every coarse segment j:
- |Q(𝔅)| ≤ ∏_{W∈𝔅} e^{θ°(W)} with θ°(W) ≤ νσ(W)/16 (Lemma c5-5-3(d), rooted Kotecký–Preiss; §2(d));
- Σ_{W∋n} e^{θ°(W)}‖Y_W‖ ≤ ν_n, with ν_n as in D1(ii) below;
- Σ_{X within R_0 of K_j} |e_X|e^{a·diam X} ≤ Cτ²e^{−c'd_j} (§3b(4); whether D2 can use a diameter weight is open, gaps block D2), and |E_const| ≤ Cτ²(4ne^{−cι_T} + (n+1)e^{−cn}).

**D1 (candidate target).** It is not certified as the weakest form D2 can use: D2 is not started, and the count of §6(c) is heuristic. For the squares C_n under (c5-7-T), for every n, and for every labelled term (covered or not, §3d), F^Λ(1) is a dressed loop of step 1 such that:
- **(i)** κ_C = e^{−δm^σP(C_n)}(z_c^σ)⁴, the exact first-step coefficients of V3;
- **(ii) per-traversal form.** For every traversal n,

  ν_n ≤ C_χρ δ*_n(U₁) + Cρ e^{−c(d(n)−1)/(LM)} + Cρ e^{−cN_min/(LM)} + Cρ_t[Σ_Δ 𝔪̂_Δ e^{−η dist(Δ,n)/(C_F LM)} + C'_χ g₀ Σ_b h(m_b) e^{−η dist(b,n)/(C_F LM)}],

  with the notation of §3a(6),(7); on uncovered terms d(n) is replaced by d^Λ(n) = dist(Γ_n, E(B_ξ) ∪ (I∖D(Λ))) and ρ by ρ̂ = max(ρ, ρ_ph) (§3d(4); d11-r2 m-g). The first term is the *deviation part*. It is gauge-invariant local curvature that vanishes at flat data, with dev(W) = 𝔰(W)³δ_{Q_W}(U₁) for good groups. The other terms are *attached parts*. They are attached to B_ξ, to the torus wrap and to the collar data, with the decay shown, and they carry no deviation; they are routed to D2(d);
- **(iii)** D1(iii)′ of §3e(0): for real U₁ in the support of the term's indicators, which are kept as factors, the background-dependent factors (Υ¹_W, hence Y_W; the words U_j; f) extend analytically to 𝐔 = e^{ia′}U₁ with ‖a′‖_∞ < ρ₁ = α_{1,1}/L, G-covariantly, with (ii) holding there with δ*_n(U₁) + a*_n(a′); φ and e_X are numbers on each labelled term (D1.2b). The analyticity in the coarse field V comes from this and VAR Prop. 9, and belongs to D2;
- **(iv)** all constants are independent of n, the torus and the labelled term.

No smallness of Σ_W ‖Y_W‖ is claimed.

These contours are unions of coarse-bond traversals at every scale, which a dressed loop of step 1 needs. For a contour not aligned with the coarse blocks there is no coarse loop. V3 defines κ_C only for C_n, and Remark c5-5-11(6) makes "the square/torus geometry" "a standing hypothesis of C_pin, A_F, A_E and the hull bounds". Rectangles, needed only for the Creutz route of the iteration audit §6, are open.

D1 is per labelled term. F_ξ(1) and the form ρ₁ = Σχ₁T₁[· exp A₁] that step 2 needs come from the labelled terms by an assembly, gap D1.0.

**Where D1 stands.**
- On covered labelled terms, §2 gives the form, with (i) and (iv) from V3 under (c5-7-T).
- §3a gives (ii) at real data (D1.2a).
- (iii), in the form D1(iii)′, is derived in §3e (D1.2b) on every labelled term, under repair K; not reviewed.
- §3b gives the carrier part of E as a local sum (D1.3). E_const = E°_{T,n} depends only on n and the torus.
- D1.0 (assembly) is derived at step 1 with the choice (P) (§3c), except D1.0(P)(ii), which is OPEN (R-d″(ii), pending D2.7 and the acceptance item); p.256's conditions for the later steps are part of the acceptance item, whose small-field part is in the D2 file, D2.2(3)(b) (rd5-d2-r3 m8).
- D1.1 (uncovered branches): §3d gives the form, (i), (ii) and (iv) on every labelled term; not reviewed.

## 5. Skeptic pass on D1

- **S1 (reference point).** Closed; see §3.
- **S2 (vacuity).** Without a quantitative (ii), almost anything with bounded local activities fits the definition. The earlier qualitative (ii), "dev vanishes at the reference point and is gauge-invariant", was itself vacuous: dev := ‖Y‖/(2K_χM) satisfies it by §3 and §2(f). The content is the per-traversal form of §4(ii): the deviation part is local curvature, and every other part is attached, with explicit decay, to B_ξ, the wrap or the collar data. That is what is expected to make the non-scalar dressing irrelevant at step 2 (§6(c), heuristic).
- **S3 (gauge).** dev must be gauge-invariant, for example local curvature, while U₁ = id is a gauge choice.
  - What is needed: X_W := Υ^1_W + a^Λ_W·id is covariant under gauge transformations of the data supported near ℋ(W), acting by conjugation at the initial site of the interval (T_W(B)P_W⁻¹ is based there).
  - Then one can pass to the rooted tree gauge on Q_W, with ‖B_W‖_∞ ≤ C_tg diam(Q_W)²δ_{Q_W}(U₁) ((c4-10-17)), so the deviation scales as (LM𝔰)²δ.
  - **Closed for good groups (§3a(5)).** V3 itself proves the comparison through the rooted tree gauge and coefficient covariance (§c4-8-1, §c4-11, at D(Λ) L3082), with the gauge-invariant δ_{Q_W}.
  - For groups that are not good, no deviation is claimed. Their covariance is still needed for the step-2 covariance below.
  - At step 2 the gauge changes, so the covariance of the dressed loop under the step-2 gauge, for all groups, is part of D2.
- **S4 (count at step 1).** At step 1 nothing is summed along the contour.
  - The scalar reference gas is exact, inside S° = κ_C e^{E°}.
  - The insertions are carried and never exponentiated. Their total is the audit's term §4(6): by §3a(6),(8) it is of order n_Cρε₁ on far histories, plus O(ρ) per traversal near B_ξ.
  - The shift parts sit near the exterior, through D_ξ = Σ_{b∈I_C} e^{−μd(b,J)/2} (L2447).
- **S5 (non-interleaving).** Disjoint insertion sites are necessary but not sufficient to contain V3's bracket. The class is therefore indexed by V3's groups, with V3's compatibility (§4). At step 2, an insertion site of the coarse contour can contain several step-1 insertions. Merging them into one coarse insertion is a plan only (D2).
- **S6 (large-field weight).** On uncovered branches, the large-field suppression of the branch weight multiplies 𝒲; it is not used to bound 𝒲. D1's bounds (ii) and (iv) hold there by §3d; (iii) holds there by §3e(4). At D2 the R-operation has to resum the suppression (§6(d)).

## 6. Where the difficulty goes: D2 (not started)

- **(a) The step map.** Integrate the step-2 fluctuations with a dressed loop as the observable. Lemma c5-5-3 is needed with f a dressed loop instead of a bare W_χ: the old insertions become part of f.
- **(b) Exact absorption.** The scalar part produced at step 2 must go exactly into S°₂ = κ₂e^{E°₂}, giving δm₂ and z₂ (IT-3). It comes from the step-2 reference gas and from pair contractions of step-1 insertions.
- **(c) Contraction count (heuristic; to be derived).**
  - Suppose dev is proportional to curvature. For a smooth background, fine-scale curvature is about L⁻² times coarse curvature, and each coarse bond carries L fine sites. So the non-scalar part contracts by about L⁻¹ per step.
  - Scalar curvature terms are gauge-invariant and have no linear term, because tr π(X) = 0 for X in the semisimple 𝔤. So they are at least quadratic and contract by about L⁻³.
  - Insertions induced by the shift stay attached to large-field regions.
  - This is dimension counting, not a derivation. Deriving it needs regularity of the minimisers (VAR) on small-field regions. OPEN.
  - **The Bałaban input for it.** CRE p. 268, after (3.17): "The field U_{k+1} satisfies the regularity condition |∂U_{k+1} − 1| < 2B₃ε_{k+1}(L⁻¹η)² on Ω_{k+1}".
    - In §3a, dev(W) = 𝔰(W)³δ_{Q_W}(U₁) is a plaquette deviation.
    - So at step 2 the input is this bound for the step-2 background, read on the fine plaquettes of the step-1 insertions.
    - Whether (L⁻¹η)² gives the L⁻² of the heuristic has to be checked against the scale convention of η on that page. OPEN.
- **(d) Large-field defects.** At step 2, Bałaban's R-operation replaces large-field expressions by small-field ones "in such a way, that integrals of the densities are unchanged" (LFR I p.176, (0.3)–(0.4)). CRE refers to it on p.254 ("new terms obtained by the R-operations"). CRE p.257 describes the operations T_k, not R. With the contour inside a large-field region, R must also carry the arc holonomy, which has norm ≤ 1.
  - Scalar parts: a polymer expansion with modified activities for the polymers that touch C.
  - Non-scalar parts: they should vanish at flat outer data if the constant-gauge argument of §3 applies there. Not checked. OPEN.
- **(f) Words on the polydisc (constraint from §3e(3.8), (5); local Cauchy estimates derived 11:13–11:30, 22 Oct, date; not reviewed).** At 𝐔 = e^{ia′}U₁ the words and f_ξ(m) have norm up to exp Σ_{b∈C}‖a′(b)‖ ≤ e^{P(C)ρ₁}, which is unbounded in the perimeter. So D2 cannot take a sup of the words over the whole ρ₁-polydisc and then a Cauchy estimate. What it can do instead:
  - *(f1) Cauchy estimates in a bounded set of variables (derived from §3e(4)).* Let F be f_ξ(m₀) or a word U_j, analytic in a′ on {‖a′‖_∞ < ρ₁} with |F(a′)| ≤ exp(C_UΣ_{n∈C_F}‖a′‖_{N(r_n)}) (§3e(4); C_F is C for f_ξ and the traversals of U_j for U_j; operator norm for words). Fix a real basis (T_k) of 𝔤 and c_𝔤 ≥ 1 with ‖Σ_kz_kT_k‖ ≤ c_𝔤max_k|z_k| for complex z_k. Fix a′₀ with ‖a′₀‖_∞ < ρ₁, a set S of fine bonds and 0 < r < ρ₁ − ‖a′₀‖_∞, and let D_S be the polydisc {a′₀ + z : z(b) = Σ_kz_k(b)T_k, z = 0 off S, |z_k(b)| ≤ r/c_𝔤}.
    - On D_S, ‖a′₀ + z‖_∞ < ρ₁, and ‖a′₀ + z‖_{N(r_n)} ≤ ‖a′₀‖_{N(r_n)} + c_Nr·1{N(r_n) ∩ S ≠ ∅}. Here c_N = 1 if ‖·‖_{N(b)} is the maximum over the stencil N(b), and c_N = max_b|N(b)| if it is the sum.
    - So sup_{D_S}|F| ≤ exp(C_UΣ_{n∈C_F}‖a′₀‖_{N(r_n)})·e^{C_Uc_Nrν_S}, with ν_S := #{n ∈ C_F : N(r_n) ∩ S ≠ ∅}.
    - Cauchy's estimate in the |S|·dim 𝔤 variables z_k(b) gives |∂^αF(a′₀)| ≤ α!(c_𝔤/r)^{|α|}sup_{D_S}|F|.
    - At a′₀ = 0 the first factor is 1. Every real U₁ in the support of the term's indicators is a base point of D1(iii)′. So the derivatives at real backgrounds in the variables of S cost α!(c_𝔤/r)^{|α|}e^{C_Uc_Nrν_S}.
    - ν_S ≤ N_C|S|, with N_C := max_b#{n ∈ C : b ∈ N(r_n)}. N_C is at most the number of bonds whose stencil contains a given bond times the multiplicity of C, which is one for the squares C_n of §OPEN. It does not depend on P(C).
  - *(f2) Fluctuation integrals.* Inside a Gaussian fluctuation integral the dressed loop is evaluated at real fluctuation fields. The complex parameters (V3's pair variables x_{bc}, §3i's box parameters s) go into the density, as V3 does (no cutoff or Wilson function is differentiated, L1276) and as §3i(5) does. Then the real-data bounds |f_ξ| ≤ 1 and ‖U_j‖ = 1 (L3064) apply. RG2's change of variables B′ = (C^{(k)})^{1/2}X ((2.6)) is not used on terms containing the loop: with complex s it would put the contour at complex fields, at the cost exp(C_UΣ_{n∈C}‖Im B′‖_{N(r_n)}).
  - *(f3) The coarse variables at step 2 (quoted from VAR pp.305–308, with reading R-v).*
    - VAR (172), p.305: V = V′V₀ with V₀ real and V′ = e^{iB′}, |B′| < 2C₁ε₁ on 𝔅_k. In the Landau gauge, U_k(V′V₀)U₀⁻¹ = exp iη𝓗(B) with U₀ := U_k(V₀) (p.305 l.37–38; §OPEN D1.2b (2)). 𝓗 is analytic in 𝔤^c-valued B satisfying (172) (p.307 l.3). So U_k(V′V₀) = e^{ia′}U₀ with a′ := η𝓗(B). This is the form in which D1(iii)′ is stated, with base point U₀.
    - VAR (190), p.308: |(δ/δB_ν(y′))𝓗_μ(B,x)| ≤ O(1)(L^jη)⁻¹(L^{j′}η)^{−d}exp(−⅛δ₀d(y,y′)) for x ∈ Δ(y), y ∈ Λ_j, y′ ∈ Λ_{j′}. It follows (p.308 l.37) from (189). Bałaban states (189) without its computation ("We do not perform these calculations here", p.308 l.31). It is accepted as his result.
    - *Reading R-v.* (190) holds on the whole domain (172), complex B included. The print gives (190) no domain of its own. p.307 l.18–19 announces decay properties of (δ/δB)𝓗(B) "identical to the propagator" for the analytic 𝓗 of p.307 l.3. (189) is stated "for A′ satisfying (77)", a condition on moduli (p.290).
    - *Consequence.* The functional derivative is the kernel for VAR's pairing ((63), p.287). Fix V₀ real with U₀ in the support of the term's indicators, a set S₂ of coarse bonds and r ≤ C₁ε₁, and let B be supported on S₂ with |B| ≤ r. Then a′(x) = η∫₀¹⟨(δ/δB)𝓗(τB,x), B⟩dτ, and by (190), ‖a′(x)‖ ≤ C_Vr Σ_{y′∈S₂}e^{−δ₀d(y,y′)/8} for x ∈ Δ(y). C_V is O(1)η(L^jη)⁻¹(L^{j′}η)^{−d} times the weight of the pairing, and depends on L, d and the scales only.
    - So Σ_{n∈C}‖a′‖_{N(r_n)} ≤ C_VrK_C|S₂|, with K_C := sup_{y′}Σ_{n∈C}max_{b∈N(r_n)}e^{−δ₀d(y(b),y′)/8}. K_C is at most N_C times the number of fine bonds per block times Σ_{t≥0}#{y : d(y,y′) = t}e^{−δ₀t/8}, which is finite and independent of P(C).
    - With r so small that C_VrK_V < ρ₁, K_V := sup_yΣ_{y′}e^{−δ₀d(y,y′)/8}, (f1) at a′₀ = 0 gives |∂^αF(V₀)| ≤ α!(c_𝔤/r)^{|α|}exp(C_Uc_NC_VrK_C|S₂|) for derivatives in the coarse variables of S₂.
    - *Gauge.* This is the Landau gauge of p.305 relative to U₀. f_ξ and the closed-contour terms of the dressed loop are class functions of closed holonomies, so they are invariant under G^c-valued gauge transformations. So they are the same in VAR's axial gauge ((181), p.307). Open words get conjugations at their endpoints; D2 uses them only inside closed products.
    - *Units (open, a bookkeeping item of D2).* (190) is in Bałaban's dimensional variables at spacing η. The identification of 𝔅_k, j, j′ and the pairing weight with V3's units at step 2 is the passage that §OPEN D1.2b (2) leaves to D2. Above, only the form is used: a prefactor depending on L, d and the scales, and decay at rate δ₀/8 in the block distance.
  - *(f4) What D2 has to check.* Every Cauchy estimate that D2 applies to a term containing the loop must be taken on a polydisc in the variables of a set S charged to that term: its group, its polymer, or the sites it differentiates. |S| is then paid by the term's own weight, and (f1)–(f3) give a factor e^{C|S|r}, never e^{CP(C)ρ₁}. Which of Bałaban's step-2 operations apply Cauchy estimates to such terms is part of the step map (a).

## 7. Next steps, in order

Done at 21:36:
- S1 (§3);
- D1.2a (§3a). It came from V3's path argument, not from a Cauchy estimate: V3's coefficient path already compares each good group with its reference;
- S3 for good groups (§3a(5)).

Done at 21:50: D1.3 (§3b), not reviewed.

Done (reports written 21:54–22:00 by file time; read and repaired by 22:14): the six reviews were read and repaired (status lines of this note, of the iteration audit and of the LIP-1(a) note).

Done 22:14–22:23: D1.0 at step 1 (§3c), up to the choice (A)/(P) and the check D1.0(P). Not reviewed. If (P) is chosen, D2 starts from CRE's T₁ form, with V3's labels as refined labels.

Done 23:10–23:31: reviews it1-d-d13 (§3b) and it1-c-d10 (§3c up to (4″)) read and repaired. Neither found anything fatal. §3b now has the anchored decomposition. §3c now defines V^{(0)} as the exact change, bounds the cross-component blocks, routes the bad tests through the positivity bound and uses the enlarged retreat 𝒬⁺ (§3c(4⁗)).

Done 23:35–23:48: the D1.0 leftovers. The four placements of §3c(2) are fixed (new reading R-f for z^{(0)}). The label sum factorises over the ∗-components of Λᶜ (§3c(4⁗)(d), derived). Not reviewed.

Done 23:50–00:15 (22 Oct): D1.1 by the closed-contour route (§3d). The identity holds on every labelled term, with V3's coverage hypotheses checked at each use. Not reviewed.

Done 00:24:46 (22 Oct): review round 3 launched at the user's "Launch reviewers and continue": packets it1-c2-place, it1-c4t-ii, it1-c4q-rep and it1-d11 (§3c(2), §3c(4‴), §3c(4⁗), §3d). Reports written 00:37–00:40.

Done 00:30–00:57 (22 Oct): D1.2b (§3e), in the form D1(iii)′, with repair K of V3's constants. Not reviewed; not in round 3.

Done 01:05–02:05 (22 Oct): every round-3 finding repaired (§3f). Not reviewed.

Done 05:18:41 (22 Oct): review round 4 and the R-d″ reading review launched at the user's "Run a review on the reading of R-d'' and R4" (nine packets, header). Before the launch, §3f(2) R1 was corrected: [16] is UV3 and is transcribed.

Done 05:19–05:29 (22 Oct): the D1.3 leftovers (§3g). The reference species are local in the carrier, with a size- and diameter-weighted bound. The label sum has the polymer form. Not reviewed.

Done 05:55–07:28 (22 Oct, session log): the round-4 reports read and repaired (§3h; triage file in verification/isolated_reviewer/reviews). No fatal finding. R-d″ is not printed, so D1.0(P)(ii) is OPEN. Repair K′ is proposed. Not reviewed.

Done 08:57–09:39 (22 Oct, from the user's "1.(a), 2(a)" at 08:57): R-d″ derived (§3f(2) R1, (D0)–(D2)). The bad-cube factor comes pointwise from half of the T₁^Λ form, by a localisation lemma from H ≥ 0 (CRE p.248) and V3's local gap near I. Its insertion into (1.79) rests on reading R-s (not printed). Not reviewed.

Done 10:18 (22 Oct): the user accepted R-s as a logged Bałaban reading ("(a)"), to be reviewed with (D0)–(D2) in the next round.

Done 10:25:42 (22 Oct, at the user's "(a)"): review round 5 launched, packets it1-rd3-pw-20261022-r1 ((D0)–(D1), geometry, use) and it1-rd3-rs-20261022-r1 ((D2), R-s, positivity, Minor 4's factor), on claude-opus-5-5. Finished 10:39 and 10:43; no fatal finding.

Done 10:33–10:50 (22 Oct, date): D2's first item, the thin form of E^∂, derived in §3i. Not reviewed.

Done 10:50–11:04 (22 Oct, date): round 5 read and repaired in §3f(2) R1. R-s is withdrawn; R-d″(ii) follows from the printed (1.79) by Hölder's inequality and the subadditivity of the linear size (rd3-rs S1). The comparison with Λ₁ is withdrawn (rd3-rs S2). R-d″ is restated in two parts (rd3-pw S1); the minors are applied. Not reviewed.

Done 11:12:37 (22 Oct, at the user's "Yes: launch the review of the round-5 repairs … and §3i now"): review round 6 launched, packets it1-rd4-d2-20261022-r1 (§3f(2) R1 (D2), Minor 4's factor), it1-rd4-thin1-20261022-r1 (§3i(0)–(4)) and it1-rd4-thin2-20261022-r1 (§3i(5)–(7)), on claude-opus-5-5. No fatal finding.

Done 11:13–11:30 (22 Oct): the constraint §6(f) written.

Done by 11:36 (22 Oct, date): round 6 read. d2 S1: the Hölder route is not valid as used; thin1 S1: the complex-s claim of §3i(2) is wrong; thin2 S1: X(Γ,Y) need not be connected.

Done 11:36–12:04 (22 Oct, date): d2 S1 and m1–m12 repaired in §3f(2) R1 and the §3c lines. R-d″(ii) is derived factor by factor at Λ, under R-c, R-p and R-q; (D-b⁺) and (D1⁺) are added. Not reviewed.

Done 12:04–12:13 (22 Oct, date): thin1 S1, M1–M7 and thin2 S1, m1–m11 repaired in §3i. Not reviewed.

Done 12:13–12:24 (22 Oct, date): D2's second item, the carrier dependence of the t > 0 species, derived in §3j, except (O1)–(O3). Not reviewed.

Done after 12:26, by 12:43 (22 Oct, date): R-p and R-q checked against UV3 (70)–(71) p.273, VAR p.279 and CRE pp.245–250. Neither is a reading: the 12:24 listing as readings was made before the available sources were read. R-p's status is "location checked; rates quoted from p.380 (step k ≥ N + 1)" (rd5-d2-r2 m2); R-q₀ is quoted and checked and not used. D1.0(P) at step 1 rests on reading R-c, apart from the open D2.7 item of R-d″(ii) (now two items, §3f(2) R1 status; rd5-d2-r4 m-1(c)).

Done after 12:44, by 12:53 (22 Oct, date): §3j (O1)–(O3) closed. V3's η is fixed by forest-sum bounds only (L4619, L4775, L4790), which do not imply η/(A_ELM) ≤ μ_H/20. The condition is withdrawn as unneeded: §3j(5) now uses the pointwise decay form at rate μ_H/20, which serves Prop. c5-5-9 and all its consumers for every η. The pass over V3 L2479–3120 classified every use of m. No V3 change beyond the m → m̂ repair. Not reviewed.

Done 13:06 (22 Oct, at the user's "Yes: launch the review of the round-6 repairs …" and "launch them through the app"): review round 7 started as six app sessions on claude-opus-5-5, one subsection per packet: it1-rd5-dbq, -d2, -thin1, -thin2, -tj1, -tj2 (all -20261022-r1; builder verification/isolated_reviewer/build_round7_review_packets_20261022.py, rendered to .packet.md).

Done 13:17–13:21 (22 Oct, date): the LFR II T′ citation check ((D2) (l)), against pp.356–380 and LFR I p.178. pp.356–379 use the step-1 domain data only through R-c and (1.76). At k = 1, T′_k acts on no component (LFR I p.177 (ii); wording corrected 13:26), so (D2) now bounds CRE's step-1 integral on 𝒳, and the step-k B-integral is dropped from (D2) *Setting*, (h) and *The bound*. [Superseded by the rd5-d2-r2 S1 repair (i) and rd5-d2-r3 m1; rd5-d2-r4 m-1(c).] Not reviewed; not in round 7.

Done 14:11–14:24 (22 Oct, date): round 7 read and triaged. No fatal finding. Serious findings repaired: rd5-dbq S1 ((B-q) replaces R-q's layer clause, from V3's logged (B1)(iii); (D-b⁺), (D1⁺) redone with ε′, μ̂′, r_∂ = (4C_n+1)r), rd5-d2 S1 (the (D2) (l) check), rd5-tj1 S1 (finite check in §3j(4)), rd5-tj2 S1 (Repair A) and S2 (per-cube count in §3j(6)). Minors applied in §3f(2) R1, §3i (thin1 M-a to M-h, thin2 m1 to m8: rooted form in (7), admissibility criterion in (2), R_H defined, d⁺ in the near-segment step, ᾱ, K̄₂, C̄′_*, inputs and range of D) and §3j. New open item: the complex-background polylog factor, for D2.4. Not reviewed.

Remaining:
1. **Repair K′:** agreed by the user for the overhaul (22 Oct, 08:57: "1.(a), 2(a)"); not made in V3.
2. **D2:** continued in WILSON_IT1_D2_STEP_MAP_2026_10_22.md, at D2.2 with D2.5 (the user's "Do all of D2", 22 Oct).
3. **Review of the round-7 repairs and of the T′ corrections of (D2):** with the next D2 review batch.

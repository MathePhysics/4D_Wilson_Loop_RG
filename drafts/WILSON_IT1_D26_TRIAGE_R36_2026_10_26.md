# Round 36 triage (10:26, 26 Oct 2026, date)

Launcher: `verification\isolated_reviewer\run_app_review_cli.ps1 -Rev <folder>` (claude -p, claude-opus-5-5, effort high). The user: "Yes, run round 36 in the CLI on Pass 6 (f) and the new R-𝐇 forms."

Reports (verification/isolated_reviewer/reviews/):
- `it1-rh-a-20261026-r3/review.md` — R-𝐇 bound and domain, map l.971–973 (the gauge of the argument bound, the units of the decay, the passage to 𝐇^{(j)}). Verdict: no significant finding; minors N1–N10.
- `it1-rh-b-20261026-r3/review.md` — R-𝐇 frame links and R-𝐇₀, map l.972, l.980. Verdict: no significant finding; minors n1–n4 (n1–n3 were repaired in round 35's form; n4 new).
- `it1-rc-p6f-20261026-r3/review.md` — RC_PROOF_PASS Pass 6 (f), the complex backgrounds. Verdict: two significant findings S-A, S-B; minors m-1–m-7.

Every report was read in full; every finding was checked against the sources (Bałaban\tex\<paper>\parts, V3, V4) before the repair.

## Open after this round

- OPEN: the base points on Ω₁∖Ω₂ (rooted at k = 1, every k) — unchanged, D2.4(LPG′).
- OPEN: the gauge frame of σ_j (D2.2(4)(d)) — unchanged.
- Not re-reviewed: RC_PROOF_PASS Pass 6 (f) in its new form (the local shift m^{loc}); the R-𝐇 forms of map l.972–973 after N1–N10, n4.

## it1-rc-p6f-20261026-r3 (Pass 6 (f))

**S-A (confirmed, at every background).** Pass 6 (f) shifted by the global centre m_t = −tH_{DD}^{−1}H_{DJ}A_e inside the sharp cutoffs χ(A″ + m_t). m_t(b) depends on U on all of D(Λ), and a sharp cutoff's dependence on its shift cannot be s-decoupled or Taylor-expanded (each derivative costs O(r²) against a fixed e^{−κ₁}, divergent as g₀ → 0). So the pieces of V4's translated polymer representation (Lemma c5-4-1, L2659: "m a fixed vector") are not functions of U|_X, and Pass 4 (4)'s X-locality fails for them even at real U — not only at complex 𝐔. Pass 5 (d)'s "walk localisation of the shift" did not localise the cutoffs' dependence. The reviewer's variant (shift by the global centre, remainder linear) gives volume terms e^{O(e^{−δ₀M/3})r²} that are not small; also confirmed.
*Repair (RC_PROOF_PASS Pass 6 (f), rewritten; Pass 5 (a), (d), Pass 6 (c), (e) amended).* The X-local pieces are defined with the truncated local centre m^{loc} = −Σ_{|ω|≤ρ₂}C_ωℓ, ℓ = H_{DJ}A_e, the walk expansion of C^{(0)}(Λ) (PBG Thm 3.15) cut at length ρ₂ = (δ_*′)^{−1}log(K′m_Lr³) = O(log r), so |m − m^{loc}| ≤ 1/(m_Lr²) per bond. Completing the square at m^{loc} leaves the Gaussian in A″ = A′ − m^{loc}, the linear factor e^{−⟨A″,w⟩} with w = H(m^{loc} − m), |w| ≤ 1/r², and an A″-free constant that cancels exactly in ⟨·⟩_t. The cutoffs χ(A″ + m^{loc}) and potentials then depend on (U, J_U) within ρ₂ + ρ_L of their bonds; w's far dependence is s-decoupled at cost O(1/r) per cube. Collar pieces' localisation domains are enlarged by the (ρ₂ + ρ_L)-neighbourhood (RG2 p.13), a factor ≤ O(1)r against the 𝐁-decay once LM ≥ κ/δ_*′, paid by the penalty e^{−γ₂r²/8} or a potential's g₀-power; pure Gaussian pieces carry no shift. Pointwise |Re m^{loc}| ≤ r/4 + 1/(m_Lr²) + ρ₂O(ϵ_H)Kr ≤ r/2 (V4 (c5-4-1) at the real base, the truncation, the perturbation of ≤ ρ₂ local analytic factors), so the penalty is at r/2; Im m^{loc} = O(ϵ_Hρ₂)r gives volume terms with coefficient O(g₀²(log g₀^{−2})^{2q+2p₀+2}) → 0. Derived, not reviewed.

**S-B (confirmed).** (f) wrote H(𝐔) with no 𝐉 slot and took V4's (I1)–(I3) at the real base U alone, while Pass 4 (4)'s domain is Ũ^c₁(X) in (𝐔, 𝐉) with (2.36) on 𝐉, and V4's H at (U, J) contains the current term (V3 L384–388: −⟨J_U, h_UD²𝒩_U(0)[a,a]⟩).
*Repair.* Base (U, J_U), J_U the current of U, where Lemma regular-bounds is verbatim; δH = H(𝐔,𝐉) − H(U,J_U) has the entry differences f_{bb′}(𝐔) − f_{bb′}(U) (Lemma c2-regional-entry, analytic in the stencil's links; Cauchy's estimate on a fixed polydisc gives O(α_{1,1})) plus the linear 𝐉-part with |𝐉 − J_U| ≤ O(1)α_{0,1} by (2.36), (2.34); range ρ_L; Re H ≥ γ_L/4. RG2 (2.16) is no longer cited for δH (its constants are RG2's, and it concerns RG2's operators).

**Minors.** m-1: "analytic where Re H ≥ γ_L/4, which contains Ũ^c₁(X) for small g₀" replaces the bare "entire". m-2: the quadratic remainder is R₂ (R₁ is in the gauge/current part); the (i)–(iii) split is now the exact identity Hm^{loc} + tℓ = w. m-3: the per-piece normalisation terms (det ratio (2.17), e^{½⟨m_I,H_Rm_I⟩}) are stated as small-coefficient volume terms. m-4: the entries' analyticity is cited to V4's f_{bb′} (Lemma c2-regional-entry); RG2's δ₀ is not CRE's δ₀. m-5: the localisation is per bond of Z₀ with the decay of m from J₁(Λ). m-6: Pass 6 (e) now says "Lemma c5-3-1(b) and Remark c5-3-2 transfer verbatim to the 𝒬⁺ rounds (V4's rounds use 𝒬)" in place of "No change to V4 is needed". m-7: the local gauge for Lemma regular-bounds comes from (2.34) through V4 Lemma c2-local-gauge (L3977), not from the cube gauge (2.38).

## it1-rh-a-20261026-r3 (R-𝐇, map l.971–973)

All ten minors verified and applied at map l.972–973:
- N1 (gauge of the argument bound): 𝒰_j is G-invariant and has no axial condition; the bound was derived for real bases in the axial gauge (CRE p.247–248, REG (1.19)/(1.24)). Added: the covariance reduction, M^·(𝐔^v) = M^·(𝐔)^{v̄} (CMP 98 (93), iterated; PBG p.395's transport law), U_k(V^{v̄}) = U_k(V)^{v̄} (VAR (181), p.307 for G^c), so 𝐇^{(j)}(𝐔^v)(b) = v̄(b₋)𝐇^{(j)}(𝐔)(b)v̄(b₋)^{−1}, same modulus; every real U has an axial representative (REG p.79), and 𝐔^v ∈ 𝒰_j.
- N2 (units of the decay): p.268's LMR_{j+1}-cubes are in the units where (j+1)-blocks have side L (CRE p.246, p.256); (190)'s distance is PRT2 (2.46)'s (p.231, in the local set), counting the layer's own blocks, so the separation is ≥ ½MR_{j+1} and the condition is (δ₀/32)M ≥ L+1 (was (δ₀/32)LM ≥ L+1; map l.222, l.973, l.981, l.984; READINGS row 2). The deleted "[3] not in the local set" was wrong.
- N3 (polydisc constants): phases ≤ 2L^{n_b}ρ_b = c₃/2, ‖R(u^{±1})‖ ≤ e^{O(dL)c₃} ≤ 2 for c₃ ≤ c/(dL); Prop. 3's composition needs c₃ ≤ 1/(12C₁^{CMP}); the principal logarithm needs C_{d,L}c₃ < 1.
- N4 (reference data): the averages of a lift are the lift, M^m(Q^{s*}V) = Q^{s*}V (CRE (1.3): V(c) on the bonds between the blocks, 1 inside; every block path of (106) transports V(c)), so V″ = Q^{s*}(V′) exactly and (127)–(129) are not needed there.
- N5: Φ_b(h) = u(h)^{−1}(b₋)·exp iQ̃_j(h)·(R̄^ju(h))(b₊) (the garbled factor "(V^{(j)}_{Y_j}(b))^{−1}V^{(j)}_{Y_j}(b)" removed); u(0) = 1 (the reference is in the axial frame); "factors of u(h) and u(0)^{−1}" → "factors of u(h)".
- N6: "(106) uses the averages of the levels up to j along contours inside the (j+1)-blocks".
- N7: Y_j's second boundary component (∂Λ_j) carries argument too; it is farther from S_{j+1} ⊂ Ω_{j+1} by CRE (3.5) with p.265's B^{j+1}(P¹_{j+1}) (eight layers of LMR_{j+1}-cubes), so the first component's bound covers it.
- N8: ε₁ is the larger of V₀'s curvature bound and 3α_{1,n}/C₁^{VAR} (|e^{iB} − 1| ≤ (3/2)|B| for |B| ≤ 1/2).
- N9: PBG (3.33)–(3.34) cited for the conjugation of G′, R, Δ_a, G under gauge transformations, extended to G^c by analyticity as VAR p.307 does for (181).
- N10: "|C| < C₁^{CMP}(Lα₁)²".

## it1-rh-b-20261026-r3 (R-𝐇 frame links, R-𝐇₀)

- n4 (map l.972 (ii), "conjugation cost ≤ 2 as for u above" was unargued for the G^c-valued u_L): written out. u_L is the tree-gauge transformation to the axial representative (REG (1.19); CMP 98 (77), (87)), level by level ≤ d(L−1) block bonds with averaged phases ≤ 2L^nη sup|𝓗| ≤ 2ε₂L^{n−j} ((127)–(131), VAR (19)), total phase ≤ 4dε₂, ‖R(u_L^{±1})‖ ≤ e^{8dε₂} ≤ 2 for ε₂ ≤ (log 2)/(8d); analytic in 𝓗 as a finite product of Prop. 3's averages — the construction of u(h), applied to U₀.
- n1–n3: already in round 35's form (the lift identity, the Landau frame of (190), p.309's extension); no change.

## Files changed

- WILSON_IT1_D2_STEP_MAP_2026_10_22.md: l.972 (N1, N3, N4, N5, N6, N8, N9, N10, n4), l.973 (N2, N7), l.222/l.981/l.984 (decay condition), l.185, l.188 (R-c status).
- RC_PROOF_PASS_2026_10_23.md: Pass 6 (f) rewritten; Pass 5 (a), (d) and Pass 6 (c), (e) amended.
- READINGS_RECHECK_2026_10_23.md: rows 2, 28, 35; summary.
- SESSION_HANDOVER.md: round-36 entry.

Hashes after the repairs: Map 9814f453f6c5, RTR 2d7c298f53eb (unchanged), RC 1cbe78b41456, READINGS aa9dca712a37.

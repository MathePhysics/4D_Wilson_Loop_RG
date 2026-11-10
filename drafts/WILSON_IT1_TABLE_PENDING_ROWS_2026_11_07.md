# Table rows held during the LF 13a r5 freeze (7 Nov 2026)

The LF session froze the LF, the table, and the Cauchy note at 20:27 while 13a1 r5 runs (SESSION_HANDOVER.md). The table fork had entered the two rows below at 20:28, after the freeze, without seeing it. It removed them again, so the table is back at c6beb03f3952 and LABELS at f93fef03e92d, the hashes the freeze records. The rows go in after #T6.5 once the freeze ends, followed by a relabel.

The rows were requested by two-loops after BC referee bc38 r1. They were re-derived from CMP98 *_corrected.tex (file line = print line, #T6.6). Two-loops' pins for (92), (97), and (99) were off and are corrected here. R̄_{0,c} := R((V̄₀)_c) is CMP98 p.027 l.35.

- {#T6.5-1} CMP98 (92), (97), (99) (p.031 l.55–59, p.032 l.28–35, l.49–53): for U = U₁U₀, the relative k-th average is (Ũ₁^k)_b = v_k(b₋)(Ū̿₁^k)_bR̄^k_{0,b}v_k^{−1}(b₊) = (Ū̿₁^k)_b^{v_k}, with R̄_{0,c} := R((V̄₀)_c) the conjugation (p.027 l.35; R(U)X := UXU^{−1}, #T11.19-1), Ū̿₁^k the composed average of (89)–(91), and v_k(x) = (R_{0,x}U₁)‾(R̄_{0,x}Ū̿₁)‾⋯(R̄^{k−1}_{0,x}Ū̿₁^{k−1})‾ (97), which is the k-th average of R_{0,x}U₁ at x (99). So (1/i)log Ũ₁^k and Q_k := (1/i)log Ū̿₁^k differ in general by the factors v_k(b±).
- {#T6.5-2} CMP98 Proposition 3 (p.036 l.49–52): there are C₁ = C(d) and c₃ = c(d, L) ≤ c₂ such that, for α₀, α₁ ≤ c₃, Q(V₀, A) = (1/i)log V̄̿₁ is analytic in A with (122)–(124); so it holds at 𝔤^c-valued A in that ball. By (127) (p.037 l.2–8), (1/i)log Ū̿₁^k is the composition Q_k(U₀, ηA) of Q(Ū₀^j, ·), j < k, and for U₀ under Proposition 2's assumptions and U₁ = e^{iηA}, abs(A) < α₁, (130)–(131) (p.038 l.1–15) give abs(Q_j(U₀, ηA)) < 2α₁L^jη; for α₁ ≤ ½c₃ Proposition 3 then applies at each step (p.038 l.17).

## BETA's edits after R80d (held)

The table fork re-derived these edits from BD 7ca5b0cd909e, BQ 9a4ef80ae827, and BX 9cf57811cdb7 (BR 78c8181e7a0d needs no row change). It checked #BQ.8 (l.32), #BQ.8-3 (l.35), #BQ.10-4 (l.43), #BQ.12 (l.47), #BD.3-3 and #BD.3-3a (l.19–20), #BD.10-2 (l.53, which now uses ψ and no longer defines it), #BX.1-5, #BX.10-1, and #BX.11-1. δ₂, "Q_j(□)", and "ε(δ" no longer occur in BQ or BD. The c₀ left in BQ is Lemma A's c₀ (#BQ.5, l.25–26). Each edit below is old → new, in the table's own text.

- #T12.22: "Q_j(□) := □̃⁴, Q_n(□) := □̃³ for n > j, Ω_n(□) := Q_n(□) ∩ Ω_n, X_□ := Q_□G_□Q_□*, and δ₂ := δ₀/(√dL²) (#BQ.8, #BQ.8-3), not #T3.27's or #T12.15's δ₂, nor #T12.8's X_□;" → "□^{(n)}, n < j, the cubes of PBG p.408 l.30–32, □^{(j)} := □̃⁴, □^{(n)} := □̃³ for n > j, and Ω_n(□) := □^{(n)} ∩ Ω_n (#BQ.8); X_□ := Q_□G_□Q_□* and d_□, the local distance (#BQ.8-3), not #T12.8's X_□;"
- #T12.22-1: "ρ(c) := d(c,c₀)" → "ρ(c) := d(c,c_⋆), c_⋆ a fixed bond"; "The c₀, t, T, ε, and δ₁ here are local" → "The c_⋆, t, T, ε, and δ₁ here are local"; add "f_□ := h_□G_□h_□v (#BQ.10-4);" after the #BQ.10 entries.
- #T12.23-1: "δ := 1/10 (#BD.3-3), not #T4.30's δ;" → "ψ(a, b) := (1/i)log(e^{ia}e^{−ib}), not #T12.21's profile ψ, with r_ψ = r_ψ(G) and c_ψ = c_ψ(G) its radius and constant (abs(∂_aψ − I) ≤ 1 and abs(ψ(a, −b) − a − b) ≤ c_ψabs(a)abs(b) for abs(a), abs(b) ≤ r_ψ), and N = N(d, L), the maximum number of contours in 𝐆(y, x) (#BD.3-3); Z_m := ψ(Z_{m−1}, −z_m) with Z₀ := 0, δ := 1/10, not #T4.30's δ, and ε_δ = ε_δ(d, L, G) > 0 with e^{c_ψε_δ} ≤ 1 + δ, (1 + δ)ε_δ ≤ r_ψ, and abs(log M({e^{iz_Γ}})) ≤ (1 + δ)max abs(z_Γ) for max abs(z_Γ) ≤ ε_δ (#BD.3-3a);" and delete "ψ(a, b) := (1/i)log(e^{ia}e^{−ib}) (#BD.10-2), not #T12.21's profile ψ;". N may need a clash note against the other N rows, to be checked when entered.

## Two-loops' #T12.27 update after bc38 r1 (held)

Re-derived from BP_DERIVED_CONFIGS.md 59a87ac1e28a, at #BC.5-1-3, #BC.5-1-3-4, #BC.7, #BC.8, and #BC.8-2-1 to #BC.8-2-2.
- C_{BX}: v_n^{±1} each within e^{4dLt} − 1, and e^{iQ_n} within e^{2Lt} − 1, give e^{(8d+2)Lt} − 1 ≤ 2(8d + 2)Lt ≤ ½. Then abs(B^X) ≤ 4(8d + 2)Lt = (32d + 8)Lt.
- t^X: abs(𝓗^X) ≤ (2B₅/C₁)abs(B^X).
- δ_F: σ_l := d(L − 1)t^XL^{l−n} is (d(L − 1)/2) factors × 2t^XL^{l−n}, and Σ_{l<n}σ_l < dt^X. With 10dt^X < 1, e^{5dt^X} − 1 ≤ 10dt^X.

- #T12.27: "t := (2B₅/C₁)abs(B), t^X := 4LB₅t/C₁, and δ_F := 16dt^X, with Θ ≤ (1 − δ_F)^{−4}e^{d(t+t^X)} (#BC.8), δ_F not #T12.9's δ_f." → "C_{BX} := 32d + 8, with abs(B^X) ≤ C_{BX}Lt(B) for Lt(B) < ½c₃ and (8d + 2)Lt(B) ≤ ¼ (#BC.5-1-3), not #T12.9's C_d; π, the orthogonal projection onto 𝔤^c for tr X*Y (CMP98 p.020 l.31–34), a definition: #BC.7 takes π orthogonal for tr X*Y, while RG I (1.8) prints "the projection" onto 𝔤^c and names no complement (p.261 l.36–41) (#BC.7); t := (2B₅/C₁)abs(B), t^X := (2B₅/C₁)C_{BX}Lt, and δ_F := 10dt^X, with Θ ≤ (1 − δ_F)^{−4}e^{d(t+t^X)} for t^X < ½c₃ and δ_F < 1 (#BC.8), δ_F not #T12.9's δ_f."
- #T12.24-1: "M₀ := ⌊M/4⌋, and b₁ := O(1)LMBα₀ (#BX.10-1), not the M₀ of #T4.30" → "M₄ := L^{−2}M, a power of L (M = L^m, RG1 p.257 l.3) with M₄ ≥ M₃ ≥ 2R₀M₀ (BQ's K ≥ 2, #BX.11), so M₄ = KR₀M₀ with K ≥ 2 as R₀, M₀ are powers of L (PBG p.408 l.26–28) (#BX.10-1); BX needs M ≥ L²M₃ (#BX.1-5, #BX.11-1); b₁ := O(1)LMBα₀ (#BX.10-1a)". This is amended per BETA's recheck (BX b1de415ff627, BQ 248571cab4b3, BD a2968184d2bd). Re-derived: RG1 p257_corrected l.3 prints "M=L^m". PBG p.408 l.26–28 takes R, M as powers of L and M = KR₀M₀ with K a positive integer. M₄/(R₀M₀) is then a power of L that is ≥ 2, hence an integer K ≥ 2. No table row cites #BX.10-1b, #BD.3-4a/b, or (I5), so the (Loc) move to #BX.10-1c and the corner-block sign fix need no row change. BQ's j_c (#BQ.10-1) is a bound index local to one estimate, so it gets no row.

## Two-loops' #94 split (held)

At TL 940d14e17be9, #94 keeps the VAR Theorem 1 inputs, the choice of ε₁, and BC's thresholds. #94-1 holds Proposition 9, r_B, (172), and (190) with its gradient and D*D entries; this was checked at TL l.206–207. Both of #T4.48's #94 citations are for (190) on the ball. No other table line cites #94.
- #T4.48: "rooms (#94, #128)" → "rooms (#94-1, #128)", and "two-loops #14, #94, #121, #128, #138" → "two-loops #14, #94-1, #121, #128, #138".

## Entered

Everything above was entered at table 9e1dbb8c8284 (LABELS bfdc1e21d136, LF 22a21c559148) once (2) ended the freeze. The BETA and BC sources were re-hashed unchanged first. #BD.3-3's N was entered with "not #T12.20's N".

## Two-loops' 𝐉_{p,X} row (held for (2)'s builds of 13a1 r6, 13a2 r6, 13b r3, 22:02; entered at 22:09, table 3b28dde0e875, LABELS 00aaa0b56fb6)

Re-derived from the corrected transcripts: CRE p.260 l.54–55 and p.261 l.2 ("spaces defined similarly as in (I.1.11)–(I.1.16)"), p.261 l.10 (U_{p,X} and 𝐉_{p,X} listed together), (2.34)–(2.37) at p.261 l.15–22; RG I (1.8) at p.261 l.37 and (1.15) at p.262 l.46–50. (2.35) has L^{−2p} where (2.34) has ξ², and (2.37)'s (L^nL^{−p})^{−3} is (2.36)'s (L^nξ)^{−3} at ξ = L^{−p}. To go after #T6.11:
- {#T6.11-1} CRE's 𝐉_{p,X}(M^·(𝐔)) of (2.37) is RG I's J_n of (1.15) at n = p on X: the current (1.8), D^{ξ*}_{U}ξ^{−2}π Im∂U, at U = U_{p,X}(M^·(𝐔)) := U(𝐁_p(X) ∪ {Γ_i}_{i<p}, M^·(𝐔)) and ξ = L^{−p}. CRE prints no formula; its spaces are defined "similarly as in (I.1.11)–(I.1.16)" (p.260 l.54–55, p.261 l.2, l.10), and RG I defines J_n "by the formula (1.8) with U_n(M^·(𝐔)) instead of U_j, L^{−n} instead of ξ" (p.262 l.49–50). (2.37)'s room α_{0,n}L^{n−min{p,n}}(L^nL^{−p})^{−3} (p.261 l.21) is (2.36)'s at ξ = L^{−p}, times L^{n−min{p,n}}.

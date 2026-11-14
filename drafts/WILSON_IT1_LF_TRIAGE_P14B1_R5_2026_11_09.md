# Packet 14b1 (Cauchy #C10.3.1–#C10.3.16), Round 5, 9 Nov 2026

## Pre-Check of cauchy-p14b1-20261109-r5 (Narrow)

- **Under review:** the lines repaired after round 4 (S1 and m1–m3, WILSON_IT1_LF_TRIAGE_P14B1_R4_2026_11_09.md), with their consumer #C10.3.10-2:
  - #C10.3.3-6–#C10.3.3-10-1, including the new #C10.3.3-10-0, #C10.3.3-10-0-1, and #C10.3.3-10-0-2;
  - #C10.3.3-11-6–#C10.3.3-11-8-1, including the new #C10.3.3-11-6-0-1;
  - #C10.3.10-2.
  The rest of 14b1 is context. So are the consumers in 14b2 (#C10.3.42-3, #C10.3.43, and #C10.3.51–#C10.3.51-1, under review in cauchy-p14b2-20261109-r4).
- **Every changed line re-read** at Cauchy 1f73875e3b26 (lines 1822–1852). The re-read found three weak points, repaired before the build:
  - **#C10.3.3-10-0-1.** The comparison "α₁/L ≤ O(1)M·α₁/(10ML)" used PBG's O(1) ≥ 10 without a pin. PBG p.396 l.16 prints "Here O(1) will mean a number ≥ 10". The sentence now reads "PBG's O(1) being ≥ 10 (p.396 l.16), 3α₁/L ≤ 2O(1)M·α₁/(ML) and (3/2)O(1)Mα₀ ≤ 2O(1)Mα₀". At 621 characters it was split at the sentence into #C10.3.3-10-0-2, and #C10.3.51-0-2's range was re-pointed to "#C10.3.3-10-0–#C10.3.3-10-0-2".
  - **#C10.3.3-8.** "the complex extensions of G′, R, and G₀ are given by Theorem 3.4": Theorem 3.4 (p.400 l.7–10) names G(U). The line now adds "(Theorem 3.4's G, p.421 l.33)"; p.421 l.33 prints "operator we have investigated in previous sections by G₀, i.e. G₀=(Δ+DRD*+Q*aQ)^{−1}".
  - **#C10.3.3-11-6-1.** "bounds the coefficient of ss′" did not say of which function. It now reads "the coefficient of ss′ in F_c, 2Lℓ·C̃^{(2)}(X1_b, Y1_{b′})(c)".
- **Re-derived:**
  - **#C10.3.3-10-0.**
    - 𝐔^u(b) = u(b₋)e^{iεA(b)}U₀(b)u(b₊)^{−1} = e^{iεA^u(b)}e^{iεA₀(b)}, with |A^u| = |A| < (α₁/L)ℓ^{−1} because u is real.
    - The one-bond transport has |Ad(e^{iεA₀}) − 1| ≤ e^{2ε|A₀|} − 1 ≤ 4ε|A₀|, so ∇A^u differs from the covariant gradient by ≤ 4|A₀||A| ≤ 4O(1)Mα₀(α₁/L)ℓ^{−2} ≤ (α₁/L)ℓ^{−2}.
  - **#C10.3.3-10-0-1.**
    - ε^{−1}|Φ(εA^u, εA₀)| ≤ c_Bε|A^u||A₀| ≤ c_Bα₁O(1)Mα₀ℓ^{−1}, using ε ≤ ℓ and L ≥ 1.
    - The finite differences of ε^{−1}Φ, by the mean value along segments inside the ball of radius r_{BCH}/2, are ≤ 2c_B(O(1)Mα₀|∇A^u| + α₁|∇A₀|) ≤ ½(|∇A^u| + |∇A₀|).
  - **#C10.3.3-10-0-2.**
    - |A_tot| ≤ (α₁/L + 2O(1)Mα₀)ℓ^{−1} ≤ 2O(1)M(α₀ + α₁/(ML))ℓ^{−1}, by c_Bα₁ ≤ 1.
    - |∇A_tot| ≤ (3α₁/L + (3/2)O(1)Mα₀)ℓ^{−2} ≤ 2O(1)M(α₀ + α₁/(ML))ℓ^{−2}, by 3 ≤ 2O(1).
    - 4c_Bα₁ ≤ 1 follows from #C10.3.51-0-1's 64c_Bα₁ ≤ 1.
  - **#C10.3.3-11-6-0-1.**
    - |A″| ≤ r_P/2 + r_P/3 + c_Br_P²/(6L), and c_Br_P²/(6L) ≤ r_P/(6L) < r_P/6 for L ≥ 2, so |A″| < r_P.
    - Factors X and Y within 1/8 of 1 give |Y^{−1}| ≤ 8/7 and |Y^{−1} − 1| ≤ 1/7, so |XY^{−1} − 1| ≤ 2/7.
    - |F_c| ≤ log(7/5) < 1/2.
  - **#C10.3.3-11-6-1.**
    - On |s|, |s′| ≤ ρ := r_P/(4Lℓ), Lℓ sup|B| ≤ 2Lℓρ = r_P/2, the case b = b′ included.
    - The coefficient of ss′ in F_c is ≤ (1/2)ρ^{−2} = 8(Lℓ)²/r_P².
    - It equals Lℓ times twice C̃^{(2)}(X1_b, Y1_{b′})(c), cubic and higher terms giving no ss′, so |C̃^{(2)}(X1_b, Y1_{b′})(c)| ≤ 4Lℓ/r_P².
  - **#C10.3.3-11-7.** b₀(c′) has both end-points in B(c₋) ∪ B(c₊) only if c′ = c as an unoriented bond, so Q̄₁(W)h = I.
  - **#C10.3.3-11-7-1.** |h(c)| = L^d|T_c^{−1}(1 + e_c)^{−1}| ≤ L^d(4/3)·2.
  - **#C10.3.3-11-8–#C10.3.3-11-8-1.**
    - 2·2d·(8/3)·4 = 128d/3, and 4N times that is 512Nd/3.
    - The powers are L^{−3}·L^d·L = L^{d−2} and ℓ^{−d}ℓ^{−3}ℓ = ℓ^{−2}ℓ^{−d}.
    - The support distance ≤ (d + 1)L gives e^{δ₁′(d + (d+1)L)} ≤ e^{δ₁′(2d+1)L}.
  - **#C10.3.3-6, #C10.3.3-10, and #C10.3.10-2.** Pins re-read today:
    - p.419 l.11–12: "From now on we assume that U satisfies the regularity conditions (3.35), (3.36)", for J small;
    - p.422 l.15–21: (3.132) for (QGQ*)^{−1} "and the same for the operator with G₁";
    - p.422 l.50: |(H*J)(b)| ≤ O(1)Mα₀(L^jη)^{−3} from (3.36) and (3.133);
    - p.423 l.33–36: Theorem 3.12 for an external field satisfying (3.35) and (3.36) "for α₀ sufficiently small";
    - p.396 l.46: (3.38) asks (3.35) and (3.36) of U.
- **Consumers grep** (tag-exact, over the Cauchy note, the LF, the W-δ note, and balaban_proofs/):
  - C_𝐉 is used at #C10.3.42-3, #C10.3.43, #C10.4.122, #C10.4.123, and #CK.1-28, as a symbol only.
  - r_P is used in #C10.3.3-11-6-0–#C10.3.3-11-8-1, #C10.3.51-0-2, and #CK.1-28.
  - #C10.3.3-6, #C10.3.3-9, and #C10.3.3-10 are cited by #C10.1.3-3, #C10.1.6-1, #C10.2.1, #C10.2.1-0, #C10.2.3, and #C10.3.10-2, all for content still at the cited tag.
- **Table and peers.** The fork applied r_{BCH} at #T12.7-24-2 and #T12.7-24-4 (table 40e20f5e4530), and later changed δ₁′ to min(δ_cx, ½δ₀)/8 with δ_cx ≤ δ₁ (table 1e252f854c47, LABELS 7de12f87e5de). No line here restates δ₁′'s formula. The fork was told of #C10.3.3-10-0-2.
- **Definition check:** 0 conflicts (6 allowed). **Size:** reviewed blocks 6.80k (25k cap), max line 512. CR is 0, and there are no trailing spaces or duplicate tags.
- **Spec:** specs\spec_p14b1_r5.json (Cauchy a0464784c8bc, LF 029a1d03a304).
- **Order:** after 14bp r6, which is running. Rebuild at launch.

Written 2026-11-09 10:25.

## Round 5, Reviewed by Me in Place of the Referee

- **How:** at the user's request, no referee was launched. I read every line under review and its context against PBG and CMP 98 in the corrected transcriptions. Every PBG pin above was re-read.
- **Verdict:** clean; two cosmetics, repaired.
- **Cosmetics:**
  - #C10.3.3-11-6-0 called r_P "a constant of d and L", but r_P ≤ r_{BCH} and c_Br_P ≤ 1 make it depend on G. It now reads "Let r_P, a constant of d, L, and G, be an α₁ of CMP 98 Proposition 6".
  - #C10.3.10-2's "So (3.132)–(3.133) hold for it" did not say which bound is for which operator. It now reads "So H₀ satisfies (3.133), and (Q_jG₀Q_j*)^{−1} (3.132), at real U".
- **Checked and correct:** the re-derivations above, line by line, and the factor N of the C_𝐉 bound, which is defined for a general compact G.
- **Next round:** a full round, at Cauchy 282155b15f71.

Written 2026-11-09 16:41.

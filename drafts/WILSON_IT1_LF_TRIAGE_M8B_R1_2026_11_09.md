# Packet M8b (the lines converted to RG I (0.4)), round 1, 9 Nov 2026

## Pre-check of lf-m8b-20261109-r1 (narrow)

- **Lines under review:**
  - Cauchy: #C5.22-3, #C7.5-2, #C9.3.1-1–#C9.3.1-3, #C9.4.3-2, #C9.4.4-4, #C9.4.5, #C9.8.1–#C9.8.1-2, #C9.8.14–#C9.8.14-2, #C9.8.18-7, #C10.4.9-1-1–#C10.4.9-3, #C10.4.35-3–#C10.4.35-4, #C10.4.67, #C10.4.70-1, #C10.4.71-2, and #C11b.2-3.
  - LF: #4.51, #4.52-1-1.1-1, #4.174–#4.174-0-2, #4.454.4-2, #4.561.1–#4.561.1-0, #4.597-1, and #5.21–#5.22.
  - W-δ: #W10.5.45-16–#W10.5.45-18 and #W11.161-4.
  - BP_VAR_PROP4: #4.36-0-3.
  - Context: the convention #C10.1.4–#C10.1.4-1-1, #C11b.2-4, #C10.3.3-11-1–#C10.3.3-11-2-1, the axial gauge #C10.4.9–#C10.4.9-1, and δ_T's consumers #C10.4.11–#C10.4.12. BP_LFR2 #3.84-1.1 and #3.85.1, reviewed CORRECT in 12b-bp r2 (full), are also context.
- **Every line re-read** on 9 Nov 2026, against the convention #C10.1.4-0-1–#C10.1.4-0-2: MW(c) = e^{iY_c}W(c), Y_c = L^{−d}Σ_x|𝐆(c₋, x)|^{−2}Σ_{Γ,Γ′}(1/i)log h_{c,x}^{Γ,Γ′}, and h = W(γ)W(c)^{−1} with γ = Γ ∪ [x, x′] ∪ (−Γ′).
- **Re-derived:**
  - Path lengths. Γ and Γ′ have |n|₁ ≤ dL/2 bonds each and [x, x′] has L, so γ has ≤ (d + 1)L, and the loop γ ∪ (−c) has ≤ (d + 2)L. A coordinate-monotone path from the centre of a cube to one of its points stays in the cube, so γ ⊂ B(c₋) ∪ B(c₊). The plaquette count is A_L ≤ (d − 1)(d + 4)L²/8 ≤ dL² for d ≤ 5 (BP adjoint #C10.3.21-6).
  - #C9.8.1: the linear part of log MW(c) is L^{−d}Σ_x mean_{Γ,Γ′}[A(γ) − A(c)] + A(c) = L^{−d}Σ_xA(γ̄_{c,x}). The units are LηĀ = ηL^{−d}ΣA(γ̄), so Ā = L^{−(d+1)}ΣA(γ̄).
  - #C9.8.1-1–-2: I wrote out the four chains. Γ̄_{y,x} occurs with +1 (c₁) and −1 (c₄). Γ̄_{y+Le_μ,·} occurs with −1 (c₁) and +1 (c₂). Γ̄_{y+Le_ν,·} occurs with −1 (from −c₃) and +1 (from −c₄'s −Γ̄). Γ̄_{y+Le_μ+Le_ν,·} occurs with −1 (c₂) and +1 (from −c₃'s −Γ̄). The four segments leave ∂S_x, and x + Le_μ ∈ B(c₂₋).
  - #C9.8.14-1: two axial contours to adjacent points agree up to the direction of b, then run parallel. The loop bounds ≤ (d − 1)L/2 fine plaquettes, of area ≤ dε²/(2L).
  - #C9.8.18-7: under v, W(c) ↦ ṽ(c₋)W(c)ṽ(c₊)^{−1} and h ↦ ṽ(c₋)hṽ(c₋)^{−1}. So e^{iY}W transforms covariantly, by f(ghg^{−1}) = gf(h)g^{−1}.
  - #C10.4.9-3: changing x by one μ-step either keeps the set of directions, giving a bijection of 𝐆, or adds or removes μ. In the latter case each contour of the smaller family arises from m + 1 contours of the larger by deleting the μ-run, the same number for each. Equal repetition leaves Federbush's average (0.10) unchanged.
  - #C10.4.35-4: the fine plaquettes of e^{i(ε/L)Y} have log O((ε/L)²|Y|²), and the loops are spanned by ≤ dL² of them. So Y_c = O(ε²|Y|²) and Ȳ_μ = Y_μ + O(ε|Y|²).
  - LF #4.561.1-0.0–-0: |A′_R| + 25|A′_I| ≤ 26|A′|, and e^{27t} − 1 ≤ 54t for 27t ≤ 1. C_{V′}ε₁′ ≥ 240c_avα̂₁ with C_{V′}ε₁′ ≤ ½ gives 27c_avα̂₁ ≤ 27/480, and 54 ≤ C_c = 60.
  - W-δ #W10.5.45-17: at W ≠ 1 the linear part carries dlog_h and dexp_Y, each within O(|log h(W)|) of the identity, which is the second term of the BCH bound.
- **Repairs made in this pre-check:**
  - #C10.4.9-2 bounded the coarse links by "the logarithms of (0.4) adding a second-order term". Y_c is first order in ε²|F|, so this did not bound them. The line is rewritten in place and split.
    - #C10.4.9-2: the path transports are within 4d(d + 1)ε²|F| of 1.
    - #C10.4.9-2-1: the loops have ≤ (d + 2)L bonds within 4dε of y, so |h − 1| ≤ 4d(d + 2)ε²|F| and |Y_c| ≤ 2πd(d + 2)ε²|F| by the (π/2) of #T11.26. Hence |e^{iY_c}U^B(c) − 1| ≤ (2πd(d + 2) + 4d)ε²|F|, and |Ad(g) − 1| ≤ 2|g − 1|.
    - δ_T = 32d²ε²|F| is unchanged. It holds for d ≥ 2, since 4πd² + 8πd + 8d ≤ 32d² for d ≥ 1.71, and 8d² + 14d and 8d² + 8d are ≤ 32d². Its consumers #C10.4.11, #C10.4.12, #C10.4.36-1, #C10.4.49-2, #C10.4.50, #C10.4.70-2, #C10.4.71-3, #C10.4.74-1, #C10.4.97-2, #C10.4.109-4, and #CK.1-25 use only the value.
  - BP_VAR_PROP4 #4.36-0-3 quoted PBG p.414 l.15 as "the bonds with an endpoint in B^j(c₋) ∪ B^j(c₊)". The print sums over b ⊂ B^j(c₋) ∪ B^j(c₊), and the line now says so. The new set is a subset of the old, so #4.36-0-4's spans only tighten.
  - Cauchy #C5.22-3: RG I's analyticity statement and (3.26) are p.275 l.19–26, no longer l.18–24.
  - REG pins under #T6.6 (a REG pin is the file line minus 1). The table fork passed on two pins in BP_COMPLEX_BASE_GAUGE (#4.536.1 → p.79 l.4, #4.536.3 → p.88 l.36). I checked them and swept the REG pins of my files.
    - LF: #4.517-0 p.88 l.9 → l.8; #4.517-0-1 p.88 l.37–38 → l.36; #A.9.3-1 and #A.11.1.1-2 p.78 l.15 → l.14.
    - Cauchy: #C9.4-1 p.099 l.43 → l.42; #C9.8.6-3 p.077 l.17 → l.16 (×2) and p.098 l.19 → l.18.
    - W-δ: #W12.237-2 p.098 l.17–18 → l.18.
    - BP_LFR2: as in WILSON_IT1_LF_TRIAGE_P12BBP_R2_2026_11_09.md.
    - The table pins near #T11.19 (p.78 l.15–19 and p.77 l.17–19) are sent to the fork.
  - W-δ #W10.5.45-16 now states (0.4) as e^{iY_c}U(c), with U(c) the straight transport along the L fine bonds of c. It had omitted the exponential form.
  - LF #4.174 (1306 characters) is split at its sentence boundaries into #4.174, #4.174-0-1, and #4.174-0-2. No words changed.
- **Citations quoted and checked:**
  - RG I p.275 l.19–28: "We will prove that it is analytic on the space U′^c_{k+1}(□₀, (1+2β)α₀, (1+2β)α₁, α₀)" and (3.26): M^·(𝐔) = V^v, |V(b) − 1| < O(1)Mα₀, |v − 1| < O(1)Mα₁; V(b) = Ū^{k+1}(Γ_{y₀,b₋} ∪ b ∪ Γ_{b₊,y₀}).
  - CRE (1.3) (p.246 l.38–45): Q₁^{s*}V is 1 on b ⊂ B(y) and V(c) on b ∈ B(c). CRE p.257 l.34: "only 1-blocks are replaced by k-blocks".
  - CMP98 (43) (p.024 l.2–5) is the iterated average. CMP98 (53) (p.026 l.27–34) is the inductive plaquette bound, and (54) (p.026 l.46–52) is Proposition 2, α₀ ≤ c₂ = min{1/(3C₀), c₂′/2}.
  - PBG p.414 l.15 prints (Q_jA)(c) = Σ_{b⊂B^j(c₋)∪B^j(c₊)}L^{−jd}Q_j(c, b)A(b). VAR (48) (p.285 l.37–43) shows C_j as the nonlinear part of Q_j(ηA).
  - Table #T11.26: abs(U − 1) ≤ abs(log U) ≤ (π/2)abs(U − 1) for unitary U.
- **Definition check:** 0 conflicts (5 allowed).
  - c_av: LF's O(1) of #4.523 and the adjoint file's max(4d, 1/(8ρ_𝔤)) are different objects, a clash the table fork now records in #T12.12(a) (table 0d6adc9e81d4, LABELS 9faef7334bc0, relabelled against LF 6ac728004094).
  - δ_T: the note's own constants index.
  - F, W, X: local abbreviations of W-δ.
- **Size:** the reviewed blocks are 15.7k (25k cap). Before the pre-check they were 15.4k; the growth is #C10.4.9-2-1's bound. The longest reviewed line is LF #4.561.1-0.0 (under 600).
- **SHAs:** LF 6ac728004094, Cauchy c495b103652a, W-δ 8322401162ae, BP_VAR_PROP4 ff78146d9430, BP χ_{k,Λ} df3dad742c4d, BP_COMPLEX_BASE_GAUGE fcde092b1e4e.
- **Spec:** specs\spec_m8b_r1.json.
- **Order:** after packet 50 r1. Rebuild at launch.

Written 2026-11-09 07:58.

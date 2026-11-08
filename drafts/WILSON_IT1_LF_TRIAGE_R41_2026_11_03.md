# Triage of lf-k0-20261103-r41 (LF f478e9c590fd → 7233fdd32c4d), 3 Nov 2026

Review: verification\isolated_reviewer\reviews\lf-k0-20261103-r41\review.md. Verdict: not established as written; no fatal; one serious (S1), five minor. r40's d6′ and all r40 minors closed. Each finding was checked against the text before repair. All repairs are derived, not reviewed.

## Serious

- **S1, the gauge representative at the interfaces j ≥ 1.** Confirmed: A_N is least on A_N + ∂N(Q′), while H_jV_N is in PRT1's R-gauge (R∂*H_kB = 0), so A_N = H_jV_N + w_G + ∂ζ with Q′_jζ = 0, and V_N is not least on its scale-j orbit. The bound on dA_N stands; the bounds on ‖A_N‖ in ℳ and the pointwise bound in (g)(5) lacked an input.
- **Repair: a scale-j V-problem, a block-anchored lift, and the chain's representative A_♮.**
  - (g)(1) The global decomposition A_N = H_jV_N + w_G + ∂ζ, ζ in the residual group. N_V := {λ′: λ′ = 0 at the scale-j sites of Λ_j and off Ω_j, Q′^{(1)}λ′ = 0 at the blocks of Ω_{j+1}}, and V_L the ℓ²-least element of V_N + ∂₁N_V, so ∂₁*V_L is constant on the blocks of Ω_{j+1}; (K1) and (KW) at scale j run for V_L.
  - (g)(2) "(f) holds for V_L, whose minimality on V_N + ∂₁N_V is the scalar problem on N_V".
  - (g)(6) (new, {#K0.g6}). (i) A pointwise bound for least ν ∈ N_𝔫, 𝔫 := L^j: bump test for the block constants, a cut-off and the Green's function (Lawler–Limic Corollary 4.3.3, p.84), Poincaré on the cube, and the scalar Combes–Thomas argument with δ = c(d). (ii) The block-anchored lift H^Λ_j := H_j − ∂ν, with an exponentially decaying kernel, and H^Λ_j∂₁λ′ = ∂λ̂ with Q′_jλ̂ = λ′. (iii) A_N = H^Λ_jV_N + Z_j, Z_j ≤ C(L)e^{−c(d)RM/16}. (iv) V_N = V_L − ∂₁λ″_j, V_N least for ⟨·,·⟩_♯, Combes–Thomas in both norms, per-block Poincaré. (v) The bounds of ℳ through V_L, with coefficient ε(d)(1 + log L)^{−q}, q = d + 2. (vi) A_♮ := A_N + ∂ω_♮ with a smooth partition χ_j (block-constant cut-offs would cost L^j) and scalar block-mean bump corrections; ω_♮ ∈ N(Q′), R_♮ ≤ θ, abs(Im ηω_♮) ≤ C(L, M)ε₁.
  - (g)(5) (KW) run for V_L; W_j(y′) ≤ (1 + abs(y − y′)/ρ₀)W_j(y); ‖A_♮‖_{W_ms} ≤ C(d)(1 + log L)^pC_H^{reg}θ_B.
  - l.6: "the chain uses A_♮ in place of A_N and ω − ω_♮ in place of ω"; C_H^{reg} ≤ C(d)(1 + log L)^{p′}, constants of d only, no dependence on M or β₀.

## Minor (repaired)

- n1: 𝒞₁ uses the scale-1 bonds with an endpoint in Ω₂, the crossing bonds from Λ₁ into Λ₂ included; likewise Ω_{j+2} in (g)(1).
- n2: the ℳ-coefficient ε(d)(1 + log L)^{−q}, C(d) in r₂ chosen after ε(d) and the constants of (g)(6); the regions use 2r₂; RM ≥ 4r₂/L; δr₂/L ≥ 2(d + 4)log L + C(d)(1 + log(1 + log L)), δRM ≥ d log L + C(d).
- n3: for x₀ ∈ Λ₀, Q_{2L}(x₀) is covered by C(d) cubes Q_{L/(2√d)}(x′) centred in Λ₁.
- n4: block counts C r^d per layer and C r^d(1 + r/RM) in total; only p changes.
- n5: the O(δ) commutator in (g)(2) uses D = 0 on Λ_j and the width RM.

## Labels

Every definition X := … carries {#D.X} (repeats {#D.X.2}, …); index in LABELS_LF_AND_TABLE.md "## Definitions of the LF". The block side of (g)(6) is 𝔫 (n is l.6's {#D.n}), and (g)(6) writes ∂*∂ in place of a local Δ (Δ is l.220's {#D.Δ}). 100 symbols remain defined more than once. First pass: most are case-wise definitions within one step (E, R, Ψ, Ĝ_f, e(b), u, h′_μ, ν_ℓ, s^{W,tot}_K), restatements with the same value (δ^f_j, δ^s_j, κ_s, G₁^Q, Ũ, μ_mem, Δ_𝐇, J′, δ𝐉, q_D(δ), A_♮, W_ms, θ, □₀, k_s, ρ̄(x), M₁, c₀(α), w_K, ω(X)), or letters local to one step (E, t, f, X, W, R, N, w, ℓ, r, v, λ, ρ, K, T, …); ε₁ and ε₃ are VAR's parameters set per application of VAR (§1.3, §4.43, §4.525; §4.37, §4.47, §4.561). α₀, t^X, α_m, d̄_j, and δ_w were checked in context: each definition is confined to its step (t^X differs by the common factor M₀ of both runs, which cancels in §3.10's relative bounds).

## Queued (apply after r42 lands; the LF is not edited during a review)

- **C_H has five meanings.** (1) l.6, the LF's constant C_H := C(d)(1 + log L)^pC_H^{reg} (the one table l.232 and the two-loops note read); (2) the segment constant of §4(d)(iii), l.12, 496, 501–502, 651–657, 742, 775 (C_Hϑ̂_H ≤ 1/6, a constant of L, B₅, …); (3) Proposition 9's data constant, l.664, 728–734, 772, 783 (|V′ − 1| < C_Hε₁′; VAR p.305 l.41–44 prints this as C₁, with B₅ = 6B₁B₃C₁); (4) l.210, ‖HD(A)‖_y ≤ C_Hε₃Σ…; (5) l.598–606, the walk-term factor C_Hδ_w; l.871 (§4.645) uses C_H for the sup-norm constant of 𝐇_k^{(ν)} on a field of amplitude δ′_j; RG I p.271 ("The derivative δ𝐇_j/δB is an exponentially decaying function, with the decay rate δ₀ on the ξ-scale, see Proposition 9, (190) [15]") makes it the sum of (190)'s kernel, which is (1) by l.6 ("C_H is the sum of (190)'s kernel over the data"), so l.871 keeps C_H and gains the pointer "(l.6)". None of (2)–(5) is Bałaban's printed C_H, and the table (l.232) reads only (1). Repair: keep C_H for (1) only and give (2)–(5) distinct names, each step read in full before the rename, no line count changed. (2) is quoted twice in the walk-factor note (l.176 and l.482, "the LF note's C_Hϑ_H ≤ 1/6"); those two quotes change with it, hash-checked, and the fork is told. (5) is the walk-factor note's constant of §7 l.155, |(Q₁H^B(s) − H^A(s))X| ≤ C_telδ_w(Y)B₀′e^{16κ₁}|X|, to be written as such once §4.380's H(s) is matched to that setup. (4) is the product of (3.133)'s constant with (73)'s O(1)C₃.
- **δ_w has three meanings.** The walk-term factor δ_w(ω) of the walk-factor note (l.598–606), and the weight rates δ_w := δ₀/32 (l.447, §4.236) and δ_w := ⅛δ_min (l.496, §4.284). §4.380 follows l.496's definition, so δ_w there reads as ⅛δ_min. Repair: rename the two weight rates, which are local to their steps.

## Next

Self-check of (f)–(g). Then the re-review of (K0) (r42, prior review r41), then (K1)–(K6).

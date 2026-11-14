# Packet 50 (LF §4(d): d and 𝐂_k), round 1, 9 Nov 2026

## Pre-check of lf-p50-20261109-r1 (full)

- **Whole part read** (#4.151–#4.169-3) on 9 Nov 2026, with its context: LF #4.41-1–#4.42-1, #4.48-3–#4.48-3.0.1, #4.54-0.1, #4.109, #4.122, #4.156–#4.156-1, #4.171–#4.171-2, #4.189-2, #4.563-3–#4.569, balaban_proofs/BP_COUPLING_PROFILES.md, and BP_LAYER_WIDTHS #4.18-2-1-2. Printed sources re-read in the corrected transcriptions: LFR II p.356 l.11–39, p.357 l.1–12, p.358 l.1–45, p.361 l.1–30, p.364 l.25–45, p.365 l.1–51, pp.366–368, p.369 l.1–30, and p.378 l.1–24; LFR I p.201 l.24–33.
- **Repairs made in this pre-check:**
  - *The weights of 𝐂_k (#4.157–#4.160-0.3-1).* #4.159-1 claimed that p.364 l.44's weight (g″)^{−2}(1 − ζ₀) = w_e is the sum of the two weights of p.364 l.36–45. Re-derived from p.365 l.19 and l.29–33: the sum is (g″)^{−2} off Z, where ζ₀ = 0, and g_k^{−2}(1 − ζ₀) on Z. That is (g_k(·))^{−2}(1 − ζ₀), which p.365 l.33 prints, and it equals w_e − w_Z with the new w_Z := ((g″)^{−2} − g_k^{−2})(1 − ζ₀)1_Z (#4.158). w_Z is nonzero in general, since at a point of the layer m of g″, (g″)^{−2} − g_k^{−2} = β_m(1 − φ_m) + Σ_{m<l≤k}β_l (#4.171). Changes:
    - #4.157 carries −A(w_Z, U_k);
    - new #4.159-1-1 gives the split A((g_k(·))^{−2}, U_k) = g_k^{−2}A(ζ₀, U_k) + A(w_e, U_k) − A(w_Z, U_k), the first term of (1.36)'s expansion being the action at U_k by gauge invariance;
    - #4.160 counts five actions;
    - new #4.160-0.2–#4.160-0.3-1 derive A(w_Z, ·)'s bounds. Z is a union of MR_k-cubes of the scale k, so ∂Z meets a block of the layer j in ≤ 2d faces, with ≤ 2(a_j/ε)³ sites within ε of each. The jump of 1_Z adds ≤ 48d²C₀^{ms}C_∇g_j^{−2}ε₁ρ̄(x) per block to the first-order term and ≤ 12d(C₀^{ms})²C_∇g_j^{−2}(ε/a_j)ε₁² to b_w, which are d² and 2d times #4.42's terms, so #4.42 holds with (1 + d²)C_w(ε₀);
    - #4.160-2's count goes from 11d to 13d (10 from the five actions, ½ from the form, 2 from φ_d), and #4.189-2's to 13d + 1.
  - *Check of #4.157 against the print.* 𝐂_k = LHS of (1.37) + A((g_k(·))^{−2}, U_k) + A((g″)^{−2}ζ₁, U″_{h+2}(exp ig_kB, V″)) + ½Σ_pη⁴ζ|DH″B|², with g_k^{−2}A(ζ₀, U_0) + I(U_0) = −log d + E_k(Λ) by (1.10). (1.37)'s second term is put into O(1) by p.366 l.12. Its ζ₁ term on U″_{k,Z} is localised in Z″_{h+2} (p.367 l.54–p.368 l.4), and (1.48) passes it to U″_{h+2}(exp ig_kB, V″), the configuration of (1.49). The signs agree with (1.49).
  - *ζ₀'s gradient.* #4.109 chose |∇ζ₀| ≤ C/a_k with an unnamed C, while C_∇ (#4.41-1-1) carries only ζ₁'s c_ζ; #4.153 and #4.160 used C_∇ or C for the weights with ζ₀. LFR I p.201 l.28–29 prints only ζ_i ∈ C₀^∞(X_i), changing from 0 to 1 in a neighbourhood of ∂X_i^{∼−2}. New BP_COUPLING_PROFILES #4.41-1-5–#4.41-1-5-1 constructs ζ₀ := 1_{S₀} ∗ ψ_{a_k/2}:
    - ζ₀ = 1 on Z^{∼−2} and ζ₀ = 0 beyond the ℓ∞-distance a_k from it;
    - abs(∇ζ₀) ≤ 2‖∇ψ‖₁/a_k = c_ζ/a_k;
    - supp ζ₀ ⊂ Z, since Z^{∼−1} lies at ℓ∞-distance ≥ MR_ka_k ≥ 2a_k from Z^c (#BC.2-2-1: cubes touch when they share a point).
    So #4.109 reads c_ζ for C, C_ζ := 2c_ζ(1 + L), #4.122's c_w := 4(d − 1)(1 + c_ζ)C₀^{ms}, and #4.153 and #4.160-0.2 cite #4.109. Re-derived: |∇w| ≤ c_ζ/a_k + c_ζ/a_h ≤ c_ζ(1 + L)/a_n by k ≥ n and h + 1 ≥ n, and 2(d − 1)(|∇F| + |∇ζ₀||F|) ≤ 4(d − 1)(1 + c_ζ)C₀^{ms}ε₁/a_j³. The BP file's header lost its status sentence.
  - *The class clause of #4.160-2.* The line claimed 13dC_hθ̃^n also on the class. There log d has #4.155-3's bound, |D(1)| ≤ φ_d plus 4e^{c(M)}C_d(M)C_hθ̃^n. The line now says so; it was split at its sentence boundary into new #4.160-2-1. #4.151-1 and #4.189-2 cite #4.160–#4.160-2-1, and #4.189-2 names #4.160-2-1's addition.
  - #4.569 (packet 17): "four actions" became "five actions". The Lemma (Two Constants) needs only A(w_Z, ·)'s real bounds and 0 ≤ w_Z ≤ (g″)^{−2} on the disc.
- **Re-derived without change:**
  - #4.152: d of p.356 l.19–20.
  - #4.155: |log∫e^{a+D} − log∫e^a| ≤ sup|D| for positive integrands.
  - #4.155-2: D(1) factors out of both integrals exactly.
  - #4.159-2 from (1.10): −log d = g_k^{−2}A(ζ₀, U_0) + I(U_0) − E_k(Λ).
  - #4.164: χ̄(f/t) has Lipschitz constant 1/(κ_st) in f and |∂_tχ̄(f/t)| ≤ (1 + κ_s)/(κ_st). Hence δ^χ_c ≤ 2(1 + κ_s)Cg_k²|δ_k|/κ_s ≤ 4Cg_k²|δ_k|/κ_s.
  - #4.155-1 and #4.169-0.1 against (1.11) and p.358 l.26.
  - #4.160-0.1 and #4.161–#4.163 against p.365 l.10–13 and p.378 l.10–22.
- **Definition check:** 0 conflicts (1 allowed: t^X, #D.t^X.2 of #4.163 against §2's #D.t^X, which the table marks as different objects). w_Z is new to the table, the Cauchy note, the step map, and LABELS.
- **Table:** the table fork entered w_Z in #T12.9 and (1 + d²)C_w(ε₀) in #T4.35 (table fa191df06f65), then C_ζ, c_w, and c_ζ's ζ₀ clause (197ee9e2d0ff). I checked each against the LF; LABELS 0b3bbed47643 has #4.159-1-1, #4.160-0.2, #4.160-0.3, #4.160-0.3-1, and #4.160-2-1. No row carries 13d, 13d + 1, #4.160-2-1's class addition, or #4.569's count. Messages: the first sent before 06:35, the second at 06:44; both replies verified.
- **Size:** reviewed blocks 4.43k (#4.151–#4.155-3) and 10.26k (#4.157–#4.169-3), 14.70k in all (plan estimate 13k; the growth is the new mathematics of w_Z). The longest line is 585. CR is 0, and there are no trailing spaces or duplicate tags.
- **Spec:** specs\spec_p50_r1.json (LF 56d172c27cf2, BP_COUPLING_PROFILES 46439c799825, BP_LAYER_WIDTHS f1eadb8c867a).
- **Order:** after 14b r2 (running), 12b-bp r2, 14a r3, and 14bp r3–r4.

Written 2026-11-09 06:46.

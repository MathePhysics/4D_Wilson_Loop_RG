# Bałaban Proof: The Action Bounds the Stopping-Scale Plaquettes

Bałaban proof: on the all-small-field term ℓ₀ at the stopping scale K′, the Wilson action of the background U_{K′}(V) bounds the plaquette energy of the stopping-scale field V, Σ_{p′}|V(∂p′) − 1|² ≤ 8N·A(U_{K′}(V)), and a bound on the action puts U_{K′}(V) in VAR's space at the matching parameter. Bałaban states no such bound; the closest is UV3 (69)–(71) (p.273), which needs the regularity (68) of the fine field and gives one averaged plaquette at a time. The derivation below uses CMP98's (50) at every level and the fact that in d = 4 the plaquette energy does not grow under averaging.

Used by the pair factorisation note (WILSON_IT1_PAIR_FACTORISATION_2026_11_05.md, #PF4.3-3). Cauchy, BR and the table are WILSON_IT1_CAUCHY_ESTIMATE_2026_10_27.md, balaban_proofs/BP_REG_DRESSED.md and CONSTANTS_AND_CONVENTIONS_WDELTA.md.

## Setting

- {#BPA.1} V is a stopping-scale field in the support of ρ_{ℓ₀} = χ_{K′}(T)exp(𝒜_{ℓ₀}) (Cauchy #C11a.10), so every test (2.17) of the step K′ passes (CRE p.257 l.36–40). U := U_{K′}(V) is the global minimiser of (2.12) for the determining set T^{(K′)} of ℓ₀ (CRE p.256), on T_η with η = L^{−K′} in step-K′ units, so M^{K′}U = V. d = 4.
  {#BPA.1-1} For 0 ≤ n ≤ K′ let U^{av}_n := M^nU, with M RG I's average (0.4) (Cauchy #C10.1.4) and M^{n+1} := M∘M^n (CMP98 (43)). So U^{av}_0 = U and U^{av}_{K′} = V.
  {#BPA.1-2} E^{av}_n := Σ_p|U^{av}_n(∂p) − 1|², the sum over the positively oriented plaquettes p of the level-n lattice of the torus, and σ^{av}_n := max_p|U^{av}_n(∂p) − 1|, with |·| CMP98 (19)'s operator norm in G ⊂ U(N) (#T6.23). So σ^{av}_n ≤ (E^{av}_n)^{1/2}.

## One Averaging Step

- {#BPA.2} *Lemma.* If σ^{av}_n < c₂′^{ch}, then (E^{av}_{n+1})^{1/2} ≤ (1 + C^{av}σ^{av}_n)(E^{av}_n)^{1/2}, with C^{av} := (2d(d − 1))^{1/2}L⁴C₀^{ch}, and C₀^{ch} and c₂′^{ch} BR's (#BR.6-1, #BR.6-3; #T4.56-0-2, #T4.56-1).
  {#BPA.2-1} *Proof.* Write a_p := |U^{av}_n(∂p) − 1|. For a level-(n + 1) plaquette p′ with corners y₀, y₁, y, y₂, let Δ(p′) be the union of the four blocks of its corners and α(p′) := max_{p⊂Δ(p′)}a_p ≤ σ^{av}_n. The second line of CMP98 (50) (p.025 l.49–56), which BR derives for (0.4) with the identity (48) (#BR.6-1–#BR.6-3), and which is local in Δ(p′), gives |U^{av}_{n+1}(∂p′) − 1| ≤ m(p′) + C₀^{ch}L⁴α(p′)², with m(p′) := Σ_{x∈B(y₀)}L^{−d}Σ_{p⊂(p′)_x}a_p and (p′)_x the translate of p′ by x − y₀, a square of L² plaquettes. It is applied with α₀ := α(p′) + δ and δ ↓ 0.
  {#BPA.2-2} Since the weights L^{−d} sum to 1 over B(y₀), the Cauchy–Schwarz inequality gives m(p′)² ≤ Σ_{x∈B(y₀)}L^{−d}(Σ_{p⊂(p′)_x}a_p)² ≤ L^{2−d}Σ_{x∈B(y₀)}Σ_{p⊂(p′)_x}a_p².
  {#BPA.2-3} Fix the plane (μ, ν) of p′. The blocks partition the fine lattice (Cauchy #C10.1.4-0-1), and p′ is fixed by its corner y₀ and the plane, so the pairs (p′, x) with x ∈ B(y₀) correspond to the fine points x. A plaquette p in the plane (μ, ν) lies in the square (p′)_x for exactly L² points x. So Σ_{p′}m(p′)² ≤ L^{4−d}Σ_pa_p², summed over each plane, and over all planes Σ_{p′}m(p′)² ≤ E^{av}_n in d = 4.
  {#BPA.2-4} A plaquette p lies in Δ(p′) only if the block of its first corner is one of the four corner blocks of p′, which leaves at most four p′ in each of the d(d − 1)/2 planes. So Σ_{p′}α(p′)² ≤ Σ_{p′}Σ_{p⊂Δ(p′)}a_p² ≤ 2d(d − 1)E^{av}_n, and Σ_{p′}α(p′)⁴ ≤ (σ^{av}_n)²·2d(d − 1)E^{av}_n.
  {#BPA.2-5} By the Minkowski inequality in ℓ² over p′, (E^{av}_{n+1})^{1/2} ≤ (Σ_{p′}m(p′)²)^{1/2} + C₀^{ch}L⁴(Σ_{p′}α(p′)⁴)^{1/2} ≤ (E^{av}_n)^{1/2} + C^{av}σ^{av}_n(E^{av}_n)^{1/2}.

## From the Fine Lattice to the Stopping Scale

- {#BPA.3} *The regularity of U.* If ε_{K′} ≤ c₂^{CMP98}, 2ε_{K′} ≤ a₁ and 2B₃ε_{K′} ≤ c₂^{CMP98}, then |U(∂p) − 1| < 2B₃ε_{K′}η² on T_η and σ^{av}_n < 4B₃ε_{K′}L^{2(n−K′)} for n ≤ K′, with a₁ and B₃ VAR's (#T3.31, #T3.32-2) and c₂^{CMP98} BR's (#BR.6-4, #T4.56-0-1).
  {#BPA.3-1} *Proof.* On a cube □ of (2.17) at the step K′, V = M^{K′}(U_{K′,□}) on the K′-plaquettes of □^∼, and the test bounds the plaquettes of U_{K′,□} in □^∼ by ε_{K′}η². So Proposition 2 of CMP98 for (0.4) (#BR.6-4), local in the four blocks of the corners, gives |V(∂p′) − 1| < 2ε_{K′}, as at BP_LFR2_CHI_K_LAMBDA #3.84-1.1–#3.84-1.1-1 with κ_s = 0. Every K′-plaquette p′ has its corner blocks in □^∼ for the cube □ of its first corner.
  {#BPA.3-2} For the determining set T^{(K′)}, the data plaquettes of VAR (7) are the V(∂p′) (VAR p.278 l.39–40). So VAR Theorem 1 with ε₁ = 2ε_{K′} (p.279 l.8–15) puts U in VAR (2) with ε₀ = 2B₃ε_{K′}, |U(∂p) − 1| < 2B₃ε_{K′}η² on T_η, as at Cauchy #C11b.2-6.
  {#BPA.3-3} CMP98 (53) for (0.4) (#BR.6-4) with α₀ = 2B₃ε_{K′} ≤ c₂^{CMP98} bounds the plaquettes of U^{av}_n by α₀L^{2n}η² + 2C₀^{ch}(α₀L^{2n}η²)² < 2α₀L^{2(n−K′)}, since α₀L^{2n}η² ≤ α₀ and C₀^{ch}α₀ ≤ 1/3.
- {#BPA.4} *Energy.* Under #BPA.3 and 2C^{av}B₃ε_{K′} ≤ log 2, E^{av}_{K′} ≤ 4E^{av}_0.
  {#BPA.4-1} *Proof.* By #BPA.3, σ^{av}_n < 4B₃ε_{K′}L^{−2} ≤ 2c₂^{CMP98} ≤ c₂′^{ch} for n < K′, so #BPA.2 applies at each of these levels, and Σ_{n<K′}C^{av}σ^{av}_n ≤ 4C^{av}B₃ε_{K′}Σ_{i≥1}L^{−2i} ≤ 2C^{av}B₃ε_{K′}, as L ≥ 2. So (E^{av}_{K′})^{1/2} ≤ exp(2C^{av}B₃ε_{K′})(E^{av}_0)^{1/2} ≤ 2(E^{av}_0)^{1/2}.
- {#BPA.5} *The action.* E^{av}_0 ≤ 2N·A(U), A = A^η of VAR (5) (p.278 l.25), which in d = 4 is Σ_p[1 − Re tr U(∂p)] over the plaquettes of T_η. Indeed |X| ≤ √N‖X‖ (CMP98 (20), p.021 l.23) and ‖U(∂p) − 1‖² = 2[1 − Re tr U(∂p)] with the normalised trace (CMP98 (17); Cauchy #C11b.2-7).

## The Plaquettes and the Regularity at a Given Action

- {#BPA.6} *Proposition.* Under #BPA.4, Σ_{p′}|V(∂p′) − 1|² ≤ 8N·A(U), the sum over the plaquettes of T^{(K′)}. If moreover A(U) ≤ Tg_{K′}² for a T > 0, then every plaquette of V is within 2(2NT)^{1/2}g_{K′} of 1; and if ε^{act} := 3(2NT)^{1/2}g_{K′} ≤ min(a₁, 2ε_{K′}) and 2B₃ε_{K′} ≤ a₀ (VAR's a₀, #T3.32-2), then |U(∂p) − 1| < B₃ε^{act}η² on T_η.
  {#BPA.6-1} *Proof.* The first claim is #BPA.4 with #BPA.5, as Σ_{p′}|V(∂p′) − 1|² = E^{av}_{K′}; the second follows, a single term being at most the sum.
  {#BPA.6-2} For the third, VAR (7) holds with ε₁ = ε^{act} ≤ a₁, so VAR Theorem 1 gives a minimal orbit in VAR (2) with ε₀ = B₃ε^{act}. It is the unique critical orbit in the space (6) with ε₀ = 2B₃ε_{K′} ≤ a₀, since B₃ε^{act} ≤ 2B₃ε_{K′} (p.279 l.15), and U lies in that space by #BPA.3, so U is on it.

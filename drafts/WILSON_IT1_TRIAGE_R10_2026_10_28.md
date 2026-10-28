# Triage R10 (2026-10-28, from 13:53)

Reviews launched about 13:45: cauchy-loclift-20261028-r1, var-20261028-r5, cauchy-pair-20261028-r1.

## Closed in this round (unreviewed)

- **LF note l.158, p.378 l.10 at the soft thresholds.** Derived by CRE (3.6)–(3.8) with U_{k,Z} as the background: CRE (3.20) gives Λ_k ⊂ Ω_k^{∼−2}, so each plaquette of Ω_k^c ∩ X_i is ≥ 2MR_k from Z^c; the cube □ ∋ p passes the soft test (χ_k(Ω_k^{∼4}) or the p.378 decomposition); □^{∼4} ⊂ Z^{∼−2} by M ≫ M₂ (CRE p.245); U_{k,Z} is the □^{∼4}-minimiser at its own data; B = 0 off the 2M₁ layer, |B| < 11d²α₀ on it (REG (1.65)); VAR (190) gives τ; REG (1.43) solved for X gives |U_{k,Z}(∂p) − 1| < 2ε_kη² for κ_s ≤ 1/4, τ ≤ 1/20.

## cauchy-loclift-20261028-r1 (Cauchy §9.8): applied

- S (B2), CRE's 𝐁_1(X^∼) rejected wrongly: accepted, checked at CRE p.246 (1.2)–(1.3). §9.8 now defines ι_XU := U(𝐁_1(X^∼), M^·(Q_1^{s*}U)), Q_1^{s*} an exact right inverse; Mι_XU = U on all coarse bonds of X^∼ by VAR p.277 l.18 (bonds with an endpoint in Ω₁ are constrained).
- S (C3), accuracy of R at the scale a: accepted. The collar mismatch in the block-axial gauge of ιU^A_k is ≤ LC_LC_F(ε/a)ε₁/a per fine bond.
- S (C4, D3), tail units and gradient: accepted and closed. The tail is derived, not assumed: ιU^A_k is the X^∼-minimiser at its own data (as CRE (3.6)), T := ℋ(B), VAR (190) along tB as CRE (3.7): |T| ≤ C_ι(ε/a)(ε₁/a)e^{−δ₀dist/ε}, |∇T| ≤ C_ι(ε/a)(ε₁/(aε))e^{…}. No weighted contraction is needed, since (190) is the decay of the nonlinear map's derivative. Linearised at 1 it gives C″_Π of the moment.
- δ₀ redefined in the Constants: the smaller of PBG's rate and 1/16 of VAR (190)'s.
- Minors applied: CRE p.259 (i) has X; collar RM₁ε/L rounded to M₁ε-blocks; scales with L^j ≤ R/L + 2 through e^{δ₀(R/L+2)M₁}; conclusion on X and within 2L fine spacings; the ρ-source remark dropped; E1 collar covariance (ṽ_b); E3 cited as RG I (1.19), p.263 l.34–37, CRE p.259 (iii); the unchecked V4 pointer dropped.
- Callers updated: Cauchy l.15–16, l.29 (four open items), l.170, l.177, l.192, l.196, l.200, l.204, l.208, l.213, l.235, l.237–238, l.875, l.878; LF Open Gaps (3) second bullet (the tail at the multiscale chain stays open), l.381, l.433; walk-factor l.12.

## var-20261028-r5 (LF §4(d) (i)–(iv), room): accepted, repairs applied (unreviewed)

- S1, completions at U_k: accepted. Applied: the completions read the entry ι_YU^A_k, so their r_z at U_k is part of the open r_z item (LF body and Open Gaps (3)); "is the Cauchy note's variation group itself" deleted.
- S2, U_1, U_2 (supported on Ω″^∼_{h+1} and its complement, LFR II p.370 l.22–25, quote checked): accepted. Applied: their entries, ι_Y of them, ι(Mc^B) = c^B, and the patch U_{1,2} are not defined by the link maps; the lift–patch commutator at U_{1,2} near the cut is named. The open item of the body is renamed "(i), r_z, and the lift–patch commutator at U_{1,2} near the cut, and (i) at the decoupled configurations", and the Open Gaps (3) sub-bullet with it.
- S3, r_z closure option (b): accepted. Applied in the body ((a) and (b) as sub-bullets; without the z-sum across the Y or a per-Y bound of the weight-change part (b) doesn't work) and in Open Gaps (3).
- S4, the rate of (iv) and (α): accepted, then closed (derived, unreviewed). θ̃ gains the term L^{−θ_V/8} (Cauchy §8.7 and Constants); every use of θ̃ in the Cauchy and LF notes is a lower bound or θ̃ < 1 (grep of both notes and the walk-factor note), so only constants change, uniformly in K and in γ small. New LF bullet *The rate of (iv) and (α) in the layer*: per point at the layers ≥ n, the configuration part decays as L^{−θ_V(1−25ε₀)n/3} (fine side of (ii) as in *At real points the ratio is small.*, r_{0,m} ≥ ε_m), ≤ θ̃^nL^{−5θ_V(1−40ε₀)n/24}; the moment part, split at j = m/2, as L^{−β′n/4} plus a super-exponential term; so |(iv)| ≤ C_{iv}θ̃^n, the (LF-2) form, C_{iv} polynomial in j(C). The fine-side and tail sub-bullets of Open Gaps (3) now state the size the rate needs (ρ_k and the tail at most the size of σ_c).
- Minors applied: M1 𝔰 := 8σ_c′^{15/16} (the two Two-Constants bounds added and doubled for the commutator) and 8 in *The Ratio.*; M2 (W-δ) per walk term, B₀′; M3 C_Π(j) j-dependent, O(k)E₀ (body and Open Gaps); M4 the near domains at the boundaries of minimisation domains as their own Open Gaps (3) item; M5 RG II p.5 l.6–7 gives the domain only, and LFR I (1.16) (p.180 l.19–26, read) for the layer j, the cascade test (1.24) marked as a test; M6 the §4(d) header and the Status exclude point (7), Open Gaps (7) adds the analyticity of D and 𝐀₀ in the operators; M7 the field A among the shared variables, the counterterm of z; M8 the device renamed; item 10 the nesting Y = Y_4 ⊇ Y_1 ⊇ X ⊇ Y_0 ⊇ □₀; item 13 the telescoping order and (β)'s fixed-point part; item 25 the lift condition at the composites "open".

## cauchy-pair-20261028-r1

- Landed about 14:03; read in full (l.1–274) by 14:10. Repairs applied 14:10–14:22.
- S1, Euclidean covariance of G: accepted as a finding (CRE p.260 l.2–4 checked: covariance "only" for the unrestricted X-sum at one configuration). Closed without covariance (derived, unreviewed). CRE pp.281–282 checked: (3.49)–(3.56) use only the Ward identity per X; (2.29) enters only at (3.58)–(3.61), to reduce the summed tensor Π_{μν,κλ} to Π_{22,11}. Repair:
  - §3 *The plane-resolved moment.* (new): plane-pair actions A_{PP′}(h_z, U) := ½Σε⁴h_z Re tr Φ_PΦ_{P′} (log-plaquettes based at one corner, gauge invariant); N_j := Σ(Π^G_{μν,κλ} − Π^G_{22,11}δδ)A_{(κμ)(λν)}; irr(Δ_j) and irr^G subtract N_j; telescoping unchanged.
  - §5 *The moment of the lifted term.*: the affine-field argument gives the whole tensor of the global-lift term, Π^{B∘ι}_{μν,κλ} = Π^{B,(j+1)}_{μν,κλ}, isotropic by (3.60)–(3.61) for run B's own sum; the current slot vanishes at affine fields; the boundary bound C_Π(j)E₀e^{−δ₀M₁L^j} holds per component (polarisation in C′_Π), so N_j's coefficients are ≤ 2C_Π(j)E₀e^{…}.
  - (5.1) and (5.1c) subtract N (N_j for the frozen difference, 0 for covariant families); Δ_j's tensor is Π^G − β^A_jδδ, run A isotropic, so its marginal part is removed in full. Evidence paragraph: (3.66) for each A_{PP′} with the elementary tensor, computed at affine fields.
  - Moment defect: (Π^G_{22,11} − β^B)A + N_j(U^A_k) ≤ 2496C_XC₀²E₀C_Π(j)ε₁²e^{…} (each A_{PP′} ≤ 32C₀²ε₁²L^{4(j−k)}, 36 coefficients); 192 → 2496 in the second bound, E_V (twice), and LF l.385.
  - The Open item added at 14:05 was replaced by a "Derived, unreviewed" item; the Status line is back to four open items.
- Minor 1 (C(ε₀, δ₀M₁) must cover the sup tail): resolved by the new §9.8 consequences, C(ε₀)e^{−2y} ≤ C(ε₀, δ₀M₁)e^{−y}.
- Minor 2 (q₀ > p₀ + r under (T-Λ)): applied in *The lift condition.*'s current bullet. CRE p.259 l.50 asks only that q₀ be an integer > 1; grep of CRE, LFR I, and LFR II found no upper bound on q₀.
- Minor 3 (decay of dι_X − dι at 1): resolved, §9.8 *The linearisation at 1*.
- Minor 4: (3.1) now carries Σirr(Δ_j)(U^A_k).
- Minor 5: one line on the complex room of C_{Q*} added (transports and the four operators within exp(O((2d+1)Ls_{1,j}L^{−j})) of real values).
- Minor 6: §3 "(Exact)" kept, since §9.8 now defines ι_X; l.122 now says that run A's part at complex points rests on the unchecked reduced-thresholds reading.
- Minor 7: convention-free bound 4ε/a_j (ℓ¹-Lipschitz tent, 4-cell ℓ¹-diameter 4ε); 384 → 768 in C_A′ (bullet, Constants) and LF l.385. CRE's A(φ, U) definition is not on the transcribed pages near (2.23).
- Minor 8: β̄ ≤ b′ + C by ONE_LOOP_PROOFS (W) at n = m + 1 (l.85–86), established by its Corollary 8.2 (l.734) for simple G; RG I p.264 l.32 noted as per-j only.
- Minor 9: "the gauge group is compact and simple" stated at the Ad-invariance step.
- Minor 10: λ := 16B₃²C_{Q*} renamed λ_Q (Cauchy l.122, Constants; LF l.434, l.448); polydisc radii a → s in *Complex domain*.

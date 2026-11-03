# Triage of lf-k0-20261103-r43 (LF c460bb3394e3 → 360a739b3955 → 0b23b1cfe8c8 → e6494bdbe0a5), 3 Nov 2026

Review: verification\isolated_reviewer\reviews\lf-k0-20261103-r43\review.md. Verdict: not established as written; no fatal; one serious (S1); five minor (n1–n5); r42's m1–m7 closed. Not a clean pass. Each finding was checked against the text and the cited sources before repair. All repairs are derived, not reviewed. No line was added or removed.

The queued renames of the r41 triage file (C_H meanings (2)–(5) as C_{Δ𝐇}, C_{V′}, C_{HD}, C_{Hδ}; the weight rates δ_w of §4.236 and §4.284 as κ_b and κ_w) were applied first (rename_ch.py): LF c460bb3394e3 → 360a739b3955, labels 47ba86dfb92f → bc7d395f9c3e, walk-factor note c9a09f9bc56f → ea53b821152a. l.6's C_H is unchanged; l.871 names it.

## Serious (repaired)

- **S1, uniformity in j at the interfaces j ≥ 2.** Confirmed against the text: (g)(1) set V_N := Q_jA_N on all scale-j bonds and applied the single-scale H_j, G, Δ_j, H^Λ_j, N_𝔫, and ♯ to it. A field θ in the units of Λ_{j″} is L^{j−j″}θ in those of L^j, and the Euclidean distance from Ω_j to Λ_{j″} is < RM/(L − 1) in the units of L^j, so the kernels give a fixed e^{−cRM}. S1(b) also holds as stated: ρ grows by about L^{j−j″} per unit length across Λ_{j″}, so the commutators of the scale-j kernels with e^{±δρ} are not O(δ) for pairs of Ω_{j+1} separated by finer layers.
- **Repair: the split at the start of (g).**
  - In the free case A_N = H₀B − ∂ω_H, with H₀B PBG's HB of (3.109)–(3.110) (p.417) at the flat base. Δ = D*D there (PBG (3.10)). Every element of 𝒞 is carried to RD*a = 0 by a gauge of N(Q′) (PBG (3.119)), and the minimisers differ by ∂N(Q′) ((K0)(a)). So A_N is linear in B.
  - B^{(j)} keeps the data of the layers ≥ j − 1. A_N^{(j)} is the A_N of B^{(j)}, and ω^f_j := ω_H(B − B^{(j)}).
  - (s1) PBG (3.133) (p.422) with the normalisation of p.422 l.32–33. The constants are of d and L, independent of the domains (Theorem 3.1, p.397; p.399 l.2). PRT2's distance (2.46) (p.231), with its passages > RM (2.57) and the sum (2.58)–(2.59), gives:
    - H₀(B − B^{(j)}) ≤ C(L)e^{−δ₁RM/4}θ_B on Ω_j;
    - H₀B^{(j)} ≤ C(L)θ_Be^{−(j−2−j″)} on Λ_{j″} in the units of L^j, with its curvature at every scale ≤ C(L)θ_B.
  - (s2) The gauge part: l.1007's bound for ω₀ with f = H₀B, and (f)'s scalar Combes–Thomas bound on the full N(Q′).
  - (s3) Q_jA_N^{(j)} ≤ C(L)θ_B on Ω_j^c in the units of L^j, uniformly in j.
  - (1)–(6) are run for A_N^{(j)}. The far part enters ω_♮ through χ_jω^f_j, so A_♮ gains χ_jH₀(B − B^{(j)}) ≤ C(L)e^{−δ₁RM/4}θ_B. In (f), the far part is ≤ C(L)(e^{−δ₁RM/4} + e^{−δRM/32})L^{d/2}θ_B on the regions of ℳ.
  - Self-check before r44 (LF 0b23b1cfe8c8 → e6494bdbe0a5, labels e942e181c109 → 7687a1afb67d):
    - H₀B is identified with VAR's H₀B of (129) (p.297). VAR minimises ½⟨A′, Δ_aA′⟩ under the first equations of its (126) only. At the flat base ΔD = 0, so Δ_π = Δ in PBG (3.119)–(3.120), PBG's G of (3.126) is Δ_a^{−1}, and PBG (3.124) gives RD*GQ* = 0. VAR bounds it by PBG (3.133); VAR's [5] is PBG (p.309).
    - (s1) now states that PBG's regularity condition (3.35) (p.396) holds at the flat base for every α₀.
  - PBG p.397 cites the distance as "(2.36) in [4]". In PRT2 the distance is (2.46) (p.231), and (2.36) is the partition of unity (p.229). The LF cites (2.46).
- **Repair of S1(b): the capped metric.** ρ_j is the distance of ds = dx/max(ℓ_ms, 1) in the units of L^j:
  - it equals ρ on paths in Ω_j and is 1-Lipschitz everywhere;
  - ρ_j(x, Ω_j^c) ≥ min(dist(x, Ω_j^c), RM) on Λ_j;
  - it is used in (2), (iv), and (v).
  - The pair classification of (2) is now by distance: below min(RM, ML)/2, the same or touching cubes of Ω_{j+1}^{(j+1)}; above it, far pairs with L²e^{−δ₀min(RM, ML)/8} ≤ c(d)δ².
  - The blocks of Ω_j^c enter (v) at ρ_j ≥ RM/2 with the bound of (s3).

## Minor (repaired)

- **n1.** (v)'s display now carries (1 + r₂/L)^d(1 + m/RM), with m := max(r₂/(2L), ρ_j(x, y″)).
- **n2.** Packet text: the claim's parenthesis in r44 lists L²e^{−δ₀min(RM, ML)/8} ≤ c(d)δ² with M ≥ M₀(L), and (1) now reads "which RM chosen after L and M ≥ M₀(L) absorb".
- **n3.**
  - The Im bound now goes through the data. Im ηω_♮ is ω_♮ for Im B.
  - Im B = L^{j′}ηQ_{j′} Im u_R − D̄Q′_{j′} Im ηω on Λ_{j′}, bounded by the bounds used and derived at l.1007 (not l.6).
  - The real kernels are those of the free case, which is (K0)'s scope.
- **n4.** "Ω_j^c, whose points next to Ω_j lie in Λ_{j−1}".
- **n5.** "Q_{48L} of (KW), of Euclidean radius 48√dL", and "≥ 48√dL".

## Next

r44 on (K0), prior review r43. If r44 is clean, it is the first clean pass after S1's repair; a second is needed.

# Packet 14bp (balaban_proofs/BP_CMP98_ADJOINT_AVERAGING.md), round 2, 9 Nov 2026

## Pre-check of bp-p14bp-20261109-r2 (full)

- **Whole part read** (#C10.3.21–#C10.3.24-4) on 9 Nov 2026, with its context: Cauchy #C3.2-1, #C9.8.1–#C9.8.1-2, #C10.1.4–#C10.1.4-0-3, #C10.3.3, #C10.3.17–#C10.3.20, and #C10.3.25–#C10.3.28.
- **Earlier repairs:** r1's M1–M6 are in the text (WILSON_IT1_LF_TRIAGE_P14BP_R1_2026_11_09.md).
- **Re-derived:**
  - #C10.3.21: Ā_c = L^{−(d+1)}Σ_xA(γ̄_{c,x}) has weight L^{−(d+1)}|𝐆(c₋, x)|^{−2} per pair (Γ, Γ′), since |𝐆(c₊, x′)| = |𝐆(c₋, x)|. The adjoint for η^dΣ_b and (Lη)^dΣ_c multiplies this by L^d, which gives L^{−1}|𝐆(c₋, x)|^{−2}.
  - #C10.3.21-5: dW(c)W(c)^{−1} is η times a transported sum over the L fine bonds of c, and the coarse field is divided by Lη. So the weight is L^d·L^{−1} = L^{d−1}, and a fine bond lies on at most one coarse bond.
  - #C10.3.21-6: |n|₁ ≤ dL/2 gives Σ_{α<β}|n_α||n_β| ≤ (d − 1)dL²/8, and L(|n|₁ − |n_μ|) ≤ (d − 1)L²/2. The sum is (d − 1)(d + 4)L²/8: 4.5L² at d = 5 and 6.25L² > 6L² at d = 6, so the restriction d ≤ 5 is needed and suffices.
  - #C10.3.21-7: c_{av} ≥ 4d gives dL²κ_W ≤ 1/32, and c_{av} ≥ 1/(8ρ_𝔤) with L ≥ 3 gives κ_W ≤ ρ_𝔤/L² < ρ_𝔤.
  - #C10.3.21-7-1 and -7-2: the path stays within 1/16 of 1, the principal logarithm along it has norm ≤ 1/8, and |ad X| ≤ 1/4 < 2π, so exp restricted to 𝔤 is a local diffeomorphism there. The set where the logarithm lies in i𝔤 is open and closed and contains 1.
  - #C10.3.21-8:
    - The dexp bound is (e^a − 1 − a)/a. At a = 1/8 this is 0.0652 = 0.52a, so 0.53a holds on a ≤ 1/8.
    - For dexp_{Y_c}, a ≤ 4dL²κ_W ≤ 1/8.
    - The inverse is within 0.53a/(1 − 0.53a) ≤ 2.12dL²κ_W/0.934 ≤ 2.27dL²κ_W ≤ 2.4dL²κ_W.
    - dexp_Z* = dexp_{−Z}, dlog_h* = (dexp_{−log h})^{−1}, and Ad(g)* = Ad(g^{−1}) carry the same bounds in any norm with |[Z, X]| ≤ 2|Z||X|, so no duality of norms enters.
  - #C10.3.22: a fine bond b on [x, x′] determines L points x, and each x determines its block and coarse bond. The total weight is L·L^{−1} = 1.
  - #C10.3.23-2 to -4:
    - Leaving bonds: summing over the last contours gives L^{−1}|𝐆(y, x̂)|^{−1}. Entering bonds: summing over the first contours gives the same weight, by |𝐆(c₊, x′)| = |𝐆(c₋, x)|.
    - With ⟨ν, Dω⟩ = (Lη)^dΣ_c and D_{W̄}ω(c) = (Lη)^{−1}(Ad(W̄(c))ω(c₊) − ω(c₋)), D*_{W̄}ν(y) = (Lη)^{−1}(Σ_{c₊=y}Ad(W̄(c))^{−1}ν(c) − Σ_{c₋=y}ν(c)). So the leaving and entering terms sum to −LηD*_{W̄}ν(y).
    - e^{iω(c₋)}W̄e^{−iω(c₊)} = e^{−iLηD_{W̄}ω}W̄ to first order.
  - #C10.3.24-1:
    - The −Γ′ terms carry three operators (dexp, dlog, Ad(h)), and the entering terms also the replacement Ad(W(c))^{−1} → Ad(W̄(c))^{−1}, of cost |Ad(e^{iY_c})^{−1} − 1| ≤ x.
    - (1 + x)³ − 1 + x ≤ 4x + 3x/8 + x/64 ≤ 5x.
    - The path weight is ≤ 1 + 2dN_bL^{−1} ≤ 1 + 2dL^{d−1}.
  - #C10.3.24-2: the weights of #C10.3.21-4 sum to 1, so its operator is (Ad(e^{iY_c}) − 1) − (average of dexp∘dlog∘Ad(h) − 1), of norm ≤ x + ((1 + x)³ − 1) ≤ x + 3.4x ≤ 5x.
  - #C10.3.24-3: 5x(1 + 2dL^{d−1}) + 5xL^{d−1} ≤ 5xL^{d−1}(2d + 2) = 10(d + 1)xL^{d−1}.
  - #C10.3.24-4:
    - x ≤ 4c_{av}C₀ε₁L^{2(i+1−n)} ≤ 4c_{av}C₀ε₁ for i < n.
    - (AQ) #C10.3.26, 8c_QL^{d−1}C₀ε₁ ≤ 1 with c_Q = 10(d + 1)c_{av}, gives 4c_{av}C₀ε₁ ≤ 1/(20(d + 1)L^{d−1}) ≤ 1/8.
- **Repair made in this pre-check:** #C10.3.21-8-1 announced "three groups of path terms" before a list with two path items. It now reads "the path terms, on the straight segments [x, x′] and on the contours Γ and −Γ′, and the term of #C10.3.21-4". This is a rewording, with no change to the mathematics.
- **Citations:**
  - RG I (0.3) and (0.4) and the families of p.252 l.27–32 enter through #C10.1.4–#C10.1.4-0-3; (0.4) was re-read on p.253 today.
  - The plaquette-move count #MOSTC.8–#MOSTC.12 is permitted background.
  - c_B and r_B do not occur in this part.
- **Definition check (build of 06:17):** 0 conflicts (8 allowed). r1's x, A_L, and N_b, plus five new entries. D_{W̄}ω(c), c_{av}, and ρ_𝔤 are defined only in this file; the check's second hit is the file itself. Q := Ad(q)P (#C10.3.21-7-1) and a := |ad Z| (#C10.3.21-8) are local letters.
- **Spec:** the claim now names c_{av} := max(4d, 1/(8ρ_𝔤)), the logarithm in 𝔤, the adjoints, and (a)'s hypothesis. allow_defs (x, A_L, N_b) are as in r1.
- **Size:** BP file 8.09k characters with header. The longest line is under 600, CR is 0, and there are no trailing spaces or duplicate tags.
- **SHAs:** BP 4b28500bb832, Cauchy 00e33ad08351 (after packet 14b's pre-check repairs and 14a r2's repairs; of this packet's context only #C10.1.4-0-3 changed, by the added pin to RG I p.253 l.42), LF b142ee965e51, table 4f338b69054c, labels 4796ce6479b5.
- **Order:** launch after 14a r2 reports (one referee at a time).

Written 2026-11-09 05:59.

## Verdict of bp-p14bp-20261109-r2

- No fatal and no serious finding; four minor findings, m1–m4. The round is not clean. The referee verified the derivation of (ii), the move count, the logarithm in 𝔤 for disconnected G, and the arithmetic, and found no change to any constant or bound.
- I re-derived all four findings and agree with them.
  - **m1.** If n_μ > 0 and μ is the last direction of Γ′, then Γ′'s last n_μ bonds run in +μ to x′ = x + Le_μ, with the other coordinates already those of x. So they lie on [x, x′], with the opposite sign to the straight segment, since −Γ′ is reversed.
  - **m2.** With dexp_Z := Σ(ad iZ)^n/(n + 1)!, the derivative of Z ↦ e^{iZ}, and log h = iP, the logarithm's derivative is the inverse of dexp_P = dexp_{(1/i)log h}.
  - **m3.** −LηD*_{W̄}ν(y) is the adjoint for the site pairing (Lη)^dΣ_y, which neither the BP file nor Cauchy #C10.3.1-5 stated.
  - **m4.** The column of b carries the adjoint T* of the operator T of #C10.3.21-4. Since (dexp∘avg)* = avg*∘dexp*, T* = Ad(e^{−iY_c}) − (avg of Ad(h^{−1})dlog_h*)∘dexp_{Y_c}*. #C10.3.21-8-1 bounds each adjoint factor, and the weights sum to 1, so |T*| ≤ x + ((1 + x)³ − 1) ≤ 5x.

## Repairs

| Finding | Line | Repair |
|---|---|---|
| m1 | #C10.3.21 | "b may occur twice, with opposite signs, when μ is the last direction of the contour: on Γ and on [x, x′] when n_μ < 0, and on −Γ′ and on [x, x′] when n_μ > 0". |
| m2 | #C10.3.21-8 | "dlog_h is the inverse of dexp_{(1/i)log h}". |
| m3 | #C10.3.23-4 | "the adjoint for the site pairing ⟨ω, φ⟩ = (Lη)^dΣ_y". |
| m3, Cauchy | #C10.3.1-5 (packet 14b) | "The inner products on a lattice of spacing η are Σ_bη^d⟨·, ·⟩ on the bonds and Σ_xη^d⟨·, ·⟩ on the sites". This is the pairing that (i) and #C10.3.4-1's R* = (a_j/η)^d1 use. |
| m4 | #C10.3.24-2 | The line now bounds the adjoint, Ad(e^{−iY_c}) minus the average of Ad(h^{−1})dlog_h* with the weights of #C10.3.21-4, composed with dexp_{Y_c}*, by #C10.3.21-8-1. |

- I first wrote the m4 adjoint as dexp*∘avg* and corrected it to avg*∘dexp* before hashing.
- Hygiene: CR is 0, there are no trailing spaces or duplicate tags, and no line is over 600 characters.
- **Repaired SHAs:** BP f03186fe900e, Cauchy 3802c8fb4ced.
- **Next round:** 14bp r3, narrow (the changed lines #C10.3.21, #C10.3.21-8, #C10.3.23-4, and #C10.3.24-2, with the rest as context), then r4 full. Order: 14b r2, 12b-bp r2, 14a r3, then 14bp r3.

Written 2026-11-09 06:27.

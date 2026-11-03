# JB Draft: CRE (2.36) for the Real Base Current J_k (Target: Note l.173, *The real base points*)

Status: draft, premises being checked. Not in the note until TB8 is back; review only after TB9.

## Claim

On the support of the R-step's indicators, at every real base point U_k, the current J_k = D^{ξ*}_{U_k}ξ^{−2}π Im ∂U_k satisfies (L^nξ)³|J_k| < (1−β)α_{0,n} on each layer n, for g small, uniformly in n and K.

## Steps

1. **Units.** VAR's space 𝔘_k({Ω_j}, ε₀) bounds |D*_U∂U| < ε₀η²(L^jη)^{−3} on Ω_j (VAR (2), p.278 l.2–8). R(U) commutes with π Im, so |J| ≤ ξ^{−2}|D*_U∂U| < ε₀(L^jξ)^{−3} at η = ξ.
2. **Localisation to a cube.** On a cube □ of layer j, U_k^{(n)} = (e^{−iξ𝐇_{j,□}}·U_{j,□}^{u_{j,□}}), from LFR I (1.?) at p.183 l.42.
   - U_{j,□}(V_j) = U(𝐁_j(□^{∼4}), M(Q_j^{s*}V_j)) (CRE p.257 l.29–31).
   - 𝐇_{j,□} and its derivatives are below (β/10)ε_j (LFR I p.184 l.4).
   - The current is gauge covariant, so |J(U_k^{(n)})| ≤ |J(U_{j,□})| + (terms of D*D of ξ𝐇, and products), all O(ε_j)(L^jξ)^{−3}. CHECK the units of 𝐇's derivative bounds (which powers of L^jξ).
3. **The cube minimiser's current.** VAR Theorem 1 (p.279 l.8–12), applied to the single-scale set 𝐁_j(□^{∼4}) (CRE takes VAR for every determining set, p.256 l.48–53), with data M(Q_j^{s*}V_j). It puts U_{j,□} in 𝔘(B₃ε₁) once the data meet (7) at ε₁.
   - CHECK (7) for M(Q_j^{s*}V_j) at ε₁ = Cε_j from χ_j's condition sup|U_{j,□}(V_j, ∂p) − 1| < ε_jη² (CRE p.257 l.39, in that step's units). VAR p.278 l.47 gives (7) with ε₁ = O(ε₀) only for the non-empty 𝔘, which needs the current, so it is circular. A direct route is the plaquette curvature of the averages of U_{j,□} via M = averages of the minimiser itself (constraint), with block plaquette ≈ L^{2j}·(fine curvature), Proposition 2 of [4] in VAR's references. CHECK which paper.
4. **Comparison with the room.** (L^jξ)³|J_k| ≤ (B₃C + C′)ε_j < (1−β)α_{0,j} for g small, since ε_j/α_{0,j} = (A₀/α₀)(log g_j^{−2})^{p₀−q₀} ≤ (A₀/α₀)(log ḡ^{−2})^{p₀−q₀} → 0, uniformly in j and K (CRE (2.4); α_{0,j} from (2.28)). CHECK q₀ > p₀ in CRE (2.28) (memory: (R-m′) q > p₀ accepted provisionally).
5. **Which layers.** The indicators χ_j on Ω_j (CRE p.257 l.39; LFR I (1.3)–(1.4) for the last N steps, on Z) cover every layer of the support. CHECK the older layers j < h = k − N in LFR's representation (T_h(Z_h)). CHECK the components excluded from Z.

## Found 13:34: Per-Region Curvature of the Configuration Itself

- LFR I (1.24) (p.182 l.1–15) is a characteristic function in Bałaban's scheme. It bounds |U^{(n)}_{k,Z}(∂p) − 1| region by region:
  - on Ω_{j−1}∖Ω_{j+1}: c(1−β/2)ε_j(L^{k−j}η)²;
  - on an older layer Ω_m∖Ω_{m+1}: (1−β/2)L₀^{2(j−m−1)}ε_j(L^{k−j}η)²;
  - on the Z″ shells: the ε_{k₀+i} levels.
- LFR I p.183 l.36–42 uses it on □^{∼4} ⊂ Ω_{j−1}∖Ω_{j+1}, with M^j(U_k^{(n)}) = V_j, to get (1.30)–(1.31). This replaces P1 (the curvature of the configuration itself) by a printed indicator on its support.
- In layer-m scaling the old-layer bound is ε_j(L₀/L)^{2(j−m)}L₀^{−2}·L^{−2m}. With g_j ≤ (1+β₀)(j−m)^{1/2}g_m (CRE (2.6), first line), ε_j(L₀/L)^{2(j−m)}/α_{0,m} ≤ C(1+β₀)(j−m)^{1/2}(L₀/L)^{2(j−m)}(log)^{p₀−q₀} → 0. L₀: "2 ≤ L₀ < ½L" (p.182 l.18), so (L₀/L)^{2(j−m)} ≤ 4^{−(j−m)}. CHECKED.
- (1.24) is the indicator χ_k^{(n)} of LFR I's inductive representation (p.181 l.48 to p.182 l.15), for U^{(n)}_{k,Z} = U(𝔹_k^{(n)}(Z), (M(Q_k^{s*}V_k)⌈_{Z∩Ω_k}, V⌈_{Z∩Ω_k^c})) (p.180 l.57). CHECKED.
- U_k^{(n)} = U(𝔹_k^{(n)}, V) are "background fields in the successive integrations" (p.180 l.41–42), with 𝔹_k^{(N)} = 𝔹_k″ (1.17). CHECK whether 𝔹_k^{(0)} = 𝔹_k, so that the step-k base is the n = 0 member. CHECK the relation between j and n in χ_k^{(n)} (p.181 l.48), and that χ_k^{(0)} is in the integrand at the R-step's start.
- Read 13:36. χ_k^{(n)} is Bałaban's inductive assumption inside the R-step proof: "after n integrations the only characteristic functions which remain … are χ_k^{(n)}χ_h(Z_h∩Ω_h)" (p.181 l.38–40), with j = h + n.
  - χ_k^{(0)} (1.22) (p.181 l.12–14) bounds U^{(0)}_{k,Z} only on Ω_h∖Ω_{h+1}, by (1−β/2)ε_h(L^{k−h}η)². Components with 1 − χ_k^{(0)} are excluded from Z (l.16–20).
  - At n = N (j = k), χ_k^{(N)} is (1.24) for U″_{k,Z}, every region at ε-level. So the POST-R background has the per-region bound on all of Z. At n = 0, only layer h comes from χ_k^{(0)}. The layers j > h have the (1.3) indicators on the cube minimisers U_{j,□}(V_j), and (1.30) relates these to U_k^{(n)} with 𝐇 ≤ (β/10)ε_j, but in the direction from U_k^{(n)}'s bound to U_{j,□}'s.
  - CHECK which configuration the note's J_k belongs to (l.173: U_k^{(0)} vs D(k)(iii)'s base points; l.51's J_k). If it is the post-R background, (1.24) at n = N suffices. If it is the pre-R U_k, use (1.3) with the reverse of (1.30).
- Read 13:38. Note l.173: U_k^{(0)} is a G-valued gauge transform of one of D(k)(iii)'s real base points, so J_k is the PRE-R current, that of U_k^{(0)} = U(𝔹_k, V).
  - Data route: VAR (7) needs only the data's block-plaquette curvature. On □^{∼3}, V_j = M^j(U_{j,□}) (p.183 l.39), and (1.3) bounds U_{j,□}'s fine curvature by ε_j(L^{k−j}η)². So |∂V_j(p′) − 1| ≤ Cε_j (block plaquette from fine plaquettes). CHECK the citation for that averaging bound (VAR's "Proposition 2 [4]", p.278 l.47).
  - The global VAR fails: its ε₁ is the maximum, about ε_k, and g_k/g_m ≤ (1+β₀)(k−m)^{1/2} is not uniform in K.
  - The local VAR needs (7) on the pinned bonds Γ₀ of the localised set, which is U_k^{(0)}'s own fine curvature (circular). The other way is the reverse of LFR I (1.30) with 𝐇's bound, "22d²ε_j by the argument leading to (1.65) in [14]" (p.183 l.45 to p.184 l.1). CHECK whether that argument uses U_k^{(n)}'s curvature (circular) or only the data.
- Read 13:40.
  - The averaging bound is CMP98 Proposition 2, as REG quotes it: |∂U − 1| < α₀η² implies |∂Ū^j − 1| < 2α₀L^{2j}η² (REG p.87 l.35–36, raw minus 1).
  - REG (1.65)'s argument (p.87 l.33–43) starts from the configuration's own fine curvature. So LFR I (1.30)'s 22d²ε_j bound on 𝐇 uses U_k^{(n)}'s curvature on Ω_{j−1}∖Ω_{j+1}, which χ_k^{(n)} supplies at stage n = j − h. That is circular for stage 0 at layers j > h.
  - Consequence: for the pre-R U_k^{(0)}, the layers j > h need its own curvature at ε_j-level. The candidates are (a) CRE's inductive χ_j on U_{j,□}(V_j) (CRE p.257 l.39) plus a non-circular comparison, or (b) the map's D(k)(iii) pre-R clause extended by the current, which must then be propagated to k+1 from the T-step output U_{k+1} on χ_{k+1}'s support. NEXT: read how the map derives the real-U (2.34) at k+1 (map l.313–315 and D2.2), and reuse that mechanism for J.
- CHECK how U^{(n)}_{k,Z} (LFR I's interpolating sequence) relates to the note's real base points (post-R backgrounds; l.159, l.173).
- Read 13:40: Bałaban's mechanism.
  - At each stage he imposes the background's curvature by a decomposition of unity, 1 = χ_k^{(n)} + (1 − χ_k^{(n)}). The components with 1 − χ_k^{(n)} "do not satisfy the condition (ii)" and are excluded from Z as new large fields (LFR I p.181 l.15–20, for n = 0). He does this "following the procedure of Sect. 3 [III]" (p.181 l.8–10).
  - So on the support, the background's curvature at ε_j-level on the layer being integrated holds by construction. It is not derived from the data.
  - He never inserts an indicator on the current. In his spaces the real pair's 𝐉 is the configuration's current (CRE p.260 l.54, "in the same way as in the regular cases before"), and RG I p.263 l.21–22 is his single-scale statement that small curvature implies it.
- Plan for the write-up:
  - (i) Per layer, the background's curvature at ε-level on the support (the χ's).
  - (ii) The localised VAR problem around b, with its pinned collar inside the region where (i) holds. (7) at ε₁ = Cε_n then holds for every datum, the pinned bonds included.
  - (iii) VAR Theorem 1 bounds the current.
  - (iv) The ratio to α_{0,n}.
  - Open point of the plan: (i) for the pre-R U_k^{(0)} on layers j > h, and on layers older than h. Read CRE Sect. 3 (the T-step's own decomposition of unity on the new background U_{k+1}): if it imposes the background's curvature on every layer of Ω_{k+1} at the T-step, then (i) holds for the T-step output, which is the next step's pre-R base.

## Derivation Plan (13:41), Non-Circular

- (1) **Global level.** All data levels of U_k's set are at most (1+β₀)ε_k, since g_m ≤ (1+β₀)g_n for n > m (CRE (2.6)) and x(log x^{−2})^{p₀} is increasing. VAR Theorem 1 on the global set gives U_k ∈ 𝔘_k(B₃ε₁) with ε₁ = C(1+β₀)ε_k. So |U_k(∂p) − 1| < B₃ε₁L^{−2j} and (L^jξ)³|J_k| < B₃ε₁ on every layer j. This is uniform but at ε_k, not ε_j.
- (2) **Cube comparison.** On a cube □ ⊂ layer j, U_k equals (exp(−iξ𝐇_{j,□})·U_{j,□})^{u} as in LFR I (1.30) (p.183 l.42), with U_{j,□} = U(𝐁_j(□^{∼4}), M(Q_j^{s*}V_j)) (CRE p.257 l.31).
  - The argument field of 𝐇 vanishes off a boundary layer of width 2M₁. On that layer it is bounded by REG (1.65)'s reasoning from U_k's curvature, which is (1)'s B₃ε₁, not U_k^{(n)}'s imposed one. So it is not circular.
  - (190)'s decay over the cube, distance ≥ 2M₂R_j, gives 𝐇, ∇𝐇, and D*D𝐇 ≤ C B₃² e^{−δ2M₂R_j}ε_k on □^∼, as in CRE (3.7) (p.266 l.15–20).
  - R_j ≥ (log g_j^{−2})^r (CRE (2.5)). So e^{−δ2M₂R_j} ≤ g_j² for g small, and that term is ≤ Cg_j²ε_k = o(α_{0,j}), uniformly in j and K (ε_k ≤ A₀ḡ(log ḡ^{−2})^{p₀}). CHECK r and δM₂ so that e^{−δ2M₂R_j} ≤ g_j², and check (190)'s D*D entry (note l.164–165).
- (3) **Cube minimiser's current.** U_{j,□}'s fine curvature is below ε_jξ²-level on the support, by the indicator (CRE p.257 l.39; LFR I (1.3)). Its data are its own averages (the constraints), so CMP98 Proposition 2 (REG p.87 l.35–36) gives (7) at ε₁ = 2ε_j for the block plaquettes, and the pinned bonds of 𝐁_j(□^{∼4}) are the bonds of Q_j^{s*}V_j. CHECK (7) on those pinned bonds: Q^{s*}'s regularity from V_j. VAR Theorem 1 on 𝐁_j(□^{∼4}) then gives (L^jξ)³|J(U_{j,□})| < 2B₃ε_j.
- (4) **Sum.** The current is gauge covariant, and U_k = e^{−iξ𝐇}U_{j,□} up to gauge. So (L^jξ)³|J_k| ≤ 2B₃ε_j + C(𝐇 terms) + products ≤ (2B₃ + o(1))ε_j. And ε_j/α_{0,j} = (A₀/α₀)(log g_j^{−2})^{p₀−q₀} → 0. So C_J = 1, even (1−β), holds for g small, uniformly in j and K.
- (5) **Which layers.** CRE (2.36) is posed on Ω_n∖Ω_{n+1}, n = 1, …, j − 1, and on Ω_j. Every such cube carries its layer's indicator: CRE's χ_j(Ω_j) (p.257 l.39) for the step that made the layer, and LFR's (1.3)–(1.4). Nothing is posed on Ω₁^c. CHECK that the indicator of an old layer j (imposed at step j on U_{j,□}(V_j)) is still present at step k: the V_j stay integration variables, as l.5 states for V_h; CRE's inductive representation keeps the χ's as factors (map l.313, "kept as factors").

## Remaining checks (13:42)

- CRE (2.5) (p.255 l.34–37): "R_j is the smallest number of the form L^r such, that R_j ≥ (log g_j^{−2})^r". CHECK the value of r (r ≥ 1 is needed) and that 2δM₂ ≥ 1 (CRE's choice of M₂). Then e^{−δ2M₂R_j} ≤ g_j^{4δM₂} ≤ g_j².
- α_{0,j} = g_jC₀(log g_j^{−2})^{q₀}, with q₀ an integer > 1 (CRE (2.28), p.259 l.47–50). ε_j = g_jA₀(log g_j^{−2})^{p₀} (2.4). q₀ > p₀ is the table's standing provisional assumption ((R-m′)).
- 𝐇's D*D entry from (190), and the units of the current from 𝐇 (ξ-scaling).
- (7) on the pinned bonds of 𝐁_j(□^{∼4}): Q_j^{s*}V_j's regularity from V_j.
- Old layers: the indicators are kept as factors at step k.
- Related derived result (13:43): Cauchy note l.197 (*The current*) bounds a single-scale-k minimiser's current through its §10.3, a³|J′| ≤ 2B_λε₁, with ε₁ ≤ C_{ε₁}ε_k (CRE (3.12)). At the (T-Λ) data parameter ε₁ = C(M)R_kε_k it needs q₀ > p₀ + r, a choice of q₀ (CRE prints no upper bound). For step (3), §10.3 at scale j applied to U_{j,□} may replace VAR Theorem 1. CHECK whether step (3)'s ε₁ is 2ε_j (from the cube indicator) or carries C(M)R_j (from Q^{s*}'s pinned bonds). If it carries R_j, JB needs q₀ > p₀ + r, as the Cauchy note does.
- The Cauchy note's old-layer comparison, |J| ≤ B′ε₁L^{3(j−k)} < r_{0,j}, is for single-scale-k data. It does not transfer to the multiscale base, whose layer-j data are at scale j.

## TB9-3's Weaker Target and the Uniqueness Route (14:05–14:20)

- Target, as l.130 now states it: B_J := sup_n(L^nξ)³|J_k| → 0 as g → 0, uniformly in k and K. A constant would also do if it fits l.54's slack, but the order of ε₁ against λ and λ_R is untraced.
- **Uniqueness step (written into l.130).** The base is VAR's minimal configuration for regular data (CRE (2.12), p.256 l.42–47; l.94, l.101). Let ε₁′ ≤ ε₁ be any level at which the data meet VAR (7). Theorem 1 at ε₁′ gives an orbit in 𝔘_k(B₃ε₁′). By the uniqueness clause in (6) with ε₀ := B₃ε₁ ≤ B₃a₁ ≤ a₀, this is the base's orbit. Then VAR (2)'s second line (p.278 l.6) and (28) (p.282 l.34) give B_J ≤ B₃ε₁′. This avoids the circularity of VAR p.278 l.46–47.
- **Data level from curvature (checked).**
  - CMP98 Proposition 2 (p.26 l.46–53) assumes only (52), |U(∂p) − 1| < α₀η² at η = L^{−k} (p.26 l.14). It is local: (52) is needed only on the four blocks of p.
  - The real-U part of (2.34) gives α_{0,m}L^{−2m} ≤ (1+β₀)α_{0,k}L^{−2m} on layer m ≥ 1.
  - A layer-j block plaquette, mixed ones included (VAR p.278 l.38–45), has its blocks in global layers ≥ j − 1. So α₀ = (1+β₀)L²α_{0,k}, and the level is ε₁′ = 2(1+β₀)L²α_{0,k}.
- **Gap: Γ₀ = Ω₁^c.** CRE (2.34)–(2.37) are posed only on n = 1, …, j − 1 and on Ω_j (p.261 l.20). Nothing is posed on Ω₁^c, which carries the bonds themselves (CRE (2.2)). So the global level is not shown to tend to 0.
- **Localized version (sketch, 14:15).**
  - Take S := the localized set with support Ω_1 (CRE p.256 l.58–61). Its maximal domains are finer than 𝐁_k's on Ω_1, and its problem lives on Ω_1, so its (7) needs only plaquettes in Ω_1. There (2.34) gives the level ε₁′ = 2(1+β₀)L²α_{0,k}.
  - The note's nesting argument (l.130, *The identity on minimisers*) gives U(S, M_S(U_k)) = U_k on Ω_1 up to gauge. The global membership in 𝔘_k(B₃ε₁) puts U_k in S's uniqueness space, since S's layer indices are no larger.
  - The uniqueness step for S gives |D*∂U_k| < B₃ε₁′ξ²(L^{j_S}ξ)^{−3} at the bonds of S's free region, with j_S ≥ n − 1 on S's collar (the collar lies in Ω_1∖Ω_2 when 2M₁ < L²M₁) and j_S = n off it.
  - So (L^nξ)³|J_k| ≤ L³B₃ε₁′ = 2L⁵B₃(1+β₀)α_{0,k} → 0 at every bond of Ω_1 whose plaquettes all lie in Ω_1.
- **Left open in the sketch.**
  - (i) The bonds of Ω_1 with a plaquette meeting Ω₁^c. Their current involves layer-0 plaquettes, which are only regular at the fixed ε₁. Check whether CRE's frame room is posed there (X ∩ (Ω_1∖Ω_2) includes them) and whether the post-R base has Γ₀ = ∅ for k > N (old large fields renormalized by the R-operations, so Ω_1 = … = Ω_{k−N} = T_ξ?).
  - (ii) The collar widths of S (CRE p.257 l.8–11, l.22–26), against Ω_1∖Ω_2's width L²ξM₁ (CRE p.256 l.61).
  - (iii) That the nesting argument's VAR uniqueness for S is used within its scope: S finer than 𝐁_k on S's support.
- Read 14:22: Γ₀ ≠ ∅ in general.
  - The R-operation renormalizes only the components of Λ_k^c contained in a cube of size 100MR_k with no new large fields in the last N steps (LFR I p.177 l.17–27). Larger large-field regions persist, so Ω₁^c can persist at every k.
  - On (i), the likely closure: the layer-j small-field indicators in Bałaban's representation are posed on Ω_j^{∼4}∖Ω_{j+1}^∼ (LFR I p.178 l.16–19, as χ(sup|U_{j,□}(V_j, ∂p) − 1| < ε_j(L^{k−j}η)²)). If ∼ shrinks, as (1.10)'s use suggests, the scale-0 condition reaches one cube layer into Ω_1 and covers the outside of ∂Ω_1 up to Ω_0^{∼4}.
  - The layer-0 plaquettes next to Ω_1 would then be below O(ε_0) ≤ O((1+β₀)ε_k), and S's support can be Ω_1 enlarged into that zone.
  - Correction (14:25): ∼ ENLARGES. CRE p.250 l.26 defines Ω₁^{∼−1} = ((Ω₁^c)^∼)^c, so X^∼ adds a layer of cubes. The scale-j condition on Ω_j^{∼4}∖Ω_{j+1}^∼ therefore reaches 4 cube layers outside Ω_j and stops one layer short of Ω_{j+1}.
    - At j = 0 the fine-field condition is posed on Ω_0^{∼4}∖Ω_1^∼. It misses the one-cube collar Ω_1^∼∖Ω_1 just outside Ω_1.
    - That collar lies in the scale-1 condition's range Ω_1^{∼4}∖Ω_2^∼, which is a condition on the cube minimisers U_{1,□}(V_1), not on the fine plaquettes. The closure of (i) then needs the fine curvature in the collar from the scale-1 cube condition (an LFR I (1.30)-type comparison), or a support for S that stops inside Ω_1 with (i)'s bonds handled separately.
  - Read 14:30, the first step (CRE pp.246–248).
    - The fine field's small-field indicator is χ_0(P_0^c) = Π χ(sup_{p⊂□^∼}|U(∂p) − 1| < ε_0) (p.246 l.4–6).
    - Ω_1 = (Q_1′^{∼2})^c ∩ B(P_1^1)^{∼−3} (p.248 l.5) lies at distance at least 2LMR_1 from every large-field region. "On the set Ω_1^∼ we have only the small field characteristic functions", and χ_0 there is implied by the others (p.248 l.8–12).
    - So the ORIGINAL fine field, which is the base's field on Γ₀ = Ω₁^c, has |U(∂p) − 1| < ε_0 within distance 2LMR_1 of Ω_1. This assumes the first-step factors are kept at step k (CRE p.255 l.8–10).
  - Remaining point of (i), the plaquettes straddling ∂Ω_1 at the base. They have free bonds in Ω_1 (U_k's values, not the original field's) and pinned bonds outside. They enter J at the bonds next to ∂Ω_1, and Proposition 2's local hypothesis for the layer-1 block plaquettes with vertices in Λ_0.
    - The real-U part of (2.34) is posed on plaquettes in Ω_n∖Ω_{n+1}, n ≥ 1, so it does not obviously cover them.
    - Candidates: the step-1 comparison χ_0′, |U(b)U_{1,□′}^{−1}(b) − 1| < 2δ_0 on □′^{∼2} (p.247 l.45, δ_0 = (A_1/A_0)ε_0), carried to U_k by the inductive comparisons; or VAR (9)–(10)'s local regularity in the cubes of Ω_0∖Ω_2.
    - Also check whether the frame room is posed at bonds next to ∂Ω_1 at all: member domains and CRE p.257 l.8–11, l.22–26.
  - 14:33, two simplifications.
    - (A) The frame term vanishes on layer 0. At n = 0 the bound Σ_{m<n}8dL^{m+1}φ is an empty sum, so λ_f = 0 there; REG's normalisation is trivial on Γ₀. So J_k is needed only on Ω_1 (l.48's n ≤ k includes n = 0, but the term is 0 there).
    - (B) VAR (7) is a condition on the DATA V, not on U_k's fine plaquettes, so the straddling fine plaquettes need not be bounded first. Take as S the restriction of 𝐁_k to the support Ω (Ω_1 plus a margin of fine layers inside the ε_0-zone). Its layering is 𝐁_k's, so S's layer index is the global n and there is no collar loss. Its (7) needs:
      - (a) layer-j data plaquettes inside Ω_1 (j ≥ 1): Proposition 2 from (2.34), at level 2(1+β₀)L²α_{0,k};
      - (b) layer-0 data in the margin, which are the original fine field: level ε_0 by χ_0;
      - (c) the mixed layer-1 plaquettes across ∂Ω_1, V(x,y)V̄(y,z)V(z,w)V(w,x), with V̄ the average of the original layer-0 bonds. By χ_0′ (|U(b)U_{1,□′}^{−1}(b) − 1| < 2δ_0 on □′^{∼2}, p.247 l.45) the original field near ∂Ω_1 is within 2δ_0 of the cube minimiser U_{1,□′}. With V_1 = M(U_{1,□′}) on □′'s interior (as LFR I p.183 l.39 states at scale j), (∂V)(p′) is Ū_{1,□′}(∂p′) up to O(δ_0). Proposition 2 applied to U_{1,□′} (curvature < ε_1-level by χ_1) gives O(L²ε_1 + δ_0) → 0.
    - Then VAR Theorem 1 with uniqueness gives U_k ∈ 𝔘_S(B₃ε₁′) with ε₁′ → 0, and the current bound at every bond of Ω_1, including those next to ∂Ω_1, whose plaquettes lie in the support. So B_J ≤ B₃ε₁′ → 0.
    - CHECK for (c): that χ_0′ and χ_1 (step-1 factors) are still factors at step k at the real base; that V_1 = M(U_{1,□′}) on the relevant cubes; the units of χ_1's ε_1η² against VAR's normalisation; and that (c)'s cubes □′^{∼2} cover the blocks of every mixed plaquette at ∂Ω_1.
  - Localisation: the free bonds of 𝐁_k lie in Ω_1, and the plaquettes in which they occur lie within one fine step of Ω_1, so U_k is the minimiser of the problem with support Ω := Ω_1 plus a margin of a few fine layers inside the zone above. CRE (2.12) defines the minimal orbit as the set of minima over regular U with M(U) = V, so VAR is applied to that problem.
  - CHECK: that the old layers' indicators are factors at the real base (CRE (2.18): χ_k(Ω_k) for the newest layer, with the older ones inside 𝐓_k); and the relation between U_{0,□} and the fine field at scale 0 (Q^{s*} at j = 0 is the identity?).

## Checks Done and the Derivation (14:35–14:40)

- **(A) checked.** REG (1.70) for x ∈ B^j(Λ_j) sums over n = 0, …, j − 1 (REG p.88 l.38–44, raw l.39–45). At j = 0 the sum is empty, so every REG-normalised transformation is 1 at the layer-0 points. So u″ = v_k = 1 and f = 1 there, and the frame term (R(f) − 1)J_k vanishes on the bonds of Γ₀. J_k is needed on Ω_1 only.
- **(c) replaced by Bałaban's own first-step bound, so χ_0′ and χ_1 are not needed.**
  - CRE p.246 l.21–22: "If a plaquette p′ is contained in (P_0^c)^{(1)}, then Proposition 1 [12] implies that the new field V satisfies the bound |V(∂p′) − 1| < 2L²ε_0". Here V = Ū of the fine field U that obeys χ_0(P_0^c) (p.246 l.4–6, |U(∂p) − 1| < ε_0 for p ⊂ □^∼).
  - For a mixed layer-1 plaquette at ∂Ω_1, VAR's (∂V)(p′) (p.278 l.38–45) is Ū(∂p′): V = Ū on Ω_1^{(1)} by the δ(ŪV^{−1}) of CRE (1.11) (p.248), and V̄ on the layer-0 bonds is the average of V_0 = U on Ω₁^c (p.248, below (1.11)).
  - Its blocks lie in Ω_1^∼, inside P_0^c, since Ω_1 is at distance ≥ 2LMR_1 from every large-field region (p.248 l.7–8). So |(∂V)(p′) − 1| < 2L²ε_0 on the support of ρ_1, which is the support of the step-1 factors.
  - The same bound covers every layer-1 data plaquette in (P_0^c)^{(1)}.
- **(b) checked.** "On the set Ω_1^∼ we have only the small field characteristic functions", and χ_0 localized in Ω_1^∼ is "equal to 1" on the domain of integration (p.248 l.8–12). So |V_0(∂p) − 1| < ε_0 for the plaquettes of the original field in Ω_1^∼ (one LMR_1-cube layer, at least one fine step, outside Ω_1).
- **Bałaban's own instance.** At step 1 Bałaban applies VAR Theorem 1 to exactly this problem, "U = V_0 on Ω_1^c, Ū = V on Ω_1^{(1)}" (CRE (1.12), p.248): "By Theorem 1 [15] there exists exactly one critical point … for ε_0 sufficiently small". This is the step-1 case of the route, with a data level O(L²ε_0).
- **Persistence to step k.** The layer-0 variables V_0 = U|_{Ω_1^c} and the layer-1 variables V on Ω_1∖Ω_2 are not integrated at later steps. Their first-step factors stay in the density: ζ(Ω_1^c) and the characteristic functions "defined in the first step" (CRE p.255 l.8–10), and D(k)(iii) takes the base on the support of the term's indicators, kept as factors (map l.313).
  - The R-operation changes Ω₁^c only by removing whole components Z of the large-field region (LFR I p.177 l.17–27; LFR II (1.33)). So the remaining parts of ∂Ω_1 keep their first-step margin.
  - Checked 14:42: every part of ∂Ω_1 at step k is a first-step boundary.
    - Λ_k ⊂ Ω_k ⊂ Ω_1, so Ω₁^c ⊂ Λ_k^c, and each component of Ω₁^c lies in one component of Λ_k^c.
    - An R-operation's region Z is a union of whole components of Λ_k^c (LFR I p.177 l.17–31). On Z the new set is Z^{(k)} at scale k, and off Z it is unchanged: Γ_j = Γ″_j ∩ Z^c with Ω_j″ = Ω_j off Z (LFR II (1.33), p.365 l.2–7; LFR I (1.12)).
    - So an R-operation either removes a component of Ω₁^c entirely (it becomes part of Ω_1 at scale k) or leaves it with its first-step boundary.
    - Large fields found at later steps j ≥ 1 change only Ω_{j+1} ⊂ Ω_j ⊂ Ω_1.
    - So the first-step margin of (b) and (c) holds at every remaining part of ∂Ω_1.
- **Derivation, as it will go into l.173 (after TB clears).**
  1. Only Ω_1 matters, by (A).
  2. The support problem. Let Ω := Ω_1^∼. The free bonds of 𝐁_k lie in Ω_1 (Γ₀ = Ω₁^c is pinned, CRE (2.2)), and every plaquette containing a free bond lies in Ω. So U_k is the minimal configuration of 𝐁_k restricted to the support Ω, the problem of CRE (1.12) at step k (CRE p.256 l.58–61 for a support), with its layering equal to 𝐁_k's.
  3. Its data meet VAR (7) at ε₁′ := max(2L²ε_0, 2(1+β₀)L²α_{0,k}):
     - layer 0 (the original field in Ω∖Ω_1) at ε_0, by (b);
     - layer 1 at 2L²ε_0, by p.246 l.21–22;
     - layer j ≥ 2, mixed plaquettes included, at 2(1+β₀)L²α_{0,k}, by CMP98 Proposition 2 (local form, p.26 l.46–53). Its hypothesis on the four blocks, all in Ω_{j−1} ⊂ Ω_1, comes from the real-U part of (2.34) (map l.315) with α_{0,m} ≤ (1+β₀)α_{0,k}.
     ε₁′ → 0 as g → 0, uniformly in k and K.
  4. VAR Theorem 1 at ε₁′, and the uniqueness clause at ε₀ := B₃ε₁ (l.130), put U_k's orbit in 𝔘(B₃ε₁′). By VAR (2)'s second line and (28), (L^nξ)³|J_k| < B₃ε₁′ at every bond of Ω_1 (the layer index of the restriction is the global n).
  5. So B_J ≤ B₃ε₁′ → 0. This closes Open (R-eval-Jbase) (derived; it awaits its own two rounds as packet JB, after TB clears).

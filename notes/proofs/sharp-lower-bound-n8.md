# Towards finiteness of $GG_8(r)$ for all $r<\sqrt{10-5\sqrt2}$: induced pseudogroups and a reduction to the critical radius

Authors: Eric Vergo, Claude

**Statement and status.** Let $r_c=\sqrt{10-5\sqrt2}\approx1.711412$. `critical-radius-n8.md` (Theorem A; refereed and Lean-checked) proves that $GG_8(r)$ is infinite for every $r\ge r_c$. This note is about the converse, Conjecture F₈: $GG_8(r)$ is finite for every $r<r_c$. **F₈ is still open: this note does not prove it, and so does not prove that $r_c$ is exactly the critical radius.** The note has been independently refereed; see `referee-report-sharp-lower-bounds.md` in this directory, whose verdicts §7 follows. What it contains:

1. **The certified initial range.** The best checked certificate for $n=8$ is the one recorded in `../certificates.md`: $\delta=1/36$, generated and checked by the repository's Lean engine. So $GG_8(r)$ is finite for every $r\le r_\ast$ with $r_\ast^2=r_c^2-1/36$, i.e. $r_\ast\approx1.703278$, leaving an open window $r_c-r_\ast\approx0.008135$. This is proved modulo that exact computation. The certificates of §3 ($\delta=1/16$, $1/20$, $1/35$) are consistent with it and implied by it through monotonicity. $\delta=1/16$ is the one also checked by a second, unrelated exact verifier. All of them lie past the level-4 jump and before $\delta_5\approx0.0272$. A deeper certificate is a symmetry-reduced window-free closure at $\delta=547/25000=0.02188$ ($r_\ast\approx1.705008$, $r_c-r_\ast\approx0.006404$), past $\delta_5$, with (C1)–(C4) checked by the engine's relative checker ([`../relative-certificates.md`](../relative-certificates.md) §§7, 10; [`../certificates.md`](../certificates.md) §5).
2. **A reduction theorem (proved).** By Theorem 5.3 and Theorem 5.5:
   - bound the orbits by a product of restricted-orbit counts, taken over nested windows about the 32 critical lattice points;
   - by monotonicity, every factor except the innermost is bounded by its value **at $r_c$ itself**.

   So F₈ follows from Conjecture S (§5.5), which has two parts. (S1) is a statement about the critical system alone: restricted orbits that avoid small windows about the critical points are finite. (S2) is an exact combinatorial renormalization of the innermost induced pseudogroup along one geometric sequence $r_m\uparrow r_c$.
3. **Algebraic lemmas (proved).**
   - Every cut set has all its circle centres in $1+2\mathbb Z[\zeta]$.
   - On the radius families used here, no two circles are ever tangent and no lattice point lies on a circle.
   - The levels have a closed form, and the natural scaling is $\delta\asymp\varepsilon^m$ with zoom $\varepsilon^{-m}$.
   - There are exactly 32 critical lattice points, in 8 classes under the symmetries, and the circle normals there take 16 directions.
   - No affine lattice map that is a physical isometry expands internal space. So no such map gives an exact global recursion of the centre set. Nothing is proved about other maps (Proposition 2.5).
4. **The proposed "stable limiting pattern" strategy fails for the cut set itself.** Near $p^\ast$, $K(r)$ has no locally finite scaling limit (evidence, §4). It refines everywhere, and $p^\ast$ is a typical point of it.
5. **Evidence (sampled floating-point orbits, not proof) that the induced pseudogroup does renormalize.**
   - Under $\tau\mapsto\varepsilon^2\tau$ ($\varepsilon^2=3-2\sqrt2$), the sampled germ sets agree exactly for levels $2\to4$ (27 of 27 germs) and in 20 of 23 germs for $3\to5$. These are sets of sampled germs from floating-point orbits, not complete germ sets.
   - Its zoomed partitions converge: identical patterns at identical zoomed points in 83%, 90% and 95% of samples for $m\to m+2$, $m=2,3,4$.
   - Its boundaries lie on lines in only 8 directions.
   - Its orbit counts in the innermost window stay at 188, 224, 223 for $m=2,4,6$.
   - At $r_c$, the bulk factor and the coarsest annulus factor of (S1) were finite in every sample. The bulk factor reached at most about $4.4\cdot10^4$ points, with the same values from starting points at any depth near $p^\ast$. Finer annulus factors at $r_c$ were not measured (§6.4).

Throughout, "verified exactly" means every decision is an exact sign in $\mathbb Q(\sqrt2)$ or in a tower $\mathbb Q(\sqrt2)(\sqrt{H_1},\sqrt{H_2})$. Statements from floating-point orbit sampling are labelled **evidence**.

Terms:
- A *germ* is the local isometry $x\mapsto\zeta^jx+t$ by which a group element acts near a point.
- A *pseudogroup* is a family of partial isometries closed under composition and inverses where defined.
- The *induced* pseudogroup on a set $U$ consists of the germs of group elements carrying points of $U$ into $U$.
- A *restricted* orbit allows only chains whose intermediate points avoid a given set.

---

## 1. Setting and notation

As in `critical-radius-n8.md` §1:
- $\zeta=e^{2\pi i/8}$; $D_1,D_2$ are the closed disks of radius $r$ about $\mp1$;
- $A,B$ are the rotations by $-2\pi/8$ about $\mp1$; $a=A$ on $D_1$ and $a=\mathrm{id}$ elsewhere, and likewise $b$ with $B$ and $D_2$; $G(r)=GG_8(r)=\langle a,b\rangle$;
- $\varepsilon=\sqrt2-1$, and $\sigma:\zeta\mapsto\zeta^3$ is the internal embedding;
- $p^\ast=1-2\zeta+\zeta^2-\zeta^3=-1+(2+i)(1-\zeta)$, and $r^2=r_c^2-\delta$.

Lattice points are written as integer vectors in the basis $1,\zeta,\zeta^2,\zeta^3$.

- A **chain** is a sequence $z_0,\dots,z_L$ with $z_i=s_i(z_{i-1})$ and $s_i\in\{a^{\pm1},b^{\pm1}\}$. $O_r(z)$ is the set of endpoints of chains from $z$ (`boundary-contact.md` Lemma 2.3).
- The **cut set** $K(r)$ is the closure of $\partial D_1\cup\partial D_2$ under $A^{\pm1}$ on $D_1$ and $B^{\pm1}$ on $D_2$. If it is a finite union of arcs satisfying (C1)–(C4), then $G(r)$ is finite (`critical-radius-n8.md` Theorem 3.1).
- **Group monotonicity** (`boundary-contact.md` Theorem 3.4, refereed): if $G(r)$ is finite, so is $G(r')$ for every $r'\le r$. Hence F₈ is equivalent to finiteness along *any one* sequence $r_m\uparrow r_c$. This is how the intermediate radii are handled throughout: they never need separate treatment.
- **Uniform orbit bound** (`boundary-contact.md` Proposition 3.3): $G(r)$ is finite if and only if its orbit sizes are bounded.

---

## 2. Algebraic lemmas (proved)

**Lemma 2.1 (centre coset).** Every circle carrying an arc of $K(r)$ has its centre in $1+2\mathbb Z[\zeta]$, and so does every endpoint symbol used to name arc endpoints.

*Proof.* The centres of $\partial D_{1,2}$ are $\mp1$, and every other circle is an image of these under composites of $A^{\pm1}$ and $B^{\pm1}$. If $z\equiv1\pmod2$, then $z+1\equiv0$, so $A(z)=-1+\zeta^{-1}(z+1)\equiv-1\equiv1$. The same holds for $A^{-1}$ and $B^{\pm1}$. Endpoint symbols are such centres too. The residues were also checked exhaustively (`exactlemmas.py`). $\square$

**Lemma 2.2 (tangency, lattice points on circles, triple points).** Let $\rho=r^2$.
1. Two distinct circles of radius $r$ with centres in $1+2\mathbb Z[\zeta]$ are tangent only if $\rho=|w|^2$ for some $w\in\mathbb Z[\zeta]$, so only if $\rho\in\mathbb Z[\sqrt2]$.
2. A lattice point lies on such a circle only if $\rho\in\mathbb Z[\sqrt2]$.
3. Three such circles pass through one point only if $\rho$ is the squared circumradius of a lattice triangle, which lies in $\mathbb Q(\sqrt2)$. If $\rho\notin\mathbb Q(\sqrt2)$ the arrangement of all such circles is generic.
4. Consider the family $\rho=(10-\delta)-5\sqrt2$ with $\delta\in\mathbb Q\setminus\mathbb Z$, and the family $\rho_m=r_c^2-\theta(3\sqrt2-2)\varepsilon^m$ with $\theta\in\mathbb Q\setminus\mathbb Z$ and $m\ge0$. On both, no two circles are tangent and no lattice point lies on a circle.

*Proof.*
1. The centres differ by $2w$, and tangency of two equal circles means $|2w|=2r$.
2. $|z-c|^2\in\mathbb Z[\sqrt2]$ for lattice points $z,c$.
3. With $u=c_2-c_1$ and $v=c_3-c_1$, $R^2=|u|^2|v|^2|u-v|^2/(4\,\mathrm{Im}(u\bar v)^2)$, and every factor lies in $\mathbb Q(\sqrt2)$.
4. For the first family, $\rho\in\mathbb Z[\sqrt2]$ forces $\delta\in\mathbb Z$. For the second, $\varepsilon^m$ is a unit, so $\rho_m\in\mathbb Z[\sqrt2]$ iff $\theta(3\sqrt2-2)\in\mathbb Z[\sqrt2]$. Writing $\theta=a/b$ in lowest terms, that requires $b\mid3a$ and $b\mid2a$, so $b=1$. $\square$

Part 4 sharpens the remark of `critical-radius-n8.md` §3.3, which needed $4\delta\notin\mathbb Z$. Triple points are not excluded on these families. The exact engine detects them, and every run reported in §3 found **none**: "0 equalities of points with different symbols".

**Lemma 2.3 (levels and scaling).** Let $q_m=p^\ast+i\varepsilon^m$. Exactly,
$$|q_m+1|^2=r_c^2-(3\sqrt2-2)\varepsilon^m+\varepsilon^{2m},\qquad\delta_m:=r_c^2-|q_m+1|^2=(3\sqrt2-2)\varepsilon^m-\varepsilon^{2m}.$$
So $q_m$ enters $D_1$ exactly at $r^2=r_c^2-\delta_m$, and $\delta_m/\delta_{m+1}\to1+\sqrt2$. The circle $\partial D_1(r)$ passes at distance $\delta/(r_c+r)$ from $p^\ast$, which is first order in $\delta$.

**So the natural scaling is $\delta\asymp\varepsilon^m$ with spatial zoom $\varepsilon^{-m}$ about $p^\ast$.** In the zoomed picture, $\partial D_1$ sits at a fixed offset, and each circle of radius $r$ becomes a circle of radius $r\varepsilon^{-m}$. Over a zoomed window of size $O(1)$ such a circle deviates from a line by $O(\varepsilon^m)$.

*Proof.* $|q_m+1|^2=|p^\ast+1|^2+2\varepsilon^m\mathrm{Im}(p^\ast+1)+\varepsilon^{2m}$, and $\mathrm{Im}\,p^\ast=-(3\sqrt2-2)/2$. Checked exactly for $m\le12$. Examples: $\delta_4=-683+483\sqrt2\approx0.065151$, $\delta_5=-3107+2197\sqrt2\approx0.027197$, $\delta_6=-20219+14297\sqrt2\approx0.011301$. $\square$

The $\sqrt2$-coefficient of $|q_m+1|^2$ ($-2,-30,-44,-488,-2202,\dots$) is never $-5$. So the rational-$\delta$ family of §3 never lands exactly on an entry radius.

**Lemma 2.4 (the critical configuration).**
1. The lattice points on $\partial D_1(r_c)\cup\partial D_2(r_c)$ are exactly the 32 points $\mp1+u(2\pm i)(1-\zeta)$, $u\in\mu_8$. Under the symmetry group $\{z,-z,\bar z,-\bar z\}$ they form **8 classes** (Table 2.1). The rotation $A$, which permutes the 16 points on $\partial D_1$, is not a symmetry of the system, so distinct classes are genuinely inequivalent for $r<r_c$.
2. The circles of radius $r_c$ through $p^\ast$ with centre in $1+2\mathbb Z[\zeta]$ are exactly the four with centres $(-1,0,0,0)$, $(3,-4,0,0)$, $(3,-4,2,-2)$ and $(-1,0,2,-2)$.
3. At $r_c$, the circle about $\mp1+2v$, with $v=u(2\pm i)(1-\zeta)$, is tangent to $\partial D_{1,2}$ at the critical point $\mp1+v$. All 32 of these centres lie in $1+2\mathbb Z[\zeta]$. At $r=r_c$ the engine stops at once on one of them: the circle about $(-3,-2,2,-4)$ is tangent to $\partial D_2$.
4. The normals of the radius-$r_c$ lattice circles through the critical points take exactly the 16 directions $u(2\pm i)(1-\zeta)$. Modulo $\pi/4$ these are $0.0709$ and $0.7144$ radians.

*Proof.*
1. $\mathbb Z[\zeta_8]$ is a principal ideal domain. $w\bar w=5(2-\sqrt2)$ forces $w=\mu(2\pm i)(1-\zeta)$ with $|\mu|^2=1$. Every conjugate of $|\mu|^2$ is then 1, so $\mu$ is a root of unity by Kronecker's theorem.
2. Enumerate the 16 candidates $p^\ast+v$ against the class $1+2\mathbb Z[\zeta]$.
3. $|w|^2=4r_c^2$ forces $w=2\mu(2\pm i)(1-\zeta)$ by the same argument.

Everything was checked exactly by `exactlemmas.py`. $\square$

**Table 2.1.** The 8 classes of critical points. "Side" says which boundary circle the point lies on at $r_c$. "Other disk" says whether it lies inside the other disk.

| representative | value | side | other disk |
|---|---|---|---|
| $(1,1,-1,2)$, the class of $p^\ast$ | $0.2929+1.1213i$ | $\partial D_1$ | inside $D_2$ ($6-3\sqrt2$) |
| $(0,-1,2,-2)$ | $0.7071-0.1213i$ | $\partial D_1$ | inside $D_2$ ($10-7\sqrt2$) |
| $(-2,1,2,-2)$ | $0.1213+1.2929i$ | $\partial D_1$ | outside ($18-11\sqrt2$) |
| $(0,1,2,-2)$ | $2.1213+1.2929i$ | $\partial D_2$ | outside ($10+\sqrt2$) |
| $(-1,2,1,-1)$ | $1.1213+1.7071i$ | $\partial D_2$ | outside ($6+\sqrt2$) |
| $(3,-2,1,-1)$ | $2.2929-1.1213i$ | $\partial D_2$ | outside ($22-7\sqrt2$) |
| $(3,-1,1,2)$ | $0.8787+1.7071i$ | $\partial D_2$ | outside ($22-11\sqrt2$) |
| $(2,-1,2,-2)$ | $2.7071-0.1213i$ | $\partial D_2$ | outside ($18-3\sqrt2$) |

**Proposition 2.5 (physical isometries do not expand internally).** Let $\alpha\in\mathbb Q(\zeta)^\times$ and $\beta\in\mathbb Q(\zeta)$. If $c\mapsto\alpha c+\beta$ or $c\mapsto\alpha\bar c+\beta$ is an isometry in physical space, then it is also an isometry in internal space. Among the $\mathbb Q$-affine maps respecting the physical/internal splitting (the maps $x\mapsto\alpha x+\beta' \bar x+\gamma$ with $\alpha,\beta'\in\mathbb Q(\zeta)$), these two forms are exactly the physical isometries.

*Proof.* Physical isometry means $|\alpha|^2=1$. Since $|\alpha|^2\in\mathbb Q(\sqrt2)$ is then rational, its Galois conjugate $|\sigma\alpha|^2$ is also 1. $\square$

So no lattice affine map that is a physical isometry can give an exact recursion $C(r_{m+1})=F(C(r_m))$ of the circle centres, since such a recursion would need the internal window to grow. The proposition says nothing about maps that are not physical isometries, about piecewise or local maps, or about the window itself. §6 reports what was observed to recur: the sampled germs of the induced pseudogroup.

---

## 3. The certified initial range (proved modulo an exact computation)

**The certified range is that of `../certificates.md`.** It records exact engine certificates for $n=8$ up to $\delta=1/36$ ($r\approx1.703278$, $r_c-r\approx0.008135$; 582 886 circles, 6 474 082 maximal arcs, 82 624 (C4) endpoints). Each was generated and checked by the repository's Lean engine. With group monotonicity this gives:

**Theorem 3.1 (proved modulo the exact computation recorded in `../certificates.md`).** $GG_8(r)$ is finite for every $r\le r_\ast$, where $r_\ast^2=r_c^2-1/36$ and $r_\ast\approx1.703278$.

The certificates produced for this note, listed below, are consistent with that record and implied by it. They are kept because the $1/16$ one has also been checked by a second, unrelated exact verifier, and because the step structure below comes from the same runs.

**Programs.** The certificates were produced by the repository's compiled engine, run read-only:
```
tdcsg-orbit certify -n 8 --r2 closed-δ --max-pieces 400000000 --out FILE
```
Its generator uses a floating-point filter with rigorous error bounds, and an exact fallback whenever the filter cannot decide. Each certificate is checked by `tdcsg-orbit check-certificate FILE`. That checker makes no floating-point decision. It shares with the generator only the exact field layer, and it re-derives (C1)–(C4) from scratch.

As a second, unrelated check, the exact Python verifier of the earlier note (`verify.py`, copied unchanged into the scratch directory `sharp8/exact/`) reads the engine's files after conversion by `conv.py`.

**Cross-checks with the earlier note.**
- At $\delta=1/7$ the engine gives 24 150 circles, 122 762 maximal arcs and 5 692 (C4) endpoints, as in `critical-radius-n8.md` Table 3.1.
- `verify.py` declares the engine's $1/7$ file VALID: 290 660 image arcs, 465 s.
- At $\delta=1/14$ the engine gives 36 024 circles and 291 418 arcs, again as tabulated.

**Table 3.1.** Certificates produced for this note, at $r^2=r_c^2-\delta$.

| $\delta$ | $r$ | $r_c-r$ | circles | maximal arcs | (C4) endpoints | max $\lvert\sigma(c)\rvert$ | generator | `check-certificate` | `verify.py` |
|---|---|---|---|---|---|---|---|---|---|
| $1/16$ | 1.693054 | 0.01836 | 129 380 | 882 710 | 17 012 | 262.5 | 98 s, 0.58 GB | **VALID** (2 092 704 image arcs, 275 s) | **VALID** (2 092 708 image arcs ‡, 3 595 s) |
| $1/20$ | 1.696742 | 0.01467 | 174 540 | 1 921 458 | 35 216 | 288.5 | 555 s, 1.26 GB | **VALID** (4 559 776 image arcs, 607 s) † | not run |
| $1/35$ | 1.703045 | 0.00837 | 248 500 | 3 764 582 | 78 384 | 356.0 | 2 152 s, 2.27 GB | **VALID** (8 940 960 image arcs, 1 241 s, 2.97 GB) | not run |

‡ The two verifiers count image arcs slightly differently (2 092 704 against 2 092 708); every other invariant agrees exactly.

† The $1/20$ certificate and its check log were produced by another session, in the scratch directory `cert/deep/`, by the same engine. For this note, its SHA-256 (`7e0e16ee…aa8aa0f728`) was recomputed and found to match the recorded value, and the check log was read. The check was rerun here with the same checker: **VALID**, 638 s.

These certificates give, independently of the record, finiteness for $r^2\le r_c^2-1/35$ ($r\approx1.703045$), which Theorem 3.1 contains. Finiteness for $r^2\le r_c^2-1/16$ is the best-supported part, since it was checked by two unrelated exact implementations.

The referee re-ran `check-certificate` on the $1/35$ and $1/16$ files: both VALID, with all counts as in Table 3.1. The SHA-256 of the $1/35$ file is `d08fa0d01e118e941c32c3e7105596cf15ec9980a93fa556d32f4ffad54a26df`.

**The step structure (evidence; generator output only).** Every run below closed, with no (C4) failure and no exact coincidence.

| $\delta$ | 0.15 | 0.13 | 0.11 | 0.09 | 0.08 | 0.075 | 0.0705 | 0.069 | 0.068 | 0.067 | 0.066 | $\delta_4\pm10^{-6}$ | 0.064 | 0.0625 | 0.06 | 0.055 | 0.05 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| circles ($10^3$) | 19.5 | 28.0 | 28.2 | 31.2 | 31.4 | 35.6 | 36.0 | 36.0 | 64.4 | 71.6 | 73.7 | 100.3 / 100.4 | 117.0 | 129.4 | 138.0 | 170.2 | 174.5 |

**The level-4 jump.**
- Bisection locates the first big step of level 4 in $\delta\in(0.0684648,\,0.0684688)$. Across that interval the circle count goes from 36 040 to 64 402 (28 362 new circles, none lost).
- The new circles of smallest internal size come in 8-fold symmetric families. Each passes at distance $0.0214\approx0.31\,\delta$ from a critical point of one of the five classes on $\partial D_2$ outside $D_1$ (Table 2.1).
- So this new structure is **born at level-scale distance from critical points**, but not at $p^\ast$.
- The entry of $q_4$ into $D_1$ itself (at $\delta_4$) changes the cut set by only 40 circles.
- The orbit of $0$, by contrast, jumps exactly at $\delta_4$ and at $\delta_5$, by an exact threshold sweep: $3\,149\to16\,297$ points at $r^2=693-488\sqrt2$, and $24\,163\to86\,679$ at $3117-2202\sqrt2$.
- At $r^2=693-488\sqrt2$ exactly the engine stops on a tangency, which Lemma 2.2 permits for $\rho\in\mathbb Z[\sqrt2]$.

**Cost.** The compiled engine is about 40 times faster than the Python closure of the earlier note. Level 5 ($\delta<\delta_5\approx0.0272$) should need about $10^6$ circles and roughly 10 GB, which is beyond the 8 GB budget of this run. In any case no single computation reaches $r_c$.

---

## 4. The "stable limiting pattern" strategy for $K(r)$: tested, and refuted in its literal form

The strategy: zoom $K(r)$ by $\varepsilon^{-m}$ about $p^\ast$ at $\delta\asymp\varepsilon^m$ (Lemma 2.3), and expect finitely many arcs in each fixed zoomed window, converging in $C^1$ to a limit arrangement of lines.

**Observation 4.1 (evidence).** The number of circles of $K(r)$ whose arcs meet the disc of radius $0.4\delta$ about $p^\ast$ is:

| $\delta$ | 1/2 | 1/3 | 1/5 | 1/6 | 1/7 | 1/10 | 1/12 | 1/13 | 1/14 | 1/16 |
|---|---|---|---|---|---|---|---|---|---|---|
| at $p^\ast$ | 36 | 77 | 66 | 64 | 174 | 191 | 141 | 139 | 143 | 282 |
| median at random points of $D_1$ | 34 | | | 57 | | | | | 132 | 161 |

- The count roughly doubles per level: for example 64 at $1/6$, 143 at $1/14$, 282 at $1/16$.
- It is of the same order as at random points of $D_1$. At $1/16$ it is above the random median of 161; the random quartiles there are 3 and 249, because some regions of $D_1$ are large empty cells.
- Matching each circle near $p^\ast$, recorded by (centre direction, offset$/\delta$), to its nearest neighbour one level or two levels later gives median mismatches of 0.2–0.4. The pattern does not recur.

**Conclusion.** The cut set has no locally finite limit at $p^\ast$, so claim (1) of the strategy is false for $K(r)$. Claim (4) fails too: there is no stable bulk with local copies glued in.
- $K(r)$ refines everywhere. Its total length grows about 5-fold per level (582, 3 219 and 15 625 at $\delta=1/2,1/6,1/14$), so its mesh shrinks roughly like $\delta^{1.8}$ (a factor of about 5 in length against $1+\sqrt2$ in $\delta$).
- Generic orbits equidistribute. A level-6 orbit of $3\cdot10^5$ points visits the 32 windows of half-width $\varepsilon^5$ about as often as their area predicts.

**The centre set is a model set with a growing disc window (evidence).** Here a model set means the lattice points whose internal coordinate $\sigma(c)$ falls in a fixed region, the window.
- At $\delta=1/14$, every $c\in1+2\mathbb Z[\zeta]$ whose circle meets $D_1\cup D_2$ and has $|\sigma(c)|\le40$ is a centre of $K(r)$.
- The filled fraction is at least $0.986$ up to $|\sigma(c)|=100$, then falls through $0.95,0.78,0.43,0.11,0$.
- The window's angular profile is flat to 3%, and its radius $R_W$ satisfies $R_W\delta\in[7.8,14.4]$ for $\delta\in[1/14,1/2]$.
- By Proposition 2.5, no lattice affine map that is a physical isometry can carry this growing window to itself.

**What survives.** The scaling of Lemma 2.3 and the line limit of single circles are correct. The object that has a limit is the pseudogroup *induced* on windows about the critical points. Its partition is much coarser than $K(r)\cap U$: most arcs of $K$ in $U$ are discontinuities of excursions that never return to $U$ at that scale.

---

## 5. Induced pseudogroups and the reduction (proved)

### 5.1 Restricted orbits

Fix $r$. For $W\subseteq\mathbb C$ and $x\in\mathbb C$ let
$$R_W(x)=\{z_L:\ z_0=x,\dots,z_L\text{ a chain with }z_1,\dots,z_{L-1}\notin W\}.$$
This includes $L=0$, and the endpoint may lie in $W$. Put
$$\beta(W)=\sup_{x\in\mathbb C}|R_W(x)|,\qquad\beta(V;W)=\sup_{x\in W}|R_V(x)\cap W|\quad(V\subseteq W).$$

**Lemma 5.1 (last visit).** If $O(z)\cap W=\emptyset$ then $O(z)=R_W(z)$. Otherwise $O(z)=\bigcup_{w\in O(z)\cap W}R_W(w)$.

*Proof.* The first case is immediate. In the second, let $y\in O(z)$ and $w_0\in O(z)\cap W$. Orbits are equivalence classes, since the generating set is closed under inverses, so there is a chain $w_0=z_0,\dots,z_L=y$. Let $i<L$ be its last index with $z_i\in W$ (or $i=L$ if $y=w_0$). Then $z_i\in O(z)\cap W$ and $y\in R_W(z_i)$. $\square$

**Lemma 5.2 (nested windows).** If $V\subseteq W$, then $|O(z)\cap W|\le\beta(V;W)\max(1,|O(z)\cap V|)$.

*Proof.* If $O(z)\cap V\neq\emptyset$, Lemma 5.1 for $V$ gives $O(z)\cap W\subseteq\bigcup_{v}(R_V(v)\cap W)$ over $v\in O(z)\cap V\subseteq W$. If $O(z)\cap V=\emptyset$ but $w\in O(z)\cap W$, then $O(z)=R_V(w)$. $\square$

**Theorem 5.3 (reduction).** Let $W_0\supseteq\dots\supseteq W_n$. For every $z$,
$$|O_r(z)|\le\beta(W_0)\prod_{i=1}^n\beta(W_i;W_{i-1})\cdot\max\big(1,\sup_x|O_r(x)\cap W_n|\big).$$
If the right-hand side is finite, $G(r)$ is finite.

*Proof.* Chain Lemma 5.1 with Lemma 5.2, and conclude by the uniform orbit bound. $\square$

The theorem holds for any finitely generated group of bijections. Its content is localization. $\beta(W_i;W_{i-1})$ depends only on the pseudogroup induced on $W_{i-1}$, restricted to chains avoiding $W_i$. The last factor depends only on the pseudogroup induced on $W_n$.

### 5.2 Monotonicity of restricted orbits

**Lemma 5.4.** For $r\le r'$ and every $W$, $R^{(r)}_W(x)\subseteq R^{(r')}_W(x)$. Hence $\beta^{(r)}(W)\le\beta^{(r')}(W)$ and $\beta^{(r)}(V;W)\le\beta^{(r')}(V;W)$.

*Proof.* Take an $r$-chain witnessing $y\in R^{(r)}_W(x)$ and delete its trivial steps. The remaining points are a subset of the original ones, so they still avoid $W$. Each remaining step applies $A^{\pm1}$ or $B^{\pm1}$ at a point of the closed disk of radius $r\le r'$, so it is also an $r'$-step (`boundary-contact.md` Lemmas 2.1, 2.3). For inverse letters this uses $a^{-1}=A^{-1}$ on $D_1$, which holds because $A(D_1)=D_1$, and likewise for $b^{-1}$. $\square$

**Theorem 5.5 (reduction to the critical radius).** For $r<r_c$ and $W_0\supseteq\dots\supseteq W_n$,
$$|O_r(z)|\le\beta^{(r_c)}(W_0)\prod_{i=1}^n\beta^{(r_c)}(W_i;W_{i-1})\cdot\max\big(1,\sup_x|O_r(x)\cap W_n|\big).$$

*Proof.* Theorem 5.3 and Lemma 5.4. $\square$

So **all dependence on $r$ is in the innermost (core) factor**. The bulk and annulus factors may be computed at $r_c$. There the group is infinite, but these factors can still be finite: the infinite orbits of Theorem A pass through every window about $p^\ast$, so they are cut by the windows.

### 5.3 Windows, zoom and the induction identity

Let $\Xi$ be the 32 critical points of Lemma 2.4, $Q=[-\kappa,\kappa]^2$, and $U_k=\bigcup_{\xi\in\Xi}(\xi+\varepsilon^kQ)$. The smallest sup-norm distance between two critical points is exactly $\varepsilon^2=3-2\sqrt2$, so the squares are pairwise disjoint if and only if $2\kappa\varepsilon^k<\varepsilon^2$. For $\kappa=1$ that means $k\ge3$; at $k=1,2$ they overlap.

Theorems 5.3 and 5.5 need only that the windows are nested, which holds for every $k$. The zoomed pseudogroups below need one window per critical point, so they are defined only for $k$ with $2\kappa\varepsilon^k<\varepsilon^2$; this is assumed from here on. For such $k$, zoom each component by $Z_k:x\mapsto\xi+\varepsilon^kx$, and let
$$\mathcal P_k(\theta)=Z_k^{-1}P(r,U_k)Z_k,\qquad\theta=\delta/\varepsilon^k,$$
where $P(r,U)$ is the induced pseudogroup on $U$.

A germ of $\mathcal P_k(\theta)$ from the window of $\xi$ to that of $\xi'$ is $x\mapsto\zeta^jx+\tau$ with $\varepsilon^k\tau=\zeta^j\xi+t-\xi'\in\mathbb Z[\zeta]$.

**Lemma 5.6 (induction identity; exact).** Let $\mathcal R$ restrict a pseudogroup on $Q$ to $\varepsilon^2Q$ (composites whose intermediate points stay in $Q$) and then zoom by $\varepsilon^{-2}$. Then $\mathcal R(\mathcal P_k(\theta))=\mathcal P_{k+2}(\theta/\varepsilon^2)$ for every $r$ and every $k$ with $2\kappa\varepsilon^k<\varepsilon^2$.

*Proof.* Cut a chain between two points of $U_{k+2}$ at its visits to $U_k\supseteq U_{k+2}$. Conversely, composites of germs of $P(r,U_k)$ are germs of chains. The zooms satisfy $Z_{k+2}=Z_k\circ(\varepsilon^2\cdot)$. $\square$

*Renormalization* means: at the same zoomed parameter $\theta$, the pseudogroups $\mathcal P_{k+2}(\theta)$ and $\mathcal P_k(\theta)$ are combinatorially the same (same germs, same cell structure), their domains differing only by the curvature correction $O(\varepsilon^k)$.

### 5.4 Where the intermediate radii and the curvature enter

Fix a phase $\theta_\ast\in\mathbb Q\setminus\mathbb Z$ and put $\lambda=\theta_\ast(3\sqrt2-2)$, $\delta_{(m)}=\lambda\varepsilon^m$ and $r_m^2=r_c^2-\delta_{(m)}$. (The factor $3\sqrt2-2$ makes $\theta_\ast$ the ratio $\delta_{(m)}/(\delta_m+\varepsilon^{2m})$ to the level spacing of Lemma 2.3.) At $r_m$ the window $U_m$ has zoomed parameter $\delta_{(m)}/\varepsilon^m=\lambda$.
- Only one sequence of radii is needed (monotonicity). By Theorem 5.5, the non-core factors are taken at $r_c$, and the core is the induced pseudogroup at the level scale, $\mathcal P_m(\lambda)$ at $r_m$.
- So **only one zoomed parameter $\lambda$ is involved for $r<r_c$**, together with $\theta=0$ at $r_c$. No uniformity over a level interval or over $\theta\to0$ is needed.
- Since $\theta_\ast\notin\mathbb Z$, there are no tangencies and no lattice points on circles at any $r_m$ (Lemma 2.2(4)).
- For a limiting line pseudogroup, whose offsets are affine in $\theta$, $\theta_\ast$ can also be chosen so that $\lambda$ avoids its finitely many events.

### 5.5 The remaining conjecture

**Conjecture S.** There are $\kappa\in(0,1]$, $k_1\ge1$ with $2\kappa\varepsilon^{k_1}<\varepsilon^2$, $m_0\ge k_1$ and $\theta_\ast\in\mathbb Q\setminus\mathbb Z$ such that the following hold, with $\lambda=\theta_\ast(3\sqrt2-2)$ and $r_m^2=r_c^2-\lambda\varepsilon^m$ as in §5.4.

- **(S1, critical radius only).** At $r=r_c$: $\beta(U_{k_1})<\infty$ and $\beta(U_{k_1+1})<\infty$, and $\beta(U_{k+2};U_k)<\infty$ for every $k\ge k_1$.
- **(S2, core renormalization).** For every $m\ge m_0+2$, $\mathcal P_m(\lambda)$ (at $r_m$) and $\mathcal P_{m-2}(\lambda)$ (at $r_{m-2}$) have the same maximal orbit size. This would follow from a combinatorial conjugacy, that is, an orbit-size-preserving bijection of orbits.
- **(base).** $G(r_{m_0})$ and $G(r_{m_0+1})$ are finite.

**Corollary 5.7 (proved).** Conjecture S implies F₈. Combined with Theorem A of `critical-radius-n8.md`, it implies that the critical radius of $GG_8$ is exactly $\sqrt{10-5\sqrt2}$.

*Proof.* By (S2) and (base), $\sup_x|O_{r_m}(x)\cap U_m|$ equals its value at level $m_0$ or $m_0+1$. That value is finite because those groups are finite: the orbits of $\mathcal P_k$ are the sets $O\cap U_k$, zoomed. Apply Theorem 5.5 with $W_i=U_{k_1'+2i}$, where $k_1'\in\{k_1,k_1+1\}$ has the parity of $m$, and $W_n=U_m$. All factors are finite by (S1). So $G(r_m)$ is finite for all $m\ge m_0$, and monotonicity gives F₈. $\square$

**The base is in reach.** With $\theta_\ast=4/5$ (the value used in §6.2 and §6.4, so $\lambda=0.8(3\sqrt2-2)$), the radii are $\delta=0.3078$, $0.1275$, $0.0528$ and $0.02188$ at $m=2,3,4,5$.
- $m=2,3$ satisfy $\delta\ge1/16$, so (base) would hold with $m_0=2$ by Theorem 3.1.
- $m=4$ lies inside the certified range ($0.0528>1/36$).
- $m=5$ lies beyond the $1/36$ certificate, since $0.02188<1/36$. A certificate just short of level 5 exists ([`../relative-certificates.md`](../relative-certificates.md) §7): a certificate at $\delta=547/25000=0.02188$, checked with (C1)–(C4). For $\theta_\ast=4/5$ exactly, $\lambda\varepsilon^5\approx0.0218762$ is slightly smaller, so it covers $r_5$ for $\theta_\ast\ge0.80014$ (e.g. $\theta_\ast=4001/5000$, for which $m=4$ is also certified). Nothing about Conjecture S itself follows.

The sampled core maxima (188, 224, 223 at $m=2,4,6$; §6.4) suggest that the core stabilizes only from $m=4$ on. If so, (S2) holds from $m_0+2$ with $m_0=4$, and the base needs levels 4 and 5. Level 4 is certified, and level 5 is certified in the sense of the previous item.

More generally, if a perturbation argument proves (S2) only from some $m_1$ on, the base has to reach $m_1$.

**What a proof of S needs.**
- **(S1)** is a statement about the critical system alone, so it is a natural target for an exact computation at $r_c$. One would need:
  - a *relative certificate* at $r_c$: a finite arc set closed under the dynamics outside the inner windows;
  - (R_c): the annulus pseudogroups at $r_c$ are combinatorially self-similar from window $k$ to $k+2$. This is the 2-D extension of the 31-word family of `critical-radius-n8.md` §2.

  Given (R_c), finiteness for two consecutive $k$ gives it for all $k$.
- **(S2)** concerns one parameter value. The expected route has three steps:
  - (R1) *limit*: $\mathcal P_m(\lambda)\to\mathcal P_\infty^{(m\bmod2)}(\lambda)$, a pseudogroup with polygonal domains, bounded by lines in the 8 critical directions and by images of $\partial Q$, with exactly the observed germs;
  - (R2) *genericity* of the two limit partitions at $\lambda$, with explicit margins. With 8 directions and offsets in $\mathbb Q(\sqrt2)$, this is a finite exact computation once the limits are written down;
  - (R3) a *perturbation lemma*: domains bounded by arcs of radius $\ge R$ that are $C^1$-close to a generic polygonal partition, with the same exact germs, have the same combinatorics once $1/R$ is below an explicit multiple of the margins.

  Combined, these give (S2) for $m\ge m_1$ with $m_1$ explicit. The base must then reach level $m_1$.

---

## 6. Evidence for the renormalization (floating-point sampling)

**Method.**
- A sample point $z$ is a generic complex number.
- Its orbit is computed exactly as a set of germs $(j,t)$, $t\in\mathbb Z[\zeta]$, standing for the point $\zeta^jz+t$ (`induced.py`). Only the disk tests are in double precision. The points are far from all circles, but no rounding bound was certified.
- All the orbits used closed.
- Induced germs at $p^\ast$ are the pairs $(j,\tau)$ with $\tau=\zeta^jp^\ast+t-p^\ast$ for the orbit points in the window.
- Sampling finds germs; it cannot exclude rare ones.

### 6.1 Sampled germ sets: agreement with period two

The window is the disc of radius $0.4\delta$ about $p^\ast$, and $\delta=0.8\,\delta_m$.

| $m$ | $\delta$ | samples | orbit size, median / max | distinct germs | mean germs per orbit |
|---|---|---|---|---|---|
| 2 | 0.2840 | 6 000 | 367 / 1 688 | 27 | 2.36 |
| 3 | 0.1235 | 3 000 | 1 748 / 8 874 | 23 | 1.96 |
| 4 | 0.0521 | 2 000 | 9 490 / 46 833 | 27 | 2.61 |
| 5 | 0.02176 | 300 | 53 844 / 256 990 | 21 | 2.19 |
| 6 | 0.00904 | 200 | 282 287 / 1 391 778 | 23 | 2.77 |

**Observation 6.1 (floating-point evidence; $G_m$ is the set of germs found in the samples).**
- $\{(j,\varepsilon^2\tau)\}$ over $G_2$ equals $G_4$: all 27 sampled germs, in both directions.
- $\varepsilon^2G_3$ (23 germs) and $G_5$ (21 germs) share 20 germs. The 3 germs of $\varepsilon^2G_3$ missing at $m=5$ each had frequency at most 1% at $m=3$, and $m=5$ had only 300 samples.
- With period one, $\tau\mapsto\varepsilon\tau$, only 10 germs match. No additional rotation or reflection about $p^\ast$ fixes this: the best of 16 such maps matches 16 germs.
- Orbit sizes grow by about $(1+\sqrt2)^2$ per level, while the number of visits to the window and the number of germs stay bounded.

### 6.2 Convergence of the zoomed partitions

Take 1 500 zoomed points $X$ in the unit disc, $z=p^\ast+\varepsilon^mX$ and $\delta=0.8(3\sqrt2-2)\varepsilon^m$. Record the normalized pattern $\{(j,\varepsilon^{-m}\tau)\}$ of each $X$ (`samex.py`, `agree.py`).

| levels | identical patterns at identical $X$ | germ sets |
|---|---|---|
| $2\to4$ | 82.8% (first 600; 81.7% over 1 500) | 40 / 42, all 40 common |
| $3\to5$ | 90.2% (first 600) | 38 / 38, identical |
| $4\to6$ | 95.0% (600) | 42 / 42, identical |
| $2\to3$, $3\to4$, $4\to5$ | 0% | 14 common |

The disagreement halves about every level, as expected if the boundaries move by the curvature correction. The two parity classes are distinct.

### 6.3 Boundary directions

At level 4 with a square window, `bdir.py` bisected 40 boundary points of the zoomed induced partition. Each boundary is one of two kinds:
- an image of the window's sides: direction $\equiv0\pmod{\pi/4}$, straight;
- an arc within $0.03$ rad of the critical directions $0.0709$ or $0.7144\pmod{\pi/4}$ of Lemma 2.4(4), with curvature consistent with radius $r\varepsilon^{-4}\approx57$.

No other direction occurred. With a disc window there are, in addition, arcs of radius about 1 in all directions: the images of the window circle.

So in the limit the induced partition should be polygonal, with lines in 8 directions only: those perpendicular to $u(2\pm i)(1-\zeta)$. The arcs of $K(r)$ itself near $p^\ast$ have all directions.

### 6.4 The factors of Theorem 5.5

Windows are squares with $\kappa=1$. Counts are sample maxima. At $\kappa=1$ the squares of $U_2$ overlap (§5.3), so the annulus rows that use $U_2$ refer to the union $U_2$, not to 32 separate windows. This does not affect the definitions of $R_W$ and $\beta$, which need only sets.

| quantity | $m=2$ | $m=3$ | $m=4$ | $m=5$ | $m=6$ | $m=8$ | $r_c$ |
|---|---|---|---|---|---|---|---|
| bulk $\lvert R_{U_3}(x)\rvert$ | 547 | 8 704 | 9 833 | 33 582 | 41 721 | | 43 842 |
| annulus $\lvert R_{U_4}(x)\cap U_2\rvert$, $x\in U_2$ | | | 6 060 | | 30 558 | | 99 409 |
| renormalized annulus $(m,k)=(6,4)$ | | | | | 4 172 | | |
| core $\lvert O(z)\cap U_m\rvert$ | 188 | | 224 | | 223 | | (infinite) |

Sample sizes:
- bulk: 12 random starting points at $m=2$ (`probe_rc.py`); 100 at $m=3,4,5$; 60 at $m=6$; at $r_c$, the same 12 random points plus 54 points near $p^\ast$ (`deep.py`);
- annuli: 193, 39 and 39;
- core: 300, 200 and 40.

- **Monotone convergence to $r_c$ values** (Lemma 5.4). The fixed-window factors increase with $m$, and the same starting points at $r_c$ give finite values. For 12 random starting points, the restricted sizes at $m=2,4,6$ and at $r_c$ are 362 / 1 896 / 39 683 / 41 774, 547 / 1 902 / 16 203 / 37 947, and so on.
- **Independence of depth at $r_c$.** Starting points $p^\ast+\varepsilon^ju$ for $j=3,\dots,11$ (6 each) give $|R_{U_3}|$ in the set $\{2\,000;\,5\,852;\,10\,196$–$10\,925;\,37\,878$–$37\,947;\,41\,774$–$43\,842\}$, at every depth. This is consistent with $\beta^{(r_c)}(U_3)<\infty$ in (S1), and with the critical system being self-similar.
- **Renormalized pairs agree.** Annulus $(6,4)$ gives 4 172, against 6 060 for $(4,2)$. The core stays at 188, 224, 223 for $m=2,4,6$, as (S2) predicts.
- **Which classes are active.** Orbits of random points visit discs of radius $0.05$ about all 8 critical classes from $m=3$ on (3 classes at $m=2$). Orbits that avoid all 32 discs have at most 1 688, 1 784, 432, 1 784, 432 points at $m=2,\dots,6$.
- **Not tested.** $\beta^{(r_c)}(U_{k+2};U_k)$ for $k\ge3$. One annulus run at $r_c$ with $k=3$ reached the cap of $3\cdot10^6$ points. That is not evidence of an infinite orbit: by Lemma 5.2 the full restricted orbit can be as large as the product of the bulk and annulus factors, about $10^9$. Counting only the annulus points would need an induced-pseudogroup implementation, which was not written.

---

## 7. Status and gaps

| claim | status |
|---|---|
| Lemma 2.1 (centres in $1+2\mathbb Z[\zeta]$); Lemma 2.2 (no tangency or lattice points on circles on the families used) | **proved**; referee: correct, recomputed |
| Lemma 2.3 (levels; scaling $\delta\asymp\varepsilon^m$, zoom $\varepsilon^{-m}$) | **proved**; referee: correct, identity recomputed for $m\le12$ |
| Lemma 2.4 (32 critical points, 8 classes, tangency circles, 16 normal directions) | **proved**; referee: correct, all recomputed exactly |
| Proposition 2.5 (physical isometries among the lattice affine maps are internal isometries) | **proved**; referee: correct but weak, now stated with its premise |
| Finiteness up to $\delta=1/36$ ($r_\ast\approx1.703278$; Theorem 3.1) | **proved modulo the exact computation recorded in `../certificates.md`** |
| Finiteness up to $\delta=1/35$, and up to $1/16$ (Table 3.1) | **proved modulo the exact computation**; consistent with and implied by the $1/36$ record. Referee: re-ran `check-certificate` on the $1/35$ and $1/16$ files, both VALID. $1/16$ is also VALID under `verify.py` (not re-run by the referee) |
| Lemmas 5.1, 5.2, Theorem 5.3, Lemma 5.4, Theorem 5.5 | **proved**; referee: correct line by line, and general in $n$ |
| Lemma 5.6; the window condition $2\kappa\varepsilon^k<\varepsilon^2$ in §5.3 and Conjecture S | **proved**; the window condition is not yet refereed |
| Corollary 5.7 (S ⇒ F₈) | **proved**; referee: correct, given the consistent notation $\lambda$ of §5.4 |
| Stable limit of $K(r)$ at $p^\ast$ (the literal strategy) | **fails** (evidence, §4) |
| Period-2 agreement of sampled germ sets ($2\to4$: 27/27; $3\to5$: 20 of 23); convergence of the zoomed induced partitions; 8 limit directions; bounded core; finite bulk factor at $r_c$ | **evidence** (§6; floating-point sampling); not checked by the referee |
| Conjecture S, hence F₈ | **open** |

**Gaps.**
1. **Conjecture S is the gap.** Its parts:
   - (S1) needs a relative certificate at $r_c$ and the exact self-similarity of the critical annulus pseudogroups. Neither was attempted.
   - (S2) needs the two limit polygonal pseudogroups written down explicitly, from the active constraints of each germ's realizing word, together with an exact genericity check and a perturbation lemma. Not done.
   - The base must reach the perturbation threshold $m_1$, which is unknown.
2. **Section 6 uses floating-point disk tests and samples.** Germ sets may miss rare germs. No proof step rests on §6.
3. **Independent checking.**
   - The $1/16$ certificate was checked by the engine's exact checker, which shares the exact field layer with the generator, and by the unrelated Python verifier; both VALID.
   - The $1/20$, $1/35$ and $1/36$ certificates were checked by the engine's checker only. The referee re-ran it on $1/35$ and $1/16$.
   - The correctness of the Lean engine itself rests on `../certificates.md` §7 and its referee report.
   - The note has been refereed (`referee-report-sharp-lower-bounds.md`). The referee did **not** check: the floating-point experiments of §§4 and 6; `verify.py` on the $1/16$ certificate; the $1/20$ certificate; the regeneration of the $1/36$ certificate; the Lean engine's own correctness; or whether Conjecture S is plausible. In particular, (S1) at $r_c$ could fail if $r_c$ has infinite orbits that avoid all critical windows. Nothing here rules that out.
4. **Where structure is born.** It is assumed, not proved, that the 32 lattice points of Lemma 2.4 are the only places where structure is born. Evidence: the level-4 jump is born within $0.31\delta$ of them (§3); orbits avoiding them stay small (§6.4); the bulk factor at $r_c$ is finite in every sample.

---

## 8. What transfers to $n=5,10,12$

- **Section 5 is general:** Lemmas 5.1, 5.2, 5.4, 5.6 and Theorems 5.3, 5.5 hold for every $n$, and for any nested windows. So F₅, F₁₀ and F₁₂ each reduce to the corresponding Conjecture S: a statement at $r_c$ plus an exact core renormalization at one phase.
- **Lemma 2.1** transfers to the coset of $\pm1$ under $\Gamma$. **Lemma 2.2** transfers: tangency requires $r^2$ to be a norm. For $n=5$ this sharpens the "$4\rho_k\notin\mathbb Z[\varphi]$" remark of `critical-radius-n5.md` §6.
- **Lemma 2.4** becomes a norm equation for the critical points and their normal directions. **Proposition 2.5** holds verbatim.
- **The §4 test should be repeated.** The prediction is that $K(r)$ has no local limit for any $n$.
- **The §6 programs** use only $\mathbb Z[\zeta]$ arithmetic with $\zeta^4=-1$. Porting them means changing the reduction rule, the critical points and the unit. The period of the germ recursion must be measured. For $n=8$ it is two levels ($\varepsilon^2$), even though the orbit-of-0 thresholds jump once per factor $1+\sqrt2$.
- **The certificates** of §3 come from the repository engine, which handles $n=5,8,10,12$. Certified ranges for every $n$ are those recorded in `../certificates.md`.

---

## Appendix A. Data and reproduction

The programs and outputs are in the session scratch directory `sharp8/`, not in this repository. The engine is `.lake/build/bin/tdcsg-orbit`, run read-only.

**Proof-relevant commands.**
- `tdcsg-orbit certify -n 8 --r2 closed-1/16 --out c8_1_16.txt --max-pieces 400000000`, then `tdcsg-orbit check-certificate c8_1_16.txt`, which reports VALID. The file has 882 708 `arc` records and 2 `full` records.
- `python3 -I exact/conv.py c8_1_16.txt exact/c8_1_16.pkl`, then `python3 -I exact/verify.py exact/c8_1_16.pkl`. The same pipeline at $1/7$ gives VALID.
- `runlevels.sh 1/35` generates and checks $\delta=1/35$.
- `exactlemmas.py` checks Lemmas 2.1, 2.3 ($m\le12$) and 2.4.

**Evidence programs.**
- `near.py`, `counts.py`, `zoom.py`, `generic.py`: §4.
- `fill.py`, `window.py`: the window of the centre set.
- `scan.sh`, `bisect.sh`, `newcirc.py`: the step table and the level-4 jump.
- `induced.py`, `rec.py`, `cmpgerms.py`: §6.1.
- `samex.py`, `agree.py`: §6.2.
- `bdir.py`: §6.3.
- `bulk.py`, `annulus.py`, `probe.py`, `probe_rc.py`, `deep.py`, `capprobe.py`, `capgrow.py`: §6.4.

Random seeds are fixed in each program.

**Orbit-of-0 thresholds.** `tdcsg-orbit thresholds -n 8 --from closed-0.2 --upto closed-0.025 --rc closed --unit fund` gives 15 thresholds. The large jumps are at $693-488\sqrt2=r_c^2-\delta_4$ and $3117-2202\sqrt2=r_c^2-\delta_5$.

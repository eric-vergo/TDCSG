# The regularity scale of a two-disk system

Authors: Eric Vergo, Claude

**Statement.** Let $n=5$ or $n\ge 7$. Consider functions on $\Omega_r=D_1\cup D_2$ (open disks of
radius $r$ about $\mp1$) that are invariant under the $-2\pi/n$ rotation of each disk. For a class
$\mathcal C$ of functions, let $r_{\mathcal C}(n)$ be the radius beyond which every invariant function
in $\mathcal C$ is constant. Then:

1. **Unique continuation gives threshold $r_A$.** Every motion-invariant class of continuous
   functions that contains the constants and the real-analytic functions, and has unique continuation
   from open sets, has threshold $r_{\mathcal C}(n)=r_A(n)=\sec(\pi/n)$. This covers every
   quasi-analytic Denjoy–Carleman class containing $C^\omega$. Smaller quasi-analytic classes can have
   a smaller threshold (Remark 3.4).
2. **Bump functions give a much larger threshold.** This covers every non-quasi-analytic
   Denjoy–Carleman class, the Gevrey classes, $C^\infty$, $C^k$, Hölder, Sobolev and continuous
   functions, and $L^p$ and measurable functions taken modulo null sets. Their thresholds satisfy
   $$
   \max\bigl(2,\ d_n\bigr)\ \le\ r_{\mathcal C}(n)\ \le\ R_{\rm erg}(n)<\infty,\qquad
   d_n=\sqrt{\sec^2\tfrac{\pi}{n}+16\sin^2\tfrac{\pi}{n}} .
   $$
   The lower bound comes from two explicit families of periodic islands. The upper bound is the radius
   above which the action is ergodic.
3. **The scale jumps at the quasi-analyticity boundary.** On the whole interval
   $r_A<r<\max(2,d_n)$, a log-convex Denjoy–Carleman class has only constant invariants **if and only
   if it is quasi-analytic**. So no continuum of thresholds fills $(r_A,\max(2,d_n))$.
   - That this interval contains $(r_A,r_c)$, so that the bump thresholds lie above $r_c$, needs
     $r_c(n)\le\max(2,d_n)$.
   - For $n=5$ this is proved, since `critical-radius-n5.md` (Theorem A) proves
     $r_c(5)\le\sqrt{3+\varphi}=2.149<d_5$.
   - For $n=8,10,12$ it is also proved: `critical-radius-n8.md`, `critical-radius-n10.md` and
     `critical-radius-n12.md` (Theorem A, also proved in Lean as
     `TDCSG.CriticalRadius.criticalRadius_eight_le` and its analogues) give $r_c(n)<2$.
   - For the other $n$ it rests on the paper's computed table of $r_c$.
4. **For $n=5$ the window is narrow.** All bump-class thresholds lie in
   $[\,2\sqrt{4-\sqrt5},\ 3.662\,]=[2.656,\,3.662]$, while $r_A=1.236$ and $r_c(5)\le2.149$.
   - The exact value $r_c(5)=\sqrt{3+\varphi}$ is proved, with finiteness below it in
     [`sharp-lower-bound-n5-pentagrid.md`](sharp-lower-bound-n5-pentagrid.md) (machine-checked).
     Weaker lower bounds are proved modulo computations: $r_c(5)\ge2.12557$ by the refereed
     Theorem B of `critical-radius-n5.md`, and $r_c(5)\ge2.144727$ by the certificate recorded in
     [`../certificates.md`](../certificates.md).
   - Nothing below uses the lower bound.

So, for the classes treated here (classes with unique continuation, Denjoy–Carleman classes and bump
classes), $r_c(n)$ is not a rigidity threshold. The other characterization that $r_A$ has, besides
being the analytic threshold, is the radius where the orbit space stops being Hausdorff (§8).

**Status.**
- **Proved here, without caveat:**
  - item 1;
  - the dichotomy on $(r_A,\max(2,d_n))$ of item 3: there are non-constant smooth, and even Gevrey,
    invariants for every $r<\max(2,d_n)$;
  - the general upper bound $R_{\rm erg}(n)$ of item 2.

  The proofs use Theorems 4.1 and 8.1 of [`analytic-radius.md`](analytic-radius.md), which are refereed.
- **Proved by exact computation**, and reproduced independently by the referee: the upper bound
  $3.662$ of item 4. The certificate is a finite orbit computation in $\mathbb Z[\zeta_5]$, with every
  disk test decided exactly in $\mathbb Q(\sqrt5)$; it is described in §5.3.
- **[computed]** (floating point): the upper bounds for $n=7,8,10,12$ (§5.3), and the comparison with
  $r_c$ for $n\notin\{5,8,10,12\}$.
- **[conjecture]**: all bump classes have the same threshold, equal to $\max(2,d_n)$, the radius where
  the last explicit island dies (§6).
- **Refereeing.** The note has been independently refereed; the report is
  [`referee-report-regularity-scale.md`](referee-report-regularity-scale.md), and §9 records its
  verdicts. Two arguments were completed after the report and have not yet been refereed:
  - the proof that a.e.-invariance and everywhere-invariance agree (Lemma 1.3);
  - the extension of the non-Hausdorff statement to every $r>r_A$ (Proposition 8.2).

---

## 0. Results

1. **[proved]** (Lemma 2.1, *descent*) For $r>\sec(\pi/n)$ and every $K\in(\sec(\pi/n),r)$, every
   pseudogroup orbit meets $D(-1,K)\cup D(1,K)$.
2. **[proved]** (Proposition 2.2) For every class closed under restriction, the set of radii at which
   the class is rigid is an up-set in $(r_A,\infty)$. So $r_{\mathcal C}$ is a genuine threshold.
3. **[proved]** (Theorem 3.1) Let $\mathcal C$ be a class of continuous functions that contains the
   constants, has unique continuation from open sets, and is invariant under Euclidean motions. Then
   every invariant $f\in\mathcal C(\Omega_r)$ is constant for $r>r_A$. If also
   $\mathcal C\supseteq C^\omega$, then $r_{\mathcal C}=r_A$. Quasi-analytic Denjoy–Carleman classes
   qualify (Proposition 3.2).
4. **[proved]** (Lemma 4.1, Theorems 4.3–4.4, Proposition 4.2) A finite pseudogroup orbit that avoids
   the two circles is surrounded by an invariant island. Such islands exist:
   - for almost every point when $GG_n(r)$ is finite, i.e. for $r<r_c$;
   - on the *necklace orbit*, with $2n-2$ points, for $r_A<r<d_n$;
   - near the centres for $0<r<2$.

   So every bump class is non-rigid for $r<\max(2,d_n)$. Whether $d_n>r_c$ is proved for $n=5$ and
   computed for the other $n$.
5. **[proved]** (Theorem 5.2, Corollary 5.3) For
   $r>R_{\rm erg}(n)=\sec\frac{\pi}{n}+\max(2,4\sin\frac{\pi}{n})+16\sin\frac{\pi}{n}$, the
   pseudogroup acts ergodically. So every class contained in $C^0$, and every class of measurable
   functions taken modulo null sets, is rigid there. For $n=5$ the same holds for $r>3.662$
   [proved by exact computation].
6. **[proved]** (Theorem 4.5) The dichotomy of item 3 of the statement.
7. **[proved]** (§7c) A single round of analytic continuation already gives the intermediate
   pseudogroup $H^{(1)}_r$ infinite, dense orbits at every $r>r_A$, for $n\ge63$. So the
   intermediate pseudogroups do not interpolate either.
8. **[proved]** (Proposition 8.2) $\Omega_r/P_r$ is Hausdorff for $0<r\le r_A$ and not Hausdorff for
   every $r>r_A$. The case $r>r_A$ in this generality is not yet refereed: the referee checked it on
   $(r_A,r_c)$ and above $R_{\rm erg}$ and suggested the general argument.
9. **[proved]** (Proposition 8.3) For $r<r_c$, invariant smooth functions separate almost every orbit
   from every other orbit. That this fails just above $r_c$ is a **[conjecture]**.

---

## 1. Setting and definitions

Notation follows [`analytic-radius.md`](analytic-radius.md) (cited below as AR).
- $\zeta=e^{2\pi i/n}$, $A(z)=\zeta^{-1}(z+1)-1$, $B(z)=\zeta^{-1}(z-1)+1$.
- $D_1=D(-1,r)$, $D_2=D(1,r)$ are open, and $\Omega_r=D_1\cup D_2$.
- $t=2(\zeta-1)$, so that $A^{-1}B=\tau_t$, where $\tau_s(z)=z+s$; and $|t|=4\sin(\pi/n)$.
- $r_A=\sec(\pi/n)$, and $\Lambda=t\,\mathbb Z[\zeta]$, which is dense in $\mathbb C$ for
  $n\notin\{1,2,3,4,6\}$.
- The map $z\mapsto-z$ exchanges $D_1$ and $D_2$ and conjugates $A$ to $B$, since $-A(-z)=B(z)$. All
  statements below are symmetric under it.

**Definition 1.1.**
1. **Classes.** A *class* $\mathcal C$ assigns to each open $U\subset\mathbb C$ a real vector space
   $\mathcal C(U)$ of real functions on $U$. Throughout, a class is either contained in $C^0$, or
   consists of measurable functions taken modulo null sets.
   - Without this restriction rigidity can fail at every $r$. For example, the indicator of a single
     orbit is a non-constant Borel invariant, since orbits are countable.
2. **Invariant functions.** $f\in\mathcal C(\Omega_r)$ is *invariant* if $f\circ A=f$ on $D_1$ and
   $f\circ B=f$ on $D_2$. For measurable classes the two notions below agree, by Lemma 1.3:
   - some representative satisfies both identities everywhere;
   - $f$ satisfies both identities almost everywhere.
3. **Rigidity.** $\mathcal C$ is *rigid at $r$* if every invariant $f\in\mathcal C(\Omega_r)$ is
   constant (a.e. constant, for measurable classes). Let
   $\mathcal R_{\mathcal C}=\{r>0:\mathcal C\text{ rigid at }r\}$ and
   $r_{\mathcal C}(n)=\inf\mathcal R_{\mathcal C}$.
4. **Pseudogroup.** $P_r$ is the pseudogroup generated by $A|_{D_1}$ and $B|_{D_2}$ (AR, Definition 3.4).
   An *$r$-chain* is a sequence $z_0,\dots,z_m$ in which each $z_i=A^{\pm1}z_{i-1}$ with
   $z_{i-1}\in D_1$, or $z_i=B^{\pm1}z_{i-1}$ with $z_{i-1}\in D_2$. The $P_r$-orbit $O_r(z)$ is the set
   of endpoints of $r$-chains from $z$.

**Lemma 1.2 (orbits)** [proved].
1. A function $f$ on $\Omega_r$ is invariant if and only if it is constant on every $P_r$-orbit.
   No regularity is involved.
2. $O_r(z)$ is the orbit of $z$ under the piecewise group generated by the open-disk rotations,
   i.e. $GG_n(r)$ with open disks.
3. Write $O^{\rm cl}_r(z)$ for the orbit under $GG_n(r)$ with closed disks. Then
   $O_r(z)\subseteq O^{\rm cl}_r(z)\subseteq O_{r'}(z)$ for every $r'>r$.
4. If $O^{\rm cl}_r(z)$ avoids $\partial D_1\cup\partial D_2$, then $O_r(z)=O^{\rm cl}_r(z)$.

*Proof.*
1. If $f$ is invariant and $z_i=A^{\pm1}z_{i-1}$ with $z_{i-1}\in D_1$, then $f(z_i)=f(z_{i-1})$,
   and likewise for $B$; so $f$ is constant along chains. Conversely, $Az\in O_r(z)$ for $z\in D_1$.
2. This is the chain description of orbits (`boundary-contact.md`, Lemma 2.3 and §6).
3. An open chain is a closed chain. A closed chain at $r$, with its trivial steps deleted, is an open
   chain at $r'$, because $|z-c|\le r<r'$.
4. Every non-trivial step of a closed chain inside $O^{\rm cl}_r(z)$ starts at a point with
   $|z-c|\le r$. By hypothesis $|z-c|\ne r$, so the step is an open step. ∎

So the pseudogroup orbits off the boundary circles are exactly the $GG_n(r)$-orbits. Two consequences:
- the infimum of the radii with an infinite orbit is the same for open and closed disks;
- the supremum of the radii with a finite group is the same for open and closed disks (by
  `boundary-contact.md`, Proposition 3.3).

So $r_c$ can be read through either convention.

**Lemma 1.3 (a.e. invariance)** [proved; not yet refereed, following the referee's suggestion].
Let $f$ be measurable on $\Omega_r$ with $f\circ A=f$ a.e. on $D_1$ and $f\circ B=f$ a.e. on $D_2$.
Then $f$ agrees a.e. with an everywhere-invariant function. Hence $P_r$ is ergodic in the usual sense
(every a.e.-invariant measurable set is null or conull) iff every everywhere-invariant measurable
function is a.e. constant.

*Proof.*
1. **The bad set.** Let $E=\{z\in D_1:f(Az)\ne f(z)\}\cup\{z\in D_2:f(Bz)\ne f(z)\}$. It is null.
2. **Its saturation is null.** The saturation $\hat E=\bigcup_w w(E\cap{\rm Dom}(w))$, over the
   countably many words $w$, is a countable union of isometric images of null sets, so it is null.
   It is $P_r$-invariant by construction.
3. **The modified function.** Put $\tilde f=f$ off $\hat E$ and $\tilde f=0$ on $\hat E$. Take
   $z\in D_1$:
   - if $z\in\hat E$, then $Az\in\hat E$, and both values of $\tilde f$ are $0$;
   - otherwise $z\notin E$ and $Az\notin\hat E$, so $\tilde f(Az)=f(Az)=f(z)=\tilde f(z)$.

   The case of $B$ is the same.
4. **Ergodicity.** Apply this to indicators for one direction. For the other, apply it to the level
   sets $\{f>a\}$, $a\in\mathbb Q$. ∎

---

## 2. Descent to the centres, and monotonicity

**Lemma 2.1 (descent)** [proved]. Let $n\ge 5$, $c=\cos(\pi/n)$, $r>\sec(\pi/n)$ and
$K\in(\sec(\pi/n),r)$. Then every $P_r$-orbit contains a point of $D(-1,K)\cup D(1,K)$. More
precisely, for each $z\in\Omega_r$ there is a word $w$ with $z\in{\rm Dom}(w)$ and
$w(z)\in D(\pm1,K)$.

*Proof.*
1. Let $F(\rho)=\sqrt{\rho^2-4\rho c+4}$. Then $F(\rho)^2=(\rho-2c)^2+4\sin^2(\pi/n)$, so
   $F(\rho)>|\rho-2c|$.
2. Also $F(\rho)^2-\rho^2=4(1-\rho c)$, so $F(\rho)<\rho$ exactly when $\rho>1/c=\sec(\pi/n)$.
3. $\frac{d}{d\rho}(\rho-F(\rho))=1-(\rho-2c)/F(\rho)>0$. Hence $\rho-F(\rho)\ge\delta:=K-F(K)>0$ for
   all $\rho\ge K$.
4. Let $z\in D_1$ with $\rho=|z+1|>K$. The $n$ points $A^kz$ lie on the circle of radius $\rho$ about
   $-1$, at equally spaced angles. So one of them, $z'$, makes an angle at most $\pi/n$ with the
   direction from $-1$ to $1$. Then $|z'-1|^2\le\rho^2-4\rho\cos(\pi/n)+4$, i.e.
   $|z'-1|\le F(\rho)\le\rho-\delta<r$. So $z'\in D_2$, and $z'$ is at distance at most $\rho-\delta$
   from $+1$.
5. By the symmetry $z\mapsto-z$, the same step applies with the roles of the disks exchanged.
6. Run steps 3–4 with some $K_1\in(\sec(\pi/n),K)$ in place of $K$. Alternating, the distance to the
   current centre drops by at least $K_1-F(K_1)>0$ at each step while it exceeds $K_1$. It starts
   below $r$, so after finitely many steps it is at most $K_1<K$. The point then lies in the open disk
   $D(\pm1,K)$. Each step is a power of one generator applied inside its own open disk, so it is
   realized by a word. ∎

The fixed point of $F$ is the necklace radius $\sec(\pi/n)$. This is the same triangle as in AR,
Lemma 1.2. Above $r_A$, every orbit is pulled into the necklace disks around the centres.

**Proposition 2.2 (monotonicity)** [proved]. Let $n=5$ or $n\ge7$. Let $\mathcal C$ be closed under
restriction to open subsets, and let $r_A<r<r'$. If $\mathcal C$ is rigid at $r$, it is rigid at $r'$.
If moreover $\mathcal C\supseteq C^\omega$, then $\mathcal C$ is not rigid at any $r\le r_A$. So
$\mathcal R_{\mathcal C}$ is $(r_{\mathcal C},\infty)$ or $[r_{\mathcal C},\infty)$, and
$r_{\mathcal C}\ge r_A$.

*Proof.*
1. Let $f\in\mathcal C(\Omega_{r'})$ be invariant. Since $D_k(r)\subset D_k(r')$, the restriction
   $f|_{\Omega_r}$ is invariant, so it equals a constant $c$ (a.e., for measurable classes).
2. Fix $K\in(r_A,r)$. By Lemma 2.1 at radius $r'$, each $z\in\Omega_{r'}$ lies in an open set
   $V_w=\{z\in{\rm Dom}(w):w(z)\in D(\pm1,K)\}$ for some word $w$.
3. On $V_w$, $f=f\circ w$ by Lemma 1.2, and $w$ maps $V_w$ isometrically into
   $D(\pm1,K)\subset\Omega_r$, where $f=c$.
4. There are countably many words, so $f=c$ on $\Omega_{r'}$ (a.e. in the measurable case, since
   isometries preserve null sets).
5. For $r\le r_A$: when $r\le1$, $\Omega_r$ is disconnected and locally constant functions suffice.
   When $1<r\le r_A$, the real part of the holomorphic invariant of AR, §5, is a non-constant
   real-analytic invariant. ∎

So, unlike the naive restriction argument (which loses non-constancy for non-quasi-analytic
classes), monotonicity holds for every class closed under restriction. The reason is dynamical, not
function-theoretic.

---

## 3. Quasi-analytic classes: the threshold is $r_A$

**Theorem 3.1** [proved]. Let $n=5$ or $n\ge7$, and let $\mathcal C$ be a class of continuous
functions such that:
- **(C0)** it contains the constants;
- **(C1)** it is closed under restriction to open subsets;
- **(C2)** it is closed under composition with orientation-preserving Euclidean motions, i.e.
  $f\in\mathcal C(U)\Rightarrow f\circ\gamma\in\mathcal C(\gamma^{-1}U)$;
- **(C3)** it has unique continuation from open sets: if $U$ is connected, $f\in\mathcal C(U)$ and $f$
  vanishes on a non-empty open subset, then $f\equiv0$.

Then for every $r>r_A$, every invariant $f\in\mathcal C(\Omega_r)$ is constant. If moreover
- **(C4)** $\mathcal C\supseteq C^\omega$,

then $r_{\mathcal C}(n)=r_A(n)=\sec(\pi/n)$, and $\mathcal R_{\mathcal C}=(r_A,\infty)$.

*Proof.*
1. **$f$ is invariant under the analytic hull $H_r$ (AR, Definition 3.4).** On $P_r$-domains,
   $f\circ\gamma=f$ by Lemma 1.2. Composition and inverses preserve such identities pointwise.
2. **Extension step.** Suppose $f\circ\gamma=f$ on an open $U_\gamma$, and let $C$ be a component of
   $\Omega_r\cap\gamma^{-1}\Omega_r$ meeting $U_\gamma$. Then $f\circ\gamma-f\in\mathcal C(C)$ by (C1),
   (C2) and linearity. It vanishes on the non-empty open set $C\cap U_\gamma$, hence on $C$ by (C3).
3. **Dense translations.** By AR, Theorem 8.1(2), whose proof uses only hull operations and never $f$,
   there is $\varepsilon\in(0,r/8)$ such that $f(z+s)=f(z)$ on $D_1\cap(D_1-s)$ for a dense set of
   $s\in D(0,\varepsilon)$.
4. **Constancy on a disk.** Let $z,w\in D(-1,r/4)$ with $|w-z|<\varepsilon$. Choose such $s_k\to w-z$.
   Then $z+s_k\in D(-1,3r/8)$, so $f(w)=\lim f(z+s_k)=f(z)$ by continuity. Hence $f$ is locally
   constant, and so constant, on the disk $D(-1,r/4)$.
5. **Constancy everywhere.** By (C0), $f-c\in\mathcal C(\Omega_r)$. It vanishes on an open set, so
   $f\equiv c$ on the connected $\Omega_r$ by (C3).
6. **The threshold.** Under (C4), Proposition 2.2 gives non-rigidity for $r\le r_A$. ∎

**What the argument needs.**
- Unique continuation **from an open set**, applied on connected unions of atoms and on $\Omega_r$.
  Unique continuation from the $\infty$-jet at a point is stronger and is not needed.
- Invariance under the motions $z\mapsto\zeta^jz+\tau$ only. General affine maps are not needed.
- Continuity, used in step 4.
- No derivatives. Step 4 replaces AR, Lemma 6.1, which differentiated. So closure of $\mathcal C$ under
  differentiation is not needed.

**Proposition 3.2 (Denjoy–Carleman classes).** Let $M=(M_k)$ be log-convex with $M_0=1$. Let
$C\{M\}(U)$ be the Roumieu class: smooth $f$ such that for each compact $K\subset U$ there are
$C,\rho$ with $\sup_K|\partial^\alpha f|\le C\rho^{|\alpha|}M_{|\alpha|}$ for all $\alpha$ (no
factorial; this is Rudin's convention).
1. **[proved]** $C\{M\}$ satisfies (C1) and (C2).
2. **[classical, confirmed]** (Denjoy–Carleman) The one-variable class $C\{M\}$ on an interval is
   quasi-analytic, i.e. a function all of whose derivatives vanish at a point vanishes identically,
   iff $\sum M_k/M_{k+1}=\infty$. If the sum converges, there are non-zero compactly supported
   functions in $C\{M\}(\mathbb R)$. See Rudin, *Real and Complex Analysis*, Theorem 19.11, and, for
   the compactly supported functions, Hörmander, *The Analysis of Linear Partial Differential
   Operators I*, Theorem 1.3.8. The theorem numbers are as given by the referee and have not been
   checked against the books.
3. **[proved from 2]** If $\sum M_k/M_{k+1}=\infty$, then $C\{M\}(U)$ satisfies (C3) on connected
   open $U\subset\mathbb R^2$.
4. **[proved]** (C4) holds iff $\inf_k(M_k/k!)^{1/k}>0$.

*Proof.*
1. **(C0) and (C1)** are clear.
2. **(C2), translations** do not change derivatives.
3. **(C2), rotations.** For a rotation $R$, $D^k(f\circ R)(e_{i_1},\dots,e_{i_k})=D^kf(Re_{i_1},\dots,Re_{i_k})$.
   Expanding each $Re_i$ in the standard basis gives at most $2^k$ terms, each bounded by
   $\max_{|\beta|=k}|\partial^\beta f|$. So $f\circ R\in C\{M\}$ with $\rho$ replaced by $2\rho$.
4. **(C3).** Suppose $f$ vanishes on an open set, and let $Z$ be the set of points where all
   derivatives of $f$ vanish. $Z$ is closed and non-empty. It is also open:
   - let $p\in Z$, let $\bar B(p,\delta)\subset U$, and let $v$ be a unit vector;
   - put $g(\tau)=f(p+\tau v)$. Then
     $|g^{(k)}|=\big|\sum_{|\alpha|=k}\tfrac{k!}{\alpha!}v^\alpha\partial^\alpha f\big|\le(\sqrt2)^k C\rho^kM_k$;
   - so $g$ lies in the one-variable class and is flat at $0$. Hence $g\equiv0$, so $f=0$ on
     $B(p,\delta)$, and $B(p,\delta)\subset Z$.

   Since $U$ is connected, $Z=U$.
5. **(C4).** A real-analytic function satisfies $|\partial^\alpha f|\le C\rho^kk!$ on compacts, and
   functions such as $1/(1-x)$ show that $k!$ growth is needed. ∎

**Corollary 3.3** [proved]. Every quasi-analytic Denjoy–Carleman class containing $C^\omega$ has
$r_{\mathcal C}(n)=\sec(\pi/n)$. Examples are $M_k=k!$, $M_k=k!(\log(k+e))^k$, and
$M_k=k!\prod_{j\le k}\log(j+e)$. The same conclusion holds for every class satisfying (C0)–(C4).
For the real-analytic class it is AR, Theorem 4.1, which also covers the harmonic and holomorphic
classes; those two satisfy (C1)–(C3) but not (C4), and are handled there directly.

**Remark 3.4 (classes below $C^\omega$)** [proved]. Without (C4) the threshold can be smaller. Take
$M_k\equiv1$, which is quasi-analytic.
1. For $f\in C\{1\}(\Omega_r)$, the Taylor series at any point converges on all of $\mathbb R^2$, and
   it equals $f$ near that point. So $f$ extends to a real-analytic $g$ on $\mathbb R^2$.
2. If $f$ is invariant, then $g\circ A-g$ vanishes on $D_1$, hence everywhere, and likewise for $B$.
   So $g$ is $\Gamma$-invariant, hence constant, because $\Gamma$ contains the dense translation group
   $T$.
3. So $r_{C\{1\}}=1$. The same holds for polynomials.

Inside the quasi-analytic world, then, the threshold moves only when the class is too small to contain
the Behnke–Stein invariants. For every class satisfying (C0)–(C4) it is $r_A$.

---

## 4. Classes with bump functions: islands

**Definition 4.0.** A class is a *bump class* if:
- it satisfies (C1) and (C2);
- it is local: a function that agrees near each point with a member of the class is a member;
- for some $\delta_0>0$ and every $\delta\in(0,\delta_0)$, $\mathcal C(\mathbb C)$ contains a
  function $\psi\ge0$ with $\psi(0)>0$, support in $D(0,\delta)$, and $\psi(\zeta z)=\psi(z)$.

Examples:
- non-quasi-analytic Denjoy–Carleman classes. Take a compactly supported $g\ge0$ in the one-variable
  class, with $g(0)>0$ (Proposition 3.2, part 2, followed by squaring and translating). Put
  $\varphi(x+iy)=g(x)g(y)$, which is in the class by log-convexity, $M_jM_{k-j}\le M_k$. Then take
  $\psi=\sum_{k<n}\varphi(\zeta^kz)$;
- Gevrey classes $G^s$ with $s>1$;
- $C^\infty$, $C^k$, Hölder and local Sobolev classes;
- $C^0$, $L^p_{\rm loc}$ and measurable functions.

**Definition.** A point $p\in\Omega_r$ is *stable periodic* if $O_r(p)$ is finite and disjoint from
$\partial D_1\cup\partial D_2$. Write ${\rm Reg}_r$ for the set of such points.

**Lemma 4.1 (islands)** [proved]. Let $O=\{y_1,\dots,y_N\}=O_r(p)$ be finite and avoid both circles.
Choose $\varepsilon>0$ smaller than three quantities:
- $\tfrac12\min_{i\ne j}|y_i-y_j|$;
- $\big||y_i-c_k|-r\big|$ for all $i$ and $k$;
- the $\delta_0$ of the class.

Then $U=\bigcup_iD(y_i,\varepsilon)\subset\Omega_r$ is $P_r$-invariant, and each generator maps each
disk $D(y_i,\varepsilon)$ that it acts on isometrically onto some $D(y_j,\varepsilon)$. Consequently:

for every bump class, the function $f=\psi(\cdot-y_i)$ on $D(y_i,\varepsilon)$, extended by $0$ on
$\Omega_r\setminus U$, is a non-constant invariant in $\mathcal C(\Omega_r)$. For measurable classes
$\mathbf 1_U$ is one, and $U$ and $\Omega_r\setminus\bar U$ both have positive measure. So $P_r$ is
not ergodic.

*Proof.*
1. **Disk membership is constant on each small disk.** By the choice of $\varepsilon$, a point of
   $D(y_i,\varepsilon)$ lies in $D_k$ iff $y_i$ does. If $y_i\in D_k$, then
   $D(y_i,\varepsilon)\subset D_k\subset\Omega_r$.
2. **The generators permute the disks.** If $y_i\in D_1$, then $A^{\pm1}$ maps $D(y_i,\varepsilon)$
   isometrically onto $D(A^{\pm1}y_i,\varepsilon)$, and $A^{\pm1}y_i\in O$. Likewise for $B$.
3. **The complement is invariant too.** If $z\in D_1\setminus U$ and $Az\in D(y_j,\varepsilon)$,
   then $y_j\in D_1$ (since $Az\in D_1$), so $z\in D(A^{-1}y_j,\varepsilon)\subset U$, a
   contradiction. So $\Omega_r\setminus U$ is invariant.
4. **$f$ is invariant.** Every generator acts on $D(y_i,\varepsilon)$ as a motion $z\mapsto\zeta^jz+\tau$
   carrying $y_i$ to $y_{i'}$. It carries $\psi(\cdot-y_i)$ to $\psi(\cdot-y_{i'})$, because $\psi$ is
   $\zeta$-invariant.
5. **$f$ is in the class.** It is in $\mathcal C$ by (C2) and locality. It is non-constant since
   $f(y_1)>0=f$ off $U$. ∎

**Proposition 4.2 (below $r_c$ almost every point is stable)** [proved]. If $GG_n(r)$ (closed disks)
is finite, then ${\rm Reg}_r$ is open and of full measure in $\Omega_r$.

*Proof.*
1. Each of the finitely many elements $g$ has finitely many pieces, bounded by circle arcs. So
   $E=\bigcup_g g^{-1}(\partial D_1\cup\partial D_2)$ is contained in finitely many circles, and is
   null.
2. For $z\in\Omega_r\setminus E$, the closed orbit avoids the circles. So it equals $O_r(z)$
   (Lemma 1.2(4)), and it is finite.
3. **${\rm Reg}_r$ is open.** Let $p\in{\rm Reg}_r$ with $|O_r(p)|=N$, and let $U$ be the
   neighbourhood of Lemma 4.1. Each point $z\in D(p,\varepsilon)$ has its orbit in $U$, and that orbit
   meets each disk $D(y_i,\varepsilon)$ in the images of $z$ under the motions carrying that disk to
   itself. These are rotations about $y_i$ by powers of $\zeta$. So $O_r(z)$ is finite, with at most
   $Nn$ points, and it avoids the circles because $U$ does. ∎

**Theorem 4.3 (the necklace island)** [proved]. Let $n\ge5$, let $q=i\tan(\pi/n)$ be the upper corner
of the lens at the necklace radius, and let $r_A<r<d_n$, where
$$
d_n^2=\sec^2\tfrac{\pi}{n}+16\sin^2\tfrac{\pi}{n}=r_A^2+|t|^2 .
$$
Then $O_r(q)$ consists of $2n-2$ points: the $n$ points $A^kq$ and the $n$ points $B^kq$, with the two
corners $\pm q$ counted once. It avoids both circles, so $q$ is stable periodic.

*Proof.*
1. **Where the points lie.** Write $s=\sec(\pi/n)$. Then $|q\pm1|=s<r$, so $q$ is in both disks.
   Seen from $-1$, $q$ has angle $\pi/n$, so $A^kq=-1+se^{i(2k+1)\pi/n}$; these points include
   $\bar q=-q$ (AR, Lemma 1.2: $A$ maps $q$ to $-q$). By symmetry the $B^kq$ lie on the circle of
   radius $s$ about $1$ and also include $\pm q$.
2. **The other points lie outside the other disk.** The distance from $A^kq$ to $+1$ satisfies
   $|A^kq-1|^2=s^2+4-4s\cos\frac{(2k+1)\pi}{n}$. Apart from the corners ($k=0,n-1$), it is smallest at
   angle $\pm3\pi/n$. There it equals
   $$s^2+4-4\tfrac{\cos(3\pi/n)}{\cos(\pi/n)}=s^2+8-8\cos\tfrac{2\pi}{n}=d_n^2,$$
   using $\cos3x/\cos x=2\cos2x-1$. So for $r<d_n$ the non-corner points of the $A$-circle lie
   outside $\bar D_2$. The $B$-circle is symmetric.
3. **The set is closed under the generators.** $A^{\pm1}$ acts on the $A$-circle points, which are in
   $D_1$; $B^{\pm1}$ acts on the $B$-circle points. No other moves apply. So the set is an orbit.
4. **It avoids the circles.** Every point is at distance $s<r$ from its own centre and, except for
   the corners, at distance at least $d_n>r$ from the other. ∎

| $n$ | $r_A$ | $r_c$ (table) | $d_n$ | closed form of $d_n$ |
|---|---|---|---|---|
| 5 | 1.236068 | 2.148961 | 2.656262 | $2\sqrt{4-\sqrt5}$ |
| 7 | 1.109916 | 1.623574 | 2.060096 | |
| 8 | 1.082392 | 1.711411 | 1.874758 | $\sqrt{12-6\sqrt2}$ |
| 10 | 1.051462 | 1.543357 | 1.622787 | |
| 12 | 1.035276 | 1.376547 | 1.464102 | $2\sqrt3-2$ |

As $n\to\infty$, $d_n=1+\frac{17\pi^2}{2n^2}+O(n^{-4})$, while $r_c\approx g(n)=1+\frac{4\pi^2}{n^2}$
[table, computed]. So $d_n>r_c$:
- for every tabulated $n$ [computed, from the paper's table];
- for $n=5$ [proved]: $GG_5(r)$ is infinite for $r\ge\sqrt{3+\varphi}=2.149$
  (`critical-radius-n5.md`, Theorem A), so $r_c(5)\le2.149<d_5$.

For $n\ge7$ the dependence on the table could be removed by proving $GG_n(r)$ infinite for some
$r\le2$. The referee found, in floating point, that the orbit of $-1$ is infinite at $r=2.001$ for
$n=7,8,10,12$, which suggests this is true.

The island is born exactly at $r_A$, when the lens corners enter both disks. That is the same
necklace event that kills analytic invariants.

**Theorem 4.4 (central islands)** [proved]. For $r<2$ and $0<|z+1|<\min(r,2-r)$, $O_r(z)=\{A^kz\}$
has $n$ points and avoids both circles.

*Proof.* We have $|A^kz-1|\ge2-|z+1|>r$, so no orbit point is in $\bar D_2$. Each point is at
distance $|z+1|\in(0,r)$ from $-1$. ∎

**Further islands** [computed, by the referee; floating point]. Two more families were found. They
lie below $\max(2,d_n)$, so neither changes any bound in this note.
1. For $n=12$, the orbit of the lens corner $q$ stays finite (64 points, away from the circles) on
   about $(d_{12},1.556)$. The necklace survives past $d_{12}$ in another form, but
   $1.556<2=\max(2,d_{12})$.
2. For $n=5$ and $2<r<|t|=2.351$, the orbit of the centre $-1$ is $\{-1\}\cup\{B^k(-1)\}$, with 5
   points, and is stable.
   - This is in fact [proved]: $|-1-1|=2<r$, and the points $B^k(-1)\ne-1$ are at distance at least
     $|t|>r$ from $-1$.
   - The interval lies below $d_5=2.656$.

**Theorem 4.5 (the dichotomy)** [proved]. Let $n=5$ or $n\ge7$, let $r_A<r<\max(2,d_n)$, and let
$\mathcal C=C\{M\}$ be a log-convex Denjoy–Carleman class with $M_0=1$. Then $\mathcal C$ is rigid at
$r$ if and only if $\sum M_k/M_{k+1}=\infty$, i.e. iff $\mathcal C$ is quasi-analytic. Every bump
class is non-rigid at every $r<\max(2,d_n)$.

*Proof.* The quasi-analytic case is Theorem 3.1 with Proposition 3.2. In the non-quasi-analytic case,
$\mathcal C$ is a bump class, and an island exists by Theorem 4.3 (when $r<d_n$) or Theorem 4.4 (when
$r<2$). Apply Lemma 4.1. For $r\le r_A$, use Proposition 2.2. ∎

The proof needs no computation and does not use $r_c$. For $n=5$ the interval contains
$(r_A,r_c)$ [proved]; for the other $n$ it does so according to the paper's table [computed].

What the system detects, strictly, is the alternative "unique continuation from open sets" versus
"compactly supported $\zeta$-invariant bumps". For Denjoy–Carleman classes these coincide with
quasi-analyticity and its failure.

---

## 5. Ergodicity at large radius: every continuous or measurable class becomes rigid

**Lemma 5.1 (translations from the orbit of a centre)** [proved]. Let $r'<r$ and $\rho=r-r'$.
1. If $y\in O_{r'}(-1)$, then $P_r$ contains $\tau_{y+1}$ on $D(-1,\rho)$.
2. If $y_1,y_2\in O_{r'}(-1)$ and $s=y_2-y_1$, then $P_r$ contains:
   - $\tau_{\zeta^js}$ on $D(-1,\rho-|s|)$, for all $j$;
   - $\tau_{-\zeta^js}$ on $D(-1,\rho-2|s|)$, for all $j$.

*Proof.*
1. **Shadowing the chain of $-1$.** Let $-1=y_0,\dots,y_m=y$ be an $r'$-chain, with word $w$ and
   exponent sum $e$, so $w(z)=\zeta^{-e}(z+1)+y$. For $z\in D(-1,\rho)$, apply the same letters. The
   $i$-th point is within $|z+1|<\rho$ of $y_i$, because the maps are isometries, and $y_i$ is within
   $r'$ of the relevant centre. So each step is legal at radius $r$.
2. **Removing the rotation.** $A^{-e}$ preserves $D(-1,\rho)$, and $w\circ A^{-e}=\tau_{y+1}$.
3. **Differences.** $\tau_{y_1+1}^{-1}\circ\tau_{y_2+1}=\tau_s$ is defined at $z$ if $z\in D(-1,\rho)$
   and $z+y_2+1\in\tau_{y_1+1}(D(-1,\rho))=D(y_1,\rho)$. Both hold when $|z+1|<\rho-|s|$.
4. **Rotated copies.** Conjugating by $A^{j}$, which preserves every $D(-1,\cdot)$, gives
   $\tau_{\zeta^js}$ on $D(-1,\rho-|s|)$.
5. **Inverses.** $\tau_{-\zeta^js}$ is defined on the image $D(-1+\zeta^js,\rho-|s|)$, which contains
   $D(-1,\rho-2|s|)$. ∎

**Theorem 5.2 (ergodicity criterion)** [proved]. Let $n=5$ or $n\ge7$. Suppose $r'<r$ and
$y_1\ne y_2\in O_{r'}(-1)$ satisfy
$$
r-r'>\sec\tfrac{\pi}{n}+6|y_2-y_1| .
$$
Then:
- every continuous invariant function on $\Omega_r$ is constant;
- every measurable invariant function is a.e. constant, i.e. $P_r$ is ergodic for Lebesgue measure
  (Lemma 1.3);
- ${\rm Reg}_r=\emptyset$.

So every class contained in $C^0$, and every class of measurable functions modulo null sets, is rigid
at $r$.

*Proof.*
1. **Setup.** Let $s=y_2-y_1$ and $K'=r-r'-6|s|>\sec(\pi/n)$. Let $V=\{\pm\zeta^js\}$. By Lemma 5.1,
   every $\tau_v$ with $v\in V$ is in $P_r$ on $D(-1,K'+4|s|)$.
2. **Paths by the Steinitz lemma.** Let $x\in\Lambda_s:=\mathbb Z[\zeta]s$, the subgroup generated by
   $V$, and write $x=\sum_{i=1}^Nv_i$ with $v_i\in V$. The vectors $u_i=v_i-x/N$ have modulus at most
   $2|s|$ and sum $0$.
   - **[classical, from memory]** The Steinitz lemma with the Grinberg–Sevast'yanov constant $d=2$
     in the plane orders them so that every partial sum has modulus at most $4|s|$.
   - So the partial sums of the reordered $v_i$ stay within $4|s|$ of the segment $[0,x]$.
3. **Orbits are dense in $D(-1,K')$.** Let $z,z+x\in D(-1,K')$. Every point $z+S_k$ of the path lies
   in $D(-1,K'+4|s|)$, by convexity, so each step is a legal $\tau_v$. Hence $z+x\in O_r(z)$. Since
   $\Lambda_s$ is dense, $O_r(z)$ is dense in $D(-1,K')$.
4. **Continuous invariants are constant on $D(-1,K')$.** Given $z,w\in D(-1,K')$, take $x_k\in\Lambda_s$
   with $z+x_k\to w$. Then $f(w)=\lim f(z+x_k)=f(z)$.
5. **Measurable invariants are a.e. constant on $D(-1,K')$.**
   - Replace $f$ by $\arctan f$, which is bounded and still invariant.
   - For a mollifier $\eta_\epsilon$, $g=f*\eta_\epsilon$ is continuous on $D(-1,K'-\epsilon)$. It
     satisfies $g(z+x)=g(z)$ whenever the $\epsilon$-disks about $z$ and $z+x$ lie in $D(-1,K')$:
     apply the identity $f(\cdot+x)=f$, which holds at every point of $D(-1,K')\cap(D(-1,K')-x)$
     by step 3.
   - So $g$ is constant on $D(-1,K'-2\epsilon)$, by step 4's argument.
   - Letting $\epsilon\to0$, $g\to f$ in $L^1_{\rm loc}$. So $f$ is a.e. constant on $D(-1,K')$.
6. **Globally.** By the symmetry $z\mapsto-z$, the same holds on $D(1,K')$, and the two disks
   overlap since $K'>1$. By Lemma 2.1, with $K=K'$, and the countable-word argument of
   Proposition 2.2, $f$ is constant (a.e. constant) on $\Omega_r$.
7. **No islands.** An island would give a non-constant continuous invariant (Lemma 4.1). ∎

**Corollary 5.3 (general bound)** [proved]. For $n=5$ or $n\ge7$, every class contained in $C^0$,
and every class of measurable functions modulo null sets, is rigid at every
$$
r>R_{\rm erg}(n):=\sec\tfrac{\pi}{n}+\max\bigl(2,4\sin\tfrac{\pi}{n}\bigr)+16\sin\tfrac{\pi}{n}.
$$
This gives $12.99$ for $n=5$, $10.05$ for $n=7$, and $R_{\rm erg}(n)\to3$ as $n\to\infty$.

*Proof.*
1. **The translation $\tau_t$.** $\tau_t=A^{-1}B$ has domain $D(1,r)\cap D(-1-t,r)$. This contains
   $D(-1,r-\max(2,|t|))$, because $|{-1}-1|=2$ and $|{-1}-(-1-t)|=|t|$.
2. **Its inverse.** $\tau_{-t}=B^{-1}A$ has domain $D(-1,r)\cap D(2\zeta-1,r)\supseteq D(-1,r-2)$.
3. **Rotated copies.** Conjugating by $A^j$ gives $\tau_{\pm\zeta^jt}$ on $D(-1,r-\max(2,|t|))$.
4. **Conclusion.** Run steps 2–6 of Theorem 5.2 with $s=t$ and margin $4|t|$. ∎

### 5.3 Sharper bounds by exact computation

1. **$n=5$ [proved by exact computation].** The computation is not in this repository. It is
   specified here completely enough to reproduce, and the referee reproduced it independently
   (`referee-report-regularity-scale.md`, §3.1).
   - **Arithmetic.**
     - A point of $\mathbb Z[\zeta_5]$ is an integer vector $(a_0,a_1,a_2,a_3)$, meaning
       $\sum a_i\zeta^i$, with $\zeta^4=-1-\zeta-\zeta^2-\zeta^3$.
     - The maps are $A(z)=\zeta^{-1}(z+1)-1$, $A^{-1}(z)=\zeta(z+1)-1$, and $B^{\pm1}$ likewise about
       $+1$. They are integer-linear in these coordinates.
     - For $w=\sum_{i=0}^4c_i\zeta^i$ (with $c_4=0$), put $e_m=\sum_jc_jc_{j-m}$, indices mod 5. Then
       $|w|^2=e_0+e_1(\zeta+\zeta^4)+e_2(\zeta^2+\zeta^3)=\tfrac12\big((2e_0-e_1-e_2)+(e_1-e_2)\sqrt5\big)$.
   - **Membership in $\mathbb Q(\sqrt5)$.** A point $z$ is in the open disk about $c=\pm1$ iff
     $|z-c|^2-r'^2<0$. With
     $$r'^2=\tfrac12(-56+30\sqrt5),\qquad r'=2.35394\ldots,$$
     this is the sign of $P+Q\sqrt5$ with $P,Q\in\mathbb Z$. That sign is decided exactly: it is
     immediate when $P$ and $Q$ have the same sign, and otherwise it is the sign of $P^2-5Q^2$
     combined with the sign of the dominant term.
   - **The radius.** Exact comparisons give $|t|<r'<2.354$. Here $|t|^2=10-2\sqrt5$, so
     $|t|=2.35114\ldots$; this is the radius at which $B^{\pm1}(-1)$ enter $D_1$.
   - **Breadth-first search.** Start from $-1=(-1,0,0,0)$. Repeatedly take the next unexplored point.
     For each centre whose open disk contains it, decided exactly as above, apply both rotations about
     that centre, and record each new point. Stop once $60\,001$ points have been recorded.
   - **Why this suffices.** Every recorded point lies in $O_{r'}(-1)$, because it is the end of an
     $r'$-chain with exactly verified steps. Theorem 5.2 needs only two distinct orbit points, so the
     search need not be complete, and the orbit need not be finite.
   - **The two points.** Among the recorded points there are two whose difference is
     $s=576+110\zeta+288\zeta^2+466\zeta^3$. By the formula above,
     $$|s|^2=\tfrac12(573140-256316\sqrt5).$$
     - $|s|>0$, because $573140^2>5\cdot256316^2$.
     - $|s|<0.0119$, because $L=573140-2(0.0119)^2>0$ and $L^2<5\cdot256316^2$.
     - Numerically $|s|=0.011814\ldots$.
     - The referee found this difference among 2163 pairs of recorded points.
   - **Conclusion.** Theorem 5.2 with $y_1,y_2$ these two points gives rigidity, for every class
     contained in $C^0$ and every measurable class modulo null sets, at every
     $$r>2.354+(\sqrt5-1)+6(0.0119)=3.6615 .$$
     With the exact values of $r'$ and $|s|$ the bound is $3.66089$.
2. **$n=7,8,10,12$ [computed].** The same method, with floating-point disk tests whose smallest
   margin was at least $4\cdot10^{-5}$ and with $r'$ just above 2, gives:

   | $n$ | 7 | 8 | 10 | 12 |
   |---|---|---|---|---|
   | rigid for $r>$ | 3.171 | 3.200 | 3.154 | 3.160 |
   | referee, from $r'=2.001$ | 3.136 | 3.130 | 3.113 | 3.098 |

   None of these is certified.
3. **The limits of the method.** It cannot go below about $\max(2,|t|)+\sec(\pi/n)$. Two things set
   that floor: the orbit of $-1$ is trivial until $-1$ enters $D_2$, at $r'=2$; and the descent of
   Lemma 2.1 only reaches $D(\pm1,K)$ with $K>r_A$.

---

## 6. The true picture, and the conjecture

For $n=5$ or $n\ge7$, the thresholds are ordered by inclusion of classes:
$$
\underbrace{r_A}_{\text{every q.-a. class}\,\supseteq C^\omega}
\;<\;\max(2,d_n)\;\le\; r_{G^s}\le r_{G^{s'}}\le r_{C^\infty}\le r_{C^k}\le r_{C^0}\le r_{L^\infty}=r_{\rm erg}\;\le\;R_{\rm erg}(n)
\qquad(1<s<s').
$$
Notes on the chain:
- **$r_{L^\infty}=r_{\rm erg}$.** Here $r_{\rm erg}$ is the ergodicity threshold. Ergodicity is exactly
  rigidity of bounded measurable invariants (Lemma 1.3), and the threshold is well defined by
  Proposition 2.2.
- **$r_{C^0}\le r_{L^\infty}$.** A continuous function need not be bounded on $\Omega_r$, so this does
  not follow from inclusion. Instead: if $f$ is a non-constant continuous invariant, then $\arctan f$
  is a bounded continuous invariant. It is not a.e. constant, since a continuous function that is
  a.e. constant is constant.
- **Status.** Every inequality is [proved].

For $n=5$ this reads
$$
1.236 < r_c(5)\le 2.149 < 2.656 \le r_{\text{every bump class}} \le 3.662 .
$$

**Conjecture 6.1.** For $n=5$ or $n\ge7$, every bump class has the same threshold, namely
$$
r_{\rm bump}(n)=\max\Bigl(2,\ \sqrt{\sec^2\tfrac{\pi}{n}+16\sin^2\tfrac{\pi}{n}}\Bigr).
$$
That is: ${\rm Reg}_r=\emptyset$ and $P_r$ is ergodic for every $r$ above it. Concretely this is
$2\sqrt{4-\sqrt5}$ for $n=5$, $2.0601$ for $n=7$, and $2$ for $n\ge8$.

**Evidence** [computed, floating point, not certified].
1. **Islands found by random search** for $n=5$: orbits of random points, capped at 400–5000 points,
   with the margin to the circles recorded. The only islands found for $r\in[2.3,2.65]$ were cells of
   the necklace orbit; each cell is centred at a point of that orbit with stabilizer of order 5,
   giving orbits of 40 points for generic points of a cell. Their margin is $d_5-r$ to all printed
   digits, and they vanish at $d_5$.
2. **No islands found above $d_n$ or $2$.**
   - $n=5$: none in 2000–3000 random points at each of $r=2.66,2.7,2.8,3$.
   - $n=5$: none among the orbits of all points of $\mathbb Z[\zeta_5]$ with coefficients in
     $[-3,3]$, at $r\in\{2.66,2.7,2.8,3,3.5,4\}$. Every rotation centre of $\Gamma$ lies in
     $\mathbb Z[\zeta]$.
   - $n=7$: none at $r=2.07,2.1$. $n=8$: none at $2.02,2.1$. $n=12$: none at $2.02$.
   - Just below the conjectured value they are found: $n=7$ at $r=2.0$ (necklace orbits of 84
     points), and $n=8$ at $r=1.9$ (central orbits of 8 points).
   - The referee also found none, in 300 random points per radius with an orbit cap of 3000:
     - $n=5$ at $r=2.7,3,3.5,4,13$;
     - $n=8$ at $r=2.05,2.5,3,3.3$;
     - $n=7$ at $r=2.07,2.5$.
3. **Orbits fill the domain.** For $n=5$, orbits of 60 000 points from random starts visit every cell
   of a $0.1$-grid of $\Omega_r$ at $r=2.7$ and $r=3$, for each of 3 starting points. At $r=2.5$ they
   visit 99% of the cells; the missing cells are the necklace islands. For $n=8$ at $r=2.05$, they
   visit 99.7–99.9% of a $0.05$-grid.

**What the picture says about the owner's question.**
- The hoped-for continuum of regularity thresholds filling $(r_A,r_c)$ **does not exist**.
- Quasi-analytic classes stop at $r_A$. Non-quasi-analytic classes, even Gevrey classes arbitrarily
  close to analytic, survive up to at least $\max(2,d_n)$.
- $\max(2,d_n)$ lies above $r_c$: for $n=5$ this is proved, and for the other $n$ it follows from the
  paper's table.
- The two-disk system detects quasi-analyticity: for $r\in(r_A,\max(2,d_n))$, rigidity of a
  Denjoy–Carleman class is *equivalent* to $\sum M_k/M_{k+1}=\infty$ (Theorem 4.5).
- Within the bump classes there is room for different thresholds, in $[\max(2,d_n),R_{\rm erg}]$.
  Conjecture 6.1 says there is none.

---

## 7. Intermediate notions

**(a) Piecewise-analytic invariants.**
- With finitely many analytic pieces, these behave like bump classes. The indicator of the
  $2n-2$ necklace disks has $2n-1$ pieces and is invariant on $(r_A,d_n)$. The central island gives
  $n+1$ pieces on $(0,2)$. Above $R_{\rm erg}$ no non-constant measurable invariant exists. So there
  is no new threshold.
- A genuine integer-valued scale would be $\kappa(r)$, the least number of analytic pieces of a
  non-constant invariant. Theorem 4.1 of AR and the islands give $2\le\kappa(r)\le\min(2n-1,n+1)$ on
  $(r_A,\max(2,d_n))$, and $\kappa=\infty$ above $r_{\rm erg}$.
- Whether $\kappa$ takes intermediate values, or how it behaves near $r_c$, is **open**. The lower
  bound needs a careful definition of "piece" that excludes slits.

**(b) Hölder, Sobolev, and the quotient.**
- Hölder and Sobolev classes are bump classes, so they fall under §4–§5 and give nothing new.
- "Sobolev functions on the quotient" are not available: the quotient is non-Hausdorff for
  $r>r_A$ (§8).

**(c) Intermediate pseudogroups.**
- Let $H^{(1)}_r$ be the pseudogroup generated by $P_r$ and the germ produced by one round of
  continuation. That germ is $\tau_t$, extended from its $P_r$-domain $U_{21}=D_2\cap(D_1-t)$ to the
  union of the atoms of $\Omega_r\cap(\Omega_r-t)$ that it meets.
  - For $r>r_A$, that union is $U_{11}\cup U_{21}$ (AR, §6, Step 1).
  - For $r\le r_A$, it is $U_{21}$ itself, because $U_{11}\cap U_{21}=\emptyset$. So
    $H^{(1)}_r=P_r$ there.
- **[proved]** For $n\ge63$ and every $r>r_A$, $H^{(1)}_r$ has orbits dense in
  $D(-1,r-20\sin\frac{\pi}{n})\ne\emptyset$.

  *Proof.*
  1. $\tau_{\pm\zeta^jt}$ is defined on $D_1\cap(D_1\mp\zeta^jt)\supseteq D(-1,r-|t|)$.
  2. Steinitz, as in Theorem 5.2, puts $z$ and $z+x$ in one orbit whenever both lie in
     $D(-1,r-5|t|)$ and $x\in\Lambda$.
  3. That disk is non-empty, since $20\sin(\pi/n)<1<r$ for $n\ge63$. The bound $n\ge63$ is sharp for
     this argument: $20\sin(\pi/62)=1.0130>\sec(\pi/62)$. ∎

  So the critical radius of $H^{(1)}$ is $r_A$. One continuation step already destroys finiteness.
- The filtration $P_r=H^{(0)}\subset H^{(1)}\subset\cdots\subset H_r$ does not interpolate between
  $r_A$ and $r_c$, at least for large $n$. For $5\le n<63$, whether $H^{(1)}_r$ has finite orbits
  just above $r_A$ is **open**. It is computable.

**(d) Ergodic version.**
- $L^2$ invariants are constant iff $P_r$ is ergodic.
- $P_r$ is not ergodic for $r<\max(2,d_n)$, because of islands of positive measure (Lemma 4.1).
- $P_r$ is ergodic for $r>R_{\rm erg}(n)$ (Theorem 5.2).
- This matches the usual picture of piecewise isometries, in which periodic islands obstruct
  ergodicity. What is perhaps unexpected is that here the islands disappear completely at finite
  radius. The reason is the descent of Lemma 2.1: every orbit is pulled into the deep part of the
  disks, where the dense translation group acts freely.

---

## 8. Reinterpreting $r_c$, and the Hausdorff property

**Proposition 8.1.** With open or closed disks:
- $r_c=\sup\{r:\text{orbit sizes are bounded}\}$ [proved, `boundary-contact.md` Proposition 3.3];
- $r_c\le r_c^{\rm orb}=\inf\{r:\text{some }P_r\text{-orbit is infinite}\}$ [proved, Lemma 1.2].

Equality is the paper's open question.

So "$r_c=\sup\{r:\text{every pseudogroup orbit is finite}\}$" is exactly the statement
$r_c=r_c^{\rm orb}$, which is open. It is not a separate characterization.

**Proposition 8.2 (Hausdorff quotient)** [proved; part 2 in this generality is not yet refereed].
Let $n=5$ or $n\ge7$, and let $Q_r=\Omega_r/P_r$.
1. $Q_r$ is Hausdorff for $0<r\le r_A$.
2. $Q_r$ is not Hausdorff for any $r>r_A$.

*Proof.*
1. **Part 1.** For $1<r\le r_A$ this is AR, Lemma 5.3. For $r\le1$ the disks are disjoint, and $Q_r$
   is two disjoint cones.
2. **Part 2, setup.** Suppose $Q_r$ were Hausdorff. The orbit relation is open (AR, Lemma 5.3, step 1),
   so its graph would be closed in $\Omega_r\times\Omega_r$. The motions realized by $P_r$ lie in the
   countable group $\Gamma$.
3. **Fullness up to countable sets.** Let $\gamma\in\Gamma$, let $C$ be a component of
   $\Omega_r\cap\gamma^{-1}\Omega_r$ meeting ${\rm Dom}_P(\gamma)$, and let $z_k\in{\rm Dom}_P(\gamma)$
   converge to $p\in C$. Then $(z_k,\gamma z_k)\to(p,\gamma p)$, so $\gamma p=\delta p$ for some
   $\delta$ with $p\in{\rm Dom}_P(\delta)$.
   - Either $\delta=\gamma$, or $p$ is the fixed point of the non-identity motion
     $\delta^{-1}\gamma$, which has at most one.
   - So ${\rm Dom}_P(\gamma)\cap C$ is relatively closed in $C\setminus F_\gamma$, with $F_\gamma$
     countable.
   - A connected open subset of the plane minus a countable set is connected. So
     ${\rm Dom}_P(\gamma)\supseteq C\setminus F_\gamma$.
4. **The hull construction, up to countable sets.** Rerun AR, §6 Steps 1–3 and the Steinitz step of
   AR, Theorem 8.1, with $P_r$ in place of the hull.
   - Each step composes elements of $P_r$, which gives an open domain containing a non-empty open set
     minus a countable set, or extends a domain to a component, which step 3 allows up to a
     countable set.
   - So every $s$ in the countable set $S_H$ of AR, Theorem 8.1, satisfies $\tau_s\in P_r$ on
     $(D_1\cap(D_1-s))\setminus F_s$, with $F_s$ countable.
   - Let $E=\bigcup_s(F_s\cup(F_s-s))$, which is countable. For $z\in D(-1,r/4)\setminus E$, the
     orbit $O_r(z)$ contains $z+(S_H\cap D(0,\varepsilon))$. This set is dense in $D(z,\varepsilon)$.
5. **Contradiction.** Choose such a $z$, and $w\in D(z,\varepsilon/2)\setminus E$ with
   $w\notin O_r(z)$. This is possible because $E\cup O_r(z)$ is countable. Every saturated open set
   containing $w$ contains a ball about $w$. That ball meets the dense set $O_r(z)\cap D(z,\varepsilon)$,
   so the saturated set contains $z$. Hence $[w]$ and $[z]$ cannot be separated, contradicting the
   assumption. ∎

The referee checked part 2 on $(r_A,r_c)$, where $P_r$ has finitely many motions and the exceptional
sets are finite, and above $R_{\rm erg}$, where orbits are dense by Theorem 5.2. The referee suggested
the countable version above (report, issue 11); its write-up here has not been refereed.

The parallel the brief suggests therefore has a different shape. $r_A$ carries all of the following:
- analytic invariants exist;
- $P_r$ is full;
- $Q_r$ is Hausdorff;
- $Q_r$ is a Riemann surface.

All four hold up to $r_A$ and fail just above it. Non-Hausdorffness, which implies the failure of
the other three, fails for every $r>r_A$ by Proposition 8.2. Fullness fails at least on $(r_A,r_c)$
(AR, Corollary 8.2). Invariant continuous functions already fail to
separate orbits at $r_A$: they cannot separate $[p]$ from $[\gamma p]$ at a boundary point $p$ of a
non-full domain. So "$r_c$ = where continuous invariants stop separating orbits" is false as stated.
The correct statement is measure-theoretic.

**Proposition 8.3 (a.e. separation)** [proved]. If $r<r_c$, then for every $z\in{\rm Reg}_r$, which is
a set of full measure by Proposition 4.2, and every $w\notin O_r(z)$, there is a $C^\infty$ (even
Gevrey) invariant $f$ with $f(z)\ne f(w)$.

*Proof.* Use Lemma 4.1 with $\psi(z)=g(|z|^2)$. Here $g$ is smooth (or Gevrey), strictly decreasing
on $[0,a]$ for some $a<\varepsilon^2$, and zero on $[a,\infty)$.
- If $w$ lies in an island disk $D(y_i,\varepsilon)$ with $|w-y_i|^2<a$, then $w\ne y_i$, since
  $w\notin O_r(z)$. So $f(w)<f(y_i)=f(z)$.
- Otherwise $f(w)=0<f(z)$. ∎

Let $r_{\rm sep}$ be the supremum of the radii at which invariant continuous functions separate almost
every point from the points outside its orbit. Then
$$
r_c\le r_{\rm sep}\le r_{\rm erg}.
$$

**[conjecture]** $r_{\rm sep}=r_c$. This would follow if, for $r>r_c$, the points with infinite orbits
formed a set of positive measure on which orbits are somewhere dense. The random scans for $n=5$ at
$r=2.2$ are consistent with this, but they do not decide it: 29% of the points had finite orbits
below the cap.

This would give the two ends a parallel description:
- **$r_A$:** where the orbit space stops being Hausdorff, and where invariants of every class
  satisfying (C0)–(C4) become constant;
- **$r_c$:** (conjecturally) where smooth and continuous invariants stop separating almost every
  orbit;
- **$r_{\rm bump}$:** (conjecturally $\max(2,d_n)$) where they become constant.

---

## 9. Status and gaps

**Independent referee's verdicts**
([`referee-report-regularity-scale.md`](referee-report-regularity-scale.md)). The referee
re-derived every proof in §§1–5, §7(c) and §8 by hand, and found no fatal error and no gap in any
proof. The issues raised were overstatements of wording and small omissions; their fixes are
incorporated.

| claim | verdict |
|---|---|
| Rigidity is an up-set on $(r_A,\infty)$ (Lemma 2.1, Proposition 2.2) | correct |
| Classes satisfying (C0)–(C4), including quasi-analytic Denjoy–Carleman classes $\supseteq C^\omega$, have $r_{\mathcal C}=r_A$; $C\{1\}$ has threshold 1 | correct after minor fixes |
| Bump classes: $\max(2,d_n)\le r_{\mathcal C}\le R_{\rm erg}(n)$, through the necklace island, the central islands and ergodicity | correct after minor fixes |
| The dichotomy (Theorem 4.5) | correct; the status wording around it was corrected |
| $n=5$: bump thresholds in $[2\sqrt{4-\sqrt5},3.662]$ | correct; the exact certificate was reproduced independently |
| Hausdorff for $r\le r_A$; not Hausdorff on $(r_A,r_c)$ or above $R_{\rm erg}$; a.e. separation below $r_c$ | correct |
| $H^{(1)}_r$ has dense orbits for $r>r_A$, $n\ge63$ | correct after a minor fix |
| The classical inputs (Denjoy–Carleman, Steinitz with the Grinberg–Sevast'yanov constant, Behnke–Stein via AR) | correctly stated and used |

**Not yet refereed.** These were written after the report:
- Lemma 1.3 (a.e. versus everywhere invariance), which follows the referee's sketch;
- Proposition 8.2 part 2 for all $r>r_A$, which follows the referee's sketch (issue 11);
- the remark in §4 proving the $n=5$ centre island on $(2,|t|)$.

**Not checked by the referee.**
- AR's results (Theorems 4.1 and 8.1, Lemma 5.3). These are refereed in
  [`referee-report-thread6.md`](referee-report-thread6.md) and were relied on.
- `critical-radius-n5.md` Theorems A and B, and the paper's table of $r_c$.
- The classical theorems against their sources: Denjoy–Carleman (Rudin, Theorem 19.11; Hörmander,
  Theorem 1.3.8) and Grinberg–Sevast'yanov.
- The §6 evidence (random scans and coverage tests), beyond the referee's own spot checks.

**Proved by an exact computation.** The bound of $3.662$ for $n=5$, for every class contained in
$C^0$ and every measurable class modulo null sets (§5.3). It was reproduced independently by the
referee. The computation is specified in §5.3; it is not in the repository.

**Computed only.**
- The bounds for $n=7,8,10,12$ in §5.3.
- All island searches and coverage tests in §6, and the $n=12$ corner orbit of §4.
- $d_n>r_c(n)$ for $n\notin\{5,8,10,12\}$, which rests on the paper's table. For $n=5,8,10,12$ the
  upper bound on $r_c(n)$ is proved (Theorem A of the four critical-radius notes, and in Lean).
- For $n=5$, the lower bound is proved as well, so $r_c(5)=\sqrt{3+\varphi}$
  ([`sharp-lower-bound-n5-pentagrid.md`](sharp-lower-bound-n5-pentagrid.md)). Only the upper bound
  is used here.

**Classical results used.**
- Denjoy–Carleman, both directions, in Rudin's normalization: **[classical, confirmed]** in the
  form $\sum M_k/M_{k+1}=\infty\iff$ quasi-analytic, for log-convex $M$.
- Steinitz lemma with constant $d$ (Grinberg–Sevast'yanov): **[classical, from memory]**. The proofs
  work with any finite constant $C$, by replacing $4|s|$ with $2C|s|$ and $6|s|$ with $(2+2C)|s|$.
- AR, Theorems 4.1 and 8.1 (refereed), which in turn use Behnke–Stein, Jordan's theorem and Steinitz.

**Gaps and open questions.**
1. **Conjecture 6.1.** Is every bump-class threshold equal to $\max(2,d_n)$? Equivalently: no islands
   and ergodicity just above it. A proof would need either a sharper version of Theorem 5.2 that
   reaches inside $D(\pm1,r_A)$, or a classification of finite orbits for $r\in(d_n,R_{\rm erg})$.
2. Whether $C^0$, $C^\infty$ and Gevrey rigidity can differ inside $[\max(2,d_n),r_{\rm erg}]$, for
   example through non-ergodic decompositions with fractal boundaries.
3. **$r_{\rm sep}=r_c$?** Do infinite orbits have positive measure just above $r_c$?
4. The piece-counting scale $\kappa(r)$ of §7(a).
5. Whether $H^{(1)}_r$ has infinite orbits just above $r_A$ for $5\le n<63$.
6. Remove the dependence on the table for the remaining $n\ge7$ (all but $8,10,12$) by proving
   $GG_n(r)$ infinite for some $r\le2$ (§4).
7. **Self-check.**
   - In Theorem 5.2 the descent radius $K$ must be strictly below $r$ and strictly above $r_A$. That
     holds, since $K'<r-r'<r$.
   - The density step uses only that $\mathbb Z[\zeta]s$ is dense for $s\ne0$, which holds for
     $n\notin\{1,2,3,4,6\}$.
   - For $n=6$ none of the rigidity statements hold: by AR, §11 item 6, real-analytic invariants exist
     at every $r$.

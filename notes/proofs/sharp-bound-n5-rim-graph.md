# Finiteness of $GG_5(r)$ below $\sqrt{3+\varphi}$: the rim graph, a renormalization of the radius, and where parent orbits are glued

Authors: Eric Vergo, Claude

**Review.** Not refereed. The note develops idea 47 of [`sharp-bound-n5-atlas.md`](sharp-bound-n5-atlas.md) in the form given by its referee ([`referee-report-sharp-bound-n5-atlas.md`](referee-report-sharp-bound-n5-atlas.md), §4), who defined the rim graph and stated the recursion $D(\varepsilon\delta)\le(R+1)D(\delta)+R$. From refereed notes it uses: `sharp-lower-bound-n5.md` Lemma 2.2(3) (every level radius is a non-norm radius) and Theorem 4.1 (at a non-norm radius, $GG_5(r)$ is finite iff the internal translations of word maps at lattice points are bounded); the certified finiteness at level 0, $\delta=1/10$ ([`../certificates.md`](../certificates.md); the certificate theorem `critical-radius-n5.md` Theorem 4.2 is refereed on paper, not proved in Lean); group monotonicity, `boundary-contact.md` Theorem 3.4 (refereed, Lean-checked); and, for the component-graph form only, the conventions of `sharp-bound-n5-component-graph.md` §1 and Theorem 4 and Corollary 5(2) of `sharp-bound-n5-token-components.md` (the (T) note). All of these are refereed.

**What is established and what is not.** Let $r_c=\sqrt{3+\varphi}$, $\delta=r_c^2-r^2$, $\varepsilon=\varphi^{-3}$; the parent radius is $r$, the child radius $r'>r$ (in the main case $r_c^2-r'^2=\varepsilon\delta$).

- **Not established: (B).** Finiteness of $GG_5(r)$ for every $r<r_c$ is not proved. A uniform bound on the diameter of rim graphs is not proved.
- **Proved.**
  1. *The rim recursion* (Theorem 1). For any radii $r<r'$, with $R$ the largest rim-graph diameter of a lattice orbit at $r'$ relative to $r$ and $M(\cdot)$ the largest internal translation of a word map at a lattice point: $M(r')+c\le(R+1)\bigl(M(r)+c\bigr)$, $c=|1-\zeta^2|=1.90211$. For the component-graph diameter, $D(r')+1\le(R+1)(D(r)+1)$, which is the referee's recursion.
  2. *Finiteness from one sequence* (Theorem 2). If the rim-graph diameters $R_k$ for the steps between consecutive level radii $r_{k-1}<r_k$ are all finite, then $GG_5(r)$ is finite for every $r<r_c$. If $R_k\le R$ for all $k$, then $M(r_k)\le(M(r_0)+c)(R+1)^k$, that is $M=O(\delta^{-\log(R+1)/\log\varphi^3})$. One geometric sequence suffices; any other sequence of non-norm radii increasing to $r_c$ from a certified base works as well. This route uses neither (T) nor the component graph.
  3. *What it is worth* (Proposition 3). "$R_k<\infty$ for every $k$" is equivalent to (B). All content is in a uniform bound. Conversely every child orbit satisfies $R\ge(\operatorname{diam}_V O'-M(r))/(M(r)+c)$, so rim graphs must grow when the step from $r$ to $r'$ grows.
  4. *Anatomy of the rim* (Proposition 4). For $2\le r<r'\le r_c$: rim letters come in rotation cycles of five points on one circle; each cycle has exactly one or two *anchors* (points in the other disk at radius $r$); all its other points are fixed by the parent group, so their states are singleton pieces. Two non-singleton pieces are adjacent in the rim graph only through an *essential edge*: the move between the two consecutive anchors of a two-anchor cycle. For the letter $a$ the upper anchor lies in the crescent $D_1(r')\setminus D_1(r)$ inside $D_2(r)$, at an angle about $-1$ between $72^\circ-\theta_0$ and $\theta_0$, $\cos\theta_0=(4+\rho^2-r^2)/(4\rho)$; as $\delta\to0$ this is the arc of $\partial D_1$ from $E$ to the cusp $\zeta-\zeta^4$, whose $a$-image runs from the cusp $\zeta^4-\zeta$ to $\bar E$. The only other gluing is through *junction states*, which lie outside both disks of radius $r$ and inside both of radius $r'$, next to the cusps. Every singleton is within distance 2 of a non-singleton piece, so $R\le R_{\rm red}+4$, where $R_{\rm red}$ is the largest rim distance between non-singleton pieces.
  5. *The gluing is one partial translation* (Proposition 5). $a=T_v\circ b$ with $v=2(\zeta^{-1}-1)\in\Lambda_T$. An essential edge $y\mapsto a(y)$ joins the pieces of $b(y)$ and $b(y)+v$, and it is internal to one piece exactly when some parent word maps $(b(y),j)$ to $(b(y)+v,j)$.
  6. *One event merges at most two orbits per cycle* (Corollary 6). Each rotation cycle that enters as the radius grows past $|y+1|$ contributes at most one edge between non-singleton pieces.
- **Computed** (exact arithmetic in $\mathbb Z[\zeta]$; §4).
  1. *Orbit of $0$, levels 1–4* (level 4: $76\,031\,321$ states, $14\,991$ pieces): rim-graph diameter $12,14,14,14$; radius $6,7,7,7$, with the parent orbit of $0$ as the unique centre; $R_{\rm red}=8,10,10,10$. This extends the referee's 12, 14, 14 by level 4.
  2. *Named orbits.* $E$: $10,11,10,10$ at levels 1–4. Class of $-\zeta^2$: $16,11,18,11$ at levels 1–4. The $1/55$ family: $26,24,24,24$. The $1/30$ family: $18,22,22$.
  3. *Random child orbits, sampled child first.* $1\,573$ distinct children at 30 parent defects from $\delta=1/400$ to $1/10$ with step ratio $\varepsilon$ (709 with at least $10^4$ states, up to $2.6\cdot10^7$): diameter at most **29**, with no growth as $\delta$ decreases (the maxima are 15 at $1/400$, 16 at $1/250$, 29 at $1/30$). Along the $\varepsilon$-chains of the two worst children: $29\to29$ and $26\to16\to18$. Other ratios (about 115 children each): at most 4 for ratio $0.99$, 8 for $0.9$, 11 for $\varphi^{-1}$, 20 for $1/2$, 16 for $\varphi^{-2}$, and 84 for $\varepsilon^2$. With a fixed base the diameter grows like $1/\delta$: $12,38,164$ from level 0 to levels 1, 2, 3.
  4. *Where the gluing sits.* The rim points are spread along whole arcs, but the essential edges between different pieces lie in 7 fixed angular windows per quarter-arc, for example $[9.75^\circ,10.13^\circ]$ next to $E$ and $[25.27^\circ,25.89^\circ]$ next to the critical point $0.927+0.951i$. The windows are the same at levels 2, 3, 4: they are arcs of fixed length, not $\delta$-neighbourhoods of the tight points. In the middle window ($29^\circ$–$43^\circ$) every essential edge is internal. Junction states number at most 20 on every $\varepsilon$-step child examined (6 on the orbit of $0$ at every level), and $R-R_{\rm red}\le4$ always.
  5. *No hub.* The largest piece is adjacent to only $9\%$ of the pieces. The rim graph is nearly a tree, with cycle rank $4\,398$ against $14\,991$ vertices at level 4, and its radius is half its diameter.
  6. *Transport by $\varepsilon$.* Under the plurality map $P\mapsto$ (the child piece of $\varepsilon P$), the rim distance of a non-singleton piece from the seed piece never increases (levels $1\to2$, $2\to3$, $3\to4$). Every non-singleton piece of the next level lies within 2 rim steps of an image piece.
  7. *Events.* The orbit of $0$ grows through 9, 22 and 83 exact thresholds between consecutive levels. The child has $654$, $1\,944$, $7\,074$, $21\,964$ rim states and $44$, $108$, $392$, $1\,152$ essential edges between pieces at levels 1–4. Both counts grow; the diameter does not.
- **Conjectured.** Conjecture 7 (uniform rim bound): there is $R_0$ (the data suggest $R_0=29$) such that for $0<\delta\le1/10$ every lattice orbit at defect $\varepsilon\delta$ has rim-graph diameter at most $R_0$ relative to defect $\delta$. With Theorem 2 it implies (B).

**The remaining gap.** Conjecture 7. All three proof routes tried (§5) end at the same place:
- *Tight points:* the gluing windows are fixed arcs, not $\delta$-neighbourhoods of tight points.
- *A hub:* there is none, and the tube version needs a (K)-type input for the parent.
- *Events:* the essential merges are controlled one at a time, but their number grows like $1/\delta$, and no monotone potential was found.

What a proof needs is control of the parent orbit partition on the gluing crescents. That is the statement that every parent orbit meeting a gluing window is linked, in boundedly many applications of the partial translation $T_v$ and the junctions, to the parent orbit of the seed. It is a global, reverse-type statement of the same nature as (R2) and (A6). **The rim graph is (K) in a new form.** It localizes the difficulty to a curve times internal space, which is a genuine sharpening, but it does not remove it.

Labels: **proved** (argument written here), **computed** (exact; method in §7), **conjecture**.

---

## 1. Setting

As in the component-graph note §1. $\zeta=e^{2\pi i/5}$, $\Lambda=\mathbb Z[\zeta]$; $a,b$ rotate by $\zeta^{-1}$ about $-1,+1$ on the closed disks $D_1(r),D_2(r)$; $A,B$ are their inverses. Tokens, sheets and the component graph $\mathcal C(O)$ are as in that note, and $\Lambda_T=2(1-\zeta)\Lambda$ is the token translation module.

- **Lifted state graph** $G(r)$: vertices $(y,j)\in\Lambda\times\mathbb Z/5$; an edge from $(y,j)$ to $(L(y),j\pm1)$ for each letter $L$ acting at $y$ at radius $r$ (the sign is that of the rotation of $L$). A *lattice orbit* at $r$ is a connected component of $G(r)$. The shift $(y,j)\mapsto(y,j+1)$ is an automorphism of $G(r)$ that preserves token edges, so every component is isomorphic to the lifted orbit of some $(y,0)$.
- **Internal translation.** For states $s_1,s_2$ of one orbit, every word taking $s_1$ to $s_2$ has the same map $z\mapsto\zeta^mz+t$: the sheets fix $m$, and then $t=y_2-\zeta^my_1$. Put $\tau(s_1,s_2)=|\sigma(t)|$. Composition gives $\tau(s_1,s_3)\le\tau(s_1,s_2)+\tau(s_2,s_3)$, and a single letter contributes $|\sigma(p(1-\zeta^{\mp1}))|=|1-\zeta^{\mp2}|=c=1.90211$. Let $\operatorname{diam}_VO=\sup\tau$ over pairs of states of $O$, and let $M(r)$ be the supremum of $\operatorname{diam}_VO$ over lattice orbits $O$ at $r$. This is the supremum of $|\sigma(t)|$ over word maps realised at lattice points, the quantity of `sharp-lower-bound-n5.md` Theorem 4.1(3). $D(r)$ is the supremum of $\operatorname{diam}\mathcal C(O)$ over lattice orbits.
- **Pieces, rim, rim graph.** Let $r<r'$. Every letter acting at $y$ at radius $r$ acts there at $r'$, so $G(r)$ is a subgraph of $G(r')$ on the same vertex set. Hence each lattice orbit $O'$ at $r'$ is partitioned exactly into components of $G(r)$, its *pieces*.
  - A *rim move* is an edge of $G(r')$ that is not in $G(r)$: a letter about $p=\mp1$ at a point $y$ with $r<|y-p|\le r'$ (a *rim point*). It moves $y$, since $y\ne p$.
  - The *rim graph* $\mathcal R(O')$ has the pieces as vertices and an edge between two different pieces joined by a rim move. It is connected, because $O'$ is. Write $R(O')=\operatorname{diam}\mathcal R(O')$, and let $R(r,r')$ be the supremum over lattice orbits $O'$ at $r'$.
  - A piece is a *singleton* if it is one state, that is, a point outside $D_1(r)\cup D_2(r)$.
  - $R_{\rm red}(O')$ is the largest rim distance between two non-singleton pieces.
- **Level radii.** $r_k^2=r_c^2-\varepsilon^k/10$, exactly $r_0^2=(29+10\varphi)/10$, $r_1^2=(33+8\varphi)/10$, $r_2^2=(17+18\varphi)/10$, $r_3^2=(85-24\varphi)/10$, $r_4^2=(-203+154\varphi)/10$. They are non-norm radii (`sharp-lower-bound-n5.md` Lemma 2.2(3)). $GG_5(r_0)$ is finite (certified).

## 2. Statements

**Theorem 1 (rim recursion).** Let $0<r<r'$, and let $O'$ be a lattice orbit at $r'$ with rim graph of diameter $\ell=R(O')$.
1. $\operatorname{diam}_VO'\le(\ell+1)M(r)+c\,\ell$. Hence $M(r')+c\le(R(r,r')+1)(M(r)+c)$.
2. $\operatorname{diam}\mathcal C(O')\le(\ell+1)D(r)+\ell$. Hence $D(r')+1\le(R(r,r')+1)(D(r)+1)$.
3. If $2\le r$ and $r'\le r_c$, both bounds hold with $\ell$ replaced by $R_{\rm red}(O')$, with the additive terms increased by $4c$ and $4$ respectively.

**[proved]**

**Theorem 2 (finiteness from one sequence).** Let $r_0<r_1<\cdots$ be non-norm radii with $r_k\to r_c$ and $GG_5(r_0)$ finite (for example the level radii), and let $R_k=R(r_{k-1},r_k)$.
1. If every $R_k$ is finite, then $GG_5(r)$ is finite for every $r<r_c$, and $M(r_k)+c\le(M(r_0)+c)\prod_{i\le k}(R_i+1)$.
2. If $R_k\le R$ for all $k$ along the level radii, then $M(r_k)\le(M(r_0)+c)(R+1)^k$, so $M(r)=O\bigl(\delta^{-\log(R+1)/\log\varphi^3}\bigr)$.

The same holds with $D$ in place of $M$ through Theorem 1(2), the (T) note's Corollary 5(2) and the lattice reduction. **[proved, given the cited results]**

**Proposition 3 (logical status).**
1. Along the level radii, "$R_k<\infty$ for all $k$" is equivalent to (B).
2. For every lattice orbit $O'$ at $r'$: $R(O')\ge(\operatorname{diam}_VO'-M(r))/(M(r)+c)$.

**[proved]**

Item 1 is the rim form of the remark after Theorem 1 of the transport note: a per-radius bound is (B) restated. Only a uniform bound, Conjecture 7, has content. Item 2 shows that the rim graph cannot stay small when the internal range grows by a large factor in one step. If $M\sim C/\delta$, a step of ratio $\rho$ forces $R\gtrsim1/\rho-1$. This agrees with the growth of rim graphs over a fixed base (Computation 4.3).

**Proposition 4 (anatomy of the rim).** Let $2\le r<r'\le r_c$, and let $O'$ be a lattice orbit at $r'$. Let $y$ be a rim point for $a$, so $\rho=|y+1|\in(r,r']$, and let $y_k=a^k(y)$, $k\in\mathbb Z/5$, with $\theta_k=\arg(y_k+1)=\theta_0'-72^\circ k$.
1. All $y_k$ are rim points for $a$, and their states $(y_k,j+k)$ lie in $O'$ and form a cycle of rim moves: the *rim cycle* of $y$.
2. Let $\cos\theta_0=(4+\rho^2-r^2)/(4\rho)$. Then $y_k\in D_2(r)$ iff $|\theta_k|\le\theta_0$, and $72^\circ<2\theta_0<144^\circ$. So exactly one or two $y_k$ lie in $D_2(r)$ (the *anchors*), and if two, they are consecutive: $y_k$ and $y_{k+1}=a(y_k)$ with $\theta_k\in[72^\circ-\theta_0,\theta_0]$.
3. An anchor lies in a piece with at least 5 states. Every other $y_k$ lies outside $D_1(r)\cup D_2(r)$, so its state is a singleton piece.
4. Two non-singleton pieces are adjacent in $\mathcal R(O')$ iff they contain the two anchors of a two-anchor cycle (an *essential edge*).
5. On a shortest path in $\mathcal R(O')$ between two non-singleton pieces, every maximal run of singleton pieces contains a *junction state*: a singleton lying on a rim cycle of $a$ and on one of $b$, hence a point outside $D_1(r)\cup D_2(r)$ and inside $D_1(r')\cap D_2(r')$.
6. Every singleton piece is within distance 2 of a non-singleton piece. Hence $R(O')\le R_{\rm red}(O')+4$.

The same holds for $b$ with the roles of the disks exchanged (apply $z\mapsto-z$, which exchanges $a$ and $b$ and keeps the rotation sense). As $r,r'\to r_c$, $72^\circ-\theta_0\to9.73^\circ=\arg(E+1)$ and $\theta_0\to62.27^\circ=\arg(\zeta-\zeta^4+1)$, and $a(E)=\zeta^4-\zeta$. So the upper anchors of essential $a$-edges lie in the crescent along the arc of $\partial D_1$ from the critical point $E$ to the cusp $\zeta-\zeta^4$, and the lower anchors along the arc from the cusp $\zeta^4-\zeta$ to $\bar E$. All four are among the 38 critical points of $r_c$. **[proved]**

**Proposition 5 (the gluing is one partial translation).** $a(z)=b(z)+v$ for all $z$, with $v=2(\zeta^{-1}-1)\in\Lambda_T$, and $b(z)=a(z)-v$. For an essential edge $y\mapsto a(y)$ with $y\in D_2(r)$, put $x=b(y)$. Then $(x,j+1)$ lies in the piece of $(y,j)$, and $a(y)=x+v$ lies in the same sheet. So the two anchors lie in one piece iff some word at radius $r$ maps $(x,j+1)$ to $(x+v,j+1)$, equivalently iff the translation germ $T_v$ at $x$ is realised in $GG_5(r)$. This holds in particular when $x$ and $x+v$ lie in one parent token component. **[proved]**

**Corollary 6 (one event).** Let the radius grow from $r$ to $r'$. At the radius $\rho=|y+1|$ the whole rim cycle of $y$ enters at once (and likewise for $b$). Each such cycle adds at most one edge between non-singleton pieces, and none if it has one anchor and no junction state. **[proved]**

**Conjecture 7 (uniform rim bound).** There is $R_0$ such that $R(r,r')\le R_0$ whenever $0<\delta\le1/10$ and $r_c^2-r'^2=\varepsilon\delta$. In the data $R_0=29$ (Computation 4.3). Along the level radii alone, it implies (B) by Theorem 2. **[conjecture]**

## 3. Proofs

### 3.1 Theorem 1

Let $s,t$ be states of $O'$, in pieces $P,Q$. Take a path $P=P_0,P_1,\dots,P_\ell=Q$ in $\mathcal R(O')$ with $\ell\le R(O')$, and rim moves $u_i\to v_i$ with $u_i\in P_{i-1}$, $v_i\in P_i$. Put $v_0=s$ and $u_{\ell+1}=t$.

*Item 1.* Each piece $P_i$ is a lattice orbit at $r$, up to the shift of $j$, which does not change $\tau$. So $\tau(v_i,u_{i+1})\le M(r)$. A rim move is one letter, so $\tau(u_i,v_i)=c$. The triangle inequality gives $\tau(s,t)\le(\ell+1)M(r)+c\ell$. Taking suprema, $M(r')\le(R+1)M(r)+cR$, which is the stated product form.

*Item 2.* Every token edge of $G(r)$ is one of $G(r')$, so each token component $K$ at $r$ lies in a unique token component $\iota(K)$ at $r'$. A connector at $r$ moves its point by a letter that also acts at $r'$, so the images of its two ends are equal or adjacent in $\mathcal C(O')$. Thus $\iota:\mathcal C(P_i)\to\mathcal C(O')$ does not increase distances, and $\operatorname{diam}\mathcal C(P_i)\le D(r)$. A rim move is a letter that moves its point at $r'$, so it changes the child component by at most one step. Hence the token components of $s$ and $t$ are within $(\ell+1)D(r)+\ell$. Taking suprema and adding 1 gives the product form.

*Item 3.* By Proposition 4(6), $s$ and $t$ are within 2 rim moves, through singletons, of states $s',t'$ in non-singleton pieces. Those are joined as above with $\ell\le R_{\rm red}(O')$. Each of the at most 4 extra moves costs $c$ in item 1 and $1$ in item 2. $\square$

### 3.2 Theorem 2

*Item 1.* $M(r_0)<\infty$ because $GG_5(r_0)$ is finite. By Theorem 1(1) and induction, $M(r_k)+c\le(M(r_0)+c)\prod_{i\le k}(R_i+1)<\infty$. Each $r_k$ is a non-norm radius, so `sharp-lower-bound-n5.md` Theorem 4.1 ((3)⇒(1)) gives finiteness of $GG_5(r_k)$. For $r<r_c$ choose $k$ with $r\le r_k$; group monotonicity (`boundary-contact.md` Theorem 3.4) gives finiteness at $r$. No hypothesis at radii off the sequence is used.

*Item 2.* At level $k$, $\delta=\varepsilon^k/10$, so $k=\log(1/(10\delta))/\log\varphi^3$ and $(R+1)^k=(10\delta)^{-\log(R+1)/\log\varphi^3}$.

For the $D$ form: $D(r_0)\le5|GG_5(r_0)|$, since a lifted orbit has at most 5 states per point and a graph has diameter less than its number of vertices. Theorem 1(2) then bounds $D(r_k)$, and at the non-norm radius $r_k$ a finite lattice $D(r_k)$ gives finiteness by the (T) note's Corollary 5(2) with Theorem 4.1 of `sharp-lower-bound-n5.md`, as in the component-graph note's Proposition 1(3). $\square$

### 3.3 Proposition 3

*Item 1.* "⇐" follows from Theorem 2. "⇒": if $GG_5(r_k)$ is finite, a lattice orbit at $r_k$ has at most $5|GG_5(r_k)|$ states, hence fewer pieces, and $R_k<5|GG_5(r_k)|$.

*Item 2* is Theorem 1(1) for the single orbit $O'$, solved for $\ell$. $\square$

### 3.4 Proposition 4

*Item 1.* $a$ is a rotation about $-1$, so $|y_k+1|=\rho$ for all $k$. Each $y_k$ is a rim point, and $a$ moves $(y_k,j+k)$ to $(y_{k+1},j+k+1)$ in $G(r')$. Since $a^5=1$, the states close up after five moves.

*Item 2.* For $z=-1+\rho e^{i\theta}$, $|z-1|^2=4+\rho^2-4\rho\cos\theta$, which is at most $r^2$ iff $\cos\theta\ge\cos\theta_0$. For $\rho\in(r,r']$ with $2\le r$ and $r'\le r_c$:
- $\cos\theta_0\ge1/\rho\ge1/r_c=0.4653>\cos72^\circ$;
- $\cos\theta_0\le(4+r'^2-r^2)/(4r)\le(4+r_c^2-4)/8=(3+\varphi)/8=0.5773<\cos36^\circ$.

So $2\theta_0\in(72^\circ,144^\circ)$. A closed arc of that length contains one or two points of a set spaced by $72^\circ$, and if two they are adjacent. $a$ turns by $-72^\circ$, so the upper anchor has $\theta_k$ and $\theta_k-72^\circ$ both in $[-\theta_0,\theta_0]$.

*Item 3.* An anchor $y_k$ lies in $D_2(r)$ and is not $+1$, because $|y_k+1|>r\ge2=|1+1|$. So $b$ acts at it at radius $r$ and moves it, and its piece contains the five states of its $b$-cycle. A non-anchor lies outside $D_2(r)$, and outside $D_1(r)$ since $\rho>r$. No letter acts there at radius $r$, so its state is a component of $G(r)$ by itself.

*Item 4.* A rim move between two non-singleton pieces starts and ends at points of one rim cycle that are both anchors. A move joins consecutive points of the cycle.

*Item 5.* Let $X,S_1,\dots,S_m,Y$ be such a run, with $X,Y$ non-singleton and no $S_i$ a junction. A singleton $S$ that is not a junction lies in one crescent only, say $r<|S+1|\le r'$ and $|S-1|>r'$. Then only $a^{\pm1}$ act at $S$ at radius $r'$, and all rim moves at $S$ stay in its $a$-cycle. So $X,S_1,\dots,S_m,Y$ lie on one cycle $C$, and $X,Y$ contain anchors of $C$.
- If $X=Y$, the run can be cut out of the path.
- Otherwise $C$ has two anchors, and the essential edge $X$–$Y$ has length $1<m+1$.

Either way the path was not shortest.

*Item 6.* In a cycle $A,S_1,S_2,S_3,S_4$ with one anchor, $S_1,S_4$ are at distance 1 from $A$ and $S_2,S_3$ at distance 2. In a cycle $A_1,A_2,S_1,S_2,S_3$ with two anchors, every $S_i$ is within 2 of an anchor. A singleton is a rim point, so it lies on some cycle; and a cycle always has an anchor. The bound on $R$ follows from the triangle inequality.

*The limit angles.* At $\rho=r=r_c$, $\cos\theta_0=1/r_c$. The point $\zeta-\zeta^4=2i\sin72^\circ$ satisfies $|\zeta-\zeta^4\pm1|^2=1+(2+\varphi)=3+\varphi$, so it is the upper cusp, at angle $\theta_0$ about $-1$. Next, $a(E)=-1+\zeta^{-1}(1+\zeta-\zeta^2)=\zeta^{-1}-\zeta$, the lower cusp at angle $-\theta_0$. So $E$ lies at angle $72^\circ-\theta_0$, and $|E+1|^2=3+\varphi$. $\square$

### 3.5 Proposition 5 and Corollary 6

$a(z)-b(z)=(-1+\zeta^{-1}(z+1))-(1+\zeta^{-1}(z-1))=2(\zeta^{-1}-1)$. Since $\zeta^{-1}-1=\zeta^{-1}(1-\zeta)$, $v\in2(1-\zeta)\Lambda=\Lambda_T$.

An anchor $y$ of an $a$-cycle lies in $D_2(r)$, so $b$ acts at $y$ at radius $r$, and $(b(y),j+1)$ is in the piece of $(y,j)$. Then $(a(y),j+1)=(b(y)+v,j+1)$. A word taking $(x,j+1)$ to $(x+v,j+1)$ keeps the sheet, so its map is $z\mapsto z+v$. Token paths are sheet-preserving with translations in $\Lambda_T$, which gives the special case.

The corollary restates Proposition 4(1), (4) and (5): a cycle has at most two anchors, and they are consecutive. $\square$

## 4. Computations

All orbit, piece, rim and graph decisions are exact. Points are integer 4-vectors, and disk tests are the exact sign of an element of $\mathbb Z[\varphi]$, computed with 128-bit integers. Angles and $|\sigma y|$ are double-precision evaluations of exact points, used only to bin and to report. Diameters and radii of rim graphs are exact: breadth-first search from every vertex. Orbit sizes agree with the engine and with the earlier notes ($30\,165$; $400\,519$; $5\,673\,561$; $76\,031\,321$ for the orbit of $0$ at levels 1–4; the engine gives the same at levels 1–3).

### 4.1 Named orbits (step ratio $\varepsilon$)

The child is the orbit at the level or radius named; the parent radius is one $\varepsilon$-step larger in defect. "Ess." is the number of essential edges between different pieces, $J$ the number of junction states.

| child | states | pieces | non-singleton | largest piece | rim states | $R$ | radius | $R_{\rm red}$ | ess. | $J$ |
|---|---|---|---|---|---|---|---|---|---|---|
| $0$, level 1 | 30 165 | 449 | 27 | 5 242 | 654 | 12 | 6 | 8 | 44 | 6 |
| $0$, level 2 | 400 519 | 1 307 | 83 | 62 163 | 1 944 | 14 | 7 | 10 | 108 | 6 |
| $0$, level 3 | 5 673 561 | 4 815 | 361 | 803 274 | 7 074 | 14 | 7 | 10 | 392 | 6 |
| $0$, level 4 | 76 031 321 | 14 991 | 1 135 | 11 329 798 | 21 964 | **14** | 7 | 10 | 1 152 | 6 |
| $E$, levels 1–4 | 20 424 … 45 941 440 | 301 … 9 069 | | | | 10, 11, 10, 10 | 6, 6, 7, 7 | | | |
| $-\zeta^2$, levels 1–4 | 62 095 … 46 195 574 | 1 025 … 9 219 | | | | 16, 11, 18, 11 | 11, 6, 12, 6 | | | |
| $1/55$ witness ($\delta'=1/55$) | 111 107 | 1 177 | | 5 503 | | 26 | 13 | | | |
| rows 6, 7, 8 ($\varepsilon/55$, $\varepsilon/55$, $\varepsilon^2/55$) | 1.45, 1.47, 20.1 M | 3 784, 3 868, 12 857 | | | | 24, 24, 24 | 12 | | | |
| $1/30$ witness, row 10, $\varepsilon^2/30$ | 54 210; 747 936; 9 929 377 | 1 326; 3 600; 11 488 | | | | 18, 22, 22 | 12, 13, 13 | | | |

On the orbit of $0$ the parent orbit of $0$ is the unique centre at levels 1, 3, 4, and one of three at level 2. The diametral path runs symmetrically through it under $z\mapsto-z$. Its essential edges sit next to $E$, the cusps and their mirror images, and its ends are the middle singletons of pendant rim cycles in the outer region (for example at $-2.138-1.822i$). Seeds: $E=(0,1,-1,0)$, $-\zeta^2=(0,0,-1,0)$, and the $1/55$ and $1/30$ seeds of the chaining note's Computation 4.

### 4.2 The anatomy on data

On every orbit run with the cycle analysis (the named orbits and about $1\,200$ random children of §4.3):
- every rim cycle has one or two anchors;
- the anchors are exactly the points of the cycle in the other disk at radius $r$, with no mismatch between the geometric test and the piece size;
- $R-R_{\rm red}\le4$.

The orbit of $0$ has $2\cdot50$, $2\cdot165$, $2\cdot602$, $2\cdot1\,857$ two-anchor cycles at levels 1–4. Of their essential edges, $56$, $222$, $812$, $2\,562$ are internal to one piece. Among the internal ones at levels 2 and 3, $134$ of $222$ and $454$ of $812$ are internal already through one parent token component joining $b(y)$ and $b(y)+v$ (Proposition 5); the others go through longer parent words. The essential edges between pieces lie at the following angles $\arg(y+1)$, mirrored under $\theta\mapsto72^\circ-\theta$ (level 4; levels 2 and 3 have the same windows):

$[9.75,10.13]$ (20 edges), $[10.80,10.93]$ (25), $[11.33,11.43]$ (13), $[14.26,14.97]$ (87), $[16.72,16.80]$ (18), $[24.01,24.61]$ (52), $[25.27,25.89]$ (73).

None lies in $[29^\circ,43^\circ]$, where 621 essential edges are all internal. The critical points on this arc are $E$ ($9.73^\circ$), $0.927+0.951i$ ($26.3^\circ$), $0.5+1.539i$ ($45.7^\circ$) and the cusp ($62.27^\circ$). Only the first and last windows touch critical points. In the windows, small parent orbits (17, 40, 155 and 596 states, recurring at every level) are glued directly to large pieces, and the large pieces to each other next to $E$ and the cusp.

### 4.3 Random child orbits

Child seeds as in the atlas note §4.5:
- a physical point uniform in $D_1\cup D_2$ at the child radius;
- an internal point uniform of modulus at most $25/\delta'$, or $8/\delta'$ in two batches, rounded to $\Lambda$;
- children with more than 40 states, distinct by (states, pieces, largest piece).

Parent defect $\delta=p/q$, parent $r^2=3+\varphi-\delta$, child $r'^2=3+\varphi-\rho\delta$ exactly.

| ratio $\rho$ | parent defects | children | with $\ge10^4$ states | max $R$ |
|---|---|---|---|---|
| $\varepsilon$ | 30, from $1/400$ to $1/10$ | 1 573 | 709 | **29** |
| $\varepsilon^2$ | $1/16,1/30,1/55,1/100$ | 191 | 102 | 84 |
| $\varphi^{-2}$ | same four | 116 | 58 | 16 |
| $1/2$ | same four | 112 | 55 | 20 |
| $\varphi^{-1}$ | same four | 123 | 43 | 11 |
| $9/10$ | same four | 115 | 34 | 8 |
| $99/100$ | same four | 111 | 43 | 4 |

The maximum of $R$ per parent defect for ratio $\varepsilon$:

| $\delta$ | max $R$ | $\delta$ | max $R$ | $\delta$ | max $R$ |
|---|---|---|---|---|---|
| $1/10$ | 18 | $1/26$ | 28 | $1/55$ | 24 |
| $1/12$ | 18 | $1/28$ | 24 | $1/60$ | 16 |
| $4/55$ | 15 | $1/30$ | **29** | $1/70$ | 26 |
| $1/14$ | 16 | $1/35$ | 21 | $1/80$ | 17 |
| $1/16$ | 20 | $3/80$ | 22 | $1/100$ | 14 |
| $1/18$ | 20 | $2/55$ | 12 | $1/120$ | 14 |
| $3/55$ | 17 | $1/40$ | 20 | $1/150$ | 22 |
| $1/20$ | 26 | $2/45$ | 18 | $1/200$ | 19 |
| $1/22$ | 18 | $1/45$ | 18 | $1/250$ | 16 |
| $1/25$ | 14 | $1/50$ | 21 | $1/400$ | 15 |

There are 224 children at $1/30$ and 180 at $1/26$; the other defects have 33–122 each. Junction states number at most 20 for ratio $\varepsilon$ (up to 293 for $\varepsilon^2$, whose rim is wider).

*Adversarial chains.* The worst child is at $1/30$: seed $(1729,1258,292,2329)$, $711\,317$ states, $R=29$. Its $\varepsilon$-child, seed $\varepsilon\cdot$seed, $9\,637\,204$ states, has $R=29$. The child at $1/20$ with seed $(-485,28,-316,-272)$ ($R=26$) continues $16$ ($2.59\cdot10^6$ states), then $18$ ($3.68\cdot10^7$ states).

*Fixed base.* With the parent fixed at level 0, the orbit of $0$ at levels 1, 2, 3 has $R=12,38,164$ (non-singleton pieces $27$, $483$, $7\,511$). With the parent at level 1, levels 2 and 3 give $14,40$. The growth factor is about $\varphi^3$ per level, as Proposition 3(2) requires if $M\sim1/\delta$.

### 4.4 Transport by $\varepsilon$

For the orbit of $0$, map each piece $P$ of the level-$k$ child (an $r_{k-1}$-orbit) to the level-$(k+1)$ piece containing the most states $(\varepsilon y,j)$, $(y,j)\in P$, using the sheet-preserving lift.

| pair | image fraction | rim depth of non-singleton pieces, $d_k(P)\to d_{k+1}(\text{image})$ | non-singleton pieces of level $k+1$ at distance 0 / 1 / 2 from images |
|---|---|---|---|
| $1\to2$ | 0.679 | never increases (e.g. $1\to0$: 4, $4\to3$: 4) | 35 / 36 / 12 |
| $2\to3$ | 0.680 | never increases | 75 / 218 / 68 |
| $3\to4$ | 0.680 | never increases (e.g. $4\to3$: 118, $5\to3$: 16) | 227 / 868 / 40 |

### 4.5 Events

`tdcsg-orbit thresholds` from level $k$ to level $k+1$ for the orbit of $0$ finds 9, 22 and 83 exact thresholds ($k=0,1,2$). The final orbits are $30\,165$, $400\,519$ and $5\,673\,561$ points, as above. So the orbit of the seed absorbs the other pieces in a growing number of events, while the rim depth stays at most 7. The rim states grow by factors $3.0$, $3.6$, $3.1$ per level: they are lattice points of an annulus of width about $0.18\delta$ with internal coordinates up to about $6.5/\delta$, which is about $1/\delta$ of them. A count of events cannot give a uniform bound.

## 5. Attempts at a uniform bound, and where each stops

- **(a) Tight points and the golden rotation.** The hope was that rim gluing happens in $O(\delta)$-neighbourhoods of the tight points, where the scaled dynamics is the golden rotation (the chaining note's Proposition 2, the fence of the (T) note). It does not. Proposition 4 places the essential edges on the arc between $E$ and the cusp, and the data place the gluing between pieces in seven windows per quarter-arc of *fixed* length (up to $0.7^\circ$, about $47\delta$ at level 4). Only two of them touch tight points. The scaled picture at $E$ describes the end of the chord, not these windows. The route fails as stated.
- **(b) A hub.** There is no hub: the largest piece is adjacent to about $9\%$ of the pieces, and the centre of the rim graph is at eccentricity 7. The tube version would need two inputs:
  1. every parent orbit has a state within boundedly many parent connectors of the chord tube;
  2. the tube states of different pieces near $E$ are glued by the rim in boundedly many steps.

  Input 1 is a (K)-type uniform statement for the parent, computed but not proved (component-graph note, Computation 4.4). Input 2 is about the chord-line model set near $E$, itself open (idea 35). So the route needs the old difficulty as an input.
- **(c) Induction over events.** Corollary 6 controls one event: each entering rotation cycle merges at most two non-singleton classes. But the number of essential edges between pieces grows like $1/\delta$ (44, 108, 392, 1 152), and the depth stays bounded only because of where those edges fall. No potential was found that stays bounded as the radius sweeps from $r$ to $r'$. Distances only shrink as edges are added, but classes far from the seed's class are joined to it only near the end of the sweep. A potential would have to know which parent orbits the later events join, which is the global information again.
- **(d) Renormalizing the rim graph by $\varepsilon$.** Computation 4.4 is the rim analogue of (R1) and (R2): rim depth does not increase under the plurality map, and new pieces lie within 2 rim steps of images. If both halves were proved, rim depth would grow by at most 2 per level and $R_k=O(k)$, which suffices for (B) by Theorem 2. But the coverage half is a reverse-type statement about all parent orbits meeting the gluing windows, of the same kind as (R2) and (A6).

**The common obstruction.** Propositions 4 and 5 reduce the rim graph to two ingredients:
- the partition of the thin gluing crescents into parent orbits;
- the partial translation $T_v$, plus $O(1)$ junctions in the data.

A uniform bound needs that every parent orbit meeting a window is linked to the seed's orbit in boundedly many $T_v$-steps. Which parent orbits meet a window, and at which internal coordinates, is a property of the whole parent system: the windows are fixed arcs, but they are met at all internal coordinates up to $C/\delta$. So the statement is global and reverse-type, the same uniform bound that ended the transport, component-graph and atlas notes. The referees warned that each reformulation so far ended there, and this one does too.

## 6. Assessment

- **Formulation: settled.** The rim recursion is proved in a form that needs neither (T) nor the component graph (Theorem 1(1)). One geometric sequence of non-norm radii from a certified base suffices (Theorem 2). A per-step bound is equivalent to (B) (Proposition 3), so only Conjecture 7 has content. A uniform $R$ gives a polynomial bound on $M$, not Conjecture A, and larger steps give better exponents ($\log30/\log\varphi^3=2.36$ for ratio $\varepsilon$ with $R=29$; $\log85/\log\varphi^6=1.54$ for $\varepsilon^2$ with $R=84$).
- **Structure: proved and sharp.** Parent orbits are glued only along the two arcs of the lens boundary, by one partial translation by $v\in\Lambda_T$, plus junctions at the cusps. Each rotation cycle contributes at most one gluing.
- **Uniformity: strongly supported, not proved.** $R\le29$ on $1\,573$ $\varepsilon$-step children at 30 radii and on every named orbit. There is no growth from $\delta=1/10$ to $1/400$, and none along the $\varepsilon$-chains tested, up to $7.6\cdot10^7$ states.
- **Overall: repairable in principle, not closed.** The difficulty is (K) in a new form, localized to a curve times internal space. That is a cleaner target than (A5)–(A6), but no route found here proves it. The most concrete next steps are recorded in `../ideas.md`:
  - describe the seven gluing windows exactly, and test whether they are arcs of the cut set at $r_c$;
  - describe the gluing sites as a model set in (angle, rescaled internal coordinate);
  - the rim form of (R1)/(R2) with additive growth.

## 7. Reproduction

Throwaway C and Python programs in the session scratch folder (`lineRim/`), not committed. They use the exact arithmetic layer of the atlas referee (`z5.h`: $\mathbb Z[\zeta]$ in the basis $1,\zeta,\zeta^2,\zeta^3$, $|x|^2=P+Q\varphi$, exact sign of $\alpha+\beta\varphi$ with 128-bit integers; $a$ multiplies by $\zeta^{-1}$ about $-1$; tokens $AABAB$, $ababb$, $abaBAB$ and their images).

- `rim` (`rim P0 P1 PD C0 C1 CD s0 s1 s2 s3 cap prefix`, with $r^2=(P_0+P_1\varphi)/P_D$ and $r'^2=(C_0+C_1\varphi)/C_D$):
  - lifted breadth-first search of the child orbit of $(s,0)$ at $r'$, with an open-addressing hash;
  - pieces by breadth-first search with the letters acting at $r$, checking that every move stays in the child (orbit monotonicity);
  - rim moves (acting at $r'$, not at $r$) between pieces, deduplicated into the rim graph;
  - exact eccentricity of every vertex: diameter, radius, centres, distances from the largest piece, degrees, a diametral path with its rim moves;
  - angle histograms; dumps of pieces and rim moves.
- `rim2`: `rim` plus the cycle analysis of Proposition 4 (for each rim cycle, listed once from its least-index state: the anchors by piece size, checked against the geometric test in the other disk; the essential edges with angle, depth and $|\sigma y|$; junction states) and $R_{\rm red}$ by breadth-first search from every non-singleton piece. `rim3`: `rim2` plus parent token components (union-find over the twelve tokens at $r$), to test $b(y)\sim b(y)+v$ (§4.2).
- `rmap`: both child orbits with pieces and rim graphs; the plurality map of pieces under $y\mapsto\varepsilon y$ with the sheet-preserving lift; rim distances from the seed piece before and after; multi-source distances from image pieces (§4.4).
- `gen` (the chaining note's seed generator: physical point uniform in $D_1\cup D_2$, internal point uniform in a disk, rounded through the inverse Minkowski matrix), `drv.py`/`drv2.py` (exact radii for ratios $\varepsilon=2\varphi-3$, $\varepsilon^2=13-8\varphi$, $\varphi^{-1}=\varphi-1$, $\varphi^{-2}=2-\varphi$, $1/2$, $9/10$, $99/100$; five parallel runs; deduplication), `campaign*.sh` (generator seeds 101–138, 301–316, 501–505).
- Engine (a copy of `tdcsg-orbit`): `orbit -n 5 --r2 pow:33/10,0,-4/5,-4/5` (level 1, $30\,165$ points), and `thresholds -n 5 --from L_k --upto L_{k+1}` with $L_k$ in the power basis (for example level 2 is `pow:17/10,0,-9/5,-9/5`).
- Resources: level 4 used 2.9 GB and 25 s; at most 5 processes at once.

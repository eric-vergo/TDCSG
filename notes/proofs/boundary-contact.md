# Orbit monotonicity and boundary contact in two-disk systems

Authors: Eric Vergo, Claude

**Result and status.** For arbitrary rotation orders $n_1,n_2\ge1$ and closed disks of common radius $r$ centred at $\mp1$, we prove the following.
- **(Monotonicity)** The orbit $O_r(p)$ of every point is non-decreasing in $r$ *as a set*, and finiteness of the group $GG_{n_1,n_2}(r)$ is monotone: if it is finite at $r'$ it is finite at every $r\le r'$. So the critical radius is well defined.
- **(Stability)** A finite orbit stays unchanged for radii slightly above, so for each point the set of radii with an infinite orbit is either empty or a closed half-line $[r^*(p),\infty)$.
- **(Boundary contact)** At $r^*(p)$ the infinite orbit either contains a point lying exactly on a boundary circle, or has, for every $\varepsilon>0$, infinitely many points strictly inside a disk within $\varepsilon$ of its boundary, and therefore an accumulation point on a boundary circle.

**Status: all three are proved.** The paper's stated *reason* for monotonicity ("all group elements that affect it are still available") is **imprecise**. Read at the level of group words it is false: the same word acts differently at different radii, and there is no generator-preserving homomorphism between the groups at two radii (Example 3.2). Its intended meaning, that every move applied to the point is still applicable, is made rigorous by the chain argument of Theorem 3.1. The proofs have been independently refereed. The report is `referee-report-thread1.md` in this directory, and §10 records its verdicts and what it did not check.

The boundary-contact theorem does **not** say *where* the contact occurs. It does not show that the specific limit point used in the paper's closed-form radii lies on a boundary circle. It does not decide which alternative of the dichotomy occurs. And it does not show that the group-level critical radius has an infinite orbit (the paper's footnote 4). These remain open (§10).

---

## 1. Setting

Fix $n_1,n_2\ge1$, $\zeta_k=e^{-2\pi\mathrm i/n_k}$, $c_1=-1$, $c_2=1$. The global rotations are $A(z)=c_1+\zeta_1(z-c_1)$ and $B(z)=c_2+\zeta_2(z-c_2)$. No arithmetic condition on $n_1,n_2$ is used anywhere in this note.

**Definition 1.1.** For a radius pair $\boldsymbol r=(r_1,r_2)$ with $r_k>0$:
- $D_k(\boldsymbol r)=\{|z-c_k|\le r_k\}$, closed disks;
- $a_{\boldsymbol r}=A$ on $D_1(\boldsymbol r)$ and $\mathrm{id}$ elsewhere; $b_{\boldsymbol r}=B$ on $D_2(\boldsymbol r)$ and $\mathrm{id}$ elsewhere;
- $G_{\boldsymbol r}=\langle a_{\boldsymbol r},b_{\boldsymbol r}\rangle\le\mathrm{Sym}(\mathbb C)$;
- $O_{\boldsymbol r}(p)=G_{\boldsymbol r}\,p$.

For equal radii write $r$ for $(r,r)$. Pairs are ordered coordinatewise: $\boldsymbol r\le\boldsymbol r'$ iff $r_1\le r_1'$ and $r_2\le r_2'$.

Since $A(D_1)=D_1$, each $a_{\boldsymbol r}$ is a bijection, and $a_{\boldsymbol r}^{-1}=A^{-1}$ on $D_1(\boldsymbol r)$ and $\mathrm{id}$ elsewhere; similarly for $b$. Write $S_{\boldsymbol r}=\{a_{\boldsymbol r}^{\pm1},b_{\boldsymbol r}^{\pm1}\}$.

---

## 2. Orbits as chains

**Lemma 2.1 (step lemma).** For $z\in\mathbb C$ and $\varepsilon=\pm1$:
- $a^\varepsilon_{\boldsymbol r}(z)=A^\varepsilon(z)$ if $|z-c_1|\le r_1$, and $a^\varepsilon_{\boldsymbol r}(z)=z$ otherwise;
- likewise $b^\varepsilon_{\boldsymbol r}(z)=B^\varepsilon(z)$ if $|z-c_2|\le r_2$, and $z$ otherwise.

*Proof.* This is the definition, together with the description of the inverse in §1. $\square$

**Definition 2.2.** An $\boldsymbol r$-*chain* from $p$ to $y$ is a finite sequence $p=z_0,z_1,\dots,z_\ell=y$ such that each $z_j=s_j(z_{j-1})$ for some $s_j\in S_{\boldsymbol r}$. A step is *trivial* if $z_j=z_{j-1}$.

**Lemma 2.3.** $y\in O_{\boldsymbol r}(p)$ if and only if there is an $\boldsymbol r$-chain from $p$ to $y$. If there is one, there is one with no trivial steps. Every non-trivial step $z_{j-1}\mapsto z_j$ of an $\boldsymbol r$-chain satisfies one of:
- $z_j=A^{\pm1}(z_{j-1})$ and $|z_{j-1}-c_1|\le r_1$;
- $z_j=B^{\pm1}(z_{j-1})$ and $|z_{j-1}-c_2|\le r_2$.

*Proof.* Every element of $G_{\boldsymbol r}$ is a word in $S_{\boldsymbol r}$, and applying a word to $p$ letter by letter produces a chain. Conversely a chain from $p$ to $y$ gives the word $s_\ell\cdots s_1$ mapping $p$ to $y$. Deleting trivial steps leaves a chain. The description of non-trivial steps is Lemma 2.1. $\square$

---

## 3. Monotonicity

**Theorem 3.1 (orbit monotonicity).** If $\boldsymbol r\le\boldsymbol r'$, then $O_{\boldsymbol r}(p)\subseteq O_{\boldsymbol r'}(p)$ for every $p$. In particular $|O_{\boldsymbol r}(p)|\le|O_{\boldsymbol r'}(p)|$.

*Proof.*
1. Let $y\in O_{\boldsymbol r}(p)$ and take an $\boldsymbol r$-chain from $p$ to $y$ without trivial steps (Lemma 2.3).
2. Consider a step $z_j=A^{\pm1}(z_{j-1})$ with $|z_{j-1}-c_1|\le r_1$. Then $|z_{j-1}-c_1|\le r_1'$, so $a^{\pm1}_{\boldsymbol r'}(z_{j-1})=z_j$ by Lemma 2.1. Steps through $B$ are handled the same way.
3. So the same sequence is an $\boldsymbol r'$-chain, and $y\in O_{\boldsymbol r'}(p)$. $\square$

The argument deletes the trivial steps first. That deletion is the essential point, and Example 3.2 shows why it is needed.

**Example 3.2 (the paper's justification is imprecise).** Take $n_1=n_2=4$, so $\zeta_k=-\mathrm i$, and $p=-1+\mathrm i/2$. Then $A(p)=-1+(-\mathrm i)(\mathrm i/2)=-\tfrac12$, and $|-\tfrac12-c_2|=\tfrac32$.
- At $r=1$: $p\in D_1$ and $-\tfrac12\notin D_2$, so $(b_1\circ a_1)(p)=-\tfrac12$.
- At $r=2$: $(b_2\circ a_2)(p)=B(-\tfrac12)=1+(-\mathrm i)(-\tfrac32)=1+\tfrac32\mathrm i$.

So the word $b\circ a$, which carries $p$ to $-\tfrac12$ at $r=1$, does not do so at $r=2$. The point $-\tfrac12$ is still in $O_2(p)$, but it is reached by the shorter word $a$.

More strongly, there is in general no homomorphism $G_r\to G_{r'}$ with $a_r\mapsto a_{r'}$, $b_r\mapsto b_{r'}$.
- For $r<1$ the disks are disjoint, so $[a_r,b_r]=\mathrm{id}$.
- For $r'=5$, the chain $0\xrightarrow{b^{-1}}1-\mathrm i\xrightarrow{a^{-1}}2\mathrm i\xrightarrow{b}3+\mathrm i\xrightarrow{a}-4\mathrm i$ uses only points inside the relevant disk: $|0-1|=1$, $|2-\mathrm i|=\sqrt5$, $|2\mathrm i-1|=\sqrt5$, $|4+\mathrm i|=\sqrt{17}$, all $\le5$. So $[a_5,b_5](0)=a_5b_5a_5^{-1}b_5^{-1}(0)=-4\mathrm i\neq0$.

So, read word by word, "all group elements that affect it are still available" is false. The charitable reading is that every individual move $z\mapsto A^{\pm1}z$ or $z\mapsto B^{\pm1}z$ applied along the way stays applicable at the larger radius. That reading is correct, and it is exactly the chain argument of Theorem 3.1.

To pass from orbits to the group we need the following lemma. It is also proved, in the same words, in `theorem1-converse.md` (Proposition 4.2).

**Proposition 3.3.** Let $G$ be a group of bijections of a set $X$ generated by $k$ elements. Then $G$ is finite if and only if its orbits have uniformly bounded size.

*Proof.* If $G$ is finite, every orbit has at most $|G|$ points. Conversely, suppose every orbit has at most $N$ points.
1. Let $\pi\colon F_k\to G$ be the surjection from the free group. For $x\in X$ the subgroup $H_x=\pi^{-1}(\mathrm{Stab}(x))$ has index $|Gx|\le N$.
2. A subgroup $H$ of index $j$ is the stabilizer of the coset $H$ for the left action $F_k\to\mathrm{Sym}(F_k/H)\cong\mathrm{Sym}(j)$. That action is determined by the images of the $k$ generators. So $F_k$ has at most $(j!)^k$ subgroups of index $j$, and finitely many of index at most $N$.
3. Since $G$ consists of bijections of $X$, $\ker\pi=\bigcap_xH_x$. This is an intersection of finitely many distinct finite-index subgroups.
4. Using $[F:H\cap H']\le[F:H][F:H']$, the intersection has finite index. So $G\cong F_k/\ker\pi$ is finite. $\square$

**Theorem 3.4 (group monotonicity).** If $\boldsymbol r\le\boldsymbol r'$ and $G_{\boldsymbol r'}$ is finite, then $G_{\boldsymbol r}$ is finite.

*Proof.* By Theorem 3.1, $|O_{\boldsymbol r}(p)|\le|O_{\boldsymbol r'}(p)|\le|G_{\boldsymbol r'}|$ for every $p$. Apply Proposition 3.3 to $G_{\boldsymbol r}$. $\square$

**Definition 3.5 (critical radii, equal radii).** Let
- $\mathcal F=\{r>0: G_r\text{ finite}\}$;
- $\mathcal I=\{r>0:G_r\text{ has an infinite orbit}\}$;
- $\mathcal I(p)=\{r>0:O_r(p)\text{ infinite}\}$.

By Theorems 3.1 and 3.4, $\mathcal F$ is a down-set. It is an interval $(0,r_c)$ or $(0,r_c]$, or all of $(0,\infty)$, in which case $r_c=\infty$; this happens for $n_1,n_2$ both dividing 4 or both dividing 6, by `theorem1-converse.md`. $\mathcal I$ and each $\mathcal I(p)$ are up-sets. Define $r_c=\sup\mathcal F$, $r_c^{\rm orb}=\inf\mathcal I$, and $r^*(p)=\inf\mathcal I(p)$ (each is $+\infty$ when the set is empty, and $\sup\emptyset=0$).

**Corollary 3.6.** The following hold.
1. $r_c\le r_c^{\rm orb}\le r^*(p)$ for every $p$. The first inequality holds because an infinite orbit forces an infinite group, and the second because $\mathcal I(p)\subseteq\mathcal I$.
2. $\mathcal I=\bigcup_p\mathcal I(p)$.
3. For $r>r_c$ the group $G_r$ is infinite. So the paper's statement that $GG_n$ "can never go from infinite to finite as $r$ increases" is **true** (Theorem 3.4), although its argument is imprecise (Example 3.2).
4. By Proposition 3.3, $G_r$ is infinite exactly when its orbit sizes are unbounded. Whether "unbounded" can occur with every orbit finite, that is whether $r_c<r_c^{\rm orb}$ is possible, is the paper's open question and is not settled here.

Since $G_r$ is finite for $r<1$ (disjoint disks), $r_c\ge1$.

---

## 4. Stability of finite orbits (closed disks)

**Theorem 4.1.** Suppose $S=O_{r_0}(p)$ is finite. Let
$$\delta=\min\{\,|y-c_k|-r_0:\ y\in S,\ k\in\{1,2\},\ |y-c_k|>r_0\,\},$$
with $\delta=+\infty$ if the set is empty, so that $\delta>0$. Then $O_r(p)=S$ for every $r\in[r_0,r_0+\delta)$.

*Proof.*
1. *Same disk membership.* Let $r\in[r_0,r_0+\delta)$, $y\in S$ and $k\in\{1,2\}$. If $|y-c_k|\le r_0$, then $|y-c_k|\le r$. If $|y-c_k|>r_0$, then $|y-c_k|\ge r_0+\delta>r$. So $y\in D_k(r)\iff y\in D_k(r_0)$.
2. *$S$ is invariant at radius $r$.* By Lemma 2.1, each $s_r\in S_r$ agrees on $S$ with the corresponding $s_{r_0}\in S_{r_0}$. Now $s_{r_0}$ maps $S$ into $S$, because $S$ is a $G_{r_0}$-orbit. So $s_r(S)\subseteq S$. Since $s_r$ is injective and $S$ is finite, $s_r(S)=S$.
3. *Conclusion.* Hence $O_r(p)\subseteq S$, as $S$ is invariant under all of $S_r$ and contains $p$. Theorem 3.1 gives $S\subseteq O_r(p)$. $\square$

Closedness is used in step 1: a point with $|y-c_k|=r_0$ is in $D_k(r_0)$ and stays in $D_k(r)$.

**Corollary 4.2 (the per-point critical radius is attained).** For every $p$, either $\mathcal I(p)=\emptyset$ or $\mathcal I(p)=[r^*(p),\infty)$. In other words, $O_{r^*(p)}(p)$ is infinite.

*Proof.* First, $r^*(p)\ge1>0$, so $O_{r^*(p)}(p)$ is defined: for $r\le1$ the disks are disjoint or tangent, and every orbit is finite (Proposition 7.1 of `theorem1-converse.md`). $\mathcal I(p)$ is an up-set (Theorem 3.1). Suppose $r^*=r^*(p)<\infty$ and $O_{r^*}(p)$ were finite. Then Theorem 4.1 gives $O_r(p)=O_{r^*}(p)$, finite, for all $r\in[r^*,r^*+\delta)$. That contradicts $r^*=\inf\mathcal I(p)$. $\square$

**Remark 4.3 (footnote 4 of the paper).** The paper believes, without proof, that the group is infinite *at* the critical radius. Corollary 4.2 is the per-point version, and it is proved. The group-level version does not follow.
- The number $\delta$ in Theorem 4.1 depends on $p$, so a uniform orbit bound at $r_0$ does not give one at $r_0+\delta$.
- Similarly, $r_c^{\rm orb}=\inf_p r^*(p)$ need not be attained by any single $p$.

Both "$r_c\notin\mathcal F$" and "$r_c^{\rm orb}\in\mathcal I$" remain **open**.

---

## 5. Boundary contact

For $y\in\mathbb C$ and $k$ with $y\in D_k(r_0)$, the *inner depth* of $y$ in disk $k$ is $d_k(y)=r_0-|y-c_k|\ge0$.

**Theorem 5.1 (boundary contact).** Suppose $O=O_{r_0}(p)$ is infinite and $O_r(p)$ is finite for some sequence of radii $r\uparrow r_0$, $r<r_0$. By Theorem 3.1 this is equivalent to "$O_r(p)$ is finite for all $r<r_0$", and by Corollary 4.2 to "$r_0=r^*(p)$". Then:

1. $\inf\{d_k(y): y\in O,\ k\in\{1,2\},\ y\in D_k(r_0)\}=0$.
2. Consequently at least one of the following holds:
   - **(B)** some orbit point lies exactly on a boundary circle: $O\cap(\partial D_1(r_0)\cup\partial D_2(r_0))\neq\emptyset$;
   - **(A)** for every $\varepsilon>0$, infinitely many $y\in O$ satisfy $r_0-\varepsilon<|y-c_k|<r_0$ for some $k$. In this case there are $k$ and $y^*\in\partial D_k(r_0)$ with $y^*$ a limit of distinct orbit points lying in the open disk $\{|z-c_k|<r_0\}$.
3. If (B) fails, then (A) holds, $O=\bigcup_{r<r_0}O_r(p)$, and $|O_r(p)|\to\infty$ as $r\uparrow r_0$.

*Proof.*
1. *Part 1.* Suppose the infimum is $\Delta>0$ and fix $r\in(r_0-\Delta,r_0)$. For $y\in O$:
   - if $y\in D_k(r_0)$, then $|y-c_k|=r_0-d_k(y)\le r_0-\Delta<r$, so $y\in D_k(r)$;
   - if $y\notin D_k(r_0)$, then $|y-c_k|>r_0>r$, so $y\notin D_k(r)$.

   So membership of orbit points is the same at $r$ and at $r_0$. Take any $y\in O$ and an $r_0$-chain from $p$ to $y$. All its points lie in $O$, so by Lemma 2.1 each step is also a step of an $r$-chain. Hence $O\subseteq O_r(p)$, and $O_r(p)$ is infinite. By monotonicity this holds for every $r\in(r_0-\Delta,r_0)$, contradicting the hypothesis.
2. *Part 2.* The infimum $0$ is either attained or not. If it is attained, some $y\in O$ has $d_k(y)=0$, that is $y\in\partial D_k(r_0)$: case (B). If it is not attained, every $\varepsilon>0$ admits infinitely many pairs $(y,k)$ with $0<d_k(y)<\varepsilon$. (A set of positive reals with infimum $0$ that is not attained has infinitely many elements below every $\varepsilon$.) Each $y$ occurs in at most two pairs, so there are infinitely many such $y$. Choose distinct $y_j$ with $0<d_{k_j}(y_j)\to0$. Pass to a subsequence with constant $k_j=k$, and then, by compactness of $D_k(r_0)$, to a convergent one with limit $y^*$. Then $|y^*-c_k|=r_0$, and the $y_j$ are distinct points of the open disk converging to $y^*$: case (A).
3. *Part 3.* Suppose (B) fails and $y\in O$. Take an $r_0$-chain from $p$ to $y$ without trivial steps. Every non-trivial step starts at a point $z\in O$ with $|z-c_k|\le r_0$ for the relevant $k$. Since (B) fails, in fact $|z-c_k|<r_0$. The chain is finite, so there is $r<r_0$ exceeding all these distances, and the same sequence is an $r$-chain (Lemma 2.1). Hence $y\in O_r(p)$, which proves $O=\bigcup_{r<r_0}O_r(p)$.

   This is an increasing union (Theorem 3.1) of finite sets with infinite union, so the sizes are unbounded, and by monotonicity $|O_r(p)|\to\infty$. Finally, (A) holds by part 2. $\square$

**Corollary 5.2.** If $r_c^{\rm orb}<\infty$ and $G_{r_c^{\rm orb}}$ has an infinite orbit $O_{r_c^{\rm orb}}(p)$, then $r^*(p)=r_c^{\rm orb}$, and that orbit satisfies the conclusions of Theorem 5.1.

*Proof.* $O_r(p)$ is finite for all $r<r_c^{\rm orb}$ by the definition of $r_c^{\rm orb}$. $\square$

**What Theorem 5.1 does not show.**
1. *Which point.* It gives no information on where on $\partial D_1\cup\partial D_2$ the contact occurs. In particular it does **not** imply the paper's assumption, behind the closed-form radii for $n=8,12$ and others, that the limit point of a specific segment construction lies on a boundary circle at the critical value. That assumption would need, in addition:
   - that the construction's limit point is the contact point;
   - that its radius is the critical one, i.e. that orbits are finite below it.

   Neither follows.
2. *Which case.* It does not decide between (A) and (B). It also does not exclude that (B) holds while only finitely many orbit points lie near the circles.
3. *Group level.* It applies to a point $p$ at its own critical radius $r^*(p)$. It says nothing at $r_c$ or $r_c^{\rm orb}$ unless an infinite orbit exists there (Corollary 5.2), which is open (Remark 4.3).
4. *A necessary condition only.* It is a necessary condition for a radius to be critical for $p$, not a way to compute $r^*(p)$.

---

## 6. Open disks

The boundary convention matters, and the open-disk statements are slightly different. Replace $\le$ by $<$ in Definition 1.1 and Lemma 2.1. Theorem 3.1, Proposition 3.3 and Theorem 3.4 hold verbatim, with the same proofs ($|z-c_k|<r_k\le r_k'$).

**Proposition 6.1 (open disks).**
1. If $O_{r_0}(p)$ is finite, then $O_r(p)=O_{r_0}(p)$ for $r\in(\max(0,r_0-\delta'),r_0]$. Here $\delta'=\min\{r_0-|y-c_k| : y\in O_{r_0}(p),\ |y-c_k|<r_0\}$, with $\delta'=+\infty$ when this set is empty (for example when $p$ lies in neither open disk).
2. If $O_{r_0}(p)$ is finite and $O_r(p)\neq O_{r_0}(p)$ for $r$ arbitrarily close above $r_0$, then $O_{r_0}(p)$ contains a point of $\partial D_1(r_0)\cup\partial D_2(r_0)$.
3. If $O_{r_0}(p)$ is infinite and $O_r(p)$ is finite for all $r<r_0$, then case (A) of Theorem 5.1 holds. Here an orbit point inside a disk is strictly inside, so the infimum of inner depths is never attained. Also $O_{r_0}(p)=\bigcup_{r<r_0}O_r(p)$.

*Proof.*
1. Let $S=O_{r_0}(p)$ and $r\in(\max(0,r_0-\delta'),r_0]$.
   - *Same membership.* Points $y\in S$ with $|y-c_k|<r_0$ satisfy $|y-c_k|\le r_0-\delta'<r$. Points with $|y-c_k|\ge r_0$ are not in the open disk of radius $r\le r_0$. So membership of points of $S$ is the same at $r$ and at $r_0$, and by Lemma 2.1 each generator at radius $r$ agrees on $S$ with the corresponding generator at $r_0$.
   - *$S\subseteq O_r(p)$.* Every $r_0$-chain from $p$ stays inside $S$, so by the previous point it is also an $r$-chain.
   - *$O_r(p)\subseteq S$.* This is monotonicity (Theorem 3.1), since $r\le r_0$.
2. If no orbit point lies on a circle, let $\delta''$ be the minimum of $|y-c_k|-r_0$ over orbit points with $|y-c_k|>r_0$, with $\delta''=+\infty$ if there are none. Membership in the open disks then agrees for $r\in[r_0,r_0+\delta'')$, and the argument of Theorem 4.1 applies there: the generators at $r$ agree with those at $r_0$ on $S$, so $S$ is invariant at radius $r$ and $O_r(p)\subseteq S$, while monotonicity ($r\ge r_0$) gives $S\subseteq O_r(p)$.
3. Part 1 of Theorem 5.1 goes through with open disks. Non-trivial chain steps start strictly inside, so the argument of Theorem 5.1(3) applies without assumption. $\square$

So with open disks the critical behaviour is "accumulation from inside" (case (A)) whenever the orbit is infinite at its critical radius. With closed disks, Theorem 4.1 makes the critical radius always carry an infinite orbit, at the price of the extra alternative (B).

---

## 7. Other one-parameter families (sketch)

This section is a **sketch**. It is not among the results claimed in the status paragraph or in §10. The proofs above use only coordinatewise monotonicity and one-sided continuity of the radii. Let $t\mapsto\boldsymbol r(t)=(r_1(t),r_2(t))$ be non-decreasing in each coordinate.
- Theorem 3.1, Proposition 3.3 and Theorem 3.4 hold along the family.
- If each $r_k$ is right-continuous, Theorem 4.1 and Corollary 4.2 hold, with $\delta$ chosen so that $r_k(t)<r_k(t_0)+\delta$ for $t$ near $t_0$.
- If each $r_k$ is left-continuous at $t_0$, and the orbit is infinite at $t_0$ and finite for all $t<t_0$, then Theorem 5.1 holds with the inner depths taken only over disks $k\in J=\{k: r_k(t)<r_k(t_0)\text{ for all }t<t_0\}$. A disk $k\notin J$ has constant radius on some $[t_1,t_0]$ (by monotonicity), so membership in it does not change there. In part 1 one chooses $t\in[t_1,t_0)$ with $r_k(t)>r_k(t_0)-\Delta$ for $k\in J$, which left-continuity allows; then $r_k(t)=r_k(t_0)$ for $k\notin J$. For example, with $r_1$ fixed and $r_2$ varying, contact is with $\partial D_2$ only.

---

## 8. Relation to `analytic-continuation.md`

- The proposition in §2.3 of [`analytic-continuation.md`](../analytic-continuation.md) (the "Cauchy–Hadamard theorem for two-disk orbits") is **correct**. It is Theorem 5.1(1) here, with the same proof.
- That section's remark that the set of radii with an infinite orbit has the form $(r^*,\infty)$ or $[r^*,\infty)$ is weaker than the truth for closed disks: it is always $[r^*,\infty)$ (Corollary 4.2).
- That section relies on "the paper's monotonicity of orbit sizes". That monotonicity is true (Theorem 3.1); the paper's justification is imprecise (Example 3.2).
- Group-level monotonicity, which the paper's definition of the critical radius needs, is proved here via Proposition 3.3 (Theorem 3.4).

---

## 9. Computational sanity checks (not part of the proof)

These checks used exact arithmetic in $\mathbb Q(\mathrm i)$ ($n=4$) and $\mathbb Q(e^{\mathrm i\pi/3})$ ($n=3,6$), with exact squared-norm disk tests.
- Squared radii $\{1/2,1,9/8,3/2,2,9/4,5/2,3,4\}$. Starting points: grid points of mesh $1/2$ in $U$.
- $O_r(p)\subseteq O_{r'}(p)$ was checked for all pairs $r<r'$, together with $O_{r}(p)=O_{r+\eta}(p)$ for $r^2\mapsto r^2+10^{-9}$ (Theorem 4.1).
- 5346 checks, no violation.
- Example 3.2 was checked by hand and is elementary.

The scripts were scratch work and are not part of this repository.

---

## 10. Status

Verdicts are those of the independent referee (`referee-report-thread1.md`), who also re-ran the computations of §9 and wider ones (orders $n=3,4,5,6$, boundary starting points, open disks) with no counterexample.

| Statement | Status |
|---|---|
| Theorem 3.1: orbits non-decreasing (as sets) in the radii, any n₁, n₂ | proved; refereed correct |
| Example 3.2: words act differently, and no generator-preserving homomorphism exists in general | proved; refereed correct; the paper's stated reason is imprecise |
| Proposition 3.3, Theorem 3.4, Corollary 3.6: G finite at r′ ⇒ G finite at r ≤ r′ (so r_c is well defined) | proved; refereed correct |
| Theorem 4.1, Corollary 4.2: finite orbits are right-stable; 𝓘(p) = [r*(p), ∞) (closed disks) | proved; refereed correct |
| Theorem 5.1, Corollary 5.2: boundary contact dichotomy (A)/(B) at r*(p); (A) and blow-up of \|O_r(p)\| if (B) fails | proved; refereed correct |
| Proposition 6.1: open-disk version, always (A) | proved; refereed correct |
| §7: other one-parameter families | sketch only; not claimed |
| Group-level footnote 4 (G infinite at r_c), and attainment of r_c^orb | open |
| r_c = r_c^orb (infinite group ⇒ infinite orbit) | open (paper's open question) |
| Location of the contact point; the paper's "limit point on the boundary" assumption | not implied; open |
| Whether case (B) without (A) can occur | open |

Not independently checked by the referee: computations for orders other than $n\in\{1,\dots,6\}$, and the comparisons of §8 (made against a note the referee did not have).

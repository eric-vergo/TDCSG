# Independent review of the pentagrid lower bound for fivefold rotations

Authors: Eric Vergo and OpenAI GPT-6.2 Astra (independent referee)

The claim under review is that the two closed-disk rotations through one fifth of a turn generate a finite permutation group for every radius $0\le r<\sqrt{3+\varphi}$. The following checks use exact identities.

## The geometry of a crossing

Write $R=r/2$, $R_c=\sqrt{3+\varphi}/2$, $c=(\sqrt5-1)/4$, $d=-(\sqrt5+1)/4$, $h=c-d=\sqrt5/2$ and $a=1/2+h/2$. Rotate the coordinate under consideration to the positive horizontal direction and translate the disk center to the origin. For an edge with positive midpoint abscissa, its right endpoint $v$ has color one. Its other possible neighbors are $v-u$ for unit vectors $u$ with horizontal component $c$ or $d$. For a negative midpoint, negate both coordinates at the left endpoint of color zero. Its other neighbors then have exactly the same form. This color reversal is essential.

If $u_x=d$ and both endpoints of the proposed second edge lie in the disk, then $v_x\le R+d<1<a$, since $R_c<3/2$ and $d<-1/2$. For $u_x=c$, put $t=1/2-c\in(0,1)$. The two disk tests imply
\[
 |v-tu|^2=(1-t)|v|^2+t|v-u|^2-t(1-t)\le R^2-t(1-t).
\]
A negative right side rules out the edge. Otherwise
\[
 v_x\le tc+\sqrt{R^2-t(1-t)}<tc+1=a.
\]
Here $R_c^2=5/4-c^2$, $t(1-t)=1/4-c^2$, and $tc=(\sqrt5-2)/4$. At $R=R_c$, equality holds for $v=(1,0)+tu$, since $|v|^2=|v-u|^2=R_c^2$. Its original horizontal neighbor $v-(1,0)=tu$ lies inside as well. The strict change in radius therefore has a genuine role. For a fixed $R<R_c$ these bounds leave a positive gap between $a$ and every feasible abscissa of a vertex supporting a second edge.

## Uniform barriers and paths

At a sum-zero label $n$ with $n_j=m$, let $P=n_{j-1}+n_{j+1}$. The two remaining coordinates sum to $-m-P$. The midpoint abscissa relative to the disk center is $(1-d)m+hP+1/2-x_j$, where $x_j$ is the disk center's component in direction $j$. Since $(1-d)/h=\varphi$, a level $m$ for which $\varphi m+(1/2-x_j)/h$ is sufficiently close modulo one to $1/2$ places *every* midpoint at absolute abscissa at least $h/2-\eta$. Choose $\eta$ strictly smaller than the geometric gap above and $h/2$. Every surviving crossing then has a degree-one endpoint.

For any such open target interval on the circle, finitely many inverse images under forward iterates of the irrational rotation cover the circle, by density and compactness. Each consecutive block of a fixed length thus contains a suitable level, uniformly in $x_j$, the initial level and $j$. Starting at coordinate $k$, choose an upper barrier $m\ge k+1$ and a lower one $m\le k-2$, both a uniformly bounded distance from $k$. Neither endpoint of either crossing can be the starting label. Any crossing on a simple path from the starting label must consequently be its final edge. This confines even the possible terminal overshoot to a box of uniformly bounded cardinality. Arbitrary walks reach the same vertices as simple paths.

## Returning to the disk rotations

Use the affine coordinate $(w+1)/2$, so the original centers are $0,1$ and the disk radius is $R$. A prefix of applied rotations gives an isometry $g$ whose inverse has linear part a fifth root of unity. The pulled-back centers $g^{-1}(0),g^{-1}(1)$ are an oriented pair differing by that root. Initially they have labels $0,e_0$. A rotation about either center fixes its pulled-back label and changes the other endpoint by replacing the edge direction with the new fifth root. Thus the formal labels retain sums zero and one, even if the unused endpoint falls outside the window. Inactive letters may be removed for the given seed. Consecutive active centers coincide when the same generator is used and otherwise are endpoints of the oriented pair immediately before the later rotation. Both belong to the closed disk around the initial seed. The first active center is an initial endpoint, and at most two starting labels are possible.

The final active center $p$ remains fixed as a pulled-back center of the completed word. The final image of the normalized seed $y$ has the form $b+\zeta^k(y-p)$ for $b\in\{0,1\}$ and one of five phases. The empty active word gives $y$. Hence the box bound on active labels gives a uniform bound on orbit sizes, irrespective of the final unused endpoint. On each orbit, number its points and record the pair of permutations induced by the generators. The uniform bound allows only finitely many numbered types; one copy of each occurring type detects every nonidentity group element. Their finite product proves group finiteness.

## Verdict on the manuscript

I checked all four lemmas and the conclusions in [the proof](sharp-lower-bound-n5-pentagrid.md). Its explicit choice $\eta=\delta/16$ is valid: the weighted squared-distance identity gains $\delta/8$ in the supporting abscissa. Consecutive Fibonacci numbers are coprime, and $F_k<\varphi^k$ proves the stated strict approximation. The perturbations of the rational grid have common sign and span less than one grid spacing, including across the circular seam. Thus the claimed bound on the return gaps holds for every phase. Removing the first and last edge from a simple path removes all possible degree-one vertices from its remaining edges. The original-coordinate translation formula and its bound $10N+32$ follow on applying the cyclotomic embedding. I accept both subcritical finiteness and the stated conjugate bound as mathematical theorems. This review verifies the written proof; it does not certify a Lean implementation.

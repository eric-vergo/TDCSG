# Referee report: the critical radius of $GG_{10}$

Referee: Claude (independent of the authoring agent)

Note refereed: `critical-radius-n10.md` (this directory). The paper is arXiv 2302.12950; I judged statements about it only against its extracted text. I could not render Figure 5b.

## Verdicts

| claim | verdict |
|---|---|
| (A) Lemma 3.1 (the chord $J$), Lemma 3.2 (the three words), §3.3 (circle rotation), Theorem A: $GG_{10}(r)$ infinite for every $r\ge\sqrt{4-\varphi}$ | **correct**. Every number, vector, trajectory and boundary contact of §3 and Appendix A.1 agrees with my own exact computation. Wording fixes: issues 1, 4, 6 |
| Theorem 4.1 (cut-set certificate, restated from the $n=5$ note) | **correct**. The restatement agrees with the refereed $n=5$ version and includes that referee's fix on the unbounded face |
| `verify.py` checks (C1)–(C4) exactly, including the coordinates $(x,y/\sin36^\circ)$ | **correct**. Every decision is exact. Floats only order candidates and propose merge partners (§B.1 below) |
| (B) Theorem B: $GG_{10}(r)$ finite for $r\le r_\ast$, $r_\ast^2=63/16-\varphi$ | **correct given the computation, which I reproduced independently** with identical circle, piece, maximal-arc, (C2)-image and (C4) counts at every $\delta$ in Table 4.1, including $\delta_\ast=1/16$ (§B.2). Reproducibility gap: issue 7 |
| (C) $GG_5=\langle a^2,b^2\rangle\subseteq GG_{10}$; $GG_5$ finite at $r_c(10)$; lens-corner formula and Galois conjugacy | **correct**. I reproduced the 54-circle $GG_5$ certificate (same 54 centres as Appendix A.2). Issue 6 is cosmetic |
| Status and titles | **correct after minor fixes** (issues 1, 2, 3). The note states the right thing: the bound $r_{\rm crit}(10)\le\sqrt{4-\varphi}$ is proved, $r_\ast\le r_{\rm crit}(10)$ is proved modulo the exact computation, and equality is open. I found no overclaim of the main results |

## Issues

**1. §6, first bullet: "the orbit of 0 is infinite at $r=\sqrt{4-\varphi}$ itself (the paper's footnote 4, for this $n$)". Severity: minor.**
Footnote 4 of the paper reads: "We believe, but have not proved, that it will also be infinite exactly at the critical radius." Theorem A proves the group infinite at $\sqrt{4-\varphi}$. That confirms footnote 4 for $n=10$ only if $\sqrt{4-\varphi}$ *is* the critical radius, and that is open. `boundary-contact.md` §8 lists "group-level footnote 4" as open. As written, the parenthesis can be read as saying footnote 4 is now settled for $n=10$.
*Repair:* "(this is what footnote 4 of the paper predicts if $r_{\rm crit}(10)=\sqrt{4-\varphi}$; footnote 4 itself stays open for $n=10$ until (B) is proved)".

**2. §3.1, "Relation to the paper's Figure 5b". Severity: minor.**
The paper's text says only: "A similar analysis of the geometry in Figure 5b, where $n=10$, gives $r=\sqrt{4-\varphi}\approx1.543$." Everything else is the author's reading of the rendered figure: the decagons of circumradius $\varphi^{-1}$, the dotted line through $0$, and the identification of the "similar analysis" with the condition $P\in\partial D_2$. I could not check that reading. The exact identity it rests on, $P=-1+\varphi^{-1}\zeta=\zeta^2-\zeta$ with $|P-1|^2=4-\varphi$, is correct, and no proof uses the paragraph. Caveat 5 of §8 already says this.
*Repair:* open the paragraph with "Our reading of the figure (not stated in the paper's text):", and change "the paper's 'similar analysis' is the condition $P\in\partial D_2$" to "is presumably the condition $P\in\partial D_2$".

**3. Status, bullets 2–3, and §6. Severity: minor.**
(a) The second status bullet says (B) "is proved only for $r\le r_\ast$ … by an exact finite computation". §4.3 and §8 say "proved modulo the computation". Use the same qualifier in the status bullet, and cite this independent reproduction.
(b) "Whether some other mechanism already gives an infinite group at a radius in $(r_\ast,r_c)$ is not excluded; the evidence (§6) says no." The evidence is consistent with "no" but is not decisive. *Repair:* "the evidence (§6) is consistent with no".
(c) For completeness, §6 should record a datum from the paper. Its Table 1 gives the numerical estimate $1.543357$ for $n=10$, which is below the closed form $1.543362$ and so lies in the open window $(r_\ast,r_c)$. For $n=5,8,12$ the estimate agrees with the closed form to six decimals. The paper says its estimates "may be too high … or too low because the points searched had very large but finite images", so this is fully consistent with the huge finite orbits of §6. It is still the one published number that sits inside the window, and it should be mentioned there.

**4. "Each word fails for every $r<r_c$" (status bullet 3, §3.2 last paragraph, §6 "switches on exactly"). Severity: minor (precision).**
The statement is true, but only in the weakest sense. Each word fails on its *closed* segment because its first letter is applied at an endpoint at squared distance exactly $4-\varphi$ ($b$ at $W'$, $a$ at $P'$, $a$ at $W$). For $r$ slightly below $r_c$, each word is still valid on most of its segment. I checked exactly: at $r^2=4-\varphi-\varepsilon$, with $\varepsilon=10^{-6}$, $1/16$ and $10^{-30}$, the first letter fails, as stated. The claim is not used in the proof of Theorem A. "The mechanism switches on exactly at $r_c$" therefore means: the three words are valid on three closed segments covering $J$ if and only if $r\ge r_c$. That is a statement about this construction, not evidence that $r_c$ is critical.
*Repair:* state it in that form once, in §3.2, and refer to it elsewhere.

**5. §4.2, tangency remark: "impossible when $8\delta\notin\mathbb Z$". Severity: cosmetic.**
This is correct but not sharp. $\mathbb Z[\varphi]=\{(a+b\sqrt5)/2: a\equiv b \bmod 2\}$, and $4\rho=\big((28-8\delta)-4\sqrt5\big)/2$. So $4\rho\in\mathbb Z[\varphi]$ if and only if $4\delta\in\mathbb Z$, and tangency is impossible whenever $4\delta\notin\mathbb Z$. The tangency at $\delta=1$ (which I also hit, circle $(1,0,0,2)$ against $-1$) is consistent with this.

**6. §3.3 Remark 4, "the translation is again $2\varphi^{-1}$ (in absolute units)". Severity: cosmetic.**
For $n=5$ the translation is $2\varphi^{-1}$ *in units of $|E|$*, with $|E|=|1-\zeta_5|=2\sin36^\circ\approx1.176$. It is not $2\varphi^{-1}$ in absolute units, so "again" is wrong. *Repair:* "the translation is $2\varphi^{-1}$ (here in absolute units, there in units of $|E|$)".

**7. Reproducibility of Parts A and B (§4.2, Appendix A.3). Severity: gap (reproducibility only; not a gap in the mathematics).**
All programs, logs and certificates live in a session scratch directory (`t4_10/`), which a reboot or cleanup can erase. The refereed $n=5$ note had the same issue (its referee's issue 6). The proof of Theorem B is "modulo the computation", so the computation must stay available.
*Repair:* archive `partA10.py`, `z10.py`, `cut/cut.py`, `cut/cut5.py`, `cut/field.py`, `cut/verify.py`, `cut/test_cut.py` and the `ver_10_*.log` files in the repository, or in another durable place the note names. The certificates themselves are deterministic outputs and need not be stored. Also, the docstring of `verify.py` still says "for n in {8,12}". This is cosmetic, but it should say $n\in\{8,10,12\}$ when archived.

No fatal issues. Nothing in Part A uses an identity letter (see §A.2 below), so the extension from $r_c$ to $r>r_c$ is valid as argued.

## What I recomputed, and what agreed

All my programs are in `/private/tmp/claude-501/-Users-eric-Github-riemann-hypothesis/8e07d302-d180-4cc0-ac7d-117a36aae2f9/scratchpad/ref10/`: `zq.py`, `partA.py`, `partA_orbit.py`, `lat.py` and `rcut.py`. I wrote them from the note's statements, without importing or copying the author's code, and ran them with `python3 -I`. The run logs are `runs_a.log`, `runs_b.log` and `run_inf.log`.

### A. Part A (own exact arithmetic: $\mathbb Q(\zeta_{10})$ as Fraction 4-vectors reduced by $\zeta^4=\zeta^3-\zeta^2+\zeta-1$; real numbers as $a+b\sqrt5$, with $\sqrt5$ realized as $2(\zeta+\zeta^{-1})-1$)

**A.1 Geometry.**
- Points $su$ with $u=\zeta^4$, for $s=\pm\sqrt5,\pm\varphi^{-1},1,-1$, give exactly the vectors of the table in §3.1. $P=\zeta^2-\zeta$.
- Squared distances:
  - $|W+1|^2=|W'-1|^2=|P'+1|^2=|P-1|^2=4-\varphi$;
  - $|W-1|^2=|W'+1|^2=8+\varphi$;
  - $|P+1|^2=|P'-1|^2=2-\varphi$;
  - $|U+1|^2=2-\varphi<4-\varphi$, so $U$ is interior to $D_1$;
  - $|L\pm1|^2=|{-L}+1|^2=4-\varphi$.
- $2\operatorname{Re}u=-\varphi$. Both $\sqrt5$ and $-\varphi^{-1}$ are roots of $s^2-\varphi s+\varphi-3$, which confirms Lemma 3.1.
- $L+1=\zeta^{-2}(W+1)$ and $P'+1=\zeta^3\,\overline{(W+1)}$ hold exactly.
- A brute-force search over $|x_j|\le6$ finds exactly 20 solutions of $|w|^2=4-\varphi$. All have conjugate norm $4.618=4-\varphi'$, consistent with the ideal-theoretic count.

**A.2 The words.** I read words left to right, as in the note and the paper. Before every letter I checked exactly that *both* current endpoints lie in that letter's closed disk. Every letter of all three words passed, so **every letter acts as a rotation on the whole current segment** (convexity). No letter is ever meant to act as the identity, so the question of a segment lying wholly outside a disk does not arise. For $r>r_c$ the same disk tests hold because the disks grow, so the words act identically; the argument of Theorem A, step 1, is correct.
- Composite rotation exponent: $0$ for each word.
- Translations: $(0,-2,2,0)=2P=2\varphi^{-1}u$ for `bbAB` and `abAA`, and $(2,0,0,-2)=-2\varphi u$ for `aaaBBB`. The same vector is obtained at both endpoints.
- Final endpoints equal $s=-1,\varphi^{-1}$; $\varphi^{-1},\sqrt5$; and $-\sqrt5,-1$, exactly.
- The intermediate vectors agree entry by entry with Appendix A.1.
- The boundary contacts (letter, point) agree exactly with the list in §3.2.

**A.3 The circle map.**
- The source segments $[-\sqrt5,-\varphi^{-1}]$, $[-\varphi^{-1},1]$ and $[1,\sqrt5]$ cover $J$.
- Their images $[-1,\varphi^{-1}]$, $[\varphi^{-1},\sqrt5]$ and $[-\sqrt5,-1]$ lie in $J$.
- At $s=-\varphi^{-1}$ the words `bbAB` and `abAA` agree.
- $2\varphi^{-1}+2\varphi=2\sqrt5$ (checked exactly).
- The rotation number is $\varphi^{-1}/\sqrt5=(5-\sqrt5)/10=1/(\varphi+2)$. Its continued fraction is $[0;3,1,1,\dots]$, because $\varphi+2=3+\varphi^{-1}$.
- The injectivity argument (rational parts of $(k-l)\varphi^{-1}=(m_k-m_l)\sqrt5$) is correct, and $0\in J$.

**A.4 Gated simulation (redundant check).** I followed 200 steps from $0$ with the genuinely gated generators, at $r^2=4-\varphi$, $13/3-\varphi$, $9$ and $100$. Every step reproduced $T$ exactly, and the 200 points are distinct.

### B. Part B

**B.1 Reading of the author's programs** (`t4_10/cut/field.py`, `cut.py`, `verify.py`; read only).
- `field.reim` for $n=10$ returns $(\operatorname{Re}x,\operatorname{Im}x/\sin36^\circ)$ in $\mathbb Q(\sqrt5)$. I re-derived both formulas ($\cos36^\circ,\cos72^\circ,\cos108^\circ$; $\sin72^\circ/\sin36^\circ=\sin108^\circ/\sin36^\circ=\varphi$). `norm2` multiplies the scaled imaginary part squared by $\sin^236^\circ=(5-\sqrt5)/8$, stored exactly. $\sin36^\circ$ never appears as a float in a decision.
- The endpoint formulas in `Cut.key` match the note's display. I re-derived $X=d_x/2-s\,g\,d_y/2$ and $Y=d_y/2+s\,g\,d_x/(2\sin^236^\circ)$ with $g=h\sin36^\circ=\sqrt{H\sin^236^\circ}>0$.
- The half-plane bit uses the exact sign of $Y$, then of $X$. The scaling is a positive diagonal map, so the half-plane and the sign of the cross product are preserved. The angular order on each circle is therefore decided correctly.
- `sgn1` and `sgn2` are correct sign procedures for $a+b\sqrt H$ and $P+Q\sqrt{H_2}$, using squaring only when the signs are opposite.
- In `verify.py`, `S.FAST=False` disables the float shortcut in `acmp`. The 1e-7 float window only proposes merge partners, which are then accepted by exact equality. A missed merge only makes (C2) and (C4) stricter.
- The (C2) containment test is exact: both image endpoints lie in a target maximal arc, in the right order.
- (C3): `meets()` raises on exact tangency and is called for every circle against both centres.
- (C4): every maximal-arc endpoint equal to $(p,\pm1)$ must be the start $(p,-1)$ or the end $(p,+1)$, which is stricter than the theorem requires.
- Isolated points of $\alpha\cap D_p$, which `clip` discards, lie on $\partial D_p\subseteq K$, so (C2) is unaffected.
- The checks are also sound if the merged arcs fail to be truly maximal.
- I conclude that `verify.py` checks (C1)–(C4) exactly. The author's logs `ver_10_{1_5,1_7,1_10,1_14,1_16}.log` end with `CERTIFICATE VALID` and the counts of Table 4.1.

**B.2 Independent implementation** (`rcut.py`). Its design differs from the author's:
- **Integer arithmetic only.** Numbers are pairs of integers in $\mathbb Z[\sqrt5]$. The radicals are cleared by positive integer scalings of my own derivation: $R=4\operatorname{Re}d$, $J=4\operatorname{Im}d/\sin36^\circ$, $N'=128|d|^2=8R^2+(5-\sqrt5)J^2$, $M=q(512\rho-N')$, $T=8q(5-\sqrt5)MN'$, and coordinates $X^\ast=\kappa R-sJ\sqrt T$, $Y^\ast=\kappa(5-\sqrt5)J+8sR\sqrt T$ with $\kappa=8qN'$.
- **Merged-arc store.** Each circle holds a list of disjoint maximal arcs (merged on insertion), not pieces. Only the newly covered gaps are processed further.
- **Separate exact checker** with no float decision, applied to my own closure. The closure itself uses a float shortcut only for angles more than $10^{-8}$ apart and away from the angle $0$.
- **Self-test.** 37 000 exact angular comparisons against independent complex-float angles gave 0 mismatches; 78 of them were exact coincidences of distinct symbols.

| $\delta$ | mine: closed / circles / processed pieces / maximal arcs / (C2) images / (C4) endpoints / max $\lvert\sigma(c)\rvert$ / result | author (Table 4.1) | agree? |
|---|---|---|---|
| 1/2 | yes / 318 / 4 056 / 678 / 1 564 / 432 / 12.71 / **valid** | 318 / 4 056 / 678 / 1 564 / 432 / 12.7 | identical |
| 1/3 | yes / 988 / 9 895 / 2 322 / 5 324 / 632 / 23.49 / **valid** | 988 / 9 895 / 2 322 / 5 324 / 632 / 23.5 | identical |
| 1/5 | yes / 5 986 / 176 617 / 19 388 / 44 484 / 1 816 / 50.97 / **valid** | 5 986 / 176 617 / 19 388 / 44 484 / 1 816 / 51.0 | identical |
| 1/7 | yes / 6 058 / 290 916 / 24 000 / 55 204 / 2 252 / 50.97 / **valid** | 6 058 / 290 916 / 24 000 / 55 204 / 2 252 / 51.0 | identical |
| 1/10 | yes / 11 722 / 530 151 / 47 128 / 108 324 / 3 112 / 79.87 / **valid** | 11 722 / 530 151 / 47 128 / 108 324 / 3 112 / 79.9 | identical |
| 1/14 | yes / 33 040 / 2 718 214 / 205 320 / 471 844 / 9 448 / 117.20 / **valid** (closure 207 s, exact check 53 s, peak 2.0 GB) | 33 040 / 2 718 214 / 205 320 / 471 844 / 9 448 / 117.2 | identical |
| 1/16 | yes / 33 364 / 3 901 930 / 260 176 / 598 244 / 11 792 / 117.20 / **valid** (closure 318 s, exact check 67 s, peak 2.0 GB) | 33 364 / 3 901 930 / 260 176 / 598 244 / 11 792 / 117.2 | identical |

My "processed pieces" (gaps ever added) coincides with the author's stored-piece count at every $\delta$. This is expected, since both closures add exactly the uncovered parts of each image. The agreement in all six columns makes it very unlikely that the two closures differ.

**B.3 Sanity checks** (my program).
- $\delta=0$ ($r=r_c$): the closure stops on an exact tangency, circle $(1,2,-2,0)$ against $-1$. It does not certify.
- $\delta=1$: tangency, as the note says.
- $\delta=-1/10$ ($r^2=4-\varphi+1/10$, infinite by Theorem A): no termination. After 3.35 million pieces and 1.83 million circles, with the work list still growing, I killed the run at 5.5 GB.
- Known finite cases certify. $\delta=3/2$ ($r<1$, disjoint disks): 2 circles, valid. $\delta=13/10$ ($r\approx1.04$): 20 circles, 20 arcs, valid.

### C. Relation to $n=5$
- $a^2$ is the gated rotation by $\zeta^{-2}=e^{-2\pi i/5}$ about $-1$ on the same disk, so $\langle a^2,b^2\rangle=GG_5(r)\subseteq GG_{10}(r)$.
- $a=(a^2)^3(a^5)^{-1}$, and $a^5$ is $z\mapsto-2-z$ on $D_1$.
- **$GG_5$ certificate.** My program with rotations $\zeta^{\pm2}$ at $r^2=4-\varphi+1/10$ gives 54 circles, 64 maximal arcs, 164 (C2) images and 60 (C4) endpoints: **valid**. The 54 centres coincide with the list in Appendix A.2. At $\delta=0$ the $GG_5$ closure hits a tangency (circle $(3,-4,2,-2)$ against $-1$), as the note says. Group monotonicity then gives finiteness of $GG_5$ at $r_c(10)$. The $n=5$ note's Theorem B ($r\le2.1256$) also covers it.
- **Lens-corner formula.** $\rho_n=1+4\sin^2(2\pi/n)=3-2\cos(4\pi/n)$, so $\rho_5=3+\varphi$ and $\rho_{10}=4-\varphi$. These are conjugate under $\zeta_5\mapsto\zeta_5^2$, which sends $\sqrt5\mapsto-\sqrt5$. The paper itself lists the same minimal polynomial $x^4-7x^2+11$ for $n=5$ and $n=10$.
- I checked "$\rho_n>r_c(n)^2$ for the other $n$ of the paper's Table 1" for every $n\in\{7,8,9,11,\dots,19\}$, not only for the $n$ the note names. It holds for all of them; the tightest is $n=8$, with $3$ against $2.9289$.

## What I did not check
- The figure (Figure 5b), and the pixel measurement mentioned in §3.1.
- The float closure `arcs_float10.py` and its circle counts. These are consistency data only.
- The $\delta=1/20$ and $\delta=0.03$ float runs of §4.4, and the memory and timing figures.
- §6 evidence from `tdcsg-orbit` (orbit sizes, threshold sweep, gap ratios), and §7 renormalization data and Conjecture R₁₀. These are conjectural and not proofs.
- The Galois-transport search of §5.2, item 1 (negative result).
- The proofs of the cited monotonicity results and of Theorem 4.1 beyond comparing the restatement with the refereed $n=5$ version. They are refereed elsewhere.
- I did not use the repository's `tdcsg-orbit` engine.

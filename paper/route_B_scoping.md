# Scoping dynamic routes to Frohmanian Tether Hypothesis (B) without BKM

Status: **no non-circular route found.** This note is on paper only; nothing in it is a theorem
unless it is cited as a Lean declaration.

## Setup
Along trajectories, $D\tau/Dt = (I-\tau\otimes\tau)S\tau + \nu(I-\tau\otimes\tau)\Delta\omega/|\omega|$
(see `DirectionEvolution.lean`). The input is `FrohmanianDirectionCoercivity`: bending is $o(|\omega|)$ on the high set.

## Routes, and where each one fails
1. **Lagrangian two-point integration** (`twoPoint_direction_drift`, proved). Fails at
   $\int_0^{T^*}\|\omega\|_\infty\,dt<\infty$ (BKM), at the viscous term, and at trajectory separation, which needs $\int\|\nabla u\|_\infty$.
2. **Gradient transport for $\nabla\tau$.** $D(\nabla\tau)/Dt$ contains $\nabla(\text{bend})$, and that involves
   $\nabla S\sim\nabla\omega$. Pointwise control of bending says nothing about its gradient. Fails at needing
   $\|\nabla\omega\|_\infty$, which is stronger than BKM.
3. **Nonlocal Constantin–Fefferman kernel** (`ConstantinKernel.lean`). Bending is a PV integral whose geometric
   kernel vanishes when $\tau(x+y)\parallel\tau(x)$, **including antiparallel**. So bending control is blind
   to sign flips (`PlanarObstruction.lean`: zero bending, Hölder constant $\ge2\sqrt{n/\pi}$). Even modulo sign,
   inverting an $|\omega|/|y|^3$-weighted average of $|\sin\angle|$ into a pointwise two-point bound needs a
   lower bound on $|\omega|$ near $x$ (thickness of the high set). That is not available, so this route fails there.
4. **Parabolic, geometric-depletion style** (Grujić-type sparseness, Giga–Miura). These need an a priori
   sparseness or scale hypothesis on the super-level sets, which is a new assumption of the same strength.
   Not pursued.

## Honest consequence and a non-drift suggestion
The Constantin–Fefferman and Beirão da Veiga–Berselli criteria use $|\sin\angle(\omega(x),\omega(y))|$, which is
regularity of the vorticity **line field**, not of the signed direction $\tau$. Part (B) as currently
stated, ½-Hölder $\tau$, is stronger than those criteria need, and the planar obstruction refutes any
pointwise route to it. A line-field version of (B) would be weaker and still sufficient. It is **suggested,
not added**, pending your approval.

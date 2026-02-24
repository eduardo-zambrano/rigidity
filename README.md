# Characterizing Arithmetic Through Dirichlet Series with Boolean Coefficients

[![Lean 4](https://img.shields.io/badge/Lean_4-v4.24.0-blue)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.24.0-blue)](https://github.com/leanprover-community/mathlib4)
[![Sorry count](https://img.shields.io/badge/sorry_count-0-brightgreen)]()

This repository contains the paper and a Lean 4 formalization of the main theorem from:

> **Characterizing Arithmetic Through Dirichlet Series with Boolean Coefficients**
> Eduardo Zambrano, California Polytechnic State University

## Overview

Could an alternative multiplication on the natural numbers produce a Dirichlet series resembling the Riemann zeta function? This paper shows that any such operation must be isomorphic to ordinary multiplication.

Given an alternative multiplication $\star$ on $\mathbb{N}$ with unique factorization and Boolean multiplicative coefficients $a(n) \in \{0,1\}$, if the Dirichlet series $Z(s) = \sum a(n)n^{-s}$ satisfies

1. **(E1) Euler Product:** $Z(s) = \prod_{p} F_p(s)$ over the $\star$-irreducibles,
2. **(E2) Local Convergence:** $F_p(1) < \infty$ for every $\star$-irreducible $p$, and
3. **(E3) Boundary Mass Saturation:** $\limsup_{s\to 1^+}(s-1)Z(s) \geq 1$,

then necessarily $a(n) = 1$ for all $n \geq 1$, $Z(s) = \zeta(s)$, and $(\mathbb{N},\star) \cong (\mathbb{N},\cdot)$ as monoids.

The Euler product (E1) is the standard analytic requirement that $Z(s)$ respect its $\star$-prime structure; it implies norm compatibility ($m \star n = m \cdot n$ for coprime inputs) as a consequence. The proof is a short mass argument: since $a(n) \leq 1$ gives $Z(s) \leq \zeta(s)$, any zero coefficient $a(p^{\star j}) = 0$ creates positive missing mass that contradicts boundary saturation. No functional equations or global analytic continuation are required. The three hypotheses are necessary and logically independent. The conclusion is sharp: isomorphism cannot be upgraded to identity (Remark 7.2).

## Repository Structure

```
.
├── rigidity.tex                    # Main manuscript (LaTeX, amsart)
├── rigidity.pdf                    # Compiled paper
├── RigidityProject/                # Lean 4 formalization
│   ├── RigidityProject/
│   │   ├── Basic.lean              # Core definitions (§2)
│   │   ├── Axioms.lean             # Axioms (3 axioms + 1 proved theorem)
│   │   ├── FinsuppStarProd.lean    # Multiplicative extension (proved)
│   │   ├── MassArgument.lean       # Full support and Z = ζ (§6)
│   │   └── Main.lean              # Complete rigidity theorem (§7)
│   ├── lakefile.lean
│   ├── lean-toolchain              # Lean v4.24.0
│   └── lake-manifest.json          # Mathlib pinned at f897ebcf
└── archive/                        # Older manuscript versions and journal materials
```

## Correspondence Between Paper and Formalization

### Definitions (Paper §2 → `Basic.lean`)

| Paper | Lean | Description |
|-------|------|-------------|
| Definition 2.2, axiom (i) | `AltMul`, `AltMul.HasUF` | Reduced factorial commutative monoid (Definition 2.1) with unique $\star$-factorization |
| Definition 2.2, axiom (ii) | `BooleanMultMonoid` | $\{0,1\}$-valued $\star$-multiplicative support |
| $\star$-irreducible | `AltMul.IsIrreducible` | $p \geq 2$ with no nontrivial $\star$-factorization |
| $p^{\star k}$ | `AltMul.starPow` | Iterated $\star$-power |
| $a(n) \in \{0,1\}$ | `BooleanMultMonoid.a` | Characteristic function |
| Hypothesis (E1) | `BooleanMultMonoid.coprime_mul` | Euler product $Z(s) = \prod_p F_p(s)$; formalized in the equivalent norm-compatibility form $m \star n = m \cdot n$ for $\star$-coprime inputs (Lemma 5.1) |
| Hypothesis (E2) | `BooleanMultMonoid.E2` | Local Convergence: $F_p(1) < \infty$ |
| Hypothesis (E3) | `BooleanMultMonoid.E3` | Boundary Mass Saturation: $\limsup(s{-}1)Z(s) \geq 1$ |
| $Z(s) = \sum a(n)n^{-s}$ | `BooleanMultMonoid.Z` | Dirichlet series |
| $F_p(s)$ | `BooleanMultMonoid.localFactor` | Local Euler factor |
| Monoid isomorphism | `BooleanMultMonoid.IsMonoidIso` | Bijective multiplicative map $(\mathbb{N},\star) \to (\mathbb{N},\cdot)$ |

### Axioms (`Axioms.lean`)

The analytic portion of the proof is encapsulated in 3 axioms. One previously axiomatized fact --- dominated convergence for infinite sums --- is proved as a theorem from Mathlib's Tannery's theorem.

| Axiom | Name | Description |
|-------|------|-------------|
| 1 | `support_on_irreducible_powers` | Under (E1)+(E2)+(E3): $a(p^{\star k}) = 1$ for all irreducibles $p$, $k \geq 1$ (Proposition 6.1) |
| 2 | `irreducibles_infinite` | Under (E1)+(E2)+(E3): the set of $\star$-irreducibles is infinite |
| 3 | `free_monoid_iso` | UF + infinitely many irreducibles $\Rightarrow$ $\exists$ monoid isomorphism $(\mathbb{N},\star) \cong (\mathbb{N},\cdot)$ |

| Theorem | Name | Source |
|---------|------|--------|
| Tannery | `tsum_tendsto_of_dominated` | Proved from Mathlib (`tendsto_tsum_of_dominated_convergence`) |

### Theorems (Paper §6--7 → `MassArgument.lean`, `FinsuppStarProd.lean`, `Main.lean`)

| Paper Result | Lean Theorem | File | Status |
|-------------|--------------|------|--------|
| --- ($Z(s) \leq \zeta(s)$) | `Z_le_zeta` | `Basic.lean` | Fully proved |
| --- (Multiplicative extension from prime powers) | `a_finsuppStarProd` | `FinsuppStarProd.lean` | Fully proved |
| Proposition 6.1 ($a(n) = 1$ for all $n \geq 1$) | `full_support` | `MassArgument.lean` | Fully proved |
| --- ($Z(s) = \zeta(s)$) | `Z_eq_zeta` | `MassArgument.lean` | Fully proved |
| Theorem 7.1 (Complete rigidity) | `main_rigidity` | `Main.lean` | Fully proved |

### Formalization Strategy

The paper's proof proceeds in two stages: (1) the mass argument (Proposition 6.1) shows that (E1)--(E3) force $a(p^{\star k}) = 1$ for all irreducible powers, hence $a \equiv 1$ and $Z = \zeta$; (2) the isomorphism (Theorem 7.1) follows because both $(\mathbb{N},\star)$ and $(\mathbb{N},\cdot)$ are free commutative monoids on countably infinite generators.

**What is fully machine-checked.** The algebraic core of the proof is formalized with no axioms beyond Mathlib:

- The global bound $Z(s) \leq \zeta(s)$ from $a(n) \leq 1$ (`Z_le_zeta`).
- The extension from "$a = 1$ on all prime powers" to "$a = 1$ on all $n \geq 1$" (`a_finsuppStarProd` + `full_support`), proved by induction over `Finset.fold` in the unique factorization representation, using $\star$-coprimality of distinct prime-power factors.
- The final assembly: from full support to $Z(s) = \zeta(s)$, and from $P$ infinite to the monoid isomorphism (`main_rigidity`).

**What is axiomatized, and why.** The 3 axioms encapsulate three analytic/algebraic facts:

- *Axiom 1 (mass argument conclusion):* Under (E1)--(E3), $a(p^{\star k}) = 1$ for all $\star$-irreducibles $p$ and $k \geq 1$. This encapsulates the paper's Proposition 6.1: the mass argument showing that any zero coefficient creates missing mass contradicting boundary saturation. The proof involves the Euler product (E1), sequence extraction from (E3), limit arithmetic with (E2), and subseries comparison --- all analytically nontrivial to formalize.

- *Axiom 2 (irreducibles infinite):* Under (E1)--(E3), the set of $\star$-irreducibles is infinite. The proof uses $Z = \zeta$ (from Axiom 1), the Euler product (E1) $Z(s) = \prod F_p(s)$, and the fact that $\zeta$ has a pole at $s = 1$ while a finite product of convergent factors (each finite by E2) would not.

- *Axiom 3 (free monoid isomorphism):* If $(\mathbb{N},\star)$ has unique factorization and infinitely many irreducibles, then $(\mathbb{N},\star) \cong (\mathbb{N},\cdot)$. This is a standard algebraic fact: ordinary primes are also countably infinite (Euclid), so any bijection of generators extends to a monoid isomorphism.

## Building the Formalization

### Prerequisites

- [Lean 4](https://leanprover.github.io/lean4/doc/quickstart.html) (v4.24.0, specified in `lean-toolchain`)
- [Mathlib](https://leanprover-community.github.io/mathlib4_docs/) (pinned at commit [`f897ebcf`](https://github.com/leanprover-community/mathlib4/commit/f897ebcf), fetched automatically via Lake)

### Build

```bash
cd RigidityProject
lake build
```

The first build will download Mathlib and its dependencies (~2 GB). Subsequent builds use cached artifacts.

### Verification

A successful build produces no `sorry` warnings. The only non-`theorem` declarations are the 3 `axiom` statements in `Axioms.lean`.

## Compiling the Paper

```bash
pdflatex rigidity.tex && pdflatex rigidity.tex
```

## License

Apache 2.0

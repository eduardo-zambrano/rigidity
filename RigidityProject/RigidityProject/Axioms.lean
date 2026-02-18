/-
Copyright (c) 2025 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Axioms

This file states axioms used in the conditional formalization.

Axiom 1: Support on irreducible powers (mass argument conclusion)
  Under (E1)–(E3), a(p^{★k}) = 1 for all ★-irreducibles p and k ≥ 1.
  This encapsulates Proposition 6.1 of the paper (the mass argument).
  (E1) is axiomatized as `coprime_mul` in `BooleanMultMonoid`; (E2) and (E3)
  are passed as explicit hypotheses.

Axiom 2: Irreducibles are infinite
  Under (E1)–(E3), the set of ★-irreducibles is infinite.
  This follows from Z = ζ having a pole at s = 1, combined with the
  Euler product (E1) and local convergence (E2).

Axiom 3: Free monoid isomorphism
  If (ℕ,★) has unique factorization and infinitely many irreducibles,
  then (ℕ,★) ≅ (ℕ,·). This is a standard algebraic fact: two free
  commutative monoids on countably infinite generators are isomorphic.

Theorem (proved from Mathlib): Dominated convergence for tsum (Tannery's theorem)
-/

import RigidityProject.Basic
import Mathlib.Analysis.Normed.Group.Tannery

set_option linter.mathlibStandardSet false

open scoped BigOperators Classical

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-!
## Axiom 1: Support on irreducible powers (Proposition 6.1)

Under (E1)–(E3), for every ★-irreducible p and every k ≥ 1,
a(p^{★k}) = 1. This is the analytic core of the paper: the mass argument
shows that any zero coefficient a(p^{★j}) = 0 creates missing mass
that contradicts boundary saturation.
-/

axiom support_on_irreducible_powers
    (D : BooleanMultMonoid) (hE2 : D.E2) (hE3 : D.E3)
    (p : ℕ) (hp : D.toAltMul.IsIrreducible p)
    (k : ℕ) (hk : 1 ≤ k) :
    D.a (D.toAltMul.starPow p k) = 1

/-!
## Axiom 2: Irreducibles are infinite

Under (E1)–(E3), the set of ★-irreducibles is infinite. The proof
(not formalized here) proceeds: from full support, Z(s) = ζ(s); if P
were finite, Z(s) = ∏_{p∈P} F_p(s) would converge at s = 1 (each factor
is finite by (E2)), contradicting ζ having a pole.
-/

axiom irreducibles_infinite
    (D : BooleanMultMonoid) (hE2 : D.E2) (hE3 : D.E3) :
    Set.Infinite {q : ℕ | D.toAltMul.IsIrreducible q}

/-!
## Axiom 3: Free monoid isomorphism

If (ℕ,★) is a free commutative monoid (has unique factorization) with
countably infinitely many irreducibles, then (ℕ,★) ≅ (ℕ,·). This is a
standard algebraic fact: the ordinary primes are also countably infinite
(Euclid), so any bijection P → {primes} extends to a monoid isomorphism.
-/

axiom free_monoid_iso
    (D : BooleanMultMonoid)
    (hP_infinite : Set.Infinite {q : ℕ | D.toAltMul.IsIrreducible q}) :
    ∃ φ : ℕ → ℕ, D.IsMonoidIso φ

/-!
## Theorem (Tannery): Dominated convergence for tsum

A version of dominated convergence for infinite sums indexed by ℕ.
Proved from Mathlib's `tendsto_tsum_of_dominated_convergence` (Tannery's theorem).
-/

theorem tsum_tendsto_of_dominated
    {f : ℕ → ℕ → ℝ} {g : ℕ → ℝ} {h : ℕ → ℝ}
    (hg : Summable g)
    (hbound : ∀ n k, |f n k| ≤ g k)
    (hlim : ∀ k, Filter.Tendsto (fun n => f n k) Filter.atTop (nhds (h k))) :
    Filter.Tendsto (fun n => ∑' k, f n k) Filter.atTop (nhds (∑' k, h k)) :=
  tendsto_tsum_of_dominated_convergence hg hlim
    (Filter.Eventually.of_forall fun n k => by rw [Real.norm_eq_abs]; exact hbound n k)

end -- noncomputable section

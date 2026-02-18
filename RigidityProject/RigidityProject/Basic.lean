/-
Copyright (c) 2025 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Core Definitions for the Rigidity Theorem

This file contains fundamental definitions for the formalization of
"Characterizing Arithmetic Through Dirichlet Series with Boolean Coefficients."

Main definitions:
- `AltMul`: An alternative multiplication ★ on ℕ
- `BooleanMultMonoid`: A Boolean multiplicative monoid (★, A) with (E1)
  (stated in its equivalent norm-compatibility form; see docstring)
- `BooleanMultMonoid.E2`: Local Convergence hypothesis
- `BooleanMultMonoid.E3`: Boundary Mass Saturation hypothesis
- `BooleanMultMonoid.Z`: The associated Dirichlet series
- `BooleanMultMonoid.localFactor`: Local Euler factor F_p(s)
- `BooleanMultMonoid.IsMonoidIso`: Monoid isomorphism (ℕ,★) ≅ (ℕ,·)

Based on the paper by Eduardo Zambrano.
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Classical

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-!
## The Alternative Multiplication Structure

We call it `AltMul` (alternative multiplication) to avoid collision with
Mathlib's `StarMul` class for star-algebras.
-/

/-- An alternative multiplication ★ on ℕ.
    Modeled as an explicit structure (not a typeclass) to avoid diamond
    with ℕ's existing CommMonoid instance. -/
structure AltMul where
  op : ℕ → ℕ → ℕ
  op_pos : ∀ a b, 0 < a → 0 < b → 0 < op a b
  op_assoc : ∀ a b c, op (op a b) c = op a (op b c)
  op_comm : ∀ a b, op a b = op b a
  op_one_left : ∀ a, op 1 a = a
  op_zero_left : ∀ a, op 0 a = 0

namespace AltMul

/-- Right identity follows from left identity and commutativity. -/
theorem op_one_right (S : AltMul) (a : ℕ) : S.op a 1 = a := by
  rw [S.op_comm, S.op_one_left]

/-- Right absorption by zero follows from left absorption and commutativity. -/
theorem op_zero_right (S : AltMul) (a : ℕ) : S.op a 0 = 0 := by
  rw [S.op_comm, S.op_zero_left]

/-- Iterated ★-power: p^{★0} = 1, p^{★(k+1)} = p ★ p^{★k}.
    Defined with explicit S parameter to avoid field notation issues
    in the recursive call. -/
def starPow (S : AltMul) (p : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => S.op p (starPow S p k)

variable (S : AltMul)

@[simp]
theorem starPow_zero (p : ℕ) : S.starPow p 0 = 1 := rfl

@[simp]
theorem starPow_succ (p : ℕ) (k : ℕ) :
    S.starPow p (k + 1) = S.op p (S.starPow p k) := rfl

theorem starPow_one (p : ℕ) : S.starPow p 1 = p := by
  simp [S.op_one_right]

/-- ★-powers of positive numbers are positive. -/
theorem starPow_pos (p : ℕ) (hp : 0 < p) (k : ℕ) : 0 < S.starPow p k := by
  induction k with
  | zero => simp
  | succ n ih => simp; exact S.op_pos p (S.starPow p n) hp ih

/-- ★-irreducible: p ≥ 2 with no nontrivial ★-factorization -/
def IsIrreducible (p : ℕ) : Prop :=
  2 ≤ p ∧ ∀ a b : ℕ, 2 ≤ a → 2 ≤ b → S.op a b ≠ p

theorem IsIrreducible.two_le {p : ℕ} (h : S.IsIrreducible p) : 2 ≤ p := h.1

theorem IsIrreducible.one_lt {p : ℕ} (h : S.IsIrreducible p) : 1 < p := by
  have := h.1; omega

theorem IsIrreducible.pos {p : ℕ} (h : S.IsIrreducible p) : 0 < p := by
  have := h.1; omega

/-- ★-divisibility: a ★-divides b if b = a ★ c for some c -/
def StarDvd (a b : ℕ) : Prop :=
  ∃ c, S.op a c = b

/-- ★-coprimality: m and n share no common ★-irreducible factor -/
def StarCoprime (m n : ℕ) : Prop :=
  ∀ p, S.IsIrreducible p → ¬(S.StarDvd p m ∧ S.StarDvd p n)

/-- Product of ★-powers according to a finsupp.
    Given f : ℕ →₀ ℕ mapping primes to exponents,
    computes p₁^{★f(p₁)} ★ p₂^{★f(p₂)} ★ ⋯ -/
def finsuppStarProd (f : ℕ →₀ ℕ) : ℕ :=
  letI : Std.Commutative S.op := ⟨S.op_comm⟩
  letI : Std.Associative S.op := ⟨S.op_assoc⟩
  f.support.fold S.op 1 (fun p => S.starPow p (f p))

/-- Unique ★-factorization: every n ≥ 2 factors uniquely into ★-irreducibles -/
structure HasUF : Prop where
  exists_factorization : ∀ n, 2 ≤ n → ∃ f : ℕ →₀ ℕ,
    (∀ p ∈ f.support, S.IsIrreducible p) ∧
    S.finsuppStarProd f = n
  unique_factorization : ∀ n, ∀ f g : ℕ →₀ ℕ,
    (∀ p ∈ f.support, S.IsIrreducible p) →
    (∀ p ∈ g.support, S.IsIrreducible p) →
    S.finsuppStarProd f = n → S.finsuppStarProd g = n → f = g

end AltMul

/-!
## Boolean Multiplicative Monoid
-/

/-- Boolean multiplicative monoid (★, A) as in Definition 2.2 of the paper.
    Packages a ★-multiplication with a ★-multiplicative Boolean support set.

    **On (E1) and the Euler product.**  The paper's hypothesis (E1)
    is the Euler product identity Z(s) = ∏_p F_p(s).  Lemma 5.1 of
    the paper derives norm compatibility (m★n = m·n for ★-coprime
    inputs) as a consequence.  In the formalization we axiomatize (E1)
    in its equivalent norm-compatibility form directly as `coprime_mul`,
    because the Euler product identity — an equality between an infinite
    product of Dirichlet series and an infinite sum — would require
    substantial Mathlib infrastructure (infinite products, convergence
    of Dirichlet series) that is not yet available.  The analytic
    content that flows from the Euler product (the mass argument,
    Proposition 6.1) is captured by `support_on_irreducible_powers`
    in Axioms.lean.

    Hypotheses (E2) and (E3) are formalized as `E2` and `E3` below,
    matching the paper's numbering. -/
structure BooleanMultMonoid extends AltMul where
  inSupport : ℕ → Prop
  one_in : inSupport 1
  zero_not_in : ¬ inSupport 0
  star_mult : ∀ m n, 0 < m → 0 < n → toAltMul.StarCoprime m n →
    (inSupport (toAltMul.op m n) ↔ inSupport m ∧ inSupport n)
  has_uf : toAltMul.HasUF
  /-- Hypothesis (E1) in norm-compatibility form (equivalent to the Euler
      product; see Lemma 5.1 of the paper). m★n = m·n for ★-coprime m,n. -/
  coprime_mul : ∀ m n, 0 < m → 0 < n → toAltMul.StarCoprime m n →
    toAltMul.op m n = m * n

namespace BooleanMultMonoid

variable (D : BooleanMultMonoid)

/-!
### Characteristic function
-/

/-- Characteristic function a(n) ∈ {0, 1} -/
def a (n : ℕ) : ℝ :=
  if D.inSupport n then 1 else 0

theorem a_zero_or_one (n : ℕ) : D.a n = 0 ∨ D.a n = 1 := by
  unfold a; split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem a_nonneg (n : ℕ) : 0 ≤ D.a n := by
  unfold a; split_ifs <;> norm_num

theorem a_le_one (n : ℕ) : D.a n ≤ 1 := by
  unfold a; split_ifs <;> norm_num

@[simp]
theorem a_one : D.a 1 = 1 := by
  unfold a; exact if_pos D.one_in

@[simp]
theorem a_zero : D.a 0 = 0 := by
  unfold a; exact if_neg D.zero_not_in

theorem a_eq_one_iff (n : ℕ) : D.a n = 1 ↔ D.inSupport n := by
  constructor
  · intro h; unfold a at h; split_ifs at h with hp
    · exact hp
    · norm_num at h
  · intro h; unfold a; exact if_pos h

theorem a_eq_zero_iff (n : ℕ) : D.a n = 0 ↔ ¬ D.inSupport n := by
  constructor
  · intro h; unfold a at h; split_ifs at h with hp
    · norm_num at h
    · exact hp
  · intro h; unfold a; exact if_neg h

/-!
### Dirichlet series and Euler factors
-/

/-- Local Euler factor F_p(s) = Σ_{k≥0} a(p^{★k}) / (p^{★k})^s -/
def localFactor (p : ℕ) (s : ℝ) : ℝ :=
  ∑' k : ℕ, D.a (D.toAltMul.starPow p k) /
    (D.toAltMul.starPow p k : ℝ) ^ s

/-- Dirichlet series Z(s) = Σ_{n≥0} a(n) / n^s.
    The n=0 term vanishes since (0:ℝ)^s = 0 for s > 0. -/
def Z (s : ℝ) : ℝ :=
  ∑' n : ℕ, D.a n / (n : ℝ) ^ s

/-!
### Hypotheses (E2) and (E3)
-/

/-- (E2) Local Convergence: F_p(1) < ∞ for every ★-irreducible p.
    Formulated as: the local factor series converges at s=1. -/
def E2 : Prop :=
  ∀ p : ℕ, D.toAltMul.IsIrreducible p →
    Summable (fun k : ℕ => D.a (D.toAltMul.starPow p k) /
      (D.toAltMul.starPow p k : ℝ))

/-- (E3) Boundary Mass Saturation: limsup_{s→1+} (s-1)Z(s) ≥ 1.
    Formulated as: for every ε > 0, there exists s ∈ (1, 1+ε) with
    (s-1)Z(s) > 1-ε. -/
def E3 : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ s : ℝ, 1 < s ∧ s < 1 + ε ∧ 1 - ε < (s - 1) * D.Z s

/-!
### Global bound Z(s) ≤ ζ(s)
-/

/-- Global bound: Z(s) ≤ ζ(s) for s > 1.
    Since a(n) ≤ 1 for all n, each term a(n)/n^s ≤ 1/n^s. -/
theorem Z_le_zeta {s : ℝ} (hs : 1 < s) :
    D.Z s ≤ ∑' n : ℕ, 1 / ((n : ℕ) : ℝ) ^ s := by
  unfold Z
  have h_zeta_summable : Summable (fun n : ℕ => 1 / ((n : ℕ) : ℝ) ^ s) :=
    Real.summable_one_div_nat_rpow.mpr hs
  have h_nn : ∀ n : ℕ, 0 ≤ (n : ℝ) ^ s :=
    fun n => Real.rpow_nonneg (Nat.cast_nonneg n) s
  have h_Z_summable : Summable (fun n : ℕ => D.a n / (n : ℝ) ^ s) :=
    Summable.of_nonneg_of_le
      (fun n => div_nonneg (D.a_nonneg n) (h_nn n))
      (fun n => div_le_div_of_nonneg_right (D.a_le_one n) (h_nn n))
      h_zeta_summable
  exact Summable.tsum_le_tsum
    (fun n => div_le_div_of_nonneg_right (D.a_le_one n) (h_nn n))
    h_Z_summable h_zeta_summable

/-!
### Monoid isomorphism
-/

/-- A monoid isomorphism from (ℕ,★) to (ℕ,·). -/
def IsMonoidIso (φ : ℕ → ℕ) : Prop :=
  Function.Bijective φ ∧
  φ 1 = 1 ∧
  ∀ m n, φ (D.toAltMul.op m n) = φ m * φ n

end BooleanMultMonoid

end -- noncomputable section

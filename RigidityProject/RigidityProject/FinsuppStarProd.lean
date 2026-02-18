/-
Copyright (c) 2025 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Multiplicative Extension from Prime Powers

This file proves that if all ★-prime-power factors of a ★-factorization
are in the support, then the full product is in the support.

This was previously axiomatized as Axiom 6. The proof proceeds by
induction on the support of the finsupp, using ★-coprimality of
distinct prime-power factors under unique factorization.

Main result:
- `a_finsuppStarProd`: If a(p^{★f(p)}) = 1 for all p in f.support,
  then a(finsuppStarProd f) = 1.
-/

import RigidityProject.Basic

set_option linter.mathlibStandardSet false

open scoped BigOperators Classical

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace AltMul

variable (S : AltMul)

/-!
## Basic fold lemmas for finsuppStarProd
-/

/-- The ★-product of the empty finsupp is 1. -/
theorem finsuppStarProd_empty : S.finsuppStarProd 0 = 1 := by
  simp [finsuppStarProd, Finsupp.support_zero, Finset.fold_empty]

/-- When p ∈ f.support, finsuppStarProd decomposes as
    starPow p (f p) ★ finsuppStarProd (f.erase p). -/
theorem finsuppStarProd_erase (f : ℕ →₀ ℕ) {p : ℕ} (hp : p ∈ f.support) :
    S.finsuppStarProd f =
    S.op (S.starPow p (f p)) (S.finsuppStarProd (Finsupp.erase p f)) := by
  unfold finsuppStarProd
  letI : Std.Commutative S.op := ⟨S.op_comm⟩
  letI : Std.Associative S.op := ⟨S.op_assoc⟩
  conv_lhs => rw [show f.support = insert p (f.support.erase p) from
    (Finset.insert_erase hp).symm]
  rw [Finset.fold_insert (Finset.notMem_erase p f.support)]
  congr 1
  rw [show (Finsupp.erase p f).support = f.support.erase p from Finsupp.support_erase]
  apply Finset.fold_congr
  intro q hq
  rw [Finsupp.erase_ne (Finset.ne_of_mem_erase hq)]

/-- finsuppStarProd of a single is starPow. -/
theorem finsuppStarProd_single {p k : ℕ} (hk : k ≠ 0) :
    S.finsuppStarProd (Finsupp.single p k) = S.starPow p k := by
  have hp : p ∈ (Finsupp.single p k).support := by
    rw [Finsupp.support_single_ne_zero _ hk]
    exact Finset.mem_singleton.mpr rfl
  rw [S.finsuppStarProd_erase _ hp, Finsupp.single_eq_same]
  have h2 : Finsupp.erase p (Finsupp.single p k) = 0 := by
    ext q; simp [Finsupp.erase_single]
  rw [h2, S.finsuppStarProd_empty, S.op_one_right]

/-- ★-product of a finsupp with ★-irreducible support is positive. -/
theorem finsuppStarProd_pos (f : ℕ →₀ ℕ)
    (hf : ∀ p ∈ f.support, S.IsIrreducible p) :
    0 < S.finsuppStarProd f := by
  induction h : f.support.card generalizing f with
  | zero =>
    have hf0 : f = 0 := Finsupp.support_eq_empty.mp (Finset.card_eq_zero.mp h)
    rw [hf0, S.finsuppStarProd_empty]; omega
  | succ n ih =>
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (by omega : 0 < f.support.card)
    rw [S.finsuppStarProd_erase f hp]
    have hf_erase : ∀ q ∈ (Finsupp.erase p f).support, S.IsIrreducible q := by
      intro q hq
      rw [Finsupp.support_erase] at hq
      exact hf q (Finset.mem_of_mem_erase hq)
    have hcard : (Finsupp.erase p f).support.card = n := by
      rw [Finsupp.support_erase, Finset.card_erase_of_mem hp]; omega
    exact S.op_pos _ _ (S.starPow_pos p (hf p hp).pos (f p))
      (ih _ hf_erase hcard)

/-- For non-empty irreducible support, finsuppStarProd ≥ 2.
    Uses UF uniqueness: if finsuppStarProd f = 1, then f = 0 (the unique
    factorization of 1), contradicting non-empty support. -/
theorem finsuppStarProd_ge_two (huf : S.HasUF) (f : ℕ →₀ ℕ)
    (hf : ∀ p ∈ f.support, S.IsIrreducible p) (hne : f.support.Nonempty) :
    2 ≤ S.finsuppStarProd f := by
  by_contra h
  push_neg at h
  have h_pos := S.finsuppStarProd_pos f hf
  have h_eq : S.finsuppStarProd f = 1 := by omega
  have h_irred_zero : ∀ p ∈ (0 : ℕ →₀ ℕ).support, S.IsIrreducible p := by
    intro p hp; simp [Finsupp.support_zero] at hp
  have h_feq := huf.unique_factorization 1 f 0 hf h_irred_zero
    h_eq S.finsuppStarProd_empty
  rw [h_feq, Finsupp.support_zero] at hne
  simp at hne

/-!
## Factorization lemmas

The key result: if ★-irreducible q divides finsuppStarProd f, then q ∈ f.support.
-/

/-- Incrementing the exponent of q by 1 multiplies the ★-product by q:
    finsuppStarProd (g + single q 1) = q ★ finsuppStarProd g. -/
theorem finsuppStarProd_add_single (g : ℕ →₀ ℕ) (q : ℕ) :
    S.finsuppStarProd (g + Finsupp.single q 1) =
    S.op q (S.finsuppStarProd g) := by
  have hq_mem : q ∈ (g + Finsupp.single q 1).support := by
    rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_same]; omega
  rw [S.finsuppStarProd_erase _ hq_mem]
  have h_val : (g + Finsupp.single q 1 : ℕ →₀ ℕ) q = g q + 1 := by
    rw [Finsupp.add_apply, Finsupp.single_eq_same]
  rw [h_val, S.starPow_succ, S.op_assoc]
  congr 1
  -- erase q (g + single q 1) = erase q g
  have h_erase : Finsupp.erase q (g + Finsupp.single q 1) = Finsupp.erase q g := by
    ext r
    by_cases hrq : r = q
    · subst hrq; simp [Finsupp.erase_same]
    · rw [Finsupp.erase_ne hrq, Finsupp.add_apply, Finsupp.single_apply,
          if_neg (Ne.symm hrq), add_zero, Finsupp.erase_ne hrq]
  rw [h_erase]
  -- op (starPow q (g q)) (finsuppStarProd (erase q g)) = finsuppStarProd g
  by_cases hq_g : q ∈ g.support
  · exact (S.finsuppStarProd_erase g hq_g).symm
  · have hgq : g q = 0 := Finsupp.notMem_support_iff.mp hq_g
    rw [hgq, S.starPow_zero, S.op_one_left]
    congr 1
    ext r
    by_cases hrq : r = q
    · subst hrq; rw [Finsupp.erase_same, hgq]
    · rw [Finsupp.erase_ne hrq]

/-- Key lemma: if ★-irreducible q ★-divides finsuppStarProd f (with f having
    non-empty ★-irreducible support), then q ∈ f.support.

    Proof: build an alternative factorization containing q (by extending the
    UF factorization of the cofactor), then apply UF uniqueness. -/
theorem irred_in_factorization (huf : S.HasUF)
    (f : ℕ →₀ ℕ) (hf : ∀ p ∈ f.support, S.IsIrreducible p)
    (hne : f.support.Nonempty)
    {q : ℕ} (hq : S.IsIrreducible q)
    (hdvd : S.StarDvd q (S.finsuppStarProd f)) :
    q ∈ f.support := by
  obtain ⟨c, hc⟩ := hdvd
  have h_ge2 := S.finsuppStarProd_ge_two huf f hf hne
  have hc_pos : 0 < c := by
    by_contra h; push_neg at h; interval_cases c
    rw [S.op_zero_right] at hc; omega
  have hk1 : (1 : ℕ) ≠ 0 := Nat.one_ne_zero
  by_cases hc1 : c = 1
  · -- c = 1: finsuppStarProd f = q
    rw [hc1, S.op_one_right] at hc
    have h_single_prod : S.finsuppStarProd (Finsupp.single q 1) = q := by
      rw [S.finsuppStarProd_single hk1, S.starPow_one]
    have h_irred_single : ∀ p ∈ (Finsupp.single q 1).support, S.IsIrreducible p := by
      intro p hp
      rw [Finsupp.support_single_ne_zero q hk1, Finset.mem_singleton] at hp
      rwa [hp]
    have h_f_eq := huf.unique_factorization _ f (Finsupp.single q 1) hf h_irred_single
      rfl (by rw [h_single_prod]; exact hc)
    rw [h_f_eq, Finsupp.support_single_ne_zero q hk1]
    exact Finset.mem_singleton.mpr rfl
  · -- c ≥ 2: factor c, build g + single q 1
    obtain ⟨g, hg_irred, hg_prod⟩ := huf.exists_factorization c (by omega)
    set h := g + Finsupp.single q 1 with h_def
    have hh_irred : ∀ p ∈ h.support, S.IsIrreducible p := by
      intro p hp; rw [h_def] at hp
      rcases Finset.mem_union.mp (Finsupp.support_add hp) with hp_g | hp_s
      · exact hg_irred p hp_g
      · rw [Finsupp.support_single_ne_zero q hk1, Finset.mem_singleton] at hp_s
        rwa [hp_s]
    have hh_prod : S.finsuppStarProd h = S.finsuppStarProd f := by
      rw [h_def, S.finsuppStarProd_add_single g q, hg_prod, hc]
    have hq_mem : q ∈ h.support := by
      rw [h_def, Finsupp.mem_support_iff, Finsupp.add_apply,
          Finsupp.single_eq_same]; omega
    rw [huf.unique_factorization _ f h hf hh_irred rfl hh_prod]
    exact hq_mem

/-- If ★-irreducible q ★-divides starPow p k (p ★-irreducible, k ≥ 1), then q = p. -/
theorem irreducible_of_starDvd_starPow (huf : S.HasUF)
    {p q : ℕ} (hp : S.IsIrreducible p) (hq : S.IsIrreducible q)
    {k : ℕ} (hk : 1 ≤ k) (hdvd : S.StarDvd q (S.starPow p k)) :
    q = p := by
  have hk0 : k ≠ 0 := by omega
  have h_irred_single : ∀ r ∈ (Finsupp.single p k).support, S.IsIrreducible r := by
    intro r hr
    rw [Finsupp.support_single_ne_zero p hk0, Finset.mem_singleton] at hr
    rwa [hr]
  have h_ne : (Finsupp.single p k).support.Nonempty := by
    rw [Finsupp.support_single_ne_zero p hk0]; exact Finset.singleton_nonempty p
  have hq_mem := S.irred_in_factorization huf (Finsupp.single p k)
    h_irred_single h_ne hq
    (by rwa [S.finsuppStarProd_single hk0])
  rwa [Finsupp.support_single_ne_zero p hk0, Finset.mem_singleton] at hq_mem

/-- starPow p (f p) and finsuppStarProd(erase p f) are ★-coprime,
    provided (erase p f).support is nonempty. -/
theorem starCoprime_starPow_finsuppStarProd_erase (huf : S.HasUF)
    (f : ℕ →₀ ℕ) (hf : ∀ p ∈ f.support, S.IsIrreducible p)
    {p : ℕ} (hp : p ∈ f.support)
    (hne_erase : (Finsupp.erase p f).support.Nonempty) :
    S.StarCoprime (S.starPow p (f p))
      (S.finsuppStarProd (Finsupp.erase p f)) := by
  intro q hq_irred ⟨hdvd1, hdvd2⟩
  have hfp : 1 ≤ f p := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp)
  have hqp := S.irreducible_of_starDvd_starPow huf (hf p hp) hq_irred hfp hdvd1
  rw [hqp] at hdvd2
  have hf_erase : ∀ r ∈ (Finsupp.erase p f).support, S.IsIrreducible r := by
    intro r hr
    rw [Finsupp.support_erase] at hr
    exact hf r (Finset.mem_of_mem_erase hr)
  have hp_mem := S.irred_in_factorization huf _ hf_erase hne_erase (hf p hp) hdvd2
  rw [Finsupp.support_erase] at hp_mem
  exact Finset.notMem_erase p f.support hp_mem

end AltMul

/-!
## Main theorem: a_finsuppStarProd

Defined at the top level (not in a namespace) to match the signature of the
former axiom, ensuring downstream code in Main.lean works without changes.
-/

/-- **Theorem (formerly Axiom 6)**: If a(p^{★f(p)}) = 1 for all p in f.support,
    then a(finsuppStarProd f) = 1.

    Proved by induction on f.support.card:
    - Empty: finsuppStarProd 0 = 1, a(1) = 1
    - Singleton {p}: finsuppStarProd f = starPow p (f p), use hypothesis
    - ≥ 2 elements: decompose, use coprimality + star_mult + IH -/
theorem a_finsuppStarProd (D : BooleanMultMonoid) (_hE2 : D.E2) (_hE3 : D.E3)
    (f : ℕ →₀ ℕ) (hf : ∀ p ∈ f.support, D.toAltMul.IsIrreducible p)
    (ha : ∀ p ∈ f.support, D.a (D.toAltMul.starPow p (f p)) = 1) :
    D.a (D.toAltMul.finsuppStarProd f) = 1 := by
  induction h : f.support.card generalizing f with
  | zero =>
    rw [Finsupp.support_eq_empty.mp (Finset.card_eq_zero.mp h),
        D.toAltMul.finsuppStarProd_empty]
    exact D.a_one
  | succ n ih =>
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (by omega : 0 < f.support.card)
    rw [D.toAltMul.finsuppStarProd_erase f hp]
    by_cases h_erase_empty : (Finsupp.erase p f).support = ∅
    · -- Singleton case: erase p f = 0
      rw [Finsupp.support_eq_empty.mp h_erase_empty,
          D.toAltMul.finsuppStarProd_empty, D.toAltMul.op_one_right]
      exact ha p hp
    · -- ≥ 2 elements: use coprimality + star_mult + IH
      have hne_erase : (Finsupp.erase p f).support.Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr h_erase_empty
      have h_irred_erase : ∀ q ∈ (Finsupp.erase p f).support,
          D.toAltMul.IsIrreducible q := by
        intro q hq; rw [Finsupp.support_erase] at hq
        exact hf q (Finset.mem_of_mem_erase hq)
      -- IH gives a(finsuppStarProd(erase p f)) = 1
      have ha_rest : D.a (D.toAltMul.finsuppStarProd (Finsupp.erase p f)) = 1 := by
        apply ih
        · exact h_irred_erase
        · intro q hq; rw [Finsupp.support_erase] at hq
          rw [Finsupp.erase_ne (Finset.ne_of_mem_erase hq)]
          exact ha q (Finset.mem_of_mem_erase hq)
        · rw [Finsupp.support_erase, Finset.card_erase_of_mem hp]; omega
      -- Apply star_mult with coprimality
      rw [D.a_eq_one_iff]
      exact (D.star_mult _ _
        (D.toAltMul.starPow_pos p (hf p hp).pos (f p))
        (D.toAltMul.finsuppStarProd_pos _ h_irred_erase)
        (D.toAltMul.starCoprime_starPow_finsuppStarProd_erase
          D.has_uf f hf hp hne_erase)).mpr
        ⟨(D.a_eq_one_iff _).mp (ha p hp),
         (D.a_eq_one_iff _).mp ha_rest⟩

end -- noncomputable section

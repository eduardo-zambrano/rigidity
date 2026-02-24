/-
Copyright (c) 2025 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Section 6: Full Support via the Mass Argument (Proposition 6.1)

This file proves that under (E1)–(E3), a(n) = 1 for all n ≥ 1
and Z(s) = ζ(s) for s > 1.

The analytic core (the mass argument showing a(p^{★k}) = 1 for all
★-irreducibles p and k ≥ 1) is axiomatized in `support_on_irreducible_powers`
(Axioms.lean). Given this axiom, the extension to all n ≥ 1 uses:
- Unique ★-factorization to decompose n into ★-prime powers
- The multiplicative extension theorem `a_finsuppStarProd`

Main results:
- `full_support`: a(n) = 1 for all n ≥ 1
- `Z_eq_zeta`: Z(s) = ζ(s) for s > 1
- `zeta_shift`: index shift ∑ 1/n^s = ∑ 1/(n+1)^s
-/

import RigidityProject.FinsuppStarProd
import RigidityProject.Axioms

set_option linter.mathlibStandardSet false

open scoped BigOperators Classical

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace BooleanMultMonoid

variable (D : BooleanMultMonoid)

/-!
## Proposition 6.1: Full Support

From the mass argument axiom and the multiplicative extension theorem,
we extract a(n) = 1 for all n ≥ 1.
-/

/-- Under (E1)–(E3), a(n) = 1 for all n ≥ 1. -/
theorem full_support (hE2 : D.E2) (hE3 : D.E3) (n : ℕ) (hn : 1 ≤ n) :
    D.a n = 1 := by
  cases n with
  | zero => omega
  | succ m =>
    cases m with
    | zero => simp  -- n = 1
    | succ k =>
      -- n = k + 2 ≥ 2: use unique factorization
      have hn2 : 2 ≤ k + 2 := by omega
      obtain ⟨f, hf_irred, hf_prod⟩ := D.has_uf.exists_factorization (k + 2) hn2
      have ha_factors : ∀ p ∈ f.support, D.a (D.toAltMul.starPow p (f p)) = 1 := by
        intro p hp
        have hfp_pos : 1 ≤ f p := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp)
        exact support_on_irreducible_powers D hE2 hE3 p (hf_irred p hp) (f p) hfp_pos
      rw [← hf_prod]
      exact a_finsuppStarProd D hE2 hE3 f hf_irred ha_factors

/-!
## Z(s) = ζ(s)

Direct consequence of full support: since a(n) = 1 for all n ≥ 1, the Dirichlet
series Z(s) = Σ a(n)/n^s equals Σ 1/n^s = ζ(s).
-/

/-- Under (E1)–(E3), Z(s) = ζ(s) for s > 1 (unshifted index). -/
theorem Z_eq_zeta_pre (hE2 : D.E2) (hE3 : D.E3) {s : ℝ} (hs : 1 < s) :
    D.Z s = ∑' n : ℕ, 1 / ((n : ℕ) : ℝ) ^ s := by
  unfold Z
  apply tsum_congr
  intro n
  cases n with
  | zero => simp [D.a_zero, Real.zero_rpow (by linarith : s ≠ 0)]
  | succ m => rw [D.full_support hE2 hE3 (m + 1) (by omega)]

/-!
## Index Shift for Zeta

The shifted index form ∑_{n≥0} 1/(n+1)^s is sometimes needed for
compatibility with standard formulations.
-/

/-- Index shift: ∑_{n≥0} 1/n^s = ∑_{n≥0} 1/(n+1)^s for s > 1. -/
theorem zeta_shift {s : ℝ} (hs : 1 < s) :
    ∑' n : ℕ, 1 / ((n : ℕ) : ℝ) ^ s =
    ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℝ) ^ s := by
  have h_summable : Summable (fun n : ℕ => 1 / ((n : ℕ) : ℝ) ^ s) :=
    Real.summable_one_div_nat_rpow.mpr hs
  rw [h_summable.tsum_eq_zero_add]
  simp [Real.zero_rpow (by linarith : s ≠ 0)]

/-- Under (E1)–(E3), Z(s) = ζ(s) for s > 1 (shifted index form). -/
theorem Z_eq_zeta (hE2 : D.E2) (hE3 : D.E3) {s : ℝ} (hs : 1 < s) :
    D.Z s = ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℝ) ^ s := by
  rw [D.Z_eq_zeta_pre hE2 hE3 hs, zeta_shift hs]

end BooleanMultMonoid

end -- noncomputable section

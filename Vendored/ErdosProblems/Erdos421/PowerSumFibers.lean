import ErdosProblems.Erdos421.DomainTuples
import Mathlib.Data.ZMod.Basic

/-! # Fiber counts for a complete power-sum system

Fixing the last `m` entries reduces a system with `n + m` entries to a
system with `n` entries. Newton identities then bound each remaining
fiber by `n!`. This also applies in prime fields when `n < p`.
-/

namespace Erdos421

section CommRing

variable {R : Type*} [CommRing R] {s n m : ℕ}

def powerSumVector (n : ℕ) (x : Fin s → R) : Fin n → R :=
  fun j ↦ ∑ i : Fin s, x i ^ ((j : ℕ) + 1)

theorem powerSumVector_eq_iff (x y : Fin s → R) :
    powerSumVector n x = powerSumVector n y ↔
      ∀ k : ℕ, 0 < k → k ≤ n → (∑ i : Fin s, x i ^ k) = ∑ i : Fin s, y i ^ k := by
  constructor
  · intro h k hk hkn
    have hi : k - 1 < n := by omega
    have he := congrFun h ⟨k - 1, hi⟩
    simpa only [powerSumVector, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk.ne')]
      using he
  · intro h
    funext j
    exact h (j + 1) (Nat.succ_pos _) (Nat.succ_le_of_lt j.isLt)

end CommRing

section Domain

variable {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R] {n m : ℕ}

end Domain

end Erdos421

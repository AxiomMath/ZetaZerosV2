/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import ZetaZeros.Hilbert.Defs

/-!
# The non-real part split by multiplicity

The simple non-real part `simpleNonRealPart` (multiplicity one) and the multiple non-real part
`multipleNonRealPart` (multiplicity at least two) of the support of a multiset.
-/

@[expose] public section

namespace ZetaZeros

/-- The simple non-real part of the support: non-real points of multiplicity one. This is the
source's `𝒮₁`, of cardinality `2p`. -/
@[zz_tag "def_S1"]
noncomputable def simpleNonRealPart (Z : Finset ℂ) (m : ℂ → ℕ) : Finset ℂ :=
  Z.filter fun z => z.im ≠ 0 ∧ m z = 1

/-- The multiple non-real part of the support: non-real points of multiplicity at least two. This
is the source's `𝒮₂`, of cardinality `2q`. -/
@[zz_tag "def_S2"]
noncomputable def multipleNonRealPart (Z : Finset ℂ) (m : ℂ → ℕ) : Finset ℂ :=
  Z.filter fun z => z.im ≠ 0 ∧ 2 ≤ m z

end ZetaZeros

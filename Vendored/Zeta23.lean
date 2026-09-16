/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import Zeta23.RvM.Statement
import Zeta23.GammaFacts.Complete
import Zeta23.WeilEF.Main
import Zeta23.ExplicitFormula
import Zeta23.ExplicitFormula.Bridge
import Zeta23.MV.Final
import Zeta23.MV
import Zeta23.Chebyshev
import Zeta23.ZetaReflect
import Zeta23.Statement.SeamClosed

/-!
# Vendored classical inputs from `zeta23`

The modules under `Vendored/Zeta23/` are copied from the `zeta23/` project of
anthropics/formal-math (Apache-2.0; see `NOTICE`), which formalizes Alpöge–Furman's proof.
The retained declarations supply the classical analytic inputs: the Riemann–von Mangoldt formula with its
local zero count, the Weil explicit formula, the Montgomery–Vaughan Hilbert inequality, the
Stirling-type facts for `Γ'/Γ`, Chebyshev–Mertens prime sums, and the reflection symmetry of
zero multiplicities. Necessary spectral-calculus and zero-tail helpers are retained from
`LinAlg` and `Tail`; the headline rank–trace / Gram-matrix argument is not imported.
Unused declarations within the imported modules have been removed.
-/

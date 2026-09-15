import ZetaZeros.Unconditional

example : ZetaZeros.RiemannVonMangoldt :=
  ZetaZeros.Unconditional.riemannVonMangoldt

example : ZetaZeros.PairCorrelation :=
  ZetaZeros.Unconditional.pairCorrelation

#print axioms ZetaZeros.Unconditional.riemannVonMangoldt
#print axioms ZetaZeros.Unconditional.pairCorrelation
#print axioms ZetaZeros.Unconditional.simple_proportion_d4
#print axioms ZetaZeros.Unconditional.distinct_proportion_d5
#print axioms ZetaZeros.Unconditional.average_proportion_d5
#print axioms ZetaZeros.Unconditional.simpleOrOnLine_proportion_d4
#print axioms ZetaZeros.Unconditional.PairCorrelationProof.rawPairCorrelation_asymptotic
#print axioms Erdos421.riemannZeta_eventually_ne_zero_log_power_strip

open Lean Elab Command in
run_cmd do
  let declarations : Array Name := #[
    `ZetaZeros.Unconditional.riemannVonMangoldt,
    `ZetaZeros.Unconditional.pairCorrelation,
    `ZetaZeros.Unconditional.simple_proportion_d4,
    `ZetaZeros.Unconditional.distinct_proportion_d5,
    `ZetaZeros.Unconditional.average_proportion_d5,
    `ZetaZeros.Unconditional.simpleOrOnLine_proportion_d4,
    `ZetaZeros.Unconditional.PairCorrelationProof.rawPairCorrelation_asymptotic,
    `Erdos421.riemannZeta_eventually_ne_zero_log_power_strip]
  let allowedDependencies : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let environment ← getEnv
  for declarationName in declarations do
    unless environment.contains declarationName do
      throwError "Missing audit declaration: {declarationName}"
    let dependencies ← Lean.collectAxioms declarationName
    for dependencyName in dependencies do
      unless allowedDependencies.contains dependencyName do
        throwError "Nonstandard dependency {dependencyName} in {declarationName}"
  logInfo m!"Unconditional audit passed for {declarations.size} declarations"

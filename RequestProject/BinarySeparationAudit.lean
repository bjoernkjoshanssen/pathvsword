import RequestProject.BinarySeparationInfinitude
import Lean.Util.CollectAxioms

/-!
# Kernel dependency audit for binary infinitude

Compilation of this module fails if a public result depends on any axiom beyond
Lean's usual propositional extensionality, classical choice, and quotient soundness.
In particular this checks the transitive dependencies for `sorryAx`, custom
axioms, and native evaluation axioms, even if they arrive through an import.
-/

open Lean in
run_cmd do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets : Array Lean.Name := #[
    ``AneVsAn.BinarySeparation.binary_family_separation,
    ``AneVsAn.BinarySeparation.separation_at_exponential_lengths,
    ``AneVsAn.BinarySeparation.binary_separations_unbounded_lengths,
    ``AneVsAn.BinarySeparation.infinite_binary_separations,
    ``AneVsAn.BinarySeparation.infinite_binary_separation_lengths]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    let unexpected := axioms.filter (fun axiomName => !allowed.contains axiomName)
    unless unexpected.isEmpty do
      throwError "Unexpected axioms in {target}: {unexpected}"
  logInfo "Binary separation audit passed: all five public results use only standard Lean axioms."

#print axioms AneVsAn.BinarySeparation.infinite_binary_separations
#print axioms AneVsAn.BinarySeparation.infinite_binary_separation_lengths

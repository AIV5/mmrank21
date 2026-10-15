import MMRank
import Lean

/-! Audit the public theorem and every declaration in the imported project.
This audit runs after the build and adds no assumptions to the proof library. -/

#check @MMRank.matrix_multiplication_length_ge_twenty_one
#check @MMRank.ExactAlgorithm.length_bound_twenty_one
#check @MMRank.ExactAlgorithm.length_bound_two_by_two
#check @MMRank.ExactAlgorithm.length_22n_ge_ceil
#print axioms MMRank.matrix_multiplication_length_ge_twenty_one
#print axioms MMRank.ExactAlgorithm.length_bound_twenty_one
#print axioms MMRank.ExactAlgorithm.length_bound_two_by_two
#print axioms MMRank.ExactAlgorithm.length_22n_ge_ceil

open Lean in
run_elab do
  let env ← getEnv
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    unless (`MMRank).isPrefixOf env.header.moduleNames[i]! do continue
    for ci in env.header.moduleData[i]!.constants do
      if env.getModuleIdxFor? ci.name != some i then continue
      for ax in ← collectAxioms ci.name do
        unless allowed.contains ax do
          throwError "Disallowed axiom {ax} in {ci.name}"
      count := count + 1
  if count == 0 then throwError "No project declarations were audited"
  logInfo m!"PASS: {count} project declarations use only propext, Classical.choice, Quot.sound."

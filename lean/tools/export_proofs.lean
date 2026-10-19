import Lean

/-!
# The declarations checked by Lean

Load completed roots and print their theorem names, exact elaborated types,
direct proof dependencies and axiom dependencies as JSON. A comma-separated
list reads compatible roots in one environment. The exterior and matrix
libraries are read in separate environments with their own declaration names.

Run from `lean/` after `lake build`:

    lake env lean --run tools/export_proofs.lean Comparison.System proofs.json
-/

open Lean

private def nameArray (names : Array Name) : Json :=
  toJson (names.map Name.toString)

private def records : CoreM (Array Json) := do
  let env ← getEnv
  let mut rows := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let moduleName := env.header.moduleNames[idx.toNat]!
    if !(moduleName.toString.startsWith "Comparison") then continue
    let .thmInfo val := info | continue
    let axioms ← collectAxioms name
    let dependencies := info.getUsedConstantsAsSet.toArray.qsort Name.lt
    let projectDependencies := dependencies.filterMap fun dependency => do
      let idx ← env.getModuleIdxFor? dependency
      let dependencyModule := env.header.moduleNames[idx.toNat]!
      if !(dependencyModule.toString.startsWith "Comparison") then none
      else some <| Json.mkObj [
        ("name", toJson dependency.toString),
        ("module", toJson dependencyModule.toString)]
    rows := rows.push <| Json.mkObj [
      ("name", toJson name.toString),
      ("module", toJson moduleName.toString),
      ("elaborated_type", toJson (toString val.type)),
      ("direct_dependencies", nameArray dependencies),
      ("project_dependencies", Json.arr projectDependencies),
      ("axioms", nameArray axioms)]
  return rows

unsafe def main (args : List String) : IO Unit := do
  let [root, destination] := args
    | throw <| IO.userError "Usage: lake env lean --run tools/export_proofs.lean ROOT[,ROOT...] OUTPUT.json"
  initSearchPath (← findSysroot)
  let roots := (root.splitOn ",").toArray
  let env ← importModules (roots.map fun name => {module := name.toName}) {} (loadExts := false)
  let rows ← records.toIO' {fileName := "<proof index>", fileMap := default} {env := env}
  IO.FS.writeFile destination <| (Json.mkObj [
    ("roots", toJson roots), ("theorems", Json.arr rows)]).pretty ++ "\n"
  IO.println s!"{roots.size} import roots: {rows.size} theorem declarations read from the compiled environment"

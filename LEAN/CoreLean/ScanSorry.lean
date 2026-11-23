import CoreLean
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut bad : Array Name := #[]
  let mut count : Nat := 0
  for (n, ci) in env.constants.toList do
    if (`CoreLean).isPrefixOf n then
      count := count + 1
      let usesSorry := (ci.value?.map (·.getUsedConstants.contains ``sorryAx)).getD false ||
        ci.type.getUsedConstants.contains ``sorryAx
      if usesSorry then bad := bad.push n
  logInfo m!"declarations in CoreLean: {count}; with sorryAx: {bad.size} {bad.toList}"

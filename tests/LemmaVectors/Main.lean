/-
  `lake exe lemma-vectors [--write]` — (re)generate `vectors/*.json`. Without `--write`, fails if
  a committed vector file is missing or stale.
-/
import LemmaTest.Vectors

def main (args : List String) : IO UInt32 := do
  let write := args.contains "--write"
  let mut bad := 0
  for (path, content) in LemmaTest.Vectors.files do
    if write then
      IO.FS.createDirAll "vectors"
      IO.FS.writeFile path content
      IO.println s!"wrote {path}"
    else
      match (← (IO.FS.readFile path).toBaseIO) with
      | .ok cur => if cur != content then IO.eprintln s!"stale: {path}"; bad := bad + 1
      | .error _ => IO.eprintln s!"missing: {path}"; bad := bad + 1
  if bad > 0 then IO.eprintln "run `lake exe lemma-vectors --write`"
  return if bad == 0 then 0 else 1

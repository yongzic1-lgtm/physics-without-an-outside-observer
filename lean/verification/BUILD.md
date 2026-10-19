# Checking the proof development

The development pins Lean 4.35.0 and its Mathlib revision in `lean-toolchain`, `lakefile.toml` and
`lake-manifest.json`. From `lean/`:

```sh
python tools/check_sources.py
lake exe cache get
LEAN_NUM_THREADS=1 lake build Comparison.System
LEAN_NUM_THREADS=1 lake build
LEAN_NUM_THREADS=1 xargs lake build < verification/additional_roots.txt
lake env lean Comparison/System/Audit/Axioms.lean
```

`additional_roots.txt` lists the modules outside the default roots of `lakefile.toml`. A complete build compiles
every module of `Comparison`; `Comparison/System/Audit/Axioms.lean` prints the axioms each named theorem uses.
Building Mathlib from source needs much memory; `lake exe cache get` downloads its compiled files instead.

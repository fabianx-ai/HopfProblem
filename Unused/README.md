# Unused

Proved declarations that no other declaration of the project uses: neither for Mathlib nor anything else, they just exist.
A declaration gets here by a verbatim move out of `Lib` (statement, proof, docstring, attributes unchanged; at most a visibility modifier), checked by an environment diff that shows module moves only.
Modules here may import `Lib` (also `import all` of a `Lib` module for its private helpers); nothing imports `Unused`.
`Unused` is not a default target: build it with `lake build Unused` (and `lake build Unused.AxiomAudit` for its axiom probes).
Each move has a receipt under `Lib/reports/unused/`.

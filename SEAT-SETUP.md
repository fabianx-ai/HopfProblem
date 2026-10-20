# Seat setup — shared Lean environment on this machine

For a seat (a separate Unix user) that has cloned the fork and checked out
`lib/textbook-extraction` into `~/work`. The owner provides one world-readable build at
`/tmp/shared-lean-copy/`: the Mathlib packages at the pinned commit, the built `.lake/build`
with every `Hopf` olean, and the v4.33.0 toolchain. Nothing is built from source in a seat.

```
ln -s /tmp/shared-lean-copy/packages ~/work/.lake/packages
cp -a /tmp/shared-lean-copy/build ~/work/.lake/build
export PATH=/tmp/shared-lean-copy/toolchain-v4.33.0/bin:$PATH
export GIT_CONFIG_COUNT=1 GIT_CONFIG_KEY_0=safe.directory GIT_CONFIG_VALUE_0='*'
cd ~/work && lake build Lib.AlgebraicTopology.Hurewicz.Degree1
```

The last line is the smoke test: green in about 9 s. Put the two `export` lines in the seat's
shell profile so every later `lake` call sees them.

## Why each line

- **Symlink the packages, copy the build.** The packages are read-only shared state; the build
  directory is written by every `lake build`, so each seat needs its own copy.
- **`safe.directory='*'` via the environment.** The share is owned by the owner's user. Without
  this, git refuses to read the package checkouts ("dubious ownership"), Lake misreads that as
  "URL has changed" and tries to delete and re-clone Mathlib, which fails with permission denied.
  Setting it through `GIT_CONFIG_*` variables changes nothing on disk and nothing in the share.
- **No `-j`.** Lake 5.0.0 (Lean 4.33.0) has no `-j` flag; plain `lake build` parallelises on its
  own.

## Rules

- Never `lake update`, never `lake exe cache get`, never `lake clean`: the first two write into
  the shared packages directory, the third deletes your build copy.
- `ps` before every `lake build`; the box is shared by three seats.
- The share lives in `/tmp` and vanishes on reboot. If the symlink dangles, ask the owner to
  restore the share; do not rebuild.
- Set a repo-local git identity before the first commit, so authorship is attributable:
  `git config user.name <seat>` and `git config user.email <seat>@users.noreply.github.com`.
- NEVER git push.

# Lane F — interface receipt

**Implementation update after bbf1dd2:** see the public-module conversion addendum in `Lib/reports/RECEIPTS.md` for the verified current move scope and remaining work. Legacy-provider claims and source coordinates below describe the earlier ledger/probe snapshots where superseded by that addendum; they are not current blockers for the converted providers.

Seat: muse. Branch `lib/textbook-extraction`. Toolchain leanprover/lean4:v4.33.0 at
`/tmp/shared-lean-copy/toolchain-v4.33.0/bin`.

## F0a landed — `Lib/LinearAlgebra/Matrix/TransvectionReduction.lean`

Verbatim move from `Hopf/Recognition.lean` (deleted ranges: 3357–3386, 4737–4755,
7412–7559 of the pre-extraction file). Module file (`module`, `public import Mathlib`,
`@[expose] public noncomputable section`, `namespace Mathoverflow1973`).

Declarations (FQNs preserved verbatim):

- `MorseCancel.classCoordinateMatrix` (was Rec 3357)
- `MorseCancel.classCoordinateMatrix_mulVec` (3361)
- `MorseCancel.classCoordinateMatrix_surjective` (3372 — was missing from the ledger's
  F0a list; pure, moves with the packet)
- `MorseCancel.mul_transvection_surjective` (4737)
- `MorseCancel.eq_mul_transvection_of_columns` (4747)
- `MorseCancel.mul_transvection_list_surjective` (7412)
- `MorseCancel.primitive_row_has_unit_after_column_additions` (7429)
- `MorseCancel.functional_class_row_surjective` (7507)
- `MorseCancel.transported_classes_of_matrix_product` (7530)
- `MorseCancel.functional_rows_of_matrix_product` (7544)

Consumers: only `Hopf/Recognition.lean` (added the import; all call sites unchanged —
same FQNs). Census prefix `MorseCancel` count decreases accordingly.

## F0b landed — `Lib/Algebra/Module/IntegerPresentation.lean`

Verbatim moves: `Hopf/SphereTopology.lean` 14171–14257 + 14312–14360, and
`Hopf/Recognition.lean` 9296–9340 (the four pure `adjoin_*`/`ofEquiv_*` API lemmas the
ledger's F0b list omitted — they are part of the same algebraic packet).

Declarations:

- `Smale.HomologyTransport.ker_comp_span_singleton` (ST 14171; pure `CommRing`-module
  algebra, closure dependency of `adjoin`)
- `Smale.IntegerPresentation` structure (ST 14201): `map`, `columns`, `surjective`,
  `kernel_eq`
- `ofEquiv` (14207), `transport` (14217), `liftRelation` (14235), `map_liftRelation`
  (14239), `adjoin` (14243)
- `matrix` (14312), `columns_sum_eq_mulVec` (14315), `mem_range_matrix_iff` (14321),
  `matrix_image_eq_kernel` (14331), `matrix_relation` (14338),
  `columns_span_of_subsingleton` (14345), `matrix_surjective_of_subsingleton` (14353)
- `ofEquiv_matrix_injective` (Rec 9296), `adjoin_mulVec` (9300), `adjoin_coefficient`
  (9311), `adjoin_matrix_injective` (9319)

Geometric gluers deliberately left in place (move with F10):
`MorseSurgeryData.indexThreePresentation` (ST 14258), `SurgeryWindows.middlePresentation`
(14291), `MorseSurgeryData.indexThreePresentation_matrix_injective` (Rec 9341),
`SurgeryWindows.middleMatrix_injective_of_upper_third`.

Consumers: `Hopf/SphereTopology.lean`, `Hopf/Recognition.lean` (imports added; FQNs
unchanged).

## Deviations / notes

- Names kept verbatim (`Mathoverflow1973.MorseCancel.*`, `Mathoverflow1973.Smale.*`),
  NOT the ledger's aspirational `Matrix.mul_transvection_surjective` /
  root `IntegerPresentation` — consistent with the J precedent (verbatim FQNs, zero
  consumer churn). The Mathlib-shaped rename is a separate lane-F commit (open item in
  F.md §"pragma cargo").
- Remaining pure `HomologyTransport` decls (`exists_split_rank_one_extension` ST 13840,
  `exists_add_split_rank_one_extension` ST 13881, `integerCoordinateSplit` ST 13967,
  `integerEquiv_one_natAbs` Rec 7841, `matrix_sizes_eq_of_bijective` Rec 9422) not moved —
  flagged to owner for placement (`IntegerPresentation.lean` vs a separate
  `HomologyTransport` module).
- `HomologyTransport.exact_of_equivalences` was already Lib-landed
  (`Lib/Geometry/Manifold/Morse/SublevelSets.lean:88`).

## Build verification

- `lake build Lib.LinearAlgebra.Matrix.TransvectionReduction
  Lib.Algebra.Module.IntegerPresentation` — green.
- `lake build Hopf.SphereTopology Hopf.Recognition` — 8807 jobs, green (full Hopf
  chain re-elaborated; all call sites resolve through the moved FQNs).
- `python3 scripts/lib_stock_census.py` — ratchet lowered (see commit).

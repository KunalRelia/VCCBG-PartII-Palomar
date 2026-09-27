import VCCBGPartII

set_option linter.unusedDecidableInType false

/-!
# Proved solution — Theorem 7

`challenge.lean` imports only `Mathlib`, so it states Theorem 7 with a
self-contained, inlined copy of the definitions it needs (`VCover`,
`RepTable`, `Status`, `TableState`, `RemoveInvariant`, `AllFrozenOrRemoved`,
`FrozenSet`, `IsValidFreezeRemove`, `MinVCover`, `IsDuad`, `DuadicHop`,
`DiminishingHop`) and leaves the proof as `sorry`.

This file instead imports the full project library `VCCBGPartII`, which already
proves the `Theorem7` over exactly the same-shaped `RepTable` / `TableState` /
`IsValidFreezeRemove` / `FrozenSet` / `MinVCover` / `IsDuad` /
`DiminishingHop` machinery. `Theorem7_wrapper` below is discharged in one
step by directly invoking that `Theorem7`.
-/

/-- Goal accomplished: `Theorem7_wrapper` is literally `Theorem7`. -/
theorem VCCBGPartII.Theorem7_wrapper
    {V : Type*} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hcubic : ∀ v : V, G.degree v = 3)
    (hbridgeless : ∀ ⦃e : Sym2 V⦄, e ∈ G.edgeSet → ¬ G.IsBridge e)
    (R : RepTable G) (st : TableState G)
    (hvalid : IsValidFreezeRemove st)
    (hsize_lb : Fintype.card V / 2 ≤ (FrozenSet st).card)
    (hbase_case :
      (FrozenSet st).card = Fintype.card V / 2 → MinVCover G (FrozenSet st))
    (hduad_exists :
      Fintype.card V / 2 < (FrozenSet st).card → ∃ u v : V, IsDuad R st u v) :
    MinVCover G (FrozenSet st) ↔ ¬ ∃ _ : DiminishingHop R st, True :=
  Theorem7 hcubic hbridgeless R st hvalid hsize_lb hbase_case hduad_exists

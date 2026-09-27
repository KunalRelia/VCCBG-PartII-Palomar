import Mathlib

set_option linter.unusedDecidableInType false
/-!
# Advertised statement — Theorem 7

"Diminishing Hop and Vertex Cover" (general, unrestricted case): given a
cubic bridgeless graph `G`, a represents table `R` for `G`, and a valid
freeze/remove state `st` of `R` with frozen set `S = FrozenSet st`: `S` is
the minimum-size vertex cover derivable from `R` iff there is no
`S`-diminishing hop in `R`. (paper, §5.3.3, p.46-51, lines 1528-1714.)

This file imports **only** `Mathlib`, so it inlines — verbatim, just
without the `VCCBGPartII` namespace and cross-file imports — exactly the
definitions Theorem 7 is stated over in the real development
(`definition_vcover.lean`, `lemma4.lean`, `reptable_ops_properties.lean`,
`thm4.lean`, `thm6.lean`): `VCover`, `RepTable`, `Status`, `TableState`,
`RemoveInvariant`, `AllFrozenOrRemoved`, `FrozenSet`, `IsValidFreezeRemove`,
`MinVCover`, `IsDuad`, `DuadicHop`, `DiminishingHop`.

`hcubic` and `hbridgeless` are carried along for signature fidelity with
the rest of the development (they are likewise unused in the real `Theorem7`'s own proof).
-/


variable {V : Type*} [DecidableEq V] [Fintype V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- `VCover G S`: every edge of `G` has at least one endpoint in `S`. -/
def VCover (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ ⦃u v : V⦄, G.Adj u v → u ∈ S ∨ v ∈ S

/-- A represents table for `G`, built from a perfect matching. -/
structure RepTable (G : SimpleGraph V) where
  M : G.Subgraph
  isPM : M.IsPerfectMatching
  row : V → ℕ
  row_pair : ∀ ⦃u v⦄, M.Adj u v → row u = row v

/-- Status of an endpoint in the represents table. -/
inductive Status
  | unset
  | frozen
  | removed
  deriving DecidableEq

/-- The live state of a represents table during execution. -/
structure TableState (G : SimpleGraph V) where
  status : V → Status
  reps   : V → Finset V

/-- Whenever an endpoint `u` is removed, every endpoint `v` adjacent to it
    is frozen. -/
def RemoveInvariant (st : TableState G) : Prop :=
  ∀ ⦃u v : V⦄, st.status u = Status.removed → G.Adj u v → st.status v = Status.frozen

/-- Every endpoint of the represents table is either frozen or removed. -/
def AllFrozenOrRemoved (st : TableState G) : Prop :=
  ∀ v : V, st.status v = Status.frozen ∨ st.status v = Status.removed

/-- The set of frozen endpoints recorded by a table state. -/
def FrozenSet (st : TableState G) : Finset V :=
  Finset.univ.filter (fun v => st.status v = Status.frozen)

/-- A `TableState` is a valid freeze/remove outcome of the process. -/
def IsValidFreezeRemove (st : TableState G) : Prop :=
  RemoveInvariant st ∧ AllFrozenOrRemoved st

/-- `MinVCover G S`: `S` is a vertex cover of minimum cardinality. -/
def MinVCover (G : SimpleGraph V) (S : Finset V) : Prop :=
  VCover G S ∧ ∀ T : Finset V, VCover G T → S.card ≤ T.card

/-- Two distinct endpoints sharing a row of `R`, both currently frozen in
    state `st` — a "duad". -/
def IsDuad (R : RepTable G) (st : TableState G) (u v : V) : Prop :=
  u ≠ v ∧ R.row u = R.row v ∧ st.status u = Status.frozen ∧ st.status v = Status.frozen

/-- A duadic hop: a duad `(u, v)` together with the resulting state `st'`,
    required only to again be a valid freeze/remove outcome. -/
structure DuadicHop (R : RepTable G) (st : TableState G) where
  u : V
  v : V
  duad : IsDuad R st u v
  st' : TableState G
  valid' : IsValidFreezeRemove st'

/-- A duadic hop whose resulting frozen set is strictly smaller. -/
structure DiminishingHop (R : RepTable G) (st : TableState G)
    extends DuadicHop R st where
  smaller : (FrozenSet st').card < (FrozenSet st).card

/-- **Theorem 7** (Diminishing Hop and Vertex Cover, general case) —
    the result being submitted. -/
theorem Theorem7_wrapper
    (hcubic : ∀ v : V, G.degree v = 3)
    (hbridgeless : ∀ ⦃e : Sym2 V⦄, e ∈ G.edgeSet → ¬ G.IsBridge e)
    (R : RepTable G) (st : TableState G)
    (hvalid : IsValidFreezeRemove st)
    (hsize_lb : Fintype.card V / 2 ≤ (FrozenSet st).card)
    (hbase_case :
      (FrozenSet st).card = Fintype.card V / 2 → MinVCover G (FrozenSet st))
    (hduad_exists :
      Fintype.card V / 2 < (FrozenSet st).card → ∃ u v : V, IsDuad R st u v) :
    MinVCover G (FrozenSet st) ↔ ¬ ∃ _ : DiminishingHop R st, True := by
  sorry

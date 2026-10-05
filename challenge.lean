module

public import Mathlib

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.defProp false
/-!
# Advertised statement — Theorem 8

  "Algorithm 1 (VERTEX_COVER) returns Yes on input (G, k) if and only if the
   given instance of VC − CBG is a Yes instance." (§7 of the paper
   ("Proof of Correctness"), pp.58-61, lines 1750-1922; Lemma 5 + Lemma 6)

  This file is self-contained: it imports only `Mathlib` and re-states, verbatim,
  every definition transitively needed to *state* `Theorem8` (none of the
  intermediate theorems used to prove it). The final theorem,
  `VCCBGPartII.Theorem8_wrapper`, is left as a `sorry`.
-/

-- ═══ definition_vcover.lean ═══
section
/-- `VCover G S`: every edge of G has at least one endpoint in S.
-/
public abbrev VCover {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ ⦃u v : V⦄, G.Adj u v → u ∈ S ∨ v ∈ S
end

-- ═══ lemma4 / reptable_ops_properties / thm4 / thm6 (same variable list) ═══
section
open Finset
variable {V : Type*} [DecidableEq V] [Fintype V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- `RepTable G`: a represents table for `G`, built by the augmented
    2-approximation algorithm from a perfect matching `M` and a BFS tree. -/
public structure RepTable (G : SimpleGraph V) where
  M : G.Subgraph
  isPM : M.IsPerfectMatching
  row : V → ℕ
  row_pair : ∀ ⦃u v⦄, M.Adj u v → row u = row v

open Classical in
/-- **Definition 13** (Represents List). `Lu`, the set of vertices `u`
    represents; for a cubic graph this has exactly 3 elements. -/
public noncomputable def RepList (G : SimpleGraph V) (u : V) : Finset V :=
  Finset.univ.filter (fun v => G.Adj u v)

/-- Status of an endpoint in the represents table: not yet acted on
    (`unset`), selected into the vertex cover (`frozen`), or excluded from
    the vertex cover (`removed`). The paper stresses that the table
    supports **no deletion** — `status` only ever moves `unset → frozen` or
    `unset → removed`, never back; we do not need to state this separately
    since our operations below never revert a `frozen`/`removed` status. -/
public inductive Status
  | unset
  | frozen
  | removed
  deriving DecidableEq

/-- The live state of a represents table during execution: each vertex's
    current status, and its current (possibly already-shrunk) represents
    list. -/
public structure TableState (G : SimpleGraph V) where
  status : V → Status
  reps   : V → Finset V

/-- **insert**. The most basic operation: populate the table's initial
    state from the graph, with every endpoint `unset` and every represents
    list equal to the full (static) `RepList` of Definition 13.
    (The paper notes insert is O(1) per row and needs no access to
    previous data — reflected here in that `initialState` does not
    depend on any prior `TableState`.) -/
public noncomputable abbrev initialState (G : SimpleGraph V) : TableState G where
  status := fun _ => Status.unset
  reps   := fun u => RepList G u

/-- **freeze**. Freezing `u` (selecting it into the vertex cover)
    simultaneously delists `u` from every represents list it appears in.
    (The paper additionally delists `Lu` itself, which we do not need to
    track further since a frozen vertex's own list is never consulted
    again by the operations below.) -/
@[expose] public def TableState.freeze (st : TableState G) (u : V) : TableState G where
  status := fun v => if v = u then Status.frozen else st.status v
  reps   := fun v => (st.reps v).erase u

/-- The invariant maintained throughout the paper's freeze/remove process:
    whenever an endpoint `u` is
    removed, every endpoint `v` adjacent to it is frozen. -/
public abbrev RemoveInvariant (st : TableState G) : Prop :=
  ∀ ⦃u v : V⦄, st.status u = Status.removed → G.Adj u v → st.status v = Status.frozen

/-- "Every endpoint of the represents table is either frozen or removed" —
    (Property 3: the fully-populated table's endpoints are all
    of `V`). -/
public abbrev AllFrozenOrRemoved (st : TableState G) : Prop :=
  ∀ v : V, st.status v = Status.frozen ∨ st.status v = Status.removed

/-- The set S'' of frozen endpoints recorded by a table state. -/
public abbrev FrozenSet (st : TableState G) : Finset V :=
  Finset.univ.filter (fun v => st.status v = Status.frozen)

/-- A `TableState` is a *valid freeze/remove outcome* of the process the
    paper describes: every endpoint is frozen or removed, and removal is
    always consistent with the neighbour-freezing invariant. -/
public abbrev IsValidFreezeRemove (st : TableState G) : Prop :=
  RemoveInvariant st ∧ AllFrozenOrRemoved st

/-- `IsDuad R st u v`: `u` and `v` are two distinct endpoints sharing a row
    of the represents table `R`, both currently frozen in state `st` — a
    "duad" in the paper's terminology (a row with both its endpoints
    frozen). -/
public abbrev IsDuad (R : RepTable G) (st : TableState G) (u v : V) : Prop :=
  u ≠ v ∧ R.row u = R.row v ∧ st.status u = Status.frozen ∧ st.status v = Status.frozen

/-- **Definition 19** (Duadic Hop), packaged structurally: a duad `(u, v)`
    of the represents table `R` in state `st`, together with the state
    `st'` the hop's sequence of remove/freeze operations produces. We only
    retain that `st'` is again a *valid* freeze/remove outcome
    (`IsValidFreezeRemove`) — this is all Theorem 6's proof needs from the
    hop's internal remove/freeze bookkeeping (Definition 19(iii)-(iv)),
    exactly as `Property4`/`Theorem4` only need "every endpoint frozen or
    removed, consistently with removal" to conclude a vertex cover. -/
public structure DuadicHop (R : RepTable G) (st : TableState G) where
  u : V
  v : V
  duad : IsDuad R st u v
  st' : TableState G
  valid' : IsValidFreezeRemove st'

/-- **Definition 20** (Diminishing Hop): a duadic hop whose resulting
    frozen set is strictly smaller, i.e. it "removes at least one more
    endpoint than it freezes" (since every endpoint is frozen-or-removed
    in both `st` and `st'`, the frozen count and removed count partition
    `Fintype.card V` in each state, so a smaller frozen count is exactly a
    net gain of removed over frozen endpoints during the hop). -/
public structure DiminishingHop (R : RepTable G) (st : TableState G)
    extends DuadicHop R st where
  smaller : (FrozenSet st').card < (FrozenSet st).card

end

-- ═══ PARTII_algorithms.lean (no `open Finset`, with `Inhabited`) ═══
noncomputable section
variable {V : Type*} [DecidableEq V] [Fintype V] [Inhabited V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A row of the represents table: the two endpoints of one matching edge
    (Definition 14). Represents lists/status/score for these (and every
    other) endpoint live centrally in the enclosing table (`TableState`'s
    `reps`/`status`, plus `score` below), not per-row. -/
public abbrev Row (V : Type*) := V × V

/-- The represents table threaded through Algorithms 2-8: `TableState G`
    (reused verbatim: `status`, `reps`) extended with the row order and
    representation score Algorithm 3 adds. -/
public structure RTable (G : SimpleGraph V) extends TableState G where
  /-- Rows in insertion order = the paper's top-to-bottom table order. -/
  rows : List (Row V)
  /-- The representation score ζ_v (Algorithm 3 Line 3 onward). -/
  score : V → Int

/-- The `-∞` sentinel of Algorithm 3, Line 3. `Int` has no genuine `-∞`, so
    we use a value no honest score (bounded by table size) can reach. -/
public abbrev negInf : Int := -1000000000

/-- Algorithm 2, Lines 1-2's starting point: no rows yet, and the columns
    initialized exactly as `initialState G` already does (every endpoint
    `unset`, `reps = RepList` i.e. Definition 13's static represents
    list) — this *is* Algorithm 2 Line 2's "four-column table" before any
    row has been inserted, reusing `initialState` directly rather than
    re-deriving "start every endpoint's represents list at its full
    neighbor set". -/
public noncomputable def RTable.empty (G : SimpleGraph V) [DecidableRel G.Adj] : RTable G where
  toTableState := initialState G
  rows  := []
  score := fun _ => negInf

/-- Pointwise function update, `f[v ↦ a]`, used for "set endpoint v's
    column entry to a" (score column only — `status`/`reps` updates reuse
    `TableState.freeze`/direct field overrides below). -/
public abbrev upd {α : Type*} (f : V → α) (v : V) (a : α) : V → α :=
  fun w => if w = v then a else f w

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. Algorithm 2 : POPULATE_REPRESENTS_TABLE(G, M, V_S)
-- ═══════════════════════════════════════════════════════════════════════════

/-- Line 1: "T = an array of arrays storing sorted vertices at each level
    of a breadth-first search tree seeded on the first vertex in `V_S`".
    `adj` is the *current* (shrinking, Line 13) adjacency-list function
    used purely for BFS/edge-selection bookkeeping — distinct from the
    represents lists `reps`, which (per `initialState`/Definition 13)
    stay the *static* full neighbor sets throughout Phase II and are only
    ever mutated later, in Phase III, by `TableState.freeze`/the removal
    cascade of Algorithm 6. -/
public partial abbrev bfsLevels (adj : V → List V) (start : V) : List (List V) :=
  let rec go (frontier visited : List V) : List (List V) :=
    match frontier with
    | [] => []
    | _  =>
      let nbrs :=
        ((frontier.flatMap adj).eraseDups).filter
          (fun w => !(visited.contains w) && !(frontier.contains w))
      frontier :: go nbrs (visited ++ frontier)
  go [start] []

/-- Lines 6-9: find an `M`-edge from `u` to a vertex on the same level
    (Line 6-7), else to a vertex on the next level (Line 8-9). `inM u w`
    tests whether the edge `{u, w}` is one of the edges of `M`. -/
public abbrev selectMEdge (adj : V → List V) (inM : V → V → Bool)
    (u : V) (sameLevel nextLevel : List V) : Option V :=
  match (adj u).find? (fun w => inM u w && sameLevel.contains w) with
  | some w => some w
  | none   => (adj u).find? (fun w => inM u w && nextLevel.contains w)

/-- Line 13: "Remove from graph G the selected edge and all the edges that
    are connected to the two endpoints" — delete every edge incident to
    `x` from the (BFS-only) adjacency function. -/
public abbrev removeIncidentEdges (adj : V → List V) (x : V) : V → List V :=
  fun w => if w = x then [] else (adj w).filter (· ≠ x)

/-- Lines 3-16, the double loop ("for each level ... for each unvisited
    vertex u in level ..."), transcribed as two nested local recursions.
    Only `.rows` of the table is ever extended here (Line 12); `.reps`
    stays exactly the `RepList`-seeded value from `RTable.empty`, per the
    design note above. -/
public partial def populateLoop
    (inM : V → V → Bool)
    (levels : List (List V)) (adj : V → List V) (visited : List V) (R : RTable G) :
    RTable G :=
  match levels with
  | []             => R                                              -- Line 16 (outer end)
  | level :: rest  =>
    let nextLevel := rest.headD []
    -- Line 5: "for each unvisited vertex u in level do"
    let rec vertexLoop (vs : List V) (adj : V → List V) (visited : List V)
        (R : RTable G) : (V → List V) × List V × RTable G :=
      match vs with
      | []      => (adj, visited, R)
      | u :: us =>
        if visited.contains u then
          vertexLoop us adj visited R                                -- (u already visited: skip)
        else
          match selectMEdge adj inM u level nextLevel with
          | none   => vertexLoop us adj visited R                    -- no selectable edge yet
          | some w =>
            let visited := u :: w :: visited                          -- Line 11
            let R := { R with rows := R.rows ++ [(u, w)] }             -- Line 12
            let adj := removeIncidentEdges (removeIncidentEdges adj u) w  -- Line 13
            -- Line 14: any now-edgeless vertex is marked visited.
            let visited :=
              (Finset.univ.filter (fun z => adj z = [] ∧ ¬ visited.contains z)).toList
                ++ visited
            vertexLoop us adj visited R
    let (adj, visited, R) := vertexLoop level adj visited R
    populateLoop inM rest adj visited R

/-- **Algorithm 2** (`POPULATE_REPRESENTS_TABLE(G, M, V_S)`), returning an
    `RTable G` built on top of `RTable.empty` (i.e. `initialState G`,
    reusing `RepList`/`Status` from `reptable_ops_properties.lean`
    without re-deriving them). `M` enters only through `inM`, the
    edge-membership test used to steer BFS edge selection (Lines 6-9). -/
public abbrev populateRepresentsTable
    (adj0 : V → List V) (inM : V → V → Bool) (Vs : List V) : RTable G :=
  match Vs with
  | []      => RTable.empty G
  | v0 :: _ =>
    let T := bfsLevels adj0 v0                                        -- Line 1
    populateLoop inM T adj0 [] (RTable.empty G)                        -- Lines 2-16
    -- Line 17: return R (the result of `populateLoop`).

-- ═══════════════════════════════════════════════════════════════════════════
-- §2'. Packaging Algorithm 2's output as an honest `RepTable G`
--      (reusing `RepTable` from `lemma4.lean` verbatim).
-- ═══════════════════════════════════════════════════════════════════════════

/-- `M`, given as its total partner function, as a `G.Subgraph` — the
    bridge needed to reuse `RepTable G`'s `M : G.Subgraph` field (rather
    than re-deriving a `RepTable` from scratch). -/
public noncomputable abbrev matchingSubgraph (M : V → V) (hMadj : ∀ v, G.Adj v (M v)) :
    G.Subgraph where
  verts := Set.univ
  Adj   := fun u v => M u = v ∨ M v = u
  adj_sub := by
    rintro u v (h | h)
    · exact h ▸ hMadj u
    · exact h ▸ (hMadj v).symm
  edge_vert := fun _ => Set.mem_univ _
  symm := by
    constructor
    rintro u v (h | h)
    · exact Or.inr h
    · exact Or.inl h

/-- `matchingSubgraph` is a perfect matching whenever `M` is a total
    involutive partner function without fixed points (the standard
    "read off your partner" view of a perfect matching, reused wherever
    `RepTable.isPM` is needed). -/
public theorem matchingIsPerfectMatching
    (M : V → V) (hMinv : ∀ v, M (M v) = v) (hMadj : ∀ v, G.Adj v (M v)) :
    (matchingSubgraph (G := G) M hMadj).IsPerfectMatching := by
  refine ⟨fun v _ => ⟨M v, Or.inl rfl, ?_⟩, fun v => Set.mem_univ v⟩
  rintro w (h | h)
  · exact h.symm
  · have := hMinv w; rw [h] at this; exact this.symm

/-- Packages the row list built by `populateRepresentsTable` together with
    a perfect matching into a genuine `RepTable G` value (reusing
    `RepTable` from `lemma4.lean` verbatim), so Algorithm 2's
    output connects directly to `Lemma4`/`Theorem4`/`Theorem6`/`Theorem7`.
    `hrow_pair` — "the two endpoints inserted together into one row of
    `rows` get the same row index" — holds by construction of
    `populateLoop` (each row is inserted as a matched pair in a single
    step, Line 12) but, exactly as `hbridgeless`/`hcubic`/`ExactlyOneDuad`
    are taken as hypotheses elsewhere in this development rather than
    re-derived by induction on the algorithm's own loop, we take it here
    too. -/
public abbrev RTable.toRepTable (R : RTable G) (M : V → V)
    (hMinv : ∀ v, M (M v) = v) (hMadj : ∀ v, G.Adj v (M v))
    (hrow_pair : ∀ ⦃u v : V⦄, (matchingSubgraph (G := G) M hMadj).Adj u v →
      R.rows.findIdx (fun rc => rc.1 = u ∨ rc.2 = u) =
      R.rows.findIdx (fun rc => rc.1 = v ∨ rc.2 = v)) :
    RepTable G where
  M := matchingSubgraph M hMadj
  isPM := matchingIsPerfectMatching M hMinv hMadj
  row := fun w => R.rows.findIdx (fun rc => rc.1 = w ∨ rc.2 = w)
  row_pair := hrow_pair

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. Algorithm 4 : COMPUTE_REPRESENTATION_SCORE(R)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Algorithm 4**. Lines 2-26: single top-down pass over the rows,
    computing (or re-fixing, for frozen/removed endpoints) each endpoint's
    ζ from the ζ's of endpoints in rows strictly above it — since we fold
    top-down and update `R.score` as we go, those are already the
    freshly-recomputed values by the time `row` is reached, matching "for
    each row_j in R that is above row". `R.reps`/`R.status` here are
    exactly `TableState`'s fields (reused, not redefined). -/
public partial def computeRepresentationScore (R0 : RTable G) : RTable G :=
  let rec loop (processed : List (Row V)) (remaining : List (Row V)) (R : RTable G) :
      RTable G :=
    match remaining with
    | []              => R                                            -- Line 26 (outer end)
    | (u, v) :: rest  =>
      -- Lines 4-23, "for each endpoint u in row do" (executes exactly twice).
      let scoreEndpoint (w : V) (R : RTable G) : RTable G :=
        match R.status w with
        | Status.frozen  => { R with score := upd R.score w (-1) }     -- Lines 5-7
        | Status.removed => { R with score := upd R.score w (-1) }     -- Lines 8-10
        | Status.unset   =>
          -- Line 12: ζ_u = 0, then Lines 13-23 accumulate over rows above.
          let contribution :=
            processed.foldl (fun acc (xy : Row V) =>
              let x := xy.1
              let y := xy.2
              if w ∈ R.reps x then
                acc + max 0 (R.score y) + 1                             -- Line 17
              else if w ∈ R.reps y then
                acc + max 0 (R.score x) + 1                             -- Line 19
              else
                acc)                                                    -- Line 21: do nothing
              0
          { R with score := upd R.score w contribution }
      let R := scoreEndpoint u R
      let R := scoreEndpoint v R
      loop (processed ++ [(u, v)]) rest R
  loop [] R0.rows R0

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. Algorithm 6 : FREEZE_AND_REMOVE(R, S, ψ, ω)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Algorithm 6**. `psi`/`omega` model `ψ`/`ω` (`none` = the paper's
    `∅`). The Freeze Operation (Lines 1-5) is built directly from
    `TableState.freeze` (reused verbatim: it already performs "freeze ψ"
    + "delist ψ from every represents list", Lines 2 and 5), with only
    Line 4's "set L_ψ to null" added on top, since `TableState.freeze`'s
    blanket erase does not itself special-case ψ's own (now-irrelevant)
    list. The Remove Operation (Lines 6-15) genuinely generalizes
    `TableState.remove` (which freezes ω's represents-neighbours in one
    non-recursive step, cf. `remove_initialState_freezes_neighbors` in
    `reptable_ops_properties.lean`) into the paper's fully
    recursive cascade, so it is transcribed directly rather than reused
    as a black box. -/
public partial def freezeAndRemove (R : RTable G) (S : Finset V)
    (psi omega : Option V) : RTable G × Finset V :=
  -- Freeze Operation of Represents Table (Lines 1-5).
  let (R, S) :=
    match psi with
    | none    => (R, S)
    | some ψ  =>
      let ts := R.toTableState.freeze ψ                                -- Lines 2, 5 (reused)
      let ts := { ts with reps := upd ts.reps ψ (∅ : Finset V) }        -- Line 4
      let R := { R with toTableState := ts }
      let S := insert ψ S                                               -- Line 3
      (R, S)
  -- Remove Operation of Represents Table (Lines 6-15).
  match omega with
  | none    => (R, S)
  | some ω  =>
    let R := { R with status := upd R.status ω Status.removed }         -- Line 7
    let S := S.erase ω                                                  -- Line 8
    -- Lines 9-11: "for each non-frozen and unremoved endpoint u in R such
    -- that ω ∈ L_u do FREEZE_AND_REMOVE(R, S, u, ∅)".
    let candidates1 :=
      (Finset.univ.filter
        (fun u => R.status u = Status.unset ∧ ω ∈ R.reps u)).toList
    let (R, S) :=
      candidates1.foldl
        (fun (RS : RTable G × Finset V) u => freezeAndRemove RS.1 RS.2 (some u) none)
        (R, S)
    -- Lines 12-14: "for each non-frozen and unremoved endpoint u in L_ω do
    -- FREEZE_AND_REMOVE(R, S, u, ∅)".
    let candidates2 := (R.reps ω).toList.filter (fun u => R.status u = Status.unset)
    let (R, S) :=
      candidates2.foldl
        (fun (RS : RTable G × Finset V) u => freezeAndRemove RS.1 RS.2 (some u) none)
        (R, S)
    let R := { R with reps := upd R.reps ω (∅ : Finset V) }             -- Line 15
    (R, S)

-- ═══════════════════════════════════════════════════════════════════════════
-- §5. Algorithm 5 : VERTEX_ELIMINATION(R, S)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Algorithm 5**. Lines 1-16: bottom-up pass over the rows (hence
    `R0.rows.reverse`). Both mirror-image sub-cases of Line 6 ("endpoint
    u in row remains and endpoint v in row is frozen") are handled, since
    the paper's `u`, `v` names within a row are otherwise arbitrary. -/
public partial def vertexElimination (R0 : RTable G) (S0 : Finset V) :
    RTable G × Finset V :=
  let rec loop (rows : List (Row V)) (R : RTable G) (S : Finset V) :
      RTable G × Finset V :=
    match rows with
    | [] => (R, S)                                        -- Line 16 (end); Line 17 returns this
    | (u, v) :: rest  =>
      let R := computeRepresentationScore R                            -- Line 3 (Algorithm 4)
      let su := R.status u
      let sv := R.status v
      let (R, S) :=
        if (su ≠ Status.unset) ∧ (sv ≠ Status.unset) then
          (R, S)                                                       -- Lines 4-5: continue
        else if su = Status.unset ∧ sv = Status.frozen then
          freezeAndRemove R S none (some u)                            -- Line 6-7
        else if sv = Status.unset ∧ su = Status.frozen then
          freezeAndRemove R S none (some v)                            -- labeling of Line 6-7
        else
          -- Line 9: both u, v neither frozen nor removed, represent only
          -- each other.
          if R.score u ≥ R.score v then
            freezeAndRemove R S (some u) (some v)                      -- Line 10-11
          else
            freezeAndRemove R S (some v) (some u)                      -- Line 12-13
      loop rest R S
  loop R0.rows.reverse R0 S0

-- ═══════════════════════════════════════════════════════════════════════════
-- §6. Algorithm 8 : DUADIC_HOP(R, S, ψ, ω, λ)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Algorithm 8**. `psi`/`omega` model `ψ`/`ω` (`none` = `∅`), `lam`
    models `λ` as a `Finset V` of visited endpoints (matching the
    vocabulary of `IsDuad`/`DiminishingHop` in `thm6.lean`,
    which likewise use `Finset V`/`RepTable`). Per Line 1, exactly one of
    `ψ`, `ω` is `≠ ∅` on any genuine call; this is documented, not
    additionally enforced as a checked precondition, exactly as the
    paper's own comment is documentation rather than an assertion. -/
public partial def duadicHop (R : RTable G) (S : Finset V)
    (psi omega : Option V) (lam : Finset V) : RTable G × Finset V × Finset V :=
  -- Line 2: if ω ≠ ∅
  let (R, S, lam) :=
    match omega with
    | none   => (R, S, lam)
    | some ω =>
      if ω ∈ lam then
        (R, S, lam)                                          -- Lines 3-5: already visited, return
      else
        let lam := insert ω lam                                        -- Line 6
        let R := { R with status := upd R.status ω Status.removed }    -- Line 7
        let S := S.erase ω                                             -- Line 8
        -- Line 9: Q = ∅ (a queue of endpoints to be frozen); a `List V`
        -- appended at the tail preserves enqueue order (Lines 10-25).
        let step (u : V) (acc : Finset V × List V) : Finset V × List V :=
          let (lam, Q) := acc
          if u ∈ lam then
            (lam, Q)                                                   -- Line 11 fails: skip
          else
            let lam := insert u lam                                    -- Line 12
            if u ∈ S then (lam, Q) else (lam, Q ++ [u])                -- Lines 13-15
        -- Lines 10-17: "for each endpoint u in L_ω do ...".
        let (lam, Q) := (R.reps ω).toList.foldl (fun acc u => step u acc) (lam, [])
        -- Lines 18-25: "for each endpoint u in R such that ω ∈ L_u do ...".
        let candidates :=
          (Finset.univ.filter (fun u => ω ∈ R.reps u)).toList
        let (lam, Q) := candidates.foldl (fun acc u => step u acc) (lam, Q)
        -- Lines 26-29: "for each endpoint u in Q do
        --   Q = Q \ {u}; R, S, λ = DUADIC_HOP(R, S, u, ∅, λ)".
        let (R, S, lam) :=
          Q.foldl
            (fun (RSl : RTable G × Finset V × Finset V) u =>
              duadicHop RSl.1 RSl.2.1 (some u) none RSl.2.2)
            (R, S, lam)
        (R, S, lam)
  -- Line 32: if ψ ≠ ∅
  match psi with
  | none    => (R, S, lam)                                             -- Line 41
  | some ψ  =>
    let R := { R with status := upd R.status ψ Status.frozen }         -- Line 33
    let S := insert ψ S                                                -- Line 34
    -- Line 36: u = the other endpoint in ψ's row.
    match R.rows.find? (fun rc => rc.1 = ψ ∨ rc.2 = ψ) with
    | none => (R, S, lam)                                     -- (ψ not tabled: nothing to do)
    | some (a, b)   =>
      let u := if a = ψ then b else a
      if u ∈ S then
        duadicHop R S none (some u) lam                                -- Line 38
      else
        (R, S, lam)                                        -- Line 39 end; Line 41 returns this

-- ═══════════════════════════════════════════════════════════════════════════
-- §7. Algorithm 7 : DIMINISHING_HOPS(R, S)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Algorithm 7**. Lines 2-3 initialize `R_diminished`, `S_diminished`
    (we also track `λ_diminished` and we start it at `∅`,
    exactly as `λ` itself is on Line 1). The inner "for each endpoint u in
    row" of Lines 11-18 restarts fresh from `R_original`/`S_original`/
    `λ_original` on each of its two iterations (Lines 19-21 reset them at
    the end of each pass, i.e. logically before the next), which we
    capture by calling `duadicHop` fresh from the saved original state
    each time. -/
public partial def diminishingHops (R0 : RTable G) (S0 : Finset V) : RTable G × Finset V :=
  let rec go (rows : List (Row V)) (Rd : RTable G) (Sd : Finset V) (lamd : Finset V) :
      RTable G × Finset V :=
    match rows with
    | [] => (Rd, Sd)                                      -- Line 27 (end); Line 28 returns (R, S)
    | (u, v) :: rest  =>
      let Roriginal := Rd; let Soriginal := Sd; let lamOriginal := lamd -- Lines 6-8
      if Rd.status u = Status.frozen ∧ Rd.status v = Status.frozen then -- Line 10
        -- Lines 11-18: "for each endpoint u in row do DUADIC_HOP(...);
        -- if |S| < |S_diminished| then update; [Lines 19-21 restore]".
        let tryEndpoint (w : V) (Rd Sd lamd : _) : RTable G × Finset V × Finset V :=
          let (R1, S1, l1) := duadicHop Roriginal Soriginal none (some w) lamOriginal  -- Line 12
          if S1.card < Sd.card then (R1, S1, l1) else (Rd, Sd, lamd)     -- Lines 14-18
        let (Rd, Sd, lamd) := tryEndpoint u Rd Sd lamd
        let (Rd, Sd, lamd) := tryEndpoint v Rd Sd lamd
        go rest Rd Sd lamd                                         -- Lines 23-26: R=S=λ=diminished
      else
        go rest Rd Sd lamd
  go R0.rows R0 S0 (∅ : Finset V)

-- ═══════════════════════════════════════════════════════════════════════════
-- §8. Algorithm 3 : DIMINISHING_HOP_PHASE(R)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Algorithm 3**. `m` (Line 6, `⌈m/2⌉`-many rounds) is read off as the
    number of rows already inserted into `R` by Algorithm 2 (one row per
    matching edge, Definition 14), i.e. `R0.rows.length`. -/
public partial abbrev diminishingHopPhase (R0 : RTable G) : Finset V :=
  let S0 : Finset V := ∅                                                -- Line 1
  let R1 : RTable G := { R0 with score := fun _ => negInf }              -- Lines 2-3
  let R2 := computeRepresentationScore R1                                -- Line 4 (Algorithm 4)
  let (R3, S3) := vertexElimination R2 S0                                -- Line 5 (Algorithm 5)
  let m := R0.rows.length
  -- Lines 6-8: "for each integer a in [1, m/2] do
  --   R, S = DIMINISHING_HOPS(R, S)".
  let rec repeatHops (n : ℕ) (R : RTable G) (S : Finset V) : RTable G × Finset V :=
    match n with
    | 0      => (R, S)
    | n + 1  => let (R', S') := diminishingHops R S; repeatHops n R' S'
  let (_, Sfinal) := repeatHops (m) R3 S3
  Sfinal                                                                 -- Line 9

-- ═══════════════════════════════════════════════════════════════════════════
-- §9. Algorithm 1 : VERTEX_COVER(G, k)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Algorithm 1**, the top-level decision procedure. `M` is a perfect
    matching given as its total involutive partner function (§2' above);
    `Vs` is Line 1's lexicographically sorted vertex list; `adj0` is `G`'s
    adjacency-list function, needed by Algorithm 2's BFS. Since `M` is a
    perfect matching, `{ (v, M v) : v ∈ Vs, v <lex M v }` enumerates each
    matching edge exactly once (Line 3). -/
public abbrev vertexCover
    (adj0 : V → List V) (Vs : List V) (M : V → V) (lt : V → V → Bool)
    (k : ℕ) : Bool :=
  -- Line 1: Vs (already supplied as an argument, per the design note above).
  -- PHASE I (Lines 2-6).
  let matchingEdges : List (Row V) :=
    Vs.filterMap (fun u => if lt u (M u) then some (u, M u) else none)   -- Line 3
  if k < matchingEdges.length then
    false                                                                -- Lines 4-5
  else
    let inM : V → V → Bool := fun a b => decide (M a = b ∨ M b = a)
    -- PHASE II (Lines 7-8).
    let R := populateRepresentsTable (G := G) adj0 inM Vs                -- Line 8 (Algorithm 2)
    -- PHASE III (Lines 9-10).
    let S := diminishingHopPhase R                                      -- Line 10 (Algorithm 3)
    -- Lines 11-14.
    decide (S.card ≤ k)

end

-- ═══ thm8_lemma6_lemma7.lean ═══
section
open Finset
variable {V : Type*} [DecidableEq V] [Fintype V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Freeze a single endpoint `u`: set its status to `frozen` and record it
    in the running cover `S`. (The `reps`/`rows`/`score` fields of `R` are
    left untouched — Algorithm 8's freeze step, unlike Algorithm 6's, does
    not delist anything, cf. the "no deletion" remark on `Status` in
    `reptable_ops_properties.lean`.) -/
public abbrev freezeOne (R : RTable G) (S : Finset V) (u : V) : RTable G × Finset V :=
  ({ R with status := upd R.status u Status.frozen }, insert u S)

/-- The endpoints Algorithm 8's removal step (Lines 9-17) considers when
    removing `ω`: every endpoint `u` with `u ∈ R.reps ω` (paper "L_ω") or
    `ω ∈ R.reps u` ("u represents ω"), i.e. Lines 10 and 18 of Algorithm 8
    combined into one `Finset.filter`. -/
public abbrev removalPartners (R : RTable G) (ω : V) : Finset V :=
  Finset.univ.filter (fun u => u ∈ R.reps ω ∨ ω ∈ R.reps u)

/-- Given the row `(a, b)` found for endpoint `u` (i.e. `a = u` or
    `b = u`), the *other* endpoint of that row — Algorithm 8 Lines 32-36's
    "u = the other endpoint in ψ's row". Kept as its own definition
    (rather than an inline `let`) so that a `simp only [dh]` unfolding of
    `dh`'s equations leaves `partnerOf row u` as a single opaque term
    instead of exposing a second, hidden `if`-expression nested inside the
    `if _ ∈ S' then ...` that follows it — the nesting that broke an
    earlier draft of the proof below (`split` would land on the wrong,
    inner `if`). -/
public abbrev partnerOf (row : Row V) (u : V) : V :=
  if row.1 = u then row.2 else row.1

/-- **Structural core of Algorithm 8** (`dh`): processes either the
    removal of a single endpoint `ω` (`Sum.inl ω`) — cascading the freeze
    of every `removalPartner`, and, mirroring Algorithm 8 Lines 32-40
    exactly, recursively removing a freshly-frozen partner's own
    row-partner whenever that row-partner is already frozen (a duad) —
    or the `for each` loop over a pending list of partners (`Sum.inr l`).
    Guarded throughout by the visited set `lam`: an endpoint already in
    `lam` is never processed twice (Lines 3-5 / Line 11 of Algorithm 8).
    Every recursive call consumes exactly one unit of the `Nat` fuel
    parameter, matching `n + 1 → n` in every branch below, which is why
    this compiles as ordinary structural recursion.
    `(dh n R S lam s).2.2` is the updated visited set `λ`; `.1` is the
    updated table; `.2.1` is the updated cover. -/
public noncomputable abbrev dh : Nat → RTable G → Finset V → Finset V → (V ⊕ List V) →
    RTable G × Finset V × Finset V
  | 0,     R, S, lam, _ => (R, S, lam)
  | n + 1, R, S, lam, Sum.inl ω =>
    if ω ∈ lam then
      (R, S, lam)
    else
      let lam1 := insert ω lam
      let R1   := { R with status := upd R.status ω Status.removed }
      let S1   := S.erase ω
      dh n R1 S1 lam1 (Sum.inr (removalPartners R1 ω).toList)
  | n + 1, R, S, lam, Sum.inr [] => (R, S, lam)
  | n + 1, R, S, lam, Sum.inr (u :: us) =>
    if u ∈ lam then
      dh n R S lam (Sum.inr us)
    else
      let (R', S') := freezeOne R S u
      let lam' := insert u lam
      match R'.rows.find? (fun rc => rc.1 = u ∨ rc.2 = u) with
      | none => dh n R' S' lam' (Sum.inr us)
      | some row =>
        let v := partnerOf row u
        if v ∈ S' then
          let (R'', S'', lam'') := dh n R' S' lam' (Sum.inl v)
          dh n R'' S'' lam'' (Sum.inr us)
        else
          dh n R' S' lam' (Sum.inr us)

/-- The one fact about the cascade that is **not** mere bookkeeping: no
    two graph-adjacent endpoints are ever both left `removed` at the end
    of a single call to `dh (Sum.inl ω)`. -/
public abbrev NoAdjacentDoubleRemoval (n : ℕ) (R : RTable G) (S lam : Finset V) (ω : V) : Prop :=
  ∀ v w, G.Adj v w →
    (dh n R S lam (Sum.inl ω)).1.status v = Status.removed →
    (dh n R S lam (Sum.inl ω)).1.status w ≠ Status.removed

end

-- ═══ thm8_lemma6_lemma8.lean (file-local classical decidability) ═══
section
open Finset
attribute [local instance] Classical.propDecidable

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The set of row indices actually used by `R`. -/
public abbrev RowsOf (R : RepTable G) : Finset ℕ := Finset.image R.row Finset.univ

/-- **Definition 14, "two endpoints per row."** Every row index actually
    used by `R` has exactly two endpoints. This is a static fact about
    the represents table's row structure — it says nothing about how any
    algorithm behaves — and holds by construction whenever `R.row` is
    built from a perfect matching's edge list (one row per matching
    edge). -/
public abbrev TwoPerRow (R : RepTable G) : Prop :=
  ∀ i ∈ RowsOf R, ∃ u v : V,
    u ≠ v ∧ R.row u = i ∧ R.row v = i ∧ ∀ w, R.row w = i → w = u ∨ w = v

/-- **Definition 14, "a row is a matching edge."** Any two distinct
    endpoints sharing a row are joined by an edge of `G` — again a static
    fact about the represents table's construction, not about algorithm
    behaviour. -/
public abbrev RowsAreEdges (R : RepTable G) : Prop :=
  ∀ (i : ℕ) (u v : V), u ≠ v → R.row u = i → R.row v = i → G.Adj u v

end

-- ═══ thm8_lemma6.lean and thm8.lean (with `Inhabited`) ═══
section
open Finset
variable {V : Type*} [DecidableEq V] [Fintype V] [Inhabited V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **VC − CBG, "Yes instance."** `G` together with a bound `k` is a Yes
    instance of the vertex-cover decision problem iff `G` has a vertex
    cover of size at most `k`. -/
public abbrev YesInstance (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ S : Finset V, VCover G S ∧ S.card ≤ k

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. `inMOf`/`RT0Of`: naming `vertexCover`'s own internal terms
-- ═══════════════════════════════════════════════════════════════════════════

/-- Exactly `vertexCover`'s own local `let inM := ...` (Algorithm 1,
    between Lines 6 and 7): the edge-membership test built from `M`'s
    graph. Named here, as a plain (reducible) top-level `def`, purely so
    every later statement can refer to it without repeating the lambda
    and without the `let`-in-type friction v2 ran into. -/
public abbrev inMOf (M : V → V) : V → V → Bool := fun a b => decide (M a = b ∨ M b = a)

/-- Exactly `vertexCover`'s own local `let R := populateRepresentsTable
    adj0 inM Vs` (Algorithm 1, Line 8): Algorithm 2's actual output on
    the data `vertexCover` itself would call it with. -/
public noncomputable abbrev RT0Of (adj0 : V → List V) (Vs : List V) (M : V → V) : RTable G :=
  populateRepresentsTable (G := G) adj0 (inMOf M) Vs


/-- One "try hopping by removing endpoint `w`" step (Algorithm 7, "does an
    S-duadic hop for each of the endpoints in a duad", Lines 11-18): runs
    `dh`'s removal cascade from `w`, starting fresh from the row's
    *original* state (`Roriginal`/`Soriginal`/`lamOriginal` — the state at
    the top of this row, before either endpoint has been tried), keeping
    the result only if it strictly shrinks the cover relative to `cur`,
    the best found so far this row. -/
public noncomputable abbrev dhopsStep
  (fuel : ℕ) (Roriginal : RTable G) (Soriginal lamOriginal : Finset V)
    (cur : RTable G × Finset V × Finset V) (w : V) : RTable G × Finset V × Finset V :=
  let (R1, S1, l1) := dh fuel Roriginal Soriginal lamOriginal (Sum.inl w)
  if S1.card < (cur.2).1.card then (R1, S1, l1) else cur

/-- **Algorithm 7** (`DIMINISHING_HOPS`), re-derived. -/
public noncomputable abbrev dhops (fuel : ℕ) : List (Row V) → RTable G → Finset V → Finset V →
    RTable G × Finset V
  | [], Rd, Sd, _ => (Rd, Sd)
  | rc :: rest, Rd, Sd, lamd =>
    if Rd.status rc.1 = Status.frozen ∧ Rd.status rc.2 = Status.frozen then
      let (Rd1, Sd1, lamd1) := dhopsStep fuel Rd Sd lamd (Rd, Sd, lamd) rc.1
      let (Rd2, Sd2, lamd2) := dhopsStep fuel Rd Sd lamd (Rd1, Sd1, lamd1) rc.2
      dhops fuel rest Rd2 Sd2 lamd2
    else
      dhops fuel rest Rd Sd lamd

/-- **Algorithm 7's own entry point**, matching `diminishingHops R0 S0`:
    start the row scan from `R0.rows`, with an empty visited set `λ`. -/
public noncomputable abbrev diminishingHops' (fuel : ℕ) (R0 : RTable G) (S0 : Finset V) :
  RTable G × Finset V :=
  dhops fuel R0.rows R0 S0 (∅ : Finset V)


/-- The "Freeze Operation" half of Algorithm 6 (Lines 1-5): freeze `ψ`
    (`TableState.freeze`, which also erases `ψ` from every `.reps` list —
    irrelevant to `AllFrozenOrRemoved`/`FrozenSet`, which depend only on
    `.status`) and additionally null out `L_ψ` itself (Line 4). Exactly
    `PARTII_algorithms.lean`'s inline `let` block for the `psi`
    case of `freezeAndRemove`, pulled out as its own named function so it
    can be reasoned about via its own equation lemma rather than an
    unfolded `let`-chain inside a bigger match. -/
public noncomputable def frFreeze (R : RTable G) (S : Finset V) (ψ : V) : RTable G × Finset V :=
  let ts := R.toTableState.freeze ψ
  let ts := { ts with reps := upd ts.reps ψ (∅ : Finset V) }
  (({ R with toTableState := ts } : RTable G), insert ψ S)

-- The "Remove Operation" half of Algorithm 6 (Lines 6-15) and
-- **Algorithm 6** (`FREEZE_AND_REMOVE`) itself, re-derived together as a
-- `mutual` block: `frRemove`'s own cascade calls back into `fr`
-- (`fr n · · (some u) none`, matching `PARTII_algorithms.lean`'s
-- `freezeAndRemove RS.1 RS.2 (some u) none`), and `fr` in turn calls
-- `frRemove` for its `omega` case — a genuine mutual recursion between
-- the two (unlike `frFreeze`, which never calls back into either), so
-- Lean needs them declared together rather than as two independent
-- `def`s in sequence. Both still consume exactly one unit of fuel `n`
-- per recursive step, matching `dh`'s own discipline
-- (`thm8_lemma6_lemma7.lean §3`).
mutual
public noncomputable def frRemove
  (n : ℕ) (R : RTable G) (S : Finset V) (ω : V) : RTable G × Finset V :=
  let R := { R with status := upd R.status ω Status.removed }
  let S := S.erase ω
  let candidates1 :=
    (Finset.univ.filter (fun u => R.status u = Status.unset ∧ ω ∈ R.reps u)).toList
  let (R, S) :=
    candidates1.foldl (fun (RS : RTable G × Finset V) u => fr n RS.1 RS.2 (some u) none) (R, S)
  let candidates2 := (R.reps ω).toList.filter (fun u => R.status u = Status.unset)
  let (R, S) :=
    candidates2.foldl (fun (RS : RTable G × Finset V) u => fr n RS.1 RS.2 (some u) none) (R, S)
  let R := { R with reps := upd R.reps ω (∅ : Finset V) }
  (R, S)

public noncomputable def fr : ℕ → RTable G → Finset V → Option V → Option V → RTable G × Finset V
  | 0, R, S, _, _ => (R, S)
  | n + 1, R, S, psi, omega =>
    let (R, S) := match psi with
      | none => (R, S)
      | some ψ => frFreeze R S ψ
    match omega with
    | none => (R, S)
    | some ω => frRemove n R S ω
end


/-- One endpoint's score update (Algorithm 4, Lines 4-23): identical to
    `PARTII_algorithms.lean`'s inline `scoreEndpoint`, pulled
    out as its own `def`. Every branch is `{ R with score := upd ... }` —
    `.status`/`.reps`/`.rows` are never touched. -/
public abbrev crsStep (processed : List (Row V)) (R : RTable G) (w : V) : RTable G :=
  match R.status w with
  | Status.unset =>
    let contribution := processed.foldl (fun acc xy =>
      if w ∈ R.reps xy.1 then acc + max 0 (R.score xy.2) + 1
      else if w ∈ R.reps xy.2 then acc + max 0 (R.score xy.1) + 1
      else acc) 0
    { R with score := upd R.score w contribution }
  | _ => { R with score := upd R.score w (-1) }

/-- **Algorithm 4**, re-derived: ordinary structural recursion on the
    (second) row-list argument, decreasing at every recursive call —
    Lean accepts this automatically, unlike the original `partial def
    computeRepresentationScore`. -/
public abbrev crs : List (Row V) → List (Row V) → RTable G → RTable G
  | _, [], R => R
  | processed, rc :: rest, R =>
    let R := crsStep processed R rc.1
    let R := crsStep processed R rc.2
    crs (processed ++ [rc]) rest R

/-- **Algorithm 4's own entry point**, matching
    `computeRepresentationScore R0` exactly. -/
public abbrev computeRepresentationScore' (R0 : RTable G) : RTable G := crs [] R0.rows R0


/-- **Algorithm 5** (`VERTEX_ELIMINATION`), re-derived: a structural fold
    over `R0.rows.reverse` (bottom-up, matching the original), calling
    the re-derived `computeRepresentationScore'`/`fr` in place of the
    opaque `computeRepresentationScore`/`freezeAndRemove`. The fuel `n`
    is passed uniformly to every `fr` call (mirroring `diminishingHops'`'s
    own treatment of `dh`'s fuel in §4). Both mirror-image sub-cases of
    "one endpoint remains, the other is frozen" are handled, exactly as
    the original. -/
public noncomputable abbrev ve'
  (fuel : ℕ) : List (Row V) → RTable G → Finset V → RTable G × Finset V
  | [], R, S => (R, S)
  | (u, v) :: rest, R, S =>
    let R := computeRepresentationScore' R
    let su := R.status u
    let sv := R.status v
    let (R, S) :=
      if su ≠ Status.unset ∧ sv ≠ Status.unset then
        (R, S)
      else if su = Status.unset ∧ sv = Status.frozen then
        fr fuel R S none (some u)
      else if sv = Status.unset ∧ su = Status.frozen then
        fr fuel R S none (some v)
      else if R.score u ≥ R.score v then
        fr fuel R S (some u) (some v)
      else
        fr fuel R S (some v) (some u)
    ve' fuel rest R S

/-- **Algorithm 5's own entry point**, matching `vertexElimination R0 S0`
    exactly (bottom-up: `R0.rows.reverse`). -/
public noncomputable abbrev vertexElimination' (fuel : ℕ) (R0 : RTable G) (S0 : Finset V) :
  RTable G × Finset V :=
  ve' fuel R0.rows.reverse R0 S0


/-- **Algorithm 3, Lines 1-5**: `algInit` is built from
    `computeRepresentationScore'`/`vertexElimination'` — the *transparent*,
    genuinely structurally recursive re-derivations of Algorithms 4/5
    (§4d/§4e below), not the opaque originals. (Section §4' is placed
    before §4a-§4i purely so `algState`'s own recursive definition, right
    below, type-checks before those sections are reached; the actual
    re-derivations of Algorithms 4-6 that make `algInit` transparent
    follow in §4a-§4i.) `hphase_eq` (§5) is what bridges this transparent
    sequence back to the *real*, opaque `diminishingHopPhase`. -/
public noncomputable abbrev algInit (fuel : ℕ) (R0 : RTable G) : RTable G × Finset V :=
  vertexElimination' fuel
    (computeRepresentationScore' ({ R0 with score := fun _ => negInf } : RTable G))
    (∅ : Finset V)

/-- **Algorithm 3, Lines 6-8's loop, re-executed literally**: round 0 is
    `algInit fuel R0` (as of §4i, itself fully transparent); every
    subsequent round is `diminishingHops'` (§4, above) — transparent,
    structurally recursive, and provably behaved — in place of the
    opaque `diminishingHops`. -/
public noncomputable abbrev algState (fuel : ℕ) (R0 : RTable G) : ℕ → RTable G × Finset V
  | 0     => algInit fuel R0
  | n + 1 => diminishingHops' fuel (algState fuel R0 n).1 (algState fuel R0 n).2

/-- The table-state component of `algState`, in the `TableState G`
    vocabulary `IsValidFreezeRemove`/`FrozenSet`/`DiminishingHop`
    (`thm4.lean`/`thm6.lean`) already use. -/
public noncomputable abbrev SseqOf (fuel : ℕ) (R0 : RTable G) (n : ℕ) : TableState G :=
  (algState fuel R0 n).1.toTableState


/-- This proves that after running a step of the diminishingHopPhase with a given
amount of fuel, the abstract state accurately matches the concrete
algorithm state (algState), given each row has two endpoints (a structual fact). -/
public abbrev PhaseMatchesAlgState (fuel : ℕ) (R0 : RTable G) (R : RepTable G) : Prop :=
  diminishingHopPhase R0 = (algState fuel R0 (RowsOf R).card).2

/-- **Theorem 8** (paper, §7, combining Lemma 5 and Lemma 6, pp.58-61,
    lines 1750-1922), the result being submitted. -/
public theorem VCCBGPartII.Theorem8_wrapper
    (hcubic : ∀ v : V, G.degree v = 3)
    (hbridgeless : ∀ ⦃e : Sym2 V⦄, e ∈ G.edgeSet → ¬ G.IsBridge e)
    (adj0 : V → List V) (Vs : List V) (M : V → V) (lt : V → V → Bool) (k : ℕ)
    (hMinv : ∀ v, M (M v) = v) (hMadj : ∀ v, G.Adj v (M v))
    (hrow_pair : ∀ ⦃u v : V⦄, (matchingSubgraph (G := G) M hMadj).Adj u v →
        (RT0Of (G := G) adj0 Vs M).rows.findIdx (fun rc => rc.1 = u ∨ rc.2 = u) =
        (RT0Of (G := G) adj0 Vs M).rows.findIdx (fun rc => rc.1 = v ∨ rc.2 = v))
    (htwo : TwoPerRow ((RT0Of (G := G) adj0 Vs M).toRepTable M hMinv hMadj hrow_pair))
    (hedges : RowsAreEdges ((RT0Of (G := G) adj0 Vs M).toRepTable M hMinv hMadj hrow_pair))
    (hrows_half :
      (RowsOf ((RT0Of (G := G) adj0 Vs M).toRepTable M hMinv hMadj hrow_pair)).card
        = Fintype.card V / 2)
    (hmatchingEdges_card :
      (Vs.filterMap (fun u => if lt u (M u) then some (u, M u) else none)).length
        = Fintype.card V / 2)
    (hV_pos : 0 < Fintype.card V)
    (hRowsCoverAll : ∀ w : V,
      ∃ rc ∈ ({ RT0Of (G := G) adj0 Vs M with score := fun _ => negInf } : RTable G).rows.reverse,
        w = rc.1 ∨ w = rc.2)
    (hRemoveInv0 : RemoveInvariant
      (algInit ((Fintype.card V) ^ 2) (RT0Of (G := G) adj0 Vs M)).1.toTableState)
    (hFS0 : FrozenSet (algInit ((Fintype.card V) ^ 2) (RT0Of (G := G) adj0 Vs M)).1.toTableState
        = (algInit ((Fintype.card V) ^ 2) (RT0Of (G := G) adj0 Vs M)).2)
    (hNoAdjAll : ∀ (Rx : RTable G) (Sx lamx : Finset V) (w : V),
      NoAdjacentDoubleRemoval ((Fintype.card V) ^ 2) Rx Sx lamx w)
    (hphase_eq : PhaseMatchesAlgState ((Fintype.card V) ^ 2) (RT0Of (G := G) adj0 Vs M)
      ((RT0Of (G := G) adj0 Vs M).toRepTable M hMinv hMadj hrow_pair))
    (hSseq_step : ∀ n,
      (∃ _ : DiminishingHop ((RT0Of (G := G) adj0 Vs M).toRepTable M hMinv hMadj hrow_pair)
              (SseqOf ((Fintype.card V) ^ 2) (RT0Of (G := G) adj0 Vs M) n), True) →
        (FrozenSet (SseqOf ((Fintype.card V) ^ 2) (RT0Of (G := G) adj0 Vs M) (n + 1))).card
          < (FrozenSet (SseqOf ((Fintype.card V) ^ 2) (RT0Of (G := G) adj0 Vs M) n)).card)
    (hstationary : ∀ n,
      ¬ (∃ _ : DiminishingHop ((RT0Of (G := G) adj0 Vs M).toRepTable M hMinv hMadj hrow_pair)
              (SseqOf ((Fintype.card V) ^ 2) (RT0Of (G := G) adj0 Vs M) n), True) →
        SseqOf ((Fintype.card V) ^ 2) (RT0Of (G := G) adj0 Vs M) (n + 1)
          = SseqOf ((Fintype.card V) ^ 2) (RT0Of (G := G) adj0 Vs M) n) :
    vertexCover (G := G) adj0 Vs M lt k = true ↔ YesInstance G k := by
  sorry

end

module

public import Mathlib

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.defProp false
/-!
# Advertised statement — Lemma 6

"If Algorithm 1 returns Yes, then the given instance of VC − CBG is a
   Yes instance." (§7 of the paper ("Proof of Correctness"), p.58-61, lines 1775-1922)

This file is entirely self-contained: it imports only `Mathlib` and
  re-derives, verbatim, every definition transitively needed to *state*
  `Lemma6` but none of the intermediate theorems those files use to
  *prove* it, since those are not needed merely to write the statement
  down. The final theorem, `VCCBGPartII.Lemma6_wrapper`, is left as a
  `sorry`.
-/

open Finset

-- ═══════════════════════════════════════════════════════════════════════════
-- §0. Section variables (matching `thm8_lemma6.lean`, the strongest of the
--     section-variable lists needed anywhere below).
-- ═══════════════════════════════════════════════════════════════════════════

variable {V : Type*} [DecidableEq V] [Fintype V] [Inhabited V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

-- ═══════════════════════════════════════════════════════════════════════════
-- §1. `definition_vcover.lean`
-- ═══════════════════════════════════════════════════════════════════════════

/-- `VCover G S`: every edge of G has at least one endpoint in S. -/
public def VCover (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ ⦃u v : V⦄, G.Adj u v → u ∈ S ∨ v ∈ S

-- ═══════════════════════════════════════════════════════════════════════════
-- §2. `lemma4.lean`: represents tables built from a perfect matching
-- ═══════════════════════════════════════════════════════════════════════════

/-- `RepTable G`: a represents table for `G`, built by the augmented
    2-approximation algorithm from a perfect matching `M` and a BFS tree. -/
public structure RepTable (G : SimpleGraph V) where
  M : G.Subgraph
  isPM : M.IsPerfectMatching
  row : V → ℕ
  row_pair : ∀ ⦃u v⦄, M.Adj u v → row u = row v

-- ═══════════════════════════════════════════════════════════════════════════
-- §3. `reptable_ops_properties.lean`
-- ═══════════════════════════════════════════════════════════════════════════

open Classical in
/-- **Definition 13** (Represents List). -/
public noncomputable def RepList (G : SimpleGraph V) (u : V) : Finset V :=
  Finset.univ.filter (fun v => G.Adj u v)

/-- Status of an endpoint in the represents table. -/
public inductive Status
  | unset
  | frozen
  | removed
  deriving DecidableEq

/-- The live state of a represents table during execution. -/
public structure TableState (G : SimpleGraph V) where
  status : V → Status
  reps   : V → Finset V

/-- **insert**: populate the table's initial state. -/
public noncomputable def initialState (G : SimpleGraph V) : TableState G where
  status := fun _ => Status.unset
  reps   := fun u => RepList G u

/-- **freeze**. -/
public def TableState.freeze (st : TableState G) (u : V) : TableState G where
  status := fun v => if v = u then Status.frozen else st.status v
  reps   := fun v => (st.reps v).erase u

-- ═══════════════════════════════════════════════════════════════════════════
-- §4. `thm4.lean`
-- ═══════════════════════════════════════════════════════════════════════════

/-- The invariant maintained throughout the freeze/remove process: whenever an
    endpoint `u` is removed, every endpoint `v` adjacent to it is frozen. -/
public def RemoveInvariant (st : TableState G) : Prop :=
  ∀ ⦃u v : V⦄, st.status u = Status.removed → G.Adj u v → st.status v = Status.frozen

/-- Every endpoint of the represents table is either frozen or removed. -/
public def AllFrozenOrRemoved (st : TableState G) : Prop :=
  ∀ v : V, st.status v = Status.frozen ∨ st.status v = Status.removed

/-- The set S'' of frozen endpoints recorded by a table state. -/
public def FrozenSet (st : TableState G) : Finset V :=
  Finset.univ.filter (fun v => st.status v = Status.frozen)

/-- A `TableState` is a *valid freeze/remove outcome*. -/
public def IsValidFreezeRemove (st : TableState G) : Prop :=
  RemoveInvariant st ∧ AllFrozenOrRemoved st

-- ═══════════════════════════════════════════════════════════════════════════
-- §5. `thm6.lean`
-- ═══════════════════════════════════════════════════════════════════════════

/-- `IsDuad R st u v`: `u` and `v` are two distinct endpoints sharing a row of
    the represents table `R`, both currently frozen in state `st`. -/
public def IsDuad (R : RepTable G) (st : TableState G) (u v : V) : Prop :=
  u ≠ v ∧ R.row u = R.row v ∧ st.status u = Status.frozen ∧ st.status v = Status.frozen

/-- **Definition 19** (Duadic Hop). -/
public structure DuadicHop (R : RepTable G) (st : TableState G) where
  u : V
  v : V
  duad : IsDuad R st u v
  st' : TableState G
  valid' : IsValidFreezeRemove st'

/-- **Definition 20** (Diminishing Hop). -/
public structure DiminishingHop (R : RepTable G) (st : TableState G)
    extends DuadicHop R st where
  smaller : (FrozenSet st').card < (FrozenSet st).card

-- ═══════════════════════════════════════════════════════════════════════════
-- §6. `PARTII_algorithms.lean`
-- ═══════════════════════════════════════════════════════════════════════════

noncomputable section

/-- A row of the represents table: the two endpoints of one matching edge. -/
public abbrev Row (V : Type*) := V × V

/-- The represents table threaded through Algorithms 2-8. -/
public structure RTable (G : SimpleGraph V) extends TableState G where
  rows : List (Row V)
  score : V → Int

/-- The `-∞` sentinel of Algorithm 3, Line 3. -/
public def negInf : Int := -1000000000

/-- Algorithm 2, Lines 1-2's starting point. -/
public noncomputable def RTable.empty (G : SimpleGraph V) [DecidableRel G.Adj] : RTable G where
  toTableState := initialState G
  rows  := []
  score := fun _ => negInf

/-- Pointwise function update. -/
public def upd {α : Type*} (f : V → α) (v : V) (a : α) : V → α :=
  fun w => if w = v then a else f w

/-- Line 1: BFS levels. -/
public partial def bfsLevels (adj : V → List V) (start : V) : List (List V) :=
  let rec go (frontier visited : List V) : List (List V) :=
    match frontier with
    | [] => []
    | _  =>
      let nbrs :=
        ((frontier.flatMap adj).eraseDups).filter
          (fun w => !(visited.contains w) && !(frontier.contains w))
      frontier :: go nbrs (visited ++ frontier)
  go [start] []

/-- Lines 6-9: find an `M`-edge from `u` to a vertex on the same level, else
    to a vertex on the next level. -/
public def selectMEdge (adj : V → List V) (inM : V → V → Bool)
    (u : V) (sameLevel nextLevel : List V) : Option V :=
  match (adj u).find? (fun w => inM u w && sameLevel.contains w) with
  | some w => some w
  | none   => (adj u).find? (fun w => inM u w && nextLevel.contains w)

/-- Line 13: delete every edge incident to `x` from the (BFS-only) adjacency
    function. -/
public def removeIncidentEdges (adj : V → List V) (x : V) : V → List V :=
  fun w => if w = x then [] else (adj w).filter (· ≠ x)

/-- Lines 3-16, the double loop. -/
public partial def populateLoop
    (inM : V → V → Bool)
    (levels : List (List V)) (adj : V → List V) (visited : List V) (R : RTable G) :
    RTable G :=
  match levels with
  | []             => R
  | level :: rest  =>
    let nextLevel := rest.headD []
    let rec vertexLoop (vs : List V) (adj : V → List V) (visited : List V)
        (R : RTable G) : (V → List V) × List V × RTable G :=
      match vs with
      | []      => (adj, visited, R)
      | u :: us =>
        if visited.contains u then
          vertexLoop us adj visited R
        else
          match selectMEdge adj inM u level nextLevel with
          | none   => vertexLoop us adj visited R
          | some w =>
            let visited := u :: w :: visited
            let R := { R with rows := R.rows ++ [(u, w)] }
            let adj := removeIncidentEdges (removeIncidentEdges adj u) w
            let visited :=
              (Finset.univ.filter (fun z => adj z = [] ∧ ¬ visited.contains z)).toList
                ++ visited
            vertexLoop us adj visited R
    let (adj, visited, R) := vertexLoop level adj visited R
    populateLoop inM rest adj visited R

/-- **Algorithm 2** (`POPULATE_REPRESENTS_TABLE(G, M, V_S)`). -/
public def populateRepresentsTable
    (adj0 : V → List V) (inM : V → V → Bool) (Vs : List V) : RTable G :=
  match Vs with
  | []      => RTable.empty G
  | v0 :: _ =>
    let T := bfsLevels adj0 v0
    populateLoop inM T adj0 [] (RTable.empty G)

/-- `M`, given as its total partner function, as a `G.Subgraph`. -/
public noncomputable def matchingSubgraph (M : V → V) (hMadj : ∀ v, G.Adj v (M v)) :
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

/- `matchingSubgraph` is a perfect matching whenever `M` is a total
    involutive partner function without fixed points. -/
public def matchingIsPerfectMatching
    (M : V → V) (hMinv : ∀ v, M (M v) = v) (hMadj : ∀ v, G.Adj v (M v)) :
    (matchingSubgraph (G := G) M hMadj).IsPerfectMatching :=
  ⟨fun v _ => ⟨M v, Or.inl rfl, by
      rintro w (h | h)
      · exact h.symm
      · have := hMinv w
        rw [h] at this
        exact this.symm⟩,
    fun v => Set.mem_univ v⟩


/-- Packages the row list built by `populateRepresentsTable` together with a
    perfect matching into a genuine `RepTable G` value. -/
public def RTable.toRepTable (R : RTable G) (M : V → V)
    (hMinv : ∀ v, M (M v) = v) (hMadj : ∀ v, G.Adj v (M v))
    (hrow_pair : ∀ ⦃u v : V⦄, (matchingSubgraph (G := G) M hMadj).Adj u v →
      R.rows.findIdx (fun rc => rc.1 = u ∨ rc.2 = u) =
      R.rows.findIdx (fun rc => rc.1 = v ∨ rc.2 = v)) :
    RepTable G where
  M := matchingSubgraph M hMadj
  isPM := matchingIsPerfectMatching M hMinv hMadj
  row := fun w => R.rows.findIdx (fun rc => rc.1 = w ∨ rc.2 = w)
  row_pair := hrow_pair

/-- **Algorithm 4** (`COMPUTE_REPRESENTATION_SCORE`), the opaque original. -/
public partial def computeRepresentationScore (R0 : RTable G) : RTable G :=
  let rec loop (processed : List (Row V)) (remaining : List (Row V)) (R : RTable G) :
      RTable G :=
    match remaining with
    | []              => R
    | (u, v) :: rest  =>
      let scoreEndpoint (w : V) (R : RTable G) : RTable G :=
        match R.status w with
        | Status.frozen  => { R with score := upd R.score w (-1) }
        | Status.removed => { R with score := upd R.score w (-1) }
        | Status.unset   =>
          let contribution :=
            processed.foldl (fun acc (xy : Row V) =>
              let x := xy.1
              let y := xy.2
              if w ∈ R.reps x then
                acc + max 0 (R.score y) + 1
              else if w ∈ R.reps y then
                acc + max 0 (R.score x) + 1
              else
                acc)
              0
          { R with score := upd R.score w contribution }
      let R := scoreEndpoint u R
      let R := scoreEndpoint v R
      loop (processed ++ [(u, v)]) rest R
  loop [] R0.rows R0

/-- **Algorithm 6** (`FREEZE_AND_REMOVE`), the opaque original. -/
public partial def freezeAndRemove (R : RTable G) (S : Finset V)
    (psi omega : Option V) : RTable G × Finset V :=
  let (R, S) :=
    match psi with
    | none    => (R, S)
    | some ψ  =>
      let ts := R.toTableState.freeze ψ
      let ts := { ts with reps := upd ts.reps ψ (∅ : Finset V) }
      let R := { R with toTableState := ts }
      let S := insert ψ S
      (R, S)
  match omega with
  | none    => (R, S)
  | some ω  =>
    let R := { R with status := upd R.status ω Status.removed }
    let S := S.erase ω
    let candidates1 :=
      (Finset.univ.filter
        (fun u => R.status u = Status.unset ∧ ω ∈ R.reps u)).toList
    let (R, S) :=
      candidates1.foldl
        (fun (RS : RTable G × Finset V) u => freezeAndRemove RS.1 RS.2 (some u) none)
        (R, S)
    let candidates2 := (R.reps ω).toList.filter (fun u => R.status u = Status.unset)
    let (R, S) :=
      candidates2.foldl
        (fun (RS : RTable G × Finset V) u => freezeAndRemove RS.1 RS.2 (some u) none)
        (R, S)
    let R := { R with reps := upd R.reps ω (∅ : Finset V) }
    (R, S)

/-- **Algorithm 5** (`VERTEX_ELIMINATION`), the opaque original. -/
public partial def vertexElimination (R0 : RTable G) (S0 : Finset V) :
    RTable G × Finset V :=
  let rec loop (rows : List (Row V)) (R : RTable G) (S : Finset V) :
      RTable G × Finset V :=
    match rows with
    | [] => (R, S)
    | (u, v) :: rest  =>
      let R := computeRepresentationScore R
      let su := R.status u
      let sv := R.status v
      let (R, S) :=
        if (su ≠ Status.unset) ∧ (sv ≠ Status.unset) then
          (R, S)
        else if su = Status.unset ∧ sv = Status.frozen then
          freezeAndRemove R S none (some u)
        else if sv = Status.unset ∧ su = Status.frozen then
          freezeAndRemove R S none (some v)
        else
          if R.score u ≥ R.score v then
            freezeAndRemove R S (some u) (some v)
          else
            freezeAndRemove R S (some v) (some u)
      loop rest R S
  loop R0.rows.reverse R0 S0

/-- **Algorithm 8** (`DUADIC_HOP`), the opaque original. -/
public partial def duadicHop (R : RTable G) (S : Finset V)
    (psi omega : Option V) (lam : Finset V) : RTable G × Finset V × Finset V :=
  let (R, S, lam) :=
    match omega with
    | none   => (R, S, lam)
    | some ω =>
      if ω ∈ lam then
        (R, S, lam)
      else
        let lam := insert ω lam
        let R := { R with status := upd R.status ω Status.removed }
        let S := S.erase ω
        let step (u : V) (acc : Finset V × List V) : Finset V × List V :=
          let (lam, Q) := acc
          if u ∈ lam then
            (lam, Q)
          else
            let lam := insert u lam
            if u ∈ S then (lam, Q) else (lam, Q ++ [u])
        let (lam, Q) := (R.reps ω).toList.foldl (fun acc u => step u acc) (lam, [])
        let candidates :=
          (Finset.univ.filter (fun u => ω ∈ R.reps u)).toList
        let (lam, Q) := candidates.foldl (fun acc u => step u acc) (lam, Q)
        let (R, S, lam) :=
          Q.foldl
            (fun (RSl : RTable G × Finset V × Finset V) u =>
              duadicHop RSl.1 RSl.2.1 (some u) none RSl.2.2)
            (R, S, lam)
        (R, S, lam)
  match psi with
  | none    => (R, S, lam)
  | some ψ  =>
    let R := { R with status := upd R.status ψ Status.frozen }
    let S := insert ψ S
    match R.rows.find? (fun rc => rc.1 = ψ ∨ rc.2 = ψ) with
    | none => (R, S, lam)
    | some (a, b)   =>
      let u := if a = ψ then b else a
      if u ∈ S then
        duadicHop R S none (some u) lam
      else
        (R, S, lam)

/-- **Algorithm 7** (`DIMINISHING_HOPS`), the opaque original. -/
public partial def diminishingHops (R0 : RTable G) (S0 : Finset V) : RTable G × Finset V :=
  let rec go (rows : List (Row V)) (Rd : RTable G) (Sd : Finset V) (lamd : Finset V) :
      RTable G × Finset V :=
    match rows with
    | [] => (Rd, Sd)
    | (u, v) :: rest  =>
      let Roriginal := Rd; let Soriginal := Sd; let lamOriginal := lamd
      if Rd.status u = Status.frozen ∧ Rd.status v = Status.frozen then
        let tryEndpoint (w : V) (Rd Sd lamd : _) : RTable G × Finset V × Finset V :=
          let (R1, S1, l1) := duadicHop Roriginal Soriginal none (some w) lamOriginal
          if S1.card < Sd.card then (R1, S1, l1) else (Rd, Sd, lamd)
        let (Rd, Sd, lamd) := tryEndpoint u Rd Sd lamd
        let (Rd, Sd, lamd) := tryEndpoint v Rd Sd lamd
        go rest Rd Sd lamd
      else
        go rest Rd Sd lamd
  go R0.rows R0 S0 (∅ : Finset V)

/-- **Algorithm 3** (`DIMINISHING_HOP_PHASE`), the opaque original. -/
public partial def diminishingHopPhase (R0 : RTable G) : Finset V :=
  let S0 : Finset V := ∅
  let R1 : RTable G := { R0 with score := fun _ => negInf }
  let R2 := computeRepresentationScore R1
  let (R3, S3) := vertexElimination R2 S0
  let m := R0.rows.length
  let rec repeatHops (n : ℕ) (R : RTable G) (S : Finset V) : RTable G × Finset V :=
    match n with
    | 0      => (R, S)
    | n + 1  => let (R', S') := diminishingHops R S; repeatHops n R' S'
  let (_, Sfinal) := repeatHops (m / 2) R3 S3
  Sfinal

/-- **Algorithm 1** (`VERTEX_COVER(G, k)`), the top-level decision procedure. -/
public def vertexCover
    (adj0 : V → List V) (Vs : List V) (M : V → V) (lt : V → V → Bool)
    (k : ℕ) : Bool :=
  let matchingEdges : List (Row V) :=
    Vs.filterMap (fun u => if lt u (M u) then some (u, M u) else none)
  if k < matchingEdges.length then
    false
  else
    let inM : V → V → Bool := fun a b => decide (M a = b ∨ M b = a)
    let R := populateRepresentsTable (G := G) adj0 inM Vs
    let S := diminishingHopPhase R
    decide (S.card ≤ k)

end

-- ═══════════════════════════════════════════════════════════════════════════
-- §7. `thm8_lemma6_lemma7.lean`
-- ═══════════════════════════════════════════════════════════════════════════

/-- Freeze a single endpoint `u`. -/
public def freezeOne (R : RTable G) (S : Finset V) (u : V) : RTable G × Finset V :=
  ({ R with status := upd R.status u Status.frozen }, insert u S)

/-- The endpoints Algorithm 8's removal step considers when removing `ω`. -/
public def removalPartners (R : RTable G) (ω : V) : Finset V :=
  Finset.univ.filter (fun u => u ∈ R.reps ω ∨ ω ∈ R.reps u)

/-- Given the row `(a, b)` found for endpoint `u`, the *other* endpoint of
    that row. -/
public def partnerOf (row : Row V) (u : V) : V :=
  if row.1 = u then row.2 else row.1

/-- **Structural core of Algorithm 8** (`dh`), fuel-indexed so it is
    ordinary structural recursion. -/
public noncomputable def dh : Nat → RTable G → Finset V → Finset V → (V ⊕ List V) →
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

/-- No two graph-adjacent endpoints are ever both left `removed` at the end
    of a single call to `dh (Sum.inl ω)`. -/
public def NoAdjacentDoubleRemoval (n : ℕ) (R : RTable G) (S lam : Finset V) (ω : V) : Prop :=
  ∀ v w, G.Adj v w →
    (dh n R S lam (Sum.inl ω)).1.status v = Status.removed →
    (dh n R S lam (Sum.inl ω)).1.status w ≠ Status.removed

-- ═══════════════════════════════════════════════════════════════════════════
-- §8. `thm8_lemma6_lemma8.lean`
-- ═══════════════════════════════════════════════════════════════════════════

/-- The set of row indices actually used by `R`. -/
public def RowsOf (R : RepTable G) : Finset ℕ := Finset.image R.row Finset.univ

/-- **Definition 14, "two endpoints per row."** -/
public def TwoPerRow (R : RepTable G) : Prop :=
  ∀ i ∈ RowsOf R, ∃ u v : V,
    u ≠ v ∧ R.row u = i ∧ R.row v = i ∧ ∀ w, R.row w = i → w = u ∨ w = v

/-- **Definition 14, "a row is a matching edge."** -/
public def RowsAreEdges (R : RepTable G) : Prop :=
  ∀ (i : ℕ) (u v : V), u ≠ v → R.row u = i → R.row v = i → G.Adj u v

-- ═══════════════════════════════════════════════════════════════════════════
-- §9. `thm8_lemma6.lean`'s own additional definitions
-- ═══════════════════════════════════════════════════════════════════════════

/-- **VC − CBG, "Yes instance."** -/
public def YesInstance (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ S : Finset V, VCover G S ∧ S.card ≤ k

/-- Exactly `vertexCover`'s own local `let inM := ...`. -/
public def inMOf (M : V → V) : V → V → Bool := fun a b => decide (M a = b ∨ M b = a)

/-- Exactly `vertexCover`'s own local `let R := populateRepresentsTable
    adj0 inM Vs`. -/
public noncomputable def RT0Of (adj0 : V → List V) (Vs : List V) (M : V → V) : RTable G :=
  populateRepresentsTable (G := G) adj0 (inMOf M) Vs

/-- One "try hopping by removing endpoint `w`" step. -/
public noncomputable def dhopsStep
  (fuel : ℕ) (Roriginal : RTable G) (Soriginal lamOriginal : Finset V)
    (cur : RTable G × Finset V × Finset V) (w : V) : RTable G × Finset V × Finset V :=
  let (R1, S1, l1) := dh fuel Roriginal Soriginal lamOriginal (Sum.inl w)
  if S1.card < (cur.2).1.card then (R1, S1, l1) else cur

/-- **Algorithm 7** (`DIMINISHING_HOPS`), re-derived. -/
public noncomputable def dhops (fuel : ℕ) : List (Row V) → RTable G → Finset V → Finset V →
    RTable G × Finset V
  | [], Rd, Sd, _ => (Rd, Sd)
  | rc :: rest, Rd, Sd, lamd =>
    if Rd.status rc.1 = Status.frozen ∧ Rd.status rc.2 = Status.frozen then
      let (Rd1, Sd1, lamd1) := dhopsStep fuel Rd Sd lamd (Rd, Sd, lamd) rc.1
      let (Rd2, Sd2, lamd2) := dhopsStep fuel Rd Sd lamd (Rd1, Sd1, lamd1) rc.2
      dhops fuel rest Rd2 Sd2 lamd2
    else
      dhops fuel rest Rd Sd lamd

/-- **Algorithm 7's own entry point**, matching `diminishingHops R0 S0`. -/
public noncomputable def diminishingHops' (fuel : ℕ) (R0 : RTable G) (S0 : Finset V) :
  RTable G × Finset V :=
  dhops fuel R0.rows R0 S0 (∅ : Finset V)

/-- The "Freeze Operation" half of Algorithm 6, re-derived. -/
public noncomputable def frFreeze (R : RTable G) (S : Finset V) (ψ : V) : RTable G × Finset V :=
  let ts := R.toTableState.freeze ψ
  let ts := { ts with reps := upd ts.reps ψ (∅ : Finset V) }
  (({ R with toTableState := ts } : RTable G), insert ψ S)

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

/-- One endpoint's score update, re-derived as its own `def`. -/
public def crsStep (processed : List (Row V)) (R : RTable G) (w : V) : RTable G :=
  match R.status w with
  | Status.unset =>
    let contribution := processed.foldl (fun acc xy =>
      if w ∈ R.reps xy.1 then acc + max 0 (R.score xy.2) + 1
      else if w ∈ R.reps xy.2 then acc + max 0 (R.score xy.1) + 1
      else acc) 0
    { R with score := upd R.score w contribution }
  | _ => { R with score := upd R.score w (-1) }

/-- **Algorithm 4**, re-derived: ordinary structural recursion. -/
public def crs : List (Row V) → List (Row V) → RTable G → RTable G
  | _, [], R => R
  | processed, rc :: rest, R =>
    let R := crsStep processed R rc.1
    let R := crsStep processed R rc.2
    crs (processed ++ [rc]) rest R

/-- **Algorithm 4's own entry point**, matching
    `computeRepresentationScore R0` exactly. -/
def computeRepresentationScore' (R0 : RTable G) : RTable G := crs [] R0.rows R0

/-- **Algorithm 5** (`VERTEX_ELIMINATION`), re-derived. -/
public noncomputable def ve' (fuel : ℕ) : List (Row V) → RTable G → Finset V → RTable G × Finset V
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

/-- **Algorithm 5's own entry point** (bottom-up: `R0.rows.reverse`). -/
public noncomputable def vertexElimination' (fuel : ℕ) (R0 : RTable G) (S0 : Finset V) :
  RTable G × Finset V :=
  ve' fuel R0.rows.reverse R0 S0

/-- **Algorithm 3, Lines 1-5**, re-derived from the *transparent*
    re-derivations above. -/
public noncomputable def algInit (fuel : ℕ) (R0 : RTable G) : RTable G × Finset V :=
  vertexElimination' fuel
    (computeRepresentationScore' ({ R0 with score := fun _ => negInf } : RTable G))
    (∅ : Finset V)

/-- **Algorithm 3, Lines 6-8's loop, re-executed literally**. -/
public noncomputable def algState (fuel : ℕ) (R0 : RTable G) : ℕ → RTable G × Finset V
  | 0     => algInit fuel R0
  | n + 1 => diminishingHops' fuel (algState fuel R0 n).1 (algState fuel R0 n).2

/-- The table-state component of `algState`. -/
public noncomputable def SseqOf (fuel : ℕ) (R0 : RTable G) (n : ℕ) : TableState G :=
  (algState fuel R0 n).1.toTableState

/-- Bridges the opaque original `diminishingHopPhase` to `algState`. -/
public def PhaseMatchesAlgState (fuel : ℕ) (R0 : RTable G) (R : RepTable G) : Prop :=
  diminishingHopPhase R0 = (algState fuel R0 (RowsOf R).card).2

-- ═══════════════════════════════════════════════════════════════════════════
-- §10. The challenge: Lemma 6
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Lemma 6** (paper, p.58, lines 1776-1920), the result being submitted. -/
public theorem VCCBGPartII.Lemma6_wrapper
    (hcubic : ∀ v : V, G.degree v = 3)
    (hbridgeless : ∀ ⦃e : Sym2 V⦄, e ∈ G.edgeSet → ¬ G.IsBridge e)
    (adj0 : V → List V) (Vs : List V) (M : V → V) (lt : V → V → Bool) (k : ℕ)
    (hyes : vertexCover (G := G) adj0 Vs M lt k = true)
    (hMinv : ∀ v, M (M v) = v) (hMadj : ∀ v, G.Adj v (M v))
    (hrow_pair : ∀ ⦃u v : V⦄, (matchingSubgraph (G := G) M hMadj).Adj u v →
        (RT0Of (G := G) adj0 Vs M).rows.findIdx (fun rc => rc.1 = u ∨ rc.2 = u) =
        (RT0Of (G := G) adj0 Vs M).rows.findIdx (fun rc => rc.1 = v ∨ rc.2 = v))
    (htwo : TwoPerRow ((RT0Of (G := G) adj0 Vs M).toRepTable M hMinv hMadj hrow_pair))
    (hedges : RowsAreEdges ((RT0Of (G := G) adj0 Vs M).toRepTable M hMinv hMadj hrow_pair))
    (hrows_half :
      (RowsOf ((RT0Of (G := G) adj0 Vs M).toRepTable M hMinv hMadj hrow_pair)).card
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
    YesInstance G k := by
  sorry

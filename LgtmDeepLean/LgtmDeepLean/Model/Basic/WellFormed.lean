module

public import LgtmDeepLean.Model.Basic

/-! # Well-formedness of the model's values

What a `CommentManager` and a `CommentThreads` value have to satisfy.  Each predicate's first clause
is typing: `Value.HasType` says a value is a struct of the right name with a value of the right type
under each field, and the clauses after it are what it cannot say — which *key* a comment is bound
to, or which node a comment ref resolves to — facts that relate two fields of one value to each
other and that every declaration reading a comment out of a manager depends on.

Having typing as a clause is what makes the field types of the model's structs available to the
theorems below rather than something they would each have to assume: a type table these predicates
can be read against is one that declares those structs, which is `Model.Declares`.

Extrinsic, in the style of `Value.HasType`: a predicate over the value rather than a field of it.  A
`Value` is what `Eval` builds, and it carries no proofs, so an invariant about one is a hypothesis a
theorem takes rather than something a constructor could have enforced.

The clauses here are the ones the theorems proved so far spend, which is fewer than the shallow
model's `CommentThreads` carries as fields: a clause nothing needs is a hypothesis every theorem
would have to be handed and none would use, so the rest — that a node's children are registered,
that the location roots are duplicate-free — belong here as the theorems that need them arrive. -/

@[expose] public section

/-- The structure types a table has to declare for the predicates below to be read against it: the
model's own declarations, under the model's own names.

A hypothesis on the table rather than `modelProgram.typeDecls` spelled out, which this module cannot
mention — the model is assembled from modules including this one.  It is also the weaker statement:
a theorem here reads the field types of `Comment` and friends, and any table agreeing with the model
at those names serves.  `Model.declares_modelProgram` is where the model's own table meets it. -/
structure Model.Declares (td : TypeDecls) : Prop where
  commentManager : td.ss.lookup "CommentManager" = some CommentManager
  comment : td.ss.lookup "Comment" = some Comment
  commentThreads : td.ss.lookup "CommentThreads" = some CommentThreads
  /-- Added for `CommentThread.linearize.apply_exists`: that proof reads `thread`'s own `value`
  and `children` fields at their declared types, where every theorem before it only ever read a
  `CommentThread` back out of a `CommentThreads` or `CommentManager` value without opening it up. -/
  commentThread : td.ss.lookup "CommentThread" = some CommentThread

/-- The comment `manager` binds `ref` to: what a call to `CommentManager.get` answers with, read off
the value. -/
def CommentManager.get? (manager ref : Value) : Option Value :=
  manager.lookupField? "comments" ref

/-- The thread node `threads` binds `ref` to: what `threads.commentTreeNodes[ref]` answers with,
read off the value. -/
def CommentThreads.node? (threads ref : Value) : Option Value :=
  threads.lookupField? "commentTreeNodes" ref

/-- The timestamp `manager` records for the root comment of the thread node `thread`, where it
records one: the node's `value` resolved to a comment and that comment's `createdTimestamp`.

This is `(manager.get thread.value).createdTimestamp` from the shallow model, with every step it
takes for granted made a `none`: the shallow `get` is total because a `Comment` has a `default`,
where here a node naming a comment the manager does not contain has no timestamp at all. -/
def CommentManager.rootTimestamp? (manager thread : Value) : Option Int :=
  match (thread.field? "value").bind (CommentManager.get? manager) with
  | some c =>
    match c.field? "createdTimestamp" with
    | some (.int i) => some i
    | _ => none
  | none => none

/-- Every comment in `cs` is one `manager` contains.

What reading a list of comments out of a manager leaves a caller with, and what getting back from a
thread node to the comment whose timestamp orders it needs: a comment the manager does not contain
is one `CommentManager.rootTimestamp?` has no answer about. -/
def CommentManager.ContainsComments (manager : Value) (cs : List Value) : Prop :=
  ∀ c ∈ cs, ∃ ref, CommentManager.get? manager ref = some c

/-- Every registered node names a comment the manager has: what `expectComment`'s `unreachable`
branch assumes, and what a sort over the children needs in order to have a comparison for every
pair it asks about. -/
def CommentThreads.NodesCovered (manager threads : Value) : Prop :=
  ∀ ref node, CommentThreads.node? threads ref = some node →
    ∃ c, CommentManager.get? manager ref = some c

/-- What a `CommentManager` value has to be: well typed, and well formed besides.

A `structure ... : Prop` rather than a conjunction, so each clause keeps its name and a proof reads
one off by projection. -/
structure CommentManager.WellFormed (td : TypeDecls) (manager : Value) : Prop where
  /-- The value is a `CommentManager` under `td`.

  A clause rather than a hypothesis beside this predicate because everything stated here is about a
  comment read out of the manager, and typing is what says those comments are `Comment`s — see
  `CommentManager.hasType_get?`, which is where the clause is spent. -/
  hasType : manager.HasType td (.struct "CommentManager")
  /-- A comment is bound to its own ref, so a comment found in the manager says which key found it.
  This is what lets a thread node's `value` be turned back into the comment it names. -/
  refMatchesKey : ∀ ref c, CommentManager.get? manager ref = some c → c.field? "ref" = some ref

/-- One descent of `linearize`: `child` is the node a child ref of the registered node `parent`
resolves to.  Stated node-to-node, because a node is what the recursive call takes, and with the
parent required to be registered so that a rank function witnessing well-foundedness only has to
rank the nodes the pool actually holds. -/
def CommentThreads.ChildEdge (threads child parent : Value) : Prop :=
  ∃ parentRef childRefs childRef,
    CommentThreads.node? threads parentRef = some parent ∧
    parent.field? "children" = some (.list childRefs) ∧ childRef ∈ childRefs ∧
    CommentThreads.node? threads childRef = some child

/-- What a `CommentThreads` value has to be: well typed, and a node bound to the ref of the comment
it is the thread of. -/
structure CommentThreads.WellFormed (td : TypeDecls) (threads : Value) : Prop where
  /-- The value is a `CommentThreads` under `td`; `CommentThreads.hasType_node?` is what it buys. -/
  hasType : threads.HasType td (.struct "CommentThreads")
  rootMatchesKey : ∀ ref node,
    CommentThreads.node? threads ref = some node → node.field? "value" = some ref
  /-- No dangling child ref: a child of a registered node is itself registered.  Without this the
  `none` branch of `threads.commentTreeNodes[childRef]` is reached, and `unreachable` has no value,
  so the call has no derivation. -/
  childrenRegistered : ∀ ref node childRefs child,
    CommentThreads.node? threads ref = some node →
    node.field? "children" = some (.list childRefs) → child ∈ childRefs →
    ∃ childNode, CommentThreads.node? threads child = some childNode
  /-- No cycle of child links.  This is what the fuel parameter stood in for: it is the measure the
  recursion descends on, and so the reason a call to `linearize` has a derivation at all. -/
  childEdgeWf : WellFounded (CommentThreads.ChildEdge threads)

/-- A rank function decreasing across every descent is enough to witness `childEdgeWf`: every future
construction proof will have a rank in hand rather than a `WellFounded` already assembled. -/
theorem CommentThreads.wellFounded_childEdge_of_rank {threads : Value} (rank : Value → Nat)
    (h : ∀ child parent, CommentThreads.ChildEdge threads child parent → rank child < rank parent) :
    WellFounded (CommentThreads.ChildEdge threads) :=
  Subrelation.wf (fun {_ _} hxy => h _ _ hxy) (InvImage.wf rank Nat.lt_wfRel.wf)

/-! ## What typing gives about what is read out

The invariants above say which key a value was found under; these say what the value found is.  Both
are one application of `Value.hasType_lookupField` to the typing clause and the declaration the
table holds the struct to: `comments` and `commentTreeNodes` are hashmap fields, so whatever a
lookup in one of them answers with is of that map's value type, which is all the type of a value
read out of a manager or a thread pool can be known to be. -/

/-- A comment read out of a well-formed manager is a `Comment`. -/
theorem CommentManager.hasType_get? {td : TypeDecls} {manager : Value} (hd : Model.Declares td)
    (hwf : CommentManager.WellFormed td manager) {ref c : Value}
    (h : CommentManager.get? manager ref = some c) : c.HasType td (.struct "Comment") :=
  Value.hasType_lookupField hwf.hasType hd.commentManager rfl h

/-- A thread node read out of a well-formed thread pool is a `CommentThread`. -/
theorem CommentThreads.hasType_node? {td : TypeDecls} {threads : Value} (hd : Model.Declares td)
    (hwf : CommentThreads.WellFormed td threads) {ref node : Value}
    (h : CommentThreads.node? threads ref = some node) :
    node.HasType td (.struct "CommentThread") :=
  Value.hasType_lookupField hwf.hasType hd.commentThreads rfl h

/-- Every comment in the manager records its timestamp as an `int`.

Was a clause of `CommentManager.WellFormed`, so that a theorem about the order comments come out in
needed no type table and no typing hypothesis; now that typing is a clause it is a consequence, and
one a caller of `CommentThreads.asAlist` no longer has to be handed separately.  `createdTimestamp`
is an `int` field of `Comment`, and `CommentManager.hasType_get?` says the comment is one. -/
theorem CommentManager.timestampIsInt {td : TypeDecls} {manager : Value} (hd : Model.Declares td)
    (hwf : CommentManager.WellFormed td manager) {ref c : Value}
    (h : CommentManager.get? manager ref = some c) :
    ∃ i : Int, c.field? "createdTimestamp" = some (.int i) := by
  have hc := CommentManager.hasType_get? hd hwf h
  obtain ⟨i, hi⟩ :=
    Value.hasType_int_iff.mp (Value.hasType_fieldOf hc hd.comment "createdTimestamp")
  exact ⟨i, hi ▸ Value.field?_fieldOf hc hd.comment "createdTimestamp"⟩

end

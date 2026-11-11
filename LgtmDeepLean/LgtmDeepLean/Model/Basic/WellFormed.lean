module

public import LgtmDeepLean.Model.Basic

/-! # Well-formedness of the model's values

What a `CommentManager` and a `CommentThreads` value have to satisfy beyond having the right shape.
`Value.HasType` says a value is a struct of the right name with a value of the right type under each
field; what it cannot say is which *key* a comment is bound to, or which node a comment ref resolves
to — facts that relate two fields of one value to each other and that every declaration reading a
comment out of a manager depends on.

Extrinsic, in the style of `Value.HasType`: a predicate over the value rather than a field of it.  A
`Value` is what `Eval` builds, and it carries no proofs, so an invariant about one is a hypothesis a
theorem takes rather than something a constructor could have enforced.

The clauses here are the ones the theorems proved so far spend, which is fewer than the shallow
model's `CommentThreads` carries as fields: a clause nothing needs is a hypothesis every theorem
would have to be handed and none would use, so the rest — that a node's children are registered,
that the location roots are duplicate-free — belong here as the theorems that need them arrive. -/

@[expose] public section

/-- The value `f` is bound to in a struct value, or `none` where `v` is not a struct that carries
`f`.

The value's own fields, as `Eval`'s `EStructGet` reads them: a field is found by name in what the
value carries, and no declaration is consulted. -/
def Value.field? : Value → FieldName → Option Value
  | .struct _ fvs, f => fvs.lookup f
  | _, _ => none

/-- The value a hashmap-valued field of `v` binds `k` to, where it binds one.

`KeyValues.lookup?`'s two options collapsed into one: a field that is not a hashmap, a key no answer
could be given about, and a key the map does not bind are all `none` here, because nothing stated
over this distinguishes them. -/
def Value.lookupField? (v : Value) (f : FieldName) (k : Value) : Option Value :=
  match v.field? f with
  | some (.hashmap kvs) => (KeyValues.lookup? kvs k).join
  | _ => none

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

/-- The invariants a `CommentManager` value carries that its type does not.

A `structure ... : Prop` rather than a conjunction, so each clause keeps its name and a proof reads
one off by projection. -/
structure CommentManager.WellFormed (manager : Value) : Prop where
  /-- A comment is bound to its own ref, so a comment found in the manager says which key found it.
  This is what lets a thread node's `value` be turned back into the comment it names. -/
  refMatchesKey : ∀ ref c, CommentManager.get? manager ref = some c → c.field? "ref" = some ref
  /-- Every comment records its timestamp as an `int`.

  What `Value.HasType` would give of a well-typed manager — `createdTimestamp` is an `int` field of
  `Comment` — stated here instead so that a theorem about the order comments come out in needs no
  type table and no typing hypothesis. -/
  timestampIsInt : ∀ ref c, CommentManager.get? manager ref = some c →
    ∃ i : Int, c.field? "createdTimestamp" = some (.int i)

/-- The invariant a `CommentThreads` value carries that its type does not: a node is bound to the
ref of the comment it is the thread of. -/
structure CommentThreads.WellFormed (threads : Value) : Prop where
  rootMatchesKey : ∀ ref node,
    CommentThreads.node? threads ref = some node → node.field? "value" = some ref

end

module

public import Lean

open Lean

/-- A human-readable name for a kind of declaration, used in `@[public_api]`'s rejection message. -/
private def kindDescription : ConstantKind → String
  | .defn => "a definition"
  | .thm => "a theorem"
  | .axiom => "an axiom"
  | .opaque => "an opaque definition"
  | .quot => "a `Quot` primitive"
  | .induct => "an inductive type"
  | .ctor => "a constructor"
  | .recursor => "a recursor"

/-- Marks a definition or a structure in `LgtmLean` as part of the public API of the generated elisp
library.

Extraction renders the declarations it translates under an internal `lgtm--` prefix; the ones tagged
`@[public_api]` are instead rendered under the plain `lgtm-` prefix, which is the elisp convention
for the names that callers outside the library are meant to use.

The tag only makes sense on declarations that have a run-time representation and a name the
extractor renders, so it is rejected on anything that is neither an ordinary function definition
nor a structure definition (theorems, axioms, non-structure inductives, ...).

It is likewise rejected on declarations that aren't `public`, since those are compiled under a
mangled `_private.` name that the tag doesn't survive to -- and a declaration `LgtmLean` itself
keeps module-private can hardly be part of the extracted library's public API. -/
public initialize publicApiAttr : TagAttribute ←
  registerTagAttribute `public_api
    "mark a definition as part of LgtmLean's public API, so that extraction renders it under the \
     public `lgtm-` prefix rather than the internal `lgtm--` one"
    (validate := fun declName => do
      -- `getEnv` yields an *exporting* view of the environment here, in which a `public` (but
      -- unexposed) definition or theorem appears as an `axiom`: its body is deliberately not part
      -- of the module's interface. `setExporting false` looks past that at the declaration's real
      -- kind.
      let env := (← getEnv).setExporting false
      if isPrivateName declName then
        throwError "`@[public_api]` cannot be applied to `{.ofConstName declName}`: only `public` \
          declarations can be part of the extracted library's public API"
      let kind? : Option ConstantKind := env.findAsync? declName |>.map (·.kind)
      match kind? with
      | some .defn => pure ()
      | some .induct =>
        unless isStructure env declName do
          throwError "`@[public_api]` cannot be applied to the inductive type \
            `{.ofConstName declName}`: only function and structure definitions are rendered under \
            a public name"
      | some kind =>
        throwError "`@[public_api]` cannot be applied to `{.ofConstName declName}`: expected a \
          function or structure definition, but it is {kindDescription kind}"
      | none => throwError "unknown declaration `{declName}`")

/-- Whether `declName` is tagged `@[public_api]` in `env`. -/
public def isPublicApi (env : Environment) (declName : Name) : Bool :=
  publicApiAttr.hasTag env declName

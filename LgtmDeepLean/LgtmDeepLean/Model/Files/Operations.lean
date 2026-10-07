module

public import LgtmDeepLean.Model.Basic
meta import LgtmDeepLean.Lang.Syntax
meta import LgtmDeepLean.Model.Basic

@[expose] public section

/-- Return the path of VERSION of the MODIFIED-FILE. -/
lgtm def pathOfFileAtVersion (version : inductive FileVersion) (modifiedFile : struct ModifiedFileRef) : string :=
  match version with
  | Base => modifiedFile.baseFileName
  | Current => modifiedFile.currentFileName

def Model.Files.funcDecls : List FuncDecl :=
  [pathOfFileAtVersion]

end

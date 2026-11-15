module

public import LgtmDeepLean.Model.Basic
meta import LgtmDeepLean.Lang.Syntax

@[expose] public section

/-- Return the path of VERSION of the MODIFIED-FILE. -/
@[lgtm] def pathOfFileAtVersion (version : inductive FileVersion) (modifiedFile : struct ModifiedFileRef) : string :=
  match version with
  | Base => modifiedFile.baseFileName
  | Current => modifiedFile.currentFileName

@[lgtm] def ModifiedFileState.resetFileState (fileState : struct ModifiedFileState) : struct ModifiedFileState :=
  new ModifiedFileState { ref = fileState.ref
                        ,  fileRef = fileState.fileRef
                        ,  selectedComment = (none : struct SelectedComment)
                        ,  baseThreads = CommentThreads.empty()
                        ,  currentThreads = CommentThreads.empty()
                        }

@[lgtm] def ModifiedFileManager.resetCommentState (fileState : struct ModifiedFileManager) : struct ModifiedFileManager :=
  let newState := map hashmap fileState.state (fun (_r : struct ModifiedFileRef) (s : struct ModifiedFileState) => ModifiedFileState.resetFileState(s));
  new ModifiedFileManager { modifiedFiles = fileState.modifiedFiles
                          , state = newState
                          }

def Model.Files.funcDecls : List FuncDecl :=
  [pathOfFileAtVersion, ModifiedFileState.resetFileState, ModifiedFileManager.resetCommentState]

end

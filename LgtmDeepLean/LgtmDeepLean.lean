module
-- This module serves as the root of the `LgtmDeepLean` library.
-- Import modules here that should be built as part of the library.
public import LgtmDeepLean.Basic
public import LgtmDeepLean.Lang.Eval
import LgtmDeepLean.Lang.Eval.Tests
public import LgtmDeepLean.Lang.IR
public import LgtmDeepLean.Lang.Syntax
import LgtmDeepLean.Lang.Syntax.Tests
public import LgtmDeepLean.Lang.TypeCheck
public import LgtmDeepLean.Lang.TypeCheck.Comparable
public import LgtmDeepLean.Lang.TypeCheck.Infer
import LgtmDeepLean.Lang.TypeCheck.Tests
public import LgtmDeepLean.Lang.TypeCheck.TypeDecls
public import LgtmDeepLean.Lang.TypeCheck.Uniqueness
public import LgtmDeepLean.Lang.Value

public import LgtmDeepLean.Model.Basic
public import LgtmDeepLean.Model.Location.Operations
public import LgtmDeepLean.Model.Location.Properties
public import LgtmDeepLean.Model.Program
import LgtmDeepLean.Model.Tests
